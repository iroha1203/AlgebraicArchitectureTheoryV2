#!/usr/bin/env python3
"""論文 source を明示した一覧から検査・ビルド・梱包する。Python 3.10+ / 標準ライブラリ。"""
import argparse
import csv
import hashlib
import json
import platform
import re
import shutil
import subprocess
import sys
import zipfile
from pathlib import Path, PurePosixPath

MARKERS = re.compile(r'\b(?:TODO|FIXME|TBD|PLACEHOLDER)\b|\[insert\b|as an AI language model|here is (?:the|your) (?:revised|updated)|fill in (?:the )?(?:real|actual) (?:numbers|values)|turn\d+(?:search|view)\d+', re.I)
HIDDEN = re.compile(r'[\u200b-\u200f\u202a-\u202e\u2066-\u2069]')
LOCAL = re.compile(r'/Users/|/home/|[A-Z]:\\Users\\')


def digest(data):
    return hashlib.sha256(data).hexdigest()


def encoded(value):
    return (json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2) + '\n').encode()


def relative(value):
    p = PurePosixPath(value)
    if not value or p.is_absolute() or '..' in p.parts or '\\' in value or str(p) != value:
        raise ValueError(f'相対パスの形式が不正: {value}')
    return p


def load(config_path):
    config_path = Path(config_path).resolve()
    config_bytes = config_path.read_bytes()
    cfg = json.loads(config_bytes)
    if cfg['schema'] != 'paper-project/v1':
        raise ValueError('未対応の config schema')
    root = config_path.parent
    data, originals = {}, {}
    for entry in cfg['files']:
        src, dst = relative(entry['source']), relative(entry['target'])
        path = root / str(src)
        if any(p.is_symlink() for p in [path, *path.parents] if p != root.parent):
            raise ValueError(f'symlink source: {src}')
        if not path.resolve().is_relative_to(root) or not path.is_file():
            raise ValueError(f'入力ファイル欠落: {src}')
        if str(dst) in data or str(dst).startswith('.'):
            raise ValueError(f'出力パス重複・非公開名: {dst}')
        raw = path.read_bytes()
        originals[str(src)] = digest(raw)
        if dst.suffix == '.tex':
            text = raw.decode('utf-8')
            for old, new in cfg.get('tex_replacements', {}).items():
                text = text.replace(old, new)
            raw = text.encode()
        if dst.suffix not in {'.tex', '.bib', '.sty', '.cls', '.png', '.jpg', '.jpeg', '.pdf', '.eps', '.bbl'}:
            raise ValueError(f'投稿用 source の未対応拡張子: {dst}')
        data[str(dst)] = raw
    main = str(relative(cfg['main']))
    if main not in data or '/' in main or not main.endswith('.tex'):
        raise ValueError('main は投稿ルートの一覧内 .tex を指定する')
    identity = {'config_sha256': digest(config_bytes), 'original_files': originals}
    return cfg, data, digest(encoded(identity)), originals


def uncomment(text):
    return re.sub(r'(?<!\\)%[^\n]*', '', text)


def check(cfg, data, references=None, source_hash=None):
    findings, labels, refs, cited, bibkeys = [], [], [], set(), []
    def add(level, file, message):
        findings.append({'level': level, 'file': file, 'message': message})
    for name, raw in data.items():
        if Path(name).suffix not in {'.tex', '.bib', '.sty', '.cls', '.bbl'}:
            continue
        text = raw.decode('utf-8')
        for n, line in enumerate(text.splitlines(), 1):
            for pattern, message in [(HIDDEN, 'hidden / bidirectional Unicode'), (LOCAL, 'ローカル絶対パス'), (MARKERS, '編集・生成残存候補')]:
                if pattern.search(line):
                    add('error', f'{name}:{n}', message)
        body = uncomment(text)
        if name.endswith('.bib'):
            bibkeys += re.findall(r'@(?!(?:comment|string|preamble)\b)\w+\s*[{(]\s*([^,\s]+)\s*,', body, re.I)
        if not name.endswith('.tex'):
            continue
        labels += re.findall(r'\\label\s*\{([^}]+)\}', body)
        refs += [(name, key) for key in re.findall(r'\\(?:ref|eqref|pageref|autoref|cref|Cref)\*?\s*\{([^}]+)\}', body)]
        for keys in re.findall(r'\\(?:cite\w*|nocite)\*?(?:\[[^\]]*\])*\s*\{([^}]+)\}', body):
            cited.update(k.strip() for k in keys.split(','))
        for command, value in re.findall(r'\\(input|include|includegraphics|bibliography)(?:\[[^\]]*\])?\s*\{([^}]+)\}', body):
            for value in value.split(','):
                value = value.strip()
                try:
                    relative(value)
                except ValueError:
                    add('error', name, f'{command}: 非静的またはルート外の参照 {value}')
                    continue
                suffixes = {'input': ['', '.tex'], 'include': ['', '.tex'], 'bibliography': ['', '.bib'], 'includegraphics': ['', '.pdf', '.png', '.jpg', '.jpeg', '.eps']}[command]
                if not any(value + ext in data for ext in suffixes):
                    add('error', name, f'{command}: ファイル欠落 {value}')
    for key in set(labels):
        if labels.count(key) > 1:
            add('error', 'labels', f'重複 label: {key}')
    for key in set(bibkeys):
        if bibkeys.count(key) > 1:
            add('error', 'bibliography', f'重複 citation key: {key}')
    for name, keys in refs:
        for key in keys.split(','):
            if key.strip() not in labels:
                add('error', name, f'未定義 label: {key}')
    if '*' in cited:
        cited = (cited - {'*'}) | set(bibkeys)
    for key in sorted(cited - set(bibkeys)):
        add('error', 'bibliography', f'未定義 citation key: {key}')
    if references:
        with open(references, newline='', encoding='utf-8') as stream:
            rows = list(csv.DictReader(stream))
        keys = [row.get('key') for row in rows]
        bibhash = digest(encoded({k: digest(v) for k, v in data.items() if k.endswith('.bib')}))
        for key in sorted(cited):
            matched = [row for row in rows if row.get('key') == key]
            if len(matched) != 1:
                add('error', 'references.csv', f'{key}: 確認行欠落または重複')
                continue
            row = matched[0]
            required = ['source_url', 'source_locator', 'cited_claim', 'reviewer', 'checked_on']
            if row.get('status') != 'verified' or any(not row.get(k, '').strip() for k in required):
                add('error', 'references.csv', f'{key}: 原典確認記録が未完了')
            if row.get('bib_sha256') != bibhash or row.get('manuscript_sha256') != source_hash:
                add('error', 'references.csv', f'{key}: 確認対象 hash 不一致')
        for key in keys:
            if key not in bibkeys:
                add('error', 'references.csv', f'書誌にない確認行: {key}')
    return findings


def prepare(out, data):
    out = Path(out).resolve()
    if out.exists():
        raise ValueError(f'既存の出力先を上書きしません: {out}')
    out.mkdir(parents=True)
    for name, raw in data.items():
        dest = out / name
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(raw)
    return out


def run(argv, cwd):
    result = subprocess.run(argv, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    return result.returncode, result.stdout


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('action', choices=['check', 'build', 'package'])
    ap.add_argument('config')
    ap.add_argument('--out', help='新しい出力ディレクトリ (build/package 必須)')
    ap.add_argument('--engine', choices=['tectonic', 'xelatex', 'pdflatex'], default='tectonic')
    ap.add_argument('--references', help='原典確認 CSV を機械照合する')
    ap.add_argument('--build-record', help='PDF の生成記録 (省略時は PDF の親の親/build.json)')
    ap.add_argument('--pdf', help='完成 PDF の抽出テキストも検査する (check のみ)')
    args = ap.parse_args()
    cfg, data, source_hash, originals = load(args.config)
    findings = check(cfg, data, args.references, source_hash)
    report = {'schema': 'paper-check/v1', 'source_sha256': source_hash,
              'bib_sha256': digest(encoded({k: digest(v) for k, v in data.items() if k.endswith('.bib')})),
              'files': {k: digest(v) for k, v in data.items()}, 'findings': findings,
              'original_files': originals, 'tool_sha256': digest(Path(__file__).read_bytes()),
              'submission_ready': False,
              'coverage': '静的な TeX 参照・書誌キー・残存候補。原典の実在・内容、証明、PDF 目視は別途確認。'}
    if args.pdf:
        if args.action != 'check':
            raise ValueError('--pdf は check のみ')
        pdf = Path(args.pdf).resolve()
        code, output = run(['pdftotext', str(pdf), '-'], pdf.parent)
        if code:
            raise ValueError('PDF テキスト抽出失敗')
        report['pdf_sha256'] = digest(pdf.read_bytes())
        record = json.loads(Path(args.build_record or pdf.parent.parent / 'build.json').read_text())
        if record.get('pdf_sha256') != report['pdf_sha256'] or record.get('source_sha256') != source_hash:
            findings.append({'level': 'error', 'file': 'PDF', 'message': '生成記録の PDF/source hash 不一致'})
        for pattern, label in [(MARKERS, '編集・生成残存候補'), (LOCAL, 'ローカル絶対パス'), (HIDDEN, '不可視文字候補'), (re.compile(r'\?\?'), '未解決参照候補')]:
            if pattern.search(output):
                findings.append({'level': 'error', 'file': 'PDF', 'message': label})
    if args.action == 'check':
        print(encoded(report).decode(), end='')
        return int(bool(findings))
    if not args.out:
        raise ValueError('--out が必要')
    if findings:
        print(encoded(report).decode(), end='')
        return 1
    out = Path(args.out).resolve()
    if args.action == 'package':
        prepare(out, {})
        prepare(out / 'source', data)
        archive = out / 'source.zip'
        with zipfile.ZipFile(archive, 'w', zipfile.ZIP_DEFLATED) as z:
            for name, raw in sorted(data.items()):
                info = zipfile.ZipInfo(name, date_time=(2026, 1, 1, 0, 0, 0))
                info.compress_type = zipfile.ZIP_DEFLATED
                info.external_attr = 0o644 << 16
                z.writestr(info, raw)
        report['zip_sha256'] = digest(archive.read_bytes())
        (out / 'manifest.json').write_bytes(encoded(report))
        print(f'source.zip 作成: {out} (投稿可否は投稿記録で判断)')
        return 0
    engine = shutil.which(args.engine)
    if not engine:
        raise ValueError(f'処理系がありません: {args.engine}')
    code, version = run([engine, '--version'], Path.cwd())
    expected = cfg['environment']['tectonic'] if args.engine == 'tectonic' else f"TeX Live {cfg['environment']['texlive']}"
    if code or expected not in version:
        raise ValueError(f'処理系の版不一致: expected {expected}; {version.splitlines()[0]}')
    if args.engine != 'tectonic':
        code, texroot = run(['kpsewhich', '--var-value=TEXMFROOT'], Path.cwd())
        tlpdb = Path(texroot.strip()) / 'tlpkg/texlive.tlpdb'
        if code or not tlpdb.is_file():
            raise ValueError('TeX Live package inventory を取得できません')
        report['texlive_packages_sha256'] = digest(tlpdb.read_bytes())
    prepare(out, {})
    source = prepare(out / 'source', data)
    build = out / 'build'
    build.mkdir()
    if args.engine == 'tectonic':
        commands = [[engine, '--untrusted', '--only-cached', '--keep-logs', '--keep-intermediates', '--outdir', str(build), cfg['main']]]
        cwd = source
    else:
        # arXiv と同様、投稿ルートを作業ディレクトリとして処理する。
        tex = [engine, '-interaction=nonstopmode', '-halt-on-error', '-no-shell-escape', cfg['main']]
        commands = [tex]
        if any(k.endswith('.bib') for k in data):
            commands += [['bibtex', Path(cfg['main']).stem]]
        commands += [tex, tex]
        cwd = source
    log = ''
    exit_code = 0
    for command in commands:
        exit_code, output = run(command, cwd)
        log += output
        if exit_code:
            break
    if args.engine != 'tectonic':
        for suffix in ['.pdf', '.log', '.blg']:
            p = source / (Path(cfg['main']).stem + suffix)
            if p.exists():
                shutil.copy2(p, build / p.name)
    (out / 'process.log').write_text(log)
    pdf = build / (Path(cfg['main']).stem + '.pdf')
    texlog = build / (Path(cfg['main']).stem + '.log')
    final_log = texlog.read_text(errors='replace') if texlog.exists() else ''
    bad = re.findall(r'[^\n]*(?:undefined|Missing character:|multiply defined)[^\n]*', final_log, re.I)
    report.update({'engine': args.engine, 'version': version.splitlines()[0],
                   'executable_sha256': digest(Path(engine).read_bytes()),
                   'platform': platform.platform(), 'python': platform.python_version(),
                   'original_files': originals, 'exit_code': exit_code,
                   'overfull': re.findall(r'Overfull[^\n]*', final_log),
                   'underfull_count': len(re.findall(r'Underfull', final_log)),
                   'unresolved': bad, 'pdf_sha256': digest(pdf.read_bytes()) if pdf.exists() else None})
    report['source_changed_during_build'] = source_hash != load(args.config)[2]
    (out / 'build.json').write_bytes(encoded(report))
    print(encoded({k: report[k] for k in ['engine', 'exit_code', 'overfull', 'underfull_count', 'unresolved', 'pdf_sha256', 'source_changed_during_build']}).decode())
    return int(bool(exit_code or not pdf.exists() or bad or report['source_changed_during_build']))


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (ValueError, KeyError, OSError, json.JSONDecodeError) as exc:
        print(f'paper: {exc}', file=sys.stderr)
        sys.exit(2)
