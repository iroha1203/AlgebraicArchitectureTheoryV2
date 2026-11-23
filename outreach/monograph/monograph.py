#!/usr/bin/env python3
"""AAT 純粋数学本文 (docs/aat/algebraic_geometric_theory/) から
モノグラフ .tex / .pdf を決定的に生成・検証・ビルドする CLI。

Python 3.10+ / 標準ライブラリのみ。
数学本文 Markdown を唯一の編集元 (Single Source of Truth) とし、入力は変更しない。
"""
from __future__ import annotations

import argparse
import hashlib
import json
import platform
import re
import shutil
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path, PurePosixPath
from typing import Any

HIDDEN_RE = re.compile(r'[\u200b-\u200f\u202a-\u202e\u2066-\u2069]')
LOCAL_PATH_RE = re.compile('/' + r'Users/|/' + r'home/|[A-Z]:\\' + r'Users\\')
NAV_PARA_RE = re.compile(r'\[[^\]]+\]\([^)]+\)(?:\s*·\s*\[[^\]]+\]\([^)]+\))*')
HEADING_RE = re.compile(r'^(#{1,6})\s+(.*)$')
HR_RE = re.compile(r'^\s*---+\s*$')
FENCE_OPEN_RE = re.compile(r'^(\s*)```(\S*)\s*$')
FENCE_CLOSE_RE = re.compile(r'^(\s*)```\s*$')
TABLE_SEP_RE = re.compile(r'^\|[\s:|-]+\|\s*$')
LIST_ITEM_RE = re.compile(r'^(\s*)([-*]|\d+\.)\s+(.*)$')
EQ_TAG_RE = re.compile(r'^\*\*式\(([A-F0-9]+\.[0-9]+[a-z]?)\)\*\*\s*$')
DECL_START_RE = re.compile(
    r'^\*\*((?:定義|命題|補題|定理|系|構成|例|問題|設定)[A-F0-9]+\.[0-9]+[a-z]?(?:（[^）]*）)?\.?)\*\*(.*)$',
    re.S,
)
PROOF_START_RE = re.compile(
    r'^\*\*((?:原始)?(?:構成と)?証明(?:（[^）]*）)?\.?)\*\*(.*)$',
    re.S,
)

DEFAULT_MANIFEST = Path(__file__).resolve().parent / 'manifest.json'
DEFAULT_PREAMBLE = Path(__file__).resolve().parent / 'preamble.tex'


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def encoded(value: Any) -> bytes:
    return (json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2) + '\n').encode('utf-8')


def relative_posix(value: str) -> PurePosixPath:
    p = PurePosixPath(value)
    if not value or p.is_absolute() or '..' in p.parts or '\\' in value or str(p) != value:
        raise ValueError(f'相対パスの形式が不正: {value}')
    return p


def normalize_relative_link(cur_rel: str, target_path: str) -> str | None:
    """cur_rel (POSIX 相対パス) から target_path を正規化する。ルート外は None。"""
    if not target_path:
        return cur_rel
    if target_path.startswith('/') or '\\' in target_path:
        return None
    cur_dir = PurePosixPath(cur_rel).parent
    parts = list(cur_dir.parts) + list(PurePosixPath(target_path).parts)
    norm: list[str] = []
    for part in parts:
        if part in ('', '.'):
            continue
        if part == '..':
            if not norm:
                return None
            norm.pop()
        else:
            norm.append(part)
    return '/'.join(norm)


def github_slug(title: str) -> str:
    """GitHub の Markdown 見出しアンカー規則に沿って slug を生成する。"""
    s = title.strip().lower()
    s = re.sub(r'[`*_]', '', s)
    out: list[str] = []
    for ch in s:
        if ch in (' ', '-'):
            out.append('-')
        elif ch.isalnum() or ch == '_':
            out.append(ch)
    return ''.join(out)


def escape_latex_text(text: str) -> str:
    """LaTeX 通常本文用のエスケープを行う。"""
    out: list[str] = []
    for ch in text:
        if ch == '\\':
            out.append(r'\textbackslash{}')
        elif ch == '{':
            out.append(r'\{')
        elif ch == '}':
            out.append(r'\}')
        elif ch == '#':
            out.append(r'\#')
        elif ch == '$':
            out.append(r'\$')
        elif ch == '%':
            out.append(r'\%')
        elif ch == '&':
            out.append(r'\&')
        elif ch == '_':
            out.append(r'\_')
        elif ch == '~':
            out.append(r'\textasciitilde{}')
        elif ch == '^':
            out.append(r'\textasciicircum{}')
        elif ch == '□':
            out.append(r'$\square$')
        elif ch == '·':
            out.append(r'\textperiodcentered{}')
        else:
            out.append(ch)
    return ''.join(out)


def escape_latex_code(text: str) -> str:
    """インラインコード (\\texttt{...}) 用のエスケープを行う。"""
    return escape_latex_text(text)


def sanitize_ascii_id(raw: str) -> str:
    return re.sub(r'[^A-Za-z0-9:_-]+', '_', raw)


@dataclass
class ChapterEntry:
    chapter_id: str
    rel_path: str
    section_kind: str  # 'front', 'part_chapter', 'appendix'
    part_id: str | None = None


@dataclass
class AnchorIndex:
    doc_labels: dict[str, str] = field(default_factory=dict)
    heading_labels: dict[tuple[str, str], str] = field(default_factory=dict)
    readme_anchors: dict[str, str] = field(default_factory=dict)

    def resolve(self, cur_rel: str, href: str) -> str | None:
        if '#' in href:
            path_part, anchor = href.split('#', 1)
        else:
            path_part, anchor = href, None
        target_rel = normalize_relative_link(cur_rel, path_part)
        if target_rel is None:
            return None
        if target_rel == 'README.md':
            key = anchor or ''
            return self.readme_anchors.get(key)
        if anchor is None:
            return self.doc_labels.get(target_rel)
        return self.heading_labels.get((target_rel, anchor))


@dataclass
class ConversionStats:
    chapters: int = 0
    sections: int = 0
    subsections: int = 0
    declarations: int = 0
    proofs: int = 0
    equations: int = 0
    display_maths: int = 0
    inline_maths: int = 0
    tables: int = 0
    internal_links: int = 0
    stripped_nav_footers: int = 0
    qed_marks: int = 0

    def to_dict(self) -> dict[str, int]:
        return {
            'chapters': self.chapters,
            'sections': self.sections,
            'subsections': self.subsections,
            'declarations': self.declarations,
            'proofs': self.proofs,
            'equations': self.equations,
            'display_maths': self.display_maths,
            'inline_maths': self.inline_maths,
            'tables': self.tables,
            'internal_links': self.internal_links,
            'stripped_nav_footers': self.stripped_nav_footers,
            'qed_marks': self.qed_marks,
        }


def resolve_source_dir(manifest_path: Path, cfg: dict[str, Any], source_override: str | None) -> Path:
    if source_override:
        src = Path(source_override).resolve()
        if not src.is_dir():
            raise ValueError(f'ソースディレクトリが存在しません: {src}')
        return src
    raw = cfg.get('source_dir')
    if not raw:
        raise ValueError('manifest に source_dir が指定されていません')
    rel = relative_posix(raw)
    # manifest_path から上位へたどり、最初に見つかったリポジトリ基準の source_dir を使う
    for base in [Path.cwd().resolve(), *manifest_path.resolve().parents]:
        cand = base / str(rel)
        if cand.is_dir():
            return cand.resolve()
    raise ValueError(f'source_dir が見つかりません: {raw}')


def iter_manifest_chapters(cfg: dict[str, Any]) -> list[ChapterEntry]:
    entries: list[ChapterEntry] = []
    for item in cfg['structure']:
        kind = item['kind']
        if kind == 'chapter':
            entries.append(ChapterEntry(
                chapter_id=item['id'],
                rel_path=str(relative_posix(item['source'])),
                section_kind='front',
            ))
        elif kind == 'part':
            for ch in item['chapters']:
                entries.append(ChapterEntry(
                    chapter_id=ch['id'],
                    rel_path=str(relative_posix(ch['source'])),
                    section_kind='part_chapter',
                    part_id=item['id'],
                ))
        elif kind == 'appendices':
            for ch in item['chapters']:
                entries.append(ChapterEntry(
                    chapter_id=ch['id'],
                    rel_path=str(relative_posix(ch['source'])),
                    section_kind='appendix',
                ))
        else:
            raise ValueError(f'未対応の structure kind: {kind}')
    return entries


def check_no_symlink(path: Path, root: Path) -> None:
    cur = path
    while True:
        if cur.is_symlink():
            raise ValueError(f'symlink は許可されていません: {cur}')
        if cur == root or cur.parent == cur:
            break
        cur = cur.parent


def load_corpus(
    manifest_path: Path,
    preamble_path: Path,
    source_override: str | None = None,
) -> tuple[dict[str, Any], Path, list[ChapterEntry], dict[str, str], dict[str, str], str, list[dict[str, str]]]:
    manifest_path = manifest_path.resolve()
    preamble_path = preamble_path.resolve()
    manifest_bytes = manifest_path.read_bytes()
    preamble_bytes = preamble_path.read_bytes()
    cfg = json.loads(manifest_bytes.decode('utf-8'))
    if cfg.get('schema') != 'aat-monograph-manifest/v1':
        raise ValueError(f"未対応の manifest schema: {cfg.get('schema')}")

    source_dir = resolve_source_dir(manifest_path, cfg, source_override)
    chapters = iter_manifest_chapters(cfg)
    excluded = {str(relative_posix(x)) for x in cfg.get('excluded_files', [])}

    findings: list[dict[str, str]] = []
    seen_ids: set[str] = set()
    seen_paths: set[str] = set()
    texts: dict[str, str] = {}
    originals: dict[str, str] = {}

    for entry in chapters:
        if entry.chapter_id in seen_ids:
            findings.append({'level': 'error', 'file': 'manifest.json', 'message': f'重複 chapter id: {entry.chapter_id}'})
        seen_ids.add(entry.chapter_id)
        if entry.rel_path in seen_paths:
            findings.append({'level': 'error', 'file': 'manifest.json', 'message': f'重複 source: {entry.rel_path}'})
        seen_paths.add(entry.rel_path)
        if entry.rel_path in excluded:
            findings.append({'level': 'error', 'file': 'manifest.json', 'message': f'excluded_files と重複: {entry.rel_path}'})
        path = source_dir / entry.rel_path
        check_no_symlink(path, source_dir)
        if not path.is_file() or not path.resolve().is_relative_to(source_dir):
            findings.append({'level': 'error', 'file': entry.rel_path, 'message': f'マニフェスト記載ファイルが欠落: {entry.rel_path}'})
            continue
        raw = path.read_bytes()
        originals[entry.rel_path] = digest(raw)
        try:
            texts[entry.rel_path] = raw.decode('utf-8')
        except UnicodeDecodeError as exc:
            findings.append({'level': 'error', 'file': entry.rel_path, 'message': f'UTF-8 復号失敗: {exc}'})

    # マニフェスト未登録 .md ファイルの検出
    actual_md = sorted(str(p.relative_to(source_dir).as_posix()) for p in source_dir.rglob('*.md'))
    registered = seen_paths | excluded
    for rel in actual_md:
        if rel not in registered:
            findings.append({'level': 'error', 'file': rel, 'message': f'マニフェスト未登録ファイル: {rel}'})

    identity = {
        'manifest_sha256': digest(manifest_bytes),
        'preamble_sha256': digest(preamble_bytes),
        'original_files': originals,
    }
    source_hash = digest(encoded(identity))
    return cfg, source_dir, chapters, texts, originals, source_hash, findings


def index_anchors(
    cfg: dict[str, Any],
    chapters: list[ChapterEntry],
    texts: dict[str, str],
    findings: list[dict[str, str]],
) -> tuple[AnchorIndex, dict[str, dict[int, str]]]:
    """Pass 1: 全ファイルの見出しとアンカーを索引化する。"""
    index = AnchorIndex(readme_anchors=dict(cfg.get('readme_anchor_map', {})))
    heading_label_by_line: dict[str, dict[int, str]] = {}

    for entry in chapters:
        rel = entry.rel_path
        if rel not in texts:
            continue
        doc_label = f'doc:{sanitize_ascii_id(entry.chapter_id)}'
        index.doc_labels[rel] = doc_label
        line_map: dict[int, str] = {}
        heading_label_by_line[rel] = line_map

        slug_counts: dict[str, int] = {}
        heading_seq = 0
        in_fence = False
        fence_start = 0
        lines = texts[rel].splitlines()
        for lineno, line in enumerate(lines, 1):
            if not in_fence:
                if FENCE_OPEN_RE.match(line):
                    in_fence = True
                    fence_start = lineno
                    continue
            else:
                if FENCE_CLOSE_RE.match(line):
                    in_fence = False
                continue

            m = HEADING_RE.match(line)
            if not m:
                continue
            level = len(m.group(1))
            title = m.group(2).strip()
            base = github_slug(title)
            count = slug_counts.get(base, 0)
            slug_counts[base] = count + 1
            slug = base if count == 0 else f'{base}-{count}'
            if level == 1 and heading_seq == 0:
                lbl = doc_label
            else:
                heading_seq += 1
                lbl = f'sec:{sanitize_ascii_id(entry.chapter_id)}:h{heading_seq:03d}'
            index.heading_labels[(rel, slug)] = lbl
            line_map[lineno] = lbl

        if in_fence:
            findings.append({
                'level': 'error',
                'file': f'{rel}:{fence_start}',
                'message': '未閉じのコード/数式ブロック ```',
            })

    return index, heading_label_by_line


def scan_hygiene(rel: str, text: str, findings: list[dict[str, str]]) -> None:
    for lineno, line in enumerate(text.splitlines(), 1):
        if HIDDEN_RE.search(line):
            findings.append({'level': 'error', 'file': f'{rel}:{lineno}', 'message': 'hidden / bidirectional Unicode'})
        if LOCAL_PATH_RE.search(line):
            findings.append({'level': 'error', 'file': f'{rel}:{lineno}', 'message': 'ローカル絶対パス'})


def find_matching_link_end(text: str, start: int) -> tuple[int, str, str] | None:
    """text[start] == '[' から始まる [label](href) を探す。インライン数式・コード内をスキップ。"""
    n = len(text)
    i = start + 1
    depth = 1
    while i < n:
        if text.startswith('$`', i):
            end = text.find('`$', i + 2)
            if end == -1:
                return None
            i = end + 2
            continue
        if text[i] == '`':
            end = text.find('`', i + 1)
            if end == -1:
                return None
            i = end + 1
            continue
        if text[i] == '[':
            depth += 1
        elif text[i] == ']':
            depth -= 1
            if depth == 0:
                break
        i += 1
    if i >= n or text[i] != ']':
        return None
    label = text[start + 1:i]
    if i + 1 >= n or text[i + 1] != '(':
        return None
    j = i + 2
    pdepth = 1
    while j < n:
        if text[j] == '(':
            pdepth += 1
        elif text[j] == ')':
            pdepth -= 1
            if pdepth == 0:
                break
        j += 1
    if j >= n or text[j] != ')':
        return None
    href = text[i + 2:j].strip()
    return j + 1, label, href


def find_matching_bold_end(text: str, start: int) -> int:
    """text[start:start+2] == '**' に対応する閉じ '**' の開始位置を返す。なければ -1。"""
    n = len(text)
    i = start + 2
    while i < n:
        if text.startswith('$`', i):
            end = text.find('`$', i + 2)
            if end == -1:
                return -1
            i = end + 2
            continue
        if text[i] == '`':
            end = text.find('`', i + 1)
            if end == -1:
                return -1
            i = end + 1
            continue
        if text.startswith('**', i):
            return i
        i += 1
    return -1


def render_inline(
    text: str,
    rel: str,
    lineno: int,
    anchors: AnchorIndex,
    findings: list[dict[str, str]],
    stats: ConversionStats,
    allow_links: bool = True,
) -> str:
    """単一パスでインライン Markdown (数式・コード・リンク・太字・通常文字) を LaTeX へ変換する。"""
    out: list[str] = []
    n = len(text)
    i = 0
    while i < n:
        # 1. GitHub インライン数式 $`...`$
        if text.startswith('$`', i):
            end = text.find('`$', i + 2)
            if end == -1:
                findings.append({
                    'level': 'error',
                    'file': f'{rel}:{lineno}',
                    'message': '未閉じのインライン数式 $`...`$',
                })
                return ''.join(out)
            math_body = text[i + 2:end].strip()
            if not math_body:
                findings.append({
                    'level': 'error',
                    'file': f'{rel}:{lineno}',
                    'message': '空のインライン数式 $``$',
                })
            else:
                stats.inline_maths += 1
                out.append(f'${math_body}$')
            i = end + 2
            continue

        # 2. 単独の $ (未閉じ `$ の残骸や非標準記法を検出)
        if text[i] == '$':
            findings.append({
                'level': 'error',
                'file': f'{rel}:{lineno}',
                'message': '未閉じまたは非標準の $ 記法を検出（$`...`$ を使用してください）',
            })
            out.append(r'\$')
            i += 1
            continue

        # 3. インラインコード `...`
        if text[i] == '`':
            if i + 1 < n and text[i + 1] == '$':
                findings.append({
                    'level': 'error',
                    'file': f'{rel}:{lineno}',
                    'message': '対応する開始 $` のない閉じ `$ を検出',
                })
                i += 2
                continue
            end = text.find('`', i + 1)
            if end == -1:
                findings.append({
                    'level': 'error',
                    'file': f'{rel}:{lineno}',
                    'message': '未閉じのインラインコード `...`',
                })
                return ''.join(out)
            code_body = text[i + 1:end]
            out.append(r'\texttt{' + escape_latex_code(code_body) + '}')
            i = end + 1
            continue

        # 4. 太字 **...**
        if text.startswith('**', i):
            end = find_matching_bold_end(text, i)
            if end == -1:
                findings.append({
                    'level': 'error',
                    'file': f'{rel}:{lineno}',
                    'message': '未閉じの強調 **...**',
                })
                out.append(escape_latex_text('**'))
                i += 2
                continue
            inner = render_inline(text[i + 2:end], rel, lineno, anchors, findings, stats, allow_links=allow_links)
            out.append(r'\textbf{' + inner + '}')
            i = end + 2
            continue

        # 5. Markdown リンク [label](href)
        if allow_links and text[i] == '[':
            parsed = find_matching_link_end(text, i)
            if parsed is not None:
                next_i, label_raw, href = parsed
                label_tex = render_inline(label_raw, rel, lineno, anchors, findings, stats, allow_links=False)
                if href.startswith('http://') or href.startswith('https://'):
                    out.append(r'\href{' + href + '}{' + label_tex + '}')
                else:
                    target_label = anchors.resolve(rel, href)
                    if target_label is None:
                        findings.append({
                            'level': 'error',
                            'file': f'{rel}:{lineno}',
                            'message': f'存在しない相対リンクまたはアンカー: [{label_raw}]({href})',
                        })
                        out.append(label_tex)
                    else:
                        stats.internal_links += 1
                        out.append(r'\hyperref[' + target_label + ']{' + label_tex + '}')
                i = next_i
                continue

        # 6. 通常文字
        out.append(escape_latex_text(text[i]))
        i += 1
    return ''.join(out)


def split_table_row(line: str) -> list[str]:
    """インライン数式・コード内の | を保護しながら Markdown 表の行をセル分割する。"""
    s = line.strip()
    if s.startswith('|'):
        s = s[1:]
    if s.endswith('|'):
        s = s[:-1]
    cells: list[str] = []
    buf: list[str] = []
    i = 0
    n = len(s)
    while i < n:
        if s.startswith('$`', i):
            end = s.find('`$', i + 2)
            if end == -1:
                buf.append(s[i:])
                break
            buf.append(s[i:end + 2])
            i = end + 2
            continue
        if s[i] == '`':
            end = s.find('`', i + 1)
            if end == -1:
                buf.append(s[i:])
                break
            buf.append(s[i:end + 1])
            i = end + 1
            continue
        if s[i] == '|':
            cells.append(''.join(buf).strip())
            buf = []
            i += 1
            continue
        buf.append(s[i])
        i += 1
    cells.append(''.join(buf).strip())
    return cells


def estimate_cell_width(cell: str) -> float:
    """セルの視覚幅を大まかに見積もる（列幅配分用）。"""
    # Markdown リンクはラベル部分だけを残す
    s = re.sub(r'\[([^\]]+)\]\([^)]+\)', r'\1', cell)
    # TeX コマンド名は短く見積もる
    s = re.sub(r'\\[A-Za-z]+', 'X', s)
    s = re.sub(r'[\$`{}]', '', s)
    width = 0.0
    for ch in s:
        width += 1.65 if ord(ch) > 127 else 0.85
    return max(width, 3.0)


def compute_table_colspec(rows: list[list[str]]) -> str:
    ncols = len(rows[0])
    if ncols == 1:
        return 'L'
    scores: list[float] = []
    for c in range(ncols):
        widths = sorted(estimate_cell_width(r[c]) if c < len(r) else 3.0 for r in rows)
        p85 = widths[min(len(widths) - 1, int(len(widths) * 0.85))]
        scores.append(min(max(p85, 5.0), 65.0))

    if ncols == 2:
        total = scores[0] + scores[1]
        w0 = min(max(scores[0] / total, 0.20), 0.40)
        return f'P{{{w0:.2f}\\linewidth}} L'

    if ncols == 3:
        # 最も広い列を L (flexible X)、他2列を比率配分した P{...} にする
        widest = max(range(3), key=lambda idx: scores[idx])
        total = sum(scores)
        other_ratios: dict[int, float] = {}
        for idx in range(3):
            if idx == widest:
                continue
            r = scores[idx] / total
            # 最終列 (定義・参照列) は少しコンパクトに
            lo = 0.14 if idx == 2 else 0.18
            hi = 0.34 if idx == 0 else 0.24
            other_ratios[idx] = min(max(r, lo), hi)
        # 合計が大きすぎないよう調整
        other_sum = sum(other_ratios.values())
        if other_sum > 0.56:
            scale = 0.56 / other_sum
            for idx in other_ratios:
                other_ratios[idx] *= scale
        specs = []
        for idx in range(3):
            if idx == widest:
                specs.append('L')
            else:
                specs.append(f'P{{{other_ratios[idx]:.2f}\\linewidth}}')
        return ' '.join(specs)

    # 4列以上: 全列均等寄りの L / P 構成
    widest = max(range(ncols), key=lambda idx: scores[idx])
    total = sum(scores)
    usable = 0.90 - 0.02 * ncols
    other_ratios = {}
    for idx in range(ncols):
        if idx == widest:
            continue
        r = (scores[idx] / total) * usable
        other_ratios[idx] = min(max(r, 0.10), 0.24)
    if sum(other_ratios.values()) > 0.68:
        scale = 0.68 / sum(other_ratios.values())
        for idx in other_ratios:
            other_ratios[idx] *= scale
    specs = []
    for idx in range(ncols):
        if idx == widest:
            specs.append('L')
        else:
            specs.append(f'P{{{other_ratios[idx]:.2f}\\linewidth}}')
    return ' '.join(specs)


def strip_trailing_nav_footer(lines: list[str], stats: ConversionStats) -> list[str]:
    """章末尾の Markdown ナビゲーション行（[前章] · [全体の構成] · [次章] 等）を除去する。"""
    end = len(lines)
    while end > 0 and not lines[end - 1].strip():
        end -= 1
    if end == 0:
        return lines
    start = end
    while start > 0 and lines[start - 1].strip():
        start -= 1
    joined = ' '.join(l.strip() for l in lines[start:end])
    if NAV_PARA_RE.fullmatch(joined):
        stats.stripped_nav_footers += 1
        return lines[:start]
    return lines


def is_block_start(lines: list[str], idx: int) -> bool:
    line = lines[idx]
    if not line.strip():
        return True
    if HEADING_RE.match(line):
        return True
    if HR_RE.match(line):
        return True
    if FENCE_OPEN_RE.match(line):
        return True
    if EQ_TAG_RE.match(line):
        return True
    if line.startswith('>'):
        return True
    if LIST_ITEM_RE.match(line):
        return True
    if line.startswith('|') and idx + 1 < len(lines) and TABLE_SEP_RE.match(lines[idx + 1]):
        return True
    return False


class ChapterConverter:
    def __init__(
        self,
        entry: ChapterEntry,
        text: str,
        anchors: AnchorIndex,
        heading_line_labels: dict[int, str],
        findings: list[dict[str, str]],
        stats: ConversionStats,
        used_eq_labels: set[str],
    ) -> None:
        self.entry = entry
        self.rel = entry.rel_path
        self.cid = sanitize_ascii_id(entry.chapter_id)
        self.anchors = anchors
        self.heading_line_labels = heading_line_labels
        self.findings = findings
        self.stats = stats
        self.used_eq_labels = used_eq_labels
        self.decl_seq = 0
        self.lines = strip_trailing_nav_footer(text.splitlines(), stats)
        self.n = len(self.lines)

    def convert(self) -> str:
        out: list[str] = []
        i = 0
        saw_h1 = False
        while i < self.n:
            line = self.lines[i]
            if not line.strip():
                i += 1
                continue

            # 見出し
            hm = HEADING_RE.match(line)
            if hm:
                level = len(hm.group(1))
                raw_title = hm.group(2).strip()
                lineno = i + 1
                title_tex = render_inline(raw_title, self.rel, lineno, self.anchors, self.findings, self.stats)
                lbl = self.heading_line_labels.get(lineno, f'sec:{self.cid}:line{lineno}')
                if level == 1 and not saw_h1:
                    saw_h1 = True
                    self.stats.chapters += 1
                    cm = re.match(r'^((?:第\d+章|付録[A-F]))\s+(.*)$', raw_title)
                    if cm:
                        prefix_tex = render_inline(cm.group(1), self.rel, lineno, self.anchors, self.findings, self.stats)
                        rest_tex = render_inline(cm.group(2), self.rel, lineno, self.anchors, self.findings, self.stats)
                        title_tex = f'{prefix_tex}\\texorpdfstring{{\\enspace }}{{ }}{rest_tex}'
                    out.append(f'\\aatchapter{{{lbl}}}{{{title_tex}}}')
                elif level == 2:
                    self.stats.sections += 1
                    out.append(f'\\aatsection{{{lbl}}}{{{title_tex}}}')
                elif level == 3:
                    self.stats.subsections += 1
                    out.append(f'\\aatsubsection{{{lbl}}}{{{title_tex}}}')
                else:
                    out.append(f'\\paragraph*{{{title_tex}}}')
                i += 1
                continue

            # 水平線
            if HR_RE.match(line):
                out.append(r'\aathrule')
                i += 1
                continue

            # 独立式番号 **式(X.Y)** (+ 後続 ```math)
            eqm = EQ_TAG_RE.match(line)
            if eqm:
                tag_str = eqm.group(1)
                j = i + 1
                while j < self.n and not self.lines[j].strip():
                    j += 1
                if j < self.n:
                    fm = FENCE_OPEN_RE.match(self.lines[j])
                    if fm and fm.group(2) == 'math':
                        math_lines, next_i = self._consume_fence(j)
                        self.stats.equations += 1
                        eq_label = self._unique_eq_label(tag_str)
                        body = '\n'.join(math_lines).strip()
                        out.append(
                            f'\\begin{{equation}}\n\\label{{{eq_label}}}\\tag{{{tag_str}}}\n'
                            f'\\aatfitmath{{0.86\\linewidth}}{{\n{body}\n}}\n\\end{{equation}}'
                        )
                        i = next_i
                        continue
                # 万一 ```math が続かない場合でも欠落させず出力
                self.stats.equations += 1
                out.append(f'\\par\\noindent\\textbf{{式({escape_latex_text(tag_str)})}}\\par')
                i += 1
                continue

            # コード/数式ブロック
            fm = FENCE_OPEN_RE.match(line)
            if fm:
                lang = fm.group(2)
                block_lines, next_i = self._consume_fence(i)
                out.append(self._format_fence(lang, block_lines))
                i = next_i
                continue

            # 表
            if line.startswith('|') and i + 1 < self.n and TABLE_SEP_RE.match(self.lines[i + 1]):
                table_tex, next_i = self._consume_table(i)
                out.append(table_tex)
                i = next_i
                continue

            # 引用
            if line.startswith('>'):
                quote_tex, next_i = self._consume_blockquote(i)
                out.append(quote_tex)
                i = next_i
                continue

            # リスト
            lm = LIST_ITEM_RE.match(line)
            if lm:
                list_tex, next_i = self._consume_list(i, len(lm.group(1)), lm.group(2) in ('-', '*'))
                out.append(list_tex)
                i = next_i
                continue

            # 段落 (宣言 / 証明 / 通常段落)
            para_tex, next_i = self._consume_paragraph(i)
            out.append(para_tex)
            i = next_i

        if not saw_h1:
            self.findings.append({
                'level': 'error',
                'file': self.rel,
                'message': '章見出し (# ...) が存在しません',
            })
        return '\n\n'.join(out) + '\n'

    def _unique_eq_label(self, tag_str: str) -> str:
        base = f'eq:{sanitize_ascii_id(tag_str)}'
        lbl = base
        suffix = 1
        while lbl in self.used_eq_labels:
            suffix += 1
            lbl = f'{base}_{suffix}'
        self.used_eq_labels.add(lbl)
        return lbl

    def _consume_fence(self, start: int) -> tuple[list[str], int]:
        i = start + 1
        buf: list[str] = []
        while i < self.n:
            if FENCE_CLOSE_RE.match(self.lines[i]):
                return buf, i + 1
            buf.append(self.lines[i])
            i += 1
        # Pass 1 でも検出済みだが安全のため二重検出を避けつつ終端まで返す
        return buf, self.n

    def _format_fence(self, lang: str, block_lines: list[str]) -> str:
        # インデント付きブロックの共通先頭空白を整える
        non_empty = [l for l in block_lines if l.strip()]
        indent = min((len(l) - len(l.lstrip(' ')) for l in non_empty), default=0)
        dedented = [l[indent:] if len(l) >= indent else l for l in block_lines]
        body = '\n'.join(dedented).strip()
        if lang == 'math':
            self.stats.display_maths += 1
            return f'\\[\n\\aatfitmath{{0.98\\linewidth}}{{\n{body}\n}}\n\\]'
        return f'\\begin{{verbatim}}\n{body}\n\\end{{verbatim}}'

    def _consume_table(self, start: int) -> tuple[str, int]:
        header = split_table_row(self.lines[start])
        ncols = len(header)
        raw_rows: list[list[str]] = [header]
        row_linenos: list[int] = [start + 1]
        i = start + 2
        while i < self.n and self.lines[i].startswith('|'):
            cells = split_table_row(self.lines[i])
            if len(cells) < ncols:
                cells += [''] * (ncols - len(cells))
            elif len(cells) > ncols:
                cells = cells[:ncols]
            raw_rows.append(cells)
            row_linenos.append(i + 1)
            i += 1

        self.stats.tables += 1
        colspec = compute_table_colspec(raw_rows)
        rendered_rows: list[str] = []
        for r_idx, cells in enumerate(raw_rows):
            ln = row_linenos[r_idx]
            rendered = [
                render_inline(c, self.rel, ln, self.anchors, self.findings, self.stats)
                for c in cells
            ]
            if r_idx == 0:
                rendered = [r'\textbf{' + c + '}' for c in rendered]
            rendered_rows.append(' & '.join(rendered) + r' \\')

        font_cmd = r'\small' if ncols >= 4 else r'\normalsize'
        lines_out = [
            '{',
            font_cmd,
            f'\\begin{{xltabular}}{{\\linewidth}}{{{colspec}}}',
            r'\toprule',
            rendered_rows[0],
            r'\midrule',
            r'\endhead',
            r'\bottomrule',
            r'\endfoot',
        ]
        lines_out.extend(rendered_rows[1:])
        lines_out.append(r'\end{xltabular}')
        lines_out.append('}')
        return '\n'.join(lines_out), i

    def _consume_blockquote(self, start: int) -> tuple[str, int]:
        buf: list[str] = []
        i = start
        while i < self.n and self.lines[i].startswith('>'):
            buf.append(re.sub(r'^>\s?', '', self.lines[i]))
            i += 1
        rendered = render_inline('\n'.join(buf), self.rel, start + 1, self.anchors, self.findings, self.stats)
        return f'\\begin{{quote}}\n{rendered}\n\\end{{quote}}', i

    def _consume_list(self, start: int, base_indent: int, is_unordered: bool) -> tuple[str, int]:
        env = 'itemize' if is_unordered else 'enumerate'
        items: list[str] = []
        i = start
        while i < self.n:
            line = self.lines[i]
            if not line.strip():
                # 次行が同じリストまたは子要素・継続段落なら続行、そうでなければ終了
                j = i + 1
                while j < self.n and not self.lines[j].strip():
                    j += 1
                if j >= self.n:
                    i = j
                    break
                nxt = self.lines[j]
                nm = LIST_ITEM_RE.match(nxt)
                if nm and len(nm.group(1)) == base_indent and (nm.group(2) in ('-', '*')) == is_unordered:
                    i = j
                    continue
                if len(nxt) - len(nxt.lstrip(' ')) > base_indent:
                    i = j
                    continue
                break

            lm = LIST_ITEM_RE.match(line)
            if not lm:
                break
            indent = len(lm.group(1))
            ul = lm.group(2) in ('-', '*')
            if indent < base_indent or (indent == base_indent and ul != is_unordered):
                break
            if indent > base_indent:
                # 異常な飛び出しインデントは直前項目へぶら下げる
                sub_tex, i = self._consume_list(i, indent, ul)
                if items:
                    items[-1] += '\n' + sub_tex
                continue

            # 項目先頭行
            first_text = lm.group(3)
            item_parts: list[str] = [
                render_inline(first_text, self.rel, i + 1, self.anchors, self.findings, self.stats)
            ]
            i += 1

            # 項目内の継続行・インデント済み数式ブロック・ネストしたリストを回収
            para_buf: list[tuple[int, str]] = []

            def flush_para_buf() -> None:
                if not para_buf:
                    return
                first_ln = para_buf[0][0]
                joined = '\n'.join(t for _, t in para_buf)
                item_parts.append(
                    '\n\n' + render_inline(joined, self.rel, first_ln, self.anchors, self.findings, self.stats)
                )
                para_buf.clear()

            while i < self.n:
                cur = self.lines[i]
                if not cur.strip():
                    j = i + 1
                    while j < self.n and not self.lines[j].strip():
                        j += 1
                    if j >= self.n:
                        i = j
                        break
                    nxt = self.lines[j]
                    nxt_indent = len(nxt) - len(nxt.lstrip(' '))
                    if nxt_indent > base_indent:
                        flush_para_buf()
                        i = j
                        continue
                    break

                cur_indent = len(cur) - len(cur.lstrip(' '))
                if cur_indent <= base_indent:
                    break

                sub_lm = LIST_ITEM_RE.match(cur)
                if sub_lm:
                    flush_para_buf()
                    sub_tex, i = self._consume_list(i, len(sub_lm.group(1)), sub_lm.group(2) in ('-', '*'))
                    item_parts.append('\n' + sub_tex)
                    continue

                sub_fm = FENCE_OPEN_RE.match(cur)
                if sub_fm:
                    flush_para_buf()
                    block_lines, i = self._consume_fence(i)
                    item_parts.append('\n' + self._format_fence(sub_fm.group(2), block_lines))
                    continue

                # 継続テキスト
                stripped = cur.strip()
                if len(item_parts) == 1 and not para_buf and i > start and self.lines[i - 1].strip():
                    # 直前行から空行なしで続く折り返し行
                    item_parts[0] += '\n' + render_inline(stripped, self.rel, i + 1, self.anchors, self.findings, self.stats)
                else:
                    para_buf.append((i + 1, stripped))
                i += 1

            flush_para_buf()
            items.append(r'\item ' + ''.join(item_parts))

        body = '\n'.join(items)
        return f'\\begin{{{env}}}\n{body}\n\\end{{{env}}}', i

    def _consume_paragraph(self, start: int) -> tuple[str, int]:
        para_lines: list[str] = [self.lines[start]]
        i = start + 1
        while i < self.n and not is_block_start(self.lines, i):
            para_lines.append(self.lines[i])
            i += 1
        raw = '\n'.join(para_lines)
        lineno = start + 1

        # 末尾 □ の検出
        has_qed = False
        if raw.rstrip().endswith('□'):
            has_qed = True
            raw = raw.rstrip()[:-1].rstrip()
            self.stats.qed_marks += 1

        # 番号付き宣言 (**定理11.5a（...）.** 等)
        dm = DECL_START_RE.match(raw)
        if dm:
            self.decl_seq += 1
            self.stats.declarations += 1
            decl_title_raw = dm.group(1)
            decl_rest = dm.group(2).lstrip()
            decl_label = f'decl:{self.cid}:d{self.decl_seq:03d}'
            title_tex = render_inline(decl_title_raw, self.rel, lineno, self.anchors, self.findings, self.stats)
            if not decl_rest:
                res = f'\\aatdeclstandalone{{{decl_label}}}{{{title_tex}}}'
            else:
                rest_tex = render_inline(decl_rest, self.rel, lineno, self.anchors, self.findings, self.stats)
                res = f'\\aatdecl{{{decl_label}}}{{{title_tex}}}\n{rest_tex}'
            if has_qed:
                res += r'\aatqed'
            return res, i

        # 証明 (**証明.** / **構成と証明.** 等)
        pm = PROOF_START_RE.match(raw)
        if pm:
            self.stats.proofs += 1
            proof_title_raw = pm.group(1)
            proof_rest = pm.group(2).lstrip()
            title_tex = render_inline(proof_title_raw, self.rel, lineno, self.anchors, self.findings, self.stats)
            if not proof_rest:
                res = f'\\aatproofstandalone{{{title_tex}}}'
            else:
                rest_tex = render_inline(proof_rest, self.rel, lineno, self.anchors, self.findings, self.stats)
                res = f'\\aatproof{{{title_tex}}}\n{rest_tex}'
            if has_qed:
                res += r'\aatqed'
            return res, i

        rendered = render_inline(raw, self.rel, lineno, self.anchors, self.findings, self.stats)
        if has_qed:
            rendered += r'\aatqed'
        return rendered, i


def build_tex_bundle(
    manifest_path: Path,
    preamble_path: Path,
    source_override: str | None = None,
) -> tuple[dict[str, Any], dict[str, bytes], dict[str, str], str, list[dict[str, str]], ConversionStats]:
    cfg, _source_dir, chapters, texts, originals, source_hash, findings = load_corpus(
        manifest_path, preamble_path, source_override
    )
    for entry in chapters:
        if entry.rel_path in texts:
            scan_hygiene(entry.rel_path, texts[entry.rel_path], findings)

    anchors, heading_line_labels = index_anchors(cfg, chapters, texts, findings)
    stats = ConversionStats()
    used_eq_labels: set[str] = set()

    tex_files: dict[str, bytes] = {}
    preamble_text = preamble_path.read_text(encoding='utf-8')
    tex_files['preamble.tex'] = preamble_text.encode('utf-8')

    chapter_tex_by_id: dict[str, str] = {}
    for entry in chapters:
        if entry.rel_path not in texts:
            continue
        conv = ChapterConverter(
            entry=entry,
            text=texts[entry.rel_path],
            anchors=anchors,
            heading_line_labels=heading_line_labels.get(entry.rel_path, {}),
            findings=findings,
            stats=stats,
            used_eq_labels=used_eq_labels,
        )
        tex_body = conv.convert()
        rel_tex = f'chapters/{sanitize_ascii_id(entry.chapter_id)}.tex'
        chapter_tex_by_id[entry.chapter_id] = rel_tex
        tex_files[rel_tex] = tex_body.encode('utf-8')

    # main.tex 組み立て
    title_tex = escape_latex_text(cfg['title'])
    subtitle_tex = escape_latex_text(cfg.get('subtitle', ''))
    main_lines = [
        '% Auto-generated from docs/aat/algebraic_geometric_theory/ -- DO NOT EDIT DIRECTLY.',
        r'\input{preamble.tex}',
        r'\begin{document}',
        f'\\aattitlepage{{{title_tex}}}{{{subtitle_tex}}}',
        r'\aattoc',
    ]
    for item in cfg['structure']:
        kind = item['kind']
        if kind == 'chapter':
            cid = item['id']
            if cid in chapter_tex_by_id:
                main_lines.append(f'\\input{{{chapter_tex_by_id[cid]}}}')
        elif kind == 'part':
            lbl = item['label']
            pnum = escape_latex_text(item['part_num'])
            ptitle = escape_latex_text(item['title'])
            psub = escape_latex_text(item.get('subtitle', ''))
            main_lines.append(f'\\aatpart{{{lbl}}}{{{pnum}}}{{{ptitle}}}{{{psub}}}')
            for ch in item['chapters']:
                cid = ch['id']
                if cid in chapter_tex_by_id:
                    main_lines.append(f'\\input{{{chapter_tex_by_id[cid]}}}')
        elif kind == 'appendices':
            main_lines.append(r'\aatappendices')
            for ch in item['chapters']:
                cid = ch['id']
                if cid in chapter_tex_by_id:
                    main_lines.append(f'\\input{{{chapter_tex_by_id[cid]}}}')
    main_lines.append(r'\end{document}')
    main_name = str(relative_posix(cfg.get('main', 'aat_monograph.tex')))
    tex_files[main_name] = ('\n'.join(main_lines) + '\n').encode('utf-8')

    # 生成 TeX に対する静的検査 (paper.py の規律と整合)
    static_check_generated_tex(tex_files, findings)
    return cfg, tex_files, originals, source_hash, findings, stats


def uncomment_tex(text: str) -> str:
    return re.sub(r'(?<!\\)%[^\n]*', '', text)


def static_check_generated_tex(tex_files: dict[str, bytes], findings: list[dict[str, str]]) -> None:
    labels: list[str] = []
    hyperrefs: list[tuple[str, str]] = []
    # preamble の \aatpart / \aatchapter / \aatsection / \aatsubsection / \aatdecl / \aatdeclstandalone も \label を定義する
    macro_label_re = re.compile(
        r'\\(?:aatpart|aatchapter|aatsection|aatsubsection|aatdecl|aatdeclstandalone)\{([^}]+)\}'
    )
    for name, raw in tex_files.items():
        if not name.endswith('.tex'):
            continue
        text = raw.decode('utf-8')
        for lineno, line in enumerate(text.splitlines(), 1):
            if HIDDEN_RE.search(line):
                findings.append({'level': 'error', 'file': f'{name}:{lineno}', 'message': '生成 TeX に hidden / bidirectional Unicode'})
            if LOCAL_PATH_RE.search(line):
                findings.append({'level': 'error', 'file': f'{name}:{lineno}', 'message': '生成 TeX にローカル絶対パス'})
        body = uncomment_tex(text)
        if name == 'preamble.tex':
            # \aattoc 内の doc:toc のみ固定登録
            labels.extend(re.findall(r'\\label\{([A-Za-z0-9:_-]+)\}', body))
            continue
        labels.extend(re.findall(r'\\label\{([^}]+)\}', body))
        labels.extend(macro_label_re.findall(body))
        for target in re.findall(r'\\hyperref\[([^\]]+)\]', body):
            hyperrefs.append((name, target))
        for target in re.findall(r'\\(?:ref|eqref|pageref)\*?\{([^}]+)\}', body):
            hyperrefs.append((name, target))

    label_counts: dict[str, int] = {}
    for lbl in labels:
        label_counts[lbl] = label_counts.get(lbl, 0) + 1
    for lbl, cnt in sorted(label_counts.items()):
        if cnt > 1:
            findings.append({'level': 'error', 'file': 'labels', 'message': f'重複 label: {lbl}'})
    label_set = set(label_counts)
    for name, target in hyperrefs:
        if target not in label_set:
            findings.append({'level': 'error', 'file': name, 'message': f'未定義 label 参照: {target}'})


def analyze_tex_log(log_text: str) -> dict[str, Any]:
    """TeX ビルドログからエラー・未定義参照・未定義制御列・文字欠落・行幅警告を抽出する。"""
    errors: list[str] = []
    error_patterns = [
        re.compile(r'^! [A-Za-z]'),
        re.compile(r'Undefined control sequence', re.I),
        re.compile(r'There were undefined references', re.I),
        re.compile(r'Reference `[^\']*\' on page .* undefined', re.I),
        re.compile(r'Citation `[^\']*\' on page .* undefined', re.I),
        re.compile(r'multiply defined', re.I),
        re.compile(r'Missing character:', re.I),
        re.compile(r'destination with the same identifier', re.I),
        re.compile(r'LaTeX Error:', re.I),
        re.compile(r'Fatal error occurred', re.I),
    ]
    for line in log_text.splitlines():
        if any(pat.search(line) for pat in error_patterns):
            errors.append(line.strip())
    overfull = re.findall(r'Overfull[^\n]*', log_text)
    underfull_count = len(re.findall(r'Underfull', log_text))
    return {
        'errors': errors,
        'overfull': overfull,
        'underfull_count': underfull_count,
    }


def prepare_output(out: Path, data: dict[str, bytes]) -> Path:
    out = out.resolve()
    if out.exists():
        raise ValueError(f'既存の出力先を上書きしません: {out}')
    out.mkdir(parents=True)
    for name, raw in data.items():
        dest = out / name
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(raw)
    return out


def run_cmd(argv: list[str], cwd: Path) -> tuple[int, str]:
    result = subprocess.run(argv, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    return result.returncode, result.stdout


def inspect_pdf_text(pdf_path: Path, findings: list[dict[str, str]]) -> dict[str, Any]:
    if not shutil.which('pdftotext'):
        return {'checked': False, 'reason': 'pdftotext not found'}
    code, output = run_cmd(['pdftotext', str(pdf_path), '-'], pdf_path.parent)
    if code != 0:
        findings.append({'level': 'error', 'file': 'PDF', 'message': 'pdftotext による抽出に失敗'})
        return {'checked': False, 'reason': 'pdftotext failed'}
    if not output.strip():
        findings.append({'level': 'error', 'file': 'PDF', 'message': 'PDF テキストが空です'})
    for pat, msg in [
        (HIDDEN_RE, 'PDF テキストに不可視文字候補'),
        (LOCAL_PATH_RE, 'PDF テキストにローカル絶対パス'),
        (re.compile(r'\?\?'), 'PDF テキストに未解決参照候補 (??)'),
    ]:
        if pat.search(output):
            findings.append({'level': 'error', 'file': 'PDF', 'message': msg})
    return {'checked': True, 'char_count': len(output)}


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('action', choices=['check', 'generate', 'build'])
    ap.add_argument('--manifest', default=str(DEFAULT_MANIFEST), help='モノグラフ構成マニフェスト JSON')
    ap.add_argument('--preamble', default=str(DEFAULT_PREAMBLE), help='LaTeX プリアンブルファイル')
    ap.add_argument('--source', help='数学本文 Markdown ディレクトリの上書き指定')
    ap.add_argument('--out', help='新しい出力ディレクトリ (generate / build 必須、既存上書き不可)')
    ap.add_argument('--engine', choices=['tectonic', 'xelatex'], default='tectonic')
    ap.add_argument('--allow-network', action='store_true', help='Tectonic 初回キャッシュ取得時に --only-cached を外す')
    ap.add_argument('--pdf', help='完成 PDF の抽出テキスト・ハッシュ照合 (check のみ)')
    ap.add_argument('--build-record', help='PDF の生成記録 JSON (省略時は PDF の親の親/build.json)')
    args = ap.parse_args(argv)

    manifest_path = Path(args.manifest).resolve()
    preamble_path = Path(args.preamble).resolve()
    cfg, tex_files, originals, source_hash, findings, stats = build_tex_bundle(
        manifest_path, preamble_path, args.source
    )

    report: dict[str, Any] = {
        'schema': 'aat-monograph-check/v1',
        'source_sha256': source_hash,
        'original_files': originals,
        'generated_files': {k: digest(v) for k, v in sorted(tex_files.items())},
        'tool_sha256': digest(Path(__file__).read_bytes()),
        'stats': stats.to_dict(),
        'findings': findings,
    }

    if args.pdf:
        if args.action != 'check':
            raise ValueError('--pdf は check のみ指定できます')
        pdf = Path(args.pdf).resolve()
        if not pdf.is_file():
            raise ValueError(f'PDF が存在しません: {pdf}')
        report['pdf_sha256'] = digest(pdf.read_bytes())
        rec_path = Path(args.build_record) if args.build_record else pdf.parent.parent / 'build.json'
        if not rec_path.is_file():
            raise ValueError(f'build.json が見つかりません: {rec_path}')
        record = json.loads(rec_path.read_text(encoding='utf-8'))
        if record.get('pdf_sha256') != report['pdf_sha256'] or record.get('source_sha256') != source_hash:
            findings.append({'level': 'error', 'file': 'PDF', 'message': '生成記録の PDF/source hash 不一致'})
        report['pdf_text_check'] = inspect_pdf_text(pdf, findings)

    if args.action == 'check':
        print(encoded(report).decode('utf-8'), end='')
        return int(bool(findings))

    if not args.out:
        raise ValueError('--out を指定してください')
    if findings:
        print(encoded(report).decode('utf-8'), end='')
        return 1

    out = Path(args.out).resolve()
    if args.action == 'generate':
        prepare_output(out, tex_files)
        (out / 'generate.json').write_bytes(encoded(report))
        print(encoded({
            'action': 'generate',
            'out': str(out),
            'source_sha256': source_hash,
            'stats': stats.to_dict(),
        }).decode('utf-8'), end='')
        return 0

    # action == 'build'
    engine_bin = shutil.which(args.engine)
    if not engine_bin:
        raise ValueError(f'TeX 処理系が見つかりません: {args.engine}')
    code, version = run_cmd([engine_bin, '--version'], Path.cwd())
    expected = cfg['environment']['tectonic'] if args.engine == 'tectonic' else f"TeX Live {cfg['environment']['texlive']}"
    if code != 0 or expected not in version:
        first_line = version.splitlines()[0] if version else ''
        raise ValueError(f'処理系の版不一致: expected {expected}; got {first_line}')

    if args.engine == 'xelatex':
        kcode, texroot = run_cmd(['kpsewhich', '--var-value=TEXMFROOT'], Path.cwd())
        tlpdb = Path(texroot.strip()) / 'tlpkg/texlive.tlpdb'
        if kcode != 0 or not tlpdb.is_file():
            raise ValueError('TeX Live package inventory を取得できません')
        report['texlive_packages_sha256'] = digest(tlpdb.read_bytes())

    main_tex = str(relative_posix(cfg.get('main', 'aat_monograph.tex')))
    stem = Path(main_tex).stem
    prepare_output(out, {})
    source_out = prepare_output(out / 'source', tex_files)
    build_out = out / 'build'
    build_out.mkdir()

    if args.engine == 'tectonic':
        cmd = [engine_bin, '--untrusted']
        if not args.allow_network:
            cmd.append('--only-cached')
        cmd.extend(['--keep-logs', '--keep-intermediates', '--outdir', str(build_out), main_tex])
        commands = [cmd]
    else:
        tex_cmd = [engine_bin, '-interaction=nonstopmode', '-halt-on-error', '-no-shell-escape', main_tex]
        commands = [tex_cmd, tex_cmd, tex_cmd]

    process_log = ''
    exit_code = 0
    for cmd in commands:
        exit_code, output = run_cmd(cmd, source_out)
        process_log += output
        if exit_code != 0:
            break

    if args.engine == 'xelatex':
        for suffix in ('.pdf', '.log'):
            p = source_out / (stem + suffix)
            if p.exists():
                shutil.copy2(p, build_out / p.name)

    (out / 'process.log').write_text(process_log, encoding='utf-8')
    pdf = build_out / (stem + '.pdf')
    texlog = build_out / (stem + '.log')
    final_log = texlog.read_text(encoding='utf-8', errors='replace') if texlog.exists() else ''
    log_analysis = analyze_tex_log(final_log)

    pdf_findings: list[dict[str, str]] = []
    pdf_text_info: dict[str, Any] = {'checked': False}
    if pdf.exists() and exit_code == 0:
        pdf_text_info = inspect_pdf_text(pdf, pdf_findings)

    # ビルド中の入力変更を検知
    _, _, _, _, _, post_hash, _ = load_corpus(manifest_path, preamble_path, args.source)
    changed_during = post_hash != source_hash

    report.update({
        'schema': 'aat-monograph-build/v1',
        'engine': args.engine,
        'version': version.splitlines()[0] if version else '',
        'executable_sha256': digest(Path(engine_bin).read_bytes()),
        'platform': platform.platform(),
        'python': platform.python_version(),
        'exit_code': exit_code,
        'log_errors': log_analysis['errors'],
        'overfull': log_analysis['overfull'],
        'overfull_count': len(log_analysis['overfull']),
        'underfull_count': log_analysis['underfull_count'],
        'pdf_sha256': digest(pdf.read_bytes()) if pdf.exists() else None,
        'pdf_text_check': pdf_text_info,
        'pdf_findings': pdf_findings,
        'source_changed_during_build': changed_during,
    })
    (out / 'build.json').write_bytes(encoded(report))

    summary = {
        'engine': report['engine'],
        'exit_code': report['exit_code'],
        'log_errors': report['log_errors'],
        'overfull_count': report['overfull_count'],
        'underfull_count': report['underfull_count'],
        'pdf_sha256': report['pdf_sha256'],
        'pdf_text_check': report['pdf_text_check'],
        'pdf_findings': report['pdf_findings'],
        'stats': report['stats'],
        'source_changed_during_build': report['source_changed_during_build'],
    }
    print(encoded(summary).decode('utf-8'), end='')
    failed = bool(
        exit_code
        or not pdf.exists()
        or log_analysis['errors']
        or pdf_findings
        or changed_during
    )
    return int(failed)


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (ValueError, KeyError, OSError, json.JSONDecodeError) as exc:
        print(f'monograph: {exc}', file=sys.stderr)
        sys.exit(2)
