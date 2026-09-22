#!/usr/bin/env python3
"""Rising Sea 論文の日本語原稿(ja/*.md)と英語 TeX 原稿(en/*.tex)を照合する。

skeleton: 日本語原稿の見出し・番号付き項目・数式・表・リンク・相互参照を TeX へ移し、
          地の文を日本語のまま残した翻訳用の骨組みを出力する。
check:    日英の数式・番号・相互参照・リンクの一致と、英語原稿の ASCII 性を検査する。
          --aux を渡すと、組版後の番号がラベルの番号と一致することも確かめる。
pending:  英語原稿が参照し、未翻訳のパートにある番号を仮ラベルとして出力する。

Python 3.10+ / 標準ライブラリ。
"""
import argparse
import collections
import csv
import re
import sys
import unicodedata
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
JA, EN = ROOT / 'ja', ROOT / 'en'

# 日本語の項目名 -> (TeX 環境, ラベル接頭辞, 英語名, 英語複数形)
KINDS = {
    '定義': ('definition', 'def', 'Definition', 'Definitions'),
    '命題': ('proposition', 'prop', 'Proposition', 'Propositions'),
    '定理': ('theorem', 'thm', 'Theorem', 'Theorems'),
    '補題': ('lemma', 'lem', 'Lemma', 'Lemmas'),
    '系': ('corollary', 'cor', 'Corollary', 'Corollaries'),
    '例': ('example', 'ex', 'Example', 'Examples'),
    '構成': ('construction', 'cons', 'Construction', 'Constructions'),
}
ENV_PREFIX = {env: prefix for env, prefix, _, _ in KINDS.values()}
PROOFS = {'証明': None, '構成と証明': 'Construction and proof', '証明と構成': 'Proof and construction'}

# 準備節 P.5 は番号の付け方を例示する。例示の番号は相互参照ではない。
EXEMPT_REFS = {
    '03-preliminaries-and-notation': {'def:2.1', 'prop:2.2', 'def:2.3', 'sec:2.1', 'eq:2.1', 'fig:2.1', 'tab:2.1'},
}

NUM = r'\d+\.\d+(?![.\d])'
SECNUM = r'(?:[PRA-C]|\d+)\.\d+(?![.\d])'
ITEM_REF = re.compile(rf'({"|".join(KINDS)})({NUM})((?:[・/](?:{NUM}))*)(?:[–](({NUM})))?')
SEC_REF = re.compile(rf'(§§?)({SECNUM})(?:[–]({SECNUM}))?((?:[・,]\s*{SECNUM})*)')
CHAP_REF = re.compile(r'第(\d+(?:[・〜]\d+)*)章')
EQ_REF = re.compile(rf'式\(({NUM})\)(?:[–]\(({NUM})\))?')
FIG_REF = re.compile(rf'(図|表)({NUM})')
APP_REF = re.compile(r'付録([A-C])(?![A-Za-z])')

MD_INLINE = re.compile(r'\$`(.*?)`\$', re.S)
MD_BLOCK = re.compile(r'^```math\n(.*?)^```', re.S | re.M)
TAG = re.compile(r'\s*\\q?quad\s*\\text\{\((' + SECNUM + r')\)\}\s*$')
CJK = re.compile(r'[\u3000-\u30ff\u3400-\u9fff\uff00-\uffef]')
LINK = re.compile(r'\[((?:[^\[\]]|\[[^\[\]]*\])*)\]\(([^()\s]+(?:\([^()\s]*\)[^()\s]*)*)\)')
URL_MD = re.compile(r'\]\((https?://[^\s)]+(?:\([^\s)]*\)[^\s)]*)*)\)|<(https?://[^>\s]+)>')


# ---------------------------------------------------------------- 数式

UNI = re.compile(r'^(?:MATHEMATICAL )?(SCRIPT|DOUBLE-STRUCK|FRAKTUR|BOLD) (CAPITAL|SMALL) ([A-Z])$')
STYLE = {'SCRIPT': 'mathcal', 'DOUBLE-STRUCK': 'mathbb', 'FRAKTUR': 'mathfrak', 'BOLD': 'mathbf'}


def unicode_math(s):
    """GitHub 表示用の Unicode 数学英字を TeX の字体命令へ戻す。連続する同字体はまとめる。"""
    out, run, style = [], [], None
    def flush():
        if run:
            out.append(f'\\{STYLE[style]}{{{"".join(run)}}}')
            run.clear()
    for c in s:
        m = UNI.match(unicodedata.name(c, ''))
        if m and not (m[1] == 'SCRIPT' and m[2] == 'SMALL'):
            letter = m[3] if m[2] == 'CAPITAL' else m[3].lower()
            if style != m[1]:
                flush()
                style = m[1]
            run.append(letter)
        else:
            flush()
            style = None
            out.append(c)
    flush()
    return ''.join(out)


def split_tag(body):
    m = TAG.search(body)
    return (body[:m.start()], m[1]) if m else (body, None)


def canon(s):
    """空白と、英文の句読点として式末尾に置く . , ; を除いて比べる。"""
    s = re.sub(r'\s+', ' ', s).strip()
    s = re.sub(r'(?<![A-Za-z]) | (?![A-Za-z])', '', s)
    return re.sub(r'[.,;]+$', '', s)


def mask_text(s):
    return re.sub(r'\\text\{[^{}]*\}', r'\\text{}', s)


def ja_math(md):
    items = [unicode_math(m) for m in MD_INLINE.findall(md)]
    tags = []
    for body in MD_BLOCK.findall(md):
        body, tag = split_tag(body)
        items.append(unicode_math(body))
        if tag:
            tags.append(tag)
    return items, tags


def strip_comments(tex):
    return re.sub(r'(?<!\\)%[^\n]*', '', tex)


def en_math(tex):
    tex = strip_comments(tex)
    items, tags, bad = [], [], []
    def display(m):
        body = m.group('body')
        found = re.findall(r'\\tag\{([^}]*)\}', body)
        labels = re.findall(r'\\label\{([^}]*)\}', body)
        for t in found:
            tags.append(t)
            if f'eq:{t}' not in labels:
                bad.append(f'\\tag{{{t}}} に \\label{{eq:{t}}} がない')
        items.append(re.sub(r'\\(?:tag|label)\{[^}]*\}', '', body))
        return ' '
    tex = re.sub(r'\\begin\{(equation\*?)\}(?P<body>.*?)\\end\{\1\}', display, tex, flags=re.S)
    tex = re.sub(r'\\\[(?P<body>.*?)\\\]', display, tex, flags=re.S)
    items += re.findall(r'(?<![\\$])\$(?!\$)(.+?)(?<!\\)\$', tex, re.S)
    return items, tags, bad


# ---------------------------------------------------------------- 番号と参照

def ja_items(md):
    pat = re.compile(rf'^\*\*({"|".join(KINDS)})({NUM})', re.M)
    return [(KINDS[k][1] + ':' + n, k) for k, n in pat.findall(md)]


def ja_sections(md):
    labels = [f'sec:{n}' for n in re.findall(rf'^## ({SECNUM}) ', md, re.M)]
    labels += [f'chap:{n}' for n in re.findall(r'^# 第(\d+)章', md, re.M)]
    labels += [f'fig:{n}' for n in re.findall(rf'^\*\*図({NUM})：', md, re.M)]
    labels += [f'app:{n}' for n in re.findall(r'^# 付録([A-C]) ', md, re.M)]
    return labels


def all_kinds():
    """全パートの番号付き項目: 番号 -> ラベル接頭辞。"""
    table = {}
    for path in sorted(JA.glob('*.md')):
        for label, _ in ja_items(path.read_text()):
            prefix, n = label.split(':')
            table[n] = prefix
    return table


def join_refs(parts):
    if len(parts) == 1:
        return parts[0]
    if len(parts) == 2:
        return f'{parts[0]} and~{parts[1]}'
    return ', '.join(parts[:-1]) + f', and~{parts[-1]}'


def convert_refs(text, kinds, labels, warnings):
    """日本語の相互参照を \\ref 付きの英語へ置き換え、参照先ラベルを labels に集める。"""
    def item(m):
        kind, first, rest, end = m[1], m[2], m[3], m[4]
        nums = [first] + re.findall(NUM, rest or '')
        names = KINDS[kind]
        refs = []
        for n in nums + ([end] if end else []):
            prefix = kinds.get(n)
            if prefix is None:
                warnings.append(f'番号付き項目が見つからない参照: {kind}{n}')
                prefix = names[1]
            elif prefix != names[1]:
                warnings.append(f'種別の食い違い: {kind}{n} は {prefix}')
            labels.add(f'{prefix}:{n}')
            refs.append(f'\\ref{{{prefix}:{n}}}')
        if end:
            return f'{names[3]}~{refs[0]}--{refs[1]}'
        return (names[3] if len(refs) > 1 else names[2]) + '~' + join_refs(refs)
    def sec(m):
        nums = [m[2]] + ([m[3]] if m[3] else []) + re.findall(SECNUM, m[4] or '')
        for n in nums:
            labels.add(f'sec:{n}')
        if m[3]:
            return f'\\S\\S\\ref{{sec:{m[2]}}}--\\ref{{sec:{m[3]}}}'
        refs = [f'\\ref{{sec:{n}}}' for n in nums]
        return ('\\S\\S' if len(refs) > 1 else '\\S') + join_refs(refs)
    def chap(m):
        parts = []
        for piece in m[1].split('・'):
            ends = piece.split('〜')
            for n in ends:
                labels.add(f'chap:{n}')
            parts.append('--'.join(f'\\ref{{chap:{n}}}' for n in ends))
        plural = len(parts) > 1 or '〜' in m[1]
        return ('Chapters' if plural else 'Chapter') + '~' + join_refs(parts)
    def eq(m):
        labels.add(f'eq:{m[1]}')
        if m[2]:
            labels.add(f'eq:{m[2]}')
            return f'\\eqref{{eq:{m[1]}}}--\\eqref{{eq:{m[2]}}}'
        return f'\\eqref{{eq:{m[1]}}}'
    def fig(m):
        prefix, name = ('fig', 'Figure') if m[1] == '図' else ('tab', 'Table')
        labels.add(f'{prefix}:{m[2]}')
        return f'{name}~\\ref{{{prefix}:{m[2]}}}'
    def app(m):
        labels.add(f'app:{m[1]}')
        return f'Appendix~\\ref{{app:{m[1]}}}'
    for pattern, fn in [(ITEM_REF, item), (SEC_REF, sec), (CHAP_REF, chap), (EQ_REF, eq), (FIG_REF, fig), (APP_REF, app)]:
        text = pattern.sub(fn, text)
    return text


def ja_refs(md, kinds):
    text = MD_BLOCK.sub(' ', md)
    text = MD_INLINE.sub(' ', text)
    text = LINK.sub(' ', text)
    # 見出しと、番号付き項目・図の見出しにある自身の番号は参照ではない。
    text = re.sub(rf'^#.*$|^\*\*(?:{"|".join(KINDS)}|図){NUM}', ' ', text, flags=re.M)
    labels, warnings = set(), []
    convert_refs(text, kinds, labels, warnings)
    return labels, warnings


def skip_args(tex, pos):
    """pos 以降の空白・[...]・{...} を読み飛ばした位置を返す。"""
    while True:
        while pos < len(tex) and tex[pos] in ' \t\n':
            pos += 1
        if pos < len(tex) and tex[pos] in '[{':
            close = ']' if tex[pos] == '[' else '}'
            depth, brace = 0, 0
            pos += 1
            while pos < len(tex):
                c = tex[pos]
                if c == '\\':
                    pos += 2
                    continue
                if c == '{':
                    brace += 1
                elif c == '}':
                    if close == '}' and brace == 0:
                        break
                    brace -= 1
                elif c == ']' and close == ']' and brace == 0:
                    break
                pos += 1
            pos += 1
            continue
        return pos


def label_after(tex, pos):
    pos = skip_args(tex, pos)
    m = re.match(r'\\label\{([^}]+)\}', tex[pos:])
    return m[1] if m else None


def en_items(tex):
    tex = strip_comments(tex)
    found, bad = [], []
    for m in re.finditer(r'\\begin\{(' + '|'.join(ENV_PREFIX) + r')\}', tex):
        label = label_after(tex, m.end())
        if not label or not label.startswith(ENV_PREFIX[m[1]] + ':'):
            bad.append(f'{m[1]} の直後のラベルが種別と合わない: {label}')
        else:
            found.append(label)
    return found, bad


def en_sections(tex):
    tex = strip_comments(tex)
    found = []
    for m in re.finditer(r'\\(chapter|section|subsection)(?![a-z*])', tex):
        label = label_after(tex, m.end())
        if label:
            found.append(label)
    found += re.findall(r'\\label\{(fig:[^}]+|app:[^}]+)\}', tex)
    return found


def en_refs(tex):
    return set(re.findall(r'\\(?:eq)?ref\{([^}]+)\}', strip_comments(tex)))


def bib_urls():
    urls = {}
    path = EN / 'references.bib'
    if not path.exists():
        return urls
    for key, body in re.findall(r'@\w+\{([^,\s]+),(.*?)\n\}', path.read_text(), re.S):
        found = set(re.findall(r'\burl\s*=\s*\{([^}]*)\}', body))
        found |= {f'https://doi.org/{d}' for d in re.findall(r'\bdoi\s*=\s*\{([^}]*)\}', body)}
        found |= set(re.findall(r'\\(?:href|url)\{([^}]*)\}', body))
        urls[key] = {u.replace('\\%', '%').replace('\\#', '#') for u in found}
    return urls


def en_urls(tex):
    found = set(re.findall(r'\\(?:href|url)\{([^}]*)\}', tex))
    return {u.replace('\\%', '%').replace('\\#', '#').replace('\\_', '_') for u in found}


def cite_keys(tex):
    keys = set()
    for group in re.findall(r'\\cite\w*(?:\[(?:[^\[\]]|\[[^\]]*\])*\])*\{([^}]+)\}', strip_comments(tex)):
        keys |= {k.strip() for k in group.split(',')}
    return keys


# ---------------------------------------------------------------- skeleton

def bib_keys():
    with open(ROOT / 'references.csv', newline='', encoding='utf-8') as f:
        return [row['key'] for row in csv.DictReader(f)]


def escape(text):
    text = text.replace('\\', '\\textbackslash{}')
    for a, b in [('%', '\\%'), ('&', '\\&'), ('#', '\\#'), ('_', '\\_'), ('~', '\\textasciitilde{}'), ('^', '\\^{}')]:
        text = text.replace(a, b)
    return text


def texttt(code):
    code = escape(code).replace('{', '\\{').replace('}', '\\}').replace('\\textbackslash\\{\\}', '\\textbackslash{}')
    return f'\\texttt{{{code}}}'


class Inline:
    def __init__(self, kinds, keys, warnings):
        self.kinds, self.keys, self.warnings = kinds, keys, warnings
        self.labels = set()

    def __call__(self, text, refs=True):
        slots = []
        text = self.convert(text, refs, slots)
        while '\x00' in text:
            text = re.sub(r'\x00(\d+)\x00', lambda m: slots[int(m[1])], text)
        return text

    def convert(self, text, refs, slots):
        def hold(s):
            slots.append(s)
            return f'\x00{len(slots) - 1}\x00'
        text = MD_INLINE.sub(lambda m: hold(f'${unicode_math(m[1])}$'), text)
        text = re.sub(r'`([^`]+)`', lambda m: hold(texttt(m[1])), text)
        def link(m):
            label, target = m[1], m[2]
            key = re.match(r'([A-Za-z][A-Za-z0-9]*)(?:,\s*(.+))?$', label)
            if key and key[1] in self.keys:
                if key[2]:
                    return hold(f'\\cite[\\href{{{target}}}{{{self.convert(key[2], False, slots)}}}]{{{key[1]}}}')
                return hold(f'\\cite{{{key[1]}}}')
            if re.match(r'https?://', target):
                return hold(f'\\href{{{target}}}{{{self.convert(label, False, slots)}}}')
            return hold(f'\\mdlink{{{target}}}{{{self.convert(label, False, slots)}}}')
        text = LINK.sub(link, text)
        text = re.sub(r'\[([A-Za-z][A-Za-z0-9]*)\]', lambda m: hold(f'\\cite{{{m[1]}}}') if m[1] in self.keys else m[0], text)
        text = escape(text)
        if refs:
            text = convert_refs(text, self.kinds, self.labels, self.warnings)
        text = re.sub(r'\*\*(.+?)\*\*', r'\\textbf{\1}', text)
        text = re.sub(r'(?<![*\\])\*(?!\s)(.+?)(?<!\s)\*', r'\\emph{\1}', text)
        return text


def table(rows, inline):
    def cells(row):
        slots = []
        row = MD_INLINE.sub(lambda m: (slots.append(m[0]), f'\x01{len(slots) - 1}\x01')[1], row.strip())
        parts = [p.strip() for p in row.strip('|').split('|')]
        return [re.sub(r'\x01(\d+)\x01', lambda m: slots[int(m[1])], p) for p in parts]
    head, body = cells(rows[0]), [cells(r) for r in rows[2:]]
    spec = 'L' * len(head)
    out = [f'\\begin{{xltabular}}{{\\linewidth}}{{@{{}}{spec}@{{}}}}', '\\toprule',
           ' & '.join(inline(c) for c in head) + ' \\\\', '\\midrule', '\\endhead']
    out += ['\n\\addlinespace[3pt]\n'.join(' & '.join(inline(c) for c in r) + ' \\\\' for r in body)]
    out += ['\\bottomrule', '\\end{xltabular}']
    return '\n'.join(out)


def skeleton(path):
    md = path.read_text()
    warnings = []
    inline = Inline(all_kinds(), set(bib_keys()), warnings)
    lines = md.split('\n')
    out, env, proof, para = [], None, False, []
    item_re = re.compile(rf'^\*\*({"|".join(KINDS)})({NUM})(（.*）)?\.\*\*\s*(.*)$')
    proof_re = re.compile(r'^\*\*(' + '|'.join(PROOFS) + r')\.\*\*\s*(.*)$')

    def close_env():
        nonlocal env
        if env:
            out.append(f'\\end{{{env}}}')
            env = None

    def flush():
        nonlocal proof
        if not para:
            return
        text = inline('\n'.join(para))
        para.clear()
        if proof and text.rstrip().endswith('□'):
            out.append(text.rstrip()[:-1].rstrip())
            out.append('\\end{proof}')
            proof = False
        else:
            out.append(text)

    i = 0
    while i < len(lines):
        line = lines[i]
        if line.startswith('```math'):
            flush()
            j = i + 1
            while lines[j] != '```':
                j += 1
            body, tag = split_tag('\n'.join(lines[i + 1:j]) + '\n')
            body = unicode_math(body).strip('\n')
            if tag:
                out.append(f'\\begin{{equation*}}\n{body}\n\\tag{{{tag}}}\\label{{eq:{tag}}}\n\\end{{equation*}}')
            else:
                out.append(f'\\[\n{body}\n\\]')
            i = j + 1
            continue
        if not line.strip():
            flush()
            i += 1
            continue
        heading = re.match(r'^(#{1,3}) (.*)$', line)
        if heading:
            flush()
            close_env()
            level, title = len(heading[1]), heading[2]
            m = re.match(rf'^第(\d+)章 (.*)$', title) if level == 1 else re.match(rf'^({SECNUM}) (.*)$', title)
            app = re.match(r'^付録([A-C]) (.*)$', title) if level == 1 else None
            cmd = ['chapter', 'section', 'subsection'][level - 1]
            if app:
                out.append(f'\\chapter{{{inline(app[2], refs=False)}}}\\label{{app:{app[1]}}}')
            elif m:
                prefix = 'chap' if level == 1 else 'sec'
                out.append(f'\\{cmd}{{{inline(m[2], refs=False)}}}\\label{{{prefix}:{m[1]}}}')
            else:
                out.append(f'\\{cmd}*{{{inline(title, refs=False)}}}')
            i += 1
            continue
        m = item_re.match(line)
        if m:
            flush()
            close_env()
            kind, n, title, rest = m[1], m[2], m[3], m[4]
            envname, prefix = KINDS[kind][0], KINDS[kind][1]
            opt = f'[{inline(title[1:-1], refs=False)}]' if title else ''
            out.append(f'\\begin{{{envname}}}{opt}\\label{{{prefix}:{n}}}')
            env = envname
            if rest:
                para.append(rest)
            i += 1
            continue
        m = proof_re.match(line)
        if m:
            flush()
            close_env()
            name = PROOFS[m[1]]
            out.append('\\begin{proof}' + (f'[{name}]' if name else ''))
            proof = True
            if m[2]:
                para.append(m[2])
            i += 1
            continue
        if line.startswith('|'):
            flush()
            j = i
            while j < len(lines) and lines[j].startswith('|'):
                j += 1
            out.append(table(lines[i:j], inline))
            i = j
            continue
        if re.match(r'^(- |\d+\. )', line):
            flush()
            ordered = not line.startswith('- ')
            items, j = [], i
            while j < len(lines) and (re.match(r'^(- |\d+\. )', lines[j]) or (lines[j].startswith('  ') and items)):
                if re.match(r'^(- |\d+\. )', lines[j]):
                    items.append(re.sub(r'^(- |\d+\. )', '', lines[j]))
                else:
                    items[-1] += '\n' + lines[j].strip()
                j += 1
            name = 'enumerate' if ordered else 'itemize'
            out.append(f'\\begin{{{name}}}\n' + '\n'.join(f'\\item {inline(t)}' for t in items) + f'\n\\end{{{name}}}')
            i = j
            continue
        fig = re.match(r'^!\[(.*)\]\(\.\./figures/([^)]+)\.svg\)$', line)
        if fig:
            flush()
            close_env()
            j = i + 1
            while not lines[j].strip():
                j += 1
            cap = re.match(rf'^\*\*図({NUM})：(.*?)\*\*\s*(.*)$', lines[j])
            k = j + 1
            caption = [cap[3]] if cap else []
            while cap and k < len(lines) and lines[k].strip():
                caption.append(lines[k])
                k += 1
            n = cap[1] if cap else '?'
            out.append('\\begin{figure}[htbp]\n\\centering\n'
                       f'\\input{{figures/{fig[2]}}}\n'
                       f'\\caption{{\\textbf{{{inline(cap[2] if cap else fig[1], refs=False)}}} '
                       f'{inline(chr(10).join(caption))}}}\\label{{fig:{n}}}\n\\end{{figure}}')
            i = k
            continue
        para.append(line)
        i += 1
    flush()
    close_env()
    for w in warnings:
        print(f'warning: {path.name}: {w}', file=sys.stderr)
    # 別行立ての数式は前後の段落の途中に置く(Markdown の空行を段落の区切りにしない)。
    text = '\n\n'.join(out) + '\n'
    text = re.sub(r'\n\n(\\\[|\\begin\{equation\*\})', r'\n\1', text)
    return re.sub(r'(\\\]|\\end\{equation\*\})\n\n(?!\\(?:begin|end|section|subsection|chapter))', r'\1\n', text)


# ---------------------------------------------------------------- check

def parts():
    for path in sorted(JA.glob('*.md')):
        tex = EN / (path.stem + '.tex')
        if tex.exists():
            yield path, tex


def aux_numbers(aux):
    table = {}
    for path in [aux, *aux.parent.glob('*.aux')]:
        for label, number in re.findall(r'\\newlabel\{([^}]+)\}\{\{([^}]*)\}', path.read_text(errors='replace')):
            table[label] = number
    return table


def check(aux=None):
    kinds, urls_by_key = all_kinds(), bib_urls()
    errors, notes = [], []
    defined_all = set()
    for md_path, tex_path in parts():
        name = md_path.stem
        md, tex = md_path.read_text(), tex_path.read_text()
        err = lambda msg: errors.append(f'{name}: {msg}')
        # 数式
        ja_list, ja_tags = ja_math(md)
        en_list, en_tags, bad = en_math(tex)
        for b in bad:
            err(b)
        ja_c = collections.Counter(canon(m) for m in ja_list)
        en_c = collections.Counter(canon(m) for m in en_list)
        left_ja, left_en = ja_c - en_c, en_c - ja_c
        masked_ja = collections.Counter(mask_text(m) for m in left_ja.elements())
        masked_en = collections.Counter(mask_text(m) for m in left_en.elements())
        text_only = masked_ja & masked_en
        for m in (masked_ja - masked_en).elements():
            err(f'英語原稿にない数式: {m[:160]}')
        for m in (masked_en - masked_ja).elements():
            err(f'日本語原稿にない数式: {m[:160]}')
        if text_only:
            notes.append(f'{name}: \\text{{}} の中身だけが異なる数式 {sum(text_only.values())} 件(翻訳した注記を目視確認)')
        if sorted(ja_tags) != sorted(en_tags):
            err(f'式番号の不一致: ja={sorted(set(ja_tags) - set(en_tags))} en={sorted(set(en_tags) - set(ja_tags))}')
        # 番号付き項目・見出し
        ja_labels = [l for l, _ in ja_items(md)] + ja_sections(md) + [f'eq:{t}' for t in ja_tags]
        en_labels, bad = en_items(tex)
        for b in bad:
            err(b)
        en_labels += en_sections(tex) + [f'eq:{t}' for t in en_tags]
        if sorted(ja_labels) != sorted(en_labels):
            err(f'番号の不一致: ja のみ={sorted(set(ja_labels) - set(en_labels))} en のみ={sorted(set(en_labels) - set(ja_labels))}')
        defined_all |= set(en_labels)
        # 相互参照
        want, warns = ja_refs(md, kinds)
        want -= EXEMPT_REFS.get(name, set())
        have = en_refs(tex)
        for w in warns:
            notes.append(f'{name}: {w}')
        if want - have:
            err(f'英語原稿にない参照: {sorted(want - have)}')
        if have - want:
            err(f'日本語原稿にない参照: {sorted(have - want)}')
        # リンク
        ja_urls = {a or b for a, b in URL_MD.findall(md)}
        keys = cite_keys(tex)
        via_bib = set().union(*[urls_by_key.get(k, set()) for k in keys]) if keys else set()
        missing = ja_urls - en_urls(tex) - via_bib
        extra = en_urls(tex) - ja_urls
        if missing:
            err(f'英語原稿にないリンク: {sorted(missing)}')
        if extra:
            err(f'日本語原稿にないリンク: {sorted(extra)}')
        undefined_keys = keys - set(bib_keys())
        if undefined_keys:
            err(f'文献一覧にない引用: {sorted(undefined_keys)}')
        # 英語原稿の文字
        for n, line in enumerate(tex.split('\n'), 1):
            if CJK.search(line):
                err(f'{tex_path.name}:{n}: 日本語が残っている')
            elif re.search(r'[^\x00-\x7f]', line):
                err(f'{tex_path.name}:{n}: ASCII 以外の文字')
            if '\\mdlink' in line:
                err(f'{tex_path.name}:{n}: 未解決の Markdown リンク')
        notes.append(f'{name}: 数式 {len(ja_list)} 件・番号 {len(ja_labels)} 件・参照 {len(want)} 件・リンク {len(ja_urls)} 件を照合')
    if aux:
        numbers = aux_numbers(Path(aux))
        for label in sorted(defined_all):
            prefix, n = label.split(':', 1)
            got = numbers.get(label)
            if got is None:
                errors.append(f'aux: ラベル {label} が組版結果にない')
            elif got != n:
                errors.append(f'aux: {label} が {got} と組版された')
    return errors, notes


def pending():
    defined, wanted = set(), set()
    for _, tex_path in parts():
        tex = tex_path.read_text()
        items, _ = en_items(tex)
        _, tags, _ = en_math(tex)
        defined |= set(items) | set(en_sections(tex)) | {f'eq:{t}' for t in tags}
        wanted |= en_refs(tex)
    lines = ['% Provisional labels for numbers in parts not yet translated.',
             '% Generated by tools/ja_en.py pending.', '\\makeatletter']
    for label in sorted(wanted - defined, key=lambda s: [int(x) if x.isdigit() else x for x in re.split(r'[:.]', s)]):
        lines.append(f'\\def\\@currentlabel{{{label.split(":", 1)[1]}}}\\label{{{label}}}')
    lines.append('\\makeatother')
    return '\n'.join(lines) + '\n'


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest='action', required=True)
    s = sub.add_parser('skeleton')
    s.add_argument('part', help='ja/ のファイル名 (例: 04-relative-architecture.md)')
    c = sub.add_parser('check')
    c.add_argument('--aux', help='組版結果の main.aux')
    sub.add_parser('pending')
    args = ap.parse_args()
    if args.action == 'skeleton':
        print(skeleton(JA / args.part), end='')
        return 0
    if args.action == 'pending':
        print(pending(), end='')
        return 0
    errors, notes = check(args.aux)
    for n in notes:
        print(f'note: {n}')
    for e in errors:
        print(f'error: {e}')
    print(f'{len(errors)} error(s)')
    return int(bool(errors))


if __name__ == '__main__':
    sys.exit(main())
