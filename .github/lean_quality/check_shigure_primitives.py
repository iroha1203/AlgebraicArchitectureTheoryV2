"""Check SHIGURE sources for proof placeholders and trusted evaluation."""

from pathlib import Path
import re
import sys


ROOT = Path("Formal/SHIGURE")
TEST = ROOT / "AssertStandardAxiomsTest.lean"
TEST_ASSUMPTION = "private axiom SHIGURE.KernelAuditTest.nonstandard : False"
FORBIDDEN = {"axiom", "sorry", "admit", "unsafe", "native_decide",
             "sorryAx", "ofReduceBool", "trustCompiler"}

# Match the lexical constructs relevant to this check. The subsequent build
# still checks the source with Lean's own parser.
TOKEN = re.compile(
    r'--[^\n]*|/-|(?P<raw>r(?P<hashes>#*)")|!"'
    r'|"(?:\\[\s\S]|[^"\\])*"|«[^»]*»'
    r"|'(?:\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|.)|[^'\\\n])'"
    r"|[\w'′″‴]+|:=|\S"
)
COMMENT_EDGE = re.compile(r"/-|-/")
STRING_EDGE = re.compile(r'\\[\s\S]|[{"]')


def tokens(source):
    """Yield relevant code tokens with offsets, including interpolated expressions."""
    pos = 0
    modes = [0]
    while pos < len(source):
        if modes[-1] == "string":
            edge = STRING_EDGE.search(source, pos)
            if edge is None:
                break
            pos = edge.end()
            if edge[0] == '"':
                modes.pop()
            elif edge[0] == "{":
                modes.append(1)
            continue

        match = TOKEN.search(source, pos)
        if match is None:
            break
        pos = match.end()
        word = match[0]
        if word.startswith("--"):
            continue
        if word == "/-":
            depth = 1
            while depth:
                edge = COMMENT_EDGE.search(source, pos)
                if edge is None:
                    raise ValueError("unclosed block comment")
                pos = edge.end()
                depth += 1 if edge[0] == "/-" else -1
        elif match["raw"]:
            terminator = '"' + match["hashes"]
            end = source.find(terminator, pos)
            if end == -1:
                raise ValueError("unclosed raw string")
            pos = end + len(terminator)
            yield "", match.start()
        elif word == '!"':
            modes.append("string")
            yield "", match.start()
        elif word.startswith(('"', "'")):
            yield "", match.start()
        elif word.startswith("«"):
            name = word[1:-1]
            yield name if name in {"sorryAx", "ofReduceBool", "trustCompiler"} else "", match.start()
        elif word == "{" and modes[-1]:
            modes[-1] += 1
            yield word, match.start()
        elif word == "}" and modes[-1]:
            modes[-1] -= 1
            if modes[-1] == 0:
                modes.pop()
            yield word, match.start()
        else:
            yield word, match.start()
    if len(modes) != 1:
        raise ValueError("unclosed interpolated string")


def violations(path, source):
    code = list(tokens(source))
    allowed_fixture = False
    for index, (word, offset) in enumerate(code):
        if word == "native":
            preceding = code[index - 1][0] if index else ""
            following = [item[0] for item in code[index + 1:index + 3]]
            if preceding != "+" and following != [":=", "true"]:
                continue
        elif word not in FORBIDDEN:
            continue

        start = source.rfind("\n", 0, offset) + 1
        end = source.find("\n", offset)
        line = source[start:None if end == -1 else end]
        if path == TEST and line == TEST_ASSUMPTION and word == "axiom" and not allowed_fixture:
            allowed_fixture = True
        else:
            yield source.count("\n", 0, offset) + 1, word


def main():
    valid = True
    for path in sorted([ROOT.with_suffix(".lean"), *ROOT.rglob("*.lean")]):
        try:
            for line, token in violations(path, path.read_text(encoding="utf-8")):
                print(f"{path}:{line}: disallowed source token {token}", file=sys.stderr)
                valid = False
        except (OSError, ValueError) as error:
            print(f"{path}: {error}", file=sys.stderr)
            valid = False
    return 0 if valid else 1


if __name__ == "__main__":
    sys.exit(main())
