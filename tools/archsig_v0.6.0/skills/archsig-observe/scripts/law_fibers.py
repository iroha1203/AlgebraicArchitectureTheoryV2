#!/usr/bin/env python3
"""Check ker(q) <= intersection ker(v) on an explicitly enumerated finite table."""
import argparse
import json
import sys
from itertools import combinations
from pathlib import Path


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate key: {key}")
        result[key] = value
    return result


def names(value, label):
    if not isinstance(value, list) or any(not isinstance(x, str) or not x for x in value):
        raise ValueError(f"{label}: expected a list of nonempty strings")
    if len(set(value)) != len(value):
        raise ValueError(f"{label}: duplicate name")
    return value


def exact_keys(value, expected, label):
    if not isinstance(value, dict) or set(value) != set(expected):
        raise ValueError(f"{label}: expected exactly {list(expected)}")


def token(value, label):
    if not isinstance(value, str) or not value:
        raise ValueError(f"{label}: expected a nonempty equality token; missing values are not evaluations")
    return value


def check(table):
    exact_keys(table, ['scope', 'sources', 'laws', 'q', 'v'], 'table')
    token(table['scope'], 'scope')
    sources = names(table['sources'], 'sources')
    laws = names(table['laws'], 'laws')
    exact_keys(table['q'], sources, 'q')
    exact_keys(table['v'], sources, 'v')
    for source in sources:
        token(table['q'][source], f'q[{source}]')
        exact_keys(table['v'][source], laws, f'v[{source}]')
        for law in laws:
            token(table['v'][source][law], f'v[{source}][{law}]')
    q_groups = {}
    joint_groups = {}
    for source in sources:
        q_groups.setdefault(table['q'][source], []).append(source)
        values = tuple(table['v'][source][law] for law in laws)
        joint_groups.setdefault(values, []).append(source)
    witnesses = []
    for group in q_groups.values():
        for left, right in combinations(group, 2):
            differences = [law for law in laws if table['v'][left][law] != table['v'][right][law]]
            if differences:
                witnesses.append({'left': left, 'right': right, 'laws': differences})
    result = {
        'scope': table['scope'], 'source_count': len(sources), 'law_count': len(laws),
        'adequate_on_table': not witnesses,
        'vacuous': not sources or not laws,
        'q_partition': list(q_groups.values()),
        'joint_law_partition': list(joint_groups.values()),
        'counterexamples': witnesses,
    }
    if not witnesses:
        result['descent'] = {q: table['v'][members[0]].copy() for q, members in q_groups.items()}
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('table', type=Path)
    args = parser.parse_args()
    try:
        table = json.loads(args.table.read_text(encoding='utf-8'), object_pairs_hook=unique_object)
        result = check(table)
        print(json.dumps(result, ensure_ascii=True, indent=2))
        return 0 if result['adequate_on_table'] else 1
    except (ValueError, OSError) as error:
        print(f'Invalid finite table: {error}', file=sys.stderr)
        return 2


if __name__ == '__main__':
    sys.exit(main())
