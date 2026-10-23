#!/usr/bin/env python3
"""Expand selected ArchMap atoms to their existing, file-backed source excerpts."""
import argparse
import hashlib
import json
from pathlib import Path
import sys


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f'duplicate key: {key}')
        result[key] = value
    return result


def index(items):
    result = {}
    for item in items:
        key = item['id']
        if key in result:
            raise ValueError(f'duplicate id: {key}')
        result[key] = item
    return result


def expand(archmap, selected, files):
    """Only follow explicit atom -> origin -> source references; infer no edges."""
    if not selected or len(set(selected)) != len(selected):
        raise ValueError('select distinct snapshot/atom IDs')
    sources = index(archmap['sources'])
    origins = index(archmap['origins'])
    snapshots = index(archmap['snapshots'])
    atoms, used_origins, used_sources = [], {}, {}
    for selector in selected:
        snapshot_id, atom_id = selector.split('/')
        atom = index(snapshots[snapshot_id]['atoms'])[atom_id]
        atoms.append({'snapshot': snapshot_id, **atom})
        origin_id = atom['origin']
        if origin_id in used_origins:
            continue
        origin = origins[origin_id]
        locations = []
        for location in origin['locations']:
            source_id = location['source']
            source = sources[source_id]
            if source_id not in used_sources:
                data = Path(files[source_id]).read_bytes()
                data.decode('utf-8')
                if source['digest'] != 'sha256:' + hashlib.sha256(data).hexdigest():
                    raise ValueError(f'source digest mismatch: {source_id}')
                used_sources[source_id] = (source, data)
            data = used_sources[source_id][1]
            span = location.get('span', [0, len(data)])
            if (not isinstance(span, list) or len(span) != 2
                    or any(type(x) is not int for x in span)
                    or not 0 <= span[0] <= span[1] <= len(data)):
                raise ValueError(f'invalid byte span: {origin_id}')
            start, end = span
            # Decoding both prefix and excerpt rejects a split UTF-8 code point.
            data[:start].decode('utf-8')
            excerpt = data[start:end].decode('utf-8')
            locations.append({**location, 'resolved_span': span, 'excerpt': excerpt})
        used_origins[origin_id] = {**origin, 'locations': locations}
    return {
        'atoms': atoms, 'origins': list(used_origins.values()),
        'sources': [source for source, _ in used_sources.values()],
        'verification': 'Local bytes match declared file digests and spans. '
                        'Revision provenance, reading coverage, meaning and Law fidelity are not verified.',
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('archmap', type=Path)
    parser.add_argument('--atom', action='append', required=True, help='snapshot/atom ID; repeatable')
    parser.add_argument('--source', action='append', default=[], help='source-id=local-file; repeatable')
    args = parser.parse_args()
    try:
        files = {}
        for binding in args.source:
            name, path = binding.split('=', 1)
            if not name or not path or name in files:
                raise ValueError('source bindings must have distinct IDs and nonempty paths')
            files[name] = path
        archmap = json.loads(args.archmap.read_text(encoding='utf-8'), object_pairs_hook=unique_object)
        print(json.dumps(expand(archmap, args.atom, files), ensure_ascii=False, indent=2))
        return 0
    except (ValueError, KeyError, TypeError, OSError) as error:
        print(f'Cannot resolve evidence: {error}', file=sys.stderr)
        return 2


if __name__ == '__main__':
    sys.exit(main())
