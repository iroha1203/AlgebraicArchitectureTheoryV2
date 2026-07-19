#!/usr/bin/env python3
"""Mechanical integration layer (train-ticket fullbuild, Issue #3545).

Allowed operations only: enumerate, hash-free literal key comparison, refs
union, deterministic subject normalization derived from refs. No semantic
choice: every atom here was either mechanically matched (both passes) or
carries an integrator-ratified adjudication decision.
"""
import json, glob, re, collections, sys

BASE = "<SCRATCHPAD>/fullbuild"

def service_dir_of(refs):
    for r in refs:
        m = re.match(r"src:(ts-[a-z0-9-]+|ts-common)/", r)
        if m:
            return m.group(1)
    return None

def normalize_subject(subject, refs):
    """<service-dir>.<ClassName> using the ref's service dir. Idempotent."""
    svc = service_dir_of(refs)
    if not svc:
        return subject
    if subject.startswith(svc + "."):
        tail = subject[len(svc) + 1:]
    else:
        tail = subject
    cls = tail.split(".")[-1] if "." in tail else tail
    return f"{svc}.{cls}"

def slug(s):
    return re.sub(r"-+", "-", re.sub(r"[^a-z0-9]+", "-", s.lower())).strip("-")

def match_key(a):
    return "|".join([a["kind"], a["subject"].strip(), a["axis"],
                     a.get("predicate") or "", a.get("object") or ""])

def main():
    packets = {}
    for f in glob.glob(BASE + "/candidates/*.json"):
        p = json.load(open(f))
        packets[(p["passId"], "chunk-" + f.split("chunk-")[1][:2])] = p
    atom_by_id = {}
    for (pid, _), p in packets.items():
        for a in p["candidateAtoms"]:
            atom_by_id[(pid, a["id"])] = a

    cons = json.load(open(BASE + "/extraction-consistency.json"))
    matched_rows = cons["matched"]["rows"] if isinstance(cons["matched"], dict) else cons["matched"]

    pool = []  # (atom, provenance)
    # 1) matched rows: take pass-a body, union both passes' refs
    for row in matched_rows:
        a_id = row["passAAtomIds"][0]
        body = None
        for (pid, aid), a in atom_by_id.items():
            if pid == "pass-a" and aid == a_id:
                body = dict(a); break
        if body is None:
            continue
        refs = set(body.get("refs", []))
        for bid in row.get("passBAtomIds", []):
            for (pid, aid), a in atom_by_id.items():
                if pid == "pass-b" and aid == bid:
                    refs |= set(a.get("refs", []))
        body["refs"] = sorted(refs)
        pool.append((body, "matched"))

    # 2) adjudicated canonical atoms
    adj_stats = collections.Counter()
    seen_canonical = set()
    adj_files = sorted(glob.glob(BASE + "/adjudication/adj-chunk-*.json"))
    for f in adj_files:
        d = json.load(open(f))
        for row in d["adjudications"]:
            adj_stats[row["decision"]] += 1
            ca = row.get("canonicalAtom")
            if row["decision"] in ("merged", "adopted") and ca:
                # merged pairs repeat the same canonical atom; dedup by identity key
                k = (f, ca["id"]) if False else ca["id"] + "|" + (ca.get("object") or "")
                if k in seen_canonical:
                    # union refs anyway
                    for body, _ in pool:
                        if body["id"] == ca["id"] and (body.get("object") or "") == (ca.get("object") or ""):
                            body["refs"] = sorted(set(body.get("refs", [])) | set(ca.get("refs", [])))
                            break
                    continue
                seen_canonical.add(k)
                pool.append((dict(ca), f.split("/")[-1]))

    # 3) subject normalization + id re-slug + key dedup with refs union
    canon = {}
    norm_log = []
    for body, prov in pool:
        old_subject = body["subject"]
        body["subject"] = normalize_subject(body["subject"], body.get("refs", []))
        if body["subject"] != old_subject:
            norm_log.append({"atomId": body["id"], "from": old_subject, "to": body["subject"]})
        k = match_key(body)
        if k in canon:
            canon[k]["refs"] = sorted(set(canon[k].get("refs", [])) | set(body.get("refs", [])))
        else:
            canon[k] = body

    atoms = sorted(canon.values(), key=lambda a: a["id"])
    kinds = collections.Counter(a["kind"] for a in atoms)
    cech = [a for a in atoms if a.get("axis") == "cech"]

    json.dump({"atoms": atoms}, open(BASE + "/integrated-atoms.json", "w"), ensure_ascii=False, indent=1)
    json.dump(norm_log, open(BASE + "/subject-normalization-log.json", "w"), ensure_ascii=False, indent=1)

    # subject index per service for context design
    by_svc = collections.defaultdict(list)
    for a in atoms:
        svc = a["subject"].split(".")[0]
        by_svc[svc].append(a["id"])
    json.dump({k: len(v) for k, v in sorted(by_svc.items())},
              open(BASE + "/atoms-per-service.json", "w"), ensure_ascii=False, indent=1)

    print("adj files:", len(adj_files))
    print("adjudication decisions:", dict(adj_stats))
    print("canonical atoms:", len(atoms))
    print("kinds:", dict(kinds))
    print("cech atoms:", len(cech))
    print("subjects normalized:", len(norm_log))
    print("services:", len(by_svc))

if __name__ == "__main__":
    main()
