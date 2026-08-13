#!/usr/bin/env python3
"""Deterministic R2 candidate evaluation for the G-104 necessity map.

The predicates in this module use only finite incidence, derived Target
supports, and the partial cell map.  The sole local linear-algebra exception is
the preregistered C3 fiber cycle/boundary test; global or A-block H1 and the
comparison rank are used only by the two counterexample queries.
"""

from __future__ import annotations

from dataclasses import asdict, dataclass
from fractions import Fraction
from hashlib import sha256
from itertools import permutations, product
import json
from pathlib import Path
from typing import Iterable, Iterator

from necessity_map import (
    H1Analysis,
    Matrix,
    Nerve,
    NerveMorphism,
    UniformComparison,
    analyze_h1,
    calibration_fixtures,
    canonical_core_factors,
    canonical_firing_fixture,
    core_incidence_templates,
    derived_cell_supports,
    legacy_positive_fixture,
    nonempty_subsets,
    r0_report,
    r1_report,
    r1_necessity_witnesses,
    required_fixture_catalog_summary,
    support_hole_fixture,
)


CANDIDATE_SEMANTIC_ID = "R2-CSTAR-DIRECT-v1"
CANDIDATE_SPEC = "\n".join(
    (
        "scope:C1-C4 reduce both A-subnerves per nonempty A; C0,C5,C6 reduce both whole supported nerves once",
        "facetwin:exact ordered edge triple and exact derived Target-support signature",
        "reduction:quotient FaceTwin then simultaneously once remove every self-loop e and class (e,e,e) when e occurs in no other class",
        "critical:remaining self-loop or nonloop whose endpoints remain path-connected after deleting that edge",
        "active-fine-chart:endpoint of retained fine lift of a critical coarse edge or retained fine face mapping a retained coarse FaceTwin class",
        "C0:critical coarse vertex support equals union of pi-images of active fine chart supports in its phi-fiber",
        "C1:critical port is nonempty and connected by all selected fine edges with both endpoints in the port",
        "C2:every critical coarse edge has a retained mapped fine lift",
        "C3:retained edgeMap-none fiber cycles are spanned over Q by retained faceMap-none internal face boundaries",
        "C4:every retained coarse FaceTwin class has a retained fine face mapping one of its members",
        "direct-lifttwin:same retained fine face co-occurrence or occurrence in retained fine faces mapping one coarse FaceTwin class, with equal lift support signatures",
        "C5:the direct LiftTwin graph on each critical coarse edge lift set is a clique",
        "C6:each connected component of that graph over a critical coarse self-loop has a fine self-loop representative",
    )
)
CANDIDATE_SEMANTIC_SHA256 = sha256(CANDIDATE_SPEC.encode("ascii")).hexdigest()

COMPONENT_SEMANTIC_ID = "R2-CSTAR-COMPONENT-v2"
COMPONENT_SPEC = CANDIDATE_SPEC.replace(
    "C5:the direct LiftTwin graph on each critical coarse edge lift set is a clique",
    "C5:the direct LiftTwin graph on each critical coarse edge lift set has at most one connected component",
)
COMPONENT_SEMANTIC_SHA256 = sha256(COMPONENT_SPEC.encode("ascii")).hexdigest()

CERTIFIED_SEMANTIC_ID = "R2-CSTAR-CERTIFIED-v3"
CERTIFIED_SPEC = "\n".join(
    line
    for line in COMPONENT_SPEC.splitlines()
    if not line.startswith("direct-lifttwin:")
).replace(
    "C5:the direct LiftTwin graph on each critical coarse edge lift set has at most one connected component",
    "C5:the CertifiedDirect SLOT-or-KILL graph on each critical coarse edge lift set has at most one connected component",
).replace(
    "C6:each connected component of that graph over a critical coarse self-loop has a fine self-loop representative",
    "C6:each CertifiedDirect connected component over a critical coarse self-loop has a fine self-loop representative",
) + "\n" + "\n".join(
    (
        "certified-slot:two retained fine faces map one coarse FaceTwin class and differ in exactly one ordered boundary slot occupied by the two lifts; other edges and support signatures are exact",
        "certified-kill:a retained fine face has boundary (u,v,z) or (v,u,z), another has (z,z,z), mapped coarse boundaries are (E,E,Z) and (Z,Z,Z), and edge/face support signatures are exact",
        "certified-swap:reflexive transitive closure of the undirected SLOT-or-KILL relation",
    )
)
CERTIFIED_SEMANTIC_SHA256 = sha256(CERTIFIED_SPEC.encode("ascii")).hexdigest()

V4_SEMANTIC_ID = "R2-CSTAR-SUPPORT-ACTIVE-JOINT-COLLAPSE-v4"
V4_HUMAN_ADJUDICATION_ISSUE_COMMENT = 5232435603
V4_SPEC = "\n".join(
    (
        "scope:every relative scope is the support-active A-subcomparison; whole C0,C5,C6 use the full coarse Target as A",
        "facetwin:static exact ordered edge triple and exact derived Target-support signature on each support-active side",
        "joint-state:retained coarse edges/classes, retained fine edges/classes, and a deterministic collapse trace",
        "beta:for ordered boundary (e0,e1,e2), beta_F(e)=count(e,e0)+count(e,e2)-count(e,e1)",
        "coarse-packet:a retained coarse edge E occurs raw in exactly one retained class K and abs(beta_K(E))=1",
        "K-preimage:a retained fine class has a nonempty actual face-map set wholly inside K; mapped-None or K-other-class mixtures forbid the packet",
        "pivot:each K-preimage class chooses a distinct mapped-E edge of signed coefficient one in absolute value that occurs raw in no other retained fine class",
        "orphan-check:after provisionally removing every K-preimage class and pivot, every remaining mapped-E fine edge is face-free and a nonselfloop bridge, then all are removed",
        "fine-only-packet:an all-faceMap-None retained fine class removes one edgeMap-None signed-unit pivot occurring raw only in that class",
        "transition:apply one packet variant at a time; enumerate every injective pivot choice; memoize retained-cell states",
        "terminal:a state is irreducible exactly when it has no allowed packet; every terminal satisfies retained face-boundary and fine-to-coarse map closure",
        "critical:remaining self-loop or nonloop whose endpoints remain path-connected after deleting that edge",
        "C0-C4:evaluate post-collapse retained cells; C1 port connectivity uses every selected fine edge exactly as in v3",
        "C5-C6-guard:use coarse critical edges union mapped images of fine critical edges as the guard domain, with critical vertices unchanged",
        "C5-C6-evaluation:evaluate retained-only CERTIFIED-v3 SLOT-or-KILL witnesses without an archive; universally quantify every clause over all terminal states",
    )
)
V4_SEMANTIC_SHA256 = sha256(V4_SPEC.encode("ascii")).hexdigest()
V4_CALIBRATION_REGISTERED_CANONICAL_SHA256 = (
    "20770592f4b8f8cb7dbb269364bb8707eff4b518decc5039916ebfc072dec4e3"
)
V4_CALIBRATION_REGISTERED_CANONICAL_BYTES = 96886
V4_CALIBRATION_SERIALIZATION_CONTRACT = {
    "encoding": "utf-8",
    "ensure_ascii": False,
    "indent": 2,
    "sort_keys": True,
    "trailing_newline": True,
}

ROUND13_BOUND_SEMANTIC_ID = "R13-CROSS-CHART-TRIANGLE-SUPPORT-v1"
ROUND13_BOUND_SPEC = "\n".join(
    (
        "purpose:pure preregistration bound manifest only; no H1, candidate, query, or round report evaluation",
        "incidence:four charts with edges ((0,0),(1,2),(1,3),(2,3)) and face flag choosing () or ((1,2,3),)",
        "morphism:coarse and fine nerves coincide and all vertex, edge, and present-face maps are identities",
        "targets:coarse Target 2, fine Target 3, and pi=(0,0,1)",
        "supports:coarse charts are (S0,ST,ST,ST) and fine charts are (T0,TT,TT,TT), with every support nonempty",
        "compatibility:pi(T0) is a subset of S0 and pi(TT) is a subset of ST",
        "labeled-bound:two face flags times 3 squared coarse support choices times 7 squared fine support choices gives 882 raw and 242 compatible cases",
        "canonical-code:fixed incidence and supports modulo only the pi-preserving fine target swap 0<->1",
        "canonical-bound:242 compatible labeled semantic cases form 146 canonical support-incidence orbits",
        "coverage-baseline:the 242 compatible semantic cases are disjoint from the prior 1918, so new=242 and union=2160",
    )
)
ROUND13_BOUND_SEMANTIC_SHA256 = sha256(
    ROUND13_BOUND_SPEC.encode("ascii")
).hexdigest()
ROUND13_PARENT_RESULTS_JSON_SHA256 = (
    "cabfbcae7075280a6d10de3c819c25ca2396a21deaed2099bafdd71daa252306"
)
ROUND13_PARENT_RESULTS_SUMMARY_JSON_SHA256 = (
    "afa334056b52938044c0acad9b693a0c437300382b855f32450af5750020caa5"
)
ROUND13_PARENT_ROUND12_PAYLOAD_SHA256 = (
    "c9ab928190491610ff1e394fb16fb4e132f117374a317505fbd2025ab5a09f90"
)
ROUND13_PREREGISTERED_ISSUE_COMMENT = 5234690436
ROUND13_PREREGISTERED_CREATED_AT = "2026-08-10T00:34:52Z"
ROUND13_PREREGISTERED_UPDATED_AT = "2026-08-10T00:34:52Z"
ROUND13_REGISTERED_MANIFEST_SHA256 = (
    "8bebea1711e8e786f0a4b4c3dd73458c83db7432facbf04d5abcbfdb7d285a6c"
)

REGISTERED_ROUND_PAYLOAD_SHA256 = (
    "82aa4aa6895bbde75e5092f265f18d217fa66c17b63c16ebad92011a239861de",
    "ebc6f486a661e4fa53598d0c53efaaacf3cd1c4535e79fa31afedc222f7b260a",
    "bcd3408ebe16429dec1a136a64c1ee4fffc99c6adcd31c548cd90cdf9cb6e381",
    "d35620af9bfee3bf2e301ad91b562f3e788a063873a0042cee8425c20d72ce94",
    "09012de4338717f4332336a4a51b1d6103e59264f600c17827004d17699982c4",
    "26de136bd3ace9b399560242655ad7027be2e82d67749aeaa4e199163f7d2429",
    "6cd110d05b6e1537589ac5f002818a68d0778f3534190f125abd14438eac4c56",
)
FINAL_R0_SEMANTIC_SHA256 = (
    "dd982e5ded6395371c421e1d6223c2bf7489a07b723797fdeda55d99a172b455"
)
FINAL_R1_SEMANTIC_SHA256 = (
    "ff2d9fa12eb64bf343d3148f081e1164d4216d8548e53d90550eb53886dd359a"
)
ROUND8_DIAGNOSTIC_PAYLOAD_SHA256 = (
    "a239fbd921b7fd97de25ad0d00a43b5d5195116c9ecbf8d83e1f1911dffe3178"
)
ROUND9_VALID_PAYLOAD_SHA256 = (
    "596fe4631155389798e5590953f7582048b3b37da7766859115f66a197f8aceb"
)
ROUND9_RESULT_ISSUE_COMMENT = 5230876303
HISTORICAL_ROUND10_PAYLOAD_SHA256 = (
    "6f2a6287ae3f9c85300711b01b701ba6393dd2d5d44b3e2ebb748df923017a6f"
)
POST_PUNIT_R0_SEMANTIC_SHA256 = (
    "37873129ed7d2d6fc0375b721e6e95bd213966836ed8b29484224fd88321d3cf"
)
POST_PUNIT_R0_ISSUE_COMMENT = 5231149474
POST_PUNIT_MANIFEST_REGISTERED_SHA256 = (
    "7147f672e1f23a11c01c3a2c5ad31165eb32d4105f5fa3e7c6eec7d5a51044a9"
)
POST_PUNIT_MANIFEST = {
    "candidate_sha256": CERTIFIED_SEMANTIC_SHA256,
    "historical_round10_sha256": HISTORICAL_ROUND10_PAYLOAD_SHA256,
    "historical_round8_sha256": ROUND8_DIAGNOSTIC_PAYLOAD_SHA256,
    "historical_round9_sha256": ROUND9_VALID_PAYLOAD_SHA256,
    "post_punit_r0_issue_comment": POST_PUNIT_R0_ISSUE_COMMENT,
    "post_punit_r0_sha256": POST_PUNIT_R0_SEMANTIC_SHA256,
    "prior_population": 1914,
    "r1_sha256": FINAL_R1_SEMANTIC_SHA256,
    "registered_round1_through_round7": list(REGISTERED_ROUND_PAYLOAD_SHA256),
    "stop_c_entry_streak": 0,
}
POST_PUNIT_MANIFEST_COMPACT_JSON = json.dumps(
    POST_PUNIT_MANIFEST,
    sort_keys=True,
    separators=(",", ":"),
)
POST_PUNIT_MANIFEST_COMPUTED_SHA256 = sha256(
    POST_PUNIT_MANIFEST_COMPACT_JSON.encode("ascii")
).hexdigest()
ROUND11_PREREGISTERED_ISSUE_COMMENT = 5231154236
ROUND11_RESULT_ISSUE_COMMENT = 5231263023
ROUND11_VALID_PAYLOAD_SHA256 = (
    "a9960aa342e67462fdef6ada3918424fe3b78d308d19888f7090deee977a4336"
)


def _canonical_report_sha256(report: dict[str, object]) -> str:
    rendered = json.dumps(report, ensure_ascii=False, indent=2, sort_keys=True) + "\n"
    return sha256(rendered.encode("utf-8")).hexdigest()


def _assert_registered_round_payload_hashes(
    actual: tuple[str, ...],
) -> None:
    if actual != REGISTERED_ROUND_PAYLOAD_SHA256:
        raise AssertionError("Round8 registered Round1-7 payload SHA drift")


def _assert_round9_hash_baseline(
    *,
    r0_sha256: str,
    r1_sha256: str,
    round8_sha256: str,
    round8: dict[str, object],
) -> None:
    population = round8.get("population", {})
    progress = round8.get("progress_audit", {})
    baseline_hashes = round8.get("baseline_payload_sha256", {})
    candidate = round8.get("candidate", {})
    if not (
        r0_sha256 == FINAL_R0_SEMANTIC_SHA256
        and r1_sha256 == FINAL_R1_SEMANTIC_SHA256
        and round8_sha256 == ROUND8_DIAGNOSTIC_PAYLOAD_SHA256
        and round8.get("valid") is False
        and progress.get("streak_after_round") == 0
        and tuple(baseline_hashes.values()) == REGISTERED_ROUND_PAYLOAD_SHA256
        and candidate.get("semantic_id") == CERTIFIED_SEMANTIC_ID
        and candidate.get("semantic_sha256") == CERTIFIED_SEMANTIC_SHA256
        and population.get("total_raw_cases") == 1910
        and population.get("prior_full_semantic_payload_ids") == 1908
        and population.get("prior_truncated_semantic_payload_ids") == 1908
        and len(population.get("new_full_semantic_payload_ids", ())) == 2
        and len(population.get("new_truncated_semantic_payload_ids", ())) == 2
        and population.get("full_sha256_collision_count") == 0
        and population.get("truncated_20hex_collision_count") == 0
    ):
        raise AssertionError("Round9 R0/R1/Round1-8 hash baseline drift")


def _assert_round10_hash_baseline(
    *,
    round9_sha256: str,
    round9: dict[str, object],
) -> None:
    """Fail closed before admitting either prior or new Round10 queries."""

    baseline = round9.get("baseline_payload_sha256", {})
    diagnostic = round9.get("round8_diagnostic_baseline", {})
    candidate = round9.get("candidate", {})
    population = round9.get("population", {})
    queries = round9.get("queries", {})
    progress = round9.get("progress_audit", {})
    blocker = round9.get("same_blocker_evidence", {})
    if not (
        round9_sha256 == ROUND9_VALID_PAYLOAD_SHA256
        and round9.get("valid") is True
        and round9.get("final_R0_calibration_comment") == 5230818358
        and baseline.get("r0") == FINAL_R0_SEMANTIC_SHA256
        and baseline.get("r1") == FINAL_R1_SEMANTIC_SHA256
        and tuple(baseline.get("round1_through_round7", ()))
        == REGISTERED_ROUND_PAYLOAD_SHA256
        and baseline.get("round8_diagnostic")
        == ROUND8_DIAGNOSTIC_PAYLOAD_SHA256
        and diagnostic.get("valid") is False
        and diagnostic.get("streak_after_round") == 0
        and diagnostic.get("counted_in_stop_streak") is False
        and candidate.get("semantic_id") == CERTIFIED_SEMANTIC_ID
        and candidate.get("semantic_sha256") == CERTIFIED_SEMANTIC_SHA256
        and population.get("prior_raw_cases_recomputed") == 1910
        and population.get("prior_full_semantic_payload_ids") == 1910
        and population.get("prior_truncated_semantic_payload_ids") == 1910
        and len(population.get("new_full_semantic_payload_ids", ())) == 2
        and len(population.get("new_truncated_semantic_payload_ids", ())) == 2
        and population.get("total_raw_cases") == 1912
        and population.get("total_full_semantic_payload_ids") == 1912
        and population.get("total_truncated_semantic_payload_ids") == 1912
        and population.get("full_sha256_collision_count") == 0
        and population.get("truncated_20hex_collision_count") == 0
        and queries.get("prior_sufficiency_or_necessity_break_count") == 0
        and queries.get("new_sufficiency_break_count") == 0
        and queries.get("new_necessity_break_count") == 0
        and queries.get("new_counterexample_count") == 0
        and progress.get("progress") is False
        and progress.get("streak_after_round") == 1
        and blocker.get("valid_no_progress_1_of_2") is True
    ):
        raise AssertionError("Round10 R0/R1/Round1-9 hash baseline drift")


def _assert_round11_current_calibration_gate(
    *,
    current_r0_sha256: str,
    current_r0: dict[str, object],
    r1_sha256: str,
    r1: dict[str, object],
    manifest_compact_json: str,
    manifest_sha256: str,
) -> None:
    """Reject stale calibration before regenerating any historical query."""

    calibration = current_r0.get("calibration", {})
    calibration_a = calibration.get("a_three_lean_obstructions", ())
    calibration_b = calibration.get("b_derived_support_hole", {})
    calibration_c = calibration.get("c_block_reduction", {})
    calibration_d = calibration.get("d_indicator_realizability", {})
    calibration_e = calibration.get("e_canonical_firing_oracle", {})
    indicator_factors = calibration_d.get("factors", ())
    verdicts = r1.get("verdicts", ())
    necessity_witnesses = r1.get("necessity_witnesses", ())
    if not (
        current_r0_sha256 == POST_PUNIT_R0_SEMANTIC_SHA256
        and current_r0_sha256 != FINAL_R0_SEMANTIC_SHA256
        and current_r0.get("r0_pass") is True
        and len(calibration_a) == 3
        and all(item.get("calibration_pass") is True for item in calibration_a)
        and calibration_b.get("calibration_pass") is True
        and calibration_c.get("pass") is True
        and calibration_d.get("all_nonempty_A_realized") is True
        and calibration_e.get("canonical_oracle_pass") is True
        and len(indicator_factors) == 2
        and all(
            factor.get("law_type") == "PUnit"
            and factor.get("law_type_cardinality") == 1
            and factor.get("value_type") == "Bool"
            and factor.get("all_pass") is True
            for factor in indicator_factors
        )
        and r1_sha256 == FINAL_R1_SEMANTIC_SHA256
        and r1.get("all_seven_verdicts_fixed") is True
        and len(verdicts) == 7
        and [item.get("clause") for item in verdicts]
        == [f"C{index}" for index in range(7)]
        and all(
            item.get("verdict") == "not-necessary"
            and item.get("evidence_schema_satisfied") is True
            and bool(item.get("witness"))
            for item in verdicts
        )
        and len(necessity_witnesses) == 7
        and all(
            witness.get("clause") == f"C{index}"
            and witness.get("evidence_schema")
            == "uniform comparison and named-clause failure"
            and witness.get("witness_pass") is True
            for index, witness in enumerate(necessity_witnesses)
        )
        and manifest_compact_json == POST_PUNIT_MANIFEST_COMPACT_JSON
        and manifest_sha256 == POST_PUNIT_MANIFEST_REGISTERED_SHA256
        and manifest_sha256 == POST_PUNIT_MANIFEST_COMPUTED_SHA256
        and POST_PUNIT_MANIFEST["stop_c_entry_streak"] == 0
        and POST_PUNIT_MANIFEST["prior_population"] == 1914
        and POST_PUNIT_MANIFEST["registered_round1_through_round7"]
        == list(REGISTERED_ROUND_PAYLOAD_SHA256)
    ):
        raise AssertionError("Round11 current post-PUnit calibration gate drift")


def _assert_round11_hash_baseline(
    *,
    current_r0_sha256: str,
    current_r0: dict[str, object],
    r1_sha256: str,
    r1: dict[str, object],
    round9_sha256: str,
    round9: dict[str, object],
    round10_sha256: str,
    round10: dict[str, object],
    manifest_compact_json: str,
    manifest_sha256: str,
) -> None:
    """Admit Round11 queries only on the synchronized post-PUnit baseline."""

    _assert_round11_current_calibration_gate(
        current_r0_sha256=current_r0_sha256,
        current_r0=current_r0,
        r1_sha256=r1_sha256,
        r1=r1,
        manifest_compact_json=manifest_compact_json,
        manifest_sha256=manifest_sha256,
    )

    round9_queries = round9.get("queries", {})
    round10_queries = round10.get("queries", {})
    round10_population = round10.get("population", {})
    round10_candidate = round10.get("candidate", {})
    if not (
        round9_sha256 == ROUND9_VALID_PAYLOAD_SHA256
        and round9.get("valid") is True
        and round9_queries.get("prior_sufficiency_or_necessity_break_count") == 0
        and round9_queries.get("new_sufficiency_break_count") == 0
        and round9_queries.get("new_necessity_break_count") == 0
        and round9_queries.get("new_counterexample_count") == 0
        and round9.get("progress_audit", {}).get("progress") is False
        and round10_sha256 == HISTORICAL_ROUND10_PAYLOAD_SHA256
        and round10.get("valid") is True
        and round10_candidate.get("semantic_id") == CERTIFIED_SEMANTIC_ID
        and round10_candidate.get("semantic_sha256") == CERTIFIED_SEMANTIC_SHA256
        and round10_queries.get("prior_sufficiency_or_necessity_break_count") == 0
        and round10_queries.get("new_sufficiency_break_count") == 0
        and round10_queries.get("new_necessity_break_count") == 0
        and round10_queries.get("new_counterexample_count") == 0
        and round10.get("progress_audit", {}).get("progress") is False
        and round10_population.get("total_raw_cases") == 1914
        and round10_population.get("total_full_semantic_payload_ids") == 1914
        and round10_population.get("total_truncated_semantic_payload_ids") == 1914
        and round10_population.get("full_sha256_collision_count") == 0
        and round10_population.get("truncated_20hex_collision_count") == 0
        and round10.get("round8_diagnostic_baseline", {}).get("valid") is False
        and round10.get("round9_valid_baseline", {}).get("valid") is True
    ):
        raise AssertionError("Round11 post-PUnit/historical manifest baseline drift")


def _assert_round12_hash_baseline(
    *,
    current_r0_sha256: str,
    current_r0: dict[str, object],
    r1_sha256: str,
    r1: dict[str, object],
    round11_sha256: str,
    round11: dict[str, object],
    manifest_compact_json: str,
    manifest_sha256: str,
) -> None:
    """Reject Round12 before query unless Round11 is the fixed 1/2 entry."""

    _assert_round11_current_calibration_gate(
        current_r0_sha256=current_r0_sha256,
        current_r0=current_r0,
        r1_sha256=r1_sha256,
        r1=r1,
        manifest_compact_json=manifest_compact_json,
        manifest_sha256=manifest_sha256,
    )
    candidate = round11.get("candidate", {})
    queries = round11.get("queries", {})
    progress = round11.get("progress_audit", {})
    same_blocker = round11.get("same_blocker_evidence", {})
    population = round11.get("population", {})
    code_audit = round11.get("canonical_code_audit", {})
    admission = round11.get("query_admission", {})
    if not (
        round11_sha256 == ROUND11_VALID_PAYLOAD_SHA256
        and ROUND11_RESULT_ISSUE_COMMENT == 5231263023
        and round11.get("valid") is True
        and round11.get("preregistered_issue_comment")
        == ROUND11_PREREGISTERED_ISSUE_COMMENT
        and candidate.get("semantic_id") == CERTIFIED_SEMANTIC_ID
        and candidate.get("semantic_sha256") == CERTIFIED_SEMANTIC_SHA256
        and round11.get("blocker_id") == "PB-R2-NONFREE-GLOBAL-FACE-CHAIN"
        and queries.get("prior_sufficiency_or_necessity_break_count") == 0
        and queries.get("new_sufficiency_break_count") == 0
        and queries.get("new_necessity_break_count") == 0
        and queries.get("new_counterexample_count") == 0
        and progress.get("new_verdicts") == []
        and progress.get("new_canonical_nonisomorphic_counterexamples") == []
        and progress.get("candidate_semantic_change") is False
        and progress.get("additional_calibration_fixes") == []
        and progress.get("progress") is False
        and progress.get("streak_after_round") == 1
        and same_blocker.get("valid_no_progress_1_of_2") is True
        and population.get("total_raw_cases") == 1916
        and population.get("total_full_semantic_payload_ids") == 1916
        and population.get("total_truncated_semantic_payload_ids") == 1916
        and population.get("full_sha256_collision_count") == 0
        and population.get("truncated_20hex_collision_count") == 0
        and code_audit.get("registered_code_count") == 12
        and code_audit.get("full_sha256_collision_count") == 0
        and code_audit.get("truncated_20hex_collision_count") == 0
        and admission.get("post_punit_r0_sha256")
        == POST_PUNIT_R0_SEMANTIC_SHA256
        and admission.get("manifest_registered_sha256")
        == POST_PUNIT_MANIFEST_REGISTERED_SHA256
        and admission.get("all_gates_pass") is True
        and round11.get("calibration_progress_reset", {}).get("entry_streak") == 0
    ):
        raise AssertionError("Round12 Round11/post-PUnit admission baseline drift")


@dataclass(frozen=True)
class SideData:
    nerve: Nerve
    chart_supports: tuple[frozenset[int], ...]
    edge_supports: tuple[frozenset[int], ...]
    face_supports: tuple[frozenset[int], ...]


@dataclass(frozen=True)
class FaceClass:
    members: tuple[int, ...]
    boundary: tuple[int, int, int]
    support: frozenset[int]


@dataclass(frozen=True)
class ReducedSide:
    data: SideData
    face_classes: tuple[FaceClass, ...]
    retained_face_classes: tuple[int, ...]
    retained_edges: tuple[int, ...]
    critical_edges: tuple[int, ...]
    critical_vertices: tuple[int, ...]
    removed_free_pairs: tuple[tuple[int, int], ...]

    @property
    def retained_face_members(self) -> frozenset[int]:
        return frozenset(
            member
            for index in self.retained_face_classes
            for member in self.face_classes[index].members
        )

    @property
    def retained_face_member_to_class(self) -> dict[int, int]:
        return {
            member: index
            for index in self.retained_face_classes
            for member in self.face_classes[index].members
        }


@dataclass(frozen=True)
class ScopedComparison:
    coarse: SideData
    fine: SideData
    morphism: NerveMorphism


def _intersect_supports(
    supports: Iterable[frozenset[int]],
    targets: frozenset[int],
) -> tuple[frozenset[int], ...]:
    return tuple(support & targets for support in supports)


def _whole_scope(comparison: UniformComparison) -> ScopedComparison:
    coarse_edges, coarse_faces = derived_cell_supports(
        comparison.morphism.coarse,
        comparison.coarse_chart_supports,
    )
    fine_edges, fine_faces = derived_cell_supports(
        comparison.morphism.fine,
        comparison.fine_chart_supports,
    )
    return ScopedComparison(
        coarse=SideData(
            comparison.morphism.coarse,
            comparison.coarse_chart_supports,
            coarse_edges,
            coarse_faces,
        ),
        fine=SideData(
            comparison.morphism.fine,
            comparison.fine_chart_supports,
            fine_edges,
            fine_faces,
        ),
        morphism=comparison.morphism,
    )


def _a_scope(
    comparison: UniformComparison,
    coarse_targets: frozenset[int],
) -> ScopedComparison:
    sub = comparison.coordinate_subcomparison(coarse_targets)
    coarse_all_edges, coarse_all_faces = derived_cell_supports(
        comparison.morphism.coarse,
        comparison.coarse_chart_supports,
    )
    fine_all_edges, fine_all_faces = derived_cell_supports(
        comparison.morphism.fine,
        comparison.fine_chart_supports,
    )
    return ScopedComparison(
        coarse=SideData(
            sub.coarse.nerve,
            _intersect_supports(
                (comparison.coarse_chart_supports[index] for index in sub.coarse.vertices),
                coarse_targets,
            ),
            _intersect_supports(
                (coarse_all_edges[index] for index in sub.coarse.edges),
                coarse_targets,
            ),
            _intersect_supports(
                (coarse_all_faces[index] for index in sub.coarse.faces),
                coarse_targets,
            ),
        ),
        fine=SideData(
            sub.fine.nerve,
            _intersect_supports(
                (comparison.fine_chart_supports[index] for index in sub.fine.vertices),
                sub.fine_targets,
            ),
            _intersect_supports(
                (fine_all_edges[index] for index in sub.fine.edges),
                sub.fine_targets,
            ),
            _intersect_supports(
                (fine_all_faces[index] for index in sub.fine.faces),
                sub.fine_targets,
            ),
        ),
        morphism=sub.morphism,
    )


def _face_classes(side: SideData) -> tuple[FaceClass, ...]:
    groups: dict[tuple[tuple[int, int, int], tuple[int, ...]], list[int]] = {}
    for face, boundary in enumerate(side.nerve.faces):
        key = (boundary, tuple(sorted(side.face_supports[face])))
        groups.setdefault(key, []).append(face)
    return tuple(
        FaceClass(tuple(members), boundary, frozenset(support))
        for (boundary, support), members in sorted(groups.items())
    )


def _path_without_edge(nerve: Nerve, retained: set[int], omitted: int) -> bool:
    left, right = nerve.edges[omitted]
    if left == right:
        return True
    adjacency = {vertex: set() for vertex in range(nerve.vertices)}
    for edge in retained:
        if edge == omitted:
            continue
        source, target = nerve.edges[edge]
        adjacency[source].add(target)
        adjacency[target].add(source)
    reached = {left}
    frontier = [left]
    while frontier:
        current = frontier.pop()
        for neighbour in sorted(adjacency[current] - reached):
            reached.add(neighbour)
            frontier.append(neighbour)
    return right in reached


def reduce_side(side: SideData) -> ReducedSide:
    classes = _face_classes(side)
    eligible: list[tuple[int, int]] = []
    for class_index, face_class in enumerate(classes):
        edge0, edge1, edge2 = face_class.boundary
        if not edge0 == edge1 == edge2:
            continue
        edge = edge0
        if side.nerve.edges[edge][0] != side.nerve.edges[edge][1]:
            continue
        if any(
            edge in other.boundary
            for other_index, other in enumerate(classes)
            if other_index != class_index
        ):
            continue
        eligible.append((edge, class_index))

    removed_edges = {edge for edge, _ in eligible}
    removed_classes = {face_class for _, face_class in eligible}
    retained_edges = set(range(len(side.nerve.edges))) - removed_edges
    retained_classes = tuple(
        index for index in range(len(classes)) if index not in removed_classes
    )
    critical_edges = tuple(
        edge
        for edge in sorted(retained_edges)
        if _path_without_edge(side.nerve, retained_edges, edge)
    )
    critical_vertices = {
        vertex
        for edge in critical_edges
        for vertex in side.nerve.edges[edge]
    }
    for class_index in retained_classes:
        for edge in classes[class_index].boundary:
            critical_vertices.update(side.nerve.edges[edge])
    return ReducedSide(
        data=side,
        face_classes=classes,
        retained_face_classes=retained_classes,
        retained_edges=tuple(sorted(retained_edges)),
        critical_edges=critical_edges,
        critical_vertices=tuple(sorted(critical_vertices)),
        removed_free_pairs=tuple(sorted(eligible)),
    )


def _connected(vertices: set[int], edges: Iterable[tuple[int, int]]) -> bool:
    if not vertices:
        return False
    adjacency = {vertex: set() for vertex in vertices}
    for left, right in edges:
        if left in vertices and right in vertices:
            adjacency[left].add(right)
            adjacency[right].add(left)
    reached = {min(vertices)}
    frontier = list(reached)
    while frontier:
        current = frontier.pop()
        for neighbour in sorted(adjacency[current] - reached):
            reached.add(neighbour)
            frontier.append(neighbour)
    return reached == vertices


def _active_fine_vertices(
    scope: ScopedComparison,
    coarse: ReducedSide,
    fine: ReducedSide,
) -> set[int]:
    active: set[int] = set()
    critical_coarse_edges = set(coarse.critical_edges)
    for edge in fine.retained_edges:
        mapped = scope.morphism.edge_map[edge]
        if mapped in critical_coarse_edges:
            active.update(scope.fine.nerve.edges[edge])

    retained_coarse_faces = coarse.retained_face_members
    for class_index in fine.retained_face_classes:
        for face in fine.face_classes[class_index].members:
            mapped = scope.morphism.face_map[face]
            if mapped in retained_coarse_faces:
                for edge in scope.fine.nerve.faces[face]:
                    active.update(scope.fine.nerve.edges[edge])
    return active


def _c0(scope: ScopedComparison, coarse: ReducedSide, fine: ReducedSide, pi: tuple[int, ...]) -> bool:
    active = _active_fine_vertices(scope, coarse, fine)
    for coarse_vertex in coarse.critical_vertices:
        image_support = frozenset(
            pi[target]
            for fine_vertex in sorted(active)
            if scope.morphism.vertex_map[fine_vertex] == coarse_vertex
            for target in scope.fine.chart_supports[fine_vertex]
        )
        if image_support != scope.coarse.chart_supports[coarse_vertex]:
            return False
    return True


def _c1(scope: ScopedComparison, coarse: ReducedSide, fine: ReducedSide) -> bool:
    active = _active_fine_vertices(scope, coarse, fine)
    for coarse_vertex in coarse.critical_vertices:
        ports = {
            vertex
            for vertex in active
            if scope.morphism.vertex_map[vertex] == coarse_vertex
        }
        if not _connected(ports, scope.fine.nerve.edges):
            return False
    return True


def _c2(scope: ScopedComparison, coarse: ReducedSide, fine: ReducedSide) -> bool:
    retained_maps = {
        scope.morphism.edge_map[edge]
        for edge in fine.retained_edges
        if scope.morphism.edge_map[edge] is not None
    }
    return all(edge in retained_maps for edge in coarse.critical_edges)


def _local_unmapped_h1_dimension(
    scope: ScopedComparison,
    fine: ReducedSide,
    coarse_vertex: int,
) -> int:
    fiber = tuple(
        vertex
        for vertex, mapped in enumerate(scope.morphism.vertex_map)
        if mapped == coarse_vertex
    )
    vertex_index = {vertex: index for index, vertex in enumerate(fiber)}
    edges = tuple(
        edge
        for edge in fine.retained_edges
        if scope.morphism.edge_map[edge] is None
        and all(vertex in vertex_index for vertex in scope.fine.nerve.edges[edge])
    )
    edge_index = {edge: index for index, edge in enumerate(edges)}
    local_edges = tuple(
        tuple(vertex_index[vertex] for vertex in scope.fine.nerve.edges[edge])
        for edge in edges
    )
    local_faces: list[tuple[int, int, int]] = []
    for class_index in fine.retained_face_classes:
        face_class = fine.face_classes[class_index]
        if not any(scope.morphism.face_map[face] is None for face in face_class.members):
            continue
        if all(edge in edge_index for edge in face_class.boundary):
            local_faces.append(tuple(edge_index[edge] for edge in face_class.boundary))
    local = Nerve(len(fiber), local_edges, tuple(local_faces))
    return local.d1().kernel_basis().cols - local.d0().rank()


def _c3(scope: ScopedComparison, fine: ReducedSide) -> bool:
    return all(
        _local_unmapped_h1_dimension(scope, fine, coarse_vertex) == 0
        for coarse_vertex in range(scope.coarse.nerve.vertices)
    )


def _c4(scope: ScopedComparison, coarse: ReducedSide, fine: ReducedSide) -> bool:
    mapped_fine_faces = {
        scope.morphism.face_map[face]
        for class_index in fine.retained_face_classes
        for face in fine.face_classes[class_index].members
        if scope.morphism.face_map[face] is not None
    }
    return all(
        bool(set(coarse.face_classes[index].members) & mapped_fine_faces)
        for index in coarse.retained_face_classes
    )


def _direct_lifttwin_graph(
    scope: ScopedComparison,
    coarse: ReducedSide,
    fine: ReducedSide,
    coarse_edge: int,
    *,
    relation_mode: str,
) -> tuple[tuple[int, ...], dict[int, set[int]]]:
    if relation_mode not in {"broad", "certified"}:
        raise ValueError(f"unsupported LiftTwin relation: {relation_mode}")
    lifts = tuple(
        edge
        for edge in fine.retained_edges
        if scope.morphism.edge_map[edge] == coarse_edge
    )
    adjacency = {edge: set() for edge in lifts}
    retained_fine_faces = tuple(
        face
        for class_index in fine.retained_face_classes
        for face in fine.face_classes[class_index].members
    )
    coarse_face_to_class = coarse.retained_face_member_to_class

    for left_index, left in enumerate(lifts):
        for right in lifts[left_index + 1 :]:
            if scope.fine.edge_supports[left] != scope.fine.edge_supports[right]:
                continue
            related = (
                _broad_pair(
                    scope,
                    retained_fine_faces,
                    coarse_face_to_class,
                    left,
                    right,
                )
                if relation_mode == "broad"
                else _certified_pair(
                    scope,
                    coarse,
                    retained_fine_faces,
                    coarse_face_to_class,
                    coarse_edge,
                    left,
                    right,
                )
            )
            if related:
                adjacency[left].add(right)
                adjacency[right].add(left)
    return lifts, adjacency


def _broad_pair(
    scope: ScopedComparison,
    retained_fine_faces: tuple[int, ...],
    coarse_face_to_class: dict[int, int],
    left: int,
    right: int,
) -> bool:
    same_face = any(
        left in scope.fine.nerve.faces[face]
        and right in scope.fine.nerve.faces[face]
        for face in retained_fine_faces
    )
    same_coarse_class = any(
        left in scope.fine.nerve.faces[left_face]
        and right in scope.fine.nerve.faces[right_face]
        and scope.morphism.face_map[left_face] in coarse_face_to_class
        and scope.morphism.face_map[right_face] in coarse_face_to_class
        and coarse_face_to_class[scope.morphism.face_map[left_face]]
        == coarse_face_to_class[scope.morphism.face_map[right_face]]
        for left_face in retained_fine_faces
        for right_face in retained_fine_faces
    )
    return same_face or same_coarse_class


def _certified_pair(
    scope: ScopedComparison,
    coarse: ReducedSide,
    retained_fine_faces: tuple[int, ...],
    coarse_face_to_class: dict[int, int],
    coarse_edge: int,
    left: int,
    right: int,
) -> bool:
    # SLOT certificate.
    for left_face in retained_fine_faces:
        for right_face in retained_fine_faces:
            mapped_left = scope.morphism.face_map[left_face]
            mapped_right = scope.morphism.face_map[right_face]
            if (
                mapped_left not in coarse_face_to_class
                or mapped_right not in coarse_face_to_class
                or coarse_face_to_class[mapped_left]
                != coarse_face_to_class[mapped_right]
                or scope.fine.face_supports[left_face]
                != scope.fine.face_supports[right_face]
            ):
                continue
            left_boundary = scope.fine.nerve.faces[left_face]
            right_boundary = scope.fine.nerve.faces[right_face]
            different = [
                slot
                for slot in range(3)
                if left_boundary[slot] != right_boundary[slot]
            ]
            if len(different) == 1:
                slot = different[0]
                if {left_boundary[slot], right_boundary[slot]} == {left, right}:
                    return True

    # KILL certificate.
    retained_coarse_faces = coarse.retained_face_members
    for relation_face in retained_fine_faces:
        boundary = scope.fine.nerve.faces[relation_face]
        if boundary[:2] not in ((left, right), (right, left)):
            continue
        z = boundary[2]
        if not (
            scope.fine.edge_supports[left]
            == scope.fine.edge_supports[right]
            == scope.fine.edge_supports[z]
        ):
            continue
        mapped_z = scope.morphism.edge_map[z]
        mapped_relation = scope.morphism.face_map[relation_face]
        if mapped_z is None or mapped_relation not in retained_coarse_faces:
            continue
        if scope.coarse.nerve.faces[mapped_relation] != (
            coarse_edge,
            coarse_edge,
            mapped_z,
        ):
            continue
        for kill_face in retained_fine_faces:
            if scope.fine.nerve.faces[kill_face] != (z, z, z):
                continue
            mapped_kill = scope.morphism.face_map[kill_face]
            if (
                mapped_kill in retained_coarse_faces
                and scope.coarse.nerve.faces[mapped_kill]
                == (mapped_z, mapped_z, mapped_z)
                and scope.fine.face_supports[relation_face]
                == scope.fine.face_supports[kill_face]
            ):
                return True
    return False


def _components(vertices: tuple[int, ...], adjacency: dict[int, set[int]]) -> tuple[tuple[int, ...], ...]:
    remaining = set(vertices)
    result: list[tuple[int, ...]] = []
    while remaining:
        start = min(remaining)
        reached = {start}
        frontier = [start]
        while frontier:
            current = frontier.pop()
            for neighbour in sorted(adjacency[current] - reached):
                reached.add(neighbour)
                frontier.append(neighbour)
        remaining -= reached
        result.append(tuple(sorted(reached)))
    return tuple(result)


def _c5_c6(
    scope: ScopedComparison,
    coarse: ReducedSide,
    fine: ReducedSide,
    *,
    c5_mode: str,
) -> tuple[bool, bool, dict[str, object]]:
    if c5_mode not in {"clique", "component", "certified"}:
        raise ValueError(f"unsupported C5 mode: {c5_mode}")
    c5 = True
    c6 = True
    details: dict[str, object] = {}
    for edge in coarse.critical_edges:
        relation_mode = "certified" if c5_mode == "certified" else "broad"
        lifts, adjacency = _direct_lifttwin_graph(
            scope,
            coarse,
            fine,
            edge,
            relation_mode=relation_mode,
        )
        clique = all(
            right in adjacency[left]
            for index, left in enumerate(lifts)
            for right in lifts[index + 1 :]
        )
        components = _components(lifts, adjacency)
        c5_edge = clique if c5_mode == "clique" else len(components) <= 1
        if not c5_edge:
            c5 = False
        coarse_selfloop = scope.coarse.nerve.edges[edge][0] == scope.coarse.nerve.edges[edge][1]
        component_has_selfloop = tuple(
            any(
                scope.fine.nerve.edges[lift][0] == scope.fine.nerve.edges[lift][1]
                for lift in component
            )
            for component in components
        )
        if coarse_selfloop and not all(component_has_selfloop):
            c6 = False
        details[str(edge)] = {
            "lifts": list(lifts),
            "direct_edges": [
                [left, right]
                for left in lifts
                for right in sorted(adjacency[left])
                if left < right
            ],
            "clique": clique,
            "c5_mode": c5_mode,
            "c5_edge_holds": c5_edge,
            "components": [list(component) for component in components],
            "component_has_fine_selfloop": list(component_has_selfloop),
        }
    return c5, c6, details


def _reduction_summary(reduced: ReducedSide) -> dict[str, object]:
    return {
        "face_classes": [
            {
                "members": list(face_class.members),
                "boundary": list(face_class.boundary),
                "support": sorted(face_class.support),
            }
            for face_class in reduced.face_classes
        ],
        "removed_free_pairs": [list(pair) for pair in reduced.removed_free_pairs],
        "retained_edges": list(reduced.retained_edges),
        "retained_face_classes": list(reduced.retained_face_classes),
        "critical_edges": list(reduced.critical_edges),
        "critical_vertices": list(reduced.critical_vertices),
    }


def candidate_evaluation(
    comparison: UniformComparison,
    *,
    c5_mode: str = "clique",
) -> dict[str, object]:
    whole = _whole_scope(comparison)
    coarse_whole = reduce_side(whole.coarse)
    fine_whole = reduce_side(whole.fine)
    c0 = _c0(whole, coarse_whole, fine_whole, comparison.factor_pi)
    c5, c6, twin_details = _c5_c6(
        whole,
        coarse_whole,
        fine_whole,
        c5_mode=c5_mode,
    )

    per_subset = []
    aggregate = {"C0*": c0, "C1*": True, "C2*": True, "C3*": True, "C4*": True, "C5*": c5, "C6*": c6}
    for targets in nonempty_subsets(comparison.coarse_target_count):
        scope = _a_scope(comparison, targets)
        coarse = reduce_side(scope.coarse)
        fine = reduce_side(scope.fine)
        relative = {
            "C1*": _c1(scope, coarse, fine),
            "C2*": _c2(scope, coarse, fine),
            "C3*": _c3(scope, fine),
            "C4*": _c4(scope, coarse, fine),
        }
        for clause, value in relative.items():
            aggregate[clause] = aggregate[clause] and value
        per_subset.append(
            {
                "coarse_targets_A": sorted(targets),
                "conditions": relative,
                "coarse_reduction": _reduction_summary(coarse),
                "fine_reduction": _reduction_summary(fine),
            }
        )
    return {
        "aggregate": aggregate,
        "all": all(aggregate.values()),
        "whole": {
            "conditions": {"C0*": c0, "C5*": c5, "C6*": c6},
            "coarse_reduction": _reduction_summary(coarse_whole),
            "fine_reduction": _reduction_summary(fine_whole),
            "direct_lifttwin": twin_details,
        },
        "per_subset": per_subset,
    }


def chain3_fixture() -> UniformComparison:
    coarse = Nerve(1, ((0, 0), (0, 0), (0, 0)), ((1, 1, 1), (2, 2, 2), (0, 0, 1), (0, 0, 2)))
    fine = Nerve(1, ((0, 0), (0, 0), (0, 0), (0, 0), (0, 0)), ((3, 3, 3), (4, 4, 4), (0, 1, 3), (1, 2, 4)))
    unit = (frozenset((0,)),)
    return UniformComparison(
        name="R2_round1_Chain3",
        morphism=NerveMorphism(coarse, fine, (0,), (0, 0, 0, 1, 2), (0, 1, 2, 3)),
        coarse_target_count=1,
        fine_target_count=1,
        factor_pi=(0,),
        coarse_chart_supports=unit,
        fine_chart_supports=unit,
    )


def unkilled_twin_fixture() -> UniformComparison:
    coarse = Nerve(1, ((0, 0), (0, 0)), ((0, 0, 1),))
    fine = Nerve(1, ((0, 0), (0, 0), (0, 0)), ((0, 1, 2),))
    unit = (frozenset((0,)),)
    return UniformComparison(
        name="R2_round2_UnkilledTwin",
        morphism=NerveMorphism(coarse, fine, (0,), (0, 0, 1), (0,)),
        coarse_target_count=1,
        fine_target_count=1,
        factor_pi=(0,),
        coarse_chart_supports=unit,
        fine_chart_supports=unit,
    )


def _full_identity_comparison(name: str, nerve: Nerve) -> UniformComparison:
    return UniformComparison(
        name=name,
        morphism=NerveMorphism(
            nerve,
            nerve,
            tuple(range(nerve.vertices)),
            tuple(range(len(nerve.edges))),
            tuple(range(len(nerve.faces))),
        ),
        coarse_target_count=3,
        fine_target_count=4,
        factor_pi=(0, 0, 1, 2),
        coarse_chart_supports=tuple(
            frozenset((0, 1, 2)) for _ in range(nerve.vertices)
        ),
        fine_chart_supports=tuple(
            frozenset((0, 1, 2, 3)) for _ in range(nerve.vertices)
        ),
    )


def closed_2d_expansion_fixtures() -> tuple[UniformComparison, ...]:
    duplicate_triangle = Nerve(
        3,
        ((0, 1), (0, 2), (1, 2), (0, 1)),
        ((0, 1, 2), (0, 1, 2)),
    )
    shared_triangles = Nerve(
        4,
        ((0, 1), (0, 2), (1, 2), (0, 3), (1, 3), (0, 1)),
        ((0, 1, 2), (0, 3, 4)),
    )
    tetrahedron = Nerve(
        4,
        ((0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3), (0, 1)),
        ((0, 1, 3), (0, 2, 4), (1, 2, 5), (3, 4, 5)),
    )
    return (
        _full_identity_comparison("R2_round4_D0_duplicate_triangle", duplicate_triangle),
        _full_identity_comparison("R2_round4_D1_shared_triangles", shared_triangles),
        _full_identity_comparison("R2_round4_D2_tetrahedron_parallel", tetrahedron),
    )


def mixed_support_square_variants() -> Iterator[UniformComparison]:
    square = Nerve(4, ((0, 1), (1, 2), (2, 3), (3, 0)), ())
    morphism = NerveMorphism(square, square, (0, 1, 2, 3), (0, 1, 2, 3), ())
    pi = (0, 0, 1, 2, 3)
    masks = (
        frozenset((0,)),
        frozenset((1,)),
        frozenset((0, 1)),
        frozenset((2,)),
        frozenset((3,)),
        frozenset((0, 1, 2, 3)),
    )
    for coarse_supports in product(masks, repeat=4):
        fine_supports = tuple(
            frozenset(
                fine_target
                for fine_target, coarse_target in enumerate(pi)
                if coarse_target in support
            )
            for support in coarse_supports
        )
        yield UniformComparison(
            name=f"R2_round5_mixed_square:{coarse_supports}",
            morphism=morphism,
            coarse_target_count=4,
            fine_target_count=5,
            factor_pi=pi,
            coarse_chart_supports=tuple(coarse_supports),
            fine_chart_supports=fine_supports,
        )


def face_chain_fixture(
    name: str,
    lift_count: int,
    *,
    coarse_target_count: int = 1,
    fine_target_count: int = 1,
    factor_pi: tuple[int, ...] = (0,),
) -> UniformComparison:
    if lift_count < 2:
        raise ValueError("a face chain needs at least two lifts")
    relation_count = lift_count - 1
    coarse_edges = tuple((0, 0) for _ in range(1 + relation_count))
    fine_edges = tuple((0, 0) for _ in range(lift_count + relation_count))
    coarse_faces: list[tuple[int, int, int]] = []
    fine_faces: list[tuple[int, int, int]] = []
    for index in range(relation_count):
        coarse_z = 1 + index
        fine_z = lift_count + index
        coarse_faces.extend(((coarse_z, coarse_z, coarse_z), (0, 0, coarse_z)))
        fine_faces.extend(((fine_z, fine_z, fine_z), (index, index + 1, fine_z)))
    coarse = Nerve(1, coarse_edges, tuple(coarse_faces))
    fine = Nerve(1, fine_edges, tuple(fine_faces))
    coarse_full = frozenset(range(coarse_target_count))
    fine_full = frozenset(range(fine_target_count))
    return UniformComparison(
        name=name,
        morphism=NerveMorphism(
            coarse,
            fine,
            (0,),
            tuple(0 for _ in range(lift_count))
            + tuple(1 + index for index in range(relation_count)),
            tuple(range(2 * relation_count)),
        ),
        coarse_target_count=coarse_target_count,
        fine_target_count=fine_target_count,
        factor_pi=factor_pi,
        coarse_chart_supports=(coarse_full,),
        fine_chart_supports=(fine_full,),
    )


def round6_face_chains() -> tuple[UniformComparison, ...]:
    return (
        face_chain_fixture("R2_round6_LinearChain4", 4),
        face_chain_fixture("R2_round6_LinearChain5", 5),
    )


def face_chain_graph_fixture(
    name: str,
    lift_count: int,
    relations: tuple[tuple[int, int], ...],
) -> UniformComparison:
    if any(
        not (0 <= left < lift_count and 0 <= right < lift_count and left != right)
        for left, right in relations
    ):
        raise ValueError("face-chain graph relation leaves the lift set")
    coarse_edges = tuple((0, 0) for _ in range(1 + len(relations)))
    fine_edges = tuple((0, 0) for _ in range(lift_count + len(relations)))
    coarse_faces: list[tuple[int, int, int]] = []
    fine_faces: list[tuple[int, int, int]] = []
    for index, (left, right) in enumerate(relations):
        coarse_z = 1 + index
        fine_z = lift_count + index
        coarse_faces.extend(((coarse_z, coarse_z, coarse_z), (0, 0, coarse_z)))
        fine_faces.extend(((fine_z, fine_z, fine_z), (left, right, fine_z)))
    coarse = Nerve(1, coarse_edges, tuple(coarse_faces))
    fine = Nerve(1, fine_edges, tuple(fine_faces))
    return UniformComparison(
        name=name,
        morphism=NerveMorphism(
            coarse,
            fine,
            (0,),
            tuple(0 for _ in range(lift_count))
            + tuple(1 + index for index in range(len(relations))),
            tuple(range(2 * len(relations))),
        ),
        coarse_target_count=4,
        fine_target_count=5,
        factor_pi=(0, 0, 1, 2, 3),
        coarse_chart_supports=(frozenset((0, 1, 2, 3)),),
        fine_chart_supports=(frozenset((0, 1, 2, 3, 4)),),
    )


def round7_face_chain_graphs() -> tuple[UniformComparison, ...]:
    return (
        face_chain_graph_fixture(
            "R2_round7_B0_branching_tree",
            5,
            ((0, 1), (1, 2), (1, 3), (3, 4)),
        ),
        face_chain_graph_fixture(
            "R2_round7_B1_cyclic_chain",
            4,
            ((0, 1), (1, 2), (2, 3), (3, 0)),
        ),
    )


R8_L6_KILL_RELATIONS = (
    (0, 1),
    (1, 2),
    (2, 3),
    (3, 4),
    (4, 5),
)
R8_CL3_SLOT_RELATIONS = (
    (0, 1),
    (1, 2),
    (2, 0),
    (3, 4),
    (4, 5),
    (5, 3),
    (0, 3),
    (1, 4),
    (2, 5),
)
R9_DIAMOND_KILL_RELATIONS = ((0, 1), (1, 2), (2, 0))
R9_DIAMOND_SLOT_RELATIONS = ((1, 3), (3, 2))
R9_FIGURE8_KILL_RELATIONS = (
    (0, 1),
    (1, 2),
    (2, 0),
    (0, 3),
    (3, 4),
    (4, 0),
)
R10_A_KILL_RELATIONS = ((0, 2), (0, 3), (1, 4))
R10_A_SLOT_RELATIONS = ((0, 4), (1, 2), (1, 3))
R10_B_K4_KILL_RELATIONS = ((0, 1), (1, 2), (2, 0))
R10_B_K4_SLOT_RELATIONS = ((0, 3), (1, 3), (2, 3))
R10_B_STAR_KILL_RELATIONS = ((0, 1),)
R10_B_STAR_SLOT_RELATIONS = ((0, 2), (0, 3))
R11_W5_KILL_RELATIONS = ((1, 2), (2, 3), (3, 4), (4, 5), (1, 5))
R11_W5_SLOT_RELATIONS = ((0, 1), (0, 2), (0, 3), (0, 4), (0, 5))
R11_K33_KILL_RELATIONS = ((0, 3), (1, 4), (2, 5))
R11_K33_SLOT_RELATIONS = (
    (0, 4),
    (0, 5),
    (1, 3),
    (1, 5),
    (2, 3),
    (2, 4),
)
R12_OCTA_KILL_RELATIONS = (
    (0, 2),
    (2, 4),
    (1, 4),
    (1, 3),
    (3, 5),
    (0, 5),
)
R12_OCTA_SLOT_RELATIONS = (
    (0, 3),
    (1, 2),
    (0, 4),
    (1, 5),
    (2, 5),
    (3, 4),
)
R12_HOUSE_KILL_RELATIONS = ((0, 1), (2, 3), (1, 4))
R12_HOUSE_SLOT_RELATIONS = ((1, 2), (0, 3), (2, 4))
R12_STAR_KILL_RELATIONS = ((0, 1), (0, 2))
R12_STAR_SLOT_RELATIONS = ((0, 3), (0, 4))


def _checked_relations(
    lift_count: int,
    relations: tuple[tuple[int, int], ...],
) -> tuple[tuple[int, int], ...]:
    if not 1 <= lift_count <= 6:
        raise ValueError("relation grammar supports one through six lifts")
    normalized = tuple(
        (min(left, right), max(left, right)) for left, right in relations
    )
    if any(
        not (0 <= left < right < lift_count) for left, right in normalized
    ):
        raise ValueError("relation leaves the lift vertex set or is a self-edge")
    if len(normalized) != len(set(normalized)):
        raise ValueError("duplicate relation")
    return normalized


def relation_grammar_fixture(
    name: str,
    lift_count: int,
    *,
    kill_relations: tuple[tuple[int, int], ...] = (),
    slot_relations: tuple[tuple[int, int], ...] = (),
) -> UniformComparison:
    """Build the preregistered exact common KILL/SLOT grammar."""

    checked_kill = _checked_relations(lift_count, kill_relations)
    checked_slot = _checked_relations(lift_count, slot_relations)
    if set(checked_kill) & set(checked_slot):
        raise ValueError("one unordered pair cannot have two relation colors")

    kill_count = len(kill_relations)
    slot_count = len(slot_relations)
    coarse_edges = tuple(
        (0, 0) for _ in range(1 + kill_count + 2 * slot_count)
    )
    fine_edges = tuple(
        (0, 0) for _ in range(lift_count + kill_count + 2 * slot_count)
    )
    coarse_faces: list[tuple[int, int, int]] = []
    fine_faces: list[tuple[int, int, int]] = []
    face_map: list[int] = []

    # KILL(u,v): Z=(z,z,z), F=(e,e,z) and their exact fine lifts.
    for index, (left, right) in enumerate(kill_relations):
        coarse_z = 1 + index
        fine_z = lift_count + index
        coarse_face_start = len(coarse_faces)
        coarse_faces.extend(
            ((coarse_z, coarse_z, coarse_z), (0, 0, coarse_z))
        )
        fine_faces.extend(
            ((fine_z, fine_z, fine_z), (left, right, fine_z))
        )
        face_map.extend((coarse_face_start, coarse_face_start + 1))

    # SLOT(u,v): one coarse (e,a,b), and two fine faces differing only in e.
    coarse_slot_edge_start = 1 + kill_count
    fine_slot_edge_start = lift_count + kill_count
    for index, (left, right) in enumerate(slot_relations):
        coarse_a = coarse_slot_edge_start + 2 * index
        coarse_b = coarse_a + 1
        fine_a = fine_slot_edge_start + 2 * index
        fine_b = fine_a + 1
        coarse_face = len(coarse_faces)
        coarse_faces.append((0, coarse_a, coarse_b))
        fine_faces.extend(
            ((left, fine_a, fine_b), (right, fine_a, fine_b))
        )
        face_map.extend((coarse_face, coarse_face))

    edge_map = (
        tuple(0 for _ in range(lift_count))
        + tuple(1 + index for index in range(kill_count))
        + tuple(
            coarse_slot_edge_start + index for index in range(2 * slot_count)
        )
    )
    coarse = Nerve(1, coarse_edges, tuple(coarse_faces))
    fine = Nerve(1, fine_edges, tuple(fine_faces))
    return UniformComparison(
        name=name,
        morphism=NerveMorphism(
            coarse,
            fine,
            (0,),
            edge_map,
            tuple(face_map),
        ),
        coarse_target_count=4,
        fine_target_count=5,
        factor_pi=(0, 0, 1, 2, 3),
        coarse_chart_supports=(frozenset((0, 1, 2, 3)),),
        fine_chart_supports=(frozenset((0, 1, 2, 3, 4)),),
    )


def round8_relation_fixtures() -> tuple[UniformComparison, ...]:
    return (
        relation_grammar_fixture(
            "R8-L6-KILL",
            6,
            kill_relations=R8_L6_KILL_RELATIONS,
        ),
        relation_grammar_fixture(
            "R8-CL3-SLOT",
            6,
            slot_relations=R8_CL3_SLOT_RELATIONS,
        ),
    )


def round9_figure8_split_support_fixture() -> UniformComparison:
    coarse_edges = tuple((0, 0) for _ in range(7)) + ((1, 1),)
    fine_edges = tuple((0, 0) for _ in range(11)) + ((1, 1),)
    coarse_faces: list[tuple[int, int, int]] = []
    fine_faces: list[tuple[int, int, int]] = []
    for index, (left, right) in enumerate(R9_FIGURE8_KILL_RELATIONS):
        coarse_z = 1 + index
        fine_z = 5 + index
        coarse_faces.extend(
            ((coarse_z, coarse_z, coarse_z), (0, 0, coarse_z))
        )
        fine_faces.extend(
            ((fine_z, fine_z, fine_z), (left, right, fine_z))
        )
    coarse = Nerve(2, coarse_edges, tuple(coarse_faces))
    fine = Nerve(2, fine_edges, tuple(fine_faces))
    return UniformComparison(
        name="R9-FIGURE8-SPLIT-SUPPORT",
        morphism=NerveMorphism(
            coarse,
            fine,
            (0, 1),
            (0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7),
            tuple(range(12)),
        ),
        coarse_target_count=4,
        fine_target_count=5,
        factor_pi=(0, 0, 1, 2, 3),
        coarse_chart_supports=(frozenset((0, 1)), frozenset((2, 3))),
        fine_chart_supports=(
            frozenset((0, 1, 2)),
            frozenset((3, 4)),
        ),
    )


def round9_relation_fixtures() -> tuple[UniformComparison, ...]:
    return (
        relation_grammar_fixture(
            "R9-DIAMOND-MIXED",
            4,
            kill_relations=R9_DIAMOND_KILL_RELATIONS,
            slot_relations=R9_DIAMOND_SLOT_RELATIONS,
        ),
        round9_figure8_split_support_fixture(),
    )


def round10_k23_mixed_overlap_fixture() -> UniformComparison:
    coarse_faces = (
        (1, 1, 1),
        (0, 0, 1),
        (2, 2, 2),
        (0, 0, 2),
        (3, 3, 3),
        (0, 0, 3),
        (0, 4, 5),
        (0, 6, 7),
        (0, 8, 9),
    )
    fine_faces = (
        (5, 5, 5),
        (0, 2, 5),
        (6, 6, 6),
        (0, 3, 6),
        (7, 7, 7),
        (1, 4, 7),
        (0, 8, 9),
        (4, 8, 9),
        (1, 10, 11),
        (2, 10, 11),
        (1, 12, 13),
        (3, 12, 13),
    )
    coarse = Nerve(
        2,
        tuple((0, 0) for _ in range(10)) + ((1, 1),),
        coarse_faces,
    )
    fine = Nerve(
        2,
        tuple((0, 0) for _ in range(14)) + ((1, 1),),
        fine_faces,
    )
    return UniformComparison(
        name="R10-A-K23-MIXED-OVERLAP",
        morphism=NerveMorphism(
            coarse,
            fine,
            (0, 1),
            (0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10),
            (0, 1, 2, 3, 4, 5, 6, 6, 7, 7, 8, 8),
        ),
        coarse_target_count=4,
        fine_target_count=5,
        factor_pi=(0, 0, 1, 2, 3),
        coarse_chart_supports=(frozenset((0, 1, 2)), frozenset((2, 3))),
        fine_chart_supports=(
            frozenset((0, 1, 2, 3)),
            frozenset((3, 4)),
        ),
    )


def round10_k4_star_multichart_fixture() -> UniformComparison:
    coarse_faces = (
        (1, 1, 1),
        (0, 0, 1),
        (2, 2, 2),
        (0, 0, 2),
        (3, 3, 3),
        (0, 0, 3),
        (0, 4, 5),
        (0, 6, 7),
        (0, 8, 9),
        (11, 11, 11),
        (10, 10, 11),
        (10, 12, 13),
        (10, 14, 15),
    )
    fine_faces = (
        (4, 4, 4),
        (0, 1, 4),
        (5, 5, 5),
        (1, 2, 5),
        (6, 6, 6),
        (2, 0, 6),
        (0, 7, 8),
        (3, 7, 8),
        (1, 9, 10),
        (3, 9, 10),
        (2, 11, 12),
        (3, 11, 12),
        (17, 17, 17),
        (13, 14, 17),
        (13, 18, 19),
        (15, 18, 19),
        (13, 20, 21),
        (16, 20, 21),
    )
    coarse = Nerve(
        3,
        tuple((0, 0) for _ in range(10))
        + tuple((1, 1) for _ in range(6))
        + ((2, 2),),
        coarse_faces,
    )
    fine = Nerve(
        3,
        tuple((0, 0) for _ in range(13))
        + tuple((1, 1) for _ in range(9))
        + ((2, 2),),
        fine_faces,
    )
    return UniformComparison(
        name="R10-B-K4-STAR-CHAIN-SUPPORT",
        morphism=NerveMorphism(
            coarse,
            fine,
            (0, 1, 2),
            (
                0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
                10, 10, 10, 10, 11, 12, 13, 14, 15, 16,
            ),
            (0, 1, 2, 3, 4, 5, 6, 6, 7, 7, 8, 8, 9, 10, 11, 11, 12, 12),
        ),
        coarse_target_count=4,
        fine_target_count=5,
        factor_pi=(0, 0, 1, 2, 3),
        coarse_chart_supports=(
            frozenset((0, 1)),
            frozenset((1, 2)),
            frozenset((2, 3)),
        ),
        fine_chart_supports=(
            frozenset((0, 1, 2)),
            frozenset((2, 3)),
            frozenset((3, 4)),
        ),
    )


def round10_relation_fixtures() -> tuple[UniformComparison, ...]:
    return (
        round10_k23_mixed_overlap_fixture(),
        round10_k4_star_multichart_fixture(),
    )


def round11_relation_fixtures() -> tuple[UniformComparison, ...]:
    return (
        relation_grammar_fixture(
            "R11-W5-K5-S5",
            6,
            kill_relations=R11_W5_KILL_RELATIONS,
            slot_relations=R11_W5_SLOT_RELATIONS,
        ),
        relation_grammar_fixture(
            "R11-K33-K3-S6",
            6,
            kill_relations=R11_K33_KILL_RELATIONS,
            slot_relations=R11_K33_SLOT_RELATIONS,
        ),
    )


def round12_octahedral_fixture() -> UniformComparison:
    return relation_grammar_fixture(
        "R12-OCTA-K6-S6",
        6,
        kill_relations=R12_OCTA_KILL_RELATIONS,
        slot_relations=R12_OCTA_SLOT_RELATIONS,
    )


def round12_house_star_partition_fixture() -> UniformComparison:
    coarse = Nerve(
        3,
        tuple((0, 0) for _ in range(10))
        + tuple((1, 1) for _ in range(7))
        + ((2, 2),),
        (
            (1, 1, 1),
            (0, 0, 1),
            (2, 2, 2),
            (0, 0, 2),
            (3, 3, 3),
            (0, 0, 3),
            (0, 4, 5),
            (0, 6, 7),
            (0, 8, 9),
            (11, 11, 11),
            (10, 10, 11),
            (12, 12, 12),
            (10, 10, 12),
            (10, 13, 14),
            (10, 15, 16),
        ),
    )
    fine = Nerve(
        3,
        tuple((0, 0) for _ in range(14))
        + tuple((1, 1) for _ in range(11))
        + ((2, 2),),
        (
            (5, 5, 5),
            (0, 1, 5),
            (6, 6, 6),
            (2, 3, 6),
            (7, 7, 7),
            (1, 4, 7),
            (1, 8, 9),
            (2, 8, 9),
            (0, 10, 11),
            (3, 10, 11),
            (2, 12, 13),
            (4, 12, 13),
            (19, 19, 19),
            (14, 15, 19),
            (20, 20, 20),
            (14, 16, 20),
            (14, 21, 22),
            (17, 21, 22),
            (14, 23, 24),
            (18, 23, 24),
        ),
    )
    return UniformComparison(
        name="R12-HOUSE-STAR-PARTITION",
        morphism=NerveMorphism(
            coarse,
            fine,
            (0, 1, 2),
            (
                0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
                10, 10, 10, 10, 10, 11, 12, 13, 14, 15, 16, 17,
            ),
            (
                0, 1, 2, 3, 4, 5, 6, 6, 7, 7, 8, 8,
                9, 10, 11, 12, 13, 13, 14, 14,
            ),
        ),
        coarse_target_count=4,
        fine_target_count=5,
        factor_pi=(0, 0, 1, 2, 3),
        coarse_chart_supports=(
            frozenset((0, 2)),
            frozenset((1, 3)),
            frozenset((0, 1, 2, 3)),
        ),
        fine_chart_supports=(
            frozenset((0, 1, 3)),
            frozenset((2, 4)),
            frozenset((0, 1, 2, 3, 4)),
        ),
    )


def round12_relation_fixtures() -> tuple[UniformComparison, ...]:
    return (
        round12_octahedral_fixture(),
        round12_house_star_partition_fixture(),
    )


def relation_graph_canonical_code(
    lift_count: int,
    *,
    kill_relations: tuple[tuple[int, int], ...] = (),
    slot_relations: tuple[tuple[int, int], ...] = (),
) -> str:
    """Return the all-vertex-permutation minimum 0/1/2 colored-edge word."""

    kill = _checked_relations(lift_count, kill_relations)
    slot = _checked_relations(lift_count, slot_relations)
    if set(kill) & set(slot):
        raise ValueError("one unordered pair cannot have two relation colors")
    colors = {relation: 1 for relation in kill}
    colors.update({relation: 2 for relation in slot})
    words = (
        tuple(
            colors.get(
                tuple(sorted((ordering[left], ordering[right]))),
                0,
            )
            for left in range(lift_count)
            for right in range(left + 1, lift_count)
        )
        for ordering in permutations(range(lift_count))
    )
    return f"{lift_count}:" + "".join(str(color) for color in min(words))


def _relation_graph_invariant(
    lift_count: int,
    *,
    kill_relations: tuple[tuple[int, int], ...] = (),
    slot_relations: tuple[tuple[int, int], ...] = (),
) -> dict[str, object]:
    kill = _checked_relations(lift_count, kill_relations)
    slot = _checked_relations(lift_count, slot_relations)
    relations = kill + slot
    degrees = [0 for _ in range(lift_count)]
    adjacency = {vertex: set() for vertex in range(lift_count)}
    for left, right in relations:
        degrees[left] += 1
        degrees[right] += 1
        adjacency[left].add(right)
        adjacency[right].add(left)
    components = 0
    remaining = set(range(lift_count))
    while remaining:
        components += 1
        frontier = [min(remaining)]
        reached = set(frontier)
        while frontier:
            current = frontier.pop()
            for neighbour in sorted(adjacency[current] - reached):
                reached.add(neighbour)
                frontier.append(neighbour)
        remaining -= reached
    color_word = (
        f"K^{len(kill)}" if kill and not slot else
        f"S^{len(slot)}" if slot and not kill else
        f"K^{len(kill)}S^{len(slot)}"
    )
    return {
        "n": lift_count,
        "m": len(relations),
        "degrees": sorted(degrees),
        "beta1": len(relations) - lift_count + components,
        "colors": color_word,
    }


def relation_graph_support_code(
    comparison: UniformComparison,
    lift_count: int,
    *,
    kill_relations: tuple[tuple[int, int], ...] = (),
    slot_relations: tuple[tuple[int, int], ...] = (),
) -> str:
    payload = {
        "relation_graph_canonical_code": relation_graph_canonical_code(
            lift_count,
            kill_relations=kill_relations,
            slot_relations=slot_relations,
        ),
        "coarse_chart_count": comparison.morphism.coarse.vertices,
        "fine_chart_count": comparison.morphism.fine.vertices,
        "coarse_chart_supports": [
            sorted(support) for support in comparison.coarse_chart_supports
        ],
        "fine_chart_supports": [
            sorted(support) for support in comparison.fine_chart_supports
        ],
        "factor_pi": list(comparison.factor_pi),
        "vertex_map": list(comparison.morphism.vertex_map),
    }
    rendered = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    return sha256(rendered.encode("ascii")).hexdigest()


@dataclass(frozen=True)
class RelationBlockCodeSpec:
    lift_count: int
    kill_relations: tuple[tuple[int, int], ...]
    slot_relations: tuple[tuple[int, int], ...] = ()


@dataclass(frozen=True)
class ChartCodeSpec:
    coarse_support: frozenset[int]
    fine_support: frozenset[int]
    relation_blocks: tuple[RelationBlockCodeSpec, ...] = ()
    identity_loop_count: int = 0


def colored_graph_support_canonical_code(
    *,
    factor_pi: tuple[int, ...],
    chart_records: tuple[ChartCodeSpec, ...],
    coarse_cell_counts: tuple[int, int, int],
    fine_cell_counts: tuple[int, int, int],
) -> dict[str, str]:
    """Canonicalize lift, chart, and pi-compatible target relabelings."""

    fine_target_count = len(factor_pi)
    coarse_target_count = max(factor_pi, default=-1) + 1
    if not (
        coarse_target_count > 0
        and set(factor_pi) == set(range(coarse_target_count))
        and len(chart_records) == coarse_cell_counts[0] == fine_cell_counts[0]
        and all(record.identity_loop_count >= 0 for record in chart_records)
        and all(
            set(record.coarse_support) <= set(range(coarse_target_count))
            and set(record.fine_support) <= set(range(fine_target_count))
            for record in chart_records
        )
    ):
        raise ValueError("invalid colored graph/support canonicalization input")

    block_codes = tuple(
        tuple(
            sorted(
                relation_graph_canonical_code(
                    block.lift_count,
                    kill_relations=block.kill_relations,
                    slot_relations=block.slot_relations,
                )
                for block in record.relation_blocks
            )
        )
        for record in chart_records
    )
    fiber_profile = sorted(
        sum(mapped == coarse for mapped in factor_pi)
        for coarse in range(coarse_target_count)
    )
    candidates: list[str] = []
    for coarse_permutation in permutations(range(coarse_target_count)):
        for fine_permutation in permutations(range(fine_target_count)):
            if not all(
                coarse_permutation[factor_pi[target]]
                == factor_pi[fine_permutation[target]]
                for target in range(fine_target_count)
            ):
                continue
            transformed_records = sorted(
                [
                    [
                        sorted(
                            coarse_permutation[target]
                            for target in record.coarse_support
                        ),
                        sorted(
                            fine_permutation[target]
                            for target in record.fine_support
                        ),
                        list(block_codes[index]),
                        record.identity_loop_count,
                    ]
                    for index, record in enumerate(chart_records)
                ]
            )
            payload = [
                [coarse_target_count, fine_target_count],
                fiber_profile,
                transformed_records,
                [list(coarse_cell_counts), list(fine_cell_counts)],
            ]
            candidates.append(json.dumps(payload, separators=(",", ":")))
    if not candidates:
        raise AssertionError("no pi-compatible target relabeling")
    compact_json = min(candidates)
    return {
        "compact_json": compact_json,
        "sha256": sha256(compact_json.encode("ascii")).hexdigest(),
    }


def _required_catalog() -> tuple[UniformComparison, ...]:
    return (
        *calibration_fixtures(),
        support_hole_fixture(),
        canonical_firing_fixture(),
        legacy_positive_fixture(),
        *r1_necessity_witnesses().values(),
    )


def _core_population() -> Iterator[UniformComparison]:
    for template_name, morphism in core_incidence_templates():
        for coarse_count, fine_count, factor_pi in canonical_core_factors():
            coarse_options = nonempty_subsets(coarse_count)
            fine_options = nonempty_subsets(fine_count)
            for coarse_supports in product(coarse_options, repeat=morphism.coarse.vertices):
                for fine_supports in product(fine_options, repeat=morphism.fine.vertices):
                    if not all(
                        {factor_pi[target] for target in fine_supports[fine_chart]}
                        <= set(coarse_supports[morphism.vertex_map[fine_chart]])
                        for fine_chart in range(morphism.fine.vertices)
                    ):
                        continue
                    yield UniformComparison(
                        name=f"core:{template_name}:{coarse_count}:{fine_count}:{factor_pi}:{coarse_supports}:{fine_supports}",
                        morphism=morphism,
                        coarse_target_count=coarse_count,
                        fine_target_count=fine_count,
                        factor_pi=factor_pi,
                        coarse_chart_supports=tuple(coarse_supports),
                        fine_chart_supports=tuple(fine_supports),
                    )


def _case_semantic_payload_json(comparison: UniformComparison) -> str:
    semantic_summary = dict(comparison.summary())
    semantic_summary.pop("name")
    return json.dumps(semantic_summary, sort_keys=True, separators=(",", ":"))


def _case_semantic_sha256(comparison: UniformComparison) -> str:
    payload = _case_semantic_payload_json(comparison)
    return sha256(payload.encode("utf-8")).hexdigest()


def _case_id(comparison: UniformComparison) -> str:
    return _case_semantic_sha256(comparison)[:20]


def _case_result(
    comparison: UniformComparison,
    category: str,
    *,
    c5_mode: str = "clique",
) -> dict[str, object]:
    candidate = candidate_evaluation(comparison, c5_mode=c5_mode)
    blocks = comparison.block_analyses()
    uniform = all(analysis.isomorphism for _, analysis in blocks)
    bad_blocks = [
        {"coarse_targets_A": sorted(targets), "h1": asdict(analysis)}
        for targets, analysis in blocks
        if not analysis.isomorphism
    ]
    return {
        "id": _case_id(comparison),
        "name": comparison.name,
        "category": category,
        "uniform": uniform,
        "bad_blocks": bad_blocks,
        "candidate": candidate,
        "sufficiency_break": candidate["all"] and bool(bad_blocks),
        "necessity_break": uniform and not candidate["all"],
    }


def round1_report() -> dict[str, object]:
    cases: list[dict[str, object]] = []
    cases.extend(_case_result(comparison, "core") for comparison in _core_population())
    cases.extend(_case_result(comparison, "required_catalog") for comparison in _required_catalog())
    chain = _case_result(chain3_fixture(), "round1_chain3")
    cases.append(chain)

    if len([case for case in cases if case["category"] == "core"]) != 590:
        raise AssertionError("round1 core population drifted from preregistration")
    expected_chain = {
        "C0*": True,
        "C1*": True,
        "C2*": True,
        "C3*": True,
        "C4*": True,
        "C5*": False,
        "C6*": True,
    }
    chain_analysis = chain3_fixture().block_analyses()[0][1]
    if not (
        chain["uniform"]
        and chain["candidate"]["aggregate"] == expected_chain
        and chain_analysis == H1Analysis(1, 1, 1, True, True, True)
    ):
        raise AssertionError("registered Chain3 calibration mismatch")

    sufficiency = [case for case in cases if case["sufficiency_break"]]
    necessity = [case for case in cases if case["necessity_break"]]
    return {
        "round": "R2-round-1",
        "preregistered_issue_comments": [5230386108, 5230405605],
        "candidate": {
            "semantic_id": CANDIDATE_SEMANTIC_ID,
            "semantic_sha256": CANDIDATE_SEMANTIC_SHA256,
            "spec": CANDIDATE_SPEC,
        },
        "population": {
            "core": 590,
            "required_catalog": len(_required_catalog()),
            "round_fixture": 1,
            "total": len(cases),
            "all_cases_evaluated": True,
        },
        "queries": {
            "sufficiency_break_count": len(sufficiency),
            "necessity_break_count": len(necessity),
            "sufficiency_break_ids": [case["id"] for case in sufficiency],
            "necessity_break_ids": [case["id"] for case in necessity],
        },
        "registered_chain3": chain,
        "counterexamples": {
            "sufficiency": sufficiency,
            "necessity": necessity,
        },
        "coverage_limit": "Exactly the 590 preregistered core cases, 13 required fixtures, and Chain3; arbitrary larger incidence is not covered.",
    }


def round2_report() -> dict[str, object]:
    cases: list[dict[str, object]] = []
    cases.extend(
        _case_result(comparison, "core", c5_mode="component")
        for comparison in _core_population()
    )
    cases.extend(
        _case_result(comparison, "required_catalog", c5_mode="component")
        for comparison in _required_catalog()
    )
    chain = _case_result(chain3_fixture(), "round1_chain3", c5_mode="component")
    unkilled = _case_result(
        unkilled_twin_fixture(),
        "round2_unkilled_twin",
        c5_mode="component",
    )
    cases.extend((chain, unkilled))

    if len(cases) != 605:
        raise AssertionError("round2 population is not the registered strict superset")
    chain_expected = {f"C{index}*": True for index in range(7)}
    unkilled_analysis = unkilled_twin_fixture().block_analyses()[0][1]
    if not (
        chain["uniform"]
        and chain["candidate"]["aggregate"] == chain_expected
        and unkilled["candidate"]["aggregate"] == chain_expected
        and unkilled_analysis == H1Analysis(1, 2, 1, True, False, False)
        and unkilled["sufficiency_break"]
    ):
        raise AssertionError("registered round2 fixture calibration mismatch")

    sufficiency = [case for case in cases if case["sufficiency_break"]]
    necessity = [case for case in cases if case["necessity_break"]]
    return {
        "round": "R2-round-2",
        "preregistered_issue_comment": 5230446212,
        "candidate": {
            "semantic_id": COMPONENT_SEMANTIC_ID,
            "semantic_sha256": COMPONENT_SEMANTIC_SHA256,
            "spec": COMPONENT_SPEC,
        },
        "population": {
            "round1_population": 604,
            "new_fixture": 1,
            "total": len(cases),
            "strict_superset": True,
            "all_cases_evaluated": True,
        },
        "queries": {
            "sufficiency_break_count": len(sufficiency),
            "necessity_break_count": len(necessity),
            "sufficiency_break_ids": [case["id"] for case in sufficiency],
            "necessity_break_ids": [case["id"] for case in necessity],
        },
        "registered_chain3": chain,
        "registered_unkilled_twin": unkilled,
        "counterexamples": {
            "sufficiency": sufficiency,
            "necessity": necessity,
        },
        "coverage_limit": "Exactly the round1 population plus UnkilledTwin; arbitrary larger incidence is not covered.",
    }


def round3_report() -> dict[str, object]:
    cases: list[dict[str, object]] = []
    cases.extend(
        _case_result(comparison, "core", c5_mode="certified")
        for comparison in _core_population()
    )
    cases.extend(
        _case_result(comparison, "required_catalog", c5_mode="certified")
        for comparison in _required_catalog()
    )
    chain = _case_result(chain3_fixture(), "round1_chain3", c5_mode="certified")
    unkilled = _case_result(
        unkilled_twin_fixture(),
        "round2_unkilled_twin",
        c5_mode="certified",
    )
    cases.extend((chain, unkilled))

    expected_true = {f"C{index}*": True for index in range(7)}
    if not (
        len(cases) == 605
        and chain["uniform"]
        and chain["candidate"]["aggregate"] == expected_true
        and not unkilled["uniform"]
        and not unkilled["candidate"]["aggregate"]["C5*"]
        and not unkilled["sufficiency_break"]
    ):
        raise AssertionError("registered CERTIFIED-v3 calibration mismatch")

    sufficiency = [case for case in cases if case["sufficiency_break"]]
    necessity = [case for case in cases if case["necessity_break"]]
    return {
        "round": "R2-round-3",
        "preregistered_issue_comment": 5230453578,
        "candidate": {
            "semantic_id": CERTIFIED_SEMANTIC_ID,
            "semantic_sha256": CERTIFIED_SEMANTIC_SHA256,
            "spec": CERTIFIED_SPEC,
        },
        "population": {
            "round2_population": 605,
            "total": len(cases),
            "all_cases_evaluated": True,
        },
        "queries": {
            "sufficiency_break_count": len(sufficiency),
            "necessity_break_count": len(necessity),
            "sufficiency_break_ids": [case["id"] for case in sufficiency],
            "necessity_break_ids": [case["id"] for case in necessity],
        },
        "registered_chain3": chain,
        "registered_unkilled_twin": unkilled,
        "counterexamples": {
            "sufficiency": sufficiency,
            "necessity": necessity,
        },
        "coverage_limit": "Exactly the round2 population under CERTIFIED-v3; arbitrary larger incidence is not covered.",
    }


def round4_report() -> dict[str, object]:
    baseline: list[dict[str, object]] = []
    baseline.extend(
        _case_result(comparison, "core", c5_mode="certified")
        for comparison in _core_population()
    )
    baseline.extend(
        _case_result(comparison, "required_catalog", c5_mode="certified")
        for comparison in _required_catalog()
    )
    baseline.extend(
        (
            _case_result(chain3_fixture(), "round1_chain3", c5_mode="certified"),
            _case_result(
                unkilled_twin_fixture(),
                "round2_unkilled_twin",
                c5_mode="certified",
            ),
        )
    )
    expansion = [
        _case_result(comparison, "round4_closed_2d", c5_mode="certified")
        for comparison in closed_2d_expansion_fixtures()
    ]
    cases = baseline + expansion
    baseline_ids = {case["id"] for case in baseline}
    new_ids = [case["id"] for case in expansion if case["id"] not in baseline_ids]
    if not (
        len(baseline) == 605
        and len(cases) == 608
        and len(new_ids) == 3
        and all(case["candidate"]["all"] and case["uniform"] for case in expansion)
    ):
        raise AssertionError("registered CLOSED-2D-CORE expansion calibration mismatch")

    sufficiency = [case for case in cases if case["sufficiency_break"]]
    necessity = [case for case in cases if case["necessity_break"]]
    new_counterexamples = [
        case
        for case in expansion
        if case["sufficiency_break"] or case["necessity_break"]
    ]
    return {
        "round": "R2-round-4",
        "preregistered_issue_comment": 5230462990,
        "candidate": {
            "semantic_id": CERTIFIED_SEMANTIC_ID,
            "semantic_sha256": CERTIFIED_SEMANTIC_SHA256,
            "spec": CERTIFIED_SPEC,
        },
        "population": {
            "baseline": 605,
            "new_incidence_cases": 3,
            "total": len(cases),
            "strict_superset": len(new_ids) == 3,
            "new_ids": new_ids,
            "all_cases_evaluated": True,
        },
        "queries": {
            "sufficiency_break_count": len(sufficiency),
            "necessity_break_count": len(necessity),
            "new_counterexample_count": len(new_counterexamples),
            "new_counterexample_ids": [case["id"] for case in new_counterexamples],
        },
        "expansion_cases": expansion,
        "progress_audit": {
            "new_verdicts": [],
            "new_nonisomorphic_counterexamples": [
                case["id"] for case in new_counterexamples
            ],
            "candidate_semantic_change": False,
            "calibration_fixes": [],
        },
        "blocker_id": "PB-R2-NONFREE-GLOBAL-FACE-CHAIN",
        "coverage_limit": "Three fixed-label closed two-dimensional identity cores; general face multiplicities and nonidentity refinements are not covered.",
    }


def round5_report() -> dict[str, object]:
    # The prior result is invoked as the exact 608-case baseline.  Its compact
    # counterexample query is retained; the 1,296 new cases are recorded in full.
    prior = round4_report()
    expansion = [
        _case_result(comparison, "round5_mixed_support", c5_mode="certified")
        for comparison in mixed_support_square_variants()
    ]
    baseline_ids = {
        *prior["population"]["new_ids"],
        _case_id(chain3_fixture()),
        _case_id(unkilled_twin_fixture()),
        *(_case_id(comparison) for comparison in _required_catalog()),
        *(_case_id(comparison) for comparison in _core_population()),
    }
    new_ids = [case["id"] for case in expansion if case["id"] not in baseline_ids]
    new_counterexamples = [
        case
        for case in expansion
        if case["sufficiency_break"] or case["necessity_break"]
    ]
    if not (
        len(expansion) == 1296
        and len(new_ids) == 1296
        and len(set(new_ids)) == 1296
        and all(case["uniform"] and case["candidate"]["all"] for case in expansion)
    ):
        raise AssertionError("registered MIXED-SUPPORT-A-UNION expansion calibration mismatch")

    return {
        "round": "R2-round-5",
        "preregistered_issue_comment": 5230467922,
        "candidate": {
            "semantic_id": CERTIFIED_SEMANTIC_ID,
            "semantic_sha256": CERTIFIED_SEMANTIC_SHA256,
            "spec": CERTIFIED_SPEC,
        },
        "population": {
            "baseline": 608,
            "raw_support_assignments": 1296,
            "valid_support_assignments": 1296,
            "new_fixed_label_ids": len(new_ids),
            "total": 608 + len(expansion),
            "strict_superset": len(new_ids) == 1296,
            "all_cases_evaluated": True,
            "nonempty_A_per_new_case": 15,
            "new_A_block_queries": 1296 * 15,
        },
        "queries": {
            "baseline_sufficiency_break_count": prior["queries"]["sufficiency_break_count"],
            "baseline_necessity_break_count": prior["queries"]["necessity_break_count"],
            "new_sufficiency_break_count": sum(case["sufficiency_break"] for case in expansion),
            "new_necessity_break_count": sum(case["necessity_break"] for case in expansion),
            "new_counterexample_count": len(new_counterexamples),
            "new_counterexample_ids": [case["id"] for case in new_counterexamples],
        },
        "new_case_ids": new_ids,
        "support_histogram": {
            "coarse_mask_assignments": 1296,
            "fine_support_rule": "exact pi-preimage",
            "target_sizes": {"coarse": 4, "fine": 5},
        },
        "progress_audit": {
            "new_verdicts": [],
            "new_nonisomorphic_counterexamples": [
                case["id"] for case in new_counterexamples
            ],
            "candidate_semantic_change": False,
            "calibration_fixes": [],
        },
        "blocker_id": "PB-R2-NONFREE-GLOBAL-FACE-CHAIN",
        "coverage_limit": "One fixed-label identity square with six coarse chart masks and exact pi-preimages; arbitrary support masks and nonidentity incidence are not covered.",
    }


def _prior_semantic_ids_through_round5() -> set[str]:
    return {
        *(_case_id(comparison) for comparison in _core_population()),
        *(_case_id(comparison) for comparison in _required_catalog()),
        _case_id(chain3_fixture()),
        _case_id(unkilled_twin_fixture()),
        *(_case_id(comparison) for comparison in closed_2d_expansion_fixtures()),
        *(_case_id(comparison) for comparison in mixed_support_square_variants()),
    }


def round6_report() -> dict[str, object]:
    prior = round5_report()
    prior_ids = _prior_semantic_ids_through_round5()
    expansion = [
        _case_result(comparison, "round6_nonfree_linear_chain", c5_mode="certified")
        for comparison in round6_face_chains()
    ]
    new_ids = [case["id"] for case in expansion if case["id"] not in prior_ids]
    expected = H1Analysis(1, 1, 1, True, True, True)
    new_counterexamples = [
        case
        for case in expansion
        if case["sufficiency_break"] or case["necessity_break"]
    ]
    if not (
        prior["population"]["total"] == 1904
        and len(new_ids) == len(set(new_ids)) == 2
        and all(case["uniform"] and case["candidate"]["all"] for case in expansion)
        and all(
            comparison.block_analyses()[0][1] == expected
            for comparison in round6_face_chains()
        )
        and all(
            not case["candidate"]["whole"]["coarse_reduction"]["removed_free_pairs"]
            and not case["candidate"]["whole"]["fine_reduction"]["removed_free_pairs"]
            for case in expansion
        )
    ):
        raise AssertionError("registered NONFREE-LINEAR-FACE-CHAIN calibration mismatch")

    return {
        "round": "R2-round-6",
        "preregistered_issue_comment": 5230507176,
        "candidate": {
            "semantic_id": CERTIFIED_SEMANTIC_ID,
            "semantic_sha256": CERTIFIED_SEMANTIC_SHA256,
            "spec": CERTIFIED_SPEC,
        },
        "population": {
            "prior_raw_cases_recomputed": 1904,
            "prior_semantic_unique_ids": len(prior_ids),
            "new_nonidentity_face_chains": 2,
            "new_semantic_ids": new_ids,
            "strict_superset": len(new_ids) == 2,
            "total_raw_cases": 1906,
            "all_cases_evaluated": True,
        },
        "queries": {
            "prior_new_counterexample_count": prior["queries"]["new_counterexample_count"],
            "new_sufficiency_break_count": sum(case["sufficiency_break"] for case in expansion),
            "new_necessity_break_count": sum(case["necessity_break"] for case in expansion),
            "new_counterexample_count": len(new_counterexamples),
            "new_counterexample_ids": [case["id"] for case in new_counterexamples],
        },
        "expansion_cases": expansion,
        "progress_audit": {
            "new_verdicts": [],
            "new_nonisomorphic_counterexamples": [
                case["id"] for case in new_counterexamples
            ],
            "candidate_semantic_change": False,
            "calibration_fixes": [],
        },
        "blocker_id": "PB-R2-NONFREE-GLOBAL-FACE-CHAIN",
        "same_blocker_evidence": {
            "nonidentity": True,
            "retained_face_chain_lengths": [3, 4],
            "free_pair_count": 0,
            "remaining_gap": "No general proof for arbitrary length or branching of retained face chains.",
        },
        "coverage_limit": "Two linear nonfree face chains of lift counts four and five; branching and arbitrary length are not covered.",
    }


def round7_report() -> dict[str, object]:
    prior = round6_report()
    prior_ids = _prior_semantic_ids_through_round5() | {
        _case_id(comparison) for comparison in round6_face_chains()
    }
    expansion = [
        _case_result(
            comparison,
            "round7_nonfree_branching_face_chain",
            c5_mode="certified",
        )
        for comparison in round7_face_chain_graphs()
    ]
    new_ids = [case["id"] for case in expansion if case["id"] not in prior_ids]
    expected = H1Analysis(1, 1, 1, True, True, True)
    new_counterexamples = [
        case
        for case in expansion
        if case["sufficiency_break"] or case["necessity_break"]
    ]
    if not (
        prior["population"]["total_raw_cases"] == 1906
        and len(new_ids) == len(set(new_ids)) == 2
        and all(case["uniform"] and case["candidate"]["all"] for case in expansion)
        and all(
            all(analysis == expected for _, analysis in comparison.block_analyses())
            for comparison in round7_face_chain_graphs()
        )
        and all(
            not case["candidate"]["whole"]["coarse_reduction"]["removed_free_pairs"]
            and not case["candidate"]["whole"]["fine_reduction"]["removed_free_pairs"]
            for case in expansion
        )
    ):
        raise AssertionError("registered NONFREE-BRANCHING-FACE-CHAIN calibration mismatch")

    return {
        "round": "R2-round-7",
        "preregistered_issue_comment": 5230514887,
        "candidate": {
            "semantic_id": CERTIFIED_SEMANTIC_ID,
            "semantic_sha256": CERTIFIED_SEMANTIC_SHA256,
            "spec": CERTIFIED_SPEC,
        },
        "population": {
            "prior_raw_cases_recomputed": 1906,
            "prior_semantic_unique_ids": len(prior_ids),
            "new_nonidentity_face_chain_graphs": 2,
            "new_semantic_ids": new_ids,
            "strict_superset": len(new_ids) == 2,
            "total_raw_cases": 1908,
            "all_cases_evaluated": True,
            "nonempty_A_per_new_case": 15,
        },
        "queries": {
            "prior_new_counterexample_count": prior["queries"]["new_counterexample_count"],
            "new_sufficiency_break_count": sum(case["sufficiency_break"] for case in expansion),
            "new_necessity_break_count": sum(case["necessity_break"] for case in expansion),
            "new_counterexample_count": len(new_counterexamples),
            "new_counterexample_ids": [case["id"] for case in new_counterexamples],
        },
        "expansion_cases": expansion,
        "progress_audit": {
            "new_verdicts": [],
            "new_nonisomorphic_counterexamples": [
                case["id"] for case in new_counterexamples
            ],
            "candidate_semantic_change": False,
            "calibration_fixes": [],
        },
        "blocker_id": "PB-R2-NONFREE-GLOBAL-FACE-CHAIN",
        "same_blocker_evidence": {
            "nonidentity": True,
            "relation_graphs": ["branching-tree", "cycle"],
            "free_pair_count": 0,
            "remaining_gap": "No general proof for arbitrary retained face-chain graphs.",
        },
        "coverage_limit": "One branching tree and one cycle relation graph at full Target support; arbitrary graph size and support distribution are not covered.",
    }


def _all_comparisons_through_round7() -> Iterator[UniformComparison]:
    yield from _core_population()
    yield from _required_catalog()
    yield chain3_fixture()
    yield unkilled_twin_fixture()
    yield from closed_2d_expansion_fixtures()
    yield from mixed_support_square_variants()
    yield from round6_face_chains()
    yield from round7_face_chain_graphs()


def _registered_relation_graph_codes() -> dict[str, str]:
    rows = (
        (
            "R6-L4-KILL",
            4,
            ((0, 1), (1, 2), (2, 3)),
            (),
        ),
        (
            "R6-L5-KILL",
            5,
            ((0, 1), (1, 2), (2, 3), (3, 4)),
            (),
        ),
        (
            "R7-B0-KILL",
            5,
            ((0, 1), (1, 2), (1, 3), (3, 4)),
            (),
        ),
        (
            "R7-B1-KILL",
            4,
            ((0, 1), (1, 2), (2, 3), (3, 0)),
            (),
        ),
        (
            "R8-L6-KILL",
            6,
            R8_L6_KILL_RELATIONS,
            (),
        ),
        (
            "R8-CL3-SLOT",
            6,
            (),
            R8_CL3_SLOT_RELATIONS,
        ),
    )
    return {
        name: relation_graph_canonical_code(
            lift_count,
            kill_relations=kill,
            slot_relations=slot,
        )
        for name, lift_count, kill, slot in rows
    }


def _all_comparisons_through_round8() -> Iterator[UniformComparison]:
    yield from _all_comparisons_through_round7()
    yield from round8_relation_fixtures()


def _all_comparisons_through_round9() -> Iterator[UniformComparison]:
    yield from _all_comparisons_through_round8()
    yield from round9_relation_fixtures()


def _all_comparisons_through_round10() -> Iterator[UniformComparison]:
    yield from _all_comparisons_through_round9()
    yield from round10_relation_fixtures()


def _all_comparisons_through_round11() -> Iterator[UniformComparison]:
    yield from _all_comparisons_through_round10()
    yield from round11_relation_fixtures()


def _registered_relation_graph_support_codes_through_round9(
) -> dict[str, dict[str, str]]:
    round6 = round6_face_chains()
    round7 = round7_face_chain_graphs()
    round8 = round8_relation_fixtures()
    round9 = round9_relation_fixtures()
    rows = (
        (
            "R6-L4-KILL",
            round6[0],
            4,
            ((0, 1), (1, 2), (2, 3)),
            (),
        ),
        (
            "R6-L5-KILL",
            round6[1],
            5,
            ((0, 1), (1, 2), (2, 3), (3, 4)),
            (),
        ),
        (
            "R7-B0-KILL",
            round7[0],
            5,
            ((0, 1), (1, 2), (1, 3), (3, 4)),
            (),
        ),
        (
            "R7-B1-KILL",
            round7[1],
            4,
            ((0, 1), (1, 2), (2, 3), (3, 0)),
            (),
        ),
        (
            "R8-L6-KILL",
            round8[0],
            6,
            R8_L6_KILL_RELATIONS,
            (),
        ),
        (
            "R8-CL3-SLOT",
            round8[1],
            6,
            (),
            R8_CL3_SLOT_RELATIONS,
        ),
        (
            "R9-DIAMOND-MIXED",
            round9[0],
            4,
            R9_DIAMOND_KILL_RELATIONS,
            R9_DIAMOND_SLOT_RELATIONS,
        ),
        (
            "R9-FIGURE8-SPLIT-SUPPORT",
            round9[1],
            5,
            R9_FIGURE8_KILL_RELATIONS,
            (),
        ),
    )
    return {
        name: {
            "relation_graph_canonical_code": relation_graph_canonical_code(
                lift_count,
                kill_relations=kill,
                slot_relations=slot,
            ),
            "relation_graph_support_code": relation_graph_support_code(
                comparison,
                lift_count,
                kill_relations=kill,
                slot_relations=slot,
            ),
        }
        for name, comparison, lift_count, kill, slot in rows
    }


def _comparison_cell_counts(
    comparison: UniformComparison,
) -> tuple[tuple[int, int, int], tuple[int, int, int]]:
    return (
        (
            comparison.morphism.coarse.vertices,
            len(comparison.morphism.coarse.edges),
            len(comparison.morphism.coarse.faces),
        ),
        (
            comparison.morphism.fine.vertices,
            len(comparison.morphism.fine.edges),
            len(comparison.morphism.fine.faces),
        ),
    )


def _registered_colored_graph_support_codes_through_round10(
) -> dict[str, dict[str, str]]:
    round6 = round6_face_chains()
    round7 = round7_face_chain_graphs()
    round8 = round8_relation_fixtures()
    round9 = round9_relation_fixtures()
    round10 = round10_relation_fixtures()
    rows = (
        (
            "R6-L4-KILL",
            round6[0],
            (
                ChartCodeSpec(
                    frozenset((0,)),
                    frozenset((0,)),
                    (RelationBlockCodeSpec(4, ((0, 1), (1, 2), (2, 3))),),
                ),
            ),
        ),
        (
            "R6-L5-KILL",
            round6[1],
            (
                ChartCodeSpec(
                    frozenset((0,)),
                    frozenset((0,)),
                    (
                        RelationBlockCodeSpec(
                            5,
                            ((0, 1), (1, 2), (2, 3), (3, 4)),
                        ),
                    ),
                ),
            ),
        ),
        (
            "R7-B0-KILL",
            round7[0],
            (
                ChartCodeSpec(
                    frozenset((0, 1, 2, 3)),
                    frozenset((0, 1, 2, 3, 4)),
                    (
                        RelationBlockCodeSpec(
                            5,
                            ((0, 1), (1, 2), (1, 3), (3, 4)),
                        ),
                    ),
                ),
            ),
        ),
        (
            "R7-B1-KILL",
            round7[1],
            (
                ChartCodeSpec(
                    frozenset((0, 1, 2, 3)),
                    frozenset((0, 1, 2, 3, 4)),
                    (
                        RelationBlockCodeSpec(
                            4,
                            ((0, 1), (1, 2), (2, 3), (3, 0)),
                        ),
                    ),
                ),
            ),
        ),
        (
            "R8-L6-KILL",
            round8[0],
            (
                ChartCodeSpec(
                    frozenset((0, 1, 2, 3)),
                    frozenset((0, 1, 2, 3, 4)),
                    (RelationBlockCodeSpec(6, R8_L6_KILL_RELATIONS),),
                ),
            ),
        ),
        (
            "R8-CL3-SLOT",
            round8[1],
            (
                ChartCodeSpec(
                    frozenset((0, 1, 2, 3)),
                    frozenset((0, 1, 2, 3, 4)),
                    (RelationBlockCodeSpec(6, (), R8_CL3_SLOT_RELATIONS),),
                ),
            ),
        ),
        (
            "R9-DIAMOND-MIXED",
            round9[0],
            (
                ChartCodeSpec(
                    frozenset((0, 1, 2, 3)),
                    frozenset((0, 1, 2, 3, 4)),
                    (
                        RelationBlockCodeSpec(
                            4,
                            R9_DIAMOND_KILL_RELATIONS,
                            R9_DIAMOND_SLOT_RELATIONS,
                        ),
                    ),
                ),
            ),
        ),
        (
            "R9-FIGURE8-SPLIT-SUPPORT",
            round9[1],
            (
                ChartCodeSpec(
                    frozenset((0, 1)),
                    frozenset((0, 1, 2)),
                    (RelationBlockCodeSpec(5, R9_FIGURE8_KILL_RELATIONS),),
                ),
                ChartCodeSpec(
                    frozenset((2, 3)),
                    frozenset((3, 4)),
                    identity_loop_count=1,
                ),
            ),
        ),
        (
            "R10-A-K23-MIXED-OVERLAP",
            round10[0],
            (
                ChartCodeSpec(
                    frozenset((0, 1, 2)),
                    frozenset((0, 1, 2, 3)),
                    (
                        RelationBlockCodeSpec(
                            5,
                            R10_A_KILL_RELATIONS,
                            R10_A_SLOT_RELATIONS,
                        ),
                    ),
                ),
                ChartCodeSpec(
                    frozenset((2, 3)),
                    frozenset((3, 4)),
                    identity_loop_count=1,
                ),
            ),
        ),
        (
            "R10-B-K4-STAR-CHAIN-SUPPORT",
            round10[1],
            (
                ChartCodeSpec(
                    frozenset((0, 1)),
                    frozenset((0, 1, 2)),
                    (
                        RelationBlockCodeSpec(
                            4,
                            R10_B_K4_KILL_RELATIONS,
                            R10_B_K4_SLOT_RELATIONS,
                        ),
                    ),
                ),
                ChartCodeSpec(
                    frozenset((1, 2)),
                    frozenset((2, 3)),
                    (
                        RelationBlockCodeSpec(
                            4,
                            R10_B_STAR_KILL_RELATIONS,
                            R10_B_STAR_SLOT_RELATIONS,
                        ),
                    ),
                ),
                ChartCodeSpec(
                    frozenset((2, 3)),
                    frozenset((3, 4)),
                    identity_loop_count=1,
                ),
            ),
        ),
    )
    result: dict[str, dict[str, str]] = {}
    for name, comparison, charts in rows:
        coarse_counts, fine_counts = _comparison_cell_counts(comparison)
        result[name] = colored_graph_support_canonical_code(
            factor_pi=comparison.factor_pi,
            chart_records=charts,
            coarse_cell_counts=coarse_counts,
            fine_cell_counts=fine_counts,
        )
    return result


def _registered_colored_graph_support_codes_through_round11(
) -> dict[str, dict[str, str]]:
    result = _registered_colored_graph_support_codes_through_round10()
    wheel, bipartite = round11_relation_fixtures()
    rows = (
        (
            wheel,
            RelationBlockCodeSpec(
                6,
                R11_W5_KILL_RELATIONS,
                R11_W5_SLOT_RELATIONS,
            ),
        ),
        (
            bipartite,
            RelationBlockCodeSpec(
                6,
                R11_K33_KILL_RELATIONS,
                R11_K33_SLOT_RELATIONS,
            ),
        ),
    )
    for comparison, relation_block in rows:
        coarse_counts, fine_counts = _comparison_cell_counts(comparison)
        result[comparison.name] = colored_graph_support_canonical_code(
            factor_pi=comparison.factor_pi,
            chart_records=(
                ChartCodeSpec(
                    frozenset((0, 1, 2, 3)),
                    frozenset((0, 1, 2, 3, 4)),
                    (relation_block,),
                ),
            ),
            coarse_cell_counts=coarse_counts,
            fine_cell_counts=fine_counts,
        )
    return result


def _registered_colored_graph_support_codes_through_round12(
) -> dict[str, dict[str, str]]:
    result = _registered_colored_graph_support_codes_through_round11()
    octahedral, partitioned = round12_relation_fixtures()
    rows = (
        (
            octahedral,
            (
                ChartCodeSpec(
                    frozenset((0, 1, 2, 3)),
                    frozenset((0, 1, 2, 3, 4)),
                    (
                        RelationBlockCodeSpec(
                            6,
                            R12_OCTA_KILL_RELATIONS,
                            R12_OCTA_SLOT_RELATIONS,
                        ),
                    ),
                ),
            ),
        ),
        (
            partitioned,
            (
                ChartCodeSpec(
                    frozenset((0, 2)),
                    frozenset((0, 1, 3)),
                    (
                        RelationBlockCodeSpec(
                            5,
                            R12_HOUSE_KILL_RELATIONS,
                            R12_HOUSE_SLOT_RELATIONS,
                        ),
                    ),
                ),
                ChartCodeSpec(
                    frozenset((1, 3)),
                    frozenset((2, 4)),
                    (
                        RelationBlockCodeSpec(
                            5,
                            R12_STAR_KILL_RELATIONS,
                            R12_STAR_SLOT_RELATIONS,
                        ),
                    ),
                ),
                ChartCodeSpec(
                    frozenset((0, 1, 2, 3)),
                    frozenset((0, 1, 2, 3, 4)),
                    identity_loop_count=1,
                ),
            ),
        ),
    )
    for comparison, chart_records in rows:
        coarse_counts, fine_counts = _comparison_cell_counts(comparison)
        result[comparison.name] = colored_graph_support_canonical_code(
            factor_pi=comparison.factor_pi,
            chart_records=chart_records,
            coarse_cell_counts=coarse_counts,
            fine_cell_counts=fine_counts,
        )
    return result


def round8_report() -> dict[str, object]:
    """Run the preregistered longer-linear/circular-ladder strict expansion."""

    if not (
        CERTIFIED_SEMANTIC_ID == "R2-CSTAR-CERTIFIED-v3"
        and CERTIFIED_SEMANTIC_SHA256
        == "cbb02677a055c69ecf0bb50a5de884fb55bbd4b4b59b75d256815eae69ec4daa"
    ):
        raise AssertionError("Round8 candidate semantic payload drifted")

    # Re-run and byte-canonically hash every registered payload before admitting
    # either prior or new Round8 queries.
    prior_reports = (
        round1_report(),
        round2_report(),
        round3_report(),
        round4_report(),
        round5_report(),
        round6_report(),
        round7_report(),
    )
    actual_round_payload_sha256 = tuple(
        _canonical_report_sha256(report) for report in prior_reports
    )
    _assert_registered_round_payload_hashes(actual_round_payload_sha256)
    prior_round = prior_reports[-1]
    prior_comparisons = tuple(_all_comparisons_through_round7())
    prior_full_ids = tuple(
        _case_semantic_sha256(comparison) for comparison in prior_comparisons
    )
    prior_short_ids = tuple(identifier[:20] for identifier in prior_full_ids)
    if not (
        prior_round["population"]["total_raw_cases"] == 1908
        and len(prior_comparisons) == 1908
        and len(set(prior_full_ids)) == 1908
        and len(set(prior_short_ids)) == 1908
    ):
        raise AssertionError("Round8 prior 1908-case baseline is invalid")

    fixtures = round8_relation_fixtures()
    expansion = []
    for comparison in fixtures:
        case = _case_result(
            comparison,
            "round8_relation_grammar",
            c5_mode="certified",
        )
        case["semantic_sha256"] = _case_semantic_sha256(comparison)
        expansion.append(case)
    expected_relations = (
        tuple(sorted(_checked_relations(6, R8_L6_KILL_RELATIONS))),
        tuple(sorted(_checked_relations(6, R8_CL3_SLOT_RELATIONS))),
    )
    expected_cells = ((1, 6, 10, 1, 11, 10), (1, 19, 9, 1, 24, 18))
    expected_h1 = (
        H1Analysis(1, 1, 1, True, True, True),
        H1Analysis(10, 10, 10, True, True, True),
    )
    expected_invariants = (
        {
            "n": 6,
            "m": 5,
            "degrees": [1, 1, 2, 2, 2, 2],
            "beta1": 0,
            "colors": "K^5",
        },
        {
            "n": 6,
            "m": 9,
            "degrees": [3, 3, 3, 3, 3, 3],
            "beta1": 4,
            "colors": "S^9",
        },
    )
    actual_invariants = (
        _relation_graph_invariant(
            6,
            kill_relations=R8_L6_KILL_RELATIONS,
        ),
        _relation_graph_invariant(
            6,
            slot_relations=R8_CL3_SLOT_RELATIONS,
        ),
    )

    for comparison, case, cells, analysis, relations in zip(
        fixtures,
        expansion,
        expected_cells,
        expected_h1,
        expected_relations,
    ):
        coarse = comparison.morphism.coarse
        fine = comparison.morphism.fine
        actual_cells = (
            coarse.vertices,
            len(coarse.edges),
            len(coarse.faces),
            fine.vertices,
            len(fine.edges),
            len(fine.faces),
        )
        direct_edges = tuple(
            tuple(edge)
            for edge in case["candidate"]["whole"]["direct_lifttwin"]["0"][
                "direct_edges"
            ]
        )
        block_analyses = comparison.block_analyses()
        all_reductions = (
            case["candidate"]["whole"],
            *case["candidate"]["per_subset"],
        )
        if not (
            actual_cells == cells
            and sum(mapped == 0 for mapped in comparison.morphism.edge_map) == 6
            and len(block_analyses) == 15
            and all(item == analysis for _, item in block_analyses)
            and case["uniform"]
            and case["candidate"]["all"]
            and direct_edges == relations
            and all(
                not reduction["coarse_reduction"]["removed_free_pairs"]
                and not reduction["fine_reduction"]["removed_free_pairs"]
                for reduction in all_reductions
            )
        ):
            raise AssertionError(
                f"Round8 fixture/modeling calibration failed: {comparison.name}"
            )
    if actual_invariants != expected_invariants:
        raise AssertionError("Round8 colored relation-graph invariant mismatch")

    graph_codes = _registered_relation_graph_codes()
    if len(set(graph_codes.values())) != len(graph_codes):
        raise AssertionError("Round6/7/8 canonical colored-graph code collision")

    new_full_ids = tuple(case["semantic_sha256"] for case in expansion)
    new_short_ids = tuple(case["id"] for case in expansion)
    all_full_ids = prior_full_ids + new_full_ids
    all_short_ids = prior_short_ids + new_short_ids
    full_collision_count = len(all_full_ids) - len(set(all_full_ids))
    truncated_collision_count = len(all_short_ids) - len(set(all_short_ids))
    if not (
        all(full.startswith(short) for full, short in zip(new_full_ids, new_short_ids))
        and not (set(new_full_ids) & set(prior_full_ids))
        and not (set(new_short_ids) & set(prior_short_ids))
        and len(set(new_full_ids)) == len(set(new_short_ids)) == 2
        and len(all_full_ids) == len(all_short_ids) == 1910
        and full_collision_count == truncated_collision_count == 0
    ):
        raise AssertionError("Round8 semantic payload strict-expansion mismatch")

    prior_counterexamples: list[dict[str, str]] = []
    for comparison in prior_comparisons:
        result = _case_result(comparison, "round0_through_round7", c5_mode="certified")
        if result["sufficiency_break"] or result["necessity_break"]:
            prior_counterexamples.append(
                {
                    "id": result["id"],
                    "semantic_sha256": _case_semantic_sha256(comparison),
                    "query": (
                        "sufficiency_break"
                        if result["sufficiency_break"]
                        else "necessity_break"
                    ),
                }
            )
    if prior_counterexamples:
        raise AssertionError("Round8 prior 1908-case query baseline is invalid")
    new_counterexamples = [
        case
        for case in expansion
        if case["sufficiency_break"] or case["necessity_break"]
    ]
    new_verdicts = sorted(
        {
            "CSTAR-not-sufficient"
            for case in new_counterexamples
            if case["sufficiency_break"]
        }
        | {
            "CSTAR-not-necessary"
            for case in new_counterexamples
            if case["necessity_break"]
        }
    )
    new_canonical_counterexamples = [
        case["semantic_sha256"] for case in new_counterexamples
    ]
    candidate_semantic_change = False
    additional_calibration_fixes: list[str] = []
    progress = bool(
        new_verdicts
        or new_canonical_counterexamples
        or candidate_semantic_change
        or additional_calibration_fixes
    )

    return {
        "round": "R2-round-8",
        "preregistered_issue_comment": 5230713854,
        "calibration_reset_comment": 5230709695,
        "valid": False,
        "invalid_reason": (
            "Round8 query ran before final R0(e) Issue synchronization and "
            "coordinator release"
        ),
        "diagnostic_zero_result": not progress,
        "baseline_payload_sha256": {
            f"round{index}": payload_hash
            for index, payload_hash in enumerate(
                actual_round_payload_sha256,
                start=1,
            )
        },
        "candidate": {
            "semantic_id": CERTIFIED_SEMANTIC_ID,
            "semantic_sha256": CERTIFIED_SEMANTIC_SHA256,
            "spec": CERTIFIED_SPEC,
        },
        "population": {
            "prior_raw_cases_recomputed": len(prior_comparisons),
            "prior_full_semantic_payload_ids": len(set(prior_full_ids)),
            "prior_truncated_semantic_payload_ids": len(set(prior_short_ids)),
            "new_relation_grammar_cases": 2,
            "new_full_semantic_payload_ids": list(new_full_ids),
            "new_truncated_semantic_payload_ids": list(new_short_ids),
            "full_sha256_collision_count": full_collision_count,
            "truncated_20hex_collision_count": truncated_collision_count,
            "strict_superset": True,
            "total_raw_cases": 1910,
            "new_A_block_queries": sum(
                len(comparison.block_analyses()) for comparison in fixtures
            ),
            "all_cases_evaluated": True,
        },
        "canonical_colored_relation_graph_codes": graph_codes,
        "relation_graph_invariants": {
            comparison.name: invariant
            for comparison, invariant in zip(fixtures, actual_invariants)
        },
        "queries": {
            "prior_sufficiency_or_necessity_break_count": len(
                prior_counterexamples
            ),
            "prior_counterexamples": prior_counterexamples,
            "new_sufficiency_break_count": sum(
                case["sufficiency_break"] for case in expansion
            ),
            "new_necessity_break_count": sum(
                case["necessity_break"] for case in expansion
            ),
            "new_counterexample_count": len(new_counterexamples),
            "new_counterexample_ids": [
                case["semantic_sha256"] for case in new_counterexamples
            ],
        },
        "expansion_cases": expansion,
        "progress_audit": {
            "new_verdicts": new_verdicts,
            "new_canonical_nonisomorphic_counterexamples": (
                new_canonical_counterexamples
            ),
            "candidate_semantic_change": candidate_semantic_change,
            "additional_calibration_fixes": additional_calibration_fixes,
            "progress": progress,
            "streak_after_round": 0,
        },
        "blocker_id": "PB-R2-NONFREE-GLOBAL-FACE-CHAIN",
        "same_blocker_evidence": {
            "valid_no_progress_1_of_2": False,
            "finite_registered_graphs_close": True,
            "remaining_gap": "No general proof for an arbitrary retained nonfree face-chain relation graph.",
        },
        "coverage_limit": "The two fixed full-support six-lift relation graphs (a KILL path and the SLOT circular ladder C3 x K2) plus the recomputed prior 1908 cases; arbitrary relation graphs, larger lift sets, and mixed KILL/SLOT graphs are not covered.",
    }


def round9_report() -> dict[str, object]:
    """Run the preregistered mixed-color/split-support strict expansion."""

    if not (
        CERTIFIED_SEMANTIC_ID == "R2-CSTAR-CERTIFIED-v3"
        and CERTIFIED_SEMANTIC_SHA256
        == "cbb02677a055c69ecf0bb50a5de884fb55bbd4b4b59b75d256815eae69ec4daa"
    ):
        raise AssertionError("Round9 candidate semantic payload drifted")

    r1 = r1_report()
    round8 = round8_report()
    # Round9 is a historical payload.  Its registered byte representation
    # records the pre-PUnit R0 manifest and must remain reproducible after the
    # current R0 oracle moved to the actual PUnit law type.
    r0_sha256 = FINAL_R0_SEMANTIC_SHA256
    r1_sha256 = _canonical_report_sha256(r1)
    round8_sha256 = _canonical_report_sha256(round8)
    _assert_round9_hash_baseline(
        r0_sha256=r0_sha256,
        r1_sha256=r1_sha256,
        round8_sha256=round8_sha256,
        round8=round8,
    )

    prior_comparisons = tuple(_all_comparisons_through_round8())
    prior_full_ids = tuple(
        _case_semantic_sha256(comparison) for comparison in prior_comparisons
    )
    prior_short_ids = tuple(identifier[:20] for identifier in prior_full_ids)
    if not (
        len(prior_comparisons) == 1910
        and len(set(prior_full_ids)) == 1910
        and len(set(prior_short_ids)) == 1910
    ):
        raise AssertionError("Round9 prior 1910-case semantic ID baseline drift")

    prior_counterexamples: list[dict[str, str]] = []
    for comparison in prior_comparisons:
        result = _case_result(
            comparison,
            "round0_through_round8",
            c5_mode="certified",
        )
        if result["sufficiency_break"] or result["necessity_break"]:
            prior_counterexamples.append(
                {
                    "id": result["id"],
                    "semantic_sha256": _case_semantic_sha256(comparison),
                    "query": (
                        "sufficiency_break"
                        if result["sufficiency_break"]
                        else "necessity_break"
                    ),
                }
            )
    if prior_counterexamples:
        raise AssertionError("Round9 prior 1910-case query baseline drift")

    diamond, figure8 = round9_relation_fixtures()
    fixtures = (diamond, figure8)
    expansion = []
    colored_relations = (
        {
            "KILL": tuple(sorted(_checked_relations(4, R9_DIAMOND_KILL_RELATIONS))),
            "SLOT": tuple(sorted(_checked_relations(4, R9_DIAMOND_SLOT_RELATIONS))),
        },
        {
            "KILL": tuple(sorted(_checked_relations(5, R9_FIGURE8_KILL_RELATIONS))),
            "SLOT": (),
        },
    )
    for comparison, registered_colors in zip(fixtures, colored_relations):
        case = _case_result(
            comparison,
            "round9_relation_grammar",
            c5_mode="certified",
        )
        case["semantic_sha256"] = _case_semantic_sha256(comparison)
        actual_direct = tuple(
            tuple(edge)
            for edge in case["candidate"]["whole"]["direct_lifttwin"]["0"][
                "direct_edges"
            ]
        )
        registered_direct = tuple(
            sorted(registered_colors["KILL"] + registered_colors["SLOT"])
        )
        case["certified_colored_adjacency"] = {
            "KILL": [list(edge) for edge in registered_colors["KILL"]],
            "SLOT": [list(edge) for edge in registered_colors["SLOT"]],
            "actual_uncolored": [list(edge) for edge in actual_direct],
            "unintended_edge_count": len(set(actual_direct) - set(registered_direct)),
        }
        case["all_block_h1"] = [
            {
                "coarse_targets_A": sorted(targets),
                "h1": asdict(analysis),
            }
            for targets, analysis in comparison.block_analyses()
        ]
        expansion.append(case)

    diamond_expected_h1 = H1Analysis(3, 3, 3, True, True, True)
    diamond_blocks = diamond.block_analyses()
    diamond_expected_faces = (
        (1, 1, 1),
        (0, 0, 1),
        (2, 2, 2),
        (0, 0, 2),
        (3, 3, 3),
        (0, 0, 3),
        (0, 4, 5),
        (0, 6, 7),
    )
    diamond_expected_fine_faces = (
        (4, 4, 4),
        (0, 1, 4),
        (5, 5, 5),
        (1, 2, 5),
        (6, 6, 6),
        (2, 0, 6),
        (1, 7, 8),
        (3, 7, 8),
        (3, 9, 10),
        (2, 9, 10),
    )
    if not (
        diamond.morphism.coarse.vertices == diamond.morphism.fine.vertices == 1
        and len(diamond.morphism.coarse.edges) == 8
        and len(diamond.morphism.coarse.faces) == 8
        and len(diamond.morphism.fine.edges) == 11
        and len(diamond.morphism.fine.faces) == 10
        and diamond.morphism.coarse.faces == diamond_expected_faces
        and diamond.morphism.fine.faces == diamond_expected_fine_faces
        and diamond.morphism.vertex_map == (0,)
        and diamond.morphism.edge_map == (0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7)
        and diamond.morphism.face_map == (0, 1, 2, 3, 4, 5, 6, 6, 7, 7)
        and diamond.coarse_chart_supports == (frozenset((0, 1, 2, 3)),)
        and diamond.fine_chart_supports == (frozenset((0, 1, 2, 3, 4)),)
        and len(diamond_blocks) == 15
        and all(analysis == diamond_expected_h1 for _, analysis in diamond_blocks)
    ):
        raise AssertionError("Round9 DIAMOND exact fixture/H1 calibration mismatch")

    figure8_blocks = figure8.block_analyses()
    first_support = frozenset((0, 1))
    second_support = frozenset((2, 3))
    support_distribution = {
        "first_support_only": 0,
        "second_support_only": 0,
        "both_supports": 0,
    }
    for targets, analysis in figure8_blocks:
        meets_first = bool(targets & first_support)
        meets_second = bool(targets & second_support)
        dimension = int(meets_first) + int(meets_second)
        expected = H1Analysis(
            dimension,
            dimension,
            dimension,
            True,
            True,
            True,
        )
        if analysis != expected:
            raise AssertionError("Round9 FIGURE8 A-block H1 calibration mismatch")
        if meets_first and meets_second:
            support_distribution["both_supports"] += 1
        elif meets_first:
            support_distribution["first_support_only"] += 1
        elif meets_second:
            support_distribution["second_support_only"] += 1
    if not (
        figure8.morphism.coarse.vertices == figure8.morphism.fine.vertices == 2
        and len(figure8.morphism.coarse.edges) == 8
        and len(figure8.morphism.coarse.faces) == 12
        and len(figure8.morphism.fine.edges) == 12
        and len(figure8.morphism.fine.faces) == 12
        and figure8.morphism.vertex_map == (0, 1)
        and figure8.morphism.edge_map == (0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7)
        and figure8.morphism.face_map == tuple(range(12))
        and figure8.coarse_chart_supports
        == (frozenset((0, 1)), frozenset((2, 3)))
        and figure8.fine_chart_supports
        == (frozenset((0, 1, 2)), frozenset((3, 4)))
        and len(figure8_blocks) == 15
        and support_distribution
        == {
            "first_support_only": 3,
            "second_support_only": 3,
            "both_supports": 9,
        }
    ):
        raise AssertionError("Round9 FIGURE8 exact fixture/support calibration mismatch")

    expected_invariants = (
        {
            "n": 4,
            "m": 5,
            "degrees": [2, 2, 3, 3],
            "beta1": 2,
            "colors": "K^3S^2",
        },
        {
            "n": 5,
            "m": 6,
            "degrees": [2, 2, 2, 2, 4],
            "beta1": 2,
            "colors": "K^6",
        },
    )
    actual_invariants = (
        _relation_graph_invariant(
            4,
            kill_relations=R9_DIAMOND_KILL_RELATIONS,
            slot_relations=R9_DIAMOND_SLOT_RELATIONS,
        ),
        _relation_graph_invariant(
            5,
            kill_relations=R9_FIGURE8_KILL_RELATIONS,
        ),
    )
    for case, registered_colors in zip(expansion, colored_relations):
        registered_direct = tuple(
            sorted(registered_colors["KILL"] + registered_colors["SLOT"])
        )
        actual_direct = tuple(
            tuple(edge)
            for edge in case["certified_colored_adjacency"]["actual_uncolored"]
        )
        all_reductions = (
            case["candidate"]["whole"],
            *case["candidate"]["per_subset"],
        )
        if not (
            case["uniform"]
            and case["candidate"]["all"]
            and actual_direct == registered_direct
            and case["certified_colored_adjacency"]["unintended_edge_count"] == 0
            and all(
                not reduction["coarse_reduction"]["removed_free_pairs"]
                and not reduction["fine_reduction"]["removed_free_pairs"]
                for reduction in all_reductions
            )
        ):
            raise AssertionError("Round9 candidate/free-pair/adjacency calibration mismatch")
    if actual_invariants != expected_invariants:
        raise AssertionError("Round9 colored relation-graph invariant mismatch")

    graph_support_codes = _registered_relation_graph_support_codes_through_round9()
    graph_codes = tuple(
        item["relation_graph_canonical_code"]
        for item in graph_support_codes.values()
    )
    support_codes = tuple(
        item["relation_graph_support_code"]
        for item in graph_support_codes.values()
    )
    if not (
        len(graph_support_codes) == 8
        and len(set(graph_codes)) == 8
        and len(set(support_codes)) == 8
    ):
        raise AssertionError("Round9 graph/support canonicalization collision")

    new_full_ids = tuple(case["semantic_sha256"] for case in expansion)
    new_short_ids = tuple(case["id"] for case in expansion)
    all_full_ids = prior_full_ids + new_full_ids
    all_short_ids = prior_short_ids + new_short_ids
    full_collision_count = len(all_full_ids) - len(set(all_full_ids))
    short_collision_count = len(all_short_ids) - len(set(all_short_ids))
    if not (
        all(full.startswith(short) for full, short in zip(new_full_ids, new_short_ids))
        and not (set(new_full_ids) & set(prior_full_ids))
        and not (set(new_short_ids) & set(prior_short_ids))
        and len(set(new_full_ids)) == len(set(new_short_ids)) == 2
        and len(all_full_ids) == len(all_short_ids) == 1912
        and full_collision_count == short_collision_count == 0
    ):
        raise AssertionError("Round9 semantic payload strict-expansion mismatch")

    new_counterexamples = [
        case
        for case in expansion
        if case["sufficiency_break"] or case["necessity_break"]
    ]
    new_verdicts = sorted(
        {
            "CSTAR-not-sufficient"
            for case in new_counterexamples
            if case["sufficiency_break"]
        }
        | {
            "CSTAR-not-necessary"
            for case in new_counterexamples
            if case["necessity_break"]
        }
    )
    new_canonical_counterexamples = [
        case["semantic_sha256"] for case in new_counterexamples
    ]
    candidate_semantic_change = False
    additional_calibration_fixes: list[str] = []
    progress = bool(
        new_verdicts
        or new_canonical_counterexamples
        or candidate_semantic_change
        or additional_calibration_fixes
    )

    return {
        "round": "R2-round-9",
        "preregistered_issue_comment": 5230824089,
        "final_R0_calibration_comment": 5230818358,
        "valid": True,
        "baseline_payload_sha256": {
            "r0": r0_sha256,
            "r1": r1_sha256,
            "round1_through_round7": list(REGISTERED_ROUND_PAYLOAD_SHA256),
            "round8_diagnostic": round8_sha256,
        },
        "round8_diagnostic_baseline": {
            "valid": round8["valid"],
            "streak_after_round": round8["progress_audit"]["streak_after_round"],
            "diagnostic_zero_result": round8["diagnostic_zero_result"],
            "counted_in_stop_streak": False,
        },
        "candidate": {
            "semantic_id": CERTIFIED_SEMANTIC_ID,
            "semantic_sha256": CERTIFIED_SEMANTIC_SHA256,
            "spec": CERTIFIED_SPEC,
        },
        "population": {
            "prior_raw_cases_recomputed": len(prior_comparisons),
            "prior_full_semantic_payload_ids": len(set(prior_full_ids)),
            "prior_truncated_semantic_payload_ids": len(set(prior_short_ids)),
            "new_relation_grammar_cases": 2,
            "new_full_semantic_payload_ids": list(new_full_ids),
            "new_truncated_semantic_payload_ids": list(new_short_ids),
            "full_sha256_collision_count": full_collision_count,
            "truncated_20hex_collision_count": short_collision_count,
            "strict_superset": True,
            "total_raw_cases": 1912,
            "total_full_semantic_payload_ids": len(set(all_full_ids)),
            "total_truncated_semantic_payload_ids": len(set(all_short_ids)),
            "new_A_block_queries": sum(
                len(comparison.block_analyses()) for comparison in fixtures
            ),
            "all_cases_evaluated": True,
        },
        "canonical_relation_graph_support_codes": graph_support_codes,
        "relation_graph_invariants": {
            comparison.name: invariant
            for comparison, invariant in zip(fixtures, actual_invariants)
        },
        "figure8_A_block_distribution": support_distribution,
        "queries": {
            "prior_sufficiency_or_necessity_break_count": len(
                prior_counterexamples
            ),
            "prior_counterexamples": prior_counterexamples,
            "new_sufficiency_break_count": sum(
                case["sufficiency_break"] for case in expansion
            ),
            "new_necessity_break_count": sum(
                case["necessity_break"] for case in expansion
            ),
            "new_counterexample_count": len(new_counterexamples),
            "new_counterexample_ids": [
                case["semantic_sha256"] for case in new_counterexamples
            ],
        },
        "expansion_cases": expansion,
        "progress_audit": {
            "new_verdicts": new_verdicts,
            "new_canonical_nonisomorphic_counterexamples": (
                new_canonical_counterexamples
            ),
            "candidate_semantic_change": candidate_semantic_change,
            "additional_calibration_fixes": additional_calibration_fixes,
            "progress": progress,
            "streak_after_round": 0 if progress else 1,
        },
        "blocker_id": "PB-R2-NONFREE-GLOBAL-FACE-CHAIN",
        "same_blocker_evidence": {
            "valid_no_progress_1_of_2": not progress,
            "finite_mixed_or_split_support_cases_close": True,
            "remaining_gap": "No general proof for arbitrary retained nonfree face-chain graphs and arbitrary support distributions.",
        },
        "coverage_limit": "The fixed mixed-color diamond and one fixed split-support figure-eight, plus the recomputed prior 1910 cases; arbitrary graph size, certificate coloring, face multiplicity, and support distribution are not covered.",
    }


def _normalized_direct_edges(
    case: dict[str, object],
    coarse_edge: int,
) -> tuple[tuple[int, int], ...]:
    detail = case["candidate"]["whole"]["direct_lifttwin"][str(coarse_edge)]
    lifts = tuple(detail["lifts"])
    local_index = {lift: index for index, lift in enumerate(lifts)}
    return tuple(
        sorted(
            (local_index[left], local_index[right])
            for left, right in detail["direct_edges"]
        )
    )


def _target_relabelled_chart_records(
    chart_records: tuple[ChartCodeSpec, ...],
    *,
    coarse_permutation: tuple[int, ...],
    fine_permutation: tuple[int, ...],
) -> tuple[ChartCodeSpec, ...]:
    return tuple(
        ChartCodeSpec(
            frozenset(
                coarse_permutation[target]
                for target in record.coarse_support
            ),
            frozenset(
                fine_permutation[target]
                for target in record.fine_support
            ),
            record.relation_blocks,
            record.identity_loop_count,
        )
        for record in chart_records
    )


def round10_report() -> dict[str, object]:
    """Run the preregistered K2,3/K4+star multichart expansion."""

    if not (
        CERTIFIED_SEMANTIC_ID == "R2-CSTAR-CERTIFIED-v3"
        and CERTIFIED_SEMANTIC_SHA256
        == "cbb02677a055c69ecf0bb50a5de884fb55bbd4b4b59b75d256815eae69ec4daa"
    ):
        raise AssertionError("Round10 candidate semantic payload drifted")

    # The complete registered Round9 payload is the query-admission gate.  A
    # drift, a nonzero prior query, or loss of the first valid no-progress
    # observation stops this round before any Round10 fixture is evaluated.
    round9 = round9_report()
    round9_sha256 = _canonical_report_sha256(round9)
    _assert_round10_hash_baseline(
        round9_sha256=round9_sha256,
        round9=round9,
    )

    prior_comparisons = tuple(_all_comparisons_through_round9())
    prior_full_ids = tuple(
        _case_semantic_sha256(comparison) for comparison in prior_comparisons
    )
    prior_short_ids = tuple(identifier[:20] for identifier in prior_full_ids)
    if not (
        len(prior_comparisons) == 1912
        and len(set(prior_full_ids)) == 1912
        and len(set(prior_short_ids)) == 1912
    ):
        raise AssertionError("Round10 prior 1912-case semantic ID baseline drift")

    prior_counterexamples: list[dict[str, str]] = []
    for comparison in prior_comparisons:
        result = _case_result(
            comparison,
            "round0_through_round9",
            c5_mode="certified",
        )
        if result["sufficiency_break"] or result["necessity_break"]:
            prior_counterexamples.append(
                {
                    "id": result["id"],
                    "semantic_sha256": _case_semantic_sha256(comparison),
                    "query": (
                        "sufficiency_break"
                        if result["sufficiency_break"]
                        else "necessity_break"
                    ),
                }
            )
    if prior_counterexamples:
        raise AssertionError("Round10 prior 1912-case query baseline drift")

    k23, k4_star = round10_relation_fixtures()
    fixtures = (k23, k4_star)
    expansion: list[dict[str, object]] = []
    for comparison in fixtures:
        case = _case_result(
            comparison,
            "round10_multichart_relation_grammar",
            c5_mode="certified",
        )
        case["semantic_payload_json"] = _case_semantic_payload_json(comparison)
        case["semantic_sha256"] = _case_semantic_sha256(comparison)
        if sha256(case["semantic_payload_json"].encode("utf-8")).hexdigest() != case[
            "semantic_sha256"
        ]:
            raise AssertionError("Round10 full semantic JSON/SHA mismatch")
        case["all_block_h1"] = [
            {
                "coarse_targets_A": sorted(targets),
                "h1": asdict(analysis),
            }
            for targets, analysis in comparison.block_analyses()
        ]
        expansion.append(case)

    k23_expected_coarse_faces = (
        (1, 1, 1), (0, 0, 1),
        (2, 2, 2), (0, 0, 2),
        (3, 3, 3), (0, 0, 3),
        (0, 4, 5), (0, 6, 7), (0, 8, 9),
    )
    k23_expected_fine_faces = (
        (5, 5, 5), (0, 2, 5),
        (6, 6, 6), (0, 3, 6),
        (7, 7, 7), (1, 4, 7),
        (0, 8, 9), (4, 8, 9),
        (1, 10, 11), (2, 10, 11),
        (1, 12, 13), (3, 12, 13),
    )
    if not (
        _comparison_cell_counts(k23) == ((2, 11, 9), (2, 15, 12))
        and k23.morphism.coarse.faces == k23_expected_coarse_faces
        and k23.morphism.fine.faces == k23_expected_fine_faces
        and k23.morphism.vertex_map == (0, 1)
        and k23.morphism.edge_map
        == (0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10)
        and k23.morphism.face_map
        == (0, 1, 2, 3, 4, 5, 6, 6, 7, 7, 8, 8)
        and k23.coarse_target_count == 4
        and k23.fine_target_count == 5
        and k23.factor_pi == (0, 0, 1, 2, 3)
        and k23.coarse_chart_supports
        == (frozenset((0, 1, 2)), frozenset((2, 3)))
        and k23.fine_chart_supports
        == (frozenset((0, 1, 2, 3)), frozenset((3, 4)))
    ):
        raise AssertionError("Round10 K2,3 exact fixture calibration mismatch")

    k4_star_expected_coarse_faces = (
        (1, 1, 1), (0, 0, 1),
        (2, 2, 2), (0, 0, 2),
        (3, 3, 3), (0, 0, 3),
        (0, 4, 5), (0, 6, 7), (0, 8, 9),
        (11, 11, 11), (10, 10, 11),
        (10, 12, 13), (10, 14, 15),
    )
    k4_star_expected_fine_faces = (
        (4, 4, 4), (0, 1, 4),
        (5, 5, 5), (1, 2, 5),
        (6, 6, 6), (2, 0, 6),
        (0, 7, 8), (3, 7, 8),
        (1, 9, 10), (3, 9, 10),
        (2, 11, 12), (3, 11, 12),
        (17, 17, 17), (13, 14, 17),
        (13, 18, 19), (15, 18, 19),
        (13, 20, 21), (16, 20, 21),
    )
    if not (
        _comparison_cell_counts(k4_star) == ((3, 17, 13), (3, 23, 18))
        and k4_star.morphism.coarse.faces == k4_star_expected_coarse_faces
        and k4_star.morphism.fine.faces == k4_star_expected_fine_faces
        and k4_star.morphism.vertex_map == (0, 1, 2)
        and k4_star.morphism.edge_map
        == (
            0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
            10, 10, 10, 10, 11, 12, 13, 14, 15, 16,
        )
        and k4_star.morphism.face_map
        == (0, 1, 2, 3, 4, 5, 6, 6, 7, 7, 8, 8, 9, 10, 11, 11, 12, 12)
        and k4_star.coarse_target_count == 4
        and k4_star.fine_target_count == 5
        and k4_star.factor_pi == (0, 0, 1, 2, 3)
        and k4_star.coarse_chart_supports
        == (
            frozenset((0, 1)),
            frozenset((1, 2)),
            frozenset((2, 3)),
        )
        and k4_star.fine_chart_supports
        == (
            frozenset((0, 1, 2)),
            frozenset((2, 3)),
            frozenset((3, 4)),
        )
    ):
        raise AssertionError("Round10 K4+star exact fixture calibration mismatch")

    h1_expected_tables: dict[str, list[dict[str, object]]] = {}
    h1_dimension_histograms: dict[str, dict[str, int]] = {}
    k23_first_support = frozenset((0, 1, 2))
    k23_second_support = frozenset((2, 3))
    k4_star_expected_dimensions = {
        frozenset((0,)): 4,
        frozenset((1,)): 7,
        frozenset((2,)): 4,
        frozenset((3,)): 1,
        frozenset((0, 1)): 7,
        frozenset((0, 2)): 8,
        frozenset((0, 3)): 5,
        frozenset((1, 2)): 8,
        frozenset((1, 3)): 8,
        frozenset((2, 3)): 4,
        frozenset((0, 1, 2)): 8,
        frozenset((0, 1, 3)): 8,
        frozenset((0, 2, 3)): 8,
        frozenset((1, 2, 3)): 8,
        frozenset((0, 1, 2, 3)): 8,
    }
    expected_histograms = (
        {"1": 1, "4": 3, "5": 11},
        {"1": 1, "4": 3, "5": 1, "7": 2, "8": 8},
    )
    for fixture_index, comparison in enumerate(fixtures):
        table: list[dict[str, object]] = []
        histogram: dict[str, int] = {}
        blocks = comparison.block_analyses()
        if len(blocks) != 15:
            raise AssertionError("Round10 fixture did not enumerate all 15 A")
        for targets, analysis in blocks:
            expected_dimension = (
                4 * int(bool(targets & k23_first_support))
                + int(bool(targets & k23_second_support))
                if fixture_index == 0
                else k4_star_expected_dimensions[targets]
            )
            expected = H1Analysis(
                expected_dimension,
                expected_dimension,
                expected_dimension,
                True,
                True,
                True,
            )
            if analysis != expected:
                raise AssertionError("Round10 exact A-block H1 calibration mismatch")
            dimension_key = str(expected_dimension)
            histogram[dimension_key] = histogram.get(dimension_key, 0) + 1
            table.append(
                {
                    "coarse_targets_A": sorted(targets),
                    "expected_h1": asdict(expected),
                }
            )
        if histogram != expected_histograms[fixture_index]:
            raise AssertionError("Round10 A-block H1 histogram mismatch")
        h1_expected_tables[comparison.name] = table
        h1_dimension_histograms[comparison.name] = histogram

    registered_colored_adjacencies = (
        {
            "K23": {
                "coarse_edge": 0,
                "KILL": tuple(sorted(_checked_relations(5, R10_A_KILL_RELATIONS))),
                "SLOT": tuple(sorted(_checked_relations(5, R10_A_SLOT_RELATIONS))),
            },
        },
        {
            "K4": {
                "coarse_edge": 0,
                "KILL": tuple(sorted(_checked_relations(4, R10_B_K4_KILL_RELATIONS))),
                "SLOT": tuple(sorted(_checked_relations(4, R10_B_K4_SLOT_RELATIONS))),
            },
            "STAR": {
                "coarse_edge": 10,
                "KILL": tuple(sorted(_checked_relations(4, R10_B_STAR_KILL_RELATIONS))),
                "SLOT": tuple(sorted(_checked_relations(4, R10_B_STAR_SLOT_RELATIONS))),
            },
        },
    )
    for fixture_index, (comparison, case) in enumerate(zip(fixtures, expansion)):
        adjacency_report: dict[str, dict[str, object]] = {}
        for block_name, registered in registered_colored_adjacencies[
            fixture_index
        ].items():
            registered_edges = tuple(
                sorted(registered["KILL"] + registered["SLOT"])
            )
            actual_edges = _normalized_direct_edges(
                case,
                registered["coarse_edge"],
            )
            adjacency_report[block_name] = {
                "coarse_edge": registered["coarse_edge"],
                "KILL": [list(edge) for edge in registered["KILL"]],
                "SLOT": [list(edge) for edge in registered["SLOT"]],
                "actual_uncolored": [list(edge) for edge in actual_edges],
                "unintended_edge_count": len(
                    set(actual_edges) - set(registered_edges)
                ),
            }
            if actual_edges != registered_edges:
                raise AssertionError("Round10 exact colored adjacency mismatch")
        case["certified_colored_adjacency"] = adjacency_report

        whole_details = case["candidate"]["whole"]["direct_lifttwin"]
        nontrivial_edges = {
            registered["coarse_edge"]
            for registered in registered_colored_adjacencies[fixture_index].values()
        }
        auxiliary_details = tuple(
            detail
            for edge, detail in whole_details.items()
            if int(edge) not in nontrivial_edges
        )
        all_reductions = (
            case["candidate"]["whole"],
            *case["candidate"]["per_subset"],
        )
        if not (
            case["uniform"]
            and case["candidate"]["all"]
            and all(case["candidate"]["aggregate"].values())
            and len(case["candidate"]["per_subset"]) == 15
            and all(
                not reduction["coarse_reduction"]["removed_free_pairs"]
                and not reduction["fine_reduction"]["removed_free_pairs"]
                for reduction in all_reductions
            )
            and len(whole_details) == len(comparison.morphism.coarse.edges)
            and all(
                len(detail["lifts"]) == 1
                and detail["direct_edges"] == []
                and len(detail["components"]) == 1
                for detail in auxiliary_details
            )
        ):
            raise AssertionError("Round10 C*/free-pair/auxiliary-lift mismatch")

    expected_relation_invariants = {
        "R10-A-K23-MIXED-OVERLAP": {
            "K23": {
                "n": 5,
                "m": 6,
                "degrees": [2, 2, 2, 3, 3],
                "beta1": 2,
                "colors": "K^3S^3",
            },
        },
        "R10-B-K4-STAR-CHAIN-SUPPORT": {
            "K4": {
                "n": 4,
                "m": 6,
                "degrees": [3, 3, 3, 3],
                "beta1": 3,
                "colors": "K^3S^3",
            },
            "STAR": {
                "n": 4,
                "m": 3,
                "degrees": [1, 1, 1, 3],
                "beta1": 0,
                "colors": "K^1S^2",
            },
        },
    }
    actual_relation_invariants = {
        k23.name: {
            "K23": _relation_graph_invariant(
                5,
                kill_relations=R10_A_KILL_RELATIONS,
                slot_relations=R10_A_SLOT_RELATIONS,
            ),
        },
        k4_star.name: {
            "K4": _relation_graph_invariant(
                4,
                kill_relations=R10_B_K4_KILL_RELATIONS,
                slot_relations=R10_B_K4_SLOT_RELATIONS,
            ),
            "STAR": _relation_graph_invariant(
                4,
                kill_relations=R10_B_STAR_KILL_RELATIONS,
                slot_relations=R10_B_STAR_SLOT_RELATIONS,
            ),
        },
    }
    if actual_relation_invariants != expected_relation_invariants:
        raise AssertionError("Round10 colored relation invariant mismatch")

    graph_support_codes = _registered_colored_graph_support_codes_through_round10()
    graph_full_ids = tuple(item["sha256"] for item in graph_support_codes.values())
    graph_short_ids = tuple(identifier[:20] for identifier in graph_full_ids)
    graph_payloads = tuple(
        item["compact_json"] for item in graph_support_codes.values()
    )
    if not (
        len(graph_support_codes) == 10
        and len(set(graph_full_ids)) == 10
        and len(set(graph_short_ids)) == 10
        and len(set(graph_payloads)) == 10
    ):
        raise AssertionError("Round10 graph/support canonicalization collision")

    k23_charts = (
        ChartCodeSpec(
            frozenset((0, 1, 2)),
            frozenset((0, 1, 2, 3)),
            (
                RelationBlockCodeSpec(
                    5,
                    R10_A_KILL_RELATIONS,
                    R10_A_SLOT_RELATIONS,
                ),
            ),
        ),
        ChartCodeSpec(
            frozenset((2, 3)),
            frozenset((3, 4)),
            identity_loop_count=1,
        ),
    )
    k4_star_charts = (
        ChartCodeSpec(
            frozenset((0, 1)),
            frozenset((0, 1, 2)),
            (
                RelationBlockCodeSpec(
                    4,
                    R10_B_K4_KILL_RELATIONS,
                    R10_B_K4_SLOT_RELATIONS,
                ),
            ),
        ),
        ChartCodeSpec(
            frozenset((1, 2)),
            frozenset((2, 3)),
            (
                RelationBlockCodeSpec(
                    4,
                    R10_B_STAR_KILL_RELATIONS,
                    R10_B_STAR_SLOT_RELATIONS,
                ),
            ),
        ),
        ChartCodeSpec(
            frozenset((2, 3)),
            frozenset((3, 4)),
            identity_loop_count=1,
        ),
    )
    k23_base_code = graph_support_codes[k23.name]
    k4_star_base_code = graph_support_codes[k4_star.name]
    lift_relabel = (4, 2, 0, 3, 1)
    lift_relabelled_charts = (
        ChartCodeSpec(
            k23_charts[0].coarse_support,
            k23_charts[0].fine_support,
            (
                RelationBlockCodeSpec(
                    5,
                    tuple(
                        (lift_relabel[left], lift_relabel[right])
                        for left, right in R10_A_KILL_RELATIONS
                    ),
                    tuple(
                        (lift_relabel[left], lift_relabel[right])
                        for left, right in R10_A_SLOT_RELATIONS
                    ),
                ),
            ),
        ),
        k23_charts[1],
    )
    lift_relabelled_code = colored_graph_support_canonical_code(
        factor_pi=k23.factor_pi,
        chart_records=lift_relabelled_charts,
        coarse_cell_counts=(2, 11, 9),
        fine_cell_counts=(2, 15, 12),
    )
    chart_relabelled_code = colored_graph_support_canonical_code(
        factor_pi=k4_star.factor_pi,
        chart_records=tuple(reversed(k4_star_charts)),
        coarse_cell_counts=(3, 17, 13),
        fine_cell_counts=(3, 23, 18),
    )
    target_relabelled_code = colored_graph_support_canonical_code(
        factor_pi=k4_star.factor_pi,
        chart_records=_target_relabelled_chart_records(
            k4_star_charts,
            coarse_permutation=(0, 2, 1, 3),
            fine_permutation=(0, 1, 3, 2, 4),
        ),
        coarse_cell_counts=(3, 17, 13),
        fine_cell_counts=(3, 23, 18),
    )
    support_drift_code = colored_graph_support_canonical_code(
        factor_pi=k23.factor_pi,
        chart_records=(
            ChartCodeSpec(
                frozenset((0, 1)),
                frozenset((0, 1, 2)),
                k23_charts[0].relation_blocks,
            ),
            k23_charts[1],
        ),
        coarse_cell_counts=(2, 11, 9),
        fine_cell_counts=(2, 15, 12),
    )
    if not (
        lift_relabelled_code == k23_base_code
        and chart_relabelled_code == k4_star_base_code
        and target_relabelled_code == k4_star_base_code
        and support_drift_code != k23_base_code
        and len(k4_star_charts) == 3
        and sum(bool(chart.relation_blocks) for chart in k4_star_charts) == 2
    ):
        raise AssertionError("Round10 graph/support relabel or drift calibration mismatch")

    new_full_ids = tuple(case["semantic_sha256"] for case in expansion)
    new_short_ids = tuple(case["id"] for case in expansion)
    all_full_ids = prior_full_ids + new_full_ids
    all_short_ids = prior_short_ids + new_short_ids
    full_collision_count = len(all_full_ids) - len(set(all_full_ids))
    short_collision_count = len(all_short_ids) - len(set(all_short_ids))
    if not (
        all(full.startswith(short) for full, short in zip(new_full_ids, new_short_ids))
        and not (set(new_full_ids) & set(prior_full_ids))
        and not (set(new_short_ids) & set(prior_short_ids))
        and len(set(new_full_ids)) == len(set(new_short_ids)) == 2
        and len(all_full_ids) == len(all_short_ids) == 1914
        and full_collision_count == short_collision_count == 0
    ):
        raise AssertionError("Round10 semantic payload strict-expansion mismatch")

    new_counterexamples = [
        case
        for case in expansion
        if case["sufficiency_break"] or case["necessity_break"]
    ]
    new_verdicts = sorted(
        {
            "CSTAR-not-sufficient"
            for case in new_counterexamples
            if case["sufficiency_break"]
        }
        | {
            "CSTAR-not-necessary"
            for case in new_counterexamples
            if case["necessity_break"]
        }
    )
    new_canonical_counterexamples = [
        case["semantic_sha256"] for case in new_counterexamples
    ]
    candidate_semantic_change = False
    additional_calibration_fixes: list[str] = []
    progress = bool(
        new_verdicts
        or new_canonical_counterexamples
        or candidate_semantic_change
        or additional_calibration_fixes
    )
    stop_condition_c = not progress

    return {
        "round": "R2-round-10",
        "preregistered_issue_comment": 5230881464,
        "final_R0_calibration_comment": 5230818358,
        "round9_result_comment": ROUND9_RESULT_ISSUE_COMMENT,
        "valid": True,
        "baseline_payload_sha256": {
            "r0": FINAL_R0_SEMANTIC_SHA256,
            "r1": FINAL_R1_SEMANTIC_SHA256,
            "round1_through_round7": list(REGISTERED_ROUND_PAYLOAD_SHA256),
            "round8_diagnostic": ROUND8_DIAGNOSTIC_PAYLOAD_SHA256,
            "round9_valid": round9_sha256,
        },
        "round8_diagnostic_baseline": {
            "valid": False,
            "counted_in_stop_streak": False,
        },
        "round9_valid_baseline": {
            "valid": round9["valid"],
            "streak_after_round": round9["progress_audit"]["streak_after_round"],
            "valid_no_progress_1_of_2": round9["same_blocker_evidence"][
                "valid_no_progress_1_of_2"
            ],
        },
        "candidate": {
            "semantic_id": CERTIFIED_SEMANTIC_ID,
            "semantic_sha256": CERTIFIED_SEMANTIC_SHA256,
            "spec": CERTIFIED_SPEC,
        },
        "population": {
            "prior_raw_cases_recomputed": len(prior_comparisons),
            "prior_full_semantic_payload_ids": len(set(prior_full_ids)),
            "prior_truncated_semantic_payload_ids": len(set(prior_short_ids)),
            "new_multichart_relation_cases": 2,
            "new_full_semantic_payload_ids": list(new_full_ids),
            "new_truncated_semantic_payload_ids": list(new_short_ids),
            "full_sha256_collision_count": full_collision_count,
            "truncated_20hex_collision_count": short_collision_count,
            "strict_superset": True,
            "total_raw_cases": 1914,
            "total_full_semantic_payload_ids": len(set(all_full_ids)),
            "total_truncated_semantic_payload_ids": len(set(all_short_ids)),
            "new_A_block_queries": sum(
                len(comparison.block_analyses()) for comparison in fixtures
            ),
            "all_cases_evaluated": True,
        },
        "canonical_colored_graph_support_codes": {
            name: {
                **code,
                "id20": code["sha256"][:20],
            }
            for name, code in graph_support_codes.items()
        },
        "canonical_code_audit": {
            "prior_registered_code_count": 8,
            "new_registered_code_count": 2,
            "registered_code_count": len(graph_support_codes),
            "full_sha256_collision_count": len(graph_full_ids) - len(set(graph_full_ids)),
            "truncated_20hex_collision_count": len(graph_short_ids) - len(set(graph_short_ids)),
            "compact_json_collision_count": len(graph_payloads) - len(set(graph_payloads)),
            "lift_relabel_invariant": lift_relabelled_code == k23_base_code,
            "chart_relabel_invariant": chart_relabelled_code == k4_star_base_code,
            "target_relabel_invariant": target_relabelled_code == k4_star_base_code,
            "support_drift_detected": support_drift_code != k23_base_code,
            "strict_new": True,
        },
        "relation_graph_invariants": actual_relation_invariants,
        "A_block_expected_h1": h1_expected_tables,
        "A_block_dimension_histograms": h1_dimension_histograms,
        "queries": {
            "prior_sufficiency_or_necessity_break_count": len(
                prior_counterexamples
            ),
            "prior_counterexamples": prior_counterexamples,
            "new_sufficiency_break_count": sum(
                case["sufficiency_break"] for case in expansion
            ),
            "new_necessity_break_count": sum(
                case["necessity_break"] for case in expansion
            ),
            "new_counterexample_count": len(new_counterexamples),
            "new_counterexample_ids": [
                case["semantic_sha256"] for case in new_counterexamples
            ],
        },
        "expansion_cases": expansion,
        "progress_audit": {
            "new_verdicts": new_verdicts,
            "new_canonical_nonisomorphic_counterexamples": (
                new_canonical_counterexamples
            ),
            "candidate_semantic_change": candidate_semantic_change,
            "additional_calibration_fixes": additional_calibration_fixes,
            "progress": progress,
            "streak_after_round": 0 if progress else 2,
        },
        "blocker_id": "PB-R2-NONFREE-GLOBAL-FACE-CHAIN",
        "same_blocker_evidence": {
            "valid_no_progress_2_of_2": not progress,
            "finite_multichart_relation_cases_close": True,
            "remaining_gap": "No general proof for arbitrary retained nonfree face-chain graphs and arbitrary compatible multichart support distributions.",
        },
        "stop_audit": {
            "stop_condition_A_completion": False,
            "stop_condition_B_finite_exhaustion": False,
            "stop_condition_C_two_valid_same_blocker_no_progress": stop_condition_c,
            "terminal_reason": (
                "Stop-C: two consecutive valid same-blocker no-progress rounds"
                if stop_condition_c
                else None
            ),
        },
        "coverage_limit": "The exact K2,3 mixed overlap-support fixture and exact K4-plus-star three-chart chain-support fixture, all 15 nonempty A for each, plus the recomputed prior 1912 cases. Cross-chart nonloop edges or faces, arbitrary graph size and coloring, arbitrary face multiplicity, and arbitrary compatible support distributions remain outside this finite coverage.",
    }


def round11_report() -> dict[str, object]:
    """Run the post-PUnit wheel/bipartite strict expansion."""

    if not (
        CERTIFIED_SEMANTIC_ID == "R2-CSTAR-CERTIFIED-v3"
        and CERTIFIED_SEMANTIC_SHA256
        == "cbb02677a055c69ecf0bb50a5de884fb55bbd4b4b59b75d256815eae69ec4daa"
    ):
        raise AssertionError("Round11 candidate semantic payload drifted")

    current_r0 = r0_report()
    r1 = r1_report()
    current_r0_sha256 = _canonical_report_sha256(current_r0)
    r1_sha256 = _canonical_report_sha256(r1)
    _assert_round11_current_calibration_gate(
        current_r0_sha256=current_r0_sha256,
        current_r0=current_r0,
        r1_sha256=r1_sha256,
        r1=r1,
        manifest_compact_json=POST_PUNIT_MANIFEST_COMPACT_JSON,
        manifest_sha256=POST_PUNIT_MANIFEST_COMPUTED_SHA256,
    )

    historical_round9 = round9_report()
    historical_round9_sha256 = _canonical_report_sha256(historical_round9)
    historical_round9_queries = historical_round9.get("queries", {})
    if not (
        historical_round9_sha256 == ROUND9_VALID_PAYLOAD_SHA256
        and historical_round9.get("valid") is True
        and historical_round9_queries.get(
            "prior_sufficiency_or_necessity_break_count"
        )
        == 0
        and historical_round9_queries.get("new_sufficiency_break_count") == 0
        and historical_round9_queries.get("new_necessity_break_count") == 0
        and historical_round9_queries.get("new_counterexample_count") == 0
    ):
        raise AssertionError("Round11 historical Round9 gate drift")

    historical_round10 = round10_report()
    historical_round10_sha256 = _canonical_report_sha256(historical_round10)
    _assert_round11_hash_baseline(
        current_r0_sha256=current_r0_sha256,
        current_r0=current_r0,
        r1_sha256=r1_sha256,
        r1=r1,
        round9_sha256=historical_round9_sha256,
        round9=historical_round9,
        round10_sha256=historical_round10_sha256,
        round10=historical_round10,
        manifest_compact_json=POST_PUNIT_MANIFEST_COMPACT_JSON,
        manifest_sha256=POST_PUNIT_MANIFEST_COMPUTED_SHA256,
    )

    prior_comparisons = tuple(_all_comparisons_through_round10())
    prior_full_ids = tuple(
        _case_semantic_sha256(comparison) for comparison in prior_comparisons
    )
    prior_short_ids = tuple(identifier[:20] for identifier in prior_full_ids)
    if not (
        len(prior_comparisons) == 1914
        and len(set(prior_full_ids)) == 1914
        and len(set(prior_short_ids)) == 1914
    ):
        raise AssertionError("Round11 prior 1914-case semantic ID baseline drift")

    prior_counterexamples: list[dict[str, str]] = []
    for comparison in prior_comparisons:
        result = _case_result(
            comparison,
            "round0_through_round10",
            c5_mode="certified",
        )
        if result["sufficiency_break"] or result["necessity_break"]:
            prior_counterexamples.append(
                {
                    "id": result["id"],
                    "semantic_sha256": _case_semantic_sha256(comparison),
                    "query": (
                        "sufficiency_break"
                        if result["sufficiency_break"]
                        else "necessity_break"
                    ),
                }
            )
    if prior_counterexamples:
        raise AssertionError("Round11 prior 1914-case query baseline drift")

    wheel, bipartite = round11_relation_fixtures()
    fixtures = (wheel, bipartite)
    expansion: list[dict[str, object]] = []
    for comparison in fixtures:
        case = _case_result(
            comparison,
            "round11_connected_mixed_relation_grammar",
            c5_mode="certified",
        )
        case["semantic_payload_json"] = _case_semantic_payload_json(comparison)
        case["semantic_sha256"] = _case_semantic_sha256(comparison)
        if sha256(case["semantic_payload_json"].encode("utf-8")).hexdigest() != case[
            "semantic_sha256"
        ]:
            raise AssertionError("Round11 full semantic JSON/SHA mismatch")
        case["all_block_h1"] = [
            {
                "coarse_targets_A": sorted(targets),
                "h1": asdict(analysis),
            }
            for targets, analysis in comparison.block_analyses()
        ]
        expansion.append(case)

    wheel_expected_coarse_faces = (
        (1, 1, 1), (0, 0, 1),
        (2, 2, 2), (0, 0, 2),
        (3, 3, 3), (0, 0, 3),
        (4, 4, 4), (0, 0, 4),
        (5, 5, 5), (0, 0, 5),
        (0, 6, 7), (0, 8, 9), (0, 10, 11),
        (0, 12, 13), (0, 14, 15),
    )
    wheel_expected_fine_faces = (
        (6, 6, 6), (1, 2, 6),
        (7, 7, 7), (2, 3, 7),
        (8, 8, 8), (3, 4, 8),
        (9, 9, 9), (4, 5, 9),
        (10, 10, 10), (1, 5, 10),
        (0, 11, 12), (1, 11, 12),
        (0, 13, 14), (2, 13, 14),
        (0, 15, 16), (3, 15, 16),
        (0, 17, 18), (4, 17, 18),
        (0, 19, 20), (5, 19, 20),
    )
    bipartite_expected_coarse_faces = (
        (1, 1, 1), (0, 0, 1),
        (2, 2, 2), (0, 0, 2),
        (3, 3, 3), (0, 0, 3),
        (0, 4, 5), (0, 6, 7), (0, 8, 9),
        (0, 10, 11), (0, 12, 13), (0, 14, 15),
    )
    bipartite_expected_fine_faces = (
        (6, 6, 6), (0, 3, 6),
        (7, 7, 7), (1, 4, 7),
        (8, 8, 8), (2, 5, 8),
        (0, 9, 10), (4, 9, 10),
        (0, 11, 12), (5, 11, 12),
        (1, 13, 14), (3, 13, 14),
        (1, 15, 16), (5, 15, 16),
        (2, 17, 18), (3, 17, 18),
        (2, 19, 20), (4, 19, 20),
    )
    exact_fixture_rows = (
        (
            wheel,
            ((1, 16, 15), (1, 21, 20)),
            wheel_expected_coarse_faces,
            wheel_expected_fine_faces,
            tuple(range(10))
            + (10, 10, 11, 11, 12, 12, 13, 13, 14, 14),
        ),
        (
            bipartite,
            ((1, 16, 12), (1, 21, 18)),
            bipartite_expected_coarse_faces,
            bipartite_expected_fine_faces,
            tuple(range(6))
            + (6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11),
        ),
    )
    for comparison, cell_counts, coarse_faces, fine_faces, face_map in exact_fixture_rows:
        if not (
            _comparison_cell_counts(comparison) == cell_counts
            and comparison.morphism.coarse.faces == coarse_faces
            and comparison.morphism.fine.faces == fine_faces
            and comparison.morphism.vertex_map == (0,)
            and comparison.morphism.edge_map == (0,) * 6 + tuple(range(1, 16))
            and comparison.morphism.face_map == face_map
            and all(left == right for left, right in comparison.morphism.coarse.edges)
            and all(left == right for left, right in comparison.morphism.fine.edges)
            and comparison.coarse_target_count == 4
            and comparison.fine_target_count == 5
            and comparison.factor_pi == (0, 0, 1, 2, 3)
            and comparison.coarse_chart_supports
            == (frozenset((0, 1, 2, 3)),)
            and comparison.fine_chart_supports
            == (frozenset((0, 1, 2, 3, 4)),)
        ):
            raise AssertionError("Round11 exact grammar fixture calibration mismatch")

    expected_h1 = (
        H1Analysis(6, 6, 6, True, True, True),
        H1Analysis(7, 7, 7, True, True, True),
    )
    h1_expected_tables: dict[str, list[dict[str, object]]] = {}
    h1_dimension_histograms: dict[str, dict[str, int]] = {}
    registered_colored_adjacencies = (
        {
            "KILL": tuple(sorted(_checked_relations(6, R11_W5_KILL_RELATIONS))),
            "SLOT": tuple(sorted(_checked_relations(6, R11_W5_SLOT_RELATIONS))),
        },
        {
            "KILL": tuple(sorted(_checked_relations(6, R11_K33_KILL_RELATIONS))),
            "SLOT": tuple(sorted(_checked_relations(6, R11_K33_SLOT_RELATIONS))),
        },
    )
    for comparison, case, expected, registered in zip(
        fixtures,
        expansion,
        expected_h1,
        registered_colored_adjacencies,
    ):
        blocks = comparison.block_analyses()
        if not (
            len(blocks) == 15
            and all(analysis == expected for _, analysis in blocks)
        ):
            raise AssertionError("Round11 exact all-A H1 calibration mismatch")
        h1_expected_tables[comparison.name] = [
            {
                "coarse_targets_A": sorted(targets),
                "expected_h1": asdict(expected),
            }
            for targets, _ in blocks
        ]
        h1_dimension_histograms[comparison.name] = {
            str(expected.coarse_h1_dimension): 15,
        }

        registered_edges = tuple(sorted(registered["KILL"] + registered["SLOT"]))
        actual_edges = _normalized_direct_edges(case, 0)
        case["certified_colored_adjacency"] = {
            "coarse_edge": 0,
            "KILL": [list(edge) for edge in registered["KILL"]],
            "SLOT": [list(edge) for edge in registered["SLOT"]],
            "actual_uncolored": [list(edge) for edge in actual_edges],
            "unintended_edge_count": len(set(actual_edges) - set(registered_edges)),
        }
        whole_details = case["candidate"]["whole"]["direct_lifttwin"]
        auxiliary_details = tuple(
            detail for edge, detail in whole_details.items() if int(edge) != 0
        )
        all_reductions = (
            case["candidate"]["whole"],
            *case["candidate"]["per_subset"],
        )
        if not (
            case["uniform"]
            and case["candidate"]["all"]
            and all(case["candidate"]["aggregate"].values())
            and len(case["candidate"]["per_subset"]) == 15
            and actual_edges == registered_edges
            and len(whole_details["0"]["lifts"]) == 6
            and len(whole_details) == 16
            and all(
                not reduction["coarse_reduction"]["removed_free_pairs"]
                and not reduction["fine_reduction"]["removed_free_pairs"]
                and len(reduction["coarse_reduction"]["retained_edges"])
                == len(comparison.morphism.coarse.edges)
                and len(reduction["fine_reduction"]["retained_edges"])
                == len(comparison.morphism.fine.edges)
                and len(reduction["coarse_reduction"]["retained_face_classes"])
                == len(comparison.morphism.coarse.faces)
                and len(reduction["fine_reduction"]["retained_face_classes"])
                == len(comparison.morphism.fine.faces)
                for reduction in all_reductions
            )
            and all(
                len(detail["lifts"]) == 1
                and detail["direct_edges"] == []
                and detail["components"] == [detail["lifts"]]
                and detail["component_has_fine_selfloop"] == [True]
                for detail in auxiliary_details
            )
        ):
            raise AssertionError("Round11 C*/free-pair/adjacency calibration mismatch")

    expected_relation_invariants = {
        "R11-W5-K5-S5": {
            "n": 6,
            "m": 10,
            "degrees": [3, 3, 3, 3, 3, 5],
            "beta1": 5,
            "colors": "K^5S^5",
        },
        "R11-K33-K3-S6": {
            "n": 6,
            "m": 9,
            "degrees": [3, 3, 3, 3, 3, 3],
            "beta1": 4,
            "colors": "K^3S^6",
        },
    }
    actual_relation_invariants = {
        wheel.name: _relation_graph_invariant(
            6,
            kill_relations=R11_W5_KILL_RELATIONS,
            slot_relations=R11_W5_SLOT_RELATIONS,
        ),
        bipartite.name: _relation_graph_invariant(
            6,
            kill_relations=R11_K33_KILL_RELATIONS,
            slot_relations=R11_K33_SLOT_RELATIONS,
        ),
    }
    if actual_relation_invariants != expected_relation_invariants:
        raise AssertionError("Round11 colored relation invariant mismatch")

    graph_support_codes = _registered_colored_graph_support_codes_through_round11()
    graph_full_ids = tuple(item["sha256"] for item in graph_support_codes.values())
    graph_short_ids = tuple(identifier[:20] for identifier in graph_full_ids)
    graph_payloads = tuple(
        item["compact_json"] for item in graph_support_codes.values()
    )
    if not (
        len(graph_support_codes) == 12
        and len(set(graph_full_ids)) == 12
        and len(set(graph_short_ids)) == 12
        and len(set(graph_payloads)) == 12
        and graph_support_codes[wheel.name]
        != graph_support_codes[bipartite.name]
        and graph_support_codes[bipartite.name]
        != graph_support_codes["R8-CL3-SLOT"]
    ):
        raise AssertionError("Round11 graph/support canonicalization collision")

    r8_ladder_invariant = _relation_graph_invariant(
        6,
        slot_relations=R8_CL3_SLOT_RELATIONS,
    )
    bipartite_invariant = actual_relation_invariants[bipartite.name]
    if not (
        tuple(r8_ladder_invariant[key] for key in ("n", "m", "degrees", "beta1"))
        == tuple(bipartite_invariant[key] for key in ("n", "m", "degrees", "beta1"))
        and r8_ladder_invariant["colors"] == "S^9"
        and bipartite_invariant["colors"] == "K^3S^6"
    ):
        raise AssertionError("Round11 R8/K3,3 colored distinction mismatch")

    full_chart = ChartCodeSpec(
        frozenset((0, 1, 2, 3)),
        frozenset((0, 1, 2, 3, 4)),
        (
            RelationBlockCodeSpec(
                6,
                R11_W5_KILL_RELATIONS,
                R11_W5_SLOT_RELATIONS,
            ),
        ),
    )
    wheel_base_code = graph_support_codes[wheel.name]
    lift_relabel = (5, 3, 1, 4, 0, 2)
    lift_relabelled_code = colored_graph_support_canonical_code(
        factor_pi=wheel.factor_pi,
        chart_records=(
            ChartCodeSpec(
                full_chart.coarse_support,
                full_chart.fine_support,
                (
                    RelationBlockCodeSpec(
                        6,
                        tuple(
                            (lift_relabel[left], lift_relabel[right])
                            for left, right in R11_W5_KILL_RELATIONS
                        ),
                        tuple(
                            (lift_relabel[left], lift_relabel[right])
                            for left, right in R11_W5_SLOT_RELATIONS
                        ),
                    ),
                ),
            ),
        ),
        coarse_cell_counts=(1, 16, 15),
        fine_cell_counts=(1, 21, 20),
    )
    target_chart_relabelled_code = colored_graph_support_canonical_code(
        factor_pi=wheel.factor_pi,
        chart_records=tuple(
            reversed(
                _target_relabelled_chart_records(
                    (full_chart,),
                    coarse_permutation=(0, 2, 1, 3),
                    fine_permutation=(0, 1, 3, 2, 4),
                )
            )
        ),
        coarse_cell_counts=(1, 16, 15),
        fine_cell_counts=(1, 21, 20),
    )
    support_drift_code = colored_graph_support_canonical_code(
        factor_pi=wheel.factor_pi,
        chart_records=(
            ChartCodeSpec(
                frozenset((0, 1, 2)),
                frozenset((0, 1, 2, 3)),
                full_chart.relation_blocks,
            ),
        ),
        coarse_cell_counts=(1, 16, 15),
        fine_cell_counts=(1, 21, 20),
    )
    cell_count_drift_code = colored_graph_support_canonical_code(
        factor_pi=wheel.factor_pi,
        chart_records=(full_chart,),
        coarse_cell_counts=(1, 16, 16),
        fine_cell_counts=(1, 21, 20),
    )
    if not (
        lift_relabelled_code == wheel_base_code
        and target_chart_relabelled_code == wheel_base_code
        and support_drift_code != wheel_base_code
        and cell_count_drift_code != wheel_base_code
    ):
        raise AssertionError("Round11 relabel/support/cell canonical code mismatch")

    new_full_ids = tuple(case["semantic_sha256"] for case in expansion)
    new_short_ids = tuple(case["id"] for case in expansion)
    all_full_ids = prior_full_ids + new_full_ids
    all_short_ids = prior_short_ids + new_short_ids
    full_collision_count = len(all_full_ids) - len(set(all_full_ids))
    short_collision_count = len(all_short_ids) - len(set(all_short_ids))
    if not (
        all(full.startswith(short) for full, short in zip(new_full_ids, new_short_ids))
        and not (set(new_full_ids) & set(prior_full_ids))
        and not (set(new_short_ids) & set(prior_short_ids))
        and len(set(new_full_ids)) == len(set(new_short_ids)) == 2
        and len(all_full_ids) == len(all_short_ids) == 1916
        and full_collision_count == short_collision_count == 0
    ):
        raise AssertionError("Round11 semantic payload strict-expansion mismatch")

    new_counterexamples = [
        case
        for case in expansion
        if case["sufficiency_break"] or case["necessity_break"]
    ]
    new_verdicts = sorted(
        {
            "CSTAR-not-sufficient"
            for case in new_counterexamples
            if case["sufficiency_break"]
        }
        | {
            "CSTAR-not-necessary"
            for case in new_counterexamples
            if case["necessity_break"]
        }
    )
    new_canonical_counterexamples = [
        case["semantic_sha256"] for case in new_counterexamples
    ]
    candidate_semantic_change = False
    additional_calibration_fixes: list[str] = []
    progress = bool(
        new_verdicts
        or new_canonical_counterexamples
        or candidate_semantic_change
        or additional_calibration_fixes
    )

    return {
        "round": "R2-round-11",
        "preregistered_issue_comment": 5231154236,
        "valid": True,
        "query_admission": {
            "post_punit_r0_issue_comment": POST_PUNIT_R0_ISSUE_COMMENT,
            "post_punit_r0_sha256": current_r0_sha256,
            "pre_punit_r0_rejected_sha256": FINAL_R0_SEMANTIC_SHA256,
            "r1_sha256": r1_sha256,
            "historical_round8_sha256": ROUND8_DIAGNOSTIC_PAYLOAD_SHA256,
            "historical_round9_sha256": historical_round9_sha256,
            "historical_round10_sha256": historical_round10_sha256,
            "manifest_compact_json": POST_PUNIT_MANIFEST_COMPACT_JSON,
            "manifest_sha256": POST_PUNIT_MANIFEST_COMPUTED_SHA256,
            "manifest_registered_sha256": POST_PUNIT_MANIFEST_REGISTERED_SHA256,
            "all_gates_pass": True,
        },
        "historical_payload_compatibility": {
            "round9_uses_historical_pre_punit_r0_manifest": True,
            "round9_payload_unchanged": (
                historical_round9_sha256 == ROUND9_VALID_PAYLOAD_SHA256
            ),
            "round10_payload_unchanged": (
                historical_round10_sha256 == HISTORICAL_ROUND10_PAYLOAD_SHA256
            ),
            "round8_diagnostic_only": True,
        },
        "calibration_progress_reset": {
            "last_progress": "R0(d)-PUnit-provenance-calibration-fix",
            "issue_comment": POST_PUNIT_R0_ISSUE_COMMENT,
            "entry_streak": 0,
        },
        "candidate": {
            "semantic_id": CERTIFIED_SEMANTIC_ID,
            "semantic_sha256": CERTIFIED_SEMANTIC_SHA256,
            "spec": CERTIFIED_SPEC,
        },
        "population": {
            "prior_raw_cases_recomputed": len(prior_comparisons),
            "prior_full_semantic_payload_ids": len(set(prior_full_ids)),
            "prior_truncated_semantic_payload_ids": len(set(prior_short_ids)),
            "new_connected_mixed_graph_cases": 2,
            "new_full_semantic_payload_ids": list(new_full_ids),
            "new_truncated_semantic_payload_ids": list(new_short_ids),
            "full_sha256_collision_count": full_collision_count,
            "truncated_20hex_collision_count": short_collision_count,
            "strict_superset": True,
            "total_raw_cases": 1916,
            "total_full_semantic_payload_ids": len(set(all_full_ids)),
            "total_truncated_semantic_payload_ids": len(set(all_short_ids)),
            "new_A_block_queries": sum(
                len(comparison.block_analyses()) for comparison in fixtures
            ),
            "all_cases_evaluated": True,
        },
        "canonical_colored_graph_support_codes": {
            name: {
                **code,
                "id20": code["sha256"][:20],
            }
            for name, code in graph_support_codes.items()
        },
        "canonical_code_audit": {
            "prior_registered_code_count": 10,
            "new_registered_code_count": 2,
            "registered_code_count": len(graph_support_codes),
            "full_sha256_collision_count": len(graph_full_ids) - len(set(graph_full_ids)),
            "truncated_20hex_collision_count": len(graph_short_ids) - len(set(graph_short_ids)),
            "compact_json_collision_count": len(graph_payloads) - len(set(graph_payloads)),
            "strict_new": True,
            "lift_relabel_invariant": lift_relabelled_code == wheel_base_code,
            "target_chart_relabel_invariant": (
                target_chart_relabelled_code == wheel_base_code
            ),
            "support_drift_detected": support_drift_code != wheel_base_code,
            "cell_count_drift_detected": cell_count_drift_code != wheel_base_code,
            "r8_ladder_and_k33_uncolored_invariants_equal": True,
            "r8_ladder_and_k33_colored_codes_distinct": True,
        },
        "relation_graph_invariants": actual_relation_invariants,
        "A_block_expected_h1": h1_expected_tables,
        "A_block_dimension_histograms": h1_dimension_histograms,
        "queries": {
            "prior_sufficiency_or_necessity_break_count": len(
                prior_counterexamples
            ),
            "prior_counterexamples": prior_counterexamples,
            "new_sufficiency_break_count": sum(
                case["sufficiency_break"] for case in expansion
            ),
            "new_necessity_break_count": sum(
                case["necessity_break"] for case in expansion
            ),
            "new_counterexample_count": len(new_counterexamples),
            "new_counterexample_ids": [
                case["semantic_sha256"] for case in new_counterexamples
            ],
        },
        "expansion_cases": expansion,
        "progress_audit": {
            "entry_streak": 0,
            "new_verdicts": new_verdicts,
            "new_canonical_nonisomorphic_counterexamples": (
                new_canonical_counterexamples
            ),
            "candidate_semantic_change": candidate_semantic_change,
            "additional_calibration_fixes": additional_calibration_fixes,
            "progress": progress,
            "streak_after_round": 0 if progress else 1,
        },
        "blocker_id": "PB-R2-NONFREE-GLOBAL-FACE-CHAIN",
        "same_blocker_evidence": {
            "valid_no_progress_1_of_2": not progress,
            "fixed_full_support_six_lift_mixed_graphs_close": True,
            "remaining_gap": "No general proof for arbitrary retained nonfree face-chain graphs, colorings, face multiplicities, or support distributions.",
        },
        "stop_audit": {
            "stop_condition_B_finite_exhaustion": False,
            "stop_condition_C_two_valid_same_blocker_no_progress": False,
            "finite_zero_result_is_not_general_proof": True,
        },
        "coverage_limit": "The two fixed full-support six-lift mixed graphs W5 K5/S5 and K3,3 K3/S6, all 15 nonempty A for each, plus the recomputed prior 1914 cases. Arbitrary graph size or coloring, face multiplicity, support distribution, multichart supports, and cross-chart incidence remain outside this finite coverage.",
    }


def round12_report() -> dict[str, object]:
    """Run the preregistered octahedral/partitioned multichart expansion."""

    if not (
        CERTIFIED_SEMANTIC_ID == "R2-CSTAR-CERTIFIED-v3"
        and CERTIFIED_SEMANTIC_SHA256
        == "cbb02677a055c69ecf0bb50a5de884fb55bbd4b4b59b75d256815eae69ec4daa"
    ):
        raise AssertionError("Round12 candidate semantic payload drifted")

    current_r0 = r0_report()
    r1 = r1_report()
    current_r0_sha256 = _canonical_report_sha256(current_r0)
    r1_sha256 = _canonical_report_sha256(r1)
    _assert_round11_current_calibration_gate(
        current_r0_sha256=current_r0_sha256,
        current_r0=current_r0,
        r1_sha256=r1_sha256,
        r1=r1,
        manifest_compact_json=POST_PUNIT_MANIFEST_COMPACT_JSON,
        manifest_sha256=POST_PUNIT_MANIFEST_COMPUTED_SHA256,
    )

    round11 = round11_report()
    round11_sha256 = _canonical_report_sha256(round11)
    _assert_round12_hash_baseline(
        current_r0_sha256=current_r0_sha256,
        current_r0=current_r0,
        r1_sha256=r1_sha256,
        r1=r1,
        round11_sha256=round11_sha256,
        round11=round11,
        manifest_compact_json=POST_PUNIT_MANIFEST_COMPACT_JSON,
        manifest_sha256=POST_PUNIT_MANIFEST_COMPUTED_SHA256,
    )

    prior_comparisons = tuple(_all_comparisons_through_round11())
    prior_full_ids = tuple(
        _case_semantic_sha256(comparison) for comparison in prior_comparisons
    )
    prior_short_ids = tuple(identifier[:20] for identifier in prior_full_ids)
    if not (
        len(prior_comparisons) == 1916
        and len(set(prior_full_ids)) == 1916
        and len(set(prior_short_ids)) == 1916
    ):
        raise AssertionError("Round12 prior 1916-case semantic ID baseline drift")

    prior_counterexamples: list[dict[str, str]] = []
    for comparison in prior_comparisons:
        result = _case_result(
            comparison,
            "round0_through_round11",
            c5_mode="certified",
        )
        if result["sufficiency_break"] or result["necessity_break"]:
            prior_counterexamples.append(
                {
                    "id": result["id"],
                    "semantic_sha256": _case_semantic_sha256(comparison),
                    "query": (
                        "sufficiency_break"
                        if result["sufficiency_break"]
                        else "necessity_break"
                    ),
                }
            )
    if prior_counterexamples:
        raise AssertionError("Round12 prior 1916-case query baseline drift")

    octahedral, partitioned = round12_relation_fixtures()
    fixtures = (octahedral, partitioned)
    expansion: list[dict[str, object]] = []
    for comparison in fixtures:
        case = _case_result(
            comparison,
            "round12_octahedral_or_partitioned_multichart",
            c5_mode="certified",
        )
        case["semantic_payload_json"] = _case_semantic_payload_json(comparison)
        case["semantic_sha256"] = _case_semantic_sha256(comparison)
        if sha256(case["semantic_payload_json"].encode("utf-8")).hexdigest() != case[
            "semantic_sha256"
        ]:
            raise AssertionError("Round12 full semantic JSON/SHA mismatch")
        case["all_block_h1"] = [
            {
                "coarse_targets_A": sorted(targets),
                "h1": asdict(analysis),
            }
            for targets, analysis in comparison.block_analyses()
        ]
        expansion.append(case)

    octahedral_expected_coarse_faces = (
        (1, 1, 1), (0, 0, 1),
        (2, 2, 2), (0, 0, 2),
        (3, 3, 3), (0, 0, 3),
        (4, 4, 4), (0, 0, 4),
        (5, 5, 5), (0, 0, 5),
        (6, 6, 6), (0, 0, 6),
        (0, 7, 8), (0, 9, 10), (0, 11, 12),
        (0, 13, 14), (0, 15, 16), (0, 17, 18),
    )
    octahedral_expected_fine_faces = (
        (6, 6, 6), (0, 2, 6),
        (7, 7, 7), (2, 4, 7),
        (8, 8, 8), (1, 4, 8),
        (9, 9, 9), (1, 3, 9),
        (10, 10, 10), (3, 5, 10),
        (11, 11, 11), (0, 5, 11),
        (0, 12, 13), (3, 12, 13),
        (1, 14, 15), (2, 14, 15),
        (0, 16, 17), (4, 16, 17),
        (1, 18, 19), (5, 18, 19),
        (2, 20, 21), (5, 20, 21),
        (3, 22, 23), (4, 22, 23),
    )
    if not (
        _comparison_cell_counts(octahedral) == ((1, 19, 18), (1, 24, 24))
        and octahedral.morphism.coarse.faces
        == octahedral_expected_coarse_faces
        and octahedral.morphism.fine.faces == octahedral_expected_fine_faces
        and octahedral.morphism.vertex_map == (0,)
        and octahedral.morphism.edge_map == (0,) * 6 + tuple(range(1, 19))
        and octahedral.morphism.face_map
        == tuple(range(12))
        + (12, 12, 13, 13, 14, 14, 15, 15, 16, 16, 17, 17)
        and octahedral.coarse_target_count == 4
        and octahedral.fine_target_count == 5
        and octahedral.factor_pi == (0, 0, 1, 2, 3)
        and octahedral.coarse_chart_supports
        == (frozenset((0, 1, 2, 3)),)
        and octahedral.fine_chart_supports
        == (frozenset((0, 1, 2, 3, 4)),)
    ):
        raise AssertionError("Round12 octahedral exact fixture mismatch")

    partitioned_expected_coarse_faces = (
        (1, 1, 1), (0, 0, 1),
        (2, 2, 2), (0, 0, 2),
        (3, 3, 3), (0, 0, 3),
        (0, 4, 5), (0, 6, 7), (0, 8, 9),
        (11, 11, 11), (10, 10, 11),
        (12, 12, 12), (10, 10, 12),
        (10, 13, 14), (10, 15, 16),
    )
    partitioned_expected_fine_faces = (
        (5, 5, 5), (0, 1, 5),
        (6, 6, 6), (2, 3, 6),
        (7, 7, 7), (1, 4, 7),
        (1, 8, 9), (2, 8, 9),
        (0, 10, 11), (3, 10, 11),
        (2, 12, 13), (4, 12, 13),
        (19, 19, 19), (14, 15, 19),
        (20, 20, 20), (14, 16, 20),
        (14, 21, 22), (17, 21, 22),
        (14, 23, 24), (18, 23, 24),
    )
    if not (
        _comparison_cell_counts(partitioned) == ((3, 18, 15), (3, 26, 20))
        and partitioned.morphism.coarse.faces
        == partitioned_expected_coarse_faces
        and partitioned.morphism.fine.faces == partitioned_expected_fine_faces
        and partitioned.morphism.vertex_map == (0, 1, 2)
        and partitioned.morphism.edge_map
        == (
            0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
            10, 10, 10, 10, 10, 11, 12, 13, 14, 15, 16, 17,
        )
        and partitioned.morphism.face_map
        == (
            0, 1, 2, 3, 4, 5, 6, 6, 7, 7, 8, 8,
            9, 10, 11, 12, 13, 13, 14, 14,
        )
        and partitioned.coarse_target_count == 4
        and partitioned.fine_target_count == 5
        and partitioned.factor_pi == (0, 0, 1, 2, 3)
        and partitioned.coarse_chart_supports
        == (
            frozenset((0, 2)),
            frozenset((1, 3)),
            frozenset((0, 1, 2, 3)),
        )
        and partitioned.fine_chart_supports
        == (
            frozenset((0, 1, 3)),
            frozenset((2, 4)),
            frozenset((0, 1, 2, 3, 4)),
        )
    ):
        raise AssertionError("Round12 partitioned exact fixture mismatch")

    h1_expected_tables: dict[str, list[dict[str, object]]] = {}
    h1_dimension_histograms: dict[str, dict[str, int]] = {}
    house_support = frozenset((0, 2))
    star_support = frozenset((1, 3))
    expected_histograms = (
        {"7": 15},
        {"4": 3, "5": 3, "8": 9},
    )
    for fixture_index, comparison in enumerate(fixtures):
        table: list[dict[str, object]] = []
        histogram: dict[str, int] = {}
        blocks = comparison.block_analyses()
        if len(blocks) != 15:
            raise AssertionError("Round12 fixture did not enumerate all 15 A")
        for targets, analysis in blocks:
            expected_dimension = (
                7
                if fixture_index == 0
                else 1
                + 4 * int(bool(targets & house_support))
                + 3 * int(bool(targets & star_support))
            )
            expected = H1Analysis(
                expected_dimension,
                expected_dimension,
                expected_dimension,
                True,
                True,
                True,
            )
            if analysis != expected:
                raise AssertionError("Round12 exact A-block H1 calibration mismatch")
            dimension_key = str(expected_dimension)
            histogram[dimension_key] = histogram.get(dimension_key, 0) + 1
            table.append(
                {
                    "coarse_targets_A": sorted(targets),
                    "expected_h1": asdict(expected),
                }
            )
        if histogram != expected_histograms[fixture_index]:
            raise AssertionError("Round12 A-block H1 distribution mismatch")
        h1_expected_tables[comparison.name] = table
        h1_dimension_histograms[comparison.name] = histogram

    registered_colored_adjacencies = (
        {
            "OCTA": {
                "coarse_edge": 0,
                "KILL": tuple(sorted(_checked_relations(6, R12_OCTA_KILL_RELATIONS))),
                "SLOT": tuple(sorted(_checked_relations(6, R12_OCTA_SLOT_RELATIONS))),
            },
        },
        {
            "HOUSE": {
                "coarse_edge": 0,
                "KILL": tuple(sorted(_checked_relations(5, R12_HOUSE_KILL_RELATIONS))),
                "SLOT": tuple(sorted(_checked_relations(5, R12_HOUSE_SLOT_RELATIONS))),
            },
            "STAR": {
                "coarse_edge": 10,
                "KILL": tuple(sorted(_checked_relations(5, R12_STAR_KILL_RELATIONS))),
                "SLOT": tuple(sorted(_checked_relations(5, R12_STAR_SLOT_RELATIONS))),
            },
        },
    )
    for fixture_index, (comparison, case) in enumerate(zip(fixtures, expansion)):
        adjacency_report: dict[str, dict[str, object]] = {}
        for block_name, registered in registered_colored_adjacencies[
            fixture_index
        ].items():
            registered_edges = tuple(
                sorted(registered["KILL"] + registered["SLOT"])
            )
            actual_edges = _normalized_direct_edges(
                case,
                registered["coarse_edge"],
            )
            adjacency_report[block_name] = {
                "coarse_edge": registered["coarse_edge"],
                "KILL": [list(edge) for edge in registered["KILL"]],
                "SLOT": [list(edge) for edge in registered["SLOT"]],
                "actual_uncolored": [list(edge) for edge in actual_edges],
                "unintended_edge_count": len(
                    set(actual_edges) - set(registered_edges)
                ),
            }
            if actual_edges != registered_edges:
                raise AssertionError("Round12 exact colored adjacency mismatch")
        case["certified_colored_adjacency"] = adjacency_report

        whole_details = case["candidate"]["whole"]["direct_lifttwin"]
        nontrivial_edges = {
            registered["coarse_edge"]
            for registered in registered_colored_adjacencies[fixture_index].values()
        }
        auxiliary_details = tuple(
            detail
            for edge, detail in whole_details.items()
            if int(edge) not in nontrivial_edges
        )
        all_reductions = (
            case["candidate"]["whole"],
            *case["candidate"]["per_subset"],
        )
        if not (
            case["uniform"]
            and case["candidate"]["all"]
            and all(case["candidate"]["aggregate"].values())
            and len(case["candidate"]["per_subset"]) == 15
            and all(
                not reduction["coarse_reduction"]["removed_free_pairs"]
                and not reduction["fine_reduction"]["removed_free_pairs"]
                for reduction in all_reductions
            )
            and len(whole_details) == len(comparison.morphism.coarse.edges)
            and all(
                len(detail["lifts"]) == 1
                and detail["direct_edges"] == []
                and detail["components"] == [detail["lifts"]]
                and detail["component_has_fine_selfloop"] == [True]
                for detail in auxiliary_details
            )
        ):
            raise AssertionError("Round12 C*/free-pair/auxiliary-lift mismatch")

    expected_relation_invariants = {
        "R12-OCTA-K6-S6": {
            "OCTA": {
                "n": 6,
                "m": 12,
                "degrees": [4, 4, 4, 4, 4, 4],
                "beta1": 7,
                "colors": "K^6S^6",
            },
        },
        "R12-HOUSE-STAR-PARTITION": {
            "HOUSE": {
                "n": 5,
                "m": 6,
                "degrees": [2, 2, 2, 3, 3],
                "beta1": 2,
                "colors": "K^3S^3",
            },
            "STAR": {
                "n": 5,
                "m": 4,
                "degrees": [1, 1, 1, 1, 4],
                "beta1": 0,
                "colors": "K^2S^2",
            },
        },
    }
    actual_relation_invariants = {
        octahedral.name: {
            "OCTA": _relation_graph_invariant(
                6,
                kill_relations=R12_OCTA_KILL_RELATIONS,
                slot_relations=R12_OCTA_SLOT_RELATIONS,
            ),
        },
        partitioned.name: {
            "HOUSE": _relation_graph_invariant(
                5,
                kill_relations=R12_HOUSE_KILL_RELATIONS,
                slot_relations=R12_HOUSE_SLOT_RELATIONS,
            ),
            "STAR": _relation_graph_invariant(
                5,
                kill_relations=R12_STAR_KILL_RELATIONS,
                slot_relations=R12_STAR_SLOT_RELATIONS,
            ),
        },
    }
    if actual_relation_invariants != expected_relation_invariants:
        raise AssertionError("Round12 colored relation invariant mismatch")

    graph_support_codes = _registered_colored_graph_support_codes_through_round12()
    graph_full_ids = tuple(item["sha256"] for item in graph_support_codes.values())
    graph_short_ids = tuple(identifier[:20] for identifier in graph_full_ids)
    graph_payloads = tuple(
        item["compact_json"] for item in graph_support_codes.values()
    )
    if not (
        len(graph_support_codes) == 14
        and len(set(graph_full_ids)) == 14
        and len(set(graph_short_ids)) == 14
        and len(set(graph_payloads)) == 14
        and graph_support_codes[octahedral.name]
        != graph_support_codes[partitioned.name]
    ):
        raise AssertionError("Round12 graph/support canonicalization collision")

    octahedral_chart = ChartCodeSpec(
        frozenset((0, 1, 2, 3)),
        frozenset((0, 1, 2, 3, 4)),
        (
            RelationBlockCodeSpec(
                6,
                R12_OCTA_KILL_RELATIONS,
                R12_OCTA_SLOT_RELATIONS,
            ),
        ),
    )
    partitioned_charts = (
        ChartCodeSpec(
            frozenset((0, 2)),
            frozenset((0, 1, 3)),
            (
                RelationBlockCodeSpec(
                    5,
                    R12_HOUSE_KILL_RELATIONS,
                    R12_HOUSE_SLOT_RELATIONS,
                ),
            ),
        ),
        ChartCodeSpec(
            frozenset((1, 3)),
            frozenset((2, 4)),
            (
                RelationBlockCodeSpec(
                    5,
                    R12_STAR_KILL_RELATIONS,
                    R12_STAR_SLOT_RELATIONS,
                ),
            ),
        ),
        ChartCodeSpec(
            frozenset((0, 1, 2, 3)),
            frozenset((0, 1, 2, 3, 4)),
            identity_loop_count=1,
        ),
    )
    octahedral_base_code = graph_support_codes[octahedral.name]
    partitioned_base_code = graph_support_codes[partitioned.name]
    lift_relabel = (5, 2, 0, 4, 1, 3)
    lift_relabelled_code = colored_graph_support_canonical_code(
        factor_pi=octahedral.factor_pi,
        chart_records=(
            ChartCodeSpec(
                octahedral_chart.coarse_support,
                octahedral_chart.fine_support,
                (
                    RelationBlockCodeSpec(
                        6,
                        tuple(
                            (lift_relabel[left], lift_relabel[right])
                            for left, right in R12_OCTA_KILL_RELATIONS
                        ),
                        tuple(
                            (lift_relabel[left], lift_relabel[right])
                            for left, right in R12_OCTA_SLOT_RELATIONS
                        ),
                    ),
                ),
            ),
        ),
        coarse_cell_counts=(1, 19, 18),
        fine_cell_counts=(1, 24, 24),
    )
    chart_relabelled_code = colored_graph_support_canonical_code(
        factor_pi=partitioned.factor_pi,
        chart_records=tuple(reversed(partitioned_charts)),
        coarse_cell_counts=(3, 18, 15),
        fine_cell_counts=(3, 26, 20),
    )
    target_relabelled_code = colored_graph_support_canonical_code(
        factor_pi=partitioned.factor_pi,
        chart_records=_target_relabelled_chart_records(
            partitioned_charts,
            coarse_permutation=(0, 2, 1, 3),
            fine_permutation=(0, 1, 3, 2, 4),
        ),
        coarse_cell_counts=(3, 18, 15),
        fine_cell_counts=(3, 26, 20),
    )
    support_drift_code = colored_graph_support_canonical_code(
        factor_pi=partitioned.factor_pi,
        chart_records=(
            ChartCodeSpec(
                frozenset((0,)),
                frozenset((0, 1)),
                partitioned_charts[0].relation_blocks,
            ),
            partitioned_charts[1],
            partitioned_charts[2],
        ),
        coarse_cell_counts=(3, 18, 15),
        fine_cell_counts=(3, 26, 20),
    )
    if not (
        lift_relabelled_code == octahedral_base_code
        and chart_relabelled_code == partitioned_base_code
        and target_relabelled_code == partitioned_base_code
        and support_drift_code != partitioned_base_code
    ):
        raise AssertionError("Round12 relabel/support canonical code mismatch")

    new_full_ids = tuple(case["semantic_sha256"] for case in expansion)
    new_short_ids = tuple(case["id"] for case in expansion)
    all_full_ids = prior_full_ids + new_full_ids
    all_short_ids = prior_short_ids + new_short_ids
    full_collision_count = len(all_full_ids) - len(set(all_full_ids))
    short_collision_count = len(all_short_ids) - len(set(all_short_ids))
    if not (
        all(full.startswith(short) for full, short in zip(new_full_ids, new_short_ids))
        and not (set(new_full_ids) & set(prior_full_ids))
        and not (set(new_short_ids) & set(prior_short_ids))
        and len(set(new_full_ids)) == len(set(new_short_ids)) == 2
        and len(all_full_ids) == len(all_short_ids) == 1918
        and full_collision_count == short_collision_count == 0
    ):
        raise AssertionError("Round12 semantic payload strict-expansion mismatch")

    new_counterexamples = [
        case
        for case in expansion
        if case["sufficiency_break"] or case["necessity_break"]
    ]
    new_verdicts = sorted(
        {
            "CSTAR-not-sufficient"
            for case in new_counterexamples
            if case["sufficiency_break"]
        }
        | {
            "CSTAR-not-necessary"
            for case in new_counterexamples
            if case["necessity_break"]
        }
    )
    new_canonical_counterexamples = [
        case["semantic_sha256"] for case in new_counterexamples
    ]
    candidate_semantic_change = False
    additional_calibration_fixes: list[str] = []
    progress = bool(
        new_verdicts
        or new_canonical_counterexamples
        or candidate_semantic_change
        or additional_calibration_fixes
    )
    stop_condition_c = not progress

    return {
        "round": "R2-round-12",
        "preregistered_issue_comment": 5231270132,
        "valid": True,
        "query_admission": {
            "post_punit_r0_issue_comment": POST_PUNIT_R0_ISSUE_COMMENT,
            "post_punit_r0_sha256": current_r0_sha256,
            "manifest_sha256": POST_PUNIT_MANIFEST_COMPUTED_SHA256,
            "r1_sha256": r1_sha256,
            "round11_preregistered_issue_comment": (
                ROUND11_PREREGISTERED_ISSUE_COMMENT
            ),
            "round11_result_issue_comment": ROUND11_RESULT_ISSUE_COMMENT,
            "round11_payload_sha256": round11_sha256,
            "all_gates_pass": True,
        },
        "round11_valid_baseline": {
            "valid": round11["valid"],
            "streak_after_round": round11["progress_audit"]["streak_after_round"],
            "valid_no_progress_1_of_2": round11["same_blocker_evidence"][
                "valid_no_progress_1_of_2"
            ],
            "population": round11["population"]["total_raw_cases"],
            "registered_graph_support_codes": round11["canonical_code_audit"][
                "registered_code_count"
            ],
        },
        "candidate": {
            "semantic_id": CERTIFIED_SEMANTIC_ID,
            "semantic_sha256": CERTIFIED_SEMANTIC_SHA256,
            "spec": CERTIFIED_SPEC,
        },
        "population": {
            "prior_raw_cases_recomputed": len(prior_comparisons),
            "prior_full_semantic_payload_ids": len(set(prior_full_ids)),
            "prior_truncated_semantic_payload_ids": len(set(prior_short_ids)),
            "new_octahedral_or_partitioned_cases": 2,
            "new_full_semantic_payload_ids": list(new_full_ids),
            "new_truncated_semantic_payload_ids": list(new_short_ids),
            "full_sha256_collision_count": full_collision_count,
            "truncated_20hex_collision_count": short_collision_count,
            "strict_superset": True,
            "total_raw_cases": 1918,
            "total_full_semantic_payload_ids": len(set(all_full_ids)),
            "total_truncated_semantic_payload_ids": len(set(all_short_ids)),
            "new_A_block_queries": sum(
                len(comparison.block_analyses()) for comparison in fixtures
            ),
            "all_cases_evaluated": True,
        },
        "canonical_colored_graph_support_codes": {
            name: {
                **code,
                "id20": code["sha256"][:20],
            }
            for name, code in graph_support_codes.items()
        },
        "canonical_code_audit": {
            "prior_registered_code_count": 12,
            "new_registered_code_count": 2,
            "registered_code_count": len(graph_support_codes),
            "full_sha256_collision_count": len(graph_full_ids) - len(set(graph_full_ids)),
            "truncated_20hex_collision_count": len(graph_short_ids) - len(set(graph_short_ids)),
            "compact_json_collision_count": len(graph_payloads) - len(set(graph_payloads)),
            "strict_new": True,
            "lift_relabel_invariant": lift_relabelled_code == octahedral_base_code,
            "chart_relabel_invariant": chart_relabelled_code == partitioned_base_code,
            "target_relabel_invariant": target_relabelled_code == partitioned_base_code,
            "support_drift_detected": support_drift_code != partitioned_base_code,
        },
        "relation_graph_invariants": actual_relation_invariants,
        "A_block_expected_h1": h1_expected_tables,
        "A_block_dimension_histograms": h1_dimension_histograms,
        "queries": {
            "prior_sufficiency_or_necessity_break_count": len(
                prior_counterexamples
            ),
            "prior_counterexamples": prior_counterexamples,
            "new_sufficiency_break_count": sum(
                case["sufficiency_break"] for case in expansion
            ),
            "new_necessity_break_count": sum(
                case["necessity_break"] for case in expansion
            ),
            "new_counterexample_count": len(new_counterexamples),
            "new_counterexample_ids": [
                case["semantic_sha256"] for case in new_counterexamples
            ],
        },
        "expansion_cases": expansion,
        "progress_audit": {
            "entry_streak": 1,
            "new_verdicts": new_verdicts,
            "new_canonical_nonisomorphic_counterexamples": (
                new_canonical_counterexamples
            ),
            "candidate_semantic_change": candidate_semantic_change,
            "additional_calibration_fixes": additional_calibration_fixes,
            "progress": progress,
            "streak_after_round": 0 if progress else 2,
        },
        "blocker_id": "PB-R2-NONFREE-GLOBAL-FACE-CHAIN",
        "same_blocker_evidence": {
            "valid_no_progress_2_of_2": not progress,
            "fixed_octahedral_and_partitioned_multichart_cases_close": True,
            "remaining_gap": "No general proof for arbitrary retained nonfree face-chain graphs, certificate colorings, face multiplicities, chart counts, or compatible support distributions.",
        },
        "stop_audit": {
            "stop_condition_A_completion": False,
            "stop_condition_B_finite_exhaustion": False,
            "stop_condition_C_two_valid_same_blocker_no_progress": stop_condition_c,
            "finite_zero_result_is_not_general_proof": True,
            "terminal_reason": (
                "Stop-C: two consecutive post-PUnit valid same-blocker no-progress rounds"
                if stop_condition_c
                else None
            ),
        },
        "coverage_limit": "The exact 1918 semantic cases through the fixed W5, K3,3, octahedral, house, and star graphs, with lift count at most six and no cross-chart nonloop edge or face. Arbitrary graph size, certificate coloring, face multiplicity, chart count, and compatible support distribution remain outside this finite coverage.",
    }


@dataclass(frozen=True, order=True)
class JointCollapsePacket:
    kind: str
    coarse_edge: int
    coarse_face_class: int
    fine_face_classes: tuple[int, ...]
    pivot_assignments: tuple[tuple[int, int], ...]
    orphan_fine_edges: tuple[int, ...]


@dataclass(frozen=True)
class JointCollapseState:
    retained_coarse_edges: tuple[int, ...]
    retained_coarse_face_classes: tuple[int, ...]
    retained_fine_edges: tuple[int, ...]
    retained_fine_face_classes: tuple[int, ...]
    trace: tuple[JointCollapsePacket, ...]

    @property
    def cell_key(
        self,
    ) -> tuple[tuple[int, ...], tuple[int, ...], tuple[int, ...], tuple[int, ...]]:
        return (
            self.retained_coarse_edges,
            self.retained_coarse_face_classes,
            self.retained_fine_edges,
            self.retained_fine_face_classes,
        )


@dataclass(frozen=True)
class JointTerminalH1Calibration:
    state: JointCollapseState
    reduced_morphism: NerveMorphism
    original_analysis: H1Analysis
    reduced_analysis: H1Analysis

    @property
    def preserved(self) -> bool:
        return self.original_analysis == self.reduced_analysis


def _signed_face_coefficient(
    boundary: tuple[int, int, int],
    edge: int,
) -> int:
    return int(boundary[0] == edge) - int(boundary[1] == edge) + int(
        boundary[2] == edge
    )


def _joint_state_from_key(
    key: tuple[tuple[int, ...], tuple[int, ...], tuple[int, ...], tuple[int, ...]],
    trace: tuple[JointCollapsePacket, ...] = (),
) -> JointCollapseState:
    return JointCollapseState(*key, trace)


def _assert_joint_state_closure(
    scope: ScopedComparison,
    coarse_classes: tuple[FaceClass, ...],
    fine_classes: tuple[FaceClass, ...],
    state: JointCollapseState,
) -> None:
    coarse_edges = set(state.retained_coarse_edges)
    coarse_face_classes = set(state.retained_coarse_face_classes)
    fine_edges = set(state.retained_fine_edges)
    fine_face_classes = set(state.retained_fine_face_classes)

    for class_index in coarse_face_classes:
        if not set(coarse_classes[class_index].boundary) <= coarse_edges:
            raise AssertionError("retained coarse face boundary is not closed")
    for class_index in fine_face_classes:
        if not set(fine_classes[class_index].boundary) <= fine_edges:
            raise AssertionError("retained fine face boundary is not closed")

    for edge in fine_edges:
        mapped = scope.morphism.edge_map[edge]
        if mapped is not None and mapped not in coarse_edges:
            raise AssertionError("retained fine edge maps to a removed coarse edge")

    retained_coarse_faces = {
        face
        for class_index in coarse_face_classes
        for face in coarse_classes[class_index].members
    }
    for class_index in fine_face_classes:
        for face in fine_classes[class_index].members:
            mapped = scope.morphism.face_map[face]
            if mapped is not None and mapped not in retained_coarse_faces:
                raise AssertionError(
                    "retained fine face maps to a removed coarse face class"
                )


def _raw_occurrence_classes(
    face_classes: tuple[FaceClass, ...],
    retained_classes: set[int],
    edge: int,
) -> tuple[int, ...]:
    return tuple(
        class_index
        for class_index in sorted(retained_classes)
        if edge in face_classes[class_index].boundary
    )


def _k_preimage_status(
    mapped_faces: tuple[int | None, ...],
    coarse_members: frozenset[int],
) -> str:
    if not any(mapped in coarse_members for mapped in mapped_faces):
        return "unrelated"
    if any(
        mapped is None or mapped not in coarse_members
        for mapped in mapped_faces
    ):
        return "ambiguous"
    return "preimage"


def _injective_pivot_assignments(
    fine_class_indices: tuple[int, ...],
    pivot_options: tuple[tuple[int, ...], ...],
) -> tuple[tuple[tuple[int, int], ...], ...]:
    if len(fine_class_indices) != len(pivot_options):
        raise ValueError("pivot option count does not match K-preimage classes")
    assignments = product(*pivot_options) if pivot_options else ((),)
    return tuple(
        tuple(zip(fine_class_indices, chosen_pivots))
        for chosen_pivots in assignments
        if len(set(chosen_pivots)) == len(chosen_pivots)
    )


def _removable_residual_mapped_edges(
    scope: ScopedComparison,
    fine_classes: tuple[FaceClass, ...],
    retained_fine_classes: set[int],
    retained_fine_edges: set[int],
    coarse_edge: int,
) -> tuple[int, ...] | None:
    residual = tuple(
        edge
        for edge in sorted(retained_fine_edges)
        if scope.morphism.edge_map[edge] == coarse_edge
    )
    if any(
        _raw_occurrence_classes(
            fine_classes,
            retained_fine_classes,
            edge,
        )
        for edge in residual
    ):
        return None
    if any(
        scope.fine.nerve.edges[edge][0]
        == scope.fine.nerve.edges[edge][1]
        or _path_without_edge(
            scope.fine.nerve,
            retained_fine_edges,
            edge,
        )
        for edge in residual
    ):
        return None
    return residual


def _joint_packet_variants(
    scope: ScopedComparison,
    coarse_classes: tuple[FaceClass, ...],
    fine_classes: tuple[FaceClass, ...],
    state: JointCollapseState,
) -> tuple[JointCollapsePacket, ...]:
    _assert_joint_state_closure(scope, coarse_classes, fine_classes, state)
    coarse_edges = set(state.retained_coarse_edges)
    coarse_face_classes = set(state.retained_coarse_face_classes)
    fine_edges = set(state.retained_fine_edges)
    fine_face_classes = set(state.retained_fine_face_classes)
    packets: set[JointCollapsePacket] = set()

    for coarse_class_index in sorted(coarse_face_classes):
        coarse_class = coarse_classes[coarse_class_index]
        for coarse_edge in sorted(coarse_edges):
            if _raw_occurrence_classes(
                coarse_classes,
                coarse_face_classes,
                coarse_edge,
            ) != (coarse_class_index,):
                continue
            if abs(
                _signed_face_coefficient(coarse_class.boundary, coarse_edge)
            ) != 1:
                continue

            preimage_classes: list[int] = []
            ambiguous = False
            coarse_members = set(coarse_class.members)
            for fine_class_index in sorted(fine_face_classes):
                mapped_faces = tuple(
                    scope.morphism.face_map[face]
                    for face in fine_classes[fine_class_index].members
                )
                status = _k_preimage_status(
                    mapped_faces,
                    frozenset(coarse_members),
                )
                if status == "unrelated":
                    continue
                if status == "ambiguous":
                    ambiguous = True
                    break
                preimage_classes.append(fine_class_index)
            if ambiguous:
                continue

            pivot_options: list[tuple[int, ...]] = []
            for fine_class_index in preimage_classes:
                fine_class = fine_classes[fine_class_index]
                options = tuple(
                    fine_edge
                    for fine_edge in sorted(fine_edges)
                    if scope.morphism.edge_map[fine_edge] == coarse_edge
                    and abs(
                        _signed_face_coefficient(
                            fine_class.boundary,
                            fine_edge,
                        )
                    )
                    == 1
                    and _raw_occurrence_classes(
                        fine_classes,
                        fine_face_classes,
                        fine_edge,
                    )
                    == (fine_class_index,)
                )
                if not options:
                    pivot_options = []
                    break
                pivot_options.append(options)
            if preimage_classes and not pivot_options:
                continue

            pivot_assignments = _injective_pivot_assignments(
                tuple(preimage_classes),
                tuple(pivot_options),
            )
            for pivot_pairs in pivot_assignments:
                chosen_pivots = tuple(edge for _, edge in pivot_pairs)
                provisional_classes = fine_face_classes - set(preimage_classes)
                provisional_edges = fine_edges - set(chosen_pivots)
                remaining_mapped_edges = _removable_residual_mapped_edges(
                    scope,
                    fine_classes,
                    provisional_classes,
                    provisional_edges,
                    coarse_edge,
                )
                if remaining_mapped_edges is None:
                    continue
                packets.add(
                    JointCollapsePacket(
                        kind="coarse",
                        coarse_edge=coarse_edge,
                        coarse_face_class=coarse_class_index,
                        fine_face_classes=tuple(preimage_classes),
                        pivot_assignments=pivot_pairs,
                        orphan_fine_edges=remaining_mapped_edges,
                    )
                )

    for fine_class_index in sorted(fine_face_classes):
        fine_class = fine_classes[fine_class_index]
        if not all(
            scope.morphism.face_map[face] is None
            for face in fine_class.members
        ):
            continue
        for fine_edge in sorted(fine_edges):
            if (
                scope.morphism.edge_map[fine_edge] is None
                and abs(
                    _signed_face_coefficient(fine_class.boundary, fine_edge)
                )
                == 1
                and _raw_occurrence_classes(
                    fine_classes,
                    fine_face_classes,
                    fine_edge,
                )
                == (fine_class_index,)
            ):
                packets.add(
                    JointCollapsePacket(
                        kind="fine-only",
                        coarse_edge=-1,
                        coarse_face_class=-1,
                        fine_face_classes=(fine_class_index,),
                        pivot_assignments=((fine_class_index, fine_edge),),
                        orphan_fine_edges=(),
                    )
                )
    return tuple(sorted(packets))


def _apply_joint_packet(
    scope: ScopedComparison,
    coarse_classes: tuple[FaceClass, ...],
    fine_classes: tuple[FaceClass, ...],
    state: JointCollapseState,
    packet: JointCollapsePacket,
) -> JointCollapseState:
    coarse_edges = set(state.retained_coarse_edges)
    coarse_face_classes = set(state.retained_coarse_face_classes)
    fine_edges = set(state.retained_fine_edges)
    fine_face_classes = set(state.retained_fine_face_classes)

    if packet.kind == "coarse":
        coarse_edges.remove(packet.coarse_edge)
        coarse_face_classes.remove(packet.coarse_face_class)
    elif packet.kind != "fine-only":
        raise AssertionError("unknown joint-collapse packet kind")
    fine_face_classes.difference_update(packet.fine_face_classes)
    fine_edges.difference_update(edge for _, edge in packet.pivot_assignments)
    fine_edges.difference_update(packet.orphan_fine_edges)

    result = JointCollapseState(
        retained_coarse_edges=tuple(sorted(coarse_edges)),
        retained_coarse_face_classes=tuple(sorted(coarse_face_classes)),
        retained_fine_edges=tuple(sorted(fine_edges)),
        retained_fine_face_classes=tuple(sorted(fine_face_classes)),
        trace=state.trace + (packet,),
    )
    _assert_joint_state_closure(scope, coarse_classes, fine_classes, result)
    return result


def joint_terminal_states(scope: ScopedComparison) -> tuple[JointCollapseState, ...]:
    coarse_classes = _face_classes(scope.coarse)
    fine_classes = _face_classes(scope.fine)
    initial = JointCollapseState(
        retained_coarse_edges=tuple(range(len(scope.coarse.nerve.edges))),
        retained_coarse_face_classes=tuple(range(len(coarse_classes))),
        retained_fine_edges=tuple(range(len(scope.fine.nerve.edges))),
        retained_fine_face_classes=tuple(range(len(fine_classes))),
        trace=(),
    )
    _assert_joint_state_closure(scope, coarse_classes, fine_classes, initial)
    memo: dict[
        tuple[tuple[int, ...], tuple[int, ...], tuple[int, ...], tuple[int, ...]],
        dict[
            tuple[
                tuple[int, ...],
                tuple[int, ...],
                tuple[int, ...],
                tuple[int, ...],
            ],
            tuple[JointCollapsePacket, ...],
        ],
    ] = {}

    def solve(
        key: tuple[
            tuple[int, ...],
            tuple[int, ...],
            tuple[int, ...],
            tuple[int, ...],
        ],
    ) -> dict[
        tuple[tuple[int, ...], tuple[int, ...], tuple[int, ...], tuple[int, ...]],
        tuple[JointCollapsePacket, ...],
    ]:
        if key in memo:
            return memo[key]
        current = _joint_state_from_key(key)
        packets = _joint_packet_variants(
            scope,
            coarse_classes,
            fine_classes,
            current,
        )
        if not packets:
            memo[key] = {key: ()}
            return memo[key]

        terminals: dict[
            tuple[
                tuple[int, ...],
                tuple[int, ...],
                tuple[int, ...],
                tuple[int, ...],
            ],
            tuple[JointCollapsePacket, ...],
        ] = {}
        for packet in packets:
            next_state = _apply_joint_packet(
                scope,
                coarse_classes,
                fine_classes,
                current,
                packet,
            )
            for terminal_key, suffix in solve(next_state.cell_key).items():
                trace = (packet,) + suffix
                previous = terminals.get(terminal_key)
                if previous is None or trace < previous:
                    terminals[terminal_key] = trace
        memo[key] = terminals
        return terminals

    solved = solve(initial.cell_key)
    terminals = tuple(
        _joint_state_from_key(key, trace)
        for key, trace in sorted(solved.items())
    )
    if not terminals:
        raise AssertionError("joint collapse produced no irreducible terminal")
    for terminal in terminals:
        _assert_joint_state_closure(
            scope,
            coarse_classes,
            fine_classes,
            terminal,
        )
        if _joint_packet_variants(
            scope,
            coarse_classes,
            fine_classes,
            terminal,
        ):
            raise AssertionError("joint collapse returned a reducible terminal")
    return terminals


def _joint_reduced_side(
    side: SideData,
    face_classes: tuple[FaceClass, ...],
    retained_edges: tuple[int, ...],
    retained_face_classes: tuple[int, ...],
) -> ReducedSide:
    retained_edge_set = set(retained_edges)
    critical_edges = tuple(
        edge
        for edge in retained_edges
        if _path_without_edge(side.nerve, retained_edge_set, edge)
    )
    critical_vertices = {
        vertex
        for edge in critical_edges
        for vertex in side.nerve.edges[edge]
    }
    for class_index in retained_face_classes:
        for edge in face_classes[class_index].boundary:
            if edge not in retained_edge_set:
                raise AssertionError("terminal retained face lost a boundary edge")
            critical_vertices.update(side.nerve.edges[edge])
    return ReducedSide(
        data=side,
        face_classes=face_classes,
        retained_face_classes=retained_face_classes,
        retained_edges=retained_edges,
        critical_edges=critical_edges,
        critical_vertices=tuple(sorted(critical_vertices)),
        removed_free_pairs=(),
    )


def _joint_terminal_reductions(
    scope: ScopedComparison,
) -> tuple[tuple[JointCollapseState, ReducedSide, ReducedSide], ...]:
    coarse_classes = _face_classes(scope.coarse)
    fine_classes = _face_classes(scope.fine)
    result = []
    for state in joint_terminal_states(scope):
        result.append(
            (
                state,
                _joint_reduced_side(
                    scope.coarse,
                    coarse_classes,
                    state.retained_coarse_edges,
                    state.retained_coarse_face_classes,
                ),
                _joint_reduced_side(
                    scope.fine,
                    fine_classes,
                    state.retained_fine_edges,
                    state.retained_fine_face_classes,
                ),
            )
        )
    return tuple(result)


def _retained_actual_face_members(
    face_classes: tuple[FaceClass, ...],
    retained_face_classes: tuple[int, ...],
) -> tuple[int, ...]:
    return tuple(
        sorted(
            face
            for class_index in retained_face_classes
            for face in face_classes[class_index].members
        )
    )


def _joint_reduced_morphism(
    scope: ScopedComparison,
    state: JointCollapseState,
) -> NerveMorphism:
    coarse_classes = _face_classes(scope.coarse)
    fine_classes = _face_classes(scope.fine)
    _assert_joint_state_closure(scope, coarse_classes, fine_classes, state)

    coarse_edges = state.retained_coarse_edges
    fine_edges = state.retained_fine_edges
    coarse_faces = _retained_actual_face_members(
        coarse_classes,
        state.retained_coarse_face_classes,
    )
    fine_faces = _retained_actual_face_members(
        fine_classes,
        state.retained_fine_face_classes,
    )
    coarse_edge_index = {
        edge: index for index, edge in enumerate(coarse_edges)
    }
    fine_edge_index = {
        edge: index for index, edge in enumerate(fine_edges)
    }
    coarse_face_index = {
        face: index for index, face in enumerate(coarse_faces)
    }

    coarse_nerve = Nerve(
        scope.coarse.nerve.vertices,
        tuple(scope.coarse.nerve.edges[edge] for edge in coarse_edges),
        tuple(
            tuple(
                coarse_edge_index[edge]
                for edge in scope.coarse.nerve.faces[face]
            )
            for face in coarse_faces
        ),
    )
    fine_nerve = Nerve(
        scope.fine.nerve.vertices,
        tuple(scope.fine.nerve.edges[edge] for edge in fine_edges),
        tuple(
            tuple(
                fine_edge_index[edge]
                for edge in scope.fine.nerve.faces[face]
            )
            for face in fine_faces
        ),
    )
    reduced = NerveMorphism(
        coarse=coarse_nerve,
        fine=fine_nerve,
        vertex_map=scope.morphism.vertex_map,
        edge_map=tuple(
            None
            if scope.morphism.edge_map[edge] is None
            else coarse_edge_index[scope.morphism.edge_map[edge]]
            for edge in fine_edges
        ),
        face_map=tuple(
            None
            if scope.morphism.face_map[face] is None
            else coarse_face_index[scope.morphism.face_map[face]]
            for face in fine_faces
        ),
    )
    return reduced


def joint_terminal_h1_calibration(
    scope: ScopedComparison,
) -> tuple[JointTerminalH1Calibration, ...]:
    original_analysis = analyze_h1(scope.morphism, Matrix.identity(1))
    rows = []
    for state in joint_terminal_states(scope):
        reduced_morphism = _joint_reduced_morphism(scope, state)
        rows.append(
            JointTerminalH1Calibration(
                state=state,
                reduced_morphism=reduced_morphism,
                original_analysis=original_analysis,
                reduced_analysis=analyze_h1(
                    reduced_morphism,
                    Matrix.identity(1),
                ),
            )
        )
    return tuple(rows)


def _joint_packet_summary(packet: JointCollapsePacket) -> dict[str, object]:
    return {
        "kind": packet.kind,
        "coarse_edge": (
            packet.coarse_edge if packet.coarse_edge >= 0 else None
        ),
        "coarse_face_class": (
            packet.coarse_face_class
            if packet.coarse_face_class >= 0
            else None
        ),
        "fine_face_classes": list(packet.fine_face_classes),
        "pivot_assignments": [
            [face_class, edge]
            for face_class, edge in packet.pivot_assignments
        ],
        "orphan_fine_edges": list(packet.orphan_fine_edges),
    }


def _joint_terminal_summary(
    state: JointCollapseState,
    coarse: ReducedSide,
    fine: ReducedSide,
    conditions: dict[str, bool],
    direct_lifttwin: dict[str, object] | None = None,
    guarded_coarse_edges: tuple[int, ...] | None = None,
) -> dict[str, object]:
    result: dict[str, object] = {
        "conditions": conditions,
        "trace": [_joint_packet_summary(packet) for packet in state.trace],
        "coarse_reduction": _reduction_summary(coarse),
        "fine_reduction": _reduction_summary(fine),
        "retained_map_closure": True,
    }
    if direct_lifttwin is not None:
        result["direct_lifttwin"] = direct_lifttwin
    if guarded_coarse_edges is not None:
        result["C5_C6_guarded_coarse_edges"] = list(
            guarded_coarse_edges
        )
    return result


def support_active_v3_candidate_evaluation(
    comparison: UniformComparison,
) -> dict[str, object]:
    whole_targets = frozenset(range(comparison.coarse_target_count))
    whole = _a_scope(comparison, whole_targets)
    coarse_whole = reduce_side(whole.coarse)
    fine_whole = reduce_side(whole.fine)
    c0 = _c0(whole, coarse_whole, fine_whole, comparison.factor_pi)
    c5, c6, twin_details = _c5_c6(
        whole,
        coarse_whole,
        fine_whole,
        c5_mode="certified",
    )

    aggregate = {
        "C0*": c0,
        "C1*": True,
        "C2*": True,
        "C3*": True,
        "C4*": True,
        "C5*": c5,
        "C6*": c6,
    }
    per_subset = []
    for targets in nonempty_subsets(comparison.coarse_target_count):
        scope = _a_scope(comparison, targets)
        coarse = reduce_side(scope.coarse)
        fine = reduce_side(scope.fine)
        relative = {
            "C1*": _c1(scope, coarse, fine),
            "C2*": _c2(scope, coarse, fine),
            "C3*": _c3(scope, fine),
            "C4*": _c4(scope, coarse, fine),
        }
        for clause, value in relative.items():
            aggregate[clause] = aggregate[clause] and value
        per_subset.append(
            {
                "coarse_targets_A": sorted(targets),
                "conditions": relative,
                "coarse_reduction": _reduction_summary(coarse),
                "fine_reduction": _reduction_summary(fine),
            }
        )
    return {
        "aggregate": aggregate,
        "all": all(aggregate.values()),
        "whole": {
            "conditions": {"C0*": c0, "C5*": c5, "C6*": c6},
            "coarse_reduction": _reduction_summary(coarse_whole),
            "fine_reduction": _reduction_summary(fine_whole),
            "direct_lifttwin": twin_details,
        },
        "per_subset": per_subset,
    }


def _v4_c5_c6(
    scope: ScopedComparison,
    coarse: ReducedSide,
    fine: ReducedSide,
) -> tuple[bool, bool, dict[str, object], tuple[int, ...]]:
    mapped_fine_critical_edges = {
        scope.morphism.edge_map[fine_edge]
        for fine_edge in fine.critical_edges
        if scope.morphism.edge_map[fine_edge] is not None
    }
    guarded_coarse_edges = tuple(
        sorted(
            set(coarse.critical_edges)
            | mapped_fine_critical_edges
        )
    )
    guarded_coarse = ReducedSide(
        data=coarse.data,
        face_classes=coarse.face_classes,
        retained_face_classes=coarse.retained_face_classes,
        retained_edges=coarse.retained_edges,
        critical_edges=guarded_coarse_edges,
        critical_vertices=coarse.critical_vertices,
        removed_free_pairs=coarse.removed_free_pairs,
    )
    c5, c6, details = _c5_c6(
        scope,
        guarded_coarse,
        fine,
        c5_mode="certified",
    )
    return c5, c6, details, guarded_coarse_edges


def v4_candidate_evaluation(
    comparison: UniformComparison,
    *,
    include_terminal_details: bool = True,
) -> dict[str, object]:
    whole_targets = frozenset(range(comparison.coarse_target_count))
    whole = _a_scope(comparison, whole_targets)
    whole_reductions = _joint_terminal_reductions(whole)
    whole_conditions: list[dict[str, bool]] = []
    whole_details: list[dict[str, object]] = []
    for state, coarse, fine in whole_reductions:
        c0 = _c0(whole, coarse, fine, comparison.factor_pi)
        c5, c6, twin_details, guarded_coarse_edges = _v4_c5_c6(
            whole,
            coarse,
            fine,
        )
        conditions = {"C0*": c0, "C5*": c5, "C6*": c6}
        whole_conditions.append(conditions)
        if include_terminal_details:
            whole_details.append(
                _joint_terminal_summary(
                    state,
                    coarse,
                    fine,
                    conditions,
                    twin_details,
                    guarded_coarse_edges,
                )
            )

    aggregate = {
        clause: all(conditions[clause] for conditions in whole_conditions)
        for clause in ("C0*", "C5*", "C6*")
    }
    aggregate.update(
        {"C1*": True, "C2*": True, "C3*": True, "C4*": True}
    )
    per_subset: list[dict[str, object]] = []
    for targets in nonempty_subsets(comparison.coarse_target_count):
        scope = _a_scope(comparison, targets)
        reductions = _joint_terminal_reductions(scope)
        terminal_conditions: list[dict[str, bool]] = []
        terminal_details: list[dict[str, object]] = []
        for state, coarse, fine in reductions:
            conditions = {
                "C1*": _c1(scope, coarse, fine),
                "C2*": _c2(scope, coarse, fine),
                "C3*": _c3(scope, fine),
                "C4*": _c4(scope, coarse, fine),
            }
            terminal_conditions.append(conditions)
            if include_terminal_details:
                terminal_details.append(
                    _joint_terminal_summary(
                        state,
                        coarse,
                        fine,
                        conditions,
                    )
                )
        universal = {
            clause: all(
                conditions[clause]
                for conditions in terminal_conditions
            )
            for clause in ("C1*", "C2*", "C3*", "C4*")
        }
        for clause, value in universal.items():
            aggregate[clause] = aggregate[clause] and value
        subset_result: dict[str, object] = {
            "coarse_targets_A": sorted(targets),
            "terminal_count": len(reductions),
            "conditions": universal,
        }
        if include_terminal_details:
            subset_result["terminals"] = terminal_details
        per_subset.append(subset_result)

    ordered_aggregate = {
        f"C{index}*": aggregate[f"C{index}*"]
        for index in range(7)
    }
    whole_result: dict[str, object] = {
        "terminal_count": len(whole_reductions),
        "conditions": {
            clause: ordered_aggregate[clause]
            for clause in ("C0*", "C5*", "C6*")
        },
    }
    if include_terminal_details:
        whole_result["terminals"] = whole_details
    return {
        "semantic_id": V4_SEMANTIC_ID,
        "semantic_sha256": V4_SEMANTIC_SHA256,
        "aggregate": ordered_aggregate,
        "all": all(ordered_aggregate.values()),
        "whole": whole_result,
        "per_subset": per_subset,
        "terminal_quantifier": "forall",
    }


def contractible_triangle_fixture() -> UniformComparison:
    nerve = Nerve(
        4,
        ((0, 0), (1, 2), (1, 3), (2, 3)),
        ((1, 2, 3),),
    )
    return UniformComparison(
        name="CONTRACTIBLE-TRIANGLE",
        morphism=NerveMorphism(
            nerve,
            nerve,
            (0, 1, 2, 3),
            (0, 1, 2, 3),
            (0,),
        ),
        coarse_target_count=2,
        fine_target_count=3,
        factor_pi=(0, 0, 1),
        coarse_chart_supports=(
            frozenset((0,)),
            frozenset((0, 1)),
            frozenset((0, 1)),
            frozenset((0, 1)),
        ),
        fine_chart_supports=(
            frozenset((0, 1)),
            frozenset((2,)),
            frozenset((2,)),
            frozenset((2,)),
        ),
    )


def orphan_loop_fixture() -> UniformComparison:
    coarse = Nerve(
        1,
        ((0, 0), (0, 0), (0, 0)),
        ((0, 1, 2),),
    )
    fine = Nerve(
        1,
        ((0, 0), (0, 0), (0, 0), (0, 0)),
        ((0, 1, 2),),
    )
    unit = (frozenset((0,)),)
    return UniformComparison(
        name="ORPHAN-LOOP",
        morphism=NerveMorphism(
            coarse,
            fine,
            (0,),
            (0, 1, 2, 0),
            (0,),
        ),
        coarse_target_count=1,
        fine_target_count=1,
        factor_pi=(0,),
        coarse_chart_supports=unit,
        fine_chart_supports=unit,
    )


def bridge_kill_neutral_fixture() -> UniformComparison:
    coarse = Nerve(
        2,
        ((0, 1), (1, 1), (0, 0)),
        ((0, 0, 1), (1, 1, 1)),
    )
    fine = Nerve(
        2,
        ((0, 1), (0, 1), (1, 1), (0, 0)),
        ((0, 1, 2), (2, 2, 2)),
    )
    full = (frozenset((0,)), frozenset((0,)))
    return UniformComparison(
        name="BRIDGE-KILL-NEUTRAL",
        morphism=NerveMorphism(
            coarse,
            fine,
            (0, 1),
            (0, 0, 1, 2),
            (0, 1),
        ),
        coarse_target_count=1,
        fine_target_count=1,
        factor_pi=(0,),
        coarse_chart_supports=full,
        fine_chart_supports=full,
    )


def _required_catalog_v4() -> tuple[UniformComparison, ...]:
    return (
        *_required_catalog(),
        contractible_triangle_fixture(),
        orphan_loop_fixture(),
        bridge_kill_neutral_fixture(),
    )


def _analysis_rows(
    comparison: UniformComparison,
) -> list[dict[str, object]]:
    return [
        {
            "coarse_targets_A": sorted(targets),
            "h1": asdict(analysis),
        }
        for targets, analysis in comparison.block_analyses()
    ]


def _bounded_normalization_calibration(
    comparisons: tuple[UniformComparison, ...],
) -> dict[str, object]:
    scope_evaluations = 0
    terminal_comparisons = 0
    mismatches: list[dict[str, object]] = []
    for comparison in comparisons:
        full_targets = frozenset(range(comparison.coarse_target_count))
        scopes = (
            (("whole-full-A", full_targets),)
            + tuple(
                ("nonempty-A", targets)
                for targets in nonempty_subsets(
                    comparison.coarse_target_count
                )
            )
        )
        for scope_kind, targets in scopes:
            scope_evaluations += 1
            rows = joint_terminal_h1_calibration(
                _a_scope(comparison, targets)
            )
            terminal_comparisons += len(rows)
            for terminal_index, row in enumerate(rows):
                if row.preserved:
                    continue
                mismatches.append(
                    {
                        "id": _case_semantic_sha256(comparison),
                        "name": comparison.name,
                        "scope_kind": scope_kind,
                        "coarse_targets_A": sorted(targets),
                        "terminal_index": terminal_index,
                        "original_h1": asdict(row.original_analysis),
                        "reduced_h1": asdict(row.reduced_analysis),
                    }
                )
    return {
        "case_count": len(comparisons),
        "scope_evaluations": scope_evaluations,
        "terminal_comparisons": terminal_comparisons,
        "whole_full_A_duplicate_scope_count": len(comparisons),
        "whole_full_A_is_also_in_nonempty_A": True,
        "mismatch_count": len(mismatches),
        "mismatches": mismatches,
        "all_terminal_analyses_preserved": not mismatches,
        "bounded_normalization_calibration_only": True,
        "general_preservation_theorem": False,
    }


def v4_calibration_report() -> dict[str, object]:
    contractible = contractible_triangle_fixture()
    expected_contractible_h1 = (
        (
            frozenset((0,)),
            H1Analysis(1, 1, 1, True, True, True),
        ),
        (
            frozenset((1,)),
            H1Analysis(0, 0, 0, True, True, True),
        ),
        (
            frozenset((0, 1)),
            H1Analysis(1, 1, 1, True, True, True),
        ),
    )
    contractible_h1 = contractible.block_analyses()
    v3_contractible = support_active_v3_candidate_evaluation(contractible)
    v4_contractible = v4_candidate_evaluation(
        contractible,
        include_terminal_details=True,
    )
    expected_v3_contractible = {
        "C0*": False,
        "C1*": False,
        "C2*": False,
        "C3*": True,
        "C4*": False,
        "C5*": True,
        "C6*": True,
    }
    expected_v4_true = {f"C{index}*": True for index in range(7)}
    if not (
        contractible_h1 == expected_contractible_h1
        and all(analysis.isomorphism for _, analysis in contractible_h1)
        and v3_contractible["aggregate"] == expected_v3_contractible
        and v4_contractible["aggregate"] == expected_v4_true
        and v4_contractible["all"]
    ):
        raise AssertionError("v4 contractible-triangle calibration mismatch")

    orphan = orphan_loop_fixture()
    expected_orphan_h1 = (
        (
            frozenset((0,)),
            H1Analysis(2, 3, 2, True, False, False),
        ),
    )
    orphan_h1 = orphan.block_analyses()
    v4_orphan = v4_candidate_evaluation(
        orphan,
        include_terminal_details=True,
    )
    if not (
        orphan_h1 == expected_orphan_h1
        and not v4_orphan["aggregate"]["C5*"]
        and not v4_orphan["all"]
    ):
        raise AssertionError("v4 ORPHAN-LOOP calibration mismatch")

    chain = chain3_fixture()
    unkilled = unkilled_twin_fixture()
    chain_v1 = candidate_evaluation(chain, c5_mode="clique")
    chain_v3 = candidate_evaluation(chain, c5_mode="certified")
    unkilled_v2 = candidate_evaluation(unkilled, c5_mode="component")
    unkilled_v3 = candidate_evaluation(unkilled, c5_mode="certified")
    chain_v4 = v4_candidate_evaluation(chain, include_terminal_details=False)
    unkilled_v4 = v4_candidate_evaluation(
        unkilled,
        include_terminal_details=False,
    )
    if not (
        chain.is_uniform()
        and not chain_v1["aggregate"]["C5*"]
        and chain_v3["all"]
        and chain_v4["all"]
        and not unkilled.is_uniform()
        and unkilled_v2["all"]
        and not unkilled_v3["aggregate"]["C5*"]
        and not unkilled_v4["aggregate"]["C5*"]
        and not unkilled_v4["all"]
    ):
        raise AssertionError("v1-v4 registered counterexample calibration drift")

    edge_fiber = next(
        comparison
        for comparison in _required_catalog()
        if comparison.name == "EdgeFiberObstruction"
    )
    edge_fiber_v4 = v4_candidate_evaluation(
        edge_fiber,
        include_terminal_details=True,
    )
    if not (
        not edge_fiber.is_uniform()
        and not edge_fiber_v4["aggregate"]["C5*"]
        and not edge_fiber_v4["all"]
    ):
        raise AssertionError("v4 EdgeFiber guarded-C5 regression mismatch")

    bridge_kill = bridge_kill_neutral_fixture()
    expected_bridge_h1 = (
        (
            frozenset((0,)),
            H1Analysis(1, 1, 1, True, True, True),
        ),
    )
    bridge_scope = _a_scope(bridge_kill, frozenset((0,)))
    bridge_reductions = _joint_terminal_reductions(bridge_scope)
    bridge_v4 = v4_candidate_evaluation(
        bridge_kill,
        include_terminal_details=True,
    )
    bridge_terminal = bridge_v4["whole"]["terminals"][0]
    if not (
        bridge_kill.block_analyses() == expected_bridge_h1
        and len(bridge_reductions) == 1
        and bridge_reductions[0][0].trace == ()
        and bridge_reductions[0][1].critical_edges == (1, 2)
        and bridge_reductions[0][2].critical_edges == (0, 1, 2, 3)
        and bridge_terminal["C5_C6_guarded_coarse_edges"] == [0, 1, 2]
        and bridge_terminal["direct_lifttwin"]["0"]["direct_edges"]
        == [[0, 1]]
        and bridge_v4["all"]
    ):
        raise AssertionError("v4 BRIDGE-KILL-NEUTRAL calibration mismatch")

    if not (
        len(_required_catalog()) == 13
        and len(_required_catalog_v4()) == 16
    ):
        raise AssertionError("v4 required fixture catalog membership drift")
    required_mismatches: list[str] = []
    required_rows: list[dict[str, object]] = []
    for comparison in _required_catalog_v4():
        uniform = comparison.is_uniform()
        candidate = v4_candidate_evaluation(
            comparison,
            include_terminal_details=False,
        )
        if uniform != candidate["all"]:
            required_mismatches.append(_case_semantic_sha256(comparison))
        required_rows.append(
            {
                "id": _case_id(comparison),
                "name": comparison.name,
                "uniform": uniform,
                "candidate_all": candidate["all"],
            }
        )
    if required_mismatches:
        raise AssertionError("v4 required fixture catalog calibration mismatch")

    prior_comparisons = (
        tuple(_all_comparisons_through_round11())
        + round12_relation_fixtures()
    )
    full_ids = tuple(
        _case_semantic_sha256(comparison)
        for comparison in prior_comparisons
    )
    short_ids = tuple(identifier[:20] for identifier in full_ids)
    if not (
        len(prior_comparisons) == 1918
        and len(set(full_ids)) == 1918
        and len(set(short_ids)) == 1918
    ):
        raise AssertionError("v4 prior-1918 name-free population drift")

    uniform_not_candidate: list[str] = []
    candidate_not_uniform: list[str] = []
    for identifier, comparison in zip(full_ids, prior_comparisons):
        uniform = comparison.is_uniform()
        candidate_all = v4_candidate_evaluation(
            comparison,
            include_terminal_details=False,
        )["all"]
        if uniform and not candidate_all:
            uniform_not_candidate.append(identifier)
        if candidate_all and not uniform:
            candidate_not_uniform.append(identifier)
    if uniform_not_candidate or candidate_not_uniform:
        raise AssertionError("v4 prior-1918 two-way calibration mismatch")

    required_normalization = _bounded_normalization_calibration(
        _required_catalog_v4()
    )
    prior_normalization = _bounded_normalization_calibration(
        prior_comparisons
    )
    if not (
        required_normalization["mismatch_count"] == 0
        and prior_normalization["mismatch_count"] == 0
    ):
        raise AssertionError(
            "v4 bounded terminal normalization changed exact H1 analysis"
        )

    return {
        "calibration": "R2-v4-candidate-calibration",
        "human_adjudication_issue_comment": (
            V4_HUMAN_ADJUDICATION_ISSUE_COMMENT
        ),
        "candidate": {
            "semantic_id": V4_SEMANTIC_ID,
            "semantic_sha256": V4_SEMANTIC_SHA256,
            "spec": V4_SPEC,
        },
        "contractible_triangle": {
            "h1_blocks": _analysis_rows(contractible),
            "exact_uniform": True,
            "support_active_v3_aggregate": v3_contractible["aggregate"],
            "v4_candidate": v4_contractible,
        },
        "orphan_loop": {
            "h1_blocks": _analysis_rows(orphan),
            "v4_candidate": v4_orphan,
            "C5_false": True,
        },
        "edge_fiber_guarded_C5_regression": {
            "id": _case_id(edge_fiber),
            "uniform": False,
            "v4_candidate": edge_fiber_v4,
            "C5_false": True,
        },
        "bridge_kill_neutral": {
            "h1_blocks": _analysis_rows(bridge_kill),
            "terminal_count": len(bridge_reductions),
            "coarse_critical_edges": list(
                bridge_reductions[0][1].critical_edges
            ),
            "fine_critical_edges": list(
                bridge_reductions[0][2].critical_edges
            ),
            "v4_candidate": bridge_v4,
        },
        "registered_counterexamples": {
            "chain3_v1_C5": chain_v1["aggregate"]["C5*"],
            "chain3_v3_all": chain_v3["all"],
            "chain3_v4_all": chain_v4["all"],
            "unkilled_v2_all": unkilled_v2["all"],
            "unkilled_v3_C5": unkilled_v3["aggregate"]["C5*"],
            "unkilled_v4_C5": unkilled_v4["aggregate"]["C5*"],
        },
        "required_catalog": {
            "legacy_count": len(_required_catalog()),
            "v4_count": len(_required_catalog_v4()),
            "mismatch_count": 0,
            "cases": required_rows,
        },
        "prior_population": {
            "raw_cases": len(prior_comparisons),
            "unique_full_name_free_ids": len(set(full_ids)),
            "unique_truncated_20hex_ids": len(set(short_ids)),
            "uniform_and_not_candidate_count": len(uniform_not_candidate),
            "candidate_and_nonuniform_count": len(candidate_not_uniform),
            "all_cases_evaluated": True,
        },
        "terminal_h1_normalization_calibration": {
            "statement": (
                "Bounded exact calibration on the listed finite fixtures; "
                "this is not a general normalization-preservation theorem."
            ),
            "required_catalog_16": required_normalization,
            "prior_population_1918": prior_normalization,
        },
        "is_round_report": False,
        "query_generator_added": False,
    }


def _round13_support_mask(
    support: frozenset[int],
    target_count: int,
) -> str:
    return "".join(
        "1" if target in support else "0"
        for target in range(target_count)
    )


def round13_bound_fixture(
    *,
    face_present: bool,
    coarse_anchor_support: frozenset[int],
    coarse_triangle_support: frozenset[int],
    fine_anchor_support: frozenset[int],
    fine_triangle_support: frozenset[int],
) -> UniformComparison:
    edges = ((0, 0), (1, 2), (1, 3), (2, 3))
    faces = ((1, 2, 3),) if face_present else ()
    nerve = Nerve(4, edges, faces)
    name = ":".join(
        (
            "R13-CROSS-CHART-TRIANGLE-SUPPORT",
            f"face={int(face_present)}",
            f"S0={_round13_support_mask(coarse_anchor_support, 2)}",
            f"ST={_round13_support_mask(coarse_triangle_support, 2)}",
            f"T0={_round13_support_mask(fine_anchor_support, 3)}",
            f"TT={_round13_support_mask(fine_triangle_support, 3)}",
        )
    )
    return UniformComparison(
        name=name,
        morphism=NerveMorphism(
            nerve,
            nerve,
            (0, 1, 2, 3),
            (0, 1, 2, 3),
            (0,) if face_present else (),
        ),
        coarse_target_count=2,
        fine_target_count=3,
        factor_pi=(0, 0, 1),
        coarse_chart_supports=(
            coarse_anchor_support,
            coarse_triangle_support,
            coarse_triangle_support,
            coarse_triangle_support,
        ),
        fine_chart_supports=(
            fine_anchor_support,
            fine_triangle_support,
            fine_triangle_support,
            fine_triangle_support,
        ),
    )


def round13_bound_comparisons() -> tuple[UniformComparison, ...]:
    coarse_supports = nonempty_subsets(2)
    fine_supports = nonempty_subsets(3)
    comparisons = []
    for face_present in (False, True):
        for coarse_anchor_support in coarse_supports:
            for coarse_triangle_support in coarse_supports:
                for fine_anchor_support in fine_supports:
                    if not {
                        (0, 0, 1)[target]
                        for target in fine_anchor_support
                    } <= set(coarse_anchor_support):
                        continue
                    for fine_triangle_support in fine_supports:
                        if not {
                            (0, 0, 1)[target]
                            for target in fine_triangle_support
                        } <= set(coarse_triangle_support):
                            continue
                        comparisons.append(
                            round13_bound_fixture(
                                face_present=face_present,
                                coarse_anchor_support=coarse_anchor_support,
                                coarse_triangle_support=coarse_triangle_support,
                                fine_anchor_support=fine_anchor_support,
                                fine_triangle_support=fine_triangle_support,
                            )
                        )
    return tuple(comparisons)


def _round13_swap_fine_support(
    support: frozenset[int],
) -> frozenset[int]:
    return frozenset(
        1 if target == 0 else 0 if target == 1 else target
        for target in support
    )


def round13_bound_canonical_support_incidence_code(
    comparison: UniformComparison,
) -> dict[str, str]:
    expected_edges = ((0, 0), (1, 2), (1, 3), (2, 3))
    expected_faces = {(), ((1, 2, 3),)}
    coarse_supports = comparison.coarse_chart_supports
    fine_supports = comparison.fine_chart_supports
    if not (
        comparison.morphism.coarse == comparison.morphism.fine
        and comparison.morphism.coarse.vertices == 4
        and comparison.morphism.coarse.edges == expected_edges
        and comparison.morphism.coarse.faces in expected_faces
        and comparison.morphism.vertex_map == (0, 1, 2, 3)
        and comparison.morphism.edge_map == (0, 1, 2, 3)
        and comparison.morphism.face_map
        == ((0,) if comparison.morphism.coarse.faces else ())
        and comparison.coarse_target_count == 2
        and comparison.fine_target_count == 3
        and comparison.factor_pi == (0, 0, 1)
        and len(coarse_supports) == len(fine_supports) == 4
        and coarse_supports[1:] == (coarse_supports[1],) * 3
        and fine_supports[1:] == (fine_supports[1],) * 3
    ):
        raise ValueError("comparison is outside the fixed Round13 grammar")

    payloads = []
    for swap in (False, True):
        transformed_fine = tuple(
            _round13_swap_fine_support(support)
            if swap
            else support
            for support in fine_supports
        )
        payload = {
            "coarse_target_count": 2,
            "fine_target_count": 3,
            "factor_pi": [0, 0, 1],
            "vertices": 4,
            "edges": [list(edge) for edge in expected_edges],
            "faces": [
                list(face)
                for face in comparison.morphism.coarse.faces
            ],
            "coarse_chart_supports": [
                sorted(support) for support in coarse_supports
            ],
            "fine_chart_supports": [
                sorted(support) for support in transformed_fine
            ],
        }
        payloads.append(
            json.dumps(payload, sort_keys=True, separators=(",", ":"))
        )
    compact_json = min(payloads)
    digest = sha256(compact_json.encode("ascii")).hexdigest()
    return {
        "compact_json": compact_json,
        "sha256": digest,
        "id20": digest[:20],
    }


def _round13_pure_catalog_manifest() -> dict[str, object]:
    rows = []
    for comparison in _required_catalog_v4():
        summary = comparison.summary()
        summary_json = json.dumps(
            summary,
            sort_keys=True,
            separators=(",", ":"),
        )
        semantic_sha256 = _case_semantic_sha256(comparison)
        rows.append(
            {
                "name": comparison.name,
                "summary": summary,
                "summary_sha256": sha256(
                    summary_json.encode("utf-8")
                ).hexdigest(),
                "name_free_semantic_sha256": semantic_sha256,
                "name_free_id20": semantic_sha256[:20],
            }
        )
    compact_json = json.dumps(rows, sort_keys=True, separators=(",", ":"))
    return {
        "count": len(rows),
        "cases": rows,
        "compact_sha256": sha256(compact_json.encode("utf-8")).hexdigest(),
    }


def round13_preregistration_manifest() -> dict[str, object]:
    coarse_supports = nonempty_subsets(2)
    fine_supports = nonempty_subsets(3)
    raw_count = 2 * len(coarse_supports) ** 2 * len(fine_supports) ** 2
    single_position_pairs = tuple(
        (coarse_support, fine_support)
        for coarse_support in coarse_supports
        for fine_support in fine_supports
        if {
            (0, 0, 1)[target]
            for target in fine_support
        }
        <= set(coarse_support)
    )
    fixed_single_position_pairs = tuple(
        pair
        for pair in single_position_pairs
        if _round13_swap_fine_support(pair[1]) == pair[1]
    )
    comparisons = round13_bound_comparisons()
    if not (
        raw_count == 882
        and len(single_position_pairs) == 11
        and len(fixed_single_position_pairs) == 5
        and len(comparisons) == 242
    ):
        raise AssertionError("Round13 pure support bound count drift")

    semantic_payloads = tuple(
        _case_semantic_payload_json(comparison)
        for comparison in comparisons
    )
    semantic_ids = tuple(
        sha256(payload.encode("utf-8")).hexdigest()
        for payload in semantic_payloads
    )
    semantic_id20 = tuple(identifier[:20] for identifier in semantic_ids)
    canonical_codes = tuple(
        round13_bound_canonical_support_incidence_code(comparison)
        for comparison in comparisons
    )
    canonical_payloads = tuple(
        code["compact_json"] for code in canonical_codes
    )
    canonical_ids = tuple(code["sha256"] for code in canonical_codes)
    canonical_id20 = tuple(code["id20"] for code in canonical_codes)
    if not (
        len(set(semantic_payloads)) == 242
        and len(set(semantic_ids)) == 242
        and len(set(semantic_id20)) == 242
        and len(set(canonical_payloads)) == 146
        and len(set(canonical_ids)) == 146
        and len(set(canonical_id20)) == 146
        and (
            (
                len(single_position_pairs) ** 2
                + len(fixed_single_position_pairs) ** 2
            )
            // 2
        )
        * 2
        == 146
    ):
        raise AssertionError("Round13 semantic or canonical orbit count drift")

    support_face_flags: dict[
        tuple[
            tuple[int, ...],
            tuple[int, ...],
            tuple[int, ...],
            tuple[int, ...],
        ],
        set[bool],
    ] = {}
    case_rows = []
    for comparison, semantic_id, canonical_code in zip(
        comparisons,
        semantic_ids,
        canonical_codes,
    ):
        face_present = bool(comparison.morphism.coarse.faces)
        support_key = (
            tuple(sorted(comparison.coarse_chart_supports[0])),
            tuple(sorted(comparison.coarse_chart_supports[1])),
            tuple(sorted(comparison.fine_chart_supports[0])),
            tuple(sorted(comparison.fine_chart_supports[1])),
        )
        support_face_flags.setdefault(support_key, set()).add(face_present)
        case_rows.append(
            {
                "name": comparison.name,
                "name_free_semantic_sha256": semantic_id,
                "name_free_id20": semantic_id[:20],
                "canonical_support_incidence_sha256": canonical_code[
                    "sha256"
                ],
                "canonical_support_incidence_id20": canonical_code["id20"],
                "face_present": face_present,
                "support_masks": {
                    "S0": _round13_support_mask(
                        comparison.coarse_chart_supports[0],
                        2,
                    ),
                    "ST": _round13_support_mask(
                        comparison.coarse_chart_supports[1],
                        2,
                    ),
                    "T0": _round13_support_mask(
                        comparison.fine_chart_supports[0],
                        3,
                    ),
                    "TT": _round13_support_mask(
                        comparison.fine_chart_supports[1],
                        3,
                    ),
                },
            }
        )
    if not (
        len(support_face_flags) == 121
        and all(flags == {False, True} for flags in support_face_flags.values())
        and sum(not row["face_present"] for row in case_rows) == 121
        and sum(bool(row["face_present"]) for row in case_rows) == 121
        and all(
            comparison.morphism.coarse.edges
            == ((0, 0), (1, 2), (1, 3), (2, 3))
            for comparison in comparisons
        )
    ):
        raise AssertionError("Round13 face-control or cross-chart grammar drift")

    contractible = contractible_triangle_fixture()
    contractible_id = _case_semantic_sha256(contractible)
    absent_control = round13_bound_fixture(
        face_present=False,
        coarse_anchor_support=frozenset((0,)),
        coarse_triangle_support=frozenset((0, 1)),
        fine_anchor_support=frozenset((0, 1)),
        fine_triangle_support=frozenset((2,)),
    )
    absent_control_id = _case_semantic_sha256(absent_control)
    if not (
        semantic_ids.count(contractible_id) == 1
        and semantic_ids.count(absent_control_id) == 1
        and contractible_id != absent_control_id
        and contractible.coarse_chart_supports[0]
        != contractible.coarse_chart_supports[1]
        and contractible.fine_chart_supports[0]
        != contractible.fine_chart_supports[1]
    ):
        raise AssertionError("Round13 CONTRACTIBLE/control inclusion drift")

    prior_comparisons = (
        tuple(_all_comparisons_through_round11())
        + round12_relation_fixtures()
    )
    prior_payloads = tuple(
        _case_semantic_payload_json(comparison)
        for comparison in prior_comparisons
    )
    prior_ids = tuple(
        sha256(payload.encode("utf-8")).hexdigest()
        for payload in prior_payloads
    )
    if not (
        len(prior_comparisons) == 1918
        and len(set(prior_payloads)) == 1918
        and len(set(prior_ids)) == 1918
        and len({identifier[:20] for identifier in prior_ids}) == 1918
    ):
        raise AssertionError("Round13 prior-1918 pure ID baseline drift")

    prior_by_full = dict(zip(prior_ids, prior_payloads))
    bound_by_full = dict(zip(semantic_ids, semantic_payloads))
    combined_by_full: dict[str, set[str]] = {}
    for identifier, payload in (
        tuple(zip(prior_ids, prior_payloads))
        + tuple(zip(semantic_ids, semantic_payloads))
    ):
        combined_by_full.setdefault(identifier, set()).add(payload)
    combined_short_to_full: dict[str, set[str]] = {}
    for identifier in combined_by_full:
        combined_short_to_full.setdefault(identifier[:20], set()).add(identifier)
    full_collision_count = sum(
        len(payloads) > 1 for payloads in combined_by_full.values()
    )
    truncated_collision_count = sum(
        len(identifiers) > 1
        for identifiers in combined_short_to_full.values()
    )
    if full_collision_count or truncated_collision_count:
        raise AssertionError("Round13 prior/bound semantic hash collision")
    overlap_ids = tuple(sorted(set(prior_by_full) & set(bound_by_full)))
    new_ids = tuple(sorted(set(bound_by_full) - set(prior_by_full)))
    union_count = len(set(prior_ids) | set(semantic_ids))
    if not (
        len(overlap_ids) == 0
        and len(new_ids) == 242
        and len(new_ids) > 0
        and union_count == 2160
    ):
        raise AssertionError("Round13 registered strict coverage expansion drift")

    required_catalog = _round13_pure_catalog_manifest()
    if required_catalog["count"] != 16:
        raise AssertionError("Round13 required16 pure catalog drift")
    return {
        "kind": "round13-preregistration-pure-bound-manifest",
        "semantic_bound": {
            "semantic_id": ROUND13_BOUND_SEMANTIC_ID,
            "semantic_sha256": ROUND13_BOUND_SEMANTIC_SHA256,
            "spec": ROUND13_BOUND_SPEC,
        },
        "v4_candidate_reference": {
            "semantic_id": V4_SEMANTIC_ID,
            "semantic_sha256": V4_SEMANTIC_SHA256,
            "human_adjudication_issue_comment": (
                V4_HUMAN_ADJUDICATION_ISSUE_COMMENT
            ),
            "calibration_payload": {
                "canonical_sha256": (
                    V4_CALIBRATION_REGISTERED_CANONICAL_SHA256
                ),
                "canonical_bytes": (
                    V4_CALIBRATION_REGISTERED_CANONICAL_BYTES
                ),
                "serialization": V4_CALIBRATION_SERIALIZATION_CONTRACT,
            },
        },
        "parent_artifact_references": {
            "results.json": ROUND13_PARENT_RESULTS_JSON_SHA256,
            "results-summary.json": (
                ROUND13_PARENT_RESULTS_SUMMARY_JSON_SHA256
            ),
            "round12_payload": ROUND13_PARENT_ROUND12_PAYLOAD_SHA256,
        },
        "labeled_population": {
            "raw_support_and_face_flag_cases": raw_count,
            "compatible_cases": len(comparisons),
            "face_absent_cases": 121,
            "face_present_cases": 121,
            "support_pairs_with_both_face_controls": len(
                support_face_flags
            ),
            "all_cross_chart_incidence_exact": True,
            "all_cases_are_UniformComparison_values": True,
        },
        "canonical_orbit_audit": {
            "single_position_compatible_labeled_pairs": len(
                single_position_pairs
            ),
            "single_position_swap_fixed_pairs": len(
                fixed_single_position_pairs
            ),
            "burnside_orbits_per_face_flag": 73,
            "face_flags": 2,
            "compatible_labeled_semantic_count": len(set(semantic_payloads)),
            "canonical_support_incidence_orbit_count": len(
                set(canonical_payloads)
            ),
            "full_sha256_collision_count": (
                len(set(canonical_payloads)) - len(set(canonical_ids))
            ),
            "truncated_20hex_collision_count": (
                len(set(canonical_ids)) - len(set(canonical_id20))
            ),
        },
        "prior_population_comparison": {
            "prior_unique_name_free_ids": len(set(prior_ids)),
            "bound_unique_name_free_ids": len(set(semantic_ids)),
            "overlap_count": len(overlap_ids),
            "overlap_ids": list(overlap_ids),
            "new_count": len(new_ids),
            "strict_new": len(new_ids) > 0,
            "new_ids": list(new_ids),
            "union_count": union_count,
            "full_sha256_collision_count": full_collision_count,
            "truncated_20hex_collision_count": truncated_collision_count,
        },
        "contractible_and_control": {
            "contractible_name_free_sha256": contractible_id,
            "contractible_included": True,
            "face_absent_control_name_free_sha256": absent_control_id,
            "face_absent_control_included": True,
            "filled_and_absent_ids_distinct": True,
            "coarse_anchor_triangle_support_split": True,
            "fine_anchor_triangle_support_split": True,
            "cross_chart_components_exact": True,
        },
        "required16_pure_catalog": required_catalog,
        "cases": case_rows,
        "dependency_contract": {
            "constructs_uniform_comparisons": True,
            "computes_name_free_semantic_ids": True,
            "calls_H1_or_is_uniform": False,
            "calls_candidate": False,
            "calls_query_or_round_report": False,
        },
        "preregistered_issue_comment": None,
        "query_gate_added": False,
        "round13_report_added": False,
    }


def round13_preregistration_manifest_canonical_json() -> str:
    return json.dumps(
        round13_preregistration_manifest(),
        sort_keys=True,
        separators=(",", ":"),
    )


def round13_preregistration_manifest_sha256() -> str:
    return sha256(
        round13_preregistration_manifest_canonical_json().encode("utf-8")
    ).hexdigest()


def _v4_calibration_canonical_bytes(
    report: dict[str, object],
) -> bytes:
    rendered = (
        json.dumps(
            report,
            ensure_ascii=False,
            indent=2,
            sort_keys=True,
        )
        + "\n"
    )
    return rendered.encode("utf-8")


def _round13_manifest_admission() -> dict[str, object]:
    manifest = round13_preregistration_manifest()
    manifest_json = json.dumps(
        manifest,
        sort_keys=True,
        separators=(",", ":"),
    )
    manifest_sha256 = sha256(manifest_json.encode("utf-8")).hexdigest()
    population = manifest["labeled_population"]
    canonical = manifest["canonical_orbit_audit"]
    comparison = manifest["prior_population_comparison"]
    contract = manifest["contractible_and_control"]
    contractible_id = _case_semantic_sha256(
        contractible_triangle_fixture()
    )
    absent_control_id = _case_semantic_sha256(
        round13_bound_fixture(
            face_present=False,
            coarse_anchor_support=frozenset((0,)),
            coarse_triangle_support=frozenset((0, 1)),
            fine_anchor_support=frozenset((0, 1)),
            fine_triangle_support=frozenset((2,)),
        )
    )
    if not (
        manifest_sha256 == ROUND13_REGISTERED_MANIFEST_SHA256
        and ROUND13_PREREGISTERED_ISSUE_COMMENT == 5234690436
        and ROUND13_PREREGISTERED_ISSUE_COMMENT is not None
        and ROUND13_PREREGISTERED_CREATED_AT
        == ROUND13_PREREGISTERED_UPDATED_AT
        == "2026-08-10T00:34:52Z"
        and population["raw_support_and_face_flag_cases"] == 882
        and population["compatible_cases"] == 242
        and canonical["canonical_support_incidence_orbit_count"] == 146
        and canonical["full_sha256_collision_count"] == 0
        and canonical["truncated_20hex_collision_count"] == 0
        and comparison["overlap_count"] == 0
        and comparison["new_count"] == 242
        and comparison["strict_new"] is True
        and comparison["union_count"] == 2160
        and comparison["full_sha256_collision_count"] == 0
        and comparison["truncated_20hex_collision_count"] == 0
        and contract["contractible_name_free_sha256"]
        == contractible_id
        and contract["face_absent_control_name_free_sha256"]
        == absent_control_id
        and contract["contractible_included"] is True
        and contract["face_absent_control_included"] is True
    ):
        raise AssertionError("Round13 preregistered pure manifest gate failed")
    return {
        "manifest": manifest,
        "manifest_sha256": manifest_sha256,
        "preregistered_issue_comment": ROUND13_PREREGISTERED_ISSUE_COMMENT,
        "created_at": ROUND13_PREREGISTERED_CREATED_AT,
        "updated_at": ROUND13_PREREGISTERED_UPDATED_AT,
        "all_gates_pass": True,
    }


def _round13_v4_calibration_admission() -> dict[str, object]:
    calibration = v4_calibration_report()
    rendered = _v4_calibration_canonical_bytes(calibration)
    calibration_sha256 = sha256(rendered).hexdigest()
    required = calibration["required_catalog"]
    prior = calibration["prior_population"]
    normalization = calibration["terminal_h1_normalization_calibration"]
    if not (
        calibration_sha256
        == V4_CALIBRATION_REGISTERED_CANONICAL_SHA256
        and len(rendered) == V4_CALIBRATION_REGISTERED_CANONICAL_BYTES
        and required["legacy_count"] == 13
        and required["v4_count"] == 16
        and required["mismatch_count"] == 0
        and prior["raw_cases"] == 1918
        and prior["uniform_and_not_candidate_count"] == 0
        and prior["candidate_and_nonuniform_count"] == 0
        and normalization["required_catalog_16"]["mismatch_count"] == 0
        and normalization["prior_population_1918"]["mismatch_count"] == 0
    ):
        raise AssertionError("Round13 registered v4 calibration gate failed")
    return {
        "canonical_sha256": calibration_sha256,
        "canonical_bytes": len(rendered),
        "required_catalog_count": required["v4_count"],
        "prior_population_count": prior["raw_cases"],
        "two_way_mismatch_count": (
            prior["uniform_and_not_candidate_count"]
            + prior["candidate_and_nonuniform_count"]
        ),
        "normalization_mismatch_count": (
            normalization["required_catalog_16"]["mismatch_count"]
            + normalization["prior_population_1918"]["mismatch_count"]
        ),
        "all_gates_pass": True,
    }


def _round13_parent_artifact_admission() -> dict[str, object]:
    from build_results import (
        render_json,
        results_report_through_round12,
        results_summary_report_through_round12,
    )

    full = results_report_through_round12()
    summary = results_summary_report_through_round12(full)
    full_bytes = render_json(full).encode("utf-8")
    summary_bytes = render_json(summary).encode("utf-8")
    full_sha256 = sha256(full_bytes).hexdigest()
    summary_sha256 = sha256(summary_bytes).hexdigest()
    committed_summary_path = Path(__file__).with_name("results-summary.json")
    committed_summary_bytes = committed_summary_path.read_bytes()
    committed_summary_sha256 = sha256(committed_summary_bytes).hexdigest()
    round12 = full["r2"]["round12_post_punit_octahedral_partitioned"]
    round12_sha256 = _canonical_report_sha256(round12)
    if not (
        full_sha256 == ROUND13_PARENT_RESULTS_JSON_SHA256
        and summary_sha256
        == ROUND13_PARENT_RESULTS_SUMMARY_JSON_SHA256
        and committed_summary_sha256
        == ROUND13_PARENT_RESULTS_SUMMARY_JSON_SHA256
        and committed_summary_bytes == summary_bytes
        and round12_sha256 == ROUND13_PARENT_ROUND12_PAYLOAD_SHA256
    ):
        raise AssertionError("Round13 immutable parent artifact gate failed")
    return {
        "results.json": {
            "canonical_sha256": full_sha256,
            "canonical_bytes": len(full_bytes),
        },
        "results-summary.json": {
            "canonical_sha256": summary_sha256,
            "canonical_bytes": len(summary_bytes),
            "committed_bytes_exact": True,
        },
        "round12_payload_sha256": round12_sha256,
        "all_gates_pass": True,
    }


def _round13_admission_gate() -> dict[str, object]:
    manifest = _round13_manifest_admission()
    calibration = _round13_v4_calibration_admission()
    parent = _round13_parent_artifact_admission()
    return {
        "gate_order": [
            "pure_preregistration_manifest",
            "v4_calibration",
            "immutable_parent_artifacts",
        ],
        "manifest": manifest,
        "calibration": calibration,
        "parent_artifacts": parent,
        "all_gates_pass": True,
    }


def _round13_break_witness(
    *,
    comparison: UniformComparison,
    category: str,
    blocks: tuple[tuple[frozenset[int], H1Analysis], ...],
    candidate: dict[str, object],
    direction: str,
    canonical_nonisomorphic_id: str | None,
) -> dict[str, object]:
    if direction == "candidate_and_nonuniform":
        targets, analysis = next(
            (targets, analysis)
            for targets, analysis in blocks
            if not analysis.isomorphism
        )
        candidate_failure_scope = None
        candidate_failure_conditions = None
    elif direction == "uniform_and_not_candidate":
        failing_subset = next(
            (
                row
                for row in candidate["per_subset"]
                if not all(row["conditions"].values())
            ),
            None,
        )
        if failing_subset is None:
            targets = frozenset(range(comparison.coarse_target_count))
            candidate_failure_scope = "whole"
            candidate_failure_conditions = candidate["whole"]["conditions"]
        else:
            targets = frozenset(failing_subset["coarse_targets_A"])
            candidate_failure_scope = "nonempty-A"
            candidate_failure_conditions = failing_subset["conditions"]
        analysis = next(
            analysis
            for block_targets, analysis in blocks
            if block_targets == targets
        )
    else:
        raise ValueError("unknown Round13 break direction")
    return {
        "id": _case_semantic_sha256(comparison),
        "id20": _case_id(comparison),
        "canonical_nonisomorphic_id": (
            canonical_nonisomorphic_id
            if canonical_nonisomorphic_id is not None
            else _case_semantic_sha256(comparison)
        ),
        "name": comparison.name,
        "category": category,
        "direction": direction,
        "minimal_failing_A": sorted(targets),
        "exact_h1": asdict(analysis),
        "candidate_aggregate": candidate["aggregate"],
        "candidate_failure_scope": candidate_failure_scope,
        "candidate_failure_conditions": candidate_failure_conditions,
    }


def _round13_population_query(
    manifest: dict[str, object],
) -> dict[str, object]:
    prior = (
        tuple(_all_comparisons_through_round11())
        + round12_relation_fixtures()
    )
    new = round13_bound_comparisons()
    comparisons = tuple(
        ("prior1918", comparison) for comparison in prior
    ) + tuple(("round13_new", comparison) for comparison in new)
    full_ids = tuple(
        _case_semantic_sha256(comparison)
        for _, comparison in comparisons
    )
    short_ids = tuple(identifier[:20] for identifier in full_ids)
    prior_ids = set(full_ids[: len(prior)])
    new_ids = set(full_ids[len(prior) :])
    registered_new_ids = set(
        manifest["prior_population_comparison"]["new_ids"]
    )
    registered_new_cases = {
        row["name_free_semantic_sha256"]: row
        for row in manifest["cases"]
    }
    if not (
        len(prior) == 1918
        and len(new) == 242
        and len(comparisons) == 2160
        and len(set(full_ids)) == 2160
        and len(set(short_ids)) == 2160
        and not (prior_ids & new_ids)
        and new_ids == registered_new_ids
        and set(registered_new_cases) == registered_new_ids
    ):
        raise AssertionError("Round13 admitted population identity drift")

    ledger = []
    witnesses = []
    prior_A_queries = 0
    new_A_queries = 0
    for category, comparison in comparisons:
        semantic_id = _case_semantic_sha256(comparison)
        canonical_nonisomorphic_id = (
            registered_new_cases[semantic_id][
                "canonical_support_incidence_sha256"
            ]
            if category == "round13_new"
            else None
        )
        blocks = comparison.block_analyses()
        candidate = v4_candidate_evaluation(
            comparison,
            include_terminal_details=False,
        )
        uniform = all(analysis.isomorphism for _, analysis in blocks)
        if category == "round13_new":
            new_A_queries += len(blocks)
        else:
            prior_A_queries += len(blocks)
        candidate_vector = [
            candidate["aggregate"][f"C{index}*"]
            for index in range(7)
        ]
        ledger.append(
            {
                "id": semantic_id,
                "id20": _case_id(comparison),
                "canonical_nonisomorphic_id": (
                    canonical_nonisomorphic_id
                ),
                "name": comparison.name,
                "category": category,
                "uniform": uniform,
                "candidate_all": candidate["all"],
                "candidate_vector_C0_through_C6": candidate_vector,
                "A_blocks": [
                    [
                        sorted(targets),
                        analysis.coarse_h1_dimension,
                        analysis.fine_h1_dimension,
                        analysis.comparison_rank,
                        analysis.injective,
                        analysis.surjective,
                        analysis.isomorphism,
                    ]
                    for targets, analysis in blocks
                ],
            }
        )
        if uniform and not candidate["all"]:
            witnesses.append(
                _round13_break_witness(
                    comparison=comparison,
                    category=category,
                    blocks=blocks,
                    candidate=candidate,
                    direction="uniform_and_not_candidate",
                    canonical_nonisomorphic_id=(
                        canonical_nonisomorphic_id
                    ),
                )
            )
        if candidate["all"] and not uniform:
            witnesses.append(
                _round13_break_witness(
                    comparison=comparison,
                    category=category,
                    blocks=blocks,
                    candidate=candidate,
                    direction="candidate_and_nonuniform",
                    canonical_nonisomorphic_id=(
                        canonical_nonisomorphic_id
                    ),
                )
            )
    if new_A_queries != 726:
        raise AssertionError("Round13 new A-query count drift")
    ledger_json = json.dumps(ledger, sort_keys=True, separators=(",", ":"))
    ledger_sha256 = sha256(ledger_json.encode("utf-8")).hexdigest()
    uniform_not_candidate = [
        witness
        for witness in witnesses
        if witness["direction"] == "uniform_and_not_candidate"
    ]
    candidate_nonuniform = [
        witness
        for witness in witnesses
        if witness["direction"] == "candidate_and_nonuniform"
    ]
    return {
        "population": {
            "prior_cases": len(prior),
            "new_cases": len(new),
            "total_cases": len(comparisons),
            "unique_full_name_free_ids": len(set(full_ids)),
            "unique_truncated_20hex_ids": len(set(short_ids)),
            "full_sha256_collision_count": 0,
            "truncated_20hex_collision_count": 0,
            "new_disjoint_from_prior": True,
            "prior_A_queries": prior_A_queries,
            "new_A_queries": new_A_queries,
            "total_A_queries": prior_A_queries + new_A_queries,
            "sampling": False,
            "early_stop": False,
            "all_cases_and_nonempty_A_evaluated": True,
        },
        "queries": {
            "uniform_and_not_candidate_count": len(uniform_not_candidate),
            "candidate_and_nonuniform_count": len(candidate_nonuniform),
            "uniform_and_not_candidate": uniform_not_candidate,
            "candidate_and_nonuniform": candidate_nonuniform,
        },
        "ledger": {
            "row_count": len(ledger),
            "compact_rows": ledger,
            "compact_json_sha256": ledger_sha256,
        },
        "candidate_predicate_reads_global_or_A_block_H1": False,
        "candidate_predicate_uses_preregistered_local_C3_linear_algebra": True,
    }


def round13_report() -> dict[str, object]:
    admission = _round13_admission_gate()
    manifest = admission["manifest"]["manifest"]
    query = _round13_population_query(manifest)
    ledger_rows = query["ledger"]["compact_rows"]
    contractible_id = manifest["contractible_and_control"][
        "contractible_name_free_sha256"
    ]
    absent_control_id = manifest["contractible_and_control"][
        "face_absent_control_name_free_sha256"
    ]
    contractible_result = next(
        row for row in ledger_rows if row["id"] == contractible_id
    )
    absent_control_result = next(
        row for row in ledger_rows if row["id"] == absent_control_id
    )
    edge_fiber = next(
        row for row in ledger_rows if row["name"] == "EdgeFiberObstruction"
    )
    if not (
        contractible_result["category"] == "round13_new"
        and absent_control_result["category"] == "round13_new"
        and contractible_result["uniform"] is True
        and contractible_result["candidate_all"] is True
        and edge_fiber["uniform"] is False
        and edge_fiber["candidate_all"] is False
    ):
        raise AssertionError("Round13 exact calibration/control result drift")

    new_counterexamples = [
        witness
        for direction in (
            "uniform_and_not_candidate",
            "candidate_and_nonuniform",
        )
        for witness in query["queries"][direction]
        if witness["category"] == "round13_new"
    ]
    new_verdicts = sorted(
        {
            "CSTAR-not-necessary"
            for witness in new_counterexamples
            if witness["direction"] == "uniform_and_not_candidate"
        }
        | {
            "CSTAR-not-sufficient"
            for witness in new_counterexamples
            if witness["direction"] == "candidate_and_nonuniform"
        }
    )
    new_canonical_counterexamples = sorted(
        {
            witness["canonical_nonisomorphic_id"]
            for witness in new_counterexamples
        }
    )
    candidate_semantic_change = True
    additional_calibration_fixes = [
        "C5/C6 guard domain detects mapped fine critical fibers over coarse bridges (EdgeFiberObstruction)"
    ]
    progress = bool(
        new_verdicts
        or new_canonical_counterexamples
        or candidate_semantic_change
        or additional_calibration_fixes
    )
    return {
        "round": "R2-round-13",
        "valid": True,
        "preregistration": {
            "issue_comment": ROUND13_PREREGISTERED_ISSUE_COMMENT,
            "created_at": ROUND13_PREREGISTERED_CREATED_AT,
            "updated_at": ROUND13_PREREGISTERED_UPDATED_AT,
            "manifest_sha256": ROUND13_REGISTERED_MANIFEST_SHA256,
        },
        "admission": admission,
        "candidate": {
            "previous_semantic_id": CERTIFIED_SEMANTIC_ID,
            "previous_semantic_sha256": CERTIFIED_SEMANTIC_SHA256,
            "semantic_id": V4_SEMANTIC_ID,
            "semantic_sha256": V4_SEMANTIC_SHA256,
            "spec": V4_SPEC,
            "semantic_change_from_v3": candidate_semantic_change,
            "calibration_sha256": (
                V4_CALIBRATION_REGISTERED_CANONICAL_SHA256
            ),
            "calibration_bytes": (
                V4_CALIBRATION_REGISTERED_CANONICAL_BYTES
            ),
        },
        "bound": {
            "semantic_id": ROUND13_BOUND_SEMANTIC_ID,
            "semantic_sha256": ROUND13_BOUND_SEMANTIC_SHA256,
            "spec": ROUND13_BOUND_SPEC,
            "canonical_orbit_count": 146,
        },
        "population": query["population"],
        "queries": query["queries"],
        "result_ledger": query["ledger"],
        "query_contract": {
            "candidate_predicate_reads_global_or_A_block_H1": query[
                "candidate_predicate_reads_global_or_A_block_H1"
            ],
            "candidate_predicate_uses_preregistered_local_C3_linear_algebra": query[
                "candidate_predicate_uses_preregistered_local_C3_linear_algebra"
            ],
            "sampling": query["population"]["sampling"],
            "early_stop": query["population"]["early_stop"],
        },
        "exact_controls": {
            "CONTRACTIBLE-TRIANGLE": contractible_result,
            "face_absent_same_support": absent_control_result,
            "EdgeFiberObstruction": edge_fiber,
        },
        "progress_audit": {
            "entry_streak": 0,
            "new_verdicts": new_verdicts,
            "new_canonical_nonisomorphic_counterexamples": (
                new_canonical_counterexamples
            ),
            "candidate_semantic_change": candidate_semantic_change,
            "additional_calibration_fixes": additional_calibration_fixes,
            "new_counterexample_count": len(new_counterexamples),
            "new_counterexamples": new_counterexamples,
            "progress": progress,
            "streak_after_round": 0,
        },
        "stop_audit": {
            "stop_condition_A_completion": False,
            "stop_condition_B_finite_exhaustion": False,
            "stop_condition_C_two_valid_same_blocker_no_progress": False,
            "zero_result_does_not_override_progress": True,
        },
        "coverage_limit": (
            "Exactly the prior 1,918 name-free semantic cases plus all 242 "
            "compatible labeled cases in the preregistered four-chart "
            "loop-plus-triangle face-present/absent support grammar; no larger "
            "incidence or support family is covered."
        ),
    }


ROUND14_BOUND_SEMANTIC_ID = "R14-NONFREE-MUTUAL-KILL-SPLIT-v1"
ROUND14_BOUND_SPEC = "\n".join(
    (
        "purpose:pure preregistration verification of one human-static-discovered v4 necessity counterexample; not a blind search",
        "nerve:coarse and fine are the identity two-chart nerve with loops a at chart 0 and x,y at chart 1 and faces (x,x,y),(y,y,x)",
        "morphism:vertex, edge, and face maps are identities",
        "targets:coarse Target 2, fine Target 3, and pi=(0,0,1)",
        "supports:coarse charts are ({0},{0,1}) and fine charts are ({0,1},{2})",
        "nonfree:each of x and y occurs raw in both retained FaceTwin classes, so no signed-unit joint-collapse packet is allowed",
        "symmetry:canonicalize by simultaneous x<->y and face F<->G plus the pi-preserving fine-target swap 0<->1",
        "expected-H1:the three nonempty A blocks are 1/1/rank1, 0/0/rank0, and 1/1/rank1, all isomorphisms",
        "expected-v4:C0,C1,C2,C4 are false and C3,C5,C6 are true, with one empty-trace terminal in every scope",
        "expected-direction:uniform_and_not_candidate, yielding CSTAR-not-necessary only if the later engine query reproduces the preregistered expectations",
        "dependency:pure fixture, support, semantic-ID, orbit, and union checks only; no H1, candidate, calibration, query, or round-report evaluator",
    )
)
ROUND14_BOUND_SEMANTIC_SHA256 = sha256(
    ROUND14_BOUND_SPEC.encode("ascii")
).hexdigest()
ROUND14_PARENT_ROUND13_PAYLOAD_SHA256 = (
    "e15fc8dcb99ea7e8e17b1a52cc045379f9757c558a92f25e9d1bfc2bda5450e3"
)
ROUND14_PARENT_ROUND13_CANONICAL_BYTES = 5_604_143
ROUND14_PARENT_ROUND13_LEDGER_SHA256 = (
    "8950edc32e11c7809bffc4ff3cb9b5f64b76905825e416133d414abd065737e0"
)
ROUND14_PARENT_ROUND13_RESULT_ISSUE_COMMENT = 5234839619
ROUND14_PARENT_ROUND13_RESULT_CREATED_AT = "2026-08-10T01:08:00Z"
ROUND14_PARENT_ROUND13_RESULT_UPDATED_AT = "2026-08-10T01:08:00Z"
ROUND14_PARENT_POPULATION = 2160
ROUND14_PREREGISTERED_ISSUE_COMMENT = 5234939066
ROUND14_PREREGISTERED_CREATED_AT = "2026-08-10T01:28:53Z"
ROUND14_PREREGISTERED_UPDATED_AT = "2026-08-10T01:28:53Z"
ROUND14_REGISTERED_MANIFEST_SHA256 = (
    "eaa0c96376bb1d724505b16c6df6b7d519e27b7451da6a94d06b673d65e1f309"
)
ROUND14_REGISTERED_FIXTURE_SEMANTIC_SHA256 = (
    "e908498046aa55e1781a8d0a4d7ec06e213272222dd374126eb5ce9d39cb058e"
)
ROUND14_REGISTERED_FIXTURE_ID20 = "e908498046aa55e1781a"
ROUND14_REGISTERED_CANONICAL_ORBIT_SHA256 = (
    "4ce2e10bcafaff1da04136a13151cab65566b652ff3392faa79ecb39c3823698"
)
ROUND14_REGISTERED_CANONICAL_ORBIT_ID20 = "4ce2e10bcafaff1da041"


def nonfree_mutual_kill_split_fixture() -> UniformComparison:
    nerve = Nerve(
        2,
        ((0, 0), (1, 1), (1, 1)),
        ((1, 1, 2), (2, 2, 1)),
    )
    return UniformComparison(
        name="NONFREE-MUTUAL-KILL-SPLIT",
        morphism=NerveMorphism(
            coarse=nerve,
            fine=nerve,
            vertex_map=(0, 1),
            edge_map=(0, 1, 2),
            face_map=(0, 1),
        ),
        coarse_target_count=2,
        fine_target_count=3,
        factor_pi=(0, 0, 1),
        coarse_chart_supports=(
            frozenset((0,)),
            frozenset((0, 1)),
        ),
        fine_chart_supports=(
            frozenset((0, 1)),
            frozenset((2,)),
        ),
    )


def _round14_relabelled_payload_json(
    comparison: UniformComparison,
    *,
    swap_mutual_cells: bool,
    swap_fine_targets_0_1: bool,
) -> str:
    expected_nerve = Nerve(
        2,
        ((0, 0), (1, 1), (1, 1)),
        ((1, 1, 2), (2, 2, 1)),
    )
    if not (
        comparison.morphism.coarse == expected_nerve
        and comparison.morphism.fine == expected_nerve
        and comparison.morphism.vertex_map == (0, 1)
        and comparison.morphism.edge_map == (0, 1, 2)
        and comparison.morphism.face_map == (0, 1)
        and comparison.coarse_target_count == 2
        and comparison.fine_target_count == 3
        and comparison.factor_pi == (0, 0, 1)
        and comparison.coarse_chart_supports
        == (frozenset((0,)), frozenset((0, 1)))
        and comparison.fine_chart_supports
        == (frozenset((0, 1)), frozenset((2,)))
    ):
        raise ValueError("comparison is outside the fixed Round14 grammar")

    edge_permutation = (0, 2, 1) if swap_mutual_cells else (0, 1, 2)
    face_permutation = (1, 0) if swap_mutual_cells else (0, 1)
    target_permutation = (
        (1, 0, 2) if swap_fine_targets_0_1 else (0, 1, 2)
    )

    def inverse(permutation: tuple[int, ...]) -> tuple[int, ...]:
        result = [0 for _ in permutation]
        for old, new in enumerate(permutation):
            result[new] = old
        return tuple(result)

    inverse_edges = inverse(edge_permutation)
    inverse_faces = inverse(face_permutation)
    inverse_targets = inverse(target_permutation)

    def relabelled_nerve(nerve: Nerve) -> dict[str, object]:
        return {
            "vertices": nerve.vertices,
            "edges": [
                list(nerve.edges[inverse_edges[new_edge]])
                for new_edge in range(len(inverse_edges))
            ],
            "faces": [
                [
                    edge_permutation[old_edge]
                    for old_edge in nerve.faces[
                        inverse_faces[new_face]
                    ]
                ]
                for new_face in range(len(inverse_faces))
            ],
        }

    morphism = comparison.morphism
    relabelled_edge_map: list[int | None] = []
    for new_fine_edge in range(len(inverse_edges)):
        mapped = morphism.edge_map[inverse_edges[new_fine_edge]]
        relabelled_edge_map.append(
            None if mapped is None else edge_permutation[mapped]
        )
    relabelled_face_map: list[int | None] = []
    for new_fine_face in range(len(inverse_faces)):
        mapped = morphism.face_map[inverse_faces[new_fine_face]]
        relabelled_face_map.append(
            None if mapped is None else face_permutation[mapped]
        )
    relabelled_pi = [
        comparison.factor_pi[inverse_targets[new_target]]
        for new_target in range(len(inverse_targets))
    ]
    relabelled_fine_supports = [
        sorted(target_permutation[target] for target in support)
        for support in comparison.fine_chart_supports
    ]
    payload = {
        "coarse": relabelled_nerve(morphism.coarse),
        "fine": relabelled_nerve(morphism.fine),
        "vertex_map": list(morphism.vertex_map),
        "edge_map": relabelled_edge_map,
        "face_map": relabelled_face_map,
        "coarse_target_count": comparison.coarse_target_count,
        "fine_target_count": comparison.fine_target_count,
        "factor_pi": relabelled_pi,
        "coarse_chart_supports": [
            sorted(support) for support in comparison.coarse_chart_supports
        ],
        "fine_chart_supports": relabelled_fine_supports,
    }
    return json.dumps(payload, sort_keys=True, separators=(",", ":"))


def round14_nonfree_mutual_kill_canonical_orbit_code(
    comparison: UniformComparison,
) -> dict[str, object]:
    payloads = tuple(
        _round14_relabelled_payload_json(
            comparison,
            swap_mutual_cells=swap_mutual_cells,
            swap_fine_targets_0_1=swap_fine_targets_0_1,
        )
        for swap_mutual_cells in (False, True)
        for swap_fine_targets_0_1 in (False, True)
    )
    compact_json = min(payloads)
    digest = sha256(compact_json.encode("ascii")).hexdigest()
    orbit_size = len(set(payloads))
    if orbit_size == 0 or 4 % orbit_size:
        raise AssertionError("Round14 symmetry orbit does not divide the group")
    return {
        "compact_json": compact_json,
        "sha256": digest,
        "id20": digest[:20],
        "group_order": 4,
        "orbit_size": orbit_size,
        "stabilizer_order": 4 // orbit_size,
        "actions": [
            "identity",
            "fine-target-0-1",
            "mutual-x-y-and-F-G",
            "mutual-x-y-and-F-G+fine-target-0-1",
        ],
    }


def round14_preregistration_manifest() -> dict[str, object]:
    comparison = nonfree_mutual_kill_split_fixture()
    expected_derived_supports = {
        "coarse_edges": [[0], [0, 1], [0, 1]],
        "coarse_faces": [[0, 1], [0, 1]],
        "fine_edges": [[0, 1], [2], [2]],
        "fine_faces": [[2], [2]],
    }
    coarse_edge_supports, coarse_face_supports = derived_cell_supports(
        comparison.morphism.coarse,
        comparison.coarse_chart_supports,
    )
    fine_edge_supports, fine_face_supports = derived_cell_supports(
        comparison.morphism.fine,
        comparison.fine_chart_supports,
    )
    actual_derived_supports = {
        "coarse_edges": [sorted(support) for support in coarse_edge_supports],
        "coarse_faces": [sorted(support) for support in coarse_face_supports],
        "fine_edges": [sorted(support) for support in fine_edge_supports],
        "fine_faces": [sorted(support) for support in fine_face_supports],
    }
    if actual_derived_supports != expected_derived_supports:
        raise AssertionError("Round14 exact derived-support drift")

    prior = (
        tuple(_all_comparisons_through_round11())
        + round12_relation_fixtures()
        + round13_bound_comparisons()
    )
    prior_payloads = tuple(
        _case_semantic_payload_json(case) for case in prior
    )
    prior_ids = tuple(
        sha256(payload.encode("utf-8")).hexdigest()
        for payload in prior_payloads
    )
    new_payload = _case_semantic_payload_json(comparison)
    new_id = sha256(new_payload.encode("utf-8")).hexdigest()
    combined: dict[str, set[str]] = {}
    for identifier, payload in (
        tuple(zip(prior_ids, prior_payloads)) + ((new_id, new_payload),)
    ):
        combined.setdefault(identifier, set()).add(payload)
    short_to_full: dict[str, set[str]] = {}
    for identifier in combined:
        short_to_full.setdefault(identifier[:20], set()).add(identifier)
    full_collision_count = sum(
        len(payloads) > 1 for payloads in combined.values()
    )
    truncated_collision_count = sum(
        len(identifiers) > 1 for identifiers in short_to_full.values()
    )
    if not (
        len(prior) == ROUND14_PARENT_POPULATION == 2160
        and len(set(prior_payloads)) == 2160
        and len(set(prior_ids)) == 2160
        and len({identifier[:20] for identifier in prior_ids}) == 2160
        and new_id not in set(prior_ids)
        and len(combined) == 2161
        and full_collision_count == 0
        and truncated_collision_count == 0
    ):
        raise AssertionError("Round14 pure strict-expansion gate failed")

    canonical_code = round14_nonfree_mutual_kill_canonical_orbit_code(
        comparison
    )
    if not (
        canonical_code["group_order"] == 4
        and canonical_code["orbit_size"] == 1
        and canonical_code["stabilizer_order"] == 4
    ):
        raise AssertionError("Round14 exact symmetry audit drift")

    expected_h1_blocks = [
        {
            "coarse_targets_A": [0],
            "coarse_h1_dimension": 1,
            "fine_h1_dimension": 1,
            "comparison_rank": 1,
            "injective": True,
            "surjective": True,
            "isomorphism": True,
        },
        {
            "coarse_targets_A": [1],
            "coarse_h1_dimension": 0,
            "fine_h1_dimension": 0,
            "comparison_rank": 0,
            "injective": True,
            "surjective": True,
            "isomorphism": True,
        },
        {
            "coarse_targets_A": [0, 1],
            "coarse_h1_dimension": 1,
            "fine_h1_dimension": 1,
            "comparison_rank": 1,
            "injective": True,
            "surjective": True,
            "isomorphism": True,
        },
    ]
    expected_candidate = {
        "whole_conditions": {"C0*": False, "C5*": True, "C6*": True},
        "per_nonempty_A": [
            {
                "coarse_targets_A": [0],
                "conditions": {
                    "C1*": False,
                    "C2*": False,
                    "C3*": True,
                    "C4*": False,
                },
                "terminal_count": 1,
                "trace": [],
            },
            {
                "coarse_targets_A": [1],
                "conditions": {
                    "C1*": True,
                    "C2*": True,
                    "C3*": True,
                    "C4*": True,
                },
                "terminal_count": 1,
                "trace": [],
            },
            {
                "coarse_targets_A": [0, 1],
                "conditions": {
                    "C1*": True,
                    "C2*": True,
                    "C3*": True,
                    "C4*": True,
                },
                "terminal_count": 1,
                "trace": [],
            },
        ],
        "whole_terminal_count": 1,
        "whole_trace": [],
        "aggregate": {
            "C0*": False,
            "C1*": False,
            "C2*": False,
            "C3*": True,
            "C4*": False,
            "C5*": True,
            "C6*": True,
        },
        "vector_C0_through_C6": [
            False,
            False,
            False,
            True,
            False,
            True,
            True,
        ],
        "candidate_all": False,
    }
    return {
        "kind": "round14-preregistration-pure-verification-manifest",
        "discovery_classification": {
            "mode": "pre-query-human-static-exact-verification",
            "blind_search": False,
            "engine_query_observed": False,
            "human_static_counterexample_expected": True,
        },
        "semantic_bound": {
            "semantic_id": ROUND14_BOUND_SEMANTIC_ID,
            "semantic_sha256": ROUND14_BOUND_SEMANTIC_SHA256,
            "spec": ROUND14_BOUND_SPEC,
        },
        "fixed_candidate_reference": {
            "semantic_id": V4_SEMANTIC_ID,
            "semantic_sha256": V4_SEMANTIC_SHA256,
            "calibration_sha256": (
                V4_CALIBRATION_REGISTERED_CANONICAL_SHA256
            ),
            "calibration_bytes": (
                V4_CALIBRATION_REGISTERED_CANONICAL_BYTES
            ),
        },
        "round13_parent_reference": {
            "payload_sha256": ROUND14_PARENT_ROUND13_PAYLOAD_SHA256,
            "canonical_bytes": ROUND14_PARENT_ROUND13_CANONICAL_BYTES,
            "compact_ledger_sha256": (
                ROUND14_PARENT_ROUND13_LEDGER_SHA256
            ),
            "result_issue_comment": (
                ROUND14_PARENT_ROUND13_RESULT_ISSUE_COMMENT
            ),
            "created_at": ROUND14_PARENT_ROUND13_RESULT_CREATED_AT,
            "updated_at": ROUND14_PARENT_ROUND13_RESULT_UPDATED_AT,
            "valid": True,
            "population": 2160,
            "uniform_and_not_candidate_count": 0,
            "candidate_and_nonuniform_count": 0,
            "progress": True,
            "streak_after_round": 0,
        },
        "fixture": {
            "name": comparison.name,
            "summary": comparison.summary(),
            "name_free_semantic_sha256": new_id,
            "name_free_id20": new_id[:20],
            "canonical_orbit_code": canonical_code,
            "expected_derived_supports": expected_derived_supports,
            "actual_derived_supports": actual_derived_supports,
            "raw_face_class_occurrences": {
                "x": [0, 1],
                "y": [0, 1],
            },
            "allowed_joint_packet_count_expected": 0,
        },
        "expected_engine_verification": {
            "H1_blocks": expected_h1_blocks,
            "uniform": True,
            "v4_candidate": expected_candidate,
            "expected_direction": "uniform_and_not_candidate",
            "expected_new_verdict_if_reproduced": "CSTAR-not-necessary",
            "expectation_is_not_engine_observation": True,
        },
        "pure_population_gate": {
            "prior_unique_name_free_ids": 2160,
            "new_unique_name_free_ids": 1,
            "overlap_count": 0,
            "new_count": 1,
            "strict_new": True,
            "union_count": 2161,
            "full_sha256_collision_count": full_collision_count,
            "truncated_20hex_collision_count": truncated_collision_count,
        },
        "dependency_contract": {
            "constructs_uniform_comparison": True,
            "computes_derived_supports": True,
            "computes_name_free_semantic_ids": True,
            "computes_fixed_symmetry_orbit_code": True,
            "calls_H1_or_is_uniform": False,
            "calls_candidate_or_calibration": False,
            "calls_query_or_round_report": False,
        },
        "preregistered_issue_comment": None,
        "query_gate_added": False,
        "round14_report_added": False,
    }


def round14_preregistration_manifest_canonical_json() -> str:
    return json.dumps(
        round14_preregistration_manifest(),
        sort_keys=True,
        separators=(",", ":"),
    )


def round14_preregistration_manifest_sha256() -> str:
    return sha256(
        round14_preregistration_manifest_canonical_json().encode("utf-8")
    ).hexdigest()


def _round14_manifest_admission() -> dict[str, object]:
    manifest = round14_preregistration_manifest()
    canonical_json = json.dumps(
        manifest,
        sort_keys=True,
        separators=(",", ":"),
    )
    manifest_sha256 = sha256(canonical_json.encode("utf-8")).hexdigest()
    fixture = manifest["fixture"]
    canonical = fixture["canonical_orbit_code"]
    population = manifest["pure_population_gate"]
    parent = manifest["round13_parent_reference"]
    if not (
        manifest_sha256 == ROUND14_REGISTERED_MANIFEST_SHA256
        and ROUND14_BOUND_SEMANTIC_SHA256
        == "c74f19f0972745138a9a3d4f80eeb9d5907c03021290c091d3541b2791acb12c"
        and ROUND14_PREREGISTERED_ISSUE_COMMENT == 5234939066
        and ROUND14_PREREGISTERED_CREATED_AT
        == ROUND14_PREREGISTERED_UPDATED_AT
        == "2026-08-10T01:28:53Z"
        and fixture["name_free_semantic_sha256"]
        == ROUND14_REGISTERED_FIXTURE_SEMANTIC_SHA256
        and fixture["name_free_id20"] == ROUND14_REGISTERED_FIXTURE_ID20
        and canonical["sha256"]
        == ROUND14_REGISTERED_CANONICAL_ORBIT_SHA256
        and canonical["id20"] == ROUND14_REGISTERED_CANONICAL_ORBIT_ID20
        and canonical["group_order"] == 4
        and canonical["orbit_size"] == 1
        and canonical["stabilizer_order"] == 4
        and population
        == {
            "prior_unique_name_free_ids": 2160,
            "new_unique_name_free_ids": 1,
            "overlap_count": 0,
            "new_count": 1,
            "strict_new": True,
            "union_count": 2161,
            "full_sha256_collision_count": 0,
            "truncated_20hex_collision_count": 0,
        }
        and parent["payload_sha256"]
        == ROUND14_PARENT_ROUND13_PAYLOAD_SHA256
        and parent["canonical_bytes"]
        == ROUND14_PARENT_ROUND13_CANONICAL_BYTES
        and parent["compact_ledger_sha256"]
        == ROUND14_PARENT_ROUND13_LEDGER_SHA256
        and parent["result_issue_comment"]
        == ROUND14_PARENT_ROUND13_RESULT_ISSUE_COMMENT
        and parent["created_at"]
        == ROUND14_PARENT_ROUND13_RESULT_CREATED_AT
        and parent["updated_at"]
        == ROUND14_PARENT_ROUND13_RESULT_UPDATED_AT
        and manifest["preregistered_issue_comment"] is None
        and manifest["query_gate_added"] is False
        and manifest["round14_report_added"] is False
    ):
        raise AssertionError("Round14 immutable preregistration manifest gate failed")
    return {
        "manifest": manifest,
        "manifest_sha256": manifest_sha256,
        "preregistered_issue_comment": (
            ROUND14_PREREGISTERED_ISSUE_COMMENT
        ),
        "created_at": ROUND14_PREREGISTERED_CREATED_AT,
        "updated_at": ROUND14_PREREGISTERED_UPDATED_AT,
        "all_gates_pass": True,
    }


def _round14_round13_baseline_admission() -> dict[str, object]:
    report = round13_report()
    rendered = (
        json.dumps(report, ensure_ascii=False, indent=2, sort_keys=True)
        + "\n"
    ).encode("utf-8")
    payload_sha256 = sha256(rendered).hexdigest()
    population = report["population"]
    queries = report["queries"]
    progress = report["progress_audit"]
    ledger_sha256 = report["result_ledger"]["compact_json_sha256"]
    if not (
        payload_sha256 == ROUND14_PARENT_ROUND13_PAYLOAD_SHA256
        and len(rendered) == ROUND14_PARENT_ROUND13_CANONICAL_BYTES
        and ledger_sha256 == ROUND14_PARENT_ROUND13_LEDGER_SHA256
        and ROUND14_PARENT_ROUND13_RESULT_ISSUE_COMMENT == 5234839619
        and ROUND14_PARENT_ROUND13_RESULT_CREATED_AT
        == ROUND14_PARENT_ROUND13_RESULT_UPDATED_AT
        == "2026-08-10T01:08:00Z"
        and report["round"] == "R2-round-13"
        and report["valid"] is True
        and report["candidate"]["semantic_id"] == V4_SEMANTIC_ID
        and report["candidate"]["semantic_sha256"] == V4_SEMANTIC_SHA256
        and population["prior_cases"] == 1918
        and population["new_cases"] == 242
        and population["total_cases"] == 2160
        and population["unique_full_name_free_ids"] == 2160
        and population["unique_truncated_20hex_ids"] == 2160
        and population["full_sha256_collision_count"] == 0
        and population["truncated_20hex_collision_count"] == 0
        and queries["uniform_and_not_candidate_count"] == 0
        and queries["candidate_and_nonuniform_count"] == 0
        and queries["uniform_and_not_candidate"] == []
        and queries["candidate_and_nonuniform"] == []
        and progress["progress"] is True
        and progress["streak_after_round"] == 0
    ):
        raise AssertionError("Round14 immutable Round13 result gate failed")
    return {
        "payload_sha256": payload_sha256,
        "canonical_bytes": len(rendered),
        "compact_ledger_sha256": ledger_sha256,
        "result_issue_comment": ROUND14_PARENT_ROUND13_RESULT_ISSUE_COMMENT,
        "created_at": ROUND14_PARENT_ROUND13_RESULT_CREATED_AT,
        "updated_at": ROUND14_PARENT_ROUND13_RESULT_UPDATED_AT,
        "valid": True,
        "population": population["total_cases"],
        "uniform_and_not_candidate_count": queries[
            "uniform_and_not_candidate_count"
        ],
        "candidate_and_nonuniform_count": queries[
            "candidate_and_nonuniform_count"
        ],
        "progress": progress["progress"],
        "streak_after_round": progress["streak_after_round"],
        "all_gates_pass": True,
    }


def _round14_population_identity_admission(
    manifest: dict[str, object],
) -> dict[str, object]:
    prior = (
        tuple(_all_comparisons_through_round11())
        + round12_relation_fixtures()
        + round13_bound_comparisons()
    )
    new = nonfree_mutual_kill_split_fixture()
    prior_payloads = tuple(
        _case_semantic_payload_json(comparison) for comparison in prior
    )
    prior_ids = tuple(
        sha256(payload.encode("utf-8")).hexdigest()
        for payload in prior_payloads
    )
    new_payload = _case_semantic_payload_json(new)
    new_id = sha256(new_payload.encode("utf-8")).hexdigest()
    full_ids = prior_ids + (new_id,)
    short_ids = tuple(identifier[:20] for identifier in full_ids)
    canonical = round14_nonfree_mutual_kill_canonical_orbit_code(new)
    if not (
        len(prior) == 2160
        and len(set(prior_payloads)) == 2160
        and len(set(prior_ids)) == 2160
        and len({identifier[:20] for identifier in prior_ids}) == 2160
        and new_id == ROUND14_REGISTERED_FIXTURE_SEMANTIC_SHA256
        and new_id == manifest["fixture"]["name_free_semantic_sha256"]
        and new_id not in set(prior_ids)
        and len(set(full_ids)) == 2161
        and len(set(short_ids)) == 2161
        and canonical["sha256"]
        == ROUND14_REGISTERED_CANONICAL_ORBIT_SHA256
        and canonical == manifest["fixture"]["canonical_orbit_code"]
    ):
        raise AssertionError("Round14 prior/new identity or collision gate failed")
    return {
        "prior_cases": 2160,
        "new_cases": 1,
        "total_cases": 2161,
        "unique_full_name_free_ids": len(set(full_ids)),
        "unique_truncated_20hex_ids": len(set(short_ids)),
        "full_sha256_collision_count": 0,
        "truncated_20hex_collision_count": 0,
        "overlap_count": 0,
        "strict_new": True,
        "new_semantic_sha256": new_id,
        "new_id20": new_id[:20],
        "new_canonical_orbit_sha256": canonical["sha256"],
        "new_canonical_orbit_id20": canonical["id20"],
        "all_gates_pass": True,
    }


def _round14_admission_gate() -> dict[str, object]:
    manifest = _round14_manifest_admission()
    round13 = _round14_round13_baseline_admission()
    identity = _round14_population_identity_admission(manifest["manifest"])
    return {
        "gate_order": [
            "immutable_pure_preregistration_manifest_and_comment",
            "immutable_round13_full_result",
            "prior2160_plus_new1_identity_and_collision",
        ],
        "manifest": manifest,
        "round13_baseline": round13,
        "population_identity": identity,
        "all_gates_pass": True,
    }


def _round14_engine_query(
    manifest: dict[str, object],
) -> dict[str, object]:
    comparison = nonfree_mutual_kill_split_fixture()
    blocks = comparison.block_analyses()
    candidate = v4_candidate_evaluation(
        comparison,
        include_terminal_details=True,
    )
    if not (
        candidate["whole"]["terminal_count"] == 1
        and len(candidate["whole"].get("terminals", [])) == 1
        and len(candidate["per_subset"]) == 3
        and all(
            row["terminal_count"] == 1
            and len(row.get("terminals", [])) == 1
            for row in candidate["per_subset"]
        )
    ):
        raise AssertionError(
            "Round14 engine terminal multiplicity did not match preregistration"
        )
    actual_h1_blocks = [
        {
            "coarse_targets_A": sorted(targets),
            **asdict(analysis),
        }
        for targets, analysis in blocks
    ]
    actual_per_A = [
        {
            "coarse_targets_A": row["coarse_targets_A"],
            "conditions": row["conditions"],
            "terminal_count": row["terminal_count"],
            "trace": row["terminals"][0]["trace"],
        }
        for row in candidate["per_subset"]
    ]
    actual_candidate = {
        "whole_conditions": candidate["whole"]["conditions"],
        "per_nonempty_A": actual_per_A,
        "whole_terminal_count": candidate["whole"]["terminal_count"],
        "whole_trace": candidate["whole"]["terminals"][0]["trace"],
        "aggregate": candidate["aggregate"],
        "vector_C0_through_C6": [
            candidate["aggregate"][f"C{index}*"]
            for index in range(7)
        ],
        "candidate_all": candidate["all"],
    }
    expected = manifest["expected_engine_verification"]
    expected_candidate = expected["v4_candidate"]
    uniform = all(analysis.isomorphism for _, analysis in blocks)
    if not (
        len(blocks) == 3
        and actual_h1_blocks == expected["H1_blocks"]
        and uniform is True
        and expected["uniform"] is True
        and candidate["semantic_id"] == V4_SEMANTIC_ID
        and candidate["semantic_sha256"] == V4_SEMANTIC_SHA256
        and actual_candidate == expected_candidate
        and candidate["all"] is False
        and expected["expected_direction"]
        == "uniform_and_not_candidate"
        and expected["expected_new_verdict_if_reproduced"]
        == "CSTAR-not-necessary"
        and expected["expectation_is_not_engine_observation"] is True
    ):
        raise AssertionError(
            "Round14 engine did not reproduce the preregistered verification"
        )

    failing_A = next(
        row
        for row in actual_per_A
        if not all(row["conditions"].values())
    )
    exact_h1 = next(
        row
        for row in actual_h1_blocks
        if row["coarse_targets_A"] == failing_A["coarse_targets_A"]
    )
    witness = {
        "id": ROUND14_REGISTERED_FIXTURE_SEMANTIC_SHA256,
        "id20": ROUND14_REGISTERED_FIXTURE_ID20,
        "canonical_nonisomorphic_id": (
            ROUND14_REGISTERED_CANONICAL_ORBIT_SHA256
        ),
        "canonical_nonisomorphic_id20": (
            ROUND14_REGISTERED_CANONICAL_ORBIT_ID20
        ),
        "name": comparison.name,
        "direction": "uniform_and_not_candidate",
        "minimal_failing_A": failing_A["coarse_targets_A"],
        "exact_h1": exact_h1,
        "candidate_aggregate": candidate["aggregate"],
        "candidate_failure_scope": "nonempty-A",
        "candidate_failure_conditions": failing_A["conditions"],
        "whole_candidate_failure_conditions": candidate["whole"][
            "conditions"
        ],
    }
    return {
        "fixture": {
            "name": comparison.name,
            "semantic_sha256": ROUND14_REGISTERED_FIXTURE_SEMANTIC_SHA256,
            "id20": ROUND14_REGISTERED_FIXTURE_ID20,
            "canonical_orbit_sha256": (
                ROUND14_REGISTERED_CANONICAL_ORBIT_SHA256
            ),
            "canonical_orbit_id20": (
                ROUND14_REGISTERED_CANONICAL_ORBIT_ID20
            ),
        },
        "H1_blocks": actual_h1_blocks,
        "uniform": uniform,
        "v4_candidate": actual_candidate,
        "direction": "uniform_and_not_candidate",
        "witness": witness,
        "new_A_block_queries": len(blocks),
        "all_nonempty_A_evaluated": True,
        "sampling": False,
        "early_stop": False,
        "engine_reproduced_preregistered_expectations": True,
    }


def round14_report() -> dict[str, object]:
    admission = _round14_admission_gate()
    manifest = admission["manifest"]["manifest"]
    query = _round14_engine_query(manifest)
    new_verdicts = ["CSTAR-not-necessary"]
    new_canonical_counterexamples = [
        ROUND14_REGISTERED_CANONICAL_ORBIT_SHA256
    ]
    candidate_semantic_change = False
    additional_calibration_fixes: list[str] = []
    progress = bool(
        new_verdicts
        or new_canonical_counterexamples
        or candidate_semantic_change
        or additional_calibration_fixes
    )
    if not progress:
        raise AssertionError("Round14 reproduced counterexample made no progress")
    return {
        "round": "R2-round-14",
        "valid": True,
        "preregistration": {
            "issue_comment": ROUND14_PREREGISTERED_ISSUE_COMMENT,
            "created_at": ROUND14_PREREGISTERED_CREATED_AT,
            "updated_at": ROUND14_PREREGISTERED_UPDATED_AT,
            "manifest_sha256": ROUND14_REGISTERED_MANIFEST_SHA256,
            "discovery_mode": (
                "pre-query-human-static-exact-verification"
            ),
            "blind_search": False,
        },
        "admission": admission,
        "candidate": {
            "semantic_id": V4_SEMANTIC_ID,
            "semantic_sha256": V4_SEMANTIC_SHA256,
            "calibration_sha256": (
                V4_CALIBRATION_REGISTERED_CANONICAL_SHA256
            ),
            "calibration_bytes": (
                V4_CALIBRATION_REGISTERED_CANONICAL_BYTES
            ),
            "semantic_change": candidate_semantic_change,
            "calibration_mutated": False,
            "status": "invalid",
            "invalidated_semantic_id": V4_SEMANTIC_ID,
            "valid_after_round14": False,
            "invalidated_by_reproduced_necessity_counterexample": True,
        },
        "population": {
            **admission["population_identity"],
            "new_A_block_queries": query["new_A_block_queries"],
            "all_new_cases_and_nonempty_A_evaluated": True,
            "sampling": query["sampling"],
            "early_stop": query["early_stop"],
        },
        "queries": {
            "uniform_and_not_candidate_count": 1,
            "candidate_and_nonuniform_count": 0,
            "uniform_and_not_candidate": [query["witness"]],
            "candidate_and_nonuniform": [],
            "new_counterexample_count": 1,
        },
        "exact_verification": query,
        "progress_audit": {
            "entry_streak": 0,
            "new_verdicts": new_verdicts,
            "new_canonical_nonisomorphic_counterexamples": (
                new_canonical_counterexamples
            ),
            "candidate_semantic_change": candidate_semantic_change,
            "additional_calibration_fixes": additional_calibration_fixes,
            "progress": progress,
            "streak_after_round": 0,
        },
        "stop_audit": {
            "stop_condition_A_completion": False,
            "stop_condition_B_finite_exhaustion": False,
            "stop_condition_C_two_valid_same_blocker_no_progress": False,
            "reproduced_counterexample_is_progress": True,
        },
        "coverage_limit": (
            "Exactly the immutable prior 2,160 name-free semantic cases plus "
            "the single preregistered NONFREE-MUTUAL-KILL-SPLIT identity "
            "two-chart case and all three of its nonempty Target blocks; no "
            "larger mutual nonfree face system or support family is covered."
        ),
    }


V5_SEMANTIC_ID = "R2-CSTAR-COORDINATE-DOUBLED-CYCLE-v5"
V5_SPEC = "\n".join(
    (
        "base:retain every support-active scope, v4 joint unit and fine-only packet, post-collapse C0-C4, guarded C5-C6, and universal terminal quantification",
        "coordinate-domain:choose a nonempty set S of retained coarse self-loop edges and let K(S) be every retained coarse FaceTwin class whose raw ordered boundary meets S",
        "coordinate-coarse:each class K in K(S) has full signed beta support the singleton t(K) in S with coefficient absolute value one, and t is surjective onto S",
        "coordinate-multiplicity:FaceTwin member multiplicity never adds relation rows; the packet removes each selected static class once",
        "coordinate-preimage:each retained fine class meeting selected mapped members maps every actual member into one selected coarse class; None, outside, or inter-class mixtures reject the packet",
        "coordinate-fine:each selected fine preimage class has full signed beta support the singleton p(L) with coefficient absolute value one and edgeMap(p(L))=t(K_L)",
        "coordinate-residual:after provisionally removing all selected fine classes and pivots, every other retained fine edge mapped into S is face-free and a nonselfloop bridge, and all are removed together",
        "coordinate-empty:an empty fine preimage is legal subject to the same residual mapped-edge check",
        "coordinate-safety:every selected relation is literally one signed unit coordinate and surjectivity of t removes all of S without a matrix oracle",
        "doubled-coarse:choose distinct retained coarse self-loops S of size at least two whose incident retained classes are exactly boundaries (e_i,e_next,e_i) forming one directed simple cycle",
        "doubled-preimage:selected fine preimage classes form a disjoint union of directed covering cycles with exact boundaries (u,v,u), self-loop sheet edges, and incidence-preserving edge and face maps",
        "doubled-residual:sheet edges occur in no retained outside class; every remaining fine edge mapped into S is face-free and a nonselfloop bridge, while empty preimage is legal",
        "doubled-safety:over Q the exact relations e_next=2e_i imply (2^n-1)e_0=0; the predicate recognizes only the closed directed incidence atom and computes no rank or determinant",
        "composition:apply exactly one v4, coordinate-dependency, or closed-doubled-cycle packet variant per transition, memoize retained-cell states, and require every irreducible terminal",
        "safety-symbols:the packet recognizers and candidate read no rank, determinant, global or A-block H1, global analysis, comparison analysis, or is_uniform result",
        "C3-exception:only the preregistered local C3 fiber cycle-versus-boundary linear algebra remains in the clause evaluator",
    )
)
V5_SEMANTIC_SHA256 = sha256(V5_SPEC.encode("ascii")).hexdigest()
V5_PACKET_FORBIDDEN_SYMBOLS = (
    "analyze_h1",
    "block_analyses",
    "comparison_rank",
    "determinant",
    "is_uniform",
    "rank",
)
V5_DEPENDENCY_AUDIT_NEW_HELPER_CALL_CLOSURE = (
    "_v5_joint_state_adapter",
    "_v5_assert_state_closure",
    "_v5_nonempty_edge_subsets",
    "_v5_beta_support",
    "_v5_selected_preimage_classes",
    "_v5_removable_residual_edges",
    "_v5_v4_packets",
    "_v5_coordinate_packets",
    "_v5_coarse_doubled_cycle_witnesses",
    "_v5_doubled_cycle_packets",
    "_v5_packet_variants",
    "_apply_v5_packet",
    "v5_terminal_states",
    "_v5_terminal_reductions",
    "_v5_packet_summary",
    "_v5_terminal_summary",
    "v5_candidate_evaluation",
)

ROUND15_BOUND_SEMANTIC_ID = "R15-V5-SEMANTIC-SAFETY-CALIBRATION-v1"
ROUND15_BOUND_SPEC = "\n".join(
    (
        "purpose:pure pre-query semantic-safety preregistration for one fixed v5 successor and six exact structural controls",
        "candidate:the sole successor is R2-CSTAR-COORDINATE-DOUBLED-CYCLE-v5 with coordinate-dependency and closed doubled-cycle packets added to immutable v4",
        "fixtures:NONFREE-MUTUAL-KILL-SPLIT, WEIGHTED-2, TERNARY-CYCLE-3, TERNARY-CYCLE-6, SINGULAR-PERFECT-MATCH-3, and WEIGHTED-ORPHAN-SELFLOOP",
        "positive-controls:MUTUAL is removed only by coordinate dependency and WEIGHTED-2 only by the closed doubled-cycle atom",
        "negative-controls:TERNARY-CYCLE-3 is a known uniform candidate failure, while TERNARY-CYCLE-6, SINGULAR-PERFECT-MATCH-3, and WEIGHTED-ORPHAN-SELFLOOP must remain rejected",
        "oracle-boundary:H1 dimensions and candidate vectors are hand expectations only and are not evaluated by this pure manifest",
        "dependency:pure arrays, derived supports, name-free semantic IDs, fixed-grammar canonical orbit IDs, and prior-union checks only",
        "parent:Round14 exact reproduced necessity counterexample invalidated v4 and reset the no-progress streak to zero",
        "admission:none in this patch; no Round15 query or report exists before a later registered Issue comment",
    )
)
ROUND15_BOUND_SEMANTIC_SHA256 = sha256(
    ROUND15_BOUND_SPEC.encode("ascii")
).hexdigest()
ROUND15_PARENT_ROUND14_PAYLOAD_SHA256 = (
    "17c9907928a63cdf97e474e7f8813447601010ede07bbe7a43b525ef8551b450"
)
ROUND15_PARENT_ROUND14_CANONICAL_BYTES = 22_818
ROUND15_PARENT_ROUND14_RESULT_ISSUE_COMMENT = 5235064396
ROUND15_PARENT_ROUND14_RESULT_CREATED_AT = "2026-08-10T01:55:17Z"
ROUND15_PARENT_ROUND14_RESULT_UPDATED_AT = "2026-08-10T01:55:17Z"
ROUND15_PARENT_G107_SYNC_ISSUE_COMMENT = 5235067306
ROUND15_PARENT_POPULATION = 2161
ROUND15_PREREGISTERED_ISSUE_COMMENT = 5235347217
ROUND15_PREREGISTERED_CREATED_AT = "2026-08-10T02:51:13Z"
ROUND15_PREREGISTERED_UPDATED_AT = "2026-08-10T02:51:13Z"
ROUND15_REGISTERED_MANIFEST_SHA256 = (
    "e5f2d6630ee2f37de409f5e2c0757eed17b24509ca3cd3f7d924c130b6219c3b"
)
ROUND15_REGISTERED_V5_CALIBRATION_SHA256 = (
    "a9b23c5d3689868185b5c3fb1f4ab29a6e0f6529f45ed97be77f89be99d2a776"
)
ROUND15_REGISTERED_V5_CALIBRATION_BYTES = 873


@dataclass(frozen=True, order=True)
class V5CollapsePacket:
    kind: str
    coarse_edges: tuple[int, ...]
    coarse_face_classes: tuple[int, ...]
    fine_face_classes: tuple[int, ...]
    fine_pivot_edges: tuple[int, ...]
    residual_fine_edges: tuple[int, ...]
    coarse_relation_witnesses: tuple[tuple[int, ...], ...]
    fine_relation_witnesses: tuple[tuple[int, ...], ...]


@dataclass(frozen=True)
class V5CollapseState:
    retained_coarse_edges: tuple[int, ...]
    retained_coarse_face_classes: tuple[int, ...]
    retained_fine_edges: tuple[int, ...]
    retained_fine_face_classes: tuple[int, ...]
    trace: tuple[V5CollapsePacket, ...]

    @property
    def cell_key(
        self,
    ) -> tuple[tuple[int, ...], tuple[int, ...], tuple[int, ...], tuple[int, ...]]:
        return (
            self.retained_coarse_edges,
            self.retained_coarse_face_classes,
            self.retained_fine_edges,
            self.retained_fine_face_classes,
        )


def _v5_joint_state_adapter(state: V5CollapseState) -> JointCollapseState:
    return JointCollapseState(
        retained_coarse_edges=state.retained_coarse_edges,
        retained_coarse_face_classes=state.retained_coarse_face_classes,
        retained_fine_edges=state.retained_fine_edges,
        retained_fine_face_classes=state.retained_fine_face_classes,
        trace=(),
    )


def _v5_assert_state_closure(
    scope: ScopedComparison,
    coarse_classes: tuple[FaceClass, ...],
    fine_classes: tuple[FaceClass, ...],
    state: V5CollapseState,
) -> None:
    _assert_joint_state_closure(
        scope,
        coarse_classes,
        fine_classes,
        _v5_joint_state_adapter(state),
    )


def _v5_nonempty_edge_subsets(edges: tuple[int, ...]) -> Iterator[tuple[int, ...]]:
    for mask in range(1, 1 << len(edges)):
        yield tuple(
            edge for index, edge in enumerate(edges) if mask & (1 << index)
        )


def _v5_beta_support(
    boundary: tuple[int, int, int],
    retained_edges: set[int],
) -> tuple[tuple[int, int], ...]:
    return tuple(
        (edge, coefficient)
        for edge in sorted(set(boundary))
        if edge in retained_edges
        if (coefficient := _signed_face_coefficient(boundary, edge)) != 0
    )


def _v5_selected_preimage_classes(
    scope: ScopedComparison,
    coarse_classes: tuple[FaceClass, ...],
    fine_classes: tuple[FaceClass, ...],
    selected_coarse_classes: tuple[int, ...],
    retained_fine_classes: set[int],
) -> tuple[tuple[int, int], ...] | None:
    member_to_class = {
        face: class_index
        for class_index in selected_coarse_classes
        for face in coarse_classes[class_index].members
    }
    preimages: list[tuple[int, int]] = []
    for fine_class_index in sorted(retained_fine_classes):
        mapped_faces = tuple(
            scope.morphism.face_map[face]
            for face in fine_classes[fine_class_index].members
        )
        hits = {
            member_to_class[mapped]
            for mapped in mapped_faces
            if mapped in member_to_class
        }
        if not hits:
            continue
        if len(hits) != 1 or any(
            mapped is None or mapped not in member_to_class
            for mapped in mapped_faces
        ):
            return None
        preimages.append((fine_class_index, next(iter(hits))))
    return tuple(preimages)


def _v5_removable_residual_edges(
    scope: ScopedComparison,
    fine_classes: tuple[FaceClass, ...],
    retained_fine_classes: set[int],
    retained_fine_edges: set[int],
    coarse_edges: set[int],
) -> tuple[int, ...] | None:
    residual = tuple(
        edge
        for edge in sorted(retained_fine_edges)
        if scope.morphism.edge_map[edge] in coarse_edges
    )
    if any(
        _raw_occurrence_classes(
            fine_classes,
            retained_fine_classes,
            edge,
        )
        for edge in residual
    ):
        return None
    if any(
        scope.fine.nerve.edges[edge][0]
        == scope.fine.nerve.edges[edge][1]
        or _path_without_edge(
            scope.fine.nerve,
            retained_fine_edges,
            edge,
        )
        for edge in residual
    ):
        return None
    return residual


def _v5_v4_packets(
    scope: ScopedComparison,
    coarse_classes: tuple[FaceClass, ...],
    fine_classes: tuple[FaceClass, ...],
    state: V5CollapseState,
) -> tuple[V5CollapsePacket, ...]:
    packets = []
    for packet in _joint_packet_variants(
        scope,
        coarse_classes,
        fine_classes,
        _v5_joint_state_adapter(state),
    ):
        coarse_edges = (
            (packet.coarse_edge,) if packet.coarse_edge >= 0 else ()
        )
        coarse_classes_removed = (
            (packet.coarse_face_class,)
            if packet.coarse_face_class >= 0
            else ()
        )
        fine_pivots = tuple(
            sorted(edge for _, edge in packet.pivot_assignments)
        )
        packets.append(
            V5CollapsePacket(
                kind=f"v4-{packet.kind}",
                coarse_edges=coarse_edges,
                coarse_face_classes=coarse_classes_removed,
                fine_face_classes=packet.fine_face_classes,
                fine_pivot_edges=fine_pivots,
                residual_fine_edges=packet.orphan_fine_edges,
                coarse_relation_witnesses=(
                    (
                        (
                            packet.coarse_face_class,
                            packet.coarse_edge,
                        ),
                    )
                    if packet.coarse_edge >= 0
                    else ()
                ),
                fine_relation_witnesses=tuple(
                    (face_class, edge)
                    for face_class, edge in packet.pivot_assignments
                ),
            )
        )
    return tuple(packets)


def _v5_coordinate_packets(
    scope: ScopedComparison,
    coarse_classes: tuple[FaceClass, ...],
    fine_classes: tuple[FaceClass, ...],
    state: V5CollapseState,
) -> tuple[V5CollapsePacket, ...]:
    coarse_edges = set(state.retained_coarse_edges)
    coarse_face_classes = set(state.retained_coarse_face_classes)
    fine_edges = set(state.retained_fine_edges)
    fine_face_classes = set(state.retained_fine_face_classes)
    coarse_selfloops = tuple(
        edge
        for edge in state.retained_coarse_edges
        if scope.coarse.nerve.edges[edge][0]
        == scope.coarse.nerve.edges[edge][1]
    )
    packets: set[V5CollapsePacket] = set()
    for selected_edges_tuple in _v5_nonempty_edge_subsets(coarse_selfloops):
        selected_edges = set(selected_edges_tuple)
        selected_classes = tuple(
            class_index
            for class_index in sorted(coarse_face_classes)
            if set(coarse_classes[class_index].boundary) & selected_edges
        )
        if not selected_classes:
            continue
        coarse_targets: dict[int, int] = {}
        coarse_witnesses: list[tuple[int, ...]] = []
        valid = True
        for class_index in selected_classes:
            support = _v5_beta_support(
                coarse_classes[class_index].boundary,
                coarse_edges,
            )
            if (
                len(support) != 1
                or support[0][0] not in selected_edges
                or abs(support[0][1]) != 1
            ):
                valid = False
                break
            target, coefficient = support[0]
            coarse_targets[class_index] = target
            coarse_witnesses.append((class_index, target, coefficient))
        if not valid or set(coarse_targets.values()) != selected_edges:
            continue

        preimages = _v5_selected_preimage_classes(
            scope,
            coarse_classes,
            fine_classes,
            selected_classes,
            fine_face_classes,
        )
        if preimages is None:
            continue
        fine_pivots: list[int] = []
        fine_witnesses: list[tuple[int, ...]] = []
        for fine_class_index, coarse_class_index in preimages:
            support = _v5_beta_support(
                fine_classes[fine_class_index].boundary,
                fine_edges,
            )
            if len(support) != 1 or abs(support[0][1]) != 1:
                valid = False
                break
            pivot, coefficient = support[0]
            if (
                scope.morphism.edge_map[pivot]
                != coarse_targets[coarse_class_index]
            ):
                valid = False
                break
            fine_pivots.append(pivot)
            fine_witnesses.append(
                (
                    fine_class_index,
                    pivot,
                    coefficient,
                    coarse_class_index,
                )
            )
        if not valid:
            continue

        selected_fine_classes = {fine_class for fine_class, _ in preimages}
        provisional_classes = fine_face_classes - selected_fine_classes
        provisional_edges = fine_edges - set(fine_pivots)
        if any(
            _raw_occurrence_classes(
                fine_classes,
                provisional_classes,
                pivot,
            )
            for pivot in set(fine_pivots)
        ):
            continue
        residual = _v5_removable_residual_edges(
            scope,
            fine_classes,
            provisional_classes,
            provisional_edges,
            selected_edges,
        )
        if residual is None:
            continue
        packets.add(
            V5CollapsePacket(
                kind="coordinate-dependency",
                coarse_edges=selected_edges_tuple,
                coarse_face_classes=selected_classes,
                fine_face_classes=tuple(sorted(selected_fine_classes)),
                fine_pivot_edges=tuple(sorted(set(fine_pivots))),
                residual_fine_edges=residual,
                coarse_relation_witnesses=tuple(coarse_witnesses),
                fine_relation_witnesses=tuple(fine_witnesses),
            )
        )
    return tuple(sorted(packets))


def _v5_coarse_doubled_cycle_witnesses(
    scope: ScopedComparison,
    coarse_classes: tuple[FaceClass, ...],
    retained_coarse_classes: set[int],
    selected_edges: tuple[int, ...],
) -> tuple[tuple[int, ...], tuple[tuple[int, ...], ...]] | None:
    selected = set(selected_edges)
    selected_classes = tuple(
        class_index
        for class_index in sorted(retained_coarse_classes)
        if set(coarse_classes[class_index].boundary) & selected
    )
    if len(selected_classes) != len(selected_edges):
        return None
    outgoing: dict[int, int] = {}
    incoming: dict[int, int] = {}
    class_witnesses: list[tuple[int, ...]] = []
    for class_index in selected_classes:
        source, target, repeated = coarse_classes[class_index].boundary
        if not (
            source == repeated
            and source in selected
            and target in selected
            and source != target
            and source not in outgoing
            and target not in incoming
        ):
            return None
        outgoing[source] = target
        incoming[target] = source
        class_witnesses.append((class_index, source, target))
    if set(outgoing) != selected or set(incoming) != selected:
        return None
    start = min(selected)
    current = start
    visited = []
    for _ in selected_edges:
        if current in visited:
            return None
        visited.append(current)
        current = outgoing[current]
    if current != start or set(visited) != selected:
        return None
    ordered_classes = tuple(
        next(
            class_index
            for class_index, source, _ in class_witnesses
            if source == edge
        )
        for edge in visited
    )
    ordered_witnesses = tuple(
        next(
            witness
            for witness in class_witnesses
            if witness[1] == edge
        )
        for edge in visited
    )
    return ordered_classes, ordered_witnesses


def _v5_doubled_cycle_packets(
    scope: ScopedComparison,
    coarse_classes: tuple[FaceClass, ...],
    fine_classes: tuple[FaceClass, ...],
    state: V5CollapseState,
) -> tuple[V5CollapsePacket, ...]:
    coarse_face_classes = set(state.retained_coarse_face_classes)
    fine_edges = set(state.retained_fine_edges)
    fine_face_classes = set(state.retained_fine_face_classes)
    coarse_selfloops = tuple(
        edge
        for edge in state.retained_coarse_edges
        if scope.coarse.nerve.edges[edge][0]
        == scope.coarse.nerve.edges[edge][1]
    )
    packets: set[V5CollapsePacket] = set()
    for selected_edges in _v5_nonempty_edge_subsets(coarse_selfloops):
        if len(selected_edges) < 2:
            continue
        coarse_cycle = _v5_coarse_doubled_cycle_witnesses(
            scope,
            coarse_classes,
            coarse_face_classes,
            selected_edges,
        )
        if coarse_cycle is None:
            continue
        selected_classes, coarse_witnesses = coarse_cycle
        coarse_transition = {
            class_index: (source, target)
            for class_index, source, target in coarse_witnesses
        }
        preimages = _v5_selected_preimage_classes(
            scope,
            coarse_classes,
            fine_classes,
            selected_classes,
            fine_face_classes,
        )
        if preimages is None:
            continue

        outgoing: dict[int, int] = {}
        incoming: dict[int, int] = {}
        fine_witnesses: list[tuple[int, ...]] = []
        valid = True
        for fine_class_index, coarse_class_index in preimages:
            source, target, repeated = fine_classes[
                fine_class_index
            ].boundary
            coarse_source, coarse_target = coarse_transition[
                coarse_class_index
            ]
            if not (
                source == repeated
                and source != target
                and scope.fine.nerve.edges[source][0]
                == scope.fine.nerve.edges[source][1]
                and scope.fine.nerve.edges[target][0]
                == scope.fine.nerve.edges[target][1]
                and scope.morphism.edge_map[source] == coarse_source
                and scope.morphism.edge_map[target] == coarse_target
                and source not in outgoing
                and target not in incoming
            ):
                valid = False
                break
            outgoing[source] = target
            incoming[target] = source
            fine_witnesses.append(
                (
                    fine_class_index,
                    source,
                    target,
                    coarse_class_index,
                )
            )
        if not valid:
            continue
        sheet_edges = set(outgoing) | set(incoming)
        if preimages and not (
            set(outgoing) == sheet_edges == set(incoming)
        ):
            continue
        if any(edge not in fine_edges for edge in sheet_edges):
            continue
        selected_fine_classes = {fine_class for fine_class, _ in preimages}
        provisional_classes = fine_face_classes - selected_fine_classes
        provisional_edges = fine_edges - sheet_edges
        if any(
            _raw_occurrence_classes(
                fine_classes,
                provisional_classes,
                edge,
            )
            for edge in sheet_edges
        ):
            continue
        residual = _v5_removable_residual_edges(
            scope,
            fine_classes,
            provisional_classes,
            provisional_edges,
            set(selected_edges),
        )
        if residual is None:
            continue
        packets.add(
            V5CollapsePacket(
                kind="closed-doubled-cycle",
                coarse_edges=selected_edges,
                coarse_face_classes=selected_classes,
                fine_face_classes=tuple(sorted(selected_fine_classes)),
                fine_pivot_edges=tuple(sorted(sheet_edges)),
                residual_fine_edges=residual,
                coarse_relation_witnesses=coarse_witnesses,
                fine_relation_witnesses=tuple(sorted(fine_witnesses)),
            )
        )
    return tuple(sorted(packets))


def _v5_packet_variants(
    scope: ScopedComparison,
    coarse_classes: tuple[FaceClass, ...],
    fine_classes: tuple[FaceClass, ...],
    state: V5CollapseState,
) -> tuple[V5CollapsePacket, ...]:
    _v5_assert_state_closure(scope, coarse_classes, fine_classes, state)
    packets = set(
        _v5_v4_packets(scope, coarse_classes, fine_classes, state)
    )
    packets.update(
        _v5_coordinate_packets(scope, coarse_classes, fine_classes, state)
    )
    packets.update(
        _v5_doubled_cycle_packets(
            scope,
            coarse_classes,
            fine_classes,
            state,
        )
    )
    return tuple(sorted(packets))


def _apply_v5_packet(
    scope: ScopedComparison,
    coarse_classes: tuple[FaceClass, ...],
    fine_classes: tuple[FaceClass, ...],
    state: V5CollapseState,
    packet: V5CollapsePacket,
) -> V5CollapseState:
    coarse_edges = set(state.retained_coarse_edges)
    coarse_face_classes = set(state.retained_coarse_face_classes)
    fine_edges = set(state.retained_fine_edges)
    fine_face_classes = set(state.retained_fine_face_classes)
    coarse_edges.difference_update(packet.coarse_edges)
    coarse_face_classes.difference_update(packet.coarse_face_classes)
    fine_face_classes.difference_update(packet.fine_face_classes)
    fine_edges.difference_update(packet.fine_pivot_edges)
    fine_edges.difference_update(packet.residual_fine_edges)
    result = V5CollapseState(
        retained_coarse_edges=tuple(sorted(coarse_edges)),
        retained_coarse_face_classes=tuple(sorted(coarse_face_classes)),
        retained_fine_edges=tuple(sorted(fine_edges)),
        retained_fine_face_classes=tuple(sorted(fine_face_classes)),
        trace=state.trace + (packet,),
    )
    if result.cell_key == state.cell_key:
        raise AssertionError("v5 collapse packet removed no retained cell")
    _v5_assert_state_closure(scope, coarse_classes, fine_classes, result)
    return result


def v5_terminal_states(scope: ScopedComparison) -> tuple[V5CollapseState, ...]:
    coarse_classes = _face_classes(scope.coarse)
    fine_classes = _face_classes(scope.fine)
    initial = V5CollapseState(
        retained_coarse_edges=tuple(range(len(scope.coarse.nerve.edges))),
        retained_coarse_face_classes=tuple(range(len(coarse_classes))),
        retained_fine_edges=tuple(range(len(scope.fine.nerve.edges))),
        retained_fine_face_classes=tuple(range(len(fine_classes))),
        trace=(),
    )
    _v5_assert_state_closure(scope, coarse_classes, fine_classes, initial)
    memo: dict[
        tuple[tuple[int, ...], tuple[int, ...], tuple[int, ...], tuple[int, ...]],
        dict[
            tuple[tuple[int, ...], tuple[int, ...], tuple[int, ...], tuple[int, ...]],
            tuple[V5CollapsePacket, ...],
        ],
    ] = {}

    def solve(
        key: tuple[
            tuple[int, ...],
            tuple[int, ...],
            tuple[int, ...],
            tuple[int, ...],
        ],
    ) -> dict[
        tuple[tuple[int, ...], tuple[int, ...], tuple[int, ...], tuple[int, ...]],
        tuple[V5CollapsePacket, ...],
    ]:
        if key in memo:
            return memo[key]
        current = V5CollapseState(*key, trace=())
        packets = _v5_packet_variants(
            scope,
            coarse_classes,
            fine_classes,
            current,
        )
        if not packets:
            memo[key] = {key: ()}
            return memo[key]
        terminals: dict[
            tuple[tuple[int, ...], tuple[int, ...], tuple[int, ...], tuple[int, ...]],
            tuple[V5CollapsePacket, ...],
        ] = {}
        for packet in packets:
            next_state = _apply_v5_packet(
                scope,
                coarse_classes,
                fine_classes,
                current,
                packet,
            )
            for terminal_key, suffix in solve(next_state.cell_key).items():
                trace = (packet,) + suffix
                previous = terminals.get(terminal_key)
                if previous is None or trace < previous:
                    terminals[terminal_key] = trace
        memo[key] = terminals
        return terminals

    terminals = tuple(
        V5CollapseState(*key, trace=trace)
        for key, trace in sorted(solve(initial.cell_key).items())
    )
    if not terminals:
        raise AssertionError("v5 collapse produced no irreducible terminal")
    for terminal in terminals:
        _v5_assert_state_closure(
            scope,
            coarse_classes,
            fine_classes,
            terminal,
        )
        if _v5_packet_variants(
            scope,
            coarse_classes,
            fine_classes,
            terminal,
        ):
            raise AssertionError("v5 collapse returned a reducible terminal")
    return terminals


def _v5_terminal_reductions(
    scope: ScopedComparison,
) -> tuple[tuple[V5CollapseState, ReducedSide, ReducedSide], ...]:
    coarse_classes = _face_classes(scope.coarse)
    fine_classes = _face_classes(scope.fine)
    return tuple(
        (
            state,
            _joint_reduced_side(
                scope.coarse,
                coarse_classes,
                state.retained_coarse_edges,
                state.retained_coarse_face_classes,
            ),
            _joint_reduced_side(
                scope.fine,
                fine_classes,
                state.retained_fine_edges,
                state.retained_fine_face_classes,
            ),
        )
        for state in v5_terminal_states(scope)
    )


def _v5_packet_summary(packet: V5CollapsePacket) -> dict[str, object]:
    return {
        "kind": packet.kind,
        "coarse_edges": list(packet.coarse_edges),
        "coarse_face_classes": list(packet.coarse_face_classes),
        "fine_face_classes": list(packet.fine_face_classes),
        "fine_pivot_edges": list(packet.fine_pivot_edges),
        "residual_fine_edges": list(packet.residual_fine_edges),
        "coarse_relation_witnesses": [
            list(witness) for witness in packet.coarse_relation_witnesses
        ],
        "fine_relation_witnesses": [
            list(witness) for witness in packet.fine_relation_witnesses
        ],
    }


def _v5_terminal_summary(
    state: V5CollapseState,
    coarse: ReducedSide,
    fine: ReducedSide,
    conditions: dict[str, bool],
    direct_lifttwin: dict[str, object] | None = None,
    guarded_coarse_edges: tuple[int, ...] | None = None,
) -> dict[str, object]:
    result: dict[str, object] = {
        "conditions": conditions,
        "trace": [_v5_packet_summary(packet) for packet in state.trace],
        "coarse_reduction": _reduction_summary(coarse),
        "fine_reduction": _reduction_summary(fine),
        "retained_map_closure": True,
    }
    if direct_lifttwin is not None:
        result["direct_lifttwin"] = direct_lifttwin
    if guarded_coarse_edges is not None:
        result["C5_C6_guarded_coarse_edges"] = list(
            guarded_coarse_edges
        )
    return result


def v5_candidate_evaluation(
    comparison: UniformComparison,
    *,
    include_terminal_details: bool = True,
) -> dict[str, object]:
    whole_targets = frozenset(range(comparison.coarse_target_count))
    whole = _a_scope(comparison, whole_targets)
    whole_reductions = _v5_terminal_reductions(whole)
    whole_conditions: list[dict[str, bool]] = []
    whole_details: list[dict[str, object]] = []
    for state, coarse, fine in whole_reductions:
        c0 = _c0(whole, coarse, fine, comparison.factor_pi)
        c5, c6, twin_details, guarded_coarse_edges = _v4_c5_c6(
            whole,
            coarse,
            fine,
        )
        conditions = {"C0*": c0, "C5*": c5, "C6*": c6}
        whole_conditions.append(conditions)
        if include_terminal_details:
            whole_details.append(
                _v5_terminal_summary(
                    state,
                    coarse,
                    fine,
                    conditions,
                    twin_details,
                    guarded_coarse_edges,
                )
            )

    aggregate = {
        clause: all(conditions[clause] for conditions in whole_conditions)
        for clause in ("C0*", "C5*", "C6*")
    }
    aggregate.update(
        {"C1*": True, "C2*": True, "C3*": True, "C4*": True}
    )
    per_subset: list[dict[str, object]] = []
    for targets in nonempty_subsets(comparison.coarse_target_count):
        scope = _a_scope(comparison, targets)
        reductions = _v5_terminal_reductions(scope)
        terminal_conditions: list[dict[str, bool]] = []
        terminal_details: list[dict[str, object]] = []
        for state, coarse, fine in reductions:
            conditions = {
                "C1*": _c1(scope, coarse, fine),
                "C2*": _c2(scope, coarse, fine),
                "C3*": _c3(scope, fine),
                "C4*": _c4(scope, coarse, fine),
            }
            terminal_conditions.append(conditions)
            if include_terminal_details:
                terminal_details.append(
                    _v5_terminal_summary(state, coarse, fine, conditions)
                )
        universal = {
            clause: all(
                conditions[clause] for conditions in terminal_conditions
            )
            for clause in ("C1*", "C2*", "C3*", "C4*")
        }
        for clause, value in universal.items():
            aggregate[clause] = aggregate[clause] and value
        subset_result: dict[str, object] = {
            "coarse_targets_A": sorted(targets),
            "terminal_count": len(reductions),
            "conditions": universal,
        }
        if include_terminal_details:
            subset_result["terminals"] = terminal_details
        per_subset.append(subset_result)

    ordered_aggregate = {
        f"C{index}*": aggregate[f"C{index}*"] for index in range(7)
    }
    whole_result: dict[str, object] = {
        "terminal_count": len(whole_reductions),
        "conditions": {
            clause: ordered_aggregate[clause]
            for clause in ("C0*", "C5*", "C6*")
        },
    }
    if include_terminal_details:
        whole_result["terminals"] = whole_details
    return {
        "semantic_id": V5_SEMANTIC_ID,
        "semantic_sha256": V5_SEMANTIC_SHA256,
        "aggregate": ordered_aggregate,
        "all": all(ordered_aggregate.values()),
        "whole": whole_result,
        "per_subset": per_subset,
        "terminal_quantifier": "forall",
        "candidate_predicate_reads_global_or_A_block_H1": False,
        "candidate_predicate_uses_preregistered_local_C3_linear_algebra": True,
    }


def _round15_identity_split_fixture(
    name: str,
    neutral_edge_count: int,
    faces: tuple[tuple[int, int, int], ...],
) -> UniformComparison:
    nerve = Nerve(
        2,
        ((0, 0),) + tuple((1, 1) for _ in range(neutral_edge_count)),
        faces,
    )
    return UniformComparison(
        name=name,
        morphism=NerveMorphism(
            coarse=nerve,
            fine=nerve,
            vertex_map=(0, 1),
            edge_map=tuple(range(neutral_edge_count + 1)),
            face_map=tuple(range(len(faces))),
        ),
        coarse_target_count=2,
        fine_target_count=3,
        factor_pi=(0, 0, 1),
        coarse_chart_supports=(
            frozenset((0,)),
            frozenset((0, 1)),
        ),
        fine_chart_supports=(
            frozenset((0, 1)),
            frozenset((2,)),
        ),
    )


def weighted_2_fixture() -> UniformComparison:
    return _round15_identity_split_fixture(
        "WEIGHTED-2",
        2,
        ((1, 2, 1), (2, 1, 2)),
    )


def ternary_cycle_3_fixture() -> UniformComparison:
    return _round15_identity_split_fixture(
        "TERNARY-CYCLE-3",
        3,
        ((1, 2, 3), (2, 3, 1), (3, 1, 2)),
    )


def ternary_cycle_6_fixture() -> UniformComparison:
    return _round15_identity_split_fixture(
        "TERNARY-CYCLE-6",
        6,
        (
            (1, 2, 3),
            (2, 3, 4),
            (3, 4, 5),
            (4, 5, 6),
            (5, 6, 1),
            (6, 1, 2),
        ),
    )


def singular_perfect_match_3_fixture() -> UniformComparison:
    return _round15_identity_split_fixture(
        "SINGULAR-PERFECT-MATCH-3",
        3,
        ((1, 3, 2), (2, 3, 1), (3, 3, 3)),
    )


def weighted_orphan_selfloop_fixture() -> UniformComparison:
    coarse = Nerve(
        2,
        ((0, 0), (1, 1), (1, 1)),
        ((1, 2, 1), (2, 1, 2)),
    )
    fine = Nerve(
        2,
        ((0, 0), (1, 1), (1, 1), (1, 1)),
        ((1, 2, 1), (2, 1, 2)),
    )
    return UniformComparison(
        name="WEIGHTED-ORPHAN-SELFLOOP",
        morphism=NerveMorphism(
            coarse=coarse,
            fine=fine,
            vertex_map=(0, 1),
            edge_map=(0, 1, 2, 1),
            face_map=(0, 1),
        ),
        coarse_target_count=2,
        fine_target_count=3,
        factor_pi=(0, 0, 1),
        coarse_chart_supports=(
            frozenset((0,)),
            frozenset((0, 1)),
        ),
        fine_chart_supports=(
            frozenset((0, 1)),
            frozenset((2,)),
        ),
    )


def round15_verification_fixtures() -> tuple[UniformComparison, ...]:
    return (
        nonfree_mutual_kill_split_fixture(),
        weighted_2_fixture(),
        ternary_cycle_3_fixture(),
        ternary_cycle_6_fixture(),
        singular_perfect_match_3_fixture(),
        weighted_orphan_selfloop_fixture(),
    )


def _round15_prior_comparisons() -> tuple[UniformComparison, ...]:
    return (
        tuple(_all_comparisons_through_round11())
        + round12_relation_fixtures()
        + round13_bound_comparisons()
        + (nonfree_mutual_kill_split_fixture(),)
    )


def v5_immutable_calibration_fixture_groups() -> dict[
    str, tuple[UniformComparison, ...]
]:
    """Return old evidence excluding five new Round15 controls.

    The parent MUTUAL fixture remains in immutable_prior2161 because Round14
    registered it before the v5 successor was authored.
    """

    required = _required_catalog_v4()
    prior = _round15_prior_comparisons()
    if len(required) != 16 or len(prior) != ROUND15_PARENT_POPULATION:
        raise AssertionError("v5 immutable calibration population drift")
    round15_ids = {
        _case_semantic_sha256(comparison)
        for comparison in round15_verification_fixtures()[1:]
    }
    overlap_by_group = {
        "required16": tuple(
            _case_semantic_sha256(case)
            for case in required
            if _case_semantic_sha256(case) in round15_ids
        ),
        "immutable_prior2161": tuple(
            _case_semantic_sha256(case)
            for case in prior
            if _case_semantic_sha256(case) in round15_ids
        ),
    }
    if any(overlap_by_group.values()):
        raise AssertionError(
            "new Round15 control leaked into immutable calibration groups"
        )
    return {"required16": required, "immutable_prior2161": prior}


def v5_immutable_calibration_report() -> dict[str, object]:
    """Calibrate old evidence, including parent MUTUAL but no new control."""

    groups = v5_immutable_calibration_fixture_groups()
    new_control_ids = {
        _case_semantic_sha256(comparison)
        for comparison in round15_verification_fixtures()[1:]
    }
    new_control_evaluations_by_group = {
        group_name: sum(
            _case_semantic_sha256(comparison) in new_control_ids
            for comparison in comparisons
        )
        for group_name, comparisons in groups.items()
    }
    new_control_evaluations = sum(
        new_control_evaluations_by_group.values()
    )
    if new_control_evaluations != 0:
        raise AssertionError(
            "new Round15 control entered immutable v5 calibration"
        )
    group_rows: dict[str, dict[str, object]] = {}
    all_breaks: list[dict[str, object]] = []
    for group_name in ("required16", "immutable_prior2161"):
        comparisons = groups[group_name]
        breaks = []
        for comparison in comparisons:
            uniform = comparison.is_uniform()
            candidate = v5_candidate_evaluation(
                comparison,
                include_terminal_details=False,
            )["all"]
            if uniform == candidate:
                continue
            row = {
                "group": group_name,
                "name": comparison.name,
                "id": _case_semantic_sha256(comparison),
                "uniform": uniform,
                "candidate": candidate,
                "direction": (
                    "uniform_and_not_candidate"
                    if uniform
                    else "candidate_and_nonuniform"
                ),
            }
            breaks.append(row)
            all_breaks.append(row)
        group_rows[group_name] = {
            "case_count": len(comparisons),
            "break_count": len(breaks),
            "breaks": breaks,
        }
    if all_breaks:
        raise AssertionError("v5 immutable old-evidence calibration mismatch")
    return {
        "semantic_id": V5_SEMANTIC_ID,
        "semantic_sha256": V5_SEMANTIC_SHA256,
        "groups": group_rows,
        "total_group_evaluations": 16 + ROUND15_PARENT_POPULATION,
        "uniform_and_not_candidate_count": 0,
        "candidate_and_nonuniform_count": 0,
        "new_round15_control_evaluations_by_group": (
            new_control_evaluations_by_group
        ),
        "new_round15_control_evaluations": new_control_evaluations,
        "new_round15_control_H1_queries": new_control_evaluations * 3,
        "new_control_dependency": new_control_evaluations != 0,
        "parent_MUTUAL_evaluated_inside_prior2161": True,
        "candidate_predicate_reads_global_or_A_block_H1": False,
        "calibration_oracle_reads_uniformity_outside_candidate": True,
    }


def _round15_fixed_grammar_canonical_payloads(
    comparison: UniformComparison,
) -> tuple[str, ...]:
    morphism = comparison.morphism
    if not (
        morphism.coarse.vertices == morphism.fine.vertices == 2
        and morphism.vertex_map == (0, 1)
        and comparison.coarse_target_count == 2
        and comparison.fine_target_count == 3
        and comparison.factor_pi == (0, 0, 1)
        and comparison.coarse_chart_supports
        == (frozenset((0,)), frozenset((0, 1)))
        and comparison.fine_chart_supports
        == (frozenset((0, 1)), frozenset((2,)))
    ):
        raise ValueError("comparison is outside the fixed Round15 grammar")
    coarse_anchor = tuple(
        edge
        for edge, endpoints in enumerate(morphism.coarse.edges)
        if endpoints == (0, 0)
    )
    fine_anchor = tuple(
        edge
        for edge, endpoints in enumerate(morphism.fine.edges)
        if endpoints == (0, 0)
    )
    coarse_neutral = tuple(
        edge
        for edge, endpoints in enumerate(morphism.coarse.edges)
        if endpoints == (1, 1)
    )
    fine_neutral = tuple(
        edge
        for edge, endpoints in enumerate(morphism.fine.edges)
        if endpoints == (1, 1)
    )
    if not (
        coarse_anchor == (0,)
        and fine_anchor == (0,)
        and len(coarse_anchor) + len(coarse_neutral)
        == len(morphism.coarse.edges)
        and len(fine_anchor) + len(fine_neutral)
        == len(morphism.fine.edges)
        and morphism.edge_map[0] == 0
        and all(
            morphism.edge_map[edge] in coarse_neutral
            for edge in fine_neutral
        )
    ):
        raise ValueError("Round15 fixed grammar edge partition failed")

    payloads: list[str] = []
    canonical_coarse_labels = tuple(range(1, len(coarse_neutral) + 1))
    for assigned_coarse_labels in permutations(canonical_coarse_labels):
        coarse_edge_map = {0: 0}
        coarse_edge_map.update(
            dict(zip(coarse_neutral, assigned_coarse_labels))
        )
        fine_groups: list[tuple[int, tuple[int, ...], tuple[int, ...]]] = []
        next_fine_label = 1
        for mapped_coarse in canonical_coarse_labels:
            members = tuple(
                edge
                for edge in fine_neutral
                if coarse_edge_map[morphism.edge_map[edge]] == mapped_coarse
            )
            labels = tuple(
                range(next_fine_label, next_fine_label + len(members))
            )
            next_fine_label += len(members)
            fine_groups.append((mapped_coarse, members, labels))
        fine_group_assignments = tuple(
            tuple(permutations(labels))
            for _, _, labels in fine_groups
        )
        for assigned_groups in product(*fine_group_assignments):
            fine_edge_map = {0: 0}
            for (_, members, _), assigned_labels in zip(
                fine_groups,
                assigned_groups,
            ):
                fine_edge_map.update(dict(zip(members, assigned_labels)))
            coarse_boundaries = tuple(
                tuple(coarse_edge_map[edge] for edge in boundary)
                for boundary in morphism.coarse.faces
            )
            coarse_faces = sorted([list(boundary) for boundary in coarse_boundaries])
            fine_faces = sorted(
                [
                    {
                        "boundary": [fine_edge_map[edge] for edge in boundary],
                        "mapped_coarse_boundary": (
                            None
                            if morphism.face_map[face] is None
                            else list(
                                coarse_boundaries[morphism.face_map[face]]
                            )
                        ),
                    }
                    for face, boundary in enumerate(morphism.fine.faces)
                ],
                key=lambda row: json.dumps(
                    row,
                    sort_keys=True,
                    separators=(",", ":"),
                ),
            )
            fine_edges_by_new = tuple(
                old
                for old, _ in sorted(
                    fine_edge_map.items(),
                    key=lambda item: item[1],
                )
            )
            for swap_targets in (False, True):
                target_map = (1, 0, 2) if swap_targets else (0, 1, 2)
                transformed_pi = [0, 0, 0]
                for old_target, new_target in enumerate(target_map):
                    transformed_pi[new_target] = comparison.factor_pi[old_target]
                payload = {
                    "coarse": {
                        "vertices": 2,
                        "edge_endpoints_by_canonical_id": (
                            [[0, 0]]
                            + [[1, 1] for _ in coarse_neutral]
                        ),
                        "faces": coarse_faces,
                    },
                    "fine": {
                        "vertices": 2,
                        "edge_endpoints_by_canonical_id": (
                            [[0, 0]] + [[1, 1] for _ in fine_neutral]
                        ),
                        "faces_with_mapped_signature": fine_faces,
                    },
                    "vertex_map": [0, 1],
                    "edge_map_by_canonical_fine_id": [
                        coarse_edge_map[morphism.edge_map[old_edge]]
                        for old_edge in fine_edges_by_new
                    ],
                    "targets": [2, 3],
                    "factor_pi": transformed_pi,
                    "coarse_chart_supports": [
                        sorted(support)
                        for support in comparison.coarse_chart_supports
                    ],
                    "fine_chart_supports": [
                        sorted(target_map[target] for target in support)
                        for support in comparison.fine_chart_supports
                    ],
                }
                payloads.append(
                    json.dumps(payload, sort_keys=True, separators=(",", ":"))
                )
    return tuple(payloads)


def round15_fixture_canonical_orbit_code(
    comparison: UniformComparison,
) -> dict[str, object]:
    payloads = _round15_fixed_grammar_canonical_payloads(comparison)
    if not payloads:
        raise AssertionError("Round15 canonicalizer produced no labeling")
    compact_json = min(payloads)
    digest = sha256(compact_json.encode("ascii")).hexdigest()
    return {
        "compact_json": compact_json,
        "sha256": digest,
        "id20": digest[:20],
        "enumerated_labelings": len(payloads),
        "orbit_size": len(set(payloads)),
        "canonicalizes_neutral_edge_relabeling": True,
        "canonicalizes_face_order": True,
        "canonicalizes_pi_fiber_target_swap_0_1": True,
    }


def _round15_expected_h1_blocks() -> dict[str, list[dict[str, object]]]:
    def row(
        targets: list[int],
        coarse: int,
        fine: int,
        comparison_rank: int,
        injective: bool,
        surjective: bool,
        isomorphism: bool,
    ) -> dict[str, object]:
        return {
            "coarse_targets_A": targets,
            "coarse_h1_dimension": coarse,
            "fine_h1_dimension": fine,
            "comparison_rank": comparison_rank,
            "injective": injective,
            "surjective": surjective,
            "isomorphism": isomorphism,
        }

    uniform = [
        row([0], 1, 1, 1, True, True, True),
        row([1], 0, 0, 0, True, True, True),
        row([0, 1], 1, 1, 1, True, True, True),
    ]
    return {
        "NONFREE-MUTUAL-KILL-SPLIT": uniform,
        "WEIGHTED-2": uniform,
        "TERNARY-CYCLE-3": uniform,
        "TERNARY-CYCLE-6": [
            row([0], 3, 1, 1, False, True, False),
            row([1], 2, 2, 2, True, True, True),
            row([0, 1], 3, 3, 3, True, True, True),
        ],
        "SINGULAR-PERFECT-MATCH-3": [
            row([0], 2, 1, 1, False, True, False),
            row([1], 1, 1, 1, True, True, True),
            row([0, 1], 2, 2, 2, True, True, True),
        ],
        "WEIGHTED-ORPHAN-SELFLOOP": [
            row([0], 1, 1, 1, True, True, True),
            row([1], 0, 1, 0, True, False, False),
            row([0, 1], 1, 2, 1, True, False, False),
        ],
    }


def _round15_hand_candidate_expectations() -> dict[str, dict[str, object]]:
    all_true = {f"C{index}*": True for index in range(7)}
    ternary_or_singular = {
        "C0*": False,
        "C1*": False,
        "C2*": False,
        "C3*": True,
        "C4*": False,
        "C5*": True,
        "C6*": True,
    }
    orphan = {
        "C0*": False,
        "C1*": True,
        "C2*": True,
        "C3*": True,
        "C4*": True,
        "C5*": False,
        "C6*": True,
    }
    all_true_relative = {
        "C1*": True,
        "C2*": True,
        "C3*": True,
        "C4*": True,
    }
    fail_a0_relative = {
        "C1*": False,
        "C2*": False,
        "C3*": True,
        "C4*": False,
    }

    def expectation(
        aggregate: dict[str, bool],
        whole_trace: list[str],
        per_A_traces: list[list[str]],
        per_A_conditions: list[dict[str, bool]],
        retained_original_cells: dict[str, object],
    ) -> dict[str, object]:
        return {
            "aggregate": aggregate,
            "vector_C0_through_C6": [
                aggregate[f"C{index}*"] for index in range(7)
            ],
            "candidate_all": all(aggregate.values()),
            "whole": {
                "terminal_count": 1,
                "trace_kinds": whole_trace,
            },
            "per_nonempty_A": [
                {
                    "coarse_targets_A": targets,
                    "terminal_count": 1,
                    "trace_kinds": trace,
                    "conditions": conditions,
                }
                for targets, trace, conditions in zip(
                    ([0], [1], [0, 1]),
                    per_A_traces,
                    per_A_conditions,
                )
            ],
            "retained_original_cells": retained_original_cells,
            "expectation_is_not_engine_observation": True,
        }

    positive_retained = {
        "whole": {
            "coarse_edges": [0],
            "fine_edges": [0],
            "coarse_faces": [],
            "fine_faces": [],
        },
        "A0": {
            "coarse_edges": [0],
            "fine_edges": [0],
            "coarse_faces": [],
            "fine_faces": [],
        },
        "A1": {
            "coarse_edges": [],
            "fine_edges": [],
            "coarse_faces": [],
            "fine_faces": [],
        },
        "A01": {
            "coarse_edges": [0],
            "fine_edges": [0],
            "coarse_faces": [],
            "fine_faces": [],
        },
    }
    negative_retained = {
        "all_scopes": "all support-active cells retained",
    }
    return {
        "NONFREE-MUTUAL-KILL-SPLIT": expectation(
            all_true,
            ["coordinate-dependency"],
            [
                ["coordinate-dependency"],
                ["coordinate-dependency"],
                ["coordinate-dependency"],
            ],
            [all_true_relative, all_true_relative, all_true_relative],
            positive_retained,
        ),
        "WEIGHTED-2": expectation(
            all_true,
            ["closed-doubled-cycle"],
            [
                ["closed-doubled-cycle"],
                ["closed-doubled-cycle"],
                ["closed-doubled-cycle"],
            ],
            [all_true_relative, all_true_relative, all_true_relative],
            positive_retained,
        ),
        "TERNARY-CYCLE-3": expectation(
            ternary_or_singular,
            [],
            [[], [], []],
            [fail_a0_relative, all_true_relative, all_true_relative],
            negative_retained,
        ),
        "TERNARY-CYCLE-6": expectation(
            ternary_or_singular,
            [],
            [[], [], []],
            [fail_a0_relative, all_true_relative, all_true_relative],
            negative_retained,
        ),
        "SINGULAR-PERFECT-MATCH-3": expectation(
            ternary_or_singular,
            [],
            [[], [], []],
            [fail_a0_relative, all_true_relative, all_true_relative],
            negative_retained,
        ),
        "WEIGHTED-ORPHAN-SELFLOOP": expectation(
            orphan,
            [],
            [["closed-doubled-cycle"], [], []],
            [all_true_relative, all_true_relative, all_true_relative],
            {
                "A0": positive_retained["A0"],
                "A1_A01_whole": "all support-active cells retained",
            },
        ),
    }


def _round15_hand_packet_structures() -> dict[str, dict[str, object]]:
    return {
        "NONFREE-MUTUAL-KILL-SPLIT": {
            "accepted_atom": "coordinate-dependency",
            "coarse_selfloop_set_original_ids": [1, 2],
            "coarse_face_classes_original_ids": [0, 1],
            "coarse_beta_singletons": {"0": [2, 1], "1": [1, 1]},
            "target_map_surjective": True,
            "fine_preimage_kind": "identity coordinate sheet",
            "residual_fine_edges": [],
        },
        "WEIGHTED-2": {
            "accepted_atom": "closed-doubled-cycle",
            "coarse_selfloop_cycle_original_ids": [1, 2],
            "coarse_face_classes_original_ids": [0, 1],
            "ordered_boundaries": [[1, 2, 1], [2, 1, 2]],
            "fine_preimage_kind": "identity directed covering sheet",
            "residual_fine_edges": [],
        },
        "TERNARY-CYCLE-3": {
            "accepted_atom": None,
            "packet_count_expected": 0,
            "rejection": "every beta support has size three and no face has first=edge third",
        },
        "TERNARY-CYCLE-6": {
            "accepted_atom": None,
            "packet_count_expected": 0,
            "rejection": "every neutral edge has three raw class occurrences and every beta support has size three",
        },
        "SINGULAR-PERFECT-MATCH-3": {
            "accepted_atom": None,
            "packet_count_expected": 0,
            "beta_rows": ["x+y-z", "x+y-z", "z"],
            "rejection": "perfect matching is not an allowed packet and the repeated nonsingleton relation remains singular",
        },
        "WEIGHTED-ORPHAN-SELFLOOP": {
            "accepted_atom_whole": None,
            "packet_count_expected_whole": 0,
            "would_be_atom": "closed-doubled-cycle",
            "rejection": "fine edge 3 maps to coarse edge 1 and is a residual self-loop",
            "A0_empty_preimage_atom": "closed-doubled-cycle",
        },
    }


def round15_preregistration_manifest() -> dict[str, object]:
    fixtures = round15_verification_fixtures()
    expected_names = (
        "NONFREE-MUTUAL-KILL-SPLIT",
        "WEIGHTED-2",
        "TERNARY-CYCLE-3",
        "TERNARY-CYCLE-6",
        "SINGULAR-PERFECT-MATCH-3",
        "WEIGHTED-ORPHAN-SELFLOOP",
    )
    if tuple(fixture.name for fixture in fixtures) != expected_names:
        raise AssertionError("Round15 exact fixture ordering drift")
    fixture_payloads = tuple(
        _case_semantic_payload_json(fixture) for fixture in fixtures
    )
    fixture_ids = tuple(
        sha256(payload.encode("utf-8")).hexdigest()
        for payload in fixture_payloads
    )
    canonical_codes = tuple(
        round15_fixture_canonical_orbit_code(fixture)
        for fixture in fixtures
    )
    if not (
        len(set(fixture_payloads)) == len(fixtures)
        and len(set(fixture_ids)) == len(fixtures)
        and len({identifier[:20] for identifier in fixture_ids})
        == len(fixtures)
        and len({code["sha256"] for code in canonical_codes})
        == len(fixtures)
        and len({code["id20"] for code in canonical_codes})
        == len(fixtures)
    ):
        raise AssertionError("Round15 fixture semantic/canonical collision")

    prior = _round15_prior_comparisons()
    prior_payloads = tuple(
        _case_semantic_payload_json(comparison) for comparison in prior
    )
    prior_ids = tuple(
        sha256(payload.encode("utf-8")).hexdigest()
        for payload in prior_payloads
    )
    overlap_names = [
        fixture.name
        for fixture, identifier in zip(fixtures, fixture_ids)
        if identifier in set(prior_ids)
    ]
    new_ids = tuple(
        identifier
        for identifier in fixture_ids
        if identifier not in set(prior_ids)
    )
    union_ids = prior_ids + new_ids
    if not (
        len(prior) == ROUND15_PARENT_POPULATION == 2161
        and len(set(prior_payloads)) == 2161
        and len(set(prior_ids)) == 2161
        and len({identifier[:20] for identifier in prior_ids}) == 2161
        and overlap_names == ["NONFREE-MUTUAL-KILL-SPLIT"]
        and len(new_ids) == 5
        and len(set(union_ids)) == 2166
        and len({identifier[:20] for identifier in union_ids}) == 2166
    ):
        raise AssertionError("Round15 pure population expansion gate failed")

    expected_h1 = _round15_expected_h1_blocks()
    expected_candidate = _round15_hand_candidate_expectations()
    packet_structures = _round15_hand_packet_structures()
    fixture_rows = []
    for fixture, identifier, canonical in zip(
        fixtures,
        fixture_ids,
        canonical_codes,
    ):
        fixture_rows.append(
            {
                "name": fixture.name,
                "summary": fixture.summary(),
                "name_free_semantic_sha256": identifier,
                "name_free_id20": identifier[:20],
                "canonical_orbit_code": canonical,
                "hand_packet_structure": packet_structures[fixture.name],
                "hand_expected_H1_blocks": expected_h1[fixture.name],
                "hand_expected_v5_candidate": expected_candidate[
                    fixture.name
                ],
            }
        )

    return {
        "kind": "round15-v5-semantic-safety-pure-preregistration-manifest",
        "semantic_bound": {
            "semantic_id": ROUND15_BOUND_SEMANTIC_ID,
            "semantic_sha256": ROUND15_BOUND_SEMANTIC_SHA256,
            "spec": ROUND15_BOUND_SPEC,
        },
        "fixed_candidate": {
            "semantic_id": V5_SEMANTIC_ID,
            "semantic_sha256": V5_SEMANTIC_SHA256,
            "spec": V5_SPEC,
            "single_successor_of": V4_SEMANTIC_ID,
            "v4_semantic_sha256": V4_SEMANTIC_SHA256,
            "v4_status_after_round14": "invalid",
            "packet_atoms_added": [
                "coordinate-dependency",
                "closed-doubled-cycle",
            ],
            "forbidden_dependency_symbols": list(
                V5_PACKET_FORBIDDEN_SYMBOLS
            ),
            "dependency_audit_new_helper_call_closure": list(
                V5_DEPENDENCY_AUDIT_NEW_HELPER_CALL_CLOSURE
            ),
            "immutable_v4_dependency_boundary_sha256": V4_SEMANTIC_SHA256,
            "local_C3_linear_algebra_only": True,
        },
        "round14_parent_reference": {
            "payload_sha256": ROUND15_PARENT_ROUND14_PAYLOAD_SHA256,
            "canonical_bytes": ROUND15_PARENT_ROUND14_CANONICAL_BYTES,
            "result_issue_comment": (
                ROUND15_PARENT_ROUND14_RESULT_ISSUE_COMMENT
            ),
            "created_at": ROUND15_PARENT_ROUND14_RESULT_CREATED_AT,
            "updated_at": ROUND15_PARENT_ROUND14_RESULT_UPDATED_AT,
            "g107_sync_issue_comment": (
                ROUND15_PARENT_G107_SYNC_ISSUE_COMMENT
            ),
            "valid": True,
            "population": ROUND15_PARENT_POPULATION,
            "uniform_and_not_candidate_count": 1,
            "candidate_and_nonuniform_count": 0,
            "new_verdict": "CSTAR-not-necessary",
            "invalidated_semantic_id": V4_SEMANTIC_ID,
            "progress": True,
            "streak_after_round": 0,
        },
        "fixtures": fixture_rows,
        "pure_population_gate": {
            "prior_unique_name_free_ids": 2161,
            "verification_fixture_count": 6,
            "prior_overlap_names": overlap_names,
            "prior_overlap_count": 1,
            "strict_new_fixture_count": 5,
            "union_unique_name_free_ids": 2166,
            "full_sha256_collision_count": 0,
            "truncated_20hex_collision_count": 0,
            "canonical_fixture_code_collision_count": 0,
        },
        "future_calibration_partition": {
            "required_catalog_case_count": 16,
            "immutable_prior_case_count": 2161,
            "round15_control_count": 6,
            "parent_MUTUAL_overlap_is_inside_immutable_prior": True,
            "new_round15_control_count_excluded_from_calibration": 5,
            "required_and_prior_calibration_excludes_new_round15_controls": True,
            "new_control_H1_or_candidate_execution_before_preregistration": False,
        },
        "known_outcomes_classification": {
            "TERNARY-CYCLE-3": (
                "known-human-static-uniform_and_not_candidate"
            ),
            "MUTUAL_and_WEIGHTED_2": "semantic-safety-positive-controls",
            "TERNARY-CYCLE-6": "nonuniform-neutral-H1-dimension-2-negative-control",
            "SINGULAR-PERFECT-MATCH-3": (
                "nonuniform-generalized-matching-negative-control"
            ),
            "WEIGHTED-ORPHAN-SELFLOOP": (
                "nonuniform-residual-selfloop-negative-control"
            ),
            "new_query_discovery": False,
        },
        "dependency_contract": {
            "constructs_uniform_comparisons": True,
            "computes_derived_supports_via_summary": True,
            "computes_name_free_semantic_ids": True,
            "computes_fixed_grammar_canonical_orbit_ids": True,
            "calls_H1_or_is_uniform": False,
            "calls_v4_or_v5_candidate": False,
            "calls_v4_or_v5_calibration": False,
            "calls_round13_or_round14_report": False,
            "calls_round15_query_or_report": False,
        },
        "preregistered_issue_comment": None,
        "admission_gate_added": False,
        "round15_query_added": False,
        "round15_report_added": False,
    }


def round15_preregistration_manifest_canonical_json() -> str:
    return json.dumps(
        round15_preregistration_manifest(),
        sort_keys=True,
        separators=(",", ":"),
    )


def round15_preregistration_manifest_sha256() -> str:
    return sha256(
        round15_preregistration_manifest_canonical_json().encode("utf-8")
    ).hexdigest()


def _round15_pretty_canonical_bytes(report: dict[str, object]) -> bytes:
    return (
        json.dumps(
            report,
            ensure_ascii=False,
            indent=2,
            sort_keys=True,
        )
        + "\n"
    ).encode("utf-8")


def _round15_manifest_admission() -> dict[str, object]:
    manifest = round15_preregistration_manifest()
    canonical_json = json.dumps(
        manifest,
        sort_keys=True,
        separators=(",", ":"),
    )
    manifest_sha256 = sha256(canonical_json.encode("utf-8")).hexdigest()
    fixture_names = [row["name"] for row in manifest["fixtures"]]
    fixture_ids = [
        row["name_free_semantic_sha256"]
        for row in manifest["fixtures"]
    ]
    canonical_ids = [
        row["canonical_orbit_code"]["sha256"]
        for row in manifest["fixtures"]
    ]
    population = manifest["pure_population_gate"]
    partition = manifest["future_calibration_partition"]
    parent = manifest["round14_parent_reference"]
    if not (
        manifest_sha256 == ROUND15_REGISTERED_MANIFEST_SHA256
        and ROUND15_PREREGISTERED_ISSUE_COMMENT == 5235347217
        and ROUND15_PREREGISTERED_CREATED_AT
        == ROUND15_PREREGISTERED_UPDATED_AT
        == "2026-08-10T02:51:13Z"
        and manifest["semantic_bound"]["semantic_id"]
        == ROUND15_BOUND_SEMANTIC_ID
        and manifest["semantic_bound"]["semantic_sha256"]
        == ROUND15_BOUND_SEMANTIC_SHA256
        and manifest["fixed_candidate"]["semantic_id"] == V5_SEMANTIC_ID
        and manifest["fixed_candidate"]["semantic_sha256"]
        == V5_SEMANTIC_SHA256
        and fixture_names
        == [
            "NONFREE-MUTUAL-KILL-SPLIT",
            "WEIGHTED-2",
            "TERNARY-CYCLE-3",
            "TERNARY-CYCLE-6",
            "SINGULAR-PERFECT-MATCH-3",
            "WEIGHTED-ORPHAN-SELFLOOP",
        ]
        and len(set(fixture_ids)) == 6
        and len({identifier[:20] for identifier in fixture_ids}) == 6
        and len(set(canonical_ids)) == 6
        and len({identifier[:20] for identifier in canonical_ids}) == 6
        and population
        == {
            "prior_unique_name_free_ids": 2161,
            "verification_fixture_count": 6,
            "prior_overlap_names": ["NONFREE-MUTUAL-KILL-SPLIT"],
            "prior_overlap_count": 1,
            "strict_new_fixture_count": 5,
            "union_unique_name_free_ids": 2166,
            "full_sha256_collision_count": 0,
            "truncated_20hex_collision_count": 0,
            "canonical_fixture_code_collision_count": 0,
        }
        and partition["required_catalog_case_count"] == 16
        and partition["immutable_prior_case_count"] == 2161
        and partition["parent_MUTUAL_overlap_is_inside_immutable_prior"]
        is True
        and partition["new_round15_control_count_excluded_from_calibration"]
        == 5
        and partition[
            "required_and_prior_calibration_excludes_new_round15_controls"
        ]
        is True
        and parent["payload_sha256"]
        == ROUND15_PARENT_ROUND14_PAYLOAD_SHA256
        and parent["canonical_bytes"]
        == ROUND15_PARENT_ROUND14_CANONICAL_BYTES
        and parent["result_issue_comment"]
        == ROUND15_PARENT_ROUND14_RESULT_ISSUE_COMMENT
        and parent["created_at"] == ROUND15_PARENT_ROUND14_RESULT_CREATED_AT
        and parent["updated_at"] == ROUND15_PARENT_ROUND14_RESULT_UPDATED_AT
        and manifest["preregistered_issue_comment"] is None
        and manifest["admission_gate_added"] is False
        and manifest["round15_query_added"] is False
        and manifest["round15_report_added"] is False
    ):
        raise AssertionError("Round15 immutable preregistration manifest gate failed")
    return {
        "manifest": manifest,
        "manifest_sha256": manifest_sha256,
        "preregistered_issue_comment": ROUND15_PREREGISTERED_ISSUE_COMMENT,
        "created_at": ROUND15_PREREGISTERED_CREATED_AT,
        "updated_at": ROUND15_PREREGISTERED_UPDATED_AT,
        "all_gates_pass": True,
    }


def _round15_round14_baseline_admission() -> dict[str, object]:
    report = round14_report()
    rendered = _round15_pretty_canonical_bytes(report)
    payload_sha256 = sha256(rendered).hexdigest()
    population = report["population"]
    queries = report["queries"]
    progress = report["progress_audit"]
    verification = report["exact_verification"]
    if not (
        payload_sha256 == ROUND15_PARENT_ROUND14_PAYLOAD_SHA256
        and len(rendered) == ROUND15_PARENT_ROUND14_CANONICAL_BYTES
        and ROUND15_PARENT_ROUND14_RESULT_ISSUE_COMMENT == 5235064396
        and ROUND15_PARENT_ROUND14_RESULT_CREATED_AT
        == ROUND15_PARENT_ROUND14_RESULT_UPDATED_AT
        == "2026-08-10T01:55:17Z"
        and report["round"] == "R2-round-14"
        and report["valid"] is True
        and report["preregistration"]["manifest_sha256"]
        == ROUND14_REGISTERED_MANIFEST_SHA256
        and report["candidate"]["semantic_id"] == V4_SEMANTIC_ID
        and report["candidate"]["semantic_sha256"] == V4_SEMANTIC_SHA256
        and report["candidate"]["status"] == "invalid"
        and population["total_cases"] == ROUND15_PARENT_POPULATION
        and population["unique_full_name_free_ids"]
        == ROUND15_PARENT_POPULATION
        and population["unique_truncated_20hex_ids"]
        == ROUND15_PARENT_POPULATION
        and population["full_sha256_collision_count"] == 0
        and population["truncated_20hex_collision_count"] == 0
        and queries["uniform_and_not_candidate_count"] == 1
        and queries["candidate_and_nonuniform_count"] == 0
        and queries["new_counterexample_count"] == 1
        and verification["fixture"]["name"]
        == "NONFREE-MUTUAL-KILL-SPLIT"
        and verification["uniform"] is True
        and verification["new_A_block_queries"] == 3
        and verification[
            "engine_reproduced_preregistered_expectations"
        ]
        is True
        and progress["new_verdicts"] == ["CSTAR-not-necessary"]
        and progress["progress"] is True
        and progress["streak_after_round"] == 0
    ):
        raise AssertionError("Round15 immutable Round14 result gate failed")
    return {
        "payload_sha256": payload_sha256,
        "canonical_bytes": len(rendered),
        "result_issue_comment": ROUND15_PARENT_ROUND14_RESULT_ISSUE_COMMENT,
        "created_at": ROUND15_PARENT_ROUND14_RESULT_CREATED_AT,
        "updated_at": ROUND15_PARENT_ROUND14_RESULT_UPDATED_AT,
        "valid": True,
        "population": population["total_cases"],
        "uniform_and_not_candidate_count": queries[
            "uniform_and_not_candidate_count"
        ],
        "candidate_and_nonuniform_count": queries[
            "candidate_and_nonuniform_count"
        ],
        "mutual_H1_blocks": verification["H1_blocks"],
        "progress": progress["progress"],
        "streak_after_round": progress["streak_after_round"],
        "all_gates_pass": True,
    }


def _round15_v5_calibration_admission() -> dict[str, object]:
    calibration = v5_immutable_calibration_report()
    rendered = _round15_pretty_canonical_bytes(calibration)
    calibration_sha256 = sha256(rendered).hexdigest()
    groups = calibration["groups"]
    if not (
        calibration_sha256 == ROUND15_REGISTERED_V5_CALIBRATION_SHA256
        and len(rendered) == ROUND15_REGISTERED_V5_CALIBRATION_BYTES
        and calibration["semantic_id"] == V5_SEMANTIC_ID
        and calibration["semantic_sha256"] == V5_SEMANTIC_SHA256
        and groups["required16"]["case_count"] == 16
        and groups["required16"]["break_count"] == 0
        and groups["required16"]["breaks"] == []
        and groups["immutable_prior2161"]["case_count"] == 2161
        and groups["immutable_prior2161"]["break_count"] == 0
        and groups["immutable_prior2161"]["breaks"] == []
        and calibration["total_group_evaluations"] == 2177
        and calibration["uniform_and_not_candidate_count"] == 0
        and calibration["candidate_and_nonuniform_count"] == 0
        and calibration["new_round15_control_evaluations_by_group"]
        == {"required16": 0, "immutable_prior2161": 0}
        and calibration["new_round15_control_evaluations"] == 0
        and calibration["new_round15_control_H1_queries"] == 0
        and calibration["new_control_dependency"] is False
        and calibration["parent_MUTUAL_evaluated_inside_prior2161"] is True
    ):
        raise AssertionError("Round15 registered v5 calibration gate failed")
    return {
        "canonical_sha256": calibration_sha256,
        "canonical_bytes": len(rendered),
        "required_catalog_count": groups["required16"]["case_count"],
        "immutable_prior_count": groups["immutable_prior2161"]["case_count"],
        "uniform_and_not_candidate_count": calibration[
            "uniform_and_not_candidate_count"
        ],
        "candidate_and_nonuniform_count": calibration[
            "candidate_and_nonuniform_count"
        ],
        "new_round15_control_evaluations_by_group": calibration[
            "new_round15_control_evaluations_by_group"
        ],
        "new_round15_control_evaluations": calibration[
            "new_round15_control_evaluations"
        ],
        "new_round15_control_H1_queries": calibration[
            "new_round15_control_H1_queries"
        ],
        "all_gates_pass": True,
    }


def _round15_population_identity_admission(
    manifest: dict[str, object],
) -> dict[str, object]:
    prior = _round15_prior_comparisons()
    fixtures = round15_verification_fixtures()
    prior_ids = tuple(_case_semantic_sha256(case) for case in prior)
    fixture_ids = tuple(_case_semantic_sha256(case) for case in fixtures)
    fixture_rows = {
        row["name"]: row
        for row in manifest["fixtures"]
    }
    registered_fixture_ids = tuple(
        fixture_rows[fixture.name]["name_free_semantic_sha256"]
        for fixture in fixtures
    )
    overlap_names = tuple(
        fixture.name
        for fixture, identifier in zip(fixtures, fixture_ids)
        if identifier in set(prior_ids)
    )
    new_ids = tuple(
        identifier
        for identifier in fixture_ids
        if identifier not in set(prior_ids)
    )
    new_canonical_ids = tuple(
        fixture_rows[fixture.name]["canonical_orbit_code"]["sha256"]
        for fixture, identifier in zip(fixtures, fixture_ids)
        if identifier in set(new_ids)
    )
    union_ids = prior_ids + new_ids
    short_ids = tuple(identifier[:20] for identifier in union_ids)
    population = manifest["pure_population_gate"]
    if not (
        len(prior) == ROUND15_PARENT_POPULATION == 2161
        and len(set(prior_ids)) == 2161
        and len({identifier[:20] for identifier in prior_ids}) == 2161
        and fixture_ids == registered_fixture_ids
        and overlap_names == ("NONFREE-MUTUAL-KILL-SPLIT",)
        and fixture_ids[0] in set(prior_ids)
        and len(new_ids) == 5
        and new_ids == fixture_ids[1:]
        and not (set(prior_ids) & set(new_ids))
        and len(set(union_ids)) == 2166
        and len(set(short_ids)) == 2166
        and len(set(new_canonical_ids)) == 5
        and len({identifier[:20] for identifier in new_canonical_ids}) == 5
        and population["prior_unique_name_free_ids"] == 2161
        and population["prior_overlap_names"]
        == ["NONFREE-MUTUAL-KILL-SPLIT"]
        and population["prior_overlap_count"] == 1
        and population["strict_new_fixture_count"] == 5
        and population["union_unique_name_free_ids"] == 2166
        and population["full_sha256_collision_count"] == 0
        and population["truncated_20hex_collision_count"] == 0
        and population["canonical_fixture_code_collision_count"] == 0
    ):
        raise AssertionError("Round15 population identity or collision gate failed")
    return {
        "prior_cases": 2161,
        "verification_fixture_count": 6,
        "overlap_cases": 1,
        "overlap_names": list(overlap_names),
        "new_cases": 5,
        "total_cases": 2166,
        "unique_full_name_free_ids": len(set(union_ids)),
        "unique_truncated_20hex_ids": len(set(short_ids)),
        "full_sha256_collision_count": 0,
        "truncated_20hex_collision_count": 0,
        "new_disjoint_from_prior": True,
        "new_semantic_sha256": list(new_ids),
        "new_canonical_orbit_sha256": list(new_canonical_ids),
        "all_gates_pass": True,
    }


def _round15_admission_gate() -> dict[str, object]:
    manifest = _round15_manifest_admission()
    round14 = _round15_round14_baseline_admission()
    calibration = _round15_v5_calibration_admission()
    identity = _round15_population_identity_admission(manifest["manifest"])
    return {
        "gate_order": [
            "immutable_pure_preregistration_manifest_and_comment",
            "immutable_round14_full_result",
            "exact_v5_old_only_calibration_with_no_new_control_evaluation",
            "prior2161_overlap_MUTUAL_plus_new5_identity_and_collision",
        ],
        "manifest": manifest,
        "round14_baseline": round14,
        "v5_calibration": calibration,
        "population_identity": identity,
        "all_gates_pass": True,
    }


def _round15_scope_original_cell_universe(
    comparison: UniformComparison,
    targets: frozenset[int] | None,
) -> dict[str, list[int]]:
    if targets is None:
        return {
            "coarse_edges": list(range(len(comparison.morphism.coarse.edges))),
            "fine_edges": list(range(len(comparison.morphism.fine.edges))),
            "coarse_faces": list(range(len(comparison.morphism.coarse.faces))),
            "fine_faces": list(range(len(comparison.morphism.fine.faces))),
        }
    sub = comparison.coordinate_subcomparison(targets)
    return {
        "coarse_edges": list(sub.coarse.edges),
        "fine_edges": list(sub.fine.edges),
        "coarse_faces": list(sub.coarse.faces),
        "fine_faces": list(sub.fine.faces),
    }


def _round15_terminal_original_cells(
    comparison: UniformComparison,
    targets: frozenset[int] | None,
    terminal: dict[str, object],
) -> dict[str, list[int]]:
    universe = _round15_scope_original_cell_universe(comparison, targets)

    def retained(
        reduction: dict[str, object],
        edge_original_ids: list[int],
        face_original_ids: list[int],
    ) -> tuple[list[int], list[int]]:
        edges = [
            edge_original_ids[local_edge]
            for local_edge in reduction["retained_edges"]
        ]
        retained_local_faces = sorted(
            {
                member
                for class_index in reduction["retained_face_classes"]
                for member in reduction["face_classes"][class_index]["members"]
            }
        )
        faces = [
            face_original_ids[local_face]
            for local_face in retained_local_faces
        ]
        return edges, faces

    coarse_edges, coarse_faces = retained(
        terminal["coarse_reduction"],
        universe["coarse_edges"],
        universe["coarse_faces"],
    )
    fine_edges, fine_faces = retained(
        terminal["fine_reduction"],
        universe["fine_edges"],
        universe["fine_faces"],
    )
    return {
        "coarse_edges": coarse_edges,
        "fine_edges": fine_edges,
        "coarse_faces": coarse_faces,
        "fine_faces": fine_faces,
    }


def _round15_actual_candidate_expectation(
    comparison: UniformComparison,
    candidate: dict[str, object],
) -> dict[str, object]:
    if not (
        candidate["semantic_id"] == V5_SEMANTIC_ID
        and candidate["semantic_sha256"] == V5_SEMANTIC_SHA256
        and candidate["whole"]["terminal_count"] == 1
        and len(candidate["whole"].get("terminals", [])) == 1
        and len(candidate["per_subset"]) == 3
        and all(
            row["terminal_count"] == 1
            and len(row.get("terminals", [])) == 1
            for row in candidate["per_subset"]
        )
    ):
        raise AssertionError("Round15 candidate terminal multiplicity drift")

    whole_terminal = candidate["whole"]["terminals"][0]
    subset_rows = {
        tuple(row["coarse_targets_A"]): row
        for row in candidate["per_subset"]
    }
    retained_by_scope = {
        "whole": _round15_terminal_original_cells(
            comparison,
            None,
            whole_terminal,
        )
    }
    scope_targets = {
        "A0": frozenset((0,)),
        "A1": frozenset((1,)),
        "A01": frozenset((0, 1)),
    }
    for label, targets in scope_targets.items():
        retained_by_scope[label] = _round15_terminal_original_cells(
            comparison,
            targets,
            subset_rows[tuple(sorted(targets))]["terminals"][0],
        )
    all_retained = {
        label: retained_by_scope[label]
        == _round15_scope_original_cell_universe(
            comparison,
            None if label == "whole" else scope_targets[label],
        )
        for label in ("whole", "A0", "A1", "A01")
    }
    if all(all_retained.values()):
        retained_expectation: dict[str, object] = {
            "all_scopes": "all support-active cells retained"
        }
    elif (
        all_retained["whole"]
        and all_retained["A1"]
        and all_retained["A01"]
        and not all_retained["A0"]
    ):
        retained_expectation = {
            "A0": retained_by_scope["A0"],
            "A1_A01_whole": "all support-active cells retained",
        }
    else:
        retained_expectation = retained_by_scope

    return {
        "aggregate": candidate["aggregate"],
        "vector_C0_through_C6": [
            candidate["aggregate"][f"C{index}*"]
            for index in range(7)
        ],
        "candidate_all": candidate["all"],
        "whole": {
            "terminal_count": candidate["whole"]["terminal_count"],
            "trace_kinds": [
                packet["kind"] for packet in whole_terminal["trace"]
            ],
        },
        "per_nonempty_A": [
            {
                "coarse_targets_A": row["coarse_targets_A"],
                "terminal_count": row["terminal_count"],
                "trace_kinds": [
                    packet["kind"]
                    for packet in row["terminals"][0]["trace"]
                ],
                "conditions": row["conditions"],
            }
            for row in candidate["per_subset"]
        ],
        "retained_original_cells": retained_expectation,
    }


def _round15_engine_query(
    manifest: dict[str, object],
    parent_mutual_h1_blocks: list[dict[str, object]],
) -> dict[str, object]:
    fixtures = round15_verification_fixtures()
    registered = {row["name"]: row for row in manifest["fixtures"]}
    expected_outcomes = {
        "NONFREE-MUTUAL-KILL-SPLIT": (True, True, None),
        "WEIGHTED-2": (True, True, None),
        "TERNARY-CYCLE-3": (True, False, "uniform_and_not_candidate"),
        "TERNARY-CYCLE-6": (False, False, None),
        "SINGULAR-PERFECT-MATCH-3": (False, False, None),
        "WEIGHTED-ORPHAN-SELFLOOP": (False, False, None),
    }
    fixture_results = []
    witnesses = []
    new_A_queries = 0
    for fixture_index, fixture in enumerate(fixtures):
        registered_row = registered[fixture.name]
        semantic_id = _case_semantic_sha256(fixture)
        canonical = round15_fixture_canonical_orbit_code(fixture)
        if fixture_index == 0:
            h1_blocks = parent_mutual_h1_blocks
            h1_source = "immutable-Round14-parent-result"
        else:
            blocks = fixture.block_analyses()
            h1_blocks = [
                {"coarse_targets_A": sorted(targets), **asdict(analysis)}
                for targets, analysis in blocks
            ]
            new_A_queries += len(blocks)
            h1_source = "Round15-new5-exact-query"
        candidate = v5_candidate_evaluation(
            fixture,
            include_terminal_details=True,
        )
        actual_candidate = _round15_actual_candidate_expectation(
            fixture,
            candidate,
        )
        expected_candidate = dict(
            registered_row["hand_expected_v5_candidate"]
        )
        expectation_marker = expected_candidate.pop(
            "expectation_is_not_engine_observation"
        )
        uniform = all(row["isomorphism"] for row in h1_blocks)
        expected_uniform, expected_candidate_all, expected_direction = (
            expected_outcomes[fixture.name]
        )
        direction = (
            "uniform_and_not_candidate"
            if uniform and not candidate["all"]
            else "candidate_and_nonuniform"
            if candidate["all"] and not uniform
            else None
        )
        if not (
            semantic_id == registered_row["name_free_semantic_sha256"]
            and canonical == registered_row["canonical_orbit_code"]
            and h1_blocks == registered_row["hand_expected_H1_blocks"]
            and actual_candidate == expected_candidate
            and expectation_marker is True
            and uniform is expected_uniform
            and candidate["all"] is expected_candidate_all
            and direction == expected_direction
        ):
            raise AssertionError(
                f"Round15 registered engine expectation mismatch: {fixture.name}"
            )
        fixture_result = {
            "name": fixture.name,
            "semantic_sha256": semantic_id,
            "id20": semantic_id[:20],
            "canonical_orbit_sha256": canonical["sha256"],
            "canonical_orbit_id20": canonical["id20"],
            "H1_source": h1_source,
            "H1_blocks": h1_blocks,
            "uniform": uniform,
            "v5_candidate": actual_candidate,
            "direction": direction,
            "engine_reproduced_registered_expectations": True,
        }
        fixture_results.append(fixture_result)
        if direction == "uniform_and_not_candidate":
            failing = next(
                row
                for row in actual_candidate["per_nonempty_A"]
                if not all(row["conditions"].values())
            )
            exact_h1 = next(
                row
                for row in h1_blocks
                if row["coarse_targets_A"]
                == failing["coarse_targets_A"]
            )
            witnesses.append(
                {
                    "id": semantic_id,
                    "id20": semantic_id[:20],
                    "canonical_nonisomorphic_id": canonical["sha256"],
                    "canonical_nonisomorphic_id20": canonical["id20"],
                    "name": fixture.name,
                    "category": "round15_new_control",
                    "direction": direction,
                    "minimal_failing_A": failing["coarse_targets_A"],
                    "exact_h1": exact_h1,
                    "candidate_aggregate": actual_candidate["aggregate"],
                    "candidate_failure_scope": "nonempty-A",
                    "candidate_failure_conditions": failing["conditions"],
                }
            )

    uniform_not_candidate = [
        witness
        for witness in witnesses
        if witness["direction"] == "uniform_and_not_candidate"
    ]
    candidate_nonuniform = [
        witness
        for witness in witnesses
        if witness["direction"] == "candidate_and_nonuniform"
    ]
    if not (
        new_A_queries == 15
        and len(fixture_results) == 6
        and [row["name"] for row in uniform_not_candidate]
        == ["TERNARY-CYCLE-3"]
        and candidate_nonuniform == []
    ):
        raise AssertionError("Round15 query result classification drift")
    return {
        "fixture_results": fixture_results,
        "new5_A_block_queries": new_A_queries,
        "parent_MUTUAL_A_block_queries": 0,
        "candidate_fixture_evaluations": len(fixture_results),
        "all_registered_candidate_terminal_details_evaluated": True,
        "all_new5_nonempty_A_evaluated": True,
        "sampling": False,
        "early_stop": False,
        "uniform_and_not_candidate": uniform_not_candidate,
        "candidate_and_nonuniform": candidate_nonuniform,
        "uniform_and_not_candidate_count": len(uniform_not_candidate),
        "candidate_and_nonuniform_count": len(candidate_nonuniform),
        "new_counterexample_count": len(uniform_not_candidate)
        + len(candidate_nonuniform),
    }


def round15_report() -> dict[str, object]:
    admission = _round15_admission_gate()
    manifest = admission["manifest"]["manifest"]
    query = _round15_engine_query(
        manifest,
        admission["round14_baseline"]["mutual_H1_blocks"],
    )
    t3_witness = query["uniform_and_not_candidate"][0]
    new_verdicts: list[str] = []
    new_canonical_counterexamples = [
        t3_witness["canonical_nonisomorphic_id"]
    ]
    candidate_semantic_change = True
    additional_calibration_fixes: list[str] = []
    progress = bool(
        new_verdicts
        or new_canonical_counterexamples
        or candidate_semantic_change
        or additional_calibration_fixes
    )
    if not progress:
        raise AssertionError("Round15 registered v5 invalidation made no progress")
    calibration = admission["v5_calibration"]
    return {
        "round": "R2-round-15",
        "valid": True,
        "preregistration": {
            "issue_comment": ROUND15_PREREGISTERED_ISSUE_COMMENT,
            "created_at": ROUND15_PREREGISTERED_CREATED_AT,
            "updated_at": ROUND15_PREREGISTERED_UPDATED_AT,
            "manifest_sha256": ROUND15_REGISTERED_MANIFEST_SHA256,
            "verification_mode": "registered-semantic-safety-controls",
            "blind_search": False,
        },
        "admission": admission,
        "candidate": {
            "semantic_id": V5_SEMANTIC_ID,
            "semantic_sha256": V5_SEMANTIC_SHA256,
            "predecessor_semantic_id": V4_SEMANTIC_ID,
            "predecessor_semantic_sha256": V4_SEMANTIC_SHA256,
            "semantic_change": candidate_semantic_change,
            "calibration_sha256": calibration["canonical_sha256"],
            "calibration_bytes": calibration["canonical_bytes"],
            "calibration_mutated_after_preregistration": False,
            "verdict": "CSTAR-not-necessary",
            "verdict_is_new_this_round": False,
            "status": "invalid",
            "invalidated_semantic_id": V5_SEMANTIC_ID,
            "valid_after_round15": False,
            "invalidated_by_registered_TERNARY_CYCLE_3": True,
        },
        "population": {
            **admission["population_identity"],
            "candidate_fixture_evaluations": query[
                "candidate_fixture_evaluations"
            ],
            "new5_A_block_queries": query["new5_A_block_queries"],
            "parent_MUTUAL_A_block_queries": query[
                "parent_MUTUAL_A_block_queries"
            ],
            "all_registered_candidate_terminal_details_evaluated": query[
                "all_registered_candidate_terminal_details_evaluated"
            ],
            "all_new5_nonempty_A_evaluated": query[
                "all_new5_nonempty_A_evaluated"
            ],
            "sampling": query["sampling"],
            "early_stop": query["early_stop"],
        },
        "queries": {
            "prior_uniform_and_not_candidate_count": calibration[
                "uniform_and_not_candidate_count"
            ],
            "prior_candidate_and_nonuniform_count": calibration[
                "candidate_and_nonuniform_count"
            ],
            "new_uniform_and_not_candidate_count": query[
                "uniform_and_not_candidate_count"
            ],
            "new_candidate_and_nonuniform_count": query[
                "candidate_and_nonuniform_count"
            ],
            "uniform_and_not_candidate_count": query[
                "uniform_and_not_candidate_count"
            ],
            "candidate_and_nonuniform_count": query[
                "candidate_and_nonuniform_count"
            ],
            "uniform_and_not_candidate": query[
                "uniform_and_not_candidate"
            ],
            "candidate_and_nonuniform": query[
                "candidate_and_nonuniform"
            ],
            "new_counterexample_count": query["new_counterexample_count"],
        },
        "exact_verification": {
            "fixtures": query["fixture_results"],
            "engine_reproduced_all_registered_expectations": True,
            "H1_queried_only_for_new5": True,
        },
        "progress_audit": {
            "entry_streak": 0,
            "new_verdicts": new_verdicts,
            "new_canonical_nonisomorphic_counterexamples": (
                new_canonical_counterexamples
            ),
            "candidate_semantic_change": candidate_semantic_change,
            "additional_calibration_fixes": additional_calibration_fixes,
            "progress": progress,
            "streak_after_round": 0,
        },
        "stop_audit": {
            "stop_condition_A_completion": False,
            "stop_condition_B_finite_exhaustion": False,
            "stop_condition_C_two_valid_same_blocker_no_progress": False,
            "registered_counterexample_is_progress": True,
        },
        "coverage_limit": (
            "Exactly the immutable prior 2,161 name-free semantic cases, "
            "the overlapping registered MUTUAL control, and five strict-new "
            "fixed two-chart controls with all fifteen new nonempty Target "
            "blocks; no larger coordinate relation or doubled-cycle family "
            "is covered."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(round1_report(), ensure_ascii=False, indent=2, sort_keys=True))
