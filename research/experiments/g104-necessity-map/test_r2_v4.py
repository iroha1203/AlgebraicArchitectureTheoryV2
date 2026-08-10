#!/usr/bin/env python3
"""Focused calibration tests for the support-active joint-collapse v4 candidate."""

import ast
from hashlib import sha256
import inspect
import json
import unittest
from unittest.mock import patch

import r2_hunt
from necessity_map import H1Analysis, Nerve, NerveMorphism, UniformComparison
from r2_hunt import (
    ROUND13_BOUND_SEMANTIC_ID,
    ROUND13_BOUND_SEMANTIC_SHA256,
    ROUND13_BOUND_SPEC,
    ROUND13_PARENT_RESULTS_JSON_SHA256,
    ROUND13_PARENT_RESULTS_SUMMARY_JSON_SHA256,
    ROUND13_PARENT_ROUND12_PAYLOAD_SHA256,
    ROUND13_PREREGISTERED_CREATED_AT,
    ROUND13_PREREGISTERED_ISSUE_COMMENT,
    ROUND13_PREREGISTERED_UPDATED_AT,
    ROUND13_REGISTERED_MANIFEST_SHA256,
    ROUND14_BOUND_SEMANTIC_ID,
    ROUND14_BOUND_SEMANTIC_SHA256,
    ROUND14_BOUND_SPEC,
    ROUND14_PARENT_POPULATION,
    ROUND14_PARENT_ROUND13_CANONICAL_BYTES,
    ROUND14_PARENT_ROUND13_LEDGER_SHA256,
    ROUND14_PARENT_ROUND13_PAYLOAD_SHA256,
    ROUND14_PARENT_ROUND13_RESULT_CREATED_AT,
    ROUND14_PARENT_ROUND13_RESULT_ISSUE_COMMENT,
    ROUND14_PARENT_ROUND13_RESULT_UPDATED_AT,
    ROUND14_PREREGISTERED_CREATED_AT,
    ROUND14_PREREGISTERED_ISSUE_COMMENT,
    ROUND14_PREREGISTERED_UPDATED_AT,
    ROUND14_REGISTERED_CANONICAL_ORBIT_ID20,
    ROUND14_REGISTERED_CANONICAL_ORBIT_SHA256,
    ROUND14_REGISTERED_FIXTURE_ID20,
    ROUND14_REGISTERED_FIXTURE_SEMANTIC_SHA256,
    ROUND14_REGISTERED_MANIFEST_SHA256,
    ROUND15_BOUND_SEMANTIC_ID,
    ROUND15_BOUND_SEMANTIC_SHA256,
    ROUND15_BOUND_SPEC,
    ROUND15_PARENT_G107_SYNC_ISSUE_COMMENT,
    ROUND15_PARENT_POPULATION,
    ROUND15_PARENT_ROUND14_CANONICAL_BYTES,
    ROUND15_PARENT_ROUND14_PAYLOAD_SHA256,
    ROUND15_PARENT_ROUND14_RESULT_CREATED_AT,
    ROUND15_PARENT_ROUND14_RESULT_ISSUE_COMMENT,
    ROUND15_PARENT_ROUND14_RESULT_UPDATED_AT,
    ROUND15_PREREGISTERED_CREATED_AT,
    ROUND15_PREREGISTERED_ISSUE_COMMENT,
    ROUND15_PREREGISTERED_UPDATED_AT,
    ROUND15_REGISTERED_MANIFEST_SHA256,
    ROUND15_REGISTERED_V5_CALIBRATION_BYTES,
    ROUND15_REGISTERED_V5_CALIBRATION_SHA256,
    V4_CALIBRATION_REGISTERED_CANONICAL_BYTES,
    V4_CALIBRATION_REGISTERED_CANONICAL_SHA256,
    V4_CALIBRATION_SERIALIZATION_CONTRACT,
    V4_HUMAN_ADJUDICATION_ISSUE_COMMENT,
    V4_SEMANTIC_ID,
    V4_SEMANTIC_SHA256,
    V4_SPEC,
    V5_DEPENDENCY_AUDIT_NEW_HELPER_CALL_CLOSURE,
    V5_PACKET_FORBIDDEN_SYMBOLS,
    V5_SEMANTIC_ID,
    V5_SEMANTIC_SHA256,
    V5_SPEC,
    _a_scope,
    _case_semantic_sha256,
    _injective_pivot_assignments,
    _k_preimage_status,
    _removable_residual_mapped_edges,
    _required_catalog,
    _required_catalog_v4,
    bridge_kill_neutral_fixture,
    candidate_evaluation,
    chain3_fixture,
    contractible_triangle_fixture,
    joint_terminal_h1_calibration,
    joint_terminal_states,
    nonfree_mutual_kill_split_fixture,
    orphan_loop_fixture,
    round13_bound_canonical_support_incidence_code,
    round13_bound_comparisons,
    round13_bound_fixture,
    round13_preregistration_manifest,
    round13_preregistration_manifest_canonical_json,
    round13_preregistration_manifest_sha256,
    round13_report,
    round14_nonfree_mutual_kill_canonical_orbit_code,
    round14_preregistration_manifest,
    round14_preregistration_manifest_canonical_json,
    round14_preregistration_manifest_sha256,
    round14_report,
    round15_fixture_canonical_orbit_code,
    round15_preregistration_manifest,
    round15_preregistration_manifest_canonical_json,
    round15_preregistration_manifest_sha256,
    round15_report,
    round15_verification_fixtures,
    singular_perfect_match_3_fixture,
    support_active_v3_candidate_evaluation,
    ternary_cycle_3_fixture,
    ternary_cycle_6_fixture,
    unkilled_twin_fixture,
    v4_calibration_report,
    v4_candidate_evaluation,
    v5_candidate_evaluation,
    v5_immutable_calibration_report,
    v5_immutable_calibration_fixture_groups,
    weighted_2_fixture,
    weighted_orphan_selfloop_fixture,
)


class R2V4PureTest(unittest.TestCase):
    def test_v4_semantic_spec_is_ascii_and_deterministic(self) -> None:
        self.assertEqual(
            V4_SEMANTIC_ID,
            "R2-CSTAR-SUPPORT-ACTIVE-JOINT-COLLAPSE-v4",
        )
        self.assertEqual(V4_HUMAN_ADJUDICATION_ISSUE_COMMENT, 5232435603)
        self.assertEqual(
            V4_SEMANTIC_SHA256,
            sha256(V4_SPEC.encode("ascii")).hexdigest(),
        )
        self.assertNotIn("\r", V4_SPEC)
        self.assertFalse(any(line.endswith(" ") for line in V4_SPEC.splitlines()))
        self.assertNotIn("H1", V4_SPEC)
        self.assertNotIn("cohom", V4_SPEC.lower())
        lines = V4_SPEC.splitlines()
        self.assertTrue(all(":" in line for line in lines))
        prefixes = [line.split(":", 1)[0] for line in lines]
        self.assertEqual(len(prefixes), len(set(prefixes)))

    def test_contractible_triangle_exact_fixture_and_h1(self) -> None:
        fixture = contractible_triangle_fixture()
        self.assertEqual(fixture.name, "CONTRACTIBLE-TRIANGLE")
        self.assertEqual(fixture.morphism.coarse.vertices, 4)
        self.assertEqual(
            fixture.morphism.coarse.edges,
            ((0, 0), (1, 2), (1, 3), (2, 3)),
        )
        self.assertEqual(fixture.morphism.coarse.faces, ((1, 2, 3),))
        self.assertEqual(fixture.morphism.fine, fixture.morphism.coarse)
        self.assertEqual(fixture.morphism.vertex_map, (0, 1, 2, 3))
        self.assertEqual(fixture.morphism.edge_map, (0, 1, 2, 3))
        self.assertEqual(fixture.morphism.face_map, (0,))
        self.assertEqual(
            (
                fixture.coarse_target_count,
                fixture.fine_target_count,
                fixture.factor_pi,
            ),
            (2, 3, (0, 0, 1)),
        )
        self.assertEqual(
            fixture.coarse_chart_supports,
            (
                frozenset((0,)),
                frozenset((0, 1)),
                frozenset((0, 1)),
                frozenset((0, 1)),
            ),
        )
        self.assertEqual(
            fixture.fine_chart_supports,
            (
                frozenset((0, 1)),
                frozenset((2,)),
                frozenset((2,)),
                frozenset((2,)),
            ),
        )
        self.assertEqual(
            fixture.block_analyses(),
            (
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
            ),
        )

    def test_contractible_triangle_joint_terminals_and_candidate(self) -> None:
        fixture = contractible_triangle_fixture()
        scope = _a_scope(fixture, frozenset((0, 1)))
        terminals = joint_terminal_states(scope)
        self.assertEqual(len(terminals), 3)
        self.assertTrue(all(len(state.trace) == 1 for state in terminals))
        self.assertEqual(
            {state.trace[0].coarse_edge for state in terminals},
            {1, 2, 3},
        )
        self.assertTrue(
            all(state.trace[0].kind == "coarse" for state in terminals)
        )
        self.assertEqual(
            support_active_v3_candidate_evaluation(fixture)["aggregate"],
            {
                "C0*": False,
                "C1*": False,
                "C2*": False,
                "C3*": True,
                "C4*": False,
                "C5*": True,
                "C6*": True,
            },
        )
        candidate = v4_candidate_evaluation(fixture)
        self.assertTrue(candidate["all"])
        self.assertEqual(
            candidate["aggregate"],
            {f"C{index}*": True for index in range(7)},
        )
        self.assertEqual(candidate["terminal_quantifier"], "forall")
        self.assertEqual(candidate["whole"]["terminal_count"], 3)
        self.assertEqual(
            [row["terminal_count"] for row in candidate["per_subset"]],
            [3, 3, 3],
        )

    def test_contractible_all_terminal_h1_analyses_are_exact(self) -> None:
        fixture = contractible_triangle_fixture()
        for targets, expected in fixture.block_analyses():
            rows = joint_terminal_h1_calibration(
                _a_scope(fixture, targets)
            )
            self.assertEqual(len(rows), 3)
            self.assertTrue(all(row.preserved for row in rows))
            self.assertTrue(
                all(row.original_analysis == expected for row in rows)
            )
            self.assertTrue(
                all(row.reduced_analysis == expected for row in rows)
            )

    def test_fine_only_packet_reaches_a_closed_terminal(self) -> None:
        coarse = Nerve(1, (), ())
        fine = Nerve(1, ((0, 0),), ((0, 0, 0),))
        fixture = UniformComparison(
            name="V4-FINE-ONLY-UNIT",
            morphism=NerveMorphism(
                coarse,
                fine,
                (0,),
                (None,),
                (None,),
            ),
            coarse_target_count=1,
            fine_target_count=1,
            factor_pi=(0,),
            coarse_chart_supports=(frozenset((0,)),),
            fine_chart_supports=(frozenset((0,)),),
        )
        terminals = joint_terminal_states(_a_scope(fixture, frozenset((0,))))
        self.assertEqual(len(terminals), 1)
        self.assertEqual(len(terminals[0].trace), 1)
        self.assertEqual(terminals[0].trace[0].kind, "fine-only")
        self.assertEqual(terminals[0].retained_fine_edges, ())
        self.assertEqual(terminals[0].retained_fine_face_classes, ())
        h1_rows = joint_terminal_h1_calibration(
            _a_scope(fixture, frozenset((0,)))
        )
        expected_h1 = H1Analysis(0, 0, 0, True, True, True)
        self.assertEqual(len(h1_rows), 1)
        self.assertEqual(h1_rows[0].original_analysis, expected_h1)
        self.assertEqual(h1_rows[0].reduced_analysis, expected_h1)
        self.assertTrue(h1_rows[0].preserved)

    def test_mixed_k_preimage_maps_are_ambiguous(self) -> None:
        coarse_members = frozenset((7, 8))
        self.assertEqual(
            _k_preimage_status((7, 8), coarse_members),
            "preimage",
        )
        self.assertEqual(
            _k_preimage_status((7, None), coarse_members),
            "ambiguous",
        )
        self.assertEqual(
            _k_preimage_status((7, 9), coarse_members),
            "ambiguous",
        )
        self.assertEqual(
            _k_preimage_status((9, None), coarse_members),
            "unrelated",
        )

    def test_shared_pivot_assignments_are_rejected(self) -> None:
        self.assertEqual(
            _injective_pivot_assignments((3, 4), ((8,), (8,))),
            (),
        )
        self.assertEqual(
            _injective_pivot_assignments((3, 4), ((8, 9), (8, 9))),
            (
                ((3, 8), (4, 9)),
                ((3, 9), (4, 8)),
            ),
        )

    def test_residual_bridge_is_accepted(self) -> None:
        nerve = Nerve(2, ((0, 1),), ())
        fixture = UniformComparison(
            name="V4-RESIDUAL-BRIDGE",
            morphism=NerveMorphism(
                nerve,
                nerve,
                (0, 1),
                (0,),
                (),
            ),
            coarse_target_count=1,
            fine_target_count=1,
            factor_pi=(0,),
            coarse_chart_supports=(frozenset((0,)), frozenset((0,))),
            fine_chart_supports=(frozenset((0,)), frozenset((0,))),
        )
        scope = _a_scope(fixture, frozenset((0,)))
        self.assertEqual(
            _removable_residual_mapped_edges(
                scope,
                (),
                set(),
                {0},
                0,
            ),
            (0,),
        )

    def test_residual_selfloop_and_cycle_nonbridge_are_rejected(self) -> None:
        loop = Nerve(1, ((0, 0),), ())
        loop_fixture = UniformComparison(
            name="V4-RESIDUAL-SELFLOOP",
            morphism=NerveMorphism(loop, loop, (0,), (0,), ()),
            coarse_target_count=1,
            fine_target_count=1,
            factor_pi=(0,),
            coarse_chart_supports=(frozenset((0,)),),
            fine_chart_supports=(frozenset((0,)),),
        )
        loop_scope = _a_scope(loop_fixture, frozenset((0,)))
        self.assertIsNone(
            _removable_residual_mapped_edges(
                loop_scope,
                (),
                set(),
                {0},
                0,
            )
        )

        cycle = Nerve(3, ((0, 1), (0, 2), (1, 2)), ())
        cycle_fixture = UniformComparison(
            name="V4-RESIDUAL-CYCLE",
            morphism=NerveMorphism(
                cycle,
                cycle,
                (0, 1, 2),
                (0, 1, 2),
                (),
            ),
            coarse_target_count=1,
            fine_target_count=1,
            factor_pi=(0,),
            coarse_chart_supports=(
                frozenset((0,)),
                frozenset((0,)),
                frozenset((0,)),
            ),
            fine_chart_supports=(
                frozenset((0,)),
                frozenset((0,)),
                frozenset((0,)),
            ),
        )
        cycle_scope = _a_scope(cycle_fixture, frozenset((0,)))
        self.assertIsNone(
            _removable_residual_mapped_edges(
                cycle_scope,
                (),
                set(),
                {0, 1, 2},
                0,
            )
        )

    def test_orphan_loop_blocks_the_unsound_coarse_packet(self) -> None:
        fixture = orphan_loop_fixture()
        self.assertEqual(fixture.name, "ORPHAN-LOOP")
        self.assertEqual(fixture.morphism.coarse.vertices, 1)
        self.assertEqual(
            fixture.morphism.coarse.edges,
            ((0, 0), (0, 0), (0, 0)),
        )
        self.assertEqual(fixture.morphism.coarse.faces, ((0, 1, 2),))
        self.assertEqual(fixture.morphism.fine.vertices, 1)
        self.assertEqual(
            fixture.morphism.fine.edges,
            ((0, 0), (0, 0), (0, 0), (0, 0)),
        )
        self.assertEqual(fixture.morphism.fine.faces, ((0, 1, 2),))
        self.assertEqual(fixture.morphism.vertex_map, (0,))
        self.assertEqual(fixture.morphism.edge_map, (0, 1, 2, 0))
        self.assertEqual(fixture.morphism.face_map, (0,))
        self.assertEqual(
            (
                fixture.coarse_target_count,
                fixture.fine_target_count,
                fixture.factor_pi,
            ),
            (1, 1, (0,)),
        )
        self.assertEqual(
            fixture.coarse_chart_supports,
            (frozenset((0,)),),
        )
        self.assertEqual(
            fixture.fine_chart_supports,
            (frozenset((0,)),),
        )
        self.assertEqual(
            fixture.block_analyses(),
            (
                (
                    frozenset((0,)),
                    H1Analysis(2, 3, 2, True, False, False),
                ),
            ),
        )
        terminals = joint_terminal_states(_a_scope(fixture, frozenset((0,))))
        self.assertEqual(len(terminals), 2)
        self.assertEqual(
            {state.trace[0].coarse_edge for state in terminals},
            {1, 2},
        )
        candidate = v4_candidate_evaluation(fixture)
        self.assertFalse(candidate["aggregate"]["C5*"])
        self.assertFalse(candidate["all"])
        self.assertEqual(candidate["whole"]["terminal_count"], 2)
        self.assertEqual(
            [row["terminal_count"] for row in candidate["per_subset"]],
            [2],
        )
        h1_rows = joint_terminal_h1_calibration(
            _a_scope(fixture, frozenset((0,)))
        )
        expected_h1 = H1Analysis(2, 3, 2, True, False, False)
        self.assertEqual(len(h1_rows), 2)
        self.assertTrue(all(row.preserved for row in h1_rows))
        self.assertTrue(
            all(row.original_analysis == expected_h1 for row in h1_rows)
        )
        self.assertTrue(
            all(row.reduced_analysis == expected_h1 for row in h1_rows)
        )

    def test_registered_histories_and_v4_catalog_are_preserved(self) -> None:
        chain = chain3_fixture()
        unkilled = unkilled_twin_fixture()
        self.assertFalse(
            candidate_evaluation(chain, c5_mode="clique")["aggregate"]["C5*"]
        )
        self.assertTrue(
            candidate_evaluation(chain, c5_mode="certified")["all"]
        )
        self.assertTrue(v4_candidate_evaluation(chain)["all"])
        self.assertTrue(
            candidate_evaluation(unkilled, c5_mode="component")["all"]
        )
        self.assertFalse(
            candidate_evaluation(unkilled, c5_mode="certified")["aggregate"][
                "C5*"
            ]
        )
        self.assertFalse(
            v4_candidate_evaluation(unkilled)["aggregate"]["C5*"]
        )
        self.assertEqual(len(_required_catalog()), 13)
        self.assertEqual(len(_required_catalog_v4()), 16)

    def test_edge_fiber_guarded_c5_literal_regression(self) -> None:
        fixture = next(
            comparison
            for comparison in _required_catalog()
            if comparison.name == "EdgeFiberObstruction"
        )
        candidate = v4_candidate_evaluation(fixture)
        self.assertFalse(fixture.is_uniform())
        self.assertFalse(candidate["aggregate"]["C5*"])
        self.assertFalse(candidate["all"])
        self.assertEqual(candidate["whole"]["terminal_count"], 2)
        for terminal in candidate["whole"]["terminals"]:
            self.assertEqual(
                terminal["C5_C6_guarded_coarse_edges"],
                [0],
            )
            self.assertEqual(
                terminal["direct_lifttwin"]["0"]["lifts"],
                [0, 1],
            )
            self.assertEqual(
                terminal["direct_lifttwin"]["0"]["direct_edges"],
                [],
            )
            self.assertFalse(
                terminal["direct_lifttwin"]["0"]["c5_edge_holds"]
            )

    def test_bridge_kill_neutral_exact_guard_calibration(self) -> None:
        fixture = bridge_kill_neutral_fixture()
        self.assertEqual(fixture.name, "BRIDGE-KILL-NEUTRAL")
        self.assertEqual(fixture.morphism.coarse.vertices, 2)
        self.assertEqual(
            fixture.morphism.coarse.edges,
            ((0, 1), (1, 1), (0, 0)),
        )
        self.assertEqual(
            fixture.morphism.coarse.faces,
            ((0, 0, 1), (1, 1, 1)),
        )
        self.assertEqual(fixture.morphism.fine.vertices, 2)
        self.assertEqual(
            fixture.morphism.fine.edges,
            ((0, 1), (0, 1), (1, 1), (0, 0)),
        )
        self.assertEqual(
            fixture.morphism.fine.faces,
            ((0, 1, 2), (2, 2, 2)),
        )
        self.assertEqual(fixture.morphism.vertex_map, (0, 1))
        self.assertEqual(fixture.morphism.edge_map, (0, 0, 1, 2))
        self.assertEqual(fixture.morphism.face_map, (0, 1))
        self.assertEqual(
            (
                fixture.coarse_target_count,
                fixture.fine_target_count,
                fixture.factor_pi,
            ),
            (1, 1, (0,)),
        )
        full = (frozenset((0,)), frozenset((0,)))
        self.assertEqual(fixture.coarse_chart_supports, full)
        self.assertEqual(fixture.fine_chart_supports, full)
        self.assertEqual(
            fixture.block_analyses(),
            (
                (
                    frozenset((0,)),
                    H1Analysis(1, 1, 1, True, True, True),
                ),
            ),
        )
        candidate = v4_candidate_evaluation(fixture)
        self.assertTrue(candidate["all"])
        self.assertEqual(candidate["whole"]["terminal_count"], 1)
        terminal = candidate["whole"]["terminals"][0]
        self.assertEqual(terminal["trace"], [])
        self.assertEqual(
            terminal["coarse_reduction"]["critical_edges"],
            [1, 2],
        )
        self.assertEqual(
            terminal["fine_reduction"]["critical_edges"],
            [0, 1, 2, 3],
        )
        self.assertEqual(
            terminal["C5_C6_guarded_coarse_edges"],
            [0, 1, 2],
        )
        self.assertEqual(
            terminal["direct_lifttwin"]["0"]["direct_edges"],
            [[0, 1]],
        )
        self.assertTrue(
            terminal["direct_lifttwin"]["0"]["c5_edge_holds"]
        )
        h1_rows = joint_terminal_h1_calibration(
            _a_scope(fixture, frozenset((0,)))
        )
        self.assertEqual(len(h1_rows), 1)
        self.assertTrue(h1_rows[0].preserved)
        self.assertEqual(
            h1_rows[0].reduced_analysis,
            H1Analysis(1, 1, 1, True, True, True),
        )


class R2V4FullCalibrationTest(unittest.TestCase):
    def test_full_prior_1918_calibration(self) -> None:
        report = v4_calibration_report()
        self.assertEqual(
            report["human_adjudication_issue_comment"],
            5232435603,
        )
        self.assertFalse(report["is_round_report"])
        self.assertFalse(report["query_generator_added"])
        self.assertEqual(report["required_catalog"]["mismatch_count"], 0)
        population = report["prior_population"]
        self.assertEqual(population["raw_cases"], 1918)
        self.assertEqual(population["unique_full_name_free_ids"], 1918)
        self.assertEqual(population["unique_truncated_20hex_ids"], 1918)
        self.assertEqual(population["uniform_and_not_candidate_count"], 0)
        self.assertEqual(population["candidate_and_nonuniform_count"], 0)
        self.assertTrue(population["all_cases_evaluated"])
        normalization = report["terminal_h1_normalization_calibration"]
        self.assertIn("not a general", normalization["statement"])
        required = normalization["required_catalog_16"]
        self.assertEqual(required["case_count"], 16)
        self.assertEqual(required["mismatch_count"], 0)
        self.assertTrue(required["all_terminal_analyses_preserved"])
        self.assertTrue(required["whole_full_A_is_also_in_nonempty_A"])
        self.assertFalse(required["general_preservation_theorem"])
        prior = normalization["prior_population_1918"]
        self.assertEqual(prior["case_count"], 1918)
        self.assertEqual(prior["mismatch_count"], 0)
        self.assertTrue(prior["all_terminal_analyses_preserved"])
        self.assertTrue(prior["whole_full_A_is_also_in_nonempty_A"])
        self.assertFalse(prior["general_preservation_theorem"])


class R2Round13PureManifestTest(unittest.TestCase):
    def test_round13_bound_spec_and_literal_generator_counts(self) -> None:
        self.assertEqual(
            ROUND13_BOUND_SEMANTIC_ID,
            "R13-CROSS-CHART-TRIANGLE-SUPPORT-v1",
        )
        self.assertEqual(
            ROUND13_BOUND_SEMANTIC_SHA256,
            sha256(ROUND13_BOUND_SPEC.encode("ascii")).hexdigest(),
        )
        lines = ROUND13_BOUND_SPEC.splitlines()
        self.assertTrue(all(":" in line for line in lines))
        prefixes = [line.split(":", 1)[0] for line in lines]
        self.assertEqual(len(prefixes), len(set(prefixes)))
        self.assertNotIn("\r", ROUND13_BOUND_SPEC)
        self.assertEqual(
            ROUND13_PARENT_RESULTS_JSON_SHA256,
            "cabfbcae7075280a6d10de3c819c25ca2396a21deaed2099bafdd71daa252306",
        )
        self.assertEqual(
            ROUND13_PARENT_RESULTS_SUMMARY_JSON_SHA256,
            "afa334056b52938044c0acad9b693a0c437300382b855f32450af5750020caa5",
        )
        self.assertEqual(
            ROUND13_PARENT_ROUND12_PAYLOAD_SHA256,
            "c9ab928190491610ff1e394fb16fb4e132f117374a317505fbd2025ab5a09f90",
        )
        self.assertEqual(ROUND13_PREREGISTERED_ISSUE_COMMENT, 5234690436)
        self.assertEqual(
            ROUND13_PREREGISTERED_CREATED_AT,
            "2026-08-10T00:34:52Z",
        )
        self.assertEqual(
            ROUND13_PREREGISTERED_UPDATED_AT,
            "2026-08-10T00:34:52Z",
        )
        self.assertEqual(
            ROUND13_REGISTERED_MANIFEST_SHA256,
            "8bebea1711e8e786f0a4b4c3dd73458c83db7432facbf04d5abcbfdb7d285a6c",
        )
        self.assertEqual(
            V4_CALIBRATION_REGISTERED_CANONICAL_SHA256,
            "20770592f4b8f8cb7dbb269364bb8707eff4b518decc5039916ebfc072dec4e3",
        )
        self.assertEqual(V4_CALIBRATION_REGISTERED_CANONICAL_BYTES, 96886)
        self.assertEqual(
            V4_CALIBRATION_SERIALIZATION_CONTRACT,
            {
                "encoding": "utf-8",
                "ensure_ascii": False,
                "indent": 2,
                "sort_keys": True,
                "trailing_newline": True,
            },
        )
        comparisons = round13_bound_comparisons()
        self.assertEqual(len(comparisons), 242)
        self.assertTrue(
            all(isinstance(case, UniformComparison) for case in comparisons)
        )
        self.assertEqual(
            sum(bool(case.morphism.coarse.faces) for case in comparisons),
            121,
        )
        self.assertEqual(
            sum(not case.morphism.coarse.faces for case in comparisons),
            121,
        )
        self.assertEqual(
            len({_case_semantic_sha256(c) for c in comparisons}),
            242,
        )

    def test_round13_canonical_swap_invariance_and_drift(self) -> None:
        common = {
            "coarse_anchor_support": frozenset((0,)),
            "coarse_triangle_support": frozenset((0, 1)),
            "fine_triangle_support": frozenset((2,)),
        }
        base = round13_bound_fixture(
            face_present=True,
            fine_anchor_support=frozenset((0,)),
            **common,
        )
        swapped = round13_bound_fixture(
            face_present=True,
            fine_anchor_support=frozenset((1,)),
            **common,
        )
        support_drift = round13_bound_fixture(
            face_present=True,
            coarse_anchor_support=frozenset((0, 1)),
            coarse_triangle_support=common["coarse_triangle_support"],
            fine_anchor_support=frozenset((0,)),
            fine_triangle_support=common["fine_triangle_support"],
        )
        face_drift = round13_bound_fixture(
            face_present=False,
            fine_anchor_support=frozenset((0,)),
            **common,
        )
        base_code = round13_bound_canonical_support_incidence_code(base)
        self.assertEqual(
            base_code,
            round13_bound_canonical_support_incidence_code(swapped),
        )
        self.assertNotEqual(
            _case_semantic_sha256(base),
            _case_semantic_sha256(swapped),
        )
        self.assertNotEqual(
            base_code,
            round13_bound_canonical_support_incidence_code(support_drift),
        )
        self.assertNotEqual(
            base_code,
            round13_bound_canonical_support_incidence_code(face_drift),
        )

    def test_round13_manifest_has_no_forbidden_dependency(self) -> None:
        forbidden = AssertionError(
            "Round13 pure manifest called a forbidden evaluator"
        )
        with (
            patch.object(
                UniformComparison,
                "block_analyses",
                side_effect=forbidden,
            ),
            patch.object(
                UniformComparison,
                "is_uniform",
                side_effect=forbidden,
            ),
            patch.object(r2_hunt, "analyze_h1", side_effect=forbidden),
            patch.object(
                r2_hunt,
                "candidate_evaluation",
                side_effect=forbidden,
            ),
            patch.object(
                r2_hunt,
                "v4_candidate_evaluation",
                side_effect=forbidden,
            ),
            patch.object(
                r2_hunt,
                "v4_calibration_report",
                side_effect=forbidden,
            ),
            patch.object(r2_hunt, "round12_report", side_effect=forbidden),
        ):
            manifest = round13_preregistration_manifest()
            canonical_json = round13_preregistration_manifest_canonical_json()
            manifest_sha256 = round13_preregistration_manifest_sha256()

        self.assertEqual(
            manifest["labeled_population"]["raw_support_and_face_flag_cases"],
            882,
        )
        self.assertEqual(
            manifest["labeled_population"]["compatible_cases"],
            242,
        )
        orbit = manifest["canonical_orbit_audit"]
        self.assertEqual(orbit["single_position_compatible_labeled_pairs"], 11)
        self.assertEqual(orbit["single_position_swap_fixed_pairs"], 5)
        self.assertEqual(orbit["burnside_orbits_per_face_flag"], 73)
        self.assertEqual(orbit["canonical_support_incidence_orbit_count"], 146)
        self.assertEqual(orbit["full_sha256_collision_count"], 0)
        self.assertEqual(orbit["truncated_20hex_collision_count"], 0)
        population = manifest["prior_population_comparison"]
        self.assertEqual(population["prior_unique_name_free_ids"], 1918)
        self.assertEqual(population["bound_unique_name_free_ids"], 242)
        self.assertEqual(population["overlap_count"], 0)
        self.assertEqual(population["new_count"], 242)
        self.assertTrue(population["strict_new"])
        self.assertGreater(population["new_count"], 0)
        self.assertEqual(population["union_count"], 2160)
        self.assertEqual(population["full_sha256_collision_count"], 0)
        self.assertEqual(population["truncated_20hex_collision_count"], 0)
        contractible = contractible_triangle_fixture()
        contractible_id = _case_semantic_sha256(contractible)
        contract = manifest["contractible_and_control"]
        self.assertEqual(
            contract["contractible_name_free_sha256"],
            contractible_id,
        )
        self.assertTrue(contract["contractible_included"])
        self.assertTrue(contract["face_absent_control_included"])
        self.assertTrue(contract["filled_and_absent_ids_distinct"])
        self.assertTrue(contract["coarse_anchor_triangle_support_split"])
        self.assertTrue(contract["fine_anchor_triangle_support_split"])
        self.assertTrue(contract["cross_chart_components_exact"])
        self.assertIn(
            contractible_id,
            {case["name_free_semantic_sha256"] for case in manifest["cases"]},
        )

        catalog = manifest["required16_pure_catalog"]
        self.assertEqual(catalog["count"], 16)
        for row in catalog["cases"]:
            summary_json = json.dumps(
                row["summary"],
                sort_keys=True,
                separators=(",", ":"),
            )
            self.assertEqual(
                row["summary_sha256"],
                sha256(summary_json.encode("utf-8")).hexdigest(),
            )
            name_free = dict(row["summary"])
            name_free.pop("name")
            name_free_json = json.dumps(
                name_free,
                sort_keys=True,
                separators=(",", ":"),
            )
            self.assertEqual(
                row["name_free_semantic_sha256"],
                sha256(name_free_json.encode("utf-8")).hexdigest(),
            )
            self.assertEqual(
                row["name_free_id20"],
                row["name_free_semantic_sha256"][:20],
            )
        refs = manifest["parent_artifact_references"]
        self.assertEqual(refs["results.json"], ROUND13_PARENT_RESULTS_JSON_SHA256)
        self.assertEqual(
            refs["results-summary.json"],
            ROUND13_PARENT_RESULTS_SUMMARY_JSON_SHA256,
        )
        self.assertEqual(
            refs["round12_payload"],
            ROUND13_PARENT_ROUND12_PAYLOAD_SHA256,
        )
        v4_reference = manifest["v4_candidate_reference"]
        self.assertEqual(
            v4_reference["calibration_payload"],
            {
                "canonical_sha256": (
                    V4_CALIBRATION_REGISTERED_CANONICAL_SHA256
                ),
                "canonical_bytes": (
                    V4_CALIBRATION_REGISTERED_CANONICAL_BYTES
                ),
                "serialization": V4_CALIBRATION_SERIALIZATION_CONTRACT,
            },
        )
        self.assertEqual(json.loads(canonical_json), manifest)
        self.assertEqual(
            manifest_sha256,
            sha256(canonical_json.encode("utf-8")).hexdigest(),
        )
        self.assertNotIn("manifest_sha256", manifest)
        self.assertIsNone(manifest["preregistered_issue_comment"])
        self.assertFalse(manifest["query_gate_added"])
        self.assertFalse(manifest["round13_report_added"])

    def test_round13_manifest_one_bit_drift_calls_no_query(self) -> None:
        drifted = json.loads(
            json.dumps(round13_preregistration_manifest())
        )
        drifted["labeled_population"][
            "raw_support_and_face_flag_cases"
        ] = 883
        with (
            patch.object(
                r2_hunt,
                "round13_preregistration_manifest",
                return_value=drifted,
            ),
            patch.object(
                r2_hunt,
                "_round13_v4_calibration_admission",
            ) as calibration_gate,
            patch.object(
                r2_hunt,
                "_round13_parent_artifact_admission",
            ) as parent_gate,
            patch.object(
                r2_hunt,
                "_round13_population_query",
            ) as query,
        ):
            with self.assertRaises(AssertionError):
                round13_report()
        calibration_gate.assert_not_called()
        parent_gate.assert_not_called()
        query.assert_not_called()

    def test_round13_calibration_one_bit_drift_calls_no_query(self) -> None:
        canonical_bytes = r2_hunt._v4_calibration_canonical_bytes

        def flip_one_bit(report: dict[str, object]) -> bytes:
            rendered = bytearray(canonical_bytes(report))
            rendered[-1] ^= 1
            return bytes(rendered)

        with (
            patch.object(
                r2_hunt,
                "_round13_manifest_admission",
                return_value={"one_bit_manifest_baseline": True},
            ),
            patch.object(
                r2_hunt,
                "_v4_calibration_canonical_bytes",
                side_effect=flip_one_bit,
            ),
            patch.object(
                r2_hunt,
                "_round13_parent_artifact_admission",
            ) as parent_gate,
            patch.object(
                r2_hunt,
                "_round13_population_query",
            ) as query,
        ):
            with self.assertRaises(AssertionError):
                round13_report()
        parent_gate.assert_not_called()
        query.assert_not_called()

    def test_round13_parent_one_bit_drift_calls_no_query(self) -> None:
        drifted_parent_sha256 = (
            "d" + ROUND13_PARENT_RESULTS_JSON_SHA256[1:]
        )
        with (
            patch.object(
                r2_hunt,
                "_round13_manifest_admission",
                return_value={"one_bit_manifest_baseline": True},
            ),
            patch.object(
                r2_hunt,
                "_round13_v4_calibration_admission",
                return_value={"one_bit_calibration_baseline": True},
            ),
            patch.object(
                r2_hunt,
                "ROUND13_PARENT_RESULTS_JSON_SHA256",
                drifted_parent_sha256,
            ),
            patch.object(
                r2_hunt,
                "_round13_population_query",
            ) as query,
        ):
            with self.assertRaises(AssertionError):
                round13_report()
        query.assert_not_called()

    def test_round13_exact_admitted_report_and_full_evaluation(self) -> None:
        report = round13_report()
        self.assertEqual(
            set(report),
            {
                "round",
                "valid",
                "preregistration",
                "admission",
                "candidate",
                "bound",
                "population",
                "queries",
                "result_ledger",
                "query_contract",
                "exact_controls",
                "progress_audit",
                "stop_audit",
                "coverage_limit",
            },
        )
        self.assertTrue(report["valid"])
        self.assertEqual(report["round"], "R2-round-13")
        preregistration = report["preregistration"]
        self.assertEqual(preregistration["issue_comment"], 5234690436)
        self.assertEqual(
            preregistration["manifest_sha256"],
            ROUND13_REGISTERED_MANIFEST_SHA256,
        )
        admission = report["admission"]
        self.assertTrue(admission["all_gates_pass"])
        self.assertEqual(
            admission["gate_order"],
            [
                "pure_preregistration_manifest",
                "v4_calibration",
                "immutable_parent_artifacts",
            ],
        )
        self.assertEqual(
            admission["manifest"]["manifest_sha256"],
            ROUND13_REGISTERED_MANIFEST_SHA256,
        )
        self.assertEqual(
            admission["calibration"]["canonical_sha256"],
            V4_CALIBRATION_REGISTERED_CANONICAL_SHA256,
        )
        self.assertEqual(
            admission["calibration"]["canonical_bytes"],
            V4_CALIBRATION_REGISTERED_CANONICAL_BYTES,
        )
        parent = admission["parent_artifacts"]
        self.assertEqual(
            parent["results.json"]["canonical_sha256"],
            ROUND13_PARENT_RESULTS_JSON_SHA256,
        )
        self.assertEqual(
            parent["results-summary.json"]["canonical_sha256"],
            ROUND13_PARENT_RESULTS_SUMMARY_JSON_SHA256,
        )
        self.assertTrue(
            parent["results-summary.json"]["committed_bytes_exact"]
        )
        self.assertEqual(
            parent["round12_payload_sha256"],
            ROUND13_PARENT_ROUND12_PAYLOAD_SHA256,
        )

        population = report["population"]
        self.assertEqual(population["prior_cases"], 1918)
        self.assertEqual(population["new_cases"], 242)
        self.assertEqual(population["total_cases"], 2160)
        self.assertEqual(population["unique_full_name_free_ids"], 2160)
        self.assertEqual(population["unique_truncated_20hex_ids"], 2160)
        self.assertEqual(population["full_sha256_collision_count"], 0)
        self.assertEqual(population["truncated_20hex_collision_count"], 0)
        self.assertTrue(population["new_disjoint_from_prior"])
        self.assertEqual(population["new_A_queries"], 726)
        self.assertEqual(
            population["total_A_queries"],
            population["prior_A_queries"] + 726,
        )
        self.assertFalse(population["sampling"])
        self.assertFalse(population["early_stop"])
        self.assertTrue(population["all_cases_and_nonempty_A_evaluated"])
        self.assertEqual(report["bound"]["canonical_orbit_count"], 146)
        self.assertEqual(
            report["candidate"]["previous_semantic_id"],
            r2_hunt.CERTIFIED_SEMANTIC_ID,
        )
        self.assertEqual(
            report["candidate"]["previous_semantic_sha256"],
            r2_hunt.CERTIFIED_SEMANTIC_SHA256,
        )
        self.assertTrue(report["candidate"]["semantic_change_from_v3"])

        queries = report["queries"]
        self.assertEqual(
            queries["uniform_and_not_candidate_count"],
            len(queries["uniform_and_not_candidate"]),
        )
        self.assertEqual(
            queries["candidate_and_nonuniform_count"],
            len(queries["candidate_and_nonuniform"]),
        )
        for direction in (
            "uniform_and_not_candidate",
            "candidate_and_nonuniform",
        ):
            for witness in queries[direction]:
                self.assertEqual(witness["direction"], direction)
                self.assertIn("minimal_failing_A", witness)
                self.assertIn("exact_h1", witness)
                self.assertEqual(
                    set(witness["candidate_aggregate"]),
                    {f"C{index}*" for index in range(7)},
                )

        ledger = report["result_ledger"]
        self.assertEqual(ledger["row_count"], 2160)
        self.assertEqual(len(ledger["compact_rows"]), 2160)
        ledger_json = json.dumps(
            ledger["compact_rows"],
            sort_keys=True,
            separators=(",", ":"),
        )
        self.assertEqual(
            ledger["compact_json_sha256"],
            sha256(ledger_json.encode("utf-8")).hexdigest(),
        )
        self.assertEqual(
            set(report["query_contract"]),
            {
                "candidate_predicate_reads_global_or_A_block_H1",
                "candidate_predicate_uses_preregistered_local_C3_linear_algebra",
                "sampling",
                "early_stop",
            },
        )
        self.assertFalse(
            report["query_contract"][
                "candidate_predicate_reads_global_or_A_block_H1"
            ]
        )
        self.assertTrue(
            report["query_contract"][
                "candidate_predicate_uses_preregistered_local_C3_linear_algebra"
            ]
        )
        self.assertFalse(report["query_contract"]["sampling"])
        self.assertFalse(report["query_contract"]["early_stop"])
        contractible = report["exact_controls"]["CONTRACTIBLE-TRIANGLE"]
        absent = report["exact_controls"]["face_absent_same_support"]
        self.assertEqual(contractible["category"], "round13_new")
        self.assertEqual(absent["category"], "round13_new")
        self.assertEqual(len(contractible["A_blocks"]), 3)
        self.assertEqual(len(absent["A_blocks"]), 3)
        self.assertTrue(contractible["uniform"])
        self.assertTrue(contractible["candidate_all"])
        edge_fiber = report["exact_controls"]["EdgeFiberObstruction"]
        self.assertFalse(edge_fiber["uniform"])
        self.assertFalse(edge_fiber["candidate_all"])

        progress = report["progress_audit"]
        self.assertEqual(
            set(progress),
            {
                "entry_streak",
                "new_verdicts",
                "new_canonical_nonisomorphic_counterexamples",
                "candidate_semantic_change",
                "additional_calibration_fixes",
                "new_counterexample_count",
                "new_counterexamples",
                "progress",
                "streak_after_round",
            },
        )
        self.assertEqual(progress["entry_streak"], 0)
        self.assertTrue(progress["candidate_semantic_change"])
        self.assertTrue(progress["additional_calibration_fixes"])
        self.assertEqual(
            progress["new_counterexample_count"],
            len(progress["new_counterexamples"]),
        )
        expected_verdicts = sorted(
            {
                "CSTAR-not-necessary"
                for witness in progress["new_counterexamples"]
                if witness["direction"] == "uniform_and_not_candidate"
            }
            | {
                "CSTAR-not-sufficient"
                for witness in progress["new_counterexamples"]
                if witness["direction"] == "candidate_and_nonuniform"
            }
        )
        self.assertEqual(progress["new_verdicts"], expected_verdicts)
        self.assertEqual(
            progress["new_canonical_nonisomorphic_counterexamples"],
            sorted(
                {
                    witness["canonical_nonisomorphic_id"]
                    for witness in progress["new_counterexamples"]
                }
            ),
        )
        expected_progress = bool(
            progress["new_verdicts"]
            or progress["new_canonical_nonisomorphic_counterexamples"]
            or progress["candidate_semantic_change"]
            or progress["additional_calibration_fixes"]
        )
        self.assertEqual(progress["progress"], expected_progress)
        self.assertTrue(progress["progress"])
        self.assertEqual(progress["streak_after_round"], 0)
        stop = report["stop_audit"]
        self.assertFalse(stop["stop_condition_A_completion"])
        self.assertFalse(stop["stop_condition_B_finite_exhaustion"])
        self.assertFalse(
            stop["stop_condition_C_two_valid_same_blocker_no_progress"]
        )


class R2Round14PurePreregistrationTest(unittest.TestCase):
    def test_round14_exact_fixture_spec_and_static_expectations(self) -> None:
        self.assertEqual(
            ROUND14_BOUND_SEMANTIC_ID,
            "R14-NONFREE-MUTUAL-KILL-SPLIT-v1",
        )
        self.assertEqual(
            ROUND14_BOUND_SEMANTIC_SHA256,
            sha256(ROUND14_BOUND_SPEC.encode("ascii")).hexdigest(),
        )
        self.assertEqual(
            ROUND14_BOUND_SEMANTIC_SHA256,
            "c74f19f0972745138a9a3d4f80eeb9d5907c03021290c091d3541b2791acb12c",
        )
        lines = ROUND14_BOUND_SPEC.splitlines()
        self.assertTrue(all(":" in line for line in lines))
        prefixes = [line.split(":", 1)[0] for line in lines]
        self.assertEqual(len(prefixes), len(set(prefixes)))
        self.assertNotIn("\r", ROUND14_BOUND_SPEC)
        self.assertFalse(
            any(line.endswith(" ") for line in ROUND14_BOUND_SPEC.splitlines())
        )
        self.assertEqual(
            ROUND14_PARENT_ROUND13_PAYLOAD_SHA256,
            "e15fc8dcb99ea7e8e17b1a52cc045379f9757c558a92f25e9d1bfc2bda5450e3",
        )
        self.assertEqual(ROUND14_PARENT_ROUND13_CANONICAL_BYTES, 5_604_143)
        self.assertEqual(
            ROUND14_PARENT_ROUND13_LEDGER_SHA256,
            "8950edc32e11c7809bffc4ff3cb9b5f64b76905825e416133d414abd065737e0",
        )
        self.assertEqual(
            ROUND14_PARENT_ROUND13_RESULT_ISSUE_COMMENT,
            5234839619,
        )
        self.assertEqual(
            ROUND14_PARENT_ROUND13_RESULT_CREATED_AT,
            "2026-08-10T01:08:00Z",
        )
        self.assertEqual(
            ROUND14_PARENT_ROUND13_RESULT_UPDATED_AT,
            "2026-08-10T01:08:00Z",
        )
        self.assertEqual(ROUND14_PARENT_POPULATION, 2160)
        self.assertEqual(ROUND14_PREREGISTERED_ISSUE_COMMENT, 5234939066)
        self.assertEqual(
            ROUND14_PREREGISTERED_CREATED_AT,
            "2026-08-10T01:28:53Z",
        )
        self.assertEqual(
            ROUND14_PREREGISTERED_UPDATED_AT,
            "2026-08-10T01:28:53Z",
        )
        self.assertEqual(
            ROUND14_REGISTERED_MANIFEST_SHA256,
            "eaa0c96376bb1d724505b16c6df6b7d519e27b7451da6a94d06b673d65e1f309",
        )
        self.assertEqual(
            ROUND14_REGISTERED_FIXTURE_SEMANTIC_SHA256,
            "e908498046aa55e1781a8d0a4d7ec06e213272222dd374126eb5ce9d39cb058e",
        )
        self.assertEqual(
            ROUND14_REGISTERED_FIXTURE_ID20,
            "e908498046aa55e1781a",
        )
        self.assertEqual(
            ROUND14_REGISTERED_CANONICAL_ORBIT_SHA256,
            "4ce2e10bcafaff1da04136a13151cab65566b652ff3392faa79ecb39c3823698",
        )
        self.assertEqual(
            ROUND14_REGISTERED_CANONICAL_ORBIT_ID20,
            "4ce2e10bcafaff1da041",
        )

        fixture = nonfree_mutual_kill_split_fixture()
        self.assertEqual(fixture.name, "NONFREE-MUTUAL-KILL-SPLIT")
        self.assertEqual(fixture.morphism.coarse, fixture.morphism.fine)
        self.assertEqual(fixture.morphism.coarse.vertices, 2)
        self.assertEqual(
            fixture.morphism.coarse.edges,
            ((0, 0), (1, 1), (1, 1)),
        )
        self.assertEqual(
            fixture.morphism.coarse.faces,
            ((1, 1, 2), (2, 2, 1)),
        )
        self.assertEqual(fixture.morphism.vertex_map, (0, 1))
        self.assertEqual(fixture.morphism.edge_map, (0, 1, 2))
        self.assertEqual(fixture.morphism.face_map, (0, 1))
        self.assertEqual(
            (
                fixture.coarse_target_count,
                fixture.fine_target_count,
                fixture.factor_pi,
            ),
            (2, 3, (0, 0, 1)),
        )
        self.assertEqual(
            fixture.coarse_chart_supports,
            (frozenset((0,)), frozenset((0, 1))),
        )
        self.assertEqual(
            fixture.fine_chart_supports,
            (frozenset((0, 1)), frozenset((2,))),
        )
        coarse_edges, coarse_faces = r2_hunt.derived_cell_supports(
            fixture.morphism.coarse,
            fixture.coarse_chart_supports,
        )
        fine_edges, fine_faces = r2_hunt.derived_cell_supports(
            fixture.morphism.fine,
            fixture.fine_chart_supports,
        )
        self.assertEqual(
            coarse_edges,
            (
                frozenset((0,)),
                frozenset((0, 1)),
                frozenset((0, 1)),
            ),
        )
        self.assertEqual(
            coarse_faces,
            (frozenset((0, 1)), frozenset((0, 1))),
        )
        self.assertEqual(
            fine_edges,
            (
                frozenset((0, 1)),
                frozenset((2,)),
                frozenset((2,)),
            ),
        )
        self.assertEqual(
            fine_faces,
            (frozenset((2,)), frozenset((2,))),
        )

    def test_round14_fixed_symmetry_orbit_code(self) -> None:
        fixture = nonfree_mutual_kill_split_fixture()
        code = round14_nonfree_mutual_kill_canonical_orbit_code(fixture)
        self.assertEqual(code["group_order"], 4)
        self.assertEqual(code["orbit_size"], 1)
        self.assertEqual(code["stabilizer_order"], 4)
        self.assertEqual(len(code["actions"]), 4)
        self.assertEqual(
            code["sha256"],
            sha256(code["compact_json"].encode("ascii")).hexdigest(),
        )
        self.assertEqual(code["id20"], code["sha256"][:20])
        action_payloads = {
            r2_hunt._round14_relabelled_payload_json(
                fixture,
                swap_mutual_cells=swap_mutual_cells,
                swap_fine_targets_0_1=swap_fine_targets_0_1,
            )
            for swap_mutual_cells in (False, True)
            for swap_fine_targets_0_1 in (False, True)
        }
        self.assertEqual(action_payloads, {code["compact_json"]})

        support_drift = UniformComparison(
            name="ROUND14-SUPPORT-DRIFT",
            morphism=fixture.morphism,
            coarse_target_count=2,
            fine_target_count=3,
            factor_pi=(0, 0, 1),
            coarse_chart_supports=(
                frozenset((0,)),
                frozenset((1,)),
            ),
            fine_chart_supports=fixture.fine_chart_supports,
        )
        with self.assertRaises(ValueError):
            round14_nonfree_mutual_kill_canonical_orbit_code(support_drift)

    def test_round14_manifest_is_pure_and_strictly_expands_2160(self) -> None:
        forbidden = AssertionError(
            "Round14 pure manifest called a forbidden evaluator"
        )
        with (
            patch.object(
                UniformComparison,
                "block_analyses",
                side_effect=forbidden,
            ),
            patch.object(
                UniformComparison,
                "is_uniform",
                side_effect=forbidden,
            ),
            patch.object(r2_hunt, "analyze_h1", side_effect=forbidden),
            patch.object(
                r2_hunt,
                "candidate_evaluation",
                side_effect=forbidden,
            ),
            patch.object(
                r2_hunt,
                "v4_candidate_evaluation",
                side_effect=forbidden,
            ),
            patch.object(
                r2_hunt,
                "v4_calibration_report",
                side_effect=forbidden,
            ),
            patch.object(
                r2_hunt,
                "joint_terminal_states",
                side_effect=forbidden,
            ),
            patch.object(
                r2_hunt,
                "joint_terminal_h1_calibration",
                side_effect=forbidden,
            ),
            patch.object(
                r2_hunt,
                "_round13_population_query",
                side_effect=forbidden,
            ),
            patch.object(
                r2_hunt,
                "round13_report",
                side_effect=forbidden,
            ),
        ):
            manifest = round14_preregistration_manifest()
            canonical_json = (
                round14_preregistration_manifest_canonical_json()
            )
            manifest_sha256 = round14_preregistration_manifest_sha256()

        self.assertEqual(
            manifest["discovery_classification"],
            {
                "mode": "pre-query-human-static-exact-verification",
                "blind_search": False,
                "engine_query_observed": False,
                "human_static_counterexample_expected": True,
            },
        )
        self.assertEqual(
            manifest["semantic_bound"]["semantic_id"],
            ROUND14_BOUND_SEMANTIC_ID,
        )
        self.assertEqual(
            manifest["semantic_bound"]["semantic_sha256"],
            ROUND14_BOUND_SEMANTIC_SHA256,
        )
        self.assertEqual(
            manifest["fixed_candidate_reference"],
            {
                "semantic_id": V4_SEMANTIC_ID,
                "semantic_sha256": V4_SEMANTIC_SHA256,
                "calibration_sha256": (
                    V4_CALIBRATION_REGISTERED_CANONICAL_SHA256
                ),
                "calibration_bytes": (
                    V4_CALIBRATION_REGISTERED_CANONICAL_BYTES
                ),
            },
        )
        parent = manifest["round13_parent_reference"]
        self.assertEqual(
            parent["payload_sha256"],
            ROUND14_PARENT_ROUND13_PAYLOAD_SHA256,
        )
        self.assertEqual(
            parent["canonical_bytes"],
            ROUND14_PARENT_ROUND13_CANONICAL_BYTES,
        )
        self.assertEqual(
            parent["compact_ledger_sha256"],
            ROUND14_PARENT_ROUND13_LEDGER_SHA256,
        )
        self.assertEqual(
            parent["result_issue_comment"],
            ROUND14_PARENT_ROUND13_RESULT_ISSUE_COMMENT,
        )
        self.assertEqual(
            parent["created_at"],
            ROUND14_PARENT_ROUND13_RESULT_CREATED_AT,
        )
        self.assertEqual(
            parent["updated_at"],
            ROUND14_PARENT_ROUND13_RESULT_UPDATED_AT,
        )
        self.assertEqual(parent["population"], ROUND14_PARENT_POPULATION)
        self.assertEqual(
            (
                parent["uniform_and_not_candidate_count"],
                parent["candidate_and_nonuniform_count"],
            ),
            (0, 0),
        )
        self.assertTrue(parent["progress"])
        self.assertEqual(parent["streak_after_round"], 0)

        fixture = nonfree_mutual_kill_split_fixture()
        fixture_row = manifest["fixture"]
        self.assertEqual(
            fixture_row["name_free_semantic_sha256"],
            _case_semantic_sha256(fixture),
        )
        self.assertEqual(
            fixture_row["name_free_id20"],
            fixture_row["name_free_semantic_sha256"][:20],
        )
        self.assertEqual(
            fixture_row["canonical_orbit_code"],
            round14_nonfree_mutual_kill_canonical_orbit_code(fixture),
        )
        self.assertEqual(
            fixture_row["expected_derived_supports"],
            fixture_row["actual_derived_supports"],
        )
        self.assertEqual(
            fixture_row["raw_face_class_occurrences"],
            {"x": [0, 1], "y": [0, 1]},
        )
        self.assertEqual(fixture_row["allowed_joint_packet_count_expected"], 0)

        expected = manifest["expected_engine_verification"]
        self.assertEqual(
            [
                (
                    row["coarse_targets_A"],
                    row["coarse_h1_dimension"],
                    row["fine_h1_dimension"],
                    row["comparison_rank"],
                    row["isomorphism"],
                )
                for row in expected["H1_blocks"]
            ],
            [
                ([0], 1, 1, 1, True),
                ([1], 0, 0, 0, True),
                ([0, 1], 1, 1, 1, True),
            ],
        )
        self.assertTrue(expected["uniform"])
        candidate = expected["v4_candidate"]
        self.assertEqual(
            candidate["whole_conditions"],
            {"C0*": False, "C5*": True, "C6*": True},
        )
        self.assertEqual(candidate["whole_terminal_count"], 1)
        self.assertEqual(candidate["whole_trace"], [])
        self.assertEqual(
            [
                (
                    row["coarse_targets_A"],
                    row["conditions"],
                    row["terminal_count"],
                    row["trace"],
                )
                for row in candidate["per_nonempty_A"]
            ],
            [
                (
                    [0],
                    {
                        "C1*": False,
                        "C2*": False,
                        "C3*": True,
                        "C4*": False,
                    },
                    1,
                    [],
                ),
                (
                    [1],
                    {
                        "C1*": True,
                        "C2*": True,
                        "C3*": True,
                        "C4*": True,
                    },
                    1,
                    [],
                ),
                (
                    [0, 1],
                    {
                        "C1*": True,
                        "C2*": True,
                        "C3*": True,
                        "C4*": True,
                    },
                    1,
                    [],
                ),
            ],
        )
        self.assertEqual(
            candidate["vector_C0_through_C6"],
            [False, False, False, True, False, True, True],
        )
        self.assertFalse(candidate["candidate_all"])
        self.assertEqual(
            expected["expected_direction"],
            "uniform_and_not_candidate",
        )
        self.assertEqual(
            expected["expected_new_verdict_if_reproduced"],
            "CSTAR-not-necessary",
        )
        self.assertTrue(expected["expectation_is_not_engine_observation"])

        population = manifest["pure_population_gate"]
        self.assertEqual(population["prior_unique_name_free_ids"], 2160)
        self.assertEqual(population["new_unique_name_free_ids"], 1)
        self.assertEqual(population["overlap_count"], 0)
        self.assertEqual(population["new_count"], 1)
        self.assertTrue(population["strict_new"])
        self.assertEqual(population["union_count"], 2161)
        self.assertEqual(population["full_sha256_collision_count"], 0)
        self.assertEqual(population["truncated_20hex_collision_count"], 0)
        self.assertEqual(json.loads(canonical_json), manifest)
        self.assertEqual(
            manifest_sha256,
            sha256(canonical_json.encode("utf-8")).hexdigest(),
        )
        self.assertEqual(
            manifest_sha256,
            ROUND14_REGISTERED_MANIFEST_SHA256,
        )
        self.assertNotIn("manifest_sha256", manifest)
        self.assertIsNone(manifest["preregistered_issue_comment"])
        self.assertFalse(manifest["query_gate_added"])
        self.assertFalse(manifest["round14_report_added"])

    def test_round14_manifest_drift_calls_no_later_gate_or_query(self) -> None:
        drifted = json.loads(
            json.dumps(round14_preregistration_manifest())
        )
        drifted["pure_population_gate"]["union_count"] = 2162
        with (
            patch.object(
                r2_hunt,
                "round14_preregistration_manifest",
                return_value=drifted,
            ),
            patch.object(
                r2_hunt,
                "_round14_round13_baseline_admission",
            ) as round13_gate,
            patch.object(
                r2_hunt,
                "_round14_population_identity_admission",
            ) as identity_gate,
            patch.object(
                r2_hunt,
                "_round14_engine_query",
            ) as query,
        ):
            with self.assertRaises(AssertionError):
                round14_report()
        round13_gate.assert_not_called()
        identity_gate.assert_not_called()
        query.assert_not_called()

    def test_round14_round13_drift_calls_no_identity_or_query(self) -> None:
        manifest = round14_preregistration_manifest()
        with (
            patch.object(
                r2_hunt,
                "_round14_manifest_admission",
                return_value={"manifest": manifest},
            ),
            patch.object(
                r2_hunt,
                "_round14_round13_baseline_admission",
                side_effect=AssertionError("one-bit Round13 payload drift"),
            ),
            patch.object(
                r2_hunt,
                "_round14_population_identity_admission",
            ) as identity_gate,
            patch.object(
                r2_hunt,
                "_round14_engine_query",
            ) as query,
        ):
            with self.assertRaises(AssertionError):
                round14_report()
        identity_gate.assert_not_called()
        query.assert_not_called()

    def test_round14_identity_drift_calls_no_query(self) -> None:
        manifest = round14_preregistration_manifest()
        with (
            patch.object(
                r2_hunt,
                "_round14_manifest_admission",
                return_value={"manifest": manifest},
            ),
            patch.object(
                r2_hunt,
                "_round14_round13_baseline_admission",
                return_value={"all_gates_pass": True},
            ),
            patch.object(
                r2_hunt,
                "_round14_population_identity_admission",
                side_effect=AssertionError("Round14 new semantic ID drift"),
            ),
            patch.object(
                r2_hunt,
                "_round14_engine_query",
            ) as query,
        ):
            with self.assertRaises(AssertionError):
                round14_report()
        query.assert_not_called()

    def test_round14_engine_mismatch_is_not_a_valid_result(self) -> None:
        manifest = round14_preregistration_manifest()
        admission = {
            "manifest": {"manifest": manifest},
            "all_gates_pass": True,
        }
        with (
            patch.object(
                r2_hunt,
                "_round14_admission_gate",
                return_value=admission,
            ),
            patch.object(
                r2_hunt,
                "_round14_engine_query",
                side_effect=AssertionError(
                    "engine did not reproduce preregistered values"
                ),
            ) as query,
        ):
            with self.assertRaises(AssertionError):
                round14_report()
        query.assert_called_once_with(manifest)

    def test_round14_exact_admitted_report_and_reproduction(self) -> None:
        report = round14_report()
        self.assertEqual(
            set(report),
            {
                "round",
                "valid",
                "preregistration",
                "admission",
                "candidate",
                "population",
                "queries",
                "exact_verification",
                "progress_audit",
                "stop_audit",
                "coverage_limit",
            },
        )
        self.assertEqual(report["round"], "R2-round-14")
        self.assertTrue(report["valid"])
        preregistration = report["preregistration"]
        self.assertEqual(preregistration["issue_comment"], 5234939066)
        self.assertEqual(
            preregistration["created_at"],
            "2026-08-10T01:28:53Z",
        )
        self.assertEqual(
            preregistration["updated_at"],
            "2026-08-10T01:28:53Z",
        )
        self.assertEqual(
            preregistration["manifest_sha256"],
            ROUND14_REGISTERED_MANIFEST_SHA256,
        )
        self.assertEqual(
            preregistration["discovery_mode"],
            "pre-query-human-static-exact-verification",
        )
        self.assertFalse(preregistration["blind_search"])

        admission = report["admission"]
        self.assertTrue(admission["all_gates_pass"])
        self.assertEqual(
            admission["gate_order"],
            [
                "immutable_pure_preregistration_manifest_and_comment",
                "immutable_round13_full_result",
                "prior2160_plus_new1_identity_and_collision",
            ],
        )
        self.assertEqual(
            admission["manifest"]["manifest_sha256"],
            ROUND14_REGISTERED_MANIFEST_SHA256,
        )
        round13 = admission["round13_baseline"]
        self.assertEqual(
            round13["payload_sha256"],
            ROUND14_PARENT_ROUND13_PAYLOAD_SHA256,
        )
        self.assertEqual(
            round13["canonical_bytes"],
            ROUND14_PARENT_ROUND13_CANONICAL_BYTES,
        )
        self.assertEqual(
            round13["compact_ledger_sha256"],
            ROUND14_PARENT_ROUND13_LEDGER_SHA256,
        )
        self.assertEqual(
            round13["result_issue_comment"],
            ROUND14_PARENT_ROUND13_RESULT_ISSUE_COMMENT,
        )
        self.assertEqual(
            round13["created_at"],
            ROUND14_PARENT_ROUND13_RESULT_CREATED_AT,
        )
        self.assertEqual(
            round13["updated_at"],
            ROUND14_PARENT_ROUND13_RESULT_UPDATED_AT,
        )
        self.assertEqual(
            (
                round13["uniform_and_not_candidate_count"],
                round13["candidate_and_nonuniform_count"],
            ),
            (0, 0),
        )
        self.assertTrue(round13["progress"])
        self.assertEqual(round13["streak_after_round"], 0)

        population = report["population"]
        self.assertEqual(population["prior_cases"], 2160)
        self.assertEqual(population["new_cases"], 1)
        self.assertEqual(population["total_cases"], 2161)
        self.assertEqual(population["unique_full_name_free_ids"], 2161)
        self.assertEqual(population["unique_truncated_20hex_ids"], 2161)
        self.assertEqual(population["full_sha256_collision_count"], 0)
        self.assertEqual(population["truncated_20hex_collision_count"], 0)
        self.assertEqual(
            population["new_semantic_sha256"],
            ROUND14_REGISTERED_FIXTURE_SEMANTIC_SHA256,
        )
        self.assertEqual(
            population["new_canonical_orbit_sha256"],
            ROUND14_REGISTERED_CANONICAL_ORBIT_SHA256,
        )
        self.assertEqual(population["new_A_block_queries"], 3)
        self.assertTrue(population["all_new_cases_and_nonempty_A_evaluated"])
        self.assertFalse(population["sampling"])
        self.assertFalse(population["early_stop"])

        candidate = report["candidate"]
        self.assertEqual(candidate["semantic_id"], V4_SEMANTIC_ID)
        self.assertEqual(candidate["semantic_sha256"], V4_SEMANTIC_SHA256)
        self.assertFalse(candidate["semantic_change"])
        self.assertFalse(candidate["calibration_mutated"])
        self.assertEqual(candidate["status"], "invalid")
        self.assertEqual(
            candidate["invalidated_semantic_id"],
            V4_SEMANTIC_ID,
        )
        self.assertFalse(candidate["valid_after_round14"])
        self.assertTrue(
            candidate["invalidated_by_reproduced_necessity_counterexample"]
        )

        queries = report["queries"]
        self.assertEqual(queries["uniform_and_not_candidate_count"], 1)
        self.assertEqual(queries["candidate_and_nonuniform_count"], 0)
        self.assertEqual(queries["candidate_and_nonuniform"], [])
        self.assertEqual(queries["new_counterexample_count"], 1)
        self.assertEqual(len(queries["uniform_and_not_candidate"]), 1)
        witness = queries["uniform_and_not_candidate"][0]
        self.assertEqual(
            witness["id"],
            ROUND14_REGISTERED_FIXTURE_SEMANTIC_SHA256,
        )
        self.assertEqual(
            witness["canonical_nonisomorphic_id"],
            ROUND14_REGISTERED_CANONICAL_ORBIT_SHA256,
        )
        self.assertEqual(witness["direction"], "uniform_and_not_candidate")
        self.assertEqual(witness["minimal_failing_A"], [0])
        self.assertEqual(
            witness["exact_h1"],
            {
                "coarse_targets_A": [0],
                "coarse_h1_dimension": 1,
                "fine_h1_dimension": 1,
                "comparison_rank": 1,
                "injective": True,
                "surjective": True,
                "isomorphism": True,
            },
        )

        verification = report["exact_verification"]
        self.assertTrue(verification["uniform"])
        self.assertEqual(verification["new_A_block_queries"], 3)
        self.assertTrue(
            verification["engine_reproduced_preregistered_expectations"]
        )
        self.assertEqual(
            verification["v4_candidate"]["vector_C0_through_C6"],
            [False, False, False, True, False, True, True],
        )
        self.assertFalse(verification["v4_candidate"]["candidate_all"])
        self.assertEqual(
            verification["v4_candidate"]["whole_terminal_count"],
            1,
        )
        self.assertEqual(
            verification["v4_candidate"]["whole_trace"],
            [],
        )
        self.assertTrue(
            all(
                row["terminal_count"] == 1 and row["trace"] == []
                for row in verification["v4_candidate"]["per_nonempty_A"]
            )
        )

        progress = report["progress_audit"]
        self.assertEqual(
            progress,
            {
                "entry_streak": 0,
                "new_verdicts": ["CSTAR-not-necessary"],
                "new_canonical_nonisomorphic_counterexamples": [
                    ROUND14_REGISTERED_CANONICAL_ORBIT_SHA256
                ],
                "candidate_semantic_change": False,
                "additional_calibration_fixes": [],
                "progress": True,
                "streak_after_round": 0,
            },
        )
        stop = report["stop_audit"]
        self.assertFalse(stop["stop_condition_A_completion"])
        self.assertFalse(stop["stop_condition_B_finite_exhaustion"])
        self.assertFalse(
            stop["stop_condition_C_two_valid_same_blocker_no_progress"]
        )
        self.assertTrue(stop["reproduced_counterexample_is_progress"])


class R2V5Round15PurePreregistrationTest(unittest.TestCase):
    def test_v5_semantic_specs_are_ascii_exact_and_dependency_bounded(self) -> None:
        self.assertEqual(
            V5_SEMANTIC_ID,
            "R2-CSTAR-COORDINATE-DOUBLED-CYCLE-v5",
        )
        self.assertEqual(
            V5_SEMANTIC_SHA256,
            sha256(V5_SPEC.encode("ascii")).hexdigest(),
        )
        self.assertEqual(
            ROUND15_BOUND_SEMANTIC_ID,
            "R15-V5-SEMANTIC-SAFETY-CALIBRATION-v1",
        )
        self.assertEqual(
            ROUND15_BOUND_SEMANTIC_SHA256,
            sha256(ROUND15_BOUND_SPEC.encode("ascii")).hexdigest(),
        )
        for spec in (V5_SPEC, ROUND15_BOUND_SPEC):
            self.assertNotIn("\r", spec)
            self.assertFalse(
                any(line.endswith(" ") for line in spec.splitlines())
            )
            prefixes = [line.split(":", 1)[0] for line in spec.splitlines()]
            self.assertTrue(all(":" in line for line in spec.splitlines()))
            self.assertEqual(len(prefixes), len(set(prefixes)))

        registered_closure_literal = (
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
        self.assertEqual(
            V5_DEPENDENCY_AUDIT_NEW_HELPER_CALL_CLOSURE,
            registered_closure_literal,
        )
        module_tree = ast.parse(inspect.getsource(r2_hunt))
        function_nodes = {
            node.name: node
            for node in module_tree.body
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
        }
        call_graph = {
            function_name: {
                call.func.id
                for call in ast.walk(function_node)
                if isinstance(call, ast.Call)
                and isinstance(call.func, ast.Name)
                and call.func.id in function_nodes
            }
            for function_name, function_node in function_nodes.items()
        }
        reachable = set()
        frontier = ["v5_candidate_evaluation"]
        while frontier:
            function_name = frontier.pop()
            if function_name in reachable:
                continue
            reachable.add(function_name)
            frontier.extend(sorted(call_graph[function_name] - reachable))
        reachable_v5_core = {
            function_name
            for function_name in reachable
            if function_name.startswith("_v5")
            or function_name
            in {
                "_apply_v5_packet",
                "v5_terminal_states",
                "v5_candidate_evaluation",
            }
        }
        self.assertEqual(
            reachable_v5_core,
            set(registered_closure_literal),
        )

        immutable_v4_packet_boundary = {
            "_signed_face_coefficient",
            "_raw_occurrence_classes",
            "_k_preimage_status",
            "_injective_pivot_assignments",
            "_removable_residual_mapped_edges",
            "_joint_packet_variants",
        }
        audited_nodes = [
            function_nodes[function_name]
            for function_name in (
                reachable_v5_core | immutable_v4_packet_boundary
            )
        ]
        referenced_symbols = {
            symbol
            for function_node in audited_nodes
            for node in ast.walk(function_node)
            for symbol in (
                node.id
                if isinstance(node, ast.Name)
                else node.attr
                if isinstance(node, ast.Attribute)
                else None,
            )
            if symbol is not None
        }
        self.assertTrue(
            set(V5_PACKET_FORBIDDEN_SYMBOLS).isdisjoint(referenced_symbols)
        )
        local_c3_call_count = sum(
            isinstance(node, ast.Call)
            and isinstance(node.func, ast.Name)
            and node.func.id == "_c3"
            for function_name in reachable_v5_core
            for node in ast.walk(function_nodes[function_name])
        )
        self.assertEqual(local_c3_call_count, 1)
        self.assertIn("coordinate-dependency", V5_SPEC)
        self.assertIn("closed-doubled-cycle", V5_SPEC)

    def test_round15_parent_provenance_literals(self) -> None:
        self.assertEqual(
            ROUND15_PARENT_ROUND14_PAYLOAD_SHA256,
            "17c9907928a63cdf97e474e7f8813447601010ede07bbe7a43b525ef8551b450",
        )
        self.assertEqual(ROUND15_PARENT_ROUND14_CANONICAL_BYTES, 22_818)
        self.assertEqual(
            ROUND15_PARENT_ROUND14_RESULT_ISSUE_COMMENT,
            5235064396,
        )
        self.assertEqual(
            ROUND15_PARENT_ROUND14_RESULT_CREATED_AT,
            "2026-08-10T01:55:17Z",
        )
        self.assertEqual(
            ROUND15_PARENT_ROUND14_RESULT_UPDATED_AT,
            "2026-08-10T01:55:17Z",
        )
        self.assertEqual(ROUND15_PARENT_G107_SYNC_ISSUE_COMMENT, 5235067306)
        self.assertEqual(ROUND15_PARENT_POPULATION, 2161)

    def test_round15_exact_fixture_arrays_maps_and_supports(self) -> None:
        fixtures = round15_verification_fixtures()
        self.assertEqual(
            tuple(fixture.name for fixture in fixtures),
            (
                "NONFREE-MUTUAL-KILL-SPLIT",
                "WEIGHTED-2",
                "TERNARY-CYCLE-3",
                "TERNARY-CYCLE-6",
                "SINGULAR-PERFECT-MATCH-3",
                "WEIGHTED-ORPHAN-SELFLOOP",
            ),
        )
        common_coarse_supports = (
            frozenset((0,)),
            frozenset((0, 1)),
        )
        common_fine_supports = (
            frozenset((0, 1)),
            frozenset((2,)),
        )
        for fixture in fixtures:
            self.assertEqual(fixture.coarse_target_count, 2)
            self.assertEqual(fixture.fine_target_count, 3)
            self.assertEqual(fixture.factor_pi, (0, 0, 1))
            self.assertEqual(fixture.morphism.vertex_map, (0, 1))
            self.assertEqual(
                fixture.coarse_chart_supports,
                common_coarse_supports,
            )
            self.assertEqual(
                fixture.fine_chart_supports,
                common_fine_supports,
            )

        weighted = weighted_2_fixture()
        self.assertEqual(
            weighted.morphism.coarse,
            Nerve(
                2,
                ((0, 0), (1, 1), (1, 1)),
                ((1, 2, 1), (2, 1, 2)),
            ),
        )
        self.assertEqual(weighted.morphism.fine, weighted.morphism.coarse)
        self.assertEqual(weighted.morphism.edge_map, (0, 1, 2))
        self.assertEqual(weighted.morphism.face_map, (0, 1))

        ternary3 = ternary_cycle_3_fixture()
        self.assertEqual(
            ternary3.morphism.coarse.faces,
            ((1, 2, 3), (2, 3, 1), (3, 1, 2)),
        )
        ternary6 = ternary_cycle_6_fixture()
        self.assertEqual(
            ternary6.morphism.coarse.faces,
            (
                (1, 2, 3),
                (2, 3, 4),
                (3, 4, 5),
                (4, 5, 6),
                (5, 6, 1),
                (6, 1, 2),
            ),
        )
        singular = singular_perfect_match_3_fixture()
        self.assertEqual(
            singular.morphism.coarse.faces,
            ((1, 3, 2), (2, 3, 1), (3, 3, 3)),
        )
        orphan = weighted_orphan_selfloop_fixture()
        self.assertEqual(orphan.morphism.edge_map, (0, 1, 2, 1))
        self.assertEqual(orphan.morphism.face_map, (0, 1))
        self.assertEqual(len(orphan.morphism.fine.edges), 4)

    def test_round15_canonical_code_is_name_free_and_relabel_invariant(self) -> None:
        base = ternary_cycle_3_fixture()
        edge_relabel = {0: 0, 1: 2, 2: 3, 3: 1}
        relabelled_faces = tuple(
            tuple(edge_relabel[edge] for edge in face)
            for face in reversed(base.morphism.coarse.faces)
        )
        relabelled_nerve = Nerve(
            2,
            base.morphism.coarse.edges,
            relabelled_faces,
        )
        relabelled = UniformComparison(
            name="NAME-DOES-NOT-ENTER-CANONICAL-CODE",
            morphism=NerveMorphism(
                relabelled_nerve,
                relabelled_nerve,
                (0, 1),
                (0, 1, 2, 3),
                (0, 1, 2),
            ),
            coarse_target_count=2,
            fine_target_count=3,
            factor_pi=(0, 0, 1),
            coarse_chart_supports=base.coarse_chart_supports,
            fine_chart_supports=base.fine_chart_supports,
        )
        base_code = round15_fixture_canonical_orbit_code(base)
        relabelled_code = round15_fixture_canonical_orbit_code(relabelled)
        self.assertEqual(base_code["compact_json"], relabelled_code["compact_json"])
        self.assertEqual(base_code["sha256"], relabelled_code["sha256"])
        self.assertEqual(
            base_code["sha256"],
            sha256(base_code["compact_json"].encode("ascii")).hexdigest(),
        )
        self.assertEqual(base_code["id20"], base_code["sha256"][:20])

        support_drift = UniformComparison(
            name="SUPPORT-DRIFT",
            morphism=base.morphism,
            coarse_target_count=2,
            fine_target_count=3,
            factor_pi=(0, 0, 1),
            coarse_chart_supports=base.coarse_chart_supports,
            fine_chart_supports=(
                frozenset((0, 1)),
                frozenset((0, 2)),
            ),
        )
        with self.assertRaises(ValueError):
            round15_fixture_canonical_orbit_code(support_drift)

    def test_round15_manifest_is_pure_and_evaluator_independent(self) -> None:
        forbidden = AssertionError("pure Round15 manifest called evaluator")
        with (
            patch.object(
                UniformComparison,
                "block_analyses",
                side_effect=forbidden,
            ) as block_analyses,
            patch.object(
                UniformComparison,
                "is_uniform",
                side_effect=forbidden,
            ) as is_uniform,
            patch.object(
                r2_hunt,
                "analyze_h1",
                side_effect=forbidden,
            ) as analyze,
            patch.object(
                r2_hunt,
                "v4_candidate_evaluation",
                side_effect=forbidden,
            ) as v4_candidate,
            patch.object(
                r2_hunt,
                "v5_candidate_evaluation",
                side_effect=forbidden,
            ) as v5_candidate,
            patch.object(
                r2_hunt,
                "v4_calibration_report",
                side_effect=forbidden,
            ) as calibration,
            patch.object(
                r2_hunt,
                "v5_immutable_calibration_report",
                side_effect=forbidden,
            ) as v5_calibration,
            patch.object(
                r2_hunt,
                "round13_report",
                side_effect=forbidden,
            ) as round13,
            patch.object(
                r2_hunt,
                "round14_report",
                side_effect=forbidden,
            ) as round14,
            patch.object(
                r2_hunt,
                "_round15_engine_query",
                side_effect=forbidden,
            ) as round15_query,
            patch.object(
                r2_hunt,
                "round15_report",
                side_effect=forbidden,
            ) as round15_round,
        ):
            manifest = round15_preregistration_manifest()
        for evaluator in (
            block_analyses,
            is_uniform,
            analyze,
            v4_candidate,
            v5_candidate,
            calibration,
            v5_calibration,
            round13,
            round14,
            round15_query,
            round15_round,
        ):
            evaluator.assert_not_called()
        self.assertEqual(
            manifest["dependency_contract"],
            {
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
        )

    def test_round15_manifest_exact_hand_expectations_and_population(self) -> None:
        manifest = round15_preregistration_manifest()
        self.assertEqual(
            json.loads(round15_preregistration_manifest_canonical_json()),
            manifest,
        )
        self.assertEqual(
            round15_preregistration_manifest_sha256(),
            sha256(
                round15_preregistration_manifest_canonical_json().encode(
                    "utf-8"
                )
            ).hexdigest(),
        )
        self.assertEqual(
            manifest["round14_parent_reference"],
            {
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
                "population": 2161,
                "uniform_and_not_candidate_count": 1,
                "candidate_and_nonuniform_count": 0,
                "new_verdict": "CSTAR-not-necessary",
                "invalidated_semantic_id": V4_SEMANTIC_ID,
                "progress": True,
                "streak_after_round": 0,
            },
        )
        self.assertEqual(
            manifest["pure_population_gate"],
            {
                "prior_unique_name_free_ids": 2161,
                "verification_fixture_count": 6,
                "prior_overlap_names": ["NONFREE-MUTUAL-KILL-SPLIT"],
                "prior_overlap_count": 1,
                "strict_new_fixture_count": 5,
                "union_unique_name_free_ids": 2166,
                "full_sha256_collision_count": 0,
                "truncated_20hex_collision_count": 0,
                "canonical_fixture_code_collision_count": 0,
            },
        )
        fixed_candidate = manifest["fixed_candidate"]
        self.assertEqual(
            fixed_candidate["dependency_audit_new_helper_call_closure"],
            list(V5_DEPENDENCY_AUDIT_NEW_HELPER_CALL_CLOSURE),
        )
        self.assertEqual(
            fixed_candidate["immutable_v4_dependency_boundary_sha256"],
            V4_SEMANTIC_SHA256,
        )
        self.assertEqual(
            manifest["future_calibration_partition"],
            {
                "required_catalog_case_count": 16,
                "immutable_prior_case_count": 2161,
                "round15_control_count": 6,
                "parent_MUTUAL_overlap_is_inside_immutable_prior": True,
                "new_round15_control_count_excluded_from_calibration": 5,
                "required_and_prior_calibration_excludes_new_round15_controls": True,
                "new_control_H1_or_candidate_execution_before_preregistration": False,
            },
        )
        fixture_rows = {row["name"]: row for row in manifest["fixtures"]}
        self.assertEqual(len(fixture_rows), 6)
        for row in fixture_rows.values():
            self.assertEqual(len(row["name_free_semantic_sha256"]), 64)
            self.assertEqual(len(row["name_free_id20"]), 20)
            self.assertEqual(len(row["canonical_orbit_code"]["sha256"]), 64)
            self.assertEqual(len(row["canonical_orbit_code"]["id20"]), 20)
            self.assertTrue(
                row["hand_expected_v5_candidate"][
                    "expectation_is_not_engine_observation"
                ]
            )
        self.assertTrue(
            fixture_rows["NONFREE-MUTUAL-KILL-SPLIT"][
                "hand_expected_v5_candidate"
            ]["candidate_all"]
        )
        self.assertTrue(
            fixture_rows["WEIGHTED-2"]["hand_expected_v5_candidate"][
                "candidate_all"
            ]
        )
        self.assertEqual(
            fixture_rows["TERNARY-CYCLE-3"]["hand_expected_v5_candidate"][
                "vector_C0_through_C6"
            ],
            [False, False, False, True, False, True, True],
        )
        self.assertEqual(
            fixture_rows["TERNARY-CYCLE-6"]["hand_expected_H1_blocks"][1][
                "coarse_h1_dimension"
            ],
            2,
        )
        self.assertEqual(
            fixture_rows["TERNARY-CYCLE-6"]["hand_expected_H1_blocks"][1][
                "fine_h1_dimension"
            ],
            2,
        )
        self.assertFalse(
            fixture_rows["SINGULAR-PERFECT-MATCH-3"][
                "hand_expected_v5_candidate"
            ]["candidate_all"]
        )
        self.assertEqual(
            fixture_rows["WEIGHTED-ORPHAN-SELFLOOP"][
                "hand_packet_structure"
            ]["packet_count_expected_whole"],
            0,
        )
        self.assertIsNone(manifest["preregistered_issue_comment"])
        self.assertFalse(manifest["admission_gate_added"])
        self.assertFalse(manifest["round15_query_added"])
        self.assertFalse(manifest["round15_report_added"])

    def test_round15_all_hand_expectations_equal_independent_literals(self) -> None:
        fixture_rows = {
            row["name"]: row
            for row in round15_preregistration_manifest()["fixtures"]
        }
        expected_h1_literal = {
            "NONFREE-MUTUAL-KILL-SPLIT": [
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
            ],
            "WEIGHTED-2": [
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
            ],
            "TERNARY-CYCLE-3": [
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
            ],
            "TERNARY-CYCLE-6": [
                {
                    "coarse_targets_A": [0],
                    "coarse_h1_dimension": 3,
                    "fine_h1_dimension": 1,
                    "comparison_rank": 1,
                    "injective": False,
                    "surjective": True,
                    "isomorphism": False,
                },
                {
                    "coarse_targets_A": [1],
                    "coarse_h1_dimension": 2,
                    "fine_h1_dimension": 2,
                    "comparison_rank": 2,
                    "injective": True,
                    "surjective": True,
                    "isomorphism": True,
                },
                {
                    "coarse_targets_A": [0, 1],
                    "coarse_h1_dimension": 3,
                    "fine_h1_dimension": 3,
                    "comparison_rank": 3,
                    "injective": True,
                    "surjective": True,
                    "isomorphism": True,
                },
            ],
            "SINGULAR-PERFECT-MATCH-3": [
                {
                    "coarse_targets_A": [0],
                    "coarse_h1_dimension": 2,
                    "fine_h1_dimension": 1,
                    "comparison_rank": 1,
                    "injective": False,
                    "surjective": True,
                    "isomorphism": False,
                },
                {
                    "coarse_targets_A": [1],
                    "coarse_h1_dimension": 1,
                    "fine_h1_dimension": 1,
                    "comparison_rank": 1,
                    "injective": True,
                    "surjective": True,
                    "isomorphism": True,
                },
                {
                    "coarse_targets_A": [0, 1],
                    "coarse_h1_dimension": 2,
                    "fine_h1_dimension": 2,
                    "comparison_rank": 2,
                    "injective": True,
                    "surjective": True,
                    "isomorphism": True,
                },
            ],
            "WEIGHTED-ORPHAN-SELFLOOP": [
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
                    "fine_h1_dimension": 1,
                    "comparison_rank": 0,
                    "injective": True,
                    "surjective": False,
                    "isomorphism": False,
                },
                {
                    "coarse_targets_A": [0, 1],
                    "coarse_h1_dimension": 1,
                    "fine_h1_dimension": 2,
                    "comparison_rank": 1,
                    "injective": True,
                    "surjective": False,
                    "isomorphism": False,
                },
            ],
        }
        expected_candidate_literal = {
            "NONFREE-MUTUAL-KILL-SPLIT": {
                "aggregate": {
                    "C0*": True,
                    "C1*": True,
                    "C2*": True,
                    "C3*": True,
                    "C4*": True,
                    "C5*": True,
                    "C6*": True,
                },
                "vector_C0_through_C6": [
                    True,
                    True,
                    True,
                    True,
                    True,
                    True,
                    True,
                ],
                "candidate_all": True,
                "whole": {
                    "terminal_count": 1,
                    "trace_kinds": ["coordinate-dependency"],
                },
                "per_nonempty_A": [
                    {
                        "coarse_targets_A": [0],
                        "terminal_count": 1,
                        "trace_kinds": ["coordinate-dependency"],
                        "conditions": {
                            "C1*": True,
                            "C2*": True,
                            "C3*": True,
                            "C4*": True,
                        },
                    },
                    {
                        "coarse_targets_A": [1],
                        "terminal_count": 1,
                        "trace_kinds": ["coordinate-dependency"],
                        "conditions": {
                            "C1*": True,
                            "C2*": True,
                            "C3*": True,
                            "C4*": True,
                        },
                    },
                    {
                        "coarse_targets_A": [0, 1],
                        "terminal_count": 1,
                        "trace_kinds": ["coordinate-dependency"],
                        "conditions": {
                            "C1*": True,
                            "C2*": True,
                            "C3*": True,
                            "C4*": True,
                        },
                    },
                ],
                "retained_original_cells": {
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
                },
                "expectation_is_not_engine_observation": True,
            },
            "WEIGHTED-2": {
                "aggregate": {
                    "C0*": True,
                    "C1*": True,
                    "C2*": True,
                    "C3*": True,
                    "C4*": True,
                    "C5*": True,
                    "C6*": True,
                },
                "vector_C0_through_C6": [
                    True,
                    True,
                    True,
                    True,
                    True,
                    True,
                    True,
                ],
                "candidate_all": True,
                "whole": {
                    "terminal_count": 1,
                    "trace_kinds": ["closed-doubled-cycle"],
                },
                "per_nonempty_A": [
                    {
                        "coarse_targets_A": [0],
                        "terminal_count": 1,
                        "trace_kinds": ["closed-doubled-cycle"],
                        "conditions": {
                            "C1*": True,
                            "C2*": True,
                            "C3*": True,
                            "C4*": True,
                        },
                    },
                    {
                        "coarse_targets_A": [1],
                        "terminal_count": 1,
                        "trace_kinds": ["closed-doubled-cycle"],
                        "conditions": {
                            "C1*": True,
                            "C2*": True,
                            "C3*": True,
                            "C4*": True,
                        },
                    },
                    {
                        "coarse_targets_A": [0, 1],
                        "terminal_count": 1,
                        "trace_kinds": ["closed-doubled-cycle"],
                        "conditions": {
                            "C1*": True,
                            "C2*": True,
                            "C3*": True,
                            "C4*": True,
                        },
                    },
                ],
                "retained_original_cells": {
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
                },
                "expectation_is_not_engine_observation": True,
            },
            "TERNARY-CYCLE-3": {
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
                "whole": {"terminal_count": 1, "trace_kinds": []},
                "per_nonempty_A": [
                    {
                        "coarse_targets_A": [0],
                        "terminal_count": 1,
                        "trace_kinds": [],
                        "conditions": {
                            "C1*": False,
                            "C2*": False,
                            "C3*": True,
                            "C4*": False,
                        },
                    },
                    {
                        "coarse_targets_A": [1],
                        "terminal_count": 1,
                        "trace_kinds": [],
                        "conditions": {
                            "C1*": True,
                            "C2*": True,
                            "C3*": True,
                            "C4*": True,
                        },
                    },
                    {
                        "coarse_targets_A": [0, 1],
                        "terminal_count": 1,
                        "trace_kinds": [],
                        "conditions": {
                            "C1*": True,
                            "C2*": True,
                            "C3*": True,
                            "C4*": True,
                        },
                    },
                ],
                "retained_original_cells": {
                    "all_scopes": "all support-active cells retained"
                },
                "expectation_is_not_engine_observation": True,
            },
            "TERNARY-CYCLE-6": {
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
                "whole": {"terminal_count": 1, "trace_kinds": []},
                "per_nonempty_A": [
                    {
                        "coarse_targets_A": [0],
                        "terminal_count": 1,
                        "trace_kinds": [],
                        "conditions": {
                            "C1*": False,
                            "C2*": False,
                            "C3*": True,
                            "C4*": False,
                        },
                    },
                    {
                        "coarse_targets_A": [1],
                        "terminal_count": 1,
                        "trace_kinds": [],
                        "conditions": {
                            "C1*": True,
                            "C2*": True,
                            "C3*": True,
                            "C4*": True,
                        },
                    },
                    {
                        "coarse_targets_A": [0, 1],
                        "terminal_count": 1,
                        "trace_kinds": [],
                        "conditions": {
                            "C1*": True,
                            "C2*": True,
                            "C3*": True,
                            "C4*": True,
                        },
                    },
                ],
                "retained_original_cells": {
                    "all_scopes": "all support-active cells retained"
                },
                "expectation_is_not_engine_observation": True,
            },
            "SINGULAR-PERFECT-MATCH-3": {
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
                "whole": {"terminal_count": 1, "trace_kinds": []},
                "per_nonempty_A": [
                    {
                        "coarse_targets_A": [0],
                        "terminal_count": 1,
                        "trace_kinds": [],
                        "conditions": {
                            "C1*": False,
                            "C2*": False,
                            "C3*": True,
                            "C4*": False,
                        },
                    },
                    {
                        "coarse_targets_A": [1],
                        "terminal_count": 1,
                        "trace_kinds": [],
                        "conditions": {
                            "C1*": True,
                            "C2*": True,
                            "C3*": True,
                            "C4*": True,
                        },
                    },
                    {
                        "coarse_targets_A": [0, 1],
                        "terminal_count": 1,
                        "trace_kinds": [],
                        "conditions": {
                            "C1*": True,
                            "C2*": True,
                            "C3*": True,
                            "C4*": True,
                        },
                    },
                ],
                "retained_original_cells": {
                    "all_scopes": "all support-active cells retained"
                },
                "expectation_is_not_engine_observation": True,
            },
            "WEIGHTED-ORPHAN-SELFLOOP": {
                "aggregate": {
                    "C0*": False,
                    "C1*": True,
                    "C2*": True,
                    "C3*": True,
                    "C4*": True,
                    "C5*": False,
                    "C6*": True,
                },
                "vector_C0_through_C6": [
                    False,
                    True,
                    True,
                    True,
                    True,
                    False,
                    True,
                ],
                "candidate_all": False,
                "whole": {"terminal_count": 1, "trace_kinds": []},
                "per_nonempty_A": [
                    {
                        "coarse_targets_A": [0],
                        "terminal_count": 1,
                        "trace_kinds": ["closed-doubled-cycle"],
                        "conditions": {
                            "C1*": True,
                            "C2*": True,
                            "C3*": True,
                            "C4*": True,
                        },
                    },
                    {
                        "coarse_targets_A": [1],
                        "terminal_count": 1,
                        "trace_kinds": [],
                        "conditions": {
                            "C1*": True,
                            "C2*": True,
                            "C3*": True,
                            "C4*": True,
                        },
                    },
                    {
                        "coarse_targets_A": [0, 1],
                        "terminal_count": 1,
                        "trace_kinds": [],
                        "conditions": {
                            "C1*": True,
                            "C2*": True,
                            "C3*": True,
                            "C4*": True,
                        },
                    },
                ],
                "retained_original_cells": {
                    "A0": {
                        "coarse_edges": [0],
                        "fine_edges": [0],
                        "coarse_faces": [],
                        "fine_faces": [],
                    },
                    "A1_A01_whole": "all support-active cells retained",
                },
                "expectation_is_not_engine_observation": True,
            },
        }
        self.assertEqual(
            {
                name: row["hand_expected_H1_blocks"]
                for name, row in fixture_rows.items()
            },
            expected_h1_literal,
        )
        self.assertEqual(
            {
                name: row["hand_expected_v5_candidate"]
                for name, row in fixture_rows.items()
            },
            expected_candidate_literal,
        )

    def test_v5_old_only_calibration_groups_exclude_new_controls(self) -> None:
        groups = v5_immutable_calibration_fixture_groups()
        self.assertEqual(set(groups), {"required16", "immutable_prior2161"})
        self.assertEqual(len(groups["required16"]), 16)
        self.assertEqual(len(groups["immutable_prior2161"]), 2161)
        new_control_ids = {
            _case_semantic_sha256(fixture)
            for fixture in round15_verification_fixtures()[1:]
        }
        overlap_by_group = {
            group_name: [
                _case_semantic_sha256(fixture)
                for fixture in groups[group_name]
                if _case_semantic_sha256(fixture) in new_control_ids
            ]
            for group_name in ("required16", "immutable_prior2161")
        }
        self.assertEqual(
            overlap_by_group,
            {"required16": [], "immutable_prior2161": []},
        )


class R2V5Round15AdmissionAndReportTest(unittest.TestCase):
    def test_round15_registered_literals_and_immutable_manifest(self) -> None:
        self.assertEqual(ROUND15_PREREGISTERED_ISSUE_COMMENT, 5235347217)
        self.assertEqual(
            ROUND15_PREREGISTERED_CREATED_AT,
            "2026-08-10T02:51:13Z",
        )
        self.assertEqual(
            ROUND15_PREREGISTERED_UPDATED_AT,
            "2026-08-10T02:51:13Z",
        )
        self.assertEqual(
            ROUND15_REGISTERED_MANIFEST_SHA256,
            "e5f2d6630ee2f37de409f5e2c0757eed17b24509ca3cd3f7d924c130b6219c3b",
        )
        self.assertEqual(
            ROUND15_REGISTERED_V5_CALIBRATION_SHA256,
            "a9b23c5d3689868185b5c3fb1f4ab29a6e0f6529f45ed97be77f89be99d2a776",
        )
        self.assertEqual(ROUND15_REGISTERED_V5_CALIBRATION_BYTES, 873)
        manifest = round15_preregistration_manifest()
        self.assertEqual(
            round15_preregistration_manifest_sha256(),
            ROUND15_REGISTERED_MANIFEST_SHA256,
        )
        self.assertEqual(
            json.loads(round15_preregistration_manifest_canonical_json()),
            manifest,
        )
        self.assertIsNone(manifest["preregistered_issue_comment"])
        self.assertFalse(manifest["admission_gate_added"])
        self.assertFalse(manifest["round15_query_added"])
        self.assertFalse(manifest["round15_report_added"])

    def test_round15_manifest_drift_calls_no_later_gate_or_query(self) -> None:
        drifted = json.loads(json.dumps(round15_preregistration_manifest()))
        drifted["pure_population_gate"]["union_unique_name_free_ids"] = 2167
        with (
            patch.object(
                r2_hunt,
                "round15_preregistration_manifest",
                return_value=drifted,
            ),
            patch.object(
                r2_hunt,
                "_round15_round14_baseline_admission",
            ) as round14_gate,
            patch.object(
                r2_hunt,
                "_round15_v5_calibration_admission",
            ) as calibration_gate,
            patch.object(
                r2_hunt,
                "_round15_population_identity_admission",
            ) as identity_gate,
            patch.object(r2_hunt, "_round15_engine_query") as query,
        ):
            with self.assertRaises(AssertionError):
                round15_report()
        round14_gate.assert_not_called()
        calibration_gate.assert_not_called()
        identity_gate.assert_not_called()
        query.assert_not_called()

    def test_round15_round14_drift_calls_no_calibration_identity_or_query(
        self,
    ) -> None:
        manifest = round15_preregistration_manifest()
        with (
            patch.object(
                r2_hunt,
                "_round15_manifest_admission",
                return_value={"manifest": manifest},
            ),
            patch.object(
                r2_hunt,
                "_round15_round14_baseline_admission",
                side_effect=AssertionError("one-bit Round14 payload drift"),
            ),
            patch.object(
                r2_hunt,
                "_round15_v5_calibration_admission",
            ) as calibration_gate,
            patch.object(
                r2_hunt,
                "_round15_population_identity_admission",
            ) as identity_gate,
            patch.object(r2_hunt, "_round15_engine_query") as query,
        ):
            with self.assertRaises(AssertionError):
                round15_report()
        calibration_gate.assert_not_called()
        identity_gate.assert_not_called()
        query.assert_not_called()

    def test_round15_calibration_drift_calls_no_identity_or_query(self) -> None:
        manifest = round15_preregistration_manifest()
        with (
            patch.object(
                r2_hunt,
                "_round15_manifest_admission",
                return_value={"manifest": manifest},
            ),
            patch.object(
                r2_hunt,
                "_round15_round14_baseline_admission",
                return_value={"all_gates_pass": True},
            ),
            patch.object(
                r2_hunt,
                "_round15_v5_calibration_admission",
                side_effect=AssertionError("one-bit v5 calibration drift"),
            ),
            patch.object(
                r2_hunt,
                "_round15_population_identity_admission",
            ) as identity_gate,
            patch.object(r2_hunt, "_round15_engine_query") as query,
        ):
            with self.assertRaises(AssertionError):
                round15_report()
        identity_gate.assert_not_called()
        query.assert_not_called()

    def test_round15_population_drift_calls_no_query(self) -> None:
        manifest = round15_preregistration_manifest()
        with (
            patch.object(
                r2_hunt,
                "_round15_manifest_admission",
                return_value={"manifest": manifest},
            ),
            patch.object(
                r2_hunt,
                "_round15_round14_baseline_admission",
                return_value={"all_gates_pass": True},
            ),
            patch.object(
                r2_hunt,
                "_round15_v5_calibration_admission",
                return_value={"all_gates_pass": True},
            ),
            patch.object(
                r2_hunt,
                "_round15_population_identity_admission",
                side_effect=AssertionError("Round15 union identity drift"),
            ),
            patch.object(r2_hunt, "_round15_engine_query") as query,
        ):
            with self.assertRaises(AssertionError):
                round15_report()
        query.assert_not_called()

    def test_round15_engine_mismatch_is_not_a_valid_result(self) -> None:
        manifest = round15_preregistration_manifest()
        mutual_h1 = manifest["fixtures"][0]["hand_expected_H1_blocks"]
        admission = {
            "manifest": {"manifest": manifest},
            "round14_baseline": {"mutual_H1_blocks": mutual_h1},
            "all_gates_pass": True,
        }
        with (
            patch.object(
                r2_hunt,
                "_round15_admission_gate",
                return_value=admission,
            ),
            patch.object(
                r2_hunt,
                "_round15_engine_query",
                side_effect=AssertionError(
                    "engine did not reproduce registered control"
                ),
            ) as query,
        ):
            with self.assertRaises(AssertionError):
                round15_report()
        query.assert_called_once_with(manifest, mutual_h1)

    def test_round15_exact_admitted_report_and_registered_controls(self) -> None:
        report = round15_report()
        self.assertEqual(
            set(report),
            {
                "round",
                "valid",
                "preregistration",
                "admission",
                "candidate",
                "population",
                "queries",
                "exact_verification",
                "progress_audit",
                "stop_audit",
                "coverage_limit",
            },
        )
        self.assertEqual(report["round"], "R2-round-15")
        self.assertTrue(report["valid"])
        preregistration = report["preregistration"]
        self.assertEqual(
            preregistration,
            {
                "issue_comment": ROUND15_PREREGISTERED_ISSUE_COMMENT,
                "created_at": ROUND15_PREREGISTERED_CREATED_AT,
                "updated_at": ROUND15_PREREGISTERED_UPDATED_AT,
                "manifest_sha256": ROUND15_REGISTERED_MANIFEST_SHA256,
                "verification_mode": "registered-semantic-safety-controls",
                "blind_search": False,
            },
        )

        admission = report["admission"]
        self.assertTrue(admission["all_gates_pass"])
        self.assertEqual(
            admission["gate_order"],
            [
                "immutable_pure_preregistration_manifest_and_comment",
                "immutable_round14_full_result",
                "exact_v5_old_only_calibration_with_no_new_control_evaluation",
                "prior2161_overlap_MUTUAL_plus_new5_identity_and_collision",
            ],
        )
        self.assertEqual(
            admission["manifest"]["manifest_sha256"],
            ROUND15_REGISTERED_MANIFEST_SHA256,
        )
        round14 = admission["round14_baseline"]
        self.assertEqual(
            round14["payload_sha256"],
            ROUND15_PARENT_ROUND14_PAYLOAD_SHA256,
        )
        self.assertEqual(
            round14["canonical_bytes"],
            ROUND15_PARENT_ROUND14_CANONICAL_BYTES,
        )
        self.assertEqual(
            round14["result_issue_comment"],
            ROUND15_PARENT_ROUND14_RESULT_ISSUE_COMMENT,
        )
        self.assertTrue(round14["progress"])
        self.assertEqual(round14["streak_after_round"], 0)

        calibration = admission["v5_calibration"]
        self.assertEqual(
            calibration["canonical_sha256"],
            ROUND15_REGISTERED_V5_CALIBRATION_SHA256,
        )
        self.assertEqual(
            calibration["canonical_bytes"],
            ROUND15_REGISTERED_V5_CALIBRATION_BYTES,
        )
        self.assertEqual(calibration["required_catalog_count"], 16)
        self.assertEqual(calibration["immutable_prior_count"], 2161)
        self.assertEqual(
            calibration["new_round15_control_evaluations_by_group"],
            {"required16": 0, "immutable_prior2161": 0},
        )
        self.assertEqual(calibration["new_round15_control_evaluations"], 0)
        self.assertEqual(calibration["new_round15_control_H1_queries"], 0)

        population = report["population"]
        self.assertEqual(population["prior_cases"], 2161)
        self.assertEqual(population["verification_fixture_count"], 6)
        self.assertEqual(population["overlap_cases"], 1)
        self.assertEqual(
            population["overlap_names"],
            ["NONFREE-MUTUAL-KILL-SPLIT"],
        )
        self.assertEqual(population["new_cases"], 5)
        self.assertEqual(population["total_cases"], 2166)
        self.assertEqual(population["unique_full_name_free_ids"], 2166)
        self.assertEqual(population["unique_truncated_20hex_ids"], 2166)
        self.assertEqual(population["full_sha256_collision_count"], 0)
        self.assertEqual(population["truncated_20hex_collision_count"], 0)
        self.assertTrue(population["new_disjoint_from_prior"])
        self.assertEqual(population["candidate_fixture_evaluations"], 6)
        self.assertEqual(population["new5_A_block_queries"], 15)
        self.assertEqual(population["parent_MUTUAL_A_block_queries"], 0)
        self.assertTrue(
            population["all_registered_candidate_terminal_details_evaluated"]
        )
        self.assertTrue(population["all_new5_nonempty_A_evaluated"])
        self.assertFalse(population["sampling"])
        self.assertFalse(population["early_stop"])

        fixtures = report["exact_verification"]["fixtures"]
        self.assertEqual(
            [fixture["name"] for fixture in fixtures],
            [
                "NONFREE-MUTUAL-KILL-SPLIT",
                "WEIGHTED-2",
                "TERNARY-CYCLE-3",
                "TERNARY-CYCLE-6",
                "SINGULAR-PERFECT-MATCH-3",
                "WEIGHTED-ORPHAN-SELFLOOP",
            ],
        )
        outcomes = {
            fixture["name"]: (
                fixture["uniform"],
                fixture["v5_candidate"]["candidate_all"],
                fixture["direction"],
            )
            for fixture in fixtures
        }
        self.assertEqual(
            outcomes,
            {
                "NONFREE-MUTUAL-KILL-SPLIT": (True, True, None),
                "WEIGHTED-2": (True, True, None),
                "TERNARY-CYCLE-3": (
                    True,
                    False,
                    "uniform_and_not_candidate",
                ),
                "TERNARY-CYCLE-6": (False, False, None),
                "SINGULAR-PERFECT-MATCH-3": (False, False, None),
                "WEIGHTED-ORPHAN-SELFLOOP": (False, False, None),
            },
        )
        self.assertEqual(
            fixtures[0]["H1_source"],
            "immutable-Round14-parent-result",
        )
        self.assertTrue(
            all(
                fixture["H1_source"] == "Round15-new5-exact-query"
                for fixture in fixtures[1:]
            )
        )
        self.assertTrue(
            report["exact_verification"][
                "engine_reproduced_all_registered_expectations"
            ]
        )
        self.assertTrue(
            report["exact_verification"]["H1_queried_only_for_new5"]
        )

        queries = report["queries"]
        self.assertEqual(queries["prior_uniform_and_not_candidate_count"], 0)
        self.assertEqual(queries["prior_candidate_and_nonuniform_count"], 0)
        self.assertEqual(queries["new_uniform_and_not_candidate_count"], 1)
        self.assertEqual(queries["new_candidate_and_nonuniform_count"], 0)
        self.assertEqual(queries["uniform_and_not_candidate_count"], 1)
        self.assertEqual(queries["candidate_and_nonuniform_count"], 0)
        self.assertEqual(queries["candidate_and_nonuniform"], [])
        self.assertEqual(queries["new_counterexample_count"], 1)
        self.assertEqual(len(queries["uniform_and_not_candidate"]), 1)
        witness = queries["uniform_and_not_candidate"][0]
        self.assertEqual(witness["name"], "TERNARY-CYCLE-3")
        self.assertEqual(witness["direction"], "uniform_and_not_candidate")
        self.assertEqual(witness["minimal_failing_A"], [0])
        self.assertEqual(
            witness["exact_h1"],
            {
                "coarse_targets_A": [0],
                "coarse_h1_dimension": 1,
                "fine_h1_dimension": 1,
                "comparison_rank": 1,
                "injective": True,
                "surjective": True,
                "isomorphism": True,
            },
        )
        t3 = next(
            fixture for fixture in fixtures if fixture["name"] == "TERNARY-CYCLE-3"
        )
        self.assertEqual(
            witness["canonical_nonisomorphic_id"],
            t3["canonical_orbit_sha256"],
        )

        candidate = report["candidate"]
        self.assertEqual(candidate["semantic_id"], V5_SEMANTIC_ID)
        self.assertEqual(candidate["semantic_sha256"], V5_SEMANTIC_SHA256)
        self.assertEqual(candidate["predecessor_semantic_id"], V4_SEMANTIC_ID)
        self.assertTrue(candidate["semantic_change"])
        self.assertEqual(candidate["verdict"], "CSTAR-not-necessary")
        self.assertFalse(candidate["verdict_is_new_this_round"])
        self.assertEqual(candidate["status"], "invalid")
        self.assertEqual(candidate["invalidated_semantic_id"], V5_SEMANTIC_ID)
        self.assertFalse(candidate["valid_after_round15"])
        self.assertTrue(candidate["invalidated_by_registered_TERNARY_CYCLE_3"])

        progress = report["progress_audit"]
        self.assertEqual(progress["entry_streak"], 0)
        self.assertEqual(progress["new_verdicts"], [])
        self.assertEqual(
            progress["new_canonical_nonisomorphic_counterexamples"],
            [t3["canonical_orbit_sha256"]],
        )
        self.assertTrue(progress["candidate_semantic_change"])
        self.assertEqual(progress["additional_calibration_fixes"], [])
        self.assertTrue(progress["progress"])
        self.assertEqual(progress["streak_after_round"], 0)
        stop = report["stop_audit"]
        self.assertFalse(stop["stop_condition_A_completion"])
        self.assertFalse(stop["stop_condition_B_finite_exhaustion"])
        self.assertFalse(
            stop["stop_condition_C_two_valid_same_blocker_no_progress"]
        )
        self.assertTrue(stop["registered_counterexample_is_progress"])


if __name__ == "__main__":
    unittest.main()
