#!/usr/bin/env python3
"""Regression tests for the preregistered R2 checkpoint rounds."""

import unittest

from necessity_map import H1Analysis
from r2_hunt import (
    CANDIDATE_SEMANTIC_SHA256,
    ChartCodeSpec,
    CERTIFIED_SEMANTIC_SHA256,
    COMPONENT_SEMANTIC_SHA256,
    FINAL_R0_SEMANTIC_SHA256,
    FINAL_R1_SEMANTIC_SHA256,
    REGISTERED_ROUND_PAYLOAD_SHA256,
    R10_A_KILL_RELATIONS,
    R10_A_SLOT_RELATIONS,
    R10_B_K4_KILL_RELATIONS,
    R10_B_K4_SLOT_RELATIONS,
    R10_B_STAR_KILL_RELATIONS,
    R10_B_STAR_SLOT_RELATIONS,
    ROUND8_DIAGNOSTIC_PAYLOAD_SHA256,
    ROUND9_VALID_PAYLOAD_SHA256,
    RelationBlockCodeSpec,
    _assert_registered_round_payload_hashes,
    _assert_round10_hash_baseline,
    _assert_round9_hash_baseline,
    _case_id,
    _case_semantic_sha256,
    candidate_evaluation,
    chain3_fixture,
    colored_graph_support_canonical_code,
    relation_graph_canonical_code,
    relation_graph_support_code,
    round1_report,
    round2_report,
    round3_report,
    round4_report,
    round5_report,
    round6_report,
    round7_report,
    round8_relation_fixtures,
    round8_report,
    round9_relation_fixtures,
    round9_report,
    round10_relation_fixtures,
    round10_report,
    unkilled_twin_fixture,
)


class R2HuntTest(unittest.TestCase):
    def test_registered_semantic_hashes(self) -> None:
        self.assertEqual(
            CANDIDATE_SEMANTIC_SHA256,
            "5e883518c3f82052d1921752118adf8307a259282eb359abdc069dc2b4a82756",
        )
        self.assertEqual(
            COMPONENT_SEMANTIC_SHA256,
            "b16b934268aded0fd256141f1c516f3f28ee45bf8c0d40bad4dbfe8819ce6e80",
        )
        self.assertEqual(
            CERTIFIED_SEMANTIC_SHA256,
            "cbb02677a055c69ecf0bb50a5de884fb55bbd4b4b59b75d256815eae69ec4daa",
        )

    def test_exact_progress_fixtures(self) -> None:
        self.assertEqual(
            chain3_fixture().block_analyses()[0][1],
            H1Analysis(1, 1, 1, True, True, True),
        )
        self.assertEqual(
            unkilled_twin_fixture().block_analyses()[0][1],
            H1Analysis(1, 2, 1, True, False, False),
        )

    def test_case_id_is_name_invariant(self) -> None:
        fixture = chain3_fixture()
        renamed = type(fixture)(
            name="renamed-only",
            morphism=fixture.morphism,
            coarse_target_count=fixture.coarse_target_count,
            fine_target_count=fixture.fine_target_count,
            factor_pi=fixture.factor_pi,
            coarse_chart_supports=fixture.coarse_chart_supports,
            fine_chart_supports=fixture.fine_chart_supports,
        )
        self.assertEqual(_case_id(fixture), _case_id(renamed))

    def test_round1_direct_clique_necessity_break(self) -> None:
        report = round1_report()
        self.assertEqual(report["population"]["total"], 604)
        self.assertEqual(report["queries"]["sufficiency_break_count"], 0)
        self.assertEqual(report["queries"]["necessity_break_count"], 1)
        self.assertFalse(
            report["registered_chain3"]["candidate"]["aggregate"]["C5*"]
        )

    def test_round2_component_sufficiency_break(self) -> None:
        report = round2_report()
        self.assertEqual(report["population"]["total"], 605)
        self.assertEqual(report["queries"]["sufficiency_break_count"], 1)
        self.assertEqual(report["queries"]["necessity_break_count"], 0)
        self.assertTrue(report["registered_unkilled_twin"]["candidate"]["all"])

    def test_round3_certified_zero_result(self) -> None:
        report = round3_report()
        self.assertEqual(report["queries"]["sufficiency_break_count"], 0)
        self.assertEqual(report["queries"]["necessity_break_count"], 0)
        self.assertTrue(report["registered_chain3"]["candidate"]["all"])
        self.assertFalse(
            report["registered_unkilled_twin"]["candidate"]["aggregate"]["C5*"]
        )

    def test_round4_first_no_progress_strict_expansion(self) -> None:
        report = round4_report()
        self.assertTrue(report["population"]["strict_superset"])
        self.assertEqual(report["population"]["new_incidence_cases"], 3)
        self.assertEqual(report["queries"]["new_counterexample_count"], 0)
        self.assertEqual(report["progress_audit"]["new_verdicts"], [])

    def test_round5_support_expansion_is_not_terminal_evidence(self) -> None:
        report = round5_report()
        self.assertTrue(report["population"]["strict_superset"])
        self.assertEqual(report["population"]["new_fixed_label_ids"], 1296)
        self.assertEqual(report["population"]["new_A_block_queries"], 19440)
        self.assertEqual(report["queries"]["new_counterexample_count"], 0)
        self.assertEqual(
            report["blocker_id"],
            "PB-R2-NONFREE-GLOBAL-FACE-CHAIN",
        )

    def test_round6_first_valid_same_blocker_no_progress(self) -> None:
        report = round6_report()
        self.assertTrue(report["population"]["strict_superset"])
        self.assertEqual(report["population"]["new_nonidentity_face_chains"], 2)
        self.assertEqual(report["queries"]["new_counterexample_count"], 0)
        self.assertEqual(report["same_blocker_evidence"]["free_pair_count"], 0)

    def test_round7_second_valid_same_blocker_no_progress(self) -> None:
        report = round7_report()
        self.assertTrue(report["population"]["strict_superset"])
        self.assertEqual(
            report["population"]["new_nonidentity_face_chain_graphs"],
            2,
        )
        self.assertEqual(report["queries"]["new_counterexample_count"], 0)
        self.assertEqual(
            report["same_blocker_evidence"]["relation_graphs"],
            ["branching-tree", "cycle"],
        )

    def test_round8_exact_kill_and_slot_fixtures(self) -> None:
        kill, slot = round8_relation_fixtures()
        self.assertEqual(
            (
                kill.morphism.coarse.vertices,
                len(kill.morphism.coarse.edges),
                len(kill.morphism.coarse.faces),
                kill.morphism.fine.vertices,
                len(kill.morphism.fine.edges),
                len(kill.morphism.fine.faces),
            ),
            (1, 6, 10, 1, 11, 10),
        )
        self.assertEqual(
            (
                slot.morphism.coarse.vertices,
                len(slot.morphism.coarse.edges),
                len(slot.morphism.coarse.faces),
                slot.morphism.fine.vertices,
                len(slot.morphism.fine.edges),
                len(slot.morphism.fine.faces),
            ),
            (1, 19, 9, 1, 24, 18),
        )
        self.assertEqual(kill.morphism.edge_map, (0,) * 6 + tuple(range(1, 6)))
        self.assertEqual(slot.morphism.edge_map, (0,) * 6 + tuple(range(1, 19)))
        self.assertEqual(kill.morphism.face_map, tuple(range(10)))
        self.assertEqual(
            slot.morphism.face_map,
            tuple(index for index in range(9) for _ in range(2)),
        )
        expected = (
            H1Analysis(1, 1, 1, True, True, True),
            H1Analysis(10, 10, 10, True, True, True),
        )
        for fixture, analysis in zip((kill, slot), expected):
            self.assertEqual(len(fixture.block_analyses()), 15)
            self.assertTrue(
                all(item == analysis for _, item in fixture.block_analyses())
            )
            candidate = candidate_evaluation(fixture, c5_mode="certified")
            self.assertTrue(candidate["all"])
            self.assertEqual(
                candidate["whole"]["coarse_reduction"]["removed_free_pairs"],
                [],
            )
            self.assertEqual(
                candidate["whole"]["fine_reduction"]["removed_free_pairs"],
                [],
            )

    def test_round8_colored_graph_code_is_name_free_and_strict(self) -> None:
        path = relation_graph_canonical_code(
            6,
            kill_relations=((0, 1), (1, 2), (2, 3), (3, 4), (4, 5)),
        )
        relabeled_path = relation_graph_canonical_code(
            6,
            kill_relations=((5, 3), (3, 1), (1, 4), (4, 0), (0, 2)),
        )
        ladder = relation_graph_canonical_code(
            6,
            slot_relations=(
                (0, 1), (1, 2), (2, 0),
                (3, 4), (4, 5), (5, 3),
                (0, 3), (1, 4), (2, 5),
            ),
        )
        self.assertEqual(path, relabeled_path)
        self.assertNotEqual(path, ladder)
        for fixture in round8_relation_fixtures():
            self.assertEqual(len(_case_semantic_sha256(fixture)), 64)
            self.assertEqual(
                _case_id(fixture),
                _case_semantic_sha256(fixture)[:20],
            )

    def test_round8_strict_expansion_and_dynamic_progress(self) -> None:
        report = round8_report()
        population = report["population"]
        self.assertFalse(report["valid"])
        self.assertEqual(
            report["invalid_reason"],
            "Round8 query ran before final R0(e) Issue synchronization and "
            "coordinator release",
        )
        self.assertEqual(population["prior_raw_cases_recomputed"], 1908)
        self.assertEqual(population["prior_full_semantic_payload_ids"], 1908)
        self.assertEqual(population["prior_truncated_semantic_payload_ids"], 1908)
        self.assertEqual(population["total_raw_cases"], 1910)
        self.assertEqual(population["new_A_block_queries"], 30)
        self.assertEqual(population["full_sha256_collision_count"], 0)
        self.assertEqual(population["truncated_20hex_collision_count"], 0)
        self.assertEqual(
            tuple(report["baseline_payload_sha256"].values()),
            REGISTERED_ROUND_PAYLOAD_SHA256,
        )
        self.assertEqual(
            len(set(report["canonical_colored_relation_graph_codes"].values())),
            6,
        )
        self.assertEqual(
            report["relation_graph_invariants"]["R8-L6-KILL"],
            {
                "n": 6,
                "m": 5,
                "degrees": [1, 1, 2, 2, 2, 2],
                "beta1": 0,
                "colors": "K^5",
            },
        )
        self.assertEqual(
            report["relation_graph_invariants"]["R8-CL3-SLOT"],
            {
                "n": 6,
                "m": 9,
                "degrees": [3, 3, 3, 3, 3, 3],
                "beta1": 4,
                "colors": "S^9",
            },
        )
        progress = report["progress_audit"]["progress"]
        self.assertEqual(report["diagnostic_zero_result"], not progress)
        self.assertEqual(report["progress_audit"]["streak_after_round"], 0)
        self.assertFalse(
            report["same_blocker_evidence"]["valid_no_progress_1_of_2"]
        )

    def test_round8_registered_payload_hash_gate_fails_closed(self) -> None:
        _assert_registered_round_payload_hashes(
            REGISTERED_ROUND_PAYLOAD_SHA256
        )
        drifted = list(REGISTERED_ROUND_PAYLOAD_SHA256)
        drifted[0] = "0" * 64
        with self.assertRaises(AssertionError):
            _assert_registered_round_payload_hashes(tuple(drifted))

    def test_round9_hash_baseline_fails_closed_without_query(self) -> None:
        round8_stub = {
            "valid": False,
            "progress_audit": {"streak_after_round": 0},
            "baseline_payload_sha256": {
                f"round{index}": payload_hash
                for index, payload_hash in enumerate(
                    REGISTERED_ROUND_PAYLOAD_SHA256,
                    start=1,
                )
            },
            "candidate": {
                "semantic_id": "R2-CSTAR-CERTIFIED-v3",
                "semantic_sha256": CERTIFIED_SEMANTIC_SHA256,
            },
            "population": {
                "total_raw_cases": 1910,
                "prior_full_semantic_payload_ids": 1908,
                "prior_truncated_semantic_payload_ids": 1908,
                "new_full_semantic_payload_ids": ["a", "b"],
                "new_truncated_semantic_payload_ids": ["a", "b"],
                "full_sha256_collision_count": 0,
                "truncated_20hex_collision_count": 0,
            },
        }
        _assert_round9_hash_baseline(
            r0_sha256=FINAL_R0_SEMANTIC_SHA256,
            r1_sha256=FINAL_R1_SEMANTIC_SHA256,
            round8_sha256=ROUND8_DIAGNOSTIC_PAYLOAD_SHA256,
            round8=round8_stub,
        )
        with self.assertRaises(AssertionError):
            _assert_round9_hash_baseline(
                r0_sha256="0" * 64,
                r1_sha256=FINAL_R1_SEMANTIC_SHA256,
                round8_sha256=ROUND8_DIAGNOSTIC_PAYLOAD_SHA256,
                round8=round8_stub,
            )

    def test_round9_exact_diamond_and_figure8_fixtures(self) -> None:
        diamond, figure8 = round9_relation_fixtures()
        self.assertEqual(
            (
                diamond.morphism.coarse.vertices,
                len(diamond.morphism.coarse.edges),
                len(diamond.morphism.coarse.faces),
                diamond.morphism.fine.vertices,
                len(diamond.morphism.fine.edges),
                len(diamond.morphism.fine.faces),
            ),
            (1, 8, 8, 1, 11, 10),
        )
        self.assertEqual(
            diamond.morphism.coarse.faces,
            (
                (1, 1, 1), (0, 0, 1),
                (2, 2, 2), (0, 0, 2),
                (3, 3, 3), (0, 0, 3),
                (0, 4, 5), (0, 6, 7),
            ),
        )
        self.assertEqual(
            diamond.morphism.fine.faces,
            (
                (4, 4, 4), (0, 1, 4),
                (5, 5, 5), (1, 2, 5),
                (6, 6, 6), (2, 0, 6),
                (1, 7, 8), (3, 7, 8),
                (3, 9, 10), (2, 9, 10),
            ),
        )
        self.assertEqual(
            diamond.morphism.edge_map,
            (0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7),
        )
        self.assertEqual(
            diamond.morphism.face_map,
            (0, 1, 2, 3, 4, 5, 6, 6, 7, 7),
        )
        self.assertEqual(
            (
                figure8.morphism.coarse.vertices,
                len(figure8.morphism.coarse.edges),
                len(figure8.morphism.coarse.faces),
                figure8.morphism.fine.vertices,
                len(figure8.morphism.fine.edges),
                len(figure8.morphism.fine.faces),
            ),
            (2, 8, 12, 2, 12, 12),
        )
        self.assertEqual(figure8.morphism.vertex_map, (0, 1))
        self.assertEqual(
            figure8.morphism.edge_map,
            (0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7),
        )
        self.assertEqual(figure8.morphism.face_map, tuple(range(12)))
        self.assertEqual(
            figure8.coarse_chart_supports,
            (frozenset((0, 1)), frozenset((2, 3))),
        )
        self.assertEqual(
            figure8.fine_chart_supports,
            (frozenset((0, 1, 2)), frozenset((3, 4))),
        )
        self.assertNotEqual(
            relation_graph_support_code(
                diamond,
                4,
                kill_relations=((0, 1), (1, 2), (2, 0)),
                slot_relations=((1, 3), (3, 2)),
            ),
            relation_graph_support_code(
                figure8,
                5,
                kill_relations=(
                    (0, 1), (1, 2), (2, 0),
                    (0, 3), (3, 4), (4, 0),
                ),
            ),
        )

    def test_round9_strict_expansion_and_dynamic_progress(self) -> None:
        report = round9_report()
        population = report["population"]
        self.assertTrue(report["valid"])
        self.assertEqual(report["final_R0_calibration_comment"], 5230818358)
        self.assertEqual(report["baseline_payload_sha256"]["r0"], FINAL_R0_SEMANTIC_SHA256)
        self.assertEqual(report["baseline_payload_sha256"]["r1"], FINAL_R1_SEMANTIC_SHA256)
        self.assertEqual(
            report["baseline_payload_sha256"]["round8_diagnostic"],
            ROUND8_DIAGNOSTIC_PAYLOAD_SHA256,
        )
        self.assertFalse(report["round8_diagnostic_baseline"]["valid"])
        self.assertFalse(
            report["round8_diagnostic_baseline"]["counted_in_stop_streak"]
        )
        self.assertEqual(population["prior_raw_cases_recomputed"], 1910)
        self.assertEqual(population["prior_full_semantic_payload_ids"], 1910)
        self.assertEqual(population["prior_truncated_semantic_payload_ids"], 1910)
        self.assertEqual(population["total_raw_cases"], 1912)
        self.assertEqual(population["total_full_semantic_payload_ids"], 1912)
        self.assertEqual(population["total_truncated_semantic_payload_ids"], 1912)
        self.assertEqual(population["new_A_block_queries"], 30)
        self.assertEqual(population["full_sha256_collision_count"], 0)
        self.assertEqual(population["truncated_20hex_collision_count"], 0)
        self.assertEqual(
            report["figure8_A_block_distribution"],
            {
                "first_support_only": 3,
                "second_support_only": 3,
                "both_supports": 9,
            },
        )
        self.assertEqual(
            len(
                {
                    item["relation_graph_canonical_code"]
                    for item in report[
                        "canonical_relation_graph_support_codes"
                    ].values()
                }
            ),
            8,
        )
        progress = report["progress_audit"]["progress"]
        self.assertEqual(
            report["progress_audit"]["streak_after_round"],
            0 if progress else 1,
        )
        self.assertEqual(
            report["same_blocker_evidence"]["valid_no_progress_1_of_2"],
            not progress,
        )

    def test_round10_hash_baseline_fails_closed_without_query(self) -> None:
        round9_stub = {
            "valid": True,
            "final_R0_calibration_comment": 5230818358,
            "baseline_payload_sha256": {
                "r0": FINAL_R0_SEMANTIC_SHA256,
                "r1": FINAL_R1_SEMANTIC_SHA256,
                "round1_through_round7": list(
                    REGISTERED_ROUND_PAYLOAD_SHA256
                ),
                "round8_diagnostic": ROUND8_DIAGNOSTIC_PAYLOAD_SHA256,
            },
            "round8_diagnostic_baseline": {
                "valid": False,
                "streak_after_round": 0,
                "counted_in_stop_streak": False,
            },
            "candidate": {
                "semantic_id": "R2-CSTAR-CERTIFIED-v3",
                "semantic_sha256": CERTIFIED_SEMANTIC_SHA256,
            },
            "population": {
                "prior_raw_cases_recomputed": 1910,
                "prior_full_semantic_payload_ids": 1910,
                "prior_truncated_semantic_payload_ids": 1910,
                "new_full_semantic_payload_ids": ["a", "b"],
                "new_truncated_semantic_payload_ids": ["a", "b"],
                "total_raw_cases": 1912,
                "total_full_semantic_payload_ids": 1912,
                "total_truncated_semantic_payload_ids": 1912,
                "full_sha256_collision_count": 0,
                "truncated_20hex_collision_count": 0,
            },
            "queries": {
                "prior_sufficiency_or_necessity_break_count": 0,
                "new_sufficiency_break_count": 0,
                "new_necessity_break_count": 0,
                "new_counterexample_count": 0,
            },
            "progress_audit": {
                "progress": False,
                "streak_after_round": 1,
            },
            "same_blocker_evidence": {
                "valid_no_progress_1_of_2": True,
            },
        }
        _assert_round10_hash_baseline(
            round9_sha256=ROUND9_VALID_PAYLOAD_SHA256,
            round9=round9_stub,
        )
        with self.assertRaises(AssertionError):
            _assert_round10_hash_baseline(
                round9_sha256="0" * 64,
                round9=round9_stub,
            )
        round9_stub["queries"]["new_counterexample_count"] = 1
        with self.assertRaises(AssertionError):
            _assert_round10_hash_baseline(
                round9_sha256=ROUND9_VALID_PAYLOAD_SHA256,
                round9=round9_stub,
            )

    def test_round10_exact_multichart_fixtures(self) -> None:
        k23, k4_star = round10_relation_fixtures()
        self.assertEqual(
            (
                k23.morphism.coarse.vertices,
                len(k23.morphism.coarse.edges),
                len(k23.morphism.coarse.faces),
                k23.morphism.fine.vertices,
                len(k23.morphism.fine.edges),
                len(k23.morphism.fine.faces),
            ),
            (2, 11, 9, 2, 15, 12),
        )
        self.assertEqual(
            k23.morphism.coarse.faces,
            (
                (1, 1, 1), (0, 0, 1),
                (2, 2, 2), (0, 0, 2),
                (3, 3, 3), (0, 0, 3),
                (0, 4, 5), (0, 6, 7), (0, 8, 9),
            ),
        )
        self.assertEqual(
            k23.morphism.fine.faces,
            (
                (5, 5, 5), (0, 2, 5),
                (6, 6, 6), (0, 3, 6),
                (7, 7, 7), (1, 4, 7),
                (0, 8, 9), (4, 8, 9),
                (1, 10, 11), (2, 10, 11),
                (1, 12, 13), (3, 12, 13),
            ),
        )
        self.assertEqual(k23.morphism.vertex_map, (0, 1))
        self.assertEqual(
            k23.morphism.edge_map,
            (0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10),
        )
        self.assertEqual(
            k23.morphism.face_map,
            (0, 1, 2, 3, 4, 5, 6, 6, 7, 7, 8, 8),
        )
        self.assertEqual(
            k23.coarse_chart_supports,
            (frozenset((0, 1, 2)), frozenset((2, 3))),
        )
        self.assertEqual(
            k23.fine_chart_supports,
            (frozenset((0, 1, 2, 3)), frozenset((3, 4))),
        )

        self.assertEqual(
            (
                k4_star.morphism.coarse.vertices,
                len(k4_star.morphism.coarse.edges),
                len(k4_star.morphism.coarse.faces),
                k4_star.morphism.fine.vertices,
                len(k4_star.morphism.fine.edges),
                len(k4_star.morphism.fine.faces),
            ),
            (3, 17, 13, 3, 23, 18),
        )
        self.assertEqual(
            k4_star.morphism.coarse.faces,
            (
                (1, 1, 1), (0, 0, 1),
                (2, 2, 2), (0, 0, 2),
                (3, 3, 3), (0, 0, 3),
                (0, 4, 5), (0, 6, 7), (0, 8, 9),
                (11, 11, 11), (10, 10, 11),
                (10, 12, 13), (10, 14, 15),
            ),
        )
        self.assertEqual(
            k4_star.morphism.fine.faces,
            (
                (4, 4, 4), (0, 1, 4),
                (5, 5, 5), (1, 2, 5),
                (6, 6, 6), (2, 0, 6),
                (0, 7, 8), (3, 7, 8),
                (1, 9, 10), (3, 9, 10),
                (2, 11, 12), (3, 11, 12),
                (17, 17, 17), (13, 14, 17),
                (13, 18, 19), (15, 18, 19),
                (13, 20, 21), (16, 20, 21),
            ),
        )
        self.assertEqual(k4_star.morphism.vertex_map, (0, 1, 2))
        self.assertEqual(
            k4_star.morphism.edge_map,
            (
                0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
                10, 10, 10, 10, 11, 12, 13, 14, 15, 16,
            ),
        )
        self.assertEqual(
            k4_star.morphism.face_map,
            (
                0, 1, 2, 3, 4, 5, 6, 6, 7,
                7, 8, 8, 9, 10, 11, 11, 12, 12,
            ),
        )
        self.assertEqual(
            k4_star.coarse_chart_supports,
            (
                frozenset((0, 1)),
                frozenset((1, 2)),
                frozenset((2, 3)),
            ),
        )
        self.assertEqual(
            k4_star.fine_chart_supports,
            (
                frozenset((0, 1, 2)),
                frozenset((2, 3)),
                frozenset((3, 4)),
            ),
        )
        for fixture in (k23, k4_star):
            self.assertEqual(fixture.factor_pi, (0, 0, 1, 2, 3))
            self.assertEqual(len(fixture.block_analyses()), 15)

    def test_round10_colored_graph_support_code_relabel_and_drift(self) -> None:
        factor_pi = (0, 0, 1, 2, 3)
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
        k23_code = colored_graph_support_canonical_code(
            factor_pi=factor_pi,
            chart_records=k23_charts,
            coarse_cell_counts=(2, 11, 9),
            fine_cell_counts=(2, 15, 12),
        )
        lift_relabel = (4, 2, 0, 3, 1)
        lift_relabelled = colored_graph_support_canonical_code(
            factor_pi=factor_pi,
            chart_records=(
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
            ),
            coarse_cell_counts=(2, 11, 9),
            fine_cell_counts=(2, 15, 12),
        )
        support_drift = colored_graph_support_canonical_code(
            factor_pi=factor_pi,
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
        self.assertEqual(k23_code, lift_relabelled)
        self.assertNotEqual(k23_code, support_drift)

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
        k4_star_code = colored_graph_support_canonical_code(
            factor_pi=factor_pi,
            chart_records=k4_star_charts,
            coarse_cell_counts=(3, 17, 13),
            fine_cell_counts=(3, 23, 18),
        )
        chart_relabelled = colored_graph_support_canonical_code(
            factor_pi=factor_pi,
            chart_records=tuple(reversed(k4_star_charts)),
            coarse_cell_counts=(3, 17, 13),
            fine_cell_counts=(3, 23, 18),
        )
        target_relabelled = colored_graph_support_canonical_code(
            factor_pi=factor_pi,
            chart_records=(
                ChartCodeSpec(
                    frozenset((0, 2)),
                    frozenset((0, 1, 3)),
                    k4_star_charts[0].relation_blocks,
                ),
                ChartCodeSpec(
                    frozenset((1, 2)),
                    frozenset((2, 3)),
                    k4_star_charts[1].relation_blocks,
                ),
                ChartCodeSpec(
                    frozenset((1, 3)),
                    frozenset((2, 4)),
                    identity_loop_count=1,
                ),
            ),
            coarse_cell_counts=(3, 17, 13),
            fine_cell_counts=(3, 23, 18),
        )
        self.assertEqual(k4_star_code, chart_relabelled)
        self.assertEqual(k4_star_code, target_relabelled)

    def test_round10_strict_expansion_and_dynamic_stop_c(self) -> None:
        report = round10_report()
        population = report["population"]
        self.assertTrue(report["valid"])
        self.assertEqual(report["preregistered_issue_comment"], 5230881464)
        self.assertEqual(report["round9_result_comment"], 5230876303)
        self.assertEqual(
            report["baseline_payload_sha256"]["round9_valid"],
            ROUND9_VALID_PAYLOAD_SHA256,
        )
        self.assertFalse(report["round8_diagnostic_baseline"]["valid"])
        self.assertTrue(report["round9_valid_baseline"]["valid"])
        self.assertEqual(
            report["round9_valid_baseline"]["streak_after_round"],
            1,
        )
        self.assertTrue(
            report["round9_valid_baseline"]["valid_no_progress_1_of_2"]
        )
        self.assertEqual(population["prior_raw_cases_recomputed"], 1912)
        self.assertEqual(population["prior_full_semantic_payload_ids"], 1912)
        self.assertEqual(population["prior_truncated_semantic_payload_ids"], 1912)
        self.assertEqual(population["total_raw_cases"], 1914)
        self.assertEqual(population["total_full_semantic_payload_ids"], 1914)
        self.assertEqual(population["total_truncated_semantic_payload_ids"], 1914)
        self.assertEqual(population["new_A_block_queries"], 30)
        self.assertEqual(population["full_sha256_collision_count"], 0)
        self.assertEqual(population["truncated_20hex_collision_count"], 0)
        self.assertEqual(
            report["A_block_dimension_histograms"],
            {
                "R10-A-K23-MIXED-OVERLAP": {"1": 1, "4": 3, "5": 11},
                "R10-B-K4-STAR-CHAIN-SUPPORT": {
                    "1": 1,
                    "4": 3,
                    "5": 1,
                    "7": 2,
                    "8": 8,
                },
            },
        )
        self.assertEqual(len(report["A_block_expected_h1"]), 2)
        self.assertTrue(
            all(
                len(table) == 15
                for table in report["A_block_expected_h1"].values()
            )
        )
        code_audit = report["canonical_code_audit"]
        self.assertEqual(code_audit["registered_code_count"], 10)
        self.assertEqual(code_audit["full_sha256_collision_count"], 0)
        self.assertEqual(code_audit["truncated_20hex_collision_count"], 0)
        self.assertEqual(code_audit["compact_json_collision_count"], 0)
        self.assertTrue(code_audit["lift_relabel_invariant"])
        self.assertTrue(code_audit["chart_relabel_invariant"])
        self.assertTrue(code_audit["target_relabel_invariant"])
        self.assertTrue(code_audit["support_drift_detected"])
        for case in report["expansion_cases"]:
            self.assertTrue(case["uniform"])
            self.assertTrue(case["candidate"]["all"])
            self.assertTrue(all(case["candidate"]["aggregate"].values()))
            self.assertEqual(len(case["all_block_h1"]), 15)
            self.assertEqual(len(case["semantic_sha256"]), 64)
            self.assertEqual(case["id"], case["semantic_sha256"][:20])
            self.assertTrue(case["semantic_payload_json"].startswith("{"))
            self.assertTrue(
                all(
                    adjacency["unintended_edge_count"] == 0
                    for adjacency in case[
                        "certified_colored_adjacency"
                    ].values()
                )
            )
            reductions = (
                case["candidate"]["whole"],
                *case["candidate"]["per_subset"],
            )
            self.assertTrue(
                all(
                    not reduction["coarse_reduction"]["removed_free_pairs"]
                    and not reduction["fine_reduction"]["removed_free_pairs"]
                    for reduction in reductions
                )
            )
        progress = report["progress_audit"]["progress"]
        self.assertEqual(
            report["progress_audit"]["streak_after_round"],
            0 if progress else 2,
        )
        self.assertEqual(
            report["same_blocker_evidence"]["valid_no_progress_2_of_2"],
            not progress,
        )
        self.assertEqual(
            report["stop_audit"][
                "stop_condition_C_two_valid_same_blocker_no_progress"
            ],
            not progress,
        )


if __name__ == "__main__":
    unittest.main()
