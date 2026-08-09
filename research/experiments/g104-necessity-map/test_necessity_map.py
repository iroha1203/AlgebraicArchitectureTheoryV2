#!/usr/bin/env python3
"""Regression tests for the G-104 exact necessity-map engine."""

import json
import unittest

from necessity_map import (
    bounded_core_population_summary,
    canonical_firing_report,
    condition_report,
    indicator_realizability_report,
    nonempty_subsets,
    parser,
    r0_report,
    r1_report,
    r1_witness_report,
    required_fixture_catalog_summary,
    run_report,
    support_hole_fixture,
    support_hole_report,
)


class NecessityMapTest(unittest.TestCase):
    def test_r0_a_three_reviewed_obstructions(self) -> None:
        report = r0_report()["calibration"]["a_three_lean_obstructions"]
        self.assertEqual(
            [item["fixture"]["name"] for item in report],
            ["FaceLiftObstruction", "EdgeFiberObstruction", "LoopLiftObstruction"],
        )
        self.assertTrue(
            all(
                item["fixture"]["targets"]
                == {
                    "coarse_count": 3,
                    "fine_count": 4,
                    "canonical_surjective_factor_pi": [0, 0, 1, 2],
                }
                for item in report
            )
        )
        self.assertEqual(
            [
                (
                    item["blocks"][0]["h1"]["injective"],
                    item["blocks"][0]["h1"]["surjective"],
                )
                for item in report
            ],
            [(True, False), (True, False), (False, True)],
        )
        self.assertTrue(all(item["calibration_pass"] for item in report))

    def test_r0_b_derived_support_hole_and_relative_c2(self) -> None:
        report = support_hole_report()
        self.assertEqual(
            report["law_value_singleton_block_direct_sum"],
            {
                "coarse_h1_dimension": 4,
                "fine_h1_dimension": 1,
                "comparison_rank": 1,
                "injective": False,
                "surjective": True,
                "isomorphism": False,
            },
        )
        self.assertEqual(report["relative_C2_failing_subsets"], [[0], [1]])
        self.assertEqual(
            report["fixture"]["fine"]["derived_edge_supports"],
            [[], [0], [0], [0, 1], [1], [0]],
        )

    def test_coordinate_subnerve_selects_cells_and_reindexes(self) -> None:
        comparison = support_hole_fixture()
        a = comparison.coordinate_subcomparison(frozenset((0,)))
        b = comparison.coordinate_subcomparison(frozenset((1,)))
        self.assertEqual(a.coarse.edges, (0, 1, 2, 3, 4))
        self.assertEqual(a.fine.edges, (1, 2, 3, 5))
        self.assertEqual(a.morphism.edge_map, (0, 1, 2, 4))
        self.assertEqual(b.fine.vertices, (1, 2, 3))
        self.assertEqual(b.fine.edges, (3, 4))
        self.assertEqual(b.morphism.vertex_map, (0, 1, 2))
        self.assertFalse(condition_report(comparison)["aggregate"]["C2"])

    def test_r0_c_and_e_canonical_firing_oracle(self) -> None:
        report = canonical_firing_report()
        self.assertEqual(
            report["fixture"]["targets"],
            {
                "coarse_count": 2,
                "fine_count": 3,
                "canonical_surjective_factor_pi": [0, 0, 1],
            },
        )
        self.assertEqual(
            report["actual_law_blocks"]["value_zero"]["h1"][
                "coarse_h1_dimension"
            ],
            1,
        )
        self.assertEqual(
            report["actual_law_blocks"]["value_zero"]["h1"],
            {
                "coarse_h1_dimension": 1,
                "fine_h1_dimension": 1,
                "comparison_rank": 1,
                "injective": True,
                "surjective": True,
                "isomorphism": True,
            },
        )
        self.assertEqual(
            report["actual_law_blocks"]["value_one"]["h1"],
            {
                "coarse_h1_dimension": 0,
                "fine_h1_dimension": 0,
                "comparison_rank": 0,
                "injective": True,
                "surjective": True,
                "isomorphism": True,
            },
        )
        self.assertEqual(
            report["global_supported_direct_sum"],
            {
                "coarse_h1_dimension": 1,
                "fine_h1_dimension": 1,
                "comparison_rank": 1,
                "injective": True,
                "surjective": True,
                "isomorphism": True,
            },
        )
        self.assertTrue(report["uniform"])
        self.assertTrue(all(report["conditions"]["aggregate"].values()))

    def test_r0_d_indicator_realizability_for_both_factors(self) -> None:
        report = indicator_realizability_report()
        self.assertTrue(report["all_nonempty_A_realized"])
        self.assertEqual(
            [factor["factor_pi"] for factor in report["factors"]],
            [[0, 0, 1], [0, 0, 1, 2]],
        )
        self.assertEqual(
            [factor["nonempty_subset_count"] for factor in report["factors"]],
            [3, 7],
        )
        for factor in report["factors"]:
            self.assertEqual(factor["law_type"], "Unit")
            self.assertEqual(factor["value_type"], "Bool")
            self.assertTrue(all(case["assertions"]["A_is_true_fiber"] for case in factor["cases"]))

    def test_r0_gate_covers_a_through_e(self) -> None:
        report = r0_report()
        self.assertTrue(report["r0_pass"])
        self.assertEqual(
            list(report["calibration"]),
            [
                "a_three_lean_obstructions",
                "b_derived_support_hole",
                "c_block_reduction",
                "d_indicator_realizability",
                "e_canonical_firing_oracle",
            ],
        )

    def test_seven_reproducible_nondegenerate_not_necessary_witnesses(self) -> None:
        report = r1_witness_report()
        self.assertEqual([item["clause"] for item in report], [f"C{i}" for i in range(7)])
        self.assertTrue(all(item["verdict"] == "not-necessary" for item in report))
        self.assertTrue(all(item["uniform"] for item in report))
        self.assertTrue(all(item["witness_pass"] for item in report))
        for item in report:
            self.assertFalse(item["conditions"]["aggregate"][item["clause"]])
            self.assertTrue(item["nondegenerate_blocks_with_both_H1_nonzero"])
            self.assertIn(
                [0, 1],
                item["nondegenerate_blocks_where_named_failure_fires"],
            )
            self.assertEqual(
                [
                    (
                        block["h1"]["coarse_h1_dimension"],
                        block["h1"]["fine_h1_dimension"],
                        block["h1"]["comparison_rank"],
                    )
                    for block in item["blocks"]
                ],
                [(1, 1, 1), (0, 0, 0), (1, 1, 1)],
            )

    def test_preregistered_bounded_population_is_exhaustive_and_compact(self) -> None:
        report = bounded_core_population_summary()
        self.assertEqual(
            report["totals"],
            {
                "raw_support_assignments": 1526,
                "compatible_comparisons": 590,
                "uniform_comparisons": 580,
                "nonuniform_comparisons": 10,
            },
        )
        self.assertEqual(len(report["counts_by_template_and_factor"]), 24)
        self.assertEqual(report["preregistered_issue_comment"], 5230270861)
        self.assertNotIn("comparisons", report)

    def test_required_fixture_catalog_matches_registered_maxima(self) -> None:
        report = required_fixture_catalog_summary()
        self.assertEqual(report["fixture_count"], 13)
        self.assertEqual(report["observed_maxima"], report["registered_limits"])
        self.assertEqual(
            report["category_counts"],
            {
                "current_canonical_oracle": 1,
                "derived_support_hole": 1,
                "lean_obstruction": 3,
                "necessity_witness": 7,
                "old_positive_G103_scale": 1,
            },
        )

    def test_r1_and_run_reports_have_deterministic_structure(self) -> None:
        first = run_report()
        second = run_report()
        self.assertEqual(first, second)
        self.assertEqual(
            json.dumps(first, ensure_ascii=False, indent=2, sort_keys=True),
            json.dumps(second, ensure_ascii=False, indent=2, sort_keys=True),
        )
        self.assertEqual(list(first), [
            "artifact",
            "arithmetic",
            "randomness",
            "serialization",
            "r0",
            "r1",
            "engine_gates_pass",
            "R2_prose_implemented",
        ])
        self.assertTrue(first["engine_gates_pass"])
        self.assertFalse(first["R2_prose_implemented"])
        self.assertTrue(r1_report()["all_seven_verdicts_fixed"])

    def test_cli_contract_is_r0_r1_run(self) -> None:
        action = next(action for action in parser()._actions if action.dest == "command")
        self.assertEqual(tuple(action.choices), ("r0", "r1", "run"))
        self.assertEqual(nonempty_subsets(2), (
            frozenset((0,)),
            frozenset((1,)),
            frozenset((0, 1)),
        ))


if __name__ == "__main__":
    unittest.main()
