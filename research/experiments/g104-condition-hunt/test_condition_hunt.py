#!/usr/bin/env python3
"""Regression tests for the G-104 off-loop enumerator."""

import unittest

from condition_hunt import (
    calibration_report,
    cellwise_coefficient_search,
    exhaustive_search,
    firing_report,
    independence_report,
)


class ConditionHuntTest(unittest.TestCase):
    def test_reviewed_lean_obstructions_calibrate(self) -> None:
        report = calibration_report()
        self.assertEqual(
            [item["name"] for item in report],
            ["FaceLiftObstruction", "EdgeFiberObstruction", "LoopLiftObstruction"],
        )
        self.assertTrue(all(item["calibration_pass"] for item in report))

    def test_each_candidate_clause_has_a_removal_witness(self) -> None:
        report = independence_report()
        self.assertEqual(len(report), 7)
        self.assertTrue(all(item["independence_pass"] for item in report))
        self.assertTrue(all(not item["h1"]["isomorphism"] for item in report))
        c0 = report[0]
        self.assertFalse(c0["target_supports"]["C0_chart_support_image"])
        self.assertTrue(c0["target_supports"]["pi_compatible"])
        self.assertEqual(c0["reading_comparison"]["canonical_factor_pi"], [0, 0, 1, 2])

    def test_nondegenerate_positive_fires(self) -> None:
        report = firing_report()
        self.assertTrue(report["firing_pass"])
        self.assertTrue(report["h1"]["isomorphism"])
        self.assertTrue(all(report["firing_gate"].values()))
        self.assertTrue(report["firing_gate"]["comparison_factor_pi_noninjective"])
        self.assertTrue(report["firing_gate"]["nerve_chart_map_phi_noninjective"])
        self.assertEqual(report["reading_comparison"]["canonical_factor_pi"], [0, 0, 1, 2])
        self.assertEqual(report["reading_comparison"]["law_evaluation"], [0, 0, 1, 2])

    def test_cellwise_free_coefficients_force_structural_stop(self) -> None:
        report = cellwise_coefficient_search()
        self.assertTrue(report["structural_negative"])
        pair = report["same_incidence_pair"]
        support_hole = pair["support_hole_counterexample"]
        duplicate = pair["duplicate_coordinate_counterexample"]
        self.assertEqual(pair["positive"]["conditions"], support_hole["conditions"])
        self.assertEqual(pair["positive"]["conditions"], duplicate["conditions"])
        self.assertEqual(pair["positive"]["reading_comparison"], support_hole["reading_comparison"])
        self.assertEqual(pair["positive"]["reading_comparison"], duplicate["reading_comparison"])
        self.assertEqual(pair["positive"]["target_supports"], support_hole["target_supports"])
        self.assertEqual(pair["positive"]["target_supports"], duplicate["target_supports"])
        self.assertIn("2 fine coordinate(s)", duplicate["cell_maps"])
        self.assertTrue(pair["positive"]["h1"]["isomorphism"])
        self.assertFalse(support_hole["h1"]["isomorphism"])
        self.assertFalse(duplicate["h1"]["isomorphism"])
        self.assertGreater(support_hole["h1"]["coarse_h1_dimension"], 0)
        self.assertGreater(support_hole["h1"]["fine_h1_dimension"], 0)
        self.assertGreater(duplicate["h1"]["coarse_h1_dimension"], 0)
        self.assertGreater(duplicate["h1"]["fine_h1_dimension"], 0)

    def test_small_exhaustive_slice_has_no_counterexample(self) -> None:
        report = exhaustive_search(
            max_coarse_vertices=2,
            max_coarse_edges=2,
            max_coarse_faces=1,
            max_fine_vertices=3,
            max_coefficient_rank=2,
        )
        self.assertGreater(report["counts"]["candidate_refinements"], 0)
        self.assertEqual(report["counterexamples"], [])


if __name__ == "__main__":
    unittest.main()
