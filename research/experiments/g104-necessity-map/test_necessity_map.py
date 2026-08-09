#!/usr/bin/env python3
"""Regression tests for the G-104 exact necessity-map engine."""

import json
import inspect
import unittest
from dataclasses import replace
from unittest.mock import patch

from necessity_map import (
    Matrix,
    Nerve,
    SingletonLawFamily,
    UniformComparison,
    bounded_core_population_summary,
    build_law_generated_comparison,
    canonical_firing_fixture,
    canonical_firing_law_family,
    canonical_firing_report,
    condition_report,
    indicator_factor_report,
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
    def test_nerve_rejects_d1d0_zero_face_without_endpoint_coherence(self) -> None:
        raw_d0 = Matrix.from_mutable(((0, 0), (0, 0), (0, 0)))
        raw_d1 = Matrix.from_mutable(((1, -1, 1),))
        self.assertTrue((raw_d1 @ raw_d0).is_zero())
        with self.assertRaisesRegex(ValueError, "three endpoint equalities"):
            Nerve(
                2,
                ((0, 0), (1, 1), (0, 0)),
                ((0, 1, 2),),
            )

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
        generated = report["law_generated_global"]
        block_sum = report["value_block_A_subnerve_direct_sum"]
        self.assertEqual(generated, block_sum)
        self.assertTrue(all(report["exact_global_block_matrix_equality"].values()))
        self.assertEqual(
            report["block_reduction_pass"],
            all(report["exact_global_block_matrix_equality"].values()),
        )
        self.assertEqual(
            report["canonical_oracle_pass"],
            all(
                (
                    report["block_reduction_pass"],
                    all(report["canonical_fixed_fixture_assertions"].values()),
                    all(report["canonical_nonvacuity_assertions"].values()),
                    all(report["canonical_firing_class_assertions"].values()),
                    all(report["computed_oracle_assertions"].values()),
                )
            ),
        )
        self.assertEqual(
            report["canonical_fixed_fixture"],
            {
                "name": "ResolutionInvarianceFiringData",
                "target_counts": {"coarse": 2, "fine": 3},
                "factor_pi": [0, 0, 1],
                "coarse": {
                    "nerve": {
                        "vertices": 2,
                        "edges": [[0, 1], [1, 0], [0, 0]],
                        "faces": [[2, 2, 2]],
                    },
                    "chart_supports": [[0, 1], [0]],
                    "edge_supports": [[0], [0], [0, 1]],
                    "face_supports": [[0, 1]],
                },
                "fine": {
                    "nerve": {
                        "vertices": 3,
                        "edges": [
                            [0, 2],
                            [2, 0],
                            [0, 0],
                            [0, 1],
                            [1, 1],
                        ],
                        "faces": [[2, 2, 2], [4, 4, 4]],
                    },
                    "chart_supports": [[0, 2], [0, 1], [0]],
                    "edge_supports": [[0], [0], [0, 2], [0], [0, 1]],
                    "face_supports": [[0, 2], [0, 1]],
                },
                "morphism": {
                    "chart_map_phi": [0, 0, 1],
                    "edge_map": [0, 1, 2, None, None],
                    "face_map": [0, None],
                },
                "law_family": {
                    "name": "canonical_nonconstant_law",
                    "law_type": "PUnit",
                    "law_carrier": ["unit"],
                    "value_type": "Fin 2",
                    "source_evaluation": [0, 0, 1],
                    "coarse_descend": [0, 1],
                    "fine_descend": [0, 0, 1],
                },
            },
        )
        self.assertTrue(all(report["canonical_fixed_fixture_assertions"].values()))
        nonvacuity = report["canonical_nonvacuity_evidence"]
        self.assertEqual(
            nonvacuity["map_properties"],
            {
                "pi_fine_target_to_coarse_target": {
                    "mapping": [0, 0, 1],
                    "surjective": True,
                    "noninjective_witness": {
                        "domain_elements": [0, 1],
                        "common_image": 0,
                    },
                },
                "phi_fine_chart_to_coarse_chart": {
                    "mapping": [0, 0, 1],
                    "surjective": True,
                    "noninjective_witness": {
                        "domain_elements": [0, 1],
                        "common_image": 0,
                    },
                },
            },
        )
        self.assertEqual(
            nonvacuity["mapped_faces"],
            [
                {
                    "fine_face": 0,
                    "coarse_face": 0,
                    "fine_boundary": [2, 2, 2],
                    "mapped_boundary": [2, 2, 2],
                    "coarse_boundary": [2, 2, 2],
                }
            ],
        )
        self.assertEqual(
            nonvacuity["degenerate_edges"],
            [
                {
                    "fine_edge": 3,
                    "endpoints": [0, 1],
                    "mapped_endpoints": [0, 0],
                    "support": [0],
                },
                {
                    "fine_edge": 4,
                    "endpoints": [1, 1],
                    "mapped_endpoints": [0, 0],
                    "support": [0, 1],
                },
            ],
        )
        self.assertEqual(
            nonvacuity["degenerate_faces"],
            [
                {
                    "fine_face": 1,
                    "boundary": [4, 4, 4],
                    "mapped_boundary": [None, None, None],
                    "support": [0, 1],
                }
            ],
        )
        self.assertEqual(
            nonvacuity["proper_one_label_subnerve"],
            {
                "coarse_targets_A": [1],
                "fine_targets_pi_preimage_A": [2],
                "coarse_original_cells": {
                    "charts": [0],
                    "edges": [2],
                    "faces": [0],
                },
                "fine_original_cells": {
                    "charts": [0],
                    "edges": [2],
                    "faces": [0],
                },
                "coarse_incidence": {
                    "vertices": 1,
                    "edges": [[0, 0]],
                    "faces": [[0, 0, 0]],
                },
                "fine_incidence": {
                    "vertices": 1,
                    "edges": [[0, 0]],
                    "faces": [[0, 0, 0]],
                },
                "restricted_maps": {
                    "chart_map_phi": [0],
                    "edge_map": [0],
                    "face_map": [0],
                },
            },
        )
        self.assertTrue(all(report["canonical_nonvacuity_assertions"].values()))
        firing = report["canonical_firing_class_evidence"]
        self.assertEqual(
            firing["coarse_firing_1_cochain"],
            {"rows": 4, "cols": 1, "entries": [[1], [0], [0], [0]]},
        )
        self.assertEqual(
            firing["coarse_cycle_value"],
            {"rows": 2, "cols": 1, "entries": [[0], [0]]},
        )
        self.assertEqual(
            firing["directed_period_functional"],
            {"rows": 1, "cols": 4, "entries": [[1, 1, 0, 0]]},
        )
        self.assertEqual(
            firing["directed_period_on_coboundaries"],
            {"rows": 1, "cols": 3, "entries": [[0, 0, 0]]},
        )
        self.assertEqual(
            firing["directed_period_on_firing"],
            {"rows": 1, "cols": 1, "entries": [[1]]},
        )
        self.assertEqual(
            firing["generated_fine_image"],
            {
                "rows": 6,
                "cols": 1,
                "entries": [[1], [0], [0], [0], [0], [0]],
            },
        )
        self.assertEqual(
            firing["fine_cycle_value"],
            {"rows": 3, "cols": 1, "entries": [[0], [0], [0]]},
        )
        self.assertEqual(
            (
                firing["coarse_coboundary_rank"],
                firing["coarse_coboundary_plus_firing_rank"],
                firing["fine_coboundary_rank"],
                firing["fine_coboundary_plus_image_rank"],
            ),
            (1, 2, 2, 3),
        )
        self.assertTrue(all(report["canonical_firing_class_assertions"].values()))
        self.assertEqual(
            generated["coarse"]["basis"],
            {
                "charts": [
                    {"cell": 0, "value": 0},
                    {"cell": 1, "value": 0},
                    {"cell": 0, "value": 1},
                ],
                "edges": [
                    {"cell": 0, "value": 0},
                    {"cell": 1, "value": 0},
                    {"cell": 2, "value": 0},
                    {"cell": 2, "value": 1},
                ],
                "faces": [
                    {"cell": 0, "value": 0},
                    {"cell": 0, "value": 1},
                ],
            },
        )
        self.assertEqual(
            generated["fine"]["basis"],
            {
                "charts": [
                    {"cell": 0, "value": 0},
                    {"cell": 1, "value": 0},
                    {"cell": 2, "value": 0},
                    {"cell": 0, "value": 1},
                ],
                "edges": [
                    {"cell": 0, "value": 0},
                    {"cell": 1, "value": 0},
                    {"cell": 2, "value": 0},
                    {"cell": 3, "value": 0},
                    {"cell": 4, "value": 0},
                    {"cell": 2, "value": 1},
                ],
                "faces": [
                    {"cell": 0, "value": 0},
                    {"cell": 1, "value": 0},
                    {"cell": 0, "value": 1},
                ],
            },
        )
        self.assertEqual(
            generated["coarse"]["d0"]["entries"],
            [[-1, 1, 0], [1, -1, 0], [0, 0, 0], [0, 0, 0]],
        )
        self.assertEqual(
            generated["coarse"]["d1"]["entries"],
            [[0, 0, 1, 0], [0, 0, 0, 1]],
        )
        self.assertEqual(
            generated["fine"]["d0"]["entries"],
            [
                [-1, 0, 1, 0],
                [1, 0, -1, 0],
                [0, 0, 0, 0],
                [-1, 1, 0, 0],
                [0, 0, 0, 0],
                [0, 0, 0, 0],
            ],
        )
        self.assertEqual(
            generated["fine"]["d1"]["entries"],
            [
                [0, 0, 1, 0, 0, 0],
                [0, 0, 0, 0, 1, 0],
                [0, 0, 0, 0, 0, 1],
            ],
        )
        self.assertEqual(
            generated["pullback0"]["entries"],
            [[1, 0, 0], [1, 0, 0], [0, 1, 0], [0, 0, 1]],
        )
        self.assertEqual(
            generated["pullback1"]["entries"],
            [
                [1, 0, 0, 0],
                [0, 1, 0, 0],
                [0, 0, 1, 0],
                [0, 0, 0, 0],
                [0, 0, 0, 0],
                [0, 0, 0, 1],
            ],
        )
        self.assertEqual(
            generated["pullback2"]["entries"],
            [[1, 0], [0, 0], [0, 1]],
        )
        self.assertEqual(
            generated["h1_map"],
            {
                "coarse_representatives": {
                    "rows": 4,
                    "cols": 1,
                    "entries": [[1], [0], [0], [0]],
                },
                "fine_representatives": {
                    "rows": 6,
                    "cols": 1,
                    "entries": [[1], [0], [0], [0], [0], [0]],
                },
                "matrix": {"rows": 1, "cols": 1, "entries": [[1]]},
            },
        )
        self.assertTrue(report["uniform"])
        self.assertTrue(all(report["conditions"]["aggregate"].values()))

    def test_global_law_generation_does_not_call_A_subcomparison(self) -> None:
        comparison = canonical_firing_fixture()
        with patch.object(
            UniformComparison,
            "coordinate_subcomparison",
            side_effect=AssertionError("global path called A-subcomparison"),
        ):
            generated = build_law_generated_comparison(
                comparison,
                SingletonLawFamily(
                    name="canonical_nonconstant_law",
                    value_type="Fin2",
                    source_evaluation=(0, 0, 1),
                    coarse_descend=(0, 1),
                    fine_descend=(0, 0, 1),
                ),
            )
        self.assertEqual(
            (
                len(generated.coarse.chart_basis),
                len(generated.coarse.edge_basis),
                len(generated.coarse.face_basis),
            ),
            (3, 4, 2),
        )
        self.assertEqual(
            (
                len(generated.fine.chart_basis),
                len(generated.fine.edge_basis),
                len(generated.fine.face_basis),
            ),
            (4, 6, 3),
        )
        self.assertEqual(
            (
                generated.pullback0.rows,
                generated.pullback1.rows,
                generated.pullback2.rows,
            ),
            (4, 6, 3),
        )

    def test_canonical_oracle_fails_closed_when_fixed_fixture_drifts(self) -> None:
        fixture = canonical_firing_fixture()
        drifted = replace(
            fixture,
            fine_chart_supports=(
                fixture.fine_chart_supports[0],
                frozenset((0,)),
                fixture.fine_chart_supports[2],
            ),
        )
        with patch(
            "necessity_map.canonical_firing_fixture",
            return_value=drifted,
        ):
            with self.assertRaisesRegex(
                AssertionError,
                "canonical firing oracle mismatch",
            ):
                canonical_firing_report()

    def test_canonical_oracle_fails_closed_when_law_metadata_drifts(self) -> None:
        law_family = canonical_firing_law_family()
        drifts = {
            "family_name": replace(law_family, name="renamed_law"),
            "law_carrier": replace(law_family, law_carrier=("other",)),
            "value_type": replace(law_family, value_type="Bool"),
        }
        for field, drifted in drifts.items():
            with self.subTest(field=field):
                with patch(
                    "necessity_map.canonical_firing_law_family",
                    return_value=drifted,
                ):
                    with self.assertRaisesRegex(
                        AssertionError,
                        "canonical firing oracle mismatch",
                    ):
                        canonical_firing_report()

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
            self.assertEqual(factor["law_type"], "PUnit")
            self.assertEqual(factor["law_type_cardinality"], 1)
            self.assertEqual(factor["value_type"], "Bool")
            self.assertEqual(factor["value_type_cardinality"], 2)
            self.assertTrue(all(factor["dedup_fired_by_dimension"].values()))
            self.assertEqual(
                factor["all_pass"],
                all(
                    all(case["assertions"].values())
                    and all(
                        case["cell_incidence_partial_map_assertions"].values()
                    )
                    for case in factor["cases"]
                )
                and all(factor["dedup_fired_by_dimension"].values()),
            )
            for case in factor["cases"]:
                assertions = case["assertions"]
                self.assertEqual(
                    assertions["fine_read_identity_surjective"],
                    sorted(factor["fine_read"])
                    == list(range(factor["source_count"])),
                )
                self.assertEqual(
                    assertions["coarse_read_factors_through_fine"],
                    all(
                        factor["coarse_read"][source]
                        == factor["factor_pi"][factor["fine_read"][source]]
                        for source in range(factor["source_count"])
                    ),
                )
                self.assertEqual(
                    assertions["unit_law_family_fields_finite"],
                    factor["law_type_cardinality"] == 1,
                )
                self.assertEqual(
                    assertions["bool_has_two_distinct_values"],
                    factor["value_type_cardinality"] == 2,
                )
                self.assertTrue(case["assertions"]["A_is_true_fiber"])
                self.assertEqual(
                    case["actual_true_coordinate_block"],
                    case["A_subnerve_constant_Q_block"],
                )
                self.assertEqual(
                    case["actual_true_block_signatures"],
                    case["A_subnerve_signatures"],
                )
                self.assertTrue(
                    all(case["cell_incidence_partial_map_assertions"].values())
                )
                self.assertEqual(
                    case["actual_true_block_signatures"]["coarse"][
                        "original_cells"
                    ],
                    {
                        "charts": [
                            item["cell"]
                            for item in case["actual_true_coordinate_block"][
                                "coarse"
                            ]["basis"]["charts"]
                        ],
                        "edges": [
                            item["cell"]
                            for item in case["actual_true_coordinate_block"][
                                "coarse"
                            ]["basis"]["edges"]
                        ],
                        "faces": [
                            item["cell"]
                            for item in case["actual_true_coordinate_block"][
                                "coarse"
                            ]["basis"]["faces"]
                        ],
                    },
                )
        canonical_zero = report["factors"][0]["cases"][0]
        self.assertEqual(canonical_zero["coarse_targets_A"], [0])
        self.assertGreater(
            canonical_zero["coordinate_dedup"]["fine"]["charts"][
                "deduplicated_occurrences"
            ],
            0,
        )
        self.assertGreater(
            canonical_zero["coordinate_dedup"]["fine"]["edges"][
                "deduplicated_occurrences"
            ],
            0,
        )
        self.assertGreater(
            canonical_zero["coordinate_dedup"]["fine"]["faces"][
                "deduplicated_occurrences"
            ],
            0,
        )

    def test_r0_pass_fields_and_indicator_oracles_are_computed(self) -> None:
        indicator_source = inspect.getsource(indicator_factor_report)
        for forbidden in (
            '"fine_read_identity_surjective": True',
            '"coarse_read_factors_through_fine": True',
            '"unit_law_family_fields_finite": True',
            "False is not True",
        ):
            self.assertNotIn(forbidden, indicator_source)
        canonical_source = inspect.getsource(canonical_firing_report)
        self.assertNotIn("literal_oracle_assertions", canonical_source)
        self.assertNotIn('"canonical_oracle_pass": True', canonical_source)
        report = r0_report()
        calibration = report["calibration"]
        self.assertEqual(
            report["r0_pass"],
            all(
                item["calibration_pass"]
                for item in calibration["a_three_lean_obstructions"]
            )
            and calibration["b_derived_support_hole"]["calibration_pass"]
            and calibration["c_block_reduction"]["pass"]
            and calibration["e_canonical_firing_oracle"][
                "canonical_oracle_pass"
            ]
            and calibration["d_indicator_realizability"][
                "all_nonempty_A_realized"
            ],
        )

    def test_r0_gate_covers_a_through_e(self) -> None:
        report = r0_report()
        self.assertTrue(report["r0_pass"])
        reduction = report["calibration"]["c_block_reduction"]
        self.assertEqual(
            reduction["law_generated_global"],
            reduction["value_block_A_subnerve_direct_sum"],
        )
        self.assertEqual(
            reduction["pass"],
            all(reduction["exact_global_block_matrix_equality"].values()),
        )
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
