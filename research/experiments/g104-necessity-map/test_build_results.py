#!/usr/bin/env python3
"""Regression tests for the committed slim checkpoint summary."""

from __future__ import annotations

from hashlib import sha256
import json
from pathlib import Path
import unittest
from unittest.mock import patch

import build_results
import r2_hunt


class Round12ParentBoundaryTest(unittest.TestCase):
    def test_round_keys_are_the_fixed_twelve_key_tuple(self) -> None:
        expected = (
            "round1_direct",
            "round2_component",
            "round3_certified",
            "round4_closed_2d",
            "round5_mixed_support",
            "round6_nonfree_linear_face_chain",
            "round7_nonfree_branching_face_chain",
            "round8_invalid_diagnostic_relation_grammar",
            "round9_valid_mixed_relation_support",
            "round10_valid_multichart_face_chain",
            "round11_post_punit_wheel_bipartite",
            "round12_post_punit_octahedral_partitioned",
        )
        self.assertIsInstance(
            build_results.R2_ROUND_KEYS_THROUGH_ROUND12,
            tuple,
        )
        self.assertEqual(len(build_results.R2_ROUND_KEYS_THROUGH_ROUND12), 12)
        self.assertEqual(build_results.R2_ROUND_KEYS_THROUGH_ROUND12, expected)
        self.assertIs(
            build_results.R2_ROUND_KEYS,
            build_results.R2_ROUND_KEYS_THROUGH_ROUND12,
        )
        self.assertIs(
            build_results.R2_ROUND_PROVENANCE,
            build_results.R2_ROUND_PROVENANCE_THROUGH_ROUND12,
        )
        self.assertEqual(
            tuple(build_results.R2_ROUND_PROVENANCE_THROUGH_ROUND12),
            expected,
        )


class BuildResultsSummaryTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.through12_full = build_results.results_report_through_round12()
        with patch.object(
            build_results,
            "results_report_through_round12",
            return_value=cls.through12_full,
        ) as full_helper:
            cls.full = build_results.results_report()
        cls.full_helper_mock = full_helper
        cls.full_rendered = build_results.render_json(cls.full)
        cls.through12_summary = (
            build_results.results_summary_report_through_round12(
                cls.through12_full
            )
        )
        with patch.object(
            build_results,
            "results_summary_report_through_round12",
            wraps=build_results.results_summary_report_through_round12,
        ) as summary_helper:
            cls.summary = build_results.results_summary_report(cls.full)
        cls.summary_helper_mock = summary_helper
        cls.summary_rendered = build_results.render_json(cls.summary)

    def test_through_round12_helpers_match_public_canonical_bytes(self) -> None:
        self.full_helper_mock.assert_called_once_with()
        self.summary_helper_mock.assert_called_once_with(self.full)

        through12_full_rendered = build_results.render_json(self.through12_full)
        self.assertEqual(through12_full_rendered, self.full_rendered)
        self.assertEqual(
            sha256(through12_full_rendered.encode("utf-8")).hexdigest(),
            build_results.FULL_RESULTS_EXPECTED_SHA256,
        )
        self.assertIsNot(self.full, self.through12_full)

        through12_summary_rendered = build_results.render_json(
            self.through12_summary
        )
        self.assertEqual(through12_summary_rendered, self.summary_rendered)
        self.assertEqual(
            sha256(through12_summary_rendered.encode("utf-8")).hexdigest(),
            build_results.SUMMARY_RESULTS_EXPECTED_SHA256,
        )
        self.assertIsNot(self.summary, self.through12_summary)

    def test_registered_full_audit_hashes_are_unchanged(self) -> None:
        self.assertEqual(
            sha256(self.full_rendered.encode("utf-8")).hexdigest(),
            build_results.FULL_RESULTS_EXPECTED_SHA256,
        )
        self.assertEqual(
            self.summary["r0"]["payload_sha256"],
            r2_hunt.POST_PUNIT_R0_SEMANTIC_SHA256,
        )
        self.assertEqual(
            self.summary["r1"]["payload_sha256"],
            r2_hunt.FINAL_R1_SEMANTIC_SHA256,
        )
        self.assertEqual(
            self.summary["provenance"]["post_punit_manifest_sha256"],
            r2_hunt.POST_PUNIT_MANIFEST_REGISTERED_SHA256,
        )
        for row in self.summary["r2"]["rounds"]:
            with self.subTest(round=row["round"]):
                self.assertEqual(
                    row["payload_sha256"],
                    r2_hunt._canonical_report_sha256(
                        self.full["r2"][row["key"]]
                    ),
                )
        candidates = self.summary["r2"]["candidate_generations"]
        self.assertEqual(
            [candidate["semantic_id"] for candidate in candidates],
            [
                r2_hunt.CANDIDATE_SEMANTIC_ID,
                r2_hunt.COMPONENT_SEMANTIC_ID,
                r2_hunt.CERTIFIED_SEMANTIC_ID,
            ],
        )
        self.assertEqual(
            candidates[-1]["semantic_sha256"],
            r2_hunt.CERTIFIED_SEMANTIC_SHA256,
        )

    def test_summary_is_a_complete_consistent_projection(self) -> None:
        for key, value in self.full["terminal"].items():
            self.assertEqual(self.summary["terminal"][key], value)
        self.assertEqual(
            self.summary["terminal"]["stop_audit"],
            self.full["r2"][
                "round12_post_punit_octahedral_partitioned"
            ]["stop_audit"],
        )
        self.assertTrue(self.summary["r0"]["pass"])
        self.assertTrue(
            all(gate["pass"] for gate in self.summary["r0"]["gates"].values())
        )
        calibration = self.full["r0"]["calibration"]
        gate_a = self.summary["r0"]["gates"]["a_three_lean_obstructions"]
        for projected, source in zip(
            gate_a["fixtures"],
            calibration["a_three_lean_obstructions"],
            strict=True,
        ):
            self.assertEqual(projected["name"], source["fixture"]["name"])
            self.assertEqual(projected["pass"], source["calibration_pass"])
            self._assert_blocks_equal(projected["blocks"], source["blocks"])
        gate_b = self.summary["r0"]["gates"]["b_derived_support_hole"]
        source_b = calibration["b_derived_support_hole"]
        self.assertEqual(
            gate_b["global_h1"],
            source_b["law_value_singleton_block_direct_sum"],
        )
        self._assert_blocks_equal(gate_b["blocks"], source_b["blocks"])
        gate_c = self.summary["r0"]["gates"]["c_block_reduction"]
        source_c = calibration["c_block_reduction"]
        self.assertEqual(gate_c["global_h1"], source_c["law_generated_global"]["h1"])
        for name, source_block in source_c["actual_law_blocks"].items():
            self._assert_block_equal(gate_c["blocks"][name], source_block)
        gate_d = self.summary["r0"]["gates"]["d_indicator_realizability"]
        source_d = calibration["d_indicator_realizability"]
        for projected, source in zip(
            gate_d["factors"], source_d["factors"], strict=True
        ):
            for field in ("name", "factor_pi", "law_type", "value_type"):
                self.assertEqual(projected[field], source[field])
            self.assertEqual(projected["pass"], source["all_pass"])
            for projected_block, source_case in zip(
                projected["blocks"], source["cases"], strict=True
            ):
                self.assertEqual(
                    projected_block["coarse_targets_A"],
                    source_case["coarse_targets_A"],
                )
                self.assertEqual(
                    projected_block["fine_targets_pi_preimage_A"],
                    source_case["fine_targets_pi_preimage_A"],
                )
                self.assertEqual(
                    projected_block["h1"],
                    source_case["A_subnerve_constant_Q_block"]["h1"],
                )
        gate_e = self.summary["r0"]["gates"]["e_canonical_firing_oracle"]
        source_e = calibration["e_canonical_firing_oracle"]
        self.assertEqual(gate_e["global_h1"], source_e["law_generated_global"]["h1"])
        self._assert_blocks_equal(gate_e["blocks"], source_e["blocks"])
        self.assertEqual(len(self.summary["r1"]["verdicts"]), 7)
        self.assertEqual(self.summary["r1"]["verdicts"], self.full["r1"]["verdicts"])
        self.assertEqual(len(self.summary["r1"]["witnesses"]), 7)
        for witness, source in zip(
            self.summary["r1"]["witnesses"],
            self.full["r1"]["necessity_witnesses"],
            strict=True,
        ):
            with self.subTest(witness=witness["clause"]):
                for field in (
                    "clause",
                    "verdict",
                    "uniform",
                    "failure_scope",
                    "witness_pass",
                    "fixture",
                ):
                    self.assertEqual(witness[field], source[field])
                self.assertEqual(
                    set(witness["fixture"]),
                    {
                        "name",
                        "targets",
                        "coarse",
                        "fine",
                        "morphism",
                        "chartSupport_compatible",
                        "K1_supports_derived_by_intersection",
                    },
                )
                self.assertTrue(witness["blocks"])
                self.assertTrue(
                    all("h1" in block for block in witness["blocks"])
                )
                self._assert_blocks_equal(witness["blocks"], source["blocks"])
        fixtures = self.summary["r2"]["counterexample_fixtures"]
        self.assertEqual(set(fixtures), {"Chain3", "UnkilledTwin"})
        for fixture in fixtures.values():
            self.assertEqual(
                set(fixture["fixture"]),
                {
                    "name",
                    "targets",
                    "coarse",
                    "fine",
                    "morphism",
                    "chartSupport_compatible",
                    "K1_supports_derived_by_intersection",
                },
            )
            self.assertTrue(fixture["blocks"])
        rounds = self.summary["r2"]["rounds"]
        self.assertEqual(len(rounds), 12)
        for row in rounds:
            with self.subTest(round=row["round"]):
                population = row["population"]
                self.assertEqual(
                    population["raw_cases"],
                    population["full_semantic_unique_ids"],
                )
                self.assertEqual(
                    population["raw_cases"],
                    population["prefix_20hex_unique_ids"],
                )
                self.assertEqual(population["full_sha256_collision_count"], 0)
                self.assertEqual(population["prefix_20hex_collision_count"], 0)
                self.assertTrue(row["issue_comments"]["preregistration"])
                self.assertTrue(row["issue_comments"]["result"])
                self.assertIn("progress", row["progress_audit"])
                self.assertIn("valid", row["status"])
                self.assertNotIn("expansion_cases", row)
                self.assertNotIn("canonical_colored_graph_support_codes", row)
                self.assertNotIn("canonical_relation_graph_support_codes", row)
        self.assertFalse(rounds[7]["status"]["valid"])
        self.assertEqual(rounds[10]["status"]["final_stop_c_streak_after_round"], 1)
        self.assertEqual(rounds[11]["status"]["final_stop_c_streak_after_round"], 2)

        full_before_mutation = build_results.render_json(self.full)
        detached = build_results.results_summary_report(self.full)
        self.assertIsNot(detached, self.full)
        detached["r0"]["gates"]["c_block_reduction"]["global_h1"][
            "comparison_rank"
        ] = -1
        detached["r1"]["verdicts"][0]["verdict"] = "mutated"
        detached["r1"]["witnesses"][0]["fixture"]["name"] = "mutated"
        self.assertEqual(build_results.render_json(self.full), full_before_mutation)

    def test_committed_summary_is_deterministic_and_bounded(self) -> None:
        regenerated = build_results.render_json(
            build_results.results_summary_report(self.full)
        )
        self.assertEqual(regenerated, self.summary_rendered)
        self.assertLessEqual(len(regenerated.encode("utf-8")), 100_000)
        self.assertEqual(
            sha256(regenerated.encode("utf-8")).hexdigest(),
            build_results.SUMMARY_RESULTS_EXPECTED_SHA256,
        )
        committed = Path(__file__).with_name("results-summary.json").read_text(
            encoding="utf-8"
        )
        self.assertEqual(committed, regenerated)
        self.assertEqual(json.loads(committed), self.summary)

    def _assert_blocks_equal(
        self,
        projected: list[dict[str, object]],
        source: list[dict[str, object]],
    ) -> None:
        self.assertEqual(len(projected), len(source))
        for projected_block, source_block in zip(projected, source, strict=True):
            self._assert_block_equal(projected_block, source_block)

    def _assert_block_equal(
        self,
        projected: dict[str, object],
        source: dict[str, object],
    ) -> None:
        self.assertEqual(
            projected["coarse_targets_A"], source["coarse_targets_A"]
        )
        self.assertEqual(
            projected["fine_targets_pi_preimage_A"],
            source["fine_targets_pi_preimage_A"],
        )
        self.assertEqual(projected["h1"], source["h1"])


if __name__ == "__main__":
    unittest.main()
