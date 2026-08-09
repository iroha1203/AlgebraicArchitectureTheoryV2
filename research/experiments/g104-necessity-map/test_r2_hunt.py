#!/usr/bin/env python3
"""Regression tests for the preregistered R2 checkpoint rounds."""

import unittest

from necessity_map import H1Analysis
from r2_hunt import (
    CANDIDATE_SEMANTIC_SHA256,
    CERTIFIED_SEMANTIC_SHA256,
    COMPONENT_SEMANTIC_SHA256,
    _case_id,
    chain3_fixture,
    round1_report,
    round2_report,
    round3_report,
    round4_report,
    round5_report,
    round6_report,
    round7_report,
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


if __name__ == "__main__":
    unittest.main()
