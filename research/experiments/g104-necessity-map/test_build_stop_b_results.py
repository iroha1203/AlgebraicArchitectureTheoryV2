#!/usr/bin/env python3
"""Regression tests for the G_local-v1 Stop-B artifact builder."""

from __future__ import annotations

import ast
from contextlib import ExitStack
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import sys
from tempfile import TemporaryDirectory
import unittest
from unittest.mock import patch

import build_stop_b_results as builder


HERE = Path(__file__).resolve().parent


class StopBBuilderStaticTest(unittest.TestCase):
    def test_builder_direct_call_sites_are_single_and_historical_queries_absent(
        self,
    ) -> None:
        source = (HERE / "build_stop_b_results.py").read_text(
            encoding="utf-8"
        )
        tree = ast.parse(source)
        called_names = [
            node.func.id
            for node in ast.walk(tree)
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
        ]
        called_attributes = [
            node.func.attr
            for node in ast.walk(tree)
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
        ]
        for name in (
            "results_report_through_round12",
            "results_summary_report_through_round12",
            "g_local_v1_preregistration_manifest",
            "check_g_local_v1_stop_b",
        ):
            with self.subTest(single_call=name):
                self.assertEqual(called_names.count(name), 1)
        for forbidden in (
            "round13_report",
            "round14_report",
            "round15_report",
            "_round13_population_query",
            "_round14_engine_query",
            "_round15_engine_query",
        ):
            with self.subTest(forbidden_call=forbidden):
                self.assertNotIn(forbidden, called_names)
                self.assertNotIn(forbidden, called_attributes)

    def test_checker_reconstructs_the_registered_manifest_once(self) -> None:
        source = (HERE / "g_local_v1_stop_b.py").read_text(
            encoding="utf-8"
        )
        tree = ast.parse(source)
        functions = {
            node.name: node
            for node in tree.body
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
        }

        def direct_calls(function_name: str, callee: str) -> int:
            return sum(
                isinstance(node, ast.Call)
                and isinstance(node.func, ast.Name)
                and node.func.id == callee
                for node in ast.walk(functions[function_name])
            )

        self.assertEqual(
            direct_calls(
                "check_g_local_v1_stop_b",
                "_admit_registered_manifest",
            ),
            1,
        )
        self.assertEqual(
            direct_calls(
                "_admit_registered_manifest",
                "g_local_v1_preregistration_manifest",
            ),
            1,
        )

    def test_historical_ledger_has_exact_three_progress_payloads(self) -> None:
        rows = builder.ROUND13_THROUGH_15_IMMUTABLE_HISTORY
        self.assertIsInstance(rows, tuple)
        self.assertEqual(len(rows), 3)
        self.assertEqual(
            tuple(row["round"] for row in rows),
            ("R2-round-13", "R2-round-14", "R2-round-15"),
        )
        self.assertEqual(
            tuple(row["canonical_payload_sha256"] for row in rows),
            (
                "e15fc8dcb99ea7e8e17b1a52cc045379f9757c558a92f25e9d1bfc2bda5450e3",
                "17c9907928a63cdf97e474e7f8813447601010ede07bbe7a43b525ef8551b450",
                "21b59632026d5ec0f104700f26808a8455e2ca607802a108c6934f68e8911969",
            ),
        )
        self.assertEqual(
            tuple(row["canonical_bytes"] for row in rows),
            (5_604_143, 22_818, 97_792),
        )
        self.assertEqual(
            tuple(row["preregistration"]["issue_comment"] for row in rows),
            (5234690436, 5234939066, 5235347217),
        )
        self.assertEqual(
            tuple(row["result"]["issue_comment"] for row in rows),
            (5234839619, 5235064396, 5235636358),
        )
        self.assertTrue(all(row["valid"] for row in rows))
        self.assertTrue(all(row["progress"] for row in rows))
        self.assertTrue(
            all(row["progress_recomputed"] is False for row in rows)
        )
        self.assertTrue(
            all(row["report_or_query_reexecuted"] is False for row in rows)
        )

    def test_canonical_and_result_provenance_constants_are_exact(self) -> None:
        self.assertEqual(
            builder.CANONICAL_SERIALIZATION,
            {
                "encoding": "UTF-8",
                "ensure_ascii": False,
                "indent": 2,
                "sort_keys": True,
                "trailing_newline": True,
            },
        )
        self.assertEqual(
            builder.STOP_B_RESULT_PROVENANCE,
            {
                "issue_comment": 5245347326,
                "created_at": "2026-08-10T20:04:41Z",
                "updated_at": "2026-08-10T20:04:41Z",
            },
        )
        self.assertEqual(
            builder.G107_STOP_B_SYNC_PROVENANCE,
            (
                {
                    "surface": "PR-3955",
                    "comment": 5245356130,
                    "created_at": "2026-08-10T20:05:35Z",
                    "updated_at": "2026-08-10T20:05:35Z",
                },
                {
                    "surface": "Issue-3954",
                    "comment": 5245356137,
                    "created_at": "2026-08-10T20:05:35Z",
                    "updated_at": "2026-08-10T20:05:35Z",
                },
            ),
        )
        self.assertEqual(
            builder.CHECKER_RESULT_COMPACT_EXPECTED_SHA256,
            "0d644121840591cd4303fbda99d94cd887836b001d3993bd9d284bb3c0366c80",
        )
        self.assertEqual(builder.CHECKER_RESULT_COMPACT_EXPECTED_BYTES, 55_566)
        self.assertEqual(
            builder.COMMON_OBSERVATION_EXPECTED_SHA256,
            "742e6395bb21221fcac070975cbe9505d49d0c75f826289984288776836aa7dc",
        )
        self.assertEqual(builder.COMMON_OBSERVATION_EXPECTED_BYTES, 53_279)

    def test_cli_requires_an_explicit_output_path(self) -> None:
        with (
            patch.object(
                builder,
                "stop_b_results_report",
            ) as full_builder,
            patch.object(sys, "argv", ["build_stop_b_results.py"]),
            self.assertRaises(SystemExit) as raised,
        ):
            builder.main()
        self.assertEqual(raised.exception.code, 2)
        full_builder.assert_not_called()


class StopBBuilderIntegrationTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        original_parent_full = builder.results_report_through_round12
        original_parent_summary = builder.results_summary_report_through_round12

        def parent_full_once() -> dict[str, object]:
            cls.parent_full_value = original_parent_full()
            return cls.parent_full_value

        def parent_summary_once(
            full: dict[str, object],
        ) -> dict[str, object]:
            cls.parent_summary_argument = full
            return original_parent_summary(full)

        forbidden_names = (
            "round13_report",
            "round14_report",
            "round15_report",
            "_round13_population_query",
            "_round14_engine_query",
            "_round15_engine_query",
        )
        with ExitStack() as stack:
            cls.parent_full_mock = stack.enter_context(
                patch.object(
                    builder,
                    "results_report_through_round12",
                    side_effect=parent_full_once,
                )
            )
            cls.parent_summary_mock = stack.enter_context(
                patch.object(
                    builder,
                    "results_summary_report_through_round12",
                    side_effect=parent_summary_once,
                )
            )
            cls.manifest_mock = stack.enter_context(
                patch.object(
                    builder,
                    "g_local_v1_preregistration_manifest",
                    wraps=builder.g_local_v1_preregistration_manifest,
                )
            )
            cls.checker_mock = stack.enter_context(
                patch.object(
                    builder,
                    "check_g_local_v1_stop_b",
                    wraps=builder.check_g_local_v1_stop_b,
                )
            )
            cls.forbidden_mocks = {
                name: stack.enter_context(
                    patch.object(
                        builder.historical_source,
                        name,
                        side_effect=AssertionError(
                            f"historical execution forbidden: {name}"
                        ),
                    )
                )
                for name in forbidden_names
            }
            cls.full = builder.stop_b_results_report()
        cls.full_rendered = builder.render_json(cls.full)
        cls.full_before_summary = cls.full_rendered
        cls.summary = builder.stop_b_results_summary(cls.full)
        cls.summary_again = builder.stop_b_results_summary(cls.full)
        cls.summary_rendered = builder.render_json(cls.summary)

    def test_direct_requests_are_once_and_manifest_effective_total_is_two(
        self,
    ) -> None:
        self.__class__.parent_full_mock.assert_called_once_with()
        self.__class__.parent_summary_mock.assert_called_once_with(
            self.__class__.parent_full_value
        )
        self.assertIs(
            self.__class__.parent_summary_argument,
            self.__class__.parent_full_value,
        )
        self.__class__.manifest_mock.assert_called_once_with()
        self.__class__.checker_mock.assert_called_once_with()
        manifest_admission = self.full["g_local_v1"]["manifest_admission"]
        self.assertEqual(manifest_admission["builder_direct_manifest_requests"], 1)
        self.assertEqual(
            manifest_admission[
                "checker_internal_manifest_admission_reconstructions"
            ],
            1,
        )
        self.assertEqual(
            manifest_admission["effective_manifest_constructions"],
            2,
        )
        for mock in self.__class__.forbidden_mocks.values():
            mock.assert_not_called()

    def test_parent_full_and_summary_are_reproduced_fail_closed(self) -> None:
        parent = self.full["immutable_parent_through_round12"]
        full_text = builder.render_json(parent["full_report"])
        summary_text = builder.render_json(parent["summary_report"])
        self.assertEqual(
            sha256(full_text.encode("utf-8")).hexdigest(),
            builder.PARENT_FULL_EXPECTED_SHA256,
        )
        self.assertEqual(
            sha256(summary_text.encode("utf-8")).hexdigest(),
            builder.PARENT_SUMMARY_EXPECTED_SHA256,
        )
        self.assertEqual(
            len(summary_text.encode("utf-8")),
            builder.PARENT_SUMMARY_EXPECTED_BYTES,
        )
        self.assertEqual(
            parent["admission"]["full"]["canonical_sha256"],
            builder.PARENT_FULL_EXPECTED_SHA256,
        )
        self.assertEqual(
            parent["admission"]["summary"]["canonical_sha256"],
            builder.PARENT_SUMMARY_EXPECTED_SHA256,
        )
        self.assertEqual(
            parent["admission"]["round12_payload_sha256"],
            "c9ab928190491610ff1e394fb16fb4e132f117374a317505fbd2025ab5a09f90",
        )

    def test_manifest_checker_and_common_observation_hashes_are_exact(self) -> None:
        stop_b = self.full["g_local_v1"]
        manifest = stop_b["preregistration_manifest"]
        manifest_encoded = builder._compact_json(manifest).encode("utf-8")
        self.assertEqual(
            sha256(manifest_encoded).hexdigest(),
            stop_b["manifest_admission"]["registered_sha256"],
        )

        checker = stop_b["checker_result"]
        checker_encoded = builder._compact_json(checker).encode("utf-8")
        self.assertEqual(
            sha256(checker_encoded).hexdigest(),
            "0d644121840591cd4303fbda99d94cd887836b001d3993bd9d284bb3c0366c80",
        )
        self.assertEqual(
            len(checker_encoded),
            55_566,
        )
        common = checker["observation_evidence"]["common_observation"]
        common_encoded = builder._compact_json(common).encode("utf-8")
        self.assertEqual(
            sha256(common_encoded).hexdigest(),
            "742e6395bb21221fcac070975cbe9505d49d0c75f826289984288776836aa7dc",
        )
        self.assertEqual(
            len(common_encoded),
            53_279,
        )

    def test_full_artifact_contains_history_checker_and_terminal_B(self) -> None:
        self.assertEqual(
            self.full["historical_rounds_13_through_15"],
            list(builder.ROUND13_THROUGH_15_IMMUTABLE_HISTORY),
        )
        checker = self.full["g_local_v1"]["checker_result"]
        self.assertTrue(checker["valid"])
        self.assertTrue(checker["stop_B"])
        self.assertTrue(checker["observations_equal"])
        self.assertTrue(all(checker["component_equality"].values()))
        self.assertEqual(
            {
                key: checker[key]
                for key in (
                    "Obs_G_structural_evaluations",
                    "new_v5_candidate_evaluation_calls",
                    "new_global_or_A_block_H1_queries",
                    "new_population_queries",
                )
            },
            {
                "Obs_G_structural_evaluations": 2,
                "new_v5_candidate_evaluation_calls": 0,
                "new_global_or_A_block_H1_queries": 0,
                "new_population_queries": 0,
            },
        )
        terminal = self.full["terminal"]
        self.assertEqual(terminal["kind"], "B")
        self.assertFalse(terminal["task_complete"])
        self.assertFalse(terminal["stop_condition_A_completion"])
        self.assertTrue(
            terminal["stop_condition_B_G_local_v1_two_point_separation"]
        )
        self.assertFalse(terminal["stop_condition_B_finite_exhaustion"])
        self.assertFalse(
            terminal["stop_condition_C_two_valid_same_blocker_no_progress"]
        )
        self.assertTrue(terminal["issue_remains_open_until_non_draft_PR_merge"])
        self.assertTrue(terminal["prd_retained_until_completion_closeout"])
        self.assertTrue(terminal["grammar_relative"])
        self.assertFalse(terminal["absolute_impossibility_claim"])
        self.assertEqual(
            terminal["result_provenance"],
            builder.STOP_B_RESULT_PROVENANCE,
        )
        self.assertEqual(
            terminal["G107_sync_provenance"],
            list(builder.G107_STOP_B_SYNC_PROVENANCE),
        )

    def test_summary_is_deterministic_bounded_and_references_full(self) -> None:
        self.assertEqual(self.summary, self.summary_again)
        self.assertEqual(builder.render_json(self.full), self.full_before_summary)
        full_encoded = self.full_rendered.encode("utf-8")
        self.assertEqual(
            self.summary["full_results"]["canonical_sha256"],
            sha256(full_encoded).hexdigest(),
        )
        self.assertEqual(
            self.summary["full_results"]["canonical_bytes"],
            len(full_encoded),
        )
        self.assertLess(len(self.summary_rendered.encode("utf-8")), 100_000)
        self.assertNotIn(
            "common_observation",
            self.summary["stop_B"]["observation_evidence"],
        )
        self.assertEqual(
            self.summary["stop_B"]["component_equality"],
            self.full["g_local_v1"]["checker_result"]["component_equality"],
        )
        self.assertEqual(
            self.summary["stop_B"]["result_provenance"],
            builder.STOP_B_RESULT_PROVENANCE,
        )

    def test_fail_closed_admissions_reject_hash_and_history_drift(self) -> None:
        checker = deepcopy(self.full["g_local_v1"]["checker_result"])
        checker["new_population_queries"] = 1
        with self.assertRaises(AssertionError):
            builder._admit_checker_result(checker)

        manifest = deepcopy(self.full["g_local_v1"]["preregistration_manifest"])
        manifest["checker_executed"] = True
        with self.assertRaises(AssertionError):
            builder._admit_manifest(manifest)

        with patch.object(
            builder.historical_source,
            "ROUND15_PARENT_ROUND14_CANONICAL_BYTES",
            22_819,
        ):
            with self.assertRaises(AssertionError):
                builder._admit_historical_rounds()

        parent = self.full["immutable_parent_through_round12"]
        with patch.object(
            builder.historical_source,
            "ROUND13_PARENT_ROUND12_PAYLOAD_SHA256",
            "d9ab928190491610ff1e394fb16fb4e132f117374a317505fbd2025ab5a09f90",
        ):
            with self.assertRaises(AssertionError):
                builder._admit_parent_relation(
                    parent["full_report"],
                    parent["admission"]["full"],
                    parent["admission"]["summary"],
                )

    def test_cli_writes_exact_full_and_summary_bytes_without_rebuilding(self) -> None:
        with TemporaryDirectory() as temporary:
            full_path = Path(temporary) / "full.json"
            summary_path = Path(temporary) / "summary.json"
            with (
                patch.object(
                    builder,
                    "stop_b_results_report",
                    return_value=self.full,
                ) as full_builder,
                patch.object(
                    builder,
                    "stop_b_results_summary",
                    return_value=self.summary,
                ) as summary_builder,
                patch.object(
                    sys,
                    "argv",
                    [
                        "build_stop_b_results.py",
                        "--output",
                        str(full_path),
                        "--summary-output",
                        str(summary_path),
                    ],
                ),
            ):
                self.assertEqual(builder.main(), 0)
            full_builder.assert_called_once_with()
            summary_builder.assert_called_once_with(self.full)
            self.assertEqual(
                full_path.read_bytes(),
                self.full_rendered.encode("utf-8"),
            )
            self.assertEqual(
                summary_path.read_bytes(),
                self.summary_rendered.encode("utf-8"),
            )

    def test_committed_summary_matches_the_canonical_projection(self) -> None:
        committed = (HERE / "results-stop-b-summary.json").read_bytes()
        self.assertEqual(committed, self.summary_rendered.encode("utf-8"))
        self.assertEqual(json.loads(committed), self.summary)


if __name__ == "__main__":
    unittest.main()
