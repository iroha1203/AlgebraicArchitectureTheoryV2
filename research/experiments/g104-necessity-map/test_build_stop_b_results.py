#!/usr/bin/env python3
"""Regression tests for the G_local-v1 final Stop-B artifact builder."""

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


def _paths_with_value(
    value: object,
    candidate: object,
    path: tuple[str, ...] = (),
) -> list[tuple[str, ...]]:
    paths: list[tuple[str, ...]] = []
    if candidate == value:
        paths.append(path)
    if isinstance(candidate, dict):
        for key, child in candidate.items():
            paths.extend(_paths_with_value(value, child, path + (str(key),)))
    elif isinstance(candidate, (list, tuple)):
        for index, child in enumerate(candidate):
            paths.extend(_paths_with_value(value, child, path + (str(index),)))
    return paths


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
            "g_local_v1_permanent_contract_manifest",
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

    def test_checker_reconstructs_current_permanent_contract_once(self) -> None:
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
                "_admit_current_permanent_contract",
            ),
            1,
        )
        self.assertEqual(
            direct_calls(
                "_admit_current_permanent_contract",
                "g_local_v1_permanent_contract_manifest",
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

    def test_current_contract_generator_and_hash_constants_are_exact(self) -> None:
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
            builder.CANONICAL_GENERATOR,
            {
                "working_directory": "repository-root",
                "argv": [
                    "python3",
                    (
                        "research/experiments/g104-necessity-map/"
                        "build_stop_b_results.py"
                    ),
                    "--output",
                    "/tmp/g104-necessity-map-stop-b-results.json",
                    "--summary-output",
                    (
                        "research/experiments/g104-necessity-map/"
                        "results-stop-b-summary.json"
                    ),
                ],
            },
        )
        self.assertEqual(
            builder.PERMANENT_CONTRACT_COMPACT_EXPECTED_SHA256,
            "955b75d7f88c2d7e3f7e516cb83928127fed9cbd8d28bb50572b17c49a7531af",
        )
        self.assertEqual(
            builder.PERMANENT_CONTRACT_COMPACT_EXPECTED_BYTES,
            314_821,
        )
        self.assertEqual(
            builder.CHECKER_RESULT_COMPACT_EXPECTED_SHA256,
            "834d97547d037ebe76fea942a95996f2b2a0bdcfe9f14eda73bc450c4ac9ebca",
        )
        self.assertEqual(builder.CHECKER_RESULT_COMPACT_EXPECTED_BYTES, 56_940)
        self.assertEqual(
            builder.COMMON_OBSERVATION_EXPECTED_SHA256,
            "742e6395bb21221fcac070975cbe9505d49d0c75f826289984288776836aa7dc",
        )
        self.assertEqual(builder.COMMON_OBSERVATION_EXPECTED_BYTES, 53_279)
        self.assertEqual(
            builder.PERMANENT_CONTRACT_REGRESSION_PROVENANCE,
            {
                "issue_comment": 5246749681,
                "created_at": "2026-08-10T22:28:47Z",
                "updated_at": "2026-08-10T22:28:47Z",
            },
        )

    def test_cli_requires_an_explicit_output_path(self) -> None:
        with (
            patch.object(builder, "stop_b_results_report") as full_builder,
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
            cls.contract_mock = stack.enter_context(
                patch.object(
                    builder,
                    "g_local_v1_permanent_contract_manifest",
                    wraps=builder.g_local_v1_permanent_contract_manifest,
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

    def test_direct_requests_are_once_and_contract_effective_total_is_two(
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
        self.__class__.contract_mock.assert_called_once_with()
        self.__class__.checker_mock.assert_called_once_with()
        admission = self.full["g_local_v1"]["contract_admission"]
        self.assertEqual(admission["builder_direct_contract_requests"], 1)
        self.assertEqual(
            admission["checker_internal_contract_admission_reconstructions"],
            1,
        )
        self.assertEqual(admission["effective_contract_constructions"], 2)
        for mock in self.__class__.forbidden_mocks.values():
            mock.assert_not_called()

    def test_parent_full_and_summary_are_reproduced_fail_closed(self) -> None:
        parent = self.full["immutable_parent_through_round12"]
        full_text = builder.render_json(parent["full_report"])
        summary_text = builder.render_json(parent["summary_report"])
        self.assertEqual(
            sha256(full_text.encode("utf-8")).hexdigest(),
            "cabfbcae7075280a6d10de3c819c25ca2396a21deaed2099bafdd71daa252306",
        )
        self.assertEqual(
            sha256(summary_text.encode("utf-8")).hexdigest(),
            "afa334056b52938044c0acad9b693a0c437300382b855f32450af5750020caa5",
        )
        self.assertEqual(len(summary_text.encode("utf-8")), 95_410)
        self.assertEqual(
            parent["admission"]["round12_payload_sha256"],
            "c9ab928190491610ff1e394fb16fb4e132f117374a317505fbd2025ab5a09f90",
        )

    def test_contract_checker_and_common_observation_hashes_are_exact(self) -> None:
        stop_b = self.full["g_local_v1"]
        contract = stop_b["permanent_contract_manifest"]
        contract_encoded = builder._compact_json(contract).encode("utf-8")
        self.assertEqual(
            sha256(contract_encoded).hexdigest(),
            "955b75d7f88c2d7e3f7e516cb83928127fed9cbd8d28bb50572b17c49a7531af",
        )
        self.assertEqual(len(contract_encoded), 314_821)
        self.assertEqual(
            stop_b["round15_hash_roles"],
            {
                "registered_manifest_sha256": (
                    "e5f2d6630ee2f37de409f5e2c0757eed17b24509ca3cd3f7d924c130b6219c3b"
                ),
                "label_ledger_sha256": (
                    "2e7d95c35bb7490eda4d6fcd6a193bfde6122ddbc6e314bc2a52ed3f5c1828a0"
                ),
            },
        )
        self.assertEqual(
            self.summary["stop_B"]["round15_hash_roles"],
            stop_b["round15_hash_roles"],
        )

        checker = stop_b["checker_result"]
        checker_encoded = builder._compact_json(checker).encode("utf-8")
        self.assertEqual(
            sha256(checker_encoded).hexdigest(),
            "834d97547d037ebe76fea942a95996f2b2a0bdcfe9f14eda73bc450c4ac9ebca",
        )
        self.assertEqual(len(checker_encoded), 56_940)
        common = checker["observation_evidence"]["common_observation"]
        common_encoded = builder._compact_json(common).encode("utf-8")
        self.assertEqual(
            sha256(common_encoded).hexdigest(),
            "742e6395bb21221fcac070975cbe9505d49d0c75f826289984288776836aa7dc",
        )
        self.assertEqual(len(common_encoded), 53_279)

    def test_full_artifact_is_schema_v2_final_mathematical_terminal(self) -> None:
        self.assertEqual(
            self.full["artifact"],
            "G-104 G_local-v1 final Stop-B result",
        )
        self.assertEqual(self.full["schema_version"], 2)
        self.assertEqual(
            self.full["historical_rounds_13_through_15"],
            list(builder.ROUND13_THROUGH_15_IMMUTABLE_HISTORY),
        )
        checker = self.full["g_local_v1"]["checker_result"]
        self.assertTrue(checker["valid"])
        self.assertTrue(checker["stop_B"])
        self.assertTrue(checker["observations_equal"])
        self.assertTrue(all(checker["component_equality"].values()))
        terminal = self.full["terminal"]
        self.assertEqual(terminal["kind"], "B")
        self.assertEqual(terminal["role"], "final-mathematical-terminal")
        self.assertFalse(terminal["stop_condition_A_completion"])
        self.assertTrue(
            terminal["stop_condition_B_G_local_v1_two_point_separation"]
        )
        self.assertFalse(terminal["stop_condition_B_finite_exhaustion"])
        self.assertFalse(
            terminal["stop_condition_C_two_valid_same_blocker_no_progress"]
        )
        self.assertTrue(terminal["grammar_relative"])
        self.assertFalse(terminal["absolute_impossibility_claim"])
        for lifecycle_key in (
            "task_complete",
            "issue_remains_open_until_non_draft_PR_merge",
            "prd_retained_until_completion_closeout",
            "repository_status",
        ):
            self.assertNotIn(lifecycle_key, terminal)
            self.assertNotIn(lifecycle_key, self.summary["terminal"])
        self.assertNotIn("repository_status", self.summary["full_results"])

    def test_superseded_values_occur_only_as_opaque_history(self) -> None:
        old_values = (
            "32e5db03f8f66b091b2594954bd121e2c97c5bfb70fb049c50cd97a070b5"
            + "9969",
            "0d644121840591cd4303fbda99d94cd887836b001d3993bd9d284bb3c036"
            + "6c80",
            int("52453" + "47326"),
        )
        for value in old_values:
            paths = _paths_with_value(value, self.full)
            self.assertTrue(paths, value)
            for path in paths:
                self.assertIn("historical", ".".join(path), path)
        opaque = self.full["historical_provenance"]
        self.assertEqual(
            opaque["stop_b_execution_and_downstream_sync"]["role"],
            "opaque-git-and-issue-history-provenance",
        )
        self.assertEqual(
            opaque["superseded_execution_bridge"]["role"],
            "opaque history bridge; no current-source reconstruction claim",
        )

    def test_summary_is_deterministic_bounded_and_references_full(self) -> None:
        self.assertEqual(self.summary, self.summary_again)
        self.assertEqual(builder.render_json(self.full), self.full_before_summary)
        self.assertEqual(self.summary["schema_version"], 2)
        self.assertEqual(
            self.summary["artifact"],
            "G-104 G_local-v1 final Stop-B terminal summary",
        )
        self.assertIs(self.summary["stop_B"]["reached"], True)
        full_encoded = self.full_rendered.encode("utf-8")
        self.assertEqual(
            self.summary["full_results"]["canonical_sha256"],
            sha256(full_encoded).hexdigest(),
        )
        self.assertEqual(
            self.summary["full_results"]["canonical_bytes"],
            len(full_encoded),
        )
        self.assertEqual(
            self.summary["full_results"]["canonical_generator"],
            builder.CANONICAL_GENERATOR,
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
            self.summary["stop_B"]["query_counts"],
            self.full["g_local_v1"]["checker_admission"]["query_counts"],
        )
        self.assertEqual(
            self.summary["historical_provenance"],
            self.full["historical_provenance"],
        )

    def test_fail_closed_admissions_reject_hash_and_history_drift(self) -> None:
        contract = deepcopy(
            self.full["g_local_v1"]["permanent_contract_manifest"]
        )
        contract["checker_executed"] = True
        with self.assertRaises(AssertionError):
            builder._admit_permanent_contract(contract)

        original_contract = self.full["g_local_v1"][
            "permanent_contract_manifest"
        ]
        checker = deepcopy(self.full["g_local_v1"]["checker_result"])
        checker["new_population_queries"] = 1
        with self.assertRaises(AssertionError):
            builder._admit_checker_result(checker, original_contract)

        checker = deepcopy(self.full["g_local_v1"]["checker_result"])
        checker["current_permanent_contract_provenance"]["sha256"] = "0" * 64
        with self.assertRaises(AssertionError):
            builder._admit_checker_result(checker, original_contract)

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
