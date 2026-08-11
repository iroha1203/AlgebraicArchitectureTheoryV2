#!/usr/bin/env python3
"""Pure permanent-contract tests for the structural ``G_local-v1`` packet.

These tests inspect literals, source, and the pure contract only.  They do not
call the observation evaluator, the Stop-B checker, a witness constructor, an
H1 routine, a v5 candidate/terminal routine, or a population/report query.
"""

from __future__ import annotations

import ast
from copy import deepcopy
from hashlib import sha256
import inspect
import json
from pathlib import Path
import unittest
from unittest.mock import patch

import g_local_v1 as structural
import g_local_v1_stop_b as stop_b


HERE = Path(__file__).resolve().parent
HISTORICAL_EXECUTION_LITERAL = {
    "role": "opaque-git-and-issue-history-provenance",
    "git_commit": "ded12203d2f95fa8f83aadfd3a1e453f6e7efa06",
    "preregistration": {
        "issue_comment": 5245279192,
        "manifest_sha256": (
            "32e5db03f8f66b091b2594954bd121e2c97c5bfb70fb049c50cd97a070b59969"
        ),
        "manifest_canonical_bytes": 311_163,
    },
    "result": {
        "issue_comment": 5245347326,
        "checker_sha256": (
            "0d644121840591cd4303fbda99d94cd887836b001d3993bd9d284bb3c0366c80"
        ),
        "checker_canonical_bytes": 55_566,
        "common_observation_sha256": (
            "742e6395bb21221fcac070975cbe9505d49d0c75f826289984288776836aa7dc"
        ),
        "common_observation_canonical_bytes": 53_279,
    },
    "old_manifest_reconstructed_from_current_source": False,
    "old_checker_reconstructed_from_current_source": False,
}


def _compact(value: object) -> str:
    return json.dumps(
        value,
        ensure_ascii=True,
        sort_keys=True,
        separators=(",", ":"),
    )


def _all_root_rows(record: dict[str, object]) -> list[dict[str, object]]:
    return record["rooted_ball_histogram"]


def _root_labels(record: dict[str, object]) -> list[dict[str, object]]:
    return [row["ball"]["root_label"] for row in _all_root_rows(record)]


class GLocalV1PermanentContractTests(unittest.TestCase):
    def test_historical_execution_and_round15_ledger_are_exact_literals(
        self,
    ) -> None:
        self.assertEqual(
            stop_b.G_LOCAL_V1_HISTORICAL_EXECUTION,
            HISTORICAL_EXECUTION_LITERAL,
        )

        ledger = stop_b.ROUND15_LABEL_LEDGER
        self.assertEqual(ledger["preregistration_issue_comment"], 5235347217)
        self.assertEqual(
            stop_b.ROUND15_PREREGISTRATION_CREATED_AT,
            "2026-08-10T02:51:13Z",
        )
        self.assertEqual(
            stop_b.ROUND15_PREREGISTRATION_UPDATED_AT,
            "2026-08-10T02:51:13Z",
        )
        self.assertEqual(
            stop_b.ROUND15_REGISTERED_MANIFEST_SHA256,
            "e5f2d6630ee2f37de409f5e2c0757eed17b24509ca3cd3f7d924c130b6219c3b",
        )
        contract = stop_b.g_local_v1_permanent_contract_manifest()
        self.assertEqual(
            contract["immutable_round15_label_ledger"]["sha256"],
            "2e7d95c35bb7490eda4d6fcd6a193bfde6122ddbc6e314bc2a52ed3f5c1828a0",
        )
        self.assertEqual(
            contract["round15_immutable_ledger_provenance"]["sha256"],
            "e5f2d6630ee2f37de409f5e2c0757eed17b24509ca3cd3f7d924c130b6219c3b",
        )
        self.assertNotEqual(
            contract["immutable_round15_label_ledger"]["sha256"],
            contract["round15_immutable_ledger_provenance"]["sha256"],
        )
        self.assertEqual(
            ledger["result_provenance"],
            {
                "issue_comment": 5235636358,
                "created_at": "2026-08-10T03:46:15Z",
                "updated_at": "2026-08-10T03:46:15Z",
                "canonical_payload_sha256": (
                    "21b59632026d5ec0f104700f26808a8455e2ca607802a108"
                    "c6934f68e8911969"
                ),
                "canonical_bytes": 97_792,
                "serialization": {
                    "encoding": "UTF-8",
                    "ensure_ascii": False,
                    "indent": 2,
                    "sort_keys": True,
                    "trailing_newline": True,
                },
            },
        )
        literal_labels = {
            row["fixture"]: (row["field_path"], row["uniform"])
            for row in ledger["labels"]
        }
        self.assertEqual(
            literal_labels,
            {
                "TERNARY-CYCLE-3": (
                    "exact_verification.fixtures[name=\"TERNARY-CYCLE-3\"]"
                    ".uniform",
                    True,
                ),
                "TERNARY-CYCLE-6": (
                    "exact_verification.fixtures[name=\"TERNARY-CYCLE-6\"]"
                    ".uniform",
                    False,
                ),
            },
        )
        projection_rows = {
            row["fixture"]: (
                row["registered_projection_source"],
                row["registered_projection_value"],
            )
            for row in ledger["labels"]
        }
        self.assertEqual(
            projection_rows,
            {
                "TERNARY-CYCLE-3": (
                    "round15_preregistration_manifest.fixtures[name=\""
                    "TERNARY-CYCLE-3\"].name_free_semantic_sha256",
                    (
                        "452517a5dd3df09eea96f4de0c0b737f274384c239267aeba"
                        "2d5ba06fda616a2"
                    ),
                ),
                "TERNARY-CYCLE-6": (
                    "round15_preregistration_manifest.fixtures[name=\""
                    "TERNARY-CYCLE-6\"].name_free_semantic_sha256",
                    (
                        "0e92de476cd0af4dbeb80290afff463354da87c01c4548bab"
                        "5d7806927d1d180"
                    ),
                ),
            },
        )
        self.assertIs(ledger["caller_supplied_labels_permitted"], False)

    def test_witness_inputs_are_name_free_exact_literals(self) -> None:
        expected_digests = {
            "TERNARY-CYCLE-3": (
                "452517a5dd3df09eea96f4de0c0b737f274384c239267aeba2d5ba06"
                "fda616a2"
            ),
            "TERNARY-CYCLE-6": (
                "0e92de476cd0af4dbeb80290afff463354da87c01c4548bab5d780692"
                "7d1d180"
            ),
        }
        self.assertEqual(stop_b.G_LOCAL_V1_WITNESS_INPUT_SHA256, expected_digests)
        for name, payload in stop_b.G_LOCAL_V1_WITNESS_INPUTS.items():
            self.assertNotIn("name", payload)
            self.assertEqual(
                sha256(_compact(payload).encode("utf-8")).hexdigest(),
                expected_digests[name],
            )
            self.assertEqual(payload["targets"]["coarse_count"], 2)
            self.assertEqual(payload["targets"]["fine_count"], 3)
            self.assertEqual(
                payload["targets"]["canonical_surjective_factor_pi"],
                [0, 0, 1],
            )
            self.assertEqual(payload["coarse"]["chart_supports"], [[0], [0, 1]])
            self.assertEqual(payload["fine"]["chart_supports"], [[0, 1], [2]])
            self.assertEqual(payload["morphism"]["vertex_map"], [0, 1])
            self.assertNotIn(None, payload["morphism"]["edge_map"])
            self.assertNotIn(None, payload["morphism"]["face_map"])

    def test_closed_grammar_registries_and_binary_map_status(self) -> None:
        self.assertEqual(structural.G_LOCAL_V1_SEMANTIC_ID, "G_local-v1")
        self.assertEqual(
            structural.G_LOCAL_V1_PACKET_KIND_REGISTRY,
            (
                "v4-coarse",
                "v4-fine-only",
                "coordinate-dependency",
                "closed-doubled-cycle",
            ),
        )
        self.assertEqual(
            structural.G_LOCAL_V1_FLAG_REGISTRY,
            ("critical", "guard", "port", "bridge", "self-loop", "FaceTwin"),
        )
        self.assertEqual(
            structural.G_LOCAL_V1_MAP_STATUS_REGISTRY,
            ("None", "mapped"),
        )
        self.assertEqual(
            structural.G_LOCAL_V1_CELL_TYPE_REGISTRY,
            ("chart", "vertex", "edge", "face"),
        )
        spec = structural.G_LOCAL_V1_SPEC.splitlines()
        prefixes = [line.split(":", 1)[0] for line in spec]
        self.assertEqual(len(prefixes), len(set(prefixes)))
        self.assertIn(
            "map-status:fine chart and vertex are mapped, fine edge and face use actual None or mapped, and every coarse root is canonical mapped; no third value exists",
            spec,
        )
        self.assertIn(
            "chart-role:each retained incidence vertex v has exactly one chart-role c_v and exactly one chart-at edge c_v--v; charts have no direct edge or face incidence",
            spec,
        )
        self.assertIn(
            "faces:each actual member of a retained FaceTwin class is a separate face root and only the FaceTwin flag records class multiplicity at least two",
            spec,
        )

    def test_all_path_packet_union_overlap_control_is_literal(self) -> None:
        self.assertEqual(
            structural.G_LOCAL_V1_TRACE_UNION_OVERLAP_CONTROL,
            {
                "kind": "all-path-packet-kind-union-overlap-control",
                "coarse": {
                    "vertices": 1,
                    "edges": ((0, 0),),
                    "faces": ((0, 0, 0),),
                    "chart_supports": ((0,),),
                },
                "fine": {
                    "vertices": 1,
                    "edges": ((0, 0),),
                    "faces": ((0, 0, 0),),
                    "chart_supports": ((0,),),
                },
                "morphism": {
                    "vertex_map": (0,),
                    "edge_map": (0,),
                    "face_map": (0,),
                },
                "targets": {"coarse": 1, "fine": 1, "pi": (0,)},
                "same_terminal_cell_key": ((), (), (), ()),
                "distinct_path_packet_kinds": (
                    "v4-coarse",
                    "coordinate-dependency",
                ),
                "expected_union": ("coordinate-dependency", "v4-coarse"),
                "lexicographic_single_trace_is_insufficient": True,
            },
        )
        source = (HERE / "g_local_v1.py").read_text(encoding="utf-8")
        tree = ast.parse(source)
        functions = {
            node.name: node
            for node in tree.body
            if isinstance(node, ast.FunctionDef)
        }
        union_source = ast.get_source_segment(
            source,
            functions["_g_all_v5_trace_packet_kinds"],
        )
        scope_source = ast.get_source_segment(source, functions["_g_scope_record"])
        self.assertIn("packets = _v5_packet_variants", union_source)
        self.assertIn("packet_kinds.add(packet.kind)", union_source)
        self.assertIn("_apply_v5_packet", union_source)
        self.assertIn("seen.add(state.cell_key)", union_source)
        self.assertIn("_g_all_v5_trace_packet_kinds(scope)", scope_source)
        self.assertNotIn("state.trace", scope_source)

    def test_hand_expected_observation_is_literal_and_component_complete(self) -> None:
        expected = stop_b.G_LOCAL_V1_EXPECTED_COMMON_OBS
        self.assertEqual(
            expected["aggregate_C0_through_C6"],
            [False, False, False, True, False, True, True],
        )
        self.assertEqual(
            expected["whole"]["conditions"],
            {"C0*": False, "C5*": True, "C6*": True},
        )
        self.assertEqual(expected["whole"]["packet_kind_union"], [])
        self.assertEqual(len(expected["A_record_histogram"]), 3)
        self.assertTrue(
            all(row["count"] == 1 for row in expected["A_record_histogram"])
        )
        condition_multiset = sorted(
            (
                _compact(row["record"]["conditions"])
                for row in expected["A_record_histogram"]
            )
        )
        self.assertEqual(
            condition_multiset,
            sorted(
                (
                    _compact(
                        {"C1*": False, "C2*": False, "C3*": True, "C4*": False}
                    ),
                    _compact(
                        {"C1*": True, "C2*": True, "C3*": True, "C4*": True}
                    ),
                    _compact(
                        {"C1*": True, "C2*": True, "C3*": True, "C4*": True}
                    ),
                )
            ),
        )
        for record in [expected["whole"]] + [
            row["record"] for row in expected["A_record_histogram"]
        ]:
            self.assertEqual(record["packet_kind_union"], [])
            for label in _root_labels(record):
                self.assertEqual(label["map_status"], "mapped")
                self.assertEqual(
                    set(label["flags"]),
                    set(structural.G_LOCAL_V1_FLAG_REGISTRY),
                )

        whole_counts = {
            (side, cell_type): sum(
                row["count"]
                for row in _all_root_rows(expected["whole"])
                if row["ball"]["root_label"]["side"] == side
                and row["ball"]["root_label"]["cell_type"] == cell_type
            )
            for side in ("coarse", "fine")
            for cell_type in ("chart", "vertex", "edge", "face")
        }
        self.assertEqual(
            whole_counts,
            {
                ("coarse", "chart"): 2,
                ("coarse", "vertex"): 2,
                ("coarse", "edge"): 3,
                ("coarse", "face"): 2,
                ("fine", "chart"): 2,
                ("fine", "vertex"): 2,
                ("fine", "edge"): 3,
                ("fine", "face"): 2,
            },
        )
        self.assertIs(
            stop_b.G_LOCAL_V1_HAND_EXPECTATION[
                "generated_from_engine_observation"
            ],
            False,
        )

    def test_hand_flags_are_exact_for_every_root_domain(self) -> None:
        labels = _root_labels(stop_b.G_LOCAL_V1_EXPECTED_COMMON_OBS["whole"])
        for label in labels:
            true_flags = {
                flag for flag, value in label["flags"].items() if value
            }
            domain = (label["side"], label["cell_type"])
            expected = {
                ("coarse", "chart"): set(),
                ("fine", "chart"): set(),
                ("coarse", "vertex"): {"critical"},
                ("fine", "vertex"): {"critical", "port"},
                ("coarse", "edge"): {"critical", "guard", "self-loop"},
                ("fine", "edge"): {"critical", "self-loop"},
                ("coarse", "face"): set(),
                ("fine", "face"): set(),
            }[domain]
            self.assertEqual(true_flags, expected)

    def test_hand_outer_histograms_match_anchor_neutral_scope_partition(self) -> None:
        records = [row["record"] for row in stop_b.G_LOCAL_V1_EXPECTED_COMMON_OBS[
            "A_record_histogram"
        ]]
        a0 = next(record for record in records if not record["conditions"]["C1*"])
        all_true = [record for record in records if record["conditions"]["C1*"]]
        self.assertEqual(len(all_true), 2)

        fine_a0_labels = [
            label for label in _root_labels(a0) if label["side"] == "fine"
        ]
        self.assertEqual(
            sorted(label["cell_type"] for label in fine_a0_labels),
            ["chart", "edge", "vertex"],
        )
        self.assertTrue(
            all(label["support"] == [0, 1] for label in fine_a0_labels)
        )
        neutral_only = next(
            record
            for record in all_true
            if all(
                label["support"] in ([1], [2])
                for label in _root_labels(record)
            )
        )
        self.assertFalse(
            any(
                label["support"] in ([0], [0, 1])
                and label["pi_image"] == [0]
                for label in _root_labels(neutral_only)
            )
        )

    def test_independent_hand_controls_detect_every_registered_change(self) -> None:
        clip2 = lambda value: min(value, 2)
        self.assertNotEqual(clip2(1), clip2(2))
        self.assertEqual(clip2(2), clip2(3))
        self.assertEqual(clip2(3), clip2(6))

        baseline = stop_b.G_LOCAL_V1_EXPECTED_COMMON_OBS
        mutations: list[dict[str, object]] = []

        def mutate_label(
            side: str,
            cell_type: str,
            field: str,
            value: object,
        ) -> None:
            changed = deepcopy(baseline)
            for row in changed["whole"]["rooted_ball_histogram"]:
                label = row["ball"]["root_label"]
                if label["side"] == side and label["cell_type"] == cell_type:
                    label[field] = value
                    break
            else:
                self.fail("hand control could not find its root domain")
            mutations.append(changed)

        mutate_label("fine", "edge", "map_status", "None")
        mutate_label("fine", "face", "map_status", "None")
        mutate_label("coarse", "chart", "support", [99])
        for side, cell_type, flag in (
            ("coarse", "face", "FaceTwin"),
            ("coarse", "edge", "bridge"),
            ("coarse", "edge", "guard"),
            ("fine", "vertex", "port"),
        ):
            changed = deepcopy(baseline)
            for row in changed["whole"]["rooted_ball_histogram"]:
                label = row["ball"]["root_label"]
                flags = label["flags"]
                if label["side"] == side and label["cell_type"] == cell_type:
                    flags[flag] = not flags[flag]
                    break
            mutations.append(changed)
        packet_positive = deepcopy(baseline)
        packet_positive["whole"]["packet_kind_union"] = ["v4-coarse"]
        mutations.append(packet_positive)
        nonloop_neighbor_split = deepcopy(baseline)
        for row in nonloop_neighbor_split["whole"]["rooted_ball_histogram"]:
            label = row["ball"]["root_label"]
            if label["cell_type"] == "edge" and label["flags"]["self-loop"]:
                label["flags"]["self-loop"] = False
                label["flags"]["bridge"] = True
                row["ball"]["neighbor_descriptors"].append(
                    deepcopy(row["ball"]["neighbor_descriptors"][0])
                )
                break
        mutations.append(nonloop_neighbor_split)
        self.assertEqual(
            len(mutations),
            len(
                stop_b.G_LOCAL_V1_HAND_CONTROL_EXPECTATIONS[
                    "mutations_that_must_change_the_observation"
                ]
            ),
        )
        self.assertTrue(
            all(_compact(changed) != _compact(baseline) for changed in mutations)
        )

    def test_observation_source_has_one_chart_at_and_no_chart_cell_shortcut(self) -> None:
        source = (HERE / "g_local_v1.py").read_text(encoding="utf-8")
        tree = ast.parse(source)
        functions = {
            node.name: node
            for node in tree.body
            if isinstance(node, ast.FunctionDef)
        }
        incidence = functions["_g_terminal_incidence"]
        chart_at_calls = [
            node
            for node in ast.walk(incidence)
            if isinstance(node, ast.Call)
            and isinstance(node.func, ast.Name)
            and node.func.id == "_g_relation"
            and node.args
            and isinstance(node.args[0], ast.Constant)
            and node.args[0].value == "chart-at"
        ]
        self.assertEqual(len(chart_at_calls), 1)
        incidence_source = ast.get_source_segment(source, incidence)
        self.assertIn("chart,\n                incidence_vertex", incidence_source)
        self.assertNotIn("chart,\n                    edge_key", incidence_source)
        self.assertNotIn("chart,\n                    face_key", incidence_source)

    def test_observation_reachable_source_has_no_oracle_or_ledger_dependency(self) -> None:
        source = (HERE / "g_local_v1.py").read_text(encoding="utf-8")
        tree = ast.parse(source)
        closure = stop_b._function_closure(
            tree,
            structural.G_LOCAL_V1_LOCAL_SOURCE_ENTRYPOINTS,
        )
        functions = stop_b._function_definitions(tree)
        identifiers = stop_b._identifier_set(functions[name] for name in closure)
        self.assertTrue(
            set(stop_b.G_LOCAL_V1_FORBIDDEN_REACHABLE_SYMBOLS).isdisjoint(
                identifiers
            )
        )
        imports = [
            alias.name
            for node in tree.body
            if isinstance(node, (ast.Import, ast.ImportFrom))
            for alias in node.names
        ]
        self.assertFalse(any("g_local_v1_stop_b" in name for name in imports))
        self.assertFalse(any("ledger" in name.lower() for name in imports))
        self.assertNotIn("uniform", identifiers)
        self.assertNotIn("result_provenance", identifiers)
        self.assertNotIn("stop_B", identifiers)

    def test_observation_source_erases_cell_and_target_names_statically(self) -> None:
        source = (HERE / "g_local_v1.py").read_text(encoding="utf-8")
        tree = ast.parse(source)
        functions = {
            node.name: node
            for node in tree.body
            if isinstance(node, ast.FunctionDef)
        }
        label_source = ast.get_source_segment(source, functions["_g_cell_label"])
        self.assertNotIn('"cell":', label_source)
        self.assertNotIn('"cell_id":', label_source)
        ball_source = ast.get_source_segment(source, functions["_g_rooted_ball"])
        self.assertNotIn('"root": root', ball_source)
        observe_source = ast.get_source_segment(
            source,
            functions["observe_g_local_v1"],
        )
        self.assertNotIn("comparison.name", observe_source)
        self.assertNotIn("coarse_targets_A", observe_source)
        self.assertIn("_g_pi_preserving_relabels", observe_source)
        self.assertIn("min(canonical_candidates)", observe_source)

    def test_import_bindings_and_rebindings_are_independently_ast_fixed(self) -> None:
        def import_map(tree: ast.Module) -> dict[str, dict[str, str]]:
            result: dict[str, dict[str, str]] = {}
            for node in tree.body:
                if isinstance(node, ast.ImportFrom) and node.level == 0:
                    for alias in node.names:
                        result.setdefault(node.module or "", {})[alias.name] = (
                            alias.asname or alias.name
                        )
                elif isinstance(node, ast.Import):
                    for alias in node.names:
                        result.setdefault(alias.name, {})[alias.name] = (
                            alias.asname or alias.name.split(".")[0]
                        )
            return result

        expected_g_r2 = {
            "ReducedSide": "ReducedSide",
            "ScopedComparison": "ScopedComparison",
            "V5CollapseState": "V5CollapseState",
            "_apply_v5_packet": "_apply_v5_packet",
            "_a_scope": "_a_scope",
            "_active_fine_vertices": "_active_fine_vertices",
            "_c0": "_c0",
            "_c1": "_c1",
            "_c2": "_c2",
            "_c3": "_c3",
            "_c4": "_c4",
            "_face_classes": "_face_classes",
            "_path_without_edge": "_path_without_edge",
            "_v4_c5_c6": "_v4_c5_c6",
            "_v5_packet_variants": "_v5_packet_variants",
            "_v5_terminal_reductions": "_v5_terminal_reductions",
        }
        trees = {
            filename: ast.parse((HERE / filename).read_text(encoding="utf-8"))
            for filename in (
                "g_local_v1.py",
                "g_local_v1_stop_b.py",
                "r2_hunt.py",
                "necessity_map.py",
            )
        }
        maps = {name: import_map(tree) for name, tree in trees.items()}
        self.assertEqual(
            maps["g_local_v1.py"]["necessity_map"],
            {
                "UniformComparison": "UniformComparison",
                "nonempty_subsets": "nonempty_subsets",
            },
        )
        self.assertEqual(maps["g_local_v1.py"]["r2_hunt"], expected_g_r2)
        self.assertEqual(
            maps["g_local_v1_stop_b.py"]["g_local_v1"],
            {"g_local_v1": "structural"},
        )
        self.assertEqual(
            maps["g_local_v1_stop_b.py"]["necessity_map"],
            {"necessity_map": "base_structural"},
        )
        self.assertEqual(
            maps["g_local_v1_stop_b.py"]["r2_hunt"],
            {"r2_hunt": "r2_structural"},
        )
        self.assertEqual(
            maps["necessity_map.py"]["fractions"],
            {"Fraction": "Fraction"},
        )
        for name in (
            "Matrix",
            "Nerve",
            "NerveMorphism",
            "UniformComparison",
            "derived_cell_supports",
            "nonempty_subsets",
        ):
            self.assertEqual(maps["r2_hunt.py"]["necessity_map"][name], name)

        for filename, tree in trees.items():
            imported = {
                bound
                for bindings in maps[filename].values()
                for bound in bindings.values()
            }
            other_top_level = {
                node.name
                for node in tree.body
                if isinstance(node, (ast.FunctionDef, ast.ClassDef))
            }
            for node in tree.body:
                if isinstance(node, (ast.Assign, ast.AnnAssign)):
                    targets = (
                        node.targets
                        if isinstance(node, ast.Assign)
                        else (node.target,)
                    )
                    other_top_level.update(
                        child.id
                        for target in targets
                        for child in ast.walk(target)
                        if isinstance(child, ast.Name)
                    )
            self.assertTrue(imported.isdisjoint(other_top_level), filename)

        base_assignments = [
            node
            for node in trees["necessity_map.py"].body
            if isinstance(node, ast.Assign)
            and any(
                isinstance(target, ast.Name) and target.id == "Q"
                for target in node.targets
            )
        ]
        self.assertEqual(len(base_assignments), 1)
        self.assertIsInstance(base_assignments[0].value, ast.Name)
        self.assertEqual(base_assignments[0].value.id, "Fraction")

    def test_checker_signature_and_source_are_fail_closed_without_execution(self) -> None:
        signature = inspect.signature(stop_b.check_g_local_v1_stop_b)
        self.assertEqual(tuple(signature.parameters), ())
        source = inspect.getsource(stop_b.check_g_local_v1_stop_b)
        contract_index = source.index("_admit_current_permanent_contract()")
        witness_index = source.index("_admit_witness_structures(contract)")
        observation_index = source.index("structural.observe_g_local_v1")
        hand_index = source.index("_assert_hand_observation_components")
        component_index = source.index("_observation_component_equality")
        history_index = source.index("_admit_historical_observation_bridge")
        ledger_index = source.index("_admit_round15_ledger(contract)")
        self.assertLess(contract_index, witness_index)
        self.assertLess(witness_index, observation_index)
        self.assertLess(observation_index, hand_index)
        self.assertLess(hand_index, component_index)
        self.assertLess(component_index, history_index)
        self.assertLess(history_index, ledger_index)
        self.assertIn("component_equality = _observation_component_equality", source)
        self.assertIn('"component_equality": component_equality', source)
        self.assertIn('"common_observation_sha256": sha256(', source)
        self.assertIn('"common_observation": observations[', source)
        self.assertIn('"historical_execution_provenance":', source)
        self.assertIn('"current_permanent_contract_provenance":', source)
        self.assertIn('"historical_bridge": historical_observation_bridge', source)
        self.assertIn('"Obs_G_structural_evaluations": 2', source)
        self.assertIn('"new_v5_candidate_evaluation_calls": 0', source)
        self.assertIn('"new_global_or_A_block_H1_queries": 0', source)
        self.assertIn('"new_population_queries": 0', source)
        witness_source = inspect.getsource(stop_b._admit_witness_structures)
        for fixture_name in (
            "NONFREE-MUTUAL-KILL-SPLIT",
            "WEIGHTED-2",
            "TERNARY-CYCLE-3",
            "TERNARY-CYCLE-6",
            "SINGULAR-PERFECT-MATCH-3",
            "WEIGHTED-ORPHAN-SELFLOOP",
        ):
            self.assertIn(f'"{fixture_name}"', witness_source)
        self.assertIn(
            "tuple(fixture.name for fixture in fixtures) != expected_fixture_domain",
            witness_source,
        )
        tree = ast.parse(source)
        identifiers = stop_b._identifier_set((tree,))
        self.assertNotIn("analyze_h1", identifiers)
        self.assertNotIn("block_analyses", identifiers)
        self.assertNotIn("is_uniform", identifiers)
        self.assertNotIn("v5_candidate_evaluation", identifiers)
        self.assertEqual(
            stop_b.G_LOCAL_V1_PERMANENT_CONTRACT_SHA256,
            "955b75d7f88c2d7e3f7e516cb83928127fed9cbd8d28bb50572b17c49a7531af",
        )
        self.assertEqual(
            stop_b.G_LOCAL_V1_PERMANENT_CONTRACT_MIGRATION_ISSUE_COMMENT,
            5246699114,
        )
        self.assertEqual(
            stop_b.G_LOCAL_V1_PERMANENT_CONTRACT_MIGRATION_CREATED_AT,
            "2026-08-10T22:22:12Z",
        )
        self.assertEqual(
            stop_b.G_LOCAL_V1_PERMANENT_CONTRACT_MIGRATION_UPDATED_AT,
            "2026-08-10T22:22:12Z",
        )
        admission_source = inspect.getsource(
            stop_b._admit_current_permanent_contract
        )
        for field in (
            "G_LOCAL_V1_PERMANENT_CONTRACT_SHA256",
            "G_LOCAL_V1_PERMANENT_CONTRACT_MIGRATION_ISSUE_COMMENT",
            "G_LOCAL_V1_PERMANENT_CONTRACT_MIGRATION_CREATED_AT",
            "G_LOCAL_V1_PERMANENT_CONTRACT_MIGRATION_UPDATED_AT",
        ):
            self.assertIn(field, admission_source)
        unregistered_gate_index = admission_source.index(
            "G_LOCAL_V1_PERMANENT_CONTRACT_SHA256 is None"
        )
        contract_generation_index = admission_source.index(
            "contract = g_local_v1_permanent_contract_manifest()"
        )
        digest_index = admission_source.index(
            "actual_sha = sha256(_compact_json(contract)"
        )
        registered_comparison_index = admission_source.index(
            "actual_sha != G_LOCAL_V1_PERMANENT_CONTRACT_SHA256"
        )
        self.assertLess(unregistered_gate_index, contract_generation_index)
        self.assertLess(contract_generation_index, digest_index)
        self.assertLess(digest_index, registered_comparison_index)
        self.assertNotIn("G_LOCAL_V1_HISTORICAL_EXECUTION", admission_source)
        bridge_source = inspect.getsource(
            stop_b._admit_historical_observation_bridge
        )
        self.assertIn(
            'expected_witness_names = {"TERNARY-CYCLE-3", "TERNARY-CYCLE-6"}',
            bridge_source,
        )
        self.assertIn("set(witness_rows) == expected_witness_names", bridge_source)
        self.assertIn("common_observation_sha256", bridge_source)
        self.assertIn("common_observation_canonical_bytes", bridge_source)
        self.assertNotIn("checker_sha256", bridge_source)
        self.assertNotIn("manifest_sha256", bridge_source)

    def test_unregistered_contract_fails_before_manifest_generation(self) -> None:
        with patch.multiple(
            stop_b,
            G_LOCAL_V1_PERMANENT_CONTRACT_SHA256=None,
            G_LOCAL_V1_PERMANENT_CONTRACT_MIGRATION_ISSUE_COMMENT=None,
            G_LOCAL_V1_PERMANENT_CONTRACT_MIGRATION_CREATED_AT=None,
            G_LOCAL_V1_PERMANENT_CONTRACT_MIGRATION_UPDATED_AT=None,
        ):
            with patch.object(
                stop_b,
                "g_local_v1_permanent_contract_manifest",
            ) as manifest_mock:
                with self.assertRaisesRegex(
                    AssertionError,
                    "permanent contract is not registered",
                ):
                    stop_b._admit_current_permanent_contract()
                manifest_mock.assert_not_called()

    def test_pure_contract_cannot_call_evaluator_fixture_or_oracle(self) -> None:
        forbidden = AssertionError("pure contract crossed dependency boundary")
        patch_targets = (
            "r2_hunt.v5_candidate_evaluation",
            "r2_hunt.v5_immutable_calibration_report",
            "r2_hunt.round13_report",
            "r2_hunt.round14_report",
            "r2_hunt.round15_report",
        )
        managers = [patch(target, side_effect=forbidden) for target in patch_targets]
        entered = []
        try:
            for manager in managers:
                entered.append(manager.__enter__())
            contract = stop_b.g_local_v1_permanent_contract_manifest()
        finally:
            for manager in reversed(managers):
                manager.__exit__(None, None, None)
        self.assertEqual(
            contract["kind"],
            "G-local-v1-permanent-structural-contract-v1",
        )
        self.assertEqual(
            sha256(_compact(contract).encode("utf-8")).hexdigest(),
            "955b75d7f88c2d7e3f7e516cb83928127fed9cbd8d28bb50572b17c49a7531af",
        )
        self.assertIs(contract["current_registration_values_in_contract"], False)
        self.assertEqual(
            contract["current_registration_fields"],
            [
                "G_LOCAL_V1_PERMANENT_CONTRACT_SHA256",
                "G_LOCAL_V1_PERMANENT_CONTRACT_MIGRATION_ISSUE_COMMENT",
                "G_LOCAL_V1_PERMANENT_CONTRACT_MIGRATION_CREATED_AT",
                "G_LOCAL_V1_PERMANENT_CONTRACT_MIGRATION_UPDATED_AT",
            ],
        )
        self.assertEqual(
            contract["contract_serialization"],
            {
                "encoding": "UTF-8",
                "ensure_ascii": True,
                "sort_keys": True,
                "separators": [",", ":"],
                "trailing_newline": False,
                "self_contained_hash": False,
            },
        )
        self.assertIs(contract["checker_executed"], False)
        self.assertIs(contract["observation_executed"], False)
        self.assertIs(contract["contract_contains_its_own_sha256"], False)
        self.assertNotIn("permanent_contract_sha256", contract)

        source = (HERE / "g_local_v1_stop_b.py").read_text(encoding="utf-8")
        tree = ast.parse(source)
        functions = {
            node.name: node
            for node in tree.body
            if isinstance(node, ast.FunctionDef)
        }
        pending = ["g_local_v1_permanent_contract_manifest"]
        reachable: set[str] = set()
        while pending:
            name = pending.pop()
            if name in reachable:
                continue
            reachable.add(name)
            direct = {
                child.func.id
                for child in ast.walk(functions[name])
                if isinstance(child, ast.Call)
                and isinstance(child.func, ast.Name)
            }
            pending.extend(sorted(direct & functions.keys()))
        external_calls = {
            child.func.attr
            for name in reachable
            for child in ast.walk(functions[name])
            if isinstance(child, ast.Call)
            and isinstance(child.func, ast.Attribute)
        }
        self.assertTrue(
            {
                "observe_g_local_v1",
                "serialize_g_local_v1_observation",
                "round15_verification_fixtures",
                "v5_terminal_states",
            }.isdisjoint(external_calls)
        )
        self.assertTrue(
            {
                "check_g_local_v1_stop_b",
                "_admit_current_permanent_contract",
                "_admit_witness_structures",
                "_admit_round15_ledger",
            }.isdisjoint(reachable)
        )
        self.assertEqual(
            contract["dependency_contract"],
            {
                "direction": (
                    "structural-input->Obs_G-serialization->equality-checker<-"
                    "immutable-label-ledger"
                ),
                "contract_calls_observation": False,
                "contract_calls_witness_constructors": False,
                "contract_calls_v5_candidate_or_terminal": False,
                "contract_calls_H1_rank_or_uniformity": False,
                "contract_calls_round13_14_15_report_or_population": False,
                "checker_accepts_caller_labels": False,
                "registered_local_C3_exception_only": True,
                "later_checker_Obs_G_structural_evaluations": 2,
                "later_checker_new_v5_candidate_evaluation_calls": 0,
                "later_checker_new_global_or_A_block_H1_queries": 0,
                "later_checker_new_population_queries": 0,
            },
        )

    def test_contract_binds_exact_source_closures_and_hand_packet(self) -> None:
        contract = stop_b.g_local_v1_permanent_contract_manifest()
        source = contract["source_bundle"]
        g_text = (HERE / "g_local_v1.py").read_text(encoding="utf-8")
        self.assertEqual(
            source["observation_module"]["normalized_full_source"],
            g_text,
        )
        self.assertEqual(
            source["observation_module"]["normalized_full_source_sha256"],
            sha256(g_text.encode("utf-8")).hexdigest(),
        )
        source_normalization = {
            "read_encoding": "UTF-8",
            "newline_normalization": "CRLF-and-CR-to-LF",
            "trailing_newline_preserved": True,
            "hash_input": "normalized-UTF-8-bytes",
        }
        for module_key, filename in (
            ("observation_module", "g_local_v1.py"),
            ("r2_structural_helpers", "r2_hunt.py"),
            ("base_structural_helpers", "necessity_map.py"),
        ):
            normalized = (
                (HERE / filename)
                .read_bytes()
                .decode("utf-8")
                .replace("\r\n", "\n")
                .replace("\r", "\n")
            )
            self.assertEqual(
                source[module_key]["normalization"],
                source_normalization,
            )
            self.assertEqual(
                source[module_key]["normalized_full_source_sha256"],
                sha256(normalized.encode("utf-8")).hexdigest(),
            )
            self.assertEqual(
                source[module_key]["normalized_full_source_bytes"],
                len(normalized.encode("utf-8")),
            )

        checker_text = (
            (HERE / "g_local_v1_stop_b.py")
            .read_bytes()
            .decode("utf-8")
            .replace("\r\n", "\n")
            .replace("\r", "\n")
        )
        registration_fields = (
            "G_LOCAL_V1_PERMANENT_CONTRACT_SHA256",
            "G_LOCAL_V1_PERMANENT_CONTRACT_MIGRATION_ISSUE_COMMENT",
            "G_LOCAL_V1_PERMANENT_CONTRACT_MIGRATION_CREATED_AT",
            "G_LOCAL_V1_PERMANENT_CONTRACT_MIGRATION_UPDATED_AT",
        )

        def rewrite_registration_values(
            text: str,
            values: dict[str, bytes],
        ) -> str:
            encoded = text.encode("utf-8")
            lines = encoded.splitlines(keepends=True)
            tree = ast.parse(text)
            replacements = []
            found: set[str] = set()
            for node in tree.body:
                if not isinstance(node, (ast.Assign, ast.AnnAssign)):
                    continue
                targets = (
                    node.targets
                    if isinstance(node, ast.Assign)
                    else (node.target,)
                )
                selected = [
                    target.id
                    for target in targets
                    if isinstance(target, ast.Name)
                    and target.id in values
                ]
                if not selected or node.value is None:
                    continue
                start = sum(
                    len(line) for line in lines[: node.value.lineno - 1]
                ) + node.value.col_offset
                end = sum(
                    len(line) for line in lines[: node.value.end_lineno - 1]
                ) + node.value.end_col_offset
                replacements.append((start, end, values[selected[0]]))
                found.add(selected[0])
            self.assertEqual(found, set(values))
            self.assertEqual(len(replacements), len(values))
            for start, end, value in sorted(replacements, reverse=True):
                encoded = encoded[:start] + value + encoded[end:]
            return encoded.decode("utf-8")

        canonical_values = {name: b"None" for name in registration_fields}
        checker_normalized = rewrite_registration_values(
            checker_text,
            canonical_values,
        )
        expected_pre_registration_lines = {
            "G_LOCAL_V1_PERMANENT_CONTRACT_SHA256": (
                "G_LOCAL_V1_PERMANENT_CONTRACT_SHA256: str | None = None"
            ),
            "G_LOCAL_V1_PERMANENT_CONTRACT_MIGRATION_ISSUE_COMMENT": (
                "G_LOCAL_V1_PERMANENT_CONTRACT_MIGRATION_ISSUE_COMMENT: "
                "int | None = None"
            ),
            "G_LOCAL_V1_PERMANENT_CONTRACT_MIGRATION_CREATED_AT": (
                "G_LOCAL_V1_PERMANENT_CONTRACT_MIGRATION_CREATED_AT: "
                "str | None = None"
            ),
            "G_LOCAL_V1_PERMANENT_CONTRACT_MIGRATION_UPDATED_AT": (
                "G_LOCAL_V1_PERMANENT_CONTRACT_MIGRATION_UPDATED_AT: "
                "str | None = None"
            ),
        }
        normalized_lines = checker_normalized.splitlines()
        for field, expected_line in expected_pre_registration_lines.items():
            self.assertEqual(
                [
                    line
                    for line in normalized_lines
                    if line.startswith(f"{field}:")
                ],
                [expected_line],
            )
        registered_variant = rewrite_registration_values(
            checker_text,
            {
                registration_fields[0]: b'"registered-sha"',
                registration_fields[1]: b"123456789",
                registration_fields[2]: b'"2026-08-10T19:00:00Z"',
                registration_fields[3]: b'"2026-08-10T19:00:00Z"',
            },
        )
        self.assertEqual(
            checker_normalized,
            rewrite_registration_values(
                registered_variant,
                canonical_values,
            ),
        )
        checker_record = source["checker_module"]
        self.assertEqual(
            checker_record["registration_normalization"],
            {
                "base_normalization": source_normalization,
                "normalized_assignment_fields": registration_fields,
                "canonical_assignment_value": "None",
                "all_other_source_bytes_preserved": True,
            },
        )
        self.assertEqual(
            checker_record["registration_normalized_full_source_sha256"],
            sha256(checker_normalized.encode("utf-8")).hexdigest(),
        )
        self.assertEqual(
            checker_record["registration_normalized_full_source_bytes"],
            len(checker_normalized.encode("utf-8")),
        )
        one_bit_drift = checker_text.replace(
            "Permanent structural contract",
            "Qermanent structural contract",
            1,
        )
        self.assertNotEqual(one_bit_drift, checker_text)
        self.assertNotEqual(
            sha256(
                rewrite_registration_values(
                    one_bit_drift,
                    canonical_values,
                ).encode("utf-8")
            ).hexdigest(),
            checker_record["registration_normalized_full_source_sha256"],
        )
        self.assertEqual(
            source["observation_module"]["entrypoints"],
            list(structural.G_LOCAL_V1_LOCAL_SOURCE_ENTRYPOINTS),
        )
        self.assertEqual(
            source["r2_structural_helpers"]["entrypoints"],
            list(structural.G_LOCAL_V1_R2_STRUCTURAL_ENTRYPOINTS),
        )
        self.assertEqual(
            source["r2_structural_helpers"]["witness_admission"][
                "entrypoints"
            ],
            ["_case_semantic_payload_json", "round15_verification_fixtures"],
        )
        admission_closure = set(
            source["r2_structural_helpers"]["witness_admission"][
                "reachable_function_names"
            ]
        )
        self.assertTrue(
            {
                "_case_semantic_payload_json",
                "round15_verification_fixtures",
                "nonfree_mutual_kill_split_fixture",
                "weighted_2_fixture",
                "ternary_cycle_3_fixture",
                "ternary_cycle_6_fixture",
                "singular_perfect_match_3_fixture",
                "weighted_orphan_selfloop_fixture",
            }
            <= admission_closure
        )
        self.assertEqual(
            source["base_structural_helpers"]["exact_locators"],
            [
                "Matrix.__post_init__",
                "Matrix.__matmul__",
                "Matrix.from_mutable",
                "Matrix.is_zero",
                "Matrix.kernel_basis",
                "Matrix.rank",
                "Matrix.zero",
                "Nerve.__post_init__",
                "Nerve.d0",
                "Nerve.d1",
                "NerveMorphism.__post_init__",
                "UniformComparison.__post_init__",
                "UniformComparison.coarse_edge_supports",
                "UniformComparison.coarse_face_supports",
                "UniformComparison.coordinate_subcomparison",
                "UniformComparison.fine_edge_supports",
                "UniformComparison.fine_face_supports",
                "UniformComparison.summary",
                "derived_cell_supports",
                "nerve_summary",
                "nonempty_subsets",
                "restrict_nerve",
                "supports_summary",
            ],
        )
        literal_base_fields = {
            "Matrix": ("rows", "cols", "entries"),
            "Nerve": ("vertices", "edges", "faces"),
            "NerveMorphism": (
                "coarse",
                "fine",
                "vertex_map",
                "edge_map",
                "face_map",
            ),
            "RestrictedNerve": ("nerve", "vertices", "edges", "faces"),
            "CoordinateSubcomparison": (
                "coarse_targets",
                "fine_targets",
                "coarse",
                "fine",
                "morphism",
            ),
            "UniformComparison": (
                "name",
                "morphism",
                "coarse_target_count",
                "fine_target_count",
                "factor_pi",
                "coarse_chart_supports",
                "fine_chart_supports",
            ),
        }
        base_tree = ast.parse(
            (HERE / "necessity_map.py").read_text(encoding="utf-8")
        )
        base_classes = {
            node.name: node
            for node in base_tree.body
            if isinstance(node, ast.ClassDef)
        }
        independently_extracted = {
            name: tuple(
                child.target.id
                for child in base_classes[name].body
                if isinstance(child, ast.AnnAssign)
                and isinstance(child.target, ast.Name)
            )
            for name in literal_base_fields
        }
        self.assertEqual(independently_extracted, literal_base_fields)
        self.assertEqual(
            source["base_structural_helpers"][
                "registered_dataclass_field_schemas"
            ],
            literal_base_fields,
        )
        self.assertEqual(
            source["base_structural_helpers"][
                "extracted_dataclass_field_schemas"
            ],
            literal_base_fields,
        )
        self.assertEqual(
            source["r2_structural_helpers"]["local_C3_exception"]["entrypoint"],
            "_c3",
        )
        self.assertEqual(
            source["r2_structural_helpers"]["local_C3_exception"]["helper"],
            "_local_unmapped_h1_dimension",
        )
        self.assertEqual(
            source["r2_structural_helpers"]["local_C3_exception"][
                "required_direct_r2_structural_symbols"
            ],
            ("Nerve", "d0", "d1"),
        )
        self.assertEqual(
            source["r2_structural_helpers"]["local_C3_exception"][
                "permitted_direct_r2_linear_algebra_symbols"
            ],
            ("kernel_basis", "rank"),
        )
        self.assertEqual(
            source["r2_structural_helpers"]["local_C3_exception"][
                "required_transitive_base_locators"
            ],
            (
                "Matrix.__post_init__",
                "Matrix.__matmul__",
                "Matrix.from_mutable",
                "Matrix.is_zero",
                "Matrix.kernel_basis",
                "Matrix.rank",
                "Matrix.zero",
                "Nerve.__post_init__",
                "Nerve.d0",
                "Nerve.d1",
            ),
        )
        self.assertEqual(
            source["base_structural_helpers"]["module_constants"]["Q"][
                "assignment"
            ]["source"],
            "Q = Fraction\n",
        )
        self.assertEqual(
            source["base_structural_helpers"]["required_import_bindings"],
            {"fractions": {"Fraction": "Fraction"}},
        )
        qualified_descriptors = {
            row["binding"]: row["descriptor_kind"]
            for row in source["base_structural_helpers"][
                "runtime_qualified_method_source_bindings"
            ]
        }
        self.assertEqual(
            {
                binding: kind
                for binding, kind in qualified_descriptors.items()
                if kind == "property"
            },
            {
                "necessity_map.UniformComparison.coarse_edge_supports": (
                    "property"
                ),
                "necessity_map.UniformComparison.coarse_face_supports": (
                    "property"
                ),
                "necessity_map.UniformComparison.fine_edge_supports": (
                    "property"
                ),
                "necessity_map.UniformComparison.fine_face_supports": (
                    "property"
                ),
            },
        )
        self.assertEqual(
            qualified_descriptors["necessity_map.Matrix.zero"],
            "staticmethod",
        )
        self.assertEqual(
            qualified_descriptors["necessity_map.Matrix.from_mutable"],
            "staticmethod",
        )
        runtime_bindings = {
            row["binding"]: (row["module"], row["name"])
            for row in source["runtime_structural_bindings"]
        }
        self.assertEqual(
            runtime_bindings["necessity_map.Q"],
            ("fractions", "Fraction"),
        )
        for r2_name in ("ReducedSide", "ScopedComparison", "V5CollapseState"):
            self.assertEqual(
                runtime_bindings[f"g_local_v1.{r2_name}"],
                ("r2_hunt", r2_name),
            )
        checker_runtime_bindings = {
            row["binding"]
            for row in source["checker_module"][
                "runtime_function_source_bindings"
            ]
        }
        self.assertIn(
            "g_local_v1_stop_b._admit_current_permanent_contract",
            checker_runtime_bindings,
        )
        self.assertIn(
            "g_local_v1_stop_b._admit_historical_observation_bridge",
            checker_runtime_bindings,
        )
        self.assertIn(
            "g_local_v1_stop_b.g_local_v1_permanent_contract_manifest",
            checker_runtime_bindings,
        )
        for module_key in (
            "observation_module",
            "r2_structural_helpers",
            "base_structural_helpers",
            "checker_module",
        ):
            self.assertEqual(
                source[module_key]["top_level_import_rebindings"],
                [],
            )
        self.assertEqual(
            contract["hand_expectation"]["expected_common_observation"],
            stop_b.G_LOCAL_V1_EXPECTED_COMMON_OBS,
        )
        self.assertEqual(
            [
                (
                    row["ledger_key"],
                    row["registered_projection_source"],
                    row["registered_projection_value"],
                )
                for row in contract["witness_inputs"]
            ],
            [
                (
                    "TERNARY-CYCLE-3",
                    "round15_preregistration_manifest.fixtures[name=\""
                    "TERNARY-CYCLE-3\"].name_free_semantic_sha256",
                    (
                        "452517a5dd3df09eea96f4de0c0b737f274384c239267aeba"
                        "2d5ba06fda616a2"
                    ),
                ),
                (
                    "TERNARY-CYCLE-6",
                    "round15_preregistration_manifest.fixtures[name=\""
                    "TERNARY-CYCLE-6\"].name_free_semantic_sha256",
                    (
                        "0e92de476cd0af4dbeb80290afff463354da87c01c4548bab"
                        "5d7806927d1d180"
                    ),
                ),
            ],
        )
        self.assertIs(
            contract["hand_expectation"][
                "engine_observation_called_to_build_expectation"
            ],
            False,
        )
        self.assertEqual(
            contract["round15_immutable_ledger_provenance"],
            {
                "issue_comment": 5235347217,
                "created_at": "2026-08-10T02:51:13Z",
                "updated_at": "2026-08-10T02:51:13Z",
                "sha256": (
                    "e5f2d6630ee2f37de409f5e2c0757eed17b24509ca3cd3f7d"
                    "924c130b6219c3b"
                ),
                "fixture_projection_paths": [
                    (
                        "round15_preregistration_manifest.fixtures[name=\""
                        "TERNARY-CYCLE-3\"].name_free_semantic_sha256"
                    ),
                    (
                        "round15_preregistration_manifest.fixtures[name=\""
                        "TERNARY-CYCLE-6\"].name_free_semantic_sha256"
                    ),
                ],
            },
        )
        self.assertEqual(
            contract["historical_execution_bridge"],
            {
                "record": HISTORICAL_EXECUTION_LITERAL,
                "role": (
                    "opaque history bridge; no current-source reconstruction "
                    "claim"
                ),
                "current_checker_must_match_historical_common_observation": (
                    True
                ),
            },
        )
        self.assertIs(
            contract["historical_execution_bridge"]["record"][
                "old_manifest_reconstructed_from_current_source"
            ],
            False,
        )
        self.assertIs(
            contract["historical_execution_bridge"]["record"][
                "old_checker_reconstructed_from_current_source"
            ],
            False,
        )
        self.assertEqual(
            contract["expected_later_verdict_if_reproduced"],
            "CSTAR-not-expressible-in-G_local-v1",
        )


if __name__ == "__main__":
    unittest.main()
