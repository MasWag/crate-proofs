#!/usr/bin/env python3
"""Inspect every emitted Coma target and its nonempty Why3find proof tree."""
import hashlib
import json
import pathlib
import re
import subprocess
import sys
import os

run = pathlib.Path(sys.argv[1]).resolve()
files = [pathlib.Path(x) for x in (run / "generated-targets.txt").read_text().splitlines()]
actual_files = sorted((run / "coma").rglob("*.coma"))
if sorted(files) != actual_files:
    raise SystemExit("Generated target list differs from complete Coma output tree")
if len(files) != len(set(files)):
    raise SystemExit("Duplicate generated target")
exit_lines = [(path, code) for path, code in
              (line.split("\t", 1) for line in
               (run / "target-exits.tsv").read_text().splitlines())]
target_exits_match = ([path for path, _ in exit_lines] == [str(path) for path in files]
                      and all(code == "0" for _, code in exit_lines))


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def tree_ok(node):
    if node is None or not isinstance(node, dict):
        return False, 0
    if "prover" in node:
        return bool(node["prover"]), 1
    children = node.get("children")
    if not isinstance(children, list) or not children:
        return False, 0
    checks = [tree_ok(child) for child in children]
    return all(item[0] for item in checks), sum(item[1] for item in checks)


def unique_pairs(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"Duplicate proof JSON key: {key}")
        result[key] = value
    return result


def reconstruct_roots(coma):
    data = pathlib.Path(os.environ["XDG_DATA_HOME"])
    config = pathlib.Path(os.environ["WHY3CONFIG"])
    library = data / "creusot/share/why3find/packages/creusot"
    result = subprocess.run(["why3", "prove", "-C", str(config), "-L", str(library), str(coma)],
                            check=True, capture_output=True, text=True, timeout=30)
    roots = set()
    module = None
    for line in result.stdout.splitlines():
        header = re.match(r"^theory (\S+)$", line)
        if header:
            module = header.group(1)
        goal = re.match(r"^  goal (\S+)\s*:", line)
        if goal:
            if module is None:
                raise ValueError(f"Goal without theory in {coma}")
            name = f"{module}.{goal.group(1)}"
            if name in roots:
                raise ValueError(f"Duplicate reconstructed root {name} in {coma}")
            roots.add(name)
    if not roots:
        raise ValueError(f"Zero reconstructed root goals in {coma}")
    return roots


def printed_root_name(name):
    """Conservative subset of Why3's why3-printer identifier sanitizer.

    Why3 src/printer/why3printer.ml uses Ident.char_to_alpha for the first
    character and char_to_alnumus thereafter (src/core/ident.ml): apostrophe
    becomes "qt"; ASCII letters, subsequent digits and underscores survive.
    Refuse other spellings rather than approximate printer uniqueness rules.
    """
    if not (re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", name)
            or re.fullmatch(r"vc_[A-Za-z0-9_]+(?:'[0-9]+)+", name)):
        return None
    return name.replace("'", "qt")


def replay_computed_root(coma, module, name, actual_roots):
    """Check that Why3's exact compute_specified step removes this original goal."""
    data = pathlib.Path(os.environ["XDG_DATA_HOME"])
    config = pathlib.Path(os.environ["WHY3CONFIG"])
    library = data / "creusot/share/why3find/packages/creusot"
    base = ["why3", "prove", "-C", str(config), "-L", str(library),
            "-D", "why3", str(coma), "-T", module, "-G", name]
    original = subprocess.run(base, capture_output=True, text=True, timeout=30)
    original_goals = re.findall(r"^\s*goal\s+(\S+)\s*:", original.stdout,
                                re.MULTILINE)
    transformed_command = base + ["-a", "compute_specified"]
    transformed = subprocess.run(transformed_command, capture_output=True,
                                 text=True, timeout=30)
    expected_printed_name = printed_root_name(name)
    same_module_names = [root[len(module) + 1:] for root in actual_roots
                         if root.startswith(module + ".")]
    root_print_map = {root: printed_root_name(root) for root in sorted(same_module_names)}
    printed_names = list(root_print_map.values())
    # -G is Why3's exact namespace lookup (why3prove.ml: ns_find_pr), not a
    # pattern. Also bind its single printed task to an unambiguous original
    # root; a literal "qt" spelling must never alias an apostrophe root.
    identity_ok = (f"{module}.{name}" in actual_roots
                   and expected_printed_name is not None
                   and None not in printed_names
                   and len(set(printed_names)) == len(printed_names)
                   and printed_names.count(expected_printed_name) == 1
                   and original_goals == [expected_printed_name])
    closed = (original.returncode == 0 and identity_ok
              and transformed.returncode == 0 and not transformed.stdout.strip())
    evidence = {
        "target": str(coma.relative_to(run)),
        "root": f"{module}.{name}",
        "original_command": base,
        "original_exit": original.returncode,
        "original_goal_names": original_goals,
        "expected_printed_goal_name": expected_printed_name,
        "original_root_identity_unambiguous": identity_ok,
        "module_root_print_map": root_print_map,
        "module_root_print_map_sha256": hashlib.sha256(
            json.dumps(root_print_map, sort_keys=True).encode()).hexdigest(),
        "printer_identity_source": {
            "why3_revision": "05bf4ddf55cb3042f34c3bc0ed3aff56a226978a",
            "origin": "installed opam switch sources/why3 (read-only inspection)",
            "src/core/ident.ml_sha256": "0ad589919afcd0d066c3142c83ca64129a463c7a45df07b4ac7feea3720c2f8b",
            "src/printer/why3printer.ml_sha256": "83b8dbec2e005cd2d102174b34e6e230d33fde1087dbbda9018459ff3d9419b1",
            "src/tools/why3prove.ml_sha256": "903e9643355c5b67ed628e206022a668d480d7f493a0a483969337061798c70d",
            "rule": "exact ns_find_pr -G lookup; why3 printer sanitizer maps apostrophe to qt; reject noninjective aliases",
        },
        "original_stdout_sha256": hashlib.sha256(original.stdout.encode()).hexdigest(),
        "original_stderr_sha256": hashlib.sha256(original.stderr.encode()).hexdigest(),
        "transformed_command": transformed_command,
        "transformed_exit": transformed.returncode,
        "transformed_stdout_bytes": len(transformed.stdout.encode()),
        "transformed_stdout_sha256": hashlib.sha256(transformed.stdout.encode()).hexdigest(),
        "transformed_stderr_sha256": hashlib.sha256(transformed.stderr.encode()).hexdigest(),
        "closed": closed,
    }
    return closed, evidence


targets = []
computed_replays = []
for coma in files:
    proof = coma.with_suffix("") / "proof.json"
    item = {"target": str(coma.relative_to(run)), "coma_sha256": digest(coma)}
    if not proof.is_file():
        item.update({"proof_json": None, "root_goals": 0, "proved_leaves": 0, "closed": False})
    else:
        data = json.loads(proof.read_text(), object_pairs_hook=unique_pairs)
        roots = [(module, name, tree) for module, goals in data.get("proofs", {}).items()
                 for name, tree in goals.items()]
        session_roots = {f"{module}.{name}" for module, name, _ in roots}
        actual_roots = reconstruct_roots(coma)
        checks = []
        computed_names = []
        for module, name, tree in roots:
            if (isinstance(tree, dict) and tree.get("tactic") == "compute_specified"
                    and tree.get("children") == []):
                closed, evidence = replay_computed_root(coma, module, name, actual_roots)
                computed_replays.append(evidence)
                computed_names.append(f"{module}.{name}")
                checks.append((closed, 0))
            else:
                checks.append(tree_ok(tree))
        target_kind = "body_vc"
        target_vcs = re.findall(r"^goal (vc_\w+):", coma.read_text(), re.MULTILINE)
        bodies = re.findall(r"^let (?:rec )?(\w+) ", coma.read_text(), re.MULTILINE)
        if coma.name.endswith("__refines.coma"):
            declarations = re.findall(r"^goal[ \t]+([^\s:]+)[ \t]*:", coma.read_text(), re.MULTILINE)
            if declarations != ["refines"] or target_vcs or bodies:
                raise ValueError(f"Unexpected trait refinement declarations in {coma}")
            target_kind = "trait_refinement"
            target_vc = "refines"
        else:
            if not target_vcs and not bodies:
                raise ValueError(f"No target VC or body declaration in {coma}")
            target_vc = target_vcs[-1] if target_vcs else f"vc_{bodies[-1]}"
        item.update({"proof_json": str(proof.relative_to(run)),
                     "proof_json_sha256": digest(proof),
                     "root_goals": len(roots),
                     "root_names": sorted(session_roots),
                     "reconstructed_root_names": sorted(actual_roots),
                     "target_kind": target_kind,
                     "target_vc": target_vc,
                     "proved_leaves": sum(n for _, n in checks),
                     "computed_roots": sorted(computed_names),
                     "closed": bool(roots) and session_roots == actual_roots
                         and any(name.endswith(f".{target_vc}") for name in session_roots)
                         and all(ok and (n > 0 or f"{module}.{name}" in computed_names)
                                 for (module, name, _), (ok, n) in zip(roots, checks))})
    targets.append(item)

replay_path = run / "computed-roots-replay.json"
replay_path.write_text(json.dumps(computed_replays, indent=2) + "\n")
status = {
    "compile_exit": int((run / "compile.exit").read_text()),
    "prove_exit": int((run / "prove.exit").read_text()),
    "inputs_match": (run / "inputs-before.sha256").read_bytes()
                    == (run / "inputs-after.sha256").read_bytes(),
    "generated_targets": len(targets),
    "target_exits_match": target_exits_match,
    "root_goals": sum(item["root_goals"] for item in targets),
    "computed_root_goals": len(computed_replays),
    "computed_replay_sha256": digest(replay_path),
    "all_trees_closed": bool(targets) and all(item["closed"] for item in targets),
    "targets": targets,
}
(run / "goal-inventory.json").write_text(json.dumps(status, indent=2) + "\n")
print(f"Generated {status['generated_targets']} targets, {status['root_goals']} root goals; "
      f"all trees closed: {status['all_trees_closed']}")
if (status["compile_exit"] != 0 or not status["inputs_match"]
        or not status["target_exits_match"]
        or not status["all_trees_closed"] or status["prove_exit"] != 0):
    sys.exit(1)
