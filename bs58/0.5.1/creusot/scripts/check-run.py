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


def replay_computed_root(coma, module, name):
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
    closed = (original.returncode == 0 and original_goals == [name]
              and transformed.returncode == 0 and not transformed.stdout.strip())
    evidence = {
        "target": str(coma.relative_to(run)),
        "root": f"{module}.{name}",
        "original_command": base,
        "original_exit": original.returncode,
        "original_goal_names": original_goals,
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
                closed, evidence = replay_computed_root(coma, module, name)
                computed_replays.append(evidence)
                computed_names.append(f"{module}.{name}")
                checks.append((closed, 0))
            else:
                checks.append(tree_ok(tree))
        target_vcs = re.findall(r"^goal (vc_\w+):", coma.read_text(), re.MULTILINE)
        bodies = re.findall(r"^let (?:rec )?(\w+) ", coma.read_text(), re.MULTILINE)
        if not target_vcs and not bodies:
            raise ValueError(f"No target VC or body declaration in {coma}")
        target_vc = target_vcs[-1] if target_vcs else f"vc_{bodies[-1]}"
        item.update({"proof_json": str(proof.relative_to(run)),
                     "proof_json_sha256": digest(proof),
                     "root_goals": len(roots),
                     "root_names": sorted(session_roots),
                     "reconstructed_root_names": sorted(actual_roots),
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
