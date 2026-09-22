#!/usr/bin/env python3
"""Audit the Palomar package before running Comparator.

This checks the closed Comparator schema, direct Challenge imports, boundary
size and holes, elaboration of both modules, metadata presence, and axioms.
Comparator remains the authority for kernel-level type equality and Palomar
remains the authority for the transitive import closure and protected kernels.
"""

import json
import os
import pathlib
import re
import subprocess
import sys
import tempfile

REQUIRED_KEYS = {
    "challenge_module",
    "solution_module",
    "theorem_names",
    "permitted_axioms",
}
OPTIONAL_KEYS = {"definition_names", "enable_nanoda"}
ALLOWED_IMPORT_ROOTS = ("Lean", "Mathlib")
AXIOMS_RE = re.compile(r"'([^']+)' depends on axioms: \[(.*)\]")
NO_AXIOMS_RE = re.compile(r"'([^']+)' does not depend on any axioms")


def fail(message: str) -> None:
    print(f"FAIL: {message}")
    raise SystemExit(1)


def run(*command: str) -> str:
    proc = subprocess.run(command, capture_output=True, text=True)
    output = proc.stdout + proc.stderr
    if proc.returncode:
        print(output.rstrip())
        fail(f"command failed ({proc.returncode}): {' '.join(command)}")
    return output


def module_path(module: str) -> pathlib.Path:
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.]*", module):
        fail(f"invalid Lean module name: {module!r}")
    return pathlib.Path(*module.split(".")).with_suffix(".lean")


def allowed_import(module: str) -> bool:
    return any(module == root or module.startswith(root + ".")
               for root in ALLOWED_IMPORT_ROOTS)


def joined_lines(output: str) -> list[str]:
    result: list[str] = []
    for line in output.splitlines():
        if result and line.startswith(" "):
            result[-1] += " " + line.strip()
        else:
            result.append(line)
    return result


def main() -> None:
    manifest_path = pathlib.Path(
        sys.argv[1] if len(sys.argv) > 1 else "comparator-black-scholes.json"
    )
    if not manifest_path.is_file():
        fail(f"{manifest_path} not found")
    manifest = json.loads(manifest_path.read_text())

    keys = set(manifest)
    missing = REQUIRED_KEYS - keys
    unknown = keys - REQUIRED_KEYS - OPTIONAL_KEYS
    if missing:
        fail(f"Comparator config is missing keys: {sorted(missing)}")
    if unknown:
        fail(f"Comparator config has policy-unknown keys: {sorted(unknown)}")

    theorems = manifest["theorem_names"]
    definitions = manifest.get("definition_names", [])
    if not isinstance(theorems, list) or not theorems:
        fail("theorem_names must be a nonempty list")
    if len(theorems) != len(set(theorems)):
        fail("theorem_names contains duplicates")
    if definitions:
        fail("this publication boundary must not use definition holes")

    challenge = module_path(manifest["challenge_module"])
    solution = module_path(manifest["solution_module"])
    if not challenge.is_file() or not solution.is_file():
        fail(f"missing boundary module: {challenge} or {solution}")

    raw = challenge.read_text()
    line_count = len(raw.splitlines())
    byte_count = len(raw.encode())
    if line_count > 1000 or byte_count > 100 * 1024:
        fail(f"Challenge exceeds hard limit: {line_count} lines, "
             f"{byte_count} bytes")
    if line_count > 300 or byte_count > 32 * 1024:
        print(f"WARNING: Challenge triggers human-audit size warning: "
              f"{line_count} lines, {byte_count} bytes")

    imports = re.findall(r"^import\s+([^\s]+)", raw, re.MULTILINE)
    disallowed = [name for name in imports if not allowed_import(name)]
    if disallowed:
        fail(f"Challenge has disallowed direct imports: {disallowed}")

    sorry_count = len(re.findall(r"\bsorry\b", raw))
    if sorry_count != len(theorems):
        fail(f"Challenge has {sorry_count} sorry tokens for "
             f"{len(theorems)} selected theorems")
    namespaces = re.findall(r"^namespace\s+(\S+)", raw, re.MULTILINE)
    for name in theorems:
        short = name
        for ns in namespaces:
            if name.startswith(ns + "."):
                short = name[len(ns) + 1:]
                break
        if not re.search(rf"\b(?:theorem|lemma)\s+{re.escape(short)}\b", raw):
            fail(f"selected theorem {name!r} is not declared in Challenge")

    metadata = pathlib.Path("formalization.yaml")
    if not metadata.is_file():
        fail("formalization.yaml not found")
    metadata_raw = metadata.read_text()
    if not re.search(r'^version:\s*["\']?v0\.4["\']?\s*$',
                     metadata_raw, re.MULTILINE):
        fail("formalization.yaml is not visibly version v0.4")
    for field in ("description:", "responsible_maintainers:", "arxiv:",
                  "relationship:"):
        if field not in metadata_raw:
            fail(f"formalization.yaml is missing {field}")

    print("=== Palomar package preflight ===")
    print(f"[1/5] PASS: closed Comparator schema; {len(theorems)} theorems, "
          "zero definition holes")
    print(f"[2/5] PASS: {challenge}: {line_count} lines, {byte_count} bytes; "
          "direct imports permitted")
    print("[3/5] Building Challenge and Solution ...")
    run("lake", "build", manifest["challenge_module"],
        manifest["solution_module"])
    print("      PASS: both modules build")
    print("[4/5] PASS: v0.4 metadata has required publication fields")

    all_names = theorems + definitions
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".lean", prefix="_palomar_axioms_",
        dir=".", delete=False
    ) as scratch:
        scratch.write(f"import {manifest['solution_module']}\n")
        scratch.writelines(f"#print axioms {name}\n" for name in all_names)
        scratch_path = pathlib.Path(scratch.name)
    try:
        output = run("lake", "env", "lean", str(scratch_path))
    finally:
        scratch_path.unlink(missing_ok=True)

    seen: dict[str, set[str]] = {}
    for line in joined_lines(output):
        match = AXIOMS_RE.match(line)
        if match:
            seen[match.group(1)] = {
                axiom.strip() for axiom in match.group(2).split(",")
                if axiom.strip()
            }
            continue
        match = NO_AXIOMS_RE.match(line)
        if match:
            seen[match.group(1)] = set()

    permitted = set(manifest["permitted_axioms"])
    for name in all_names:
        if name not in seen:
            fail(f"no axiom report found for {name}")
        unexpected = seen[name] - permitted
        if unexpected:
            fail(f"{name} uses non-permitted axioms: {sorted(unexpected)}")
        print(f"      {name}: {sorted(seen[name])}")
    print("[5/5] PASS: selected declarations use only permitted axioms")

    comparator = os.environ.get("COMPARATOR")
    exporter = os.environ.get("LEAN4EXPORT")
    if comparator and exporter:
        print("[6/6] Running the pinned Comparator (COMPARATOR and LEAN4EXPORT set) ...")
        output = run("bash", "scripts/run_comparator.sh")
        if "Your solution is okay" not in output:
            fail("Comparator did not accept the Challenge/Solution pair")
        print("      PASS: Comparator accepts the Challenge/Solution pair")
    else:
        print("[6/6] SKIPPED: set COMPARATOR and LEAN4EXPORT to run the pinned "
              "Comparator; the preflight cannot see body mismatches without it")
    print("=== PREFLIGHT PASSED ===")
    print("Next release gate: protected Comparator/NanoDa run.")


if __name__ == "__main__":
    main()
