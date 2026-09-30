#!/usr/bin/env python3
"""Audit the Palomar package before running Comparator.

This checks the closed Comparator schema, Lean source requirements (the module
header on every tracked .lean file, per-file line caps, the toolchain match
with Mathlib), Challenge imports, boundary size and holes, elaboration of both
modules, basic metadata presence, and axioms. Comparator remains the authority
for kernel-level type equality and Palomar remains the authority for the
transitive import closure, Lean's own header parse and protected kernels.
"""

import argparse
import json
import pathlib
import re
import subprocess
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
STANDARD_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}
SOURCE_LINE_CAP = 10_000


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


def physical_lines(raw: str) -> int:
    """Lines as Palomar counts them: LF or CRLF ends a line, an unterminated
    final line counts, and a final newline adds no empty line."""
    return raw.count("\n") + (1 if raw and not raw.endswith("\n") else 0)


def starts_with_module_header(raw: str) -> bool:
    """Whether the first command is `module`, after ordinary comments.

    Module documentation (`/-!`) and doc comments (`/--`) are commands, so
    they must come after the header. Palomar confirms this with Lean's own
    header parser; this mirrors it for comments, whitespace and the keyword.
    """
    i, n = 0, len(raw)
    while i < n:
        if raw[i].isspace():
            i += 1
        elif raw.startswith("--", i):
            end = raw.find("\n", i)
            i = n if end < 0 else end + 1
        elif raw.startswith("/-", i) and not raw.startswith(("/-!", "/--"), i):
            depth, i = 1, i + 2
            while i < n and depth:
                if raw.startswith("/-", i):
                    depth, i = depth + 1, i + 2
                elif raw.startswith("-/", i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
        else:
            break
    return re.match(r"module(\s|$)", raw[i:]) is not None


def check_source_requirements() -> tuple[int, int, str]:
    """Palomar's Lean source requirements and the Mathlib toolchain match."""
    tracked = run("git", "ls-files", "-z", "--", "*.lean").split("\0")
    files = [pathlib.Path(name) for name in tracked if name]
    if not files:
        fail("no tracked .lean files found")
    longest = 0
    for path in files:
        if path.is_symlink():
            fail(f"{path} is a symbolic link; Palomar rejects .lean symlinks")
        raw = path.read_text(encoding="utf-8")
        lines = physical_lines(raw)
        if lines > SOURCE_LINE_CAP:
            fail(f"{path} has {lines} lines; the per-file cap is {SOURCE_LINE_CAP}")
        longest = max(longest, lines)
        if path.name != "lakefile.lean" and not starts_with_module_header(raw):
            fail(f"{path} does not start with the `module` header")
    toolchain = pathlib.Path("lean-toolchain").read_text().strip()
    mathlib = pathlib.Path(".lake/packages/mathlib/lean-toolchain")
    if not mathlib.is_file():
        fail(f"{mathlib} not found; build the project first")
    if mathlib.read_text().strip() != toolchain:
        fail(f"lean-toolchain {toolchain!r} differs from Mathlib's "
             f"{mathlib.read_text().strip()!r}")
    return len(files), longest, toolchain


def joined_lines(output: str) -> list[str]:
    result: list[str] = []
    for line in output.splitlines():
        if result and line.startswith(" "):
            result[-1] += " " + line.strip()
        else:
            result.append(line)
    return result


def check_import_closure(module: str) -> int:
    """Inspect the complete loaded import list, including indirect imports.

    check_metadata.py separately checks these dependency checkouts and pins.
    Palomar authenticates and rebuilds the sources in its protected job.
    """
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".lean", prefix="_palomar_imports_",
        dir=".", delete=False
    ) as scratch:
        scratch.write(f"import {module}\nopen Lean\n")
        scratch.write('#eval show CoreM Unit from do\n'
                      '  for name in (← getEnv).header.moduleNames do\n'
                      '    IO.println s!"PALOMAR_IMPORT\\t{name}\\t{← findOLean name}"\n')
        scratch_path = pathlib.Path(scratch.name)
    try:
        output = run("lake", "env", "lean", str(scratch_path))
    finally:
        scratch_path.unlink(missing_ok=True)
    mathlib = json.loads(pathlib.Path(".lake/packages/mathlib/lake-manifest.json").read_text())
    packages = {"mathlib"} | {p["name"] for p in mathlib["packages"]}
    allowed = [(pathlib.Path(run("lean", "--print-prefix").strip()) / "lib/lean").resolve()]
    allowed += [(pathlib.Path(".lake/packages") / p / ".lake/build/lib/lean").resolve()
                for p in packages]
    records = [line.split("\t") for line in output.splitlines()
               if line.startswith("PALOMAR_IMPORT\t")]
    if not records or not any(row[1] == module for row in records):
        fail("Challenge import audit did not report the Challenge")
    for _, name, filename in records:
        if name == module:
            continue
        path = pathlib.Path(filename).resolve()
        if not any(path.is_relative_to(root) for root in allowed):
            fail(f"Challenge imports {name} from outside Lean/Mathlib's dependencies: {path}")
    return len(records) - 1


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--comparator", action="store_true",
                        help="also run the toolchain's Comparator and independent kernels")
    parser.add_argument("--local", action="store_true",
                        help="run Comparator without Linux sandboxing (e.g. on macOS)")
    args = parser.parse_args()
    if args.local and not args.comparator:
        parser.error("--local requires --comparator")
    manifest_path = pathlib.Path("comparator-black-scholes.json")
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
    if not set(manifest["permitted_axioms"]) <= STANDARD_AXIOMS:
        fail("permitted_axioms exceeds Palomar's standard allowlist")
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

    imports = re.findall(r"^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([^\s]+)",
                         raw, re.MULTILINE)
    if not imports:
        fail("found no Challenge imports; the import check would pass vacuously")
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

    source_count, longest, toolchain = check_source_requirements()

    print("=== Palomar package preflight ===")
    print(f"[1/7] PASS: closed Comparator schema; {len(theorems)} theorems, "
          "zero definition holes")
    print(f"[2/7] PASS: all {source_count} tracked .lean files start with the "
          f"`module` header (lakefile.lean exempt), longest {longest} lines; "
          f"toolchain {toolchain} matches Mathlib's")
    print(f"[3/7] PASS: {challenge}: {line_count} lines, {byte_count} bytes; "
          f"{len(imports)} direct imports permitted")
    print("[4/7] Building Challenge and Solution ...")
    run("lake", "build", manifest["challenge_module"],
        manifest["solution_module"])
    print("      PASS: both modules build")
    import_count = check_import_closure(manifest["challenge_module"])
    print(f"      PASS: all {import_count} transitive imports resolve inside "
          "Lean or Mathlib's pinned dependency set")
    print("[5/7] PASS: basic v0.4 metadata presence checks; "
          "run check_metadata.py for Palomar's validator")

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
    print("[6/7] PASS: selected declarations use only permitted axioms")

    if args.comparator:
        print("[7/7] Running the toolchain's Comparator and independent kernels ...",
              flush=True)
        command = ["bash", "scripts/run_comparator.sh"]
        if args.local:
            command.append("--local")
        output = run(*command)
        print(output.rstrip())
        if "Your solution is okay" not in output:
            fail("Comparator did not accept the Challenge/Solution pair")
        print("      PASS: Comparator accepts the Challenge/Solution pair")
    else:
        print("[7/7] SKIPPED: pass --comparator (and --local on macOS); "
              "the preflight cannot see body mismatches without it")
    print("=== PREFLIGHT PASSED ===")
    print("Palomar's protected verification and review remain separate.")


if __name__ == "__main__":
    main()
