#!/usr/bin/env python3
"""Check local metadata and packaging with a pinned Palomar validator.

Requires Python 3.11+, PyYAML, and a clean PalomarSubmission checkout at the
revision below. This does not submit anything or run Palomar's protected job.
"""

import argparse
import hashlib
from pathlib import Path
import subprocess
import sys

PALOMAR_REV = "a59f25bd8a66bf6faf3a4f4260d412989c0185ea"
# Matches https://www.apache.org/licenses/LICENSE-2.0.txt after whitespace normalization.
APACHE_LICENSE_SHA256 = "c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4"


def git(path: Path, *args: str) -> str:
    return subprocess.check_output(["git", "-C", str(path), *args], text=True).strip()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit("FAIL: " + message)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("palomar_checkout", nargs="?", default=".lake/palomar-submission")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    upstream = Path(args.palomar_checkout).resolve()
    require(git(upstream, "rev-parse", "HEAD") == PALOMAR_REV,
            f"PalomarSubmission must be at {PALOMAR_REV}")
    require(not git(upstream, "status", "--porcelain", "--untracked-files=no"),
            "PalomarSubmission has modified tracked files")
    sys.path.insert(0, str(upstream))
    from scripts import submission_contract as contract, verify_submission as verifier

    metadata = contract.load_formalization_metadata(root / "formalization.yaml")
    require(metadata.get("version") == "v0.4", "metadata must declare v0.4")
    origin = contract.normalized_provenance(metadata)["result_origin"]
    require(origin == "source-based", "Black-Scholes must be classified as source-based")
    verifier.load_comparator_config(root / "comparator-black-scholes.json")
    print("PASS: Palomar metadata validator; source-based provenance; Comparator schema")

    toolchain = (root / "lean-toolchain").read_text().strip()
    verifier.supported_toolchain(toolchain)
    packages = verifier.manifest_packages(root)
    require(bool(packages), "expected pinned Mathlib dependencies")
    verifier.check_mathlib_toolchain(
        root, packages, checkout=root, project_toolchain=toolchain,
        project_toolchain_path="lean-toolchain")
    mathlib = root / ".lake/packages/mathlib"
    authoritative = {p["name"]: p for p in verifier.manifest_packages(mathlib)}
    for package in packages:
        name = package["name"]
        checkout = root / ".lake/packages" / name
        require(git(checkout, "rev-parse", "HEAD") == package["revision"],
                f"{name} checkout differs from its manifest pin")
        require(not git(checkout, "status", "--porcelain", "--untracked-files=no"),
                f"{name} has modified tracked files")
        if name != "mathlib":
            require(name in authoritative and
                    package["revision"] == authoritative[name]["revision"] and
                    package["repository"] == authoritative[name]["repository"],
                    f"{name} does not match Mathlib's dependency manifest")
        verifier.validate_preservable_git_checkout(
            checkout, name, allow_inert_submodules=True)
    print(f"PASS: supported matching toolchains; {len(packages)} exact Git dependency pins")

    verifier.validate_preservable_git_checkout(root, "submission")
    verifier.reject_committed_build_artifacts(root)
    license_path = verifier.repository_license_file(root)
    require(metadata["project"]["license"] == "Apache-2.0" and
            hashlib.sha256(license_path.read_bytes()).hexdigest() == APACHE_LICENSE_SHA256,
            "license changed: recheck its text and metadata against Apache-2.0")
    # Include new review files, which are not yet in the Git index.
    files = subprocess.check_output(
        ["git", "-C", str(root), "ls-files", "--cached", "--others", "--exclude-standard", "-z"]
    ).decode().split("\0")
    for name in filter(None, files):
        path = root / name
        if path.is_file() and path.stat().st_size <= 1024:
            require(not path.read_bytes().startswith(b"version https://git-lfs.github.com/spec/v1"),
                    f"Git LFS pointer: {name}")
    print("PASS: repository packaging and unchanged standard Apache-2.0 license")
    print(f"Validator: PalomarRegistry/PalomarSubmission@{PALOMAR_REV}")
    print("Palomar must still check the submitted commit in its protected environment.")


if __name__ == "__main__":
    main()
