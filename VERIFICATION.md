# Black-Scholes submission preparation — 2026-09-27

This records local checks of the Lean 4.35 upgrade and the final document
review in `lean-stochastic-calculus` on 2026-09-27. The upgrade was prepared
from `3bb950a4439da4997ec0e9fe31668f0a84c2ae98` and committed by the author as
`d9afe51e59cf7108e4243ce43ba5579ceee75742`. The review corrections described
below were made after that commit. The eventual submission must include them,
and GitHub CI must pass on that exact final commit. This local record is not
a Palomar verification report or a substitute for the final commit identifier.

## What changed

Lean and Mathlib were upgraded together. The proof repairs adapt to changed
library interfaces for integrability, Gaussian laws, product measures and
uniform integrability, and replace deprecated lemma names. Some internal
helper assumptions changed to match Mathlib. The public mathematical statement,
its assumptions, definition bodies and proof are unchanged. The final review
corrected an explanatory comment in the Solution.

The metadata now identifies the Black-Scholes paper as the source of the known
result, with `relationship: independently-proves`, and explains the standard
Girsanov proof route. Agent involvement, untracked working time and the absence
of an in-depth human review remain disclosed. The general integrand constructor
remains deferred.

The README, blueprint, library guide and metadata explicitly describe the
constant-drift application of the general predictable (dynamic) Girsanov
theorem. The blueprint and library guide identify the retained adapters that
are outside this Black-Scholes proof.

The final review made the positivity assumptions and time-zero scope explicit,
corrected the account of the field-by-field conversion between the two
strong-solution structures, and repaired the blueprint's probability-measure
explanation and Novikov lemma location. The Challenge and Comparator
configuration needed no further changes. The existing disclosure about the
absence of in-depth human review still applies.

Checking scripts now use Lean's bundled Comparator and exporters. They select
the bundled NanoDa and con-ron checkers in a temporary local configuration.
The negative control restores both the Challenge source and its compiled form.
CI also checks the Girsanov dependency and uses Palomar's pinned metadata
validator.

## Versions

| Component | Version or exact revision |
| --- | --- |
| Lean | `v4.35.0-rc3`, `470d5ce1400764999581fd26d5d72b00d990b0f4` |
| Mathlib | `v4.35.0-rc3`, `c55e6e786f49471c72fbddbec5415808896aec1e` |
| Comparator, leanexport, Lean kernel, NanoDa, con-ron | Bundled with that Lean toolchain |
| PalomarSubmission validator | `a59f25bd8a66bf6faf3a4f4260d412989c0185ea` |
| Minimum Lean in that validator | `v4.35.0-rc2` |
| Python metadata dependency | `PyYAML==6.0.3` |

All nine Lake dependency revisions are recorded in
[lake-manifest.json](lake-manifest.json). Their local checkouts are clean and
match those pins; Mathlib's own dependencies agree with its manifest.

The validator revision is linked
[here](https://github.com/PalomarRegistry/PalomarSubmission/tree/a59f25bd8a66bf6faf3a4f4260d412989c0185ea).
Its implementation uses the submitted Lean toolchain's Comparator, NanoDa and
con-ron. This replaces the earlier local arrangement using a separately built
Comparator, lean4export and a Landrun shim.

## Checks

1. **Strict library and Solution build — passed.**
   `lake build StochasticCalculus BlackScholesSolution --iofail` completed
   successfully (3,391 jobs), without warnings. No new proof holes, axioms,
   warning suppressions or increased heartbeat limits were introduced.
2. **Challenge build — passed.** Its one intentional theorem placeholder is
   the expected warning. The completed Solution uses only `propext`,
   `Classical.choice` and `Quot.sound`.
3. **Comparator and three proof checkers — passed.**
   `python3 scripts/check_boundary.py --comparator --local` reported acceptance
   by Lean's kernel, NanoDa and con-ron, followed by `Your solution is okay!`.
   con-ron reported 62,110 accepted declarations.
4. **Dynamic Girsanov dependency — passed.**
   `lake env lean scripts/check_girsanov_route.lean` found 63,471 reachable
   constants. The predictable Girsanov theorem, its martingale proof, the
   constant-drift bridge and the continuous Brownian version are present.
   No constant from the old Gaussian oracle namespace, or its measure
   identification bridge, occurs in the proof's dependencies.
5. **Negative control — passed.**
   `bash scripts/negative_control.sh --local` requires an accepted baseline,
   removes the two absolute-continuity clauses, builds that altered statement,
   and requires Comparator to reject the named theorem for a statement
   mismatch. Comparator rejected `PalomarBlackScholes.black_scholes` for
   exactly that mismatch. The original Challenge was restored and rebuilt
   successfully before the script exited with status zero.
6. **Metadata and packaging — passed.**
   `python scripts/check_metadata.py` in the PyYAML environment used Palomar's
   own validator. It accepted source-based provenance, the Comparator schema,
   matching supported toolchains and exact dependency pins. Local packaging
   checks found no disallowed submodule, LFS or compiled-artifact packaging.
   The unchanged license text matches Apache's published Apache-2.0 license
   after whitespace normalization and agrees with the metadata. Palomar's
   license detector remains part of its protected run.
7. **Statement preservation — passed.** The Challenge is byte-for-byte
   identical to the base commit. The Solution differs only in its module
   comment; its declarations and proof are unchanged. SHA-256:
   - Challenge: `3b553460fe14af05f193ac8f57a062aca5b36853187aed787a0f15db85928421`
   - Solution: `2f668d3f5146c8838f34bb3425f7f9101118a8217650831d47f8cbf0026fcc11`

Commands for a fresh checkout are in [README.md](README.md). Local transcripts
are retained under the ignored `.lake/palomar-prep-20260927/` directory:
`build.log`, `boundary.log`, `girsanov-route.log`, `negative-control.log` and
`metadata.log`. `final-preflight.log` records the checks after the negative
control restored the Challenge. The import audit also recorded the complete
Challenge import graph: 4,780 imported modules, all from Lean or Mathlib's
pinned dependency set.

The final-review checks are recorded separately under
`.lake/palomar-review-20260927/`. They include the updated Solution build,
Comparator and independent kernels, negative control, proof-dependency audit,
and a compiled check that the two strong-solution structures imply each other
by transferring the same five fields.

## Limits and next steps

These checks ran on macOS with `--local`, which explicitly disables the Linux
sandbox. They are local proof checks, not a Palomar mechanical or editorial
review. Palomar must independently rebuild, protect the Challenge and verify
the exact submitted commit. Its rules may change before submission.

Before submission: commit and push all review corrections, require GitHub CI
to pass on that exact commit, and record its full identifier. The repository
must also be publicly accessible, as required by
[Palomar's submission instructions](https://palomar-registry.org/how-to-submit).
Any subsequent proof or configuration changes require the relevant checks
again. Palomar submission,
review and the author's decision about registration remain outstanding.
