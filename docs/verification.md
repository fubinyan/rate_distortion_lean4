# Local verification record

Verified on 22 September 2026 using Lean 4.28.0 and Mathlib v4.28.0 on Windows.

The mathematical source is unchanged from upstream commit
`abe3000db8beb77484fd8b082961d947dfa30050`.
SHA-256 of `RateDistortion.lean`:
`3e243cc4338bd99161c79da323ae9e49f4413e7b971a187e231452b1fba4a496`.

After fetching the required Mathlib caches, `lake -R build` completed
successfully (3161 jobs), including `RateDistortion`, `ApiCheck`, and
`MainResults`. The existing mathematical source emits linter warnings;
these did not prevent the build.

The five endpoints audited in `MainResults.lean` each depended only on
`propext`, `Classical.choice`, and `Quot.sound`. The automated allowlist
check passed. It rejects any other axiom, including `sorryAx`.
This verifies the formal results relative to their definitions and axioms;
it does not replace mathematical review of the statements.

The dependency extractor ran against the compiled module. It selected 45
declarations and produced 204 merged dependency edges, reduced to 82 edges.
The report overview displays 17 declarations and 25 reduced dependency paths.
The graph is a selected overview, not a complete inventory or an axiom audit.

The GitHub Actions workflow is included for future pushes and pull requests.
This record reports a local build; it does not claim a completed GitHub Actions run.
