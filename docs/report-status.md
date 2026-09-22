# Architecture report revision notes

The earlier PDF dated 14 August 2026 described an older version. The updated report has been aligned with the mathematical source at upstream commit `abe3000db8beb77484fd8b082961d947dfa30050`. No mathematical proof was changed in this documentation update.

The finite-PMF, entropy, memoryless-distribution, concentration, random-coding, and diagonalization descriptions are retained. The following scope changes are now reflected in the report.

| Report location | Earlier description | Current source |
| --- | --- | --- |
| Abstract; Sections 11, 15, 16 | Converse restricted to interior distortion | `rate_distortion_converse` applies at every threshold. |
| Sections 11, 15, 16 | Equality-rate achievability left open | `rate_distortion_achievability_at_boundary` proves it under an asymptotic rate constraint when `R_I(D)` is finite. A pointwise bound at equality is not claimed. |
| Section 11.1 | Direct theorem assumes feasibility and returns `isAchievable` | The principal strict-rate theorem returns `isAchievablePointwise`; no separate feasibility hypothesis is needed. |
| Sections 10, 11 | One achievability predicate | Both pointwise and asymptotic rate constraints are exposed, with a proved implication between them. |
| Sections 6, 11, 15 | Interior right continuity | Compactness, continuity, attainment under feasibility, and lower semicontinuity support `rateDistortionRightContinuousAt_all`. |
| Section 14 | Build target `Myproject.RateDistortion.RateDistortion` | With the standalone configuration, use `lake build`, or `lake build RateDistortion`. |

The previously missing reproduction files are now included under `docs/report/`:

- `GenerateDependencyGraph.lean`
- `GenerateDependencyArtifacts.ps1`
- `rate_distortion_dependencies.json`
- `rate_distortion_dependency_graph.html`

The graph has additional nodes for attainment, lower semicontinuity, right continuity at all thresholds, the two operational rate predicates, and equality-rate achievability. The report source and a vector-figure renderer are included. Historical declaration counts have been removed in favor of identifying the mathematical source commit.
