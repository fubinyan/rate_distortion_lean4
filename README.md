# Rate-distortion theory in Lean 4

This project formalizes the finite-alphabet rate-distortion theorem in Lean 4, building on Mathlib. It also develops reusable definitions and lemmas for finite probability distributions, information measures, optimization over test channels, and asymptotic coding arguments.

The main development is in [RateDistortion.lean](RateDistortion.lean). Start with [MainResults.lean](MainResults.lean) for the principal theorem signatures and their axiom dependencies.

## Mathematical setting

The source and reproduction alphabets are finite. Sources and test channels use Mathlib's `PMF`; a test channel has type `X → PMF Y`. Single-letter distortion takes values in `NNReal`, so it is finite and nonnegative. Expected distortions, thresholds, and the information rate-distortion function take values in `ENNReal`.

$$R_I(D)=\inf_{W:\,\mathbb{E}_{P,W}[d(X,Y)]\leq D} I(X;Y).$$

The source marginal is fixed at `P`. An empty feasible set has infimum `∞`. All logarithms are natural, so rates and information quantities are measured in nats.

Operational codes have deterministic encoders and decoders. A `CodeSequence` uses blocklength `n + 1` at index `n`, excluding zero blocklength. The distortion constraint bounds the limit superior of expected average per-letter distortion by `D`.

## Main results

Two rate constraints are provided:

- `isAchievablePointwise`: every code in the sequence has rate at most `R`.
- `isAchievable`: the limit superior of the code rates is at most `R`.

Both use the same asymptotic distortion constraint. The theorem `isAchievablePointwise_imp_isAchievable` relates them.

For a nonnegative real rate `R`, the principal endpoints are:

| Declaration | Result |
| --- | --- |
| `rate_distortion_achievability` | If `R_I(D) < R`, then `isAchievablePointwise P d R D`. |
| `rate_distortion_converse` | Pointwise achievability implies `R_I(D) ≤ R`, for every distortion threshold. |
| `rate_distortion_achievability_asymptotic` | If `R_I(D) ≤ R`, then `isAchievable P d R D`. |
| `rate_distortion_converse_asymptotic` | Asymptotic achievability implies `R_I(D) ≤ R`. |
| `rate_distortion_achievability_at_boundary` | Equality-rate achievability holds under the asymptotic rate constraint when `R_I(D)` is finite. |
| `rate_distortion_achievable_iff` | Asymptotic achievability is equivalent to `R_I(D) ≤ R`. |

Lean compares `RateDistortionFunction P d D` with `ENNReal.ofReal R`. The equality-rate theorem uses `.toReal` with an explicit finiteness hypothesis. It does not assert that every individual code has rate at most `R_I(D)`.

The final converse has no separate right-continuity or interior-distortion hypothesis: `rateDistortionRightContinuousAt_all` proves the required property within the development. Optimal test channels exist under feasible distortion constraints, as established in `RateDistortionFunction_attained`.

## Build and verify

Install Lean through [elan and the Lean installation guide](https://leanprover-community.github.io/get_started.html). The development environment uses Lean **4.28.0** and Mathlib **v4.28.0**. `lean-toolchain` and `lake-manifest.json` pin the toolchain and dependency revisions.

From a checkout containing these build files, run:

```sh
lake exe cache get
lake build
lake env lean MainResults.lean
```

The first command downloads precompiled dependencies. The build checks the main module, the PMF API example, and the main-results audit. The final command displays theorem signatures and axiom dependencies.

The audit permits only `propext`, `Classical.choice`, and `Quot.sound` for the checked endpoints. `MainResults.lean` fails if an additional axiom, including `sorryAx`, appears in their dependencies. Kernel checking verifies the formal statements relative to their definitions and axioms; correspondence with the intended mathematics also requires reading those definitions and statements.

The standalone build and axiom audit passed locally on 22 September 2026; see the [verification record](docs/verification.md). GitHub Actions repeats the checks on pushes and pull requests.

For interactive inspection, open the repository folder in VS Code with the Lean 4 extension. The main module uses a `noncomputable section`; it proves existence and analytic properties rather than providing an executable compression algorithm.

## Reusable components

The development reuses Mathlib's probability mass functions, finite sums and products, KL divergence, filters, and topological results. Additional components include:

| Area | Selected declarations |
| --- | --- |
| Finite probability | `pmfRealExpectation`, `pmfRealVariance`, `exists_le_pmf_weighted_sum` |
| Information measures | `shannonEntropy`, `conditionalEntropy`, `mutual_information`, `mutual_information_eq_ofReal_entropy` |
| Test-channel optimization | `induced_joint`, `expected_distortion_single`, `RateDistortionFunction`, `RateDistortionFunction_attained` |
| Continuity and compactness | `PMF.instCompactSpace`, `continuous_shannonEntropy`, `continuous_mutual_information`, `lowerSemicontinuous_RateDistortionFunction`, `rateDistortionRightContinuousAt_all` |
| Memoryless distributions | `iidBlockPMF`, `memorylessChannelBlockPMF`, `memorylessJointPMF` |
| Random coding | `randomCodebookPMF`, `memorylessCodebookPMF`, `goodBlockPair`, `codebookEncoder` |
| Finite-block converse | `averageCoordinateJointPMF`, `RateDistortionFunction_expectedDistortion_le_codeRate` |
| Asymptotic coding | `CodeSequence`, `exists_diagonalCodeSequence_of_eventually_codes`, `exists_codeSequence_testChannel_achieves` |

These declarations currently live in one module. A future split can expose smaller imports for downstream developments. They are project-level additions; this repository does not claim that they have already been incorporated into Mathlib.

## Files and reading guide

- [RateDistortion.lean](RateDistortion.lean): definitions, supporting infrastructure, and proofs.
- [MainResults.lean](MainResults.lean): principal theorem signatures and axiom checks.
- [ApiCheck.lean](ApiCheck.lean): a small standalone example of constructing an i.i.d. block PMF. It is not an audit of the full proof.
- [Architecture report](rate_distortion_formalization_infrastructure.pdf): the proof architecture, mathematical scope, and reusable components.
- [Report source and reproduction instructions](docs/report/README.md): LaTeX source and dependency-graph generation tools.
- [Interactive dependency graph](docs/report/rate_distortion_dependency_graph.html): download or clone the repository and open this file locally, keeping the adjacent JavaScript data file.
- [Report revision notes](docs/report-status.md): changes from the earlier report.

The updated report distinguishes the pointwise and asymptotic rate constraints, describes the converse at all distortion thresholds, and includes equality-rate achievability under the asymptotic rate constraint. Its dependency data are extracted from the compiled module.

For a mathematical reading, begin with `Distortion`, `RateDistortionFunction`, `CodeSequence`, and the two achievability definitions, then inspect the main theorem statements. For the proofs, the finite-block converse and random-codebook construction provide separate entry points before the asymptotic arguments.

## Scope and further work

The present formalization covers finite alphabets, finite nonnegative single-letter distortion, and deterministic operational codes. Countable or continuous alphabets, infinite letterwise distortion, and stochastic operational encoders or decoders are outside this development. Equality-rate achievability with a pointwise rate bound is not asserted.

Further infrastructure work includes splitting the main module, providing downstream examples, and assessing which general lemmas fit Mathlib's existing interfaces.

## Contributions and citation

Issues and improvements can be discussed in the [issue tracker](https://github.com/fubinyan/rate_distortion_lean4/issues). Changes to definitions or main theorem hypotheses should explain their mathematical effect and update the documentation.

When referring to the development, include the repository URL and the commit used. A paper citation and a versioned archive can be added when publication metadata is available.
