import RateDistortion

/-! Main public results and a reproducible axiom audit. -/

#check rate_distortion_achievability
#check rate_distortion_converse
#check rate_distortion_achievability_at_boundary
#check rate_distortion_achievable_iff
#check RateDistortionFunction_attained
#check rateDistortionRightContinuousAt_all

#print axioms rate_distortion_achievability
#print axioms rate_distortion_converse
#print axioms rate_distortion_achievability_at_boundary
#print axioms rate_distortion_achievable_iff
#print axioms rateDistortionRightContinuousAt_all

open Lean in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let results : Array Name := #[
    ``rate_distortion_achievability,
    ``rate_distortion_converse,
    ``rate_distortion_achievability_at_boundary,
    ``rate_distortion_achievable_iff,
    ``rateDistortionRightContinuousAt_all]
  for result in results do
    let axioms ← Lean.collectAxioms result
    let unexpected := axioms.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError "Unexpected axioms in {result}: {unexpected}"
