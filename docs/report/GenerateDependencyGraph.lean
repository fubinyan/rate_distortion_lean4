import RateDistortion
import Lean

open Lean

namespace RateDistortionDependencyGraph

private def targetModule : Name := `RateDistortion

private def keyDeclarations : Array (String × Array Name) := #[
  ("Finite probability and coding", #[
    `Distortion,
    `RateDistortionCode,
    `blockDistortion,
    `codeRate,
    `pmfRealExpectation,
    `pmfRealVariance,
    `pmf_deviation_probability_le_variance_div_sq
  ]),
  ("Entropy and mutual information", #[
    `shannonEntropy,
    `kl_divergence,
    `mutual_information,
    `conditionalEntropy,
    `mutual_information_eq_ofReal_entropy
  ]),
  ("Single-letter rate-distortion", #[
    `expected_distortion_single,
    `induced_joint,
    `RateDistortionFunction,
    `feasibleDistortion,
    `interiorDistortion,
    `RateDistortionFunction_attained,
    `continuous_mutual_information,
    `lowerSemicontinuous_RateDistortionFunction,
    `RateDistortionFunction_antitone,
    `RateDistortionFunction_convex_of_feasible
  ]),
  ("Direct part: memoryless random coding", #[
    `iidBlockPMF,
    `memorylessJointPMF,
    `singleLetterInformationDensity,
    `goodBlockPair,
    `exists_nat_forall_exists_exponentialCode_rate_and_expectedDistortion
  ]),
  ("Converse: single-letterization", #[
    `codeJointPMF,
    `averageCoordinateJointPMF,
    `expectedDistortion,
    `RateDistortionFunction_expectedDistortion_le_codeRate
  ]),
  ("Asymptotics and final theorem", #[
    `CodeSequence,
    `asymptoticDistortion,
    `asymptoticRate,
    `isAchievable,
    `isAchievablePointwise,
    `isAchievablePointwise_imp_isAchievable,
    `exists_codeSequence_testChannel_achieves,
    `rateDistortionRightContinuousAt_all,
    `rate_distortion_achievability_at_boundary,
    `rate_distortion_achievable_iff,
    `rate_distortion_sequence_converse_add,
    `rate_distortion_achievability,
    `rate_distortion_converse,
    `rate_distortion_nonachievability
  ])
]

private def keyNames : NameSet :=
  keyDeclarations.foldl (init := {}) fun acc (_, names) =>
    names.foldl (init := acc) fun acc name => acc.insert name

private def overviewNames : NameSet := NameSet.ofList [
  `pmfRealVariance,
  `shannonEntropy,
  `mutual_information,
  `RateDistortionFunction,
  `RateDistortionFunction_attained,
  `lowerSemicontinuous_RateDistortionFunction,
  `memorylessJointPMF,
  `goodBlockPair,
  `exists_nat_forall_exists_exponentialCode_rate_and_expectedDistortion,
  `averageCoordinateJointPMF,
  `RateDistortionFunction_expectedDistortion_le_codeRate,
  `CodeSequence,
  `rateDistortionRightContinuousAt_all,
  `rate_distortion_achievability,
  `rate_distortion_converse,
  `rate_distortion_achievability_at_boundary,
  `rate_distortion_achievable_iff
]

private def declarationModule? (env : Environment) (name : Name) : Option Name := do
  let idx <- env.getModuleIdxFor? name
  env.header.moduleNames[idx.toNat]?

private def isTargetDeclaration (env : Environment) (name : Name) : Bool :=
  declarationModule? env name == some targetModule

private partial def nearestKeyDependenciesFrom
    (env : Environment) (root : Name) (initial : NameSet) : NameSet := Id.run do
  let mut result : NameSet := {}
  let mut visited : NameSet := {root}
  let mut pending : List Name := initial.toList
  while !pending.isEmpty do
    let current := pending.head!
    pending := pending.tail!
    if !visited.contains current then
      visited := visited.insert current
      if keyNames.contains current then
        result := result.insert current
      else if isTargetDeclaration env current then
        if let some info := env.find? current then
          pending := info.getUsedConstantsAsSet.toList ++ pending
  return result

private def bodyUsedConstants (info : ConstantInfo) : NameSet :=
  match info.value? with
  | some value => value.getUsedConstantsAsSet
  | none =>
      match info with
      | .opaqueInfo value => value.value.getUsedConstantsAsSet
      | _ => {}

private def declarationKind (env : Environment) (name : Name) : String :=
  match env.find? name with
  | some (.axiomInfo _) => "axiom"
  | some (.defnInfo _) => "definition"
  | some (.thmInfo _) => "theorem"
  | some (.opaqueInfo _) => "opaque"
  | some (.quotInfo _) => "quotient"
  | some (.inductInfo _) => "inductive"
  | some (.ctorInfo _) => "constructor"
  | some (.recInfo _) => "recursor"
  | none => "missing"

private def hasDirectSorry (env : Environment) (name : Name) : Bool :=
  match env.find? name with
  | some info => info.getUsedConstantsAsSet.contains ``sorryAx
  | none => false

private def renderJson (env : Environment) : String := Id.run do
  let mut nodes : Array Json := #[]
  let mut edges : Array Json := #[]
  for ((group, names), groupIndex) in keyDeclarations.zipIdx do
    for name in names do
      let node := Json.mkObj [
        ("id", name.toString),
        ("label", name.toString),
        ("group", group),
        ("groupIndex", groupIndex),
        ("kind", declarationKind env name),
        ("hasSorry", hasDirectSorry env name),
        ("overview", overviewNames.contains name)
      ]
      nodes := nodes.push node
      let info := env.find? name |>.get!
      for dependency in nearestKeyDependenciesFrom env name info.type.getUsedConstantsAsSet do
        edges := edges.push <| Json.mkObj [
          ("source", dependency.toString),
          ("target", name.toString),
          ("kind", "statement")
        ]
      for dependency in nearestKeyDependenciesFrom env name (bodyUsedConstants info) do
        edges := edges.push <| Json.mkObj [
          ("source", dependency.toString),
          ("target", name.toString),
          ("kind", "proof")
        ]
  let graph := Json.mkObj [
    ("module", targetModule.toString),
    ("extraction", "nearest selected declarations along kernel-level constant references"),
    ("nodes", Json.arr nodes),
    ("edges", Json.arr edges)
  ]
  return graph.pretty 120

elab "#export_rate_distortion_dependencies" path:str : command => do
  let env <- getEnv
  let missing := keyNames.toList.filter fun name => !(env.contains name)
  unless missing.isEmpty do
    throwError "Missing declarations: {missing}"
  let outputPath := System.FilePath.mk path.getString
  IO.FS.writeFile outputPath (renderJson env)
  logInfo m!"Wrote {keyNames.size} selected declarations to {outputPath}"

end RateDistortionDependencyGraph

#export_rate_distortion_dependencies
  "docs/report/rate_distortion_dependencies.json"
