/-! Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
/- Inspect binders in the elaborated theorem type. The named propositions are the
potential theory, flux and stability inputs identified in AUDIT_NOTES.md. -/
namespace ErdosVolumeAudit
open Lean Elab Command

def analyticInputs : List Name := [
  `ErdosVolume.OpenIsoFact, `ErdosVolume.CapacityNormalization,
  `ErdosVolume.BallCapacityFact, `ErdosVolume.EquilibriumExistence,
  `ErdosVolume.EquilibriumMomentFact, `ErdosVolume.EquilibriumSphereFact,
  `ErdosVolume.Paper.EquilibriumBallLaw,
  `ErdosVolume.Flux.AnalyticNull, `ErdosVolume.Flux.SardScalar,
  `ErdosVolume.Flux.CoareaSlabs, `ErdosVolume.Flux.PuncturedGauss,
  `ErdosVolume.Flux.BallGauss, `ErdosVolume.Flux.SphereArea,
  `ErdosVolume.Flux.SharpIso, `ErdosVolume.Flux.SurfaceFinite,
  `ErdosVolume.Stability.CompactIso, `ErdosVolume.Stability.EqExists,
  `ErdosVolume.Stability.Frostman, `ErdosVolume.Stability.EqUnique,
  `ErdosVolume.Stability.BallLaw,
  `ErdosVolume.Paper.PlanarTwoMarkBound]

partial def binderInputs : Expr → NameSet
  | .forallE _ domain body _ => Id.run do
    let mut found := binderInputs body
    for name in domain.getUsedConstants do
      if analyticInputs.contains name then found := found.insert name
    return found
  | .letE _ _ _ body _ | .mdata _ body => binderInputs body
  | _ => {}

def report (name : Name) : CommandElabM Unit := do
  let info ← getConstInfo name
  let inputs := ((binderInputs info.type).toList.map Name.toString).mergeSort (· ≤ ·)
  logInfo m!"INPUTS|{name}|{String.intercalate "," inputs}|END"
end ErdosVolumeAudit
