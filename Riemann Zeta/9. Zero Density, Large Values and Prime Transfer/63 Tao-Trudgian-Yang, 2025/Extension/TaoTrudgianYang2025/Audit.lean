import TaoTrudgianYang2025

open Lean

namespace TaoTrudgianYang2025.Audit

private def permittedAxioms : Array Name :=
  #[`propext, `Classical.choice, `Quot.sound]

private def bootstrapDeclarations : Array Name := #[
  `Expdb.automatic_uniformity_of_choicewise_bounded,
  `Expdb.isExponentSumBound_exponentSumGrowthExponent,
  `Expdb.exponentSumGrowthExponent_le_iff_nonAsymptotic,
  `RiemannZeta.GuthMaynard.guthMaynardLargeValues_published_native,
  `RiemannZeta.GuthMaynard.guthMaynardZeroDensity_published_native
]

private def targetTheorems (env : Environment) : Array Name := Id.run do
  let mut names := #[]
  for (name, info) in env.constants.toList do
    if name.getRoot == `TaoTrudgianYang2025 && info.isTheorem &&
        !isPrivateName name then
      names := names.push name
  return names.qsort Name.quickLt

def runBootstrapDependencyAudit : CoreM Unit := do
  let env ← getEnv
  let discovered := targetTheorems env
  let declarations := bootstrapDeclarations ++ discovered
  let mut failures : Nat := 0
  logInfo "=== TAO--TRUDGIAN--YANG BOOTSTRAP AXIOM AUDIT ==="
  logInfo m!"Imported boundary declarations: {bootstrapDeclarations.size}"
  logInfo m!"Discovered nonprivate target theorems: {discovered.size}"
  for name in declarations do
    if !env.contains name then
      failures := failures + 1
      logInfo m!"FAIL [missing declaration] {name}"
    else
      let axioms ← Lean.collectAxioms name
      let forbidden := axioms.filter fun axiomName =>
        !permittedAxioms.contains axiomName
      if forbidden.isEmpty then
        logInfo m!"PASS {name}: {axioms}"
      else
        failures := failures + 1
        logInfo m!"FAIL {name}: forbidden dependencies {forbidden}; all axioms {axioms}"
  if failures == 0 then
    logInfo m!"AUDIT PASS: all {declarations.size} imported and target declarations have permitted dependencies."
  else
    throwError "AUDIT FAIL: {failures} bootstrap dependency failure(s)"

#print axioms Expdb.automatic_uniformity_of_choicewise_bounded
#print axioms Expdb.isExponentSumBound_exponentSumGrowthExponent
#print axioms Expdb.exponentSumGrowthExponent_le_iff_nonAsymptotic
#print axioms RiemannZeta.GuthMaynard.guthMaynardLargeValues_published_native
#print axioms RiemannZeta.GuthMaynard.guthMaynardZeroDensity_published_native
#print axioms TaoTrudgianYang2025.guthMaynard_largeValuePattern_estimate
#print axioms TaoTrudgianYang2025.guthMaynard_largeValueBound
#print axioms TaoTrudgianYang2025.largeValueExponent_le_guthMaynard
#print axioms TaoTrudgianYang2025.zetaLargeValueExponent_le_guthMaynard
#print axioms TaoTrudgianYang2025.two_mul_largeValueExponent_le_largeValueEnergyExponent
#print axioms TaoTrudgianYang2025.largeValueEnergyExponent_le_three_mul_largeValueExponent
#print axioms TaoTrudgianYang2025.two_mul_zetaLargeValueExponent_le_zetaLargeValueEnergyExponent
#print axioms TaoTrudgianYang2025.zetaLargeValueEnergyExponent_le_three_mul_zetaLargeValueExponent
#print axioms TaoTrudgianYang2025.InLargeValueEnergyRegion.two_mul_rho_le_rhoStar
#print axioms TaoTrudgianYang2025.InLargeValueEnergyRegion.rhoStar_le_three_mul_rho
#print axioms TaoTrudgianYang2025.InLargeValueEnergyRegion.rho_le_tau

#eval runBootstrapDependencyAudit

end TaoTrudgianYang2025.Audit
