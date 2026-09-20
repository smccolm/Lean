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
#print axioms TaoTrudgianYang2025.generatedExponentPairCoordinates_count
#print axioms TaoTrudgianYang2025.generatedBourgainDensityPieces_count
#print axioms TaoTrudgianYang2025.generatedEnergyClauses_count
#print axioms TaoTrudgianYang2025.generatedEnergyClauses_denominatorsPositive
#print axioms TaoTrudgianYang2025.bourgainPieceOne_eq_candidateFormula
#print axioms TaoTrudgianYang2025.bourgainPieceEight_eq_candidateFormula
#print axioms TaoTrudgianYang2025.optimizedBourgain_endpoint_agreement
#print axioms TaoTrudgianYang2025.optimizedBourgain_interval_cover
#print axioms TaoTrudgianYang2025.guthMaynard_largeValuePattern_estimate
#print axioms TaoTrudgianYang2025.guthMaynard_largeValueBound
#print axioms TaoTrudgianYang2025.largeValueExponent_le_guthMaynard
#print axioms TaoTrudgianYang2025.zetaLargeValueExponent_le_guthMaynard
#print axioms TaoTrudgianYang2025.two_mul_largeValueExponent_le_largeValueEnergyExponent
#print axioms TaoTrudgianYang2025.largeValueEnergyExponent_le_three_mul_largeValueExponent
#print axioms TaoTrudgianYang2025.two_mul_zetaLargeValueExponent_le_zetaLargeValueEnergyExponent
#print axioms TaoTrudgianYang2025.zetaLargeValueEnergyExponent_le_three_mul_zetaLargeValueExponent
#print axioms TaoTrudgianYang2025.approximateAdditiveEnergyOf_le_localMass_mul_cube
#print axioms TaoTrudgianYang2025.approximateAdditiveEnergyOf_perturbation_le
#print axioms TaoTrudgianYang2025.approximateAdditiveEnergyOf_le_natCeil_mul_unit
#print axioms TaoTrudgianYang2025.four_mul_mixedApproximateAdditiveEnergyOf_le_nine_mul_sum_self
#print axioms TaoTrudgianYang2025.exists_energy_color_classes
#print axioms TaoTrudgianYang2025.zeroAdditiveEnergy_le_perturbed
#print axioms TaoTrudgianYang2025.zeroAdditiveEnergy_le_mul_perturbed_unit
#print axioms TaoTrudgianYang2025.typeIZeroCopy_exists_shifted_detector
#print axioms TaoTrudgianYang2025.typeIZero_exists_shifted_detector
#print axioms TaoTrudgianYang2025.typeIZeroCopy_shifted_unitBin_card
#print axioms TaoTrudgianYang2025.typeIZeroCopy_shifted_unitBin_card_le
#print axioms TaoTrudgianYang2025.typeIZeroAdditiveEnergy_le_shifted_detector_energy
#print axioms TaoTrudgianYang2025.typeIZeroShiftedEnergy_exists_scale_classes
#print axioms TaoTrudgianYang2025.typeIZeroShiftedEnergy_exists_separated_scale_classes
#print axioms TaoTrudgianYang2025.typeIZeroAdditiveEnergy_le_detector_scale_class_energies
#print axioms TaoTrudgianYang2025.typeIZeroAdditiveEnergy_le_separated_detector_scale_class_energies
#print axioms TaoTrudgianYang2025.unitBinRank_lt_card
#print axioms TaoTrudgianYang2025.unitBinRank_injective_on_bin
#print axioms TaoTrudgianYang2025.oneSeparated_on_boundedMultiplicityColor
#print axioms TaoTrudgianYang2025.separatedRefinementColor_base
#print axioms TaoTrudgianYang2025.separatedRefinementColor_oneSeparated
#print axioms TaoTrudgianYang2025.injective_of_indexed_oneSeparated
#print axioms TaoTrudgianYang2025.image_isOneSeparated_of_indexed_oneSeparated
#print axioms TaoTrudgianYang2025.approximateAdditiveEnergyOf_equiv
#print axioms TaoTrudgianYang2025.finsetAdditiveEnergy_image_eq
#print axioms TaoTrudgianYang2025.typeISeparatedScaleColor_index_mem
#print axioms TaoTrudgianYang2025.detectorPatternNormalization_pos
#print axioms TaoTrudgianYang2025.normalizedDetectorPatternCoeff_norm_le_one
#print axioms TaoTrudgianYang2025.normalizedDetectorPattern_sum_eq
#print axioms TaoTrudgianYang2025.indexedDetectorLargeValuePattern_energy_eq
#print axioms TaoTrudgianYang2025.exists_typeIDetectorClassPattern
#print axioms TaoTrudgianYang2025.typeIDetectorClass_energy_eq_zero_or_exists_pattern
#print axioms TaoTrudgianYang2025.zeroCopy_local_card_eq_weighted_sum
#print axioms TaoTrudgianYang2025.IsZeroDensityEnergyBound.toZeroDensityBound_half
#print axioms TaoTrudgianYang2025.IsZeroDensityBound.toEnergyBound_four_mul
#print axioms TaoTrudgianYang2025.two_mul_zeroDensityExponent_le_zeroDensityEnergyExponent
#print axioms TaoTrudgianYang2025.zeroDensityEnergyExponent_le_four_mul_zeroDensityExponent
#print axioms TaoTrudgianYang2025.zeroAdditiveEnergy_le_globalCap_mul_cube
#print axioms TaoTrudgianYang2025.globalMultiplicityCap_le_rpow
#print axioms TaoTrudgianYang2025.IsZeroDensityBound.toEnergyBound_three_mul
#print axioms TaoTrudgianYang2025.zeroDensityEnergyExponent_le_three_mul_zeroDensityExponent
#print axioms TaoTrudgianYang2025.InLargeValueEnergyRegion.two_mul_rho_le_rhoStar
#print axioms TaoTrudgianYang2025.InLargeValueEnergyRegion.rhoStar_le_three_mul_rho
#print axioms TaoTrudgianYang2025.InLargeValueEnergyRegion.rho_le_tau
#print axioms TaoTrudgianYang2025.InLargeValueEnergyRegion.rhoStar_le_of_energyBound
#print axioms TaoTrudgianYang2025.InZetaLargeValueEnergyRegion.rhoStar_le_of_energyBound
#print axioms TaoTrudgianYang2025.largeValueEnergyRegionSupremum_le_largeValueEnergyExponent
#print axioms TaoTrudgianYang2025.zetaLargeValueEnergyRegionSupremum_le_zetaLargeValueEnergyExponent
#print axioms TaoTrudgianYang2025.energyRegion_exists_rhoStar_gt_of_not_bound
#print axioms TaoTrudgianYang2025.zetaEnergyRegion_exists_rhoStar_gt_of_not_bound
#print axioms TaoTrudgianYang2025.largeValueEnergyExponent_eq_regionSupremum
#print axioms TaoTrudgianYang2025.zetaLargeValueEnergyExponent_eq_regionSupremum
#print axioms TaoTrudgianYang2025.inLargeValueEnergyRegionAsymptotic_iff
#print axioms TaoTrudgianYang2025.inZetaLargeValueEnergyRegionAsymptotic_iff
#print axioms TaoTrudgianYang2025.isLargeValueEnergyBoundAsymptotic_iff
#print axioms TaoTrudgianYang2025.isZetaLargeValueEnergyBoundAsymptotic_iff
#print axioms TaoTrudgianYang2025.isZeroDensityEnergyBoundAsymptotic_iff

#eval runBootstrapDependencyAudit

end TaoTrudgianYang2025.Audit
