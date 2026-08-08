import Lean.Util.CollectAxioms
import RiemannZeta

open Lean

/-!
# Riemann Zeta dependency audit

This file is executable verification, not a declaration-name classification.
`auditedDeclarations` explicitly lists every source-level theorem exported by the
production modules imported above. `runDependencyAudit` computes each theorem's
transitive axioms with `Lean.collectAxioms` and rejects every dependency except
Lean's standard logical axioms.

The synchronization check also rejects a newly exported project theorem until it
is deliberately added to the explicit list. Compiler-generated equation and proof
theorems are excluded from that public-source check.
-/

/-- Standard Lean/Mathlib logical axioms permitted by the project policy. -/
def permittedAxioms : Array Name :=
  #[``propext, ``Classical.choice, ``Quot.sound]

/--
Every public source-level theorem in the imported production modules.

The count is derived from this array rather than maintained as a second literal,
so the reported count cannot drift from the actual audit list.
-/
def auditedDeclarations : Array Name := #[
  -- Foundational zeta and Dirichlet-polynomial modules
  ``RiemannZeta.point_re,
  ``RiemannZeta.point_im,
  ``RiemannZeta.one_sub_point,
  ``RiemannZeta.star_point,
  ``RiemannZeta.completedRiemannZeta_reflection,
  ``RiemannZeta.completedRiemannZeta_zero_reflection_iff,
  ``RiemannZeta.completedRiemannZeta_norm_reflection,
  ``RiemannZeta.completedRiemannZeta_fourfold_zero_orbit,
  ``RiemannZeta.dirichletPoly_conj,
  ``RiemannZeta.dirichletPoly_norm_conj,
  ``RiemannZeta.dirichletNormSquare_conj_line,
  ``RiemannZeta.threshold_conj_line_iff,
  ``RiemannZeta.dirichletPoly_zero_conj,
  ``RiemannZeta.dirichletPoly_zero_conj_iff,
  ``RiemannZeta.crossNormProduct_nonneg,
  ``RiemannZeta.conjCoeff_conjCoeff,
  ``RiemannZeta.crossNormProduct_swap,
  ``RiemannZeta.realPart_abs_le_crossNormProduct,
  ``RiemannZeta.crossNormProduct_eq_zero_of_left,
  ``RiemannZeta.crossNormProduct_eq_zero_of_right,
  ``RiemannZeta.crossNormProduct_eq_zero_iff,
  ``RiemannZeta.criticalLinePoint_re,
  ``RiemannZeta.criticalLinePoint_im,
  ``RiemannZeta.conj_criticalLinePoint,
  ``RiemannZeta.criticalLinePoint_neg_eq_one_sub,
  ``RiemannZeta.completedRiemannZeta_criticalLine_functional_eq,
  ``RiemannZeta.completedRiemannZeta_criticalLine_symm,
  ``RiemannZeta.completedRiemannZeta_norm_criticalLine_neg,
  ``RiemannZeta.hardyZ_norm_eq_riemannZeta_norm,
  ``RiemannZeta.hardyZ_zero_iff_riemannZeta_zero,
  ``RiemannZeta.hardyZ_neg_norm,
  ``RiemannZeta.riemannZeta_ne_zero_of_re_ge_one_of_ne_one,
  ``RiemannZeta.riemannZeta_ne_zero_on_one_line,
  ``RiemannZeta.riemannZeta_ne_zero_totalized,

  -- Guth--Maynard infrastructure and transfer modules
  ``RiemannZeta.GuthMaynard.EpsilonPowerBound.refl,
  ``RiemannZeta.GuthMaynard.EpsilonPowerBound.trans,
  ``RiemannZeta.GuthMaynard.EpsilonPowerBound.add,
  ``RiemannZeta.GuthMaynard.EpsilonPowerBound.congr_left,
  ``RiemannZeta.GuthMaynard.card_pos_of_nonempty,
  ``RiemannZeta.GuthMaynard.isSeparated_translate,
  ``RiemannZeta.GuthMaynard.inBaseInterval_translate,
  ``RiemannZeta.GuthMaynard.translateSet_card,
  ``RiemannZeta.GuthMaynard.dirichletPoly_eq_existing,
  ``RiemannZeta.GuthMaynard.norm_sourceDirichletPoly_conjugateCoeffs,
  ``RiemannZeta.GuthMaynard.norm_conjugateCoeffs,
  ``RiemannZeta.GuthMaynard.dirichletPoly_translate,
  ``RiemannZeta.GuthMaynard.norm_phaseShiftCoeffs,
  ``RiemannZeta.GuthMaynard.norm_normalizedCoeffs_le,
  ``RiemannZeta.GuthMaynard.convolution_support,
  ``RiemannZeta.GuthMaynard.guthMaynardLargeValues_neg,
  ``RiemannZeta.GuthMaynard.guth_maynard_exponent_pos,
  ``RiemannZeta.GuthMaynard.mem_ZeroRectangle,
  ``RiemannZeta.GuthMaynard.ZeroRectangle_subset,
  ``RiemannZeta.GuthMaynard.isCompact_ZeroRectangle,
  ``RiemannZeta.GuthMaynard.riemannZeta_finite_zeros_in_rect,
  ``RiemannZeta.GuthMaynard.zeroCountRect_nonneg,
  ``RiemannZeta.GuthMaynard.zerosInRect_subset_of_rect_subset,
  ``RiemannZeta.GuthMaynard.zeroCountRect_mono,
  ``RiemannZeta.GuthMaynard.zerosInRect_subset,
  ``RiemannZeta.GuthMaynard.zeroCountRect_split,
  ``RiemannZeta.GuthMaynard.riemannZeta_conj,
  ``RiemannZeta.GuthMaynard.iteratedDeriv_conj_conj,
  ``RiemannZeta.GuthMaynard.analyticOrderAt_conj_conj,
  ``RiemannZeta.GuthMaynard.analyticVanishingOrder_conj,
  ``RiemannZeta.GuthMaynard.zeroCountRect_neg_eq_pos,
  ``RiemannZeta.GuthMaynard.zeroCountRect_zero_two_pow_le,
  ``RiemannZeta.GuthMaynard.phragmen_lindelof_rhs_nonneg,
  ``RiemannZeta.GuthMaynard.zeta_growth_bound_native,
  ``RiemannZeta.GuthMaynard.euler_product_rhs_nonneg,
  ``RiemannZeta.GuthMaynard.zeta_lower_bound_native,
  ``RiemannZeta.GuthMaynard.mem_detectorDivisors,
  ``RiemannZeta.GuthMaynard.detectorDivisors_subset_range,
  ``RiemannZeta.GuthMaynard.detectorDivisors_subset_divisors,
  ``RiemannZeta.GuthMaynard.detectorDivisors_card_le_cutoff,
  ``RiemannZeta.GuthMaynard.norm_moebius_cast_le_one,
  ``RiemannZeta.GuthMaynard.norm_mobius_sum_le_cutoff,
  ``RiemannZeta.GuthMaynard.norm_mobius_sum_le_divisors_card,
  ``RiemannZeta.GuthMaynard.detectorCoeff_eq_zero_iff,
  ``RiemannZeta.GuthMaynard.exp_smoothing_bound,
  ``RiemannZeta.GuthMaynard.norm_detectorCoeff_le_cutoff,
  ``RiemannZeta.GuthMaynard.norm_detectorCoeff_le_divisors_card,
  ``RiemannZeta.GuthMaynard.detectorCoeff_bound,
  ``RiemannZeta.GuthMaynard.uniformDetectorCoeffBound_of_divisorCount,
  ``RiemannZeta.GuthMaynard.detectPoly_eval,
  ``RiemannZeta.GuthMaynard.admissibleDyadicScale_index_lt,
  ``RiemannZeta.GuthMaynard.mem_admissibleDyadicIndices,
  ``RiemannZeta.GuthMaynard.admissibleDyadicIndices_card_le,
  ``RiemannZeta.GuthMaynard.detectorScaleUpper_le_rpow,
  ``RiemannZeta.GuthMaynard.dyadicScaleIndexCount_le_log,
  ``RiemannZeta.GuthMaynard.typeII_exponent_pos,
  ``RiemannZeta.GuthMaynard.denom_pos,
  ``RiemannZeta.GuthMaynard.k_selection,
  ``RiemannZeta.GuthMaynard.eventually_detectorScaleUpper_sq_le,
  ``RiemannZeta.GuthMaynard.central_denominators_pos,
  ``RiemannZeta.GuthMaynard.alpha_pos,
  ``RiemannZeta.GuthMaynard.final_exponent_nonneg,
  ``RiemannZeta.GuthMaynard.first_term_exponent_identity,
  ``RiemannZeta.GuthMaynard.second_term_exponent_identity,
  ``RiemannZeta.GuthMaynard.third_term_exponent_identity,
  ``RiemannZeta.GuthMaynard.mean_value_exponent_le,
  ``RiemannZeta.GuthMaynard.large_values_first_term_le,
  ``RiemannZeta.GuthMaynard.large_values_second_term_le,
  ``RiemannZeta.GuthMaynard.large_values_third_term_le,
  ``RiemannZeta.GuthMaynard.mean_value_height_term_le,
  ``RiemannZeta.GuthMaynard.large_values_terms_le,
  ``RiemannZeta.GuthMaynard.mean_value_terms_le,
  ``RiemannZeta.GuthMaynard.residual_exponent_le_final,
  ``RiemannZeta.GuthMaynard.huxley_exponent_le_final,
  ``RiemannZeta.GuthMaynard.pow_coeff_rhs_nonneg,
  ``RiemannZeta.GuthMaynard.pow_coeff_subset,
  ``RiemannZeta.GuthMaynard.powCoeff_bound_of_uniform_detector_and_factorization,
  ``RiemannZeta.GuthMaynard.powCoeff_bound_of_divisor_and_factorization,
  ``RiemannZeta.GuthMaynard.powPoly_eval,
  ``RiemannZeta.GuthMaynard.prod_natCast_cpow_eq,
  ``RiemannZeta.GuthMaynard.powCoeff_product_mem_support,
  ``RiemannZeta.GuthMaynard.polynomial_power_identity,
  ``RiemannZeta.GuthMaynard.powCoeff_lower_endpoint_eq_zero,
  ``RiemannZeta.GuthMaynard.polynomial_power_identity_Ioc,
  ``RiemannZeta.GuthMaynard.wideDirichletPoly_eq_sum_blocks,
  ``RiemannZeta.GuthMaynard.exists_large_dyadic_block,
  ``RiemannZeta.GuthMaynard.wideDirichletPoly_poweredLineCoeffs,
  ``RiemannZeta.GuthMaynard.wideDirichletPoly_poweredLineCoeffs_translate,
  ``RiemannZeta.GuthMaynard.norm_poweredLineCoeffs_le,
  ``RiemannZeta.GuthMaynard.norm_phaseShift_normalizedPoweredCoeffs_le_one,
  ``RiemannZeta.GuthMaynard.wideDirichletPoly_normalizedPoweredCoeffs_translate,
  ``RiemannZeta.GuthMaynard.exists_dyadic_block_and_subset,
  ``RiemannZeta.GuthMaynard.normalized_powered_wide_lower,
  ``RiemannZeta.GuthMaynard.mean_value_pos,
  ``RiemannZeta.GuthMaynard.l2_norm_sq_nonneg,
  ``RiemannZeta.GuthMaynard.l2_norm_sq_zero_iff,
  ``RiemannZeta.GuthMaynard.montgomery_mean_value_rhs_nonneg,
  ``RiemannZeta.GuthMaynard.sum_sq_le_card_mul_sum_sq,
  ``RiemannZeta.GuthMaynard.complex_sum_sq_le_card_mul_sum_sq,
  ``RiemannZeta.GuthMaynard.pigeonhole_real_sum,
  ``RiemannZeta.GuthMaynard.separated_selection,
  ``RiemannZeta.GuthMaynard.weighted_separated_selection,
  ``RiemannZeta.GuthMaynard.typeI_add_residual_eq_total,
  ``RiemannZeta.GuthMaynard.chosenTypeIScale_spec,
  ``RiemannZeta.GuthMaynard.chosenTypeIScale_mem,
  ``RiemannZeta.GuthMaynard.sum_shiftedMultiplicity,
  ``RiemannZeta.GuthMaynard.shifted_bin_weight_le_of_unit_bin_weight,
  ``RiemannZeta.GuthMaynard.weighted_finite_pigeonhole,
  ``RiemannZeta.GuthMaynard.finite_weighted_extract_separated,
  ``RiemannZeta.GuthMaynard.detectPoly_eq_dirichletPoly,
  ``RiemannZeta.GuthMaynard.detectPoly_translate,
  ``RiemannZeta.GuthMaynard.norm_translatedDetectorCoeffs,
  ``RiemannZeta.GuthMaynard.rpow_mul_log_sq_le_epsilon,
  ``RiemannZeta.GuthMaynard.rawExtractSeparated_of_beta_shift_and_local_multiplicity,
  ``RiemannZeta.GuthMaynard.extractSeparated_of_beta_shift_and_local_multiplicity,
  ``RiemannZeta.GuthMaynard.cexp_periodic_1,
  ``RiemannZeta.GuthMaynard.cexp_zero_eval,
  ``RiemannZeta.GuthMaynard.psiCutoff_nonneg,
  ``RiemannZeta.GuthMaynard.psiCutoff_zero,
  ``RiemannZeta.GuthMaynard.psiCutoff_zero_right,
  ``RiemannZeta.GuthMaynard.psiCutoff_le_exp,
  ``RiemannZeta.GuthMaynard.psiCutoff_bounded_of_sigma_le_beta,
  ``RiemannZeta.GuthMaynard.norm_cexp_ofReal_mul_I,
  ``RiemannZeta.GuthMaynard.fourier_inversion_integrand_bound,
  ``RiemannZeta.GuthMaynard.fourier_decay_rhs_nonneg,
  ``RiemannZeta.GuthMaynard.beta_dependence_removal,
  ``RiemannZeta.GuthMaynard.monotonic_density_reduction,
  ``RiemannZeta.GuthMaynard.dyadicHeightIndex_spec,
  ``RiemannZeta.GuthMaynard.dyadicToGlobalZeroCount,
  ``RiemannZeta.GuthMaynard.uniform_powCoeff_bound_up_to_101,
  ``RiemannZeta.GuthMaynard.dirichletPoly_restrictToDyadicBlock,
  ``RiemannZeta.GuthMaynard.norm_restrictToDyadicBlock_le_one,
  ``RiemannZeta.GuthMaynard.dyadic_block_subset_powered_support,
  ``RiemannZeta.GuthMaynard.selected_block_coefficients,
  ``RiemannZeta.GuthMaynard.inverse_normalized_threshold_sq,
  ``RiemannZeta.GuthMaynard.inverse_normalized_threshold_fourth,
  ``RiemannZeta.GuthMaynard.section13_threshold_identity,
  ``RiemannZeta.GuthMaynard.eventually_log_pow_le_rpow,
  ``RiemannZeta.GuthMaynard.eventually_section13Loss_fourth_bound,
  ``RiemannZeta.GuthMaynard.selected_block_large_value_terms_le,
  ``RiemannZeta.GuthMaynard.selected_block_mean_value_terms_le,
  ``RiemannZeta.GuthMaynard.typeIPositiveSlabBound_of_section13_inputs,
  ``RiemannZeta.GuthMaynard.central_positive_slab_of_typeI_and_residual,
  ``RiemannZeta.GuthMaynard.high_sigma_of_huxley,
  ``RiemannZeta.GuthMaynard.conditionalZeroDensityTransfer,
  ``RiemannZeta.GuthMaynard.EpsilonPowerBound_mono,
  ``RiemannZeta.GuthMaynard.combined_zero_density_transfer_native,

  -- Production modules formerly omitted from the root import graph
  ``RiemannZeta.GuthMaynard.halasz_montgomery_rhs_nonneg,
  ``RiemannZeta.GuthMaynard.discrete_duality_cauchy_schwarz,
  ``RiemannZeta.GuthMaynard.halasz_montgomery_lemma_of_mean_value,
  ``RiemannZeta.GuthMaynard.weightedResidualCount_le_weightedCount_of_cover,
  ``RiemannZeta.GuthMaynard.residual_epsilonPowerBound_of_cover,
  ``RiemannZeta.GuthMaynard.EpsilonPowerBound.mul_left_rpow,
  ``RiemannZeta.GuthMaynard.scaled_twistedZetaFourthMoment_bound,
  ``RiemannZeta.GuthMaynard.residual_zero_bound_of_cover_reduction_and_fourth_moment,
  ``RiemannZeta.GuthMaynard.finiteTypeICover_of_typeIContourTypeII,
  ``RiemannZeta.GuthMaynard.weightedResidualCount_dyadicZetaZeros_eq,
  ``RiemannZeta.GuthMaynard.residualZeroBound_of_contourTypeII_reduction_and_fourthMoment,
  ``RiemannZeta.GuthMaynard.l2_decoupling_rhs_nonneg,
  ``RiemannZeta.GuthMaynard.l2_decoupling_bound_native
]

/-- The number printed by the audit, derived directly from its explicit list. -/
def auditedDeclarationCount : Nat := auditedDeclarations.size

private def isCompilerGeneratedTheorem (name : Name) : Bool :=
  let text := name.toString
  text.contains "._proof_" || text.contains ".eq_" || text.contains "._simp_"

private def exportedProjectTheorems (env : Environment) : Array Name := Id.run do
  let mut names := #[]
  for (name, info) in env.constants.toList do
    if name.getRoot == `RiemannZeta && info.isTheorem && !isCompilerGeneratedTheorem name then
      names := names.push name
  return names.qsort Name.quickLt

/-- Execute the synchronized, transitive dependency audit. -/
def runDependencyAudit : CoreM Unit := do
  let env ← getEnv
  let discovered := exportedProjectTheorems env
  let mut failures : Nat := 0

  logInfo m!"=== RIEMANN ZETA TRANSITIVE AXIOM AUDIT ==="
  logInfo m!"Explicit declarations: {auditedDeclarationCount}"
  logInfo m!"Discovered source-level theorems: {discovered.size}"
  logInfo m!"Permitted axioms: {permittedAxioms}"

  for name in discovered do
    if !auditedDeclarations.contains name then
      failures := failures + 1
      logInfo m!"FAIL [unlisted theorem] {name}"

  for name in auditedDeclarations do
    if !discovered.contains name then
      failures := failures + 1
      logInfo m!"FAIL [missing or non-theorem declaration] {name}"

  for i in [:auditedDeclarations.size] do
    let name := auditedDeclarations[i]!
    if (auditedDeclarations.extract 0 i).contains name then
      failures := failures + 1
      logInfo m!"FAIL [duplicate audit entry] {name}"

  for name in auditedDeclarations do
    if discovered.contains name then
      let axioms ← Lean.collectAxioms name
      let forbidden := axioms.filter fun axiomName => !permittedAxioms.contains axiomName
      if forbidden.isEmpty then
        logInfo m!"PASS {name}: {axioms}"
      else
        failures := failures + 1
        logInfo m!"FAIL {name}: forbidden dependencies {forbidden}; all axioms {axioms}"

  if failures == 0 then
    logInfo m!"AUDIT PASS: all {auditedDeclarationCount} declarations have permitted dependencies."
  else
    throwError "AUDIT FAIL: {failures} dependency or synchronization failure(s) across {auditedDeclarationCount} explicit declarations"

#eval runDependencyAudit
