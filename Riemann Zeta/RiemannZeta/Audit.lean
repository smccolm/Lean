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
  ``RiemannZeta.GuthMaynard.abelZetaKernel_eq_of_one_lt,
  ``RiemannZeta.GuthMaynard.abelZetaKernel_eq_zero_of_le_one,
  ``RiemannZeta.GuthMaynard.norm_abelZetaKernel_le_one,
  ``RiemannZeta.GuthMaynard.measurable_abelZetaKernel,
  ``RiemannZeta.GuthMaynard.locallyIntegrableOn_abelZetaKernel,
  ``RiemannZeta.GuthMaynard.abelZetaKernel_isBigO_atTop,
  ``RiemannZeta.GuthMaynard.abelZetaKernel_isBigO_zero,
  ``RiemannZeta.GuthMaynard.differentiableAt_abelZetaRemainder,
  ``RiemannZeta.GuthMaynard.mellinConvergent_abelZetaKernel,
  ``RiemannZeta.GuthMaynard.abelZetaRemainder_eq_integral,
  ``RiemannZeta.GuthMaynard.integrableOn_abelZetaRemainder_integrand,
  ``RiemannZeta.GuthMaynard.differentiableAt_regularizedRiemannZeta,
  ``RiemannZeta.GuthMaynard.differentiableAt_regularizedAbelZeta,
  ``RiemannZeta.GuthMaynard.sum_one_Icc,
  ``RiemannZeta.GuthMaynard.sum_one_Icc_isBigO,
  ``RiemannZeta.GuthMaynard.natFloor_cast_complex,
  ``RiemannZeta.GuthMaynard.integral_Ioi_cpow_neg,
  ``RiemannZeta.GuthMaynard.riemannZeta_eq_abel_of_one_lt_re,
  ``RiemannZeta.GuthMaynard.regularized_zeta_eq_abel_of_one_lt_re,
  ``RiemannZeta.GuthMaynard.regularized_zeta_eq_abel,
  ``RiemannZeta.GuthMaynard.riemannZeta_eq_abel,
  ``RiemannZeta.GuthMaynard.norm_abelZetaRemainder_le,
  ``RiemannZeta.GuthMaynard.norm_riemannZeta_le_five_mul_norm,
  ``RiemannZeta.GuthMaynard.mem_ZeroRectangle,
  ``RiemannZeta.GuthMaynard.ZeroRectangle_subset,
  ``RiemannZeta.GuthMaynard.isCompact_ZeroRectangle,
  ``RiemannZeta.GuthMaynard.finset_analyticVanishingOrder_le_finsum_divisor,
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
  ``RiemannZeta.GuthMaynard.zeta_two_norm_lt_five_thirds,
  ``RiemannZeta.GuthMaynard.zeta_right_half_plane_bound,
  ``RiemannZeta.GuthMaynard.zeta_jensen_sphere_bound,
  ``RiemannZeta.GuthMaynard.zeta_jensen_rhs_nonneg,
  ``RiemannZeta.GuthMaynard.zeta_growth_bound_native,
  ``RiemannZeta.GuthMaynard.moebius_coeff_norm_le_one,
  ``RiemannZeta.GuthMaynard.moebius_LSeries_norm_lt_five_thirds,
  ``RiemannZeta.GuthMaynard.euler_product_lower_bound_2,
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
  ``RiemannZeta.GuthMaynard.exponent_succ_le_const_mul_two_rpow,
  ``RiemannZeta.GuthMaynard.exponent_succ_le_large_prime_rpow,
  ``RiemannZeta.GuthMaynard.divisorCountBound_native,
  ``RiemannZeta.GuthMaynard.factorizationCountBound_native,
  ``RiemannZeta.GuthMaynard.powCoeffBound_native,
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
  ``RiemannZeta.GuthMaynard.integral_cexp_int,
  ``RiemannZeta.GuthMaynard.integral_conj_fourier_term_mul_fourier_term,
  ``RiemannZeta.GuthMaynard.integral_conj_trigPoly_mul_trigPoly,
  ``RiemannZeta.GuthMaynard.integral_norm_sq_trigPoly,
  ``RiemannZeta.GuthMaynard.continuous_trigPoly,
  ``RiemannZeta.GuthMaynard.integral_sawtooth_cexp,
  ``RiemannZeta.GuthMaynard.integral_sawtooth_cexp_all,
  ``RiemannZeta.GuthMaynard.hilbertForm_norm_le,
  ``RiemannZeta.GuthMaynard.nat_hilbertForm_norm_le,
  ``RiemannZeta.GuthMaynard.integral_sawtooth_conj_fourier_mul_fourier,
  ``RiemannZeta.GuthMaynard.integral_sawtooth_conj_trigPoly_mul_trigPoly,
  ``RiemannZeta.GuthMaynard.norm_sawtooth_conj_trigPoly_mul_trigPoly_le,
  ``RiemannZeta.GuthMaynard.abs_inv_log_sub_sub_div_le_one,
  ``RiemannZeta.GuthMaynard.norm_complex_log_kernel_error_le_one,
  ``RiemannZeta.GuthMaynard.logHilbertQuad_eq_main_add_error,
  ``RiemannZeta.GuthMaynard.logKernelErrorQuad_norm_le,
  ``RiemannZeta.GuthMaynard.natMainQuad_eq_scaled_hilbert,
  ``RiemannZeta.GuthMaynard.natScaledCoeff_l2_le,
  ``RiemannZeta.GuthMaynard.natMainQuad_norm_le,
  ``RiemannZeta.GuthMaynard.logHilbertQuad_norm_le,
  ``RiemannZeta.GuthMaynard.norm_endpointTwist,
  ``RiemannZeta.GuthMaynard.integral_conj_dirichlet_term_mul_dirichlet_term,
  ``RiemannZeta.GuthMaynard.integral_conj_dirichletTime_mul_dirichletTime,
  ``RiemannZeta.GuthMaynard.continuous_dirichletTime,
  ``RiemannZeta.GuthMaynard.ofReal_integral_norm_sq_dirichletTime,
  ``RiemannZeta.GuthMaynard.integral_norm_sq_dirichletTime_le,
  ``RiemannZeta.GuthMaynard.local_sample_le_energy,
  ``RiemannZeta.GuthMaynard.sum_local_intervalIntegrals_le,
  ``RiemannZeta.GuthMaynard.centeredDirichletTime_eq,
  ``RiemannZeta.GuthMaynard.norm_centeredDirichletTime,
  ``RiemannZeta.GuthMaynard.hasDerivAt_centeredDirichletTime,
  ``RiemannZeta.GuthMaynard.differentiable_centeredDirichletTime,
  ``RiemannZeta.GuthMaynard.deriv_centeredDirichletTime,
  ``RiemannZeta.GuthMaynard.continuous_deriv_centeredDirichletTime,
  ``RiemannZeta.GuthMaynard.abs_log_ratio_le_one,
  ``RiemannZeta.GuthMaynard.centeredDerivCoeff_l2_le,
  ``RiemannZeta.GuthMaynard.nat_cpow_neg_mul_I_eq,
  ``RiemannZeta.GuthMaynard.montgomery_mean_value_estimate,
  ``RiemannZeta.GuthMaynard.montgomery_mean_value_native,
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
  ``RiemannZeta.GuthMaynard.typeI_unit_bin_sum_le_jensen,
  ``RiemannZeta.GuthMaynard.localZeroMultiplicityBound_native,
  ``RiemannZeta.GuthMaynard.rpow_mul_log_sq_le_epsilon,
  ``RiemannZeta.GuthMaynard.rawExtractSeparated_of_beta_shift_and_local_multiplicity,
  ``RiemannZeta.GuthMaynard.extractSeparated_of_beta_shift_and_local_multiplicity,
  ``RiemannZeta.GuthMaynard.extractSeparated_of_beta_shift,
  ``RiemannZeta.GuthMaynard.norm_detectPoly_le_detectorMass,
  ``RiemannZeta.GuthMaynard.differentiable_detectPoly_add,
  ``RiemannZeta.GuthMaynard.localizer_norm_le_one,
  ``RiemannZeta.GuthMaynard.localizedDetector_le_detectorMass,
  ``RiemannZeta.GuthMaynard.localizedDetector_halfPlane_bound,
  ``RiemannZeta.GuthMaynard.localizer_norm_boundary_le,
  ``RiemannZeta.GuthMaynard.exists_nearby_large_value,
  ``RiemannZeta.GuthMaynard.detectorCutoff_le_three_mul,
  ``RiemannZeta.GuthMaynard.detectorMass_le_pow_seven,
  ``RiemannZeta.GuthMaynard.localizer_factor_gt_three_fourths,
  ``RiemannZeta.GuthMaynard.detectorMass_mul_localizer_lt,
  ``RiemannZeta.GuthMaynard.beta_dependence_removal,
  ``RiemannZeta.GuthMaynard.extractSeparated_native,
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

  -- Classical density foundations and proved endpoint boundary cases
  ``RiemannZeta.GuthMaynard.mollifiedZetaCoeff_eq_ite,
  ``RiemannZeta.GuthMaynard.mollifiedZetaCoeff_eq_zero,
  ``RiemannZeta.GuthMaynard.truncatedMoebius_apply,
  ``RiemannZeta.GuthMaynard.truncatedMoebius_hasFiniteSupport,
  ``RiemannZeta.GuthMaynard.truncatedMoebius_LSeriesSummable,
  ``RiemannZeta.GuthMaynard.zetaMollifier_eq_LSeries,
  ``RiemannZeta.GuthMaynard.zeta_mul_truncatedMoebius_apply,
  ``RiemannZeta.GuthMaynard.riemannZeta_mul_zetaMollifier_eq_LSeries,
  ``RiemannZeta.GuthMaynard.mollifiedZetaErrorCoeff_eq_zero,
  ``RiemannZeta.GuthMaynard.LSeriesSummable_delta,
  ``RiemannZeta.GuthMaynard.mollifiedZetaCoeff_LSeriesSummable,
  ``RiemannZeta.GuthMaynard.mollifiedZetaError_eq_LSeries,
  ``RiemannZeta.GuthMaynard.inghamZeroDetector_eq_one_sub_sq,
  ``RiemannZeta.GuthMaynard.regularizedInghamZeroDetector_of_ne,
  ``RiemannZeta.GuthMaynard.analyticAt_zetaMollifier,
  ``RiemannZeta.GuthMaynard.analytic_regularizedInghamZeroDetector,
  ``RiemannZeta.GuthMaynard.tendsto_natCast_cpow_neg_ofReal_atTop,
  ``RiemannZeta.GuthMaynard.tendsto_zetaMollifier_ofReal_atTop,
  ``RiemannZeta.GuthMaynard.exists_zetaMollifier_ofReal_ne_zero,
  ``RiemannZeta.GuthMaynard.zetaMollifier_analyticOrderAt_ne_top,
  ``RiemannZeta.GuthMaynard.analyticAt_mollifiedZetaError,
  ``RiemannZeta.GuthMaynard.analyticAt_inghamZeroDetector,
  ``RiemannZeta.GuthMaynard.riemannZeta_analyticOrderAt_ne_top,
  ``RiemannZeta.GuthMaynard.inghamZeroDetector_eq_zero_of_zeta_eq_zero,
  ``RiemannZeta.GuthMaynard.analyticVanishingOrder_zeta_le_inghamZeroDetector,
  ``RiemannZeta.GuthMaynard.analyticVanishingOrder_regularizedInghamZeroDetector_eq,
  ``RiemannZeta.GuthMaynard.analyticVanishingOrder_zeta_le_regularizedInghamZeroDetector,
  ``RiemannZeta.GuthMaynard.sum_zeta_multiplicity_le_regularizedInghamZeroDetector,
  ``RiemannZeta.GuthMaynard.sum_zeta_multiplicity_le_of_regularizedInghamZeroDetector_bound,
  ``RiemannZeta.GuthMaynard.zerosInRect_one_eq_empty,
  ``RiemannZeta.GuthMaynard.N_one,
  ``RiemannZeta.GuthMaynard.epsilonPowerBound_zero,
  ``RiemannZeta.GuthMaynard.ingham_zero_density_at_one_native,
  ``RiemannZeta.GuthMaynard.huxley_zero_density_at_one_native,
  ``RiemannZeta.GuthMaynard.zeroUnitBin_multiplicity_le_jensen,
  ``RiemannZeta.GuthMaynard.zeroCountRect_dyadic_le_jensen,
  ``RiemannZeta.GuthMaynard.dyadic_zero_count_epsilon_one,
  ``RiemannZeta.GuthMaynard.global_zero_count_epsilon_one,
  ``RiemannZeta.GuthMaynard.ingham_zero_density_at_half_native,
  ``RiemannZeta.GuthMaynard.logHilbertQuadUpTo_eq_main_add_error,
  ``RiemannZeta.GuthMaynard.logKernelErrorQuadUpTo_norm_le,
  ``RiemannZeta.GuthMaynard.natMainQuadUpTo_eq_scaled_hilbert,
  ``RiemannZeta.GuthMaynard.natScaledCoeffUpTo_l2_le,
  ``RiemannZeta.GuthMaynard.natMainQuadUpTo_norm_le,
  ``RiemannZeta.GuthMaynard.logHilbertQuadUpTo_norm_le,
  ``RiemannZeta.GuthMaynard.integral_conj_dirichletTimeUpTo_mul_dirichletTimeUpTo,
  ``RiemannZeta.GuthMaynard.continuous_dirichletTimeUpTo,
  ``RiemannZeta.GuthMaynard.ofReal_integral_norm_sq_dirichletTimeUpTo,
  ``RiemannZeta.GuthMaynard.integral_norm_sq_dirichletTimeUpTo_le,
  ``RiemannZeta.GuthMaynard.zetaMollifier_criticalLine_eq_dirichletTimeUpTo,
  ``RiemannZeta.GuthMaynard.norm_mollifierCriticalCoeff_sq_le_inv,
  ``RiemannZeta.GuthMaynard.mollifierCriticalCoeff_l2_le_harmonic,
  ``RiemannZeta.GuthMaynard.integral_norm_sq_zetaMollifier_criticalLine_le,
  ``RiemannZeta.GuthMaynard.norm_riemannZeta_le_twenty_mul_abs_im_on_classical_strip,
  ``RiemannZeta.GuthMaynard.analytic_rectangle_logDeriv_integral_eq_order_sum,
  ``RiemannZeta.GuthMaynard.regularizedInghamZeroDetector_rectangle_argumentPrinciple,

  -- Vendored PNT+ rectangle and argument-principle infrastructure
  ``MeromorphicOn.exists_nonzero_seq_divisor_support_diff_zero,
  ``mem_Rect,
  ``mapsTo_rectangle_left_re,
  ``mapsTo_rectangleBorder_right_re,
  ``Square_apply,
  ``ContinuousOn.rectangleBorderNoPIntegrable,
  ``Set.ne_left_of_mem_uIoo,
  ``square_subset_square,
  ``RectanglePullToNhdOfPole'',
  ``ResidueTheoremAtOrigin',
  ``Rectangle.symm,
  ``logDeriv_hasSimplePolesOn_of_meromorphicOrderAt_ne_top,
  ``HolomorphicOn.rectangleBorderIntegrable,
  ``segment_reProdIm_segment_eq_convexHull,
  ``RectangleIntegralHSplit',
  ``RectangleIntegral_congr,
  ``integral_const_div_sq_add_sq,
  ``HIntegral_symm,
  ``residue_eq_of_tendsto,
  ``mapsTo_rectangle_left_im_NoP,
  ``RectangleBorderIntegrable.add,
  ``RectangleIntegral.const_smul,
  ``rectangle_argumentChange_eq_two_pi_sum_meromorphicOrderAt,
  ``mapsTo_rectangleBorder_right_im,
  ``rectangle_subset_punctured_rect,
  ``ResidueTheoremAtOrigin_aux1c',
  ``ResidueTheoremAtOrigin_aux2c',
  ``rectangleBorder_subset_rectangle,
  ``simplePole_sub_residue_isBigO_one,
  ``sumResiduesIn_inter_eq_of_set_eq,
  ``RectSubRect',
  ``verticalPath_not_eventuallyConst,
  ``RectangleIntegral'_congr,
  ``mapsTo_rectangleBorder_left_im,
  ``residue_eq_zero_of_not_pole_of_meromorphicAt,
  ``rectangle_mem_nhds_iff,
  ``ContinuousOn.rectangleBorder_integrable,
  ``integral_const_div_self_add_im,
  ``Complex.inv_re_add_im,
  ``RectanglePullToNhdOfPole,
  ``RectangleIntegralVSplit,
  ``continuous_self_div_sq_add_sq,
  ``HolomorphicOn.rectangleBorderIntegrable',
  ``MeromorphicOn.divisor_support_inter_compact_finite,
  ``ContinuousLinearEquiv.coe_toLinearEquiv_symm,
  ``existsDifferentiableOn_of_bddAbove,
  ``SmallSquareInRectangle,
  ``verticalIntegral_split_three,
  ``rectangle_disjoint_singleton,
  ``ResidueTheoremAtOrigin,
  ``rectangleIntegral_symm,
  ``rectangleIntegral_symm_re,
  ``mapsTo_rectangleBorder_left_re,
  ``RectangleIntegralVSplit',
  ``MeromorphicOn.exists_ball_inter_divisor_support_eq_singleton,
  ``square_neg,
  ``MeromorphicOn.divisor_support_discrete,
  ``VIntegral_symm,
  ``MeromorphicOn.exists_seq_eq_range_divisor_support,
  ``divisor_support_rectangle_finite,
  ``logDeriv_sub_principal_isBigO_one_of_meromorphicOrderAt,
  ``preimage_equivRealProdCLM_reProdIm,
  ``left_mem_rect,
  ``HasSimplePolesOn.mono,
  ``logDeriv_poles_eq_divisor_support,
  ``mapsTo_rectangle_left_im,
  ``ResidueTheoremAtOrigin_aux2c,
  ``RectangleIntegralHSplit,
  ``RectangleIntegral.translate',
  ``rect_subset_iff,
  ``residue_analyticAt_eq_zero,
  ``Set.ne_right_of_mem_uIoo,
  ``Complex.nhds_hasBasis_square,
  ``right_mem_rect,
  ``integral_const_div_re_add_self,
  ``rectangleBorder_disjoint_singleton,
  ``Set.left_not_mem_uIoo,
  ``RectanglePullToNhdOfPole',
  ``square_mem_nhds,
  ``RectSubRect,
  ``mapsTo_rectangle_right_re,
  ``ContinuousOn.rectangleBorderIntegrable,
  ``IsBigO_to_BddAbove,
  ``RectangleIntegral'_eq_sumResiduesIn,
  ``ResidueTheoremOnRectangleWithSimplePole',
  ``logDeriv_residue_eq_meromorphicOrderAt,
  ``rectangleIntegral_logDeriv_eq_sum_meromorphicOrderAt,
  ``rectangle_in_convex,
  ``RectangleIntegral.translate,
  ``not_mem_rectangleBorder_of_rectangle_mem_nhds,
  ``mapsTo_rectangle_right_im_NoP,
  ``mapsTo_rectangle_left_re_NoP,
  ``ResidueTheoremOnRectangleWithSimplePole,
  ``HolomorphicOn.vanishesOnRectangle,
  ``RectangleIntegral.const_mul',
  ``rectangleBorder_subset_punctured_rect,
  ``MeromorphicOn.divisor_support_countable,
  ``ResidueTheoremAtOrigin_aux1c,
  ``ResidueTheoremInRectangle,
  ``DiffVertRect_eq_UpperLowerUs,
  ``Rectangle.symm_re,
  ``mapsTo_rectangle_right_re_NoP,
  ``Set.right_not_mem_uIoo,
  ``mapsTo_rectangle_right_im,
  ``sq_add_sq_ne_zero,
  ``BddAbove_on_rectangle_of_bdd_near,
  ``integral_self_div_sq_add_sq,

  -- Production modules formerly omitted from the root import graph
  ``RiemannZeta.GuthMaynard.halasz_montgomery_rhs_nonneg,
  ``RiemannZeta.GuthMaynard.discrete_duality_cauchy_schwarz,
  ``RiemannZeta.GuthMaynard.halasz_montgomery_lemma_of_mean_value,
  ``RiemannZeta.GuthMaynard.halasz_montgomery_lemma_native,
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

/-- Vendored PNT+ modules are production proof infrastructure even though the
upstream declarations intentionally extend root namespaces. -/
private def auditedExternalModules : Array Name := #[
  `RiemannZeta.External.PNT.Rectangle,
  `RiemannZeta.External.PNT.DivisorSupport,
  `RiemannZeta.External.PNT.ResidueCalcOnRectangles,
  `RiemannZeta.External.PNT.RectangleArgumentPrinciple
]

private def isFromAuditedExternalModule (env : Environment) (name : Name) : Bool :=
  match env.getModuleIdxFor? name with
  | none => false
  | some moduleIdx =>
      auditedExternalModules.contains env.header.modules[moduleIdx.toNat]!.module

private def exportedProjectTheorems (env : Environment) : Array Name := Id.run do
  let mut names := #[]
  for (name, info) in env.constants.toList do
    if (name.getRoot == `RiemannZeta || isFromAuditedExternalModule env name) &&
        info.isTheorem && !isPrivateName name && !isCompilerGeneratedTheorem name then
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
