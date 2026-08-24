import RiemannZeta.GuthMaynard.MediumTypeIEndpoint

open scoped BigOperators Topology
open Complex Real Filter MeasureTheory Set
open RiemannZeta.GuthMaynard

#check exists_signed_shift_large_normalized_reflected_wide
#check norm_typeIPowerReflectionIntegral_le_on_symmetric_window
#check exists_norm_typeIReflectedMellinIntegral_tail_le
#check exists_sourceScalar_zeroMode_decay
#check exists_sourceScalar_farModes_bound
#check select_common_signed_reflected_family
#check reflected_family_mhh_cardinality
#check positive_reflected_family_mhh_cardinality
#check endpoint_witness_count_le_of_mhh_power
#check endpoint_witness_count_le_of_mhh_power_factor
#check Finset.Ioc_union_Ioc_eq_Ioc
#check Finset.sum_union
#check Finset.sum_bij

open Complex Finset MeasureTheory Real Set
open scoped BigOperators
open RiemannZeta.GuthMaynard

example (sigma t : ℝ) (Q M : ℕ) :
    typeINormalizedNegativeModes sigma t Q M =
      typeINormalizedNegativeInterval sigma t Q 0 M := by
  unfold typeINormalizedNegativeModes typeINormalizedNegativeInterval
  congr 1

example (sigma t : ℝ) (Q L U M : ℕ) (hLU : L ≤ U) (hUM : U ≤ M) :
    typeINormalizedNegativeModes sigma t Q M =
      typeINormalizedNegativeInterval sigma t Q 0 L +
      typeINormalizedNegativeInterval sigma t Q L U +
      typeINormalizedNegativeInterval sigma t Q U M := by
  rw [show typeINormalizedNegativeModes sigma t Q M =
      typeINormalizedNegativeInterval sigma t Q 0 M by
    unfold typeINormalizedNegativeModes typeINormalizedNegativeInterval
    congr 1]
  unfold typeINormalizedNegativeInterval
  let f : ℕ → ℂ := fun m =>
    (Q : ℂ) * typeINormalizedFourier sigma t
      ((Q : ℝ) * (-(m : ℝ)))
  have hDisj₁ : Disjoint (Finset.Ioc 0 L) (Finset.Ioc L U) := by
    rw [Finset.disjoint_left]
    intro m hm₁ hm₂
    simp only [Finset.mem_Ioc] at hm₁ hm₂
    omega
  have hDisj₂ : Disjoint (Finset.Ioc 0 U) (Finset.Ioc U M) := by
    rw [Finset.disjoint_left]
    intro m hm₁ hm₂
    simp only [Finset.mem_Ioc] at hm₁ hm₂
    omega
  have hUnion₁ := Finset.Ioc_union_Ioc_eq_Ioc (a := 0) (Nat.zero_le L) hLU
  have hUnion₂ := Finset.Ioc_union_Ioc_eq_Ioc (a := 0) (Nat.zero_le U) hUM
  change (∑ m ∈ Finset.Ioc 0 M, f m) =
    (∑ m ∈ Finset.Ioc 0 L, f m) +
      (∑ m ∈ Finset.Ioc L U, f m) +
      ∑ m ∈ Finset.Ioc U M, f m
  rw [← hUnion₂, Finset.sum_union hDisj₂, ← hUnion₁,
    Finset.sum_union hDisj₁]

example {sigma t m : ℝ} (hm : 0 < m) :
    ‖typeIReflectionScaleFactor sigma t m‖ = m ^ (sigma - 1) := by
  unfold typeIReflectionScaleFactor
  rw [norm_mul, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hm, Complex.norm_exp,
    Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re,
    mul_zero, Complex.ofReal_im, Complex.I_im, sub_self, mul_one]
  rw [Real.exp_zero, mul_one]
  rw [show sigma * Real.log m = Real.log m * sigma by ring]
  rw [← Real.rpow_def_of_pos hm]
  rw [← Real.rpow_neg_one, ← Real.rpow_add hm]
  congr 1
  ring

example {sigma t Q : ℝ} (m : ℕ)
    (hsigma : 0 < sigma) (hQ : 0 < Q) (hm : 0 < m)
    (hleft : 4 * Real.pi * (m : ℝ) * Q < t) :
    ‖typeISourceNormalizationScalar sigma t Q *
        ((Q : ℂ) * typeINormalizedFourier sigma t
          (Q * (-(m : ℝ))))‖ ≤
      (m : ℝ) ^ (sigma - 1) *
        ((4 / (t - 4 * Real.pi * (m : ℝ) * Q)) *
          (((m : ℝ) * Q) / 2) ^ (-sigma)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [sourceScalar_mul_normalizedFourier_neg_eq_physicalIntegral
    sigma t Q m hQ]
  rw [typeIDyadicPhysicalIntegral_rescale hmR hQ (by positivity)
    (by linarith : Q / 2 ≤ 2 * Q)]
  rw [norm_mul]
  change ‖typeIReflectionScaleFactor sigma t (m : ℝ)‖ *
      ‖typeIPowerReflectionIntegral sigma t
        ((m : ℝ) * (Q / 2)) ((m : ℝ) * (2 * Q))‖ ≤ _
  rw [norm_typeIReflectionScaleFactor hmR]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hmR.le _)
  have hMQ : 0 < (m : ℝ) * Q := mul_pos hmR hQ
  have hA : 0 < ((m : ℝ) * Q) / 2 := by positivity
  have hAB : ((m : ℝ) * Q) / 2 ≤ (m : ℝ) * (2 * Q) := by nlinarith
  have hleft' : 2 * Real.pi * ((m : ℝ) * (2 * Q)) < t := by
    nlinarith
  have h := norm_powerWeighted_gmReflectionIntegral_le_left
    hsigma hA hAB hleft'
  convert h using 1 <;> ring
