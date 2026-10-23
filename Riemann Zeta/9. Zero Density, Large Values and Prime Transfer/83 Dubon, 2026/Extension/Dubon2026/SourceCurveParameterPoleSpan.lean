import Dubon2026.SourceCurveParameterApproximation

/-! The actual quotient by integral functions is spanned by the pure
poles in a specified order-one coordinate. Reuse the existing finite-pole
induction with the proved parameter approximation. This supports the exact
rational-coordinate residue calculation needed for DUB-17/18. -/

noncomputable section

namespace Dubon2026.SourceCurve.Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {t : F}

/-- A cleared pole of order at most `n` has a class spanned by the first `n` pure poles. -/
theorem parameterPoleClass_mem_span_of_clear_pole (ht : v.ord t = 1)
    (hres : Function.Surjective (algebraMap K v.ResidueField)) (n : ℕ) (f : F)
    (hf : t ^ n * f ∈ v.toValuationSubring) :
    v.integralFunctions.mkQ f ∈ Submodule.span K ((v.parameterPoleClass t) '' Set.Iio n) := by
  induction n generalizing f with
  | zero =>
      have hf' : f ∈ v.integralFunctions := by simpa using hf
      rw [show v.integralFunctions.mkQ f = 0 from
        (Submodule.Quotient.mk_eq_zero _).mpr hf']
      exact Submodule.zero_mem _
  | succ n ih =>
      have hfg : t * (t ^ n * f) ∈ v.toValuationSubring := by
        simpa only [pow_succ, mul_assoc, mul_left_comm] using hf
      obtain ⟨c, hc⟩ := v.exists_integral_sub_parameterPole ht hres (t ^ n * f) hfg
      have hrem : t ^ n * (f - c • t ^ (-(n + 1 : ℤ))) ∈
          v.toValuationSubring := by
        rw [mul_sub, Algebra.smul_def, mul_left_comm (t ^ n),
          v.parameter_pow_mul_neg_pow ht]
        simpa only [Algebra.smul_def] using hc
      have hsmall := ih _ hrem
      have hlarge : v.integralFunctions.mkQ
          (f - c • t ^ (-(n + 1 : ℤ))) ∈
          Submodule.span K ((v.parameterPoleClass t) '' Set.Iio (n + 1)) :=
        Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio (Nat.le_succ n))) hsmall
      have hpole : (v.parameterPoleClass t) n ∈ Submodule.span K ((v.parameterPoleClass t) '' Set.Iio (n + 1)) :=
        Submodule.subset_span ⟨n, Nat.lt_succ_self n, rfl⟩
      have hadd := Submodule.add_mem _ hlarge (Submodule.smul_mem _ c hpole)
      simpa only [map_sub, map_smul, Submodule.mkQ_apply, parameterPoleClass, sub_add_cancel] using hadd

/-- The actual quotient by integral functions is spanned by its pure pole classes. -/
theorem parameterPoleClass_span_eq_top (ht : v.ord t = 1)
    (hres : Function.Surjective (algebraMap K v.ResidueField)) :
    Submodule.span K (Set.range (v.parameterPoleClass t)) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective v.integralFunctions x
  exact Submodule.span_mono (Set.image_subset_range _ _)
    (v.parameterPoleClass_mem_span_of_clear_pole ht hres _ f (v.parameter_clear_pole_mem ht f))

/-- The coefficient map from finite pure-pole sums to the actual quotient is bijective. -/
theorem parameterPoleClass_linearCombination_bijective (ht : v.ord t = 1)
    (hres : Function.Surjective (algebraMap K v.ResidueField)) :
    Function.Bijective (Finsupp.linearCombination K (v.parameterPoleClass t)) := by
  refine ⟨v.parameterPoleClass_linearIndependent ht, ?_⟩
  rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination,
    v.parameterPoleClass_span_eq_top ht hres]

end Dubon2026.SourceCurve.Place
