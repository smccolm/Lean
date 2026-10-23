import Dubon2026.SourceCurveLocalResidueUniqueness

/-! DUB-17/18 -> canonical degree in residue characteristic -> global residues
-> residue/trace compatibility. At rational places, the existing finite
principal-part induction bounds the image modulo integral functions by a
finite span of pure poles. This avoids constructing general coefficient-field
sections in a completion for this local finite-rank step. -/

noncomputable section

namespace Dubon2026.SourceCurve.Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

/-- A cleared pole of order at most `n` has a class spanned by the first `n` pure poles. -/
theorem poleClass_mem_span_of_clear_pole
    (hres : Function.Surjective (algebraMap K v.ResidueField)) (n : ℕ) (f : F)
    (hf : v.uniformizer ^ n * f ∈ v.toValuationSubring) :
    v.integralFunctions.mkQ f ∈ Submodule.span K (v.poleClass '' Set.Iio n) := by
  induction n generalizing f with
  | zero =>
      have hf' : f ∈ v.integralFunctions := by simpa using hf
      rw [show v.integralFunctions.mkQ f = 0 from
        (Submodule.Quotient.mk_eq_zero _).mpr hf']
      exact Submodule.zero_mem _
  | succ n ih =>
      have hfg : v.uniformizer * (v.uniformizer ^ n * f) ∈ v.toValuationSubring := by
        simpa only [pow_succ, mul_assoc, mul_left_comm] using hf
      obtain ⟨c, _, hc⟩ := v.exists_integral_sub_simplePole hres (v.uniformizer ^ n * f) hfg
      have hrem : v.uniformizer ^ n * (f - c • v.uniformizer ^ (-(n + 1 : ℤ))) ∈
          v.toValuationSubring := by
        rw [mul_sub, Algebra.smul_def, mul_left_comm (v.uniformizer ^ n),
          v.uniformizer_pow_mul_neg_pow]
        simpa only [Algebra.smul_def] using hc
      have hsmall := ih _ hrem
      have hlarge : v.integralFunctions.mkQ
          (f - c • v.uniformizer ^ (-(n + 1 : ℤ))) ∈
          Submodule.span K (v.poleClass '' Set.Iio (n + 1)) :=
        Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio (Nat.le_succ n))) hsmall
      have hpole : v.poleClass n ∈ Submodule.span K (v.poleClass '' Set.Iio (n + 1)) :=
        Submodule.subset_span ⟨n, Nat.lt_succ_self n, rfl⟩
      have hadd := Submodule.add_mem _ hlarge (Submodule.smul_mem _ c hpole)
      simpa only [map_sub, map_smul, Submodule.mkQ_apply, poleClass, sub_add_cancel] using hadd

/-- The actual quotient by integral functions is spanned by its pure pole classes. -/
theorem poleClass_span_eq_top
    (hres : Function.Surjective (algebraMap K v.ResidueField)) :
    Submodule.span K (Set.range v.poleClass) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective v.integralFunctions x
  exact Submodule.span_mono (Set.image_subset_range _ _)
    (v.poleClass_mem_span_of_clear_pole hres _ f (v.clear_pole_mem f))

/-- The coefficient map from finite pure-pole sums to the actual quotient is bijective. -/
theorem poleClass_linearCombination_bijective
    (hres : Function.Surjective (algebraMap K v.ResidueField)) :
    Function.Bijective (Finsupp.linearCombination K v.poleClass) := by
  refine ⟨v.poleClass_linearIndependent, ?_⟩
  rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination,
    v.poleClass_span_eq_top hres]

end Dubon2026.SourceCurve.Place
