import Dubon2026.RealAutomorphicLift
import Mathlib.Analysis.Complex.Circle
import Mathlib.RepresentationTheory.Tannaka

/-! # The actual compact weight character and finite-dimensional compact orbit -/

namespace Dubon2026

noncomputable section
open UpperHalfPlane Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm ComplexConjugate

/-- The genuine compact subgroup fixing the base point in the real upper half-plane. -/
def realCompactSubgroup : Subgroup SL(2, ℝ) := MulAction.stabilizer SL(2, ℝ) I

/-- Compactness follows from the proper real-group orbit map. -/
theorem realCompactSubgroup_isCompact : IsCompact (realCompactSubgroup : Set SL(2, ℝ)) := by
  convert isProperMap_smul_I.isCompact_preimage (isCompact_singleton (x := I)) using 1

/-- The original denominator on the compact stabilizer has exact unit absolute value. -/
theorem realCompactSubgroup_denom_norm (h : realCompactSubgroup) :
    ‖denom (mapGL ℝ h.val) I‖ = 1 := by
  have hh : h.val • I = I := h.property
  have hi := UpperHalfPlane.im_smul_eq_div_normSq (mapGL ℝ h.val) I
  have he : (mapGL ℝ h.val) • I = I := hh
  rw [he] at hi
  have hn : Complex.normSq (denom (mapGL ℝ h.val) I) = 1 := by
    have heq : (Complex.normSq (denom (mapGL ℝ h.val) I))⁻¹ = 1 := by
      simpa using hi.symm
    exact inv_eq_one.mp heq
  rw [Complex.normSq_eq_norm_sq] at hn
  nlinarith [norm_nonneg (denom (mapGL ℝ h.val) I)]

/-- The precise unitary compact character associated to the original integral weight. -/
def realCompactWeight (k : ℤ) : realCompactSubgroup →* Circle where
  toFun h := ⟨denom (mapGL ℝ h.val) I ^ (-k), by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_zpow, realCompactSubgroup_denom_norm, one_zpow]⟩
  map_one' := by
    apply Subtype.ext
    simp [denom]
  map_mul' g h := by
    apply Subtype.ext
    change denom (mapGL ℝ (g.val * h.val)) I ^ (-k) =
      denom (mapGL ℝ g.val) I ^ (-k) * denom (mapGL ℝ h.val) I ^ (-k)
    rw [map_mul, denom_cocycle_σ]
    have hh : (mapGL ℝ h.val) • I = I := h.property
    simp [hh, UpperHalfPlane.σ, mul_zpow, mul_comm]

/-- The actual compact weight character varies continuously on the genuine stabilizer. -/
theorem realCompactWeight_continuous (k : ℤ) : Continuous (realCompactWeight k) := by
  apply Continuous.subtype_mk
  have hd : Continuous (fun h : realCompactSubgroup => denom (mapGL ℝ h.val) I) :=
    denom_continuous.comp (((continuous_mapGL (R := ℝ) (S := ℝ)).comp
      continuous_subtype_val).prodMk continuous_const)
  exact hd.zpow₀ (-k) (fun h => Or.inl (denom_ne_zero (mapGL ℝ h.val) I))

/-- The actual real-group lift is a compact-character eigenvector in the genuine right regular representation. -/
theorem realWeightLift_rightRegular (k : ℤ) (f : ℍ → ℂ) (h : realCompactSubgroup) :
    TannakaDuality.FiniteGroup.rightRegular (k := ℂ) h.val (realWeightLift k f) =
      (realCompactWeight k h : ℂ) • realWeightLift k f := by
  ext g
  change realWeightLift k f (g * h.val) =
    (denom (mapGL ℝ h.val) I ^ (-k)) * realWeightLift k f g
  rw [realWeightLift_right_stabilizer k f g h.val h.property, mul_comm]

/-- The full compact orbit of the actual lift spans exactly its original line. -/
theorem realWeightLift_compact_span (k : ℤ) (f : ℍ → ℂ) :
    Submodule.span ℂ (Set.range (fun h : realCompactSubgroup =>
      TannakaDuality.FiniteGroup.rightRegular (k := ℂ) h.val (realWeightLift k f))) =
      Submodule.span ℂ {realWeightLift k f} := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨h, rfl⟩
    dsimp only
    rw [realWeightLift_rightRegular]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · apply Submodule.span_le.mpr
    intro v hv
    have he : v = realWeightLift k f := Set.mem_singleton_iff.mp hv
    rw [he]
    apply Submodule.subset_span
    refine ⟨1, ?_⟩
    ext g
    simp

/-- For every nonzero original function, the genuine compact orbit has dimension exactly one. -/
theorem realWeightLift_compact_finrank (k : ℤ) {f : ℍ → ℂ} (hf : f ≠ 0) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range (fun h : realCompactSubgroup =>
      TannakaDuality.FiniteGroup.rightRegular (k := ℂ) h.val (realWeightLift k f)))) = 1 := by
  rw [realWeightLift_compact_span]
  apply finrank_span_singleton
  intro he
  apply hf
  apply realWeightLift_injective k
  rw [he]
  ext g
  simp [realWeightLift_apply]

end
end Dubon2026
