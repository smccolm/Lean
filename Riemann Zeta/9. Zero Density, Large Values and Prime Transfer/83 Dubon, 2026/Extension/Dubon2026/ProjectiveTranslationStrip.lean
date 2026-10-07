import Dubon2026.ModularGamma0Domain

/-! # The actual translation strip for projective Γ₀ -/

namespace Dubon2026

open UpperHalfPlane Matrix.SpecialLinearGroup CongruenceSubgroup ModularGroup MeasureTheory Set
open scoped MatrixGroups

noncomputable section

/-- Translation by one belongs to every actual Γ₀ level. -/
theorem modular_T_mem_gamma0 (Q : ℕ) : T ∈ Gamma0 Q := by
  simp [Gamma0_mem, ModularGroup.coe_T]

/-- The actual projective translation matrix, viewed inside projective Γ₀. -/
def gamma0ProjectiveT (Q : ℕ) : projectiveGamma0 Q :=
  ⟨QuotientGroup.mk T, T, modular_T_mem_gamma0 Q, rfl⟩

/-- Its integer powers act by the literal integer horizontal translations. -/
theorem gamma0ProjectiveT_zpow_smul (Q : ℕ) (n : ℤ) (z : ℍ) :
    (gamma0ProjectiveT Q ^ n) • z = (n : ℝ) +ᵥ z := by
  change ((gamma0ProjectiveT Q ^ n : projectiveGamma0 Q) : PSL(2, ℤ)) • z = _
  rw [Subgroup.coe_zpow]
  change ((QuotientGroup.mk' (Subgroup.center SL(2, ℤ)) T) ^ n) • z = _
  rw [← map_zpow]
  exact modular_T_zpow_smul z n

/-- The genuine projective parabolic translation subgroup at infinity. -/
def gamma0ProjectiveTranslations (Q : ℕ) : Subgroup (projectiveGamma0 Q) :=
  Subgroup.zpowers (gamma0ProjectiveT Q)

/-- The half-open unit strip in the actual upper half-plane. -/
def upperHalfPlaneUnitStrip : Set ℍ := {z | z.re ∈ Ico (0 : ℝ) 1}

/-- This strip is measurable for hyperbolic volume. -/
theorem measurableSet_upperHalfPlaneUnitStrip : MeasurableSet upperHalfPlaneUnitStrip :=
  measurableSet_Ico.preimage UpperHalfPlane.continuous_re.measurable

/-- The literal strip is a fundamental domain for the genuine projective translations. -/
theorem isFundamentalDomain_gamma0Translations (Q : ℕ) :
    IsFundamentalDomain (gamma0ProjectiveTranslations Q) upperHalfPlaneUnitStrip
      (volume : Measure ℍ) := by
  apply IsFundamentalDomain.mk' measurableSet_upperHalfPlaneUnitStrip.nullMeasurableSet
  intro z
  refine ⟨⟨gamma0ProjectiveT Q ^ (-⌊z.re⌋), Subgroup.zpow_mem_zpowers _ _⟩, ?_, ?_⟩
  · change ((gamma0ProjectiveT Q ^ (-⌊z.re⌋)) • z).re ∈ Ico (0 : ℝ) 1
    rw [gamma0ProjectiveT_zpow_smul, vadd_re, Int.cast_neg]
    constructor
    · linarith [Int.floor_le z.re]
    · linarith [Int.lt_floor_add_one z.re]
  · intro g hg
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp g.property
    have he : g • z = (n : ℝ) +ᵥ z := by
      change g.val • z = _
      rw [← hn, gamma0ProjectiveT_zpow_smul]
    have hh : 0 ≤ (n : ℝ) + z.re ∧ (n : ℝ) + z.re < 1 := by
      simpa only [upperHalfPlaneUnitStrip, mem_setOf_eq, he, vadd_re, mem_Ico] using hg
    have hf : ⌊z.re⌋ = -n := Int.floor_eq_iff.mpr ⟨by push_cast; linarith,
      by push_cast; linarith⟩
    apply Subtype.ext
    rw [← hn, hf, neg_neg]

end
end Dubon2026
