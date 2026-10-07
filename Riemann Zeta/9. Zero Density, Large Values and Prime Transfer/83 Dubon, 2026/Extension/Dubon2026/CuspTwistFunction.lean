import Dubon2026.QuadraticTwistHecke

/-! # Literal analytic formula for the constructed character twist -/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups ModularForm

noncomputable section

/-- The actual principal-level twist evaluates as its finite Gauss-weighted translation sum. -/
theorem principalCharacterTwist_apply (N : ℕ) (k : ℤ) {D : ℕ} [NeZero D]
    (χ : DirichletCharacter ℂ D)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) (τ : ℍ) :
    principalCharacterTwist N k χ f τ = (gaussSum χ ZMod.stdAddChar)⁻¹ *
      ∑ a : ZMod D, χ a * f (((a.val * (N / D) : ℕ) : ℝ) +ᵥ τ) := by
  let ev : CuspForm ((Gamma N).map (mapGL ℝ)) k →ₗ[ℂ] ℂ :=
    { toFun := fun g => g τ
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  change ev (principalCharacterTwist N k χ f) = _
  simp only [principalCharacterTwist, LinearMap.smul_apply, LinearMap.sum_apply,
    map_smul, map_sum]
  change (gaussSum χ ZMod.stdAddChar)⁻¹ *
    (∑ a : ZMod D, χ a * principalTranslation N k ((a.val * (N / D) : ℕ) : ℤ) f τ) = _
  simp only [principalTranslation_apply, Int.cast_natCast]

/-- Dilating, translating and undoing the principal rescaling gives the exact rational shift. -/
theorem twist_rescaling_point (D H : ℕ) [NeZero D] [NeZero H] (a : ℕ) (τ : ℍ) :
    heckeUpperPoint (D * H) 0
      (((a * ((D * H) / D) : ℕ) : ℝ) +ᵥ (levelRaiseMatrix (D * H) • τ)) =
      ((a : ℝ) / D) +ᵥ τ := by
  apply UpperHalfPlane.ext
  simp only [heckeUpperPoint, coe_mk, coe_vadd, coe_levelRaiseMatrix_smul,
    Nat.cast_zero, add_zero, Nat.mul_div_cancel_left H (Nat.pos_of_neZero D)]
  push_cast
  field_simp [Nat.cast_ne_zero.mpr (NeZero.ne D), Nat.cast_ne_zero.mpr (NeZero.ne H)]

/-- The genuine level-preserving cusp twist is the literal normalized sum f(z+a/D). -/
theorem cuspQuadraticTwistAtLevel_apply {D H : ℕ} [NeZero D] [NeZero H]
    (hDH : D ∣ H) (k : ℤ) (χ : DirichletCharacter ℂ D) (hq : χ.IsQuadratic)
    (f : CuspForm ((Gamma0 (D * H)).map (mapGL ℝ)) k) (τ : ℍ) :
    cuspQuadraticTwistAtLevel hDH k χ hq f τ = (gaussSum χ ZMod.stdAddChar)⁻¹ *
      ∑ a : ZMod D, χ a * f (((a.val : ℝ) / D) +ᵥ τ) := by
  rw [cuspQuadraticTwistAtLevel, LinearMap.comp_apply, principalUpperToGamma0_apply]
  change principalCharacterTwist (D * H) k χ (cuspRescaledPrincipal (D * H) k f)
    (levelRaiseMatrix (D * H) • τ) = _
  rw [principalCharacterTwist_apply]
  simp only [cuspRescaledPrincipal_apply, twist_rescaling_point]

/-- The constructed level-D²Q cusp form equals the actual Gauss-weighted rational-translation formula. -/
theorem cuspQuadraticTwist_apply {Q D : ℕ} [NeZero Q] [NeZero D] {k : ℤ}
    (χ : DirichletCharacter ℂ D) (hq : χ.IsQuadratic)
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (τ : ℍ) :
    cuspQuadraticTwist k χ hq f τ = (gaussSum χ ZMod.stdAddChar)⁻¹ *
      ∑ a : ZMod D, χ a * f (((a.val : ℝ) / D) +ᵥ τ) := by
  rw [cuspQuadraticTwist, LinearMap.comp_apply, cuspQuadraticTwistAtLevel_apply]
  rfl

end
end Dubon2026
