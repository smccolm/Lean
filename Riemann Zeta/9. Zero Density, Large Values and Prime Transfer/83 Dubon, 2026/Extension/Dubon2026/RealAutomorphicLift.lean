import Dubon2026.ModularPeterssonLevel
import Mathlib.Analysis.Complex.UpperHalfPlane.ProperAction

/-! # The genuine real-group lift of the original classical cusp form

This constructs the archimedean automorphic function directly from its original upper-half-plane
values. It does not assert the adelic representation or any higher symmetric lift.
-/

namespace Dubon2026

noncomputable section
open UpperHalfPlane Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm ComplexConjugate

/-- The actual weight-k real-group function, obtained by evaluating the original slash translate at i. -/
def realWeightLift (k : ℤ) (f : ℍ → ℂ) (g : SL(2, ℝ)) : ℂ :=
  (f ∣[k] (mapGL ℝ g)) I

/-- The literal classical formula for the real-group lift, with determinant exactly one. -/
theorem realWeightLift_apply (k : ℤ) (f : ℍ → ℂ) (g : SL(2, ℝ)) :
    realWeightLift k f g = f (g • I) * denom (mapGL ℝ g) I ^ (-k) := by
  simp [realWeightLift, ModularForm.slash_apply, UpperHalfPlane.σ, MulAction.compHom_smul_def]

/-- Right translation of the actual lift is exactly the original slash composition. -/
theorem realWeightLift_mul (k : ℤ) (f : ℍ → ℂ) (g h : SL(2, ℝ)) :
    realWeightLift k f (g * h) = realWeightLift k (f ∣[k] (mapGL ℝ g)) h := by
  simp only [realWeightLift, map_mul, SlashAction.slash_mul]

/-- The real-group lift retains the whole original function; the explicit upper-half-plane section recovers it. -/
theorem realWeightLift_injective (k : ℤ) : Function.Injective (realWeightLift k) := by
  intro f f' he
  funext z
  have hh := congrFun he z.toSL2R
  rw [realWeightLift_apply, realWeightLift_apply, toSL2R_smul_I] at hh
  exact mul_right_cancel₀ (zpow_ne_zero _ (denom_ne_zero (mapGL ℝ z.toSL2R) I)) hh

/-- The original cusp-form slash invariance is exactly left invariance of its actual real-group lift. -/
theorem realWeightLift_cusp_left_invariant {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (f : CuspForm Γ k) (γ g : SL(2, ℝ)) (hγ : mapGL ℝ γ ∈ Γ) :
    realWeightLift k f (γ * g) = realWeightLift k f g := by
  rw [realWeightLift_mul, SlashInvariantFormClass.slash_action_eq f _ hγ]

/-- The genuine stabilizer of i acts by the exact weight character on the right. -/
theorem realWeightLift_right_stabilizer (k : ℤ) (f : ℍ → ℂ) (g h : SL(2, ℝ))
    (hh : h • I = I) :
    realWeightLift k f (g * h) = realWeightLift k f g * denom (mapGL ℝ h) I ^ (-k) := by
  rw [realWeightLift_mul, realWeightLift_apply, hh]
  rfl

/-- Continuity of the original function gives genuine continuity on the real group. -/
theorem realWeightLift_continuous (k : ℤ) {f : ℍ → ℂ} (hf : Continuous f) :
    Continuous (realWeightLift k f) := by
  have ha : Continuous (fun g : SL(2, ℝ) => g • I) := by fun_prop
  have hd : Continuous (fun g : SL(2, ℝ) => denom (mapGL ℝ g) I) :=
    denom_continuous.comp ((continuous_mapGL (R := ℝ) (S := ℝ)).prodMk continuous_const)
  have he : realWeightLift k f =
      fun g : SL(2, ℝ) => f (g • I) * denom (mapGL ℝ g) I ^ (-k) :=
    funext (realWeightLift_apply k f)
  rw [he]
  exact (hf.comp ha).mul (hd.zpow₀ (-k) (fun g => Or.inl (denom_ne_zero (mapGL ℝ g) I)))

/-- The exact Petersson pairing is the pointwise pairing of the two original real-group lifts. -/
theorem realWeightLift_pairing (k : ℤ) (f f' : ℍ → ℂ) (g : SL(2, ℝ)) :
    conj (realWeightLift k f g) * realWeightLift k f' g = petersson k f f' (g • I) := by
  simpa [realWeightLift, petersson, UpperHalfPlane.σ, MulAction.compHom_smul_def] using
    petersson_slash k f f' (mapGL ℝ g) I

/-- The squared absolute value of the actual lift is the original Petersson density. -/
theorem realWeightLift_norm_sq (k : ℤ) (f : ℍ → ℂ) (g : SL(2, ℝ)) :
    ‖realWeightLift k f g‖ ^ 2 = ‖petersson k f f (g • I)‖ := by
  have hh := congrArg norm (realWeightLift_pairing k f f g)
  simpa only [norm_mul, Complex.norm_conj, ← pow_two] using hh

/-- On the canonical real-group section, the original function has precisely the classical square-root height factor. -/
theorem realWeightLift_section (k : ℤ) (f : ℍ → ℂ) (z : ℍ) :
    realWeightLift k f z.toSL2R = f z * ((Real.sqrt z.im : ℝ) : ℂ) ^ k := by
  have hd : denom (mapGL ℝ z.toSL2R) I = ((Real.sqrt z.im : ℝ) : ℂ)⁻¹ := by
    simp [denom, UpperHalfPlane.toSL2R, mapGL, Matrix.SpecialLinearGroup.toGL]
  rw [realWeightLift_apply, toSL2R_smul_I, hd, inv_zpow, zpow_neg, inv_inv]

end
end Dubon2026
