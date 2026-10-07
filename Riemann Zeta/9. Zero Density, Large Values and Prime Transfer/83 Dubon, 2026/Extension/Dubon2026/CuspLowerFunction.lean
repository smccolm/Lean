import Dubon2026.CuspSparsePeriod
import Dubon2026.LevelLowerFactorization
import Dubon2026.HeckeCuspBehavior

/-! # Literal divisor rescaling and its analytic and slash transport -/

namespace Dubon2026

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups ModularForm Manifold

noncomputable section

/-- The actual inverse-dilation function f(z/d), with the slash normalization canceled. -/
def levelLowerFun (d : ℕ) [NeZero d] (k : ℤ) (f : ℍ → ℂ) : ℍ → ℂ :=
  (d : ℂ) • (f ∣[k] heckeTriangularMatrix 1 d 0)

/-- The normalized inverse slash is literally f(z/d). -/
theorem levelLowerFun_apply (d : ℕ) [NeZero d] (k : ℤ) (f : ℍ → ℂ) (τ : ℍ) :
    levelLowerFun d k f τ = f (heckeUpperPoint d 0 τ) := by
  change (d : ℂ) * ((f ∣[k] heckeTriangularMatrix 1 d 0) τ) = _
  rw [heckeTriangular_slash_apply]
  have he : levelRaiseMatrix 1 • τ = τ := by
    apply UpperHalfPlane.ext
    simp [coe_levelRaiseMatrix_smul]
  rw [he]
  simp [Nat.cast_ne_zero.mpr (NeZero.ne d)]

/-- Dilation after this exact inverse-dilation recovers the original function. -/
theorem levelRaiseFun_levelLowerFun (d : ℕ) [NeZero d] (k : ℤ) (f : ℍ → ℂ) :
    levelRaiseFun d k (levelLowerFun d k f) = f := by
  funext τ
  rw [levelRaiseFun_apply, levelLowerFun_apply]
  congr 1
  apply UpperHalfPlane.ext
  simp only [heckeUpperPoint, coe_mk, Nat.cast_zero, add_zero, coe_levelRaiseMatrix_smul]
  exact mul_div_cancel_left₀ _ (show (d : ℂ) ≠ 0 from Nat.cast_ne_zero.mpr (NeZero.ne d))

/-- The actual inverse-dilation preserves holomorphy on the upper half-plane. -/
theorem levelLowerFun_holomorphic (d : ℕ) [NeZero d] (k : ℤ) (f : ℍ → ℂ)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (levelLowerFun d k f) :=
  (hf.slash k _).const_smul _

/-- Rational inverse dilation preserves vanishing at every cusp of every positive Gamma0 level. -/
theorem levelLowerFun_zero_at_cusps {N M : ℕ} [NeZero N] [NeZero M] {k : ℤ}
    (d : ℕ) [NeZero d] (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    {c : OnePoint ℝ} (hc : IsCusp c ((Gamma0 M).map (mapGL ℝ))) :
    c.IsZeroAt (levelLowerFun d k f) k := by
  have hcN : IsCusp c ((Gamma0 N).map (mapGL ℝ)) := by
    rwa [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
  have hz : c.IsZeroAt (⇑f ∣[k] heckeTriangularMatrix 1 d 0) k :=
    OnePoint.IsZeroAt.smul_iff.mp (f.zero_at_cusps'
      (rationalMatrix_smul_isCusp (heckeTriangularRat 1 d 0) hcN))
  intro γ hγ
  rw [levelLowerFun, ModularForm.smul_slash]
  exact (hz γ hγ).smul _

/-- The exact matrix conjugation transports slash before dilation to slash after dilation. -/
theorem levelRaiseFun_slash_conjugate (d : ℕ) [NeZero d] (k : ℤ) (f : ℍ → ℂ)
    (γ : SL(2, ℤ)) (hd : (d : ℤ) ∣ γ.val 1 0) :
    levelRaiseFun d k (f ∣[k] mapGL ℝ (levelRaiseConjOfDvd d γ hd)) =
      (levelRaiseFun d k f) ∣[k] mapGL ℝ γ := by
  unfold levelRaiseFun
  change (d : ℂ) ^ (1 - k) • ((f ∣[k] mapGL ℝ (levelRaiseConjOfDvd d γ hd)) ∣[k]
    levelRaiseMatrix d) = (((d : ℂ) ^ (1 - k)) • (f ∣[k] levelRaiseMatrix d)) ∣[k] γ
  rw [ModularForm.SL_smul_slash]
  rw [← SlashAction.slash_mul, ModularForm.SL_slash, ← SlashAction.slash_mul,
    levelRaiseMatrix_mul_mapGL]
  rfl

end
end Dubon2026
