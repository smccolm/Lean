import Dubon2026.RealMatrixSmoothSubmodule
import Dubon2026.SmoothParameterDerivative

/-! # The genuine smooth-vector subspace is preserved by original infinitesimal differentiation -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup
open scoped MatrixGroups ContDiff

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V]

/-- Actual bounded real-group operators carry infinitesimal derivatives of genuine smooth vectors back into the same smooth subspace. -/
theorem realMatrixSmoothSubmodule_deriv (ρ : Representation ℂ SL(2, ℝ) V)
    (L : SL(2, ℝ) → V →L[ℝ] V) (hL : ∀ g v, L g v = ρ g v)
    (c : ℝ → SL(2, ℝ)) (hc : ∀ i j : Fin 2, ContDiff ℝ ∞ (fun t => c t i j))
    (v : V) (hv : v ∈ realMatrixSmoothSubmodule ρ) :
    deriv (fun t : ℝ => ρ (c t) v) 0 ∈ realMatrixSmoothSubmodule ρ := by
  intro E _ _ h hh
  let G : E × ℝ → SL(2, ℝ) := fun w => h w.1 * c w.2
  have hG (i j : Fin 2) : ContDiff ℝ ∞ (fun w => G w i j) := by
    change ContDiff ℝ ∞ (fun w : E × ℝ => ∑ l : Fin 2, h w.1 i l * c w.2 l j)
    exact ContDiff.sum (fun l _ => ((hh i l).comp contDiff_fst).mul ((hc l j).comp contDiff_snd))
  let F : E → ℝ → V := fun w t => ρ (h w * c t) v
  have hF : ContDiff ℝ ∞ (Function.uncurry F) := hv (E × ℝ) G hG
  have hs := contDiff_parameter_deriv_zero F hF
  have hd : DifferentiableAt ℝ (fun t : ℝ => ρ (c t) v) 0 :=
    ((contDiff_infty.mp (hv ℝ c hc) 1).differentiable (by norm_num)) 0
  have he : (fun w : E => ρ (h w) (deriv (fun t : ℝ => ρ (c t) v) 0)) =
      fun w : E => deriv (F w) 0 := by
    funext w
    have hm := deriv_continuousLinearMap (L (h w)) (fun t : ℝ => ρ (c t) v) 0 hd
    have hhF : (fun t : ℝ => L (h w) (ρ (c t) v)) = F w := by
      funext t
      rw [hL]
      exact (congrArg (fun T : Module.End ℂ V => T v) (ρ.map_mul (h w) (c t))).symm
    rw [hhF, hL] at hm
    exact hm.symm
  rw [he]
  exact hs

end
end Dubon2026
