import Dubon2026.MixedExponentialScaling
import Dubon2026.RealSmoothInfinitesimalOperator

/-! # Actual infinitesimal brackets forced by genuine exponential subgroup relations -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup
open scoped MatrixGroups ContDiff

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V]

omit [IsScalarTower ℝ ℂ V] in
/-- Two actual infinitesimal actions are the original mixed orbit derivative, with bounded action used to pass the inner derivative through. -/
theorem realMatrixInfinitesimal_mixed (ρ : Representation ℂ SL(2, ℝ) V)
    (L : SL(2, ℝ) → V →L[ℝ] V) (hL : ∀ g v, L g v = ρ g v)
    (c d : ℝ → SL(2, ℝ)) (v : V)
    (hd : DifferentiableAt ℝ (fun t : ℝ => ρ (d t) v) 0) :
    deriv (fun s : ℝ => ρ (c s) (deriv (fun t : ℝ => ρ (d t) v) 0)) 0 =
      deriv (fun s : ℝ => deriv (fun t : ℝ => ρ (c s * d t) v) 0) 0 := by
  apply congrArg (fun C : ℝ → V => deriv C 0)
  funext s
  have he := deriv_continuousLinearMap (L (c s)) (fun t : ℝ => ρ (d t) v) 0 hd
  simpa only [hL, map_mul, Module.End.mul_apply] using he.symm

/-- The original exponential matrix relation gives its precise infinitesimal bracket on every genuine smooth vector. -/
theorem realMatrixInfinitesimal_semidirect (ρ : Representation ℂ SL(2, ℝ) V)
    (L : SL(2, ℝ) → V →L[ℝ] V) (hL : ∀ g v, L g v = ρ g v)
    (a b : ℝ → SL(2, ℝ)) (ha : ∀ i j : Fin 2, ContDiff ℝ ∞ (fun t => a t i j))
    (hb : ∀ i j : Fin 2, ContDiff ℝ ∞ (fun t => b t i j)) (ha0 : a 0 = 1)
    (r : ℝ) (hab : ∀ s t, a s * b t = b (Real.exp (r * s) * t) * a s)
    (v : V) (hv : v ∈ realMatrixSmoothSubmodule ρ) :
    deriv (fun s : ℝ => ρ (a s) (deriv (fun t : ℝ => ρ (b t) v) 0)) 0 -
      deriv (fun t : ℝ => ρ (b t) (deriv (fun s : ℝ => ρ (a s) v) 0)) 0 =
      r • deriv (fun t : ℝ => ρ (b t) v) 0 := by
  have haD : DifferentiableAt ℝ (fun s : ℝ => ρ (a s) v) 0 :=
    ((contDiff_infty.mp (hv ℝ a ha) 1).differentiable (by norm_num)) 0
  have hbD : DifferentiableAt ℝ (fun t : ℝ => ρ (b t) v) 0 :=
    ((contDiff_infty.mp (hv ℝ b hb) 1).differentiable (by norm_num)) 0
  let F : ℝ → ℝ → V := fun s t => ρ (b t * a s) v
  have hF : ContDiff ℝ ∞ (Function.uncurry F) := by
    apply hv (ℝ × ℝ) (fun w => b w.2 * a w.1)
    intro i j
    change ContDiff ℝ ∞ (fun w : ℝ × ℝ => ∑ l : Fin 2, b w.2 i l * a w.1 l j)
    exact ContDiff.sum (fun l _ => ((hb i l).comp contDiff_snd).mul ((ha l j).comp contDiff_fst))
  have hAB := realMatrixInfinitesimal_mixed ρ L hL a b v hbD
  have hBA := realMatrixInfinitesimal_mixed ρ L hL b a v haD
  simp_rw [hab] at hAB
  have hs := mixedExpScaling_deriv F hF r
  have hzero : F 0 = fun t : ℝ => ρ (b t) v := by
    funext t
    simp only [F, ha0, mul_one]
  rw [hzero, ← hBA] at hs
  exact sub_eq_iff_eq_add.mpr (hAB.trans hs)

/-- The original exponential subgroup relation is an equality of genuine infinitesimal endomorphisms of the actual smooth subspace. -/
theorem realMatrixSmoothInfinitesimal_semidirect (ρ : Representation ℂ SL(2, ℝ) V)
    (L : SL(2, ℝ) → V →L[ℝ] V) (hL : ∀ g v, L g v = ρ g v)
    (a b : ℝ → SL(2, ℝ)) (ha : ∀ i j : Fin 2, ContDiff ℝ ∞ (fun t => a t i j))
    (hb : ∀ i j : Fin 2, ContDiff ℝ ∞ (fun t => b t i j)) (ha0 : a 0 = 1)
    (r : ℝ) (hab : ∀ s t, a s * b t = b (Real.exp (r * s) * t) * a s) :
    realMatrixSmoothInfinitesimal ρ L hL a ha * realMatrixSmoothInfinitesimal ρ L hL b hb -
      realMatrixSmoothInfinitesimal ρ L hL b hb * realMatrixSmoothInfinitesimal ρ L hL a ha =
      (r : ℂ) • realMatrixSmoothInfinitesimal ρ L hL b hb := by
  ext v
  exact (realMatrixInfinitesimal_semidirect ρ L hL a b ha hb ha0 r hab v.val v.property).trans
    (RCLike.real_smul_eq_coe_smul (K := ℂ) r _)

end
end Dubon2026
