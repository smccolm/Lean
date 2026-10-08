import Dubon2026.RealSmoothInfinitesimal

/-! # Actual infinitesimal operators on the genuine smooth-vector subspace -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup
open scoped MatrixGroups ContDiff

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V]

/-- The actual derivative of a smooth matrix orbit is a complex-linear endomorphism of its genuine smooth-vector subspace. -/
def realMatrixSmoothInfinitesimal (ρ : Representation ℂ SL(2, ℝ) V)
    (L : SL(2, ℝ) → V →L[ℝ] V) (hL : ∀ g v, L g v = ρ g v)
    (c : ℝ → SL(2, ℝ)) (hc : ∀ i j : Fin 2, ContDiff ℝ ∞ (fun t => c t i j)) :
    Module.End ℂ (realMatrixSmoothSubmodule ρ) := by
  have hd (v : realMatrixSmoothSubmodule ρ) :
      DifferentiableAt ℝ (fun t : ℝ => ρ (c t) v.val) 0 :=
    ((contDiff_infty.mp (v.property ℝ c hc) 1).differentiable (by norm_num)) 0
  exact {
    toFun := fun v => ⟨deriv (fun t : ℝ => ρ (c t) v.val) 0,
      realMatrixSmoothSubmodule_deriv ρ L hL c hc v.val v.property⟩
    map_add' := by
      intro v w
      apply Subtype.ext
      change deriv (fun t : ℝ => ρ (c t) (v.val + w.val)) 0 =
        deriv (fun t : ℝ => ρ (c t) v.val) 0 + deriv (fun t : ℝ => ρ (c t) w.val) 0
      simp_rw [map_add]
      exact deriv_add (hd v) (hd w)
    map_smul' := by
      intro a v
      apply Subtype.ext
      change deriv (fun t : ℝ => ρ (c t) (a • v.val)) 0 = a • deriv (fun t : ℝ => ρ (c t) v.val) 0
      simp_rw [map_smul]
      exact deriv_fun_const_smul a (hd v) }

/-- The smooth-space operator retains the literal original Hilbert derivative as its value. -/
theorem realMatrixSmoothInfinitesimal_apply (ρ : Representation ℂ SL(2, ℝ) V)
    (L : SL(2, ℝ) → V →L[ℝ] V) (hL : ∀ g v, L g v = ρ g v)
    (c : ℝ → SL(2, ℝ)) (hc : ∀ i j : Fin 2, ContDiff ℝ ∞ (fun t => c t i j))
    (v : realMatrixSmoothSubmodule ρ) :
    (realMatrixSmoothInfinitesimal ρ L hL c hc v).val =
      deriv (fun t : ℝ => ρ (c t) v.val) 0 := rfl

end
end Dubon2026
