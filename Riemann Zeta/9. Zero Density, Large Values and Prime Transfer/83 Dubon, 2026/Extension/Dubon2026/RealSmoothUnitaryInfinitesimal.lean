import Dubon2026.RealSmoothInfinitesimalOperator
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! # Skew symmetry of original norm derivatives in a genuine unitary representation -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup
open scoped MatrixGroups ContDiff

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V]

/-- Differentiating actual unitarity makes each original smooth-curve infinitesimal skew symmetric on the genuine smooth domain. -/
theorem realMatrixSmoothInfinitesimal_skew (ρ : Representation ℂ SL(2, ℝ) V)
    (L : SL(2, ℝ) → V →L[ℝ] V) (hL : ∀ g v, L g v = ρ g v)
    (hunit : ∀ g v w, inner ℂ (ρ g v) (ρ g w) = inner ℂ v w)
    (c : ℝ → SL(2, ℝ)) (hc : ∀ i j : Fin 2, ContDiff ℝ ∞ (fun t => c t i j))
    (hc0 : c 0 = 1) (v w : realMatrixSmoothSubmodule ρ) :
    inner ℂ (realMatrixSmoothInfinitesimal ρ L hL c hc v).val w.val +
      inner ℂ v.val (realMatrixSmoothInfinitesimal ρ L hL c hc w).val = 0 := by
  have hd (u : realMatrixSmoothSubmodule ρ) :
      HasDerivAt (fun t : ℝ => ρ (c t) u.val) (deriv (fun t : ℝ => ρ (c t) u.val) 0) 0 :=
    (((contDiff_infty.mp (u.property ℝ c hc) 1).differentiable (by norm_num)) 0).hasDerivAt
  have h := (hd v).inner ℂ (hd w)
  have he : (fun t : ℝ => inner ℂ (ρ (c t) v.val) (ρ (c t) w.val)) =
      (fun _ : ℝ => inner ℂ v.val w.val) := funext (fun t => hunit (c t) v.val w.val)
  rw [he] at h
  have hz := h.unique (hasDerivAt_const 0 (inner ℂ v.val w.val))
  simpa only [realMatrixSmoothInfinitesimal_apply, hc0, map_one, Module.End.one_apply,
    add_comm] using hz

end
end Dubon2026
