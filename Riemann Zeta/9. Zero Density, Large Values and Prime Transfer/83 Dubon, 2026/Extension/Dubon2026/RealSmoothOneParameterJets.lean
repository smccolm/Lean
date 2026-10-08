import Dubon2026.RealSmoothInfinitesimalOperator
import Dubon2026.LinearMapSmoothJets

/-! # Every original norm derivative is the corresponding genuine infinitesimal power -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup
open scoped MatrixGroups ContDiff

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V]

/-- The original one-parameter orbit derivative is the original translate of its genuine infinitesimal vector at every parameter. -/
theorem realMatrixSmoothInfinitesimal_orbit_deriv (ρ : Representation ℂ SL(2, ℝ) V)
    (L : SL(2, ℝ) → V →L[ℝ] V) (hL : ∀ g v, L g v = ρ g v)
    (c : ℝ → SL(2, ℝ)) (hc : ∀ i j : Fin 2, ContDiff ℝ ∞ (fun t => c t i j))
    (hadd : ∀ s t, c (s + t) = c s * c t) (v : realMatrixSmoothSubmodule ρ) (s : ℝ) :
    deriv (fun t : ℝ => ρ (c t) v.val) s =
      ρ (c s) (realMatrixSmoothInfinitesimal ρ L hL c hc v).val := by
  have hd : DifferentiableAt ℝ (fun t : ℝ => ρ (c t) v.val) 0 :=
    ((contDiff_infty.mp (v.property ℝ c hc) 1).differentiable (by norm_num)) 0
  have he := continuousLinearMap_orbit_deriv (L (c s)) (fun t : ℝ => ρ (c t) v.val) s
    (fun t => show L (c s) (ρ (c t) v.val) = ρ (c (s + t)) v.val by
      rw [hL, hadd, map_mul, Module.End.mul_apply]) hd
  exact he.symm.trans (hL (c s) _)

/-- All actual Hilbert-norm orbit jets agree with powers of the original infinitesimal endomorphism, retaining the original translate at every parameter. -/
theorem realMatrixSmoothInfinitesimal_iteratedDeriv (ρ : Representation ℂ SL(2, ℝ) V)
    (L : SL(2, ℝ) → V →L[ℝ] V) (hL : ∀ g v, L g v = ρ g v)
    (c : ℝ → SL(2, ℝ)) (hc : ∀ i j : Fin 2, ContDiff ℝ ∞ (fun t => c t i j))
    (hadd : ∀ s t, c (s + t) = c s * c t) (v : realMatrixSmoothSubmodule ρ) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => ρ (c t) v.val) =
      (fun t => ρ (c t) (((realMatrixSmoothInfinitesimal ρ L hL c hc) ^ n) v).val) := by
  induction n with
  | zero => simp only [iteratedDeriv_zero, pow_zero, Module.End.one_apply]
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext t
      rw [realMatrixSmoothInfinitesimal_orbit_deriv ρ L hL c hc hadd]
      simp only [pow_succ', Module.End.mul_apply]

end
end Dubon2026
