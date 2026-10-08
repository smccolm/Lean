import Dubon2026.ScalarVectorODE
import Dubon2026.RealSmoothOneParameterJets

/-! # Genuine one-parameter eigencharacters from original norm infinitesimals -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup
open scoped MatrixGroups ContDiff

/-- An actual smooth infinitesimal eigenvector has the exact exponential character under its genuine original one-parameter action. -/
theorem realSmoothInfinitesimal_eigen_orbit {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V]
    (ρ : Representation ℂ SL(2, ℝ) V) (L : SL(2, ℝ) → V →L[ℝ] V)
    (hL : ∀ g v, L g v = ρ g v)
    (c : ℝ → SL(2, ℝ)) (hc : ∀ i j, ContDiff ℝ ∞ (fun t => c t i j))
    (hadd : ∀ s t, c (s + t) = c s * c t) (hc0 : c 0 = 1)
    (v : realMatrixSmoothSubmodule ρ) (a : ℂ)
    (he : realMatrixSmoothInfinitesimal ρ L hL c hc v = a • v) (t : ℝ) :
    ρ (c t) v.val = Complex.exp ((t : ℂ) * a) • v.val := by
  have hd (s : ℝ) : HasDerivAt (fun t => ρ (c t) v.val) (a • ρ (c s) v.val) s := by
    have h := ((contDiff_infty.mp (v.property ℝ c hc) 1).differentiable (by norm_num) s).hasDerivAt
    rw [realMatrixSmoothInfinitesimal_orbit_deriv ρ L hL c hc hadd v s, he] at h
    simpa only [Submodule.coe_smul, map_smul] using h
  simpa only [hc0, map_one, Module.End.one_apply] using scalarVectorODE_solution _ a hd t

end
end Dubon2026
