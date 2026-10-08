import Dubon2026.RealGaussSmoothCoordinates

/-! # First derivatives of original smooth orbits depend on actual matrix tangents -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup
open scoped MatrixGroups ContDiff Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V]

/-- The actual real differential at the identity of the original Gaussian orbit. -/
def realSmoothOrbitDifferential (ρ : Representation ℂ SL(2, ℝ) V) (v : V) :
    (ℝ × ℝ × ℝ) →L[ℝ] V :=
  fderiv ℝ (fun w => ρ (realGaussCoordinates w) v) 0

/-- For every genuine smooth vector, the original matrix curve has the derivative of its exact Gaussian tangent. -/
theorem realSmoothOrbitDifferential_hasDerivAt (ρ : Representation ℂ SL(2, ℝ) V)
    (v : V) (hv : v ∈ realMatrixSmoothSubmodule ρ)
    (c : ℝ → SL(2, ℝ)) (hc : c 0 = 1) (a b d : ℝ)
    (ha : HasDerivAt (fun t => c t 0 0) a 0)
    (hb : HasDerivAt (fun t => c t 1 0) b 0)
    (hd : HasDerivAt (fun t => c t 0 1) d 0) :
    HasDerivAt (fun t => ρ (c t) v) (realSmoothOrbitDifferential ρ v (b, 2 * a, d)) 0 := by
  have hF := hv (ℝ × ℝ × ℝ) realGaussCoordinates realGaussCoordinates_entries_contDiff
  have hD := ((contDiff_infty.mp hF 1).differentiable (by norm_num) 0).hasFDerivAt
  have hC := realGaussCoordinates_curve_deriv c hc a b d ha hb hd
  have hcomp := hD.comp_hasDerivAt_of_eq 0 hC (by simp [hc]; rfl)
  apply hcomp.congr_of_eventuallyEq
  have hp : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < c t 0 0 :=
    ha.continuousAt.eventually (lt_mem_nhds (show (0 : ℝ) < c 0 0 0 by simp [hc]))
  filter_upwards [hp] with t ht
  dsimp only [Function.comp_def]
  rw [realGaussCoordinates_eq _ ht]

/-- The original infinitesimal is exactly the differential applied to the original entry tangent. -/
theorem realSmoothOrbitDifferential_deriv (ρ : Representation ℂ SL(2, ℝ) V)
    (v : V) (hv : v ∈ realMatrixSmoothSubmodule ρ)
    (c : ℝ → SL(2, ℝ)) (hc : c 0 = 1) (a b d : ℝ)
    (ha : HasDerivAt (fun t => c t 0 0) a 0)
    (hb : HasDerivAt (fun t => c t 1 0) b 0)
    (hd : HasDerivAt (fun t => c t 0 1) d 0) :
    deriv (fun t => ρ (c t) v) 0 = realSmoothOrbitDifferential ρ v (b, 2 * a, d) :=
  (realSmoothOrbitDifferential_hasDerivAt ρ v hv c hc a b d ha hb hd).deriv

end
end Dubon2026
