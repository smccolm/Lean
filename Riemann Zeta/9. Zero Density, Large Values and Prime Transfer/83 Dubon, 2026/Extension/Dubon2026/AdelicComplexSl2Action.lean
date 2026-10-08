import Dubon2026.ComplexSl2LieHom
import Dubon2026.AdelicSmoothCasimirCommutation

/-! # The genuine complex sl2 action from original adelic Hilbert infinitesimals -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

local notation "A" => adelicSmoothInfinitesimal f realGeodesicCurve realGeodesicCurve_entries_contDiff
local notation "U" => adelicSmoothInfinitesimal f realUpperUnipotent realUpperUnipotent_entries_contDiff
local notation "F" => adelicSmoothInfinitesimal f realLowerUnipotent realLowerUnipotent_entries_contDiff

/-- The actual matrix Lie algebra acts by the original smooth Hilbert infinitesimals and their complex-linear extension. -/
def adelicComplexSl2Action : ComplexSl2 →ₗ⁅ℂ⁆ Module.End ℂ (adelicRealSmoothSubmodule f) :=
  complexSl2LieHom A U F (adelicSmoothInfinitesimal_geodesic_upper f)
    (adelicSmoothInfinitesimal_geodesic_lower f)
    ((adelicSmoothInfinitesimal_upper_lower f).trans (two_smul ℂ A))

/-- The genuine half-diagonal matrix acts by the original geodesic Hilbert derivative. -/
theorem adelicComplexSl2Action_A : adelicComplexSl2Action f complexSl2A = A :=
  complexSl2LinearMap_A A U F

/-- The genuine upper matrix acts by the original upper Hilbert derivative. -/
theorem adelicComplexSl2Action_U : adelicComplexSl2Action f complexSl2U = U :=
  complexSl2LinearMap_U A U F

/-- The genuine lower matrix acts by the original lower Hilbert derivative. -/
theorem adelicComplexSl2Action_F : adelicComplexSl2Action f complexSl2F = F :=
  complexSl2LinearMap_F A U F

/-- Every actual traceless complex matrix acts by exactly its original infinitesimal coordinate combination. -/
theorem adelicComplexSl2Action_apply (x : ComplexSl2) :
    adelicComplexSl2Action f x = (2 * x.val 0 0) • A + x.val 0 1 • U + x.val 1 0 • F := rfl

open scoped ContDiff in
/-- Every original smooth real matrix curve acts through the exact complexified matrix tangent by its literal original Hilbert infinitesimal. -/
theorem adelicComplexSl2Action_curve (c : ℝ → SL(2, ℝ))
    (hc : ∀ i j : Fin 2, ContDiff ℝ ∞ (fun t => c t i j)) (hc0 : c 0 = 1) :
    adelicComplexSl2Action f (complexSl2OfRealTangent
      (deriv (fun t => c t 0 0) 0) (deriv (fun t => c t 1 0) 0) (deriv (fun t => c t 0 1) 0)) =
      adelicSmoothInfinitesimal f c hc := by
  letI : IsScalarTower ℝ ℂ (AdelicCyclicHilbert f) := inferInstance
  have hd (i j : Fin 2) : HasDerivAt (fun t => c t i j) (deriv (fun t => c t i j) 0) 0 :=
    (((contDiff_infty.mp (hc i j) 1).differentiable (by norm_num)) 0).hasDerivAt
  have he := @realMatrixSmoothInfinitesimal_tangent (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance inferInstance
    ((adelicCyclicHilbertRepresentation f).comp adelicRealSL2Embedding)
    (fun g => (adelicCyclicHilbertOperator f (adelicRealSL2Embedding g)).restrictScalars ℝ)
    (fun _ _ => rfl) c hc hc0 _ _ _ (hd 0 0) (hd 1 0) (hd 0 1)
  exact (complexSl2LinearMap_real_tangent A U F _ _ _).trans he.symm

end
end Dubon2026
