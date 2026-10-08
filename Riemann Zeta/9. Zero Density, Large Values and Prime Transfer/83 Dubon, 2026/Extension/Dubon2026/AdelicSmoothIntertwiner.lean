import Dubon2026.RealSmoothIntertwiner
import Dubon2026.AdelicClosedWeightLines

/-! # Actual bounded Hilbert intertwiners on the original smooth matrix module -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ContDiff

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The original bounded intertwiner restricted to the original genuine smooth domain. -/
def adelicSmoothIntertwiner (T : AdelicCyclicHilbert f →L[ℂ] AdelicCyclicHilbert f)
    (hT : ∀ g : SL(2, ℝ), ∀ v, T (adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding g) v) =
      adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding g) (T v)) :
    Module.End ℂ (adelicRealSmoothSubmodule f) := by
  letI : IsScalarTower ℝ ℂ (AdelicCyclicHilbert f) := inferInstance
  exact @realMatrixSmoothIntertwiner (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance inferInstance
    ((adelicCyclicHilbertRepresentation f).comp adelicRealSL2Embedding) T hT

/-- Restriction preserves the literal original bounded Hilbert action. -/
theorem adelicSmoothIntertwiner_apply (T : AdelicCyclicHilbert f →L[ℂ] AdelicCyclicHilbert f)
    (hT : ∀ g : SL(2, ℝ), ∀ v, T (adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding g) v) =
      adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding g) (T v))
    (v : adelicRealSmoothSubmodule f) : (adelicSmoothIntertwiner f T hT v).val = T v.val := rfl

/-- Every original bounded real-group intertwiner commutes with every genuine smooth-curve infinitesimal. -/
theorem adelicSmoothIntertwiner_infinitesimal
    (T : AdelicCyclicHilbert f →L[ℂ] AdelicCyclicHilbert f)
    (hT : ∀ g : SL(2, ℝ), ∀ v, T (adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding g) v) =
      adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding g) (T v))
    (c : ℝ → SL(2, ℝ)) (hc : ∀ i j : Fin 2, ContDiff ℝ ∞ (fun t => c t i j)) :
    Commute (adelicSmoothIntertwiner f T hT) (adelicSmoothInfinitesimal f c hc) := by
  letI : IsScalarTower ℝ ℂ (AdelicCyclicHilbert f) := inferInstance
  exact @realMatrixSmoothIntertwiner_infinitesimal (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance inferInstance
    ((adelicCyclicHilbertRepresentation f).comp adelicRealSL2Embedding)
    (fun g => (adelicCyclicHilbertOperator f (adelicRealSL2Embedding g)).restrictScalars ℝ)
    (fun _ _ => rfl) T hT c hc

/-- The original bounded intertwiner commutes with the actual entire complex matrix Lie action. -/
theorem adelicSmoothIntertwiner_matrix (T : AdelicCyclicHilbert f →L[ℂ] AdelicCyclicHilbert f)
    (hT : ∀ g : SL(2, ℝ), ∀ v, T (adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding g) v) =
      adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding g) (T v)) (x : ComplexSl2) :
    Commute (adelicSmoothIntertwiner f T hT) (adelicComplexSl2Action f x) := by
  have hA := adelicSmoothIntertwiner_infinitesimal f T hT realGeodesicCurve
    realGeodesicCurve_entries_contDiff
  have hU := adelicSmoothIntertwiner_infinitesimal f T hT realUpperUnipotent
    realUpperUnipotent_entries_contDiff
  have hF := adelicSmoothIntertwiner_infinitesimal f T hT realLowerUnipotent
    realLowerUnipotent_entries_contDiff
  rw [adelicComplexSl2Action_apply]
  exact ((hA.smul_right (2 * x.val 0 0)).add_right (hU.smul_right (x.val 0 1))).add_right
    (hF.smul_right (x.val 1 0))

end
end Dubon2026
