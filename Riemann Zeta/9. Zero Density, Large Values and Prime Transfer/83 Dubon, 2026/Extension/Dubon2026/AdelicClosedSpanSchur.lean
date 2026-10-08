import Dubon2026.AdelicSmoothIntertwiner
import Dubon2026.ContinuousCyclicScalar

/-! # Exact scalar action of original bounded intertwiners on the original raising closure -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- A genuine bounded real-group intertwiner whose original generator image lies in the original raising closure preserves its exact original generator line. -/
theorem adelicIntertwiner_generator_line (hf : f ≠ 0) (hk : 0 < k)
    (T : AdelicCyclicHilbert f →L[ℂ] AdelicCyclicHilbert f)
    (hT : ∀ g : SL(2, ℝ), ∀ v, T (adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding g) v) =
      adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding g) (T v))
    (hv : T (adelicCyclicHilbertGenerator f) ∈ adelicRaisingClosedSpan f) :
    ∃ a : ℂ, adelicSmoothIntertwiner f T hT (adelicSmoothGenerator f) = a • adelicSmoothGenerator f := by
  have he := commutingEnd_eigenvector (adelicComplexSl2Action f compactSl2H)
    (adelicSmoothIntertwiner f T hT) (adelicSmoothGenerator f) _
    (adelicSmoothIntertwiner_matrix f T hT compactSl2H).symm (adelicRaisingJet_weight f hf 0)
  exact adelicRaisingClosedSpan_weight_line f hf hk 0 _ hv he

/-- The same original intertwiner scalar propagates through all literal original raising derivatives. -/
theorem adelicIntertwiner_raising_scalar
    (T : AdelicCyclicHilbert f →L[ℂ] AdelicCyclicHilbert f)
    (hT : ∀ g : SL(2, ℝ), ∀ v, T (adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding g) v) =
      adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding g) (T v))
    (a : ℂ) (ha : adelicSmoothIntertwiner f T hT (adelicSmoothGenerator f) = a • adelicSmoothGenerator f)
    (n : ℕ) : T (adelicRaisingJet f n).val = a • (adelicRaisingJet f n).val := by
  have he := commutingEnd_eigenvector (adelicSmoothIntertwiner f T hT)
    ((adelicComplexSl2Action f compactSl2E) ^ n) (adelicSmoothGenerator f) a
    ((adelicSmoothIntertwiner_matrix f T hT compactSl2E).pow_right n) ha
  exact congrArg Subtype.val he

/-- Every such original bounded real-group intertwiner has a single exact scalar on the entire genuine original raising closure. -/
theorem adelicIntertwiner_closedSpan_scalar (hf : f ≠ 0) (hk : 0 < k)
    (T : AdelicCyclicHilbert f →L[ℂ] AdelicCyclicHilbert f)
    (hT : ∀ g : SL(2, ℝ), ∀ v, T (adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding g) v) =
      adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding g) (T v))
    (hv : T (adelicCyclicHilbertGenerator f) ∈ adelicRaisingClosedSpan f) :
    ∃ a : ℂ, ∀ v ∈ adelicRaisingClosedSpan f, T v = a • v := by
  obtain ⟨a, ha⟩ := adelicIntertwiner_generator_line f hf hk T hT hv
  refine ⟨a, fun v hv => ?_⟩
  exact @continuousLinearMap_scalar_on_closedSpan (AdelicCyclicHilbert f) ℕ
    inferInstance inferInstance T a (fun n => (adelicRaisingJet f n).val)
    (adelicIntertwiner_raising_scalar f T hT a ha) v hv

end
end Dubon2026
