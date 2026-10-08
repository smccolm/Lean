import Dubon2026.AdelicRealSmoothSubmodule
import Dubon2026.RealSmoothInfinitesimalOperator
import Dubon2026.RealInfinitesimalSmoothCurves
import Dubon2026.AdelicHilbertCasimir

/-! # The original generator and actual differential operators on its genuine smooth subspace -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ContDiff

/-- The actual original completed generator, now as a member of the proved real smooth-vector subspace. -/
def adelicSmoothGenerator {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) : adelicRealSmoothSubmodule f :=
  ⟨adelicCyclicHilbertGenerator f, adelicCyclicHilbertGenerator_mem_realSmooth f⟩

/-- The literal original Hilbert derivative acts complex-linearly on the original genuine smooth-vector subspace. -/
def adelicSmoothInfinitesimal {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (c : ℝ → SL(2, ℝ))
    (hc : ∀ i j : Fin 2, ContDiff ℝ ∞ (fun t => c t i j)) :
    Module.End ℂ (adelicRealSmoothSubmodule f) := by
  letI : IsScalarTower ℝ ℂ (AdelicCyclicHilbert f) := inferInstance
  exact @realMatrixSmoothInfinitesimal (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance inferInstance
    ((adelicCyclicHilbertRepresentation f).comp adelicRealSL2Embedding)
    (fun g => (adelicCyclicHilbertOperator f (adelicRealSL2Embedding g)).restrictScalars ℝ)
    (fun _ _ => rfl) c hc

/-- The smooth-space action is precisely the original completed infinitesimal derivative. -/
theorem adelicSmoothInfinitesimal_apply {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (c : ℝ → SL(2, ℝ))
    (hc : ∀ i j : Fin 2, ContDiff ℝ ∞ (fun t => c t i j)) (v : adelicRealSmoothSubmodule f) :
    (adelicSmoothInfinitesimal f c hc v).val = adelicHilbertInfinitesimal f c v.val := rfl

/-- The original displayed second-order operator as an actual endomorphism of the genuine smooth-vector subspace. -/
def adelicSmoothCasimirOperator {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) : Module.End ℂ (adelicRealSmoothSubmodule f) := by
  let A := adelicSmoothInfinitesimal f realGeodesicCurve realGeodesicCurve_entries_contDiff
  let U := adelicSmoothInfinitesimal f realUpperUnipotent realUpperUnipotent_entries_contDiff
  let K := adelicSmoothInfinitesimal f realRotationCurve realRotationCurve_entries_contDiff
  exact -A * A + A - U * U + U * K

/-- The genuine smooth-space endomorphism has exactly the original successive Hilbert infinitesimal value. -/
theorem adelicSmoothCasimirOperator_apply {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (v : adelicRealSmoothSubmodule f) :
    (adelicSmoothCasimirOperator f v).val = adelicHilbertCasimirOperator f v.val := by
  simp only [adelicSmoothCasimirOperator, LinearMap.add_apply, LinearMap.sub_apply,
    Module.End.mul_apply, LinearMap.neg_apply, Submodule.coe_add, Submodule.coe_sub,
    Submodule.coe_neg, adelicSmoothInfinitesimal_apply, adelicHilbertCasimirOperator]

/-- The actual smooth original generator is an eigenvector of the genuine smooth-space second-order endomorphism. -/
theorem adelicSmoothGenerator_casimir {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    adelicSmoothCasimirOperator f (adelicSmoothGenerator f) =
      (((k : ℂ) / 2) * (1 - (k : ℂ) / 2)) • adelicSmoothGenerator f := by
  apply Subtype.ext
  rw [adelicSmoothCasimirOperator_apply]
  exact adelicCyclicHilbertGenerator_casimir f

end
end Dubon2026
