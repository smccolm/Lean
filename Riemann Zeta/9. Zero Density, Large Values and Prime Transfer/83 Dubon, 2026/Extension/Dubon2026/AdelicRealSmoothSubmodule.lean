import Dubon2026.RealSmoothInfinitesimal
import Dubon2026.AdelicHilbertRealSmoothFamilies
import Dubon2026.AdelicHilbertInfinitesimal

/-! # The original generator in the genuine real smooth-vector subspace -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ContDiff

/-- The genuine smooth-vector subspace of the original completed adelic representation under its actual real action. -/
def adelicRealSmoothSubmodule {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) : Submodule ℂ (AdelicCyclicHilbert f) := by
  letI : IsScalarTower ℝ ℂ (AdelicCyclicHilbert f) := inferInstance
  exact @realMatrixSmoothSubmodule (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance
    inferInstance ((adelicCyclicHilbertRepresentation f).comp adelicRealSL2Embedding)

/-- The actual completed cusp generator belongs to its genuine real smooth-vector subspace with no smoothness premise. -/
theorem adelicCyclicHilbertGenerator_mem_realSmooth {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    adelicCyclicHilbertGenerator f ∈ adelicRealSmoothSubmodule f := by
  intro E _ _ h hh
  exact adelicCyclicHilbertGenerator_real_contDiff f h hh

/-- Every actual real translate of an original smooth completed vector is again smooth. -/
theorem adelicRealSmoothSubmodule_invariant {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (v : AdelicCyclicHilbert f)
    (hv : v ∈ adelicRealSmoothSubmodule f) (g : SL(2, ℝ)) :
    adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding g) v ∈ adelicRealSmoothSubmodule f := by
  letI : IsScalarTower ℝ ℂ (AdelicCyclicHilbert f) := inferInstance
  exact @realMatrixSmoothSubmodule_invariant (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance inferInstance
    ((adelicCyclicHilbertRepresentation f).comp adelicRealSL2Embedding) v hv g

/-- Every actual smooth real matrix curve defines an infinitesimal action preserving the original completed smooth-vector subspace. -/
theorem adelicRealSmoothSubmodule_infinitesimal {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (v : AdelicCyclicHilbert f)
    (hv : v ∈ adelicRealSmoothSubmodule f) (c : ℝ → SL(2, ℝ))
    (hc : ∀ i j : Fin 2, ContDiff ℝ ∞ (fun t => c t i j)) :
    adelicHilbertInfinitesimal f c v ∈ adelicRealSmoothSubmodule f := by
  letI : IsScalarTower ℝ ℂ (AdelicCyclicHilbert f) := inferInstance
  exact @realMatrixSmoothSubmodule_deriv (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance inferInstance
    ((adelicCyclicHilbertRepresentation f).comp adelicRealSL2Embedding)
    (fun g => (adelicCyclicHilbertOperator f (adelicRealSL2Embedding g)).restrictScalars ℝ)
    (fun _ _ => rfl) c hc v hv

end
end Dubon2026
