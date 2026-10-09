import Dubon2026.AdelicLocalBoundedHecke
import Dubon2026.RealClosedCyclicSubspace

/-! # The original closed cyclic Hilbert space of the genuine single-place cusp action -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The literal closed span of the original single-place translates of the original cusp generator. -/
def adelicLocalCyclicClosedSpan (v : HeightOneSpectrum ℤ) : Submodule ℂ (AdelicCyclicHilbert f) :=
  (Submodule.span ℂ (Set.range (fun g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ) =>
    adelicCyclicLocalRepresentation f v g (adelicCyclicHilbertGenerator f)))).topologicalClosure

/-- The original single-place cyclic Hilbert subspace is closed. -/
theorem adelicLocalCyclicClosedSpan_isClosed (v : HeightOneSpectrum ℤ) :
    IsClosed (adelicLocalCyclicClosedSpan f v : Set (AdelicCyclicHilbert f)) :=
  Submodule.isClosed_topologicalClosure _

/-- Every original local translate belongs to its genuine local cyclic closure. -/
theorem adelicLocalCyclicClosedSpan_orbit_mem (v : HeightOneSpectrum ℤ)
    (g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) :
    adelicCyclicLocalRepresentation f v g (adelicCyclicHilbertGenerator f) ∈
      adelicLocalCyclicClosedSpan f v :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨g, rfl⟩)

/-- The actual original cusp generator belongs to its local cyclic closure. -/
theorem adelicLocalCyclicClosedSpan_generator_mem (v : HeightOneSpectrum ℤ) :
    adelicCyclicHilbertGenerator f ∈ adelicLocalCyclicClosedSpan f v := by
  simpa only [map_one, Module.End.one_apply] using adelicLocalCyclicClosedSpan_orbit_mem f v 1

/-- The actual single-place cyclic closure is invariant under the same original local action. -/
theorem adelicLocalCyclicClosedSpan_invariant (v : HeightOneSpectrum ℤ)
    (g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) (x : AdelicCyclicHilbert f)
    (hx : x ∈ adelicLocalCyclicClosedSpan f v) :
    adelicCyclicLocalRepresentation f v g x ∈ adelicLocalCyclicClosedSpan f v :=
  @closedCyclicSpan_invariant (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance
    (adelicCyclicLocalRepresentation f v) (adelicCyclicLocalOperator f v) (fun _ _ => rfl)
    (adelicCyclicHilbertGenerator f) g x hx

/-- Restriction of the actual original local group action to its genuine closed cyclic space. -/
def adelicLocalCyclicRepresentation (v : HeightOneSpectrum ℤ) :
    Representation ℂ (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
      (adelicLocalCyclicClosedSpan f v) :=
  Representation.subrepresentation (adelicCyclicLocalRepresentation f v)
    (adelicLocalCyclicClosedSpan f v) (fun g x hx => adelicLocalCyclicClosedSpan_invariant f v g x hx)

/-- The local cyclic restriction is exactly the original single-place Hilbert action. -/
theorem adelicLocalCyclicRepresentation_apply (v : HeightOneSpectrum ℤ)
    (g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) (x : adelicLocalCyclicClosedSpan f v) :
    (adelicLocalCyclicRepresentation f v g x).val = adelicCyclicLocalRepresentation f v g x.val := rfl

end
end Dubon2026
