import Dubon2026.AdelicLocalCyclicSchur
import Dubon2026.UnitaryInvariantProjection
import Dubon2026.ScalarProjectionSubspace

/-! # Genuine good-prime local cyclic Hilbert irreducibility for the original primitive cusp form -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

/-- The original primitive good-prime cyclic Hilbert space has no nonzero proper closed subspace invariant under its genuine local GL2 action. -/
theorem adelicLocalCyclicClosedSpan_irreducible {N p : ℕ} [NeZero N] [NeZero p]
    [Fact p.Prime] {k : ℤ} (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    (S : Submodule ℂ (AdelicCyclicHilbert F.toCuspForm))
    (hclosed : IsClosed (S : Set (AdelicCyclicHilbert F.toCuspForm)))
    (hle : S ≤ adelicLocalCyclicClosedSpan F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
    (hinv : ∀ g x, x ∈ S → adelicCyclicLocalRepresentation F.toCuspForm
      (rationalPrimePlace p (Fact.out : p.Prime)) g x ∈ S) :
    S = ⊥ ∨ S = adelicLocalCyclicClosedSpan F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) := by
  letI : CompleteSpace S := hclosed.isComplete.completeSpace_coe
  let T : AdelicCyclicHilbert F.toCuspForm →L[ℂ] AdelicCyclicHilbert F.toCuspForm :=
    @Submodule.starProjection ℂ (AdelicCyclicHilbert F.toCuspForm)
      inferInstance inferInstance inferInstance S inferInstance
  have hT : ∀ g x, T (adelicCyclicLocalRepresentation F.toCuspForm
      (rationalPrimePlace p (Fact.out : p.Prime)) g x) =
        adelicCyclicLocalRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) g (T x) := by
    intro g x
    exact @unitary_invariant_starProjection
      (GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ))
      (AdelicCyclicHilbert F.toCuspForm) inferInstance inferInstance inferInstance
      (adelicCyclicLocalRepresentation F.toCuspForm _)
      (adelicCyclicLocalRepresentation_inner F.toCuspForm _) S inferInstance hinv g x
  have hs := adelicLocalCyclic_intertwiner_scalar F hpN T hT
    (hle (@Submodule.starProjection_apply_mem ℂ (AdelicCyclicHilbert F.toCuspForm)
      inferInstance inferInstance inferInstance S inferInstance (adelicCyclicHilbertGenerator F.toCuspForm)))
  exact @scalarProjection_eq_bot_or_eq (AdelicCyclicHilbert F.toCuspForm)
    inferInstance inferInstance S (adelicLocalCyclicClosedSpan F.toCuspForm _) inferInstance hle
    (adelicCyclicHilbertGenerator F.toCuspForm)
    (adelicLocalCyclicClosedSpan_generator_mem F.toCuspForm _)
    (adelicCyclicHilbertGenerator_ne_zero F.toCuspForm (primitiveCuspForm_ne_zero F)) hs

end
end Dubon2026
