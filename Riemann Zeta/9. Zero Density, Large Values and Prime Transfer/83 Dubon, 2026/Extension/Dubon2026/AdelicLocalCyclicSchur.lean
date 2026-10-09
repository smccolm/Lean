import Dubon2026.AdelicLocalCyclicFixedLine
import Dubon2026.ContinuousCyclicScalar

/-! # Original bounded local intertwiners act scalarly on the genuine primitive cyclic Hilbert space -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

/-- A genuine original local bounded intertwiner whose generator image lies in the actual local cyclic space acts by one scalar on that entire space. -/
theorem adelicLocalCyclic_intertwiner_scalar {N p : ℕ} [NeZero N] [NeZero p]
    [Fact p.Prime] {k : ℤ} (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    (T : AdelicCyclicHilbert F.toCuspForm →L[ℂ] AdelicCyclicHilbert F.toCuspForm)
    (hT : ∀ g x, T (adelicCyclicLocalRepresentation F.toCuspForm
      (rationalPrimePlace p (Fact.out : p.Prime)) g x) =
        adelicCyclicLocalRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) g (T x))
    (hcyclic : T (adelicCyclicHilbertGenerator F.toCuspForm) ∈
      adelicLocalCyclicClosedSpan F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) :
    ∃ c : ℂ, ∀ x ∈ adelicLocalCyclicClosedSpan F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)),
      T x = c • x := by
  have hfixed : T (adelicCyclicHilbertGenerator F.toCuspForm) ∈
      adelicLocalFixedSpace F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) := by
    intro g
    change adelicCyclicLocalRepresentation F.toCuspForm
      (rationalPrimePlace p (Fact.out : p.Prime)) g.val (T (adelicCyclicHilbertGenerator F.toCuspForm)) = _
    rw [← hT]
    exact congrArg T ((adelicCyclicHilbertGenerator_mem_localFixed F.toCuspForm _) g)
  obtain ⟨c, hc⟩ := adelicLocalCyclic_fixed_generator_scalar F hpN _ hcyclic hfixed
  refine ⟨c, fun x hx => ?_⟩
  apply @continuousLinearMap_scalar_on_closedSpan (AdelicCyclicHilbert F.toCuspForm)
    (GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ))
    inferInstance inferInstance T c
    (fun g => adelicCyclicLocalRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))
      g (adelicCyclicHilbertGenerator F.toCuspForm))
  · intro g
    rw [hT, hc, map_smul]
  · exact hx

end
end Dubon2026
