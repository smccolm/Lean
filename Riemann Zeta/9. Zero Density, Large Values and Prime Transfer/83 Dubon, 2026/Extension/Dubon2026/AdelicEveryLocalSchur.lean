import Dubon2026.AdelicEveryLocalFixedLine
import Dubon2026.ContinuousCyclicScalar

/-! # Original bounded local intertwiners act scalarly on the genuine primitive cyclic Hilbert space -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

/-- A genuine original local bounded intertwiner whose generator image lies in the actual local cyclic space acts by one scalar on that entire space. -/
theorem adelicEveryLocalCyclic_intertwiner_scalar {N : ℕ} [NeZero N] {k : ℤ} (F : PrimitiveCuspForm N k) (hk : 0 < k) (v : HeightOneSpectrum ℤ)
    (T : AdelicCyclicHilbert F.toCuspForm →L[ℂ] AdelicCyclicHilbert F.toCuspForm)
    (hT : ∀ g x, T (adelicCyclicLocalRepresentation F.toCuspForm
      v g x) =
        adelicCyclicLocalRepresentation F.toCuspForm v g (T x))
    (hcyclic : T (adelicCyclicHilbertGenerator F.toCuspForm) ∈
      adelicLocalCyclicClosedSpan F.toCuspForm v) :
    ∃ c : ℂ, ∀ x ∈ adelicLocalCyclicClosedSpan F.toCuspForm v,
      T x = c • x := by
  have hfixed : T (adelicCyclicHilbertGenerator F.toCuspForm) ∈
      adelicLocalFixedSpace F.toCuspForm v := by
    intro g
    change adelicCyclicLocalRepresentation F.toCuspForm
      v g.val (T (adelicCyclicHilbertGenerator F.toCuspForm)) = _
    rw [← hT]
    exact congrArg T ((adelicCyclicHilbertGenerator_mem_localFixed F.toCuspForm _) g)
  obtain ⟨c, hc⟩ := adelicEveryLocalCyclic_fixed_generator_scalar F hk v _ hcyclic hfixed
  refine ⟨c, fun x hx => ?_⟩
  apply @continuousLinearMap_scalar_on_closedSpan (AdelicCyclicHilbert F.toCuspForm)
    (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    inferInstance inferInstance T c
    (fun g => adelicCyclicLocalRepresentation F.toCuspForm v
      g (adelicCyclicHilbertGenerator F.toCuspForm))
  · intro g
    rw [hT, hc, map_smul]
  · exact hx

end
end Dubon2026
