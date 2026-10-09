import Dubon2026.AdelicPrimitiveIntertwinerLine
import Dubon2026.ContinuousCyclicScalar

/-! # Scalar commutant of the original full primitive adelic Hilbert representation -/

namespace Dubon2026

noncomputable section

/-- Every bounded intertwiner of the original full primitive adelic representation is scalar on its entire genuine Hilbert space. -/
theorem adelicPrimitiveIntertwiner_scalar {N : ℕ} [NeZero N] {k : ℤ}
    (f : PrimitiveCuspForm N k) (hk : 0 < k)
    (A : AdelicCyclicHilbert f.toCuspForm →L[ℂ] AdelicCyclicHilbert f.toCuspForm)
    (hA : ∀ g v, A (adelicCyclicHilbertRepresentation f.toCuspForm g v) =
      adelicCyclicHilbertRepresentation f.toCuspForm g (A v)) :
    ∃ c : ℂ, ∀ v, A v = c • v := by
  obtain ⟨c, hc⟩ := adelicPrimitiveIntertwiner_generator_scalar f hk A hA
  refine ⟨c, fun v => ?_⟩
  apply @continuousLinearMap_scalar_on_closedSpan (AdelicCyclicHilbert f.toCuspForm)
    RationalAdelicGL2 inferInstance inferInstance A c
    (fun g => adelicCyclicHilbertRepresentation f.toCuspForm g
      (adelicCyclicHilbertGenerator f.toCuspForm))
  · intro g
    rw [hA, hc, map_smul]
  · change v ∈ closure ((Submodule.span ℂ (Set.range (fun g : RationalAdelicGL2 =>
      adelicCyclicHilbertRepresentation f.toCuspForm g
        (adelicCyclicHilbertGenerator f.toCuspForm)))) : Set (AdelicCyclicHilbert f.toCuspForm))
    rw [adelicCyclicHilbertGenerator_cyclic]
    trivial

end
end Dubon2026
