import Dubon2026.AdelicEveryLocalFixedLine
import Dubon2026.AdelicLocalFullMixedCoefficient

/-! # Actual coefficient and Gram factorization at every original finite place -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- At every original finite place, the original local and real-plus-away matrix coefficient factors with the genuine original generator norm. -/
theorem adelicEveryLocal_fullAway_coefficient_factor (F : PrimitiveCuspForm N k) (hk : 0 < k) (v : HeightOneSpectrum ℤ)
    (g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (a : AdelicFullAwayGroup v) :
    inner ℂ (adelicCyclicHilbertGenerator F.toCuspForm)
      (adelicCyclicLocalRepresentation F.toCuspForm v g
        (adelicCyclicFullAwayRepresentation F.toCuspForm v a
          (adelicCyclicHilbertGenerator F.toCuspForm))) *
      inner ℂ (adelicCyclicHilbertGenerator F.toCuspForm) (adelicCyclicHilbertGenerator F.toCuspForm) =
    inner ℂ (adelicCyclicHilbertGenerator F.toCuspForm)
      (adelicCyclicLocalRepresentation F.toCuspForm v g
        (adelicCyclicHilbertGenerator F.toCuspForm)) *
      inner ℂ (adelicCyclicHilbertGenerator F.toCuspForm)
        (adelicCyclicFullAwayRepresentation F.toCuspForm v a
          (adelicCyclicHilbertGenerator F.toCuspForm)) := by
  obtain ⟨c, hc⟩ := adelicEveryLocalCyclicProjection_fixed_scalar F hk v _
    (adelicCyclicFullAway_generator_local_fixed F.toCuspForm _ a)
  exact @unitary_projection_coefficient_factor
    (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (AdelicCyclicHilbert F.toCuspForm) inferInstance inferInstance inferInstance
    (adelicCyclicLocalRepresentation F.toCuspForm _) (adelicCyclicLocalRepresentation_inner F.toCuspForm _)
    (adelicLocalCyclicClosedSpan F.toCuspForm _) inferInstance
    (adelicLocalCyclicClosedSpan_invariant F.toCuspForm _) _ _
    (adelicLocalCyclicClosedSpan_generator_mem F.toCuspForm _) c hc g

/-- The full genuine mixed Gram matrix factors between the original local and real-plus-away orbit vectors at every original finite place. -/
theorem adelicEveryLocal_fullAway_mixed_gram (F : PrimitiveCuspForm N k) (hk : 0 < k) (v : HeightOneSpectrum ℤ)
    (g₁ g₂ : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (a₁ a₂ : AdelicFullAwayGroup v) :
    inner ℂ
      (adelicCyclicLocalRepresentation F.toCuspForm v g₁
        (adelicCyclicFullAwayRepresentation F.toCuspForm v a₁
          (adelicCyclicHilbertGenerator F.toCuspForm)))
      (adelicCyclicLocalRepresentation F.toCuspForm v g₂
        (adelicCyclicFullAwayRepresentation F.toCuspForm v a₂
          (adelicCyclicHilbertGenerator F.toCuspForm))) *
      inner ℂ (adelicCyclicHilbertGenerator F.toCuspForm) (adelicCyclicHilbertGenerator F.toCuspForm) =
    inner ℂ
      (adelicCyclicLocalRepresentation F.toCuspForm v g₁
        (adelicCyclicHilbertGenerator F.toCuspForm))
      (adelicCyclicLocalRepresentation F.toCuspForm v g₂
        (adelicCyclicHilbertGenerator F.toCuspForm)) *
    inner ℂ
      (adelicCyclicFullAwayRepresentation F.toCuspForm v a₁
        (adelicCyclicHilbertGenerator F.toCuspForm))
      (adelicCyclicFullAwayRepresentation F.toCuspForm v a₂
        (adelicCyclicHilbertGenerator F.toCuspForm)) :=
  @commuting_unitary_mixed_gram
    (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (AdelicFullAwayGroup v)
    (AdelicCyclicHilbert F.toCuspForm) inferInstance inferInstance inferInstance inferInstance
    (adelicCyclicLocalRepresentation F.toCuspForm _) (adelicCyclicFullAwayRepresentation F.toCuspForm _)
    (adelicCyclicLocalRepresentation_inner F.toCuspForm _)
    (fun a x y => adelicCyclicHilbertRepresentation_inner F.toCuspForm
      (adelicFullAwayEmbedding _ a) x y)
    (adelicCyclicLocal_fullAway_commute F.toCuspForm _) (adelicCyclicHilbertGenerator F.toCuspForm)
    (adelicEveryLocal_fullAway_coefficient_factor F hk v) g₁ g₂ a₁ a₂


end
end Dubon2026
