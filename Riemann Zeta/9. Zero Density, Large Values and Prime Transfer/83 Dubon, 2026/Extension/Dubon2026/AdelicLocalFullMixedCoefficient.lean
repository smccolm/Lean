import Dubon2026.AdelicLocalCyclicProjection
import Dubon2026.AdelicLocalFullAwayProduct
import Dubon2026.CyclicProjectionCoefficient

/-! # Genuine local and real-plus-away matrix coefficients of the original primitive cusp representation -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The genuine original full complementary group acts by restricting the actual full adelic representation. -/
def adelicCyclicFullAwayRepresentation (v : HeightOneSpectrum ℤ) :
    Representation ℂ (AdelicFullAwayGroup v) (AdelicCyclicHilbert f) :=
  (adelicCyclicHilbertRepresentation f).comp
    (adelicFullAwayEmbedding v)

/-- Actual full complementary and local actions commute on the entire original Hilbert space. -/
theorem adelicCyclicLocal_fullAway_commute (v : HeightOneSpectrum ℤ)
    (g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) (a : AdelicFullAwayGroup v)
    (x : AdelicCyclicHilbert f) :
    adelicCyclicLocalRepresentation f v g (adelicCyclicFullAwayRepresentation f v a x) =
      adelicCyclicFullAwayRepresentation f v a (adelicCyclicLocalRepresentation f v g x) := by
  have he := (adelicLocal_fullAway_commute v g a).map (adelicCyclicHilbertRepresentation f)
  exact LinearMap.congr_fun he.eq x

/-- An actual full complementary translate of the original cusp generator retains its genuine local level invariance. -/
theorem adelicCyclicFullAway_generator_local_fixed (v : HeightOneSpectrum ℤ)
    (a : AdelicFullAwayGroup v) :
    adelicCyclicFullAwayRepresentation f v a (adelicCyclicHilbertGenerator f) ∈ adelicLocalFixedSpace f v := by
  intro g
  change adelicCyclicLocalRepresentation f v g.val
    (adelicCyclicFullAwayRepresentation f v a (adelicCyclicHilbertGenerator f)) = _
  rw [adelicCyclicLocal_fullAway_commute]
  exact congrArg (adelicCyclicFullAwayRepresentation f v a)
    ((adelicCyclicHilbertGenerator_mem_localFixed f v) g)

/-- At every good prime, the original local and real-plus-away matrix coefficient factors with the genuine original generator norm. -/
theorem adelicCyclicLocal_fullAway_coefficient_factor {p : ℕ} [NeZero p] [Fact p.Prime]
    (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    (g : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ))
    (a : AdelicFullAwayGroup (rationalPrimePlace p (Fact.out : p.Prime))) :
    inner ℂ (adelicCyclicHilbertGenerator F.toCuspForm)
      (adelicCyclicLocalRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) g
        (adelicCyclicFullAwayRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) a
          (adelicCyclicHilbertGenerator F.toCuspForm))) *
      inner ℂ (adelicCyclicHilbertGenerator F.toCuspForm) (adelicCyclicHilbertGenerator F.toCuspForm) =
    inner ℂ (adelicCyclicHilbertGenerator F.toCuspForm)
      (adelicCyclicLocalRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) g
        (adelicCyclicHilbertGenerator F.toCuspForm)) *
      inner ℂ (adelicCyclicHilbertGenerator F.toCuspForm)
        (adelicCyclicFullAwayRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) a
          (adelicCyclicHilbertGenerator F.toCuspForm)) := by
  obtain ⟨c, hc⟩ := adelicLocalCyclicProjection_fixed_scalar F hpN _
    (adelicCyclicFullAway_generator_local_fixed F.toCuspForm _ a)
  exact @unitary_projection_coefficient_factor
    (GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ))
    (AdelicCyclicHilbert F.toCuspForm) inferInstance inferInstance inferInstance
    (adelicCyclicLocalRepresentation F.toCuspForm _) (adelicCyclicLocalRepresentation_inner F.toCuspForm _)
    (adelicLocalCyclicClosedSpan F.toCuspForm _) inferInstance
    (adelicLocalCyclicClosedSpan_invariant F.toCuspForm _) _ _
    (adelicLocalCyclicClosedSpan_generator_mem F.toCuspForm _) c hc g

/-- The full genuine mixed Gram matrix factors between the original local and real-plus-away orbit vectors at every good prime. -/
theorem adelicCyclicLocal_fullAway_mixed_gram {p : ℕ} [NeZero p] [Fact p.Prime]
    (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    (g₁ g₂ : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ))
    (a₁ a₂ : AdelicFullAwayGroup (rationalPrimePlace p (Fact.out : p.Prime))) :
    inner ℂ
      (adelicCyclicLocalRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) g₁
        (adelicCyclicFullAwayRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) a₁
          (adelicCyclicHilbertGenerator F.toCuspForm)))
      (adelicCyclicLocalRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) g₂
        (adelicCyclicFullAwayRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) a₂
          (adelicCyclicHilbertGenerator F.toCuspForm))) *
      inner ℂ (adelicCyclicHilbertGenerator F.toCuspForm) (adelicCyclicHilbertGenerator F.toCuspForm) =
    inner ℂ
      (adelicCyclicLocalRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) g₁
        (adelicCyclicHilbertGenerator F.toCuspForm))
      (adelicCyclicLocalRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) g₂
        (adelicCyclicHilbertGenerator F.toCuspForm)) *
    inner ℂ
      (adelicCyclicFullAwayRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) a₁
        (adelicCyclicHilbertGenerator F.toCuspForm))
      (adelicCyclicFullAwayRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) a₂
        (adelicCyclicHilbertGenerator F.toCuspForm)) :=
  @commuting_unitary_mixed_gram
    (GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ))
    (AdelicFullAwayGroup (rationalPrimePlace p (Fact.out : p.Prime)))
    (AdelicCyclicHilbert F.toCuspForm) inferInstance inferInstance inferInstance inferInstance
    (adelicCyclicLocalRepresentation F.toCuspForm _) (adelicCyclicFullAwayRepresentation F.toCuspForm _)
    (adelicCyclicLocalRepresentation_inner F.toCuspForm _)
    (fun a x y => adelicCyclicHilbertRepresentation_inner F.toCuspForm
      (adelicFullAwayEmbedding _ a) x y)
    (adelicCyclicLocal_fullAway_commute F.toCuspForm _) (adelicCyclicHilbertGenerator F.toCuspForm)
    (adelicCyclicLocal_fullAway_coefficient_factor F hpN) g₁ g₂ a₁ a₂

end
end Dubon2026
