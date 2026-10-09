import Dubon2026.AdelicLocalCyclicProjection
import Dubon2026.AdelicLocalAwayFixed
import Dubon2026.CyclicProjectionCoefficient

/-! # Genuine local and away-place matrix coefficients of the original primitive cusp representation -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

/-- The literal subgroup of original finite adelic matrices with identity at a specified genuine place. -/
def finiteAdelicAwayGroup (v : HeightOneSpectrum ℤ) :
    Subgroup (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :=
  (GeneralLinearGroup.map (finiteAdelePlace v)).ker

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The genuine original away-place group acts by restricting the actual full adelic representation. -/
def adelicCyclicAwayRepresentation (v : HeightOneSpectrum ℤ) :
    Representation ℂ (finiteAdelicAwayGroup v) (AdelicCyclicHilbert f) :=
  (adelicCyclicHilbertRepresentation f).comp
    (rationalAdelicFiniteGL2Embedding.comp (finiteAdelicAwayGroup v).subtype)

/-- Actual away-place and local actions commute on the entire original Hilbert space. -/
theorem adelicCyclicLocal_away_commute (v : HeightOneSpectrum ℤ)
    (g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) (a : finiteAdelicAwayGroup v)
    (x : AdelicCyclicHilbert f) :
    adelicCyclicLocalRepresentation f v g (adelicCyclicAwayRepresentation f v a x) =
      adelicCyclicAwayRepresentation f v a (adelicCyclicLocalRepresentation f v g x) := by
  have he := ((finiteAdelicLocalGL2_commute_of_place_one v a.val a.property g).map
    rationalAdelicFiniteGL2Embedding).map (adelicCyclicHilbertRepresentation f)
  exact (LinearMap.congr_fun he.eq x).symm

/-- An actual away-place translate of the original cusp generator retains its genuine local level invariance. -/
theorem adelicCyclicAway_generator_local_fixed (v : HeightOneSpectrum ℤ)
    (a : finiteAdelicAwayGroup v) :
    adelicCyclicAwayRepresentation f v a (adelicCyclicHilbertGenerator f) ∈ adelicLocalFixedSpace f v := by
  intro g
  change adelicCyclicLocalRepresentation f v g.val
    (adelicCyclicAwayRepresentation f v a (adelicCyclicHilbertGenerator f)) = _
  rw [adelicCyclicLocal_away_commute]
  exact congrArg (adelicCyclicAwayRepresentation f v a)
    ((adelicCyclicHilbertGenerator_mem_localFixed f v) g)

/-- At every good prime, the original local and away-place matrix coefficient factors with the genuine original generator norm. -/
theorem adelicCyclicLocal_away_coefficient_factor {p : ℕ} [NeZero p] [Fact p.Prime]
    (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    (g : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ))
    (a : finiteAdelicAwayGroup (rationalPrimePlace p (Fact.out : p.Prime))) :
    inner ℂ (adelicCyclicHilbertGenerator F.toCuspForm)
      (adelicCyclicLocalRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) g
        (adelicCyclicAwayRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) a
          (adelicCyclicHilbertGenerator F.toCuspForm))) *
      inner ℂ (adelicCyclicHilbertGenerator F.toCuspForm) (adelicCyclicHilbertGenerator F.toCuspForm) =
    inner ℂ (adelicCyclicHilbertGenerator F.toCuspForm)
      (adelicCyclicLocalRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) g
        (adelicCyclicHilbertGenerator F.toCuspForm)) *
      inner ℂ (adelicCyclicHilbertGenerator F.toCuspForm)
        (adelicCyclicAwayRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) a
          (adelicCyclicHilbertGenerator F.toCuspForm)) := by
  obtain ⟨c, hc⟩ := adelicLocalCyclicProjection_fixed_scalar F hpN _
    (adelicCyclicAway_generator_local_fixed F.toCuspForm _ a)
  exact @unitary_projection_coefficient_factor
    (GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ))
    (AdelicCyclicHilbert F.toCuspForm) inferInstance inferInstance inferInstance
    (adelicCyclicLocalRepresentation F.toCuspForm _) (adelicCyclicLocalRepresentation_inner F.toCuspForm _)
    (adelicLocalCyclicClosedSpan F.toCuspForm _) inferInstance
    (adelicLocalCyclicClosedSpan_invariant F.toCuspForm _) _ _
    (adelicLocalCyclicClosedSpan_generator_mem F.toCuspForm _) c hc g

/-- The full genuine mixed Gram matrix factors between the original local and away-place orbit vectors at every good prime. -/
theorem adelicCyclicLocal_away_mixed_gram {p : ℕ} [NeZero p] [Fact p.Prime]
    (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    (g₁ g₂ : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ))
    (a₁ a₂ : finiteAdelicAwayGroup (rationalPrimePlace p (Fact.out : p.Prime))) :
    inner ℂ
      (adelicCyclicLocalRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) g₁
        (adelicCyclicAwayRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) a₁
          (adelicCyclicHilbertGenerator F.toCuspForm)))
      (adelicCyclicLocalRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) g₂
        (adelicCyclicAwayRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) a₂
          (adelicCyclicHilbertGenerator F.toCuspForm))) *
      inner ℂ (adelicCyclicHilbertGenerator F.toCuspForm) (adelicCyclicHilbertGenerator F.toCuspForm) =
    inner ℂ
      (adelicCyclicLocalRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) g₁
        (adelicCyclicHilbertGenerator F.toCuspForm))
      (adelicCyclicLocalRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) g₂
        (adelicCyclicHilbertGenerator F.toCuspForm)) *
    inner ℂ
      (adelicCyclicAwayRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) a₁
        (adelicCyclicHilbertGenerator F.toCuspForm))
      (adelicCyclicAwayRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) a₂
        (adelicCyclicHilbertGenerator F.toCuspForm)) :=
  @commuting_unitary_mixed_gram
    (GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ))
    (finiteAdelicAwayGroup (rationalPrimePlace p (Fact.out : p.Prime)))
    (AdelicCyclicHilbert F.toCuspForm) inferInstance inferInstance inferInstance inferInstance
    (adelicCyclicLocalRepresentation F.toCuspForm _) (adelicCyclicAwayRepresentation F.toCuspForm _)
    (adelicCyclicLocalRepresentation_inner F.toCuspForm _)
    (fun a x y => adelicCyclicHilbertRepresentation_inner F.toCuspForm
      (rationalAdelicFiniteGL2Embedding a.val) x y)
    (adelicCyclicLocal_away_commute F.toCuspForm _) (adelicCyclicHilbertGenerator F.toCuspForm)
    (adelicCyclicLocal_away_coefficient_factor F hpN) g₁ g₂ a₁ a₂

end
end Dubon2026
