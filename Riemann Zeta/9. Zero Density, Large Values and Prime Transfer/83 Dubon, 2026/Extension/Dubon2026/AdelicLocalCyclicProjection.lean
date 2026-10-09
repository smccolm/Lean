import Dubon2026.AdelicLocalCyclicFixedLine
import Dubon2026.UnitaryInvariantProjection

/-! # The actual projector onto the original local cyclic Hilbert factor -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The original closed local cyclic Hilbert subspace is complete in its actual inherited norm. -/
instance adelicLocalCyclicClosedSpan_complete (v : HeightOneSpectrum ℤ) :
    CompleteSpace (adelicLocalCyclicClosedSpan f v) :=
  (adelicLocalCyclicClosedSpan_isClosed f v).isComplete.completeSpace_coe

/-- Genuine orthogonal projection onto the literal original local cyclic Hilbert space. -/
def adelicLocalCyclicProjection (v : HeightOneSpectrum ℤ) :
    AdelicCyclicHilbert f →L[ℂ] AdelicCyclicHilbert f :=
  @Submodule.starProjection ℂ (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance
    (adelicLocalCyclicClosedSpan f v) inferInstance

/-- The actual local cyclic projector fixes the original cusp generator. -/
theorem adelicLocalCyclicProjection_generator (v : HeightOneSpectrum ℤ) :
    adelicLocalCyclicProjection f v (adelicCyclicHilbertGenerator f) = adelicCyclicHilbertGenerator f :=
  (@Submodule.starProjection_eq_self_iff ℂ (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance (adelicLocalCyclicClosedSpan f v) inferInstance _).mpr
      (adelicLocalCyclicClosedSpan_generator_mem f v)

/-- The original local cyclic projector commutes with every genuine action at that same place. -/
theorem adelicLocalCyclicProjection_commutes (v : HeightOneSpectrum ℤ)
    (g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) (x : AdelicCyclicHilbert f) :
    adelicLocalCyclicProjection f v (adelicCyclicLocalRepresentation f v g x) =
      adelicCyclicLocalRepresentation f v g (adelicLocalCyclicProjection f v x) :=
  @unitary_invariant_starProjection (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance
    (adelicCyclicLocalRepresentation f v) (adelicCyclicLocalRepresentation_inner f v)
    (adelicLocalCyclicClosedSpan f v) inferInstance (adelicLocalCyclicClosedSpan_invariant f v) g x

/-- Projection onto the actual local cyclic space preserves every genuine local level-fixed equation. -/
theorem adelicLocalCyclicProjection_fixed (v : HeightOneSpectrum ℤ)
    (x : AdelicCyclicHilbert f) (hx : x ∈ adelicLocalFixedSpace f v) :
    adelicLocalCyclicProjection f v x ∈ adelicLocalFixedSpace f v := by
  intro g
  change adelicCyclicLocalRepresentation f v g.val (adelicLocalCyclicProjection f v x) = _
  rw [← adelicLocalCyclicProjection_commutes]
  exact congrArg (adelicLocalCyclicProjection f v) (hx g)

/-- The genuine original inner product with the cusp generator is unchanged by local cyclic projection. -/
theorem adelicLocalCyclicProjection_inner_generator (v : HeightOneSpectrum ℤ)
    (x : AdelicCyclicHilbert f) :
    inner ℂ (adelicCyclicHilbertGenerator f) (adelicLocalCyclicProjection f v x) =
      inner ℂ (adelicCyclicHilbertGenerator f) x := by
  have he := @Submodule.inner_starProjection_left_eq_right ℂ (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance (adelicLocalCyclicClosedSpan f v) inferInstance
    (adelicCyclicHilbertGenerator f) x
  change inner ℂ (adelicLocalCyclicProjection f v (adelicCyclicHilbertGenerator f)) x =
    inner ℂ (adelicCyclicHilbertGenerator f) (adelicLocalCyclicProjection f v x) at he
  rw [adelicLocalCyclicProjection_generator] at he
  exact he.symm

/-- At a good prime, every actual ambient level-fixed vector projects onto the original primitive generator line. -/
theorem adelicLocalCyclicProjection_fixed_scalar {p : ℕ} [NeZero p] [Fact p.Prime]
    (F : PrimitiveCuspForm N k) (hpN : p.Coprime N) (x : AdelicCyclicHilbert F.toCuspForm)
    (hx : x ∈ adelicLocalFixedSpace F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) :
    ∃ c : ℂ, adelicLocalCyclicProjection F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) x =
      c • adelicCyclicHilbertGenerator F.toCuspForm :=
  adelicLocalCyclic_fixed_generator_scalar F hpN _
    (@Submodule.starProjection_apply_mem ℂ (AdelicCyclicHilbert F.toCuspForm)
      inferInstance inferInstance inferInstance
      (adelicLocalCyclicClosedSpan F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) inferInstance x)
    (adelicLocalCyclicProjection_fixed F.toCuspForm _ x hx)

end
end Dubon2026
