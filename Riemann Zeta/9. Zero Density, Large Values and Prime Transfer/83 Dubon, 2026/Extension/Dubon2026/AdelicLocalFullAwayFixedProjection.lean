import Dubon2026.AdelicLocalCoreProjection
import Dubon2026.AdelicLocalFullMixedCoefficient

/-! # The actual local integral-fixed projection and the original full complementary action -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- Actual local/full-complement coordinates factor every original group operator in commuting order. -/
theorem adelicCyclicFullAway_local_factor (v : HeightOneSpectrum ℤ)
    (g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) (a : AdelicFullAwayGroup v)
    (x : AdelicCyclicHilbert f) :
    adelicCyclicHilbertRepresentation f (adelicLocalFullAwayEquiv v (g, a)) x =
      adelicCyclicFullAwayRepresentation f v a (adelicCyclicLocalRepresentation f v g x) := by
  have he := @representation_hom_mul_apply RationalAdelicGL2 RationalAdelicGL2
    (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance inferInstance
    (adelicCyclicHilbertRepresentation f) (MonoidHom.id _)
    (rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 v g)) (adelicFullAwayEmbedding v a) x
  rw [← adelicLocalFullAwayEquiv_factor] at he
  exact he.trans (adelicCyclicLocal_fullAway_commute f v g a x)

/-- Every original full complementary operator preserves the entire genuine local integral-fixed Hilbert space. -/
theorem adelicLocalFixedSpace_fullAway_invariant (v : HeightOneSpectrum ℤ)
    (a : AdelicFullAwayGroup v) (x : AdelicCyclicHilbert f) (hx : x ∈ adelicLocalFixedSpace f v) :
    adelicCyclicFullAwayRepresentation f v a x ∈ adelicLocalFixedSpace f v := by
  intro g
  change adelicCyclicLocalRepresentation f v g.val (adelicCyclicFullAwayRepresentation f v a x) = _
  rw [adelicCyclicLocal_fullAway_commute]
  exact congrArg (adelicCyclicFullAwayRepresentation f v a) (hx g)

/-- The genuine local fixed projector commutes with every actual full complementary group operator. -/
theorem adelicLocalFixedProjection_fullAway_commutes (v : HeightOneSpectrum ℤ)
    (a : AdelicFullAwayGroup v) (x : AdelicCyclicHilbert f) :
    adelicLocalFixedProjection f v (adelicCyclicFullAwayRepresentation f v a x) =
      adelicCyclicFullAwayRepresentation f v a (adelicLocalFixedProjection f v x) :=
  @unitary_invariant_starProjection (AdelicFullAwayGroup v) (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance
    (adelicCyclicFullAwayRepresentation f v)
    (fun a x y => adelicCyclicHilbertRepresentation_inner f (adelicFullAwayEmbedding v a) x y)
    (adelicLocalFixedSpace f v) inferInstance (adelicLocalFixedSpace_fullAway_invariant f v) a x

/-- The actual compact local fixed projector sends each original primitive local orbit vector onto the literal original generator line. -/
theorem adelicLocalFixedProjection_primitive_orbit_scalar {p : ℕ} [NeZero p] [Fact p.Prime]
    (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    (g : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)) :
    ∃ c : ℂ, adelicLocalFixedProjection F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))
      (adelicCyclicLocalRepresentation F.toCuspForm _ g (adelicCyclicHilbertGenerator F.toCuspForm)) =
        c • adelicCyclicHilbertGenerator F.toCuspForm := by
  have hcore := adelicLocalFixedProjection_mem_invariantCore F.toCuspForm
    (rationalPrimePlace p (Fact.out : p.Prime)) (adelicLocalCyclicCore F.toCuspForm _) le_rfl
    (adelicLocalCyclicCore_invariant F.toCuspForm _) _ (Submodule.subset_span ⟨g, rfl⟩)
  exact adelicLocalCyclic_fixed_generator_scalar F hpN _
    (Submodule.le_topologicalClosure _ hcore) (adelicLocalFixedProjection_mem F.toCuspForm _ _)

end
end Dubon2026
