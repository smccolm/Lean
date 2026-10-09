import Dubon2026.AdelicLocalFullAwayFixedProjection
import Dubon2026.AdelicLocalFullAwayTensor

/-! # The entire original good-prime fixed space is the actual full complementary cyclic closure -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

variable {N p : ℕ} [NeZero N] [NeZero p] [Fact p.Prime] {k : ℤ}
    (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)

include hpN

/-- The genuine local fixed projector sends every vector of the original full adelic Hilbert representation into the actual full complementary cyclic closure. -/
theorem adelicLocalFixedProjection_mem_fullAwayClosure (x : AdelicCyclicHilbert F.toCuspForm) :
    adelicLocalFixedProjection F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) x ∈
      (adelicFullAwayCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))).topologicalClosure := by
  let v := rationalPrimePlace p (Fact.out : p.Prime)
  let S := (adelicFullAwayCyclicCore F.toCuspForm v).topologicalClosure
  let P := adelicLocalFixedProjection F.toCuspForm v
  have ho (b : RationalAdelicGL2) : P (adelicCyclicHilbertRepresentation F.toCuspForm b
      (adelicCyclicHilbertGenerator F.toCuspForm)) ∈ S := by
    obtain ⟨⟨g, a⟩, rfl⟩ := (adelicLocalFullAwayEquiv v).surjective b
    have he := adelicCyclicFullAway_local_factor F.toCuspForm v g a
      (adelicCyclicHilbertGenerator F.toCuspForm)
    obtain ⟨c, hc⟩ := adelicLocalFixedProjection_primitive_orbit_scalar F hpN g
    change adelicLocalFixedProjection F.toCuspForm v _ ∈ S
    have he' := (congrArg P he).trans
      (adelicLocalFixedProjection_fullAway_commutes F.toCuspForm v a _)
    have he'' := congrArg (adelicCyclicFullAwayRepresentation F.toCuspForm v a) hc
    have hm := (adelicCyclicFullAwayRepresentation F.toCuspForm v a).map_smul c
      (adelicCyclicHilbertGenerator F.toCuspForm)
    exact (he'.trans (he''.trans hm)).symm ▸
      S.smul_mem c (Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨a, rfl⟩))
  have hs : Submodule.span ℂ (Set.range (fun b : RationalAdelicGL2 =>
      adelicCyclicHilbertRepresentation F.toCuspForm b (adelicCyclicHilbertGenerator F.toCuspForm))) ≤
      S.comap P.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨b, rfl⟩
    exact ho b
  have hx : x ∈ closure ((Submodule.span ℂ (Set.range (fun b : RationalAdelicGL2 =>
      adelicCyclicHilbertRepresentation F.toCuspForm b (adelicCyclicHilbertGenerator F.toCuspForm)))) :
      Set (AdelicCyclicHilbert F.toCuspForm)) := by
    rw [adelicCyclicHilbertGenerator_cyclic]
    exact Set.mem_univ x
  exact closure_minimal hs ((Submodule.isClosed_topologicalClosure _).preimage P.continuous) hx

/-- The full original local integral-fixed Hilbert space is precisely the actual cyclic closure under the full real-plus-away group. -/
theorem adelicLocalFixedSpace_eq_fullAwayClosure :
    adelicLocalFixedSpace F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) =
      (adelicFullAwayCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))).topologicalClosure := by
  apply le_antisymm
  · intro x hx
    have he : adelicLocalFixedProjection F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) x = x :=
      (@Submodule.starProjection_eq_self_iff ℂ (AdelicCyclicHilbert F.toCuspForm)
        inferInstance inferInstance inferInstance (adelicLocalFixedSpace F.toCuspForm _) inferInstance x).mpr hx
    exact he ▸ adelicLocalFixedProjection_mem_fullAwayClosure F hpN x
  · intro x hx
    have hs : adelicFullAwayCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) ≤
        adelicLocalFixedSpace F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨a, rfl⟩
      exact adelicCyclicFullAway_generator_local_fixed F.toCuspForm _ a
    exact closure_minimal hs (adelicLocalFixedSpace_isClosed F.toCuspForm _) hx

end
end Dubon2026
