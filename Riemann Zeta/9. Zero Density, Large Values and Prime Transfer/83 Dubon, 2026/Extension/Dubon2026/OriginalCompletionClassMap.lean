import Dubon2026.OriginalAdicFundamentalAcyclicity
import Dubon2026.OriginalFiniteNormalizedClassSystem

/-! # The actual completion-to-class map and full-order comparison

The single-place idele map followed by the actual class quotient is the
coefficient map used in the source normalization. Compatibility with a
full-order global class forces full local order by the proved local H2
bound. This removes the local-order premise from DUB-17's norm comparison.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField
attribute [-instance] UniformSpace.Completion.instSMul
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

/-- The literal single-completion unit map to the actual idele classes. -/
def originalCompletionClassRepHom :
    originalAdicUnitRep K L w ⟶
      Rep.res (OriginalFiniteDecompositionGroup K L w).subtype (originalIdeleClassRep K L) :=
  originalIdeleSingleFiniteRepHom K L w ≫
    (Rep.resFunctor (OriginalFiniteDecompositionGroup K L w).subtype).map
      (originalFullClassRepHom K L)

include v in
/-- The actual local class mapping to the restriction of a full-order
global class has full decomposition-group order. -/
theorem originalCompletionClass_full_order
    (u : groupCohomology (originalIdeleClassRep K L) 2)
    (hu : addOrderOf u = Module.finrank K L)
    (z : groupCohomology (originalAdicUnitRep K L w) 2)
    (hz : (groupCohomology.functor ℤ (OriginalFiniteDecompositionGroup K L w) 2).map
        (originalCompletionClassRepHom K L w) z =
      groupCohomology.map (OriginalFiniteDecompositionGroup K L w).subtype (𝟙 _) 2 u) :
    addOrderOf z = Nat.card (OriginalFiniteDecompositionGroup K L w) := by
  let D := OriginalFiniteDecompositionGroup K L w
  let C := originalIdeleClassRep K L
  let a := groupCohomology.map D.subtype (𝟙 (Rep.res D.subtype C)) 2 u
  obtain ⟨hc, hg⟩ := originalIdeleClass_full_order_restricts_to_generators K L u hu
  have ha : ∀ x : groupCohomology (Rep.res D.subtype C) 2,
      x ∈ AddSubgroup.zmultiples a := by
    intro x
    have hx : x ∈ Submodule.span ℤ {a} := by rw [hg D]; trivial
    obtain ⟨j, hj⟩ := Submodule.mem_span_singleton.mp hx
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨j, by
      rw [← Int.cast_smul_eq_zsmul ℤ j a, Int.cast_id]
      exact hj⟩
  have ho : addOrderOf a = Nat.card D :=
    (addOrderOf_eq_card_of_forall_mem_zmultiples ha).trans (hc D)
  letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
    (originalAdicBaseChangeMap K L v w).toAlgebra
  haveI := (originalAdicBaseChange_finite_galois K L v w).1
  haveI := (originalAdicBaseChange_finite_galois K L v w).2
  letI : ValuativeRel (v.adicCompletion K) :=
    ValuativeRel.ofValuation (NormedField.valuation (K := v.adicCompletion K))
  haveI := originalAdic_isNonarchimedeanLocalField K v
  obtain ⟨hf, hd⟩ := localField_finite_galois_second_cohomology_card_dvd
    (v.adicCompletion K) (w.adicCompletion L)
  haveI := hf
  let e := (originalAdicUnitCohomologyIso K L v w 2).toLinearEquiv.toEquiv
  haveI : Finite (groupCohomology (originalAdicUnitRep K L w) 2) := Finite.of_equiv _ e
  have hb : Nat.card (groupCohomology (originalAdicUnitRep K L w) 2) ≤ Nat.card D := by
    rw [← Nat.card_congr e]
    have he := Nat.card_congr (originalAdicDecompositionGaloisEquiv K L v w).toEquiv
    rw [← he] at hd
    exact Nat.le_of_dvd (Nat.card_pos (α := D)) hd
  change ((groupCohomology.functor ℤ D 2).map (originalCompletionClassRepHom K L w)) z = a at hz
  have hdiv : Nat.card D ∣ addOrderOf z := by
    rw [← ho, ← hz]
    exact addOrderOf_map_dvd
      ((groupCohomology.functor ℤ D 2).map (originalCompletionClassRepHom K L w)).hom.toAddMonoidHom z
  letI : Fintype (groupCohomology (originalAdicUnitRep K L w) 2) := Fintype.ofFinite _
  apply le_antisymm
  · exact (addOrderOf_le_card_univ (x := z)).trans (Nat.card_eq_fintype_card.symm.le.trans hb)
  · exact Nat.le_of_dvd (addOrderOf_pos z) hdiv

end
end Dubon2026
