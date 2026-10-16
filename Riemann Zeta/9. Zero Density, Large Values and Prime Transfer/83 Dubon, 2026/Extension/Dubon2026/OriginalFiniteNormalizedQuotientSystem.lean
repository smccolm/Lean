import Dubon2026.OriginalQuotientH2SubgroupGenerators
import Dubon2026.OriginalQuotientCompletionRestrictions
import Dubon2026.OriginalFiniteNormalizedClassSystem

/-! # The normalized finite system for the actual outside-unit quotient

The full-class H2 isomorphism supplies a full-order quotient class, and
the actual trace/restriction theorem supplies every subgroup generator.
The local compatibility is transported through the literal quotient map.
This discharges the finite quotient coefficient input on DUB-17's route
to class/Ext duality; it does not assert the remaining duality theorem.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- One actual quotient class generates all subgroup H2 groups and has every source-normalized completion restriction, with vanishing subgroup H1 and exact subgroup H2 orders. This proposition alone asserts no existence. -/
def OriginalFiniteNormalizedQuotientSystem : Prop :=
    ∃ u : groupCohomology (originalIdeleClassesModOutsideRep K L S hS) 2,
      addOrderOf u = Module.finrank K L ∧
      (∀ H : Subgroup Gal(L/K), Limits.IsZero
        (groupCohomology (Rep.res H.subtype (originalIdeleClassesModOutsideRep K L S hS)) 1)) ∧
      (∀ H : Subgroup Gal(L/K),
        Nat.card (groupCohomology (Rep.res H.subtype
          (originalIdeleClassesModOutsideRep K L S hS)) 2) = Nat.card H) ∧
      (∀ H : Subgroup Gal(L/K), Submodule.span ℤ
        {(groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype
          (originalIdeleClassesModOutsideRep K L S hS))) 2).hom u} = ⊤) ∧
      OriginalCompletionQuotientRestrictions K L S hS u

/-- The original normalized full-class system descends to the actual outside-unit quotient, discharging every finite subgroup and completion clause. -/
theorem originalClassQuotient_finite_normalized_system
    (hu : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 L),
      w ∉ S → Algebra.IsUnramifiedAt ℤ w.asIdeal)
    (h : OriginalFiniteNormalizedClassSystem K L) :
    OriginalFiniteNormalizedQuotientSystem K L S hS := by
  obtain ⟨u, ho, _, _, _, hl⟩ := h
  let e := (originalClassesModOutsideH2Iso K L S hS hu).toLinearEquiv
  have he : addOrderOf (e u) = Module.finrank K L :=
    (e.toAddEquiv.addOrderOf_eq u).trans ho
  obtain ⟨hcard, hgen⟩ :=
    originalClassQuotient_full_order_restricts_to_generators K L S hS hu (e u) he
  refine ⟨e u, he, fun H => ?_, hcard, hgen, ?_⟩
  · exact originalClassQuotientSubgroup_first_zero K L S hS H hu
  · exact originalClassQuotient_completion_restrictions K L S hS u hl

/-- The same normalized quotient class explicitly writes every subgroup H2 class as an integer multiple of its restriction. This proposition alone asserts no existence. -/
def OriginalFiniteNormalizedQuotientGenerators : Prop :=
    let C := originalIdeleClassesModOutsideRep K L S hS
    ∃ u : groupCohomology C 2,
      addOrderOf u = Module.finrank K L ∧
      (∀ H : Subgroup Gal(L/K), Limits.IsZero (groupCohomology (Rep.res H.subtype C) 1)) ∧
      (∀ H : Subgroup Gal(L/K), Nat.card (groupCohomology (Rep.res H.subtype C) 2) = Nat.card H) ∧
      (∀ (H : Subgroup Gal(L/K)) (x : groupCohomology (Rep.res H.subtype C) 2),
        ∃ z : ℤ, z • (groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype C)) 2).hom u = x) ∧
      OriginalCompletionQuotientRestrictions K L S hS u

/-- Consume the finite quotient class system to obtain integer representatives for every subgroup H2 class using the same source-normalized generator. -/
theorem originalClassQuotient_normalized_system_explicit_generators
    (h : OriginalFiniteNormalizedQuotientSystem K L S hS) :
    OriginalFiniteNormalizedQuotientGenerators K L S hS := by
  obtain ⟨u, ho, h1, hc, hg, hl⟩ := h
  refine ⟨u, ho, h1, hc, fun H x => ?_, hl⟩
  let v := (groupCohomology.map H.subtype
    (𝟙 (Rep.res H.subtype (originalIdeleClassesModOutsideRep K L S hS))) 2).hom u
  have hx : x ∈ Submodule.span ℤ {v} := by
    rw [hg H]
    exact Submodule.mem_top
  obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.mp hx
  refine ⟨z, ?_⟩
  change z • v = x
  rw [← Int.cast_smul_eq_zsmul ℤ z v, Int.cast_id]
  exact hz

end
end Dubon2026
