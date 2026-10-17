import Dubon2026.OriginalInertiaFixedField
import Dubon2026.OriginalAdicIntegralNormRepresentative
import Dubon2026.OriginalFinitePrimeOrbits

/-! # Integral norm representatives for actual inertia subgroups

Reindexing through the literal inertia fixed field identifies both the
completion action and its actual group norm. The proved totally ramified
adjustment then gives integral representatives for the original subgroup
coefficient, removing the ramification premise from DUB-17's inertia step.
-/
namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField BigOperators
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (w : HeightOneSpectrum (𝓞 L))
  (S : Subgroup (OriginalFiniteDecompositionGroup K L w))
  (hS : S.map (OriginalFiniteDecompositionGroup K L w).subtype ≤ w.asIdeal.inertia Gal(L/K))

/-- The original inertia subgroup reindexed as the full decomposition
group above its actual fixed field. -/
def originalAdicInertiaSubgroupEquiv :
    S ≃* OriginalFiniteDecompositionGroup
      (IntermediateField.fixedField (S.map (OriginalFiniteDecompositionGroup K L w).subtype)) L w :=
  (S.equivMapOfInjective (OriginalFiniteDecompositionGroup K L w).subtype
    (Subgroup.subtype_injective _)).trans (originalInertiaFixedDecompositionEquiv w _ hS)

omit [NumberField K] [IsGalois K L] in
/-- These are the same original completed transports on every unit. -/
theorem originalAdicInertiaSubgroup_action (σ : S) (x : originalAdicUnitRep K L w) :
    (originalAdicUnitRep
      (IntermediateField.fixedField (S.map (OriginalFiniteDecompositionGroup K L w).subtype)) L w).ρ
      (originalAdicInertiaSubgroupEquiv w S hS σ) x =
    (originalAdicUnitRep K L w).ρ σ.val x := rfl

include hS in
omit [NumberField K] [IsGalois K L] in
/-- The fixed-field and original inertia subgroup norms agree literally. -/
theorem originalAdicInertiaSubgroup_norm [Fintype S]
    [Fintype (OriginalFiniteDecompositionGroup
      (IntermediateField.fixedField (S.map (OriginalFiniteDecompositionGroup K L w).subtype)) L w)]
    (x : originalAdicUnitRep K L w) :
    (Rep.res S.subtype (originalAdicUnitRep K L w)).ρ.norm x =
      (originalAdicUnitRep
        (IntermediateField.fixedField (S.map (OriginalFiniteDecompositionGroup K L w).subtype)) L w).ρ.norm x := by
  simp only [Representation.norm, LinearMap.sum_apply]
  apply Fintype.sum_equiv (originalAdicInertiaSubgroupEquiv w S hS).toEquiv
  intro σ
  exact (originalAdicInertiaSubgroup_action w S hS σ x).symm

include hS in
/-- Every invariant under an actual inertia subgroup has an integral
representative modulo its literal subgroup norm, without a ramification
or fixed-field comparison premise. -/
theorem originalAdicInertiaSubgroup_exists_integral_mod_norm [Fintype S]
    (x : (Rep.res S.subtype (originalAdicUnitRep K L w)).ρ.invariants) :
    ∃ b : originalAdicUnitRep K L w,
      (x.val - (Rep.res S.subtype (originalAdicUnitRep K L w)).ρ.norm b).toMul ∈
        (w.adicCompletionIntegers L).units := by
  let T := S.map (OriginalFiniteDecompositionGroup K L w).subtype
  let F := IntermediateField.fixedField T
  let D := OriginalFiniteDecompositionGroup F L w
  letI : Fintype D := Fintype.ofFinite _
  let v := originalFinitePrimeBelow F L w
  letI : w.asIdeal.LiesOver v.asIdeal := originalFinitePrimeBelow_liesOver F L w
  let e := originalAdicInertiaSubgroupEquiv w S hS
  let y : (originalAdicUnitRep F L w).ρ.invariants := ⟨x.val, by
    intro τ
    obtain ⟨σ, rfl⟩ := e.surjective τ
    exact (originalAdicInertiaSubgroup_action w S hS σ x.val).trans (x.property σ)⟩
  obtain ⟨b, hb⟩ := originalAdicUnit_exists_integral_mod_norm F L v w
    (originalInertiaFixedField_ramification_eq_card w T hS v) y
  refine ⟨b, ?_⟩
  rw [originalAdicInertiaSubgroup_norm w S hS b]
  exact hb

end
end Dubon2026
