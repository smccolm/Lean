import Dubon2026.FiniteCyclicPeriodQuotient
import Dubon2026.RepresentationCarryPeriod

/-! # Actual finite cyclic periods detect finite-coefficient H2

The original carry cocycle realizes every norm-quotient class, and the proved
finite cyclic H2 computation supplies the cardinality comparison. This gives
the detection step for q-fold cyclic inflation, needed before unramified
support control in DUB-17's global reciprocity and Selmer route.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory

variable {R G : Type} [CommRing R] [CommGroup G] [Fintype G]
  [TopologicalSpace R] [TopologicalSpace G] [DiscreteTopology G]
  (A : Rep R G) [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)

/-- Original carry cocycles realize each original norm-quotient class in
a nontrivial finite cyclic stage, with the chosen generator explicit. -/
theorem finiteCyclicH2PeriodNormMap_surjective (hn : 1 < orderOf g) :
    Function.Surjective (finiteCyclicH2PeriodNormMap A hA g hg) := by
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ u =>
    haveI : NeZero (orderOf g) := ⟨by omega⟩
    let χ := (zmodMulEquivOfGenerator hg (orderOf_eq_card_of_forall_mem_zpowers hg).symm).symm.toMonoidHom
    have hχ : χ g = Multiplicative.ofAdd 1 :=
      zmodMulEquivOfGenerator_symm_apply_generator hg _
    have hu : ∀ z, A.ρ z u.val = u.val :=
      (Representation.mem_invariants_iff_of_forall_mem_zpowers A.ρ g hg u.val).mpr
        (sub_eq_zero.mp u.property)
    let c : continuousRepresentationCocyclesTwo A :=
      ⟨representationCarryCocycle A χ u.val hu, continuous_of_discreteTopology⟩
    refine ⟨Submodule.Quotient.mk c, ?_⟩
    rw [finiteCyclicH2PeriodNormMap_mk]
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    exact representationCarryCocycle_period A χ u.val hu g hχ hn

/-- For finite original coefficients, the literal period map is bijective.
The existing cyclic computation is used only for the finite cardinality
comparison; the actual map is the original cocycle period proved above. -/
theorem finiteCyclicH2PeriodNormMap_bijective [Finite A] (hn : 1 < orderOf g) :
    Function.Bijective (finiteCyclicH2PeriodNormMap A hA g hg) := by
  haveI : Finite (LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap) :=
    Finite.of_injective (fun x : LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap =>
      (x.val : A)) Subtype.val_injective
  haveI : Finite (LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap ⧸
      finiteCyclicInvariantNormRange A g) :=
    Finite.of_surjective (finiteCyclicInvariantNormRange A g).mkQ
      (Submodule.mkQ_surjective _)
  haveI : Finite (ContinuousRepresentationH2 A hA) :=
    Finite.of_equiv _ (continuousFiniteCyclicNormQuotientEquiv A hA g hg).toEquiv
  have hs := finiteCyclicH2PeriodNormMap_surjective A hA g hg hn
  exact ⟨(Finite.injective_iff_surjective_of_equiv
    (continuousFiniteCyclicNormQuotientEquiv A hA g hg).symm.toEquiv).mpr hs, hs⟩

include hg in
/-- A zero literal generator period kills the original continuous H2 class
for finite coefficients. Inflation will supply this period equality. -/
theorem finiteCyclicH2_eq_zero_of_period_zero [Finite A] (hn : 1 < orderOf g)
    (c : continuousRepresentationCocyclesTwo A)
    (hc : representationCyclicTwoCochainPeriodSum A g (orderOf g) c.val = 0) :
    (Submodule.Quotient.mk c : ContinuousRepresentationH2 A hA) = 0 := by
  apply (finiteCyclicH2PeriodNormMap_bijective A hA g hg hn).1
  rw [map_zero, finiteCyclicH2PeriodNormMap_mk]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  change representationCyclicTwoCochainPeriodSum A g (orderOf g) c.val ∈
    LinearMap.range A.norm.hom.toLinearMap
  rw [hc]
  exact Submodule.zero_mem _

end
end Dubon2026
