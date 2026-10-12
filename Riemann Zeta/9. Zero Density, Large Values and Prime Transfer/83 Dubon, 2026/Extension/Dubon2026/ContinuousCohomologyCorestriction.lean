import Dubon2026.ContinuousCosetTrace
import Dubon2026.CosetTraceRestrictionHomotopy
import Dubon2026.ContinuousCohomologyRestriction

/-! # Actual continuous corestriction and its exact restriction-index identity -/

namespace Dubon2026
noncomputable section

open scoped BigOperators

variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep R G) [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (S : Subgroup G) [Fintype (G ⧸ S)] (hS : IsOpen (S : Set G))

/-- Corestriction on the original continuous H2 quotient is induced by
the genuine finite coset sum, preserving actual continuous coboundaries. -/
def continuousRepresentationH2Corestriction :
    ContinuousRepresentationH2 (restrictedCoefficientRep A S.subtype)
        (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA) →ₗ[R]
      ContinuousRepresentationH2 A hA := by
  have hb : continuousRepresentationCoboundariesTwo (restrictedCoefficientRep A S.subtype)
      (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA) ≤
      (continuousRepresentationCoboundariesTwo A hA).comap (continuousCosetTraceTwo A hA S hS) := by
    rintro _ ⟨f, rfl⟩
    exact ⟨continuousCosetTraceOne A hA S hS f, (continuousCosetTraceTwo_coboundary A hA S hS f).symm⟩
  exact Submodule.mapQ (R := R) (R₂ := R)
    (M := continuousRepresentationCocyclesTwo (restrictedCoefficientRep A S.subtype))
    (M₂ := continuousRepresentationCocyclesTwo A) (τ₁₂ := RingHom.id R)
    (continuousRepresentationCoboundariesTwo (restrictedCoefficientRep A S.subtype)
      (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA))
    (continuousRepresentationCoboundariesTwo A hA) (continuousCosetTraceTwo A hA S hS) hb

/-- Actual corestriction retains the literal finite trace cocycle. -/
theorem continuousRepresentationH2Corestriction_mk
    (c : continuousRepresentationCocyclesTwo (restrictedCoefficientRep A S.subtype)) :
    continuousRepresentationH2Corestriction A hA S hS (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (continuousCosetTraceTwo A hA S hS c) := rfl

include hS in
/-- The explicit original homotopy has a genuinely continuous cochain
witness, using openness of the original subgroup. -/
theorem cosetRestrictionHomotopy_continuous (c : continuousRepresentationCocyclesTwo A) :
    Continuous (cosetRestrictionHomotopy A S c.val) := by
  letI : DiscreteTopology (G ⧸ S) := QuotientGroup.discreteTopology hS
  have hout : Continuous (fun q : G ⧸ S => q.out) := continuous_of_discreteTopology
  apply continuous_finsetSum
  intro q _
  exact (c.property.comp (continuous_id.prodMk continuous_const)).sub
    (c.property.comp ((hout.comp (continuous_id.smul continuous_const)).prodMk
      (continuous_subtype_val.comp ((cosetTransition_continuous S hS).comp
        (continuous_id.prodMk continuous_const)))))

/-- Actual continuous restriction followed by the genuine coset-sum
corestriction is multiplication by the exact original subgroup index.
The equality is proved with an explicit continuous coboundary. -/
theorem continuousRepresentationH2Corestriction_restriction
    (x : ContinuousRepresentationH2 A hA) :
    continuousRepresentationH2Corestriction A hA S hS
      (continuousRepresentationH2Restriction A hA S.subtype continuous_subtype_val x) =
        Fintype.card (G ⧸ S) • x := by
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    change Submodule.Quotient.mk
        (continuousCosetTraceTwo A hA S hS
          (continuousRepresentationCocycleTwoRestriction A S.subtype continuous_subtype_val c)) =
      (Submodule.Quotient.mk (Fintype.card (G ⧸ S) • c) : ContinuousRepresentationH2 A hA)
    symm
    apply (continuousRepresentationH2_eq_iff A hA _ _).mpr
    refine ⟨⟨cosetRestrictionHomotopy A S c.val, cosetRestrictionHomotopy_continuous A S hS c⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact cosetRestrictionHomotopy_differential A S c.val

end
end Dubon2026
