import Dubon2026.CosetCupProjectionHomotopy
import Dubon2026.ContinuousH1Corestriction
import Dubon2026.ContinuousCohomologyCorestriction
import Dubon2026.ContinuousCupRestriction

/-! # The actual continuous cup projection formula for original corestriction

The explicit coset homotopy is continuous. Thus the literal cup, restriction and
corestriction maps satisfy the compatibility needed for cyclotomic descent.
-/

namespace Dubon2026
noncomputable section

open scoped BigOperators

variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A B C : Rep R G)
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [IsTopologicalAddGroup B] [ContinuousSMul R B]
  [TopologicalSpace C] [IsTopologicalAddGroup C] [ContinuousSMul R C]
  (β : A →ₗ[R] B →ₗ[R] C)
  (hβ : ∀ g x y, β (A.ρ g x) (B.ρ g y) = C.ρ g (β x y))
  (hcβ : Continuous (fun z : A × B => β z.1 z.2))
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))
  (hC : Continuous (fun z : G × C => C.ρ z.1 z.2))
  (S : Subgroup G) [Fintype (G ⧸ S)] (hS : IsOpen (S : Set G))

include hcβ hB hS in
omit [ContinuousSMul R C] in
/-- The original projection-formula correction is an actual continuous
cochain, with continuity derived from the original open subgroup and cocycles. -/
theorem cosetCupProjectionCorrection_continuous
    (c : continuousRepresentationCocyclesOne A)
    (v : continuousRepresentationCocyclesOne (restrictedCoefficientRep B S.subtype)) :
    Continuous (cosetCupProjectionCorrection A B C β S c.val v.val) := by
  letI : DiscreteTopology (G ⧸ S) := QuotientGroup.discreteTopology hS
  have hout : Continuous (fun q : G ⧸ S => q.out) := continuous_of_discreteTopology
  apply continuous_finsetSum
  intro q _
  exact hcβ.comp ((c.property.comp (hout.comp (continuous_id.smul continuous_const))).prodMk
    (hB.comp ((hout.comp (continuous_id.smul continuous_const)).prodMk
      (v.property.comp ((cosetTransition_continuous S hS).comp
        (continuous_id.prodMk continuous_const))))))

/-- Cup with an original class commutes with actual continuous corestriction
after restricting that same class to the original subgroup. The equality is
proved using the explicit original continuous coset homotopy. -/
theorem continuousH1Cup_corestriction_projection
    (x : ContinuousRepresentationH1 A hA)
    (y : ContinuousRepresentationH1 (restrictedCoefficientRep B S.subtype)
      (restrictedCoefficientAction_continuous B S.subtype continuous_subtype_val hB)) :
    continuousRepresentationH2Corestriction C hC S hS
      (continuousH1Cup (restrictedCoefficientRep A S.subtype)
        (restrictedCoefficientRep B S.subtype) (restrictedCoefficientRep C S.subtype)
        β (fun g a b => hβ g a b) hcβ
        (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA)
        (restrictedCoefficientAction_continuous B S.subtype continuous_subtype_val hB)
        (restrictedCoefficientAction_continuous C S.subtype continuous_subtype_val hC)
        (continuousRepresentationH1Restriction A hA S.subtype continuous_subtype_val x) y) =
      continuousH1Cup A B C β hβ hcβ hA hB hC x
        (continuousRepresentationH1Corestriction B hB S hS y) := by
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    induction y using Submodule.Quotient.induction_on with
    | _ v =>
      let w : C(G, C) := ⟨cosetCupProjectionCorrection A B C β S c.val v.val,
        cosetCupProjectionCorrection_continuous A B C β hcβ hB S hS c v⟩
      have he : continuousCosetTraceTwo C hC S hS
          (continuousOneCocycleCup (restrictedCoefficientRep A S.subtype)
            (restrictedCoefficientRep B S.subtype) (restrictedCoefficientRep C S.subtype)
            β (fun g a b => hβ g a b) hcβ
            (restrictedCoefficientAction_continuous B S.subtype continuous_subtype_val hB)
            (continuousRepresentationCocycleOneRestriction A S.subtype continuous_subtype_val c) v) =
          continuousOneCocycleCup A B C β hβ hcβ hB c
            (continuousCosetTraceOneCocycle B hB S hS v) +
              continuousRepresentationCoboundaryTwo C hC w := by
        apply Subtype.ext
        apply Subtype.ext
        exact cosetCupProjection_homotopy A B C β hβ S c.val v.val
      have hz : (Submodule.Quotient.mk (continuousRepresentationCoboundaryTwo C hC w) :
          ContinuousRepresentationH2 C hC) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).mpr ⟨w, rfl⟩
      rw [continuousRepresentationH1Restriction_mk, continuousH1Cup_mk,
        continuousRepresentationH2Corestriction_mk, he, Submodule.Quotient.mk_add, hz,
        add_zero, continuousRepresentationH1Corestriction_mk, continuousH1Cup_mk]

end
end Dubon2026
