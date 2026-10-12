import Dubon2026.ContinuousCohomologyCorestriction
import Dubon2026.ContinuousCohomologyCoefficientMap

/-! # Actual H2 corestriction commutes with the original coefficient map

This is the Kummer-inclusion square needed to transfer the proved original unit
invariant under corestriction to the root coefficients in cyclotomic descent.
-/

namespace Dubon2026
noncomputable section

open scoped BigOperators

variable {R G : Type} [CommRing R] [Group G] (A B : Rep R G)
  (φ : A →ₗ[R] B) (hφρ : ∀ g a, φ (A.ρ g a) = B.ρ g (φ a))
  (S : Subgroup G) [Fintype (G ⧸ S)]

include hφρ in
/-- The original coefficient map commutes with the literal finite coset
trace, on the original two-cochains and original coefficient actions. -/
theorem cosetTraceTwo_coefficient_map (c : S × S → A) (z : G × G) :
    φ (cosetTraceTwo A S c z) = cosetTraceTwo B S (fun w => φ (c w)) z := by
  change φ (∑ q : G ⧸ S, A.ρ (z.1 • z.2 • q).out
      (c (cosetTransition S z.1 (z.2 • q), cosetTransition S z.2 q))) =
    ∑ q : G ⧸ S, B.ρ (z.1 • z.2 • q).out
      (φ (c (cosetTransition S z.1 (z.2 • q), cosetTransition S z.2 q)))
  rw [map_sum]
  exact Finset.sum_congr rfl (fun q _ => hφρ _ _)

variable [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [IsTopologicalAddGroup B] [ContinuousSMul R B]
  (hφ : Continuous φ)
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))
  (hS : IsOpen (S : Set G))

/-- The original continuous H2 coefficient map and actual corestriction
commute, with the original restricted coefficient actions on the subgroup. -/
theorem continuousCoefficientH2Map_corestriction
    (x : ContinuousRepresentationH2 (restrictedCoefficientRep A S.subtype)
      (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA)) :
    continuousCoefficientH2Map A B φ hφ hφρ hA hB
      (continuousRepresentationH2Corestriction A hA S hS x) =
      continuousRepresentationH2Corestriction B hB S hS
        (continuousCoefficientH2Map (restrictedCoefficientRep A S.subtype)
          (restrictedCoefficientRep B S.subtype) φ hφ (fun g a => hφρ g a)
          (restrictedCoefficientAction_continuous A S.subtype continuous_subtype_val hA)
          (restrictedCoefficientAction_continuous B S.subtype continuous_subtype_val hB) x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    rw [continuousRepresentationH2Corestriction_mk, continuousCoefficientH2Map_mk,
      continuousCoefficientH2Map_mk, continuousRepresentationH2Corestriction_mk]
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    funext z
    exact cosetTraceTwo_coefficient_map A B φ hφρ S c.val z

end
end Dubon2026
