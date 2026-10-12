import Dubon2026.ContinuousH2AdditiveCoefficientEquiv
import Dubon2026.ContinuousCohomologyCorestriction

/-! # Original corestriction across the actual coefficient-ring identification

The prime-field character line and the integer-linear roots have the same
additively identified coefficients. The literal coset trace comparison lets
the proved root-H2 injection discharge the target assumption in the DUB-17
induced-annihilator argument.
-/

namespace Dubon2026
noncomputable section
open scoped BigOperators

variable {R S G : Type} [CommRing R] [CommRing S] [Group G]
  (A : Rep.{0} R G) (B : Rep.{0} S G)
  (e : A ≃+ B)
  (heρ : ∀ g a, e (A.ρ g a) = B.ρ g (e a))

  (U : Subgroup G) [Fintype (G ⧸ U)]

include heρ in
/-- The original finite coset trace commutes with the actual additive
coefficient identification even when the original scalar rings differ. -/
theorem cosetTraceTwo_additiveCoefficientEquiv (c : U × U → A) (z : G × G) :
    e (cosetTraceTwo A U c z) = cosetTraceTwo B U (fun w => e (c w)) z := by
  change e (∑ q : G ⧸ U, A.ρ (z.1 • z.2 • q).out
      (c (cosetTransition U z.1 (z.2 • q), cosetTransition U z.2 q))) =
    ∑ q : G ⧸ U, B.ρ (z.1 • z.2 • q).out
      (e (c (cosetTransition U z.1 (z.2 • q), cosetTransition U z.2 q)))
  rw [map_sum]
  exact Finset.sum_congr rfl (fun _ _ => heρ _ _)

variable [TopologicalSpace R] [TopologicalSpace S] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [IsTopologicalAddGroup B] [ContinuousSMul S B]
  (he : Continuous e) (hei : Continuous e.symm)
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2)) (hU : IsOpen (U : Set G))

/-- The original continuous H2 equivalence commutes with actual finite-index
corestriction on the original cocycles, not an invariant-defined substitute. -/
theorem continuousH2AdditiveCoefficientEquiv_corestriction
    (x : ContinuousRepresentationH2 (restrictedCoefficientRep A U.subtype)
      (restrictedCoefficientAction_continuous A U.subtype continuous_subtype_val hA)) :
    continuousH2AdditiveCoefficientEquiv A B e he hei heρ hA hB
      (continuousRepresentationH2Corestriction A hA U hU x) =
    continuousRepresentationH2Corestriction B hB U hU
      (continuousH2AdditiveCoefficientEquiv (restrictedCoefficientRep A U.subtype)
        (restrictedCoefficientRep B U.subtype) e he hei (fun g a => heρ g a)
        (restrictedCoefficientAction_continuous A U.subtype continuous_subtype_val hA)
        (restrictedCoefficientAction_continuous B U.subtype continuous_subtype_val hB) x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    rw [continuousRepresentationH2Corestriction_mk, continuousH2AdditiveCoefficientEquiv_mk,
      continuousH2AdditiveCoefficientEquiv_mk, continuousRepresentationH2Corestriction_mk]
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    funext z
    exact cosetTraceTwo_additiveCoefficientEquiv A B e heρ U c.val z

end
end Dubon2026
