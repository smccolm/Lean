import Dubon2026.ContinuousCohomologyCup
import Dubon2026.ContinuousCohomologyRestriction

/-! # Actual continuous cup products commute with the genuine restriction maps -/

namespace Dubon2026
noncomputable section

variable {R G H : Type} [CommRing R] [Group G] [Group H]
  [TopologicalSpace R] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]
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
  (j : H →* G) (hj : Continuous j)

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
/-- The original continuous cup cochain restricts to the cup of the original
restricted cocycles, with the same actual pairing and restricted coefficient actions. -/
theorem continuousOneCocycleCup_restriction
    (f : continuousRepresentationCocyclesOne A) (u : continuousRepresentationCocyclesOne B) :
    continuousRepresentationCocycleTwoRestriction C j hj
        (continuousOneCocycleCup A B C β hβ hcβ hB f u) =
      continuousOneCocycleCup (restrictedCoefficientRep A j) (restrictedCoefficientRep B j)
        (restrictedCoefficientRep C j) β (fun h x y => hβ (j h) x y) hcβ
        (restrictedCoefficientAction_continuous B j hj hB)
        (continuousRepresentationCocycleOneRestriction A j hj f)
        (continuousRepresentationCocycleOneRestriction B j hj u) := by
  rfl

/-- The genuine continuous cup pairing commutes with the actual H1 and H2
restriction maps. Both sides preserve the original continuous quotient relations. -/
theorem continuousH1Cup_restriction
    (x : ContinuousRepresentationH1 A hA) (y : ContinuousRepresentationH1 B hB) :
    continuousRepresentationH2Restriction C hC j hj
        (continuousH1Cup A B C β hβ hcβ hA hB hC x y) =
      continuousH1Cup (restrictedCoefficientRep A j) (restrictedCoefficientRep B j)
        (restrictedCoefficientRep C j) β (fun h v w => hβ (j h) v w) hcβ
        (restrictedCoefficientAction_continuous A j hj hA)
        (restrictedCoefficientAction_continuous B j hj hB)
        (restrictedCoefficientAction_continuous C j hj hC)
        (continuousRepresentationH1Restriction A hA j hj x)
        (continuousRepresentationH1Restriction B hB j hj y) := by
  induction x using Quotient.inductionOn' with
  | h f =>
    induction y using Quotient.inductionOn' with
    | h u => rfl

end
end Dubon2026
