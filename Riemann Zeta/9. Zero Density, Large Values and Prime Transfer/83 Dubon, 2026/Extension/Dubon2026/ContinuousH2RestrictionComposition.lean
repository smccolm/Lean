import Dubon2026.ContinuousCohomologyRestriction

/-! # Composition of the original continuous H2 restrictions

This identifies the constructed finite-stage vanishing with its actual
absolute restriction, on the required route to unramified local support
in DUB-17 global reciprocity and Selmer duality.
-/

namespace Dubon2026
noncomputable section

variable {R G H L : Type} [CommRing R] [Group G] [Group H] [Group L]
  [TopologicalSpace R] [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace L]
  [IsTopologicalGroup G] [IsTopologicalGroup H] [IsTopologicalGroup L]
  (A : Rep R G) [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (j : H →* G) (hj : Continuous j) (k : L →* H) (hk : Continuous k)

/-- The actual continuous H2 pullback along a composition is the composition
of the original H2 pullbacks, with the original coefficient action. -/
theorem continuousRepresentationH2Restriction_comp
    (x : ContinuousRepresentationH2 A hA) :
    continuousRepresentationH2Restriction A hA (j.comp k) (hj.comp hk) x =
      continuousRepresentationH2Restriction (restrictedCoefficientRep A j)
        (restrictedCoefficientAction_continuous A j hj hA) k hk
        (continuousRepresentationH2Restriction A hA j hj x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ c => rfl

end
end Dubon2026
