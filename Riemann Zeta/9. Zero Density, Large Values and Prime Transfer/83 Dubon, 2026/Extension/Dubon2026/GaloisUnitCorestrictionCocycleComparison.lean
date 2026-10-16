import Dubon2026.GaloisUnitContinuousCorestriction

/-! # Comparing literal subgroup traces with genuine field corestriction

A proved equality of fixing subgroups and equality of the original
cocycle values suffice. This is the precise transport needed to apply
the local invariant theorem to DUB-17's arithmetic Mackey summands.
-/
namespace Dubon2026
noncomputable section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois E Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)]

/-- Equality of the actual subgroup and original two-cocycle values
identifies the literal continuous trace with genuine field corestriction. -/
theorem galoisUnitContinuousCorestriction_eq_subgroupTrace
    (S : Subgroup Gal(Ω/K)) (hS : IsOpen (S : Set Gal(Ω/K)))
    [iS : Fintype (Gal(Ω/K) ⧸ S)] (hSE : S = E.fixingSubgroup)
    (z : continuousRepresentationCocyclesTwo
      (restrictedCoefficientRep (Rep.ofAlgebraAutOnUnits K Ω) S.subtype))
    (y : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits E Ω))
    (hz : ∀ g h : S, z.val (g, h) =
      y.val (E.fixingSubgroupEquiv ⟨g.val, hSE ▸ g.property⟩,
        E.fixingSubgroupEquiv ⟨h.val, hSE ▸ h.property⟩)) :
    continuousRepresentationH2Corestriction (Rep.ofAlgebraAutOnUnits K Ω)
        (discreteGaloisUnitAction_continuous (K := K) (Ω := Ω)) S hS (Submodule.Quotient.mk z) =
      galoisUnitContinuousCorestriction K Ω E (Submodule.Quotient.mk y) := by
  subst S
  have he : z = galoisFixingUnitCocycle K Ω E y := by
    apply Subtype.ext
    apply Subtype.ext
    funext w
    exact hz w.1 w.2
  subst z
  have hi : iS = Fintype.ofFinite (Gal(Ω/K) ⧸ E.fixingSubgroup) := Subsingleton.elim _ _
  cases hi
  rfl

end
end Dubon2026
