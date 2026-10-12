import Dubon2026.FiniteCoinducedCoefficientUnit
import Mathlib.RepresentationTheory.Invariants

/-! # The actual finite coinduced quotient coefficient sequence

The original unit image and its literal quotient provide the exact sequence
used with the proved character-dual cup adjunction in DUB-17's local duality
argument. Finiteness and continuity of the quotient action are derived from
the original coefficient and finite open cosets.
-/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G] (A : Rep.{0} R G) (S : Subgroup G)

/-- The actual coefficient-unit image is stable under the original coinduced action. -/
theorem finiteCoinducedCoefficientUnit_range_stable (g : G) :
    (finiteCoinducedCoefficientUnit A S).range ≤
      (finiteCoinducedCoefficientUnit A S).range.comap
        ((Rep.coind S.subtype (Rep.res S.subtype A)).ρ g) := by
  rintro _ ⟨a, rfl⟩
  exact ⟨A.ρ g a, finiteCoinducedCoefficientUnit_equivariant A S g a⟩

/-- The literal quotient of the actual finite coinduced coefficients by the original unit image. -/
def finiteCoinducedCoefficientQuotient : Rep R G :=
  (Rep.coind S.subtype (Rep.res S.subtype A)).quotient
    (finiteCoinducedCoefficientUnit A S).range (finiteCoinducedCoefficientUnit_range_stable A S)

/-- The actual quotient projection keeps the original unit-image relation. -/
def finiteCoinducedCoefficientProjection :
    Rep.coind S.subtype (Rep.res S.subtype A) →ₗ[R] finiteCoinducedCoefficientQuotient A S :=
  (finiteCoinducedCoefficientUnit A S).range.mkQ

/-- The actual quotient map intertwines the original coefficient actions. -/
theorem finiteCoinducedCoefficientProjection_equivariant (g : G)
    (b : Rep.coind S.subtype (Rep.res S.subtype A)) :
    finiteCoinducedCoefficientProjection A S ((Rep.coind S.subtype (Rep.res S.subtype A)).ρ g b) =
      (finiteCoinducedCoefficientQuotient A S).ρ g (finiteCoinducedCoefficientProjection A S b) := rfl

/-- The original unit and literal quotient projection form an exact coefficient sequence. -/
theorem finiteCoinducedCoefficientSequence_exact :
    Function.Injective (finiteCoinducedCoefficientUnit A S) ∧
      Function.Surjective (finiteCoinducedCoefficientProjection A S) ∧
      (finiteCoinducedCoefficientUnit A S).range = (finiteCoinducedCoefficientProjection A S).ker :=
  ⟨finiteCoinducedCoefficientUnit_injective A S, Submodule.mkQ_surjective _,
    (Submodule.ker_mkQ _).symm⟩

/-- The actual quotient coefficient is finite whenever the original coefficient and cosets are finite. -/
theorem finiteCoinducedCoefficientQuotient_finite [Finite A] [Finite (G ⧸ S)] :
    Finite (finiteCoinducedCoefficientQuotient A S) := by
  haveI := coinducedCoefficient_finite A S
  exact Finite.of_surjective (finiteCoinducedCoefficientProjection A S)
    (finiteCoinducedCoefficientSequence_exact A S).2.1

variable [TopologicalSpace G]

/-- A surjective map of discrete original coefficients carries continuity of
the original action to the actual quotient action, using a discrete section. -/
theorem discreteCoefficientQuotientAction_continuous (B C : Rep.{0} R G)
    [TopologicalSpace B] [DiscreteTopology B] [TopologicalSpace C] [DiscreteTopology C]
    (ψ : B →ₗ[R] C) (hψ : Function.Surjective ψ)
    (hψρ : ∀ g b, ψ (B.ρ g b) = C.ρ g (ψ b))
    (hB : Continuous (fun z : G × B => B.ρ z.1 z.2)) :
    Continuous (fun z : G × C => C.ρ z.1 z.2) := by
  have hs : Continuous (Function.surjInv hψ) := continuous_of_discreteTopology
  have hp : Continuous ψ := continuous_of_discreteTopology
  have ht := hp.comp (hB.comp (continuous_fst.prodMk (hs.comp continuous_snd)))
  exact ht.congr (fun z => by
    change ψ (B.ρ z.1 (Function.surjInv hψ z.2)) = C.ρ z.1 z.2
    rw [hψρ, Function.surjInv_eq hψ])

variable [IsTopologicalGroup G] [TopologicalSpace A] [DiscreteTopology A]
  [Finite (G ⧸ S)]
  [TopologicalSpace (Rep.coind S.subtype (Rep.res S.subtype A))]
  [DiscreteTopology (Rep.coind S.subtype (Rep.res S.subtype A))]
  [TopologicalSpace (finiteCoinducedCoefficientQuotient A S)]
  [DiscreteTopology (finiteCoinducedCoefficientQuotient A S)]

/-- The actual finite coinduced quotient action is continuous under the
original open-subgroup and original continuous coefficient-action hypotheses. -/
theorem finiteCoinducedCoefficientQuotientAction_continuous
    (hA : Continuous (fun z : G × A => A.ρ z.1 z.2)) (hS : IsOpen (S : Set G)) :
    Continuous (fun z : G × finiteCoinducedCoefficientQuotient A S =>
      (finiteCoinducedCoefficientQuotient A S).ρ z.1 z.2) :=
  discreteCoefficientQuotientAction_continuous (Rep.coind S.subtype (Rep.res S.subtype A))
    (finiteCoinducedCoefficientQuotient A S) (finiteCoinducedCoefficientProjection A S)
    (finiteCoinducedCoefficientSequence_exact A S).2.1
    (finiteCoinducedCoefficientProjection_equivariant A S)
    (finiteCoinducedCoefficientAction_continuous A S hA hS)

end
end Dubon2026
