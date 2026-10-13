import Dubon2026.LocalFieldFiniteCyclicReciprocity
import Dubon2026.ContinuousGaloisBaseChangeFiniteStage
import Dubon2026.GaloisUnitCarryBaseChange

/-! # The normalized local invariant of original finite-field carry classes

Inflation of the literal original carry cocycle factors through an actual
finite cyclic intermediate field of the same closure. The already proved
normalized local character pairing then evaluates it. This comparison is
needed after original completion localization on DUB-17's sum-zero route.
-/
namespace Dubon2026
noncomputable section

variable (K L Ω : Type) [Field K] [Field L] [Field Ω]
  [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
  [FiniteDimensional K L] [IsGalois K L] [IsGalois K Ω] [IsSepClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  (F : FiniteGaloisIntermediateField K Ω) [IsCyclic Gal(F/K)]
  [Algebra L F] [IsScalarTower K L F] [IsScalarTower L F Ω]

/-- The actual normalized invariant of an inflated original carry class is character evaluation on the original finite local reciprocity image. -/
theorem localFieldOriginalCarryInvariant
    {n : ℕ} [NeZero n] (χ : Gal(L/K) →* Multiplicative (ZMod n)) (u : Kˣ) :
    localFieldContinuousH2InvariantEquiv K Ω
      (continuousGaloisUnitBaseChangeH2 K K L Ω
        (Submodule.Quotient.mk (galoisUnitCharacterCarryCocycle χ u))) =
      rationalCyclicInvariant n
        (χ (galoisBaseChangeRestriction K K L F
          (localFieldFiniteCyclicReciprocity K Ω F (Additive.ofMul u)).toMul)).toAdd := by
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
  rw [← continuousGaloisUnitBaseChangeH2_comp K K K L F Ω]
  change localFieldContinuousH2InvariantEquiv K Ω
    (continuousGaloisUnitBaseChangeH2 K K F Ω
      (finiteGaloisUnitBaseChangeH2 K K L F
        (Submodule.Quotient.mk (galoisUnitCharacterCarryCocycle χ u)))) = _
  rw [finiteGaloisUnitBaseChangeH2_characterCarry,
    continuousGaloisUnitBaseChangeH2_eq_finiteStage]
  change localFieldFiniteStageInvariant K Ω F
    (localFieldFiniteCharacterCarryClass K Ω F
      (χ.comp (galoisBaseChangeRestriction K K L F))
      (Units.map (algebraMap K K).toMonoidHom u)) = _
  have hu : Units.map (algebraMap K K).toMonoidHom u = u := by
    apply Units.ext
    rfl
  rw [hu, localFieldFiniteCyclicReciprocity_character]
  rfl

end
end Dubon2026
