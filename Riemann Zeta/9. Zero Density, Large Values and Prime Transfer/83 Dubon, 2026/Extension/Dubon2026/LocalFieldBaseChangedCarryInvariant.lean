import Dubon2026.LocalFieldOriginalCarryInvariant

/-! # Normalized carry pairing after changing the original base field

This applies the already proved literal carry base change and finite-stage
local pairing when the source base is the global field and the target base
is its actual completion. DUB-17's arithmetic local compositum supplies the
finite cyclic stage and all its genuine embedding towers.
-/
namespace Dubon2026
noncomputable section

variable (K E L Ω : Type) [Field K] [Field E] [Field L] [Field Ω]
  [Algebra K E] [Algebra K L] [Algebra E Ω] [Algebra K Ω] [Algebra L Ω]
  [IsScalarTower K E Ω] [IsScalarTower K L Ω]
  [FiniteDimensional K L] [IsGalois K L] [IsGalois E Ω] [IsSepClosed Ω]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)]
  (F : FiniteGaloisIntermediateField E Ω) [IsCyclic Gal(F/E)]
  [Algebra K F] [IsScalarTower K E F]
  [Algebra L F] [IsScalarTower K L F] [IsScalarTower L F Ω]

/-- Actual base change from the original global field has normalized local invariant given by its restricted character on original finite local reciprocity. -/
theorem localFieldBaseChangedCarryInvariant
    {n : ℕ} [NeZero n] (χ : Gal(L/K) →* Multiplicative (ZMod n)) (u : Kˣ) :
    localFieldContinuousH2InvariantEquiv E Ω
      (continuousGaloisUnitBaseChangeH2 K E L Ω
        (Submodule.Quotient.mk (galoisUnitCharacterCarryCocycle χ u))) =
      rationalCyclicInvariant n
        (χ (galoisBaseChangeRestriction K E L F
          (localFieldFiniteCyclicReciprocity E Ω F
            (Additive.ofMul (Units.map (algebraMap K E).toMonoidHom u))).toMul)).toAdd := by
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits E F) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits E F) := ⟨rfl⟩
  rw [← continuousGaloisUnitBaseChangeH2_comp K E E L F Ω]
  change localFieldContinuousH2InvariantEquiv E Ω
    (continuousGaloisUnitBaseChangeH2 E E F Ω
      (finiteGaloisUnitBaseChangeH2 K E L F
        (Submodule.Quotient.mk (galoisUnitCharacterCarryCocycle χ u)))) = _
  rw [finiteGaloisUnitBaseChangeH2_characterCarry,
    continuousGaloisUnitBaseChangeH2_eq_finiteStage]
  exact localFieldFiniteCyclicReciprocity_character E Ω F
    (χ.comp (galoisBaseChangeRestriction K E L F))
    (Units.map (algebraMap K E).toMonoidHom u)

end
end Dubon2026
