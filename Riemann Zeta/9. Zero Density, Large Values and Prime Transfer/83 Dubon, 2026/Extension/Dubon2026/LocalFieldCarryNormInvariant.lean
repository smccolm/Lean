import Dubon2026.GaloisCarryNormCorestriction
import Dubon2026.LocalFieldContinuousInvariantCorestriction

/-! # The original normalized carry invariant commutes with field norms

The proved genuine norm/corestriction identity combines with the existing
normalized local invariant theorem. This discharges the invariant comparison
needed for actual local reciprocity norm compatibility and DUB-17's ramified
cyclotomic formula.
-/
namespace Dubon2026
noncomputable section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  (E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois E Ω]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)]

/-- The actual normalized invariant of the original norm carry equals the invariant of the original restricted-character carry. -/
theorem localFieldContinuousCarryInvariant_norm
    {n : ℕ} [NeZero n] (χ : Gal(Ω/K) →ₜ* Multiplicative (ZMod n)) (u : Eˣ) :
    localFieldContinuousH2InvariantEquiv K Ω
      (Submodule.Quotient.mk (continuousGaloisCharacterCarryCocycle n χ
        (Units.map (Algebra.norm K (S := E)) u))) =
      localFieldContinuousH2InvariantEquiv E Ω
        (Submodule.Quotient.mk (continuousGaloisCharacterCarryCocycle n
          (galoisFiniteBaseCharacterRestriction K Ω E χ) u)) := by
  rw [← continuousGaloisCharacterCarryCocycle_corestriction_norm K Ω E χ u]
  exact localFieldContinuousH2InvariantEquiv_corestriction K Ω E _

end
end Dubon2026
