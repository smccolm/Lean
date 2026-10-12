import Dubon2026.GaloisRootContinuousCorestriction
import Dubon2026.LocalFieldContinuousInvariantCorestriction
import Dubon2026.ContinuousKummerH2Torsion

/-! # Actual local root H2 corestriction is injective

This is the target injection in cyclotomic descent of the prime-field Kummer
pairing. It follows from the proved actual unit corestriction and Kummer kernel.
-/

namespace Dubon2026
noncomputable section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (E : IntermediateField K Ω) [FiniteDimensional K E]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
  (n : ℕ) [NeZero n]
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [tUnits : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [dUnits : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Derive Galoisness above the actual intermediate field from the original Galois extension. -/
local instance rootLocalCorestrictionIsGalois : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
/-- Reuse the original root coefficient topology on the same roots over the finite base. -/
local instance rootLocalCorestrictionStageTopology : TopologicalSpace (galoisRootOfUnityRepresentation (K := E) (Ω := Ω) n) :=
  inferInstanceAs (TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n))
/-- The unchanged original root coefficient topology remains discrete. -/
local instance rootLocalCorestrictionStageDiscrete : DiscreteTopology (galoisRootOfUnityRepresentation (K := E) (Ω := Ω) n) :=
  inferInstanceAs (DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n))
/-- Reuse the original unit coefficient topology on the same units over the finite base. -/
local instance rootLocalCorestrictionUnitTopology : TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω) :=
  inferInstanceAs (TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω))
/-- The unchanged original unit coefficient topology remains discrete. -/
local instance rootLocalCorestrictionUnitDiscrete : DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω) :=
  inferInstanceAs (DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω))

include dUnits in
/-- The genuine local root H2 corestriction is injective: the original Kummer
inclusion square reduces its kernel to the already proved actual unit kernel. -/
theorem localFieldRootContinuousCorestriction_injective :
    Function.Injective (galoisRootContinuousCorestriction K Ω E n) := by
  intro x y h
  apply galoisKummerH2Inclusion_injective (K := E) (Ω := Ω) n (NeZero.pos n)
  apply (localFieldContinuousH2_corestriction_bijective K Ω E).injective
  exact (galoisRootContinuousCorestriction_inclusion K Ω E n x).symm.trans
    ((congrArg (galoisKummerH2Inclusion (K := K) (Ω := Ω) n) h).trans
      (galoisRootContinuousCorestriction_inclusion K Ω E n y))

end
end Dubon2026
