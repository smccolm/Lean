import Dubon2026.LocalFieldActualFiniteInvariantRestriction

/-! # The normalized invariant of an actual finite base-change class

Apply the proved degree formula after actual inflation into a common
closure. The literal composition identities discharge both inflation
comparisons. This is the finite-completion input for DUB-17's auxiliary
class total under field base change.
-/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel

/-- After inflation to the same closure, the actual finite base-change class has the degree-scaled normalized invariant. -/
theorem localFieldFiniteBaseChange_normalized_invariant
    (K E L M Ω : Type) [Field K] [Field E] [Field L] [Field M] [Field Ω]
    [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
    [Algebra K Ω] [Algebra E Ω] [Algebra L Ω] [Algebra M Ω]
    [IsScalarTower K E M] [IsScalarTower K L M]
    [IsScalarTower K E Ω] [IsScalarTower K L Ω] [IsScalarTower K M Ω]
    [IsScalarTower E M Ω] [IsScalarTower L M Ω]
    [FiniteDimensional K E] [IsGalois K L] [IsGalois E M]
    [IsGalois K Ω] [IsSepClosed Ω]
    [ValuativeRel K] [ValuativeRel E] [TopologicalSpace K] [TopologicalSpace E]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField E]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits E M)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits E M)]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)]
    (x : GaloisUnitContinuousH2 (K := K) (Ω := L)) :
    letI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
    localFieldContinuousH2InvariantEquiv E Ω
      (continuousGaloisUnitBaseChangeH2 E E M Ω
        (continuousGaloisUnitBaseChangeH2 K E L M x)) =
      Module.finrank K E • localFieldContinuousH2InvariantEquiv K Ω
        (continuousGaloisUnitBaseChangeH2 K K L Ω x) := by
  letI : IsGalois E Ω := IsGalois.tower_top_of_isGalois K E Ω
  have hc := continuousGaloisUnitBaseChangeH2_comp K E E L M Ω x
  have hd := continuousGaloisUnitBaseChangeH2_comp K K E L Ω Ω x
  have h := localFieldContinuousInvariant_actual_finite_restriction K E Ω
    (continuousGaloisUnitBaseChangeH2 K K L Ω x)
  exact (congrArg (localFieldContinuousH2InvariantEquiv E Ω) hc).trans
    ((congrArg (localFieldContinuousH2InvariantEquiv E Ω) hd).symm.trans h)

end
end Dubon2026
