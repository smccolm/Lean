import Dubon2026.FiniteGaloisH2DescentUnderBaseChange
import Dubon2026.LocalFieldInvariantBaseChange
import Dubon2026.LocalFieldUnramifiedCompositum

/-! # Actual unramified local H2 descent is detected by the original arithmetic period -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

variable (K E L M : Type) [Field K] [Field E] [Field L] [Field M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M]
  [IsGalois K E] [IsGalois K L] [IsGalois K M]
  [ValuativeRel K] [ValuativeRel E] [ValuativeRel L] [ValuativeRel M]
  [TopologicalSpace K] [TopologicalSpace E] [TopologicalSpace L] [TopologicalSpace M]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField E]
  [IsNonarchimedeanLocalField L] [IsNonarchimedeanLocalField M]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation M)]
  [(ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation M)]
  [(ValuativeRel.valuation L).HasExtension (ValuativeRel.valuation M)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K E)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K E)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K M)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K M)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E M)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E M)]

/-- An original unramified L/K class descends from the original E/K
class in the actual compositum exactly when the E/K degree kills its
original arithmetic-Frobenius period. Unramifiedness of the compositum
over E is constructed from the actual tensor-image integral closure. -/
theorem localFieldH2_unramified_descends_iff
    (htop : (algebraMap E M).fieldRange ⊔ (algebraMap L M).fieldRange = ⊤)
    (y : GaloisUnitContinuousH2 (K := K) (Ω := L)) :
    letI : FiniteDimensional K M := localField_field_module_finite
    (∃ x : GaloisUnitContinuousH2 (K := K) (Ω := E),
      finiteGaloisUnitTowerH2Inflation K E M x = finiteGaloisUnitTowerH2Inflation K L M y) ↔
        Module.finrank K E • localFieldPeriodRationalInvariant K L y = 0 := by
  haveI : FiniteDimensional K E := localField_field_module_finite
  haveI : FiniteDimensional K L := localField_field_module_finite
  haveI : FiniteDimensional K M := localField_field_module_finite
  haveI : FiniteDimensional E M := localField_field_module_finite
  haveI : IsGalois E M := IsGalois.tower_top_of_isGalois K E M
  haveI : Algebra.FormallyUnramified 𝒪[E] 𝒪[M] :=
    localField_integer_unramified_of_compositum K E L M htop
  exact (finiteGaloisH2_exists_inflation_eq_iff_baseChange_zero K E L M y).trans
    (finiteGaloisUnitBaseChangeH2_eq_zero_iff K E L M y)

end
end Dubon2026
