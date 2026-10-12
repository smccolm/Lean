import Dubon2026.BaseChangedUnramifiedIntegralClosure
import Dubon2026.LocalFieldIntegerIntegralClosure

/-! # Original unramified local extensions remain unramified in actual composita -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

variable (K E L M : Type) [Field K] [Field E] [Field L] [Field M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M]
  [ValuativeRel K] [ValuativeRel E] [ValuativeRel L] [ValuativeRel M]
  [TopologicalSpace K] [TopologicalSpace E] [TopologicalSpace L] [TopologicalSpace M]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField E]
  [IsNonarchimedeanLocalField L] [IsNonarchimedeanLocalField M]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [(ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation M)]
  [(ValuativeRel.valuation L).HasExtension (ValuativeRel.valuation M)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]

include K in
omit [(ValuativeRel.valuation L).HasExtension (ValuativeRel.valuation M)] in
/-- If the actual images of E and L generate M, unramifiedness of the
original L/K integer extension implies unramifiedness of the original M/E
integer extension. The base extension E/K may be ramified. -/
theorem localField_integer_unramified_of_compositum
    (htop : (algebraMap E M).fieldRange ⊔ (algebraMap L M).fieldRange = ⊤) :
    Algebra.FormallyUnramified 𝒪[E] 𝒪[M] := by
  haveI : Module.Finite 𝒪[K] 𝒪[L] := localField_integer_module_finite
  haveI : IsIntegralClosure 𝒪[M] 𝒪[E] M := localField_integer_isIntegralClosure
  haveI : IsScalarTower 𝒪[K] 𝒪[L] M :=
    IsScalarTower.of_algebraMap_eq fun x => IsScalarTower.algebraMap_apply K L M x
  haveI : IsScalarTower 𝒪[K] 𝒪[E] M :=
    IsScalarTower.of_algebraMap_eq fun x => IsScalarTower.algebraMap_apply K E M x
  let f : 𝒪[L] →ₐ[𝒪[K]] M := IsScalarTower.toAlgHom 𝒪[K] 𝒪[L] M
  apply integralClosure_formallyUnramified_of_baseChange_compositum_top
    f (algebraMap E M) (algebraMap L M) _ _ htop 𝒪[M]
  · ext x
    exact (IsScalarTower.algebraMap_apply 𝒪[E] E M x).symm
  · ext x
    exact (IsScalarTower.algebraMap_apply 𝒪[L] L M x).symm

end
end Dubon2026
