import Dubon2026.LocalFieldIntegerIntegralClosure
import Mathlib.RingTheory.Unramified.Basic

/-! # Original local integer rings under actual field equivalences -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

variable (K L M : Type) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M]
  [ValuativeRel K] [ValuativeRel L] [ValuativeRel M]
  [TopologicalSpace K] [TopologicalSpace L] [TopologicalSpace M]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [IsNonarchimedeanLocalField M]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation M)]

/-- The actual field equivalence induces an equivalence of the original
integer rings: both are the already proved actual integral closures. -/
def localFieldIntegerAlgEquiv (e : L ≃ₐ[K] M) : 𝒪[L] ≃ₐ[𝒪[K]] 𝒪[M] := by
  haveI : IsIntegralClosure 𝒪[L] 𝒪[K] L := localField_integer_isIntegralClosure
  haveI : IsIntegralClosure 𝒪[M] 𝒪[K] M := localField_integer_isIntegralClosure
  exact ((IsIntegralClosure.equiv 𝒪[K] 𝒪[L] L (integralClosure 𝒪[K] L)).trans
    (e.restrictScalars 𝒪[K]).mapIntegralClosure).trans
      (IsIntegralClosure.equiv 𝒪[K] (integralClosure 𝒪[K] M) M 𝒪[M])

/-- The induced integer equivalence preserves the literal original field
coefficient through the displayed field equivalence. -/
theorem localFieldIntegerAlgEquiv_coefficient (e : L ≃ₐ[K] M) (x : 𝒪[L]) :
    algebraMap 𝒪[M] M (localFieldIntegerAlgEquiv K L M e x) =
      e (algebraMap 𝒪[L] L x) := by
  haveI : IsIntegralClosure 𝒪[L] 𝒪[K] L := localField_integer_isIntegralClosure
  haveI : IsIntegralClosure 𝒪[M] 𝒪[K] M := localField_integer_isIntegralClosure
  simp [localFieldIntegerAlgEquiv, IsIntegralClosure.algebraMap_equiv,
    Subalgebra.algebraMap_eq]
  exact IsIntegralClosure.algebraMap_equiv 𝒪[K] 𝒪[L] L (integralClosure 𝒪[K] L) x

/-- Unramifiedness of the actual integer extension transfers along an
actual base-field equivalence, using the proved integer-ring equivalence. -/
theorem localFieldIntegerAlgEquiv_formallyUnramified
    (e : L ≃ₐ[K] M) [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]] :
    Algebra.FormallyUnramified 𝒪[K] 𝒪[M] :=
  Algebra.FormallyUnramified.of_equiv (localFieldIntegerAlgEquiv K L M e)

end
end Dubon2026
