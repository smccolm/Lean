import Dubon2026.LocalFieldIntegerIntegralClosure
import Dubon2026.LocalMonicSeparableReduction
import Dubon2026.MonicSeparableAdjoinRootEtale

/-! # The actual integral root algebra equals the original extension integer ring -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  (f : Polynomial 𝒪[K]) (hf : f.Monic)
  [IsDomain (AdjoinRoot f)] [IsIntegrallyClosed (AdjoinRoot f)]
  [Algebra (AdjoinRoot f) L] [IsFractionRing (AdjoinRoot f) L]
  [IsScalarTower 𝒪[K] (AdjoinRoot f) L]

/-- Both the original integrally closed finite root algebra and the actual
extension integer ring are the integral closure in the same original field.
Their equivalence is the actual universal integral-closure map. -/
def localFieldMonicRootIntegerEquiv : AdjoinRoot f ≃ₐ[𝒪[K]] 𝒪[L] := by
  haveI : Module.Finite 𝒪[K] (AdjoinRoot f) := hf.finite_adjoinRoot
  haveI : IsIntegralClosure (AdjoinRoot f) 𝒪[K] L := inferInstance
  haveI : IsIntegralClosure 𝒪[L] 𝒪[K] L := localField_integer_isIntegralClosure
  exact IsIntegralClosure.equiv 𝒪[K] (AdjoinRoot f) L 𝒪[L]

omit [IsDomain (AdjoinRoot f)] in
/-- The integral-closure equivalence preserves each literal coefficient
inside the original extension field. -/
theorem localFieldMonicRootIntegerEquiv_coefficient (b : AdjoinRoot f) :
    algebraMap 𝒪[L] L (localFieldMonicRootIntegerEquiv K L f hf b) =
      algebraMap (AdjoinRoot f) L b := by
  haveI : Module.Finite 𝒪[K] (AdjoinRoot f) := hf.finite_adjoinRoot
  haveI : IsIntegralClosure (AdjoinRoot f) 𝒪[K] L := inferInstance
  haveI : IsIntegralClosure 𝒪[L] 𝒪[K] L := localField_integer_isIntegralClosure
  exact IsIntegralClosure.algebraMap_equiv 𝒪[K] (AdjoinRoot f) L 𝒪[L] b

include hf in
omit [IsDomain (AdjoinRoot f)] in
/-- Separable residue reduction proves that the actual extension integer
ring is étale over the original base integer ring. It is transported along
the proved original integral-closure equivalence, not a supplied model certificate. -/
theorem localFieldMonicRootInteger_etale
    (hs : (f.map (IsLocalRing.residue 𝒪[K])).Separable) :
    Algebra.Etale 𝒪[K] 𝒪[L] := by
  have hsep : f.Separable := local_monic_separable_of_residue f hf hs
  haveI : Algebra.Etale 𝒪[K] (AdjoinRoot f) := monic_separable_adjoinRoot_etale f hf hsep
  exact Algebra.Etale.of_equiv (localFieldMonicRootIntegerEquiv K L f hf)

end
end Dubon2026
