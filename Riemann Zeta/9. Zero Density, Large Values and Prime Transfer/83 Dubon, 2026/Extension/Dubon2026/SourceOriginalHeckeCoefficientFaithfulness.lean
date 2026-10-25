import Dubon2026.SourceIntegerCoefficientExtensionInjective
import Dubon2026.SourceIntegralHeckeBasisCoordinates

/-! DUB-17/18 -> primitive projector transport. The existing integral
Hecke basis and its proved complex independence discharge faithfulness
of the actual coefficient-field realization on original cusp forms. -/
namespace Dubon2026
noncomputable section
variable (N : ℕ) [NeZero N]

theorem originalHecke_coefficient_extension_injective {F : Type*} [Field F] (ι : F →+* ℂ) :
    Function.Injective (integerCoefficientExtension ι
      (sourceOriginalIntegralHeckeAlgebra N 2).val.toRingHom) :=
  integerCoefficientExtension_injective ι (sourceOriginalIntegralHeckeAlgebra N 2).val.toRingHom
    (sourceIntegralHeckeBasis N)
    (sourceOriginalIntegralHecke_linearIndependent_complex N _
      (sourceIntegralHeckeBasis N).linearIndependent)

end
end Dubon2026
