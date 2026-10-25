import Dubon2026.SourceIntegerCoefficientExtensionLaws
import Dubon2026.SourceIntegerCoefficientExtensionOne

/-! DUB-17/18 -> primitive projector on the actual Tate module. These
endomorphism-specialized identities retain the literal tensor evaluation
while resolving its module instances before geometric specialization. -/
namespace Dubon2026
noncomputable section
open Polynomial TensorProduct
variable {F K A V : Type*} [Field F] [Field K] [Ring A]
variable [AddCommGroup V] [Module K V]

/-- Integer coefficient extension into an actual module endomorphism ring. -/
def integerCoefficientEndExtension (ι : F →+* K) (φ : A →+* Module.End K V) :
    F ⊗[ℤ] A →+* Module.End K V := integerCoefficientExtension ι φ

theorem integerCoefficientEndExtension_one_tmul
    (ι : F →+* K) (φ : A →+* Module.End K V) (a : A) :
    integerCoefficientEndExtension ι φ ((1 : F) ⊗ₜ[ℤ] a) = φ a :=
  integerCoefficientExtension_one_tmul ι φ a

theorem integerCoefficientEndExtension_shifted_squares {I : Type*}
    (ι : F →+* K) (φ : A →+* Module.End K V) (s : Finset I) (t : I → A) (a : I → F) :
    integerCoefficientEndExtension ι φ
      (∑ i ∈ s, ((1 : F) ⊗ₜ[ℤ] t i - a i • 1) ^ 2) =
        ∑ i ∈ s, (φ (t i) - ι (a i) • 1) ^ 2 :=
  integerCoefficientExtension_shifted_squares ι φ s t a

theorem integerCoefficientEndExtension_aeval
    (ι : F →+* K) (φ : A →+* Module.End K V) (z : F ⊗[ℤ] A) (P : F[X]) :
    integerCoefficientEndExtension ι φ (aeval z P) =
      aeval (integerCoefficientEndExtension ι φ z) (P.map ι) :=
  integerCoefficientExtension_aeval ι φ z P

end
end Dubon2026
