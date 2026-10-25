import Dubon2026.SourceIntegerCoefficientExtension
import Mathlib.Algebra.Polynomial.AlgebraMap

/-! DUB-17/18 -> primitive projector transport. The native extension
preserves the literal coefficient scalars and polynomial evaluation, so
the same arithmetic projector can be evaluated on each actual realization. -/
namespace Dubon2026
noncomputable section
open TensorProduct Polynomial
variable {F K A B : Type*} [Field F] [Field K] [Ring A] [Ring B] [Algebra K B]

theorem integerCoefficientExtension_algebraMap (ι : F →+* K) (φ : A →+* B) (a : F) :
    integerCoefficientExtension ι φ (algebraMap F (F ⊗[ℤ] A) a) = algebraMap K B (ι a) := by
  change integerCoefficientExtension ι φ (a ⊗ₜ[ℤ] (1 : A)) = _
  rw [integerCoefficientExtension_tmul, map_one, Algebra.algebraMap_eq_smul_one]

theorem integerCoefficientExtension_smul (ι : F →+* K) (φ : A →+* B)
    (a : F) (z : F ⊗[ℤ] A) :
    integerCoefficientExtension ι φ (a • z) = ι a • integerCoefficientExtension ι φ z := by
  calc
    _ = integerCoefficientExtension ι φ (algebraMap F (F ⊗[ℤ] A) a * z) :=
      congrArg (integerCoefficientExtension ι φ) (Algebra.smul_def a z)
    _ = algebraMap K B (ι a) * integerCoefficientExtension ι φ z := by
      rw [map_mul, integerCoefficientExtension_algebraMap]
    _ = _ := (Algebra.smul_def (ι a) (integerCoefficientExtension ι φ z)).symm

theorem integerCoefficientExtension_aeval (ι : F →+* K) (φ : A →+* B)
    (z : F ⊗[ℤ] A) (P : F[X]) :
    integerCoefficientExtension ι φ (aeval z P) =
      aeval (integerCoefficientExtension ι φ z) (P.map ι) := by
  have hc : (integerCoefficientExtension ι φ).comp (algebraMap F (F ⊗[ℤ] A)) =
      (algebraMap K B).comp ι := RingHom.ext (integerCoefficientExtension_algebraMap ι φ)
  simp only [aeval_def, hom_eval₂, eval₂_map, hc]

theorem integerCoefficientExtension_shifted_squares {I : Type*}
    (ι : F →+* K) (φ : A →+* B) (s : Finset I) (t : I → A) (a : I → F) :
    integerCoefficientExtension ι φ
      (∑ i ∈ s, ((1 : F) ⊗ₜ[ℤ] t i - a i • 1) ^ 2) =
        ∑ i ∈ s, (φ (t i) - ι (a i) • 1) ^ 2 := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_pow, map_sub, integerCoefficientExtension_tmul, map_one, one_smul,
    integerCoefficientExtension_smul, map_one]

theorem integerCoefficientExtension_mul_eq_zero (ι : F →+* K) (φ : A →+* B)
    (hi : Function.Injective (integerCoefficientExtension ι φ)) (x y : F ⊗[ℤ] A)
    (h : integerCoefficientExtension ι φ x * integerCoefficientExtension ι φ y = 0) :
    x * y = 0 := by
  apply hi
  simpa only [map_mul, map_zero] using h

theorem integerCoefficientExtension_idempotent (ι : F →+* K) (φ : A →+* B)
    (hi : Function.Injective (integerCoefficientExtension ι φ)) (x : F ⊗[ℤ] A)
    (h : IsIdempotentElem (integerCoefficientExtension ι φ x)) : IsIdempotentElem x := by
  apply hi
  simpa only [map_mul] using h

theorem integerCoefficientExtension_mul_eq_smul (ι : F →+* K) (φ : A →+* B)
    (hi : Function.Injective (integerCoefficientExtension ι φ)) (x y : F ⊗[ℤ] A) (a : F)
    (h : integerCoefficientExtension ι φ x * integerCoefficientExtension ι φ y =
      ι a • integerCoefficientExtension ι φ y) : x * y = a • y := by
  apply hi
  simpa only [map_mul, integerCoefficientExtension_smul] using h

end
end Dubon2026
