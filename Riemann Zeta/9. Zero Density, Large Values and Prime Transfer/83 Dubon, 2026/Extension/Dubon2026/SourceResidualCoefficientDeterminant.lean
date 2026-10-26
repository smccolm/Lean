import Dubon2026.SourceArithmeticWeightTwist
import Mathlib.LinearAlgebra.Matrix.Trace

/-! DUB-17/18 -> arithmetic automorphy -> finite residual coefficients.
Exact coefficient inclusions preserve the original cyclotomic character
and reflect its fixed-determinant equation for the same matrices. -/
namespace Dubon2026
noncomputable section
open scoped NumberField
open Matrix

theorem sourceArithmeticCyclotomicUnitCharacter_coefficient_map
    {K L : Type} [Field K] [Field L] [TopologicalSpace K] [TopologicalSpace L]
    (p : ℕ) [NeZero p] [CharP K p] [CharP L p]
    (a : 𝓞 ℚ) (hpa : (p : 𝓞 ℚ) ∣ a)
    (φ : K →+* L) (g : rationalArithmeticGaloisGroup a) :
    φ (sourceArithmeticCyclotomicUnitCharacter (F := K) p a hpa g : K) =
      (sourceArithmeticCyclotomicUnitCharacter (F := L) p a hpa g : L) := by
  have he : φ.comp (ZMod.castHom (dvd_refl p) K) = ZMod.castHom (dvd_refl p) L := Subsingleton.elim _ _
  exact DFunLike.congr_fun he (rationalArithmeticCyclotomicCharacter a p hpa g : ZMod p)

theorem sourceArithmetic_cyclotomic_determinant_coefficient_descent
    {K L : Type} [Field K] [Field L] [TopologicalSpace K] [TopologicalSpace L]
    (p : ℕ) [NeZero p] [CharP K p] [CharP L p]
    (a : 𝓞 ℚ) (hpa : (p : 𝓞 ℚ) ∣ a) (j : ℕ)
    (φ : K →+* L)
    (η : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin 2) K)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin 2) L)
    (hmap : (GeneralLinearGroup.map φ).comp η = ρ)
    (hdet : GeneralLinearGroup.det.comp ρ =
      (sourceArithmeticCyclotomicUnitCharacter (F := L) p a hpa).toMonoidHom ^ j) :
    GeneralLinearGroup.det.comp η =
      (sourceArithmeticCyclotomicUnitCharacter (F := K) p a hpa).toMonoidHom ^ j := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  apply φ.injective
  have he : φ (η g).val.det = (ρ g).val.det := by
    rw [RingHom.map_det]
    exact congrArg Matrix.det (congrArg Units.val (DFunLike.congr_fun hmap g))
  have hd := congrArg (fun χ => (χ g : L)) hdet
  change φ (η g).val.det =
    φ (((sourceArithmeticCyclotomicUnitCharacter (F := K) p a hpa).toMonoidHom ^ j) g : K)
  rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val]
  change φ (η g).val.det =
    φ ((sourceArithmeticCyclotomicUnitCharacter (F := K) p a hpa g : K) ^ j)
  rw [map_pow, sourceArithmeticCyclotomicUnitCharacter_coefficient_map, he]
  exact hd

end
end Dubon2026
