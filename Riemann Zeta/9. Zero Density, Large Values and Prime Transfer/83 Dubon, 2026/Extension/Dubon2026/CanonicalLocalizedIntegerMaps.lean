import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Localization.AsSubring

/-! # Canonical localized integer rings inside the original number fields -/

namespace Dubon2026

noncomputable section
open scoped NumberField nonZeroDivisors

/-- The original integer ring localized at the powers of a nonzero original integer, as literal fractions in its original field. -/
abbrev originalLocalizedIntegers (K : Type*) [Field K] [NumberField K]
    (a : 𝓞 K) (ha : a ≠ 0) : Subalgebra (𝓞 K) K :=
  Localization.subalgebra.ofField K (.powers a)
    (powers_le_nonZeroDivisors_of_noZeroDivisors ha)

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]

omit [NumberField K] [NumberField L] in
/-- A nonzero original integer stays nonzero in the actual extension integer ring. -/
theorem originalIntegerMap_ne_zero (a : 𝓞 K) (ha : a ≠ 0) :
    algebraMap (𝓞 K) (𝓞 L) a ≠ 0 := by
  intro h
  apply ha
  apply NumberField.RingOfIntegers.algebraMap.injective K L
  simpa only [map_zero] using h

/-- The original field embedding carries every original localized integer to the actual localized extension integer ring. -/
theorem originalLocalizedIntegers_map_mem (a : 𝓞 K) (ha : a ≠ 0)
    (x : originalLocalizedIntegers K a ha) :
    algebraMap K L x.val ∈ originalLocalizedIntegers L
      (algebraMap (𝓞 K) (𝓞 L) a) (originalIntegerMap_ne_zero (L := L) a ha) := by
  obtain ⟨r, s, hs, hx⟩ := x.property
  obtain ⟨n, rfl⟩ := hs
  refine ⟨algebraMap (𝓞 K) (𝓞 L) r,
    (algebraMap (𝓞 K) (𝓞 L) a) ^ n, ⟨n, rfl⟩, ?_⟩
  rw [hx]
  simp only [map_mul, map_inv₀, map_pow, ← IsScalarTower.algebraMap_apply]

/-- The canonical coefficient map between the actual localized integer rings is the restriction of the original field embedding. -/
def originalLocalizedIntegersMap (a : 𝓞 K) (ha : a ≠ 0) :
    originalLocalizedIntegers K a ha →ₐ[𝓞 K]
      originalLocalizedIntegers L (algebraMap (𝓞 K) (𝓞 L) a)
        (originalIntegerMap_ne_zero (L := L) a ha) where
  toRingHom := ((algebraMap K L).comp
    (originalLocalizedIntegers K a ha).val.toRingHom).codRestrict _
      (originalLocalizedIntegers_map_mem a ha)
  commutes' r := by
    apply Subtype.ext
    exact (IsScalarTower.algebraMap_apply (𝓞 K) K L r).symm

/-- The canonical localized coefficient map retains the exact original ambient-field value. -/
theorem originalLocalizedIntegersMap_coe (a : 𝓞 K) (ha : a ≠ 0)
    (x : originalLocalizedIntegers K a ha) :
    (originalLocalizedIntegersMap (L := L) a ha x : L) = algebraMap K L x.val := rfl

/-- The original localized integer coefficient map is injective. -/
theorem originalLocalizedIntegersMap_injective (a : 𝓞 K) (ha : a ≠ 0) :
    Function.Injective (originalLocalizedIntegersMap (L := L) a ha) := by
  intro x y h
  apply Subtype.ext
  apply (algebraMap K L).injective
  exact congrArg Subtype.val h

end
end Dubon2026
