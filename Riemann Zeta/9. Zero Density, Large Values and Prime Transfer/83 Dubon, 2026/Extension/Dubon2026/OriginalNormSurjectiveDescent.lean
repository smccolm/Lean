import Dubon2026.OriginalIdeleClassNativeNormQuotient

/-! # Actual global power descent from the cyclic norm lower bound

Surjectivity of the original class norm gives quotient order one. The
already proved original cyclic norm-index lower bound forces extension
degree one, so every actual upper-field root descends to the base field.
The selected local corrections will supply norm surjectivity for a simple
Kummer extension once its local splitting and unramifiedness are proved.
This is the final descent step of DUB-17's principal S-union-T localization
argument; it uses no global norm-index upper bound or reciprocity.
-/
namespace Dubon2026
noncomputable section
open NumberField CategoryTheory
open scoped NumberField
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]

/-- The proved actual cyclic lower bound forces degree one when the
original class norm is surjective. -/
theorem originalCyclicNormSurjective_finrank_one
    (hSurj : Function.Surjective (originalIdeleClassNorm K L)) :
    Module.finrank K L = 1 := by
  have hr : (originalIdeleClassNormLinear K L).range = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    intro c
    obtain ⟨b, hb⟩ := hSurj c.toMul
    exact ⟨Additive.ofMul b, congrArg Additive.ofMul hb⟩
  have hCard : Nat.card (OriginalIdeleClassNormQuotient K L) = 1 := by
    change Nat.card (Additive (OriginalNumberFieldIdeleClassGroup K) ⧸
      (originalIdeleClassNormLinear K L).range) = 1
    rw [hr]
    exact Nat.card_unique
  exact Nat.le_antisymm (hCard ▸ (originalIdeleClassNormQuotient_degree_lower K L).2)
    Module.finrank_pos

/-- Every actual Kummer root descends to an original base-field unit after
the selected correction argument proves original cyclic class norm surjectivity. -/
theorem originalCyclicNormSurjective_power_descent
    (hSurj : Function.Surjective (originalIdeleClassNorm K L))
    (n : ℕ) (a : Kˣ) (β : Lˣ)
    (hβ : (β : L) ^ n = algebraMap K L (a : K)) :
    a ∈ (powMonoidHom n : Kˣ →* Kˣ).range := by
  have hBij : Function.Bijective (algebraMap K L) :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.mp
      (originalCyclicNormSurjective_finrank_one K L hSurj)
  obtain ⟨b, hb⟩ := hBij.2 (β : L)
  have hb0 : b ≠ 0 := by
    intro h
    exact β.ne_zero (by rw [← hb, h, map_zero])
  refine ⟨Units.mk0 b hb0, ?_⟩
  apply Units.ext
  apply hBij.1
  change algebraMap K L (b ^ n) = algebraMap K L (a : K)
  rw [map_pow, hb]
  exact hβ

end
end Dubon2026
