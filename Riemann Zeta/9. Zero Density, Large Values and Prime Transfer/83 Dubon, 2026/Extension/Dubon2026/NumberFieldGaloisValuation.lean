/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the upstream LICENSE.
Adapted from NYLL ClassFieldTheory, commit dc55774a7fe03e742f2b4c6114aab5e7d01edfb1,
Nyll/ClassFieldTheory/AlgebraicNumberTheory/SUnit/GaloisAction.lean.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Dubon2026.NumberFieldGaloisPlaces
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Multiplicity

/-! # Simultaneous Galois transport preserves the original finite valuation

Original prime multiplicities are transported by the actual automorphism
of the original integer ring. Passing to fractions proves the valuation
identity needed for the original S-unit action and completed local maps,
which make DUB-17's supported-idele sequence equivariant.
-/

namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField nonZeroDivisors
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]

/-- The original Galois automorphism transports multiplication of original integral ideals. -/
def numberFieldGaloisIdealEquiv (σ : Gal(L/K)) : Ideal (𝓞 L) ≃* Ideal (𝓞 L) where
  toFun I := I.map (NumberField.RingOfIntegers.mapAlgEquiv σ).toRingEquiv
  invFun I := I.map (NumberField.RingOfIntegers.mapAlgEquiv σ).toRingEquiv.symm
  left_inv _ := Ideal.map_of_equiv _
  right_inv _ := Ideal.map_of_equiv _
  map_mul' I J := Ideal.map_mul _ I J

/-- The original integral valuation is unchanged when both the original prime and integer are transported. -/
theorem numberFieldGaloisPlace_intValuation (σ : Gal(L/K))
    (v : HeightOneSpectrum (𝓞 L)) (r : 𝓞 L) :
    (numberFieldGaloisPlaceEquiv K L σ v).intValuation
      (NumberField.RingOfIntegers.mapAlgEquiv σ r) = v.intValuation r := by
  let e := (NumberField.RingOfIntegers.mapAlgEquiv σ).toRingEquiv
  by_cases hr : r = 0
  · subst r
    simp
  change (numberFieldGaloisPlaceEquiv K L σ v).intValuation (e r) = v.intValuation r
  have her : e r ≠ 0 := by simpa using e.injective.ne hr
  rw [HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ her,
    HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ hr]
  congr 2
  have hspan : Ideal.span ({e r} : Set (𝓞 L)) =
      numberFieldGaloisIdealEquiv K L σ (Ideal.span ({r} : Set (𝓞 L))) := by
    simp [numberFieldGaloisIdealEquiv, e, Ideal.map_span]
  rw [numberFieldGaloisPlaceEquiv_asIdeal, hspan]
  norm_cast
  exact multiplicity_map_eq (numberFieldGaloisIdealEquiv K L σ)
    (a := v.asIdeal) (b := Ideal.span ({r} : Set (𝓞 L)))

/-- The original field valuation is unchanged under the same original Galois transport. -/
theorem numberFieldGaloisPlace_valuation (σ : Gal(L/K))
    (v : HeightOneSpectrum (𝓞 L)) (x : L) :
    (numberFieldGaloisPlaceEquiv K L σ v).valuation L (σ x) = v.valuation L x := by
  obtain ⟨r, d, hrd⟩ := IsLocalization.exists_mk'_eq (𝓞 L)⁰ x
  rw [← hrd, IsFractionRing.mk'_eq_div, map_div₀, map_div₀, map_div₀]
  have hr : σ (algebraMap (𝓞 L) L r) = algebraMap (𝓞 L) L
      (NumberField.RingOfIntegers.mapAlgEquiv σ r) := rfl
  have hd : σ (algebraMap (𝓞 L) L (d : 𝓞 L)) = algebraMap (𝓞 L) L
      (NumberField.RingOfIntegers.mapAlgEquiv σ (d : 𝓞 L)) := rfl
  rw [hr, hd]
  simp only [HeightOneSpectrum.valuation_of_algebraMap]
  rw [numberFieldGaloisPlace_intValuation, numberFieldGaloisPlace_intValuation]

end
end Dubon2026
