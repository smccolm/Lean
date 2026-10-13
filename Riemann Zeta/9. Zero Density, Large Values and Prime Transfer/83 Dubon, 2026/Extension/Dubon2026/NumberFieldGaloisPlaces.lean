/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the upstream LICENSE.
Adapted from NYLL ClassFieldTheory, commit dc55774a7fe03e742f2b4c6114aab5e7d01edfb1,
Nyll/ClassFieldTheory/AlgebraicNumberTheory/SUnit/GaloisAction.lean.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-! # The original Galois permutation of original finite places

Restriction of original automorphisms to the original integers gives the
actual place permutation. Its group laws are proved on those same ideals.
This supplies stable finite support and the original S-unit action required
for the supported-idele cohomology in DUB-17's global norm-index argument.
-/

namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField
variable (K L : Type) [Field K] [Field L] [Algebra K L]

/-- The actual permutation of original finite primes under an original Galois automorphism. -/
def numberFieldGaloisPlaceEquiv (σ : Gal(L/K)) :
    HeightOneSpectrum (𝓞 L) ≃ HeightOneSpectrum (𝓞 L) :=
  HeightOneSpectrum.equivOfRingEquiv (NumberField.RingOfIntegers.mapAlgEquiv σ).toRingEquiv

/-- The original transported prime is the original ideal mapped by the original integer automorphism. -/
theorem numberFieldGaloisPlaceEquiv_asIdeal (σ : Gal(L/K)) (v : HeightOneSpectrum (𝓞 L)) :
    (numberFieldGaloisPlaceEquiv K L σ v).asIdeal =
      v.asIdeal.map (NumberField.RingOfIntegers.mapAlgEquiv σ).toRingEquiv := by
  ext x
  exact Ideal.symm_apply_mem_of_equiv_iff

/-- Identity automorphisms fix each original finite prime. -/
theorem numberFieldGaloisPlaceEquiv_one (v : HeightOneSpectrum (𝓞 L)) :
    numberFieldGaloisPlaceEquiv K L 1 v = v := by
  apply HeightOneSpectrum.ext
  ext x
  change NumberField.RingOfIntegers.mapRingHom (1 : Gal(L/K)).symm.toRingHom x ∈ v.asIdeal ↔
    x ∈ v.asIdeal
  have hx : NumberField.RingOfIntegers.mapRingHom (1 : Gal(L/K)).symm.toRingHom x = x := by
    apply NumberField.RingOfIntegers.ext
    rfl
  rw [hx]

/-- Multiplication of original automorphisms composes their original prime permutations. -/
theorem numberFieldGaloisPlaceEquiv_mul (σ τ : Gal(L/K)) (v : HeightOneSpectrum (𝓞 L)) :
    numberFieldGaloisPlaceEquiv K L (σ * τ) v =
      numberFieldGaloisPlaceEquiv K L σ (numberFieldGaloisPlaceEquiv K L τ v) := by
  apply HeightOneSpectrum.ext
  ext x
  change NumberField.RingOfIntegers.mapRingHom (σ * τ).symm.toRingHom x ∈ v.asIdeal ↔
    NumberField.RingOfIntegers.mapRingHom τ.symm.toRingHom
      (NumberField.RingOfIntegers.mapRingHom σ.symm.toRingHom x) ∈ v.asIdeal
  have hx : NumberField.RingOfIntegers.mapRingHom (σ * τ).symm.toRingHom x =
      NumberField.RingOfIntegers.mapRingHom τ.symm.toRingHom
        (NumberField.RingOfIntegers.mapRingHom σ.symm.toRingHom x) := by
    apply NumberField.RingOfIntegers.ext
    rfl
  rw [hx]

/-- The original Galois action on original finite places, using the proved group laws. -/
@[reducible]
def numberFieldGaloisPlaceAction : MulAction Gal(L/K) (HeightOneSpectrum (𝓞 L)) where
  smul σ v := numberFieldGaloisPlaceEquiv K L σ v
  one_smul := numberFieldGaloisPlaceEquiv_one K L
  mul_smul := numberFieldGaloisPlaceEquiv_mul K L

end
end Dubon2026
