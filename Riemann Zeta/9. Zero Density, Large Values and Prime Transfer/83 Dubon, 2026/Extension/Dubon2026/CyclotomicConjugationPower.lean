import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification

/-! # The cyclotomic exponent of actual complex conjugation

The two-primary splitting field is the fixed field of a character whose
kernel excludes minus one. This lemma identifies minus one with the
actual conjugation supplied by pinned infinite-place theory, rather than
introducing a second conjugation construction. It serves DUB-17's
full-order arithmetic class through the totally complex cyclic stage.
-/
namespace Dubon2026
noncomputable section
open NumberField

/-- Any actual conjugation under a complex embedding has cyclotomic
power character minus one. -/
theorem originalCyclotomicConjugation_power
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {m : ℕ} [NeZero m] {ζ : L} (hζ : IsPrimitiveRoot ζ m)
    (φ : L →+* ℂ) (c : Gal(L/K)) (hc : ComplexEmbedding.IsConj φ c) :
    hζ.autToPow K c = -1 := by
  have hinv : ζ ^ (m - 1) = ζ⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, Nat.sub_add_cancel (NeZero.pos m), hζ.pow_eq_one]
  have hpow : ζ ^ (hζ.autToPow K c : ZMod m).val = ζ ^ (m - 1) := by
    rw [hζ.autToPow_spec K c]
    apply φ.injective
    rw [hc.eq, hinv, map_inv₀, Complex.star_def]
    have hz : (φ ζ) ^ m = 1 := by
      rw [← map_pow, hζ.pow_eq_one, map_one]
    exact (Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one hz (NeZero.ne m))).symm
  have hv := hζ.pow_inj (ZMod.val_lt _) (Nat.sub_lt (NeZero.pos m) zero_lt_one) hpow
  apply Units.ext
  rw [← ZMod.natCast_zmod_val (hζ.autToPow K c : ZMod m), hv]
  change ((m - 1 : ℕ) : ZMod m) = (-1 : ZMod m)
  rw [Nat.cast_sub (NeZero.pos m), ZMod.natCast_self, Nat.cast_one, zero_sub]

end
end Dubon2026
