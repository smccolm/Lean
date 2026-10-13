import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.NumberTheory.NumberField.Basic

/-! # The actual simple Kummer field witnessing failure of a global power

For a prime exponent, the pinned irreducibility theorem constructs the
actual splitting field when a base unit is not a global power. Pinned
Kummer theory gives its cyclic Galois structure, exact prime degree and
an actual generating unit root. These discharge the field and generator
premises of DUB-17's principal localization contradiction.
-/
namespace Dubon2026
noncomputable section
open Polynomial
variable (K : Type) [Field K]

/-- The literal polynomial splitting field used in the principal-power
localization contradiction. -/
abbrev OriginalSimpleKummerField (n : ℕ) (a : Kˣ) :=
  (Polynomial.X ^ n - Polynomial.C (a : K)).SplittingField

/-- Failure of an original prime power constructs an actual cyclic
prime-degree Kummer field with its actual generating unit root. -/
theorem originalPrimeKummerField_data
    (p : ℕ) (hp : p.Prime) (hroot : (primitiveRoots p K).Nonempty)
    (a : Kˣ) (ha : a ∉ (powMonoidHom p : Kˣ →* Kˣ).range) :
    let L := OriginalSimpleKummerField K p a
    FiniteDimensional K L ∧ IsGalois K L ∧ IsCyclic Gal(L/K) ∧
      Module.finrank K L = p ∧
      ∃ β : Lˣ, (β : L) ^ p = algebraMap K L (a : K) ∧
        IntermediateField.adjoin K {(β : L)} = ⊤ := by
  let L := OriginalSimpleKummerField K p a
  have hNoRoot (b : K) : b ^ p ≠ (a : K) := by
    intro hb
    have hb0 : b ≠ 0 := by
      intro he
      exact a.ne_zero (by rw [← hb, he, zero_pow hp.ne_zero])
    exact ha ⟨Units.mk0 b hb0, Units.ext hb⟩
  have hIrr : Irreducible (Polynomial.X ^ p - Polynomial.C (a : K)) :=
    X_pow_sub_C_irreducible_of_prime hp hNoRoot
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : FiniteDimensional K L :=
    Polynomial.IsSplittingField.finiteDimensional L (Polynomial.X ^ p - Polynomial.C (a : K))
  letI : IsGalois K L := isGalois_of_isSplittingField_X_pow_sub_C hroot hIrr L
  letI : IsCyclic Gal(L/K) := isCyclic_of_isSplittingField_X_pow_sub_C hroot hIrr L
  let b : L := rootOfSplitsXPowSubC hp.pos (a : K) L
  have hb : b ^ p = algebraMap K L (a : K) := rootOfSplitsXPowSubC_pow (a : K) L
  have hb0 : b ≠ 0 := by
    intro he
    have hZero : algebraMap K L (a : K) = 0 := by rw [← hb, he, zero_pow hp.ne_zero]
    exact a.ne_zero ((map_eq_zero (algebraMap K L)).mp hZero)
  refine ⟨inferInstance, inferInstance, inferInstance,
    finrank_of_isSplittingField_X_pow_sub_C hroot hIrr L, Units.mk0 b hb0, hb, ?_⟩
  exact IntermediateField.adjoin_root_eq_top_of_isSplittingField hroot hIrr hb

end
end Dubon2026
