/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the archived LICENSE.
Authors: The Tau Ceti contributors

Modified for Project 83 from TauCeti 8fdd17266a8b40ae0c490f85cdd9a01966a54b2b,
Algebra/Lie/Derivation/LocallyNilpotent.lean. The product argument is adapted
to pinned Mathlib's native commutative-algebra derivations. Only the
polynomial-generator consumer needed for the original source module is retained.
-/
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Nilpotent.Lemmas

/-! Local nilpotence on original coordinate polynomials.
This is the multiplication step needed to apply Engel's theorem to the
original source induced coefficient module, without a weight-space framework.
-/

namespace Dubon2026
noncomputable section
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- Powers killing two original factors give a power killing their product. -/
theorem sourceDerivation_pow_mul_zero (D : Derivation R A A) {x y : A} {n m : ℕ}
    (hx : (D.toLinearMap ^ n) x = 0) (hy : (D.toLinearMap ^ m) y = 0) :
    (D.toLinearMap ^ (n + m)) (x * y) = 0 := by
  induction n generalizing x y m with
  | zero =>
    simp only [pow_zero, Module.End.one_apply] at hx
    simp [hx]
  | succ n ih =>
    induction m generalizing y with
    | zero =>
      simp only [pow_zero, Module.End.one_apply] at hy
      simp [hy]
    | succ m ihm =>
      have hx' : (D.toLinearMap ^ n) (D.toLinearMap x) = 0 := by
        simpa only [pow_succ, Module.End.mul_apply] using hx
      have hy' : (D.toLinearMap ^ m) (D.toLinearMap y) = 0 := by
        simpa only [pow_succ, Module.End.mul_apply] using hy
      have hprod : D.toLinearMap (x * y) = D.toLinearMap x * y + x * D.toLinearMap y := by
        change D (x * y) = D x * y + x * D y
        rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
        ring
      rw [Nat.succ_add, pow_succ, Module.End.mul_apply, hprod, map_add]
      rw [ih hx' hy, Nat.add_succ, ← Nat.succ_add, ihm hy', add_zero]

/-- Local nilpotence on actual polynomial coordinates extends to every polynomial evaluated at those coordinates. -/
theorem sourceDerivation_polynomial_locallyNilpotent {σ : Type*}
    (D : Derivation R A A) (f : MvPolynomial σ R →ₐ[R] A)
    (hX : ∀ i, ∃ k : ℕ, (D.toLinearMap ^ k) (f (MvPolynomial.X i)) = 0)
    (p : MvPolynomial σ R) :
    ∃ k : ℕ, (D.toLinearMap ^ k) (f p) = 0 := by
  induction p using MvPolynomial.induction_on with
  | C r =>
    refine ⟨1, ?_⟩
    change D (f (algebraMap R (MvPolynomial σ R) r)) = 0
    rw [AlgHom.commutes, D.map_algebraMap]
  | add p q hp hq =>
    obtain ⟨k, hk⟩ := hp
    obtain ⟨l, hl⟩ := hq
    refine ⟨max k l, ?_⟩
    rw [map_add, map_add,
      Module.End.pow_map_zero_of_le (le_max_left _ _) hk,
      Module.End.pow_map_zero_of_le (le_max_right _ _) hl, add_zero]
  | mul_X p i hp =>
    obtain ⟨k, hk⟩ := hp
    obtain ⟨l, hl⟩ := hX i
    refine ⟨k + l, ?_⟩
    rw [map_mul]
    exact sourceDerivation_pow_mul_zero D hk hl

end
end Dubon2026
