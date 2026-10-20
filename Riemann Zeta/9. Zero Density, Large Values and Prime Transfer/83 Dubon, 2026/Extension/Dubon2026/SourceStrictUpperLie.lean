import Dubon2026.SourceSpecialLinearMatrices

/-! The original strictly upper triangular trace-zero matrices.
Their exact matrix powers vanish, supplying the nilpotence premise needed
by Engel's theorem for the actual source coefficient representation.
-/

namespace Dubon2026
noncomputable section
open Matrix

variable {R : Type*} [CommRing R] {n : ℕ}

/-- Powers of an original strictly upper triangular matrix vanish below the corresponding shifted diagonal. -/
theorem sourceStrictUpper_pow_entry_zero (X : Matrix (Fin n) (Fin n) R)
    (hX : ∀ i j, j ≤ i → X i j = 0) (k : ℕ) (i j : Fin n)
    (hij : j.val < i.val + k) : (X ^ k) i j = 0 := by
  induction k generalizing i j with
  | zero =>
    have hne : i ≠ j := by intro h; subst j; omega
    simpa only [pow_zero] using Matrix.one_apply_ne hne
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro l _
    by_cases hl : l.val < i.val + k
    · rw [ih i l hl, zero_mul]
    · have hjl : j ≤ l := by
        change j.val ≤ l.val
        omega
      rw [hX l j hjl, mul_zero]

/-- Every original strictly upper triangular matrix is nilpotent, with its rank as an explicit bound. -/
theorem sourceStrictUpper_isNilpotent (X : Matrix (Fin n) (Fin n) R)
    (hX : ∀ i j, j ≤ i → X i j = 0) : IsNilpotent X := by
  refine ⟨n, Matrix.ext fun i j => ?_⟩
  exact sourceStrictUpper_pow_entry_zero X hX n i j (by omega)

/-- The product of two original strictly upper triangular matrices is strictly upper triangular. -/
theorem sourceStrictUpper_mul {X Y : Matrix (Fin n) (Fin n) R}
    (hX : ∀ i j, j ≤ i → X i j = 0) (hY : ∀ i j, j ≤ i → Y i j = 0)
    (i j : Fin n) (hij : j ≤ i) : (X * Y) i j = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : k ≤ i
  · rw [hX i k hk, zero_mul]
  · rw [hY k j (le_trans hij (le_of_lt (lt_of_not_ge hk))), mul_zero]

variable (R n)

/-- The original strictly upper triangular subalgebra of the original special-linear Lie algebra. -/
def sourceStrictUpperLie : LieSubalgebra R (LieAlgebra.SpecialLinear.sl (Fin n) R) where
  carrier := {X | ∀ i j, j ≤ i → X.val i j = 0}
  zero_mem' := by
    change ∀ i j : Fin n, j ≤ i → (0 : Matrix (Fin n) (Fin n) R) i j = 0
    intro i j _
    rfl
  add_mem' {X Y} hX hY := by
    intro i j hij
    change X.val i j + Y.val i j = 0
    rw [hX i j hij, hY i j hij, add_zero]
  smul_mem' c X hX := by
    intro i j hij
    change c • X.val i j = 0
    rw [hX i j hij, smul_zero]
  lie_mem' {X Y} hX hY := by
    intro i j hij
    change (X.val * Y.val - Y.val * X.val) i j = 0
    rw [Matrix.sub_apply, sourceStrictUpper_mul hX hY i j hij,
      sourceStrictUpper_mul hY hX i j hij, sub_self]

end
end Dubon2026
