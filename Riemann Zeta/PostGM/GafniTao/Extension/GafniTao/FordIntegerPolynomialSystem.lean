import GafniTao.FordFiniteDifference

/-!
# Ford Section 3: integer polynomial systems

Ford's definition is over `ℤ[X]`.  The determinant calculation is most
convenient over `ℚ`, so this file keeps the source object integral and proves
the exact injective scalar-extension bridge used by the rational Jacobian.
-/

open Finset Polynomial Matrix
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The literal integer-polynomial version of Ford's type `(d,T)` systems.
The leading-coefficient equality is stated after the canonical injection into
`ℚ`, retaining Ford's factorial quotient without an integer-division
convention. -/
structure FordIntegerPolynomialSystem (k d T : ℕ) where
  poly : Fin k → ℤ[X]
  twoMultiplicity : ℕ
  zero_below : ∀ j : Fin k, (j : ℕ) + 1 ≤ d → poly j = 0
  degree_above : ∀ j : Fin k, d < (j : ℕ) + 1 →
    (poly j).natDegree = (j : ℕ) + 1 - d
  leadingCoeff_above : ∀ j : Fin k, d < (j : ℕ) + 1 →
    ((poly j).leadingCoeff : ℚ) =
      (((j : ℕ) + 1).factorial : ℚ) /
          (((j : ℕ) + 1 - d).factorial : ℚ) *
        ((2 ^ twoMultiplicity * T : ℕ) : ℚ)

/-- The source initial system `Ψ_j(X)=X^j`, over the integers. -/
def fordInitialIntegerPowerSystem (k : ℕ) :
    FordIntegerPolynomialSystem k 0 1 where
  poly j := X ^ ((j : ℕ) + 1)
  twoMultiplicity := 0
  zero_below j hj := by omega
  degree_above j _ := by simp
  leadingCoeff_above j _ := by
    simp only [leadingCoeff_X_pow, Int.cast_one, pow_zero, one_mul,
      Nat.sub_zero]
    rw [div_self (by exact_mod_cast Nat.factorial_ne_zero ((j : ℕ) + 1))]
    simp

/-- Injective extension of scalars from Ford's integer source system to the
rational realization used in the Jacobian calculation. -/
def fordRationalizeSystem
    {k d T : ℕ} (ψ : FordIntegerPolynomialSystem k d T) :
    FordPolynomialSystem k d T where
  poly j := (ψ.poly j).map (Int.castRingHom ℚ)
  twoMultiplicity := ψ.twoMultiplicity
  zero_below j hj := by simp [ψ.zero_below j hj]
  degree_above j hj := by
    rw [natDegree_map_eq_of_injective Int.cast_injective]
    exact ψ.degree_above j hj
  leadingCoeff_above j hj := by
    rw [leadingCoeff_map_of_injective Int.cast_injective]
    exact ψ.leadingCoeff_above j hj

@[simp] theorem fordRationalizeSystem_poly
    {k d T : ℕ} (ψ : FordIntegerPolynomialSystem k d T) (j : Fin k) :
    (fordRationalizeSystem ψ).poly j =
      (ψ.poly j).map (Int.castRingHom ℚ) := rfl

/-- Ford Lemma 3.1 for the literal integer source system, expressed after the
injective map to `ℚ`. -/
theorem ford_lemma_3_1_integer_source
    {k d T : ℕ} (ψ : FordIntegerPolynomialSystem k d T)
    (hT : 0 < T) (hdk : d ≤ k) (z : Fin (k - d) → ℤ) :
    (fordSystemJacobian (fordRationalizeSystem ψ) hdk
        (fun i => (z i : ℚ))).det =
      (((2 ^ ψ.twoMultiplicity * T : ℕ) : ℚ) ^ (k - d)) *
        (∏ j : Fin (k - d),
          ((d + (j : ℕ) + 1).factorial : ℚ) /
            ((j : ℕ).factorial : ℚ)) *
        ∏ i : Fin (k - d), ∏ j ∈ Finset.Ioi i,
          ((z j : ℚ) - (z i : ℚ)) := by
  exact ford_lemma_3_1_source (fordRationalizeSystem ψ) hT hdk
    (fun i => (z i : ℚ))

#print axioms fordInitialIntegerPowerSystem
#print axioms fordRationalizeSystem
#print axioms ford_lemma_3_1_integer_source

end

end GafniTao
