import GafniTao.FordVandermondeDeterminant

/-!
# Ford polynomial systems of type `(d,T)`

This is the literal degree/leading-coefficient data from Ford's Section 3.
Indices in Lean start at zero, so `j : Fin k` represents the source degree
`j+1`.
-/

open Finset Polynomial Matrix
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- A rational polynomial realization of Ford's system of type `(d,T)`.
The field `twoMultiplicity` is the source integer `m`. -/
structure FordPolynomialSystem (k d T : ℕ) where
  poly : Fin k → ℚ[X]
  twoMultiplicity : ℕ
  zero_below : ∀ j : Fin k, (j : ℕ) + 1 ≤ d → poly j = 0
  degree_above : ∀ j : Fin k, d < (j : ℕ) + 1 →
    (poly j).natDegree = (j : ℕ) + 1 - d
  leadingCoeff_above : ∀ j : Fin k, d < (j : ℕ) + 1 →
    (poly j).leadingCoeff =
      (((j : ℕ) + 1).factorial : ℚ) /
          (((j : ℕ) + 1 - d).factorial : ℚ) *
        ((2 ^ twoMultiplicity * T : ℕ) : ℚ)

/-- The source degree `d+j+1`, represented as an index in a `k`-system. -/
def fordAboveIndex {k d : ℕ} (hdk : d ≤ k) (j : Fin (k - d)) : Fin k :=
  ⟨d + j, by omega⟩

@[simp] theorem fordAboveIndex_val
    {k d : ℕ} (hdk : d ≤ k) (j : Fin (k - d)) :
    (fordAboveIndex hdk j : ℕ) = d + j := rfl

theorem fordAboveIndex_source_degree
    {k d : ℕ} (hdk : d ≤ k) (j : Fin (k - d)) :
    (fordAboveIndex hdk j : ℕ) + 1 - d = (j : ℕ) + 1 := by
  change (d + (j : ℕ)) + 1 - d = (j : ℕ) + 1
  omega

theorem fordAboveIndex_above
    {k d : ℕ} (hdk : d ≤ k) (j : Fin (k - d)) :
    d < (fordAboveIndex hdk j : ℕ) + 1 := by
  simp only [fordAboveIndex_val]
  omega

/-- The initial power system `Ψ_j(x)=x^j` is of type `(0,1)`. -/
def fordInitialPowerSystem (k : ℕ) : FordPolynomialSystem k 0 1 where
  poly j := X ^ ((j : ℕ) + 1)
  twoMultiplicity := 0
  zero_below j hj := by omega
  degree_above j _ := by
    simp only [natDegree_X_pow, Nat.sub_zero]
  leadingCoeff_above j _ := by
    simp only [leadingCoeff_X_pow, Nat.cast_one, pow_zero, one_mul,
      Nat.sub_zero]
    rw [div_self (by exact_mod_cast Nat.factorial_ne_zero ((j : ℕ) + 1))]
    simp

theorem fordPolynomialSystem_above_degree
    {k d T : ℕ} (ψ : FordPolynomialSystem k d T)
    (hdk : d ≤ k) (j : Fin (k - d)) :
    (ψ.poly (fordAboveIndex hdk j)).natDegree = (j : ℕ) + 1 := by
  rw [ψ.degree_above _ (fordAboveIndex_above hdk j),
    fordAboveIndex_source_degree]

theorem fordPolynomialSystem_above_lc
    {k d T : ℕ} (ψ : FordPolynomialSystem k d T)
    (hdk : d ≤ k) (j : Fin (k - d)) :
    (ψ.poly (fordAboveIndex hdk j)).leadingCoeff =
      ((d + (j : ℕ) + 1).factorial : ℚ) /
          (((j : ℕ) + 1).factorial : ℚ) *
        ((2 ^ ψ.twoMultiplicity * T : ℕ) : ℚ) := by
  rw [ψ.leadingCoeff_above _ (fordAboveIndex_above hdk j)]
  simp only [fordAboveIndex_val]
  rw [show d + (j : ℕ) + 1 - d = (j : ℕ) + 1 by omega]

theorem fordPolynomialSystem_above_lc_ne_zero
    {k d T : ℕ} (ψ : FordPolynomialSystem k d T)
    (hT : 0 < T) (hdk : d ≤ k) (j : Fin (k - d)) :
    (ψ.poly (fordAboveIndex hdk j)).leadingCoeff ≠ 0 := by
  rw [fordPolynomialSystem_above_lc ψ hdk j]
  positivity

/-- Ford's Jacobian matrix for the nonzero portion of a type `(d,T)`
system. -/
def fordSystemJacobian
    {k d T : ℕ} (ψ : FordPolynomialSystem k d T) (hdk : d ≤ k)
    (z : Fin (k - d) → ℚ) : Matrix (Fin (k - d)) (Fin (k - d)) ℚ :=
  Matrix.of fun i j =>
    (ψ.poly (fordAboveIndex hdk j)).derivative.eval (z i)

/-- Ford Lemma 3.1, already specialized to a source system of type `(d,T)`.
The next theorem extracts Ford's common `(2^m T)^(k-d)` factor. -/
theorem ford_lemma_3_1_system
    {k d T : ℕ} (ψ : FordPolynomialSystem k d T)
    (hT : 0 < T) (hdk : d ≤ k) (z : Fin (k - d) → ℚ) :
    (fordSystemJacobian ψ hdk z).det =
      (∏ j : Fin (k - d),
          (ψ.poly (fordAboveIndex hdk j)).leadingCoeff *
            ((j : ℕ) + 1 : ℚ)) *
        ∏ i : Fin (k - d), ∏ j ∈ Finset.Ioi i, (z j - z i) := by
  unfold fordSystemJacobian
  exact ford_lemma_3_1_jacobian z
    (fun j => ψ.poly (fordAboveIndex hdk j))
    (fordPolynomialSystem_above_degree ψ hdk)
    (fordPolynomialSystem_above_lc_ne_zero ψ hT hdk)

theorem ford_above_derivative_lc_source
    {k d T : ℕ} (ψ : FordPolynomialSystem k d T)
    (hT : 0 < T) (hdk : d ≤ k) (j : Fin (k - d)) :
    (ψ.poly (fordAboveIndex hdk j)).derivative.leadingCoeff =
      ((d + (j : ℕ) + 1).factorial : ℚ) /
          ((j : ℕ).factorial : ℚ) *
        ((2 ^ ψ.twoMultiplicity * T : ℕ) : ℚ) := by
  rw [ford_derivative_leadingCoeff
    (fordPolynomialSystem_above_degree ψ hdk j)
    (fordPolynomialSystem_above_lc_ne_zero ψ hT hdk j),
    fordPolynomialSystem_above_lc ψ hdk j]
  have hfac : (((j : ℕ) + 1).factorial : ℚ) =
      ((j : ℕ) + 1 : ℚ) * ((j : ℕ).factorial : ℚ) := by
    rw [Nat.factorial_succ]
    norm_num [mul_comm]
  rw [hfac]
  field_simp

/-- Ford Lemma 3.1 in the source's fully factored normalization. -/
theorem ford_lemma_3_1_source
    {k d T : ℕ} (ψ : FordPolynomialSystem k d T)
    (hT : 0 < T) (hdk : d ≤ k) (z : Fin (k - d) → ℚ) :
    (fordSystemJacobian ψ hdk z).det =
      (((2 ^ ψ.twoMultiplicity * T : ℕ) : ℚ) ^ (k - d)) *
        (∏ j : Fin (k - d),
          ((d + (j : ℕ) + 1).factorial : ℚ) /
            ((j : ℕ).factorial : ℚ)) *
        ∏ i : Fin (k - d), ∏ j ∈ Finset.Ioi i, (z j - z i) := by
  rw [ford_lemma_3_1_system ψ hT hdk z]
  have hterm : ∀ j : Fin (k - d),
      (ψ.poly (fordAboveIndex hdk j)).leadingCoeff *
          ((j : ℕ) + 1 : ℚ) =
        (((d + (j : ℕ) + 1).factorial : ℚ) /
            ((j : ℕ).factorial : ℚ)) *
          ((2 ^ ψ.twoMultiplicity * T : ℕ) : ℚ) := by
    intro j
    rw [← ford_derivative_leadingCoeff
      (fordPolynomialSystem_above_degree ψ hdk j)
      (fordPolynomialSystem_above_lc_ne_zero ψ hT hdk j)]
    exact ford_above_derivative_lc_source ψ hT hdk j
  rw [Finset.prod_congr rfl (fun j _ => hterm j), Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

#print axioms fordInitialPowerSystem
#print axioms fordPolynomialSystem_above_degree
#print axioms fordPolynomialSystem_above_lc
#print axioms fordPolynomialSystem_above_lc_ne_zero
#print axioms ford_lemma_3_1_system
#print axioms ford_above_derivative_lc_source
#print axioms ford_lemma_3_1_source

end

end GafniTao
