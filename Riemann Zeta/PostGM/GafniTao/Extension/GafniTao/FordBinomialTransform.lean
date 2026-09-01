import GafniTao.FordLemma32Arithmetic
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Ford Lemma 3.2: triangular binomial transform

Ford replaces `Ψ_j` by
`Phi_j = sum_{ℓ=0}^j choose(j,ℓ) Ψ_ℓ c^(j-ℓ)` before (3.6),
with `Ψ_0 = 0`.  The zero-based Lean definition below isolates the current
term and the strictly lower triangular part.  The main theorem proves, rather
than assumes, that this operation preserves the exact type `(d,T)` and the
same source multiplicity `m`.
-/

open Finset Polynomial
open scoped BigOperators

namespace GafniTao

noncomputable section

def fordBinomialLower
    {k d T : ℕ} (ψ : FordIntegerPolynomialSystem k d T) (c : ℤ)
    (j : Fin k) : ℤ[X] :=
  ∑ l : Fin (j : ℕ),
    C (((((j : ℕ) + 1).choose ((l : ℕ) + 1) : ℕ) : ℤ) *
      c ^ ((j : ℕ) + 1 - ((l : ℕ) + 1))) *
      ψ.poly (Fin.castLE j.isLt.le l)

def fordBinomialTranslatePoly
    {k d T : ℕ} (ψ : FordIntegerPolynomialSystem k d T) (c : ℤ)
    (j : Fin k) : ℤ[X] :=
  ψ.poly j + fordBinomialLower ψ c j

theorem fordBinomialLower_eq_zero_of_below
    {k d T : ℕ} (ψ : FordIntegerPolynomialSystem k d T) (c : ℤ)
    (j : Fin k) (hj : (j : ℕ) + 1 ≤ d) :
    fordBinomialLower ψ c j = 0 := by
  unfold fordBinomialLower
  apply Finset.sum_eq_zero
  intro l hl
  rw [ψ.zero_below]
  · simp
  · have hlj : (l : ℕ) < (j : ℕ) := l.isLt
    simp only [Fin.val_castLE]
    omega

theorem fordBinomialLower_natDegree_lt
    {k d T : ℕ} (ψ : FordIntegerPolynomialSystem k d T) (c : ℤ)
    (j : Fin k) (hj : d < (j : ℕ) + 1) :
    (fordBinomialLower ψ c j).natDegree < (j : ℕ) + 1 - d := by
  have hpos : 0 < (j : ℕ) + 1 - d := by omega
  apply lt_of_le_of_lt
    (Polynomial.natDegree_sum_le_of_forall_le
      (Finset.univ : Finset (Fin (j : ℕ)))
      (fun l => C (((((j : ℕ) + 1).choose ((l : ℕ) + 1) : ℕ) : ℤ) *
          c ^ ((j : ℕ) + 1 - ((l : ℕ) + 1))) *
        ψ.poly (Fin.castLE j.isLt.le l))
      (n := (j : ℕ) - d) ?_)
  · omega
  · intro l hl
    have hlj : (l : ℕ) < (j : ℕ) := l.isLt
    let li : Fin k := Fin.castLE j.isLt.le l
    by_cases hld : (l : ℕ) + 1 ≤ d
    · have hld' : (li : ℕ) + 1 ≤ d := by
        simpa [li] using hld
      change (C _ * ψ.poly li).natDegree ≤ (j : ℕ) - d
      rw [ψ.zero_below li hld']
      simp
    · have hdl : d < (l : ℕ) + 1 := Nat.lt_of_not_ge hld
      calc
        (C (((((j : ℕ) + 1).choose ((l : ℕ) + 1) : ℕ) : ℤ) *
              c ^ ((j : ℕ) + 1 - ((l : ℕ) + 1))) * ψ.poly li).natDegree
            ≤ (ψ.poly li).natDegree := Polynomial.natDegree_C_mul_le _ _
        _ = (l : ℕ) + 1 - d := ψ.degree_above li hdl
        _ ≤ (j : ℕ) - d := by omega

theorem fordBinomialTranslatePoly_degree
    {k d T : ℕ} (ψ : FordIntegerPolynomialSystem k d T) (c : ℤ)
    (j : Fin k) (hj : d < (j : ℕ) + 1) :
    (fordBinomialTranslatePoly ψ c j).natDegree =
      (j : ℕ) + 1 - d := by
  unfold fordBinomialTranslatePoly
  rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
  · exact ψ.degree_above j hj
  · rw [ψ.degree_above j hj]
    exact fordBinomialLower_natDegree_lt ψ c j hj

theorem fordBinomialTranslatePoly_leadingCoeff
    {k d T : ℕ} (ψ : FordIntegerPolynomialSystem k d T) (c : ℤ)
    (j : Fin k) (hj : d < (j : ℕ) + 1) :
    (fordBinomialTranslatePoly ψ c j).leadingCoeff =
      (ψ.poly j).leadingCoeff := by
  unfold fordBinomialTranslatePoly
  rw [Polynomial.leadingCoeff_add_of_degree_lt']
  exact Polynomial.degree_lt_degree (by
    rw [ψ.degree_above j hj]
    exact fordBinomialLower_natDegree_lt ψ c j hj)

/-- The exact integral system `Φ` used in Ford equations (3.6)--(3.7). -/
def fordBinomialTranslateSystem
    {k d T : ℕ} (ψ : FordIntegerPolynomialSystem k d T) (c : ℤ) :
    FordIntegerPolynomialSystem k d T where
  poly j := fordBinomialTranslatePoly ψ c j
  twoMultiplicity := ψ.twoMultiplicity
  zero_below j hj := by
    unfold fordBinomialTranslatePoly
    rw [ψ.zero_below j hj, fordBinomialLower_eq_zero_of_below ψ c j hj]
    exact zero_add 0
  degree_above j hj := fordBinomialTranslatePoly_degree ψ c j hj
  leadingCoeff_above j hj := by
    rw [fordBinomialTranslatePoly_leadingCoeff ψ c j hj]
    exact ψ.leadingCoeff_above j hj

@[simp] theorem fordBinomialTranslateSystem_twoMultiplicity
    {k d T : ℕ} (ψ : FordIntegerPolynomialSystem k d T) (c : ℤ) :
    (fordBinomialTranslateSystem ψ c).twoMultiplicity =
      ψ.twoMultiplicity := rfl

/-- Ford's sentence after (3.6): Lemma 3.1 makes the two Jacobian
determinants identical, because the triangular transform preserves every
leading coefficient and the same `m,T`. -/
theorem fordBinomialTranslateSystem_jacobian
    {k d T : ℕ} (ψ : FordIntegerPolynomialSystem k d T) (c : ℤ)
    (hT : 0 < T) (hdk : d ≤ k) (z : Fin (k - d) → ℤ) :
    (fordSystemJacobian
        (fordRationalizeSystem (fordBinomialTranslateSystem ψ c)) hdk
        (fun i => (z i : ℚ))).det =
      (fordSystemJacobian (fordRationalizeSystem ψ) hdk
        (fun i => (z i : ℚ))).det := by
  rw [ford_lemma_3_1_integer_source (fordBinomialTranslateSystem ψ c)
      hT hdk z,
    ford_lemma_3_1_integer_source ψ hT hdk z]
  rfl

#print axioms fordBinomialLower_eq_zero_of_below
#print axioms fordBinomialLower_natDegree_lt
#print axioms fordBinomialTranslatePoly_degree
#print axioms fordBinomialTranslatePoly_leadingCoeff
#print axioms fordBinomialTranslateSystem
#print axioms fordBinomialTranslateSystem_jacobian

end

end GafniTao
