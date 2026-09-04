import GafniTao.WooleyTaylorCoefficient

/-!
# Wooley's integral Omega matrix after equation (7.10)

This file packages the translated coefficients of the top `r` equations into
the literal integral matrix used in Section 7.  The source writes powers
`h^(k-r+l-i)` even when the exponent is negative.  We preserve that notation
as a Laurent identity over `ℚ`; integrality belongs to the matrix entry, not
to the displayed power by itself.
-/

open Finset Polynomial Matrix
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem wooleySection7Node_succ_le
    {k r : ℕ} (hrk : r ≤ k) (l : Fin r) :
    wooleySection7Node k r l + 1 ≤ k := by
  unfold wooleySection7Node
  omega

/-- The integral coefficient supplied by the Laurent Taylor factorization
for row `i`, column `l` of the source matrix. -/
def wooleySection7OmegaEntry
    {k r p c : ℕ} (hrk : r ≤ k) (h : ℤ) (hh : h ≠ 0)
    (psi : Fin r → Polynomial ℤ) (i l : Fin r) : ℤ :=
  Classical.choose
    (wooley_taylorCoefficient_exists_laurent_omega
      (p := p) (c := c) (i := (i : ℕ) + 1)
      (j := wooleySection7Node k r l + 1) (k := k)
      h hh (wooleySection7Node_succ_le hrk l) (psi l))

/-- The source matrix `A=(Omega_il)`, with rows indexed by Taylor degree and
columns indexed by the top `r` source equations. -/
def wooleySection7OmegaMatrix
    {k r p c : ℕ} (hrk : r ≤ k) (h : ℤ) (hh : h ≠ 0)
    (psi : Fin r → Polynomial ℤ) : Matrix (Fin r) (Fin r) ℤ :=
  fun i l => wooleySection7OmegaEntry (p := p) (c := c) hrk h hh psi i l

theorem wooleySection7OmegaEntry_spec
    {k r p c : ℕ} (hrk : r ≤ k) (h : ℤ) (hh : h ≠ 0)
    (psi : Fin r → Polynomial ℤ) (i l : Fin r) :
    let j := wooleySection7Node k r l + 1
    let degree := (i : ℕ) + 1
    ((taylor h
      (X ^ j + C ((p : ℤ) ^ c) * X ^ (k + 1) * psi l)).coeff degree : ℚ) =
        (h : ℚ) ^ ((j : ℤ) - (degree : ℤ)) *
          (wooleySection7OmegaEntry (p := p) (c := c) hrk h hh psi i l : ℚ) ∧
    Int.ModEq ((p : ℤ) ^ c)
      (wooleySection7OmegaEntry (p := p) (c := c) hrk h hh psi i l)
      (Nat.choose j degree : ℤ) := by
  exact Classical.choose_spec
    (wooley_taylorCoefficient_exists_laurent_omega
      (p := p) (c := c) (i := (i : ℕ) + 1)
      (j := wooleySection7Node k r l + 1) (k := k)
      h hh (wooleySection7Node_succ_le hrk l) (psi l))

theorem wooleySection7OmegaMatrix_mod_prime
    {k r p c : ℕ} (hc : 1 ≤ c) (hrk : r ≤ k)
    (h : ℤ) (hh : h ≠ 0) (psi : Fin r → Polynomial ℤ)
    (i l : Fin r) :
    ((wooleySection7OmegaMatrix (p := p) (c := c) hrk h hh psi i l : ℤ) : ZMod p) =
      (Nat.choose (wooleySection7Node k r l + 1) ((i : ℕ) + 1) : ZMod p) := by
  exact wooley_taylorOmega_mod_prime hc
    (wooleySection7OmegaEntry_spec (p := p) (c := c) hrk h hh psi i l).2

/-- Literal polynomial version of the display defining `Upsilon_l` after
(7.10).  It is an equality over `ℚ` solely because the source's displayed
powers of `h` may have negative exponent; every `Omega` entry itself remains
an integer. -/
theorem wooleySection7_taylor_laurent_expansion
    {k r p c : ℕ} (hrk : r ≤ k) (h : ℤ) (hh : h ≠ 0)
    (psi : Fin r → Polynomial ℤ) (l : Fin r) :
    let j := wooleySection7Node k r l + 1
    let phi := X ^ j + C ((p : ℤ) ^ c) * X ^ (k + 1) * psi l
    Polynomial.map (Int.castRingHom ℚ) (wooleyTaylorDifference h phi) =
      ∑ i : Fin r,
        C ((h : ℚ) ^ ((j : ℤ) - (((i : ℕ) + 1 : ℕ) : ℤ)) *
          (wooleySection7OmegaMatrix (p := p) (c := c)
            hrk h hh psi i l : ℚ)) * X ^ ((i : ℕ) + 1) +
      X ^ (r + 1) *
        Polynomial.map (Int.castRingHom ℚ)
          (wooleyPolynomialTail (r + 1)
            (wooleyTaylorDifference h phi)) := by
  dsimp only
  have hbase := congrArg (Polynomial.map (Int.castRingHom ℚ))
    (wooleyTaylorDifference_eq_low_sum_add_tail r h
      (X ^ (wooleySection7Node k r l + 1) +
        C ((p : ℤ) ^ c) * X ^ (k + 1) * psi l))
  rw [hbase]
  rw [Polynomial.map_add, Polynomial.map_sum]
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_C]
  apply congrArg (fun z => z + _)
  apply Finset.sum_congr rfl
  intro i hi
  have hpositive :
      (wooleyTaylorDifference h
        (X ^ (wooleySection7Node k r l + 1) +
          C ((p : ℤ) ^ c) * X ^ (k + 1) * psi l)).coeff ((i : ℕ) + 1) =
        (taylor h
          (X ^ (wooleySection7Node k r l + 1) +
            C ((p : ℤ) ^ c) * X ^ (k + 1) * psi l)).coeff ((i : ℕ) + 1) := by
    have hne : (i : ℕ) + 1 ≠ 0 := by omega
    unfold wooleyTaylorDifference
    rw [coeff_sub, coeff_C]
    simp only [if_neg hne, sub_zero]
  rw [hpositive]
  change C (((taylor h
      (X ^ (wooleySection7Node k r l + 1) +
        C ((p : ℤ) ^ c) * X ^ (k + 1) * psi l)).coeff ((i : ℕ) + 1) : ℤ) : ℚ) *
      X ^ ((i : ℕ) + 1) = _
  rw [(wooleySection7OmegaEntry_spec
    (p := p) (c := c) hrk h hh psi i l).1]
  rfl

/-- The translated-and-dilated coefficient matrix in (7.10), over `ℚ`.
Rows are powers of the new variable and columns are the top `r` equations. -/
def wooleySection7DilatedCoefficientMatrixQ
    {k r p c : ℕ} (a : ℕ) (h : ℤ)
    (psi : Fin r → Polynomial ℤ) : Matrix (Fin r) (Fin r) ℚ :=
  fun i l =>
    ((taylor h
      (X ^ (wooleySection7Node k r l + 1) +
        C ((p : ℤ) ^ c) * X ^ (k + 1) * psi l)).coeff ((i : ℕ) + 1) : ℚ) *
      (p : ℚ) ^ (a * ((i : ℕ) + 1))

def wooleySection7RowValuationMatrixQ
    (r p a : ℕ) (h : ℤ) : Matrix (Fin r) (Fin r) ℚ :=
  Matrix.diagonal (fun i : Fin r =>
    (p : ℚ) ^ (a * ((i : ℕ) + 1)) / (h : ℚ) ^ ((i : ℕ) + 1))

def wooleySection7OmegaMatrixQ
    {k r p c : ℕ} (hrk : r ≤ k) (h : ℤ) (hh : h ≠ 0)
    (psi : Fin r → Polynomial ℤ) : Matrix (Fin r) (Fin r) ℚ :=
  fun i l =>
    (wooleySection7OmegaMatrix (p := p) (c := c) hrk h hh psi i l : ℚ)

def wooleySection7ColumnValuationMatrixQ
    (k r : ℕ) (h : ℤ) : Matrix (Fin r) (Fin r) ℚ :=
  Matrix.diagonal (fun l : Fin r =>
    (h : ℚ) ^ (wooleySection7Node k r l + 1))

theorem wooleySection7_row_valuation_factor
    {p a gamma i : ℕ} {omega : ℤ}
    (hp : p ≠ 0) (homega : omega ≠ 0) (hgamma : gamma ≤ a) :
    (p : ℚ) ^ (a * i) /
        ((omega : ℚ) * (p : ℚ) ^ gamma) ^ i =
      (omega : ℚ) ^ (-(i : ℤ)) *
        (p : ℚ) ^ ((a - gamma) * i) := by
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp
  have homegaq : (omega : ℚ) ≠ 0 := by exact_mod_cast homega
  rw [mul_pow, _root_.zpow_neg, zpow_natCast]
  have hexp : gamma * i + (a - gamma) * i = a * i := by
    rw [← Nat.add_mul, Nat.add_sub_of_le hgamma]
  rw [← pow_mul]
  rw [show a * i = gamma * i + (a - gamma) * i by omega, pow_add]
  field_simp

theorem wooleySection7_column_valuation_factor
    {p gamma j : ℕ} (omega : ℤ) :
    (((omega : ℚ) * (p : ℚ) ^ gamma) ^ j) =
      (omega : ℚ) ^ j * (p : ℚ) ^ (gamma * j) := by
  rw [mul_pow, pow_mul]

def wooleySection7SeparatedRowMatrixQ
    (r p a gamma : ℕ) (omega : ℤ) : Matrix (Fin r) (Fin r) ℚ :=
  Matrix.diagonal (fun i : Fin r =>
    (omega : ℚ) ^ (-(((i : ℕ) + 1 : ℕ) : ℤ)) *
      (p : ℚ) ^ ((a - gamma) * ((i : ℕ) + 1)))

def wooleySection7SeparatedColumnMatrixQ
    (k r p gamma : ℕ) (omega : ℤ) : Matrix (Fin r) (Fin r) ℚ :=
  Matrix.diagonal (fun l : Fin r =>
    (omega : ℚ) ^ (wooleySection7Node k r l + 1) *
      (p : ℚ) ^ (gamma * (wooleySection7Node k r l + 1)))

/-- Exact row--Omega--column factorization hidden in the paragraph after
(7.10).  The denominators in the row factor are why one must retain the
source's valuation loss rather than treating the change of equations as an
arbitrary invertible rational matrix. -/
theorem wooleySection7_dilatedCoefficientMatrix_factorization
    {k r p c : ℕ} (hrk : r ≤ k) (a : ℕ) (h : ℤ) (hh : h ≠ 0)
    (psi : Fin r → Polynomial ℤ) :
    wooleySection7DilatedCoefficientMatrixQ (k := k) (p := p) (c := c) a h psi =
      wooleySection7RowValuationMatrixQ r p a h *
        wooleySection7OmegaMatrixQ (p := p) (c := c) hrk h hh psi *
      wooleySection7ColumnValuationMatrixQ k r h := by
  ext i l
  simp only [wooleySection7DilatedCoefficientMatrixQ,
    wooleySection7RowValuationMatrixQ, wooleySection7OmegaMatrixQ,
    wooleySection7OmegaMatrix, wooleySection7ColumnValuationMatrixQ,
    Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [(wooleySection7OmegaEntry_spec
    (p := p) (c := c) hrk h hh psi i l).1]
  have hhq : (h : ℚ) ≠ 0 := by exact_mod_cast hh
  rw [zpow_sub₀ hhq, zpow_natCast, zpow_natCast]
  field_simp

/-- Substituting `h = omega*p^gamma` exposes every prime valuation in the
coefficient factorization.  The remaining powers of `omega` are units at
`p`; the row carries `(a-gamma)i` and the column carries
`gamma(k-r+l)`, exactly as in the source calculation. -/
theorem wooleySection7_dilatedCoefficientMatrix_factorization_of_separation
    {k r p c a gamma : ℕ} (hp : p ≠ 0) (hrk : r ≤ k)
    (hgamma : gamma ≤ a) (omega h : ℤ) (homega : omega ≠ 0)
    (hh : h ≠ 0) (hsep : h = omega * (p : ℤ) ^ gamma)
    (psi : Fin r → Polynomial ℤ) :
    wooleySection7DilatedCoefficientMatrixQ (k := k) (p := p) (c := c)
        a h psi =
      wooleySection7SeparatedRowMatrixQ r p a gamma omega *
        wooleySection7OmegaMatrixQ (p := p) (c := c) hrk h hh psi *
      wooleySection7SeparatedColumnMatrixQ k r p gamma omega := by
  rw [wooleySection7_dilatedCoefficientMatrix_factorization hrk a h hh psi]
  have hrow :
      wooleySection7RowValuationMatrixQ r p a h =
        wooleySection7SeparatedRowMatrixQ r p a gamma omega := by
    subst h
    ext i j
    simp only [wooleySection7RowValuationMatrixQ,
      wooleySection7SeparatedRowMatrixQ, Matrix.diagonal_apply]
    split_ifs with hij
    · subst j
      push_cast
      exact wooleySection7_row_valuation_factor hp homega hgamma
    · rfl
  have hcol :
      wooleySection7ColumnValuationMatrixQ k r h =
        wooleySection7SeparatedColumnMatrixQ k r p gamma omega := by
    subst h
    ext i j
    simp only [wooleySection7ColumnValuationMatrixQ,
      wooleySection7SeparatedColumnMatrixQ, Matrix.diagonal_apply]
    split_ifs with hij
    · subst j
      push_cast
      exact wooleySection7_column_valuation_factor omega
    · rfl
  rw [hrow, hcol]

/-- The exact integral matrix occurring after (7.10) is invertible modulo
every source prime power. -/
theorem wooleySection7OmegaMatrix_exists_leftInverse
    {k r p c L : ℕ} (hp : p.Prime) (hc : 1 ≤ c)
    (hrk : r ≤ k) (hkp : k < p)
    (h : ℤ) (hh : h ≠ 0) (psi : Fin r → Polynomial ℤ) :
    ∃ G : Matrix (Fin r) (Fin r) (ZMod (p ^ L)),
      G * wooleyIntMatrixMod
          (wooleySection7OmegaMatrix (p := p) (c := c) hrk h hh psi) (p ^ L) = 1 := by
  apply wooleySection7_sourceMatrix_exists_leftInverse_primePower hp hrk hkp
  exact wooleySection7OmegaMatrix_mod_prime (p := p) hc hrk h hh psi

#print axioms wooleySection7Node_succ_le
#print axioms wooleySection7OmegaEntry_spec
#print axioms wooleySection7OmegaMatrix_mod_prime
#print axioms wooleySection7_taylor_laurent_expansion
#print axioms wooleySection7_row_valuation_factor
#print axioms wooleySection7_column_valuation_factor
#print axioms wooleySection7_dilatedCoefficientMatrix_factorization
#print axioms wooleySection7_dilatedCoefficientMatrix_factorization_of_separation
#print axioms wooleySection7OmegaMatrix_exists_leftInverse

end

end GafniTao
