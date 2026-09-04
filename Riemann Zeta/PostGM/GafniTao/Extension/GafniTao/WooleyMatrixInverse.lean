import GafniTao.WooleyPolynomialNormalForm
import Mathlib.Algebra.Ring.GeomSum

/-!
# The near-identity matrix inversion in Wooley Sections 4 and 7

The coefficient matrices occurring after the polynomial normal-form reduction
are congruent to the identity modulo `p^c`.  Over `ZMod (p^B)` their error is
nilpotent, so the finite geometric series gives an inverse.  This is the exact
algebraic reason that Wooley may replace the transformed congruences by the
monomial congruences; no determinant or assumed inverse is used here.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- A nilpotent element has a finite geometric-series left inverse after
subtracting it from one. -/
theorem wooley_geomSum_mul_one_sub_of_pow_eq_zero
    {R : Type*} [Ring R] (x : R) (m : ℕ) (hx : x ^ m = 0) :
    (∑ i ∈ range m, x ^ i) * (1 - x) = 1 := by
  rw [geom_sum_mul_neg, hx, sub_zero]

/-- Left multiplication by `1-x` is injective when `x` is nilpotent. -/
theorem wooley_one_sub_mul_eq_zero_of_pow_eq_zero
    {R : Type*} [Ring R] (x y : R) (m : ℕ)
    (hx : x ^ m = 0) (hxy : (1 - x) * y = 0) :
    y = 0 := by
  let g : R := ∑ i ∈ range m, x ^ i
  calc
    y = 1 * y := (one_mul y).symm
    _ = (g * (1 - x)) * y := by
      rw [wooley_geomSum_mul_one_sub_of_pow_eq_zero x m hx]
    _ = g * ((1 - x) * y) := by rw [mul_assoc]
    _ = 0 := by rw [hxy, mul_zero]

/-- The scalar `(p^c)` is nilpotent modulo `p^B` as soon as `c` is positive.
The exponent `B+1` handles the degenerate modulus `p^0=1` uniformly. -/
theorem wooley_primePowerScalar_pow_succ_eq_zero
    (p c B : ℕ) (hc : 1 ≤ c) :
    ((p : ZMod (p ^ B)) ^ c) ^ (B + 1) = 0 := by
  rw [← pow_mul]
  rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  apply pow_dvd_pow p
  exact (Nat.le_succ B).trans
    (Nat.le_mul_of_pos_left (B + 1) (lt_of_lt_of_le Nat.zero_lt_one hc))

/-- Entrywise scalar multiplication by `p^c` makes every square matrix
nilpotent modulo `p^B`, with a uniform exponent independent of the matrix. -/
theorem wooley_primePower_smul_matrix_pow_succ_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p c B : ℕ) (hc : 1 ≤ c) (M : Matrix ι ι (ZMod (p ^ B))) :
    (((p : ZMod (p ^ B)) ^ c) • M) ^ (B + 1) = 0 := by
  rw [smul_pow]
  rw [wooley_primePowerScalar_pow_succ_eq_zero p c B hc, zero_smul]

/-- A matrix congruent to the identity modulo `p^c` has the explicit finite
geometric-series left inverse over `ZMod (p^B)`. -/
theorem wooley_identity_add_primePower_matrix_has_leftInverse
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p c B : ℕ) (hc : 1 ≤ c) (M : Matrix ι ι (ZMod (p ^ B))) :
    let E := ((p : ZMod (p ^ B)) ^ c) • M
    (∑ i ∈ range (B + 1), (-E) ^ i) * (1 + E) = 1 := by
  dsimp only
  have hnil : (-(((p : ZMod (p ^ B)) ^ c) • M)) ^ (B + 1) = 0 := by
    rw [neg_pow]
    rw [wooley_primePower_smul_matrix_pow_succ_eq_zero p c B hc M]
    simp
  simpa only [sub_neg_eq_add] using
    wooley_geomSum_mul_one_sub_of_pow_eq_zero
      (-(((p : ZMod (p ^ B)) ^ c) • M)) (B + 1) hnil

/-- The source's near-identity coefficient change is injective on column
vectors.  This is the form used to recover monomial displacement congruences
from polynomial displacement congruences. -/
theorem wooley_identity_add_primePower_mulVec_eq_zero_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p c B : ℕ) (hc : 1 ≤ c) (M : Matrix ι ι (ZMod (p ^ B)))
    (v : ι → ZMod (p ^ B)) :
    (1 + ((p : ZMod (p ^ B)) ^ c) • M).mulVec v = 0 ↔ v = 0 := by
  constructor
  · intro hv
    let E := ((p : ZMod (p ^ B)) ^ c) • M
    let G := ∑ i ∈ range (B + 1), (-E) ^ i
    have hleft : G * (1 + E) = 1 := by
      exact wooley_identity_add_primePower_matrix_has_leftInverse p c B hc M
    calc
      v = (1 : Matrix ι ι (ZMod (p ^ B))).mulVec v :=
        (Matrix.one_mulVec v).symm
      _ = (G * (1 + E)).mulVec v := by rw [hleft]
      _ = G.mulVec ((1 + E).mulVec v) := by rw [Matrix.mulVec_mulVec]
      _ = 0 := by rw [hv, Matrix.mulVec_zero]
  · rintro rfl
    exact Matrix.mulVec_zero _

/-- The canonical low coefficient matrix, reduced modulo an arbitrary
modulus. -/
def wooleyPolynomialSystemLowMatrixMod {k : ℕ}
    (phi : WooleyPolynomialSystem k) (q : ℕ) :
    Matrix (Fin k) (Fin k) (ZMod q) :=
  fun i j => (wooleyPolynomialSystemLowMatrix phi i j : ZMod q)

/-- Reduction modulo `p^B` preserves the literal `I+p^cM` shape of the low
coefficient matrix. -/
theorem WooleyPolynomialSystem.Spaced.lowMatrixMod_eq_identity_add
    {k : ℕ} {phi : WooleyPolynomialSystem k} {p c B : ℕ}
    (hphi : phi.Spaced p c) :
    ∃ M : Matrix (Fin k) (Fin k) (ZMod (p ^ B)),
      wooleyPolynomialSystemLowMatrixMod phi (p ^ B) =
        1 + ((p : ZMod (p ^ B)) ^ c) • M := by
  obtain ⟨M, hM⟩ := hphi.lowMatrix_eq_identity_add
  refine ⟨fun i j => (M i j : ZMod (p ^ B)), ?_⟩
  ext i j
  simp only [wooleyPolynomialSystemLowMatrixMod, Matrix.add_apply,
    Matrix.one_apply]
  rw [hM i j]
  push_cast
  rfl

/-- The transpose appears because rows of the canonical matrix are monomial
degrees while columns are source equations. -/
theorem WooleyPolynomialSystem.Spaced.lowMatrixMod_transpose_eq_identity_add
    {k : ℕ} {phi : WooleyPolynomialSystem k} {p c B : ℕ}
    (hphi : phi.Spaced p c) :
    ∃ M : Matrix (Fin k) (Fin k) (ZMod (p ^ B)),
      Matrix.transpose (wooleyPolynomialSystemLowMatrixMod phi (p ^ B)) =
        1 + ((p : ZMod (p ^ B)) ^ c) • M := by
  obtain ⟨M, hM⟩ := hphi.lowMatrixMod_eq_identity_add (B := B)
  refine ⟨Matrix.transpose M, ?_⟩
  rw [hM, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul]

/-- Consequently the low coefficient transformation of any spaced system is
injective modulo `p^B`. -/
theorem WooleyPolynomialSystem.Spaced.lowMatrixMod_transpose_mulVec_eq_zero_iff
    {k : ℕ} {phi : WooleyPolynomialSystem k} {p c B : ℕ}
    (hphi : phi.Spaced p c) (hc : 1 ≤ c)
    (v : Fin k → ZMod (p ^ B)) :
    (Matrix.transpose (wooleyPolynomialSystemLowMatrixMod phi (p ^ B))).mulVec v = 0 ↔
      v = 0 := by
  obtain ⟨M, hM⟩ := hphi.lowMatrixMod_transpose_eq_identity_add (B := B)
  rw [hM]
  exact wooley_identity_add_primePower_mulVec_eq_zero_iff p c B hc M v

/-- Explicit existence of the integral-linear-change matrix used in Sections
4 and 7, represented modulo the working modulus. -/
theorem WooleyPolynomialSystem.Spaced.exists_lowMatrixMod_transpose_leftInverse
    {k : ℕ} {phi : WooleyPolynomialSystem k} {p c B : ℕ}
    (hphi : phi.Spaced p c) (hc : 1 ≤ c) :
    ∃ G : Matrix (Fin k) (Fin k) (ZMod (p ^ B)),
      G * Matrix.transpose
        (wooleyPolynomialSystemLowMatrixMod phi (p ^ B)) = 1 := by
  obtain ⟨M, hM⟩ := hphi.lowMatrixMod_transpose_eq_identity_add (B := B)
  let E := ((p : ZMod (p ^ B)) ^ c) • M
  refine ⟨∑ i ∈ range (B + 1), (-E) ^ i, ?_⟩
  rw [hM]
  exact wooley_identity_add_primePower_matrix_has_leftInverse p c B hc M

#print axioms wooley_geomSum_mul_one_sub_of_pow_eq_zero
#print axioms wooley_one_sub_mul_eq_zero_of_pow_eq_zero
#print axioms wooley_primePowerScalar_pow_succ_eq_zero
#print axioms wooley_primePower_smul_matrix_pow_succ_eq_zero
#print axioms wooley_identity_add_primePower_matrix_has_leftInverse
#print axioms wooley_identity_add_primePower_mulVec_eq_zero_iff
#print axioms WooleyPolynomialSystem.Spaced.lowMatrixMod_eq_identity_add
#print axioms WooleyPolynomialSystem.Spaced.lowMatrixMod_transpose_eq_identity_add
#print axioms WooleyPolynomialSystem.Spaced.lowMatrixMod_transpose_mulVec_eq_zero_iff
#print axioms WooleyPolynomialSystem.Spaced.exists_lowMatrixMod_transpose_leftInverse

end

end GafniTao
