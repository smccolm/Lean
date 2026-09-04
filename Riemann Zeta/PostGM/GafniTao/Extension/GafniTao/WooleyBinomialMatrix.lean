import GafniTao.WooleyMatrixInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Nat.Prime.Factorial

/-!
# The binomial/Vandermonde matrix in Wooley Section 7

For `1 ≤ i,l ≤ r`, the source matrix is congruent modulo `p` to
`choose (k-r+l) i`.  After transposing to use rows as evaluation points,
scaling column `i` by `i!`, and factoring the nonzero evaluation point from
each row, one obtains evaluation of the monic falling-factorial basis.  Its
determinant is the ordinary Vandermonde determinant.  This file formalizes
that exact calculation.
-/

open Finset Polynomial Matrix
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- Zero-indexed evaluation point corresponding to the source integer
`k-r+l`, where the paper numbers `l` from one. -/
def wooleySection7Node (k r : ℕ) (l : Fin r) : ℕ :=
  k - r + (l : ℕ)

/-- Transpose of the source's binomial coefficient matrix modulo `p`: rows
are evaluation points and columns are degrees. -/
def wooleySection7BinomialMatrix (k r p : ℕ) :
    Matrix (Fin r) (Fin r) (ZMod p) :=
  fun l i =>
    (Nat.choose (wooleySection7Node k r l + 1) ((i : ℕ) + 1) : ZMod p)

/-- Evaluation matrix for the monic descending-Pochhammer basis. -/
def wooleySection7FallingEvalMatrix (k r p : ℕ) :
    Matrix (Fin r) (Fin r) (ZMod p) :=
  fun l i =>
    (descPochhammer (ZMod p) (i : ℕ)).eval
      (wooleySection7Node k r l : ZMod p)

/-- Entrywise reduction of an integer matrix modulo `q`. -/
def wooleyIntMatrixMod {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (q : ℕ) :
    Matrix (Fin r) (Fin r) (ZMod q) :=
  fun i j => (A i j : ZMod q)

theorem wooleyIntMatrixMod_det {r q : ℕ}
    (A : Matrix (Fin r) (Fin r) ℤ) :
    (A.det : ZMod q) = (wooleyIntMatrixMod A q).det := by
  change (Int.castRingHom (ZMod q)) A.det =
    ((Int.castRingHom (ZMod q)).mapMatrix A).det
  exact (Int.castRingHom (ZMod q)).map_det A

/-- The paper's factorial scaling and row factorization, entry for entry. -/
theorem wooleySection7_binomial_factorization
    (k r p : ℕ) :
    wooleySection7BinomialMatrix k r p *
        Matrix.diagonal (fun i : Fin r =>
          (((i : ℕ) + 1).factorial : ZMod p)) =
      Matrix.diagonal (fun l : Fin r =>
          ((wooleySection7Node k r l + 1 : ℕ) : ZMod p)) *
        wooleySection7FallingEvalMatrix k r p := by
  ext l i
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul,
    wooleySection7BinomialMatrix, wooleySection7FallingEvalMatrix]
  rw [descPochhammer_eval_eq_descFactorial]
  rw [← Nat.cast_mul, ← Nat.cast_mul]
  congr 1
  rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
  exact Nat.succ_descFactorial_succ _ _

/-- The Section 7 nodes remain distinct after reduction modulo `p` under the
paper's hypotheses `r ≤ k < p`. -/
theorem wooleySection7_nodes_injective_mod_prime
    {k r p : ℕ} (hrk : r ≤ k) (hkp : k < p) :
    Function.Injective
      (fun l : Fin r => (wooleySection7Node k r l : ZMod p)) := by
  intro l m hlm
  have hl_lt : wooleySection7Node k r l < p := by
    unfold wooleySection7Node
    omega
  have hm_lt : wooleySection7Node k r m < p := by
    unfold wooleySection7Node
    omega
  have hval := congrArg ZMod.val hlm
  rw [ZMod.val_natCast_of_lt hl_lt, ZMod.val_natCast_of_lt hm_lt] at hval
  apply Fin.ext
  unfold wooleySection7Node at hval
  omega

/-- Every factored row scalar is nonzero modulo `p`. -/
theorem wooleySection7_node_succ_ne_zero
    {k r p : ℕ} (hrk : r ≤ k) (hkp : k < p) (l : Fin r) :
    ((wooleySection7Node k r l + 1 : ℕ) : ZMod p) ≠ 0 := by
  have hpos : 0 < wooleySection7Node k r l + 1 := Nat.zero_lt_succ _
  have hlt : wooleySection7Node k r l + 1 < p := by
    unfold wooleySection7Node
    omega
  intro hzero
  have hval := congrArg ZMod.val hzero
  rw [ZMod.val_natCast_of_lt hlt] at hval
  simp only [ZMod.val_zero] at hval
  omega

/-- The exact corrected determinant calculation in the paragraph following
(7.10): the binomial matrix is nonsingular modulo every prime `p>k`. -/
theorem wooleySection7_binomialMatrix_det_ne_zero
    {k r p : ℕ} (hp : p.Prime) (hrk : r ≤ k) (hkp : k < p) :
    (wooleySection7BinomialMatrix k r p).det ≠ 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  let v : Fin r → ZMod p :=
    fun l => (wooleySection7Node k r l : ZMod p)
  let P : Fin r → Polynomial (ZMod p) :=
    fun i => descPochhammer (ZMod p) (i : ℕ)
  have hdeg : ∀ i, (P i).natDegree = (i : ℕ) := by
    intro i
    exact descPochhammer_natDegree (ZMod p) (i : ℕ)
  have hmonic : ∀ i, (P i).Monic := by
    intro i
    exact monic_descPochhammer (ZMod p) (i : ℕ)
  have hEvalDet : (wooleySection7FallingEvalMatrix k r p).det ≠ 0 := by
    have hvand : (Matrix.vandermonde v).det ≠ 0 :=
      Matrix.det_vandermonde_ne_zero_iff.mpr
        (wooleySection7_nodes_injective_mod_prime hrk hkp)
    have heq := Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde
      v P hdeg hmonic
    change (Matrix.of (fun i j => (P j).eval (v i))).det ≠ 0
    rw [← heq]
    exact hvand
  have hDiagDet :
      (Matrix.diagonal (fun l : Fin r =>
        ((wooleySection7Node k r l + 1 : ℕ) : ZMod p))).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr
      (fun l _ => wooleySection7_node_succ_ne_zero hrk hkp l)
  intro hbin
  have hdet := congrArg
    (fun A : Matrix (Fin r) (Fin r) (ZMod p) => A.det)
    (wooleySection7_binomial_factorization k r p)
  dsimp only at hdet
  rw [Matrix.det_mul, Matrix.det_mul, hbin, zero_mul] at hdet
  exact (mul_ne_zero hDiagDet hEvalDet) hdet.symm

/-- Over the prime field, the source binomial matrix is a unit and therefore
has an actual matrix inverse. -/
theorem wooleySection7_binomialMatrix_isUnit
    {k r p : ℕ} (hp : p.Prime) (hrk : r ≤ k) (hkp : k < p) :
    IsUnit (wooleySection7BinomialMatrix k r p) := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [Matrix.isUnit_iff_isUnit_det]
  exact isUnit_iff_ne_zero.mpr
    (wooleySection7_binomialMatrix_det_ne_zero hp hrk hkp)

/-- Any integral matrix with the source congruence
`Ω_il ≡ choose (k-r+l) i (mod p)` has determinant prime to `p`.  The indices
here are zero based, hence both displayed arguments acquire `+1`. -/
theorem wooleySection7_sourceMatrix_det_mod_prime_ne_zero
    {k r p : ℕ} (hp : p.Prime) (hrk : r ≤ k) (hkp : k < p)
    (Omega : Matrix (Fin r) (Fin r) ℤ)
    (hOmega : ∀ i l,
      (Omega i l : ZMod p) =
        (Nat.choose (wooleySection7Node k r l + 1) ((i : ℕ) + 1) : ZMod p)) :
    (Omega.det : ZMod p) ≠ 0 := by
  have hmatrix : Matrix.transpose (wooleyIntMatrixMod Omega p) =
      wooleySection7BinomialMatrix k r p := by
    ext l i
    exact hOmega i l
  intro hzero
  apply wooleySection7_binomialMatrix_det_ne_zero hp hrk hkp
  rw [← hmatrix, Matrix.det_transpose, ← wooleyIntMatrixMod_det, hzero]

/-- Nonsingularity modulo `p` lifts to a unit determinant modulo every
`p^L`; this is the exact prime-power inverse assertion used after (7.10). -/
theorem wooleySection7_sourceMatrix_isUnit_primePower
    {k r p L : ℕ} (hp : p.Prime) (hrk : r ≤ k) (hkp : k < p)
    (Omega : Matrix (Fin r) (Fin r) ℤ)
    (hOmega : ∀ i l,
      (Omega i l : ZMod p) =
        (Nat.choose (wooleySection7Node k r l + 1) ((i : ℕ) + 1) : ZMod p)) :
    IsUnit (wooleyIntMatrixMod Omega (p ^ L)) := by
  have hdetp : (Omega.det : ZMod p) ≠ 0 :=
    wooleySection7_sourceMatrix_det_mod_prime_ne_zero hp hrk hkp Omega hOmega
  letI : Fact p.Prime := ⟨hp⟩
  have hunitp : IsUnit (Omega.det : ZMod p) := isUnit_iff_ne_zero.mpr hdetp
  have hcoprime : IsCoprime (p : ℤ) Omega.det :=
    (ZMod.coe_int_isUnit_iff_isCoprime Omega.det p).mp hunitp
  have hunitPow : IsUnit (Omega.det : ZMod (p ^ L)) :=
    (ZMod.coe_int_isUnit_iff_isCoprime Omega.det (p ^ L)).mpr (by
      simpa only [Int.natCast_pow] using
        hcoprime.pow_left (m := L))
  rw [Matrix.isUnit_iff_isUnit_det]
  rwa [← wooleyIntMatrixMod_det]

/-- The multiplicative inverse promised in the paper, exposed as a concrete
left inverse over `ZMod (p^L)`. -/
theorem wooleySection7_sourceMatrix_exists_leftInverse_primePower
    {k r p L : ℕ} (hp : p.Prime) (hrk : r ≤ k) (hkp : k < p)
    (Omega : Matrix (Fin r) (Fin r) ℤ)
    (hOmega : ∀ i l,
      (Omega i l : ZMod p) =
        (Nat.choose (wooleySection7Node k r l + 1) ((i : ℕ) + 1) : ZMod p)) :
    ∃ G : Matrix (Fin r) (Fin r) (ZMod (p ^ L)),
      G * wooleyIntMatrixMod Omega (p ^ L) = 1 := by
  have hunit : IsUnit (wooleyIntMatrixMod Omega (p ^ L)) :=
    wooleySection7_sourceMatrix_isUnit_primePower
      (L := L) hp hrk hkp Omega hOmega
  obtain ⟨u, hu⟩ := hunit
  refine ⟨(↑u⁻¹ : Matrix (Fin r) (Fin r) (ZMod (p ^ L))), ?_⟩
  rw [← hu]
  exact Units.inv_mul u

/-- The source equations occur as columns of `Omega`, so the actual change of
equations uses its transpose.  This exposes the inverse used in Section 7 as
a matrix rather than merely recording injectivity of its action on vectors. -/
theorem wooleySection7_sourceMatrix_transpose_exists_leftInverse_primePower
    {k r p L : ℕ} (hp : p.Prime) (hrk : r ≤ k) (hkp : k < p)
    (Omega : Matrix (Fin r) (Fin r) ℤ)
    (hOmega : ∀ i l,
      (Omega i l : ZMod p) =
        (Nat.choose (wooleySection7Node k r l + 1) ((i : ℕ) + 1) : ZMod p)) :
    ∃ G : Matrix (Fin r) (Fin r) (ZMod (p ^ L)),
      G * Matrix.transpose (wooleyIntMatrixMod Omega (p ^ L)) = 1 := by
  have hunit : IsUnit (wooleyIntMatrixMod Omega (p ^ L)) :=
    wooleySection7_sourceMatrix_isUnit_primePower
      (L := L) hp hrk hkp Omega hOmega
  have hunitT :
      IsUnit (Matrix.transpose (wooleyIntMatrixMod Omega (p ^ L))) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose,
      ← Matrix.isUnit_iff_isUnit_det]
    exact hunit
  obtain ⟨u, hu⟩ := hunitT
  refine ⟨(↑u⁻¹ : Matrix (Fin r) (Fin r) (ZMod (p ^ L))), ?_⟩
  rw [← hu]
  exact Units.inv_mul u

/-- Coordinate extraction from the source matrix modulo `p^L`. -/
theorem wooleySection7_sourceMatrix_mulVec_eq_zero_iff
    {k r p L : ℕ} (hp : p.Prime) (hrk : r ≤ k) (hkp : k < p)
    (Omega : Matrix (Fin r) (Fin r) ℤ)
    (hOmega : ∀ i l,
      (Omega i l : ZMod p) =
        (Nat.choose (wooleySection7Node k r l + 1) ((i : ℕ) + 1) : ZMod p))
    (v : Fin r → ZMod (p ^ L)) :
    (wooleyIntMatrixMod Omega (p ^ L)).mulVec v = 0 ↔ v = 0 := by
  constructor
  · intro hv
    obtain ⟨G, hG⟩ :=
      wooleySection7_sourceMatrix_exists_leftInverse_primePower
        (L := L) hp hrk hkp Omega hOmega
    calc
      v = (1 : Matrix (Fin r) (Fin r) (ZMod (p ^ L))).mulVec v :=
        (Matrix.one_mulVec v).symm
      _ = (G * wooleyIntMatrixMod Omega (p ^ L)).mulVec v := by rw [hG]
      _ = G.mulVec ((wooleyIntMatrixMod Omega (p ^ L)).mulVec v) := by
        rw [Matrix.mulVec_mulVec]
      _ = 0 := by rw [hv, Matrix.mulVec_zero]
  · rintro rfl
    exact Matrix.mulVec_zero _

/-- The source equations are columns of `Omega`, so their coefficient action
is `Omegaᵀ.mulVec`; it is injective modulo the same prime power. -/
theorem wooleySection7_sourceMatrix_transpose_mulVec_eq_zero_iff
    {k r p L : ℕ} (hp : p.Prime) (hrk : r ≤ k) (hkp : k < p)
    (Omega : Matrix (Fin r) (Fin r) ℤ)
    (hOmega : ∀ i l,
      (Omega i l : ZMod p) =
        (Nat.choose (wooleySection7Node k r l + 1) ((i : ℕ) + 1) : ZMod p))
    (v : Fin r → ZMod (p ^ L)) :
    (Matrix.transpose (wooleyIntMatrixMod Omega (p ^ L))).mulVec v = 0 ↔
      v = 0 := by
  constructor
  · intro hv
    obtain ⟨G, hG⟩ :=
      wooleySection7_sourceMatrix_transpose_exists_leftInverse_primePower
        (L := L) hp hrk hkp Omega hOmega
    calc
      v = (1 : Matrix (Fin r) (Fin r) (ZMod (p ^ L))).mulVec v :=
        (Matrix.one_mulVec v).symm
      _ = (G * Matrix.transpose
          (wooleyIntMatrixMod Omega (p ^ L))).mulVec v := by rw [hG]
      _ = G.mulVec
          ((Matrix.transpose (wooleyIntMatrixMod Omega (p ^ L))).mulVec v) := by
        rw [Matrix.mulVec_mulVec]
      _ = 0 := by rw [hv, Matrix.mulVec_zero]
  · rintro rfl
    exact Matrix.mulVec_zero _

#print axioms wooleySection7_binomial_factorization
#print axioms wooleySection7_nodes_injective_mod_prime
#print axioms wooleySection7_node_succ_ne_zero
#print axioms wooleySection7_binomialMatrix_det_ne_zero
#print axioms wooleySection7_binomialMatrix_isUnit
#print axioms wooleyIntMatrixMod_det
#print axioms wooleySection7_sourceMatrix_det_mod_prime_ne_zero
#print axioms wooleySection7_sourceMatrix_isUnit_primePower
#print axioms wooleySection7_sourceMatrix_exists_leftInverse_primePower
#print axioms wooleySection7_sourceMatrix_transpose_exists_leftInverse_primePower
#print axioms wooleySection7_sourceMatrix_mulVec_eq_zero_iff
#print axioms wooleySection7_sourceMatrix_transpose_mulVec_eq_zero_iff

end

end GafniTao
