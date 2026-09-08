import Tao2026.PowerfulRelations
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Data.Nat.Log
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.Pell
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
import RiemannZeta.GuthMaynard.DFIDivisorEpsilon

/-!
# Square relations: the split-discriminant branch of Tao's Lemma 2.10

Positive solutions to `a*n²+h=b*m²` are represented in finite boxes. When
`a*b` is a square, multiplication by `a` turns the equation into a difference
of squares. The positive factor `c*m-a*n` injects the solution set into the
divisors of `a*h`, exactly implementing the first branch of the source proof.
-/

namespace Tao2026

open Polynomial
open scoped NumberField

noncomputable def squareRelationSolutionsBox
    (a b h x y : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.Icc 1 x).product (Finset.Icc 1 y)).filter fun nm =>
    a * nm.1 ^ 2 + h = b * nm.2 ^ 2

theorem mem_squareRelationSolutionsBox
    {a b h x y : ℕ} {nm : ℕ × ℕ} :
    nm ∈ squareRelationSolutionsBox a b h x y ↔
      1 ≤ nm.1 ∧ nm.1 ≤ x ∧
      1 ≤ nm.2 ∧ nm.2 ≤ y ∧
      a * nm.1 ^ 2 + h = b * nm.2 ^ 2 := by
  classical
  simp [squareRelationSolutionsBox, and_assoc]

/-- Canonical squarefree-discriminant decomposition of the coefficient
product used in Tao's reduction to a Pell-type norm equation. -/
theorem exists_squarefree_discriminant
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    ∃ c D : ℕ, 0 < c ∧ 0 < D ∧ Squarefree D ∧
      a * b = D * c ^ 2 := by
  obtain ⟨c, hc⟩ := exists_sq_mul_squarefreeComponent (mul_pos ha hb)
  have hcPos : 0 < c := by
    have hprod : 0 < c ^ 2 * squarefreeComponent (a * b) := by
      rw [hc]
      exact mul_pos ha hb
    have hcPow : 0 < c ^ 2 := by
      rcases mul_pos_iff.mp hprod with hparts | hparts
      · exact hparts.1
      · omega
    exact (pow_pos_iff (by omega : 2 ≠ 0)).mp hcPow
  have hDPos : 0 < squarefreeComponent (a * b) := by
    have hprod : 0 < c ^ 2 * squarefreeComponent (a * b) := by
      rw [hc]
      exact mul_pos ha hb
    rcases mul_pos_iff.mp hprod with hparts | hparts
    · exact hparts.2
    · omega
  exact ⟨c, squarefreeComponent (a * b), hcPos, hDPos,
    squarefree_squarefreeComponent _, hc.symm.trans (mul_comm _ _)⟩

/-- Algebraic bridge for the nonsquare-discriminant branch of Lemma 2.10.
If `a*b=D*c²`, then a square relation becomes the integral norm equation
`(b*m)²-D*(c*n)²=b*h`. -/
theorem squareRelation_norm_equation
    {a b c D h n m : ℕ} (hdisc : a * b = D * c ^ 2)
    (heq : a * n ^ 2 + h = b * m ^ 2) :
    (((b * m : ℕ) : ℤ) ^ 2 -
        (D : ℤ) * (((c * n : ℕ) : ℤ) ^ 2)) =
      ((b * h : ℕ) : ℤ) := by
  change ((b : ℤ) * m) ^ 2 -
      (D : ℤ) * (((c : ℤ) * n) ^ 2) = (b : ℤ) * h
  have hdiscZ : (a : ℤ) * b = D * c ^ 2 := by exact_mod_cast hdisc
  have heqZ : (a : ℤ) * n ^ 2 + h = b * m ^ 2 := by exact_mod_cast heq
  have hdiffZ : (b : ℤ) * m ^ 2 - a * n ^ 2 = h := by
    linarith
  calc
    ((b : ℤ) * m) ^ 2 - D * ((c : ℤ) * n) ^ 2 =
        (b : ℤ) * ((b : ℤ) * (m : ℤ) ^ 2) -
          ((D : ℤ) * (c : ℤ) ^ 2) * (n : ℤ) ^ 2 := by ring
    _ = (b : ℤ) * ((b : ℤ) * (m : ℤ) ^ 2) -
        ((a : ℤ) * (b : ℤ)) * (n : ℤ) ^ 2 := by rw [← hdiscZ]
    _ = (b : ℤ) *
        ((b : ℤ) * (m : ℤ) ^ 2 - (a : ℤ) * (n : ℤ) ^ 2) := by ring
    _ = (b : ℤ) * (h : ℤ) := by rw [hdiffZ]

/-- The literal `bm+cn√D` element occurring on the left side of Tao's
norm factorization.  This lives in the quadratic order `ℤ[√D]`, which embeds
in the maximal order used later in the source's ideal-orbit argument. -/
def squareRelationNormPoint (b c D n m : ℕ) : ℤ√(D : ℤ) :=
  ⟨((b * m : ℕ) : ℤ), ((c * n : ℕ) : ℤ)⟩

@[simp]
theorem squareRelationNormPoint_re (b c D n m : ℕ) :
    (squareRelationNormPoint b c D n m).re = ((b * m : ℕ) : ℤ) :=
  rfl

@[simp]
theorem squareRelationNormPoint_im (b c D n m : ℕ) :
    (squareRelationNormPoint b c D n m).im = ((c * n : ℕ) : ℤ) :=
  rfl

/-- The rearranged square relation is exactly the norm equation for the
literal quadratic-order point `bm+cn√D`. -/
theorem squareRelationNormPoint_norm
    {a b c D h n m : ℕ} (hdisc : a * b = D * c ^ 2)
    (heq : a * n ^ 2 + h = b * m ^ 2) :
    (squareRelationNormPoint b c D n m).norm = ((b * h : ℕ) : ℤ) := by
  have hnorm := squareRelation_norm_equation hdisc heq
  rw [Zsqrtd.norm_def]
  simp only [squareRelationNormPoint_re, squareRelationNormPoint_im]
  ring_nf at hnorm ⊢
  exact hnorm

/-- The fixed-norm fiber in the integral quadratic order `ℤ[√D]`.  It is an
exact intermediate object for the nonsquare branch; it is deliberately not
identified with the maximal order of `ℚ(√D)`. -/
def zsqrtdNormFiber (D N : ℤ) :=
  {z : ℤ√D // z.norm = N}

/-- A norm-one Pell solution has norm one as an element of `ℤ[√D]`. -/
theorem norm_coe_pellSolution {D : ℤ} (u : Pell.Solution₁ D) :
    (u : ℤ√D).norm = 1 := by
  rw [Zsqrtd.norm_def]
  change u.x * u.x - D * u.y * u.y = 1
  have hu := u.prop
  ring_nf at hu ⊢
  exact hu

/-- Multiplication by a norm-one Pell solution preserves every fixed-norm
fiber.  This is the exact unit action underlying the orbit part of Tao's
proof, before passage to the maximal order and ideal classes. -/
def pellActOnNormFiber {D N : ℤ} (u : Pell.Solution₁ D)
    (z : zsqrtdNormFiber D N) : zsqrtdNormFiber D N :=
  ⟨(u : ℤ√D) * z.1, by
    rw [Zsqrtd.norm_mul, norm_coe_pellSolution, one_mul, z.2]⟩

@[simp]
theorem pellActOnNormFiber_one {D N : ℤ} (z : zsqrtdNormFiber D N) :
    pellActOnNormFiber (1 : Pell.Solution₁ D) z = z := by
  apply Subtype.ext
  exact one_mul z.1

@[simp]
theorem pellActOnNormFiber_mul {D N : ℤ} (u v : Pell.Solution₁ D)
    (z : zsqrtdNormFiber D N) :
    pellActOnNormFiber (u * v) z =
      pellActOnNormFiber u (pellActOnNormFiber v z) := by
  apply Subtype.ext
  exact mul_assoc (u : ℤ√D) (v : ℤ√D) z.1

instance instMulActionPellSolutionZsqrtdNormFiber (D N : ℤ) :
    MulAction (Pell.Solution₁ D) (zsqrtdNormFiber D N) where
  smul := pellActOnNormFiber
  one_smul := pellActOnNormFiber_one
  mul_smul := pellActOnNormFiber_mul

/-- The orbit of a fixed-norm quadratic-order point under norm-one Pell
solutions.  The later ideal-divisor estimate must bound the number of these
orbits after comparing this order with the maximal order. -/
def zsqrtdNormOrbit {D N : ℤ} (z : zsqrtdNormFiber D N) :
    Set (zsqrtdNormFiber D N) :=
  MulAction.orbit (Pell.Solution₁ D) z

theorem mem_zsqrtdNormOrbit_iff {D N : ℤ} {z w : zsqrtdNormFiber D N} :
    w ∈ zsqrtdNormOrbit z ↔
      ∃ u : Pell.Solution₁ D, pellActOnNormFiber u z = w := by
  exact MulAction.mem_orbit_iff

/-- Natural powers of a fundamental Pell solution grow at least as fast as
`2^n` in their positive real coordinate.  This is the first quantitative
ingredient in the source's logarithmic bounded-height orbit count. -/
theorem two_pow_le_fundamental_x_pow {D : ℤ} {u : Pell.Solution₁ D}
    (hu : Pell.IsFundamental u) (n : ℕ) :
    (((2 : ℕ) ^ n : ℕ) : ℤ) ≤ (u ^ n).x := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hxPos : 0 < (u ^ n).x :=
        Pell.Solution₁.x_pow_pos hu.x_pos n
      have hyNonneg : 0 ≤ (u ^ n).y := by
        cases n with
        | zero => simp
        | succ k =>
            exact (Pell.Solution₁.y_pow_succ_pos hu.x_pos hu.2.1 k).le
      rw [show u ^ (n + 1) = u ^ n * u by exact pow_succ u n,
        Pell.Solution₁.x_mul]
      calc
        (((2 : ℕ) ^ (n + 1) : ℕ) : ℤ) =
            (((2 : ℕ) ^ n : ℕ) : ℤ) * 2 := by
          rw [pow_succ]
          norm_num
        _ ≤ (u ^ n).x * u.x := by
          have huOne : (1 : ℤ) < u.x := hu.1
          have huTwo : (2 : ℤ) ≤ u.x := by omega
          exact mul_le_mul ih huTwo (by norm_num) hxPos.le
        _ ≤ (u ^ n).x * u.x + D * ((u ^ n).y * u.y) := by
          exact le_add_of_nonneg_right
            (mul_nonneg hu.d_pos.le (mul_nonneg hyNonneg hu.2.1.le))

/-- Hence a nonnegative exponent whose fundamental-unit power has bounded
`x`-coordinate is at most the base-two logarithm of that bound. -/
theorem fundamental_exponent_le_log_two_of_x_pow_le
    {D : ℤ} {u : Pell.Solution₁ D} (hu : Pell.IsFundamental u)
    {n B : ℕ} (hB : (u ^ n).x.natAbs ≤ B) :
    n ≤ Nat.log 2 B := by
  have hxPos : 0 < (u ^ n).x := Pell.Solution₁.x_pow_pos hu.x_pos n
  have hpowInt := two_pow_le_fundamental_x_pow hu n
  have hpowNat : (2 : ℕ) ^ n ≤ (u ^ n).x.natAbs := by
    rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs,
      abs_of_nonneg hxPos.le]
    exact_mod_cast hpowInt
  exact Nat.le_log_of_pow_le (by norm_num) (hpowNat.trans hB)

theorem fundamental_x_zpow_eq_x_pow_natAbs
    {D : ℤ} (u : Pell.Solution₁ D) (j : ℤ) :
    (u ^ j).x = (u ^ j.natAbs).x := by
  cases j with
  | ofNat n => simp [Int.ofNat_eq_natCast, zpow_natCast]
  | negSucc n => simp [zpow_negSucc]

/-- The exponential lower bound is symmetric in positive and negative unit
powers, because inversion changes only the sign of the `y`-coordinate. -/
theorem two_pow_natAbs_le_fundamental_x_zpow
    {D : ℤ} {u : Pell.Solution₁ D} (hu : Pell.IsFundamental u) (j : ℤ) :
    (((2 : ℕ) ^ j.natAbs : ℕ) : ℤ) ≤ (u ^ j).x := by
  rw [fundamental_x_zpow_eq_x_pow_natAbs]
  exact two_pow_le_fundamental_x_pow hu j.natAbs

/-- The explicit finite interval of exponents that can support a bounded
fundamental-unit power. -/
noncomputable def fundamentalExponentsUpTo (B : ℕ) : Finset ℤ :=
  Finset.Icc (-(Nat.log 2 B : ℤ)) (Nat.log 2 B : ℤ)

theorem mem_fundamentalExponentsUpTo_iff {B : ℕ} {j : ℤ} :
    j ∈ fundamentalExponentsUpTo B ↔
      -(Nat.log 2 B : ℤ) ≤ j ∧ j ≤ (Nat.log 2 B : ℤ) := by
  simp [fundamentalExponentsUpTo]

theorem mem_fundamentalExponentsUpTo_of_x_zpow_le
    {D : ℤ} {u : Pell.Solution₁ D} (hu : Pell.IsFundamental u)
    {j : ℤ} {B : ℕ} (hB : (u ^ j).x.natAbs ≤ B) :
    j ∈ fundamentalExponentsUpTo B := by
  have hxPos : 0 < (u ^ j).x := Pell.Solution₁.x_zpow_pos hu.x_pos j
  have hpowInt := two_pow_natAbs_le_fundamental_x_zpow hu j
  have hpowNat : (2 : ℕ) ^ j.natAbs ≤ (u ^ j).x.natAbs := by
    rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs,
      abs_of_nonneg hxPos.le]
    exact_mod_cast hpowInt
  have hjLog : j.natAbs ≤ Nat.log 2 B :=
    Nat.le_log_of_pow_le (by norm_num) (hpowNat.trans hB)
  rw [mem_fundamentalExponentsUpTo_iff]
  have habs : |j| ≤ (Nat.log 2 B : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hjLog
  exact abs_le.mp habs

theorem card_fundamentalExponentsUpTo (B : ℕ) :
    (fundamentalExponentsUpTo B).card = 2 * Nat.log 2 B + 1 := by
  rw [fundamentalExponentsUpTo, Int.card_Icc]
  simp
  omega

theorem fundamental_zpow_injective
    {D : ℤ} {u : Pell.Solution₁ D} (hu : Pell.IsFundamental u) :
    Function.Injective fun j : ℤ => u ^ j := by
  intro j k hjk
  exact hu.y_strictMono.injective
    (congr_arg Pell.Solution₁.y hjk)

/-- The actual finite family of powers allowed by the explicit coordinate
bound. -/
noncomputable def fundamentalUnitPowersUpTo
    {D : ℤ} (u : Pell.Solution₁ D) (B : ℕ) : Finset (Pell.Solution₁ D) := by
  classical
  exact (fundamentalExponentsUpTo B).image fun j => u ^ j

theorem fundamental_zpow_mem_powersUpTo_of_x_le
    {D : ℤ} {u : Pell.Solution₁ D} (hu : Pell.IsFundamental u)
    {j : ℤ} {B : ℕ} (hB : (u ^ j).x.natAbs ≤ B) :
    u ^ j ∈ fundamentalUnitPowersUpTo u B := by
  classical
  rw [fundamentalUnitPowersUpTo, Finset.mem_image]
  exact ⟨j, mem_fundamentalExponentsUpTo_of_x_zpow_le hu hB, rfl⟩

/-- There are exactly `2*log₂(B)+1` candidate fundamental-unit powers after
imposing the coordinate bound. -/
theorem card_fundamentalUnitPowersUpTo
    {D : ℤ} {u : Pell.Solution₁ D} (hu : Pell.IsFundamental u) (B : ℕ) :
    (fundamentalUnitPowersUpTo u B).card = 2 * Nat.log 2 B + 1 := by
  classical
  rw [fundamentalUnitPowersUpTo,
    Finset.card_image_iff.mpr (fundamental_zpow_injective hu).injOn,
    card_fundamentalExponentsUpTo]

/-- A squarefree natural discriminant greater than one is not a square after
casting to the integers. -/
theorem not_isSquare_intCast_of_squarefree_of_one_lt
    {D : ℕ} (hD : Squarefree D) (hDgt : 1 < D) :
    ¬IsSquare (D : ℤ) := by
  rw [Int.isSquare_natCast_iff]
  intro hsq
  obtain ⟨r, hr⟩ := hsq.exists_sq
  have hrNe : r ≠ 1 := by
    intro hrOne
    subst r
    simp at hr hDgt
    omega
  have hpowSquarefree : Squarefree (r ^ 2) := by
    rwa [← hr]
  have hexponent :=
    (Nat.squarefree_pow_iff hrNe (by norm_num : (2 : ℕ) ≠ 0)).mp
      hpowSquarefree
  omega

/-- Thus the nonsquare discriminants produced by Tao's reduction possess a
fundamental positive Pell solution in the pinned Mathlib development. -/
theorem exists_fundamental_pell_solution_of_squarefree_of_one_lt
    {D : ℕ} (hD : Squarefree D) (hDgt : 1 < D) :
    ∃ u : Pell.Solution₁ (D : ℤ), Pell.IsFundamental u := by
  exact Pell.IsFundamental.exists_of_not_isSquare
    (by exact_mod_cast (zero_lt_one.trans hDgt))
    (not_isSquare_intCast_of_squarefree_of_one_lt hD hDgt)

@[reducible] def zsqrtdNonsquareOfSquarefreeOfOneLt
    {D : ℕ} (hD : Squarefree D) (hDgt : 1 < D) : Zsqrtd.Nonsquare D where
  ns n hDn := by
    apply not_isSquare_intCast_of_squarefree_of_one_lt hD hDgt
    rw [isSquare_iff_exists_sq]
    have hNat : D = n ^ 2 := by simpa [pow_two] using hDn
    exact ⟨(n : ℤ), by exact_mod_cast hNat⟩

/-! ## The quadratic number field and its maximal order -/

/-- The defining polynomial `X²-D` for the concrete quadratic number field
used in the nonsquare branch of Tao's Lemma 2.10. -/
noncomputable def quadraticPolynomial (D : ℕ) : ℚ[X] :=
  X ^ 2 - C (D : ℚ)

theorem quadraticPolynomial_monic (D : ℕ) :
    (quadraticPolynomial D).Monic := by
  simpa [quadraticPolynomial] using
    (monic_X_pow_sub_C (D : ℚ) (n := 2) (by norm_num : (2 : ℕ) ≠ 0))

theorem quadraticPolynomial_natDegree (D : ℕ) :
    (quadraticPolynomial D).natDegree = 2 := by
  rw [quadraticPolynomial]
  exact natDegree_X_pow_sub_C

/-- If `D` is not a natural square, then `X²-D` has no rational root. -/
theorem quadraticPolynomial_not_isRoot_of_not_isSquare
    {D : ℕ} (hD : ¬ IsSquare D) (q : ℚ) :
    ¬ IsRoot (quadraticPolynomial D) q := by
  intro hroot
  have hsqQ : IsSquare (D : ℚ) := by
    refine ⟨q, ?_⟩
    simp [quadraticPolynomial, IsRoot.def] at hroot
    linarith
  exact hD (Rat.isSquare_natCast_iff.mp hsqQ)

/-- The defining polynomial of the concrete quadratic field is irreducible
for every nonsquare natural discriminant. -/
theorem quadraticPolynomial_irreducible_of_not_isSquare
    {D : ℕ} (hD : ¬ IsSquare D) :
    Irreducible (quadraticPolynomial D) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · simp [quadraticPolynomial_natDegree]
  · exact quadraticPolynomial_not_isRoot_of_not_isSquare hD

/-- The concrete field `ℚ(√D)`, constructed as `ℚ[X]/(X²-D)`. -/
abbrev quadraticField (D : ℕ) :=
  AdjoinRoot (quadraticPolynomial D)

noncomputable instance quadraticFieldFactIrreducible
    (D : ℕ) [hD : Fact (¬ IsSquare D)] :
    Fact (Irreducible (quadraticPolynomial D)) :=
  ⟨quadraticPolynomial_irreducible_of_not_isSquare hD.out⟩

noncomputable instance quadraticFieldNumberField
    (D : ℕ) [Fact (¬ IsSquare D)] : NumberField (quadraticField D) :=
  inferInstance

/-- The concrete field `ℚ(√D)` has degree exactly two over `ℚ`. -/
noncomputable instance quadraticFieldIsQuadraticExtension
    (D : ℕ) [Fact (¬ IsSquare D)] :
    Algebra.IsQuadraticExtension ℚ (quadraticField D) where
  toFree := Module.Free.of_basis
    (AdjoinRoot.powerBasis
      (quadraticPolynomial_irreducible_of_not_isSquare
        (Fact.out : ¬ IsSquare D)).ne_zero).basis
  finrank_eq_two' := by
    rw [(AdjoinRoot.powerBasis
      (quadraticPolynomial_irreducible_of_not_isSquare
        (Fact.out : ¬ IsSquare D)).ne_zero).finrank]
    exact quadraticPolynomial_natDegree D

/-- The distinguished square root of `D` in the concrete quadratic field. -/
noncomputable def quadraticSqrt (D : ℕ) [Fact (¬ IsSquare D)] :
    quadraticField D :=
  AdjoinRoot.root (quadraticPolynomial D)

theorem quadraticSqrt_sq (D : ℕ) [Fact (¬ IsSquare D)] :
    quadraticSqrt D * quadraticSqrt D =
      algebraMap ℚ (quadraticField D) (D : ℚ) := by
  rw [← sub_eq_zero]
  change AdjoinRoot.mk (quadraticPolynomial D) X *
      AdjoinRoot.mk (quadraticPolynomial D) X -
      AdjoinRoot.mk (quadraticPolynomial D) (C (D : ℚ)) = 0
  rw [← map_mul, ← map_sub]
  simpa [quadraticPolynomial, pow_two] using
    (AdjoinRoot.mk_self (f := quadraticPolynomial D))

/-- The monic integral polynomial witnessing that the distinguished square
root belongs to the maximal order. -/
noncomputable def quadraticIntegerPolynomial (D : ℕ) : ℤ[X] :=
  X ^ 2 - C (D : ℤ)

theorem quadraticIntegerPolynomial_monic (D : ℕ) :
    (quadraticIntegerPolynomial D).Monic := by
  simpa [quadraticIntegerPolynomial] using
    (monic_X_pow_sub_C (D : ℤ) (n := 2) (by norm_num : (2 : ℕ) ≠ 0))

theorem quadraticSqrt_isIntegral (D : ℕ) [Fact (¬ IsSquare D)] :
    IsIntegral ℤ (quadraticSqrt D) := by
  refine ⟨quadraticIntegerPolynomial D, quadraticIntegerPolynomial_monic D, ?_⟩
  simpa [quadraticIntegerPolynomial, pow_two] using
    sub_eq_zero.mpr (quadraticSqrt_sq D)

/-- The distinguished square root as an element of the actual ring of
integers `𝓞(ℚ(√D))`. -/
noncomputable def quadraticSqrtRingOfIntegers
    (D : ℕ) [Fact (¬ IsSquare D)] : 𝓞 (quadraticField D) :=
  ⟨quadraticSqrt D, quadraticSqrt_isIntegral D⟩

theorem quadraticSqrtRingOfIntegers_sq
    (D : ℕ) [Fact (¬ IsSquare D)] :
    quadraticSqrtRingOfIntegers D * quadraticSqrtRingOfIntegers D =
      (D : 𝓞 (quadraticField D)) := by
  apply NumberField.RingOfIntegers.coe_injective
  simp [quadraticSqrtRingOfIntegers, quadraticSqrt_sq]

/-- The canonical inclusion of the quadratic order `ℤ[√D]` into the
maximal order of `ℚ(√D)`. -/
noncomputable def quadraticOrderToRingOfIntegers
    (D : ℕ) [Fact (¬ IsSquare D)] :
    ℤ√(D : ℤ) →+* 𝓞 (quadraticField D) :=
  Zsqrtd.lift ⟨quadraticSqrtRingOfIntegers D,
    quadraticSqrtRingOfIntegers_sq D⟩

/-- For nonsquare `D`, the canonical map from `ℤ[√D]` into the maximal
order is injective.  Thus the earlier norm-point encoding survives passage
to Tao's ring of integers without loss. -/
theorem quadraticOrderToRingOfIntegers_injective
    (D : ℕ) [Fact (¬ IsSquare D)] :
    Function.Injective (quadraticOrderToRingOfIntegers D) := by
  apply Zsqrtd.lift_injective
  intro n hDn
  apply (Fact.out : ¬ IsSquare D)
  rw [isSquare_iff_exists_sq]
  refine ⟨n.natAbs, ?_⟩
  have hDn' : (D : ℤ) = n ^ 2 := by simpa [pow_two] using hDn
  apply Int.ofNat_inj.mp
  calc
    (D : ℤ) = n ^ 2 := hDn'
    _ = (n.natAbs : ℤ) ^ 2 := (Int.natAbs_sq n).symm
    _ = ((n.natAbs ^ 2 : ℕ) : ℤ) := by norm_num

/-- Multiplying a quadratic-order point by its conjugate after embedding in
the maximal order gives its original integral norm. -/
theorem quadraticOrderToRingOfIntegers_mul_conj
    (D : ℕ) [Fact (¬ IsSquare D)] (z : ℤ√(D : ℤ)) :
    quadraticOrderToRingOfIntegers D z *
        quadraticOrderToRingOfIntegers D (star z) =
      (z.norm : 𝓞 (quadraticField D)) := by
  rw [← map_mul, ← Zsqrtd.norm_eq_mul_conj]
  exact map_intCast _ _

/-- A fixed-norm point determines a divisor of `(N)` in the actual maximal
order, using its embedded conjugate as the complementary ideal factor. -/
noncomputable def maximalOrderNormFiberIdealDivisor
    {D : ℕ} [Fact (¬ IsSquare D)] {N : ℤ}
    (z : zsqrtdNormFiber (D : ℤ) N) :
    {I : Ideal (𝓞 (quadraticField D)) //
      I ∣ Ideal.span ({(N : 𝓞 (quadraticField D))} :
        Set (𝓞 (quadraticField D)))} := by
  refine ⟨Ideal.span ({quadraticOrderToRingOfIntegers D z.1} :
      Set (𝓞 (quadraticField D))), ?_⟩
  refine ⟨Ideal.span ({quadraticOrderToRingOfIntegers D (star z.1)} :
      Set (𝓞 (quadraticField D))), ?_⟩
  rw [Ideal.span_singleton_mul_span_singleton,
    quadraticOrderToRingOfIntegers_mul_conj, z.2]

/-- Fibers of the maximal-order ideal-divisor map are exactly association
classes, hence exactly orbits under multiplication by units of the maximal
order.  This is the source's orbit reduction in the correct ambient ring. -/
theorem maximalOrderNormFiberIdealDivisor_eq_iff_associated
    {D : ℕ} [Fact (¬ IsSquare D)] {N : ℤ}
    {z w : zsqrtdNormFiber (D : ℤ) N} :
    maximalOrderNormFiberIdealDivisor z =
        maximalOrderNormFiberIdealDivisor w ↔
      Associated (quadraticOrderToRingOfIntegers D z.1)
        (quadraticOrderToRingOfIntegers D w.1) := by
  rw [Subtype.ext_iff]
  exact Ideal.span_singleton_eq_span_singleton

/-- The finite set of ideal divisors of `(N)` in the maximal order.  Its
finiteness is supplied by unique factorization of nonzero ideals in a
Dedekind domain; the remaining source estimate refines its cardinality to
at most `d(|N|)²`. -/
noncomputable def maximalOrderIdealDivisors
    (D : ℕ) [Fact (¬ IsSquare D)] (N : ℤ) (hN : N ≠ 0) :
    Finset {I : Ideal (𝓞 (quadraticField D)) //
      I ∣ Ideal.span ({(N : 𝓞 (quadraticField D))} :
        Set (𝓞 (quadraticField D)))} := by
  classical
  let J : Ideal (𝓞 (quadraticField D)) :=
    Ideal.span ({(N : 𝓞 (quadraticField D))} :
      Set (𝓞 (quadraticField D)))
  have hJ : J ≠ 0 := by
    change Ideal.span ({(N : 𝓞 (quadraticField D))} :
      Set (𝓞 (quadraticField D))) ≠ 0
    rw [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact Int.cast_ne_zero.mpr hN
  letI := UniqueFactorizationMonoid.fintypeSubtypeDvd J hJ
  exact Finset.univ

theorem mem_maximalOrderIdealDivisors
    {D : ℕ} [Fact (¬ IsSquare D)] {N : ℤ} (hN : N ≠ 0)
    (I : {J : Ideal (𝓞 (quadraticField D)) //
      J ∣ Ideal.span ({(N : 𝓞 (quadraticField D))} :
        Set (𝓞 (quadraticField D)))}) :
    I ∈ maximalOrderIdealDivisors D N hN := by
  simp [maximalOrderIdealDivisors]

theorem maximalOrderNormFiberIdealDivisor_mem
    {D : ℕ} [Fact (¬ IsSquare D)] {N : ℤ} (hN : N ≠ 0)
    (z : zsqrtdNormFiber (D : ℤ) N) :
    maximalOrderNormFiberIdealDivisor z ∈
      maximalOrderIdealDivisors D N hN :=
  mem_maximalOrderIdealDivisors hN _

/-- The Galois group of the concrete quadratic field has order two. -/
theorem quadraticField_galoisGroup_card
    (D : ℕ) [Fact (¬ IsSquare D)] :
    Nat.card Gal(quadraticField D / ℚ) = 2 := by
  rw [IsGalois.card_aut_eq_finrank,
    Algebra.IsQuadraticExtension.finrank_eq_two]

/-- On a nonzero fixed-norm fiber, two quadratic-order elements generate the
same principal ideal exactly when they lie in the same norm-one Pell orbit.
This is the principal-ideal orbit invariant used in the source argument. -/
theorem span_singleton_eq_iff_mem_zsqrtdNormOrbit
    {D : ℕ} [Zsqrtd.Nonsquare D] {N : ℤ} (hN : N ≠ 0)
    {z w : zsqrtdNormFiber (D : ℤ) N} :
    Ideal.span ({z.1} : Set (ℤ√(D : ℤ))) =
        Ideal.span ({w.1} : Set (ℤ√(D : ℤ))) ↔
      w ∈ zsqrtdNormOrbit z := by
  constructor
  · intro hspan
    have hassoc : Associated z.1 w.1 :=
      Ideal.span_singleton_eq_span_singleton.mp hspan
    rcases hassoc with ⟨q, hq⟩
    have hnormq : ((q : (ℤ√(D : ℤ))ˣ) : ℤ√(D : ℤ)).norm = 1 := by
      have hnorm := congr_arg Zsqrtd.norm hq
      rw [Zsqrtd.norm_mul, z.2, w.2] at hnorm
      apply mul_left_cancel₀ hN
      simpa using hnorm
    let u : Pell.Solution₁ (D : ℤ) :=
      ⟨(q : ℤ√(D : ℤ)), Zsqrtd.norm_eq_one_iff_mem_unitary.mp hnormq⟩
    rw [mem_zsqrtdNormOrbit_iff]
    refine ⟨u, ?_⟩
    apply Subtype.ext
    change (q : ℤ√(D : ℤ)) * z.1 = w.1
    simpa [mul_comm] using hq
  · intro horbit
    rw [mem_zsqrtdNormOrbit_iff] at horbit
    rcases horbit with ⟨u, hu⟩
    apply Ideal.span_singleton_eq_span_singleton.mpr
    have huUnit : IsUnit (u : ℤ√(D : ℤ)) :=
      Zsqrtd.norm_eq_one_iff.mp (by
        rw [norm_coe_pellSolution]
        norm_num)
    rcases huUnit with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    have huPoint := congr_arg Subtype.val hu
    change (u : ℤ√(D : ℤ)) * z.1 = w.1 at huPoint
    calc
      z.1 * (q : ℤ√(D : ℤ)) = z.1 * (u : ℤ√(D : ℤ)) := by rw [hq]
      _ = (u : ℤ√(D : ℤ)) * z.1 := mul_comm _ _
      _ = w.1 := huPoint

/-- Squarefree-discriminant specialization of the principal-ideal orbit
classification, with the nonsquare order instance built from the source
hypotheses. -/
theorem span_singleton_eq_iff_mem_zsqrtdNormOrbit_of_squarefree
    {D : ℕ} (hD : Squarefree D) (hDgt : 1 < D)
    {N : ℤ} (hN : N ≠ 0) {z w : zsqrtdNormFiber (D : ℤ) N} :
    Ideal.span ({z.1} : Set (ℤ√(D : ℤ))) =
        Ideal.span ({w.1} : Set (ℤ√(D : ℤ))) ↔
      w ∈ zsqrtdNormOrbit z := by
  letI := zsqrtdNonsquareOfSquarefreeOfOneLt hD hDgt
  exact span_singleton_eq_iff_mem_zsqrtdNormOrbit hN

/-- The principal ideal generated by a fixed-norm point divides the principal
ideal generated by its norm: `(z) (conj z) = (N)`. -/
theorem span_singleton_dvd_span_norm
    {D : ℕ} [Zsqrtd.Nonsquare D] {N : ℤ}
    (z : zsqrtdNormFiber (D : ℤ) N) :
    Ideal.span ({z.1} : Set (ℤ√(D : ℤ))) ∣
      Ideal.span ({(N : ℤ√(D : ℤ))} : Set (ℤ√(D : ℤ))) := by
  refine ⟨Ideal.span ({star z.1} : Set (ℤ√(D : ℤ))), ?_⟩
  rw [Ideal.span_singleton_mul_span_singleton,
    ← Zsqrtd.norm_eq_mul_conj, z.2]

/-- A fixed-norm point, represented by the ideal divisor of `(N)` that it
generates. -/
def normFiberPrincipalIdealDivisor
    {D : ℕ} [Zsqrtd.Nonsquare D] {N : ℤ}
    (z : zsqrtdNormFiber (D : ℤ) N) :
    {I : Ideal (ℤ√(D : ℤ)) //
      I ∣ Ideal.span ({(N : ℤ√(D : ℤ))} : Set (ℤ√(D : ℤ)))} :=
  ⟨Ideal.span ({z.1} : Set (ℤ√(D : ℤ))), span_singleton_dvd_span_norm z⟩

/-- For nonzero norm, the ideal-divisor representation has exactly the Pell
orbits as its fibers. -/
theorem normFiberPrincipalIdealDivisor_eq_iff_orbit
    {D : ℕ} [Zsqrtd.Nonsquare D] {N : ℤ} (hN : N ≠ 0)
    {z w : zsqrtdNormFiber (D : ℤ) N} :
    normFiberPrincipalIdealDivisor z = normFiberPrincipalIdealDivisor w ↔
      w ∈ zsqrtdNormOrbit z := by
  rw [Subtype.ext_iff]
  exact span_singleton_eq_iff_mem_zsqrtdNormOrbit hN

/-- In a Dedekind Galois extension with Galois group of order two, every
nonzero prime has at most two primes above it.  This is the exact abstract
splitting bound used in Tao's ideal-divisor estimate. -/
theorem ncard_primesOver_le_two_of_galois_group_card_two
    {A : Type*} [CommRing A] [IsDedekindDomain A]
    {p : Ideal A} (hp : p ≠ ⊥) [p.IsMaximal]
    (B : Type*) [CommRing B] [IsDedekindDomain B] [Algebra A B]
    [Module.Finite A B]
    [Module.IsTorsionFree A B]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B] (hG : Nat.card G = 2) :
    (Ideal.primesOver p B).ncard ≤ 2 := by
  have hfund :=
    Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn hp B G
  rw [hG] at hfund
  exact Nat.le_of_dvd (by norm_num)
    ⟨Ideal.ramificationIdxIn p B * Ideal.inertiaDegIn p B, hfund.symm⟩

/-- Concrete maximal-order specialization: every nonzero rational prime has
at most two primes above it in `𝓞(ℚ(√D))`.  This instantiates the
prime-splitting input in Tao's divisor-of-an-ideal count, rather than leaving
the number field or maximal order abstract. -/
theorem quadraticField_ncard_primesOver_le_two
    (D : ℕ) [Fact (¬ IsSquare D)]
    {p : Ideal ℤ} (hp : p ≠ ⊥) [p.IsMaximal] :
    (Ideal.primesOver p (𝓞 (quadraticField D))).ncard ≤ 2 := by
  letI : IsScalarTower ℤ (𝓞 (quadraticField D))
      (quadraticField D) := by
    apply IsScalarTower.of_algebraMap_smul
    intro z x
    simp [Algebra.smul_def]
  letI : IsScalarTower ℤ ℚ (quadraticField D) := by
    apply IsScalarTower.of_algebraMap_smul
    intro z x
    simp [Algebra.smul_def]
  letI : IsGaloisGroup Gal(quadraticField D / ℚ) ℤ
      (𝓞 (quadraticField D)) := {
    faithful := by
      constructor
      intro g h gh
      have hField :=
        (inferInstance : IsGaloisGroup Gal(quadraticField D / ℚ)
          ℚ (quadraticField D))
      apply hField.faithful.eq_of_smul_eq_smul
      intro y
      obtain ⟨a, b, hb, rfl⟩ :=
        IsFractionRing.div_surjective (𝓞 (quadraticField D)) y
      simp only [smul_div₀', ← algebraMap.coe_smul', gh]
    commutes := inferInstance
    isInvariant := by
      constructor
      intro x hx
      have hField :=
        (inferInstance : IsGaloisGroup Gal(quadraticField D / ℚ)
          ℚ (quadraticField D))
      obtain ⟨q, hq⟩ :=
        hField.isInvariant.isInvariant
          (algebraMap (𝓞 (quadraticField D)) (quadraticField D) x) (by
            intro g
            rw [← algebraMap.coe_smul', hx g])
      have hxInt : IsIntegral ℤ
          (algebraMap (𝓞 (quadraticField D)) (quadraticField D) x) := x.2
      rw [← hq, isIntegral_algebraMap_iff
        (algebraMap ℚ (quadraticField D)).injective,
        IsIntegrallyClosedIn.isIntegral_iff] at hxInt
      obtain ⟨z, rfl⟩ := hxInt
      refine ⟨z, ?_⟩
      apply NumberField.RingOfIntegers.coe_injective
      simpa only [IsScalarTower.algebraMap_apply] using hq
  }
  exact ncard_primesOver_le_two_of_galois_group_card_two hp
    (𝓞 (quadraticField D)) Gal(quadraticField D / ℚ)
      (quadraticField_galoisGroup_card D)

/-- A square-relation solution supplies an element of the appropriate
fixed-norm fiber. -/
def squareRelationNormFiberPoint
    {a b c D h n m : ℕ} (hdisc : a * b = D * c ^ 2)
    (heq : a * n ^ 2 + h = b * m ^ 2) :
    zsqrtdNormFiber (D : ℤ) ((b * h : ℕ) : ℤ) :=
  ⟨squareRelationNormPoint b c D n m,
    squareRelationNormPoint_norm hdisc heq⟩

/-- With nonzero coefficients, the quadratic-order encoding loses no
information about a positive square-relation solution. -/
theorem squareRelationNormPoint_injective {b c D : ℕ}
    (hb : 0 < b) (hc : 0 < c) :
    Function.Injective fun nm : ℕ × ℕ =>
      squareRelationNormPoint b c D nm.1 nm.2 := by
  rintro ⟨n₁, m₁⟩ ⟨n₂, m₂⟩ hpoint
  have hre := congr_arg Zsqrtd.re hpoint
  have him := congr_arg Zsqrtd.im hpoint
  simp only [squareRelationNormPoint_re] at hre
  simp only [squareRelationNormPoint_im] at him
  have hbm : b * m₁ = b * m₂ := by exact_mod_cast hre
  have hcn : c * n₁ = c * n₂ := by exact_mod_cast him
  exact Prod.ext (Nat.mul_left_cancel hc hcn) (Nat.mul_left_cancel hb hbm)

/-- With nonzero coefficients, encoding a natural solution in the maximal
order remains injective. -/
theorem maximalOrderNormPoint_injective
    {b c D : ℕ} [Fact (¬ IsSquare D)] (hb : 0 < b) (hc : 0 < c) :
    Function.Injective fun nm : ℕ × ℕ =>
      quadraticOrderToRingOfIntegers D
        (squareRelationNormPoint b c D nm.1 nm.2) :=
  (quadraticOrderToRingOfIntegers_injective D).comp
    (squareRelationNormPoint_injective hb hc)

/-! ## The signed-shift split branch -/

/-- Finite positive solution box for the source's literal integer-shift
equation `a*n²+h=b*m²`. -/
noncomputable def squareRelationSolutionsBoxInt
    (a b : ℕ) (h : ℤ) (x y : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.Icc 1 x).product (Finset.Icc 1 y)).filter fun nm =>
    (a : ℤ) * (nm.1 : ℤ) ^ 2 + h = (b : ℤ) * (nm.2 : ℤ) ^ 2

theorem mem_squareRelationSolutionsBoxInt
    {a b : ℕ} {h : ℤ} {x y : ℕ} {nm : ℕ × ℕ} :
    nm ∈ squareRelationSolutionsBoxInt a b h x y ↔
      1 ≤ nm.1 ∧ nm.1 ≤ x ∧
      1 ≤ nm.2 ∧ nm.2 ≤ y ∧
      (a : ℤ) * (nm.1 : ℤ) ^ 2 + h =
        (b : ℤ) * (nm.2 : ℤ) ^ 2 := by
  classical
  simp [squareRelationSolutionsBoxInt, and_assoc]

def squareRelationSignedFactorGap (a c : ℕ) (nm : ℕ × ℕ) : ℤ :=
  ((c * nm.2 : ℕ) : ℤ) - ((a * nm.1 : ℕ) : ℤ)

private theorem squareRelation_signed_factorization
    {a b c : ℕ} {h : ℤ} {n m : ℕ} (hcSq : c ^ 2 = a * b)
    (heq : (a : ℤ) * (n : ℤ) ^ 2 + h = (b : ℤ) * (m : ℤ) ^ 2) :
    (((c * m : ℕ) : ℤ) - ((a * n : ℕ) : ℤ)) *
        (((c * m : ℕ) : ℤ) + ((a * n : ℕ) : ℤ)) =
      (a : ℤ) * h := by
  have hcSqZ : (c : ℤ) ^ 2 = (a : ℤ) * b := by exact_mod_cast hcSq
  have hdiff : (b : ℤ) * (m : ℤ) ^ 2 - (a : ℤ) * (n : ℤ) ^ 2 = h := by
    linarith
  push_cast
  calc
    ((c : ℤ) * m - (a : ℤ) * n) *
        ((c : ℤ) * m + (a : ℤ) * n) =
      (c : ℤ) ^ 2 * m ^ 2 - (a : ℤ) ^ 2 * n ^ 2 := by ring
    _ = (a : ℤ) * ((b : ℤ) * m ^ 2 - (a : ℤ) * n ^ 2) := by
      rw [hcSqZ]
      ring
    _ = (a : ℤ) * h := by rw [hdiff]

private theorem squareRelationSignedFactorGap_dvd
    {a b c : ℕ} {h : ℤ} {x y : ℕ} (hcSq : c ^ 2 = a * b)
    {nm : ℕ × ℕ} (hnm : nm ∈ squareRelationSolutionsBoxInt a b h x y) :
    squareRelationSignedFactorGap a c nm ∣ (a : ℤ) * h := by
  refine ⟨((c * nm.2 : ℕ) : ℤ) + ((a * nm.1 : ℕ) : ℤ), ?_⟩
  exact (squareRelation_signed_factorization hcSq
    (mem_squareRelationSolutionsBoxInt.mp hnm).2.2.2.2).symm

private theorem injOn_squareRelationSignedFactorGap
    {a b c : ℕ} {h : ℤ} {x y : ℕ}
    (ha : 0 < a) (hc : 0 < c) (hh : h ≠ 0) (hcSq : c ^ 2 = a * b) :
    Set.InjOn (squareRelationSignedFactorGap a c)
      (squareRelationSolutionsBoxInt a b h x y) := by
  rintro ⟨n₁, m₁⟩ h₁ ⟨n₂, m₂⟩ h₂ hgap
  have h₁factor : squareRelationSignedFactorGap a c (n₁, m₁) *
      (((c * m₁ : ℕ) : ℤ) + ((a * n₁ : ℕ) : ℤ)) = (a : ℤ) * h := by
    simpa [squareRelationSignedFactorGap] using
      squareRelation_signed_factorization hcSq
        (mem_squareRelationSolutionsBoxInt.mp h₁).2.2.2.2
  have h₂factor : squareRelationSignedFactorGap a c (n₂, m₂) *
      (((c * m₂ : ℕ) : ℤ) + ((a * n₂ : ℕ) : ℤ)) = (a : ℤ) * h := by
    simpa [squareRelationSignedFactorGap] using
      squareRelation_signed_factorization hcSq
        (mem_squareRelationSolutionsBoxInt.mp h₂).2.2.2.2
  have hgapNe : squareRelationSignedFactorGap a c (n₁, m₁) ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at h₁factor
    exact (mul_ne_zero (by exact_mod_cast ha.ne') hh) h₁factor.symm
  have hsum :
      ((c * m₁ : ℕ) : ℤ) + ((a * n₁ : ℕ) : ℤ) =
        ((c * m₂ : ℕ) : ℤ) + ((a * n₂ : ℕ) : ℤ) := by
    apply mul_left_cancel₀ hgapNe
    calc
      squareRelationSignedFactorGap a c (n₁, m₁) *
          (((c * m₁ : ℕ) : ℤ) + ((a * n₁ : ℕ) : ℤ)) =
        (a : ℤ) * h := h₁factor
      _ = squareRelationSignedFactorGap a c (n₂, m₂) *
          (((c * m₂ : ℕ) : ℤ) + ((a * n₂ : ℕ) : ℤ)) := h₂factor.symm
      _ = squareRelationSignedFactorGap a c (n₁, m₁) *
          (((c * m₂ : ℕ) : ℤ) + ((a * n₂ : ℕ) : ℤ)) := by rw [hgap]
  change ((c * m₁ : ℕ) : ℤ) - ((a * n₁ : ℕ) : ℤ) =
    ((c * m₂ : ℕ) : ℤ) - ((a * n₂ : ℕ) : ℤ) at hgap
  have hcmZ : ((c * m₁ : ℕ) : ℤ) = ((c * m₂ : ℕ) : ℤ) := by linarith
  have hanZ : ((a * n₁ : ℕ) : ℤ) = ((a * n₂ : ℕ) : ℤ) := by linarith
  have hcm : c * m₁ = c * m₂ := by exact_mod_cast hcmZ
  have han : a * n₁ = a * n₂ := by exact_mod_cast hanZ
  exact Prod.ext (Nat.mul_left_cancel ha han) (Nat.mul_left_cancel hc hcm)

theorem card_int_divisors (z : ℤ) :
    z.divisors.card = 2 * z.natAbs.divisors.card := by
  rw [Int.divisors, Finset.card_disjUnion, Finset.card_map, Finset.card_map]
  omega

/-- Source-faithful signed-shift form of the square-discriminant branch:
for every nonzero integer `h`, the number of positive boxed solutions is at
most twice the divisor count of `a*|h|`. -/
theorem card_squareRelationSolutionsBoxInt_le_two_mul_divisors_of_mul_isSquare
    {a b c : ℕ} {h : ℤ} {x y : ℕ}
    (ha : 0 < a) (hc : 0 < c) (hh : h ≠ 0) (hcSq : c ^ 2 = a * b) :
    (squareRelationSolutionsBoxInt a b h x y).card ≤
      2 * (a * h.natAbs).divisors.card := by
  have hsubset :
      (squareRelationSolutionsBoxInt a b h x y).image
          (squareRelationSignedFactorGap a c) ⊆ ((a : ℤ) * h).divisors := by
    intro d hd
    rw [Finset.mem_image] at hd
    rcases hd with ⟨nm, hnm, rfl⟩
    rw [Int.mem_divisors]
    exact ⟨squareRelationSignedFactorGap_dvd hcSq hnm,
      mul_ne_zero (by exact_mod_cast ha.ne') hh⟩
  calc
    (squareRelationSolutionsBoxInt a b h x y).card =
        ((squareRelationSolutionsBoxInt a b h x y).image
          (squareRelationSignedFactorGap a c)).card :=
      (Finset.card_image_iff.mpr
        (injOn_squareRelationSignedFactorGap ha hc hh hcSq)).symm
    _ ≤ ((a : ℤ) * h).divisors.card := Finset.card_le_card hsubset
    _ = 2 * (a * h.natAbs).divisors.card := by
      rw [card_int_divisors, Int.natAbs_mul]
      simp

/-- Divisor-epsilon consequence for the source's nonzero integer shift in
the split-discriminant branch. -/
theorem card_squareRelationSolutionsBoxInt_le_const_mul_rpow_of_mul_isSquare
    {a b c : ℕ} {h : ℤ} {x y : ℕ}
    (ha : 0 < a) (hc : 0 < c) (hh : h ≠ 0) (hcSq : c ^ 2 = a * b)
    {ε : ℝ} (hε : 0 < ε) :
    ((squareRelationSolutionsBoxInt a b h x y).card : ℝ) ≤
      2 * RiemannZeta.GuthMaynard.divisorEpsilonConstant ε *
        (((a * h.natAbs : ℕ) : ℝ) ^ ε) := by
  have hNatAbs : 0 < h.natAbs := Int.natAbs_pos.mpr hh
  calc
    ((squareRelationSolutionsBoxInt a b h x y).card : ℝ) ≤
        (2 * (a * h.natAbs).divisors.card : ℕ) := by
      exact_mod_cast
        card_squareRelationSolutionsBoxInt_le_two_mul_divisors_of_mul_isSquare
          ha hc hh hcSq
    _ = 2 * ((a * h.natAbs).divisors.card : ℝ) := by norm_num
    _ ≤ 2 * (RiemannZeta.GuthMaynard.divisorEpsilonConstant ε *
        (((a * h.natAbs : ℕ) : ℝ) ^ ε)) := by
      gcongr
      exact RiemannZeta.GuthMaynard.card_divisors_le_const_mul_rpow hε
        (mul_ne_zero ha.ne' hNatAbs.ne')
    _ = 2 * RiemannZeta.GuthMaynard.divisorEpsilonConstant ε *
        (((a * h.natAbs : ℕ) : ℝ) ^ ε) := by ring

def squareRelationFactorGap (a c : ℕ) (nm : ℕ × ℕ) : ℕ :=
  c * nm.2 - a * nm.1

private theorem squareRelation_scaled_lt
    {a b c h n m : ℕ} (ha : 0 < a) (hh : 0 < h)
    (hcSq : c ^ 2 = a * b) (heq : a * n ^ 2 + h = b * m ^ 2) :
    a * n < c * m := by
  have hsq : (a * n) ^ 2 < (c * m) ^ 2 := by
    calc
      (a * n) ^ 2 < (a * n) ^ 2 + a * h := by
        exact Nat.lt_add_of_pos_right (mul_pos ha hh)
      _ = (c * m) ^ 2 := by
        calc
          (a * n) ^ 2 + a * h = a * (a * n ^ 2 + h) := by ring
          _ = a * (b * m ^ 2) := by rw [heq]
          _ = (a * b) * m ^ 2 := by ring
          _ = c ^ 2 * m ^ 2 := by rw [hcSq]
          _ = (c * m) ^ 2 := by ring
  exact lt_of_pow_lt_pow_left' 2 hsq

private theorem squareRelation_factorization
    {a b c h n m : ℕ} (ha : 0 < a) (hh : 0 < h)
    (hcSq : c ^ 2 = a * b) (heq : a * n ^ 2 + h = b * m ^ 2) :
    (c * m - a * n) * (c * m + a * n) = a * h := by
  have hlt := squareRelation_scaled_lt ha hh hcSq heq
  have hsub : (c * m - a * n) + a * n = c * m :=
    Nat.sub_add_cancel hlt.le
  have hdiff :
      (c * m - a * n) * (c * m + a * n) =
        (c * m) ^ 2 - (a * n) ^ 2 := by
    have hsqLe : (a * n) ^ 2 ≤ (c * m) ^ 2 := by
      exact (Nat.pow_le_pow_left hlt.le 2)
    apply Nat.cast_injective (R := ℤ)
    push_cast
    rw [Nat.cast_sub hlt.le, Nat.cast_sub hsqLe]
    norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow]
    ring
  calc
    (c * m - a * n) * (c * m + a * n) =
        (c * m) ^ 2 - (a * n) ^ 2 := hdiff
    _ = a * h := by
      have hsquare : (c * m) ^ 2 = (a * n) ^ 2 + a * h := by
        calc
          (c * m) ^ 2 = c ^ 2 * m ^ 2 := by ring
          _ = (a * b) * m ^ 2 := by rw [hcSq]
          _ = a * (b * m ^ 2) := by ring
          _ = a * (a * n ^ 2 + h) := by rw [heq]
          _ = (a * n) ^ 2 + a * h := by ring
      omega

private theorem squareRelationFactorGap_pos
    {a b c h x y : ℕ} (ha : 0 < a) (hh : 0 < h)
    (hcSq : c ^ 2 = a * b) {nm : ℕ × ℕ}
    (hnm : nm ∈ squareRelationSolutionsBox a b h x y) :
    0 < squareRelationFactorGap a c nm := by
  rw [squareRelationFactorGap, Nat.sub_pos_iff_lt]
  exact squareRelation_scaled_lt ha hh hcSq
    (mem_squareRelationSolutionsBox.mp hnm).2.2.2.2

private theorem squareRelationFactorGap_dvd
    {a b c h x y : ℕ} (ha : 0 < a) (hh : 0 < h)
    (hcSq : c ^ 2 = a * b) {nm : ℕ × ℕ}
    (hnm : nm ∈ squareRelationSolutionsBox a b h x y) :
    squareRelationFactorGap a c nm ∣ a * h := by
  refine ⟨c * nm.2 + a * nm.1, ?_⟩
  exact (squareRelation_factorization ha hh hcSq
    (mem_squareRelationSolutionsBox.mp hnm).2.2.2.2).symm

private theorem injOn_squareRelationFactorGap
    {a b c h x y : ℕ} (ha : 0 < a) (hc : 0 < c) (hh : 0 < h)
    (hcSq : c ^ 2 = a * b) :
    Set.InjOn (squareRelationFactorGap a c)
      (squareRelationSolutionsBox a b h x y) := by
  rintro ⟨n₁, m₁⟩ h₁ ⟨n₂, m₂⟩ h₂ hgap
  have h₁eq := (mem_squareRelationSolutionsBox.mp h₁).2.2.2.2
  have h₂eq := (mem_squareRelationSolutionsBox.mp h₂).2.2.2.2
  have h₁factor := squareRelation_factorization ha hh hcSq h₁eq
  have h₂factor := squareRelation_factorization ha hh hcSq h₂eq
  have hgapPos := squareRelationFactorGap_pos ha hh hcSq h₁
  have hsum : c * m₁ + a * n₁ = c * m₂ + a * n₂ := by
    apply Nat.mul_left_cancel hgapPos
    change squareRelationFactorGap a c (n₁, m₁) *
        (c * m₁ + a * n₁) =
      squareRelationFactorGap a c (n₁, m₁) *
        (c * m₂ + a * n₂)
    calc
      squareRelationFactorGap a c (n₁, m₁) *
          (c * m₁ + a * n₁) = a * h := h₁factor
      _ = squareRelationFactorGap a c (n₂, m₂) *
          (c * m₂ + a * n₂) := h₂factor.symm
      _ = squareRelationFactorGap a c (n₁, m₁) *
          (c * m₂ + a * n₂) := by rw [hgap]
  have h₁lt : a * n₁ < c * m₁ :=
    squareRelation_scaled_lt ha hh hcSq h₁eq
  have h₂lt : a * n₂ < c * m₂ :=
    squareRelation_scaled_lt ha hh hcSq h₂eq
  change c * m₁ - a * n₁ = c * m₂ - a * n₂ at hgap
  have hcm : c * m₁ = c * m₂ := by omega
  have han : a * n₁ = a * n₂ := by omega
  have hm : m₁ = m₂ := Nat.mul_left_cancel hc hcm
  have hn : n₁ = n₂ := Nat.mul_left_cancel ha han
  exact Prod.ext hn hm

/-- The square-discriminant case of Tao's Lemma 2.10: if `a*b=c²`, each
positive solution determines a distinct positive divisor `c*m-a*n` of
`a*h`. The bound is uniform in both box dimensions. -/
theorem card_squareRelationSolutionsBox_le_divisors_of_mul_isSquare
    {a b c h x y : ℕ} (ha : 0 < a) (hc : 0 < c) (hh : 0 < h)
    (hcSq : c ^ 2 = a * b) :
    (squareRelationSolutionsBox a b h x y).card ≤
      (a * h).divisors.card := by
  have hsubset :
      (squareRelationSolutionsBox a b h x y).image
          (squareRelationFactorGap a c) ⊆ (a * h).divisors := by
    intro d hd
    rw [Finset.mem_image] at hd
    rcases hd with ⟨nm, hnm, rfl⟩
    rw [Nat.mem_divisors]
    exact ⟨squareRelationFactorGap_dvd ha hh hcSq hnm,
      mul_ne_zero ha.ne' hh.ne'⟩
  calc
    (squareRelationSolutionsBox a b h x y).card =
        ((squareRelationSolutionsBox a b h x y).image
          (squareRelationFactorGap a c)).card :=
      (Finset.card_image_iff.mpr
        (injOn_squareRelationFactorGap ha hc hh hcSq)).symm
    _ ≤ (a * h).divisors.card := Finset.card_le_card hsubset

/-- Quantitative form of the split-discriminant branch, using the frozen
kernel-checked divisor-function epsilon estimate. -/
theorem card_squareRelationSolutionsBox_le_const_mul_rpow_of_mul_isSquare
    {a b c h x y : ℕ} (ha : 0 < a) (hc : 0 < c) (hh : 0 < h)
    (hcSq : c ^ 2 = a * b) {ε : ℝ} (hε : 0 < ε) :
    ((squareRelationSolutionsBox a b h x y).card : ℝ) ≤
      RiemannZeta.GuthMaynard.divisorEpsilonConstant ε *
        ((a * h : ℕ) : ℝ) ^ ε := by
  calc
    ((squareRelationSolutionsBox a b h x y).card : ℝ) ≤
        ((a * h).divisors.card : ℝ) := by
      exact_mod_cast card_squareRelationSolutionsBox_le_divisors_of_mul_isSquare
        ha hc hh hcSq
    _ ≤ RiemannZeta.GuthMaynard.divisorEpsilonConstant ε *
        ((a * h : ℕ) : ℝ) ^ ε :=
      RiemannZeta.GuthMaynard.card_divisors_le_const_mul_rpow hε
        (mul_ne_zero ha.ne' hh.ne')

end Tao2026
