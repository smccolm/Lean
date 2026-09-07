import RiemannZeta.GuthMaynard.QuadraticDivisor
import Mathlib.Data.Int.GCD

/-!
# Chinese-remainder factorization of Kloosterman sums

This is the first recursive dependency of DFI equation (25).  It proves the
exact Bézout-scaled factorization of the standard additive character, moves
units and their inverses through the Chinese remainder equivalence, and then
factors the complete Kloosterman sum at coprime moduli.
-/

open Complex
open scoped BigOperators
open Classical

namespace RiemannZeta.GuthMaynard

/-- The exact additive-character factorization attached to Bézout's identity
`m*gcdA(m,n) + n*gcdB(m,n) = 1`. -/
theorem stdAddChar_intCast_mul_coprime
    (m n : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n) (z : ℤ) :
    ZMod.stdAddChar (z : ZMod (m * n)) =
      ZMod.stdAddChar (((Nat.gcdB m n : ℤ) * z : ℤ) : ZMod m) *
        ZMod.stdAddChar (((Nat.gcdA m n : ℤ) * z : ℤ) : ZMod n) := by
  rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe,
    ← Complex.exp_add]
  apply congrArg Complex.exp
  have hbez : (m : ℤ) * Nat.gcdA m n + (n : ℤ) * Nat.gcdB m n = 1 := by
    simpa [h] using (Nat.gcd_eq_gcd_ab m n).symm
  have hbezC : (m : ℂ) * (Nat.gcdA m n : ℂ) +
      (n : ℂ) * (Nat.gcdB m n : ℂ) = 1 := by
    exact_mod_cast hbez
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hratio : (z : ℂ) / ((m : ℂ) * n) =
      ((Nat.gcdB m n : ℂ) * z) / m +
        ((Nat.gcdA m n : ℂ) * z) / n := by
    field_simp
    linear_combination -(z : ℂ) * hbezC
  push_cast
  calc
    2 * (Real.pi : ℂ) * I * (z : ℂ) / ((m : ℂ) * n) =
        (2 * (Real.pi : ℂ) * I) * ((z : ℂ) / ((m : ℂ) * n)) := by ring
    _ = (2 * (Real.pi : ℂ) * I) *
        (((Nat.gcdB m n : ℂ) * z) / m +
          ((Nat.gcdA m n : ℂ) * z) / n) := by rw [hratio]
    _ = 2 * (Real.pi : ℂ) * I * ((Nat.gcdB m n : ℂ) * z) / m +
        2 * (Real.pi : ℂ) * I * ((Nat.gcdA m n : ℂ) * z) / n := by ring

theorem chineseRemainder_fst_eq_val
    (m n : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n)
    (x : ZMod (m * n)) :
    (ZMod.chineseRemainder h x).1 = (x.val : ZMod m) := by
  dsimp [ZMod.chineseRemainder]
  rw [Prod.fst_zmod_cast, ZMod.natCast_val]

theorem chineseRemainder_snd_eq_val
    (m n : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n)
    (x : ZMod (m * n)) :
    (ZMod.chineseRemainder h x).2 = (x.val : ZMod n) := by
  dsimp [ZMod.chineseRemainder]
  rw [Prod.snd_zmod_cast, ZMod.natCast_val]

/-- Pointwise CRT factorization of the standard character. -/
theorem stdAddChar_chineseRemainder
    (m n : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n)
    (x : ZMod (m * n)) :
    ZMod.stdAddChar x =
      ZMod.stdAddChar
          ((Nat.gcdB m n : ZMod m) * (ZMod.chineseRemainder h x).1) *
        ZMod.stdAddChar
          ((Nat.gcdA m n : ZMod n) * (ZMod.chineseRemainder h x).2) := by
  calc
    ZMod.stdAddChar x = ZMod.stdAddChar ((x.val : ℕ) : ZMod (m * n)) := by
      rw [ZMod.natCast_zmod_val]
    _ = ZMod.stdAddChar
          (((Nat.gcdB m n : ℤ) * (x.val : ℤ) : ℤ) : ZMod m) *
        ZMod.stdAddChar
          (((Nat.gcdA m n : ℤ) * (x.val : ℤ) : ℤ) : ZMod n) := by
      simpa only [Int.cast_natCast] using
        stdAddChar_intCast_mul_coprime m n h (x.val : ℤ)
    _ = _ := by
      rw [chineseRemainder_fst_eq_val m n h,
        chineseRemainder_snd_eq_val m n h]
      push_cast
      rfl

/-- CRT on the unit groups, including componentwise inversion. -/
noncomputable def kloostermanCRTUnits (m n : ℕ) (h : m.Coprime n) :
    (ZMod (m * n))ˣ ≃ (ZMod m)ˣ × (ZMod n)ˣ :=
  ((Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans
    MulEquiv.prodUnits).toEquiv

@[simp]
theorem kloostermanCRTUnits_inv (m n : ℕ) (h : m.Coprime n)
    (d : (ZMod (m * n))ˣ) :
    kloostermanCRTUnits m n h d⁻¹ =
      ((kloostermanCRTUnits m n h d).1⁻¹,
        (kloostermanCRTUnits m n h d).2⁻¹) := rfl

theorem chineseRemainder_kloostermanPhase_fst
    (m n : ℕ) (h : m.Coprime n) (A B : ZMod (m * n))
    (d : (ZMod (m * n))ˣ) :
    (ZMod.chineseRemainder h
      (A * (d : ZMod (m * n)) + B * (↑(d⁻¹) : ZMod (m * n)))).1 =
      (ZMod.chineseRemainder h A).1 *
          (((kloostermanCRTUnits m n h d).1 : (ZMod m)ˣ) : ZMod m) +
        (ZMod.chineseRemainder h B).1 *
          (↑((kloostermanCRTUnits m n h d).1⁻¹) : ZMod m) := by
  rw [map_add, map_mul, map_mul]
  rfl

theorem chineseRemainder_kloostermanPhase_snd
    (m n : ℕ) (h : m.Coprime n) (A B : ZMod (m * n))
    (d : (ZMod (m * n))ˣ) :
    (ZMod.chineseRemainder h
      (A * (d : ZMod (m * n)) + B * (↑(d⁻¹) : ZMod (m * n)))).2 =
      (ZMod.chineseRemainder h A).2 *
          (((kloostermanCRTUnits m n h d).2 : (ZMod n)ˣ) : ZMod n) +
        (ZMod.chineseRemainder h B).2 *
          (↑((kloostermanCRTUnits m n h d).2⁻¹) : ZMod n) := by
  rw [map_add, map_mul, map_mul]
  rfl

/-- Exact multiplicativity of the complete Kloosterman sum at coprime
moduli.  Bézout factors appear in both local frequencies because Mathlib's
standard characters all use the positive `exp(2πi·/q)` normalization. -/
theorem kloostermanSumZMod_mul_coprime
    (m n : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n)
    (A B : ZMod (m * n)) :
    kloostermanSumZMod (m * n) A B =
      kloostermanSumZMod m
          ((Nat.gcdB m n : ZMod m) * (ZMod.chineseRemainder h A).1)
          ((Nat.gcdB m n : ZMod m) * (ZMod.chineseRemainder h B).1) *
        kloostermanSumZMod n
          ((Nat.gcdA m n : ZMod n) * (ZMod.chineseRemainder h A).2)
          ((Nat.gcdA m n : ZMod n) * (ZMod.chineseRemainder h B).2) := by
  unfold kloostermanSumZMod
  let e := kloostermanCRTUnits m n h
  let F : (ZMod (m * n))ˣ → ℂ := fun d =>
    ZMod.stdAddChar
      (A * (d : ZMod (m * n)) + B * (↑(d⁻¹) : ZMod (m * n)))
  let Fm : (ZMod m)ˣ → ℂ := fun d =>
    ZMod.stdAddChar
      (((Nat.gcdB m n : ZMod m) * (ZMod.chineseRemainder h A).1) *
          (d : ZMod m) +
        ((Nat.gcdB m n : ZMod m) * (ZMod.chineseRemainder h B).1) *
          (↑(d⁻¹) : ZMod m))
  let Fn : (ZMod n)ˣ → ℂ := fun d =>
    ZMod.stdAddChar
      (((Nat.gcdA m n : ZMod n) * (ZMod.chineseRemainder h A).2) *
          (d : ZMod n) +
        ((Nat.gcdA m n : ZMod n) * (ZMod.chineseRemainder h B).2) *
          (↑(d⁻¹) : ZMod n))
  change (∑ d, F d) = (∑ d, Fm d) * ∑ d, Fn d
  calc
    (∑ d, F d) = ∑ p : (ZMod m)ˣ × (ZMod n)ˣ, Fm p.1 * Fn p.2 := by
      apply Fintype.sum_equiv e
      intro d
      dsimp only [F, Fm, Fn, e]
      rw [stdAddChar_chineseRemainder m n h]
      rw [chineseRemainder_kloostermanPhase_fst m n h,
        chineseRemainder_kloostermanPhase_snd m n h]
      congr 1 <;> apply congrArg ZMod.stdAddChar <;> ring
    _ = ∑ x : (ZMod m)ˣ, ∑ y : (ZMod n)ˣ, Fm x * Fn y := by
      rw [Fintype.sum_prod_type]
    _ = (∑ d, Fm d) * ∑ d, Fn d :=
      (Fintype.sum_mul_sum Fm Fn).symm

/-- Multiplying one frequency by a unit and the other by its inverse leaves
the complete Kloosterman sum unchanged.  This is the exact change of
variables used to normalize the nonzero local frequencies. -/
theorem kloostermanSumZMod_mul_unit_inv
    (q : ℕ) [NeZero q] (A B : ZMod q) (u : (ZMod q)ˣ) :
    kloostermanSumZMod q A B =
      kloostermanSumZMod q (A * (u : ZMod q))
        (B * (↑(u⁻¹) : ZMod q)) := by
  unfold kloostermanSumZMod
  apply Fintype.sum_equiv (Equiv.mulLeft u⁻¹)
  intro d
  dsimp
  apply congrArg ZMod.stdAddChar
  rw [show (u⁻¹ * d)⁻¹ = d⁻¹ * u by group]
  push_cast
  have huv : (u : ZMod q) * (↑u⁻¹ : ZMod q) = 1 := by
    norm_cast
    exact Units.mul_inv u
  have hvu : (↑u⁻¹ : ZMod q) * (u : ZMod q) = 1 := by
    norm_cast
    exact Units.inv_mul u
  symm
  calc
    A * (u : ZMod q) * ((↑u⁻¹ : ZMod q) * d) +
        B * (↑u⁻¹ : ZMod q) * ((↑d⁻¹ : ZMod q) * u) =
      A * ((u : ZMod q) * (↑u⁻¹ : ZMod q)) * d +
        B * ((↑u⁻¹ : ZMod q) * u) * (↑d⁻¹ : ZMod q) := by ring
    _ = A * d + B * (↑d⁻¹ : ZMod q) := by rw [huv, hvu]; ring

/-- Norm multiplicativity at coprime moduli. -/
theorem norm_kloostermanSumZMod_mul_coprime
    (m n : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n)
    (A B : ZMod (m * n)) :
    ‖kloostermanSumZMod (m * n) A B‖ =
      ‖kloostermanSumZMod m
          ((Nat.gcdB m n : ZMod m) * (ZMod.chineseRemainder h A).1)
          ((Nat.gcdB m n : ZMod m) * (ZMod.chineseRemainder h B).1)‖ *
        ‖kloostermanSumZMod n
          ((Nat.gcdA m n : ZMod n) * (ZMod.chineseRemainder h A).2)
          ((Nat.gcdA m n : ZMod n) * (ZMod.chineseRemainder h B).2)‖ := by
  rw [kloostermanSumZMod_mul_coprime m n h, norm_mul]

end RiemannZeta.GuthMaynard
