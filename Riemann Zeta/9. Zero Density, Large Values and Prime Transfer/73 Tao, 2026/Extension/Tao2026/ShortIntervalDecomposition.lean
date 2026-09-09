import Mathlib

/-!
# Shorter-than-dyadic interval decomposition

This module supplies the exact finite combinatorics behind the pinned
source's shorter-than-dyadic decomposition.  A natural interval is grouped by
the quotient of its displacement from the left endpoint.  The construction
has an exact sum identity, an explicit ceiling bound for the number of
blocks, and a strict diameter bound inside every block.
-/

open Finset
open scoped BigOperators

namespace Tao2026

/-- Number of quotient blocks of length `q` needed to cover `[a,b)`. -/
def shortIntervalBlockCount (a b q : ℕ) : ℕ :=
  (b - a) ⌈/⌉ q

/-- The `k`-th quotient block in `[a,b)`, of integer diameter less than `q`. -/
def shortIntervalBlock (a b q k : ℕ) : Finset ℕ :=
  (Finset.Ico a b).filter (fun n => (n - a) / q = k)

theorem mem_shortIntervalBlock {a b q k n : ℕ} :
    n ∈ shortIntervalBlock a b q k ↔
      a ≤ n ∧ n < b ∧ (n - a) / q = k := by
  simp [shortIntervalBlock, and_assoc]

/-- Every point of `[a,b)` belongs to a block below the ceiling block count. -/
theorem shortIntervalBlock_index_lt
    {a b q n : ℕ} (hq : 0 < q) (hn : n ∈ Finset.Ico a b) :
    (n - a) / q < shortIntervalBlockCount a b q := by
  have hsub : n - a < b - a := by
    rw [Finset.mem_Ico] at hn
    omega
  rw [Nat.div_lt_iff_lt_mul hq]
  calc
    n - a < b - a := hsub
    _ ≤ q * shortIntervalBlockCount a b q := by
      exact (ceilDiv_le_iff_le_mul hq).1 le_rfl
    _ = shortIntervalBlockCount a b q * q := Nat.mul_comm _ _

/-- Exact regrouping of a finite interval sum into shorter quotient blocks. -/
theorem sum_shortIntervalBlocks
    {A : Type*} [AddCommMonoid A] (f : ℕ → A)
    {a b q : ℕ} (hq : 0 < q) :
    ∑ n ∈ Finset.Ico a b, f n =
      ∑ k ∈ Finset.range (shortIntervalBlockCount a b q),
        ∑ n ∈ shortIntervalBlock a b q k, f n := by
  simpa only [shortIntervalBlock] using
    (Finset.sum_fiberwise_of_maps_to
      (fun n hn => Finset.mem_range.mpr (shortIntervalBlock_index_lt hq hn)) f).symm

/-- If `[a,b)` has length at most `Qq`, its shorter-than-dyadic
decomposition uses at most `Q` blocks. -/
theorem shortIntervalBlockCount_le
    {a b q Q : ℕ} (hq : 0 < q) (hlen : b - a ≤ q * Q) :
    shortIntervalBlockCount a b q ≤ Q := by
  exact (ceilDiv_le_iff_le_mul hq).2 hlen

/-- Two members of the same quotient block have natural distance strictly
less than the chosen block length. -/
theorem natDist_lt_of_mem_same_shortIntervalBlock
    {a b q k x y : ℕ} (hq : 0 < q)
    (hx : x ∈ shortIntervalBlock a b q k)
    (hy : y ∈ shortIntervalBlock a b q k) :
    Nat.dist x y < q := by
  rw [mem_shortIntervalBlock] at hx hy
  have hxmod : (x - a) % q < q := Nat.mod_lt _ hq
  have hymod : (y - a) % q < q := Nat.mod_lt _ hq
  have hxrepr : x - a = ((x - a) / q) * q + (x - a) % q := by
    simpa only [Nat.mul_comm] using (Nat.div_add_mod (x - a) q).symm
  have hyrepr : y - a = ((y - a) / q) * q + (y - a) % q := by
    simpa only [Nat.mul_comm] using (Nat.div_add_mod (y - a) q).symm
  have hsubdist : Nat.dist (x - a) (y - a) < q := by
    rw [hxrepr, hyrepr, hx.2.2, hy.2.2, Nat.dist_add_add_left]
    unfold Nat.dist
    omega
  have hxrepr' : x = a + (x - a) := by omega
  have hyrepr' : y = a + (y - a) := by omega
  rw [hxrepr', hyrepr', Nat.dist_add_add_left]
  exact hsubdist

/-- Distinct points in one block differ by one of the nonzero offsets below
the block length. -/
theorem natDist_mem_same_shortIntervalBlock_bounds
    {a b q k x y : ℕ} (hq : 0 < q) (hne : x ≠ y)
    (hx : x ∈ shortIntervalBlock a b q k)
    (hy : y ∈ shortIntervalBlock a b q k) :
    1 ≤ Nat.dist x y ∧ Nat.dist x y < q := by
  exact ⟨Nat.one_le_iff_ne_zero.mpr (fun h => hne (Nat.eq_of_dist_eq_zero h)),
    natDist_lt_of_mem_same_shortIntervalBlock hq hx hy⟩

/-- A quotient block of length `q` contains at most `q` natural numbers. -/
theorem card_shortIntervalBlock_le (a b q k : ℕ) (hq : 0 < q) :
    (shortIntervalBlock a b q k).card ≤ q := by
  have hsub : shortIntervalBlock a b q k ⊆
      Finset.Ico (a + k * q) (a + (k + 1) * q) := by
    intro n hn
    rw [mem_shortIntervalBlock] at hn
    have hmod : (n - a) % q < q := Nat.mod_lt _ hq
    have hrepr : n - a = ((n - a) / q) * q + (n - a) % q := by
      simpa only [Nat.mul_comm] using (Nat.div_add_mod (n - a) q).symm
    have hnrepr : n = a + (n - a) := by omega
    rw [Finset.mem_Ico, hnrepr, hrepr, hn.2.2]
    constructor
    · omega
    · rw [Nat.add_mul]
      simp only [one_mul]
      omega
  calc
    (shortIntervalBlock a b q k).card ≤
        (Finset.Ico (a + k * q) (a + (k + 1) * q)).card :=
      Finset.card_le_card hsub
    _ = q := by
      rw [Nat.card_Ico, Nat.add_mul]
      simp
      omega

/-- Restriction of a coefficient sequence to one shorter quotient block. -/
def shortIntervalCoefficient {A : Type*} [Zero A] (f : ℕ → A)
    (a b q k n : ℕ) : A :=
  if n ∈ shortIntervalBlock a b q k then f n else 0

theorem shortIntervalCoefficient_eq_zero_of_not_mem
    {A : Type*} [Zero A] (f : ℕ → A) {a b q k n : ℕ}
    (hn : n ∉ shortIntervalBlock a b q k) :
    shortIntervalCoefficient f a b q k n = 0 := by
  simp [shortIntervalCoefficient, hn]

/-- Exact pointwise decomposition of an interval-restricted coefficient
sequence into its quotient blocks. -/
theorem sum_shortIntervalCoefficient
    {A : Type*} [AddCommMonoid A] (f : ℕ → A)
    {a b q n : ℕ} (hq : 0 < q) :
    ∑ k ∈ Finset.range (shortIntervalBlockCount a b q),
        shortIntervalCoefficient f a b q k n =
      if n ∈ Finset.Ico a b then f n else 0 := by
  by_cases hn : n ∈ Finset.Ico a b
  · have hk := shortIntervalBlock_index_lt hq hn
    simp [shortIntervalCoefficient, shortIntervalBlock, hn, hk]
  · simp [shortIntervalCoefficient, shortIntervalBlock, hn]

/-- If `f` is supported in `[a,b)`, summing its shorter-block restrictions
recovers `f` pointwise. -/
theorem sum_shortIntervalCoefficient_eq_of_support
    {A : Type*} [AddCommMonoid A] (f : ℕ → A)
    {a b q n : ℕ} (hq : 0 < q)
    (hsupport : ∀ m, f m ≠ 0 → m ∈ Finset.Ico a b) :
    ∑ k ∈ Finset.range (shortIntervalBlockCount a b q),
        shortIntervalCoefficient f a b q k n = f n := by
  rw [sum_shortIntervalCoefficient f hq]
  by_cases hn : n ∈ Finset.Ico a b
  · simp [hn]
  · have hf : f n = 0 := by
      by_contra hne
      exact hn (hsupport n hne)
    simp [hn, hf]

/-- A uniform coefficient bound survives restriction to every short block. -/
theorem norm_shortIntervalCoefficient_le
    {A : Type*} [SeminormedAddCommGroup A] (f : ℕ → A)
    {a b q k n : ℕ} {L : ℝ} (hf : ‖f n‖ ≤ L) :
    ‖shortIntervalCoefficient f a b q k n‖ ≤ L := by
  by_cases hn : n ∈ shortIntervalBlock a b q k
  · simpa [shortIntervalCoefficient, hn] using hf
  · simp [shortIntervalCoefficient, hn, le_trans (norm_nonneg (f n)) hf]

/-- A finite weighted sum of a supported coefficient sequence is exactly the
sum of the corresponding shorter-block weighted sums.  This is the direct
interface used for each term produced by Vaughan's identity. -/
theorem weightedSum_eq_sum_shortIntervalCoefficients
    {A : Type*} [CommSemiring A] (T : Finset ℕ) (w f : ℕ → A)
    {a b q : ℕ} (hq : 0 < q)
    (hsupport : ∀ n, f n ≠ 0 → n ∈ Finset.Ico a b) :
    ∑ n ∈ T, w n * f n =
      ∑ k ∈ Finset.range (shortIntervalBlockCount a b q),
        ∑ n ∈ T, w n * shortIntervalCoefficient f a b q k n := by
  calc
    ∑ n ∈ T, w n * f n =
        ∑ n ∈ T, w n *
          (∑ k ∈ Finset.range (shortIntervalBlockCount a b q),
            shortIntervalCoefficient f a b q k n) := by
      apply Finset.sum_congr rfl
      intro n _hn
      rw [sum_shortIntervalCoefficient_eq_of_support f hq hsupport]
    _ = ∑ n ∈ T, ∑ k ∈ Finset.range (shortIntervalBlockCount a b q),
          w n * shortIntervalCoefficient f a b q k n := by
      simp_rw [Finset.mul_sum]
    _ = _ := by rw [Finset.sum_comm]

end Tao2026
