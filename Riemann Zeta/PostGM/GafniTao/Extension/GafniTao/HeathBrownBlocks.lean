import GafniTao.HeathBrownKernelFourier
import GafniTao.HeathBrownBlockParameter

/-!
# The integer block partition in Heath-Brown Section 3

The interval `(0,N]` is partitioned into consecutive integer blocks of
length `1 + N / K`.  For positive `K` at most `K` blocks are used, and two
indices in a common block have source distance at most `1 + N / K`.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

def heathBrownBlockLength (N K : ℕ) : ℕ := 1 + N / K

def heathBrownBlockIndex (N K n : ℕ) : ℕ :=
  (n - 1) / heathBrownBlockLength N K

def heathBrownBlock (N K i : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun n => heathBrownBlockIndex N K n = i)

theorem heathBrownBlockLength_pos (N K : ℕ) :
    0 < heathBrownBlockLength N K := by
  simp [heathBrownBlockLength]

theorem heathBrownBlockIndex_lt
    {N K n : ℕ} (hK : 0 < K) (hnOne : 1 ≤ n) (hnN : n ≤ N) :
    heathBrownBlockIndex N K n < K := by
  have hmod : N % K < K := Nat.mod_lt N hK
  have hdecomp : K * (N / K) + N % K = N := Nat.div_add_mod N K
  have hnsub : n - 1 < N := by omega
  rw [heathBrownBlockIndex, Nat.div_lt_iff_lt_mul (heathBrownBlockLength_pos N K)]
  simp only [heathBrownBlockLength]
  nlinarith

theorem mem_heathBrownBlock {N K i n : ℕ} :
    n ∈ heathBrownBlock N K i ↔
      1 ≤ n ∧ n ≤ N ∧ heathBrownBlockIndex N K n = i := by
  simp [heathBrownBlock, and_assoc]

theorem heathBrownBlock_pair_distance
    {N K i m n : ℕ}
    (hm : m ∈ heathBrownBlock N K i)
    (hn : n ∈ heathBrownBlock N K i) :
    Nat.dist m n ≤ heathBrownBlockLength N K := by
  rw [mem_heathBrownBlock] at hm hn
  let L := heathBrownBlockLength N K
  have hL : 0 < L := heathBrownBlockLength_pos N K
  have hquot : (m - 1) / L = (n - 1) / L := by
    simpa [L, heathBrownBlockIndex] using hm.2.2.trans hn.2.2.symm
  let q := (m - 1) / L
  have hqN : (n - 1) / L = q := hquot.symm
  have hmLower : L * q ≤ m - 1 := by
    exact Nat.mul_div_le (m - 1) L
  have hnLower : L * q ≤ n - 1 := by
    rw [← hqN]
    exact Nat.mul_div_le (n - 1) L
  have hmUpper : m - 1 < (q + 1) * L := by
    rw [← Nat.div_lt_iff_lt_mul hL]
    simp [q]
  have hnUpper : n - 1 < (q + 1) * L := by
    rw [← Nat.div_lt_iff_lt_mul hL]
    simp [hqN]
  have hmUpper' : m - 1 < L * q + L := by
    simpa [Nat.add_mul, Nat.mul_comm] using hmUpper
  have hnUpper' : n - 1 < L * q + L := by
    simpa [Nat.add_mul, Nat.mul_comm] using hnUpper
  rcases le_total m n with hmn | hnm
  · rw [Nat.dist_eq_sub_of_le hmn]
    omega
  · rw [Nat.dist_eq_sub_of_le_right hnm]
    omega

theorem heathBrownBlock_pair_source_distance
    {N K i m n : ℕ}
    (hm : m ∈ heathBrownBlock N K i)
    (hn : n ∈ heathBrownBlock N K i) :
    Nat.dist m n ≤ 1 + N / K := by
  exact heathBrownBlock_pair_distance hm hn

theorem heathBrown_sum_over_blocks
    {M : Type*} [AddCommMonoid M]
    {N K : ℕ} (hK : 0 < K) (F : ℕ → M) :
    ∑ i ∈ Finset.range K, (∑ n ∈ Finset.Icc 1 N,
        if heathBrownBlockIndex N K n = i then F n else 0) =
      ∑ n ∈ Finset.Icc 1 N, F n := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  have hn' := Finset.mem_Icc.mp hn
  have hi : heathBrownBlockIndex N K n ∈ Finset.range K :=
    Finset.mem_range.mpr (heathBrownBlockIndex_lt hK hn'.1 hn'.2)
  simp [Finset.sum_ite_eq, hi]

theorem heathBrown_block_sum_eq
    {M : Type*} [AddCommMonoid M]
    {N K i : ℕ} (F : ℕ → M) :
    (∑ n ∈ Finset.Icc 1 N,
        if heathBrownBlockIndex N K n = i then F n else 0) =
      ∑ n ∈ heathBrownBlock N K i, F n := by
  classical
  rw [← Finset.sum_filter]
  rfl

#print axioms heathBrownBlockIndex_lt
#print axioms mem_heathBrownBlock
#print axioms heathBrownBlock_pair_distance
#print axioms heathBrownBlock_pair_source_distance
#print axioms heathBrown_sum_over_blocks
#print axioms heathBrown_block_sum_eq

end

end GafniTao
