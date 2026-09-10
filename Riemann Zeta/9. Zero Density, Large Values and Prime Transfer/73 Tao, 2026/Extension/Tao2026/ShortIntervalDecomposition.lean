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

/-- A quotient block is a literal half-open natural interval. -/
theorem shortIntervalBlock_eq_Ico
    {a b q k : ℕ} (hq : 0 < q) :
    shortIntervalBlock a b q k =
      Finset.Ico (a + k * q) (min b (a + (k + 1) * q)) := by
  ext n
  rw [mem_shortIntervalBlock]
  simp only [Finset.mem_Ico, lt_min_iff]
  constructor
  · rintro ⟨han, hnb, hdiv⟩
    have hmod : (n - a) % q < q := Nat.mod_lt _ hq
    have hrepr : n - a = ((n - a) / q) * q + (n - a) % q := by
      simpa only [Nat.mul_comm] using (Nat.div_add_mod (n - a) q).symm
    rw [hdiv] at hrepr
    have hnrepr : n = a + (n - a) := by omega
    constructor
    · omega
    · exact ⟨hnb, by rw [hnrepr, hrepr, Nat.add_mul]; simp only [one_mul]; omega⟩
  · rintro ⟨hlower, hnb, hupper⟩
    have han : a ≤ n := by omega
    have hmulLower : k * q ≤ n - a := by omega
    have hmulUpper : n - a < (k + 1) * q := by omega
    have hdivLower : k ≤ (n - a) / q :=
      (Nat.le_div_iff_mul_le hq).2 hmulLower
    have hdivUpper : (n - a) / q < k + 1 :=
      (Nat.div_lt_iff_lt_mul hq).2 hmulUpper
    exact ⟨han, hnb, by omega⟩

/-- Multiplication by a positive natural identifies the product restriction
`mn ∈ [a,b)` with the ceiling-divided interval in `m`. -/
theorem mul_mem_Ico_iff_mem_Ico_ceilDiv
    {a b m n : ℕ} (hn : 0 < n) :
    m * n ∈ Finset.Ico a b ↔
      m ∈ Finset.Ico (a ⌈/⌉ n) (b ⌈/⌉ n) := by
  simp only [Finset.mem_Ico]
  constructor
  · rintro ⟨hlower, hupper⟩
    constructor
    · apply (ceilDiv_le_iff_le_mul hn).2
      simpa only [Nat.mul_comm] using hlower
    · by_contra hnot
      have hceil : b ⌈/⌉ n ≤ m := Nat.le_of_not_gt hnot
      have hb : b ≤ n * m := (ceilDiv_le_iff_le_mul hn).1 hceil
      rw [Nat.mul_comm] at hb
      omega
  · rintro ⟨hlower, hupper⟩
    constructor
    · have ha : a ≤ n * m := (ceilDiv_le_iff_le_mul hn).1 hlower
      simpa only [Nat.mul_comm] using ha
    · by_contra hnot
      have hb : b ≤ m * n := Nat.le_of_not_gt hnot
      have hceil : b ⌈/⌉ n ≤ m := by
        apply (ceilDiv_le_iff_le_mul hn).2
        simpa only [Nat.mul_comm] using hb
      omega

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

/-- Integer block length for dividing a dyadic interval `[D,2D)` into at
most `L` shorter pieces. -/
def dyadicShortIntervalLength (D L : ℕ) : ℕ :=
  D ⌈/⌉ L

theorem dyadicShortIntervalLength_pos
    {D L : ℕ} (hD : 0 < D) (hL : 0 < L) :
    0 < dyadicShortIntervalLength D L := by
  by_contra h
  have hzero : dyadicShortIntervalLength D L = 0 := Nat.eq_zero_of_not_pos h
  have hcover : D ≤ L * dyadicShortIntervalLength D L := by
    exact (ceilDiv_le_iff_le_mul hL).1 le_rfl
  rw [hzero, Nat.mul_zero] at hcover
  omega

/-- Ceiling division enlarges the ideal dyadic relative length `D/L` by at
most one integer. -/
theorem dyadicShortIntervalLength_le_div_add_one
    (D : ℕ) {L : ℕ} (hL : 0 < L) :
    dyadicShortIntervalLength D L ≤ D / L + 1 := by
  apply (ceilDiv_le_iff_le_mul hL).2
  calc
    D = L * (D / L) + D % L := (Nat.div_add_mod D L).symm
    _ ≤ L * (D / L) + L := by
      exact Nat.add_le_add_left (Nat.mod_lt D hL).le _
    _ = L * (D / L + 1) := by ring

/-- A full dyadic interval needs at most `L` quotient blocks when the block
length is `ceil(D/L)`. -/
theorem shortIntervalBlockCount_dyadic_le
    {D L : ℕ} (hD : 0 < D) (hL : 0 < L) :
    shortIntervalBlockCount D (2 * D) (dyadicShortIntervalLength D L) ≤ L := by
  apply shortIntervalBlockCount_le (dyadicShortIntervalLength_pos hD hL)
  have hcover : D ≤ L * dyadicShortIntervalLength D L := by
    exact (ceilDiv_le_iff_le_mul hL).1 le_rfl
  rw [Nat.mul_comm L] at hcover
  have hlength : 2 * D - D = D := by omega
  rw [hlength]
  exact hcover

/-- Total number of shorter blocks in the first `S` dyadic ranges. -/
def dyadicShortIntervalFamilyCount (S L : ℕ) : ℕ :=
  ∑ s ∈ Finset.range S,
    shortIntervalBlockCount (2 ^ s) (2 * 2 ^ s)
      (dyadicShortIntervalLength (2 ^ s) L)

/-- The source's finite family-count bookkeeping in exact form: at most `L`
short blocks for each of `S` dyadic ranges, hence at most `S*L` families. -/
theorem dyadicShortIntervalFamilyCount_le
    (S : ℕ) {L : ℕ} (hL : 0 < L) :
    dyadicShortIntervalFamilyCount S L ≤ S * L := by
  unfold dyadicShortIntervalFamilyCount
  calc
    ∑ s ∈ Finset.range S,
        shortIntervalBlockCount (2 ^ s) (2 * 2 ^ s)
          (dyadicShortIntervalLength (2 ^ s) L) ≤
        ∑ _s ∈ Finset.range S, L := by
      exact Finset.sum_le_sum fun s _hs =>
        shortIntervalBlockCount_dyadic_le (pow_pos (by omega) s) hL
    _ = S * L := by simp

/-- The dyadic band and short-block indices used to cover all positive
integers at most `B`.  The second range is rectangular; indices beyond the
actual ceiling block count simply name empty blocks. -/
def dyadicShortIntervalIndexBox (B L : ℕ) : Finset (ℕ × ℕ) :=
  Finset.range (Nat.log 2 B + 1) ×ˢ Finset.range L

/-- The short block named by a dyadic exponent and a within-band index. -/
def dyadicShortIntervalIndexedBlock (L : ℕ) (sk : ℕ × ℕ) : Finset ℕ :=
  shortIntervalBlock (2 ^ sk.1) (2 * 2 ^ sk.1)
    (dyadicShortIntervalLength (2 ^ sk.1) L) sk.2

/-- The canonical dyadic-band and within-band index of a natural number. -/
def dyadicShortIntervalIndex (L n : ℕ) : ℕ × ℕ :=
  let s := Nat.log 2 n
  let D := 2 ^ s
  (s, (n - D) / dyadicShortIntervalLength D L)

theorem card_dyadicShortIntervalIndexBox (B L : ℕ) :
    (dyadicShortIntervalIndexBox B L).card = (Nat.log 2 B + 1) * L := by
  simp [dyadicShortIntervalIndexBox]

/-- The canonical index of every positive integer in `[1,B]` is in the
rectangular index box and names a block containing that integer. -/
theorem dyadicShortIntervalIndex_spec
    {B L n : ℕ} (hL : 0 < L) (hn : 0 < n) (hnB : n ≤ B) :
    dyadicShortIntervalIndex L n ∈ dyadicShortIntervalIndexBox B L ∧
      n ∈ dyadicShortIntervalIndexedBlock L
        (dyadicShortIntervalIndex L n) := by
  let s := Nat.log 2 n
  let D := 2 ^ s
  let q := dyadicShortIntervalLength D L
  let k := (n - D) / q
  have hbounds : D ≤ n ∧ n < 2 * D := by
    constructor
    · exact Nat.pow_log_le_self 2 hn.ne'
    · simpa only [D, s, Nat.pow_succ, Nat.succ_eq_add_one,
        Nat.mul_comm] using
        (Nat.lt_pow_succ_log_self (by omega : 1 < 2) n)
  have hD : 0 < D := pow_pos (by omega) s
  have hq : 0 < q := dyadicShortIntervalLength_pos hD hL
  have hnIco : n ∈ Finset.Ico D (2 * D) := Finset.mem_Ico.mpr hbounds
  have hkCount : k < shortIntervalBlockCount D (2 * D) q :=
    shortIntervalBlock_index_lt hq hnIco
  have hkL : k < L := hkCount.trans_le
    (shortIntervalBlockCount_dyadic_le hD hL)
  have hsB : s < Nat.log 2 B + 1 := by
    exact lt_of_le_of_lt (Nat.log_mono_right hnB) (Nat.lt_succ_self _)
  have hindex : dyadicShortIntervalIndex L n = (s, k) := by
    rfl
  rw [hindex]
  constructor
  · simp [dyadicShortIntervalIndexBox, hsB, hkL]
  · rw [dyadicShortIntervalIndexedBlock, mem_shortIntervalBlock]
    exact ⟨hbounds.1, hbounds.2, rfl⟩

/-- Every positive integer in the ambient box `[1,B]` belongs to one of the
counted shorter-than-dyadic blocks. -/
theorem exists_mem_dyadicShortIntervalIndexedBlock
    {B L n : ℕ} (hL : 0 < L) (hn : 0 < n) (hnB : n ≤ B) :
    ∃ sk ∈ dyadicShortIntervalIndexBox B L,
      n ∈ dyadicShortIntervalIndexedBlock L sk := by
  exact ⟨dyadicShortIntervalIndex L n,
    (dyadicShortIntervalIndex_spec hL hn hnB).1,
    (dyadicShortIntervalIndex_spec hL hn hnB).2⟩

/-- Restrict a coefficient sequence to the fiber of one canonical dyadic
short-block index. -/
def dyadicShortIntervalCoefficient {A : Type*} [Zero A]
    (f : ℕ → A) (L : ℕ) (sk : ℕ × ℕ) (n : ℕ) : A :=
  if dyadicShortIntervalIndex L n = sk then f n else 0

/-- A nonzero indexed coefficient is supported in the corresponding literal
short block. -/
theorem mem_dyadicShortIntervalIndexedBlock_of_coefficient_ne_zero
    {A : Type*} [Zero A] (f : ℕ → A) {L n : ℕ} {sk : ℕ × ℕ}
    (hL : 0 < L) (hn : 0 < n)
    (hne : dyadicShortIntervalCoefficient f L sk n ≠ 0) :
    n ∈ dyadicShortIntervalIndexedBlock L sk := by
  have hindex : dyadicShortIntervalIndex L n = sk := by
    by_contra h
    simp [dyadicShortIntervalCoefficient, h] at hne
  subst sk
  exact (dyadicShortIntervalIndex_spec hL hn le_rfl).2

/-- Exact pointwise decomposition over the counted rectangular family for a
positive argument in the ambient box. -/
theorem sum_dyadicShortIntervalCoefficient
    {A : Type*} [AddCommMonoid A] (f : ℕ → A)
    {B L n : ℕ} (hL : 0 < L) (hn : 0 < n) (hnB : n ≤ B) :
    ∑ sk ∈ dyadicShortIntervalIndexBox B L,
        dyadicShortIntervalCoefficient f L sk n = f n := by
  classical
  let idx := dyadicShortIntervalIndex L n
  have hidx : idx ∈ dyadicShortIntervalIndexBox B L :=
    (dyadicShortIntervalIndex_spec hL hn hnB).1
  calc
    ∑ sk ∈ dyadicShortIntervalIndexBox B L,
        dyadicShortIntervalCoefficient f L sk n =
        dyadicShortIntervalCoefficient f L idx n := by
      apply Finset.sum_eq_single_of_mem idx hidx
      intro sk _hsk hne
      simp [dyadicShortIntervalCoefficient, idx, hne.symm]
    _ = f n := by simp [dyadicShortIntervalCoefficient, idx]

/-- Exact finite weighted-sum decomposition into the counted dyadic short
coefficient families. -/
theorem weightedSum_eq_sum_dyadicShortIntervalCoefficients
    {A : Type*} [CommSemiring A] (T : Finset ℕ) (w f : ℕ → A)
    {B L : ℕ} (hL : 0 < L)
    (hsupport : ∀ n, f n ≠ 0 → 0 < n ∧ n ≤ B) :
    ∑ n ∈ T, w n * f n =
      ∑ sk ∈ dyadicShortIntervalIndexBox B L,
        ∑ n ∈ T, w n * dyadicShortIntervalCoefficient f L sk n := by
  classical
  calc
    ∑ n ∈ T, w n * f n =
        ∑ n ∈ T, w n *
          (∑ sk ∈ dyadicShortIntervalIndexBox B L,
            dyadicShortIntervalCoefficient f L sk n) := by
      apply Finset.sum_congr rfl
      intro n _hn
      by_cases hf : f n = 0
      · simp [hf, dyadicShortIntervalCoefficient]
      · rw [sum_dyadicShortIntervalCoefficient f hL
          (hsupport n hf).1 (hsupport n hf).2]
    _ = ∑ n ∈ T, ∑ sk ∈ dyadicShortIntervalIndexBox B L,
          w n * dyadicShortIntervalCoefficient f L sk n := by
      simp_rw [Finset.mul_sum]
    _ = _ := by rw [Finset.sum_comm]

/-- The explicit strengthened logarithmic budget used for the source's
`log⁻¹⁰⁰`-scale subdivision.  The extra power absorbs integer rounding while
remaining polynomial-logarithmic. -/
def vaughanShortIntervalBudget (B : ℕ) : ℕ :=
  (Nat.log 2 B + 1) ^ 101

/-- The resulting rectangular family of all shorter dyadic blocks needed in
the positive ambient box `[1,B]`. -/
def vaughanShortIntervalIndexBox (B : ℕ) : Finset (ℕ × ℕ) :=
  dyadicShortIntervalIndexBox B (vaughanShortIntervalBudget B)

theorem vaughanShortIntervalBudget_pos (B : ℕ) :
    0 < vaughanShortIntervalBudget B := by
  exact pow_pos (by omega) 101

/-- Exact polynomial-logarithmic family count: the ambient box uses exactly
`(log₂ B + 1)^102` named short blocks. -/
theorem card_vaughanShortIntervalIndexBox (B : ℕ) :
    (vaughanShortIntervalIndexBox B).card = (Nat.log 2 B + 1) ^ 102 := by
  rw [vaughanShortIntervalIndexBox, card_dyadicShortIntervalIndexBox]
  simp only [vaughanShortIntervalBudget]
  ring

/-- Every positive coefficient index in `[1,B]` is covered by the explicit
polynomial-logarithmic Vaughan short family. -/
theorem exists_mem_vaughanShortIntervalIndexedBlock
    {B n : ℕ} (hn : 0 < n) (hnB : n ≤ B) :
    ∃ sk ∈ vaughanShortIntervalIndexBox B,
      n ∈ dyadicShortIntervalIndexedBlock
        (vaughanShortIntervalBudget B) sk := by
  exact exists_mem_dyadicShortIntervalIndexedBlock
    (vaughanShortIntervalBudget_pos B) hn hnB

/-- A coefficient restricted to one member of the explicit
polynomial-logarithmic Vaughan short family. -/
def vaughanShortIntervalCoefficient {A : Type*} [Zero A]
    (f : ℕ → A) (B : ℕ) (sk : ℕ × ℕ) (n : ℕ) : A :=
  dyadicShortIntervalCoefficient f (vaughanShortIntervalBudget B) sk n

theorem mem_vaughanShortIntervalIndexedBlock_of_coefficient_ne_zero
    {A : Type*} [Zero A] (f : ℕ → A) {B n : ℕ} {sk : ℕ × ℕ}
    (hn : 0 < n)
    (hne : vaughanShortIntervalCoefficient f B sk n ≠ 0) :
    n ∈ dyadicShortIntervalIndexedBlock
      (vaughanShortIntervalBudget B) sk := by
  exact mem_dyadicShortIntervalIndexedBlock_of_coefficient_ne_zero f
    (vaughanShortIntervalBudget_pos B) hn hne

theorem sum_vaughanShortIntervalCoefficient
    {A : Type*} [AddCommMonoid A] (f : ℕ → A)
    {B n : ℕ} (hn : 0 < n) (hnB : n ≤ B) :
    ∑ sk ∈ vaughanShortIntervalIndexBox B,
        vaughanShortIntervalCoefficient f B sk n = f n := by
  exact sum_dyadicShortIntervalCoefficient f
    (vaughanShortIntervalBudget_pos B) hn hnB

/-- Exact weighted decomposition into the explicit family of
`(log₂ B+1)^102` Vaughan short coefficients. -/
theorem weightedSum_eq_sum_vaughanShortIntervalCoefficients
    {A : Type*} [CommSemiring A] (T : Finset ℕ) (w f : ℕ → A)
    {B : ℕ} (hsupport : ∀ n, f n ≠ 0 → 0 < n ∧ n ≤ B) :
    ∑ n ∈ T, w n * f n =
      ∑ sk ∈ vaughanShortIntervalIndexBox B,
        ∑ n ∈ T, w n * vaughanShortIntervalCoefficient f B sk n := by
  exact weightedSum_eq_sum_dyadicShortIntervalCoefficients T w f
    (vaughanShortIntervalBudget_pos B) hsupport

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

/-- Two indices in one named dyadic short block differ by less than the ideal
relative length `D/L`, up to the unavoidable integer rounding term `+1`. -/
theorem natDist_lt_dyadic_div_add_one_of_mem_same_indexedBlock
    {L : ℕ} {sk : ℕ × ℕ} {x y : ℕ} (hL : 0 < L)
    (hx : x ∈ dyadicShortIntervalIndexedBlock L sk)
    (hy : y ∈ dyadicShortIntervalIndexedBlock L sk) :
    Nat.dist x y < 2 ^ sk.1 / L + 1 := by
  exact (natDist_lt_of_mem_same_shortIntervalBlock
    (dyadicShortIntervalLength_pos (pow_pos (by omega) sk.1) hL) hx hy).trans_le
      (dyadicShortIntervalLength_le_div_add_one (2 ^ sk.1) hL)

/-- The left endpoint of the literal natural interval named by a dyadic
short-block index. -/
def dyadicShortIntervalLeftEndpoint (L : ℕ) (sk : ℕ × ℕ) : ℕ :=
  2 ^ sk.1 + sk.2 * dyadicShortIntervalLength (2 ^ sk.1) L

/-- Membership in a named block places the index between its literal left
endpoint and that endpoint plus one block length. -/
theorem mem_dyadicShortIntervalIndexedBlock_bounds
    {L : ℕ} {sk : ℕ × ℕ} {n : ℕ} (hL : 0 < L)
    (hn : n ∈ dyadicShortIntervalIndexedBlock L sk) :
    dyadicShortIntervalLeftEndpoint L sk ≤ n ∧
      n < dyadicShortIntervalLeftEndpoint L sk +
        dyadicShortIntervalLength (2 ^ sk.1) L := by
  rw [dyadicShortIntervalIndexedBlock, mem_shortIntervalBlock] at hn
  let D := 2 ^ sk.1
  let q := dyadicShortIntervalLength D L
  have hq : 0 < q := dyadicShortIntervalLength_pos (pow_pos (by omega) sk.1) hL
  have hmod : (n - D) % q < q := Nat.mod_lt _ hq
  have hrepr : n - D = ((n - D) / q) * q + (n - D) % q := by
    simpa only [Nat.mul_comm] using (Nat.div_add_mod (n - D) q).symm
  have hnrepr : n = D + (n - D) := by omega
  change D + sk.2 * q ≤ n ∧ n < D + sk.2 * q + q
  rw [hnrepr, hrepr, hn.2.2]
  omega

/-- The natural logarithm of a positive integer is bounded by its
base-two integer logarithm plus one. -/
theorem realLog_nat_le_logTwo_add_one (B : ℕ) (hB : 0 < B) :
    Real.log B ≤ (Nat.log 2 B + 1 : ℝ) := by
  let S := Nat.log 2 B + 1
  have hnat : B < 2 ^ S := by
    simpa only [S, Nat.succ_eq_add_one] using
      (Nat.lt_pow_succ_log_self (by omega : 1 < 2) B)
  have hcast : (B : ℝ) < (2 ^ S : ℕ) := by exact_mod_cast hnat
  have hBlog : Real.log B < Real.log ((2 ^ S : ℕ) : ℝ) := by
    exact Real.strictMonoOn_log
      (show 0 < (B : ℝ) by exact_mod_cast hB)
      (show 0 < ((2 ^ S : ℕ) : ℝ) by
        exact_mod_cast (pow_pos (by omega : 0 < (2 : ℕ)) S)) hcast
  have hlogtwo : Real.log (2 : ℝ) ≤ 1 := by
    nlinarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact le_of_lt <| calc
    Real.log B < Real.log ((2 ^ S : ℕ) : ℝ) := hBlog
    _ = (S : ℝ) * Real.log 2 := by
      rw [Nat.cast_pow, Real.log_pow]
      norm_num
    _ ≤ (S : ℝ) * 1 := mul_le_mul_of_nonneg_left hlogtwo (by positivity)
    _ = (Nat.log 2 B + 1 : ℝ) := by simp [S]

/-- The standing source threshold `2 ≤ log B` already makes the common
Vaughan subdivision budget larger than the fixed coefficient needed by the
quadratic four-step near/far argument. -/
theorem four_mul_quadraticWeylCoefficient_le_vaughanShortIntervalBudget
    {B : ℕ} (hB : 0 < B) (hlog : 2 ≤ Real.log B) :
    4 * (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ))) ≤
      (vaughanShortIntervalBudget B : ℝ) := by
  let S : ℕ := Nat.log 2 B + 1
  have hlogS : (2 : ℝ) ≤ (S : ℝ) := by
    exact hlog.trans (by
      simpa only [S, Nat.cast_add, Nat.cast_one] using
        realLog_nat_le_logTwo_add_one B hB)
  have hpow : (2 : ℝ) ^ 101 ≤ (S : ℝ) ^ 101 :=
    pow_le_pow_left₀ (by norm_num) hlogS 101
  have hconstant :
      4 * (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ))) ≤ (2 : ℝ) ^ 101 := by
    norm_num
  calc
    4 * (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ))) ≤ (2 : ℝ) ^ 101 := hconstant
    _ ≤ (S : ℝ) ^ 101 := hpow
    _ = (vaughanShortIntervalBudget B : ℝ) := by
      simp only [S, vaughanShortIntervalBudget, Nat.cast_pow]

/-- On dyadic scales at least the strengthened budget, the rounded natural
block length is at most the source's literal `D / log(B)^100` length. -/
theorem vaughanShortIntervalLength_cast_le_realLog
    {B D : ℕ} (hB : 0 < B) (hlog : 2 ≤ Real.log B)
    (hD : (vaughanShortIntervalBudget B : ℝ) ≤ (D : ℝ)) :
    (dyadicShortIntervalLength D (vaughanShortIntervalBudget B) : ℝ) ≤
      (D : ℝ) / (Real.log B) ^ 100 := by
  let S : ℕ := Nat.log 2 B + 1
  let R : ℝ := Real.log B
  have hLpos : 0 < vaughanShortIntervalBudget B :=
    vaughanShortIntervalBudget_pos B
  have hLposR : (0 : ℝ) < (vaughanShortIntervalBudget B : ℝ) := by
    exact_mod_cast hLpos
  have hceil := dyadicShortIntervalLength_le_div_add_one D hLpos
  have hceilR :
      (dyadicShortIntervalLength D (vaughanShortIntervalBudget B) : ℝ) ≤
        ((D / vaughanShortIntervalBudget B : ℕ) : ℝ) + 1 := by
    exact_mod_cast hceil
  have hnatdiv : ((D / vaughanShortIntervalBudget B : ℕ) : ℝ) ≤
      (D : ℝ) / (vaughanShortIntervalBudget B : ℝ) := Nat.cast_div_le
  have hLcast : (vaughanShortIntervalBudget B : ℝ) =
      (S : ℝ) ^ 101 := by
    rw [vaughanShortIntervalBudget, Nat.cast_pow]
  have hSR : R ≤ (S : ℝ) := by
    simpa only [R, S, Nat.cast_add, Nat.cast_one] using
      realLog_nat_le_logTwo_add_one B hB
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) hlog
  have hpowRS : R ^ 101 ≤ (S : ℝ) ^ 101 :=
    pow_le_pow_left₀ hRpos.le hSR 101
  have hone : (1 : ℝ) ≤
      (D : ℝ) / (vaughanShortIntervalBudget B : ℝ) := by
    rw [le_div_iff₀ hLposR]
    simpa only [one_mul] using hD
  have hdiv : (D : ℝ) / (vaughanShortIntervalBudget B : ℝ) ≤
      (D : ℝ) / R ^ 101 := by
    apply div_le_div_of_nonneg_left
      (show (0 : ℝ) ≤ (D : ℝ) by exact_mod_cast (Nat.zero_le D))
      (pow_pos hRpos 101)
    exact hpowRS.trans_eq hLcast.symm
  have hlast : 2 * ((D : ℝ) / R ^ 101) ≤
      (D : ℝ) / R ^ 100 := by
    have hratio : 2 / R ≤ (1 : ℝ) := (div_le_one hRpos).2 hlog
    calc
      2 * ((D : ℝ) / R ^ 101) =
          ((D : ℝ) / R ^ 100) * (2 / R) := by
        rw [pow_succ]
        field_simp
      _ ≤ ((D : ℝ) / R ^ 100) * 1 :=
        mul_le_mul_of_nonneg_left hratio
          (div_nonneg (by exact_mod_cast (Nat.zero_le D))
            (pow_nonneg hRpos.le 100))
      _ = (D : ℝ) / R ^ 100 := mul_one _
  calc
    (dyadicShortIntervalLength D (vaughanShortIntervalBudget B) : ℝ) ≤
        ((D / vaughanShortIntervalBudget B : ℕ) : ℝ) + 1 := hceilR
    _ ≤ (D : ℝ) / (vaughanShortIntervalBudget B : ℝ) + 1 := by
      linarith
    _ ≤ 2 * ((D : ℝ) / (vaughanShortIntervalBudget B : ℝ)) := by
      linarith
    _ ≤ 2 * ((D : ℝ) / R ^ 101) := by gcongr
    _ ≤ (D : ℝ) / R ^ 100 := hlast
    _ = (D : ℝ) / (Real.log B) ^ 100 := rfl

/-- The source's logarithmic short-block width converts a low-frequency
upper bound into the scale-error inequality needed by the quadratic Type II
estimate.  The endpoint `R` may be any real number above the dyadic left
endpoint `D`; in the canonical application it is the left endpoint of the
selected inner short block. -/
theorem ten_mul_vaughanShortIntervalLength_mul_le_pow_four_mul
    {B D : ℕ} {F K R : ℝ}
    (hB : 0 < B) (hlog : 2 ≤ Real.log B)
    (hD : (vaughanShortIntervalBudget B : ℝ) ≤ (D : ℝ))
    (hFlow : 10 * F ≤ K ^ 4 * (Real.log B) ^ 100)
    (hDR : (D : ℝ) ≤ R) :
    10 * (dyadicShortIntervalLength D
      (vaughanShortIntervalBudget B) : ℝ) * F ≤ K ^ 4 * R := by
  have hq := vaughanShortIntervalLength_cast_le_realLog hB hlog hD
  have hlogPos : 0 < Real.log B := lt_of_lt_of_le (by norm_num) hlog
  have hlogPowPos : 0 < (Real.log B) ^ 100 := pow_pos hlogPos 100
  calc
    10 * (dyadicShortIntervalLength D
        (vaughanShortIntervalBudget B) : ℝ) * F =
        (dyadicShortIntervalLength D
          (vaughanShortIntervalBudget B) : ℝ) * (10 * F) := by ring
    _ ≤ (dyadicShortIntervalLength D
          (vaughanShortIntervalBudget B) : ℝ) *
        (K ^ 4 * (Real.log B) ^ 100) :=
      mul_le_mul_of_nonneg_left hFlow (by positivity)
    _ ≤ ((D : ℝ) / (Real.log B) ^ 100) *
        (K ^ 4 * (Real.log B) ^ 100) :=
      mul_le_mul_of_nonneg_right hq
        (mul_nonneg (by positivity) hlogPowPos.le)
    _ = K ^ 4 * (D : ℝ) := by field_simp
    _ ≤ K ^ 4 * R := mul_le_mul_of_nonneg_left hDR (by positivity)

/-- On every dyadic band above the Vaughan subdivision budget, the source's
logarithmic relative width is more than enough for five copies of the rounded
block length to fit inside the band. -/
theorem five_mul_vaughanShortIntervalLength_cast_le
    {B D : ℕ} (hB : 0 < B) (hlog : 2 ≤ Real.log B)
    (hD : (vaughanShortIntervalBudget B : ℝ) ≤ (D : ℝ)) :
    5 * (dyadicShortIntervalLength D (vaughanShortIntervalBudget B) : ℝ) ≤
      (D : ℝ) := by
  have hq := vaughanShortIntervalLength_cast_le_realLog hB hlog hD
  have hlogPos : 0 < Real.log B := lt_of_lt_of_le (by norm_num) hlog
  have hpowTwo : (2 : ℝ) ^ 100 ≤ (Real.log B) ^ 100 :=
    pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hlog 100
  have hfive : (5 : ℝ) ≤ (Real.log B) ^ 100 := by
    exact (by norm_num : (5 : ℝ) ≤ 2 ^ 100).trans hpowTwo
  have hratio : 5 / (Real.log B) ^ 100 ≤ (1 : ℝ) :=
    (div_le_one (pow_pos hlogPos 100)).2 hfive
  calc
    5 * (dyadicShortIntervalLength D (vaughanShortIntervalBudget B) : ℝ) ≤
        5 * ((D : ℝ) / (Real.log B) ^ 100) :=
      mul_le_mul_of_nonneg_left hq (by norm_num)
    _ = (D : ℝ) * (5 / (Real.log B) ^ 100) := by ring
    _ ≤ (D : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hratio (Nat.cast_nonneg D)
    _ = (D : ℝ) := mul_one _

/-- Every named Vaughan block has the source's literal relative
`log(B)^{-100}` support width.  Small dyadic bands are singleton blocks;
large bands use the extra logarithmic subdivision power to absorb ceiling
rounding. -/
theorem mem_vaughanShortIntervalIndexedBlock_realLog_bounds
    {B n : ℕ} {sk : ℕ × ℕ} (hB : 0 < B)
    (hlog : 2 ≤ Real.log B)
    (hn : n ∈ dyadicShortIntervalIndexedBlock
      (vaughanShortIntervalBudget B) sk) :
    let M := dyadicShortIntervalLeftEndpoint
      (vaughanShortIntervalBudget B) sk
    (M : ℝ) ≤ (n : ℝ) ∧
      (n : ℝ) < (1 + ((Real.log B) ^ 100)⁻¹) * M := by
  let L := vaughanShortIntervalBudget B
  let D := 2 ^ sk.1
  let q := dyadicShortIntervalLength D L
  let M := dyadicShortIntervalLeftEndpoint L sk
  have hL : 0 < L := vaughanShortIntervalBudget_pos B
  have hq : 0 < q := dyadicShortIntervalLength_pos (pow_pos (by omega) sk.1) hL
  have hbounds := mem_dyadicShortIntervalIndexedBlock_bounds hL hn
  have hMpos : 0 < M := by
    have hDM : D ≤ M := by
      dsimp only [M, dyadicShortIntervalLeftEndpoint, D, L]
      omega
    exact (pow_pos (by omega : 0 < (2 : ℕ)) sk.1).trans_le hDM
  have hRpos : 0 < Real.log B := lt_of_lt_of_le (by norm_num) hlog
  constructor
  · exact_mod_cast hbounds.1
  · by_cases hDL : L ≤ D
    · have hDLR : (L : ℝ) ≤ (D : ℝ) := by exact_mod_cast hDL
      have hqReal : (q : ℝ) ≤ (D : ℝ) / (Real.log B) ^ 100 := by
        exact vaughanShortIntervalLength_cast_le_realLog hB hlog hDLR
      have hDM : D ≤ M := by
        dsimp only [M, dyadicShortIntervalLeftEndpoint, D, L]
        omega
      have hdiv : (D : ℝ) / (Real.log B) ^ 100 ≤
          (M : ℝ) / (Real.log B) ^ 100 := by
        exact div_le_div_of_nonneg_right (by exact_mod_cast hDM)
          (pow_nonneg hRpos.le 100)
      have hnupper : (n : ℝ) < (M : ℝ) + (q : ℝ) := by
        exact_mod_cast hbounds.2
      calc
        (n : ℝ) < (M : ℝ) + (q : ℝ) := hnupper
        _ ≤ (M : ℝ) + (M : ℝ) / (Real.log B) ^ 100 := by
          linarith
        _ = (1 + ((Real.log B) ^ 100)⁻¹) * M := by
          simp only [div_eq_mul_inv]
          ring
    · have hDlt : D < L := Nat.lt_of_not_ge hDL
      have hqle : q ≤ 1 := by
        have := dyadicShortIntervalLength_le_div_add_one D hL
        simpa only [q, Nat.div_eq_of_lt hDlt, zero_add] using this
      have hqeq : q = 1 := by omega
      have hbounds' : M ≤ n ∧ n < M + q := by
        simpa only [M, q, L, D] using hbounds
      have hnM : n = M := by
        rw [hqeq] at hbounds'
        omega
      rw [hnM]
      have hterm : 0 < (((Real.log B) ^ 100)⁻¹ : ℝ) * M :=
        mul_pos (inv_pos.mpr (pow_pos hRpos 100)) (by exact_mod_cast hMpos)
      calc
        (M : ℝ) = (M : ℝ) + 0 := (add_zero _).symm
        _ < (M : ℝ) + ((Real.log B) ^ 100)⁻¹ * M :=
          add_lt_add_right hterm _
        _ = (1 + ((Real.log B) ^ 100)⁻¹) * M := by ring

/-- Direct source-support form for every nonzero restricted coefficient. -/
theorem vaughanShortIntervalCoefficient_realLog_support
    {A : Type*} [Zero A] (f : ℕ → A) {B n : ℕ} {sk : ℕ × ℕ}
    (hB : 0 < B) (hlog : 2 ≤ Real.log B) (hn : 0 < n)
    (hne : vaughanShortIntervalCoefficient f B sk n ≠ 0) :
    let M := dyadicShortIntervalLeftEndpoint
      (vaughanShortIntervalBudget B) sk
    (M : ℝ) ≤ (n : ℝ) ∧
      (n : ℝ) < (1 + ((Real.log B) ^ 100)⁻¹) * M := by
  exact mem_vaughanShortIntervalIndexedBlock_realLog_bounds hB hlog
    (mem_vaughanShortIntervalIndexedBlock_of_coefficient_ne_zero f hn hne)

/-- Source-scale version: if the coefficient cutoff `B` dominates the prime
scale `P`, the stronger `log(B)^{-100}` block width implies the paper's
literal `log(P)^{-100}` support width. -/
theorem vaughanShortIntervalCoefficient_realLogScale_support
    {A : Type*} [Zero A] (f : ℕ → A) {P B n : ℕ} {sk : ℕ × ℕ}
    (hP : 0 < P) (hPB : P ≤ B) (hlogP : 2 ≤ Real.log P) (hn : 0 < n)
    (hne : vaughanShortIntervalCoefficient f B sk n ≠ 0) :
    let M := dyadicShortIntervalLeftEndpoint
      (vaughanShortIntervalBudget B) sk
    (M : ℝ) ≤ (n : ℝ) ∧
      (n : ℝ) < (1 + ((Real.log P) ^ 100)⁻¹) * M := by
  let M := dyadicShortIntervalLeftEndpoint (vaughanShortIntervalBudget B) sk
  have hB : 0 < B := hP.trans_le hPB
  have hlogPB : Real.log P ≤ Real.log B := by
    exact Real.strictMonoOn_log.monotoneOn
      (show (0 : ℝ) < (P : ℝ) by exact_mod_cast hP)
      (show (0 : ℝ) < (B : ℝ) by exact_mod_cast hB)
      (by exact_mod_cast hPB)
  have hlogB : 2 ≤ Real.log B := hlogP.trans hlogPB
  have hbase := vaughanShortIntervalCoefficient_realLog_support
    f hB hlogB hn hne
  have hlogPpos : 0 < Real.log P := lt_of_lt_of_le (by norm_num) hlogP
  have hpow : (Real.log P) ^ 100 ≤ (Real.log B) ^ 100 :=
    pow_le_pow_left₀ hlogPpos.le hlogPB 100
  have hinv : ((Real.log B) ^ 100)⁻¹ ≤ ((Real.log P) ^ 100)⁻¹ := by
    simpa only [one_div] using
      one_div_le_one_div_of_le (pow_pos hlogPpos 100) hpow
  constructor
  · exact hbase.1
  · exact hbase.2.trans_le <| by
      apply mul_le_mul_of_nonneg_right
      · exact add_le_add_right hinv 1
      · exact_mod_cast (Nat.zero_le M)

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
