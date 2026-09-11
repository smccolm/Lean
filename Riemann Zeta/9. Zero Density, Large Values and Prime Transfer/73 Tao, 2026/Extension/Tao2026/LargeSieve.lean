import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Int.CardIntervalMod

/-!
# Finite Fourier foundations for Tao's large sieve

This file begins the native proof of the analytic large-sieve input required
by Section 2.  It derives Parseval for Mathlib's unnormalised DFT on `ZMod N`
from Fourier inversion and then proves the exact one-modulus Montgomery
uncertainty inequality.  No large-sieve or Selberg-sieve estimate is imported
as an assumption.
-/

open Finset AddChar
open scoped ZMod ComplexConjugate

namespace Tao2026

noncomputable section

variable {N : ℕ} [NeZero N]

/-- The unnormalised DFT is self-adjoint for the bilinear (not Hermitian)
finite pairing. -/
theorem sum_dft_mul_eq_sum_mul_dft (Φ Ψ : ZMod N → ℂ) :
    ∑ k : ZMod N, ZMod.dft Φ k * Ψ k =
      ∑ j : ZMod N, Φ j * ZMod.dft Ψ j := by
  simp only [ZMod.dft_apply, smul_eq_mul, sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro k _
  rw [mul_comm j k]
  ring

/-- Conjugation reverses the DFT frequency. -/
theorem dft_conj (Φ : ZMod N → ℂ) (k : ZMod N) :
    ZMod.dft (fun j => conj (Φ j)) k = conj (ZMod.dft Φ (-k)) := by
  simp only [ZMod.dft_apply, smul_eq_mul, map_sum, map_mul]
  apply sum_congr rfl
  intro j _
  simp only [mul_neg, neg_neg]
  congr 1
  change (↑(ZMod.stdAddChar (-(j * k))) : ℂ) =
    conj (↑(ZMod.stdAddChar (j * k)) : ℂ)
  rw [AddChar.map_neg_eq_conj]

/-- Complex-valued Parseval identity for the unnormalised DFT. -/
theorem dft_parseval_complex (Φ : ZMod N → ℂ) :
    ∑ k : ZMod N, ZMod.dft Φ k * conj (ZMod.dft Φ k) =
      (N : ℂ) * ∑ j : ZMod N, Φ j * conj (Φ j) := by
  rw [sum_dft_mul_eq_sum_mul_dft Φ (fun k => conj (ZMod.dft Φ k))]
  rw [mul_sum]
  apply sum_congr rfl
  intro j _
  rw [dft_conj]
  rw [congr_fun (ZMod.dft_dft Φ) (-j)]
  simp
  ring

/-- Real norm-square form of Parseval. -/
theorem dft_parseval_normSq (Φ : ZMod N → ℂ) :
    ∑ k : ZMod N, Complex.normSq (ZMod.dft Φ k) =
      N * ∑ j : ZMod N, Complex.normSq (Φ j) := by
  have h := dft_parseval_complex Φ
  simp only [Complex.mul_conj] at h
  exact_mod_cast h

/-- Finite Cauchy--Schwarz in the norm-square form used by the uncertainty
principle. -/
theorem normSq_sum_le_card_mul_sum_normSq
    {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℂ) :
    Complex.normSq (∑ i ∈ s, f i) ≤
      (s.card : ℝ) * ∑ i ∈ s, Complex.normSq (f i) := by
  rw [← Complex.sq_norm]
  calc
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (∑ i ∈ s, ‖f i‖) ^ 2 := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    _ = (s.card : ℝ) * ∑ i ∈ s, Complex.normSq (f i) := by
      simp only [Complex.sq_norm]

/-- A function vanishing on `S` has the same total sum as its restriction to
the complementary residue classes. -/
theorem sum_eq_sum_compl_of_eq_zero
    {S : Finset (ZMod N)} {Φ : ZMod N → ℂ}
    (hzero : ∀ j ∈ S, Φ j = 0) :
    ∑ j : ZMod N, Φ j = ∑ j ∈ Sᶜ, Φ j := by
  rw [← S.sum_add_sum_compl Φ]
  have : ∑ j ∈ S, Φ j = 0 := by
    exact Finset.sum_eq_zero fun j hj => hzero j hj
  rw [this, zero_add]

/-- Montgomery's uncertainty principle for one modulus.  If `Φ` vanishes on
`#S` residue classes, the energy at nonzero frequencies is at least
`#S / #(Sᶜ)` times the squared zero-frequency mass. -/
theorem montgomery_uncertainty_one
    (S : Finset (ZMod N)) (Φ : ZMod N → ℂ)
    (hproper : S.card < N)
    (hzero : ∀ j ∈ S, Φ j = 0) :
    (S.card : ℝ) / (Sᶜ.card : ℝ) *
        Complex.normSq (∑ j : ZMod N, Φ j) ≤
      ∑ k ∈ (Finset.univ.erase (0 : ZMod N)),
        Complex.normSq (ZMod.dft Φ k) := by
  have hcard : Sᶜ.card + S.card = N := by
    rw [Finset.card_compl, ZMod.card]
    omega
  have hcompPosNat : 0 < Sᶜ.card := by omega
  have hcompPos : (0 : ℝ) < Sᶜ.card := by exact_mod_cast hcompPosNat
  have henergy : Complex.normSq (∑ j : ZMod N, Φ j) ≤
      (Sᶜ.card : ℝ) * ∑ j : ZMod N, Complex.normSq (Φ j) := by
    rw [sum_eq_sum_compl_of_eq_zero hzero]
    calc
      Complex.normSq (∑ j ∈ Sᶜ, Φ j) ≤
          (Sᶜ.card : ℝ) * ∑ j ∈ Sᶜ, Complex.normSq (Φ j) :=
        normSq_sum_le_card_mul_sum_normSq Sᶜ Φ
      _ ≤ (Sᶜ.card : ℝ) * ∑ j : ZMod N, Complex.normSq (Φ j) := by
        apply mul_le_mul_of_nonneg_left
        · exact Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.subset_univ _)
            (fun _ _ _ => Complex.normSq_nonneg _)
        · exact Nat.cast_nonneg _
  have hparseval := dft_parseval_normSq Φ
  have hzeroFreq : Complex.normSq (ZMod.dft Φ 0) =
      Complex.normSq (∑ j : ZMod N, Φ j) := by
    rw [ZMod.dft_apply_zero]
  have hdecomp :
      (∑ k ∈ (Finset.univ.erase (0 : ZMod N)),
        Complex.normSq (ZMod.dft Φ k)) +
          Complex.normSq (∑ j : ZMod N, Φ j) =
        (N : ℝ) * ∑ j : ZMod N, Complex.normSq (Φ j) := by
    rw [← hparseval, ← hzeroFreq]
    exact Finset.sum_erase_add _ _ (by simp)
  rw [div_mul_eq_mul_div, div_le_iff₀ hcompPos]
  have hcardReal : (Sᶜ.card : ℝ) + S.card = N := by exact_mod_cast hcard
  have hNnonneg : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hbase : 0 ≤ (Sᶜ.card : ℝ) *
      (∑ j : ZMod N, Complex.normSq (Φ j)) -
        Complex.normSq (∑ j : ZMod N, Φ j) := sub_nonneg.mpr henergy
  have hR : (∑ k ∈ (Finset.univ.erase (0 : ZMod N)),
      Complex.normSq (ZMod.dft Φ k)) =
        (N : ℝ) * (∑ j : ZMod N, Complex.normSq (Φ j)) -
          Complex.normSq (∑ j : ZMod N, Φ j) := by linarith
  rw [hR]
  have hnonneg := mul_nonneg hNnonneg hbase
  rw [← hcardReal] at hnonneg ⊢
  nlinarith

/-! ## Passage from finite integer support to residue-class sums -/

/-- Aggregate a finitely supported integer function in one residue class. -/
def residueClassSum
    (s : Finset ℕ) (f : ℕ → ℂ) (r : ZMod N) : ℂ :=
  (s.filter fun n : ℕ => (n : ZMod N) = r).sum f

/-- Residue aggregation preserves the total finite sum. -/
theorem sum_residueClassSum (s : Finset ℕ) (f : ℕ → ℂ) :
    ∑ r : ZMod N, residueClassSum s f r = ∑ n ∈ s, f n := by
  unfold residueClassSum
  exact Finset.sum_fiberwise_of_maps_to
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _) f

/-- The DFT of the residue aggregation is the original finite exponential
sum at the corresponding rational frequency. -/
theorem dft_residueClassSum
    (s : Finset ℕ) (f : ℕ → ℂ) (k : ZMod N) :
    ZMod.dft (residueClassSum s f) k =
      ∑ n ∈ s, ZMod.stdAddChar (-((n : ZMod N) * k)) * f n := by
  simp only [ZMod.dft_apply, smul_eq_mul, residueClassSum, mul_sum]
  calc
    ∑ r : ZMod N,
        (s.filter fun n : ℕ => (n : ZMod N) = r).sum
          (fun n => ZMod.stdAddChar (-(r * k)) * f n) =
      ∑ r : ZMod N,
        (s.filter fun n : ℕ => (n : ZMod N) = r).sum
          (fun n => ZMod.stdAddChar (-((n : ZMod N) * k)) * f n) := by
      apply sum_congr rfl
      intro r _
      apply sum_congr rfl
      intro n hn
      rw [(Finset.mem_filter.mp hn).2]
    _ = _ := by
      exact Finset.sum_fiberwise_of_maps_to
        (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
        (fun n : ℕ => ZMod.stdAddChar (-((n : ZMod N) * k)) * f n)

/-- Sum of squared residue-class aggregates, bounded by a uniform residue
fiber multiplicity. -/
theorem sum_normSq_residueClassSum_le
    (s : Finset ℕ) (f : ℕ → ℂ) (M : ℕ)
    (hM : ∀ r : ZMod N,
      (s.filter fun n : ℕ => (n : ZMod N) = r).card ≤ M) :
    (∑ r : ZMod N, Complex.normSq (residueClassSum s f r)) ≤
      M * ∑ n ∈ s, Complex.normSq (f n) := by
  calc
    ∑ r : ZMod N, Complex.normSq (residueClassSum s f r) ≤
        ∑ r : ZMod N,
          M * ∑ n ∈ s.filter (fun n : ℕ => (n : ZMod N) = r),
            Complex.normSq (f n) := by
      apply sum_le_sum
      intro r hr
      unfold residueClassSum
      calc
        Complex.normSq
            ((s.filter fun n : ℕ => (n : ZMod N) = r).sum f) ≤
          ((s.filter fun n : ℕ => (n : ZMod N) = r).card : ℝ) *
            ∑ n ∈ s.filter (fun n : ℕ => (n : ZMod N) = r),
              Complex.normSq (f n) :=
            normSq_sum_le_card_mul_sum_normSq _ f
        _ ≤ M * ∑ n ∈ s.filter (fun n : ℕ => (n : ZMod N) = r),
              Complex.normSq (f n) := by
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast hM r
          · exact Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
    _ = M * ∑ r : ZMod N,
          ∑ n ∈ s.filter (fun n : ℕ => (n : ZMod N) = r),
            Complex.normSq (f n) := by rw [mul_sum]
    _ = M * ∑ n ∈ s, Complex.normSq (f n) := by
      congr 1
      exact Finset.sum_fiberwise_of_maps_to
        (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
        (fun n => Complex.normSq (f n))

/-- Complete cyclic DFT energy, bounded by a residue-fiber multiplicity. -/
theorem dft_energy_le_of_fiber_card_le
    (s : Finset ℕ) (f : ℕ → ℂ) (M : ℕ)
    (hM : ∀ r : ZMod N,
      (s.filter fun n : ℕ => (n : ZMod N) = r).card ≤ M) :
    (∑ k : ZMod N,
        Complex.normSq (ZMod.dft (residueClassSum s f) k)) ≤
      N * M * ∑ n ∈ s, Complex.normSq (f n) := by
  rw [dft_parseval_normSq]
  calc
    (N : ℝ) * ∑ r : ZMod N,
        Complex.normSq (residueClassSum s f r) ≤
      (N : ℝ) * (M * ∑ n ∈ s, Complex.normSq (f n)) := by
        gcongr
        exact sum_normSq_residueClassSum_le s f M hM
    _ = _ := by ring

/-- Any selected cyclic frequency energy obeys the same upper bound. -/
theorem dft_subset_energy_le_of_fiber_card_le
    (s : Finset ℕ) (f : ℕ → ℂ) (K : Finset (ZMod N)) (M : ℕ)
    (hM : ∀ r : ZMod N,
      (s.filter fun n : ℕ => (n : ZMod N) = r).card ≤ M) :
    (∑ k ∈ K,
        Complex.normSq (ZMod.dft (residueClassSum s f) k)) ≤
      N * M * ∑ n ∈ s, Complex.normSq (f n) := by
  calc
    (∑ k ∈ K,
        Complex.normSq (ZMod.dft (residueClassSum s f) k)) ≤
      ∑ k : ZMod N,
        Complex.normSq (ZMod.dft (residueClassSum s f) k) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.subset_univ _
          · intro k hk hnot
            exact Complex.normSq_nonneg _
    _ ≤ _ := dft_energy_le_of_fiber_card_le s f M hM

/-- A subset of `[0,x]` occupies any fixed residue class modulo `N` at most
`⌊(x+1)/N⌋+1` times. -/
theorem residueFiber_card_le_div_add_one
    {s : Finset ℕ} {x : ℕ} (hs : s ⊆ Finset.Icc 0 x)
    (r : ZMod N) :
    (s.filter fun n : ℕ => (n : ZMod N) = r).card ≤
      (x + 1) / N + 1 := by
  calc
    (s.filter fun n : ℕ => (n : ZMod N) = r).card ≤
        ((Finset.range (x + 1)).filter
          fun n => n ≡ r.val [MOD N]).card := by
      apply Finset.card_le_card
      intro n hn
      have hnf := Finset.mem_filter.mp hn
      apply Finset.mem_filter.mpr
      constructor
      · rw [Finset.mem_range]
        have hnx := (Finset.mem_Icc.mp (hs hnf.1)).2
        omega
      · rw [← ZMod.natCast_eq_natCast_iff]
        simpa only [ZMod.natCast_zmod_val] using hnf.2
    _ = (x + 1) / N + if r.val % N < (x + 1) % N then 1 else 0 := by
      rw [← Nat.count_eq_card_filter_range,
        Nat.count_modEq_card (x + 1) (NeZero.pos N) r.val]
    _ ≤ (x + 1) / N + 1 := by split_ifs <;> omega

/-- Cyclic large-sieve upper bound for frequencies sharing denominator `N`
and a sequence supported in `[0,x]`. -/
theorem dft_subset_energy_le_interval
    {s : Finset ℕ} {x : ℕ} (hs : s ⊆ Finset.Icc 0 x)
    (f : ℕ → ℂ) (K : Finset (ZMod N)) :
    (∑ k ∈ K,
        Complex.normSq (ZMod.dft (residueClassSum s f) k)) ≤
      ((N * ((x + 1) / N + 1) : ℕ) : ℝ) *
        ∑ n ∈ s, Complex.normSq (f n) := by
  simpa only [Nat.cast_mul] using
    dft_subset_energy_le_of_fiber_card_le s f K _
      (residueFiber_card_le_div_add_one hs)

omit [NeZero N] in
/-- Vanishing on selected integer residue classes passes to the aggregate. -/
theorem residueClassSum_eq_zero
    {s : Finset ℕ} {f : ℕ → ℂ} {S : Finset (ZMod N)}
    (hzero : ∀ n ∈ s, (n : ZMod N) ∈ S → f n = 0) :
    ∀ r ∈ S, residueClassSum s f r = 0 := by
  intro r hr
  unfold residueClassSum
  apply Finset.sum_eq_zero
  intro n hn
  exact hzero n (Finset.mem_filter.mp hn).1
    ((Finset.mem_filter.mp hn).2 ▸ hr)

/-- Exact one-modulus form of Tao's Lemma 2.6 for a function with explicit
finite integer support. -/
theorem montgomery_uncertainty_one_finite
    (s : Finset ℕ) (f : ℕ → ℂ) (S : Finset (ZMod N))
    (hproper : S.card < N)
    (hzero : ∀ n ∈ s, (n : ZMod N) ∈ S → f n = 0) :
    (S.card : ℝ) / (Sᶜ.card : ℝ) *
        Complex.normSq (∑ n ∈ s, f n) ≤
      ∑ k ∈ (Finset.univ.erase (0 : ZMod N)),
        Complex.normSq
          (∑ n ∈ s,
            ZMod.stdAddChar (-((n : ZMod N) * k)) * f n) := by
  simpa only [sum_residueClassSum, dft_residueClassSum] using
    montgomery_uncertainty_one S (residueClassSum s f) hproper
      (residueClassSum_eq_zero hzero)

/-! ## Tensorization to two moduli -/

section TwoModuli

variable {M : ℕ} [NeZero M]

/-- The product DFT on two cyclic residue spaces. -/
def twoDimensionalDft
    (Φ : ZMod N → ZMod M → ℂ) (k : ZMod N) (l : ZMod M) : ℂ :=
  ∑ i : ZMod N, ∑ j : ZMod M,
    ZMod.stdAddChar (-(i * k)) * ZMod.stdAddChar (-(j * l)) * Φ i j

/-- DFT in the first residue coordinate only. -/
def firstCoordinateDft
    (Φ : ZMod N → ZMod M → ℂ) (k : ZMod N) (j : ZMod M) : ℂ :=
  ZMod.dft (fun i => Φ i j) k

/-- Summing a first-coordinate DFT over the second coordinate is the DFT of
the corresponding row sums. -/
theorem sum_firstCoordinateDft
    (Φ : ZMod N → ZMod M → ℂ) (k : ZMod N) :
    ∑ j : ZMod M, firstCoordinateDft Φ k j =
      ZMod.dft (fun i => ∑ j : ZMod M, Φ i j) k := by
  simp only [firstCoordinateDft, ZMod.dft_apply, smul_eq_mul, mul_sum]
  rw [sum_comm]

/-- Iterating the two one-dimensional DFTs gives the product DFT. -/
theorem dft_firstCoordinateDft
    (Φ : ZMod N → ZMod M → ℂ) (k : ZMod N) (l : ZMod M) :
    ZMod.dft (firstCoordinateDft Φ k) l = twoDimensionalDft Φ k l := by
  simp only [firstCoordinateDft, twoDimensionalDft, ZMod.dft_apply,
    smul_eq_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  ring

/-- Two-modulus Montgomery uncertainty principle.  Vanishing whenever either
coordinate is in its removed set forces the product of the two
removed/allowed ratios into the energy where both Fourier coordinates are
nonzero.  This is the first genuine tensor step toward Tao's Lemma 2.6. -/
theorem montgomery_uncertainty_two
    (S : Finset (ZMod N)) (T : Finset (ZMod M))
    (Φ : ZMod N → ZMod M → ℂ)
    (hSproper : S.card < N) (hTproper : T.card < M)
    (hzero : ∀ i j, i ∈ S ∨ j ∈ T → Φ i j = 0) :
    ((S.card : ℝ) / (Sᶜ.card : ℝ)) *
        ((T.card : ℝ) / (Tᶜ.card : ℝ)) *
        Complex.normSq (∑ i : ZMod N, ∑ j : ZMod M, Φ i j) ≤
      ∑ k ∈ (Finset.univ.erase (0 : ZMod N)),
        ∑ l ∈ (Finset.univ.erase (0 : ZMod M)),
          Complex.normSq (twoDimensionalDft Φ k l) := by
  have hfirstZero : ∀ i ∈ S, (∑ j : ZMod M, Φ i j) = 0 := by
    intro i hi
    exact Finset.sum_eq_zero fun j _ => hzero i j (Or.inl hi)
  have hfirst := montgomery_uncertainty_one S
    (fun i => ∑ j : ZMod M, Φ i j) hSproper hfirstZero
  have hsecond (k : ZMod N) :
      (T.card : ℝ) / (Tᶜ.card : ℝ) *
          Complex.normSq (∑ j : ZMod M, firstCoordinateDft Φ k j) ≤
        ∑ l ∈ (Finset.univ.erase (0 : ZMod M)),
          Complex.normSq (twoDimensionalDft Φ k l) := by
    have hcolZero : ∀ j ∈ T, firstCoordinateDft Φ k j = 0 := by
      intro j hj
      simp only [firstCoordinateDft, ZMod.dft_apply, smul_eq_mul]
      exact Finset.sum_eq_zero fun i _ => by
        rw [hzero i j (Or.inr hj), mul_zero]
    simpa only [dft_firstCoordinateDft] using
      montgomery_uncertainty_one T (firstCoordinateDft Φ k)
        hTproper hcolZero
  have hsumSecond :
      (T.card : ℝ) / (Tᶜ.card : ℝ) *
          (∑ k ∈ (Finset.univ.erase (0 : ZMod N)),
            Complex.normSq
              (∑ j : ZMod M, firstCoordinateDft Φ k j)) ≤
        ∑ k ∈ (Finset.univ.erase (0 : ZMod N)),
          ∑ l ∈ (Finset.univ.erase (0 : ZMod M)),
            Complex.normSq (twoDimensionalDft Φ k l) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => hsecond k
  have hTratio : 0 ≤ (T.card : ℝ) / (Tᶜ.card : ℝ) := by positivity
  calc
    ((S.card : ℝ) / (Sᶜ.card : ℝ)) *
        ((T.card : ℝ) / (Tᶜ.card : ℝ)) *
        Complex.normSq (∑ i : ZMod N, ∑ j : ZMod M, Φ i j) =
      ((T.card : ℝ) / (Tᶜ.card : ℝ)) *
        (((S.card : ℝ) / (Sᶜ.card : ℝ)) *
          Complex.normSq (∑ i : ZMod N, ∑ j : ZMod M, Φ i j)) := by ring
    _ ≤ ((T.card : ℝ) / (Tᶜ.card : ℝ)) *
        (∑ k ∈ (Finset.univ.erase (0 : ZMod N)),
          Complex.normSq
            (∑ j : ZMod M, firstCoordinateDft Φ k j)) := by
      apply mul_le_mul_of_nonneg_left
      · simpa only [sum_firstCoordinateDft] using hfirst
      · exact hTratio
    _ ≤ _ := hsumSecond

end TwoModuli

end

end Tao2026
