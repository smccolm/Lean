import Tao2026.SmallPrimeMertens
import Tao2026.LargeSieveGlobal

/-!
# The Bombieri--Halász--Montgomery step for exceptional characters

This file specializes the finite Gram-matrix inequality to the weighted
sequence space used in the proof of Tao's Lemma 5.1.  The weight is kept
explicit: later the fundamental-lemma sieve weight will be substituted for
`w`, and the vectors will be Dirichlet characters restricted to `n < 2 Z`.
-/

namespace Tao2026

open Finset Complex
open scoped BigOperators ComplexConjugate

noncomputable section

/-- Weighted finite scalar product, linear in its second argument. -/
def finiteWeightedPairing {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w : ι → ℝ) (f g : ι → ℂ) : ℂ :=
  ∑ i ∈ s, (w i : ℂ) * conj (f i) * g i

/-- Squared norm associated to `finiteWeightedPairing`. -/
def finiteWeightedEnergy {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w : ι → ℝ) (f : ι → ℂ) : ℝ :=
  ∑ i ∈ s, w i * Complex.normSq (f i)

/-- Weighted Gram entry of two members of a finite family. -/
def finiteWeightedGram {ι κ : Type*} [DecidableEq ι]
    (s : Finset ι) (w : ι → ℝ) (φ : κ → ι → ℂ) (j k : κ) : ℂ :=
  finiteWeightedPairing s w (φ j) (φ k)

private theorem sqrt_weight_mul_identity (x : ℝ) (hx : 0 ≤ x)
    (z y : ℂ) :
    conj ((Real.sqrt x : ℂ) * z) * ((Real.sqrt x : ℂ) * y) =
      (x : ℂ) * conj z * y := by
  rw [map_mul]
  simp only [Complex.conj_ofReal]
  have hsqrt : (Real.sqrt x : ℂ) ^ 2 = (x : ℂ) := by
    exact_mod_cast Real.sq_sqrt hx
  calc
    (Real.sqrt x : ℂ) * conj z * ((Real.sqrt x : ℂ) * y) =
        (Real.sqrt x : ℂ) ^ 2 * conj z * y := by ring
    _ = (x : ℂ) * conj z * y := by rw [hsqrt]

private theorem normSq_sqrt_weight_mul (x : ℝ) (hx : 0 ≤ x)
    (z : ℂ) :
    Complex.normSq ((Real.sqrt x : ℂ) * z) =
      x * Complex.normSq z := by
  rw [Complex.normSq_mul]
  simp only [Complex.normSq_ofReal]
  rw [← pow_two (Real.sqrt x), Real.sq_sqrt hx]

/-- Weighted finite Bombieri--Halász--Montgomery inequality.  A single
uniform row bound for the weighted Gram matrix controls the total squared
correlation with an arbitrary vector. -/
theorem finiteWeighted_bombieri_halasz_montgomery
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s : Finset ι) (W : Finset κ) (w : ι → ℝ)
    (ξ : ι → ℂ) (φ : κ → ι → ℂ) (B : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hB : 0 ≤ B)
    (hrow : ∀ j ∈ W,
      ∑ k ∈ W, ‖finiteWeightedGram s w φ j k‖ ≤ B) :
    ∑ j ∈ W, ‖finiteWeightedPairing s w (φ j) ξ‖ ^ 2 ≤
      finiteWeightedEnergy s w ξ * B := by
  let u : ↥W → ↥s → ℂ := fun j i =>
    (Real.sqrt (w i.1) : ℂ) * φ j.1 i.1
  let f : ↥s → ℂ := fun i =>
    (Real.sqrt (w i.1) : ℂ) * ξ i.1
  have hanalysis (j : ↥W) :
      finiteAnalysis u f j =
        finiteWeightedPairing s w (φ j.1) ξ := by
    unfold finiteAnalysis finiteWeightedPairing u f
    rw [Finset.sum_subtype s (fun _ => Iff.rfl)]
    apply sum_congr rfl
    intro i hi
    exact sqrt_weight_mul_identity (w i) (hw i i.2) (φ j.1 i) (ξ i)
  have hgram (j k : ↥W) :
      finiteGram u j k = finiteWeightedGram s w φ j.1 k.1 := by
    unfold finiteGram finiteWeightedGram finiteWeightedPairing u
    rw [Finset.sum_subtype s (fun _ => Iff.rfl)]
    apply sum_congr rfl
    intro i hi
    exact sqrt_weight_mul_identity (w i) (hw i i.2) (φ j.1 i) (φ k.1 i)
  have henergy :
      (∑ i : ↥s, Complex.normSq (f i)) =
        finiteWeightedEnergy s w ξ := by
    unfold finiteWeightedEnergy f
    rw [Finset.sum_subtype s (fun _ => Iff.rfl)]
    apply sum_congr rfl
    intro i hi
    exact normSq_sqrt_weight_mul (w i) (hw i i.2) (ξ i)
  have hrow' : ∀ j : ↥W, ∑ k, ‖finiteGram u j k‖ ≤ B := by
    intro j
    simp_rw [hgram]
    calc
      (∑ k : ↥W, ‖finiteWeightedGram s w φ j.1 k.1‖) =
          ∑ k ∈ W, ‖finiteWeightedGram s w φ j.1 k‖ :=
        (Finset.sum_subtype W (fun _ => Iff.rfl)
          (fun k => ‖finiteWeightedGram s w φ j.1 k‖)).symm
      _ ≤ B := hrow j.1 j.2
  have h := bombieri_halasz_montgomery_inequality u f B hB hrow'
  rw [henergy] at h
  simp_rw [hanalysis] at h
  calc
    (∑ j ∈ W, ‖finiteWeightedPairing s w (φ j) ξ‖ ^ 2) =
        ∑ j : ↥W,
          Complex.normSq (finiteWeightedPairing s w (φ j.1) ξ) := by
      simp only [Complex.normSq_eq_norm_sq]
      exact Finset.sum_subtype W (fun _ => Iff.rfl)
        (fun j => ‖finiteWeightedPairing s w (φ j) ξ‖ ^ 2)
    _ ≤ B * finiteWeightedEnergy s w ξ := h
    _ = finiteWeightedEnergy s w ξ * B := mul_comm _ _

/-- Indicator of the dyadic prime band `[Z,2Z)`, regarded as a complex
sequence on the ambient interval `n < 2Z`. -/
def taoDyadicPrimeIndicator (Z n : ℕ) : ℂ :=
  if n ∈ taoDyadicPrimeBand Z then 1 else 0

/-- Every prime in Tao's dyadic band belongs to the ambient interval used in
the weighted sequence space. -/
theorem taoDyadicPrimeBand_subset_twiceRange (Z : ℕ) :
    taoDyadicPrimeBand Z ⊆ Finset.range (2 * Z) := by
  intro p hp
  exact Finset.mem_range.mpr (mem_taoDyadicPrimeBand.mp hp).2.2

/-- If a nonnegative sieve weight equals one on the prime band, pairing the
conjugated character vector with the prime indicator recovers the unweighted
prime sum exactly. -/
theorem finiteWeightedPairing_conj_primeIndicator_eq
    (Z : ℕ) (w : ℕ → ℝ) (χ : ℕ → ℂ)
    (hone : ∀ p ∈ taoDyadicPrimeBand Z, w p = 1) :
    finiteWeightedPairing (Finset.range (2 * Z)) w
        (fun n => conj (χ n)) (taoDyadicPrimeIndicator Z) =
      ∑ p ∈ taoDyadicPrimeBand Z, χ p := by
  unfold finiteWeightedPairing
  symm
  apply Finset.sum_subset_zero_on_sdiff
    (taoDyadicPrimeBand_subset_twiceRange Z)
  · intro n hn
    have hnot : n ∉ taoDyadicPrimeBand Z := (Finset.mem_sdiff.mp hn).2
    simp [taoDyadicPrimeIndicator, hnot]
  · intro p hp
    rw [hone p hp]
    simp [taoDyadicPrimeIndicator, hp]

/-- The weighted energy of the prime indicator is exactly the number of
primes in the band when the sieve weight is one there. -/
theorem finiteWeightedEnergy_primeIndicator_eq_card
    (Z : ℕ) (w : ℕ → ℝ)
    (hone : ∀ p ∈ taoDyadicPrimeBand Z, w p = 1) :
    finiteWeightedEnergy (Finset.range (2 * Z)) w
        (taoDyadicPrimeIndicator Z) =
      (taoDyadicPrimeBand Z).card := by
  unfold finiteWeightedEnergy
  calc
    (∑ i ∈ Finset.range (2 * Z),
        w i * Complex.normSq (taoDyadicPrimeIndicator Z i)) =
        ∑ p ∈ taoDyadicPrimeBand Z, (1 : ℝ) := by
      symm
      apply Finset.sum_subset_zero_on_sdiff
        (taoDyadicPrimeBand_subset_twiceRange Z)
      · intro n hn
        have hnot : n ∉ taoDyadicPrimeBand Z := (Finset.mem_sdiff.mp hn).2
        simp [taoDyadicPrimeIndicator, hnot]
      · intro p hp
        rw [hone p hp]
        simp [taoDyadicPrimeIndicator, hp]
    _ = (taoDyadicPrimeBand Z).card := by simp

/-- Prime-band specialization of Bombieri--Halász--Montgomery.  This is the
exact functional-analytic estimate used in Lemma 5.1: the left side is the
sum of squares of the (unnormalized) prime character sums and the diagonal
factor is the number of primes in `[Z,2Z)`. -/
theorem sum_primeBand_sq_le_card_mul_gramRow
    {κ : Type*} [DecidableEq κ]
    (Z : ℕ) (W : Finset κ) (w : ℕ → ℝ)
    (χ : κ → ℕ → ℂ) (B : ℝ)
    (hw : ∀ n ∈ Finset.range (2 * Z), 0 ≤ w n)
    (hone : ∀ p ∈ taoDyadicPrimeBand Z, w p = 1)
    (hB : 0 ≤ B)
    (hrow : ∀ j ∈ W,
      ∑ k ∈ W,
        ‖finiteWeightedGram (Finset.range (2 * Z)) w
          (fun a n => conj (χ a n)) j k‖ ≤ B) :
    ∑ j ∈ W, ‖∑ p ∈ taoDyadicPrimeBand Z, χ j p‖ ^ 2 ≤
      ((taoDyadicPrimeBand Z).card : ℝ) * B := by
  have h := finiteWeighted_bombieri_halasz_montgomery
    (Finset.range (2 * Z)) W w (taoDyadicPrimeIndicator Z)
      (fun a n => conj (χ a n)) B hw hB hrow
  rw [finiteWeightedEnergy_primeIndicator_eq_card Z w hone] at h
  simpa only [finiteWeightedPairing_conj_primeIndicator_eq Z w _ hone] using h

/-- Elementary diagonal estimate for a weighted Gram matrix whose vectors
are pointwise bounded by one. -/
theorem norm_finiteWeightedGram_self_le_mass
    {ι κ : Type*} [DecidableEq ι]
    (s : Finset ι) (w : ι → ℝ) (φ : κ → ι → ℂ) (j : κ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hφ : ∀ i ∈ s, ‖φ j i‖ ≤ 1) :
    ‖finiteWeightedGram s w φ j j‖ ≤ ∑ i ∈ s, w i := by
  unfold finiteWeightedGram finiteWeightedPairing
  calc
    ‖∑ i ∈ s, (w i : ℂ) * conj (φ j i) * φ j i‖ ≤
        ∑ i ∈ s, ‖(w i : ℂ) * conj (φ j i) * φ j i‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ s, w i := by
      apply sum_le_sum
      intro i hi
      rw [norm_mul, norm_mul, norm_conj, norm_real,
        Real.norm_eq_abs, abs_of_nonneg (hw i hi)]
      have hnorm : ‖φ j i‖ * ‖φ j i‖ ≤ 1 := by
        nlinarith [norm_nonneg (φ j i), hφ i hi]
      simpa only [mul_one, mul_assoc] using
        mul_le_mul_of_nonneg_left hnorm (hw i hi)

/-- A Gram row is bounded by its diagonal estimate plus one copy of a
uniform off-diagonal estimate for each remaining family member. -/
theorem sum_norm_gramRow_le_diagonal_add_offDiagonal
    {κ : Type*} [DecidableEq κ]
    (W : Finset κ) (G : κ → κ → ℂ) (j : κ) (hj : j ∈ W)
    (D E : ℝ) (hdiag : ‖G j j‖ ≤ D)
    (hoff : ∀ k ∈ W, k ≠ j → ‖G j k‖ ≤ E) :
    ∑ k ∈ W, ‖G j k‖ ≤ D + ((W.card - 1 : ℕ) : ℝ) * E := by
  have herase :
      (∑ k ∈ W.erase j, ‖G j k‖) ≤
        ((W.erase j).card : ℝ) * E := by
    have hsum := Finset.sum_le_card_nsmul (W.erase j)
      (fun k => ‖G j k‖) E (fun k hk => by
        exact hoff k (Finset.mem_of_mem_erase hk) (Finset.ne_of_mem_erase hk))
    simpa only [nsmul_eq_mul] using hsum
  calc
    (∑ k ∈ W, ‖G j k‖) =
        ‖G j j‖ + ∑ k ∈ W.erase j, ‖G j k‖ := by
      rw [add_comm, Finset.sum_erase_add _ _ hj]
    _ ≤ D + ((W.erase j).card : ℝ) * E := add_le_add hdiag herase
    _ = D + ((W.card - 1 : ℕ) : ℝ) * E := by
      rw [Finset.card_erase_of_mem hj]

/-- Source-shaped consequence combining the diagonal/off-diagonal Gram-row
decomposition with the weighted Bombieri--Halász--Montgomery inequality. -/
theorem sum_primeBand_sq_le_card_mul_diagonal_add_offDiagonal
    {κ : Type*} [DecidableEq κ]
    (Z : ℕ) (W : Finset κ) (w : ℕ → ℝ)
    (χ : κ → ℕ → ℂ) (D E : ℝ)
    (hw : ∀ n ∈ Finset.range (2 * Z), 0 ≤ w n)
    (hone : ∀ p ∈ taoDyadicPrimeBand Z, w p = 1)
    (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hdiag : ∀ j ∈ W,
      ‖finiteWeightedGram (Finset.range (2 * Z)) w
        (fun a n => conj (χ a n)) j j‖ ≤ D)
    (hoff : ∀ j ∈ W, ∀ k ∈ W, k ≠ j →
      ‖finiteWeightedGram (Finset.range (2 * Z)) w
        (fun a n => conj (χ a n)) j k‖ ≤ E) :
    ∑ j ∈ W, ‖∑ p ∈ taoDyadicPrimeBand Z, χ j p‖ ^ 2 ≤
      ((taoDyadicPrimeBand Z).card : ℝ) *
        (D + ((W.card - 1 : ℕ) : ℝ) * E) := by
  apply sum_primeBand_sq_le_card_mul_gramRow Z W w χ
    (D + ((W.card - 1 : ℕ) : ℝ) * E) hw hone
  · positivity
  · intro j hj
    exact sum_norm_gramRow_le_diagonal_add_offDiagonal W
      (finiteWeightedGram (Finset.range (2 * Z)) w
        (fun a n => conj (χ a n))) j hj D E
      (hdiag j hj) (hoff j hj)

/-- Abstract normalized dyadic prime sum.  Specializing `χ` to the values of a
Dirichlet character gives `taoNormalizedPrimeCharacterSum` definitionally. -/
def finiteNormalizedPrimeBandSum (Z : ℕ) (χ : ℕ → ℂ) : ℂ :=
  ((taoDyadicPrimeBand Z).card : ℂ)⁻¹ *
    ∑ p ∈ taoDyadicPrimeBand Z, χ p

theorem finiteNormalizedPrimeBandSum_eq_taoNormalizedPrimeCharacterSum
    {q : ℕ} (Z : ℕ) (χ : DirichletCharacter ℂ q) :
    finiteNormalizedPrimeBandSum Z (fun n => χ (n : ZMod q)) =
      taoNormalizedPrimeCharacterSum χ Z := by
  rfl

/-- Normalized form of the prime-band BHM estimate.  The factor contributed
by the prime indicator is exactly cancelled once, leaving `B/#primes`. -/
theorem sum_finiteNormalizedPrimeBandSum_sq_le_div
    {κ : Type*} [DecidableEq κ]
    (Z : ℕ) (W : Finset κ) (χ : κ → ℕ → ℂ) (B : ℝ)
    (hZ : (taoDyadicPrimeBand Z).Nonempty)
    (hraw :
      ∑ j ∈ W, ‖∑ p ∈ taoDyadicPrimeBand Z, χ j p‖ ^ 2 ≤
        ((taoDyadicPrimeBand Z).card : ℝ) * B) :
    ∑ j ∈ W, ‖finiteNormalizedPrimeBandSum Z (χ j)‖ ^ 2 ≤
      B / (taoDyadicPrimeBand Z).card := by
  let C : ℝ := (taoDyadicPrimeBand Z).card
  have hCpos : 0 < C := by
    dsimp [C]
    exact_mod_cast Finset.card_pos.mpr hZ
  have hscale :
      (∑ j ∈ W, ‖finiteNormalizedPrimeBandSum Z (χ j)‖ ^ 2) =
        C⁻¹ ^ 2 *
          ∑ j ∈ W, ‖∑ p ∈ taoDyadicPrimeBand Z, χ j p‖ ^ 2 := by
    unfold finiteNormalizedPrimeBandSum C
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro j hj
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    norm_num
    ring
  rw [hscale]
  calc
    C⁻¹ ^ 2 *
        (∑ j ∈ W, ‖∑ p ∈ taoDyadicPrimeBand Z, χ j p‖ ^ 2) ≤
        C⁻¹ ^ 2 * (C * B) := by
      exact mul_le_mul_of_nonneg_left hraw (sq_nonneg C⁻¹)
    _ = B / C := by
      field_simp [hCpos.ne']

/-- Fully normalized source-shaped consequence: diagonal and off-diagonal
Gram estimates give a bound divided by the exact number of dyadic primes. -/
theorem sum_finiteNormalizedPrimeBandSum_sq_le_diagonal_add_offDiagonal_div
    {κ : Type*} [DecidableEq κ]
    (Z : ℕ) (W : Finset κ) (w : ℕ → ℝ)
    (χ : κ → ℕ → ℂ) (D E : ℝ)
    (hZ : (taoDyadicPrimeBand Z).Nonempty)
    (hw : ∀ n ∈ Finset.range (2 * Z), 0 ≤ w n)
    (hone : ∀ p ∈ taoDyadicPrimeBand Z, w p = 1)
    (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hdiag : ∀ j ∈ W,
      ‖finiteWeightedGram (Finset.range (2 * Z)) w
        (fun a n => conj (χ a n)) j j‖ ≤ D)
    (hoff : ∀ j ∈ W, ∀ k ∈ W, k ≠ j →
      ‖finiteWeightedGram (Finset.range (2 * Z)) w
        (fun a n => conj (χ a n)) j k‖ ≤ E) :
    ∑ j ∈ W, ‖finiteNormalizedPrimeBandSum Z (χ j)‖ ^ 2 ≤
      (D + ((W.card - 1 : ℕ) : ℝ) * E) /
        (taoDyadicPrimeBand Z).card := by
  apply sum_finiteNormalizedPrimeBandSum_sq_le_div Z W χ
    (D + ((W.card - 1 : ℕ) : ℝ) * E) hZ
  exact sum_primeBand_sq_le_card_mul_diagonal_add_offDiagonal
    Z W w χ D E hw hone hD hE hdiag hoff

/-- Squaring Tao's exact exceptional threshold gives the exponent
`-0.016 = -2/125` used in the cardinality consequence of Lemma 5.1. -/
theorem taoExceptionalPrimeCharacterThreshold_pow_two (Z : ℕ) :
    taoExceptionalPrimeCharacterThreshold Z ^ (2 : ℕ) =
      (Z : ℝ) ^ (-(2 : ℝ) / 125) := by
  unfold taoExceptionalPrimeCharacterThreshold
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg Z)]
  congr 1
  norm_num

/-- Exact finite Markov step behind Tao's statement that the squared-moment
bound in Lemma 5.1 implies `J ≪ Z^0.016`. -/
theorem card_exceptional_mul_threshold_sq_le_sum_sq
    (q Z : ℕ) :
    ((taoExceptionalPrimitiveCharacters q Z).card : ℝ) *
        taoExceptionalPrimeCharacterThreshold Z ^ (2 : ℕ) ≤
      ∑ χ ∈ taoExceptionalPrimitiveCharacters q Z,
        ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (2 : ℕ) := by
  calc
    ((taoExceptionalPrimitiveCharacters q Z).card : ℝ) *
        taoExceptionalPrimeCharacterThreshold Z ^ (2 : ℕ) =
        ∑ _χ ∈ taoExceptionalPrimitiveCharacters q Z,
          taoExceptionalPrimeCharacterThreshold Z ^ (2 : ℕ) := by simp
    _ ≤ ∑ χ ∈ taoExceptionalPrimitiveCharacters q Z,
        ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (2 : ℕ) := by
      apply sum_le_sum
      intro χ hχ
      have hthreshold :=
        (mem_taoExceptionalPrimitiveCharacters.mp hχ).2.2
      nlinarith [taoExceptionalPrimeCharacterThreshold_nonneg Z,
        norm_nonneg (taoNormalizedPrimeCharacterSum χ Z)]

end

end Tao2026
