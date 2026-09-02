import GafniTao.FordLemma34Assembly
import GafniTao.FordPrimeSet
import PrimeNumberTheoremAnd.Consequences

/-!
# Eventual prime packets from the audited prime number theorem

Ford obtains an explicit packet threshold from Rosser--Schoenfeld.  The
corresponding declarations in the pinned external checkout are admitted and
therefore cannot be used here.  This file proves the logically needed
eventual packet theorem from the independently audited theorem
`chebyshev_asymptotic`; the explicit Ford threshold remains a separate source
obligation.
-/

open Filter Finset
open scoped Topology

namespace GafniTao

noncomputable section

/-- Primes in the literal integral interval `(M,B]`. -/
def fordPrimeInterval (M B : ℕ) : Finset ℕ :=
  (Nat.primesLE B) \ (Nat.primesLE M)

theorem mem_fordPrimeInterval {M B p : ℕ} :
    p ∈ fordPrimeInterval M B ↔ M < p ∧ p ≤ B ∧ Nat.Prime p := by
  simp only [fordPrimeInterval, Finset.mem_sdiff, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hpB, hpPrime⟩, hpM⟩
    refine ⟨?_, hpB, hpPrime⟩
    by_contra hle
    exact hpM ⟨by omega, hpPrime⟩
  · rintro ⟨hMp, hpB, hpPrime⟩
    exact ⟨⟨hpB, hpPrime⟩, fun h => (not_le_of_gt hMp) h.1⟩

theorem fordPrimeInterval_card_eq_sub {M B : ℕ} (hMB : M ≤ B) :
    (fordPrimeInterval M B).card =
      Nat.primeCounting B - Nat.primeCounting M := by
  rw [fordPrimeInterval, Finset.card_sdiff]
  have hinter : Nat.primesLE M ∩ Nat.primesLE B = Nat.primesLE M :=
    Finset.inter_eq_left.mpr (Nat.primesLE_mono hMB)
  rw [hinter, Nat.primesLE_card_eq_primeCounting,
    Nat.primesLE_card_eq_primeCounting]

/-- The literal prime sum over `(M,B]` is exactly the Chebyshev-theta
increment. -/
theorem sum_fordPrimeInterval_log_eq_theta_sub {M B : ℕ} (hMB : M ≤ B) :
    ∑ p ∈ fordPrimeInterval M B, Real.log p =
      Chebyshev.theta B - Chebyshev.theta M := by
  have hsubset : Nat.primesLE M ⊆ Nat.primesLE B := Nat.primesLE_mono hMB
  rw [fordPrimeInterval, Chebyshev.theta_eq_sum_primesLE_log,
    Chebyshev.theta_eq_sum_primesLE_log, ← Finset.sum_sdiff hsubset]
  ring

/-- Each logarithm in the interval `(M,B]` is bounded by `log B`. -/
theorem sum_fordPrimeInterval_log_le {M B : ℕ} :
    ∑ p ∈ fordPrimeInterval M B, Real.log p ≤
      (fordPrimeInterval M B).card * Real.log B := by
  calc
    ∑ p ∈ fordPrimeInterval M B, Real.log p ≤
        ∑ _p ∈ fordPrimeInterval M B, Real.log B := by
      apply Finset.sum_le_sum
      intro p hp
      exact Real.log_le_log (by
          exact_mod_cast (mem_fordPrimeInterval.mp hp).2.2.pos)
        (by exact_mod_cast (mem_fordPrimeInterval.mp hp).2.1)
    _ = (fordPrimeInterval M B).card * Real.log B := by simp

/-- A direct epsilon form of the clean Chebyshev PNT. -/
theorem eventually_abs_chebyshev_error_le (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ x : ℝ in atTop, |Chebyshev.theta x - x| ≤ epsilon * x := by
  have h := Asymptotics.IsEquivalent.isLittleO chebyshev_asymptotic
  rw [Asymptotics.isLittleO_iff] at h
  have h' := h hepsilon
  filter_upwards [h', eventually_gt_atTop (0 : ℝ)] with x hx xpos
  simpa [Real.norm_eq_abs, abs_of_pos hepsilon, abs_of_pos xpos, mul_comm] using hx

/-- For a fixed positive relative width, the Chebyshev mass in `(x,(1+δ)x]`
is eventually at least three quarters of its expected main term. -/
theorem eventually_chebyshev_relative_interval_lower
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ x : ℝ in atTop,
      3 * delta * x / 4 ≤
        Chebyshev.theta ((1 + delta) * x) - Chebyshev.theta x := by
  let epsilon : ℝ := delta / (4 * (2 + delta))
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    positivity
  obtain ⟨R, hR⟩ := (eventually_atTop.1
    (eventually_abs_chebyshev_error_le epsilon hepsilon))
  filter_upwards [eventually_ge_atTop (max R 0)] with x hx
  have hxR : R ≤ x := le_trans (le_max_left _ _) hx
  have hx0 : 0 ≤ x := le_trans (le_max_right _ _) hx
  have hyR : R ≤ (1 + delta) * x := by
    calc
      R ≤ x := hxR
      _ ≤ (1 + delta) * x := by nlinarith
  have hxerr := hR x hxR
  have hyerr := hR ((1 + delta) * x) hyR
  have hxhi : Chebyshev.theta x ≤ x + epsilon * x := by
    rw [abs_le] at hxerr
    linarith
  have hylo : (1 + delta) * x - epsilon * ((1 + delta) * x) ≤
      Chebyshev.theta ((1 + delta) * x) := by
    rw [abs_le] at hyerr
    linarith
  dsimp [epsilon] at *
  have hden : 0 < 4 * (2 + delta) := by positivity
  field_simp [ne_of_gt hden] at hxhi hylo ⊢
  nlinarith

/-- For fixed `N` and positive relative width, the logarithmic cost of `N`
primes is eventually at most half of the expected Chebyshev increment. -/
theorem eventually_nat_mul_log_relative_le
    (N : ℕ) {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ x : ℝ in atTop,
      (N : ℝ) * Real.log ((1 + delta) * x) ≤ delta * x / 2 := by
  have hone : 0 < 1 + delta := by linarith
  have heq :
      (fun x : ℝ => Real.log (1 + delta) + Real.log x) =ᶠ[atTop]
        (fun x : ℝ => Real.log ((1 + delta) * x)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [Real.log_mul (ne_of_gt hone) (ne_of_gt hx)]
  have hlittle :
      (fun x : ℝ => Real.log (1 + delta) + Real.log x) =o[atTop]
        (fun x : ℝ => x) :=
    (Asymptotics.isLittleO_const_id_atTop (Real.log (1 + delta))).add
      Real.isLittleO_log_id_atTop
  have hrelative :
      (fun x : ℝ => Real.log ((1 + delta) * x)) =o[atTop]
        (fun x : ℝ => x) :=
    hlittle.congr' heq (EventuallyEq.rfl)
  have hscaled :
      (fun x : ℝ => (N : ℝ) * Real.log ((1 + delta) * x)) =o[atTop]
        (fun x : ℝ => x) :=
    hrelative.const_mul_left (N : ℝ)
  rw [Asymptotics.isLittleO_iff] at hscaled
  have hbound := hscaled (show 0 < delta / 2 by positivity)
  filter_upwards [hbound, eventually_gt_atTop (0 : ℝ)] with x hx hxpos
  calc
    (N : ℝ) * Real.log ((1 + delta) * x) ≤
        |(N : ℝ) * Real.log ((1 + delta) * x)| := le_abs_self _
    _ ≤ delta / 2 * |x| := by
      simpa [Real.norm_eq_abs, abs_of_pos (show 0 < delta / 2 by positivity)] using hx
    _ = delta * x / 2 := by rw [abs_of_pos hxpos]; ring

/-- The canonical integral right endpoint for a relative prime interval. -/
def fordRelativePrimeBound (delta : ℝ) (M : ℕ) : ℕ :=
  ⌊(1 + delta) * M⌋₊

theorem ford_le_relativePrimeBound
    {delta : ℝ} (hdelta : 0 ≤ delta) (M : ℕ) :
    M ≤ fordRelativePrimeBound delta M := by
  unfold fordRelativePrimeBound
  apply (Nat.le_floor_iff (α := ℝ)
    (show 0 ≤ (1 + delta) * (M : ℝ) by positivity)).2
  nlinarith [show (0 : ℝ) ≤ (M : ℝ) by positivity]

/-- Every fixed number of primes eventually occurs in the relative interval
`(M, floor ((1+delta)M)]`. -/
theorem eventually_fordPrimeInterval_card_ge
    (N : ℕ) {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ M : ℕ in atTop,
      N ≤ (fordPrimeInterval M (fordRelativePrimeBound delta M)).card := by
  have hmass := (eventually_chebyshev_relative_interval_lower hdelta).filter_mono
    tendsto_natCast_atTop_atTop
  have hcost := (eventually_nat_mul_log_relative_le N hdelta).filter_mono
    tendsto_natCast_atTop_atTop
  filter_upwards [hmass, hcost, eventually_ge_atTop 2] with M hmass hcost hM
  change 3 * delta * (M : ℝ) / 4 ≤
    Chebyshev.theta ((1 + delta) * (M : ℝ)) - Chebyshev.theta M at hmass
  change (N : ℝ) * Real.log ((1 + delta) * (M : ℝ)) ≤
    delta * (M : ℝ) / 2 at hcost
  let B := fordRelativePrimeBound delta M
  have hMB : M ≤ B := ford_le_relativePrimeBound hdelta.le M
  have hBpos : 0 < B := lt_of_lt_of_le (by omega : 0 < M) hMB
  have hypos : 0 < (1 + delta) * (M : ℝ) := by positivity
  have hB_le_y : (B : ℝ) ≤ (1 + delta) * (M : ℝ) := by
    dsimp [B, fordRelativePrimeBound]
    exact Nat.floor_le hypos.le
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ B by omega))
  have hlog_le : Real.log B ≤ Real.log ((1 + delta) * (M : ℝ)) :=
    Real.log_le_log (by exact_mod_cast hBpos) hB_le_y
  have hthetaFloor :
      Chebyshev.theta ((1 + delta) * (M : ℝ)) = Chebyshev.theta B := by
    simpa [B, fordRelativePrimeBound] using
      Chebyshev.theta_eq_theta_coe_floor ((1 + delta) * (M : ℝ))
  have hsumEq := sum_fordPrimeInterval_log_eq_theta_sub hMB
  have hsumUpper := sum_fordPrimeInterval_log_le (M := M) (B := B)
  by_contra hcard
  change ¬N ≤ (fordPrimeInterval M B).card at hcard
  have hcardNat : (fordPrimeInterval M B).card ≤ N := by omega
  have hcardReal : ((fordPrimeInterval M B).card : ℝ) ≤ N := by exact_mod_cast hcardNat
  have hfirst :
      ((fordPrimeInterval M B).card : ℝ) * Real.log B ≤
        (N : ℝ) * Real.log B :=
    mul_le_mul_of_nonneg_right hcardReal hlogB
  have hsecond :
      (N : ℝ) * Real.log B ≤
        (N : ℝ) * Real.log ((1 + delta) * (M : ℝ)) :=
    mul_le_mul_of_nonneg_left hlog_le (Nat.cast_nonneg N)
  have hlow :
      3 * delta * (M : ℝ) / 4 ≤
        ∑ p ∈ fordPrimeInterval M B, Real.log p := by
    rw [hsumEq]
    rw [← hthetaFloor]
    exact hmass
  have hupp :
      ∑ p ∈ fordPrimeInterval M B, Real.log p ≤ delta * (M : ℝ) / 2 :=
    hsumUpper.trans (hfirst.trans (hsecond.trans hcost))
  nlinarith [show (0 : ℝ) < M by exact_mod_cast (show 0 < M by omega)]

local instance fordPrimeAboveDecidable (M : ℕ) : DecidablePred (FordPrimeAbove M) :=
  Classical.decPred _

theorem fordPrimeAbove_count_succ_eq_interval_card (M B : ℕ) :
    Nat.count (FordPrimeAbove M) (B + 1) =
      (fordPrimeInterval M B).card := by
  classical
  rw [Nat.count_eq_card_filter_range]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_range, mem_fordPrimeInterval,
    FordPrimeAbove]
  constructor
  · rintro ⟨hpB, hMp, hpPrime⟩
    exact ⟨hMp, by omega, hpPrime⟩
  · rintro ⟨hMp, hpB, hpPrime⟩
    exact ⟨by omega, hMp, hpPrime⟩

/-- A cardinality lower bound for `(M,B]` bounds every member of the
canonical packet of the first `k^3` primes above `M`. -/
theorem fordPrimeSet_le_of_interval_card
    {k M B p : ℕ}
    (hcard : k ^ 3 ≤ (fordPrimeInterval M B).card)
    (hp : p ∈ fordPrimeSet k M) :
    p ≤ B := by
  classical
  rw [fordPrimeSet, Finset.mem_image] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  have hiIndex : i < k ^ 3 := Finset.mem_range.mp hi
  have hiCount : i < Nat.count (FordPrimeAbove M) (B + 1) := by
    rw [fordPrimeAbove_count_succ_eq_interval_card M B]
    omega
  have hnth := Nat.nth_lt_of_lt_count (p := FordPrimeAbove M) hiCount
  omega

/-- The exact canonical Ford packet is eventually contained in every fixed
positive relative interval. -/
theorem eventually_fordPrimeSet_le_relative
    (k : ℕ) {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ M : ℕ in atTop, ∀ p ∈ fordPrimeSet k M,
      p ≤ fordRelativePrimeBound delta M := by
  filter_upwards [eventually_fordPrimeInterval_card_ge (k ^ 3) hdelta] with M hcard
  intro p hp
  exact fordPrimeSet_le_of_interval_card hcard hp

/-- In particular, Ford's canonical packet is eventually contained in the
source interval `(M,2M]`. -/
theorem eventually_fordPrimeSet_le_two_mul (k : ℕ) :
    ∀ᶠ M : ℕ in atTop, ∀ p ∈ fordPrimeSet k M, p ≤ 2 * M := by
  filter_upwards [eventually_fordPrimeSet_le_relative k (show (0 : ℝ) < 1 by norm_num)]
    with M hpacket
  intro p hp
  have h := hpacket p hp
  have hbound : fordRelativePrimeBound 1 M = 2 * M := by
    unfold fordRelativePrimeBound
    have hcast : (1 + (1 : ℝ)) * (M : ℝ) = ((2 * M : ℕ) : ℝ) := by
      norm_num
    rw [hcast, Nat.floor_natCast]
  rwa [hbound] at h

/-- Threshold form of the eventual packet theorem, suitable for inserting
into Ford's outer `P`-threshold. -/
theorem exists_fordPrimeSet_two_mul_threshold (k : ℕ) :
    ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → ∀ p ∈ fordPrimeSet k M, p ≤ 2 * M := by
  exact eventually_atTop.1 (eventually_fordPrimeSet_le_two_mul k)

/-- Real-endpoint threshold form matching Ford's notation
`P_i ⊂ (M_i,(1+omega)M_i]`. -/
theorem exists_fordPrimeSet_relative_threshold
    (k : ℕ) {omega : ℝ} (homega : 0 < omega) :
    ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → ∀ p ∈ fordPrimeSet k M,
      (p : ℝ) ≤ (1 + omega) * M := by
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.1
    (eventually_fordPrimeSet_le_relative k homega)
  refine ⟨M₀, fun M hM p hp => ?_⟩
  have hpFloor := hM₀ M hM p hp
  exact (Nat.cast_le.mpr hpFloor).trans (Nat.floor_le (by positivity))

#print axioms eventually_abs_chebyshev_error_le
#print axioms eventually_chebyshev_relative_interval_lower
#print axioms eventually_nat_mul_log_relative_le
#print axioms eventually_fordPrimeInterval_card_ge
#print axioms fordPrimeSet_le_of_interval_card
#print axioms eventually_fordPrimeSet_le_relative
#print axioms eventually_fordPrimeSet_le_two_mul
#print axioms exists_fordPrimeSet_two_mul_threshold
#print axioms exists_fordPrimeSet_relative_threshold

end

end GafniTao
