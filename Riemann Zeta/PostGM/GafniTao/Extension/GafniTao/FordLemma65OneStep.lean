import GafniTao.FordLemma65Algebra
import GafniTao.FordLemma32Real
import GafniTao.FordLemma34Initial
import GafniTao.FordMomentEventually

/-!
# Ford Lemma 6.5: one-step Vinogradov recurrence

This file performs Ford's direct specialization of Lemma 3.2 with
`d = 0`, `r = k`, `P = Q`, and `M = Q^(1/k)`.  It consumes the selected
prime, the translated polynomial system, the terminal `L` count, and the
incoming Vinogradov moment estimate.  The output is the genuine updated
moment exponent `Delta(1-1/k)`.
-/

open Filter

namespace GafniTao

noncomputable section

/-- The exact eventual one-step recurrence underlying Ford's Lemma 6.5. -/
theorem eventually_ford_lemma_6_5_one_step
    {s k : ℕ} {C delta : ℝ}
    (hk : 4 ≤ k) (hs : 2 ≤ s)
    (hmoment : FordVinogradovMomentBound s k C delta) :
    FordVinogradovMomentBoundEventually (s + k) k
      (fordLemma65Coefficient s k C) (fordDelta65 k delta) := by
  have hinputs := eventually_fordLemma65_inputs s k (by omega : 2 ≤ k)
  have hpacketReal := eventually_fordLemma65_packet_real k (by omega : 0 < k)
  filter_upwards [hinputs, hpacketReal] with Q hinputs hpacketReal
  rcases hinputs with ⟨hM, hkfloor, hPbig, hQbox, hpacketBox⟩
  have hQnat : 1 ≤ Q := by omega
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hQone : (1 : ℝ) ≤ Q := by exact_mod_cast hQnat
  have hsourceScale : (Q : ℝ) ≤
      fordLemma65Scale k (Q : ℝ) ^ (k + 1) :=
    fordLemma65_source_scale (by omega) hQone
  have hPbig' : 4 * k ^ 4 < ⌊(Q : ℝ)⌋₊ := by simpa using hPbig
  have hQbox' :
      32 * s ^ 2 * ⌈fordLemma65Scale k (Q : ℝ)⌉₊ < ⌊(Q : ℝ)⌋₊ := by
    simpa using hQbox
  obtain ⟨Ψ, p, hp, c, hrawNat⟩ := ford_lemma_3_2_real_endpoints
    (fordInitialIntegerPowerSystem k) hk (by omega : 2 ≤ k) le_rfl
      (by omega : 0 < k) (by omega : 1 ≤ s)
      hM hQpos hkfloor hsourceScale hPbig' hQbox'
      (by norm_num : 0 < (1 : ℕ)) (by norm_num : 0 < (1 : ℕ))
      (by simp) hpacketBox
  let Ψ' := fordBinomialTranslateSystem Ψ (fordS4TranslationScale 1 c)
  have hraw :
      (fordVinogradovMoment (s + k) k (Q : ℝ) : ℝ) ≤
        (4 * k ^ 3 * k.factorial : ℕ) *
          (p : ℝ) ^ fordLemma65PrimeExponent s k *
          (fordLCountReal Ψ' s (Q : ℝ)
            ((⌊(Q : ℝ)⌋₊ / p : ℕ) : ℝ) p 1 k : ℝ) := by
    rw [← fordKCountReal_initial_eq_vinogradov]
    simp only [Nat.sub_zero, Nat.mul_zero, add_zero] at hrawNat
    rw [fordLemma65_source_exponent_eq] at hrawNat
    exact_mod_cast hrawNat
  let R := (Q : ℝ) ^ (1 - 1 / (k : ℝ))
  have hRone : 1 ≤ R := fordLemma65_next_scale_one_le (by omega) hQone
  have hsmall : ((⌊(Q : ℝ)⌋₊ / p : ℕ) : ℝ) ≤ R :=
    ford_floor_div_prime_le_next_scale hQpos
      (fordLemma65Scale_pos hQpos) (fordPrimeSet_gt_real hp)
      (by simpa [R] using fordLemma65_div_scale (k := k) hQpos)
  have hmono :
      fordLCountReal Ψ' s (Q : ℝ)
          ((⌊(Q : ℝ)⌋₊ / p : ℕ) : ℝ) p 1 k ≤
        fordLCountReal Ψ' s (Q : ℝ) R p 1 k :=
    fordLCountReal_mono_Q Ψ' hsmall
  have hpPos : 0 < p := (fordPrimeSet_prime hp).pos
  have hterminalPower : (Q : ℝ) < (p : ℝ) ^ k :=
    fordLemma65_terminal_power (by omega) hQpos (fordPrimeSet_gt_real hp)
  have hterminal := fordLCountReal_terminal_le_moment_bound
    (s := s) (r := k) (P := (Q : ℝ)) (Q := R)
    Ψ' hpPos (by norm_num : 0 < (1 : ℕ)) hQone hRone hterminalPower
      (fun U hU => hmoment.real_endpoint hU)
  have hL :
      (fordLCountReal Ψ' s (Q : ℝ)
          ((⌊(Q : ℝ)⌋₊ / p : ℕ) : ℝ) p 1 k : ℝ) ≤
        C * (Q : ℝ) ^ k * R ^ fordLambda34 s k delta := by
    have hmonoReal :
        (fordLCountReal Ψ' s (Q : ℝ)
            ((⌊(Q : ℝ)⌋₊ / p : ℕ) : ℝ) p 1 k : ℝ) ≤
          fordLCountReal Ψ' s (Q : ℝ) R p 1 k := by
      exact_mod_cast hmono
    exact hmonoReal.trans hterminal
  have hpBound := fordLemma65_selected_power_bound
    (s := s) (k := k) (Q := (Q : ℝ)) (hpacketReal p hp)
  have hpBound' :
      (p : ℝ) ^ fordLemma65PrimeExponent s k ≤
        (2 : ℝ) ^ fordLemma65PrimeExponent s k *
          fordLemma65Scale k (Q : ℝ) ^ fordLemma65PrimeExponent s k := by
    simpa [Nat.cast_pow] using hpBound
  have hcoefficient : (0 : ℝ) ≤ (4 * k ^ 3 * k.factorial : ℕ) := by positivity
  have hpPowNonneg : (0 : ℝ) ≤ (p : ℝ) ^ fordLemma65PrimeExponent s k := by
    positivity
  have hLNonneg : (0 : ℝ) ≤
      (fordLCountReal Ψ' s (Q : ℝ)
        ((⌊(Q : ℝ)⌋₊ / p : ℕ) : ℝ) p 1 k : ℝ) := by positivity
  have hpower :
      fordLemma65Scale k (Q : ℝ) ^ fordLemma65PrimeExponent s k *
          (Q : ℝ) ^ k * R ^ fordLambda34 s k delta =
        (Q : ℝ) ^ fordLambda34 (s + k) k (fordDelta65 k delta) := by
    simpa [R] using fordLemma65_power_identity (s := s) (delta := delta)
      (show 1 ≤ k by omega) hQpos
  calc
    (fordVinogradovMomentNat (s + k) k Q : ℝ) =
        fordVinogradovMoment (s + k) k (Q : ℝ) := by
          simp [fordVinogradovMoment]
    _ ≤ (4 * k ^ 3 * k.factorial : ℕ) *
          (p : ℝ) ^ fordLemma65PrimeExponent s k *
          (fordLCountReal Ψ' s (Q : ℝ)
            ((⌊(Q : ℝ)⌋₊ / p : ℕ) : ℝ) p 1 k : ℝ) := hraw
    _ ≤ (4 * k ^ 3 * k.factorial : ℕ) *
          ((2 : ℝ) ^ fordLemma65PrimeExponent s k *
            fordLemma65Scale k (Q : ℝ) ^ fordLemma65PrimeExponent s k) *
          (C * (Q : ℝ) ^ k * R ^ fordLambda34 s k delta) := by
      gcongr
    _ = fordLemma65Coefficient s k C *
          (Q : ℝ) ^ fordLambda34 (s + k) k (fordDelta65 k delta) := by
      calc
        (4 * k ^ 3 * k.factorial : ℕ) *
              ((2 : ℝ) ^ fordLemma65PrimeExponent s k *
                fordLemma65Scale k (Q : ℝ) ^ fordLemma65PrimeExponent s k) *
              (C * (Q : ℝ) ^ k * R ^ fordLambda34 s k delta) =
            ((4 * k ^ 3 * k.factorial : ℕ) *
              (2 : ℝ) ^ fordLemma65PrimeExponent s k * C) *
              (fordLemma65Scale k (Q : ℝ) ^ fordLemma65PrimeExponent s k *
                (Q : ℝ) ^ k * R ^ fordLambda34 s k delta) := by ring
        _ = ((4 * k ^ 3 * k.factorial : ℕ) *
              (2 : ℝ) ^ fordLemma65PrimeExponent s k * C) *
              (Q : ℝ) ^ fordLambda34 (s + k) k (fordDelta65 k delta) := by
            rw [hpower]
        _ = fordLemma65Coefficient s k C *
              (Q : ℝ) ^ fordLambda34 (s + k) k (fordDelta65 k delta) := by
            unfold fordLemma65Coefficient
            push_cast
            ring

/-- The finite prefix is absorbed into the coefficient, leaving the exact
source exponent update available for iteration. -/
theorem ford_lemma_6_5_one_step_global
    {s k : ℕ} {C delta : ℝ}
    (hk : 4 ≤ k) (hs : 2 ≤ s)
    (hmoment : FordVinogradovMomentBound s k C delta) :
    ∃ C' : ℝ,
      fordLemma65Coefficient s k C ≤ C' ∧
      FordVinogradovMomentBound (s + k) k C' (fordDelta65 k delta) := by
  exact (eventually_ford_lemma_6_5_one_step hk hs hmoment).exists_global_coefficient

#print axioms eventually_ford_lemma_6_5_one_step
#print axioms ford_lemma_6_5_one_step_global

end

end GafniTao
