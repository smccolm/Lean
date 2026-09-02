import GafniTao.FordLemma35InitialMoment

/-!
# Ford Lemma 3.5: one recursive moment step

This theorem combines the canonical maximal index, the derived `phi` lower
bounds, and the complete Lemma 3.4 consumer.  Its output is eventual because
the prime packet is obtained from the audited PNT; the next module repairs the
finite prefix before another iteration.
-/

namespace GafniTao

noncomputable section

open Filter

def fordStepCoefficient35 (s k : ℕ) (C eta : ℝ) : ℝ :=
  ((k : ℝ) ^ (3 * k) * eta ^ (4 * (s : ℝ) + (k : ℝ) ^ 2)) * C

theorem eventually_ford_lemma_3_5_one_step
    {s k r : ℕ} {C delta eta omega : ℝ}
    (hk : 26 ≤ k) (hr : 4 ≤ r) (hrk : r ≤ k) (hks : k ≤ s)
    (hy : 0 ≤ fordY35 k r delta)
    (hdelta : 2 * delta ≤ (k : ℝ) ^ 2 - k)
    (hstar : 1 / (((k + 1 : ℕ) : ℝ)) ≤ fordPhiStar35 k r delta)
    (homegaLower : 1 / (3 * Real.log k) ≤ omega)
    (homegaUpper : omega ≤ 1 / 2) (hetaEq : eta = 1 + omega)
    (hmoment : FordVinogradovMomentBound s k C delta) :
    FordVinogradovMomentBoundEventually (s + k) k
      (fordStepCoefficient35 s k C eta) (fordDeltaZero35 k r delta) := by
  let j := fordJ35 k r delta
  let Φ := fordCanonicalPhiSchedule k r j delta
  have hj : 2 ≤ j := fordJ35_lower hr hy
  have hjr : 10 * j ≤ 9 * r := fordJ35_ten_mul_le_nine_mul
  have h38Y : (((j - 1) * (j - 2) : ℕ) : ℝ) ≤ fordY35 k r delta :=
    (fordJ35_admissible hr hy).2
  have h38 : (((j - 1) * (j - 2) : ℕ) : ℝ) ≤
      2 * delta - (((k - r) * (k - r + 1) : ℕ) : ℝ) :=
    fordJ35_equation_3_8 hr hrk hy
  have hlower : ∀ i, 1 ≤ i → i ≤ j →
      1 / (((k + 1 : ℕ) : ℝ)) ≤ Φ.phi i :=
    fordCanonicalPhiSchedule_lower (show 1 ≤ k by omega)
      (show 1 ≤ r by omega) h38Y hdelta hstar
  have hreal := eventually_ford_lemma_3_4 Φ hk hr hrk hks hj hjr h38
    hlower homegaLower homegaUpper hetaEq hmoment
  have hnat := tendsto_natCast_atTop_atTop.eventually hreal
  filter_upwards [hnat] with Q hQ
  simpa only [fordVinogradovMoment, Nat.floor_natCast, fordStepCoefficient35,
    fordDeltaZero35, Φ, j, fordLambda34, Nat.cast_add] using hQ

/-- The same one-step conclusion with the finite initial segment repaired,
so it can be fed into the next application of Lemma 3.4. -/
theorem ford_lemma_3_5_one_step_global
    {s k r : ℕ} {C delta eta omega : ℝ}
    (hk : 26 ≤ k) (hr : 4 ≤ r) (hrk : r ≤ k) (hks : k ≤ s)
    (hy : 0 ≤ fordY35 k r delta)
    (hdelta : 2 * delta ≤ (k : ℝ) ^ 2 - k)
    (hstar : 1 / (((k + 1 : ℕ) : ℝ)) ≤ fordPhiStar35 k r delta)
    (homegaLower : 1 / (3 * Real.log k) ≤ omega)
    (homegaUpper : omega ≤ 1 / 2) (hetaEq : eta = 1 + omega)
    (hmoment : FordVinogradovMomentBound s k C delta) :
    ∃ C' : ℝ,
      fordStepCoefficient35 s k C eta ≤ C' ∧
      FordVinogradovMomentBound (s + k) k C' (fordDeltaZero35 k r delta) := by
  exact (eventually_ford_lemma_3_5_one_step hk hr hrk hks hy hdelta hstar
    homegaLower homegaUpper hetaEq hmoment).exists_global_coefficient

#print axioms eventually_ford_lemma_3_5_one_step
#print axioms ford_lemma_3_5_one_step_global

end

end GafniTao
