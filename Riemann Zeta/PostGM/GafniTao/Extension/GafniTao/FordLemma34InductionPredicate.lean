import GafniTao.FordMomentReal
import GafniTao.FordLemma34RealRecurrence

/-!
# Ford Lemma 3.4: equation (3.10) as an exact induction invariant

The invariant below quantifies over Ford's genuine integer polynomial
systems and over the literal canonical prime packet at the physical scale
`M_{J+1}`.  It is not a detached cardinality certificate: its conclusion is
the actual `L_s` count in equation (3.10).
-/

namespace GafniTao

noncomputable section

def FordEquation310
    (s k r j : ℕ) (C delta P : ℝ)
    (Φ : FordPhiSchedule k r j delta)
    (Esch : FordESchedule s k j (1 : ℝ)) (J : ℕ) : Prop :=
  ∀ {T : ℕ} (Ψ : FordIntegerPolynomialSystem k J T),
    0 < T → T ≤ ⌊P⌋₊ ^ J →
    ∀ p ∈ fordPrimeSet k ⌊fordMScale P Φ (J + 1)⌋₊,
      ∀ q : ℕ, 0 < q →
        (fordLCountReal Ψ s P (fordQScale P Φ (J + 1)) p q r : ℝ) ≤
          Esch.E J * C * P ^ k *
            (fordQScale P Φ (J + 1)) ^ fordLambda34 s k delta

/-- Version of the invariant with Ford's actual `eta=1+omega`. -/
def FordEquation310Eta
    (s k r j : ℕ) (C delta P eta : ℝ)
    (Φ : FordPhiSchedule k r j delta)
    (Esch : FordESchedule s k j eta) (J : ℕ) : Prop :=
  ∀ {T : ℕ} (Ψ : FordIntegerPolynomialSystem k J T),
    0 < T → T ≤ ⌊P⌋₊ ^ J →
    ∀ p ∈ fordPrimeSet k ⌊fordMScale P Φ (J + 1)⌋₊,
      ∀ q : ℕ, 0 < q →
        (fordLCountReal Ψ s P (fordQScale P Φ (J + 1)) p q r : ℝ) ≤
          Esch.E J * C * P ^ k *
            (fordQScale P Φ (J + 1)) ^ fordLambda34 s k delta

/-- The terminal case `J=j-1` of Ford's equation (3.10), obtained from the
actual congruence-to-equality injection and the actual Vinogradov moment
hypothesis. -/
theorem ford_equation_3_10_terminal
    {s k r j : ℕ} {C delta P eta : ℝ}
    (Φ : FordPhiSchedule k r j delta)
    (Esch : FordESchedule s k j eta)
    (hr : 1 ≤ r) (hj : 2 ≤ j) (hP : 1 ≤ P)
    (hQj : 1 ≤ fordQScale P Φ j)
    (hmoment : FordVinogradovMomentBound s k C delta) :
    FordEquation310Eta s k r j C delta P eta Φ Esch (j - 1) := by
  intro T Ψ hT hTbound p hp q hq
  have hindex : j - 1 + 1 = j := by omega
  have hpM : fordMScale P Φ j < (p : ℝ) := by
    simpa [hindex] using fordPrimeSet_gt_real hp
  have hMpos : 0 < fordMScale P Φ j :=
    fordMScale_pos (zero_lt_one.trans_le hP) Φ j
  have hpow : (fordMScale P Φ j) ^ r < ((p : ℝ) ^ r) :=
    pow_lt_pow_left₀ hpM hMpos.le (by omega)
  have hPpr : P < (p : ℝ) ^ r := by
    rw [fordMScale_terminal_rpow (zero_lt_one.trans_le hP) hr Φ] at hpow
    exact hpow
  have hterminal := fordLCountReal_terminal_le_moment_bound
    (s := s) (r := r) (P := P) (Q := fordQScale P Φ j)
    Ψ (fordPrimeSet_prime hp).pos hq hP hQj (by simpa using hPpr)
    (fun R hR => hmoment.real_endpoint hR)
  simpa [hindex, Esch.terminal] using hterminal

#print axioms ford_equation_3_10_terminal

end

end GafniTao
