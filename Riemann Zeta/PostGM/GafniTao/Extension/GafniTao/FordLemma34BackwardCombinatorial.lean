import GafniTao.FordLemma34BackwardAlgebra

/-!
# Ford Lemma 3.4: the exact combinatorial backward step

The declarations below separately expose the Lemma-3.2 estimate, the
Lemma-3.3 estimate, and their composition.  This mirrors Ford's proof and
keeps Lean from repeatedly reducing the complete square-root expression.
-/

namespace GafniTao

noncomputable section

def fordLemma34JBound (s k : ℕ) (C delta Q : ℝ) : ℝ :=
  C * Q ^ fordLambda34 s k delta

def fordLemma34LBound (s k : ℕ) (C delta P Q EschE : ℝ) : ℝ :=
  EschE * C * P ^ k * Q ^ fordLambda34 s k delta

def fordLemma34KBound
    (s k r J : ℕ) (C delta P eta M Qnext EschE : ℝ) : ℝ :=
  ((4 * k ^ 3 * k.factorial : ℕ) : ℝ) *
    (eta * M) ^ fordLemma34PrimeExponent s J r *
      fordLemma34LBound s k C delta P Qnext EschE

def fordLemma34RawBound
    (s k r J p : ℕ) (C delta P eta M Q Qnext EschE : ℝ) : ℝ :=
  ((2 * ⌊P⌋₊ : ℕ) : ℝ) ^ k *
    max (((k ^ k : ℕ) : ℝ) * fordLemma34JBound s k C delta Q)
      (2 * (((p : ℝ) ^ (r * k))⁻¹) *
        √(fordLemma34JBound s k C delta Q *
          fordLemma34KBound s k r J C delta P eta M Qnext EschE))

/-- Lemma 3.2 with the induction hypothesis substituted into its actual
selected translated system. -/
theorem ford_equation_3_10_K_bound
    {s k r j J T q : ℕ} {C delta P eta : ℝ}
    (Φ : FordPhiSchedule k r j delta)
    (Esch : FordESchedule s k j eta)
    (Υ : FordIntegerPolynomialSystem k J T)
    (hk : 26 ≤ k) (hr2 : 2 ≤ r) (hrk : r ≤ k) (hks : k ≤ s)
    (hJj : J < j) (hjr : j ≤ r)
    (hP : 1 ≤ P) (hPbig : 4 * k ^ 4 < ⌊P⌋₊)
    (hM : 1 < fordMScale P Φ (J + 1))
    (hkM : k ≤ ⌊fordMScale P Φ (J + 1)⌋₊)
    (hPM : P ≤ (fordMScale P Φ (J + 1)) ^ (k + 1))
    (hQbox : 32 * s ^ 2 * ⌈fordMScale P Φ (J + 1)⌉₊ <
      ⌊fordQScale P Φ J⌋₊)
    (hpacketTwo : ∀ p ∈ fordPrimeSet k ⌊fordMScale P Φ (J + 1)⌋₊,
      p ≤ 2 * ⌈fordMScale P Φ (J + 1)⌉₊)
    (hpacketBound : ∀ p ∈ fordPrimeSet k ⌊fordMScale P Φ (J + 1)⌋₊,
      (p : ℝ) ≤ eta * fordMScale P Φ (J + 1))
    (hquotient : ∀ p ∈ fordPrimeSet k ⌊fordMScale P Φ (J + 1)⌋₊,
      ((⌊fordQScale P Φ J⌋₊ / p : ℕ) : ℝ) ≤ fordQScale P Φ (J + 1))
    (hq : 0 < q) (hT : 0 < T) (hTbound : T ≤ ⌊P⌋₊ ^ J)
    (hmoment : FordVinogradovMomentBound s k C delta)
    (hIH : FordEquation310Eta s k r j C delta P eta Φ Esch J) :
    (fordKCountReal Υ s P (fordQScale P Φ J) q : ℝ) ≤
      fordLemma34KBound s k r J C delta P eta
        (fordMScale P Φ (J + 1)) (fordQScale P Φ (J + 1)) (Esch.E J) := by
  have hC : 0 ≤ C := hmoment.one_le_coefficient.trans' zero_le_one
  have hLnonneg : 0 ≤ fordLemma34LBound s k C delta P
      (fordQScale P Φ (J + 1)) (Esch.E J) := by
    unfold fordLemma34LBound
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (Esch.positive J hJj).le hC) (by positivity))
      (Real.rpow_nonneg (fordQScale_pos (zero_lt_one.trans_le hP) Φ _).le _)
  apply ford_lemma_3_4_real_one_step Υ (show 4 ≤ k by omega) hr2 hrk
    (show J < r by omega) (show J + 1 ≤ s by omega)
    hM (zero_lt_one.trans_le hP) hkM hPM hPbig hQbox hq hT hTbound
    hpacketTwo hpacketBound hquotient
  · intro Θ p hp
    exact hIH Θ hT hTbound p hp q hq
  · exact hLnonneg

#print axioms ford_equation_3_10_K_bound

end

end GafniTao
