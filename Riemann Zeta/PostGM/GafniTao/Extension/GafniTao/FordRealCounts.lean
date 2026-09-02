import GafniTao.FordLemma34Recurrence

/-!
# Real-endpoint forms of Ford's finite counts

Ford states Lemma 3.4 with real scales `P`, `M_i`, and `Q_i`; the variables
remain integral.  These wrappers make the source convention explicit by
taking natural floors once, at the boundary of the finite count.
-/

namespace GafniTao

noncomputable section

def fordKCountReal
    {k d T : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (s : ℕ) (P Q : ℝ) (q : ℕ) : ℕ :=
  fordKCount Ψ s ⌊P⌋₊ ⌊Q⌋₊ q

def fordLCountReal
    {k d T : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (s : ℕ) (P Q : ℝ) (p q r : ℕ) : ℕ :=
  fordLCount Ψ s ⌊P⌋₊ ⌊Q⌋₊ p q r

theorem fordKCountReal_mono_Q
    {k d T s q : ℕ} {P Q R : ℝ}
    (Ψ : FordIntegerPolynomialSystem k d T)
    (hQR : Q ≤ R) :
    fordKCountReal Ψ s P Q q ≤ fordKCountReal Ψ s P R q := by
  unfold fordKCountReal
  exact fordKCount_mono_Q Ψ (Nat.floor_mono hQR)

theorem fordLCountReal_mono_Q
    {k d T s p q r : ℕ} {P Q R : ℝ}
    (Ψ : FordIntegerPolynomialSystem k d T)
    (hQR : Q ≤ R) :
    fordLCountReal Ψ s P Q p q r ≤ fordLCountReal Ψ s P R p q r := by
  unfold fordLCountReal
  exact fordLCount_mono_Q Ψ (Nat.floor_mono hQR)

theorem fordLCountReal_terminal_le
    {k d T s p q r : ℕ} {P Q : ℝ}
    (Ψ : FordIntegerPolynomialSystem k d T)
    (hp : 0 < p) (hq : 0 < q) (hP : 0 ≤ P)
    (hPpr : P < p ^ r) :
    fordLCountReal Ψ s P Q p q r ≤
      ⌊P⌋₊ ^ k * fordVinogradovMoment s k Q := by
  unfold fordLCountReal fordVinogradovMoment
  apply fordLCount_terminal_le Ψ hp hq
  have hreal : (⌊P⌋₊ : ℝ) < (p ^ r : ℕ) := by
    simpa using (Nat.floor_le hP).trans_lt hPpr
  exact_mod_cast hreal

theorem fordLCountReal_terminal_le_moment_bound
    {k d T s p q r : ℕ} {P Q C delta : ℝ}
    (Ψ : FordIntegerPolynomialSystem k d T)
    (hp : 0 < p) (hq : 0 < q) (hP : 1 ≤ P) (hQ : 1 ≤ Q)
    (hPpr : P < p ^ r)
    (hmoment : ∀ R : ℝ, 1 ≤ R →
      (fordVinogradovMoment s k R : ℝ) ≤
        C * R ^ fordLambda34 s k delta) :
    (fordLCountReal Ψ s P Q p q r : ℝ) ≤
      C * P ^ k * Q ^ fordLambda34 s k delta := by
  have hterminal := fordLCountReal_terminal_le (s := s) (Q := Q) Ψ hp hq
    (zero_le_one.trans hP) hPpr
  have hterminalR :
      (fordLCountReal Ψ s P Q p q r : ℝ) ≤
        (⌊P⌋₊ : ℝ) ^ k * fordVinogradovMoment s k Q := by
    exact_mod_cast hterminal
  have hfloorP : (⌊P⌋₊ : ℝ) ≤ P := Nat.floor_le (zero_le_one.trans hP)
  have hpowP : (⌊P⌋₊ : ℝ) ^ k ≤ P ^ k :=
    pow_le_pow_left₀ (by positivity) hfloorP k
  have hmomentQ := hmoment Q hQ
  have hmomentNonneg : (0 : ℝ) ≤ fordVinogradovMoment s k Q := by positivity
  have hPpowNonneg : 0 ≤ P ^ k := by positivity
  calc
    (fordLCountReal Ψ s P Q p q r : ℝ) ≤
        (⌊P⌋₊ : ℝ) ^ k * fordVinogradovMoment s k Q := hterminalR
    _ ≤ P ^ k * fordVinogradovMoment s k Q :=
      mul_le_mul_of_nonneg_right hpowP hmomentNonneg
    _ ≤ P ^ k * (C * Q ^ fordLambda34 s k delta) := by
      exact mul_le_mul_of_nonneg_left hmomentQ hPpowNonneg
    _ = C * P ^ k * Q ^ fordLambda34 s k delta := by ring

#print axioms fordKCountReal_mono_Q
#print axioms fordLCountReal_mono_Q
#print axioms fordLCountReal_terminal_le
#print axioms fordLCountReal_terminal_le_moment_bound

end

end GafniTao
