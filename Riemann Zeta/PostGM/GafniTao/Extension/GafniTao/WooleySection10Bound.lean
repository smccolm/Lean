import GafniTao.WooleySection10Chain

/-!
# Composing the Section 10 analytic recurrence

The source uses Vinogradov notation in (10.6).  Here the accumulated
constant `Cacc` and accumulated decay scale `E` are retained.  In particular,
`E ≥ n b₀` is proved from the exact inequalities `rho b' ≥ b` rather
than folded into asymptotic notation.
-/

namespace GafniTao

noncomputable section

/-- Exact finite composition of (10.8), including the endpoint state,
product weight, accumulated constant, and accumulated decay. -/
theorem WooleyIterationChain.composed_bound
    {k p n a b r : ℕ} {Lambda D delta theta : ℝ}
    {K : ℕ → ℕ → ℕ → ℝ}
    (hp : 2 ≤ p) (hD : 0 < D) (hK : ∀ r a b, 0 ≤ K r a b)
    (hchain : WooleyIterationChain
      k p Lambda D delta theta K n a b r) :
    ∃ aFinal bFinal rFinal : ℕ, ∃ R Cacc E : ℝ,
      delta * theta ≤ (aFinal : ℝ) ∧
      (k : ℝ) ^ 2 * (delta * theta) ≤ (bFinal : ℝ) ∧
      rFinal * aFinal ≤ (k - rFinal + 1) * bFinal ∧
      1 ≤ rFinal ∧ rFinal ≤ k - 1 ∧
      0 < R ∧ R ≤ 1 ∧
      (b : ℝ) ≤ R * (bFinal : ℝ) ∧
      bFinal ≤ k ^ (2 * n) * b ∧
      0 < Cacc ∧
      (n : ℝ) * (b : ℝ) ≤ E ∧
      K r a b ≤
        Cacc * (K rFinal aFinal bFinal) ^ R *
          (p : ℝ) ^ (-E * Lambda / (2 * (k : ℝ))) := by
  induction hchain with
  | nil a b r ha hb hrel hr hrk =>
      refine ⟨a, b, r, 1, 1, 0, ha, hb, hrel, hr, hrk,
        by norm_num, le_rfl, ?_, ?_, by norm_num, ?_, ?_⟩
      · simp
      · simp
      · simp
      · simp
  | @cons n a b r aPrime bPrime rPrime rho htransition htail ih =>
      rcases htransition with
        ⟨haPrime, hbPrime, hrelPrime, hrPrime, hrPrimeTop,
          hrho, hrhoOne, hgrowth, hupper, hceil, hweighted, hstepBound⟩
      obtain ⟨aFinal, bFinal, rFinal, R, Ctail, Etail,
        haFinal, hbFinal, hrelFinal, hrFinal, hrFinalTop,
        hRpos, hRone, hweightedTail, hscaleTail,
        hCtail, hEtail, htailBound⟩ := ih
      let R' : ℝ := rho * R
      let Cacc : ℝ := D * Ctail ^ rho
      let E : ℝ := (b : ℝ) + rho * Etail
      have hrhoNonneg : 0 ≤ rho := hrho.le
      have hR'pos : 0 < R' := mul_pos hrho hRpos
      have hR'one : R' ≤ 1 := by
        dsimp [R']
        nlinarith
      have hCacc : 0 < Cacc := by
        dsimp [Cacc]
        exact mul_pos hD (Real.rpow_pos_of_pos hCtail rho)
      have hE : ((n + 1 : ℕ) : ℝ) * (b : ℝ) ≤ E := by
        have hEtail' : (n : ℝ) * (bPrime : ℝ) ≤ Etail := hEtail
        have hmul := mul_le_mul_of_nonneg_left hEtail' hrhoNonneg
        have hbnonneg : (0 : ℝ) ≤ b := by positivity
        have hnnonneg : (0 : ℝ) ≤ n := by positivity
        have hweightedN : (n : ℝ) * (b : ℝ) ≤
            (n : ℝ) * (rho * (bPrime : ℝ)) :=
          mul_le_mul_of_nonneg_left hweighted hnnonneg
        dsimp [E]
        push_cast
        nlinarith
      have hKPrime : 0 ≤ K rPrime aPrime bPrime := hK _ _ _
      have hraised :
          (K rPrime aPrime bPrime) ^ rho ≤
            (Ctail * (K rFinal aFinal bFinal) ^ R *
              (p : ℝ) ^ (-Etail * Lambda / (2 * (k : ℝ)))) ^ rho :=
        Real.rpow_le_rpow hKPrime htailBound hrhoNonneg
      have hsubstitute : K r a b ≤
          D *
            (Ctail * (K rFinal aFinal bFinal) ^ R *
              (p : ℝ) ^ (-Etail * Lambda / (2 * (k : ℝ)))) ^ rho *
            (p : ℝ) ^ (-(b : ℝ) * Lambda /
              (2 * (k : ℝ))) := by
        calc
          K r a b ≤ D * (K rPrime aPrime bPrime) ^ rho *
              (p : ℝ) ^ (-(b : ℝ) * Lambda /
                (2 * (k : ℝ))) := hstepBound
          _ ≤ D *
              (Ctail * (K rFinal aFinal bFinal) ^ R *
                (p : ℝ) ^ (-Etail * Lambda / (2 * (k : ℝ)))) ^ rho *
              (p : ℝ) ^ (-(b : ℝ) * Lambda /
                (2 * (k : ℝ))) := by
            gcongr
      have hpReal : (0 : ℝ) < p := by positivity
      have hKFinal : 0 ≤ K rFinal aFinal bFinal := hK _ _ _
      have hKpow :
          ((K rFinal aFinal bFinal) ^ R) ^ rho =
            (K rFinal aFinal bFinal) ^ (rho * R) := by
        rw [← Real.rpow_mul hKFinal]
        congr 1
        ring
      have hPpow :
          ((p : ℝ) ^ (-Etail * Lambda / (2 * (k : ℝ)))) ^ rho *
              (p : ℝ) ^ (-(b : ℝ) * Lambda /
                (2 * (k : ℝ))) =
            (p : ℝ) ^
              (-((b : ℝ) + rho * Etail) * Lambda /
                (2 * (k : ℝ))) := by
        rw [← Real.rpow_mul hpReal.le, ← Real.rpow_add hpReal]
        congr 1
        ring
      have hrearrange :
          D *
              (Ctail * (K rFinal aFinal bFinal) ^ R *
                (p : ℝ) ^ (-Etail * Lambda / (2 * (k : ℝ)))) ^ rho *
              (p : ℝ) ^ (-(b : ℝ) * Lambda /
                (2 * (k : ℝ))) =
            Cacc * (K rFinal aFinal bFinal) ^ R' *
              (p : ℝ) ^ (-E * Lambda / (2 * (k : ℝ))) := by
        dsimp [Cacc, R', E]
        calc
          _ = D *
              (Ctail ^ rho *
                ((K rFinal aFinal bFinal) ^ R) ^ rho *
                ((p : ℝ) ^
                  (-Etail * Lambda / (2 * (k : ℝ)))) ^ rho) *
              (p : ℝ) ^ (-(b : ℝ) * Lambda /
                (2 * (k : ℝ))) := by
              rw [Real.mul_rpow (mul_nonneg hCtail.le
                    (Real.rpow_nonneg hKFinal R))
                  (Real.rpow_nonneg hpReal.le
                    (-Etail * Lambda / (2 * (k : ℝ)))),
                Real.mul_rpow hCtail.le (Real.rpow_nonneg hKFinal R)]
          _ = D * Ctail ^ rho *
                (K rFinal aFinal bFinal) ^ (rho * R) *
              (((p : ℝ) ^
                  (-Etail * Lambda / (2 * (k : ℝ)))) ^ rho *
                (p : ℝ) ^ (-(b : ℝ) * Lambda /
                  (2 * (k : ℝ)))) := by rw [hKpow]; ring
          _ = D * Ctail ^ rho *
                (K rFinal aFinal bFinal) ^ (rho * R) *
              (p : ℝ) ^
                (-((b : ℝ) + rho * Etail) * Lambda /
                  (2 * (k : ℝ))) := by rw [hPpow]
      refine ⟨aFinal, bFinal, rFinal, R', Cacc, E,
        haFinal, hbFinal, hrelFinal, hrFinal, hrFinalTop,
        hR'pos, hR'one, ?_, ?_, hCacc, hE, ?_⟩
      · calc
          (b : ℝ) ≤ rho * (bPrime : ℝ) := hweighted
          _ ≤ rho * (R * (bFinal : ℝ)) :=
            mul_le_mul_of_nonneg_left hweightedTail hrhoNonneg
          _ = R' * (bFinal : ℝ) := by dsimp [R']; ring
      · calc
          bFinal ≤ k ^ (2 * n) * bPrime := hscaleTail
          _ ≤ k ^ (2 * n) * (k ^ 2 * b) :=
            Nat.mul_le_mul_left _ hupper
          _ = k ^ (2 * (n + 1)) * b := by
            rw [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]
            simp only [mul_assoc]
      · exact hsubstitute.trans_eq hrearrange

#print axioms WooleyIterationChain.composed_bound

end

end GafniTao
