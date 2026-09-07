import GafniTao.HeathBrownMellinShift

/-!
# Uniform bounds for the harmless terms in Heath--Brown's Mellin shift

The right-hand divisor series in the exact shift is exponentially smoothed.
This file records a literal, summable majorant which is independent of the
height and of the real part once that real part is nonnegative.  No abstract
boundedness hypothesis is introduced.
-/

open Complex Filter ArithmeticFunction
open scoped BigOperators Topology

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- A concrete absolute constant dominating the exponentially smoothed
divisor series. -/
noncomputable def heathBrownSmoothedDivisorMajorant : ℝ :=
  ∑' n : ℕ, (n : ℝ) * Real.exp (-(n : ℝ))

theorem summable_heathBrownSmoothedDivisorMajorant :
    Summable (fun n : ℕ => (n : ℝ) * Real.exp (-(n : ℝ))) := by
  simpa only [pow_one, one_mul, neg_one_mul] using
    (Real.summable_pow_mul_exp_neg_nat_mul 1 (show (0 : ℝ) < 1 by norm_num))

theorem heathBrownSmoothedDivisorMajorant_nonneg :
    0 ≤ heathBrownSmoothedDivisorMajorant := by
  unfold heathBrownSmoothedDivisorMajorant
  exact tsum_nonneg fun n => mul_nonneg (Nat.cast_nonneg' n) (Real.exp_pos _).le

theorem norm_heathBrownSmoothedDivisorTerm_le
    {s : ℂ} (hs : 0 ≤ s.re) (n : ℕ) :
    ‖heathBrownSmoothedDivisorTerm s n‖ ≤
      (n : ℝ) * Real.exp (-(n : ℝ)) := by
  by_cases hn : n = 0
  · subst n
    simp [heathBrownSmoothedDivisorTerm]
  · have hnNatPos : 0 < n := Nat.pos_of_ne_zero hn
    have hnPos : (0 : ℝ) < n := by exact_mod_cast hnNatPos
    have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hnNatPos
    have hCard : (n.divisors.card : ℝ) ≤ n := by
      exact_mod_cast Nat.card_divisors_le_self n
    have hPow : ‖(n : ℂ) ^ (-s)‖ = (n : ℝ) ^ (-s.re) := by
      rw [show (n : ℂ) = ((n : ℝ) : ℂ) by norm_num,
        Complex.norm_cpow_eq_rpow_re_of_pos hnPos]
      simp
    have hPowOne : (n : ℝ) ^ (-s.re) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hnOne (by linarith)
    unfold heathBrownSmoothedDivisorTerm
    rw [if_neg hn, norm_mul, norm_mul, Complex.norm_natCast, hPow]
    simp only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    have hCardNonneg : 0 ≤ (n.divisors.card : ℝ) := by positivity
    have hExpNonneg : 0 ≤ Real.exp (-(n : ℝ)) := (Real.exp_pos _).le
    calc
      (n.divisors.card : ℝ) * (n : ℝ) ^ (-s.re) *
          Real.exp (-(n : ℝ)) ≤
        (n : ℝ) * 1 * Real.exp (-(n : ℝ)) := by
          gcongr
      _ = (n : ℝ) * Real.exp (-(n : ℝ)) := by ring

theorem summable_norm_heathBrownSmoothedDivisorTerm
    {s : ℂ} (hs : 0 ≤ s.re) :
    Summable (fun n : ℕ => ‖heathBrownSmoothedDivisorTerm s n‖) :=
  summable_heathBrownSmoothedDivisorMajorant.of_nonneg_of_le
    (fun _ => norm_nonneg _) (norm_heathBrownSmoothedDivisorTerm_le hs)

theorem norm_heathBrownSmoothedDivisorSeries_le
    {s : ℂ} (hs : 0 ≤ s.re) :
    ‖heathBrownSmoothedDivisorSeries s‖ ≤
      heathBrownSmoothedDivisorMajorant := by
  unfold heathBrownSmoothedDivisorSeries heathBrownSmoothedDivisorMajorant
  calc
    ‖∑' n : ℕ, heathBrownSmoothedDivisorTerm s n‖ ≤
        ∑' n : ℕ, ‖heathBrownSmoothedDivisorTerm s n‖ :=
      norm_tsum_le_tsum_norm (summable_norm_heathBrownSmoothedDivisorTerm hs)
    _ ≤ ∑' n : ℕ, (n : ℝ) * Real.exp (-(n : ℝ)) :=
      (summable_norm_heathBrownSmoothedDivisorTerm hs).tsum_le_tsum
        (norm_heathBrownSmoothedDivisorTerm_le hs)
        summable_heathBrownSmoothedDivisorMajorant

/-- Exponential Gamma decay on the positive strip containing
`1 + (1/2 - delta)`. -/
theorem exists_norm_Gamma_heathBrown_residue_strip_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (a v : ℝ),
      5 / 4 ≤ a → a ≤ 3 / 2 →
      ‖Complex.Gamma ((a : ℂ) + (v : ℂ) * I)‖ ≤
        C * Real.exp (-|v|) := by
  obtain ⟨D, hD, hShift⟩ :=
    exists_norm_Gamma_right_displacement_le
      (a := (1 / 2 : ℝ)) (b := (3 / 2 : ℝ)) (by norm_num)
  let C : ℝ := 6 * Real.exp D
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro a v haLower haUpper
  let z : ℂ := (1 / 2 : ℂ) + (v : ℂ) * I
  let d : ℝ := a - 1 / 2
  have hdLower : 0 ≤ d := by dsimp only [d]; linarith
  have hdUpper : d ≤ 1 := by dsimp only [d]; linarith
  have hzRe : z.re = 1 / 2 := by simp [z]
  have hzIm : |z.im| = |v| := by simp [z]
  have hzAdd : z + (d : ℂ) = (a : ℂ) + (v : ℂ) * I := by
    apply Complex.ext <;> simp [z, d]
  have hDisplaced := hShift z d (by rw [hzRe])
    (by rw [hzRe]; dsimp only [d]; linarith) hdLower
  have hHalf := norm_Gamma_half_vertical_le_exp v
  have hLogNonneg : 0 ≤ Real.log (|v| + 2) :=
    Real.log_nonneg (by linarith [abs_nonneg v])
  have hRatePos : 0 ≤ Real.log (|v| + 2) + D := by linarith
  have hExponent :
      (Real.log (|v| + 2) + D) * d ≤
        Real.log (|v| + 2) + D := by
    nlinarith
  have hExpShift :
      Real.exp ((Real.log (|v| + 2) + D) * d) ≤
        (|v| + 2) * Real.exp D := by
    calc
      Real.exp ((Real.log (|v| + 2) + D) * d) ≤
          Real.exp (Real.log (|v| + 2) + D) :=
        Real.exp_le_exp.mpr hExponent
      _ = (|v| + 2) * Real.exp D := by
        rw [Real.exp_add, Real.exp_log (by positivity)]
  rw [hzIm, hzAdd] at hDisplaced
  calc
    ‖Complex.Gamma ((a : ℂ) + (v : ℂ) * I)‖ ≤
        ‖Complex.Gamma z‖ *
          Real.exp ((Real.log (|v| + 2) + D) * d) := hDisplaced
    _ ≤ (3 * Real.exp (-(Real.pi * |v|) / 2)) *
        ((|v| + 2) * Real.exp D) := by gcongr
    _ ≤ (3 * (2 * Real.exp (-|v|))) * Real.exp D := by
      have hAbsorb :=
        add_two_mul_exp_neg_pi_half_le_exp_neg |v| (abs_nonneg v)
      nlinarith [Real.exp_pos D]
    _ = C * Real.exp (-|v|) := by
      dsimp only [C]
      ring

/-- Gamma decay at the moving zeta pole `1-s`, uniformly for the small
positive displacement used by Heath--Brown. -/
theorem exists_norm_Gamma_heathBrown_movingPole_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (delta v : ℝ),
      0 < delta → delta ≤ 1 / 4 →
      ‖Complex.Gamma
          (((1 / 2 - delta : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤
        C * Real.exp (-|v|) := by
  obtain ⟨B, hB, hStrip⟩ :=
    exists_norm_Gamma_heathBrown_residue_strip_le
  let C : ℝ := 4 * B
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro delta v hdelta hdeltaUpper
  let p : ℂ := ((1 / 2 - delta : ℝ) : ℂ) + (v : ℂ) * I
  have hpRe : p.re = 1 / 2 - delta := by simp [p]
  have hpNonzero : p ≠ 0 := by
    intro hp
    have hre := congrArg Complex.re hp
    rw [hpRe] at hre
    norm_num at hre
    linarith
  have harg : p + 1 =
      ((3 / 2 - delta : ℝ) : ℂ) + (v : ℂ) * I := by
    apply Complex.ext <;> simp [p]
    ring
  have hUpper :
      ‖Complex.Gamma (p + 1)‖ ≤ B * Real.exp (-|v|) := by
    rw [harg]
    exact hStrip (3 / 2 - delta) v (by linarith) (by linarith)
  have hRec := Complex.Gamma_add_one p hpNonzero
  have hRecNorm : ‖Complex.Gamma (p + 1)‖ =
      ‖p‖ * ‖Complex.Gamma p‖ := by
    rw [hRec, norm_mul]
  have hpNormLower : (1 / 4 : ℝ) ≤ ‖p‖ := by
    have hre := Complex.abs_re_le_norm p
    rw [hpRe, abs_of_pos (by linarith : 0 < 1 / 2 - delta)] at hre
    linarith
  have hGamma : ‖Complex.Gamma p‖ ≤
      4 * (B * Real.exp (-|v|)) := by
    rw [hRecNorm] at hUpper
    nlinarith [norm_nonneg (Complex.Gamma p), Real.exp_pos (-|v|)]
  simpa only [p, C, mul_assoc] using hGamma

/-- The moving double-pole residue is uniformly bounded on the source
critical strip for positive heights. -/
theorem exists_norm_heathBrownMovingPoleResidue_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (delta t : ℝ),
      0 < delta → delta ≤ 1 / 4 → 10 ≤ t →
      ‖heathBrownMovingPoleResidue
          (((1 / 2 + delta : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ C := by
  obtain ⟨B, hB, hGamma⟩ :=
    exists_norm_Gamma_heathBrown_movingPole_le
  obtain ⟨D, hD, hDigamma⟩ :=
    Complex.exists_norm_digamma_le_log
      (a := (1 / 4 : ℝ)) (b := (1 / 2 : ℝ)) (by norm_num)
  let R : ℝ := ‖deriv riemannZetaPoleRemoved 0‖
  let C : ℝ := B * (2 * D + 2 * R + 1)
  refine ⟨C, by dsimp only [C, R]; positivity, ?_⟩
  intro delta t hdelta hdeltaUpper ht
  let s : ℂ := ((1 / 2 + delta : ℝ) : ℂ) + (t : ℂ) * I
  let p : ℂ := heathBrownMovingPole s
  have hp : p = ((1 / 2 - delta : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [p, s, heathBrownMovingPole]
    ring
  have hpRe : p.re = 1 / 2 - delta := by rw [hp]; simp
  have hpIm : |p.im| = |t| := by rw [hp]; simp
  have hpPos : 0 < p.re := by rw [hpRe]; linarith
  have hGammaP : ‖Complex.Gamma p‖ ≤ B * Real.exp (-t) := by
    rw [hp]
    have h := hGamma delta (-t) hdelta hdeltaUpper
    simpa [abs_of_nonneg (by linarith : 0 ≤ t)] using h
  have hDigammaP : ‖Complex.digamma p‖ ≤ D * Real.log (t + 2) := by
    have h := hDigamma p (by rw [hpRe]; linarith)
      (by rw [hpRe]; linarith)
    rw [hpIm, abs_of_nonneg (by linarith : 0 ≤ t)] at h
    exact h
  have hLog : Real.log (t + 2) ≤ t + 1 := by
    have h := Real.log_le_sub_one_of_pos (by linarith : 0 < t + 2)
    linarith
  have hExp : Real.exp (-t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have hTExp : t * Real.exp (-t) ≤ 1 := by
    have h := Real.mul_exp_neg_le_exp_neg_one t
    have he : Real.exp (-1) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by norm_num)
    linarith
  have hLogExp : Real.exp (-t) * Real.log (t + 2) ≤ 2 := by
    have hExpNonneg := (Real.exp_pos (-t)).le
    have hLogNonneg := Real.log_nonneg (by linarith : 1 ≤ t + 2)
    calc
      Real.exp (-t) * Real.log (t + 2) ≤
          Real.exp (-t) * (t + 1) := by gcongr
      _ = t * Real.exp (-t) + Real.exp (-t) := by ring
      _ ≤ 2 := by linarith
  have hResidueEq := heathBrownMovingPoleResidue_eq (s := s) hpPos
  change ‖heathBrownMovingPoleResidue s‖ ≤ C
  rw [hResidueEq]
  calc
    ‖Complex.Gamma p * Complex.digamma p +
        2 * Complex.Gamma p * deriv riemannZetaPoleRemoved 0‖ ≤
      ‖Complex.Gamma p‖ * ‖Complex.digamma p‖ +
        2 * ‖Complex.Gamma p‖ * R := by
          dsimp only [R]
          calc
            _ ≤ ‖Complex.Gamma p * Complex.digamma p‖ +
                ‖2 * Complex.Gamma p * deriv riemannZetaPoleRemoved 0‖ :=
              norm_add_le _ _
            _ = _ := by simp
    _ ≤ (B * Real.exp (-t)) * (D * Real.log (t + 2)) +
        2 * (B * Real.exp (-t)) * R := by gcongr
    _ = B * (D * (Real.exp (-t) * Real.log (t + 2)) +
        2 * R * Real.exp (-t)) := by ring
    _ ≤ B * (D * 2 + 2 * R * 1) := by
      have hR : 0 ≤ R := by dsimp only [R]; positivity
      gcongr
    _ = B * (2 * D + 2 * R) := by ring
    _ ≤ C := by
      dsimp only [C, R]
      nlinarith [hB.le]


end

end GafniTao
