import RiemannZeta.GuthMaynard.HughesYoungHighLine

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Product tails on arbitrary Hughes--Young opening lines
-/

theorem norm_divisorDirichletTerm_vertical_eq_reference_mul
    {c t u η : ℝ} {n : ℕ} (hn : 0 < n) :
    ‖divisorDirichletTerm
        (afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I)) n‖ =
      ‖divisorDirichletTerm ((1 + η : ℝ) : ℂ) n‖ *
        (n : ℝ) ^ (-(c - 1 / 2 - η)) := by
  have heven := norm_divisorDirichletTerm_afe_vertical_eq
    t c u hn
  have heven' :
      ‖divisorDirichletTerm
          (afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I)) n‖ =
        (n.divisors.card : ℝ) *
          (n : ℝ) ^ (-(1 / 2 + c)) := heven
  have href := norm_divisorDirichletTerm_afe_vertical_eq
    0 (1 / 2 + η) 0 hn
  have harg :
      afeCriticalPoint 0 +
          (((1 / 2 + η : ℝ) : ℂ) + (((0 : ℝ) : ℂ) * I)) =
        ((1 + η : ℝ) : ℂ) := by
    unfold afeCriticalPoint
    push_cast
    ring
  rw [harg] at href
  rw [heven', href, mul_assoc]
  congr 1
  rw [← Real.rpow_add (by exact_mod_cast hn)]
  congr 1
  ring

/-- The `hughesYoungHighPairProductTail` definition used by the source-facing construction in `HughesYoungHighTail`. -/
noncomputable def hughesYoungHighPairProductTail
    (q : ℕ) (t u R : ℝ) : ℂ :=
  ∑' p : ℕ × ℕ,
    if R < (p.1 : ℝ) * p.2 then
      hughesYoungRightPairTerm t (2 * q) u p
    else 0

theorem norm_hughesYoungRightPairTerm_high_tail_le
    {q : ℕ} {t u R η : ℝ}
    (hR : 0 < R) (hη : η < 2 * (q : ℝ) - 1 / 2)
    (p : ℕ × ℕ) :
    ‖if R < (p.1 : ℝ) * p.2 then
        hughesYoungRightPairTerm t (2 * q) u p
      else 0‖ ≤
      ‖hughesYoungRightContourWeight t (2 * q) u‖ *
        R ^ (-(2 * (q : ℝ) - 1 / 2 - η)) *
        (‖divisorDirichletTerm ((1 + η : ℝ) : ℂ) p.1‖ *
          ‖divisorDirichletTerm ((1 + η : ℝ) : ℂ) p.2‖) := by
  by_cases hp : R < (p.1 : ℝ) * p.2
  · simp only [hp, if_true]
    have hp₁ : 0 < p.1 := by
      by_contra hz
      have : p.1 = 0 := Nat.eq_zero_of_not_pos hz
      simp [this] at hp
      linarith
    have hp₂ : 0 < p.2 := by
      by_contra hz
      have : p.2 = 0 := Nat.eq_zero_of_not_pos hz
      simp [this] at hp
      linarith
    have hdecay :
        ((p.1 : ℝ) * p.2) ^ (-(2 * (q : ℝ) - 1 / 2 - η)) ≤
          R ^ (-(2 * (q : ℝ) - 1 / 2 - η)) := by
      exact Real.rpow_le_rpow_of_nonpos hR hp.le (by linarith)
    have hfirst := norm_divisorDirichletTerm_vertical_eq_reference_mul
      (c := 2 * (q : ℝ)) (t := t) (u := u) (η := η) hp₁
    have hsecond := norm_divisorDirichletTerm_vertical_eq_reference_mul
      (c := 2 * (q : ℝ)) (t := -t) (u := u) (η := η) hp₂
    rw [hughesYoungRightPairTerm, norm_mul, norm_mul, hfirst, hsecond]
    let W : ℝ := ‖hughesYoungRightContourWeight t (2 * q) u‖
    let A : ℝ := ‖divisorDirichletTerm ((1 + η : ℝ) : ℂ) p.1‖
    let B : ℝ := ‖divisorDirichletTerm ((1 + η : ℝ) : ℂ) p.2‖
    let a : ℝ := -(2 * (q : ℝ) - 1 / 2 - η)
    have hxy : (p.1 : ℝ) ^ a * (p.2 : ℝ) ^ a =
        ((p.1 : ℝ) * p.2) ^ a := by
      exact (Real.mul_rpow (show 0 ≤ (p.1 : ℝ) by positivity)
        (show 0 ≤ (p.2 : ℝ) by positivity)).symm
    change W * (A * (p.1 : ℝ) ^ a) *
        (B * (p.2 : ℝ) ^ a) ≤
      W * R ^ a * (A * B)
    calc
      W * (A * (p.1 : ℝ) ^ a) * (B * (p.2 : ℝ) ^ a) =
          W * ((p.1 : ℝ) ^ a * (p.2 : ℝ) ^ a) * (A * B) := by ring
      _ = W * (((p.1 : ℝ) * p.2) ^ a) * (A * B) := by rw [hxy]
      _ ≤ _ := by gcongr
  · rw [if_neg hp, norm_zero]
    positivity

theorem summable_norm_hughesYoungRightPairTerm_high_tail
    {q : ℕ} {t u R η : ℝ}
    (hR : 0 < R) (hη0 : 0 < η)
    (hη : η < 2 * (q : ℝ) - 1 / 2) :
    Summable (fun p : ℕ × ℕ =>
      ‖if R < (p.1 : ℝ) * p.2 then
          hughesYoungRightPairTerm t (2 * q) u p
        else 0‖) := by
  let C : ℝ := ‖hughesYoungRightContourWeight t (2 * q) u‖ *
    R ^ (-(2 * (q : ℝ) - 1 / 2 - η))
  have hmajor : Summable (fun p : ℕ × ℕ =>
      C * (‖divisorDirichletTerm ((1 + η : ℝ) : ℂ) p.1‖ *
        ‖divisorDirichletTerm ((1 + η : ℝ) : ℂ) p.2‖)) :=
    (summable_norm_divisorPair_one_add hη0).mul_left C
  apply hmajor.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro p
  simpa only [C, mul_assoc] using
    norm_hughesYoungRightPairTerm_high_tail_le hR hη p

theorem norm_hughesYoungHighPairProductTail_le
    {q : ℕ} {t u R η : ℝ}
    (hR : 0 < R) (hη0 : 0 < η)
    (hη : η < 2 * (q : ℝ) - 1 / 2) :
    ‖hughesYoungHighPairProductTail q t u R‖ ≤
      ‖hughesYoungRightContourWeight t (2 * q) u‖ *
        R ^ (-(2 * (q : ℝ) - 1 / 2 - η)) *
        hughesYoungReferenceDivisorPairMass η := by
  unfold hughesYoungHighPairProductTail
  calc
    ‖∑' p : ℕ × ℕ,
        if R < (p.1 : ℝ) * p.2 then
          hughesYoungRightPairTerm t (2 * q) u p else 0‖ ≤
      ∑' p : ℕ × ℕ,
        ‖if R < (p.1 : ℝ) * p.2 then
          hughesYoungRightPairTerm t (2 * q) u p else 0‖ :=
      norm_tsum_le_tsum_norm
        (summable_norm_hughesYoungRightPairTerm_high_tail hR hη0 hη)
    _ ≤ ∑' p : ℕ × ℕ,
        (‖hughesYoungRightContourWeight t (2 * q) u‖ *
          R ^ (-(2 * (q : ℝ) - 1 / 2 - η))) *
          (‖divisorDirichletTerm ((1 + η : ℝ) : ℂ) p.1‖ *
            ‖divisorDirichletTerm ((1 + η : ℝ) : ℂ) p.2‖) := by
      exact
        (summable_norm_hughesYoungRightPairTerm_high_tail hR hη0 hη).tsum_le_tsum
          (fun p => by
            simpa only [mul_assoc] using
              norm_hughesYoungRightPairTerm_high_tail_le hR hη p)
          ((summable_norm_divisorPair_one_add hη0).mul_left
            (‖hughesYoungRightContourWeight t (2 * q) u‖ *
              R ^ (-(2 * (q : ℝ) - 1 / 2 - η))))
    _ = _ := by
      rw [tsum_mul_left]
      rfl

/-- Uniform finite-height integral bound for the complete product tail on
an arbitrary even opening line. -/
theorem exists_intervalIntegral_hughesYoungHighPairProductTail_le
    (q : ℕ) (hq : 0 < q) (η : ℝ) (hη0 : 0 < η)
    (hη : η < 2 * (q : ℝ) - 1 / 2) :
    ∃ L : ℝ, 0 < L ∧ ∀ {T t R H : ℝ},
      1 ≤ T → t ∈ Set.Icc (T / 4) (4 * T) → 0 < R → 0 ≤ H →
      ‖∫ u in -H..H, hughesYoungHighPairProductTail q t u R‖ ≤
        (256 * Real.exp (400 * (q : ℝ) ^ 2) *
          ((7 + 2 * (q : ℝ)) * T) ^ (4 * q + 8) *
          R ^ (-(2 * (q : ℝ) - 1 / 2 - η)) *
          hughesYoungReferenceDivisorPairMass η) * L := by
  obtain ⟨L, hL, hmoment⟩ :=
    exists_intervalIntegral_exp_neg_84_mul_one_add_abs_pow_le (4 * q + 16)
  let K : ℝ := 625 * (2 * (q : ℝ) + 1) ^ 8
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K * L, mul_pos hK hL, ?_⟩
  intro T t R H hT ht hR hH
  let C : ℝ := 256 * Real.exp (400 * (q : ℝ) ^ 2) *
    ((7 + 2 * (q : ℝ)) * T) ^ (4 * q + 8) *
    R ^ (-(2 * (q : ℝ) - 1 / 2 - η)) *
    hughesYoungReferenceDivisorPairMass η
  let g : ℝ → ℝ := fun u =>
    Real.exp (-84 * u ^ 2) * (1 + |u|) ^ (4 * q + 16)
  have hC0 : 0 ≤ C := by
    unfold C
    exact mul_nonneg (by positivity)
      (hughesYoungReferenceDivisorPairMass_nonneg η)
  have hg : IntervalIntegrable g volume (-H) H :=
    (integrable_exp_neg_84_mul_one_add_abs_pow (4 * q + 16)).intervalIntegrable
  have horder : -H ≤ H := by linarith
  calc
    ‖∫ u in -H..H, hughesYoungHighPairProductTail q t u R‖ ≤
        ∫ u in -H..H, (C * K) * g u := by
      apply intervalIntegral.norm_integral_le_of_norm_le horder
      · filter_upwards with u hu
        have hweight :=
          norm_hughesYoungRightContourWeight_even_le_on_height_support
            hT ht hq u
        have htail := norm_hughesYoungHighPairProductTail_le
          (q := q) (t := t) (u := u) (R := R) (η := η) hR hη0 hη
        have hexp :
            Real.exp (400 * (q : ℝ) ^ 2 - 84 * u ^ 2) =
              Real.exp (400 * (q : ℝ) ^ 2) *
                Real.exp (-84 * u ^ 2) := by
          rw [← Real.exp_add]
          congr 1
          ring
        have hbasepow :
            ((7 + 2 * (q : ℝ)) * T * (1 + |u|)) ^ (4 * q + 8) =
              ((7 + 2 * (q : ℝ)) * T) ^ (4 * q + 8) *
                (1 + |u|) ^ (4 * q + 8) := by
          rw [mul_pow]
        calc
          ‖hughesYoungHighPairProductTail q t u R‖ ≤
              ‖hughesYoungRightContourWeight t (2 * q) u‖ *
                R ^ (-(2 * (q : ℝ) - 1 / 2 - η)) *
                hughesYoungReferenceDivisorPairMass η := htail
          _ ≤ (160000 * (2 * (q : ℝ) + 1) ^ 8 *
                Real.exp (400 * (q : ℝ) ^ 2 - 84 * u ^ 2) *
                ((7 + 2 * (q : ℝ)) * T * (1 + |u|)) ^ (4 * q + 8) *
                (1 + |u|) ^ 8) *
                R ^ (-(2 * (q : ℝ) - 1 / 2 - η)) *
                hughesYoungReferenceDivisorPairMass η := by
              gcongr
              exact hughesYoungReferenceDivisorPairMass_nonneg η
          _ = (C * K) * g u := by
              rw [hexp, hbasepow]
              unfold C g
              ring
      · exact hg.const_mul (C * K)
    _ = (C * K) * (∫ u in -H..H, g u) := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ (C * K) * L := by
      exact mul_le_mul_of_nonneg_left (hmoment hH)
        (mul_nonneg hC0 hK.le)
    _ = _ := by ring

end RiemannZeta.GuthMaynard
