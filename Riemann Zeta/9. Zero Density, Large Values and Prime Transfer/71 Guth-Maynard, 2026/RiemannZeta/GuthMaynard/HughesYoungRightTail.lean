import RiemannZeta.GuthMaynard.HughesYoungFiniteMoment

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# The absolutely convergent Hughes--Young product tail

The DFI argument is applied only to the effective conductor range.  This
file begins the complementary argument on `Re w = 2`: terms with large
product are dominated by a divisor Dirichlet series on an arbitrarily close
line to `Re s = 1`.  Keeping that comparison explicit is what permits the
tail loss to be absorbed into the final epsilon.
-/

/-- Exact norm of one opened divisor coefficient on a vertical line. -/
theorem norm_divisorDirichletTerm_afe_vertical_eq
    (t c u : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖divisorDirichletTerm
        (afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I)) n‖ =
      (n.divisors.card : ℝ) * (n : ℝ) ^ (-(1 / 2 + c : ℝ)) := by
  unfold divisorDirichletTerm
  rw [LSeries.norm_term_eq]
  simp only [hn.ne', if_false, afeCriticalPoint, Complex.add_re,
    Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, I_re, I_im,
    mul_zero, mul_one, sub_zero, add_zero]
  rw [div_eq_mul_inv, ← Real.rpow_neg (by positivity)]
  simp

/-- At `Re w = 2`, a positive divisor coefficient is the coefficient on
`Re s = 1+η` times the exact product-decay factor
`n^(-(3/2-η))`. -/
theorem norm_divisorDirichletTerm_two_eq_reference_mul
    {t u η : ℝ} {n : ℕ} (hn : 0 < n) :
    ‖divisorDirichletTerm
        (afeCriticalPoint t + ((2 : ℂ) + (u : ℂ) * I)) n‖ =
      ‖divisorDirichletTerm ((1 + η : ℝ) : ℂ) n‖ *
        (n : ℝ) ^ (-(3 / 2 - η : ℝ)) := by
  have htwo := norm_divisorDirichletTerm_afe_vertical_eq t 2 u hn
  have htwo' :
      ‖divisorDirichletTerm
          (afeCriticalPoint t + ((2 : ℂ) + (u : ℂ) * I)) n‖ =
        (n.divisors.card : ℝ) * (n : ℝ) ^ (-(1 / 2 + 2 : ℝ)) := by
    simpa using htwo
  have href := norm_divisorDirichletTerm_afe_vertical_eq 0 (1 / 2 + η) 0 hn
  have harg :
      afeCriticalPoint 0 +
          (((1 / 2 + η : ℝ) : ℂ) + (((0 : ℝ) : ℂ) * I)) =
        ((1 + η : ℝ) : ℂ) := by
    unfold afeCriticalPoint
    push_cast
    ring
  rw [harg] at href
  rw [htwo', href]
  rw [mul_assoc]
  congr 1
  rw [← Real.rpow_add (by exact_mod_cast hn)]
  congr 1
  ring

/-- The reference divisor norm series is summable for every positive
distance from the line `Re s = 1`. -/
theorem summable_norm_divisorDirichletTerm_one_add
    {η : ℝ} (hη : 0 < η) :
    Summable (fun n : ℕ =>
      ‖divisorDirichletTerm ((1 + η : ℝ) : ℂ) n‖) := by
  exact (summable_divisorDirichletTerm
    (show 1 < (((1 + η : ℝ) : ℂ)).re by simpa using add_lt_add_left hη 1)).norm

/-- The two-dimensional reference divisor majorant is summable. -/
theorem summable_norm_divisorPair_one_add
    {η : ℝ} (hη : 0 < η) :
    Summable (fun p : ℕ × ℕ =>
      ‖divisorDirichletTerm ((1 + η : ℝ) : ℂ) p.1‖ *
        ‖divisorDirichletTerm ((1 + η : ℝ) : ℂ) p.2‖) := by
  exact (summable_norm_divisorDirichletTerm_one_add hη).mul_of_nonneg
    (summable_norm_divisorDirichletTerm_one_add hη)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)

/-- The product tail of the opened divisor pair on `Re w = 2`. -/
noncomputable def hughesYoungRightPairProductTail
    (t u R : ℝ) : ℂ :=
  ∑' p : ℕ × ℕ,
    if R < (p.1 : ℝ) * p.2 then
      hughesYoungRightPairTerm t 2 u p
    else 0

/-- Total mass of the absolutely summable reference divisor pair. -/
noncomputable def hughesYoungReferenceDivisorPairMass (η : ℝ) : ℝ :=
  ∑' p : ℕ × ℕ,
    ‖divisorDirichletTerm ((1 + η : ℝ) : ℂ) p.1‖ *
      ‖divisorDirichletTerm ((1 + η : ℝ) : ℂ) p.2‖

theorem hughesYoungReferenceDivisorPairMass_nonneg (η : ℝ) :
    0 ≤ hughesYoungReferenceDivisorPairMass η := by
  unfold hughesYoungReferenceDivisorPairMass
  exact tsum_nonneg fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)

/-- Pointwise product-tail comparison on the absolutely convergent line. -/
theorem norm_hughesYoungRightPairTerm_tail_le
    {t u R η : ℝ} (hR : 0 < R) (hη : η < 3 / 2)
    (p : ℕ × ℕ) :
    ‖if R < (p.1 : ℝ) * p.2 then
        hughesYoungRightPairTerm t 2 u p
      else 0‖ ≤
      ‖hughesYoungRightContourWeight t 2 u‖ *
        R ^ (-(3 / 2 - η : ℝ)) *
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
    have hprodPos : 0 < (p.1 : ℝ) * p.2 := by positivity
    have hdecay :
        ((p.1 : ℝ) * p.2) ^ (-(3 / 2 - η : ℝ)) ≤
          R ^ (-(3 / 2 - η : ℝ)) := by
      exact Real.rpow_le_rpow_of_nonpos hR hp.le (by linarith)
    have hfirst :=
      norm_divisorDirichletTerm_two_eq_reference_mul
        (t := t) (u := u) (η := η) hp₁
    have hfirst' :
        ‖divisorDirichletTerm
            (afeCriticalPoint t + (((2 : ℝ) : ℂ) + (u : ℂ) * I)) p.1‖ =
          ‖divisorDirichletTerm ((1 + η : ℝ) : ℂ) p.1‖ *
            (p.1 : ℝ) ^ (-(3 / 2 - η : ℝ)) := by
      simpa using hfirst
    have hsecond :=
      norm_divisorDirichletTerm_two_eq_reference_mul
        (t := -t) (u := u) (η := η) hp₂
    have hsecond' :
        ‖divisorDirichletTerm
            (afeCriticalPoint (-t) + (((2 : ℝ) : ℂ) + (u : ℂ) * I)) p.2‖ =
          ‖divisorDirichletTerm ((1 + η : ℝ) : ℂ) p.2‖ *
            (p.2 : ℝ) ^ (-(3 / 2 - η : ℝ)) := by
      simpa using hsecond
    rw [hughesYoungRightPairTerm, norm_mul, norm_mul, hfirst', hsecond']
    let W : ℝ := ‖hughesYoungRightContourWeight t 2 u‖
    let A : ℝ := ‖divisorDirichletTerm ((1 + η : ℝ) : ℂ) p.1‖
    let B : ℝ := ‖divisorDirichletTerm ((1 + η : ℝ) : ℂ) p.2‖
    let x : ℝ := (p.1 : ℝ) ^ (-(3 / 2 - η : ℝ))
    let y : ℝ := (p.2 : ℝ) ^ (-(3 / 2 - η : ℝ))
    have hxy : x * y =
        ((p.1 : ℝ) * p.2) ^ (-(3 / 2 - η : ℝ)) := by
      dsimp only [x, y]
      exact (Real.mul_rpow (show 0 ≤ (p.1 : ℝ) by positivity)
        (show 0 ≤ (p.2 : ℝ) by positivity)).symm
    change W * (A * x) * (B * y) ≤
      W * R ^ (-(3 / 2 - η : ℝ)) * (A * B)
    calc
      W * (A * x) * (B * y) = W * (x * y) * (A * B) := by ring
      _ = W * (((p.1 : ℝ) * p.2) ^ (-(3 / 2 - η : ℝ))) *
          (A * B) := by rw [hxy]
      _ ≤ _ := by gcongr
  · rw [if_neg hp, norm_zero]
    positivity

/-- The product-tail family is absolutely summable. -/
theorem summable_norm_hughesYoungRightPairTerm_productTail
    {t u R η : ℝ} (hR : 0 < R) (hη0 : 0 < η) (hη : η < 3 / 2) :
    Summable (fun p : ℕ × ℕ =>
      ‖if R < (p.1 : ℝ) * p.2 then
          hughesYoungRightPairTerm t 2 u p
        else 0‖) := by
  let C : ℝ := ‖hughesYoungRightContourWeight t 2 u‖ *
    R ^ (-(3 / 2 - η : ℝ))
  have hmajor : Summable (fun p : ℕ × ℕ =>
      C * (‖divisorDirichletTerm ((1 + η : ℝ) : ℂ) p.1‖ *
        ‖divisorDirichletTerm ((1 + η : ℝ) : ℂ) p.2‖)) :=
    (summable_norm_divisorPair_one_add hη0).mul_left C
  apply hmajor.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro p
  simpa only [C, mul_assoc] using
    norm_hughesYoungRightPairTerm_tail_le hR hη p

/-- Quantitative bound for the complete product tail on `Re w = 2`. -/
theorem norm_hughesYoungRightPairProductTail_le
    {t u R η : ℝ} (hR : 0 < R) (hη0 : 0 < η) (hη : η < 3 / 2) :
    ‖hughesYoungRightPairProductTail t u R‖ ≤
      ‖hughesYoungRightContourWeight t 2 u‖ *
        R ^ (-(3 / 2 - η : ℝ)) *
        hughesYoungReferenceDivisorPairMass η := by
  unfold hughesYoungRightPairProductTail
  calc
    ‖∑' p : ℕ × ℕ,
        if R < (p.1 : ℝ) * p.2 then
          hughesYoungRightPairTerm t 2 u p else 0‖ ≤
      ∑' p : ℕ × ℕ,
        ‖if R < (p.1 : ℝ) * p.2 then
          hughesYoungRightPairTerm t 2 u p else 0‖ :=
      norm_tsum_le_tsum_norm
        (summable_norm_hughesYoungRightPairTerm_productTail hR hη0 hη)
    _ ≤ ∑' p : ℕ × ℕ,
        (‖hughesYoungRightContourWeight t 2 u‖ *
          R ^ (-(3 / 2 - η : ℝ))) *
          (‖divisorDirichletTerm ((1 + η : ℝ) : ℂ) p.1‖ *
            ‖divisorDirichletTerm ((1 + η : ℝ) : ℂ) p.2‖) := by
      exact
        (summable_norm_hughesYoungRightPairTerm_productTail hR hη0 hη).tsum_le_tsum
          (fun p => by
            simpa only [mul_assoc] using
              norm_hughesYoungRightPairTerm_tail_le hR hη p)
          ((summable_norm_divisorPair_one_add hη0).mul_left
            (‖hughesYoungRightContourWeight t 2 u‖ *
              R ^ (-(3 / 2 - η : ℝ))))
    _ = _ := by
      rw [tsum_mul_left]
      rfl

end RiemannZeta.GuthMaynard
