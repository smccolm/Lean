import TaoTrudgianYang2025.ClassicalDirectSourceSupport

/-!
# Bounded Fourier extraction for a fixed Schwartz profile

The input is an actual finite weighted sum of positive natural-number
phases. An arbitrary-order Fourier tail estimate yields a coefficient-one
sum inside a bounded ordinate window. All scale factors remain explicit.
-/

noncomputable section
open scoped BigOperators FourierTransform
open MeasureTheory Complex
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

def finiteFourierMass (f : SchwartzMap ℝ ℂ) : ℝ :=
  1 + ∫ ξ : ℝ, ‖𝓕 f ξ‖

theorem finiteFourierMass_pos (f : SchwartzMap ℝ ℂ) :
    0 < finiteFourierMass f := by
  have h : 0 ≤ ∫ ξ : ℝ, ‖𝓕 f ξ‖ :=
    MeasureTheory.integral_nonneg (fun ξ : ℝ => norm_nonneg (𝓕 f ξ))
  unfold finiteFourierMass
  linarith

theorem norm_schwartz_logShift_finite_sum_tail_le
    (f : SchwartzMap ℝ ℂ) (S : Finset ℕ) (k : ℕ) (c a t R : ℝ)
    (hS : ∀ n ∈ S, 0 < n) (hc : 0 ≤ c) (hk : 1 < k) (hR : 0 < R) :
    ‖((c : ℝ) : ℂ) *
      ∫ ξ : ℝ in (Set.Icc (-R) R)ᶜ,
        𝓕 (f) ξ *
          Complex.exp
            (-(((2 * Real.pi * ξ * a : ℝ) : ℂ) * I)) *
          ∑ n ∈ S,
            (n : ℂ) ^
              (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * I)‖ ≤
      c * (S).card *
        ((2 * SchwartzMap.seminorm ℝ k 0
            (𝓕 (f)) / ((k : ℝ) - 1)) *
          R ^ (1 - (k : ℝ))) := by
  let P : ℝ → ℂ := fun ξ =>
    ∑ n ∈ S, (n : ℂ) ^ (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * I)
  let g : ℝ → ℂ := fun ξ =>
    𝓕 f ξ *
      Complex.exp
        (-(((2 * Real.pi * ξ * a : ℝ) : ℂ) * I)) *
      P ξ
  have hPbound : ∀ ξ : ℝ, ‖P ξ‖ ≤ S.card := by
    intro ξ
    calc
      ‖P ξ‖ ≤ ∑ n ∈ S,
          ‖(n : ℂ) ^ (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * I)‖ :=
        norm_sum_le _ _
      _ = ∑ _n ∈ S, 1 := by
        apply Finset.sum_congr rfl
        intro n hn
        have hnPos : 0 < n := hS n hn
        rw [Complex.norm_natCast_cpow_of_pos hnPos]
        simp
      _ = S.card := by simp
  have hmajorInt : MeasureTheory.Integrable
      (fun ξ : ℝ => ‖𝓕 f ξ‖ * (S.card : ℝ)) :=
    (𝓕 f).integrable.norm.mul_const _
  have hnorm :
      ‖∫ ξ : ℝ in (Set.Icc (-R) R)ᶜ, g ξ‖ ≤
        ∫ ξ : ℝ in (Set.Icc (-R) R)ᶜ,
          ‖𝓕 f ξ‖ * (S.card : ℝ) := by
    apply MeasureTheory.norm_integral_le_of_norm_le hmajorInt.integrableOn
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc.compl]
      with ξ _
    change ‖𝓕 f ξ *
      Complex.exp
        (-(((2 * Real.pi * ξ * a : ℝ) : ℂ) * I)) *
      P ξ‖ ≤ ‖𝓕 f ξ‖ * (S.card : ℝ)
    rw [norm_mul, norm_mul]
    have hphaseNorm :
        ‖Complex.exp
          (-(((2 * Real.pi * ξ * a : ℝ) : ℂ) * I))‖ = 1 := by
      simpa only [ofReal_neg, neg_mul] using
        Complex.norm_exp_ofReal_mul_I
          (-(2 * Real.pi * ξ * a))
    rw [hphaseNorm, mul_one]
    exact mul_le_mul_of_nonneg_left (hPbound ξ) (norm_nonneg _)
  have htail := integral_norm_fourier_schwartz_compl_Icc_le_order
    f k hk R hR
  calc
    ‖((c : ℝ) : ℂ) *
      ∫ ξ : ℝ in (Set.Icc (-R) R)ᶜ,
        𝓕 (f) ξ *
          Complex.exp
            (-(((2 * Real.pi * ξ * a : ℝ) : ℂ) * I)) *
          ∑ n ∈ S,
            (n : ℂ) ^
              (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * I)‖ =
        c *
          ‖∫ ξ : ℝ in (Set.Icc (-R) R)ᶜ, g ξ‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg hc]
    _ ≤ c *
        (∫ ξ : ℝ in (Set.Icc (-R) R)ᶜ,
          ‖𝓕 f ξ‖ * (S.card : ℝ)) :=
      mul_le_mul_of_nonneg_left hnorm hc
    _ = c *
        ((∫ ξ : ℝ in (Set.Icc (-R) R)ᶜ, ‖𝓕 f ξ‖) * S.card) := by
      rw [MeasureTheory.integral_mul_const]
    _ ≤ c *
        (((2 * SchwartzMap.seminorm ℝ k 0 (𝓕 f) / ((k : ℝ) - 1)) *
          R ^ (1 - (k : ℝ))) * S.card) := by
      gcongr
    _ = c * (S).card *
        ((2 * SchwartzMap.seminorm ℝ k 0
            (𝓕 (f)) / ((k : ℝ) - 1)) *
          R ^ (1 - (k : ℝ))) := by
      ring

theorem exists_bounded_coefficientOne_shift_of_schwartz_logShift
    (f : SchwartzMap ℝ ℂ) (S : Finset ℕ) (k : ℕ) (c a V t R : ℝ)
    (hS : ∀ n ∈ S, 0 < n) (hc : 0 < c) (hV : 0 < V)
    (hk : 1 < k) (hR : 0 < R)
    (hlarge : V ≤ ‖(c : ℂ) * ∑ n ∈ S,
      f (Real.log n-a) * (n : ℂ)^(-(t : ℂ)*I)‖)
    (htailNumeric :
      c * (S).card *
        ((2 * SchwartzMap.seminorm ℝ k 0
            (𝓕 (f)) / ((k : ℝ) - 1)) *
          R ^ (1 - (k : ℝ))) ≤ V / 2) :
    ∃ ξ ∈ Set.Icc (-R) R,
      V / (4 * c * finiteFourierMass f) ≤
        ‖∑ n ∈ S,
          (n : ℂ) ^ (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * I)‖ := by
  let C : ℝ := finiteFourierMass f
  let s : ℝ := c
  let P : ℝ → ℂ := fun ξ =>
    ∑ n ∈ S, (n : ℂ) ^ (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * I)
  let g : ℝ → ℂ := fun ξ =>
    𝓕 f ξ *
      Complex.exp
        (-(((2 * Real.pi * ξ * a : ℝ) : ℂ) * I)) *
      P ξ
  have hs : 0 < s := by dsimp only [s]; positivity
  have hC : 0 < C := finiteFourierMass_pos f
  have hmass : (∫ ξ : ℝ, ‖𝓕 f ξ‖) ≤ C := by
    dsimp only [C,finiteFourierMass]
    linarith
  have hPcontinuous : Continuous P := by
    dsimp only [P]
    apply continuous_finsetSum
    intro n hn
    apply Continuous.const_cpow
    · fun_prop
    · exact Or.inl (by
        exact_mod_cast (Nat.ne_of_gt
          (hS n hn)))
  have hPbound : ∀ ξ : ℝ, ‖P ξ‖ ≤ S.card := by
    intro ξ
    calc
      ‖P ξ‖ ≤ ∑ n ∈ S,
          ‖(n : ℂ) ^ (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * I)‖ :=
        norm_sum_le _ _
      _ = ∑ _n ∈ S, 1 := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [Complex.norm_natCast_cpow_of_pos
          (hS n hn)]
        simp
      _ = S.card := by simp
  have hphaseContinuous : Continuous (fun ξ : ℝ =>
      Complex.exp
        (-(((2 * Real.pi * ξ * a : ℝ) : ℂ) * I))) := by
    fun_prop
  have hphasePContinuous : Continuous (fun ξ : ℝ =>
      Complex.exp
          (-(((2 * Real.pi * ξ * a : ℝ) : ℂ) * I)) *
        P ξ) := hphaseContinuous.mul hPcontinuous
  have hphasePBound : ∀ ξ : ℝ,
      ‖Complex.exp
          (-(((2 * Real.pi * ξ * a : ℝ) : ℂ) * I)) *
        P ξ‖ ≤ S.card := by
    intro ξ
    rw [norm_mul]
    have hphaseNorm :
        ‖Complex.exp
          (-(((2 * Real.pi * ξ * a : ℝ) : ℂ) * I))‖ = 1 := by
      simpa only [ofReal_neg, neg_mul] using
        Complex.norm_exp_ofReal_mul_I
          (-(2 * Real.pi * ξ * a))
    rw [hphaseNorm, one_mul]
    exact hPbound ξ
  have hgInt : MeasureTheory.Integrable g := by
    have hfInt : MeasureTheory.Integrable (fun ξ : ℝ => 𝓕 f ξ) :=
      (𝓕 f).integrable
    have h := hfInt.mul_bdd (c := S.card)
      hphasePContinuous.aestronglyMeasurable
      (by
        filter_upwards with ξ
        exact hphasePBound ξ)
    simpa only [g, mul_assoc] using h
  rw [fourierDeweightFiniteBlock_logShift_native f S t a hS] at hlarge
  change V ≤ ‖(s : ℂ) * ∫ ξ : ℝ, g ξ‖ at hlarge
  have htail : ‖(s : ℂ) *
      ∫ ξ : ℝ in (Set.Icc (-R) R)ᶜ, g ξ‖ ≤ V / 2 := by
    exact (norm_schwartz_logShift_finite_sum_tail_le
      f S k c a t R hS hc.le hk hR).trans htailNumeric
  have hsplit := MeasureTheory.integral_add_compl
    (f := g) (s := Set.Icc (-R) R) measurableSet_Icc hgInt
  have hcentralLarge : V / 2 ≤
      ‖(s : ℂ) * ∫ ξ : ℝ in Set.Icc (-R) R, g ξ‖ := by
    have htriangle : ‖(s : ℂ) * ∫ ξ : ℝ, g ξ‖ ≤
        ‖(s : ℂ) * ∫ ξ : ℝ in Set.Icc (-R) R, g ξ‖ +
          ‖(s : ℂ) * ∫ ξ : ℝ in (Set.Icc (-R) R)ᶜ, g ξ‖ := by
      rw [← hsplit, mul_add]
      exact norm_add_le _ _
    linarith
  by_contra hexists
  push Not at hexists
  have hthreshold : 0 ≤ V / (4 * s * C) := by positivity
  have hmajorInt : MeasureTheory.Integrable
      (fun ξ : ℝ => ‖𝓕 f ξ‖ * (V / (4 * s * C))) :=
    (𝓕 f).integrable.norm.mul_const _
  have hcentralNorm :
      ‖∫ ξ : ℝ in Set.Icc (-R) R, g ξ‖ ≤
        ∫ ξ : ℝ in Set.Icc (-R) R,
          ‖𝓕 f ξ‖ * (V / (4 * s * C)) := by
    apply MeasureTheory.norm_integral_le_of_norm_le hmajorInt.integrableOn
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc]
      with ξ hξ
    change ‖𝓕 f ξ *
      Complex.exp
        (-(((2 * Real.pi * ξ * a : ℝ) : ℂ) * I)) *
      P ξ‖ ≤ ‖𝓕 f ξ‖ * (V / (4 * s * C))
    rw [norm_mul, norm_mul]
    have hphaseNorm :
        ‖Complex.exp
          (-(((2 * Real.pi * ξ * a : ℝ) : ℂ) * I))‖ = 1 := by
      simpa only [ofReal_neg, neg_mul] using
        Complex.norm_exp_ofReal_mul_I
          (-(2 * Real.pi * ξ * a))
    rw [hphaseNorm, mul_one]
    exact mul_le_mul_of_nonneg_left (hexists ξ hξ).le (norm_nonneg _)
  have hmajorSplit := MeasureTheory.integral_add_compl
    (f := fun ξ : ℝ => ‖𝓕 f ξ‖ * (V / (4 * s * C)))
    (s := Set.Icc (-R) R) measurableSet_Icc hmajorInt
  have hcentralMajor :
      (∫ ξ : ℝ in Set.Icc (-R) R,
        ‖𝓕 f ξ‖ * (V / (4 * s * C))) ≤
      ∫ ξ : ℝ, ‖𝓕 f ξ‖ * (V / (4 * s * C)) := by
    rw [← hmajorSplit]
    exact le_add_of_nonneg_right
      (MeasureTheory.integral_nonneg fun _ =>
        mul_nonneg (norm_nonneg _) hthreshold)
  have hquarter :
      ‖(s : ℂ) * ∫ ξ : ℝ in Set.Icc (-R) R, g ξ‖ ≤ V / 4 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    calc
      s * ‖∫ ξ : ℝ in Set.Icc (-R) R, g ξ‖ ≤
          s * (∫ ξ : ℝ in Set.Icc (-R) R,
            ‖𝓕 f ξ‖ * (V / (4 * s * C))) :=
        mul_le_mul_of_nonneg_left hcentralNorm hs.le
      _ ≤ s * (∫ ξ : ℝ, ‖𝓕 f ξ‖ * (V / (4 * s * C))) :=
        mul_le_mul_of_nonneg_left hcentralMajor hs.le
      _ = s * ((∫ ξ : ℝ, ‖𝓕 f ξ‖) * (V / (4 * s * C))) := by
        rw [MeasureTheory.integral_mul_const]
      _ ≤ s * (C * (V / (4 * s * C))) := by gcongr
      _ = V / 4 := by field_simp
  linarith

end TaoTrudgianYang2025
