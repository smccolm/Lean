import GafniTao.FordCubicExponent
import Mathlib.Analysis.SumIntegralComparisons

/-!
# Sum--integral comparison across a unimodal turning point

The single unit cell containing the turning point is the delicate part of
Ford's estimate.  The integral controls the smaller endpoint and the value at
the turning point controls the larger endpoint.
-/

open Set MeasureTheory

namespace GafniTao

noncomputable section

theorem unimodal_crossing_pair_le_peak_add_integral
    {f : ℝ → ℝ} {a c b : ℝ}
    (hab : a ≤ c) (hcb : c ≤ b) (hlen : b - a = 1)
    (hcont : Continuous f)
    (hmono : MonotoneOn f (Set.Icc a c))
    (hanti : AntitoneOn f (Set.Icc c b)) :
    f a + f b ≤ f c + ∫ x in a..b, f x := by
  have hfi : IntervalIntegrable f volume a b :=
    hcont.intervalIntegrable a b
  have hconstA : IntervalIntegrable (fun _x : ℝ => f a) volume a b :=
    intervalIntegrable_const
  have hconstB : IntervalIntegrable (fun _x : ℝ => f b) volume a b :=
    intervalIntegrable_const
  have hPeakA : f a ≤ f c :=
    hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  have hPeakB : f b ≤ f c :=
    hanti ⟨le_rfl, hcb⟩ ⟨hcb, le_rfl⟩ hcb
  by_cases hAB : f a ≤ f b
  · have hpoint : ∀ x ∈ Set.Icc a b, f a ≤ f x := by
      intro x hx
      rcases le_total x c with hxc | hcx
      · exact hmono ⟨le_rfl, hab⟩ ⟨hx.1, hxc⟩ hx.1
      · exact hAB.trans (hanti ⟨hcx, hx.2⟩ ⟨hcb, le_rfl⟩ hx.2)
    have hInt := intervalIntegral.integral_mono_on
      (hab.trans hcb) hconstA hfi hpoint
    rw [intervalIntegral.integral_const, hlen] at hInt
    simp only [one_smul] at hInt
    linarith
  · have hBA : f b ≤ f a := le_of_not_ge hAB
    have hpoint : ∀ x ∈ Set.Icc a b, f b ≤ f x := by
      intro x hx
      rcases le_total x c with hxc | hcx
      · exact hBA.trans (hmono ⟨le_rfl, hab⟩ ⟨hx.1, hxc⟩ hx.1)
      · exact hanti ⟨hcx, hx.2⟩ ⟨hcb, le_rfl⟩ hx.2
    have hInt := intervalIntegral.integral_mono_on
      (hab.trans hcb) hconstB hfi hpoint
    rw [intervalIntegral.integral_const, hlen] at hInt
    simp only [one_smul] at hInt
    linarith

/-- A nonnegative continuous unimodal function satisfies the exact comparison
used by Ford: the sampled sum is at most one continuous peak plus the
integral. -/
theorem sum_range_le_peak_add_integral_of_unimodal
    {f : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hcont : Continuous f) (hnonneg : ∀ x, 0 ≤ f x)
    (hmono : MonotoneOn f (Set.Icc 0 c))
    (hanti : AntitoneOn f (Set.Ici c)) (r : ℕ) :
    (∑ j ∈ Finset.range r, f j) ≤
      f c + ∫ x in (0 : ℝ)..r, f x := by
  let k : ℕ := ⌊c⌋₊
  have hkc : (k : ℝ) ≤ c := by
    exact Nat.floor_le hc
  have hck : c < (k : ℝ) + 1 := by
    exact Nat.lt_floor_add_one c
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hfInt (a b : ℝ) : IntervalIntegrable f volume a b :=
    hcont.intervalIntegrable a b
  by_cases hrk : r ≤ k
  · have hkr : (r : ℝ) ≤ c := by
      exact (by exact_mod_cast hrk : (r : ℝ) ≤ k).trans hkc
    have hmonoR : MonotoneOn f (Set.Icc (0 : ℝ) r) :=
      hmono.mono (Set.Icc_subset_Icc_right hkr)
    have hmonoR' : MonotoneOn f (Set.Icc (0 : ℝ) (0 + (r : ℝ))) := by
      simpa only [zero_add] using hmonoR
    have hsum := hmonoR'.sum_le_integral
    simp only [zero_add] at hsum
    linarith [hnonneg c]
  · have hkr : k < r := Nat.lt_of_not_ge hrk
    by_cases hrOne : r = k + 1
    · subst r
      have hmonoK : MonotoneOn f (Set.Icc (0 : ℝ) k) :=
        hmono.mono (Set.Icc_subset_Icc_right hkc)
      have hmonoK' : MonotoneOn f (Set.Icc (0 : ℝ) (0 + (k : ℝ))) := by
        simpa only [zero_add] using hmonoK
      have hleft := hmonoK'.sum_le_integral
      simp only [zero_add] at hleft
      have hpeak : f (k : ℝ) ≤ f c :=
        hmono ⟨by positivity, hkc⟩ ⟨hc, le_rfl⟩ hkc
      have hlast : 0 ≤ ∫ x in (k : ℝ)..(k + 1 : ℕ), f x :=
        intervalIntegral.integral_nonneg (by norm_num) (fun x _hx => hnonneg x)
      have hadd := intervalIntegral.integral_add_adjacent_intervals
        (hfInt 0 k) (hfInt k (k + 1 : ℕ))
      rw [Finset.sum_range_succ]
      norm_num [Nat.cast_add, Nat.cast_one] at hlast hadd ⊢
      linarith
    · have hTwo : k + 2 ≤ r := by omega
      let d : ℕ := r - (k + 2)
      have hrEq : r = k + 2 + d := by
        dsimp only [d]
        omega
      have hmonoK : MonotoneOn f (Set.Icc (0 : ℝ) k) :=
        hmono.mono (Set.Icc_subset_Icc_right hkc)
      have hmonoK' : MonotoneOn f (Set.Icc (0 : ℝ) (0 + (k : ℝ))) := by
        simpa only [zero_add] using hmonoK
      have hleft := hmonoK'.sum_le_integral
      simp only [zero_add] at hleft
      have hCrossMono : MonotoneOn f (Set.Icc (k : ℝ) c) := by
        apply hmono.mono
        exact Set.Icc_subset_Icc_left (by positivity)
      have hCrossAnti : AntitoneOn f (Set.Icc c (k + 1 : ℕ)) := by
        apply hanti.mono
        intro x hx
        exact hx.1
      have hcross :
          f (k : ℝ) + f (k + 1 : ℕ) ≤
            f c + ∫ x in (k : ℝ)..(k + 1 : ℕ), f x := by
        apply unimodal_crossing_pair_le_peak_add_integral
          (f := f) (a := (k : ℝ)) (c := c)
          (b := ((k + 1 : ℕ) : ℝ)) hkc
          (by exact_mod_cast hck.le)
        · norm_num [Nat.cast_add, Nat.cast_one]
        · exact hcont
        · exact hCrossMono
        · exact hCrossAnti
      have hAntiTail :
          AntitoneOn f (Set.Icc ((k + 1 : ℕ) : ℝ) r) := by
        apply hanti.mono
        intro x hx
        have hck' : c ≤ ((k + 1 : ℕ) : ℝ) := by
          exact_mod_cast hck.le
        exact hck'.trans hx.1
      have hUpper :
          ((k + 1 : ℕ) : ℝ) + (d + 1 : ℕ) = (r : ℝ) := by
        exact_mod_cast (show k + 1 + (d + 1) = r by omega)
      have hAntiTail' : AntitoneOn f
          (Set.Icc (((k + 1 : ℕ) : ℝ))
            (((k + 1 : ℕ) : ℝ) + (d + 1 : ℕ))) := by
        rw [hUpper]
        exact hAntiTail
      have htailFull := hAntiTail'.sum_le_integral
      rw [hUpper] at htailFull
      have htailDesired :
          (∑ i ∈ Finset.range d, f ((k + 2 + i : ℕ) : ℝ)) ≤
            ∑ i ∈ Finset.range (d + 1),
              f (((k + 1 : ℕ) : ℝ) + (i + 1 : ℕ)) := by
        rw [Finset.sum_range_succ]
        have hEq : ∀ i : ℕ,
            (((k + 1 : ℕ) : ℝ) + (i + 1 : ℕ)) =
              ((k + 2 + i : ℕ) : ℝ) := by
          intro i
          push_cast
          ring
        simp_rw [hEq]
        exact le_add_of_nonneg_right (hnonneg ((k + 2 + d : ℕ) : ℝ))
      have htail :
          (∑ i ∈ Finset.range d, f ((k + 2 + i : ℕ) : ℝ)) ≤
            ∫ x in ((k + 1 : ℕ) : ℝ)..r, f x :=
        htailDesired.trans htailFull
      have hadd₁ := intervalIntegral.integral_add_adjacent_intervals
        (hfInt 0 k) (hfInt k (k + 1 : ℕ))
      have hadd₂ := intervalIntegral.integral_add_adjacent_intervals
        (hfInt 0 (k + 1 : ℕ)) (hfInt (k + 1 : ℕ) r)
      have hSumSplit :
          (∑ j ∈ Finset.range r, f j) =
            (∑ j ∈ Finset.range k, f j) + f k + f (k + 1) +
              ∑ i ∈ Finset.range d, f (k + 2 + i) := by
        conv_lhs =>
          rw [hrEq, Finset.sum_range_add, Finset.sum_range_succ,
            Finset.sum_range_succ]
        norm_num [Nat.cast_add]
      rw [hSumSplit]
      norm_num [Nat.cast_add, Nat.cast_one] at hleft hcross htail hadd₁ hadd₂ ⊢
      linarith

#print axioms unimodal_crossing_pair_le_peak_add_integral
#print axioms sum_range_le_peak_add_integral_of_unimodal

end

end GafniTao
