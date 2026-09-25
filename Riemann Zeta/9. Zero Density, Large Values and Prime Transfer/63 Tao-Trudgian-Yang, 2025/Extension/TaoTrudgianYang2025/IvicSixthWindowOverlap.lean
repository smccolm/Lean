import TaoTrudgianYang2025.IvicSixthGlobalExcess
import TaoTrudgianYang2025.JutilaReflectionIntegrals

/-! Exact overlap for actual unit-separated real centers, without rounding. -/

noncomputable section
open Finset MeasureTheory Set
namespace TaoTrudgianYang2025

theorem ivicSixth_real_window_count_le (W : Finset ℝ) (hsep : IsOneSeparated W)
    {H : ℝ} (hH : 0 ≤ H) (x : ℝ) :
    ((W.filter fun u => x ∈ Ioc (u-H) (u+H)).card:ℝ) ≤ 2*H+1 := by
  classical
  have hb := oneSeparated_card_cast_le_interval_length_add_one
    (W.filter fun u => x ∈ Ioc (u-H) (u+H))
    (fun u hu v hv huv => hsep u (Finset.mem_filter.mp hu).1
      v (Finset.mem_filter.mp hv).1 huv)
    (a := x-H) (b := x+H) (by linarith)
    (by intro u hu; obtain ⟨_,hl,hr⟩ := Finset.mem_filter.mp hu
        constructor <;> linarith)
  linarith

theorem ivicSixth_sum_real_window_integral_le
    (W : Finset ℝ) (hsep : IsOneSeparated W) (f : ℝ → ℝ) (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    (H a b : ℝ) (hH : 0 ≤ H) (hab : a ≤ b)
    (hrange : ∀ ℓ ∈ W, a ≤ (ℓ : ℝ) ∧ (ℓ : ℝ) ≤ b) :
    (∑ ℓ ∈ W, ∫ x in (ℓ : ℝ)-H..(ℓ : ℝ)+H, f x) ≤
      (2*H+1) * ∫ x in a-H..b+H, f x := by
  classical
  let J := Set.Ioc (a-H) (b+H)
  let window := fun ℓ : ℝ => Set.Ioc ((ℓ : ℝ)-H) ((ℓ : ℝ)+H)
  have hfi (c d : ℝ) : IntegrableOn f (Set.Ioc c d) :=
    hf.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hwi (ℓ : ℝ) : Integrable ((window ℓ).indicator f) :=
    (hfi _ _).integrable_indicator measurableSet_Ioc
  have hJi : Integrable (J.indicator f) :=
    (hfi _ _).integrable_indicator measurableSet_Ioc
  have hsub (ℓ : ℝ) (hℓ : ℓ ∈ W) : window ℓ ⊆ J := by
    intro x hx
    have hr := hrange ℓ hℓ
    change (ℓ : ℝ)-H < x ∧ x ≤ (ℓ : ℝ)+H at hx
    constructor <;> linarith [hx.1, hx.2]
  have hpoint (x : ℝ) :
      (∑ ℓ ∈ W, (window ℓ).indicator f x) ≤
        (2*H+1) * J.indicator f x := by
    by_cases hx : x ∈ J
    · rw [Set.indicator_of_mem hx]
      have heq : (∑ ℓ ∈ W, (window ℓ).indicator f x) =
          ((W.filter fun ℓ => x ∈ window ℓ).card : ℝ) * f x := by
        calc
          _ = ∑ ℓ ∈ W.filter (fun ℓ => x ∈ window ℓ), f x := by
            rw [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro ℓ hℓ
            by_cases hw : x ∈ window ℓ <;> simp [hw]
          _ = _ := by simp
      rw [heq]
      apply mul_le_mul_of_nonneg_right _ (hf0 x)
      exact ivicSixth_real_window_count_le W hsep hH x
    · rw [Set.indicator_of_notMem hx]
      have hz : ∀ ℓ ∈ W, (window ℓ).indicator f x = 0 := by
        intro ℓ hℓ
        apply Set.indicator_of_notMem
        intro hw
        exact hx (hsub ℓ hℓ hw)
      simp only [Finset.sum_eq_zero hz, mul_zero, le_refl]
  have hleft :
      (∑ ℓ ∈ W, ∫ x in (ℓ : ℝ)-H..(ℓ : ℝ)+H, f x) =
        ∫ x, ∑ ℓ ∈ W, (window ℓ).indicator f x := by
    rw [MeasureTheory.integral_finsetSum W (fun ℓ _ => hwi ℓ)]
    apply Finset.sum_congr rfl
    intro ℓ hℓ
    rw [intervalIntegral.integral_of_le (by linarith),
      MeasureTheory.integral_indicator measurableSet_Ioc]
  rw [hleft]
  calc
    _ ≤ ∫ x, (2*H+1) * J.indicator f x :=
      MeasureTheory.integral_mono
        (integrable_finsetSum W (fun ℓ _ => hwi ℓ)) (hJi.const_mul _) hpoint
    _ = _ := by
      rw [MeasureTheory.integral_const_mul,
        MeasureTheory.integral_indicator measurableSet_Ioc,
        intervalIntegral.integral_of_le (by linarith)]

theorem ivicSixth_sum_real_window_sixth_le (W : Finset ℝ) (hsep : IsOneSeparated W)
    (f : ℝ → ℝ) (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    {H a b : ℝ} (hH : 0 ≤ H) (hab : a ≤ b)
    (hrange : ∀ u ∈ W, a ≤ u ∧ u ≤ b) :
    (∑ v ∈ W, (∫ u in -H..H, f (v+u))^6) ≤
      (2*H)^5*(2*H+1)*(∫ u in a-H..b+H, f u^6) := by
  have hpoint (v : ℝ) :
      (∫ u in -H..H, f (v+u))^6 ≤
        (2*H)^5*(∫ u in v-H..v+H, f u^6) := by
    have hh := jutila_intervalIntegral_pow_le (fun u => f (v+u)) H hH
      (by norm_num : 0 < (6:ℕ)) (hf.comp (continuous_const.add continuous_id))
      (fun u => hf0 (v+u))
    have he : (∫ u in -H..H, f (v+u)^6) = ∫ u in v-H..v+H, f u^6 := by
      convert intervalIntegral.integral_comp_add_left (fun u => f u^6) v using 1
    simpa only [Nat.reduceSub,he] using hh
  calc
    _ ≤ ∑ v ∈ W, (2*H)^5*(∫ u in v-H..v+H, f u^6) :=
      Finset.sum_le_sum (fun v _ => hpoint v)
    _ = (2*H)^5*(∑ v ∈ W, ∫ u in v-H..v+H, f u^6) :=
      (Finset.mul_sum ..).symm
    _ ≤ (2*H)^5*((2*H+1)*(∫ u in a-H..b+H, f u^6)) :=
      mul_le_mul_of_nonneg_left
        (ivicSixth_sum_real_window_integral_le W hsep (fun u => f u^6)
          (hf.pow 6) (fun u => pow_nonneg (hf0 u) _) H a b hH hab hrange)
        (pow_nonneg (by positivity) _)
    _ = _ := by ring

end TaoTrudgianYang2025
