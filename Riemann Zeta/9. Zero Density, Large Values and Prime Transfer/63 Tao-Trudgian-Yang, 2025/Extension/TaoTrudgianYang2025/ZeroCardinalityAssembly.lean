import TaoTrudgianYang2025.ZeroCardinalityRestrictions

/-!
# Symmetric multiplicity-weighted zero-count assembly

Positive and reflected negative slabs and the finite low-height rectangle
are counted using every actual signed dyadic color.
-/

noncomputable section
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem paperZeroCount_le_dyadicSlabCount
    (σ T H M : ℝ) (hH : 1 ≤ H) (hM : 0 ≤ M)
    (hlow : (paperZeroCount σ H : ℝ) ≤ M)
    (hslab : ∀ U : ℝ, H ≤ U → U ≤ T → (zeroCountRect σ 1 U (2 * U) : ℝ) ≤ M) :
    (paperZeroCount σ T : ℝ) ≤
      (Fintype.card (ZeroDyadicColor T) : ℝ) * M := by
  classical
  obtain ⟨color, hcolor⟩ := exists_zeroDyadicColor σ T H hH
  let W : ZeroCopy σ T → ℝ := fun z => (z.1 : ℂ).im
  have hclass (c : ZeroDyadicColor T) : (Fintype.card (EnergyColorFiber color c) : ℝ) ≤ M := by
    have hspec (x : EnergyColorFiber color c) :
        ZeroDyadicColorCondition H T (W x.1) c := by
      simpa only [x.2] using hcolor x.1
    cases isEmpty_or_nonempty (EnergyColorFiber color c) with
    | inl hempty =>
      have he : Fintype.card (EnergyColorFiber color c) = 0 := Fintype.card_of_isEmpty
      simpa only [he, Nat.cast_zero] using hM
    | inr hnonempty =>
      let x₀ := Classical.choice hnonempty
      have hz := (mem_paperZeros_iff (x₀.1.1 : ℂ)).mp x₀.1.1.2
      rcases Option.eq_none_or_eq_some c with hlabel | ⟨pair, hlabel⟩
      ·
        have hlowclass := zeroCopy_family_card_le_low_height σ T H
          (fun x : EnergyColorFiber color c => x.1) Subtype.val_injective (by
            intro x
            simpa only [hlabel, ZeroDyadicColorCondition] using hspec x)
        exact (show (Fintype.card (EnergyColorFiber color c) : ℝ) ≤
          paperZeroCount σ H by exact_mod_cast hlowclass).trans hlow
      ·
        obtain ⟨negative, n⟩ := pair
        let U := H * (2 : ℝ) ^ (n : ℕ)
        have hspec' (x : EnergyColorFiber color c) :
            H ≤ U ∧ U ≤ (if negative then -W x.1 else W x.1) ∧
              (if negative then -W x.1 else W x.1) ≤ 2 * U := by
          simpa only [hlabel, ZeroDyadicColorCondition] using hspec x
        have hUT : U ≤ T := by
          have h := (hspec' x₀).2.1
          cases negative <;> simp only [Bool.false_eq_true, ↓reduceIte] at h
          · exact (h.trans (le_abs_self _)).trans hz.2.2.1
          · exact (h.trans (neg_le_abs _)).trans hz.2.2.1
        have hbound := hslab U (hspec' x₀).1 hUT
        have hclassSlab : Fintype.card (EnergyColorFiber color c) ≤
            zeroCountRect σ 1 U (2 * U) := by
          cases negative
          · apply zeroCopy_family_card_le_classicalSlab σ T U
              (fun x : EnergyColorFiber color c => x.1) Subtype.val_injective
            intro x
            exact (hspec' x).2
          · apply zeroCopy_family_card_le_classicalSlab_of_neg σ T U
              (fun x : EnergyColorFiber color c => x.1) Subtype.val_injective
            intro x
            exact (hspec' x).2
        exact (show (Fintype.card (EnergyColorFiber color c) : ℝ) ≤
          zeroCountRect σ 1 U (2 * U) by exact_mod_cast hclassSlab).trans hbound
  rw [← zeroCopy_card]
  exact cardinality_le_color_count_mul color M hclass


theorem eventually_zeroDyadicColor_card_le_rpow
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ T : ℝ in Filter.atTop,
      (Fintype.card (ZeroDyadicColor T) : ℝ) ≤ T ^ η := by
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsmall := eventually_one_add_const_mul_log_le_rpow
    (3 + 2 / Real.log 2) η (by linarith)
  filter_upwards [hsmall, Filter.eventually_ge_atTop (8 : ℝ)] with
    T hsmall hT
  have hTpos : 0 < T := by linarith
  have hlogone : 1 ≤ Real.log T := by
    have he : Real.exp 1 ≤ T := Real.exp_one_lt_three.le.trans (by linarith)
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) he
  have hlogb : 0 ≤ Real.logb 2 T := Real.logb_nonneg (by norm_num) (by linarith)
  have hfloor := Nat.floor_le hlogb
  have hcard : (Fintype.card (ZeroDyadicColor T) : ℝ) ≤ T ^ η := by
    simp only [ZeroDyadicColor, Fintype.card_option, Fintype.card_prod,
      Fintype.card_bool, Fintype.card_fin, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one]
    simp only [Real.logb] at hfloor ⊢
    rw [show (3 + 2 / Real.log 2) * Real.log T =
      3 * Real.log T + 2 * (Real.log T / Real.log 2) by ring] at hsmall
    nlinarith
  exact hcard


theorem paperZeroCount_bound_of_eventual_slab_bound
    (σ q C : ℝ) (hq : 0 ≤ q)
    (hslab : ∀ᶠ T : ℝ in Filter.atTop,
      (zeroCountRect σ 1 T (2 * T) : ℝ) ≤ C * T ^ q) :
    ∀ η : ℝ, 0 < η → ∃ K : ℝ, 1 ≤ K ∧ ∀ᶠ T : ℝ in Filter.atTop,
      (paperZeroCount σ T : ℝ) ≤ K * T ^ (q + η) := by
  intro η hη
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp hslab
  let H := max 1 T₀
  let K : ℝ := max 1 (max C (paperZeroCount σ H : ℝ))
  have hK : 1 ≤ K := le_max_left _ _
  have hKC : C ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hKE : (paperZeroCount σ H : ℝ) ≤ K :=
    (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨K, hK, ?_⟩
  filter_upwards [eventually_zeroDyadicColor_card_le_rpow η hη,
    Filter.eventually_ge_atTop (1 : ℝ)] with T hcolors hT
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hTq : 1 ≤ T ^ q := Real.one_le_rpow hT hq
  have hbound := paperZeroCount_le_dyadicSlabCount σ T H (K * T ^ q)
    (le_max_left _ _) (by positivity)
    (hKE.trans (le_mul_of_one_le_right hKpos.le hTq)) (by
      intro U hHU hUT
      have hUpos : 0 < U := (zero_lt_one.trans_le (le_max_left _ _)).trans_le hHU
      exact (hT₀ U ((le_max_right _ _).trans hHU)).trans
        (mul_le_mul hKC (Real.rpow_le_rpow hUpos.le hUT hq)
          (Real.rpow_nonneg hUpos.le _) hKpos.le))
  calc
    (paperZeroCount σ T : ℝ) ≤
        (Fintype.card (ZeroDyadicColor T) : ℝ) * (K * T ^ q) := hbound
    _ ≤ T ^ η * (K * T ^ q) :=
      mul_le_mul_of_nonneg_right hcolors (by positivity)
    _ = K * T ^ (q + η) := by rw [Real.rpow_add hTpos]; ring


end TaoTrudgianYang2025
