import GafniTao.HeathBrownShiftRange

/-!
# Real-valued form of the elementary spacing bound

The exact finite spacing theorem contains a natural floor and an integer
floor/ceiling interval.  This file removes those artifacts with explicit
constants.  It is the quantitative version used in the harmonic shift sum.
-/

open Finset

namespace GafniTao

noncomputable section

theorem int_Icc_floor_ceil_card_cast_le
    {a b : ℝ} (hab : a ≤ b) :
    ((Finset.Icc ⌊a⌋ ⌈b⌉).card : ℝ) ≤ b - a + 3 := by
  have hfloorCeil : ⌊a⌋ ≤ ⌈b⌉ := by
    have hreal : (⌊a⌋ : ℝ) ≤ (⌈b⌉ : ℝ) :=
      (Int.floor_le a).trans (hab.trans (Int.le_ceil b))
    exact_mod_cast hreal
  have hcardInt : ((Finset.Icc ⌊a⌋ ⌈b⌉).card : ℤ) =
      ⌈b⌉ + 1 - ⌊a⌋ := by
    exact Int.card_Icc_of_le (a := ⌊a⌋) (b := ⌈b⌉)
      (by omega)
  have hcardReal : ((Finset.Icc ⌊a⌋ ⌈b⌉).card : ℝ) =
      (⌈b⌉ : ℝ) + 1 - (⌊a⌋ : ℝ) := by
    exact_mod_cast hcardInt
  rw [hcardReal]
  have hceil : (⌈b⌉ : ℝ) ≤ b + 1 := (Int.ceil_lt_add_one b).le
  have hfloor : a - 1 ≤ (⌊a⌋ : ℝ) := (Int.sub_one_lt_floor a).le
  linarith

theorem heathBrown_spacing_card_cast_le
    {N : ℕ} {g : ℝ → ℝ} {mu theta M : ℝ}
    (hN : 1 ≤ N) (hmu : 0 < mu) (htheta : 0 ≤ theta) (hM : 0 ≤ M)
    (hg : ContinuousOn g (Set.Icc 0 (N : ℝ)))
    (hgd : DifferentiableOn ℝ g (Set.Ioo 0 (N : ℝ)))
    (hderivLower : ∀ x ∈ Set.Ioo (0 : ℝ) (N : ℝ), mu ≤ deriv g x)
    (hderivUpper : ∀ x ∈ Set.Ioo (0 : ℝ) (N : ℝ), deriv g x ≤ M) :
    ((heathBrownSpacingSet N g theta).card : ℝ) ≤
      (2 * theta / mu + 1) * (M * N + 2 * theta + 3) := by
  let z : ℝ := 2 * theta / mu
  let lo : ℝ := g 1 - theta
  let hi : ℝ := g N + theta
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hOneI : (1 : ℝ) ∈ Set.Icc (0 : ℝ) N := by
    exact ⟨by norm_num, by exact_mod_cast hN⟩
  have hNI : (N : ℝ) ∈ Set.Icc (0 : ℝ) N :=
    ⟨by positivity, le_rfl⟩
  have hmono : g 1 ≤ g N := by
    have hslope := heathBrown_lower_slope hg hgd hderivLower hOneI hNI
      (by exact_mod_cast hN)
    have hNge : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hnonneg : 0 ≤ mu * ((N : ℝ) - 1) :=
      mul_nonneg hmu.le (sub_nonneg.mpr hNge)
    linarith
  have hlohi : lo ≤ hi := by dsimp [lo, hi]; linarith
  have hinterval := int_Icc_floor_ceil_card_cast_le hlohi
  have hspread := heathBrown_upper_slope hg hgd hderivUpper hOneI hNI
    (by exact_mod_cast hN)
  have hNminus : (N : ℝ) - 1 ≤ N := by linarith
  have hspread' : g N - g 1 ≤ M * N :=
    hspread.trans (mul_le_mul_of_nonneg_left hNminus hM)
  have hinterval' : ((Finset.Icc ⌊lo⌋ ⌈hi⌉).card : ℝ) ≤
      M * N + 2 * theta + 3 := by
    apply hinterval.trans
    dsimp [lo, hi]
    linarith
  have hfloor : ((⌊max 0 z⌋₊ + 1 : ℕ) : ℝ) ≤ z + 1 := by
    push_cast
    rw [max_eq_right hz]
    simpa only [add_comm] using add_le_add_right (Nat.floor_le hz) 1
  have hexact := heathBrown_spacing_card_le_exact (theta := theta)
    hN hmu hg hgd hderivLower
  have hcast : ((heathBrownSpacingSet N g theta).card : ℝ) ≤
      ((⌊max 0 z⌋₊ + 1 : ℕ) : ℝ) *
        ((Finset.Icc ⌊lo⌋ ⌈hi⌉).card : ℝ) := by
    exact_mod_cast hexact
  calc
    ((heathBrownSpacingSet N g theta).card : ℝ) ≤
        ((⌊max 0 z⌋₊ + 1 : ℕ) : ℝ) *
          ((Finset.Icc ⌊lo⌋ ⌈hi⌉).card : ℝ) := hcast
    _ ≤ (z + 1) * (M * N + 2 * theta + 3) := by
      exact mul_le_mul hfloor hinterval' (by positivity)
        (by linarith [hz])
    _ = (2 * theta / mu + 1) * (M * N + 2 * theta + 3) := by
      dsimp [z]

#print axioms int_Icc_floor_ceil_card_cast_le
#print axioms heathBrown_spacing_card_cast_le

end

end GafniTao
