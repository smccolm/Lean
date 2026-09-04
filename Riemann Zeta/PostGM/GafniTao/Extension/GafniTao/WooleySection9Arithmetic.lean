import GafniTao.WooleyIterationArithmetic

/-!
# Arithmetic of Wooley's two-step monograde extraction

This file formalizes the scale and weight ledger in equations (9.7)--(9.9).
The indices below are precisely the two indices selected by the two
applications of Lemma 9.2 in the proof of Lemma 9.3.
-/

namespace GafniTao

noncomputable section

def wooleyTwoStepA (k r₁ b : ℕ) : ℕ := wooleyNextB k r₁ b

def wooleyTwoStepB (k r₁ r₂ b : ℕ) : ℕ :=
  wooleyNextB k r₂ (wooleyTwoStepA k r₁ b)

def wooleyTwoStepR (k r₂ : ℕ) : ℕ := k - r₂

def wooleyTwoStepWeight (k r₁ r₂ : ℕ) : ℝ :=
  wooleyRho k r₁ * wooleyRho k r₂

theorem wooley_nextB_pos
    {k r b : ℕ} (hr : 1 ≤ r) (hb : 1 ≤ b) :
    0 < wooleyNextB k r b := by
  have hlower := wooley_nextB_lower (k := k) (r := r) (b := b) hr
  have hleft : 0 < (k - r + 1) * b := by positivity
  have hprod : 0 < r * wooleyNextB k r b := lt_of_lt_of_le hleft hlower
  by_contra hnext
  have hzero : wooleyNextB k r b = 0 := Nat.eq_zero_of_not_pos hnext
  simp [hzero] at hprod

theorem wooley_nextB_ge_divisor_scale
    {k r b : ℕ} (hr : 1 ≤ r) (hrk : r ≤ k) :
    b ≤ k * wooleyNextB k r b := by
  have hlower := wooley_nextB_lower (k := k) (r := r) (b := b) hr
  have hcoef : r ≤ k := hrk
  have hleft : b ≤ (k - r + 1) * b := by
    exact Nat.le_mul_of_pos_left b (by omega)
  exact hleft.trans (hlower.trans (Nat.mul_le_mul_right _ hcoef))

theorem wooley_twoStep_indices
    {k r₁ r₂ : ℕ} (hr₁ : 1 ≤ r₁) (hr₁k : r₁ < k)
    (hr₂ : 1 ≤ r₂) (hr₂k : r₂ ≤ k - r₁) :
    1 ≤ wooleyTwoStepR k r₂ ∧
      wooleyTwoStepR k r₂ ≤ k - 1 := by
  unfold wooleyTwoStepR
  constructor <;> omega

theorem wooley_twoStep_upper
    {k r₁ r₂ b : ℕ} (hr₁ : 1 ≤ r₁) (hr₁k : r₁ < k)
    (hr₂ : 1 ≤ r₂) (hr₂k : r₂ ≤ k - r₁) :
    wooleyTwoStepB k r₁ r₂ b ≤ k ^ 2 * b := by
  unfold wooleyTwoStepB wooleyTwoStepA
  calc
    wooleyNextB k r₂ (wooleyNextB k r₁ b) ≤
        k * wooleyNextB k r₁ b :=
      wooley_nextB_le_k_mul hr₂ (hr₂k.trans (Nat.sub_le _ _))
    _ ≤ k * (k * b) := Nat.mul_le_mul_left k
      (wooley_nextB_le_k_mul hr₁ hr₁k.le)
    _ = k ^ 2 * b := by ring

/-- The non-strict version of the scale growth asserted in (9.9). -/
theorem wooley_twoStep_growth
    {k r₁ r₂ b : ℕ} (hk : 2 ≤ k)
    (hr₁ : 1 ≤ r₁) (hr₁k : r₁ < k)
    (hr₂ : 1 ≤ r₂) (hr₂k : r₂ ≤ k - r₁) :
    (1 + 2 / (k : ℝ)) * (b : ℝ) ≤
      (wooleyTwoStepB k r₁ r₂ b : ℝ) := by
  let a' := wooleyTwoStepA k r₁ b
  let b' := wooleyTwoStepB k r₁ r₂ b
  have h₁Nat : (k - r₁ + 1) * b ≤ r₁ * a' := by
    exact wooley_nextB_lower hr₁
  have h₂Nat : (k - r₂ + 1) * a' ≤ r₂ * b' := by
    exact wooley_nextB_lower hr₂
  have h₁ : ((k - r₁ + 1) * b : ℕ) ≤ r₁ * a' := h₁Nat
  have h₂ : ((k - r₂ + 1) * a' : ℕ) ≤ r₂ * b' := h₂Nat
  have hr₁pos : (0 : ℝ) < r₁ := by exact_mod_cast (show 0 < r₁ by omega)
  have hr₂pos : (0 : ℝ) < r₂ := by exact_mod_cast (show 0 < r₂ by omega)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hcast₁ : (k - r₁ + 1 : ℕ) = k - r₁ + 1 := rfl
  have hkr₁ : r₁ ≤ k := hr₁k.le
  have hkr₂ : r₂ ≤ k := hr₂k.trans (Nat.sub_le _ _)
  have h₁R : ((k : ℝ) - r₁ + 1) * b ≤ (r₁ : ℝ) * a' := by
    exact_mod_cast h₁Nat
  have h₂R : ((k : ℝ) - r₂ + 1) * a' ≤ (r₂ : ℝ) * b' := by
    exact_mod_cast h₂Nat
  have hs₁ : (r₁ : ℝ) + r₂ ≤ k := by exact_mod_cast (by omega : r₁ + r₂ ≤ k)
  have hfac₁ : (r₂ : ℝ) + 1 ≤ (k : ℝ) - r₁ + 1 := by linarith
  have hfac₂ : (r₁ : ℝ) + 1 ≤ (k : ℝ) - r₂ + 1 := by linarith
  have hbnonneg : (0 : ℝ) ≤ b := by positivity
  have hanonneg : (0 : ℝ) ≤ a' := by positivity
  have hb'nonneg : (0 : ℝ) ≤ b' := by positivity
  have hprod :
      ((r₁ : ℝ) + 1) * ((r₂ : ℝ) + 1) * b ≤
        (r₁ : ℝ) * (r₂ : ℝ) * b' := by
    have hfirst : ((r₂ : ℝ) + 1) * b ≤ (r₁ : ℝ) * a' :=
      le_trans (mul_le_mul_of_nonneg_right hfac₁ hbnonneg) h₁R
    have hsecond : ((r₁ : ℝ) + 1) * a' ≤ (r₂ : ℝ) * b' :=
      le_trans (mul_le_mul_of_nonneg_right hfac₂ hanonneg) h₂R
    calc
      ((r₁ : ℝ) + 1) * ((r₂ : ℝ) + 1) * b =
          ((r₁ : ℝ) + 1) * (((r₂ : ℝ) + 1) * b) := by ring
      _ ≤ ((r₁ : ℝ) + 1) * ((r₁ : ℝ) * a') :=
        mul_le_mul_of_nonneg_left hfirst (by positivity)
      _ ≤ ((r₁ : ℝ) + 1) * ((r₁ : ℝ) *
          ((r₂ : ℝ) * b' / ((r₁ : ℝ) + 1))) := by
        have haBound : a' ≤ (r₂ : ℝ) * b' / ((r₁ : ℝ) + 1) :=
          (le_div_iff₀ (by positivity)).mpr (by simpa [mul_comm] using hsecond)
        gcongr
      _ = (r₁ : ℝ) * (r₂ : ℝ) * b' := by
        field_simp
  have hcoef :
      ((k : ℝ) + 2) * (r₁ : ℝ) * (r₂ : ℝ) ≤
        (k : ℝ) * ((r₁ : ℝ) + 1) * ((r₂ : ℝ) + 1) := by
    have hr₁le : (r₁ : ℝ) ≤ k := by exact_mod_cast hkr₁
    have hr₂le : (r₂ : ℝ) ≤ k := by exact_mod_cast hkr₂
    nlinarith [mul_nonneg (sub_nonneg.mpr hr₁le) (by positivity : (0 : ℝ) ≤ r₂),
      mul_nonneg (sub_nonneg.mpr hr₂le) (by positivity : (0 : ℝ) ≤ r₁)]
  have hmul :
      ((k : ℝ) + 2) * ((r₁ : ℝ) * (r₂ : ℝ)) * b ≤
        (k : ℝ) * ((r₁ : ℝ) * (r₂ : ℝ)) * b' := by
    calc
      ((k : ℝ) + 2) * ((r₁ : ℝ) * (r₂ : ℝ)) * b =
          (((k : ℝ) + 2) * r₁ * r₂) * b := by ring
      _ ≤ ((k : ℝ) * (r₁ + 1) * (r₂ + 1)) * b :=
        mul_le_mul_of_nonneg_right hcoef hbnonneg
      _ ≤ (k : ℝ) * ((r₁ : ℝ) * (r₂ : ℝ) * b') := by
        simpa [mul_assoc] using mul_le_mul_of_nonneg_left hprod hkpos.le
      _ = (k : ℝ) * ((r₁ : ℝ) * (r₂ : ℝ)) * b' := by ring
  have hcancel :
      ((k : ℝ) + 2) * (b : ℝ) ≤ (k : ℝ) * (b' : ℝ) := by
    have hrr : (0 : ℝ) < (r₁ : ℝ) * (r₂ : ℝ) := by positivity
    rw [show ((k : ℝ) + 2) * (r₁ * r₂) * b =
          (r₁ * r₂) * (((k : ℝ) + 2) * b) by ring,
        show (k : ℝ) * (r₁ * r₂) * b' =
          (r₁ * r₂) * ((k : ℝ) * b') by ring] at hmul
    nlinarith [hmul]
  rw [show (1 + 2 / (k : ℝ)) = ((k : ℝ) + 2) / k by
    field_simp]
  rw [div_mul_eq_mul_div, div_le_iff₀ hkpos]
  simpa [mul_comm] using hcancel

theorem wooley_twoStep_defining_ceiling
    {k r₁ r₂ b : ℕ} (hr₂k : r₂ ≤ k) :
    wooleyTwoStepB k r₁ r₂ b =
      ((wooleyTwoStepR k r₂ + 1) * wooleyTwoStepA k r₁ b) ⌈/⌉
        (k - wooleyTwoStepR k r₂) := by
  unfold wooleyTwoStepB wooleyTwoStepR wooleyNextB
  rw [Nat.sub_sub_self hr₂k]

theorem wooley_twoStep_weight_pos
    {k r₁ r₂ : ℕ} (hr₁ : 1 ≤ r₁) (hr₂ : 1 ≤ r₂) :
    0 < wooleyTwoStepWeight k r₁ r₂ := by
  exact mul_pos (wooleyRho_pos hr₁) (wooleyRho_pos hr₂)

/-- The last inequality in (9.9), obtained directly from the two ceiling
inequalities and not from an asymptotic comparison. -/
theorem wooley_twoStep_weight_mul_scale
    {k r₁ r₂ b : ℕ} (hr₁ : 1 ≤ r₁)
    (hr₂ : 1 ≤ r₂) :
    (b : ℝ) ≤ wooleyTwoStepWeight k r₁ r₂ *
      (wooleyTwoStepB k r₁ r₂ b : ℝ) := by
  let a' := wooleyTwoStepA k r₁ b
  let b' := wooleyTwoStepB k r₁ r₂ b
  let d₁ := k - r₁ + 1
  let d₂ := k - r₂ + 1
  have h₁ : d₁ * b ≤ r₁ * a' := wooley_nextB_lower hr₁
  have h₂ : d₂ * a' ≤ r₂ * b' := wooley_nextB_lower hr₂
  have hprodNat : d₁ * d₂ * b ≤ r₁ * r₂ * b' := by
    calc
      d₁ * d₂ * b = d₂ * (d₁ * b) := by ring
      _ ≤ d₂ * (r₁ * a') := Nat.mul_le_mul_left d₂ h₁
      _ = r₁ * (d₂ * a') := by ring
      _ ≤ r₁ * (r₂ * b') := Nat.mul_le_mul_left r₁ h₂
      _ = r₁ * r₂ * b' := by ring
  have hd₁ : (0 : ℝ) < d₁ := by
    dsimp [d₁]
    positivity
  have hd₂ : (0 : ℝ) < d₂ := by
    dsimp [d₂]
    positivity
  have hprod : (d₁ : ℝ) * d₂ * b ≤
      (r₁ : ℝ) * r₂ * b' := by exact_mod_cast hprodNat
  unfold wooleyTwoStepWeight wooleyRho
  change (b : ℝ) ≤
    ((r₁ : ℝ) / d₁) * ((r₂ : ℝ) / d₂) * b'
  rw [div_mul_div_comm, div_mul_eq_mul_div,
    le_div_iff₀ (mul_pos hd₁ hd₂)]
  simpa [mul_assoc, mul_left_comm, mul_comm] using hprod

/-- The strict damping factor in (9.8). -/
theorem wooley_twoStep_weight_lt
    {k r₁ r₂ : ℕ} (hk : 3 ≤ k)
    (hr₁ : 1 ≤ r₁) (hr₁k : r₁ < k)
    (hr₂ : 1 ≤ r₂) (hr₂k : r₂ ≤ k - r₁) :
    wooleyTwoStepWeight k r₁ r₂ < (1 - 1 / (k : ℝ)) ^ 2 := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hd₁ : (0 : ℝ) < (k - r₁ + 1 : ℕ) := by positivity
  have hd₂ : (0 : ℝ) < (k - r₂ + 1 : ℕ) := by positivity
  have hr₁R : (0 : ℝ) < r₁ := by exact_mod_cast (show 0 < r₁ by omega)
  have hr₂R : (0 : ℝ) < r₂ := by exact_mod_cast (show 0 < r₂ by omega)
  have hsum : (r₁ : ℝ) + r₂ ≤ k := by exact_mod_cast (by omega : r₁ + r₂ ≤ k)
  have hden₁ : ((k - r₁ + 1 : ℕ) : ℝ) = (k : ℝ) - r₁ + 1 := by
    rw [Nat.cast_add, Nat.cast_sub hr₁k.le]
    norm_num
  have hden₂ : ((k - r₂ + 1 : ℕ) : ℝ) = (k : ℝ) - r₂ + 1 := by
    rw [Nat.cast_add, Nat.cast_sub (hr₂k.trans (Nat.sub_le _ _))]
    norm_num
  unfold wooleyTwoStepWeight wooleyRho
  rw [hden₁, hden₂]
  have hleftDen : 0 < (k : ℝ) - r₁ + 1 := by linarith
  have hrightDen : 0 < (k : ℝ) - r₂ + 1 := by linarith
  let x : ℝ := r₁
  let y : ℝ := k - r₁
  let z : ℝ := r₂
  let m : ℝ := ((k : ℝ) - 1) / k
  have hypos : 0 < y := by
    dsimp [y]
    have hr₁kR : (r₁ : ℝ) < k := by exact_mod_cast hr₁k
    linarith
  have hzle : z ≤ y := by
    dsimp [z, y]
    linarith [hsum]
  have hxy : x + y = k := by
    dsimp [x, y]
    ring
  have hmpos : 0 < m := by
    dsimp [m]
    have hkR : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
    have hnum : (0 : ℝ) < (k : ℝ) - 1 := by linarith
    exact div_pos hnum hkpos
  have hxpos : 0 < x := by simpa [x] using hr₁R
  have hzpos : 0 < z := by simpa [z] using hr₂R
  have hxone : 1 ≤ x := by
    dsimp [x]
    exact_mod_cast hr₁
  have hyone : 1 ≤ y := by
    dsimp [y]
    have hsucc : r₁ + 1 ≤ k := by omega
    have hsuccR : (r₁ : ℝ) + 1 ≤ k := by exact_mod_cast hsucc
    linarith
  have hXle : x / (x + 1) ≤ m := by
    dsimp [m]
    rw [div_le_div_iff₀ (by positivity) hkpos]
    nlinarith [hxy, hyone]
  have hYle : y / (y + 1) ≤ m := by
    dsimp [m]
    rw [div_le_div_iff₀ (by positivity) hkpos]
    nlinarith [hxy, hxone]
  have hB : z / ((k : ℝ) - z + 1) ≤ y / (x + 1) := by
    have hdz : 0 < (k : ℝ) - z + 1 := by
      have : z ≤ k := hzle.trans (by nlinarith [hxy] : y ≤ (k : ℝ))
      linarith
    rw [div_le_div_iff₀ hdz (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hzle) (by positivity : 0 ≤ x + y + 1)]
  have hcore : x / (x + 1) * (y / (y + 1)) < m * m := by
    by_cases hxeq : x = 1
    · have hygt : 1 < y := by
        have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
        nlinarith [hxy]
      have hXlt : x / (x + 1) < m := by
        dsimp [m]
        rw [div_lt_div_iff₀ (by positivity) hkpos]
        nlinarith
      exact (mul_lt_mul_of_pos_right hXlt (div_pos hypos (by positivity))).trans_le
        (mul_le_mul_of_nonneg_left hYle hmpos.le)
    · have hxgt : 1 < x := lt_of_le_of_ne hxone (Ne.symm hxeq)
      have hYlt : y / (y + 1) < m := by
        dsimp [m]
        rw [div_lt_div_iff₀ (by positivity) hkpos]
        nlinarith
      exact (mul_lt_mul_of_pos_left hYlt (div_pos hxpos (by positivity))).trans_le
        (mul_le_mul_of_nonneg_right hXle hmpos.le)
  have hrearrange :
      ((r₁ : ℝ) / ((k : ℝ) - r₁ + 1)) * (y / (x + 1)) =
        x / (x + 1) * (y / (y + 1)) := by
    dsimp [x, y]
    field_simp
  have hmain :
      ((r₁ : ℝ) / ((k : ℝ) - r₁ + 1)) *
          ((r₂ : ℝ) / ((k : ℝ) - r₂ + 1)) < m * m := by
    have hfirstNonneg : 0 ≤ (r₁ : ℝ) / ((k : ℝ) - r₁ + 1) := by
      positivity
    calc
      _ ≤ ((r₁ : ℝ) / ((k : ℝ) - r₁ + 1)) *
          (y / (x + 1)) := mul_le_mul_of_nonneg_left (by simpa [z] using hB) hfirstNonneg
      _ = x / (x + 1) * (y / (y + 1)) := hrearrange
      _ < m * m := hcore
  have htarget :
      ((r₁ : ℝ) / ((k : ℝ) - r₁ + 1)) *
          ((r₂ : ℝ) / ((k : ℝ) - r₂ + 1)) <
        (1 - 1 / (k : ℝ)) ^ 2 := by
    convert hmain using 1
    dsimp [m]
    field_simp
  exact htarget

/-- The iteration only needs strict contraction.  This version includes
`k = 2`, where the stronger printed bound in (9.8) is in fact an equality
for `r₁ = r₂ = 1`; the weight is nevertheless `1/4 < 1`. -/
theorem wooley_twoStep_weight_lt_one
    {k r₁ r₂ : ℕ} (hk : 2 ≤ k)
    (hr₁ : 1 ≤ r₁) (hr₁k : r₁ < k)
    (hr₂ : 1 ≤ r₂) (hr₂k : r₂ ≤ k - r₁) :
    wooleyTwoStepWeight k r₁ r₂ < 1 := by
  by_cases hkTwo : k = 2
  · subst k
    have hr₁eq : r₁ = 1 := by omega
    have hr₂eq : r₂ = 1 := by omega
    subst r₁
    subst r₂
    norm_num [wooleyTwoStepWeight, wooleyRho]
  · have hkThree : 3 ≤ k := by omega
    have hstrong := wooley_twoStep_weight_lt hkThree hr₁ hr₁k hr₂ hr₂k
    have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have htop : (1 - 1 / (k : ℝ)) ^ 2 < 1 := by
      have hkpos : (0 : ℝ) < k := by positivity
      have hfrac : 0 < 1 / (k : ℝ) := by positivity
      have hbase0 : 0 ≤ 1 - 1 / (k : ℝ) := by
        rw [sub_nonneg, div_le_iff₀ hkpos]
        linarith
      have hbase1 : 1 - 1 / (k : ℝ) < 1 := by linarith
      have hsq := mul_self_lt_mul_self hbase0 hbase1
      simpa [pow_two] using hsq
    exact hstrong.trans htop

/-- All arithmetic outputs (9.7)--(9.9) of the two-step construction,
apart from the analytic recurrence itself. -/
theorem wooley_twoStep_admissible
    {k r₁ r₂ b : ℕ} {delta theta : ℝ}
    (hk : 2 ≤ k) (hr₁ : 1 ≤ r₁) (hr₁k : r₁ < k)
    (hr₂ : 1 ≤ r₂) (hr₂k : r₂ ≤ k - r₁)
    (hdt : 0 ≤ delta * theta)
    (hb : (k : ℝ) ^ 2 * (delta * theta) ≤ (b : ℝ)) :
    delta * theta ≤ (wooleyTwoStepA k r₁ b : ℝ) ∧
    (k : ℝ) ^ 2 * (delta * theta) ≤
      (wooleyTwoStepB k r₁ r₂ b : ℝ) ∧
    wooleyTwoStepR k r₂ * wooleyTwoStepA k r₁ b ≤
      (k - wooleyTwoStepR k r₂ + 1) *
        wooleyTwoStepB k r₁ r₂ b ∧
    1 ≤ wooleyTwoStepR k r₂ ∧
    wooleyTwoStepR k r₂ ≤ k - 1 := by
  have hindices := wooley_twoStep_indices hr₁ hr₁k hr₂ hr₂k
  have hbaNat : b ≤ k * wooleyTwoStepA k r₁ b :=
    wooley_nextB_ge_divisor_scale hr₁ hr₁k.le
  have hba : (b : ℝ) ≤ k * wooleyTwoStepA k r₁ b := by exact_mod_cast hbaNat
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have ha : delta * theta ≤ (wooleyTwoStepA k r₁ b : ℝ) := by
    nlinarith [mul_nonneg hdt (sq_nonneg ((k : ℝ) - 1))]
  have hgrowth := wooley_twoStep_growth (b := b)
    hk hr₁ hr₁k hr₂ hr₂k
  have hb' : (k : ℝ) ^ 2 * (delta * theta) ≤
      (wooleyTwoStepB k r₁ r₂ b : ℝ) := by
    have hone : (1 : ℝ) ≤ 1 + 2 / (k : ℝ) := by
      have : (0 : ℝ) ≤ 2 / (k : ℝ) := by positivity
      linarith
    have hbnonneg : (0 : ℝ) ≤ b := by positivity
    have hbGrow : (b : ℝ) ≤ (1 + 2 / (k : ℝ)) * b := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hone hbnonneg
    exact hb.trans (hbGrow.trans hgrowth)
  have h₂ := wooley_nextB_lower (k := k) (r := r₂)
    (b := wooleyTwoStepA k r₁ b) hr₂
  have hrel : wooleyTwoStepR k r₂ * wooleyTwoStepA k r₁ b ≤
      (k - wooleyTwoStepR k r₂ + 1) *
        wooleyTwoStepB k r₁ r₂ b := by
    unfold wooleyTwoStepR
    rw [Nat.sub_sub_self (hr₂k.trans (Nat.sub_le _ _))]
    calc
      (k - r₂) * wooleyTwoStepA k r₁ b ≤
      (k - r₂ + 1) * wooleyTwoStepA k r₁ b := by
        exact Nat.mul_le_mul_right _ (by omega)
      _ ≤ r₂ * wooleyTwoStepB k r₁ r₂ b := h₂
      _ ≤ (r₂ + 1) * wooleyTwoStepB k r₁ r₂ b := by
        exact Nat.mul_le_mul_right _ (by omega)
  exact ⟨ha, hb', hrel, hindices.1, hindices.2⟩

#print axioms wooley_nextB_pos
#print axioms wooley_nextB_ge_divisor_scale
#print axioms wooley_twoStep_indices
#print axioms wooley_twoStep_upper
#print axioms wooley_twoStep_growth
#print axioms wooley_twoStep_defining_ceiling
#print axioms wooley_twoStep_weight_pos
#print axioms wooley_twoStep_weight_mul_scale
#print axioms wooley_twoStep_weight_lt
#print axioms wooley_twoStep_weight_lt_one
#print axioms wooley_twoStep_admissible

end

end GafniTao
