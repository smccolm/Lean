import GafniTao.Pintz2023CorollaryOne

/-!
# Pintz (2023), Corollary 2

The source condition `N \ll |t|^(2/r)` is represented by an explicit positive
constant `B`.  The resulting implied constant may depend on `B`; no scale
constant is silently normalized to one.
-/

namespace GafniTao

noncomputable section

/-- The two terms retained in Pintz Corollary 2. -/
noncomputable def pintz2023CorollaryTwoMajorant
    (r N : ℕ) (epsilon xi t : ℝ) : ℝ :=
  (N : ℝ) ^ (xi - 1 / ((r : ℝ) - 1) + 3 * epsilon) *
      t ^ pintz2023HBAlpha r +
    (N : ℝ) ^ (-3 * epsilon)

/-- The source scale `N ≤ B t^(2/r)` turns the negative height power in
Corollary 1 into `B^alpha N^(-alpha)`. -/
theorem pintz2023_negative_height_le_of_scale
    {r N : ℕ} {t B : ℝ} (hr : 3 ≤ r) (hN : 0 < N)
    (ht : 0 < t) (hB : 0 < B)
    (hscale : (N : ℝ) ≤ B * t ^ (2 / (r : ℝ))) :
    t ^ (-pintz2023HBGamma r) ≤
      B ^ pintz2023HBAlpha r * (N : ℝ) ^ (-pintz2023HBAlpha r) := by
  have hrReal : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hrPos : (0 : ℝ) < r := by linarith
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
  have haPos := pintz2023HBAlpha_pos (show 2 ≤ r by omega)
  have hgamma :
      (2 / (r : ℝ)) * pintz2023HBAlpha r = pintz2023HBGamma r := by
    unfold pintz2023HBAlpha pintz2023HBGamma
    field_simp
  have hraised := Real.rpow_le_rpow hNReal.le hscale haPos.le
  have hrightNonneg : 0 ≤ t ^ (2 / (r : ℝ)) :=
    Real.rpow_nonneg ht.le _
  rw [Real.mul_rpow hB.le hrightNonneg, ← Real.rpow_mul ht.le, hgamma] at hraised
  rw [Real.rpow_neg ht.le, Real.rpow_neg hNReal.le]
  rw [inv_eq_one_div, inv_eq_one_div]
  have hdiv :
      B ^ pintz2023HBAlpha r *
          (1 / (N : ℝ) ^ pintz2023HBAlpha r) =
        B ^ pintz2023HBAlpha r /
          (N : ℝ) ^ pintz2023HBAlpha r := by
    simp only [div_eq_mul_inv, one_mul]
  rw [hdiv]
  rw [div_le_div_iff₀ (Real.rpow_pos_of_pos ht _)
    (Real.rpow_pos_of_pos hNReal _)]
  simpa only [one_mul] using hraised

/-- Pintz (2023), Corollary 2, with the hidden constant in `\ll` exposed as
the parameter `B`. -/
theorem pintz2023_corollary_two_native
    (r : ℕ) (epsilon B : ℝ) (hr : 3 ≤ r)
    (hepsilon : 0 < epsilon) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (xi : ℝ) (N R : ℕ) (t : ℝ),
      xi ≤ pintz2023HBAlpha r - 6 * epsilon →
      0 < N → N < R → R ≤ 2 * N → 0 < t →
      (N : ℝ) ≤ B * t ^ (2 / (r : ℝ)) →
      ‖pintz2023WeightedBlock xi N R t‖ ≤
        C * pintz2023CorollaryTwoMajorant r N epsilon xi t := by
  obtain ⟨C₀, hC₀, hcorOne⟩ :=
    pintz2023_corollary_one_native r epsilon hr hepsilon
  let BA : ℝ := B ^ pintz2023HBAlpha r
  let D : ℝ := 1 + BA
  have hBApos : 0 < BA := by
    dsimp only [BA]
    exact Real.rpow_pos_of_pos hB _
  have hDpos : 0 < D := by dsimp only [D]; linarith
  refine ⟨C₀ * D, mul_pos hC₀ hDpos, ?_⟩
  intro xi N R t hxi hN hNR hR ht hscale
  have hNReal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hdecay := pintz2023_negative_height_le_of_scale hr hN ht hB hscale
  have hthirdExp :
      xi + 3 * epsilon - pintz2023HBAlpha r ≤ -3 * epsilon := by
    linarith
  have hthirdPow := Real.rpow_le_rpow_of_exponent_le hNReal hthirdExp
  have hthird :
      (N : ℝ) ^ (xi + 3 * epsilon) *
          t ^ (-pintz2023HBGamma r) ≤
        BA * (N : ℝ) ^ (-3 * epsilon) := by
    calc
      _ ≤ (N : ℝ) ^ (xi + 3 * epsilon) *
          (B ^ pintz2023HBAlpha r *
            (N : ℝ) ^ (-pintz2023HBAlpha r)) :=
        mul_le_mul_of_nonneg_left hdecay (Real.rpow_nonneg (by positivity) _)
      _ = BA * ((N : ℝ) ^ (xi + 3 * epsilon) *
          (N : ℝ) ^ (-pintz2023HBAlpha r)) := by
        dsimp only [BA]
        ring
      _ = BA * (N : ℝ) ^
          (xi + 3 * epsilon - pintz2023HBAlpha r) := by
        rw [← Real.rpow_add (show (0 : ℝ) < N by positivity)]
        congr 2
      _ ≤ BA * (N : ℝ) ^ (-3 * epsilon) :=
        mul_le_mul_of_nonneg_left hthirdPow hBApos.le
  have hfirstNonneg : 0 ≤
      (N : ℝ) ^ (xi - 1 / ((r : ℝ) - 1) + 3 * epsilon) *
        t ^ pintz2023HBAlpha r := by positivity
  have hmiddleNonneg : 0 ≤ (N : ℝ) ^ (-3 * epsilon) := by positivity
  have hmaj :
      pintz2023CorollaryOneMajorant r N epsilon xi t ≤
        D * pintz2023CorollaryTwoMajorant r N epsilon xi t := by
    unfold pintz2023CorollaryOneMajorant pintz2023CorollaryTwoMajorant
    dsimp only [D]
    calc
      _ ≤
          (N : ℝ) ^ (xi - 1 / ((r : ℝ) - 1) + 3 * epsilon) *
              t ^ pintz2023HBAlpha r +
            (N : ℝ) ^ (-3 * epsilon) +
            BA * (N : ℝ) ^ (-3 * epsilon) := by
        linarith
      _ ≤ (1 + BA) *
          ((N : ℝ) ^ (xi - 1 / ((r : ℝ) - 1) + 3 * epsilon) *
              t ^ pintz2023HBAlpha r +
            (N : ℝ) ^ (-3 * epsilon)) := by
        nlinarith [mul_nonneg hBApos.le hfirstNonneg]
  calc
    ‖pintz2023WeightedBlock xi N R t‖ ≤
        C₀ * pintz2023CorollaryOneMajorant r N epsilon xi t :=
      hcorOne xi N R t hxi hN hNR hR ht
    _ ≤ C₀ * (D * pintz2023CorollaryTwoMajorant r N epsilon xi t) :=
      mul_le_mul_of_nonneg_left hmaj hC₀.le
    _ = (C₀ * D) * pintz2023CorollaryTwoMajorant r N epsilon xi t := by ring

#print axioms pintz2023_negative_height_le_of_scale
#print axioms pintz2023_corollary_two_native

end

end GafniTao
