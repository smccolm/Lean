import GafniTao.HeathBrownShiftScale

/-!
# Removing `D` and `H` from the refined count

This file composes the two source factors in the per-shift estimate and then
specializes them to `H = floor ((A * lambda)^(-1/k))`.  The resulting
majorant is still deliberately unexpanded: its two factors correspond
exactly to lines 609--611 of the published proof.
-/

namespace GafniTao

noncomputable section

noncomputable def heathBrownChosenShiftFactor
    (N k : ℕ) (A lambda : ℝ) : ℝ :=
  (12 * ((k - 1).factorial : ℝ) / lambda *
      ((2 : ℝ) ^ (k - 2) *
        (A * lambda) ^ (((k - 2 : ℕ) : ℝ) / k))) *
    (4 + 4 * A * (k - 1 : ℕ) * N *
      ((2 : ℝ) ^ (k - 1) *
        (A * lambda) ^ (((k - 1 : ℕ) : ℝ) / k)))

theorem heathBrown_shift_factor_le
    {N k H : ℕ} {A lambda : ℝ}
    (hk : 3 ≤ k) (hA : 0 ≤ A) (hlambda : 0 < lambda)
    (hH : 8 ≤ H) :
    let D := heathBrownShiftBound N k H lambda
    let c := 8 * ((k - 2).factorial : ℝ) *
      (((H : ℝ) ^ (k - 2))⁻¹) / lambda
    let b := 8 * (((H : ℝ) ^ (k - 2))⁻¹) + 3
    let a := A * lambda * N / ((k - 2).factorial : ℝ)
    ((D : ℝ) + c) * (b + a * D) ≤
      (12 * ((k - 1).factorial : ℝ) *
          (((H : ℝ) ^ (k - 2))⁻¹) / lambda) *
        (4 + 4 * A * (k - 1 : ℕ) * N *
          (((H : ℝ) ^ (k - 1))⁻¹)) := by
  dsimp only
  have hleft := heathBrown_shift_plus_c_le
    (N := N) (k := k) (H := H) hk hlambda (by omega)
  have hright := heathBrown_b_plus_aD_le
    (N := N) (k := k) (H := H) hk hA hlambda hH
  exact mul_le_mul hleft hright (by positivity) (by positivity)

theorem heathBrown_shift_factor_le_chosen
    {N k : ℕ} {A lambda : ℝ}
    (hk : 3 ≤ k) (hA : 0 < A) (hlambda : 0 < lambda)
    (hsmall : A * lambda ≤ 1 / 4)
    (hlargeH : 8 ≤ heathBrownHChoice k A lambda) :
    let H := heathBrownHChoice k A lambda
    let D := heathBrownShiftBound N k H lambda
    let c := 8 * ((k - 2).factorial : ℝ) *
      (((H : ℝ) ^ (k - 2))⁻¹) / lambda
    let b := 8 * (((H : ℝ) ^ (k - 2))⁻¹) + 3
    let a := A * lambda * N / ((k - 2).factorial : ℝ)
    ((D : ℝ) + c) * (b + a * D) ≤
      heathBrownChosenShiftFactor N k A lambda := by
  dsimp only
  let H := heathBrownHChoice k A lambda
  have hraw := heathBrown_shift_factor_le
    (N := N) (k := k) (H := H) hk hA.le hlambda hlargeH
  dsimp only at hraw
  have hinvLow := heathBrownHChoice_inv_pow_le_source
    (k := k) (r := k - 2) (A := A) (lambda := lambda)
    (by omega) hA hlambda hsmall
  have hinvLast := heathBrownHChoice_inv_pow_le_source
    (k := k) (r := k - 1) (A := A) (lambda := lambda)
    (by omega) hA hlambda hsmall
  have hleft :
      12 * ((k - 1).factorial : ℝ) *
          (((H : ℝ) ^ (k - 2))⁻¹) / lambda ≤
        12 * ((k - 1).factorial : ℝ) / lambda *
          ((2 : ℝ) ^ (k - 2) *
            (A * lambda) ^ (((k - 2 : ℕ) : ℝ) / k)) := by
    dsimp only [H]
    calc
      12 * ((k - 1).factorial : ℝ) *
          (((heathBrownHChoice k A lambda : ℝ) ^ (k - 2))⁻¹) / lambda ≤
        12 * ((k - 1).factorial : ℝ) *
          ((2 : ℝ) ^ (k - 2) *
            (A * lambda) ^ (((k - 2 : ℕ) : ℝ) / k)) / lambda := by
          gcongr
      _ = 12 * ((k - 1).factorial : ℝ) / lambda *
          ((2 : ℝ) ^ (k - 2) *
            (A * lambda) ^ (((k - 2 : ℕ) : ℝ) / k)) := by ring
  have hright :
      4 + 4 * A * (k - 1 : ℕ) * N *
          (((H : ℝ) ^ (k - 1))⁻¹) ≤
        4 + 4 * A * (k - 1 : ℕ) * N *
          ((2 : ℝ) ^ (k - 1) *
            (A * lambda) ^ (((k - 1 : ℕ) : ℝ) / k)) := by
    dsimp only [H]
    gcongr
  exact hraw.trans
    (mul_le_mul hleft hright (by positivity) (by positivity))

theorem heathBrownPairCount_card_cast_le_chosen_factor
    {N k : ℕ} {f : ℝ → ℝ} {A lambda : ℝ}
    (hk : 3 ≤ k) (hN : 1 ≤ N) (hA : 0 < A) (hlambda : 0 < lambda)
    (hsmall : A * lambda ≤ 1 / 4)
    (hlargeH : 8 ≤ heathBrownHChoice k A lambda)
    (hcoordLow : ContinuousOn
      (heathBrownDerivativeCoordinate f (k - 2))
      (Set.Icc 0 (N : ℝ)))
    (hcoordLowD : DifferentiableOn ℝ
      (heathBrownDerivativeCoordinate f (k - 2))
      (Set.Ioo 0 (N : ℝ)))
    (hcoordLast : ContinuousOn
      (heathBrownDerivativeCoordinate f (k - 1))
      (Set.Icc 0 (N : ℝ)))
    (hcoordLastD : DifferentiableOn ℝ
      (heathBrownDerivativeCoordinate f (k - 1))
      (Set.Ioo 0 (N : ℝ)))
    (hraw : ContinuousOn (iteratedDeriv (k - 1) f)
      (Set.Icc 0 (N : ℝ)))
    (hrawd : DifferentiableOn ℝ (iteratedDeriv (k - 1) f)
      (Set.Ioo 0 (N : ℝ)))
    (hkBounds : ∀ x ∈ Set.Ioo (0 : ℝ) (N : ℝ),
      lambda ≤ iteratedDeriv k f x ∧
        iteratedDeriv k f x ≤ A * lambda) :
    let H := heathBrownHChoice k A lambda
    let K := heathBrownBlockParameter A lambda N
    ((heathBrownPairCount N k H f).card : ℝ) ≤
      4 * K *
        (N + 2 * heathBrownChosenShiftFactor N k A lambda *
          (1 + Real.log N)) := by
  dsimp only
  let H := heathBrownHChoice k A lambda
  let K := heathBrownBlockParameter A lambda N
  let D := heathBrownShiftBound N k H lambda
  let c : ℝ := 8 * ((k - 2).factorial : ℝ) *
    (((H : ℝ) ^ (k - 2))⁻¹) / lambda
  let b : ℝ := 8 * (((H : ℝ) ^ (k - 2))⁻¹) + 3
  let a : ℝ := A * lambda * N / ((k - 2).factorial : ℝ)
  have hcount := heathBrownPairCount_card_cast_le_at_chosen_scale
    (N := N) (k := k) (f := f) (A := A) (lambda := lambda)
    hk hN hA hlambda hsmall hlargeH hcoordLow hcoordLowD hcoordLast
    hcoordLastD hraw hrawd hkBounds
  dsimp only at hcount
  have hfactor := heathBrown_shift_factor_le_chosen
    (N := N) (k := k) (A := A) (lambda := lambda)
    hk hA hlambda hsmall hlargeH
  dsimp only at hfactor
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 ≤ 1 + Real.log (N : ℝ) := by
    have := Real.log_nonneg hNreal
    linarith
  have hinside :
      (N : ℝ) + 2 * (((D : ℝ) + c) * (b + a * D) *
          (1 + Real.log N)) ≤
        N + 2 * heathBrownChosenShiftFactor N k A lambda *
          (1 + Real.log N) := by
    have hmul := mul_le_mul_of_nonneg_right hfactor hlog
    have hmul' := mul_le_mul_of_nonneg_left hmul
      (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [D, c, b, a, H, mul_assoc] using
      (add_le_add_right hmul' (N : ℝ))
  exact hcount.trans
    (mul_le_mul_of_nonneg_left hinside (by positivity))

#print axioms heathBrown_shift_factor_le
#print axioms heathBrown_shift_factor_le_chosen
#print axioms heathBrownPairCount_card_cast_le_chosen_factor

end

end GafniTao
