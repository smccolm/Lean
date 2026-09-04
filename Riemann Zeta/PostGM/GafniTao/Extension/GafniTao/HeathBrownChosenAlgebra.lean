import GafniTao.HeathBrownRefinedScaleBound

/-!
# Exponent algebra for Heath-Brown's chosen block length

The constants below depend only on the source parameters `A` and `k`.  They
separate those allowed constants from the two powers of `lambda` which drive
the published estimate.
-/

namespace GafniTao

noncomputable section

noncomputable def heathBrownChosenFirstConstant (k : ℕ) (A : ℝ) : ℝ :=
  12 * ((k - 1).factorial : ℝ) * (2 : ℝ) ^ (k - 2) *
    A ^ (((k - 2 : ℕ) : ℝ) / k)

noncomputable def heathBrownChosenSecondConstant (k : ℕ) (A : ℝ) : ℝ :=
  4 * A * (k - 1 : ℕ) * (2 : ℝ) ^ (k - 1) *
    A ^ (((k - 1 : ℕ) : ℝ) / k)

noncomputable def heathBrownChosenTotalConstant (k : ℕ) (A : ℝ) : ℝ :=
  4 * heathBrownChosenFirstConstant k A +
    heathBrownChosenFirstConstant k A * heathBrownChosenSecondConstant k A

theorem heathBrownChosenFirstConstant_nonneg
    (k : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    0 ≤ heathBrownChosenFirstConstant k A := by
  unfold heathBrownChosenFirstConstant
  positivity

theorem heathBrownChosenSecondConstant_nonneg
    (k : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    0 ≤ heathBrownChosenSecondConstant k A := by
  unfold heathBrownChosenSecondConstant
  positivity

theorem heathBrownChosenFirstFactor_eq
    {k : ℕ} {A lambda : ℝ}
    (hk : 3 ≤ k) (hA : 0 < A) (hlambda : 0 < lambda) :
    12 * ((k - 1).factorial : ℝ) / lambda *
        ((2 : ℝ) ^ (k - 2) *
          (A * lambda) ^ (((k - 2 : ℕ) : ℝ) / k)) =
      heathBrownChosenFirstConstant k A *
        lambda ^ (-(2 / (k : ℝ))) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have heq : (-1 : ℝ) + ((k - 2 : ℕ) : ℝ) / k =
      -(2 / (k : ℝ)) := by
    rw [Nat.cast_sub (by omega : 2 ≤ k)]
    push_cast
    field_simp
    ring
  rw [Real.mul_rpow hA.le hlambda.le]
  calc
    12 * ((k - 1).factorial : ℝ) / lambda *
        ((2 : ℝ) ^ (k - 2) *
          (A ^ (((k - 2 : ℕ) : ℝ) / k) *
            lambda ^ (((k - 2 : ℕ) : ℝ) / k))) =
      heathBrownChosenFirstConstant k A *
        (lambda⁻¹ * lambda ^ (((k - 2 : ℕ) : ℝ) / k)) := by
          unfold heathBrownChosenFirstConstant
          ring
    _ = heathBrownChosenFirstConstant k A *
        (lambda ^ (-1 : ℝ) *
          lambda ^ (((k - 2 : ℕ) : ℝ) / k)) := by
      rw [Real.rpow_neg_one]
    _ = heathBrownChosenFirstConstant k A *
        lambda ^ ((-1 : ℝ) + ((k - 2 : ℕ) : ℝ) / k) := by
      rw [Real.rpow_add hlambda]
    _ = heathBrownChosenFirstConstant k A *
        lambda ^ (-(2 / (k : ℝ))) := by rw [heq]

theorem heathBrownChosenSecondFactor_eq
    {k N : ℕ} {A lambda : ℝ}
    (hk : 3 ≤ k) (hA : 0 < A) (hlambda : 0 < lambda) :
    4 * A * (k - 1 : ℕ) * N *
        ((2 : ℝ) ^ (k - 1) *
          (A * lambda) ^ (((k - 1 : ℕ) : ℝ) / k)) =
      heathBrownChosenSecondConstant k A * N *
        lambda ^ (1 - 1 / (k : ℝ)) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have heq : ((k - 1 : ℕ) : ℝ) / k =
      1 - 1 / (k : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ k)]
    push_cast
    field_simp
  unfold heathBrownChosenSecondConstant
  rw [Real.mul_rpow hA.le hlambda.le, heq]
  ring

theorem heathBrownChosenShiftFactor_eq_source
    {k N : ℕ} {A lambda : ℝ}
    (hk : 3 ≤ k) (hA : 0 < A) (hlambda : 0 < lambda) :
    heathBrownChosenShiftFactor N k A lambda =
      (heathBrownChosenFirstConstant k A *
        lambda ^ (-(2 / (k : ℝ)))) *
      (4 + heathBrownChosenSecondConstant k A * N *
        lambda ^ (1 - 1 / (k : ℝ))) := by
  unfold heathBrownChosenShiftFactor
  rw [heathBrownChosenFirstFactor_eq hk hA hlambda,
    heathBrownChosenSecondFactor_eq hk hA hlambda]

theorem heathBrownChosenShiftFactor_le_source_sum
    {k N : ℕ} {A lambda : ℝ}
    (hk : 3 ≤ k) (hA : 0 < A) (hlambda : 0 < lambda)
    (hlambdaOne : lambda ≤ 1) :
    heathBrownChosenShiftFactor N k A lambda ≤
      heathBrownChosenTotalConstant k A *
        (lambda ^ (-(2 / (k : ℝ))) + N) := by
  let C₁ := heathBrownChosenFirstConstant k A
  let C₂ := heathBrownChosenSecondConstant k A
  let L := lambda ^ (-(2 / (k : ℝ)))
  let q := lambda ^ (1 - 3 / (k : ℝ))
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hC₁ : 0 ≤ C₁ := heathBrownChosenFirstConstant_nonneg k hA.le
  have hC₂ : 0 ≤ C₂ := heathBrownChosenSecondConstant_nonneg k hA.le
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hexp : 0 ≤ 1 - 3 / (k : ℝ) := by
    have hkReal : (3 : ℝ) ≤ k := by exact_mod_cast hk
    rw [sub_nonneg, div_le_one (by positivity : (0 : ℝ) < k)]
    exact hkReal
  have hq : q ≤ 1 := by
    dsimp only [q]
    exact Real.rpow_le_one hlambda.le hlambdaOne hexp
  have hcombine :
      lambda ^ (-(2 / (k : ℝ))) *
          lambda ^ (1 - 1 / (k : ℝ)) = q := by
    rw [← Real.rpow_add hlambda]
    congr 1
    dsimp only [q]
    field_simp
    ring
  rw [heathBrownChosenShiftFactor_eq_source hk hA hlambda]
  change (C₁ * L) *
      (4 + C₂ * (N : ℝ) * lambda ^ (1 - 1 / (k : ℝ))) ≤
    heathBrownChosenTotalConstant k A * (L + N)
  have hexpand :
      (C₁ * L) *
          (4 + C₂ * (N : ℝ) * lambda ^ (1 - 1 / (k : ℝ))) =
        4 * C₁ * L + C₁ * C₂ * N * q := by
    rw [← hcombine]
    ring
  rw [hexpand]
  have hterm₂a : C₁ * C₂ * (N : ℝ) * q ≤ C₁ * C₂ * N := by
    have hcoeff : 0 ≤ C₁ * C₂ * (N : ℝ) := by positivity
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hq hcoeff
  have hcoeff₁ : 4 * C₁ ≤ heathBrownChosenTotalConstant k A := by
    change 4 * C₁ ≤ 4 * C₁ + C₁ * C₂
    nlinarith [mul_nonneg hC₁ hC₂]
  have hcoeff₂ : C₁ * C₂ ≤ heathBrownChosenTotalConstant k A := by
    change C₁ * C₂ ≤ 4 * C₁ + C₁ * C₂
    nlinarith
  have hterm₁ : 4 * C₁ * L ≤
      heathBrownChosenTotalConstant k A * L :=
    mul_le_mul_of_nonneg_right hcoeff₁ hL
  have hterm₂b : C₁ * C₂ * (N : ℝ) ≤
      heathBrownChosenTotalConstant k A * N := by
    exact mul_le_mul_of_nonneg_right hcoeff₂ (Nat.cast_nonneg N)
  calc
    4 * C₁ * L + C₁ * C₂ * (N : ℝ) * q ≤
        heathBrownChosenTotalConstant k A * L +
          heathBrownChosenTotalConstant k A * N :=
      add_le_add hterm₁ (hterm₂a.trans hterm₂b)
    _ = heathBrownChosenTotalConstant k A * (L + N) := by ring

#print axioms heathBrownChosenFirstFactor_eq
#print axioms heathBrownChosenSecondFactor_eq
#print axioms heathBrownChosenShiftFactor_eq_source
#print axioms heathBrownChosenShiftFactor_le_source_sum

end

end GafniTao
