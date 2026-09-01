import GafniTao.FordKThreeHolder

/-!
# Ford Lemma 3.2: the scaled Vinogradov factor

The auxiliary power sum in Ford's `K` count has coordinate `j` multiplied
by `q^(j+1)`.  For positive `q`, cancellation gives exactly the ordinary
Vinogradov solution set.  This file proves that fact before identifying the
literal torus factor in the three-factor Hölder estimate.
-/

open Finset
open scoped BigOperators
open MeasureTheory

namespace GafniTao

noncomputable section

abbrev FordScaledPowerSolution (s k Q q : ℕ) :=
  {xy : FordBox s Q × FordBox s Q //
    fordS3BoxMoment (k := k) q xy.1 = fordS3BoxMoment q xy.2}

theorem fordS3BoxMoment_eq_scaled_vinogradov
    {s k Q q : ℕ} (x : FordBox s Q) (j : Fin k) :
    fordS3BoxMoment (k := k) q x j =
      (q : ℤ) ^ ((j : ℕ) + 1) * fordVinogradovPowerVector s k Q x j := by
  simp [fordS3BoxMoment, fordVinogradovPowerVector, fordBoxValue,
    Finset.mul_sum]

def fordScaledPowerSolutionEquiv
    {s k Q q : ℕ} (hq : 0 < q) :
    FordScaledPowerSolution s k Q q ≃ FordPowerSolution s k Q where
  toFun u := ⟨u.1, by
    funext j
    have h := congrFun u.2 j
    rw [fordS3BoxMoment_eq_scaled_vinogradov,
      fordS3BoxMoment_eq_scaled_vinogradov] at h
    exact mul_left_cancel₀ (by positivity : (q : ℤ) ^ ((j : ℕ) + 1) ≠ 0) h⟩
  invFun u := ⟨u.1, by
    funext j
    have h := congrFun u.2 j
    rw [fordS3BoxMoment_eq_scaled_vinogradov,
      fordS3BoxMoment_eq_scaled_vinogradov, h]⟩
  left_inv u := by rfl
  right_inv u := by rfl

theorem card_fordScaledPowerSolution
    {s k Q q : ℕ} (hq : 0 < q) :
    Nat.card (FordScaledPowerSolution s k Q q) =
      fordVinogradovMomentNat s k Q := by
  rw [Nat.card_congr (fordScaledPowerSolutionEquiv hq),
    card_fordPowerSolution]

def fordScaledPowerToCharacterCollision
    {s k Q q : ℕ} :
    FordScaledPowerSolution s k Q q ≃
      FordCharacterCollision
        (fordS3BoxMoment (k := k) q : FordBox s Q → Fin k → ℤ)
        (fun _ : Unit ↦ (0 : Fin k → ℤ)) where
  toFun u := ⟨((u.1.1, ()), (u.1.2, ())), by
    simpa using u.2⟩
  invFun u := ⟨(u.1.1.1, u.1.2.1), by
    simpa using u.2⟩
  left_inv u := by rfl
  right_inv u := by
    apply Subtype.ext
    rcases u with ⟨⟨⟨x, u⟩, ⟨y, v⟩⟩, h⟩
    cases u
    cases v
    rfl

theorem fordPowerMomentIntegral_eq_scaled_card (k s Q q : ℕ) :
    fordPowerMomentIntegral k s Q q =
      (Nat.card (FordScaledPowerSolution s k Q q) : ℝ) := by
  let M : FordBox s Q → Fin k → ℤ := fordS3BoxMoment (k := k) q
  let Z : Unit → Fin k → ℤ := fun _ ↦ 0
  have hmean := ford_character_collision_mean_eq M Z
  have hcard : Nat.card (FordScaledPowerSolution s k Q q) =
      Nat.card (FordCharacterCollision M Z) :=
    Nat.card_congr
      (fordScaledPowerToCharacterCollision (s := s) (k := k) (Q := Q) (q := q))
  calc
    fordPowerMomentIntegral k s Q q =
        ∫ a : UnitAddTorus (Fin k),
          ‖fordCharacterSum M a‖ ^ 2 * ‖fordCharacterSum Z a‖ ^ 2
          ∂fordTorusMeasure k := by
      unfold fordPowerMomentIntegral
      apply integral_congr_ae
      filter_upwards [] with a
      have hZ : fordCharacterSum Z a = 1 := by
        simp [Z, fordCharacterSum, UnitAddTorus.mFourier_zero]
      rw [hZ, norm_one, one_pow, mul_one]
      dsimp [M]
      rw [fordPowerBoxCharacterSum_eq_pow]
      simp only [norm_pow, ← pow_mul]
      rw [mul_comm s 2]
    _ = (Nat.card (FordCharacterCollision M Z) : ℝ) := hmean
    _ = (Nat.card (FordScaledPowerSolution s k Q q) : ℝ) := by
      norm_cast
      exact hcard.symm

theorem fordPowerMomentIntegral_eq_vinogradov
    {k s Q q : ℕ} (hq : 0 < q) :
    fordPowerMomentIntegral k s Q q =
      (fordVinogradovMomentNat s k Q : ℝ) := by
  rw [fordPowerMomentIntegral_eq_scaled_card,
    card_fordScaledPowerSolution hq]

theorem fordK_repeated_integral_holder_real
    {k d T : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (s P Q q : ℕ) (hk : 1 ≤ k) (hq : 0 < q) :
    fordKRepeatedIntegral Ψ s P Q q ≤
      (fordKCount Ψ s P Q q : ℝ) ^ (1 - 1 / (k : ℝ)) *
        (fordVinogradovMomentNat s k Q : ℝ) ^ (1 / (2 * k : ℝ)) *
        (fordKCount (fordDoubleIntegerPolynomialSystem Ψ) s P Q q : ℝ) ^
          (1 / (2 * k : ℝ)) := by
  have h := fordK_repeated_integral_holder Ψ s P Q q hk
  rw [fordKFourier_eq_count, fordPowerMomentIntegral_eq_vinogradov hq,
    fordKFourier_eq_count] at h
  have hkR : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hp : 0 ≤ 1 - 1 / (k : ℝ) := by
    rw [sub_nonneg, div_le_one hkR]
    exact_mod_cast hk
  have hr : 0 ≤ 1 / (2 * k : ℝ) := by positivity
  let RHS : ℝ :=
    (fordKCount Ψ s P Q q : ℝ) ^ (1 - 1 / (k : ℝ)) *
      (fordVinogradovMomentNat s k Q : ℝ) ^ (1 / (2 * k : ℝ)) *
      (fordKCount (fordDoubleIntegerPolynomialSystem Ψ) s P Q q : ℝ) ^
        (1 / (2 * k : ℝ))
  have hRHS : 0 ≤ RHS := by dsimp [RHS]; positivity
  apply (ENNReal.ofReal_le_ofReal_iff hRHS).mp
  calc
    ENNReal.ofReal (fordKRepeatedIntegral Ψ s P Q q) ≤
        ENNReal.ofReal (fordKCount Ψ s P Q q : ℝ) ^
            (1 - 1 / (k : ℝ)) *
          ENNReal.ofReal (fordVinogradovMomentNat s k Q : ℝ) ^
            (1 / (2 * k : ℝ)) *
          ENNReal.ofReal
            (fordKCount (fordDoubleIntegerPolynomialSystem Ψ) s P Q q : ℝ) ^
              (1 / (2 * k : ℝ)) := h
    _ = ENNReal.ofReal RHS := by
      dsimp [RHS]
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_rpow_of_nonneg (by positivity) hp,
        ENNReal.ofReal_rpow_of_nonneg (by positivity) hr,
        ENNReal.ofReal_rpow_of_nonneg (by positivity) hr]

#print axioms card_fordScaledPowerSolution
#print axioms fordPowerMomentIntegral_eq_vinogradov
#print axioms fordK_repeated_integral_holder_real

end

end GafniTao
