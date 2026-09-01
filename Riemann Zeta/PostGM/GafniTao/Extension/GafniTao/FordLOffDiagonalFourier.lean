import GafniTao.FordLOffDiagonalEnlargement

/-!
# Ford Lemma 3.3: Fourier formula for a fixed shift tuple

For each fixed sign/shift tuple, zero-frequency orthogonality expresses the
enlarged solution count as the mean of a product of shifted Weyl sums and the
power-pair factor.  Taking the norm gives the exact nonnegative majorant used
in Ford's off-diagonal branch.
-/

open Finset
open scoped BigOperators
open MeasureTheory

namespace GafniTao

noncomputable section

def fordLShiftedWeylSum
    {k d T P : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (m : ℕ) (u : Bool × FordPositiveShift P m)
    (α : UnitAddTorus (Fin k)) : ℂ :=
  fordCharacterSum (fordLSignedShiftMoment Ψ m u) α

theorem fordLFixedPolynomial_characterSum
    {k d T P : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (m : ℕ) (u : FordLOffDiagonalParameter k P m)
    (α : UnitAddTorus (Fin k)) :
    fordCharacterSum (fordLFixedPolynomialMoment Ψ m u) α =
      ∏ i : Fin k, fordLShiftedWeylSum Ψ m (u i) α := by
  classical
  have hfourier (z : Fin k → Fin P) :
      UnitAddTorus.mFourier (fordLFixedPolynomialMoment Ψ m u z) α =
        ∏ i : Fin k,
          UnitAddTorus.mFourier (fordLSignedShiftMoment Ψ m (u i) (z i)) α := by
    have hset (t : Finset (Fin k)) :
        UnitAddTorus.mFourier
            (∑ i ∈ t, fordLSignedShiftMoment Ψ m (u i) (z i)) α =
          ∏ i ∈ t,
            UnitAddTorus.mFourier (fordLSignedShiftMoment Ψ m (u i) (z i)) α := by
      induction t using Finset.induction_on with
      | empty =>
          change UnitAddTorus.mFourier (0 : Fin k → ℤ) α = 1
          rw [UnitAddTorus.mFourier_zero]
      | @insert i t hi ih =>
          rw [Finset.sum_insert hi, UnitAddTorus.mFourier_add,
            Finset.prod_insert hi, ih]
    have hmoment : fordLFixedPolynomialMoment Ψ m u z =
        ∑ i : Fin k, fordLSignedShiftMoment Ψ m (u i) (z i) := by
      funext j
      simp [fordLFixedPolynomialMoment]
    rw [hmoment]
    simpa using hset Finset.univ
  unfold fordCharacterSum
  simp_rw [hfourier]
  symm
  calc
    (∏ i : Fin k, fordLShiftedWeylSum Ψ m (u i) α) =
        ∏ i : Fin k, ∑ z : Fin P,
          UnitAddTorus.mFourier (fordLSignedShiftMoment Ψ m (u i) z) α := by
      rfl
    _ = ∑ z : Fin k → Fin P, ∏ i : Fin k,
          UnitAddTorus.mFourier (fordLSignedShiftMoment Ψ m (u i) (z i)) α := by
      rw [Finset.prod_univ_sum]
      simp

theorem fordLFixedTotal_characterSum
    {k d T P : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (m p q s Q : ℕ) (u : FordLOffDiagonalParameter k P m)
    (α : UnitAddTorus (Fin k)) :
    fordCharacterSum (fordLFixedTotalMoment Ψ m p q s Q u) α =
      (∏ i : Fin k, fordLShiftedWeylSum Ψ m (u i) α) *
        (‖fordPowerFullWeylSum k Q (p * q) α‖ ^ (2 * s) : ℝ) := by
  unfold fordLFixedTotalMoment fordCharacterSum
  rw [Fintype.sum_prod_type]
  simp_rw [UnitAddTorus.mFourier_add]
  rw [← Finset.sum_mul_sum]
  change fordCharacterSum (fordLFixedPolynomialMoment Ψ m u) α *
      fordCharacterSum (fordLPowerPairMoment k Q p q s) α = _
  rw [fordLFixedPolynomial_characterSum, fordLPowerPair_characterSum]

theorem fordLFixed_character_mean_eq_count
    {k d T P : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (m p q s Q : ℕ) (u : FordLOffDiagonalParameter k P m) :
    ∫ α : UnitAddTorus (Fin k),
        (∏ i : Fin k, fordLShiftedWeylSum Ψ m (u i) α) *
          (‖fordPowerFullWeylSum k Q (p * q) α‖ ^ (2 * s) : ℝ)
        ∂fordTorusMeasure k =
      (Nat.card (FordLFixedSolution Ψ m p q s Q u) : ℂ) := by
  rw [← ford_character_sum_mean_eq_zero_count
    (fordLFixedTotalMoment Ψ m p q s Q u)]
  apply integral_congr_ae
  filter_upwards [] with α
  exact (fordLFixedTotal_characterSum Ψ m p q s Q u α).symm

def fordLFixedMajorant
    {k d T P : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (m p q s Q : ℕ) (u : FordLOffDiagonalParameter k P m)
    (α : UnitAddTorus (Fin k)) : ℝ :=
  (∏ i : Fin k, ‖fordLShiftedWeylSum Ψ m (u i) α‖) *
    ‖fordPowerFullWeylSum k Q (p * q) α‖ ^ (2 * s)

theorem continuous_fordLShiftedWeylSum
    {k d T P : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (m : ℕ) (u : Bool × FordPositiveShift P m) :
    Continuous (fordLShiftedWeylSum Ψ m u) := by
  unfold fordLShiftedWeylSum fordCharacterSum
  fun_prop

theorem integrable_fordLFixedMajorant
    {k d T P : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (m p q s Q : ℕ) (u : FordLOffDiagonalParameter k P m) :
    Integrable (fordLFixedMajorant Ψ m p q s Q u) (fordTorusMeasure k) := by
  rw [← integrableOn_univ]
  apply ContinuousOn.integrableOn_compact isCompact_univ
  unfold fordLFixedMajorant
  exact ((continuous_finsetProd _ fun i _ =>
    (continuous_fordLShiftedWeylSum Ψ m (u i)).norm).mul
      ((continuous_fordPowerFullWeylSum k Q (p * q)).norm.pow (2 * s))).continuousOn

theorem fordLFixed_card_le_integral_majorant
    {k d T P : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (m p q s Q : ℕ) (u : FordLOffDiagonalParameter k P m) :
    (Nat.card (FordLFixedSolution Ψ m p q s Q u) : ℝ) ≤
      ∫ α : UnitAddTorus (Fin k), fordLFixedMajorant Ψ m p q s Q u α
        ∂fordTorusMeasure k := by
  let H : UnitAddTorus (Fin k) → ℂ := fun α =>
    (∏ i : Fin k, fordLShiftedWeylSum Ψ m (u i) α) *
      (‖fordPowerFullWeylSum k Q (p * q) α‖ ^ (2 * s) : ℝ)
  have hmean := fordLFixed_character_mean_eq_count Ψ m p q s Q u
  have hnorm (α : UnitAddTorus (Fin k)) :
      ‖H α‖ = fordLFixedMajorant Ψ m p q s Q u α := by
    dsimp [H]
    simp [fordLFixedMajorant, norm_prod, norm_pow]
  calc
    (Nat.card (FordLFixedSolution Ψ m p q s Q u) : ℝ) =
        ‖∫ α, H α ∂fordTorusMeasure k‖ := by rw [hmean]; simp
    _ ≤ ∫ α, ‖H α‖ ∂fordTorusMeasure k := norm_integral_le_integral_norm H
    _ = ∫ α, fordLFixedMajorant Ψ m p q s Q u α
          ∂fordTorusMeasure k := by
      apply integral_congr_ae
      filter_upwards [] with α
      exact hnorm α

#print axioms fordLFixedPolynomial_characterSum
#print axioms fordLFixed_character_mean_eq_count
#print axioms fordLFixed_card_le_integral_majorant

end

end GafniTao
