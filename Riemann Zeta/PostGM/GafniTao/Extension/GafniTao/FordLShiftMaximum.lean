import GafniTao.FordLShiftJensen

/-!
# Ford Lemma 3.3: selecting one physical shift

Finite Jensen is integrated, the two signs are collapsed exactly, and a
maximizing positive shift is selected.  The result is Ford's precise
`(2 * (P / m))^k` factor multiplying one shifted integral.
-/

open Finset
open scoped BigOperators
open MeasureTheory

namespace GafniTao

noncomputable section

def fordLPositiveShiftIntegral
    {k d T P : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (m p q s Q : ℕ) (h : FordPositiveShift P m) : ℝ :=
  ∫ α : UnitAddTorus (Fin k),
    ‖fordLShiftedWeylSum Ψ m (true, h) α‖ ^ k *
      ‖fordPowerFullWeylSum k Q (p * q) α‖ ^ (2 * s)
    ∂fordTorusMeasure k

theorem integrable_fordLPositiveShiftIntegrand
    {k d T P : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (m p q s Q : ℕ) (h : FordPositiveShift P m) :
    Integrable (fun α : UnitAddTorus (Fin k) =>
      ‖fordLShiftedWeylSum Ψ m (true, h) α‖ ^ k *
        ‖fordPowerFullWeylSum k Q (p * q) α‖ ^ (2 * s))
      (fordTorusMeasure k) := by
  rw [← integrableOn_univ]
  exact (((continuous_fordLShiftedWeylSum Ψ m (true, h)).norm.pow k).mul
    ((continuous_fordPowerFullWeylSum k Q (p * q)).norm.pow (2 * s)))
    |>.continuousOn.integrableOn_compact isCompact_univ

theorem fordLPositiveShiftIntegral_nonneg
    {k d T P : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (m p q s Q : ℕ) (h : FordPositiveShift P m) :
    0 ≤ fordLPositiveShiftIntegral Ψ m p q s Q h := by
  unfold fordLPositiveShiftIntegral
  apply integral_nonneg
  intro α
  exact mul_nonneg (pow_nonneg (norm_nonneg _) _)
    (pow_nonneg (norm_nonneg _) _)

theorem fordL_aggregateIntegral_le_signedSum
    {k d T P : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (m p q s Q : ℕ) (hk : 1 ≤ k) :
    (∫ α : UnitAddTorus (Fin k),
        fordLShiftAmplitude (P := P) Ψ m α ^ k *
          ‖fordPowerFullWeylSum k Q (p * q) α‖ ^ (2 * s)
        ∂fordTorusMeasure k) ≤
      (((2 * (P / m) : ℕ) : ℝ) ^ (k - 1)) *
        ∑ u : Bool × FordPositiveShift P m,
          ∫ α : UnitAddTorus (Fin k),
            ‖fordLShiftedWeylSum Ψ m u α‖ ^ k *
              ‖fordPowerFullWeylSum k Q (p * q) α‖ ^ (2 * s)
            ∂fordTorusMeasure k := by
  let C : ℝ := ((2 * (P / m) : ℕ) : ℝ) ^ (k - 1)
  let R : UnitAddTorus (Fin k) → ℝ := fun α =>
    ‖fordPowerFullWeylSum k Q (p * q) α‖ ^ (2 * s)
  have hleft := integrable_fordLShiftAmplitude_power
    (P := P) Ψ m p q s Q
  have hterm (u : Bool × FordPositiveShift P m) :
      Integrable (fun α : UnitAddTorus (Fin k) =>
        ‖fordLShiftedWeylSum Ψ m u α‖ ^ k * R α)
        (fordTorusMeasure k) := by
    rw [← integrableOn_univ]
    exact (((continuous_fordLShiftedWeylSum Ψ m u).norm.pow k).mul
      ((continuous_fordPowerFullWeylSum k Q (p * q)).norm.pow (2 * s)))
      |>.continuousOn.integrableOn_compact isCompact_univ
  have hright : Integrable (fun α : UnitAddTorus (Fin k) =>
      C * ((∑ u : Bool × FordPositiveShift P m,
        ‖fordLShiftedWeylSum Ψ m u α‖ ^ k) * R α))
      (fordTorusMeasure k) := by
    rw [← integrableOn_univ]
    apply ContinuousOn.integrableOn_compact isCompact_univ
    dsimp [C, R]
    exact (continuous_const.mul
      ((continuous_finsetSum _ fun u _ =>
        (continuous_fordLShiftedWeylSum Ψ m u).norm.pow k).mul
        ((continuous_fordPowerFullWeylSum k Q (p * q)).norm.pow (2 * s))))
      |>.continuousOn
  have hpoint (α : UnitAddTorus (Fin k)) :
      fordLShiftAmplitude (P := P) Ψ m α ^ k * R α ≤
        C * ((∑ u : Bool × FordPositiveShift P m,
          ‖fordLShiftedWeylSum Ψ m u α‖ ^ k) * R α) := by
    dsimp [C]
    have hR : 0 ≤ R α := by dsimp [R]; positivity
    calc
      fordLShiftAmplitude (P := P) Ψ m α ^ k * R α ≤
          (((2 * (P / m) : ℕ) : ℝ) ^ (k - 1) *
            ∑ u : Bool × FordPositiveShift P m,
              ‖fordLShiftedWeylSum Ψ m u α‖ ^ k) * R α := by
        exact mul_le_mul_of_nonneg_right
          (fordLShiftAmplitude_jensen Ψ m α hk) hR
      _ = (((2 * (P / m) : ℕ) : ℝ) ^ (k - 1)) *
          ((∑ u : Bool × FordPositiveShift P m,
            ‖fordLShiftedWeylSum Ψ m u α‖ ^ k) * R α) := by ring
  calc
    _ ≤ ∫ α : UnitAddTorus (Fin k),
        C * ((∑ u : Bool × FordPositiveShift P m,
          ‖fordLShiftedWeylSum Ψ m u α‖ ^ k) * R α)
        ∂fordTorusMeasure k := integral_mono hleft hright hpoint
    _ = C * ∫ α : UnitAddTorus (Fin k),
        (∑ u : Bool × FordPositiveShift P m,
          ‖fordLShiftedWeylSum Ψ m u α‖ ^ k) * R α
        ∂fordTorusMeasure k := by rw [integral_const_mul]
    _ = C * ∑ u : Bool × FordPositiveShift P m,
        ∫ α : UnitAddTorus (Fin k),
          ‖fordLShiftedWeylSum Ψ m u α‖ ^ k * R α
          ∂fordTorusMeasure k := by
      congr 1
      rw [← MeasureTheory.integral_finsetSum]
      · apply integral_congr_ae
        filter_upwards [] with α
        rw [Finset.sum_mul]
      · intro u hu
        exact hterm u
    _ = _ := rfl

theorem fordL_signedIntegralSum_eq_two_mul_positive
    {k d T P : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (m p q s Q : ℕ) :
    (∑ u : Bool × FordPositiveShift P m,
      ∫ α : UnitAddTorus (Fin k),
        ‖fordLShiftedWeylSum Ψ m u α‖ ^ k *
          ‖fordPowerFullWeylSum k Q (p * q) α‖ ^ (2 * s)
        ∂fordTorusMeasure k) =
      2 * ∑ h : FordPositiveShift P m,
        fordLPositiveShiftIntegral Ψ m p q s Q h := by
  rw [Fintype.sum_prod_type]
  simp_rw [norm_fordLShiftedWeylSum_sign]
  simp [fordLPositiveShiftIntegral]

theorem exists_fordL_positiveShift_max
    {k d T P : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (m p q s Q : ℕ) (hH : 1 ≤ P / m) :
    ∃ h : FordPositiveShift P m,
      ∀ h' : FordPositiveShift P m,
        fordLPositiveShiftIntegral Ψ m p q s Q h' ≤
          fordLPositiveShiftIntegral Ψ m p q s Q h := by
  let h₀ : FordPositiveShift P m := ⟨1, by simp [hH]⟩
  obtain ⟨h, hh, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (FordPositiveShift P m))
    (fordLPositiveShiftIntegral Ψ m p q s Q) ⟨h₀, Finset.mem_univ h₀⟩
  exact ⟨h, fun h' => hmax h' (Finset.mem_univ h')⟩

theorem exists_fordL_aggregateIntegral_le_oneShift
    {k d T P : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (m p q s Q : ℕ) (hk : 1 ≤ k) (hH : 1 ≤ P / m) :
    ∃ h : FordPositiveShift P m,
      (∫ α : UnitAddTorus (Fin k),
          fordLShiftAmplitude (P := P) Ψ m α ^ k *
            ‖fordPowerFullWeylSum k Q (p * q) α‖ ^ (2 * s)
          ∂fordTorusMeasure k) ≤
        (((2 * (P / m) : ℕ) : ℝ) ^ k) *
          fordLPositiveShiftIntegral Ψ m p q s Q h := by
  obtain ⟨h, hmax⟩ := exists_fordL_positiveShift_max Ψ m p q s Q hH
  refine ⟨h, (fordL_aggregateIntegral_le_signedSum Ψ m p q s Q hk).trans ?_⟩
  rw [fordL_signedIntegralSum_eq_two_mul_positive]
  have hsum :
      ∑ h' : FordPositiveShift P m,
          fordLPositiveShiftIntegral Ψ m p q s Q h' ≤
        (P / m : ℕ) * fordLPositiveShiftIntegral Ψ m p q s Q h := by
    simpa [← Nat.card_eq_fintype_card, natCard_fordPositiveShift,
      nsmul_eq_mul] using Finset.sum_le_card_nsmul
        (Finset.univ : Finset (FordPositiveShift P m))
        (fordLPositiveShiftIntegral Ψ m p q s Q)
        (fordLPositiveShiftIntegral Ψ m p q s Q h)
        (fun h' _ => hmax h')
  calc
    (((2 * (P / m) : ℕ) : ℝ) ^ (k - 1)) *
        (2 * ∑ h' : FordPositiveShift P m,
          fordLPositiveShiftIntegral Ψ m p q s Q h') ≤
      (((2 * (P / m) : ℕ) : ℝ) ^ (k - 1)) *
        (2 * ((P / m : ℕ) *
          fordLPositiveShiftIntegral Ψ m p q s Q h)) := by
      gcongr
    _ = (((2 * (P / m) : ℕ) : ℝ) ^ k) *
        fordLPositiveShiftIntegral Ψ m p q s Q h := by
      push_cast
      have hpow : (2 * ((P / m : ℕ) : ℝ)) ^ k =
          (2 * ((P / m : ℕ) : ℝ)) ^ (k - 1) *
            (2 * ((P / m : ℕ) : ℝ)) := by
        calc
          _ = (2 * ((P / m : ℕ) : ℝ)) ^ ((k - 1) + 1) := by
            congr 1
            exact (Nat.sub_add_cancel hk).symm
          _ = _ := pow_succ _ _
      rw [hpow]
      ring

#print axioms fordL_aggregateIntegral_le_signedSum
#print axioms exists_fordL_aggregateIntegral_le_oneShift

end

end GafniTao
