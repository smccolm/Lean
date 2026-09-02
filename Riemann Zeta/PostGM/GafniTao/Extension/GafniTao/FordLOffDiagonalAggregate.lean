import GafniTao.FordLOffDiagonalFourier

/-!
# Ford Lemma 3.3: summing the sign/shift partition

The sigma-type enlargement is summed exactly over every sign/shift tuple.
Because the coordinates are independent, the sum of products is the `k`th
power of the one-coordinate amplitude.  This is the finite identity behind
Ford's subsequent arithmetic-geometric-mean step.
-/

open Finset
open scoped BigOperators
open MeasureTheory

namespace GafniTao

noncomputable section

def fordLShiftAmplitude
    {k d T P : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (m : ℕ) (α : UnitAddTorus (Fin k)) : ℝ :=
  ∑ u : Bool × FordPositiveShift P m, ‖fordLShiftedWeylSum Ψ m u α‖

theorem fordL_sum_fixedMajorant
    {k d T P : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (m p q s Q : ℕ) (α : UnitAddTorus (Fin k)) :
    (∑ u : FordLOffDiagonalParameter k P m,
        fordLFixedMajorant Ψ m p q s Q u α) =
      fordLShiftAmplitude (P := P) Ψ m α ^ k *
        ‖fordPowerFullWeylSum k Q (p * q) α‖ ^ (2 * s) := by
  unfold fordLFixedMajorant fordLShiftAmplitude
  rw [← Finset.sum_mul]
  congr 1
  rw [Fintype.sum_pow]

theorem integrable_fordLShiftAmplitude_power
    {k d T P : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (m p q s Q : ℕ) :
    Integrable (fun α : UnitAddTorus (Fin k) =>
      fordLShiftAmplitude (P := P) Ψ m α ^ k *
        ‖fordPowerFullWeylSum k Q (p * q) α‖ ^ (2 * s))
      (fordTorusMeasure k) := by
  rw [← integrableOn_univ]
  apply ContinuousOn.integrableOn_compact isCompact_univ
  unfold fordLShiftAmplitude
  exact (((continuous_finsetSum _ fun u _ =>
    (continuous_fordLShiftedWeylSum Ψ m u).norm).pow k).mul
      ((continuous_fordPowerFullWeylSum k Q (p * q)).norm.pow (2 * s))).continuousOn

theorem fordLOffDiagonalCount_le_aggregateIntegral
    {k d T : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (s P Q p q r : ℕ) [NeZero (p ^ r)] :
    (fordLOffDiagonalCount Ψ s P Q p q r : ℝ) ≤
      ∫ α : UnitAddTorus (Fin k),
        fordLShiftAmplitude (P := P) Ψ (p ^ r) α ^ k *
          ‖fordPowerFullWeylSum k Q (p * q) α‖ ^ (2 * s)
        ∂fordTorusMeasure k := by
  let U := FordLOffDiagonalParameter k P (p ^ r)
  let S := fun u : U => FordLFixedSolution Ψ (p ^ r) p q s Q u
  have hinj := fordLOffDiagonalCount_le_fixedSigma Ψ s P Q p q r
  calc
    (fordLOffDiagonalCount Ψ s P Q p q r : ℝ) ≤
        (Nat.card (Σ u : U, S u) : ℝ) := by exact_mod_cast hinj
    _ = ∑ u : U, (Nat.card (S u) : ℝ) := by
      rw [Nat.card_sigma, Nat.cast_sum]
    _ ≤ ∑ u : U, ∫ α : UnitAddTorus (Fin k),
          fordLFixedMajorant Ψ (p ^ r) p q s Q u α
          ∂fordTorusMeasure k := by
      apply Finset.sum_le_sum
      intro u hu
      exact fordLFixed_card_le_integral_majorant Ψ (p ^ r) p q s Q u
    _ = ∫ α : UnitAddTorus (Fin k), ∑ u : U,
          fordLFixedMajorant Ψ (p ^ r) p q s Q u α
          ∂fordTorusMeasure k := by
      rw [MeasureTheory.integral_finsetSum]
      intro u hu
      exact integrable_fordLFixedMajorant Ψ (p ^ r) p q s Q u
    _ = ∫ α : UnitAddTorus (Fin k),
          fordLShiftAmplitude (P := P) Ψ (p ^ r) α ^ k *
            ‖fordPowerFullWeylSum k Q (p * q) α‖ ^ (2 * s)
          ∂fordTorusMeasure k := by
      apply integral_congr_ae
      filter_upwards [] with α
      exact fordL_sum_fixedMajorant Ψ (p ^ r) p q s Q α

#print axioms fordL_sum_fixedMajorant
#print axioms fordLOffDiagonalCount_le_aggregateIntegral

end

end GafniTao
