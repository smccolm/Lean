import GafniTao.FordS4BoundaryRange
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# The exact Hölder interpolation used in Ford Lemma 3.2

This is the nonnegative `L^{n-1}` interpolation between the weighted zeroth
and `n`-th moments.  It is stated for `ENNReal` so zero and infinite
integrals are handled without hidden divisions.
-/

open MeasureTheory

namespace GafniTao

noncomputable section

theorem ford_ennreal_interpolation_point
    {n : ℕ} (hn : 2 ≤ n) (x y : ENNReal) :
    (x * y ^ n) ^ (((n : ℝ) - 1) / (n : ℝ)) *
        x ^ (1 / (n : ℝ)) =
      x * y ^ (n - 1) := by
  let p : ℝ := ((n : ℝ) - 1) / (n : ℝ)
  let q : ℝ := 1 / (n : ℝ)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnOneR : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hp : 0 < p := by
    dsimp [p]
    exact div_pos (sub_pos.mpr hnOneR) hnR
  have hq : 0 < q := by
    dsimp [q]
    positivity
  have hpq : p + q = 1 := by
    dsimp [p, q]
    field_simp
    ring
  have hnp : (n : ℝ) * p = (n : ℝ) - 1 := by
    dsimp [p]
    field_simp
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  change (x * y ^ n) ^ p * x ^ q = _
  calc
    (x * y ^ n) ^ p * x ^ q =
        (x ^ p * x ^ q) * (y ^ n) ^ p := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le]
      ac_rfl
    _ = x ^ (p + q) * (y ^ n) ^ p := by
      rw [ENNReal.rpow_add_of_nonneg p q hp.le hq.le]
    _ = x * (y ^ n) ^ p := by rw [hpq, ENNReal.rpow_one]
    _ = x * y ^ (n - 1) := by
      congr 1
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, hnp,
        ← hcast, ENNReal.rpow_natCast]

theorem ford_lintegral_weighted_interpolation
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {A B : α → ENNReal} (hA : AEMeasurable A μ) (hB : AEMeasurable B μ)
    {n : ℕ} (hn : 2 ≤ n) :
    ∫⁻ x, A x * B x ^ (n - 1) ∂μ ≤
      (∫⁻ x, A x * B x ^ n ∂μ) ^ (((n : ℝ) - 1) / (n : ℝ)) *
        (∫⁻ x, A x ∂μ) ^ (1 / (n : ℝ)) := by
  let p : ℝ := ((n : ℝ) - 1) / (n : ℝ)
  let q : ℝ := 1 / (n : ℝ)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnOneR : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hp : 0 ≤ p := by
    dsimp [p]
    exact (div_pos (sub_pos.mpr hnOneR) hnR).le
  have hq : 0 ≤ q := by
    dsimp [q]
    positivity
  have hpq : p + q = 1 := by
    dsimp [p, q]
    field_simp
    ring
  have heven : AEMeasurable (fun x ↦ A x * B x ^ n) μ :=
    hA.mul (hB.pow_const n)
  have hholder := ENNReal.lintegral_mul_norm_pow_le
    heven hA hp hq hpq
  change (∫⁻ x, A x * B x ^ (n - 1) ∂μ) ≤ _
  rw [show (∫⁻ x, A x * B x ^ (n - 1) ∂μ) =
      ∫⁻ x, (A x * B x ^ n) ^ p * A x ^ q ∂μ by
    apply lintegral_congr
    intro x
    exact (ford_ennreal_interpolation_point hn (A x) (B x)).symm]
  exact hholder

theorem ford_lintegral_weighted_interpolation_pow
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {A B : α → ENNReal} (hA : AEMeasurable A μ) (hB : AEMeasurable B μ)
    {n : ℕ} (hn : 2 ≤ n) :
    (∫⁻ x, A x * B x ^ (n - 1) ∂μ) ^ n ≤
      (∫⁻ x, A x * B x ^ n ∂μ) ^ (n - 1) *
        ∫⁻ x, A x ∂μ := by
  let O := ∫⁻ x, A x * B x ^ (n - 1) ∂μ
  let S := ∫⁻ x, A x * B x ^ n ∂μ
  let I := ∫⁻ x, A x ∂μ
  let p : ℝ := ((n : ℝ) - 1) / (n : ℝ)
  let q : ℝ := 1 / (n : ℝ)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hp : 0 ≤ p := by
    dsimp [p]
    exact (div_pos (sub_pos.mpr (by exact_mod_cast (by omega : 1 < n))) hnR).le
  have hq : 0 ≤ q := by
    dsimp [q]
    positivity
  have hnp : (n : ℝ) * p = (n : ℝ) - 1 := by
    dsimp [p]
    field_simp
  have hnq : (n : ℝ) * q = 1 := by
    dsimp [q]
    field_simp
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  have hinterp : O ≤ S ^ p * I ^ q :=
    ford_lintegral_weighted_interpolation hA hB hn
  calc
    O ^ n = O ^ (n : ℝ) := by rw [ENNReal.rpow_natCast]
    _ ≤ (S ^ p * I ^ q) ^ (n : ℝ) :=
      ENNReal.rpow_le_rpow hinterp (by positivity)
    _ = (S ^ p) ^ (n : ℝ) * (I ^ q) ^ (n : ℝ) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
    _ = S ^ (n - 1) * I := by
      rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      rw [mul_comm p, hnp, mul_comm q, hnq, ← hcast,
        ENNReal.rpow_natCast, ENNReal.rpow_one]

#print axioms ford_ennreal_interpolation_point
#print axioms ford_lintegral_weighted_interpolation
#print axioms ford_lintegral_weighted_interpolation_pow

end

end GafniTao
