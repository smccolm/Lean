import GafniTao.WooleyWeightedHolder

/-!
# Complex finite-sum form of Wooley's Hölder step

This is the precise inequality applied to the residue-class decomposition
immediately before equation (3.9).
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem wooley_weighted_complex_sum_pow_le
    {ι : Type*} (t : Finset ι) (w : ι → ℝ) (z : ι → ℂ)
    {s : ℕ} (hs : 1 ≤ s) (hw : ∀ i, 0 ≤ w i) :
    ‖∑ i ∈ t, (Real.sqrt (w i) : ℂ) * z i‖ ^ (2 * s) ≤
      (#t : ℝ) ^ s * (∑ i ∈ t, w i) ^ (s - 1) *
        ∑ i ∈ t, w i * ‖z i‖ ^ (2 * s) := by
  let A : ℝ := ∑ i ∈ t, Real.sqrt (w i) * ‖z i‖
  let D : ℝ := ∑ i ∈ t, w i * ‖z i‖ ^ 2
  have hnorm :
      ‖∑ i ∈ t, (Real.sqrt (w i) : ℂ) * z i‖ ≤ A := by
    calc
      ‖∑ i ∈ t, (Real.sqrt (w i) : ℂ) * z i‖ ≤
          ∑ i ∈ t, ‖(Real.sqrt (w i) : ℂ) * z i‖ :=
        norm_sum_le _ _
      _ = A := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hA : 0 ≤ A := by
    dsimp [A]
    exact Finset.sum_nonneg fun i hi =>
      mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hD : 0 ≤ D := by
    dsimp [D]
    exact Finset.sum_nonneg fun i hi =>
      mul_nonneg (hw i) (sq_nonneg _)
  have hCauchy : A ^ 2 ≤ (#t : ℝ) * D := by
    have h := sum_mul_sq_le_sq_mul_sq (R := ℝ) t
      (fun _ : ι => 1)
      (fun i => Real.sqrt (w i) * ‖z i‖)
    simpa only [A, D, one_mul, one_pow, sum_const, nsmul_eq_mul,
      Nat.cast_ofNat, Nat.cast_card, mul_one, mul_pow,
      Real.sq_sqrt (hw _)] using h
  have hBase :
      ‖∑ i ∈ t, (Real.sqrt (w i) : ℂ) * z i‖ ^ 2 ≤
        (#t : ℝ) * D :=
    (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans hCauchy
  have hPower := pow_le_pow_left₀ (by positivity) hBase s
  have hWeighted := wooley_weighted_rpow_sum_le t w
    (fun i => ‖z i‖ ^ 2) (p := (s : ℝ))
    (by exact_mod_cast hs) hw (fun i => sq_nonneg _)
  have hWeightedNat :
      D ^ s ≤ (∑ i ∈ t, w i) ^ (s - 1) *
        ∑ i ∈ t, w i * ‖z i‖ ^ (2 * s) := by
    have hexponent : (s : ℝ) - 1 = ((s - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hs]
      norm_num
    calc
      D ^ s = D ^ (s : ℝ) := by rw [Real.rpow_natCast]
      _ ≤ (∑ i ∈ t, w i) ^ ((s : ℝ) - 1) *
          ∑ i ∈ t, w i * (‖z i‖ ^ 2) ^ (s : ℝ) := hWeighted
      _ = (∑ i ∈ t, w i) ^ (s - 1) *
          ∑ i ∈ t, w i * ‖z i‖ ^ (2 * s) := by
        rw [hexponent, Real.rpow_natCast]
        apply congrArg ((∑ i ∈ t, w i) ^ (s - 1) * ·)
        apply Finset.sum_congr rfl
        intro i hi
        rw [Real.rpow_natCast, ← pow_mul]
  calc
    ‖∑ i ∈ t, (Real.sqrt (w i) : ℂ) * z i‖ ^ (2 * s) =
        (‖∑ i ∈ t, (Real.sqrt (w i) : ℂ) * z i‖ ^ 2) ^ s := by
      rw [pow_mul]
    _ ≤ ((#t : ℝ) * D) ^ s := hPower
    _ = (#t : ℝ) ^ s * D ^ s := by rw [mul_pow]
    _ ≤ (#t : ℝ) ^ s *
        ((∑ i ∈ t, w i) ^ (s - 1) *
          ∑ i ∈ t, w i * ‖z i‖ ^ (2 * s)) := by
      gcongr
    _ = (#t : ℝ) ^ s * (∑ i ∈ t, w i) ^ (s - 1) *
        ∑ i ∈ t, w i * ‖z i‖ ^ (2 * s) := by ring

#print axioms wooley_weighted_complex_sum_pow_le

end

end GafniTao
