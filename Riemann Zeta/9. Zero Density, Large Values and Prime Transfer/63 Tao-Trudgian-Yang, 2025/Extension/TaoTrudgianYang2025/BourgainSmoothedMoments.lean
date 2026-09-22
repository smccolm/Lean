import TaoTrudgianYang2025.BourgainSmoothedPolynomial
import TaoTrudgianYang2025.PointMeanExponentialOverlap
import TaoTrudgianYang2025.FiniteOccupancy

/-!
# Summing the pole term on separated ordinates

Distance-shell occupancy gives a uniform reciprocal-square overlap bound.
It turns the retained moving-pole sum into L times the actual cardinality.
The zeta-square term is left intact for Bourgain's subsequent level selection.
-/

open Complex Finset MeasureTheory Set
open RiemannZeta.GuthMaynard

noncomputable section

namespace TaoTrudgianYang2025

/-- Uniform reciprocal-square overlap on every unit-separated finite set. -/
theorem bourgain_sum_reciprocal_sq_le_four (W : Finset ℝ) (x : ℝ)
    (hsep : IsSeparated 1 W) :
    (∑ u ∈ W, 1/(1+|u-x|)^2) ≤ 4 := by
  let shell : ℝ → ℕ := fun u => Nat.floor |u-x|
  let S : Finset ℕ := W.image shell
  have hsum : (∑ k ∈ S, (((k : ℝ)+1)^2)⁻¹) ≤ 2 := by
    calc
      _ = ∑ m ∈ S.image (fun k : ℕ => (k+1 : ℕ)), ((m : ℝ)^2)⁻¹ := by
        rw [Finset.sum_image (fun a _ b _ hab => Nat.add_right_cancel hab)]
        simp only [Nat.cast_add, Nat.cast_one]
      _ ≤ ∑ m ∈ Finset.Icc 1 (S.sup (fun k => k+1)), ((m : ℝ)^2)⁻¹ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro m hm
          obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hm
          exact Finset.mem_Icc.mpr ⟨by omega, Finset.le_sup hk⟩
        · intro m hm hn
          positivity
      _ ≤ 2 := sum_pos_nat_inv_sq_le_two _
  calc
    _ ≤ ∑ u ∈ W, (((shell u : ℝ)+1)^2)⁻¹ := by
      apply Finset.sum_le_sum
      intro u hu
      have hf := Nat.floor_le (abs_nonneg (u-x))
      rw [← one_div (((shell u : ℝ)+1)^2)]
      apply one_div_le_one_div_of_le (by positivity : 0 < ((shell u : ℝ)+1)^2)
      exact pow_le_pow_left₀ (by positivity)
        (show (shell u : ℝ)+1 ≤ 1+|u-x| by dsimp [shell]; linarith) 2
    _ = ∑ k ∈ S, ∑ u ∈ W with shell u = k, (((shell u : ℝ)+1)^2)⁻¹ := by
      symm
      exact Finset.sum_fiberwise_of_maps_to (fun u hu => Finset.mem_image.mpr ⟨u,hu,rfl⟩) _
    _ ≤ ∑ k ∈ S, 2*(((k : ℝ)+1)^2)⁻¹ := by
      apply Finset.sum_le_sum
      intro k hk
      have hcard : ((W.filter (fun u => shell u = k)).card : ℝ) ≤ 2 := by
        exact_mod_cast separated_distance_shell_card_le_two W x k hsep
      calc
        _ = ((W.filter (fun u => shell u = k)).card : ℝ)*(((k : ℝ)+1)^2)⁻¹ := by
          calc
            _ = ∑ _u ∈ W.filter (fun u => shell u = k), (((k : ℝ)+1)^2)⁻¹ := by
              apply Finset.sum_congr rfl
              intro u hu
              rw [(Finset.mem_filter.mp hu).2]
            _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 2*∑ k ∈ S, (((k : ℝ)+1)^2)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ 4 := by linarith

/-- Any larger even decay order has the same overlap constant. -/
theorem bourgain_sum_reciprocal_pow_le_four (W : Finset ℝ) (x : ℝ)
    (hsep : IsSeparated 1 W) {q : ℕ} (hq : 0 < q) :
    (∑ u ∈ W, 1/(1+|u-x|)^(2*q)) ≤ 4 := by
  apply le_trans _ (bourgain_sum_reciprocal_sq_le_four W x hsep)
  apply Finset.sum_le_sum
  intro u hu
  apply one_div_le_one_div_of_le (by positivity : 0 < (1+|u-x|)^2)
  exact pow_le_pow_right₀ (by linarith [abs_nonneg (u-x)] : 1 ≤ 1+|u-x|) (by omega)

/-- The pole sum over all ordered pairs is at most four times the actual
number of ordinates, with no cardinality-squared diagonal loss. -/
theorem bourgain_pair_reciprocal_pow_le (W : Finset ℝ)
    (hsep : IsSeparated 1 W) {q : ℕ} (hq : 0 < q) :
    (∑ t ∈ W, ∑ v ∈ W, 1/(1+|t-v|)^(2*q)) ≤ 4*(W.card : ℝ) := by
  calc
    _ ≤ ∑ t ∈ W, (4 : ℝ) := by
      apply Finset.sum_le_sum
      intro t ht
      simpa only [abs_sub_comm t] using bourgain_sum_reciprocal_pow_le_four W t hsep hq
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

/-- Complete separated smooth-polynomial moment, retaining the actual
integer zeta-square moment and an explicit, arbitrarily decaying tail. -/
theorem bourgainSmoothedCriticalPolynomial_separated_moment {q : ℕ} (hq : 0 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 0 < L →
      ∀ (W : Finset ℝ) (T H : ℝ), 0 ≤ T → 0 ≤ H →
      IsSeparated 1 W → InBaseInterval T W →
      (∑ t ∈ W, ∑ v ∈ W, ‖bourgainSmoothedCriticalPolynomial L (t-v)‖^2) ≤
        C*(L*(W.card : ℝ) + H*bourgainZetaDifferenceMoment W (H+1) +
          (W.card : ℝ)^2*(1+T)^2/(1+H)^(2*q)) := by
  obtain ⟨A,hA,hbound⟩ := bourgainSmoothedCriticalPolynomial_pair_moment q
  refine ⟨4*A, by positivity, ?_⟩
  intro L hL W T H hT hH hsep hbase
  have hp := bourgain_pair_reciprocal_pow_le W hsep hq
  have hm : 0 ≤ bourgainZetaDifferenceMoment W (H+1) := by
    unfold bourgainZetaDifferenceMoment
    exact Finset.sum_nonneg (fun ℓ _ =>
      mul_nonneg (Nat.cast_nonneg _) (bourgainLocalZetaSquare_nonneg (by linarith) ℓ))
  have ht : 0 ≤ (W.card : ℝ)^2*(1+T)^2/(1+H)^(2*q) := by positivity
  have hlocal : 0 ≤ H*bourgainZetaDifferenceMoment W (H+1) := mul_nonneg hH hm
  have hraw := hbound L hL W T H hT hH hbase
  have hscaled := mul_le_mul_of_nonneg_left hp hL.le
  nlinarith [mul_nonneg hA.le hlocal, mul_nonneg hA.le ht,
    mul_le_mul_of_nonneg_left hscaled hA.le]

end TaoTrudgianYang2025
