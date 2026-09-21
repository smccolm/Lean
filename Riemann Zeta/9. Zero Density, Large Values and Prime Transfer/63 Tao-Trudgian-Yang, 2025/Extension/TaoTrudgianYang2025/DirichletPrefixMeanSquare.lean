import TaoTrudgianYang2025.DirichletPrefixBlocks

/-!
# Complete-prefix mean square from the actual dyadic blocks

The finite coefficient hypotheses are stated explicitly and will be
discharged for the ordinary divisor coefficients in the zeta source.
The interval may be translated arbitrarily; no height-center cost occurs.
-/

noncomputable section

open Complex MeasureTheory
open scoped Interval
open RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

theorem integral_norm_sq_dirichletPrefix_le_blocks
    (M : ℕ) (a : ℕ → ℂ) {A B : ℝ} (hAB : A ≤ B) :
    (∫ t : ℝ in A..B, ‖dirichletPrefix (2^M) a t‖^2) ≤
      2*((M:ℝ)+1)*((B-A)*‖a 1‖^2+
        ∑ j ∈ Finset.range M, ∫ t : ℝ in A..B, ‖dirichletTime (2^j) a t‖^2) := by
  have hi (j : ℕ) : IntervalIntegrable
      (fun t : ℝ => ‖dirichletTime (2^j) a t‖^2) volume A B :=
    ((continuous_dirichletTime (2^j) a).norm.pow 2).intervalIntegrable A B
  have hsum : IntervalIntegrable
      (fun t : ℝ => ∑ j ∈ Finset.range M, ‖dirichletTime (2^j) a t‖^2) volume A B := by
    convert IntervalIntegrable.sum (Finset.range M) (fun j _ => hi j) using 1
    ext t
    simp
  have hconst : IntervalIntegrable (fun _ : ℝ => ‖a 1‖^2) volume A B :=
    intervalIntegrable_const
  calc
    _ ≤ ∫ t : ℝ in A..B,
        2*((M:ℝ)+1)*(‖a 1‖^2+
          ∑ j ∈ Finset.range M, ‖dirichletTime (2^j) a t‖^2) :=
      intervalIntegral.integral_mono_on hAB
        (((continuous_dirichletPrefix (2^M) a).norm.pow 2).intervalIntegrable A B)
        ((hconst.add hsum).const_mul _)
        (fun t _ => norm_dirichletPrefix_pow_two_sq_le M a t)
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add hconst hsum,
        intervalIntegral.integral_const,
        intervalIntegral.integral_finsetSum (fun j _ => hi j)]
      rfl

theorem integral_norm_sq_dirichletPrefix_le
    (M : ℕ) (a : ℕ → ℂ) {A B L : ℝ} (hAB : A ≤ B)
    (hone : ‖a 1‖^2 ≤ L)
    (hcoeff : ∀ j ∈ Finset.range M,
      (∑ n ∈ Finset.Ioc (2^j) (2*(2^j)), ‖a n‖^2) ≤ L) :
    (∫ t : ℝ in A..B, ‖dirichletPrefix (2^M) a t‖^2) ≤
      2*((M:ℝ)+1)^2*(B-A+2*(5*Real.pi+1)*(2:ℝ)^M)*L := by
  have hL : 0 ≤ L := (sq_nonneg ‖a 1‖).trans hone
  have hT : 0 ≤ B-A := sub_nonneg.mpr hAB
  let E : ℝ := (B-A+2*(5*Real.pi+1)*(2:ℝ)^M)*L
  have hfirst : (B-A)*‖a 1‖^2 ≤ E := by
    dsimp [E]
    apply mul_le_mul (le_add_of_nonneg_right (by positivity)) hone (sq_nonneg _)
    positivity
  have hblock : ∀ j ∈ Finset.range M,
      (∫ t : ℝ in A..B, ‖dirichletTime (2^j) a t‖^2) ≤ E := by
    intro j hj
    have hjM : j ≤ M := (Finset.mem_range.mp hj).le
    have hp : ((2^j:ℕ):ℝ) ≤ (2:ℝ)^M := by
      norm_cast
      exact pow_le_pow_right₀ (by decide : (1:ℕ) ≤ 2) hjM
    apply (integral_norm_sq_dirichletTime_interval_le (2^j) a
      (by positivity) hAB).trans
    dsimp [E]
    apply mul_le_mul (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hp (by positivity)))
      (hcoeff j hj) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    positivity
  have hsum : (∑ j ∈ Finset.range M,
      ∫ t : ℝ in A..B, ‖dirichletTime (2^j) a t‖^2) ≤ (M:ℝ)*E := by
    simpa using Finset.sum_le_sum hblock
  calc
    _ ≤ 2*((M:ℝ)+1)*((B-A)*‖a 1‖^2+
        ∑ j ∈ Finset.range M, ∫ t : ℝ in A..B, ‖dirichletTime (2^j) a t‖^2) :=
      integral_norm_sq_dirichletPrefix_le_blocks M a hAB
    _ ≤ 2*((M:ℝ)+1)*((M:ℝ)+1)*E := by
      rw [mul_assoc (2*((M:ℝ)+1))]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith
    _ = _ := by dsimp [E]; ring

theorem integral_norm_sq_dirichletPrefix_reflected_le
    (M : ℕ) (a : ℕ → ℂ) (u : ℝ) {H L : ℝ} (hH : 0 ≤ H)
    (hone : ‖a 1‖^2 ≤ L)
    (hcoeff : ∀ j ∈ Finset.range M,
      (∑ n ∈ Finset.Ioc (2^j) (2*(2^j)), ‖a n‖^2) ≤ L) :
    (∫ t : ℝ in H..2*H, ‖dirichletPrefix (2^M) a (u-t)‖^2) ≤
      2*((M:ℝ)+1)^2*(H+2*(5*Real.pi+1)*(2:ℝ)^M)*L := by
  rw [intervalIntegral.integral_comp_sub_left
    (fun t : ℝ => ‖dirichletPrefix (2^M) a t‖^2) u]
  have h := integral_norm_sq_dirichletPrefix_le M a
    (show u-2*H ≤ u-H by linarith) hone hcoeff
  have heq : u-H-(u-2*H) = H := by ring
  simpa only [heq] using h

end TaoTrudgianYang2025
