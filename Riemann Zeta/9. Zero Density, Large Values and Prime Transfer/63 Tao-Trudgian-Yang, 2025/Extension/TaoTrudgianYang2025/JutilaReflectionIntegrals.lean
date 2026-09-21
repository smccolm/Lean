import TaoTrudgianYang2025.JutilaPrefixMoments
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul

/-!
# Powered reflection integrals

Finite Jensen and interval Jensen are applied to the actual reflected
prefix. Constants remain uniform in the physical prefix length.
-/

open Complex Finset MeasureTheory Filter
open scoped BigOperators Interval
open RiemannZeta.GuthMaynard

noncomputable section

namespace TaoTrudgianYang2025

/-- Interval Hölder for a positive natural power, with the exact interval
length. This is Jensen for the normalized interval measure. -/
theorem jutila_intervalIntegral_pow_le (f : ℝ → ℝ) (H : ℝ) {p : ℕ}
    (hH : 0 ≤ H) (hp : 0 < p) (hf : Continuous f) (hf0 : ∀ u, 0 ≤ f u) :
    (∫ u in -H..H, f u) ^ p ≤
      (2*H) ^ (p-1) * ∫ u in -H..H, f u ^ p := by
  rcases eq_or_lt_of_le hH with hHz | hHp
  · subst H
    simp [hp.ne']
  have horder : -H ≤ H := by linarith
  have hlen : 0 < 2*H := by positivity
  have hμ0 : volume (Set.Ioc (-H) H) ≠ 0 := by
    rw [Real.volume_Ioc]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith))
  have hμtop : volume (Set.Ioc (-H) H) ≠ ⊤ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have hi : IntegrableOn f (Set.Ioc (-H) H) :=
    hf.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hpi : IntegrableOn (fun x => f x ^ p) (Set.Ioc (-H) H) :=
    (hf.pow p).continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hJ := (convexOn_pow (𝕜 := ℝ) p).map_set_average_le
    (continuous_id.pow p).continuousOn isClosed_Ici hμ0 hμtop
    (Eventually.of_forall hf0) hi hpi
  have hmeasure : volume.real (Set.Ioc (-H) H) = 2*H := by
    rw [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
    ring
  simp only [setAverage_eq, hmeasure, smul_eq_mul] at hJ
  rw [← intervalIntegral.integral_of_le horder,
    ← intervalIntegral.integral_of_le horder] at hJ
  simp only [← div_eq_inv_mul] at hJ
  rw [div_pow] at hJ
  have hmul := (div_le_div_iff₀ (pow_pos hlen p) hlen).mp hJ
  have hexp : (2*H) ^ p = (2*H) ^ (p-1) * (2*H) := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hexp] at hmul
  apply (mul_le_mul_iff_left₀ hlen).mp
  convert hmul using 1
  ring

/-- The exact reflected prefix satisfies interval Hölder for every 2k. -/
theorem jutila_reflected_prefix_integral_power_le (t : ℝ) (M k : ℕ)
    (H : ℝ) (hk : 0 < k) (hH : 0 ≤ H) :
    (∫ u in -H..H, ‖gmReflectionDirichletPoly t M u‖) ^ (2*k) ≤
      (2*H) ^ (2*k-1) *
        ∫ u in -H..H, ‖gmReflectionDirichletPoly t M u‖ ^ (2*k) :=
  jutila_intervalIntegral_pow_le _ H hH (by omega)
    (continuous_gmReflectionDirichletPoly t M).norm (fun _ => norm_nonneg _)

/-- Uniform 2k-th reflection-integral moment on every actual difference
bin. The majorant is applied to the full ordered-pair set before restricting
to a bin, so no false positivity principle for a restricted kernel is used. -/
theorem jutila_reflected_bin_integral_moment_uniform (k : ℕ) (hk : 0 < k)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
      ∀ (M : ℕ) (T H : ℝ) (W : Finset ℝ) (j : ℕ),
        0 < M → T₀ ≤ T → 0 ≤ H → IsSeparated 1 W → InBaseInterval T W →
        (∑ p ∈ heathBrownDifferenceBin W j,
          (∫ u in -H..H, ‖gmReflectionDirichletPoly (p.1-p.2) M u‖) ^ (2*k)) ≤
          (2*H) ^ (2*k) *
            (C * ((Nat.clog 2 M : ℝ) + 1) ^ (2*k) * (2 ^ k * M ^ k : ℕ) *
              (((2 ^ k * M ^ k : ℕ) : ℝ) ^ η) ^ 2 * T ^ ε *
              ((W.card : ℝ) ^ 2 + (W.card : ℝ) * (2 ^ k * M ^ k : ℕ) +
                (W.card : ℝ) ^ (5/4 : ℝ) * T ^ (1/2 : ℝ))) := by
  obtain ⟨C, T₀, hC, hT₀, hm⟩ := jutila_reflected_prefix_moment_uniform k hk hε hη
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro M T H W j hM hT hH hsep hbase
  let B : ℝ := C * ((Nat.clog 2 M : ℝ) + 1) ^ (2*k) * (2 ^ k * M ^ k : ℕ) *
    (((2 ^ k * M ^ k : ℕ) : ℝ) ^ η) ^ 2 * T ^ ε *
    ((W.card : ℝ) ^ 2 + (W.card : ℝ) * (2 ^ k * M ^ k : ℕ) +
      (W.card : ℝ) ^ (5/4 : ℝ) * T ^ (1/2 : ℝ))
  have hbin (u : ℝ) :
      (∑ p ∈ heathBrownDifferenceBin W j,
        ‖gmReflectionDirichletPoly (p.1-p.2) M u‖ ^ (2*k)) ≤ B := by
    calc
      _ ≤ ∑ p ∈ W ×ˢ W, ‖gmReflectionDirichletPoly (p.1-p.2) M u‖ ^ (2*k) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
        · intro p hp hpn
          positivity
      _ = ∑ t ∈ W, ∑ v ∈ W, ‖gmReflectionDirichletPoly (t-v) M u‖ ^ (2*k) := by
        rw [Finset.sum_product]
      _ ≤ B := hm M T W u hM hT hsep hbase
  calc
    _ ≤ ∑ p ∈ heathBrownDifferenceBin W j, (2*H) ^ (2*k-1) *
        ∫ u in -H..H, ‖gmReflectionDirichletPoly (p.1-p.2) M u‖ ^ (2*k) :=
      Finset.sum_le_sum fun p _ => jutila_reflected_prefix_integral_power_le
        (p.1-p.2) M k H hk hH
    _ = (2*H) ^ (2*k-1) * ∫ u in -H..H,
        ∑ p ∈ heathBrownDifferenceBin W j,
          ‖gmReflectionDirichletPoly (p.1-p.2) M u‖ ^ (2*k) := by
      rw [← Finset.mul_sum]
      congr 1
      symm
      apply intervalIntegral.integral_finsetSum
      intro p hp
      exact ((continuous_gmReflectionDirichletPoly (p.1-p.2) M).norm.pow (2*k))
        |>.intervalIntegrable _ _
    _ ≤ (2*H) ^ (2*k-1) * ∫ _u in -H..H, B := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply intervalIntegral.integral_mono_on
      · linarith
      · exact (continuous_finsetSum (heathBrownDifferenceBin W j) (fun p _ =>
          (continuous_gmReflectionDirichletPoly (p.1-p.2) M).norm.pow (2*k)))
          |>.intervalIntegrable _ _
      · exact continuous_const.intervalIntegrable _ _
      · intro u hu
        exact hbin u
    _ = (2*H) ^ (2*k) * B := by
      have hp : 2*k-1+1 = 2*k := by omega
      simp only [intervalIntegral.integral_const, smul_eq_mul]
      calc
        _ = ((2*H) ^ (2*k-1) * (2*H)) * B := by ring
        _ = _ := by rw [← pow_succ, hp]

end TaoTrudgianYang2025
