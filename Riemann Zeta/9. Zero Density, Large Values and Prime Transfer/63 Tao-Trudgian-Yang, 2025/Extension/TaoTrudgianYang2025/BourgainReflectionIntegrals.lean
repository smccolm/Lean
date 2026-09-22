import TaoTrudgianYang2025.BourgainPrefixMoments
import TaoTrudgianYang2025.JutilaReflectionIntegrals

/-!
# Integrating the actual retained-prefix moment on displacement bins

The positive-kernel majorant was applied on the full ordered-pair set.
Restriction to an actual bin uses only nonnegativity. Interval Holder
then integrates the real reflected polynomial, uniformly in its shift.
-/

open Complex Finset MeasureTheory
open scoped BigOperators Interval
open RiemannZeta.GuthMaynard

noncomputable section

namespace TaoTrudgianYang2025

/-- Notation for the proved, scale-faithful retained-prefix bound. -/
def bourgainPrefixMomentMajorant (q k M : ℕ) (T H : ℝ)
    (W : Finset ℝ) (A η : ℝ) : ℝ :=
  A*((Nat.clog 2 M : ℝ)+1)^(2*k)*(2^k*M^k : ℕ)*
    (((2^k*M^k : ℕ) : ℝ)^η)^2*bourgainMomentBudget q (2^k*M^k : ℕ) T H W

/-- The full reflected integral moment on every actual displacement bin. -/
theorem bourgain_reflected_bin_integral_moment_retained (k : ℕ) (hk : 0 < k)
    {q : ℕ} (hq : 0 < q) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ℕ) (T H : ℝ) (W : Finset ℝ) (j : ℕ),
        0 < M → 0 ≤ T → 0 ≤ H → IsSeparated 1 W → InBaseInterval T W →
        (∑ p ∈ heathBrownDifferenceBin W j,
          (∫ u in -H..H, ‖gmReflectionDirichletPoly (p.1-p.2) M u‖)^(2*k)) ≤
            (2*H)^(2*k)*bourgainPrefixMomentMajorant q k M T H W C η := by
  obtain ⟨C,hC,hm⟩ := bourgain_reflected_prefix_moment_retained k hk hq hη
  refine ⟨C,hC,?_⟩
  intro M T H W j hM hT hH hsep hbase
  let B : ℝ := bourgainPrefixMomentMajorant q k M T H W C η
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
      _ ≤ B := hm M T H W u hM hT hH hsep hbase
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
