import TaoTrudgianYang2025.BourgainReflectionIntegrals
import TaoTrudgianYang2025.JutilaTraceBins

/-!
# Actual trace-bin moments with retained zeta integrals

The full native reflection is consumed at the real displacement scale.
The Mellin truncation, omitted frequencies and zero-mode errors remain
visible beside the proved retained-zeta main term.
-/

open Complex Finset MeasureTheory
open scoped BigOperators Interval
open RiemannZeta.GuthMaynard

noncomputable section

namespace TaoTrudgianYang2025

/-- The actual retained main term and all three native reflection errors. -/
def bourgainTraceBinMajorant (q k Q M j : ℕ) (T H : ℝ) (W : Finset ℝ)
    (A C K L D η : ℝ) : ℝ :=
  (2 : ℝ) ^ (2*k-1) *
    (((Q : ℝ) * C / Real.sqrt ((2 ^ j : ℕ) : ℝ)) ^ (2*k) *
        ((2*H) ^ (2*k) * bourgainPrefixMomentMajorant q k M T H W A η) +
      ((heathBrownDifferenceBin W j).card : ℝ) *
        (heathBrownReflectionBinError q Q M H
          ((2 ^ (j+1) : ℕ) : ℝ) ((2 ^ j : ℕ) : ℝ) K L D) ^ (2*k))

/-- Complete reflected trace moment on a genuine displacement bin. -/
theorem bourgain_trace_bin_moment_retained (cutoff : GMSmoothCutoff)
    (q k : ℕ) (hq : 2 ≤ q) (hk : 0 < k)
    {η : ℝ} (hη : 0 < η) :
    ∃ A C K L D : ℝ,
      0 < A ∧ 0 < C ∧ 0 < K ∧ 0 < L ∧ 0 < D ∧
      ∀ (Q M j : ℕ) (T H : ℝ) (W : Finset ℝ),
        0 < Q → 0 < M → 2 ≤ j → 0 ≤ T → 1 ≤ H →
        H ≤ ((2 ^ j : ℕ) : ℝ) / 2 →
        IsSeparated 1 W → InBaseInterval T W →
        (∑ p ∈ heathBrownDifferenceBin W j,
          ‖heathBrownTracePolynomial cutoff Q (p.1-p.2)‖ ^ (2*k)) ≤
          bourgainTraceBinMajorant q k Q M j T H W A C K L D η := by
  obtain ⟨C, K, L, D, hC, hK, hL, hD, hReflect⟩ :=
    heathBrownTracePolynomial_reflection_with_length cutoff q hq
  obtain ⟨A, hA, hIntegral⟩ :=
    bourgain_reflected_bin_integral_moment_retained k hk (by omega : 0 < q) hη
  refine ⟨A, C, K, L, D, hA, hC, hK, hL, hD, ?_⟩
  intro Q M j T H W hQ hM hj hT hH hHupper hsep hbase
  let S : ℝ := (2 ^ j : ℕ)
  let U : ℝ := (2 ^ (j+1) : ℕ)
  let F : ℝ := (Q : ℝ) * C / Real.sqrt S
  let E : ℝ := heathBrownReflectionBinError q Q M H U S K L D
  have hS : 4 ≤ S := by
    have hn : 2 ^ 2 ≤ (2 : ℕ) ^ j := Nat.pow_le_pow_right (by omega) hj
    dsimp [S]
    exact_mod_cast hn
  have hH0 : 0 ≤ H := le_trans zero_le_one hH
  have hpoint (p : ℝ × ℝ) (hp : p ∈ heathBrownDifferenceBin W j) :
      ‖heathBrownTracePolynomial cutoff Q (p.1-p.2)‖ ≤
        F * (∫ u in -H..H, ‖gmReflectionDirichletPoly (p.1-p.2) M u‖) + E := by
    have hb := heathBrownDifferenceBin_bounds hsep hp
    have hr := hReflect hS hb.1 hH hHupper hQ hM
    have hfreq :
        (Q : ℝ) * L * (1 + |p.1-p.2|) ^ (q+2) /
            ((Q : ℝ) ^ (q+2) * (M : ℝ) ^ q) ≤
          (Q : ℝ) * L * (1 + U) ^ (q+2) /
            ((Q : ℝ) ^ (q+2) * (M : ℝ) ^ q) := by
      gcongr
      exact hb.2.le
    dsimp [F, E, heathBrownReflectionBinError]
    dsimp [S, U] at *
    linarith
  have hpower (p : ℝ × ℝ) (hp : p ∈ heathBrownDifferenceBin W j) :
      ‖heathBrownTracePolynomial cutoff Q (p.1-p.2)‖ ^ (2*k) ≤
        (2 : ℝ) ^ (2*k-1) *
          (F ^ (2*k) * (∫ u in -H..H, ‖gmReflectionDirichletPoly (p.1-p.2) M u‖) ^ (2*k) +
            E ^ (2*k)) := by
    calc
      _ ≤ (F * (∫ u in -H..H, ‖gmReflectionDirichletPoly (p.1-p.2) M u‖) + E) ^ (2*k) :=
        pow_le_pow_left₀ (norm_nonneg _) (hpoint p hp) _
      _ ≤ _ := by
        simpa only [mul_pow] using (even_two_mul k).add_pow_le
          (a := F * (∫ u in -H..H, ‖gmReflectionDirichletPoly (p.1-p.2) M u‖)) (b := E)
  have hint := hIntegral M T H W j hM hT hH0 hsep hbase
  change _ ≤ (2*H) ^ (2*k) * bourgainPrefixMomentMajorant q k M T H W A η at hint
  have hsum := Finset.sum_le_sum hpower
  have heq :
      (∑ p ∈ heathBrownDifferenceBin W j,
        (2 : ℝ) ^ (2*k-1) *
          (F ^ (2*k) * (∫ u in -H..H, ‖gmReflectionDirichletPoly (p.1-p.2) M u‖) ^ (2*k) +
            E ^ (2*k))) =
      (2 : ℝ) ^ (2*k-1) *
        (F ^ (2*k) * (∑ p ∈ heathBrownDifferenceBin W j,
          (∫ u in -H..H, ‖gmReflectionDirichletPoly (p.1-p.2) M u‖) ^ (2*k)) +
            ((heathBrownDifferenceBin W j).card : ℝ) * E ^ (2*k)) := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_const, nsmul_eq_mul]
  rw [heq] at hsum
  apply hsum.trans
  change _ ≤ (2 : ℝ) ^ (2*k-1) *
    (F ^ (2*k) * ((2*H) ^ (2*k) * bourgainPrefixMomentMajorant q k M T H W A η) +
      ((heathBrownDifferenceBin W j).card : ℝ) * E ^ (2*k))
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add (mul_le_mul_of_nonneg_left hint (by dsimp [F]; positivity)) le_rfl


end TaoTrudgianYang2025
