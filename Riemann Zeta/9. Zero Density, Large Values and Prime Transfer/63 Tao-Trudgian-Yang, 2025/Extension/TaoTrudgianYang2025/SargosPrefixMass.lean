import TaoTrudgianYang2025.SargosPrefixKernelBound
import Mathlib.NumberTheory.Harmonic.Bounds

/-! The total mass of the prefix-independent Fourier majorant is logarithmic. -/

noncomputable section

open scoped BigOperators

namespace TaoTrudgianYang2025

theorem sargos_sum_zmod_val {N : ℕ} [NeZero N] (g : ℕ → ℝ) :
    (∑ k : ZMod N, g k.val) = ∑ j ∈ Finset.range N, g j := by
  refine Finset.sum_bij (fun k _ => k.val) ?_ ?_ ?_ ?_
  · intro k hk
    exact Finset.mem_range.mpr (ZMod.val_lt k)
  · intro k hk l hl he
    exact ZMod.val_injective N he
  · intro j hj
    exact ⟨(j : ZMod N),Finset.mem_univ _,
      ZMod.val_cast_of_lt (Finset.mem_range.mp hj)⟩
  · intro k hk
    rfl

theorem sargos_sum_range_inv_le_harmonic (N : ℕ) :
    (∑ j ∈ Finset.range N, (j : ℝ)⁻¹) ≤ (harmonic N : ℝ) := by
  calc
    _ ≤ ∑ j ∈ Finset.range (N+1), (j : ℝ)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (Nat.le_succ N)) (fun _ _ _ => by positivity)
    _ = _ := by
      rw [Finset.sum_range_succ']
      simp [harmonic]

theorem sum_sargosPrefixMajorant_eq {N : ℕ} [NeZero N] :
    (∑ k : ZMod N, sargosPrefixMajorant k) =
      1+2*(∑ j ∈ Finset.range N, (j : ℝ)⁻¹) := by
  have hn : (∑ k : ZMod N, ((-k).val : ℝ)⁻¹) =
      ∑ k : ZMod N, (k.val : ℝ)⁻¹ := by
    exact Fintype.sum_equiv (Equiv.neg (ZMod N)) _ _ (fun k => by rfl)
  unfold sargosPrefixMajorant
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,hn]
  simp_rw [sargos_sum_zmod_val (fun j => (j : ℝ)⁻¹)]
  simp
  ring

theorem sum_sargosPrefixMajorant_le_harmonic {N : ℕ} [NeZero N] :
    (∑ k : ZMod N, sargosPrefixMajorant k) ≤ 1+2*(harmonic N : ℝ) := by
  rw [sum_sargosPrefixMajorant_eq]
  linarith [sargos_sum_range_inv_le_harmonic N]

theorem sum_sargosPrefixMajorant_le_log {N : ℕ} [NeZero N] :
    (∑ k : ZMod N, sargosPrefixMajorant k) ≤ 3*(1+Real.log N) := by
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hlog := Real.log_nonneg hN
  have h := sum_sargosPrefixMajorant_le_harmonic (N := N)
  have hh := harmonic_le_one_add_log N
  linarith

end TaoTrudgianYang2025
