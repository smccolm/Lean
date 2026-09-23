import TaoTrudgianYang2025.SargosCharacterGap

/-! Prefix-independent geometric majorants for finite Fourier completion. -/

noncomputable section

open scoped BigOperators

namespace TaoTrudgianYang2025

def sargosResidueDistance {N : ℕ} [NeZero N] (k : ZMod N) : ℝ :=
  min (k.val : ℝ) ((N : ℝ)-k.val)

def sargosPrefixMajorant {N : ℕ} [NeZero N] (k : ZMod N) : ℝ :=
  (if k = 0 then 1 else 0)+(k.val : ℝ)⁻¹+((-k).val : ℝ)⁻¹

theorem sargosResidueDistance_pos {N : ℕ} [NeZero N] {k : ZMod N} (hk : k ≠ 0) :
    0 < sargosResidueDistance k := by
  unfold sargosResidueDistance
  apply lt_min
  · exact_mod_cast ZMod.val_pos.mpr hk
  · exact sub_pos.mpr (by exact_mod_cast ZMod.val_lt k)

theorem sargos_stdAddChar_sub_one_lower {N : ℕ} [NeZero N] (k : ZMod N) :
    4*sargosResidueDistance k/(N : ℝ) ≤ ‖ZMod.stdAddChar k-1‖ := by
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hv : (k.val : ℝ) ≤ N := by exact_mod_cast (ZMod.val_lt k).le
  have hs := sargos_sin_pi_lower (t := (k.val : ℝ)/(N : ℝ))
    (by positivity) ((div_le_one hN).mpr hv)
  have he : 1-(k.val : ℝ)/(N : ℝ) = ((N : ℝ)-k.val)/(N : ℝ) := by
    field_simp
  rw [he,min_div_div_right hN.le] at hs
  rw [sargos_stdAddChar_sub_one_norm]
  have harg : Real.pi*((k.val : ℝ)/(N : ℝ)) =
      Real.pi*(k.val : ℝ)/(N : ℝ) := by ring
  rw [harg] at hs
  unfold sargosResidueDistance
  calc
    _ = 2*(2*(min (k.val : ℝ) ((N : ℝ)-k.val)/(N : ℝ))) := by ring
    _ ≤ 2*Real.sin (Real.pi*(k.val : ℝ)/(N : ℝ)) :=
      mul_le_mul_of_nonneg_left hs (by norm_num)
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num)

theorem sargos_geometric_kernel_product_le_two {N : ℕ} [NeZero N]
    (H : ℕ) (k : ZMod N) :
    ‖∑ j ∈ Finset.range H, ZMod.stdAddChar (k*(j : ZMod N))‖*
      ‖ZMod.stdAddChar k-1‖ ≤ 2 := by
  rw [← norm_mul,sargos_sum_stdAddChar_mul_sub_one]
  calc
    _ ≤ ‖(ZMod.stdAddChar k)^H‖+‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow,sargos_stdAddChar_norm]; norm_num

theorem norm_sargosPrefixKernel_le_inv_distance {N : ℕ} [NeZero N]
    (H : ℕ) {k : ZMod N} (hk : k ≠ 0) :
    ‖sargosPrefixKernel H k‖ ≤ 1/sargosResidueDistance k := by
  have hd := sargosResidueDistance_pos hk
  have hK : ‖sargosPrefixKernel H k‖ =
      ‖∑ j ∈ Finset.range H, ZMod.stdAddChar (k*(j : ZMod N))‖/(N : ℝ) := by
    rw [sargosPrefixKernel,norm_mul,norm_inv,Complex.norm_natCast]
    ring
  have hprod : ‖sargosPrefixKernel H k‖*(4*sargosResidueDistance k) ≤ 2 := by
    calc
      _ = ‖∑ j ∈ Finset.range H, ZMod.stdAddChar (k*(j : ZMod N))‖*
          (4*sargosResidueDistance k/(N : ℝ)) := by rw [hK]; ring
      _ ≤ ‖∑ j ∈ Finset.range H, ZMod.stdAddChar (k*(j : ZMod N))‖*
          ‖ZMod.stdAddChar k-1‖ :=
        mul_le_mul_of_nonneg_left (sargos_stdAddChar_sub_one_lower k) (norm_nonneg _)
      _ ≤ 2 := sargos_geometric_kernel_product_le_two H k
  apply (le_div_iff₀ hd).mpr
  nlinarith

theorem sargosPrefixMajorant_nonneg {N : ℕ} [NeZero N] (k : ZMod N) :
    0 ≤ sargosPrefixMajorant k := by
  unfold sargosPrefixMajorant
  positivity

theorem norm_sargosPrefixKernel_le_majorant {N H : ℕ} [NeZero N]
    (hH : H ≤ N) (k : ZMod N) :
    ‖sargosPrefixKernel H k‖ ≤ sargosPrefixMajorant k := by
  by_cases hk : k = 0
  · subst k
    simpa [sargosPrefixMajorant] using norm_sargosPrefixKernel_zero_le_one hH
  · have h := norm_sargosPrefixKernel_le_inv_distance H hk
    rw [sargosPrefixMajorant,if_neg hk,zero_add,ZMod.neg_val,if_neg hk,
      Nat.cast_sub (ZMod.val_lt k).le]
    unfold sargosResidueDistance at h
    by_cases hd : (k.val : ℝ) ≤ (N : ℝ)-k.val
    · rw [min_eq_left hd,one_div] at h
      exact h.trans (le_add_of_nonneg_right (inv_nonneg.mpr
        (sub_nonneg.mpr (by exact_mod_cast (ZMod.val_lt k).le))))
    · rw [min_eq_right (le_of_not_ge hd),one_div] at h
      exact h.trans (le_add_of_nonneg_left (inv_nonneg.mpr (Nat.cast_nonneg _)))

end TaoTrudgianYang2025
