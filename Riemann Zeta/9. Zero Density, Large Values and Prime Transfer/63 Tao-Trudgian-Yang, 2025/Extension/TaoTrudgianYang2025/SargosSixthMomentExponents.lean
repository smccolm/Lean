import TaoTrudgianYang2025.SargosSixthOptimizedBootstrap

/-! Epsilon-quantified exponents for the actual base moment and their genuine improvement. -/

noncomputable section

namespace TaoTrudgianYang2025

def SargosSixthMomentExponent (β : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 1 ≤ B ∧
    ∀ N : ℕ, 1 ≤ N → sargosSixthBaseMoment N ≤ B*(N:ℝ)^(β+ε)

theorem sargosSixthMomentExponent_three : SargosSixthMomentExponent 3 := by
  intro ε hε
  refine ⟨2,by norm_num,?_⟩
  intro N hN
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN
  calc
    _ ≤ 2*(N:ℝ)^3 := sargosSixthBaseMoment_trivial hN
    _ = 2*(N:ℝ)^(3:ℝ) := by rw [show (3:ℝ) = (3:ℕ) by norm_num,Real.rpow_natCast]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hNr (by linarith only [hε])) (by norm_num)

theorem sargosSixthMomentExponent_step {β : ℝ} (hβ : 0 ≤ β)
    (h : SargosSixthMomentExponent β) :
    SargosSixthMomentExponent (sargosSixthExponentStep β) := by
  intro ε hε
  have hη : 0 < ε/2 := by positivity
  obtain ⟨B,hB,hbound⟩ := h (ε/2) hη
  obtain ⟨C,hC,hopt⟩ := sargosSixthBaseMoment_optimized_bootstrap
  let L : ℝ := (1+6/(ε/2))^6
  let D : ℝ := C*(4+B)*L
  have hDp : 0 < D := by dsimp [D,L]; positivity
  have hq := sargosSixthExponentStep_nonneg hβ
  have hqη := sargosSixthExponentStep_add_le hβ hη.le
  refine ⟨D+8193,by linarith only [hDp],?_⟩
  intro N hN
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0:ℝ) < N := by linarith only [hNr]
  have ht : 1 ≤ (N:ℝ)^(sargosSixthExponentStep β+ε) :=
    Real.one_le_rpow hNr (add_nonneg hq hε.le)
  by_cases hlarge : 16 ≤ N
  · have ho := hopt (β+ε/2) B (by linarith only [hβ,hη])
      (by linarith only [hB]) hbound N hlarge
    have hl := sargos_log_six_le_rpow hNr hη
    have he : (N:ℝ)^(ε/2)*(N:ℝ)^(sargosSixthExponentStep (β+ε/2)) =
        (N:ℝ)^(sargosSixthExponentStep (β+ε/2)+ε/2) := by
      rw [← Real.rpow_add hNp]
      congr 1
      ring
    have hpow := Real.rpow_le_rpow_of_exponent_le hNr
      (by linarith only [hqη] :
        sargosSixthExponentStep (β+ε/2)+ε/2 ≤ sargosSixthExponentStep β+ε)
    calc
      _ ≤ C*(4+B)*(1+Real.log N)^6*(N:ℝ)^(sargosSixthExponentStep (β+ε/2)) := ho
      _ ≤ C*(4+B)*(L*(N:ℝ)^(ε/2))*
          (N:ℝ)^(sargosSixthExponentStep (β+ε/2)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hl (by positivity)) (by positivity)
      _ = D*(N:ℝ)^(sargosSixthExponentStep (β+ε/2)+ε/2) := by
        dsimp [D]
        calc
          _ = C*(4+B)*L*((N:ℝ)^(ε/2)*(N:ℝ)^(sargosSixthExponentStep (β+ε/2))) := by ring
          _ = _ := by rw [he]
      _ ≤ D*(N:ℝ)^(sargosSixthExponentStep β+ε) :=
        mul_le_mul_of_nonneg_left hpow hDp.le
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [hDp]) (by positivity)
  · have hNup : (N:ℝ) ≤ 16 := by exact_mod_cast (by omega : N ≤ 16)
    have hp := pow_le_pow_left₀ hNp.le hNup 3
    have hb := sargosSixthBaseMoment_trivial hN
    have hsmall : sargosSixthBaseMoment N ≤ 8192 := by nlinarith only [hp,hb]
    have hmul := mul_le_mul_of_nonneg_left ht
      (by linarith only [hDp] : 0 ≤ D+8193)
    nlinarith only [hsmall,hmul,hDp]

end TaoTrudgianYang2025
