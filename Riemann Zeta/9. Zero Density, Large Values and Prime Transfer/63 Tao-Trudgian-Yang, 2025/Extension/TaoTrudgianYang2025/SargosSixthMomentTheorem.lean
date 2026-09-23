import TaoTrudgianYang2025.SargosSixthMomentIteration
import TaoTrudgianYang2025.SargosSixthStripTransfer

/-! The weighted maximal sixth moment on actual natural-length quartic blocks. -/

noncomputable section

open MeasureTheory Set

namespace TaoTrudgianYang2025

theorem sargosQuartic_maximal_sixth_moment (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N : ℕ), 2 ≤ N → ∀ z : ℤ → ℂ,
      (∀ n ∈ sargosSourceInterval N, ‖z n‖ ≤ 1) →
      ∀ lambda : ℝ, 0 < lambda → ∀ c d : ℝ,
      (∫ α in Icc c (c+1), ∫ γ in Icc d (d+lambda),
        (sargosQuarticPrefixMaximum N z α γ)^6) ≤
        C*(lambda*(N:ℝ)^(3+ε)+(N:ℝ)^ε) := by
  have hη : 0 < ε/2 := by positivity
  obtain ⟨B,hB,hbase⟩ := sargosSixthBaseMoment_subpolynomial (ε/2) hη
  let L : ℝ := (1+6/(ε/2))^6
  let D : ℝ := 128*sargosWindowConstant 3 0*L*B
  have hW := sargosWindowConstant_nonneg 3 (le_refl (0:ℝ))
  have hD : 0 ≤ D := by dsimp [D,L]; positivity
  refine ⟨D+1,by linarith only [hD],?_⟩
  intro N hN z hz lambda hlambda c d
  have hN₁ : 1 ≤ N := by omega
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN₁
  have hNp : (0:ℝ) < N := by linarith only [hNr]
  have hlog : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg hNr
  have hlogBound : (Real.log (N:ℝ))^6 ≤ L*(N:ℝ)^(ε/2) :=
    (pow_le_pow_left₀ hlog (by linarith : Real.log (N:ℝ) ≤ 1+Real.log N) 6).trans
      (sargos_log_six_le_rpow hNr hη)
  have hI := hbase N hN₁
  have hraw := sargosQuartic_maximal_sixth_strip_reduction hN z hz hlambda c d
  have he : (N:ℝ)^(ε/2)*(N:ℝ)^(ε/2) = (N:ℝ)^ε := by
    rw [← Real.rpow_add hNp]
    congr 1
    ring
  have hcub : (N:ℝ)^3*(N:ℝ)^ε = (N:ℝ)^(3+ε) := by
    calc
      _ = (N:ℝ)^(3:ℝ)*(N:ℝ)^ε := by
        rw [← Real.rpow_natCast]
        norm_num
      _ = _ := (Real.rpow_add hNp 3 ε).symm
  have hsum : 0 ≤ lambda*(N:ℝ)^(3+ε)+(N:ℝ)^ε := by positivity
  calc
    _ ≤ 128*sargosWindowConstant 3 0*(1+lambda*(N:ℝ)^3)*
        (Real.log N)^6*sargosSixthBaseMoment N := hraw
    _ ≤ 128*sargosWindowConstant 3 0*(1+lambda*(N:ℝ)^3)*
        (L*(N:ℝ)^(ε/2))*(B*(N:ℝ)^(ε/2)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hlogBound (by positivity)
      · exact hI
      · exact sargosSixthBaseMoment_nonneg N
      · positivity
    _ = D*(1+lambda*(N:ℝ)^3)*((N:ℝ)^(ε/2)*(N:ℝ)^(ε/2)) := by dsimp [D]; ring
    _ = D*(lambda*(N:ℝ)^(3+ε)+(N:ℝ)^ε) := by
      rw [he,← hcub]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [hD]) hsum

end TaoTrudgianYang2025
