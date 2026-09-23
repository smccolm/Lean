import TaoTrudgianYang2025.SargosSixthDyadicBudget

/-! A genuine finite-scale bootstrap from upstream bounds on the actual base moments. -/

noncomputable section

namespace TaoTrudgianYang2025

theorem sargosQuarticDyadicSixthMoment_le_power :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (β B : ℝ), 0 ≤ β → 0 ≤ B →
      (∀ M : ℕ, 1 ≤ M → sargosSixthBaseMoment M ≤ B*(M:ℝ)^β) →
      ∀ (N : ℕ) (A δ : ℝ), 16 ≤ N → A ≤ 1/4 →
        1/Real.sqrt N ≤ δ → δ ≤ A →
        sargosQuarticDyadicSixthMoment N δ ≤
          C*B*δ*(Real.log N)^6*(4*A*N)^β := by
  obtain ⟨C,hC,hsource⟩ := sargosQuartic_sixth_moment_reduction
  refine ⟨2*C,by linarith only [hC],?_⟩
  intro β B hβ hB hbound N A δ hN hA hδ hδA
  let m := sargosQuarticRoundedDualScale N δ
  have hNr : (16:ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0:ℝ) < N := by linarith only [hNr]
  have hs := sargosQuartic_source_scale_sixteen hNr hδ
  have hδp : 0 < δ := hs.1
  have hm : 1 ≤ m := by change 1 ≤ sargosQuarticRoundedDualScale N δ; omega
  have hm₂ : 1 ≤ 2*m := by omega
  have hfloor : (m:ℝ) ≤ 2*δ*N := Nat.floor_le (by positivity)
  have hδN := mul_le_mul_of_nonneg_right hδA hNp.le
  have hmA : (m:ℝ) ≤ 4*A*N := by nlinarith only [hfloor,hδN,hs.2.1]
  have hm₂A : ((2*m:ℕ):ℝ) ≤ 4*A*N := by
    push_cast
    nlinarith only [hfloor,hδN]
  have h₁ := (hbound m hm).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Nat.cast_nonneg m) hmA hβ) hB)
  have h₂ := (hbound (2*m) hm₂).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Nat.cast_nonneg (2*m)) hm₂A hβ) hB)
  have hsum : sargosSixthBaseMoment m+sargosSixthBaseMoment (2*m) ≤
      2*B*(4*A*N)^β := by linarith only [h₁,h₂]
  have hsourceN := hsource N δ hN hδ (hδA.trans hA)
  calc
    _ ≤ C*δ*(Real.log N)^6*
        (sargosSixthBaseMoment m+sargosSixthBaseMoment (2*m)) := hsourceN
    _ ≤ C*δ*(Real.log N)^6*(2*B*(4*A*N)^β) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

theorem sargosSixthBaseMoment_power_bootstrap :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (β B : ℝ), 0 ≤ β → 0 ≤ B →
      (∀ M : ℕ, 1 ≤ M → sargosSixthBaseMoment M ≤ B*(M:ℝ)^β) →
      ∀ (N : ℕ) (A : ℝ), 16 ≤ N → 0 < A → A ≤ 1/4 →
        sargosSixthBaseMoment N ≤
          C*((1+Real.log N)^5/A+B*(Real.log N)^6*(4*A*N)^β) := by
  obtain ⟨D,hD,hdyadic⟩ := sargosQuarticDyadicSixthMoment_le_power
  let C : ℝ := 1024*44845498368+2048*D+1
  have hC : 1 ≤ C := by dsimp [C]; linarith only [hD]
  refine ⟨C,hC,?_⟩
  intro β B hβ hB hbound N A hN hA hA₁
  have hN₁ : 1 ≤ N := by omega
  have hlog : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast hN₁)
  have hbudget : 0 ≤ D*B*(Real.log N)^6*(4*A*N)^β := by positivity
  have hpre := sargosSixthBaseMoment_le_dyadic_budget hN₁ hA
    (by linarith only [hA₁] : A ≤ 1/2) hbudget (by
      intro δ hδ hδA
      exact (hdyadic β B hβ hB hbound N A δ hN hA₁ hδ hδA).trans_eq (by ring))
  have hX : 0 ≤ (1+Real.log (N:ℝ))^5/A := by positivity
  have hY : 0 ≤ B*(Real.log N)^6*(4*A*N)^β := by positivity
  have hc₁ : (1024:ℝ)*44845498368 ≤ C := by dsimp [C]; linarith only [hD]
  have hc₂ : 2048*D ≤ C := by dsimp [C]; linarith only [hD]
  calc
    _ ≤ (1024/A)*(44845498368*(1+Real.log N)^5)+
        2048*(D*B*(Real.log N)^6*(4*A*N)^β) := hpre
    _ = (1024*44845498368)*((1+Real.log N)^5/A)+
        (2048*D)*(B*(Real.log N)^6*(4*A*N)^β) := by ring
    _ ≤ C*((1+Real.log N)^5/A)+C*(B*(Real.log N)^6*(4*A*N)^β) :=
      add_le_add (mul_le_mul_of_nonneg_right hc₁ hX) (mul_le_mul_of_nonneg_right hc₂ hY)
    _ = _ := by ring

end TaoTrudgianYang2025
