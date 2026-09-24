import TaoTrudgianYang2025.ZetaLogarithmicPair
import TaoTrudgianYang2025.ZetaPointwiseNonexistence

/-! Margins retaining the low-frequency N/t contribution. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem exists_zetaPair_nonexistence_margin {k l σ τ : ℝ}
    (hk : 0 ≤ k) (hτ : 0 ≤ τ)
    (hmain : k*τ+l-k < σ) (hres : 1-τ < σ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 ≤ k+δ ∧
      (τ+δ)*(k+δ)+l-k ≤ σ-3*δ ∧ 1-τ+δ ≤ σ-3*δ := by
  let δ := min 1 (min ((σ-(k*τ+l-k))/(2*(τ+k+4))) ((σ-(1-τ))/8))
  have hd : 0 < τ+k+4 := by linarith
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδa : δ ≤ (σ-(k*τ+l-k))/(2*(τ+k+4)) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hδb : δ ≤ (σ-(1-τ))/8 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have ha := (le_div_iff₀ (by positivity : 0 < 2*(τ+k+4))).mp hδa
  have hb := (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mp hδb
  have hs : δ^2 ≤ δ := by nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hδ1)]
  refine ⟨δ,hδ,hδ1,by linarith,?_,?_⟩
  · nlinarith [mul_nonneg hδ.le hd.le]
  · linarith

theorem zetaPair_unweighted_scale_identity {t N : ℝ}
    (ht : 0 < t) (hN : 0 < N) (k l ε : ℝ) :
    (t/N)^(k+ε)*N^(l+ε) = t^(k+ε)*N^(l-k) := by
  rw [Real.div_rpow ht.le hN.le]
  calc
    _ = t^(k+ε)*(N^(l+ε)/N^(k+ε)) := by ring
    _ = t^(k+ε)*N^((l+ε)-(k+ε)) := by rw [Real.rpow_sub hN]
    _ = _ := by congr 2; ring

theorem zetaPair_power_majorant {k l σ τ δ N t : ℝ}
    (hN : 1 ≤ N) (ht : 0 < t) (hkδ : 0 ≤ k+δ)
    (hmain : (τ+δ)*(k+δ)+l-k ≤ σ-3*δ)
    (hres : 1-τ+δ ≤ σ-3*δ)
    (htlo : N^(τ-δ) ≤ t) (hthi : t ≤ N^(τ+δ)) :
    (t/N)^(k+δ)*N^(l+δ)+2*Real.pi*N/t ≤
      (1+2*Real.pi)*N^(σ-3*δ) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hm : (t/N)^(k+δ)*N^(l+δ) ≤ N^(σ-3*δ) := by
    rw [zetaPair_unweighted_scale_identity ht hNp]
    calc
      _ ≤ (N^(τ+δ))^(k+δ)*N^(l-k) :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow ht.le hthi hkδ)
          (Real.rpow_nonneg hNp.le _)
      _ = N^((τ+δ)*(k+δ)+l-k) := by
        rw [← Real.rpow_mul hNp.le,← Real.rpow_add hNp]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN hmain
  have hr : N/t ≤ N^(σ-3*δ) := by
    calc
      _ ≤ N/N^(τ-δ) :=
        div_le_div_of_nonneg_left hNp.le (Real.rpow_pos_of_pos hNp _) htlo
      _ = N^(1-τ+δ) := by
        conv_lhs => lhs; rw [← Real.rpow_one N]
        rw [← Real.rpow_sub hNp]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN hres
  have hh := mul_le_mul_of_nonneg_left hr (show 0 ≤ 2*Real.pi by positivity)
  calc
    _ = (t/N)^(k+δ)*N^(l+δ)+2*Real.pi*(N/t) := by ring
    _ ≤ N^(σ-3*δ)+2*Real.pi*N^(σ-3*δ) := add_le_add hm hh
    _ = _ := by ring

end TaoTrudgianYang2025
