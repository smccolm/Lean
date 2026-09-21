import TaoTrudgianYang2025.ZetaSixthPerron
import TaoTrudgianYang2025.ZetaTwelfthMoment

/-!
# Actual twelfth-moment large values down to height exponent 7/5

The genuine dyadic moment and sixth-order Mellin entry discharge all
analytic inputs. The physical height and value windows remain linked.
-/

noncomputable section

open Filter MeasureTheory Set

namespace TaoTrudgianYang2025

theorem zetaTwelfth_lower_short_largeValueBound {σ τ : ℝ}
    (hσ : 7/10 ≤ σ) (hτ : 7/5 ≤ τ) :
    IsZetaLargeValueBound σ τ (2*τ-12*(σ-1/2)) := by
  intro ε hε
  let η : ℝ := min 1 (ε / (4 * (τ + 1)))
  let δ : ℝ := min (1 / 80) (ε / 64)
  have hτpos : 0 < τ + 1 := by linarith
  have hη : 0 < η := lt_min (by norm_num) (div_pos hε (mul_pos (by norm_num) hτpos))
  have hηone : η ≤ 1 := min_le_left _ _
  have hηeps : η * (4 * (τ + 1)) ≤ ε :=
    (le_div_iff₀ (mul_pos (by norm_num) hτpos)).1 (min_le_right _ _)
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by norm_num))
  have hδsmall : δ ≤ 1 / 80 := min_le_left _ _
  have hδeps : δ * 64 ≤ ε := (le_div_iff₀ (by norm_num : (0 : ℝ) < 64)).1 (min_le_right _ _)
  obtain ⟨N₀, hN₀, hEntry⟩ := exists_zetaSixthPerron_uniform_threshold
  obtain ⟨T₀, hT₀, hfinite⟩ := zetaPattern_twelfth_cardinality_of_dyadic_and_convolution zeta_twelfth_dyadic hη
  let C : ℝ := max 1 (max N₀ (max T₀ (zetaPerronConstant ^ 12)))
  have hC : 1 ≤ C := le_max_left _ _
  have hCN : N₀ ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCT : T₀ ≤ C := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hCf : zetaPerronConstant ^ 12 ≤ C :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨C, hC, δ, hδ, ?_⟩
  intro P hPN hTlower hTupper hVlower _
  have hNpos : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hNT : P.N ≤ P.T := by
    apply le_trans _ hTlower
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le
      (by linarith : (1 : ℝ) ≤ τ - δ)
  have hphysical := hfinite P ((hCT.trans hPN).trans hNT)
    zetaPerronConstant zetaPerronConstant_pos
      (hEntry P (hCN.trans hPN) σ τ δ hσ hτ hδsmall hTlower hVlower)
  have hVp : P.N ^ (12 * (σ - δ)) ≤ P.V ^ 12 := by
    have h := pow_le_pow_left₀ (Real.rpow_nonneg hNpos.le (σ - δ)) hVlower 12
    convert h using 1
    rw [← Real.rpow_natCast (P.N ^ (σ - δ)) 12, ← Real.rpow_mul hNpos.le]
    congr 1
    ring
  have hTp : P.T ^ (2 + η) ≤ P.N ^ ((τ + δ) * (2 + η)) := by
    calc
      _ ≤ (P.N ^ (τ + δ)) ^ (2 + η) :=
        Real.rpow_le_rpow P.T_pos.le hTupper (by linarith)
      _ = _ := (Real.rpow_mul hNpos.le _ _).symm
  have hExponent : 6 + (τ + δ) * (2 + η) ≤
      (2 * τ - 12 * (σ - 1 / 2) + ε) + 12 * (σ - δ) := by
    nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hηone)]
  apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hNpos (12 * (σ - δ)))).mp
  calc
    _ ≤ (P.ordinates.card : ℝ) * P.V ^ 12 :=
      mul_le_mul_of_nonneg_left hVp (Nat.cast_nonneg _)
    _ ≤ zetaPerronConstant ^ 12 * P.N ^ 6 * P.T ^ (2 + η) := hphysical
    _ ≤ C * P.N ^ 6 * P.N ^ ((τ + δ) * (2 + η)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hCf (pow_nonneg hNpos.le _)) hTp
        (Real.rpow_nonneg P.T_pos.le _) (mul_nonneg (zero_le_one.trans hC) (pow_nonneg hNpos.le _))
    _ = C * P.N ^ (6 + (τ + δ) * (2 + η)) := by
      rw [mul_assoc, ← Real.rpow_natCast P.N 6, ← Real.rpow_add hNpos]
      norm_num
    _ ≤ C * P.N ^ ((2 * τ - 12 * (σ - 1 / 2) + ε) + 12 * (σ - δ)) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le hExponent)
        (zero_le_one.trans hC)
    _ = _ := by rw [Real.rpow_add hNpos, mul_assoc]

end TaoTrudgianYang2025
