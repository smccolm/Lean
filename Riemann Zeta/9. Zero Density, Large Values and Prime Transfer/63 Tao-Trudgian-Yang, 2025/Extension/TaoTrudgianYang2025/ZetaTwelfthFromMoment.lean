import TaoTrudgianYang2025.ZetaPerronEntry
import TaoTrudgianYang2025.ZetaShortPerron
import TaoTrudgianYang2025.ZetaMomentAsymptotics
import TaoTrudgianYang2025.EnergyClauseOneZeta

/-!
# The uniform zeta large-values consequence of a genuine twelfth moment

The coefficient-one entry, localization, residue, logarithmic loss, and
physical exponent windows are all proved. The only analytic theorem input
is the explicitly quantified dyadic critical-line twelfth moment.
-/

noncomputable section

open Filter MeasureTheory Set

namespace TaoTrudgianYang2025

private theorem zetaTwelfth_largeValueBound_of_uniform_entry
    (hDyadic : ∀ η : ℝ, 0 < η → ∃ C T₀ : ℝ, 0 ≤ C ∧
      ∀ H : ℝ, T₀ ≤ H → 0 < H →
        (∫ u in H..2 * H, zetaMomentCriticalNorm u ^ 12) ≤ C * H ^ (2 + η))
    {σ τ : ℝ} (hτ : 3 / 2 ≤ τ)
    (hUniform : ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ P : ZetaLargeValuePattern, N₀ ≤ P.N →
      ∀ δ : ℝ, δ ≤ 1 / 16 → P.N ^ (τ - δ) ≤ P.T → P.N ^ (σ - δ) ≤ P.V →
        ∀ t ∈ P.ordinates,
          P.V ≤ zetaPerronConstant * Real.sqrt P.N * zetaMomentConvolution P.T t) :
    IsZetaLargeValueBound σ τ (2 * τ - 12 * (σ - 1 / 2)) := by
  intro ε hε
  let η : ℝ := min 1 (ε / (4 * (τ + 1)))
  let δ : ℝ := min (1 / 16) (ε / 64)
  have hτpos : 0 < τ + 1 := by linarith
  have hη : 0 < η := lt_min (by norm_num) (div_pos hε (mul_pos (by norm_num) hτpos))
  have hηone : η ≤ 1 := min_le_left _ _
  have hηeps : η * (4 * (τ + 1)) ≤ ε :=
    (le_div_iff₀ (mul_pos (by norm_num) hτpos)).1 (min_le_right _ _)
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by norm_num))
  have hδsmall : δ ≤ 1 / 16 := min_le_left _ _
  have hδeps : δ * 64 ≤ ε := (le_div_iff₀ (by norm_num : (0 : ℝ) < 64)).1 (min_le_right _ _)
  obtain ⟨N₀, hN₀, hEntry⟩ := hUniform
  obtain ⟨T₀, hT₀, hfinite⟩ := zetaPattern_twelfth_cardinality_of_dyadic_and_convolution hDyadic hη
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
      (hEntry P (hCN.trans hPN) δ hδsmall hTlower hVlower)
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

theorem zetaTwelfth_largeValueBound_of_dyadic
    (hDyadic : ∀ η : ℝ, 0 < η → ∃ C T₀ : ℝ, 0 ≤ C ∧
      ∀ H : ℝ, T₀ ≤ H → 0 < H →
        (∫ u in H..2 * H, zetaMomentCriticalNorm u ^ 12) ≤ C * H ^ (2 + η))
    {σ τ : ℝ} (hσ : 1 / 2 ≤ σ) (hτ : 2 ≤ τ) :
    IsZetaLargeValueBound σ τ (2 * τ - 12 * (σ - 1 / 2)) := by
  apply zetaTwelfth_largeValueBound_of_uniform_entry hDyadic (by linarith : 3 / 2 ≤ τ)
  obtain ⟨N₀, hN₀, h⟩ := exists_zetaPerron_uniform_threshold
  refine ⟨N₀, hN₀, ?_⟩
  intro P hN δ hδ hT hV
  exact h P hN σ τ δ hσ hτ (by linarith) hT hV

/-- The actual short-height Perron consumer extends the same moment
consequence to `τ ≥ 3/2` when `σ ≥ 3/4`. -/
theorem zetaTwelfth_short_largeValueBound_of_dyadic
    (hDyadic : ∀ η : ℝ, 0 < η → ∃ C T₀ : ℝ, 0 ≤ C ∧
      ∀ H : ℝ, T₀ ≤ H → 0 < H →
        (∫ u in H..2 * H, zetaMomentCriticalNorm u ^ 12) ≤ C * H ^ (2 + η))
    {σ τ : ℝ} (hσ : 3 / 4 ≤ σ) (hτ : 3 / 2 ≤ τ) :
    IsZetaLargeValueBound σ τ (2 * τ - 12 * (σ - 1 / 2)) := by
  apply zetaTwelfth_largeValueBound_of_uniform_entry hDyadic hτ
  obtain ⟨N₀, hN₀, h⟩ := exists_zetaPerron_short_uniform_threshold
  exact ⟨N₀, hN₀, fun P hN δ hδ => h P hN σ τ δ hσ hτ hδ⟩

theorem energyClauseOne_of_dyadic_moment_and_short_zeta
    (hDyadic : ∀ η : ℝ, 0 < η → ∃ C T₀ : ℝ, 0 ≤ C ∧
      ∀ H : ℝ, T₀ ≤ H → 0 < H →
        (∫ u in H..2 * H, zetaMomentCriticalNorm u ^ 12) ≤ C * H ^ (2 + η))
    {σ : ℝ} (hlo : 3 / 4 ≤ σ) (hhi : σ ≤ 5 / 6)
    (hShort : ∀ τ ∈ Ico (1 : ℝ) 2,
      IsZetaLargeValueEnergyBound σ τ (energyClauseOnePublicRate σ * τ)) :
    IsZeroDensityEnergyBound σ (energyClauseOnePublicRate σ / (1 - σ)) :=
  energyClauseOne_of_twelfth_and_short_zeta hlo hhi hShort
    (fun _ hτ => zetaTwelfth_largeValueBound_of_dyadic hDyadic (by linarith) hτ.1)

end TaoTrudgianYang2025
