import TaoTrudgianYang2025.ZetaPerronAboveOne
import TaoTrudgianYang2025.ZetaRealMomentEndpoint

/-! Actual real-order moment transfer throughout tau>1, including c=1. -/

noncomputable section
open Filter MeasureTheory Set
namespace TaoTrudgianYang2025

theorem zetaRealMoment_largeValueBound_aboveOne
    {c p M : ℝ} (hc : 1/2 ≤ c) (hc1 : c < 1) (hp : 1 ≤ p)
    (hDyadic : ∀ η : ℝ, 0 < η → ∃ C T₀ : ℝ, 0 ≤ C ∧
      ∀ H : ℝ, T₀ ≤ H → 0 < H →
        (∫ u in H..2*H, zetaMomentLineNorm c u^p) ≤ C*H^(M+η))
    {σ τ : ℝ} (hσ : 1/2 ≤ σ) (hτ : 1 < τ) :
    IsZetaLargeValueBound σ τ (τ*M-p*(σ-c)) := by
  intro ε hε
  let η : ℝ := min 1 (ε/(4*(τ+1)))
  let δ : ℝ := min (min (1/4) ((τ-1)/4)) (ε/(4*(|M|+p+1)))
  have hτpos : 0 < τ+1 := by linarith
  have hden : 0 < 4*(|M|+p+1) := by linarith [abs_nonneg M]
  have hη : 0 < η := lt_min (by norm_num) (div_pos hε (by positivity))
  have hηone : η ≤ 1 := min_le_left _ _
  have hηeps : η*(4*(τ+1)) ≤ ε :=
    (le_div_iff₀ (by positivity : 0 < 4*(τ+1))).mp (min_le_right _ _)
  have hδ : 0 < δ :=
    lt_min (lt_min (by norm_num) (by linarith)) (div_pos hε hden)
  have hδsmall : δ ≤ min (1/4) ((τ-1)/4) := min_le_left _ _
  have hδgap : δ ≤ (τ-1)/4 := hδsmall.trans (min_le_right _ _)
  have hδeps : δ*(4*(|M|+p+1)) ≤ ε :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  obtain ⟨N₀,hN₀,hEntry⟩ := exists_zetaLinePerron_aboveOne_uniform_threshold hc hc1 hτ
  obtain ⟨T₀,hT₀,hfinite⟩ :=
    zetaPattern_realMoment_cardinality_of_dyadic_and_convolution hc1.ne hp hDyadic hη
  let C : ℝ := max 1 (max N₀ (max T₀ (zetaLinePerronConstant c^p)))
  have hC : 1 ≤ C := le_max_left _ _
  have hCN : N₀ ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCT : T₀ ≤ C := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hCf : zetaLinePerronConstant c^p ≤ C :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨C,hC,δ,hδ,?_⟩
  intro P hPN hTlower hTupper hVlower _
  have hNpos : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hNT : P.N ≤ P.T := by
    apply le_trans _ hTlower
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le
      (by linarith : (1 : ℝ) ≤ τ-δ)
  have hphysical := hfinite P ((hCT.trans hPN).trans hNT)
    (zetaLinePerronConstant c) (zetaLinePerronConstant_pos c)
      (hEntry P (hCN.trans hPN) σ δ hσ hδsmall hTlower hVlower)
  have hVp : P.N^(p*(σ-δ)) ≤ P.V^p := by
    have hh := Real.rpow_le_rpow (Real.rpow_nonneg hNpos.le (σ-δ)) hVlower
      (show 0 ≤ p by linarith)
    rw [← Real.rpow_mul hNpos.le] at hh
    simpa only [mul_comm] using hh
  have hTp : P.T^(M+η) ≤ P.N^(τ*(M+η)+δ*|M+η|) :=
    rpow_le_from_two_sided_height_window hNpos P.T_pos.le hTlower hTupper
  have hMη : |M+η| ≤ |M|+1 := by
    have hh := abs_add_le M η
    rw [abs_of_pos hη] at hh
    linarith
  have hExponent : c*p+τ*(M+η)+δ*|M+η| ≤
      (τ*M-p*(σ-c)+ε)+p*(σ-δ) := by
    nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hMη)]
  apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hNpos (p*(σ-δ)))).mp
  calc
    _ ≤ (P.ordinates.card : ℝ)*P.V^p :=
      mul_le_mul_of_nonneg_left hVp (Nat.cast_nonneg _)
    _ ≤ zetaLinePerronConstant c^p*P.N^(c*p)*P.T^(M+η) := hphysical
    _ ≤ C*P.N^(c*p)*P.N^(τ*(M+η)+δ*|M+η|) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hCf (Real.rpow_nonneg hNpos.le _)) hTp
        (Real.rpow_nonneg P.T_pos.le _) (mul_nonneg (zero_le_one.trans hC)
          (Real.rpow_nonneg hNpos.le _))
    _ = C*P.N^(c*p+τ*(M+η)+δ*|M+η|) := by
      rw [mul_assoc,← Real.rpow_add hNpos]
      congr 2
      ring
    _ ≤ C*P.N^((τ*M-p*(σ-c)+ε)+p*(σ-δ)) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le hExponent) (zero_le_one.trans hC)
    _ = _ := by rw [Real.rpow_add hNpos,mul_assoc]

/-- The EReal least exponent, not just a separately stated candidate
bound, consumes the exact arbitrary-real-order dyadic moment input. -/
theorem zetaLargeValueExponent_le_of_realMoment_aboveOne
    {c p M : ℝ} (hc : 1/2 ≤ c) (hc1 : c < 1) (hp : 1 ≤ p)
    (hDyadic : ∀ η : ℝ, 0 < η → ∃ C T₀ : ℝ, 0 ≤ C ∧
      ∀ H : ℝ, T₀ ≤ H → 0 < H →
        (∫ u in H..2*H, zetaMomentLineNorm c u^p) ≤ C*H^(M+η))
    {σ τ : ℝ} (hσ : 1/2 ≤ σ) (hτ : 1 < τ) :
    zetaLargeValueExponent σ τ ≤ ((τ*M-p*(σ-c) : ℝ) : EReal) :=
  zetaLargeValueExponent_le_of_bound
    (zetaRealMoment_largeValueBound_aboveOne hc hc1 hp hDyadic hσ hτ)

theorem zetaRealMoment_largeValueBound_closedStrip_aboveOne
    {c p M : ℝ} (hc : 1/2 ≤ c) (hc1 : c ≤ 1) (hp : 1 ≤ p)
    (hDyadic : ∀ η : ℝ, 0 < η → ∃ C T₀ : ℝ, 0 ≤ C ∧
      ∀ H : ℝ, T₀ ≤ H → 0 < H →
        (∫ u in H..2*H, zetaMomentLineNorm c u^p) ≤ C*H^(M+η))
    {σ τ : ℝ} (hσ : 1/2 ≤ σ) (hσ1 : σ ≤ 1) (hτ : 1 < τ) :
    IsZetaLargeValueBound σ τ (τ*M-p*(σ-c)) := by
  rcases lt_or_eq_of_le hc1 with hlt | heq
  · exact zetaRealMoment_largeValueBound_aboveOne hc hlt hp hDyadic hσ hτ
  · subst c
    have hM := one_le_zetaOneLine_moment_exponent hp hDyadic
    apply isZetaLargeValueBound_of_exponent_le
    apply (zetaLargeValueExponent_le_tau σ (by linarith : 0 ≤ τ)).trans
    apply EReal.coe_le_coe_iff.mpr
    nlinarith [mul_nonneg (show 0 ≤ p by linarith) (sub_nonneg.mpr hσ1),
      mul_nonneg (show 0 ≤ τ by linarith) (sub_nonneg.mpr hM)]

theorem zetaLargeValueExponent_le_of_realMoment_closedStrip_aboveOne
    {c p M : ℝ} (hc : 1/2 ≤ c) (hc1 : c ≤ 1) (hp : 1 ≤ p)
    (hDyadic : ∀ η : ℝ, 0 < η → ∃ C T₀ : ℝ, 0 ≤ C ∧
      ∀ H : ℝ, T₀ ≤ H → 0 < H →
        (∫ u in H..2*H, zetaMomentLineNorm c u^p) ≤ C*H^(M+η))
    {σ τ : ℝ} (hσ : 1/2 ≤ σ) (hσ1 : σ ≤ 1) (hτ : 1 < τ) :
    zetaLargeValueExponent σ τ ≤ ((τ*M-p*(σ-c) : ℝ) : EReal) :=
  zetaLargeValueExponent_le_of_bound
    (zetaRealMoment_largeValueBound_closedStrip_aboveOne hc hc1 hp hDyadic hσ hσ1 hτ)

end TaoTrudgianYang2025
