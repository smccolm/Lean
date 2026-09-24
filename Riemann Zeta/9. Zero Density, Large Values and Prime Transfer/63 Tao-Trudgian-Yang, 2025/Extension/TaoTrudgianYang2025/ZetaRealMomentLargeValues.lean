import TaoTrudgianYang2025.ZetaGeneralPerronEntry
import TaoTrudgianYang2025.ZetaRealMomentAsymptotics

/-!
# Real zeta moment transfer on every fixed line below one

This proves the moment-to-large-values assertion for 1/2 <= c < 1,
all real moment orders p >= 1, all real dyadic exponents M, and tau >= 2.
The only analytic input is the actual dyadic zeta moment inequality.
The endpoint c=1 is deliberately not identified with this contour proof.
-/

noncomputable section
open Filter MeasureTheory Set
namespace TaoTrudgianYang2025

theorem rpow_le_from_two_sided_height_window
    {N T τ δ B : ℝ} (hN : 0 < N) (hT : 0 ≤ T)
    (hlo : N^(τ-δ) ≤ T) (hhi : T ≤ N^(τ+δ)) :
    T^B ≤ N^(τ*B+δ*|B|) := by
  by_cases hB : 0 ≤ B
  · calc
      _ ≤ (N^(τ+δ))^B := Real.rpow_le_rpow hT hhi hB
      _ = _ := by rw [← Real.rpow_mul hN.le,abs_of_nonneg hB]; congr 1; ring
  · have hB' : B ≤ 0 := le_of_not_ge hB
    calc
      _ ≤ (N^(τ-δ))^B :=
        Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hN _) hlo hB'
      _ = _ := by rw [← Real.rpow_mul hN.le,abs_of_nonpos hB']; congr 1; ring

theorem zetaRealMoment_largeValueBound_of_dyadic
    {c p M : ℝ} (hc : 1/2 ≤ c) (hc1 : c < 1) (hp : 1 ≤ p)
    (hDyadic : ∀ η : ℝ, 0 < η → ∃ C T₀ : ℝ, 0 ≤ C ∧
      ∀ H : ℝ, T₀ ≤ H → 0 < H →
        (∫ u in H..2*H, zetaMomentLineNorm c u^p) ≤ C*H^(M+η))
    {σ τ : ℝ} (hσ : 1/2 ≤ σ) (hτ : 2 ≤ τ) :
    IsZetaLargeValueBound σ τ (τ*M-p*(σ-c)) := by
  intro ε hε
  let η : ℝ := min 1 (ε/(4*(τ+1)))
  let δ : ℝ := min (min (1/4) ((1-c)/4)) (ε/(4*(|M|+p+1)))
  have hτpos : 0 < τ+1 := by linarith
  have hden : 0 < 4*(|M|+p+1) := by linarith [abs_nonneg M]
  have hη : 0 < η := lt_min (by norm_num) (div_pos hε (by positivity))
  have hηone : η ≤ 1 := min_le_left _ _
  have hηeps : η*(4*(τ+1)) ≤ ε :=
    (le_div_iff₀ (by positivity : 0 < 4*(τ+1))).mp (min_le_right _ _)
  have hδ : 0 < δ :=
    lt_min (lt_min (by norm_num) (by linarith)) (div_pos hε hden)
  have hδsmall : δ ≤ min (1/4) ((1-c)/4) := min_le_left _ _
  have hδone : δ ≤ 1/4 := hδsmall.trans (min_le_left _ _)
  have hδeps : δ*(4*(|M|+p+1)) ≤ ε :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  obtain ⟨N₀,hN₀,hEntry⟩ := exists_zetaLinePerron_uniform_threshold hc hc1
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
      (hEntry P (hCN.trans hPN) σ τ δ hσ hτ hδsmall hTlower hVlower)
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
theorem zetaLargeValueExponent_le_of_realMoment
    {c p M : ℝ} (hc : 1/2 ≤ c) (hc1 : c < 1) (hp : 1 ≤ p)
    (hDyadic : ∀ η : ℝ, 0 < η → ∃ C T₀ : ℝ, 0 ≤ C ∧
      ∀ H : ℝ, T₀ ≤ H → 0 < H →
        (∫ u in H..2*H, zetaMomentLineNorm c u^p) ≤ C*H^(M+η))
    {σ τ : ℝ} (hσ : 1/2 ≤ σ) (hτ : 2 ≤ τ) :
    zetaLargeValueExponent σ τ ≤ ((τ*M-p*(σ-c) : ℝ) : EReal) :=
  zetaLargeValueExponent_le_of_bound
    (zetaRealMoment_largeValueBound_of_dyadic hc hc1 hp hDyadic hσ hτ)

end TaoTrudgianYang2025

