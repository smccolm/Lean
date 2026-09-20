import TaoTrudgianYang2025.EnergyClauseOneGeneral

/-!
# Zeta-energy optimization for Add-est (i)

The rational certificate and the corrected Huxley cardinality cap are proved
here. The source twelfth-moment cardinality bound is a separate analytic
input: every theorem that needs it keeps it explicit. Neither this module
nor the printed five-coordinate powering statement supplies that input.
-/

noncomputable section

namespace TaoTrudgianYang2025

/-- The exact maximum in the source intermediate `imphb-zlver-ineq`. -/
def energyClauseOneZetaRate (σ : ℝ) : ℝ :=
  max ((45 - 46 * σ) / (4 * (4 * σ - 1)))
    (4 * (10 - 9 * σ) / (5 * (4 * σ - 1)))

theorem energyClauseOneZetaRate_lower_piece {σ : ℝ}
    (hlo : 3 / 4 ≤ σ) (hhi : σ ≤ 65 / 86) :
    energyClauseOneZetaRate σ = (45 - 46 * σ) / (4 * (4 * σ - 1)) := by
  have hd : 0 < 4 * σ - 1 := by linarith
  apply max_eq_left
  apply (div_le_div_iff₀ (by positivity : 0 < 5 * (4 * σ - 1))
    (by positivity : 0 < 4 * (4 * σ - 1))).2
  nlinarith [mul_nonneg hd.le (by linarith : 0 ≤ 65 - 86 * σ)]

theorem energyClauseOneZetaRate_upper_piece {σ : ℝ}
    (hlo : 65 / 86 ≤ σ) :
    energyClauseOneZetaRate σ = 4 * (10 - 9 * σ) / (5 * (4 * σ - 1)) := by
  have hd : 0 < 4 * σ - 1 := by linarith
  apply max_eq_right
  apply (div_le_div_iff₀ (by positivity : 0 < 4 * (4 * σ - 1))
    (by positivity : 0 < 5 * (4 * σ - 1))).2
  nlinarith [mul_nonneg hd.le (by linarith : 0 ≤ 86 * σ - 65)]

/-- The source's strict slope bounds, with both closed sigma endpoints. -/
theorem energyClauseOneZetaRate_slope {σ : ℝ}
    (hlo : 3 / 4 ≤ σ) (hhi : σ ≤ 5 / 6) :
    4 / 5 < energyClauseOneZetaRate σ ∧ energyClauseOneZetaRate σ < 2 := by
  have hd : 0 < 4 * σ - 1 := by linarith
  constructor
  · apply lt_of_lt_of_le _ (le_max_right _ _)
    apply (lt_div_iff₀ (by positivity : 0 < 5 * (4 * σ - 1))).2
    linarith
  · apply max_lt
    · apply (div_lt_iff₀ (by positivity : 0 < 4 * (4 * σ - 1))).2
      linarith
    · apply (div_lt_iff₀ (by positivity : 0 < 5 * (4 * σ - 1))).2
      linarith

private theorem zetaRate_first_three_at_two {σ : ℝ}
    (hlo : 3 / 4 ≤ σ) (i : Fin 3) :
    heathBrownEnergyBranch σ 2 (4 - 4 * σ) i.castSucc.castSucc.castSucc ≤
      energyClauseOneZetaRate σ * 2 := by
  have hd : 0 < 5 * (4 * σ - 1) := by linarith
  have hright := le_max_right ((45 - 46 * σ) / (4 * (4 * σ - 1)))
    (4 * (10 - 9 * σ) / (5 * (4 * σ - 1)))
  change _ ≤ energyClauseOneZetaRate σ at hright
  apply le_trans _ (mul_le_mul_of_nonneg_right hright (by norm_num : (0 : ℝ) ≤ 2))
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hd).2
  fin_cases i <;> norm_num [heathBrownEnergyBranch]
  · nlinarith [sq_nonneg (σ - 17 / 20)]
  · nlinarith [sq_nonneg (σ - 181 / 240)]
  · nlinarith [sq_nonneg (σ - 13 / 16)]

private theorem zetaRate_last_three_at_mid {σ : ℝ}
    (hlo : 3 / 4 ≤ σ) (hhi : σ ≤ 5 / 6) (i : Fin 3) :
    heathBrownEnergyBranch σ (4 * σ - 1) (4 - 4 * σ) (i.addNat 3) ≤
      energyClauseOneZetaRate σ * (4 * σ - 1) := by
  have hd : 0 < 4 * σ - 1 := by linarith
  have hfirst := (div_le_iff₀ (show 0 < 4 * (4 * σ - 1) by positivity)).1
    (le_max_left ((45 - 46 * σ) / (4 * (4 * σ - 1)))
      (4 * (10 - 9 * σ) / (5 * (4 * σ - 1))))
  have hsecond := (div_le_iff₀ (show 0 < 5 * (4 * σ - 1) by positivity)).1
    (le_max_right ((45 - 46 * σ) / (4 * (4 * σ - 1)))
      (4 * (10 - 9 * σ) / (5 * (4 * σ - 1))))
  change _ ≤ energyClauseOneZetaRate σ * _ at hfirst hsecond
  fin_cases i
  · change 3 - 4 * σ + 5 / 4 * (4 - 4 * σ) + (4 * σ - 1) / 2 ≤ _
    nlinarith
  · change 1 - 2 * σ + 21 / 8 * (4 - 4 * σ) + (4 * σ - 1) / 4 ≤ _
    nlinarith
  · change (8 - 16 * σ + 9 * (4 - 4 * σ) + 4 * (4 * σ - 1)) / 5 ≤ _
    nlinarith

/-- Exact six-branch certificate. The two cardinality caps are narrower
upstream constraints, not the desired energy conclusion. -/
theorem energyClauseOneZeta_branch_bound
    {σ t r : ℝ} (hlo : 3 / 4 ≤ σ) (hhi : σ ≤ 5 / 6)
    (ht : 2 ≤ t) (hrHuxley : r ≤ 4 - 4 * σ)
    (hrTwelfth : r ≤ 2 * t - 12 * (σ - 1 / 2)) (i : Fin 6) :
    heathBrownEnergyBranch σ t r i ≤ energyClauseOneZetaRate σ * t := by
  obtain ⟨hBLower, hBUpper⟩ := energyClauseOneZetaRate_slope hlo hhi
  by_cases hi : i.val < 3
  · let j : Fin 3 := ⟨i.val, hi⟩
    have hbase := zetaRate_first_three_at_two hlo j
    have heq : j.castSucc.castSucc.castSucc = i := Fin.ext rfl
    rw [heq] at hbase
    apply (heathBrownEnergyBranch_mono_card σ t i hrHuxley).trans
    have hg := mul_nonneg (by linarith : 0 ≤ t - 2)
      (by linarith : 0 ≤ energyClauseOneZetaRate σ - 2 / 5)
    fin_cases i <;> norm_num at hi <;>
      norm_num [heathBrownEnergyBranch] at hbase ⊢ <;> nlinarith
  · have hi' : 3 ≤ i.val := by omega
    let j : Fin 3 := ⟨i.val - 3, by omega⟩
    have hbase := zetaRate_last_three_at_mid hlo hhi j
    have heq : j.addNat 3 = i := Fin.ext (by dsimp [j]; omega)
    rw [heq] at hbase
    by_cases htMid : t ≤ 4 * σ - 1
    · apply (heathBrownEnergyBranch_mono_card σ t i hrTwelfth).trans
      have hg := mul_nonneg (by linarith : 0 ≤ 4 * σ - 1 - t)
        (by linarith : 0 ≤ 2 - energyClauseOneZetaRate σ)
      fin_cases i <;> norm_num at hi' <;>
        norm_num [heathBrownEnergyBranch] at hbase ⊢ <;> nlinarith
    · apply (heathBrownEnergyBranch_mono_card σ t i hrHuxley).trans
      have hg := mul_nonneg (by linarith : 0 ≤ t - (4 * σ - 1))
        (by linarith : 0 ≤ energyClauseOneZetaRate σ - 4 / 5)
      fin_cases i <;> norm_num at hi' <;>
        norm_num [heathBrownEnergyBranch] at hbase ⊢ <;> nlinarith

/-- Huxley's short general-height cardinality cap, using the corrected
cardinality witness at power two. No zeta theorem is needed for this cap. -/
theorem InCardinalityEnergyRegion.energyClauseOneZeta_cardinality_cap
    {σ τ ρ e : ℝ} (h : InCardinalityEnergyRegion σ τ ρ e)
    (hτ : τ ≤ 8 * σ - 4) : ρ ≤ 4 - 4 * σ := by
  have hpower := h.huxley_cardinality_powered 2 (by norm_num)
  change ρ / 2 ≤ max (2 - 2 * σ) (4 + τ / 2 - 6 * σ) at hpower
  rw [max_eq_left (by linarith : 4 + τ / 2 - 6 * σ ≤ 2 - 2 * σ)] at hpower
  linarith

/-- The source zeta intermediate, conditional only on its separately stated
twelfth-moment cardinality inequality. Actual region membership discharges
the Huxley cap and the Heath--Brown energy relation. -/
theorem InZetaLargeValueEnergyRegion.energyClauseOneZeta_of_twelfth_cardinality
    {σ τ ρ e s : ℝ} (h : InZetaLargeValueEnergyRegion σ τ ρ e s)
    (hlo : 3 / 4 ≤ σ) (hhi : σ ≤ 5 / 6)
    (htlo : 2 ≤ τ) (hthi : τ ≤ 8 * σ - 4)
    (hTwelfth : ρ ≤ 2 * τ - 12 * (σ - 1 / 2)) :
    e / τ ≤ energyClauseOneZetaRate σ := by
  have hcap := (show InCardinalityEnergyRegion σ τ ρ e from
    ⟨s, h.toGeneral⟩).energyClauseOneZeta_cardinality_cap hthi
  obtain ⟨i, hi⟩ := exists_heathBrownEnergyBranch (by linarith : ρ ≤ 1)
    h.toGeneral.heathBrown_relation
  apply (div_le_iff₀ (by linarith : 0 < τ)).2
  exact hi.trans (energyClauseOneZeta_branch_bound hlo hhi htlo hcap hTwelfth i)

/-- The intermediate zeta maximum lies below the advertised final maximum
on the exact closed source interval. -/
theorem energyClauseOneZetaRate_le_public {σ : ℝ}
    (hlo : 3 / 4 ≤ σ) (hhi : σ ≤ 5 / 6) :
    energyClauseOneZetaRate σ ≤ energyClauseOnePublicRate σ := by
  apply max_le
  · apply le_trans _ (le_max_left _ _)
    apply (div_le_div_iff₀ (by linarith : 0 < 4 * (4 * σ - 1))
      (by linarith : 0 < 2 * (3 * σ - 1))).2
    nlinarith [sq_nonneg (σ - 3 / 4)]
  · exact le_max_right _ _

/-- A uniform zeta large-value estimate controls the cardinality coordinate
of an actual zeta energy-region witness. All epsilon losses and the
constant, chosen before the pattern, are absorbed at genuinely large scale. -/
theorem InZetaLargeValueEnergyRegion.rho_le_of_largeValueBound
    {σ τ ρ e s B : ℝ} (hregion : InZetaLargeValueEnergyRegion σ τ ρ e s)
    (hbound : IsZetaLargeValueBound σ τ B) : ρ ≤ B := by
  by_contra hcontra
  have hgap : 0 < ρ - B := sub_pos.mpr (lt_of_not_ge hcontra)
  let ε : ℝ := (ρ - B) / 4
  have hε : 0 < ε := div_pos hgap (by norm_num)
  obtain ⟨K, hK, δ, hδ, hcard⟩ := hbound ε hε
  let C : ℝ := max K (K ^ (1 / ε : ℝ))
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (hK.trans (le_max_left _ _))
  obtain ⟨P, hNLower, hTLower, hTUpper, hVLower, hVUpper, hCardLower, _⟩ :=
    hregion.2.2.2.2.2 ε hε δ hδ C hC
  have hKN : K ≤ P.N := (le_max_left _ _).trans hNLower
  have hCardUpper := hcard P hKN hTLower hTUpper hVLower hVUpper
  have hKPowerBase : K ^ (1 / ε : ℝ) ≤ P.N := (le_max_right _ _).trans hNLower
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hKAbsorb : K ≤ P.N ^ ε := by
    calc
      K = K ^ (1 : ℝ) := (Real.rpow_one K).symm
      _ = K ^ ((1 / ε) * ε) := by congr 1; field_simp
      _ = (K ^ (1 / ε : ℝ)) ^ ε := Real.rpow_mul hKpos.le _ _
      _ ≤ P.N ^ ε := Real.rpow_le_rpow (by positivity) hKPowerBase hε.le
  have hPowerOrder : P.N ^ (ρ - ε) ≤ P.N ^ (B + 2 * ε) := by
    calc
      P.N ^ (ρ - ε) ≤ (P.ordinates.card : ℝ) := hCardLower
      _ ≤ K * P.N ^ (B + ε) := hCardUpper
      _ ≤ P.N ^ ε * P.N ^ (B + ε) :=
        mul_le_mul_of_nonneg_right hKAbsorb
          (Real.rpow_nonneg (zero_le_one.trans P.one_lt_N.le) _)
      _ = P.N ^ (B + 2 * ε) := by
        rw [← Real.rpow_add (lt_trans zero_lt_one P.one_lt_N)]
        congr 1
        ring
  have hExponentStrict : B + 2 * ε < ρ - ε := by dsimp [ε]; linarith
  exact (not_lt_of_ge hPowerOrder)
    (Real.rpow_lt_rpow_of_exponent_lt P.one_lt_N hExponentStrict)

/-- Compactness promotes the exact zeta-region certificate to the uniform
energy predicate, conditional on the actual twelfth-moment LV predicate. -/
theorem energyClauseOneZeta_uniform_bound_of_twelfth
    {σ τ : ℝ} (hlo : 3 / 4 ≤ σ) (hhi : σ ≤ 5 / 6)
    (htlo : 2 ≤ τ) (hthi : τ ≤ 8 * σ - 4)
    (hTwelfth : IsZetaLargeValueBound σ τ (2 * τ - 12 * (σ - 1 / 2))) :
    IsZetaLargeValueEnergyBound σ τ (energyClauseOneZetaRate σ * τ) := by
  by_contra hnot
  obtain ⟨ρ, e, s, hregion, hlarge⟩ := zetaEnergyRegion_exists_rhoStar_gt_of_not_bound
    (by linarith : 1 / 2 ≤ σ) (by linarith : σ ≤ 1) (by linarith : 0 ≤ τ) hnot
  have hbound := hregion.energyClauseOneZeta_of_twelfth_cardinality hlo hhi htlo hthi
    (hregion.rho_le_of_largeValueBound hTwelfth)
  have := (div_le_iff₀ (by linarith : 0 < τ)).1 hbound
  linarith

/-- The advertised rate is a valid uniform zeta-energy bound on the source
range once the independently stated twelfth-moment estimate is supplied. -/
theorem energyClauseOneZeta_public_rate_bound_of_twelfth
    {σ τ : ℝ} (hlo : 3 / 4 ≤ σ) (hhi : σ ≤ 5 / 6)
    (htlo : 2 ≤ τ) (hthi : τ ≤ 8 * σ - 4)
    (hTwelfth : IsZetaLargeValueBound σ τ (2 * τ - 12 * (σ - 1 / 2))) :
    IsZetaLargeValueEnergyBound σ τ (energyClauseOnePublicRate σ * τ) := by
  intro ε hε
  obtain ⟨C, hC, δ, hδ, hbound⟩ :=
    energyClauseOneZeta_uniform_bound_of_twelfth hlo hhi htlo hthi hTwelfth ε hε
  refine ⟨C, hC, δ, hδ, ?_⟩
  intro P hN hTl hTu hVl hVu
  apply (hbound P hN hTl hTu hVl hVu).trans
  apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hC)
  apply Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le
  have := mul_le_mul_of_nonneg_right (energyClauseOneZetaRate_le_public hlo hhi)
    (by linarith : 0 ≤ τ)
  linarith

/-- End-to-end clause-(i) assembly with exactly two remaining analytic
inputs: short zeta energy on `[1,2)` and twelfth-moment cardinality on the
source range. Neither input is proved by this conditional theorem. -/
theorem energyClauseOne_of_twelfth_and_short_zeta
    {σ : ℝ} (hlo : 3 / 4 ≤ σ) (hhi : σ ≤ 5 / 6)
    (hShort : ∀ τ ∈ Set.Ico (1 : ℝ) 2,
      IsZetaLargeValueEnergyBound σ τ (energyClauseOnePublicRate σ * τ))
    (hTwelfth : ∀ τ ∈ Set.Ico (2 : ℝ) (8 * σ - 4),
      IsZetaLargeValueBound σ τ (2 * τ - 12 * (σ - 1 / 2))) :
    IsZeroDensityEnergyBound σ (energyClauseOnePublicRate σ / (1 - σ)) := by
  apply energyClauseOne_of_zeta_range hlo hhi
  intro τ hτ
  by_cases ht : τ < 2
  · exact hShort τ ⟨hτ.1, ht⟩
  · exact energyClauseOneZeta_public_rate_bound_of_twelfth hlo hhi
      (le_of_not_gt ht) hτ.2.le (hTwelfth τ ⟨le_of_not_gt ht, hτ.2⟩)

end TaoTrudgianYang2025
