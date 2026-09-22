import TaoTrudgianYang2025.BourgainDiagonalFamily

/-!
# Bourgain's zero-loss logarithmic dichotomy on actual energy regions

Both limiting coordinates come from one subsequence of actual retained sets
and complete integer slices. The source packing inequality identifies the
retained exponent; the explicit diagonal losses tend to zero.
-/

open Filter Set Topology
open scoped Classical

set_option maxHeartbeats 800000

noncomputable section

namespace TaoTrudgianYang2025

/-- Subset monotonicity compares actual source and retained logarithmic counts. -/
theorem BourgainDiagonalFamily.retained_log_le {σ τ χ α ρ : ℝ}
    (F : BourgainDiagonalFamily σ τ χ α ρ) (n : ℕ) :
    Real.logb (F.pattern n).N ((F.retained n).card : ℝ) ≤
      Real.logb (F.pattern n).N ((F.pattern n).ordinates.card : ℝ) := by
  have hS : (0 : ℝ) < (F.retained n).card := by
    exact_mod_cast (F.retained_nonempty n).card_pos
  have hP : (0 : ℝ) < (F.pattern n).ordinates.card := by
    exact_mod_cast ((F.retained_nonempty n).mono (F.retained_subset n)).card_pos
  apply (Real.logb_le_logb (F.pattern n).one_lt_N hS hP).2
  exact_mod_cast Finset.card_le_card (F.retained_subset n)

/-- The large branch gives the source's exact auxiliary-witness inequality.
The family input is consumed through its physical geometry and comparisons. -/
theorem BourgainDiagonalFamily.source_witness {σ τ χ α ρ : ℝ}
    (F : BourgainDiagonalFamily σ τ χ α ρ)
    (hgap : bourgainSmallExponent σ τ α χ < ρ) :
    ∃ x : ℝ, 0 ≤ x ∧
      max (-2*α+2*σ+x+ρ) (-α-χ/2+2*σ+x/2+3*ρ/2) ≤
        heathBrownDoubleZetaExponent τ ρ/2+heathBrownDoubleZetaExponent τ x/2 := by
  obtain ⟨r, x, _, _, hx0, _, φ, hφ, hr, hx⟩ :=
    bourgain_source_slice_log_subsequence F.pattern F.retained
      F.localHeight F.accuracy F.delta F.sliceValue F.shift τ χ
      F.scale_two F.retained_nonempty F.retained_subset F.scale_le_local
      F.local_le_time F.time_upper F.local_upper
      (fun n => (F.delta_le n).trans (F.accuracy_le n))
      (fun n => (F.accuracy_le n).trans (by norm_num))
      F.shift_mem F.slice_nonempty
  have he := F.accuracy_zero.comp hφ.tendsto_atTop
  have hsource := F.source_log.comp hφ.tendsto_atTop
  have hrle : r ≤ ρ := le_of_tendsto_of_tendsto hr hsource
    (Eventually.of_forall fun n => F.retained_log_le (φ n))
  have hpackLim : Tendsto
      (fun n => F.accuracy (φ n)+
        max (bourgainSmallExponent σ τ α χ+F.accuracy (φ n))
          (2*F.accuracy (φ n)+Real.logb (F.pattern (φ n)).N
            ((F.retained (φ n)).card : ℝ)))
      atTop (nhds (max (bourgainSmallExponent σ τ α χ) r)) := by
    simpa only [zero_add, add_zero, mul_zero] using
      he.add ((he.const_add (bourgainSmallExponent σ τ α χ)).max ((he.const_mul 2).add hr))
  have hρr : ρ ≤ max (bourgainSmallExponent σ τ α χ) r :=
    le_of_tendsto_of_tendsto hsource hpackLim (Eventually.of_forall fun n => F.packing (φ n))
  have hrEq : r = ρ := by
    apply le_antisymm hrle
    rcases le_max_iff.mp hρr with hsmall | hlarge
    · exact False.elim (not_le_of_gt hgap hsmall)
    · exact hlarge
  have hleft₁ : Tendsto
      (fun n => -2*α+2*σ+Real.logb (F.pattern (φ n)).N
        ((bourgainIntegerSlice ((F.pattern (φ n)).N^(F.accuracy (φ n)/8))
          (F.localHeight (φ n)+(F.pattern (φ n)).N^(F.accuracy (φ n)/8)+1)
          (F.sliceValue (φ n)) (F.shift (φ n))).card : ℝ)+
        Real.logb (F.pattern (φ n)).N ((F.retained (φ n)).card : ℝ))
      atTop (nhds (-2*α+2*σ+x+r)) :=
    (hx.const_add (-2*α+2*σ)).add hr
  have hleft₂ : Tendsto
      (fun n => -α-χ/2+2*σ+Real.logb (F.pattern (φ n)).N
        ((bourgainIntegerSlice ((F.pattern (φ n)).N^(F.accuracy (φ n)/8))
          (F.localHeight (φ n)+(F.pattern (φ n)).N^(F.accuracy (φ n)/8)+1)
          (F.sliceValue (φ n)) (F.shift (φ n))).card : ℝ)/2+
        3*Real.logb (F.pattern (φ n)).N ((F.retained (φ n)).card : ℝ)/2)
      atTop (nhds (-α-χ/2+2*σ+x/2+3*r/2)) :=
    ((hx.div_const 2).const_add (-α-χ/2+2*σ)).add ((hr.const_mul 3).div_const 2)
  have hpairR : Tendsto (fun n => (τ, Real.logb (F.pattern (φ n)).N
      ((F.retained (φ n)).card : ℝ))) atTop (nhds (τ,r)) :=
    tendsto_const_nhds.prodMk_nhds hr
  have hpairX : Tendsto (fun n => (τ, Real.logb (F.pattern (φ n)).N
      ((bourgainIntegerSlice ((F.pattern (φ n)).N^(F.accuracy (φ n)/8))
        (F.localHeight (φ n)+(F.pattern (φ n)).N^(F.accuracy (φ n)/8)+1)
        (F.sliceValue (φ n)) (F.shift (φ n))).card : ℝ))) atTop (nhds (τ,x)) :=
    tendsto_const_nhds.prodMk_nhds hx
  have hBR := (bourgain_doubleZeta_exponent_continuous.tendsto (τ,r)).comp hpairR
  have hBX := (bourgain_doubleZeta_exponent_continuous.tendsto (τ,x)).comp hpairX
  have hright := ((he.const_mul (2*τ-χ+12)).add (hBR.div_const 2)).add (hBX.div_const 2)
  simp only [mul_zero, zero_add] at hright
  have hresult := le_of_tendsto_of_tendsto (hleft₁.max hleft₂) hright
    (Eventually.of_forall fun n => F.comparison (φ n))
  exact ⟨x, hx0, by simpa only [hrEq] using hresult⟩

/-- The complete zero-loss dichotomy in the proved physical source range.
The actual realizing family and its large branch are constructed internally. -/
theorem InCardinalityEnergyRegion.bourgain_log_dichotomy
    {σ τ ρ energy χ α : ℝ}
    (hregion : InCardinalityEnergyRegion σ τ ρ energy)
    (hσ : 3/4 < σ) (hχ : 0 ≤ χ) (hmargin : 1 < τ-χ) :
    ρ ≤ bourgainSmallExponent σ τ α χ ∨
      ∃ x : ℝ, 0 ≤ x ∧
        max (-2*α+2*σ+x+ρ) (-α-χ/2+2*σ+x/2+3*ρ/2) ≤
          heathBrownDoubleZetaExponent τ ρ/2+heathBrownDoubleZetaExponent τ x/2 := by
  by_cases hsmall : ρ ≤ bourgainSmallExponent σ τ α χ
  · exact Or.inl hsmall
  · have hgap := lt_of_not_ge hsmall
    obtain ⟨F⟩ := exists_bourgain_diagonal_family hregion hσ hχ hmargin hgap
    exact Or.inr (F.source_witness hgap)

end TaoTrudgianYang2025
