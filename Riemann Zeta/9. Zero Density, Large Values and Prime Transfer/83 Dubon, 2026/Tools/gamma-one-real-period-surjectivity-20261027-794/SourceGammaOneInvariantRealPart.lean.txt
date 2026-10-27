import Dubon2026.SourceCuspRealMaximum
import Dubon2026.SourcePeriodSlash
import Dubon2026.SourceGammaOneCuspAuxiliaryForm
import Mathlib.NumberTheory.Modular

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> original all-weight
arithmetic association -> actual finite Gamma1 Hecke characters -> Picard/H1
and modular periods -> injectivity of real periods. Adapt the already
proved finite-tile maximum argument to actual Gamma1. Existing principal
congruence normality supplies every cusp translation. This is required by
both candidate dimension routes; no dimension or surjectivity is assumed.
The local argument derives from anthropics/fermats-last-theorem,
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0. -/
namespace Dubon2026
noncomputable section
open UpperHalfPlane Filter Topology Complex Function ModularForm Metric Set CongruenceSubgroup
open scoped MatrixGroups Real CongruenceSubgroup ModularForm Manifold
variable {N : ℕ} [NeZero N]

omit [NeZero N] in
/-- Every original point lies in a translated finite fundamental-domain tile. -/
theorem sourceGamma1_exists_tile_translate (z : ℍ) :
    ∃ (q : SL(2, ℤ) ⧸ (Gamma1 N : Subgroup SL(2, ℤ))) (v : ℍ) (γ : SL(2, ℤ)),
      v ∈ ModularGroup.fd ∧ γ ∈ Gamma1 N ∧ z = γ • ((Quotient.out q)⁻¹ • v) := by
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z
  set q : SL(2, ℤ) ⧸ (Gamma1 N : Subgroup SL(2, ℤ)) := QuotientGroup.mk g with hq
  set s : SL(2, ℤ) := Quotient.out q with hs
  have hcoset : s⁻¹ * g ∈ (Gamma1 N : Subgroup SL(2, ℤ)) := by
    have hout : (QuotientGroup.mk s : SL(2, ℤ) ⧸ (Gamma1 N : Subgroup SL(2, ℤ)))
        = QuotientGroup.mk g := by
      rw [hs, hq]
      exact Quotient.out_eq _
    exact (QuotientGroup.eq).mp hout
  refine ⟨q, g • z, (s⁻¹ * g)⁻¹, hg, (Gamma1 N).inv_mem hcoset, ?_⟩
  have hcollapse : ((s⁻¹ * g)⁻¹ • ((Quotient.out q)⁻¹ • (g • z)) : ℍ) = z := by
    rw [← hs, smul_smul, smul_smul]
    have h1 : (s⁻¹ * g)⁻¹ * s⁻¹ * g = 1 := by group
    rw [h1, one_smul]
  exact hcollapse.symm

/-- A holomorphic primitive whose real part is invariant under the original Gamma1
and which has finite limits at every original cusp has constant real part. -/
theorem sourceGamma1_realPart_constant {φ φ' : ℍ → ℂ}
    (hφ : ∀ τ : ℍ, HasDerivAt (φ ∘ ofComplex) (φ' τ) ↑τ)
    (hinv : ∀ γ ∈ Gamma1 N, ∀ z : ℍ, (φ (γ • z)).re = (φ z).re)
    (hlim : ∀ δ : SL(2, ℤ), ∃ L : ℂ, Tendsto (fun w : ℍ => φ (δ • w)) atImInfty (𝓝 L))
    (z w : ℍ) : (φ z).re = (φ w).re := by
  classical

  set A : SL(2, ℤ) → ℂ := fun δ => (hlim δ).choose with hAdef
  have hA : ∀ δ : SL(2, ℤ), Tendsto (fun w : ℍ => φ (δ • w)) atImInfty (𝓝 (A δ)) :=
    fun δ => (hlim δ).choose_spec
  clear_value A

  have hthresh : ∀ (δ : SL(2, ℤ)) (ε : ℝ), 0 < ε →
      ∃ Y : ℝ, ∀ v : ℍ, Y ≤ v.im → ‖φ (δ • v) - A δ‖ ≤ ε := by
    intro δ ε hε
    have := (Metric.tendsto_nhds.mp (hA δ)) ε hε
    rw [Filter.eventually_iff, atImInfty_mem] at this
    obtain ⟨Y, hY⟩ := this
    refine ⟨Y, fun v hv => le_of_lt ?_⟩
    have := hY v hv
    simpa [dist_eq_norm] using this

  haveI : Nonempty (SL(2, ℤ) ⧸ (Gamma1 N : Subgroup SL(2, ℤ))) :=
    ⟨QuotientGroup.mk (1 : SL(2, ℤ))⟩

  set r : (SL(2, ℤ) ⧸ (Gamma1 N : Subgroup SL(2, ℤ))) → ℝ :=
    fun q => (A (Quotient.out q)⁻¹).re with hrdef
  obtain ⟨q₀, hq₀⟩ := Finite.exists_max r
  set R : ℝ := r q₀ with hRdef
  clear_value r R

  have hu_cont : Continuous fun z : ℍ => (φ z).re := by
    have h1 : Continuous fun z : ℍ => φ z := by
      rw [continuous_iff_continuousAt]
      intro z
      have h2 : ContinuousAt (φ ∘ ofComplex) (z : ℂ) := (hφ z).differentiableAt.continuousAt
      have heq : (fun z : ℍ => φ z) = (φ ∘ ofComplex) ∘ (fun z : ℍ => (z : ℂ)) := by
        funext w
        simp [ofComplex_apply]
      rw [heq]
      exact h2.comp continuous_coe.continuousAt
    exact Complex.continuous_re.comp h1

  suffices hsuff : ∃ z₀ : ℍ, ∀ ζ : ℍ, (φ ζ).re ≤ (φ z₀).re by
    obtain ⟨z₀, hz₀⟩ := hsuff
    have hd : DifferentiableOn ℂ (φ ∘ ofComplex) upperHalfPlaneSet :=
      fun x hx => (hφ ⟨x, hx⟩).differentiableAt.differentiableWithinAt
    have hm (x : ℂ) (hx : x ∈ upperHalfPlaneSet) :
        ((φ ∘ ofComplex) x).re ≤ ((φ ∘ ofComplex) (z₀ : ℂ)).re := by
      simpa only [Function.comp_apply, ofComplex_apply, ofComplex_apply_of_im_pos hx] using hz₀ ⟨x, hx⟩
    have he (v : ℍ) : (φ v).re = (φ z₀).re := by
      simpa only [Function.comp_apply, ofComplex_apply] using
        sourceHolomorphic_re_eq_of_isMaxOn isOpen_upperHalfPlaneSet
          (convex_halfSpace_im_gt 0).isPreconnected hd z₀.2 hm v.2
    exact (he z).trans (he w).symm
  by_cases hcase : ∃ ζ₀ : ℍ, R < (φ ζ₀).re
  ·

    obtain ⟨ζ₀, hζ₀⟩ := hcase
    set ε : ℝ := ((φ ζ₀).re - R) / 2 with hεdef
    have hε : 0 < ε := by
      rw [hεdef]
      linarith

    have hYq : ∀ q : SL(2, ℤ) ⧸ (Gamma1 N : Subgroup SL(2, ℤ)), ∃ Y : ℝ, ∀ v : ℍ, Y ≤ v.im →
        ‖φ ((Quotient.out q)⁻¹ • v) - A (Quotient.out q)⁻¹‖ ≤ ε :=
      fun q => hthresh (Quotient.out q)⁻¹ ε hε
    set Yf : (SL(2, ℤ) ⧸ (Gamma1 N : Subgroup SL(2, ℤ))) → ℝ := fun q => (hYq q).choose with hYfdef
    have hYfspec : ∀ q : SL(2, ℤ) ⧸ (Gamma1 N : Subgroup SL(2, ℤ)), ∀ v : ℍ, Yf q ≤ v.im →
        ‖φ ((Quotient.out q)⁻¹ • v) - A (Quotient.out q)⁻¹‖ ≤ ε :=
      fun q => (hYq q).choose_spec
    obtain ⟨qY, hqY⟩ := Finite.exists_max Yf
    set Y : ℝ := Yf qY with hYdef

    set C : Set ℍ := (⋃ q : SL(2, ℤ) ⧸ (Gamma1 N : Subgroup SL(2, ℤ)), (fun v : ℍ => (Quotient.out q)⁻¹ • v) ''
        (ModularGroup.truncatedFundamentalDomain Y)) ∪ {ζ₀} with hCdef
    have hC_compact : IsCompact C := by
      apply IsCompact.union
      · apply isCompact_iUnion
        intro q
        exact (ModularGroup.isCompact_truncatedFundamentalDomain Y).image
          (show Continuous (fun v : ℍ => (Quotient.out q)⁻¹ • v) from
            continuous_const_smul (Matrix.SpecialLinearGroup.mapGL ℝ (Quotient.out q)⁻¹))
      · exact isCompact_singleton
    have hC_nonempty : C.Nonempty := ⟨ζ₀, Set.mem_union_right _ rfl⟩
    obtain ⟨z₀, hz₀C, hz₀max⟩ := hC_compact.exists_isMaxOn hC_nonempty
      (hu_cont.continuousOn)
    refine ⟨z₀, fun ζ => ?_⟩

    obtain ⟨q, v, γ, hvfd, hγ, hζeq⟩ := sourceGamma1_exists_tile_translate (N := N) ζ
    have hval : (φ ζ).re = (φ ((Quotient.out q)⁻¹ • v)).re := by
      rw [hζeq]
      exact hinv γ hγ _
    by_cases hsplit : v.im ≤ Y
    ·
      have hmem : ((Quotient.out q)⁻¹ • v) ∈ C := by
        rw [hCdef]
        exact Set.mem_union_left _
          (Set.mem_iUnion.mpr ⟨q, Set.mem_image_of_mem _ ⟨hvfd, hsplit⟩⟩)
      rw [hval]
      exact hz₀max hmem
    ·
      push Not at hsplit
      have hvY : Yf q ≤ v.im := le_trans (hqY q) (le_of_lt hsplit)
      have hclose := hYfspec q v hvY
      have hre_le : (φ ((Quotient.out q)⁻¹ • v)).re ≤ r q + ε := by
        have h1 : (φ ((Quotient.out q)⁻¹ • v)).re - (A (Quotient.out q)⁻¹).re
            ≤ ‖φ ((Quotient.out q)⁻¹ • v) - A (Quotient.out q)⁻¹‖ := by
          have habs := Complex.abs_re_le_norm (φ ((Quotient.out q)⁻¹ • v) - A (Quotient.out q)⁻¹)
          rw [Complex.sub_re] at habs
          calc (φ ((Quotient.out q)⁻¹ • v)).re - (A (Quotient.out q)⁻¹).re
              ≤ |(φ ((Quotient.out q)⁻¹ • v)).re - (A (Quotient.out q)⁻¹).re| := le_abs_self _
            _ ≤ _ := habs
        simp only [hrdef]
        linarith
      have hζ₀C : ζ₀ ∈ C := Set.mem_union_right _ rfl
      have : (φ ((Quotient.out q)⁻¹ • v)).re ≤ (φ ζ₀).re := by
        have hrR : r q ≤ R := hq₀ q
        linarith
      rw [hval]
      exact le_trans this (hz₀max hζ₀C)
  · push Not at hcase
    let δ : SL(2, ℤ) := (Quotient.out q₀)⁻¹
    let Φ : ℍ → ℂ := fun τ => φ (δ • τ)
    have hΦ : ∀ τ : ℍ, HasDerivAt (Φ ∘ ofComplex)
        ((φ' ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ δ)) τ) (τ : ℂ) := by
      intro τ
      simpa only [Φ, Function.comp_def, ofComplex_apply] using
        sourceHasDerivAt_comp_smul hφ
          (g := Matrix.SpecialLinearGroup.mapGL ℝ δ)
          (by
            change 0 < ((δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ)).det
            rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, δ.det_coe, map_one]
            exact zero_lt_one) τ
    have hper (τ : ℍ) : (Φ ((N : ℝ) +ᵥ τ)).re = (Φ τ).re := by
      have hT : ((N : ℝ) +ᵥ τ) = ModularGroup.T ^ (N : ℤ) • τ := by
        rw [UpperHalfPlane.modular_T_zpow_smul]
        norm_num
      have hs : δ • ((N : ℝ) +ᵥ τ) =
          (δ * ModularGroup.T ^ (N : ℤ) * δ⁻¹) • (δ • τ) := by
        rw [hT, smul_smul, smul_smul]
        congr 1
        group
      change (φ (δ • ((N : ℝ) +ᵥ τ))).re = (φ (δ • τ)).re
      rw [hs]
      apply hinv
      exact SourceFunctionField.GammaOne.CuspAuxiliary.conj_T_pow_mem N
        (by intro a ha; simp_all [Gamma1_mem, Gamma_mem]) δ
    have hN : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (NeZero.pos N)
    have hR : (A δ).re = R := by simp only [δ, hRdef, hrdef]
    have hm (τ : ℍ) : (Φ τ).re ≤ (A δ).re := by
      rw [hR]
      exact hcase (δ • τ)
    have hc := sourceUpperHalfPlane_re_eq_of_cusp_max hN (A δ) hΦ hper (hA δ) hm
    refine ⟨δ • UpperHalfPlane.I, fun ζ => ?_⟩
    have hζ := hc (δ⁻¹ • ζ)
    have hI := hc UpperHalfPlane.I
    simpa only [Φ, smul_inv_smul] using hζ.le.trans hI.symm.le

end
end Dubon2026
