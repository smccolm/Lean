import Dubon2026.SourceMeromorphicPrimitiveCusps

/-! DUB17/18 -> actual Gamma1 Picard/H1 -> principal-divisor converse ->
actual meromorphic construction -> analytic differential input. Fill only
removable point values, preserving the actual residue germ, weight-two
slash invariance and exponential cusp decay. The existing native modular
action lemmas are reused. No finite-divisor or two-point assembly is repeated. -/
namespace Dubon2026.SourceMeromorphicDifferentialRegularization
noncomputable section
open UpperHalfPlane Filter Set SourceMeromorphicPrimitiveMultiplier
open scoped MatrixGroups Topology ModularForm

/-- Weight-two invariance under the actual subgroup. -/
def Inv (Γ : Subgroup SL(2, ℤ)) (ω : ℍ → ℂ) : Prop := ∀ γ ∈ Γ, ω ∣[(2 : ℤ)] γ = ω

/-- Exponential decay at every actual translated cusp. -/
def Cusp (ω : ℍ → ℂ) : Prop :=
  ∀ σ : SL(2, ℤ), ∃ δ : ℝ, 0 < δ ∧
    (ω ∣[(2 : ℤ)] σ) =O[atImInfty] fun τ : ℍ => Real.exp (-δ * τ.im)

/-- The exact local residue expansion of the actual differential coefficient. -/
def Loc (ω : ℍ → ℂ) (ρ : ℍ → ℂ) : Prop :=
  ∀ τ : ℍ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
    ∀ᶠ z in 𝓝[≠] (τ : ℂ), ω (ofComplex z) = ρ τ / (z - τ) + g z

theorem eventually_im_pos (τ : ℍ) : ∀ᶠ z in 𝓝[≠] (τ : ℂ), 0 < z.im :=
  mem_nhdsWithin_of_mem_nhds (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)

theorem im_ofComplex_of_im_pos {z : ℂ} (hz : 0 < z.im) : (ofComplex z : ℍ).im = z.im := by
  rw [ofComplex_apply_of_im_pos hz]
  rfl

/-- A removable limit in the actual upper-half-plane complex coordinate. -/
def HasLim (ω : ℍ → ℂ) (τ : ℍ) (L : ℂ) : Prop :=
  Tendsto (fun z : ℂ => ω (ofComplex z)) (𝓝[≠] (τ : ℂ)) (𝓝 L)

open Classical in

/-- Fill a removable value by its unique limit; preserve other values. -/
def reg (ω : ℍ → ℂ) (τ : ℍ) : ℂ := if h : ∃ L, HasLim ω τ L then h.choose else ω τ

theorem reg_eq_of_hasLim {ω : ℍ → ℂ} {τ : ℍ} {L : ℂ} (h : HasLim ω τ L) : reg ω τ = L := by
  have hex : ∃ L, HasLim ω τ L := ⟨L, h⟩
  rw [reg, dif_pos hex]
  exact tendsto_nhds_unique hex.choose_spec h

theorem reg_eq_of_not {ω : ℍ → ℂ} {τ : ℍ} (h : ¬ ∃ L, HasLim ω τ L) : reg ω τ = ω τ := by
  rw [reg, dif_neg h]

theorem hasLim_slash {ω : ℍ → ℂ} (σ : SL(2, ℤ)) (τ : ℍ) {L : ℂ} (h : HasLim ω (σ • τ) L) :
    HasLim (ω ∣[(2 : ℤ)] σ) τ
      (L * denom (Matrix.SpecialLinearGroup.mapGL ℝ σ) ↑τ ^ (-2 : ℤ)) := by
  have hev : ∀ᶠ z in 𝓝[≠] (τ : ℂ), (ω ∣[(2 : ℤ)] σ) (ofComplex z) =
      ω (ofComplex (μ σ z)) * denom (Matrix.SpecialLinearGroup.mapGL ℝ σ) z ^ (-2 : ℤ) := by
    filter_upwards [eventually_im_pos τ] with z hz
    rw [slash_two_apply, ofComplex_apply_of_im_pos hz, μ_of_im_pos σ hz, ofComplex_apply]
  refine Tendsto.congr' (EventuallyEq.symm hev) ?_
  refine (h.comp (tendsto_μ_nhdsNE σ τ)).mul ?_
  exact (((continuous_denom _).continuousAt.zpow₀ _ (Or.inl (denom_ne_zero _ τ))).tendsto).mono_left
    nhdsWithin_le_nhds

theorem inv_reg {Γ : Subgroup SL(2, ℤ)} {ω : ℍ → ℂ} (hω : Inv Γ ω) : Inv Γ (reg ω) := by
  intro γ hγ
  funext τ
  rw [slash_two_apply]
  by_cases h : ∃ L, HasLim ω (γ • τ) L
  · obtain ⟨L, hL⟩ := h
    have h1 : HasLim ω τ (L * denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) ↑τ ^ (-2 : ℤ)) := by
      have := hasLim_slash γ τ hL
      rwa [hω γ hγ] at this
    rw [reg_eq_of_hasLim hL, reg_eq_of_hasLim h1]
  · have h' : ¬ ∃ L, HasLim ω τ L := by
      rintro ⟨L, hL⟩
      apply h
      have hL' : HasLim ω (γ⁻¹ • (γ • τ)) L := by rwa [inv_smul_smul]
      have := hasLim_slash γ⁻¹ (γ • τ) hL'
      rw [hω γ⁻¹ (Subgroup.inv_mem _ hγ)] at this
      exact ⟨_, this⟩
    rw [reg_eq_of_not h, reg_eq_of_not h', ← slash_two_apply, hω γ hγ]

theorem cusp_reg {ω : ℍ → ℂ} (hω : Cusp ω) : Cusp (reg ω) := by
  intro σ
  obtain ⟨δ, hδ, hO⟩ := hω σ
  obtain ⟨C, hC⟩ := hO.bound
  obtain ⟨A, hA⟩ := (atImInfty_mem _).mp hC
  refine ⟨δ, hδ, Asymptotics.IsBigO.of_bound C ?_⟩
  rw [Filter.Eventually, atImInfty_mem]
  refine ⟨A + 1, fun τ hτ => ?_⟩
  have hAτ : A < τ.im := by linarith
  show ‖(reg ω ∣[(2 : ℤ)] σ) τ‖ ≤ C * ‖Real.exp (-δ * τ.im)‖
  rw [slash_two_apply]
  by_cases h : ∃ L, HasLim ω (σ • τ) L
  · obtain ⟨L, hL⟩ := h
    rw [reg_eq_of_hasLim hL]
    have hlim := hasLim_slash σ τ hL
    have hf : Tendsto (fun z => ‖(ω ∣[(2 : ℤ)] σ) (ofComplex z)‖) (𝓝[≠] (τ : ℂ))
        (𝓝 ‖L * denom (Matrix.SpecialLinearGroup.mapGL ℝ σ) ↑τ ^ (-2 : ℤ)‖) := hlim.norm
    have hc : Continuous fun z : ℂ => C * ‖Real.exp (-δ * z.im)‖ := by fun_prop
    have hg : Tendsto (fun z : ℂ => C * ‖Real.exp (-δ * (ofComplex z : ℍ).im)‖) (𝓝[≠] (τ : ℂ))
        (𝓝 (C * ‖Real.exp (-δ * τ.im)‖)) := by
      refine ((hc.tendsto (τ : ℂ)).mono_left nhdsWithin_le_nhds).congr' ?_
      filter_upwards [eventually_im_pos τ] with z hz
      rw [im_ofComplex_of_im_pos hz]
    refine le_of_tendsto_of_tendsto hf hg ?_
    have hopen : IsOpen {z : ℂ | A < z.im} := isOpen_lt continuous_const Complex.continuous_im
    filter_upwards [eventually_im_pos τ, mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds hAτ)]
      with z hz hzA
    exact hA (ofComplex z) (by rw [im_ofComplex_of_im_pos hz]; exact le_of_lt hzA)
  · rw [reg_eq_of_not h, ← slash_two_apply]
    exact hA τ hAτ.le

theorem reg_ofComplex_eventuallyEq {ω : ℍ → ℂ} {τ : ℍ} {a : ℂ} {g : ℂ → ℂ}
    (hg : AnalyticAt ℂ g τ)
    (he : ∀ᶠ z in 𝓝[≠] (τ : ℂ), ω (ofComplex z) = a / (z - τ) + g z) :
    ∀ᶠ z in 𝓝[≠] (τ : ℂ), reg ω (ofComplex z) = ω (ofComplex z) := by
  have h1 : ∀ᶠ z in 𝓝 (τ : ℂ), AnalyticAt ℂ g z := hg.eventually_analyticAt
  have h2 : ∀ᶠ z in 𝓝 (τ : ℂ), ∀ᶠ w in 𝓝 z, w ≠ (τ : ℂ) → ω (ofComplex w) = a / (w - τ) + g w :=
    (eventually_nhdsWithin_iff.mp he).eventually_nhds
  have h3 : ∀ᶠ z in 𝓝 (τ : ℂ), 0 < z.im := isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos
  rw [eventually_nhdsWithin_iff]
  filter_upwards [h1, h2, h3] with z hz1 hz2 hz3 hzτ
  apply reg_eq_of_hasLim
  have hF : ContinuousAt (fun w => a / (w - τ) + g w) z :=
    (continuousAt_const.div (continuousAt_id.sub continuousAt_const) (sub_ne_zero.mpr hzτ)).add
      hz1.continuousAt
  have hev : (fun w => ω (ofComplex w)) =ᶠ[𝓝 z] fun w => a / (w - τ) + g w := by
    filter_upwards [hz2, isOpen_ne.mem_nhds hzτ] with w hw hwτ
    exact hw hwτ
  have hlim : Tendsto (fun w => ω (ofComplex w)) (𝓝 z) (𝓝 (ω (ofComplex z))) := by
    rw [show ω (ofComplex z) = a / (z - τ) + g z from hev.self_of_nhds]
    exact hF.tendsto.congr' hev.symm
  show Tendsto _ (𝓝[≠] ((ofComplex z : ℍ) : ℂ)) _
  rw [coe_ofComplex_of_im_pos hz3]
  exact hlim.mono_left nhdsWithin_le_nhds

theorem loc_reg {ω ρ : ℍ → ℂ} (h : Loc ω ρ) (τ : ℍ) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g τ ∧
      (∀ᶠ z in 𝓝[≠] (τ : ℂ), reg ω (ofComplex z) = ρ τ / (z - τ) + g z) ∧
      (ρ τ = 0 → reg ω τ = g τ) := by
  obtain ⟨g, hg, he⟩ := h τ
  refine ⟨g, hg, ?_, fun h0 => ?_⟩
  · filter_upwards [reg_ofComplex_eventuallyEq hg he, he] with z h1 h2
    rw [h1, h2]
  · apply reg_eq_of_hasLim
    have hev : (fun z => ω (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)] g := by
      filter_upwards [he] with z hz
      rw [hz, h0, zero_div, zero_add]
    exact ((hg.continuousAt.tendsto).mono_left nhdsWithin_le_nhds).congr' hev.symm


theorem exists_regularized_differential (Γ : Subgroup SL(2, ℤ))
    (m : ℍ → ℤ) (ω : ℍ → ℂ) (hinv : Inv Γ ω) (hcusp : Cusp ω)
    (hloc : Loc ω (fun τ => (m τ : ℂ))) :
    ∃ ω₁ : ℍ → ℂ, Inv Γ ω₁ ∧ Cusp ω₁ ∧
      ∀ τ : ℍ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
        (∀ᶠ z in 𝓝[≠] (τ : ℂ), ω₁ (ofComplex z) = (m τ : ℂ) / (z - τ) + g z) ∧
        (m τ = 0 → ω₁ τ = g τ) := by
  refine ⟨reg ω, inv_reg hinv, cusp_reg hcusp, fun τ => ?_⟩
  obtain ⟨g, hg, he, hv⟩ := loc_reg hloc τ
  exact ⟨g, hg, he, fun hm => hv (by simp only [hm, Int.cast_zero])⟩

end
end Dubon2026.SourceMeromorphicDifferentialRegularization
