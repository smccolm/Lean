import Dubon2026.SourceSmoothLocalModelRegularization
import Dubon2026.SourceSmoothDivisorInvarianceCusps

/-! DUB-17/18 -> full all-weight arithmetic association -> original Gamma1
Picard/H1 -> Abel-Jacobi converse -> analytic reciprocity -> filled comparison
quotient and its winding logarithm. Equal integer local orders cancel.
The existing removable-filling theorem gives the nonvanishing C1 quotient
without duplicating the source open-neighborhood limit argument. The quotient
is proved equal to the source limUnder at every actual upper-half-plane point.
The existing punctured action-limit theorem supplies invariance transport.
Adapted from the pinned Apache-2.0 winding-period source, scope 848. -/
namespace Dubon2026.SourceSmoothComparison
noncomputable section
open UpperHalfPlane hiding I
open Filter Complex Set SourceSmoothLocalModel SourceSmoothDivisor
open scoped MatrixGroups Topology Real

/-- Exact integer local models with a nonvanishing C1 factor on the upper half-plane. -/
def HasLocalModels (F : ℂ → ℂ) (n : ℍ → ℤ) : Prop :=
  ∀ τ : ℍ, ∃ Ψ : ℂ → ℂ, ContDiffAt ℝ 1 Ψ (τ : ℂ) ∧ Ψ τ ≠ 0 ∧
    F =ᶠ[𝓝 (τ : ℂ)] fun z => (z - τ) ^ (n τ) * Ψ z

/-- Removable filling of the actual quotient; proved equal to the source punctured limit. -/
def quot (Φ V : ℂ → ℂ) : ℂ → ℂ := regularize (fun w => Φ w / V w)

variable {Φ V : ℂ → ℂ} {n : ℍ → ℤ}

theorem quot_local (hΦ : HasLocalModels Φ n) (hV : HasLocalModels V n) (τ : ℍ) :
    ∃ R : ℂ → ℂ, ContDiffAt ℝ 1 R (τ : ℂ) ∧ R τ ≠ 0 ∧ (quot Φ V =ᶠ[𝓝 (τ : ℂ)] R) ∧
      (∀ᶠ w in 𝓝[≠] (τ : ℂ), V w ≠ 0 ∧ Φ w = R w * V w) ∧
      (n τ = 0 → ∀ᶠ w in 𝓝 (τ : ℂ), V w ≠ 0 ∧ Φ w = quot Φ V w * V w) := by
  obtain ⟨Ψ, hΨ, hΨ0, hΦe⟩ := hΦ τ
  obtain ⟨Θ, hΘ, hΘ0, hVe⟩ := hV τ
  let R : ℂ → ℂ := fun w => Ψ w * (Θ w)⁻¹
  have hRcd : ContDiffAt ℝ 1 R τ := hΨ.mul (hΘ.inv hΘ0)
  have hRτ : R τ ≠ 0 := mul_ne_zero hΨ0 (inv_ne_zero hΘ0)
  have hΘne : ∀ᶠ w in 𝓝 (τ : ℂ), Θ w ≠ 0 :=
    hΘ.continuousAt.eventually_ne hΘ0
  have hp : ∀ᶠ w in 𝓝[≠] (τ : ℂ), V w ≠ 0 ∧ Φ w = R w * V w := by
    filter_upwards [hΦe.filter_mono nhdsWithin_le_nhds,
      hVe.filter_mono nhdsWithin_le_nhds,
      hΘne.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with w h1 h2 h3 hne
    have hz : (w - τ) ^ (n τ) ≠ 0 := zpow_ne_zero _ (sub_ne_zero.2 hne)
    refine ⟨by rw [h2]; exact mul_ne_zero hz h3, ?_⟩
    rw [h1, h2]
    dsimp only [R]
    field_simp
  have hdiv : (fun w => Φ w / V w) =ᶠ[𝓝[≠] (τ : ℂ)] R := by
    filter_upwards [hp] with w hw
    rw [hw.2]
    exact mul_div_cancel_right₀ _ hw.1
  have hreg := regularize_eventuallyEq (k := (0 : ℤ))
    (by simpa only [zpow_zero, one_mul] using hdiv)
    (eventually_continuousAt hRcd) hRτ
  have hqR : quot Φ V =ᶠ[𝓝 (τ : ℂ)] R := by
    simpa only [quot, zpow_zero, one_mul] using hreg
  refine ⟨R, hRcd, hRτ, hqR, hp, ?_⟩
  intro hn0
  filter_upwards [hΦe, hVe, hΘne, hqR] with w h1 h2 h3 h4
  rw [hn0, zpow_zero, one_mul] at h1 h2
  refine ⟨by rw [h2]; exact h3, ?_⟩
  rw [h1, h2, h4]
  dsimp only [R]
  field_simp

theorem contDiffAt_quot (hΦ : HasLocalModels Φ n) (hV : HasLocalModels V n) (τ : ℍ) :
    ContDiffAt ℝ 1 (quot Φ V) (τ : ℂ) := by
  obtain ⟨R, hR, -, hqR, -⟩ := quot_local hΦ hV τ
  exact hR.congr_of_eventuallyEq hqR

theorem quot_ne_zero (hΦ : HasLocalModels Φ n) (hV : HasLocalModels V n) (τ : ℍ) :
    quot Φ V τ ≠ 0 := by
  obtain ⟨R, -, hR0, hqR, -⟩ := quot_local hΦ hV τ
  rwa [hqR.self_of_nhds]

theorem tendsto_div_quot (hΦ : HasLocalModels Φ n) (hV : HasLocalModels V n) (τ : ℍ) :
    Tendsto (fun w => Φ w / V w) (𝓝[≠] (τ : ℂ)) (𝓝 (quot Φ V τ)) := by
  obtain ⟨R, hR, -, hqR, hev, -⟩ := quot_local hΦ hV τ
  have h1 : (fun w => Φ w / V w) =ᶠ[𝓝[≠] (τ : ℂ)] R := by
    filter_upwards [hev] with w hw
    rw [hw.2]; field_simp [hw.1]
  rw [hqR.self_of_nhds]
  exact ((hR.continuousAt.tendsto).mono_left nhdsWithin_le_nhds).congr' h1.symm

theorem eventually_eq_quot_mul (hΦ : HasLocalModels Φ n) (hV : HasLocalModels V n) (τ : ℍ)
    (hn : n τ = 0) : ∀ᶠ w in 𝓝 (τ : ℂ), V w ≠ 0 ∧ Φ w = quot Φ V w * V w := by
  obtain ⟨R, -, -, -, -, h⟩ := quot_local hΦ hV τ
  exact h hn

theorem quot_smul (hΦ : HasLocalModels Φ n) (hV : HasLocalModels V n) {Γ : Subgroup SL(2, ℤ)}
    (hinvΦ : ∀ γ ∈ Γ, ∀ τ : ℍ, Φ ((γ • τ : ℍ) : ℂ) = Φ τ)
    (hinvV : ∀ γ ∈ Γ, ∀ τ : ℍ, V ((γ • τ : ℍ) : ℂ) = V τ)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) (τ : ℍ) :
    quot Φ V ((γ • τ : ℍ) : ℂ) = quot Φ V τ := by
  have hτ : 0 < (τ : ℂ).im := τ.im_pos

  have hsm : Tendsto (sm γ) (𝓝[≠] (τ : ℂ)) (𝓝[≠] ((γ • τ : ℍ) : ℂ)) := by
    simpa only [sm_coe] using SourceSmoothDivisor.Data.tendsto_sm_nhdsNE γ hτ
  have h1 := (tendsto_div_quot hΦ hV (γ • τ)).comp hsm
  have h2 : ((fun w => Φ w / V w) ∘ sm γ) =ᶠ[𝓝[≠] (τ : ℂ)] fun w => Φ w / V w := by
    have h1 : ∀ᶠ u in 𝓝[≠] (τ : ℂ), u ∈ upperHalfPlaneSet :=
      mem_nhdsWithin_of_mem_nhds (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)
    filter_upwards [h1] with u hu
    simp only [Function.comp, sm]
    rw [hinvΦ γ hγ, hinvV γ hγ, coe_ofComplex hu]
  exact tendsto_nhds_unique (h1.congr' h2) (tendsto_div_quot hΦ hV τ)

theorem quot_eq_limUnder (hΦ : HasLocalModels Φ n) (hV : HasLocalModels V n) (τ : ℍ) :
    quot Φ V τ = limUnder (𝓝[≠] (τ : ℂ)) (fun w => Φ w / V w) :=
  (tendsto_div_quot hΦ hV τ).limUnder_eq.symm


end
end Dubon2026.SourceSmoothComparison
