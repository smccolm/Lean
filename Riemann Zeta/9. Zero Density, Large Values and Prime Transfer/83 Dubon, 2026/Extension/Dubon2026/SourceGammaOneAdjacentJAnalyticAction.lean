import Dubon2026.SourceGammaOneUpperHalfPlaneHeckeGerms
import Dubon2026.SourceGammaOneAdjacentJAutomorphism
import Dubon2026.SourceGammaOneAdjacentJDiamondAction

/-! DUB-17/18 -> original Gamma1 Frobenius norm -> exact diamond term.
The actual adjacent-j automorphism is identified analytically on the
proved generating field. The matrix calculation identifies the second
generator; native quotient invariance identifies the whole lower field.
This avoids any extra automorphism-extension or analytic-action premise. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane Filter CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups Topology
variable (M p : ℕ) [NeZero M] [Fact p.Prime]
local notation "Γ" => Gamma1 M ⊓ Gamma0 (p * M)
local notation "FF" => x1FunctionField M
local notation "GG" => x1x0FunctionFieldC ℚ M (p * M)

omit [NeZero M] in
theorem adjacentJ_realize_base_eventuallyEq
    (w : GG ≃ₐ[ℚ] GG)
    (hbase : ∀ (z : FF) (hz : (z : LaurentSeries ℚ) ∈ GG),
      (w ⟨z, hz⟩ : LaurentSeries ℚ) = qExpand ℚ p z.val)
    (γ : Gamma1 M) (z : FF) (hz : (z : LaurentSeries ℚ) ∈ GG) (τ : ℍ) :
    realize Γ (coeffEmb ℂ (w ⟨z, hz⟩)) =ᶠ[𝓝[≠] τ]
      fun t => realize Γ (coeffEmb ℂ z) (γ.val • (levelRaiseMatrix p • t)) := by
  rw [hbase z hz]
  have hH : ModularGroup.T ∈ Γ := by simp [Gamma1_mem, Gamma0_mem, ModularGroup.T]
  let W : GL (Fin 2) ℝ := (γ.val : GL (Fin 2) ℝ) * levelRaiseMatrix p
  have htW : Tendsto (fun t : ℍ => W • t) (𝓝[≠] τ) (𝓝[≠] (W • τ)) :=
    le_of_eq ((Homeomorph.smul W).map_punctured_nhds_eq τ)
  have htD : Tendsto (fun t : ℍ => levelRaiseMatrix p • t) (𝓝[≠] τ)
      (𝓝[≠] (levelRaiseMatrix p • τ)) :=
    le_of_eq ((Homeomorph.smul (levelRaiseMatrix p)).map_punctured_nhds_eq τ)
  let f := rationalComplexMap (Gamma1 M) z
  have hb : (heckeBeta ℂ M p f : LaurentSeries ℂ) = coeffEmb ℂ (qExpand ℚ p z.val) := by
    rw [heckeBeta_coe]
    exact (coeffMap_qExpand (algebraMap ℚ ℂ) p z.val).symm
  have hbeta := realize_heckeBeta_upperHalfPlane_eventuallyEq M p hH.1 hH f τ
  rw [hb] at hbeta
  have hr := (realize_restrict_upperHalfPlane_eventuallyEq inf_le_left hH f
    (W • τ)).comp_tendsto htW
  have hi := (realize_smul_upperHalfPlane_eventuallyEq hH.1 f γ
    (levelRaiseMatrix p • τ)).comp_tendsto htD
  filter_upwards [hbeta, hr, hi] with t hb' hr' hi'
  simp only [Function.comp_apply, W, mul_smul] at hr'
  exact hb'.trans (hi'.symm.trans hr'.symm)

omit [NeZero M] in
theorem adjacentJ_realize_j_eventuallyEq
    (w : GG ≃ₐ[ℚ] GG)
    (hj : (w ⟨qExpand ℚ p jq, adjacentJ_mem_correspondence M p⟩ : LaurentSeries ℚ) = jq)
    (γ : Gamma1 M) (hd : (p : ℤ) ∣ γ.val 1 1) (τ : ℍ) :
    realize Γ (coeffEmb ℂ (w ⟨qExpand ℚ p jq, adjacentJ_mem_correspondence M p⟩))
      =ᶠ[𝓝[≠] τ] fun t => realize Γ (coeffEmb ℂ (qExpand ℚ p jq))
        (γ.val • (levelRaiseMatrix p • t)) := by
  rw [hj]
  have hH : ModularGroup.T ∈ Γ := by simp [Gamma1_mem, Gamma0_mem, ModularGroup.T]
  let W : GL (Fin 2) ℝ := (γ.val : GL (Fin 2) ℝ) * levelRaiseMatrix p
  have htW : Tendsto (fun t : ℍ => W • t) (𝓝[≠] τ) (𝓝[≠] (W • τ)) :=
    le_of_eq ((Homeomorph.smul W).map_punctured_nhds_eq τ)
  have hr := (realize_adjacentJ_upperHalfPlane_eventuallyEq M p hH (W • τ)).comp_tendsto htW
  filter_upwards [hr] with t ht
  simp only [Function.comp_apply, W, mul_smul] at ht
  change realize Γ (jCoordinateOver Γ ℂ : LaurentSeries ℂ) t = _
  rw [realize_jCoordinateOver hH]
  calc
    JMultiplicity.jf t = JMultiplicity.jf
        (levelRaiseMatrix p • (γ.val • (levelRaiseMatrix p • t))) := by
      rw [adjacentJDiamondMatrix_smul p γ.val hd, JMultiplicity.jf_smul]
    _ = _ := ht.symm

theorem adjacentJ_realize_upperHalfPlane_eventuallyEq (hcop : Nat.Coprime M p)
    (w : GG ≃ₐ[ℚ] GG)
    (hbase : ∀ (z : FF) (hz : (z : LaurentSeries ℚ) ∈ GG),
      (w ⟨z, hz⟩ : LaurentSeries ℚ) = qExpand ℚ p z.val)
    (hj : (w ⟨qExpand ℚ p jq, adjacentJ_mem_correspondence M p⟩ : LaurentSeries ℚ) = jq)
    (γ : Gamma1 M) (hd : (p : ℤ) ∣ γ.val 1 1) (x : GG) (τ : ℍ) :
    realize Γ (coeffEmb ℂ (w x)) =ᶠ[𝓝[≠] τ]
      fun z => realize Γ (coeffEmb ℂ x) (γ.val • (levelRaiseMatrix p • z)) := by
  let wr : GG →+* GG := w.toRingHom
  letI := upperHalfPlaneGermRatAlgebra τ
  letI : Algebra ℚ GG := (GG).toSubalgebra.algebra
  have hH : ModularGroup.T ∈ Γ := by simp [Gamma1_mem, Gamma0_mem, ModularGroup.T]
  let W : GL (Fin 2) ℝ := (γ.val : GL (Fin 2) ℝ) * levelRaiseMatrix p
  have htW : Tendsto (fun z : ℍ => W • z) (𝓝[≠] τ) (𝓝[≠] (W • τ)) :=
    le_of_eq ((Homeomorph.smul W).map_punctured_nhds_eq τ)
  let lhs : GG →+* Germ (𝓝[≠] τ) ℂ := (rationalAnalyticGerm Γ hH τ).comp wr
  let rhs : GG →+* Germ (𝓝[≠] τ) ℂ := (germPullback (fun z : ℍ => W • z) htW).comp
    (rationalAnalyticGerm Γ hH (W • τ))
  have he : lhs.toRatAlgHom = rhs.toRatAlgHom := by
    apply IntermediateField.algHom_ext_of_eq_adjoin ℚ (gammaOne_adjacentJ_generation M p hcop)
    intro z hz
    rcases hz with hz | rfl
    · change (realize Γ (coeffEmb ℂ (w ⟨z, _⟩)) : Germ (𝓝[≠] τ) ℂ) =
        ((fun t => realize Γ (coeffEmb ℂ z) (W • t)) : Germ (𝓝[≠] τ) ℂ)
      apply Germ.coe_eq.mpr
      simpa only [W, mul_smul] using
        adjacentJ_realize_base_eventuallyEq M p w hbase γ ⟨z, hz⟩ _ τ
    · change (realize Γ (coeffEmb ℂ (w ⟨qExpand ℚ p jq, _⟩)) : Germ (𝓝[≠] τ) ℂ) =
        ((fun t => realize Γ (coeffEmb ℂ (qExpand ℚ p jq)) (W • t)) : Germ (𝓝[≠] τ) ℂ)
      apply Germ.coe_eq.mpr
      simpa only [W, mul_smul] using adjacentJ_realize_j_eventuallyEq M p w hj γ hd τ
  apply Germ.coe_eq.mp
  have hx := DFunLike.congr_fun he x
  change (realize Γ (coeffEmb ℂ (w x)) : Germ (𝓝[≠] τ) ℂ) =
    ((fun z => realize Γ (coeffEmb ℂ x) (W • z)) : Germ (𝓝[≠] τ) ℂ) at hx
  simpa only [W, mul_smul] using hx

end
end Dubon2026.SourceFunctionField.GammaOne
