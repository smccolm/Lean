import Dubon2026.SourceSubgroupStabilizerCharacter
import Mathlib.Analysis.Meromorphic.Order

/-! DUB-17/18 -> numerical modular genus -> actual normalized ramification
equals half the Gamma0 stabilizer cardinality. The stabilizer character is
the actual Mobius denominator. Its injectivity and finite cyclic image
turn invariance of meromorphic germs into divisibility of their orders.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, selected proofs from
S_ModularCurve_ComplexPlaceDictionary_two_mul_ramification_eq_card_stabilizer
and S_UpperHalfPlane_natCard_stabilizer_dvd_two_mul_of_meromorphicOrderAt_eq.
-/
namespace Dubon2026.SourceFunctionField.SubgroupStabilizer
noncomputable section
open UpperHalfPlane Filter
open scoped MatrixGroups Topology
theorem num_mul_denom_sub (g : GL (Fin 2) ℝ) (z w : ℂ) :
    num g z * denom g w - denom g z * num g w = (g.val.det : ℝ) * (z - w) := by
  simp only [num, denom, Matrix.det_fin_two]
  push_cast
  ring

theorem det_coe_SL (γ : SL(2, ℤ)) : ((γ : GL (Fin 2) ℝ).val.det : ℝ) = 1 :=
  Matrix.SpecialLinearGroup.det_coe _

/-- The Mobius rational function in a complex coordinate. -/
def moeb (γ : SL(2, ℤ)) (z : ℂ) : ℂ := num (γ : GL (Fin 2) ℝ) z / denom (γ : GL (Fin 2) ℝ) z

theorem coe_smul_eq_moeb (γ : SL(2, ℤ)) (z : ℍ) : ((γ • z : ℍ) : ℂ) = moeb γ z := by
  rw [ModularGroup.sl_moeb, coe_smul_of_det_pos (by simp)]; rfl

theorem moeb_sub (γ : SL(2, ℤ)) (τ : ℍ) (hγ : γ • τ = τ) (z : ℂ)
    (hz : denom (γ : GL (Fin 2) ℝ) z ≠ 0) :
    moeb γ z - τ = (z - τ) / (denom (γ : GL (Fin 2) ℝ) z * denom (γ : GL (Fin 2) ℝ) τ) := by
  have hτ : (τ : ℂ) = moeb γ τ := by rw [← coe_smul_eq_moeb, hγ]
  conv_lhs => rw [hτ]
  simp only [moeb]
  rw [div_sub_div _ _ hz (denom_ne_zero _ τ), num_mul_denom_sub, det_coe_SL]
  push_cast
  ring

theorem continuousAt_moeb (γ : SL(2, ℤ)) (τ : ℍ) : ContinuousAt (moeb γ) τ := by
  apply ContinuousAt.div
  · exact (continuous_const.mul continuous_id).add continuous_const |>.continuousAt
  · exact (continuous_const.mul continuous_id).add continuous_const |>.continuousAt
  · exact denom_ne_zero _ τ

theorem continuous_denom (g : GL (Fin 2) ℝ) : Continuous (fun z : ℂ => denom g z) :=
  (continuous_const.mul continuous_id).add continuous_const

theorem chi_zpow_eq_one (Γ : Subgroup SL(2, ℤ)) (F : ℍ → ℂ)
    (hF : ∀ γ ∈ Γ, ∀ τ : ℍ, F (γ • τ) = F τ) (τ : ℍ) (n : ℤ)
    (g : ℂ → ℂ) (hg : AnalyticAt ℂ g τ) (hg0 : g τ ≠ 0)
    (hfg : ∀ᶠ z in 𝓝[≠] (τ : ℂ), F (ofComplex z) = (z - τ) ^ n • g z)
    (γ : MulAction.stabilizer Γ τ) :
    chi Γ τ γ ^ (2 * n) = 1 := by
  set γ₀ : SL(2, ℤ) := ((γ : Γ) : SL(2, ℤ)) with hγ₀
  have hfix : γ₀ • τ = τ := γ.2
  set d : ℂ → ℂ := fun z => denom (γ₀ : GL (Fin 2) ℝ) z with hd
  have hdτ : d τ ≠ 0 := denom_ne_zero _ τ
  have hmoebτ : moeb γ₀ τ = τ := by rw [← coe_smul_eq_moeb, hfix]

  have him : ∀ᶠ z in 𝓝[≠] (τ : ℂ), 0 < z.im :=
    eventually_nhdsWithin_of_eventually_nhds
      ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds τ.im_pos)

  have hmt : Tendsto (moeb γ₀) (𝓝[≠] (τ : ℂ)) (𝓝[≠] (τ : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h := (continuousAt_moeb γ₀ τ).tendsto
      rw [hmoebτ] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [him, self_mem_nhdsWithin] with z hz hne
      have hdz : d z ≠ 0 := denom_ne_zero_of_im _ hz.ne'
      intro (habs : moeb γ₀ z = τ)
      have := moeb_sub γ₀ τ hfix z hdz
      rw [habs, sub_self, eq_comm, div_eq_zero_iff] at this
      rcases this with h | h
      · exact hne (sub_eq_zero.mp h)
      · exact mul_ne_zero hdz hdτ h

  have hkey : ∀ᶠ z in 𝓝[≠] (τ : ℂ),
      g z = (d z * d τ) ^ (-n) * g (moeb γ₀ z) := by
    filter_upwards [hfg, hmt.eventually hfg, him, self_mem_nhdsWithin] with z hz hmz hzi hne
    have hdz : d z ≠ 0 := denom_ne_zero_of_im _ hzi.ne'
    have hzτ : (z : ℂ) - τ ≠ 0 := sub_ne_zero.mpr hne

    have hinv : F (ofComplex (moeb γ₀ z)) = F (ofComplex z) := by
      have h1 : ofComplex z = (⟨z, hzi⟩ : ℍ) := by
        ext; exact congrArg _ (ofComplex_apply_of_im_pos hzi)
      have h2 : moeb γ₀ z = ((γ₀ • (⟨z, hzi⟩ : ℍ) : ℍ) : ℂ) := by
        rw [coe_smul_eq_moeb]
      rw [h2, ofComplex_apply, h1]
      exact hF γ₀ (γ : Γ).2 _
    rw [hmz, hz, moeb_sub γ₀ τ hfix z hdz, smul_eq_mul, smul_eq_mul, div_zpow,
      div_mul_eq_mul_div, div_eq_iff (zpow_ne_zero _ (mul_ne_zero hdz hdτ)), mul_assoc] at hinv
    have := mul_left_cancel₀ (zpow_ne_zero n hzτ) hinv

    rw [zpow_neg, eq_inv_mul_iff_mul_eq₀ (zpow_ne_zero _ (mul_ne_zero hdz hdτ)), this, mul_comm]

  have hlim1 : Tendsto g (𝓝[≠] (τ : ℂ)) (𝓝 (g τ)) :=
    hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hlim2 : Tendsto (fun z => (d z * d τ) ^ (-n) * g (moeb γ₀ z)) (𝓝[≠] (τ : ℂ))
      (𝓝 ((d τ * d τ) ^ (-n) * g τ)) := by
    apply Tendsto.mul
    · have hc : ContinuousAt (fun z => (d z * d τ) ^ (-n)) τ := by
        apply ContinuousAt.zpow₀
        · exact ((continuous_denom _).mul continuous_const).continuousAt
        · exact Or.inl (mul_ne_zero hdτ hdτ)
      exact hc.tendsto.mono_left nhdsWithin_le_nhds
    · have hm : Tendsto (moeb γ₀) (𝓝[≠] (τ : ℂ)) (𝓝 (τ : ℂ)) := by
        have h := (continuousAt_moeb γ₀ τ).tendsto
        rw [hmoebτ] at h
        exact h.mono_left nhdsWithin_le_nhds
      exact hg.continuousAt.tendsto.comp hm
  have heq := tendsto_nhds_unique (hlim1.congr' hkey) hlim2

  rw [eq_comm, mul_eq_right₀ hg0, zpow_neg, inv_eq_one] at heq
  rw [chi_apply, zpow_mul, zpow_two]
  exact heq

theorem main (Γ : Subgroup SL(2, ℤ)) (F : ℍ → ℂ) (hF : ∀ γ ∈ Γ, ∀ τ : ℍ, F (γ • τ) = F τ)
    (τ : ℍ) (n : ℤ)
    (hn : meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) = n) :
    (Nat.card (MulAction.stabilizer Γ τ) : ℤ) ∣ 2 * n := by
  by_cases hmer : MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ)
  · obtain ⟨g, hg, hg0, hfg⟩ := (meromorphicOrderAt_eq_int_iff hmer).mp hn
    exact card_dvd_of_forall_chi_zpow_eq_one Γ τ n
      (chi_zpow_eq_one Γ F hF τ n g hg hg0 hfg)
  · rw [meromorphicOrderAt_of_not_meromorphicAt hmer] at hn
    have : n = 0 := by exact_mod_cast hn.symm
    rw [this, mul_zero]
    exact dvd_zero _


end
end Dubon2026.SourceFunctionField.SubgroupStabilizer
