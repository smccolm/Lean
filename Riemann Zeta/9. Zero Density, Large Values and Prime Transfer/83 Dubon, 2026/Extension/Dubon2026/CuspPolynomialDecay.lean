import Dubon2026.ModularGamma0Domain
import Dubon2026.LatticeThetaFEPair

/-! # Polynomially weighted decay of genuine cusp Petersson densities -/

namespace Dubon2026

open UpperHalfPlane ModularGroup MeasureTheory Asymptotics Filter
open Matrix.SpecialLinearGroup ConjAct
open scoped MatrixGroups ModularForm Pointwise Topology

noncomputable section

/-- The actual Petersson density at every rational cusp has exponential decay in a standard cusp coordinate. -/
theorem petersson_slash_exp_decay {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    {k : ℤ} (f : CuspForm Γ k) (g : SL(2, ℤ)) :
    ∃ a > 0, (petersson k (⇑f ∣[k] g) (⇑f ∣[k] g)) =O[atImInfty]
      (fun z : ℍ => Real.exp (-a * z.im)) := by
  have : ((toConjAct (g : GL (Fin 2) ℝ)⁻¹) • Γ).IsArithmetic := by
    simpa [(show Rat.castHom ℝ = algebraMap ℚ ℝ by rfl), map_inv, map_mapGL]
      using Subgroup.IsArithmetic.conj Γ (mapGL ℚ g)⁻¹
  exact (CuspFormClass.zero_at_infty (CuspForm.translate f g)).petersson_exp_decay_left k _
    (CuspForm.translate f g)

/-- Every real polynomial weight times the true slashed cusp density stays bounded at infinity. -/
theorem petersson_slash_rpow_isBigO_one {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    {k : ℤ} (f : CuspForm Γ k) (g : SL(2, ℤ)) (σ : ℝ) :
    (fun z : ℍ => ‖petersson k (⇑f ∣[k] g) (⇑f ∣[k] g) z‖ * z.im ^ σ) =O[atImInfty]
      (fun _ : ℍ => (1 : ℝ)) := by
  obtain ⟨a, ha, hf⟩ := petersson_slash_exp_decay f g
  have h := hf.norm_left.mul (isBigO_refl (fun z : ℍ => z.im ^ σ) atImInfty)
  have he : (fun z : ℍ => Real.exp (-a * z.im) * z.im ^ σ) =O[atImInfty]
      (fun _ : ℍ => (1 : ℝ)) := by
    simpa only [zero_mul, Real.exp_zero] using
      ((isLittleO_exp_mul_rpow_of_lt σ (neg_lt_zero.mpr ha)).isBigO.comp_tendsto
        (tendsto_comap : Tendsto (fun z : ℍ => z.im) atImInfty atTop))
  exact h.trans he

/-- Every real polynomial weight times the actual cusp density is uniformly bounded on the entire standard domain. -/
theorem exists_petersson_slash_rpow_bound_fd {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    {k : ℤ} (f : CuspForm Γ k) (g : SL(2, ℤ)) (σ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ fd,
      z.im ^ σ * ‖petersson k (⇑f ∣[k] g) (⇑f ∣[k] g) z‖ ≤ C := by
  have hc : Continuous (fun z : ℍ => ‖petersson k (⇑f ∣[k] g) (⇑f ∣[k] g) z‖ * z.im ^ σ) := by
    apply Continuous.mul
    · exact (petersson_continuous k (ModularFormClass.continuous (CuspForm.translate f g))
        (ModularFormClass.continuous (CuspForm.translate f g))).norm
    · exact continuous_im.rpow_const (fun z => Or.inl z.im_ne_zero)
  have ht : (fun z : ℍ => ‖petersson k (⇑f ∣[k] g) (⇑f ∣[k] g) z‖ * z.im ^ σ) =O[atImInfty]
      (fun z : ℍ => z.im ^ (0 : ℝ)) := by
    simpa only [Real.rpow_zero] using petersson_slash_rpow_isBigO_one f g σ
  obtain ⟨C, hC⟩ := exists_bound_fundamental_domain_of_isBigO hc ht
  refine ⟨max 1 C, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro z hz
  have h := hC z hz
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg z.im_pos.le _)),
    Real.rpow_zero, mul_one] at h
  have h' : z.im ^ σ * ‖petersson k (⇑f ∣[k] g) (⇑f ∣[k] g) z‖ ≤ C := by
    simpa only [mul_comm] using h
  exact h'.trans (le_max_right _ _)

end
end Dubon2026
