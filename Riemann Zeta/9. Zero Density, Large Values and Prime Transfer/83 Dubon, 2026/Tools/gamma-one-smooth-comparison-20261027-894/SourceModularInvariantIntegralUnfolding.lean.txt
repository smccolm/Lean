import Dubon2026.CongruenceTraceDomain

/-! DUB-17/18 -> original Gamma1 Picard/H1 -> Abel-Jacobi converse ->
analytic reciprocity -> smooth invariant integral limit. Native fundamental-
domain unfolding and Tonelli control the actual invariant integrand.
The cutoff summability, nonnegativity and orbit bound are explicit upstream
conditions, discharged by the compact smooth partition in its consumer.
No integral identity is assumed. -/
namespace Dubon2026.SourceSmoothedUnfolding
noncomputable section
open UpperHalfPlane MeasureTheory Set
open scoped MatrixGroups ENNReal
variable (Γ : Subgroup SL(2, ℤ))

theorem integral_mul_eq_periodized {S : Set ℍ}
    (hS : IsFundamentalDomain (projectiveIntegralSubgroup Γ) S (volume : Measure ℍ))
    (P : ℍ → ℂ) (hPm : AEStronglyMeasurable P volume)
    (hP : ∀ (g : projectiveIntegralSubgroup Γ) (τ : ℍ), P (g • τ) = P τ)
    (hPi : IntegrableOn P S volume) (w : ℍ → ℝ) (hwm : Measurable w)
    (hw0 : ∀ τ, 0 ≤ w τ)
    (hws : ∀ τ : ℍ, Summable fun g : projectiveIntegralSubgroup Γ => w (g • τ))
    (hwb : ∀ τ : ℍ, ∑' g : projectiveIntegralSubgroup Γ, w (g • τ) ≤ 1) :
    Integrable (fun τ => P τ * (w τ : ℂ)) ∧
      (∫ τ : ℍ, P τ * (w τ : ℂ)) =
        ∫ τ in S, P τ * ((∑' g : projectiveIntegralSubgroup Γ, w (g • τ) : ℝ) : ℂ) := by
  let F : ℍ → ℂ := fun τ => P τ * (w τ : ℂ)
  have hFm : AEStronglyMeasurable F volume :=
    hPm.mul (Complex.continuous_ofReal.measurable.comp hwm).aestronglyMeasurable
  have hterm (g : projectiveIntegralSubgroup Γ) :
      AEStronglyMeasurable (fun τ : ℍ => F (g • τ)) (volume.restrict S) :=
    (hFm.comp_measurePreserving (measurePreserving_smul g volume)).restrict
  have hnorm (τ : ℍ) :
      ∑' g : projectiveIntegralSubgroup Γ, ‖F (g • τ)‖ₑ =
        ‖P τ‖ₑ * ENNReal.ofReal (∑' g : projectiveIntegralSubgroup Γ, w (g • τ)) := by
    calc
      ∑' g : projectiveIntegralSubgroup Γ, ‖F (g • τ)‖ₑ =
          ∑' g : projectiveIntegralSubgroup Γ, ENNReal.ofReal (‖P τ‖ * w (g • τ)) := by
        apply tsum_congr
        intro g
        rw [← ofReal_norm]
        simp only [F, norm_mul, hP, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hw0 (g • τ))]
      _ = ‖P τ‖ₑ * ENNReal.ofReal (∑' g : projectiveIntegralSubgroup Γ, w (g • τ)) := by
        simp_rw [ENNReal.ofReal_mul (norm_nonneg (P τ))]
        rw [ENNReal.tsum_mul_left, ofReal_norm,
          ← ENNReal.ofReal_tsum_of_nonneg (fun g => hw0 (g • τ)) (hws τ)]
  have hbound (τ : ℍ) :
      ∑' g : projectiveIntegralSubgroup Γ, ‖F (g • τ)‖ₑ ≤ ‖P τ‖ₑ := by
    rw [hnorm]
    have hle : ENNReal.ofReal (∑' g : projectiveIntegralSubgroup Γ, w (g • τ)) ≤ 1 := by
      simpa using ENNReal.ofReal_le_ofReal (hwb τ)
    simpa only [mul_one] using mul_le_mul' (le_refl ‖P τ‖ₑ) hle
  have hfin : (∑' g : projectiveIntegralSubgroup Γ,
      ∫⁻ τ in S, ‖F (g • τ)‖ₑ) < ⊤ := by
    rw [← lintegral_tsum (fun g => (hterm g).enorm)]
    exact lt_of_le_of_lt (lintegral_mono hbound) hPi.2
  have hFi : Integrable F := by
    refine ⟨hFm, ?_⟩
    change (∫⁻ τ, ‖F τ‖ₑ) < ⊤
    rw [hS.lintegral_eq_tsum'']
    exact hfin
  refine ⟨hFi, ?_⟩
  rw [hS.integral_eq_tsum'' F hFi, ← integral_tsum hterm hfin.ne]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun τ => by
    simp only [F, hP]
    rw [tsum_mul_left, ← Complex.ofReal_tsum]

end
end Dubon2026.SourceSmoothedUnfolding
