import Dubon2026.SourceIntegralTraceTranslationCoefficients
import Dubon2026.SourceIntegralTracePeriodWidth
import Dubon2026.SourceIntegralTraceSlashPeriods

/-! DUB-17/18 -> original Gamma1 degree preservation -> even-weight
slash integrality -> peaked auxiliary trace. Exact finite translation and
signed transversal identities used by the actual trace decomposition.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularForm_qExpansion_slash_coeff_mem_of_peaked_auxiliary. -/
namespace Dubon2026.SourceFunctionField.IntegralTrace
noncomputable section
open scoped MatrixGroups ModularForm Manifold
open UpperHalfPlane GammaOne

theorem translation_sum_eq (f : ℍ → ℂ) (k : ℤ) (h₀ : ℕ) :
    (fun τ : ℍ => ∑ j ∈ Finset.range h₀,
      (f ∣[k] ((ModularGroup.T ^ j : SL(2, ℤ)) : GL (Fin 2) ℝ)) τ) =
      Translates.trSum f h₀ := by
  funext τ
  exact Finset.sum_congr rfl fun j _ => slash_T_pow_apply _ _ _ _

theorem coeff_qExpansion_one_sum_slash_T_pow {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] (h : ℕ) (hh : 0 < h)
    {κ : ℤ} (hκ : Even κ) (X : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) κ)
    (h₀ : ℕ) (hh₀ : 0 < h₀) (hh₀h : h₀ ∣ h) (hT₀ : ModularGroup.T ^ h₀ ∈ Γ ∨ -(ModularGroup.T ^ h₀) ∈ Γ) (i : ℕ) :
    PowerSeries.coeff i (UpperHalfPlane.qExpansion 1 (fun τ : UpperHalfPlane =>
        ∑ j ∈ Finset.range h₀, ((⇑X : UpperHalfPlane → ℂ) ∣[κ] ((ModularGroup.T ^ j : SL(2, ℤ)) : GL (Fin 2) ℝ)) τ)) =
      (h₀ : ℂ) * PowerSeries.coeff (h * i) (UpperHalfPlane.qExpansion (h : ℝ) (⇑X : UpperHalfPlane → ℂ)) := by
  have hper₀ : Function.Periodic ((⇑X : UpperHalfPlane → ℂ) ∘ UpperHalfPlane.ofComplex) (h₀ : ℝ) :=
    periodic_of_pm_mem X hκ h₀ hT₀
  have hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑X : UpperHalfPlane → ℂ) := ModularFormClass.holo X
  have hbdd : UpperHalfPlane.IsBoundedAtImInfty (⇑X : UpperHalfPlane → ℂ) := ModularFormClass.bdd_at_infty X
  rw [translation_sum_eq, Translates.coeff_translation_sum hh₀ hper₀ hhol hbdd i]
  congr 1
  obtain ⟨m', hm'⟩ := hh₀h
  have hm'pos : 0 < m' := Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at hm'; omega
  have hw := qExpansion_coeff_multiple_width (⇑X) (h₀ : ℝ) (by exact_mod_cast hh₀) hm'pos.ne' hper₀ hhol hbdd (h * i)
  have hcast : ((m' : ℝ) * (h₀ : ℝ)) = (h : ℝ) := by rw [hm']; push_cast; ring
  rw [hcast] at hw
  rw [hw, if_pos ⟨h₀ * i, by rw [hm']; ring⟩]
  congr 1
  rw [hm', show h₀ * m' * i = m' * (h₀ * i) by ring, Nat.mul_div_cancel_left _ hm'pos]

end
end Dubon2026.SourceFunctionField.IntegralTrace
