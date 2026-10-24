import Dubon2026.SourceEllipticCharThreeModel

/-! Actual coordinate equations for the exceptional characteristic-three
stabilizer. They serve its order bound and the wild cyclic-subgroup census
in the DUB-17/18 good-reduction chain.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_exists_isGalois_ord_jqModC_dvd_six_of_char_three, stab_E0. -/
namespace Dubon2026.SourceEllipticExceptional
open WeierstrassCurve
noncomputable section
variable {K : Type*} [Field K] [CharP K 3]

theorem char_three_stabilizer_coordinates {γ : VariableChange K}
    (h : γ • EA (-1 : K) = EA (-1 : K)) :
    γ.s = 0 ∧ γ.t = 0 ∧ (γ.u : K) ^ 4 = 1 ∧ γ.r ^ 3 = γ.r := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_char_three
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  let v : K := ((γ.u⁻¹ : Kˣ) : K)
  have hv : v ≠ 0 := (γ.u⁻¹).ne_zero
  have ha₁ := congrArg WeierstrassCurve.a₁ h
  have ha₃ := congrArg WeierstrassCurve.a₃ h
  have ha₄ := congrArg WeierstrassCurve.a₄ h
  have ha₆ := congrArg WeierstrassCurve.a₆ h
  simp only [variableChange_a₁, variableChange_a₃, variableChange_a₄,
    variableChange_a₆, EA] at ha₁ ha₃ ha₄ ha₆
  have hs : γ.s = 0 := by
    have hz : v * (2 * γ.s) = 0 := by linear_combination ha₁
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hv)).resolve_left h2
  have ht : γ.t = 0 := by
    have hz : v ^ 3 * (2 * γ.t) = 0 := by linear_combination ha₃
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ hv))).resolve_left h2
  have h4 : v ^ 4 = 1 := by
    linear_combination -ha₄ + (v ^ 4 * γ.r ^ 2) * h3 - (2 * v ^ 4 * γ.t) * hs
  have hr : γ.r ^ 3 = γ.r := by
    have hz : v ^ 6 * (γ.r ^ 3 - γ.r) = 0 := by
      linear_combination ha₆ + (v ^ 6 * γ.t) * ht
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ hv))
  refine ⟨hs, ht, ?_, hr⟩
  change ((γ.u⁻¹ : Kˣ) : K) ^ 4 = 1 at h4
  rwa [Units.val_inv_eq_inv_val, inv_pow, inv_eq_one] at h4

end
end Dubon2026.SourceEllipticExceptional
