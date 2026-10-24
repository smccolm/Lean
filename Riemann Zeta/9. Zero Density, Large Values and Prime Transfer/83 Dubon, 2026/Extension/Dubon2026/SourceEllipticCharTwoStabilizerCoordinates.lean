import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ
import Mathlib.Tactic

/-! DUB-17/18 -> characteristic-two modular genus comparison -> actual
exceptional stabilizer. Adapted from anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_exists_isGalois_ord_jqModC_dvd_twelve_of_char_two.
The existing Mathlib.ofJ0 is the literal source curve. -/
namespace Dubon2026.SourceEllipticCharTwo
open WeierstrassCurve Polynomial
noncomputable section
variable (K : Type*) [Field K] [CharP K 2]

lemma two_eq_zero : (2 : K) = 0 := by
  simpa using CharP.cast_eq_zero K 2

lemma three_eq_one : (3 : K) = 1 := by
  linear_combination two_eq_zero K

variable {K}

lemma stabilizer_coordinates_iff (γ : VariableChange K) :
    γ • ofJ0 K = ofJ0 K ↔
      (γ.u : K) ^ 3 = 1 ∧ γ.r = γ.s ^ 2 ∧ γ.s ^ 4 = γ.s ∧ γ.t ^ 2 + γ.t = γ.s ^ 6 := by
  have h2 := two_eq_zero K
  have h3K := three_eq_one K
  set v : K := ((γ.u⁻¹ : Kˣ) : K) with hv_def
  have hv : v ≠ 0 := (γ.u⁻¹).ne_zero
  have hvu : v * (γ.u : K) = 1 := by simp [hv_def]
  constructor
  · intro h
    have e1 := congrArg WeierstrassCurve.a₂ h
    have e3 := congrArg WeierstrassCurve.a₃ h
    have e4 := congrArg WeierstrassCurve.a₄ h
    have e6 := congrArg WeierstrassCurve.a₆ h
    simp only [variableChange_a₂, variableChange_a₃, variableChange_a₄, variableChange_a₆, ofJ0, h2,
      h3K, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, mul_one, one_mul] at e1 e3 e4 e6
    rw [← hv_def] at e1 e3 e4 e6
    have e1' := (mul_eq_zero.mp e1).resolve_left (pow_ne_zero 2 hv)
    have e4' := (mul_eq_zero.mp e4).resolve_left (pow_ne_zero 4 hv)
    have e6' := (mul_eq_zero.mp e6).resolve_left (pow_ne_zero 6 hv)
    have hr : γ.r = γ.s ^ 2 := by linear_combination e1'
    refine ⟨?_, hr, ?_, ?_⟩
    · linear_combination (-(γ.u : K) ^ 3) * e3 + ((v * γ.u) ^ 2 + v * γ.u + 1) * hvu
    · linear_combination e4' - (γ.r + γ.s ^ 2) * hr
    · linear_combination -e6' + (γ.r ^ 2 + γ.r * γ.s ^ 2 + γ.s ^ 4) * hr
  · rintro ⟨hu3, hr, hs4, ht⟩
    have hv3 : v ^ 3 = 1 := by
      linear_combination (-(v ^ 3)) * hu3 + ((v * γ.u) ^ 2 + v * γ.u + 1) * hvu
    ext
    · simp only [variableChange_a₁, ofJ0]
      rw [← hv_def]
      linear_combination v * γ.s * h2
    · simp only [variableChange_a₂, ofJ0]
      rw [← hv_def]
      linear_combination 3 * v ^ 2 * hr + v ^ 2 * γ.s ^ 2 * h2
    · simp only [variableChange_a₃, ofJ0]
      rw [← hv_def]
      linear_combination hv3 + v ^ 3 * γ.t * h2
    · simp only [variableChange_a₄, ofJ0]
      rw [← hv_def]
      linear_combination (3 * v ^ 4 * (γ.r + γ.s ^ 2)) * hr + 3 * v ^ 4 * hs4
        + v ^ 4 * γ.s * (1 - γ.t) * h2
    · simp only [variableChange_a₆, ofJ0]
      rw [← hv_def]
      linear_combination v ^ 6 * (γ.r ^ 2 + γ.r * γ.s ^ 2 + γ.s ^ 4) * hr - v ^ 6 * ht

variable (K) in

end
end Dubon2026.SourceEllipticCharTwo
