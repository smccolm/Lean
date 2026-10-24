import Dubon2026.SourceEllipticDeuringInvariants
import Dubon2026.SourceEllipticDeuringIntegralParameter
import Dubon2026.SourceEllipticThreeTorsionFlex

/-! DUB-17/18 -> characteristic-two good models -> faithful inertia.
The exact Deuring coordinate and flex argument is adapted from
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_WeierstrassCurve_exists_variableChange_eq_deuring_of_isUnit_three.
The actual field and torsion inputs remain for the subsequent consumer. -/
namespace Dubon2026.SourceEllipticDeuring
open WeierstrassCurve WeierstrassCurve.Affine
noncomputable section
variable {M : Type*} [Field M]

theorem exists_deuring_good_model [DecidableEq M] (A : ValuationSubring M) (h3 : IsUnit (3 : A))
    (E : WeierstrassCurve M) [E.IsElliptic] (hj : E.j ∈ A)
    {x₀ y₀ : M} (hP : E.toAffine.Nonsingular x₀ y₀) (h3P : (3 : ℕ) • Point.some x₀ y₀ hP = 0)
    {c : M} (hc : c ^ 3 = 2 * y₀ + E.a₁ * x₀ + E.a₃) :
    ∃ (α : A) (κ : VariableChange M),
      IsUnit (⟨α, 0, 1, 0, 0⟩ : WeierstrassCurve A).Δ ∧
      (κ.u : M) = c ∧ κ.r = x₀ ∧
      κ.s = (3 * x₀ ^ 2 + 2 * E.a₂ * x₀ + E.a₄ - E.a₁ * y₀) / (2 * y₀ + E.a₁ * x₀ + E.a₃) ∧
      κ.t = y₀ ∧
      κ • E = (⟨α, 0, 1, 0, 0⟩ : WeierstrassCurve A).map A.subtype := by
  obtain ⟨hd, hflex⟩ := flex_of_order_three E hP h3P
  set d : M := 2 * y₀ + E.a₁ * x₀ + E.a₃ with hd_def
  set n : M := 3 * x₀ ^ 2 + 2 * E.a₂ * x₀ + E.a₄ - E.a₁ * y₀ with hn_def
  set m : M := n / d with hm_def
  have hmd : m * d = n := div_mul_cancel₀ _ hd
  have hc0 : c ≠ 0 := by
    intro h; apply hd; rw [← hc, h]; ring
  have heq : y₀ ^ 2 + E.a₁ * x₀ * y₀ + E.a₃ * y₀ = x₀ ^ 3 + E.a₂ * x₀ ^ 2 + E.a₄ * x₀ + E.a₆ :=
    (equation_iff x₀ y₀).mp hP.1

  set α₀ : M := (E.a₁ + 2 * m) / c with hα₀
  set κ : VariableChange M := ⟨Units.mk0 c hc0, x₀, m, y₀⟩ with hκ
  have hκE : κ • E = (⟨α₀, 0, 1, 0, 0⟩ : WeierstrassCurve M) := by
    ext
    · simp only [variableChange_a₁, hκ, Units.val_inv_eq_inv_val, Units.val_mk0, hα₀]
      field_simp
    · simp only [variableChange_a₂, hκ, Units.val_inv_eq_inv_val, Units.val_mk0]
      rw [show E.a₂ - m * E.a₁ + 3 * x₀ - m ^ 2 = 0 by linear_combination -hflex, mul_zero]
    · simp only [variableChange_a₃, hκ, Units.val_inv_eq_inv_val, Units.val_mk0]
      rw [show E.a₃ + x₀ * E.a₁ + 2 * y₀ = c ^ 3 by rw [hc]; ring, inv_pow,
        inv_mul_cancel₀ (pow_ne_zero 3 hc0)]
    · simp only [variableChange_a₄, hκ, Units.val_inv_eq_inv_val, Units.val_mk0]
      rw [show E.a₄ - m * E.a₃ + 2 * x₀ * E.a₂ - (y₀ + x₀ * m) * E.a₁ + 3 * x₀ ^ 2 - 2 * m * y₀
        = n - m * d by rw [hn_def, hd_def]; ring, hmd, sub_self, mul_zero]
    · simp only [variableChange_a₆, hκ, Units.val_inv_eq_inv_val, Units.val_mk0]
      rw [show E.a₆ + x₀ * E.a₄ + x₀ ^ 2 * E.a₂ + x₀ ^ 3 - y₀ * E.a₃ - y₀ ^ 2 - x₀ * y₀ * E.a₁ = 0 by
        linear_combination -heq, mul_zero]

  haveI : (⟨α₀, 0, 1, 0, 0⟩ : WeierstrassCurve M).IsElliptic := by rw [← hκE]; infer_instance
  have hjE : E.j = (⟨α₀, 0, 1, 0, 0⟩ : WeierstrassCurve M).j := by
    have h1 : (κ • E).j = E.j := variableChange_j E κ
    have h2' : ∀ (V₁ V₂ : WeierstrassCurve M) [V₁.IsElliptic] [V₂.IsElliptic], V₁ = V₂ → V₁.j = V₂.j := by
      rintro V₁ V₂ _ _ rfl; rfl
    rw [← h1]; exact h2' _ _ hκE
  have hjα : E.j * (α₀ ^ 3 - 27) = α₀ ^ 3 * (α₀ ^ 3 - 24) ^ 3 := by
    rw [hjE]; exact j_deuring_mul α₀
  obtain ⟨α, hα, hΔ⟩ := exists_integral_deuring_parameter A h3 ⟨E.j, hj⟩ hjα
  refine ⟨α, κ, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · rw [deuring_Δ]
    exact hΔ
  · change A.subtype α = α₀ at hα
    rw [hκE, deuring_map, hα]

end
end Dubon2026.SourceEllipticDeuring
