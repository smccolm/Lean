import Dubon2026.SourceEllipticTorsionIntegralCoordinates
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.Tactic

/-! DUB-17/18 -> wild good reduction -> faithful inertia specialization.
Monic quartic and quadratic identities give integral translation parameters
without invertibility of two or three. Adapted from TauCeti IntegralModel,
Apache-2.0, commit e177885ee120f8074a7610c3e60571ab00b20004.
The existing local valuation-ring integral-closure bridge is reused. -/
namespace Dubon2026.SourceEllipticReduction
noncomputable section
open WeierstrassCurve Polynomial
variable {M : Type*} [Field M] (A : ValuationSubring M)

theorem mem_of_monic_quadratic (b c : A) {z : M}
    (hz : z ^ 2 + (b : M) * z + (c : M) = 0) : z ∈ A := by
  apply SourceEllipticFunctionField.mem_valuationSubring_of_integral A
  refine ⟨X ^ 2 + (C b * X + C c), monic_X_pow_add (by compute_degree!), ?_⟩
  rw [← aeval_def]
  simpa only [map_add, map_mul, map_pow, aeval_X, aeval_C, add_assoc] using hz

theorem integral_change_r_mem (W W' : WeierstrassCurve A) (g : VariableChange M)
    (hg : g • W'.map A.subtype = W.map A.subtype)
    (u : A) (hu : (u : M) = (g.u : M)) : g.r ∈ A := by
  have hb6 : (g.u : M) ^ 6 * (W.map A.subtype).b₆ =
      (W'.map A.subtype).b₆ + 2 * g.r * (W'.map A.subtype).b₄ +
      g.r ^ 2 * (W'.map A.subtype).b₂ + 4 * g.r ^ 3 := by
    rw [← hg, variableChange_b₆]
    simp only [Units.val_inv_eq_inv_val]
    field_simp
  have hb8 : (g.u : M) ^ 8 * (W.map A.subtype).b₈ =
      (W'.map A.subtype).b₈ + 3 * g.r * (W'.map A.subtype).b₆ +
      3 * g.r ^ 2 * (W'.map A.subtype).b₄ + g.r ^ 3 * (W'.map A.subtype).b₂ +
      3 * g.r ^ 4 := by
    rw [← hg, variableChange_b₈]
    simp only [Units.val_inv_eq_inv_val]
    field_simp
  apply SourceEllipticFunctionField.mem_valuationSubring_of_integral A
  refine ⟨X ^ 4 + (C (-W'.b₄) * X ^ 2 +
    C (-(2 * W'.b₆) - u ^ 6 * W.b₆) * X + C (u ^ 8 * W.b₈ - W'.b₈)),
    monic_X_pow_add (by compute_degree!), ?_⟩
  rw [← aeval_def]
  simp only [map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, aeval_X, aeval_C]
  change g.r ^ 4 + (-((W'.map A.subtype).b₄) * g.r ^ 2 +
    (-(2 * (W'.map A.subtype).b₆) - (u : M) ^ 6 * (W.map A.subtype).b₆) * g.r +
    ((u : M) ^ 8 * (W.map A.subtype).b₈ - (W'.map A.subtype).b₈)) = 0
  rw [hu]
  linear_combination hb8 - g.r * hb6

theorem integral_change_s_mem (W W' : WeierstrassCurve A) (g : VariableChange M)
    (hg : g • W'.map A.subtype = W.map A.subtype)
    (u r : A) (hu : (u : M) = (g.u : M)) (hr : (r : M) = g.r) : g.s ∈ A := by
  have ha2 : (g.u : M) ^ 2 * (W.map A.subtype).a₂ =
      (W'.map A.subtype).a₂ - g.s * (W'.map A.subtype).a₁ + 3 * g.r - g.s ^ 2 := by
    rw [← hg, variableChange_a₂]
    simp only [Units.val_inv_eq_inv_val]
    field_simp
  apply mem_of_monic_quadratic A W'.a₁ (u ^ 2 * W.a₂ - W'.a₂ - 3 * r)
  change g.s ^ 2 + (W'.a₁ : M) * g.s +
    ((u : M) ^ 2 * (W.a₂ : M) - (W'.a₂ : M) - 3 * (r : M)) = 0
  rw [hu, hr]
  change (g.u : M) ^ 2 * (W.a₂ : M) =
    (W'.a₂ : M) - g.s * (W'.a₁ : M) + 3 * g.r - g.s ^ 2 at ha2
  linear_combination ha2

theorem integral_change_t_mem (W W' : WeierstrassCurve A) (g : VariableChange M)
    (hg : g • W'.map A.subtype = W.map A.subtype)
    (u r : A) (hu : (u : M) = (g.u : M)) (hr : (r : M) = g.r) : g.t ∈ A := by
  have ha6 : (g.u : M) ^ 6 * (W.map A.subtype).a₆ =
      (W'.map A.subtype).a₆ + g.r * (W'.map A.subtype).a₄ +
      g.r ^ 2 * (W'.map A.subtype).a₂ + g.r ^ 3 - g.t * (W'.map A.subtype).a₃ -
      g.t ^ 2 - g.r * g.t * (W'.map A.subtype).a₁ := by
    rw [← hg, variableChange_a₆]
    simp only [Units.val_inv_eq_inv_val]
    field_simp
  apply mem_of_monic_quadratic A (W'.a₃ + r * W'.a₁)
    (u ^ 6 * W.a₆ - (W'.a₆ + r * W'.a₄ + r ^ 2 * W'.a₂ + r ^ 3))
  change g.t ^ 2 + ((W'.a₃ : M) + (r : M) * (W'.a₁ : M)) * g.t +
    ((u : M) ^ 6 * (W.a₆ : M) - ((W'.a₆ : M) + (r : M) * (W'.a₄ : M) +
      (r : M) ^ 2 * (W'.a₂ : M) + (r : M) ^ 3)) = 0
  rw [hu, hr]
  change (g.u : M) ^ 6 * (W.a₆ : M) =
    (W'.a₆ : M) + g.r * (W'.a₄ : M) + g.r ^ 2 * (W'.a₂ : M) + g.r ^ 3 -
    g.t * (W'.a₃ : M) - g.t ^ 2 - g.r * g.t * (W'.a₁ : M) at ha6
  linear_combination ha6

end
end Dubon2026.SourceEllipticReduction
