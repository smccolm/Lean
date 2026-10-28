import Dubon2026.SourceModularPeriodCorners
import Dubon2026.SourceWeightTwoPrimitiveEdges
import Dubon2026.SourceWeightTwoIntegralPeriods

/-! DUB-17/18 -> original arithmetic association -> Gamma1 Picard/H1 ->
Abel-Jacobi converse -> reciprocity -> integral periods of the winding sum.
Transport the actual normalized primitive across the fixed coset transitions.
Reuse the original period additivity and the actual cusp limits. -/
namespace Dubon2026.SourceParabolicEdgePeriod
noncomputable section
open UpperHalfPlane hiding I
open Filter Complex MeasureTheory
open SourcePeriodUntwist SourceSmoothDivisor SourceModularSidePairing SourceModularGreenPairing
open scoped MatrixGroups Topology Real
variable {Γ : Subgroup SL(2, ℤ)}
local notation "Q" => SL(2, ℤ) ⧸ Γ

theorem out_inv_smul (M : SL(2, ℤ)) (q : Q) (τ : ℍ) :
    (Quotient.out (M • q))⁻¹ • τ =
      ((transition Γ M q : Γ) : SL(2, ℤ)) • (Quotient.out q)⁻¹ • M⁻¹ • τ := by
  rw [← mul_smul, ← mul_smul, coe_transition]
  congr 1
  group

theorem phi_transition_S_eq (φ : Additive Γ →+ ℤ) (q : Q) :
    φ (Additive.ofMul (transition Γ ModularGroup.S q)) =
      φ (Additive.ofMul (transition Γ W q)) +
        φ (Additive.ofMul (transition Γ ModularGroup.T (W • q))) := by
  have h : ModularGroup.S = ModularGroup.T * W := by rw [W, mul_inv_cancel_left]
  conv_lhs => rw [h, transition_mul]
  rw [ofMul_mul, map_add, add_comm]

variable [Γ.FiniteIndex] (g : CuspForm (Γ.map (Matrix.SpecialLinearGroup.mapGL ℝ)) 2)

theorem I_mul_integral_ray_corner (σ : SL(2, ℤ)) {L : ℂ}
    (hL : Tendsto (fun w : ℍ => Ek g ((σ • w : ℍ) : ℂ)) atImInfty (𝓝 L)) :
    Complex.I * ∫ y in Set.Ioi (Real.sqrt 3 / 2),
        tilePull g σ (-(1 / 2) + y * Complex.I) =
      L - Ek g ((σ • ρ : ℍ) : ℂ) := by
  rw [I_mul_integral_ray g σ hL, Ep, ← coe_rho, sm_coe]

theorem integral_arc_corner (σ : SL(2, ℤ)) :
    ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
      tilePull g σ (Complex.exp (θ * Complex.I)) * (Complex.I * Complex.exp (θ * Complex.I)) =
        Ek g ((σ • ρ : ℍ) : ℂ) - Ek g ((σ • (ModularGroup.T • ρ) : ℍ) : ℂ) := by
  rw [integral_arc g σ, exp_two_pi_div_three, exp_pi_div_three, Ep, Ep, sm_coe, sm_coe]

theorem period_neg_one (hΓ : (-1 : SL(2, ℤ)) ∈ Γ) :
    sourceWeightTwoPeriodValue Γ g ⟨-1, hΓ⟩ = 0 := by
  have h := Ek_smul g ⟨-1, hΓ⟩ UpperHalfPlane.I
  rw [ModularGroup.SL_neg_smul, one_smul] at h
  linear_combination -h

theorem period_transition_S_S (hΓ : (-1 : SL(2, ℤ)) ∈ Γ) (q : Q) :
    sourceWeightTwoPeriodValue Γ g (transition Γ ModularGroup.S (ModularGroup.S • q)) =
      -sourceWeightTwoPeriodValue Γ g (transition Γ ModularGroup.S q) := by
  have h := sourceWeightTwoPeriodValue_mul Γ g
    (transition Γ ModularGroup.S (ModularGroup.S • q)) (transition Γ ModularGroup.S q)
  have h2 : transition Γ ModularGroup.S (ModularGroup.S • q) *
      transition Γ ModularGroup.S q = ⟨-1, hΓ⟩ :=
    Subtype.ext (coe_transition_S_S_mul hΓ q)
  rw [h2, period_neg_one g hΓ] at h
  linear_combination -h

theorem Ek_out_inv_smul (M : SL(2, ℤ)) (q : Q) (τ : ℍ) :
    Ek g (((Quotient.out (M • q))⁻¹ • τ : ℍ) : ℂ) =
      Ek g (((Quotient.out q)⁻¹ • M⁻¹ • τ : ℍ) : ℂ) +
        sourceWeightTwoPeriodValue Γ g (transition Γ M q) := by
  rw [out_inv_smul, Ek_smul]

theorem lim_T_smul {L : SL(2, ℤ) → ℂ}
    (hL : ∀ σ, Tendsto (fun w : ℍ => Ek g ((σ • w : ℍ) : ℂ)) atImInfty (𝓝 (L σ))) (q : Q) :
    L (Quotient.out (ModularGroup.T • q))⁻¹ =
      L (Quotient.out q)⁻¹ + sourceWeightTwoPeriodValue Γ g (transition Γ ModularGroup.T q) := by
  refine tendsto_nhds_unique (hL _) ?_
  have : (fun w : ℍ => Ek g (((Quotient.out (ModularGroup.T • q))⁻¹ • w : ℍ) : ℂ)) =
      fun w => Ek g (((Quotient.out q)⁻¹ • ModularGroup.T⁻¹ • w : ℍ) : ℂ) +
        sourceWeightTwoPeriodValue Γ g (transition Γ ModularGroup.T q) :=
    funext fun w => Ek_out_inv_smul g _ q w
  rw [this]
  exact ((hL _).comp tendsto_T_inv_smul).add_const _

end
end Dubon2026.SourceParabolicEdgePeriod
