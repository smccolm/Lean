import Dubon2026.SourceRealPrimitiveGreenData
import Dubon2026.SourceWindingBoundaryIntegral

/-! DUB-17/18 -> original Gamma1 Picard/H1 -> principal-divisor converse ->
integral Petersson duality. One application of the already proved exact Green
formula to Re(Ek) yields the real-period/Petersson side identity. All primitive,
differentiability, continuity and cusp bounds are derived from actual cusp
forms. The source domain, central factor and sign are retained. -/
namespace Dubon2026.SourceRealPrimitive
noncomputable section
open UpperHalfPlane MeasureTheory SourceModularGreenPairing SourceModularSidePairing
open SourceParabolicEdgePeriod SourceSmoothedUnfolding
open scoped MatrixGroups ComplexConjugate
variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] [Fintype (SL(2, ℤ) ⧸ Γ)]
local notation "Q" => SL(2, ℤ) ⧸ Γ
local notation "V" => CuspForm (Γ.map (Matrix.SpecialLinearGroup.mapGL ℝ)) 2

theorem petersson_eq_real_period_pairing (hΓ : (-1 : SL(2, ℤ)) ∈ Γ) (k g : V) :
    Complex.I * (∫ τ in closedDomain Γ, petersson 2 k g τ) =
      Complex.I * (∑ q : Q, ((sourceWeightTwoPeriodValue Γ k
        (transition Γ ModularGroup.T q)).re : ℂ) *
          (∫ y in Set.Ioi (Real.sqrt 3 / 2),
            tilePull g (Quotient.out q)⁻¹ (-(1 / 2) + y * Complex.I))) +
      1 / 2 * (∑ q : Q, ((sourceWeightTwoPeriodValue Γ k
        (transition Γ ModularGroup.S q)).re : ℂ) *
          (∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
            tilePull g (Quotient.out q)⁻¹ (Complex.exp (θ * Complex.I)) *
              (Complex.I * Complex.exp (θ * Complex.I)))) := by
  classical
  let c : SL(2, ℤ) → ℂ := fun γ =>
    if hγ : γ ∈ Γ then ((sourceWeightTwoPeriodValue Γ k ⟨γ, hγ⟩).re : ℂ) else 0
  have hLc : ∀ γ ∈ Γ, ∀ τ : ℍ,
      realEk k ((γ • τ : ℍ) : ℂ) = realEk k τ + c γ := by
    intro γ hγ τ
    dsimp only [c]
    rw [dif_pos hγ]
    exact realEk_smul k ⟨γ, hγ⟩ τ
  have hc (M : SL(2, ℤ)) (q : Q) :
      c ((Quotient.out (M • q))⁻¹ * M * Quotient.out q) =
        ((sourceWeightTwoPeriodValue Γ k (transition Γ M q)).re : ℂ) := by
    dsimp only [c]
    have hm : (Quotient.out (M • q))⁻¹ * M * Quotient.out q ∈ Γ :=
      (transition Γ M q).property
    rw [dif_pos hm]
    rfl
  obtain ⟨_, h⟩ := integral_dbar_cusp_eq_side_pairing Γ hΓ (realEk k)
    (fun z => realMul (k (ofComplex z))) (fun _ hz => hasFDerivAt_realEk k hz)
    (continuousOn_realEk_derivative k) c hLc (realEk_cusp_bound k)
    g (fun q => tilePull g (Quotient.out q)⁻¹)
    (fun q z => tilePull_eq_div g (Quotient.out q)⁻¹ z)
  have hd (τ : ℍ) :
      (realMul (k (ofComplex (τ : ℂ))) 1 +
        Complex.I * realMul (k (ofComplex (τ : ℂ))) Complex.I) / 2 *
          g τ * ((τ.im : ℂ) ^ 2) = (1 / 2 : ℂ) * petersson 2 k g τ := by
    rw [dbar_realMul, ofComplex_apply]
    simp only [petersson, zpow_ofNat]
    ring
  simp_rw [hd, hc] at h
  rw [integral_const_mul] at h
  rw [show Complex.I * (∫ τ in closedDomain Γ, petersson 2 k g τ) =
    (2 * Complex.I) * ((1 / 2 : ℂ) * (∫ τ in closedDomain Γ, petersson 2 k g τ)) by ring, h]
  rw [one_div, ← mul_assoc, mul_inv_cancel₀ (mul_ne_zero two_ne_zero Complex.I_ne_zero), one_mul]

end
end Dubon2026.SourceRealPrimitive
