import Dubon2026.SourceModularGreenDensity

/-! DUB-17/18 -> original all-weight arithmetic association -> Gamma1 Picard/H1
-> Abel-Jacobi converse -> analytic reciprocity -> winding-period boundary
identity. The complete Green formula consumes the actual function and cusp
form. Cusp estimates prove integrability; the literal coset tiling and proved
boundary pairing give the exact source constants and signs. Adapted from the
pinned Apache-2.0 anthropics solution, replacing its geometry, slash and tiling
infrastructure by existing proved results. Quasiperiods and translated bounds
remain explicit upstream inputs here; the actual winding consumer must derive
them from the constructed logarithm and quotient cusp data. -/
namespace Dubon2026.SourceModularGreenPairing
noncomputable section
open UpperHalfPlane hiding I
open Filter Complex MeasureTheory Asymptotics
open SourceSmoothedUnfolding SourceSmoothDivisor SourceSmoothOrbitIntegral SourceModularSidePairing
open SourceComplexReciprocity.Dipole
open scoped MatrixGroups Topology ModularForm ComplexConjugate Real NNReal Pointwise

theorem integral_dbar_cusp_eq_side_pairing (Γ : Subgroup SL(2, ℤ)) [Fintype (SL(2, ℤ) ⧸ Γ)] (hΓ : (-1 : SL(2, ℤ)) ∈ Γ)
    (L : ℂ → ℂ) (L' : ℂ → ℂ →L[ℝ] ℂ)
    (hL : ∀ z : ℂ, 0 < z.im → HasFDerivAt L (L' z) z)
    (hL' : ContinuousOn L' {z : ℂ | 0 < z.im})
    (c : SL(2, ℤ) → ℂ) (hLc : ∀ γ ∈ Γ, ∀ τ : ℍ, L ((γ • τ : ℍ) : ℂ) = L τ + c γ)
    (hbd : ∀ σ : SL(2, ℤ), ∃ C Y : ℝ, ∀ z : ℂ, Y ≤ z.im →
      ‖L ((σ • ofComplex z : ℍ) : ℂ)‖ ≤ C ∧
        ‖fderiv ℝ (fun u : ℂ => L ((σ • ofComplex u : ℍ) : ℂ)) z‖ ≤ C)
    (g : CuspForm (Γ.map (Matrix.SpecialLinearGroup.mapGL ℝ)) 2) (G : SL(2, ℤ) ⧸ Γ → ℂ → ℂ)
    (hG : ∀ q z, G q z = g ((Quotient.out q)⁻¹ • ofComplex z) /
      denom (((Quotient.out q)⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) (ofComplex z) ^ 2) :
    IntegrableOn (fun τ : ℍ => (L' τ 1 + I * L' τ I) / 2 * g τ * ((τ.im : ℂ) ^ 2))
      (closedDomain Γ) ∧
    (∫ τ in closedDomain Γ,
        (L' τ 1 + I * L' τ I) / 2 * g τ * ((τ.im : ℂ) ^ 2)) =
      1 / (2 * I) *
        (I * ∑ q : SL(2, ℤ) ⧸ Γ,
            c ((Quotient.out (ModularGroup.T • q))⁻¹ * ModularGroup.T * Quotient.out q) *
              (∫ y in Set.Ioi (Real.sqrt 3 / 2), G q (-(1 / 2) + y * I)) +
          1 / 2 * ∑ q : SL(2, ℤ) ⧸ Γ,
            c ((Quotient.out (ModularGroup.S • q))⁻¹ * ModularGroup.S * Quotient.out q) *
              (∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
                G q (Complex.exp (θ * I)) * (I * Complex.exp (θ * I)))) := by
  haveI : Γ.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hG' : G = fun q => tilePull g (Quotient.out q)⁻¹ := by
    funext q z; exact (hG q z).trans (tilePull_eq_div g (Quotient.out q)⁻¹ z).symm
  subst hG'
  beta_reduce
  refine ⟨integrableOn_Pd g L L' hL hL' hbd, ?_⟩
  obtain ⟨e2, e3⟩ := side_pairing g L L' hL hL' c hLc hbd
  have e1 : ∀ q : SL(2, ℤ) ⧸ Γ,
      2 * I * ∫ z in SourceModularGreen.D, Hd L' g (Quotient.out q)⁻¹ z =
        I * (∫ y in Set.Ioi (Real.sqrt 3 / 2),
            Φt L g (Quotient.out q)⁻¹ (1 / 2 + y * I)) -
          I * (∫ y in Set.Ioi (Real.sqrt 3 / 2),
            Φt L g (Quotient.out q)⁻¹ (-(1 / 2) + y * I)) -
          ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
            Φt L g (Quotient.out q)⁻¹ (Complex.exp (θ * I)) *
              (I * Complex.exp (θ * I)) := fun q => by
    rw [← smul_eq_mul I, ← smul_eq_mul I,
      ← tile_identity g L L' hL hL' (Quotient.out q)⁻¹ (hbd _), ← integral_const_mul]
    rfl
  have e1s := Finset.sum_congr rfl fun q (_ : q ∈ Finset.univ) => e1 q
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum] at e1s
  have hlhs := lhs_unfold g L L' hL hL' hbd hΓ
  change (∫ τ in closedDomain Γ, Pd L' g τ) = _
  rw [hlhs]
  have key : 2 * I * (∑ q : SL(2, ℤ) ⧸ Γ, ∫ z in SourceModularGreen.D, Hd L' g (Quotient.out q)⁻¹ z) =
      I * (∑ q : SL(2, ℤ) ⧸ Γ,
          c ((Quotient.out (ModularGroup.T • q))⁻¹ * ModularGroup.T * Quotient.out q) *
            ∫ y in Set.Ioi (Real.sqrt 3 / 2), tilePull g (Quotient.out q)⁻¹ (-(1 / 2) + y * I)) +
        1 / 2 * ∑ q : SL(2, ℤ) ⧸ Γ,
          c ((Quotient.out (ModularGroup.S • q))⁻¹ * ModularGroup.S * Quotient.out q) *
            ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
              tilePull g (Quotient.out q)⁻¹ (Complex.exp (θ * I)) * (I * Complex.exp (θ * I)) := by
    linear_combination e1s + I * e2 - (1 / 2 : ℂ) * e3
  have h2I : (2 * I : ℂ) ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
  rw [← key]
  field_simp


end
end Dubon2026.SourceModularGreenPairing
