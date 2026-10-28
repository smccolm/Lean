import Dubon2026.SourceIntegralPeriodLatticeDual
import Dubon2026.SourceRealPeriodPeterssonPairing
import Dubon2026.SourceClosedPeterssonNondegenerate
import Dubon2026.SourceSignedPeriodLatticeLift
import Dubon2026.SourceGammaOneSignedRealPeriods

/-! DUB-17/18 -> original all-weight characteristic-zero association ->
Gamma1 Picard/H1 -> Abel-Jacobi principal-divisor converse -> multiplier
triviality. Membership of the actual Petersson functional in the original
integer-period lattice forces integral real periods. The proof consumes
the constructed integer parabolic dual, native real-period surjectivity,
the exact Green identity and nondegeneracy on the actual signed domain.
No period duality, positivity or realization premise remains. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane MeasureTheory CongruenceSubgroup Matrix.SpecialLinearGroup
open SourceSmoothedUnfolding SourceIntegralPeriodDual SourceRealPrimitive
open scoped MatrixGroups GammaOne

theorem real_periods_integral_of_petersson_mem_lattice (N : ℕ) [NeZero N]
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) 2)
    (h : ∃ Λ ∈ sourceWeightTwoIntegralLattice (Gamma1 N),
      ∀ g : CuspForm ((Gamma1 N).map (mapGL ℝ)) 2,
        Complex.I * (∫ τ in closedDomain (plusMinus (Gamma1 N)), petersson 2 f g τ) = Λ g) :
    ∀ γ : Gamma1 N, ∃ m : ℤ, (sourceWeightTwoPeriodValue (Gamma1 N) f γ).re = m := by
  classical
  letI : Fintype (SL(2, ℤ) ⧸ plusMinus (Gamma1 N)) := Fintype.ofFinite _
  obtain ⟨Λ, hΛ, hf⟩ := h
  obtain ⟨L, hL, hLΛ⟩ := SignedForms.exists_signed_integral_lattice_lift (Gamma1 N) Λ hΛ
  obtain ⟨φ, hφ, hφL⟩ := exists_parabolic_character_eq_lattice
    (plusMinus (Gamma1 N)) (neg_one_mem_plusMinus _) L hL
  let φR : Additive (plusMinus (Gamma1 N)) →+ ℝ := (Int.castAddHom ℝ).comp φ
  have hp : ∀ γ : plusMinus (Gamma1 N), γ.val.val.trace ^ 2 = 4 →
      φR (Additive.ofMul γ) = 0 := by
    intro γ hγ
    simp [φR, hφ γ hγ]
  obtain ⟨k, hk⟩ := SignedPeriods.exists_original_cuspForm_of_signed_real_character N φR hp
  have hk' : ∀ γ : plusMinus (Gamma1 N),
      (sourceWeightTwoPeriodValue (plusMinus (Gamma1 N)) (SignedForms.extend (Gamma1 N) k) γ).re =
        (φ (Additive.ofMul γ) : ℝ) := fun γ => hk γ
  have hb (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) 2) :
      Complex.I * (∫ τ in closedDomain (plusMinus (Gamma1 N)), petersson 2 k g τ) = Λ g := by
    have he := petersson_eq_real_period_pairing (neg_one_mem_plusMinus (Gamma1 N))
      (SignedForms.extend (Gamma1 N) k) (SignedForms.extend (Gamma1 N) g)
    simp only [hk', Complex.ofReal_intCast] at he
    exact he.trans ((hφL (SignedForms.extend (Gamma1 N) g)).trans (hLΛ g))
  have heq : k = f := SourcePeterssonClosed.eq_of_signed_petersson_eq k f
    (fun g => mul_left_cancel₀ Complex.I_ne_zero ((hb g).trans (hf g).symm))
  intro γ
  refine ⟨φ (Additive.ofMul ⟨γ.val, le_plusMinus (Gamma1 N) γ.property⟩), ?_⟩
  rw [← heq, ← SignedForms.period_extend_member (Gamma1 N) k γ, hk']

end
end Dubon2026.SourceFunctionField.GammaOne
