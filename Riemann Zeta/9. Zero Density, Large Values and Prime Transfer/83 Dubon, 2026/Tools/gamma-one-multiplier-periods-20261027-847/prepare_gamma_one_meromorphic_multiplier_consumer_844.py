from pathlib import Path
p=Path(r'E:\Lean\.tmp\dubon83')
ell='''import SourceMeromorphicMultiplierGerm
import Dubon2026.SourceGammaOneExactRamification

/-! DUB-17/18 -> original Gamma1 Picard/H1 -> Abel-Jacobi -> actual
unitary multiplier. The existing exact ramification formula uses the
signed stabilizer, so no assumption that -1 belongs to Gamma1 is needed. -/
namespace Dubon2026.SourceMeromorphicMultiplier
noncomputable section
open UpperHalfPlane Filter CongruenceSubgroup SourceFunctionField
open SourceFunctionField.GammaOne
open scoped MatrixGroups Topology SubgroupStabilizer GammaOne

theorem gammaOne_multiplier_eq_one_of_trace_sq_lt (N : ℕ) [NeZero N]
    (hT : ModularGroup.T ∈ Gamma1 N) (F : ℍ → ℂ) (χ : Gamma1 N → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (F ∘ ofComplex) (τ : ℂ))
    (hχ : ∀ (γ : Gamma1 N) (τ : ℍ), F (γ.val • τ) = χ γ * F τ)
    (hord : ∀ τ : ℍ, ∃ m : ℤ, meromorphicOrderAt (F ∘ ofComplex) (τ : ℂ) =
      (((analyticRamification hT τ : ℤ) * m : ℤ) : WithTop ℤ))
    (γ : Gamma1 N) (hγ : γ.val.val.trace ^ 2 < 4) : χ γ = 1 := by
  obtain ⟨τ, hfix⟩ := exists_smul_eq_self_of_trace_sq_lt_four γ.val hγ
  obtain ⟨m, hm⟩ := hord τ
  let n : ℤ := (analyticRamification hT τ : ℤ) * m
  obtain ⟨g, hg, hg0, hfg⟩ := (meromorphicOrderAt_eq_int_iff (hF τ)).mp hm
  have hχγ := multiplier_eq_denom_zpow F γ.val (χ γ) (hχ γ) τ hfix n g hg hg0 hfg
  let γs : MulAction.stabilizer (plusMinus (Gamma1 N)) τ :=
    ⟨⟨γ.val, le_plusMinus (Gamma1 N) γ.property⟩, hfix⟩
  have hpow : denom (γ.val : GL (Fin 2) ℝ) τ ^
      Nat.card (MulAction.stabilizer (plusMinus (Gamma1 N)) τ) = 1 := by
    change SubgroupStabilizer.chi (plusMinus (Gamma1 N)) τ γs ^
      Nat.card (MulAction.stabilizer (plusMinus (Gamma1 N)) τ) = 1
    rw [← map_pow, pow_card_eq_one', map_one]
  have hcard : (Nat.card (MulAction.stabilizer (plusMinus (Gamma1 N)) τ) : ℤ) =
      2 * (analyticRamification hT τ : ℤ) := by
    exact_mod_cast (two_mul_ramification_eq_stabilizer_card N hT τ).symm
  have hn : 2 * n =
      (Nat.card (MulAction.stabilizer (plusMinus (Gamma1 N)) τ) : ℤ) * m := by
    dsimp only [n]
    rw [hcard]
    ring
  have hd : denom (γ.val : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ _
  rw [hχγ, zpow_neg, inv_eq_one, mul_zpow, ← zpow_add₀ hd, ← two_mul,
    hn, zpow_mul, zpow_natCast, hpow, one_zpow]

end
end Dubon2026.SourceMeromorphicMultiplier
'''
main='''import SourceGammaOneMeromorphicMultiplierElliptic
import SourceGammaOneUnitaryCharacterPeriods
import Dubon2026.SourceGammaOneMeromorphicPrincipalDivisor

/-! DUB-17/18 -> original Gamma1 Picard/H1 -> Abel-Jacobi -> actual
meromorphic multiplier correction. Consume the original divisor's actual
ramified analytic orders and nonzero translated cusp limits. Derive
multiplicativity and triviality on all elliptic/parabolic elements, then
realize this specific multiplier by genuine weight-two cusp-form periods. -/
namespace Dubon2026
noncomputable section
open UpperHalfPlane Filter CongruenceSubgroup Matrix.SpecialLinearGroup
open SourceCurve SourceFunctionField SourceFunctionField.GammaOne SourceMeromorphicMultiplier
open scoped MatrixGroups Topology

theorem sourceGamma1_meromorphic_multiplier_eq_exp_real_period (N : ℕ) [NeZero N]
    (hT : ModularGroup.T ∈ Gamma1 N)
    (D : Divisor ℂ (functionFieldOver (Gamma1 N) ℂ))
    (F : ℍ → ℂ) (χ : Gamma1 N → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (F ∘ ofComplex) (τ : ℂ))
    (hχ : ∀ (γ : Gamma1 N) (τ : ℍ), F (γ.val • τ) = χ γ * F τ)
    (hunit : ∀ γ, ‖χ γ‖ = 1)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L))
    (ho : ∀ τ : ℍ, meromorphicOrderAt (F ∘ ofComplex) (τ : ℂ) =
      (((analyticRamification hT τ : ℤ) * D (analyticPlace hT τ) : ℤ) : WithTop ℤ)) :
    ∃ f : CuspForm ((Gamma1 N).map (mapGL ℝ)) 2,
      ∀ γ : Gamma1 N, χ γ =
        Complex.exp (2 * Real.pi * Complex.I *
          ((sourceWeightTwoPeriodValue (Gamma1 N) f γ).re : ℂ)) := by
  obtain ⟨τ, hτ⟩ := exists_apply_ne_zero hcusp
  have hmul : ∀ γ δ : Gamma1 N, χ (γ * δ) = χ γ * χ δ :=
    multiplier_mul hχ hτ
  have htriv : ∀ γ : Gamma1 N, γ.val.val.trace ^ 2 ≤ 4 → χ γ = 1 := by
    intro γ hγ
    rcases hγ.lt_or_eq with hlt | heq
    · exact gammaOne_multiplier_eq_one_of_trace_sq_lt N hT F χ hF hχ
        (fun τ => ⟨D (analyticPlace hT τ), ho τ⟩) γ hlt
    · exact multiplier_eq_one_of_trace_sq hχ hcusp γ heq
  exact sourceGamma1_unitary_character_eq_exp_real_period N χ hmul hunit htriv

end
end Dubon2026
'''
for mod,body in [('SourceGammaOneMeromorphicMultiplierElliptic',ell),('SourceGammaOneMeromorphicMultiplierPeriods',main)]:
 with (p/(mod+'.lean')).open('x',encoding='utf-8',newline='\n') as f:f.write(body)
print('Prepared actual Gamma1 meromorphic-multiplier consumer with signed ramification.')
