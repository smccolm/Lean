from pathlib import Path
import re,json,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
s=(p/'SourceGammaOneSmoothDivisorPeriodIntegral.lean').read_text(encoding='utf-8')
base=s[s.index('    ∃ S : Finset'):s.index(' := by\n',s.index('theorem exists_original'))]
base=base.replace('      ∀ g : CuspForm','      (∀ g : CuspForm')+')'
q=(p/'SourceSmoothComparisonWindingLog.lean').read_text(encoding='utf-8')
qs=q[q.index('    (∀ τ : ℍ, quot'):q.index(' := by\n',q.index('theorem exists_filled'))]
qs=qs.replace('quot Φ V','quot (SourcePeriodUntwist.Φ F k) V')
qs=re.sub(r'\bΓ\b','plusMinus (Gamma1 N)',qs)
# Parenthesize substituted group expressions in dependent type applications.
qs=qs.replace('Additive plusMinus (Gamma1 N)','Additive (plusMinus (Gamma1 N))')
header='''import SourceGammaOneSmoothDivisorPeriodIntegral
import SourceSmoothComparisonWindingLog
import SourceGammaOneInvariantUntwist

/-! DUB-17/18 -> full all-weight arithmetic association -> original Gamma1
Picard/H1 -> Abel-Jacobi converse -> analytic reciprocity -> actual winding
comparison. Derive the cusp form from the original unitary multiplier,
construct V from the original degree-zero divisor, and form the filled
quotient of the actual meromorphic untwist by V. Its logarithm and parabolic
integer character are proved, retaining the original divisor period limit.
The meromorphic function with a unitary multiplier is still an upstream input;
an invariant principal-divisor realization is not assumed or claimed. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane SourceCurve CongruenceSubgroup MeasureTheory Filter Complex Set
open Matrix.SpecialLinearGroup SourceSmoothComparison SourcePeriodUntwist
open SourceSmoothedFundamental (smoothedFundamental)
open scoped MatrixGroups Topology Real Classical ComplexConjugate GammaOne

theorem exists_original_divisor_winding_comparison (N : ℕ) [NeZero N]
    (hT : ModularGroup.T ∈ Gamma1 N) (c : ℍ →₀ ℤ) (hc : c.sum (fun _ n => n) = 0)
    (F : ℍ → ℂ) (χ : Gamma1 N → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (F ∘ ofComplex) (τ : ℂ))
    (hχ : ∀ (γ : Gamma1 N) (τ : ℍ), F (γ.val • τ) = χ γ * F τ)
    (hunit : ∀ γ, ‖χ γ‖ = 1)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L))
    (ho : ∀ τ : ℍ, meromorphicOrderAt (F ∘ ofComplex) (τ : ℂ) =
      (((analyticRamification hT τ : ℤ) *
        (Finsupp.mapDomain (analyticPlace hT) c) (analyticPlace hT τ) : ℤ) : WithTop ℤ)) :
    let D := Finsupp.mapDomain (analyticPlace hT) c
    ∃ k : CuspForm ((Gamma1 N).map (mapGL ℝ)) 2,
      (∀ γ : Gamma1 N, χ γ = Complex.exp (2 * Real.pi * Complex.I *
        ((sourceWeightTwoPeriodValue (Gamma1 N) k γ).re : ℂ))) ∧
'''
proof=''' := by
  classical
  dsimp only
  let D := Finsupp.mapDomain (analyticPlace hT) c
  let n : ℍ → ℤ := fun τ => (analyticRamification hT τ : ℤ) * D (analyticPlace hT τ)
  obtain ⟨k, hk⟩ := sourceGamma1_meromorphic_multiplier_eq_exp_real_period
    N hT D F χ hF hχ hunit hcusp ho
  have hperiod : ∀ (γ : Gamma1 N) (τ : ℍ), F (γ.val • τ) =
      Complex.exp (2 * Real.pi * Complex.I *
        ((sourceWeightTwoPeriodValue (Gamma1 N) k γ).re : ℂ)) * F τ := by
    intro γ τ
    rw [hχ, hk]
  have hΦ : HasLocalModels (SourcePeriodUntwist.Φ F k) n :=
    fun τ => Φ_local F k hF τ (n τ) (ho τ)
  have hΦinv : ∀ γ ∈ plusMinus (Gamma1 N), ∀ τ : ℍ,
      SourcePeriodUntwist.Φ F k ((γ • τ : ℍ) : ℂ) = SourcePeriodUntwist.Φ F k τ := by
    intro γ hγ τ
    obtain ⟨δ, hδ⟩ := exists_gamma_smul_eq_of_mem_plusMinus (Gamma1 N) hγ τ
    rw [← hδ]
    exact Φ_smul F k hF hperiod δ τ
  have hΦcusp : ∀ σ : SL(2, ℤ), ∃ c : ℂ, c ≠ 0 ∧
      Tendsto (fun τ : ℍ => SourcePeriodUntwist.Φ F k ((σ • τ : ℍ) : ℂ))
        atImInfty (𝓝 c) := by
    intro σ
    obtain ⟨c, hc, hlim⟩ := hcusp σ
    exact Φ_cusp F k hF σ hc hlim
  have hΦdecay : ∀ σ : SL(2, ℤ), Tendsto
      (fun τ : ℍ => fderiv ℝ (fun u : ℂ =>
        SourcePeriodUntwist.Φ F k (SourceSmoothDivisor.sm σ u)) (τ : ℂ))
      atImInfty (𝓝 0) := by
    intro σ
    obtain ⟨c, hc, hlim⟩ := hcusp σ
    exact Φ_decay F k hF σ hc hlim
  obtain ⟨S, hsub, hinj, hcov, V, hVi, hVl, hVc, hVint, hVlim⟩ :=
    exists_original_divisor_smooth_period_limit N hT c hc
  have hcov' : ∀ τ : ℍ, n τ ≠ 0 →
      ∃ s ∈ S, ∃ γ : plusMinus (Gamma1 N), γ.val • s = τ := by
    intro τ hτ
    obtain ⟨s, hs, γ, hγ⟩ := hcov τ (fun he => hτ (by simp [n, D, he]))
    exact ⟨s, hs, ⟨γ.val, le_plusMinus (Gamma1 N) γ.property⟩, hγ⟩
  have hq := exists_filled_winding_log (plusMinus (Gamma1 N)) S n hcov' hΦ hVl
    hΦinv (fun γ hγ τ => hVi ⟨γ, hγ⟩ τ) hVc hΦcusp hΦdecay
  exact ⟨k, hk, S, hsub, hinj, hcov, V, hVi, hVl, hVc, hVint, hVlim, hq⟩

end
end Dubon2026.SourceFunctionField.GammaOne
'''
out=header+base+' ∧\n'+qs+proof
# The action derivative notation in the generic conclusion is made explicit.
out=out.replace('quot (SourcePeriodUntwist.Φ F k) V (sm σ u)','quot (SourcePeriodUntwist.Φ F k) V (SourceSmoothDivisor.sm σ u)')
with (p/'SourceGammaOneDivisorWindingComparison.lean').open('x',encoding='utf-8',newline='\n') as f:f.write(out)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
route=dict(chain='DUB-17/18 -> original all-weight arithmetic association -> original Gamma1 Picard/H1 -> Abel-Jacobi converse -> analytic reciprocity -> actual filled-quotient parabolic winding character',reuseChecked=[dict(path=str(p/n),sha256=sha(p/n)) for n in ['smooth-comparison-quotient-route-915.json','SourceGammaOneSmoothDivisorPeriodIntegral.lean','SourceGammaOneInvariantUntwist.lean','SourceModularParabolicWindingLog.lean']],assumptionsToDischarge=['Derive the actual original cusp form from the unitary multiplier','Construct the comparison V and its original-divisor period limit','Derive quotient regularity, nonvanishing, signed invariance and nonzero cusp limits with derivative decay','Produce the actual logarithm and integer character vanishing on literal trace-squared-four elements','Preserve source punctured-limit convention via a proved equality'],remaining='The meromorphic function with exact orders and a unitary multiplier remains an upstream input. Winding side-pairing/period integral, Petersson comparison, analytic reciprocity, principal-divisor converse and full all-weight arithmetic chain remain. 16/20; DUB-17--20 OPEN.')
with (p/'gamma-one-divisor-winding-comparison-route-918.json').open('x',encoding='utf-8') as f:json.dump(route,f,indent=2)
print('Prepared actual original-divisor winding consumer, including unchanged original period-limit conclusion.')
