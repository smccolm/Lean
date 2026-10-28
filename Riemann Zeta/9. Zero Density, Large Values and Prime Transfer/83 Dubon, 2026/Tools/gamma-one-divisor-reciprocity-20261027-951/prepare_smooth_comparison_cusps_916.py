from pathlib import Path
import json,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
src=p/'gamma-one-reciprocity-reuse-848/S_ModularCurve_exists_mem_periodLatticeOf_tendsto_windingPairing_smoothedFundamental.lean.txt'
t=src.read_text(encoding='utf-8')
div=t[t.index('section Divisor'):t.index('scoped instance countable_SL2Z')]
div=div.replace('im_smul_le_max (σ⁻¹', 'SourceSmoothedFundamental.im_smul_le_max (σ⁻¹')
div+='\nend Divisor\n\n'
cusp=t[t.index('section CuspTransfer'):t.index('\nsection Density')]
cusp=cusp.replace('{Y : ℝ} (hY0 : 0 < Y) (hY :', '{Y : ℝ} (hY :',1)
header='''import SourceSmoothComparisonQuotient

/-! DUB-17/18 -> original all-weight arithmetic association -> Gamma1 Picard/H1
-> Abel-Jacobi converse -> analytic reciprocity -> filled quotient cusp control.
The proved modular height bound makes the actual finite divisor order vanish
high in every translated cusp. The constructed V is then identically one,
so the quotient inherits the actual untwist limit and derivative decay.
This discharges the cusp assumptions needed by the winding log and boundary
pairing. Adapted from pinned Apache-2.0 source 848; existing geometry reused. -/
namespace Dubon2026.SourceSmoothComparison
noncomputable section
open UpperHalfPlane hiding I
open Filter Complex Set SourceSmoothDivisor
open scoped MatrixGroups Topology Real

'''
assemble='''theorem quot_cusp_data {Γ : Subgroup SL(2, ℤ)} (S : Finset ℍ) (n : ℍ → ℤ)
    (hcov : ∀ τ : ℍ, n τ ≠ 0 → ∃ s ∈ S, ∃ γ : Γ, γ.val • s = τ)
    {Φ V : ℂ → ℂ} (hΦ : HasLocalModels Φ n) (hV : HasLocalModels V n)
    (hV1 : ∀ σ : SL(2, ℤ), ∃ Y : ℝ, ∀ z : ℂ, Y < z.im → V (sm σ z) = 1)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ c : ℂ, c ≠ 0 ∧
      Tendsto (fun τ : ℍ => Φ ((σ • τ : ℍ) : ℂ)) atImInfty (𝓝 c))
    (hdecay : ∀ σ : SL(2, ℤ), Tendsto
      (fun τ : ℍ => fderiv ℝ (fun u : ℂ => Φ (sm σ u)) (τ : ℂ)) atImInfty (𝓝 0)) :
    ∀ σ : SL(2, ℤ), ∃ c : ℂ, c ≠ 0 ∧
      Tendsto (fun τ : ℍ => quot Φ V ((σ • τ : ℍ) : ℂ)) atImInfty (𝓝 c) ∧
      Tendsto (fun τ : ℍ => fderiv ℝ (fun u : ℂ => quot Φ V (sm σ u)) (τ : ℂ))
        atImInfty (𝓝 0) := by
  intro σ
  obtain ⟨Yn, hYn0, hYn⟩ := exists_height_n_eq_zero S n hcov σ
  obtain ⟨Yv, hYv⟩ := hV1 σ
  obtain ⟨c, hc, hclim⟩ := hcusp σ
  have hY0 : 0 < max Yn Yv := hYn0.trans_le (le_max_left _ _)
  have hY : ∀ τ : ℍ, max Yn Yv < τ.im → n (σ • τ) = 0 :=
    fun τ hτ => hYn τ ((le_max_left _ _).trans_lt hτ)
  have hW : ∀ z : ℂ, max Yn Yv < z.im → V (sm σ z) = 1 :=
    fun z hz => hYv z ((le_max_right _ _).trans_lt hz)
  exact ⟨c, hc, tendsto_quot_smul hΦ hV σ hY hW hclim,
    tendsto_fderiv_quot_smul hΦ hV σ hY0 hY hW (hdecay σ)⟩
'''
out=header+div+cusp+'\n'+assemble+'\nend\nend Dubon2026.SourceSmoothComparison\n'
with (p/'SourceSmoothComparisonCusps.lean').open('x',encoding='utf-8',newline='\n') as f:f.write(out)
print('Prepared finite-divisor cusp transfer and assembled quotient limit/derivative decay.')
