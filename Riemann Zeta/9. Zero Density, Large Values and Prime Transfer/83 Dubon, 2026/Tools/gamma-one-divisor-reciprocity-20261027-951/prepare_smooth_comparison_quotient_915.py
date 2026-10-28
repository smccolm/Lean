from pathlib import Path
import json,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
src=p/'gamma-one-reciprocity-reuse-848/S_ModularCurve_exists_mem_periodLatticeOf_tendsto_windingPairing_smoothedFundamental.lean.txt'
t=src.read_text(encoding='utf-8')
# Keep the source signatures, but reuse the already proved removable filling.
prefix=t[t.index('def HasLocalModels'):t.index('theorem quot_local')]
prefix=prefix.replace('def HasLocalModels','/-- Exact integer local models with a nonvanishing C1 factor on the upper half-plane. -/\ndef HasLocalModels')
prefix=prefix.replace('def quot (Φ V : ℂ → ℂ) (z : ℂ) : ℂ := limUnder (𝓝[≠] z) fun w => Φ w / V w','/-- Removable filling of the actual quotient; proved equal to the source punctured limit. -/\ndef quot (Φ V : ℂ → ℂ) : ℂ → ℂ := regularize (fun w => Φ w / V w)')
sig=t[t.index('theorem quot_local'):t.index('  obtain ⟨Ψ',t.index('theorem quot_local'))]
body='''  obtain ⟨Ψ, hΨ, hΨ0, hΦe⟩ := hΦ τ
  obtain ⟨Θ, hΘ, hΘ0, hVe⟩ := hV τ
  let R : ℂ → ℂ := fun w => Ψ w * (Θ w)⁻¹
  have hRcd : ContDiffAt ℝ 1 R τ := hΨ.mul (hΘ.inv hΘ0)
  have hRτ : R τ ≠ 0 := mul_ne_zero hΨ0 (inv_ne_zero hΘ0)
  have hΘne : ∀ᶠ w in 𝓝 (τ : ℂ), Θ w ≠ 0 :=
    hΘ.continuousAt.eventually_ne hΘ0
  have hp : ∀ᶠ w in 𝓝[≠] (τ : ℂ), V w ≠ 0 ∧ Φ w = R w * V w := by
    filter_upwards [hΦe.filter_mono nhdsWithin_le_nhds,
      hVe.filter_mono nhdsWithin_le_nhds,
      hΘne.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with w h1 h2 h3 hne
    have hz : (w - τ) ^ (n τ) ≠ 0 := zpow_ne_zero _ (sub_ne_zero.2 hne)
    refine ⟨by rw [h2]; exact mul_ne_zero hz h3, ?_⟩
    rw [h1, h2]
    dsimp only [R]
    field_simp
  have hdiv : (fun w => Φ w / V w) =ᶠ[𝓝[≠] (τ : ℂ)] R := by
    filter_upwards [hp] with w hw
    rw [hw.2]
    exact mul_div_cancel_right₀ _ hw.1
  have hreg := regularize_eventuallyEq (k := (0 : ℤ))
    (by simpa only [zpow_zero, one_mul] using hdiv)
    (eventually_continuousAt hRcd) hRτ
  have hqR : quot Φ V =ᶠ[𝓝 (τ : ℂ)] R := by
    simpa only [quot, zpow_zero, one_mul] using hreg
  refine ⟨R, hRcd, hRτ, hqR, hp, ?_⟩
  intro hn0
  filter_upwards [hΦe, hVe, hΘne, hqR] with w h1 h2 h3 h4
  rw [hn0, zpow_zero, one_mul] at h1 h2
  refine ⟨by rw [h2]; exact h3, ?_⟩
  rw [h1, h2, h4]
  dsimp only [R]
  field_simp

'''
rest=t[t.index('theorem contDiffAt_quot'):t.index('\nend LocalModels')]
a=rest.index('  have hsm :')
b=rest.index('  have h1 := (tendsto_div_quot',a)
rest=rest[:a]+'''  have hsm : Tendsto (sm γ) (𝓝[≠] (τ : ℂ)) (𝓝[≠] ((γ • τ : ℍ) : ℂ)) := by
    simpa only [sm_coe] using SourceSmoothDivisor.Data.tendsto_sm_nhdsNE γ hτ
'''+rest[b:]
rest=rest.replace('(mem_U τ)','τ.im_pos').replace(chr(0x1d54c),'upperHalfPlaneSet')
bridge='''theorem quot_eq_limUnder (hΦ : HasLocalModels Φ n) (hV : HasLocalModels V n) (τ : ℍ) :
    quot Φ V τ = limUnder (𝓝[≠] (τ : ℂ)) (fun w => Φ w / V w) :=
  (tendsto_div_quot hΦ hV τ).limUnder_eq.symm

'''
header='''import SourceSmoothLocalModelRegularization
import SourceSmoothDivisorInvarianceCusps

/-! DUB-17/18 -> full all-weight arithmetic association -> original Gamma1
Picard/H1 -> Abel-Jacobi converse -> analytic reciprocity -> filled comparison
quotient and its winding logarithm. Equal integer local orders cancel.
The existing removable-filling theorem gives the nonvanishing C1 quotient
without duplicating the source open-neighborhood limit argument. The quotient
is proved equal to the source limUnder at every actual upper-half-plane point.
The existing punctured action-limit theorem supplies invariance transport.
Adapted from the pinned Apache-2.0 winding-period source, scope 848. -/
namespace Dubon2026.SourceSmoothComparison
noncomputable section
open UpperHalfPlane hiding I
open Filter Complex Set SourceSmoothLocalModel SourceSmoothDivisor
open scoped MatrixGroups Topology Real

'''
out=header+prefix+sig+body+rest+'\n'+bridge+'\nend\nend Dubon2026.SourceSmoothComparison\n'
with (p/'SourceSmoothComparisonQuotient.lean').open('x',encoding='utf-8',newline='\n') as f:f.write(out)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
r=dict(chain='DUB-17/18 -> all-weight arithmetic association -> original Gamma1 Picard/H1 -> Abel-Jacobi converse -> analytic reciprocity -> actual filled quotient -> parabolic winding logarithm',source=dict(path=str(src),sha256=sha(src),sectionsRead='LocalModels, Divisor and CuspTransfer (lines 269-465); remaining sections not copied here.'),reuseChecked=[dict(path=str(p/n),sha256=sha(p/n)) for n in ['SourceSmoothLocalModelRegularization.lean','SourceSmoothDivisorInvarianceCusps.lean','SourceModularParabolicWindingLog.lean']],shorterRoute='Reuse regularize_eventuallyEq at order zero and existing punctured action-limit transport. Prove equality with source limUnder at each upper-half-plane point. Meromorphic normal forms do not apply to the merely C1 smooth quotient.',assumptionsToDischarge=['Equal original integer local orders imply a nonvanishing C1 filled quotient','Both actual invariances imply quotient invariance','Source punctured-limit convention is exactly preserved'],remaining='Cusp transfer and actual original-object consumer must discharge winding-log hypotheses; then side-pairing/period/Petersson assembly and the full source chain. 16/20; DUB-17--20 OPEN.')
with (p/'smooth-comparison-quotient-route-915.json').open('x',encoding='utf-8') as f:json.dump(r,f,indent=2)
print('Prepared filled quotient using existing regularization and exact source-limit bridge.')
