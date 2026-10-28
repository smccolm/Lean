from pathlib import Path
import json,hashlib
p=Path(__file__).parent
src=p/'anthropic-flt-residual-closure-20261020/P2M/Sol/S_Complex_integral_mul_logDeriv_mul_dbar_eq_neg_pi_mul_finsum.lean.txt'
t=src.read_text(encoding='utf-8-sig')
b=t[t.index('theorem eventually_nhdsNE_eventually_nhds'):t.index('end Complex.LogDerivStokes')]
i=b.index('  have h1 : HasDerivAt');j=b.index('\ntheorem analyticAt_dslope')
b=b[:i]+"""  change logDeriv (fun w => (w - a) ^ n * G w) z = _
  have hp : DifferentiableAt ℂ (fun w : ℂ => (w - a) ^ n) z :=
    ((hasDerivAt_zpow n (z - a) (Or.inl hsub)).comp z
      ((hasDerivAt_id z).sub_const a)).differentiableAt
  rw [logDeriv_mul z (zpow_ne_zero n hsub) hG0 hp hG,
    logDeriv_fun_zpow (differentiableAt_id.sub_const a)]
  simp [logDeriv_apply]
"""+b[j:]
b=b.replace('theorem main ', 'theorem integral_mul_logDeriv_mul_dbar ')
b=b.replace('Complex.integral_mul_dbar_eq_neg_pi_mul_finsum_residue','Residue.integral_mul_dbar_eq_residues')
head="""import SourceComplexResidueIntegral

/-! DUB-17/18 -> original Gamma1 Picard/H1 -> Abel-Jacobi converse ->
analytic reciprocity -> exact logarithmic-derivative residue identity.
Actual finite meromorphic orders supply the residues. Native logDeriv_mul
and logDeriv_fun_zpow shorten the primary derivative calculation. -/
namespace Dubon2026.SourceComplexReciprocity.LogDerivStokes
noncomputable section
open MeasureTheory Complex Filter Set
open scoped Topology Real

"""
with (p/'SourceComplexLogDerivativeResidues.lean').open('x',encoding='utf-8',newline='\n') as f:f.write(head+b+'end\nend Dubon2026.SourceComplexReciprocity.LogDerivStokes\n')
r={'gate':'DUB-17/18','chain':['all-weight arithmetic association','original Gamma1 Picard/H1','Abel-Jacobi converse','analytic reciprocity','actual logarithmic-derivative residues'],'reuseChecked':[{'path':str(src),'sha256':hashlib.sha256(src.read_bytes()).hexdigest().upper(),'review':'Full primary proof read. Native logDeriv_mul and logDeriv_fun_zpow replace explicit product differentiation and field simplification. Native meromorphicOrderAt_eq_int_iff supplies the actual local factor; prior simple-pole integral is consumed.'}],'assumptionsToDischarge':['finite actual meromorphic orders determine logarithmic residues','compact C1 test function gives exact residue sum with actual orders and holomorphic multiplier'],'remaining':'Actual modular smoothed winding/period/Petersson comparison and original principal-divisor converse remain, followed by full arithmetic chain.'}
with (p/'complex-log-derivative-residues-route-867.json').open('x',encoding='utf-8') as f:json.dump(r,f,indent=2)
