from pathlib import Path
import json,hashlib
p=Path(__file__).parent
src=p/'anthropic-flt-residual-closure-20261020/P2M/Sol/S_Complex_integral_inv_sub_mul_dbar_eq_neg_pi_mul.lean.txt'
t=src.read_text(encoding='utf-8-sig')
b=t[t.index('noncomputable def D '):t.index('end DbarFundamental')]
ix=[0,b.index('theorem integrableOn_inv '),b.index('theorem integral_deriv_φ '),b.index('theorem main '),len(b)]
mods=['SourceComplexDbarCutoff','SourceComplexDbarKernelIntegrability','SourceComplexDbarRadialNormalization','SourceComplexCauchyPompeiu']
for i,m in enumerate(mods):
 part=b[ix[i]:ix[i+1]]
 if i>0:part='variable (a : ℂ) {ε : ℝ}\n\n'+part
 part=part.replace('theorem main ', 'theorem integral_inv_sub_mul_dbar ')
 part=part.replace('Complex.integral_mul_dbar_eq_zero_of_differentiableOn','Dubon2026.SourceComplexReciprocity.integral_mul_dbar_eq_zero')
 prev='SourceComplexHolomorphicStokes' if i==0 else mods[i-1]
 body='import '+prev+'\n\n'+""" /-! DUB-17/18 -> original Gamma1 Picard/H1 -> Abel-Jacobi converse ->
analytic reciprocity -> logarithmic-derivative residue identity ->
the simple-pole dbar kernel. Adapted from the frozen primary FLT proof;
native radial integration and integration by parts prove the normalization.
No residue or Cauchy-Pompeiu conclusion is assumed. -/
namespace Dubon2026.SourceComplexReciprocity.DbarFundamental
noncomputable section
open MeasureTheory Filter Complex Metric Set
open scoped Topology Real InnerProductSpace

"""+part+'end\nend Dubon2026.SourceComplexReciprocity.DbarFundamental\n'
 with (p/(m+'.lean')).open('x',encoding='utf-8',newline='\n') as f:f.write(body)
route={'gate':'DUB-17/18','chain':['all-weight arithmetic association','original Gamma1 Picard/H1','Abel-Jacobi converse','analytic reciprocity','logarithmic-derivative residue identity','simple-pole dbar kernel'],'reuseChecked':[{'path':str(src),'sha256':hashlib.sha256(src.read_bytes()).hexdigest().upper(),'review':'Full primary proof read. Existing local production searched for dbar/residue/compact-support identities, none found. Native Cauchy circle/rectangle formulas inspected; direct faithful radial cutoff proof has a smaller adaptation burden than a new punctured-domain Stokes proof. Native radial Haar integration, integrableOn_ball_of_norm_le_rpow and improper FTC are consumed.'}],'assumptionsToDischarge':['actual singular kernel integrable against compact continuous multiplier','radial cutoff integral exactly minus pi','arbitrary compact C1 test function gives minus pi times its value at the pole'],'remaining':'Finite residue decomposition and actual modular smoothed winding/period/Petersson comparison remain; all-weight source gates stay open.'}
with (p/'complex-cauchy-pompeiu-route-865.json').open('x',encoding='utf-8') as f:json.dump(route,f,indent=2)
print('Prepared four modules for the actual simple-pole dbar identity.')
