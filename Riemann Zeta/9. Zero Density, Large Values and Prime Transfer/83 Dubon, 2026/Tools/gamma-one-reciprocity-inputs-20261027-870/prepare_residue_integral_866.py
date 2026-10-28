from pathlib import Path
import json,hashlib
p=Path(__file__).parent
src=p/'anthropic-flt-residual-closure-20261020/P2M/Sol/S_Complex_integral_mul_dbar_eq_neg_pi_mul_finsum_residue.lean.txt'
t=src.read_text(encoding='utf-8-sig')
support=t[t.index('theorem tsupport_D_subset'):t.index('theorem integrableOn_inv')]
local=t[t.index('noncomputable def Freg'):t.index('theorem main ')]
main=t[t.index('theorem main '):t.index('end CauchyPompeiuResidue')]
main=main.replace('theorem main ','theorem integral_mul_dbar_eq_residues ')
main=main.replace('Complex.integral_mul_dbar_eq_zero_of_differentiableOn','Dubon2026.SourceComplexReciprocity.integral_mul_dbar_eq_zero')
main=main.replace('Complex.integral_inv_sub_mul_dbar_eq_neg_pi_mul','DbarFundamental.integral_inv_sub_mul_dbar')
for m,imp,body in [('SourceComplexResidueLocalModels','SourceComplexCauchyPompeiu',support+local),('SourceComplexResidueIntegral','SourceComplexResidueLocalModels',main)]:
 head='import '+imp+'\n\n'+"""/-! DUB-17/18 -> original Gamma1 Picard/H1 -> Abel-Jacobi converse ->
analytic reciprocity -> compact-support logarithmic residue identity.
Actual local simple-pole expansions give finite residue support and an
analytic remainder. Previously proved dbar integrability and the kernel
normalization are reused; no integration formula is assumed. -/
namespace Dubon2026.SourceComplexReciprocity.Residue
noncomputable section
open MeasureTheory Filter Complex Metric Set DbarFundamental
open scoped Topology Real

"""
 with (p/(m+'.lean')).open('x',encoding='utf-8',newline='\n') as f:f.write(head+body+'end\nend Dubon2026.SourceComplexReciprocity.Residue\n')
route={'gate':'DUB-17/18','chain':['all-weight arithmetic association','original Gamma1 Picard/H1','Abel-Jacobi converse','analytic reciprocity','compact-support logarithmic residue identity'],'reuseChecked':[{'path':str(src),'sha256':hashlib.sha256(src.read_bytes()).hexdigest().upper(),'review':'Entire primary proof read. Duplicate dbar, integrability and continuity lemmas removed in favor of already compiled 863/865 results. Native meromorphic normal form was checked, but its zero-at-pole convention does not provide the actual finite part required when subtracting the singular kernel. This proof constructs that finite part and proves finite exceptional support without a supplied residue theorem.'}],'assumptionsToDischarge':['local actual simple-pole expansions imply finite relevant residues and exact compact-support integral formula'],'remaining':'Actual logarithmic-derivative specialization, modular winding/period/Petersson comparison, original principal-divisor converse and all-weight arithmetic chain remain.'}
with (p/'complex-residue-integral-route-866.json').open('x',encoding='utf-8') as f:json.dump(route,f,indent=2)
