from pathlib import Path
import json,hashlib
p=Path(__file__).parent
src=p/'anthropic-flt-residual-closure-20261020/P2M/Sol/S_Complex_integral_logDeriv_wedge_add_finsum_eq_integral_dbarLogDeriv.lean.txt'
t=src.read_text(encoding='utf-8-sig')
a=t.index('variable {a :');b=t.index('def Lg ',a)
variables=t[a:b]
disc_start=t.index('include hΨ hΨ1 hΨa hΦ hE hk hks hkr in')
local=t[a:disc_start]
disc=variables+t[disc_start:t.index('end Disc')]
glob=t[t.index('section Global'):t.index('end Complex.WedgeArgument')]
def shorten(b):
 b=b.replace('include hΨ1 hΨa in\ntheorem Ψ_ne','include hΨ1 in\ntheorem Ψ_ne')
 b=b.replace('Ψ_ne hΨ1 hΨa','Ψ_ne hΨ1')
 b=b.replace('include hE hk hkr in\ntheorem fderiv_vEk','include hE hk in\ntheorem fderiv_vEk')
 b=b.replace('fderiv_vEk hE hk hkr','fderiv_vEk hE hk')
 b=b.replace('include hΨ hΨ1 hΨa hΦ in\ntheorem Φ_ne','include hΨ1 hΦ in\ntheorem Φ_ne')
 b=b.replace('Φ_ne hΨ hΨ1 hΨa hΦ','Φ_ne hΨ1 hΦ')
 b=b.replace('Φ_ne (hΨf τ hτ) (hΨ1 τ hτ) (hΨ0 τ hτ) (hΦf τ hτ)','Φ_ne (hΨ1 τ hτ) (hΦf τ hτ)')
 b=b.replace('Complex.integral_inv_sub_mul_dbar_eq_neg_pi_mul','DbarFundamental.integral_inv_sub_mul_dbar')
 return b
local=shorten(local)
local=local.replace('def Lg ','/-- Local logarithm of the normalized nonzero smooth factor. -/\ndef Lg ')
local=local.replace('def vEk ','/-- The actual holomorphic primitive times the compact test function. -/\ndef vEk ')
disc=shorten(disc)
glob=shorten(glob).replace('theorem main ','theorem integral_wedge_residue_identity ')
for m,imp,body in [('SourceComplexWedgeLocalLog','SourceComplexWedgeStokes\nimport SourceComplexCauchyPompeiu',local),('SourceComplexWedgeDisc','SourceComplexWedgeLocalLog',disc),('SourceComplexWedgeIntegral','SourceComplexWedgeDisc',glob)]:
 head='import '+imp+'\n\n'+"""/-! DUB-17/18 -> original Gamma1 Picard/H1 -> Abel-Jacobi converse ->
analytic reciprocity -> winding-period limit -> smooth local comparison
function. Its exact local integer orders give the wedge/residue identity
by compact-support integration by parts, the proved simple-pole kernel,
and native smooth partition of unity. Holomorphicity of the smooth
comparison function is not assumed. -/
namespace Dubon2026.SourceComplexReciprocity.Wedge
noncomputable section
open MeasureTheory Filter Complex Metric Set DbarFundamental
open scoped Topology Real Manifold ContDiff

"""
 with (p/(m+'.lean')).open('x',encoding='utf-8',newline='\n') as f:f.write(head+body+'end\nend Dubon2026.SourceComplexReciprocity.Wedge\n')
r={'gate':'DUB-17/18','chain':['all-weight arithmetic association','original Gamma1 Picard/H1','Abel-Jacobi converse','analytic reciprocity','winding-period limit','smooth local comparison function','exact wedge/residue identity'],'reuseChecked':[{'path':str(src),'sha256':hashlib.sha256(src.read_bytes()).hexdigest().upper(),'review':'Entire primary proof read. Duplicate continuity, dbar and singular-integrability infrastructure removed in favor of 863/865 results. Unused upstream helper parameters removed while the complete local/global statement is retained. Native local logarithm, second-derivative symmetry, smooth partition of unity and the locally proved simple-pole integral replace external axiomatic imports.'}],'assumptionsToDischarge':['actual C1 local integer-order models imply integrability and exact wedge/residue sum for compact C2 tests'],'remaining':'Actual invariant comparison model and smoothed modular period/Petersson limit, original principal-divisor converse and full all-weight arithmetic association remain. This proof alone closes no DUB gate.'}
with (p/'complex-wedge-integral-route-872.json').open('x',encoding='utf-8') as f:json.dump(r,f,indent=2)
