from pathlib import Path
import json,re,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
src=p/'anthropic-flt-residual-closure-20261020/P2M/Sol/S_UpperHalfPlane_exists_localModel_pair_integral_mul_dbarLogDeriv_eq.lean.txt'
s=src.read_text(encoding='utf-8-sig')
b=s[s.index('def dbarL'):s.index('end DipoleConstruction')]
b=re.sub(r'^def dbar \(f : ℂ → ℂ\).*?\n\n','',b,flags=re.M)
b=re.sub(r'\bdbar\b','D',b)
b=b.replace('include hO hSeg hχ1 in\n\ntheorem dfun_eq_near','include hχ1 in\n\ntheorem dfun_eq_near').replace('dfun_eq_near hO hSeg hχ1','dfun_eq_near hχ1')
b=b.replace('include hχ hO hχ1 in\n\ntheorem Dχ_eq_zero','include hO hχ1 in\n\ntheorem Dχ_eq_zero').replace('Dχ_eq_zero hχ hO hχ1','Dχ_eq_zero hO hχ1')
b=b.replace('include hb hs hbs hχ hO hSeg hχ1 hOK hK hχK h01 hη hηs hηU hO\' hKO\' hη1 hKU in','include hbs hχ hO hSeg hχ1 hOK hK hχK h01 hη hηs hηU hO\' hKO\' hη1 in')
b=b.replace('pairing hb hs hbs','pairing hbs').replace("hη1' hKU E E' hE","hη1' E E' hE")
b=b.replace('Complex.integral_logDeriv_wedge_add_finsum_eq_integral_dbarLogDeriv','Wedge.integral_wedge_residue_identity')
old="""    have hev : χC χ =ᶠ[𝓝 z] fun _ => (0 : ℂ) := notMem_tsupport_iff_eventuallyEq.1 hz'
    simp only [Dχ, D, hev.fderiv_eq, fderiv_fun_const, Pi.zero_apply,
      ContinuousLinearMap.zero_apply, mul_zero, add_zero, zero_div]"""
assert old in b
b=b.replace(old,"    exact D_eq_zero_of_notMem_tsupport hz'")
a=b.index('theorem isCompact_segment');e=b.index('theorem exists_cutoff',a)
b=b[:a]+b[e:]
b=b.replace('have hSegc : IsCompact Seg := isCompact_segment b s',"""have hSegc : IsCompact Seg := by
    rw [hSegdef, segment_eq_image]
    exact isCompact_Icc.image (by continuity)""")
b=b.replace('(segment_subset_U hb hs)','((Complex.convex_halfSpace_im_gt 0).segment_subset hb hs)')
docs={'dbarL':'Antiholomorphic coordinate projection of a real differential.','χC':'The real cutoff viewed as a complex-valued function.','dfun':'Compactly supported modification of the ratio (z-s)/(z-b), with pole value zero.','gfun':'The formula for the dipole away from its pole.','wfun':'The numerator of the cutoff dipole.','Dχ':'Antiholomorphic derivative of the complex-valued cutoff.','Ffun':'Continuous compactly supported logarithmic antiholomorphic derivative of the dipole.'}
for n,d in docs.items():b=b.replace('def '+n+' ','/-- '+d+' -/\ndef '+n+' ')
head="""/-! Adapted from anthropics/fermats-last-theorem (Apache-2.0), pinned
S_UpperHalfPlane_exists_localModel_pair_integral_mul_dbarLogDeriv_eq.
DUB-17/18 -> original all-weight arithmetic association -> actual Gamma1
Picard/H1 -> Abel-Jacobi converse -> analytic reciprocity -> smooth invariant
comparison function -> compact dipole with exact integer local orders.
The existing wedge/residue identity and antiholomorphic derivative are reused.
This constructs a smooth local comparison, without assuming meromorphic
realization or the desired principal-divisor converse. -/
namespace Dubon2026.SourceComplexReciprocity.Dipole
noncomputable section
open Complex MeasureTheory Filter Set Metric DbarFundamental
open scoped Real Topology Manifold ContDiff
local notation "𝕌" => {z : ℂ | 0 < z.im}

"""
core=b[b.index('variable {b s'):b.index('/-- The real cutoff')]
# No generality beyond the actual cutoff needed for the dipole.
i=b.index('include hO hχ1 in\n\ntheorem Dχ_eq_zero')
j=b.index('variable {η')
k=b.index('end Core')
sections=[
('SourceComplexDipoleLocalModel','import Dubon2026.SourceComplexDbarCutoff\n\n',b[:i]+'end Core\n'),
('SourceComplexDipoleLogDerivative','import SourceComplexDipoleLocalModel\n\n','section Core\n'+core+b[i:j]+'end Core\n'),
('SourceComplexDipolePairing','import SourceComplexDipoleLogDerivative\nimport SourceComplexWedgeIntegral\n\n','section Core\n'+core+b[j:k]+'end Core\n'),
('SourceUpperHalfPlaneDipole','import SourceComplexDipolePairing\n\n',b[k+len('end Core'):].replace('theorem main','theorem exists_localModel_pair'))
]
for n,imp,body in sections:
 with (p/(n+'.lean')).open('x',encoding='utf-8',newline='\n') as f:f.write(imp+head+body+'end\nend Dubon2026.SourceComplexReciprocity.Dipole\n')
route=dict(chain=['DUB-17/18','original all-weight arithmetic association','actual Gamma1 Picard/H1','Abel-Jacobi converse','analytic reciprocity','smooth invariant comparison V','compact dipole'],primary=dict(path=str(src),sha256=hashlib.sha256(src.read_bytes()).hexdigest().upper(),read='Entire primary read before adaptation.'),reuse='Existing DbarFundamental.D and D_eq_zero_of_notMem_tsupport reused. Existing audited Wedge.integral_wedge_residue_identity proves exact pairing; native convex_halfSpace_im_gt discharges segment containment. Native smooth Urysohn cutoff supplies compact support. The unused source segment helpers are omitted.',scope='Construct actual smooth dipole with orders +1 at s and -1 at b and exact integral pi*(E(s)-E(b)); these are the factors of the required invariant comparison function.',remaining='Orbit product, removable regularization, exact stabilizer multiplicity and degree-zero cancellation for V; quotient, winding-period comparison, reciprocity, principal-divisor converse and full all-weight chain remain. 16/20; DUB-17--20 OPEN.')
with (p/'complex-dipole-reuse-route-891.json').open('x',encoding='utf-8') as f:json.dump(route,f,indent=2)
