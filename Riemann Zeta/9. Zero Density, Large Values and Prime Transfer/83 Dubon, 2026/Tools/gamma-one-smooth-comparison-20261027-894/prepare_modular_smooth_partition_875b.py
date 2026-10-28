from pathlib import Path
import json,re,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
d=p/'anthropic-flt-residual-closure-20261020/Definitions/Def_ModularCurve_SmoothedFundamental.lean.txt'
s=p/'anthropic-flt-residual-closure-20261020/P2M/Sol/S_ModularCurve_contDiff_and_finsum_smoothedFundamental_eq_one.lean.txt'
dt=d.read_text(encoding='utf-8-sig');st=s.read_text(encoding='utf-8-sig')
ns='Dubon2026.SourceSmoothedFundamental'
header="""/-! DUB-17/18 -> original all-weight arithmetic association -> actual Gamma1
Picard/H1 comparison -> Abel-Jacobi converse -> analytic reciprocity ->
winding/period limit -> smooth modular orbit partition. This constructs the
specific compact smooth family required by the source integral limit.
It assumes neither a period identity nor a principal-divisor realization.
Native proper discontinuity, Mobius imaginary-part identity, and coset
equivalence are reused. The central sign is not quotiented away here. -/
"""
def write(n,t):
 if (p/n).exists():
  assert n=='SourceModularSmoothCutoff.lean' and (p/n).read_text(encoding='utf-8')==t
 else:
  with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(t)
def remove_decl(t,n):
 pat=r'(?m)^(?:theorem|def) '+re.escape(n)+r'\b[\s\S]*?(?=^(?:theorem|def) |\Z)'
 out,num=re.subn(pat,'',t);assert num==1,(n,num);return out
b=dt[dt.index('def mob '):dt.rindex('end ModularCurve.SmoothedFundamental')]
b=b.replace('end ModularCurve.SmoothedFundamental\n','').replace('namespace ModularCurve.SmoothedFundamental\n','')
b=b.replace('ModularCurve.SmoothedFundamental.','').replace('ModularCurve.smoothedFundamental','smoothedFundamental')
# Defer source helpers which are not consumed in this smoothing contract.
for n in ['pOne_le_one','pOne_sub_one_add','pTwo_le_one','bump_le_one','gcut_eq_zero','tsupport_bump_subset','tsupport_pu_subset','tsupport_puCut_subset']:
 b=remove_decl(b,n)
docs={'mob':'The literal complex fractional-linear transformation, defined on all of C.',
'pOne':'Compact horizontal smooth cutoff.','pTwo':'Height-dependent compact vertical smooth cutoff.',
'bump':'Product of the horizontal and vertical smooth cutoffs.',
'box':'Compact rectangle containing the support of the product cutoff.',
'recip':'Smooth regularized reciprocal, exact above one half.',
'gcut':'Smooth upper-height truncation.','cover':'Sum of the cutoff over all integral modular transforms.',
'pu':'Cutoff normalized by the regularized orbit sum.','puCut':'Normalized cutoff with upper-height truncation.',
'smoothedFundamental':'Coset sum of the normalized cutoff for the actual subgroup.'}
for n,doc in docs.items():b=b.replace('def '+n+' ', '/-- '+doc+' -/\ndef '+n+' ',1)
write('SourceModularSmoothCutoff.lean','import Mathlib\n\n'+header+'namespace '+ns+'\nnoncomputable section\nopen UpperHalfPlane Set\nopen scoped MatrixGroups Topology\n\n'+b+'\nend\nend '+ns+'\n')
g=st[st.index('theorem det_entries'):st.index('theorem pOne_contDiff')]
for n in ['det_entries','num_eq','analyticAt_denom','analyticAt_num','denom_ne_zero\'','mob_inv_mob']:g=remove_decl(g,n)
a=g.index('theorem analyticAt_mob');z=g.index('theorem mob_contDiffAt')
g=g[:a]+"""theorem analyticAt_mob (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    AnalyticAt ℂ (mob γ) z := by
  unfold mob num denom
  exact ((analyticAt_const.mul analyticAt_id).add analyticAt_const).div
    ((analyticAt_const.mul analyticAt_id).add analyticAt_const)
    (UpperHalfPlane.denom_ne_zero_of_im γ hz.ne')

"""+g[z:]
a=g.index('theorem im_mob');z=g.index('theorem im_pos_of_im_mob_pos')
g=g[:a]+"""theorem im_mob (γ : SL(2, ℤ)) (z : ℂ) :
    (mob γ z).im = z.im / Complex.normSq (denom γ z) := by
  simpa [mob] using UpperHalfPlane.moebius_im (γ : GL (Fin 2) ℝ) z

"""+g[z:]
write('SourceModularSmoothGeometry.lean','import SourceModularSmoothCutoff\n\n'+header+'namespace '+ns+'\nnoncomputable section\nopen UpperHalfPlane hiding I coe_smul\nopen Filter Complex MulAction Set\nopen scoped MatrixGroups Topology ContDiff Pointwise\n\n'+g+'end\nend '+ns+'\n')
route=dict(chain=['DUB-17/18','all-weight arithmetic association','actual original Gamma1 coefficient Hecke realization','Picard/H1','Abel-Jacobi converse','analytic reciprocity','winding-period limit','compact smooth orbit partition'],primary=[dict(path=str(f),sha256=hashlib.sha256(f.read_bytes()).hexdigest().upper(),read='Entire source read before adaptation') for f in [d,s]],reuse=['Native ProperlyDiscontinuousSMul.finite_disjoint_inter_image','Native UpperHalfPlane.moebius_im eliminates determinant-entry algebra','Native Subgroup.groupEquivQuotientProdSubgroup assessed for exact Quotient.out representatives','Existing projective fundamental domain and generic transport/unfolding reviewed; existing Gamma0 domain is not silently substituted for Gamma1'],scope='Literal compact cutoff and proper modular geometry; partition and integral limit to follow. Unconsumed elementary bounds and identities deferred.',remaining='Analytic reciprocity and actual principal-divisor converse remain, followed by original all-weight arithmetic association, automorphy and literal higher symmetric powers. 16/20; DUB-17--20 OPEN.')
write('modular-smooth-partition-route-875.json',json.dumps(route,indent=2)+'\n')
