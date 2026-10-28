from pathlib import Path
import re,json,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
src=p/'gamma-one-local-model-construction-reuse-889/S_ModularCurve_exists_invariant_localModel_dbarLogDeriv_eq_sum_finsum_translate_of_finiteIndex.lean.txt'
s=src.read_text(encoding='utf-8-sig')
a=s[s.index('theorem coe_ofComplex'):s.index('theorem im_smul_le_max')]
for n in ['sm_neg','dsm_neg']:
 pat=r'theorem '+n+r'\b[\s\S]*?(?=\ntheorem|\ndef)'
 a,k=re.subn(pat,'',a,count=1);assert k==1,n
a=a.replace('def sm ','/-- Actual upper-half-plane action extended by the standard complex retraction. -/\ndef sm ').replace('def dsm ','/-- The actual holomorphic derivative of the determinant-one action. -/\ndef dsm ')
b=s[s.index('theorem im_le_of_sm_mem'):s.index('theorem finite_moving (')]
b=b.replace('im_smul_le_max','SourceSmoothedFundamental.im_smul_le_max')
c=s[s.index("theorem finite_moving'"):s.index('def iPt')]
c=c[:c.index('scoped instance finite_stabilizer')]
c=c.replace('finite_moving _ _','SourceSmoothedFundamental.finite_moving _ _').replace('isCompact_coe_preimage','SourceSmoothedFundamental.isCompact_coe_preimage').replace('(finite_moving {τ} {s}','(SourceSmoothedFundamental.finite_moving {τ} {s}')
head="""import SourceModularSmoothCover

/-! DUB-17/18 -> original all-weight arithmetic association -> Gamma1 Picard/H1
-> Abel-Jacobi converse -> analytic reciprocity -> invariant comparison V.
These are the actual action and local-finiteness facts needed for the orbit
product of compact dipoles. The existing smooth-partition geometry supplies
the height bound, compact preimages and proper discontinuity. Native analytic
action supplies derivatives, avoiding repeated Mobius calculations.
Adapted from the pinned Apache-2.0 construction recorded in scope 889. -/
namespace Dubon2026.SourceSmoothDivisor
noncomputable section
open UpperHalfPlane hiding I
open Filter Complex Set
open scoped MatrixGroups Topology Real
local notation "𝕌" => UpperHalfPlane.upperHalfPlaneSet

"""
with (p/'SourceSmoothModularGeometry.lean').open('x',encoding='utf-8',newline='\n') as f:f.write(head+a+b+c+'end\nend Dubon2026.SourceSmoothDivisor\n')
