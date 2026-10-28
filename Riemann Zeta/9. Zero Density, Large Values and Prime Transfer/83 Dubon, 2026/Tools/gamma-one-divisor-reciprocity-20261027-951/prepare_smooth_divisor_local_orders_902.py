from pathlib import Path
import re
p=Path(r'E:\Lean\.tmp\dubon83')
s=(p/'gamma-one-local-model-construction-reuse-889/S_ModularCurve_exists_invariant_localModel_dbarLogDeriv_eq_sum_finsum_translate_of_finiteIndex.lean.txt').read_text(encoding='utf-8-sig')
b=s[s.index('theorem sm_eq_coe_iff'):s.index('theorem tendsto_sm_nhdsNE')]
b=b.replace('Rset (Γ)','projectiveIntegralSubgroup Γ').replace('Rset Γ','projectiveIntegralSubgroup Γ')
b=b.replace('sm ((δ : Γ) : SL(2, ℤ))','sm (representative Γ δ)').replace('sm ((p.2 : Γ) : SL(2, ℤ))','sm (representative Γ p.2)')
b=b.replace('((δ : Γ) : SL(2, ℤ)) •','δ •')
b=b.replace('simp only [sm, this]','simp only [sm, this, representative_smul]')
b=b.replace('two_mul_card_fibreR D.hneg','two_mul_card_projective_fibre Γ D.hneg').replace(' (Γ := Γ)','')
head="""import SourceSmoothDivisorLocalProduct

/-! DUB-17/18 -> original all-weight arithmetic association -> Gamma1 Picard/H1
-> Abel-Jacobi converse -> analytic reciprocity -> invariant comparison V.
Exact projective orbit-fiber counts identify the local product exponent with
the prescribed invariant integer order. The finite degree-zero sum cancels
the auxiliary base-point orders. Removable filling then gives the literal C1
integer local model of V. No global comparison-function property is assumed.
Adapted from the pinned Apache-2.0 scope-889 construction with native projective
fiber/kernel counting replacing its positive-matrix representatives. -/
namespace Dubon2026.SourceSmoothDivisor
noncomputable section
open UpperHalfPlane hiding I
open Filter Complex Set Metric
open SourceSmoothProjective SourceSmoothLocalModel
open scoped MatrixGroups Topology Real Classical
namespace Data
variable {Γ : Subgroup SL(2, ℤ)} (D : Data Γ)

"""
with (p/'SourceSmoothDivisorLocalOrders.lean').open('x',encoding='utf-8',newline='\n') as f:f.write(head+b+'end Data\nend\nend Dubon2026.SourceSmoothDivisor\n')
