from pathlib import Path
p=Path(r'E:\Lean\.tmp\dubon83')
s=(p/'gamma-one-local-model-construction-reuse-889/S_ModularCurve_exists_invariant_localModel_dbarLogDeriv_eq_sum_finsum_translate_of_finiteIndex.lean.txt').read_text(encoding='utf-8-sig')
b=s[s.index('theorem tendsto_sm_nhdsNE'):s.index('theorem dip_ne_zero')]
head="""import SourceSmoothDivisorLocalOrders

/-! DUB-17/18 -> original all-weight arithmetic association -> Gamma1 Picard/H1
-> Abel-Jacobi converse -> analytic reciprocity -> invariant comparison V.
Removable filling preserves actual subgroup invariance, and the proved height
bound makes the product equal one sufficiently high after every integral
translate. The source cusp condition is derived from the compact dipoles;
neither global invariance nor cusp normalization of V is an input.
Adapted from the pinned Apache-2.0 scope-889 construction. -/
namespace Dubon2026.SourceSmoothDivisor
noncomputable section
open UpperHalfPlane hiding I
open Filter Complex Set Metric
open SourceSmoothProjective SourceSmoothLocalModel
open scoped MatrixGroups Topology Real Classical
namespace Data
variable {Γ : Subgroup SL(2, ℤ)} (D : Data Γ)

"""
with (p/'SourceSmoothDivisorInvarianceCusps.lean').open('x',encoding='utf-8',newline='\n') as f:f.write(head+b+'end Data\nend\nend Dubon2026.SourceSmoothDivisor\n')
