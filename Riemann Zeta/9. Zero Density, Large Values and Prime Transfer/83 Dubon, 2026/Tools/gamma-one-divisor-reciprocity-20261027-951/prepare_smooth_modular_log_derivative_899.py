from pathlib import Path
p=Path(r'E:\Lean\.tmp\dubon83')
s=(p/'gamma-one-local-model-construction-reuse-889/S_ModularCurve_exists_invariant_localModel_dbarLogDeriv_eq_sum_finsum_translate_of_finiteIndex.lean.txt').read_text(encoding='utf-8-sig')
b=s[s.index('theorem dbarL_comp_smul'):s.index('end Dbar')]
b=b.replace('dbar_eq_dbarL','SourceComplexReciprocity.Dipole.dbar_eq')
head="""import SourceSmoothProjectiveOrbitSum
import SourceComplexDipoleLocalModel

/-! DUB-17/18 -> original all-weight arithmetic association -> Gamma1 Picard/H1
-> Abel-Jacobi converse -> analytic reciprocity -> invariant comparison V.
Actual local product and action rules identify V's antiholomorphic logarithmic
derivative. The existing DbarFundamental.D and Dipole.dbarL operations are
reused; no second derivative operator is introduced. Adapted from the pinned
Apache-2.0 scope-889 construction. The finite product is later supplied by
proper discontinuity, rather than assumed for the whole orbit product. -/
namespace Dubon2026.SourceSmoothDivisor
noncomputable section
open UpperHalfPlane hiding I
open Complex Filter
open SourceComplexReciprocity.Dipole
open scoped MatrixGroups Topology ComplexConjugate
local notation "dbar" => SourceComplexReciprocity.DbarFundamental.D

"""
with (p/'SourceSmoothModularLogDerivative.lean').open('x',encoding='utf-8',newline='\n') as f:f.write(head+b+'end\nend Dubon2026.SourceSmoothDivisor\n')
