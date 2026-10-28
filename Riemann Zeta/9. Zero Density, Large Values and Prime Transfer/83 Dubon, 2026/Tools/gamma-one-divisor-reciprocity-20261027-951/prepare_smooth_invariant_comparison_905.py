from pathlib import Path
import shutil
p=Path(r'E:\Lean\.tmp\dubon83')
d=p/'smooth-divisor-log-derivative-failed-904a';d.mkdir();f=p/'SourceSmoothDivisorLogDerivative.lean';shutil.copy2(f,d/f.name)
s=f.read_text(encoding='utf-8').replace('    · exact h\n    · exact Filter.mem_of_superset','    · simpa only [Data.V, zpow_zero, one_mul] using h\n    · exact Filter.mem_of_superset');f.write_text(s,encoding='utf-8')
s=(p/'gamma-one-local-model-construction-reuse-889/S_ModularCurve_exists_invariant_localModel_dbarLogDeriv_eq_sum_finsum_translate_of_finiteIndex.lean.txt').read_text(encoding='utf-8-sig')
b=s[s.index('theorem main (Γ'):s.index('end ModularCurve.DivisorFunctionOf')]
b=b.replace('theorem main','theorem exists_invariant_comparison')
b=b.replace('UpperHalfPlane.exists_localModel_pair_integral_mul_dbarLogDeriv_eq','SourceComplexReciprocity.Dipole.exists_localModel_pair')
head="""import SourceSmoothDivisorLogDerivative
import SourceUpperHalfPlaneDipole

/-! DUB-17/18 -> original all-weight arithmetic association -> Gamma1 Picard/H1
-> Abel-Jacobi converse -> analytic reciprocity -> invariant smooth comparison V.
Construct V from the actual invariant finite integer-order data. Compact
dipoles, local finite products, exact projective stabilizer counts and zero
weighted degree discharge all local orders, invariance, cusp normalization
and logarithmic derivative requirements. Its compact coefficient functions
retain the exact integral pi times endpoint difference.
Adapted from the pinned Apache-2.0 scope-889 primary with native projective
fibers and existing local analytic facts. No global V property is assumed. -/
namespace Dubon2026.SourceSmoothDivisor
noncomputable section
open UpperHalfPlane hiding I
open MeasureTheory Filter Complex Set
open scoped MatrixGroups Topology Real Classical ComplexConjugate

"""
with (p/'SourceSmoothInvariantComparison.lean').open('x',encoding='utf-8',newline='\n') as f:f.write(head+b+'end\nend Dubon2026.SourceSmoothDivisor\n')
