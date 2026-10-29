from pathlib import Path
s=Path(__file__).parent
f=s/'SourceSiegelPolynomialFactors1584a.lean';t=f.read_text(encoding='utf-8')
t=t.replace('(add_le_add_right (norm_sub_le _ _) _)','(add_le_add (norm_sub_le _ _) le_rfl)')
assert not f.with_suffix('.lean.txt').exists();f.rename(f.with_suffix('.lean.txt'))
n=s/'SourceSiegelPolynomialFactors1584b.lean';assert not n.exists();n.write_text(t,encoding='utf-8')
t=(s/'anthropic-siegel-dependencies-1553/S_ModularCurve_SiegelUnit_exists_isIntegral_hasSum_siegelFun.lean.txt').read_text(encoding='utf-8')
body=t[t.index('theorem coeff_one_sub_C_mul_X '):t.index('theorem Pc_coeff_zero ')]
body+=t[t.index('def CoeffInt '):t.index('theorem isIntegral_coeff_W ')]
body=body.replace('def CoeffInt ', '/-- Every coefficient of the actual finite polynomial lies in the integral closure of Z. -/\ndef CoeffInt ',1)
ns='Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.EulerExpansion'
f=s/'SourceSiegelIntegralCoefficients1585a.lean';assert not f.exists()
f.write_text('''import SourceSiegelPolynomialFactors1584b
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-! DUB-17/18 -> original Gamma1 degree/genus preservation -> level-power
slash integrality -> peaked auxiliary -> integral Siegel expansion.
The actual stabilized coefficient belongs to the integral closure because
it is already a coefficient of a finite product of integral linear
factors. No infinite-product integrality or closedness premise is needed.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_SiegelUnit_exists_isIntegral_hasSum_siegelFun. -/
namespace '''+ns+'''
noncomputable section
open Polynomial

'''+body+'''
theorem isIntegral_stableCoeff (N r : ℕ) {u v : ℂ}
    (hu : IsIntegral ℤ u) (hv : IsIntegral ℤ v) (m : ℕ) :
    IsIntegral ℤ (stableCoeff (Pc N r u v) m) :=
  coeffInt_pp N r hu hv m m

end
end '''+ns+'\n',encoding='utf-8')
