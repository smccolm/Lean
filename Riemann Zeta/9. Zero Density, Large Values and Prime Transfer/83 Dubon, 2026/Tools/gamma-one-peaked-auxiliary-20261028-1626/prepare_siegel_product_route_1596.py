from pathlib import Path
import json,hashlib
from datetime import datetime,timezone
s=Path(__file__).parent
p=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
inputs=[s/'anthropic-peaked-leaves-1535/S_ModularCurve_SiegelUnit_exists_isIntegral_hasSum_prod_siegelFun_pow.lean.txt',p/'SourcePowerSeriesProduct.lean',p/'SourceRealizedPowerSeries.lean',s/'SourceIntegralTracePowerCoefficients.lean',s/'SourceSiegelCoefficientSeries1591c.lean']
record=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> original Gamma1 degree/genus preservation -> reduced field action -> level-power slash integrality -> actual peaked auxiliary -> exact integral finite Siegel product expansion.',reuseChecked=[dict(path=str(f),sha256=hashlib.sha256(f.read_bytes()).hexdigest().upper()) for f in inputs],shorterRoute='Reuse the proved native q-series multiplication and cusp-limit theorems, and the audited trace coefficient multiplication/power lemmas. Our explicit single-factor coefficients represent every residue pair, including (0,0); exponent zero handles that factor exactly. This eliminates the candidate choice construction, dummy series and repeated integrality algebra. Split finite-series closure, literal phases, leading coefficient and final assembly; no raised proof limits.',assumptionsToDischarge=['Actual finite product has the exact source normalized series with integral coefficients.','Its specified constant coefficient is nonzero from e(0,0)=0.','Its level-cleared constant coefficient inverse is integral.','Its literal phase satisfies C^N=1.','Its cusp limit equals that constant coefficient.'],remaining='Discriminant adjustment, cusp order and decay bounds, and actual peaked auxiliary existence. Reduced field action, degree/genus preservation, integral parabolic transfer, characteristic-zero realization, automorphy and literal higher continuation remain open. Acceptance remains 16/20; DUB-17--20 OPEN.',externalBuild=False,externalImport=False,proofLimitsChanged=False)
f=s/'siegel-finite-product-route-review-1596.json';assert not f.exists();f.write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
src=inputs[0].read_text(encoding='utf-8')
c=src[src.index('variable (h : ℝ)'):src.index('end SExpPi')]
c=c.replace('def Expands','/-- Exact q-series realization on the upper half-plane. -/\ndef Expands').replace('ModularCurve.hasSum_qParam_mul','Dubon2026.SourceFunctionField.Realized.hasSum_qParam_mul')
header='''import Dubon2026.SourcePowerSeriesProduct
import SourceIntegralTracePowerCoefficients

/-! DUB-17/18 -> original Gamma1 degree/genus preservation -> level-power
slash integrality -> actual peaked auxiliary -> integral finite Siegel product.
Reuse the native exact q-series product and the audited trace coefficient
algebra. Only finite powers/products needed by the actual auxiliary are added.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_SiegelUnit_exists_isIntegral_hasSum_prod_siegelFun_pow. -/
namespace Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.FiniteExpansion
noncomputable section
open Complex Filter Finset Topology

'''
tail='''
theorem coeff_prod_mem {R : Subring ℂ} {ι : Type*} (s : Finset ι)
    (A : ι → PowerSeries ℂ) (h : ∀ i ∈ s, ∀ n, PowerSeries.coeff n (A i) ∈ R) (n : ℕ) :
    PowerSeries.coeff n (∏ i ∈ s, A i) ∈ R := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, PowerSeries.coeff_one]
    split_ifs <;> simp [R.one_mem, R.zero_mem]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact Dubon2026.SourceFunctionField.IntegralTrace.coeff_mul_mem
      (h a (Finset.mem_insert_self a s)) (fun m => ih (fun i hi => h i (Finset.mem_insert_of_mem hi)) m) n

end
end Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.FiniteExpansion
'''
f=s/'SourceSiegelFiniteSeriesProducts1596a.lean';assert not f.exists();f.write_text(header+c+tail,encoding='utf-8')
print('Prepared actual finite-product route and minimal series consumer.')
