from pathlib import Path
from datetime import datetime,timezone
import json,hashlib
s=Path(__file__).parent;p=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
paths=[s/'anthropic-even-integrality-depth-1503/S_ModularCurve_SiegelUnit_exists_gamma1_peaked_auxiliary_form_twelve_dvd.lean.txt',s/'anthropic-peaked-core-1533/S_ModularCurve_SiegelUnit_isIntegral_qExpansion_slash_S_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow.lean.txt',p/'SourceGammaOneCuspAuxiliaryForm.lean',s/'SourceSiegelCuspPermutation1604a.lean',s/'SourcePeakedShiftedSeries1613c.lean']
r=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain='DUB-17/18 -> original all-weight characteristic-zero association -> Gamma1 degree/genus preservation -> level-power slash integrality -> actual even-weight peaked auxiliary -> integral slash-S expansion and source order arithmetic.',reuseChecked=[dict(path=str(f),sha256=hashlib.sha256(f.read_bytes()).hexdigest().upper()) for f in paths],shorterRoute='The required auxiliary is existential. Scale the already constructed separating exponent family by N; this preserves nonnegativity, translation invariance, zero pair, positivity and strict cusp separation while making the infinity order visibly divisible by N. This avoids the candidate additive-orbit divisibility framework without changing the source endpoint. Choose the discriminant power to make every shifted order nonnegative. Then the proved row permutation and a minimally generalized monomial shift give the integral expansion of every translated actual form, using the existing strict-period-under-conjugation theorem and native coefficient uniqueness. The external unrestricted slash-S theorem infers nonnegative order from boundedness and builds a new GammaS subgroup; those generalities are unnecessary for the chosen auxiliary, whose nonnegative order is already proved.',assumptionsToDischarge=['Every shifted cusp order is nonnegative for the chosen discriminant power.','The actual infinity order is a level multiple by proved exponent scaling.','Actual slash-S coefficients are integral, using the constructed nonnegative shift.','All hypotheses of the existing even-weight trace integrality theorem are supplied by a constructed auxiliary.'],remaining='Implement the scaling and power choice, translated coefficient consumer and actual auxiliary assembly; then apply the trace theorem and continue to reduced field action, degree/genus and downstream arithmetic association. Acceptance remains 16/20; DUB-17--20 OPEN.',externalBuild=False,externalImport=False,proofLimitsChanged=False)
def write(n,t):
 f=s/n;assert not f.exists(),f;f.write_text(t,encoding='utf-8')
write('peaked-cusp-shorter-route-1619.json',json.dumps(r,indent=2)+'\n')
c=(s/'SourcePeakedShiftedSeries1613c.lean').read_text(encoding='utf-8')
a=c.index('/-- The actual monomial');b=c.index('theorem hasSum_adjustedSeries',a)
defs='''/-- The actual Siegel and discriminant series shifted by a specified cusp order. -/
def shiftedSeries (N : ℕ) [NeZero N] (m : ZMod N → ZMod N → ℕ) (t M : ℕ) : PowerSeries ℂ :=
  phase N m • (PowerSeries.X ^ M * (productSeries N m * deltaN N ^ t))

/-- The actual shifted series when the infinity order is N times the width-one order. -/
def adjustedSeries (N : ℕ) [NeZero N] (m : ZMod N → ZMod N → ℕ) (t m₀ : ℕ) : PowerSeries ℂ :=
  shiftedSeries N m t (N * m₀)

'''
theorem=c[b:c.index('\nend\n',b)]
general=theorem.replace('hasSum_adjustedSeries','hasSum_shiftedSeries').replace('(t m₀ : ℕ)','(t M : ℕ)').replace('(N : ℤ) * m₀','(M : ℤ)').replace('adjustedSeries N m t m₀','shiftedSeries N m t M').replace('N * m₀','M')
wrapper=theorem[:theorem.index(' := by')]+''' :=
  hasSum_shiftedSeries N m t (N * m₀) (by simpa only [Nat.cast_mul] using hm₀) τ

theorem integral_shiftedSeries (N : ℕ) [NeZero N] (m : ZMod N → ZMod N → ℕ) (t M k : ℕ) :
    IsIntegral ℤ (coeff k (shiftedSeries N m t M)) := by
  simp only [shiftedSeries, coeff_smul, smul_eq_mul, coeff_X_pow_mul']
  split_ifs
  · exact (isIntegral_phase N m).mul (integral_product_delta N m t _)
  · rw [mul_zero]; exact isIntegral_zero
'''
write('SourcePeakedShiftedSeries1613d.lean',c[:a]+defs+general+'\n\n'+wrapper+c[c.index('\nend\n',b):])
c=(s/'SourcePeakedWidthOneIdentification1617a.lean').read_text(encoding='utf-8').replace('SourcePeakedShiftedSeries1613c','SourcePeakedShiftedSeries1613d').replace('[adjustedSeries, coeff_smul','[adjustedSeries, shiftedSeries, coeff_smul')
a=c.index(' := by',c.index('theorem integral_adjustedSeries'));b=c.index('\nend\n',a)
c=c[:a]+' :=\n  integral_shiftedSeries N m t (N * m₀) k\n'+c[b:]
write('SourcePeakedWidthOneIdentification1617b.lean',c)
c=(s/'SourcePeakedIntegralQExpansion1618a.lean').read_text(encoding='utf-8').replace('SourcePeakedWidthOneIdentification1617a','SourcePeakedWidthOneIdentification1617b')
write('SourcePeakedIntegralQExpansion1618b.lean',c)
print('Recorded endpoint-preserving scaling route and generalized only the necessary cusp shift.')
