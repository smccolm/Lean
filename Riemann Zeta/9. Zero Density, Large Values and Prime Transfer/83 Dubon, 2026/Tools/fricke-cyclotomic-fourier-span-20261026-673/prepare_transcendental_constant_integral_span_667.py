from pathlib import Path
import re,json,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
src=p/'fricke-base-change-dependencies-reuse-662/P2M/Sol/S_IsIntegral_mem_span_of_adjoin_simple_constants_transcendental.lean.txt'
s=src.read_text(encoding='utf-8')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
def part(a,b):return s[s.index(a):s.index(b)]
header='''/-! DUB-17/18 -> original all-weight arithmetic association -> actual
Gamma1 character realization -> differential/cusp comparison -> rational
Fourier spanning -> integral base change of Fricke fractions. This is the
transcendental constant-adjoining step of the finite constant-list induction.
Native integral closure and polynomial normality recover integral coefficients
after clearing scalar denominators. The original finite generator integrality
and j transcendence are explicit inputs, supplied later by the actual Fricke field.
Adapted from anthropics/fermats-last-theorem,
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0,
S_IsIntegral_mem_span_of_adjoin_simple_constants_transcendental.
All source proof-limit settings are omitted; native limits are unchanged. -/
namespace Dubon2026.SourceFricke.ConstantDescent
noncomputable section
open Polynomial
open scoped IntermediateField IntermediateField.algebraAdjoinAdjoin
variable {K : Type*} [Field K] [Algebra ℂ K]
variable (F : IntermediateField ℚ ℂ) (t : K) (S : Set K)
'''
tail='\nend\nend Dubon2026.SourceFricke.ConstantDescent\n'
core=part('abbrev RFld','theorem algebraMap_adjoinF_mem')
core=core.replace('abbrev RFld','/-- The rational coordinate field over the original constants. -/\nabbrev RFld').replace('abbrev KFldT','/-- The finite generator field viewed over the rational coordinate field. -/\nabbrev KFldT').replace('abbrev RFa','/-- The integral closure of the original coordinate algebra in the generator field. -/\nabbrev RFa').replace('def TRngEquiv','/-- Polynomial evaluation identifies the transcendental coordinate algebra. -/\ndef TRngEquiv')
instnames=['scalarTowerBaseRationalGenerated','scalarTowerBaseGeneratedAmbient','faithfulSMulBaseGenerated','isDomainCoordinateRing']
for name in instnames:
 core=core.replace('scoped instance :','scoped instance '+name+' :',1)
core=re.sub(r'^(noncomputable scoped instance|scoped instance) (\\w+)',r'/-- The native scalar structure on the actual coordinate and generator fields. -/\\n\\1 \\2',core,flags=re.M)
# The preceding regex is intentionally checked below; normal names are inserted explicitly if needed.
core=re.sub(r'(?m)^(noncomputable scoped instance|scoped instance) ([A-Za-z]\\w*)',lambda m:'/-- The native scalar structure on the actual coordinate and generator fields. -/\n'+m[0],core)
evalbody=part('theorem t_mem_RSet','theorem exists_clear_denominator')
evalbody=evalbody.replace('def rfPolyEval','/-- Evaluation of integral-closure polynomials at the new constant. -/\ndef rfPolyEval')
evalbody='''theorem algebraMap_subfield_apply (c : F) :
    algebraMap F K c = algebraMap ℂ K (c : ℂ) := rfl

'''+evalbody
denom=part('theorem exists_clear_denominator','variable {F t}')
main=part('theorem mem_span_RSet_of_adjoin_simple_transcendental','variable (F) in\ntheorem mem_KFld_iff_closure')
main=main.replace('closure_adjoin_le F S hxK','closure_adjoin_le F (S := S) hxK')
native='''import SourceAlgebraicConstantLift
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.Polynomial.GaussLemma
'''
mods=[
('SourceTranscendentalConstantAlgebra',native,core),
('SourceTranscendentalConstantEvaluation','import SourceTranscendentalConstantAlgebra\n',evalbody),
('SourceTranscendentalConstantDenominators','import SourceTranscendentalConstantEvaluation\n','variable {c : ℂ}\n\n'+denom),
('SourceTranscendentalConstantIntegralSpan','import SourceTranscendentalConstantDenominators\nimport Mathlib.Tactic.LinearCombination\n','variable {F t}\n\n'+main)]
for m,imp,body in mods:
 body=re.sub(r'^set_option .*\n','',body,flags=re.M)
 body=body.replace('TRng F t','TRng F {t}').replace('RSet F t S','RSet F {t} S')
 f=p/(m+'.lean');assert not f.exists(),f
 f.write_text(imp+'\n'+header+body+tail,encoding='utf-8')
 assert not re.search(r'^set_option|import P2M|\\\\1|\\\\2',f.read_text(encoding='utf-8'),re.M),f
route=p/'transcendental-constant-integral-span-route-667.json';assert not route.exists()
reuse=[src,p/'SourceConstantExtensionIntegralAlgebra.lean',p/'SourceAlgebraicConstantLift.lean',p/'SourceFrickeJTranscendence.lean',p/'SourceFrickeCyclotomicMonic.lean']
route.write_text(json.dumps(dict(scope=667,chain='DUB-17/18 -> original all-weight arithmetic association -> actual Gamma1 characters -> Picard/H1 and differential/cusp comparison -> rational Fourier spanning -> integral base change of actual Fricke fractions -> finite constant-list induction -> transcendental constant-adjoining descent.',
assumptionsToDischarge='At a transcendental constant-adjoining step, every integral element of the enlarged generated field lies in the complex span of elements integral over the original coordinate algebra. Derive the finite generator extension, Dedekind integral closure and polynomial integrally-closed instance from actual finite integral generators and j transcendence; clear scalar denominators and recover polynomial coefficients.',
reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in reuse],
shorterRouteReview='Reuse the algebraic-step coefficient algebra and embedding helpers from scope 666. Native integral-closure and polynomial normality theorems provide the remaining commutative algebra. No pinned Mathlib base-change normalization/span theorem was found. The existing coordinate regularity result addresses only a rational coordinate subfield. The actual j-transcendence input is already proved, and scope 665 supplies cyclotomic monic descent. Omit duplicate source wrappers, repeated coefficient structures, source limit increases and final closure reformulations.',
sourceCommit='6e837e75355538c7f80bab5b956861e86c4eacc2',sourceLicense='Apache-2.0',externalImport=False,externalFullClosureVerified=False,rootPinsChanged=False,proofLimitsChanged=False,modules=[m for m,_,_ in mods],
remaining='This is a necessary foundation, not a gate closure. Finite constant-list induction, actual Fricke-field instantiation, relative transcendence from Fourier coefficient independence, holomorphic representative recovery, rational Fourier spanning, arbitrary Gamma1 differential realization and the remaining arithmetic association/automorphy/higher continuation chain remain. 16/20; DUB-17--20 OPEN.'),indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(modules=len(mods),lines=sum(len((p/(m+'.lean')).read_text(encoding='utf-8').splitlines()) for m,_,_ in mods),limitsRaised=False)))