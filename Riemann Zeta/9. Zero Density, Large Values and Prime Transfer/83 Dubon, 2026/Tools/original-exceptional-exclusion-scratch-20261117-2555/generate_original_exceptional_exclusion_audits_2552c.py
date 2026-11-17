from pathlib import Path
import json,hashlib,re,datetime
s=Path(__file__).parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
versions=['SourceExceptionalProjectiveExponent2523b','SourceOriginalExceptionalScalarPower2524a','SourceExceptionalTraceChebyshev2525b','SourceExceptionalNormalizedSquare2526b','SourceOriginalExceptionalTraceEquation2527c','SourceExceptionalIntegralPolynomial2530d','SourceExceptionalPolynomialConstant2531b','SourceOriginalExceptionalPolynomialRoot2532c','SourceExceptionalRootArithmetic2533b','SourceExceptionalValuationParity2534b','SourceExceptionalNumberFieldRoot2535b','SourceExceptionalCoefficientNonvanishing2536a','SourceExceptionalUnramifiedPrime2537c','SourceExceptionalCoefficientPrimeSupport2538b','SourceOriginalIdentityFrobenius2539a','SourceOriginalLocalNonzeroPrimeCoefficient2541d','SourceOriginalNonzeroPrimeCoefficient2540f','SourceOriginalExceptionalPrimeObstruction2542b','SourceNonzeroAlgebraicIntegerRelation2543c','SourceIntegerRelationReduction2544d','SourceIntegralPolynomialRatio2545a','SourceOriginalExceptionalIntegerObstruction2546a','SourceOriginalExceptionalFixedObstruction2547b','SourceOriginalFixedLocalExceptionalExclusion2548b','SourceOriginalExceptionalUniformBound2549b','SourceNonexceptionalSmallAlternatives2550a','SourceGammaOneOriginalNonexceptionalInputs2551b']
pairs=[(v,re.sub(r'\d{4}[a-z]$','',v)) for v in versions]
mods=[m for _,m in pairs];assert len(mods)==len(set(mods))==27
review=dict(recordedUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),dependency='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> automorphy -> eventual large original residual image -> arithmetic exclusion of A4, S4 and A5 in the same original projective representation.',sourceContract='The actual primitive cusp form has weight at least two; all original integral/residual representation data, residue field and topology, literal reduction, good-prime Hecke characteristic polynomial, determinant, oddness, original auxiliary primes and genuine CM deformation conclusions are retained. A form-dependent bound removes exactly A4/S4/A5. No new image certificate or nonzero residual Fourier coefficient is assumed.',reuse=[dict(result='Native original integral and residual arithmetic realizations and all good-prime Frobenius data',use='Identity Chebotarev at p=5 produces an actual nonzero prime Fourier coefficient outside every finite set; the same original local Frobenius data later supplies the exceptional trace equation.'),dict(result='Mathlib finite-group exponent and matrix Cayley-Hamilton; native Chebyshev recurrence',use='Exceptional projective group orders divide 120. Original matrices have scalar 120th powers; normalized squares give the fixed integer trace polynomial.'),dict(result='Native finite ramification, unramified valuation of the rational coefficient prime and actual source weight parity',use='The nonzero-trace polynomial is monic with constant -14400; an integral root has valuation one away from that constant, whereas the actual coefficient-square divided by q^(k-1) has nonzero odd valuation.'),dict(result='Mathlib IsAlgebraic.exists_nonzero_coeff_and_aeval_eq_zero and restriction of algebraicity from rationals to integers',use='The nonzero actual characteristic-zero obstruction has an integer relation with fixed nonzero constant. This avoids a separate norm/denominator-clearing framework.'),dict(result='Mathlib local residue-unit equivalence, polynomial evaluation under ring maps and characteristic-divisibility',use='A unit q gives the literal integral ratio. Exceptional reduction forces the characteristic to divide the fixed nonzero constant, impossible above its absolute value.')],routeAdjustment='Use the full fixed polynomial in residue characteristic, including its zero root. Nonzero Fourier reduction is unnecessary; only the original characteristic-zero coefficient needs to be nonzero. Three unused nonzero-residue/root-unit corollaries are retained in historical scratch variants but deferred from the selected scope.',remaining='Cyclic, dihedral and elementary-abelian-by-cyclic projective branches remain explicit. Their arithmetic exclusions, required local deformation conditions, CM disjointness where required, automorphy and literal higher continuation remain open. These are unrestricted polarized deformation rings. No final acceptance gate is closed; 16/20 accepted and DUB-17--20 OPEN.',noProductionMutation=True,pinsChanged=False,limitsChanged=False)
reviewpath=s/'original-exceptional-exclusion-reuse-review-2552.json'
assert not reviewpath.exists()
planned={}
for source,module in pairs:
 f=s/(source+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0',source
 assert f.with_suffix('.log').stat().st_size==0,source
 t=f.read_text(encoding='utf-8')
 def qualify(m):
  name=m[1]; base=re.sub(r'\d{4}[a-z]?$','',name)
  return 'import '+(base if base in mods else name)
 t=re.sub(r'(?m)^import (\S+)',qualify,t)
 assert not (s/(module+'.lean')).exists(),module
 assert all(n.startswith(('Mathlib.','Dubon2026.')) or n in mods for n in re.findall(r'^import (\S+)',t,re.M)),module
 planned[module]=t
c=dict(files=[],modules=[],queries=[],theorems=[],constructions=[],roots=[],proofEdges=[],scope=review['sourceContract'])
def write(name,t):
 f=s/name;assert not f.exists(),name;f.write_text(t,encoding='utf-8')
write(reviewpath.name,json.dumps(review,indent=2)+'\n')
for source,module in pairs:
 f=s/(source+'.lean');t=planned[module];write(module+'.lean',t);canonical=s/(module+'.lean')
 c['files'].append(dict(source=str(f),sourceSha256=sha(f),module=module,path=str(canonical),canonicalSha256=sha(canonical)))
 c['modules'].append(module)
 ns=re.search(r'(?m)^namespace (\S+)',t)[1]
 th=[ns+'.'+n for n in re.findall(r'(?m)^theorem (\S+)',t)]
 df=[ns+'.'+n for n in re.findall(r'(?m)^def (\S+)',t)]
 c['queries']+=th+df;c['theorems']+=th;c['constructions']+=df
c['roots']=[c['theorems'][-1]]
prior=json.loads((s/'source-original-cm-dimensions-audit-config-2518.json').read_text())
c['proofEdges']=list(dict.fromkeys(prior['proofEdges']+c['queries']+['IsAlgebraic.exists_nonzero_coeff_and_aeval_eq_zero','IsAlgebraic.restrictScalars','IsLocalization.isAlgebraic','Polynomial.IsRoot.dvd_coeff_zero','CharP.intCast_eq_zero_iff','IsLocalRing.residue_ne_zero_iff_isUnit','Dubon2026.absolute_continuous_exists_norm_frobenius_conjugate']))
c['sourceAssemblyReview']=review
arr=lambda xs:'#['+', '.join('`'+n for n in xs)+']'
for a,b in [('SourceOriginalCMDimensionsAudit1','SourceOriginalExceptionalExclusionAudit1'),('SourceOriginalCMDimensionsDependencyAudit1','SourceOriginalExceptionalExclusionDependencyAudit1'),('SourceOriginalCMDimensionsDeclarations2518','SourceOriginalExceptionalExclusionDeclarations2552')]:
 t=(s/(a+'.lean')).read_text(encoding='utf-8');t=re.sub(r'(?m)^import Source.*\n','',t);t='import '+mods[-1]+'\n'+t
 if 'Audit' in a and 'Dependency' not in a:
  t=re.sub(r'(?m)^#print axioms .*\n','',t);t=t.replace('open Lean\n','open Lean\n\n'+'\n'.join('#print axioms '+q for q in c['queries'])+'\n',1)
  t=re.sub(r'let modules : Array Name := #\[.*\]','let modules : Array Name := '+arr(mods),t)
  t=re.sub(r'(?m)^#lint in .*\n','',t);t+='\n'.join('#lint in '+m for m in mods)+'\n'
  t=t.replace('SOURCE ORIGINAL CM DIMENSIONS AXIOM AUDIT PASS','SOURCE ORIGINAL EXCEPTIONAL EXCLUSION AXIOM AUDIT PASS')
 elif 'Dependency' in a:
  for label,values in [('roots',c['roots']),('localModules',mods),('required',c['proofEdges'])]:t=re.sub('let '+label+r' : Array Name := #\[.*\]','let '+label+' : Array Name := '+arr(values),t)
  t=re.sub(r'logInfo m!"SOURCE ORIGINAL CM DIMENSIONS VALUE AUDIT PASS:.*"','logInfo m!"SOURCE ORIGINAL EXCEPTIONAL EXCLUSION VALUE AUDIT PASS: all {required.size} required proof dependencies occur in the actual original-form consumer proof-value closure. The original residual realization, fixed Fourier obstruction, literal integral reduction and exact remaining projective alternatives are consumed. DUB-17--20 remain OPEN."',t)
 else:t=re.sub(r'let mods : Array Name := #\[.*\]','let mods : Array Name := '+arr(mods),t)
 write(b+'.lean',t)
write('source-original-exceptional-exclusion-audit-config-2552.json',json.dumps(c,indent=2)+'\n')
t=(s/'SourceOriginalCMDimensionsScratchSemantic2519.lean').read_text(encoding='utf-8');t=re.sub(r'(?m)^import Source.*\n','',t);t='import '+mods[-1]+'\n'+t
for label in ['moduleNames','auditedModuleNames']:t=re.sub('private def '+label+r' : Array String := #\[.*\]','private def '+label+' : Array String := #['+', '.join(json.dumps(x) for x in mods)+']',t)
write('SourceOriginalExceptionalExclusionScratchSemantic2553.lean',t)
write('SourceOriginalExceptionalExclusionProductionSemantic2553.lean',re.sub(r'(?m)^import (Source\S+)',r'import Dubon2026.\1',t))
lines=["$ErrorActionPreference='Stop'",r"$taskScratch='E:\Lean\.tmp\dubon83'"]
for m in mods:lines+=["& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name '"+m+"'",'if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}']
for m in ['SourceOriginalExceptionalExclusionAudit1','SourceOriginalExceptionalExclusionDependencyAudit1','SourceOriginalExceptionalExclusionDeclarations2552','SourceOriginalExceptionalExclusionScratchSemantic2553']:
 lines+=["& (Join-Path $taskScratch 'run_dickson_audit_2285.ps1') -Name '"+m+"'",'if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}']
write('build_original_exceptional_exclusion_2552.ps1','\n'.join(lines)+'\n')
print(json.dumps(dict(modules=len(mods),publicQueries=len(c['queries']),publicTheorems=len(c['theorems']),publicConstructions=len(c['constructions']),requiredEdges=len(c['proofEdges']))))
