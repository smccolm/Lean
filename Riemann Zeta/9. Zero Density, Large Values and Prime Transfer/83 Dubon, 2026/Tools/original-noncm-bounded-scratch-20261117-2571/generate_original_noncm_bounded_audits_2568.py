from pathlib import Path
import json,re,hashlib,datetime
s=Path(__file__).parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
versions=['SourceNonCMInertPrime2560a','SourceNonCMInertIntegerObstruction2561a','SourceOriginalCoefficientReductionObstruction2562b','SourceNonCMOriginalInertReductionBound2563a','SourceNonCMBoundedConductorReduction2564c','SourceOriginalBoundedQuadraticFrobenius2565a','SourceOriginalNonCMBoundedInputsProperty2566a','SourceGammaOneOriginalNonCMBoundedInputs2567a']
pairs=[(v,re.sub(r'\d{4}[a-z]$','',v)) for v in versions]
old=json.loads((s/'source-original-exceptional-exclusion-audit-config-2552.json').read_text())
mods=[m for _,m in pairs];assert len(mods)==8
mapping=set(old['modules']+mods)
review=json.loads((s/'original-noncm-selftwist-route-review-2560.json').read_text())
review.update(recordedUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),completedMathematicalObligation='The actual non-CM form supplies one bound, uniform over every primitive nontrivial quadratic Dirichlet character of conductor at most M and every original local coefficient embedding. Above that bound the same original residual action has an inert good-prime norm Frobenius with nonzero trace. The complete original integral/residual, local Hecke, determinant, oddness, auxiliary-prime and CM conclusions are retained, together with the three remaining small-image cases.',boundary='A dihedral-character comparison and a conductor bound independent of residual characteristic still must be proved. No dihedral branch or final gate is closed; DUB-17--20 remain OPEN at 16/20.',scopeModules=mods)
planned={}
for source,module in pairs:
 f=s/(source+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0',source
 assert f.with_suffix('.log').stat().st_size==0,source
 def mapped(m):
  n=m[1]; b=re.sub(r'\d{4}[a-z]?$','',n);return 'import '+(b if b in mapping else n)
 t=re.sub(r'(?m)^import (\S+)',mapped,f.read_text(encoding='utf-8'))
 assert not (s/(module+'.lean')).exists()
 assert all(n.startswith(('Mathlib.','Dubon2026.')) or n in mapping for n in re.findall(r'^import (\S+)',t,re.M))
 planned[module]=t
for row in old['files']:assert sha(Path(row['path']))==row['canonicalSha256']
def write(n,t):
 f=s/n;assert not f.exists(),n;f.write_text(t,encoding='utf-8')
write('original-noncm-bounded-reuse-review-2568.json',json.dumps(review,indent=2)+'\n')
c=dict(files=[],modules=mods,queries=[],theorems=[],constructions=[],roots=[],proofEdges=[],scope=review['completedMathematicalObligation'],sourceAssemblyReview=review)
for source,module in pairs:
 f=s/(source+'.lean');t=planned[module];write(module+'.lean',t);canonical=s/(module+'.lean')
 c['files'].append(dict(source=str(f),sourceSha256=sha(f),module=module,path=str(canonical),canonicalSha256=sha(canonical)))
 ns=re.search(r'^namespace (\S+)',t,re.M)[1]
 th=[ns+'.'+n for n in re.findall(r'^theorem (\S+)',t,re.M)];df=[ns+'.'+n for n in re.findall(r'^def (\S+)',t,re.M)]
 c['queries']+=th+df;c['theorems']+=th;c['constructions']+=df
c['roots']=[c['theorems'][-1]]
c['proofEdges']=list(dict.fromkeys(old['proofEdges']+c['queries']+['Dubon2026.coefficientSelfTwist_iff_inert_zero','Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction.sourcePrimitiveFieldCoefficient_coe']))
arr=lambda xs:'#['+', '.join('`'+n for n in xs)+']'
for a,b in [('SourceOriginalExceptionalExclusionAudit1','SourceOriginalNonCMBoundedAudit1'),('SourceOriginalExceptionalExclusionDependencyAudit1','SourceOriginalNonCMBoundedDependencyAudit1'),('SourceOriginalExceptionalExclusionDeclarations2552','SourceOriginalNonCMBoundedDeclarations2568')]:
 t=(s/(a+'.lean')).read_text(encoding='utf-8');t=re.sub(r'^import Source.*\n','',t,flags=re.M);t='import '+mods[-1]+'\n'+t
 if 'Audit' in a and 'Dependency' not in a:
  t=re.sub(r'^#print axioms .*\n','',t,flags=re.M);t=t.replace('open Lean\n','open Lean\n\n'+'\n'.join('#print axioms '+q for q in c['queries'])+'\n',1)
  t=re.sub(r'let modules : Array Name := #\[.*\]','let modules : Array Name := '+arr(mods),t)
  t=re.sub(r'^#lint in .*\n','',t,flags=re.M);t+='\n'.join('#lint in '+m for m in mods)+'\n'
  t=t.replace('SOURCE ORIGINAL EXCEPTIONAL EXCLUSION AXIOM AUDIT PASS','SOURCE ORIGINAL NONCM BOUNDED AXIOM AUDIT PASS')
 elif 'Dependency' in a:
  for label,values in [('roots',c['roots']),('localModules',old['modules']+mods),('required',c['proofEdges'])]:t=re.sub('let '+label+r' : Array Name := #\[.*\]','let '+label+' : Array Name := '+arr(values),t)
  t=re.sub(r'logInfo m!"SOURCE ORIGINAL EXCEPTIONAL EXCLUSION VALUE AUDIT PASS:.*"','logInfo m!"SOURCE ORIGINAL NONCM BOUNDED VALUE AUDIT PASS: all {required.size} required proof dependencies occur in the actual original non-CM consumer proof-value closure. Original non-CM coefficients, literal reduction and bounded-conductor inert Frobenius witnesses are consumed. The dihedral character comparison and its uniform conductor bound remain open, with DUB-17--20 OPEN."',t)
 else:t=re.sub(r'let mods : Array Name := #\[.*\]','let mods : Array Name := '+arr(mods),t)
 write(b+'.lean',t)
write('source-original-noncm-bounded-audit-config-2568.json',json.dumps(c,indent=2)+'\n')
t=(s/'SourceOriginalExceptionalExclusionScratchSemantic2553.lean').read_text(encoding='utf-8');t=re.sub(r'^import Source.*\n','',t,flags=re.M);t='import '+mods[-1]+'\n'+t
for label,values in [('moduleNames',old['modules']+mods),('auditedModuleNames',mods)]:t=re.sub('private def '+label+r' : Array String := #\[.*\]','private def '+label+' : Array String := #['+', '.join(json.dumps(x) for x in values)+']',t)
write('SourceOriginalNonCMBoundedScratchSemantic2569.lean',t)
write('SourceOriginalNonCMBoundedProductionSemantic2569.lean',re.sub(r'^import (Source\S+)',r'import Dubon2026.\1',t,flags=re.M))
lines=["$ErrorActionPreference='Stop'",r"$taskScratch='E:\Lean\.tmp\dubon83'"]
for m in mods:lines+=["& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name '"+m+"'",'if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}']
for m in ['SourceOriginalNonCMBoundedAudit1','SourceOriginalNonCMBoundedDependencyAudit1','SourceOriginalNonCMBoundedDeclarations2568','SourceOriginalNonCMBoundedScratchSemantic2569']:
 lines+=["& (Join-Path $taskScratch 'run_dickson_audit_2285.ps1') -Name '"+m+"'",'if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}']
write('build_original_noncm_bounded_2568.ps1','\n'.join(lines)+'\n')
print(json.dumps(dict(modules=len(mods),queries=len(c['queries']),theorems=len(c['theorems']),definitions=len(c['constructions']),requiredValueEdges=len(c['proofEdges']))))
