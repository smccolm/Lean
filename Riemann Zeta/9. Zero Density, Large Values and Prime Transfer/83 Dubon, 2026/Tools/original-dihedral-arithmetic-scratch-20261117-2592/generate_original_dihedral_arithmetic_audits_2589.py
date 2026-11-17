from pathlib import Path
import json,re,hashlib,datetime
s=Path(__file__).parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
versions=['SourceProjectiveInvolutionTrace2580b', 'SourceOriginalProjectiveInvolutionTrace2581a', 'SourceDihedralReflectionSign2582d', 'SourceOriginalDihedralCharacter2583c', 'SourceOriginalDihedralContinuity2584a', 'SourceOriginalDihedralArithmetic2585a', 'SourceOriginalNonCMDihedralInputsProperty2587a', 'SourceGammaOneOriginalDihedralInputs2588a']
pairs=[(v,re.sub(r'\d{4}[a-z]$','',v)) for v in versions]
old=json.loads((s/'source-original-noncm-bounded-audit-config-2568c.json').read_text())
prior=json.loads((s/'source-original-exceptional-exclusion-audit-config-2552.json').read_text())
inherited=prior['modules']+old['modules']
mods=[m for _,m in pairs];assert len(mods)==8
mapping=set(inherited+mods)
review=json.loads((s/'original-dihedral-character-route-review-2580.json').read_text())
review.update(recordedUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),completedMathematicalObligation='The same actual non-CM original integral and residual pair retains every prior arithmetic and CM conclusion and bounded-conductor inert Frobenius obstruction, and constructs each literal nontrivial continuous quadratic character of its original dihedral projective range. Negative values force zero original-field trace, and actual inertia away from Qp is trivial.',boundary='A dihedral-character comparison and a conductor bound independent of residual characteristic still must be proved. No dihedral branch or final gate is closed; DUB-17--20 remain OPEN at 16/20.',scopeModules=mods)
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
write('original-dihedral-arithmetic-reuse-review-2589.json',json.dumps(review,indent=2)+'\n')
c=dict(files=[],modules=mods,queries=[],theorems=[],constructions=[],roots=[],proofEdges=[],scope=review['completedMathematicalObligation'],sourceAssemblyReview=review)
for source,module in pairs:
 f=s/(source+'.lean');t=planned[module];write(module+'.lean',t);canonical=s/(module+'.lean')
 c['files'].append(dict(source=str(f),sourceSha256=sha(f),module=module,path=str(canonical),canonicalSha256=sha(canonical)))
 ns=re.search(r'^namespace (\S+)',t,re.M)[1]
 th=[ns+'.'+n for n in re.findall(r'^theorem (\S+)',t,re.M)];df=[ns+'.'+n for n in re.findall(r'^def (\S+)',t,re.M)]
 c['queries']+=th+df;c['theorems']+=th;c['constructions']+=df
c['roots']=[c['theorems'][-1]]
c['proofEdges']=list(dict.fromkeys(old['proofEdges']+c['queries']+['Dubon2026.rationalPrimeArithmeticRestriction_inertia_eq_one_of_away','AddMonoidHom.map_trace','Matrix.aeval_self_charpoly']))
arr=lambda xs:'#['+', '.join('`'+n for n in xs)+']'
for a,b in [('SourceOriginalNonCMBoundedAudit1','SourceOriginalDihedralArithmeticAudit1'),('SourceOriginalNonCMBoundedDependencyAudit3','SourceOriginalDihedralArithmeticDependencyAudit1'),('SourceOriginalNonCMBoundedDeclarations2568','SourceOriginalDihedralArithmeticDeclarations2589')]:
 t=(s/(a+'.lean')).read_text(encoding='utf-8');t=re.sub(r'^import Source.*\n','',t,flags=re.M);t='import '+mods[-1]+'\n'+t
 if 'Audit' in a and 'Dependency' not in a:
  t=re.sub(r'^#print axioms .*\n','',t,flags=re.M);t=t.replace('open Lean\n','open Lean\n\n'+'\n'.join('#print axioms '+q for q in c['queries'])+'\n',1)
  t=re.sub(r'let modules : Array Name := #\[.*\]','let modules : Array Name := '+arr(mods),t)
  t=re.sub(r'^#lint in .*\n','',t,flags=re.M);t+='\n'.join('#lint in '+m for m in mods)+'\n'
  t=t.replace('SOURCE ORIGINAL NONCM BOUNDED AXIOM AUDIT PASS','SOURCE ORIGINAL DIHEDRAL ARITHMETIC AXIOM AUDIT PASS')
 elif 'Dependency' in a:
  for label,values in [('roots',c['roots']),('localModules',inherited+mods),('required',c['proofEdges'])]:t=re.sub('let '+label+r' : Array Name := #\[.*\]','let '+label+' : Array Name := '+arr(values),t)
  t=re.sub(r'logInfo m!"SOURCE ORIGINAL NONCM BOUNDED VALUE AUDIT PASS:.*"','logInfo m!"SOURCE ORIGINAL DIHEDRAL ARITHMETIC VALUE AUDIT PASS: all {required.size} required proof dependencies occur in the actual original non-CM consumer proof-value closure. The original continuous quadratic character, actual projective involution trace relation, same original residue topology and original inertia triviality are consumed. The dihedral character comparison and its uniform conductor bound remain open, with DUB-17--20 OPEN."',t)
 else:t=re.sub(r'let mods : Array Name := #\[.*\]','let mods : Array Name := '+arr(mods),t)
 write(b+'.lean',t)
write('source-original-dihedral-arithmetic-audit-config-2589.json',json.dumps(c,indent=2)+'\n')
t=(s/'SourceOriginalNonCMBoundedScratchSemantic2569b.lean').read_text(encoding='utf-8');t=re.sub(r'^import Source.*\n','',t,flags=re.M);t='import '+mods[-1]+'\n'+t
allNames=json.loads(re.search(r'private def moduleNames : Array String := #(\[.*\])',t)[1])+mods
for label,values in [('moduleNames',list(dict.fromkeys(allNames))),('auditedModuleNames',mods)]:t=re.sub('private def '+label+r' : Array String := #\[.*\]','private def '+label+' : Array String := #['+', '.join(json.dumps(x) for x in values)+']',t)
write('SourceOriginalDihedralArithmeticScratchSemantic2590.lean',t)
write('SourceOriginalDihedralArithmeticProductionSemantic2590.lean',re.sub(r'^import (Source\S+)',r'import Dubon2026.\1',t,flags=re.M))
lines=["$ErrorActionPreference='Stop'",r"$taskScratch='E:\Lean\.tmp\dubon83'"]
for m in mods:lines+=["& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name '"+m+"'",'if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}']
for m in ['SourceOriginalDihedralArithmeticAudit1','SourceOriginalDihedralArithmeticDependencyAudit1','SourceOriginalDihedralArithmeticDeclarations2589','SourceOriginalDihedralArithmeticScratchSemantic2590']:
 lines+=["& (Join-Path $taskScratch 'run_dickson_audit_2285.ps1') -Name '"+m+"'",'if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}']
write('build_original_dihedral_arithmetic_2589.ps1','\n'.join(lines)+'\n')
print(json.dumps(dict(modules=len(mods),queries=len(c['queries']),theorems=len(c['theorems']),definitions=len(c['constructions']),requiredValueEdges=len(c['proofEdges']))))
