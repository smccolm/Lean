from pathlib import Path
from datetime import datetime, timezone
import ast, hashlib, json, re
p=Path(__file__).parent
src=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
versions=['SourceGammaOnePrimitiveCuspBoundary2047d','SourceGammaOneFiniteBinaryBoundary2048c','SourceGammaOnePrimitiveBoundaryOrbit2051a','SourceGammaOnePrimitiveCuspCoordinates2052b','SourceGammaOneBoundaryHeckeTrace2053a','SourceGammaOnePrimitiveBoundaryHeckeRows2054a']
mapping={v:re.sub(r'\d+[a-z]$','',v) for v in versions}
modules=list(mapping.values());queries=[];theorems=[];constructions=[];files=[]
def output(name,text):
 f=p/name;assert not f.exists(),f
 if name.endswith('.py'):ast.parse(text)
 f.write_text(text,encoding='utf-8')
for v,m in mapping.items():
 f=p/(v+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0
 assert not (src/(m+'.lean')).exists()
 t=f.read_text(encoding='utf-8');ns=re.search(r'(?m)^namespace (\S+)',t)[1]+'.'
 qs=re.findall(r'(?m)^(?:scoped |noncomputable )?(theorem|lemma|def|abbrev|instance)\s+(\S+)',t)
 queries += [ns+n for k,n in qs]
 theorems += [ns+n for k,n in qs if k in ['theorem','lemma']]
 constructions += [ns+n for k,n in qs if k not in ['theorem','lemma']]
 c=re.sub(r'(?m)^import (\S+)$',lambda x:'import '+mapping.get(x[1],{'SourceGammaOnePrimitiveCuspBoundary2047c':'SourceGammaOnePrimitiveCuspBoundary'}.get(x[1],x[1])),t)
 assert re.sub(r'(?m)^import .*\n','',c)==re.sub(r'(?m)^import .*\n','',t)
 output(m+'.lean',c)
 files.append(dict(version=v,module=m,sourcePath=str(f),originalSha256=sha(f),canonicalSha256=sha(p/(m+'.lean')),mathematicalBodyIdentical=True))
assert (len(modules),len(queries),len(theorems),len(constructions))==(6,17,14,3)
assert len(queries)==len(set(queries))
ns='Dubon2026.SourceFunctionField.GammaOne.'
roots=[ns+'binaryPrimePowerHeckeWord_parabolic_iff_primitive_boundary_zero',ns+'binaryPrimitiveCuspBoundary_ker',ns+'primitiveBoundaryHecke_exists_integer_rows']
separate=[ns+'primitiveCuspWidth_pos']
edges=[n for n in queries if n not in separate]+[
 'Dubon2026.SourceParabolic.classification',
 'MulAction.zpow_smul_eq_iff_minimalPeriod_dvd',
 'Dubon2026.SourceIntegralCharacterLift.trace_conj_T_zpow',
 'Dubon2026.sourcePrimePower_six_isUnit',
 'MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot',
 'Dubon2026.sourceTransfer_eq_coset_product',
 'Dubon2026.sourceGammaOneConstantHeckeH1_coefficient_hom_apply',
 'Dubon2026.SourceParabolic.exists_conj_T_zpow_of_trace_eq_two']
assert len(edges)==len(set(edges))==24

cfg=dict(modules=modules,theorems=theorems,constructions=constructions,queries=queries,roots=roots,proofEdges=edges,compileEvidence={m:m+'-2055' for m in modules},separatelyAxiomChecked=separate)
output('source-gammaone-primitive-boundary-2-audit-config.json',json.dumps(cfg,indent=2)+'\n')
output('gammaone-primitive-boundary-versions-2055.json',json.dumps(files,indent=2)+'\n')
imports='\n'.join('import '+m for m in modules)+'\nimport Mathlib.Tactic\n\nopen Lean\n\n'
def array(t,name,names):
 t,n=re.subn(r'(?m)^  let '+name+r' : Array Name := #\[.*$','  let '+name+' : Array Name := #['+', '.join('`'+x for x in names)+']',t)
 assert n==1;return t.replace('Audit1','Audit2').replace('boundary-1','boundary-2')
seen=set(modules);upstream=[]
def local_imports(m):
 for n in re.findall(r'(?m)^import (\S+)$',(p/(m+'.lean')).read_text(encoding='utf-8')):
  if '.' not in n and n not in seen and (p/(n+'.lean')).exists():seen.add(n);upstream.append(n);local_imports(n)
for m in modules:local_imports(m)
for old,new in [('SourceMarkedWildDifferentAudit1','SourceGammaOnePrimitiveBoundaryAudit2'),('SourceMarkedWildDifferentDependencyAudit1','SourceGammaOnePrimitiveBoundaryDependencyAudit2'),('SourceMarkedWildDifferentScratchOwnership1984','SourceGammaOnePrimitiveBoundaryScratchOwnership2055')]:
 t=(p/(old+'.lean')).read_text(encoding='utf-8');t=t[t.index('private def'):]
 t=t.replace('MarkedWildDifferent','GammaOnePrimitiveBoundary').replace('SOURCE MARKED WILD DIFFERENT','SOURCE GAMMAONE PRIMITIVE BOUNDARY')
 if 'Dependency' in old:
  for n,ns in [('roots',roots),('localModules',modules+upstream),('required',edges)]:t=array(t,n,ns)
  a,b=t.index('  logInfo m!'),t.index('\n\n#eval')
  t=t[:a]+'  logInfo m!"SOURCE GAMMAONE PRIMITIVE BOUNDARY DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the VALUE closure of the actual homogeneous H1 boundary kernel and prime-power word criterion. Native primitive periods and signed trace classification are consumed. The boundary word and its unit value remain unconstructed; DUB17--20 OPEN."'+t[b:]
 elif 'Ownership' in old:t=array(t,'mods',modules)
 else:
  t=t[:t.index('\n#lint')]
  for n,ns in [('modules',modules),('theorems',theorems),('constructions',constructions)]:t=array(t,n,ns)
  t='\n'.join('#print axioms '+n for n in queries)+'\n\n'+t+'\n'+'\n'.join('#lint in '+m for m in modules)+'\n'
 output(new+'.lean',imports+t)
prior=json.loads((p/'primitive-cusp-boundary-route-2047.json').read_text(encoding='utf-8'))
paths=[src/(n+'.lean') for n in ['SourceCuspCorrectionCyclicCosets','SourceParabolicClassification','SourceGammaOneBinaryParabolicH1','SourceIntegralCharacterModularFacts','SourceCosetTransfer']]
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain=prior['sourceChain'],shorterRoute=prior['shorterRouteAssessment'],assumptionsToDischarge=prior['assumptionsDischarged'],remaining=prior['remaining'],boundary='Six focused modules compile; two missing docstrings from the failed first scope have been corrected in a fresh retained version. Exhaustive scratch audit, production promotion and assembled verification pending.',reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in paths])
output('source-gammaone-primitive-boundary-audit-route-2055.json',json.dumps(route,indent=2)+'\n')

replacements={'MarkedWildDifferent':'GammaOnePrimitiveBoundary','marked_wild_different':'gammaone_primitive_boundary','marked-wild-different':'gammaone-primitive-boundary','SOURCE MARKED WILD DIFFERENT':'SOURCE GAMMAONE PRIMITIVE BOUNDARY','1984':'2055','20261029':'20261116','2026-10-29 America/Vancouver':'2026-11-16 America/Whitehorse'}
def tr(t):
 for a,b in replacements.items():t=t.replace(a,b)
 return t.replace('Audit1','Audit2').replace('boundary-1','boundary-2')
t=tr((p/'build_marked_wild_different_canonical_1984.ps1').read_text(encoding='utf-8'))
t=re.sub(r'(?m)^\$names=@\(.*$', '$names=@('+','.join("'"+m+"'" for m in modules)+')',t)
output('build_gammaone_primitive_boundary_canonical_2055.ps1',t)
output('audit_gammaone_primitive_boundary_2055.ps1',tr((p/'audit_marked_wild_different_1984.ps1').read_text(encoding='utf-8')))
t=tr((p/'record_marked_wild_different_1984.py').read_text(encoding='utf-8'))
t=t.replace('(8, 10, 23)','(6, 17, 24)').replace('== 8','== 6').replace('linterScopes=8','linterScopes=6').replace('all 23 required','all 24 required').replace('requiredProofValueEdges=23','requiredProofValueEdges=24').replace('modules=8, queries=10','modules=6, queries=17').replace('proofEdges=23','proofEdges=24')
output('record_gammaone_primitive_boundary_2055.py',t)
print(json.dumps(dict(modules=6,queries=17,theorems=14,constructions=3,proofEdges=24)))
