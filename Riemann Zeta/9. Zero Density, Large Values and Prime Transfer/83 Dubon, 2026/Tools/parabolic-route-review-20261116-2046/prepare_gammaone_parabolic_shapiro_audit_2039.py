from pathlib import Path
from datetime import datetime, timezone
import ast, hashlib, json, re
p=Path(__file__).parent
src=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
versions=['SourceParabolicShapiroPotentials2033c','SourceOriginalCoinducedLocalCoboundary2034b','SourceParabolicTracePowers2035a','SourceGammaOneParabolicShapiro2036b','SourceGammaOneParabolicShapiroComparison2038d']
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
 c=re.sub(r'(?m)^import (\S+)$',lambda x:'import '+mapping.get(x[1],x[1]),t)
 assert re.sub(r'(?m)^import .*\n','',c)==re.sub(r'(?m)^import .*\n','',t)
 output(m+'.lean',c)
 files.append(dict(version=v,module=m,sourcePath=str(f),originalSha256=sha(f),canonicalSha256=sha(p/(m+'.lean')),mathematicalBodyIdentical=True))
assert (len(modules),len(queries),len(theorems),len(constructions))==(5,8,8,0)
assert len(queries)==len(set(queries))
roots=['Dubon2026.sourceGammaOneConstantH1Transfer_parabolic']
edges=queries+[
 'Dubon2026.SourceIntegralCharacterLift.exists_potential',
 'Dubon2026.SourceIntegralCharacterLift.isCrossed_shapiro',
 'Dubon2026.sourceGammaOneDiagonalHom_binary_trivial',
 'Dubon2026.sourceShapiroH1_evaluation_lift',
 'Dubon2026.sourceGammaOneSubgroupH1Iso_hom_eq_map',
 'Dubon2026.sourceParabolicCocycles_coefficientMap',
 'Dubon2026.SourceParabolic.classification',
 'Dubon2026.SourceManin.trace_conj']
assert len(edges)==len(set(edges))==16

cfg=dict(modules=modules,theorems=theorems,constructions=constructions,queries=queries,roots=roots,proofEdges=edges,compileEvidence={m:m+'-2039' for m in modules},separatelyAxiomChecked=[])
output('source-gammaone-parabolic-shapiro-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
output('gammaone-parabolic-shapiro-versions-2039.json',json.dumps(files,indent=2)+'\n')
imports='\n'.join('import '+m for m in modules)+'\nimport Mathlib.Tactic\n\nopen Lean\n\n'
def array(t,name,names):
 t,n=re.subn(r'(?m)^  let '+name+r' : Array Name := #\[.*$','  let '+name+' : Array Name := #['+', '.join('`'+x for x in names)+']',t)
 assert n==1;return t
seen=set(modules);upstream=[]
def local_imports(m):
 for n in re.findall(r'(?m)^import (\S+)$',(p/(m+'.lean')).read_text(encoding='utf-8')):
  if '.' not in n and n not in seen and (p/(n+'.lean')).exists():seen.add(n);upstream.append(n);local_imports(n)
for m in modules:local_imports(m)
for old,new in [('SourceMarkedWildDifferentAudit1','SourceGammaOneParabolicShapiroAudit1'),('SourceMarkedWildDifferentDependencyAudit1','SourceGammaOneParabolicShapiroDependencyAudit1'),('SourceMarkedWildDifferentScratchOwnership1984','SourceGammaOneParabolicShapiroScratchOwnership2039')]:
 t=(p/(old+'.lean')).read_text(encoding='utf-8');t=t[t.index('private def'):]
 t=t.replace('MarkedWildDifferent','GammaOneParabolicShapiro').replace('SOURCE MARKED WILD DIFFERENT','SOURCE GAMMAONE PARABOLIC SHAPIRO')
 if 'Dependency' in old:
  for n,ns in [('roots',roots),('localModules',modules+upstream),('required',edges)]:t=array(t,n,ns)
  a,b=t.index('  logInfo m!'),t.index('\n\n#eval')
  t=t[:a]+'  logInfo m!"SOURCE GAMMAONE PARABOLIC SHAPIRO DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the VALUE closure of parabolic stability of the literal original Gamma1 counit transfer. Native orbit potentials construct local Shapiro coboundaries, and the original coefficient triviality and trace classification discharge their geometric inputs. The original constant-H1 comparison and native coefficient map finish stability. Parabolic surjectivity, association and higher continuation remain open; DUB17--20 OPEN."'+t[b:]
 elif 'Ownership' in old:t=array(t,'mods',modules)
 else:
  t=t[:t.index('\n#lint')]
  for n,ns in [('modules',modules),('theorems',theorems),('constructions',constructions)]:t=array(t,n,ns)
  t='\n'.join('#print axioms '+n for n in queries)+'\n\n'+t+'\n'+'\n'.join('#lint in '+m for m in modules)+'\n'
 output(new+'.lean',imports+t)
reuse=['SourceIntegralCharacterPotential','SourceIntegralCharacterShapiro','SourceShapiroH1CocycleComparison','SourceGammaOneCohomologyTransfer','SourceGammaOneSubgroupCohomologyMap','SourceGammaOneParabolicRestriction','SourceParabolicCoefficientMap','SourceParabolicClassification','SourceManinCuspStabilizer']
paths=[src/(n+'.lean') for n in reuse]
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain='DUB17 Theorem2.6 / DUB18 Cor8.2 -> literal higher symmetric-power continuation -> automorphy -> original all-weight association -> homogeneous Gamma1 realization -> parabolic transfer -> local Shapiro comparison and parabolic stability.',shorterRoute='The native orbit-potential theorem already handles arbitrary additive coefficients; no new finite-permutation or cohomological foundation is needed. Its scalar Shapiro cocycle matches the native coinduced coordinates. Original subgroup coefficient triviality, signed translation classification and native H1 pullback then prove the exact original parabolic comparison and counit stability.',assumptionsToDischarge=['Construct local coinduced coboundaries from literal vanishing on stabilizer powers, using existing orbit potentials.','Transport to the original coefficient action with native subgroup triviality.','Prove every required conjugate power remains parabolic from literal squared trace four.','Prove native Shapiro sends the original subgroup parabolic classes to coinduced parabolic classes.','Identify the actual Gamma1 constant-H1 comparison on cocycles and derive parabolic preservation of the original transfer.'],remaining='Parabolic stability is proved; it does not show that every reduced integral parabolic class has a parabolic preimage. That surjectivity, exceptional-prime removal, two-dimensional characteristic-zero realization, original all-weight association, automorphy and higher continuation remain required. Acceptance16/20; DUB17--20 OPEN.',boundary='Five focused modules compile. Exhaustive scratch audit, promotion and assembled verification pending.',reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in paths])
output('source-gammaone-parabolic-shapiro-audit-route-2039.json',json.dumps(route,indent=2)+'\n')
replacements={'MarkedWildDifferent':'GammaOneParabolicShapiro','marked_wild_different':'gammaone_parabolic_shapiro','marked-wild-different':'gammaone-parabolic-shapiro','SOURCE MARKED WILD DIFFERENT':'SOURCE GAMMAONE PARABOLIC SHAPIRO','1984':'2039','20261029':'20261116','2026-10-29 America/Vancouver':'2026-11-16 America/Whitehorse'}
def tr(t):
 for a,b in replacements.items():t=t.replace(a,b)
 return t
t=tr((p/'build_marked_wild_different_canonical_1984.ps1').read_text(encoding='utf-8'))
t=re.sub(r'(?m)^\$names=@\(.*$', '$names=@('+','.join("'"+m+"'" for m in modules)+')',t)
output('build_gammaone_parabolic_shapiro_canonical_2039.ps1',t)
output('audit_gammaone_parabolic_shapiro_2039.ps1',tr((p/'audit_marked_wild_different_1984.ps1').read_text(encoding='utf-8')))
t=tr((p/'record_marked_wild_different_1984.py').read_text(encoding='utf-8'))
t=t.replace('(8, 10, 23)','(5, 8, 16)').replace('== 8','== 5').replace('linterScopes=8','linterScopes=5').replace('all 23 required','all 16 required').replace('requiredProofValueEdges=23','requiredProofValueEdges=16').replace('modules=8, queries=10','modules=5, queries=8').replace('proofEdges=23','proofEdges=16')
output('record_gammaone_parabolic_shapiro_2039.py',t)
print(json.dumps(dict(modules=5,queries=8,theorems=8,constructions=0,proofEdges=16)))
