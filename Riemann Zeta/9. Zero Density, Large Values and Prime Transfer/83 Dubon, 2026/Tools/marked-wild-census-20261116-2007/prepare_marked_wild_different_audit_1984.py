from pathlib import Path
from datetime import datetime, timezone
import ast, hashlib, json, re
p=Path(__file__).parent
src=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
versions=['SourceMarkedEmbeddingSignKernel1975a','SourceMarkedOriginalNormalField1976b','SourceMarkedOriginalNormalFieldTwo1977a','SourceMarkedOriginalNormalFieldThree1978a','SourceMarkedOriginalLocalDifferentials1979f','SourceMarkedOriginalWildDifferent1980b','SourceMarkedOriginalWildDifferentTwo1981a','SourceMarkedOriginalWildDifferentThree1982a']
mapping={v:re.sub(r'\d+[a-z]$','',v) for v in versions}
modules=list(mapping.values());queries=[];files=[]
def output(name,text):
 f=p/name;assert not f.exists(),f
 if name.endswith('.py'):ast.parse(text)
 f.write_text(text,encoding='utf-8')
for v,m in mapping.items():
 f=p/(v+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0
 assert not (src/(m+'.lean')).exists()
 t=f.read_text(encoding='utf-8');ns=re.search(r'(?m)^namespace (\S+)',t)[1]+'.'
 queries += [ns+n for n in re.findall(r'(?m)^(?:@\[[^]]*\] )?(?:theorem|lemma)\s+(\S+)',t)]
 c=re.sub(r'(?m)^import (\S+)$',lambda x:'import '+mapping.get(x[1],x[1]),t)
 assert re.sub(r'(?m)^import .*\n','',c)==re.sub(r'(?m)^import .*\n','',t)
 output(m+'.lean',c)
 files.append(dict(version=v,module=m,sourcePath=str(f),originalSha256=sha(f),canonicalSha256=sha(p/(m+'.lean')),mathematicalBodyIdentical=True))
assert len(queries)==len(set(queries))==10
mc='Dubon2026.SourceFunctionField.MarkedChart.'
roots=[mc+'original_fourteen_le_different_of_j_order_twelve',mc+'original_seven_le_different_of_j_order_six']
edges=queries+[
 mc+'exists_original_ofJ_full_torsion_chart',mc+'exists_exactOrder_point_of_full_torsion',mc+'original_coordinate_isSeparable',
 'Dubon2026.SourceCurve.coordinateEmbeddingFixingField','Dubon2026.SourceCurve.coordinateEmbeddingIntoFixingField',
 'Dubon2026.SourceCurve.coordinateEmbedding_fixingField_isGalois','Dubon2026.SourceCurve.coordinateEmbeddingIntoFixingField_coordinate','Dubon2026.SourceCurve.coordinateEmbedding_fixingField_fixed',
 'Dubon2026.SourceEllipticDivisionField.exists_char_two_exceptional_inertia_sign','Dubon2026.SourceEllipticDivisionField.exists_char_three_exceptional_inertia_permutation',
 'Dubon2026.SourceCurve.Place.normal_coordinate_order_dvd_of_inertia_kernel',
 'Dubon2026.SourceCurve.Place.rational_wild_different_bound','Dubon2026.SourceCurve.Place.ordDifferential_map_of_ramificationIndex_one_all_char']
assert len(edges)==len(set(edges))==23
cfg=dict(modules=modules,theorems=queries,constructions=[],queries=queries,roots=roots,proofEdges=edges,compileEvidence={m:m+'-1984' for m in modules},separatelyAxiomChecked=[])
output('source-marked-wild-different-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
output('marked-wild-different-versions-1984.json',json.dumps(files,indent=2)+'\n')
imports='\n'.join('import '+m for m in modules)+'\nimport Mathlib.Tactic\n\nopen Lean\n\n'
def array(t,name,names):
 t,n=re.subn(r'(?m)^  let '+name+r' : Array Name := #\[.*$','  let '+name+' : Array Name := #['+', '.join('`'+x for x in names)+']',t)
 assert n==1;return t
seen=set(modules);upstream=[]
def local_imports(m):
 for n in re.findall(r'(?m)^import (\S+)$',(p/(m+'.lean')).read_text(encoding='utf-8')):
  if '.' not in n and n not in seen and (p/(n+'.lean')).exists():seen.add(n);upstream.append(n);local_imports(n)
for m in modules:local_imports(m)
for old,new in [('SourceMarkedExceptionalFibersAudit1','SourceMarkedWildDifferentAudit1'),('SourceMarkedExceptionalFibersDependencyAudit1','SourceMarkedWildDifferentDependencyAudit1'),('SourceMarkedExceptionalFibersScratchOwnership1974','SourceMarkedWildDifferentScratchOwnership1984')]:
 t=(p/(old+'.lean')).read_text(encoding='utf-8');t=t[t.index('private def'):]
 t=t.replace('MarkedExceptionalFibers','MarkedWildDifferent').replace('SOURCE MARKED EXCEPTIONAL FIBERS','SOURCE MARKED WILD DIFFERENT')
 if 'Dependency' in old:
  for n,ns in [('roots',roots),('localModules',modules+upstream),('required',edges)]:t=array(t,n,ns)
  a,b=t.index('  logInfo m!'),t.index('\n\n#eval')
  t=t[:a]+'  logInfo m!"SOURCE MARKED WILD DIFFERENT DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the VALUE closure of the original Gamma1 different bounds fourteen and seven. Inertia sign kernels construct the normal fields; local differential hypotheses are proved. Wild fiber census, small levels and reverse genus remain open; DUB17--20 OPEN."'+t[b:]
 elif 'Ownership' in old:t=array(t,'mods',modules)
 else:
  t=t[:t.index('\n#lint')]
  for n,ns in [('modules',modules),('theorems',queries),('constructions',[])]:t=array(t,n,ns)
  t='\n'.join('#print axioms '+n for n in queries)+'\n\n'+t+'\n'+'\n'.join('#lint in '+m for m in modules)+'\n'
 output(new+'.lean',imports+t)
reuse=['SourceCoordinateEmbeddingFixingField','SourceCoordinateEmbeddingFixedFieldMap','SourceNormalFieldCoordinateOrder','SourceEllipticCharTwoInertiaSign','SourceEllipticCharThreeInertiaPermutationR2','SourceRatFuncWildDifferent','SourceCurveUnramifiedDifferentialAllChar','SourceCurveSeparatingLocalFinite','SourceCurveFiniteCoordinateResidues','SourceModularCoefficientDifferentials','SourceModularCharTwoStrongDifferent','SourceModularCharThreeStrongDifferent']
paths=[src/(n+'.lean') for n in reuse]
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain='DUB17 Theorem2.6 / DUB18 Cor8.2 -> literal higher symmetric-power continuation -> automorphy -> original all-weight association -> homogeneous Gamma1 realization -> original genus preservation -> reverse genus -> characteristic-two/three wild different contribution.',shorterRoute='Reuse the native coordinate-embedding fixed field, actual inertia sign kernels, normal coordinate order theorem and all-characteristic unramified differential transport. No new general local ramification theory is needed. The final endpoints concern the original Gamma1 field and assume only the actual level/characteristic conditions and the specified j order.',assumptionsToDischarge=['Sign kernels fix all normalized original embeddings.','The actual original field embeds in a constructed normal auxiliary field with positive j orders dividing twelve or six.','Original j has nonzero differential, rank-one differentials and generating local uniformizer differential.','At a place attaining the auxiliary order bound, the extension ramification index is one.','Native wild different bounds descend, giving fourteen at order twelve in characteristic two and seven at order six in characteristic three.'],remaining='Wild numerical fiber census, small levels and reverse genus remain open, followed by original association and higher continuation. Acceptance16/20; DUB17--20 OPEN.',boundary='Eight focused modules compile. Exhaustive scratch audit, promotion and assembled verification pending. No conditional normal-field or local differential certificate remains in the two final bounds.',reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in paths])
output('source-marked-wild-different-audit-route-1984.json',json.dumps(route,indent=2)+'\n')
replacements={'MarkedExceptionalFibers':'MarkedWildDifferent','marked_exceptional_fibers':'marked_wild_different','marked-exceptional-fibers':'marked-wild-different','SOURCE MARKED EXCEPTIONAL FIBERS':'SOURCE MARKED WILD DIFFERENT','1974':'1984'}
def tr(t):
 for a,b in replacements.items():t=t.replace(a,b)
 return t
t=tr((p/'build_marked_exceptional_fibers_canonical_1974.ps1').read_text(encoding='utf-8'))
t=re.sub(r'(?m)^\$names=@\(.*$', '$names=@('+','.join("'"+m+"'" for m in modules)+')',t)
output('build_marked_wild_different_canonical_1984.ps1',t)
output('audit_marked_wild_different_1984.ps1',tr((p/'audit_marked_exceptional_fibers_1974.ps1').read_text(encoding='utf-8')))
t=tr((p/'record_marked_exceptional_fibers_1974.py').read_text(encoding='utf-8'))
t=t.replace('(12, 20, 30)','(8, 10, 23)').replace('== 12','== 8').replace('linterScopes=12','linterScopes=8').replace('all 30 required','all 23 required').replace('requiredProofValueEdges=30','requiredProofValueEdges=23').replace('modules=12, queries=20','modules=8, queries=10').replace('proofEdges=30','proofEdges=23')
output('record_marked_wild_different_1984.py',t)
print(json.dumps(dict(modules=8,queries=10,proofEdges=23)))
