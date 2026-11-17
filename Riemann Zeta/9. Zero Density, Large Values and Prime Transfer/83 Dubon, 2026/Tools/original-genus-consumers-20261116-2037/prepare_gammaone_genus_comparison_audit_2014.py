from pathlib import Path
from datetime import datetime, timezone
import ast, hashlib, json, re
p=Path(__file__).parent
src=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
versions=['SourceGammaOneConormDivisorSpaces2003a','SourceGammaOneConormDimension2004b','SourceGammaOneArithmeticGenus2005a','SourceGammaOneArithmeticGenusBound2006a']
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
assert (len(modules),len(queries),len(theorems),len(constructions))==(4,6,6,0)
assert len(queries)==len(set(queries))
gn='Dubon2026.SourceFunctionField.GammaOne.'
roots=[gn+'gamma1_arithmetic_genus_cusp_bound']
edges=queries+[
 gn+'ConstantField.degree_conorm',gn+'ConstantField.mem_span_of_regular_off_image',
 gn+'ConstantField.fieldMap_linearIndependent',
 'Dubon2026.SourceCurve.separating_coordinate_degree_dimension_maximum',
 'Dubon2026.SourceCurve.separating_coordinate_index_zero_eq_maximum',
 'Dubon2026.SourceCurve.finite_coordinate_finrank_regular_eq_genusFF',
 gn+'gammaOne_real_parabolic_dimension_upper']
assert len(edges)==len(set(edges))==13
cfg=dict(modules=modules,theorems=theorems,constructions=constructions,queries=queries,roots=roots,proofEdges=edges,compileEvidence={m:m+'-2014' for m in modules},separatelyAxiomChecked=[])
output('source-gammaone-genus-comparison-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
output('gammaone-genus-comparison-versions-2014.json',json.dumps(files,indent=2)+'\n')
imports='\n'.join('import '+m for m in modules)+'\nimport Mathlib.Tactic\n\nopen Lean\n\n'
def array(t,name,names):
 t,n=re.subn(r'(?m)^  let '+name+r' : Array Name := #\[.*$','  let '+name+' : Array Name := #['+', '.join('`'+x for x in names)+']',t)
 assert n==1;return t
seen=set(modules);upstream=[]
def local_imports(m):
 for n in re.findall(r'(?m)^import (\S+)$',(p/(m+'.lean')).read_text(encoding='utf-8')):
  if '.' not in n and n not in seen and (p/(n+'.lean')).exists():seen.add(n);upstream.append(n);local_imports(n)
for m in modules:local_imports(m)
for old,new in [('SourceMarkedWildDifferentAudit1','SourceGammaOneGenusComparisonAudit1'),('SourceMarkedWildDifferentDependencyAudit1','SourceGammaOneGenusComparisonDependencyAudit1'),('SourceMarkedWildDifferentScratchOwnership1984','SourceGammaOneGenusComparisonScratchOwnership2014')]:
 t=(p/(old+'.lean')).read_text(encoding='utf-8');t=t[t.index('private def'):]
 t=t.replace('MarkedWildDifferent','GammaOneGenusComparison').replace('SOURCE MARKED WILD DIFFERENT','SOURCE GAMMAONE GENUS COMPARISON')
 if 'Dependency' in old:
  for n,ns in [('roots',roots),('localModules',modules+upstream),('required',edges)]:t=array(t,n,ns)
  a,b=t.index('  logInfo m!'),t.index('\n\n#eval')
  t=t[:a]+'  logInfo m!"SOURCE GAMMAONE GENUS COMPARISON DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the VALUE closure of the actual arithmetic Gamma1 genus/cusp upper bound. The native conorm section spaces give arithmetic-to-complex genus equality with no invariance premise. Original residue Hurwitz, small levels and reverse genus remain open; DUB17--20 OPEN."'+t[b:]
 elif 'Ownership' in old:t=array(t,'mods',modules)
 else:
  t=t[:t.index('\n#lint')]
  for n,ns in [('modules',modules),('theorems',theorems),('constructions',constructions)]:t=array(t,n,ns)
  t='\n'.join('#print axioms '+n for n in queries)+'\n\n'+t+'\n'+'\n'.join('#lint in '+m for m in modules)+'\n'
 output(new+'.lean',imports+t)
reuse=['SourceOriginalConormDivisorSpaces','SourceOriginalConormDimension','SourceOriginalArithmeticGenus','SourceGammaOnePrincipalDescent','SourceGammaOneComplexFieldIndependence','SourceCurveSeparatingGenusMaximum','SourceCurveFiniteCoordinateRegularGenus','SourceGammaOneRealPeriodDimensionUpper']
paths=[src/(n+'.lean') for n in reuse]
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain='DUB17 Theorem2.6 / DUB18 Cor8.2 -> literal higher symmetric-power continuation -> automorphy -> original all-weight association -> homogeneous Gamma1 realization -> original genus preservation -> reverse genus -> arithmetic-to-complex genus comparison and arithmetic genus upper bound.',shorterRoute='Reuse native actual Gamma1 conorm, unique extended places, span descent and coefficient independence. The existing Gamma0 conorm dimension argument adapts to these actual Gamma1 inputs, while the proved separating-coordinate genus maximum removes any need for new finiteness or index foundations. Native regular/cusp equivalence and real Manin dimension bound finish the arithmetic upper bound.',assumptionsToDischarge=['Actual conorm section membership and span descent are proved from native Gamma1 place and coefficient results.','The arithmetic and complex divisor-space dimensions agree without a finite-space or basis premise.','Positive-divisor stabilization proves equality of actual source H1 genera without an invariance premise.','The arithmetic genus/cusp upper bound follows from native real Manin and actual cusp dimensions.'],remaining='Original residue canonical degree and Hurwitz, small levels and reverse genus remain required. Original association and higher continuation remain open. Acceptance16/20; DUB17--20 OPEN.',boundary='Four focused modules compile. Exhaustive scratch audit, promotion and assembled verification pending.',reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in paths])
output('source-gammaone-genus-comparison-audit-route-2014.json',json.dumps(route,indent=2)+'\n')
replacements={'MarkedWildDifferent':'GammaOneGenusComparison','marked_wild_different':'gammaone_genus_comparison','marked-wild-different':'gammaone-genus-comparison','SOURCE MARKED WILD DIFFERENT':'SOURCE GAMMAONE GENUS COMPARISON','1984':'2014','20261029':'20261116','2026-10-29 America/Vancouver':'2026-11-16 America/Whitehorse'}
def tr(t):
 for a,b in replacements.items():t=t.replace(a,b)
 return t
t=tr((p/'build_marked_wild_different_canonical_1984.ps1').read_text(encoding='utf-8'))
t=re.sub(r'(?m)^\$names=@\(.*$', '$names=@('+','.join("'"+m+"'" for m in modules)+')',t)
output('build_gammaone_genus_comparison_canonical_2014.ps1',t)
output('audit_gammaone_genus_comparison_2014.ps1',tr((p/'audit_marked_wild_different_1984.ps1').read_text(encoding='utf-8')))
t=tr((p/'record_marked_wild_different_1984.py').read_text(encoding='utf-8'))
t=t.replace('(8, 10, 23)','(4, 6, 13)').replace('== 8','== 4').replace('linterScopes=8','linterScopes=4').replace('all 23 required','all 13 required').replace('requiredProofValueEdges=23','requiredProofValueEdges=13').replace('modules=8, queries=10','modules=4, queries=6').replace('proofEdges=23','proofEdges=13')
output('record_gammaone_genus_comparison_2014.py',t)
print(json.dumps(dict(modules=4,queries=6,theorems=6,constructions=0,proofEdges=13)))
