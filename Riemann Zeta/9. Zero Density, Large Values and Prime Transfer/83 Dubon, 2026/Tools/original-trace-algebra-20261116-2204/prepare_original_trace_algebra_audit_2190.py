from pathlib import Path
from datetime import datetime, timezone
import re,json,hashlib,sys
p=Path(__file__).parent
src=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
premap={}
for n in ['primitive-trace-audit-config-2165.json','original-local-trace-audit-config-2176.json']:
    c=json.loads((p/n).read_text(encoding='utf-8'))
    for row in c['files']:
        premap[row['version']]=row['module']
        premap[row['module']]=row['module']
seen=set();versions=[];mapping={**premap}
def visit(v):
    if '.' in v or v in premap or v in seen:return
    seen.add(v)
    f=p/(v+'.lean');assert f.exists(),v
    for d in re.findall(r'(?m)^import (\S+)',f.read_text(encoding='utf-8')):visit(d)
    versions.append(v);mapping[v]=re.sub(r'\d+[a-z]$','',v)
assert len(sys.argv)==2
visit(sys.argv[1])
assert len(versions)==9,(len(versions),versions)
def output(n,t):
    f=p/n;assert not f.exists(),f;f.write_text(t,encoding='utf-8')
queries=[];theorems=[];constructions=[];rows=[]
for v in versions:
    f=p/(v+'.lean');t=f.read_text(encoding='utf-8');m=mapping[v]
    assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,v
    assert not(src/(m+'.lean')).exists(),m
    c=re.sub(r'(?m)^import (\S+)$',lambda x:'import '+mapping.get(x[1],x[1]),t)
    assert all(x.startswith(('Dubon2026.','Mathlib.')) or x in mapping.values() for x in re.findall(r'(?m)^import (\S+)',c))
    output(m+'.lean',c)
    assert re.sub(r'(?m)^import .*\n','',t)==re.sub(r'(?m)^import .*\n','',c)
    ns=re.search(r'(?m)^namespace (\S+)',t)[1]+'.'
    qs=re.findall(r'(?m)^(?:noncomputable )?(theorem|lemma|def|abbrev|instance)\s+(\S+)',t)
    queries += [ns+n for k,n in qs]
    theorems += [ns+n for k,n in qs if k in ['theorem','lemma']]
    constructions += [ns+n for k,n in qs if k not in ['theorem','lemma']]
    rows.append(dict(version=v,module=m,path=str(p/(m+'.lean')),sourceSha256=sha(f),canonicalSha256=sha(p/(m+'.lean')),mathematicalBodyIdentical=True))
modules=[mapping[v] for v in versions]
ns='Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction.'
roots=[ns+'exists_gammaOne_original_local_trace_algebra']
separate=['Dubon2026.sourceTraceRadical_mem']
edges=[n for n in theorems if n not in separate]+[
    ns+'exists_gammaOne_original_constructed_local_trace',
    ns+'exists_gammaOne_compatible_original_adic_trace',
    'MonoidAlgebra.induction_on','Submodule.liftQ',
    'Ideal.Quotient.eq_zero_iff_mem','MonoidHom.toHomUnits']
cfg=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),modules=modules,queries=queries,theorems=theorems,constructions=constructions,roots=roots,proofEdges=edges,separatelyAxiomChecked=separate+constructions,files=rows,routeAssessment='original-trace-algebra-route-2189.json',productionMutation=False,scope='Original constructed characteristic-zero trace algebra with a genuine unit action, nondegenerate trace pairing and scalar idempotent corners. Rank-two matrices, continuity, exceptional primes and full source gates remain OPEN.')
output('original-trace-algebra-audit-config-2190.json',json.dumps(cfg,indent=2)+'\n')
imports='\n'.join('import '+m for m in modules)+'\nimport Mathlib.Tactic\n\nopen Lean\n\n'
def array(t,n,x):
    t,k=re.subn(r'(?m)^  let '+n+r' : Array Name := #\[.*$', '  let '+n+' : Array Name := #['+', '.join('`'+v for v in x)+']',t);assert k==1;return t
for old,new in [('SourceGammaOnePrimitiveArithmeticAudit1','SourceOriginalTraceAlgebraAudit1'),('SourceGammaOnePrimitiveArithmeticDependencyAudit1','SourceOriginalTraceAlgebraDependencyAudit1'),('SourceGammaOnePrimitiveArithmeticScratchOwnership2143','SourceOriginalTraceAlgebraScratchOwnership2190')]:
    t=(p/(old+'.lean')).read_text(encoding='utf-8');t=t[t.index('private def'):]
    t=t.replace('GammaOnePrimitiveArithmetic','OriginalTraceAlgebra').replace('SOURCE GAMMAONE PRIMITIVE ARITHMETIC','SOURCE ORIGINAL TRACE ALGEBRA')
    if 'Dependency' in old:
        for n,x in [('roots',roots),('localModules',modules),('required',edges)]:t=array(t,n,x)
        a,b=t.index('  logInfo m!'),t.index('\n\n#eval')
        t=t[:a]+'  logInfo m!"SOURCE ORIGINAL TRACE ALGEBRA DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the VALUE closure of the original trace-algebra consumer. Original constructed local traces, native group-algebra induction, actual trace radical and quotient lift are consumed. Rank-two matrix realization and DUB-17--20 remain OPEN."'+t[b:]
    elif 'Ownership' in old:t=array(t,'mods',modules)
    else:
        t=t[:t.index('\n#lint')]
        for n,x in [('modules',modules),('theorems',theorems),('constructions',constructions)]:t=array(t,n,x)
        a,b=t.index('  logInfo m!'),t.index('\n\n#eval')
        t=t[:a]+'  logInfo m!"SOURCE ORIGINAL TRACE ALGEBRA AUDIT PASS: {count} theorems including private/generated declarations. Original trace algebra with nondegenerate pairing and scalar corners proved; actual rank-two matrices and source gates remain OPEN."'+t[b:]
        t='\n'.join('#print axioms '+n for n in queries)+'\n\n'+t+'\n'+'\n'.join('#lint in '+m for m in modules)+'\n'
    output(new+'.lean',imports+t)
runner=(p/'build_primitive_column_audit_2118.ps1').read_text(encoding='utf-8')
runner=runner.replace('primitive-column-audit-config-2118.json','original-trace-algebra-audit-config-2190.json').replace('$taskName-2118','$taskName-2190').replace('SourceGammaOnePrimitiveColumnAudit1','SourceOriginalTraceAlgebraAudit1').replace('SourceGammaOnePrimitiveColumnDependencyAudit1','SourceOriginalTraceAlgebraDependencyAudit1').replace('SourceGammaOnePrimitiveColumnScratchOwnership2118','SourceOriginalTraceAlgebraScratchOwnership2190')
output('build_original_trace_algebra_audit_2190.ps1',runner)
print(json.dumps(dict(modules=len(modules),queries=len(queries),theorems=len(theorems),constructions=len(constructions),proofEdges=len(edges),productionMutation=False)))
