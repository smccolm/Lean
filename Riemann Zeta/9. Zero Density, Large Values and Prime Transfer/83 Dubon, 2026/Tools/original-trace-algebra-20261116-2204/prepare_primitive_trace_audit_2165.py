from pathlib import Path
from datetime import datetime, timezone
import re,json,hashlib,sys
p=Path(__file__).parent
src=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
premap={}
for n in ['primitive-column-audit-config-2118b.json','primitive-arithmetic-audit-config-2143.json']:
    c=json.loads((p/n).read_text(encoding='utf-8'))
    for row in c['files']:
        premap[row['version']]='Dubon2026.'+row['module']
        premap[row['module']]='Dubon2026.'+row['module']
seen=set();versions=[];mapping={**premap}
def visit(v):
    if '.' in v or v in premap or v in seen:return
    seen.add(v)
    f=p/(v+'.lean');assert f.exists(),v
    for d in re.findall(r'(?m)^import (\S+)',f.read_text(encoding='utf-8')):visit(d)
    versions.append(v);mapping[v]=re.sub(r'\d+[a-z]$','',v)
assert len(sys.argv)==2
visit(sys.argv[1])
assert len(versions)==19,(len(versions),versions)
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
ns='Dubon2026.SourceFunctionField.GammaOne.'
roots=[ns+'CoefficientReduction.exists_gammaOne_compatible_original_adic_trace']
separate=[ns+'binaryPrimitiveJointTrace_exists_local_frobenius']
edges=[n for n in theorems if n not in separate]+[
    ns+'CoefficientReduction.exists_gammaOne_primitive_joint_original_character',
    ns+'binaryPrimitiveJoint_character_hecke',ns+'binaryPrimitiveJoint_character_diamond',
    ns+'binaryPrimitiveJointHeckeDiamondWord_range_isMulCommutative',
    ns+'binaryPrimitiveJointGaloisRep_word',ns+'CoefficientReduction.gammaOne_local_degree_and_genus_eq',
    'Dubon2026.algebraicLocal_frobenius_class_of_original_residue',
    'Dubon2026.continuous_rational_galois_exists_frobenius_prime',
    'Dubon2026.sourceRationalLocalValuation_frobenius',
    'Dubon2026.rationalPrimeOriginalNorm_exists_frobenius',
    'krullTopology_mem_nhds_one_iff_of_normal','Ideal.Quotient.factor_mk']
cfg=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),modules=modules,queries=queries,theorems=theorems,constructions=constructions,roots=roots,proofEdges=edges,separatelyAxiomChecked=separate+constructions,files=rows,routeAssessment='primitive-joint-trace-route-2161.json',productionMutation=False,scope='Compatible original all-precision continuous traces with exact Fourier and determinant norm-Frobenius values; characteristic-zero reconstruction, rank-two realization, exceptional primes and full source gates remain OPEN.')
output('primitive-trace-audit-config-2165.json',json.dumps(cfg,indent=2)+'\n')
imports='\n'.join('import '+m for m in modules)+'\nimport Mathlib.Tactic\n\nopen Lean\n\n'
def array(t,n,x):
    t,k=re.subn(r'(?m)^  let '+n+r' : Array Name := #\[.*$', '  let '+n+' : Array Name := #['+', '.join('`'+v for v in x)+']',t);assert k==1;return t
for old,new in [('SourceGammaOnePrimitiveArithmeticAudit1','SourceGammaOnePrimitiveTraceAudit1'),('SourceGammaOnePrimitiveArithmeticDependencyAudit1','SourceGammaOnePrimitiveTraceDependencyAudit1'),('SourceGammaOnePrimitiveArithmeticScratchOwnership2143','SourceGammaOnePrimitiveTraceScratchOwnership2165')]:
    t=(p/(old+'.lean')).read_text(encoding='utf-8');t=t[t.index('private def'):]
    t=t.replace('GammaOnePrimitiveArithmetic','GammaOnePrimitiveTrace').replace('SOURCE GAMMAONE PRIMITIVE ARITHMETIC','SOURCE GAMMAONE PRIMITIVE TRACE')
    if 'Dependency' in old:
        for n,x in [('roots',roots),('localModules',modules),('required',edges)]:t=array(t,n,x)
        a,b=t.index('  logInfo m!'),t.index('\n\n#eval')
        t=t[:a]+'  logInfo m!"SOURCE GAMMAONE PRIMITIVE TRACE DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the VALUE closure of the original compatible all-precision trace consumer. Exact local Frobenius, native Chebotarev and Krull neighborhoods, original Fourier character, Hecke centrality and quotient transitions are consumed. Characteristic-zero reconstruction, rank-two realization and DUB-17--20 remain OPEN."'+t[b:]
    elif 'Ownership' in old:t=array(t,'mods',modules)
    else:
        t=t[:t.index('\n#lint')]
        for n,x in [('modules',modules),('theorems',theorems),('constructions',constructions)]:t=array(t,n,x)
        a,b=t.index('  logInfo m!'),t.index('\n\n#eval')
        t=t[:a]+'  logInfo m!"SOURCE GAMMAONE PRIMITIVE TRACE AUDIT PASS: {count} theorems including private/generated declarations. Compatible original adic traces proved; characteristic-zero realization and source gates remain OPEN."'+t[b:]
        t='\n'.join('#print axioms '+n for n in queries)+'\n\n'+t+'\n'+'\n'.join('#lint in '+m for m in modules)+'\n'
    output(new+'.lean',imports+t)
runner=(p/'build_primitive_column_audit_2118.ps1').read_text(encoding='utf-8')
runner=runner.replace('primitive-column-audit-config-2118.json','primitive-trace-audit-config-2165.json').replace('$taskName-2118','$taskName-2165').replace('SourceGammaOnePrimitiveColumnAudit1','SourceGammaOnePrimitiveTraceAudit1').replace('SourceGammaOnePrimitiveColumnDependencyAudit1','SourceGammaOnePrimitiveTraceDependencyAudit1').replace('SourceGammaOnePrimitiveColumnScratchOwnership2118','SourceGammaOnePrimitiveTraceScratchOwnership2165')
output('build_primitive_trace_audit_2165.ps1',runner)
print(json.dumps(dict(modules=len(modules),queries=len(queries),theorems=len(theorems),constructions=len(constructions),proofEdges=len(edges),productionMutation=False)))
