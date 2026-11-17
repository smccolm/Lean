from pathlib import Path
from datetime import datetime, timezone
import re, json, hashlib, sys

p = Path(__file__).parent
src = Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
core = json.loads((p/'primitive-arithmetic-core-2140.json').read_text(encoding='utf-8'))
column = json.loads((p/'primitive-column-audit-config-2118b.json').read_text(encoding='utf-8'))
amap = {r['version']: r['module'] for r in column['files']}
mapping = amap | {r['version']: r['module'] for r in core['files']}
versions = [r['version'] for r in core['files']]
seen = set(versions) | set(amap)

def visit(v):
    if v in seen: return
    seen.add(v)
    for d in re.findall(r'(?m)^import (\S+)', (p/(v+'.lean')).read_text(encoding='utf-8')):
        if '.' not in d: visit(d)
    versions.append(v)
    mapping[v] = re.sub(r'\d+[a-z]$', '', v)

assert len(sys.argv) == 2, 'Supply the focused-PASS arithmetic-system version.'
visit(sys.argv[1])
visit('SourceGammaOnePrimitiveJointCommutativity2139a')
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
queries, theorems, constructions, rows = [], [], [], []

def output(n, t):
    f = p/n
    assert not f.exists(), f
    f.write_text(t, encoding='utf-8')

for v in versions:
    f = p/(v+'.lean'); t = f.read_text(encoding='utf-8'); m = mapping[v]
    assert f.with_suffix('.exit').read_text().strip() == '0', v
    assert f.with_suffix('.log').stat().st_size == 0, v
    assert not (src/(m+'.lean')).exists(), m
    c = re.sub(r'(?m)^import (\S+)$', lambda x: 'import '+mapping.get(x[1], x[1]), t)
    cf = p/(m+'.lean')
    if cf.exists(): assert cf.read_text(encoding='utf-8') == c, m
    else: output(cf.name, c)
    assert re.sub(r'(?m)^import .*\n', '', t) == re.sub(r'(?m)^import .*\n', '', c)
    ns = re.search(r'(?m)^namespace (\S+)', t)[1]+'.'
    names = re.findall(r'(?m)^(?:noncomputable )?(theorem|lemma|def|abbrev|instance)\s+(\S+)', t)
    queries += [ns+n for k,n in names]
    theorems += [ns+n for k,n in names if k in ['theorem','lemma']]
    constructions += [ns+n for k,n in names if k not in ['theorem','lemma']]
    rows.append(dict(version=v, module=m, sourceSha256=sha(f), canonicalSha256=sha(cf), mathematicalBodyIdentical=True))

modules = [mapping[v] for v in versions]
ns = 'Dubon2026.SourceFunctionField.GammaOne.'
roots = [ns+'CoefficientReduction.exists_gammaOne_primitive_joint_arithmetic_system', ns+'binaryPrimitiveJointHeckeDiamondWord_range_isMulCommutative']
separate = [ns+'binaryPrimitiveBoundaryGaloisRep_arithmetic_descent']
edges = [n for n in theorems if n not in separate] + [
    ns+'binaryPrimitiveColumnBoundary_eq_zero_iff', ns+'binaryPrimitiveColumnBoundary_hecke',
    ns+'binaryPrimitiveColumnBoundary_diamond', ns+'CoefficientReduction.gammaOne_local_degree_and_genus_eq',
    'Dubon2026.sourceGammaOneHeckeDiamondCoefficient_square',
    'Dubon2026.sourcePrimitiveH1AdicQuotientCharacter_zero_of_operator_square',
    'Dubon2026.sourceRationalLocalValuation_exists_frobenius',
    'Dubon2026.sourceGammaOneDiamondLabel_lift']
cfg = dict(recordedUTC=datetime.now(timezone.utc).isoformat(), modules=modules, queries=queries,
    theorems=theorems, constructions=constructions, roots=roots, proofEdges=edges,
    separatelyAxiomChecked=separate+constructions, files=rows,
    priorCanonicalCore=core['modules'], prerequisiteColumnModules=column['modules'],
    productionMutation=False, scope='Actual finite primitive joint arithmetic system and commutative exact character image. Compatible trace/character specialization, rank-two characteristic-zero realization and DUB-17--20 remain open.')
output('primitive-arithmetic-audit-config-2143.json', json.dumps(cfg, indent=2)+'\n')
imports = '\n'.join('import '+m for m in modules)+'\nimport Mathlib.Tactic\n\nopen Lean\n\n'

def array(t, n, names):
    t, count = re.subn(r'(?m)^  let '+n+r' : Array Name := #\[.*$',
        '  let '+n+' : Array Name := #['+', '.join('`'+x for x in names)+']', t)
    assert count == 1
    return t

for old,new in [('SourceGammaOnePrimitiveColumnAudit1','SourceGammaOnePrimitiveArithmeticAudit1'),
    ('SourceGammaOnePrimitiveColumnDependencyAudit2','SourceGammaOnePrimitiveArithmeticDependencyAudit1'),
    ('SourceGammaOnePrimitiveColumnScratchOwnership2118','SourceGammaOnePrimitiveArithmeticScratchOwnership2143')]:
    t=(p/(old+'.lean')).read_text(encoding='utf-8'); t=t[t.index('private def'):]
    t=t.replace('GammaOnePrimitiveColumn','GammaOnePrimitiveArithmetic').replace('SOURCE GAMMAONE PRIMITIVE COLUMN','SOURCE GAMMAONE PRIMITIVE ARITHMETIC').replace('Primitive column','Primitive arithmetic')
    if 'Dependency' in old:
        for n,x in [('roots',roots),('localModules',modules+column['modules']),('required',edges)]: t=array(t,n,x)
        a,b=t.index('  logInfo m!'),t.index('\n\n#eval')
        t=t[:a]+'  logInfo m!"SOURCE GAMMAONE PRIMITIVE ARITHMETIC DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the VALUE closure of the original arithmetic-system consumer and exact joint range commutativity. Native primitive boundary, original character, geometry, Frobenius, inertia and arithmetic descent are consumed. Compatible trace specialization, characteristic-zero rank two and source gates remain OPEN."'+t[b:]
    elif 'Ownership' in old: t=array(t,'mods',modules)
    else:
        t=t[:t.index('\n#lint')]
        for n,x in [('modules',modules),('theorems',theorems),('constructions',constructions)]: t=array(t,n,x)
        t='\n'.join('#print axioms '+n for n in queries)+'\n\n'+t+'\n'+'\n'.join('#lint in '+m for m in modules)+'\n'
    output(new+'.lean',imports+t)

runner=(p/'build_primitive_column_audit_2118.ps1').read_text(encoding='utf-8')
runner=runner.replace('primitive-column-audit-config-2118.json','primitive-arithmetic-audit-config-2143.json').replace('$taskName-2118','$taskName-2143')
runner=runner.replace('foreach($taskName in $taskConfig.modules){','foreach($taskName in $taskConfig.modules){\n  if($taskConfig.priorCanonicalCore -contains $taskName){\n    $prior=Join-Path $taskScratch "$taskName-2140"\n    if(!(Test-Path -LiteralPath "$prior.exit") -or (Get-Content -LiteralPath "$prior.exit" -Raw).Trim() -ne "0" -or (Get-Item -LiteralPath "$prior.log").Length -ne 0){throw "Canonical core not verified: $taskName"}\n    continue\n  }')
runner=runner.replace('SourceGammaOnePrimitiveColumnAudit1','SourceGammaOnePrimitiveArithmeticAudit1').replace('SourceGammaOnePrimitiveColumnDependencyAudit1','SourceGammaOnePrimitiveArithmeticDependencyAudit1').replace('SourceGammaOnePrimitiveColumnScratchOwnership2118','SourceGammaOnePrimitiveArithmeticScratchOwnership2143')
output('build_primitive_arithmetic_audit_2143.ps1', runner)
print(json.dumps(dict(modules=len(modules), publicQueries=len(queries), proofValueEdges=len(edges), productionMutation=False)))
