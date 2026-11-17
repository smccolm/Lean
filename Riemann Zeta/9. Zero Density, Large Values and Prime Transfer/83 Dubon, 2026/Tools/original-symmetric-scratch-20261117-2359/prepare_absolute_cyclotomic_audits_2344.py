from pathlib import Path
import hashlib
import json
import re

p = Path(__file__).parent
c = json.loads((p / 'source-cyclotomic-symmetric-audit-config-2339.json').read_text())
pairs = [
    ('SourceFiniteLinearAbsoluteGalois2341a', 'SourceFiniteLinearAbsoluteGalois'),
    ('SourceGammaOneAbsoluteCyclotomicResidual2343a', 'SourceGammaOneAbsoluteCyclotomicResidual'),
]
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()

def write(name, text):
    f = p / name
    assert not f.exists(), f
    f.write_text(text, encoding='utf-8')

for old, new in pairs:
    f = p / (old + '.lean')
    assert f.with_suffix('.exit').read_text().strip() == '0'
    assert f.with_suffix('.log').stat().st_size == 0
    t = f.read_text(encoding='utf-8')
    for a, b in pairs:
        t = re.sub(r'(?m)^import ' + a + '$', 'import ' + b, t)
    write(new + '.lean', t)
    target = p / (new + '.lean')
    c['files'].append(dict(source=str(f), sourceSha256=sha(f), module=new,
                          path=str(target), canonicalSha256=sha(target)))
    c['modules'].append(new)
    ns = re.search(r'(?m)^namespace (\S+)', t)[1]
    qs = [ns + '.' + n for n in re.findall(r'(?m)^theorem (\S+)', t)]
    c['queries'] += qs
    c['theorems'] += qs

c['roots'] = [c['queries'][-1]]
c['proofEdges'] = list(dict.fromkeys(c['proofEdges'] + c['queries'] + [
    'Dubon2026.sourceAbsoluteArithmeticRestriction_surjective',
]))
c['scope'] = ('Nine modules: absolute symmetric irreducibility on the finite large-image '
              'branch, including the actual arithmetic and absolute cyclotomic kernels.')
arr = lambda xs: '#[' + ', '.join('`' + n for n in xs) + ']'
prior = json.loads((p / 'source-projective-finite-audit-config-2321.json').read_text())

for old, new in [
    ('SourceCyclotomicSymmetricAudit1', 'SourceAbsoluteCyclotomicSymmetricAudit1'),
    ('SourceCyclotomicSymmetricDependencyAudit1', 'SourceAbsoluteCyclotomicSymmetricDependencyAudit1'),
    ('SourceCyclotomicSymmetricDeclarations2339', 'SourceAbsoluteCyclotomicSymmetricDeclarations2344'),
]:
    t = (p / (old + '.lean')).read_text(encoding='utf-8')
    t = t.replace('import SourceGammaOneCyclotomicSymmetricResidual', 'import ' + c['modules'][-1])
    if old == 'SourceCyclotomicSymmetricAudit1':
        t = re.sub(r'(?m)^#print axioms .*\n', '', t)
        t = t.replace('open Lean\n', 'open Lean\n\n' + '\n'.join(
            '#print axioms ' + q for q in c['queries']) + '\n', 1)
        t = re.sub(r'let modules : Array Name := #\[.*\]',
                   'let modules : Array Name := ' + arr(c['modules']), t)
        t = re.sub(r'(?m)^#lint in .*\n', '', t)
        t += '\n'.join('#lint in ' + m for m in c['modules']) + '\n'
        t = t.replace('SOURCE CYCLOTOMIC SYMMETRIC AXIOM AUDIT PASS',
                      'SOURCE ABSOLUTE CYCLOTOMIC SYMMETRIC AXIOM AUDIT PASS')
        t = t.replace('the original arithmetic cyclotomic kernel.',
                      'the original arithmetic and absolute Galois cyclotomic kernels.')
    elif 'Dependency' in old:
        for label, values in [('roots', c['roots']),
                              ('localModules', prior['modules'] + c['modules']),
                              ('required', c['proofEdges'])]:
            t = re.sub('let ' + label + r' : Array Name := #\[.*\]',
                       'let ' + label + ' : Array Name := ' + arr(values), t)
        t = t.replace('SOURCE CYCLOTOMIC SYMMETRIC VALUE AUDIT PASS',
                      'SOURCE ABSOLUTE CYCLOTOMIC SYMMETRIC VALUE AUDIT PASS')
    else:
        t = re.sub(r'let mods : Array Name := #\[.*\]',
                   'let mods : Array Name := ' + arr(c['modules']), t)
    write(new + '.lean', t)

write('source-absolute-cyclotomic-symmetric-audit-config-2344.json', json.dumps(c, indent=2) + '\n')
print(json.dumps(dict(modules=len(c['modules']), queries=len(c['queries']),
                      requiredProofEdges=len(c['proofEdges']))))
