from pathlib import Path
from datetime import datetime, timezone
import ast, json, re, hashlib

p = Path(__file__).parent
r = Path(r'E:\Lean\Riemann Zeta')
paper = r / '9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026'
prod = paper / 'Extension/Dubon2026'
mods = ['SourceGammaOneDiamondConjugation', 'SourceGammaOneDiamondH1',
        'SourceGammaOneDiamondLabels', 'SourceGammaOneUnitDiamondAction']
attempts = ['1185a', '1186a', '1187a', '1188a']
ev = {m: m+a for m,a in zip(mods, attempts)}
ths, defs = [], []
for m in mods:
    assert (p/(ev[m]+'.exit')).read_text().strip() == '0'
    assert (p/(ev[m]+'.log')).stat().st_size == 0
    code = re.sub(r'--[^\n]*', '', re.sub(r'/\-.*?\-/', '', (p/(m+'.lean')).read_text(encoding='utf-8'), flags=re.S))
    ths += ['Dubon2026.'+x for x in re.findall(r'^theorem\s+(\w+)', code, re.M)]
    defs += ['Dubon2026.'+x for x in re.findall(r'^def\s+(\w+)', code, re.M)]
assert (len(ths),len(defs)) == (12,5)
edges = ths + defs + ['CongruenceSubgroup.Gamma1_mem', 'CongruenceSubgroup.Gamma1_to_Gamma0_mem',
    'CongruenceSubgroup.Gamma1_in_Gamma0', 'Matrix.trace_mul_comm',
    'Dubon2026.SL2Reduction.SL2_reduction_surjective',
    'groupCohomology.H1π_comp_map_apply', 'groupCohomology.H1IsoOfIsTrivial_H1π_apply_apply']
cfg = dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,roots=ths+defs,
    proofEdges=edges,localModules=mods,separatelyAxiomChecked=[],compileEvidence=ev)
def write(n,s):
    f=p/n; assert not f.exists(),f; f.write_text(s,encoding='utf-8')
stem='source-gamma-one-diamond-1'
write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
old='SourceGammaOneParabolicDescent';new='SourceGammaOneDiamond'
for a,b in [('Audit1','Audit1'),('DependencyAudit1','DependencyAudit1'),('ScratchOwnership1181','ScratchOwnership1189')]:
    s=(p/(old+a+'.lean')).read_text(encoding='utf-8')
    s='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n'+s[s.index('\nopen Lean'):]
    if a=='Audit1':
        s=re.sub(r'(#print axioms [^\n]+\n)+',''.join('#print axioms '+x+'\n' for x in cfg['queries']),s,count=1)
        for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:
            s=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),s)
        s=re.sub(r'#lint in [^\n]+\n','',s).rstrip()+'\n\n'+''.join('#lint in '+m+'\n' for m in mods)
    elif a=='DependencyAudit1':
        for k,v in [('roots',cfg['roots']),('localModules',mods),('required',edges)]:
            s=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),s)
        start=s.index(' occur in the ');end=s.index('; DUB17--20 OPEN.',start)
        s=s[:start]+' occur in the literal native Gamma1 diamond conjugation, lift independence, unit action and original parabolic H1 preservation. Analytic-period and arithmetic diamond comparisons, homogeneous coefficient conventions and the separate transfer lifting remain unresolved'+s[end:]
    else:
        s=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),s)
    s=s.replace('GAMMA ONE PARABOLIC DESCENT','GAMMA ONE DIAMOND').replace('Gamma One Parabolic Descent','Gamma One Diamond')
    write(new+b+'.lean',s)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
reuse=[p/'diamond-route-1185.md',
    r/'.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean',
    r/'.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Trace.lean',
    prod/'SL2Reduction.lean',prod/'SourceGammaOneConstantHecke.lean',prod/'SourceGammaOneBinaryParabolicH1.lean',
    paper/'Tools/reuse-refresh-20261028-1159/reuse-head-refresh-1159b/TauCetiProject__TauCeti__TauCeti__NumberTheory__ModularForms__ModularSymbols__Hecke__Diamond.lean.txt',
    p/'association-reuse-1184/assessment.md',p/'association-reuse-1184/manifest.json']
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),
    chain='DUB17 Theorem 2.6 / DUB18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight association -> arithmetic realization of original finite Gamma1 characters -> diamond comparison on actual native parabolic H1.',
    reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in reuse],
    shorterRoute='Native Gamma0 character kernel, proved integral SL2 reduction, native cohomology pullback and its existing trivial-coefficient character isomorphism; no second modular-symbol or cohomology model.',
    assumptionsToDischarge=['Literal Gamma0 conjugation preserves actual Gamma1 and trace.',
        'The native H1 map has the exact conjugated-character formula with an explicit coefficient endomorphism.',
        'Its action on constant-coefficient H1 is independent of the lift, every unit label has a lift, and the unit-labelled operators form a monoid action.',
        'The same actual original homogeneous-valued parabolic H1 is stable under these maps.'],
    remaining='Analytic-period and arithmetic Picard/Tate diamond compatibility and identification of the original homogeneous coefficient convention remain. The separately stated parabolic transfer lifting, exceptional primes, Frobenius/inertia and original all-weight association are still open. No finite character or characteristic-zero lift is inferred.16/20; DUB17--20 OPEN.',
    externalBuild=False,externalImport=False,rootPinsChanged=False)
write('source-gamma-one-diamond-audit-route-1189.json',json.dumps(route,indent=2)+'\n')
s=(p/'record_gamma_one_parabolic_descent_1181.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-parabolic-descent-audit-route-1181','source-gamma-one-diamond-audit-route-1189'),
    ('source-gamma-one-parabolic-descent-1',stem),(old,new),('ScratchOwnership1181','ScratchOwnership1189'),
    ('GAMMA ONE PARABOLIC DESCENT','GAMMA ONE DIAMOND')]:s=s.replace(a,b)
s=s.replace('(5, 12, 23)',str((4,17,len(edges)))).replace('== 5','== 4').replace('linterScopes=5','linterScopes=4')
s=s.replace('all 23 required',f'all {len(edges)} required').replace('requiredProofValueEdges=23',f'requiredProofValueEdges={len(edges)}').replace('proofEdges=23',f'proofEdges={len(edges)}').replace('modules=5, queries=12','modules=4, queries=17')
ast.parse(s);write('record_gamma_one_diamond_1189.py',s)
s=(p/'audit_gamma_one_parabolic_descent_1181.ps1').read_text(encoding='utf-8')
for a,b in [(old,new),('ScratchOwnership1181','ScratchOwnership1189'),('record_gamma_one_parabolic_descent_1181','record_gamma_one_diamond_1189')]:s=s.replace(a,b)
write('audit_gamma_one_diamond_1189.ps1',s)
print(json.dumps(dict(modules=4,queries=17,edges=len(edges))))
