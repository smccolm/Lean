from pathlib import Path
from datetime import datetime, timezone
import ast, json, re, hashlib

p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
mods=['SourceGammaOneDiamondCuspPrimitive','SourceGammaOneDiamondPeriodH1',
      'SourceGammaOneDiamondPeriodLattice','SourceGammaOneDiamondFiniteH1']
attempts=['1190b','1191a','1192c','1193b']
ev={m:m+a for m,a in zip(mods,attempts)}
ths=[];defs=[]
for m in mods:
    assert (p/(ev[m]+'.exit')).read_text().strip()=='0'
    assert (p/(ev[m]+'.log')).stat().st_size==0
    code=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',(p/(m+'.lean')).read_text(encoding='utf-8'),flags=re.S))
    ns='Dubon2026.SourceFunctionField.GammaOne.'
    ths += [ns+x for x in re.findall(r'^theorem\s+(\w+)',code,re.M)]
    defs += [ns+x for x in re.findall(r'^def\s+(\w+)',code,re.M)]
assert (len(ths),len(defs))==(13,4),(ths,defs)
edges=ths+defs+['Dubon2026.'+x for x in ['sourceHasDerivAt_comp_smul',
    'sourceUpperHalfPlane_primitive_difference','sourceWeightTwoPrimitive_hasDerivAt',
    'sourceGammaOneDiamondConjugation','sourceGammaOneDiamondH1_hom_apply',
    'sourceGammaOneUnitDiamondH1_eq','sourceWeightTwoDualPeriod_mem']]+[
    'Dubon2026.SourceFunctionField.GammaOne.'+x for x in ['primitive_one_period',
    'latticePeriodHom_surjective','realPeriodH1_hom_apply','binaryLatticeH1Equiv_hom_apply']]
prior=json.loads((p/'source-gamma-one-diamond-1-audit-config.json').read_text())
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,roots=ths+defs,
    proofEdges=edges,localModules=mods+prior['localModules'],separatelyAxiomChecked=[],compileEvidence=ev)
def write(n,s):
    f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
stem='source-gamma-one-diamond-period-1'
write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
old='SourceGammaOneDiamond';new='SourceGammaOneDiamondPeriod'
for a,b in [('Audit1','Audit1'),('DependencyAudit1','DependencyAudit1'),('ScratchOwnership1189','ScratchOwnership1195')]:
    s=(p/(old+a+'.lean')).read_text(encoding='utf-8')
    s='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n'+s[s.index('\nopen Lean'):]
    if a=='Audit1':
        s=re.sub(r'(#print axioms [^\n]+\n)+',''.join('#print axioms '+x+'\n' for x in cfg['queries']),s,count=1)
        for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:
            s=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),s)
        s=re.sub(r'#lint in [^\n]+\n','',s).rstrip()+'\n\n'+''.join('#lint in '+m+'\n' for m in mods)
    elif a=='DependencyAudit1':
        for k,v in [('roots',cfg['roots']),('localModules',cfg['localModules']),('required',edges)]:
            s=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),s)
        start=s.index(' occur in the ');end=s.index('; DUB17--20 OPEN.',start)
        s=s[:start]+' occur in the actual slash cusp diamond, original endpoint periods, stable original integer lattice and literal homogeneous-valued finite H1 transpose. Arithmetic Picard diamond and the original coefficient convention, transfer lifting and exceptional primes remain unresolved'+s[end:]
    else:
        s=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),s)
    s=s.replace('GAMMA ONE DIAMOND','GAMMA ONE DIAMOND PERIOD').replace('Gamma One Diamond','Gamma One Diamond Period')
    write(new+b+'.lean',s)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
reuse=[p/'source-gamma-one-diamond-1-scratch-receipt.json',p/'diamond-route-1185.md']
reuse += [r/'Extension/Dubon2026'/(m+'.lean') for m in ['SourceGammaOneCuspHeckeTrace',
    'SourceGammaOneHeckePrimitiveDerivative','SourceGammaOneHeckePrimitiveTrace',
    'SourceGammaOnePeriodNormalization','SourceGammaOneScalarHeckePeriods',
    'SourceGammaOneCuspHeckeLinear','SourceGammaOnePeriodHeckeLattice',
    'SourceGammaOneFiniteParabolicCharacters','SourceGammaOneBinaryParabolicH1']]
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),
    chain='DUB17 Theorem 2.6 / DUB18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight association -> arithmetic realization of original finite Gamma1 characters -> diamond comparison -> literal slash, original integral periods and homogeneous-valued native H1 transpose.',
    reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in reuse],
    shorterRoute='Existing native cusp translation and subgroup restriction, primitive chain rule and endpoint uniqueness, actual period surjectivity and existing binary lattice/H1 equivalence. Lattice-period surjectivity directly proves lattice stability; no new span induction or lattice basis is needed.',
    assumptionsToDischarge=['The literal slash diamond is an actual Gamma1 cusp form.',
        'Its exact original endpoint and group-period identities and real H1 intertwining are proved.',
        'The dual slash operator preserves the original integer lattice without a stability premise.',
        'The original homogeneous-valued lattice/H1 equivalence intertwines its transpose with the native diamond and an explicit coefficient endomorphism.'],
    remaining='The independently defined arithmetic Picard diamond and the identification of the required original homogeneous coefficient action remain. The separate parabolic transfer lifting and exceptional primes, Frobenius/inertia, original all-weight association and higher continuation remain.16/20; DUB17--20 OPEN.',
    preservedFailures='1190a conjugation simp error/warning; 1192a explicit dual-period and notation errors; 1192b kernel deterministic timeout in span proof, resolved by existing lattice-period surjectivity with unchanged limits; 1193a prerequisite not yet compiled. Every failed source and log is retained.',
    externalBuild=False,externalImport=False,rootPinsChanged=False)
write('source-gamma-one-diamond-period-audit-route-1195.json',json.dumps(route,indent=2)+'\n')
s=(p/'record_gamma_one_diamond_1189.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-diamond-audit-route-1189','source-gamma-one-diamond-period-audit-route-1195'),
    ('source-gamma-one-diamond-1',stem),(old,new),('ScratchOwnership1189','ScratchOwnership1195'),
    ('GAMMA ONE DIAMOND','GAMMA ONE DIAMOND PERIOD')]:s=s.replace(a,b)
s=s.replace('(4, 17, 24)',str((4,17,len(edges)))).replace('all 24 required',f'all {len(edges)} required')
s=s.replace('requiredProofValueEdges=24',f'requiredProofValueEdges={len(edges)}').replace('proofEdges=24',f'proofEdges={len(edges)}')
ast.parse(s);write('record_gamma_one_diamond_period_1195.py',s)
s=(p/'audit_gamma_one_diamond_1189.ps1').read_text(encoding='utf-8')
for a,b in [(old,new),('ScratchOwnership1189','ScratchOwnership1195'),('record_gamma_one_diamond_1189','record_gamma_one_diamond_period_1195')]:s=s.replace(a,b)
write('audit_gamma_one_diamond_period_1195.ps1',s)
print(json.dumps(dict(modules=4,queries=17,edges=len(edges))))
