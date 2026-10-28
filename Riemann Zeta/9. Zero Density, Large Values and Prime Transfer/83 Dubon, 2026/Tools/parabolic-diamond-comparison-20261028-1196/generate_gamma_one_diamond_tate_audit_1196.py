from pathlib import Path
from datetime import datetime, timezone
import ast, json, re, hashlib

p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
mods=['SourceGammaOneDiamondPeriodTate']
attempts=['1194a']
ev={m:m+a for m,a in zip(mods,attempts)}
ths=[];defs=[]
for m in mods:
    assert (p/(ev[m]+'.exit')).read_text().strip()=='0'
    assert (p/(ev[m]+'.log')).stat().st_size==0
    code=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',(p/(m+'.lean')).read_text(encoding='utf-8'),flags=re.S))
    ns='Dubon2026.SourceFunctionField.GammaOne.'
    ths += [ns+x for x in re.findall(r'^theorem\s+(\w+)',code,re.M)]
    defs += [ns+x for x in re.findall(r'^def\s+(\w+)',code,re.M)]
assert (len(ths),len(defs))==(2,1),(ths,defs)
edges=ths+defs+['Dubon2026.SourceFunctionField.GammaOne.periodDiamondLinear_preserves_integralLattice',
    'Dubon2026.SourceFunctionField.GammaOne.periodLatticeDiamond',
    'Dubon2026.TateModule.Period.phi2_baseChange']
prior=json.loads((p/'source-gamma-one-diamond-period-1-audit-config.json').read_text())
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,roots=ths+defs,
    proofEdges=edges,localModules=mods+prior['localModules'],separatelyAxiomChecked=[],compileEvidence=ev)
def write(n,s):
    f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
stem='source-gamma-one-diamond-tate-1'
write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
old='SourceGammaOneDiamondPeriod';new='SourceGammaOneDiamondTate'
for a,b in [('Audit1','Audit1'),('DependencyAudit1','DependencyAudit1'),('ScratchOwnership1195','ScratchOwnership1196')]:
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
        s=s[:start]+' occur in the actual original integral-period quotient diamond and its native Tate-torus base-change intertwiner. Arithmetic Picard diamond and the original coefficient convention, transfer lifting and exceptional primes remain unresolved'+s[end:]
    else:
        s=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),s)
    s=s.replace('GAMMA ONE DIAMOND PERIOD','GAMMA ONE DIAMOND TATE').replace('Gamma One Diamond Period','Gamma One Diamond Tate')
    write(new+b+'.lean',s)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
reuse=[p/'SourceGammaOneDiamondPeriodLattice.lean',
    r/'Extension/Dubon2026/SourceGammaOnePeriodTateHecke.lean',
    r/'Extension/Dubon2026/SourceGammaOneComplexTatePeriods.lean',
    r/'Extension/Dubon2026/SourceTateTorusNaturality.lean']
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),
    chain='DUB17 Theorem 2.6 / DUB18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight association -> arithmetic realization of original finite Gamma1 characters -> diamond comparison -> literal slash on the original period quotient and Tate-torus base change.',
    reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in reuse],
    shorterRoute='Apply the existing native Tate-torus naturality theorem to the already proved actual integral-period diamond; no new tensor basis or Tate-module theory.',
    assumptionsToDischarge=['The actual dual slash diamond descends to the original integer-period quotient.',
        'The original Tate-torus equivalence intertwines this quotient action with base change of the actual integral-lattice diamond.'],
    remaining='The independently defined arithmetic Picard diamond and the identification of the required original homogeneous coefficient action remain. The separate parabolic transfer lifting and exceptional primes, Frobenius/inertia, original all-weight association and higher continuation remain.16/20; DUB17--20 OPEN.',
    externalBuild=False,externalImport=False,rootPinsChanged=False)
write('source-gamma-one-diamond-tate-audit-route-1196.json',json.dumps(route,indent=2)+'\n')
s=(p/'record_gamma_one_diamond_period_1195.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-diamond-period-audit-route-1195','source-gamma-one-diamond-tate-audit-route-1196'),
    ('source-gamma-one-diamond-period-1',stem),(old,new),('ScratchOwnership1195','ScratchOwnership1196'),
    ('GAMMA ONE DIAMOND PERIOD','GAMMA ONE DIAMOND TATE')]:s=s.replace(a,b)
s=s.replace('(4, 17, 28)',str((1,3,len(edges)))).replace('== 4','== 1').replace('linterScopes=4','linterScopes=1')
s=s.replace('all 28 required',f'all {len(edges)} required').replace('requiredProofValueEdges=28',f'requiredProofValueEdges={len(edges)}').replace('proofEdges=28',f'proofEdges={len(edges)}').replace('modules=4, queries=17','modules=1, queries=3')
ast.parse(s);write('record_gamma_one_diamond_tate_1196.py',s)
s=(p/'audit_gamma_one_diamond_period_1195.ps1').read_text(encoding='utf-8')
for a,b in [(old,new),('ScratchOwnership1195','ScratchOwnership1196'),('record_gamma_one_diamond_period_1195','record_gamma_one_diamond_tate_1196')]:s=s.replace(a,b)
write('audit_gamma_one_diamond_tate_1196.ps1',s)
print(json.dumps(dict(modules=1,queries=3,edges=len(edges))))
