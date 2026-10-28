from pathlib import Path
import ast
p=Path(__file__).parent
s=(p/'prepare_gamma_one_diamond_period_audit_1195.py').read_text(encoding='utf-8')
a=s.index('mods=');b=s.index('ev=',a)
s=s[:a]+"mods=['SourceGammaOneDiamondPeriodTate']\nattempts=['1194a']\n"+s[b:]
s=s.replace("==(13,4)","==(2,1)")
a=s.index('edges=');b=s.index('cfg=',a)
s=s[:a]+'''edges=ths+defs+['Dubon2026.SourceFunctionField.GammaOne.periodDiamondLinear_preserves_integralLattice',
    'Dubon2026.SourceFunctionField.GammaOne.periodLatticeDiamond',
    'Dubon2026.TateModule.Period.phi2_baseChange']
prior=json.loads((p/'source-gamma-one-diamond-period-1-audit-config.json').read_text())
'''+s[b:]
s=s.replace("stem='source-gamma-one-diamond-period-1'","stem='source-gamma-one-diamond-tate-1'")
s=s.replace("old='SourceGammaOneDiamond';new='SourceGammaOneDiamondPeriod'", "old='SourceGammaOneDiamondPeriod';new='SourceGammaOneDiamondTate'")
s=s.replace("('ScratchOwnership1189','ScratchOwnership1195')", "('ScratchOwnership1195','ScratchOwnership1196')")
s=s.replace("s=s.replace('GAMMA ONE DIAMOND','GAMMA ONE DIAMOND PERIOD').replace('Gamma One Diamond','Gamma One Diamond Period')", "s=s.replace('GAMMA ONE DIAMOND PERIOD','GAMMA ONE DIAMOND TATE').replace('Gamma One Diamond Period','Gamma One Diamond Tate')")
s=s.replace('actual slash cusp diamond, original endpoint periods, stable original integer lattice and literal homogeneous-valued finite H1 transpose', 'actual original integral-period quotient diamond and its native Tate-torus base-change intertwiner')
a=s.index('reuse=[p/');b=s.index('sha=lambda',0) if False else s.index('route=dict',a)
s=s[:a]+'''reuse=[p/'SourceGammaOneDiamondPeriodLattice.lean',
    r/'Extension/Dubon2026/SourceGammaOnePeriodTateHecke.lean',
    r/'Extension/Dubon2026/SourceGammaOneComplexTatePeriods.lean',
    r/'Extension/Dubon2026/SourceTateTorusNaturality.lean']
'''+s[b:]
s=s.replace('diamond comparison -> literal slash, original integral periods and homogeneous-valued native H1 transpose.', 'diamond comparison -> literal slash on the original period quotient and Tate-torus base change.')
a=s.index('    shorterRoute=');b=s.index('    remaining=',a)
s=s[:a]+'''    shorterRoute='Apply the existing native Tate-torus naturality theorem to the already proved actual integral-period diamond; no new tensor basis or Tate-module theory.',
    assumptionsToDischarge=['The actual dual slash diamond descends to the original integer-period quotient.',
        'The original Tate-torus equivalence intertwines this quotient action with base change of the actual integral-lattice diamond.'],
'''+s[b:]
a=s.index("    preservedFailures=");b=s.index("    externalBuild=",a)
s=s[:a]+s[b:]
s=s.replace("write('source-gamma-one-diamond-period-audit-route-1195.json'", "write('source-gamma-one-diamond-tate-audit-route-1196.json'")
a=s.index("s=(p/'record_gamma_one_diamond_");b=s.index("print(json.dumps",a)
s=s[:a]+'''s=(p/'record_gamma_one_diamond_period_1195.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-diamond-period-audit-route-1195','source-gamma-one-diamond-tate-audit-route-1196'),
    ('source-gamma-one-diamond-period-1',stem),(old,new),('ScratchOwnership1195','ScratchOwnership1196'),
    ('GAMMA ONE DIAMOND PERIOD','GAMMA ONE DIAMOND TATE')]:s=s.replace(a,b)
s=s.replace('(4, 17, 28)',str((1,3,len(edges)))).replace('== 4','== 1').replace('linterScopes=4','linterScopes=1')
s=s.replace('all 28 required',f'all {len(edges)} required').replace('requiredProofValueEdges=28',f'requiredProofValueEdges={len(edges)}').replace('proofEdges=28',f'proofEdges={len(edges)}').replace('modules=4, queries=17','modules=1, queries=3')
ast.parse(s);write('record_gamma_one_diamond_tate_1196.py',s)
s=(p/'audit_gamma_one_diamond_period_1195.ps1').read_text(encoding='utf-8')
for a,b in [(old,new),('ScratchOwnership1195','ScratchOwnership1196'),('record_gamma_one_diamond_period_1195','record_gamma_one_diamond_tate_1196')]:s=s.replace(a,b)
write('audit_gamma_one_diamond_tate_1196.ps1',s)
'''+s[b:]
s=s.replace('dict(modules=4,queries=17,edges=len(edges))','dict(modules=1,queries=3,edges=len(edges))')
ast.parse(s)
f=p/'generate_gamma_one_diamond_tate_audit_1196.py';assert not f.exists()
f.write_text(s,encoding='utf-8')
print(str(f))
