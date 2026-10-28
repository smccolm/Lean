from pathlib import Path
from datetime import datetime, timezone
import ast, json, re, hashlib

p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
mods=['SourceGammaOneDiamondAnalyticGerms','SourceGammaOneDiamondAnalyticPlaces',
      'SourceGammaOneDiamondAnalyticDivisors','SourceGammaOneDiamondEndpoint',
      'SourceGammaOneDiamondPicardPeriods','SourceGammaOneDiamondComplexComparison',
      'SourceGammaOneArithmeticDiamondTate']
attempts=['1213a','1214b','1215a','1216a','1217a','1218a','1219a']
ev={m:m+a for m,a in zip(mods,attempts)}
ths=[];defs=[]
for m in mods:
    assert (p/(ev[m]+'.exit')).read_text().strip()=='0'
    assert (p/(ev[m]+'.log')).stat().st_size==0
    raw=(p/(m+'.lean')).read_text(encoding='utf-8')
    ns=re.search(r'^namespace (\S+)',raw,re.M)[1]+'.'
    code=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',raw,flags=re.S))
    ths += [ns+x for x in re.findall(r'^theorem\s+(\w+)',code,re.M)]
    defs += [ns+x for x in re.findall(r'^def\s+(\w+)',code,re.M)]
edges=ths+defs+['Dubon2026.SourceFunctionField.GammaOne.'+x for x in [
    'diamondFieldHom_cuspGerm','modularDiamond_translate_coe','modular_ratio_mem',
    'realize_smul_eq_translated_ratio','fieldCuspGerm','arithmeticDiamondPicard',
    'complexDiamondPicard','analyticPicardHom_surjective','picardPeriodEquiv_analytic_divisor',
    'periodDiamondLinear_along','periodDiamondLinear_preserves_integralLattice',
    'periodTateTensor_diamond','ConstantField.fieldMap_arithmeticDiamondHom',
    'ConstantField.liftPlace_unique','ConstantField.mem_liftPlace_iff',
    'ConstantField.tateComplexEquiv_naturality']]
prior=json.loads((p/'source-gamma-one-arithmetic-diamond-1-audit-config.json').read_text())
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,roots=ths+defs,
    proofEdges=edges,localModules=mods+['SourceGammaOneDiamondPeriodTate']+prior['localModules'],
    separatelyAxiomChecked=[],compileEvidence=ev)
def write(n,s):
    f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
stem='source-diamond-picard-periods-1'
write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
old='SourceGammaOneArithmeticDiamond';new='SourceDiamondPicardPeriods'
for a,b in [('Audit1','Audit1'),('DependencyAudit1','DependencyAudit1'),('ScratchOwnership1212','ScratchOwnership1220')]:
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
        s=s[:start]+' occur in the original diamond quotient and analytic place identities, actual analytic divisor and period actions, independent complex Picard-period comparison, arithmetic constant-field square, and original arithmetic Picard Tate tensor compatibility. Galois commutation, homogeneous coefficient comparison and association remain unresolved'+s[end:]
    else:
        s=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),s)
    s=s.replace('GAMMA ONE ARITHMETIC DIAMOND','DIAMOND PICARD PERIODS')
    write(new+b+'.lean',s)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
reuse=[p/'diamond-picard-period-route-1213.md',
       p/'source-gamma-one-diamond-field-1-scratch-receipt.json',
       p/'source-gamma-one-arithmetic-diamond-1-scratch-receipt.json',
       p/'source-gamma-one-diamond-tate-1-scratch-receipt.json']
reuse += [r/'Extension/Dubon2026'/(m+'.lean') for m in [
    'SourceGammaOneCuspRatioRealization','SourceGammaOneAnalyticPlaceInvariance',
    'SourceGammaOneAnalyticPicardPresentation','SourceGammaOnePicardPeriodEquiv',
    'SourceGammaOneEndpointHecke','SourceGammaOneComplexTateHecke',
    'SourceGammaOneExtendedPlaceMap','SourceGammaOneDivisorConorm',
    'SourceGammaOneTateComparison','SourceGammaOneArithmeticTatePeriods']]
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),
    chain='DUB17 Theorem 2.6 / DUB18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight association -> original finite Gamma1 homogeneous-coefficient arithmetic realization -> arithmetic diamond/Picard comparison.',
    reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in reuse],
    shorterRoute='Original quotient and cusp germ identities determine the field diamond. Native Mobius order invariance identifies analytic places. The existing moving lemma covers every Picard class from finite analytic divisors, avoiding new cusp presentation. The existing primitive formula and degree zero remove the endpoint basepoint correction. Unique original constant-field place extension gives the arithmetic conorm square. Native Tate naturality composes the actual arithmetic Picard action with the original period tensor equivalence.',
    assumptionsToDischarge=[
        'The actual field diamond has the literal modular quotient, interior analytic germ and analytic place action.',
        'The independent complex field/Picard diamond agrees with the original period quotient on every Picard class; the moving lemma discharges analytic representatives and degree zero discharges the basepoint term.',
        'The original arithmetic-to-complex divisor conorm and Picard map intertwine the arithmetic and complex diamonds, by unique place extension and the proved field square.',
        'For every Tate prime, the original arithmetic Picard diamond acts on the original p-adic period tensor by the native dual slash diamond, without extra prime restrictions or compatibility premises.'],
    remaining='Supersedes historical missing Picard-period and arithmetic constant-field compatibility in scopes 1204/1212. Galois commutation, original homogeneous coefficient convention, parabolic transfer preimages and exceptional primes, all-weight association and higher continuation remain.16/20; DUB17--20 OPEN.',
    preservedFailures='1214a determinant coercion rewrite, repaired with an explicit native determinant equality; source/log retained. No proof limits or standards changed.',
    externalBuild=False,externalImport=False,rootPinsChanged=False)
write('source-diamond-picard-periods-audit-route-1220.json',json.dumps(route,indent=2)+'\n')
s=(p/'record_gamma_one_arithmetic_diamond_1212.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-arithmetic-diamond-audit-route-1212','source-diamond-picard-periods-audit-route-1220'),
    ('source-gamma-one-arithmetic-diamond-1',stem),(old,new),('ScratchOwnership1212','ScratchOwnership1220'),
    ('GAMMA ONE ARITHMETIC DIAMOND','DIAMOND PICARD PERIODS')]:s=s.replace(a,b)
s=s.replace('(7, 34, 47)',str((7,len(ths+defs),len(edges))))
s=s.replace('all 47 required',f'all {len(edges)} required').replace('requiredProofValueEdges=47',f'requiredProofValueEdges={len(edges)}')
s=s.replace('proofEdges=47',f'proofEdges={len(edges)}').replace('queries=34',f'queries={len(ths+defs)}')
ast.parse(s);write('record_diamond_picard_periods_1220.py',s)
s=(p/'audit_gamma_one_arithmetic_diamond_1212.ps1').read_text(encoding='utf-8')
for a,b in [(old,new),('ScratchOwnership1212','ScratchOwnership1220'),('record_gamma_one_arithmetic_diamond_1212','record_diamond_picard_periods_1220')]:s=s.replace(a,b)
write('audit_diamond_picard_periods_1220.ps1',s)
print(json.dumps(dict(modules=7,theorems=len(ths),constructions=len(defs),queries=len(ths+defs),edges=len(edges))))
