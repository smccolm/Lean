from pathlib import Path
from datetime import datetime, timezone
import ast, json, re, hashlib

p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
mods=['SourceGammaOneDiamondFieldRatios','SourceGammaOneFieldCuspGerm',
      'SourceGammaOneDiamondFieldHom','SourceGammaOneDiamondFieldLabels',
      'SourceGammaOneDiamondFieldJ','SourceLaurentAlgebraicCoefficient',
      'SourceLaurentAlgebraicallyClosedLift']
attempts=['1197c','1198a','1199b','1200a','1201a','1202c','1203a']
ev={m:m+a for m,a in zip(mods,attempts)}
ths=[];defs=[]
for m in mods:
    assert (p/(ev[m]+'.exit')).read_text().strip()=='0'
    assert (p/(ev[m]+'.log')).stat().st_size==0
    code=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',(p/(m+'.lean')).read_text(encoding='utf-8'),flags=re.S))
    ns='Dubon2026.SourceFunctionField.'+('GammaOne.' if 'GammaOne' in m else '')
    ths += [ns+x for x in re.findall(r'^theorem\s+(\w+)',code,re.M)]
    defs += [ns+x for x in re.findall(r'^def\s+(\w+)',code,re.M)]
assert (len(ths),len(defs))==(17,6),(ths,defs)
edges=ths+defs+['Dubon2026.SourceFunctionField.GammaOne.'+x for x in [
    'modular_ratio_mem','functionFieldOver_modular_ratio','diamondGL_le_conj',
    'cuspRealize_eventuallyEq_of_ratio','cuspRealize_const_eventuallyEq',
    'cuspRealize_add_eventuallyEq','cuspRealize_mul_eventuallyEq',
    'cuspRealize_mul_left_eventuallyEq','realize_jCoordinateOver']]+[
    'Dubon2026.sourceGammaOneDiamondLabel_lift',
    'Dubon2026.SourceFunctionField.JMultiplicity.jf_smul',
    'Dubon2026.SourceCurve.ConstantField.exists_translation_of_transcendental',
    'Dubon2026.SourceFunctionField.coeffMap']
prior=json.loads((p/'source-gamma-one-diamond-period-1-audit-config.json').read_text())
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,roots=ths+defs,
    proofEdges=edges,localModules=mods+prior['localModules'],separatelyAxiomChecked=[],compileEvidence=ev)
def write(n,s):
    f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
stem='source-gamma-one-diamond-field-1'
write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
old='SourceGammaOneDiamondPeriod';new='SourceGammaOneDiamondField'
for a,b in [('Audit1','Audit1'),('DependencyAudit1','DependencyAudit1'),('ScratchOwnership1195','ScratchOwnership1204')]:
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
        s=s[:start]+' occur in the original complex Gamma1 field diamond, exact translated cusp germs, inverse and unit labels, fixed original j, and Laurent coefficient algebraicity/lift. Arithmetic field stability, Picard comparison and association remain unresolved'+s[end:]
    else:
        s=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),s)
    s=s.replace('GAMMA ONE DIAMOND PERIOD','GAMMA ONE DIAMOND FIELD')
    write(new+b+'.lean',s)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
reuse=[p/'diamond-field-route-1197.md',p/'diamond-arithmetic-descent-route-1202.md',
       p/'source-gamma-one-diamond-period-1-scratch-receipt.json']
reuse += [r/'Extension/Dubon2026'/(m+'.lean') for m in [
    'SourceGammaOneAllModularRatioMembership','SourceGammaOneFieldModularRatio',
    'SourceGammaOneCuspRealizationAlgebra','SourceGammaOneCuspPlaceLeftInvariance',
    'SourceGammaOneCuspJExactOrder','SourceTranscendentalTranslation',
    'SourceLaurentCoefficientMap','SourceLaurentSpanDescent',
    'SourceGammaOneComplexTranslations','SourceGammaOneComplexFieldIndependence']]
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),
    chain='DUB17 Theorem 2.6 / DUB18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight association -> arithmetic Gamma1 diamond/Picard comparison -> actual field diamond and arithmetic coefficient descent.',
    reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in reuse],
    shorterRoute='Original equal-weight modular quotients, native slash translation and injective cusp germs give the exact complex field automorphism without another analytic model. Existing transcendental translation automorphisms and finite polynomial roots give Laurent coefficient algebraicity and the same-series lift over algebraically closed constants; no new geometric integrality framework is needed.',
    assumptionsToDischarge=[
        'The literal diamond translate stays in the original complex function field, with exact realization at every translated cusp.',
        'Its ring laws, inverse, constant preservation, lift independence, unit multiplication and fixed original j are proved.',
        'Every Laurent root of a nonzero polynomial over the base Laurent field has algebraic coefficients; over algebraically closed constants the same series has a literal coefficient lift.'],
    remaining='The fixed-j field relation must still be transported to use the Laurent lifting theorem on the actual diamond image, and membership in the original arithmetic field must be proved. Arithmetic field stability, Galois/Picard diamond comparison, original homogeneous coefficient convention, parabolic transfer preimages and exceptional primes, all-weight association and higher continuation remain.16/20; DUB17--20 OPEN.',
    preservedFailures='1197a/b elaboration and subgroup lemma names;1199a coercions in inverse laws;1202a/b missing CharZero infinitude import. Failed sources and logs preserved. No limits or proof standards changed.',
    externalBuild=False,externalImport=False,rootPinsChanged=False)
write('source-gamma-one-diamond-field-audit-route-1204.json',json.dumps(route,indent=2)+'\n')
s=(p/'record_gamma_one_diamond_period_1195.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-diamond-period-audit-route-1195','source-gamma-one-diamond-field-audit-route-1204'),
    ('source-gamma-one-diamond-period-1',stem),(old,new),('ScratchOwnership1195','ScratchOwnership1204'),
    ('GAMMA ONE DIAMOND PERIOD','GAMMA ONE DIAMOND FIELD')]:s=s.replace(a,b)
s=s.replace('(4, 17, 28)',str((7,23,len(edges)))).replace('all 28 required',f'all {len(edges)} required')
s=s.replace('== 4','== 7').replace('linterScopes=4','linterScopes=7')
s=s.replace('requiredProofValueEdges=28',f'requiredProofValueEdges={len(edges)}').replace('proofEdges=28',f'proofEdges={len(edges)}')
s=s.replace('modules=4, queries=17','modules=7, queries=23')
ast.parse(s);write('record_gamma_one_diamond_field_1204.py',s)
s=(p/'audit_gamma_one_diamond_period_1195.ps1').read_text(encoding='utf-8')
for a,b in [(old,new),('ScratchOwnership1195','ScratchOwnership1204'),('record_gamma_one_diamond_period_1195','record_gamma_one_diamond_field_1204')]:s=s.replace(a,b)
write('audit_gamma_one_diamond_field_1204.ps1',s)
print(json.dumps(dict(modules=7,queries=23,edges=len(edges))))
