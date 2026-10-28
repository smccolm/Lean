from pathlib import Path
from datetime import datetime, timezone
import ast, json, re, hashlib

p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
mods=['SourceGammaOneDiamondArithmeticRelation','SourceLaurentCoefficientProjection',
      'SourceLaurentFieldIntersection','SourceGammaOneDiamondArithmeticLift',
      'SourceGammaOneArithmeticDiamond','SourceCurveFieldEquivPicard','SourceGammaOneDiamondPicard']
attempts=['1205b','1206c','1207d','1208c','1209b','1210b','1211a']
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
edges=ths+defs+[
    'Dubon2026.SourceFunctionField.GammaOne.diamondFieldHom_j',
    'Dubon2026.SourceFunctionField.GammaOne.diamondFieldHom_cuspGerm',
    'Dubon2026.SourceFunctionField.GammaOne.finiteDimensional_jCoordinateOver',
    'Dubon2026.SourceFunctionField.GammaOne.ConstantField.fieldMap_j',
    'Dubon2026.SourceFunctionField.exists_laurent_lift_of_relation',
    'Dubon2026.SourceFunctionField.isAlgebraic_laurent_coeff_of_relation',
    'Dubon2026.SourceCurve.ConstantField.exists_translation_of_transcendental',
    'Dubon2026.SourceFunctionField.OriginalConstantField.coeffMap_sigma_rational',
    'Dubon2026.SourceCurve.Place.ord_comapEquiv',
    'Dubon2026.SourceCurve.divisorTransform_orders',
    'Dubon2026.SourceCurve.degree_divisorTransform',
    'Dubon2026.SourceFunctionField.GammaOne.functionFieldOver_residue_bijective',
    'Dubon2026.SourceFunctionField.GammaOne.diamondFieldHom_lift_independent']
prior=json.loads((p/'source-gamma-one-diamond-field-1-audit-config.json').read_text())
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,roots=ths+defs,
    proofEdges=edges,localModules=mods+prior['localModules'],separatelyAxiomChecked=[],compileEvidence=ev)
def write(n,s):
    f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
stem='source-gamma-one-arithmetic-diamond-1'
write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
old='SourceGammaOneDiamondField';new='SourceGammaOneArithmeticDiamond'
for a,b in [('Audit1','Audit1'),('DependencyAudit1','DependencyAudit1'),('ScratchOwnership1204','ScratchOwnership1212')]:
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
        s=s[:start]+' occur in the transported original j-field relation, Laurent coefficient lift, original arithmetic field membership, arithmetic diamond automorphism and independent arithmetic/complex Picard actions. Galois commutation, period comparison and association remain unresolved'+s[end:]
    else:
        s=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),s)
    s=s.replace('GAMMA ONE DIAMOND FIELD','GAMMA ONE ARITHMETIC DIAMOND')
    write(new+b+'.lean',s)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
reuse=[p/'diamond-arithmetic-descent-route-1202.md',p/'source-gamma-one-diamond-field-1-scratch-receipt.json']
reuse += [r/'Extension/Dubon2026'/(m+'.lean') for m in [
    'SourceGammaOneComplexFieldExtension','SourceLaurentSpanDescent',
    'SourceCurvePlaceTransport','SourceCurvePrincipalDivisorTransport',
    'SourceCurvePicardGroup','SourceGammaOneArithmeticDivisors']]
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),
    chain='DUB17 Theorem 2.6 / DUB18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight association -> original finite Gamma1 homogeneous-coefficient arithmetic realization -> arithmetic diamond/Picard comparison.',
    reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in reuse],
    shorterRoute='Transport the existing finite original j-field relation through the proved complex diamond. Use the already audited same-series Laurent lift. Descend original field membership by a single linear coefficient functional on a finite numerator/denominator span; no geometric integrality framework. Reuse literal valuation, order and principal-divisor transport to construct both Picard actions independently of periods.',
    assumptionsToDischarge=[
        'The actual complex diamond image of every original arithmetic field element satisfies a nonzero polynomial over the arithmetic Laurent field, without an algebraicity premise.',
        'Its exact Laurent coefficient lift lies in the original arithmetic field: arithmetic field stability is proved.',
        'The original arithmetic diamond has field laws, constants, inverse, fixed j and the exact original complex comparison.',
        'Both original arithmetic and complex diamonds induce actual degree-zero Picard automorphisms and preserve torsion; closed residue fields and principal-divisor transport discharge the construction inputs.'],
    remaining='Supersedes the historical 1204 remaining arithmetic relation/lift/membership boundary only. Galois commutation, Picard-period comparison, original homogeneous coefficient convention, parabolic transfer preimages and exceptional primes, all-weight association and higher continuation remain.16/20; DUB17--20 OPEN.',
    preservedFailures='1205a induction index;1206a/b scalar instances;1207a prerequisite guard before Lean,1207b/c scalar instances and induction;1208a implicit field,1208b unused instance warning;1209a redundant rewrites;1210a missing section inclusion. Failed sources/logs retained. No limits or proof standards changed.',
    externalBuild=False,externalImport=False,rootPinsChanged=False)
write('source-gamma-one-arithmetic-diamond-audit-route-1212.json',json.dumps(route,indent=2)+'\n')
s=(p/'record_gamma_one_diamond_field_1204.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-diamond-field-audit-route-1204','source-gamma-one-arithmetic-diamond-audit-route-1212'),
    ('source-gamma-one-diamond-field-1',stem),(old,new),('ScratchOwnership1204','ScratchOwnership1212'),
    ('GAMMA ONE DIAMOND FIELD','GAMMA ONE ARITHMETIC DIAMOND')]:s=s.replace(a,b)
s=s.replace('(7, 23, 36)',str((7,len(ths+defs),len(edges))))
s=s.replace('all 36 required',f'all {len(edges)} required').replace('requiredProofValueEdges=36',f'requiredProofValueEdges={len(edges)}')
s=s.replace('proofEdges=36',f'proofEdges={len(edges)}').replace('queries=23',f'queries={len(ths+defs)}')
ast.parse(s);write('record_gamma_one_arithmetic_diamond_1212.py',s)
s=(p/'audit_gamma_one_diamond_field_1204.ps1').read_text(encoding='utf-8')
for a,b in [(old,new),('ScratchOwnership1204','ScratchOwnership1212'),('record_gamma_one_diamond_field_1204','record_gamma_one_arithmetic_diamond_1212')]:s=s.replace(a,b)
write('audit_gamma_one_arithmetic_diamond_1212.ps1',s)
print(json.dumps(dict(modules=7,theorems=len(ths),constructions=len(defs),queries=len(ths+defs),edges=len(edges))))
