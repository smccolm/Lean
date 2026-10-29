from pathlib import Path
from datetime import datetime, timezone
import ast, hashlib, json, re
p=Path(__file__).parent
versions=json.loads((p/'gamma-one-continuity-versions-1422.json').read_text(encoding='utf-8'))
mods=list(versions);ths=[];defs=[]
for m in mods:
    code=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',(p/(m+'.lean')).read_text(encoding='utf-8'),flags=re.S))
    ns=re.search(r'^namespace (\S+)',code,re.M)[1]+'.'
    ths += [ns+x for x in re.findall(r'^theorem\s+([\w.\x27]+)',code,re.M)]
    defs += [ns+x for x in re.findall(r'^(?:def|instance)\s+([\w.\x27]+)',code,re.M)]
gn='Dubon2026.SourceFunctionField.GammaOne.'
roots=[gn+'binaryArithmeticTateGaloisRep_faithful_finite_factor',gn+'binaryArithmeticTateDual_finite']
edges=ths+defs+[
    'Dubon2026.SourceCurve.finite_function_support_of_separating_coordinate',
    gn+'functionFieldOver_residue_bijective',gn+'finiteDimensional_jCoordinateOver',
    gn+'transcendental_jCoordinateOver',gn+'arithmeticPicardTatePeriodTensorEquiv',
    gn+'integralPeriodBasis','Dubon2026.TateModule.proj_eq_zero_iff',
    'Dubon2026.TateModule.pow_smul_shiftOfProjEqZero',
    'Dubon2026.binaryHomogeneousMonomialBasis',
    'Dubon2026.galois_open_kernel_faithful_finite_factor',
    'Dubon2026.sourceRationalAlgebraicClosure_isGalois',
    'Dubon2026.primitiveRootCyclotomicCharacter_continuous',
    gn+'binaryArithmeticTateGaloisRep']
assert (len(mods),len(ths),len(defs),len(edges))==(9,13,1,27)
assert len(set(edges))==len(edges)
prior=json.loads((p/'source-gamma-one-twisted-1-audit-config.json').read_text(encoding='utf-8'))['localModules']
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,roots=roots,proofEdges=edges,localModules=list(dict.fromkeys(prior+mods)),separatelyAxiomChecked=[],compileEvidence={m:m+'-1422' for m in mods})
def write(n,s):
    f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
stem='source-gamma-one-continuity-1';write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
old,new='SourceGammaOneInertia','SourceGammaOneContinuity'
for a,b in [('Audit1','Audit1'),('DependencyAudit1','DependencyAudit1'),('ScratchOwnership1368','ScratchOwnership1423')]:
    s=(p/(old+a+'.lean')).read_text(encoding='utf-8')
    s='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n'+s[s.index('\nopen Lean'):]
    if a=='Audit1':
        s=re.sub(r'(#print axioms [^\n]+\n)+',''.join('#print axioms '+x+'\n' for x in cfg['queries']),s,count=1)
        for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:s=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),s)
        s=re.sub(r'#lint in [^\n]+\n','',s).rstrip()+'\n\n'+''.join('#lint in '+m+'\n' for m in mods)
    elif a=='DependencyAudit1':
        for k,v in [('roots',roots),('localModules',cfg['localModules']),('required',edges)]:s=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),s)
        start=s.index(' occur in the ');end=s.index('; DUB17--20 OPEN.',start)
        s=s[:start]+' occur in the proof value closure of finiteness of the actual homogeneous-valued Tate dual and the actual faithful finite Galois factor of its genuine global action. Finite function/place/Picard fields of definition, open stabilizers, uniform finite-coordinate Tate congruences and cyclotomic continuity are derived. No continuity or finite realization is supplied. Degree/genus equalities for inertia/Frobenius, parabolic character transfer, two-dimensional realization and higher continuation remain'+s[end:]
    else:s=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),s)
    s=s.replace('GAMMA ONE INERTIA','GAMMA ONE CONTINUITY')
    write(new+b+'.lean',s)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
routes=[p/n for n in ['gamma-one-continuity-reuse-1413.json','gamma-one-twisted-factor-reuse-1421.json']]
rr=[json.loads(f.read_text(encoding='utf-8')) for f in routes]
reuse=list(dict.fromkeys(routes+[Path(row['path']) for r in rr for row in r['reuse']]))
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain=rr[0]['chain'],reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in reuse],shorterRoute=[r['selected'] for r in rr],assumptionsToDischarge=['Derive finite fields of definition for the exact Gamma1 functions, places and Picard classes; hence their actual stabilizers are open.','Reuse the exact Tate projection kernel and original period basis to obtain open uniform congruences.','Prove finiteness of the actual homogeneous-valued Tate dual and its factorization through the indicated torsion coordinate.','Derive continuity of its genuine global Galois action and apply the native faithful finite fixed-field theorem. No geometric degree/genus assumption is needed for these continuity conclusions.'],remaining='The original coordinate-degree and genus equalities remain for inertia/Frobenius. Original parabolic character transfer/nonvanishing, exceptional coefficient primes, two-dimensional all-weight arithmetic association, automorphy and literal higher continuation remain. Faithful finite Galois factorization is proved; prescribed unramified arithmetic descent is not yet claimed. 16/20; DUB-17--20 OPEN.',externalBuild=False,externalImport=False,rootPinsChanged=False,proofLimitsChanged=False)
routefile='source-gamma-one-continuity-audit-route-1423.json';write(routefile,json.dumps(route,indent=2)+'\n')
s=(p/'record_gamma_one_inertia_1368.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-inertia-audit-route-1368',routefile[:-5]),('source-gamma-one-inertia-1',stem),(old,new),('ScratchOwnership1368','ScratchOwnership1423'),('GAMMA ONE INERTIA','GAMMA ONE CONTINUITY')]:s=s.replace(a,b)
s=s.replace('(8, 16, 35)','(9, 14, 27)').replace('queries=16','queries=14').replace('modules=8','modules=9').replace('linterScopes=8','linterScopes=9')
s=s.replace("text.count('with 16 linters') == 8","text.count('with 16 linters') == 9")
s=s.replace('all 35 required','all 27 required').replace('requiredProofValueEdges=35','requiredProofValueEdges=27').replace('proofEdges=35','proofEdges=27')
ast.parse(s);write('record_gamma_one_continuity_1423.py',s)
s=(p/'audit_gamma_one_inertia_1368.ps1').read_text(encoding='utf-8-sig')
for a,b in [(old,new),('ScratchOwnership1368','ScratchOwnership1423'),('record_gamma_one_inertia_1368','record_gamma_one_continuity_1423')]:s=s.replace(a,b)
write('audit_gamma_one_continuity_1423.ps1',s)
print(json.dumps(dict(modules=len(mods),queries=len(cfg['queries']),proofEdges=len(edges))))
