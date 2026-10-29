from pathlib import Path
from datetime import datetime, timezone
import ast, hashlib, json, re
p=Path(__file__).parent
versions=json.loads((p/'gamma-one-arithmetic-orbit-versions-1429.json').read_text(encoding='utf-8'))
mods=list(versions);ths=[];defs=[]
for m in mods:
    code=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',(p/(m+'.lean')).read_text(encoding='utf-8'),flags=re.S))
    ns=re.search(r'^namespace (\S+)',code,re.M)[1]+'.'
    ths += [ns+x for x in re.findall(r'^theorem\s+([\w.\x27]+)',code,re.M)]
    defs += [ns+x for x in re.findall(r'^(?:def|instance)\s+([\w.\x27]+)',code,re.M)]
gn='Dubon2026.SourceFunctionField.GammaOne.'
cr=gn+'CoefficientReduction.'
roots=[cr+'binaryArithmeticTateGaloisRep_arithmetic_descent_of_degree_genus_eq',cr+'exists_parabolic_binaryTate_galois_orbit_frobenius_of_degree_genus_eq']
edges=ths+defs+[
    'Dubon2026.absolute_continuous_normInertia_arithmetic_descent',
    'ContinuousMonoidHom.toHomUnits',
    'Dubon2026.sourceRationalLocalValuation_inertia',
    'Dubon2026.sourceRationalLocalValuation_prime',
    'Dubon2026.GaussReduction.residue_charP_of_prime_mem_nonunits',
    gn+'binaryArithmeticTateGaloisRep_continuous',
    cr+'gammaOne_binaryArithmeticTateGaloisRep_eq_one_of_inertia_of_degree_genus_eq',
    'Dubon2026.sourceGammaOneBinaryDiamondCoefficient_eq_diagonal',
    gn+'arithmeticTateGaloisRep_diamond',
    'Dubon2026.sourceTwistedCoefficientDualAction_operator',
    'Dubon2026.sourceCyclotomicHomogeneousAction_apply',
    gn+'exists_binaryTate_restriction_diamond_fixed',
    cr+'exists_gammaOne_galois_frobenius_quadratic_of_degree_genus_eq',
    'Dubon2026.sourceGammaOneBinaryRestrictionH1_diamond',
    gn+'binaryTateH1Equiv']
assert (len(mods),len(ths),len(defs),len(edges))==(5,6,0,21)
assert len(set(edges))==len(edges)
prior=json.loads((p/'source-gamma-one-continuity-1-audit-config.json').read_text(encoding='utf-8'))['localModules']
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,roots=roots,proofEdges=edges,localModules=list(dict.fromkeys(prior+mods)),separatelyAxiomChecked=[],compileEvidence={m:m+'-1429' for m in mods})
def write(n,s):
    f=p/n
    if f.exists():
        assert n in ['source-gamma-one-arithmetic-orbit-1-audit-config.json','SourceGammaOneArithmeticOrbitAudit1.lean','SourceGammaOneArithmeticOrbitDependencyAudit1.lean','SourceGammaOneArithmeticOrbitScratchOwnership1430.lean']
        assert f.read_text(encoding='utf-8')==s,f
    else:f.write_text(s,encoding='utf-8')
stem='source-gamma-one-arithmetic-orbit-1';write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
old,new='SourceGammaOneInertia','SourceGammaOneArithmeticOrbit'
for a,b in [('Audit1','Audit1'),('DependencyAudit1','DependencyAudit1'),('ScratchOwnership1368','ScratchOwnership1430')]:
    s=(p/(old+a+'.lean')).read_text(encoding='utf-8')
    s='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n'+s[s.index('\nopen Lean'):]
    if a=='Audit1':
        s=re.sub(r'(#print axioms [^\n]+\n)+',''.join('#print axioms '+x+'\n' for x in cfg['queries']),s,count=1)
        for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:s=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),s)
        s=re.sub(r'#lint in [^\n]+\n','',s).rstrip()+'\n\n'+''.join('#lint in '+m+'\n' for m in mods)
    elif a=='DependencyAudit1':
        for k,v in [('roots',roots),('localModules',cfg['localModules']),('required',edges)]:s=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),s)
        start=s.index(' occur in the ');end=s.index('; DUB17--20 OPEN.',start)
        s=s[:start]+' occur in the proof value closure of the actual prescribed-support arithmetic descent and the original parabolic Tate Galois-orbit Frobenius polynomial. Continuity, unit lift, original norm-inertia triviality, diamond stability and original parabolic diamond fixedness are derived. Only the original degree/genus equalities remain for these local conclusions; original character nonvanishing and two-dimensional realization remain'+s[end:]
    else:s=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),s)
    s=s.replace('GAMMA ONE INERTIA','GAMMA ONE ARITHMETIC ORBIT')
    write(new+b+'.lean',s)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
routes=[p/n for n in ['gamma-one-arithmetic-descent-reuse-1424.json','gamma-one-unit-lift-reuse-1425.json','gamma-one-twisted-diamond-reuse-1426.json']]
rr=[json.loads(f.read_text(encoding='utf-8')) for f in routes]
reuse=list(dict.fromkeys(routes+[Path(row['path']) for r in rr for row in (r['reuse'] if isinstance(r['reuse'],list) else [r['reuse']])]))
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain=rr[0]['chain'],reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in reuse],shorterRoute=[r['selected'] for r in rr],assumptionsToDischarge=['Derive norm-inertia triviality at the literal pulled-back rational local valuation from original coordinate-degree and genus equality.','Reuse the proved continuous unit lift and original arithmetic quotient descent; no continuity, unit action, inertia identity or arithmetic factorization is supplied.','Derive combined-diamond stability under the genuine global Galois action using the exact original diagonal coefficient and Picard commutations.','Derive the Frobenius polynomial on every Galois translate of the actual Tate lift of an original parabolic class. Diamond fixedness is derived; the existing Tate/H1 comparison requires 3<p.'],remaining='Original coordinate-degree and genus equalities remain explicit. Nonzero parabolic Hecke-character realization/transfer, exceptional coefficient primes, two-dimensional all-weight arithmetic association, automorphy and literal higher continuation remain. 16/20; DUB-17--20 OPEN.',externalBuild=False,externalImport=False,rootPinsChanged=False,proofLimitsChanged=False)
routefile='source-gamma-one-arithmetic-orbit-audit-route-1430.json';write(routefile,json.dumps(route,indent=2)+'\n')
s=(p/'record_gamma_one_inertia_1368.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-inertia-audit-route-1368',routefile[:-5]),('source-gamma-one-inertia-1',stem),(old,new),('ScratchOwnership1368','ScratchOwnership1430'),('GAMMA ONE INERTIA','GAMMA ONE ARITHMETIC ORBIT')]:s=s.replace(a,b)
s=s.replace('(8, 16, 35)','(5, 6, 21)').replace('queries=16','queries=6').replace('modules=8','modules=5').replace('linterScopes=8','linterScopes=5')
s=s.replace("text.count('with 16 linters') == 8","text.count('with 16 linters') == 5")
s=s.replace('all 35 required','all 21 required').replace('requiredProofValueEdges=35','requiredProofValueEdges=21').replace('proofEdges=35','proofEdges=21')
ast.parse(s);write('record_gamma_one_arithmetic_orbit_1430.py',s)
s=(p/'audit_gamma_one_inertia_1368.ps1').read_text(encoding='utf-8-sig')
for a,b in [(old,new),('ScratchOwnership1368','ScratchOwnership1430'),('record_gamma_one_inertia_1368','record_gamma_one_arithmetic_orbit_1430')]:s=s.replace(a,b)
write('audit_gamma_one_arithmetic_orbit_1430.ps1',s)
print(json.dumps(dict(modules=len(mods),queries=len(cfg['queries']),proofEdges=len(edges))))
