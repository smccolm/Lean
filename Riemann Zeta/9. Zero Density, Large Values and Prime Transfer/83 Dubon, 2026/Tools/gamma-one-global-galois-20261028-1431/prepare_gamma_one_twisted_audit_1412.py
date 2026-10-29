from pathlib import Path
from datetime import datetime, timezone
import ast, hashlib, json, re
p=Path(__file__).parent
versions=json.loads((p/'gamma-one-twisted-versions-1411.json').read_text(encoding='utf-8'))
mods=list(versions);ths=[];defs=[]
for m in mods:
    code=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',(p/(m+'.lean')).read_text(encoding='utf-8'),flags=re.S))
    ns=re.search(r'^namespace (\S+)',code,re.M)[1]+'.'
    ths += [ns+x for x in re.findall(r'^theorem\s+([\w.\x27]+)',code,re.M)]
    defs += [ns+x for x in re.findall(r'^def\s+([\w.\x27]+)',code,re.M)]
gn='Dubon2026.SourceFunctionField.GammaOne.';cn=gn+'CoefficientReduction.'
roots=[cn+'exists_parabolic_binaryTate_galois_frobenius_of_degree_genus_eq',cn+'gammaOne_binaryArithmeticTateGaloisRep_eq_one_of_inertia_of_degree_genus_eq',gn+'binaryArithmeticTateGaloisRep_prime']
edges=ths+defs+[
    'Dubon2026.valuation_frobenius_root',
    'Dubon2026.primitiveRootCyclotomicCharacter_apply_root',
    'Dubon2026.homogeneousMatrixRepresentation',
    'Dubon2026.sourceGammaOneBinaryRestrictionH1_parabolic',
    'Dubon2026.sourceGammaOneBinaryRestrictionH1_diamond',
    gn+'binaryTateH1Equiv',gn+'binaryTateH1Equiv_diamond',
    gn+'arithmeticTateGaloisRep_hecke',
    cn+'exists_gammaOne_arithmetic_frobenius_quadratic_of_degree_genus_eq',
    cn+'exists_gammaOne_tate_frobenius_relation_of_degree_genus_eq',
    cn+'exists_gammaOne_hecke_gauss_norm_reduction_of_degree_eq',
    cn+'gammaOne_arithmeticTateGaloisRep_eq_one_of_inertia_of_degree_genus_eq',
    cn+'gammaOne_pic0_eq_zero_of_torsion_of_degree_genus_eq']
assert (len(mods),len(ths),len(defs),len(edges))==(12,14,5,32)
assert len(set(edges))==len(edges)
prior=[]
for stem in ['source-gamma-one-inertia-1','source-gamma-one-arithmetic-1']:
    prior+=json.loads((p/(stem+'-audit-config.json')).read_text(encoding='utf-8'))['localModules']
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,roots=roots,proofEdges=edges,localModules=list(dict.fromkeys(prior+mods)),separatelyAxiomChecked=[],compileEvidence={m:m+'-1411' for m in mods})
def write(n,s):
    f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
stem='source-gamma-one-twisted-1';write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
old,new='SourceGammaOneInertia','SourceGammaOneTwisted'
for a,b in [('Audit1','Audit1'),('DependencyAudit1','DependencyAudit1'),('ScratchOwnership1368','ScratchOwnership1412')]:
    s=(p/(old+a+'.lean')).read_text(encoding='utf-8')
    s='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n'+s[s.index('\nopen Lean'):]
    if a=='Audit1':
        s=re.sub(r'(#print axioms [^\n]+\n)+',''.join('#print axioms '+x+'\n' for x in cfg['queries']),s,count=1)
        for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:s=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),s)
        s=re.sub(r'#lint in [^\n]+\n','',s).rstrip()+'\n\n'+''.join('#lint in '+m+'\n' for m in mods)
    elif a=='DependencyAudit1':
        for k,v in [('roots',roots),('localModules',cfg['localModules']),('required',edges)]:s=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),s)
        start=s.index(' occur in the ');end=s.index('; DUB17--20 OPEN.',start)
        s=s[:start]+' occur in the proof value closure of the genuine original homogeneous-valued Tate Galois action, its Hecke commutation, inertia triviality and Frobenius polynomial on the actual Tate preimage of each original parabolic class. The actual cyclotomic value, norm-derived relation and combined-diamond fixedness are derived. Coordinate-degree/genus equalities and the comparison range 3<p remain; nonvanishing, finite character transfer, continuity and two-dimensional association are not claimed'+s[end:]
    else:s=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),s)
    s=s.replace('GAMMA ONE INERTIA','GAMMA ONE TWISTED')
    write(new+b+'.lean',s)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
routes=[p/n for n in ['gamma-one-global-coefficient-route-1399.json','gamma-one-cyclotomic-local-reuse-1405.json','gamma-one-parabolic-tate-reuse-1409.json']]
rr=[json.loads(f.read_text(encoding='utf-8')) for f in routes]
reuse=list(dict.fromkeys(routes+[Path(row['path']) for r in rr for row in r['reuse']]))
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain=rr[0]['chain'],reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in reuse],shorterRoute=[r['selected'] for r in rr],assumptionsToDischarge=['Construct a genuine global Galois representation on the original homogeneous-valued Tate dual using the native cyclotomic character and inverse actual Tate action.','Derive its Hecke commutation and actual cyclotomic Frobenius/inertia values from existing valuation-root and original Picard results.','Derive the actual Galois Frobenius polynomial from the norm-derived Tate relation rather than accepting it as an input.','Derive combined-diamond fixedness for the actual Tate preimage of every original parabolic class, then consume that same class in the Galois Frobenius polynomial.'],remaining='The original coordinate-degree and genus equalities remain. The comparison retains 3<p. Neither nonvanishing of restriction nor surjective parabolic transfer is claimed. Finite continuous character realization, exceptional primes, original two-dimensional all-weight arithmetic association, automorphy and literal higher continuation remain. 16/20; DUB-17--20 OPEN.',externalBuild=False,externalImport=False,rootPinsChanged=False,proofLimitsChanged=False)
routefile='source-gamma-one-twisted-audit-route-1412.json';write(routefile,json.dumps(route,indent=2)+'\n')
s=(p/'record_gamma_one_inertia_1368.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-inertia-audit-route-1368',routefile[:-5]),('source-gamma-one-inertia-1',stem),(old,new),('ScratchOwnership1368','ScratchOwnership1412'),('GAMMA ONE INERTIA','GAMMA ONE TWISTED')]:s=s.replace(a,b)
s=s.replace('(8, 16, 35)','(12, 19, 32)').replace('queries=16','queries=19').replace('modules=8','modules=12').replace('linterScopes=8','linterScopes=12')
s=s.replace("text.count('with 16 linters') == 8","text.count('with 16 linters') == 12")
s=s.replace('all 35 required','all 32 required').replace('requiredProofValueEdges=35','requiredProofValueEdges=32').replace('proofEdges=35','proofEdges=32')
ast.parse(s);write('record_gamma_one_twisted_1412.py',s)
s=(p/'audit_gamma_one_inertia_1368.ps1').read_text(encoding='utf-8-sig')
for a,b in [(old,new),('ScratchOwnership1368','ScratchOwnership1412'),('record_gamma_one_inertia_1368','record_gamma_one_twisted_1412')]:s=s.replace(a,b)
write('audit_gamma_one_twisted_1412.ps1',s)
print(json.dumps(dict(modules=len(mods),queries=len(cfg['queries']),proofEdges=len(edges))))
