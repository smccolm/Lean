from pathlib import Path
from datetime import datetime, timezone
import ast, hashlib, json, re
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
versions=json.loads((p/'gamma-one-arithmetic-versions-1396.json').read_text(encoding='utf-8'))
mods=list(versions);ths=[];defs=[]
for m in mods:
    code=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',(p/(m+'.lean')).read_text(encoding='utf-8'),flags=re.S))
    ns=re.search(r'^namespace (\S+)',code,re.M)[1]+'.'
    ths += [ns+x for x in re.findall(r'^theorem\s+([\w.\x27]+)',code,re.M)]
    defs += [ns+x for x in re.findall(r'^def\s+([\w.\x27]+)',code,re.M)]
gn='Dubon2026.SourceFunctionField.GammaOne.';cn=gn+'CoefficientReduction.'
roots=[cn+'exists_gammaOne_arithmetic_frobenius_quadratic_of_degree_genus_eq']
edges=ths+['Dubon2026.sourceGammaOneHeckeDiamondCoefficient_square','Dubon2026.homogeneousHeckeDiamond_square','Dubon2026.binaryHomogeneousMonomialBasis_diagonal_ring',gn+'arithmeticTateGaloisRep_diamond',cn+'exists_gammaOne_tate_frobenius_relation_of_degree_genus_eq',cn+'exists_gammaOne_picard_frobenius_relation_of_degree_genus_eq',cn+'exists_gammaOne_hecke_reduction_torsion_picard_of_degree_eq',cn+'exists_gammaOne_hecke_gauss_norm_reduction_of_degree_eq',cn+'gammaOne_pic0_eq_zero_of_torsion_of_degree_genus_eq',gn+'heckeDivisor_principal_norm','Dubon2026.TateModule.tateMap_diamond_quadratic',gn+'arithmeticDiamondTate_galois']
assert (len(mods),len(ths),len(defs),len(edges))==(3,3,1,15)
assert len(set(edges))==len(edges)
prior=json.loads((p/'source-gamma-one-frobenius-1-audit-config.json').read_text(encoding='utf-8'))['localModules']
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,roots=roots,proofEdges=edges,localModules=list(dict.fromkeys(prior+mods)),separatelyAxiomChecked=defs,compileEvidence={m:m+'-1396' for m in mods})
def write(n,s):
    f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
stem='source-gamma-one-arithmetic-1';write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
old,new='SourceGammaOneInertia','SourceGammaOneArithmetic'
for a,b in [('Audit1','Audit1'),('DependencyAudit1','DependencyAudit1'),('ScratchOwnership1368','ScratchOwnership1397')]:
    s=(p/(old+a+'.lean')).read_text(encoding='utf-8')
    s='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n'+s[s.index('\nopen Lean'):]
    if a=='Audit1':
        s=re.sub(r'(#print axioms [^\n]+\n)+',''.join('#print axioms '+x+'\n' for x in cfg['queries']),s,count=1)
        for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:s=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),s)
        s=re.sub(r'#lint in [^\n]+\n','',s).rstrip()+'\n\n'+''.join('#lint in '+m+'\n' for m in mods)
    elif a=='DependencyAudit1':
        for k,v in [('roots',roots),('localModules',cfg['localModules']),('required',edges)]:s=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),s)
        start=s.index(' occur in the ');end=s.index('; DUB17--20 OPEN.',start)
        s=s[:start]+' occur in the proof value closure of the original all-weight inverse-action Frobenius polynomial Y*Hdual = Y*Y + ell^(w+1), where Y uses ell times the native Hecke coefficient matrix and inverse actual Tate Galois action. The literal twisted Picard relation is derived from the norm and specialization, and native homogeneous coefficients give the weight. Coordinate-degree, genus preservation and combined-diamond fixedness remain explicit; the global Galois representation and character realization are not claimed'+s[end:]
    else:s=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),s)
    s=s.replace('GAMMA ONE INERTIA','GAMMA ONE ARITHMETIC')
    write(new+b+'.lean',s)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
rr=json.loads((p/'gamma-one-arithmetic-frobenius-route-1393.json').read_text(encoding='utf-8'))
reuse=[p/'gamma-one-arithmetic-frobenius-route-1393.json']+[Path(row['path']) for row in rr['reuse']]
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain=rr['chain'],reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in reuse],shorterRoute=rr['selected'],assumptionsToDischarge=['The literal original twisted Picard/Tate relation yields a scalar weight polynomial for the inverse coefficient action with the existing homogeneous Hecke matrix and one cyclotomic factor.','The original all-weight coefficient-valued Tate dual satisfies Y*Hdual = Y^2 + ell^(w+1) on its actual combined-diamond fixed part.','The final original-object consumer derives the required Picard/Tate relation from the actual norm and geometric specialization; it does not accept a Frobenius quadratic as a hypothesis.'],remaining=rr['remaining'],externalBuild=False,externalImport=False,rootPinsChanged=False,proofLimitsChanged=False)
routefile='source-gamma-one-arithmetic-audit-route-1397.json';write(routefile,json.dumps(route,indent=2)+'\n')
s=(p/'record_gamma_one_inertia_1368.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-inertia-audit-route-1368',routefile[:-5]),('source-gamma-one-inertia-1',stem),(old,new),('ScratchOwnership1368','ScratchOwnership1397'),('GAMMA ONE INERTIA','GAMMA ONE ARITHMETIC')]:s=s.replace(a,b)
s=s.replace('(8, 16, 35)','(3, 4, 15)').replace('queries=16','queries=4').replace('modules=8','modules=3').replace('linterScopes=8','linterScopes=3')
s=s.replace("text.count('with 16 linters') == 8","text.count('with 16 linters') == 3")
s=s.replace('all 35 required','all 15 required').replace('requiredProofValueEdges=35','requiredProofValueEdges=15').replace('proofEdges=35','proofEdges=15')
ast.parse(s);write('record_gamma_one_arithmetic_1397.py',s)
s=(p/'audit_gamma_one_inertia_1368.ps1').read_text(encoding='utf-8-sig')
for a,b in [(old,new),('ScratchOwnership1368','ScratchOwnership1397'),('record_gamma_one_inertia_1368','record_gamma_one_arithmetic_1397')]:s=s.replace(a,b)
write('audit_gamma_one_arithmetic_1397.ps1',s)
print(json.dumps(dict(modules=len(mods),queries=len(cfg['queries']),proofEdges=len(edges))))
