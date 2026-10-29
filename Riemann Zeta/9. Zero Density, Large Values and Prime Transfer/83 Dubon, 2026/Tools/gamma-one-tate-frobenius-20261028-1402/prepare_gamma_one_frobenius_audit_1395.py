from pathlib import Path
from datetime import datetime, timezone
import ast, hashlib, json, re
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
versions=json.loads((p/'gamma-one-frobenius-versions-1394.json').read_text(encoding='utf-8'))
mods=list(versions);ths=[];defs=[]
for m in mods:
    code=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',(p/(m+'.lean')).read_text(encoding='utf-8'),flags=re.S))
    ns=re.search(r'^namespace (\S+)',code,re.M)[1]+'.'
    ths += [ns+x for x in re.findall(r'^theorem\s+([\w.\x27]+)',code,re.M)]
    defs += [ns+x for x in re.findall(r'^def\s+([\w.\x27]+)',code,re.M)]
gn='Dubon2026.SourceFunctionField.GammaOne.';cn=gn+'CoefficientReduction.';sc='Dubon2026.SourceCurve.'
roots=[cn+'exists_gammaOne_tate_frobenius_relation_of_degree_genus_eq']
edges=ths+defs+[
    sc+'Divisor.geometricCorrespondence_order',
    sc+'RegularProlongation.exists_smul_mem',
    sc+'RegularProlongation.isUnit_of_residue_ne_zero',
    sc+'Pic0.mk_mem_torsion_iff',
    gn+'ConstantField.principal_smul',
    cn+'geometricFrobenius_coe',cn+'geometricFrobenius_place_order',
    cn+'geometricFrobeniusPlace_eq_decomposition',cn+'decompositionResiduePlace_ord_action',
    cn+'residueImage_place_residue_bijective',sc+'fieldDivisorEquiv',cn+'arithmeticDiamondGauss',
    cn+'exists_gammaOne_hecke_gauss_norm_reduction_of_degree_eq',
    cn+'gammaOne_pic0_eq_zero_of_torsion_of_degree_genus_eq',
    cn+'exists_gammaOne_reduction_decomposition_equivariant_of_degree_genus_eq',
    gn+'arithmeticDiamondPicard_galois',gn+'gamma1ArithmeticPicardRep_torsion',
    gn+'arithmeticDiamondPicard_torsion','Dubon2026.TateModule.torsion','Dubon2026.TateModule.tateMap']
assert (len(mods),len(ths),len(defs),len(edges))==(15,26,3,49)
assert len(set(edges))==len(edges)
prior=[]
for stem in ['source-gamma-one-specialization-1','source-gamma-one-kummer-1','source-gamma-one-gauss-norm-1','source-gamma-one-inertia-1']:
    prior += json.loads((p/(stem+'-audit-config.json')).read_text(encoding='utf-8'))['localModules']
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,roots=roots,proofEdges=edges,localModules=list(dict.fromkeys(prior+mods)),separatelyAxiomChecked=[],compileEvidence={m:m+'-1394' for m in mods})
def write(n,s):
    f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
stem='source-gamma-one-frobenius-1'
write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
old,new='SourceGammaOneInertia','SourceGammaOneFrobenius'
for a,b in [('Audit1','Audit1'),('DependencyAudit1','DependencyAudit1'),('ScratchOwnership1368','ScratchOwnership1395')]:
    s=(p/(old+a+'.lean')).read_text(encoding='utf-8')
    s='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n'+s[s.index('\nopen Lean'):]
    if a=='Audit1':
        s=re.sub(r'(#print axioms [^\n]+\n)+',''.join('#print axioms '+x+'\n' for x in cfg['queries']),s,count=1)
        for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:s=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),s)
        s=re.sub(r'#lint in [^\n]+\n','',s).rstrip()+'\n\n'+''.join('#lint in '+m+'\n' for m in mods)
    elif a=='DependencyAudit1':
        for k,v in [('roots',roots),('localModules',cfg['localModules']),('required',edges)]:s=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),s)
        start=s.index(' occur in the ');end=s.index('; DUB17--20 OPEN.',start)
        s=s[:start]+' occur in the proof value closure of the exact original Gamma1 Tate relation H*F = F*F*D + p with Picard diamond label p. The actual norm, divisor cancellation, Picard quotient descent, equivariant specialization and invertible-torsion injectivity are consumed. Coordinate-degree and genus preservation remain; no untwisted relation, global all-weight Galois representation, or acceptance gate is claimed'+s[end:]
    else:s=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),s)
    s=s.replace('GAMMA ONE INERTIA','GAMMA ONE FROBENIUS')
    write(new+b+'.lean',s)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
rr=json.loads((p/'gamma-one-frobenius-divisor-route-1369.json').read_text(encoding='utf-8'))
reuse=[p/'gamma-one-frobenius-divisor-route-1369.json',p/'gamma-one-arithmetic-frobenius-route-1393.json']+[Path(row['path']) for row in rr['reuse']]
reuse += [p/(x+'-scratch-receipt.json') for x in ['source-gamma-one-specialization-1','source-gamma-one-kummer-1','source-gamma-one-gauss-norm-1','source-gamma-one-inertia-1']]
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain=rr['chain'],reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in reuse],shorterRoute=rr['selected'],assumptionsToDischarge=['The actual original Gamma1 Hecke divisor correspondence equals the divisor of the literal alpha norm of beta.','The actual residue norm gives coefficient-Frobenius diamond plus p times inverse coefficient Frobenius on integral principal divisors.','Primitive constant normalization and torsion-free integer-divisor cancellation extend the equality to every finite Picard torsion class without an upper-correspondence good-reduction model.','The same equivariant specialization and invertible-torsion injection transport the identity to original Picard torsion and actual Tate sequences: H*F = F*F*D + p, with Picard diamond label p.'],remaining='Actual original Gamma1 coordinate-degree equality and genus preservation remain. The derived twisted coefficient relation does not close the previously conditional differently normalized relation. Its inverse-action coefficient normalization, global Galois realization, parabolic and coefficient/character realization, all-weight two-dimensional association, automorphy and literal higher continuation remain. 16/20; DUB-17--20 OPEN.',externalBuild=False,externalImport=False,rootPinsChanged=False,proofLimitsChanged=False)
routefile='source-gamma-one-frobenius-audit-route-1395.json';write(routefile,json.dumps(route,indent=2)+'\n')
s=(p/'record_gamma_one_inertia_1368.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-inertia-audit-route-1368',routefile[:-5]),('source-gamma-one-inertia-1',stem),(old,new),('ScratchOwnership1368','ScratchOwnership1395'),('GAMMA ONE INERTIA','GAMMA ONE FROBENIUS')]:s=s.replace(a,b)
s=s.replace('(8, 16, 35)','(15, 29, 49)').replace('queries=16','queries=29').replace('modules=8','modules=15').replace('linterScopes=8','linterScopes=15')
s=s.replace("text.count('with 16 linters') == 8","text.count('with 16 linters') == 15")
s=s.replace('all 35 required','all 49 required').replace('requiredProofValueEdges=35','requiredProofValueEdges=49').replace('proofEdges=35','proofEdges=49')
ast.parse(s);write('record_gamma_one_frobenius_1395.py',s)
s=(p/'audit_gamma_one_inertia_1368.ps1').read_text(encoding='utf-8-sig')
for a,b in [(old,new),('ScratchOwnership1368','ScratchOwnership1395'),('record_gamma_one_inertia_1368','record_gamma_one_frobenius_1395')]:s=s.replace(a,b)
write('audit_gamma_one_frobenius_1395.ps1',s)
print(json.dumps(dict(modules=len(mods),queries=len(cfg['queries']),proofEdges=len(edges))))
