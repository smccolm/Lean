from pathlib import Path
from datetime import datetime, timezone
import ast, hashlib, json, re
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
versions=json.loads((p/'gamma-one-inertia-versions-1367.json').read_text(encoding='utf-8'))
mods=list(versions);ths=[]
for m in mods:
 code=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',(p/(m+'.lean')).read_text(encoding='utf-8'),flags=re.S))
 ns=re.search(r'^namespace (\S+)',code,re.M)[1]+'.'
 ths += [ns+x for x in re.findall(r'^theorem\s+([\w.\x27]+)',code,re.M)]
 assert not re.findall(r'^def\s+',code,re.M)
gn='Dubon2026.SourceFunctionField.GammaOne.';cn=gn+'CoefficientReduction.'
sc='Dubon2026.SourceCurve.'
roots=[cn+'gammaOne_arithmeticTateGaloisRep_eq_one_of_inertia_of_degree_genus_eq']
edges=ths+[
 sc+'RegularProlongation.integral_charts_lift_of_degree_genus_eq',
 sc+'RegularProlongation.exists_principal_divisor_reduction_map_with_charts',
 sc+'ConstantReduction.ofPlaceMap',
 cn+'gammaOne_pic0_eq_zero_of_torsion_of_degree_genus_eq',
 cn+'gammaOne_pic0_eq_zero_of_prime_torsion_of_degree_genus_eq',
 cn+'gammaOne_exists_power_of_residue_power_of_degree_genus_eq',
 gn+'gammaOne_kummer_genus_sub_one',
 sc+'RegularProlongation.JointChartAssembly.genus_inequality_of_separating_residue_coordinate',
 cn+'regularProlongation',
 cn+'decompositionGaussHom',
 cn+'decompositionGaussHom_residueToImage',
 cn+'decompositionResidueAut_constants',
 cn+'decompositionResiduePlace_eq_self_of_inertia',
 cn+'specializationResidueAlgebra',
 gn+'arithmeticRingAut',gn+'arithmeticPicard',gn+'gamma1ArithmeticPicardRep',
 gn+'arithmeticTateGaloisRep','Dubon2026.TateModule.torsion']
assert (len(mods),len(ths),len(edges))==(8,16,35)
assert len(set(edges))==len(edges)
prior=[]
for stem in ['source-gamma-one-specialization-1','source-gamma-one-kummer-1']:
 prior += json.loads((p/(stem+'-audit-config.json')).read_text(encoding='utf-8'))['modules']
cfg=dict(modules=mods,theorems=ths,constructions=[],queries=ths,roots=roots,proofEdges=edges,
 localModules=prior+mods,separatelyAxiomChecked=[],compileEvidence={m:m+'-1367' for m in mods})
def write(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
stem='source-gamma-one-inertia-1'
write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
old,new='SourceGammaOneGaussNorm','SourceGammaOneInertia'
for a,b in [('Audit1','Audit1'),('DependencyAudit1','DependencyAudit1'),('ScratchOwnership1357','ScratchOwnership1368')]:
 s=(p/(old+a+'.lean')).read_text(encoding='utf-8')
 s='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n'+s[s.index('\nopen Lean'):]
 if a=='Audit1':
  s=re.sub(r'(#print axioms [^\n]+\n)+',''.join('#print axioms '+x+'\n' for x in ths),s,count=1)
  for k,v in [('modules',mods),('theorems',ths),('constructions',[])]:
   s=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),s)
  s=re.sub(r'#lint in [^\n]+\n','',s).rstrip()+'\n\n'+''.join('#lint in '+m+'\n' for m in mods)
 elif a=='DependencyAudit1':
  for k,v in [('roots',roots),('localModules',cfg['localModules']),('required',edges)]:
   s=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),s)
  start=s.index(' occur in the ');end=s.index('; DUB17--20 OPEN.',start)
  s=s[:start]+' occur in the proof value closure of inertia triviality on the actual original Gamma1 Tate representation. Exact chart equivariance, specialization-place inertia invariance and Picard invertible-torsion injectivity are derived. Coordinate-degree and genus preservation remain explicit; the two-dimensional arithmetic association and Frobenius relation are not claimed'+s[end:]
 else:s=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),s)
 s=s.replace('GAMMA ONE GAUSS NORM','GAMMA ONE INERTIA')
 write(new+b+'.lean',s)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
reuse=[p/'gamma-one-inertia-route-1359.json',p/'source-gamma-one-specialization-1-scratch-receipt.json',p/'source-gamma-one-kummer-1-scratch-receipt.json']
rr=json.loads((p/'gamma-one-inertia-route-1359.json').read_text(encoding='utf-8'))
reuse += [Path(row['path']) for row in rr['reuse']]
reuse += [r/'Extension/Dubon2026'/n for n in ['SourceGammaOneHeckeArithmetic.lean','SourceGammaOneArithmeticTateOperators.lean','SourceTateFunctor.lean','SourceOriginalTateInertia.lean']]
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain=rr['chain'],reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in reuse],shorterRoute=rr['selected'],assumptionsToDischarge=['The same actual original Gamma1 constant reduction is decomposition-equivariant on places and injective on every invertible Picard torsion group.','Arithmetic inertia fixes the actual specialization of places, hence Picard classes after reduction.','Coordinate-degree and genus preservation therefore imply inertia triviality on the actual original Gamma1 Picard torsion and its Tate representation, for every invertible Tate prime.'],remaining='Actual original Gamma1 coordinate-degree equality and genus preservation remain. Hecke norm/place/Picard compatibility and the geometric Frobenius characteristic relation remain, as do parabolic and coefficient realization, original all-weight two-dimensional association, automorphy and literal higher continuation. 16/20; DUB-17--20 OPEN.',externalBuild=False,externalImport=False,rootPinsChanged=False,proofLimitsChanged=False)
routefile='source-gamma-one-inertia-audit-route-1368.json'
write(routefile,json.dumps(route,indent=2)+'\n')
s=(p/'record_gamma_one_gauss_norm_1357.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-gauss-norm-audit-route-1357',routefile[:-5]),('source-gamma-one-gauss-norm-1',stem),(old,new),('ScratchOwnership1357','ScratchOwnership1368'),('GAMMA ONE GAUSS NORM','GAMMA ONE INERTIA')]:s=s.replace(a,b)
s=s.replace('(6, 8, 25)','(8, 16, 35)').replace('queries=8','queries=16').replace('modules=6','modules=8').replace('linterScopes=6','linterScopes=8')
s=s.replace("text.count('with 16 linters') == 6","text.count('with 16 linters') == 8")
s=s.replace('all 25 required','all 35 required').replace('requiredProofValueEdges=25','requiredProofValueEdges=35').replace('proofEdges=25','proofEdges=35')
ast.parse(s);write('record_gamma_one_inertia_1368.py',s)
s=(p/'audit_gamma_one_gauss_norm_1357.ps1').read_text(encoding='utf-8-sig')
for a,b in [(old,new),('ScratchOwnership1357','ScratchOwnership1368'),('record_gamma_one_gauss_norm_1357','record_gamma_one_inertia_1368')]:s=s.replace(a,b)
write('audit_gamma_one_inertia_1368.ps1',s)
print(json.dumps(dict(modules=len(mods),queries=len(ths),proofEdges=len(edges))))
