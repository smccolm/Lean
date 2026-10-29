from pathlib import Path
from datetime import datetime, timezone
import ast, hashlib, json, re
s=Path(__file__).parent
versions=json.loads((s/'gamma-one-diamond-versions-1441.json').read_text(encoding='utf-8'))
mods=list(versions);ths=[];defs=[]
for m in mods:
 code=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',(s/(m+'.lean')).read_text(encoding='utf-8'),flags=re.S))
 ns=re.search(r'^namespace (\S+)',code,re.M)[1]+'.'
 ths += [ns+x for x in re.findall(r'^theorem\s+([\w.\x27]+)',code,re.M)]
 defs += [ns+x for x in re.findall(r'^(?:def|instance)\s+([\w.\x27]+)',code,re.M)]
gn='Dubon2026.SourceFunctionField.GammaOne.';cr=gn+'CoefficientReduction.'
roots=[cr+'exists_gammaOne_diamond_quotient_hecke_frobenius_of_degree_genus_eq',cr+'gammaOne_diamond_relations_hecke_of_degree_genus_eq',gn+'binaryDiamondQuotientGaloisRep_continuous',gn+'binaryDiamondQuotient_finite',gn+'binaryDiamondQuotientGaloisRep_mk']
edges=ths+defs+[
 cr+'exists_gammaOne_tate_frobenius_relation_of_degree_genus_eq',
 'Dubon2026.sourceAbsoluteCyclotomicCharacter_frobenius',
 gn+'binaryArithmeticTateGaloisRep_frobenius_operator',
 'Dubon2026.sourceGammaOneHeckeDiamondCoefficient_square',
 gn+'binaryArithmeticTateGaloisRep_diamond',
 gn+'binaryArithmeticTateDual_finite',
 gn+'binaryArithmeticTateGaloisRep_eventually_one',
 'Representation.quotient','Submodule.mapQ',gn+'arithmeticTateGaloisRep_diamond',
 gn+'binaryTatePrimeOperators',gn+'binaryTateArithmeticFrobeniusOperator']
assert (len(mods),len(ths),len(defs),len(edges))==(8,14,3,29)
assert len(set(edges))==len(edges)
prior=json.loads((s/'source-gamma-one-arithmetic-orbit-2-audit-config.json').read_text(encoding='utf-8'))['localModules']
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,roots=roots,proofEdges=edges,localModules=list(dict.fromkeys(prior+mods)),separatelyAxiomChecked=[],compileEvidence={m:m+'-1441' for m in mods})
def write(n,c):
 t=s/n;assert not t.exists(),t;t.write_text(c,encoding='utf-8')
stem='source-gamma-one-diamond-quotient-1';write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
old,new='SourceGammaOneArithmeticOrbit','SourceGammaOneDiamondQuotient'
for a,b in [('Audit1','Audit1'),('DependencyAudit2','DependencyAudit1'),('ScratchOwnership1430','ScratchOwnership1442')]:
 c=(s/(old+a+'.lean')).read_text(encoding='utf-8')
 c='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n'+c[c.index('\nopen Lean'):]
 if a=='Audit1':
  c=re.sub(r'(#print axioms [^\n]+\n)+',''.join('#print axioms '+x+'\n' for x in cfg['queries']),c,count=1)
  for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:c=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),c)
  c=re.sub(r'#lint in [^\n]+\n','',c).rstrip()+'\n\n'+''.join('#lint in '+m+'\n' for m in mods)
 elif a=='DependencyAudit2':
  for k,v in [('roots',roots),('localModules',cfg['localModules']),('required',edges)]:c=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),c)
  start=c.index(' occur in the ');end=c.index('; DUB17--20 OPEN.',start)
  c=c[:start]+' occur in the proof value closure of the actual diamond quotient Galois action, its finite discrete continuity, its original Hecke stability and its descended Frobenius polynomial. Combined-diamond fixedness, Galois stability and Hecke stability are derived. Coordinate-degree/genus preservation and nonzero original character realization remain'+c[end:]
 else:c=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),c)
 c=c.replace('GAMMA ONE ARITHMETIC ORBIT','GAMMA ONE DIAMOND QUOTIENT')
 write(new+b+'.lean',c)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
r=json.loads((s/'gamma-one-diamond-polynomial-route-1433.json').read_text(encoding='utf-8'))
repo=Path(r'E:\Lean\Riemann Zeta');src=repo/'9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026/Extension/Dubon2026'
reuse=[s/'gamma-one-diamond-polynomial-route-1433.json']+[src/(m+'.lean') for m in r['sources']]+[repo/'.lake/packages/mathlib/Mathlib/RepresentationTheory/Basic.lean',repo/'.lake/packages/mathlib/Mathlib/LinearAlgebra/Quotient/Basic.lean',s/'SourceGammaOneTwistedGaloisDiamond.lean',s/'SourceGammaOneTwistedContinuity.lean',s/'SourceGammaOneFiniteTateDual.lean']
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain=r['scope'],reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in reuse],shorterRoute=r['reuse']+' The Frobenius polynomial and invertible quotient Galois action derive Hecke stability directly, avoiding a separate Hecke/diamond commutation expansion.',assumptionsToDischarge=['Derive the combined-diamond-valued Frobenius relation on every original homogeneous Tate class.','Construct the actual diamond-minus-one quotient and derive Galois stability, finite action and discrete continuity.','Project the actual polynomial, derive original Hecke stability, and descend the genuine operator with its entire-quotient Frobenius identity.'],remaining=r['limits']+' 16/20; DUB-17--20 OPEN.',externalBuild=False,externalImport=False,rootPinsChanged=False,proofLimitsChanged=False)
rf='source-gamma-one-diamond-quotient-audit-route-1442.json';write(rf,json.dumps(route,indent=2)+'\n')
c=(s/'record_gamma_one_arithmetic_orbit_1430b.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-arithmetic-orbit-audit-route-1430',rf[:-5]),('source-gamma-one-arithmetic-orbit-2',stem),(old,new),('DependencyAudit2','DependencyAudit1'),('ScratchOwnership1430','ScratchOwnership1442'),('GAMMA ONE ARITHMETIC ORBIT','GAMMA ONE DIAMOND QUOTIENT')]:c=c.replace(a,b)
c=c.replace('(5, 6, 21)','(8, 17, 29)').replace('queries=6','queries=17').replace('modules=5','modules=8').replace('linterScopes=5','linterScopes=8')
c=c.replace("text.count('with 16 linters') == 5","text.count('with 16 linters') == 8").replace('all 21 required','all 29 required').replace('requiredProofValueEdges=21','requiredProofValueEdges=29').replace('proofEdges=21','proofEdges=29')
ast.parse(c);write('record_gamma_one_diamond_1442.py',c)
c=(s/'audit_gamma_one_arithmetic_orbit_1430b.ps1').read_text(encoding='utf-8-sig')
for a,b in [(old,new),('DependencyAudit2','DependencyAudit1'),('ScratchOwnership1430','ScratchOwnership1442'),('record_gamma_one_arithmetic_orbit_1430b','record_gamma_one_diamond_1442')]:c=c.replace(a,b)
c=c.replace("$names=@(","$names=@('SourceGammaOneDiamondQuotientAudit1',")
write('audit_gamma_one_diamond_1442.ps1',c)
print(json.dumps(dict(modules=len(mods),queries=len(cfg['queries']),proofEdges=len(edges))))
