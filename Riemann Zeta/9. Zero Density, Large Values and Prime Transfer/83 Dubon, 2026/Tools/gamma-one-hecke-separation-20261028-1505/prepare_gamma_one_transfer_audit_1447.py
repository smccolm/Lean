from pathlib import Path
from datetime import datetime, timezone
import ast,hashlib,json,re
s=Path(__file__).parent
versions=json.loads((s/'gamma-one-transfer-versions-1446.json').read_text(encoding='utf-8'))
mods=list(versions);ths=[];defs=[]
for m in mods:
 code=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',(s/(m+'.lean')).read_text(encoding='utf-8'),flags=re.S))
 ns=re.search(r'^namespace (\S+)',code,re.M)[1]+'.'
 ths += [ns+x for x in re.findall(r'^theorem\s+([\w.\x27]+)',code,re.M)]
 defs += [ns+x for x in re.findall(r'^(?:def|instance)\s+([\w.\x27]+)',code,re.M)]
gn='Dubon2026.SourceFunctionField.GammaOne.';cr=gn+'CoefficientReduction.'
roots=[gn+'binaryDiamondQuotient_nontrivial_of_transfer_away',cr+'exists_gammaOne_diamond_quotient_original_transfer_frobenius']
edges=ths+defs+['Dubon2026.sourceGammaOneConstantH1Transfer_diamond','Dubon2026.sourceGammaOneConstantH1Transfer_hecke',gn+'binaryTateH1Equiv_diamond',gn+'binaryTateH1Equiv_prime',gn+'binaryTateH1Equiv','Dubon2026.sourcePrimitiveParabolicH1AdicQuotientCharacter_zero','Dubon2026.sourcePrimitiveParabolicH1AdicQuotientCharacter_zero_away','Ideal.pow_le_self','Ideal.Quotient.zero_eq_one_iff','Submodule.liftQ',cr+'exists_gammaOne_diamond_quotient_hecke_frobenius_of_degree_genus_eq',gn+'binaryTateDiamondRelations']
assert (len(mods),len(ths),len(defs),len(edges))==(4,8,2,22)
assert len(set(edges))==len(edges)
prior=json.loads((s/'source-gamma-one-diamond-quotient-1-audit-config.json').read_text(encoding='utf-8'))['localModules']
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,roots=roots,proofEdges=edges,localModules=list(dict.fromkeys(prior+mods)),separatelyAxiomChecked=[],compileEvidence={m:m+'-1446' for m in mods})
def write(n,c):
 t=s/n;assert not t.exists(),t;t.write_text(c,encoding='utf-8')
stem='source-gamma-one-diamond-transfer-1';write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
old,new='SourceGammaOneArithmeticOrbit','SourceGammaOneDiamondTransfer'
for a,b in [('Audit1','Audit1'),('DependencyAudit2','DependencyAudit1'),('ScratchOwnership1430','ScratchOwnership1447')]:
 c=(s/(old+a+'.lean')).read_text(encoding='utf-8')
 c='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n'+c[c.index('\nopen Lean'):]
 if a=='Audit1':
  c=re.sub(r'(#print axioms [^\n]+\n)+',''.join('#print axioms '+x+'\n' for x in cfg['queries']),c,count=1)
  for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:c=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),c)
  c=re.sub(r'#lint in [^\n]+\n','',c).rstrip()+'\n\n'+''.join('#lint in '+m+'\n' for m in mods)
 elif a=='DependencyAudit2':
  for k,v in [('roots',roots),('localModules',cfg['localModules']),('required',edges)]:c=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),c)
  start=c.index(' occur in the ');end=c.index('; DUB17--20 OPEN.',start)
  c=c[:start]+' occur in the proof value closure of the original transfer on the actual diamond quotient, its geometric Frobenius/Hecke square, and nonvanishing derived from the original unital character. No transfer compatibility, quotient preimage or nonzero vector is separately assumed. Original parabolic transfer, the existing prime restrictions and degree/genus preservation remain explicit where used'+c[end:]
 else:c=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),c)
 c=c.replace('GAMMA ONE ARITHMETIC ORBIT','GAMMA ONE DIAMOND TRANSFER')
 write(new+b+'.lean',c)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
routefiles=[s/'gamma-one-tate-transfer-route-1443.json',s/'gamma-one-diamond-nonzero-route-1445.json']
rr=[json.loads(f.read_text(encoding='utf-8')) for f in routefiles]
reuse=list(dict.fromkeys(routefiles+[Path(row['path']) for r in rr for row in r['reuse']]))
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain=rr[0]['chain'],reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in reuse],shorterRoute=[r['selected'] for r in rr],assumptionsToDischarge=['Compose the actual Tate/parabolic-H1 comparison and original transfer; derive its diamond invariance and original Hecke compatibility.','Derive factorization through the genuine diamond quotient and its exact parabolic preimages from the original separately identified lifting input.','Derive nonzero quotient from the original unital adic character and parabolic congruence, away from the fixed exceptional integer.','Consume the geometric quotient Hecke/Frobenius witness to derive its original transfer square; no operator descent or square is supplied.'],remaining='Original parabolic-preimage theorem remains open; transfer uses 3<p and nonvanishing also excludes the original fixed exceptional integer. Degree/genus preservation remains in the geometric Hecke/Frobenius witness, not in the independent transfer/nonvanishing deductions. Two-dimensional original character realization, all-weight characteristic-zero association and all remaining gates are open. 16/20; DUB-17--20 OPEN.',externalBuild=False,externalImport=False,rootPinsChanged=False,proofLimitsChanged=False)
rf='source-gamma-one-diamond-transfer-audit-route-1447.json';write(rf,json.dumps(route,indent=2)+'\n')
c=(s/'record_gamma_one_arithmetic_orbit_1430b.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-arithmetic-orbit-audit-route-1430',rf[:-5]),('source-gamma-one-arithmetic-orbit-2',stem),(old,new),('DependencyAudit2','DependencyAudit1'),('ScratchOwnership1430','ScratchOwnership1447'),('GAMMA ONE ARITHMETIC ORBIT','GAMMA ONE DIAMOND TRANSFER')]:c=c.replace(a,b)
c=c.replace('(5, 6, 21)','(4, 10, 22)').replace('queries=6','queries=10').replace('modules=5','modules=4').replace('linterScopes=5','linterScopes=4')
c=c.replace("text.count('with 16 linters') == 5","text.count('with 16 linters') == 4").replace('all 21 required','all 22 required').replace('requiredProofValueEdges=21','requiredProofValueEdges=22').replace('proofEdges=21','proofEdges=22')
ast.parse(c);write('record_gamma_one_transfer_1447.py',c)
c=(s/'audit_gamma_one_arithmetic_orbit_1430b.ps1').read_text(encoding='utf-8-sig')
for a,b in [(old,new),('DependencyAudit2','DependencyAudit1'),('ScratchOwnership1430','ScratchOwnership1447'),('record_gamma_one_arithmetic_orbit_1430b','record_gamma_one_transfer_1447')]:c=c.replace(a,b)
c=c.replace("$names=@(","$names=@('SourceGammaOneDiamondTransferAudit1',")
write('audit_gamma_one_transfer_1447.ps1',c)
print(json.dumps(dict(modules=len(mods),queries=len(cfg['queries']),proofEdges=len(edges))))
