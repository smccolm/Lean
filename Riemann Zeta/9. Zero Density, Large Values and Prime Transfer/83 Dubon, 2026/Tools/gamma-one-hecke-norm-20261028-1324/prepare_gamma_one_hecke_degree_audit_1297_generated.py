from pathlib import Path
from datetime import datetime,timezone
import ast,hashlib,json,re
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
mods=['SourceGammaOnePrimeHeckeIndex','SourceGammaOneSignedHeckeIndex','SourceGammaOneHeckeCoordinateDegree','SourceGammaOneHeckePrimeDegree']
ev=dict(zip(mods,['1293b','1294a','1295a','1296d'],strict=True))
cn='Dubon2026.SourceFunctionField.GammaOne.'
ths=[];defs=[]
for m in mods:
 assert (p/(m+ev[m]+'.exit')).read_text().strip()=='0'
 assert (p/(m+ev[m]+'.log')).stat().st_size==0
 code=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',(p/(m+'.lean')).read_text(encoding='utf-8'),flags=re.S))
 ths += [cn+x for x in re.findall(r"^theorem\s+([\w.']+)",code,re.M)]
 defs += [cn+x for x in re.findall(r"^def\s+([\w.']+)",code,re.M)]
roots=[cn+'heckeAlpha_finrank']
edges=ths+defs+[cn+x for x in ['finrank_over_j_eq_index',
 'HeckeFiberOrbits.finrank_over_j_eq_index','finite_rational_coordinate',
 'gamma1_hecke_baseChange_le']]+[
 'Dubon2026.SourceFunctionField.DegreeTransport.relfinrank_eq_of_finite',
 'Dubon2026.sourcePrincipalReduction_surjective',
 'Dubon2026.SourceLevelProjective.gamma0_index',
 'Dubon2026.SourceLevelProjective.dedekindPsi_prime']
prev=json.loads((p/'source-gamma-one-residue-compatibility-1-audit-config.json').read_text(encoding='utf-8'))
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,roots=roots,
 proofEdges=edges,localModules=mods,separatelyAxiomChecked=[],
 compileEvidence={m:m+ev[m] for m in mods})
assert(len(ths),len(defs),len(edges))==(14,0,22)
def write(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
stem='source-gamma-one-hecke-degree-1'
write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
old='SourceGammaOneResidueCompatibility';new='SourceGammaOneHeckeDegree'
for a,b in [('Audit1','Audit1'),('DependencyAudit1','DependencyAudit1'),
 ('ScratchOwnership1285','ScratchOwnership1297')]:
 s=(p/(old+a+'.lean')).read_text(encoding='utf-8')
 s='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n'+s[s.index('\nopen Lean'):]
 if a=='Audit1':
  s=re.sub(r'(#print axioms [^\n]+\n)+',''.join('#print axioms '+x+'\n' for x in cfg['queries']),s,count=1)
  for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:
   s=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),s)
  s=re.sub(r'#lint in [^\n]+\n','',s).rstrip()+'\n\n'+''.join('#lint in '+m+'\n' for m in mods)
 elif a=='DependencyAudit1':
  for k,v in [('roots',roots),('localModules',cfg['localModules']),('required',edges)]:
   s=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),s)
  start=s.index(' occur in the ');end=s.index('; DUB17--20 OPEN.',start)
  s=s[:start]+' occur in the proof value closure of the actual Gamma1 alpha inclusion degree p+1, consuming native coprime principal lifting, signed subgroup indices, complex j-fiber degrees and Laurent coefficient-field degree transport. The explicit embedding census and norm identity, residue degree preservation and original Picard specialization remain unresolved'+s[end:]
 else:
  s=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),s)
 s=s.replace('GAMMA ONE RESIDUE COMPATIBILITY','GAMMA ONE HECKE DEGREE')
 write(new+b+'.lean',s)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
reuse=[r/'Extension/Dubon2026'/(m+'.lean') for m in [
 'SourcePrincipalCoprimeReduction','SourceLevelProjectiveCosets','SourceLevelIndexFormula',
 'SourceLevelPsiPrimeStep','SourceGammaOnePlusMinus','SourceGammaOneExactRamification',
 'SourceGammaOneHeckeJDegree','SourceGammaOneDegreeBaseChange','SourceLaurentDegreeTransport',
 'SourceOriginalHeckePrimeDegree','SourceOriginalHeckeEmbeddingCensus',
 'SourceGammaOneHeckeFieldFinite']]
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),
 chain='DUB17 Theorem 2.6 / DUB18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> original Gamma1 geometric Tate Frobenius -> actual original Hecke norm reduction -> complete original embedding census -> exact original alpha inclusion degree p+1.',
 reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in reuse],
 shorterRoute='Existing principal-level lifting gives surjectivity modulo a coprime prime for the actual Gamma1 group. Pulling back the native Borel identifies the literal lower correspondence subgroup. The proved Gamma0 index gives p+1, also after adjoining central negative identity. Existing complex j-fiber degrees and Laurent base-change degree transport then identify the two original coordinate degrees. Native relative-degree multiplicativity and the signed index ratio prove the actual alpha inclusion degree. Explicit Algebra.toModule selects the actual inclusion scalar action and avoids typeclass normalization without raising limits. No new projective-line count, modular polynomial or Atkin hypothesis is introduced.',
 assumptionsToDischarge=[
 'At every nonzero level M and prime p coprime to M, the original Gamma1 lower Hecke subgroup has relative index p+1, with the same exact relative index after the required central-sign enlargement.',
 'The j-coordinate degrees of both original fields equal their signed subgroup indices over every characteristic-zero coefficient field.',
 'The original alpha field inclusion has degree p+1 under its actual scalar action, removing the dimension input for a complete p+1 embedding census.'],
 remaining='The exact field degree does not construct the explicit conjugate embeddings or prove their values on the second Hecke map. The original Gamma1 norm identity with its diamond convention, residue degree equality, genus preservation, original-to-residue place/Picard specialization and torsion injectivity remain. Consequently the original geometric Tate quadratic/inertia, parabolic character realization, exceptional primes, coefficient-field realization, original all-weight characteristic-zero association, automorphy and literal higher continuation remain. 16/20; DUB17--20 OPEN.',
 externalBuild=False,externalImport=False,rootPinsChanged=False)
routefile='source-gamma-one-hecke-degree-audit-route-1297.json'
write(routefile,json.dumps(route,indent=2)+'\n')
s=(p/'record_gamma_one_residue_compatibility_1285.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-residue-compatibility-audit-route-1285',routefile[:-5]),
 ('source-gamma-one-residue-compatibility-1',stem),(old,new),
 ('ScratchOwnership1285','ScratchOwnership1297'),
 ('GAMMA ONE RESIDUE COMPATIBILITY','GAMMA ONE HECKE DEGREE')]:s=s.replace(a,b)
s=s.replace('(6, 28, 39)','(4, 14, 22)').replace('== 6','== 4')
s=s.replace('linterScopes=6','linterScopes=4').replace('modules=6','modules=4')
s=s.replace('all 39 required','all 22 required').replace('requiredProofValueEdges=39','requiredProofValueEdges=22')
s=s.replace('proofEdges=39','proofEdges=22').replace('queries=28','queries=14')
ast.parse(s);write('record_gamma_one_hecke_degree_1297.py',s)
s=(p/'audit_gamma_one_residue_compatibility_1285.ps1').read_text(encoding='utf-8')
for a,b in [(old,new),('ScratchOwnership1285','ScratchOwnership1297'),
 ('record_gamma_one_residue_compatibility_1285','record_gamma_one_hecke_degree_1297')]:s=s.replace(a,b)
write('audit_gamma_one_hecke_degree_1297.ps1',s)
print(json.dumps(dict(modules=4,queries=14,edges=22)))
