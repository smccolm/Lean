from pathlib import Path
from datetime import datetime,timezone
import ast,hashlib,json,re
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
mods=['SourceGammaOneCoprimeGeneration','SourceGammaOneAdjacentJRatio',
 'SourceGammaOneRealizationRestriction','SourceGammaOneAdjacentJNonmembership',
 'SourceGammaOneAdjacentJGeneration','SourceGammaOneAdjacentJPolynomial',
 'SourceGammaOneAdjacentJEmbedding','SourceGammaOneAdjacentJPreservation',
 'SourceGammaOneAdjacentJAutomorphism','SourceGammaOneAdjacentJCoefficients',
 'SourceGammaOneHeckeNormEmbeddings','SourceGammaOneHeckeEmbeddingCensus',
 'SourceGammaOneHeckeNormProduct']
ev=dict(zip(mods,['1298a','1299b','1300a','1301b','1302a','1303b','1304a',
 '1305d','1306b','1307a','1308b','1309a','1310a'],strict=True))
ths=[];defs=[]
for m in mods:
 assert (p/(m+ev[m]+'.exit')).read_text().strip()=='0',m
 assert (p/(m+ev[m]+'.log')).stat().st_size==0,m
 code=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',(p/(m+'.lean')).read_text(encoding='utf-8'),flags=re.S))
 ns=re.search(r'^namespace (\S+)',code,re.M)[1]+'.'
 ths += [ns+x for x in re.findall(r"^theorem\s+([\w.']+)",code,re.M)]
 defs += [ns+x for x in re.findall(r"^def\s+([\w.']+)",code,re.M)]
cn='Dubon2026.SourceFunctionField.GammaOne.'
roots=[cn+'HeckeNorm.exists_gammaOne_hecke_norm_product']
degree=json.loads((p/'source-gamma-one-hecke-degree-1-audit-config.json').read_text(encoding='utf-8'))
edges=ths+defs+degree['queries']+[
 'Dubon2026.SourceFunctionField.rational_prime_step_finrank_eq_of_not_mem',
 'Dubon2026.SourceFunctionField.PrimeDegreeAux.aeval_jqModC_ne_jqNModC_charZero',
 'Dubon2026.SourceFricke.exists_polynomial_j_of_poleBounded_invariant',
 cn+'functionFieldOver_modular_ratio',cn+'holomorphic_quotient_cusp_pole_bound',
 cn+'finiteDimensional_jCoordinate',
 'Dubon2026.SourceFunctionField.IntegralJCoordinate.modularPolynomial_prime_adjacent_relations',
 'Dubon2026.SourceFunctionField.extend_simple_embedding_in_expansion_range',
 'Dubon2026.SourceFunctionField.geomAut',
 'Dubon2026.SourceFunctionField.HeckeNorm.primeConjugates_injective',
 'Algebra.norm_eq_prod_embeddings','AlgHom.bijective']
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,roots=roots,
 proofEdges=edges,localModules=degree['modules']+mods,separatelyAxiomChecked=[],
 compileEvidence={m:m+ev[m] for m in mods})
assert (len(ths),len(defs),len(edges))==(30,8,64),(len(ths),len(defs),len(edges))
def write(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
stem='source-gamma-one-norm-1'
write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
old='SourceGammaOneHeckeDegree';new='SourceGammaOneNorm'
for a,b in [('Audit1','Audit1'),('DependencyAudit1','DependencyAudit1'),
 ('ScratchOwnership1297','ScratchOwnership1311')]:
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
  s=s[:start]+' occur in the proof value closure of the actual original Gamma1 expanded norm product, including coprime generation, analytic adjacent-j nonmembership, original simple-extension generation, exact minimal polynomial and reverse root, preserved reverse automorphism, algebraic coefficient extension and complete embedding census. Its diamond identification on general beta inputs and original Picard specialization remain unresolved'+s[end:]
 else:
  s=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),s)
 s=s.replace('GAMMA ONE HECKE DEGREE','GAMMA ONE NORM')
 write(new+b+'.lean',s)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
reuse=[r/'Extension/Dubon2026'/(m+'.lean') for m in [
 'SourceGammaOneHeckeAlphaGerms','SourceGammaOneHeckeBetaGerms',
 'SourceGammaOneRatioRealization','SourceGammaOneAnalyticPlaceInvariance',
 'SourceGammaOneQuotientCuspSeries','SourceInvariantAnalyticJPolynomial',
 'SourceJPrimeNonpolynomial','SourceCuspLaurentPolynomial',
 'SourceRationalPrimeStepDegree','SourcePrimePowerRelativeStep',
 'SourceIntegralPrimeLaurentRoots','SourceOriginalAtkinPrimePolynomial',
 'SourceOriginalAtkinEmbedding','SourceOriginalAtkinInvolution',
 'SourceOriginalTensorCoefficientEquivR2','SourceOriginalAtkinCoefficientExtensionR2',
 'SourceOriginalHeckeNormEmbeddings','SourceOriginalHeckeEmbeddingCensus',
 'SourceOriginalHeckeNormProduct','SourceHeckeLaurentNormExtraction']]
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),
 chain='DUB17 Theorem 2.6 / DUB18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> original Gamma1 geometric Tate Frobenius -> actual Hecke norm reduction -> original reverse-map diamond identification and complete expanded norm product.',
 reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in reuse],
 shorterRoute='Native coprime modular reduction proves the actual subgroup join. Original modular-ratio germs transfer hypothetical adjacent-j membership to analytic invariance. Native cusp bounds and level-one polynomial classification, Laurent uniqueness and the positive-coefficient obstruction prove nonmembership. Reusing the rational prime-step theorem and actual alpha degree gives original simple-extension generation. The exact modular polynomial and reverse root feed the existing embedding constructor; preimage/map field closure proves preservation. Its square fixes j, so the already finite original j-extension gives surjectivity, without claiming involutivity. Native tensor coefficient extension and distinct Laurent conjugates then give all p+1 embeddings and the exact norm product. This avoids a general new modular-curve generator, scheme or Jacobian development. No proof limits, root pins or mathematical scope changed.',
 assumptionsToDischarge=[
 'For every nonzero M and prime p coprime to M, the original Gamma1 field excludes j(q^p), over both complex and rational coefficients.',
 'The original correspondence field is exactly the original lower field with j(q^p) adjoined, of degree p+1; the exact modular polynomial and reverse adjacent root are derived.',
 'An actual original-field reverse automorphism exists with the full forward Hecke equation and reverse j-coordinate equation, over rational and algebraic coefficient fields.',
 'The p twists and final q-expansion form the complete original embedding census; the actual norm is their literal Laurent product, with no assumed generator, embedding-completeness or norm-product premise.'],
 remaining='The norm product retains the constructed reverse automorphism. Its value on general beta inputs must still be identified with the exact original diamond action; no involution or Gamma0 reverse formula is claimed. The resulting diamond-correct norm reduction, residue degree equality, genus preservation, original-to-residue place/Picard specialization and torsion injectivity remain. Consequently original geometric Tate Frobenius/inertia, parabolic character realization, exceptional primes, coefficient-field realization, all-weight characteristic-zero association, automorphy and literal higher continuation remain. 16/20; DUB17--20 OPEN.',
 externalBuild=False,externalImport=False,rootPinsChanged=False)
routefile='source-gamma-one-norm-audit-route-1311.json'
write(routefile,json.dumps(route,indent=2)+'\n')
s=(p/'record_gamma_one_hecke_degree_1297.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-hecke-degree-audit-route-1297',routefile[:-5]),
 ('source-gamma-one-hecke-degree-1',stem),(old,new),
 ('ScratchOwnership1297','ScratchOwnership1311'),
 ('GAMMA ONE HECKE DEGREE','GAMMA ONE NORM')]:s=s.replace(a,b)
s=s.replace('(4, 14, 22)','(13, 38, 64)').replace('== 4','== 13')
s=s.replace('linterScopes=4','linterScopes=13').replace('modules=4','modules=13')
s=s.replace('all 22 required','all 64 required').replace('requiredProofValueEdges=22','requiredProofValueEdges=64')
s=s.replace('proofEdges=22','proofEdges=64').replace('queries=14','queries=38')
ast.parse(s);write('record_gamma_one_norm_1311.py',s)
s=(p/'audit_gamma_one_hecke_degree_1297.ps1').read_text(encoding='utf-8')
for a,b in [(old,new),('ScratchOwnership1297','ScratchOwnership1311'),
 ('record_gamma_one_hecke_degree_1297','record_gamma_one_norm_1311')]:s=s.replace(a,b)
write('audit_gamma_one_norm_1311.ps1',s)
print(json.dumps(dict(modules=len(mods),queries=len(ths+defs),edges=len(edges))))
