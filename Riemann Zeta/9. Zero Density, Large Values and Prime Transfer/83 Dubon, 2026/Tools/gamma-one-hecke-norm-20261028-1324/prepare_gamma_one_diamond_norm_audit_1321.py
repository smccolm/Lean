from pathlib import Path
from datetime import datetime, timezone
import ast, hashlib, json, re
p = Path(__file__).parent
r = Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
mods = ['SourceGammaOneAdjacentJDiamondMatrix', 'SourceGammaOneAdjacentJDiamondAction',
 'SourceGammaOneRationalAnalyticGerms', 'SourceGammaOneUpperHalfPlaneHeckeGerms',
 'SourceGammaOneAdjacentJAnalyticAction', 'SourceGammaOneUpperHalfPlaneGermFaithfulness',
 'SourceGammaOneAdjacentJReverseDiamond', 'SourceGammaOneAdjacentJArithmeticDiamond',
 'SourceGammaOneHeckeDiamondNorm']
ths, defs, ev = [], [], {}
for m in mods:
 exits = [f for f in p.glob(m+'*.exit') if re.fullmatch(re.escape(m)+r'\d+[a-z]\.exit', f.name)]
 f = max(exits, key=lambda a:a.stat().st_mtime)
 assert f.read_text().strip() == '0' and f.with_suffix('.log').stat().st_size == 0, f
 assert (p/(m+'.olean')).stat().st_mtime >= (p/(m+'.lean')).stat().st_mtime, m
 ev[m] = f.stem
 code = re.sub(r'--[^\n]*', '', re.sub(r'/\-.*?\-/', '', (p/(m+'.lean')).read_text(encoding='utf-8'), flags=re.S))
 ns = re.search(r'^namespace (\S+)', code, re.M)[1]+'.'
 ths += [ns+x for x in re.findall(r'^theorem\s+([\w.\x27]+)', code, re.M)]
 defs += [ns+x for x in re.findall(r'^(?:@\[[^\n]*\]\s*)?def\s+([\w.\x27]+)', code, re.M)]
 defs += [ns+x for x in re.findall(r'^local instance\s+([\w.\x27]+)', code, re.M)]
cn = 'Dubon2026.SourceFunctionField.GammaOne.'
degree = json.loads((p/'source-gamma-one-hecke-degree-1-audit-config.json').read_text(encoding='utf-8'))
norm = json.loads((p/'source-gamma-one-norm-1-audit-config.json').read_text(encoding='utf-8'))
separate = [cn+'rationalAnalyticGerm_constants']
roots = [cn+'exists_gammaOne_hecke_norm_beta_product'] + norm['roots']
native = [cn+'realize_diamondFieldHom_eventuallyEq', cn+'ConstantField.fieldMap_arithmeticDiamondHom',
 cn+'ConstantField.arithmeticDiamondHom_j', cn+'realize_heckeBeta_eventuallyEq',
 cn+'realize_smul_eventuallyEq', 'Dubon2026.SourceFunctionField.OriginalConstantField.coeffMap_sigma_rational',
 'Dubon2026.SourceFunctionField.coe_geomAut_coeffEmb', 'Dubon2026.germPullback']
edges = list(dict.fromkeys([x for x in ths+defs if x not in separate] + degree['queries'] + norm['queries'] + native))
cfg = dict(modules=mods, theorems=ths, constructions=defs, queries=ths+defs, roots=roots,
 proofEdges=edges, localModules=degree['modules']+norm['modules']+mods,
 separatelyAxiomChecked=separate, compileEvidence=ev)
assert (len(ths),len(defs)) == (22,7), (len(ths),len(defs))
def write(n,s):
 f=p/n
 assert not f.exists(), f
 f.write_text(s,encoding='utf-8')
stem='source-gamma-one-diamond-norm-1'
write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
old='SourceGammaOneNorm';new='SourceGammaOneDiamondNorm'
for a,b in [('Audit1','Audit1'),('DependencyAudit1','DependencyAudit1'),('ScratchOwnership1311','ScratchOwnership1321')]:
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
  s=s[:start]+' occur in the proof value closure of the original Gamma1 norm product and its exact arithmetic diamond comparison. The label satisfies p*d=1 in ZMod M. The rational constant-germ sanity lemma is separately axiom checked and is not claimed as an endpoint dependency. Integral reduction, degree and genus preservation, original Picard specialization and torsion injectivity remain unresolved'+s[end:]
 else:
  s=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),s)
 s=s.replace('GAMMA ONE NORM','GAMMA ONE DIAMOND NORM')
 write(new+b+'.lean',s)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
reuse=[r/'Extension/Dubon2026'/(m+'.lean') for m in [
 'SourceGammaOneRealizationAlgebra','SourceGammaOneHeckeAlphaGerms','SourceGammaOneHeckeBetaGerms',
 'SourceGammaOneAnalyticPlaceInvariance','SourceGammaOneDiamondAnalyticGerms',
 'SourceGammaOneArithmeticDiamond','SourceGammaOneComplexCoefficientMap',
 'SourceOriginalTensorCoefficientEquivR2','SourceHeckeLaurentNormExtraction',
 'SourceOriginalHeckeNormReduction','SourceGermPullback']]
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),
 chain='DUB17 Theorem 2.6 / DUB18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> original Gamma1 geometric Tate Frobenius -> Hecke norm reduction -> exact reverse-map arithmetic diamond and expanded norm product.',
 reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in reuse],
 shorterRoute='Use native coprime reduction to lift the matrix S modulo p in Gamma1(M). The exact matrix D_p gamma D_p/p lies in Gamma0(M) and has p*d=1 under the lower-right convention. Native modular-ratio realization, restriction and Hecke germs identify the reverse map on the already proved generating field F(j(q^p)). Faithfulness of the actual field-to-germ homomorphism then gives the complex diamond identity. The existing fixed coefficient embedding and arithmetic diamond comparison descend this equality to Qbar; native tensor realization and adjoin extensionality extend it to every original arithmetic function. The actual embedding census gives the complete norm. This avoids a new extension theory over transcendental constants, a new curve model, or an assumed involution. Kernel proof decomposition replaces the oversized intermediate proof; proof limits remain unchanged.',
 assumptionsToDischarge=[
 'The reverse automorphism acts analytically on every function of the original correspondence field, derived from the exact field generators.',
 'Its value on every original beta input is alpha of the actual arithmetic diamond, with the exact integral matrix and label p*d=1.',
 'There exist actual arithmetic reverse and diamond automorphisms satisfying both Hecke equations and the literal expanded norm formula, without supplied action, label or norm-product certificates.'],
 remaining='Integral reduction of the diamond-correct norm product, residue degree equality, genus preservation, compatible original-to-residue place/Picard specialization and prime-to-residue torsion injectivity remain. These are still needed for original geometric Tate Frobenius/inertia, parabolic character realization or a faithful alternative, exceptional primes, coefficient-field realization, all-weight characteristic-zero association, automorphy and literal higher continuation. 16/20; DUB17--20 OPEN.',
 externalBuild=False, externalImport=False, rootPinsChanged=False, proofLimitsChanged=False)
routefile='source-gamma-one-diamond-norm-audit-route-1321.json'
write(routefile,json.dumps(route,indent=2)+'\n')
s=(p/'record_gamma_one_norm_1311.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-norm-audit-route-1311',routefile[:-5]),('source-gamma-one-norm-1',stem),
 (old,new),('ScratchOwnership1311','ScratchOwnership1321'),('GAMMA ONE NORM','GAMMA ONE DIAMOND NORM')]:s=s.replace(a,b)
s=s.replace('(13, 38, 64)',repr((len(mods),len(ths+defs),len(edges))))
s=s.replace('== 13','== 9').replace('linterScopes=13','linterScopes=9').replace('modules=13','modules=9')
s=s.replace('queries=38','queries='+str(len(ths+defs))).replace('all 64 required','all '+str(len(edges))+' required')
s=s.replace('requiredProofValueEdges=64','requiredProofValueEdges='+str(len(edges))).replace('proofEdges=64','proofEdges='+str(len(edges)))
ast.parse(s);write('record_gamma_one_diamond_norm_1321.py',s)
s=(p/'audit_gamma_one_norm_1311.ps1').read_text(encoding='utf-8')
for a,b in [(old,new),('ScratchOwnership1311','ScratchOwnership1321'),('record_gamma_one_norm_1311','record_gamma_one_diamond_norm_1321')]:s=s.replace(a,b)
write('audit_gamma_one_diamond_norm_1321.ps1',s)
print(json.dumps(dict(modules=len(mods),queries=len(ths+defs),edges=len(edges))))
