from pathlib import Path
import json,re,hashlib,ast
p=Path(r'E:\Lean\.tmp\dubon83')
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
ns='Dubon2026.SourceFunctionField.GammaOne.'
mods=['SourceGammaOneEllipticCosetFiber','SourceGammaOneEllipticFiberBounds','SourceGammaOneRealPeriodSurjectivity']
ths=[];defs=[]
for m in mods:
 code=re.sub(r'/\-.*?\-/','',(p/(m+'.lean')).read_text(encoding='utf-8'),flags=re.S)
 for kind,n in re.findall(r'^(theorem|def|abbrev) ([\w.]+)',code,re.M):
  prefix=ns+'EllipticCounting.' if m!='SourceGammaOneRealPeriodSurjectivity' else (ns if n=='gammaOne_real_parabolic_dimension_le_twice_cusp' else 'Dubon2026.')
  (ths if kind=='theorem' else defs).append(prefix+n)
queries=ths+defs
required=queries+[ns+'AnalyticFiberOrbits.toFiber_surjective','Dubon2026.SourceManin.two_mul_natCard_orb','Dubon2026.SourceManin.three_mul_natCard_orb',ns+'gammaOne_real_parabolic_dimension_upper',ns+'gammaOne_cusp_dimension_lower_fiber_cards',ns+'RealManin.parabolic_dimension_bound',ns+'CuspCounting.orbitToRationalCusp_bijective',ns+'gammaOneCuspOrbitPlaceMap_bijective','Dubon2026.SourceCurve.finite_coordinate_canonical_degree_eq_regular_dimension',ns+'regularCuspEquiv','Dubon2026.sourceGamma1RealParabolicPeriodHom_injective','Dubon2026.sourceGamma1RealParabolicHoms_finite','Dubon2026.sourceGamma1_real_periods_injective']
assert (len(mods),len(ths),len(defs),len(queries),len(required))==(3,15,4,19,32)
closure=mods+['SourceGammaOneInvariantRealPart', 'SourceGammaOneRealPeriodInjectivity', 'SourceGammaOneRealPeriodMap', 'SourceGammaOneRealParabolicPeriods', 'SourceGammaOneCuspPlaceLeftInvariance', 'SourceGammaOneCuspTranslations', 'SourceGammaOneCuspPlaceRightInvariance', 'SourceGammaOneRationalCuspPlace', 'SourceGammaOneRationalCuspOrbit', 'SourceGammaOneCuspJExactOrder', 'SourceGammaOneCuspRotationOrder', 'SourceGammaOneCuspTranslationRamification', 'SourceGammaOneCuspCyclicOrbit', 'SourceGammaOneCuspCosetPlaces', 'SourceGammaOneCuspCosetBound', 'SourceGammaOneCuspPoleDegree', 'SourceGammaOneCuspPositiveWeight', 'SourceGammaOneCuspOrbitBijection', 'SourceGammaOneExactCuspOrbits', 'SourceGammaOneCentralSignCharacters', 'SourceGammaOneSignedParabolicCharacters', 'SourceGammaOneRealManinCharacter', 'SourceGammaOneRealCuspPotential', 'SourceGammaOneRealManinDimension', 'SourceGammaOneRationalCyclicCusps', 'SourceGammaOneRealPeriodDimensionUpper', 'SourceGammaOneCanonicalCoordinates', 'SourceGammaOneJDegreeFinsets', 'SourceGammaOneCanonicalFiberLower', 'SourceGammaOneGenusFiberLower']
for m in mods:
 f=p/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0;assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime
def output(n,t):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(t)
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=queries,proofEdges=required,roots=queries,separatelyAxiomChecked=[],scratchImportClosure=closure,separateReason='Every original real Gamma1 parabolic character is realized by an actual weight-two cusp form. Exact real-period surjectivity is proved; reciprocity and the full arithmetic branch remain.')
output('source-gamma-one-real-period-surjectivity-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceGammaOneExactRamificationAudit1.lean').read_text(encoding='utf-8-sig');b=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b.replace('SOURCE GAMMA ONE EXACT RAMIFICATION','SOURCE GAMMA ONE REAL PERIOD SURJECTIVITY').replace('Gamma One Exact Ramification','Gamma One Real Period Surjectivity')
output('SourceGammaOneRealPeriodSurjectivityAudit1.lean',imports+''.join('#print axioms '+n+'\n' for n in queries)+'\n'+b+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceGammaOneExactRamificationDependencyAudit1.lean').read_text(encoding='utf-8-sig');b=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,v in [('roots',queries),('localModules',closure),('required',required)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b[:b.index('  logInfo m!')]+'  logInfo m!"SOURCE GAMMA ONE REAL PERIOD SURJECTIVITY DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the actual original Gamma1 real period surjectivity, matching Manin and canonical-degree bounds, actual cusp and elliptic fibers, and real-period injectivity. Only declaration values are traversed. Real period surjectivity is proved. Reciprocity, original arithmetic comparison and higher continuation remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceGammaOneRealPeriodSurjectivityDependencyAudit1.lean',imports+b)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
files=[r/'SourceOriginalCosetFiber.lean',r/'SourceEllipticStabilizerOrbits.lean',r/'SourceManinOrbitCount.lean',p/'gamma-one-genus-lower-route-785.json',p/'source-gamma-one-real-manin-1b-scratch-receipt.json',p/'source-gamma-one-canonical-genus-lower-1-scratch-receipt.json',p/'source-gamma-one-real-period-upper-1-scratch-receipt.json',p/'source-gamma-one-real-parabolic-periods-1-scratch-receipt.json']
rd=dict(chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> original all-weight arithmetic association -> actual Gamma1 Hecke-character realization -> Picard/H1 and Abel-Jacobi -> actual real period realization.',assumptionsToDischarge='Actual signed cosets map onto each original finite j fiber and descend through cyclic actions fixing its analytic value. The existing S/ST orbit counts give the required elliptic fiber bounds. These close the canonical-degree/Manin dimension comparison for the ORIGINAL Gamma1 real parabolic-character space. Its dimension equals the real dimension of weight-two cusp forms. The already proved injective real-period map is therefore surjective, giving an actual linear equivalence and a cusp form realizing EVERY original real parabolic character. No period-surjectivity, genus, dimension, fiber-cardinality or character-extension premise remains.',remaining='Promote and run assembled verification. Reciprocity and construction of meromorphic functions from Abel-Jacobi periods, Picard/Hecke/diamond/H1, full all-weight characteristic-zero association and higher continuation remain. 16/20; DUB-17--20 OPEN.',reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in files],shorterRoute='Use surjective elliptic fiber maps and a genus lower bound, which are exactly sufficient to match the real Manin upper bound. Reuse the generic orbit counts, canonical-degree theorem, actual Fourier equivalence and native finite-dimensional linear equivalence. No new exact genus formula, elliptic fiber injectivity proof or abstract homology presentation is needed.')
output('gamma-one-real-period-surjectivity-audit-route-793.json',json.dumps(rd,indent=2)+'\n')
s=(p/'record_gamma_one_signed_parabolic_777.py').read_text(encoding='utf-8-sig')
for a,b in [('source-gamma-one-signed-parabolic-1','source-gamma-one-real-period-surjectivity-1'),('SourceGammaOneSignedParabolic','SourceGammaOneRealPeriodSurjectivity'),('SOURCE GAMMA ONE SIGNED PARABOLIC','SOURCE GAMMA ONE REAL PERIOD SURJECTIVITY'),('gamma-one-signed-parabolic-audit-route-777.json','gamma-one-real-period-surjectivity-audit-route-793.json'),('(2, 15, 18)','(3, 19, 32)'),('all 18 required','all 32 required'),('requiredProofValueEdges=18','requiredProofValueEdges=32'),('modules=2, queries=15','modules=3, queries=19'),('proofEdges=18','proofEdges=32'),('== 2','== 3'),('linterScopes=2','linterScopes=3')]:
 assert a in s,a;s=s.replace(a,b)
ast.parse(s);output('record_gamma_one_real_period_surjectivity_793.py',s)
s=(p/'SourceGammaOneExactRamificationScratchOwnership731.lean').read_text(encoding='utf-8-sig').replace('import SourceGammaOneExactRamification',''.join('import '+m+'\n' for m in mods).rstrip()).replace('#[`SourceGammaOneExactRamification]',arr(mods))
output('SourceGammaOneRealPeriodSurjectivityScratchOwnership793.lean',s)
print(json.dumps(dict(modules=3,queries=19,edges=32)))
