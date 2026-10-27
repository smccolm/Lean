from pathlib import Path
import json,re,hashlib,ast
p=Path(r'E:\Lean\.tmp\dubon83')
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
ns='Dubon2026.SourceFunctionField.GammaOne.'
mods=['SourceGammaOneRationalCyclicCusps','SourceGammaOneRealPeriodDimensionUpper']
ths=[];defs=[]
for m in mods:
 code=re.sub(r'/\-.*?\-/','',(p/(m+'.lean')).read_text(encoding='utf-8'),flags=re.S)
 for kind,n in re.findall(r'^(theorem|def|abbrev) ([\w.]+)',code,re.M):
  prefix=ns+'CuspCounting.' if m=='SourceGammaOneRationalCyclicCusps' else ns
  (ths if kind=='theorem' else defs).append(prefix+n)
queries=ths+defs
required=queries+['Dubon2026.SourceManin.smul_infty_eq_iff',ns+'exists_T_zpow_or_neg_of_lower_left',ns+'rationalCuspOrbitMk_eq_iff',ns+'rationalCuspOrbitFromCoset_surjective',ns+'gammaOne_j_pole_card_eq_translation_orbits',ns+'RealManin.parabolic_dimension_bound',ns+'gammaOne_parabolic_finrank_le_signed']
assert (len(mods),len(ths),len(defs),len(queries),len(required))==(2,6,1,7,14)
closure=mods+['SourceGammaOneRationalCuspOrbit','SourceGammaOneRationalCuspPlace','SourceGammaOneCuspCosetPlaces','SourceGammaOneExactCuspOrbits','SourceGammaOneRealManinDimension','SourceGammaOneRealCuspPotential','SourceGammaOneRealManinCharacter','SourceGammaOneSignedParabolicCharacters']
for m in mods:
 f=p/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0;assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime
def output(n,t):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(t)
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=queries,proofEdges=required,roots=queries,separatelyAxiomChecked=[],scratchImportClosure=closure,separateReason='The actual original Gamma1 real parabolic dimension satisfies the Manin upper bound with the actual algebraic cusp count. The genus lower bound remains.')
output('source-gamma-one-real-period-upper-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceGammaOneExactRamificationAudit1.lean').read_text(encoding='utf-8-sig');b=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b.replace('SOURCE GAMMA ONE EXACT RAMIFICATION','SOURCE GAMMA ONE REAL PERIOD UPPER').replace('Gamma One Exact Ramification','Gamma One Real Period Upper')
output('SourceGammaOneRealPeriodUpperAudit1.lean',imports+''.join('#print axioms '+n+'\n' for n in queries)+'\n'+b+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceGammaOneExactRamificationDependencyAudit1.lean').read_text(encoding='utf-8-sig');b=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,v in [('roots',queries),('localModules',closure),('required',required)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b[:b.index('  logInfo m!')]+'  logInfo m!"SOURCE GAMMA ONE REAL PERIOD UPPER DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the actual rational-cusp and cyclic-orbit bijection and the assembled original real parabolic dimension bound. Only declaration values are traversed. The real period dimension inequality, surjectivity, reciprocity, original arithmetic comparison and higher continuation remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceGammaOneRealPeriodUpperDependencyAudit1.lean',imports+b)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
files=[p/'SourceGammaOneRationalCuspPlace.lean',p/'SourceGammaOneRationalCuspOrbit.lean',p/'SourceGammaOneCuspCosetPlaces.lean',p/'SourceGammaOneExactCuspOrbits.lean',p/'SourceGammaOneRealManinDimension.lean',p/'SourceGammaOneSignedParabolicCharacters.lean',p/'gamma-one-real-manin-route-775.json']
rd=dict(chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> original all-weight arithmetic association -> actual Gamma1 Hecke-character realization -> Picard/H1 and Abel-Jacobi -> real period surjectivity -> reverse dimension inequality -> real Manin bound with actual algebraic cusp count.',assumptionsToDischarge='Rational cusp orbits of the signed subgroup are proved bijective with cyclic translation orbits of its integral cosets, using the actual integral infinity stabilizer. The already proved cyclic-cusp-place bijection identifies this count with the actual j poles. The signed extension and real Manin theorem then bound the ORIGINAL Gamma1 real parabolic-character dimension, with the original field cusp term and the signed elliptic fixed-point terms; the central-sign hypothesis is derived.',remaining='The corresponding actual genus lower bound must be assembled from canonical degree and elliptic fiber counts. Real period surjectivity, reciprocity, Picard/Hecke/diamond/H1, full all-weight characteristic-zero association and higher continuation remain. 16/20; DUB-17--20 OPEN.',reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in files],shorterRoute='Use the exact infinity stabilizer and the existing cyclic cusp-place bijection. No independent arithmetic cusp enumeration or general double-coset development is needed. The only character extension needed is the already proved injection.')
output('gamma-one-real-period-upper-audit-route-784.json',json.dumps(rd,indent=2)+'\n')
s=(p/'record_gamma_one_signed_parabolic_777.py').read_text(encoding='utf-8-sig')
for a,b in [('source-gamma-one-signed-parabolic-1','source-gamma-one-real-period-upper-1'),('SourceGammaOneSignedParabolic','SourceGammaOneRealPeriodUpper'),('SOURCE GAMMA ONE SIGNED PARABOLIC','SOURCE GAMMA ONE REAL PERIOD UPPER'),('gamma-one-signed-parabolic-audit-route-777.json','gamma-one-real-period-upper-audit-route-784.json'),('(2, 15, 18)','(2, 7, 14)'),('all 18 required','all 14 required'),('requiredProofValueEdges=18','requiredProofValueEdges=14'),('modules=2, queries=15','modules=2, queries=7'),('proofEdges=18','proofEdges=14')]:
 assert a in s,a;s=s.replace(a,b)
ast.parse(s);output('record_gamma_one_real_period_upper_784.py',s)
s=(p/'SourceGammaOneExactRamificationScratchOwnership731.lean').read_text(encoding='utf-8-sig').replace('import SourceGammaOneExactRamification',''.join('import '+m+'\n' for m in mods).rstrip()).replace('#[`SourceGammaOneExactRamification]',arr(mods))
output('SourceGammaOneRealPeriodUpperScratchOwnership784.lean',s)
print(json.dumps(dict(modules=2,queries=7,edges=14)))
