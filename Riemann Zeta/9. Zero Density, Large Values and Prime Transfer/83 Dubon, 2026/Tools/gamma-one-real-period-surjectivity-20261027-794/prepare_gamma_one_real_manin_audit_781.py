from pathlib import Path
import json,re,hashlib,ast
p=Path(r'E:\Lean\.tmp\dubon83')
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
ns='Dubon2026.SourceFunctionField.GammaOne.RealManin.'
mods=['SourceGammaOneRealManinCharacter','SourceGammaOneRealCuspPotential','SourceGammaOneRealManinDimension']
ths=[];defs=[]
for m in mods:
 code=re.sub(r'/\-.*?\-/','',(p/(m+'.lean')).read_text(encoding='utf-8'),flags=re.S)
 for kind,n in re.findall(r'^(?:noncomputable )?(theorem|def|abbrev) ([\w.]+)',code,re.M):
  prefix=ns
  (ths if kind=='theorem' else defs).append(prefix+n)
queries=ths+defs
required=queries+['Dubon2026.SourceManin.relSpace_rank_bound','SpecialLinearGroup.SL2Z_generators','Dubon2026.SourceFunctionField.GammaOne.realParabolicCharacters_finite','Dubon2026.SourceFunctionField.GammaOne.rationalCuspOrbit_finite','Dubon2026.SourceFunctionField.GammaOne.rationalCuspOrbitMk_eq_iff']
assert len(mods)==3
counts=(len(mods),len(queries),len(required))
closure=mods+['SourceGammaOneCentralSignCharacters','SourceGammaOneRealManinCharacters','SourceGammaOneRationalCuspOrbit']
for m in mods:
 f=p/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0;assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime
def output(n,t):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(t)
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=queries,proofEdges=required,roots=queries,separatelyAxiomChecked=[],scratchImportClosure=closure,separateReason='Actual real parabolic characters and cusp potentials inject into the finite Manin relation space with one constant. The exact upper bound follows; matching cusp terms and the genus lower bound remain.')
output('source-gamma-one-real-manin-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceGammaOneExactRamificationAudit1.lean').read_text(encoding='utf-8-sig');b=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b.replace('SOURCE GAMMA ONE EXACT RAMIFICATION','SOURCE GAMMA ONE REAL MANIN').replace('Gamma One Exact Ramification','Gamma One Real Manin')
output('SourceGammaOneRealManinAudit1.lean',imports+''.join('#print axioms '+n+'\n' for n in queries)+'\n'+b+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceGammaOneExactRamificationDependencyAudit1.lean').read_text(encoding='utf-8-sig');b=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,v in [('roots',queries),('localModules',closure),('required',required)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b[:b.index('  logInfo m!')]+'  logInfo m!"SOURCE GAMMA ONE REAL MANIN DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the actual real cusp potentials, injective Manin comparison and finite relation-space dimension bound. Only declaration values are traversed. The real period dimension inequality, surjectivity, reciprocity, original arithmetic comparison and higher continuation remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceGammaOneRealManinDependencyAudit1.lean',imports+b)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
files=[r/'SourceManinCuspStabilizer.lean',r/'SourceManinCuspPotential.lean',r/'SourceManinParabolicDimension.lean',r/'SourceManinRelationDimension.lean',p/'gamma-one-real-manin-route-775.json',p/'source-gamma-one-signed-parabolic-1-scratch-receipt.json']
rd=dict(chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> original all-weight arithmetic association -> actual Gamma1 Hecke-character realization -> Picard/H1 and Abel-Jacobi -> real period surjectivity -> reverse dimension inequality -> actual real Manin bound.',assumptionsToDischarge='Actual real parabolic characters and rational cusp potentials satisfy the two and three term relations. Adding the value at infinity gives an injective map into the existing finite Manin relation space. Native finite H1 and finite cusp orbits supply finiteness. The unchanged generic relation-space theorem proves six times the real parabolic dimension plus six times the rational cusp count and the weighted elliptic fixed-point counts is at most twelve plus the subgroup index. The central-sign hypothesis is explicit for application to the signed Gamma1 subgroup.',remaining='Match rational cusp orbits with the proved algebraic cusp bijection and assemble the actual Hurwitz/genus inequality using finite fibers. Real period surjectivity, reciprocity, Picard/Hecke/diamond/H1, full all-weight characteristic-zero association and higher continuation remain. 16/20; DUB-17--20 OPEN.',reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in files],shorterRoute='Adapt only the coefficient and subgroup interfaces of the existing cusp potential and Manin comparison. Reuse the generic relation-space theorem unchanged; no separate homology presentation or full character isomorphism is needed.')
output('gamma-one-real-manin-audit-route-781.json',json.dumps(rd,indent=2)+'\n')
s=(p/'record_gamma_one_signed_parabolic_777.py').read_text(encoding='utf-8-sig')
for a,b in [('source-gamma-one-signed-parabolic-1','source-gamma-one-real-manin-1'),('SourceGammaOneSignedParabolic','SourceGammaOneRealManin'),('SOURCE GAMMA ONE SIGNED PARABOLIC','SOURCE GAMMA ONE REAL MANIN'),('gamma-one-signed-parabolic-audit-route-777.json','gamma-one-real-manin-audit-route-781.json'),('(2, 15, 18)',str(counts)),('all 18 required','all '+str(len(required))+' required'),('requiredProofValueEdges=18','requiredProofValueEdges='+str(len(required))),('modules=2, queries=15','modules=3, queries='+str(len(queries))),('proofEdges=18','proofEdges='+str(len(required))),('== 2','== 3'),('linterScopes=2','linterScopes=3')]:
 assert a in s,a;s=s.replace(a,b)
ast.parse(s);output('record_gamma_one_real_manin_781.py',s)
s=(p/'SourceGammaOneExactRamificationScratchOwnership731.lean').read_text(encoding='utf-8-sig').replace('import SourceGammaOneExactRamification',''.join('import '+m+'\n' for m in mods).rstrip()).replace('#[`SourceGammaOneExactRamification]',arr(mods))
output('SourceGammaOneRealManinScratchOwnership781.lean',s)
print(json.dumps(dict(modules=len(mods),theorems=len(ths),constructions=len(defs),queries=len(queries),edges=len(required))))
