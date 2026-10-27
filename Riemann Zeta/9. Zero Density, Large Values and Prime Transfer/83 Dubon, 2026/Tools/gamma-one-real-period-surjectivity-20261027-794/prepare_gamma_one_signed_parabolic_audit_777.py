from pathlib import Path
import json,re,hashlib,ast
p=Path(r'E:\Lean\.tmp\dubon83')
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
ns='Dubon2026.SourceFunctionField.GammaOne.'
mods=['SourceGammaOneCentralSignCharacters','SourceGammaOneSignedParabolicCharacters']
ths=[];defs=[]
for m in mods:
 code=re.sub(r'/\-.*?\-/','',(p/(m+'.lean')).read_text(encoding='utf-8'),flags=re.S)
 for kind,n in re.findall(r'^(theorem|def|abbrev) ([\w.]+)',code,re.M):
  prefix=ns+'CentralSign.' if m=='SourceGammaOneCentralSignCharacters' else ns
  (ths if kind=='theorem' else defs).append(prefix+n)
queries=ths+defs
required=queries+[ns+'mem_plusMinus_iff','Dubon2026.sourceH1Finite','SpecialLinearGroup.SL2Z_generators']
assert (len(mods),len(ths),len(defs),len(queries),len(required))==(2,11,4,15,18)
closure=mods+['SourceGammaOneRealParabolicPeriods','SourceGammaOneRealPeriodMap','SourceGammaOneRealPeriodInjectivity','SourceGammaOneInvariantRealPart']
for m in mods:
 f=p/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0;assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime
def output(n,t):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(t)
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=queries,proofEdges=required,roots=queries,separatelyAxiomChecked=[],scratchImportClosure=closure,separateReason='Actual real Gamma1 parabolic characters inject linearly into the finite real parabolic character space of the central-sign enlargement. The needed finrank inequality follows; Manin and genus dimension comparison remain.')
output('source-gamma-one-signed-parabolic-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceGammaOneExactRamificationAudit1.lean').read_text(encoding='utf-8-sig');b=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b.replace('SOURCE GAMMA ONE EXACT RAMIFICATION','SOURCE GAMMA ONE SIGNED PARABOLIC').replace('Gamma One Exact Ramification','Gamma One Signed Parabolic')
output('SourceGammaOneSignedParabolicAudit1.lean',imports+''.join('#print axioms '+n+'\n' for n in queries)+'\n'+b+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceGammaOneExactRamificationDependencyAudit1.lean').read_text(encoding='utf-8-sig');b=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,v in [('roots',queries),('localModules',closure),('required',required)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b[:b.index('  logInfo m!')]+'  logInfo m!"SOURCE GAMMA ONE SIGNED PARABOLIC DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the actual real parabolic central-sign extension, its injectivity and finite-dimensional target. Only declaration values are traversed. The real period dimension inequality, surjectivity, reciprocity, original arithmetic comparison and higher continuation remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceGammaOneSignedParabolicDependencyAudit1.lean',imports+b)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
files=[r/'SourceGammaOnePlusMinus.lean',r/'SourceIntegralCohomologyFinite.lean',r/'SourceManinRelationDimension.lean',p/'gamma-one-real-manin-route-775.json',p/'source-gamma-one-real-parabolic-periods-1-scratch-receipt.json']
rd=dict(chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> original all-weight arithmetic association -> actual Gamma1 Hecke-character realization -> Picard/H1 and Abel-Jacobi -> real period surjectivity -> reverse dimension inequality -> real Manin relations on signed cosets.',assumptionsToDischarge='Every enlarged-group element has an actual original-subgroup representative up to central sign. Equality of squares forces equality of real additive-character values, proving additivity and independence of sign. The extension agrees with the original character and is injective. Squared trace is unchanged by central sign, so the actual original real parabolic characters embed linearly in the signed parabolic space. Native finite H1 proves target finiteness; the required finrank inequality is derived without an extension or torsion-vanishing hypothesis.',remaining='Adapt the exact real Manin dimension bound and assemble the actual Hurwitz/genus inequality using the proved finite and cusp fibers. Real period surjectivity, reciprocity, Picard/Hecke/diamond/H1, full all-weight characteristic-zero association and higher continuation remain. 16/20; DUB-17--20 OPEN.',reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in files],shorterRoute='Construct only the injection and dimension comparison needed downstream. Equality of squares avoids transfer, abelianization and divisible-character extension infrastructure. Native finite H1 replaces a new finite-generator character argument.')
output('gamma-one-signed-parabolic-audit-route-777.json',json.dumps(rd,indent=2)+'\n')
s=(p/'record_gamma_one_exact_cusp_orbits_774.py').read_text(encoding='utf-8-sig')
for a,b in [('source-gamma-one-exact-cusp-orbits-1','source-gamma-one-signed-parabolic-1'),('SourceGammaOneExactCuspOrbits','SourceGammaOneSignedParabolic'),('SOURCE GAMMA ONE EXACT CUSP ORBITS','SOURCE GAMMA ONE SIGNED PARABOLIC'),('gamma-one-exact-cusp-orbits-audit-route-774.json','gamma-one-signed-parabolic-audit-route-777.json'),('(7, 32, 39)','(2, 15, 18)'),('all 39 required','all 18 required'),('requiredProofValueEdges=39','requiredProofValueEdges=18'),('modules=7, queries=32','modules=2, queries=15'),('proofEdges=39','proofEdges=18'),('== 7','== 2'),('linterScopes=7','linterScopes=2')]:
 assert a in s,a;s=s.replace(a,b)
ast.parse(s);output('record_gamma_one_signed_parabolic_777.py',s)
s=(p/'SourceGammaOneExactRamificationScratchOwnership731.lean').read_text(encoding='utf-8-sig').replace('import SourceGammaOneExactRamification',''.join('import '+m+'\n' for m in mods).rstrip()).replace('#[`SourceGammaOneExactRamification]',arr(mods))
output('SourceGammaOneSignedParabolicScratchOwnership777.lean',s)
print(json.dumps(dict(modules=2,queries=15,edges=18)))
