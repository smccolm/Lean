from pathlib import Path
import json,re,hashlib,ast
p=Path(r'E:\Lean\.tmp\dubon83')
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
ns='Dubon2026.SourceFunctionField.GammaOne.'
mods=['SourceGammaOneCanonicalCoordinates','SourceGammaOneJDegreeFinsets','SourceGammaOneCanonicalFiberLower','SourceGammaOneGenusFiberLower']
ths=[];defs=[]
for m in mods:
 code=re.sub(r'/\-.*?\-/','',(p/(m+'.lean')).read_text(encoding='utf-8'),flags=re.S)
 for kind,n in re.findall(r'^(theorem|def|abbrev) ([\w.]+)',code,re.M):
  prefix=ns
  (ths if kind=='theorem' else defs).append(prefix+n)
queries=ths+defs
required=queries+['Dubon2026.SourceCurve.finite_coordinate_canonical_degree_eq_regular_dimension','Dubon2026.SourceCurve.Place.ordDifferential_D_eq_ord_sub_one',ns+'functionFieldOver_dCoordGenerates',ns+'functionFieldOver_localDifferentials',ns+'place_residue_bijective','Dubon2026.SourceCurve.finite_function_support_of_separating_coordinate',ns+'sum_j_fiber_orders_eq_finrank',ns+'sum_j_pole_orders_eq_finrank',ns+'finrank_over_j_eq_index',ns+'regularCuspEquiv',ns+'regular_cusp_qExpansion_range_eq']
assert (len(mods),len(ths),len(defs),len(queries),len(required))==(4,13,1,14,25)
closure=mods+['SourceGammaOneCuspPoleDegree']
for m in mods:
 f=p/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0;assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime
def output(n,t):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(t)
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=queries,proofEdges=required,roots=queries,separatelyAxiomChecked=[],scratchImportClosure=closure,separateReason='The actual original Gamma1 cusp-form dimension satisfies the canonical exceptional-fiber lower bound. Elliptic fiber counts and the real period dimension comparison remain.')
output('source-gamma-one-canonical-genus-lower-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceGammaOneExactRamificationAudit1.lean').read_text(encoding='utf-8-sig');b=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b.replace('SOURCE GAMMA ONE EXACT RAMIFICATION','SOURCE GAMMA ONE CANONICAL GENUS LOWER').replace('Gamma One Exact Ramification','Gamma One Canonical Genus Lower')
output('SourceGammaOneCanonicalGenusLowerAudit1.lean',imports+''.join('#print axioms '+n+'\n' for n in queries)+'\n'+b+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceGammaOneExactRamificationDependencyAudit1.lean').read_text(encoding='utf-8-sig');b=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,v in [('roots',queries),('localModules',closure),('required',required)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b[:b.index('  logInfo m!')]+'  logInfo m!"SOURCE GAMMA ONE CANONICAL GENUS LOWER DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the actual j differential, finite exceptional-fiber contribution bound, canonical degree and literal regular-differential/cusp comparison. Only declaration values are traversed. The real period dimension inequality, surjectivity, reciprocity, original arithmetic comparison and higher continuation remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceGammaOneCanonicalGenusLowerDependencyAudit1.lean',imports+b)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
files=[r/'SourceCurveFiniteCoordinateRegularGenus.lean',r/'SourceCurveExactDerivativeOrder.lean',r/'SourceGammaOneCurveGeometry.lean',r/'SourceGammaOneRegularCuspEquiv.lean',r/'SourceOriginalCanonicalFiberDegree.lean',r/'SourceOriginalJDegreeSums.lean',p/'gamma-one-genus-lower-route-785.json']
rd=dict(chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> original all-weight arithmetic association -> actual Gamma1 Hecke-character realization -> Picard/H1 and Abel-Jacobi -> real period surjectivity -> reverse dimension inequality -> actual genus lower bound.',assumptionsToDischarge='The actual j differential has its literal finite canonical divisor and degree twice the regular-differential dimension minus two. All local differential, residue and finite-coordinate prerequisites are derived. At poles and finite values its coefficient is the corresponding j-coordinate order minus one; other finite contributions are nonnegative. The actual three finite exceptional sets exist and their order sums are derived, so the field degree minus their cardinalities is a lower bound for canonical degree. The literal Fourier equivalence converts this into the original Gamma1 weight-two cusp-form dimension bound, with no canonical-degree, genus or local-order premise.',remaining='Bound the two finite elliptic fiber cardinalities by the already counted signed S/ST cyclic orbits, then combine with the audited real Manin upper bound. Real period surjectivity, reciprocity, Picard/Hecke/diamond/H1, full all-weight characteristic-zero association and higher continuation remain. 16/20; DUB-17--20 OPEN.',reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in files],shorterRoute='Reuse the existing generic finite-coordinate canonical-degree and exact derivative-order theorems. A lower bound suffices, so retain nonnegative off-exceptional contributions and avoid an exact genus formula or new off-exceptional vanishing proof. Reuse the actual field degree and literal Fourier equivalence.')
output('gamma-one-canonical-genus-lower-audit-route-789.json',json.dumps(rd,indent=2)+'\n')
s=(p/'record_gamma_one_signed_parabolic_777.py').read_text(encoding='utf-8-sig')
for a,b in [('source-gamma-one-signed-parabolic-1','source-gamma-one-canonical-genus-lower-1'),('SourceGammaOneSignedParabolic','SourceGammaOneCanonicalGenusLower'),('SOURCE GAMMA ONE SIGNED PARABOLIC','SOURCE GAMMA ONE CANONICAL GENUS LOWER'),('gamma-one-signed-parabolic-audit-route-777.json','gamma-one-canonical-genus-lower-audit-route-789.json'),('(2, 15, 18)','(4, 14, 25)'),('all 18 required','all 25 required'),('requiredProofValueEdges=18','requiredProofValueEdges=25'),('modules=2, queries=15','modules=4, queries=14'),('proofEdges=18','proofEdges=25'),('== 2','== 4'),('linterScopes=2','linterScopes=4')]:
 assert a in s,a;s=s.replace(a,b)
ast.parse(s);output('record_gamma_one_canonical_genus_lower_789.py',s)
s=(p/'SourceGammaOneExactRamificationScratchOwnership731.lean').read_text(encoding='utf-8-sig').replace('import SourceGammaOneExactRamification',''.join('import '+m+'\n' for m in mods).rstrip()).replace('#[`SourceGammaOneExactRamification]',arr(mods))
output('SourceGammaOneCanonicalGenusLowerScratchOwnership789.lean',s)
print(json.dumps(dict(modules=4,queries=14,edges=25)))
