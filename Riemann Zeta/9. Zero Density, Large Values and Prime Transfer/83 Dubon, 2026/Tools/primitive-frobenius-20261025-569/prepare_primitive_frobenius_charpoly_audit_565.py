from pathlib import Path
import json,re,hashlib
p=Path(__file__).parent
prod=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
mods=['SourceValuationFrobeniusRoots','SourceValuationCyclotomicFrobenius','SourceRankTwoQuadraticTrace','SourceCyclotomicFrobeniusCharpoly','SourceOriginalPrimitiveFrobeniusCharpolyRealization']
ths=[];defs=[]
for m in mods:
 f=p/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 s=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',f.read_text(encoding='utf-8'),flags=re.S))
 ns=re.search(r'^namespace (\S+)',s,re.M)[1]
 ths += [ns+'.'+n for n in re.findall(r"^theorem ([\w.']+)",s,re.M)]
 defs += [ns+'.'+n for n in re.findall(r"^(?:noncomputable\s+)?(?:def|abbrev) ([\w.']+)",s,re.M)]
roots=['Dubon2026.SourceFunctionField.OriginalChart.originalPrimitive_continuous_unramified_frobenius_charpoly_realization']
extra=['Dubon2026.SourceFunctionField.OriginalChart.originalPrimitive_continuous_unramified_cyclotomic_realization','Dubon2026.SourceFunctionField.GaussReduction.residue_charP_of_prime_mem_nonunits','Dubon2026.sourceLocal_roots_eq_of_residue_eq','cyclotomicCharacter.spec','PadicInt.ext_of_toZModPow','Matrix.aeval_self_charpoly','Matrix.charpoly_fin_two','Dubon2026.SourceFunctionField.OriginalChart.originalPrimitive_continuous_unramified_frobenius_quadratic_realization']
required=list(dict.fromkeys(ths+extra))
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,proofEdges=required,roots=roots)
def output(name,s):
 f=p/name;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output('source-original-primitive-frobenius-charpoly-5-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda ns:'#['+', '.join('`'+n for n in ns)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
template=(p/'SourceOriginalPrimitiveTateRestrictionAudit8.lean').read_text(encoding='utf-8')
body=template[template.index('private def runPlanarPairingAudit'):template.index('#lint in')]
for key,ns in [('modules',mods),('theorems',ths),('constructions',defs)]:
 body=re.sub(r'let '+key+r' : Array Name := #\[[^\n]*','let '+key+' : Array Name := '+arr(ns),body)
body=body.replace('Primitive Tate Restriction','Primitive Frobenius Charpoly').replace('PRIMITIVE TATE RESTRICTION','PRIMITIVE FROBENIUS CHARPOLY')
output('SourceOriginalPrimitiveFrobeniusCharpolyAudit5.lean',imports+''.join('#print axioms '+n+'\n' for n in cfg['queries'])+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
localClosure=[];todo=mods.copy()
while todo:
 m=todo.pop()
 if m in localClosure:continue
 f=p/(m+'.lean')
 if not f.exists():continue
 localClosure.append(m)
 for line in re.findall(r'^import (.+)$',f.read_text(encoding='utf-8-sig'),re.M):
  for imp in line.split():
   if not imp.startswith(('Mathlib.','Dubon2026.','Lean.')) and (p/(imp+'.lean')).exists():todo.append(imp)
prior=(p/'SourceOriginalPrimitiveTateRestrictionDependencyAudit8.lean').read_text(encoding='utf-8')
dep=prior[prior.index('private def runPlanarPairingDependencyAudit'):]
for key,ns in [('roots',roots),('localModules',localClosure),('required',required)]:
 dep=re.sub(r'let '+key+r' : Array Name := #\[[^\n]*','let '+key+' : Array Name := '+arr(ns),dep)
dep=dep[:dep.index('  logInfo m!')]+'  logInfo m!"SOURCE ORIGINAL PRIMITIVE FROBENIUS CHARPOLY DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the same actual primitive representation consumer. Only declaration values are traversed. The actual source valuation hypothesis gives the residue characteristic, and existing local root separation evaluates the original cyclotomic character on the exact arithmetic Frobenius lift. Native Cayley-Hamilton and the two-dimensional characteristic polynomial determine trace from the independently proved determinant and quadratic identity. The same actual continuous unramified primitive representation retains all original Hecke eigenvalues and specialization equations and now has exact Frobenius determinant, trace and characteristic polynomial. No determinant, root-action, trace or characteristic-polynomial premise is supplied. Integral residual transport, residual association, arithmetic automorphy and all-weight continuation remain required. 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceOriginalPrimitiveFrobeniusCharpolyDependencyAudit5.lean',imports+dep)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
mathlib=Path(r'E:\Lean\Riemann Zeta\.lake\packages\mathlib\Mathlib')
files=[prod/(m+'.lean') for m in ['SourceLocalCyclotomicAction','SourceOriginalTateInertia','SourceHeckePrimeRootReduction','SourceOriginalCyclotomicLocal','SourceOriginalPrimitiveFrobeniusQuadraticRealization','SourceOriginalPrimitiveResidualRealization','SourceStableLatticeResidualRealization']]+[mathlib/m for m in ['NumberTheory/Cyclotomic/CyclotomicCharacter.lean','LinearAlgebra/Matrix/Charpoly/Basic.lean','LinearAlgebra/Matrix/Charpoly/Coeff.lean']]
rd=dict(scope=565,chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> residual association -> actual primitive Frobenius characteristic polynomial -> cyclotomic value at the exact source valuation-subring arithmetic Frobenius and native Cayley-Hamilton',reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in files],shorterRoute='Reuse existing local-domain root separation, the proved residue characteristic from the source nonunit hypothesis, native padic cyclotomic specification at every prime-power root and native Cayley-Hamilton. Add only valuation-ring membership for the required roots and the exact decomposition-subgroup action. The existing norm-model Frobenius theorem was reviewed but its different local interface is not silently substituted. The actual consumer retains its original representation and all prior clauses. For the next residual step, reuse the already constructed original integral lattice, change of basis and entrywise residual realization rather than constructing new lattices or local models.',assumptionsToDischarge='The cyclotomic character at each source arithmetic Frobenius lift is the rational prime. The same representation therefore has determinant p, trace equal to its actual embedded prime Fourier coefficient, and characteristic polynomial X^2-a_p X+p, without determinant, trace or root-action assumptions.',remaining='Integral and residual transport of these identities and inertia, residual association, arithmetic automorphy and all-weight continuation remain required. 16/20; DUB-17--20 OPEN.',scratchImportClosure=localClosure)
output('primitive-frobenius-charpoly-route-565.json',json.dumps(rd,indent=2)+'\n')
print(json.dumps(dict(modules=len(mods),queries=len(cfg['queries']),theorems=len(ths),constructions=len(defs),edges=len(required))))
