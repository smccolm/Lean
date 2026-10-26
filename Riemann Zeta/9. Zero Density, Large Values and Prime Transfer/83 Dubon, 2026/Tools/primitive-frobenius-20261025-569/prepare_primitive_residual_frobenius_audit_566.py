from pathlib import Path
import json,re,hashlib
p=Path(__file__).parent
prod=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
mods=['SourceMatrixIntertwinerCharpoly','SourceIntegralMatrixCharpoly','SourceRankTwoCharpolyCoefficients','SourceOriginalSpecializationFrobeniusCharpoly','SourceOriginalResidualFrobeniusCharpoly','SourceOriginalResidualInertia','SourceOriginalPrimitiveResidualFrobeniusRealization']
ths=[];defs=[]
for m in mods:
 f=p/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 s=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',f.read_text(encoding='utf-8'),flags=re.S))
 ns=re.search(r'^namespace (\S+)',s,re.M)[1]
 ths += [ns+'.'+n for n in re.findall(r"^theorem ([\w.']+)",s,re.M)]
 defs += [ns+'.'+n for n in re.findall(r"^(?:noncomputable\s+)?(?:def|abbrev) ([\w.']+)",s,re.M)]
roots=['Dubon2026.SourceFunctionField.OriginalChart.originalPrimitive_continuous_residual_frobenius_realization']
extra=['Dubon2026.SourceFunctionField.OriginalChart.originalPrimitive_continuous_residual_realization','Dubon2026.SourceFunctionField.OriginalChart.original_specialization_cyclotomic_determinant','Dubon2026.SourceFunctionField.OriginalChart.original_specialization_inertia_identity','Dubon2026.SourceFunctionField.OriginalChart.original_specialization_quadratic','Dubon2026.SourceFunctionField.GaussReduction.originalRationalTateGaloisRep_frobenius_quadratic_away','Dubon2026.cyclotomic_frobenius_charpoly','Dubon2026.sourcePrimitiveCoefficient_valuation_le_one','Dubon2026.stableLattice_integral_residual_realization','LinearEquiv.charpoly_conj','Matrix.charpoly_map','Polynomial.map_injective','Matrix.map_injective']
required=list(dict.fromkeys(ths+extra))
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,proofEdges=required,roots=roots)
def output(name,s):
 f=p/name;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output('source-original-primitive-residual-frobenius-7-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda ns:'#['+', '.join('`'+n for n in ns)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
template=(p/'SourceOriginalPrimitiveTateRestrictionAudit8.lean').read_text(encoding='utf-8')
body=template[template.index('private def runPlanarPairingAudit'):template.index('#lint in')]
for key,ns in [('modules',mods),('theorems',ths),('constructions',defs)]:
 body=re.sub(r'let '+key+r' : Array Name := #\[[^\n]*','let '+key+' : Array Name := '+arr(ns),body)
body=body.replace('Primitive Tate Restriction','Primitive Residual Frobenius').replace('PRIMITIVE TATE RESTRICTION','PRIMITIVE RESIDUAL FROBENIUS')
output('SourceOriginalPrimitiveResidualFrobeniusAudit7.lean',imports+''.join('#print axioms '+n+'\n' for n in cfg['queries'])+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
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
dep=dep[:dep.index('  logInfo m!')]+'  logInfo m!"SOURCE ORIGINAL PRIMITIVE RESIDUAL FROBENIUS DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the same actual primitive representation consumer. Only declaration values are traversed. The existing constructed integral and residual primitive representations retain their actual finite local coefficient field, continuity, spanning Hecke specialization, original arithmetic action, lattice change of basis and literal entrywise residue map. Original Tate inertia transfers to these same integral and residual actions. The separately proved cyclotomic determinant and original quadratic give the field Frobenius polynomial; native conjugacy and injective polynomial coefficient extension descend it to the actual integral matrix. Entrywise reduction gives the residual polynomial, trace and determinant with the original integral Fourier coefficient. No new lattice, residue map, inertia, determinant, trace or characteristic-polynomial hypothesis is supplied by the assembled consumer. Prescribed coefficient-reduction compatibility, comparison to the source arithmetic quotient and local norm interfaces, residual association, arithmetic automorphy and all-weight continuation remain required. 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceOriginalPrimitiveResidualFrobeniusDependencyAudit7.lean',imports+dep)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
mathlib=Path(r'E:\Lean\Riemann Zeta\.lake\packages\mathlib\Mathlib')
files=[prod/(m+'.lean') for m in ['SourceOriginalPrimitiveResidualRealization','SourceOriginalPrimitiveIntegralLattice','SourceStableLatticeResidualRealization','SourcePadicResidualLocalConsumer','SourceOriginalSpecializationInertia','SourceOriginalSpecializationQuadratic','SourcePrimitiveLocalCoefficients','SourcePrimitiveResidualHeckeCharacter','SourcePrimitiveGaloisAlternative','SourceOriginalFinitePadicSpecialization','SourceOriginalPadicEigencharacter']]+[mathlib/m for m in ['LinearAlgebra/Charpoly/ToMatrix.lean','LinearAlgebra/Matrix/Charpoly/Basic.lean','LinearAlgebra/Matrix/Charpoly/Coeff.lean']]
rd=dict(scope=566,chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> residual association -> exact Frobenius and inertia compatibility for the existing actual primitive integral and residual representations -> original Tate specialization, integral coefficient and lattice basis comparison',reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in files],shorterRoute='Reuse the existing original primitive residual realization rather than constructing another local coefficient field or stable lattice. Its original spanning specialization lets the proved determinant, Frobenius quadratic and inertia theorems apply to that same representation. Native linear-equivalence conjugacy, injectivity of polynomial coefficient extension and Matrix.charpoly_map transport the polynomial through the existing basis and residue map. The original Fourier coefficient integrality supplies its exact integral lift. For the next all-weight source branch, inspected SourcePrimitiveGaloisAlternative and SourceOriginalFinitePadicSpecialization: compatibility with a prescribed reduction remains required; the existing originalPadicHeckeEigencharacter already accepts a prescribed coefficient embedding, so that narrower route is available without rebuilding the Tate geometry.',assumptionsToDischarge='The existing integral and residual representations are trivial on source inertia away from the level and Tate prime. The original field Frobenius polynomial descends to the actual integral basis and reduces to the exact original Fourier residue polynomial. The residual trace and determinant follow in the actual finite characteristic-ell residue field. The assembled consumer supplies every specialization, lattice-basis and residue-map premise from the existing genuine construction.',remaining='Prescribed coefficient-reduction compatibility, comparison to the source arithmetic quotient and local norm interfaces, residual association, arithmetic automorphy and all-weight continuation remain required. 16/20; DUB-17--20 OPEN.',scratchImportClosure=localClosure)
output('primitive-residual-frobenius-route-566.json',json.dumps(rd,indent=2)+'\n')
print(json.dumps(dict(modules=len(mods),queries=len(cfg['queries']),theorems=len(ths),constructions=len(defs),edges=len(required))))
