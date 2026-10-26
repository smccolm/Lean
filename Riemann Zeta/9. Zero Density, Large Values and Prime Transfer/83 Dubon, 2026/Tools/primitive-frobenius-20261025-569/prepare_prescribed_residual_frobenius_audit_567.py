from pathlib import Path
import json,re,hashlib
p=Path(__file__).parent
prod=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
mods=['SourceOriginalPrescribedTateSpecialization','SourceOriginalPrescribedResidualFrobenius']
ths=[];defs=[]
for m in mods:
 f=p/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 s=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',f.read_text(encoding='utf-8'),flags=re.S))
 ns=re.search(r'^namespace (\S+)',s,re.M)[1]
 ths += [ns+'.'+n for n in re.findall(r"^theorem ([\w.']+)",s,re.M)]
 defs += [ns+'.'+n for n in re.findall(r"^(?:noncomputable\s+)?(?:def|abbrev) ([\w.']+)",s,re.M)]
roots=['Dubon2026.SourceFunctionField.OriginalChart.originalPrimitive_prescribed_residual_frobenius_realization']
extra=['Dubon2026.SourceFunctionField.OriginalChart.originalPadicHeckeEigencharacter','Dubon2026.SourceFunctionField.OriginalChart.originalPadicHeckeEigencharacter_prime','Dubon2026.SourceFunctionField.OriginalChart.originalRationalTate_explicit_continuous_galois','Dubon2026.rankTwoCoefficientGaloisRep_continuous','Dubon2026.rankTwoCoefficientMap_span','Dubon2026.rankTwoCoefficientMap_smul','Dubon2026.rankTwoCoefficientGaloisRep_action','Dubon2026.SourceFunctionField.original_tate_free_finite_rank','Dubon2026.padicSpecialization_stable_lattice','Dubon2026.stableLattice_integral_residual_realization','Dubon2026.SourceFunctionField.OriginalChart.original_residual_inertia_identity','Dubon2026.SourceFunctionField.OriginalChart.original_residual_frobenius_charpoly','Dubon2026.padicCoefficientResidue_charP','Dubon2026.localCoefficientResidue_finite_discrete','IsModuleTopology.continuous_of_linearMap']
required=list(dict.fromkeys(ths+extra))
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,proofEdges=required,roots=roots)
def output(name,s):
 f=p/name;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output('source-original-prescribed-residual-frobenius-2-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda ns:'#['+', '.join('`'+n for n in ns)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
template=(p/'SourceOriginalPrimitiveTateRestrictionAudit8.lean').read_text(encoding='utf-8')
body=template[template.index('private def runPlanarPairingAudit'):template.index('#lint in')]
for key,ns in [('modules',mods),('theorems',ths),('constructions',defs)]:
 body=re.sub(r'let '+key+r' : Array Name := #\[[^\n]*','let '+key+' : Array Name := '+arr(ns),body)
body=body.replace('Primitive Tate Restriction','Prescribed Residual Frobenius').replace('PRIMITIVE TATE RESTRICTION','PRESCRIBED RESIDUAL FROBENIUS')
output('SourceOriginalPrescribedResidualFrobeniusAudit2.lean',imports+''.join('#print axioms '+n+'\n' for n in cfg['queries'])+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
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
dep=dep[:dep.index('  logInfo m!')]+'  logInfo m!"SOURCE ORIGINAL PRESCRIBED RESIDUAL FROBENIUS DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the same actual primitive representation consumer. Only declaration values are traversed. The original p-adic Hecke eigencharacter retains any supplied embedding of the original Fourier field through the already constructed continuous rank-two Tate action. Existing coefficient change gives the same prescribed eigenvalues and spanning specialization. The actual finite original Tate module constructs a stable integral lattice; its existing basis and entrywise reduction give continuous integral and residual representations. The same resulting representations satisfy the proved source Frobenius polynomial, residual trace and determinant, and inertia identities. Local coefficient-field structure and its supplied embedding are explicit upstream inputs to this prescribed construction; no representation, lattice or local-compatibility theorem is assumed. Choosing that embedding to match a prescribed source algebraic-integer reduction, source arithmetic quotient and norm-interface comparison, residual association, arithmetic automorphy and all-weight continuation remain required. 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceOriginalPrescribedResidualFrobeniusDependencyAudit2.lean',imports+dep)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
files=[prod/(m+'.lean') for m in ['SourceOriginalPrimitiveTateSpecialization','SourceOriginalFinitePadicSpecialization','SourceOriginalPadicEigencharacter','SourceOriginalExplicitHeckeGalois','SourceRankTwoCoefficientSpecialization','SourcePadicSpecializationLattice','SourceStableLatticeResidualRealization','SourcePrimitiveGaloisAlternative','IntegralCoefficientEmbedding','RationalPrimeOriginalResidueCard']]
rd=dict(scope=567,chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> all-weight residual association -> prescribed algebraic-integer reduction compatibility -> retain a prescribed Fourier-field embedding through actual Tate specialization, integral lattice and residual Frobenius realization',reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in files],shorterRoute='The existing originalPadicHeckeEigencharacter already accepts any prescribed Fourier-field embedding. Apply it directly to the existing explicit continuous rank-two Tate realization and native coefficient-change maps. Reuse the actual finite Tate module and existing stable-lattice/residual construction, keeping the supplied embedding rather than using an existential wrapper that forgets it. The previous pointwise Frobenius and inertia consumers then apply unchanged. No new Hecke algebra, Tate geometry, coefficient representation or lattice theory is built. IntegralCoefficientEmbedding was reviewed for the next prescribed-reduction step: it constructs a place from an embedding, so it does not by itself supply an embedding compatible with a specified reduction. The native rational completion/p-adic equivalence used in RationalPrimeOriginalResidueCard is a candidate for the required completion route, not yet claimed consumed here.',assumptionsToDischarge='Given a genuine local coefficient field with its valuation extending the Tate-prime valuation and a specified embedding of the actual Fourier field, construct continuous original integral and residual representations with exactly that embedding in every prime eigenvalue and the derived original Frobenius/inertia identities. No representation, lattice, residue action or local-compatibility assumption is supplied.',remaining='Choosing the local coefficient embedding to match a prescribed source algebraic-integer reduction remains required. Source arithmetic quotient and norm-interface comparison, residual association, arithmetic automorphy and all-weight continuation remain required. 16/20; DUB-17--20 OPEN.',scratchImportClosure=localClosure)
output('prescribed-residual-frobenius-route-567.json',json.dumps(rd,indent=2)+'\n')
print(json.dumps(dict(modules=len(mods),queries=len(cfg['queries']),theorems=len(ths),constructions=len(defs),edges=len(required))))
