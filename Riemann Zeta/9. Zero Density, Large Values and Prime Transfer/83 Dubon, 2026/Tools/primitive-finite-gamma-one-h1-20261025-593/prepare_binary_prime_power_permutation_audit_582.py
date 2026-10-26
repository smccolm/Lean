from pathlib import Path
import json,re,hashlib
p=Path(__file__).parent
prod=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
mods=['SourcePermutationCoefficientQuotient', 'SourceBinaryPrimePowerPermutation', 'SourceBinaryPermutationHecke', 'SourceBinaryPermutationCongruence', 'SourceIntegralBinaryPermutationRealization']
ths=[];defs=[]
for m in mods:
 f=p/(m+'.lean')
 assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 s=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',f.read_text(encoding='utf-8'),flags=re.S))
 ns=re.search(r'^namespace (\S+)',s,re.M)[1]
 ths += [ns+'.'+n for n in re.findall(r"^theorem ([\w.']+)",s,re.M)]
 defs += [ns+'.'+n for n in re.findall(r"^(?:noncomputable\s+)?(?:def|abbrev) ([\w.']+)",s,re.M)]
roots=['Dubon2026.sourceIntegralBinary_exists_primePowerPermutationRealization']
extra=['Dubon2026.sourceGamma0H1_map_surjective', 'Dubon2026.sourcePrimeHeckeH1_naturality', 'Dubon2026.sourceBinaryHeckeDiagonal_intertwine', 'Dubon2026.sourceBinaryH1Change_hecke', 'Dubon2026.binaryHomogeneousMonomialBasis', 'Finsupp.linearCombination', 'Dubon2026.sourceBinaryH1Change']
separate=[]
required=list(dict.fromkeys([n for n in ths+defs if n not in separate]+extra))
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,proofEdges=required,roots=roots,separatelyAxiomChecked=separate)
def output(name,s):
 f=p/name;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output('source-binary-prime-power-permutation-5-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda ns:'#['+', '.join(chr(96)+n for n in ns)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
template=(p/'SourceOriginalPrimitiveTateRestrictionAudit8.lean').read_text(encoding='utf-8')
body=template[template.index('private def runPlanarPairingAudit'):template.index('#lint in')]
for key,ns in [('modules',mods),('theorems',ths),('constructions',defs)]:
 body=re.sub(r'let '+key+r' : Array Name := #\[[^\n]*','let '+key+' : Array Name := '+arr(ns),body)
body=body.replace('SOURCE ORIGINAL PRIMITIVE TATE RESTRICTION','SOURCE BINARY PRIME POWER PERMUTATION')
output('SourceBinaryPrimePowerPermutationAudit5.lean',imports+''.join('#print axioms '+n+'\n' for n in cfg['queries'])+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
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
dep=dep[:dep.index('  logInfo m!')]+ '  logInfo m!"SOURCE BINARY PRIME POWER PERMUTATION DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the actual original integral binary H1 prime-power consumer. Only declaration values are traversed. The finite permutation module is built on the actual coefficient vectors, evaluation is surjective on native H1, principal congruence acts trivially, and all original prime Hecke transforms are retained. The original full Hecke naturality and Gamma0 H2-vanishing surjection are reused. No eigenvector lift, geometric Galois realization, compatible adic specialization or all-weight association is asserted. DUB-17--20 OPEN; 16/20."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceBinaryPrimePowerPermutationDependencyAudit5.lean',imports+dep)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
files=[prod/n for n in ['SourceGamma0H1Surjection.lean','SourcePrimeHeckeNaturality.lean','SourceBinaryHeckeCohomology.lean','SourceBinaryHeckeChange.lean','SourceIntegralCohomologyFinite.lean','HomogeneousMonomialBasis.lean']]
math=Path(r'E:\Lean\Riemann Zeta\.lake\packages\mathlib\Mathlib')
files += [math/n for n in ['RepresentationTheory/Rep/Basic.lean','LinearAlgebra/Finsupp/LinearCombination.lean','Data/ZMod/Basic.lean','NumberTheory/ModularForms/CongruenceSubgroups.lean']]
rd=dict(scope=582,chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero Galois association -> compatible prime-power Hecke realizations -> original integral binary H1 as a Hecke-equivariant quotient of finite congruence permutation coefficients',reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in files],shorterRoute='Native finite-support linearization and evaluation avoid a Vandermonde or pure-power spanning development. Existing Gamma0 H2 vanishing gives H1 surjectivity directly when six is invertible. Existing full prime Hecke naturality supplies compatibility without rebuilding coset traces. Native congruence reduction identifies the principal congruence action. No new general local-duality, Selmer, deformation-ring or geometric theory is introduced.',assumptionsToDischarge='Construct the actual finite permutation coefficient module modulo every positive power of every prime greater than three, prove evaluation surjectivity on the original native binary H1 and exact compatibility with original prime Hecke transforms, and prove that the principal congruence subgroup acts trivially. Every degree and original integral class is retained.',remaining='The preimage class is not asserted to be an eigenvector. A compatible family of finite-level Hecke specializations with an actual geometric Galois realization is still needed; neither the characteristic-zero point nor all-weight association follows from this quotient alone. Required local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain open. The route assessment is a mathematical inference using local proved results, not an external claim of a completed alternative construction. 16/20; DUB-17--20 OPEN.',scratchImportClosure=localClosure,separatelyAxiomChecked=[],renewedExternalReview='reuse-20261025-579/reuse-assessment.json')
output('binary-prime-power-permutation-route-582.json',json.dumps(rd,indent=2)+'\n')
print(json.dumps(dict(modules=len(mods),queries=len(cfg['queries']),theorems=len(ths),constructions=len(defs),edges=len(required))))
