from pathlib import Path
import re,json,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
src=p/'gamma-one-local-model-construction-reuse-889/S_ModularCurve_exists_invariant_localModel_dbarLogDeriv_eq_sum_finsum_translate_of_finiteIndex.lean.txt'
s=src.read_text(encoding='utf-8-sig')
b=s[s.index('theorem exists_basePoint'):s.index('section Reps')]
b=b.replace('  refine ⟨iPt y (by linarith), fun s hs γ h => hyB ?_⟩',"""  let b : ℍ := ⟨(y : ℂ) * Complex.I, by simpa using (show 0 < y by linarith)⟩
  refine ⟨b, fun s hs γ h => hyB ?_⟩""")
b=b.replace('  rw [h, im_iPt]','  rw [h]\n  simp [b]')
c=s[s.index('theorem card_fibre_eq_card_stabilizer'):s.index('end Reps')]
head="""import SourceSmoothModularGeometry
import SourceModularSmoothProjectiveRepresentatives
import Dubon2026.SourceModularStabilizerCharacter

/-! DUB-17/18 -> original all-weight arithmetic association -> Gamma1 Picard/H1
-> Abel-Jacobi converse -> analytic reciprocity -> invariant comparison V.
A base point outside the finite union of original modular orbits is chosen.
Actual stabilizer finiteness is inherited from the existing full integral
stabilizer theorem; actual orbit fibers are counted by stabilizers.
These are exactly the multiplicity and cancellation inputs of the dipole
orbit product. No divisor realization or period identity is assumed.
Adapted from the pinned Apache-2.0 scope-889 construction. -/
namespace Dubon2026.SourceSmoothDivisor
noncomputable section
open UpperHalfPlane hiding I
open MeasureTheory Filter Complex Set
open scoped MatrixGroups Topology Real

/-- The stabilizer of any integral subgroup is contained in the proved finite full stabilizer. -/
scoped instance finiteStabilizer (Γ : Subgroup SL(2, ℤ)) (τ : ℍ) :
    Finite (MulAction.stabilizer Γ τ) := by
  letI := SourceFunctionField.StabilizerCharacter.finite_stabilizer τ
  refine Finite.of_injective
    (fun a => (⟨a.val.val, a.property⟩ : MulAction.stabilizer SL(2, ℤ) τ)) ?_
  intro a b h
  exact Subtype.ext (Subtype.ext (congrArg Subtype.val h))

"""
with (p/'SourceSmoothDivisorOrbitData.lean').open('x',encoding='utf-8',newline='\n') as f:f.write(head+b+'variable {Γ : Subgroup SL(2, ℤ)}\n\n'+c+'end\nend Dubon2026.SourceSmoothDivisor\n')
route=dict(primary=dict(path=str(src),sha256=hashlib.sha256(src.read_bytes()).hexdigest().upper()),chain=['DUB-17/18','original all-weight arithmetic association','actual Gamma1 Picard/H1','Abel-Jacobi converse','analytic reciprocity','invariant comparison V','exact orbit multiplicities and compact local factors'],reuse='All of scope-889 primary read. Existing two-element projective kernel and native sigma-fiber/kernel equivalence replace positive-matrix representatives and the source two-copy fiber equivalence. Native finite-support sum currying gives exact factor two; native derivative uniqueness identifies representative derivatives. Existing smooth partition geometry replaces repeated height/proper-discontinuity arguments. Existing full integral stabilizer finiteness gives finite subgroup stabilizers. The source direct orbit-fiber/stabilizer equivalence is retained because it is shorter than transporting general orbit-quotient machinery.',discharged='Local product/removable filling compiled in scope 892; projective orbit fiber cardinality compiled in scope 895. Geometry, orbit-sum and finite orbit data are being assembled. These are not yet audited or promoted; the invariant comparison V remains unconstructed.',remaining='Construct V with exact local orders, global invariance, cusp value one and logarithmic derivative formula, then smooth integral, filled quotient, winding/Petersson comparison, reciprocity, principal-divisor converse and full all-weight chain. 16/20; DUB-17--20 OPEN.')
with (p/'smooth-projective-orbit-route-898.json').open('x',encoding='utf-8') as f:json.dump(route,f,indent=2)
