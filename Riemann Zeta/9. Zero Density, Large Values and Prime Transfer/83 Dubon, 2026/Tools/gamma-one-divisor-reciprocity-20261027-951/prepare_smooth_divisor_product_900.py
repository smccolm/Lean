from pathlib import Path
import re
p=Path(r'E:\Lean\.tmp\dubon83')
s=(p/'gamma-one-local-model-construction-reuse-889/S_ModularCurve_exists_invariant_localModel_dbarLogDeriv_eq_sum_finsum_translate_of_finiteIndex.lean.txt').read_text(encoding='utf-8-sig')
b=s[s.index('structure Data'):s.index('theorem fac_sm')]
b=b.replace('structure Data','/-- Actual compact dipoles and finite divisor data; no orbit-product conclusion is assumed. -/\nstructure Data')
b=b.replace('Rset (Γ)','projectiveIntegralSubgroup Γ').replace('sm ((δ : Γ) : SL(2, ℤ))','sm (representative Γ δ)')
docs={'hneg':'The integral subgroup contains the central negative identity.','S':'Finite representatives of the prescribed nonzero orders.','n':'The actual invariant integer-order function.','b':'The auxiliary base point outside all chosen orbits.','mS':'Integer multiplicities normalized by stabilizer order.','dip':'Actual compact smooth dipoles at the chosen points.','Fk':'Their antiholomorphic logarithmic derivative coefficients.','Kk':'Their compact supports in the upper half-plane.','hn':'Invariance of the prescribed integer orders.','hcov':'The finite chosen orbits cover all nonzero orders.','hinj':'The chosen representatives have distinct subgroup orbits.','hmS':'Exact stabilizer-normalized integer multiplicity.','hsum':'Degree-zero cancellation of the base-point multiplicity.','hb':'The base point lies outside all chosen full modular orbits.','hKc':'Each dipole support is compact.','hKU':'Every dipole support lies in the upper half-plane.','hd1':'The dipole equals one off its compact support.','hloc':'Each dipole has exactly its zero and pole local integer orders.','hFt':'The coefficient support lies in the same compact set.','hFeq':'The actual dipole logarithmic derivative equals its coefficient away from the pole.'}
for n,d in docs.items():b=b.replace('  '+n+' :','  /-- '+d+' -/\n  '+n+' :',1)
for n,d in [('ex','The actual signed local exponent of a dipole.'),('fac','The dipole translated by an actual projective group representative.'),('Vraw','The locally finite projective orbit product of compact dipoles.'),('V','Fill the removable finite limits of the actual orbit product.')]:
 b=b.replace('def '+n+' ','/-- '+d+' -/\ndef '+n+' ')
c="""theorem fac_sm (s : ℍ) (q : projectiveIntegralSubgroup Γ) (γ : Γ) (z : ℂ) :
    D.fac s q (sm γ z) = D.fac s (q * projection Γ γ) z := by
  simp only [fac, sm, ofComplex_apply, representative_smul]
  change D.dip s (((q • ((projection Γ γ) • ofComplex z) : ℍ) : ℂ)) ^ D.mS s =
    D.dip s ((((q * projection Γ γ) • ofComplex z : ℍ) : ℂ)) ^ D.mS s
  rw [mul_smul]

theorem Vraw_sm (γ : Γ) (z : ℂ) : D.Vraw (sm γ z) = D.Vraw z := by
  simp only [Vraw]
  refine Finset.prod_congr rfl fun s _ => ?_
  exact finprod_eq_of_bijective _ (Equiv.mulRight (projection Γ γ)).bijective
    fun q => D.fac_sm s q γ z

end Data
"""
head="""import SourceSmoothDivisorOrbitData
import SourceSmoothLocalModelProducts
import SourceSmoothModularLogDerivative

/-! DUB-17/18 -> original all-weight arithmetic association -> Gamma1 Picard/H1
-> Abel-Jacobi converse -> analytic reciprocity -> invariant comparison V.
The actual product uses the projective image of the original integral subgroup,
with representatives from the proved projection/fiber equivalence. Its raw
invariance follows by group translation. The data record contains only finite
divisor data and the separately constructed compact dipoles, not the desired
global comparison-function properties. Adapted from the pinned Apache-2.0
scope-889 construction, replacing its positive-matrix representative system. -/
namespace Dubon2026.SourceSmoothDivisor
noncomputable section
open UpperHalfPlane hiding I
open Filter Complex Set
open SourceSmoothProjective SourceSmoothedUnfolding SourceSmoothLocalModel
open scoped MatrixGroups Topology Real
local notation "𝕌" => UpperHalfPlane.upperHalfPlaneSet
local notation "dbar" => SourceComplexReciprocity.DbarFundamental.D

"""
with (p/'SourceSmoothDivisorProduct.lean').open('x',encoding='utf-8',newline='\n') as f:f.write(head+b+c+'end\nend Dubon2026.SourceSmoothDivisor\n')
