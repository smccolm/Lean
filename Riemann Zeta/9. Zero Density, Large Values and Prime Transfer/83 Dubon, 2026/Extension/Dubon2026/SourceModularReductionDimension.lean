import Dubon2026.SourceReductionDimension
import Dubon2026.SourceModularReductionCoordinate

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> genus
comparison. The actual modular Gauss valuation and residue map instantiate
the prolongation theorem. Every finite-dimensional space of original modular
functions has a residue span of the same dimension, using the proved literal
j coordinate and its equal positive degrees. No abstract prolongation or
degree-equality hypothesis remains on this consumer. Genus and place
comparison still require separate proofs. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
variable {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L) (N : ℕ) [NeZero N]
variable (hNL : (N : L) ≠ 0) (hNk : (N : IsLocalRing.ResidueField A) ≠ 0)
local notation "FF" => modularFunctionFieldCoeff N L
local notation "kk" => IsLocalRing.ResidueField A
local notation "Fb" => modularFunctionFieldCoeff N kk

/-- The canonical constant-field algebra, made explicit to avoid unrelated tower searches. -/
local instance residueModularAlgebra : Algebra kk Fb :=
  (modularFunctionFieldCoeff N kk).toSubalgebra.algebra

/-- The regular prolongation given by the actual modular Gauss valuation and coefficient reduction. -/
def modularRegularProlongation : SourceCurve.RegularProlongation A FF Fb where
  integers := gaussRing A N
  residue := modularResidueHom A N hNL hNk
  algebraMap_mem_iff := algebraMap_mem_gaussRing_iff A N
  residue_surjective := modularResidueHom_surjective A N hNL hNk
  ker_residue := ker_modularResidueHom A N hNL hNk
  residue_algebraMap := fun a => modularResidueHom_algebraMap A N hNL hNk a _
  exists_smul_mem := exists_smul_mem_modularResidueHom A N hNL hNk

theorem finrank_modular_residue_span (V : Submodule L FF) [FiniteDimensional L V] :
    Module.finrank kk (Submodule.span kk
      {h : Fb | ∃ f : gaussRing A N, (f : FF) ∈ V ∧ modularResidueHom A N hNL hNk f = h}) =
      Module.finrank L V := by
  obtain ⟨x, hx, hfin, hdeg⟩ := exists_reduction_coordinate A N hNL hNk
  exact SourceCurve.RegularProlongation.finrank_span_residue_eq_finrank'
    (modularRegularProlongation A N hNL hNk) x hx hfin hdeg V

end
end Dubon2026.SourceFunctionField.GaussReduction
