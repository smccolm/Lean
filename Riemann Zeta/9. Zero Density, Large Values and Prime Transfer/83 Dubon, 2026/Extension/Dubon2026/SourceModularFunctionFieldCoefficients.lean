import Dubon2026.SourceModularJTranscendence
import Dubon2026.SourceLaurentCoefficientReindex

/-! DUB-17/18 -> higher symmetric-power continuation -> modular residual
association -> original Frobenius/inertia identities -> reduction of the
original modular curve. The residue-characteristic function field must
use the literal integral j expansions; it cannot carry a rational-field
algebra structure. Existing coefficient maps and transcendence suffice
for this source object, without a second j-series construction.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
Definitions/Def_ModularCurve_X0ModL.lean, FunctionField section. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open IntermediateField

/-- Actual divisor j expansions over an arbitrary coefficient ring. -/
def divisorExpansionsCoeff (N : ℕ) (R : Type*) [CommRing R] : Set (LaurentSeries R) :=
  {x | ∃ (d : ℕ) (_ : NeZero d), d ∣ N ∧ x = qExpand R d (jqModC R)}

/-- The source full modular function field, including in residue characteristic. -/
def modularFunctionFieldCoeff (N : ℕ) (K : Type*) [Field K] :
    IntermediateField K (LaurentSeries K) :=
  IntermediateField.adjoin K (divisorExpansionsCoeff N K)

variable (N : ℕ) (K : Type*) [Field K]

theorem jqd_mem_coeff_field {d : ℕ} [NeZero d] (hd : d ∣ N) :
    qExpand K d (jqModC K) ∈ modularFunctionFieldCoeff N K :=
  subset_adjoin K _ ⟨d, ‹_›, hd, rfl⟩

theorem jq_mem_coeff_field : jqModC K ∈ modularFunctionFieldCoeff N K := by
  have h := jqd_mem_coeff_field N K (one_dvd N)
  rwa [qExpand_one_apply] at h

/-- The literal j coordinate in the source coefficient function field. -/
def jCoeff : modularFunctionFieldCoeff N K := ⟨jqModC K, jq_mem_coeff_field N K⟩

theorem transcendental_jCoeff : Transcendental K (jCoeff N K) := by
  intro h
  exact transcendental_jqModC K (h.algebraMap (A := LaurentSeries K))

end
end Dubon2026.SourceFunctionField
