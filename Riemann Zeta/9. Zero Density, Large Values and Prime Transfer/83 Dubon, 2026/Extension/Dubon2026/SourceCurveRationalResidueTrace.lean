import Dubon2026.SourceCurveRationalFunctionEvaluation
import Mathlib.RingTheory.Trace.Basic

/-! DUB-17/18 -> cover prescribed residues. Trace of the actual regular
residue equals rational residue evaluation when the residue map is bijective. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable (v : Place K F) (hv : Function.Bijective (algebraMap K v.ResidueField))

theorem trace_residue_eq_rationalEval (h : F) (hh : h ∈ v.toValuationSubring) :
    Algebra.trace K v.ResidueField (IsLocalRing.residue v.toValuationSubring ⟨h, hh⟩) =
      v.rationalEval hv h := by
  have he : algebraMap K v.ResidueField (v.rationalEval hv h) =
      IsLocalRing.residue v.toValuationSubring ⟨h, hh⟩ := by
    rw [v.rationalEval_of_mem hv hh]
    exact (RingEquiv.ofBijective (algebraMap K v.ResidueField) hv).apply_symm_apply _
  rw [← he, Algebra.trace_algebraMap, Module.finrank_of_bijective_algebraMap hv, one_smul]

end
end Dubon2026.SourceCurve.Place
