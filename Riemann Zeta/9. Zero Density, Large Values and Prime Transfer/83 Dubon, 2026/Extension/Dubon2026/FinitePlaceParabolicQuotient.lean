import Dubon2026.ParabolicResidueAmbientQuotient
import Dubon2026.OriginalAdicCompletionResidue

/-! # The original finite-place auxiliary quotient

This applies the local parabolic construction to the actual completed
valuation ring at a number-field prime. The existing repository residue
comparison supplies the original global residue field and its finiteness.
The last index is explicitly Fin.last, as in BLGG Sections 3.2 and 3.6.
-/

namespace Dubon2026

noncomputable section

open NumberField IsDedekindDomain
open scoped NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- The actual finite-place U0/U1 is the unit group of the original arithmetic residue field. -/
def finitePlaceParabolicQuotientEquiv (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    parabolicResidueLevelZero (Valued.integer (v.adicCompletion K)) (Fin.last n) ⧸
      (parabolicResidueLevelOneAmbient (Valued.integer (v.adicCompletion K)) (Fin.last n)).subgroupOf
        (parabolicResidueLevelZero (Valued.integer (v.adicCompletion K)) (Fin.last n)) ≃*
          (𝓞 K ⧸ v.asIdeal)ˣ :=
  (parabolicResidueAmbientQuotientEquiv (Valued.integer (v.adicCompletion K)) (Fin.last n)).trans
    (Units.mapEquiv (originalRingOfIntegersQuotientEquivAdicResidueField K v).symm.toMulEquiv)

/-- The actual finite-place auxiliary quotient has its finiteness proved from the number field. -/
theorem finitePlaceParabolicQuotient_finite (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Finite (parabolicResidueLevelZero (Valued.integer (v.adicCompletion K)) (Fin.last n) ⧸
      (parabolicResidueLevelOneAmbient (Valued.integer (v.adicCompletion K)) (Fin.last n)).subgroupOf
        (parabolicResidueLevelZero (Valued.integer (v.adicCompletion K)) (Fin.last n))) := by
  letI := original_finite_adicCompletion_residueField K v
  exact parabolicResidueAmbientQuotient_finite (Valued.integer (v.adicCompletion K)) (Fin.last n)

end
end Dubon2026
