import Dubon2026.SourceCurveFiberPrimes
import Dubon2026.SourceCurveResidueRestrictionConstants

/-! Every actual base place has an extension place. Thus rational upper
residue fields give rational residues at every base place, with no extra
base hypothesis in the global residue/trace assembly for DUB-17/18. -/

noncomputable section

namespace Dubon2026.SourceCurve.Place

open IsDedekindDomain IsLocalRing

variable {K F E : Type*} [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
  [FiniteDimensional F E] [Algebra.IsSeparable F E] (v : Place K F)

/-- Lying over on the actual integral-closure chart produces an extension place. -/
theorem exists_fiberPlace : ∃ w : Place K E, w.restrict F = v := by
  let P := Classical.choice (inferInstance : Nonempty
    (Ideal.primesOver (maximalIdeal v.toValuationSubring) (integralClosureAt E v)))
  let Q : HeightOneSpectrum (integralClosureAt E v) :=
    ⟨P.1, P.2.1, Ideal.ne_bot_of_mem_primesOver v.maximalIdeal_ne_bot P.2⟩
  exact ⟨fiberPrimePlace E v Q, restrict_fiberPrimePlace v Q⟩

/-- Rational residues in the actual upper field force rational residues at every base place. -/
theorem residue_bijective_of_all_upper
    (htop : ∀ w : Place K E, Function.Bijective (algebraMap K w.ResidueField)) :
    Function.Bijective (algebraMap K v.ResidueField) := by
  obtain ⟨w, hw⟩ := v.exists_fiberPlace (E := E)
  refine ⟨(algebraMap K v.ResidueField).injective, ?_⟩
  rw [← hw]
  exact w.residue_algebraMap_surjective_restrict (htop w).surjective

end Dubon2026.SourceCurve.Place
