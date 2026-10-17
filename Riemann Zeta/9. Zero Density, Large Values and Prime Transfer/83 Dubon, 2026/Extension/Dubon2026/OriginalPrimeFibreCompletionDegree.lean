import Dubon2026.OriginalPrimeFibreTower
import Dubon2026.OriginalPrimeFibreDegree
import Dubon2026.OriginalFullIdeleCompletionBaseChange

/-! # Completion degrees on the actual prime fibre

The tower identity supplies the weights in the required nonnormal-base
total comparison. Finiteness is derived from the same Galois overfield.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField
attribute [-instance] UniformSpace.Completion.instSMul

/-- The literal completion degree at a member of the actual prime fibre. -/
def originalPrimeFibreCompletionDegree
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : OriginalPrimeFibre K L v) : ℕ := by
  letI : w.val.asIdeal.LiesOver v.asIdeal := by
    simpa only [w.property] using originalFinitePrimeBelow_liesOver K L w.val
  letI : Algebra (v.adicCompletion K) (w.val.adicCompletion L) :=
    (originalAdicBaseChangeMap K L v w.val).toAlgebra
  exact Module.finrank (v.adicCompletion K) (w.val.adicCompletion L)

/-- At a Galois stage the existing original-prime degree sum has exactly
these literal fibre weights. -/
theorem originalPrimeFibreCompletionDegree_sum_galois
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (v : HeightOneSpectrum (𝓞 K)) :
    (∑ᶠ w : OriginalPrimeFibre K L v, originalPrimeFibreCompletionDegree K L v w) =
      Module.finrank K L :=
  originalFinitePrime_finsum_completion_degree K L v

/-- The same original completion degrees multiply in a tower through an
arbitrary intermediate field of the given finite Galois upper field. -/
theorem originalPrimeFibreCompletionDegree_tower
    (K E M : Type) [Field K] [NumberField K] [Field E] [NumberField E]
    [Field M] [NumberField M] [Algebra K E] [Algebra E M] [Algebra K M]
    [IsScalarTower K E M] [FiniteDimensional K M] [IsGalois K M]
    (v : HeightOneSpectrum (𝓞 K)) (u : OriginalPrimeFibre K E v)
    (t : OriginalPrimeFibre E M u.val) :
    originalPrimeFibreCompletionDegree K M v (originalPrimeFibreTowerEquiv K E M v ⟨u, t⟩) =
      originalPrimeFibreCompletionDegree K E v u * originalPrimeFibreCompletionDegree E M u.val t := by
  letI : u.val.asIdeal.LiesOver v.asIdeal := by
    simpa only [u.property] using originalFinitePrimeBelow_liesOver K E u.val
  letI : t.val.asIdeal.LiesOver u.val.asIdeal := by
    simpa only [t.property] using originalFinitePrimeBelow_liesOver E M t.val
  let w := originalPrimeFibreTowerEquiv K E M v ⟨u, t⟩
  letI : t.val.asIdeal.LiesOver v.asIdeal := by
    simpa only [w.property] using originalFinitePrimeBelow_liesOver K M w.val
  letI : Algebra (v.adicCompletion K) (u.val.adicCompletion E) :=
    (originalAdicBaseChangeMap K E v u.val).toAlgebra
  letI : Algebra (u.val.adicCompletion E) (t.val.adicCompletion M) :=
    (originalAdicBaseChangeMap E M u.val t.val).toAlgebra
  letI : Algebra (v.adicCompletion K) (t.val.adicCompletion M) :=
    (originalAdicBaseChangeMap K M v t.val).toAlgebra
  letI := originalAdicBaseChange_isScalarTower K E M v u.val t.val
  letI : FiniteDimensional (v.adicCompletion K) (t.val.adicCompletion M) :=
    (originalAdicBaseChange_finite_galois K M v t.val).1
  exact (Module.finrank_mul_finrank (v.adicCompletion K)
    (u.val.adicCompletion E) (t.val.adicCompletion M)).symm

end
end Dubon2026
