import Dubon2026.OriginalGlobalCompletionH2
import Dubon2026.OriginalAdicCompletionTower
import Dubon2026.GaloisUnitBaseChange

/-! # Literal global and local Galois restriction commute with base change

Both routes act on the same original field elements. The original
completion embedding and actual Galois restriction identities prove the
square, without an assumed compatibility certificate. This is the group
map needed to transfer finite local H2 killing to the original global
class in DUB-17's invariant sum-zero argument.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
attribute [-instance] UniformSpace.Completion.instSMul
variable (K E L M : Type) [Field K] [NumberField K] [Field E] [NumberField E]
  [Field L] [NumberField L] [Field M] [NumberField M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M]
  [FiniteDimensional K L] [FiniteDimensional E M] [IsGalois K L] [IsGalois E M]
  (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 E))
  (w : HeightOneSpectrum (𝓞 L)) (t : HeightOneSpectrum (𝓞 M))
  [u.asIdeal.LiesOver v.asIdeal] [w.asIdeal.LiesOver v.asIdeal]
  [t.asIdeal.LiesOver v.asIdeal] [t.asIdeal.LiesOver u.asIdeal] [t.asIdeal.LiesOver w.asIdeal]

/-- Restricting original completion automorphisms to original fields commutes with the actual change of base. -/
theorem originalCompletionGaloisRestriction_baseChange :
  letI : Algebra (v.adicCompletion K) (u.adicCompletion E) :=
    (originalAdicBaseChangeMap K E v u).toAlgebra
  letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
    (originalAdicBaseChangeMap K L v w).toAlgebra
  letI : Algebra (v.adicCompletion K) (t.adicCompletion M) :=
    (originalAdicBaseChangeMap K M v t).toAlgebra
  letI : Algebra (u.adicCompletion E) (t.adicCompletion M) :=
    (originalAdicBaseChangeMap E M u t).toAlgebra
  letI : Algebra (w.adicCompletion L) (t.adicCompletion M) :=
    (originalAdicBaseChangeMap L M w t).toAlgebra
  letI := originalAdicBaseChange_isScalarTower K E M v u t
  letI := originalAdicBaseChange_isScalarTower K L M v w t
  letI := (originalAdicBaseChange_finite_galois K L v w).2
  ∀ σ : Gal(t.adicCompletion M/u.adicCompletion E),
    originalCompletionGaloisRestriction K L v w
      (galoisBaseChangeRestriction (v.adicCompletion K) (u.adicCompletion E)
        (w.adicCompletion L) (t.adicCompletion M) σ) =
      galoisBaseChangeRestriction K E L M (originalCompletionGaloisRestriction E M u t σ) := by
  letI : Algebra (v.adicCompletion K) (u.adicCompletion E) :=
    (originalAdicBaseChangeMap K E v u).toAlgebra
  letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
    (originalAdicBaseChangeMap K L v w).toAlgebra
  letI : Algebra (v.adicCompletion K) (t.adicCompletion M) :=
    (originalAdicBaseChangeMap K M v t).toAlgebra
  letI : Algebra (u.adicCompletion E) (t.adicCompletion M) :=
    (originalAdicBaseChangeMap E M u t).toAlgebra
  letI : Algebra (w.adicCompletion L) (t.adicCompletion M) :=
    (originalAdicBaseChangeMap L M w t).toAlgebra
  letI := originalAdicBaseChange_isScalarTower K E M v u t
  letI := originalAdicBaseChange_isScalarTower K L M v w t
  letI := (originalAdicBaseChange_finite_galois K L v w).2
  intro σ
  apply AlgEquiv.ext
  intro x
  apply (algebraMap L M).injective
  apply (algebraMap M (t.adicCompletion M)).injective
  calc
    algebraMap M (t.adicCompletion M) (algebraMap L M
        (originalCompletionGaloisRestriction K L v w
          (galoisBaseChangeRestriction (v.adicCompletion K) (u.adicCompletion E)
            (w.adicCompletion L) (t.adicCompletion M) σ) x)) =
      originalAdicBaseChangeMap L M w t
        (algebraMap L (w.adicCompletion L)
          (originalCompletionGaloisRestriction K L v w
            (galoisBaseChangeRestriction (v.adicCompletion K) (u.adicCompletion E)
              (w.adicCompletion L) (t.adicCompletion M) σ) x)) :=
      (originalAdicBaseChangeMap_algebraMap L M w t _).symm
    _ = σ (originalAdicBaseChangeMap L M w t (algebraMap L (w.adicCompletion L) x)) := by
      rw [originalCompletionGaloisRestriction_commutes]
      exact galoisBaseChangeRestriction_commutes (v.adicCompletion K) (u.adicCompletion E)
        (w.adicCompletion L) (t.adicCompletion M) σ _
    _ = σ (algebraMap M (t.adicCompletion M) (algebraMap L M x)) := by
      rw [originalAdicBaseChangeMap_algebraMap]
    _ = algebraMap M (t.adicCompletion M)
        (algebraMap L M (galoisBaseChangeRestriction K E L M
          (originalCompletionGaloisRestriction E M u t σ) x)) := by
      rw [galoisBaseChangeRestriction_commutes, originalCompletionGaloisRestriction_commutes]

end
end Dubon2026
