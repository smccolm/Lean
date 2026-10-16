import Dubon2026.OriginalCompletionCarryInvariant

/-! # Original completion restriction agrees with ambient localization

Both restrictions act on the same original number-field elements. The
existing completion restriction identity and literal scalar towers prove
their equality. This is the group-map comparison needed to identify
DUB-17's Mackey localization with the existing finite-global invariant.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] UniformSpace.Completion.instSMul
attribute [local instance] originalCompletionCarryAlgebra originalCompletionCarryGalois

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  (Ω : Type) [Field Ω] [Algebra K Ω] [Algebra L Ω]
  [Algebra (v.adicCompletion K) Ω] [Algebra (w.adicCompletion L) Ω]
  [IsScalarTower K L Ω] [IsScalarTower K (v.adicCompletion K) Ω]
  [IsScalarTower L (w.adicCompletion L) Ω]
  [IsScalarTower (v.adicCompletion K) (w.adicCompletion L) Ω]

/-- Restriction through the genuine completion and direct ambient restriction agree on every original automorphism. -/
theorem originalCompletionGaloisRestriction_ambient
    (g : Gal(Ω/v.adicCompletion K)) :
    originalCompletionGaloisRestriction K L v w
      (galoisBaseChangeRestriction (v.adicCompletion K) (v.adicCompletion K)
        (w.adicCompletion L) Ω g) =
      galoisBaseChangeRestriction K (v.adicCompletion K) L Ω g := by
  apply AlgEquiv.ext
  intro x
  apply (algebraMap L Ω).injective
  calc
    algebraMap L Ω (originalCompletionGaloisRestriction K L v w
        (galoisBaseChangeRestriction (v.adicCompletion K) (v.adicCompletion K)
          (w.adicCompletion L) Ω g) x) =
      algebraMap (w.adicCompletion L) Ω
        (algebraMap L (w.adicCompletion L)
          (originalCompletionGaloisRestriction K L v w
            (galoisBaseChangeRestriction (v.adicCompletion K) (v.adicCompletion K)
              (w.adicCompletion L) Ω g) x)) :=
      IsScalarTower.algebraMap_apply L (w.adicCompletion L) Ω _
    _ = g (algebraMap (w.adicCompletion L) Ω (algebraMap L (w.adicCompletion L) x)) := by
      rw [originalCompletionGaloisRestriction_commutes]
      exact galoisBaseChangeRestriction_commutes (v.adicCompletion K) (v.adicCompletion K)
        (w.adicCompletion L) Ω g _
    _ = g (algebraMap L Ω x) := by
      rw [← IsScalarTower.algebraMap_apply L (w.adicCompletion L) Ω]
    _ = algebraMap L Ω (galoisBaseChangeRestriction K (v.adicCompletion K) L Ω g x) :=
      (galoisBaseChangeRestriction_commutes K (v.adicCompletion K) L Ω g x).symm

end
end Dubon2026
