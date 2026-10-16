import Dubon2026.OriginalLocalEmbeddingPrimeContraction
import Dubon2026.LocalFieldAlgHomContinuity
import Dubon2026.OriginalLocalCompletionMap
import Dubon2026.OriginalAdicBaseChangeMap

/-! # Constructed completion maps commute with the original global tower

The actual induced primes lie over one another by the proved contraction
comparison. Equality of the two continuous completed maps follows from
Mathlib's completion extensionality and their literal original field
values. This identifies the maps needed to compare DUB-17's Mackey
localizations with the existing original finite-global H2 localization.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField

variable (L H E M : Type) [Field L] [NumberField L] [Field H] [NumberField H]
  [Algebra L H] [Field E] [Field M] [Algebra L E] [Algebra H M]
  (p : ℕ) (hp : p.Prime)
  [Algebra (rationalPrimeLocalField p hp) E] [Algebra (rationalPrimeLocalField p hp) M]
  [ValuativeRel E] [ValuativeRel M] [TopologicalSpace E] [TopologicalSpace M]
  [IsNonarchimedeanLocalField E] [IsNonarchimedeanLocalField M]
  [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension (ValuativeRel.valuation E)]
  [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension (ValuativeRel.valuation M)]
  (e : E →ₐ[rationalPrimeLocalField p hp] M)
  (he : ∀ x : L, e (algebraMap L E x) = algebraMap H M (algebraMap L H x))

include e he in
/-- The two genuine induced primes lie over one another in the actual original number-field tower. -/
theorem originalLocalEmbeddingPrime_liesOver :
    (originalLocalEmbeddingPrime H M p hp).asIdeal.LiesOver
      (originalLocalEmbeddingPrime L E p hp).asIdeal :=
  ⟨(congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal
    (originalLocalEmbeddingPrime_under_eq L H E M p hp e he)).symm⟩

/-- Retain the source local field's original additive uniformity. -/
local instance originalCompletionTowerSourceUniformity : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
/-- The retained source uniformity is compatible with its actual addition. -/
local instance originalCompletionTowerSourceUniformAdd : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
/-- Retain the target local field's original additive uniformity. -/
local instance originalCompletionTowerTargetUniformity : UniformSpace M := IsTopologicalAddGroup.rightUniformSpace M
/-- The retained target uniformity is compatible with its actual addition. -/
local instance originalCompletionTowerTargetUniformAdd : IsUniformAddGroup M := isUniformAddGroup_of_addCommGroup

/-- The literal constructed completion embedding commutes with the original completed number-field base-change map. -/
theorem originalLocalCompletionMap_tower
    (x : (originalLocalEmbeddingPrime L E p hp).adicCompletion L) :
    letI := originalLocalEmbeddingPrime_liesOver L H E M p hp e he
    e (originalLocalCompletionMap L E p hp x) =
      originalLocalCompletionMap H M p hp
        (originalAdicBaseChangeMap L H (originalLocalEmbeddingPrime L E p hp)
          (originalLocalEmbeddingPrime H M p hp) x) := by
  letI := originalLocalEmbeddingPrime_liesOver L H E M p hp e he
  letI : NontriviallyNormedField M := localFieldOriginalNorm M
  apply UniformSpace.Completion.ext'
    ((localFieldAlgHom_continuous (rationalPrimeLocalField p hp) E M e).comp
      (originalLocalCompletionMap_continuous L E p hp))
    ((originalLocalCompletionMap_continuous H M p hp).comp
      (originalAdicBaseChangeMap_continuous L H (originalLocalEmbeddingPrime L E p hp)
        (originalLocalEmbeddingPrime H M p hp)))
  intro z
  change e (originalLocalCompletionMap L E p hp
    (algebraMap L ((originalLocalEmbeddingPrime L E p hp).adicCompletion L) z.ofVal)) =
      originalLocalCompletionMap H M p hp
        (originalAdicBaseChangeMap L H (originalLocalEmbeddingPrime L E p hp)
          (originalLocalEmbeddingPrime H M p hp)
          (algebraMap L ((originalLocalEmbeddingPrime L E p hp).adicCompletion L) z.ofVal))
  rw [originalLocalCompletionMap_algebraMap, originalAdicBaseChangeMap_algebraMap,
    originalLocalCompletionMap_algebraMap]
  exact he z.ofVal

end
end Dubon2026
