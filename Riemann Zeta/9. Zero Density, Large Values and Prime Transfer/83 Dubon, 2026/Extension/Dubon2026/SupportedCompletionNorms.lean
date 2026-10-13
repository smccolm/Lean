import Dubon2026.SupportedOrbitUnitFieldComparison
import Dubon2026.OriginalAdicCompletionResidue

/-! # Original norms and local compactness of unrestricted completions

These structures retain the original completion fields and original norms.
At finite places the proved original residue comparison supplies properness.
They prepare the exact local-stabilizer H2 inputs in DUB-17's idele formula.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Valued
variable (L : Type) [Field L] [NumberField L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))

@[reducible]
private def completionNormedField (p : SUnitLogPlace L S) : NormedField (supportedUnrestrictedCompletion L S p) := by
  cases p with
  | inl v => exact inferInstanceAs (NormedField v.Completion)
  | inr v => exact inferInstanceAs (NormedField (v.val.adicCompletion L))

instance (p : SUnitLogPlace L S) : NormedField (supportedUnrestrictedCompletion L S p) where
  toField := inferInstance
  toMetricSpace := (completionNormedField L S p).toMetricSpace
  norm := (completionNormedField L S p).norm
  dist_eq := by cases p <;> exact (completionNormedField L S _).dist_eq
  norm_mul := by cases p <;> exact (completionNormedField L S _).norm_mul

instance (p : SUnitLogPlace L S) : LocallyCompactSpace (supportedUnrestrictedCompletion L S p) := by
  cases p with
  | inl v => exact inferInstanceAs (LocallyCompactSpace v.Completion)
  | inr v =>
    haveI := original_adicCompletion_properSpace L v.val
    exact inferInstanceAs (LocallyCompactSpace (v.val.adicCompletion L))

/-- The exact finite completion carries its original nontrivial norm. -/
@[reducible]
def supportedFiniteCompletionNontrivialNorm (p : SUnitLogPlace L S)
    (h : p.isRight) : NontriviallyNormedField (supportedUnrestrictedCompletion L S p) where
  toNormedField := inferInstance
  non_trivial := by
    cases p with
    | inl v => cases h
    | inr v => exact (Valued.toNontriviallyNormedField (v.val.adicCompletion L) (WithZero (Multiplicative ℤ))).non_trivial

/-- The original norm on each actual finite completion is ultrametric. -/
theorem supportedFiniteCompletion_isUltrametric (p : SUnitLogPlace L S)
    (h : p.isRight) : IsUltrametricDist (supportedUnrestrictedCompletion L S p) := by
  cases p with
  | inl v => cases h
  | inr v => exact inferInstanceAs (IsUltrametricDist (v.val.adicCompletion L))

end
end Dubon2026
