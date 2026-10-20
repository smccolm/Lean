import Dubon2026.NumberFieldFiniteAdelicLocalIntegral

/-! # The original Hermitian form has only finitely many bad integral places

Restricted-product integrality of the matrix and its inverse gives the
precise finite exceptional set to avoid in the source split unitary
level construction for DUB-17. No globally unimodular form is assumed.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain Matrix Filter
open scoped NumberField

/-- Every original invertible adelic matrix is an integral invertible local matrix at all but finitely many original places. -/
theorem numberFieldFiniteAdelicMatrix_eventually_integral
    (K : Type*) [Field K] [NumberField K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : (Matrix ι ι (FiniteAdeleRing (𝓞 K) K))ˣ) :
    ∀ᶠ v in cofinite, numberFieldFiniteAdelicMatrixProjection K ι v M ∈
      ((v.adicCompletionIntegers K).matrix (n := ι)).toSubmonoid.units := by
  have h : ∀ᶠ v in cofinite, ∀ i j, M.val i j v ∈ v.adicCompletionIntegers K :=
    eventually_all.mpr fun i => eventually_all.mpr fun j => (M.val i j).property
  have hi : ∀ᶠ v in cofinite, ∀ i j, (M⁻¹).val i j v ∈ v.adicCompletionIntegers K :=
    eventually_all.mpr fun i => eventually_all.mpr fun j => ((M⁻¹).val i j).property
  filter_upwards [h, hi] with v h hi
  exact ⟨h, hi⟩

end
end Dubon2026
