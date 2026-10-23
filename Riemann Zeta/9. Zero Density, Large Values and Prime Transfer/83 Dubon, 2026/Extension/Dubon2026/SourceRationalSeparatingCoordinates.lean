import Dubon2026.SourceCurveSeparatingPrincipalDegree
import Mathlib.FieldTheory.RatFunc.IntermediateField

/-! DUB-17/18 -> original Frobenius/inertia -> residue principal divisors ->
rational-function base of Galois descent. Linear rational coordinates X-c
generate the whole field in every characteristic. Their finite separability
and degree-zero order sums therefore follow without a perfectness premise. -/
namespace Dubon2026.SourceCurve
noncomputable section
open IntermediateField

theorem finite_separable_of_adjoin_eq_top
    {K F : Type*} [Field K] [Field F] [Algebra K F] (t : F)
    (h : K⟮t⟯ = ⊤) : FiniteDimensional K⟮t⟯ F ∧ Algebra.IsSeparable K⟮t⟯ F := by
  have hs : Function.Surjective (algebraMap K⟮t⟯ F) := by
    intro x
    exact ⟨⟨x, h ▸ IntermediateField.mem_top⟩, rfl⟩
  refine ⟨Module.Finite.of_surjective (Algebra.linearMap K⟮t⟯ F) hs, ⟨fun x => ?_⟩⟩
  obtain ⟨y, rfl⟩ := hs x
  exact isSeparable_algebraMap y

theorem rational_coordinate_finite (K : Type*) [Field K] :
    FiniteDimensional K⟮(RatFunc.X : RatFunc K)⟯ (RatFunc K) :=
  (finite_separable_of_adjoin_eq_top _ RatFunc.adjoin_X).1

theorem rational_coordinate_separable (K : Type*) [Field K] :
    Algebra.IsSeparable K⟮(RatFunc.X : RatFunc K)⟯ (RatFunc K) :=
  (finite_separable_of_adjoin_eq_top _ RatFunc.adjoin_X).2

theorem adjoin_rational_X_sub_const (K : Type*) [Field K] (c : K) :
    K⟮(RatFunc.X : RatFunc K) - algebraMap K (RatFunc K) c⟯ = ⊤ := by
  apply top_le_iff.mp
  rw [← RatFunc.adjoin_X]
  apply adjoin_simple_le_iff.mpr
  have h := add_mem
    (mem_adjoin_simple_self K ((RatFunc.X : RatFunc K) - algebraMap K (RatFunc K) c))
    ((K⟮(RatFunc.X : RatFunc K) - algebraMap K (RatFunc K) c⟯).algebraMap_mem c)
  simpa only [sub_add_cancel] using h

theorem sum_orders_rational_X_sub_const (K : Type*) [Field K] (c : K) :
    (∑ᶠ v : Place K (RatFunc K), v.ord (RatFunc.X - algebraMap K (RatFunc K) c) *
      (Module.finrank K v.ResidueField : ℤ)) = 0 := by
  have ht : Transcendental K ((RatFunc.X : RatFunc K) - algebraMap K (RatFunc K) c) := by
    intro ha
    apply RatFunc.transcendental_X (K := K)
    simpa only [sub_add_cancel] using ha.add (isAlgebraic_algebraMap c)
  obtain ⟨hfinite, hsep⟩ := finite_separable_of_adjoin_eq_top _ (adjoin_rational_X_sub_const K c)
  exact sum_orders_eq_zero_of_separating_coordinate _ ht

end
end Dubon2026.SourceCurve
