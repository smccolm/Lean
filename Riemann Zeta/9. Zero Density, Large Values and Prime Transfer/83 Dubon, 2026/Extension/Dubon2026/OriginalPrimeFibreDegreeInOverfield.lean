import Dubon2026.OriginalPrimeFibreCompletionDegree

/-! # The required prime-fibre degree sum through a nonnormal fixed field

Reindex the already proved degree sums in the same Galois overfield.
Multiplicativity of actual completion degrees and cancellation of the
upper degree give the lower sum without assuming lower normality.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField BigOperators

/-- The actual completion degrees above a lower prime sum to the degree
of an arbitrary intermediate field in the given finite Galois overfield. -/
theorem originalPrimeFibreCompletionDegree_sum_in_galois_overfield
    (K E M : Type) [Field K] [NumberField K] [Field E] [NumberField E]
    [Field M] [NumberField M] [Algebra K E] [Algebra E M] [Algebra K M]
    [IsScalarTower K E M] [FiniteDimensional K M] [IsGalois K M]
    (v : HeightOneSpectrum (𝓞 K)) :
    (∑ᶠ u : OriginalPrimeFibre K E v, originalPrimeFibreCompletionDegree K E v u) =
      Module.finrank K E := by
  classical
  letI : FiniteDimensional K E := FiniteDimensional.left K E M
  letI : FiniteDimensional E M := FiniteDimensional.right K E M
  letI : IsGalois E M := IsGalois.tower_top_of_isGalois K E M
  letI : Fintype (OriginalPrimeFibre K E v) := Fintype.ofFinite _
  letI : Fintype (OriginalPrimeFibre K M v) := Fintype.ofFinite _
  letI : ∀ u : OriginalPrimeFibre K E v, Fintype (OriginalPrimeFibre E M u.val) :=
    fun _ => Fintype.ofFinite _
  have htop : (∑ w : OriginalPrimeFibre K M v, originalPrimeFibreCompletionDegree K M v w) =
      Module.finrank K M := by
    simpa only [finsum_eq_sum_of_fintype] using originalPrimeFibreCompletionDegree_sum_galois K M v
  have hupper (u : OriginalPrimeFibre K E v) :
      (∑ t : OriginalPrimeFibre E M u.val, originalPrimeFibreCompletionDegree E M u.val t) =
        Module.finrank E M := by
    simpa only [finsum_eq_sum_of_fintype] using originalPrimeFibreCompletionDegree_sum_galois E M u.val
  have hs : (∑ u : OriginalPrimeFibre K E v, originalPrimeFibreCompletionDegree K E v u) *
      Module.finrank E M = Module.finrank K M := by
    calc
      _ = ∑ u : OriginalPrimeFibre K E v, ∑ t : OriginalPrimeFibre E M u.val,
          originalPrimeFibreCompletionDegree K E v u * originalPrimeFibreCompletionDegree E M u.val t := by
        simp only [← Finset.mul_sum, hupper, Finset.sum_mul]
      _ = ∑ z : (Σ u : OriginalPrimeFibre K E v, OriginalPrimeFibre E M u.val),
          originalPrimeFibreCompletionDegree K M v (originalPrimeFibreTowerEquiv K E M v z) := by
        rw [Fintype.sum_sigma]
        apply Finset.sum_congr rfl
        intro u _
        apply Finset.sum_congr rfl
        intro t _
        exact (originalPrimeFibreCompletionDegree_tower K E M v u t).symm
      _ = ∑ w : OriginalPrimeFibre K M v, originalPrimeFibreCompletionDegree K M v w :=
        (originalPrimeFibreTowerEquiv K E M v).sum_comp _
      _ = Module.finrank K M := htop
  rw [finsum_eq_sum_of_fintype]
  apply Nat.eq_of_mul_eq_mul_right (Module.finrank_pos (R := E) (M := M))
  exact hs.trans (Module.finrank_mul_finrank K E M).symm

end
end Dubon2026
