import Dubon2026.SourceRationalRootDivisors

/-! DUB-17/18 -> original Weil reciprocity -> rational-coordinate case.
Literal divisor evaluation on the actual rational curve reduces evaluation
of its finite root divisor at X to the product of roots, with multiplicity. -/
namespace Dubon2026.SourceCurve.RationalFunction
noncomputable section
open Polynomial
open scoped Classical BigOperators
variable (K : Type*) [Field K] [IsAlgClosed K]

/-- Literal evaluation on an integer divisor of the actual rational curve. -/
def divisorEval (f : RatFunc K) (D : Divisor K (RatFunc K)) : K :=
  D.prod fun v n => placeEval K v f ^ n

theorem divisorEval_sub (f : RatFunc K) (D E : Divisor K (RatFunc K))
    (h : ∀ v ∈ D.support ∪ E.support, placeEval K v f ≠ 0) :
    divisorEval K f (D - E) = divisorEval K f D / divisorEval K f E := by
  let s := D.support ∪ E.support
  have hzero (v : Place K (RatFunc K)) (_ : v ∈ s) : placeEval K v f ^ (0 : ℤ) = 1 :=
    zpow_zero _
  unfold divisorEval
  rw [Finsupp.prod_of_support_subset (D - E) Finsupp.support_sub _ hzero,
    Finsupp.prod_of_support_subset D Finset.subset_union_left _ hzero,
    Finsupp.prod_of_support_subset E Finset.subset_union_right _ hzero,
    ← Finset.prod_div_distrib]
  exact Finset.prod_congr rfl fun v hv => by
    rw [Finsupp.sub_apply, zpow_sub₀ (h v hv)]

theorem divisorEval_single (f : RatFunc K) (v : Place K (RatFunc K)) (n : ℤ) :
    divisorEval K f (Finsupp.single v n) = placeEval K v f ^ n :=
  Finsupp.prod_single_index (zpow_zero _)

theorem rootDivisor_support_subset (q : K[X]) :
    (rootDivisor K q).support ⊆ q.roots.toFinset.image (pointPlace K) := by
  intro v hv
  rcases eq_point_or_infinity K v with ⟨a, rfl⟩ | rfl
  · apply Finset.mem_image.mpr
    refine ⟨a, ?_, rfl⟩
    rw [Finsupp.mem_support_iff, rootDivisor_point, Nat.cast_ne_zero] at hv
    rw [Multiset.mem_toFinset, ← Multiset.count_ne_zero, count_roots]
    exact hv
  · rw [Finsupp.mem_support_iff, rootDivisor_infinity] at hv
    exact (hv rfl).elim

theorem divisorEval_X_rootDivisor (q : K[X]) :
    divisorEval K RatFunc.X (rootDivisor K q) = q.roots.prod := by
  unfold divisorEval
  rw [Finsupp.prod_of_support_subset _ (rootDivisor_support_subset K q) _
    (fun _ _ => zpow_zero _), Finset.prod_image]
  · simp_rw [placeEval_X, rootDivisor_point, zpow_natCast, ← count_roots]
    exact (Finset.prod_multiset_count _).symm
  · exact (pointPlace_injective K).injOn

theorem placeEval_X_ne_zero_on_rootDivisor {q : K[X]} (hq : q ≠ 0) (h0 : q.eval 0 ≠ 0)
    (v : Place K (RatFunc K)) (hv : v ∈ (rootDivisor K q).support) :
    placeEval K v RatFunc.X ≠ 0 := by
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (rootDivisor_support_subset K q hv)
  rw [placeEval_X]
  intro hz
  subst a
  exact h0 ((mem_roots hq).mp (Multiset.mem_toFinset.mp ha))

end
end Dubon2026.SourceCurve.RationalFunction
