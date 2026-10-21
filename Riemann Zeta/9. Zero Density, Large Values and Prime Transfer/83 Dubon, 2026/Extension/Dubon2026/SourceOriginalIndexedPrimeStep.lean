import Dubon2026.SourceOriginalReducedConjugateRoot

/-! DUB-17/18 -> numerical modular genus -> composite degree -> exact
indexed roots. A lower-level product identity constructs an actual field
embedding. The full or reduced prime relation then supplies the requested
primitive conjugate. The reduced branch derives its removed-root
distinction from the preceding level's product identity. All generation,
degree and lower product inputs are explicit induction obligations.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField ConjugateSlots PrimeDegreeAux
open scoped IntermediateField
variable {K : Type*} [Field K] [Algebra ℚ K] [IsAlgClosed K]

theorem original_indexed_prime_step_root (a d p b : ℕ)
    [NeZero a] [NeZero d] [hp : Fact p.Prime]
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) (a * d * p))
    (hs : (⟨a, b⟩ : Σ _ : ℕ, ℕ) ∈ indices (a * d * p))
    (hgen : modularFunctionFieldFull (a * d) =
      IntermediateField.adjoin ℚ ({jq, qExpand ℚ (a * d) jq} : Set (LaurentSeries ℚ)))
    (hdeg : (minpoly (modularFunctionFieldFull (a * d))
      (qExpand ℚ (a * d * p) jq)).natDegree = if p ∣ a * d then p else p + 1)
    (hlower : expandedJMinpoly K (a * d) (a * d) = slotProduct (a * d) (ζ ^ p))
    (hprev : ∀ (m : ℕ) [NeZero m], a * d = m * p →
      expandedJMinpoly K m m = slotProduct m (ζ ^ (p * p))) :
    (expandedJMinpoly K (a * d * p) (a * d * p)).IsRoot (slotValue ζ a b) := by
  have hd := index_prime_descent a d p b hs
  have hroot := expanded_minpoly_slot_root_of_identity p (a * d) (ζ ^ p)
    hlower ⟨a, b % d⟩ hd.1
  have hroot' : (expandedJMinpoly K (a * d * p) (a * d)).IsRoot
      (qExpand K p (slotValue (ζ ^ p) a (b % d))) := by
    simpa only [Nat.mul_comm p (a * d)] using hroot
  obtain ⟨σ, _, hnew, hbase⟩ := original_full_embedding_of_expanded_minpoly_root
    (a * d * p) (a * d) hgen _ hroot'
  have hseed : σ ⟨qExpand ℚ (a * d) jq, jqd_mem_full (a * d) dvd_rfl⟩ =
      TS K (a * a * p) ((ζ ^ (b % d * a)) ^ p) :=
    hnew.trans (slotValue_prime_seed ζ a d p b)
  have hη : IsPrimitiveRoot ((ζ ^ (a * d) : Kˣ) : K) p := by
    have h := primitive_root_pow_div hζ (dvd_mul_left p (a * d))
    rwa [Nat.mul_div_cancel _ hp.out.pos] at h
  have hbranch := slotValue_prime_branch ζ a d b
  by_cases hpM : p ∣ a * d
  · obtain ⟨m, hm⟩ := hpM
    have hM : a * d = m * p := hm.trans (Nat.mul_comm p m)
    haveI : NeZero m := ⟨fun he => by
      have hn := NeZero.ne (a * d)
      rw [hM, he, zero_mul] at hn
      exact hn rfl⟩
    have hprevious := hprev m hM
    have hpa : p ∣ (a * d * p) / a := by
      rw [Nat.mul_assoc, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne a))]
      exact dvd_mul_left p d
    rw [if_pos ⟨m, hm⟩] at hdeg
    have htransport : ∀ (M : ℕ) [NeZero M], M = a * d →
        ∃ τ : modularFunctionFieldFull M →+* LaurentSeries K,
        (∀ (z : ℚ⟮jq⟯) (hz : (z : LaurentSeries ℚ) ∈ modularFunctionFieldFull M),
          τ ⟨z, hz⟩ = coeffEmb K (qExpand ℚ (M * p) (z : LaurentSeries ℚ))) ∧
        τ ⟨qExpand ℚ M jq, jqd_mem_full M dvd_rfl⟩ =
          TS K (a * a * p) ((ζ ^ (b % d * a)) ^ p) ∧
        (minpoly (modularFunctionFieldFull M) (qExpand ℚ (M * p) jq)).natDegree = p := by
      intro M _ he
      subst M
      exact ⟨σ, hbase, hseed, hdeg⟩
    obtain ⟨τ, hτbase, hτseed, hτdeg⟩ := htransport (m * p) hM.symm
    simp only [hM] at hζ hs hbranch hη hpa ⊢
    exact original_reduced_prime_root_of_lower_identity m p a b ζ hζ hs hpa
      τ hτbase (ζ ^ (m * p)) hη (ζ ^ (b % d * a)) (b / d) hd.2
      hτseed hbranch hτdeg hprevious
  · rw [if_neg hpM] at hdeg
    have hr := prime_twisted_minpoly_root_of_full_step_degree p (ζ ^ (a * d)) hη
      (modularFunctionFieldFull (a * d)) σ (a * d) (jqd_mem_full (a * d) dvd_rfl)
      (a * a) (ζ ^ (b % d * a)) hseed hdeg (b / d) hd.2
    rw [hbranch] at hr
    exact expanded_minpoly_root_of_relative_root (modularFunctionFieldFull (a * d))
      (jq_mem_full _) σ (a * d * p) (a * d * p) hbase _ hr

end
end Dubon2026.SourceFunctionField
