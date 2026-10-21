import Dubon2026.SourceOriginalEmbeddedConjugate

/-! DUB-17/18 -> numerical modular genus -> composite degree -> indexed
root induction. The actual preceding j-substitution belongs to the
original lower divisor field. Its embedded value has a lower-level
conjugate shape, so primitive-index arithmetic proves it differs from
the requested root. This supplies the formerly explicit removed-root
distinction to the actual reduced prime-relation consumer.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField ConjugateSlots PrimeDegreeAux
open scoped IntermediateField
variable {K : Type*} [Field K] [Algebra ℚ K] [IsAlgClosed K]

theorem original_reduced_prime_root_of_lower_identity
    (m p a b : ℕ) [NeZero m] [hp : Fact p.Prime] [NeZero a]
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) (m * p * p))
    (hs : (⟨a, b⟩ : Σ _ : ℕ, ℕ) ∈ indices (m * p * p))
    (hpa : p ∣ (m * p * p) / a)
    (σ : modularFunctionFieldFull (m * p) →+* LaurentSeries K)
    (hbase : ∀ (z : ℚ⟮jq⟯) (hz : (z : LaurentSeries ℚ) ∈ modularFunctionFieldFull (m * p)),
      σ ⟨z, hz⟩ = coeffEmb K (qExpand ℚ (m * p * p) (z : LaurentSeries ℚ)))
    (η : Kˣ) (hη : IsPrimitiveRoot (η : K) p) (u : Kˣ) (c : ℕ) (hc : c < p)
    (hseed : σ ⟨qExpand ℚ (m * p) jq, jqd_mem_full (m * p) dvd_rfl⟩ =
      TS K (a * a * p) (u ^ p))
    (hbranch : TS K (a * a) (u * η ^ c) = slotValue ζ a b)
    (hdeg : (minpoly (modularFunctionFieldFull (m * p))
      (qExpand ℚ (m * p * p) jq)).natDegree = p)
    (hprev : expandedJMinpoly K m m = slotProduct m (ζ ^ (p * p))) :
    (expandedJMinpoly K (m * p * p) (m * p * p)).IsRoot (slotValue ζ a b) := by
  have hmem := jqd_mem_full (m * p) (dvd_mul_right m p)
  have hr := expanded_minpoly_root_of_member (modularFunctionFieldFull (m * p))
    (jq_mem_full _) σ (m * p * p) m hbase hmem
  have he : m * p * p = (p * p) * m := by ring
  have hr' : (expandedJMinpoly K ((p * p) * m) m).IsRoot
      (σ ⟨qExpand ℚ m jq, hmem⟩) := by simpa only [he] using hr
  obtain ⟨s, hs', hshape⟩ := expanded_minpoly_root_shape_of_identity
    (p * p) m (ζ ^ (p * p)) hprev _ hr'
  have hne : TS K (a * a) (u * η ^ c) ≠ σ ⟨qExpand ℚ m jq, hmem⟩ := by
    rw [hbranch, hshape]
    exact slotValue_ne_prime_square_expansion hp.out he ζ hζ hs hs' hpa
  have hroot := prime_twisted_minpoly_root_of_reduced_step_degree p η hη
    (modularFunctionFieldFull (m * p)) σ m hmem (jqd_mem_full (m * p) dvd_rfl)
    (a * a) u hseed hdeg c hc hne
  rw [hbranch] at hroot
  exact expanded_minpoly_root_of_relative_root (modularFunctionFieldFull (m * p))
    (jq_mem_full _) σ (m * p * p) (m * p * p) hbase _ hroot

end
end Dubon2026.SourceFunctionField
