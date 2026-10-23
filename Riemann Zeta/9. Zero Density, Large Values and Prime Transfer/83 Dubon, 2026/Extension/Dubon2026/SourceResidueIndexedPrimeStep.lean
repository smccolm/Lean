import Dubon2026.SourceResidueReducedConjugateRoot
import Dubon2026.SourceResiduePrimeMinpolyStep

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> all-level
residue degree -> coprime nonmembership -> lower-level conjugate induction.
Adapt local SourceOriginalIndexedPrimeStep to the actual coefficient-field j series and divisor field.
The same native minimal-polynomial, tower and primitive-slot arguments are used.
Every lower-level generation, degree and product hypothesis remains explicit;
the all-level consumer must derive them by induction. No new characteristic-zero
structure is imposed on the residue coefficient field. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField ConjugateSlots PrimeDegreeAux
open scoped IntermediateField
variable {K : Type*} [Field K]

theorem residue_indexed_prime_step_root (a d p b : ℕ)
    [NeZero a] [NeZero d] [hp : Fact p.Prime]
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) (a * d * p))
    (hs : (⟨a, b⟩ : Σ _ : ℕ, ℕ) ∈ indices (a * d * p))
    (hgen : modularFunctionFieldCoeff (a * d) K =
      IntermediateField.adjoin K ({(jqModC K), qExpand K (a * d) (jqModC K)} : Set (LaurentSeries K)))
    (hdeg : (minpoly (modularFunctionFieldCoeff (a * d) K)
      (qExpand K (a * d * p) (jqModC K))).natDegree = if p ∣ a * d then p else p + 1)
    (hlower : residueExpandedJMinpoly K (a * d) (a * d) = slotProduct (a * d) (ζ ^ p))
    (hprev : ∀ (m : ℕ) [NeZero m], a * d = m * p →
      residueExpandedJMinpoly K m m = slotProduct m (ζ ^ (p * p))) :
    (residueExpandedJMinpoly K (a * d * p) (a * d * p)).IsRoot (slotValue ζ a b) := by
  have hd := index_prime_descent a d p b hs
  have hroot := residue_expanded_minpoly_slot_root_of_identity p (a * d) (ζ ^ p)
    hlower ⟨a, b % d⟩ hd.1
  have hroot' : (residueExpandedJMinpoly K (a * d * p) (a * d)).IsRoot
      (qExpand K p (slotValue (ζ ^ p) a (b % d))) := by
    simpa only [Nat.mul_comm p (a * d)] using hroot
  obtain ⟨σ, _, hnew, hbase⟩ := residue_full_embedding_of_expanded_minpoly_root
    (a * d * p) (a * d) hgen _ hroot'
  have hseed : σ ⟨qExpand K (a * d) (jqModC K), jqd_mem_coeff_field (a * d) K dvd_rfl⟩ =
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
        ∃ τ : modularFunctionFieldCoeff M K →+* LaurentSeries K,
        (∀ (z : K⟮(jqModC K)⟯) (hz : (z : LaurentSeries K) ∈ modularFunctionFieldCoeff M K),
          τ ⟨z, hz⟩ = (qExpand K (M * p) (z : LaurentSeries K))) ∧
        τ ⟨qExpand K M (jqModC K), jqd_mem_coeff_field M K dvd_rfl⟩ =
          TS K (a * a * p) ((ζ ^ (b % d * a)) ^ p) ∧
        (minpoly (modularFunctionFieldCoeff M K) (qExpand K (M * p) (jqModC K))).natDegree = p := by
      intro M _ he
      subst M
      exact ⟨σ, hbase, hseed, hdeg⟩
    obtain ⟨τ, hτbase, hτseed, hτdeg⟩ := htransport (m * p) hM.symm
    simp only [hM] at hζ hs hbranch hη hpa ⊢
    exact residue_reduced_prime_root_of_lower_identity m p a b ζ hζ hs hpa
      τ hτbase (ζ ^ (m * p)) hη (ζ ^ (b % d * a)) (b / d) hd.2
      hτseed hbranch hτdeg hprevious
  · rw [if_neg hpM] at hdeg
    have hr := residue_prime_twisted_minpoly_root_of_full_step_degree p (ζ ^ (a * d)) hη
      (modularFunctionFieldCoeff (a * d) K) σ (a * d) (jqd_mem_coeff_field (a * d) K dvd_rfl)
      (a * a) (ζ ^ (b % d * a)) hseed hdeg (b / d) hd.2
    rw [hbranch] at hr
    exact residue_expanded_minpoly_root_of_relative_root (modularFunctionFieldCoeff (a * d) K)
      (jq_mem_coeff_field _ K) σ (a * d * p) (a * d * p) hbase _ hr

end
end Dubon2026.SourceFunctionField
