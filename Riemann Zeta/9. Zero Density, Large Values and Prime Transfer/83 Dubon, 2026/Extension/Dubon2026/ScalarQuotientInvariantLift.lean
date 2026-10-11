import Dubon2026.ScalarRepresentationQuotient
import Mathlib.Tactic.Abel

/-! # Actual invariant lifts and norm preimages in scalar quotients -/

namespace Dubon2026
noncomputable section

open CategoryTheory
open scoped BigOperators

variable {R G : Type} [CommRing R] [Group G] (A : Rep R G)

/-- Vanishing of the actual first cohomology supplies an original coefficient
whose coboundary is the given original one-cocycle. -/
theorem representation_one_cocycle_coboundary_of_isZero
    (hA : Limits.IsZero (groupCohomology A 1)) (c : groupCohomology.cocycles₁ A) :
    ∃ x : A, ∀ g, A.ρ g x - x = c g := by
  haveI := ModuleCat.subsingleton_of_isZero hA
  obtain ⟨x, hx⟩ := (groupCohomology.H1π_eq_zero_iff c).mp
    (Subsingleton.elim (groupCohomology.H1π A c) 0)
  exact ⟨x, fun g => congrFun hx g⟩

/-- An invariant class in the actual scalar quotient has an original invariant
lift. Its discrepancy cocycle is divided by the injective scalar map and
removed using the actual first-cohomology vanishing theorem. -/
theorem repScalarQuotient_invariant_lift (r : R)
    (hinj : Function.Injective (fun x : A => r • x))
    (hA : Limits.IsZero (groupCohomology A 1))
    (q : repScalarQuotient A r)
    (hq : ∀ g, (repScalarQuotient A r).ρ g q = q) :
    ∃ a : A, (∀ g, A.ρ g a = a) ∧ (repScalarRange A r).mkQ a = q := by
  obtain ⟨a, ha⟩ := (repScalarRange A r).mkQ_surjective q
  have hdiff (g : G) : ∃ b : A, r • b = A.ρ g a - a := by
    apply (Submodule.Quotient.mk_eq_zero (repScalarRange A r)).mp
    change (repScalarRange A r).mkQ (A.ρ g a - a) = 0
    rw [map_sub]
    have he : (repScalarRange A r).mkQ (A.ρ g a) =
        (repScalarQuotient A r).ρ g ((repScalarRange A r).mkQ a) := rfl
    rw [he, ha, hq, sub_self]
  choose b hb using hdiff
  have hc : b ∈ groupCohomology.cocycles₁ A := by
    apply (groupCohomology.mem_cocycles₁_iff _).mpr
    intro g h
    apply hinj
    change r • b (g * h) = r • (A.ρ g (b h) + b g)
    rw [smul_add, ← (A.ρ g).map_smul, hb, hb, hb, map_sub, map_mul]
    change A.ρ g (A.ρ h a) - a =
      (A.ρ g (A.ρ h a) - A.ρ g a) + (A.ρ g a - a)
    abel
  obtain ⟨x, hx⟩ := representation_one_cocycle_coboundary_of_isZero A hA ⟨b, hc⟩
  refine ⟨a - r • x, ?_, ?_⟩
  · intro g
    apply sub_eq_zero.mp
    have he : A.ρ g a - a = r • (A.ρ g x - x) := by
      rw [hx]
      exact (hb g).symm
    rw [map_sub, map_smul]
    rw [smul_sub] at he
    have : (A.ρ g a - a) - (r • A.ρ g x - r • x) = 0 := sub_eq_zero.mpr he
    convert this using 1
    abel
  · rw [map_sub]
    have hz : (repScalarRange A r).mkQ (r • x) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨x, rfl⟩
    rw [hz, sub_zero, ha]

/-- Original action-norm preimages descend to every invariant of the actual
scalar quotient after the proved invariant lifting step. -/
theorem repScalarQuotient_invariant_mem_norm [Fintype G] (r : R)
    (hinj : Function.Injective (fun x : A => r • x))
    (hA : Limits.IsZero (groupCohomology A 1))
    (hNorm : ∀ a : A, (∀ g, A.ρ g a = a) → ∃ x : A, ∑ g : G, A.ρ g x = a)
    (q : repScalarQuotient A r)
    (hq : ∀ g, (repScalarQuotient A r).ρ g q = q) :
    ∃ x : repScalarQuotient A r, ∑ g : G, (repScalarQuotient A r).ρ g x = q := by
  obtain ⟨a, ha, haq⟩ := repScalarQuotient_invariant_lift A r hinj hA q hq
  obtain ⟨x, hx⟩ := hNorm a ha
  refine ⟨(repScalarRange A r).mkQ x, ?_⟩
  change ∑ g : G, (repScalarRange A r).mkQ (A.ρ g x) = q
  rw [← map_sum, hx, haq]

end
end Dubon2026
