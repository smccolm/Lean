import Dubon2026.OriginalClassInvariantSubgroupNormalization

/-! # Preserve the actual idele total in the normalized subgroup system

Assemble the existing finite cyclic invariant and actual subgroup
normalization over abstract number fields before instantiating the large
arithmetic union. This is the exact full-order witness deduction needed
by DUB-17's arithmetic finite-stage subgroup normalization.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory

/-- A constructed normalized full-order original witness gives injective exact-image global and subgroup invariants while retaining the actual full-idele total formula. -/
theorem originalIdeleClass_normalized_system_of_witness
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (hn : 0 < n) (hdegree : Module.finrank K L = n)
    (total : groupCohomology (originalFullIdeleRep K L) 2 →+ AddCircle (1 : ℚ))
    (h : ∃ f : groupCohomology (originalIdeleClassRep K L) 2 →+ AddCircle (1 : ℚ),
      ∃ u : groupCohomology (originalIdeleClassRep K L) 2,
        (∀ x : groupCohomology (originalFullIdeleRep K L) 2,
          f ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullClassRepHom K L) x) = total x) ∧
        f u = ↑((1 : ℚ) / n) ∧ addOrderOf u = n) :
    ∃ f : groupCohomology (originalIdeleClassRep K L) 2 →+ AddCircle (1 : ℚ),
      Function.Injective f ∧ (∀ t : AddCircle (1 : ℚ), t ∈ f.range ↔ n • t = 0) ∧
      (∀ x : groupCohomology (originalFullIdeleRep K L) 2,
        f ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullClassRepHom K L) x) = total x) ∧
      ∀ S : Subgroup Gal(L/K),
        ∃ invS : groupCohomology (Rep.res S.subtype (originalIdeleClassRep K L)) 2 →+ AddCircle (1 : ℚ),
          Function.Injective invS ∧
          (∀ t : AddCircle (1 : ℚ), t ∈ invS.range ↔ Nat.card S • t = 0) ∧
          ∀ x : groupCohomology (originalIdeleClassRep K L) 2,
            invS ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (originalIdeleClassRep K L))) 2).hom x) =
              S.index • f x := by
  obtain ⟨f, u, ht, hf, hu⟩ := h
  have hu' : addOrderOf u = Module.finrank K L := hu.trans hdegree.symm
  have hg := originalIdeleClass_full_order_generates K L u hu'
  obtain ⟨hi, hr⟩ := originalFiniteCyclic_normalized_hom u n hn hu hg f hf
  have hf' : f u = ↑((1 : ℚ) / Module.finrank K L) :=
    hf.trans (congrArg (fun k : ℕ => (↑((1 : ℚ) / k) : AddCircle (1 : ℚ))) hdegree.symm)
  exact ⟨f, hi, hr, ht, fun S => originalIdeleClass_subgroup_invariants_of_normalized K L u hu' f hf' S⟩

end
end Dubon2026
