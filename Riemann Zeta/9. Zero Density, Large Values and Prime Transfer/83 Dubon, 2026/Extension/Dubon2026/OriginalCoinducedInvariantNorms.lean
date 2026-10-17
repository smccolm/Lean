import Dubon2026.OriginalCoinducedSubgroupRetract

/-! # Literal norm preimages in the original coinduced coefficients

An identity-supported function is a norm preimage of an invariant
function. Existing coset coordinates give the subgroup version by
supporting one point per coset. These preimages calculate the augmentation ideal's first
cohomology on DUB-17's fundamental-class extension route, without a new
orbit-counting or negative-degree Tate framework.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory

variable {k G : Type} [CommRing k] [Group G]

/-- Every actual coefficient morphism commutes with the literal finite group norm. -/
theorem originalCoefficientMorphism_norm [Fintype G] {A B : Rep k G} (f : A ⟶ B) (x : A) :
    f.hom (A.ρ.norm x) = B.ρ.norm (f.hom x) := by
  simp only [Representation.norm, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl (fun g _ => Rep.hom_comm_apply f g x)

/-- Actual norm preimages descend along a coefficient retraction. -/
theorem originalInvariantNorm_preimages_of_retract [Fintype G] {A B : Rep k G}
    (i : A ⟶ B) (r : B ⟶ A) (hir : i ≫ r = 𝟙 A)
    (hB : ∀ x : B, x ∈ B.ρ.invariants → ∃ y : B, B.ρ.norm y = x) :
    ∀ x : A, x ∈ A.ρ.invariants → ∃ y : A, A.ρ.norm y = x := by
  intro x hx
  have hi : i.hom x ∈ B.ρ.invariants := by
    intro g
    rw [← Rep.hom_comm_apply, hx g]
  obtain ⟨y, hy⟩ := hB (i.hom x) hi
  refine ⟨r.hom y, ?_⟩
  rw [← originalCoefficientMorphism_norm, hy]
  exact congrArg (fun f : A ⟶ A => f.hom x) hir

/-- An identity-supported original function has norm equal to the supplied invariant function. -/
theorem originalCoinducedInvariant_norm_preimages [Fintype G] (A : Rep k G) :
    ∀ x : originalCoinducedFunctionRep A,
      x ∈ (originalCoinducedFunctionRep A).ρ.invariants →
        ∃ y : originalCoinducedFunctionRep A, (originalCoinducedFunctionRep A).ρ.norm y = x := by
  classical
  intro x hx
  refine ⟨originalCoinducedFunction A (fun g => if g = 1 then x.val 1 else 0), ?_⟩
  apply Subtype.ext
  funext g
  have hc : x.val g = x.val 1 := by
    have he := congrArg (fun f : originalCoinducedFunctionRep A => f.val 1) (hx g)
    change x.val (1 * g) = x.val 1 at he
    simpa only [one_mul] using he
  simp only [Representation.norm, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
  change (∑ h : G, if g * h = 1 then x.val 1 else 0) = x.val g
  simp only [mul_eq_one_iff_inv_eq, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact hc.symm

/-- The original coset coordinates supply literal norm preimages on every actual subgroup. -/
theorem originalCoinducedSubgroupInvariant_norm_preimages (A : Rep k G) (S : Subgroup G)
    [Fintype S] :
    ∀ x : originalCoinducedFunctionRep A,
      x ∈ (Rep.res S.subtype (originalCoinducedFunctionRep A)).ρ.invariants →
        ∃ y : originalCoinducedFunctionRep A,
          (Rep.res S.subtype (originalCoinducedFunctionRep A)).ρ.norm y = x := by
  classical
  intro x hx
  refine ⟨originalCoinducedFunction A
    (fun g => if subgroupCosetRemainder S g = 1 then x.val g else 0), ?_⟩
  apply Subtype.ext
  funext g
  have hc (s : S) : x.val (g * s) = x.val g :=
    congrArg (fun f : originalCoinducedFunctionRep A => f.val g) (hx s)
  simp only [Representation.norm, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
  change (∑ s : S, if subgroupCosetRemainder S (g * s) = 1 then x.val (g * s) else 0) = x.val g
  simp only [subgroupCosetRemainder_mul, hc, mul_eq_one_iff_inv_eq,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

end
end Dubon2026
