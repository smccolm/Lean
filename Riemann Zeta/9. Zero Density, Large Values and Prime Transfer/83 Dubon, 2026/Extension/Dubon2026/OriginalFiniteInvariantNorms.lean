import Dubon2026.OriginalInvariantNormQuotientEquiv
import Dubon2026.OriginalRepresentationNormTower
import Dubon2026.OriginalNestedSubgroupNorms

/-! # Invariant norm lifting from actual Sylow subgroups

The finite relation-obstruction surjectivity step in DUB-17 can reuse the
native integral lattice duality and norm/homology comparisons. Their
general finite-group assembly requires invariant norm lifting without a
p-group restriction. The original coset coordinates identify a subgroup
norm preimage with an index multiple in the full norm image. Sylow index
detection then removes the restriction, using the existing p-group result.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2 Submodule.module Submodule.Quotient.module
variable {G : Type} [Group G] [Fintype G] (A : Rep.{0} ℤ G)

/-- The full literal norm is the sum of the actual subgroup norm over
coset representatives. Normality of the subgroup is unnecessary. -/
theorem originalRepresentation_norm_coset_sum
    (S : Subgroup G) [Fintype S] [Fintype (G ⧸ S)] (x : A) :
    A.ρ.norm x = ∑ q : G ⧸ S, A.ρ q.out ((Rep.res S.subtype A).ρ.norm x) := by
  simp only [Representation.norm, LinearMap.sum_apply, map_sum]
  calc
    (∑ g : G, A.ρ g x) =
        ∑ z : (G ⧸ S) × S, A.ρ (z.1.out * z.2) x := by
      exact (Equiv.sum_comp (originalNormCosetEquiv S).symm (fun g => A.ρ g x)).symm
    _ = ∑ q : G ⧸ S, ∑ s : S, A.ρ q.out ((Rep.res S.subtype A).ρ s x) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro s _
      exact LinearMap.congr_fun (A.ρ.map_mul q.out s.val) x

/-- A subgroup norm preimage of an original full invariant gives a
full norm preimage of its actual subgroup-index multiple. -/
theorem originalInvariantNorm_subgroup_index_mem
    (S : Subgroup G) [Fintype S] [Fintype (G ⧸ S)]
    (x : A.ρ.invariants) (y : A) (hy : (Rep.res S.subtype A).ρ.norm y = x.val) :
    S.index • x ∈ (originalInvariantNormLinear A).range := by
  refine ⟨y, Subtype.ext ?_⟩
  change A.ρ.norm y = S.index • x.val
  rw [originalRepresentation_norm_coset_sum A S y, hy]
  calc
    (∑ q : G ⧸ S, A.ρ q.out x.val) = ∑ _q : G ⧸ S, x.val := by
      exact Finset.sum_congr rfl (fun q _ => x.property q.out)
    _ = S.index • x.val := by
      rw [Finset.sum_const, Finset.card_univ, Subgroup.index, Nat.card_eq_fintype_card]

/-- Actual H1/H2 vanishing on all subgroups gives literal invariant norm
preimages for an arbitrary finite group. -/
theorem originalFinite_norm_preimages_of_subgroup_first_second
    (h : ∀ S : Subgroup G,
      Limits.IsZero (groupCohomology (Rep.res S.subtype A) 1) ∧
        Limits.IsZero (groupCohomology (Rep.res S.subtype A) 2)) :
    ∀ x : A, x ∈ A.ρ.invariants → ∃ y : A, A.ρ.norm y = x := by
  classical
  intro x hx
  let v : A.ρ.invariants := ⟨x, hx⟩
  let q : OriginalInvariantNormQuotient A := Submodule.Quotient.mk v
  have hone : addOrderOf q = 1 := by
    by_contra hn
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hn
    letI : Fact p.Prime := ⟨hp⟩
    let P : Sylow p G := Classical.choice inferInstance
    let S : Subgroup G := P
    letI : Fintype S := Fintype.ofFinite S
    letI : Fintype (G ⧸ S) := Fintype.ofFinite _
    have hS (T : Subgroup S) :
        Limits.IsZero (groupCohomology (Rep.res T.subtype (Rep.res S.subtype A)) 1) ∧
          Limits.IsZero (groupCohomology (Rep.res T.subtype (Rep.res S.subtype A)) 2) :=
      ⟨originalNestedSubgroup_zero A S T 1 (h _).1,
        originalNestedSubgroup_zero A S T 2 (h _).2⟩
    obtain ⟨y, hy⟩ := originalPGroup_norm_preimages_of_subgroup_first_second p
      P.isPGroup' (Rep.res S.subtype A) hS x (fun s => hx s.val)
    have hi : S.index • q = 0 := by
      change S.index • (originalInvariantNormLinear A).range.mkQ v = 0
      rw [← map_nsmul]
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        (originalInvariantNorm_subgroup_index_mem A S v y hy)
    have hd := hpd.trans (addOrderOf_dvd_of_nsmul_eq_zero hi)
    exact P.not_dvd_index hd
  have hq : (Submodule.Quotient.mk v : OriginalInvariantNormQuotient A) = 0 :=
    AddMonoid.addOrderOf_eq_one_iff.mp hone
  obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero _).mp hq
  exact ⟨y, congrArg Subtype.val hy⟩

omit [Fintype G] in
/-- The finite-group norm lifting theorem applies to every actual subgroup. -/
theorem originalFinite_subgroup_norm_preimages
    (h : ∀ H : Subgroup G,
      Limits.IsZero (groupCohomology (Rep.res H.subtype A) 1) ∧
        Limits.IsZero (groupCohomology (Rep.res H.subtype A) 2))
    (S : Subgroup G) [Fintype S] :
    ∀ x : A, x ∈ (Rep.res S.subtype A).ρ.invariants →
      ∃ y : A, (Rep.res S.subtype A).ρ.norm y = x := by
  have hS (T : Subgroup S) :
      Limits.IsZero (groupCohomology (Rep.res T.subtype (Rep.res S.subtype A)) 1) ∧
        Limits.IsZero (groupCohomology (Rep.res T.subtype (Rep.res S.subtype A)) 2) :=
    ⟨originalNestedSubgroup_zero A S T 1 (h _).1,
      originalNestedSubgroup_zero A S T 2 (h _).2⟩
  exact originalFinite_norm_preimages_of_subgroup_first_second (Rep.res S.subtype A) hS

end
end Dubon2026
