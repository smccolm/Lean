import Dubon2026.SourceGamma0TorsionLift
import Dubon2026.SourceIntegralCohomologyFinite
import Mathlib.Data.Finsupp.Basic

/-! DUB-17/18 -> residual Galois association -> integral weight-two lifting.
The original congruence homomorphism is in the span of reductions of actual
integer homomorphisms when it vanishes on finite-order elements. This is the
precise hypothesis needed by the characteristic-zero Hecke eigenvalue lift.
The finite-support argument is adapted from anthropics/fermats-last-theorem,
revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_CohCarrier_mem_span_int_of_forall_isOfFinOrder_apply_eq_zero.lean.txt,
exists_finset_support_subset and mem_span_of_finiteIndex
(Apache-2.0; retained LICENSE and NOTICE).
The existing native SL2 cocycle theorem replaces the external Kurosh,
PSL2 quotient and free-product lifting infrastructure.
-/

namespace Dubon2026
noncomputable section
open scoped MatrixGroups
open Matrix.SpecialLinearGroup CongruenceSubgroup

private theorem integerHom_finite_support
    {G : Type} [Group G] [Group.FG G] {α : Type}
    (χ : Additive G →+ (α →₀ ℤ)) :
    ∃ T : Finset α, ∀ g : G, (χ (Additive.ofMul g)).support ⊆ T := by
  classical
  obtain ⟨S, hS, hSfin⟩ := Group.fg_iff.mp ‹Group.FG G›
  refine ⟨hSfin.toFinset.biUnion fun g => (χ (Additive.ofMul g)).support, fun g => ?_⟩
  have hg : g ∈ Subgroup.closure S := by rw [hS]; exact Subgroup.mem_top g
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    exact Finset.subset_biUnion_of_mem (fun g => (χ (Additive.ofMul g)).support)
      (hSfin.mem_toFinset.mpr hy)
  | one =>
    rw [ofMul_one, map_zero, Finsupp.support_zero]
    exact Finset.empty_subset _
  | mul y z _ _ hy hz =>
    rw [ofMul_mul, map_add]
    exact Finsupp.support_add.trans (Finset.union_subset hy hz)
  | inv y _ hy =>
    rw [ofMul_inv, map_neg, Finsupp.support_neg]
    exact hy

/-- Every original congruence homomorphism which vanishes on finite-order
elements is a finite linear combination of reductions of integer homomorphisms.
The integral lift and finite generation are proved, not assumed. -/
theorem sourceGamma0Hom_mem_integralSpan
    (M : ℕ) [NeZero M] (κ : Type) [CommRing κ]
    (x : Additive (Gamma0 M) →+ κ)
    (hx : ∀ g : Gamma0 M, IsOfFinOrder g → x (Additive.ofMul g) = 0) :
    x ∈ Submodule.span κ (Set.range fun y : Additive (Gamma0 M) →+ ℤ =>
      (Int.castAddHom κ).comp y) := by
  classical
  letI : Group.FG SL(2, ℤ) :=
    Group.fg_iff.mpr ⟨{ModularGroup.S, ModularGroup.T},
      SpecialLinearGroup.SL2Z_generators, Set.toFinite _⟩
  let π : (κ →₀ ℤ) →+ κ :=
    Finsupp.liftAddHom fun c : κ => (AddMonoidHom.mulLeft c).comp (Int.castAddHom κ)
  have hπ1 (c : κ) : π (Finsupp.single c 1) = c := by
    change (Finsupp.liftAddHom fun c : κ =>
      (AddMonoidHom.mulLeft c).comp (Int.castAddHom κ)) (Finsupp.single c 1) = c
    rw [Finsupp.liftAddHom_apply_single]
    simp
  obtain ⟨χ, hχ⟩ := sourceGamma0Hom_lift_of_torsion_vanishing M κ π
    (fun c => ⟨Finsupp.single c 1, hπ1 c⟩) x hx
  obtain ⟨T, hT⟩ := integerHom_finite_support χ
  let G : κ → (Additive (Gamma0 M) →+ ℤ) := fun c => (Finsupp.applyAddHom c).comp χ
  have hxsum : x = ∑ c ∈ T, c • ((Int.castAddHom κ).comp (G c)) := by
    refine AddMonoidHom.ext (Additive.ofMul.surjective.forall.mpr ?_)
    intro γ
    rw [AddMonoidHom.finsetSum_apply, ← hχ]
    change π (χ (Additive.ofMul γ)) = _
    change (Finsupp.liftAddHom fun c : κ =>
      (AddMonoidHom.mulLeft c).comp (Int.castAddHom κ)) (χ (Additive.ofMul γ)) = _
    rw [Finsupp.liftAddHom_apply, Finsupp.sum_of_support_subset _ (hT γ)]
    · refine Finset.sum_congr rfl fun c _ => ?_
      rw [AddMonoidHom.smul_apply, AddMonoidHom.comp_apply, smul_eq_mul]
      rfl
    · intro c _
      exact map_zero _
  rw [hxsum]
  exact Submodule.sum_mem _ fun c _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨G c, rfl⟩)

/-- Failure of integral-span membership supplies an actual finite-order
congruence element detected by the original homomorphism. -/
theorem sourceGamma0Hom_exists_torsion_of_not_mem_integralSpan
    (M : ℕ) [NeZero M] (κ : Type) [CommRing κ]
    (x : Additive (Gamma0 M) →+ κ)
    (hx : x ∉ Submodule.span κ (Set.range fun y : Additive (Gamma0 M) →+ ℤ =>
      (Int.castAddHom κ).comp y)) :
    ∃ g : Gamma0 M, IsOfFinOrder g ∧ x (Additive.ofMul g) ≠ 0 := by
  by_contra h
  apply hx
  apply sourceGamma0Hom_mem_integralSpan
  push Not at h
  exact h

end
end Dubon2026
