/-
Copyright 2026 Anthropic, PBC.
Licensed under the Apache License, Version 2.0; see ../../Dependencies/AnthropicFLTReuse/LICENSE.
Adapted in part from anthropics/fermats-last-theorem, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_groupCohomology_exists_corestriction_comp_res_eq_index_nsmul.lean.
Changes: reuse the native coset trace and its proved index identity; identify
the existing native comparison with literal restriction using the Shapiro bridge.
-/
import Dubon2026.OriginalShapiroRestriction

/-! # Original restriction followed by the actual coset trace

The existing native comparison and trace already satisfy the index identity.
This proves that the comparison is the actual cohomological restriction map,
discharging the corestriction assumption in DUB-17's subgroup H2 generator step.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory

variable {k G : Type} [CommRing k] [Group G] (A : Rep k G) (S : Subgroup G)

/-- The native Shapiro comparison is exactly the original subgroup restriction. -/
theorem subgroupCohomologyComparison_eq_restriction (n : ℕ) :
    subgroupCohomologyComparison A S n =
      groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype A)) n := by
  let N := Rep.res S.subtype A
  let Q := Rep.coind S.subtype N
  let ev : Rep.res S.subtype Q ⟶ N :=
    (Rep.resCoindHomEquiv S.subtype Q N).symm (𝟙 Q)
  have hev : ∀ f : Rep.res S.subtype Q, ev.hom f = (f : G → A) 1 := fun _ => rfl
  have hsh := OriginalShapiroRestriction.originalShapiroIso_eq_restriction_eval N n ev hev
  unfold subgroupCohomologyComparison
  change groupCohomology.map (MonoidHom.id G)
      (Rep.resCoindToHom S.subtype A N (𝟙 N)) n ≫
        (groupCohomology.coindIso N n).hom = _
  rw [hsh, ← groupCohomology.map_comp, ← groupCohomology.map_comp]
  change groupCohomology.map S.subtype
    ((Rep.resFunctor S.subtype).map (Rep.resCoindToHom S.subtype A N (𝟙 N)) ≫
      ((Rep.resFunctor (MonoidHom.id S)).map (𝟙 (Rep.res S.subtype Q)) ≫ ev)) n = _
  congr 1
  refine Rep.hom_ext (DFunLike.ext _ _ fun x => ?_)
  change A.ρ (1 : G) x = x
  rw [map_one, Module.End.one_apply]

variable [Fintype (G ⧸ S)]

/-- Literal subgroup restriction followed by the original trace multiplies by the actual index. -/
theorem originalCohomology_restriction_trace (n : ℕ) :
    groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype A)) n ≫
      subgroupCohomologyTrace A S n = S.index • 𝟙 (groupCohomology A n) := by
  rw [← subgroupCohomologyComparison_eq_restriction, subgroupCohomologyComparison_trace]
  rw [Subgroup.index, Nat.card_eq_fintype_card]

/-- The actual corestriction sends the literal restriction of each class to its index multiple. -/
theorem originalCohomology_trace_restriction_apply (n : ℕ) (x : groupCohomology A n) :
    (subgroupCohomologyTrace A S n).hom
      ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype A)) n).hom x) = S.index • x := by
  have h := congrArg (fun f : groupCohomology A n ⟶ groupCohomology A n => f.hom x)
    (originalCohomology_restriction_trace A S n)
  exact h

end
end Dubon2026
