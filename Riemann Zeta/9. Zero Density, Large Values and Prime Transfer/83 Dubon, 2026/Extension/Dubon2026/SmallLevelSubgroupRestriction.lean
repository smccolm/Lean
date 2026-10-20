import Mathlib.Algebra.Group.Subgroup.Basic

/-! # Restricting smallness to the actual adelic group

DUB-17's double cosets belong to the source unitary adelic subgroup,
not to the full general linear group. This transports the arithmetic
stabilizer proof into that specified subgroup before forming the modules.
-/

namespace Dubon2026

variable {A G : Type*} [Group A] [Group G]

/-- Ambient smallness restricts to the original adelic subgroup containing the arithmetic image. -/
theorem smallLevel_restrict_to_subgroup (f : A →* G) (S : Subgroup G)
    (hfS : ∀ a, f a ∈ S) (U : Subgroup S)
    (hsmall : ∀ (g : G) (u : U.map S.subtype), g * u.val * g⁻¹ ∈ f.range → u = 1) :
    ∀ (g : S) (u : U),
      g * u.val * g⁻¹ ∈ (f.codRestrict S hfS).range → u = 1 := by
  intro g u hu
  obtain ⟨a, ha⟩ := hu
  let u' : U.map S.subtype := ⟨u.val.val, u.val, u.property, rfl⟩
  have h := hsmall g.val u' ⟨a, congrArg Subtype.val ha⟩
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun x : U.map S.subtype => x.val) h

end Dubon2026
