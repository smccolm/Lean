import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Quotients of a pair of levels under the original ambient inclusion

The source unitary levels are first constructed inside the integral
level. The original injective inclusion then places both levels in the
full unitary adelic group without changing their quotient. This bridge
is required to apply DUB-17's automorphic module theorem on the full
arithmetic double-coset space.
-/

namespace Dubon2026
noncomputable section

variable {G A : Type*} [Group G] [Group A]
variable (U V : Subgroup G) (f : G →* A) (hf : Function.Injective f)
include hf

/-- The lower level inside the upper level maps to the original lower image inside the upper image. -/
theorem subgroupPairImage_subgroupOf :
    (V.subgroupOf U).map (U.equivMapOfInjective f hf).toMonoidHom =
      (V.map f).subgroupOf (U.map f) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.val, hx, rfl⟩
  · intro hy
    obtain ⟨x, rfl⟩ := (U.equivMapOfInjective f hf).surjective y
    obtain ⟨a, ha, hea⟩ := hy
    have he : a = x.val := hf hea
    subst a
    exact ⟨x, ha, rfl⟩

/-- Normality of the original pair of levels is preserved by the actual ambient inclusion. -/
theorem subgroupPairImage_normal [(V.subgroupOf U).Normal] :
    ((V.map f).subgroupOf (U.map f)).Normal := by
  rw [← subgroupPairImage_subgroupOf U V f hf]
  exact Subgroup.Normal.map inferInstance (U.equivMapOfInjective f hf).toMonoidHom
    (U.equivMapOfInjective f hf).surjective

/-- The actual pair quotient is unchanged by its original injective ambient inclusion. -/
def subgroupPairImageQuotientEquiv [(V.subgroupOf U).Normal]
    [((V.map f).subgroupOf (U.map f)).Normal] :
    U ⧸ V.subgroupOf U ≃* U.map f ⧸ (V.map f).subgroupOf (U.map f) :=
  QuotientGroup.congr _ _ (U.equivMapOfInjective f hf) (subgroupPairImage_subgroupOf U V f hf)

end
end Dubon2026
