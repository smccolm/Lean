import Dubon2026.OriginalCoinducedEquivariantExtension

/-! # The genuine coefficient diagram for an original coinduced shift

An extended coefficient morphism descends through the literal orbit
quotient. Keeping all three maps and their commuting equalities allows
the ordinary connecting-map naturality theorem to implement the two
shifts in DUB-17's converse norm criterion.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2 Submodule.module Submodule.Quotient.module
variable {G : Type} [Group G] (M : Rep.{0} ℤ G)

/-- An original coefficient morphism killing the orbit embedding descends to the actual coinduced quotient. -/
def originalCoinducedQuotientDesc {C : Rep.{0} ℤ G}
    (f : originalCoinducedFunctionRep M ⟶ C) (hf : originalCoinducedUnit M ≫ f = 0) :
    originalCoinducedQuotient M ⟶ C :=
  Rep.ofHom ⟨(originalCoinducedUnit M).hom.toLinearMap.range.liftQ f.hom.toLinearMap
    (by
      rintro _ ⟨x, rfl⟩
      exact congrArg (fun t : M ⟶ C => t.hom x) hf), fun g => by
    apply LinearMap.ext
    intro q
    obtain ⟨v, rfl⟩ := (Submodule.mkQ_surjective
      (originalCoinducedUnit M).hom.toLinearMap.range) q
    exact Rep.hom_comm_apply f g v⟩

/-- Descent retains the literal original projection equality. -/
theorem originalCoinducedQuotientDesc_comp {C : Rep.{0} ℤ G}
    (f : originalCoinducedFunctionRep M ⟶ C) (hf : originalCoinducedUnit M ≫ f = 0) :
    (originalCoinducedShortComplex M).g ≫ originalCoinducedQuotientDesc M f hf = f := by
  apply Rep.hom_ext
  rfl

/-- A genuine extended map supplies a commuting map of the two original short coefficient sequences. -/
def originalCoinducedExtensionDiagram {Y : ShortComplex (Rep ℤ G)}
    (f : M ⟶ Y.X₁) (a : originalCoinducedFunctionRep M ⟶ Y.X₂)
    (ha : originalCoinducedUnit M ≫ a = f ≫ Y.f) :
    originalCoinducedShortComplex M ⟶ Y where
  τ₁ := f
  τ₂ := a
  τ₃ := originalCoinducedQuotientDesc M (a ≫ Y.g) (by
    rw [← Category.assoc, ha, Category.assoc, Y.zero, Limits.comp_zero])
  comm₁₂ := ha.symm
  comm₂₃ := (originalCoinducedQuotientDesc_comp M _ _).symm

/-- Internal-Hom H1 vanishing constructs the actual sequence diagram with the prescribed original left map. -/
theorem originalCoinducedExtensionDiagram_exists {Y : ShortComplex (Rep ℤ G)}
    (h : Limits.IsZero (groupCohomology ((Rep.ihom (originalCoinducedQuotient M)).obj Y.X₂) 1))
    (f : M ⟶ Y.X₁) :
    ∃ d : originalCoinducedShortComplex M ⟶ Y, d.τ₁ = f := by
  obtain ⟨a, ha⟩ := originalCoinduced_equivariant_extension M Y.X₂ h (f ≫ Y.f)
  exact ⟨originalCoinducedExtensionDiagram M f a ha, rfl⟩

end
end Dubon2026
