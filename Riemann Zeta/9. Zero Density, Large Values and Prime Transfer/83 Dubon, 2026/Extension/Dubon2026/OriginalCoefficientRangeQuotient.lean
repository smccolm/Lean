import Mathlib.RepresentationTheory.Coinvariants

/-! # The actual original coefficient range quotient

The mod-p comparison's surjectivity is proved by detecting its literal
cokernel through coinvariants. These are the original range, quotient
and projection required for that argument on DUB-17's projectivity route.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory

variable {k G : Type} [CommRing k] [Group G] {A B : Rep.{0} k G} (f : A ⟶ B)

/-- The original action descends to the literal quotient by the original map's image. -/
abbrev originalCoefficientRangeQuotient : Rep k G :=
  B.quotient (LinearMap.range f.hom.toLinearMap) fun g x hx => by
    obtain ⟨y, hy⟩ := hx
    refine ⟨A.ρ g y, ?_⟩
    change f.hom (A.ρ g y) = B.ρ g x
    change f.hom y = x at hy
    rw [Rep.hom_comm_apply, hy]

/-- The actual original target projected to its literal range quotient. -/
def originalCoefficientRangeProjection : B ⟶ originalCoefficientRangeQuotient f :=
  Rep.ofHom ⟨(LinearMap.range f.hom.toLinearMap).mkQ, fun _ => rfl⟩

/-- Every literal original range element projects to zero. -/
theorem originalCoefficientRangeProjection_map (x : A) :
    (originalCoefficientRangeProjection f).hom (f.hom x) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr ⟨x, rfl⟩

/-- Surjectivity on the original coinvariants forces zero coinvariants in the literal range quotient. -/
theorem originalCoefficientRangeQuotient_coinvariants_zero
    (hf : Function.Surjective (Representation.Coinvariants.map A.ρ B.ρ f.hom))
    (x : originalCoefficientRangeQuotient f) :
    Representation.Coinvariants.mk (originalCoefficientRangeQuotient f).ρ x = 0 := by
  obtain ⟨b, rfl⟩ := (LinearMap.range f.hom.toLinearMap).mkQ_surjective x
  obtain ⟨c, hc⟩ := hf (Representation.Coinvariants.mk B.ρ b)
  obtain ⟨a, rfl⟩ := Representation.Coinvariants.mk_surjective A.ρ c
  have he := congrArg (Representation.Coinvariants.map B.ρ
    (originalCoefficientRangeQuotient f).ρ (originalCoefficientRangeProjection f).hom) hc
  simp only [Representation.Coinvariants.map_mk] at he
  rw [originalCoefficientRangeProjection_map, map_zero] at he
  exact he.symm

end
end Dubon2026
