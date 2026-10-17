import Dubon2026.OriginalTrivialDualHomology
import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality

/-! # Actual integral first homology and abelianization under group change

Pinned H1 and tensor-unit equivalences retain the actual map induced by
a group homomorphism. This is the low-degree comparison needed to turn
DUB-17's subgroup norm-homology image into the Galois subgroup image.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory

/-- Pinned first homology and the tensor unit identify the actual trivial
integral homology with the additive abelianization. -/
def originalTrivialHomologyAbelianizationEquiv (G : Type) [Group G] :
    groupHomology (Rep.trivial ℤ G ℤ) 1 ≃+ Additive (Abelianization G) :=
  (groupHomology.H1AddEquivOfIsTrivial (Rep.trivial ℤ G ℤ)).trans
    (TensorProduct.rid ℤ (Additive (Abelianization G))).toAddEquiv

/-- The actual single chain with coefficient one represents the literal
abelianized group element under the pinned equivalence. -/
theorem originalTrivialHomologyAbelianizationEquiv_single {G : Type} [Group G] (g : G) :
    originalTrivialHomologyAbelianizationEquiv G
      (groupHomology.H1π (Rep.trivial ℤ G ℤ)
        ((groupHomology.cycles₁IsoOfIsTrivial (Rep.trivial ℤ G ℤ)).inv
          (Finsupp.single g 1))) = Additive.ofMul (Abelianization.of g) := by
  change (TensorProduct.rid ℤ (Additive (Abelianization G)))
    (groupHomology.H1AddEquivOfIsTrivial (Rep.trivial ℤ G ℤ)
      (groupHomology.H1π (Rep.trivial ℤ G ℤ)
        ((groupHomology.cycles₁IsoOfIsTrivial (Rep.trivial ℤ G ℤ)).inv
          (Finsupp.single g 1)))) = _
  rw [groupHomology.H1AddEquivOfIsTrivial_single]
  change (1 : ℤ) • Additive.ofMul (Abelianization.of g) = _
  exact one_smul ℤ (Additive.ofMul (Abelianization.of g))

/-- The actual group-change map on trivial integral first homology is
the map on abelianizations induced by the same group homomorphism. -/
theorem originalTrivialHomologyAbelianizationEquiv_map
    {G H : Type} [Group G] [Group H] (f : G →* H)
    (y : groupHomology (Rep.trivial ℤ G ℤ) 1) :
    originalTrivialHomologyAbelianizationEquiv H
      (groupHomology.map f (𝟙 (Rep.trivial ℤ G ℤ)) 1 y) =
      (Abelianization.map f).toAdditive (originalTrivialHomologyAbelianizationEquiv G y) := by
  obtain ⟨g, hg⟩ := Quotient.exists_rep
    ((originalTrivialHomologyAbelianizationEquiv G y).toMul)
  let z := (groupHomology.cycles₁IsoOfIsTrivial (Rep.trivial ℤ G ℤ)).inv
    (Finsupp.single g 1)
  have hy : y = groupHomology.H1π (Rep.trivial ℤ G ℤ) z := by
    apply (originalTrivialHomologyAbelianizationEquiv G).injective
    exact (congrArg Additive.ofMul hg).symm.trans
      (originalTrivialHomologyAbelianizationEquiv_single g).symm
  rw [hy, groupHomology.H1π_comp_map_apply]
  have hz : groupHomology.mapCycles₁ f (𝟙 (Rep.trivial ℤ G ℤ)) z =
      (groupHomology.cycles₁IsoOfIsTrivial (Rep.trivial ℤ H ℤ)).inv
        (Finsupp.single (f g) 1) := by
    apply Subtype.ext
    change (groupHomology.chainsMap₁ (A := Rep.trivial ℤ G ℤ)
      (B := Rep.trivial ℤ H ℤ) f (𝟙 (Rep.trivial ℤ G ℤ))).hom
      (Finsupp.single g 1) = Finsupp.single (f g) 1
    simp [groupHomology.chainsMap₁]
    rfl
  rw [hz, originalTrivialHomologyAbelianizationEquiv_single]
  change _ = (Abelianization.map f).toAdditive
    (originalTrivialHomologyAbelianizationEquiv G
      (groupHomology.H1π (Rep.trivial ℤ G ℤ) _))
  rw [originalTrivialHomologyAbelianizationEquiv_single]
  rfl

end
end Dubon2026
