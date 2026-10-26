import Dubon2026.CoinducedCosetTrace
import Mathlib.RepresentationTheory.FiniteIndex

/-! DUB-17/18 -> original all-weight adic association -> Gamma1 geometric
Hecke realization -> compare the native transfer used for surjectivity
with the existing literal coset trace. This is the required convention
bridge before a Hecke comparison, not a replacement arithmetic action. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped Classical
variable {R G : Type} [CommRing R] [Group G] (A : Rep.{0} R G) (S : Subgroup G)

/-- Native induction's counit evaluates an actual tensor generator by
the inverse original action, fixing its convention explicitly. -/
theorem sourceNativeInductionCounit_mk (g : G) (x : A) :
    ((Rep.indResAdjunction R S.subtype).counit.app A).hom
      (Representation.IndV.mk S.subtype (Rep.res S.subtype A).ρ g x) = A.ρ g⁻¹ x := by
  change ((Rep.indResHomEquiv S.subtype (Rep.res S.subtype A) A).symm (𝟙 _)).hom
    (Representation.IndV.mk S.subtype (Rep.res S.subtype A).ρ g x) = _
  dsimp [Rep.indResHomEquiv]
  simp

/-- The native finite-index coinduction counit is exactly the repository's
literal coset trace; right and left cosets are related by inversion. -/
theorem sourceNativeCoinductionCounit_eq_cosetTrace [S.FiniteIndex] :
    letI : Fintype (G ⧸ S) := Subgroup.fintypeQuotientOfFiniteIndex
    (Rep.coindResAdjunction R S).counit.app A = coinducedCosetTrace A S := by
  letI : Fintype (G ⧸ S) := Subgroup.fintypeQuotientOfFiniteIndex
  apply Rep.hom_ext
  ext f
  change ((Rep.indResAdjunction R S.subtype).counit.app A).hom
    (Rep.coindToInd (Rep.res S.subtype A) f) = ∑ q : G ⧸ S, coinducedCosetValues A S f q
  rw [Rep.coindToInd_apply]
  change ((Rep.indResAdjunction R S.subtype).counit.app A).hom.toLinearMap _ = _
  erw [map_sum ((Rep.indResAdjunction R S.subtype).counit.app A).hom.toLinearMap]
  calc
    _ = ∑ q : Quotient (QuotientGroup.rightRel S),
        coinducedCosetValues A S f (QuotientGroup.quotientRightRelEquivQuotientLeftRel S q) := by
      apply Finset.sum_congr rfl
      intro q _
      induction q using Quotient.inductionOn with
      | h g =>
        change ((Rep.indResAdjunction R S.subtype).counit.app A).hom
          (Representation.IndV.mk S.subtype (Rep.res S.subtype A).ρ g (f.val g)) =
            A.ρ g⁻¹ (f.val (g⁻¹)⁻¹)
        rw [inv_inv]
        exact sourceNativeInductionCounit_mk A S g (f.val g)
    _ = _ := (QuotientGroup.quotientRightRelEquivQuotientLeftRel S).sum_comp
      (coinducedCosetValues A S f)

end
end Dubon2026
