import Dubon2026.SourceHeckePrimeRootReduction
import Dubon2026.SourceLaurentFrobenius
import Dubon2026.SourceLaurentCoefficientReindex

/-! DUB-17/18 -> Hecke/Picard reduction compatibility -> the actual
norm residue formula. The prime-order twists in the literal integral
Laurent product reduce to one. The full product therefore reduces to the
q-expansion of coefficient Frobenius times geometric Frobenius. Identifying
this product with the actual degeneracy norm is a separate upstream step. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
variable {L : Type*} [Field L] (A : ValuationSubring L) (p : ℕ) [Fact p.Prime]
local notation "kk" => IsLocalRing.ResidueField A

/-- The explicit integral Laurent product occurring in the prime Hecke norm. -/
def heckeLaurentProduct {ζ : L} (hζ : IsPrimitiveRoot ζ p) (y : LaurentSeries A) :
    LaurentSeries A :=
  (∏ b ∈ Finset.range p, qTwist (primeRootValuationUnit A p hζ ^ b) y) *
    qExpand A p (qExpand A p y)

theorem heckeLaurentProduct_residue [CharP kk p]
    {ζ : L} (hζ : IsPrimitiveRoot ζ p) (y : LaurentSeries A) :
    coeffMap (IsLocalRing.residue A) (heckeLaurentProduct A p hζ y) =
      qExpand kk p
        (coeffMap (frobenius kk p) (coeffMap (IsLocalRing.residue A) y) *
          qExpand kk p (coeffMap (IsLocalRing.residue A) y)) := by
  rw [heckeLaurentProduct, map_mul, map_prod, coeffMap_qExpand, coeffMap_qExpand,
    Finset.prod_eq_pow_card (b := coeffMap (IsLocalRing.residue A) y), Finset.card_range,
    map_mul, ← coeffMap_qExpand (frobenius kk p) p,
    ← pow_char_eq_coeffMap_frobenius_qExpand]
  intro b _
  rw [coeffMap_qTwist_commRing, map_pow, primeRootValuationUnit_residue,
    one_pow, qTwist_one_apply]

end
end Dubon2026.SourceFunctionField
