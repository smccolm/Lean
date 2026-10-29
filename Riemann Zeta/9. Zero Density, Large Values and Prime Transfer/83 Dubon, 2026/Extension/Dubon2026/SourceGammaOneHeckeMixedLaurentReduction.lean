import Dubon2026.SourceHeckeLaurentNormExtraction

/-! DUB-17/18 -> original Gamma1 Tate Frobenius -> diamond-correct norm
reduction. The original Laurent extraction argument applies with separate
integral inputs for the diamond-transformed function and the original
function. This proves the required two-input coefficient calculation;
integrality of the actual diamond image is a separate geometric obligation.
No new curve, valuation or general norm framework is introduced. -/
namespace Dubon2026.SourceFunctionField.GammaOne.HeckeNorm
noncomputable section
variable {L : Type*} [Field L] (A : ValuationSubring L) (p : ℕ) [Fact p.Prime]
local notation "kk" => IsLocalRing.ResidueField A

/-- The integral norm product with its distinct diamond and original inputs. -/
def diamondLaurentProduct {ζ : L} (hζ : IsPrimitiveRoot ζ p)
    (u y : LaurentSeries A) : LaurentSeries A :=
  (∏ b ∈ Finset.range p, qTwist (primeRootValuationUnit A p hζ ^ b) u) *
    qExpand A p (qExpand A p y)

theorem diamondLaurentProduct_residue [CharP kk p]
    {ζ : L} (hζ : IsPrimitiveRoot ζ p) (u y : LaurentSeries A) :
    coeffMap (IsLocalRing.residue A) (diamondLaurentProduct A p hζ u y) =
      qExpand kk p
        (coeffMap (frobenius kk p) (coeffMap (IsLocalRing.residue A) u) *
          qExpand kk p (coeffMap (IsLocalRing.residue A) y)) := by
  rw [diamondLaurentProduct, map_mul, map_prod, coeffMap_qExpand, coeffMap_qExpand,
    Finset.prod_eq_pow_card (b := coeffMap (IsLocalRing.residue A) u), Finset.card_range,
    map_mul, ← coeffMap_qExpand (frobenius kk p) p,
    ← pow_char_eq_coeffMap_frobenius_qExpand]
  intro b _
  rw [coeffMap_qTwist_commRing, map_pow, primeRootValuationUnit_residue,
    one_pow, qTwist_one_apply]

theorem exists_integral_reduction_of_diamond_product [CharP kk p]
    {ζ : L} (hζ : IsPrimitiveRoot ζ p) (u y : LaurentSeries A) (n : LaurentSeries L)
    (hprod : coeffMap A.subtype (diamondLaurentProduct A p hζ u y) = qExpand L p n) :
    ∃ y' : LaurentSeries A,
      coeffMap A.subtype y' = n ∧
      coeffMap (IsLocalRing.residue A) y' =
        coeffMap (frobenius kk p) (coeffMap (IsLocalRing.residue A) u) *
          qExpand kk p (coeffMap (IsLocalRing.residue A) y) := by
  have hs : ∀ k : ℤ, ¬ (p : ℤ) ∣ k → (diamondLaurentProduct A p hζ u y).coeff k = 0 := by
    intro k hk
    have h := congrArg (fun z : LaurentSeries L => z.coeff k) hprod
    simp only [coeffMap_coeff, qExpand_coeff_of_not_dvd p _ hk] at h
    exact (map_eq_zero_iff A.subtype Subtype.val_injective).mp h
  refine ⟨heckeLaurentUnexpand p (diamondLaurentProduct A p hζ u y), ?_, ?_⟩
  · apply qExpand_injective p
    rw [← coeffMap_qExpand, qExpand_heckeLaurentUnexpand p _ hs]
    exact hprod
  · apply qExpand_injective p
    rw [← coeffMap_qExpand, qExpand_heckeLaurentUnexpand p _ hs]
    exact diamondLaurentProduct_residue A p hζ u y

end
end Dubon2026.SourceFunctionField.GammaOne.HeckeNorm
