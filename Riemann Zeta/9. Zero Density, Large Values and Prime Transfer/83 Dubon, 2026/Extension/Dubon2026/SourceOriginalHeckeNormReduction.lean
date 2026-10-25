import Dubon2026.SourceOriginalHeckeNormProduct
import Dubon2026.SourceHeckeLaurentNormExtraction

/-! DUB-17/18 -> Hecke/Picard reduction compatibility. The actual norm
product discharges the earlier conditional extraction lemma. Thus the
original Hecke norm of every integral Laurent modular function is integral,
with residue exactly coefficient Frobenius times geometric Frobenius.
No norm-product or Atkin compatibility hypothesis remains. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open HeckeNorm
local notation "Qbar" => AlgebraicClosure ℚ
variable (N p : ℕ) [NeZero N] [hp : Fact p.Prime]
variable (A : ValuationSubring Qbar) [CharP (IsLocalRing.ResidueField A) p]
local notation "kk" => IsLocalRing.ResidueField A
attribute [local instance] HeckeNorm.alphaAlgebra

theorem original_hecke_norm_integral_reduction (hpN : ¬ p ∣ N)
    (y : LaurentSeries A)
    (hy : coeffMap A.subtype y ∈ modularFunctionFieldOver N Qbar) :
    ∃ y' : LaurentSeries A,
      coeffMap A.subtype y' =
        (Algebra.norm (modularFunctionFieldOver N Qbar)
          (originalHeckeBeta Qbar N p ⟨coeffMap A.subtype y, hy⟩) : LaurentSeries Qbar) ∧
      coeffMap (IsLocalRing.residue A) y' =
        coeffMap (frobenius kk p) (coeffMap (IsLocalRing.residue A) y) *
          qExpand kk p (coeffMap (IsLocalRing.residue A) y) := by
  haveI : Algebra.IsAlgebraic ℚ Qbar := AlgebraicClosure.isAlgebraic ℚ
  haveI : NeZero (p : ℚ) := ⟨Nat.cast_ne_zero.mpr hp.out.ne_zero⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Qbar p
  let ζ : Qbarˣ := Units.map A.subtype.toMonoidHom (primeRootValuationUnit A p hz)
  have hζ : IsPrimitiveRoot (ζ : Qbar) p := by
    change IsPrimitiveRoot ((primeRootValuationUnit A p hz : A) : Qbar) p
    rw [primeRootValuationUnit_coe]
    exact hz
  apply exists_integral_laurent_reduction_of_hecke_product A p hz y
  rw [heckeLaurentProduct, map_mul, map_prod, coeffMap_qExpand, coeffMap_qExpand]
  have hnorm := original_hecke_norm_expanded_product Qbar N p hpN ζ hζ
    ⟨coeffMap A.subtype y, hy⟩
  rw [hnorm]
  congr 1
  apply Finset.prod_congr rfl
  intro b _
  rw [coeffMap_qTwist_commRing, map_pow]

end
end Dubon2026.SourceFunctionField
