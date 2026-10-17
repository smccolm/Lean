import Dubon2026.OriginalPrimeCoinducedClassification
import Dubon2026.OriginalScalarReductionHomology

/-! # The actual integral kernel's mod-p coinduced classification

The original norm and first-homology inputs imply first-homology
vanishing after literal reduction. The proved prime-torsion criterion
then identifies that actual reduction with coinduction of its own
coinvariants. This discharges the mod-p classification input to
DUB-17's fundamental-kernel projectivity argument.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

/-- The literal mod-p reduction of an original torsion-free coefficient with the two required low-degree vanishings is actually coinduced. -/
theorem originalPrimeReduction_coinduced_iso
    {G : Type} [Group G] [Fintype G] (A : Rep.{0} ℤ G)
    [Module.IsTorsionFree ℤ A] (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G)
    (hnorm : OriginalNormCoinvariantInjective A)
    (hfirst : Limits.IsZero (groupHomology A 1)) :
    Nonempty (originalScalarReduction A (p : ℤ) ≅
      originalCoinducedFunctionRep (originalCoinvariantTrivialRep (originalScalarReduction A (p : ℤ)))) := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hred := originalScalarReduction_first_homology_zero A (p : ℤ) hp0 hnorm hfirst
  have hp (x : originalScalarReduction A (p : ℤ)) : p • x = 0 := by
    exact (Nat.cast_smul_eq_nsmul ℤ p x).symm.trans
      (originalScalarReduction_annihilated A (p : ℤ) x)
  exact originalPrimeCoefficient_coinduced_iso _ p hG hp hred

/-- The actual free kernel of the original p-group coefficient has a literal mod-p coinduced classification, with integral freeness and both low-degree inputs derived. -/
theorem originalPGroup_relationKernel_prime_coinduced
    {G : Type} [Group G] [Fintype G] (B : Rep ℤ G)
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G)
    (h : ∀ S : Subgroup G,
      Limits.IsZero (groupCohomology (Rep.res S.subtype B) 1) ∧
        Limits.IsZero (groupCohomology (Rep.res S.subtype B) 2)) :
    Nonempty (originalScalarReduction (originalRelationModule B) (p : ℤ) ≅
      originalCoinducedFunctionRep (originalCoinvariantTrivialRep
        (originalScalarReduction (originalRelationModule B) (p : ℤ)))) := by
  letI := originalArbitraryRelationModule_free B
  have hK := originalPGroup_relationKernel_subgroup_first_second_zero B p hG h
  exact originalPrimeReduction_coinduced_iso (originalRelationModule B) p hG
    (originalPGroup_normCoinvariantInjective _ p hG hK)
    (originalPGroup_first_homology_zero _ p hG hK)

end
end Dubon2026
