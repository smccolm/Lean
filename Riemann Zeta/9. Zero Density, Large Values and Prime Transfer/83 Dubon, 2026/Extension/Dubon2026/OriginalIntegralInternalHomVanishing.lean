import Dubon2026.OriginalInternalHomCoinducedTransfer
import Dubon2026.OriginalScalarCohomologyLifting

/-! # Integral internal-Hom H1 vanishing for the original p-group kernel

The proved actual mod-p classification kills reduced internal-Hom H1.
The genuine scalar sequence gives prime divisibility, and the existing
group-order annihilation theorem forces the original integral H1 to
vanish. This is the precise input that splits the actual free cover in
DUB-17's fundamental-kernel projectivity argument.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

/-- For the original integral free source and torsion-free target, the actual two low-degree source conditions force internal-Hom H1 vanishing for a finite p-group. -/
theorem originalIntegralInternalHom_first_zero
    {G : Type} [Group G] [Fintype G] (A R : Rep.{0} ℤ G)
    [Module.Free ℤ A] [Module.IsTorsionFree ℤ R]
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G)
    (hnorm : OriginalNormCoinvariantInjective A)
    (hfirst : Limits.IsZero (groupHomology A 1)) :
    Limits.IsZero (groupCohomology ((Rep.ihom A).obj R) 1) := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hred := originalPrimeReducedInternalHom_positive_zero A R p hG hnorm hfirst 0
  exact originalPGroup_first_cohomology_zero_of_prime_divisibility ((Rep.ihom A).obj R) p hG
    (originalInternalHom_first_prime_divisible A R p hp0 hred)

/-- The actual fundamental free kernel has zero internal-Hom H1 into every original torsion-free coefficient, with integral freeness and both low-degree source conditions derived. -/
theorem originalPGroup_relationKernel_internalHom_first_zero
    {G : Type} [Group G] [Fintype G] (B R : Rep.{0} ℤ G)
    [Module.IsTorsionFree ℤ R] (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G)
    (h : ∀ S : Subgroup G,
      Limits.IsZero (groupCohomology (Rep.res S.subtype B) 1) ∧
        Limits.IsZero (groupCohomology (Rep.res S.subtype B) 2)) :
    Limits.IsZero (groupCohomology ((Rep.ihom (originalRelationModule B)).obj R) 1) := by
  letI := originalArbitraryRelationModule_free B
  have hK := originalPGroup_relationKernel_subgroup_first_second_zero B p hG h
  exact originalIntegralInternalHom_first_zero (originalRelationModule B) R p hG
    (originalPGroup_normCoinvariantInjective _ p hG hK)
    (originalPGroup_first_homology_zero _ p hG hK)

end
end Dubon2026
