import Dubon2026.OriginalFundamentalNormHomologyEquiv
import Dubon2026.OriginalTrivialDualHomology

/-! # The original trivial-source norm quotient has the abelianization order

The proved norm-homology equivalence and pinned H1 identification give
the exact finite index and its exponent. Arithmetic base invariants
must still identify this with the actual field norm quotient used in
DUB-17's prescribed-support norm-field construction.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped IsMulCommutative
attribute [local instance 1100] Rep.hV2

variable {G : Type} [Group G] [Fintype G] (C : Rep.{0} ℤ G)
  (φ : groupCohomology.cocycles₂ C) (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G)
  (h : ∀ S : Subgroup G,
    Limits.IsZero (groupCohomology
      (Rep.res S.subtype (originalFundamentalSplittingModule C φ)) 1) ∧
    Limits.IsZero (groupCohomology
      (Rep.res S.subtype (originalFundamentalSplittingModule C φ)) 2))

/-- The actual trivial-source coefficient norm quotient is the additive abelianization. -/
def originalFundamentalAbelianNormEquiv :
    OriginalCoefficientNormQuotient (Rep.trivial ℤ G ℤ) C ≃+ Additive (Abelianization G) :=
  (originalFundamentalNormHomologyEquiv (Rep.trivial ℤ G ℤ) C φ p hG h).toAddEquiv.trans
    (originalTrivialDualHomologyEquiv G)

include φ p hG h in
/-- The literal original norm quotient has exactly the order of the abelianization. -/
theorem originalFundamental_abelian_norm_index :
    Nat.card (OriginalCoefficientNormQuotient (Rep.trivial ℤ G ℤ) C) =
      Nat.card (Abelianization G) :=
  Nat.card_congr (originalFundamentalAbelianNormEquiv C φ p hG h).toEquiv

include φ p hG h in
/-- A group exponent annihilates the original trivial-source coefficient norm quotient. -/
theorem originalFundamental_norm_quotient_exponent (n : ℕ) (hn : ∀ g : G, g ^ n = 1)
    (x : OriginalCoefficientNormQuotient (Rep.trivial ℤ G ℤ) C) : n • x = 0 := by
  let e := originalFundamentalAbelianNormEquiv C φ p hG h
  apply e.injective
  rw [map_nsmul, map_zero]
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (e x).toMul
  change Abelianization.of g = (e x).toMul at hg
  apply Additive.toMul.injective
  change (e x).toMul ^ n = 1
  rw [← hg, ← map_pow, hn, map_one]

include φ p hG h in
/-- For an abelian group, the original coefficient norm quotient has exactly the group order. -/
theorem originalFundamental_commutative_norm_index [IsMulCommutative G] :
    Nat.card (OriginalCoefficientNormQuotient (Rep.trivial ℤ G ℤ) C) = Nat.card G := by
  exact (originalFundamental_abelian_norm_index C φ p hG h).trans
    (Nat.card_congr (Abelianization.equivOfComm (H := G)).toEquiv).symm

end
end Dubon2026
