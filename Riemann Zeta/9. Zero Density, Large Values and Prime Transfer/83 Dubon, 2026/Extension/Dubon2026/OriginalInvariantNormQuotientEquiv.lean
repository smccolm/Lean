import Dubon2026.OriginalTrivialSourceInvariants
import Dubon2026.OriginalFundamentalAbelianNormIndex

/-! # The actual invariant norm quotient and abelianization

The evaluation comparison carries the literal morphism norm range to
the actual invariant norm range. The resulting abelianization and
order statements are the original-coefficient input for DUB-17's
arithmetic norm-index and prescribed-support norm-field construction.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2 Submodule.module Submodule.Quotient.module

variable {G : Type} [Group G] [Fintype G] (C : Rep.{0} ℤ G)

/-- The actual invariant coefficient modulo literal norms. -/
abbrev OriginalInvariantNormQuotient := C.ρ.invariants ⧸ (originalInvariantNormLinear C).range

/-- Evaluation at one carries exactly the original morphism norm range to the actual invariant norm range. -/
theorem originalTrivialSourceInvariantEquiv_norm_range :
    (originalCoefficientNormLinearMap (Rep.trivial ℤ G ℤ) C).range.map
      (originalTrivialSourceInvariantEquiv C).toLinearMap =
        (originalInvariantNormLinear C).range := by
  ext x
  constructor
  · rintro ⟨χ, ⟨η, rfl⟩, rfl⟩
    exact ⟨η 1, (originalTrivialSourceInvariantEquiv_norm C η).symm⟩
  · rintro ⟨c, rfl⟩
    let η : Rep.trivial ℤ G ℤ →ₗ[ℤ] C := LinearMap.toSpanSingleton ℤ C c
    refine ⟨originalCoefficientNormMorphism (Rep.trivial ℤ G ℤ) C η, ⟨η, rfl⟩, ?_⟩
    exact (originalTrivialSourceInvariantEquiv_norm C η).trans
      (congrArg (originalInvariantNormLinear C) (LinearMap.toSpanSingleton_apply_one ℤ C c))

/-- The existing trivial-source morphism norm quotient is exactly the original invariant norm quotient. -/
def originalTrivialSourceNormQuotientEquiv :
    OriginalCoefficientNormQuotient (Rep.trivial ℤ G ℤ) C ≃ₗ[ℤ]
      OriginalInvariantNormQuotient C :=
  Submodule.Quotient.equiv _ _ (originalTrivialSourceInvariantEquiv C)
    (originalTrivialSourceInvariantEquiv_norm_range C)

variable (φ : groupCohomology.cocycles₂ C) (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G)
  (h : ∀ S : Subgroup G,
    Limits.IsZero (groupCohomology
      (Rep.res S.subtype (originalFundamentalSplittingModule C φ)) 1) ∧
    Limits.IsZero (groupCohomology
      (Rep.res S.subtype (originalFundamentalSplittingModule C φ)) 2))

/-- The actual invariant norm quotient is the additive abelianization for the same fundamental coefficient. -/
def originalInvariantNormAbelianEquiv :
    OriginalInvariantNormQuotient C ≃+ Additive (Abelianization G) :=
  (originalTrivialSourceNormQuotientEquiv C).symm.toAddEquiv.trans
    (originalFundamentalAbelianNormEquiv C φ p hG h)

include φ p hG h in
/-- The actual invariant norm quotient has the abelianization order. -/
theorem originalInvariantNormQuotient_card :
    Nat.card (OriginalInvariantNormQuotient C) = Nat.card (Abelianization G) :=
  Nat.card_congr (originalInvariantNormAbelianEquiv C φ p hG h).toEquiv

include φ p hG h in
/-- A group exponent constructs literal norm preimages of multiples of every original invariant. -/
theorem originalInvariant_multiple_is_norm (n : ℕ) (hn : ∀ g : G, g ^ n = 1)
    (c : C.ρ.invariants) : ∃ b : C, originalInvariantNormLinear C b = n • c := by
  let e := (originalTrivialSourceNormQuotientEquiv C).toAddEquiv
  have hz := originalFundamental_norm_quotient_exponent C φ p hG h n hn
    (e.symm (Submodule.Quotient.mk c))
  have he := congrArg e hz
  rw [map_nsmul, e.apply_symm_apply, map_zero] at he
  have hq : (Submodule.Quotient.mk (n • c) : OriginalInvariantNormQuotient C) = 0 := by
    exact (map_nsmul (originalInvariantNormLinear C).range.mkQ n c).trans he
  exact (Submodule.Quotient.mk_eq_zero _).mp hq

end
end Dubon2026
