import Dubon2026.SourceHeckeLaurentProductReduction

/-! DUB-17/18 -> Hecke/Picard reduction compatibility -> integrality
and residue of the original Hecke norm. Given its narrower, explicit
q-expanded product identity, injectivity and Laurent support recover an
integral preimage and the exact coefficient/geometric Frobenius product.
The actual Hecke norm identity is still to be supplied by the embedding
census; it is not assumed as a reduction or Picard compatibility result.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_kroneckerCongruence_norm_heckeBetaBar, unexpand and solution. -/
namespace Dubon2026.SourceFunctionField
noncomputable section

/-- Extract the coefficients at multiples of p from the integral norm product. -/
def heckeLaurentUnexpand {R : Type*} [CommRing R] (p : ℕ) [NeZero p]
    (y : LaurentSeries R) : LaurentSeries R where
  coeff n := y.coeff ((p : ℤ) * n)
  isPWO_support' := by
    have hp : (0 : ℤ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
    refine (y.isPWO_support.image_of_monotone (f := fun n : ℤ => n / (p : ℤ))
      (fun a b h => Int.ediv_le_ediv hp h)).mono ?_
    intro n hn
    refine ⟨(p : ℤ) * n, hn, ?_⟩
    exact Int.mul_ediv_cancel_left n hp.ne'

theorem qExpand_heckeLaurentUnexpand {R : Type*} [CommRing R] (p : ℕ) [NeZero p]
    (y : LaurentSeries R) (hy : ∀ n : ℤ, ¬ (p : ℤ) ∣ n → y.coeff n = 0) :
    qExpand R p (heckeLaurentUnexpand p y) = y := by
  ext n
  by_cases hn : (p : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := hn
    rw [qExpand_coeff_mul]
    rfl
  · rw [qExpand_coeff_of_not_dvd p _ hn, hy n hn]

theorem exists_integral_laurent_reduction_of_hecke_product
    {L : Type*} [Field L] (A : ValuationSubring L) (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField A) p] {ζ : L} (hζ : IsPrimitiveRoot ζ p)
    (y : LaurentSeries A) (n : LaurentSeries L)
    (hprod : coeffMap A.subtype (heckeLaurentProduct A p hζ y) = qExpand L p n) :
    ∃ y' : LaurentSeries A,
      coeffMap A.subtype y' = n ∧
      coeffMap (IsLocalRing.residue A) y' =
        coeffMap (frobenius (IsLocalRing.ResidueField A) p)
            (coeffMap (IsLocalRing.residue A) y) *
          qExpand (IsLocalRing.ResidueField A) p (coeffMap (IsLocalRing.residue A) y) := by
  have hs : ∀ k : ℤ, ¬ (p : ℤ) ∣ k → (heckeLaurentProduct A p hζ y).coeff k = 0 := by
    intro k hk
    have h := congrArg (fun z : LaurentSeries L => z.coeff k) hprod
    simp only [coeffMap_coeff, qExpand_coeff_of_not_dvd p _ hk] at h
    exact (map_eq_zero_iff A.subtype Subtype.val_injective).mp h
  refine ⟨heckeLaurentUnexpand p (heckeLaurentProduct A p hζ y), ?_, ?_⟩
  · apply qExpand_injective p
    rw [← coeffMap_qExpand, qExpand_heckeLaurentUnexpand p _ hs]
    exact hprod
  · apply qExpand_injective p
    rw [← coeffMap_qExpand, qExpand_heckeLaurentUnexpand p _ hs]
    exact heckeLaurentProduct_residue A p hζ y

end
end Dubon2026.SourceFunctionField
