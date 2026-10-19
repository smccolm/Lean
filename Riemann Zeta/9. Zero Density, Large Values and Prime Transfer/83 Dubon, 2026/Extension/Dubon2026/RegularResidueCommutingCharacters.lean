import Dubon2026.RegularResidueStrictDiagonalization
import Dubon2026.DiagonalCharacterFactorization

/-! One regular residual element diagonalizes the whole commuting local
image over the actual complete local coefficients. This uses the native
Hensel-adjugate basis once, avoiding any inverse system of chosen bases in
the auxiliary deformation-ring construction for Dubon Theorem 2.6. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing

private theorem regularResidue_commuting_diagonal
    {A ι : Type} [CommRing A] [IsLocalRing A] [Fintype ι] [DecidableEq ι]
    (l : ι → A) (hsep : Function.Injective (fun i => residue A (l i)))
    (M : Matrix ι ι A) (h : diagonal l * M = M * diagonal l) :
    M = diagonal (fun i => M i i) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp
  · have he := congrArg (fun X : Matrix ι ι A => X i j) h
    simp only [diagonal_mul, mul_diagonal] at he
    have hu : IsUnit (l i - l j) := by
      apply (residue_ne_zero_iff_isUnit _).mp
      rw [map_sub]
      exact sub_ne_zero.mpr (fun hh => hij (hsep hh))
    have hz : (l i - l j) * M i j = 0 := by
      rw [sub_mul, he, mul_comm (M i j), sub_self]
    have hz' : M i j = 0 := hu.mul_left_cancel (by simpa only [mul_zero] using hz)
    rw [hz', diagonal_apply_ne _ hij]

/-- An actual regular residual element in a commuting representation
constructs labelled characters in a single strict coefficient basis. -/
theorem regularResidue_commuting_character_decomposition
    {A ι G : Type} [CommRing A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] [Fintype ι] [DecidableEq ι] [Group G]
    (ρ : G →* GeneralLinearGroup ι A) (φ : G) (α : ι → ResidueField A)
    (hφ : (ρ φ).val.map (residue A) = diagonal α) (hα : Function.Injective α)
    (hcomm : ∀ g, Commute (ρ φ) (ρ g)) :
    ∃ (U : GeneralLinearGroup ι A) (χ : G →* (ι → A)ˣ),
      GeneralLinearGroup.map (residue A) U = 1 ∧
      (∀ g, diagonal (χ g).val = (MulAut.conj U⁻¹ (ρ g)).val) ∧
      ∀ i, residue A ((χ φ).val i) = α i := by
  obtain ⟨l, U, hl, hU, hFU⟩ := regularResidue_strict_diagonalization (ρ φ).val α hφ hα
  let σ := (MulAut.conj U⁻¹).toMonoidHom.comp ρ
  have hF : (σ φ).val = diagonal l := by
    change (U⁻¹).val * (ρ φ).val * U.val = diagonal l
    have h := congrArg (fun M : Matrix ι ι A => (U⁻¹).val * M) hFU
    simpa [← mul_assoc] using h
  have hsep : Function.Injective (fun i => residue A (l i)) := by
    intro i j hij
    apply hα
    simpa only [hl] using hij
  have hσ (g) : (σ g).val = diagonal (fun i => (σ g).val i i) := by
    apply regularResidue_commuting_diagonal l hsep
    have hc := (hcomm g).map (MulAut.conj U⁻¹).toMonoidHom
    have he := congrArg Units.val hc.eq
    simpa only [Units.val_mul, ← show (MulAut.conj U⁻¹ (ρ φ)).val = diagonal l from hF] using he
  obtain ⟨χ, hχ⟩ := diagonal_representation_exists_characters σ hσ
  refine ⟨U, χ, hU, hχ, ?_⟩
  have he : (χ φ).val = l := diagonal_injective ((hχ φ).trans hF)
  intro i
  rw [he, hl]

end
end Dubon2026
