import Dubon2026.RegularResidueStrictDiagonalization
import Dubon2026.TameRegularDiagonal

/-! # Simultaneous strict diagonalization of tame Frobenius and inertia

This assembles the actual matrix equations and the constructed Frobenius basis
for the auxiliary local deformation conditions required by Dubon Theorem 2.6.
-/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing

/-- A regular residual Frobenius and residually trivial tame inertia have a
common basis reducing to the identity. In that basis every inertia entry has
the required prime-power equation, with no supplied diagonalizing basis. -/
theorem regularResidue_tame_strict_diagonalization
    {A ι : Type} [CommRing A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] [Fintype ι] [DecidableEq ι]
    (F T : GeneralLinearGroup ι A) (α : ι → ResidueField A)
    (hF : F.val.map (residue A) = diagonal α) (hα : Function.Injective α)
    (hT : GeneralLinearGroup.map (residue A) T = 1)
    (p : ℕ) (hp : (p : ResidueField A) = 1)
    (hrel : F * T * F⁻¹ = T ^ p) :
    ∃ (U : GeneralLinearGroup ι A) (l t : ι → A),
      GeneralLinearGroup.map (residue A) U = 1 ∧
      (MulAut.conj U⁻¹ F).val = diagonal l ∧
      (MulAut.conj U⁻¹ T).val = diagonal t ∧
      (∀ i, residue A (l i) = α i) ∧
      (∀ i, residue A (t i) = 1) ∧
      (∀ i, IsUnit (l i)) ∧ (∀ i, IsUnit (t i)) ∧
      ∀ i, (t i) ^ p = t i := by
  classical
  obtain ⟨l, U, hl, hU, hFU⟩ := regularResidue_strict_diagonalization F.val α hF hα
  let c : GeneralLinearGroup ι A ≃* GeneralLinearGroup ι A := MulAut.conj U⁻¹
  have hcF : (c F).val = diagonal l := by
    change (U⁻¹).val * F.val * U.val = diagonal l
    have h := congrArg (fun M : Matrix ι ι A => (U⁻¹).val * M) hFU
    simpa [← mul_assoc] using h
  have hmap (X : GeneralLinearGroup ι A) :
      GeneralLinearGroup.map (residue A) (c X) =
        GeneralLinearGroup.map (residue A) X := by
    simp [c, hU]
  have hresT : (c T).val.map (residue A) = 1 := by
    have h := (hmap T).trans hT
    exact congrArg Units.val h
  have hsep : Function.Injective (fun i => residue A (l i)) := by
    intro i j hij
    apply hα
    simpa only [hl] using hij
  have hFT : F * T = T ^ p * F := mul_inv_eq_iff_eq_mul.mp hrel
  have hct : c F * c T = c T ^ p * c F := by
    simpa only [map_mul, map_pow] using congrArg c hFT
  have hmat : diagonal l * (c T).val = (c T).val ^ p * diagonal l := by
    have h := congrArg Units.val hct
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val, hcF] using h
  let t : ι → A := fun i => (c T).val i i
  have ht : (c T).val = diagonal t :=
    regularResidue_tame_diagonal l hsep p hp (c T).val hresT hmat
  have hlu : ∀ i, IsUnit (l i) := by
    have h := (c F).isUnit
    rw [hcF, isUnit_diagonal] at h
    exact fun i => h.map (Pi.evalRingHom _ i)
  have htu : ∀ i, IsUnit (t i) := by
    have h := (c T).isUnit
    rw [ht, isUnit_diagonal] at h
    exact fun i => h.map (Pi.evalRingHom _ i)
  refine ⟨U, l, t, hU, hcF, ht, hl, ?_, hlu, htu, ?_⟩
  · intro i
    have h := congrArg (fun M : Matrix ι ι (ResidueField A) => M i i) hresT
    simpa [t] using h
  · intro i
    rw [ht, diagonal_pow] at hmat
    have h := congrArg (fun M : Matrix ι ι A => M i i) hmat
    simp only [diagonal_mul, diagonal_apply_eq, Pi.pow_apply] at h
    exact (hlu i).mul_left_cancel (by simpa only [mul_comm] using h.symm)

end
end Dubon2026
