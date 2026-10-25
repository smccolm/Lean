import Dubon2026.SourceOriginalWeilKummerRadicand
import Dubon2026.SourceCurveKummerRootAutomorphism

/-! DUB-17/18 -> original Weil nondegeneracy -> concrete auxiliary cover.
The input is a nonzero class in the existing original Picard torsion group.
Its actual principal function and splitting-field root produce a nontrivial
constant-valued Galois multiplier. Auxiliary-cover divisibility is still open. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve Polynomial
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]

theorem originalPic0_nonzero_torsion_kummer_cover (n : ℕ) [NeZero n]
    (x : Pic0.torsion (K := L) (F := modularFunctionFieldOver N L) n) (hx : x ≠ 0) :
    ∃ (D : Divisor.degZero (K := L) (F := modularFunctionFieldOver N L))
      (f : modularFunctionFieldOver N L),
      Pic0.mk D = x.val ∧ f ≠ 0 ∧
        (∀ v, v.ord f = (n : ℤ) * D.val v) ∧
        (∀ g : modularFunctionFieldOver N L, g ^ n ≠ f) ∧
        ∃ (h : (X ^ n - C f).SplittingField)
          (σ : (X ^ n - C f).SplittingField ≃ₐ[modularFunctionFieldOver N L]
            (X ^ n - C f).SplittingField) (ζ : L),
          ζ ≠ 1 ∧ h ^ n = algebraMap (modularFunctionFieldOver N L)
            (X ^ n - C f).SplittingField f ∧
          σ h = algebraMap L (X ^ n - C f).SplittingField ζ * h := by
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  obtain ⟨D, f, hD, hf, hord, hnp⟩ := originalPic0_nonzero_torsion_kummer_data N L n x hx
  exact ⟨D, f, hD, hf, hord, hnp,
    KummerCover.exists_root_moved_by_constant L (modularFunctionFieldOver N L) n f hf hnp⟩

end
end Dubon2026.SourceFunctionField
