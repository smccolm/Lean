import Dubon2026.SourceOriginalWeilPairingDescent
import Dubon2026.SourceOriginalTorsionGalois

/-! DUB-17/18 -> Frobenius determinant -> cyclotomic compatibility
of the original pairing. The already constructed arithmetic divisor and
coefficient actions descend to the actual root-valued Picard pairing. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
variable {N : ℕ} [NeZero N] {L : Type*} [Field L] [Algebra ℚ L] [IsAlgClosed L]
variable {n : ℕ} [NeZero n]

namespace OriginalWeilDatum

theorem classLeft_arithmetic (d : OriginalWeilDatum N L n) (σ : L ≃ₐ[ℚ] L) :
    (d.arithmetic σ).classLeft =
      ⟨originalArithmeticPicard N σ d.classLeft.val,
        originalArithmeticPicard_torsion N σ n d.classLeft.val d.classLeft.property⟩ := by
  exact Subtype.ext (originalArithmeticPicard_mk N σ ⟨d.D₁, d.degree_first⟩).symm

theorem classRight_arithmetic (d : OriginalWeilDatum N L n) (σ : L ≃ₐ[ℚ] L) :
    (d.arithmetic σ).classRight =
      ⟨originalArithmeticPicard N σ d.classRight.val,
        originalArithmeticPicard_torsion N σ n d.classRight.val d.classRight.property⟩ := by
  exact Subtype.ext (originalArithmeticPicard_mk N σ ⟨d.D₂, d.degree_second⟩).symm

end OriginalWeilDatum

theorem originalWeilPairing_arithmetic (σ : L ≃ₐ[ℚ] L)
    (x y : Pic0.torsion (K := L) (F := modularFunctionFieldOver N L) n) :
    ((originalWeilPairing N L n
      ⟨originalArithmeticPicard N σ x.val, originalArithmeticPicard_torsion N σ n x.val x.property⟩
      ⟨originalArithmeticPicard N σ y.val, originalArithmeticPicard_torsion N σ n y.val y.property⟩ : Lˣ) : L) =
      σ ((originalWeilPairing N L n x y : Lˣ) : L) := by
  obtain ⟨d, rfl, rfl⟩ := exists_original_weil_representative N L n x y
  rw [← d.classLeft_arithmetic σ, ← d.classRight_arithmetic σ,
    originalWeilPairing_eq_pairing, originalWeilPairing_eq_pairing, d.arithmetic_pairing]

theorem originalWeilPairing_originalGalois
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x y : originalJZeroTorsion N n) :
    ((originalWeilPairing N (AlgebraicClosure ℚ) n
      (originalJZeroTorsionGaloisRep N n σ x)
      (originalJZeroTorsionGaloisRep N n σ y) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
      σ ((originalWeilPairing N (AlgebraicClosure ℚ) n x y : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) := by
  have hx : originalJZeroTorsionGaloisRep N n σ x =
      ⟨originalArithmeticPicard N σ x.val, originalArithmeticPicard_torsion N σ n x.val x.property⟩ :=
    Subtype.ext (originalJZeroTorsionGaloisRep_apply N n σ x)
  have hy : originalJZeroTorsionGaloisRep N n σ y =
      ⟨originalArithmeticPicard N σ y.val, originalArithmeticPicard_torsion N σ n y.val y.property⟩ :=
    Subtype.ext (originalJZeroTorsionGaloisRep_apply N n σ y)
  rw [hx, hy]
  exact originalWeilPairing_arithmetic σ x y

end
end Dubon2026.SourceFunctionField
