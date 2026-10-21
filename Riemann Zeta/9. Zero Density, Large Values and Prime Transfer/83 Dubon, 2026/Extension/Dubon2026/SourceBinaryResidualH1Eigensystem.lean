import Dubon2026.SourceOperatorCharacterTensorEigenvector
import Dubon2026.SourceBinaryH1TensorInjection
import Dubon2026.SourcePrimitiveResidualH1Character

/-! Realize the actual integral H1 character on original residual cohomology.
DUB-17/18 -> residual modular Galois association -> nonzero residual H1
eigensystem. This consumer discharges finite integral H1, existence of the
nonzero tensor eigenclass, tensor injectivity and full coefficient/Hecke
compatibility. Pairwise commutativity of the actual integral H1 operators
is the remaining explicit hypothesis of this intermediate theorem.
-/

namespace Dubon2026
noncomputable section

/-- A character of the actual integral H1 Hecke algebra is realized by a nonzero
original residual H1 class once its actual good-prime operators are proved to commute. -/
theorem sourceBinaryH1HeckeCharacter_exists_residualEigenclass (Q w : ℕ) [NeZero Q]
    (ell : ℕ) (hell : ell.Prime) (F : Type) [Field F] [CharP F ell]
    (hcomm : ∀ p q : sourceBinaryHeckePrime Q,
      Commute (sourceBinaryH1PrimeOperators ℤ Q w p) (sourceBinaryH1PrimeOperators ℤ Q w q))
    (χ : sourceBinaryH1HeckeAlgebra Q w →ₐ[ℤ] F) :
    ∃ v : groupCohomology.H1 (sourceBinaryCoefficientRep F Q w), v ≠ 0 ∧
      ∀ p : sourceBinaryHeckePrime Q,
        sourceBinaryH1PrimeOperators F Q w p v =
          χ ⟨sourceBinaryH1PrimeOperators ℤ Q w p, Algebra.subset_adjoin ⟨p, rfl⟩⟩ • v := by
  letI := sourceIntegralBinaryH1Finite Q w
  obtain ⟨y, hy, heig⟩ := sourceOperatorCharacter_exists_tensorEigenvector
    (F := F) (sourceBinaryH1PrimeOperators ℤ Q w) hcomm χ
  refine ⟨sourceBinaryH1TensorChange F Q w y, ?_, fun p => ?_⟩
  · intro h
    exact hy ((sourceBinaryH1TensorChange_injective Q w ell hell F)
      (h.trans (map_zero _).symm))
  · letI : NeZero p.val := ⟨p.property.1.ne_zero⟩
    change sourceBinaryHeckeH1 F p.property.1 w (sourceBinaryH1TensorChange F Q w y) = _
    rw [← sourceBinaryH1TensorChange_hecke]
    change sourceBinaryH1TensorChange F Q w
      ((sourceBinaryH1PrimeOperators ℤ Q w p).baseChange F y) = _
    rw [heig p, map_smul]
    rfl

end
end Dubon2026
