import Dubon2026.SourceBinaryCohomologyChange
import Dubon2026.SourceHeckeCoefficientMorphism

/-! The actual Hecke coefficient morphism over the integral and residual rings.
DUB-17/18 -> residual modular Galois association -> residual H1 eigensystem
-> integral Hecke action and its coefficient change. The original integral
adjugate conjugation equation supplies equivariance over every coefficient ring.
-/

namespace Dubon2026
noncomputable section
open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup SourceModularSymbols CategoryTheory

variable (R : Type) [CommRing R] {Q p : ℕ} [NeZero p]

omit [NeZero p] in
/-- The original integral adjugate diagonal has its literal column matrix over every coefficient ring. -/
theorem sourceBinaryHeckeDiagonalMatrix :
    ((integralTriangularMatrix 1 p 0).adjugate).map (Int.castRingHom R) =
      Matrix.diagonal ![(p : R), 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [integralTriangularMatrix, Matrix.adjugate_fin_two]

/-- The actual column diagonal intertwines the original Hecke subgroup conjugation over any ring. -/
theorem sourceBinaryHeckeDiagonal_intertwine (hp : Nat.Prime p) (w : ℕ)
    (g : heckeUpperSubgroup Q p) :
    (homogeneousMatrixAction w (Matrix.diagonal ![(p : R), 1])).comp
        ((sourceBinaryCoefficientRep R Q w).ρ (sourceHeckeConjugation hp g)) =
      ((sourceBinaryCoefficientRep R Q w).ρ g.val).comp
        (homogeneousMatrixAction w (Matrix.diagonal ![(p : R), 1])) := by
  have hm := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ =>
    M.map (Int.castRingHom R)) (sourceHeckeConjugation_adjugate hp g)
  simp only [Matrix.map_mul, sourceBinaryHeckeDiagonalMatrix] at hm
  have h := congrArg (homogeneousMatrixRepresentation (R := R) w) hm
  simpa only [map_mul] using h

/-- The original binary Hecke coefficient morphism, with actual integral equivariance proved. -/
def sourceBinaryHeckeMorphism (hp : Nat.Prime p) (w : ℕ) :
    Rep.res (sourceHeckeConjugation (Q := Q) hp) (sourceBinaryCoefficientRep R Q w) ⟶
      Rep.res (heckeUpperSubgroup Q p).subtype (sourceBinaryCoefficientRep R Q w) :=
  Rep.ofHom {
    toLinearMap := homogeneousMatrixAction w (Matrix.diagonal ![(p : R), 1])
    isIntertwining' := sourceBinaryHeckeDiagonal_intertwine R hp w }

end
end Dubon2026
