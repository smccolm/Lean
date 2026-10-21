import Dubon2026.SourceBinaryHeckeMorphism
import Dubon2026.SourceHeckeCohomologyTrace

/-! The full original binary Hecke correspondence over every coefficient ring.
DUB-17/18 -> residual modular Galois association -> residual H1 eigensystem
-> integral Hecke action. This uses the actual diagonal conjugation and
finite coset trace, so it is defined on the full native H1.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup CategoryTheory

variable (R : Type) [CommRing R] {p Q : ℕ} [NeZero p] (hp : Nat.Prime p) (w : ℕ)

private local instance sourceBinaryHeckeCohomologyFintype :
    Fintype (Gamma0 Q ⧸ heckeUpperSubgroup Q p) :=
  sourceHeckeUpperFintype Q p

/-- The original prime Hecke correspondence on every binary cocycle over the actual coefficient ring. -/
def sourceBinaryHeckeCocycle :
    Module.End R (groupCohomology.cocycles₁ (sourceBinaryCoefficientRep R Q w)) :=
  (sourceHeckeTraceCocycles (sourceBinaryCoefficientRep R Q w) (heckeUpperSubgroup Q p)).comp
    (groupCohomology.mapCocycles₁ (sourceHeckeConjugation hp)
      (sourceBinaryHeckeMorphism R hp w)).hom

/-- The original prime Hecke correspondence on the full native binary H1 over the actual ring. -/
def sourceBinaryHeckeH1 :
    Module.End R (groupCohomology.H1 (sourceBinaryCoefficientRep R Q w)) :=
  (sourceHeckeH1Trace (sourceBinaryCoefficientRep R Q w) (heckeUpperSubgroup Q p)).comp
    (groupCohomology.map (sourceHeckeConjugation hp)
      (sourceBinaryHeckeMorphism R hp w) 1).hom

/-- The full original binary H1 operator is represented by its genuine Hecke cocycle. -/
theorem sourceBinaryHeckeH1_cocycle
    (c : groupCohomology.cocycles₁ (sourceBinaryCoefficientRep R Q w)) :
    sourceBinaryHeckeH1 R hp w (groupCohomology.H1π _ c) =
      groupCohomology.H1π _ (sourceBinaryHeckeCocycle R hp w c) := by
  change sourceHeckeH1Trace _ _
    ((groupCohomology.map (sourceHeckeConjugation hp) (sourceBinaryHeckeMorphism R hp w) 1)
      (groupCohomology.H1π _ c)) = _
  rw [groupCohomology.H1π_comp_map_apply, sourceHeckeH1Trace_cocycle]
  rfl

/-- Over every coefficient ring the actual Hecke cocycle is the full original finite coset sum. -/
theorem sourceBinaryHeckeCocycle_apply
    (c : groupCohomology.cocycles₁ (sourceBinaryCoefficientRep R Q w))
    (g : Gamma0 Q) :
    sourceBinaryHeckeCocycle R hp w c g =
      ∑ q : Gamma0 Q ⧸ heckeUpperSubgroup Q p,
        (sourceBinaryCoefficientRep R Q w).ρ (g • q).out
          (homogeneousMatrixAction w (Matrix.diagonal ![(p : R), 1])
            (c (sourceHeckeConjugation hp (cosetTransition (heckeUpperSubgroup Q p) g q)))) := rfl

end
end Dubon2026
