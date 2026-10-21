import Dubon2026.SourceHeckeCohomologyTrace
import Dubon2026.SourceHeckeCoefficientMorphism

/-! The actual prime Hecke correspondence on the full native H1.
DUB-17/18 -> residual modular Galois association -> original H1 Hecke
eigensystem. Restriction along the proved diagonal conjugation, the actual
adjugate coefficient morphism, and the existing finite coset trace define
the operator. No operator or quotient-descent hypothesis is supplied.
SourcePeriodHeckeCohomology proves compatibility with the original analytic
Hecke action, and SourcePrimitiveHeckeCohomology supplies its primitive consumer.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup CategoryTheory

variable {p Q : ℕ} [NeZero p] (hp : Nat.Prime p) (w : ℕ)

private local instance sourceHeckeCohomologyFintype :
    Fintype (Gamma0 Q ⧸ heckeUpperSubgroup Q p) :=
  sourceHeckeUpperFintype Q p

/-- The actual prime correspondence on original cocycles, using all the genuine cosets. -/
def sourceHeckeCocycle :
    groupCohomology.cocycles₁ (sourcePeriodDualRep (Gamma0 Q) w) →ₗ[ℂ]
      groupCohomology.cocycles₁ (sourcePeriodDualRep (Gamma0 Q) w) :=
  (sourceHeckeTraceCocycles (sourcePeriodDualRep (Gamma0 Q) w)
      (heckeUpperSubgroup Q p)).comp
    (groupCohomology.mapCocycles₁ (sourceHeckeConjugation hp)
      (sourceHeckeDualMorphism hp w)).hom

/-- The actual prime Hecke correspondence is an endomorphism of the full native H1. -/
def sourceHeckeH1 :
    Module.End ℂ (groupCohomology.H1 (sourcePeriodDualRep (Gamma0 Q) w)) :=
  (sourceHeckeH1Trace (sourcePeriodDualRep (Gamma0 Q) w)
      (heckeUpperSubgroup Q p)).comp
    (groupCohomology.map (sourceHeckeConjugation hp) (sourceHeckeDualMorphism hp w) 1).hom

/-- The full H1 operator is represented by its original restriction-conjugation-trace sum. -/
theorem sourceHeckeH1_cocycle
    (c : groupCohomology.cocycles₁ (sourcePeriodDualRep (Gamma0 Q) w)) :
    sourceHeckeH1 hp w (groupCohomology.H1π (sourcePeriodDualRep (Gamma0 Q) w) c) =
      groupCohomology.H1π (sourcePeriodDualRep (Gamma0 Q) w) (sourceHeckeCocycle hp w c) := by
  change sourceHeckeH1Trace _ _
    ((groupCohomology.map (sourceHeckeConjugation hp) (sourceHeckeDualMorphism hp w) 1)
      (groupCohomology.H1π _ c)) = _
  rw [groupCohomology.H1π_comp_map_apply, sourceHeckeH1Trace_cocycle]
  rfl

/-- The operator uses exactly the original finite coset formula on every cocycle. -/
theorem sourceHeckeCocycle_apply
    (c : groupCohomology.cocycles₁ (sourcePeriodDualRep (Gamma0 Q) w))
    (γ : Gamma0 Q) :
    sourceHeckeCocycle hp w c γ =
      ∑ q : Gamma0 Q ⧸ heckeUpperSubgroup Q p,
        (sourcePeriodDualRep (Gamma0 Q) w).ρ (γ • q).out
          (sourceHeckeDualDiagonal w p
            (c (sourceHeckeConjugation hp (cosetTransition (heckeUpperSubgroup Q p) γ q)))) := rfl

end
end Dubon2026
