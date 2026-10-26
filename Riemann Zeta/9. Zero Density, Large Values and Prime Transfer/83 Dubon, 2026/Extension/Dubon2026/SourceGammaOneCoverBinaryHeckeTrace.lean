import Dubon2026.SourceH1TraceBaseChangeCoefficient
import Dubon2026.SourceGammaOneCoverHeckeTraceBaseChange
import Dubon2026.SourceBinaryHeckeCohomology

/-! DUB-17/18 -> original all-weight adic association -> geometric Gamma1
realization -> actual surjective-transfer Hecke compatibility. Keep the
original binary Hecke coefficient morphism and actual upper-subgroup trace
while applying the proved Gamma1 coset base change. -/
namespace Dubon2026
noncomputable section
open CategoryTheory CongruenceSubgroup

private local instance upperCosetsFintype (Q ell : ℕ) [NeZero ell] :
    Fintype (Gamma0 Q ⧸ heckeUpperSubgroup Q ell) :=
  sourceHeckeUpperFintype Q ell

variable (R : Type) [CommRing R] (Q N ell : ℕ)
  [NeZero Q] [NeZero N] [NeZero ell] (hell : ell.Prime) (w : ℕ)

/-- The actual binary Hecke coefficient morphism satisfies the native
Gamma1-image trace square with all coset hypotheses discharged. -/
theorem sourceGammaOneCoverBinaryHeckeTrace_pullback
    (hcop : Nat.Coprime ell (Q * N)) :
    subgroupCohomologyTrace (sourceBinaryCoefficientRep R Q w)
        (sourceGammaOneDiagonalHom Q N).range 1 ≫
      groupCohomology.map (sourceHeckeConjugation hell) (sourceBinaryHeckeMorphism R hell w) 1 =
    groupCohomology.map
      (sourceTracePullbackSubgroupHom (sourceHeckeConjugation hell)
        (sourceGammaOneDiagonalHom Q N).range)
      ((Rep.resFunctor
        ((sourceGammaOneDiagonalHom Q N).range.comap (sourceHeckeConjugation hell)).subtype).map
          (sourceBinaryHeckeMorphism R hell w)) 1 ≫
      subgroupCohomologyTrace
        (Rep.res (heckeUpperSubgroup Q ell).subtype (sourceBinaryCoefficientRep R Q w))
        ((sourceGammaOneDiagonalHom Q N).range.comap (sourceHeckeConjugation hell)) 1 :=
  sourceSubgroupH1Trace_pullback_coefficient (sourceBinaryCoefficientRep R Q w)
    (sourceHeckeConjugation hell) (sourceGammaOneDiagonalHom Q N).range
    (Rep.res (heckeUpperSubgroup Q ell).subtype (sourceBinaryCoefficientRep R Q w))
    (sourceBinaryHeckeMorphism R hell w)
    (sourceGammaOneCoverHeckeTraceCoset_surjective Q N ell hell hcop)

/-- The original full binary H1 Hecke operator after the literal cover
trace is precisely the iterated native trace with the original coefficient
map. This supplies one side of the required surjective-transfer identity. -/
theorem sourceGammaOneCoverBinaryHeckeTrace_iterated
    (hcop : Nat.Coprime ell (Q * N)) :
    (sourceBinaryHeckeH1 R hell w).comp
      (sourceHeckeH1Trace (sourceBinaryCoefficientRep R Q w)
        (sourceGammaOneDiagonalHom Q N).range) =
    (sourceHeckeH1Trace (sourceBinaryCoefficientRep R Q w) (heckeUpperSubgroup Q ell)).comp
      ((sourceHeckeH1Trace
        (Rep.res (heckeUpperSubgroup Q ell).subtype (sourceBinaryCoefficientRep R Q w))
        ((sourceGammaOneDiagonalHom Q N).range.comap (sourceHeckeConjugation hell))).comp
        (groupCohomology.map
          (sourceTracePullbackSubgroupHom (sourceHeckeConjugation hell)
            (sourceGammaOneDiagonalHom Q N).range)
          ((Rep.resFunctor
            ((sourceGammaOneDiagonalHom Q N).range.comap (sourceHeckeConjugation hell)).subtype).map
              (sourceBinaryHeckeMorphism R hell w)) 1).hom) := by
  have he :
      (groupCohomology.map (sourceHeckeConjugation hell)
        (sourceBinaryHeckeMorphism R hell w) 1).hom.comp
        (sourceHeckeH1Trace (sourceBinaryCoefficientRep R Q w)
          (sourceGammaOneDiagonalHom Q N).range) =
      (sourceHeckeH1Trace
        (Rep.res (heckeUpperSubgroup Q ell).subtype (sourceBinaryCoefficientRep R Q w))
        ((sourceGammaOneDiagonalHom Q N).range.comap (sourceHeckeConjugation hell))).comp
        (groupCohomology.map
          (sourceTracePullbackSubgroupHom (sourceHeckeConjugation hell)
            (sourceGammaOneDiagonalHom Q N).range)
          ((Rep.resFunctor
            ((sourceGammaOneDiagonalHom Q N).range.comap (sourceHeckeConjugation hell)).subtype).map
              (sourceBinaryHeckeMorphism R hell w)) 1).hom := by
    rw [sourceHeckeH1Trace_eq_subgroupTrace, sourceHeckeH1Trace_eq_subgroupTrace]
    exact congrArg ModuleCat.Hom.hom
      (sourceGammaOneCoverBinaryHeckeTrace_pullback R Q N ell hell w hcop)
  unfold sourceBinaryHeckeH1
  rw [LinearMap.comp_assoc, he]

end
end Dubon2026
