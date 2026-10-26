import Dubon2026.SourceGammaOneCoverHeckeTraceCosets
import Dubon2026.SourceGammaOneCoverFiniteIndex
import Dubon2026.SourceH1TraceBaseChange

/-! DUB-17/18 -> original all-weight adic association -> geometric Gamma1
realization -> actual surjective-transfer Hecke compatibility. Apply the
proved native H1 base-change theorem to the original Hecke homomorphism
and actual Gamma1 image; its coset hypothesis is now discharged. -/
namespace Dubon2026
noncomputable section
open CategoryTheory CongruenceSubgroup

private instance coverCosetsFintype (Q N : ℕ) [NeZero Q] [NeZero N] :
    Fintype (Gamma0 Q ⧸ (sourceGammaOneDiagonalHom Q N).range) := by
  letI := sourceGammaOneDiagonalHom_range_finiteIndex Q N
  exact Fintype.ofFinite _

private instance coverPullbackCosetsFintype (Q N ell : ℕ)
    [NeZero Q] [NeZero N] [NeZero ell] (hell : ell.Prime) :
    Fintype (heckeUpperSubgroup Q ell ⧸
      (sourceGammaOneDiagonalHom Q N).range.comap (sourceHeckeConjugation hell)) := by
  exact Fintype.ofInjective
    (subgroupComapCosetMap (sourceHeckeConjugation hell) (sourceGammaOneDiagonalHom Q N).range)
    (subgroupComapCosetMap_injective (sourceHeckeConjugation hell)
      (sourceGammaOneDiagonalHom Q N).range)

/-- The literal native H1 trace for the actual Gamma1 cover satisfies the
original good-prime Hecke pullback square. No coset-surjectivity premise
or cohomological comparison is left to the caller. -/
theorem sourceGammaOneCoverHeckeH1Trace_pullback
    {R : Type} [CommRing R] (Q N ell : ℕ)
    [NeZero Q] [NeZero N] [NeZero ell] (hell : ell.Prime)
    (hcop : Nat.Coprime ell (Q * N)) (A : Rep.{0} R (Gamma0 Q)) :
    (groupCohomology.map (sourceHeckeConjugation hell)
      (𝟙 (Rep.res (sourceHeckeConjugation hell) A)) 1).hom.comp
        (sourceHeckeH1Trace A (sourceGammaOneDiagonalHom Q N).range) =
      (sourceHeckeH1Trace (Rep.res (sourceHeckeConjugation hell) A)
        ((sourceGammaOneDiagonalHom Q N).range.comap (sourceHeckeConjugation hell))).comp
          (groupCohomology.map
            (sourceTracePullbackSubgroupHom (sourceHeckeConjugation hell)
              (sourceGammaOneDiagonalHom Q N).range)
            (𝟙 (Rep.res
              ((sourceGammaOneDiagonalHom Q N).range.comap (sourceHeckeConjugation hell)).subtype
              (Rep.res (sourceHeckeConjugation hell) A))) 1).hom :=
  sourceHeckeH1Trace_pullback A (sourceHeckeConjugation hell)
    (sourceGammaOneDiagonalHom Q N).range
    (sourceGammaOneCoverHeckeTraceCoset_surjective Q N ell hell hcop)

end
end Dubon2026
