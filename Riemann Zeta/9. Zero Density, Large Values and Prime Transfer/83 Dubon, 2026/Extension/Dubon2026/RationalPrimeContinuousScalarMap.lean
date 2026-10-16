import Dubon2026.OriginalLocalScalarContinuity
import Dubon2026.RationalPrimeRootH2Invariant
import Dubon2026.LocalFieldOriginalNorm

/-! # Continuous original field maps commute with the actual prime-completion base

Density of the original rational field determines the map on its actual
completion. This lets the transported original prime-stabilizer action
become a genuine prime-base automorphism, the needed local/global
decomposition comparison on DUB-17's prime-indexing route.
-/
namespace Dubon2026
noncomputable section
open UniformSpace

/-- A continuous original ring homomorphism between compatible local extensions preserves the entire original rational-prime base. -/
theorem rationalPrimeLocal_continuousRingHom_commutes
    (p : ℕ) (hp : p.Prime) (E M : Type) [Field E] [Field M]
    [Algebra (rationalPrimeLocalField p hp) E] [Algebra (rationalPrimeLocalField p hp) M]
    [ValuativeRel E] [ValuativeRel M] [TopologicalSpace E] [TopologicalSpace M]
    [IsNonarchimedeanLocalField E] [IsNonarchimedeanLocalField M]
    [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension (ValuativeRel.valuation E)]
    [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension (ValuativeRel.valuation M)]
    (f : E →+* M) (hf : Continuous f) (x : rationalPrimeLocalField p hp) :
    f (algebraMap (rationalPrimeLocalField p hp) E x) = algebraMap (rationalPrimeLocalField p hp) M x := by
  letI := IsTopologicalAddGroup.rightUniformSpace M
  haveI := isUniformAddGroup_of_addCommGroup (G := M)
  letI : NontriviallyNormedField M := localFieldOriginalNorm M
  refine Completion.induction_on (p := fun x : rationalPrimeLocalField p hp =>
    f (algebraMap (rationalPrimeLocalField p hp) E x) = algebraMap (rationalPrimeLocalField p hp) M x) x ?_ ?_
  · exact isClosed_eq (hf.comp (originalLocalScalar_continuous (rationalPrimeLocalField p hp) E))
      (originalLocalScalar_continuous (rationalPrimeLocalField p hp) M)
  · intro q
    change f (algebraMap (rationalPrimeLocalField p hp) E
      (algebraMap ℚ (rationalPrimeLocalField p hp) q.ofVal)) =
      algebraMap (rationalPrimeLocalField p hp) M
        (algebraMap ℚ (rationalPrimeLocalField p hp) q.ofVal)
    simp only [eq_ratCast, map_ratCast]

end
end Dubon2026
