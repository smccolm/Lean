import Dubon2026.RationalOriginalCompletionInvariant
import Mathlib.Topology.Homeomorph.Lemmas

/-! The actual isomorphic rational completions have the same continuous
Galois group acting on the same prime-local closure. The literal field
automorphisms and original Krull topologies are retained. This transports
the actual Cartier cocycles needed for DUB-17's local relation family. -/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] UniformSpace.Completion.instSMul AlgebraicClosure.instSMulOfIsScalarTower
attribute [local instance] rationalOriginalCompletionTargetAlgebra rationalOriginalCompletionClosureAlgebra
  rationalOriginalCompletionClosureTower rationalOriginalCompletionGalois

variable (p : ℕ) (hp : p.Prime)

/-- The original closure automorphism retains its literal field map when
the isomorphic rational completion is used as its base. -/
def rationalOriginalCompletionGaloisEquiv :
    Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) ≃*
      Gal(rationalPrimeLocalClosure p hp / (rationalOriginalPrimePlace p hp).adicCompletion ℚ) where
  toFun g := g.restrictScalars ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
  invFun g := g.extendScalarsOfSurjective (rationalOriginalPrimeCompletionEquiv p hp).surjective
  left_inv g := by ext x; rfl
  right_inv g := by ext x; rfl
  map_mul' g h := by ext x; rfl

/-- The actual Galois base-change map is exactly the completion-base
equivalence, with no independent comparison hypothesis. -/
theorem rationalOriginalCompletionGaloisEquiv_baseChange
    (g : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp)) :
    galoisBaseChangeRestriction ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
      (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp) (rationalPrimeLocalClosure p hp) g =
      rationalOriginalCompletionGaloisEquiv p hp g := by
  apply AlgEquiv.ext
  intro x
  exact galoisBaseChangeRestriction_commutes ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp) (rationalPrimeLocalClosure p hp) g x

/-- The literal comparison is continuous for the original Krull topologies. -/
theorem rationalOriginalCompletionGaloisEquiv_continuous :
    Continuous (rationalOriginalCompletionGaloisEquiv p hp) := by
  have h := galoisBaseChangeRestriction_continuous ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp) (rationalPrimeLocalClosure p hp)
  have he : (galoisBaseChangeRestriction ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
      (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp) (rationalPrimeLocalClosure p hp) :
      Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) →
        Gal(rationalPrimeLocalClosure p hp / (rationalOriginalPrimePlace p hp).adicCompletion ℚ)) =
      rationalOriginalCompletionGaloisEquiv p hp :=
    funext (rationalOriginalCompletionGaloisEquiv_baseChange p hp)
  rwa [he] at h

/-- Compactness of the original Galois group proves continuity of the
inverse comparison; the infinite Galois topology is not made discrete. -/
theorem rationalOriginalCompletionGaloisEquiv_symm_continuous :
    Continuous (rationalOriginalCompletionGaloisEquiv p hp).symm :=
  Continuous.continuous_symm_of_equiv_compact_to_t2
    (f := (rationalOriginalCompletionGaloisEquiv p hp).toEquiv)
    (rationalOriginalCompletionGaloisEquiv_continuous p hp)

end
end Dubon2026
