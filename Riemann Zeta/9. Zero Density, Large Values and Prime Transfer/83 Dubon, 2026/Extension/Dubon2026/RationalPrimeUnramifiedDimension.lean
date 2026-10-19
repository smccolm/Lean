import Dubon2026.AlgebraicLocalUnramifiedDimension
import Dubon2026.LocalFieldOriginalNorm
import Dubon2026.RationalPrimeRootH2Invariant

/-! Unramified cohomology on the same rational-prime completion and
algebraic closure used by the original arithmetic restriction. The
compatible norm preserves the completion's original uniform space and
valuation relation. This supplies DUB-17's local dimension input, before
the remaining comparison with its arithmetic deformation conditions. -/

namespace Dubon2026
noncomputable section

attribute [local instance] rationalPrimeLocalField_charZero

/-- A compatible norm on the original rational-prime completion. -/
@[implicit_reducible]
def rationalPrimeOriginalNorm (p : ℕ) (hp : p.Prime) :
    NontriviallyNormedField (rationalPrimeLocalField p hp) :=
  localFieldOriginalNorm (rationalPrimeLocalField p hp)

attribute [local instance] rationalPrimeOriginalNorm

/-- The normed-field projection uses the same compatible original norm. -/
@[implicit_reducible]
def rationalPrimeOriginalNormedField (p : ℕ) (hp : p.Prime) :
    NormedField (rationalPrimeLocalField p hp) :=
  (rationalPrimeOriginalNorm p hp).toNormedField

attribute [local instance 1100] rationalPrimeOriginalNormedField

/-- The compatible norm is ultrametric on the same original completion. -/
theorem rationalPrimeOriginalNorm_ultrametric (p : ℕ) (hp : p.Prime) :
    IsUltrametricDist (rationalPrimeLocalField p hp) :=
  localFieldOriginalNorm_isUltrametric (rationalPrimeLocalField p hp)

attribute [local instance] rationalPrimeOriginalNorm_ultrametric

/-- The spectral norm extends the original local norm to its original closure. -/
@[implicit_reducible]
def rationalPrimeOriginalClosureNorm (p : ℕ) (hp : p.Prime) :
    NormedField (rationalPrimeLocalClosure p hp) :=
  spectralNorm.normedField (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)

attribute [local instance] rationalPrimeOriginalClosureNorm

/-- The original closure embedding respects these compatible norms. -/
@[implicit_reducible]
def rationalPrimeOriginalClosureNormedAlgebra (p : ℕ) (hp : p.Prime) :
    NormedAlgebra (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp) :=
  spectralNorm.normedAlgebra (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)

attribute [local instance] rationalPrimeOriginalClosureNormedAlgebra

/-- The actual original closure has the extended nonarchimedean norm. -/
theorem rationalPrimeOriginalClosureNorm_ultrametric (p : ℕ) (hp : p.Prime) :
    IsUltrametricDist (rationalPrimeLocalClosure p hp) :=
  IsUltrametricDist.of_normedAlgebra (rationalPrimeLocalField p hp)

attribute [local instance] rationalPrimeOriginalClosureNorm_ultrametric

/-- The residue-action inertia subgroup in the original prime-local closure. -/
def rationalPrimeNormInertia (p : ℕ) (hp : p.Prime) :
    Subgroup Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) :=
  algebraicLocalInertia (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)

/-- The actual original prime-local inertia is normal. -/
instance rationalPrimeNormInertia_normal (p : ℕ) (hp : p.Prime) :
    (rationalPrimeNormInertia p hp).Normal :=
  algebraicLocalInertia_normal (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp)

/-- At the original rational prime, the continuous unramified H1 dimension
equals the dimension of invariants of the same finite representation.
Residue Frobenius, cyclicity, depth and H1 finiteness are all derived. -/
theorem rationalPrime_unramified_finrank_eq_invariants
    (p : ℕ) (hp : p.Prime) (q : ℕ) [Fact q.Prime]
    (A : Rep (ZMod q) Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp))
    [FiniteDimensional (ZMod q) A] [TopologicalSpace A] [DiscreteTopology A]
    [ContinuousSMul (ZMod q) A]
    (hA : Continuous (fun z : Gal(rationalPrimeLocalClosure p hp /
      rationalPrimeLocalField p hp) × A => A.ρ z.1 z.2)) :
    Module.finrank (ZMod q) (continuousRepresentationH1Restriction A hA
      (rationalPrimeNormInertia p hp).subtype continuous_subtype_val).ker =
      Module.finrank (ZMod q) A.ρ.invariants := by
  exact algebraicLocal_unramified_finrank_eq_invariants
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp) q A hA

end
end Dubon2026
