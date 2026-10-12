import Dubon2026.LocalFieldRootH2Invariant
import Dubon2026.RationalPrimeArithmeticRestriction
import Mathlib.NumberTheory.Padics.ProperSpace

/-! # The finite local cohomology target at the original rational prime

This applies the invariant to the same actual completion and algebraic closure
used by the arithmetic restriction and trace cup, discharging the local-field
structure through the pinned p-adic equivalence.
-/

namespace Dubon2026
noncomputable section
open scoped WithZero

/-- The valuation relation is induced by the original adic valuation. -/
instance rationalPrimeLocalFieldValuativeRel (p : ℕ) (hp : p.Prime) :
    ValuativeRel (rationalPrimeLocalField p hp) :=
  ValuativeRel.ofValuation (Valued.v (R := rationalPrimeLocalField p hp) (Γ₀ := ℤᵐ⁰))

/-- The same original adic valuation represents the chosen valuation relation. -/
instance rationalPrimeLocalField_valuationCompatible (p : ℕ) (hp : p.Prime) :
    (Valued.v (R := rationalPrimeLocalField p hp) (Γ₀ := ℤᵐ⁰)).Compatible :=
  Valuation.Compatible.ofValuation _

/-- The original completion topology agrees with its original adic valuation. -/
instance rationalPrimeLocalField_isValuativeTopology (p : ℕ) (hp : p.Prime) :
    IsValuativeTopology (rationalPrimeLocalField p hp) := by
  apply IsValuativeTopology.of_zero
  intro s
  rw [Valued.mem_nhds_zero (Γ₀ := ℤᵐ⁰)]
  simpa only [sub_zero] using
    (Valuation.exists_setOf_restrict_le_iff
      (Valued.v (R := rationalPrimeLocalField p hp) (Γ₀ := ℤᵐ⁰)) 0 s)

/-- The original rational prime completion is a nonarchimedean local field.
Local compactness is transported through its actual p-adic homeomorphism. -/
instance rationalPrimeLocalField_isNonarchimedean (p : ℕ) (hp : p.Prime) :
    IsNonarchimedeanLocalField (rationalPrimeLocalField p hp) := by
  let v := rationalPrimePlace p hp
  letI : Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).property⟩
  haveI : LocallyCompactSpace (rationalPrimeLocalField p hp) :=
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toHomeomorph.locallyCompactSpace_iff.mpr
      inferInstance
  haveI : ValuativeRel.IsNontrivial (rationalPrimeLocalField p hp) :=
    (ValuativeRel.isNontrivial_iff_isNontrivial
      (Valued.v (R := rationalPrimeLocalField p hp) (Γ₀ := ℤᵐ⁰))).mpr inferInstance
  constructor

/-- The original rational embedding makes its prime completion characteristic zero. -/
theorem rationalPrimeLocalField_charZero (p : ℕ) (hp : p.Prime) :
    CharZero (rationalPrimeLocalField p hp) :=
  Algebra.charZero_of_charZero (R := ℚ) (A := rationalPrimeLocalField p hp)

attribute [local instance] rationalPrimeLocalField_charZero

/-- The original algebraic closure is Galois over the actual prime completion.
Its characteristic-zero structure is used locally to avoid changing rational embeddings. -/
instance rationalPrimeLocalClosureIsGalois (p : ℕ) (hp : p.Prime) :
    IsGalois (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp) :=
  inferInstance

variable (p : ℕ) (hp : p.Prime) (n : ℕ) [NeZero n]
  [TopologicalSpace (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) n)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]

/-- The actual prime-local root H2 has a cyclic coordinate given by its
original Kummer inclusion and arithmetic local invariant. -/
def rationalPrimeRootH2CyclicEquiv :
    GaloisRootContinuousH2 (K := rationalPrimeLocalField p hp)
      (Ω := rationalPrimeLocalClosure p hp) n ≃ₗ[ℤ] ZMod n :=
  localFieldRootH2CyclicEquiv (rationalPrimeLocalField p hp)
    (rationalPrimeLocalClosure p hp) n

/-- The finite scalar coordinate agrees with the full invariant of the same
original root inclusion at the actual rational prime. -/
theorem rationalPrimeRootH2CyclicEquiv_invariant
    (x : GaloisRootContinuousH2 (K := rationalPrimeLocalField p hp)
      (Ω := rationalPrimeLocalClosure p hp) n) :
    rationalCyclicInvariant n (rationalPrimeRootH2CyclicEquiv p hp n x) =
      localFieldContinuousH2InvariantEquiv (rationalPrimeLocalField p hp)
        (rationalPrimeLocalClosure p hp)
        (galoisKummerH2Inclusion (K := rationalPrimeLocalField p hp)
          (Ω := rationalPrimeLocalClosure p hp) n x) :=
  localFieldRootH2CyclicEquiv_invariant (rationalPrimeLocalField p hp)
    (rationalPrimeLocalClosure p hp) n x

/-- The original prime-local root H2 has exactly n elements; its finiteness
is derived rather than supplied as an arithmetic hypothesis. -/
theorem rationalPrimeRootH2_card :
    Nat.card (GaloisRootContinuousH2 (K := rationalPrimeLocalField p hp)
      (Ω := rationalPrimeLocalClosure p hp) n) = n :=
  localFieldRootH2_card (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp) n

end
end Dubon2026
