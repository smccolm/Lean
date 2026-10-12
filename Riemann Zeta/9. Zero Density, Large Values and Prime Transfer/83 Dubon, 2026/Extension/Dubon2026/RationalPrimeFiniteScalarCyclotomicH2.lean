import Dubon2026.FiniteScalarCharacterH2TraceNormalization
import Dubon2026.RationalPrimeCyclotomicH2Scalar

/-! # The original arithmetic cyclotomic H2 over a finite coefficient field

The actual arithmetic character agrees with scalar extension of its prime-field
character. Transport the proved original H2 normalization through this equality,
retaining the precise coefficient object needed by DUB-17's matrix trace cup.
-/

namespace Dubon2026
noncomputable section

variable (p : ℕ) (hp : p.Prime) (q : ℕ) [Fact q.Prime]
  (k : Type) [Field k] [CharP k q] [Algebra (ZMod q) k]
  [TopologicalSpace k]

/-- The original arithmetic cyclotomic character is the actual scalar extension
of the original prime-field character, by uniqueness of the characteristic map. -/
theorem rationalPrimeCyclotomicCoefficientCharacter_scalarExtension :
    (algebraMap (ZMod q) k).toMonoidHom.comp
        (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom =
      (rationalPrimeCyclotomicCoefficientCharacter p hp q k).toMonoidHom := by
  apply MonoidHom.ext
  intro g
  change algebraMap (ZMod q) k
      (ZMod.castHom (dvd_refl q) (ZMod q)
        ((rationalPrimeCyclotomicCharacter p hp q g) : ZMod q)) =
    ZMod.castHom (dvd_refl q) k ((rationalPrimeCyclotomicCharacter p hp q g) : ZMod q)
  rw [ZMod.castHom_self]
  exact congrArg (fun f : ZMod q →+* k => f ((rationalPrimeCyclotomicCharacter p hp q g) : ZMod q))
    (Subsingleton.elim (algebraMap (ZMod q) k) (ZMod.castHom (dvd_refl q) k))

variable [Finite k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]

/-- The original finite-field cyclotomic H2 has its scalar coordinate obtained
by extending the constructed prime-field local invariant. -/
def rationalPrimeFiniteScalarCyclotomicH2Equiv :
    ContinuousRepresentationH2
      (coefficientCharacterRep
        (rationalPrimeCyclotomicCoefficientCharacter p hp q k).toMonoidHom)
      (coefficientCharacterAction_continuous
        (rationalPrimeCyclotomicCoefficientCharacter p hp q k).toMonoidHom
        (rationalPrimeCyclotomicCoefficientCharacter p hp q k).continuous) ≃ₗ[k] k := by
  let T := fun χ : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) →* k =>
    (hχ : Continuous χ) →
      ContinuousRepresentationH2 (coefficientCharacterRep χ)
        (coefficientCharacterAction_continuous χ hχ) ≃ₗ[k] k
  have hs : T ((algebraMap (ZMod q) k).toMonoidHom.comp
      (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom) := fun _ =>
    finiteScalarCharacterH2ScalarEquiv q
      (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom
      (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).continuous
      (rationalPrimeCyclotomicH2ScalarLinearEquiv p hp q)
  exact (Eq.mp (congrArg T
    (rationalPrimeCyclotomicCoefficientCharacter_scalarExtension p hp q k)) hs)
      (rationalPrimeCyclotomicCoefficientCharacter p hp q k).continuous

/-- Passing to the actual finite-field scalar invariant loses no original H2
information, as required when detecting the two trace-cup annihilators. -/
theorem rationalPrimeFiniteScalarCyclotomicH2Equiv_eq_zero_iff
    (x : ContinuousRepresentationH2
      (coefficientCharacterRep
        (rationalPrimeCyclotomicCoefficientCharacter p hp q k).toMonoidHom)
      (coefficientCharacterAction_continuous
        (rationalPrimeCyclotomicCoefficientCharacter p hp q k).toMonoidHom
        (rationalPrimeCyclotomicCoefficientCharacter p hp q k).continuous)) :
    rationalPrimeFiniteScalarCyclotomicH2Equiv p hp q k x = 0 ↔ x = 0 :=
  (rationalPrimeFiniteScalarCyclotomicH2Equiv p hp q k).map_eq_zero_iff

end
end Dubon2026
