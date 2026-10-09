import Dubon2026.PrimitiveInducedSphericalCoefficient
import Dubon2026.SphericalCoefficientQuotient
import Dubon2026.IntertwiningQuotientEquiv

/-! # The actual original smooth cusp local factor as a genuine induced cyclic quotient -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

/-- The original algebraic cyclic subspace of the genuine Fourier-root induced model. -/
abbrev PrimitiveLocalInducedCyclicSpace {N : ℕ} [NeZero N] {k : ℤ}
    (F : PrimitiveCuspForm N k) (p : ℕ) (hp : p.Prime) :=
  representationOrbitRange
    (normalizedLocalPrincipalRepresentation (rationalPrimePlace p hp)
      (primitiveSatakePlusUnit F p) (primitiveSatakeMinusUnit F p))
    (primitiveLocalInducedSpherical F p hp)

/-- The actual induced cyclic subspace inherits its original additive group. -/
instance primitiveLocalInducedCyclicAddCommGroup {N : ℕ} [NeZero N] {k : ℤ}
    (F : PrimitiveCuspForm N k) (p : ℕ) (hp : p.Prime) :
    AddCommGroup (PrimitiveLocalInducedCyclicSpace F p hp) :=
  Submodule.addCommGroup _

/-- The actual induced cyclic subspace inherits its original complex module. -/
instance primitiveLocalInducedCyclicModule {N : ℕ} [NeZero N] {k : ℤ}
    (F : PrimitiveCuspForm N k) (p : ℕ) (hp : p.Prime) :
    Module ℂ (PrimitiveLocalInducedCyclicSpace F p hp) :=
  Submodule.module _

/-- The actual group action on the literal spherical cyclic subspace of the original induced model. -/
def primitiveLocalInducedCyclicRepresentation {N : ℕ} [NeZero N] {k : ℤ}
    (F : PrimitiveCuspForm N k) (p : ℕ) (hp : p.Prime) :
    Representation ℂ (GeneralLinearGroup (Fin 2) ((rationalPrimePlace p hp).adicCompletion ℚ))
      (PrimitiveLocalInducedCyclicSpace F p hp) :=
  representationOrbitRepresentation
    (normalizedLocalPrincipalRepresentation (rationalPrimePlace p hp)
      (primitiveSatakePlusUnit F p) (primitiveSatakeMinusUnit F p))
    (primitiveLocalInducedSpherical F p hp)

private theorem primitive_smooth_inner {N : ℕ} [NeZero N] {k : ℤ}
    (F : PrimitiveCuspForm N k) (v : HeightOneSpectrum ℤ)
    (g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (x y : adelicLocalCyclicCore F.toCuspForm v) :
    inner ℂ (adelicLocalSmoothRepresentation F.toCuspForm v g x)
      (adelicLocalSmoothRepresentation F.toCuspForm v g y) = inner ℂ x y :=
  adelicCyclicLocalRepresentation_inner F.toCuspForm v g x.val y.val

/-- The genuine spherical coefficient relation map is an actual intertwiner from the original induced cyclic subrepresentation onto the original cusp smooth local representation. -/
def primitiveLocalInducedCyclicIntertwiner {N p : ℕ} [NeZero N] [NeZero p]
    [Fact p.Prime] {k : ℤ} (F : PrimitiveCuspForm N k) (hpN : p.Coprime N) :
    Representation.IntertwiningMap (primitiveLocalInducedCyclicRepresentation F p Fact.out)
      (adelicLocalSmoothRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) := by
  refine sphericalCoefficientIntertwiner
    (adelicLocalSmoothRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
    (normalizedLocalPrincipalRepresentation (rationalPrimePlace p (Fact.out : p.Prime))
      (primitiveSatakePlusUnit F p) (primitiveSatakeMinusUnit F p))
    (primitive_smooth_inner F _)
    (adelicLocalUnitReference F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
    (primitiveLocalInducedSpherical F p Fact.out) (primitiveLocalInducedAverage F p Fact.out)
    ?_
  intro g
  exact primitiveLocalInduced_smooth_coefficient F hpN g

/-- The constructed original cusp intertwiner sends every actual induced spherical translate to the matching original unit cusp translate. -/
theorem primitiveLocalInducedCyclicIntertwiner_orbit {N p : ℕ} [NeZero N] [NeZero p]
    [Fact p.Prime] {k : ℤ} (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    (g : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)) :
    primitiveLocalInducedCyclicIntertwiner F hpN
      ⟨normalizedLocalPrincipalRepresentation (rationalPrimePlace p (Fact.out : p.Prime))
        (primitiveSatakePlusUnit F p) (primitiveSatakeMinusUnit F p) g
        (primitiveLocalInducedSpherical F p Fact.out), representationOrbitRange_orbit_mem _ _ g⟩ =
      adelicLocalSmoothRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) g
        (adelicLocalUnitReference F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) :=
  sphericalCoefficientIntertwiner_orbit _ _ _ _ _ _ _ g

/-- Every vector of the original good-prime smooth cusp representation is the image of an actual finite induced spherical orbit combination. -/
theorem primitiveLocalInducedCyclicIntertwiner_surjective {N p : ℕ} [NeZero N] [NeZero p]
    [Fact p.Prime] {k : ℤ} (F : PrimitiveCuspForm N k) (hpN : p.Coprime N) :
    Function.Surjective (primitiveLocalInducedCyclicIntertwiner F hpN) :=
  sphericalCoefficientIntertwiner_surjective _ _ _ _ _ _ _
    (adelicLocalUnitOrbit_span F.toCuspForm (primitiveCuspForm_ne_zero F) _)

/-- The original smooth cusp local factor is an actual irreducible quotient of the genuine Fourier-root induced cyclic subrepresentation. Both the surjection and the target irreducibility are proved for the original objects. -/
theorem primitiveLocalInduced_irreducible_quotient {N p : ℕ} [NeZero N] [NeZero p]
    [Fact p.Prime] {k : ℤ} (F : PrimitiveCuspForm N k) (hpN : p.Coprime N) :
    Function.Surjective (primitiveLocalInducedCyclicIntertwiner F hpN) ∧
      (adelicLocalSmoothRepresentation F.toCuspForm
        (rationalPrimePlace p (Fact.out : p.Prime))).IsIrreducible :=
  ⟨primitiveLocalInducedCyclicIntertwiner_surjective F hpN,
    adelicLocalSmoothRepresentation_irreducible F hpN⟩

/-- The original smooth cusp factor is linearly equivalent to the literal quotient of the actual induced cyclic space by the proved intertwiner kernel. -/
def primitiveLocalInducedQuotientEquiv {N p : ℕ} [NeZero N] [NeZero p]
    [Fact p.Prime] {k : ℤ} (F : PrimitiveCuspForm N k) (hpN : p.Coprime N) :
    (PrimitiveLocalInducedCyclicSpace F p Fact.out ⧸
      (primitiveLocalInducedCyclicIntertwiner F hpN).toLinearMap.ker) ≃ₗ[ℂ]
        adelicLocalCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) :=
  LinearMap.quotKerEquivOfSurjective (primitiveLocalInducedCyclicIntertwiner F hpN).toLinearMap
    (primitiveLocalInducedCyclicIntertwiner_surjective F hpN)

/-- The genuine quotient action of the original Fourier-root induced cyclic representation by its proved cusp intertwiner kernel. -/
def primitiveLocalInducedQuotientRepresentation {N p : ℕ} [NeZero N] [NeZero p]
    [Fact p.Prime] {k : ℤ} (F : PrimitiveCuspForm N k) (hpN : p.Coprime N) :=
  intertwiningQuotientRepresentation _ _ (primitiveLocalInducedCyclicIntertwiner F hpN)

/-- The actual original smooth cusp local representation is equivalent, as a group representation, to the literal quotient of the genuine induced cyclic space by the constructed intertwiner kernel. -/
def primitiveLocalInducedRepresentationEquiv {N p : ℕ} [NeZero N] [NeZero p]
    [Fact p.Prime] {k : ℤ} (F : PrimitiveCuspForm N k) (hpN : p.Coprime N) :
    Representation.Equiv (primitiveLocalInducedQuotientRepresentation F hpN)
      (adelicLocalSmoothRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) :=
  intertwiningQuotientEquiv _ _ (primitiveLocalInducedCyclicIntertwiner F hpN)
    (primitiveLocalInducedCyclicIntertwiner_surjective F hpN)

/-- The actual induced quotient equivalence is equivariant on every original quotient vector. -/
theorem primitiveLocalInducedRepresentationEquiv_intertwines {N p : ℕ} [NeZero N] [NeZero p]
    [Fact p.Prime] {k : ℤ} (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    (g : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ))
    (x : PrimitiveLocalInducedCyclicSpace F p Fact.out ⧸
      (primitiveLocalInducedCyclicIntertwiner F hpN).toLinearMap.ker) :
    primitiveLocalInducedRepresentationEquiv F hpN (primitiveLocalInducedQuotientRepresentation F hpN g x) =
      adelicLocalSmoothRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) g
        (primitiveLocalInducedRepresentationEquiv F hpN x) :=
  intertwiningQuotientEquiv_intertwines _ _ (primitiveLocalInducedCyclicIntertwiner F hpN)
    (primitiveLocalInducedCyclicIntertwiner_surjective F hpN) g x

/-- At every original good prime, the actual cusp smooth local factor is a proved irreducible spherical subquotient of its own Fourier-root induced model: it is genuinely equivalent to the constructed cyclic kernel quotient. -/
theorem primitiveLocalInduced_spherical_constituent {N p : ℕ} [NeZero N] [NeZero p]
    [Fact p.Prime] {k : ℤ} (F : PrimitiveCuspForm N k) (hpN : p.Coprime N) :
    Nonempty (Representation.Equiv (primitiveLocalInducedQuotientRepresentation F hpN)
      (adelicLocalSmoothRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))) ∧
      (adelicLocalSmoothRepresentation F.toCuspForm
        (rationalPrimePlace p (Fact.out : p.Prime))).IsIrreducible :=
  ⟨⟨primitiveLocalInducedRepresentationEquiv F hpN⟩,
    adelicLocalSmoothRepresentation_irreducible F hpN⟩

end
end Dubon2026
