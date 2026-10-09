import Dubon2026.FinitePlaceInducedAverage
import Dubon2026.FinitePlaceFunctionalSpherical
import Dubon2026.PrimitiveLocalInducedHecke
import Dubon2026.AdelicLocalClosedHeckeEigen

/-! # The actual induced spherical coefficient equals the original cusp local coefficient -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

/-- Literal compact Haar averaging in the genuine local induced space of the original Fourier roots. -/
def primitiveLocalInducedAverage {N : ℕ} [NeZero N] {k : ℤ}
    (F : PrimitiveCuspForm N k) (p : ℕ) (hp : p.Prime) :
    NormalizedLocalPrincipalSeries (rationalPrimePlace p hp)
      (primitiveSatakePlusUnit F p) (primitiveSatakeMinusUnit F p) →ₗ[ℂ] ℂ :=
  finitePlaceInducedAverage (rationalPrimePlace p hp)
    (primitiveSatakePlusUnit F p * finitePlaceSqrtResidueUnit (rationalPrimePlace p hp))
    (primitiveSatakeMinusUnit F p * (finitePlaceSqrtResidueUnit (rationalPrimePlace p hp))⁻¹)

/-- The actual Fourier-root induced spherical section has original compact Haar average one. -/
theorem primitiveLocalInducedAverage_spherical {N : ℕ} [NeZero N] {k : ℤ}
    (F : PrimitiveCuspForm N k) (p : ℕ) (hp : p.Prime) :
    primitiveLocalInducedAverage F p hp (primitiveLocalInducedSpherical F p hp) = 1 :=
  finitePlaceInducedAverage_spherical _ _ _

/-- The genuine Fourier-root induced compact average is invariant under the original local integral action. -/
theorem primitiveLocalInducedAverage_invariant {N : ℕ} [NeZero N] {k : ℤ}
    (F : PrimitiveCuspForm N k) (p : ℕ) (hp : p.Prime)
    (a : finitePlaceGL2Gamma0 1 (rationalPrimePlace p hp))
    (f : NormalizedLocalPrincipalSeries (rationalPrimePlace p hp)
      (primitiveSatakePlusUnit F p) (primitiveSatakeMinusUnit F p)) :
    primitiveLocalInducedAverage F p hp
      (normalizedLocalPrincipalRepresentation (rationalPrimePlace p hp)
        (primitiveSatakePlusUnit F p) (primitiveSatakeMinusUnit F p) a.val f) =
      primitiveLocalInducedAverage F p hp f :=
  finitePlaceInducedAverage_invariant _ _ _ a f

private theorem primitive_induced_cartan {N p : ℕ} [NeZero N] [NeZero p]
    [Fact p.Prime] {k : ℤ} (F : PrimitiveCuspForm N k)
    (u : ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)ˣ) (n : ℕ)
    (l r : finitePlaceGL2Gamma0 1 (rationalPrimePlace p (Fact.out : p.Prime))) :
    primitiveLocalInducedAverage F p Fact.out
      (normalizedLocalPrincipalRepresentation (rationalPrimePlace p (Fact.out : p.Prime))
        (primitiveSatakePlusUnit F p) (primitiveSatakeMinusUnit F p)
        (GeneralLinearGroup.scalar (Fin 2) u * l.val *
          (GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p (Fact.out : p.Prime)))
            (finiteAdelicHeckeDiagonal p)) ^ n * r.val)
        (primitiveLocalInducedSpherical F p Fact.out)) =
      sphericalChebyshevCoefficient p (Real.sqrt p) (normalizedCuspCoefficients F.toCuspForm p) n := by
  exact finitePlaceFunctional_spherical_cartan p
    (normalizedLocalPrincipalRepresentation _ (primitiveSatakePlusUnit F p) (primitiveSatakeMinusUnit F p))
    (primitiveLocalInducedAverage F p Fact.out) (primitiveLocalInducedSpherical F p Fact.out)
    (primitiveLocalInducedAverage_invariant F p Fact.out)
    (finitePlaceInducedSpherical_fixed _ _ _)
    (normalizedLocalPrincipalRepresentation_scalar _ _ _ (primitiveSatakeUnits_product F p))
    (primitiveLocalInducedAverage_spherical F p Fact.out) _ (primitiveLocalInducedSpherical_hecke F p)
    u n l r

private def primitiveClosedSphericalFunctional {N : ℕ} [NeZero N] {k : ℤ}
    (F : PrimitiveCuspForm N k) (p : ℕ) [NeZero p] [Fact p.Prime] :
    adelicLocalCyclicClosedSpan F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) →ₗ[ℂ] ℂ :=
  { toFun := fun x => inner ℂ (adelicCyclicUnitReference F.toCuspForm) x.val
    map_add' := fun x y => inner_add_right (𝕜 := ℂ) _ x.val y.val
    map_smul' := fun c x => inner_smul_right _ x.val c }

private theorem primitive_closed_functional_invariant {N p : ℕ} [NeZero N] [NeZero p]
    [Fact p.Prime] {k : ℤ} (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    (a : finitePlaceGL2Gamma0 1 (rationalPrimePlace p (Fact.out : p.Prime)))
    (x : adelicLocalCyclicClosedSpan F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) :
    primitiveClosedSphericalFunctional F p
      (adelicLocalCyclicRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) a.val x) =
        primitiveClosedSphericalFunctional F p x := by
  have he := adelicLocalCyclicRepresentation_inner F.toCuspForm _ a.val
    (adelicLocalClosedUnitReference F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) x
  rw [adelicLocalClosedUnitReference_good_fixed F hpN a] at he
  exact he

private theorem primitive_closed_cartan {N p : ℕ} [NeZero N] [NeZero p]
    [Fact p.Prime] {k : ℤ} (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    (u : ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)ˣ) (n : ℕ)
    (l r : finitePlaceGL2Gamma0 1 (rationalPrimePlace p (Fact.out : p.Prime))) :
    inner ℂ (adelicLocalClosedUnitReference F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
      (adelicLocalCyclicRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))
        (GeneralLinearGroup.scalar (Fin 2) u * l.val *
          (GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p (Fact.out : p.Prime)))
            (finiteAdelicHeckeDiagonal p)) ^ n * r.val)
        (adelicLocalClosedUnitReference F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))) =
      sphericalChebyshevCoefficient p (Real.sqrt p) (normalizedCuspCoefficients F.toCuspForm p) n := by
  change primitiveClosedSphericalFunctional F p
    (adelicLocalCyclicRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))
      (GeneralLinearGroup.scalar (Fin 2) u * l.val *
        (GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p (Fact.out : p.Prime)))
          (finiteAdelicHeckeDiagonal p)) ^ n * r.val)
      (adelicLocalClosedUnitReference F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))) = _
  refine finitePlaceFunctional_spherical_cartan p
    (adelicLocalCyclicRepresentation F.toCuspForm _) (primitiveClosedSphericalFunctional F p)
    (adelicLocalClosedUnitReference F.toCuspForm _) ?_ ?_ ?_ ?_
    (normalizedCuspCoefficients F.toCuspForm p) ?_ u n l r
  · exact primitive_closed_functional_invariant F hpN
  · exact adelicLocalClosedUnitReference_good_fixed F hpN
  · exact adelicLocalCyclicRepresentation_scalar F.toCuspForm _
  · exact adelicLocalClosedUnitReference_inner F.toCuspForm (primitiveCuspForm_ne_zero F) _
  · exact adelicLocalClosedUnitReference_hecke_eigen F hpN


/-- At each genuine good prime, the compact average of the actual induced spherical translates equals the original unit cusp local matrix coefficient at every original group element. -/
theorem primitiveLocalInduced_spherical_coefficient {N p : ℕ} [NeZero N] [NeZero p]
    [Fact p.Prime] {k : ℤ} (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    (g : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)) :
    primitiveLocalInducedAverage F p Fact.out
      (normalizedLocalPrincipalRepresentation (rationalPrimePlace p (Fact.out : p.Prime))
        (primitiveSatakePlusUnit F p) (primitiveSatakeMinusUnit F p) g
        (primitiveLocalInducedSpherical F p Fact.out)) =
    inner ℂ (adelicLocalClosedUnitReference F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
      (adelicLocalCyclicRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) g
        (adelicLocalClosedUnitReference F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))) := by
  obtain ⟨u, n, l, r, hg⟩ := finitePlaceGL2_cartan p (Fact.out : p.Prime) g
  rw [hg]
  exact (primitive_induced_cartan F u n l r).trans (primitive_closed_cartan F hpN u n l r).symm

/-- The same genuine induced coefficient is exactly the coefficient of the original irreducible smooth local algebraic core, with its original unit reference. -/
theorem primitiveLocalInduced_smooth_coefficient {N p : ℕ} [NeZero N] [NeZero p]
    [Fact p.Prime] {k : ℤ} (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    (g : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)) :
    primitiveLocalInducedAverage F p Fact.out
      (normalizedLocalPrincipalRepresentation (rationalPrimePlace p (Fact.out : p.Prime))
        (primitiveSatakePlusUnit F p) (primitiveSatakeMinusUnit F p) g
        (primitiveLocalInducedSpherical F p Fact.out)) =
    inner ℂ (adelicLocalUnitReference F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
      (adelicLocalSmoothRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) g
        (adelicLocalUnitReference F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))) :=
  primitiveLocalInduced_spherical_coefficient F hpN g

end
end Dubon2026
