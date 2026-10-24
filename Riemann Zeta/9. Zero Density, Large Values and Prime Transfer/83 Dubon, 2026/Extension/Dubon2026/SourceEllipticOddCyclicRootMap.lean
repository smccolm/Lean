import Dubon2026.SourceEllipticOddPrimeGeneratorInvariant

/-! The actual map from prime cyclic subgroups to modular-polynomial roots.
It is surjective, and its value agrees with the literal quotient attached to
every generator. Generator independence is proved by cancellation of the
complete products, including positive residue characteristic. Injectivity at
the required non-CM fibers and inertia equivariance remain separate obligations. -/

namespace Dubon2026.SourceFunctionField.IntegralJCoordinate
open Polynomial WeierstrassCurve SourceEllipticVelu.OddDiscriminant
noncomputable section
variable {K : Type*} [Field K] [DecidableEq K]
variable (W : WeierstrassCurve K) (p : ℕ)

/-- An actual generator of a specified cyclic subgroup of the original elliptic point group. -/
def primeKernelGenerator
    (H : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = p}) :
    W.toAffine.Point :=
  Classical.choose ((AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq_top H.1).mp H.2.1)

/-- The chosen generator generates the specified subgroup exactly. -/
theorem primeKernelGenerator_zmultiples
    (H : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = p}) :
    AddSubgroup.zmultiples (primeKernelGenerator W p H) = H.1 :=
  Classical.choose_spec ((AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq_top H.1).mp H.2.1)

/-- The original subgroup cardinality is the exact order of its chosen generator. -/
theorem primeKernelGenerator_order
    (H : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = p}) :
    addOrderOf (primeKernelGenerator W p H) = p := by
  rw [← Nat.card_zmultiples, primeKernelGenerator_zmultiples]
  exact H.2.2

variable [Fact p.Prime]

/-- The exact odd-order formula for the actual prime-kernel generator. -/
theorem primeKernelGenerator_oddOrder (hp2 : p ≠ 2)
    (H : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = p}) :
    addOrderOf (primeKernelGenerator W p H) = 2 * (p / 2) + 1 := by
  rw [primeKernelGenerator_order]
  obtain ⟨m, hm⟩ := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left hp2
  omega

variable [W.IsElliptic] [IsAlgClosed K]

/-- The actual cyclic-subgroup-to-root map, using the literal quotient j-value. -/
def oddPrimeCyclicRootMap (hp2 : p ≠ 2) (hp : (p : K) ≠ 0) :
    {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = p} →
      {x : K // (relationAtSeed (modularPolynomial p) W.j).IsRoot x} := fun H =>
  ⟨oddQuotientJ W (primeKernelGenerator_oddOrder W p hp2 H),
    modularPolynomial_isRoot_oddQuotientJ W p hp2 hp _
      (primeKernelGenerator_oddOrder W p hp2 H)⟩

/-- The root map has the actual quotient value for every generator of the original subgroup. -/
theorem oddPrimeCyclicRootMap_eq_quotient (hp2 : p ≠ 2) (hp : (p : K) ≠ 0)
    (H : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = p})
    {P : W.toAffine.Point} (hP : addOrderOf P = 2 * (p / 2) + 1)
    (hPH : AddSubgroup.zmultiples P = H.1) :
    (oddPrimeCyclicRootMap W p hp2 hp H).1 = oddQuotientJ W hP := by
  exact oddQuotientJ_eq_of_prime_zmultiples_eq W p hp2 hp
    (primeKernelGenerator_oddOrder W p hp2 H) hP
    ((primeKernelGenerator_zmultiples W p H).trans hPH.symm)

/-- Every actual polynomial root is reached by the original cyclic-subgroup map. -/
theorem oddPrimeCyclicRootMap_surjective (hp2 : p ≠ 2) (hp : (p : K) ≠ 0) :
    Function.Surjective (oddPrimeCyclicRootMap W p hp2 hp) := by
  intro x
  obtain ⟨P, hP, hx⟩ :=
    (modularPolynomial_isRoot_iff_exists_oddQuotientJ W p hp2 hp x.1).mp x.2
  have hpodd : p = 2 * (p / 2) + 1 := by
    obtain ⟨m, hm⟩ := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left hp2
    omega
  let H : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = p} :=
    ⟨AddSubgroup.zmultiples P,
      (AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq_top _).mpr ⟨P, rfl⟩,
      (Nat.card_zmultiples P).trans (hP.trans hpodd.symm)⟩
  refine ⟨H, Subtype.ext ?_⟩
  exact (oddPrimeCyclicRootMap_eq_quotient W p hp2 hp H hP rfl).trans hx

end
end Dubon2026.SourceFunctionField.IntegralJCoordinate
