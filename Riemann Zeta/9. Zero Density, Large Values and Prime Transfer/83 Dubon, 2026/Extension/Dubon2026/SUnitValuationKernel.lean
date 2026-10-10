import Mathlib.RingTheory.DedekindDomain.SInteger
import Mathlib.RingTheory.DedekindDomain.SelmerGroup

/-! # Original S-unit valuation coordinates and their ordinary-unit kernel -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain

variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- The actual valuations of an original S-unit at the places in S. -/
def sUnitValuations (S : Set (HeightOneSpectrum R)) :
    S.unit K →* (S → Multiplicative ℤ) :=
  Pi.monoidHom fun v => v.val.valuationOfNeZero.comp (S.unit K).subtype

/-- The finite-coordinate valuation kernel consists exactly of units trivial at every original place. -/
theorem sUnitValuations_mem_ker_iff (S : Set (HeightOneSpectrum R))
    (x : S.unit K) :
    x ∈ (sUnitValuations (K := K) S).ker ↔
      x.val ∈ (∅ : Set (HeightOneSpectrum R)).unit K := by
  constructor
  · intro hx v _
    by_cases hv : v ∈ S
    · have h := congrFun hx (⟨v, hv⟩ : S)
      change v.valuationOfNeZero x.val = 1 at h
      have h' := congrArg (fun z : Multiplicative ℤ => (z : WithZero (Multiplicative ℤ))) h
      simpa only [HeightOneSpectrum.valuationOfNeZero_eq, WithZero.coe_one] using h'
    · exact x.property v hv
  · intro hx
    apply funext
    intro v
    change v.val.valuationOfNeZero x.val = 1
    apply WithZero.coe_injective
    simpa only [HeightOneSpectrum.valuationOfNeZero_eq, WithZero.coe_one] using
      hx v.val (Set.notMem_empty v.val)

/-- The actual S-unit coordinate kernel is canonically the original empty-set unit group. -/
def sUnitValuationKernelEquiv (S : Set (HeightOneSpectrum R)) :
    (sUnitValuations (K := K) S).ker ≃*
      (∅ : Set (HeightOneSpectrum R)).unit K where
  toFun x := ⟨x.val.val, (sUnitValuations_mem_ker_iff S x.val).mp x.property⟩
  invFun x := ⟨⟨x.val, fun v _ => x.property v (Set.notMem_empty v)⟩,
    (sUnitValuations_mem_ker_iff S _).mpr x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Empty-set units of the actual fraction field identify with the original base-ring units. -/
def emptySUnitEquivBaseUnits :
    (∅ : Set (HeightOneSpectrum R)).unit K ≃* Rˣ :=
  (Set.unitEquivUnitsInteger (∅ : Set (HeightOneSpectrum R)) K).trans
    (Units.mapEquiv (((Subalgebra.equivOfEq _ _ (IsDedekindDomain.integer_empty R K)).trans
      (Algebra.botEquivOfInjective (IsFractionRing.injective R K))).toMulEquiv))

/-- The literal valuation kernel of the original S-units is the original ordinary unit group. -/
def sUnitValuationKernelBaseEquiv (S : Set (HeightOneSpectrum R)) :
    (sUnitValuations (K := K) S).ker ≃* Rˣ :=
  (sUnitValuationKernelEquiv S).trans emptySUnitEquivBaseUnits

end
end Dubon2026
