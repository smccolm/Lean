import Dubon2026.FractionalIdealPowerRoots
import Mathlib.RingTheory.ClassGroup
import Mathlib.RingTheory.DedekindDomain.SelmerGroup

/-! # Actual principal-ideal multiplicities and the pinned Selmer valuation condition -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain
open scoped nonZeroDivisors

variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- The actual principal-ideal multiplicity is the negative logarithm of the original multiplicative valuation. -/
theorem principalIdeal_count_eq_neg_valuation (v : HeightOneSpectrum R) (x : Kˣ) :
    FractionalIdeal.count K v (toPrincipalIdeal R K x).val =
      -(v.valuationOfNeZero x).toAdd := by
  classical
  let s := IsLocalization.sec R⁰ (x : K)
  have hrep : FractionalIdeal.spanSingleton R⁰ (x : K) =
      FractionalIdeal.spanSingleton R⁰ ((algebraMap R K) s.snd)⁻¹ *
        (Ideal.span {s.fst} : Ideal R) := by
    rw [FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.spanSingleton_mul_spanSingleton]
    congr 1
    have hsec := IsLocalization.mk'_sec (M := R⁰) K (x : K)
    rw [IsFractionRing.mk'_eq_div, div_eq_mul_inv, mul_comm] at hsec
    exact hsec.symm
  rw [coe_toPrincipalIdeal,
    FractionalIdeal.count_well_defined K v
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr x.ne_zero) hrep]
  change _ = -(-(Associates.mk v.asIdeal).count
      (Associates.mk (Ideal.span {s.fst} : Ideal R)).factors -
    (-(Associates.mk v.asIdeal).count
      (Associates.mk (Ideal.span {(s.snd : R)} : Ideal R)).factors : ℤ))
  ring

/-- Vanishing of the actual valuation modulo n means divisibility of the original integral valuation. -/
theorem valuationOfNeZeroMod_eq_one_iff (v : HeightOneSpectrum R) (n : ℕ) (x : Kˣ) :
    v.valuationOfNeZeroMod n
      (QuotientGroup.mk' (powMonoidHom (α := Kˣ) n).range x) = 1 ↔
      (n : ℤ) ∣ (v.valuationOfNeZero x).toAdd := by
  rw [HeightOneSpectrum.valuationOfNeZeroMod, MonoidHom.comp_apply]
  rw [map_eq_one_iff (Int.quotientZMultiplesNatEquivZMod n).toMultiplicative.toMonoidHom
    (Int.quotientZMultiplesNatEquivZMod n).toMultiplicative.injective]
  erw [QuotientGroup.map_mk']
  change QuotientAddGroup.mk' (AddSubgroup.zmultiples (n : ℤ))
    (v.valuationOfNeZero x).toAdd = 0 ↔ _
  exact (QuotientAddGroup.eq_zero_iff (N := AddSubgroup.zmultiples (n : ℤ))
    (v.valuationOfNeZero x).toAdd).trans Int.mem_zmultiples_iff

/-- The original empty-set Selmer condition is exactly divisibility of all actual principal-ideal multiplicities. -/
theorem emptySelmer_mem_iff_principal_counts (n : ℕ) (x : Kˣ) :
    QuotientGroup.mk' (powMonoidHom (α := Kˣ) n).range x ∈
        (IsDedekindDomain.selmerGroup (R := R) (K := K)
          (S := ∅) (n := n)) ↔
      ∀ v : HeightOneSpectrum R,
        (n : ℤ) ∣ FractionalIdeal.count K v (toPrincipalIdeal R K x).val := by
  constructor
  · intro hx v
    rw [principalIdeal_count_eq_neg_valuation, dvd_neg]
    exact (valuationOfNeZeroMod_eq_one_iff v n x).mp
      (hx v (Set.notMem_empty v))
  · intro hx v _
    apply (valuationOfNeZeroMod_eq_one_iff v n x).mpr
    simpa only [principalIdeal_count_eq_neg_valuation, dvd_neg] using hx v

end
end Dubon2026
