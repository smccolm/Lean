import Dubon2026.FinitePlaceHeckeDiagonalPowers
import Dubon2026.FinitePlaceIntegerUnits
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Group.Basic

/-! # Genuine unramified characters of the original local multiplicative group -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Filter
open scoped Topology

/-- The original discrete local order of an actual field unit, with positive order for a uniformizer. -/
def finitePlaceUnitOrder (v : HeightOneSpectrum ℤ) (u : (v.adicCompletion ℚ)ˣ) : ℤ :=
  -log (Valued.v u.val)

/-- The genuine local order is zero at the identity. -/
theorem finitePlaceUnitOrder_one (v : HeightOneSpectrum ℤ) : finitePlaceUnitOrder v 1 = 0 := by
  simp [finitePlaceUnitOrder]

/-- The actual discrete order adds under multiplication of original local units. -/
theorem finitePlaceUnitOrder_mul (v : HeightOneSpectrum ℤ) (a b : (v.adicCompletion ℚ)ˣ) :
    finitePlaceUnitOrder v (a * b) = finitePlaceUnitOrder v a + finitePlaceUnitOrder v b := by
  unfold finitePlaceUnitOrder
  rw [Units.val_mul, map_mul, log_mul ((Valuation.ne_zero_iff _).mpr (Units.ne_zero a))
    ((Valuation.ne_zero_iff _).mpr (Units.ne_zero b)), neg_add]

/-- Original integral units have discrete order zero. Both the original value and inverse must be integral. -/
theorem finitePlaceUnitOrder_integral (v : HeightOneSpectrum ℤ) (u : (v.adicCompletion ℚ)ˣ)
    (hu : u.val ∈ v.adicCompletionIntegers ℚ)
    (hui : u.inv ∈ v.adicCompletionIntegers ℚ) : finitePlaceUnitOrder v u = 0 := by
  have hv : Valued.v u.val = 1 := by
    apply le_antisymm hu
    calc
      1 = Valued.v u.val * Valued.v u.inv := by rw [← map_mul, u.val_inv, map_one]
      _ ≤ Valued.v u.val * 1 := mul_le_mul_right hui _
      _ = Valued.v u.val := mul_one _
  simp only [finitePlaceUnitOrder, hv, log_one, neg_zero]

/-- An actual nonzero complex parameter gives its genuine unramified local multiplicative character. -/
def finitePlaceUnramifiedCharacter (v : HeightOneSpectrum ℤ) (z : ℂˣ) :
    (v.adicCompletion ℚ)ˣ →* ℂˣ where
  toFun u := z ^ finitePlaceUnitOrder v u
  map_one' := by rw [finitePlaceUnitOrder_one, zpow_zero]
  map_mul' a b := by rw [finitePlaceUnitOrder_mul, zpow_add]

/-- The actual unramified character is one on the genuine local integral units. -/
theorem finitePlaceUnramifiedCharacter_integral (v : HeightOneSpectrum ℤ) (z : ℂˣ)
    (u : (v.adicCompletion ℚ)ˣ)
    (hu : u.val ∈ v.adicCompletionIntegers ℚ)
    (hui : u.inv ∈ v.adicCompletionIntegers ℚ) :
    finitePlaceUnramifiedCharacter v z u = 1 := by
  change z ^ finitePlaceUnitOrder v u = 1
  rw [finitePlaceUnitOrder_integral v u hu hui, zpow_zero]

/-- The actual unramified character is continuous in the genuine original local-unit topology. -/
theorem finitePlaceUnramifiedCharacter_continuous (v : HeightOneSpectrum ℤ) (z : ℂˣ) :
    Continuous (finitePlaceUnramifiedCharacter v z) := by
  apply continuous_of_continuousAt_one
  change Tendsto (finitePlaceUnramifiedCharacter v z) (𝓝 1) (𝓝 (finitePlaceUnramifiedCharacter v z 1))
  rw [map_one]
  apply tendsto_nhds_of_eventually_eq
  let U : Set (v.adicCompletion ℚ)ˣ := {u | u.val ∈ v.adicCompletionIntegers ℚ ∧
    u.inv ∈ v.adicCompletionIntegers ℚ}
  have hI : IsOpen (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) :=
    Valued.isOpen_valuationSubring _
  have hU : IsOpen U := (hI.preimage Units.continuous_val).inter
    (hI.preimage (Units.continuous_val.comp continuous_inv))
  have h1 : (1 : (v.adicCompletion ℚ)ˣ) ∈ U :=
    ⟨(v.adicCompletionIntegers ℚ).one_mem, (v.adicCompletionIntegers ℚ).one_mem⟩
  filter_upwards [hU.mem_nhds h1] with u hu
  exact finitePlaceUnramifiedCharacter_integral v z u hu.1 hu.2

/-- The original rational prime has local order exactly one at its own genuine finite place. -/
theorem finitePlaceUnitOrder_prime (p : ℕ) [NeZero p] (hp : p.Prime) :
    finitePlaceUnitOrder (rationalPrimePlace p hp) (finitePlacePrimeUnit p (rationalPrimePlace p hp)) = 1 := by
  let v := rationalPrimePlace p hp
  have hs : Ideal.span ({(p : ℤ)} : Set ℤ) = v.asIdeal := by
    ext n
    rw [Ideal.mem_span_singleton]
    exact (rationalPrimePlace_int_mem_iff p hp n).symm
  have hv : v.valuation ℚ (p : ℚ) = exp (-1 : ℤ) := by
    change v.valuation ℚ (algebraMap ℤ ℚ (p : ℤ)) = _
    rw [valuation_of_algebraMap]
    exact v.intValuation_singleton (Int.natCast_ne_zero.mpr hp.ne_zero) hs.symm
  have hc : Valued.v ((finitePlacePrimeUnit p v).val) = exp (-1 : ℤ) := by
    change Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (p : ℚ)) = _
    simpa only [algebraMap_adicCompletion, Function.comp_apply, Algebra.algebraMap_self_apply,
      valuedAdicCompletion_eq_valuation'] using hv
  change -log (Valued.v ((finitePlacePrimeUnit p v).val)) = 1
  rw [hc, log_exp, neg_neg]

/-- The actual unramified character takes exactly its original complex parameter on the original prime unit. -/
theorem finitePlaceUnramifiedCharacter_prime (p : ℕ) [NeZero p] (hp : p.Prime) (z : ℂˣ) :
    finitePlaceUnramifiedCharacter (rationalPrimePlace p hp) z
      (finitePlacePrimeUnit p (rationalPrimePlace p hp)) = z := by
  change z ^ finitePlaceUnitOrder _ _ = z
  rw [finitePlaceUnitOrder_prime, zpow_one]

end
end Dubon2026
