import Dubon2026.RationalPrimeCyclotomicReciprocityRationalUnitAction
import Dubon2026.RationalSignedPrimeProduct

/-! # The rational residual after removing its normalized p-power

For a rational unit `q`, remove the rational prime raised to the normalized
order of `q` in the actual rational-prime local field.  Its local image has
order zero, while the signed finite-prime product reconstructs the same
rational residual exactly.  This identifies the rational object whose
away-prime and real factors must cancel the ramified cyclotomic action.
-/
namespace Dubon2026
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped BigOperators ValuativeRel

/-- The positive rational prime regarded as a unit of `ℚ`. -/
def rationalPrimeRationalPrimeUnit (p : ℕ) (hp : p.Prime) : ℚˣ :=
  Units.mk0 (p : ℚ) (Nat.cast_ne_zero.mpr hp.ne_zero)

/-- A rational unit with its normalized local p-power removed. -/
def rationalPrimeNormalizedResidual (p : ℕ) (hp : p.Prime) (q : ℚˣ) : ℚˣ :=
  q / rationalPrimeRationalPrimeUnit p hp ^
    localFieldUnitOrder (rationalPrimeLocalField p hp)
      (Additive.ofMul (rationalPrimeRationalUnit p hp q))

@[simp] theorem rationalPrimeRationalUnit_prime
    (p : ℕ) (hp : p.Prime) :
    rationalPrimeRationalUnit p hp (rationalPrimeRationalPrimeUnit p hp) =
      rationalPrimePrimeUnit p hp := by
  apply Units.ext
  change algebraMap ℚ (rationalPrimeLocalField p hp) (p : ℚ) =
    (p : rationalPrimeLocalField p hp)
  rw [map_natCast]

/-- The local image of the rational normalized residual is the quotient used
inside the arbitrary rational-unit reciprocity proof. -/
theorem rationalPrimeRationalUnit_normalizedResidual
    (p : ℕ) (hp : p.Prime) (q : ℚˣ) :
    rationalPrimeRationalUnit p hp (rationalPrimeNormalizedResidual p hp q) =
      rationalPrimeRationalUnit p hp q /
        rationalPrimePrimeUnit p hp ^
          localFieldUnitOrder (rationalPrimeLocalField p hp)
            (Additive.ofMul (rationalPrimeRationalUnit p hp q)) := by
  apply Units.ext
  simp [rationalPrimeNormalizedResidual, rationalPrimeRationalUnit,
    rationalPrimeRationalPrimeUnit, rationalPrimePrimeUnit]

/-- Removing the normalized rational p-power leaves local order zero. -/
theorem rationalPrimeNormalizedResidual_order
    (p : ℕ) (hp : p.Prime) (q : ℚˣ) :
    localFieldUnitOrder (rationalPrimeLocalField p hp)
      (Additive.ofMul (rationalPrimeRationalUnit p hp
        (rationalPrimeNormalizedResidual p hp q))) = 0 := by
  rw [rationalPrimeRationalUnit_normalizedResidual]
  let K := rationalPrimeLocalField p hp
  let qK := rationalPrimeRationalUnit p hp q
  let π := rationalPrimePrimeUnit p hp
  let z := localFieldUnitOrder K (Additive.ofMul qK)
  have hπorder : localFieldUnitOrder K (Additive.ofMul π) = 1 :=
    rationalPrimeLocalField_prime_order p hp
  change localFieldUnitOrder K (Additive.ofMul (qK / π ^ z)) = 0
  change localFieldUnitOrder K (Additive.ofMul qK - z • Additive.ofMul π) = 0
  rw [map_sub, map_zsmul, hπorder, zsmul_eq_mul, mul_one]
  exact sub_self z

/-- The original rational finite-place valuation of the normalized residual
at `p` is one. -/
theorem rationalPrimeNormalizedResidual_valuation_eq_one
    (p : ℕ) (hp : p.Prime) (q : ℚˣ) :
    (rationalPrimePlace p hp).valuation ℚ
      (rationalPrimeNormalizedResidual p hp q).val = 1 := by
  let r := rationalPrimeNormalizedResidual p hp q
  have horder := rationalPrimeNormalizedResidual_order p hp q
  have hrational := rationalPrimeLocalField_rational_order p hp r
  have hlog : WithZero.log ((rationalPrimePlace p hp).valuation ℚ r.val) = 0 := by
    apply neg_eq_zero.mp
    exact hrational.symm.trans horder
  have hne : (rationalPrimePlace p hp).valuation ℚ r.val ≠ 0 :=
    ((rationalPrimePlace p hp).valuation ℚ).ne_zero_iff.mpr r.ne_zero
  calc
    (rationalPrimePlace p hp).valuation ℚ r.val =
        WithZero.exp (WithZero.log ((rationalPrimePlace p hp).valuation ℚ r.val)) :=
      (WithZero.exp_log hne).symm
    _ = WithZero.exp 0 := by rw [hlog]
    _ = 1 := WithZero.exp_zero

/-- The exact p-normalized rational residual has finite normalized-prime
support, local p-order zero, and is reconstructed by those finite factors
together with its real sign. -/
theorem rationalPrimeNormalizedResidual_exists_signed_prime_product
    (p : ℕ) (hp : p.Prime) (q : ℚˣ) :
    localFieldUnitOrder (rationalPrimeLocalField p hp)
        (Additive.ofMul (rationalPrimeRationalUnit p hp
          (rationalPrimeNormalizedResidual p hp q))) = 0 ∧
      ∃ S : Finset (HeightOneSpectrum ℤ),
        (∀ v ∉ S, v.valuation ℚ (rationalPrimeNormalizedResidual p hp q).val = 1) ∧
        (if 0 < (rationalPrimeNormalizedResidual p hp q).val then (1 : ℚ) else -1) *
          (∏ v ∈ S, (Rat.HeightOneSpectrum.natGenerator v : ℚ) ^
            localFieldUnitOrder
              (rationalPrimeLocalField (Rat.HeightOneSpectrum.natGenerator v)
                (Rat.HeightOneSpectrum.prime_natGenerator v))
              (Additive.ofMul (Units.map (algebraMap ℚ
                (rationalPrimeLocalField (Rat.HeightOneSpectrum.natGenerator v)
                  (Rat.HeightOneSpectrum.prime_natGenerator v))).toMonoidHom
                    (rationalPrimeNormalizedResidual p hp q)))) =
          (rationalPrimeNormalizedResidual p hp q).val := by
  exact ⟨rationalPrimeNormalizedResidual_order p hp q,
    rationalSignedPrimeProduct_exists_support (rationalPrimeNormalizedResidual p hp q)⟩

/-- The signed finite-prime reconstruction of the normalized residual can be
chosen with the ramified place `p` absent from its support.  Thus every
remaining finite factor is eligible for the proved away-from-conductor
reciprocity formula. -/
theorem rationalPrimeNormalizedResidual_exists_away_signed_prime_product
    (p : ℕ) (hp : p.Prime) (q : ℚˣ) :
    ∃ S : Finset (HeightOneSpectrum ℤ),
      rationalPrimePlace p hp ∉ S ∧
      (∀ v ∉ S, v.valuation ℚ (rationalPrimeNormalizedResidual p hp q).val = 1) ∧
      (if 0 < (rationalPrimeNormalizedResidual p hp q).val then (1 : ℚ) else -1) *
        (∏ v ∈ S, (Rat.HeightOneSpectrum.natGenerator v : ℚ) ^
          localFieldUnitOrder
            (rationalPrimeLocalField (Rat.HeightOneSpectrum.natGenerator v)
              (Rat.HeightOneSpectrum.prime_natGenerator v))
            (Additive.ofMul (Units.map (algebraMap ℚ
              (rationalPrimeLocalField (Rat.HeightOneSpectrum.natGenerator v)
                (Rat.HeightOneSpectrum.prime_natGenerator v))).toMonoidHom
                  (rationalPrimeNormalizedResidual p hp q)))) =
        (rationalPrimeNormalizedResidual p hp q).val := by
  classical
  let r := rationalPrimeNormalizedResidual p hp q
  let w := rationalPrimePlace p hp
  let f : HeightOneSpectrum ℤ → ℚ := fun v =>
    (Rat.HeightOneSpectrum.natGenerator v : ℚ) ^
      localFieldUnitOrder
        (rationalPrimeLocalField (Rat.HeightOneSpectrum.natGenerator v)
          (Rat.HeightOneSpectrum.prime_natGenerator v))
        (Additive.ofMul (Units.map (algebraMap ℚ
          (rationalPrimeLocalField (Rat.HeightOneSpectrum.natGenerator v)
            (Rat.HeightOneSpectrum.prime_natGenerator v))).toMonoidHom r))
  obtain ⟨S, hS, hprod⟩ := rationalSignedPrimeProduct_exists_support r
  have hwval : w.valuation ℚ r.val = 1 :=
    rationalPrimeNormalizedResidual_valuation_eq_one p hp q
  have hwfactor : f w = 1 := by
    simp only [f]
    rw [rationalPrimeLocalField_rational_order,
      rationalPrimePlace_of_natGenerator, hwval]
    simp
  have houtside : ∀ v ∉ S.erase w, v.valuation ℚ r.val = 1 := by
    intro v hv
    by_cases hvw : v = w
    · simpa only [hvw] using hwval
    · apply hS v
      intro hvS
      exact hv (Finset.mem_erase.mpr ⟨hvw, hvS⟩)
  have herase : (∏ v ∈ S.erase w, f v) = ∏ v ∈ S, f v := by
    by_cases hwS : w ∈ S
    · have h := Finset.mul_prod_erase S f hwS
      rw [hwfactor, one_mul] at h
      exact h
    · rw [Finset.erase_eq_of_notMem hwS]
  refine ⟨S.erase w, Finset.notMem_erase w S, houtside, ?_⟩
  change (if 0 < r.val then (1 : ℚ) else -1) * (∏ v ∈ S.erase w, f v) = r.val
  rw [herase]
  exact hprod

end
end Dubon2026
