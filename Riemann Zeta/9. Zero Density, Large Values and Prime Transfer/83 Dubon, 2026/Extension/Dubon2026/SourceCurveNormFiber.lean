import Dubon2026.SourceCurveIntegralNormDivisor

/-! DUB-17/18 -> original Picard Hecke correspondence -> principal-divisor
pushforward. The proved integral norm sum is transported along the exact
prime/place bijection. The actual integral closure has fraction field E,
so clearing one denominator gives the norm/order identity for every nonzero
function. No norm formula is assumed.
-/
namespace Dubon2026.SourceCurve.Place
noncomputable section
variable {K F E : Type*} [Field K] [Field F] [Field E]
variable [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
variable [FiniteDimensional F E] [Algebra.IsSeparable F E] [CharZero F]

theorem ord_norm_integral_eq_sum_fiber (v : Place K F)
    (hbase : Function.Bijective (algebraMap K v.ResidueField))
    (htop : ∀ w : Place K E, Function.Bijective (algebraMap K w.ResidueField))
    {c : integralClosureAt E v} (hc : c ≠ 0) :
    v.ord (Algebra.norm F (algebraMap (integralClosureAt E v) E c)) =
      ∑ᶠ w : {w : Place K E // w.restrict F = v},
        w.1.ord (algebraMap (integralClosureAt E v) E c) := by
  rw [ord_norm_integralClosureAt v hbase htop hc,
    ← finsum_comp_equiv (fiberPrimeEquiv E v)]
  apply finsum_congr
  intro w
  change (fiberPrimePlace E v (fiberCenter E w.2)).ord _ = w.1.ord _
  rw [fiberPrimePlace_fiberCenter w.2]

theorem ord_norm_eq_sum_fiber (v : Place K F)
    (hbase : Function.Bijective (algebraMap K v.ResidueField))
    (htop : ∀ w : Place K E, Function.Bijective (algebraMap K w.ResidueField))
    {f : E} (hf : f ≠ 0) :
    v.ord (Algebra.norm F f) =
      ∑ᶠ w : {w : Place K E // w.restrict F = v}, w.1.ord f := by
  classical
  haveI : Finite {w : Place K E // w.restrict F = v} := finite_placeFiber v
  letI := Fintype.ofFinite {w : Place K E // w.restrict F = v}
  obtain ⟨⟨c, s⟩, hcs⟩ := IsLocalization.surj
    (nonZeroDivisors (integralClosureAt E v)) f
  have hs0 : (s : integralClosureAt E v) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  have hsE : algebraMap (integralClosureAt E v) E (s : integralClosureAt E v) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (integralClosureAt E v) E)).mpr hs0
  have hcE : algebraMap (integralClosureAt E v) E c ≠ 0 := by
    rw [← hcs]
    exact mul_ne_zero hf hsE
  have hc0 : c ≠ 0 := fun h => hcE (by rw [h, map_zero])
  have hintc := ord_norm_integral_eq_sum_fiber v hbase htop hc0
  have hints := ord_norm_integral_eq_sum_fiber v hbase htop hs0
  rw [finsum_eq_sum_of_fintype] at hintc hints ⊢
  rw [← hcs, map_mul, v.ord_mul (Algebra.norm_ne_zero_iff.mpr hf)
    (Algebra.norm_ne_zero_iff.mpr hsE), hints] at hintc
  have hsplit :
      (∑ w : {w : Place K E // w.restrict F = v},
        w.1.ord (f * algebraMap (integralClosureAt E v) E (s : integralClosureAt E v))) =
      (∑ w : {w : Place K E // w.restrict F = v}, w.1.ord f) +
      ∑ w : {w : Place K E // w.restrict F = v},
        w.1.ord (algebraMap (integralClosureAt E v) E (s : integralClosureAt E v)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun w _ => w.1.ord_mul hf hsE
  rw [hsplit] at hintc
  omega

end
end Dubon2026.SourceCurve.Place
