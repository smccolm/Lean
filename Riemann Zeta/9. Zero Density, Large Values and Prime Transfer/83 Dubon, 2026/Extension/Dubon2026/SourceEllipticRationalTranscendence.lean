import Mathlib.FieldTheory.RatFunc.IntermediateField

/-! Nonconstancy of the explicit odd quotient coordinate from its existing degree bounds.
Native rational-function transcendence and fraction-ring lifting avoid a new
valuation argument. This is used to discharge the transcendence input to the actual
quotient field embedding needed for cyclic modular-polynomial roots (DUB-17/18). -/

open Polynomial

namespace Dubon2026.SourceEllipticFunctionField

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

/-- A polynomial quotient whose numerator has larger degree is transcendental. -/
theorem transcendental_ratFunc_div_of_natDegree_lt {p q : F[X]} (hq : q ≠ 0)
    (hdeg : q.natDegree < p.natDegree) :
    Transcendental F (algebraMap F[X] (RatFunc F) p / algebraMap F[X] (RatFunc F) q) := by
  apply RatFunc.transcendental_of_ne_C
  rintro ⟨c, hc⟩
  have hq' : algebraMap F[X] (RatFunc F) q ≠ 0 := by
    simpa using (RatFunc.algebraMap_injective F).ne hq
  rw [div_eq_iff hq', ← RatFunc.algebraMap_C, ← map_mul] at hc
  have he : p = C c * q := RatFunc.algebraMap_injective F hc
  have hle : (C c * q).natDegree ≤ (C c).natDegree + q.natDegree := natDegree_mul_le
  rw [← he, natDegree_C, zero_add] at hle
  exact (not_lt_of_ge hle) hdeg

/-- Evaluating such a rational function at a transcendental coordinate preserves transcendence. -/
theorem transcendental_aeval_div_of_natDegree_lt {x : L} (hx : Transcendental F x)
    {p q : F[X]} (hq : q ≠ 0) (hdeg : q.natDegree < p.natDegree) :
    Transcendental F (aeval x p / aeval x q) := by
  let f : RatFunc F →ₐ[F] L := IsFractionRing.liftAlgHom (transcendental_iff_injective.mp hx)
  have hf (r : F[X]) : f (algebraMap F[X] (RatFunc F) r) = aeval x r := by
    simp [f, IsFractionRing.liftAlgHom_apply]
  have ht := transcendental_ratFunc_div_of_natDegree_lt hq hdeg
  have hm : Transcendental F
      (f (algebraMap F[X] (RatFunc F) p / algebraMap F[X] (RatFunc F) q)) :=
    fun h => ht ((isAlgebraic_algHom_iff f f.injective).mp h)
  simpa only [map_div₀, hf] using hm

end Dubon2026.SourceEllipticFunctionField
