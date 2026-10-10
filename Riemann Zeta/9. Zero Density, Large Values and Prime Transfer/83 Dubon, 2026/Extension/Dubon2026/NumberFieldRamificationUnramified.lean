import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.NumberTheory.NumberField.Basic

/-! # The actual number-field ramification index and localized unramified algebra -/

namespace Dubon2026

open scoped NumberField

open IsDedekindDomain

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]

/-- At the actual original prime above the base prime, index one is equivalent to formal unramifiedness of the genuine prime localization over the original integer ring. -/
theorem numberField_isUnramifiedAt_iff_ramificationIdx_one
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] :
    Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal ↔
      v.asIdeal.ramificationIdx w.asIdeal = 1 := by
  have h := Algebra.isUnramifiedAt_iff_of_isDedekindDomain
    (R := 𝓞 K) (p := w.asIdeal) w.ne_bot
  rw [← Ideal.over_def w.asIdeal v.asIdeal] at h
  exact h

end Dubon2026
