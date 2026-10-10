import Mathlib.NumberTheory.RamificationInertia.HilbertTheory
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Group.Subgroup.Finite

/-! # The actual inertia subgroup and original number-field ramification index -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain
open scoped NumberField

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- The genuine inertia subgroup of an original number-field prime has cardinality equal to its original ramification index. Residue separability is derived from the actual finite residue field. -/
theorem numberField_card_inertia_eq_ramificationIdx
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] :
    Nat.card (w.asIdeal.inertia Gal(L/K)) = v.asIdeal.ramificationIdx w.asIdeal := by
  letI : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  letI : Field (𝓞 L ⧸ w.asIdeal) := Ideal.Quotient.field w.asIdeal
  letI : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  have h := Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(L/K))
    v.asIdeal v.ne_bot w.asIdeal
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.asIdeal Gal(L/K)] at h
  exact h

/-- An original index-one number-field prime has trivial actual inertia subgroup. -/
theorem numberField_inertia_eq_bot_of_ramificationIdx_one
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal]
    (hunram : v.asIdeal.ramificationIdx w.asIdeal = 1) :
    w.asIdeal.inertia Gal(L/K) = ⊥ := by
  apply Subgroup.eq_bot_of_card_eq
  rw [numberField_card_inertia_eq_ramificationIdx v w, hunram]

/-- Every original inertia automorphism at an index-one prime fixes the whole original number field. -/
theorem numberField_inertia_fixes_of_ramificationIdx_one
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal]
    (hunram : v.asIdeal.ramificationIdx w.asIdeal = 1)
    (σ : Gal(L/K)) (hσ : σ ∈ w.asIdeal.inertia Gal(L/K)) (x : L) : σ x = x := by
  rw [numberField_inertia_eq_bot_of_ramificationIdx_one v w hunram] at hσ
  have hσone : σ = 1 := hσ
  rw [hσone]
  rfl

end
end Dubon2026
