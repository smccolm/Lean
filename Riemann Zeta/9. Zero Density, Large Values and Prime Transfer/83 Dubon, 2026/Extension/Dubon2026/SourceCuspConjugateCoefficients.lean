import Dubon2026.SourceOriginalCuspWidth

/-! DUB-17/18 -> numerical modular genus -> cusp count -> distinctness of
primitive cusp labels. Leading coefficients of powers of the actual
conjugate j series detect the phase label after cancellation with a power
of j. Existing j-power coefficients and literal expansion/twist maps
supply the formulas; no analytic or residue-field hypothesis is added.
Adapted from the coeff_slot_pow argument in anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_card_poles_jqModC_modularFunctionFieldFullC_eq_cuspCount.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open PrimeDegreeAux
variable {K : Type*} [Field K]

theorem cusp_coeff_algebraMap_mul (c : K) (f : LaurentSeries K) (i : ℤ) :
    (algebraMap K (LaurentSeries K) c * f).coeff i = c * f.coeff i := by
  rw [SourceDifferential.algebraMap_laurentSeries_apply_alt,
    HahnSeries.single_zero_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]

theorem cusp_coeff_TS_pow (u : Kˣ) (e : ℕ) [NeZero e] (n : ℕ) :
    ((TS K e u) ^ n).coeff (-((e * n : ℕ) : ℤ)) = ((u ^ (-(n : ℤ)) : Kˣ) : K) ∧
      ∀ i < -((e * n : ℕ) : ℤ), ((TS K e u) ^ n).coeff i = 0 := by
  rw [TS, ← map_pow, ← map_pow]
  constructor
  · rw [show -((e * n : ℕ) : ℤ) = (e : ℤ) * (-(n : ℤ)) by push_cast; ring,
      qExpand_coeff_mul, qTwist_coeff, coeff_jqModC_pow_self, mul_one]
  · intro i hi
    by_cases hdvd : (e : ℤ) ∣ i
    · obtain ⟨m, rfl⟩ := hdvd
      have he : (0 : ℤ) < e := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne e)
      have hm : m < -(n : ℤ) := by
        apply lt_of_mul_lt_mul_left (a := (e : ℤ)) _ he.le
        rw [mul_neg]
        exact_mod_cast hi
      rw [qExpand_coeff_mul, qTwist_coeff, coeff_jqModC_pow_of_lt K hm, mul_zero]
    · exact qExpand_coeff_of_not_dvd e _ hdvd

theorem cusp_coeff_TS_one_pow (e : ℕ) [NeZero e] (n : ℕ) :
    ((TS K e 1) ^ n).coeff (-((e * n : ℕ) : ℤ)) = 1 ∧
      ∀ i < -((e * n : ℕ) : ℤ), ((TS K e 1) ^ n).coeff i = 0 := by
  simpa only [one_zpow, Units.val_one] using cusp_coeff_TS_pow (1 : Kˣ) e n

end
end Dubon2026.SourceFunctionField
