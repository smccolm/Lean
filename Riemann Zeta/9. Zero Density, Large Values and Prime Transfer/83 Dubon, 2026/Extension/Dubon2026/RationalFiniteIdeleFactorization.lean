import Dubon2026.RationalFiniteValuationBasis

/-! # A genuine rational determinant factor for every finite idele -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Filter

/-- Absolute value changes no finite rational valuation. -/
theorem rational_finite_valuation_abs (v : HeightOneSpectrum ℤ) (q : ℚ) :
    v.valuation ℚ |q| = v.valuation ℚ q := by
  rcases abs_choice q with h | h
  · rw [h]
  · rw [h, Valuation.map_neg]

/-- The valuations of a genuine finite idele are realized by one positive rational number. -/
theorem finiteIdele_exists_positive_rational_valuations (a : (FiniteAdeleRing ℤ ℚ)ˣ) :
    ∃ q : ℚ, 0 < q ∧ ∀ v : HeightOneSpectrum ℤ,
      v.valuation ℚ q = Valued.v ((a : FiniteAdeleRing ℤ ℚ) v) := by
  classical
  have ha := FiniteAdeleRing.isUnit_iff.mp a.isUnit
  have hf : {v : HeightOneSpectrum ℤ | Valued.v ((a : FiniteAdeleRing ℤ ℚ) v) ≠ 1}.Finite :=
    Filter.eventually_cofinite.mp ha.2
  let S := hf.toFinset
  let n (v : HeightOneSpectrum ℤ) : ℤ := -log (Valued.v ((a : FiniteAdeleRing ℤ ℚ) v))
  let q := rationalFiniteValuationProduct S n
  refine ⟨|q|, abs_pos.mpr (rationalFiniteValuationProduct_ne_zero S n), ?_⟩
  intro v
  rw [rational_finite_valuation_abs]
  change v.valuation ℚ (rationalFiniteValuationProduct S n) = _
  rw [rationalFiniteValuationProduct_valuation]
  by_cases hv : v ∈ S
  · rw [if_pos hv]
    simp only [n, neg_neg]
    exact exp_log ((Valuation.ne_zero_iff _).mpr (ha.1 v))
  · rw [if_neg hv]
    have he : Valued.v ((a : FiniteAdeleRing ℤ ℚ) v) = 1 := by
      simpa only [S, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] using hv
    exact he.symm

/-- Every actual finite idele is a positive rational scalar times an actual everywhere-integral unit. -/
theorem finiteIdele_positive_rational_integral_unit (a : (FiniteAdeleRing ℤ ℚ)ˣ) :
    ∃ q : ℚ, 0 < q ∧ ∃ u : finiteAdeleIntegerSubringˣ,
      (a : FiniteAdeleRing ℤ ℚ) = algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q * u.val.val := by
  obtain ⟨q, hq, hval⟩ := finiteIdele_exists_positive_rational_valuations a
  have hq0 := ne_of_gt hq
  have ha := (FiniteAdeleRing.isUnit_iff.mp a.isUnit).1
  let b : FiniteAdeleRing ℤ ℚ :=
    algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q⁻¹ * (a : FiniteAdeleRing ℤ ℚ)
  let c : FiniteAdeleRing ℤ ℚ :=
    (↑a⁻¹ : FiniteAdeleRing ℤ ℚ) * algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q
  have hloc (v : HeightOneSpectrum ℤ) :
      Valued.v (algebraMap ℚ (v.adicCompletion ℚ) q) =
        Valued.v ((a : FiniteAdeleRing ℤ ℚ) v) := by
    simpa only [algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self_apply, valuedAdicCompletion_eq_valuation'] using hval v
  have hb : b ∈ finiteAdeleIntegerSubring := by
    intro v
    change Valued.v (algebraMap ℚ (v.adicCompletion ℚ) q⁻¹ *
      (a : FiniteAdeleRing ℤ ℚ) v) ≤ 1
    rw [map_mul, map_inv₀, map_inv₀, hloc, inv_mul_cancel₀
      ((Valuation.ne_zero_iff _).mpr (ha v))]
  have hc : c ∈ finiteAdeleIntegerSubring := by
    intro v
    have hai : (↑a⁻¹ : FiniteAdeleRing ℤ ℚ) v = ((a : FiniteAdeleRing ℤ ℚ) v)⁻¹ := by
      have h := congrArg (fun x : FiniteAdeleRing ℤ ℚ => x v) a.val_inv
      change (a : FiniteAdeleRing ℤ ℚ) v * (↑a⁻¹ : FiniteAdeleRing ℤ ℚ) v = 1 at h
      calc
        (↑a⁻¹ : FiniteAdeleRing ℤ ℚ) v = (↑a⁻¹ : FiniteAdeleRing ℤ ℚ) v *
          ((a : FiniteAdeleRing ℤ ℚ) v * ((a : FiniteAdeleRing ℤ ℚ) v)⁻¹) := by
            rw [mul_inv_cancel₀ (ha v), mul_one]
        _ = ((a : FiniteAdeleRing ℤ ℚ) v * (↑a⁻¹ : FiniteAdeleRing ℤ ℚ) v) *
            ((a : FiniteAdeleRing ℤ ℚ) v)⁻¹ := by ring
        _ = ((a : FiniteAdeleRing ℤ ℚ) v)⁻¹ := by rw [h, one_mul]
    change Valued.v ((↑a⁻¹ : FiniteAdeleRing ℤ ℚ) v *
      algebraMap ℚ (v.adicCompletion ℚ) q) ≤ 1
    rw [hai, map_mul, map_inv₀, hloc, inv_mul_cancel₀
      ((Valuation.ne_zero_iff _).mpr (ha v))]
  have hbc : b * c = 1 := by
    calc
      b * c = (algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q⁻¹ *
        algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q) *
        ((a : FiniteAdeleRing ℤ ℚ) * (↑a⁻¹ : FiniteAdeleRing ℤ ℚ)) := by dsimp [b, c]; ring
      _ = 1 := by rw [Units.mul_inv, mul_one, ← map_mul, inv_mul_cancel₀ hq0, map_one]
  let u : finiteAdeleIntegerSubringˣ :=
    { val := ⟨b, hb⟩
      inv := ⟨c, hc⟩
      val_inv := Subtype.ext hbc
      inv_val := Subtype.ext (by rwa [mul_comm] at hbc) }
  refine ⟨q, hq, u, ?_⟩
  change (a : FiniteAdeleRing ℤ ℚ) =
    algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q *
      (algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q⁻¹ * (a : FiniteAdeleRing ℤ ℚ))
  rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hq0, map_one, one_mul]

end
end Dubon2026
