import Dubon2026.SourceCuspConjugateCoefficients

/-! DUB-17/18 -> numerical modular genus -> cusp count -> distinct labels.
If two actual conjugate embeddings induce the same normalized place,
their j orders force the same normalization, their j_N orders force the
same divisor a, and cancellation of the leading coefficient detects b
modulo gcd(a,N/a). Only this necessary equality criterion is needed for
injecting primitive labels; the reverse orbit-classification implication
is deferred. Adapted from the forward slotOrbit proof in
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_card_poles_jqModC_modularFunctionFieldFullC_eq_cuspCount.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve ConjugateSlots PrimeDegreeAux

theorem cusp_parameters_of_same_place (N : ℕ) [NeZero N]
    (L : Type*) [Field L] [Algebra ℚ L]
    (ζ : Lˣ) (hζ : IsPrimitiveRoot (ζ : L) N)
    (a b a' b' : ℕ) [NeZero a] [NeZero a'] (ha : a ∣ N)
    (ι ι' : modularFunctionFieldOver N L →ₐ[L] LaurentSeries L)
    (hj : ι (jOver N L) = TS L N 1) (hjN : ι (jNOver N L) = slotValue ζ a b)
    (hj' : ι' (jOver N L) = TS L N 1) (hjN' : ι' (jNOver N L) = slotValue ζ a' b')
    (w : Place L (modularFunctionFieldOver N L)) (γ γ' : ℕ)
    (hw : ∀ f, w.ord f * (γ : ℤ) = (ι f).order)
    (hw' : ∀ f, w.ord f * (γ' : ℤ) = (ι' f).order) :
    a = a' ∧ Nat.ModEq (Nat.gcd a (N / a)) b b' := by
  obtain ⟨d, rfl⟩ := ha
  have ha0 : 0 < a := Nat.pos_of_ne_zero (NeZero.ne a)
  have had : a * d / a = d := Nat.mul_div_cancel_left d ha0
  rw [had]
  have hζu : IsPrimitiveRoot ζ (a * d) := IsPrimitiveRoot.coe_units_iff.mp hζ
  have h1 := hw (jOver (a * d) L)
  have h1' := hw' (jOver (a * d) L)
  rw [hj, laurent_order_TS] at h1
  rw [hj', laurent_order_TS] at h1'
  have hne : w.ord (jOver (a * d) L) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    exact NeZero.ne (a * d) (by exact_mod_cast (neg_eq_zero.mp h1.symm))
  have hγ : (γ : ℤ) = γ' := mul_left_cancel₀ hne (h1.trans h1'.symm)
  have h2 := hw (jNOver (a * d) L)
  have h2' := hw' (jNOver (a * d) L)
  rw [hjN, slotValue_eq, laurent_order_TS] at h2
  rw [hjN', slotValue_eq, laurent_order_TS, ← hγ] at h2'
  have haa : a * a = a' * a' := by exact_mod_cast neg_injective (h2.symm.trans h2')
  obtain rfl : a = a' := Nat.mul_self_inj.mp haa
  refine ⟨rfl, ?_⟩
  obtain ⟨m, hm⟩ := Nat.gcd_dvd_left a d
  obtain ⟨n, hn⟩ := Nat.gcd_dvd_right a d
  let g := Nat.gcd a d
  have hd0 : 0 < d := Nat.pos_of_ne_zero fun h => NeZero.ne (a * d) (by rw [h, mul_zero])
  have hn0 : 0 < n := Nat.pos_of_ne_zero fun h => hd0.ne' (by rw [hn, h, mul_zero])
  have key : a * a * n = a * d * m := by
    calc a * a * n = a * (g * m) * n := by rw [← hm]
      _ = a * (g * n) * m := by ring
      _ = a * d * m := by rw [← hn]
  let c : L := (((ζ ^ (b * a)) ^ (-(n : ℤ)) : Lˣ) : L)
  let x : modularFunctionFieldOver (a * d) L :=
    jNOver (a * d) L ^ n - algebraMap L _ c * jOver (a * d) L ^ m
  have hx : ι x = (TS L (a * a) (ζ ^ (b * a))) ^ n -
      algebraMap L (LaurentSeries L) c * (TS L (a * d) 1) ^ m := by
    dsimp only [x]
    rw [map_sub, map_mul, map_pow, map_pow, ι.commutes, hj, hjN, slotValue_eq]
  have hx' : ι' x = (TS L (a * a) (ζ ^ (b' * a))) ^ n -
      algebraMap L (LaurentSeries L) c * (TS L (a * d) 1) ^ m := by
    dsimp only [x]
    rw [map_sub, map_mul, map_pow, map_pow, ι'.commutes, hj', hjN', slotValue_eq]
  obtain ⟨hS, _⟩ := cusp_coeff_TS_pow (ζ ^ (b * a)) (a * a) n
  obtain ⟨hS', hlow'⟩ := cusp_coeff_TS_pow (ζ ^ (b' * a)) (a * a) n
  obtain ⟨hE, hlowE⟩ := cusp_coeff_TS_one_pow (K := L) (a * d) m
  rw [← key] at hE hlowE
  have hcx : (ι x).coeff (-((a * a * n : ℕ) : ℤ)) = 0 := by
    rw [hx, HahnSeries.coeff_sub, hS, cusp_coeff_algebraMap_mul, hE, mul_one, sub_self]
  have hlower : ∀ i < -((a * a * n : ℕ) : ℤ), (ι' x).coeff i = 0 := by
    intro i hi
    rw [hx', HahnSeries.coeff_sub, hlow' i hi, cusp_coeff_algebraMap_mul,
      hlowE i hi, mul_zero, sub_zero]
  have hcx' : (ι' x).coeff (-((a * a * n : ℕ) : ℤ)) =
      (((ζ ^ (b' * a)) ^ (-(n : ℤ)) : Lˣ) : L) - c := by
    rw [hx', HahnSeries.coeff_sub, hS', cusp_coeff_algebraMap_mul, hE, mul_one]
  have horder : (ι' x).order = (ι x).order := by rw [← hw', ← hw, hγ]
  have hM : (0 : ℤ) < ((a * a * n : ℕ) : ℤ) := by
    exact_mod_cast Nat.mul_pos (Nat.mul_pos ha0 ha0) hn0
  have hv : (ι' x).coeff (-((a * a * n : ℕ) : ℤ)) = 0 := by
    by_cases hz : ι' x = 0
    · rw [hz, HahnSeries.coeff_zero]
    apply HahnSeries.coeff_eq_zero_of_lt_order
    refine lt_of_le_of_ne ?_ ?_
    · by_contra! hlt
      exact hz (HahnSeries.coeff_order_eq_zero.mp (hlower _ hlt))
    · intro he
      rw [horder] at he
      by_cases hz0 : ι x = 0
      · rw [hz0, HahnSeries.order_zero] at he
        exact hM.ne' (neg_eq_zero.mp he)
      · apply hz0
        apply HahnSeries.coeff_order_eq_zero.mp
        rw [← he]
        exact hcx
  rw [hcx', sub_eq_zero] at hv
  have hu : (ζ ^ (b' * a)) ^ (-(n : ℤ)) = (ζ ^ (b * a)) ^ (-(n : ℤ)) := Units.ext hv
  rw [zpow_neg, zpow_neg, inv_inj, zpow_natCast, zpow_natCast, ← pow_mul, ← pow_mul,
    pow_eq_pow_iff_modEq, ← hζu.eq_orderOf,
    show a * d = g * (a * n) by rw [hn]; ring, mul_assoc, mul_assoc] at hu
  exact (Nat.ModEq.mul_right_cancel' (Nat.mul_pos ha0 hn0).ne' hu).symm

end
end Dubon2026.SourceFunctionField
