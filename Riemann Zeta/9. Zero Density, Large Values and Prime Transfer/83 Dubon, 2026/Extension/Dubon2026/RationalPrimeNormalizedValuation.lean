import Dubon2026.RationalPrimeOriginalUniformizer

/-! # Original rational prime orders agree with the original adic valuation

Use the actual prime uniformizer and the existing original integer-unit
factorization to identify the normalized order with the adic valuation log.
This is the normalization bridge required for the finite rational prime
product in DUB-17's cyclotomic principal-product and arithmetic sum-zero chain.
-/
namespace Dubon2026
noncomputable section
open IsDedekindDomain.HeightOneSpectrum
open scoped ValuativeRel WithZero

/-- The actual adic valuation of its original rational prime is exp(-1). -/
theorem rationalPrimeLocalField_adic_prime (p : ℕ) (hp : p.Prime) :
    Valued.v (R := rationalPrimeLocalField p hp) (Γ₀ := ℤᵐ⁰) (p : rationalPrimeLocalField p hp) =
      WithZero.exp (-1 : ℤ) := by
  let v := rationalPrimePlace p hp
  rw [← map_natCast (algebraMap ℚ (rationalPrimeLocalField p hp)) p,
    algebraMap_adicCompletion, Function.comp_apply, Algebra.algebraMap_self_apply,
    valuedAdicCompletion_eq_valuation']
  change v.valuation ℚ (algebraMap ℤ ℚ (p : ℤ)) = _
  rw [valuation_of_algebraMap]
  apply v.intValuation_singleton (by exact_mod_cast hp.ne_zero)
  ext z
  rw [Ideal.mem_span_singleton, rationalPrimePlace_int_mem_iff]

/-- The original normalized integer order exactly recovers the actual adic valuation of every nonzero element. -/
theorem rationalPrimeLocalField_adic_eq_exp_order (p : ℕ) (hp : p.Prime)
    (u : (rationalPrimeLocalField p hp)ˣ) :
    Valued.v (R := rationalPrimeLocalField p hp) (Γ₀ := ℤᵐ⁰) u.val =
      WithZero.exp (-localFieldUnitOrder (rationalPrimeLocalField p hp) (Additive.ofMul u)) := by
  obtain ⟨a, ha⟩ := localFieldUnit_eq_integer_unit_mul_order_power (rationalPrimeLocalField p hp)
    (p : 𝒪[(rationalPrimeLocalField p hp)]) (rationalPrimeValuationInteger_irreducible_prime p hp) u
  have hz := (localFieldUnitOrder_eq_zero_iff_integer_unit (rationalPrimeLocalField p hp)
    (Units.map (algebraMap 𝒪[(rationalPrimeLocalField p hp)] (rationalPrimeLocalField p hp)).toMonoidHom a)).mpr ⟨a, rfl⟩
  have hva := (localFieldUnitOrder_eq_zero_iff (rationalPrimeLocalField p hp) _).mp hz
  have hva' := (ValuativeRel.isEquiv (ValuativeRel.valuation (rationalPrimeLocalField p hp))
    (Valued.v (R := rationalPrimeLocalField p hp) (Γ₀ := ℤᵐ⁰))).eq_one_iff_eq_one.mp hva
  simp only [Units.coe_map] at hva'
  have he := congrArg (fun x : (rationalPrimeLocalField p hp)ˣ => Valued.v (R := (rationalPrimeLocalField p hp)) (Γ₀ := ℤᵐ⁰) x.val) ha
  dsimp only at he
  simp only [Units.val_mul, Units.coe_map, Units.val_zpow_eq_zpow_val,
    Units.val_mk0, map_natCast] at he
  rw [map_mul, hva', one_mul, map_zpow₀, rationalPrimeLocalField_adic_prime,
    ← WithZero.exp_zsmul, zsmul_eq_mul, mul_neg_one] at he
  exact he

/-- Original rational restriction of the normalized local order is minus the logarithm of its actual rational finite-place valuation. -/
theorem rationalPrimeLocalField_rational_order (p : ℕ) (hp : p.Prime) (u : ℚˣ) :
    localFieldUnitOrder (rationalPrimeLocalField p hp)
      (Additive.ofMul (Units.map (algebraMap ℚ (rationalPrimeLocalField p hp)).toMonoidHom u)) =
        -WithZero.log ((rationalPrimePlace p hp).valuation ℚ u.val) := by
  have h := rationalPrimeLocalField_adic_eq_exp_order p hp
    (Units.map (algebraMap ℚ (rationalPrimeLocalField p hp)).toMonoidHom u)
  have hl := congrArg (fun x : ℤᵐ⁰ => -WithZero.log x) h
  dsimp only at hl
  rw [WithZero.log_exp, neg_neg] at hl
  rw [← hl]
  congr 2
  change Valued.v (algebraMap ℚ (rationalPrimeLocalField p hp) u.val) = _
  rw [algebraMap_adicCompletion, Function.comp_apply, Algebra.algebraMap_self_apply,
    valuedAdicCompletion_eq_valuation']

end
end Dubon2026
