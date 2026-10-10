import Dubon2026.EmptySelmerClassMap

/-! # The actual unit-image kernel of the original Selmer ideal-class map -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain
open scoped nonZeroDivisors

variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- An original base-ring unit generates the identity fractional ideal in the actual fraction field. -/
theorem principalIdeal_of_base_unit (u : Rˣ) :
    toPrincipalIdeal R K (Units.map (algebraMap R K).toMonoidHom u) = 1 := by
  apply Units.ext
  simp only [coe_toPrincipalIdeal, Units.val_one, Units.coe_map,
    RingHom.toMonoidHom_eq_coe]
  change FractionalIdeal.spanSingleton R⁰ (algebraMap R K u.val) = 1
  rw [← FractionalIdeal.spanSingleton_one]
  symm
  apply FractionalIdeal.spanSingleton_eq_spanSingleton.mpr
  exact ⟨u, by simp only [Units.smul_def, Algebra.smul_def, mul_one]⟩

/-- Every original ordinary unit has trivial image under the actual Selmer ideal-class map. -/
theorem emptySelmerClassMap_fromUnit (n : ℕ) (hn : n ≠ 0) (u : Rˣ) :
    emptySelmerClassMap (R := R) (K := K) n hn
      (IsDedekindDomain.selmerGroup.fromUnit (R := R) (K := K) (n := n) u) = 1 := by
  let x : EmptySelmerRepresentativeUnits (R := R) (K := K) n :=
    ⟨Units.map (algebraMap R K).toMonoidHom u,
      (IsDedekindDomain.selmerGroup.fromUnit (R := R) (K := K) (n := n) u).property⟩
  change emptySelmerClassMap n hn (emptySelmerRepresentativeProjection n x) = 1
  rw [emptySelmerClassMap_apply_representative]
  have hroot : emptySelmerRepresentativeIdealRoot n x = 1 := by
    apply fractionalIdealUnits_pow_injective n hn
    dsimp only
    rw [emptySelmerRepresentativeIdealRoot_pow, one_pow]
    exact principalIdeal_of_base_unit u
  change QuotientGroup.mk' (toPrincipalIdeal R K).range
    (emptySelmerRepresentativeIdealRoot n x) = 1
  rw [hroot, map_one]

/-- Every genuine original Selmer class with trivial ideal-root class comes from an original ordinary unit. -/
theorem emptySelmerClassMap_kernel_le_unitRange (n : ℕ) (hn : n ≠ 0) :
    (emptySelmerClassMap (R := R) (K := K) n hn).ker ≤
      (IsDedekindDomain.selmerGroup.fromUnit (R := R) (K := K) (n := n)).range := by
  intro z hz
  obtain ⟨x, rfl⟩ := emptySelmerRepresentativeProjection_surjective n z
  change emptySelmerClassMap n hn (emptySelmerRepresentativeProjection n x) = 1 at hz
  rw [emptySelmerClassMap_apply_representative] at hz
  change QuotientGroup.mk' (toPrincipalIdeal R K).range
    (emptySelmerRepresentativeIdealRoot n x) = 1 at hz
  obtain ⟨y, hy⟩ := (QuotientGroup.eq_one_iff _).mp hz
  have hprincipal : toPrincipalIdeal R K (y ^ n) = toPrincipalIdeal R K x.val := by
    rw [map_pow, hy, emptySelmerRepresentativeIdealRoot_pow]
  have hspan := congrArg Units.val hprincipal
  simp only [coe_toPrincipalIdeal] at hspan
  obtain ⟨u, hu⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.mp hspan
  have hunit : Units.map (algebraMap R K).toMonoidHom u * y ^ n = x.val := by
    apply Units.ext
    simpa only [Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe,
      Units.smul_def, Algebra.smul_def] using hu
  let q := QuotientGroup.mk' (powMonoidHom (α := Kˣ) n).range
  have hpower : q (y ^ n) = 1 :=
    (QuotientGroup.eq_one_iff (y ^ n)).mpr ⟨y, rfl⟩
  have hq : q (Units.map (algebraMap R K).toMonoidHom u) = q x.val := by
    rw [← hunit, map_mul, hpower]
    exact (mul_one (q (Units.map (algebraMap R K).toMonoidHom u))).symm
  exact ⟨u, Subtype.ext hq⟩

/-- The actual Selmer ideal-class kernel is exactly the image of original ordinary units. -/
theorem emptySelmerClassMap_kernel_eq_unitRange (n : ℕ) (hn : n ≠ 0) :
    (emptySelmerClassMap (R := R) (K := K) n hn).ker =
      (IsDedekindDomain.selmerGroup.fromUnit (R := R) (K := K) (n := n)).range := by
  apply le_antisymm (emptySelmerClassMap_kernel_le_unitRange n hn)
  rintro _ ⟨u, rfl⟩
  exact emptySelmerClassMap_fromUnit n hn u

end
end Dubon2026
