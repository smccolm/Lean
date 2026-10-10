import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.FieldTheory.Galois.Infinite

/-! # Actual Hilbert-90 radicals for original finite Galois characters -/

namespace Dubon2026

noncomputable section

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- Every original base-field unit is fixed under the actual Galois action on extension-field units. -/
theorem galois_base_unit_fixed (g : Gal(L/K)) (u : Kˣ) :
    g • Units.map (algebraMap K L).toMonoidHom u =
      Units.map (algebraMap K L).toMonoidHom u := by
  apply Units.ext
  change g (algebraMap K L u.val) = algebraMap K L u.val
  exact g.commutes u.val

/-- Hilbert 90 gives a genuine extension-field unit whose original Galois ratios realize each original base-unit-valued character. -/
theorem finiteGaloisCharacter_exists_unit [FiniteDimensional K L]
    (χ : Gal(L/K) →* Kˣ) :
    ∃ β : Lˣ, ∀ g : Gal(L/K),
      g • β / β = Units.map (algebraMap K L).toMonoidHom (χ g) := by
  let f := (Units.map (algebraMap K L).toMonoidHom).comp χ
  have hf : groupCohomology.IsMulCocycle₁ f := by
    intro g h
    simp only [f, MonoidHom.comp_apply, map_mul, galois_base_unit_fixed, mul_comm]
  exact groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units f hf

/-- Every original finite Galois character killed by n has an actual radical with its nth power in the original base field and the exact original character ratios. -/
theorem finiteGaloisCharacter_exists_radical [FiniteDimensional K L] [IsGalois K L]
    (χ : Gal(L/K) →* Kˣ) (n : ℕ) (hχ : ∀ g : Gal(L/K), χ g ^ n = 1) :
    ∃ (a : Kˣ) (β : Lˣ),
      β ^ n = Units.map (algebraMap K L).toMonoidHom a ∧
      ∀ g : Gal(L/K), g • β / β = Units.map (algebraMap K L).toMonoidHom (χ g) := by
  obtain ⟨β, hβ⟩ := finiteGaloisCharacter_exists_unit χ
  have hfixed : ∀ g : Gal(L/K), g ((β : L) ^ n) = (β : L) ^ n := by
    intro g
    have h := congrArg (fun z : Lˣ => z ^ n) (hβ g)
    dsimp only at h
    rw [div_pow, ← map_pow, hχ g, map_one] at h
    have heq := div_eq_one.mp h
    have hval := congrArg Units.val heq
    simpa only [Units.val_pow_eq_pow_val, AlgEquiv.smul_units_def,
      Units.coe_map, MonoidHom.coe_coe, map_pow] using hval
  obtain ⟨a, ha⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed ((β : L) ^ n)).mpr hfixed
  have ha0 : a ≠ 0 := by
    intro hzero
    have hpower : (β : L) ^ n = 0 := by simpa only [hzero, map_zero] using ha.symm
    exact pow_ne_zero n β.ne_zero hpower
  refine ⟨Units.mk0 a ha0, β, ?_, hβ⟩
  apply Units.ext
  exact ha.symm

end
end Dubon2026
