import Dubon2026.SourceLaurentReindex
import Dubon2026.SourceModularJSeries
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.FieldTheory.Finite.Basic

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> exact
residue-field degree -> prime nonmembership -> eta-product obstruction.
Only the power-series Frobenius calculation needed for the actual integral
eta product is selected. Native Frobenius/expansion and the existing
Laurent reindex map avoid a separate general Laurent Frobenius development. -/
namespace Dubon2026.SourceFunctionField
noncomputable section

theorem qExpand_ofPowerSeries_eq_expand {R : Type*} [CommRing R]
    (p : ℕ) [NeZero p] (u : PowerSeries R) :
    qExpand R p (HahnSeries.ofPowerSeries ℤ R u) =
      HahnSeries.ofPowerSeries ℤ R (PowerSeries.expand p (NeZero.ne p) u) := by
  have hp0 : (0 : ℤ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  ext k
  by_cases hpk : (p : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hpk
    rw [qExpand_coeff_mul]
    rcases lt_or_ge m 0 with hm | hm
    · have hpm : (p : ℤ) * m < 0 := mul_neg_of_pos_of_neg hp0 hm
      rw [ofPowerSeries_coeff_of_neg _ hm, ofPowerSeries_coeff_of_neg _ hpm]
    · lift m to ℕ using hm with m
      have hcast : ((p : ℤ) * (m : ℤ)) = ((p * m : ℕ) : ℤ) := by push_cast; ring
      rw [HahnSeries.ofPowerSeries_apply_coeff, hcast, HahnSeries.ofPowerSeries_apply_coeff,
        PowerSeries.coeff_expand_mul]
  · rw [qExpand_coeff_of_not_dvd p _ hpk]
    rcases lt_or_ge k 0 with hk | hk
    · exact (ofPowerSeries_coeff_of_neg _ hk).symm
    · lift k to ℕ using hk with k
      rw [HahnSeries.ofPowerSeries_apply_coeff,
        PowerSeries.coeff_expand_of_not_dvd p (NeZero.ne p) u
          (fun ⟨m, hm⟩ => hpk ⟨m, by exact_mod_cast hm⟩)]

theorem integral_powerSeries_pow_char (K : Type*) [CommRing K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (u : PowerSeries ℤ) :
    (u.map (Int.castRingHom K)) ^ p =
      PowerSeries.expand p (NeZero.ne p) (u.map (Int.castRingHom K)) := by
  haveI : ExpChar K p := ExpChar.prime (Fact.out : p.Prime)
  have hfix : (u.map (Int.castRingHom K)).map (frobenius K p) = u.map (Int.castRingHom K) := by
    have he : (frobenius K p).comp (Int.castRingHom K) = Int.castRingHom K := RingHom.ext_int _ _
    ext n
    simp only [PowerSeries.coeff_map]
    exact congrArg (fun f : ℤ →+* K => f (PowerSeries.coeff n u)) he
  have h := MvPowerSeries.map_frobenius_expand p (NeZero.ne p) (f := u.map (Int.castRingHom K))
  change PowerSeries.map (frobenius K p)
    (PowerSeries.expand p (NeZero.ne p) (u.map (Int.castRingHom K))) = _ at h
  rw [PowerSeries.map_expand, hfix] at h
  exact h.symm

theorem integral_ofPowerSeries_pow_char (K : Type*) [CommRing K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (u : PowerSeries ℤ) :
    (HahnSeries.ofPowerSeries ℤ K (u.map (Int.castRingHom K))) ^ p =
      qExpand K p (HahnSeries.ofPowerSeries ℤ K (u.map (Int.castRingHom K))) := by
  rw [← map_pow, integral_powerSeries_pow_char, qExpand_ofPowerSeries_eq_expand]

end
end Dubon2026.SourceFunctionField
