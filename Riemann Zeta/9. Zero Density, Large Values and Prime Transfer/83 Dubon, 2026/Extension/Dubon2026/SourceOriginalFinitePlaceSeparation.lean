import Dubon2026.SourceCurveOrderUnitPerturbation
import Dubon2026.SourceOriginalPlaceSeparation

/-! DUB-17/18 -> full original Picard-period Hecke compatibility ->
moving every divisor class away from the cusps -> finite prescribed orders.
Adapted from S_AlgebraicCurve_Place_exists_forall_ord_eq,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
Existing actual place separation, uniformizers and valuation/order identities
supply the foundations. No global approximation hypothesis is introduced.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
variable (N : ℕ) [NeZero N]

theorem exists_original_polar_regular_separator (T : Finset (Place ℂ (modularFunctionFieldOver N ℂ))) {v : Place ℂ (modularFunctionFieldOver N ℂ)}
    (hv : v ∉ T) :
    ∃ z : modularFunctionFieldOver N ℂ, v.ord z < 0 ∧ ∀ w ∈ T, 0 < w.ord z := by
  classical
  revert hv
  induction T using Finset.induction_on with
  | empty =>
      intro _
      refine ⟨v.uniformizer⁻¹, ?_, by simp⟩
      rw [v.ord_inv, v.ord_uniformizer]
      omega
  | @insert w₀ s hw₀s ih =>
      intro hv
      have hvw₀ : v ≠ w₀ := fun h => hv (h ▸ Finset.mem_insert_self w₀ s)
      have hvs : v ∉ s := fun h => hv (Finset.mem_insert_of_mem h)
      obtain ⟨z, hzv, hzs⟩ := ih hvs
      obtain ⟨u, _, huw₀, huv⟩ := original_places_separating_function N w₀ v hvw₀.symm
      have hz0 : z ≠ 0 := fun h => by simp [h] at hzv
      have hu0 : u ≠ 0 := fun h => by simp [h] at huv
      set m : ℕ := (s.sup fun w => (1 - w.ord u).toNat) + 1 with hmdef
      have hm1 : 1 ≤ m := Nat.le_add_left 1 _
      have hmw : ∀ w ∈ s, 1 ≤ (m : ℤ) + w.ord u := by
        intro w hw
        have h1 : (1 - w.ord u).toNat ≤ s.sup fun w => (1 - w.ord u).toNat :=
          Finset.le_sup (f := fun w => (1 - w.ord u).toNat) hw
        omega
      rcases lt_trichotomy (w₀.ord z) 0 with hc | hc | hc
      ·
        have ht0 : (z ^ (m : ℤ)) ≠ 0 := zpow_ne_zero _ hz0
        have htv : v.ord (z ^ (m : ℤ)) < 0 := by
          rw [v.ord_zpow]
          exact mul_neg_of_pos_of_neg (by omega) hzv
        have htw₀ : w₀.ord (z ^ (m : ℤ)) < 0 := by
          rw [w₀.ord_zpow]
          exact mul_neg_of_pos_of_neg (by omega) hc
        obtain ⟨hne, heqv⟩ := v.one_add_ne_zero_and_ord_eq_of_ord_neg htv
        have heqw₀ := (w₀.one_add_ne_zero_and_ord_eq_of_ord_neg htw₀).2
        refine ⟨z ^ (m : ℤ) * (1 + z ^ (m : ℤ))⁻¹ * u, ?_, ?_⟩
        · rw [v.ord_mul (mul_ne_zero ht0 (inv_ne_zero hne)) hu0,
            v.ord_mul ht0 (inv_ne_zero hne), v.ord_inv, heqv]
          omega
        · intro w hw
          rcases Finset.mem_insert.mp hw with h | hws
          · rw [h, w₀.ord_mul (mul_ne_zero ht0 (inv_ne_zero hne)) hu0,
              w₀.ord_mul ht0 (inv_ne_zero hne), w₀.ord_inv, heqw₀]
            omega
          · have hwz := hzs w hws
            have htw : 0 < w.ord (z ^ (m : ℤ)) := by
              rw [w.ord_zpow]
              exact mul_pos (by omega) hwz
            have h1t := w.ord_one_add_of_ord_pos htw
            rw [w.ord_mul (mul_ne_zero ht0 (inv_ne_zero hne)) hu0,
              w.ord_mul ht0 (inv_ne_zero hne), w.ord_inv, h1t, w.ord_zpow]
            have hb : (m : ℤ) * 1 ≤ (m : ℤ) * w.ord z :=
              mul_le_mul_of_nonneg_left (by omega) (by omega)
            have h2 := hmw w hws
            omega
      ·
        have ht0 : (z ^ (m : ℤ)) ≠ 0 := zpow_ne_zero _ hz0
        refine ⟨z ^ (m : ℤ) * u, ?_, ?_⟩
        · rw [v.ord_mul ht0 hu0, v.ord_zpow]
          have hb : (m : ℤ) * v.ord z ≤ (m : ℤ) * (-1) :=
            mul_le_mul_of_nonneg_left (by omega) (by omega)
          omega
        · intro w hw
          rcases Finset.mem_insert.mp hw with h | hws
          · rw [h, w₀.ord_mul ht0 hu0, w₀.ord_zpow, hc]
            omega
          · rw [w.ord_mul ht0 hu0, w.ord_zpow]
            have h1 := hzs w hws
            have hb : (m : ℤ) * 1 ≤ (m : ℤ) * w.ord z :=
              mul_le_mul_of_nonneg_left (by omega) (by omega)
            have h2 := hmw w hws
            omega
      ·
        exact ⟨z, hzv, fun w hw =>
          (Finset.mem_insert.mp hw).elim (fun h => h ▸ hc) (hzs w)⟩

end
end Dubon2026.SourceFunctionField
