import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-! A finite tame presentation and the proved inertia exponent identify
the kernel of the fixed cyclic tame quotient. This is the kernel condition
needed to descend the actual auxiliary deformation characters, on the
local-ring dependency chain for Dubon Theorem 2.6. -/

namespace Dubon2026

/-- If a tame generator surjects onto the fixed cyclic quotient and its
representation value has the quotient exponent, that quotient's inertia
kernel is killed by the representation. Both maps kill the same wild group. -/
theorem tame_cyclic_quotient_kernel
    {G H D : Type*} [Group G] [Group H] [Group D] [Finite D]
    (I W : Subgroup G) [W.Normal] (t : G)
    (hgen : I = W ⊔ Subgroup.zpowers t)
    (ρ : G →* H) (π : G →* D)
    (hWρ : W ≤ ρ.ker) (hWπ : W ≤ π.ker)
    (hπ : I.map π = ⊤) (ht : ρ t ^ Nat.card D = 1) :
    I ⊓ π.ker ≤ ρ.ker := by
  have hπt : Subgroup.zpowers (π t) = ⊤ := by
    simpa only [hgen, Subgroup.map_sup, (Subgroup.map_eq_bot_iff W).mpr hWπ,
      bot_sup_eq, π.map_zpowers] using hπ
  have hord : orderOf (π t) = Nat.card D := orderOf_eq_card_of_zpowers_eq_top hπt
  intro g hg
  obtain ⟨w, hw, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp (hgen ▸ hg.1)
  obtain ⟨n, rfl⟩ := hz
  have hπw : π w = 1 := hWπ hw
  have hρw : ρ w = 1 := hWρ hw
  have hπn : π t ^ n = 1 := by
    have h := hg.2
    change π (w * t ^ n) = 1 at h
    simpa only [map_mul, map_zpow, hπw, one_mul] using h
  have hn : (Nat.card D : ℤ) ∣ n := by
    rw [← hord]
    exact orderOf_dvd_iff_zpow_eq_one.mpr hπn
  obtain ⟨k, rfl⟩ := hn
  change ρ (w * t ^ ((Nat.card D : ℤ) * k)) = 1
  rw [map_mul, hρw, one_mul, map_zpow, zpow_mul, zpow_natCast, ht, one_zpow]

end Dubon2026
