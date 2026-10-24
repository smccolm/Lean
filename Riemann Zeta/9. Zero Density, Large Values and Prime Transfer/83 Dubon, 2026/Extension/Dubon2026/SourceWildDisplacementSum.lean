import Dubon2026.SourceResidueUnitKernelSize

/-! The exact finite sum in the wild different estimate for DUB-17/18.
Every nonidentity inertia element contributes at least one; elements in
the residue-character kernel contribute at least two. The additional
p-primary contribution follows from the proved residue-unit kernel size.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_Place_sub_one_add_pow_sub_one_le_ordDiff_D_of_isGalois,
hcount. Geometric displacement bounds remain explicit inputs here. -/
namespace Dubon2026.SourceCurve
noncomputable section
variable {G H : Type*} [Group G] [Fintype G] [DecidableEq G] [Group H]

theorem displacement_sum_ge_card_add_kernel (χ : G →* H) (i : G → ℤ)
    (hbase : ∀ σ ≠ 1, 1 ≤ i σ)
    (hwild : ∀ σ ≠ 1, σ ∈ χ.ker → 2 ≤ i σ) :
    (Nat.card G : ℤ) - 1 + ((Nat.card χ.ker : ℤ) - 1) ≤
      ∑ σ ∈ Finset.univ.erase (1 : G), i σ := by
  classical
  letI : Fintype χ.ker := Fintype.ofFinite _
  have hpt : ∀ σ ∈ Finset.univ.erase (1 : G),
      (1 : ℤ) + (if σ ∈ χ.ker then 1 else 0) ≤ i σ := by
    intro σ hσ
    have hn := (Finset.mem_erase.mp hσ).1
    split_ifs with hk
    · exact hwild σ hn hk
    · simpa only [add_zero] using hbase σ hn
  have hfk : (Finset.univ.filter fun σ : G => σ ∈ χ.ker).card =
      Fintype.card χ.ker := by
    rw [← Fintype.card_subtype]
  have hsum : ∑ σ ∈ Finset.univ.erase (1 : G),
      ((1 : ℤ) + (if σ ∈ χ.ker then 1 else 0)) =
      (Nat.card G : ℤ) - 1 + ((Nat.card χ.ker : ℤ) - 1) := by
    rw [Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Finset.sum_boole, Finset.filter_erase,
      Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, χ.ker.one_mem⟩),
      hfk, nsmul_eq_mul, Nat.cast_sub Fintype.card_pos,
      Nat.cast_sub Fintype.card_pos, Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card]
    push_cast
    ring
  rw [← hsum]
  exact Finset.sum_le_sum hpt

theorem displacement_sum_ge_wild_power {K : Type*} [Field K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (χ : G →* Kˣ)
    (a : ℕ) (ha : p ^ a ∣ Nat.card G) (i : G → ℤ)
    (hbase : ∀ σ ≠ 1, 1 ≤ i σ)
    (hwild : ∀ σ ≠ 1, σ ∈ χ.ker → 2 ≤ i σ) :
    (Nat.card G : ℤ) - 1 + ((p : ℤ) ^ a - 1) ≤
      ∑ σ ∈ Finset.univ.erase (1 : G), i σ := by
  have hker : (p : ℤ) ^ a ≤ (Nat.card χ.ker : ℤ) := by
    exact_mod_cast residue_unit_character_kernel_pow_le p χ a ha
  exact le_trans (by omega) (displacement_sum_ge_card_add_kernel χ i hbase hwild)

end
end Dubon2026.SourceCurve
