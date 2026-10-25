import Dubon2026.SourceRadialWordPeriodMatrix

/-! DUB-17/18 -> original Abel-Jacobi -> period-matrix reciprocity.
Convert the weighted sum of actual edge jumps into a sum over the same
complementary integer cycles, then substitute the exact actual period rows.
Only the proved circulation decomposition and vanishing dual-tree jumps are
used; the next analytic consumer supplies the weighted residue identity.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.RadialDissectionPeriods
noncomputable section
variable {X : Type*} [TopologicalSpace X] {κ : Type*} {𝒟 : RadialCellDissection X}

/-- The scalar edge integral around the specified actual integer cycle. -/
def cycleScalarIntegral (Z : 𝒟.ιE → 𝒟.ιE → ℤ) (Iθ : 𝒟.ιE → ℂ) (j : 𝒟.ιE) : ℂ :=
  ∑ e, (Z j e : ℂ) * Iθ e

theorem sum_smul_eq_sum_cycle {𝒯 𝒯s : Finset 𝒟.ιE} {Z : 𝒟.ιE → 𝒟.ιE → ℤ}
    {J : 𝒟.ιE → κ → ℂ}
    (hdec : ∀ e, J e = ∑ l ∈ 𝒯ᶜ, Z l e • J l)
    (hJ0 : ∀ e ∈ 𝒯s, J e = 0) (Iθ : 𝒟.ιE → ℂ) :
    ∑ e, Iθ e • J e = ∑ j ∈ (𝒯 ∪ 𝒯s)ᶜ, cycleScalarIntegral Z Iθ j • J j := by
  classical
  have hvec : ∑ e, Iθ e • J e = ∑ l ∈ 𝒯ᶜ, cycleScalarIntegral Z Iθ l • J l := by
    calc ∑ e, Iθ e • J e = ∑ e, ∑ l ∈ 𝒯ᶜ, (Iθ e * Z l e) • J l := by
          refine Finset.sum_congr rfl fun e _ => ?_
          conv_lhs => rw [hdec e]
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [← Int.cast_smul_eq_zsmul ℂ, smul_smul]
      _ = ∑ l ∈ 𝒯ᶜ, ∑ e, (Iθ e * Z l e) • J l := Finset.sum_comm
      _ = ∑ l ∈ 𝒯ᶜ, cycleScalarIntegral Z Iθ l • J l := by
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [← Finset.sum_smul]
          congr 1
          simp only [cycleScalarIntegral]
          exact Finset.sum_congr rfl fun e _ => by ring
  rw [hvec, Finset.compl_union]
  refine (Finset.sum_subset Finset.inter_subset_left fun l hl hl' => ?_).symm
  have hls : l ∈ 𝒯s := by
    by_contra h
    exact hl' (Finset.mem_inter.2 ⟨hl, Finset.mem_compl.2 h⟩)
  rw [hJ0 l hls, smul_zero]

theorem sum_mul_jump_eq_cycle_bilinear {T Ts : Finset 𝒟.ιE}
    {Z : 𝒟.ιE → 𝒟.ιE → ℤ} {J : 𝒟.ιE → κ → ℂ}
    (hdec : ∀ e, J e = ∑ l ∈ Tᶜ, Z l e • J l) (hJ0 : ∀ e ∈ Ts, J e = 0)
    (z : 𝒟.ιE → κ → ℂ) (P : 𝒟.ιE → 𝒟.ιE → ℤ)
    (hrow : ∀ j ∉ Ts, J j = -∑ l ∈ (T ∪ Ts)ᶜ, (P j l : ℂ) • z l)
    (Iθ : 𝒟.ιE → ℂ) (i : κ) :
    ∑ e, Iθ e * J e i =
      -∑ j ∈ (T ∪ Ts)ᶜ, ∑ l ∈ (T ∪ Ts)ᶜ,
        cycleScalarIntegral Z Iθ j * (P j l : ℂ) * z l i := by
  classical
  have hvec := congrFun (sum_smul_eq_sum_cycle hdec hJ0 Iθ) i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hvec
  rw [hvec, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ∉ Ts := fun h => (Finset.mem_compl.mp hj) (Finset.mem_union_right T h)
  have hJj := congrFun (hrow j hj') i
  simp only [Pi.neg_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hJj
  rw [hJj, mul_neg, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun l _ => by ring

end
end Dubon2026.SourceFunctionField.CellGeometry.RadialDissectionPeriods
