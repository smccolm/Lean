import Dubon2026.SourceOriginalCycleIntegralSums

/-! DUB-17/18 -> original Abel-Jacobi -> jump-to-period formula.
Apply the exact word-jump formula to the proved integer subword cycles.
Their fundamental-cycle expansion produces an integer matrix on the exact
2g complementary edges. The analytic word identity is consumed directly;
no further primitive or normalization assumptions are introduced here.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.DissectionPeriods
noncomputable section
variable {N : ℕ} [NeZero N] {κ : Type*} {D : CellDissection N}

/-- The exact integer coefficient of an edge in the source subword; dual-tree rows are zero. -/
noncomputable def wordMatrix {Ts : Finset D.ιE} {m : ℕ} [NeZero m]
    (wd : ZMod m ≃ {q : D.ιE × Bool // q.1 ∉ Ts}) (j l : D.ιE) : ℤ :=
  if hj : j ∉ Ts then wordChain wd j hj l else 0

theorem wordMatrix_of_not_mem {Ts : Finset D.ιE} {m : ℕ} [NeZero m]
    (wd : ZMod m ≃ {q : D.ιE × Bool // q.1 ∉ Ts}) {j : D.ιE} (hj : j ∉ Ts) (l : D.ιE) :
    wordMatrix wd j l = wordChain wd j hj l := by
  simp [wordMatrix, hj]

/-- The primitive jumps expressed by the actual cycle-integral vectors and an integer matrix. -/
def JumpFormula (T Ts : Finset D.ιE) (Z : D.ιE → D.ιE → ℤ) (I J : D.ιE → κ → ℂ)
    (P : D.ιE → D.ιE → ℤ) : Prop :=
  ∀ j ∉ Ts, J j = -∑ l ∈ (T ∪ Ts)ᶜ, (P j l : ℂ) • zv Z I l

theorem jump_formula_of_word (T Ts : Finset D.ιE) (Z : D.ιE → D.ιE → ℤ)
    (I J : D.ιE → κ → ℂ)
    (hZ : ∀ p : D.ιE → ℤ,
      (∀ w, (∑ e with (D.ends e).2 = w, p e) = ∑ e with (D.ends e).1 = w, p e) →
      ∀ e, p e = ∑ j ∈ Tᶜ, Z j e • p j)
    {m : ℕ} [NeZero m] (wd : ZMod m ≃ {q : D.ιE × Bool // q.1 ∉ Ts})
    (hcycle : ∀ e he w, (∑ f with (D.ends f).2 = w, wordChain wd e he f) =
      ∑ f with (D.ends f).1 = w, wordChain wd e he f)
    (hword : ∀ j hj,
      J j = -∑ i ∈ Finset.univ.filter
          (fun i : ZMod m => i ≠ wd.symm ⟨(j, true), hj⟩ ∧
            (i - wd.symm ⟨(j, true), hj⟩).val <
              (wd.symm ⟨(j, false), hj⟩ - wd.symm ⟨(j, true), hj⟩).val),
        (if (wd i).1.2 then (1 : ℂ) else -1) • I (wd i).1.1) :
    JumpFormula T Ts Z I J (wordMatrix wd) := by
  classical
  intro j hj
  rw [hword j hj, sum_word_eq_sum_wordChain wd j hj,
    sum_chain_smul hZ _ (hcycle j hj) I]
  congr 1
  rw [Finset.compl_union]
  have h0 : ∀ l ∈ Tᶜ, l ∉ Tᶜ ∩ Tsᶜ → (wordChain wd j hj l : ℂ) • zv Z I l = 0 := by
    intro l hl hl'
    have hls : l ∈ Ts := by
      by_contra h
      exact hl' (Finset.mem_inter.mpr ⟨hl, Finset.mem_compl.mpr h⟩)
    rw [wordChain_of_mem wd j hj hls, Int.cast_zero, zero_smul]
  rw [← Finset.sum_subset Finset.inter_subset_left h0]
  exact Finset.sum_congr rfl fun l _ => by rw [wordMatrix_of_not_mem wd hj]

end
end Dubon2026.SourceFunctionField.CellGeometry.DissectionPeriods
