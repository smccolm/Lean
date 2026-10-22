import Dubon2026.SourceOriginalDissectionVertexCount

/-! DUB-17/18 -> original Abel-Jacobi -> the cell term of the Euler identity.
The finite grid has exactly two branch squares, identified bijectively with
the actual branch values. The remaining square count is therefore the full
window count minus two. No generic cell-count framework is introduced.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.OriginalJFiniteGrid
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {Marked : Finset ℂ} (G : OriginalJFiniteGrid N Marked)

/-- Exact identification of the two branch values with the nonordinary grid squares. -/
def branchSquareEquiv : ({0, 1728} : Finset ℂ) ≃ {p : G.squares // G.D.capAt p ≠ none} := by
  let f : ({0, 1728} : Finset ℂ) → {p : G.squares // G.D.capAt p ≠ none} :=
    fun b => ⟨⟨G.branchSquare b, G.branchSquare_mem b⟩, by rw [G.branch_cap b]; simp⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro b c he
    have hp : G.branchSquare b = G.branchSquare c := congrArg (fun p => p.1.1) he
    apply Subtype.ext
    apply Option.some.inj
    exact (G.branch_cap b).symm.trans ((congrArg G.D.capAt hp).trans (G.branch_cap c))
  · intro p
    cases hc : G.D.capAt p.1 with
    | none => exact False.elim (p.2 hc)
    | some b =>
      obtain ⟨hb, hx, hy⟩ := (G.D.cap_exact p.1 b).mp hc
      refine ⟨⟨b, hb⟩, Subtype.ext (Subtype.ext ?_)⟩
      exact Prod.ext hx hy

theorem squares_card : G.squares.card = (G.D.hi - G.D.lo + 1).toNat ^ 2 := by
  have h : (Finset.Icc G.D.lo G.D.hi).card = (G.D.hi - G.D.lo + 1).toNat := by
    rw [Int.card_Icc]
    omega
  change ((Finset.Icc G.D.lo G.D.hi) ×ˢ (Finset.Icc G.D.lo G.D.hi)).card = _
  rw [Finset.card_product, h, pow_two]

theorem plain_card_add_two : Fintype.card G.PlainIndex + 2 = (G.D.hi - G.D.lo + 1).toNat ^ 2 := by
  classical
  have hc : Fintype.card {p : G.squares // G.D.capAt p ≠ none} = 2 := by
    rw [← Fintype.card_congr G.branchSquareEquiv, Fintype.card_coe]
    norm_num
  have ht := Fintype.card_subtype_compl (fun p : G.squares => G.D.capAt p = none)
  have hle := Fintype.card_subtype_le (fun p : G.squares => G.D.capAt p = none)
  rw [hc, Fintype.card_coe, G.squares_card] at ht
  rw [Fintype.card_coe, G.squares_card] at hle
  change Fintype.card {p : G.squares // G.D.capAt p = none} + 2 = _
  omega

end
end Dubon2026.SourceFunctionField.CellGeometry.OriginalJFiniteGrid
