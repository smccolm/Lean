import Dubon2026.SourceOriginalConstructedCycleLoops

/-! DUB-17/18 -> original Abel-Jacobi -> raw reciprocity.
The actual dual tree uniquely transports primitive constants between cells.
Its integer chains kill every dual-tree jump and fix one prescribed root value.
Reuse the existing boundary algebra in place of the source's repeated sums.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set IntegerEdgeChains DissectionTrees
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {κ : Type*}

theorem CellDissection.exists_normalising_constants (D : CellDissection N) (Ts : Finset D.ιE)
    (hTs : IsTree (fun e => Cside D e true) (fun e => Cside D e false) Ts)
    (J : D.ιE → κ → ℂ) (C₀ : D.ιC) (a₀ : κ → ℂ) :
    ∃ c : D.ιC → κ → ℂ, c C₀ = -a₀ ∧
      ∀ e ∈ Ts, J e + c (Cside D e true) - c (Cside D e false) = 0 := by
  classical
  choose ch hch huniq using fun C => hTs C₀ C
  refine ⟨fun C => -(∑ e, (ch C e : ℂ) • J e) - a₀, ?_, ?_⟩
  · have h0 : ch C₀ = 0 := (huniq C₀ 0 ⟨fun _ _ => rfl, fun w => by simp [bd]⟩).symm
    simp [h0]
  · intro e he
    have hkey : ch (Cside D e true) =
        fun f => ch (Cside D e false) f + if f = e then 1 else 0 := by
      apply (huniq (Cside D e true) _ ?_).symm
      constructor
      · intro f hf
        rw [(hch (Cside D e false)).1 f hf,
          if_neg (fun h : f = e => hf (by rw [h]; exact he)), add_zero]
      · intro w
        change bd _ _ (ch (Cside D e false) + (fun f => if f = e then 1 else 0)) w = _
        rw [bd_add, (hch (Cside D e false)).2 w, bd_single]
        ring
    have hsum : ∑ f, (ch (Cside D e true) f : ℂ) • J f =
        (∑ f, (ch (Cside D e false) f : ℂ) • J f) + J e := by
      rw [hkey]
      have hs : ∀ f, ((ch (Cside D e false) f + if f = e then (1 : ℤ) else 0 : ℤ) : ℂ) • J f =
          (ch (Cside D e false) f : ℂ) • J f + if f = e then J f else 0 := by
        intro f; split_ifs <;> push_cast <;> simp [add_smul]
      simp only [hs, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    change J e + (-(∑ f, (ch (Cside D e true) f : ℂ) • J f) - a₀) -
      (-(∑ f, (ch (Cside D e false) f : ℂ) • J f) - a₀) = 0
    rw [hsum]
    abel

end
end Dubon2026.SourceFunctionField.CellGeometry
