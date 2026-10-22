import Dubon2026.SourceCellGridVertexRealization
import Dubon2026.SourceCellGridSquareToPerimeter
import Dubon2026.SourceCellGridIntersectionChains

/-! DUB-17/18 -> original Abel-Jacobi -> actual paired cell dissection.
Use the exact six-arc square and refined-window outputs to identify the two
regions sharing each side, its orientation and C1 reversal, and the finite
intersection chains at every boundary point. These are the planar inputs
to pairing the constructed original-curve cells and to their Euler count.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
The existing rectangle and outer-window constructors provide the geometric
data; no new radial-region existence hypothesis is introduced by consumers.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.GridGeometry
noncomputable section
open scoped Real
open Set

open PlanarRegions

/-- Full source planar pairing, intersection-chain and vertex-count conclusions. -/
def Geometry (M : GridData) : Prop :=
    ∃ (sqbit : ∀ p : ℤ × ℤ, Fin (M.base p).N → Bool) (perbit : Fin M.winReg.N → Bool) (B₀ : Finset ℂ)
      (Shares : Option (ℤ × ℤ) → Set ℂ → Prop) (Contains : Option (ℤ × ℤ) → ℂ → Prop),
      (∀ (p : ℤ × ℤ) (k k' : Fin (M.base p).N), (M.base p).arcSet k = (M.base p).arcSet k' → k = k') ∧
      (∀ p p' : ℤ × ℤ, p ≠ p' → ∀ (k : Fin (M.base p).N) (k' : Fin (M.base p').N),
        (M.base p).arcSet k = (M.base p').arcSet k' → sqbit p' k' = !sqbit p k) ∧
      (∀ (p : ℤ × ℤ) (k : Fin (M.base p).N) (k₀ : Fin M.winReg.N),
        p ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi → (M.base p).arcSet k = M.winReg.arcSet k₀ →
          perbit k₀ = !sqbit p k) ∧
      (∀ p p' : ℤ × ℤ, p ≠ p' → ∀ (k : Fin (M.base p).N) (k' : Fin (M.base p').N),
        (M.base p).arcSet k = (M.base p').arcSet k' → sqbit p k = true →
        ∃ ψ : ℝ → ℝ, StrictAntiOn ψ ((M.base p').arcIcc k') ∧ ContDiffOn ℝ 1 ψ ((M.base p').arcIcc k') ∧
          ψ ((M.base p').φs k'.castSucc) = (M.base p).φs k.succ ∧
          ψ ((M.base p').φs k'.succ) = (M.base p).φs k.castSucc ∧
          ∀ t ∈ (M.base p').arcIcc k', (M.base p').loop t = (M.base p).loop (ψ t)) ∧
      (∀ (p : ℤ × ℤ) (k : Fin (M.base p).N) (k₀ : Fin M.winReg.N),
        p ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi → (M.base p).arcSet k = M.winReg.arcSet k₀ → sqbit p k = true →
        ∃ ψ : ℝ → ℝ, StrictMonoOn ψ (M.winReg.arcIcc k₀) ∧ ContDiffOn ℝ 1 ψ (M.winReg.arcIcc k₀) ∧
          ψ (M.winReg.φs k₀.castSucc) = (M.base p).φs k.castSucc ∧
          ψ (M.winReg.φs k₀.succ) = (M.base p).φs k.succ ∧
          ∀ t ∈ M.winReg.arcIcc k₀, M.winReg.loop t = (M.base p).loop (ψ t)) ∧
      (∀ (p : ℤ × ℤ) (k : Fin (M.base p).N) (k₀ : Fin M.winReg.N),
        p ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi → (M.base p).arcSet k = M.winReg.arcSet k₀ → sqbit p k = false →
        ∃ ψ : ℝ → ℝ, StrictMonoOn ψ ((M.base p).arcIcc k) ∧ ContDiffOn ℝ 1 ψ ((M.base p).arcIcc k) ∧
          ψ ((M.base p).φs k.castSucc) = M.winReg.φs k₀.castSucc ∧
          ψ ((M.base p).φs k.succ) = M.winReg.φs k₀.succ ∧
          ∀ t ∈ (M.base p).arcIcc k, (M.base p).loop t = M.winReg.loop (ψ t)) ∧
      (∀ (p : ℤ × ℤ) (Z : Set ℂ), Shares (some p) Z ↔
        p ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi ∧ ∃ k : Fin (M.base p).N, (M.base p).arcSet k = Z) ∧
      (∀ Z : Set ℂ, Shares none Z ↔ ∃ k₀ : Fin M.winReg.N, M.winReg.arcSet k₀ = Z) ∧
      (∀ (p : ℤ × ℤ) (v : ℂ), Contains (some p) v ↔ p ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi ∧
        v ∈ (M.base p).K) ∧
      (∀ v : ℂ, Contains none v ↔ v ∉ M.winReg.Kint) ∧
      (∀ (ρ : Option (ℤ × ℤ)) (Z : Set ℂ), Shares ρ Z →
        ∃ ρ' : Option (ℤ × ℤ), ρ' ≠ ρ ∧ Shares ρ' Z ∧
          ∀ ρ'' : Option (ℤ × ℤ), Shares ρ'' Z → ρ'' = ρ ∨ ρ'' = ρ') ∧
      (∀ (v : ℂ) (ρ ρ' : Option (ℤ × ℤ)), Contains ρ v → Contains ρ' v →
        Relation.ReflTransGen
          (fun ρ₁ ρ₂ : Option (ℤ × ℤ) => ∃ Z : Set ℂ, Shares ρ₁ Z ∧ Shares ρ₂ Z ∧ v ∈ Z) ρ ρ') ∧
      B₀.card = ((M.jhi - M.jlo + 1).toNat + 1) * ((M.khi - M.klo + 1).toNat + 1) +
        (M.jhi - M.jlo + 1).toNat * (M.khi - M.klo + 1).toNat + (M.khi - M.klo + 1).toNat ∧
      (∀ p ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi, ∀ i : Fin ((M.base p).N + 1), (M.base p).loop
        ((M.base p).φs i) ∈ B₀) ∧
      (∀ i : Fin (M.winReg.N + 1), M.winReg.loop (M.winReg.φs i) ∈ B₀) ∧
      (∀ v ∈ B₀, ∃ p ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi, ∃ k : Fin (M.base p).N,
        v = (M.base p).loop ((M.base p).φs k.castSucc) ∨ v = (M.base p).loop ((M.base p).φs k.succ)) ∧
      (∀ v ∈ B₀, ∃ j : ℤ, v.re - M.o = j * M.hm)

theorem exists_grid_geometry (M : GridData) : Geometry M := by
  have hsq : ∀ p : ℤ × ℤ, SideIdentity.IsSquare M.o M.hm p.1 p.2 (M.ctr p) (M.yL p) (M.base p) := fun p =>
    ⟨(M.hctr p).1.1, (M.hctr p).1.2, (M.hctr p).2.1, (M.hctr p).2.2, (M.yL_mem p).1, (M.yL_mem p).2, M.hbase p⟩
  have hj : M.jlo ≤ M.jhi := by have h := M.hjlt; omega
  have hk : M.klo ≤ M.khi := by have h := M.hklt; omega
  have hbreak : ∀ (R : RadialRegion), 0 < R.N → ∀ i : Fin (R.N + 1),
      ∃ k : Fin R.N, i = k.castSucc ∨ i = k.succ := by
    intro R hN i
    by_cases h : i.val < R.N
    · exact ⟨⟨i.val, h⟩, Or.inl (Fin.ext (by simp))⟩
    · refine ⟨⟨R.N - 1, by omega⟩, Or.inr (Fin.ext ?_)⟩
      have hi := i.isLt
      simp only [Fin.val_succ]
      omega
  refine ⟨ArcReversal.sqbit M, ArcReversal.perbit M, GridVertices.B₀ M.o M.hm M.jlo M.jhi M.klo M.khi M.ctr, StarProperty.Shares M,
    StarProperty.Contains M, ?_, ArcReversal.bit_sq_sq M, ArcReversal.bit_sq_per M, ArcReversal.rev_sq_sq M,
    ArcReversal.rev_per_to_sq M, ArcReversal.rev_sq_to_per M, fun _ _ => Iff.rfl, fun _ => Iff.rfl,
    fun _ _ => Iff.rfl, fun _ => Iff.rfl, StarProperty.two_regions M, StarProperty.star M, ?_, ?_, ?_, ?_,
    fun v hv => GridVertices.B₀_off_lines v hv⟩
  · exact fun p k k' h => SideIdentity.arcSet_injective (hsq p) k k' h
  · exact GridVertices.card_B₀ M.hhm M.hctr hj hk
  · intro p hp i
    exact GridVertices.rect_break_mem (ctr := M.ctr) p hp.1.1 hp.1.2 hp.2.1 hp.2.2
      (M.hbase p) i
  · intro i
    have hN : 0 < M.winReg.N := by
      have h2 := M.two_le_winReg_N
      exact lt_of_lt_of_le Nat.zero_lt_two h2
    obtain ⟨k, hk' | hk'⟩ := hbreak M.winReg hN i
    · rw [hk']
      exact (GridVertices.window_break_mem (ctr := M.ctr) (hj := hj) (hk := hk) M.hwin k).1
    · rw [hk']
      exact (GridVertices.window_break_mem (ctr := M.ctr) (hj := hj) (hk := hk) M.hwin k).2
  · intro v hv
    obtain ⟨j, kk, hj₁, hj₂, hk₁, hk₂, hb⟩ := GridVertices.mem_B₀_iff_break hj hk v hv
    obtain ⟨i, hi⟩ := hb (M.base (j, kk)) (M.hbase (j, kk))
    have hN : 0 < (M.base (j, kk)).N := by
      rw [(M.hbase (j, kk)).2.1]
      omega
    obtain ⟨k', hk' | hk'⟩ := hbreak (M.base (j, kk)) hN i
    · exact ⟨(j, kk), ⟨⟨hj₁, hj₂⟩, ⟨hk₁, hk₂⟩⟩, k', Or.inl (by rw [← hi, hk'])⟩
    · exact ⟨(j, kk), ⟨⟨hj₁, hj₂⟩, ⟨hk₁, hk₂⟩⟩, k', Or.inr (by rw [← hi, hk'])⟩


end
end Dubon2026.SourceFunctionField.CellGeometry.GridGeometry
