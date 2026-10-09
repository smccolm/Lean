import Dubon2026.DistinctWeightSubmodule

/-! # Irreducibility of genuine finite weight ladders -/

namespace Dubon2026

/-- A subspace stable under the actual three operators of a finite distinct-weight basis is zero or the whole space. -/
theorem finiteWeightLadder_submodule_eq_top {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    (n : ℕ) (H E F : Module.End K W) (v : ℕ → W) (μ c : ℕ → K)
    (hspan : Submodule.span K (Set.range (fun r : Fin (n + 1) => v r.val)) = ⊤)
    (hμ : Function.Injective μ) (hH : ∀ r, H (v r) = μ r • v r)
    (hE : ∀ r, E (v r) = v (r + 1)) (hF : ∀ r, F (v (r + 1)) = c r • v r)
    (hc : ∀ r < n, c r ≠ 0) (p : Submodule K W) (hn : p ≠ ⊥)
    (hpH : ∀ w ∈ p, H w ∈ p) (hpE : ∀ w ∈ p, E w ∈ p) (hpF : ∀ w ∈ p, F w ∈ p) :
    p = ⊤ := by
  obtain ⟨w, hw, hwn⟩ := p.ne_bot_iff.mp hn
  obtain ⟨r, hvr, _⟩ := distinctWeight_exists_mem H (fun r : Fin (n + 1) => v r.val)
    (fun r : Fin (n + 1) => μ r.val) (hμ.comp Fin.val_injective)
    (fun r => hH r.val) p hpH w hw hwn (by rw [hspan]; exact Submodule.mem_top)
  have lower : ∀ r ≤ n, v r ∈ p → v 0 ∈ p := by
    intro r
    induction r with
    | zero => intro _ hv; exact hv
    | succ r ih =>
        intro hr hv
        have hl := hpF _ hv
        rw [hF] at hl
        exact ih (Nat.le_of_succ_le hr) ((p.smul_mem_iff (hc r hr)).mp hl)
  have hzero := lower r.val (Nat.le_of_lt_succ r.is_lt) hvr
  have all : ∀ r, v r ∈ p := by
    intro r
    induction r with
    | zero => exact hzero
    | succ r ih => simpa only [hE] using hpE _ ih
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro _ ⟨r, rfl⟩
  exact all r.val

end Dubon2026
