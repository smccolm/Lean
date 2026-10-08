import Dubon2026.DistinctWeightSubmodule
import Mathlib.Algebra.Lie.Semisimple.Defs

/-! # Irreducibility from actual distinct weights and nonzero ladder recurrences -/

namespace Dubon2026

/-- Every nonzero submodule of a distinct-weight ladder stable under its three actual operators is the entire ladder span. -/
theorem weightLadder_submodule_eq_span {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    (H E F : Module.End K W) (v : ℕ → W) (μ c : ℕ → K)
    (hμ : Function.Injective μ) (hH : ∀ n, H (v n) = μ n • v n)
    (hE : ∀ n, E (v n) = v (n + 1)) (hF : ∀ n, F (v (n + 1)) = c n • v n)
    (hc : ∀ n, c n ≠ 0) (p : Submodule K W) (hn : p ≠ ⊥)
    (hle : p ≤ Submodule.span K (Set.range v))
    (hpH : ∀ w ∈ p, H w ∈ p) (hpE : ∀ w ∈ p, E w ∈ p) (hpF : ∀ w ∈ p, F w ∈ p) :
    p = Submodule.span K (Set.range v) := by
  obtain ⟨w, hw, hwn⟩ := p.ne_bot_iff.mp hn
  obtain ⟨n, hvn, _⟩ := distinctWeight_exists_mem H v μ hμ hH p hpH w hw hwn (hle hw)
  have lower : ∀ n, v n ∈ p → v 0 ∈ p := by
    intro n
    induction n with
    | zero => exact id
    | succ n ih =>
        intro h
        have h' := hpF _ h
        rw [hF] at h'
        exact ih ((p.smul_mem_iff (hc n)).mp h')
  have hzero := lower n hvn
  have all : ∀ n, v n ∈ p := by
    intro n
    induction n with
    | zero => exact hzero
    | succ n ih => simpa only [hE] using hpE _ ih
  apply le_antisymm hle
  apply Submodule.span_le.mpr
  rintro _ ⟨n, rfl⟩
  exact all n

/-- A genuine Lie module spanned by a nonzero distinct-weight ladder with invertible lowering coefficients is irreducible. -/
theorem weightLadder_lie_irreducible {K L W : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup W] [Module K W] [LieRingModule L W] [LieModule K L W]
    (H E F : L) (v : ℕ → W) (μ c : ℕ → K) (hn : v 0 ≠ 0)
    (hspan : Submodule.span K (Set.range v) = ⊤)
    (hμ : Function.Injective μ) (hH : ∀ n, ⁅H, v n⁆ = μ n • v n)
    (hE : ∀ n, ⁅E, v n⁆ = v (n + 1)) (hF : ∀ n, ⁅F, v (n + 1)⁆ = c n • v n)
    (hc : ∀ n, c n ≠ 0) : LieModule.IsIrreducible K L W := by
  letI : Nontrivial W := ⟨⟨v 0, 0, hn⟩⟩
  apply LieModule.IsIrreducible.mk
  intro p hp
  have hp' : p.toSubmodule ≠ ⊥ := by
    intro h
    apply hp
    ext w
    change w ∈ p.toSubmodule ↔ w = 0
    rw [h, Submodule.mem_bot]
  have he := weightLadder_submodule_eq_span (LieModule.toEnd K L W H)
    (LieModule.toEnd K L W E) (LieModule.toEnd K L W F) v μ c hμ hH hE hF hc
    p.toSubmodule hp' (by rw [hspan]; exact le_top)
    (fun _ hw => p.lie_mem hw) (fun _ hw => p.lie_mem hw) (fun _ hw => p.lie_mem hw)
  rw [hspan] at he
  ext w
  change w ∈ p.toSubmodule ↔ w ∈ (⊤ : Submodule K W)
  rw [he]

end Dubon2026
