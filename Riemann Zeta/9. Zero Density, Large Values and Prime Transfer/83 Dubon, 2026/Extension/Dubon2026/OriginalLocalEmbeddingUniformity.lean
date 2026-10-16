import Dubon2026.OriginalLocalEmbeddingContinuity
import Mathlib.Topology.UniformSpace.CompleteSeparated

/-! # The original local embedding reflects its induced adic uniformity

The actual prime-adic and pulled-back valuation comparison also reflects
neighbourhoods. Completion therefore embeds as a closed field, a necessary
step toward identifying DUB-17's orbit field with the individual completion.
-/
namespace Dubon2026
noncomputable section
open IsDedekindDomain UniformSpace Topology
open MonoidWithZeroHom.ValueGroup₀
open scoped NumberField ValuativeRel WithZero

variable (L E : Type) [Field L] [NumberField L] [Field E] [Algebra L E]
  (p : ℕ) (hp : p.Prime) [Algebra (rationalPrimeLocalField p hp) E]
  [ValuativeRel E] [UniformSpace E] [IsUniformAddGroup E] [IsNonarchimedeanLocalField E]
  [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension (ValuativeRel.valuation E)]

/-- The actual local embedding preserves and reflects the original
prime-adic uniformity; no completion identification is assumed. -/
theorem originalLocalEmbeddingAdicMap_isUniformInducing :
    IsUniformInducing (originalLocalEmbeddingAdicMap L E p hp) := by
  let w := originalLocalEmbeddingPrime L E p hp
  let A := WithVal (w.valuation L)
  let f := originalLocalEmbeddingAdicMap L E p hp
  rw [isUniformInducing_iff']
  refine ⟨originalLocalEmbeddingAdicMap_uniformContinuous L E p hp, ?_⟩
  apply ((Valued.hasBasis_uniformity E (ValuativeRel.ValueGroupWithZero E)).comap
    (Prod.map f f)).le_basis_iff (Valued.hasBasis_uniformity A ℤᵐ⁰) |>.mpr
  intro γ _
  obtain ⟨x, hx⟩ := restrict₀_surjective (Valued.v (R := A)) γ.val
  have hx0 : x ≠ 0 := by
    intro hz
    subst x
    exact Units.ne_zero γ (by simpa using hx.symm)
  have hfx0 : f x ≠ 0 := (map_ne_zero f).mpr hx0
  refine ⟨Units.mk0 ((Valued.v (R := E)).restrict (f x))
    (by simp [Valuation.restrict_def, restrict₀_apply, hfx0]), trivial, ?_⟩
  rintro ⟨u, v⟩ huv
  change (Valued.v (R := E)).restrict (f v - f u) < (Valued.v (R := E)).restrict (f x) at huv
  rw [Valuation.restrict_lt_iff, ← map_sub] at huv
  have hval : w.valuation L (v - u).ofVal < w.valuation L x.ofVal :=
    (originalLocalEmbeddingPrime_valuation_isEquiv L E p hp).lt_iff_lt.mpr huv
  change (Valued.v (R := A)).restrict (v - u) < γ.val
  rw [← hx]
  change (Valued.v (R := A)).restrict (v - u) < (Valued.v (R := A)).restrict x
  rw [Valuation.restrict_lt_iff]
  exact hval

end
end Dubon2026
