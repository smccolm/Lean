import Dubon2026.OriginalAdicBaseChangeMap
import Dubon2026.NumberFieldGaloisLocalTransport
import Mathlib.Topology.UniformSpace.CompleteSeparated

/-! # The original base completion is a closed fixed subfield

Closedness and pointwise invariance are two of the inputs to identifying
the actual base completion with the decomposition-group fixed field.
That identification is needed for the original idele norm quotient on
DUB-17's global duality, Selmer and automorphy dependency chain.
-/

namespace Dubon2026
noncomputable section
open IsDedekindDomain UniformSpace Topology
open scoped NumberField WithZero Topology
open MonoidWithZeroHom.ValueGroup₀

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

/-- The original completion map preserves and reflects the original uniformities. -/
theorem originalAdicBaseChangeMap_isUniformInducing :
    IsUniformInducing (originalAdicBaseChangeMap K L v w) := by
  let f := originalAdicBaseChangeMap K L v w
  rw [isUniformInducing_iff']
  refine ⟨Completion.uniformContinuous_map, ?_⟩
  apply ((Valued.hasBasis_uniformity (w.adicCompletion L) ℤᵐ⁰).comap
    (Prod.map f f)).le_basis_iff (Valued.hasBasis_uniformity (v.adicCompletion K) ℤᵐ⁰) |>.mpr
  intro γ _
  obtain ⟨x, hx⟩ := restrict₀_surjective
    (Valued.v (R := v.adicCompletion K)) γ.val
  have hx0 : x ≠ 0 := by
    intro hz
    subst x
    exact Units.ne_zero γ (by simpa using hx.symm)
  have hfx0 : f x ≠ 0 := (map_ne_zero f).mpr hx0
  refine ⟨Units.mk0 ((Valued.v (R := w.adicCompletion L)).restrict (f x))
    (by simp [Valuation.restrict_def, restrict₀_apply, hfx0]), trivial, ?_⟩
  rintro ⟨a, b⟩ hab
  change (Valued.v (R := w.adicCompletion L)).restrict (f b - f a) <
    (Valued.v (R := w.adicCompletion L)).restrict (f x) at hab
  rw [Valuation.restrict_lt_iff, ← map_sub] at hab
  change Valued.v (originalAdicBaseChangeMap K L v w (b - a)) <
    (Valued.v (originalAdicBaseChangeMap K L v w x) : ℤᵐ⁰) at hab
  rw [originalAdicBaseChangeMap_valuation, originalAdicBaseChangeMap_valuation] at hab
  change (Valued.v (R := v.adicCompletion K)).restrict (b - a) < γ.val
  rw [← hx]
  change (Valued.v (R := v.adicCompletion K)).restrict (b - a) <
    (Valued.v (R := v.adicCompletion K)).restrict x
  rw [Valuation.restrict_lt_iff]
  exact lt_of_pow_lt_pow_left₀ _ zero_le hab

/-- The original base completion is embedded as a closed subfield of the original upper completion. -/
theorem originalAdicBaseChangeMap_isClosedEmbedding :
    IsClosedEmbedding (originalAdicBaseChangeMap K L v w) := by
  exact (show IsUniformEmbedding (originalAdicBaseChangeMap K L v w) from
    ⟨originalAdicBaseChangeMap_isUniformInducing K L v w,
      (originalAdicBaseChangeMap K L v w).injective⟩).isClosedEmbedding

/-- Every original base-completion element is fixed by the actual prime stabilizer. -/
theorem originalAdicBaseChangeMap_fixed (σ : Gal(L/K))
    (hσ : numberFieldGaloisPlaceEquiv K L σ w = w) (x : v.adicCompletion K) :
    numberFieldGaloisLocalTransport K L σ w w hσ
      (originalAdicBaseChangeMap K L v w x) = originalAdicBaseChangeMap K L v w x := by
  induction x using Completion.induction_on
  · exact isClosed_eq
      ((numberFieldGaloisLocalTransport_continuous K L σ w w hσ).comp
        (originalAdicBaseChangeMap_continuous K L v w))
      (originalAdicBaseChangeMap_continuous K L v w)
  · rename_i x
    change numberFieldGaloisLocalTransport K L σ w w hσ
      (originalAdicBaseChangeMap K L v w (algebraMap K (v.adicCompletion K) x.ofVal)) = _
    rw [originalAdicBaseChangeMap_algebraMap, numberFieldGaloisLocalTransport_algebraMap,
      σ.commutes]
    exact (originalAdicBaseChangeMap_algebraMap K L v w x.ofVal).symm

end
end Dubon2026
