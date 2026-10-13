import Dubon2026.OriginalAdicFiniteGalois
import Dubon2026.OriginalAdicIntegerNormComparison
import Mathlib.RingTheory.Valuation.Extension

/-! # Original adic completions and their actual valuation extension

The original completion topology is retained. Its norm valuation defines
the already proved local-field structure, and the original completed
embedding preserves the valuation relation through the integral-element
criterion. No isometric scalar action is assumed across different
ramification normalizations. These facts supply DUB-17's local invariant
comparison on the actual completions used in global H2 detection.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField WithZero

/-- The actual original adic completion is a nonarchimedean local field in its original topology. -/
theorem originalAdic_isNonarchimedeanLocalField
    (L : Type) [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) :
    letI : ValuativeRel (w.adicCompletion L) :=
      ValuativeRel.ofValuation (NormedField.valuation (K := w.adicCompletion L))
    IsNonarchimedeanLocalField (w.adicCompletion L) := by
  letI : NontriviallyNormedField (w.adicCompletion L) :=
    Valued.toNontriviallyNormedField (w.adicCompletion L) ℤᵐ⁰
  letI : ProperSpace (w.adicCompletion L) := original_adicCompletion_properSpace L w
  exact normValuation_isNonarchimedeanLocalField (w.adicCompletion L)

/-- The actual original completed base embedding extends the original norm valuation relation, including ramified places. -/
theorem originalAdicNormValuation_hasExtension
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] :
    letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
      (originalAdicBaseChangeMap K L v w).toAlgebra
    letI : ValuativeRel (v.adicCompletion K) :=
      ValuativeRel.ofValuation (NormedField.valuation (K := v.adicCompletion K))
    letI : ValuativeRel (w.adicCompletion L) :=
      ValuativeRel.ofValuation (NormedField.valuation (K := w.adicCompletion L))
    (ValuativeRel.valuation (v.adicCompletion K)).HasExtension
      (ValuativeRel.valuation (w.adicCompletion L)) := by
  letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
    (originalAdicBaseChangeMap K L v w).toAlgebra
  letI : ValuativeRel (v.adicCompletion K) :=
    ValuativeRel.ofValuation (NormedField.valuation (K := v.adicCompletion K))
  letI : ValuativeRel (w.adicCompletion L) :=
    ValuativeRel.ofValuation (NormedField.valuation (K := w.adicCompletion L))
  apply Valuation.HasExtension.ofComapInteger
  ext x
  change originalAdicBaseChangeMap K L v w x ∈
      (ValuativeRel.valuation (w.adicCompletion L)).integer ↔
    x ∈ (ValuativeRel.valuation (v.adicCompletion K)).integer
  rw [normValuativeInteger_mem_iff, normValuativeInteger_mem_iff,
    Valued.toNormedField.norm_le_one_iff, Valued.toNormedField.norm_le_one_iff]
  exact originalAdicBaseChangeMap_mem_integers K L v w x

end
end Dubon2026
