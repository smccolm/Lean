import Dubon2026.OriginalLocalCompletionMap
import Dubon2026.OriginalAdicLocalFieldStructures

/-! # The actual completion comparison preserves the valuation relation

The integer-ball identity holds on the dense original number field and
extends by clopenness and the proved continuity of the actual map. This
supplies the valuation-extension premise needed to transport DUB-17's
normalized local invariants to the original number-field completions.
-/
namespace Dubon2026
noncomputable section
open IsDedekindDomain UniformSpace Topology
open scoped NumberField ValuativeRel

variable (L E : Type) [Field L] [NumberField L] [Field E] [Algebra L E]
  (p : ℕ) (hp : p.Prime) [Algebra (rationalPrimeLocalField p hp) E]
  [ValuativeRel E] [UniformSpace E] [IsUniformAddGroup E] [IsNonarchimedeanLocalField E]
  [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension (ValuativeRel.valuation E)]

/-- The original completion map preserves and reflects the literal valuation integer ball. -/
theorem originalLocalCompletionMap_le_one_iff
    (x : (originalLocalEmbeddingPrime L E p hp).adicCompletion L) :
    Valued.v x ≤ 1 ↔ ValuativeRel.valuation E (originalLocalCompletionMap L E p hp x) ≤ 1 := by
  let W := (originalLocalEmbeddingPrime L E p hp).adicCompletion L
  let f := originalLocalCompletionMap L E p hp
  refine Completion.induction_on (p := fun x : W =>
    Valued.v x ≤ 1 ↔ ValuativeRel.valuation E (f x) ≤ 1) x ?_ ?_
  · have hs : IsClopen {x : W | Valued.v x ≤ 1} := Valued.isClopen_integer W
    have ht : IsClopen {x : W | ValuativeRel.valuation E (f x) ≤ 1} :=
      (Valuation.isClopen_integer (v := ValuativeRel.valuation E)).preimage
        (originalLocalCompletionMap_continuous L E p hp)
    simpa only [iff_def] using (isClosed_imp hs.2 ht.1).inter (isClosed_imp ht.2 hs.1)
  · intro q
    change Valued.v
      (algebraMap L ((originalLocalEmbeddingPrime L E p hp).adicCompletion L) q.ofVal) ≤ 1 ↔
      ValuativeRel.valuation E
        (f (algebraMap L ((originalLocalEmbeddingPrime L E p hp).adicCompletion L) q.ofVal)) ≤ 1
    rw [show f (algebraMap L ((originalLocalEmbeddingPrime L E p hp).adicCompletion L) q.ofVal) =
      algebraMap L E q.ofVal from originalLocalCompletionMap_algebraMap L E p hp q.ofVal]
    change Valued.v (q : W) ≤ 1 ↔ ValuativeRel.valuation E (algebraMap L E q.ofVal) ≤ 1
    rw [Valued.valuedCompletion_apply]
    exact (originalLocalEmbeddingPrime_valuation_isEquiv L E p hp).le_one_iff_le_one

/-- The original completed embedding extends the actual source norm valuation relation. -/
theorem originalLocalCompletionMap_hasExtension :
    let W := (originalLocalEmbeddingPrime L E p hp).adicCompletion L
    letI : Algebra W E := (originalLocalCompletionMap L E p hp).toAlgebra
    letI : ValuativeRel W := ValuativeRel.ofValuation (NormedField.valuation (K := W))
    (ValuativeRel.valuation W).HasExtension (ValuativeRel.valuation E) := by
  let W := (originalLocalEmbeddingPrime L E p hp).adicCompletion L
  letI : Algebra W E := (originalLocalCompletionMap L E p hp).toAlgebra
  letI : ValuativeRel W := ValuativeRel.ofValuation (NormedField.valuation (K := W))
  apply Valuation.HasExtension.ofComapInteger
  ext x
  change ValuativeRel.valuation E (originalLocalCompletionMap L E p hp x) ≤ 1 ↔
    x ∈ (ValuativeRel.valuation W).integer
  rw [normValuativeInteger_mem_iff, Valued.toNormedField.norm_le_one_iff]
  exact (originalLocalCompletionMap_le_one_iff L E p hp x).symm

end
end Dubon2026
