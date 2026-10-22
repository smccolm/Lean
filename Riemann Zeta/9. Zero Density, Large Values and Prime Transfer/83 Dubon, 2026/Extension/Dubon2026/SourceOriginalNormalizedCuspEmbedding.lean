import Dubon2026.SourceLaurentExpansionDescent
import Dubon2026.SourceCuspTaylorFieldStability
import Dubon2026.SourceOriginalCuspFamily

/-! DUB-17/18 -> original torsion cardinality -> normalized cusp charts.
The proved original cusp range permits inversion of its exact common
power substitution. The resulting literal embedding has order equal to
the original place order. Its two generators remain explicit convergent
twisted j series; no power-compression convergence theorem is needed.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open ConjugateSlots PrimeDegreeAux CuspTaylor

theorem descendExpansion_TS_mem_realizedField {F : Type*} [Field F] [Algebra ℂ F]
    (e : ℕ) [NeZero e] (ι : F →ₐ[ℂ] LaurentSeries ℂ)
    (hrange : ∀ f, ι f ∈ (qExpandAlgHom ℂ e).fieldRange)
    (f : F) (d : ℕ) [NeZero d] (u : ℂˣ)
    (hed : e ∣ d) (hf : ι f = TS ℂ d u) :
    descendExpansion e ι hrange f ∈ realizedField := by
  obtain ⟨k, hk⟩ := hed
  haveI : NeZero k := ⟨fun h => NeZero.ne d (by rw [hk, h, mul_zero])⟩
  have he : ι f = qExpand ℂ e (TS ℂ k u) := by
    rw [hf]
    dsimp only [TS]
    rw [qExpand_qExpand]
    exact qExpand_congr hk _
  rw [descendExpansion_apply_of_eq e ι hrange f (TS ℂ k u) he]
  exact TS_mem_realizedField k u

namespace CuspLabels
variable (N : ℕ) [NeZero N]

/-- The exact common expansion exponent of the actual primitive cusp embedding. -/
def normalization (s : {s // s ∈ labels N}) : ℕ :=
  s.1.1 * Nat.gcd s.1.1 (N / s.1.1)

instance normalization_neZero (s : {s // s ∈ labels N}) : NeZero (normalization N s) := by
  have ha := index_fst_ne_zero (label_mem_indices N s.1 s.2)
  exact ⟨Nat.mul_ne_zero ha (Nat.gcd_ne_zero_left ha)⟩

variable (ζ : ℂˣ) (hζ : IsPrimitiveRoot (ζ : ℂ) N)

theorem embedding_mem_expansionRange (s : {s // s ∈ labels N})
    (f : modularFunctionFieldOver N ℂ) :
    embedding N ℂ ζ hζ s f ∈ (qExpandAlgHom ℂ (normalization N s)).fieldRange := by
  haveI : NeZero s.1.1 := ⟨index_fst_ne_zero (label_mem_indices N s.1 s.2)⟩
  exact original_slot_embedding_range ℂ N ζ s.1.1 s.1.2
    ((mem_labels N s.1).mp s.2).1 (embedding N ℂ ζ hζ s)
    (embedding_spec N ℂ ζ hζ s).1 (embedding_spec N ℂ ζ hζ s).2.1 f

/-- The actual cusp embedding with its proved common expansion inverted. -/
def normalizedEmbedding (s : {s // s ∈ labels N}) :
    modularFunctionFieldOver N ℂ →ₐ[ℂ] LaurentSeries ℂ :=
  descendExpansion (normalization N s) (embedding N ℂ ζ hζ s)
    (embedding_mem_expansionRange N ζ hζ s)

theorem qExpand_normalizedEmbedding (s : {s // s ∈ labels N})
    (f : modularFunctionFieldOver N ℂ) :
    qExpand ℂ (normalization N s) (normalizedEmbedding N ζ hζ s f) = embedding N ℂ ζ hζ s f :=
  qExpand_descendExpansion _ _ _ _

theorem normalizedEmbedding_order (s : {s // s ∈ labels N})
    (f : modularFunctionFieldOver N ℂ) :
    (normalizedEmbedding N ζ hζ s f).order = (place N ℂ ζ hζ s).ord f := by
  apply mul_left_cancel₀ (show (normalization N s : ℤ) ≠ 0 by exact_mod_cast NeZero.ne (normalization N s))
  rw [← laurent_order_qExpand, qExpand_normalizedEmbedding,
    ← (embedding_spec N ℂ ζ hζ s).2.2.1 f]
  exact mul_comm _ _

theorem normalizedEmbedding_j_realized (s : {s // s ∈ labels N}) :
    normalizedEmbedding N ζ hζ s (jOver N ℂ) ∈ realizedField := by
  apply descendExpansion_TS_mem_realizedField _ _ _ _ N 1
  · exact (Nat.mul_dvd_mul_left s.1.1 (Nat.gcd_dvd_right _ _)).trans
      (by rw [Nat.mul_div_cancel' ((mem_labels N s.1).mp s.2).1])
  · exact (embedding_spec N ℂ ζ hζ s).1

theorem normalizedEmbedding_jN_realized (s : {s // s ∈ labels N}) :
    normalizedEmbedding N ζ hζ s (jNOver N ℂ) ∈ realizedField := by
  haveI : NeZero s.1.1 := ⟨index_fst_ne_zero (label_mem_indices N s.1 s.2)⟩
  apply descendExpansion_TS_mem_realizedField _ _ _ _ (s.1.1 * s.1.1) (ζ ^ (s.1.2 * s.1.1))
  · exact Nat.mul_dvd_mul_left s.1.1 (Nat.gcd_dvd_left _ _)
  · rw [(embedding_spec N ℂ ζ hζ s).2.1, slotValue_eq]

end CuspLabels
end
end Dubon2026.SourceFunctionField
