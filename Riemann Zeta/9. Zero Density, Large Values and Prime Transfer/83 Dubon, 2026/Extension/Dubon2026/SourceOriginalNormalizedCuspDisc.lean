import Dubon2026.SourceOriginalNormalizedCuspEmbedding
import Dubon2026.SourceOriginalCuspDiscRealization

/-! DUB-17/18 -> original torsion cardinality -> normalized cusp charts.
All original functions have meromorphic realizations on one common disk
at each actual cusp, with their original normalized place orders at its
center. The exact expansion inversion removes the cusp-width factor.
All nonzero functions have finite order everywhere on the same disk.
Turning these compatible germs into a place chart remains required.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open CuspTaylor Metric

theorem original_normalized_cusp_common_disc (N : ℕ) [NeZero N]
    (ζ : ℂˣ) (hζ : IsPrimitiveRoot (ζ : ℂ) N)
    (s : {s // s ∈ CuspLabels.labels N}) :
    ∃ R : ℝ, 0 < R ∧ ∀ f : modularFunctionFieldOver N ℂ,
      ∃ F : ℂ → ℂ, MeromorphicOn F (ball 0 R) ∧
        Represents (CuspLabels.normalizedEmbedding N ζ hζ s f) F ∧
        (f ≠ 0 → meromorphicOrderAt F 0 = ((CuspLabels.place N ℂ ζ hζ s).ord f : WithTop ℤ)) ∧
        (f ≠ 0 → ∀ z ∈ ball 0 R, meromorphicOrderAt F z ≠ ⊤) := by
  obtain ⟨R, hR, hF⟩ := original_embedding_common_disc N
    (CuspLabels.normalizedEmbedding N ζ hζ s)
    (CuspLabels.normalizedEmbedding_j_realized N ζ hζ s)
    (CuspLabels.normalizedEmbedding_jN_realized N ζ hζ s)
  refine ⟨R, hR, fun f => ?_⟩
  obtain ⟨F, hm, hFA⟩ := hF f
  have hne (hf : f ≠ 0) : CuspLabels.normalizedEmbedding N ζ hζ s f ≠ 0 :=
    (map_ne_zero (CuspLabels.normalizedEmbedding N ζ hζ s)).mpr hf
  refine ⟨F, hm, hFA, fun hf => ?_, fun hf z hz => order_ne_top_on_disc hR hm hFA (hne hf) hz⟩
  rw [hFA.order (hne hf), CuspLabels.normalizedEmbedding_order]

end
end Dubon2026.SourceFunctionField
