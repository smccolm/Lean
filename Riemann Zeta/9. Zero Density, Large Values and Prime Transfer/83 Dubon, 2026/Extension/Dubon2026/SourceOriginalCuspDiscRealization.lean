import Dubon2026.SourceCuspDiscRealization
import Dubon2026.SourceOriginalCuspGermRealization

/-! DUB-17/18 -> original torsion cardinality -> cusp charts.
The actual original two-generator field admits meromorphic realization
on one disk for each literal cusp embedding. All nonzero functions have
finite meromorphic order throughout that disk, and at its center their
orders equal the exact original cusp normalization times the place order.
No uniform-radius or analytic-realization premise is supplied.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open CuspTaylor IntermediateField Metric

theorem original_embedding_common_disc (N : ℕ) [NeZero N]
    (ι : modularFunctionFieldOver N ℂ →ₐ[ℂ] LaurentSeries ℂ)
    (hjReal : RationallyRealized (ι (jOver N ℂ)))
    (hjNReal : RationallyRealized (ι (jNOver N ℂ))) :
    ∃ R : ℝ, 0 < R ∧ ∀ f : modularFunctionFieldOver N ℂ,
      ∃ F : ℂ → ℂ, MeromorphicOn F (ball 0 R) ∧
        Represents (ι f) F := by
  obtain ⟨r, hr, hj⟩ := exists_discField_of_realized hjReal
  obtain ⟨t, ht, hjN⟩ := exists_discField_of_realized hjNReal
  let R := min r t
  have hjR : ι (jOver N ℂ) ∈ discField R := discField_mono (min_le_left r t) hj
  have hjNR : ι (jNOver N ℂ) ∈ discField R := discField_mono (min_le_right r t) hjN
  have hle : IntermediateField.adjoin ℂ
      ({jOver N ℂ, jNOver N ℂ} : Set (modularFunctionFieldOver N ℂ)) ≤
      (discField R).comap ι := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    rcases hx with rfl | hx
    · exact hjR
    · rcases hx with rfl
      exact hjNR
  refine ⟨R, lt_min hr ht, fun f => ?_⟩
  apply hle
  rw [original_internal_pair_adjoin_top]
  exact IntermediateField.mem_top

theorem original_cusp_embedding_common_disc (N : ℕ) [NeZero N]
    (ζ : ℂˣ) (hζ : IsPrimitiveRoot (ζ : ℂ) N)
    (s : {s // s ∈ CuspLabels.labels N}) :
    ∃ R : ℝ, 0 < R ∧ ∀ f : modularFunctionFieldOver N ℂ,
      ∃ F : ℂ → ℂ, MeromorphicOn F (ball 0 R) ∧
        Represents (CuspLabels.embedding N ℂ ζ hζ s f) F :=
  original_embedding_common_disc N (CuspLabels.embedding N ℂ ζ hζ s)
    (original_cusp_embedding_analytic_quotient N ζ hζ s (jOver N ℂ))
    (original_cusp_embedding_analytic_quotient N ζ hζ s (jNOver N ℂ))

theorem original_cusp_embedding_common_disc_orders (N : ℕ) [NeZero N]
    (ζ : ℂˣ) (hζ : IsPrimitiveRoot (ζ : ℂ) N)
    (s : {s // s ∈ CuspLabels.labels N}) :
    ∃ R : ℝ, 0 < R ∧ ∀ f : modularFunctionFieldOver N ℂ,
      ∃ F : ℂ → ℂ, MeromorphicOn F (ball 0 R) ∧
        Represents (CuspLabels.embedding N ℂ ζ hζ s f) F ∧
        (f ≠ 0 → meromorphicOrderAt F 0 =
          (((CuspLabels.place N ℂ ζ hζ s).ord f *
            ((s.1.1 * Nat.gcd s.1.1 (N / s.1.1) : ℕ) : ℤ) : ℤ) : WithTop ℤ)) ∧
        (f ≠ 0 → ∀ z ∈ ball 0 R, meromorphicOrderAt F z ≠ ⊤) := by
  obtain ⟨R, hR, hF⟩ := original_cusp_embedding_common_disc N ζ hζ s
  refine ⟨R, hR, fun f => ?_⟩
  obtain ⟨F, hm, hFA⟩ := hF f
  have hne (hf : f ≠ 0) : CuspLabels.embedding N ℂ ζ hζ s f ≠ 0 :=
    (map_ne_zero (CuspLabels.embedding N ℂ ζ hζ s)).mpr hf
  refine ⟨F, hm, hFA, fun hf => ?_, fun hf z hz => order_ne_top_on_disc hR hm hFA (hne hf) hz⟩
  rw [hFA.order (hne hf), ← (CuspLabels.embedding_spec N ℂ ζ hζ s).2.2.1 f]

end
end Dubon2026.SourceFunctionField
