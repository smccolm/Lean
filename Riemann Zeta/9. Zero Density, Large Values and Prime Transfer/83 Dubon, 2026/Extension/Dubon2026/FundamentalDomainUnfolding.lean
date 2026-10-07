import Dubon2026.FundamentalDomainTransport

/-! # Nonnegative unfolding over actual subgroup cosets -/

namespace Dubon2026

open MeasureTheory Set
open scoped Pointwise ENNReal

noncomputable section

/-- Distinct inverse representatives of subgroup cosets give disjoint tiles of a genuine domain. -/
theorem fundamentalDomain_subgroup_tiles_aedisjoint
    {G α : Type*} [Group G] [MeasurableSpace α] [MulAction G α]
    {μ : Measure α} {S : Set α} (hS : IsFundamentalDomain G S μ) (H : Subgroup G) :
    Pairwise (fun q r : G ⧸ H => AEDisjoint μ (q.out⁻¹ • S) (r.out⁻¹ • S)) := by
  intro q r hqr
  apply hS.aedisjoint
  intro he
  apply hqr
  have h := congrArg (QuotientGroup.mk : G → G ⧸ H) (inv_injective he)
  simpa only [Quotient.out_eq'] using h

/-- The exact nonnegative coset unfolding formula, allowing infinite index and infinite integrals. -/
theorem fundamentalDomain_subgroup_unfold_lintegral
    {G α : Type*} [Group G] [MeasurableSpace α] [MulAction G α]
    [MeasurableConstSMul G α] {μ : Measure α} [SMulInvariantMeasure G α μ]
    (H : Subgroup G) [Countable (G ⧸ H)] [Countable H]
    {S V : Set α} (hS : IsFundamentalDomain G S μ) (hV : IsFundamentalDomain H V μ)
    (F : α → ℝ≥0∞) (hF : Measurable F) (hFinv : ∀ (h : H) x, F (h • x) = F x) :
    (∫⁻ x in S, ∑' q : G ⧸ H, F (q.out⁻¹ • x) ∂μ) = ∫⁻ x in V, F x ∂μ := by
  calc
    (∫⁻ x in S, ∑' q : G ⧸ H, F (q.out⁻¹ • x) ∂μ) =
        ∑' q : G ⧸ H, ∫⁻ x in S, F (q.out⁻¹ • x) ∂μ :=
      lintegral_tsum (fun q => (hF.comp (measurable_const_smul _)).aemeasurable)
    _ = ∑' q : G ⧸ H, ∫⁻ x in q.out⁻¹ • S, F x ∂μ := by
      apply tsum_congr
      intro q
      exact (measurePreserving_smul q.out⁻¹ μ).setLIntegral_comp_emb
        (measurableEmbedding_const_smul _) F S
    _ = ∫⁻ x in ⋃ q : G ⧸ H, q.out⁻¹ • S, F x ∂μ :=
      (lintegral_iUnion₀ (fun q : G ⧸ H => hS.nullMeasurableSet_smul q.out⁻¹)
        (fundamentalDomain_subgroup_tiles_aedisjoint hS H) F).symm
    _ = ∫⁻ x in V, F x ∂μ :=
      (fundamentalDomain_subgroup_iUnion_out_smul H hS).setLIntegral_eq hV F hFinv

end
end Dubon2026
