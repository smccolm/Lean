import Dubon2026.SourceOriginalCuspGermRealization
import Dubon2026.SourceTaylorLaurentOrder

/-! DUB-17/18 -> original torsion cardinality -> cusp parameters.
Every nonzero function in the literal original field has an analytic
quotient realizing its actual cusp embedding, with meromorphic order
equal to the already proved exact cusp normalization times its original
place order. No convergence or order-comparison input remains here.
Descent to a normalized parameter and a common cusp chart remain required.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open CuspTaylor

theorem original_cusp_embedding_analytic_quotient_order (N : ℕ) [NeZero N]
    (ζ : ℂˣ) (hζ : IsPrimitiveRoot (ζ : ℂ) N)
    (s : {s // s ∈ CuspLabels.labels N})
    (f : modularFunctionFieldOver N ℂ) (hf : f ≠ 0) :
    ∃ g h : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ AnalyticAt ℂ h 0 ∧
      (series h : LaurentSeries ℂ) ≠ 0 ∧
      CuspLabels.embedding N ℂ ζ hζ s f =
        (series g : LaurentSeries ℂ) / (series h : LaurentSeries ℂ) ∧
      MeromorphicAt (g / h) 0 ∧
      meromorphicOrderAt (g / h) 0 =
        (((CuspLabels.place N ℂ ζ hζ s).ord f *
          ((s.1.1 * Nat.gcd s.1.1 (N / s.1.1) : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
  obtain ⟨g, h, hg, hh, hh0, he⟩ := original_cusp_embedding_analytic_quotient N ζ hζ s f
  have hgc : (series g : LaurentSeries ℂ) ≠ 0 := by
    intro hz
    have he0 : CuspLabels.embedding N ℂ ζ hζ s f = 0 := by rw [he, hz, zero_div]
    exact hf ((CuspLabels.embedding N ℂ ζ hζ s).injective (he0.trans (map_zero _).symm))
  have hg0 : series g ≠ 0 := by
    intro hz
    exact hgc (by rw [hz, map_zero])
  have hh0' : series h ≠ 0 := by
    intro hz
    exact hh0 (by rw [hz, map_zero])
  refine ⟨g, h, hg, hh, hh0, he, hg.meromorphicAt.div hh.meromorphicAt, ?_⟩
  rw [meromorphicOrderAt_quotient hg hh hg0 hh0', ← he,
    ← (CuspLabels.embedding_spec N ℂ ζ hζ s).2.2.1 f]

end
end Dubon2026.SourceFunctionField
