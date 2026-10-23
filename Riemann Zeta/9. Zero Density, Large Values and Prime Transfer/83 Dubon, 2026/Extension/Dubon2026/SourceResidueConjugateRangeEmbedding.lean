import Dubon2026.SourceResidueConjugateInduction
import Dubon2026.SourceConjugateConstantDescent

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> exact
all-level residue degree -> coprime prime nonmembership. Adapt local SourceOriginalConjugateRangeEmbedding
to actual coefficient-field j series and divisor fields. Lower generation and
conjugate products are explicit induction inputs. Expansion-range preservation
forces each image of j_p to the distinguished branch; bounded polynomial
descent contradicts the already proved prime nonmembership in K(j).
The level and prime must remain nonzero in the coefficient field. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField
open scoped IntermediateField
variable {K : Type*} [Field K]

theorem residue_conjugate_embedding_in_prime_expansion_range
    (M p : ℕ) [NeZero M] [NeZero p]
    (hgen : modularFunctionFieldCoeff M K =
      IntermediateField.adjoin K ({(jqModC K), qExpand K M (jqModC K)} : Set (LaurentSeries K)))
    (y : LaurentSeries K) (hy : (residueExpandedJMinpoly K (M * p) M).IsRoot y)
    (hyrange : y ∈ (qExpand K p).range) :
    ∃ σ : modularFunctionFieldCoeff M K →+* LaurentSeries K,
      (∀ (z : K⟮(jqModC K)⟯) (hz : (z : LaurentSeries K) ∈ modularFunctionFieldCoeff M K),
        σ ⟨z, hz⟩ = (qExpand K (M * p) (z : LaurentSeries K))) ∧
      σ ⟨qExpand K M (jqModC K), jqd_mem_coeff_field M K dvd_rfl⟩ = y ∧
      ∀ z : modularFunctionFieldCoeff M K, σ z ∈ (qExpand K p).range := by
  let B := K⟮(jqModC K)⟯
  let φ : B →+* LaurentSeries K :=
    ((qExpand K (M * p))).comp (algebraMap B (LaurentSeries K))
  have hrange : ∀ z : B, φ z ∈ (qExpand K p).range := by
    intro z
    refine ⟨(qExpand K M (z : LaurentSeries K)), ?_⟩
    change qExpand K p (qExpand K M (z : LaurentSeries K)) = _
    rw [qExpand_qExpand,
      qExpand_congr (Nat.mul_comm p M) (z : LaurentSeries K)]
    rfl
  obtain ⟨τ, hbase, hnew, hall⟩ := extend_coefficient_simple_embedding_in_expansion_range
    B φ (qExpand K M (jqModC K)) (residue_j_substitution_isIntegral K M) y hy p hrange hyrange
  let G := IntermediateField.adjoin K ((B : Set (LaurentSeries K)) ∪ {qExpand K M (jqModC K)})
  have he : modularFunctionFieldCoeff M K = G :=
    hgen.trans (residue_j_adjoin_union_eq_pair K M).symm
  let σ : modularFunctionFieldCoeff M K →+* LaurentSeries K := τ.comp
    (Subfield.inclusion (show (modularFunctionFieldCoeff M K).toSubfield ≤ G.toSubfield from he.le))
  refine ⟨σ, ?_, ?_, ?_⟩
  · intro z hz
    have hzG : (z : LaurentSeries K) ∈ G := by rw [← he]; exact hz
    exact hbase z hzG
  · have hzG : qExpand K M (jqModC K) ∈ G := by rw [← he]; exact jqd_mem_coeff_field M K dvd_rfl
    exact hnew hzG
  · intro z
    exact hall ⟨z, he.le z.2⟩

end
end Dubon2026.SourceFunctionField
