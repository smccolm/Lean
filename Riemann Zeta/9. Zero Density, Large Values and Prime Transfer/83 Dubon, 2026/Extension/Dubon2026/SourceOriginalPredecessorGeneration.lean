import Dubon2026.SourceOriginalConjugateRootBounds

/-! DUB-17/18 -> numerical modular genus -> composite generation.
The actual prime relation and lower minimal polynomial have a unique
common Laurent root. Their split, distinct prime roots and native
minimal-polynomial descent put j(q^M) in Q(j(q),j(q^(Mp))). The only
induction input is the proved lower-level conjugate-product identity.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_jqN_div_mem_modularFunctionField.lean.
The direct minimal-polynomial argument replaces the external gcd helper.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField ConjugateSlots PrimeDegreeAux
open scoped IntermediateField
variable {K : Type*} [Field K] [Algebra ℚ K] [IsAlgClosed K]

theorem original_predecessor_mem_pair_of_lower_product (M p : ℕ)
    [NeZero M] [hp : Fact p.Prime] (η : Kˣ)
    (hlower : expandedJMinpoly K M M = slotProduct M η) :
    qExpand ℚ M jq ∈ IntermediateField.adjoin ℚ
      ({jq, qExpand ℚ (M * p) jq} : Set (LaurentSeries ℚ)) := by
  obtain ⟨ζ, P, hζ, hPm, _, hP⟩ := exists_prime_product_algClosed p K
  let F := IntermediateField.adjoin ℚ
    ({jq, qExpand ℚ (M * p) jq} : Set (LaurentSeries ℚ))
  have hj : jq ∈ F := IntermediateField.subset_adjoin ℚ _ (Or.inl rfl)
  have hjN : qExpand ℚ (M * p) jq ∈ F :=
    IntermediateField.subset_adjoin ℚ _ (Or.inr rfl)
  have hBF : ℚ⟮jq⟯ ≤ F :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hj)
  let ι : ℚ⟮jq⟯ →+* F := Subfield.inclusion
    (show (ℚ⟮jq⟯).toSubfield ≤ F.toSubfield from hBF)
  let φ : F →+* LaurentSeries K :=
    ((coeffEmb K).comp (qExpand ℚ (M * p))).comp (algebraMap F (LaurentSeries ℚ))
  letI : Algebra F (LaurentSeries K) := φ.toAlgebra
  have halg : algebraMap F (LaurentSeries K) = φ := rfl
  let A := relationAtSeed P (⟨qExpand ℚ (M * p) jq, hjN⟩ : F)
  let B := (minpoly ℚ⟮jq⟯ (qExpand ℚ M jq)).map ι
  let e := M * p * M
  have hmapA : A.map φ = relationAtSeed P (TS K (e * p) 1) := by
    dsimp only [A]
    rw [relationAtSeed_map]
    congr 1
    change coeffEmb K (qExpand ℚ (M * p) (qExpand ℚ (M * p) jq)) = _
    rw [qExpand_qExpand, coeffEmb_qExpand_jq_eq_TS]
    exact TS_congr (by dsimp [e]; ring) 1
  have hmapB : B.map φ = expandedJMinpoly K (M * p) M := by
    dsimp only [B]
    rw [Polynomial.map_map, expandedJMinpoly]
    congr 1
  have hrootA : ∀ y : LaurentSeries K, Polynomial.aeval y A = 0 ↔
      y = TS K (e * (p * p)) 1 ∨ ∃ c < p, y = TS K e (ζ ^ c) := by
    intro y
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, halg, hmapA]
    simpa only [one_pow, one_mul] using prime_twisted_product_root_iff p ζ P hP e 1 y
  have hBev : ∀ y : LaurentSeries K, Polynomial.aeval y B = 0 →
      (expandedJMinpoly K (M * p) M).IsRoot y := by
    intro y hy
    rwa [Polynomial.aeval_def, ← Polynomial.eval_map, halg, hmapB] at hy
  have hAs : (A.map (algebraMap F (LaurentSeries K))).Splits := by
    rw [halg, hmapA]
    simpa only [one_pow] using prime_twisted_product_splits p ζ P hP e 1
  have hAn : (A.map (algebraMap F (LaurentSeries K))).roots.Nodup := by
    rw [halg, hmapA]
    simpa only [one_pow] using prime_twisted_product_roots_nodup p ζ hζ P hP e 1
  have hxA : Polynomial.aeval (TS K e 1) A = 0 :=
    (hrootA _).mpr (Or.inr ⟨0, hp.out.pos, by rw [pow_zero]⟩)
  have hxB : Polynomial.aeval (TS K e 1) B = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, halg, hmapB]
    exact expandedJMinpoly_distinguished_root K (M * p) M
  have hu : ∀ y : LaurentSeries K,
      Polynomial.aeval y A = 0 → Polynomial.aeval y B = 0 → y = TS K e 1 := by
    intro y hyA hyB
    have hy := hBev y hyB
    rcases (hrootA y).mp hyA with hbig | ⟨c, _, hc⟩
    · exfalso
      apply original_lower_root_ne_larger_branch M p η hlower y hy
      exact hbig.trans (TS_congr (by dsimp [e]; ring) 1)
    · have hw := original_lower_root_top_twist_eq_one M p η hlower y hy (ζ ^ c) hc
      simpa only [hw] using hc
  obtain ⟨f, hf⟩ := mem_range_of_unique_common_root_monic A B (hPm.map _)
    hAs hAn (TS K e 1) hxA hxB hu
  have hx : coeffEmb K (qExpand ℚ (M * p) (qExpand ℚ M jq)) = TS K e 1 := by
    rw [qExpand_qExpand, coeffEmb_qExpand_jq_eq_TS]
  have he : (f : LaurentSeries ℚ) = qExpand ℚ M jq :=
    (((coeffEmb K).comp (qExpand ℚ (M * p))).injective (hf.trans hx.symm))
  rw [← he]
  exact f.2

end
end Dubon2026.SourceFunctionField
