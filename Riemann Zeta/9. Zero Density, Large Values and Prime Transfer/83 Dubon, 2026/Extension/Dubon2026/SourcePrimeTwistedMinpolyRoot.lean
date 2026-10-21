import Dubon2026.SourcePrimeTwistedRoots
import Dubon2026.SourcePrimeAdjacentRelations

/-! DUB-17/18 -> numerical modular genus -> all-level degree
-> original next-series nonmembership -> extension of twisted field embeddings.
Nonmembership makes the actual minimal polynomial non-linear. Its roots
are distinct and lie in the proved prime root list, so at least one is a
non-distinguished twisted root. This derives the root needed by the native
simple-extension homomorphism theorem; no such root is assumed.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_jqN_pow_not_mem_adjoin_full.lean, chain_extend.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial PrimeDegreeAux
variable {K : Type*} [Field K] [Algebra ℚ K]

theorem exists_prime_twisted_minpoly_root
    (p : ℕ) [Fact p.Prime] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p)
    (R : Polynomial (Polynomial ℤ)) (hRm : R.Monic)
    (hR : R.map (((coeffEmb K).comp (qExpand ℚ p)).comp evalAtJ) =
      PhiGen.phiProd p (PhiGen.conj p ζ))
    (F : IntermediateField ℚ (LaurentSeries ℚ)) (σ : F →+* LaurentSeries K)
    (d : ℕ) [NeZero d] (hd : qExpand ℚ d jq ∈ F)
    (hnot : qExpand ℚ (d * p) jq ∉ F)
    (e : ℕ) [NeZero e] (u : Kˣ)
    (hσd : σ ⟨qExpand ℚ d jq, hd⟩ = TS K (e * p) (u ^ p)) :
    IsIntegral F (qExpand ℚ (d * p) jq) ∧
      ∃ c < p, ((minpoly F (qExpand ℚ (d * p) jq)).map σ).eval (TS K e (u * ζ ^ c)) = 0 := by
  classical
  let Q := relationAtSeed R (⟨qExpand ℚ d jq, hd⟩ : F)
  have hQroot : Polynomial.aeval (qExpand ℚ (d * p) jq) Q = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, relationAtSeed_map]
    exact relationAtSeed_substitution_eval R (prime_product_forward_root p K ζ R hR) d
  have hQm : Q.Monic := hRm.map _
  have hint : IsIntegral F (qExpand ℚ (d * p) jq) := ⟨Q, hQm, hQroot⟩
  refine ⟨hint, ?_⟩
  have hmap : Q.map σ = relationAtSeed R (TS K (e * p) (u ^ p)) := by
    change (relationAtSeed R (⟨qExpand ℚ d jq, hd⟩ : F)).map σ = _
    rw [relationAtSeed_map, hσd]
  have hQne : Q.map σ ≠ 0 := (hQm.map σ).ne_zero
  have hdvd : (minpoly F (qExpand ℚ (d * p) jq)).map σ ∣ Q.map σ :=
    Polynomial.map_dvd σ (minpoly.dvd F _ hQroot)
  have hsplit : ((minpoly F (qExpand ℚ (d * p) jq)).map σ).Splits := by
    have hs : (Q.map σ).Splits := by
      rw [hmap]
      exact prime_twisted_product_splits p ζ R hR e u
    exact hs.of_dvd hQne hdvd
  have hle : ((minpoly F (qExpand ℚ (d * p) jq)).map σ).roots ≤ (Q.map σ).roots :=
    Polynomial.roots.le_of_dvd hQne hdvd
  have hnd : ((minpoly F (qExpand ℚ (d * p) jq)).map σ).roots.Nodup := by
    have hn : (Q.map σ).roots.Nodup := by
      rw [hmap]
      exact prime_twisted_product_roots_nodup p ζ hζ R hR e u
    exact Multiset.nodup_of_le hle hn
  have hdeg : 2 ≤ ((minpoly F (qExpand ℚ (d * p) jq)).map σ).natDegree := by
    rw [(minpoly.monic hint).natDegree_map, minpoly.two_le_natDegree_iff hint]
    rintro ⟨w, hw⟩
    exact hnot (hw ▸ w.2)
  have hcard : 1 < ((minpoly F (qExpand ℚ (d * p) jq)).map σ).roots.toFinset.card := by
    rw [Multiset.toFinset_card_of_nodup hnd, ← hsplit.natDegree_eq_card_roots]
    omega
  obtain ⟨y₁, hy₁, y₂, hy₂, hne⟩ := Finset.one_lt_card.mp hcard
  have hshape : ∀ y ∈ ((minpoly F (qExpand ℚ (d * p) jq)).map σ).roots,
      y = TS K (e * (p * p)) (u ^ (p * p)) ∨ ∃ c < p, y = TS K e (u * ζ ^ c) := by
    intro y hy
    have h := (Polynomial.mem_roots hQne).mp (Multiset.mem_of_le hle hy)
    rw [hmap] at h
    exact (prime_twisted_product_root_iff p ζ R hR e u y).mp h
  have hmne : (minpoly F (qExpand ℚ (d * p) jq)).map σ ≠ 0 := ((minpoly.monic hint).map σ).ne_zero
  have hr1 := (Polynomial.mem_roots hmne).mp (Multiset.mem_toFinset.mp hy₁)
  have hr2 := (Polynomial.mem_roots hmne).mp (Multiset.mem_toFinset.mp hy₂)
  rcases hshape y₁ (Multiset.mem_toFinset.mp hy₁) with h1 | ⟨c, hc, h1⟩
  · rcases hshape y₂ (Multiset.mem_toFinset.mp hy₂) with h2 | ⟨c, hc, h2⟩
    · exact (hne (h1.trans h2.symm)).elim
    · exact ⟨c, hc, h2 ▸ hr2⟩
  · exact ⟨c, hc, h1 ▸ hr1⟩

end
end Dubon2026.SourceFunctionField
