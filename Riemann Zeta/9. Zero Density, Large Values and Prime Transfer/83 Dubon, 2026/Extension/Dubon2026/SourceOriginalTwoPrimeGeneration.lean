import Dubon2026.SourceOriginalCoprimeInduction

/-! DUB-17/18 -> numerical modular genus -> composite degree ->
adjoining the missing prime-power series. Two distinct prime relations
recover j_(mpq) from j_(mp) and j_(mq). Their finite twisted branches
have different Laurent leading exponents, so their only common root is
the actual distinguished j-series. The proved unique-common-root descent
then places that series in the original subfield. This supplies the
mixed-divisor generation needed in the prime-power tower decomposition.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_full_eq_adjoin_full_div_prime.lean.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField PrimeDegreeAux

theorem original_two_prime_generation (m p q : ℕ) [NeZero m]
    [hp : Fact p.Prime] [hq : Fact q.Prime] (hpq : p ≠ q)
    (F : IntermediateField ℚ (LaurentSeries ℚ))
    (hmp : qExpand ℚ (m * p) jq ∈ F) (hmq : qExpand ℚ (m * q) jq ∈ F) :
    qExpand ℚ (m * p * q) jq ∈ F := by
  let K := AlgebraicClosure ℚ
  let N := m * p * q
  obtain ⟨ζ, P, hζ, hPm, _, hP⟩ := exists_prime_product_algClosed p K
  obtain ⟨η, Q, _, _, _, hQ⟩ := exists_prime_product_algClosed q K
  let φ : F →+* LaurentSeries K :=
    ((coeffEmb K).comp (qExpand ℚ N)).comp (algebraMap F (LaurentSeries ℚ))
  letI : Algebra F (LaurentSeries K) := φ.toAlgebra
  have halg : algebraMap F (LaurentSeries K) = φ := rfl
  let A := relationAtSeed P (⟨qExpand ℚ (m * q) jq, hmq⟩ : F)
  let B := relationAtSeed Q (⟨qExpand ℚ (m * p) jq, hmp⟩ : F)
  have hmapA : A.map φ = relationAtSeed P (TS K ((m * q) * (m * q) * p) 1) := by
    dsimp only [A]
    rw [relationAtSeed_map]
    congr 1
    change coeffEmb K (qExpand ℚ N (qExpand ℚ (m * q) jq)) = _
    rw [qExpand_qExpand, coeffEmb_qExpand_jq_eq_TS]
    exact TS_congr (by dsimp [N]; ring) 1
  have hmapB : B.map φ = relationAtSeed Q (TS K ((m * p) * (m * p) * q) 1) := by
    dsimp only [B]
    rw [relationAtSeed_map]
    congr 1
    change coeffEmb K (qExpand ℚ N (qExpand ℚ (m * p) jq)) = _
    rw [qExpand_qExpand, coeffEmb_qExpand_jq_eq_TS]
    exact TS_congr (by dsimp [N]; ring) 1
  have hrootA : ∀ y : LaurentSeries K, Polynomial.aeval y A = 0 ↔
      y = TS K (N * N) 1 ∨ ∃ b < p, y = TS K ((m * q) * (m * q)) (ζ ^ b) := by
    intro y
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, halg, hmapA]
    have h := prime_twisted_product_root_iff p ζ P hP ((m * q) * (m * q)) 1 y
    simp only [one_pow, one_mul] at h
    rw [TS_congr (show (m * q) * (m * q) * (p * p) = N * N by dsimp [N]; ring) 1] at h
    exact h
  have hrootB : ∀ y : LaurentSeries K, Polynomial.aeval y B = 0 ↔
      y = TS K (N * N) 1 ∨ ∃ b < q, y = TS K ((m * p) * (m * p)) (η ^ b) := by
    intro y
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, halg, hmapB]
    have h := prime_twisted_product_root_iff q η Q hQ ((m * p) * (m * p)) 1 y
    simp only [one_pow, one_mul] at h
    rw [TS_congr (show (m * p) * (m * p) * (q * q) = N * N by dsimp [N]; ring) 1] at h
    exact h
  have hAs : (A.map (algebraMap F (LaurentSeries K))).Splits := by
    rw [halg, hmapA]
    simpa only [one_pow] using prime_twisted_product_splits p ζ P hP ((m * q) * (m * q)) 1
  have hAn : (A.map (algebraMap F (LaurentSeries K))).roots.Nodup := by
    rw [halg, hmapA]
    simpa only [one_pow] using prime_twisted_product_roots_nodup p ζ hζ P hP ((m * q) * (m * q)) 1
  have hu : ∀ y : LaurentSeries K,
      Polynomial.aeval y A = 0 → Polynomial.aeval y B = 0 → y = TS K (N * N) 1 := by
    intro y hyA hyB
    rcases (hrootA y).mp hyA with he | ⟨b, _, hb⟩
    · exact he
    rcases (hrootB y).mp hyB with he | ⟨c, _, hc⟩
    · exact he
    have hs : m * q = m * p := Nat.mul_self_inj.mp (TS_injective (hb.symm.trans hc)).1
    exact False.elim (hpq (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (NeZero.ne m)) hs).symm)
  obtain ⟨f, hf⟩ := mem_range_of_unique_common_root_monic A B (hPm.map _) hAs hAn
    (TS K (N * N) 1) ((hrootA _).mpr (Or.inl rfl)) ((hrootB _).mpr (Or.inl rfl)) hu
  have hx : coeffEmb K (qExpand ℚ N (qExpand ℚ N jq)) = TS K (N * N) 1 := by
    rw [qExpand_qExpand, coeffEmb_qExpand_jq_eq_TS]
  have he : (f : LaurentSeries ℚ) = qExpand ℚ N jq :=
    (((coeffEmb K).comp (qExpand ℚ N)).injective (hf.trans hx.symm))
  change qExpand ℚ N jq ∈ F
  rw [← he]
  exact f.2

end
end Dubon2026.SourceFunctionField
