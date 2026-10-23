import Dubon2026.SourceResidueTwistedPrimeRelations
import Dubon2026.SourceUniqueCommonRootDescent

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> all-level
residue degree -> mixed-divisor generation. Distinct prime relations have
only the actual j_(mpq) as common root. Existing simple-pole injectivity and
the existing unique-common-root descent give membership in the original
coefficient subfield. This adapts local SourceOriginalTwoPrimeGeneration,
using the proved residue relations instead of rational coefficient transport.
The source argument is from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_relfinrank_fullC_mul_prime_pow. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField PrimeDegreeAux

theorem residue_two_prime_generation
    (K : Type*) [Field K] (m p q : ℕ) [NeZero m]
    [hp : Fact p.Prime] [hq : Fact q.Prime] (hpq : p ≠ q)
    (ζ η : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p) (hη : IsPrimitiveRoot (η : K) q)
    (F : IntermediateField K (LaurentSeries K))
    (hmp : qExpand K (m * p) (jqModC K) ∈ F) (hmq : qExpand K (m * q) (jqModC K) ∈ F) :
    qExpand K (m * p * q) (jqModC K) ∈ F := by
  let N := m * p * q
  obtain ⟨P, hPm, _, hP⟩ := exists_residue_prime_twisted_relations K p ζ hζ
  obtain ⟨Q, hQm, _, hQ⟩ := exists_residue_prime_twisted_relations K q η hη
  let φ : F →+* LaurentSeries K :=
    (qExpand K N).comp (algebraMap F (LaurentSeries K))
  letI : Algebra F (LaurentSeries K) := φ.toAlgebra
  have halg : algebraMap F (LaurentSeries K) = φ := rfl
  let A := relationAtSeed P (⟨qExpand K (m * q) (jqModC K), hmq⟩ : F)
  let B := relationAtSeed Q (⟨qExpand K (m * p) (jqModC K), hmp⟩ : F)
  have hmapA : A.map φ = relationAtSeed P (TS K ((m * q) * (m * q) * p) 1) := by
    dsimp only [A]
    rw [relationAtSeed_map]
    congr 1
    change qExpand K N (qExpand K (m * q) (jqModC K)) = _
    rw [qExpand_qExpand, TS, qTwist_one_apply]
    exact qExpand_congr (by dsimp [N]; ring) (jqModC K)
  have hmapB : B.map φ = relationAtSeed Q (TS K ((m * p) * (m * p) * q) 1) := by
    dsimp only [B]
    rw [relationAtSeed_map]
    congr 1
    change qExpand K N (qExpand K (m * p) (jqModC K)) = _
    rw [qExpand_qExpand, TS, qTwist_one_apply]
    exact qExpand_congr (by dsimp [N]; ring) (jqModC K)
  have hrootA : ∀ y : LaurentSeries K, Polynomial.aeval y A = 0 ↔
      y = TS K (N * N) 1 ∨ ∃ b < p, y = TS K ((m * q) * (m * q)) (ζ ^ b) := by
    intro y
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, halg, hmapA]
    have h := residue_prime_root_iff_of_root_list p ((m * q) * (m * q)) ζ 1 P hPm (hP _ 1).1 y
    simp only [one_pow, one_mul] at h
    rw [TS_congr (show (m * q) * (m * q) * (p * p) = N * N by dsimp [N]; ring) 1] at h
    exact h
  have hrootB : ∀ y : LaurentSeries K, Polynomial.aeval y B = 0 ↔
      y = TS K (N * N) 1 ∨ ∃ b < q, y = TS K ((m * p) * (m * p)) (η ^ b) := by
    intro y
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, halg, hmapB]
    have h := residue_prime_root_iff_of_root_list q ((m * p) * (m * p)) η 1 Q hQm (hQ _ 1).1 y
    simp only [one_pow, one_mul] at h
    rw [TS_congr (show (m * p) * (m * p) * (q * q) = N * N by dsimp [N]; ring) 1] at h
    exact h
  have hAs : (A.map (algebraMap F (LaurentSeries K))).Splits := by
    rw [halg, hmapA]
    simpa only [one_pow] using (hP ((m * q) * (m * q)) 1).2.1
  have hAn : (A.map (algebraMap F (LaurentSeries K))).roots.Nodup := by
    rw [halg, hmapA]
    simpa only [one_pow] using (hP ((m * q) * (m * q)) 1).2.2
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
  have hx : qExpand K N (qExpand K N (jqModC K)) = TS K (N * N) 1 := by
    rw [qExpand_qExpand, TS, qTwist_one_apply]
  have he : (f : LaurentSeries K) = qExpand K N (jqModC K) :=
    ((qExpand K N).injective (hf.trans hx.symm))
  change qExpand K N (jqModC K) ∈ F
  rw [← he]
  exact f.2

end
end Dubon2026.SourceFunctionField
