import Dubon2026.SourceResidueTwoPrimeGeneration

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> exact
all-level residue degree -> generation from the reverse expansion field.
The two actual prime relations recover j_(m*l) from j_m and j_(m*l*p).
Scale by l alone: simple-pole exponents separate the smaller branches from
both branches of the second relation. This shortens the global-level scaling
in the archived S_ModularCurve_relfinrank_fullC_mul_prime_pow argument
(anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2). -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField PrimeDegreeAux

theorem residue_adjacent_prime_generation
    (K : Type*) [Field K] (m l p : ℕ) [NeZero m]
    [hl : Fact l.Prime] [hp : Fact p.Prime]
    (ζ η : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) l) (hη : IsPrimitiveRoot (η : K) p)
    (F : IntermediateField K (LaurentSeries K))
    (hm : qExpand K m (jqModC K) ∈ F)
    (hmp : qExpand K (m * l * p) (jqModC K) ∈ F) :
    qExpand K (m * l) (jqModC K) ∈ F := by
  obtain ⟨P, hPm, _, hP⟩ := exists_residue_prime_twisted_relations K l ζ hζ
  obtain ⟨Q, hQm, _, hQ⟩ := exists_residue_prime_twisted_relations K p η hη
  let φ : F →+* LaurentSeries K := (qExpand K l).comp (algebraMap F (LaurentSeries K))
  letI : Algebra F (LaurentSeries K) := φ.toAlgebra
  have halg : algebraMap F (LaurentSeries K) = φ := rfl
  let A := relationAtSeed P (⟨qExpand K m (jqModC K), hm⟩ : F)
  let B := relationAtSeed Q (⟨qExpand K (m * l * p) (jqModC K), hmp⟩ : F)
  have hmapA : A.map φ = relationAtSeed P (TS K (m * l) 1) := by
    rw [relationAtSeed_map]
    congr 1
    change qExpand K l (qExpand K m (jqModC K)) = _
    rw [qExpand_qExpand, TS, qTwist_one_apply]
    exact qExpand_congr (mul_comm l m) _
  have hmapB : B.map φ = relationAtSeed Q (TS K (m * (l * l) * p) 1) := by
    rw [relationAtSeed_map]
    congr 1
    change qExpand K l (qExpand K (m * l * p) (jqModC K)) = _
    rw [qExpand_qExpand, TS, qTwist_one_apply]
    exact qExpand_congr (by ring) _
  have hrootA (y : LaurentSeries K) : Polynomial.aeval y A = 0 ↔
      y = TS K (m * (l * l)) 1 ∨ ∃ b < l, y = TS K m (ζ ^ b) := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, halg, hmapA]
    simpa only [one_pow, one_mul] using
      residue_prime_root_iff_of_root_list l m ζ 1 P hPm (hP m 1).1 y
  have hrootB (y : LaurentSeries K) : Polynomial.aeval y B = 0 ↔
      y = TS K (m * (l * l) * (p * p)) 1 ∨
        ∃ b < p, y = TS K (m * (l * l)) (η ^ b) := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, halg, hmapB]
    simpa only [one_pow, one_mul] using
      residue_prime_root_iff_of_root_list p (m * (l * l)) η 1 Q hQm (hQ _ 1).1 y
  have hAs : (A.map (algebraMap F (LaurentSeries K))).Splits := by
    rw [halg, hmapA]
    simpa only [one_pow] using (hP m 1).2.1
  have hAn : (A.map (algebraMap F (LaurentSeries K))).roots.Nodup := by
    rw [halg, hmapA]
    simpa only [one_pow] using (hP m 1).2.2
  have hu : ∀ y : LaurentSeries K,
      Polynomial.aeval y A = 0 → Polynomial.aeval y B = 0 → y = TS K (m * (l * l)) 1 := by
    intro y hyA hyB
    rcases (hrootA y).mp hyA with he | ⟨b, _, hb⟩
    · exact he
    have hm0 := Nat.pos_of_ne_zero (NeZero.ne m)
    have hl2 := hl.out.two_le
    have hbig : m < m * (l * l) :=
      lt_mul_of_one_lt_right hm0 (lt_of_lt_of_le (by decide : 1 < 4)
        (Nat.mul_le_mul hl2 hl2))
    rcases (hrootB y).mp hyB with he | ⟨c, _, hc⟩
    · have heq := (TS_injective (hb.symm.trans he)).1
      exact False.elim ((ne_of_lt (hbig.trans_le
        (Nat.le_mul_of_pos_right _ (Nat.mul_pos hp.out.pos hp.out.pos)))) heq)
    · have heq := (TS_injective (hb.symm.trans hc)).1
      exact False.elim ((ne_of_lt hbig) heq)
  obtain ⟨f, hf⟩ := mem_range_of_unique_common_root_monic A B (hPm.map _) hAs hAn
    (TS K (m * (l * l)) 1) ((hrootA _).mpr (Or.inl rfl))
    ((hrootB _).mpr (Or.inr ⟨0, hp.out.pos, by rw [pow_zero]⟩)) hu
  have hx : qExpand K l (qExpand K (m * l) (jqModC K)) = TS K (m * (l * l)) 1 := by
    rw [qExpand_qExpand, TS, qTwist_one_apply]
    exact qExpand_congr (by ring) _
  have he : (f : LaurentSeries K) = qExpand K (m * l) (jqModC K) :=
    (qExpand K l).injective (hf.trans hx.symm)
  rw [← he]
  exact f.2

end
end Dubon2026.SourceFunctionField
