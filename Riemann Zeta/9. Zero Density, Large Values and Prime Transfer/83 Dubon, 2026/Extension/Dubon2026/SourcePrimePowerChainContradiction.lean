import Dubon2026.SourcePrimePowerRelationTransport

/-! DUB-17/18 -> numerical modular genus -> exact prime-power degree.
The actual prime conjugate product forces the two adjacent roots of the
embedded relation to coincide if the next j series were already present.
Injectivity and the distinct leading Laurent exponents contradict this.
Only earlier nonmembership stages are assumed, for strong induction.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_jqN_pow_not_mem_adjoin_full.lean, chain_endgame.
-/
namespace Dubon2026.SourceFunctionField.PrimePowerNonmembership
noncomputable section
open Polynomial PrimeDegreeAux
variable {K : Type*} [Field K] [Algebra ℚ K] [IsAlgClosed K]

theorem chain_next_not_mem_of_earlier (M : ℕ) [NeZero M]
    (p : ℕ) [hp : Fact p.Prime] (a : ℕ)
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) (M * p ^ (a + 2)))
    (hnot : ∀ i : ℕ, i ≤ a → qExpand ℚ (p ^ i * p) jq ∉ chainField M p i) :
    qExpand ℚ (p ^ (a + 2)) jq ∉ chainField M p (a + 1) := by
  intro hmem
  obtain ⟨σ, ta, tt, hprev, htop, hrange⟩ :=
    exists_adjacent_spread_embedding M p a ζ hζ hnot
  have hpN : p ∣ M * p ^ (a + 2) := by
    refine ⟨M * p ^ (a + 1), ?_⟩
    rw [pow_succ]
    ring
  let η : Kˣ := ζ ^ (M * p ^ (a + 2) / p)
  have hη : IsPrimitiveRoot (η : K) p := primitive_root_pow_div hζ hpN
  obtain ⟨P, _, _, hP⟩ := exists_prime_product_at_root p η hη
  have hup : (relationAtSeed P (qExpand ℚ (p ^ (a + 1)) jq)).eval
      (qExpand ℚ (p ^ (a + 2)) jq) = 0 := by
    have h := relationAtSeed_substitution_eval P (prime_product_forward_root p K η P hP)
      (p ^ (a + 1))
    rwa [qExpand_congr (pow_succ p (a + 1)).symm jq] at h
  have hdn : (relationAtSeed P (qExpand ℚ (p ^ (a + 1)) jq)).eval
      (qExpand ℚ (p ^ a) jq) = 0 := by
    have h := relationAtSeed_reverse_substitution_eval P (prime_product_reverse_root p K η P hP)
      (p ^ a)
    rwa [qExpand_congr (pow_succ p a).symm jq] at h
  let x : chainField M p (a + 1) :=
    ⟨qExpand ℚ (p ^ (a + 1)) jq, mem_chainField M p (le_refl (a + 1))⟩
  let y : chainField M p (a + 1) := ⟨qExpand ℚ (p ^ (a + 2)) jq, hmem⟩
  let z : chainField M p (a + 1) :=
    ⟨qExpand ℚ (p ^ a) jq, mem_chainField M p (Nat.le_succ a)⟩
  have hseed : σ x = TS K (M * p) ((ζ ^ (tt * M)) ^ p) := by
    rw [htop, ← pow_mul]
    congr 2
    ring
  have hy : (relationAtSeed P (TS K (M * p) ((ζ ^ (tt * M)) ^ p))).eval (σ y) = 0 := by
    rw [← hseed]
    exact relationAtSeed_eval_subfield_map P _ σ x y hup
  have hz : (relationAtSeed P (TS K (M * p) ((ζ ^ (tt * M)) ^ p))).eval (σ z) = 0 := by
    rw [← hseed]
    exact relationAtSeed_eval_subfield_map P _ σ x z hdn
  have hMp : ¬ ((M * p : ℕ) : ℤ) ∣ (M : ℤ) := by
    rw [Int.natCast_dvd_natCast]
    intro hdvd
    have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) hdvd
    have hmul := Nat.mul_le_mul_left M hp.out.two_le
    have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
    omega
  have hySpread : σ y = TS K (M * (p * p)) ((ζ ^ (tt * M)) ^ (p * p)) := by
    rcases (prime_twisted_product_root_iff p η P hP M (ζ ^ (tt * M)) (σ y)).mp hy with
      h | ⟨c, _, h⟩
    · exact h
    · exact False.elim (TS_not_mem_range_qExpand hMp _ (h ▸ hrange y))
  have hzSpread : σ z = TS K (M * (p * p)) ((ζ ^ (tt * M)) ^ (p * p)) := by
    rcases (prime_twisted_product_root_iff p η P hP M (ζ ^ (tt * M)) (σ z)).mp hz with
      h | ⟨c, _, h⟩
    · exact h
    · have he := (TS_injective (hprev.symm.trans h)).1
      have hp1 : 1 < p := hp.out.one_lt
      have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
      have hbig : M < p * (M * p) := calc
        M < M * p := lt_mul_of_one_lt_right hM hp1
        _ ≤ p * (M * p) := Nat.le_mul_of_pos_left _ hp.out.pos
      omega
  have hval : qExpand ℚ (p ^ (a + 2)) jq = qExpand ℚ (p ^ a) jq :=
    congrArg Subtype.val (σ.injective (hySpread.trans hzSpread.symm))
  have he := qExpand_jq_injective hval
  have hlt : p ^ a < p ^ (a + 2) := Nat.pow_lt_pow_right hp.out.one_lt (by omega)
  omega

end
end Dubon2026.SourceFunctionField.PrimePowerNonmembership
