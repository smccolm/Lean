import Dubon2026.SourcePrimePowerExpansionRange

/-! DUB-17/18 -> numerical modular genus -> exact all-level degree
-> next-series nonmembership. Induction through the literal prime-power
fields repeatedly applies the proved embedding extension. The expansion
range decreases by one prime factor at each step, retaining the exact
root-of-unity phase of the current original j series.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_jqN_pow_not_mem_adjoin_full.lean, chain_endgame.
-/
namespace Dubon2026.SourceFunctionField.PrimePowerNonmembership
noncomputable section
open PrimeDegreeAux
variable {K : Type*} [Field K] [Algebra ℚ K] [IsAlgClosed K]

theorem exists_chain_spread_embedding (M : ℕ) [NeZero M]
    (p : ℕ) [Fact p.Prime] (a : ℕ)
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) (M * p ^ (a + 2)))
    (hnot : ∀ i : ℕ, i ≤ a → qExpand ℚ (p ^ i * p) jq ∉ chainField M p i)
    (i : ℕ) (hi : i ≤ a) :
    ∃ (σ : chainField M p i →+* LaurentSeries K) (t : ℕ),
      σ ⟨qExpand ℚ (p ^ i) jq, mem_chainField M p (le_refl i)⟩ =
        TS K (M * p ^ (a + 2 - i)) (ζ ^ (t * (M * p ^ (a + 2 - i)))) ∧
      ∀ y : chainField M p i, σ y ∈ (qExpand K (M * p ^ (a + 2 - i))).range := by
  induction i with
  | zero =>
    refine ⟨((coeffEmb K).comp (qExpand ℚ (M * p ^ (a + 2)))).comp
      (algebraMap (chainField M p 0) (LaurentSeries ℚ)), 0, ?_, ?_⟩
    · change coeffEmb K (qExpand ℚ (M * p ^ (a + 2)) (qExpand ℚ (p ^ 0) jq)) = _
      rw [qExpand_congr (pow_zero p) jq, qExpand_one_apply, coeffEmb_qExpand_jq_eq_TS,
        zero_mul, pow_zero, Nat.sub_zero]
    · intro y
      change coeffEmb K (qExpand ℚ (M * p ^ (a + 2)) (y : LaurentSeries ℚ)) ∈ _
      refine RingHom.mem_range.mpr ⟨coeffEmb K (y : LaurentSeries ℚ), ?_⟩
      exact (coeffMap_qExpand (algebraMap ℚ K) (M * p ^ (a + 2)) (y : LaurentSeries ℚ)).symm
  | succ i ih =>
    obtain ⟨σ, t, hσtop, hσrange⟩ := ih (Nat.le_of_succ_le hi)
    have hpow : M * p ^ (a + 2 - i) = p * (M * p ^ (a + 2 - (i + 1))) := by
      rw [show a + 2 - i = (a + 2 - (i + 1)) + 1 by omega, pow_succ]
      ring
    have hσtop' : σ ⟨qExpand ℚ (p ^ i) jq, mem_chainField M p (le_refl i)⟩ =
        TS K (p * (M * p ^ (a + 2 - (i + 1))))
          (ζ ^ (t * (p * (M * p ^ (a + 2 - (i + 1)))))) := by
      simpa only [hpow] using hσtop
    have hζ' : IsPrimitiveRoot (ζ : K) (p * (M * p ^ (a + 2 - (i + 1))) * p ^ i) := by
      have hBs : M * p ^ (a + 2) = p * (M * p ^ (a + 2 - (i + 1))) * p ^ i := by
        have h1 : 1 + (a + 2 - (i + 1)) + i = a + 2 := by omega
        calc
          M * p ^ (a + 2) = M * p ^ (1 + (a + 2 - (i + 1)) + i) := by rw [h1]
          _ = p * (M * p ^ (a + 2 - (i + 1))) * p ^ i := by
            rw [pow_add, pow_add, pow_one]
            ring
      exact hBs ▸ hζ
    have hσrange' : ∀ y : chainField M p i,
        σ y ∈ (qExpand K (p * (M * p ^ (a + 2 - (i + 1))))).range := by
      intro y
      exact range_qExpand_congr (K := K) hpow ▸ hσrange y
    obtain ⟨σ', t', _, hσnew, hσrangeNew⟩ :=
      chain_extend p (M * p ^ (a + 2 - (i + 1))) (p ^ i) ζ hζ'
        (chainField M p i) σ (p ^ i) (mem_chainField M p (le_refl i))
        (hnot i (Nat.le_of_succ_le hi)) t hσtop' hσrange'
        (chainField M p (i + 1)) (chainField_succ M p i)
    refine ⟨σ', t', ?_, hσrangeNew⟩
    have hx : qExpand ℚ (p ^ i * p) jq ∈ chainField M p (i + 1) := by
      rw [qExpand_congr (pow_succ p i).symm jq]
      exact mem_chainField M p (le_refl (i + 1))
    have hm : (⟨qExpand ℚ (p ^ (i + 1)) jq, mem_chainField M p (le_refl (i + 1))⟩ :
        chainField M p (i + 1)) = ⟨qExpand ℚ (p ^ i * p) jq, hx⟩ :=
      Subtype.ext (qExpand_congr (pow_succ p i) jq)
    rw [hm]
    exact hσnew hx

end
end Dubon2026.SourceFunctionField.PrimePowerNonmembership
