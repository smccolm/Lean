import Dubon2026.SourcePrimePowerChainSpread

/-! DUB-17/18 -> numerical modular genus -> original prime-power degree.
The final extension in the chain retains the images of both adjacent
original j series. Those two images are used in the nonmembership
contradiction; the earlier stages' nonmembership is the induction input.
-/
namespace Dubon2026.SourceFunctionField.PrimePowerNonmembership
noncomputable section
open PrimeDegreeAux
variable {K : Type*} [Field K] [Algebra ℚ K] [IsAlgClosed K]

theorem exists_adjacent_spread_embedding (M : ℕ) [NeZero M]
    (p : ℕ) [Fact p.Prime] (a : ℕ)
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) (M * p ^ (a + 2)))
    (hnot : ∀ i : ℕ, i ≤ a → qExpand ℚ (p ^ i * p) jq ∉ chainField M p i) :
    ∃ (σ : chainField M p (a + 1) →+* LaurentSeries K) (ta tt : ℕ),
      σ ⟨qExpand ℚ (p ^ a) jq, mem_chainField M p (Nat.le_succ a)⟩ =
        TS K (p * (M * p)) (ζ ^ (ta * (p * (M * p)))) ∧
      σ ⟨qExpand ℚ (p ^ (a + 1)) jq, mem_chainField M p (le_refl (a + 1))⟩ =
        TS K (M * p) (ζ ^ (tt * (M * p))) ∧
      ∀ y : chainField M p (a + 1), σ y ∈ (qExpand K (M * p)).range := by
  obtain ⟨σa, ta, hatop, harange⟩ :=
    exists_chain_spread_embedding M p a ζ hζ hnot a (le_refl a)
  have hpow : M * p ^ (a + 2 - a) = p * (M * p) := by
    rw [show a + 2 - a = 2 by omega]
    ring
  have hatop' : σa ⟨qExpand ℚ (p ^ a) jq, mem_chainField M p (le_refl a)⟩ =
      TS K (p * (M * p)) (ζ ^ (ta * (p * (M * p)))) := by
    simpa only [hpow] using hatop
  have harange' : ∀ y : chainField M p a, σa y ∈ (qExpand K (p * (M * p))).range := by
    intro y
    exact range_qExpand_congr (K := K) hpow ▸ harange y
  have hζtop : IsPrimitiveRoot (ζ : K) (p * (M * p) * p ^ a) := by
    have hBs : M * p ^ (a + 2) = p * (M * p) * p ^ a := by
      rw [pow_add]
      ring
    exact hBs ▸ hζ
  obtain ⟨σ, tt, hcompat, hnew, hrange⟩ :=
    chain_extend p (M * p) (p ^ a) ζ hζtop (chainField M p a) σa (p ^ a)
      (mem_chainField M p (le_refl a)) (hnot a (le_refl a)) ta hatop' harange'
      (chainField M p (a + 1)) (chainField_succ M p a)
  refine ⟨σ, ta, tt, ?_, ?_, hrange⟩
  · exact (hcompat ⟨qExpand ℚ (p ^ a) jq, mem_chainField M p (le_refl a)⟩
      (mem_chainField M p (Nat.le_succ a))).trans hatop'
  · have hx : qExpand ℚ (p ^ a * p) jq ∈ chainField M p (a + 1) := by
      rw [qExpand_congr (pow_succ p a).symm jq]
      exact mem_chainField M p (le_refl (a + 1))
    have hm : (⟨qExpand ℚ (p ^ (a + 1)) jq, mem_chainField M p (le_refl (a + 1))⟩ :
        chainField M p (a + 1)) = ⟨qExpand ℚ (p ^ a * p) jq, hx⟩ :=
      Subtype.ext (qExpand_congr (pow_succ p a) jq)
    rw [hm]
    exact hnew hx

end
end Dubon2026.SourceFunctionField.PrimePowerNonmembership
