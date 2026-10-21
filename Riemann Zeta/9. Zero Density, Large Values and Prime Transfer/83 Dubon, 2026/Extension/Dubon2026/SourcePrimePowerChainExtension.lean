import Dubon2026.SourcePrimePowerChainFields

/-! DUB-17/18 -> numerical modular genus -> all-level degree
-> original next-series nonmembership. This is the exact phase-indexed
embedding step for the original prime-power tower. The previously proved
actual twisted extension supplies the embedding; elementary exponent
identities express the new phase in the fixed larger root system.
-/
namespace Dubon2026.SourceFunctionField.PrimePowerNonmembership
noncomputable section
open PrimeDegreeAux
variable {K : Type*} [Field K] [Algebra ℚ K] [IsAlgClosed K]

theorem chain_extend (p e s : ℕ) [hp : Fact p.Prime] [NeZero e] [NeZero s]
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) (p * e * s))
    (F : IntermediateField ℚ (LaurentSeries ℚ)) (σ : F →+* LaurentSeries K)
    (d : ℕ) [NeZero d] (hd : qExpand ℚ d jq ∈ F)
    (hnot : qExpand ℚ (d * p) jq ∉ F) (t : ℕ)
    (hσd : σ ⟨qExpand ℚ d jq, hd⟩ = TS K (p * e) (ζ ^ (t * (p * e))))
    (hrange : ∀ y : F, σ y ∈ (qExpand K (p * e)).range)
    (G : IntermediateField ℚ (LaurentSeries ℚ))
    (hG : G = IntermediateField.adjoin ℚ
      ((F : Set (LaurentSeries ℚ)) ∪ {qExpand ℚ (d * p) jq})) :
    ∃ (σ' : G →+* LaurentSeries K) (t' : ℕ),
      (∀ (z : F) (hz : (z : LaurentSeries ℚ) ∈ G), σ' ⟨z, hz⟩ = σ z) ∧
      (∀ hx : qExpand ℚ (d * p) jq ∈ G,
        σ' ⟨qExpand ℚ (d * p) jq, hx⟩ = TS K e (ζ ^ (t' * e))) ∧
      ∀ y : G, σ' y ∈ (qExpand K e).range := by
  subst G
  have hpN : p ∣ p * e * s := ⟨e * s, by ring⟩
  have hdiv : p * e * s / p = e * s := by
    rw [show p * e * s = p * (e * s) by ring, Nat.mul_div_cancel_left _ hp.out.pos]
  have hu : ζ ^ (t * (p * e)) = (ζ ^ (t * e)) ^ p := by
    rw [← pow_mul]
    congr 1
    ring
  have hseed : σ ⟨qExpand ℚ d jq, hd⟩ = TS K (e * p) ((ζ ^ (t * e)) ^ p) := by
    rw [hσd, hu]
    exact TS_congr (Nat.mul_comm p e) _
  have hr : ∀ y : F, σ y ∈ (qExpand K (e * p)).range := by
    intro y
    simpa only [Nat.mul_comm p e] using hrange y
  obtain ⟨τ, c, _, hbase, hnew, hτrange⟩ :=
    extend_actual_embedding_at_prime_twist (p * e * s) ζ hζ p hpN
      F σ d hd hnot e (ζ ^ (t * e)) hseed hr
  refine ⟨τ, t + c * s, hbase, ?_, hτrange⟩
  intro hx
  rw [hnew hx, hdiv]
  congr 1
  rw [← pow_mul, ← pow_add]
  congr 1
  ring

end
end Dubon2026.SourceFunctionField.PrimePowerNonmembership
