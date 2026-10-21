import Dubon2026.SourceLaurentSimpleEmbedding

/-! DUB-17/18 -> numerical modular genus -> all-level degree
-> next-series nonmembership -> lowering the expansion range in a tower
of original prime-power fields. The needed twisted root is derived from
the actual prime relation and nonmembership. Native simple-extension
transport gives an embedding of the literal field adjoin, with its image
in the smaller expansion range and explicit compatibility on the base.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial PrimeDegreeAux
variable {K : Type*} [Field K] [Algebra ℚ K]

theorem extend_embedding_at_prime_twist
    (p : ℕ) [Fact p.Prime] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p)
    (R : Polynomial (Polynomial ℤ)) (hRm : R.Monic)
    (hR : R.map (((coeffEmb K).comp (qExpand ℚ p)).comp evalAtJ) =
      PhiGen.phiProd p (PhiGen.conj p ζ))
    (F : IntermediateField ℚ (LaurentSeries ℚ)) (σ : F →+* LaurentSeries K)
    (d : ℕ) [NeZero d] (hd : qExpand ℚ d jq ∈ F)
    (hnot : qExpand ℚ (d * p) jq ∉ F)
    (e : ℕ) [NeZero e] (u : Kˣ)
    (hσd : σ ⟨qExpand ℚ d jq, hd⟩ = TS K (e * p) (u ^ p))
    (hrange : ∀ z : F, σ z ∈ (qExpand K (e * p)).range) :
    let G := IntermediateField.adjoin ℚ
      ((F : Set (LaurentSeries ℚ)) ∪ {qExpand ℚ (d * p) jq})
    ∃ (τ : G →+* LaurentSeries K) (c : ℕ), c < p ∧
      (∀ (z : F) (hz : (z : LaurentSeries ℚ) ∈ G), τ ⟨z, hz⟩ = σ z) ∧
      (∀ hxG : qExpand ℚ (d * p) jq ∈ G,
        τ ⟨qExpand ℚ (d * p) jq, hxG⟩ = TS K e (u * ζ ^ c)) ∧
      ∀ z : G, τ z ∈ (qExpand K e).range := by
  intro G
  obtain ⟨hx, c, hc, hy⟩ := exists_prime_twisted_minpoly_root p ζ hζ R hRm hR
    F σ d hd hnot e u hσd
  have hbase : ∀ z : F, σ z ∈ (qExpand K e).range := by
    intro z
    obtain ⟨w, hw⟩ := RingHom.mem_range.mp (hrange z)
    refine RingHom.mem_range.mpr ⟨qExpand K p w, ?_⟩
    rw [qExpand_qExpand]
    exact hw
  have hyRange : TS K e (u * ζ ^ c) ∈ (qExpand K e).range :=
    RingHom.mem_range.mpr ⟨qTwist (u * ζ ^ c) (jqModC K), rfl⟩
  obtain ⟨τ, hτbase, hτroot, hτrange⟩ := extend_simple_embedding_in_expansion_range
    F σ (qExpand ℚ (d * p) jq) hx (TS K e (u * ζ ^ c)) hy e hbase hyRange
  exact ⟨τ, c, hc, hτbase, hτroot, hτrange⟩

theorem extend_actual_embedding_at_prime_twist [IsAlgClosed K]
    (N : ℕ) [NeZero N] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) N)
    (p : ℕ) [Fact p.Prime] (hpN : p ∣ N)
    (F : IntermediateField ℚ (LaurentSeries ℚ)) (σ : F →+* LaurentSeries K)
    (d : ℕ) [NeZero d] (hd : qExpand ℚ d jq ∈ F)
    (hnot : qExpand ℚ (d * p) jq ∉ F)
    (e : ℕ) [NeZero e] (u : Kˣ)
    (hσd : σ ⟨qExpand ℚ d jq, hd⟩ = TS K (e * p) (u ^ p))
    (hrange : ∀ z : F, σ z ∈ (qExpand K (e * p)).range) :
    let G := IntermediateField.adjoin ℚ
      ((F : Set (LaurentSeries ℚ)) ∪ {qExpand ℚ (d * p) jq})
    ∃ (τ : G →+* LaurentSeries K) (c : ℕ), c < p ∧
      (∀ (z : F) (hz : (z : LaurentSeries ℚ) ∈ G), τ ⟨z, hz⟩ = σ z) ∧
      (∀ hxG : qExpand ℚ (d * p) jq ∈ G,
        τ ⟨qExpand ℚ (d * p) jq, hxG⟩ = TS K e (u * (ζ ^ (N / p)) ^ c)) ∧
      ∀ z : G, τ z ∈ (qExpand K e).range := by
  have hη := primitive_root_pow_div hζ hpN
  obtain ⟨R, hm, _, hR⟩ := exists_prime_product_at_root p (ζ ^ (N / p)) hη
  exact extend_embedding_at_prime_twist p (ζ ^ (N / p)) hη R hm hR
    F σ d hd hnot e u hσd hrange

end
end Dubon2026.SourceFunctionField
