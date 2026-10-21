import Dubon2026.SourceOriginalConjugateRangeEmbedding

/-! DUB-17/18 -> numerical modular genus -> composite degree -> coprime
prime nonmembership. The actual prime relation forces the image of j_p
under an expansion-preserving embedding: every finite twisted branch has
leading exponent M, forbidden in the p-expansion range when p does not
divide M. Only the distinguished branch survives. Reusing the actual
prime relation avoids a second prime minimal-polynomial conjugate proof.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField PrimeDegreeAux PrimePowerNonmembership
variable {K : Type*} [Field K] [Algebra ℚ K] [IsAlgClosed K]

theorem prime_j_image_of_coprime_expansion_range (M p : ℕ) [NeZero M] [hp : Fact p.Prime]
    (hpM : ¬ p ∣ M) (F : IntermediateField ℚ (LaurentSeries ℚ))
    (hj : jq ∈ F) (hjp : qExpand ℚ p jq ∈ F) (σ : F →+* LaurentSeries K)
    (hσj : σ ⟨jq, hj⟩ = TS K (M * p) 1)
    (hrange : σ ⟨qExpand ℚ p jq, hjp⟩ ∈ (qExpand K p).range) :
    σ ⟨qExpand ℚ p jq, hjp⟩ = TS K (M * p * p) 1 := by
  obtain ⟨ζ, P, _, _, _, hP⟩ := exists_prime_product_algClosed p K
  have hrel := relationAtSeed_jq_eval P (prime_product_forward_root p K ζ P hP)
  have h := relationAtSeed_eval_subfield_map P F σ ⟨jq, hj⟩ ⟨qExpand ℚ p jq, hjp⟩ hrel
  rw [hσj] at h
  have hroot : σ ⟨qExpand ℚ p jq, hjp⟩ = TS K (M * (p * p)) 1 ∨
      ∃ b < p, σ ⟨qExpand ℚ p jq, hjp⟩ = TS K M (ζ ^ b) := by
    have h' := prime_twisted_product_root_iff p ζ P hP M 1 (σ ⟨qExpand ℚ p jq, hjp⟩)
    simp only [one_pow, one_mul] at h'
    exact h'.mp h
  rcases hroot with he | ⟨b, _, he⟩
  · exact he.trans (TS_congr (Nat.mul_assoc M p p).symm 1)
  · exfalso
    apply TS_not_mem_range_qExpand (r := p) (e := M) (by
      rwa [Int.natCast_dvd_natCast]) (ζ ^ b)
    rwa [← he]

end
end Dubon2026.SourceFunctionField
