import Dubon2026.SourceResidueConjugateRangeEmbedding

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> exact
all-level residue degree -> coprime prime nonmembership. Adapt local SourceCoprimePrimeImage
to actual coefficient-field j series and divisor fields. Lower generation and
conjugate products are explicit induction inputs. Expansion-range preservation
forces each image of j_p to the distinguished branch; bounded polynomial
descent contradicts the already proved prime nonmembership in K(j).
The level and prime must remain nonzero in the coefficient field. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField PrimeDegreeAux PrimePowerNonmembership
variable {K : Type*} [Field K]

theorem residue_relationAtSeed_eval_subfield_map
    (P : Polynomial (Polynomial ℤ))
    (F : IntermediateField K (LaurentSeries K)) (σ : F →+* LaurentSeries K)
    (x y : F) (h : (relationAtSeed P (x : LaurentSeries K)).eval (y : LaurentSeries K) = 0) :
    (relationAtSeed P (σ x)).eval (σ y) = 0 := by
  have hF : (relationAtSeed P x).eval y = 0 := by
    apply (algebraMap F (LaurentSeries K)).injective
    rw [map_zero, ← Polynomial.eval₂_hom, ← Polynomial.eval_map, relationAtSeed_map]
    exact h
  have h' := congrArg σ hF
  rw [map_zero, ← Polynomial.eval₂_hom, ← Polynomial.eval_map, relationAtSeed_map] at h'
  exact h'

theorem residue_prime_j_image_of_coprime_expansion_range [IsAlgClosed K]
    (M p : ℕ) [NeZero M] [hp : Fact p.Prime]
    (hpM : ¬ p ∣ M) (hpK : (p : K) ≠ 0) (F : IntermediateField K (LaurentSeries K))
    (hj : (jqModC K) ∈ F) (hjp : qExpand K p (jqModC K) ∈ F) (σ : F →+* LaurentSeries K)
    (hσj : σ ⟨(jqModC K), hj⟩ = TS K (M * p) 1)
    (hrange : σ ⟨qExpand K p (jqModC K), hjp⟩ ∈ (qExpand K p).range) :
    σ ⟨qExpand K p (jqModC K), hjp⟩ = TS K (M * p * p) 1 := by
  haveI : NeZero (p : K) := ⟨hpK⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K p
  have hu := hz.isUnit (NeZero.ne p)
  have hζ : IsPrimitiveRoot (hu.unit : K) p := by rw [hu.unit_spec]; exact hz
  let ζ := hu.unit
  obtain ⟨P, hPm, _, hrels, hP⟩ := exists_residue_prime_compatible_relations K p ζ hζ
  have hrel : (relationAtSeed P (jqModC K)).eval (qExpand K p (jqModC K)) = 0 := by
    simpa only [one_mul, qExpand_one_apply] using (hrels 1).1
  have h := residue_relationAtSeed_eval_subfield_map P F σ ⟨(jqModC K), hj⟩ ⟨qExpand K p (jqModC K), hjp⟩ hrel
  rw [hσj] at h
  have hroot : σ ⟨qExpand K p (jqModC K), hjp⟩ = TS K (M * (p * p)) 1 ∨
      ∃ b < p, σ ⟨qExpand K p (jqModC K), hjp⟩ = TS K M (ζ ^ b) := by
    have h' := residue_prime_root_iff_of_root_list p M ζ 1 P hPm (hP M 1).1 (σ ⟨qExpand K p (jqModC K), hjp⟩)
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
