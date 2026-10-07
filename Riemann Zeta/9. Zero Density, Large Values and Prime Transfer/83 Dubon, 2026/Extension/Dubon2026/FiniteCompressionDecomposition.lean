import Dubon2026.FiniteCompressedProducts

/-! # The finite orthogonal-compression decomposition behind support-to-oldspace -/

namespace Dubon2026

section Algebra
variable {M I : Type*} [Monoid M]

/-- An idempotent commutes with every compression by itself. -/
theorem compression_commute_idempotent {e : M} (he : IsIdempotentElem e) (a : M) :
    Commute (e * a * e) e := by
  change (e * a * e) * e = e * (e * a * e)
  calc
    (e * a * e) * e = (e * a) * (e * e) := mul_assoc _ _ _
    _ = e * a * e := by rw [he.eq]
    _ = e * (e * a * e) := by rw [← mul_assoc e (e * a) e, ← mul_assoc e e a, he.eq]

/-- Every factor fixes the range of the product of commuting idempotents. -/
theorem idempotent_mul_noncommProd (s : Finset I) (e : I → M)
    (hee : Set.Pairwise (↑s) (fun i j => Commute (e i) (e j)))
    (hid : ∀ i ∈ s, IsIdempotentElem (e i)) (i : I) (hi : i ∈ s) :
    e i * s.noncommProd e hee = s.noncommProd e hee := by
  classical
  rw [← s.mul_noncommProd_erase hi e hee, ← mul_assoc, (hid i hi).eq]

end Algebra

noncomputable section
variable {I V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- Pairwise commuting projections have pairwise commuting complements. -/
theorem pairwise_projection_complements (s : Finset I) (p : I → V →ₗ[ℂ] V)
    (hpp : Set.Pairwise (↑s) (fun i j => Commute (p i) (p j))) :
    Set.Pairwise (↑s) (fun i j => Commute (1 - p i) (1 - p j)) := by
  intro i hi j hj hij
  exact (Commute.one_left _).sub_left ((Commute.one_right _).sub_right (hpp hi hj hij))

/-- A vector in the common invariant range, killed by the product of projection complements,
lies in the sum of the individual fixed spaces inside that same invariant range.
Only operators at different indices are required to commute. -/
theorem finite_orthogonal_compression_decomposition [FiniteDimensional ℂ V]
    (s : Finset I) (e p : I → V →ₗ[ℂ] V)
    (he : ∀ i ∈ s, (e i).IsSymmetricProjection)
    (hp : ∀ i ∈ s, (p i).IsSymmetricProjection)
    (hee : Set.Pairwise (↑s) (fun i j => Commute (e i) (e j)))
    (hpp : Set.Pairwise (↑s) (fun i j => Commute (p i) (p j)))
    (hep : Set.Pairwise (↑s) (fun i j => Commute (e i) (p j))) :
    LinearMap.ker (s.noncommProd (fun i => 1 - p i) (pairwise_projection_complements s p hpp)) ⊓
      LinearMap.range (s.noncommProd e hee) ≤
        ⨆ i ∈ s, LinearMap.ker (1 - p i) ⊓ LinearMap.range (s.noncommProd e hee) := by
  classical
  let a : I → V →ₗ[ℂ] V := fun i => 1 - p i
  let A : I → V →ₗ[ℂ] V := fun i => e i * a i * e i
  let E := s.noncommProd e hee
  have ha : Set.Pairwise (↑s) (fun i j => Commute (a i) (a j)) :=
    pairwise_projection_complements s p hpp
  have hea : Set.Pairwise (↑s) (fun i j => Commute (e i) (a j)) :=
    fun _ hi _ hj hij => (Commute.one_right _).sub_right (hep hi hj hij)
  have hAA : Set.Pairwise (↑s) (fun i j => Commute (A i) (A j)) :=
    pairwise_compressed_operators s e a hee ha hea
  have hAs : ∀ i ∈ s, (A i).IsSymmetric := by
    intro i hi
    exact symmetric_compression (he i hi).isSymmetric
      (LinearMap.IsSymmetric.one.sub (hp i hi).isSymmetric)
  have hEi : IsIdempotentElem E :=
    noncommProd_idempotent s e hee (fun i hi => (he i hi).isIdempotentElem)
  have hAE : ∀ i ∈ s, Commute (A i) E := by
    intro i hi
    apply s.noncommProd_commute
    intro j hj
    by_cases hij : i = j
    · subst j
      exact compression_commute_idempotent (he i hi).isIdempotentElem (a i)
    · exact ((hee hi hj hij).mul_left
        (hea hj hi (Ne.symm hij)).symm).mul_left (hee hi hj hij)
  have hEiE : ∀ i ∈ s, e i * E = E :=
    fun i hi => idempotent_mul_noncommProd s e hee (fun j hj => (he j hj).isIdempotentElem) i hi
  have hle : (⨆ i ∈ s, LinearMap.ker (A i) ⊓ LinearMap.range E) ≤
      ⨆ i ∈ s, LinearMap.ker (1 - p i) ⊓ LinearMap.range E := by
    apply iSup_le
    intro i
    apply iSup_le
    intro hi
    exact (compressed_kernel_common_range (he i hi).isSymmetric (hp i hi) (hEiE i hi)).trans
      (le_iSup_of_le i (le_iSup_of_le hi le_rfl))
  rintro x ⟨hx, hxE⟩
  have hEx : E x = x := by
    obtain ⟨y, rfl⟩ := hxE
    exact LinearMap.congr_fun hEi y
  have hAx : x ∈ LinearMap.ker (s.noncommProd A hAA) := by
    change (s.noncommProd (fun i => e i * a i * e i) hAA) x = 0
    rw [noncommProd_compressions s e a hee ha hea]
    change E ((s.noncommProd a ha) (E x)) = 0
    rw [hEx, show (s.noncommProd a ha) x = 0 from hx, map_zero]
  exact hle (symmetric_product_kernel_inf_range s A E hAA hAs hEi hAE ⟨hAx, hxE⟩)

end
end Dubon2026
