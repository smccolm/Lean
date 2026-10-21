import Dubon2026.SourceCurveFiberDegreeSum
import Dubon2026.SourceCurveResiduePullback
import Dubon2026.SourceCurveResidueSumEquiv

/-! DUB-17/18 -> original global residue identity -> normal-closure descent.
Finite actual residue sums can be reindexed by restriction fibers. This is
the finite-support part of the pullback degree formula, adapted from the
fiber reindexing argument in S_AlgebraicCurve_residueTheoremK_of_isAlgClosed,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. No completion is introduced.
-/
namespace Dubon2026.SourceCurve
noncomputable section

theorem finsum_eq_fiber_finsum {A B M : Type*} [AddCommMonoid M]
    (r : A → B) (g : A → M) (hg : (Function.support g).Finite) :
    ∑ᶠ w, g w = ∑ᶠ v : B, ∑ᶠ w : {w // r w = v}, g w.1 := by
  classical
  let S := hg.toFinset
  let T := S.image r
  have hfib (v : B) : (∑ᶠ w : {w // r w = v}, g w.1) =
      ∑ w ∈ S with r w = v, g w := by
    rw [finsum_subtype_eq_finsum_cond]
    apply finsum_cond_eq_sum_of_cond_iff
    intro w hw
    simp only [Finset.mem_filter, S, hg.mem_toFinset.mpr hw, true_and]
  simp_rw [hfib]
  have hsup : Function.support (fun v => ∑ w ∈ S with r w = v, g w) ⊆ ↑T := by
    intro v hv
    obtain ⟨w, hw, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv
    exact Finset.mem_image.mpr ⟨w, (Finset.mem_filter.mp hw).1,
      (Finset.mem_filter.mp hw).2⟩
  rw [finsum_eq_sum_of_support_subset _ hsup, finsum_eq_sum g hg]
  exact (Finset.sum_fiberwise_of_maps_to
    (fun w hw => Finset.mem_image.mpr ⟨w, hw, rfl⟩) g).symm

open KaehlerDifferential
variable {K F E : Type*} [Field K] [Field F] [Field E]
variable [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
variable [FiniteDimensional F E] [Algebra.IsSeparable F E]
variable [CharZero K] [Nontrivial Ω[F⁄K]] [Nontrivial Ω[E⁄K]]
variable [∀ v : Place K F, v.DCoordGenerates]
variable [∀ w : Place K E, w.DCoordGenerates]
variable [∀ w : Place K E, Module.Finite w.toValuationSubring Ω[w.toValuationSubring⁄K]]
variable [∀ w : Place K E, Algebra.IsSeparable K w.ResidueField]

omit [FiniteDimensional F E] in
theorem kaehlerResidueTermKFam_pullback
    (RF : ∀ v : Place K F, v.CanonicalLocalResidueDataK)
    (RE : ∀ w : Place K E, w.CanonicalLocalResidueDataK)
    (hF : ∀ v : Place K F, Function.Bijective (algebraMap K v.ResidueField))
    (hE : ∀ w : Place K E, Function.Bijective (algebraMap K w.ResidueField))
    (ω : Ω[F⁄K]) (f : F) (w : Place K E) :
    kaehlerResidueTermKFam RE (KaehlerDifferential.map K K F E ω)
      (diagonalHom K E (algebraMap F E f)) w =
      (w.ord (algebraMap F E (w.restrict F).uniformizer) : K) *
        kaehlerResidueTermKFam RF ω (diagonalHom K F f) (w.restrict F) := by
  simp only [kaehlerResidueTermKFam_apply]
  rw [w.trace_canonicalResidue_eq_scalar (RE w) (hE w),
    (w.restrict F).trace_canonicalResidue_eq_scalar (RF _) (hF _)]
  have h := w.localResidueScalar_map_restrict (hF _).surjective (hE w).surjective (f • ω)
  rw [map_smul, ← algebraMap_smul E f, w.differentialCoeff_smul,
    (w.restrict F).differentialCoeff_smul] at h
  simpa only [smul_eq_mul] using h

end
end Dubon2026.SourceCurve
