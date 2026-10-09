import Dubon2026.FiniteAdeleClassicalIntersection

/-! # The original integral Gamma0 group is dense in its actual finite special-linear level subgroup -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

/-- Rational strong approximation and the exact classical intersection prove density of the original integral Gamma0 matrices throughout the genuine finite special-linear level subgroup. -/
theorem integralGamma0_finite_dense (N : ℕ) [NeZero N]
    (g : SL(2, FiniteAdeleRing ℤ ℚ)) (hg : g ∈ finiteAdeleGamma0 N) :
    g ∈ closure (Set.range (fun γ : Gamma0 N =>
      Matrix.SpecialLinearGroup.map (Int.castRingHom (FiniteAdeleRing ℤ ℚ)) γ.val)) := by
  have hh := rationalSL2_dense_finiteAdeles.subset_closure_image_preimage_of_isOpen
    (finiteAdeleGamma0_isOpen N)
  apply closure_mono (t := Set.range (fun γ : Gamma0 N =>
    Matrix.SpecialLinearGroup.map (Int.castRingHom (FiniteAdeleRing ℤ ℚ)) γ.val)) ?_ (hh hg)
  rintro _ ⟨q, hq, rfl⟩
  obtain ⟨γ, hγ⟩ := (rationalSL2_mem_finiteAdeleGamma0_iff N q).mp hq
  refine ⟨γ, ?_⟩
  rw [← hγ]
  apply Subtype.ext
  funext i j
  exact (map_intCast (algebraMap ℚ (FiniteAdeleRing ℤ ℚ)) (γ.val i j)).symm

end
end Dubon2026
