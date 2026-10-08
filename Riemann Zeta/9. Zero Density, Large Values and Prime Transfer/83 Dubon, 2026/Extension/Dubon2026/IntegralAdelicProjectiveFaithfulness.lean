import Dubon2026.RationalProjectiveLevelIntersection

/-! # The actual faithful integral projective arithmetic action and exact level intersection -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

/-- Original extension of integer special-linear matrices to the real place is injective on their literal entries. -/
theorem integralToRealSL_injective : Function.Injective integralToRealSL := by
  intro a b h
  apply Subtype.ext
  funext i j
  have he := congrArg (fun g : SL(2, ℝ) => g i j) h
  change ((a i j : ℤ) : ℝ) = ((b i j : ℤ) : ℝ) at he
  exact Int.cast_injective he

/-- The actual original integral projective group embeds faithfully at the real place. -/
theorem integralToRealPSL_injective : Function.Injective integralToRealPSL := by
  have hk (a : PSL(2, ℤ)) (ha : integralToRealPSL a = 1) : a = 1 := by
    obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective a
    rw [integralToRealPSL_mk] at ha
    have hc := (QuotientGroup.eq_one_iff (integralToRealSL σ)).mp ha
    rcases (realSL2_center_eq_signs (integralToRealSL σ)).mp hc with hs | hs
    · have hσ : σ = 1 := integralToRealSL_injective (hs.trans (map_one integralToRealSL).symm)
      rw [hσ]
      exact map_one (QuotientGroup.mk' _)
    · have hσ : σ = -1 := integralToRealSL_injective (hs.trans integralToRealSL_neg_one.symm)
      rw [hσ]
      apply (QuotientGroup.eq_one_iff _).mpr
      exact Subgroup.mem_center_iff.mpr (fun h => by simp)
  intro a b he
  have h : integralToRealPSL (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, he, inv_mul_cancel]
  exact inv_mul_eq_one.mp (hk _ h)

/-- The actual diagonal integral projective action in the real and finite coordinates is faithful. -/
theorem integralToAdelicProjective_injective : Function.Injective integralToAdelicProjective := by
  intro a b he
  exact integralToRealPSL_injective (congrArg Prod.fst he)

/-- Every original integral Gamma0 matrix has its actual finite projective component in the original finite level image. -/
theorem integralToAdelicProjective_finite_level (N : ℕ) [NeZero N] (σ : Gamma0 N) :
    (integralToAdelicProjective (QuotientGroup.mk σ.val)).2 ∈ finiteProjectiveGL2Level N := by
  have hm : toGL (Matrix.SpecialLinearGroup.map (Int.castRingHom (FiniteAdeleRing ℤ ℚ)) σ.val) ∈
      finiteAdeleGL2Gamma0 N :=
    finiteAdeleGamma0_toGL_mem N _ ((integralSL2_mem_finiteAdeleGamma0 N σ.val).mpr σ.property)
  refine ⟨_, hm, ?_⟩
  change ProjGenLinGroup.mk (toGL (Matrix.SpecialLinearGroup.map (Int.castRingHom (FiniteAdeleRing ℤ ℚ)) σ.val)) =
    ProjGenLinGroup.mk (GeneralLinearGroup.map (Int.castRingHom (FiniteAdeleRing ℤ ℚ)) (toGL σ.val))
  rw [generalLinear_map_toGL]

/-- The actual rational arithmetic group's finite level intersection is exactly the original embedded integral Gamma0 projective image. -/
theorem adelicProjectiveArithmetic_level_iff (N : ℕ) [NeZero N] (γ : adelicProjectiveArithmetic) :
    γ.val.2 ∈ finiteProjectiveGL2Level N ↔
      ∃ σ : Gamma0 N, integralToAdelicProjective (QuotientGroup.mk σ.val) = γ.val := by
  constructor
  · intro hγ
    obtain ⟨a, ha⟩ := γ.property
    have hlevel : ProjGenLinGroup.mk (rationalPositiveGL2ToFinite a) ∈ finiteProjectiveGL2Level N := by
      change (rationalPositiveToAdelicProjective a).2 ∈ finiteProjectiveGL2Level N
      rw [ha]
      exact hγ
    obtain ⟨σ, hσ⟩ := rationalPositiveToAdelicProjective_level_intersection N a hlevel
    exact ⟨σ, hσ.symm.trans ha⟩
  · rintro ⟨σ, hσ⟩
    rw [← hσ]
    exact integralToAdelicProjective_finite_level N σ

end
end Dubon2026
