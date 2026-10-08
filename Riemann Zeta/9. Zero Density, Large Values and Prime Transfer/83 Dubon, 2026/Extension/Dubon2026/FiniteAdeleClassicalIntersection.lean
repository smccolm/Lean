import Dubon2026.FiniteAdeleLevelSubgroup
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

/-! # The exact classical intersection of the finite adelic level subgroup -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

/-- A rational finite adele is everywhere integral precisely when its original rational is an integer. -/
theorem finiteAdele_rational_integral_iff (q : ℚ) :
    algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q ∈ finiteAdeleIntegerSubring ↔
      ∃ n : ℤ, (n : ℚ) = q := by
  constructor
  · intro h
    apply mem_integers_of_valuation_le_one (R := ℤ) ℚ q
    intro v
    have hv := h v
    change Valued.v (algebraMap ℚ (v.adicCompletion ℚ) q) ≤ 1 at hv
    simpa only [algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self_apply, valuedAdicCompletion_eq_valuation'] using hv
  · rintro ⟨n, rfl⟩
    simp only [map_intCast]
    simp

/-- An actual rational determinant-one matrix integral at every finite place has an integral lift. -/
theorem rationalSL2_integral_lift (g : SL(2, ℚ))
    (hg : ∀ i j, algebraMap ℚ (FiniteAdeleRing ℤ ℚ) (g i j) ∈ finiteAdeleIntegerSubring) :
    ∃ γ : SL(2, ℤ), Matrix.SpecialLinearGroup.map (Int.castRingHom ℚ) γ = g := by
  choose a ha using (fun i j => (finiteAdele_rational_integral_iff (g i j)).mp (hg i j))
  have hd : Matrix.det a = 1 := by
    apply Int.cast_injective (α := ℚ)
    change (Int.castRingHom ℚ) (Matrix.det a) = (1 : ℚ)
    rw [(Int.castRingHom ℚ).map_det]
    have hm : (Int.castRingHom ℚ).mapMatrix a = g.val := by
      funext i j
      exact ha i j
    rw [hm]
    exact g.property
  refine ⟨⟨a, hd⟩, ?_⟩
  apply Subtype.ext
  funext i j
  exact ha i j

/-- On the original integral matrix, finite adelic level membership is exactly classical Gamma0 membership. -/
theorem integralSL2_mem_finiteAdeleGamma0 (N : ℕ) [NeZero N] (γ : SL(2, ℤ)) :
    Matrix.SpecialLinearGroup.map (Int.castRingHom (FiniteAdeleRing ℤ ℚ)) γ ∈
      finiteAdeleGamma0 N ↔ γ ∈ CongruenceSubgroup.Gamma0 N := by
  have hN : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hint : ∀ i j, ((γ i j : ℤ) : FiniteAdeleRing ℤ ℚ) ∈ finiteAdeleIntegerSubring :=
    fun i j => by simp
  change ((∀ i j, ((γ i j : ℤ) : FiniteAdeleRing ℤ ℚ) ∈ finiteAdeleIntegerSubring) ∧
    finiteAdeleLevelMultiple N ((γ 1 0 : ℤ) : FiniteAdeleRing ℤ ℚ)) ↔ _
  rw [and_iff_right hint, finiteAdeleLevelMultiple_iff]
  have heq : algebraMap ℚ (FiniteAdeleRing ℤ ℚ) ((N : ℚ)⁻¹) *
      ((γ 1 0 : ℤ) : FiniteAdeleRing ℤ ℚ) =
      algebraMap ℚ (FiniteAdeleRing ℤ ℚ) ((N : ℚ)⁻¹ * (γ 1 0 : ℚ)) := by
    simp only [map_mul, map_intCast]
  rw [heq, finiteAdele_rational_integral_iff, CongruenceSubgroup.Gamma0_mem,
    ZMod.intCast_zmod_eq_zero_iff_dvd]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    apply Int.cast_injective (α := ℚ)
    simp only [Int.cast_mul, Int.cast_natCast]
    rw [hm, ← mul_assoc, mul_inv_cancel₀ hN, one_mul]
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    rw [hm, Int.cast_mul, Int.cast_natCast, ← mul_assoc, inv_mul_cancel₀ hN, one_mul]

/-- The rational intersection of the actual finite adelic level subgroup is exactly the original classical subgroup. -/
theorem rationalSL2_mem_finiteAdeleGamma0_iff (N : ℕ) [NeZero N] (g : SL(2, ℚ)) :
    Matrix.SpecialLinearGroup.map (algebraMap ℚ (FiniteAdeleRing ℤ ℚ)) g ∈
      finiteAdeleGamma0 N ↔
    ∃ γ : CongruenceSubgroup.Gamma0 N,
      Matrix.SpecialLinearGroup.map (Int.castRingHom ℚ) γ.val = g := by
  have hmap (γ : SL(2, ℤ)) :
      Matrix.SpecialLinearGroup.map (algebraMap ℚ (FiniteAdeleRing ℤ ℚ))
        (Matrix.SpecialLinearGroup.map (Int.castRingHom ℚ) γ) =
      Matrix.SpecialLinearGroup.map (Int.castRingHom (FiniteAdeleRing ℤ ℚ)) γ := by
    apply Subtype.ext
    funext i j
    exact map_intCast (algebraMap ℚ (FiniteAdeleRing ℤ ℚ)) (γ i j)
  constructor
  · intro hg
    obtain ⟨γ, hγ⟩ := rationalSL2_integral_lift g hg.1
    have hlevel : γ ∈ CongruenceSubgroup.Gamma0 N := by
      apply (integralSL2_mem_finiteAdeleGamma0 N γ).mp
      rw [← hmap, hγ]
      exact hg
    exact ⟨⟨γ, hlevel⟩, hγ⟩
  · rintro ⟨γ, rfl⟩
    rw [hmap]
    exact (integralSL2_mem_finiteAdeleGamma0 N γ.val).mpr γ.property

end
end Dubon2026
