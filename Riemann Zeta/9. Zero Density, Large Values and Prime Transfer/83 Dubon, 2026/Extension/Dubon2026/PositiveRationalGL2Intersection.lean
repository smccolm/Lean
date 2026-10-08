import Dubon2026.FiniteAdelicGL2Factorization
import Dubon2026.FiniteAdeleClassicalIntersection

/-! # The exact positive rational classical intersection for the actual adelic GL2 level group -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix
open scoped MatrixGroups

/-- The determinant of an actual integral level matrix is everywhere integral. -/
theorem finiteAdeleLevelMatrix_det_mem (N : ℕ)
    (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing ℤ ℚ)) (hg : finiteAdeleLevelMatrix N g) :
    Matrix.det g ∈ finiteAdeleIntegerSubring := by
  rw [Matrix.det_fin_two]
  exact finiteAdeleIntegerSubring.sub_mem
    (finiteAdeleIntegerSubring.mul_mem (hg.1 0 0) (hg.1 1 1))
    (finiteAdeleIntegerSubring.mul_mem (hg.1 0 1) (hg.1 1 0))

/-- A positive rational scalar integral together with its inverse at every finite place is one. -/
theorem positive_rational_eq_one_of_adelic_integral {q : ℚ} (hq : 0 < q)
    (h : algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q ∈ finiteAdeleIntegerSubring)
    (hi : algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q⁻¹ ∈ finiteAdeleIntegerSubring) : q = 1 := by
  obtain ⟨n, hn⟩ := (finiteAdele_rational_integral_iff q).mp h
  obtain ⟨m, hm⟩ := (finiteAdele_rational_integral_iff q⁻¹).mp hi
  have hnm : n * m = 1 := by
    apply Int.cast_injective (α := ℚ)
    rw [Int.cast_mul, Int.cast_one, hn, hm, mul_inv_cancel₀ (ne_of_gt hq)]
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hnm with hpos | hneg
  · simpa only [hpos, Int.cast_one] using hn.symm
  · have hqneg : q = -1 := by simpa only [hneg, Int.cast_neg, Int.cast_one] using hn.symm
    rw [hqneg] at hq
    norm_num at hq

/-- The original rational matrix's determinant is integral when its finite adelic matrix lies in the integral level order. -/
theorem rationalGL2_level_det_integral (N : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin 2) ℚ)
    (hg : finiteAdeleLevelMatrix N
      (Matrix.GeneralLinearGroup.map (algebraMap ℚ (FiniteAdeleRing ℤ ℚ)) g).val) :
    algebraMap ℚ (FiniteAdeleRing ℤ ℚ) (Matrix.GeneralLinearGroup.det g).val ∈
      finiteAdeleIntegerSubring := by
  have h := finiteAdeleLevelMatrix_det_mem N _ hg
  change Matrix.det ((algebraMap ℚ (FiniteAdeleRing ℤ ℚ)).mapMatrix g.val) ∈ _ at h
  rw [← RingHom.map_det] at h
  exact h

/-- An original positive rational matrix in the actual finite level group has determinant exactly one. -/
theorem positiveRationalGL2_level_det_one (N : ℕ) (g : GL(2, ℚ)⁺)
    (hg : Matrix.GeneralLinearGroup.map (algebraMap ℚ (FiniteAdeleRing ℤ ℚ)) g.val ∈
      finiteAdeleGL2Gamma0 N) : (Matrix.GeneralLinearGroup.det g.val).val = 1 := by
  apply positive_rational_eq_one_of_adelic_integral g.property
    (rationalGL2_level_det_integral N g.val hg.1)
  have hi := rationalGL2_level_det_integral N g.val⁻¹
    (by simpa only [map_inv] using hg.2)
  simpa only [map_inv, Units.val_inv_eq_inv_val] using hi

/-- The actual positive rational GL2 intersection is precisely the original embedded classical Gamma0 subgroup. -/
theorem positiveRationalGL2_mem_finiteAdeleGamma0_iff (N : ℕ) [NeZero N] (g : GL(2, ℚ)⁺) :
    Matrix.GeneralLinearGroup.map (algebraMap ℚ (FiniteAdeleRing ℤ ℚ)) g.val ∈
      finiteAdeleGL2Gamma0 N ↔
    ∃ γ : CongruenceSubgroup.Gamma0 N,
      Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ)
        (Matrix.SpecialLinearGroup.toGL γ.val) = g.val := by
  have hmap (γ : SL(2, ℤ)) :
      Matrix.GeneralLinearGroup.map (algebraMap ℚ (FiniteAdeleRing ℤ ℚ))
        (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) (Matrix.SpecialLinearGroup.toGL γ)) =
      Matrix.SpecialLinearGroup.toGL
        (Matrix.SpecialLinearGroup.map (Int.castRingHom (FiniteAdeleRing ℤ ℚ)) γ) := by
    apply Units.ext
    funext i j
    exact map_intCast (algebraMap ℚ (FiniteAdeleRing ℤ ℚ)) (γ i j)
  constructor
  · intro hg
    let s : SL(2, ℚ) := ⟨g.val.val, positiveRationalGL2_level_det_one N g hg⟩
    have hs : Matrix.SpecialLinearGroup.toGL s = g.val := by apply Units.ext; rfl
    have hSL : Matrix.SpecialLinearGroup.map (algebraMap ℚ (FiniteAdeleRing ℤ ℚ)) s ∈
        finiteAdeleGamma0 N := hg.1
    obtain ⟨γ, hγ⟩ := (rationalSL2_mem_finiteAdeleGamma0_iff N s).mp hSL
    refine ⟨γ, ?_⟩
    rw [generalLinear_map_toGL, hγ, hs]
  · rintro ⟨γ, hγ⟩
    rw [← hγ, hmap]
    exact finiteAdeleGamma0_toGL_mem N _
      ((integralSL2_mem_finiteAdeleGamma0 N γ.val).mpr γ.property)

end
end Dubon2026
