import Dubon2026.AdelicProjectiveArithmetic

/-! # Exact rational arithmetic intersections with actual finite projective levels -/

namespace Dubon2026

noncomputable section
open NumberField IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

/-- An original rational scalar unit gives its genuine positive-determinant rational matrix. -/
def rationalPositiveScalar (q : ℚˣ) : GL(2, ℚ)⁺ :=
  ⟨GeneralLinearGroup.scalar (Fin 2) q, by
    change 0 < Matrix.det (Matrix.scalar (Fin 2) q.val)
    simpa only [Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_two, ← pow_two] using
      sq_pos_of_ne_zero (Units.ne_zero q)⟩

/-- The original rational scalar has exactly its actual real positive scalar image. -/
theorem rationalPositiveScalar_real (q : ℚˣ) :
    rationalPositiveGL2ToReal (rationalPositiveScalar q) =
      realPositiveScalar ((q.val : ℚ) : ℝ) (by exact_mod_cast Units.ne_zero q) := by
  apply Subtype.ext
  change GeneralLinearGroup.map (Rat.castHom ℝ) (GeneralLinearGroup.scalar (Fin 2) q) = _
  rw [gl2Scalar_map]
  apply congrArg (GeneralLinearGroup.scalar (Fin 2))
  apply Units.ext
  rfl

/-- The genuine finite image of an original rational scalar is its literal finite scalar matrix. -/
theorem rationalPositiveScalar_finite (q : ℚˣ) :
    rationalPositiveGL2ToFinite (rationalPositiveScalar q) =
      GeneralLinearGroup.scalar (Fin 2)
        (Units.map (algebraMap ℚ (FiniteAdeleRing ℤ ℚ)).toMonoidHom q) :=
  gl2Scalar_map _ q

/-- Every original rational scalar is the identity in the actual real-times-finite projective arithmetic coordinates. -/
theorem rationalPositiveToAdelicProjective_scalar (q : ℚˣ) :
    rationalPositiveToAdelicProjective (rationalPositiveScalar q) = 1 := by
  apply Prod.ext
  · change (QuotientGroup.mk (realPositiveNormalize
      (rationalPositiveGL2ToReal (rationalPositiveScalar q))) : PSL(2, ℝ)) = 1
    rw [rationalPositiveScalar_real, realPositiveNormalize_scalar_projective]
  · change ProjGenLinGroup.mk (rationalPositiveGL2ToFinite (rationalPositiveScalar q)) = 1
    rw [rationalPositiveScalar_finite, ProjGenLinGroup.mk_scalar]

/-- Membership of an original finite rational projective matrix in the actual level image gives an exact original scalar-and-level factorization. -/
theorem rationalPositiveGL2_projective_level_factor (N : ℕ) (γ : GL(2, ℚ)⁺)
    (hγ : ProjGenLinGroup.mk (rationalPositiveGL2ToFinite γ) ∈ finiteProjectiveGL2Level N) :
    ∃ a : (FiniteAdeleRing ℤ ℚ)ˣ, ∃ u : finiteAdeleGL2Gamma0 N,
      rationalPositiveGL2ToFinite γ = GeneralLinearGroup.scalar (Fin 2) a * u.val := by
  obtain ⟨u, hu, he⟩ := hγ
  have hq : (QuotientGroup.mk (rationalPositiveGL2ToFinite γ) : RationalFiniteProjectiveGL2) =
      QuotientGroup.mk u := he.symm
  have hc := QuotientGroup.eq_iff_div_mem.mp hq
  rw [GeneralLinearGroup.center_eq_range_scalar] at hc
  obtain ⟨a, ha⟩ := hc
  refine ⟨a, ⟨u, hu⟩, ?_⟩
  rw [ha, div_mul_cancel]

/-- The actual projective-level intersection of positive rational matrices is represented by the original integral Gamma0 level group, with no projective intersection premise. -/
theorem rationalPositiveToAdelicProjective_level_intersection (N : ℕ) [NeZero N]
    (γ : GL(2, ℚ)⁺)
    (hγ : ProjGenLinGroup.mk (rationalPositiveGL2ToFinite γ) ∈ finiteProjectiveGL2Level N) :
    ∃ σ : Gamma0 N,
      rationalPositiveToAdelicProjective γ = integralToAdelicProjective (QuotientGroup.mk σ.val) := by
  obtain ⟨a, u, ha⟩ := rationalPositiveGL2_projective_level_factor N γ hγ
  obtain ⟨q, hq, w, hw⟩ := finiteIdele_positive_rational_integral_unit a
  let qU : ℚˣ := Units.mk0 q hq.ne'
  let wU : (FiniteAdeleRing ℤ ℚ)ˣ := Units.map finiteAdeleIntegerSubring.subtype.toMonoidHom w
  have haU : a = Units.map (algebraMap ℚ (FiniteAdeleRing ℤ ℚ)).toMonoidHom qU * wU := by
    apply Units.ext
    exact hw
  let δ : GL(2, ℚ)⁺ := (rationalPositiveScalar qU)⁻¹ * γ
  have hδf : rationalPositiveGL2ToFinite δ = GeneralLinearGroup.scalar (Fin 2) wU * u.val := by
    dsimp only [δ]
    rw [map_mul, map_inv, rationalPositiveScalar_finite, ha, haU, map_mul]
    group
  have hδ : rationalPositiveGL2ToFinite δ ∈ finiteAdeleGL2Gamma0 N := by
    rw [hδf]
    exact (finiteAdeleGL2Gamma0 N).mul_mem (finiteAdele_integral_unit_scalar_mem N w) u.property
  obtain ⟨σ, hσ⟩ := (positiveRationalGL2_mem_finiteAdeleGamma0_iff N δ).mp hδ
  have hσδ : toGLPos (Matrix.SpecialLinearGroup.map (Int.castRingHom ℚ) σ.val) = δ := by
    apply Subtype.ext
    exact (generalLinear_map_toGL (Int.castRingHom ℚ) σ.val).symm.trans hσ
  refine ⟨σ, ?_⟩
  have hγδ : γ = rationalPositiveScalar qU * δ := by dsimp only [δ]; group
  rw [hγδ, map_mul, rationalPositiveToAdelicProjective_scalar, one_mul, ← hσδ,
    rationalPositiveToAdelicProjective_integral]

end
end Dubon2026
