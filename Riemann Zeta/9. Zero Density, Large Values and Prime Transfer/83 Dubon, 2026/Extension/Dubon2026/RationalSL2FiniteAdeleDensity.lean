import Dubon2026.FiniteAdeleUnitPivot

/-! # Rational strong approximation for the genuine finite adelic special linear group -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

/-- The rational elementary upper matrix maps to the original adelic elementary matrix. -/
theorem rationalSL2_map_upper (q : ℚ) :
    Matrix.SpecialLinearGroup.map (n := Fin 2) (algebraMap ℚ (FiniteAdeleRing ℤ ℚ))
      (ringUpperUnipotent q) =
        ringUpperUnipotent (algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ringUpperUnipotent]

/-- The rational elementary lower matrix maps to the original adelic elementary matrix. -/
theorem rationalSL2_map_lower (q : ℚ) :
    Matrix.SpecialLinearGroup.map (n := Fin 2) (algebraMap ℚ (FiniteAdeleRing ℤ ℚ))
      (ringLowerUnipotent q) =
        ringLowerUnipotent (algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ringLowerUnipotent]

/-- The actual rational determinant-one group is dense in the canonical finite adelic group. -/
theorem rationalSL2_dense_finiteAdeles :
    DenseRange (Matrix.SpecialLinearGroup.map (n := Fin 2) (algebraMap ℚ (FiniteAdeleRing ℤ ℚ))) := by
  let H := (Matrix.SpecialLinearGroup.map (n := Fin 2)
    (algebraMap ℚ (FiniteAdeleRing ℤ ℚ))).range.topologicalClosure
  have hU (t : FiniteAdeleRing ℤ ℚ) : ringUpperUnipotent t ∈ H := by
    refine rational_dense_finiteAdeles.induction_on t
      (Subgroup.isClosed_topologicalClosure _ |>.preimage ringUpperUnipotent_continuous) ?_
    intro q
    apply Subgroup.le_topologicalClosure
    exact ⟨ringUpperUnipotent q, rationalSL2_map_upper q⟩
  have hL (t : FiniteAdeleRing ℤ ℚ) : ringLowerUnipotent t ∈ H := by
    refine rational_dense_finiteAdeles.induction_on t
      (Subgroup.isClosed_topologicalClosure _ |>.preimage ringLowerUnipotent_continuous) ?_
    intro q
    apply Subgroup.le_topologicalClosure
    exact ⟨ringLowerUnipotent q, rationalSL2_map_lower q⟩
  intro g
  exact finiteAdeleSL2_mem_of_unipotents H hU hL g

/-- Any open finite-level subgroup gives an exact rational-times-level decomposition. -/
theorem rationalSL2_finiteAdeles_open_subgroup_factorization
    (K : Subgroup SL(2, FiniteAdeleRing ℤ ℚ)) (hK : IsOpen (K : Set SL(2, FiniteAdeleRing ℤ ℚ)))
    (g : SL(2, FiniteAdeleRing ℤ ℚ)) :
    ∃ γ : SL(2, ℚ), ∃ k : K,
      g = Matrix.SpecialLinearGroup.map (n := Fin 2) (algebraMap ℚ (FiniteAdeleRing ℤ ℚ)) γ * k.val := by
  let ρ := Matrix.SpecialLinearGroup.map (n := Fin 2) (algebraMap ℚ (FiniteAdeleRing ℤ ℚ))
  have hopen : IsOpen {h : SL(2, FiniteAdeleRing ℤ ℚ) | g⁻¹ * h ∈ K} :=
    hK.preimage (continuous_const.mul continuous_id)
  obtain ⟨γ, hγ⟩ := rationalSL2_dense_finiteAdeles.exists_mem_open hopen
    ⟨g, by simp⟩
  have hk : (ρ γ)⁻¹ * g ∈ K := by
    simpa only [_root_.mul_inv_rev, inv_inv] using K.inv_mem hγ
  refine ⟨γ, ⟨(ρ γ)⁻¹ * g, hk⟩, ?_⟩
  change g = ρ γ * ((ρ γ)⁻¹ * g)
  simp

end
end Dubon2026
