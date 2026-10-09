import Dubon2026.FiniteAdelicLocalIntegral

/-! # Actual local level groups and exact finite-adelic coordinate membership -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

/-- The actual local integral level order, expressed by the original level quotient of its lower entry. -/
def finitePlaceLevelMatrix (N : ℕ) (v : HeightOneSpectrum ℤ)
    (a : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) : Prop :=
  (∀ i j, a i j ∈ v.adicCompletionIntegers ℚ) ∧
    algebraMap ℚ (v.adicCompletion ℚ) ((N : ℚ)⁻¹) * a 1 0 ∈ v.adicCompletionIntegers ℚ

/-- The genuine local identity satisfies the original level conditions. -/
theorem finitePlaceLevelMatrix_one (N : ℕ) (v : HeightOneSpectrum ℤ) :
    finitePlaceLevelMatrix N v 1 := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> simp
  · simp

/-- The original integral local level order is closed under actual matrix multiplication. -/
theorem finitePlaceLevelMatrix_mul (N : ℕ) (v : HeightOneSpectrum ℤ)
    {a b : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)}
    (ha : finitePlaceLevelMatrix N v a) (hb : finitePlaceLevelMatrix N v b) :
    finitePlaceLevelMatrix N v (a * b) := by
  constructor
  · intro i j
    change ∑ r : Fin 2, a i r * b r j ∈ v.adicCompletionIntegers ℚ
    exact (v.adicCompletionIntegers ℚ).toSubring.sum_mem fun r _ =>
      (v.adicCompletionIntegers ℚ).toSubring.mul_mem (ha.1 i r) (hb.1 r j)
  · have he : algebraMap ℚ (v.adicCompletion ℚ) ((N : ℚ)⁻¹) * (a * b) 1 0 =
        (algebraMap ℚ (v.adicCompletion ℚ) ((N : ℚ)⁻¹) * a 1 0) * b 0 0 +
          a 1 1 * (algebraMap ℚ (v.adicCompletion ℚ) ((N : ℚ)⁻¹) * b 1 0) := by
      simp only [Matrix.mul_apply, Fin.sum_univ_two]
      ring
    rw [he]
    exact (v.adicCompletionIntegers ℚ).toSubring.add_mem
      ((v.adicCompletionIntegers ℚ).toSubring.mul_mem ha.2 (hb.1 0 0))
      ((v.adicCompletionIntegers ℚ).toSubring.mul_mem (ha.1 1 1) hb.2)

/-- The actual local K0(N) consists of genuine matrices and inverse matrices in the original local level order. -/
def finitePlaceGL2Gamma0 (N : ℕ) (v : HeightOneSpectrum ℤ) :
    Subgroup (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) where
  carrier := {g | finitePlaceLevelMatrix N v g.val ∧ finitePlaceLevelMatrix N v (g⁻¹).val}
  one_mem' := ⟨finitePlaceLevelMatrix_one N v, finitePlaceLevelMatrix_one N v⟩
  mul_mem' := by
    intro g h hg hh
    constructor
    · exact finitePlaceLevelMatrix_mul N v hg.1 hh.1
    · simpa only [_root_.mul_inv_rev, Units.val_mul] using finitePlaceLevelMatrix_mul N v hh.2 hg.2
  inv_mem' := by
    intro g hg
    simpa only [inv_inv] using hg.symm

/-- The actual finite-adelic matrix level condition is equivalent to all of its original local level conditions. -/
theorem finiteAdeleLevelMatrix_iff_places (N : ℕ) [NeZero N]
    (a : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    finiteAdeleLevelMatrix N a ↔ ∀ v, finitePlaceLevelMatrix N v (a.map (finiteAdelePlace v)) := by
  constructor
  · intro ha v
    refine ⟨fun i j => ha.1 i j v, ?_⟩
    have hh := (finiteAdeleLevelMultiple_iff N (a 1 0)).mp ha.2 v
    change finiteAdelePlace v (algebraMap ℚ (FiniteAdeleRing ℤ ℚ) ((N : ℚ)⁻¹) * a 1 0) ∈ _ at hh
    simpa only [map_mul, finiteAdelePlace_rational] using hh
  · intro ha
    refine ⟨fun i j v => (ha v).1 i j, ?_⟩
    apply (finiteAdeleLevelMultiple_iff N (a 1 0)).mpr
    intro v
    change finiteAdelePlace v (algebraMap ℚ (FiniteAdeleRing ℤ ℚ) ((N : ℚ)⁻¹) * a 1 0) ∈ _
    simpa only [map_mul, finiteAdelePlace_rational] using (ha v).2

/-- The original global finite level group is exactly the condition of membership in every genuine local K0(N). -/
theorem finiteAdeleGL2Gamma0_iff_places (N : ℕ) [NeZero N]
    (g : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    g ∈ finiteAdeleGL2Gamma0 N ↔
      ∀ v, GeneralLinearGroup.map (finiteAdelePlace v) g ∈ finitePlaceGL2Gamma0 N v := by
  change (finiteAdeleLevelMatrix N g.val ∧ finiteAdeleLevelMatrix N (g⁻¹).val) ↔ _
  rw [finiteAdeleLevelMatrix_iff_places, finiteAdeleLevelMatrix_iff_places]
  constructor
  · intro h v
    exact ⟨h.1 v, h.2 v⟩
  · intro h
    exact ⟨fun v => (h v).1, fun v => (h v).2⟩

end
end Dubon2026
