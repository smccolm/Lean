import Dubon2026.FiniteAdelicLocalHom

/-! # Original integral local matrices at places away from the genuine level -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix

/-- Evaluation of the actual diagonal rational adele is its original local field embedding. -/
theorem finiteAdelePlace_rational (v : HeightOneSpectrum ℤ) (q : ℚ) :
    finiteAdelePlace v (algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q) =
      algebraMap ℚ (v.adicCompletion ℚ) q := rfl

/-- The inverse original level is an actual local integer at every place not dividing that level. -/
theorem finitePlace_inverse_level_integral (N : ℕ) (v : HeightOneSpectrum ℤ)
    (hN : (N : ℤ) ∉ v.asIdeal) :
    algebraMap ℚ (v.adicCompletion ℚ) ((N : ℚ)⁻¹) ∈ v.adicCompletionIntegers ℚ := by
  rw [mem_adicCompletionIntegers, algebraMap_adicCompletion, Function.comp_apply,
    Valued.valuedCompletion_apply]
  change v.valuation ℚ ((N : ℚ)⁻¹) ≤ 1
  have hv : v.valuation ℚ (N : ℚ) = 1 := by
    change v.valuation ℚ (algebraMap ℤ ℚ (N : ℤ)) = 1
    rw [valuation_of_algebraMap]
    exact intValuation_eq_one_iff.mpr hN
  rw [map_inv₀, hv, inv_one]

/-- Inserting an original integral local matrix gives an everywhere-integral actual finite-adelic matrix. -/
theorem finiteAdelePlaceMatrix_integral (v : HeightOneSpectrum ℤ)
    (a : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (ha : ∀ i j, a i j ∈ v.adicCompletionIntegers ℚ) :
    ∀ i j, finiteAdelePlaceMatrix v a i j ∈ finiteAdeleIntegerSubring := by
  intro i j w
  change finiteAdelePlace w (finiteAdelePlaceMatrix v a i j) ∈ w.adicCompletionIntegers ℚ
  by_cases h : w = v
  · subst w
    rw [show finiteAdelePlace v (finiteAdelePlaceMatrix v a i j) = a i j from
      congrArg (fun M => M i j) (finiteAdelePlaceMatrix_same v a)]
    exact ha i j
  · rw [show finiteAdelePlace w (finiteAdelePlaceMatrix v a i j) =
        (1 : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) i j from
      congrArg (fun M => M i j) (finiteAdelePlaceMatrix_ne v w h a)]
    fin_cases i <;> fin_cases j <;> simp

/-- Away from the original level, every actual integral local matrix inserts into the genuine finite level order. -/
theorem finiteAdelePlaceMatrix_level (N : ℕ) [NeZero N] (v : HeightOneSpectrum ℤ)
    (hN : (N : ℤ) ∉ v.asIdeal)
    (a : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (ha : ∀ i j, a i j ∈ v.adicCompletionIntegers ℚ) :
    finiteAdeleLevelMatrix N (finiteAdelePlaceMatrix v a) := by
  refine ⟨finiteAdelePlaceMatrix_integral v a ha, ?_⟩
  rw [finiteAdeleLevelMultiple_iff]
  intro w
  change finiteAdelePlace w (algebraMap ℚ (FiniteAdeleRing ℤ ℚ) ((N : ℚ)⁻¹) *
    finiteAdelePlaceMatrix v a 1 0) ∈ w.adicCompletionIntegers ℚ
  rw [map_mul, finiteAdelePlace_rational]
  by_cases h : w = v
  · subst w
    rw [show finiteAdelePlace v (finiteAdelePlaceMatrix v a 1 0) = a 1 0 from
      congrArg (fun M => M 1 0) (finiteAdelePlaceMatrix_same v a)]
    exact (v.adicCompletionIntegers ℚ).toSubring.mul_mem (finitePlace_inverse_level_integral N v hN) (ha 1 0)
  · rw [show finiteAdelePlace w (finiteAdelePlaceMatrix v a 1 0) = 0 from
      congrArg (fun M => M 1 0) (finiteAdelePlaceMatrix_ne v w h a), mul_zero]
    exact (w.adicCompletionIntegers ℚ).zero_mem

/-- The genuine local integral general-linear group inserts into the original global level group away from that level. -/
theorem finiteAdelicLocalIntegral_mem_level (N : ℕ) [NeZero N] (v : HeightOneSpectrum ℤ)
    (hN : (N : ℤ) ∉ v.asIdeal)
    (g : GeneralLinearGroup (Fin 2) (v.adicCompletionIntegers ℚ)) :
    finiteAdelicLocalGL2 v (GeneralLinearGroup.map (v.adicCompletionIntegers ℚ).subtype g) ∈
      finiteAdeleGL2Gamma0 N := by
  constructor
  · exact finiteAdelePlaceMatrix_level N v hN _ (fun i j => (g.val i j).property)
  · exact finiteAdelePlaceMatrix_level N v hN _ (fun i j => ((g⁻¹).val i j).property)

end
end Dubon2026
