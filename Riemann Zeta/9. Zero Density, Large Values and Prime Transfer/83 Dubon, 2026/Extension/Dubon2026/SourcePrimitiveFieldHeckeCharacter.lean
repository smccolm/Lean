import Dubon2026.SourcePrimitiveLocalCoefficients

/-! The original Hecke eigensystem takes values in the literal coefficient field.
This is the coefficient-realization edge for DUB-17/18's modular Galois
association: the original Fourier trace data must be reduced in one genuine
finite local coefficient field. The existing all-index eigenline supplies
the multiplicative closure; no Galois representation is asserted.
-/

namespace Dubon2026
noncomputable section
open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups
variable {Q : ℕ} [NeZero Q] {k : ℤ}

/-- Every original integral Hecke eigenvalue belongs to the actual Fourier coefficient ring. -/
theorem sourcePrimitiveHeckeCharacter_mem_coefficientRing (f : PrimitiveCuspForm Q k)
    (T : sourceOriginalIntegralHeckeAlgebra Q k) :
    sourcePrimitiveHeckeCharacter f T ∈ sourcePrimitiveCoefficientRing f := by
  have he : ∀ t : Module.End ℂ (CuspForm ((Gamma0 Q).map (mapGL ℝ)) k),
      t ∈ Algebra.adjoin ℤ (Set.range fun n : ℕ+ => cuspHeckeLinear Q k (n : ℕ)) →
        cuspCoefficientLinear Q k 1 (t f.toCuspForm) ∈ sourcePrimitiveCoefficientRing f := by
    intro t ht
    induction ht using Algebra.adjoin_induction with
    | mem t ht =>
      obtain ⟨n, rfl⟩ := ht
      change sourcePrimitiveHeckeCharacter f
        ⟨cuspHeckeLinear Q k n, Algebra.subset_adjoin ⟨n, rfl⟩⟩ ∈ _
      rw [sourcePrimitiveHeckeCharacter_hecke]
      exact Algebra.subset_adjoin ⟨(n : ℕ), rfl⟩
    | algebraMap z =>
      simp only [Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply,
        Module.End.one_apply, map_zsmul]
      change z • cuspCoefficients f.toCuspForm 1 ∈ _
      rw [f.normalized]
      exact (sourcePrimitiveCoefficientRing f).smul_mem
        (sourcePrimitiveCoefficientRing f).one_mem z
    | add a b _ _ hfa hfb =>
      rw [LinearMap.add_apply, map_add]
      exact (sourcePrimitiveCoefficientRing f).add_mem hfa hfb
    | mul a b _ hb hfa hfb =>
      have hb' := sourcePrimitiveHecke_eigenline f ⟨b, hb⟩
      change b f.toCuspForm =
        cuspCoefficientLinear Q k 1 (b f.toCuspForm) • f.toCuspForm at hb'
      rw [Module.End.mul_apply, hb', map_smul, map_smul]
      exact (sourcePrimitiveCoefficientRing f).mul_mem hfb hfa
  exact he T.val T.property

/-- The original integral eigencharacter image is exactly the literal Fourier coefficient ring. -/
theorem sourcePrimitiveHeckeCharacter_range_eq (f : PrimitiveCuspForm Q k) :
    (sourcePrimitiveHeckeCharacter f).range = sourcePrimitiveCoefficientRing f := by
  apply le_antisymm
  · rintro _ ⟨T, rfl⟩
    exact sourcePrimitiveHeckeCharacter_mem_coefficientRing f T
  · exact sourcePrimitiveCoefficientRing_le_characterRange f

/-- The literal Fourier coefficient ring lies in the literal Fourier coefficient field. -/
theorem sourcePrimitiveCoefficientRing_le_field (f : PrimitiveCuspForm Q k) :
    sourcePrimitiveCoefficientRing f ≤
      (sourcePrimitiveCoefficientField f).toSubalgebra.restrictScalars ℤ := by
  apply Algebra.adjoin_le
  rintro _ ⟨n, rfl⟩
  exact IntermediateField.subset_adjoin ℚ _ ⟨n, rfl⟩

/-- The original Hecke eigencharacter valued in the actual original coefficient number field. -/
def sourcePrimitiveFieldHeckeCharacter (f : PrimitiveCuspForm Q k) :
    sourceOriginalIntegralHeckeAlgebra Q k →ₐ[ℤ] sourcePrimitiveCoefficientField f :=
  (sourcePrimitiveHeckeCharacter f).codRestrict
    ((sourcePrimitiveCoefficientField f).toSubalgebra.restrictScalars ℤ)
    (fun T => sourcePrimitiveCoefficientRing_le_field f
      (sourcePrimitiveHeckeCharacter_mem_coefficientRing f T))

/-- The field-valued original eigencharacter recovers the exact original coefficient at each positive index. -/
theorem sourcePrimitiveFieldHeckeCharacter_hecke (f : PrimitiveCuspForm Q k) (n : ℕ+) :
    sourcePrimitiveFieldHeckeCharacter f
      ⟨cuspHeckeLinear Q k n, Algebra.subset_adjoin ⟨n, rfl⟩⟩ =
        sourcePrimitiveFieldCoefficient f n := by
  apply Subtype.ext
  exact sourcePrimitiveHeckeCharacter_hecke f n

/-- Every original integral Hecke eigenvalue in the actual coefficient field is integral. -/
theorem sourcePrimitiveFieldHeckeCharacter_isIntegral (f : PrimitiveCuspForm Q k)
    (hk : 2 ≤ k) (T : sourceOriginalIntegralHeckeAlgebra Q k) :
    IsIntegral ℤ (sourcePrimitiveFieldHeckeCharacter f T) := by
  letI := sourceOriginalIntegralHeckeAlgebra_finite Q k hk
  exact (IsIntegral.of_finite ℤ T).map (sourcePrimitiveFieldHeckeCharacter f)

end
end Dubon2026
