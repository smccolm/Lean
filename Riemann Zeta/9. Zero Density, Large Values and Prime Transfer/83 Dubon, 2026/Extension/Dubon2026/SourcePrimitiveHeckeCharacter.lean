import Dubon2026.SourceOriginalIntegralHecke
import Dubon2026.PrimitiveFullEigen

/-! Arithmetic of the original primitive Fourier coefficients.
DUB-17/18 -> modular Galois association -> the original coefficient number field.
The existing all-index primitive eigenvector theorem supplies the actual
character of the constructed finite integral Hecke algebra. This proves
integrality of the actual coefficients, including the bad indices.
-/

namespace Dubon2026
noncomputable section
open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {Q : ℕ} [NeZero Q] {k : ℤ}

/-- Every element of the original integral Hecke algebra acts on the actual primitive eigenline. -/
theorem sourcePrimitiveHecke_eigenline (f : PrimitiveCuspForm Q k)
    (T : sourceOriginalIntegralHeckeAlgebra Q k) :
    T.val f.toCuspForm = cuspCoefficientLinear Q k 1 (T.val f.toCuspForm) • f.toCuspForm := by
  have he : ∀ t : Module.End ℂ (CuspForm ((Gamma0 Q).map (mapGL ℝ)) k),
      t ∈ Algebra.adjoin ℤ (Set.range fun n : ℕ+ => cuspHeckeLinear Q k (n : ℕ)) →
        ∃ c : ℂ, t f.toCuspForm = c • f.toCuspForm := by
    intro t hT
    induction hT using Algebra.adjoin_induction with
    | mem t ht =>
      obtain ⟨n, rfl⟩ := ht
      exact ⟨cuspCoefficients f.toCuspForm n, primitiveCuspForm_eigenvector_all f n.pos⟩
    | algebraMap r =>
      exact ⟨r, by simp [Int.cast_smul_eq_zsmul]⟩
    | add a b _ _ ha hb =>
      obtain ⟨c, hc⟩ := ha
      obtain ⟨d, hd⟩ := hb
      exact ⟨c + d, by rw [LinearMap.add_apply, hc, hd, add_smul]⟩
    | mul a b _ _ ha hb =>
      obtain ⟨c, hc⟩ := ha
      obtain ⟨d, hd⟩ := hb
      exact ⟨d * c, by rw [Module.End.mul_apply, hd, map_smul, hc, smul_smul]⟩
  obtain ⟨c, hc⟩ := he T.val T.property
  have hfirst : cuspCoefficientLinear Q k 1 (T.val f.toCuspForm) = c := by
    rw [hc, map_smul]
    change c * cuspCoefficients f.toCuspForm 1 = c
    rw [f.normalized, mul_one]
  rw [hfirst]
  exact hc

/-- The actual primitive eigensystem as an integral algebra character on the original Hecke algebra. -/
def sourcePrimitiveHeckeCharacter (f : PrimitiveCuspForm Q k) :
    sourceOriginalIntegralHeckeAlgebra Q k →ₐ[ℤ] ℂ where
  toFun T := cuspCoefficientLinear Q k 1 (T.val f.toCuspForm)
  map_zero' := by simp
  map_one' := by exact f.normalized
  map_add' T U := by simp
  map_mul' T U := by
    change cuspCoefficientLinear Q k 1 (T.val (U.val f.toCuspForm)) = _
    conv_lhs => rw [sourcePrimitiveHecke_eigenline f U, map_smul, map_smul]
    change cuspCoefficientLinear Q k 1 (U.val f.toCuspForm) *
        cuspCoefficientLinear Q k 1 (T.val f.toCuspForm) =
      cuspCoefficientLinear Q k 1 (T.val f.toCuspForm) *
        cuspCoefficientLinear Q k 1 (U.val f.toCuspForm)
    exact mul_comm _ _
  commutes' r := by
    change cuspCoefficientLinear Q k 1
      ((algebraMap ℤ (Module.End ℂ (CuspForm ((Gamma0 Q).map (mapGL ℝ)) k)) r) f.toCuspForm) = _
    simp only [Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply,
      Module.End.one_apply, map_zsmul]
    change r • cuspCoefficients f.toCuspForm 1 = r • (1 : ℂ)
    rw [f.normalized]

/-- The character value at the original positive Hecke index is the actual Fourier coefficient. -/
theorem sourcePrimitiveHeckeCharacter_hecke (f : PrimitiveCuspForm Q k) (n : ℕ+) :
    sourcePrimitiveHeckeCharacter f
      ⟨cuspHeckeLinear Q k (n : ℕ), Algebra.subset_adjoin ⟨n, rfl⟩⟩ =
        cuspCoefficients f.toCuspForm n := by
  change cuspCoefficientLinear Q k 1 (cuspHeckeLinear Q k (n : ℕ) f.toCuspForm) = _
  rw [primitiveCuspForm_eigenvector_all f n.pos, map_smul]
  change cuspCoefficients f.toCuspForm n * cuspCoefficients f.toCuspForm 1 = _
  rw [f.normalized, mul_one]

/-- Every actual Fourier coefficient of a source primitive form is an algebraic integer. -/
theorem sourcePrimitiveCoefficient_isIntegral (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (n : ℕ) :
    IsIntegral ℤ (cuspCoefficients f.toCuspForm n) := by
  by_cases hn : n = 0
  · rw [hn, cuspCoefficients_zero]
    exact isIntegral_zero
  let n' : ℕ+ := ⟨n, Nat.pos_of_ne_zero hn⟩
  letI := sourceOriginalIntegralHeckeAlgebra_finite Q k hk
  change IsIntegral ℤ (cuspCoefficients f.toCuspForm n')
  rw [← sourcePrimitiveHeckeCharacter_hecke f n']
  exact (IsIntegral.of_finite ℤ
    (⟨cuspHeckeLinear Q k n, Algebra.subset_adjoin ⟨n', rfl⟩⟩ :
      sourceOriginalIntegralHeckeAlgebra Q k)).map (sourcePrimitiveHeckeCharacter f)

end
end Dubon2026
