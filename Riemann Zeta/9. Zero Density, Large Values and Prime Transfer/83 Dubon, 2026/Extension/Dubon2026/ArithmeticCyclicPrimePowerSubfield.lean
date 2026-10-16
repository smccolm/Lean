import Dubon2026.CyclotomicHigherLocalDegreeStage
import Dubon2026.OriginalAuxiliaryCyclicExtension
import Dubon2026.FiniteGaloisEmbeddingStage
import Dubon2026.ArithmeticOrbitNormalField

/-! # Cyclic prime-power subfields in the fixed arithmetic union

The existing cyclotomic stage lies inside the prescribed unramified union.
Its cyclic Galois group and the proved degree-divisor construction give
an actual subfield of every odd-prime-power degree. This is the first
field-existence input for DUB-17's now-proved auxiliary generator transfer.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat
attribute [local instance] arithmeticOrbitLocalUnionAlgebra

/-- The original rational arithmetic union contains an actual cyclic Galois subfield of every prescribed odd-prime-power degree when the prime divides the allowed ramification parameter. -/
theorem rationalArithmetic_exists_cyclic_primePower_subfield
    (a : 𝓞 ℚ) (q n : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a) :
    ∃ D : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a),
      IsCyclic Gal(D/ℚ) ∧ Module.finrank ℚ D = q ^ n := by
  obtain ⟨k, F, hk, hcycl, hcyclic, hF, _⟩ :=
    originalCyclotomic_exists_higher_localDegree_stage (Ω := AlgebraicClosure ℚ)
      a q n hq hq2 hqa ∅ (by simp)
  letI : IsCyclotomicExtension {q ^ (k + 1)} ℚ F := hcycl
  letI : IsCyclic Gal(F/ℚ) := hcyclic
  letI : IsGalois ℚ F := IsCyclotomicExtension.isGalois {q ^ (k + 1)} ℚ F
  letI : NeZero (q ^ (k + 1)) := ⟨pow_ne_zero _ hq.ne_zero⟩
  have hdegree : Module.finrank ℚ F = q ^ k * (q - 1) := by
    rw [IsCyclotomicExtension.finrank F
      (Polynomial.cyclotomic.irreducible_rat (NeZero.pos (q ^ (k + 1)))),
      Nat.totient_prime_pow_succ hq]
  have hd : q ^ n ∣ Module.finrank ℚ F := by
    rw [hdegree]
    exact dvd_mul_of_dvd_left (pow_dvd_pow q (by omega : n ≤ k)) _
  obtain ⟨D, hGal, hCyc, hD⟩ := originalCyclic_exists_intermediate_degree
    ℚ F (q ^ n) (pow_pos hq.pos n) hd
  letI : IsGalois ℚ D := hGal
  letI : IsCyclic Gal(D/ℚ) := hCyc
  let i : D →ₐ[ℚ] rationalUnramifiedExtension a := (IntermediateField.inclusion hF).comp D.val
  let C := finiteGaloisEmbeddingStage i
  let e := finiteGaloisEmbeddingStageEquiv i
  refine ⟨C, e.autCongr.isCyclic.mp hCyc, ?_⟩
  exact e.toLinearEquiv.finrank_eq.symm.trans hD

end
end Dubon2026
