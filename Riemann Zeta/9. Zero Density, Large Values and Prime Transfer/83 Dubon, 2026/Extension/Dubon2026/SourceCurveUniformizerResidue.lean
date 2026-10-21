import Dubon2026.SourceCurveUniformizerCotangent
import Dubon2026.SourceCurvePlaceRestriction
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.LocalRing.Module

/-! DUB-17/18 -> canonical divisors -> integral local derivatives.
Finite local differentials and the separable actual residue field let the
pinned cotangent sequence and Nakayama theorem prove local generation by
the derivative of the actual uniformizer. Selected from
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver, cotangent/residue engines.
The original-field consumer supplies finiteness and residue separability.
-/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open Polynomial IsLocalRing KaehlerDifferential
open scoped TensorProduct

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)


theorem irreducible_uniformizerSubring : Irreducible v.uniformizerSubring :=
  (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose_spec

theorem maximalIdeal_eq_span_uniformizer :
    IsLocalRing.maximalIdeal v.toValuationSubring = Ideal.span {v.uniformizerSubring} :=
  (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp v.irreducible_uniformizerSubring

theorem D_polynomialAlgebra_uniformizer :
    letI := v.polynomialAlgebra
    KaehlerDifferential.D K[X] v.toValuationSubring v.uniformizerSubring = 0 := by
  letI := v.polynomialAlgebra
  rw [show v.uniformizerSubring = algebraMap K[X] v.toValuationSubring X from
    (v.polynomialAlgebra_algebraMap_X).symm]
  exact (KaehlerDifferential.D K[X] v.toValuationSubring).map_algebraMap X

theorem ker_algebraMap_residueField_eq_span :
    RingHom.ker (algebraMap v.toValuationSubring v.ResidueField)
      = Ideal.span {v.uniformizerSubring} := by
  rw [IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.ker_residue,
    v.maximalIdeal_eq_span_uniformizer]

theorem formallyUnramified_polynomial_residueField_of_isSeparable
    [Algebra.IsSeparable K (IsLocalRing.ResidueField v.toValuationSubring)] :
    letI := v.polynomialAlgebra
    Algebra.FormallyUnramified K[X] (IsLocalRing.ResidueField v.toValuationSubring) := by
  letI := v.polynomialAlgebra
  letI := v.polynomialIsScalarTower
  haveI : Algebra.FormallyUnramified K (IsLocalRing.ResidueField v.toValuationSubring) :=
    Algebra.FormallyUnramified.of_isSeparable K _
  exact Algebra.FormallyUnramified.of_restrictScalars K K[X] _

theorem subsingleton_residueKaehler_of_isSeparable
    [Algebra.IsSeparable K (IsLocalRing.ResidueField v.toValuationSubring)] :
    letI := v.polynomialAlgebra
    Subsingleton Ω[(IsLocalRing.ResidueField v.toValuationSubring)⁄K[X]] := by
  letI := v.polynomialAlgebra
  haveI := v.formallyUnramified_polynomial_residueField_of_isSeparable
  exact Algebra.FormallyUnramified.subsingleton_kaehlerDifferential

theorem subsingleton_residueTensor_polynomialKaehler_of_isSeparable
    [Algebra.IsSeparable K (IsLocalRing.ResidueField v.toValuationSubring)] :
    letI := v.polynomialAlgebra
    Subsingleton (v.ResidueField ⊗[v.toValuationSubring] Ω[v.toValuationSubring⁄K[X]]) := by
  letI := v.polynomialAlgebra
  letI := v.polynomialIsScalarTower
  haveI := v.subsingleton_residueKaehler_of_isSeparable
  refine subsingleton_of_forall_eq 0 fun t => ?_

  obtain ⟨c, rfl⟩ :=
    ((KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange K[X]
      v.toValuationSubring v.ResidueField
      Ideal.Quotient.mk_surjective) t).mp (Subsingleton.elim _ _)
  obtain ⟨⟨x, hx⟩, rfl⟩ := Ideal.toCotangent_surjective _ c
  simp only [KaehlerDifferential.kerCotangentToTensor_toCotangent]

  rw [v.ker_algebraMap_residueField_eq_span] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    rcases hy with rfl
    rw [v.D_polynomialAlgebra_uniformizer, TensorProduct.tmul_zero]
  | zero => simp
  | add y z _ _ hy hz =>
    rw [map_add, TensorProduct.tmul_add, hy, hz, add_zero]
  | smul a y hy IH =>

    have hres : (algebraMap v.toValuationSubring v.ResidueField y) = 0 := by
      rw [IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_eq_zero_iff,
        v.maximalIdeal_eq_span_uniformizer]
      exact hy
    rw [smul_eq_mul, Derivation.leibniz, TensorProduct.tmul_add,
      TensorProduct.tmul_smul, IH, smul_zero, zero_add,
      ← TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one, hres,
      TensorProduct.zero_tmul]

theorem finite_polynomialKaehler_of_finite_kaehler
    [Module.Finite v.toValuationSubring Ω[v.toValuationSubring⁄K]] :
    letI := v.polynomialAlgebra
    Module.Finite v.toValuationSubring Ω[v.toValuationSubring⁄K[X]] := by
  letI := v.polynomialAlgebra
  letI := v.polynomialIsScalarTower
  exact Module.Finite.of_surjective
    (KaehlerDifferential.map K K[X] v.toValuationSubring v.toValuationSubring)
    (KaehlerDifferential.map_surjective K K[X] v.toValuationSubring)

theorem subsingleton_polynomialKaehler_of_isSeparable_of_finite
    [Algebra.IsSeparable K (IsLocalRing.ResidueField v.toValuationSubring)]
    [Module.Finite v.toValuationSubring Ω[v.toValuationSubring⁄K]] :
    letI := v.polynomialAlgebra
    Subsingleton Ω[v.toValuationSubring⁄K[X]] := by
  letI := v.polynomialAlgebra
  haveI := v.finite_polynomialKaehler_of_finite_kaehler
  haveI := v.subsingleton_residueTensor_polynomialKaehler_of_isSeparable
  exact (IsLocalRing.subsingleton_tensorProduct (R := v.toValuationSubring)).mp ‹_›

end
end Dubon2026.SourceCurve.Place
