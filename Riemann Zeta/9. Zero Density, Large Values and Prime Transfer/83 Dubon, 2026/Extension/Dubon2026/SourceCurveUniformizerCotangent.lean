import Dubon2026.SourceCurveLocalDifferentials
import Mathlib.RingTheory.Kaehler.Polynomial

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

/-- The actual uniformizer as an element of its valuation ring. -/
def uniformizerSubring : v.toValuationSubring :=
  (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose

/-- The polynomial coordinate algebra given by the actual uniformizer. -/
@[reducible]
def polynomialAlgebra : Algebra K[X] v.toValuationSubring :=
  (Polynomial.aeval (R := K) v.uniformizerSubring).toRingHom.toAlgebra

theorem polynomialAlgebra_algebraMap_X :
    letI := v.polynomialAlgebra
    algebraMap K[X] v.toValuationSubring X = v.uniformizerSubring :=
  aeval_X _

/-- The uniformizer coordinate respects the literal constant field. -/
theorem polynomialIsScalarTower :
    letI := v.polynomialAlgebra
    IsScalarTower K K[X] v.toValuationSubring := by
  letI := v.polynomialAlgebra
  refine IsScalarTower.of_algebraMap_eq fun a => ?_
  show _ = aeval v.uniformizerSubring (algebraMap K K[X] a)
  simp [Polynomial.algebraMap_eq, aeval_C]

theorem range_mapBaseChange_le_span_D_uniformizer :
    letI := v.polynomialAlgebra
    letI := v.polynomialIsScalarTower
    LinearMap.range (KaehlerDifferential.mapBaseChange K K[X] v.toValuationSubring)
      ≤ Submodule.span v.toValuationSubring
          {KaehlerDifferential.D K v.toValuationSubring v.uniformizerSubring} := by
  letI := v.polynomialAlgebra
  letI := v.polynomialIsScalarTower
  rintro _ ⟨t, rfl⟩
  induction t with
  | zero => simp
  | add x y hx hy => rw [map_add]; exact add_mem hx hy
  | tmul b ω =>
    rw [KaehlerDifferential.mapBaseChange_tmul,
      show ω = (KaehlerDifferential.polynomialEquiv K ω) • (KaehlerDifferential.D K K[X] X) from
        ((KaehlerDifferential.polynomialEquiv K).symm_apply_apply ω).symm.trans
          (KaehlerDifferential.polynomialEquiv_symm K _),
      LinearMap.map_smul, KaehlerDifferential.map_D,
      show algebraMap K[X] v.toValuationSubring X = v.uniformizerSubring from aeval_X _,
      ← algebraMap_smul (A := v.toValuationSubring)]
    exact Submodule.smul_mem _ b
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))

theorem range_mapBaseChange_eq_top_of_subsingleton
    (hsub :
      letI := v.polynomialAlgebra
      Subsingleton Ω[v.toValuationSubring⁄K[X]]) :
    letI := v.polynomialAlgebra
    letI := v.polynomialIsScalarTower
    LinearMap.range (KaehlerDifferential.mapBaseChange K K[X] v.toValuationSubring) = ⊤ := by
  letI := v.polynomialAlgebra
  letI := v.polynomialIsScalarTower
  rw [KaehlerDifferential.range_mapBaseChange]
  exact LinearMap.ker_eq_top.mpr (Subsingleton.elim _ _)

theorem span_D_uniformizer_eq_top_of_subsingleton
    (hsub :
      letI := v.polynomialAlgebra
      Subsingleton Ω[v.toValuationSubring⁄K[X]]) :
    Submodule.span v.toValuationSubring
      {KaehlerDifferential.D K v.toValuationSubring v.uniformizerSubring} = ⊤ := by
  refine top_le_iff.mp ?_
  rw [← v.range_mapBaseChange_eq_top_of_subsingleton hsub]
  exact v.range_mapBaseChange_le_span_D_uniformizer

end
end Dubon2026.SourceCurve.Place
