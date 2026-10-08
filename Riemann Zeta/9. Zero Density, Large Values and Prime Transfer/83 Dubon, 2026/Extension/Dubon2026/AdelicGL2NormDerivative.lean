import Dubon2026.AdelicSl2NormDerivative
import Dubon2026.AdelicRealGL2Normalization
import Dubon2026.RealPositiveNormalizeTangent
import Dubon2026.ComplexTracelessRealTangent

/-! # The genuine GL₂ Lie action as original adelic Hilbert norm derivatives -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The full complex matrix Lie action obtained by the actual scalar-trace projection of original cusp infinitesimals. -/
def adelicComplexGL2Action : Matrix (Fin 2) (Fin 2) ℂ →ₗ⁅ℂ⁆ Module.End ℂ (adelicRealSmoothSubmodule f) :=
  (adelicComplexSl2Action f).comp complexTracelessProjection

/-- The genuine full matrix action restricts to the exact previously proved traceless action. -/
theorem adelicComplexGL2Action_sl (x : ComplexSl2) :
    adelicComplexGL2Action f x.val = adelicComplexSl2Action f x := by
  change adelicComplexSl2Action f (complexTracelessProjection x.val) = _
  exact congrArg (adelicComplexSl2Action f) (complexTracelessProjection_sl x)

/-- Every actual scalar matrix acts by zero, as required by the original trivial central character. -/
theorem adelicComplexGL2Action_scalar (z : ℂ) :
    adelicComplexGL2Action f (z • (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 0 := by
  change adelicComplexSl2Action f (complexTracelessProjection (z • 1)) = _
  exact (congrArg (adelicComplexSl2Action f) (complexTracelessProjection_scalar z)).trans
    (map_zero (adelicComplexSl2Action f))

/-- On every original smooth vector, a genuine positive general-linear curve has exactly the norm derivative given by its actual complexified matrix tangent. -/
theorem adelicComplexGL2Action_positive_hasDerivAt (v : adelicRealSmoothSubmodule f)
    (c : ℝ → GL(2, ℝ)⁺) (hc : c 0 = 1) (a : Matrix (Fin 2) (Fin 2) ℝ)
    (hd : ∀ i j, HasDerivAt (fun t => (c t).val.val i j) (a i j) 0) :
    HasDerivAt (fun t => adelicCyclicHilbertRepresentation f (adelicRealGL2Embedding (c t).val) v.val)
      (adelicComplexGL2Action f (a.map Complex.ofReal) v).val 0 := by
  have h00 := realPositiveNormalize_entry_hasDerivAt c hc a hd 0 0
  have h10 := realPositiveNormalize_entry_hasDerivAt c hc a hd 1 0
  have h01 := realPositiveNormalize_entry_hasDerivAt c hc a hd 0 1
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
    ite_true, mul_one] at h00
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
    show (1 : Fin 2) ≠ 0 by decide, show (0 : Fin 2) ≠ 1 by decide,
    ite_false, mul_zero, sub_zero] at h10 h01
  have hn := adelicComplexSl2Action_hasDerivAt f v (fun t => realPositiveNormalize (c t))
    (by simp [hc]) (a 0 0 - Matrix.trace a / 2) (a 1 0) (a 0 1) h00 h10 h01
  have hV : (adelicComplexGL2Action f (a.map Complex.ofReal) v).val =
      (adelicComplexSl2Action f (complexSl2OfRealTangent
        (a 0 0 - Matrix.trace a / 2) (a 1 0) (a 0 1)) v).val :=
    congrArg (fun x : ComplexSl2 => (adelicComplexSl2Action f x v).val)
      (complexTracelessProjection_ofReal a)
  rw [hV]
  exact HasDerivAt.congr_of_eventuallyEq (F := AdelicCyclicHilbert f) (𝕜 := ℝ) hn (Filter.Eventually.of_forall
    (fun t => adelicCyclicHilbert_positive_normalize f (c t) v.val))

end
end Dubon2026
