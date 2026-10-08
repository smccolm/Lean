import Dubon2026.CompactSl2Basis
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Tactic.LinearCombination

/-! # Exact inner products of a genuine unitary lowest-weight ladder -/

namespace Dubon2026

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- Multiplication by minus i turns a skew-symmetric compact infinitesimal into a symmetric operator on its actual domain. -/
theorem skew_compact_symmetric (K : Module.End ℂ V)
    (hK : ∀ v w, inner ℂ (K v) w + inner ℂ v (K w) = 0) :
    ((-Complex.I) • K).IsSymmetric := by
  intro v w
  simp only [LinearMap.smul_apply, inner_smul_left, inner_smul_right, map_neg,
    Complex.conj_I, neg_neg]
  linear_combination Complex.I * hK v w

/-- The genuine raising and lowering combinations of skew-symmetric real infinitesimals are negative adjoints on their common domain. -/
theorem skew_raising_lowering_inner (A B : Module.End ℂ V)
    (hA : ∀ v w, inner ℂ (A v) w + inner ℂ v (A w) = 0)
    (hB : ∀ v w, inner ℂ (B v) w + inner ℂ v (B w) = 0) (v w : V) :
    inner ℂ ((A + (Complex.I / 2) • B) v) w =
      -inner ℂ v ((A - (Complex.I / 2) • B) w) := by
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    inner_add_left, inner_sub_right, inner_smul_left, inner_smul_right, map_div₀,
    Complex.conj_I, map_ofNat]
  linear_combination hA v w - (Complex.I / 2) * hB v w

/-- The compact Cartan image of a genuine matrix action is symmetric when its original rotation image is skew symmetric. -/
theorem compactSl2Action_Cartan_symmetric (T : ComplexSl2 →ₗ[ℂ] Module.End ℂ V)
    (K : Module.End ℂ V) (hTK : T (complexSl2U - complexSl2F) = K)
    (hK : ∀ v w, inner ℂ (K v) w + inner ℂ v (K w) = 0) :
    (T compactSl2H).IsSymmetric := by
  rw [compactSl2H, map_smul, hTK]
  exact skew_compact_symmetric K hK

/-- The genuine compact matrix combinations have the negative-adjoint relation inherited from their original three real images. -/
theorem compactSl2Action_raising_lowering_inner (T : ComplexSl2 →ₗ[ℂ] Module.End ℂ V)
    (A U F : Module.End ℂ V) (hTA : T complexSl2A = A)
    (hTU : T complexSl2U = U) (hTF : T complexSl2F = F)
    (hA : ∀ v w, inner ℂ (A v) w + inner ℂ v (A w) = 0)
    (hU : ∀ v w, inner ℂ (U v) w + inner ℂ v (U w) = 0)
    (hF : ∀ v w, inner ℂ (F v) w + inner ℂ v (F w) = 0) (v w : V) :
    inner ℂ (T compactSl2E v) w = -inner ℂ v (T compactSl2F w) := by
  have hB : ∀ v w, inner ℂ ((U + F) v) w + inner ℂ v ((U + F) w) = 0 := by
    intro v w
    simp only [LinearMap.add_apply, inner_add_left, inner_add_right]
    linear_combination hU v w + hF v w
  simpa only [compactSl2E, compactSl2F, map_add, map_sub, map_smul, hTA, hTU, hTF] using
    skew_raising_lowering_inner A (U + F) hA hB v w

/-- Distinct actual eigenvalues of a symmetric operator give orthogonal original vectors. -/
theorem symmetric_weight_inner_zero (H : Module.End ℂ V) (hH : H.IsSymmetric)
    (v w : V) (a b : ℂ) (hab : a ≠ b) (hv : H v = a • v) (hw : H w = b • w) :
    inner ℂ v w = 0 :=
  hH.orthogonalFamily_eigenspaces hab
    ⟨v, Module.End.mem_eigenspace_iff.mpr hv⟩ ⟨w, Module.End.mem_eigenspace_iff.mpr hw⟩

/-- Negative-adjoint ladder operators convert an exact lowering recurrence into its exact original squared-norm recurrence. -/
theorem raising_norm_sq_recurrence (E F : Module.End ℂ V)
    (hEF : ∀ v w, inner ℂ (E v) w = -inner ℂ v (F w))
    (v w : V) (a : ℝ) (he : E v = w) (hf : F w = (-a : ℂ) • v) :
    ‖w‖ ^ 2 = a * ‖v‖ ^ 2 := by
  have h := hEF v w
  rw [he, hf, inner_smul_right] at h
  have hr := congrArg Complex.re h
  have hvn : (inner ℂ v v).re = ‖v‖ ^ 2 := @inner_self_eq_norm_sq ℂ V _ _ _ v
  have hwn : (inner ℂ w w).re = ‖w‖ ^ 2 := @inner_self_eq_norm_sq ℂ V _ _ _ w
  simpa only [map_neg, Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, hvn, hwn, neg_mul, neg_neg] using hr

end
end Dubon2026
