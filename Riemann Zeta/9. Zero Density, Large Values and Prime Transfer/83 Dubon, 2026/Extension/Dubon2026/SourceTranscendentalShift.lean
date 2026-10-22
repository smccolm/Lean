import Mathlib.Algebra.MvPolynomial.Equiv

/-! DUB-17/18 -> arithmetic torsion comparison -> finite torsion descent.
Translation of a transcendental constant produces an infinite place orbit,
contradicting finite support of an invariant reduced divisor. Adapted from
S_IsAlgClosed_exists_algEquiv_apply_eq_add_algebraMap_of_transcendental,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
Native transcendence bases, fraction-field transport and algebraic-closure
automorphism extension supply the required construction.
-/
namespace Dubon2026.SourceCurve.ConstantField
noncomputable section
open MvPolynomial

namespace TranscendentalShift

variable {K : Type*} [Field K] {ι : Type*}

/-- Translate polynomial variables by the specified constants. -/
def shift (c : ι → K) : MvPolynomial ι K →ₐ[K] MvPolynomial ι K :=
  aeval fun i => X i + C (c i)

theorem shift_X (c : ι → K) (i : ι) : shift c (X i) = X i + C (c i) := by
  simp [shift]

theorem shift_comp_shift_neg (c : ι → K) : (shift c).comp (shift (-c)) = AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [shift, add_assoc]

theorem shift_neg_comp_shift (c : ι → K) : (shift (-c)).comp (shift c) = AlgHom.id K _ := by
  simpa using shift_comp_shift_neg (-c)

/-- The polynomial translation equivalence, with inverse the negative translation. -/
def shiftEquiv (c : ι → K) : MvPolynomial ι K ≃ₐ[K] MvPolynomial ι K :=
  AlgEquiv.ofAlgHom (shift c) (shift (-c)) (shift_comp_shift_neg c) (shift_neg_comp_shift c)

theorem shiftEquiv_X (c : ι → K) (i : ι) : shiftEquiv c (X i) = X i + C (c i) := by
  change shift c (X i) = X i + C (c i)
  exact shift_X c i

theorem shiftEquiv_C (c : ι → K) (k : K) : shiftEquiv c (C k) = C k := by
  simp [shiftEquiv, shift]

end TranscendentalShift

end
end Dubon2026.SourceCurve.ConstantField
