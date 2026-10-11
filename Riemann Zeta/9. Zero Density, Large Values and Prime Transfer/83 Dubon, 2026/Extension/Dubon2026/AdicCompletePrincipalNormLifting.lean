import Dubon2026.AdicCompleteSimpleRoot
import Dubon2026.FiniteFreeNormLinePolynomial

/-! # Lifting the original principal-unit norm equation in a complete base ring -/

namespace Dubon2026
noncomputable section

open Polynomial

variable {R S ι : Type} [CommRing R] [CommRing S] [Algebra R S]
  [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R S)
  (I : Ideal R) [IsAdicComplete I R]

include b in
/-- An actual direction with unit residual trace lifts every original
principal-unit target along the actual norm line. The witness lies in the
original ideal. Residual trace invertibility is a narrower explicit input;
the norm equation and its original ring witness are the derived conclusion. -/
theorem adicComplete_exists_principal_norm
    (x : S) (hx : IsUnit (Ideal.Quotient.mk I (Algebra.trace R S x)))
    (u : R) (hu : 1 - u ∈ I) :
    ∃ t : R, t ∈ I ∧ Algebra.norm R (1 + t • x) = u := by
  let f : R[X] := finiteFreeNormLinePolynomial b x - C u
  have hf : f.eval 0 ∈ I := by
    simpa only [f, eval_sub, eval_C, finiteFreeNormLinePolynomial_eval,
      zero_smul, add_zero, map_one] using hu
  have hdf : IsUnit (Ideal.Quotient.mk I (f.derivative.eval 0)) := by
    simpa only [f, derivative_sub, derivative_C, sub_zero,
      finiteFreeNormLinePolynomial_derivative_zero] using hx
  obtain ⟨t, ht, hti⟩ := adicComplete_polynomial_simple_root I f 0 hf hdf
  refine ⟨t, by simpa only [sub_zero] using hti, ?_⟩
  change f.eval t = 0 at ht
  simpa only [f, eval_sub, eval_C, finiteFreeNormLinePolynomial_eval,
    sub_eq_zero] using ht

include b in
/-- The original principal-unit target has a genuine extension-ring unit
norm preimage. Its invertibility follows from the actual finite-free norm
criterion, rather than being added as a new lifting hypothesis. -/
theorem adicComplete_exists_principal_unit_norm
    (x : S) (hx : IsUnit (Ideal.Quotient.mk I (Algebra.trace R S x)))
    (u : Rˣ) (hu : 1 - u.val ∈ I) :
    ∃ v : Sˣ, Units.map (Algebra.norm R (S := S)) v = u := by
  obtain ⟨t, _, ht⟩ := adicComplete_exists_principal_norm b I x hx u.val hu
  have hv : IsUnit (1 + t • x) :=
    (finiteFreeNorm_isUnit_iff b (1 + t • x)).mp (ht.symm ▸ u.isUnit)
  refine ⟨hv.unit, ?_⟩
  apply Units.ext
  change Algebra.norm R hv.unit.val = u.val
  simpa only [IsUnit.unit_spec] using ht

end
end Dubon2026
