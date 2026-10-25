import Dubon2026.SourceOriginalPicardGroup

/-! DUB-17/18 -> determinant -> Weil nondegeneracy -> Kummer witness.
A nonzero actual Picard torsion class supplies a principal function that is
not an n-th power. This is the concrete entry into the cover argument;
divisibility and reciprocity on the auxiliary cover remain separate. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L]

omit [NeZero N] in
theorem originalPic0_function_not_power (n : ℕ) [NeZero n]
    (D : Divisor.degZero (K := L) (F := modularFunctionFieldOver N L))
    (hD : Pic0.mk D ≠ 0) (f : modularFunctionFieldOver N L) (hf : f ≠ 0)
    (hord : ∀ v, v.ord f = (n : ℤ) * D.val v) :
    ∀ g : modularFunctionFieldOver N L, g ^ n ≠ f := by
  intro g hg
  apply hD
  apply (Pic0.mk_eq_zero_iff D).mpr
  have hg0 : g ≠ 0 := by
    intro hzero
    rw [hzero, zero_pow (NeZero.ne n)] at hg
    exact hf hg.symm
  refine ⟨g, hg0, fun v => ?_⟩
  apply mul_left_cancel₀ (show (n : ℤ) ≠ 0 from Nat.cast_ne_zero.mpr (NeZero.ne n))
  rw [← hord, ← hg, ← zpow_natCast, v.ord_zpow]

theorem originalPic0_nonzero_torsion_kummer_data (n : ℕ) [NeZero n]
    (x : Pic0.torsion (K := L) (F := modularFunctionFieldOver N L) n) (hx : x ≠ 0) :
    ∃ (D : Divisor.degZero (K := L) (F := modularFunctionFieldOver N L))
      (f : modularFunctionFieldOver N L),
      Pic0.mk D = x.val ∧ f ≠ 0 ∧
        (∀ v, v.ord f = (n : ℤ) * D.val v) ∧
        ∀ g : modularFunctionFieldOver N L, g ^ n ≠ f := by
  obtain ⟨D, f, hf, hD, hdiv⟩ := originalPic0_torsion_representative N L n x.val x.property
  have hord : ∀ v, v.ord f = (n : ℤ) * D.val v := by
    intro v
    have h := congrArg (fun E : Divisor L (modularFunctionFieldOver N L) => E v) hdiv
    simpa only [originalPrincipalDivisor_apply, Finsupp.smul_apply, nsmul_eq_mul] using h
  refine ⟨D, f, hD, hf, hord, originalPic0_function_not_power N L n D ?_ f hf hord⟩
  intro hzero
  exact hx (Subtype.ext (hD.symm.trans hzero))

end
end Dubon2026.SourceFunctionField
