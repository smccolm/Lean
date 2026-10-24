import Dubon2026.SourceEllipticCyclicAbscissae
import Dubon2026.SourceEllipticTwoQuotientJ

/-! The intrinsic degree-two coefficient step for successive cyclic quotients.
The finite kernel has one nonzero abscissa and its ordinate is forced by exact
order two away from characteristic two. This identifies the abscissa formula
with the existing literal quotient (DUB-17/18 all-level inertia census).
The coefficient formulas adapt Def_WeierstrassCurve_CyclicQuotientJ.lean,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. -/

namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve
noncomputable section
variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

/-- The literal degree-two coefficient contribution determined by its abscissa. -/
def twoAbscissaG (x : F) : F := veluGx W x (-(W.a₁ * x + W.a₃) / 2)

/-- The degree-two quotient coefficients, summed over the actual finite kernel abscissae. -/
def twoAbscissaQuotient (S : Finset F) : WeierstrassCurve F where
  a₁ := W.a₁
  a₂ := W.a₂
  a₃ := W.a₃
  a₄ := W.a₄ - 5 * ∑ x ∈ S, twoAbscissaG W x
  a₆ := W.a₆ - W.b₂ * (∑ x ∈ S, twoAbscissaG W x) -
    7 * ∑ x ∈ S, x * twoAbscissaG W x

/-- An actual subgroup of order two has exactly its unique nonzero point's abscissa. -/
theorem cyclicAbscissae_two_singleton
    (H : AddSubgroup W.toAffine.Point) [Finite H]
    {P : W.toAffine.Point} (hP : addOrderOf P = 2)
    (hPH : AddSubgroup.zmultiples P = H) :
    cyclicAbscissae W H = {(coordsOrZero P).1} := by
  have hP0 : P ≠ 0 := by rintro rfl; simp at hP
  have hf : IsOfFinAddOrder P := by
    by_contra hn
    have hz := addOrderOf_eq_zero hn
    omega
  ext x
  rw [mem_cyclicAbscissae, Finset.mem_singleton]
  constructor
  · rintro ⟨R, hRH, hR0, hx⟩
    rw [← hPH, hf.mem_zmultiples_iff_mem_range_addOrderOf, Finset.mem_image] at hRH
    obtain ⟨k, hk, he⟩ := hRH
    rw [Finset.mem_range, hP] at hk
    have hk0 : k ≠ 0 := by rintro rfl; simp only [zero_nsmul] at he; exact hR0 he.symm
    have hk1 : k = 1 := by omega
    rw [hk1, one_nsmul] at he
    exact hx.symm.trans (congrArg (fun T => (coordsOrZero T).1) he.symm)
  · intro hx
    exact ⟨P, hPH ▸ AddSubgroup.mem_zmultiples P, hP0, hx.symm⟩

/-- The order-two coordinate equation gives precisely the ordinate used by the abscissa formula. -/
theorem two_torsion_y_eq (h2 : (2 : F) ≠ 0) {P : W.toAffine.Point}
    (hP : addOrderOf P = 2) :
    (coordsOrZero P).2 = -(W.a₁ * (coordsOrZero P).1 + W.a₃) / 2 := by
  apply (eq_div_iff h2).mpr
  have h := (two_torsion_coordinates W hP).2
  simp only [veluGy] at h
  linear_combination -h

/-- The intrinsic degree-two quotient is the existing literal quotient by its actual generator. -/
theorem twoAbscissaQuotient_eq (h2 : (2 : F) ≠ 0)
    (H : AddSubgroup W.toAffine.Point) [Finite H]
    {P : W.toAffine.Point} (hP : addOrderOf P = 2)
    (hPH : AddSubgroup.zmultiples P = H) :
    twoAbscissaQuotient W (cyclicAbscissae W H) =
      veluQuotient2 W (coordsOrZero P).1 (coordsOrZero P).2 := by
  rw [cyclicAbscissae_two_singleton W H hP hPH]
  have hG : twoAbscissaG W (coordsOrZero P).1 =
      veluGx W (coordsOrZero P).1 (coordsOrZero P).2 := by
    rw [twoAbscissaG, ← two_torsion_y_eq W h2 hP]
  ext <;> simp [twoAbscissaQuotient, veluQuotient2, hG]

end
end Dubon2026.SourceEllipticVelu
