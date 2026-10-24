import Dubon2026.SourceEllipticPreDivisionSeparable

/-! Every prime-to-characteristic torsion point has separable coordinates.
The direct pre-division-polynomial root count replaces the archived order
induction, including its special order-four and descent arguments.
This is the finite Galois torsion-field input to the actual reduction action
and exceptional-fiber census in DUB-17/18. -/
namespace Dubon2026.SourceEllipticDivisionField
open WeierstrassCurve WeierstrassCurve.Affine Polynomial
noncomputable section
variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]

theorem natCast_ne_zero_of_ne_zero {n : ℕ} (hn : (n : F) ≠ 0) : (n : Ω) ≠ 0 := by
  intro hz
  apply hn
  apply (algebraMap F Ω).injective
  simpa only [map_natCast, map_zero] using hz

theorem natCast_ne_zero_of_dvd {n d : ℕ} (hn : (n : F) ≠ 0) (hd : d ∣ n) :
    (d : F) ≠ 0 := by
  obtain ⟨k, rfl⟩ := hd
  rw [Nat.cast_mul] at hn
  exact left_ne_zero_of_mul hn

theorem mem_separableClosure_of_root_F {z : Ω} (q : Polynomial F)
    (hsep : (q.map (algebraMap F Ω)).Separable)
    (hroot : (q.map (algebraMap F Ω)).IsRoot z) : z ∈ separableClosure F Ω := by
  rw [mem_separableClosure_iff]
  have hq : q.Separable := (Polynomial.separable_map (algebraMap F Ω)).mp hsep
  have haeval : aeval z q = 0 := by rwa [aeval_def, eval₂_eq_eval_map]
  exact hq.of_dvd (minpoly.dvd F z haeval)

variable [DecidableEq Ω] [IsAlgClosed Ω] (E : WeierstrassCurve F) [E.IsElliptic]

theorem two_torsion_x_separable {x y : Ω} (h : (E.baseChange Ω).toAffine.Nonsingular x y)
    (h2 : (2 : F) ≠ 0) (hP : (2 : ℕ) • Point.some x y h = 0) :
    x ∈ separableClosure F Ω := by
  refine mem_separableClosure_of_root_F E.twoTorsionPolynomial.toPoly ?_ ?_
  · have hsplit : ((E.twoTorsionPolynomial.toPoly).map (algebraMap F Ω)).Splits :=
      IsAlgClosed.splits _
    have ha : E.twoTorsionPolynomial.a ≠ 0 := by
      show (4 : F) ≠ 0
      simpa only [show (4 : F) = 2 * 2 by norm_num] using mul_ne_zero h2 h2
    have hdisc : E.twoTorsionPolynomial.discr ≠ 0 :=
      E.twoTorsionPolynomial_discr_ne_zero (Ne.isUnit h2) E.isUnit_Δ
    have hnodup := (Cubic.discr_ne_zero_iff_roots_nodup ha hsplit).mp hdisc
    rw [Cubic.roots, Cubic.map_toPoly] at hnodup
    exact (nodup_roots_iff_of_splits
      (Polynomial.map_ne_zero (Cubic.ne_zero_of_a_ne_zero ha)) hsplit).mp hnodup
  · have hr := (two_nsmul_eq_zero_iff_division_eval (E.baseChange Ω) h).mp hP
    rw [Ψ₂Sq_eq] at hr
    have hm : (E.baseChange Ω).twoTorsionPolynomial =
        Cubic.map (algebraMap F Ω) E.twoTorsionPolynomial := by
      simp only [twoTorsionPolynomial, Cubic.map, WeierstrassCurve.baseChange,
        map_b₂, map_b₄, map_b₆, map_ofNat, map_mul]
    rw [hm, Cubic.map_toPoly] at hr
    exact hr

theorem mem_sepPoints_of_nsmul_eq_zero {n : ℕ} (hn : (n : F) ≠ 0)
    (P : (E.baseChange Ω).toAffine.Point) (hP : n • P = 0) : P ∈ sepPoints E := by
  rcases P with _ | ⟨x, y, h⟩
  · exact zero_mem _
  rw [some_mem_sepPoints_iff]
  by_cases hP2 : (2 : ℕ) • Point.some x y h = 0
  · have hord : addOrderOf (Point.some x y h) = 2 := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact addOrderOf_eq_prime hP2 (Point.some_ne_zero h)
    have h2n : 2 ∣ n := hord ▸ addOrderOf_dvd_of_nsmul_eq_zero hP
    have h2F : (2 : F) ≠ 0 := natCast_ne_zero_of_dvd hn h2n
    have hx := two_torsion_x_separable E h h2F hP2
    exact ⟨hx, Y_mem_of_X_mem h.1 hx (Or.inr h2F)⟩
  · have hnΩ : (n : Ω) ≠ 0 := natCast_ne_zero_of_ne_zero hn
    have hmap : (E.preΨ n).map (algebraMap F Ω) = (E.baseChange Ω).preΨ n :=
      (E.map_preΨ (algebraMap F Ω) n).symm
    have hx : x ∈ separableClosure F Ω := by
      refine mem_separableClosure_of_root_F (E.preΨ n) ?_ ?_ <;> rw [hmap]
      · exact preDivision_separable (E.baseChange Ω) hnΩ
      · exact preDivision_eval_zero_of_torsion (E.baseChange Ω) h hP (fun _ => hP2)
    refine ⟨hx, Y_mem_of_X_mem h.1 hx (Or.inl ?_)⟩
    intro hy
    exact hP2 (by rw [two_nsmul]; exact Point.add_self_of_Y_eq hy)

end
end Dubon2026.SourceEllipticDivisionField
