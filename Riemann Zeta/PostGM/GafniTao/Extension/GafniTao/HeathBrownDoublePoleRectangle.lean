import RiemannZeta.GuthMaynard.DivisorVoronoi

/-!
# A rectangle theorem for a double pole

This is the exact contour primitive needed for Heath--Brown's Mellin shift.
If `N` is holomorphic on a rectangle and `p` is in its interior, then
`N(w)/(w-p)^2` contributes the derivative `N'(p)`.  The pure order-two
term is retained explicitly and cancelled by its closed-rectangle integral;
the remaining order-one term is handled by the repository's audited simple
pole theorem.
-/

open Complex Set
open scoped Topology

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Exact normalized rectangle integral of a holomorphic numerator divided
by a squared Cauchy kernel. -/
theorem rectangleIntegral'_div_sq_eq_deriv
    {N : ℂ → ℂ} {z w p : ℂ}
    (hzre : z.re ≤ w.re) (hzim : z.im ≤ w.im)
    (hp : Rectangle z w ∈ 𝓝 p)
    (hN : DifferentiableOn ℂ N (Rectangle z w)) :
    RectangleIntegral' (fun u : ℂ => N u / (u - p) ^ 2) z w =
      deriv N p := by
  let D : ℂ → ℂ := dslope N p
  let R : ℂ → ℂ := dslope D p
  let C : ℂ := N p
  let A : ℂ := D p
  let f : ℂ → ℂ := fun u => N u / (u - p) ^ 2
  let f₁ : ℂ → ℂ := fun u => f u - C / (u - p) ^ 2
  have hD : HolomorphicOn D (Rectangle z w) := by
    change DifferentiableOn ℂ D (Rectangle z w)
    dsimp only [D]
    exact (Complex.differentiableOn_dslope hp).2 hN
  have hR : HolomorphicOn R (Rectangle z w) := by
    change DifferentiableOn ℂ R (Rectangle z w)
    dsimp only [R]
    exact (Complex.differentiableOn_dslope hp).2 hD
  have hPrincipal : Set.EqOn
      (f₁ - fun u => A / (u - p)) R (Rectangle z w \ {p}) := by
    intro u hu
    have hup : u ≠ p := hu.2
    have hND := sub_smul_dslope N p u
    have hDR := sub_smul_dslope D p u
    change (u - p) * D u = N u - N p at hND
    change (u - p) * R u = D u - D p at hDR
    change N u / (u - p) ^ 2 - N p / (u - p) ^ 2 -
        D p / (u - p) = R u
    have huSub : u - p ≠ 0 := sub_ne_zero.mpr hup
    calc
      N u / (u - p) ^ 2 - N p / (u - p) ^ 2 - D p / (u - p) =
          (N u - N p) / (u - p) ^ 2 - D p / (u - p) := by ring
      _ = ((u - p) * D u) / (u - p) ^ 2 - D p / (u - p) := by
        rw [hND]
      _ = D u / (u - p) - D p / (u - p) := by
        field_simp [huSub]
      _ = (D u - D p) / (u - p) := by ring
      _ = ((u - p) * R u) / (u - p) := by rw [hDR]
      _ = R u := by field_simp [huSub]
  have hSimple := ResidueTheoremOnRectangleWithSimplePole
    (f := f₁) (g := R) (p := p) (A := A)
    hzre hzim hp hR hPrincipal
  have hDouble := rectangleIntegral'_const_div_sq_eq_zero
    (C := C) (p := p) hzre hzim hp
  have hf₁Holo : HolomorphicOn f₁ (Rectangle z w \ {p}) := by
    intro u hu
    have hup : u ≠ p := hu.2
    have huRect : u ∈ Rectangle z w := hu.1
    have hQuotient : DifferentiableWithinAt ℂ
        (fun v => N v / (v - p) ^ 2 - C / (v - p) ^ 2)
        (Rectangle z w) u := ((hN u huRect).div
        ((differentiableAt_id.sub_const p).pow 2).differentiableWithinAt
          (pow_ne_zero 2 (sub_ne_zero.mpr hup))).sub
      (differentiableWithinAt_const C |>.div
        ((differentiableAt_id.sub_const p).pow 2).differentiableWithinAt
          (pow_ne_zero 2 (sub_ne_zero.mpr hup)))
    simpa only [f₁, f] using hQuotient.mono (diff_subset)
  have hDoubleHolo : HolomorphicOn
      (fun u : ℂ => C / (u - p) ^ 2) (Rectangle z w \ {p}) := by
    intro u hu
    apply DifferentiableAt.differentiableWithinAt
    exact differentiableAt_const C |>.div
      ((differentiableAt_id.sub_const p).pow 2)
      (pow_ne_zero 2 (sub_ne_zero.mpr hu.2))
  have hf₁Int : RectangleBorderIntegrable f₁ z w :=
    HolomorphicOn.rectangleBorderIntegrable' hf₁Holo hp
  have hDoubleInt : RectangleBorderIntegrable
      (fun u : ℂ => C / (u - p) ^ 2) z w :=
    HolomorphicOn.rectangleBorderIntegrable' hDoubleHolo hp
  have hPoint : f = f₁ + fun u : ℂ => C / (u - p) ^ 2 := by
    funext u
    change f u = (f u - C / (u - p) ^ 2) + C / (u - p) ^ 2
    ring
  have hRectAdd : RectangleIntegral f z w = RectangleIntegral f₁ z w +
      RectangleIntegral (fun u : ℂ => C / (u - p) ^ 2) z w := by
    rw [hPoint]
    exact RectangleBorderIntegrable.add hf₁Int hDoubleInt
  have hA : A = deriv N p := by
    dsimp only [A, D]
    rw [dslope_same]
  change RectangleIntegral' f z w = deriv N p
  unfold RectangleIntegral' at hSimple hDouble ⊢
  rw [hRectAdd, smul_add, hSimple, hDouble, add_zero, hA]


end

end GafniTao
