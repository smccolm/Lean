import Dubon2026.SourceEllipticVeluTwoNonsingular

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> higher symmetric-power
continuation -> arithmetic automorphy -> original Frobenius/inertia -> good
reduction -> reverse genus -> finite exceptional fibers -> elliptic inertia
orbits -> cyclic-quotient interpretation of modular-polynomial roots.
This step proves ellipticity of the literal degree-two Velu curve and enumerates
the three nonzero two-torsion coordinates in characteristic different from two.
The quotient group map, kernel and modular-polynomial identity remain required.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, the six VeluOrderTwo discriminant
solutions and the two-torsion enumeration solution. Polynomial elimination
replaces the source's large linear-combination certificates. -/
namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve
noncomputable section
theorem EnumTwoAux.twoTorsionPair {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    (W : WeierstrassCurve K) {x₀ : K}
    (hx : 4 * x₀ ^ 3 + W.b₂ * x₀ ^ 2 + 2 * W.b₄ * x₀ + W.b₆ = 0) :
    W.toAffine.Equation x₀ (-(W.a₁ * x₀ + W.a₃) / 2) ∧
      veluGy W x₀ (-(W.a₁ * x₀ + W.a₃) / 2) = 0 := by
  constructor
  · rw [WeierstrassCurve.Affine.equation_iff]
    simp only [b₂, b₄, b₆] at hx
    field_simp
    linear_combination -hx
  · simp only [veluGy]
    field_simp
    ring

theorem exists_enum_twoTorsion_veluQuotient2_discriminant_ne_zero
    {K : Type*} [Field K] [IsAlgClosed K] (h2 : (2 : K) ≠ 0)
    (W : WeierstrassCurve K) [W.IsElliptic] :
    ∃ (ι : Type) (_ : Fintype ι), Fintype.card ι = 3 ∧
      ∃ P : ι → K × K, Function.Injective P ∧
        (∀ i, W.toAffine.Equation (P i).1 (P i).2) ∧ (∀ i, veluGy W (P i).1 (P i).2 = 0) ∧
        ∀ i, (veluQuotient2 W (P i).1 (P i).2).Δ ≠ 0 := by
  classical

  set C3 : Cubic K := W.twoTorsionPolynomial with hC3
  have ha : C3.a ≠ 0 := by
    show (4 : K) ≠ 0
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have hsplit : (Polynomial.map (RingHom.id K) C3.toPoly).Splits := IsAlgClosed.splits _
  obtain ⟨x₁, x₂, x₃, h3⟩ := (Cubic.splits_iff_roots_eq_three ha).mp hsplit
  have hdisc : C3.discr ≠ 0 :=
    W.twoTorsionPolynomial_discr_ne_zero (isUnit_iff_ne_zero.mpr h2) W.isUnit_Δ
  have hnodup : (Cubic.map (RingHom.id K) C3).roots.Nodup :=
    (Cubic.discr_ne_zero_iff_roots_nodup ha hsplit).mp hdisc
  rw [h3] at hnodup
  have h12 : x₁ ≠ x₂ := by intro h; subst h; simp at hnodup
  have h13 : x₁ ≠ x₃ := by intro h; subst h; simp at hnodup
  have h23 : x₂ ≠ x₃ := by intro h; subst h; simp at hnodup
  have ha' : (Cubic.map (RingHom.id K) C3).a ≠ 0 := by simpa [Cubic.map] using ha
  have hroot : ∀ x ∈ ({x₁, x₂, x₃} : Multiset K),
      4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ = 0 := by
    intro x hx
    have hx' : x ∈ (Cubic.map (RingHom.id K) C3).roots := by rw [h3]; exact hx
    have := (Cubic.mem_roots_iff (Cubic.ne_zero_of_a_ne_zero ha') x).mp hx'
    simpa [Cubic.map, hC3, twoTorsionPolynomial] using this

  let yy : K → K := fun x => -(W.a₁ * x + W.a₃) / 2
  let P : Fin 3 → K × K := ![(x₁, yy x₁), (x₂, yy x₂), (x₃, yy x₃)]
  have hPfst : ∀ i, (P i).1 ∈ ({x₁, x₂, x₃} : Multiset K) := by
    intro i; fin_cases i <;> simp [P]
  have hPsnd : ∀ i, (P i).2 = yy (P i).1 := by
    intro i; fin_cases i <;> rfl
  have hPpair : ∀ i, W.toAffine.Equation (P i).1 (P i).2 ∧ veluGy W (P i).1 (P i).2 = 0 := by
    intro i; rw [hPsnd]; exact EnumTwoAux.twoTorsionPair h2 W (hroot _ (hPfst i))
  have hPinj : Function.Injective P := by
    intro i i' h
    have h1 := congrArg Prod.fst h
    fin_cases i <;> fin_cases i' <;> simp [P] at h1 ⊢ <;> simp_all
  have hΔ : ∀ i, (veluQuotient2 W (P i).1 (P i).2).Δ ≠ 0 := fun i =>
    (@WeierstrassCurve.isUnit_Δ _ _ (veluQuotient2 W (P i).1 (P i).2)
      (isElliptic_veluQuotient2_of_isElliptic (hPpair i).1 (hPpair i).2)).ne_zero
  exact ⟨Fin 3, inferInstance, Fintype.card_fin 3, P, hPinj, fun i => (hPpair i).1, fun i => (hPpair i).2, hΔ⟩

end
end Dubon2026.SourceEllipticVelu
