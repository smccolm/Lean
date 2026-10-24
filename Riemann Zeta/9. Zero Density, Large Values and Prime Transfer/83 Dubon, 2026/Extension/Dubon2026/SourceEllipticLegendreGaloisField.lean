import Dubon2026.SourceEllipticLegendreGenerators

/-! The finite Galois Legendre good-model stage and its faithful inertia.
The generators are the actual two-torsion abscissae and square roots of
their nonzero differences. This realizes the model and action required by
the positive-characteristic exceptional-fiber census, reverse genus and
good reduction in DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, finite Legendre model proof.
Native valuation-ring inertia and the existing explicit good model are reused.
No characteristic-zero Hahn-series route is introduced. -/
namespace Dubon2026.SourceEllipticLegendreStage
open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing Polynomial
open Dubon2026.SourceEllipticLegendre
open scoped Pointwise
noncomputable section
variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
variable [DecidableEq Ω] (E : WeierstrassCurve F) [E.IsElliptic] [IsAlgClosed Ω]
  [Algebra.IsAlgebraic F Ω] (h2 : (2 : F) ≠ 0)

variable {E}

omit [DecidableEq Ω] [E.IsElliptic] [IsAlgClosed Ω] [Algebra.IsAlgebraic F Ω] in
include h2 in

lemma root_iff {e₁ e₂ e₃ : Ω}
    (h3 : (Cubic.map (algebraMap F Ω) E.twoTorsionPolynomial).roots = {e₁, e₂, e₃}) (x : Ω) :
    (E.twoTorsionPolynomial.toPoly.map (algebraMap F Ω)).IsRoot x ↔ (x = e₁ ∨ x = e₂ ∨ x = e₃) := by
  have ha := four_ne_zero E h2
  have hne : E.twoTorsionPolynomial.toPoly.map (algebraMap F Ω) ≠ 0 :=
    Polynomial.map_ne_zero (Cubic.ne_zero_of_a_ne_zero ha)
  rw [← mem_roots hne, ← Cubic.map_toPoly, show (Cubic.map (algebraMap F Ω)
    E.twoTorsionPolynomial).toPoly.roots = (Cubic.map (algebraMap F Ω) E.twoTorsionPolynomial).roots
    from rfl, h3]
  simp

include h2 in

theorem exists_S {e₁ e₂ e₃ : Ω}
    (h3 : (Cubic.map (algebraMap F Ω) E.twoTorsionPolynomial).roots = {e₁, e₂, e₃}) :
    FiniteDimensional F (IntermediateField.adjoin F (gens e₁ e₂ e₃ : Set Ω)) ∧
      IsGalois F (IntermediateField.adjoin F (gens e₁ e₂ e₃ : Set Ω)) := by
  set T := gens e₁ e₂ e₃ with hT
  set S := IntermediateField.adjoin F (T : Set Ω) with hS
  have h2Ω : (2 : Ω) ≠ 0 := SourceEllipticDivisionField.natCast_ne_zero_of_ne_zero (n := 2) h2

  have hsepq := separable_twoTorsion (Ω := Ω) E h2
  have heSC : ∀ x : Ω, (x = e₁ ∨ x = e₂ ∨ x = e₃) → x ∈ separableClosure F Ω := by
    intro x hx
    rw [mem_separableClosure_iff]
    have hroot : (E.twoTorsionPolynomial.toPoly.map (algebraMap F Ω)).IsRoot x := (root_iff h2 h3 x).mpr hx
    have hq : E.twoTorsionPolynomial.toPoly.Separable := (Polynomial.separable_map _).mp hsepq
    have haeval : aeval x E.twoTorsionPolynomial.toPoly = 0 := by rwa [aeval_def, eval₂_eq_eval_map]
    exact hq.of_dvd (minpoly.dvd F x haeval)

  have hsqSC : ∀ q : Ω, q ^ 2 ∈ diffs e₁ e₂ e₃ → q ∈ separableClosure F Ω := by
    intro q hq
    have hdSC : q ^ 2 ∈ separableClosure F Ω := by
      rcases (mem_diffs_iff.mp hq) with h | h | h | h | h | h <;> rw [h] <;>
        first
        | exact sub_mem (heSC _ (Or.inr (Or.inl rfl))) (heSC _ (Or.inl rfl))
        | exact sub_mem (heSC _ (Or.inl rfl)) (heSC _ (Or.inr (Or.inl rfl)))
        | exact sub_mem (heSC _ (Or.inr (Or.inr rfl))) (heSC _ (Or.inl rfl))
        | exact sub_mem (heSC _ (Or.inl rfl)) (heSC _ (Or.inr (Or.inr rfl)))
        | exact sub_mem (heSC _ (Or.inr (Or.inr rfl))) (heSC _ (Or.inr (Or.inl rfl)))
        | exact sub_mem (heSC _ (Or.inr (Or.inl rfl))) (heSC _ (Or.inr (Or.inr rfl)))
    have hd0 : q ^ 2 ≠ 0 := by
      obtain ⟨h12, h13, h23⟩ : e₁ ≠ e₂ ∧ e₁ ≠ e₃ ∧ e₂ ≠ e₃ := by
        have ha := four_ne_zero E h2
        have hdisc : E.twoTorsionPolynomial.discr ≠ 0 :=
          E.twoTorsionPolynomial_discr_ne_zero (isUnit_iff_ne_zero.mpr h2) E.isUnit_Δ
        exact (Cubic.discr_ne_zero_iff_roots_ne ha h3).mp hdisc
      rcases (mem_diffs_iff.mp hq) with h | h | h | h | h | h <;> rw [h] <;>
        first
        | exact sub_ne_zero.mpr (Ne.symm h12) | exact sub_ne_zero.mpr h12
        | exact sub_ne_zero.mpr (Ne.symm h13) | exact sub_ne_zero.mpr h13
        | exact sub_ne_zero.mpr (Ne.symm h23) | exact sub_ne_zero.mpr h23

    let dS : separableClosure F Ω := ⟨q ^ 2, hdSC⟩
    let f : Polynomial (separableClosure F Ω) := X ^ 2 - Polynomial.C dS
    have hfmap : f.map (algebraMap (separableClosure F Ω) Ω) = X ^ 2 - Polynomial.C (q ^ 2) := by
      simp only [f, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]; rfl
    have hfsep : (f.map (algebraMap (separableClosure F Ω) Ω)).Separable := by
      rw [hfmap]; exact separable_X_pow_sub_C _ h2Ω hd0
    have hfroot : (f.map (algebraMap (separableClosure F Ω) Ω)).IsRoot q := by
      rw [hfmap, IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_self]
    rw [mem_separableClosure_iff]
    have hf' : f.Separable := (Polynomial.separable_map _).mp hfsep
    have haeval : aeval q f = 0 := by rwa [aeval_def, eval₂_eq_eval_map]
    have hz : IsSeparable (separableClosure F Ω) q := hf'.of_dvd (minpoly.dvd _ q haeval)
    exact IsSeparable.of_algebra_isSeparable_of_isSeparable F hz
  have hTSC : ∀ x ∈ (T : Set Ω), x ∈ separableClosure F Ω := by
    intro x hx
    rcases mem_gens_cases (Finset.mem_coe.mp hx) with h | h
    · exact heSC x h
    · exact hsqSC x h

  have hfd : FiniteDimensional F S :=
    IntermediateField.finiteDimensional_adjoin fun x _hx =>
      (Algebra.IsAlgebraic.isAlgebraic (R := F) x).isIntegral
  have hsep : Algebra.IsSeparable F S :=
    (IntermediateField.isSeparable_adjoin_iff_isSeparable F Ω).mpr fun x hx =>
      mem_separableClosure_iff.mp (hTSC x hx)

  haveI : Normal F Ω :=
    normal_iff.mpr fun z => ⟨(Algebra.IsAlgebraic.isAlgebraic z).isIntegral, IsAlgClosed.splits _⟩
  have hstab : ∀ (σ : Ω →ₐ[F] Ω) (x : Ω), x ∈ T → σ x ∈ T := by
    intro σ x hx
    have hroots : ∀ y : Ω, (y = e₁ ∨ y = e₂ ∨ y = e₃) → (σ y = e₁ ∨ σ y = e₂ ∨ σ y = e₃) := by
      intro y hy
      rw [← root_iff h2 h3] at hy ⊢
      rw [IsRoot, eval_map, ← aeval_def] at hy ⊢
      rw [aeval_algHom_apply, hy, map_zero]
    rcases mem_gens_cases hx with h | h
    · rcases hroots x h with h' | h' | h' <;> rw [h'] <;> show _ ∈ gens e₁ e₂ e₃ <;> simp [gens]
    · apply mem_gens_of_sq
      rw [← map_pow]

      obtain ⟨h12, h13, h23⟩ : e₁ ≠ e₂ ∧ e₁ ≠ e₃ ∧ e₂ ≠ e₃ := by
        have ha := four_ne_zero E h2
        have hdisc : E.twoTorsionPolynomial.discr ≠ 0 :=
          E.twoTorsionPolynomial_discr_ne_zero (isUnit_iff_ne_zero.mpr h2) E.isUnit_Δ
        exact (Cubic.discr_ne_zero_iff_roots_ne ha h3).mp hdisc
      obtain ⟨a, b, ha, hb, hab, hd⟩ := exists_of_mem_diffs h12 h13 h23 h
      rw [hd, map_sub]
      exact sub_mem_diffs (hroots a ha) (hroots b hb) (fun h' => hab (σ.injective h'))
  have hnormal : Normal F S := by
    refine IntermediateField.normal_iff_forall_map_le.mpr fun σ => ?_
    show (IntermediateField.adjoin F (T : Set Ω)).map σ ≤ IntermediateField.adjoin F (T : Set Ω)
    rw [IntermediateField.adjoin_map]
    refine IntermediateField.adjoin.mono F _ _ ?_
    rintro _ ⟨z, hz, rfl⟩
    exact hstab σ z hz
  haveI := hsep; haveI := hnormal
  exact ⟨hfd, IsGalois.mk⟩


end
end Dubon2026.SourceEllipticLegendreStage
