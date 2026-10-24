import Dubon2026.SourceEllipticLegendreFieldRoots
import Dubon2026.SourceEllipticLegendreInertia

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
variable [DecidableEq Ω] {E : WeierstrassCurve F} [E.IsElliptic] [IsAlgClosed Ω]
  (h2 : (2 : F) ≠ 0) {e₁ e₂ e₃ : Ω}
  (h3 : (Cubic.map (algebraMap F Ω) E.twoTorsionPolynomial).roots = {e₁, e₂, e₃})
  (M : IntermediateField F Ω) (hM : IntermediateField.adjoin F (gens e₁ e₂ e₃ : Set Ω) ≤ M)

include h2 h3 hM in

theorem model_and_faithful (A : ValuationSubring M) (h2A : IsUnit (2 : A))
    (hjA : algebraMap F M E.j ∈ A) :
    ∃ (W : WeierstrassCurve A) (κ : VariableChange M),
      κ • E.baseChange M = W.map A.subtype ∧ IsUnit W.Δ ∧
      ∀ (σ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F),
        (⟨σ, hσ⟩ : A.decompositionSubgroup F) ∈ A.inertiaSubgroup F →
        (∀ P : (E.baseChange M).toAffine.Point, 2 • P = 0 → Point.map (σ : M →ₐ[F] M) P = P) →
        (∃ g : VariableChange A, g.map A.subtype = κ * (κ.map (σ : M →+* M))⁻¹ ∧
            g.map (residue A) = 1) →
        ∀ x : M, (x : Ω) ∈ IntermediateField.adjoin F (gens e₁ e₂ e₃ : Set Ω) → σ x = x := by
  haveI hEM : (E.baseChange M).IsElliptic := instIsEllipticMap E (algebraMap F M)
  set f₁ : M := ⟨e₁, mem_M_of_mem_gens M hM e₁_mem_gens⟩ with hf₁
  set f₂ : M := ⟨e₂, mem_M_of_mem_gens M hM e₂_mem_gens⟩ with hf₂
  set f₃ : M := ⟨e₃, mem_M_of_mem_gens M hM e₃_mem_gens⟩ with hf₃
  have h2Ω : (2 : Ω) ≠ 0 := SourceEllipticDivisionField.natCast_ne_zero_of_ne_zero (n := 2) h2
  have h2M : (2 : M) ≠ 0 := fun h => h2Ω (by rw [← map_ofNat (algebraMap M Ω) 2, h, map_zero])
  obtain ⟨h12, h13, h23⟩ : e₁ ≠ e₂ ∧ e₁ ≠ e₃ ∧ e₂ ≠ e₃ := by
    have ha := four_ne_zero E h2
    have hdisc : E.twoTorsionPolynomial.discr ≠ 0 :=
      E.twoTorsionPolynomial_discr_ne_zero (isUnit_iff_ne_zero.mpr h2) E.isUnit_Δ
    exact (Cubic.discr_ne_zero_iff_roots_ne ha h3).mp hdisc

  obtain ⟨q, hq⟩ := IsAlgClosed.exists_pow_nat_eq (e₂ - e₁) (n := 2) (by norm_num)
  have hqg : q ∈ gens e₁ e₂ e₃ := mem_gens_of_sq (by rw [hq]; simp [diffs])
  set w : M := ⟨q, mem_M_of_mem_gens M hM hqg⟩ with hw_def
  have hw : w ^ 2 = f₂ - f₁ := Subtype.ext hq
  have hw0 : w ≠ 0 := by
    intro h
    have : q = 0 := congrArg Subtype.val h
    apply sub_ne_zero.mpr (Ne.symm h12)
    rw [← hq, this]; ring

  have hjM : (E.baseChange M).j ∈ A := by
    have : (E.baseChange M).j = algebraMap F M E.j := E.map_j (algebraMap F M)
    rw [this]; exact hjA
  obtain ⟨l, κ, hlu, hl1u, hΔ, hl, hκu, hκr, hκs, hκt, hκE⟩ :=
    exists_legendre_good_model A h2A (E.baseChange M) hjM
      (roots_M h2 h3 M hM) hw
  refine ⟨legendreCurve l, κ, hκE, hΔ, ?_⟩

  intro σ hσ hσI hfix hg x hx

  have hroot : ∀ f : M, (f = f₁ ∨ f = f₂ ∨ f = f₃) → σ f = f := by
    intro f hf

    have hns : (E.baseChange M).toAffine.Nonsingular f
        (-((E.baseChange M).a₁ * f + (E.baseChange M).a₃) / 2) := by
      have hmem : f ∈ (E.baseChange M).twoTorsionPolynomial.roots := by
        rw [roots_M h2 h3 M hM]
        simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton]
        rcases hf with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
      have h4 : (E.baseChange M).twoTorsionPolynomial.toPoly ≠ 0 := by
        apply Cubic.ne_zero_of_a_ne_zero
        show (4 : M) ≠ 0
        rw [show (4 : M) = 2 * 2 by norm_num]; exact mul_ne_zero h2M h2M
      have hcubic := (Cubic.mem_roots_iff h4 f).mp hmem
      simp only [twoTorsionPolynomial, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆] at hcubic
      rw [← equation_iff_nonsingular, equation_iff,
        show (E.baseChange M).toAffine.a₁ = (E.baseChange M).a₁ from rfl,
        show (E.baseChange M).toAffine.a₂ = (E.baseChange M).a₂ from rfl,
        show (E.baseChange M).toAffine.a₃ = (E.baseChange M).a₃ from rfl,
        show (E.baseChange M).toAffine.a₄ = (E.baseChange M).a₄ from rfl,
        show (E.baseChange M).toAffine.a₆ = (E.baseChange M).a₆ from rfl]
      field_simp
      linear_combination -hcubic
    have h2P : (2 : ℕ) • (Point.some _ _ hns) = 0 := by
      rw [two_nsmul]
      apply Point.add_self_of_Y_eq
      rw [Affine.negY,
        show (E.baseChange M).toAffine.a₁ = (E.baseChange M).a₁ from rfl,
        show (E.baseChange M).toAffine.a₃ = (E.baseChange M).a₃ from rfl]
      field_simp
      ring
    have := hfix _ h2P
    rw [Point.map_some] at this
    exact (Point.some.inj this).1
  have hσ₁ : σ f₁ = f₁ := hroot f₁ (Or.inl rfl)
  have hσ₂ : σ f₂ = f₂ := hroot f₂ (Or.inr (Or.inl rfl))
  have hσ₃ : σ f₃ = f₃ := hroot f₃ (Or.inr (Or.inr rfl))

  have hσw : σ w = w := by
    obtain ⟨g, hgM, hg1⟩ := hg

    have hσw2 : (σ w) ^ 2 = w ^ 2 := by rw [← map_pow, hw, map_sub, hσ₂, hσ₁]
    have hσw0 : σ w ≠ 0 := fun h => hw0 (by rw [← map_zero σ] at h; exact σ.injective h)
    let ε : Mˣ := Units.mk0 (σ w) hσw0 * (Units.mk0 w hw0)⁻¹
    have hε : (ε : M) = σ w / w := by simp [ε, div_eq_mul_inv]
    have hκσ : κ.map (σ : M →+* M) = ⟨ε, 0, 0, 0⟩ * κ := by
      have ha₁ : σ (E.baseChange M).a₁ = (E.baseChange M).a₁ := σ.commutes E.a₁
      have ha₃ : σ (E.baseChange M).a₃ = (E.baseChange M).a₃ := σ.commutes E.a₃
      apply VariableChange.ext
      · apply Units.ext
        simp only [VariableChange.map, VariableChange.mul_def, Units.coe_map, Units.val_mul, hε]
        show σ (κ.u : M) = σ w / w * κ.u
        rw [hκu, div_mul_cancel₀ _ hw0]
      · simp only [VariableChange.map, VariableChange.mul_def]
        show σ κ.r = 0 * (κ.u : M) ^ 2 + κ.r
        rw [hκr, hσ₁]; ring
      · simp only [VariableChange.map, VariableChange.mul_def]
        show σ κ.s = (κ.u : M) * 0 + κ.s
        rw [hκs, map_div₀, map_neg, ha₁, map_ofNat]; ring
      · simp only [VariableChange.map, VariableChange.mul_def]
        show σ κ.t = 0 * (κ.u : M) ^ 3 + 0 * κ.s * (κ.u : M) ^ 2 + κ.t
        rw [hκt, map_div₀, map_neg, map_add, map_mul, ha₁, ha₃, hσ₁, map_ofNat]; ring
    have hgu : ((g.u : A) : M) = w / σ w := by
      have hgM' := hgM
      rw [hκσ, mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul] at hgM'
      have hu := congrArg (fun C : VariableChange M => (C.u : M)) hgM'
      simp only [VariableChange.map, VariableChange.inv_def, Units.coe_map, Units.val_inv_eq_inv_val,
        MonoidHom.coe_coe] at hu
      rw [hε, inv_div] at hu
      exact hu

    have hgu1 : residue A (g.u : A) = 1 := by
      have := congrArg (fun C : VariableChange (ResidueField A) => (C.u : ResidueField A)) hg1
      simp [VariableChange.map] at this
      exact this
    have hmem : (g.u : A) - 1 ∈ IsLocalRing.maximalIdeal A := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hgu1, map_one, sub_self]
    have hval : A.valuation (w / σ w - 1) < 1 := by
      have := (A.valuation_lt_one_iff _).mp hmem
      rwa [show (((g.u : A) - 1 : A) : M) = w / σ w - 1 by rw [← hgu]; rfl] at this

    have hsq : (w / σ w) ^ 2 = 1 := by rw [div_pow, ← hσw2, div_self (pow_ne_zero 2 hσw0)]
    have hpm : (w / σ w - 1) * (w / σ w + 1) = 0 := by linear_combination hsq
    rcases mul_eq_zero.mp hpm with h0 | h0
    · have : w / σ w = 1 := sub_eq_zero.mp h0
      rw [div_eq_one_iff_eq hσw0] at this
      exact this.symm
    · exfalso
      have hm1 : w / σ w = -1 := eq_neg_of_add_eq_zero_left h0
      rw [hm1, show (-1 : M) - 1 = -2 by norm_num, Valuation.map_neg] at hval
      have h2v : A.valuation ((2 : A) : M) = 1 := (A.valuation_eq_one_iff _).mp h2A
      have : A.valuation (2 : M) = 1 := h2v
      rw [this] at hval
      exact lt_irrefl _ hval

  have h2v : A.valuation (2 : M) = 1 := by
    have h := (A.valuation_eq_one_iff _).mp h2A; exact h
  have hlM : (l : M) = (f₃ - f₁) / (f₂ - f₁) := hl
  have hvl : A.valuation ((f₃ - f₁) / (f₂ - f₁)) = 1 := by
    rw [← hlM]; exact (A.valuation_eq_one_iff l).mp hlu
  have hvl1 : A.valuation ((f₃ - f₂) / (f₂ - f₁)) = 1 := by
    have hf21 : (f₂ : M) - f₁ ≠ 0 := by rw [← hw]; exact pow_ne_zero 2 hw0
    have : (f₃ - f₂) / (f₂ - f₁) = -(((1 - l : A) : A) : M) := by
      push_cast
      rw [hlM]; field_simp; ring
    rw [this, Valuation.map_neg]
    exact (A.valuation_eq_one_iff _).mp hl1u
  have hsqfix : ∀ y : M, (y : Ω) ^ 2 ∈ diffs e₁ e₂ e₃ → σ y = y := by
    intro y hy
    obtain ⟨a, b, ha, hb, hab, hd⟩ := exists_of_mem_diffs h12 h13 h23 hy

    obtain ⟨a', rfl, ha'⟩ : ∃ a' : M, (a' : Ω) = a ∧ (a' = f₁ ∨ a' = f₂ ∨ a' = f₃) := by
      rcases ha with rfl | rfl | rfl
      · exact ⟨f₁, rfl, Or.inl rfl⟩
      · exact ⟨f₂, rfl, Or.inr (Or.inl rfl)⟩
      · exact ⟨f₃, rfl, Or.inr (Or.inr rfl)⟩
    obtain ⟨b', rfl, hb'⟩ : ∃ b' : M, (b' : Ω) = b ∧ (b' = f₁ ∨ b' = f₂ ∨ b' = f₃) := by
      rcases hb with rfl | rfl | rfl
      · exact ⟨f₁, rfl, Or.inl rfl⟩
      · exact ⟨f₂, rfl, Or.inr (Or.inl rfl)⟩
      · exact ⟨f₃, rfl, Or.inr (Or.inr rfl)⟩
    have hy2 : y ^ 2 = a' - b' := Subtype.ext hd

    have hf21 : (f₂ : M) - f₁ ≠ 0 := by rw [← hw]; exact pow_ne_zero 2 hw0
    set μ : M := y / w with hμ
    have hμ2 : μ ^ 2 = (a' - b') / (f₂ - f₁) := by rw [hμ, div_pow, hy2, hw]
    have hvμ2 : A.valuation (μ ^ 2) = 1 := by
      rw [hμ2]
      have hab' : a' ≠ b' := fun h => hab (congrArg Subtype.val h)
      rcases ha' with rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl <;>
        first
        | exact absurd rfl hab'
        | skip
      ·
        rw [show (f₁ - f₂) / (f₂ - f₁) = -1 by field_simp; ring, Valuation.map_neg, Valuation.map_one]
      ·
        rw [show (f₁ - f₃) / (f₂ - f₁) = -((f₃ - f₁) / (f₂ - f₁)) by ring, Valuation.map_neg, hvl]
      · rw [div_self hf21, Valuation.map_one]
      ·
        rw [show (f₂ - f₃) / (f₂ - f₁) = -((f₃ - f₂) / (f₂ - f₁)) by ring, Valuation.map_neg, hvl1]
      · exact hvl
      · exact hvl1
    have hvμ : A.valuation μ = 1 := val_eq_one_of_sq A hvμ2
    have hσμ2 : σ (μ ^ 2) = μ ^ 2 := by
      rw [hμ2, map_div₀, map_sub, map_sub, hroot a' ha', hroot b' hb', hσ₂, hσ₁]
    have hσμ : σ μ = μ := eq_of_inertia_of_sq_eq A h2A hσ hσI hvμ hσμ2
    have hyμ : y = μ * w := by rw [hμ, div_mul_cancel₀ _ hw0]
    rw [hyμ, map_mul, hσμ, hσw]

  have hgenfix : ∀ y : M, (y : Ω) ∈ gens e₁ e₂ e₃ → σ y = y := by
    intro y hy
    rcases mem_gens_cases hy with h | h
    · apply hroot
      rcases h with h | h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Or.inl (Subtype.ext h))
      · exact Or.inr (Or.inr (Subtype.ext h))
    · exact hsqfix y h
  let Fix : IntermediateField F M :=
    (AlgHom.equalizer (σ : M →ₐ[F] M) (AlgHom.id F M)).toIntermediateField (by
      intro z hz
      rw [AlgHom.mem_equalizer] at hz ⊢
      rw [map_inv₀, hz]; rfl)
  have hmemFix : ∀ y : M, y ∈ Fix ↔ σ y = y := fun y => by
    show y ∈ AlgHom.equalizer _ _ ↔ _
    rw [AlgHom.mem_equalizer]; rfl
  have hle : IntermediateField.adjoin F (gens e₁ e₂ e₃ : Set Ω) ≤ IntermediateField.lift Fix := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro y hy
    have hyM : y ∈ M := mem_M_of_mem_gens M hM (Finset.mem_coe.mp hy)
    exact (IntermediateField.mem_lift (⟨y, hyM⟩ : M)).mpr
      ((hmemFix _).mpr (hgenfix ⟨y, hyM⟩ (Finset.mem_coe.mp hy)))
  have hxFix : x ∈ Fix := (IntermediateField.mem_lift x).mp (hle hx)
  exact (hmemFix x).mp hxFix


end
end Dubon2026.SourceEllipticLegendreStage
