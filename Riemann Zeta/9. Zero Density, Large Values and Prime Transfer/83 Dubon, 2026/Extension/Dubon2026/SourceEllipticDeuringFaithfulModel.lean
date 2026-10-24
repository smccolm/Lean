import Dubon2026.SourceEllipticDeuringGoodModel
import Dubon2026.SourceEllipticDeuringGaloisFieldR2
import Dubon2026.SourceEllipticDeuringInertia
import Dubon2026.SourceEllipticDivisionFieldRestriction

/-! DUB-17/18 -> characteristic-two modular genus/Picard -> faithful good-model inertia.
The explicit generator argument is adapted from anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
S_WeierstrassCurve_exists_isGalois_goodModel_inertia_faithful_of_three_ne_zero.
Existing local division-field restriction, torsion reduction and root separation
discharge the source interfaces. No proof-limit or linter override is used. -/
namespace Dubon2026.SourceEllipticDeuring
open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing Polynomial
open SourceEllipticDivisionField
open scoped Pointwise
noncomputable section
variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [DecidableEq Ω]

section Model

variable {E : WeierstrassCurve F} [E.IsElliptic] [IsAlgClosed Ω]
  (h3 : (3 : F) ≠ 0) (L : IntermediateField F Ω) [IsGalois F L]
  (hLfaith : ∀ σ : L ≃ₐ[F] L, (∀ P : (E.baseChange L).toAffine.Point, (3 : ℕ) • P = 0 →
      Point.map (σ : L →ₐ[F] L) P = P) → σ = 1)
  (hcoords : ∀ {x y : Ω} (h : (E.baseChange Ω).toAffine.Nonsingular x y),
      (3 : ℕ) • Point.some x y h = 0 → x ∈ L ∧ y ∈ L)
  (M : IntermediateField F Ω)
  (hM : L ⊔ IntermediateField.adjoin F (cubeRoots (Ω := Ω) E) ≤ M)

include h3 hLfaith hcoords hM in

theorem model_and_faithful (A : ValuationSubring M) (h3A : IsUnit (3 : A))
    (hjA : algebraMap F M E.j ∈ A) :
    ∃ (W : WeierstrassCurve A) (κ : VariableChange M),
      κ • E.baseChange M = W.map A.subtype ∧ IsUnit W.Δ ∧
      ∀ (σ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F),
        (⟨σ, hσ⟩ : A.decompositionSubgroup F) ∈ A.inertiaSubgroup F →
        (∀ P : (E.baseChange M).toAffine.Point, 3 • P = 0 → Point.map (σ : M →ₐ[F] M) P = P) →
        (∃ g : VariableChange A, g.map A.subtype = κ * (κ.map (σ : M →+* M))⁻¹ ∧
            g.map (residue A) = 1) →
        ∀ x : M, (x : Ω) ∈ (L ⊔ IntermediateField.adjoin F (cubeRoots (Ω := Ω) E) :
          IntermediateField F Ω) → σ x = x := by
  haveI hEM : (E.baseChange M).IsElliptic := instIsEllipticMap E (algebraMap F M)
  have hLM : L ≤ M := le_sup_left.trans hM
  have hCM : cubeRoots (Ω := Ω) E ⊆ (M : Set Ω) := fun q hq =>
    hM (le_sup_right (b := IntermediateField.adjoin F (cubeRoots (Ω := Ω) E))
      (IntermediateField.subset_adjoin F _ hq))

  have hval : Function.Injective (IntermediateField.val M) := (IntermediateField.val M).injective
  have hlift : ∀ {x y : Ω} (h : (E.baseChange Ω).toAffine.Nonsingular x y),
      (3 : ℕ) • Point.some x y h = 0 →
      ∃ (hx : x ∈ M) (hy : y ∈ M) (h' : (E.baseChange M).toAffine.Nonsingular ⟨x, hx⟩ ⟨y, hy⟩),
        (3 : ℕ) • Point.some _ _ h' = 0 := by
    intro x y h hP
    obtain ⟨hxL, hyL⟩ := hcoords h hP
    have hx : x ∈ M := hLM hxL
    have hy : y ∈ M := hLM hyL
    have h' : (E.baseChange M).toAffine.Nonsingular ⟨x, hx⟩ ⟨y, hy⟩ :=
      (Affine.baseChange_nonsingular E (f := IntermediateField.val M) hval ⟨x, hx⟩ ⟨y, hy⟩).mp h
    refine ⟨hx, hy, h', ?_⟩
    apply Point.map_injective (IntermediateField.val M)
    rw [map_nsmul, map_zero, Point.map_some]
    exact hP


  obtain ⟨P₀, hP₀, hP₀0⟩ := exists_three_torsion (Ω := Ω) E h3
  rcases P₀ with _ | ⟨x₀, y₀, h₀⟩
  · exact absurd rfl hP₀0
  obtain ⟨hx₀, hy₀, h₀', hP₀M⟩ := hlift h₀ hP₀
  obtain ⟨q₀, hq₀⟩ := IsAlgClosed.exists_pow_nat_eq (psi2 E (.some x₀ y₀ h₀)) (n := 3) (by norm_num)
  have hq₀C : q₀ ∈ cubeRoots (Ω := Ω) E := ⟨_, hP₀, hP₀0, hq₀⟩
  set c : M := ⟨q₀, hCM hq₀C⟩ with hc_def
  have hc : c ^ 3 = 2 * (⟨y₀, hy₀⟩ : M) + (E.baseChange M).a₁ * ⟨x₀, hx₀⟩ + (E.baseChange M).a₃ :=
    Subtype.ext hq₀
  have hjM : (E.baseChange M).j ∈ A := by
    have : (E.baseChange M).j = algebraMap F M E.j := E.map_j (algebraMap F M)
    rw [this]; exact hjA
  obtain ⟨α, κ, hΔ, hκu, hκr, hκs, hκt, hκE⟩ :=
    exists_deuring_good_model A h3A (E.baseChange M) hjM h₀'
      hP₀M hc
  refine ⟨⟨α, 0, 1, 0, 0⟩, κ, hκE, hΔ, ?_⟩

  intro σ hσ hσI hfix hg x hx

  have hfixc : ∀ {x y : Ω} (h : (E.baseChange Ω).toAffine.Nonsingular x y),
      (3 : ℕ) • Point.some x y h = 0 → ∀ (hx : x ∈ M) (hy : y ∈ M),
      σ ⟨x, hx⟩ = ⟨x, hx⟩ ∧ σ ⟨y, hy⟩ = ⟨y, hy⟩ := by
    intro x y h hP hx hy
    obtain ⟨hx', hy', h', hP'⟩ := hlift h hP
    have := hfix _ hP'
    rw [Point.map_some] at this
    exact Point.some.inj this
  obtain ⟨hσx₀, hσy₀⟩ := hfixc h₀ hP₀ hx₀ hy₀
  have hd0 : (2 * (⟨y₀, hy₀⟩ : M) + (E.baseChange M).a₁ * ⟨x₀, hx₀⟩ + (E.baseChange M).a₃) ≠ 0 := by
    rw [← hc]
    intro h
    apply psi2_ne_zero E h₀ hP₀
    rw [← hq₀]
    have : c = 0 := pow_eq_zero_iff (n := 3) (by norm_num) |>.mp h
    have hq : q₀ = 0 := congrArg Subtype.val this
    rw [hq]; ring
  have hc0 : c ≠ 0 := by intro h; apply hd0; rw [← hc, h]; ring
  have hσa₁ : σ (E.baseChange M).a₁ = (E.baseChange M).a₁ := σ.commutes E.a₁
  have hσa₂ : σ (E.baseChange M).a₂ = (E.baseChange M).a₂ := σ.commutes E.a₂
  have hσa₃ : σ (E.baseChange M).a₃ = (E.baseChange M).a₃ := σ.commutes E.a₃
  have hσa₄ : σ (E.baseChange M).a₄ = (E.baseChange M).a₄ := σ.commutes E.a₄
  have hσc3 : σ (c ^ 3) = c ^ 3 := by
    rw [hc, map_add, map_add, map_mul, map_mul, map_ofNat, hσa₁, hσa₃, hσx₀, hσy₀]

  have hσc : σ c = c := by
    obtain ⟨g, hgM, hg1⟩ := hg
    have hσc0 : σ c ≠ 0 := fun h => hc0 (by rw [← map_zero σ] at h; exact σ.injective h)
    let ε : Mˣ := Units.mk0 (σ c) hσc0 * (Units.mk0 c hc0)⁻¹
    have hε : (ε : M) = σ c / c := by simp [ε, div_eq_mul_inv]
    have hκσ : κ.map (σ : M →+* M) = ⟨ε, 0, 0, 0⟩ * κ := by
      apply VariableChange.ext
      · apply Units.ext
        simp only [VariableChange.map, VariableChange.mul_def, Units.coe_map, Units.val_mul, hε]
        show σ (κ.u : M) = σ c / c * κ.u
        rw [hκu, div_mul_cancel₀ _ hc0]
      · simp only [VariableChange.map, VariableChange.mul_def]
        show σ κ.r = 0 * (κ.u : M) ^ 2 + κ.r
        rw [hκr, hσx₀]; ring
      · simp only [VariableChange.map, VariableChange.mul_def]
        show σ κ.s = (κ.u : M) * 0 + κ.s
        rw [hκs, map_div₀]
        simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, hσa₁, hσa₂, hσa₃, hσa₄, hσx₀, hσy₀]
        ring
      · simp only [VariableChange.map, VariableChange.mul_def]
        show σ κ.t = 0 * (κ.u : M) ^ 3 + 0 * κ.s * (κ.u : M) ^ 2 + κ.t
        rw [hκt, hσy₀]; ring
    have hgu : ((g.u : A) : M) = c / σ c := by
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
    have hζ1 : A.valuation (c / σ c - 1) < 1 := by
      have := (A.valuation_lt_one_iff _).mp hmem
      rwa [show (((g.u : A) - 1 : A) : M) = c / σ c - 1 by rw [← hgu]; rfl] at this
    have hζA : A.valuation (c / σ c) ≤ 1 := by rw [← hgu]; exact A.valuation_le_one _
    have hζ3 : (c / σ c) ^ 3 = 1 := by rw [div_pow, ← map_pow, hσc3, div_self (pow_ne_zero 3 hc0)]
    have h1 : c / σ c = 1 := eq_one_of_cube_eq_one A h3A hζA hζ3 hζ1
    rw [div_eq_one_iff_eq hσc0] at h1
    exact h1.symm

  have hLfix : ∀ z : M, (z : Ω) ∈ L → σ z = z :=
    fixes_division_field_of_fixes_torsion E L M hLM 3 hLfaith σ hfix

  have hΔE0 : (E.baseChange M).Δ ≠ 0 := (E.baseChange M).isUnit_Δ.ne_zero
  have hΔκ : A.valuation (((κ.u⁻¹ : Mˣ) : M) ^ 12 * (E.baseChange M).Δ) = 1 := by
    have h1 := congrArg WeierstrassCurve.Δ hκE
    rw [variableChange_Δ, map_Δ] at h1
    rw [h1]
    have h2 : A.valuation ((((⟨α, 0, 1, 0, 0⟩ : WeierstrassCurve A).Δ : A) : M)) = 1 :=
      (A.valuation_eq_one_iff _).mp hΔ
    exact h2
  have hCfix : ∀ z : M, (z : Ω) ∈ cubeRoots (Ω := Ω) E → σ z = z := by
    rintro z ⟨Q, hQ, hQ0, hz3⟩
    rcases Q with _ | ⟨x₁, y₁, h₁⟩
    · exact absurd rfl hQ0
    obtain ⟨hx₁, hy₁, h₁', hQM⟩ := hlift h₁ hQ
    have hzc : z ^ 3 = 2 * (⟨y₁, hy₁⟩ : M) + (E.baseChange M).a₁ * ⟨x₁, hx₁⟩ + (E.baseChange M).a₃ :=
      Subtype.ext hz3

    obtain ⟨α', κ', hΔ', hκ'u, -, -, -, hκ'E⟩ :=
      exists_deuring_good_model A h3A (E.baseChange M) hjM h₁'
        hQM hzc
    have hz0 : z ≠ 0 := by rw [← hκ'u]; exact κ'.u.ne_zero

    set μ : M := z / c with hμ
    have hΔκ' : A.valuation (((κ'.u⁻¹ : Mˣ) : M) ^ 12 * (E.baseChange M).Δ) = 1 := by
      have h1 := congrArg WeierstrassCurve.Δ hκ'E
      rw [variableChange_Δ, map_Δ] at h1
      rw [h1]
      exact (A.valuation_eq_one_iff _).mp hΔ'
    have hvμ : A.valuation μ = 1 := by
      apply val_eq_one_of_pow A (n := 12) (by norm_num)
      have hquot : μ ^ 12 = (((κ.u⁻¹ : Mˣ) : M) ^ 12 * (E.baseChange M).Δ) /
          (((κ'.u⁻¹ : Mˣ) : M) ^ 12 * (E.baseChange M).Δ) := by
        rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, hκu, hκ'u, hμ]
        field_simp
      rw [hquot, map_div₀, hΔκ, hΔκ', div_one]

    obtain ⟨hσx₁, hσy₁⟩ := hfixc h₁ hQ hx₁ hy₁
    have hσz3 : σ (z ^ 3) = z ^ 3 := by
      rw [hzc, map_add, map_add, map_mul, map_mul, map_ofNat, hσa₁, hσa₃, hσx₁, hσy₁]
    have hσμ3 : σ (μ ^ 3) = μ ^ 3 := by
      rw [hμ, div_pow, map_div₀, hσz3, hσc3]
    have hσμ : σ μ = μ := eq_of_inertia_of_cube_eq A h3A hσ hσI hvμ hσμ3
    have hzμ : z = μ * c := by rw [hμ, div_mul_cancel₀ _ hc0]
    rw [hzμ, map_mul, hσμ, hσc]

  let Fix : IntermediateField F M :=
    (AlgHom.equalizer (σ : M →ₐ[F] M) (AlgHom.id F M)).toIntermediateField (by
      intro w hw
      rw [AlgHom.mem_equalizer] at hw ⊢
      rw [map_inv₀, hw]; rfl)
  have hmemFix : ∀ w : M, w ∈ Fix ↔ σ w = w := fun w => by
    show w ∈ AlgHom.equalizer _ _ ↔ _
    rw [AlgHom.mem_equalizer]; rfl
  have hle : (L ⊔ IntermediateField.adjoin F (cubeRoots (Ω := Ω) E) : IntermediateField F Ω) ≤
      IntermediateField.lift Fix := by
    refine sup_le ?_ ?_
    · intro w hw
      exact (IntermediateField.mem_lift (⟨w, hLM hw⟩ : M)).mpr ((hmemFix _).mpr (hLfix ⟨w, hLM hw⟩ hw))
    · apply IntermediateField.adjoin_le_iff.mpr
      intro w hw
      exact (IntermediateField.mem_lift (⟨w, hCM hw⟩ : M)).mpr ((hmemFix _).mpr (hCfix ⟨w, hCM hw⟩ hw))
  have hxFix : x ∈ Fix := (IntermediateField.mem_lift x).mp (hle hx)
  exact (hmemFix x).mp hxFix

end Model

end
end Dubon2026.SourceEllipticDeuring
