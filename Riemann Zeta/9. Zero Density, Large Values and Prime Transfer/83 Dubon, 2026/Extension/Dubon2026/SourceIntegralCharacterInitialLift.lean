import Dubon2026.SourceIntegralCharacterFreeProduct

/-! DUB-17/18 -> original Gamma1 Picard/H1 -> Abel-Jacobi -> unitary
multiplier logarithms -> integral parabolic-character lifting. The actual
free-product universal property lifts a subgroup character that vanishes
on all conjugates of the finite factors. Adapted from the Apache-2.0
pinned primary integral-lift proof in scope 796, revision
6e837e75355538c7f80bab5b956861e86c4eacc2. Native cosetTransition
multiplication is used through the scalar Shapiro construction. Parabolic
vanishing is a separate correction obligation, not assumed proved here. -/
namespace Dubon2026.SourceIntegralCharacterLift
noncomputable section
section Main

variable {ι : Type} {M : ι → Type} [∀ i, Group (M i)]
variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

open Monoid.CoprodI

theorem exists_char_comp_eq_of_forall_conj_of (H : Subgroup (Monoid.CoprodI M)) (π : A →+ B)
    (hπ : Function.Surjective π) (ψ : Additive H →+ B)
    (hψ : ∀ (i : ι) (x : M i) (g : Monoid.CoprodI M) (h : g * of x * g⁻¹ ∈ H),
      ψ (Additive.ofMul ⟨g * of x * g⁻¹, h⟩) = 0) :
    ∃ χ : Additive H →+ A, π.comp χ = ψ ∧
      ∀ (i : ι) (x : M i) (g : Monoid.CoprodI M) (h : g * of x * g⁻¹ ∈ H),
        χ (Additive.ofMul ⟨g * of x * g⁻¹, h⟩) = 0 := by
  classical

  set c₀ := shapiro H ψ with hc₀def
  have hc₀ : IsCrossed c₀ := isCrossed_shapiro H ψ

  have hkill : ∀ (i : ι), ∀ k ∈ (of : M i →* Monoid.CoprodI M).range, ∀ y : Monoid.CoprodI M ⧸ H,
      k • y = y → c₀ k y = 0 := by
    rintro i k ⟨x, rfl⟩ y hy

    have hyr : y = (y.out : Monoid.CoprodI M) • bs H := by rw [smul_bs, QuotientGroup.out_eq']
    set r : Monoid.CoprodI M := y.out
    have hfix : (r⁻¹ * of x * r⁻¹⁻¹) • bs H = bs H := by
      rw [inv_inv, mul_smul, mul_smul, ← hyr, hy, hyr, inv_smul_smul]
    have hmem : r⁻¹ * of x * r⁻¹⁻¹ ∈ H := (smul_bs_eq_bs_iff H _).mp hfix
    have h1 : c₀ (of x) y = c₀ (r * (r⁻¹ * of x * r⁻¹⁻¹) * r⁻¹) (r • bs H) := by
      rw [← hyr]; congr 1; group
    rw [h1, hc₀.conj_apply r _ (bs H) hfix]
    have h2 := hψ i x r⁻¹ hmem
    rwa [← evalBase_shapiro (H := H) ψ, evalBase_apply] at h2

  have hpot : ∀ i : ι, ∃ f : (Monoid.CoprodI M ⧸ H) → B, ∀ x : M i, c₀ (of x) = cob f (of x) := by
    intro i
    obtain ⟨f, hf⟩ := exists_potential hc₀ (of : M i →* Monoid.CoprodI M).range (hkill i)
    exact ⟨f, fun x => hf (of x) ⟨x, rfl⟩⟩
  choose f hf using hpot
  let F : ι → (Monoid.CoprodI M ⧸ H) → A := fun i y => Function.surjInv hπ (f i y)
  have hF : ∀ i y, π (F i y) = f i y := fun i y => Function.surjInv_eq hπ (f i y)

  set C := liftCrossed (M := M) (Ω := Monoid.CoprodI M ⧸ H) F with hCdef
  have hC : IsCrossed C := isCrossed_liftCrossed F
  have hπC : (fun g y => π (C g y)) = c₀ := by
    apply (hC.map π).ext_of hc₀
    intro i m
    funext y
    rw [hCdef, liftCrossed_of, cob_map, hf i m]
    simp only [hF]
  refine ⟨evalBase H C hC, ?_, ?_⟩
  · rw [evalBase_map]
    have hev : ∀ (a b : Monoid.CoprodI M → (Monoid.CoprodI M ⧸ H) → B) (ha : IsCrossed a)
        (hb : IsCrossed b), a = b → evalBase H a ha = evalBase H b hb := by
      rintro a b ha hb rfl; rfl
    rw [hev _ c₀ (hC.map π) hc₀ hπC]
    exact evalBase_shapiro H ψ
  · intro i x g h
    have hfix : of x • g⁻¹ • bs H = g⁻¹ • bs H := (conj_mem_iff_smul (H := H) g (of x)).mp h
    rw [evalBase_conj H C hC g (of x) hfix h, hCdef, liftCrossed_of]
    exact cob_apply_of_smul_eq (F i) hfix

end Main

end
end Dubon2026.SourceIntegralCharacterLift
