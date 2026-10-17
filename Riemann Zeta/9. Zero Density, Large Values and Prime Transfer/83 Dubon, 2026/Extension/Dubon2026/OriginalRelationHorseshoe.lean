/-
Copyright (c) 2026 Anthropic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Adapted from the actual horseshoe construction in P2M/Sol/
S_Rep_exists_eq_comp_add_comp_of_forall_map_delta_eq_zero_of_shortExact_of_projective.lean
at revision 6e837e75355538c7f80bab5b956861e86c4eacc2. Pinned projectivity
and exactness replace external lifting and sequence helper assumptions.
-/
import Dubon2026.OriginalPresentationComparison

/-! # A literal horseshoe presentation for relation-kernel decomposition

This constructs both genuine short exact sequences and their commuting
maps from the original coefficient sequence and presentations. Its kernel
sequence supplies the integral retraction needed to transport a norm
witness in DUB-17's nontrivial-action relation-extension argument.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance 1100] Rep.hV2

/-- The actual coefficient sequence and projective right presentation
construct a horseshoe presentation and its literal relation-kernel sequence. -/
theorem originalRelation_horseshoe
    {G : Type} [Group G]
    {SB : ShortComplex (Rep.{0} ℤ G)} (hSB : SB.ShortExact)
    {R_B P_B : Rep.{0} ℤ G} (f_B : R_B ⟶ P_B) (g_B : P_B ⟶ SB.X₁) (w_B : f_B ≫ g_B = 0)
    (hT_B : (ShortComplex.mk f_B g_B w_B).ShortExact)
    {R₁ P₁ : Rep.{0} ℤ G} (f₁ : R₁ ⟶ P₁) (g₁ : P₁ ⟶ SB.X₃) (w₁ : f₁ ≫ g₁ = 0)
    (hT₁ : (ShortComplex.mk f₁ g₁ w₁).ShortExact)
    [Projective P₁] :
    ∃ (R : Rep.{0} ℤ G) (f : R ⟶ P_B ⊞ P₁) (g : P_B ⊞ P₁ ⟶ SB.X₂) (w : f ≫ g = 0)
      (_ : (ShortComplex.mk f g w).ShortExact)
      (j : R_B ⟶ R) (q : R ⟶ R₁) (wR : j ≫ q = 0) (_ : (ShortComplex.mk j q wR).ShortExact),
      f_B ≫ biprod.inl = j ≫ f ∧ g_B ≫ SB.f = biprod.inl ≫ g ∧ f ≫ biprod.snd = q ≫ f₁ ∧ g ≫ SB.g = biprod.snd ≫ g₁ := by
  classical

  have capp : ∀ {X Y Z : Rep.{0} ℤ G} (a : X ⟶ Y) (b : Y ⟶ Z) (x : X), (a ≫ b).hom x = b.hom (a.hom x) :=
    fun a b x => rfl
  have hex : ∀ {X Y Z : Rep.{0} ℤ G} (a : X ⟶ Y) (b : Y ⟶ Z) (w : a ≫ b = 0),
      (ShortComplex.mk a b w).Exact → ∀ y : Y, b.hom y = 0 → ∃ x : X, a.hom x = y :=
    fun a b w h y hy => by
      have ht := h.map (forget₂ (Rep.{0} ℤ G) (ModuleCat ℤ))
      rw [ShortComplex.moduleCat_exact_iff] at ht
      exact ht y hy
  have hsurj : ∀ {X Y : Rep.{0} ℤ G} (e : X ⟶ Y), Epi e → Function.Surjective e.hom :=
    fun e he => (Rep.epi_iff_surjective e).1 he
  have hinj : ∀ {X Y : Rep.{0} ℤ G} (e : X ⟶ Y), Mono e → Function.Injective e.hom :=
    fun e he => (Rep.mono_iff_injective e).1 he

  letI := hSB.epi_g
  let lam := Projective.factorThru g₁ SB.g
  have hlam : lam ≫ SB.g = g₁ := Projective.factorThru_comp _ _
  let g : P_B ⊞ P₁ ⟶ SB.X₂ := biprod.desc (g_B ≫ SB.f) lam
  have hinl_g : biprod.inl ≫ g = g_B ≫ SB.f := biprod.inl_desc _ _
  have hinr_g : biprod.inr ≫ g = lam := biprod.inr_desc _ _
  have hgρ : g ≫ SB.g = biprod.snd ≫ g₁ := by
    apply biprod.hom_ext'
    · rw [← Category.assoc, hinl_g, Category.assoc, SB.zero, comp_zero, ← Category.assoc, biprod.inl_snd, zero_comp]
    · rw [← Category.assoc, hinr_g, hlam, ← Category.assoc, biprod.inr_snd, Category.id_comp]

  let f : kernel g ⟶ P_B ⊞ P₁ := kernel.ι g
  have w : f ≫ g = 0 := kernel.condition g
  have hg_surj : Function.Surjective g.hom := by
    intro i
    obtain ⟨p₁, hp₁⟩ := hsurj g₁ hT₁.epi_g (SB.g.hom i)
    have h0 : SB.g.hom (i - lam.hom p₁) = 0 := by
      rw [map_sub, ← capp lam SB.g, hlam, hp₁, sub_self]
    obtain ⟨b, hb⟩ := hex SB.f SB.g SB.zero hSB.exact _ h0
    obtain ⟨p, hp⟩ := hsurj g_B hT_B.epi_g b
    refine ⟨(biprod.inl : P_B ⟶ P_B ⊞ P₁).hom p + (biprod.inr : P₁ ⟶ P_B ⊞ P₁).hom p₁, ?_⟩
    rw [map_add, ← capp, ← capp, hinl_g, hinr_g, capp, hp, hb, sub_add_cancel]
  have hTg : (ShortComplex.mk f g w).ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel g)
      mono_f := by dsimp; infer_instance
      epi_g := (Rep.epi_iff_surjective g).2 hg_surj }

  have hj0 : (f_B ≫ biprod.inl) ≫ g = 0 := by
    rw [Category.assoc, hinl_g, ← Category.assoc, w_B, zero_comp]
  let j : R_B ⟶ kernel g := kernel.lift g (f_B ≫ biprod.inl) hj0
  have hj : j ≫ f = f_B ≫ biprod.inl := kernel.lift_ι _ _ _
  haveI : Mono f₁ := hT₁.mono_f
  haveI : Mono f_B := hT_B.mono_f
  haveI : Mono SB.f := hSB.mono_f
  have hq0 : (f ≫ biprod.snd) ≫ (ShortComplex.mk f₁ g₁ w₁).g = 0 := by
    change (f ≫ biprod.snd) ≫ g₁ = 0
    rw [Category.assoc, ← hgρ, ← Category.assoc, w, zero_comp]
  let q : kernel g ⟶ R₁ := hT₁.exact.lift (f ≫ biprod.snd) hq0
  have hq : q ≫ f₁ = f ≫ biprod.snd := hT₁.exact.lift_f _ _
  have wR : j ≫ q = 0 := by
    rw [← cancel_mono f₁, Category.assoc, hq, ← Category.assoc, hj, Category.assoc, biprod.inl_snd, comp_zero,
      zero_comp]
  have hRexact : (ShortComplex.mk j q wR).Exact := by
        apply ((ShortComplex.mk j q wR).exact_map_iff_of_faithful
          (forget₂ (Rep.{0} ℤ G) (ModuleCat ℤ))).mp
        rw [ShortComplex.moduleCat_exact_iff]
        intro r hr'
        change q.hom r = 0 at hr' 

        have hsnd : (biprod.snd : P_B ⊞ P₁ ⟶ P₁).hom (f.hom r) = 0 := by
          rw [← capp, ← hq, capp, hr', map_zero]
        set p := (biprod.fst : P_B ⊞ P₁ ⟶ P_B).hom (f.hom r) with hpdef
        have htot : f.hom r = (biprod.inl : P_B ⟶ P_B ⊞ P₁).hom p := by
          have := congrArg (fun t : P_B ⊞ P₁ ⟶ P_B ⊞ P₁ => t.hom (f.hom r)) (biprod.total : _ = 𝟙 (P_B ⊞ P₁))
          simp only [Rep.add_hom] at this
          rw [hpdef]
          change ((biprod.fst : P_B ⊞ P₁ ⟶ P_B) ≫ (biprod.inl : P_B ⟶ P_B ⊞ P₁)).hom (f.hom r) +
              ((biprod.snd : P_B ⊞ P₁ ⟶ P₁) ≫ (biprod.inr : P₁ ⟶ P_B ⊞ P₁)).hom (f.hom r) =
            (𝟙 (P_B ⊞ P₁) : _ ⟶ _).hom (f.hom r) at this
          rw [capp biprod.snd, hsnd, map_zero, add_zero] at this
          exact this.symm

        have hgBp : g_B.hom p = 0 := by
          apply hinj SB.f inferInstance
          rw [map_zero, ← capp, ← hinl_g, capp, ← htot, ← capp, w]
          rfl
        obtain ⟨rB, hrB⟩ := hex f_B g_B w_B hT_B.exact p hgBp
        refine ⟨rB, ?_⟩
        apply hinj f inferInstance
        change f.hom (j.hom rB) = f.hom r
        rw [← capp, hj, capp, hrB, htot]
  have hRmono : Mono j := by
    haveI : Mono (j ≫ f) := by rw [hj]; exact mono_comp _ _
    exact mono_of_mono j f
  have hRepi : Epi q := by
        refine (Rep.epi_iff_surjective q).2 fun r₁ => ?_

        have h0 : SB.g.hom (lam.hom (f₁.hom r₁)) = 0 := by
          rw [← capp lam SB.g, hlam, ← capp f₁ g₁, w₁]
          rfl
        obtain ⟨b, hb⟩ := hex SB.f SB.g SB.zero hSB.exact _ h0
        obtain ⟨p, hp⟩ := hsurj g_B hT_B.epi_g b
        let x : ((P_B ⊞ P₁ : Rep.{0} ℤ G) : Type) := (biprod.inr : P₁ ⟶ P_B ⊞ P₁).hom (f₁.hom r₁) - (biprod.inl : P_B ⟶ P_B ⊞ P₁).hom p
        have hxdef : x = (biprod.inr : P₁ ⟶ P_B ⊞ P₁).hom (f₁.hom r₁) - (biprod.inl : P_B ⟶ P_B ⊞ P₁).hom p := rfl
        have hgx : g.hom x = 0 := by
          rw [hxdef, map_sub, ← capp biprod.inr g, hinr_g, ← capp biprod.inl g, hinl_g, capp, hp, hb, sub_self]
        obtain ⟨r, hr⟩ := hex f g w hTg.exact x hgx
        refine ⟨r, ?_⟩
        apply hinj f₁ inferInstance
        rw [← capp, hq, capp, hr, hxdef, map_sub, ← capp biprod.inr biprod.snd, biprod.inr_snd,
          ← capp biprod.inl biprod.snd, biprod.inl_snd]
        simp
  have hR : (ShortComplex.mk j q wR).ShortExact := { exact := hRexact, mono_f := hRmono, epi_g := hRepi }

  refine ⟨kernel g, f, g, w, hTg, j, q, wR, hR, hj.symm, hinl_g.symm, hq.symm, hgρ⟩

end
end Dubon2026
