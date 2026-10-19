import Dubon2026.NumberFieldTameCharacter
import Dubon2026.TameCharacterGenerator

/-! A faithful finite number-field action supplies a normal wild subgroup,
a tame inertia generator and the Frobenius power relation. The original local
finite image will provide the action, inertia inclusion and residue action.
This is the finite presentation input required by ramified auxiliary local
deformations on the route to Dubon Theorem 2.6 through arithmetic patching. -/

namespace Dubon2026

open IsDedekindDomain
open scoped NumberField

theorem finite_numberField_exists_tame_generator
    {F G : Type} [Field F] [NumberField F] [Group G]
    (w : HeightOneSpectrum (𝓞 F)) (p : ℕ) (hp : p.Prime)
    (hpw : (p : 𝓞 F) ∈ w.asIdeal)
    (f : G →* Gal(F/ℚ)) (hf : Function.Injective f)
    (I : Subgroup G) [I.Normal]
    (hI : ∀ g ∈ I, f g ∈ w.asIdeal.inertia Gal(F/ℚ))
    (hstable : ∀ g : G, ∀ x ∈ w.asIdeal, f g • x ∈ w.asIdeal)
    (φ : G) (hφ : ∀ x : 𝓞 F, f φ • x - x ^ p ∈ w.asIdeal) :
    ∃ (t : G) (W : Subgroup G), t ∈ I ∧ W.Normal ∧ IsPGroup p W ∧
      W ≤ I ∧ I = W ⊔ Subgroup.zpowers t ∧
      φ * t * φ⁻¹ * (t ^ p)⁻¹ ∈ W := by
  classical
  obtain ⟨θ, hker, _, hθp, hθφ⟩ := numberField_exists_tame_character w p hp hpw
  let r : I →* w.asIdeal.inertia Gal(F/ℚ) :=
    { toFun := fun g => ⟨f g, hI g g.property⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' := fun a b => Subtype.ext (map_mul f (a : G) (b : G)) }
  have hr : Function.Injective r := by
    intro a b hab
    exact Subtype.ext (hf (congrArg Subtype.val hab))
  let Θ := θ.comp r
  let W := Θ.ker.map I.subtype
  have hWle : W ≤ I := by
    rintro _ ⟨s, _, rfl⟩
    exact s.property
  have hmem : ∀ (s : G) (hs : s ∈ I), s ∈ W ↔ Θ ⟨s, hs⟩ = 1 := by
    intro s hs
    constructor
    · rintro ⟨u, hu, hus⟩
      have he : u = ⟨s, hs⟩ := Subtype.ext hus
      rw [← he]
      exact hu
    · intro hsθ
      exact ⟨⟨s, hs⟩, hsθ, rfl⟩
  have hΘp : IsPGroup p Θ.ker := by
    change IsPGroup p (θ.ker.comap r)
    exact hθp.comap_of_injective r hr
  have hWp : IsPGroup p W := hΘp.map I.subtype
  have hWn : W.Normal := by
    refine ⟨fun s hs g => ?_⟩
    have hsI := hWle hs
    have hgsI : g * s * g⁻¹ ∈ I := Subgroup.Normal.conj_mem inferInstance s hsI g
    rw [hmem _ hgsI]
    change θ ⟨f (g * s * g⁻¹), hI _ hgsI⟩ = 1
    apply (hker _).mpr
    have hsθ := (hmem s hsI).mp hs
    have hs₂ : f s ∈ (w.asIdeal ^ 2).inertia Gal(F/ℚ) := (hker (r ⟨s, hsI⟩)).mp hsθ
    have hconj := TameKernel.inertia_conjugate_mem (w.asIdeal ^ 2) (f g) (f s) hs₂
      (fun x hx => TameKernel.smul_mem_sq_of_forall_smul_mem w.asIdeal (hstable g) hx)
    simpa only [map_mul, map_inv] using hconj
  letI : Field (𝓞 F ⧸ w.asIdeal) := Ideal.Quotient.field w.asIdeal
  letI : IsCyclic Θ.range := Subgroup.isCyclic _
  obtain ⟨t, ht, hgen⟩ := subgroup_eq_character_kernel_sup_zpowers I Θ
  refine ⟨t, W, ht, hWn, hWp, hWle, hgen, ?_⟩
  have hconjI : φ * t * φ⁻¹ ∈ I := Subgroup.Normal.conj_mem inferInstance t ht φ
  have hrelI : φ * t * φ⁻¹ * (t ^ p)⁻¹ ∈ I :=
    I.mul_mem hconjI (I.inv_mem (I.pow_mem ht p))
  have hstableInv : ∀ x ∈ w.asIdeal, (f φ)⁻¹ • x ∈ w.asIdeal := by
    simpa only [map_inv] using hstable φ⁻¹
  have hconjθ : Θ ⟨φ * t * φ⁻¹, hconjI⟩ = Θ ⟨t, ht⟩ ^ p := by
    have h := hθφ (f φ) hφ (hstable φ) hstableInv (r ⟨t, ht⟩)
    simpa only [Θ, MonoidHom.comp_apply, r, MonoidHom.coe_mk, OneHom.coe_mk,
      map_mul, map_inv] using h
  rw [hmem _ hrelI]
  have he : (⟨φ * t * φ⁻¹ * (t ^ p)⁻¹, hrelI⟩ : I) =
      ⟨φ * t * φ⁻¹, hconjI⟩ * (⟨t, ht⟩ ^ p)⁻¹ := rfl
  rw [he, map_mul, map_inv, map_pow, hconjθ, mul_inv_cancel]

end Dubon2026
