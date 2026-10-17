import Dubon2026.OriginalRelationFreeCoordinates
import Dubon2026.OriginalRelationNormObstruction

/-! # Extend a literal norm witness through the original relation cover

Adapt the elementary coordinate construction in the pinned upstream
relation-extension proof. The actual norm is the already proved
coinduction/trace composite. The hypotheses of prime torsion, trivial
coefficient action and divisibility of invariant norms are explicit;
their arithmetic derivation and the converse norm criterion remain
separate obligations on DUB-17's finite class/Ext dependency chain.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped BigOperators
attribute [local instance 1100] Rep.hV2

variable {G : Type} [Group G]

/-- Construct a morphism from the original additive map and its actual equivariance. -/
def originalCoefficientEquivariantAdditiveMap (A C : Rep.{0} ℤ G) (f : A →+ C)
    (h : ∀ (g : G) (x : A), f (A.ρ g x) = C.ρ g (f x)) : A ⟶ C :=
  Rep.ofHom ⟨originalCoefficientAdditiveLinearMap A C f,
    fun g => LinearMap.ext (h g)⟩

variable [Fintype G]

/-- The literal sum of the original coefficient action, as an additive map. -/
def originalCoefficientActionSum (C : Rep.{0} ℤ G) : C →+ C where
  toFun := C.ρ.norm
  map_zero' := map_zero C.ρ.norm
  map_add' := map_add C.ρ.norm

/-- The existing representation norm evaluates to the literal action sum. -/
theorem originalCoefficientActionSum_apply (C : Rep.{0} ℤ G) (c : C) :
    originalCoefficientActionSum C c = ∑ g : G, C.ρ g c := by
  simp [originalCoefficientActionSum, Representation.norm]

/-- Given integral coordinates, norm divisibility constructs an actual equivariant extension of the norm witness. -/
theorem originalRelation_norm_extension_of_coordinates (C : Rep.{0} ℤ G) (p : ℕ)
    (hnorm : ∀ c : C, ∃ d : C, (∀ g : G, C.ρ g d = d) ∧
      (∑ g : G, C.ρ g c) = p • d)
    (B : Rep.{0} ℤ G) (hB : ∀ b : B, p • b = 0)
    (htriv : ∀ (g : G) (b : B), B.ρ g b = b)
    {ι : Type} (a : ι → B) (v : B → (ι →₀ ℤ))
    (hv : ∀ b : B, originalPrimeCoordinateEvaluation B a (v b) = b)
    (hindep : ∀ z : ι →₀ ℤ, originalPrimeCoordinateEvaluation B a z = 0 →
      ∃ y : ι →₀ ℤ, z = p • y)
    (φ : originalRelationModule B ⟶ C) (ψ : originalRelationModule B →+ C)
    (hφ : ∀ x : originalRelationModule B,
      φ.hom x = ∑ g : G, C.ρ g (ψ ((originalRelationModule B).ρ g⁻¹ x))) :
    ∃ χ : Rep.free ℤ G B ⟶ C, originalRelationInclusion B ≫ χ = φ := by
  let val : originalRelationModule B →+ (B →₀ G →₀ ℤ) :=
    (originalRelationInclusion B).hom.toAddMonoidHom
  have val_inj : Function.Injective val := fun _ _ h => Subtype.ext h
  have cov_val : ∀ r : originalRelationModule B, (originalRelationFreeCover B).hom (val r) = 0 :=
    fun r => r.property
  have val_rho : ∀ (g : G) (r : originalRelationModule B),
      val ((originalRelationModule B).ρ g r) = (Rep.free ℤ G B).ρ g (val r) :=
    fun g r => Rep.hom_comm_apply (originalRelationInclusion B) g r
  have hsR : ∀ x : B →₀ G →₀ ℤ, (originalRelationFreeCover B).hom
      (x - originalRelationCoordinateSection B a (originalRelationFreeCoordinates B v x)) = 0 := by
    intro x
    rw [map_sub, originalRelationFreeCover_coordinate_section B a htriv,
      originalRelationFreeCover_eq_coordinate_evaluation B a v hv htriv, sub_self]
  let sR : (B →₀ G →₀ ℤ) →+ originalRelationModule B :=
    AddMonoidHom.mk' (fun x => ⟨_, hsR x⟩) fun x y => val_inj (by
      change x + y - originalRelationCoordinateSection B a
        (originalRelationFreeCoordinates B v (x + y)) =
        (x - originalRelationCoordinateSection B a (originalRelationFreeCoordinates B v x)) +
        (y - originalRelationCoordinateSection B a (originalRelationFreeCoordinates B v y))
      simp only [map_add]
      abel)
  have val_sR : ∀ x, val (sR x) =
      x - originalRelationCoordinateSection B a (originalRelationFreeCoordinates B v x) := fun x => rfl
  have hsecR : ∀ y : ι →₀ ℤ, (originalRelationFreeCover B).hom
      (originalRelationCoordinateSection B a (p • y)) = 0 := by
    intro y
    rw [map_nsmul, map_nsmul, originalRelationFreeCover_coordinate_section B a htriv, hB]
  let secR : (ι →₀ ℤ) →+ originalRelationModule B :=
    AddMonoidHom.mk' (fun y => ⟨_, hsecR y⟩) fun x y => val_inj (by
      change originalRelationCoordinateSection B a (p • (x + y)) =
        originalRelationCoordinateSection B a (p • x) + originalRelationCoordinateSection B a (p • y)
      rw [smul_add, map_add])
  have val_secR : ∀ y, val (secR y) = originalRelationCoordinateSection B a (p • y) := fun y => rfl
  let ω : (ι →₀ ℤ) →+ C := ψ.comp secR
  choose d hd using fun i : ι => hnorm (ω (Finsupp.single i 1))
  let θ : (ι →₀ ℤ) →+ C := Finsupp.liftAddHom fun i => zmultiplesHom C (d i)
  have θ_single : ∀ i n, θ (Finsupp.single i n) = n • d i := fun i n => by simp [θ]
  have hθ1 : ∀ (g : G) (y : ι →₀ ℤ), C.ρ g (θ y) = θ y := by
    intro g y
    suffices h : (C.ρ g).toAddMonoidHom.comp θ = θ from DFunLike.congr_fun h y
    refine Finsupp.addHom_ext fun i n => ?_
    simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, θ_single, map_zsmul, (hd i).1]
  have hθ2 : ∀ y : ι →₀ ℤ, p • θ y = originalCoefficientActionSum C (ω y) := by
    intro y
    let np : C →+ C := AddMonoidHom.mk' (fun c : C => p • c) fun x y => nsmul_add x y p
    suffices h : np.comp θ = (originalCoefficientActionSum C).comp ω from DFunLike.congr_fun h y
    refine Finsupp.addHom_ext' fun i => AddMonoidHom.ext_int ?_
    simp only [AddMonoidHom.comp_apply, Finsupp.singleAddHom_apply, θ_single, one_zsmul]
    simpa only [originalCoefficientActionSum_apply] using ((hd i).2).symm
  let χ₁ : Rep.free ℤ G B ⟶ C := originalCoefficientNormMorphism (Rep.free ℤ G B) C
    (originalCoefficientAdditiveLinearMap (Rep.free ℤ G B) C (ψ.comp sR))
  let χ₂ : Rep.free ℤ G B ⟶ C := originalCoefficientEquivariantAdditiveMap (Rep.free ℤ G B) C
    (θ.comp (originalRelationFreeCoordinates B v)) fun g x => by
      rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
        originalRelationFreeCoordinates_action, hθ1]
  refine ⟨χ₁ + χ₂, Rep.hom_ext (DFunLike.ext _ _ fun r => ?_)⟩
  obtain ⟨y, hy⟩ := hindep (originalRelationFreeCoordinates B v (val r)) (by
    rw [← originalRelationFreeCover_eq_coordinate_evaluation B a v hv htriv, cov_val])
  have hsRr : ∀ g : G, sR ((Rep.free ℤ G B).ρ g⁻¹ (val r)) =
      (originalRelationModule B).ρ g⁻¹ r - secR y := fun g => val_inj (by
        rw [val_sR, map_sub, val_rho, val_secR, originalRelationFreeCoordinates_action, hy])
  have h1 : χ₁.hom (val r) = φ.hom r - originalCoefficientActionSum C (ω y) := by
    rw [hφ, originalCoefficientNormMorphism_apply, originalCoefficientActionSum_apply]
    change (∑ g : G, C.ρ g ((ψ.comp sR) ((Rep.free ℤ G B).ρ g⁻¹ (val r)))) =
      (∑ g : G, C.ρ g (ψ ((originalRelationModule B).ρ g⁻¹ r))) - ∑ g : G, C.ρ g (ω y)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [AddMonoidHom.comp_apply, hsRr, map_sub, map_sub]
    rfl
  have h2 : χ₂.hom (val r) = originalCoefficientActionSum C (ω y) := by
    change θ (originalRelationFreeCoordinates B v (val r)) = _
    rw [hy, map_nsmul, hθ2]
  change χ₁.hom (val r) + χ₂.hom (val r) = φ.hom r
  rw [h1, h2, sub_add_cancel]

/-- For a prime-torsion coefficient with trivial action, invariant norm divisibility turns any actual norm witness into an extension through the literal free cover. -/
theorem originalRelation_exists_extension_of_norm (C : Rep.{0} ℤ G) (p : ℕ) [Fact p.Prime]
    (hnorm : ∀ c : C, ∃ d : C, (∀ g : G, C.ρ g d = d) ∧
      (∑ g : G, C.ρ g c) = p • d)
    (B : Rep.{0} ℤ G) (hB : ∀ b : B, p • b = 0)
    (htriv : ∀ (g : G) (b : B), B.ρ g b = b)
    (φ : originalRelationModule B ⟶ C) (ψ : originalRelationModule B →+ C)
    (hφ : ∀ x : originalRelationModule B,
      φ.hom x = ∑ g : G, C.ρ g (ψ ((originalRelationModule B).ρ g⁻¹ x))) :
    ∃ χ : Rep.free ℤ G B ⟶ C, originalRelationInclusion B ≫ χ = φ := by
  obtain ⟨ι, a, v, hv, hindep⟩ := originalPrimeCoefficient_exists_coordinates B p hB
  exact originalRelation_norm_extension_of_coordinates C p hnorm B hB htriv a v hv hindep φ ψ hφ

end
end Dubon2026
