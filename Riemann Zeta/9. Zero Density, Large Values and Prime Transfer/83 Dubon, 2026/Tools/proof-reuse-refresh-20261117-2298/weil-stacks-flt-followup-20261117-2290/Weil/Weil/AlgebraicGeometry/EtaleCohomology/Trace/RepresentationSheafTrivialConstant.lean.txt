module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.RepresentationLAdicSheafLevels
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.ConstantSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafRestrictionIsogeny
public import Weil.Attr

/-!
# The sheaf of the trivial representation is the constant ℓ-adic sheaf

Let `X` be a connected Noetherian quasi-separated scheme of a big étale site, `x̄` a geometric
point of `X` and `ℓ` a prime. The lisse ℓ-adic sheaf `ℱ_𝟏` of the trivial representation
`𝟏 : π₁(X, x̄) → GL₁(ℚ_ℓ)` (`Stacks.EtaleCohomology.LAdicSheaf.representationSheaf`) is
isomorphic to the constant ℓ-adic sheaf `(ℤ/ℓⁿ⁺¹)_X`
(`Stacks.EtaleCohomology.LAdicSheaf.constantSystem`). In particular the two sheaves have the same
Frobenius characteristic polynomials on `Hⁱ_c(X_k̄, - ⊗ ℚ_ℓ)`.

## Main definitions

* `Weil.LAdicSheaf.constantSystemToTrivialRepresentation`: the comparison morphism from the
  constant ℓ-adic sheaf to the ℓ-adic sheaf of the trivial `ℤ_ℓ`-representation.
* `Weil.LAdicSheaf.constantSystemIsoRepresentationSheafOne`: `(ℤ/ℓⁿ⁺¹)_X ≅ ℱ_𝟏`.

## Main results

* `Weil.LAdicSheaf.exists_constantSystem_isogeny_representationSheaf_one`: the two sheaves are
  isogenous, in the form consumed by
  `LAdicSheaf.charpoly_rationalGeometricCompactlySupportedFrobenius_eq_of_isogeny`.
* `Weil.LAdicSheaf.charpoly_rationalGeometricCompactlySupportedFrobenius_representationSheaf_one_eq`
  (`ℱ_𝟏` against `(ℤ/ℓⁿ⁺¹)_X`): their Frobenius characteristic polynomials on compactly
  supported cohomology agree in every degree.
* `Weil.isIso_of_isFreeOnSection`: a morphism from a sheaf free on a global section to a sheaf
  isomorphic to a constant sheaf of rank one is an isomorphism when it sends the section to a
  generator.

## Implementation notes

The integral model of the trivial representation is trivial (`Weil.integralModel_one_etaleFundamentalGroup`), so `ℱ_𝟏`
is the ℓ-adic sheaf of the trivial `ℤ_ℓ`-representation, whose level `n` is the finite locally
constant sheaf attached by Tag 0DV5 (2) to `(ℤ/ℓⁿ⁺¹)¹` with the trivial action, and whose
transition maps are the images of reduction. The level `n` of the constant ℓ-adic sheaf is the
extension by zero `j_{X!}(ℤ/ℓⁿ⁺¹)` from the final object, which is free on its generator, so a
morphism out of it is a global section.

The comparison is the morphism whose value on the generator is the *unit section*: the global
section corresponding to `(1)` under the identification of global sections with invariants of
Tag 0DV5 (2) (`Weil.canonicalSectionsToFibre`). This identification is natural in the module, so
the unit sections are compatible with reduction, which gives the compatibility with the
transition maps. That every level is an isomorphism is proved through Tag 0DV5 (3): the level
sheaf is isomorphic to the constant sheaf of the trivial action
(`AlgebraicGeometry.constantIsoTrivialRepresentationSheafSmall`), its global sections are free
of rank one, and the unit section is a generator of them because `ℓⁿ` does not kill it.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter IV, §4.
* [Stacks Project, Tag 0DV5](https://stacks.math.columbia.edu/tag/0DV5)
* [Stacks Project, Tag 03UM](https://stacks.math.columbia.edu/tag/03UM)
-/

/- FK states the lemma for a connected scheme of finite type
over the finite field and for any ℓ-adic sheaf of the trivial representation; here `X` is a
connected Noetherian quasi-separated scheme of a big étale site and the sheaf is StacksFrontier's
canonical `LAdicSheaf.representationSheaf` (ℓ-adic sheaves as strict systems, following the
Stacks project convention). -/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry Stacks.EtaleCohomology Stacks.GroupCohomology
  Stacks.ConstantSheaf

universe v u' w u

attribute [local instance] discreteForget₂AddCommGrpCat

open scoped Stacks.DiscreteModuleTopology

namespace Weil

section Generic
variable {C : Type u'} [Category.{v} C] (J : GrothendieckTopology C) {T : C}
  (hT : Limits.IsTerminal T)
  (R : Type) [CommRing R] [HasWeakSheafify J (ModuleCat.{w} R)]

/-- **A sheaf of modules free on a global section**: a sheaf `G` with a section `g` over the
terminal object such that morphisms out of `G` are determined by, and exist for every value on,
their value on `g`. -/
structure IsFreeOnSection (G : Sheaf J (ModuleCat.{w} R)) (g : (G.obj.obj (op T) : Type w)) :
    Prop where
  ext : ∀ {H : Sheaf J (ModuleCat.{w} R)} (f₁ f₂ : G ⟶ H),
    ConcreteCategory.hom (f₁.hom.app (op T)) g = ConcreteCategory.hom (f₂.hom.app (op T)) g →
      f₁ = f₂
  exists_eq : ∀ {H : Sheaf J (ModuleCat.{w} R)} (s : (H.obj.obj (op T) : Type w)),
    ∃ f : G ⟶ H, ConcreteCategory.hom (f.hom.app (op T)) g = s

variable {J R}

/-- **A morphism out of a sheaf free on a section into a sheaf isomorphic to a constant sheaf of
rank one is an isomorphism when it sends the section to a generator.** Here `G` is free on its
section `g` over the terminal object, `P` is free of rank one on `p`, `f : P_X ⟶ F` is an
isomorphism, and `φ : G ⟶ F` sends `g` to the image of the constant section `p`. -/
theorem isIso_of_isFreeOnSection {G : Sheaf J (ModuleCat.{w} R)} {g : (G.obj.obj (op T) : Type w)}
    (hG : IsFreeOnSection J R G g) {P : ModuleCat.{w} R} (p : P)
    (hp : Function.Bijective fun r : R => r • p) {F : Sheaf J (ModuleCat.{w} R)}
    (f : (constantSheaf J (ModuleCat.{w} R)).obj P ⟶ F) [IsIso f] (φ : G ⟶ F)
    (hφ : ConcreteCategory.hom (φ.hom.app (op T)) g = ConcreteCategory.hom (f.hom.app (op T))
      (ConcreteCategory.hom ((constantSheafAdj J (ModuleCat.{w} R) hT).unit.app P) p)) :
    IsIso φ := by
  set adj := constantSheafAdj J (ModuleCat.{w} R) hT
  let e : R ≃ₗ[R] P := LinearEquiv.ofBijective (LinearMap.toSpanSingleton R P p) hp
  obtain ⟨c₁, hc₁⟩ := hG.exists_eq (H := (constantSheaf J (ModuleCat.{w} R)).obj P)
    (ConcreteCategory.hom (adj.unit.app P) p)
  let E : P ⟶ (sheafSections J (ModuleCat.{w} R)).obj (op T) |>.obj G :=
    ModuleCat.ofHom ((LinearMap.toSpanSingleton R _ g).comp e.symm.toLinearMap)
  let c₂ : (constantSheaf J (ModuleCat.{w} R)).obj P ⟶ G := (adj.homEquiv _ _).symm E
  have hc₂ : ∀ q : P, ConcreteCategory.hom (c₂.hom.app (op T))
      (ConcreteCategory.hom (adj.unit.app P) q) = e.symm q • g := by
    intro q
    have h := adj.homEquiv_unit _ _ c₂
    rw [Equiv.apply_symm_apply] at h
    exact (ConcreteCategory.congr_hom h q).symm
  have h12 : c₁ ≫ c₂ = 𝟙 G := by
    apply hG.ext
    change ConcreteCategory.hom (c₂.hom.app (op T)) (ConcreteCategory.hom (c₁.hom.app (op T)) g) = g
    rw [hc₁, hc₂]
    have : e.symm p = 1 := by
      apply e.injective
      rw [e.apply_symm_apply]
      exact (one_smul R p).symm
    rw [this, one_smul]
  have h21 : c₂ ≫ c₁ = 𝟙 _ := by
    apply (adj.homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    ext q
    change ConcreteCategory.hom (c₁.hom.app (op T)) (ConcreteCategory.hom (c₂.hom.app (op T))
      (ConcreteCategory.hom (adj.unit.app P) q)) = ConcreteCategory.hom (adj.unit.app P) q
    rw [hc₂, map_smul, hc₁, ← map_smul]
    congr 1
    exact e.apply_symm_apply q
  have hφ' : φ = c₁ ≫ f := by
    apply hG.ext
    change _ = ConcreteCategory.hom (f.hom.app (op T)) (ConcreteCategory.hom (c₁.hom.app (op T)) g)
    rw [hc₁, hφ]
  have : IsIso c₁ := ⟨⟨c₂, h12, h21⟩⟩
  rw [hφ']
  infer_instance

end Generic

/-- An isomorphism onto the sections of a sheaf followed by the sections of an isomorphism of
sheaves is bijective. -/
theorem bijective_comp_app_of_isIso {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Type} [Ring R] {P : ModuleCat.{w} R} {F G : Sheaf J (ModuleCat.{w} R)} (U : Cᵒᵖ)
    (σ : P ⟶ F.obj.obj U) [IsIso σ] (b : F ⟶ G) [IsIso b] :
    Function.Bijective (ConcreteCategory.hom (σ ≫ b.hom.app U)) := by
  have h1 := ConcreteCategory.bijective_of_isIso σ
  have h2 :=
    ConcreteCategory.bijective_of_isIso (((sheafToPresheaf J _).mapIso (asIso b)).app U).hom
  exact h2.comp h1

/-- Sections of a composite of morphisms of sheaves of modules. -/
theorem sheaf_comp_app_apply {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Type} [Ring R] {F G H : Sheaf J (ModuleCat.{w} R)} (f : F ⟶ G) (g : G ⟶ H) (U : Cᵒᵖ)
    (s : F.obj.obj U) :
    ConcreteCategory.hom ((f ≫ g).hom.app U) s =
      ConcreteCategory.hom (g.hom.app U) (ConcreteCategory.hom (f.hom.app U) s) := rfl

/-- The value of `a ≫ b` on the constant section `p` of `P_X`, where `a` is the adjoint transpose
of `σ : P ⟶ Γ(H)`, is `b(σ p)`. -/
theorem comp_app_constantSheafAdj_unit_apply {C : Type u'} [Category.{v} C]
    {J : GrothendieckTopology C} {T : C}
    (hT : Limits.IsTerminal T) {R : Type} [CommRing R] [HasWeakSheafify J (ModuleCat.{w} R)]
    {P : ModuleCat.{w} R} {H F : Sheaf J (ModuleCat.{w} R)}
    (a : (constantSheaf J (ModuleCat.{w} R)).obj P ⟶ H) (b : H ⟶ F) (σ : P ⟶ H.obj.obj (op T))
    (hσ : (constantSheafAdj J (ModuleCat.{w} R) hT).homEquiv _ _ a = σ) (p : P) :
    ConcreteCategory.hom ((a ≫ b).hom.app (op T))
        (ConcreteCategory.hom ((constantSheafAdj J (ModuleCat.{w} R) hT).unit.app P) p) =
      ConcreteCategory.hom (b.hom.app (op T)) (ConcreteCategory.hom σ p) := by
  rw [← hσ, Adjunction.homEquiv_unit]
  rfl

/-- An element of `ℤ/ℓⁿ⁺¹` not killed by `ℓⁿ` is a unit. -/
theorem isUnit_of_pow_nsmul_ne_zero {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {n : ℕ} (c : ZMod (ℓ ^ (n + 1)))
    (h : (ℓ ^ n : ℕ) • c ≠ 0) : IsUnit c := by
  have hne : NeZero (ℓ ^ (n + 1)) := ⟨pow_ne_zero _ hℓ.out.ne_zero⟩
  by_contra hc
  apply h
  rw [← ZMod.natCast_zmod_val c, ZMod.isUnit_iff_coprime,
    Nat.coprime_pow_right_iff (Nat.succ_pos n),
    Nat.Coprime, ← Nat.Coprime, Nat.coprime_comm, hℓ.out.coprime_iff_not_dvd, not_not] at hc
  obtain ⟨d, hd⟩ := hc
  rw [← ZMod.natCast_zmod_val c, hd, nsmul_eq_mul, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff,
    ← mul_assoc, ← pow_succ]
  exact dvd_mul_right _ _

/-- `ℓⁿ ≠ 0` in `ℤ/ℓⁿ⁺¹`. -/
theorem pow_nsmul_one_ne_zero {ℓ : ℕ} [hℓ : Fact ℓ.Prime] (n : ℕ) :
    (ℓ ^ n : ℕ) • (1 : ZMod (ℓ ^ (n + 1))) ≠ 0 := by
  rw [nsmul_eq_mul, mul_one, Ne, ZMod.natCast_eq_zero_iff]
  intro h
  have := Nat.le_of_dvd (pow_pos hℓ.out.pos n) h
  have h2 : ℓ ^ n < ℓ ^ (n + 1) := Nat.pow_lt_pow_right hℓ.out.one_lt (Nat.lt_succ_self n)
  omega

/-- A vector of `(ℤ/ℓⁿ⁺¹)¹` not killed by `ℓⁿ` is a basis vector. -/
theorem bijective_smul_of_pow_nsmul_ne_zero {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ}
    (v : ULift.{w} (Fin 1 → ZMod (ℓ ^ (n + 1)))) (h : (ℓ ^ n : ℕ) • v ≠ 0) :
    Function.Bijective fun r : ZMod (ℓ ^ (n + 1)) => r • v := by
  have hc : (ℓ ^ n : ℕ) • v.down 0 ≠ 0 := fun h0 => h (ULift.ext _ _ (funext fun i => by
    rw [Subsingleton.elim i 0]; exact h0))
  have hu := isUnit_of_pow_nsmul_ne_zero _ hc
  refine ⟨fun r r' hr => ?_, fun y => ⟨y.down 0 * ↑hu.unit⁻¹, ULift.ext _ _ (funext fun i => ?_)⟩⟩
  · have := congrArg (fun z : ULift.{w} (Fin 1 → ZMod (ℓ ^ (n + 1))) => z.down 0) hr
    exact hu.mul_left_injective this
  · rw [Subsingleton.elim i 0]
    change y.down 0 * ↑hu.unit⁻¹ * v.down 0 = y.down 0
    rw [mul_assoc, IsUnit.val_inv_mul, mul_one]

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)

/-- On elements, the inverse of an isomorphism of finite discrete `G`-modules undoes it. -/
theorem finiteContinuousAbelian_iso_inv_hom_apply {G : Type (u + 1)} [Group G] [TopologicalSpace G]
    {P Q : (ContinuousGAddCommGrp.isFinite.{u + 1, u + 1} G).FullSubcategory} (i : P ≅ Q)
    (y : P.obj.obj.obj.V) : i.inv.hom.hom.hom.hom (i.hom.hom.hom.hom.hom y) = y := by
  have := congrArg (fun f : P ⟶ P => ConcreteCategory.hom f.hom.hom.hom.hom y) i.hom_inv_id
  exact this

/-- On elements, an isomorphism of finite discrete `G`-modules undoes its inverse. -/
theorem finiteContinuousAbelian_iso_hom_inv_apply {G : Type (u + 1)} [Group G] [TopologicalSpace G]
    {P Q : (ContinuousGAddCommGrp.isFinite.{u + 1, u + 1} G).FullSubcategory} (i : P ≅ Q)
    (y : Q.obj.obj.obj.V) : i.hom.hom.hom.hom.hom (i.inv.hom.hom.hom.hom y) = y :=
  finiteContinuousAbelian_iso_inv_hom_apply i.symm y

/-- **Global sections of `e⁻¹(A)` as elements of `A`**, for the canonical equivalence `e` of
Tag 0DV5 (2): a global section of the finite locally constant abelian sheaf attached to a
finite discrete `π₁(X, x̄)`-module `A` is an invariant of the module attached back to that sheaf,
read in `A` through the counit of `e`. -/
def canonicalSectionsToFibre
    (A : (ContinuousGAddCommGrp.isFinite.{u + 1, u + 1}
      (EtaleFundamentalGroup X.1 x)).FullSubcategory)
    (s : ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse.obj A).obj.obj.obj
      (op (SmallEtale.final B X.1 X.2))) : A.obj.obj.obj.V :=
  ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).counitIso.hom.app
    A).hom.hom.hom.hom
    ((finiteLocallyConstantAbelianSectionsIsoInvariants (SmallEtale.topology B X.1 X.2)
      (SmallEtale.finalIsTerminal B X.1 X.2) (EtaleFundamentalGroup X.1 x)
      (canonicalFiniteLocallyConstantSetsEquivalence B X x)).inv.app
        ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse.obj A) s).1

/-- `Weil.canonicalSectionsToFibre` is natural in the module. -/
theorem canonicalSectionsToFibre_naturality
    {A A' : (ContinuousGAddCommGrp.isFinite.{u + 1, u + 1}
      (EtaleFundamentalGroup X.1 x)).FullSubcategory}
    (g : A ⟶ A') (s) :
    canonicalSectionsToFibre B X x A'
      (((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse.map g).hom.hom.app
        (op (SmallEtale.final B X.1 X.2)) s) =
      g.hom.hom.hom.hom (canonicalSectionsToFibre B X x A s) := by
  have h1 := ConcreteCategory.congr_hom ((finiteLocallyConstantAbelianSectionsIsoInvariants
      (SmallEtale.topology B X.1 X.2)
      (SmallEtale.finalIsTerminal B X.1 X.2) (EtaleFundamentalGroup X.1 x)
      (canonicalFiniteLocallyConstantSetsEquivalence B X x)).inv.naturality
        ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse.map g)) s
  have h2 :=
    (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).counitIso.hom.naturality g
  unfold canonicalSectionsToFibre
  erw [h1]
  exact ConcreteCategory.congr_hom (congrArg (fun f => f.hom.hom.hom.hom) h2) _

/-- `Weil.canonicalSectionsToFibre` is injective. -/
theorem canonicalSectionsToFibre_injective
    (A : (ContinuousGAddCommGrp.isFinite.{u + 1, u + 1}
      (EtaleFundamentalGroup X.1 x)).FullSubcategory) :
    Function.Injective (canonicalSectionsToFibre B X x A) := by
  intro s t h
  unfold canonicalSectionsToFibre at h
  have key := finiteContinuousAbelian_iso_inv_hom_apply
    ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).counitIso.app A)
  have h1 := (Function.LeftInverse.injective key) h
  have h2 := Subtype.ext_iff.2 h1
  exact (ConcreteCategory.bijective_of_isIso ((finiteLocallyConstantAbelianSectionsIsoInvariants
      (SmallEtale.topology B X.1 X.2)
      (SmallEtale.finalIsTerminal B X.1 X.2) (EtaleFundamentalGroup X.1 x)
      (canonicalFiniteLocallyConstantSetsEquivalence B X x)).inv.app
        ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse.obj A))).1 h2

/-- Every invariant of `A` is the image of a global section. -/
theorem exists_canonicalSectionsToFibre_eq
    (A : (ContinuousGAddCommGrp.isFinite.{u + 1, u + 1}
      (EtaleFundamentalGroup X.1 x)).FullSubcategory)
    (a : A.obj.obj.obj.V) (ha : ∀ g, ConcreteCategory.hom (A.obj.obj.obj.ρ g) a = a) :
    ∃ s, canonicalSectionsToFibre B X x A s = a := by
  set c := (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).counitIso.app A
  set σ := (finiteLocallyConstantAbelianSectionsIsoInvariants (SmallEtale.topology B X.1 X.2)
      (SmallEtale.finalIsTerminal B X.1 X.2) (EtaleFundamentalGroup X.1 x)
      (canonicalFiniteLocallyConstantSetsEquivalence B X x)).app
        ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse.obj A)
  have hy : ∀ g, ConcreteCategory.hom
      (((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).functor.obj
        ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse.obj
          A)).obj.obj.obj.ρ g)
      (c.inv.hom.hom.hom.hom a) = c.inv.hom.hom.hom.hom a := fun g => by
    have := ConcreteCategory.congr_hom (c.inv.hom.hom.hom.comm g) a
    exact this.symm.trans (congrArg (ConcreteCategory.hom c.inv.hom.hom.hom.hom) (ha g))
  refine ⟨σ.hom ⟨c.inv.hom.hom.hom.hom a, hy⟩, ?_⟩
  unfold canonicalSectionsToFibre
  have h := σ.hom_inv_id
  rw [show (ConcreteCategory.hom ((finiteLocallyConstantAbelianSectionsIsoInvariants
      (SmallEtale.topology B X.1 X.2)
      (SmallEtale.finalIsTerminal B X.1 X.2) (EtaleFundamentalGroup X.1 x)
      (canonicalFiniteLocallyConstantSetsEquivalence B X x)).inv.app
        ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse.obj A)))
      (σ.hom ⟨c.inv.hom.hom.hom.hom a, hy⟩) = ⟨c.inv.hom.hom.hom.hom a, hy⟩ from
    σ.hom_inv_id_apply _]
  exact finiteContinuousAbelian_iso_hom_inv_apply c a


/-- `Weil.canonicalSectionsToFibre` is additive. -/
theorem canonicalSectionsToFibre_nsmul
    (A : (ContinuousGAddCommGrp.isFinite.{u + 1, u + 1}
      (EtaleFundamentalGroup X.1 x)).FullSubcategory)
    (k : ℕ) (s) :
    canonicalSectionsToFibre B X x A (k • s) = k • canonicalSectionsToFibre B X x A s := by
  unfold canonicalSectionsToFibre
  rw [map_nsmul]
  exact map_nsmul _ _ _

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- The trivial representation acts trivially on its level modules. -/
theorem levelAbelian_one_rho_apply (k : ℕ) (g : EtaleFundamentalGroup X.1 x) (y) :
    ConcreteCategory.hom ((levelAbelian (1 : EtaleFundamentalGroup X.1 x →* GL (Fin 1) ℤ_[ℓ])
      continuous_const k).obj.obj.obj.ρ g) y = y := by
  refine ULift.ext _ _ ?_
  change levelRepresentation (1 : EtaleFundamentalGroup X.1 x →* GL (Fin 1) ℤ_[ℓ]) k g y.down =
    y.down
  rw [levelRepresentation_apply]
  simp

/-- **The unit section** of the `k`-th level sheaf of the trivial rank-one representation: the
global section corresponding to the vector `(1)` of `(ℤ/ℓᵏ)¹`. -/
def trivialRepresentationUnitSection (k : ℕ) :
    ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse.obj
      (levelAbelian (1 : EtaleFundamentalGroup X.1 x →* GL (Fin 1) ℤ_[ℓ])
        continuous_const k)).obj.obj.obj
      (op (SmallEtale.final B X.1 X.2)) :=
  (exists_canonicalSectionsToFibre_eq B X x _ (ULift.up fun _ => 1)
    (fun g => levelAbelian_one_rho_apply B X x k g _)).choose


/-- The unit section corresponds to the vector `(1)`. -/
theorem canonicalSectionsToFibre_trivialRepresentationUnitSection (k : ℕ) :
    canonicalSectionsToFibre B X x
      (levelAbelian (1 : EtaleFundamentalGroup X.1 x →* GL (Fin 1) ℤ_[ℓ]) continuous_const k)
      (trivialRepresentationUnitSection B X x k) = ULift.up fun _ => 1 :=
  (exists_canonicalSectionsToFibre_eq B X x
    (levelAbelian (1 : EtaleFundamentalGroup X.1 x →* GL (Fin 1) ℤ_[ℓ]) continuous_const k)
    (ULift.up fun _ => 1)
    (fun g => levelAbelian_one_rho_apply B X x k g _)).choose_spec

/-- **The transition maps of the sheaf of the trivial representation preserve the unit
sections.** -/
theorem representationLevelTransition_trivialRepresentationUnitSection (n : ℕ) :
    ConcreteCategory.hom ((representationLevelTransition B X x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
      (1 : EtaleFundamentalGroup X.1 x →* GL (Fin 1) ℤ_[ℓ]) continuous_const (n + 1)).hom.app
        (op (SmallEtale.final B X.1 X.2))) (trivialRepresentationUnitSection B X x (n + 1 + 1)) =
      trivialRepresentationUnitSection B X x (n + 1) := by
  apply canonicalSectionsToFibre_injective B X x
    (levelAbelian (1 : EtaleFundamentalGroup X.1 x →* GL (Fin 1) ℤ_[ℓ]) continuous_const (n + 1))
  change canonicalSectionsToFibre B X x
    (levelAbelian (1 : EtaleFundamentalGroup X.1 x →* GL (Fin 1) ℤ_[ℓ]) continuous_const (n + 1))
    ((((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x).inverse.map
    (levelAbelianReduction (1 : EtaleFundamentalGroup X.1 x →* GL (Fin 1) ℤ_[ℓ]) continuous_const
      (n + 1))).hom.hom.app _ (trivialRepresentationUnitSection B X x (n + 1 + 1)))) = _
  rw [canonicalSectionsToFibre_naturality,
    canonicalSectionsToFibre_trivialRepresentationUnitSection,
    canonicalSectionsToFibre_trivialRepresentationUnitSection]
  refine ULift.ext _ _ (funext fun _ => ?_)
  change levelRingHom (ℓ := ℓ) (n + 1) 1 = 1
  exact map_one _


section Module

variable (k : ℕ) [NeZero (ℓ ^ k)]

/-- The level module `(ℤ/ℓᵏ)¹` of the trivial representation, as a finite module. -/
abbrev trivialLevelModule :
    ObjectProperty.FullSubcategory (ModuleCat.isFG.{u + 1} (ZMod (ℓ ^ k))) :=
  ⟨(levelModule.{u + 1, u + 1} (1 : EtaleFundamentalGroup X.1 x →* GL (Fin 1) ℤ_[ℓ])
    continuous_const k).obj.obj.obj.V,
    (levelModule.{u + 1, u + 1} (1 : EtaleFundamentalGroup X.1 x →* GL (Fin 1) ℤ_[ℓ])
    continuous_const k).property⟩

/-- The level module of the trivial representation is the module with the trivial action. -/
def trivialLevelModuleHom :
    (finiteTypeContinuousModuleTrivial (ZMod (ℓ ^ k)) (EtaleFundamentalGroup X.1 x)).obj
        (trivialLevelModule B X x k) ⟶
      levelModule.{u + 1, u + 1} (1 : EtaleFundamentalGroup X.1 x →* GL (Fin 1) ℤ_[ℓ])
        continuous_const k :=
  ObjectProperty.homMk (ObjectProperty.homMk (ObjectProperty.homMk
    { hom := 𝟙 _
      comm := fun g => by
        ext y
        refine ULift.ext _ _ ?_
        change y.down =
          levelRepresentation (1 : EtaleFundamentalGroup X.1 x →* GL (Fin 1) ℤ_[ℓ]) k g y.down
        rw [levelRepresentation_apply]
        simp }))

instance isIso_trivialLevelModuleHom : IsIso (trivialLevelModuleHom (ℓ := ℓ) B X x k) :=
  isIso_of_bijective _ _ _ Function.bijective_id

/-- The comparison of the sheaf of the trivial action with the level sheaf of the trivial
representation, the image of `Weil.trivialLevelModuleHom` under Tag 0DV5 (3). -/
def trivialLevelSheafHom :
    (trivialRepresentationSheafSmall B X x (ZMod (ℓ ^ k))).obj (trivialLevelModule B X x k) ⟶
      representationLevelSheaf B X x (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
        (1 : EtaleFundamentalGroup X.1 x →* GL (Fin 1) ℤ_[ℓ]) continuous_const k :=
  (ObjectProperty.ι _).map
    ((finiteTypeLocallyConstantModuleSheafEquivalence B X x (ZMod (ℓ ^ k))).inverse.map
      (trivialLevelModuleHom B X x k))

instance : IsIso (trivialLevelSheafHom (ℓ := ℓ) B X x k) :=
  Functor.map_isIso (ObjectProperty.ι _) _

/-- Global sections of the `k`-th level sheaf of the trivial representation are the level
module. -/
theorem bijective_trivialLevelSections :
    Function.Bijective (ConcreteCategory.hom
      ((trivialRepresentationSheafSmallSectionsIso B X x (ZMod (ℓ ^ k))).inv.app
        (trivialLevelModule B X x k) ≫
      (trivialLevelSheafHom (ℓ := ℓ) B X x k).hom.app (op (SmallEtale.final B X.1 X.2)))) :=
  bijective_comp_app_of_isIso _ _ _

attribute [local instance] AlgebraicGeometry.hasSheafify_smallEtale_moduleCat

instance : IsIso ((constantToTrivialRepresentationSheafSmall B X x (ZMod (ℓ ^ k))).app
    (trivialLevelModule B X x k) ≫ trivialLevelSheafHom (ℓ := ℓ) B X x k) := by
  have :=
    isIso_constantToTrivialRepresentationSheafSmall B X x (ZMod (ℓ ^ k))
      (trivialLevelModule B X x k)
  exact IsIso.comp_isIso

/-- The comparison of the constant sheaf with the level sheaf sends the constant section `p` to
the global section attached to `p`. -/
theorem constantToTrivialLevelSheaf_unit (p : (trivialLevelModule B X x k).obj) :
    ConcreteCategory.hom (((constantToTrivialRepresentationSheafSmall B X x (ZMod (ℓ ^ k))).app
        (trivialLevelModule B X x k) ≫ trivialLevelSheafHom (ℓ := ℓ) B X x k).hom.app
          (op (SmallEtale.final B X.1 X.2)))
      (ConcreteCategory.hom ((constantSheafAdj (SmallEtale.topology B X.1 X.2)
        (ModuleCat.{u + 1} (ZMod (ℓ ^ k))) (SmallEtale.finalIsTerminal B X.1 X.2)).unit.app
          (trivialLevelModule B X x k).obj) p) =
      ConcreteCategory.hom
      ((trivialRepresentationSheafSmallSectionsIso B X x (ZMod (ℓ ^ k))).inv.app
        (trivialLevelModule B X x k) ≫
      (trivialLevelSheafHom (ℓ := ℓ) B X x k).hom.app (op (SmallEtale.final B X.1 X.2))) p :=
  (comp_app_constantSheafAdj_unit_apply (SmallEtale.finalIsTerminal B X.1 X.2) _ _ _
    (Equiv.apply_symm_apply _ _) p).trans
    (ConcreteCategory.comp_apply _ _ _).symm

end Module

omit [ConnectedSpace X.1] in
/-- The constant free rank-one sheaf `j_{X!}R_X` of Stacks 021B is free on its generator. -/
theorem isFreeOnSection_moduleShriekConstant_final (R : Type) [CommRing R] :
    IsFreeOnSection (T := SmallEtale.final B X.1 X.2) (SmallEtale.topology B X.1 X.2) R
      (moduleShriekConstant.{u, 0, 0} B X R (SmallEtale.final B X.1 X.2))
      (moduleShriekConstantGenerator B X R (SmallEtale.final B X.1 X.2)) where
  ext f₁ f₂ h := by
    apply (moduleShriekConstantSectionEquiv.{u, 0, 0} B X R _ _).injective
    rw [moduleShriekConstantSectionEquiv_apply, moduleShriekConstantSectionEquiv_apply]
    exact h
  exists_eq s := ⟨(moduleShriekConstantSectionEquiv.{u, 0, 0} B X R _ _).symm s, by
    rw [← moduleShriekConstantSectionEquiv_apply]
    exact Equiv.apply_symm_apply _ _⟩

/-- `Weil.canonicalSectionsToFibre` preserves zero. -/
theorem canonicalSectionsToFibre_zero
    (A : (ContinuousGAddCommGrp.isFinite.{u + 1, u + 1}
      (EtaleFundamentalGroup X.1 x)).FullSubcategory) :
    canonicalSectionsToFibre B X x A 0 = 0 := by
  simpa using canonicalSectionsToFibre_nsmul B X x A 0 0

attribute [local instance] Stacks.EtaleCohomology.neZero_pow_of_fact_prime

section Level

variable (n : ℕ)

/-- Surjectivity of the identification of the level module with the global sections. -/
theorem surjective_trivialLevelSectionsMap :
    Function.Surjective (ConcreteCategory.hom
      ((trivialRepresentationSheafSmallSectionsIso B X x (ZMod (ℓ ^ (n + 1)))).inv.app
        (trivialLevelModule B X x (n + 1)) ≫
      (trivialLevelSheafHom (ℓ := ℓ) B X x (n + 1)).hom.app (op (SmallEtale.final B X.1 X.2)))) :=
  (bijective_trivialLevelSections B X x (n + 1)).2

/-- The vector of the level module corresponding to the unit section. -/
def trivialLevelGenerator : (trivialLevelModule B X x (ℓ := ℓ) (n + 1)).obj :=
  Function.surjInv (surjective_trivialLevelSectionsMap B X x n)
    (trivialRepresentationUnitSection B X x (n + 1))

set_option maxRecDepth 100000 in
/-- The vector `Weil.trivialLevelGenerator` corresponds to the unit section. -/
theorem trivialLevelSectionsMap_trivialLevelGenerator :
    ConcreteCategory.hom
      ((trivialRepresentationSheafSmallSectionsIso B X x (ZMod (ℓ ^ (n + 1)))).inv.app
        (trivialLevelModule B X x (n + 1)) ≫
      (trivialLevelSheafHom (ℓ := ℓ) B X x (n + 1)).hom.app (op (SmallEtale.final B X.1 X.2)))
        (trivialLevelGenerator (ℓ := ℓ) B X x n) =
      trivialRepresentationUnitSection B X x (n + 1) :=
  Function.surjInv_eq _ _

set_option maxRecDepth 100000 in
/-- The vector `Weil.trivialLevelGenerator` is not killed by `ℓⁿ`. -/
theorem nsmul_trivialLevelGenerator_ne_zero :
    (ℓ ^ n : ℕ) • trivialLevelGenerator (ℓ := ℓ) B X x n ≠ 0 := by
  intro h
  have h1 := congrArg (ConcreteCategory.hom
    ((trivialRepresentationSheafSmallSectionsIso B X x (ZMod (ℓ ^ (n + 1)))).inv.app
        (trivialLevelModule B X x (n + 1)) ≫
      (trivialLevelSheafHom (ℓ := ℓ) B X x (n + 1)).hom.app (op (SmallEtale.final B X.1 X.2)))) h
  rw [map_nsmul, map_zero, trivialLevelSectionsMap_trivialLevelGenerator] at h1
  have h2 := congrArg (canonicalSectionsToFibre B X x
    (levelAbelian (1 : EtaleFundamentalGroup X.1 x →* GL (Fin 1) ℤ_[ℓ]) continuous_const
      (n + 1))) h1
  have h3 := (canonicalSectionsToFibre_nsmul B X x _ (ℓ ^ n)
    (trivialRepresentationUnitSection B X x (n + 1))).symm.trans h2
  rw [canonicalSectionsToFibre_trivialRepresentationUnitSection] at h3
  have h4 := h3.trans (canonicalSectionsToFibre_zero B X x _)
  exact pow_nsmul_one_ne_zero n (congrArg (fun y => (ULift.down y) 0) h4)

end Level

/-- The integral model of the trivial representation is trivial. -/
theorem integralModel_one_etaleFundamentalGroup :
    haveI := compactSpace_etaleFundamentalGroup X.1 x
    integralModel (1 : EtaleFundamentalGroup X.1 x →* GL (Fin 1) ℚ_[ℓ]) continuous_const = 1 := by
  have := compactSpace_etaleFundamentalGroup X.1 x
  ext g i j
  have h := congrArg (fun A : GL (Fin 1) ℚ_[ℓ] => A.val i j)
    (map_integralModel (1 : EtaleFundamentalGroup X.1 x →* GL (Fin 1) ℚ_[ℓ]) continuous_const g)
  simp only [MonoidHom.one_apply, mul_one, inv_mul_cancel] at h
  apply Subtype.coe_injective
  refine h.trans ?_
  rw [MonoidHom.one_apply, Units.val_one, Units.val_one, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

section LAdic

open AlgebraicGeometry.SmallEtale

variable [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1]

omit [ConnectedSpace X.1] in
/-- **A morphism of ℓ-adic sheaves which is an isomorphism at every level is an isomorphism.** -/
theorem LAdicSheaf.isIso_of_isIso_app {F G : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G)
    [hf : ∀ n, IsIso (f.app n)] : IsIso f := by
  let g : G ⟶ F :=
    { app := fun n => inv (f.app n)
      naturality := fun n => by
        rw [← cancel_epi (f.app (n + 1)), IsIso.hom_inv_id_assoc, ← Category.assoc,
          f.naturality n, Category.assoc, ← Functor.map_comp, IsIso.hom_inv_id,
          CategoryTheory.Functor.map_id,
          Category.comp_id] }
  refine ⟨g, ?_, ?_⟩
  · exact LAdicSheaf.Hom.ext _ _ _ fun n => IsIso.hom_inv_id (f.app n)
  · exact LAdicSheaf.Hom.ext _ _ _ fun n => IsIso.inv_hom_id (f.app n)

section Level

variable [QuasiSeparatedSpace X.1]

set_option maxRecDepth 100000 in
/-- The `n`-th level of the comparison: the morphism out of the constant sheaf
`(ℤ/ℓⁿ⁺¹)_X` whose value on the generator is the unit section. -/
def LAdicSheaf.constantSystemToTrivialRepresentationLevel (n : ℕ) :
    (LAdicSheaf.constantSystem B X ℓ).level n ⟶
      (representationLAdicSheaf B X x (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
        (1 : EtaleFundamentalGroup X.1 x →* GL (Fin 1) ℤ_[ℓ]) continuous_const).level n :=
  (moduleShriekConstantSectionEquiv.{u, 0, 0} B X (ZMod (ℓ ^ (n + 1))) _ _).symm
    (trivialRepresentationUnitSection B X x (n + 1))

set_option maxRecDepth 100000 in
/-- The `n`-th level of the comparison sends the generator to the unit section. -/
theorem LAdicSheaf.constantSystemToTrivialRepresentationLevel_generator (n : ℕ) :
    ConcreteCategory.hom ((LAdicSheaf.constantSystemToTrivialRepresentationLevel B X x n).hom.app
        (op (SmallEtale.final B X.1 X.2)))
      (moduleShriekConstantGenerator B X (ZMod (ℓ ^ (n + 1))) (SmallEtale.final B X.1 X.2)) =
      trivialRepresentationUnitSection B X x (n + 1) := by
  exact (moduleShriekConstantSectionEquiv_apply B X (ZMod (ℓ ^ (n + 1)))
    (SmallEtale.final B X.1 X.2) _
    (LAdicSheaf.constantSystemToTrivialRepresentationLevel B X x n)).symm.trans
      (Equiv.apply_symm_apply _ _)

set_option maxRecDepth 100000 in
/-- **Every level of the comparison is an isomorphism**: it sends the generator to a generator of
the global sections of a sheaf isomorphic to the constant sheaf (Tag 0DV5 (3) for the trivial
action). -/
theorem LAdicSheaf.isIso_constantSystemToTrivialRepresentationLevel (n : ℕ) :
    IsIso (LAdicSheaf.constantSystemToTrivialRepresentationLevel B X x (ℓ := ℓ) n) :=
  isIso_of_isFreeOnSection (SmallEtale.finalIsTerminal B X.1 X.2)
    (isFreeOnSection_moduleShriekConstant_final B X _) (trivialLevelGenerator B X x n)
    (bijective_smul_of_pow_nsmul_ne_zero _ (nsmul_trivialLevelGenerator_ne_zero B X x n))
    ((constantToTrivialRepresentationSheafSmall B X x (ZMod (ℓ ^ (n + 1)))).app
      (trivialLevelModule B X x (n + 1)) ≫ trivialLevelSheafHom (ℓ := ℓ) B X x (n + 1)) _
    ((LAdicSheaf.constantSystemToTrivialRepresentationLevel_generator B X x n).trans
      ((constantToTrivialLevelSheaf_unit B X x (n + 1) _).trans
        (trivialLevelSectionsMap_trivialLevelGenerator B X x n)).symm)

set_option maxRecDepth 100000 in
/-- **The levels of the comparison are compatible with the transition maps.** -/
theorem LAdicSheaf.constantSystemToTrivialRepresentationLevel_naturality (n : ℕ) :
    LAdicSheaf.constantSystemToTrivialRepresentationLevel B X x (ℓ := ℓ) (n + 1) ≫
        (representationLAdicSheaf B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
          (1 : EtaleFundamentalGroup X.1 x →* GL (Fin 1) ℤ_[ℓ]) continuous_const).transition n =
      (LAdicSheaf.constantSystem B X ℓ).transition n ≫
        (sheafCompose (SmallEtale.topology B X.obj X.property)
          (ModuleCat.restrictScalars.{u + 1, 0, 0} (finiteLevelRingHom ℓ n))).map
            (LAdicSheaf.constantSystemToTrivialRepresentationLevel B X x n) := by
  apply (isFreeOnSection_moduleShriekConstant_final B X (ZMod (ℓ ^ (n + 1 + 1)))).ext
  refine (sheaf_comp_app_apply _ _ _ _).trans ?_
  refine (congrArg _
    (LAdicSheaf.constantSystemToTrivialRepresentationLevel_generator B X x (n + 1))).trans ?_
  refine (representationLevelTransition_trivialRepresentationUnitSection B X x n).trans ?_
  refine Eq.trans ?_ (sheaf_comp_app_apply _ _ _ _).symm
  refine Eq.trans ?_ (congrArg (ConcreteCategory.hom
    (((sheafCompose (SmallEtale.topology B X.obj X.property)
          (ModuleCat.restrictScalars.{u + 1, 0, 0} (finiteLevelRingHom ℓ n))).map
            (LAdicSheaf.constantSystemToTrivialRepresentationLevel B X x n)).hom.app
              (op (SmallEtale.final B X.1 X.2))))
    (LAdicSheaf.shriekConstantTransition_generator B X ℓ (SmallEtale.final B X.1 X.2) n)).symm
  exact (LAdicSheaf.constantSystemToTrivialRepresentationLevel_generator B X x n).symm

/-- **The comparison** of the constant ℓ-adic sheaf with the ℓ-adic sheaf of the trivial rank-one
`ℤ_ℓ`-representation. -/
def LAdicSheaf.constantSystemToTrivialRepresentation :
    LAdicSheaf.constantSystem B X ℓ ⟶
      representationLAdicSheaf B X x (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
        (1 : EtaleFundamentalGroup X.1 x →* GL (Fin 1) ℤ_[ℓ]) continuous_const where
  app n := LAdicSheaf.constantSystemToTrivialRepresentationLevel B X x n
  naturality n := LAdicSheaf.constantSystemToTrivialRepresentationLevel_naturality B X x n

instance : IsIso (LAdicSheaf.constantSystemToTrivialRepresentation (ℓ := ℓ) B X x) := by
  exact LAdicSheaf.isIso_of_isIso_app B X _
    (hf := fun n => LAdicSheaf.isIso_constantSystemToTrivialRepresentationLevel (ℓ := ℓ) B X x n)

omit [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] [QuasiSeparatedSpace X.1] in
/-- `ℱ_𝟏` is the ℓ-adic sheaf of the trivial `ℤ_ℓ`-representation. -/
theorem LAdicSheaf.representationSheaf_one_eq :
    LAdicSheaf.representationSheaf B X x (1 : EtaleFundamentalGroup X.1 x →* GL (Fin 1) ℚ_[ℓ])
        continuous_const =
      representationLAdicSheaf B X x (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
        (1 : EtaleFundamentalGroup X.1 x →* GL (Fin 1) ℤ_[ℓ]) continuous_const := by
  have key : ∀ (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin 1) ℤ_[ℓ]) (hρ : Continuous ρ), ρ = 1 →
      representationLAdicSheaf B X x (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
        ρ hρ =
      representationLAdicSheaf B X x (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
        (1 : EtaleFundamentalGroup X.1 x →* GL (Fin 1) ℤ_[ℓ]) continuous_const := by
    rintro _ _ rfl
    rfl
  rw [LAdicSheaf.representationSheaf_eq_representationLAdicSheaf]
  exact key _ _ (integralModel_one_etaleFundamentalGroup B X x)

/-- **The sheaf of the trivial representation is the constant ℓ-adic sheaf.** For a connected
Noetherian quasi-separated scheme `X` of a big étale site and a geometric point `x̄`, the lisse
ℓ-adic sheaf `ℱ_𝟏` of the trivial representation `𝟏 : π₁(X, x̄) → GL₁(ℚ_ℓ)` is isomorphic, as
an inverse system of étale sheaves, to the constant ℓ-adic sheaf `(ℤ/ℓⁿ⁺¹)_X`. -/
@[weil "lem_fk404_trivial_representation_sheaf_iso_constant"]
def LAdicSheaf.constantSystemIsoRepresentationSheafOne :
    LAdicSheaf.constantSystem B X ℓ ≅
      LAdicSheaf.representationSheaf B X x (1 : EtaleFundamentalGroup X.1 x →* GL (Fin 1) ℚ_[ℓ])
        continuous_const :=
  asIso (LAdicSheaf.constantSystemToTrivialRepresentation B X x) ≪≫
    eqToIso (LAdicSheaf.representationSheaf_one_eq B X x).symm

/-- The constant ℓ-adic sheaf and `ℱ_𝟏` are isogenous (with `N = 0`). -/
theorem LAdicSheaf.exists_constantSystem_isogeny_representationSheaf_one :
    ∃ (φ : LAdicSheaf.constantSystem B X ℓ ⟶
        LAdicSheaf.representationSheaf B X x (1 : EtaleFundamentalGroup X.1 x →* GL (Fin 1) ℚ_[ℓ])
          continuous_const) (ψ : _ ⟶ _) (N : ℕ),
      φ ≫ ψ = (ℓ ^ N) • 𝟙 _ ∧ ψ ≫ φ = (ℓ ^ N) • 𝟙 _ :=
  ⟨(LAdicSheaf.constantSystemIsoRepresentationSheafOne B X x).hom,
    (LAdicSheaf.constantSystemIsoRepresentationSheafOne B X x).inv, 0, by simp, by simp⟩

/-- **The Frobenius characteristic polynomials on `Hⁱ_c(X_k̄, - ⊗ ℚ_ℓ)` of `ℱ_𝟏` and of the
constant ℓ-adic sheaf agree.** -/
theorem LAdicSheaf.charpoly_rationalGeometricCompactlySupportedFrobenius_representationSheaf_one_eq
    {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] (j : CompactificationOf (Over.mk f))
    (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
    (hcard : Fintype.card k = p ^ q) (i : ℤ)
    [FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar
      (LAdicSheaf.constantSystem B X ℓ) i)]
    [FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar
      (LAdicSheaf.representationSheaf B X x (1 : EtaleFundamentalGroup X.1 x →* GL (Fin 1) ℚ_[ℓ])
        continuous_const) i)] :
    (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard
        (LAdicSheaf.representationSheaf B X x (1 : EtaleFundamentalGroup X.1 x →* GL (Fin 1) ℚ_[ℓ])
          continuous_const) i).hom.charpoly =
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard
        (LAdicSheaf.constantSystem B X ℓ) i).hom.charpoly :=
  LAdicSheaf.charpoly_rationalGeometricCompactlySupportedFrobenius_eq_of_isogeny B X ℓ f j kbar p q
    hcard (LAdicSheaf.constantSystemIsoRepresentationSheafOne B X x).hom
    (LAdicSheaf.constantSystemIsoRepresentationSheafOne B X x).inv 0 (by simp) (by simp) i

end Level

end LAdic

end Weil

end
