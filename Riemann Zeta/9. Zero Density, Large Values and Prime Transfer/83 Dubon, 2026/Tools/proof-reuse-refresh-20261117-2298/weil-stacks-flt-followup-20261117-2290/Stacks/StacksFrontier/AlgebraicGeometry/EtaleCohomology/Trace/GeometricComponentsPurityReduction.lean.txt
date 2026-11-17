module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricConnectednessPurityReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RationalPointPurityReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicExcisionCharpolyRoots
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FieldExtensionSchemeSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SurjectiveClosedImmersionWeights
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules
public import StacksFrontier.AlgebraicGeometry.GeomConnectedFibres.Basic
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.ConnectedLocal

/-!
# Purity for `X` whose geometric fibre is disconnected

In the proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) (Deligne, Weil II), purity of
`Hⁱ(X_k̄, ℱ_ρ)` for `X` connected, proper and smooth of relative dimension `d` over a finite field
`k` is reduced to the case where `X_k̄` is connected
(`Stacks.EtaleCohomology.LAdicSheaf.GeometricComponentsPurityReductionInput`).

The ring `k' = Γ(X, 𝒪_X)` is a finite field extension of `k`, of degree `m + 1`, because `X` is
connected, proper and reduced, and `X` is geometrically connected over `k'` (Tag 0FD1).  Let
`X' = X ×_k k'`.  Its geometric Frobenius over `k'` is the `(m + 1)`-th power of that of `X` on
`Hⁱ_c(X_k̄, ℱ_ρ) = Hⁱ_c(X'_{k̄}, ℱ_ρ|_{X'})`
(`LAdicSheaf.charpoly_rationalGeometricCompactlySupportedFrobenius_fieldExtension`).
The scheme `X'` is the union of the open and closed subschemes `s_τ(X)` for the sections
`s_τ = (id, Spec(τ) ∘ g)`, `τ ∈ Aut(k'/k)`, of `X' ⟶ X`
(`Stacks.EtaleCohomology.exists_mem_range_fieldExtensionSection`), each isomorphic to `X` with the
`k'`-structure `Spec(τ) ∘ g`, hence geometrically connected, proper and smooth of relative
dimension `d` over `k'`: purity holds on each by assumption, through the isogeny between the
restriction of `ℱ_ρ` and the sheaf `ℱ_{ρ'}` of the restricted representation.  Excision for the
characteristic roots
(`LAdicSheaf.isCharpolyPureOfWeight_rationalGeometricCompactlySupportedFrobenius_of_openClosed`)
gives purity on `X'`, and purity of weight `i` for a power is purity of weight `i`.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.isCharpolyPureOfWeight_fieldExtensionComponent`.
* `Stacks.EtaleCohomology.LAdicSheaf.isCharpolyPureOfWeight_fieldExtensionClopen`.
* `Stacks.EtaleCohomology.LAdicSheaf.representationPurityAt_of_fieldStructure`.
* `Stacks.EtaleCohomology.LAdicSheaf.geometricComponentsPurityReductionInput`: the reduction
  holds.
* `Stacks.EtaleCohomology.LAdicSheaf.geometricConnectednessPurityReductionInput`: hence so does
  the reduction to `X` geometrically connected of pure relative dimension.

The statements consume objects defined in the standard model `HasDerivedCategory.standard` of the
derived category, which is therefore a local instance here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  Sheaf.monoidalCategory etaleModuleInverseImageSheafPullbackMonoidal
  etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits
  etaleModuleDirectImage_preservesFiniteColimits_of_universalHomeomorphism

/-! ### Base changes and geometric points along isomorphisms -/

/-- Connectedness of a base change only depends on the two morphisms up to equality. -/
theorem connectedSpace_pullback_of_eq {X Y T : Scheme.{u}} {a a' : X ⟶ Y} {S S' : T ⟶ Y}
    (ha : a = a') (hS : S = S') [ConnectedSpace ↥(pullback a' S')] :
    ConnectedSpace ↥(pullback a S) := by
  subst ha hS
  assumption

/-- **The base change of `t ≫ G` for an isomorphism `t` is connected when that of `G` is.** -/
theorem connectedSpace_pullback_isIso_comp {U X Y T : Scheme.{u}} (t : U ⟶ X) [IsIso t]
    (G : X ⟶ Y) (S : T ⟶ Y) [ConnectedSpace ↥(pullback G S)] :
    ConnectedSpace ↥(pullback (t ≫ G) S) := by
  let φ : pullback G S ⟶ pullback (t ≫ G) S :=
    pullback.lift (pullback.fst _ _ ≫ inv t) (pullback.snd _ _) (by
      simp only [Category.assoc, IsIso.inv_hom_id_assoc, pullback.condition])
  let ψ : pullback (t ≫ G) S ⟶ pullback G S :=
    pullback.lift (pullback.fst _ _ ≫ t) (pullback.snd _ _) (by
      rw [Category.assoc, pullback.condition])
  have hψ : ψ ≫ φ = 𝟙 _ := by
    apply pullback.hom_ext <;>
      simp only [φ, ψ, Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc, IsIso.hom_inv_id, Category.comp_id, Category.id_comp]
  have hsurj : Function.Surjective φ := fun z => ⟨ψ z, by
    rw [← Scheme.Hom.comp_apply, hψ]
    rfl⟩
  exact hsurj.connectedSpace φ.continuous

/-- **A geometric point lifts along an isomorphism.** -/
theorem exists_geometricPoint_map_eq_of_isIso {U X : Scheme.{u}} (t : U ⟶ X) [IsIso t]
    (x : GeometricPoint X) : ∃ y : GeometricPoint U, y.map t = x := by
  cases x with
  | mk K hom =>
    refine ⟨{ residueField := K, hom := hom ≫ inv t }, ?_⟩
    simp only [GeometricPoint.map, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

section Cohomology

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]

/-- **On an empty scheme every Frobenius is pure**: `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ) = 0`. -/
theorem LAdicSheaf.isCharpolyPureOfWeight_rationalGeometricCompactlySupportedFrobenius_of_isEmpty
    {X : B.Scheme} [IsNoetherian X.1] [IsEmpty X.1] {k : Type u} [Field k] [Fintype k]
    (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
    (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)
    (F : LAdicSheaf.{u, u + 1} B X ℓ) (i : ℤ)
    [FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i)]
    (q' : ℕ) (ι : ℚ_[ℓ] →+* ℂ) (w : ℤ) :
    IsCharpolyPureOfWeight q' ι w
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F
        i).hom := by
  have h : ∀ n : ℕᵒᵖ, IsZero
      ((LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f j kbar F i).obj n) :=
    fun n =>
    (isZero_compactSupportSheafCohomology_obj ℤ_[ℓ] f j kbar i
      (isZero_etaleModulesUniv_of_isEmpty ℤ_[ℓ] X.1 _)).of_iso
      ((LAdicSheaf.padicTowerCohomologyIso B X ℓ f j kbar F i).app n).symm
  have hl : IsZero (lim.obj (LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f j kbar
      F i)) :=
    (IsZero.iff_id_eq_zero _).2 (limit.hom_ext fun n => (h n).eq_of_tgt _ _)
  have : Subsingleton
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i) :=
    ModuleCat.isZero_iff_subsingleton.1
      ((ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map_isZero hl)
  exact isCharpolyPureOfWeight_of_subsingleton _ _ _ _

end Cohomology

/-! ### The components of `X ×_k k'` -/

section Components

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  (hP : LAdicSheaf.GeometricPurity B ℓ)
  {k : Type u} [Field k] [Fintype k] (kbar : Type u) [Field kbar] [Algebra k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q) (hℓ : ℓ ≠ p)
  (X : B.Scheme) [IsNoetherian X.1] [ConnectedSpace X.1] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [IsProper f] (d : ℕ)
  [SmoothOfRelativeDimension d f]
  (k' : Type u) [Field k'] [Fintype k'] [Algebra k k'] [Module.Finite k k'] [CharP k' p]
  [Algebra k' kbar] [IsScalarTower k k' kbar] [IsAlgClosure k' kbar]
  (m : ℕ) (hcard' : Fintype.card k' = p ^ (q * (m + 1)))
  [IsNoetherian (fieldExtensionScheme B X f k').1]
  (g : X.1 ⟶ Spec (.of k')) (hg : g ≫ specAlgebraMap k k' = f)
  (hgc : ∀ φ : k' →+* kbar, ConnectedSpace ↥(pullback g (Spec.map (CommRingCat.ofHom φ))))
  (x : GeometricPoint X.1) {r : ℕ} (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℚ_[ℓ])
  (hρ : Continuous ρ)
  (hD : ∀ ι : ℚ_[ℓ] →+* ℂ, HasDeligneConclusions (geometricFrobeniusFamily f x) p ι ρ)
  (i : ℤ) (ι : ℚ_[ℓ] →+* ℂ)

omit [Algebra k kbar] [CharP k p] [QuasiCompact f] [IsSeparated f] [IsScalarTower k k' kbar]
  [AlgebraicGeometry.IsNoetherian (fieldExtensionScheme B X f k').1] in
include hP hℓ hgc hD d in
/-- **Purity on a component `s_τ(X)` of `X ×_k k'`.**  An open and closed subscheme `U` of
`X ×_k k'` with the same points as `s_τ(X)` is isomorphic to `X` through the projection, with the
`k'`-structure `Spec(τ) ∘ g`; it is connected, geometrically connected, proper and smooth of
relative dimension `d` over `k'`, and the restriction of `ℱ_ρ` to it is isogenous to the sheaf
`ℱ_{ρ'}` of the restriction `ρ'` of `ρ`, which satisfies the conclusions of Deligne's
conjecture. -/
theorem LAdicSheaf.isCharpolyPureOfWeight_fieldExtensionComponent (τ : k' →ₐ[k] k')
    (U : B.Scheme) [IsNoetherian U.1] (cU : U ⟶ fieldExtensionScheme B X f k')
    [IsOpenImmersion (B.inclusion.map cU)] [IsClosedImmersion (B.inclusion.map cU)]
    (hrange : Set.range (B.inclusion.map cU) = Set.range (fieldExtensionSection f g hg τ))
    (hU : U.1 ⟶ Spec (.of k')) [LocallyOfFiniteType hU] [QuasiCompact hU] [IsSeparated hU]
    (hhU : hU = B.inclusion.map cU ≫ pullback.snd f (specAlgebraMap k k'))
    (jc : CompactificationOf (Over.mk hU))
    [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ hU jc
      kbar (LAdicSheaf.inverseImage (ℓ := ℓ) (cU ≫ fieldExtensionProj B X f k')
        (LAdicSheaf.representationSheaf B X x ρ hρ)) i)] :
    IsCharpolyPureOfWeight (p ^ (q * (m + 1))) ι i
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B U ℓ hU jc kbar p (q * (m + 1))
        hcard' (LAdicSheaf.inverseImage (ℓ := ℓ) (cU ≫ fieldExtensionProj B X f k')
          (LAdicSheaf.representationSheaf B X x ρ hρ)) i).hom := by
  set c := B.inclusion.map cU with hc
  set s := fieldExtensionSection f g hg τ with hs
  have : IsOpenImmersion s := isOpenImmersion_fieldExtensionSection f g hg τ
  -- the isomorphism `t : U ≅ X`
  let t : U.1 ⟶ X.1 := IsOpenImmersion.lift s c hrange.le
  have ht : t ≫ s = c := IsOpenImmersion.lift_fac s c hrange.le
  have : IsOpenImmersion t := by
    have : IsOpenImmersion (t ≫ s) := by rw [ht]; infer_instance
    exact IsOpenImmersion.of_comp t s
  have htsurj : Function.Surjective t := fun z => by
    obtain ⟨u, hu⟩ : s z ∈ Set.range c := hrange ▸ ⟨z, rfl⟩
    refine ⟨u, s.isOpenEmbedding.injective ?_⟩
    rw [← hu, ← ht, Scheme.Hom.comp_apply]
  have : IsIso t := (isIso_iff_isOpenImmersion_and_surjective t).2 ⟨inferInstance, ⟨htsurj⟩⟩
  let h : U ⟶ X := cU ≫ fieldExtensionProj B X f k'
  have hth : h.hom = t := by
    show c ≫ pullback.fst f (specAlgebraMap k k') = t
    rw [← ht, Category.assoc, hs, fieldExtensionSection_fst, Category.comp_id]
  have : IsIso h.hom := by rw [hth]; infer_instance
  have : ConnectedSpace U.1 :=
    Function.Surjective.connectedSpace (inv t).surjective (inv t).continuous
  -- the geometric point of `U` over `x`
  obtain ⟨y, rfl⟩ := exists_geometricPoint_map_eq_of_isIso h.hom x
  -- `U` is proper and smooth of relative dimension `d` over `k'`
  have : SmoothOfRelativeDimension d (pullback.snd f (specAlgebraMap k k')) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange d).of_isPullback
      (IsPullback.of_hasPullback f (specAlgebraMap k k')) ‹_›
  have : IsProper hU := by rw [hhU]; infer_instance
  have : SmoothOfRelativeDimension d hU := by
    have h0 := smoothOfRelativeDimension_comp 0 d c (pullback.snd f (specAlgebraMap k k'))
    rwa [Nat.zero_add, ← hhU] at h0
  -- `U` is geometrically connected over `k'`
  have hbij : Function.Bijective τ := Algebra.IsAlgebraic.algHom_bijective τ
  let τe : k' ≃ₐ[k] k' := AlgEquiv.ofBijective τ hbij
  have hUeq : hU = t ≫ g ≫ Spec.map (CommRingCat.ofHom τ.toRingHom) := by
    rw [hhU, ← ht, Category.assoc, hs, fieldExtensionSection_snd]
  have hinv : ∀ a b : k' →+* k', (∀ z, b (a z) = z) →
      Spec.map (CommRingCat.ofHom b) ≫ Spec.map (CommRingCat.ofHom a) = 𝟙 _ := fun a b h => by
    rw [← Spec.map_comp]
    have hcomp : CommRingCat.ofHom a ≫ CommRingCat.ofHom b = 𝟙 _ := by
      ext z
      exact h z
    rw [hcomp, Spec.map_id]
  have hτ₁ := hinv τ.toRingHom τe.symm.toRingHom τe.symm_apply_apply
  have hτ₂ := hinv τe.symm.toRingHom τ.toRingHom τe.apply_symm_apply
  have hS : specAlgebraMap k' kbar ≫ Spec.map (CommRingCat.ofHom τe.symm.toRingHom) =
      Spec.map (CommRingCat.ofHom ((algebraMap k' kbar).comp τe.symm.toRingHom)) := by
    rw [specAlgebraMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have : ConnectedSpace ↥(pullback g (specAlgebraMap k' kbar ≫
      Spec.map (CommRingCat.ofHom τe.symm.toRingHom))) := by
    have := hgc ((algebraMap k' kbar).comp τe.symm.toRingHom)
    exact connectedSpace_pullback_of_eq rfl hS
  have : ConnectedSpace ↥(pullback (g ≫ Spec.map (CommRingCat.ofHom τ.toRingHom))
      (specAlgebraMap k' kbar)) :=
    connectedSpace_pullback_comp_of_inverse g _ _ hτ₁ hτ₂ _
  have : ConnectedSpace ↥(pullback (t ≫ g ≫ Spec.map (CommRingCat.ofHom τ.toRingHom))
      (specAlgebraMap k' kbar)) :=
    connectedSpace_pullback_isIso_comp t _ _
  have : ConnectedSpace (fieldBaseChange (Over.mk hU) kbar) :=
    connectedSpace_pullback_of_eq hUeq rfl
  -- the restricted representation satisfies the conclusions of Deligne's conjecture
  let φ₀ := (etaleFundamentalGroupMap h.hom y).toMonoidHom
  have hφ₀ : Continuous φ₀ := (etaleFundamentalGroupMap h.hom y).continuous
  have hD' : ∀ ι : ℚ_[ℓ] →+* ℂ, HasDeligneConclusions (geometricFrobeniusFamily hU y) p ι
      (ρ.comp φ₀) := fun ι =>
    HasDeligneConclusions.comp_etaleFundamentalGroupMap f hU h.hom h.hom.isClosedMap y (hD ι)
  -- purity for `ℱ_{ρ'}`, then for `h⁻¹ℱ_ρ` through the isogeny and Tag 0F7I
  have hfd : ∀ F : LAdicSheaf.{u, u + 1} B U ℓ, FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ hU
        (CompactificationOf.ofProper hU) kbar F i) := fun F =>
    LAdicSheaf.finiteDimensional_rationalGeometricCompactlySupportedCohomology B ℓ kbar p _ hcard'
      hℓ _ _ _ _ i
  have := hfd (LAdicSheaf.representationSheaf B U y (ρ.comp φ₀) (hρ.comp hφ₀))
  have := hfd (LAdicSheaf.inverseImage (ℓ := ℓ) h
    (LAdicSheaf.representationSheaf B X (y.map h.hom) ρ hρ))
  have hpure := hP k' kbar p (q * (m + 1)) hcard' hℓ U hU d y (ρ.comp φ₀) (hρ.comp hφ₀) hD' i ι
  obtain ⟨φ, ψ, N, h₁, h₂⟩ := exists_inverseImage_representationSheaf_isogeny B h y ρ hρ
  have hiso := LAdicSheaf.charpoly_rationalGeometricCompactlySupportedFrobenius_eq_of_isogeny B U ℓ
    hU (CompactificationOf.ofProper hU) kbar p (q * (m + 1)) hcard' φ ψ N h₁ h₂ i
  have hind :=
    LAdicSheaf.charpoly_rationalGeometricCompactlySupportedFrobenius_eq_of_compactifications
      B ℓ kbar p (q * (m + 1)) hcard' hℓ U hU jc (CompactificationOf.ofProper hU)
      (LAdicSheaf.inverseImage (ℓ := ℓ) h
        (LAdicSheaf.representationSheaf B X (y.map h.hom) ρ hρ)) i
  exact fun z hz => hpure z (by rwa [hind, ← hiso] at hz)

omit [Algebra k kbar] [CharP k p] [QuasiCompact f] [IsSeparated f] [IsScalarTower k k' kbar]
  [AlgebraicGeometry.IsNoetherian (fieldExtensionScheme B X f k').1] in
include hP hℓ hgc hD d in
/-- **Purity on the open and closed subschemes of `X ×_k k'` covered by finitely many
components.**  By induction on the finite set `S` of the `τ` with `W ⊆ ⋃_{τ ∈ S} s_τ(X)`: the
points of `W` on `s_τ(X)` form an open and closed subscheme `U` of `W`, empty or equal to the
connected `s_τ(X)`, and its complement lies in the components of `S \ {τ}`; excision for the
characteristic roots glues. The sheaf on `W` is given by an identification of its tower of levels
with the restriction of the tower of `ℱ_ρ`. -/
theorem LAdicSheaf.isCharpolyPureOfWeight_fieldExtensionClopen (S : Finset (k' →ₐ[k] k')) :
    ∀ (W : B.Scheme) [IsNoetherian W.1] (jW : W ⟶ fieldExtensionScheme B X f k')
      [IsOpenImmersion (B.inclusion.map jW)] [IsClosedImmersion (B.inclusion.map jW)],
      (∀ w : W.1, ∃ τ ∈ S, B.inclusion.map jW w ∈ Set.range (fieldExtensionSection f g hg τ)) →
      ∀ (hW : W.1 ⟶ Spec (.of k')) [LocallyOfFiniteType hW] [QuasiCompact hW] [IsSeparated hW],
      hW = B.inclusion.map jW ≫ pullback.snd f (specAlgebraMap k k') →
      ∀ (πW : W.1 ⟶ X.1), πW = B.inclusion.map jW ≫ pullback.fst f (specAlgebraMap k k') →
      ∀ (FW : LAdicSheaf.{u, u + 1} B W ℓ),
      (LAdicSheaf.padicTower B X ℓ (LAdicSheaf.representationSheaf B X x ρ hρ) ⋙
        etaleModuleInverseImage.{u, 0} ℤ_[ℓ] πW ≅ LAdicSheaf.padicTower B W ℓ FW) →
      ∀ (jc : CompactificationOf (Over.mk hW))
        [FiniteDimensional ℚ_[ℓ]
          (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B W ℓ hW jc kbar FW i)],
        IsCharpolyPureOfWeight (p ^ (q * (m + 1))) ι i
          (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B W ℓ hW jc kbar p (q * (m + 1))
            hcard' FW i).hom := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro W _ jW _ _ hcov hW _ _ _ _ πW _ FW _ jc _
    have : IsEmpty W.1 := ⟨fun w => by
      obtain ⟨τ, hτ, -⟩ := hcov w
      simp at hτ⟩
    exact LAdicSheaf.isCharpolyPureOfWeight_rationalGeometricCompactlySupportedFrobenius_of_isEmpty
      B ℓ hW jc kbar p (q * (m + 1)) hcard' FW i _ ι i
  | @insert τ S hτS ih =>
    intro W _ jW _ _ hcov hW _ _ _ hhW πW hπW FW eW jc _
    set c := B.inclusion.map jW with hc
    set s := fieldExtensionSection f g hg τ with hs
    have : IsOpenImmersion s := isOpenImmersion_fieldExtensionSection f g hg τ
    have : IsClosedImmersion s := isClosedImmersion_fieldExtensionSection f g hg τ
    -- the points of `W` on `s_τ(X)`, an open and closed subset
    let V : Set W.1 := c ⁻¹' Set.range s
    have hVo : IsOpen V := s.isOpenEmbedding.isOpen_range.preimage c.continuous
    have hVc : IsClosed V := s.isClosedEmbedding.isClosed_range.preimage c.continuous
    let VU : W.1.Opens := ⟨V, hVo⟩
    let VZ : W.1.Opens := ⟨Vᶜ, hVc.isOpen_compl⟩
    let U : B.Scheme := B.obj (VU : Scheme.{u})
      (Scheme.size_lt_of_mono_of_isStrongPrelimit B.cutoff_isStrongPrelimit VU.ι W.property)
    let Z : B.Scheme := B.obj (VZ : Scheme.{u})
      (Scheme.size_lt_of_mono_of_isStrongPrelimit B.cutoff_isStrongPrelimit VZ.ι W.property)
    let jU : U ⟶ W := ObjectProperty.homMk VU.ι
    let iZ : Z ⟶ W := ObjectProperty.homMk VZ.ι
    have hjUo : IsOpenImmersion (B.inclusion.map jU) := (inferInstance : IsOpenImmersion VU.ι)
    have hiZo : IsOpenImmersion (B.inclusion.map iZ) := (inferInstance : IsOpenImmersion VZ.ι)
    have hcl : ∀ O : W.1.Opens, IsClosed (O : Set W.1) →
        IsClosedImmersion O.ι ∧ IsNoetherian (O : Scheme.{u}) := fun O hO => by
      have hOc : IsClosedImmersion O.ι :=
        IsClosedImmersion.of_isPreimmersion O.ι (by rwa [Scheme.Opens.range_ι])
      have := ‹AlgebraicGeometry.IsNoetherian W.1›.toIsLocallyNoetherian
      have : IsLocallyNoetherian (O : Scheme.{u}) := isLocallyNoetherian_of_isClosedImmersion O.ι
      have : CompactSpace O := isCompact_iff_compactSpace.mp hO.isCompact
      exact ⟨hOc, { }⟩
    obtain ⟨hjUc, hUn⟩ : IsClosedImmersion (B.inclusion.map jU) ∧ IsNoetherian U.1 := hcl VU hVc
    obtain ⟨hiZc, hZn⟩ : IsClosedImmersion (B.inclusion.map iZ) ∧ IsNoetherian Z.1 :=
      hcl VZ hVo.isClosed_compl
    have hij : Set.range (B.inclusion.map jU).base = (Set.range (B.inclusion.map iZ).base)ᶜ := by
      show Set.range VU.ι = (Set.range VZ.ι)ᶜ
      rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
      exact (compl_compl V).symm
    -- the sheaves on the two pieces and their towers
    let FU : LAdicSheaf.{u, u + 1} B U ℓ := LAdicSheaf.inverseImage (ℓ := ℓ)
      ((jU ≫ jW) ≫ fieldExtensionProj B X f k') (LAdicSheaf.representationSheaf B X x ρ hρ)
    let FZ : LAdicSheaf.{u, u + 1} B Z ℓ := LAdicSheaf.inverseImage (ℓ := ℓ) iZ FW
    have hUπ :
        B.inclusion.map jU ≫ πW = B.inclusion.map ((jU ≫ jW) ≫ fieldExtensionProj B X f k') := by
      rw [hπW]
      rfl
    let eU : LAdicSheaf.padicTower B W ℓ FW ⋙ etaleModuleInverseImage.{u, 0} ℤ_[ℓ]
        (B.inclusion.map jU) ≅ LAdicSheaf.padicTower B U ℓ FU :=
      Functor.isoWhiskerRight eW.symm _ ≪≫ Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ ((etaleModuleInverseImageCompIso.{u, 0} ℤ_[ℓ]
          (B.inclusion.map jU) πW).symm ≪≫ eqToIso (congrArg _ hUπ)) ≪≫
        LAdicSheaf.padicTowerInverseImageIso B ℓ ((jU ≫ jW) ≫ fieldExtensionProj B X f k') _
    let eZ : LAdicSheaf.padicTower B W ℓ FW ⋙ etaleModuleInverseImage.{u, 0} ℤ_[ℓ]
        (B.inclusion.map iZ) ≅ LAdicSheaf.padicTower B Z ℓ FZ :=
      LAdicSheaf.padicTowerInverseImageIso B ℓ iZ FW
    let eZ' : LAdicSheaf.padicTower B X ℓ (LAdicSheaf.representationSheaf B X x ρ hρ) ⋙
        etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map iZ ≫ πW) ≅
          LAdicSheaf.padicTower B Z ℓ FZ :=
      Functor.isoWhiskerLeft _ (etaleModuleInverseImageCompIso.{u, 0} ℤ_[ℓ]
          (B.inclusion.map iZ) πW) ≪≫ (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight eW _ ≪≫ eZ
    -- finiteness
    have hfinU := LAdicSheaf.finiteCompactSupportCohomologyInput B ℓ k' kbar p (q * (m + 1))
      hcard' hℓ U (B.inclusion.map jU ≫ hW) (jc.restrictOpen (B.inclusion.map jU)) FU i
    have := hfinU.1
    have := (LAdicSheaf.finiteCompactSupportCohomologyInput B ℓ k' kbar p (q * (m + 1))
      hcard' hℓ Z (B.inclusion.map iZ ≫ hW) (jc.restrictClosed (B.inclusion.map iZ)) FZ i).1
    refine
      LAdicSheaf.isCharpolyPureOfWeight_rationalGeometricCompactlySupportedFrobenius_of_openClosed
        B ℓ hW jc kbar p (q * (m + 1)) hcard' FW i jU iZ hij FU FZ eU eZ hfinU.2 ?_ ?_
    · -- the piece on `s_τ(X)`: empty, or all of `s_τ(X)`
      rcases isEmpty_or_nonempty U.1 with hUe | hUne
      · exact
          LAdicSheaf.isCharpolyPureOfWeight_rationalGeometricCompactlySupportedFrobenius_of_isEmpty
            B ℓ _ _ kbar p (q * (m + 1)) hcard' FU i _ ι i
      · obtain ⟨u₀⟩ := hUne
        have : IsOpenImmersion (B.inclusion.map (jU ≫ jW)) :=
          (inferInstance : IsOpenImmersion (B.inclusion.map jU ≫ c))
        have : IsClosedImmersion (B.inclusion.map (jU ≫ jW)) :=
          (inferInstance : IsClosedImmersion (B.inclusion.map jU ≫ c))
        have hsub : Set.range s ⊆ Set.range c := by
          have hconn : _root_.IsPreconnected (Set.range s) :=
            (isConnected_range s.continuous).isPreconnected
          have hclopen : IsClopen (Set.range c) :=
            ⟨c.isClosedEmbedding.isClosed_range, c.isOpenEmbedding.isOpen_range⟩
          exact hconn.subset_isClopen hclopen ⟨c (VU.ι u₀), u₀.2, ⟨_, rfl⟩⟩
        have hrange : Set.range (B.inclusion.map (jU ≫ jW)) = Set.range s := by
          apply Set.Subset.antisymm
          · rintro _ ⟨u, rfl⟩
            exact u.2
          · intro z hz
            obtain ⟨w, hw⟩ := hsub hz
            have hwV : w ∈ VU := by
              show c w ∈ Set.range s
              rw [hw]
              exact hz
            refine ⟨⟨w, hwV⟩, ?_⟩
            rw [← hw]
            rfl
        exact LAdicSheaf.isCharpolyPureOfWeight_fieldExtensionComponent B ℓ hP kbar p q hℓ X f d k'
          m hcard' g hg hgc x ρ hρ hD i ι τ U (jU ≫ jW) hrange (B.inclusion.map jU ≫ hW)
          (by rw [hhW]; rfl) _
    · -- the rest lies on the components of `S`
      have : IsOpenImmersion (B.inclusion.map (iZ ≫ jW)) :=
        (inferInstance : IsOpenImmersion (B.inclusion.map iZ ≫ c))
      have : IsClosedImmersion (B.inclusion.map (iZ ≫ jW)) :=
        (inferInstance : IsClosedImmersion (B.inclusion.map iZ ≫ c))
      refine ih Z (iZ ≫ jW) (fun z => ?_) (B.inclusion.map iZ ≫ hW) (by rw [hhW]; rfl)
        (B.inclusion.map iZ ≫ πW) (by rw [hπW]; rfl) FZ eZ' (jc.restrictClosed (B.inclusion.map iZ))
      obtain ⟨σ, hσ, hz⟩ := hcov (VZ.ι z)
      rcases Finset.mem_insert.1 hσ with rfl | hσS
      · exact absurd hz z.2
      · exact ⟨σ, hσS, hz⟩

end Components

/-! ### The reduction -/

section Reduction

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]

/-- **Purity on `X` from purity on geometrically connected schemes, given a `k'`-structure of `X`
over which `X` is geometrically connected**, for a finite extension `k'` of `k` of degree `m + 1`:
the Frobenius of `X ×_k k'` over `k'` is the `(m + 1)`-th power of that of `X`, and `X ×_k k'` is
covered by the components `s_τ(X)`. -/
theorem LAdicSheaf.representationPurityAt_of_fieldStructure
    (hP : LAdicSheaf.GeometricPurity B ℓ) {k : Type u} [Field k] [Fintype k]
    (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar] (p q : ℕ)
    [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q) (hℓ : ℓ ≠ p) (X : B.Scheme)
    [IsNoetherian X.1] [ConnectedSpace X.1] (f : X.1 ⟶ Spec (.of k))
    [QuasiCompact f] [IsProper f] (d : ℕ) [SmoothOfRelativeDimension d f]
    (k' : Type u) [Field k'] [Finite k'] [Algebra k k'] [Module.Finite k k'] (m : ℕ)
    (hm : Module.finrank k k' = m + 1) (g : X.1 ⟶ Spec (.of k'))
    (hg : g ≫ specAlgebraMap k k' = f)
    (hgc : ∀ φ : k' →+* kbar, ConnectedSpace ↥(pullback g (Spec.map (CommRingCat.ofHom φ)))) :
    LAdicSheaf.RepresentationPurityAt B ℓ X f kbar p q hcard := by
  intro x r ρ hρ hD i _ ι
  have := Fintype.ofFinite k'
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  have : CharP k' p := charP_of_injective_algebraMap (algebraMap k k').injective p
  have hcard' : Fintype.card k' = p ^ (q * (m + 1)) := by
    rw [Module.card_eq_pow_finrank (K := k) (V := k'), hcard, hm, pow_mul]
  have : Algebra.IsAlgebraic k k' := Algebra.IsAlgebraic.of_finite k k'
  let σ : k' →ₐ[k] kbar := IsAlgClosed.lift
  let : Algebra k' kbar := σ.toRingHom.toAlgebra
  have : IsScalarTower k k' kbar := IsScalarTower.of_algebraMap_eq fun c => (σ.commutes c).symm
  have : Algebra.IsAlgebraic k kbar := IsAlgClosure.isAlgebraic
  have : Algebra.IsAlgebraic k' kbar := Algebra.IsAlgebraic.tower_top (K := k) k'
  have : IsAlgClosure k' kbar := ⟨inferInstance, inferInstance⟩
  have : IsNoetherian (fieldExtensionScheme B X f k').1 :=
    isNoetherian_fieldExtensionScheme B X f k'
  have := LAdicSheaf.finiteDimensional_rationalGeometricCompactlySupportedCohomology B ℓ kbar p
    (q * (m + 1)) hcard' hℓ (fieldExtensionScheme B X f k') (pullback.snd f (specAlgebraMap k k'))
    (compactificationFieldBaseChange f (CompactificationOf.ofProper f) k')
    (LAdicSheaf.inverseImage (ℓ := ℓ) (fieldExtensionProj B X f k')
      (LAdicSheaf.representationSheaf B X x ρ hρ)) i
  have : IsOpenImmersion (B.inclusion.map (𝟙 (fieldExtensionScheme B X f k'))) :=
    (inferInstance : IsOpenImmersion (𝟙 (pullback f (specAlgebraMap k k'))))
  have : IsClosedImmersion (B.inclusion.map (𝟙 (fieldExtensionScheme B X f k'))) :=
    (inferInstance : IsClosedImmersion (𝟙 (pullback f (specAlgebraMap k k'))))
  have hY :=
    LAdicSheaf.isCharpolyPureOfWeight_fieldExtensionClopen B ℓ hP kbar p q hℓ X f d k' m
      hcard' g hg hgc x ρ hρ hD i ι Finset.univ (fieldExtensionScheme B X f k') (𝟙 _)
      (fun w => (exists_mem_range_fieldExtensionSection f g hg w).imp fun _ hτ =>
        ⟨Finset.mem_univ _, hτ⟩)
      (pullback.snd f (specAlgebraMap k k'))
      (by rw [CategoryTheory.Functor.map_id, Category.id_comp])
      (pullback.fst f (specAlgebraMap k k'))
      (by rw [CategoryTheory.Functor.map_id, Category.id_comp])
      (LAdicSheaf.inverseImage (ℓ := ℓ) (fieldExtensionProj B X f k')
        (LAdicSheaf.representationSheaf B X x ρ hρ))
      (by exact LAdicSheaf.padicTowerInverseImageIso B ℓ (fieldExtensionProj B X f k') _)
      (compactificationFieldBaseChange f (CompactificationOf.ofProper f) k')
  have hc : (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B
      (fieldExtensionScheme B X f k') ℓ (pullback.snd f (specAlgebraMap k k'))
      (compactificationFieldBaseChange f (CompactificationOf.ofProper f) k') kbar p (q * (m + 1))
      hcard' (LAdicSheaf.inverseImage (ℓ := ℓ) (fieldExtensionProj B X f k')
        (LAdicSheaf.representationSheaf B X x ρ hρ)) i).hom.charpoly =
      ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
        (CompactificationOf.ofProper f) kbar p q hcard
        (LAdicSheaf.representationSheaf B X x ρ hρ) i).hom ^ (m + 1)).charpoly :=
    LAdicSheaf.charpoly_rationalGeometricCompactlySupportedFrobenius_fieldExtension B X ℓ
      f (CompactificationOf.ofProper f) k' kbar _ i p q hcard m hcard'
  refine IsCharpolyPureOfWeight.of_pow (m := m + 1) (Nat.succ_ne_zero m) fun z hz => ?_
  rw [← pow_mul]
  exact hY z (by rwa [← hc] at hz)

/-- **[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH): the reduction of purity to `X_k̄`
connected.**  For `X` connected, proper and smooth of relative dimension `d` over a finite field
`k`, the ring `k' = Γ(X, 𝒪_X)` is a finite field extension of `k` (`X` being connected, proper
and reduced), `X` is geometrically connected over `k'` (Tag 0FD1), and
`Stacks.EtaleCohomology.LAdicSheaf.representationPurityAt_of_fieldStructure` applies. -/
theorem LAdicSheaf.geometricComponentsPurityReductionInput :
    LAdicSheaf.GeometricComponentsPurityReductionInput B ℓ := by
  intro hP k _ _ kbar _ _ _ p q _ _ hcard hℓ X _ _ f _ _ _ _ d _
  have : Smooth f := SmoothOfRelativeDimension.smooth d f
  have : AlgebraicGeometry.IsReduced X.1 := isReduced_of_smooth f
  have hfield :=
    AlgebraicGeometry.ProperSectionsGeom.isField_globalSections_of_connectedSpace_of_isReduced
      k f
  let : Field Γ(X.1, ⊤) := hfield.toField
  have : Nontrivial Γ(X.1, ⊤) := ⟨hfield.exists_pair_ne⟩
  let : Algebra k Γ(X.1, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  have : Module.Finite k Γ(X.1, ⊤) :=
    Stacks.AlgebraicGeometry.ProperSectionsGeom.moduleFinite_globalSections_of_isProper k f
  have : Finite Γ(X.1, ⊤) := Module.finite_of_finite k
  let : Fintype Γ(X.1, ⊤) := Fintype.ofFinite _
  have : Module.Free k Γ(X.1, ⊤) := Module.Free.of_divisionRing k Γ(X.1, ⊤)
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero
    (Module.finrank_pos (R := k) (M := Γ(X.1, ⊤))).ne'
  have hg : X.1.toSpecΓ ≫ specAlgebraMap k Γ(X.1, ⊤) = f := by
    show X.1.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) = f
    rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
      ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]
  have hgc : ∀ φ : Γ(X.1, ⊤) →+* kbar,
      ConnectedSpace ↥(pullback X.1.toSpecΓ (Spec.map (CommRingCat.ofHom φ))) := by
    intro φ
    have h0 :=
      AlgebraicGeometry.ProperGeomConnected.geometricallyConnected_toSpecΓ_of_isProper_over_field
        k X.1 f
    rw [geometricallyConnected_iff,
      geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms] at h0
    let : Algebra Γ(X.1, ⊤) kbar := φ.toAlgebra
    exact h0 kbar
  exact LAdicSheaf.representationPurityAt_of_fieldStructure B ℓ hP kbar p q hcard hℓ X f d
    Γ(X.1, ⊤) m hm X.1.toSpecΓ hg hgc

/-- **[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH): the reduction of purity to `X`
geometrically connected of pure relative dimension** holds, with no remaining input. -/
theorem LAdicSheaf.geometricConnectednessPurityReductionInput :
    LAdicSheaf.GeometricConnectednessPurityReductionInput B ℓ :=
  LAdicSheaf.geometricConnectednessPurityReductionInput_of_componentsInput B ℓ
    (LAdicSheaf.geometricComponentsPurityReductionInput B ℓ)

end Reduction

end Stacks.EtaleCohomology

end
