module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicExcisionCharpolyRoots
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicExcisionWeights
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIIFinalAssembly
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafRestrictionIsogeny
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicFiniteCompactSupportCohomology
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.Trace.RationalCohomologyFrobenius
public import Weil.AlgebraicGeometry.EtaleCohomology.Trace.LAdicTraceFormulaFinal
public import Weil.AlgebraicGeometry.EtaleCohomology.Trace.FieldOfConstantsCohomologyDecomposition
public import Weil.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafTrivialConstant
public import Weil.AlgebraicGeometry.EtaleCohomology.Trace.ZetaSeriesProductOfPointCountSum
public import Weil.AlgebraicGeometry.EtaleCohomology.Trace.FieldValuedPointCount
public import Weil.AlgebraicGeometry.EtaleCohomology.Trace.ZetaEulerProduct
public import Weil.AlgebraicGeometry.EtaleCohomology.Trace.ConstantSystemLocalFactor
public import Weil.AlgebraicGeometry.EtaleCohomology.Duality.TopDegreeFrobenius

/-!
# Frobenius characteristic polynomials of a disconnected proper scheme

Let `S` be a scheme proper and smooth of relative dimension `n` over a finite field `k` with `q`
elements, `ℓ ≠ char k` a prime, and `F_ν` the Frobenius endomorphism of `H^ν(S_k̄, ℚ_ℓ)`. The
scheme `S` is the disjoint union of finitely many connected open and closed subschemes `Y_i`,
again proper and smooth of relative dimension `n` over `k`, and

`det(T - F_ν | H^ν(S_k̄, ℚ_ℓ)) = ∏ᵢ det(T - F_ν | H^ν(Y_{i,k̄}, ℚ_ℓ))`

for every `ν`, provided the Frobenius of every connected smooth proper scheme over `k` is pure
(Deligne's theorem).

The proof is by noetherian induction on open and closed subschemes `W` of `S`: `W` is empty,
connected, or `W = U ⊔ Z` with `U`, `Z` nonempty open and closed. For such a decomposition

* the zeta functions multiply, `Z_W = Z_U Z_Z`, because the point counts add up;
* `Z_X(t) = ∏_ν det(1 - t F_ν | H^ν(X_k̄, ℚ_ℓ))^{(-1)^{ν+1}}` for `X = W, U, Z`;
* the Frobenius of `W` is pure of weight `ν` on `H^ν` when those of `U` and `Z` are (excision);

so the weights separate the degrees in the identity of zeta functions, and
`det(1 - t F_ν | H^ν(W)) = det(1 - t F_ν | H^ν(U)) det(1 - t F_ν | H^ν(Z))`.

## Main definitions

* `Weil.constantSystemToInverseImage`: the isomorphism `ℤ_ℓ ⟶ h⁻¹ℤ_ℓ` of ℓ-adic sheaves on `X'`
  for a morphism `h : X' ⟶ X`.

## Main results

* `Weil.charpoly_frobenius_inverseImage_constantSystem`: the Frobenius on `Hⁱ_c(X'_k̄, h⁻¹ℤ_ℓ)`,
  for any compactification, has the characteristic polynomial of `F_ν`.
* `Weil.zetaFunction_eq_mul_of_openClosed`: `Z_W = Z_U Z_Z` for `W = U ⊔ Z`.
* `Weil.charpoly_rationalFrobenius_eq_mul_of_openClosed`: the characteristic polynomials of the
  Frobenius over `W = U ⊔ Z`, for `U` and `Z` pure.
* `Weil.exists_connectedComponents_charpoly_eq_prod`: the characteristic polynomials of the
  Frobenius of `S` are the products of those of its connected components.

## Implementation notes

The multiplicativity is proved from the zeta functions and the weights rather than from a
decomposition `H^ν(S_k̄) = ⊕ᵢ H^ν(Y_{i,k̄})` of the cohomology, and so uses the purity of the
connected components. The excision for the characteristic roots computes the cohomology of a
piece `U ⟶ W` with the sheaf `h⁻¹ℤ_ℓ` and the compactification induced by that of `W`; the
compactification does not matter, and `h⁻¹ℤ_ℓ ≅ ℤ_ℓ` because both are free on a global section
(`Weil.isIso_constantSystemToInverseImageLevel`).

The components are returned as a finite family `Y : ι → B.Scheme` with `ι : Type u`; their
properness is a family of proofs `hg`, used as instances in the statement.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, IV.1.
* [Stacks Project, Tag 03V0](https://stacks.math.columbia.edu/tag/03V0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.SmallEtale
  Stacks.EtaleCohomology

universe v u' w u

namespace Weil

/-! ### Sheaves free on a section -/

section Free

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} {R : Type} [CommRing R]

/-- A morphism between sheaves free on sections which sends one section to the other is an
isomorphism. -/
theorem isIso_of_isFreeOnSection_of_isFreeOnSection {T : C} {G G' : Sheaf J (ModuleCat.{w} R)}
    {g : (G.obj.obj (op T) : Type w)} {g' : (G'.obj.obj (op T) : Type w)}
    (hG : IsFreeOnSection J R G g) (hG' : IsFreeOnSection J R G' g') (φ : G ⟶ G')
    (hφ : ConcreteCategory.hom (φ.hom.app (op T)) g = g') : IsIso φ := by
  obtain ⟨ψ, hψ⟩ := hG'.exists_eq g
  refine ⟨ψ, hG.ext _ _ ?_, hG'.ext _ _ ?_⟩
  · change ConcreteCategory.hom (ψ.hom.app (op T)) (ConcreteCategory.hom (φ.hom.app (op T)) g) = g
    rw [hφ, hψ]
  · change ConcreteCategory.hom (φ.hom.app (op T)) (ConcreteCategory.hom (ψ.hom.app (op T)) g') = g'
    rw [hψ, hφ]

/-- Freeness on a section is transported along an isomorphism `a : T' ⟶ T` of objects. -/
theorem IsFreeOnSection.map {T T' : C} {G : Sheaf J (ModuleCat.{w} R)}
    {g : (G.obj.obj (op T) : Type w)} (hG : IsFreeOnSection J R G g) (a : T' ⟶ T) [IsIso a] :
    IsFreeOnSection J R G (ConcreteCategory.hom (G.obj.map a.op) g) where
  ext {H} f₁ f₂ h := by
    apply hG.ext
    have e₁ := NatTrans.naturality_apply f₁.hom a.op g
    have e₂ := NatTrans.naturality_apply f₂.hom a.op g
    rw [e₁, e₂] at h
    have hinj : Function.Injective (ConcreteCategory.hom (H.obj.map a.op)) :=
      (ConcreteCategory.bijective_of_isIso (H.obj.map a.op)).1
    exact hinj h
  exists_eq {H} s := by
    obtain ⟨f, hf⟩ := hG.exists_eq (ConcreteCategory.hom (H.obj.map (inv a).op) s)
    refine ⟨f, ?_⟩
    rw [NatTrans.naturality_apply f.hom a.op g, hf, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp, ← op_comp, IsIso.hom_inv_id, op_id, CategoryTheory.Functor.map_id]
    rfl

end Free

/-! ### The inverse image of the constant ℓ-adic sheaf -/

section InverseImage

variable {B : BigEtaleSite.{u}} {X X' : B.Scheme} (h : X' ⟶ X) {ℓ : ℕ} [Fact ℓ.Prime]

omit [Fact ℓ.Prime] in
/-- **The pullback of a sheaf free on a section `g` over `T` is free on the image of `g`** over
the base change of `T`: morphisms out of `h⁻¹ G` are morphisms out of `G` into `h_*`, and the
unit of the adjunction carries `g` to the corresponding section. -/
theorem isFreeOnSection_levelPullback (n : ℕ) {G : FiniteLevelSheaf.{u, u + 1} B X ℓ n}
    {T : SmallEtale B X.1 X.property} {g : (G.obj.obj (op T) : Type (u + 1))}
    (hG : IsFreeOnSection (SmallEtale.topology B X.1 X.property) (ZMod (ℓ ^ (n + 1))) G g) :
    IsFreeOnSection (T := (smallEtaleBaseChange B h).obj T)
      (SmallEtale.topology B X'.1 X'.property) (ZMod (ℓ ^ (n + 1)))
      ((LAdicSheaf.levelPullback h n).obj G)
      (ConcreteCategory.hom (((LAdicSheaf.levelAdjunction h n).unit.app G).hom.app (op T)) g) where
  ext {H} f₁ f₂ hf := by
    apply ((LAdicSheaf.levelAdjunction h n).homEquiv _ _).injective
    apply hG.ext
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    exact hf
  exists_eq {H} s := by
    obtain ⟨f, hf⟩ := hG.exists_eq (H := (LAdicSheaf.levelPushforward h n).obj H) s
    refine ⟨((LAdicSheaf.levelAdjunction h n).homEquiv _ _).symm f, ?_⟩
    have e := ((LAdicSheaf.levelAdjunction h n).homEquiv _ _).apply_symm_apply f
    rw [Adjunction.homEquiv_unit] at e
    rw [← hf]
    conv_rhs => rw [← e]
    rfl


variable [IsNoetherian X.1] [QuasiSeparatedSpace X.1] [IsNoetherian X'.1] [QuasiSeparatedSpace X'.1]

/-- The final object of the small étale site of `X'` is the base change of that of `X`. -/
def finalIsoSmallEtaleBaseChangeFinal :
    SmallEtale.final B X'.1 X'.property ≅
      (smallEtaleBaseChange B h).obj (SmallEtale.final B X.1 X.property) :=
  (SmallEtale.finalIsTerminal B X'.1 X'.property).uniqueUpToIso
    (isTerminal_smallEtaleBaseChange_final B h)

variable (ℓ) in
/-- The section of `h⁻¹(ℤ/ℓⁿ⁺¹)` over the final object which is the image of the generator. -/
def inverseImageConstantSystemSection (n : ℕ) :
    (((LAdicSheaf.inverseImage h (LAdicSheaf.constantSystem B X ℓ)).level n).obj.obj
      (op (SmallEtale.final B X'.1 X'.property)) : Type (u + 1)) :=
  ConcreteCategory.hom
    (((LAdicSheaf.inverseImage h (LAdicSheaf.constantSystem B X ℓ)).level n).obj.map
      (finalIsoSmallEtaleBaseChangeFinal h).hom.op)
    (ConcreteCategory.hom (((LAdicSheaf.levelAdjunction h n).unit.app
      ((LAdicSheaf.constantSystem B X ℓ).level n)).hom.app (op (SmallEtale.final B X.1 X.property)))
      (moduleShriekConstantGenerator B X (ZMod (ℓ ^ (n + 1))) (SmallEtale.final B X.1 X.property)))

variable (ℓ) in
/-- The level `n` of the comparison `(ℤ/ℓⁿ⁺¹)_{X'} ⟶ h⁻¹(ℤ/ℓⁿ⁺¹)_X`. -/
def constantSystemToInverseImageLevel (n : ℕ) :
    (LAdicSheaf.constantSystem B X' ℓ).level n ⟶
      (LAdicSheaf.inverseImage h (LAdicSheaf.constantSystem B X ℓ)).level n :=
  (moduleShriekConstantSectionEquiv.{u, 0, 0} B X' (ZMod (ℓ ^ (n + 1))) _ _).symm
    (inverseImageConstantSystemSection h ℓ n)

theorem constantSystemToInverseImageLevel_generator (n : ℕ) :
    ConcreteCategory.hom ((constantSystemToInverseImageLevel h ℓ n).hom.app
        (op (SmallEtale.final B X'.1 X'.property)))
      (moduleShriekConstantGenerator B X' (ZMod (ℓ ^ (n + 1))) (SmallEtale.final B X'.1 X'.2)) =
      inverseImageConstantSystemSection h ℓ n :=
  (moduleShriekConstantSectionEquiv_apply B X' (ZMod (ℓ ^ (n + 1)))
    (SmallEtale.final B X'.1 X'.2) _ (constantSystemToInverseImageLevel h ℓ n)).symm.trans
      (Equiv.apply_symm_apply _ _)

theorem isIso_constantSystemToInverseImageLevel (n : ℕ) :
    IsIso (constantSystemToInverseImageLevel h ℓ n) :=
  isIso_of_isFreeOnSection_of_isFreeOnSection
    (isFreeOnSection_moduleShriekConstant_final B X' _)
    ((isFreeOnSection_levelPullback h n
      (isFreeOnSection_moduleShriekConstant_final B X (ZMod (ℓ ^ (n + 1))))).map
        (finalIsoSmallEtaleBaseChangeFinal h).hom)
    _ (constantSystemToInverseImageLevel_generator h n)

omit [QuasiSeparatedSpace X'.1] in
/-- The transition map of `h⁻¹(ℤ_ℓ)` carries the image of the generator at level `n + 1` to the
image of the generator at level `n`. -/
theorem inverseImageTransition_unit_generator (n : ℕ) :
    ConcreteCategory.hom (((LAdicSheaf.inverseImage h (LAdicSheaf.constantSystem B X ℓ)).transition
        n).hom.app (op ((smallEtaleBaseChange B h).obj (SmallEtale.final B X.1 X.property))))
      (ConcreteCategory.hom (((LAdicSheaf.levelAdjunction h (n + 1)).unit.app
        ((LAdicSheaf.constantSystem B X ℓ).level (n + 1))).hom.app
          (op (SmallEtale.final B X.1 X.property)))
        (moduleShriekConstantGenerator B X (ZMod (ℓ ^ (n + 1 + 1)))
          (SmallEtale.final B X.1 X.property))) =
      ConcreteCategory.hom (((LAdicSheaf.levelAdjunction h n).unit.app
        ((LAdicSheaf.constantSystem B X ℓ).level n)).hom.app
          (op (SmallEtale.final B X.1 X.property)))
        (moduleShriekConstantGenerator B X (ZMod (ℓ ^ (n + 1)))
          (SmallEtale.final B X.1 X.property)) := by
  have e := ((LAdicSheaf.levelAdjunction h (n + 1)).homEquiv _ _).apply_symm_apply
    ((LAdicSheaf.constantSystem B X ℓ).transition n ≫
      (LAdicSheaf.levelRestrict X n).map ((LAdicSheaf.levelAdjunction h n).unit.app
        ((LAdicSheaf.constantSystem B X ℓ).level n)) ≫
      (LAdicSheaf.levelPushforwardRestrictIso h n).inv.app _)
  rw [Adjunction.homEquiv_unit] at e
  have e' := ConcreteCategory.congr_hom
    (congrArg (fun φ => φ.hom.app (op (SmallEtale.final B X.1 X.property))) e)
    (moduleShriekConstantGenerator B X (ZMod (ℓ ^ (n + 1 + 1))) (SmallEtale.final B X.1 X.property))
  refine e'.trans ?_
  change ConcreteCategory.hom (((LAdicSheaf.levelAdjunction h n).unit.app
        ((LAdicSheaf.constantSystem B X ℓ).level n)).hom.app
          (op (SmallEtale.final B X.1 X.property)))
      (ConcreteCategory.hom (((LAdicSheaf.shriekConstantTransition B X ℓ
        (SmallEtale.final B X.1 X.property) n).hom.app (op (SmallEtale.final B X.1 X.property))))
        (moduleShriekConstantGenerator B X (ZMod (ℓ ^ (n + 1 + 1)))
          (SmallEtale.final B X.1 X.property))) = _
  rw [LAdicSheaf.shriekConstantTransition_generator]

/-- **The levels of the comparison are compatible with the transition maps.** -/
theorem constantSystemToInverseImageLevel_naturality (n : ℕ) :
    constantSystemToInverseImageLevel h ℓ (n + 1) ≫
        (LAdicSheaf.inverseImage h (LAdicSheaf.constantSystem B X ℓ)).transition n =
      (LAdicSheaf.constantSystem B X' ℓ).transition n ≫
        (sheafCompose (SmallEtale.topology B X'.obj X'.property)
          (ModuleCat.restrictScalars.{u + 1, 0, 0} (finiteLevelRingHom ℓ n))).map
            (constantSystemToInverseImageLevel h ℓ n) := by
  apply (isFreeOnSection_moduleShriekConstant_final B X' (ZMod (ℓ ^ (n + 1 + 1)))).ext
  refine (sheaf_comp_app_apply _ _ _ _).trans ?_
  refine (congrArg _ (constantSystemToInverseImageLevel_generator h (n + 1))).trans ?_
  refine Eq.trans ?_ (sheaf_comp_app_apply _ _ _ _).symm
  refine Eq.trans ?_ (congrArg (ConcreteCategory.hom
    (((sheafCompose (SmallEtale.topology B X'.obj X'.property)
      (ModuleCat.restrictScalars.{u + 1, 0, 0} (finiteLevelRingHom ℓ n))).map
        (constantSystemToInverseImageLevel h ℓ n)).hom.app
          (op (SmallEtale.final B X'.1 X'.2))))
    (LAdicSheaf.shriekConstantTransition_generator B X' ℓ (SmallEtale.final B X'.1 X'.2) n)).symm
  refine Eq.trans ?_ (constantSystemToInverseImageLevel_generator h n).symm
  rw [inverseImageConstantSystemSection, inverseImageConstantSystemSection]
  exact (NatTrans.naturality_apply
    ((LAdicSheaf.inverseImage h (LAdicSheaf.constantSystem B X ℓ)).transition n).hom
    (finalIsoSmallEtaleBaseChangeFinal h).hom.op _).trans
      (congrArg _ (inverseImageTransition_unit_generator h n))

variable (ℓ) in
/-- **The comparison `(ℤ_ℓ)_{X'} ⟶ h⁻¹(ℤ_ℓ)_X`** of the constant ℓ-adic sheaf of `X'` with the
inverse image of that of `X`. -/
def constantSystemToInverseImage :
    LAdicSheaf.constantSystem B X' ℓ ⟶ LAdicSheaf.inverseImage h (LAdicSheaf.constantSystem B X ℓ)
    where
  app n := constantSystemToInverseImageLevel h ℓ n
  naturality n := constantSystemToInverseImageLevel_naturality h n

instance : IsIso (constantSystemToInverseImage h ℓ) :=
  LAdicSheaf.isIso_of_isIso_app B X' _
    (hf := fun n => isIso_constantSystemToInverseImageLevel h n)

end InverseImage

/-! ### The Frobenius on the cohomology of `h⁻¹(ℤ_ℓ)` -/

section Bridge

variable {B : BigEtaleSite.{u}} {k : Type u} [Field k] [Fintype k] {ℓ : ℕ} [Fact ℓ.Prime]
  [Fact (ℓ ≠ ringChar k)]

/-- **The Frobenius on `Hⁱ_c(X'_k̄, h⁻¹ℤ_ℓ ⊗ ℚ_ℓ)`, for any compactification, has the
characteristic polynomial of the Frobenius `F_ν` of `H^ν(X'_k̄, ℚ_ℓ)`** for `X'` proper over
`k`: the cohomology does not depend on the compactification, and `h⁻¹ℤ_ℓ ≅ ℤ_ℓ`. -/
theorem charpoly_frobenius_inverseImage_constantSystem {X X' : B.Scheme} [IsNoetherian X.1]
    [QuasiSeparatedSpace X.1] [IsNoetherian X'.1] [QuasiSeparatedSpace X'.1] (h : X' ⟶ X)
    (g : X'.1 ⟶ Spec (.of k)) [IsProper g] (j : CompactificationOf (Over.mk g)) (ν : ℕ)
    [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X' ℓ g j
      (AlgebraicClosure k) (LAdicSheaf.inverseImage h (LAdicSheaf.constantSystem B X ℓ)) ν)] :
    haveI : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k _⟩
    (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X' ℓ g j (AlgebraicClosure k)
      (ringChar k) (FiniteField.card k (ringChar k)).choose
      (FiniteField.card k (ringChar k)).choose_spec.2
      (LAdicSheaf.inverseImage h (LAdicSheaf.constantSystem B X ℓ)) ν).hom.charpoly =
      (rationalFrobenius B X' g ℓ ν).charpoly := by
  have : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k _⟩
  have hℓ : ℓ ≠ ringChar k := Fact.out
  have := LAdicSheaf.finiteDimensional_rationalGeometricCompactlySupportedCohomology B ℓ
    (AlgebraicClosure k) (ringChar k) _ (FiniteField.card k (ringChar k)).choose_spec.2 hℓ X' g
    (CompactificationOf.ofProper g)
    (LAdicSheaf.inverseImage h (LAdicSheaf.constantSystem B X ℓ)) ν
  have := LAdicSheaf.finiteDimensional_rationalGeometricCompactlySupportedCohomology B ℓ
    (AlgebraicClosure k) (ringChar k) _ (FiniteField.card k (ringChar k)).choose_spec.2 hℓ X' g
    (CompactificationOf.ofProper g) (LAdicSheaf.constantSystem B X' ℓ) ν
  rw [LAdicSheaf.charpoly_rationalGeometricCompactlySupportedFrobenius_eq_of_compactifications B ℓ
    (AlgebraicClosure k) (ringChar k) _ (FiniteField.card k (ringChar k)).choose_spec.2 hℓ X' g j
    (CompactificationOf.ofProper g)]
  exact LAdicSheaf.charpoly_rationalGeometricCompactlySupportedFrobenius_eq_of_isogeny B X' ℓ g
    (CompactificationOf.ofProper g) (AlgebraicClosure k) (ringChar k) _
    (FiniteField.card k (ringChar k)).choose_spec.2 (constantSystemToInverseImage h ℓ)
    (inv (constantSystemToInverseImage h ℓ)) 0 (by simp) (by simp) ν

end Bridge

/-! ### Polynomial lemmas -/

section Poly

open _root_.Polynomial

/-- A polynomial with nonzero constant coefficient is the reverse of its reverse. -/
theorem Polynomial.reverse_reverse_of_coeff_zero_ne_zero {R : Type*} [Semiring R] {p : R[X]}
    (h : p.coeff 0 ≠ 0) : p.reverse.reverse = p := by
  have h0 : p.natTrailingDegree = 0 := natTrailingDegree_eq_zero.2 (Or.inr h)
  ext n
  rw [coeff_reverse, coeff_reverse, reverse_natDegree, h0, Nat.sub_zero, revAt_invol]

/-- The characteristic polynomial of an endomorphism pure of some weight relative to `q > 0`
does not vanish at `0`. -/
theorem coeff_zero_charpoly_ne_zero_of_isCharpolyPureOfWeight {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {q : ℕ} (hq : 0 < q) {ι : K →+* ℂ}
    {w : ℤ} {φ : Module.End K V} (hφ : IsCharpolyPureOfWeight q ι w φ) :
    φ.charpoly.coeff 0 ≠ 0 := by
  intro h0
  have hroot : (φ.charpoly.map ι).IsRoot 0 := by
    rw [IsRoot, Polynomial.eval_map, eval₂_at_zero, h0, map_zero]
  have hn := (hφ 0 hroot).norm_eq
  rw [norm_zero] at hn
  exact (Real.rpow_pos_of_pos (by exact_mod_cast hq) _).ne' hn.symm

/-- If the characteristic polynomial of `φ` is a product of those of endomorphisms pure of weight
`w`, then `φ` is pure of weight `w`. -/
theorem isCharpolyPureOfWeight_of_charpoly_eq_prod {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {q : ℕ} {ι : K →+* ℂ} {w : ℤ} {φ : Module.End K V}
    {α : Type*} (s : Finset α) (V' : α → Type*) [∀ i, AddCommGroup (V' i)]
    [∀ i, Module K (V' i)] [∀ i, FiniteDimensional K (V' i)] (ψ : ∀ i, Module.End K (V' i))
    (h : φ.charpoly = ∏ i ∈ s, (ψ i).charpoly)
    (hψ : ∀ i ∈ s, IsCharpolyPureOfWeight q ι w (ψ i)) : IsCharpolyPureOfWeight q ι w φ := by
  intro z hz
  rw [h, Polynomial.map_prod, IsRoot, eval_prod, Finset.prod_eq_zero_iff] at hz
  obtain ⟨i, hi, hz⟩ := hz
  exact hψ i hi z hz

end Poly

/-! ### The zeta function with a bound on the cohomological degrees -/

section Zeta

variable {B : BigEtaleSite.{u}} {X : B.Scheme} {k : Type u} [Field k] [Fintype k]
  (f : X.1 ⟶ Spec (.of k)) [IsProper f] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ℓ ≠ ringChar k)]

omit [Fintype k] in
/-- The cohomology `H^ν(X_k̄, ℚ_ℓ)` vanishes in large degrees. -/
theorem exists_subsingleton_rationalCohomology [Finite k] :
    ∃ M : ℕ, ∀ ν : ℕ, M < ν → Subsingleton (rationalCohomology B X f ℓ ν) := by
  have := Fintype.ofFinite k
  have := isNoetherian_of_isProper f
  have := quasiSeparatedSpace_of_isProper f
  have : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k _⟩
  have hTF := (LAdicSheaf.traceFormula B X ℓ f (CompactificationOf.ofProper f)
    (AlgebraicClosure k) (ringChar k) (FiniteField.card k (ringChar k)).choose
    (FiniteField.card k (ringChar k)).choose_spec.2 Fact.out
    (LAdicSheaf.constantSystem B X ℓ)).2.1
  by_cases hd : ∃ d : ℕ, topologicalKrullDim X.1 = d
  · obtain ⟨d, hd⟩ := hd
    refine ⟨2 * d, fun ν hν => ?_⟩
    rw [← not_nontrivial_iff_subsingleton]
    intro hn
    obtain ⟨-, d', hd', hle⟩ := hTF ν hn
    have : d = d' := by exact_mod_cast hd.symm.trans hd'
    subst this
    omega
  · refine ⟨0, fun ν _ => ?_⟩
    rw [← not_nontrivial_iff_subsingleton]
    intro hn
    obtain ⟨-, d', hd', -⟩ := hTF ν hn
    exact hd ⟨d', hd'⟩

/-- **The zeta function of a proper scheme with denominators cleared**, the degrees bounded by
any `M` beyond which the cohomology vanishes: `Z_X(t) ∏_{ν even} P_ν(t) = ∏_{ν odd} P_ν(t)`,
the products over `0 ≤ ν ≤ M`. -/
theorem zetaFunction_mul_prod_even_eq_prod_odd_of_subsingleton (M : ℕ)
    (hM : ∀ ν : ℕ, M < ν → Subsingleton (rationalCohomology B X f ℓ ν)) :
    zetaFunction B X ℓ f *
        ∏ ν ∈ (Finset.range (M + 1)).filter Even,
          ((rationalFrobeniusCharpolyReverse B X f ℓ ν : Polynomial ℚ_[ℓ]) : PowerSeries ℚ_[ℓ]) =
      ∏ ν ∈ (Finset.range (M + 1)).filter (¬ Even ·),
        ((rationalFrobeniusCharpolyReverse B X f ℓ ν : Polynomial ℚ_[ℓ]) : PowerSeries ℚ_[ℓ]) := by
  have := isNoetherian_of_isProper f
  have := quasiSeparatedSpace_of_isProper f
  have : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k _⟩
  have hℓ : ℓ ≠ ringChar k := Fact.out
  have hTF := LAdicSheaf.traceFormula B X ℓ f (CompactificationOf.ofProper f) (AlgebraicClosure k)
    (ringChar k) (FiniteField.card k (ringChar k)).choose
    (FiniteField.card k (ringChar k)).choose_spec.2 hℓ (LAdicSheaf.constantSystem B X ℓ)
  have := hTF.1
  have hZ : zetaFunction B X ℓ f =
      ∏ ν ∈ Finset.range (M + 1),
        if Even ν then ((rationalFrobeniusCharpolyReverse B X f ℓ ν : Polynomial ℚ_[ℓ]) :
            PowerSeries ℚ_[ℓ])⁻¹
        else ((rationalFrobeniusCharpolyReverse B X f ℓ ν : Polynomial ℚ_[ℓ]) :
            PowerSeries ℚ_[ℓ]) := by
    rw [zetaFunction_def,
      LAdicSheaf.rationalLFunction_eq_gradedCharSeries_compactSupportFrobenius B X ℓ f
        (CompactificationOf.ofProper f) (AlgebraicClosure k) (ringChar k)
        (FiniteField.card k (ringChar k)).choose
        (FiniteField.card k (ringChar k)).choose_spec.2 hℓ (LAdicSheaf.constantSystem B X ℓ),
      gradedCharSeries_eq_prod _ _ ((Finset.range (M + 1)).map Nat.castEmbedding),
      Finset.prod_map]
    · exact Finset.prod_congr rfl fun ν _ => gradedCharFactor_rationalFrobenius B X f ℓ ν
    · intro i hi
      by_contra hnt
      rw [not_subsingleton_iff_nontrivial] at hnt
      obtain ⟨h0, -⟩ := hTF.2.1 i hnt
      lift i to ℕ using h0
      have hiM : M < i := by
        by_contra hle
        apply hi
        simp only [Finset.mem_map, Finset.mem_range, Nat.castEmbedding_apply, Nat.cast_inj,
          exists_eq_right]
        omega
      exact not_subsingleton_iff_nontrivial.2 hnt (hM i hiM)
  have hc : ∀ ν, PowerSeries.constantCoeff
      ((rationalFrobeniusCharpolyReverse B X f ℓ ν : Polynomial ℚ_[ℓ]) : PowerSeries ℚ_[ℓ]) ≠
        0 := by
    intro ν
    rw [rationalFrobeniusCharpolyReverse, ← charPowerSeries_one_eq_reverse_charpoly_of_free,
      constantCoeff_charPowerSeries _ one_ne_zero]
    exact one_ne_zero
  rw [hZ, Finset.prod_ite, mul_comm, ← mul_assoc, ← Finset.prod_mul_distrib,
    Finset.prod_congr rfl fun ν _ => PowerSeries.mul_inv_cancel _ (hc ν), Finset.prod_const_one,
    one_mul]

end Zeta

/-! ### An open and closed decomposition -/

section Split

variable {B : BigEtaleSite.{u}} {k : Type u} [Field k] [Fintype k] {ℓ : ℕ} [Fact ℓ.Prime]
  [Fact (ℓ ≠ ringChar k)] {W U Z : B.Scheme} (fW : W.1 ⟶ Spec (.of k)) [IsProper fW]
  (jU : U ⟶ W) (iZ : Z ⟶ W) [IsOpenImmersion (B.inclusion.map jU)]
  [IsClosedImmersion (B.inclusion.map jU)] [IsOpenImmersion (B.inclusion.map iZ)]
  [IsClosedImmersion (B.inclusion.map iZ)]

include iZ in
/-- **Purity of `F_ν` passes to an open and closed decomposition `W = U ⊔ Z`.** -/
theorem isCharpolyPureOfWeight_rationalFrobenius_of_openClosed
    (hij : Set.range (B.inclusion.map jU).base = (Set.range (B.inclusion.map iZ).base)ᶜ)
    {q' : ℕ} {ι : ℚ_[ℓ] →+* ℂ} {w : ℤ} (ν : ℕ)
    (hU : IsCharpolyPureOfWeight q' ι w (rationalFrobenius B U (B.inclusion.map jU ≫ fW) ℓ ν))
    (hZ : IsCharpolyPureOfWeight q' ι w (rationalFrobenius B Z (B.inclusion.map iZ ≫ fW) ℓ ν)) :
    IsCharpolyPureOfWeight q' ι w (rationalFrobenius B W fW ℓ ν) := by
  have := isNoetherian_of_isProper fW
  have := quasiSeparatedSpace_of_isProper fW
  have : IsNoetherian U.1 := isNoetherian_of_isProper (B.inclusion.map jU ≫ fW)
  have : QuasiSeparatedSpace U.1 := quasiSeparatedSpace_of_isProper (B.inclusion.map jU ≫ fW)
  have : IsNoetherian Z.1 := isNoetherian_of_isProper (B.inclusion.map iZ ≫ fW)
  have : QuasiSeparatedSpace Z.1 := quasiSeparatedSpace_of_isProper (B.inclusion.map iZ ≫ fW)
  have : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k _⟩
  have hℓ : ℓ ≠ ringChar k := Fact.out
  set e : ℕ := ((FiniteField.card k (ringChar k)).choose : ℕ)
  have hcard : Fintype.card k = ringChar k ^ e := (FiniteField.card k (ringChar k)).choose_spec.2
  set j := CompactificationOf.ofProper fW
  set F := LAdicSheaf.constantSystem B W ℓ
  set FU := LAdicSheaf.inverseImage jU F
  set FZ := LAdicSheaf.inverseImage iZ F
  have hfinU := LAdicSheaf.finiteCompactSupportCohomologyInput B ℓ k (AlgebraicClosure k)
    (ringChar k) e hcard hℓ U (B.inclusion.map jU ≫ fW) (j.restrictOpen (B.inclusion.map jU)) FU ν
  have := hfinU.1
  have := (LAdicSheaf.finiteCompactSupportCohomologyInput B ℓ k (AlgebraicClosure k)
    (ringChar k) e hcard hℓ Z (B.inclusion.map iZ ≫ fW) (j.restrictClosed (B.inclusion.map iZ))
    FZ ν).1
  have := LAdicSheaf.finiteDimensional_rationalGeometricCompactlySupportedCohomology B ℓ
    (AlgebraicClosure k) (ringChar k) e hcard hℓ W fW j F ν
  have hU' : IsCharpolyPureOfWeight q' ι w
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B U ℓ (B.inclusion.map jU ≫ fW)
        (j.restrictOpen (B.inclusion.map jU)) (AlgebraicClosure k) (ringChar k) e hcard FU
          ν).hom := by
    unfold IsCharpolyPureOfWeight at hU ⊢
    rwa [charpoly_frobenius_inverseImage_constantSystem]
  have hZ' : IsCharpolyPureOfWeight q' ι w
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B Z ℓ (B.inclusion.map iZ ≫ fW)
        (j.restrictClosed (B.inclusion.map iZ)) (AlgebraicClosure k) (ringChar k) e hcard FZ
          ν).hom := by
    unfold IsCharpolyPureOfWeight at hZ ⊢
    rwa [charpoly_frobenius_inverseImage_constantSystem]
  exact LAdicSheaf.isCharpolyPureOfWeight_rationalGeometricCompactlySupportedFrobenius_of_openClosed
    B ℓ fW j (AlgebraicClosure k) (ringChar k) e hcard F ν jU iZ hij FU FZ
    (LAdicSheaf.padicTowerInverseImageIso B ℓ jU F) (LAdicSheaf.padicTowerInverseImageIso B ℓ iZ F)
    hfinU.2 hU' hZ'

omit [Fintype k] [Fact (ℓ ≠ ringChar k)] [IsProper fW] in
/-- The zeta function in `ℚ_ℓ⟦T⟧` is the image of the zeta series in `ℚ⟦T⟧`. -/
theorem zetaFunction_eq_map_zetaSeries [Finite k] {X : B.Scheme} (f : X.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [QuasiSeparatedSpace X.1] :
    zetaFunction B X ℓ f = PowerSeries.map (algebraMap ℚ ℚ_[ℓ]) (zetaSeries f) := by
  have := isNoetherian_of_finiteType f
  rw [zetaFunction_def, rationalLFunction_constantSystem, zetaSeries_eq_constantLFunction,
    map_constantLFunction]

include iZ in
omit [Fintype k] [Fact (ℓ ≠ ringChar k)] in
/-- **The zeta function of `W = U ⊔ Z` is the product of those of `U` and `Z`**: the point
counts add up. -/
theorem zetaFunction_eq_mul_of_openClosed [Finite k]
    (hij : Set.range (B.inclusion.map jU).base = (Set.range (B.inclusion.map iZ).base)ᶜ) :
    zetaFunction B W ℓ fW =
      zetaFunction B U ℓ (B.inclusion.map jU ≫ fW) *
        zetaFunction B Z ℓ (B.inclusion.map iZ ≫ fW) := by
  have := quasiSeparatedSpace_of_isProper fW
  have : QuasiSeparatedSpace U.1 := quasiSeparatedSpace_of_isProper (B.inclusion.map jU ≫ fW)
  have : QuasiSeparatedSpace Z.1 := quasiSeparatedSpace_of_isProper (B.inclusion.map iZ ≫ fW)
  let Y : Bool → Scheme.{u} := fun b => Bool.rec (motive := fun _ => Scheme.{u}) Z.1 U.1 b
  let g : ∀ b, Y b ⟶ W.1 := fun b => Bool.rec (motive := fun b => Y b ⟶ W.1)
    (B.inclusion.map iZ) (B.inclusion.map jU) b
  have : ∀ b, IsPreimmersion (g b) := fun b => by
    cases b
    · exact inferInstanceAs (IsPreimmersion (B.inclusion.map iZ))
    · exact inferInstanceAs (IsPreimmersion (B.inclusion.map jU))
  have hdisj : Pairwise fun a b => Disjoint (Set.range (g a)) (Set.range (g b)) := by
    intro a b hab
    cases a <;> cases b
    · exact absurd rfl hab
    · change Disjoint (Set.range (B.inclusion.map iZ).base) (Set.range (B.inclusion.map jU).base)
      rw [hij]; exact disjoint_compl_right
    · change Disjoint (Set.range (B.inclusion.map jU).base) (Set.range (B.inclusion.map iZ).base)
      rw [hij]; exact disjoint_compl_left
    · exact absurd rfl hab
  have hcover : ∀ x : W.1, ∃ b, x ∈ Set.range (g b) := by
    intro x
    by_cases hx : x ∈ Set.range (B.inclusion.map iZ).base
    · exact ⟨false, hx⟩
    · refine ⟨true, ?_⟩
      change x ∈ Set.range (B.inclusion.map jU).base
      rw [hij]; exact hx
  have hz := zetaSeries_eq_prod_of_pointCountOfDegree_eq_sum fW Finset.univ
    (fun b => g b ≫ fW) (fun n _ => pointCountOfDegree_eq_sum_of_isPreimmersion fW g hdisj hcover n)
  rw [Fintype.prod_bool] at hz
  rw [zetaFunction_eq_map_zetaSeries, zetaFunction_eq_map_zetaSeries,
    zetaFunction_eq_map_zetaSeries, hz, map_mul]

include iZ in
/-- **The reverse characteristic polynomials over an open and closed decomposition.** If the
Frobenius of `U` and of `Z` are pure of weight `ν` in every degree `ν` along `ι`, then
`det(1 - t F_ν | H^ν(W)) = det(1 - t F_ν | H^ν(U)) det(1 - t F_ν | H^ν(Z))`. The zeta functions
multiply, and the weights separate the degrees. -/
theorem rationalFrobeniusCharpolyReverse_eq_mul_of_openClosed
    (hij : Set.range (B.inclusion.map jU).base = (Set.range (B.inclusion.map iZ).base)ᶜ)
    (ι : ℚ_[ℓ] →+* ℂ)
    (hU : ∀ ν : ℕ, IsCharpolyPureOfWeight (Fintype.card k) ι ν
      (rationalFrobenius B U (B.inclusion.map jU ≫ fW) ℓ ν))
    (hZ : ∀ ν : ℕ, IsCharpolyPureOfWeight (Fintype.card k) ι ν
      (rationalFrobenius B Z (B.inclusion.map iZ ≫ fW) ℓ ν)) (ν : ℕ) :
    rationalFrobeniusCharpolyReverse B W fW ℓ ν =
      rationalFrobeniusCharpolyReverse B U (B.inclusion.map jU ≫ fW) ℓ ν *
        rationalFrobeniusCharpolyReverse B Z (B.inclusion.map iZ ≫ fW) ℓ ν := by
  classical
  have hW : ∀ ν : ℕ, IsCharpolyPureOfWeight (Fintype.card k) ι ν
      (rationalFrobenius B W fW ℓ ν) := fun ν =>
    isCharpolyPureOfWeight_rationalFrobenius_of_openClosed fW jU iZ hij ν (hU ν) (hZ ν)
  set gU := B.inclusion.map jU ≫ fW
  set gZ := B.inclusion.map iZ ≫ fW
  set PW := fun ν => rationalFrobeniusCharpolyReverse B W fW ℓ ν
  set PU := fun ν => rationalFrobeniusCharpolyReverse B U gU ℓ ν
  set PZ := fun ν => rationalFrobeniusCharpolyReverse B Z gZ ℓ ν
  obtain ⟨MW, hMW⟩ := exists_subsingleton_rationalCohomology (B := B) fW (ℓ := ℓ)
  obtain ⟨MU, hMU⟩ := exists_subsingleton_rationalCohomology (B := B) gU (ℓ := ℓ)
  obtain ⟨MZ, hMZ⟩ := exists_subsingleton_rationalCohomology (B := B) gZ (ℓ := ℓ)
  set M := max MW (max MU MZ)
  have hW' : ∀ ν, M < ν → Subsingleton (rationalCohomology B W fW ℓ ν) := fun ν hν =>
    hMW ν (lt_of_le_of_lt (le_max_left _ _) hν)
  have hU' : ∀ ν, M < ν → Subsingleton (rationalCohomology B U gU ℓ ν) := fun ν hν =>
    hMU ν (lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hν)
  have hZ' : ∀ ν, M < ν → Subsingleton (rationalCohomology B Z gZ ℓ ν) := fun ν hν =>
    hMZ ν (lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hν)
  -- large degrees
  by_cases hν : M < ν
  · have := hW' ν hν
    have := hU' ν hν
    have := hZ' ν hν
    simp only [rationalFrobeniusCharpolyReverse, reverse_charpoly_eq_one_of_subsingleton, mul_one]
  rw [not_lt] at hν
  -- the zeta functions
  set r := Finset.range (M + 1)
  have eW := zetaFunction_mul_prod_even_eq_prod_odd_of_subsingleton fW M hW'
  have eU := zetaFunction_mul_prod_even_eq_prod_odd_of_subsingleton gU M hU'
  have eZ := zetaFunction_mul_prod_even_eq_prod_odd_of_subsingleton gZ M hZ'
  have eS := zetaFunction_eq_mul_of_openClosed (ℓ := ℓ) fW jU iZ hij
  have hcoe : ∀ G : ℕ → Polynomial ℚ_[ℓ], ∀ t : Finset ℕ,
      ((∏ i ∈ t, G i : Polynomial ℚ_[ℓ]) : PowerSeries ℚ_[ℓ]) =
        ∏ i ∈ t, ((G i : Polynomial ℚ_[ℓ]) : PowerSeries ℚ_[ℓ]) := fun G t =>
    map_prod Polynomial.coeToPowerSeries.ringHom G t
  have key : (∏ ν ∈ r.filter (¬ Even ·), PW ν) * ((∏ ν ∈ r.filter Even, PU ν) *
      ∏ ν ∈ r.filter Even, PZ ν) =
      (∏ ν ∈ r.filter Even, PW ν) * ((∏ ν ∈ r.filter (¬ Even ·), PU ν) *
        ∏ ν ∈ r.filter (¬ Even ·), PZ ν) := by
    rw [← Polynomial.coe_inj]
    simp only [Polynomial.coe_mul, hcoe]
    rw [← eW, ← eU, ← eZ, eS]
    ring
  -- separation by weights in `ℂ`
  set s : Finset ℤ := r.map Nat.castEmbedding
  set P : ℤ → Polynomial ℂ := fun i => (PW i.toNat).map ι
  set Q : ℤ → Polynomial ℂ := fun i => (PU i.toNat * PZ i.toNat).map ι
  have hsplit : ∀ A A' : ℕ → Polynomial ℂ,
      ∏ i ∈ s, (if Even i then A i.toNat else A' i.toNat) =
        (∏ ν ∈ r.filter Even, A ν) * ∏ ν ∈ r.filter (¬ Even ·), A' ν := by
    intro A A'
    rw [Finset.prod_map, ← Finset.prod_ite]
    refine Finset.prod_congr rfl fun ν _ => ?_
    simp only [Nat.castEmbedding_apply, Int.toNat_natCast, Int.even_coe_nat]
  have hq : 1 < Fintype.card k := Fintype.one_lt_card
  have hne : ∀ φ : Polynomial ℚ_[ℓ], φ.coeff 0 = 1 → φ.map ι ≠ 0 := fun φ hφ h0 => by
    have := congrArg (fun F => F.coeff 0) h0
    simp [Polynomial.coeff_map, hφ] at this
  have h1W : ∀ ν, (PW ν).coeff 0 = 1 := fun ν => coeff_zero_reverse_charpoly _
  have h1U : ∀ ν, (PU ν).coeff 0 = 1 := fun ν => coeff_zero_reverse_charpoly _
  have h1Z : ∀ ν, (PZ ν).coeff 0 = 1 := fun ν => coeff_zero_reverse_charpoly _
  have hmem : ∀ i ∈ s, ∃ ν : ℕ, i = ν := fun i hi => by
    obtain ⟨ν, -, rfl⟩ := Finset.mem_map.1 hi
    exact ⟨ν, rfl⟩
  have hsep := Weil.Polynomial.eq_of_alternating_prod_eq (s := s) P Q
    (fun w : ℤ => (((Fintype.card k : ℕ) : ℝ) ^ ((w : ℝ) / 2))⁻¹)
    ((injective_inv_rpow_half hq).injOn)
    (fun i _ => by simp only [P, Polynomial.coeff_map, h1W, map_one])
    (fun i _ => by simp only [Q, Polynomial.coeff_map, Polynomial.mul_coeff_zero, h1U, h1Z,
      mul_one, map_one])
    (fun i hi z hz => by
      obtain ⟨ν, rfl⟩ := hmem i hi
      simp only [P, Int.toNat_natCast] at hz
      exact norm_eq_of_mem_roots_map_reverse_charpoly (hW ν) hz)
    (fun i hi z hz => by
      obtain ⟨ν, rfl⟩ := hmem i hi
      simp only [Q, Int.toNat_natCast, Polynomial.map_mul] at hz
      rw [Polynomial.roots_mul (mul_ne_zero (hne _ (h1U ν)) (hne _ (h1Z ν))),
        Multiset.mem_add] at hz
      rcases hz with hz | hz
      · exact norm_eq_of_mem_roots_map_reverse_charpoly (hU ν) hz
      · exact norm_eq_of_mem_roots_map_reverse_charpoly (hZ ν) hz)
    (by
      rw [hsplit (fun ν => (PU ν * PZ ν).map ι) (fun ν => (PW ν).map ι),
        hsplit (fun ν => (PW ν).map ι) (fun ν => (PU ν * PZ ν).map ι)]
      have := congrArg (Polynomial.map ι) key
      simp only [Polynomial.map_mul, Polynomial.map_prod] at this
      simp only [Polynomial.map_mul, Finset.prod_mul_distrib]
      rw [mul_comm, this])
  have hνs : (ν : ℤ) ∈ s := Finset.mem_map_of_mem _ (Finset.mem_range.2 (Nat.lt_succ_of_le hν))
  have := hsep ν hνs
  simp only [P, Q, Int.toNat_natCast] at this
  exact Polynomial.map_injective ι ι.injective this

include iZ in
/-- **The characteristic polynomials over an open and closed decomposition `W = U ⊔ Z`**: if the
Frobenius of `U` and of `Z` are pure of weight `ν` in every degree `ν` along some `ι`, then
`det(T - F_ν | H^ν(W)) = det(T - F_ν | H^ν(U)) det(T - F_ν | H^ν(Z))`. -/
theorem charpoly_rationalFrobenius_eq_mul_of_openClosed
    (hij : Set.range (B.inclusion.map jU).base = (Set.range (B.inclusion.map iZ).base)ᶜ)
    (ι : ℚ_[ℓ] →+* ℂ)
    (hU : ∀ ν : ℕ, IsCharpolyPureOfWeight (Fintype.card k) ι ν
      (rationalFrobenius B U (B.inclusion.map jU ≫ fW) ℓ ν))
    (hZ : ∀ ν : ℕ, IsCharpolyPureOfWeight (Fintype.card k) ι ν
      (rationalFrobenius B Z (B.inclusion.map iZ ≫ fW) ℓ ν)) (ν : ℕ) :
    (rationalFrobenius B W fW ℓ ν).charpoly =
      (rationalFrobenius B U (B.inclusion.map jU ≫ fW) ℓ ν).charpoly *
        (rationalFrobenius B Z (B.inclusion.map iZ ≫ fW) ℓ ν).charpoly := by
  have hq : 0 < Fintype.card k := Fintype.card_pos
  have hW := isCharpolyPureOfWeight_rationalFrobenius_of_openClosed fW jU iZ hij ν (hU ν) (hZ ν)
  have h := rationalFrobeniusCharpolyReverse_eq_mul_of_openClosed fW jU iZ hij ι hU hZ ν
  simp only [rationalFrobeniusCharpolyReverse] at h
  have h0U := coeff_zero_charpoly_ne_zero_of_isCharpolyPureOfWeight hq (hU ν)
  have h0Z := coeff_zero_charpoly_ne_zero_of_isCharpolyPureOfWeight hq (hZ ν)
  rw [← Polynomial.reverse_mul_of_domain] at h
  rw [← Polynomial.reverse_reverse_of_coeff_zero_ne_zero
      (coeff_zero_charpoly_ne_zero_of_isCharpolyPureOfWeight hq hW), h,
    Polynomial.reverse_reverse_of_coeff_zero_ne_zero (by
      rw [Polynomial.mul_coeff_zero]; exact mul_ne_zero h0U h0Z)]

end Split

/-! ### The decomposition into connected components -/

section Components

variable {B : BigEtaleSite.{u}} {k : Type u} [Field k] [Fintype k] {ℓ : ℕ} [Fact ℓ.Prime]
  [Fact (ℓ ≠ ringChar k)]

/-- On the zero space the characteristic polynomial is `1`. -/
theorem charpoly_eq_one_of_subsingleton {K : Type*} [Field K] {V : Type*} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Subsingleton V] (φ : Module.End K V) :
    φ.charpoly = 1 :=
  Polynomial.eq_one_of_monic_natDegree_zero (LinearMap.charpoly_monic _) (by
    rw [LinearMap.charpoly_natDegree, Module.finrank_zero_of_subsingleton])

omit [Fintype k] in
/-- The cohomology of the empty scheme vanishes. -/
theorem subsingleton_rationalCohomology_of_isEmpty [Finite k] {X : B.Scheme} (hX : IsEmpty X.1)
    (f : X.1 ⟶ Spec (.of k)) [IsProper f] (ν : ℕ) :
    Subsingleton (rationalCohomology B X f ℓ ν) := by
  have := Fintype.ofFinite k
  have hN : IsNoetherian X.1 := isNoetherian_of_isProper f
  have : CompactSpace X.1 := hN.toCompactSpace
  have := quasiSeparatedSpace_of_isProper f
  have : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k _⟩
  have hTF := (LAdicSheaf.traceFormula B X ℓ f (CompactificationOf.ofProper f)
    (AlgebraicClosure k) (ringChar k) (FiniteField.card k (ringChar k)).choose
    (FiniteField.card k (ringChar k)).choose_spec.2 Fact.out
    (LAdicSheaf.constantSystem B X ℓ)).2.1
  rw [← not_nontrivial_iff_subsingleton]
  intro hn
  obtain ⟨-, d, hd, -⟩ := hTF ν hn
  have : IsEmpty (TopologicalSpace.IrreducibleCloseds X.1) :=
    ⟨fun s => (s.isIrreducible.nonempty).elim fun x _ => hX.elim x⟩
  rw [topologicalKrullDim, Order.krullDim_eq_bot] at hd
  exact WithBot.bot_ne_coe hd

variable (B) in
/-- **The Frobenius characteristic polynomials of the open and closed subschemes of `S`**, by
noetherian induction on their images: each is empty, connected, or the disjoint union of two
smaller open and closed subschemes. -/
theorem exists_charpoly_eq_prod_of_isOpenImmersion_of_isClosedImmersion (S : B.Scheme)
    (f : S.1 ⟶ Spec (.of k)) [IsProper f] (n : ℕ) [SmoothOfRelativeDimension n f]
    (hpure : ∀ (Y : B.Scheme) (g : Y.1 ⟶ Spec (.of k)) [IsProper g] [Smooth g]
      [ConnectedSpace Y.1] (ν : ℕ) (ι : ℚ_[ℓ] →+* ℂ),
      IsCharpolyPureOfWeight (Fintype.card k) ι ν (rationalFrobenius B Y g ℓ ν))
    (V : TopologicalSpace.Closeds S.1) :
    ∀ (W : B.Scheme) (c : W ⟶ S) [IsOpenImmersion (B.inclusion.map c)]
      [IsClosedImmersion (B.inclusion.map c)], Set.range (B.inclusion.map c).base = (V : Set S.1) →
      ∀ (gW : W.1 ⟶ Spec (.of k)) [IsProper gW], gW = B.inclusion.map c ≫ f →
      ∃ (ι : Type u) (_ : Fintype ι) (Y : ι → B.Scheme) (g : ∀ i, (Y i).1 ⟶ Spec (.of k))
        (hg : ∀ i, IsProper (g i)),
        (∀ i, SmoothOfRelativeDimension n (g i)) ∧ (∀ i, ConnectedSpace (Y i).1) ∧
        ∀ ν : ℕ, (rationalFrobenius B W gW ℓ ν).charpoly =
          ∏ i, haveI := hg i; (rationalFrobenius B (Y i) (g i) ℓ ν).charpoly := by
  have := isNoetherian_of_isProper f
  induction V using WellFoundedLT.induction with
  | ind V ih =>
  intro W c _ _ hV gW _ hgW
  have : IsNoetherian W.1 := isNoetherian_of_isProper gW
  have hsmooth : SmoothOfRelativeDimension n gW := by
    have h0 := smoothOfRelativeDimension_comp (n := 0) (m := n) (B.inclusion.map c) f
    rw [Nat.zero_add] at h0
    rw [hgW]
    exact h0
  rcases isEmpty_or_nonempty W.1 with hWe | hWne
  · -- the empty scheme: the empty family
    refine ⟨PEmpty, inferInstance, PEmpty.elim, fun i => PEmpty.elim i, fun i => PEmpty.elim i,
      fun i => PEmpty.elim i, fun i => PEmpty.elim i, fun ν => ?_⟩
    have := subsingleton_rationalCohomology_of_isEmpty (B := B) hWe gW (ℓ := ℓ) ν
    rw [charpoly_eq_one_of_subsingleton, Finset.univ_eq_empty, Finset.prod_empty]
  by_cases hWc : ConnectedSpace W.1
  · -- a connected scheme: the family `{W}`
    refine ⟨PUnit, inferInstance, fun _ => W, fun _ => gW, fun _ => inferInstance,
      fun _ => hsmooth, fun _ => hWc, fun ν => ?_⟩
    rw [Fintype.prod_unique]
  -- a disconnected scheme: split along a proper nonempty open and closed subset
  obtain ⟨A, hA, hA0, hA1⟩ : ∃ A : Set W.1, IsClopen A ∧ A ≠ ∅ ∧ A ≠ Set.univ := by
    by_contra hcon
    push Not at hcon
    exact hWc (connectedSpace_iff_clopen.2 ⟨hWne, fun A hA => by
      by_cases h0 : A = ∅
      · exact Or.inl h0
      · exact Or.inr (hcon A hA (Set.nonempty_iff_ne_empty.2 h0))⟩)
  let VU : W.1.Opens := ⟨A, hA.isOpen⟩
  let VZ : W.1.Opens := ⟨Aᶜ, hA.isClosed.isOpen_compl⟩
  let U : B.Scheme := B.obj (VU : Scheme.{u})
    (Scheme.size_lt_of_mono_of_isStrongPrelimit B.cutoff_isStrongPrelimit VU.ι W.property)
  let Z : B.Scheme := B.obj (VZ : Scheme.{u})
    (Scheme.size_lt_of_mono_of_isStrongPrelimit B.cutoff_isStrongPrelimit VZ.ι W.property)
  let jU : U ⟶ W := ObjectProperty.homMk VU.ι
  let iZ : Z ⟶ W := ObjectProperty.homMk VZ.ι
  have : IsOpenImmersion (B.inclusion.map jU) := (inferInstance : IsOpenImmersion VU.ι)
  have : IsOpenImmersion (B.inclusion.map iZ) := (inferInstance : IsOpenImmersion VZ.ι)
  have : IsClosedImmersion (B.inclusion.map jU) :=
    IsClosedImmersion.of_isPreimmersion VU.ι (by rw [Scheme.Opens.range_ι]; exact hA.isClosed)
  have : IsClosedImmersion (B.inclusion.map iZ) :=
    IsClosedImmersion.of_isPreimmersion VZ.ι
      (by rw [Scheme.Opens.range_ι]; exact hA.isOpen.isClosed_compl)
  have hij : Set.range (B.inclusion.map jU).base = (Set.range (B.inclusion.map iZ).base)ᶜ := by
    change Set.range VU.ι = (Set.range VZ.ι)ᶜ
    rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    exact (compl_compl A).symm
  -- the two pieces, as open and closed subschemes of `S`
  have hpiece : ∀ (P : B.Scheme) (jP : P ⟶ W) [IsOpenImmersion (B.inclusion.map jP)]
      [IsClosedImmersion (B.inclusion.map jP)], Set.range (B.inclusion.map jP).base ≠ Set.univ →
      ∃ (ι : Type u) (_ : Fintype ι) (Y : ι → B.Scheme) (g : ∀ i, (Y i).1 ⟶ Spec (.of k))
        (hg : ∀ i, IsProper (g i)),
        (∀ i, SmoothOfRelativeDimension n (g i)) ∧ (∀ i, ConnectedSpace (Y i).1) ∧
        ∀ ν : ℕ, (rationalFrobenius B P (B.inclusion.map jP ≫ gW) ℓ ν).charpoly =
          ∏ i, haveI := hg i; (rationalFrobenius B (Y i) (g i) ℓ ν).charpoly := by
    intro P jP _ _ hP
    have : IsOpenImmersion (B.inclusion.map (jP ≫ c)) :=
      (inferInstance : IsOpenImmersion (B.inclusion.map jP ≫ B.inclusion.map c))
    have : IsClosedImmersion (B.inclusion.map (jP ≫ c)) :=
      (inferInstance : IsClosedImmersion (B.inclusion.map jP ≫ B.inclusion.map c))
    refine ih ⟨Set.range (B.inclusion.map (jP ≫ c)).base,
      (B.inclusion.map (jP ≫ c)).isClosedEmbedding.isClosed_range⟩ ?_ P (jP ≫ c) rfl _ ?_
    · refine lt_of_le_of_ne ?_ ?_
      · change Set.range (B.inclusion.map (jP ≫ c)).base ⊆ (V : Set S.1)
        rw [← hV]
        rintro _ ⟨x, rfl⟩
        exact ⟨(B.inclusion.map jP).base x, rfl⟩
      · intro heq
        apply hP
        have heq' : Set.range (B.inclusion.map (jP ≫ c)).base =
            Set.range (B.inclusion.map c).base :=
          (congrArg (fun T : TopologicalSpace.Closeds S.1 => (T : Set S.1)) heq).trans hV.symm
        refine Set.eq_univ_of_forall fun w => ?_
        obtain ⟨x, hx⟩ : (B.inclusion.map c).base w ∈ Set.range (B.inclusion.map (jP ≫ c)).base :=
          heq' ▸ ⟨w, rfl⟩
        exact ⟨x, (B.inclusion.map c).isOpenEmbedding.injective hx⟩
    · rw [hgW]
      rfl
  have hU0 : Set.range (B.inclusion.map jU).base ≠ Set.univ := by
    change Set.range VU.ι ≠ Set.univ
    rw [Scheme.Opens.range_ι]
    exact hA1
  have hZ0 : Set.range (B.inclusion.map iZ).base ≠ Set.univ := by
    change Set.range VZ.ι ≠ Set.univ
    rw [Scheme.Opens.range_ι]
    intro h
    exact hA0 (Set.compl_univ_iff.1 h)
  obtain ⟨ιU, _, YU, gU, hgU, hsU, hcU, hU⟩ := hpiece U jU hU0
  obtain ⟨ιZ, _, YZ, gZ, hgZ, hsZ, hcZ, hZ⟩ := hpiece Z iZ hZ0
  -- purity of the two pieces
  have hpureFam : ∀ {ι : Type u} [Fintype ι] (Y : ι → B.Scheme) (g : ∀ i, (Y i).1 ⟶ Spec (.of k))
      (hg : ∀ i, IsProper (g i)), (∀ i, SmoothOfRelativeDimension n (g i)) →
      (∀ i, ConnectedSpace (Y i).1) → ∀ (P : B.Scheme) (gP : P.1 ⟶ Spec (.of k)) [IsProper gP],
      (∀ ν : ℕ, (rationalFrobenius B P gP ℓ ν).charpoly =
          ∏ i, haveI := hg i; (rationalFrobenius B (Y i) (g i) ℓ ν).charpoly) →
      ∀ (ι₀ : ℚ_[ℓ] →+* ℂ) (ν : ℕ),
        IsCharpolyPureOfWeight (Fintype.card k) ι₀ ν (rationalFrobenius B P gP ℓ ν) := by
    intro ι _ Y g hg hs hc P gP _ h ι₀ ν
    have := hg
    exact isCharpolyPureOfWeight_of_charpoly_eq_prod Finset.univ
      (fun i => rationalCohomology B (Y i) (g i) ℓ ν) (fun i => rationalFrobenius B (Y i) (g i) ℓ ν)
      (h ν) fun i _ => by
        have := hs i
        have := hc i
        have : Smooth (g i) := SmoothOfRelativeDimension.smooth n (g i)
        exact hpure (Y i) (g i) ν ι₀
  obtain ⟨ι₀⟩ := Padic.nonempty_ringHom_complex ℓ
  have hmul := charpoly_rationalFrobenius_eq_mul_of_openClosed gW jU iZ hij ι₀
    (hpureFam YU gU hgU hsU hcU U _ hU ι₀) (hpureFam YZ gZ hgZ hsZ hcZ Z _ hZ ι₀)
  refine ⟨ιU ⊕ ιZ, inferInstance, Sum.elim YU YZ,
    fun i => Sum.rec (motive := fun i => (Sum.elim YU YZ i).1 ⟶ Spec (.of k)) gU gZ i,
    fun i => Sum.rec (motive := fun i => IsProper
      (Sum.rec (motive := fun i => (Sum.elim YU YZ i).1 ⟶ Spec (.of k)) gU gZ i)) hgU hgZ i,
    fun i => Sum.rec (motive := fun i => SmoothOfRelativeDimension n
      (Sum.rec (motive := fun i => (Sum.elim YU YZ i).1 ⟶ Spec (.of k)) gU gZ i)) hsU hsZ i,
    fun i => Sum.rec (motive := fun i => ConnectedSpace (Sum.elim YU YZ i).1) hcU hcZ i,
    fun ν => ?_⟩
  rw [hmul ν, hU ν, hZ ν, Fintype.prod_sum_type]
  rfl

variable (B) in
/-- **The Frobenius characteristic polynomials of a smooth proper scheme are the products of
those of its connected components.** Let `S` be proper and smooth of relative dimension `n` over
the finite field `k`, and assume Deligne's purity for the connected smooth proper schemes over
`k`. Then there are finitely many connected schemes `Y i`, proper and smooth of relative dimension
`n` over `k` (the connected components of `S`), with
`det(T - F_ν | H^ν(S_k̄, ℚ_ℓ)) = ∏ᵢ det(T - F_ν | H^ν(Y_{i,k̄}, ℚ_ℓ))` for every `ν`. -/
theorem exists_connectedComponents_charpoly_eq_prod (S : B.Scheme) (f : S.1 ⟶ Spec (.of k))
    [IsProper f] (n : ℕ) [SmoothOfRelativeDimension n f]
    (hpure : ∀ (Y : B.Scheme) (g : Y.1 ⟶ Spec (.of k)) [IsProper g] [Smooth g]
      [ConnectedSpace Y.1] (ν : ℕ) (ι : ℚ_[ℓ] →+* ℂ),
      IsCharpolyPureOfWeight (Fintype.card k) ι ν (rationalFrobenius B Y g ℓ ν)) :
    ∃ (ι : Type u) (_ : Fintype ι) (Y : ι → B.Scheme) (g : ∀ i, (Y i).1 ⟶ Spec (.of k))
      (hg : ∀ i, IsProper (g i)),
      (∀ i, SmoothOfRelativeDimension n (g i)) ∧ (∀ i, ConnectedSpace (Y i).1) ∧
      ∀ ν : ℕ, (rationalFrobenius B S f ℓ ν).charpoly =
        ∏ i, haveI := hg i; (rationalFrobenius B (Y i) (g i) ℓ ν).charpoly := by
  have : IsOpenImmersion (B.inclusion.map (𝟙 S)) := by
    rw [CategoryTheory.Functor.map_id]; infer_instance
  have : IsClosedImmersion (B.inclusion.map (𝟙 S)) := by
    rw [CategoryTheory.Functor.map_id]; infer_instance
  exact exists_charpoly_eq_prod_of_isOpenImmersion_of_isClosedImmersion B S f n hpure
    ⟨Set.range (B.inclusion.map (𝟙 S)).base,
      (B.inclusion.map (𝟙 S)).isClosedEmbedding.isClosed_range⟩ S (𝟙 S) rfl f
    (by rw [CategoryTheory.Functor.map_id, Category.id_comp])

end Components

end Weil
