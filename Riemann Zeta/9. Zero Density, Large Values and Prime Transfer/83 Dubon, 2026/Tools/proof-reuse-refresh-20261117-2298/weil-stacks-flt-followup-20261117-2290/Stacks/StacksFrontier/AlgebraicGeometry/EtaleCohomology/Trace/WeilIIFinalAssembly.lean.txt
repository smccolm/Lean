module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIIAssembly
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.WeilIIPurityAssembly
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicUpperVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationLevelPowExact
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportSpecialization
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The assembly of Tag 03VH from named inputs

[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) (Deligne, Weil II): for `ℱ_ρ` with `ρ`
satisfying the conclusions of Deligne's conjecture, the eigenvalues of `π_X^*` on
`Hⁱ_c(X_k̄, ℱ_ρ)` are algebraic numbers of absolute value `q ^ (w / 2)` with `w ∈ ℤ`, `w ≤ i`; and
`w = i` if `X` is smooth and projective.

This file proves 03VH at the hypotheses of the source (`X` proper generalizing projective), as
`Stacks.EtaleCohomology.LAdicSheaf.weightBound_of_inputs`, with extra hypotheses the following
named propositions:

* the weight bound: `Stacks.EtaleCohomology.LaumonFibrePurityInput`,
  `Stacks.EtaleCohomology.LaumonDegenerationFamilyInput` and
  `Stacks.EtaleCohomology.RelativeCurvePurityInput`, through
  `Stacks.EtaleCohomology.LAdicSheaf.isCharpolyMixedOfWeightLE_representationSheaf_of_laumonInputs`;
* purity: Poincaré duality on `X_k̄` (`Stacks.EtaleCohomology.PoincareDualityCore`,
  `Stacks.EtaleCohomology.TopCohomologyPointClass`), the dual coefficients of `ℱ_ρ`
  (`Stacks.EtaleCohomology.LAdicSheaf.RepresentationDualPairingInput`), and two reductions of the
  purity statement: to `X` with a rational point
  (`Stacks.EtaleCohomology.LAdicSheaf.RationalPointPurityReductionInput`) and to `X` geometrically
  connected of pure relative dimension
  (`Stacks.EtaleCohomology.LAdicSheaf.GeometricConnectednessPurityReductionInput`).

## Main definitions

* `Stacks.EtaleCohomology.LAdicSheaf.RepresentationPurityAt`: purity of weight `i` on
  `Hⁱ(X_k̄, ℱ_ρ)` for every `ρ` satisfying the conclusions of Deligne's conjecture.
* `Stacks.EtaleCohomology.LAdicSheaf.GeometricRationalPurity`,
  `Stacks.EtaleCohomology.LAdicSheaf.GeometricPurity`: that statement for `X` geometrically
  connected of pure relative dimension, with resp. without a rational point.
* the named inputs above.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.geometricRationalPurity_of_inputs`.
* `Stacks.EtaleCohomology.LAdicSheaf.weightBound_of_inputs`.

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
  etaleModuleInverseImage_preservesFiniteLimits etaleModuleInverseImage_preservesFiniteColimits
  etaleModuleDirectImage_preservesFiniteColimits_of_universalHomeomorphism

/-- The morphisms of étale presheaves of `Λ`-modules on `S` inverted by sheafification form a
monoidal class. -/
local instance (Λ : Type) [CommRing Λ] (S : Scheme.{u}) :
    (S.smallEtaleTopology.W (A := ModuleCat.{u + 1} Λ)).IsMonoidal :=
  isMonoidal_W_etaleModules (Λ := Λ) S

/-! ### Characteristic roots on a zero space -/

/-- On a zero space every endomorphism is pure of every weight: its characteristic polynomial is
`1`, which has no roots. -/
theorem isCharpolyPureOfWeight_of_subsingleton {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Subsingleton V] (q : ℕ) (ι : K →+* ℂ) (w : ℤ)
    (f : Module.End K V) : IsCharpolyPureOfWeight q ι w f := by
  intro z hz
  have h1 : f.charpoly = 1 := by
    have hdeg : f.charpoly.natDegree = 0 := by
      rw [LinearMap.charpoly_natDegree, Module.finrank_zero_of_subsingleton]
    exact Polynomial.eq_one_of_monic_natDegree_zero (LinearMap.charpoly_monic f) hdeg
  rw [h1, Polynomial.map_one] at hz
  exact absurd hz (by simp)

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

/-- **Finite dimensionality of `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)`**, from
`Stacks.EtaleCohomology.LAdicSheaf.finiteCompactSupportCohomologyInput` (Tag 03V2). -/
@[sga "4½ Rapport 2.10" "special case",
  sga "4½ Rapport 4.11" "special case",
  sga "7 I 0.1.1" "special case",
  sga "7 XXI 2.0" "partial"]
theorem LAdicSheaf.finiteDimensional_rationalGeometricCompactlySupportedCohomology
    {k : Type u} [Field k] [Fintype k] (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)
    (hℓ : ℓ ≠ p) (X : B.Scheme) [IsNoetherian X.1] (f : X.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] (j : CompactificationOf (Over.mk f))
    (F : LAdicSheaf.{u, u + 1} B X ℓ) (i : ℤ) :
    FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i) := by
  have hfin := LAdicSheaf.finiteCompactSupportCohomologyInput B ℓ
  exact (hfin k kbar p q hcard hℓ X f j F i).1

/-- **Independence of the compactification**, from
`Stacks.EtaleCohomology.LAdicSheaf.compactSupportCompactificationIndependenceInput` (Tag 0F7I). -/
theorem LAdicSheaf.charpoly_rationalGeometricCompactlySupportedFrobenius_eq_of_compactifications
    {k : Type u} [Field k] [Fintype k] (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)
    (hℓ : ℓ ≠ p) (X : B.Scheme) [IsNoetherian X.1] (f : X.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (j₁ j₂ : CompactificationOf (Over.mk f)) (F : LAdicSheaf.{u, u + 1} B X ℓ) (i : ℤ)
    [FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j₁ kbar F i)]
    [FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j₂ kbar F i)] :
    (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j₁ kbar p q hcard F
        i).hom.charpoly =
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j₂ kbar p q hcard F
        i).hom.charpoly := by
  have hind := LAdicSheaf.compactSupportCompactificationIndependenceInput B ℓ
  exact hind k kbar p q hcard hℓ X f j₁ j₂ F i

/-! ### The purity statements -/

/-- **Purity on `X`**: for every continuous `ρ : π₁(X, x̄) → GL_r(ℚ_ℓ)` satisfying the conclusions
of Deligne's conjecture along every `ι`, and every `i`, the eigenvalues of the geometric Frobenius
on `Hⁱ(X_k̄, ℱ_ρ ⊗ ℚ_ℓ)` (`X` proper, compactified by itself) are `q`-Weil numbers of weight `i`
along every `ι`. -/
def LAdicSheaf.RepresentationPurityAt (X : B.Scheme) [IsNoetherian X.1] [ConnectedSpace X.1]
    {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    [QuasiCompact f] [IsSeparated f] [IsProper f] (kbar : Type u) [Field kbar] [Algebra k kbar]
    (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q) : Prop :=
  ∀ (x : GeometricPoint X.1) {r : ℕ} (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℚ_[ℓ])
    (hρ : Continuous ρ), (∀ ι : ℚ_[ℓ] →+* ℂ,
      HasDeligneConclusions (geometricFrobeniusFamily f x) p ι ρ) →
    ∀ (i : ℤ) [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology
      B X ℓ f (CompactificationOf.ofProper f) kbar (LAdicSheaf.representationSheaf B X x ρ hρ) i)]
      (ι : ℚ_[ℓ] →+* ℂ),
      IsCharpolyPureOfWeight (p ^ q) ι i
        (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
          (CompactificationOf.ofProper f) kbar p q hcard
          (LAdicSheaf.representationSheaf B X x ρ hρ) i).hom

/-- **Purity for geometrically connected `X` of pure relative dimension with a rational point**:
`Stacks.EtaleCohomology.LAdicSheaf.RepresentationPurityAt` for every `X` connected, proper and
smooth of relative dimension `d` over a finite field `k` with `X_k̄` connected and a `k`-rational
point, `ℓ` different from the characteristic. -/
def LAdicSheaf.GeometricRationalPurity : Prop :=
  ∀ (k : Type u) [Field k] [Fintype k] (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q),
    ℓ ≠ p → ∀ (X : B.Scheme) [IsNoetherian X.1] [ConnectedSpace X.1] (f : X.1 ⟶ Spec (.of k))
      [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [IsProper f] (d : ℕ)
      [SmoothOfRelativeDimension d f] [ConnectedSpace (fieldBaseChange (Over.mk f) kbar)],
      (∃ s : Spec (.of k) ⟶ X.1, s ≫ f = 𝟙 _) →
        LAdicSheaf.RepresentationPurityAt B ℓ X f kbar p q hcard

/-- **Purity for geometrically connected `X` of pure relative dimension**:
`Stacks.EtaleCohomology.LAdicSheaf.GeometricRationalPurity` without the rational point. -/
def LAdicSheaf.GeometricPurity : Prop :=
  ∀ (k : Type u) [Field k] [Fintype k] (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q),
    ℓ ≠ p → ∀ (X : B.Scheme) [IsNoetherian X.1] [ConnectedSpace X.1] (f : X.1 ⟶ Spec (.of k))
      [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [IsProper f] (d : ℕ)
      [SmoothOfRelativeDimension d f] [ConnectedSpace (fieldBaseChange (Over.mk f) kbar)],
      LAdicSheaf.RepresentationPurityAt B ℓ X f kbar p q hcard

/-! ### The named inputs of purity -/

/-- **The reduction of purity to a rational point** (input; the base change to the residue field
`k'` of a closed point of `X`, over which that point is rational: the geometric Frobenius of
`X ×_k k'` is the `[k' : k]`-th power of that of `X`,
`Stacks.EtaleCohomology.LAdicSheaf.rationalFieldExtensionCohomologyIso` and
`Stacks.EtaleCohomology.compactSupportFieldExtensionIso_comm`, and purity of weight `i` for a power
is purity of weight `i`). -/
def LAdicSheaf.RationalPointPurityReductionInput : Prop :=
  LAdicSheaf.GeometricRationalPurity B ℓ → LAdicSheaf.GeometricPurity B ℓ

/-- **The reduction of purity to `X` geometrically connected of pure relative dimension** (input):
for `X` connected, smooth and proper over a finite field, purity holds given it for geometrically
connected `X` of pure relative dimension (`X` is geometrically connected and of pure dimension
over the algebraic closure of `k` in `Γ(X, 𝒪_X)`, and the Frobenius of `k` permutes the
components of `X_k̄` cyclically). -/
def LAdicSheaf.GeometricConnectednessPurityReductionInput : Prop :=
  LAdicSheaf.GeometricPurity B ℓ →
    ∀ (k : Type u) [Field k] [Fintype k] (kbar : Type u) [Field kbar] [Algebra k kbar]
      [IsAlgClosure k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q),
      ℓ ≠ p → ∀ (X : B.Scheme) [IsNoetherian X.1] [ConnectedSpace X.1] (f : X.1 ⟶ Spec (.of k))
        [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [IsProper f] [Smooth f],
        LAdicSheaf.RepresentationPurityAt B ℓ X f kbar p q hcard

/-- **The dual coefficients of `ℱ_ρ`** (input of finite level Poincaré duality for `ℱ_ρ`): for `X`
connected, proper and smooth of relative dimension `d` over a finite field `k` with `X_k̄`
connected, and `ρ` satisfying the conclusions of Deligne's conjecture, there are an ℓ-adic sheaf
`F'` (the sheaf of the contragredient of an integral model of `ρ`) and pairings
`μₙ : (ℱ_ρ)ₙ ⊗ F'ₙ ⟶ ℤ/ℓⁿ⁺¹` such that the levels of `F'` are flat, `RΓ(X_k̄, -)` of the levels
of `ℱ_ρ` and of `F'` are perfect, `F'ₙ|_{X_k̄}` is lisse with flat fibres, the pulled back
pairings are perfect on the geometric fibres, and `F'` is lisse, pointwise `ι`-mixed of weights
`≤ 0` and `ι`-realizable for every `ι`. -/
def LAdicSheaf.RepresentationDualPairingInput : Prop :=
  ∀ (k : Type u) [Field k] [Fintype k] (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] (_ : Fintype.card k = p ^ q),
    ℓ ≠ p → ∀ (X : B.Scheme) [IsNoetherian X.1] [ConnectedSpace X.1] (f : X.1 ⟶ Spec (.of k))
      [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [IsProper f] (d : ℕ)
      [SmoothOfRelativeDimension d f] [ConnectedSpace (fieldBaseChange (Over.mk f) kbar)]
      (x : GeometricPoint X.1) {r : ℕ} (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℚ_[ℓ])
      (hρ : Continuous ρ), (∀ ι : ℚ_[ℓ] →+* ℂ,
        HasDeligneConclusions (geometricFrobeniusFamily f x) p ι ρ) →
      ∃ (F' : LAdicSheaf B X ℓ)
        (μ : ∀ n, (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
            (CompactificationOf.ofProper f).immersion).obj (LAdicSheaf.etaleLevel B X ℓ
              (LAdicSheaf.representationSheaf B X x ρ hρ) n) ⊗
          (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
            (CompactificationOf.ofProper f).immersion).obj (LAdicSheaf.etaleLevel B X ℓ F' n) ⟶
          Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
            X.1.smallEtaleTopology),
        (∀ n, StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
          (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f
            (CompactificationOf.ofProper f) kbar
            (LAdicSheaf.levelComplex B X ℓ (LAdicSheaf.representationSheaf B X x ρ hρ) n)))) ∧
        (∀ n, PowExact ℓ (n + 1) (LAdicSheaf.etaleLevel B X ℓ F' n)) ∧
        (∀ n, StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
          (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f
            (CompactificationOf.ofProper f) kbar (LAdicSheaf.levelComplex B X ℓ F' n)))) ∧
        (∀ n, Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology
          ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
            (fieldBaseChangeProj (Over.mk f) kbar)).obj
            ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
              (CompactificationOf.ofProper f).immersion).obj
                (LAdicSheaf.etaleLevel B X ℓ F' n)))) ∧
        (∀ (n : ℕ) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
          (s : Spec (.of Ω) ⟶ fieldBaseChange (Over.mk f) kbar),
          Module.Flat (ZMod (ℓ ^ (n + 1)))
            ((((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
              (A := ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).obj
              ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
                (fieldBaseChangeProj (Over.mk f) kbar)).obj
                ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
                  (CompactificationOf.ofProper f).immersion).obj
                    (LAdicSheaf.etaleLevel B X ℓ F' n))))) ∧
        (∀ (n : ℕ) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
          (s : Spec (.of Ω) ⟶ fieldBaseChange (Over.mk f) kbar),
          Function.Bijective (TensorProduct.curry (Functor.LaxMonoidal.μ
            (((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
              (A := ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))))
            ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
              (fieldBaseChangeProj (Over.mk f) kbar)).obj
              ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
                (CompactificationOf.ofProper f).immersion).obj (LAdicSheaf.etaleLevel B X ℓ
                  (LAdicSheaf.representationSheaf B X x ρ hρ) n)))
            ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
              (fieldBaseChangeProj (Over.mk f) kbar)).obj
              ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
                (CompactificationOf.ofProper f).immersion).obj
                  (LAdicSheaf.etaleLevel B X ℓ F' n))) ≫
            (((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
              (A := ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).map
              (inverseImageConstantPairing (fieldBaseChangeProj (Over.mk f) kbar) (ℓ ^ (n + 1))
                (μ n))).hom)) ∧
        F'.IsLisse ∧ ∀ ι : ℚ_[ℓ] →+* ℂ,
          LAdicSheaf.IsPointwiseMixedOfWeightLE B X ℓ f F' (p ^ q) ι 0 ∧
          LAdicSheaf.IsIotaRealizable B X ℓ f F' ι

/-! ### Purity at a rational point -/

/-- `ℓ` is invertible in an extension of a field of characteristic `p ≠ ℓ`. -/
theorem isUnit_natCast_of_ne_charP {k : Type u} [Field k] (kbar : Type u) [Field kbar]
    [Algebra k kbar] (p : ℕ) [Fact p.Prime] [CharP k p] (hℓ : ℓ ≠ p) : IsUnit (ℓ : kbar) := by
  have : CharP kbar p := charP_of_injective_algebraMap (algebraMap k kbar).injective p
  refine isUnit_iff_ne_zero.2 fun h => hℓ ?_
  rw [CharP.cast_eq_zero_iff kbar p] at h
  exact ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (Fact.out : ℓ.Prime)).1 h).symm

/-- **Purity for geometrically connected `X` of pure relative dimension with a rational point,
from the named inputs**: the weight bound for `ℱ_ρ` and for the dual coefficients `F'` (from
purity on the Laumon fibres, the Laumon degeneration family and relative purity), finite level
Poincaré duality (from `PoincareDualityCore` and `TopCohomologyPointClass` over `k̄`) and the dual
coefficients. In degrees `i < 0` and `i > 2d` the cohomology vanishes. -/
theorem LAdicSheaf.geometricRationalPurity_of_inputs (h7 : LaumonFibrePurityInput.{u})
    (hfam : LaumonDegenerationFamilyInput.{u})
    (hPur : RelativeCurvePurityInput B ℓ (LAdicSheaf.twistNegOneOp B ℓ))
    (hPD : ∀ (K : Type u) [Field K] [IsAlgClosed K], IsUnit (ℓ : K) → PoincareDualityCore ℓ K)
    (hTop : ∀ (K : Type u) [Field K] [IsAlgClosed K], IsUnit (ℓ : K) →
      TopCohomologyPointClass ℓ K)
    (hcoef : LAdicSheaf.RepresentationDualPairingInput B ℓ) :
    LAdicSheaf.GeometricRationalPurity B ℓ := by
  intro k _ _ kbar _ _ _ p q _ _ hcard hℓ X _ _ f _ _ _ _ d _ _ hpt x r ρ hρ hD i _ ι
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  have hℓu : IsUnit (ℓ : kbar) := isUnit_natCast_of_ne_charP ℓ (k := k) kbar p hℓ
  have : SmoothOfRelativeDimension d (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange d).of_isPullback
      (IsPullback.of_hasPullback (Over.mk f).hom (specAlgebraMap k kbar)) ‹_›
  set F := LAdicSheaf.representationSheaf B X x ρ hρ
  have hzero : IsZero (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
      (CompactificationOf.ofProper f) kbar F i) → IsCharpolyPureOfWeight (p ^ q) ι i
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
        (CompactificationOf.ofProper f) kbar p q hcard F i).hom := fun h => by
    have := ModuleCat.subsingleton_of_isZero h
    exact isCharpolyPureOfWeight_of_subsingleton _ _ _ _
  rcases lt_or_ge i 0 with hneg | hnn
  · exact hzero (LAdicSheaf.isZero_rationalGeometricCompactlySupportedCohomology_of_neg B X ℓ f
      (CompactificationOf.ofProper f) kbar F i hneg)
  rcases lt_or_ge (2 * (d : ℤ)) i with hbig | hle
  · have : Nonempty X.1 := by
      obtain ⟨s, -⟩ := hpt
      exact ⟨s.base (Nonempty.some inferInstance)⟩
    have hdim : topologicalKrullDim X.1 ≤ d :=
      (topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field d f).le
    exact hzero
      (LAdicSheaf.isZero_rationalGeometricCompactlySupportedCohomology_of_two_mul_lt B X ℓ f
        (CompactificationOf.ofProper f) kbar F d hdim i hbig)
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hnn
  have hn : n ≤ 2 * d := by omega
  obtain ⟨F', μ, hP, hF', hP', hlisse, hflat, hμ, hl', hw'⟩ :=
    hcoef k kbar p q hcard hℓ X f d x ρ hρ hD
  have hF : ∀ m, PowExact ℓ (m + 1) (LAdicSheaf.etaleLevel B X ℓ F m) := fun m => by
    have := compactSpace_etaleFundamentalGroup X.1 x
    exact powExact_etaleLevel_representationLAdicSheaf B X x (integralModel ρ hρ)
      (continuous_integralModel ρ hρ) m
  have : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ
      f (CompactificationOf.ofProper f) kbar F' (2 * d - n)) :=
    LAdicSheaf.finiteDimensional_rationalGeometricCompactlySupportedCohomology B ℓ kbar p q hcard
      hℓ X f (CompactificationOf.ofProper f) F' (2 * d - n)
  have hq : 1 ≤ p ^ q := Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  have hwt' : IsCharpolyMixedOfWeightLE (p ^ q) ι (2 * d - n)
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
        (CompactificationOf.ofProper f) kbar p q hcard F' (2 * d - n)).hom := by
    refine isCharpolyMixedOfWeightLE_of_forall_isCharpolyNormMixedOfWeightLE
      (mk_padic_le_mk_complex ℓ) hq (fun ι' => ?_) ι
    have h := LAdicSheaf.satisfiesWeightBound_of_laumonInputs h7 hfam hPur kbar p q hcard hℓ ι' X
      f (CompactificationOf.ofProper f) F' 0 hl' (hw' ι').1 (hw' ι').2 (2 * d - n)
    rwa [zero_add] at h
  exact LAdicSheaf.isCharpolyPureOfWeight_of_rationalPoint B X ℓ f kbar p q hcard d hℓu hpt
    (hPD kbar hℓu) (hTop kbar hℓu) F F' hF hP hF' hP' μ hlisse hflat hμ n hn ι
    (LAdicSheaf.isCharpolyMixedOfWeightLE_representationSheaf_of_laumonInputs h7 hfam hPur hℓ X f
      (CompactificationOf.ofProper f) x ρ hρ hD n ι) hwt'

/-! ### Tag 03VH -/

/-- **[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) from named inputs.**
Let `k` be a finite field with `q = p ^ m` elements, `k̄` an algebraic closure, `ℓ ≠ p` a prime,
`X` connected and separated of finite type over `k` with a compactification `j`, and
`ρ : π₁(X, x̄) → GL_r(ℚ_ℓ)` continuous, satisfying the conclusions of Deligne's conjecture along
every embedding `ι : ℚ_ℓ → ℂ`. Then for every `i` the eigenvalues of `π_X^*` on
`Hⁱ_c(X_k̄, ℱ_ρ ⊗ ℚ_ℓ)` (finite dimensional) are algebraic numbers of absolute value `q ^ (w / 2)`
along `ι` with `w ∈ ℤ`, `w ≤ i`; and if `X` is smooth and proper over `k`, then `w = i`. The
extra hypotheses are named inputs: purity on the Laumon fibres and the Laumon degeneration
family, relative purity, Poincaré duality over `k̄`, the dual coefficients of `ℱ_ρ`, and the two
reductions of purity. -/
theorem LAdicSheaf.weightBound_of_inputs (h7 : LaumonFibrePurityInput.{u})
    (hfam : LaumonDegenerationFamilyInput.{u})
    (hPur : RelativeCurvePurityInput B ℓ (LAdicSheaf.twistNegOneOp B ℓ))
    (hPD : ∀ (K : Type u) [Field K] [IsAlgClosed K], IsUnit (ℓ : K) → PoincareDualityCore ℓ K)
    (hTop : ∀ (K : Type u) [Field K] [IsAlgClosed K], IsUnit (ℓ : K) →
      TopCohomologyPointClass ℓ K)
    (hcoef : LAdicSheaf.RepresentationDualPairingInput B ℓ)
    (hrat : LAdicSheaf.RationalPointPurityReductionInput B ℓ)
    (hconn : LAdicSheaf.GeometricConnectednessPurityReductionInput B ℓ)
    {k : Type u} [Field k] [Fintype k] (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)
    (hℓ : ℓ ≠ p) (X : B.Scheme) [IsNoetherian X.1] [ConnectedSpace X.1] (f : X.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] (j : CompactificationOf (Over.mk f))
    (x : GeometricPoint X.1) {r : ℕ} (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℚ_[ℓ])
    (hρ : Continuous ρ)
    (hD : ∀ ι : ℚ_[ℓ] →+* ℂ, HasDeligneConclusions (geometricFrobeniusFamily f x) p ι ρ) :
    (∀ (i : ℤ) (ι : ℚ_[ℓ] →+* ℂ),
      haveI : FiniteDimensional ℚ_[ℓ]
          (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
            j kbar (LAdicSheaf.representationSheaf B X x ρ hρ) i) :=
        LAdicSheaf.finiteDimensional_rationalGeometricCompactlySupportedCohomology B ℓ kbar p q
          hcard hℓ X f j _ i
      IsCharpolyMixedOfWeightLE (p ^ q) ι i
        (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard
          (LAdicSheaf.representationSheaf B X x ρ hρ) i).hom) ∧
    (IsProper f → Smooth f → ∀ (i : ℤ) (ι : ℚ_[ℓ] →+* ℂ),
      haveI : FiniteDimensional ℚ_[ℓ]
          (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
            j kbar (LAdicSheaf.representationSheaf B X x ρ hρ) i) :=
        LAdicSheaf.finiteDimensional_rationalGeometricCompactlySupportedCohomology B ℓ kbar p q
          hcard hℓ X f j _ i
      IsCharpolyPureOfWeight (p ^ q) ι i
        (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard
          (LAdicSheaf.representationSheaf B X x ρ hρ) i).hom) := by
  have hfd : ∀ (j' : CompactificationOf (Over.mk f)) (i : ℤ), FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j' kbar
        (LAdicSheaf.representationSheaf B X x ρ hρ) i) := fun j' i =>
    LAdicSheaf.finiteDimensional_rationalGeometricCompactlySupportedCohomology B ℓ kbar p q
      hcard hℓ X f j' _ i
  refine ⟨fun i ι => ?_, fun hP hS i ι => ?_⟩
  · exact LAdicSheaf.isCharpolyMixedOfWeightLE_representationSheaf_of_laumonInputs h7 hfam hPur hℓ
      X f j x ρ hρ hD i ι
  · have := hP
    have := hS
    have hpure := hconn (hrat (LAdicSheaf.geometricRationalPurity_of_inputs B ℓ h7 hfam hPur hPD
      hTop hcoef)) k kbar p q hcard hℓ X f x ρ hρ hD i ι
    intro z hz
    rw [LAdicSheaf.charpoly_rationalGeometricCompactlySupportedFrobenius_eq_of_compactifications B
      ℓ kbar p q hcard hℓ X f j (CompactificationOf.ofProper f) _ i] at hz
    exact hpure z hz

end Stacks.EtaleCohomology

end
