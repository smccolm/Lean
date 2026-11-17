module

public import Weil.AlgebraicGeometry.EtaleCohomology.Duality.PoincareDualityFrobenius
public import Weil.AlgebraicGeometry.EtaleCohomology.Duality.RationalPoincareDualityIsogeny
public import Weil.AlgebraicGeometry.EtaleCohomology.Trace.ConstantDegreeZeroCohomology
public import Weil.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafTrivialConstant
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.Trace.RationalCohomologyFrobenius
public import Weil.LinearAlgebra.Charpoly.PointCountPositivity
public import Weil.Attr

/-!
# Poincaré duality and the top degree for `H(X_k̄, ℚ_ℓ)`, without a rational point

Let `X` be proper and smooth of relative dimension `d` over a finite field `k` with `q` elements,
with `X_k̄` connected. This file removes the hypothesis on `H⁰` from the results of
`Weil.AlgebraicGeometry.EtaleCohomology.Duality.TopDegreeFrobenius` and
`Weil.AlgebraicGeometry.EtaleCohomology.Duality.PoincareDualityFrobenius`: the Frobenius is
the identity on the line `H⁰(X_k̄, ℚ_ℓ)`
(`Weil.LAdicSheaf.rationalGeometricCompactlySupportedFrobenius_constant_zero_of_connected`,
`Weil.LAdicSheaf.finrank_rationalGeometricCompactlySupportedCohomology_constant_zero`), and the
constant ℓ-adic sheaf is the sheaf `ℱ_1` of the trivial representation
(`Weil.LAdicSheaf.constantSystemIsoRepresentationSheafOne`). The results are then transported
from `ℱ_1` to the constant ℓ-adic sheaf.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.frobeniusTrivialOnH0FieldExtension`.
* `Stacks.EtaleCohomology.LAdicSheaf.exists_closedPoint_residueDegree_dvd`: `X` has closed points of
  degree dividing every large enough `N`.
* `Stacks.EtaleCohomology.LAdicSheaf.rationalFrobenius_top_constantSystem_eq_smul`: the Frobenius on
  `H^{2d}(X_k̄, ℚ_ℓ)` is multiplication by `q^d`, and `H^{2d}(X_k̄, ℚ_ℓ)` is a line.
* `Stacks.EtaleCohomology.LAdicSheaf.exists_isFrobeniusDuality_constantSystem`: a `q^d`-duality for
  the Frobenius on `Hⁱ(X_k̄, ℚ_ℓ) × H^{2d-i}(X_k̄, ℚ_ℓ)`.

The statements consume objects defined in the standard model `HasDerivedCategory.standard` of the
derived category, which is therefore a local instance here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale
  Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

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
  {k : Type u} [Field k] [Fintype k] (kbar : Type u) [Field kbar] [Algebra k kbar]

omit [Fintype k] in
/-- **The Frobenius is trivial on the line `H⁰(X'_k̄, ℱ_1 ⊗ ℚ_ℓ)`** over every finite extension
`k'` of `k` inside `k̄`, for `X` proper over `k` with `X_k̄` connected. -/
theorem LAdicSheaf.frobeniusTrivialOnH0FieldExtension (p : ℕ) [Fact p.Prime] [CharP k p]
    (X : B.Scheme) (f : X.1 ⟶ Spec (.of k)) [IsProper f]
    [ConnectedSpace (fieldBaseChange (Over.mk f) kbar)] :
    LAdicSheaf.FrobeniusTrivialOnH0FieldExtension B ℓ kbar p X f := by
  intro k' _ _ _ _ _ _ _ q' hcard' _ _ x' h1 _
  have : ConnectedSpace (fieldBaseChange (Over.mk (pullback.snd f (specAlgebraMap k k'))) kbar) :=
    Function.Surjective.connectedSpace
      (Scheme.Hom.surjective (fieldBaseChangeExtensionIso (Over.mk f) k' kbar).inv)
      (Scheme.Hom.continuous _)
  have : QuasiSeparatedSpace (fieldExtensionScheme B X f k').1 :=
    @IsLocallyNoetherian.quasiSeparatedSpace _
      (inferInstance : IsNoetherian (fieldExtensionScheme B X f k').1).toIsLocallyNoetherian
  let I := Weil.LAdicSheaf.constantSystemIsoRepresentationSheafOne (ℓ := ℓ) B
    (fieldExtensionScheme B X f k') x'
  let e := LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsogenyIso B
    (fieldExtensionScheme B X f k') ℓ (pullback.snd f (specAlgebraMap k k'))
    (CompactificationOf.ofProper (pullback.snd f (specAlgebraMap k k'))) kbar I.hom I.inv 0
    (by simp) (by simp) ((0 : ℕ) : ℤ)
  have hC := Weil.LAdicSheaf.rationalGeometricCompactlySupportedFrobenius_constant_zero_of_connected
    B (fieldExtensionScheme B X f k') ℓ (pullback.snd f (specAlgebraMap k k')) kbar p q' hcard'
  change (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B
        (fieldExtensionScheme B X f k') ℓ
        (pullback.snd f (specAlgebraMap k k'))
        (CompactificationOf.ofProper (pullback.snd f (specAlgebraMap k k'))) kbar p q' hcard'
        (LAdicSheaf.representationSheaf B (fieldExtensionScheme B X f k') x' 1 continuous_const)
        ((0 : ℕ) : ℤ)).hom = LinearMap.id ∧
    Module.finrank ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B
      (fieldExtensionScheme B X f k') ℓ (pullback.snd f (specAlgebraMap k k'))
      (CompactificationOf.ofProper (pullback.snd f (specAlgebraMap k k'))) kbar
      (LAdicSheaf.representationSheaf B (fieldExtensionScheme B X f k') x' 1 continuous_const)
      ((0 : ℕ) : ℤ)) = 1
  refine ⟨LinearMap.ext fun v => ?_, ?_⟩
  · obtain ⟨w, rfl⟩ := e.toLinearEquiv.surjective v
    have h := LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsogenyIso_hom_frobenius B
      (fieldExtensionScheme B X f k') ℓ (pullback.snd f (specAlgebraMap k k'))
      (CompactificationOf.ofProper (pullback.snd f (specAlgebraMap k k'))) kbar p q' hcard' I.hom
      I.inv 0 (by simp) (by simp) ((0 : ℕ) : ℤ) w
    rw [hC] at h
    exact h.symm
  · rw [← e.toLinearEquiv.finrank_eq]
    exact Weil.LAdicSheaf.finrank_rationalGeometricCompactlySupportedCohomology_constant_zero B
      (fieldExtensionScheme B X f k') ℓ (pullback.snd f (specAlgebraMap k k')) kbar

variable [IsAlgClosure k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

omit [Fintype k] in
/-- `X` is connected when `X_k̄` is. -/
theorem connectedSpace_of_connectedSpace_fieldBaseChange (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    [ConnectedSpace (fieldBaseChange (Over.mk f) kbar)] : ConnectedSpace X := by
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  have : Surjective (specAlgebraMap k kbar) :=
    ⟨fun y => ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
  exact Function.Surjective.connectedSpace
    (Scheme.Hom.surjective (fieldBaseChangeProj (Over.mk f) kbar)) (Scheme.Hom.continuous _)

include hcard in
/-- **Lang–Weil-lite**: for `X` proper and smooth of relative dimension `d` over `k` with `X_k̄`
connected, `X` has a closed point of degree dividing `N` for every large enough `N`, i.e. points
over every extension of `k` of large enough degree. -/
theorem LAdicSheaf.exists_closedPoint_residueDegree_dvd (hℓ : ℓ ≠ p) (X : B.Scheme)
    (f : X.1 ⟶ Spec (.of k)) [IsProper f] (d : ℕ) [SmoothOfRelativeDimension d f]
    [ConnectedSpace (fieldBaseChange (Over.mk f) kbar)] :
    ∃ N₀, ∀ N ≥ N₀, ∃ y : closedPoints X.1, residueDegree f y.1 ∣ N := by
  have : IsNoetherian X.1 := Weil.isNoetherian_of_isProper f
  have := connectedSpace_of_connectedSpace_fieldBaseChange kbar X.1 f
  exact LAdicSheaf.exists_closedPoint_residueDegree_dvd_of_frobeniusTrivialOnH0 B ℓ kbar p q hcard
    hℓ X f d (LAdicSheaf.frobeniusTrivialOnH0FieldExtension B ℓ kbar p X f)

/-- **The Frobenius on `H^{2d}(X_k̄, ℚ_ℓ)` is multiplication by `q^d`, and `H^{2d}(X_k̄, ℚ_ℓ)` is a
line**, for `X` proper and smooth of relative dimension `d` over `k` with `X_k̄` connected; no
rational point is assumed. -/
theorem LAdicSheaf.rationalFrobenius_top_constantSystem_eq_smul (hℓ : ℓ ≠ p) (X : B.Scheme)
    (f : X.1 ⟶ Spec (.of k)) [IsProper f] (d : ℕ) [SmoothOfRelativeDimension d f]
    [ConnectedSpace (fieldBaseChange (Over.mk f) kbar)] [IsNoetherian X.1]
    [QuasiSeparatedSpace X.1] :
    (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
      (CompactificationOf.ofProper f) kbar p q hcard (LAdicSheaf.constantSystem B X ℓ)
      ((2 * d : ℕ) : ℤ)).hom = (((p ^ q) ^ d : ℕ) : ℚ_[ℓ]) • LinearMap.id ∧
    Module.finrank ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
      (CompactificationOf.ofProper f) kbar (LAdicSheaf.constantSystem B X ℓ)
      ((2 * d : ℕ) : ℤ)) = 1 := by
  have := connectedSpace_of_connectedSpace_fieldBaseChange kbar X.1 f
  have : Nonempty X.1 := ConnectedSpace.toNonempty
  let x : GeometricPoint X.1 := X.1.algClosedPoint (Classical.arbitrary X.1)
  obtain ⟨hF, hrank⟩ := LAdicSheaf.rationalFrobenius_top_representationSheaf_one_eq_smul B ℓ kbar p
    q hcard hℓ X f d (LAdicSheaf.frobeniusTrivialOnH0FieldExtension B ℓ kbar p X f) x
    continuous_const
  let e := LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsogenyIso B X ℓ f
    (CompactificationOf.ofProper f) kbar (Weil.LAdicSheaf.constantSystemIsoRepresentationSheafOne
      B X x).hom (Weil.LAdicSheaf.constantSystemIsoRepresentationSheafOne B X x).inv 0
    (by simp) (by simp) ((2 * d : ℕ) : ℤ)
  refine ⟨LinearMap.ext fun v => e.toLinearEquiv.injective ?_, ?_⟩
  · have h := LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsogenyIso_hom_frobenius B X ℓ
      f (CompactificationOf.ofProper f) kbar p q hcard
      (Weil.LAdicSheaf.constantSystemIsoRepresentationSheafOne B X x).hom
      (Weil.LAdicSheaf.constantSystemIsoRepresentationSheafOne B X x).inv 0 (by simp) (by simp)
      ((2 * d : ℕ) : ℤ) v
    rw [hF] at h
    change e.hom.hom _ = e.hom.hom _
    rw [h]
    simp [e]
  · rw [e.toLinearEquiv.finrank_eq]
    exact hrank

/-- **Poincaré duality with Frobenius on `H(X_k̄, ℚ_ℓ)`, without a rational point.** For `X`
proper and smooth of relative dimension `d` over the finite field `k` with `p ^ q` elements, with
`X_k̄` connected, `ℓ ≠ p` and `0 ≤ i ≤ 2d`, there is a `q^d`-duality for the Frobenius on
`Hⁱ(X_k̄, ℚ_ℓ) × H^{2d-i}(X_k̄, ℚ_ℓ)` (cohomology of the constant ℓ-adic sheaf). -/
theorem LAdicSheaf.exists_isFrobeniusDuality_constantSystem (hℓ : ℓ ≠ p) (X : B.Scheme)
    (f : X.1 ⟶ Spec (.of k)) [IsProper f] (d : ℕ) [SmoothOfRelativeDimension d f]
    [ConnectedSpace (fieldBaseChange (Over.mk f) kbar)] [IsNoetherian X.1]
    [QuasiSeparatedSpace X.1] (i : ℕ) (hi : i ≤ 2 * d) :
    ∃ β : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
          (CompactificationOf.ofProper f) kbar (LAdicSheaf.constantSystem B X ℓ) i →ₗ[ℚ_[ℓ]]
        LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f
          (CompactificationOf.ofProper f) kbar (LAdicSheaf.constantSystem B X ℓ)
          (2 * d - i) →ₗ[ℚ_[ℓ]] ℚ_[ℓ],
      ∃ hc : (((p ^ q) ^ d : ℕ) : ℚ_[ℓ]) ≠ 0,
        β.IsFrobeniusDuality
          (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
            (CompactificationOf.ofProper f) kbar p q hcard (LAdicSheaf.constantSystem B X ℓ) i).hom
          (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f
            (CompactificationOf.ofProper f) kbar p q hcard (LAdicSheaf.constantSystem B X ℓ)
            (2 * d - i)).hom
          (Units.mk0 _ hc) := by
  have := connectedSpace_of_connectedSpace_fieldBaseChange kbar X.1 f
  have : Nonempty X.1 := ConnectedSpace.toNonempty
  let x : GeometricPoint X.1 := X.1.algClosedPoint (Classical.arbitrary X.1)
  obtain ⟨β, hc, hβ⟩ := LAdicSheaf.exists_isFrobeniusDuality_representationSheaf_one B ℓ kbar p q
    hcard hℓ X f d (LAdicSheaf.frobeniusTrivialOnH0FieldExtension B ℓ kbar p X f) x
    continuous_const i hi
  let φ := (Weil.LAdicSheaf.constantSystemIsoRepresentationSheafOne (ℓ := ℓ) B X x).hom
  let ψ := (Weil.LAdicSheaf.constantSystemIsoRepresentationSheafOne (ℓ := ℓ) B X x).inv
  exact ⟨_, hc, LAdicSheaf.isFrobeniusDuality_compl₁₂_isogenyIso B X ℓ f
    (CompactificationOf.ofProper f) kbar p q hcard φ ψ 0 (by simp [φ, ψ]) (by simp [φ, ψ])
    φ ψ 0 (by simp [φ, ψ]) (by simp [φ, ψ]) i (2 * d - i) hβ⟩

end Stacks.EtaleCohomology

namespace Weil

open Polynomial

/-- The reverse of `X - C c` is `1 - C c * X`. -/
theorem reverse_X_sub_C_eq_one_sub_C_mul_X {K : Type*} [Field K] (c : K) :
    (Polynomial.X - C c : K[X]).reverse = 1 - C c * Polynomial.X := by
  have hX : (Polynomial.X : K[X]).reverse = 1 := by
    have := Polynomial.reverse_mul_X (1 : K[X])
    rwa [one_mul, ← Polynomial.C_1, Polynomial.reverse_C, Polynomial.C_1] at this
  rw [sub_eq_add_neg, ← C_neg, reverse_add_C, natDegree_X, pow_one, hX, C_neg, neg_mul,
    ← sub_eq_add_neg]

variable (B : BigEtaleSite.{u}) (S : B.Scheme) {k : Type u} [Field k] [Fintype k]
  (f : S.1 ⟶ Spec (.of k)) [IsProper f] (ℓ : ℕ) [Fact ℓ.Prime]

/-- **`P_{2d}(t) = 1 - q^d t`** (FK IV.1, the Remark on `P_0`, `P_{2d}`): for `X` proper and smooth
of relative dimension `d` over the finite field `k` with `q` elements, with `X_k̄` connected (FK:
`S₀` smooth projective with `S = S₀ ⊗ k̄` irreducible, `d = dim S₀`), and `ℓ ∤ q`, the reverse
characteristic polynomial of the Frobenius on `H^{2d}(X_k̄, ℚ_ℓ)` is `1 - q^d t`. No rational point
is assumed. -/
@[weil "lem_fk401_char_poly_top_degree"]
theorem rationalFrobeniusCharpolyReverse_two_mul_eq [Fact (ℓ ≠ ringChar k)] (d : ℕ)
    [SmoothOfRelativeDimension d f]
    [ConnectedSpace (Stacks.Frobenius.fieldBaseChange (Over.mk f) (AlgebraicClosure k))] :
    rationalFrobeniusCharpolyReverse B S f ℓ (2 * d) =
      1 - C ((Fintype.card k : ℚ_[ℓ]) ^ d) * Polynomial.X := by
  have := isNoetherian_of_isProper f
  have := quasiSeparatedSpace_of_isProper f
  have hp : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k _⟩
  obtain ⟨e, -, hcard⟩ := FiniteField.card k (ringChar k)
  have hℓ : ℓ ≠ ringChar k := Fact.out
  obtain ⟨hF, hrank⟩ :=
    Stacks.EtaleCohomology.LAdicSheaf.rationalFrobenius_top_constantSystem_eq_smul B ℓ
      (AlgebraicClosure k) (ringChar k) e hcard hℓ S f d
  unfold rationalFrobeniusCharpolyReverse
  rw [← rationalGeometricCompactlySupportedFrobenius_eq_rationalFrobenius B S f ℓ (ringChar k) e
    hcard (2 * d)]
  have hF' : (Stacks.EtaleCohomology.LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B S ℓ f
      (CompactificationOf.ofProper f) (AlgebraicClosure k) (ringChar k) e hcard
      (Stacks.EtaleCohomology.LAdicSheaf.constantSystem B S ℓ) ((2 * d : ℕ) : ℤ)).hom =
      (((ringChar k ^ (e : ℕ)) ^ d : ℕ) : ℚ_[ℓ]) • LinearMap.id := hF
  rw [hF', LinearMap.charpoly_smul_id_of_finrank_eq_one hrank, reverse_X_sub_C_eq_one_sub_C_mul_X,
    hcard]
  push_cast
  rfl

/-- **Poincaré duality with Frobenius on `H(X_k̄, ℚ_ℓ)`** (FK IV.1.6, for `S₀` with `S = S₀ ⊗ k̄`
connected): for `X` proper and smooth of relative dimension `d` over the finite field `k` with `q`
elements, with `X_k̄` connected, `ℓ ∤ q` and `ν ≤ 2d`, there is a `q^d`-duality for
`(F_ν, F_{2d-ν})` on `H^ν(X_k̄, ℚ_ℓ) × H^{2d-ν}(X_k̄, ℚ_ℓ)`. No rational point is assumed. -/
theorem exists_isFrobeniusDuality_rationalFrobenius [Fact (ℓ ≠ ringChar k)] (d : ℕ)
    [SmoothOfRelativeDimension d f]
    [ConnectedSpace (Stacks.Frobenius.fieldBaseChange (Over.mk f) (AlgebraicClosure k))]
    (ν : ℕ) (hν : ν ≤ 2 * d) :
    ∃ (β : rationalCohomology B S f ℓ ν →ₗ[ℚ_[ℓ]] rationalCohomology B S f ℓ (2 * d - ν) →ₗ[ℚ_[ℓ]]
      ℚ_[ℓ]) (hc : ((Fintype.card k : ℚ_[ℓ]) ^ d) ≠ 0),
      β.IsFrobeniusDuality (rationalFrobenius B S f ℓ ν) (rationalFrobenius B S f ℓ (2 * d - ν))
        (Units.mk0 _ hc) := by
  have := isNoetherian_of_isProper f
  have := quasiSeparatedSpace_of_isProper f
  have hp : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k _⟩
  obtain ⟨e, -, hcard⟩ := FiniteField.card k (ringChar k)
  have hℓ : ℓ ≠ ringChar k := Fact.out
  have h := Stacks.EtaleCohomology.LAdicSheaf.exists_isFrobeniusDuality_constantSystem B ℓ
    (AlgebraicClosure k) (ringChar k) e hcard hℓ S f d ν hν
  have hidx : (2 * (d : ℤ) - (ν : ℤ)) = ((2 * d - ν : ℕ) : ℤ) := by omega
  rw [hidx] at h
  obtain ⟨β, hc, hβ⟩ := h
  rw [rationalGeometricCompactlySupportedFrobenius_eq_rationalFrobenius B S f ℓ (ringChar k) e hcard
    ν, rationalGeometricCompactlySupportedFrobenius_eq_rationalFrobenius B S f ℓ (ringChar k) e
    hcard (2 * d - ν)] at hβ
  have hq : (((ringChar k ^ (e : ℕ)) ^ d : ℕ) : ℚ_[ℓ]) = (Fintype.card k : ℚ_[ℓ]) ^ d := by
    rw [hcard]; push_cast; rfl
  refine ⟨β, hq ▸ hc, ?_⟩
  convert hβ using 1
  ext
  simp [hq]

end Weil

end
