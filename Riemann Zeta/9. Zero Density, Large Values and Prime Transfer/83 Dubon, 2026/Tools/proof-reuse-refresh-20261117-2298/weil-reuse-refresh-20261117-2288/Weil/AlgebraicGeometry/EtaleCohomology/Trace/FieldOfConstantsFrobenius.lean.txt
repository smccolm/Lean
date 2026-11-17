module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricComponentsPurityReduction
public import Weil.AlgebraicGeometry.EtaleCohomology.Duality.TopDegreeFrobenius
public import Weil.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafTrivialConstant
public import Weil.AlgebraicGeometry.EtaleCohomology.Trace.FieldOfConstantsCohomologyDecomposition
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.Trace.RationalCohomologyFrobenius

/-!
# The Frobenius over the field of constants

Let `S` be a connected scheme, smooth and proper over a finite field `k` with `q` elements, and
`ℓ ≠ char k` a prime. By Deligne's theorem the Frobenius `F_ν` on `H^ν(S_k̄, ℚ_ℓ)` is pure of
weight `ν`: for every embedding `ι : ℚ_ℓ → ℂ` the roots of its characteristic polynomial have
absolute value `q ^ (ν / 2)`. Here this is deduced from the purity of the cohomology of the
ℓ-adic sheaf of the trivial representation, which is isomorphic to the constant ℓ-adic sheaf.

The ring `k' = Γ(S, 𝒪_S)` is a finite field extension of `k` (the *field of constants*), the
structure morphism `f` factors as `S ⟶ Spec k' ⟶ Spec k`, and `S` is proper, smooth of the same
relative dimension and geometrically connected over `k'`. For any such factorization through a
finite extension `k'` of degree `r`, `P_ν(S/k)(T) = P_ν(S/k')(T ^ r)`, where
`P_ν(T) = det(1 - T F_ν)`.

## Main results

* `Weil.LAdicSheaf.isCharpolyPureOfWeight_constantSystem`,
  `Weil.isCharpolyPureOfWeight_rationalFrobenius`: purity of `H^ν(S_k̄, ℚ_ℓ)`.
* `Weil.smoothOfRelativeDimension_of_comp_specAlgebraMap_eq`,
  `Weil.smooth_of_comp_specAlgebraMap_eq`, `Weil.isProper_of_comp_specAlgebraMap_eq`: a
  factorization `f = g ≫ (Spec k' ⟶ Spec k)` through a finite extension inherits
  smoothness and properness.
* `Weil.exists_fieldOfConstants`: the field of constants.
* `Weil.rationalFrobeniusCharpolyReverse_eq_comp_of_comp_specAlgebraMap_eq`,
  `Weil.exists_fieldOfConstants_rationalFrobeniusCharpolyReverse_eq_comp`:
  `P_ν(S/k)(T) = P_ν(S/k')(T ^ [k' : k])`.

## Implementation notes

Smoothness of `g` comes from writing it as the open immersion `(id, g) : S ⟶ S ×_k k'` followed by
the base change of `f`. The comparison of Frobenius polynomials is proved from the L-functions and
the weights over `k` and over `k'`, so it uses purity on both sides; geometric connectedness over
`k'` is not needed for it.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, IV.1.
* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)
* [Stacks Project, Tag 0BUG](https://stacks.math.columbia.edu/tag/0BUG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.EtaleCohomology Stacks.Frobenius
  Stacks.AlgebraicGeometry

universe u

namespace Weil

variable (B : BigEtaleSite.{u}) (S : B.Scheme) {k : Type u} [Field k] [Fintype k]
  (f : S.1 ⟶ Spec (.of k)) [IsProper f] (ℓ : ℕ) [Fact ℓ.Prime]

/-- **Purity of `Hⁱ(S_k̄, ℚ_ℓ)`** (Deligne). -/
theorem LAdicSheaf.isCharpolyPureOfWeight_constantSystem [IsNoetherian S.1]
    [QuasiSeparatedSpace S.1] [ConnectedSpace S.1] [Smooth f] (kbar : Type u) [Field kbar]
    [Algebra k kbar] [IsAlgClosure k kbar] (p q : ℕ)
    [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q) (hℓ : ℓ ≠ p) (i : ℤ)
    (ι : ℚ_[ℓ] →+* ℂ)
    [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B S ℓ f
      (CompactificationOf.ofProper f) kbar (LAdicSheaf.constantSystem B S ℓ) i)] :
    IsCharpolyPureOfWeight (p ^ q) ι i
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B S ℓ f
        (CompactificationOf.ofProper f) kbar p q hcard (LAdicSheaf.constantSystem B S ℓ)
        i).hom := by
  have : Nonempty S.1 := ConnectedSpace.toNonempty
  let x : GeometricPoint S.1 := S.1.algClosedPoint (Classical.arbitrary S.1)
  have := (LAdicSheaf.traceFormula B S ℓ f (CompactificationOf.ofProper f) kbar p q hcard hℓ
    (LAdicSheaf.representationSheaf B S x (1 : EtaleFundamentalGroup S.1 x →* GL (Fin 1) ℚ_[ℓ])
      continuous_const)).1 i
  have h := LAdicSheaf.isCharpolyPureOfWeight_representationSheaf_one B ℓ kbar p q hcard hℓ S f x
    (r := 1) continuous_const i ι
  unfold IsCharpolyPureOfWeight at h ⊢
  rwa [LAdicSheaf.charpoly_rationalGeometricCompactlySupportedFrobenius_representationSheaf_one_eq
    B S x f _ kbar p q hcard i] at h

variable {S} in
/-- **Purity of `F_ν` on `H^ν(S_k̄, ℚ_ℓ)`** for `S` connected, smooth and proper over `k`:
every complex conjugate of every eigenvalue has absolute value `q ^ (ν / 2)` (Deligne). -/
theorem isCharpolyPureOfWeight_rationalFrobenius [ConnectedSpace S.1] [Smooth f]
    [Fact (ℓ ≠ ringChar k)] (ν : ℕ) (ι : ℚ_[ℓ] →+* ℂ) :
    IsCharpolyPureOfWeight (Fintype.card k) ι ν (rationalFrobenius B S f ℓ ν) := by
  have := isNoetherian_of_isProper f
  have := quasiSeparatedSpace_of_isProper f
  have : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k _⟩
  have hcard := (FiniteField.card k (ringChar k)).choose_spec.2
  have h := LAdicSheaf.isCharpolyPureOfWeight_constantSystem B S f ℓ (AlgebraicClosure k)
    (ringChar k) _ hcard Fact.out ν ι
  rw [rationalGeometricCompactlySupportedFrobenius_eq_rationalFrobenius, ← hcard] at h
  exact h

/-! ### A factorization through a finite extension of the base field -/

section Factorization

variable {B S f} {k' : Type u} [Field k'] [Algebra k k'] (g : S.1 ⟶ Spec (.of k'))

omit [Fintype k] [Fact ℓ.Prime] in
/-- If `f = g ≫ (Spec k' ⟶ Spec k)`, then `g` is proper. -/
theorem isProper_of_comp_specAlgebraMap_eq (hg : g ≫ specAlgebraMap k k' = f) : IsProper g := by
  subst hg
  exact IsProper.of_comp g (specAlgebraMap k k')

omit [Fintype k] [IsProper f] in
/-- If `f = g ≫ (Spec k' ⟶ Spec k)` is smooth of relative dimension `n` and `k'` is a finite
extension of `k`, then so is `g`: it is the composition of the open immersion
`(id, g) : S ⟶ S ×_k k'` with the base change of `f`. -/
theorem smoothOfRelativeDimension_of_comp_specAlgebraMap_eq [Finite k] [Finite k']
    (hg : g ≫ specAlgebraMap k k' = f) (n : ℕ) [SmoothOfRelativeDimension n f] :
    SmoothOfRelativeDimension n g := by
  have : Module.Finite k k' := Module.Finite.of_finite
  let s := fieldExtensionSection f g hg (AlgHom.id k k')
  have : IsOpenImmersion s := isOpenImmersion_fieldExtensionSection f g hg _
  have hs : s ≫ pullback.snd f (specAlgebraMap k k') = g := by
    rw [fieldExtensionSection_snd]
    have : CommRingCat.ofHom (AlgHom.id k k').toRingHom = 𝟙 _ := rfl
    rw [this, Spec.map_id, Category.comp_id]
  have : SmoothOfRelativeDimension n (pullback.snd f (specAlgebraMap k k')) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange n).of_isPullback
      (IsPullback.of_hasPullback f (specAlgebraMap k k')) ‹_›
  have h0 := smoothOfRelativeDimension_comp 0 n s (pullback.snd f (specAlgebraMap k k'))
  rw [Nat.zero_add, hs] at h0
  exact h0

omit [Fintype k] [IsProper f] in
/-- If `f = g ≫ (Spec k' ⟶ Spec k)` is smooth and `k'` is a finite extension of `k`, then so
is `g`. -/
theorem smooth_of_comp_specAlgebraMap_eq [Finite k] [Finite k'] (hg : g ≫ specAlgebraMap k k' = f)
    [Smooth f] : Smooth g := by
  have : Module.Finite k k' := Module.Finite.of_finite
  let s := fieldExtensionSection f g hg (AlgHom.id k k')
  have : IsOpenImmersion s := isOpenImmersion_fieldExtensionSection f g hg _
  have hs : s ≫ pullback.snd f (specAlgebraMap k k') = g := by
    rw [fieldExtensionSection_snd]
    have : CommRingCat.ofHom (AlgHom.id k k').toRingHom = 𝟙 _ := rfl
    rw [this, Spec.map_id, Category.comp_id]
  have : Smooth (pullback.snd f (specAlgebraMap k k')) :=
    smooth_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback f (specAlgebraMap k k')) ‹_›
  rw [← hs]
  infer_instance

omit [Fintype k] [Fact ℓ.Prime] in
/-- `ℓ ≠ char k` gives `ℓ ≠ char k'` for an extension `k'` of `k`. -/
theorem ne_ringChar_of_algebra (hℓ : ℓ ≠ ringChar k) : ℓ ≠ ringChar k' := by
  rwa [← Algebra.ringChar_eq k k']

variable (B S) in
/-- **The Frobenius polynomials over `k` and over an extension `k'` through which the structure
morphism factors.** Let `S` be connected, smooth and proper over `k`, with structure morphism
`f = g ≫ (Spec k' ⟶ Spec k)` for a finite extension `k'` of `k` of degree `r`. Then
`P_ν(S/k)(T) = P_ν(S/k')(T ^ r)` for every `ν`: both sides are pure of weight `ν` (Deligne), and
the L-functions over `k` and over `k'` agree after `T ↦ T ^ r`. -/
theorem rationalFrobeniusCharpolyReverse_eq_comp_of_comp_specAlgebraMap_eq [Fintype k']
    [ConnectedSpace S.1] [Smooth f] [Fact (ℓ ≠ ringChar k)] (hg : g ≫ specAlgebraMap k k' = f)
    [IsProper g] [Fact (ℓ ≠ ringChar k')] (ν : ℕ) :
    rationalFrobeniusCharpolyReverse B S f ℓ ν =
      (rationalFrobeniusCharpolyReverse B S g ℓ ν).comp (Polynomial.X ^ Module.finrank k k') := by
  have hsm : Smooth g := smooth_of_comp_specAlgebraMap_eq g hg
  subst hg
  have := isNoetherian_of_isProper g
  have := quasiSeparatedSpace_of_isProper g
  have : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k _⟩
  have : CharP k' (ringChar k) := (Algebra.charP_iff k k' (ringChar k)).1 (ringChar.charP k)
  have : Module.Finite k k' := Module.Finite.of_finite
  have hℓ : ℓ ≠ ringChar k := Fact.out
  have hcard := (FiniteField.card k (ringChar k)).choose_spec.2
  set q := (FiniteField.card k (ringChar k)).choose
  have hcard' : Fintype.card k' = ringChar k ^ (q * Module.finrank k k') := by
    rw [Module.card_eq_pow_finrank (K := k) (V := k'), hcard, pow_mul]
  have := (LAdicSheaf.traceFormula B S ℓ (g ≫ specAlgebraMap k k')
    (CompactificationOf.ofProper _) (AlgebraicClosure k) (ringChar k) q hcard hℓ
    (LAdicSheaf.constantSystem B S ℓ)).1
  have := (LAdicSheaf.traceFormula B S ℓ g (CompactificationOf.ofProper g) (AlgebraicClosure k')
    (ringChar k) _ hcard' hℓ (LAdicSheaf.constantSystem B S ℓ)).1
  obtain ⟨ι⟩ := Padic.nonempty_ringHom_complex ℓ
  have key :=
    LAdicSheaf.reverse_charpoly_rationalGeometricCompactlySupportedFrobenius_eq_comp_of_pure
    B S ℓ g (CompactificationOf.ofProper _) (CompactificationOf.ofProper g) (AlgebraicClosure k)
    (AlgebraicClosure k') (ringChar k) q hcard hcard' hℓ (LAdicSheaf.constantSystem B S ℓ) ι
    (fun i => LAdicSheaf.isCharpolyPureOfWeight_constantSystem B S _ ℓ _ _ q hcard hℓ i ι)
    (fun i => LAdicSheaf.isCharpolyPureOfWeight_constantSystem B S g ℓ _ _ _ hcard' hℓ i ι) ν
  unfold rationalFrobeniusCharpolyReverse
  rw [← rationalGeometricCompactlySupportedFrobenius_eq_rationalFrobenius B S _ ℓ (ringChar k) q
    hcard, ← rationalGeometricCompactlySupportedFrobenius_eq_rationalFrobenius B S g ℓ (ringChar k)
    _ hcard']
  exact key

end Factorization

/-! ### The field of constants -/

omit [Fintype k] in
/-- **The field of constants.** A connected scheme `S` smooth of relative dimension `n` and proper
over the finite field `k` is, through `S ⟶ Spec Γ(S, 𝒪_S)`, a scheme over the finite extension
`k' = Γ(S, 𝒪_S)` of `k`, still proper and smooth of relative dimension `n`, and geometrically
connected. -/
theorem exists_fieldOfConstants [Finite k] [ConnectedSpace S.1] (n : ℕ)
    [SmoothOfRelativeDimension n f] :
    ∃ (k' : Type u) (_ : Field k') (_ : Fintype k') (_ : Algebra k k') (g : S.1 ⟶ Spec (.of k')),
      g ≫ specAlgebraMap k k' = f ∧ IsProper g ∧ SmoothOfRelativeDimension n g ∧
        ConnectedSpace (fieldBaseChange (Over.mk g) (AlgebraicClosure k')) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  have : AlgebraicGeometry.IsReduced S.1 := isReduced_of_smooth f
  have hfield :=
    ProperSectionsGeom.isField_globalSections_of_connectedSpace_of_isReduced
      k f
  let : Field Γ(S.1, ⊤) := hfield.toField
  let : Algebra k Γ(S.1, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  have : Module.Finite k Γ(S.1, ⊤) :=
    ProperSectionsGeom.moduleFinite_globalSections_of_isProper k f
  have : Finite Γ(S.1, ⊤) := Module.finite_of_finite k
  let : Fintype Γ(S.1, ⊤) := Fintype.ofFinite _
  have hg : S.1.toSpecΓ ≫ specAlgebraMap k Γ(S.1, ⊤) = f := by
    change S.1.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) = f
    rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
      ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]
  refine ⟨Γ(S.1, ⊤), inferInstance, inferInstance, inferInstance, S.1.toSpecΓ, hg,
    isProper_of_comp_specAlgebraMap_eq _ hg,
    smoothOfRelativeDimension_of_comp_specAlgebraMap_eq _ hg n, ?_⟩
  have h0 :=
    ProperGeomConnected.geometricallyConnected_toSpecΓ_of_isProper_over_field
      k S.1 f
  rw [geometricallyConnected_iff, geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms] at h0
  exact h0 (AlgebraicClosure Γ(S.1, ⊤))

/-- **The Frobenius polynomials over `k` and over the field of constants.** For `S` connected,
smooth of relative dimension `n` and proper over `k`, the field of constants `k'` of
`exists_fieldOfConstants` satisfies `P_ν(S/k)(T) = P_ν(S/k')(T ^ [k' : k])` for every `ν`. -/
theorem exists_fieldOfConstants_rationalFrobeniusCharpolyReverse_eq_comp [ConnectedSpace S.1]
    (n : ℕ) [SmoothOfRelativeDimension n f] [Fact (ℓ ≠ ringChar k)] :
    ∃ (k' : Type u) (_ : Field k') (_ : Fintype k') (_ : Algebra k k') (g : S.1 ⟶ Spec (.of k'))
      (_ : IsProper g) (_ : Fact (ℓ ≠ ringChar k')),
      g ≫ specAlgebraMap k k' = f ∧ SmoothOfRelativeDimension n g ∧
        ConnectedSpace (fieldBaseChange (Over.mk g) (AlgebraicClosure k')) ∧
        ∀ ν : ℕ, rationalFrobeniusCharpolyReverse B S f ℓ ν =
          (rationalFrobeniusCharpolyReverse B S g ℓ ν).comp
            (Polynomial.X ^ Module.finrank k k') := by
  obtain ⟨k', _, _, _, g, hg, hp, hs, hc⟩ := exists_fieldOfConstants B S f n
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hℓ : Fact (ℓ ≠ ringChar k') := ⟨ne_ringChar_of_algebra (k := k) (k' := k') ℓ Fact.out⟩
  exact ⟨k', _, _, _, g, hp, hℓ, hg, hs, hc,
    rationalFrobeniusCharpolyReverse_eq_comp_of_comp_specAlgebraMap_eq B S ℓ g hg⟩

end Weil
