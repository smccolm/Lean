module

public import Weil.AlgebraicGeometry.EtaleCohomology.Trace.ConnectedComponentsCharpoly
public import Weil.AlgebraicGeometry.EtaleCohomology.Trace.FieldOfConstantsFrobenius
public import Weil.AlgebraicGeometry.EtaleCohomology.Trace.WeilEstimateFromPurityAllEmbeddings
public import Weil.LinearAlgebra.Charpoly.Reverse
public import Weil.Attr

/-!
# Deligne's theorem: the Weil estimate for smooth proper schemes over a finite field

Let `k` be a finite field with `q` elements, `ℓ ≠ char k` a prime and `S` a scheme smooth and
proper over `k`. Deligne's theorem (Weil II, in the form of Stacks, Tag 03VH) says that the
Frobenius `F_ν` on `H^ν(S_k̄, ℚ_ℓ)` is pure of weight `ν`: every eigenvalue `λ ∈ ℚ̄_ℓ` of `F_ν`
is an algebraic number with `|ι λ| = q ^ (ν / 2)` for every field embedding `ι : ℚ(λ) → ℂ`.
This is the property `W(S/k)` (`Weil.SatisfiesWeilEstimate`).

## Main results

* `Weil.satisfiesWeilEstimate_iff_forall_isCharpolyPureOfWeight`: `W(S/k)` holds iff every `F_ν`
  is `ι`-pure of weight `ν` along every `ι : ℚ_ℓ →+* ℂ`.
* `Weil.satisfiesWeilEstimate_of_connectedSpace`: `W(S/k)` for `S` connected, smooth and proper.
* `Weil.satisfiesWeilEstimate_of_connectedComponents`: `W(S/k)` for `S` proper over `k` as soon as
  `W(T/k)` holds for every connected component `T` of `S` with its open subscheme structure.
* `Weil.satisfiesWeilEstimate`: **Deligne's theorem**, `W(S/k)` for `S` smooth and proper.
* `Weil.isAlgebraic_of_aeval_charpoly_rationalFrobenius_eq_zero`,
  `Weil.norm_eq_of_aeval_charpoly_rationalFrobenius_eq_zero`: the two halves of `W(S/k)`.
* `Weil.isAlgebraic_and_norm_eq_of_aeval_inv_rationalFrobeniusCharpolyReverse_eq_zero`: the
  reciprocal roots of `P_ν(t) = det(1 - t F_ν)` are algebraic of absolute value `q ^ (ν / 2)`.

## Implementation notes

[FK] state the theorem for `S` smooth and projective; it is stated here for `S` smooth and
proper. The connected case is Deligne's purity for the constant ℓ-adic system
(`Weil.isCharpolyPureOfWeight_rationalFrobenius`, from Stacks' `weightBound` at the trivial
representation). The general case is a noetherian induction on the open and closed subschemes of
`S`, using that purity passes to an open and closed decomposition
(`Weil.isCharpolyPureOfWeight_rationalFrobenius_of_openClosed`).

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, IV.1, IV.4.
* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.EtaleCohomology IntermediateField Polynomial

universe u

namespace Weil

variable {B : BigEtaleSite.{u}} {k : Type u} [Field k] [Fintype k] {ℓ : ℕ} [Fact ℓ.Prime]
  [Fact (ℓ ≠ ringChar k)]

/-! ### The Weil estimate and purity -/

/-- A finite-dimensional endomorphism over `ℚ_ℓ` which is pure of weight `w` along every
`ι : ℚ_ℓ →+* ℂ` has all its eigenvalues in `ℚ̄_ℓ` algebraic of absolute value `Q ^ (w / 2)`,
and conversely. -/
theorem forall_isCharpolyPureOfWeight_iff {V : Type*} [AddCommGroup V] [Module ℚ_[ℓ] V]
    [FiniteDimensional ℚ_[ℓ] V] (Q : ℕ) (w : ℤ) (φ : Module.End ℚ_[ℓ] V) :
    (∀ ι : ℚ_[ℓ] →+* ℂ, IsCharpolyPureOfWeight Q ι w φ) ↔
      ∀ μ : AlgebraicClosure ℚ_[ℓ], aeval μ φ.charpoly = 0 →
        IsAlgebraic ℚ μ ∧ ∀ ι : ℚ⟮μ⟯ →+* ℂ,
          ‖ι (AdjoinSimple.gen ℚ μ)‖ = (Q : ℝ) ^ ((w : ℝ) / 2) := by
  constructor
  · intro h μ hμ
    exact isAlgebraic_and_norm_eq_of_forall_isCharpolyPureOfWeight h hμ
  · intro h ι z hz
    -- extend `ι` to the algebraic closure
    let _ : Algebra ℚ_[ℓ] ℂ := ι.toAlgebra
    let ι' : AlgebraicClosure ℚ_[ℓ] →ₐ[ℚ_[ℓ]] ℂ := IsAlgClosed.lift
    have hsplit : (φ.charpoly.map (algebraMap ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ]))).Splits :=
      IsAlgClosed.splits _
    have hmap : φ.charpoly.map ι =
        (φ.charpoly.map (algebraMap ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ]))).map ι'.toRingHom := by
      rw [Polynomial.map_map]
      congr 1
      ext a
      exact (ι'.commutes a).symm
    rw [hmap] at hz
    obtain ⟨μ, rfl⟩ := hsplit.mem_range_of_isRoot
      ((φ.charpoly_monic.map _).ne_zero) hz
    have hμ : aeval μ φ.charpoly = 0 := by
      rw [aeval_def, eval₂_eq_eval_map]
      exact (isRoot_map_iff ι'.toRingHom.injective).1 hz
    obtain ⟨halg, hnorm⟩ := h μ hμ
    have hint : IsIntegral ℚ μ := halg.isIntegral
    refine ⟨(isAlgebraic_algHom_iff ι'.toRingHom.toRatAlgHom ι'.toRingHom.injective).2 halg, ?_⟩
    have := hnorm (ι'.toRingHom.comp (IntermediateField.val ℚ⟮μ⟯).toRingHom)
    exact this

variable (B) in
/-- `W(S/k)` holds iff every Frobenius `F_ν` on `H^ν(S_k̄, ℚ_ℓ)` is `ι`-pure of weight `ν`
relative to `q` along every `ι : ℚ_ℓ →+* ℂ`. -/
theorem satisfiesWeilEstimate_iff_forall_isCharpolyPureOfWeight (S : B.Scheme)
    (f : S.1 ⟶ Spec (.of k)) [IsProper f] :
    SatisfiesWeilEstimate B S f ℓ ↔ ∀ (ν : ℕ) (ι : ℚ_[ℓ] →+* ℂ),
      IsCharpolyPureOfWeight (Fintype.card k) ι ν (rationalFrobenius B S f ℓ ν) := by
  unfold SatisfiesWeilEstimate
  exact forall_congr' fun ν =>
    (forall_isCharpolyPureOfWeight_iff (Fintype.card k) ν (rationalFrobenius B S f ℓ ν)).symm

variable (B) in
/-- **`W(S/k)` for `S` connected, smooth and proper over `k`** (Deligne's purity for the constant
ℓ-adic sheaf, Stacks' `weightBound` at the trivial representation). -/
@[weil "lem_fk404_weil_estimate_connected_smooth_proper"]
theorem satisfiesWeilEstimate_of_connectedSpace (S : B.Scheme) (f : S.1 ⟶ Spec (.of k))
    [IsProper f] [Smooth f] [ConnectedSpace S.1] : SatisfiesWeilEstimate B S f ℓ :=
  (satisfiesWeilEstimate_iff_forall_isCharpolyPureOfWeight B S f).2 fun ν ι =>
    isCharpolyPureOfWeight_rationalFrobenius B f ℓ ν ι

/-! ### Purity over the open and closed subschemes -/

/-- On the empty scheme every Frobenius is pure (there are no eigenvalues). -/
theorem isCharpolyPureOfWeight_rationalFrobenius_of_isEmpty {X : B.Scheme}
    (hX : IsEmpty X.1) (f : X.1 ⟶ Spec (.of k)) [IsProper f] (q : ℕ) (ι : ℚ_[ℓ] →+* ℂ)
    (w : ℤ) (ν : ℕ) : IsCharpolyPureOfWeight q ι w (rationalFrobenius B X f ℓ ν) := by
  have := subsingleton_rationalCohomology_of_isEmpty (B := B) hX f (ℓ := ℓ) ν
  intro z hz
  rw [charpoly_eq_one_of_subsingleton, Polynomial.map_one] at hz
  exact absurd hz (by simp [IsRoot])

variable (B) in
/-- **Purity over the open and closed subschemes of `S`**, by noetherian induction on their images:
each is empty, connected, or the disjoint union of two smaller open and closed subschemes. The
Frobenius of every connected open and closed subscheme of `S` is assumed pure. -/
theorem isCharpolyPureOfWeight_of_isOpenImmersion_of_isClosedImmersion (S : B.Scheme)
    (f : S.1 ⟶ Spec (.of k)) [IsProper f]
    (hpure : ∀ (Y : B.Scheme) (c : Y ⟶ S) [IsOpenImmersion (B.inclusion.map c)]
      [IsClosedImmersion (B.inclusion.map c)] [ConnectedSpace Y.1]
      (g : Y.1 ⟶ Spec (.of k)) [IsProper g], g = B.inclusion.map c ≫ f →
      ∀ (ν : ℕ) (ι : ℚ_[ℓ] →+* ℂ),
      IsCharpolyPureOfWeight (Fintype.card k) ι ν (rationalFrobenius B Y g ℓ ν))
    (V : TopologicalSpace.Closeds S.1) :
    ∀ (W : B.Scheme) (c : W ⟶ S) [IsOpenImmersion (B.inclusion.map c)]
      [IsClosedImmersion (B.inclusion.map c)], Set.range (B.inclusion.map c).base = (V : Set S.1) →
      ∀ (gW : W.1 ⟶ Spec (.of k)) [IsProper gW], gW = B.inclusion.map c ≫ f →
      ∀ (ν : ℕ) (ι : ℚ_[ℓ] →+* ℂ),
        IsCharpolyPureOfWeight (Fintype.card k) ι ν (rationalFrobenius B W gW ℓ ν) := by
  have := isNoetherian_of_isProper f
  induction V using WellFoundedLT.induction with
  | ind V ih =>
  intro W c _ _ hV gW _ hgW
  rcases isEmpty_or_nonempty W.1 with hWe | hWne
  · exact fun ν ι => isCharpolyPureOfWeight_rationalFrobenius_of_isEmpty hWe gW _ ι ν ν
  by_cases hWc : ConnectedSpace W.1
  · exact hpure W c gW hgW
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
      ∀ (ν : ℕ) (ι : ℚ_[ℓ] →+* ℂ), IsCharpolyPureOfWeight (Fintype.card k) ι ν
        (rationalFrobenius B P (B.inclusion.map jP ≫ gW) ℓ ν) := by
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
  intro ν ι
  exact isCharpolyPureOfWeight_rationalFrobenius_of_openClosed gW jU iZ hij ν
    (hpiece U jU hU0 ν ι) (hpiece Z iZ hZ0 ν ι)

variable (B) in
/-- Purity of `S` from the purity of its connected open and closed subschemes. -/
theorem forall_isCharpolyPureOfWeight_of_connected (S : B.Scheme) (f : S.1 ⟶ Spec (.of k))
    [IsProper f]
    (hpure : ∀ (Y : B.Scheme) (c : Y ⟶ S) [IsOpenImmersion (B.inclusion.map c)]
      [IsClosedImmersion (B.inclusion.map c)] [ConnectedSpace Y.1]
      (g : Y.1 ⟶ Spec (.of k)) [IsProper g], g = B.inclusion.map c ≫ f →
      ∀ (ν : ℕ) (ι : ℚ_[ℓ] →+* ℂ),
      IsCharpolyPureOfWeight (Fintype.card k) ι ν (rationalFrobenius B Y g ℓ ν))
    (ν : ℕ) (ι : ℚ_[ℓ] →+* ℂ) :
    IsCharpolyPureOfWeight (Fintype.card k) ι ν (rationalFrobenius B S f ℓ ν) := by
  have : IsOpenImmersion (B.inclusion.map (𝟙 S)) := by
    rw [CategoryTheory.Functor.map_id]; infer_instance
  have : IsClosedImmersion (B.inclusion.map (𝟙 S)) := by
    rw [CategoryTheory.Functor.map_id]; infer_instance
  exact isCharpolyPureOfWeight_of_isOpenImmersion_of_isClosedImmersion B S f hpure
    ⟨Set.range (B.inclusion.map (𝟙 S)).base,
      (B.inclusion.map (𝟙 S)).isClosedEmbedding.isClosed_range⟩ S (𝟙 S) rfl f
    (by rw [CategoryTheory.Functor.map_id, Category.id_comp]) ν ι

/-! ### The connected components -/

/-- The Frobenius depends on the structure morphism only through its value. -/
theorem isCharpolyPureOfWeight_rationalFrobenius_congr {X : B.Scheme} {g g' : X.1 ⟶ Spec (.of k)}
    [IsProper g] [IsProper g'] (h : g = g') {q : ℕ} {ι : ℚ_[ℓ] →+* ℂ} {w : ℤ} {ν : ℕ}
    (hg : IsCharpolyPureOfWeight q ι w (rationalFrobenius B X g ℓ ν)) :
    IsCharpolyPureOfWeight q ι w (rationalFrobenius B X g' ℓ ν) := by
  subst h
  exact hg

/-- **Purity is invariant under isomorphism over `k`**: if `e : Y ⟶ T` is an isomorphism of schemes
with `gY = e ≫ gT`, purity of the Frobenius of `T` gives that of `Y`. -/
theorem isCharpolyPureOfWeight_rationalFrobenius_of_isIso {Y T : B.Scheme} (e : Y ⟶ T)
    [IsIso (B.inclusion.map e)] (gY : Y.1 ⟶ Spec (.of k)) (gT : T.1 ⟶ Spec (.of k)) [IsProper gY]
    [IsProper gT] (he : gY = B.inclusion.map e ≫ gT) {q : ℕ} {ι : ℚ_[ℓ] →+* ℂ} {w : ℤ} (ν : ℕ)
    (hT : IsCharpolyPureOfWeight q ι w (rationalFrobenius B T gT ℓ ν)) :
    IsCharpolyPureOfWeight q ι w (rationalFrobenius B Y gY ℓ ν) := by
  -- `Y = T ⊔ ∅`, with `T ⟶ Y` the inverse of `e`
  let jU : T ⟶ Y := ObjectProperty.homMk (inv (B.inclusion.map e))
  let V0 : Y.1.Opens := ⊥
  let Z : B.Scheme := B.obj (V0 : Scheme.{u})
    (Scheme.size_lt_of_mono_of_isStrongPrelimit B.cutoff_isStrongPrelimit V0.ι Y.property)
  let iZ : Z ⟶ Y := ObjectProperty.homMk V0.ι
  have : IsOpenImmersion (B.inclusion.map jU) :=
    (inferInstance : IsOpenImmersion (inv (B.inclusion.map e)))
  have : IsClosedImmersion (B.inclusion.map jU) :=
    (inferInstance : IsClosedImmersion (inv (B.inclusion.map e)))
  have : IsOpenImmersion (B.inclusion.map iZ) := (inferInstance : IsOpenImmersion V0.ι)
  have : IsClosedImmersion (B.inclusion.map iZ) :=
    IsClosedImmersion.of_isPreimmersion V0.ι (by rw [Scheme.Opens.range_ι]; exact isClosed_empty)
  have hij : Set.range (B.inclusion.map jU).base = (Set.range (B.inclusion.map iZ).base)ᶜ := by
    change Set.range (inv (B.inclusion.map e)).base = (Set.range V0.ι)ᶜ
    rw [Scheme.Opens.range_ι]
    have : Function.Surjective (inv (B.inclusion.map e)).base :=
      (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso (asIso (inv (B.inclusion.map e))))).surjective
    rw [this.range_eq]
    exact (Set.compl_empty).symm
  have hZe : IsEmpty Z.1 := ⟨fun z => by
    have := (z : V0).2
    simp [V0] at this⟩
  have : IsProper (B.inclusion.map jU ≫ gY) := by
    rw [he]
    change IsProper (inv (B.inclusion.map e) ≫ B.inclusion.map e ≫ gT)
    rw [IsIso.inv_hom_id_assoc]
    infer_instance
  have : IsProper (B.inclusion.map iZ ≫ gY) := inferInstance
  refine isCharpolyPureOfWeight_rationalFrobenius_of_openClosed gY jU iZ hij ν ?_
    (isCharpolyPureOfWeight_rationalFrobenius_of_isEmpty hZe _ q ι w ν)
  refine isCharpolyPureOfWeight_rationalFrobenius_congr ?_ hT
  rw [he]
  change gT = inv (B.inclusion.map e) ≫ B.inclusion.map e ≫ gT
  rw [IsIso.inv_hom_id_assoc]

/-- The connected component of `x`, when it is open, as an open subscheme. -/
def openConnectedComponent {X : Scheme.{u}} (x : X) (hx : IsOpen (connectedComponent x)) :
    X.Opens :=
  ⟨connectedComponent x, hx⟩

instance {X : Scheme.{u}} (x : X) (hx : IsOpen (connectedComponent x)) :
    IsClosedImmersion (openConnectedComponent x hx).ι :=
  IsClosedImmersion.of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι]; exact isClosed_connectedComponent)

variable (B) in
/-- The connected component of `x`, when it is open, as an open subscheme in `B`. -/
abbrev connectedComponentScheme (S : B.Scheme) (x : S.1) (hx : IsOpen (connectedComponent x)) :
    B.Scheme :=
  B.obj ((openConnectedComponent x hx : S.1.Opens) : Scheme.{u})
    (Scheme.size_lt_of_mono_of_isStrongPrelimit B.cutoff_isStrongPrelimit
      (openConnectedComponent x hx).ι S.property)

variable (B) in
/-- **`W(S/k)` from `W(T/k)` for the connected components `T` of `S`.** Let `S` be proper over
`k`, and assume `W(T/k)` for every connected component `T` of `S` with its open subscheme
structure. Then `W(S/k)` holds. -/
@[weil "lem_fk404_weil_estimate_from_connected_components"]
theorem satisfiesWeilEstimate_of_connectedComponents (S : B.Scheme) (f : S.1 ⟶ Spec (.of k))
    [IsProper f]
    (hW : ∀ (x : S.1) (hx : IsOpen (connectedComponent x)),
      SatisfiesWeilEstimate B (connectedComponentScheme B S x hx)
        ((openConnectedComponent x hx).ι ≫ f) ℓ) :
    SatisfiesWeilEstimate B S f ℓ := by
  refine (satisfiesWeilEstimate_iff_forall_isCharpolyPureOfWeight B S f).2
    (forall_isCharpolyPureOfWeight_of_connected B S f fun Y c _ _ _ g _ hg ν ι => ?_)
  -- the image of `Y` is the connected component of any of its points
  obtain ⟨y⟩ : Nonempty Y.1 := ConnectedSpace.toNonempty
  set x := (B.inclusion.map c).base y
  have hclopen : IsClopen (Set.range (B.inclusion.map c).base) :=
    ⟨(B.inclusion.map c).isClosedEmbedding.isClosed_range,
      (B.inclusion.map c).isOpenEmbedding.isOpen_range⟩
  have hrange : Set.range (B.inclusion.map c).base = connectedComponent x := by
    refine subset_antisymm ?_ (hclopen.connectedComponent_subset ⟨y, rfl⟩)
    have hpc : _root_.IsPreconnected (Set.univ : Set Y.1) := isPreconnected_univ
    have := hpc.image _ (B.inclusion.map c).base.hom.2.continuousOn
    rw [Set.image_univ] at this
    exact this.subset_connectedComponent ⟨y, rfl⟩
  have hx : IsOpen (connectedComponent x) := hrange ▸ hclopen.isOpen
  -- `Y ≅ T` over `S`
  let V := openConnectedComponent x hx
  let T := connectedComponentScheme B S x hx
  have hle : Set.range (B.inclusion.map c).base ⊆ Set.range V.ι.base := by
    rw [Scheme.Opens.range_ι, hrange]
    rfl
  let e₀ : Y.1 ⟶ V := IsOpenImmersion.lift V.ι (B.inclusion.map c) hle
  have he₀ : e₀ ≫ V.ι = B.inclusion.map c := IsOpenImmersion.lift_fac _ _ _
  let e : Y ⟶ T := ObjectProperty.homMk e₀
  have : IsOpenImmersion (e₀ ≫ V.ι) := he₀ ▸ inferInstance
  have : IsOpenImmersion e₀ := IsOpenImmersion.of_comp e₀ V.ι
  have : Function.Surjective e₀.base := by
    intro v
    obtain ⟨w, hw⟩ : V.ι.base v ∈ Set.range (B.inclusion.map c).base := by
      rw [hrange]; exact v.2
    refine ⟨w, V.ι.isOpenEmbedding.injective ?_⟩
    rw [← hw, ← Scheme.Hom.comp_apply, he₀]
  have : IsIso e₀ := (isIso_iff_isOpenImmersion_and_surjective e₀).2 ⟨inferInstance, ⟨this⟩⟩
  have : IsIso (B.inclusion.map e) := (inferInstance : IsIso e₀)
  exact isCharpolyPureOfWeight_rationalFrobenius_of_isIso e g (V.ι ≫ f)
    (by rw [hg, ← he₀, Category.assoc]; rfl) ν
    ((satisfiesWeilEstimate_iff_forall_isCharpolyPureOfWeight B T (V.ι ≫ f)).1 (hW x hx) ν ι)

/-! ### Deligne's theorem -/

variable (B) in
/-- **Deligne's theorem `W(S/k)`** (the Riemann hypothesis over finite fields). Let `S` be a
scheme smooth and proper over the finite field `k` with `q` elements and `ℓ ≠ char k` a prime.
For every `ν` and every eigenvalue `λ ∈ ℚ̄_ℓ` of the Frobenius `F_ν` on `H^ν(S_k̄, ℚ_ℓ)`, `λ` is
algebraic and `|ι λ| = q ^ (ν / 2)` for every field embedding `ι : ℚ(λ) → ℂ`. -/
@[weil "thm_fk404_deligne_weil_conjecture"]
theorem satisfiesWeilEstimate (S : B.Scheme) (f : S.1 ⟶ Spec (.of k)) [IsProper f] [Smooth f] :
    SatisfiesWeilEstimate B S f ℓ :=
  (satisfiesWeilEstimate_iff_forall_isCharpolyPureOfWeight B S f).2 fun ν ι =>
    forall_isCharpolyPureOfWeight_of_connected B S f (fun Y c _ _ _ g _ hg ν ι => by
      have : Smooth g := by rw [hg]; infer_instance
      exact isCharpolyPureOfWeight_rationalFrobenius B g ℓ ν ι) ν ι

variable (B) in
/-- **The eigenvalues of Frobenius are algebraic**: every eigenvalue `λ ∈ ℚ̄_ℓ` of `F_ν` on
`H^ν(S_k̄, ℚ_ℓ)`, for `S` smooth and proper over `k`, is algebraic over `ℚ`. -/
@[weil "thm_fk401_deligne_weil_estimate_eigenvalues_algebraic"]
theorem isAlgebraic_of_aeval_charpoly_rationalFrobenius_eq_zero (S : B.Scheme)
    (f : S.1 ⟶ Spec (.of k)) [IsProper f] [Smooth f] (ν : ℕ) (μ : AlgebraicClosure ℚ_[ℓ])
    (hμ : aeval μ (rationalFrobenius B S f ℓ ν).charpoly = 0) : IsAlgebraic ℚ μ :=
  (satisfiesWeilEstimate B S f ν μ hμ).1

variable (B) in
/-- **The Weil estimate for the eigenvalues of Frobenius**: for every eigenvalue `λ ∈ ℚ̄_ℓ` of
`F_ν` on `H^ν(S_k̄, ℚ_ℓ)`, `S` smooth and proper over `k`, and every field embedding
`ι : ℚ(λ) → ℂ`, `|ι λ| = q ^ (ν / 2)`. -/
@[weil "thm_fk401_deligne_weil_estimate_eigenvalues"]
theorem norm_eq_of_aeval_charpoly_rationalFrobenius_eq_zero (S : B.Scheme)
    (f : S.1 ⟶ Spec (.of k)) [IsProper f] [Smooth f] (ν : ℕ) (μ : AlgebraicClosure ℚ_[ℓ])
    (hμ : aeval μ (rationalFrobenius B S f ℓ ν).charpoly = 0) (ι : ℚ⟮μ⟯ →+* ℂ) :
    ‖ι (AdjoinSimple.gen ℚ μ)‖ = (Fintype.card k : ℝ) ^ ((ν : ℝ) / 2) :=
  (satisfiesWeilEstimate B S f ν μ hμ).2 ι

/-! ### Reciprocal roots of `P_ν` -/

/-- `det(1 - t φ)` does not vanish at `t = 0`, so `0⁻¹ = 0` is never a root of it. -/
theorem aeval_zero_reverse_charpoly_ne_zero {K V L : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Field L] [Algebra K L] (φ : Module.End K V) :
    aeval (0 : L) φ.charpoly.reverse ≠ 0 := by
  rw [aeval_def, eval₂_at_zero, coeff_zero_reverse, φ.charpoly_monic.leadingCoeff, map_one]
  exact one_ne_zero

variable (B) in
/-- **The reciprocal roots of `P_ν(t) = det(1 - t F_ν | H^ν(S_k̄, ℚ_ℓ))`** for `S` smooth and
proper over `k` with `q` elements: every `λ ∈ ℚ̄_ℓ` with `P_ν(λ⁻¹) = 0` is algebraic, and
`|ι λ| = q ^ (ν / 2)` for every field embedding `ι : ℚ(λ) → ℂ`. -/
@[weil "thm_fk401_deligne_eigenvalue_absolute_value"]
theorem isAlgebraic_and_norm_eq_of_aeval_inv_rationalFrobeniusCharpolyReverse_eq_zero
    (S : B.Scheme) (f : S.1 ⟶ Spec (.of k)) [IsProper f] [Smooth f] (ν : ℕ)
    (μ : AlgebraicClosure ℚ_[ℓ]) (hμ : aeval μ⁻¹ (rationalFrobeniusCharpolyReverse B S f ℓ ν) = 0) :
    IsAlgebraic ℚ μ ∧ ∀ ι : ℚ⟮μ⟯ →+* ℂ,
      ‖ι (AdjoinSimple.gen ℚ μ)‖ = (Fintype.card k : ℝ) ^ ((ν : ℝ) / 2) := by
  have h0 : μ ≠ 0 := by
    rintro rfl
    rw [inv_zero] at hμ
    exact aeval_zero_reverse_charpoly_ne_zero _ hμ
  have hμ' := (LinearMap.aeval_inv_reverse_charpoly_eq_zero_iff _ h0).1 hμ
  exact satisfiesWeilEstimate B S f ν μ hμ'

end Weil
