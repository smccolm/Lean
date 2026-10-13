/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the retained upstream LICENSE.
The mixed-place independence argument is adapted from ClassFieldTheory
dc55774a7fe03e742f2b4c6114aab5e7d01edfb1,
Nyll/ClassFieldTheory/AlgebraicNumberTheory/RayClass/Ideal.lean.
-/
import Dubon2026.FiniteIndependentAbsoluteValueApproximation
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

/-! # Approximation in the actual finite and infinite completions

One principal correction must meet local norm conditions at all exceptional
finite places and every archimedean place. This provides that exact density
input for the prime-selection argument on DUB-17's global norm-index route.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField
variable (K : Type) [Field K] [NumberField K]

/-- The actual finite and archimedean absolute values are inequivalent. -/
theorem original_adicAbv_not_isEquiv_infinitePlace
    (v : HeightOneSpectrum (𝓞 K)) (w : InfinitePlace K) :
    ¬ (NumberField.HeightOneSpectrum.adicAbv K v).IsEquiv w.1 := by
  intro h
  have hle := h.le_one_iff.mp (NumberField.HeightOneSpectrum.adicAbv_natCast_le_one K v 2)
  have hw : w.1 ((2 : ℕ) : K) = (2 : ℝ) := InfinitePlace.map_natCast w 2
  rw [hw] at hle
  norm_num at hle

/-- The original finite support together with every original infinite place. -/
abbrev OriginalApproximationPlace (S : Finset (HeightOneSpectrum (𝓞 K))) :=
  S ⊕ InfinitePlace K

/-- The original absolute value at a coordinate of the approximation family. -/
def originalApproximationAbsoluteValue (S : Finset (HeightOneSpectrum (𝓞 K))) :
    OriginalApproximationPlace K S → AbsoluteValue K ℝ
  | Sum.inl v => NumberField.HeightOneSpectrum.adicAbv K v.1
  | Sum.inr w => w.1

/-- The actual original completion at each approximation coordinate. -/
def OriginalApproximationCompletion (S : Finset (HeightOneSpectrum (𝓞 K))) :
    OriginalApproximationPlace K S → Type
  | Sum.inl v => v.1.adicCompletion K
  | Sum.inr w => w.Completion

/-- Each coordinate carries its original normed-field structure. -/
instance originalApproximationNormedField (S : Finset (HeightOneSpectrum (𝓞 K)))
    (i : OriginalApproximationPlace K S) : NormedField (OriginalApproximationCompletion K S i) := by
  cases i <;> dsimp [OriginalApproximationCompletion] <;> infer_instance

/-- Each original completion carries its original base-field algebra. -/
instance originalApproximationAlgebra (S : Finset (HeightOneSpectrum (𝓞 K)))
    (i : OriginalApproximationPlace K S) : Algebra K (OriginalApproximationCompletion K S i) := by
  cases i with
  | inl v => exact inferInstanceAs (Algebra K (v.1.adicCompletion K))
  | inr w => exact inferInstanceAs (Algebra K w.Completion)

/-- The actual mixed family is pairwise independent and nontrivial. -/
theorem originalApproximationAbsoluteValue_independent
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (∀ i, (originalApproximationAbsoluteValue K S i).IsNontrivial) ∧
      Pairwise fun i j => ¬ (originalApproximationAbsoluteValue K S i).IsEquiv
        (originalApproximationAbsoluteValue K S j) := by
  constructor
  · intro i
    cases i with
    | inl v => exact original_adicAbv_isNontrivial K v.1
    | inr w => exact w.isNontrivial
  · intro i j hij
    cases i with
    | inl v =>
      cases j with
      | inl w =>
        apply original_adicAbv_not_isEquiv_of_ne K
        intro h
        exact hij (congrArg Sum.inl (Subtype.ext h))
      | inr w => exact original_adicAbv_not_isEquiv_infinitePlace K v.1 w
    | inr v =>
      cases j with
      | inl w => exact fun h => original_adicAbv_not_isEquiv_infinitePlace K w.1 v h.symm
      | inr w =>
        intro h
        exact hij (congrArg Sum.inr (InfinitePlace.eq_iff_isEquiv.mpr h))

/-- The original number field is simultaneously dense in these actual completions. -/
theorem original_mixedCompletions_dense (S : Finset (HeightOneSpectrum (𝓞 K))) :
    DenseRange (fun x : K => fun i : OriginalApproximationPlace K S =>
      algebraMap K (OriginalApproximationCompletion K S i) x) := by
  let abv := originalApproximationAbsoluteValue K S
  let f := fun i => (algebraMap K (OriginalApproximationCompletion K S i)).comp
    (WithAbs.equiv (abv i)).toRingHom
  have hf (i : OriginalApproximationPlace K S) : Isometry (f i) := by
    apply AddMonoidHomClass.isometry_of_norm
    intro x
    cases i with
    | inl v =>
      change ‖NumberField.FinitePlace.embedding v.1 (WithAbs.equiv (abv (.inl v)) x)‖ = ‖x‖
      rw [NumberField.FinitePlace.norm_embedding]
      rfl
    | inr w =>
      exact UniformSpace.Completion.norm_coe x
  have hd (i : OriginalApproximationPlace K S) : DenseRange (f i) := by
    cases i with
    | inl v =>
      intro x
      apply (v.1.denseRange_algebraMap K).mono
      rintro y ⟨r, rfl⟩
      exact ⟨(WithAbs.equiv (abv (.inl v))).symm r, rfl⟩
    | inr w =>
      exact UniformSpace.Completion.denseRange_coe
  obtain ⟨hn, hi⟩ := originalApproximationAbsoluteValue_independent K S
  exact (DenseRange.piMap hd).comp (finite_independent_absoluteValues_dense K abv hn hi)
    (continuous_pi fun i => (hf i).continuous.comp (continuous_apply i))

end
end Dubon2026
