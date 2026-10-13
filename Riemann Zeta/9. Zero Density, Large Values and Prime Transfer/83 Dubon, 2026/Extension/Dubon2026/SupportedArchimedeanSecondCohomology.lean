import Dubon2026.SupportedCompletionNorms
import Dubon2026.FaithfulComplexFieldCohomology

/-! # Original archimedean orbit H2 orders

The pinned real/complex equivalences classify the original infinite
completions. Their actual completed transports are continuous and their
actual stabilizer actions faithful. The already proved real and complex
unit calculations therefore apply to the exact orbit coefficients in
DUB-17's original idele-class Herbrand formula.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
attribute [local instance] Units.mulDistribMulActionRight
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- The actual stabilizing completion transport is continuous for the original topology. -/
theorem supportedFieldTransport_continuous :
    letI := sUnitLogPlaceAction K L S hS
    ∀ (σ : Gal(L/K)) (p : SUnitLogPlace L S) (h : σ • p = p),
      Continuous (supportedUnrestrictedFieldTransport K L S hS σ p p h) := by
  intro σ p h
  cases p with
  | inl v => exact numberFieldGaloisArchimedeanTransport_continuous K L σ v v (Sum.inl.inj h)
  | inr v =>
    exact numberFieldGaloisLocalTransport_continuous K L σ v.val v.val
      (congrArg Subtype.val (Sum.inr.inj h))

/-- Each original infinite completion is actually real, or continuously isomorphic to the complex field. -/
theorem supportedInfiniteCompletion_real_or_complex (p : SUnitLogPlace L S) (hp : p.isLeft) :
    Nonempty (supportedUnrestrictedCompletion L S p ≃+* ℝ) ∨
      ∃ e : supportedUnrestrictedCompletion L S p ≃+* ℂ, Continuous e ∧ Continuous e.symm := by
  cases p with
  | inl v =>
    rcases v.isReal_or_isComplex with hv | hv
    · exact Or.inl ⟨InfinitePlace.Completion.ringEquivRealOfIsReal hv⟩
    · exact Or.inr ⟨InfinitePlace.Completion.ringEquivComplexOfIsComplex hv,
        (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).continuous,
        (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).symm.continuous⟩
  | inr v => cases hp

variable [FiniteDimensional K L] [IsCyclic Gal(L/K)]

/-- The exact original archimedean orbit coefficient has finite H2 of its actual stabilizer order. -/
theorem supportedArchimedeanOrbitPoint_second_cohomology_order :
    letI := IsCyclic.commGroup (α := Gal(L/K))
    letI := sUnitLogPlaceAction K L S hS
    ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S),
      ω.out.isLeft →
      Finite (groupCohomology (supportedUnrestrictedOrbitPointRep K L S hS ω) 2) ∧
      Nat.card (groupCohomology (supportedUnrestrictedOrbitPointRep K L S hS ω) 2) =
        Nat.card (MulAction.stabilizer Gal(L/K) ω.out) := by
  letI := IsCyclic.commGroup (α := Gal(L/K))
  letI := sUnitLogPlaceAction K L S hS
  intro ω hω
  let H := MulAction.stabilizer Gal(L/K) (permutationOrbitPoint Gal(L/K) (SUnitLogPlace L S) ω)
  let F := supportedUnrestrictedCompletion L S ω.out
  letI := supportedUnrestrictedOrbitFieldAction K L S hS ω
  letI : FaithfulSMul H F := supportedUnrestrictedOrbitField_faithful K L S hS ω
  have hl : Finite (groupCohomology (Rep.ofMulDistribMulAction H Fˣ) 2) ∧
      Nat.card (groupCohomology (Rep.ofMulDistribMulAction H Fˣ) 2) = Nat.card H := by
    rcases supportedInfiniteCompletion_real_or_complex L S ω.out hω with hr | hc
    · obtain ⟨e⟩ := hr
      exact faithfulRealField_second_cohomology_order H F e
    · obtain ⟨e, he, hei⟩ := hc
      apply faithfulComplexField_second_cohomology_order H F e
      intro σ
      exact he.comp ((supportedFieldTransport_continuous K L S hS σ.val ω.out
        (congrArg Subtype.val σ.property)).comp hei)
  let e : groupCohomology (supportedUnrestrictedOrbitPointRep K L S hS ω) 2 ≅
      groupCohomology (Rep.ofMulDistribMulAction H Fˣ) 2 :=
    (groupCohomology.functor ℤ H 2).mapIso (supportedUnrestrictedOrbitUnitFieldIso K L S hS ω)
  let c := e.toLinearEquiv.toEquiv
  haveI : Finite (groupCohomology (Rep.ofMulDistribMulAction H Fˣ) 2) := hl.1
  refine ⟨Finite.of_equiv (groupCohomology (Rep.ofMulDistribMulAction H Fˣ) 2) c.symm, ?_⟩
  have he : H = MulAction.stabilizer Gal(L/K) ω.out :=
    permutationOrbitPoint_stabilizer Gal(L/K) (SUnitLogPlace L S) ω
  rw [← he]
  exact (Nat.card_congr c).trans hl.2

end
end Dubon2026
