import Dubon2026.SupportedCompletionNorms
import Dubon2026.FaithfulLocalFieldSecondCohomology

/-! # Actual finite-place stabilizer H2 orders

The original completed transport preserves the original valuation and norm.
The faithful local-field theorem therefore computes H2 on the exact original
orbit coefficient, with no local-field or cardinality premise. This discharges
the finite-place unrestricted H2 input in DUB-17's idele-class formula.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
attribute [local instance] Units.mulDistribMulActionRight
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- The actual finite-place stabilizing field transport preserves the original norm. -/
theorem supportedFiniteFieldTransport_norm :
    letI := sUnitLogPlaceAction K L S hS
    ∀ (σ : Gal(L/K)) (p : SUnitLogPlace L S) (h : σ • p = p)
      (_hp : p.isRight) (x : supportedUnrestrictedCompletion L S p),
      ‖supportedUnrestrictedFieldTransport K L S hS σ p p h x‖ = ‖x‖ := by
  intro σ p h hp x
  cases p with
  | inl v => cases hp
  | inr v =>
    change ‖numberFieldGaloisLocalTransport K L σ v.val v.val _ x‖ = ‖x‖
    simp only [Valued.toNormedField.norm_def]
    rw [(Valued.v.restrict_inj).mpr
      (numberFieldGaloisLocalTransport_valuation K L σ v.val v.val _ x)]
    rfl

variable [FiniteDimensional K L] [IsCyclic Gal(L/K)]

/-- The exact original finite-place orbit coefficient has finite H2 of its actual stabilizer order. -/
theorem supportedFiniteOrbitPoint_second_cohomology_order :
    letI := IsCyclic.commGroup (α := Gal(L/K))
    letI := sUnitLogPlaceAction K L S hS
    ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S),
      ω.out.isRight →
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
  letI : NontriviallyNormedField F := supportedFiniteCompletionNontrivialNorm L S ω.out hω
  haveI : IsUltrametricDist F := supportedFiniteCompletion_isUltrametric L S ω.out hω
  have hn (σ : H) (x : F) : ‖σ • x‖ = ‖x‖ :=
    supportedFiniteFieldTransport_norm K L S hS σ.val ω.out
      (congrArg Subtype.val σ.property) hω x
  obtain ⟨hfin, hcard⟩ := faithfulLocalField_second_cohomology_order H F hn
  let e : groupCohomology (supportedUnrestrictedOrbitPointRep K L S hS ω) 2 ≅
      groupCohomology (Rep.ofMulDistribMulAction H Fˣ) 2 :=
    (groupCohomology.functor ℤ H 2).mapIso (supportedUnrestrictedOrbitUnitFieldIso K L S hS ω)
  let c := e.toLinearEquiv.toEquiv
  haveI : Finite (groupCohomology (Rep.ofMulDistribMulAction H Fˣ) 2) := hfin
  refine ⟨Finite.of_equiv (groupCohomology (Rep.ofMulDistribMulAction H Fˣ) 2) c.symm, ?_⟩
  have he : H = MulAction.stabilizer Gal(L/K) ω.out := by
    exact permutationOrbitPoint_stabilizer Gal(L/K) (SUnitLogPlace L S) ω
  rw [← he]
  exact (Nat.card_congr c).trans hcard

end
end Dubon2026
