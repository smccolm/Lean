import Dubon2026.SupportedOrbitFieldFaithfulness
import Dubon2026.FaithfulFieldUnitHilbert90

/-! # The original orbit unit coefficient is the actual completion-field unit action

The identity on each actual completion unit is equivariant for the two
proved descriptions of its original transport. This is the original
coefficient comparison needed to apply the existing fixed-field Hilbert90
theorem to the exact local modules in DUB-17's idele-class formula.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
attribute [local instance] Units.mulDistribMulActionRight
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- The original local unit module is the actual unit group of its original completion field. -/
def supportedUnrestrictedUnitFieldEquiv (p : SUnitLogPlace L S) :
    supportedUnrestrictedUnitModule L S p ≃ₗ[ℤ] Additive (supportedUnrestrictedCompletion L S p)ˣ := by
  cases p with
  | inl v => exact LinearEquiv.refl ℤ (Additive v.Completionˣ)
  | inr v => exact LinearEquiv.refl ℤ (Additive (v.val.adicCompletion L)ˣ)

/-- The coefficient identification intertwines the original unit transport and original field transport. -/
theorem supportedUnrestrictedUnitFieldEquiv_transport :
    letI := sUnitLogPlaceAction K L S hS
    ∀ (σ : Gal(L/K)) (p q : SUnitLogPlace L S) (h : σ • p = q)
      (x : supportedUnrestrictedUnitModule L S p),
      supportedUnrestrictedUnitFieldEquiv L S q (supportedUnrestrictedUnitTransport K L S hS σ p q h x) =
        Additive.ofMul (Units.map (supportedUnrestrictedFieldTransport K L S hS σ p q h).toMonoidHom
          (supportedUnrestrictedUnitFieldEquiv L S p x).toMul) := by
  intro σ p q h x
  cases p with
  | inl v =>
    cases q with
    | inl w => rfl
    | inr w => cases h
  | inr v =>
    cases q with
    | inl w => cases h
    | inr w => rfl

variable [IsCyclic Gal(L/K)]

/-- The exact original local-stabilizer unit coefficient is the unit action of its faithful original completion-field action. -/
def supportedUnrestrictedOrbitUnitFieldIso :
    letI := IsCyclic.commGroup (α := Gal(L/K))
    letI := sUnitLogPlaceAction K L S hS
    ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S),
      letI := supportedUnrestrictedOrbitFieldAction K L S hS ω
      supportedUnrestrictedOrbitPointRep K L S hS ω ≅
        Rep.ofMulDistribMulAction
          (MulAction.stabilizer Gal(L/K) (permutationOrbitPoint Gal(L/K) (SUnitLogPlace L S) ω))
          (supportedUnrestrictedCompletion L S ω.out)ˣ := by
  letI := IsCyclic.commGroup (α := Gal(L/K))
  letI := sUnitLogPlaceAction K L S hS
  intro ω
  letI := supportedUnrestrictedOrbitFieldAction K L S hS ω
  apply Rep.mkIso
  refine Representation.Equiv.mk (supportedUnrestrictedUnitFieldEquiv L S ω.out) ?_
  intro σ
  apply LinearMap.ext
  intro x
  exact supportedUnrestrictedUnitFieldEquiv_transport K L S hS σ.val ω.out ω.out
    (congrArg Subtype.val σ.property) x

end
end Dubon2026
