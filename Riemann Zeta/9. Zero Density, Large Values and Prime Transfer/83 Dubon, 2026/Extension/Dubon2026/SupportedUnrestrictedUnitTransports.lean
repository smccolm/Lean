import Dubon2026.NumberFieldLocalUnitTransports
import Dubon2026.TransportedOrbitDecomposition
import Dubon2026.SUnitLogPlaceAction

/-! # Original unrestricted idele factors on the original S-unit place set

The unrestricted completion unit groups are indexed by exactly the same
infinite and supported finite places as the proved S-unit Herbrand factor.
Their transport laws are derived from the original completion maps. This
avoids a separate orbit reindexing assumption in DUB-17's norm-index chain.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- The original completion unit module at an original unrestricted place. -/
def supportedUnrestrictedUnitModule : SUnitLogPlace L S → Type
  | Sum.inl v => Additive v.Completionˣ
  | Sum.inr v => Additive (v.val.adicCompletion L)ˣ

instance (p : SUnitLogPlace L S) : AddCommGroup (supportedUnrestrictedUnitModule L S p) := by
  cases p <;> dsimp only [supportedUnrestrictedUnitModule] <;> infer_instance

/-- The original completion-unit transport on exactly the S-unit place indexing set. -/
def supportedUnrestrictedUnitTransport :
    letI := sUnitLogPlaceAction K L S hS
    ∀ (σ : Gal(L/K)) (p q : SUnitLogPlace L S), σ • p = q →
      supportedUnrestrictedUnitModule L S p ≃ₗ[ℤ] supportedUnrestrictedUnitModule L S q := by
  letI := sUnitLogPlaceAction K L S hS
  letI := numberFieldGaloisPlaceAction K L
  intro σ p q h
  cases p with
  | inl v =>
    cases q with
    | inl w => exact numberFieldInfiniteUnitTransport K L σ v w (Sum.inl.inj h)
    | inr w => cases h
  | inr v =>
    cases q with
    | inl w => cases h
    | inr w =>
      exact numberFieldFiniteUnitTransport K L σ v.val w.val
        (congrArg Subtype.val (Sum.inr.inj h))

/-- The actual unrestricted unit transports satisfy the identity law. -/
theorem supportedUnrestrictedUnitTransport_one :
    letI := sUnitLogPlaceAction K L S hS
    ∀ (p : SUnitLogPlace L S) (x : supportedUnrestrictedUnitModule L S p),
      supportedUnrestrictedUnitTransport K L S hS 1 p p (one_smul Gal(L/K) p) x = x := by
  intro p x
  cases p with
  | inl v => exact numberFieldInfiniteUnitTransport_one K L v x
  | inr v => exact numberFieldFiniteUnitTransport_one K L v.val x

/-- The actual unrestricted unit transports satisfy the original composition law. -/
theorem supportedUnrestrictedUnitTransport_mul :
    letI := sUnitLogPlaceAction K L S hS
    ∀ (σ τ : Gal(L/K)) (p q r : SUnitLogPlace L S) (hτ : τ • p = q) (hσ : σ • q = r)
      (hστ : (σ * τ) • p = r) (x : supportedUnrestrictedUnitModule L S p),
      supportedUnrestrictedUnitTransport K L S hS (σ * τ) p r hστ x =
        supportedUnrestrictedUnitTransport K L S hS σ q r hσ
          (supportedUnrestrictedUnitTransport K L S hS τ p q hτ x) := by
  intro σ τ p q r hτ hσ hστ x
  cases p with
  | inl v =>
    cases q with
    | inr u => cases hτ
    | inl u =>
      cases r with
      | inr w => cases hσ
      | inl w =>
        exact numberFieldInfiniteUnitTransport_mul K L σ τ v u w
          (Sum.inl.inj hτ) (Sum.inl.inj hσ) (Sum.inl.inj hστ) x
  | inr v =>
    cases q with
    | inl u => cases hτ
    | inr u =>
      cases r with
      | inl w => cases hσ
      | inr w =>
        exact numberFieldFiniteUnitTransport_mul K L σ τ v.val u.val w.val
          (congrArg Subtype.val (Sum.inr.inj hτ))
          (congrArg Subtype.val (Sum.inr.inj hσ))
          (congrArg Subtype.val (Sum.inr.inj hστ)) x

/-- The original unrestricted completion-unit product with its actual Galois action. -/
def supportedUnrestrictedUnitRep : Rep ℤ Gal(L/K) := by
  letI := sUnitLogPlaceAction K L S hS
  exact transportedPiRep ℤ Gal(L/K) (SUnitLogPlace L S) (supportedUnrestrictedUnitModule L S)
    (supportedUnrestrictedUnitTransport K L S hS)
    (supportedUnrestrictedUnitTransport_one K L S hS)
    (supportedUnrestrictedUnitTransport_mul K L S hS)

end
end Dubon2026
