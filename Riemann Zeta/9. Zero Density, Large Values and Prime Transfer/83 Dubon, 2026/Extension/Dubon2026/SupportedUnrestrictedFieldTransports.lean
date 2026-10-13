import Dubon2026.SupportedUnrestrictedUnitTransports

/-! # The actual completion fields underlying the unrestricted unit factors

The fields and transports are the original infinite and finite
completions at the original S-unit places. Their global-field embeddings
and coherent action laws will prove faithfulness of the actual local
stabilizers, allowing existing Hilbert90 to discharge DUB-17's local H1
input before the remaining H2/completion comparison is developed.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- The actual completion field at an original unrestricted place. -/
def supportedUnrestrictedCompletion : SUnitLogPlace L S → Type
  | Sum.inl v => v.Completion
  | Sum.inr v => v.val.adicCompletion L

instance (p : SUnitLogPlace L S) : Field (supportedUnrestrictedCompletion L S p) := by
  cases p <;> dsimp only [supportedUnrestrictedCompletion] <;> infer_instance

instance (p : SUnitLogPlace L S) : Algebra L (supportedUnrestrictedCompletion L S p) := by
  cases p with
  | inl v => exact inferInstanceAs (Algebra L v.Completion)
  | inr v => exact inferInstanceAs (Algebra L (v.val.adicCompletion L))

/-- The original completed field transport on the exact original S-unit place set. -/
def supportedUnrestrictedFieldTransport :
    letI := sUnitLogPlaceAction K L S hS
    ∀ (σ : Gal(L/K)) (p q : SUnitLogPlace L S), σ • p = q →
      supportedUnrestrictedCompletion L S p ≃+* supportedUnrestrictedCompletion L S q := by
  letI := sUnitLogPlaceAction K L S hS
  intro σ p q h
  cases p with
  | inl v =>
    cases q with
    | inl w => exact numberFieldGaloisArchimedeanTransport K L σ v w (Sum.inl.inj h)
    | inr w => cases h
  | inr v =>
    cases q with
    | inl w => cases h
    | inr w =>
      exact numberFieldGaloisLocalTransport K L σ v.val w.val
        (congrArg Subtype.val (Sum.inr.inj h))

/-- Original completion transport extends the literal original global automorphism. -/
theorem supportedUnrestrictedFieldTransport_algebraMap :
    letI := sUnitLogPlaceAction K L S hS
    ∀ (σ : Gal(L/K)) (p q : SUnitLogPlace L S) (h : σ • p = q) (x : L),
      supportedUnrestrictedFieldTransport K L S hS σ p q h
        (algebraMap L (supportedUnrestrictedCompletion L S p) x) =
      algebraMap L (supportedUnrestrictedCompletion L S q) (σ x) := by
  intro σ p q h x
  cases p with
  | inl v =>
    cases q with
    | inl w => exact numberFieldGaloisArchimedeanTransport_algebraMap K L σ v w (Sum.inl.inj h) x
    | inr w => cases h
  | inr v =>
    cases q with
    | inl w => cases h
    | inr w =>
      exact numberFieldGaloisLocalTransport_algebraMap K L σ v.val w.val
        (congrArg Subtype.val (Sum.inr.inj h)) x

/-- Identity is identity on each actual unrestricted completion field. -/
theorem supportedUnrestrictedFieldTransport_one :
    letI := sUnitLogPlaceAction K L S hS
    ∀ (p : SUnitLogPlace L S) (x : supportedUnrestrictedCompletion L S p),
      supportedUnrestrictedFieldTransport K L S hS 1 p p (one_smul Gal(L/K) p) x = x := by
  intro p x
  cases p with
  | inl v => exact numberFieldGaloisArchimedeanTransport_one K L v x
  | inr v => exact numberFieldGaloisLocalTransport_one K L v.val x

/-- The original unrestricted completion maps satisfy composition on their actual field elements. -/
theorem supportedUnrestrictedFieldTransport_mul :
    letI := sUnitLogPlaceAction K L S hS
    ∀ (σ τ : Gal(L/K)) (p q r : SUnitLogPlace L S) (hτ : τ • p = q) (hσ : σ • q = r)
      (hστ : (σ * τ) • p = r) (x : supportedUnrestrictedCompletion L S p),
      supportedUnrestrictedFieldTransport K L S hS (σ * τ) p r hστ x =
        supportedUnrestrictedFieldTransport K L S hS σ q r hσ
          (supportedUnrestrictedFieldTransport K L S hS τ p q hτ x) := by
  intro σ τ p q r hτ hσ hστ x
  cases p with
  | inl v =>
    cases q with
    | inr u => cases hτ
    | inl u =>
      cases r with
      | inr w => cases hσ
      | inl w =>
        exact numberFieldGaloisArchimedeanTransport_mul K L σ τ v u w
          (Sum.inl.inj hτ) (Sum.inl.inj hσ) (Sum.inl.inj hστ) x
  | inr v =>
    cases q with
    | inl u => cases hτ
    | inr u =>
      cases r with
      | inl w => cases hσ
      | inr w =>
        exact numberFieldGaloisLocalTransport_mul K L σ τ v.val u.val w.val
          (congrArg Subtype.val (Sum.inr.inj hτ))
          (congrArg Subtype.val (Sum.inr.inj hσ))
          (congrArg Subtype.val (Sum.inr.inj hστ)) x

end
end Dubon2026
