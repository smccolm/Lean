import Dubon2026.SourceGammaOneOriginalAdicInertia
import Dubon2026.SourceAdicQuotientContinuity
import Dubon2026.SourceAbsoluteCyclicFrobeniusEquality
import Dubon2026.CompactSeparatedLocalAdicTopology
import Mathlib.NumberTheory.LocalField.Basic

/-! DUB-17/18 -> original unramified rank-two association -> complete trace invariance.
Every positive quotient of the existing original continuous trace agrees
with the original inertia-invariant finite witness by proved Frobenius
uniqueness. Native adic separation transfers its translate identity to the
complete coefficient ring, without rebuilding a compatible family. -/
namespace Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
noncomputable section
open scoped ValuativeRel
attribute [local instance] rationalPrimeLocalField_charZero
  rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric algebraicLocalIntegerAction
attribute [local instance 1100] rationalPrimeOriginalNormedField
local notation "Qbar" => AlgebraicClosure ℚ
private local instance : IsGalois ℚ Qbar := sourceRationalAlgebraicClosure_isGalois
variable (Q p : ℕ) [NeZero Q] [Fact p.Prime] {k : ℤ}

/-- The existing complete original trace is invariant under every actual
norm-inertia translate outside Q*p, from its original Fourier Frobenius values. -/
theorem originalPrimitiveLocalTrace_normInertia_translate
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (hlarge : 3 < p)
    {E : Type} [Field E] [CharZero E] [ValuativeRel E] [UniformSpace E]
    [IsUniformAddGroup E] [IsNonarchimedeanLocalField E] [CharP 𝓀[E] p]
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E)
    (t : (Qbar ≃ₐ[ℚ] Qbar) → 𝒪[E]) (ht : Continuous t)
    (hCyc : ∀ g h, t (g * h) = t (h * g))
    (hFrob : ∀ (q : ℕ) (hq : q.Prime), ¬q ∣ Q * p →
      ∀ (e : Qbar →ₐ[ℚ] rationalPrimeLocalClosure q hq)
        (φ : Gal(rationalPrimeLocalClosure q hq/rationalPrimeLocalField q hq)),
        (∀ z : IsLocalRing.ResidueField (algebraicLocalIntegerRing
          (rationalPrimeLocalClosure q hq)), φ • z = z ^ q) →
        t (embeddedNormalGaloisRestriction e φ) =
          ⟨τ (sourcePrimitiveFieldCoefficient f q),
            sourcePrimitiveCoefficient_valuation_le_one f hk τ q⟩)
    (q : ℕ) (hq : q.Prime) (haway : ¬q ∣ Q * p)
    (e : Qbar →ₐ[ℚ] rationalPrimeLocalClosure q hq)
    (g : Gal(rationalPrimeLocalClosure q hq/rationalPrimeLocalField q hq))
    (hg : g ∈ rationalPrimeNormInertia q hq) (σ : Qbar ≃ₐ[ℚ] Qbar) :
    t (embeddedNormalGaloisRestriction e g * σ) = t σ := by
  apply positiveAdic_ext (IsLocalRing.maximalIdeal 𝒪[E])
  intro n
  obtain ⟨tn, htn, hCn, hFn, hIn⟩ :=
    exists_gammaOne_original_adic_inertia_trace Q p n f hk hlarge τ
  let C := 𝒪[E] ⧸ (IsLocalRing.maximalIdeal 𝒪[E]) ^ (n + 1)
  let π := Ideal.Quotient.mk ((IsLocalRing.maximalIdeal 𝒪[E]) ^ (n + 1))
  letI : TopologicalSpace C := ⊥
  letI : DiscreteTopology C := ⟨rfl⟩
  have htm : Continuous (fun γ => π (t γ)) :=
    (continuous_positive_adic_quotient (IsLocalRing.maximalIdeal 𝒪[E])
      compactSeparatedLocalRing_isAdic n).comp ht
  have heq : (fun γ => π (t γ)) = tn :=
    absolute_continuous_cyclic_eq_of_norm_frobenius (fun γ => π (t γ)) tn htm htn
      (fun a b => congrArg π (hCyc a b)) hCn (Q * p).primeFactors (by
        intro r hr hrS i φ hφ
        have ha : ¬r ∣ Q * p := fun h => hrS (hr.mem_primeFactors' h)
        exact (congrArg π (hFrob r hr ha i φ hφ)).trans (hFn r hr ha i φ hφ).symm)
  exact (congrFun heq _).trans ((hIn q hq haway e g hg σ).trans (congrFun heq _).symm)

end
end Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
