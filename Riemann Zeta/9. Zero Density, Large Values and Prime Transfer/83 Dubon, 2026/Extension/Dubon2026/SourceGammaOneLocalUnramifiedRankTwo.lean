import Dubon2026.SourceGammaOneLocalRankTwo
import Dubon2026.SourceGammaOneLocalTraceInertia
import Dubon2026.SourceOriginalTraceMatrixKernel

/-! DUB-17/18 -> original all-weight association -> actual unramified rank-two matrices.
The existing complete original trace is invariant under norm inertia.
The kernel-retaining matrix construction converts this into actual trivial
inertia action, alongside the original Fourier Frobenius values and oddness.
The original form supplies every trace and matrix input. -/
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

/-- The original primitive form supplies its continuous rank-two realization
in every genuine local coefficient field of residue characteristic above three,
with trivial action of every original norm-inertia subgroup outside Q*p. -/
theorem exists_gammaOne_original_local_unramified_rankTwo
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (hlarge : 3 < p)
    {E : Type} [Field E] [CharZero E] [ValuativeRel E] [UniformSpace E]
    [IsUniformAddGroup E] [IsNonarchimedeanLocalField E] [CharP 𝓀[E] p]
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E) :
    ∃ ρ : (Qbar ≃ₐ[ℚ] Qbar) →* Matrix.GeneralLinearGroup (Fin 2) E,
      Continuous ρ ∧
      (∀ (q : ℕ) (hq : q.Prime), ¬q ∣ Q * p →
        ∀ (e : Qbar →ₐ[ℚ] rationalPrimeLocalClosure q hq)
          (φ : Gal(rationalPrimeLocalClosure q hq/rationalPrimeLocalField q hq)),
          (∀ z : IsLocalRing.ResidueField (algebraicLocalIntegerRing
            (rationalPrimeLocalClosure q hq)), φ • z = z ^ q) →
          Matrix.trace (ρ (embeddedNormalGaloisRestriction e φ)).val =
            τ (sourcePrimitiveFieldCoefficient f q) ∧
          (ρ (embeddedNormalGaloisRestriction e φ)).val.det = (q : E) ^ Int.toNat (k - 1)) ∧
      (∀ e : Qbar →ₐ[ℚ] ℂ,
        (ρ (sourceAbsoluteComplexConjugation e)).val.det = -1 ∧
        Matrix.trace (ρ (sourceAbsoluteComplexConjugation e)).val = 0) ∧
      ∀ (q : ℕ) (hq : q.Prime), ¬q ∣ Q * p →
        ∀ (e : Qbar →ₐ[ℚ] rationalPrimeLocalClosure q hq)
          (g : Gal(rationalPrimeLocalClosure q hq/rationalPrimeLocalField q hq)),
          g ∈ rationalPrimeNormInertia q hq → ρ (embeddedNormalGaloisRestriction e g) = 1 := by
  obtain ⟨t, D, ht, hD, hOne, hCyc, hProd, hFrob⟩ :=
    exists_gammaOne_original_local_trace Q p f hk hlarge τ
  let ti : (Qbar ≃ₐ[ℚ] Qbar) → E := fun g => (t g : E)
  let Di : (Qbar ≃ₐ[ℚ] Qbar) →* E :=
    (ValuativeRel.valuation E).integer.subtype.toMonoidHom.comp D
  have hti : Continuous ti := continuous_subtype_val.comp ht
  have ho : ti 1 = 2 := congrArg (fun x : 𝒪[E] => (x : E)) hOne
  have hc : ∀ g h, ti (g * h) = ti (h * g) :=
    fun g h => congrArg (fun x : 𝒪[E] => (x : E)) (hCyc g h)
  have hp : ∀ g h, ti g * ti h = ti (g * h) + ti (g * h⁻¹) * Di h :=
    fun g h => congrArg (fun x : 𝒪[E] => (x : E)) (hProd g h)
  have hodd (e : Qbar →ₐ[ℚ] ℂ) :
      Di (sourceAbsoluteComplexConjugation e) = -1 ∧ ti (sourceAbsoluteComplexConjugation e) = 0 := by
    have hod := originalPrimitiveLocalDeterminant_odd Q p f hk D hD
      (fun q hq ha i φ hφ => (hFrob q hq ha i φ hφ).2) e
    have hd : Di (sourceAbsoluteComplexConjugation e) = -1 :=
      congrArg (fun x : 𝒪[E] => (x : E)) hod
    exact ⟨hd, traceDeterminant_odd_involution_zero ti Di ho hp
      (sourceAbsoluteComplexConjugation e) (sourceAbsoluteComplexConjugation_sq e) hd⟩
  let ec : Qbar →ₐ[ℚ] ℂ := IsAlgClosed.lift
  obtain ⟨ρ, hρ, hmatrix, hkernel⟩ := exists_continuous_matrix_of_original_trace_kernel ti Di hti ho hp
    (sourceAbsoluteComplexConjugation ec) (sourceAbsoluteComplexConjugation_sq ec)
    (hodd ec).2 (exists_spanning_algebra_of_trace_determinant ti Di ho hc hp)
  refine ⟨ρ, hρ, ?_, ?_, ?_⟩
  · intro q hq ha e φ hφ
    have hf := hFrob q hq ha e φ hφ
    exact ⟨(hmatrix _).1.trans (congrArg (fun x : 𝒪[E] => (x : E)) hf.1),
      (hmatrix _).2.trans (congrArg (fun x : 𝒪[E] => (x : E)) hf.2)⟩
  · intro e
    exact ⟨(hmatrix _).2.trans (hodd e).1, (hmatrix _).1.trans (hodd e).2⟩
  · intro q hq haway e g hg
    apply hkernel
    intro σ
    exact congrArg (fun x : 𝒪[E] => (x : E))
      (originalPrimitiveLocalTrace_normInertia_translate Q p f hk hlarge τ t ht hCyc
        (fun r hr ha i φ hφ => (hFrob r hr ha i φ hφ).1) q hq haway e g hg σ)

end
end Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
