import Dubon2026.SourceGammaOneConstructedLocalTrace
import Dubon2026.SourceActualTraceAlgebra

/-! DUB-17/18 -> original all-weight characteristic-zero association ->
actual rank-two realization. The original modular form constructs its
finite local coefficient field, continuous original field-valued traces,
and a genuine trace algebra with a group action, faithful trace pairing
and scalar idempotent corners. Actual two-dimensional matrices and their
continuity remain separate requirements. -/
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

/-- The original modular form constructs its actual characteristic-zero trace
algebra over a genuine finite local coefficient field, retaining the exact
Fourier norm-Frobenius values. No trace, algebra or representation is supplied. -/
theorem exists_gammaOne_original_local_trace_algebra
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (hlarge : 3 < p) :
    letI := sourcePrimitiveCoefficientField_numberField f hk
    letI := rationalPrimeLocalField_charZero p (Fact.out : p.Prime)
    let F := rationalPrimeLocalField p (Fact.out : p.Prime)
    let L := commonCoefficientField (sourcePrimitiveCoefficientField f) F
    ∃ (u : UniformSpace L) (_ : ValuativeRel L),
      letI : TopologicalSpace L := u.toTopologicalSpace
      IsUniformAddGroup L ∧ IsNonarchimedeanLocalField L ∧
      (ValuativeRel.valuation F).HasExtension (ValuativeRel.valuation L) ∧
      FiniteDimensional F L ∧ CharP 𝓀[L] p ∧
      ∃ τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] L,
    ∃ (t : (Qbar ≃ₐ[ℚ] Qbar) → L)
      (D : (Qbar ≃ₐ[ℚ] Qbar) →* L),
      Continuous t ∧ Continuous D ∧ t 1 = 2 ∧
      (∀ g h, t (g * h) = t (h * g)) ∧
      (∀ g h, t g * t h = t (g * h) + t (g * h⁻¹) * D h) ∧
      (∀ (q : ℕ) (hq : q.Prime), ¬q ∣ Q * p →
        ∀ (e : Qbar →ₐ[ℚ] rationalPrimeLocalClosure q hq)
          (φ : Gal(rationalPrimeLocalClosure q hq/rationalPrimeLocalField q hq)),
          (∀ z : IsLocalRing.ResidueField (algebraicLocalIntegerRing
            (rationalPrimeLocalClosure q hq)), φ • z = z ^ q) →
          t (embeddedNormalGaloisRestriction e φ) =
            τ (sourcePrimitiveFieldCoefficient f q) ∧
          D (embeddedNormalGaloisRestriction e φ) = (q : L) ^ Int.toNat (k - 1)) ∧
      ∃ (A : Type) (_ : Ring A) (_ : Algebra L A) (T : A →ₗ[L] L)
        (ρ : (Qbar ≃ₐ[ℚ] Qbar) →* Aˣ),
        T 1 = 2 ∧ (∀ g, T (ρ g : A) = t g) ∧
        (∀ x y, T (x * y) = T (y * x)) ∧
        (∀ x, (∀ y, T (x * y) = 0) → x = 0) ∧
        (∀ x y, x * y + y * x - T x • y - T y • x +
          (T x * T y - T (x * y)) • (1 : A) = 0) ∧
        ∀ e : A, e * e = e → T e = 1 → ∀ x, e * x * e = T (e * x) • e := by
  letI := sourcePrimitiveCoefficientField_numberField f hk
  letI := rationalPrimeLocalField_charZero p (Fact.out : p.Prime)
  let F := rationalPrimeLocalField p (Fact.out : p.Prime)
  let L := commonCoefficientField (sourcePrimitiveCoefficientField f) F
  have hs := exists_gammaOne_original_constructed_local_trace Q p f hk hlarge
  dsimp only at hs
  obtain ⟨u, v, hu, hv, hext, hfin, hchar, τ, t, D, ht, hD, hOne, hCyc, hProd, hFrob⟩ := hs
  letI : UniformSpace L := u
  letI : TopologicalSpace L := u.toTopologicalSpace
  letI : ValuativeRel L := v
  let ti : (Qbar ≃ₐ[ℚ] Qbar) → L := fun g => (t g : L)
  let Di : (Qbar ≃ₐ[ℚ] Qbar) →* L :=
    (ValuativeRel.valuation L).integer.subtype.toMonoidHom.comp D
  have hti : Continuous ti := continuous_subtype_val.comp ht
  have hDi : Continuous Di := continuous_subtype_val.comp hD
  have ho : ti 1 = 2 := congrArg (fun x : 𝒪[L] => (x : L)) hOne
  have hc : ∀ g h, ti (g * h) = ti (h * g) :=
    fun g h => congrArg (fun x : 𝒪[L] => (x : L)) (hCyc g h)
  have hp : ∀ g h, ti g * ti h = ti (g * h) + ti (g * h⁻¹) * Di h :=
    fun g h => congrArg (fun x : 𝒪[L] => (x : L)) (hProd g h)
  refine ⟨u, v, hu, hv, hext, hfin, hchar, τ, ti, Di, hti, hDi, ho, hc, hp, ?_,
    exists_algebra_of_trace_determinant ti Di ho hc hp⟩
  intro q hq haway e φ hφ
  have hf := hFrob q hq haway e φ hφ
  exact ⟨congrArg (fun x : 𝒪[L] => (x : L)) hf.1,
    congrArg (fun x : 𝒪[L] => (x : L)) hf.2⟩

end
end Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
