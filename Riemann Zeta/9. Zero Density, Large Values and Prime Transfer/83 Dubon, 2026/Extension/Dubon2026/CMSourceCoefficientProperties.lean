import Dubon2026.CMSourceIntegralWeightContinuity
import Dubon2026.IntegralDominantTensorNontrivial

/-! Exact combined properties of the original source coefficient tensor.
The named proposition keeps later dependent field constructions small;
the theorem proves every displayed property from the original objects.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain Matrix
open scoped NumberField ValuativeRel

variable (K E : Type) [Field K] [NumberField K] [IsCMField K] [Field E] [CharZero E]
  (p : ℕ) (hp : p.Prime) [Algebra (rationalPrimeLocalField p hp) E]
  [ValuativeRel E] [UniformSpace E] [IsUniformAddGroup E] [IsNonarchimedeanLocalField E]
  [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension (ValuativeRel.valuation E)]
  (places : Set (HeightOneSpectrum (𝓞 K)))

/-- The exact finite-free, nonzero and canonical continuous-action conclusions for every original dominant source weight. This is a statement, with its proof below. -/
def CMSourceIntegralWeightProperties : Prop :=
  ∀ (n : ℕ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (lam : IntegralCoefficientEmbeddingIndex K E p hp places → Fin (n + 1) → ℤ),
    (∀ i, Antitone (lam i)) →
    Module.Finite 𝒪[E] (CMSourceIntegralWeight K E p hp places n lam) ∧
    Module.Free 𝒪[E] (CMSourceIntegralWeight K E p hp places n lam) ∧
    Nontrivial (CMSourceIntegralWeight K E p hp places n lam) ∧
    (letI : TopologicalSpace (CMSourceIntegralWeight K E p hp places n lam) :=
      moduleTopology 𝒪[E] (CMSourceIntegralWeight K E p hp places n lam)
    Continuous (fun x : cmFiniteAdelicIntegralLevel K H ×
        CMSourceIntegralWeight K E p hp places n lam =>
      cmSourceIntegralWeightRepresentation K E p hp places n H lam x.1 x.2))

/-- The actual integral coefficient tensor satisfies all the displayed properties, using the proved source constructions. -/
theorem cmSourceIntegralWeight_properties : CMSourceIntegralWeightProperties K E p hp places := by
  intro n H lam hlam
  obtain ⟨hfinite, hfree⟩ := cmSourceIntegralWeight_finite_free K E p hp places n lam
  refine ⟨hfinite, hfree, cmSourceIntegralWeight_nontrivial K E p hp places n lam hlam, ?_⟩
  letI : TopologicalSpace (CMSourceIntegralWeight K E p hp places n lam) :=
    moduleTopology 𝒪[E] (CMSourceIntegralWeight K E p hp places n lam)
  exact cmSourceIntegralWeightRepresentation_continuous K E p hp places n H lam

end
end Dubon2026
