import Dubon2026.SourcePrimitiveH1AdicOperatorKernel
import Dubon2026.SourcePrimitiveH1AdicRealization

/-! DUB-17/18 -> original all-weight adic association -> actual finite-level
Hecke specialization. The same original form and prescribed prime supply
compatible finite characters that respect all original prime-power H1
operator congruences. All coefficient-field, finite residue, character and
operator-kernel compatibility inputs are derived. Arithmetic geometric
realization and characteristic-zero Galois association remain required. -/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel
variable {Q : ℕ} [NeZero Q] {k : ℤ}
variable {E : Type} [Field E] [CharZero E] [ValuativeRel E]

/-- Compatible characters of the original H1 Hecke algebra that also
respect the literal original coefficient-reduced operator kernels. -/
def sourcePrimitiveH1AdicCongruenceData
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E) (p : ℕ) : Prop :=
  sourcePrimitiveCompatibleH1AdicData f hk τ ∧
    ∀ (n : ℕ) (T : sourceBinaryH1HeckeAlgebra Q (k - 2).toNat),
      (∀ x : groupCohomology.H1 (sourceBinaryCoefficientRep ℤ Q (k - 2).toNat),
        sourceBinaryH1Change (Int.castRingHom (ZMod (p ^ (n + 1))))
          Q (k - 2).toNat (T.val x) = 0) →
      sourcePrimitiveH1AdicQuotientCharacter f hk τ n T = 0

/-- Every original primitive form and prescribed rational prime supply
finite compatible H1 Hecke characters, with exact original Fourier values
and the original prime-power operator congruences fully discharged. -/
theorem sourcePrimitive_exists_congruentH1AdicRealization
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (p : ℕ) (hp : p.Prime) :
    letI := sourcePrimitiveCoefficientField_numberField f hk
    letI := rationalPrimeLocalField_charZero p hp
    let F := rationalPrimeLocalField p hp
    let L := commonCoefficientField (sourcePrimitiveCoefficientField f) F
    ∃ (_ : UniformSpace L) (_ : ValuativeRel L),
      IsUniformAddGroup L ∧ IsNonarchimedeanLocalField L ∧
      (ValuativeRel.valuation F).HasExtension (ValuativeRel.valuation L) ∧
      FiniteDimensional F L ∧ CharP 𝓀[L] p ∧ Finite 𝓀[L] ∧
      ∃ τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] L,
        sourcePrimitiveH1AdicCongruenceData f hk τ p := by
  letI := sourcePrimitiveCoefficientField_numberField f hk
  letI := rationalPrimeLocalField_charZero p hp
  let F := rationalPrimeLocalField p hp
  let L := commonCoefficientField (sourcePrimitiveCoefficientField f) F
  have hc := sourcePrimitive_exists_compatibleH1AdicRealization f hk p hp
  dsimp only at hc
  obtain ⟨u, v, hu, hv, hext, hdim, hchar, hfinite, τ, hdata⟩ := hc
  letI : UniformSpace L := u
  letI : ValuativeRel L := v
  letI : CharP 𝓀[L] p := hchar
  refine ⟨u, v, hu, hv, hext, hdim, hchar, hfinite, τ, hdata, ?_⟩
  intro n T hT
  exact sourcePrimitiveH1AdicQuotientCharacter_zero_of_operator f hk τ p n hp T hT

end
end Dubon2026
