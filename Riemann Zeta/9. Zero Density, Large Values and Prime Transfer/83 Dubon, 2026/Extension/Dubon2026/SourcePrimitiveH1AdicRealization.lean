import Dubon2026.SourcePrimitiveCompatibleH1AdicData
import Dubon2026.SourcePrimitiveResidualCharacteristic

/-! DUB-17/18 -> original all-weight characteristic-zero Galois association
-> compatible finite-level Hecke realizations. The actual original primitive
form and prescribed rational prime supply their coefficient completion,
finite residue field and compatible original H1 characters at every adic
precision. No eigencharacter, coefficient compatibility or local finiteness
hypothesis is supplied. Geometric Galois realization remains open.
-/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel
variable {Q : ℕ} [NeZero Q] {k : ℤ}

/-- Every original primitive form of weight at least two has compatible
finite adic H1 Hecke characters over its actual coefficient completion at
each prescribed rational prime, with the original Fourier values. -/
theorem sourcePrimitive_exists_compatibleH1AdicRealization
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
        sourcePrimitiveCompatibleH1AdicData f hk τ := by
  letI := sourcePrimitiveCoefficientField_numberField f hk
  letI := rationalPrimeLocalField_charZero p hp
  let F := rationalPrimeLocalField p hp
  let L := commonCoefficientField (sourcePrimitiveCoefficientField f) F
  have hc := sourcePrimitive_exists_residualHeckeCharacter_charP f hk p hp
  dsimp only at hc
  obtain ⟨u, v, hu, hv, hext, hdim, hchar, hfinite, τ, _, _⟩ := hc
  letI : UniformSpace L := u
  letI : ValuativeRel L := v
  letI : IsUniformAddGroup L := hu
  letI : IsNonarchimedeanLocalField L := hv
  letI : Finite 𝓀[L] := hfinite
  exact ⟨u, v, hu, hv, hext, hdim, hchar, hfinite, τ,
    sourcePrimitiveCompatibleH1AdicData_of_local f hk τ⟩

end
end Dubon2026
