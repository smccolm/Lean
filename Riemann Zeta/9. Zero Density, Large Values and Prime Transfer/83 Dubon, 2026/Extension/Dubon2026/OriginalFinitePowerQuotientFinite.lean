import Dubon2026.LocalFieldUnitPowerFinite
import Dubon2026.OriginalAdicUniformizerOrder

/-! # The original finite-completion power quotients are finite

The existing original local-field power theorem applies directly to the
original adic completion with its proved proper topology and norm valuation.
This removes the finite-place finiteness premise from DUB-17's actual local
power product and subsequent class-quotient cardinal comparison. Its precise
numerical local index is a separate remaining obligation.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField
variable (K : Type) [Field K] [NumberField K]

/-- Every original finite-place unit quotient by positive powers is finite, in the original completion. -/
theorem originalFinitePowerQuotient_finite (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ) (hn : 0 < n) :
    Finite ((v.adicCompletion K)ˣ ⧸ (powMonoidHom n : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range) := by
  let F := v.adicCompletion K
  letI : NontriviallyNormedField F := Valued.toNontriviallyNormedField F (WithZero (Multiplicative ℤ))
  haveI : ProperSpace F := original_adicCompletion_properSpace K v
  letI : ValuativeRel F := ValuativeRel.ofValuation (NormedField.valuation (K := F))
  haveI : IsNonarchimedeanLocalField F := normValuation_isNonarchimedeanLocalField F
  have hnF : (n : F) ≠ 0 := by
    have h := (algebraMap K F).injective.ne (Nat.cast_ne_zero.mpr hn.ne' : (n : K) ≠ 0)
    simpa only [map_natCast, map_zero] using h
  exact localField_unitPower_quotient_finite F n hnF

end
end Dubon2026
