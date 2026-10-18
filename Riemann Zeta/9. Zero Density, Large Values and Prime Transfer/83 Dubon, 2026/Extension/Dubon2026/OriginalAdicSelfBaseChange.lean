import Dubon2026.OriginalAdicBaseChangeMap

/-! The original completion map for an identity field inclusion is the
identity. This supplies the same-upper-completion tower required by the
actual rational-to-bottom-field invariant comparison in DUB-17. -/
namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField
attribute [-instance] UniformSpace.Completion.instSMul

variable (L : Type) [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L))

/-- The original prime lies over itself under the identity field inclusion. -/
local instance originalAdicSelfPrimeLiesOver :
    @Ideal.LiesOver (𝓞 L) _ (𝓞 L) _ (NumberField.inst_ringOfIntegersAlgebra L L)
      w.asIdeal w.asIdeal := ⟨by ext x; rfl⟩

/-- The completed original identity field map fixes every actual completion element. -/
theorem originalAdicBaseChangeMap_self (z : w.adicCompletion L) :
    originalAdicBaseChangeMap L L w w z = z := by
  apply UniformSpace.Completion.ext'
    (originalAdicBaseChangeMap_continuous L L w w) continuous_id
  intro x
  change originalAdicBaseChangeMap L L w w (algebraMap L (w.adicCompletion L) x.ofVal) =
    algebraMap L (w.adicCompletion L) x.ofVal
  exact originalAdicBaseChangeMap_algebraMap L L w w x.ofVal

end
end Dubon2026
