import Dubon2026.CMFiniteAdelicIntegralLocalMap

/-! # Equality in the original integral local matrix group

Forgetting integrality is injective, so the existing original-place
projection identifies the integral evaluation required by the source
unitary level section for DUB-17.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField

/-- Equality of the original local matrices after inclusion determines the original integral evaluation. -/
theorem cmFiniteAdelicIntegralLocalMap_eq_of_projection
    (K : Type) [Field K] [NumberField K] [IsCMField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι K) (v : HeightOneSpectrum (𝓞 K))
    (M : cmFiniteAdelicIntegralLevel K H)
    (g : (Matrix ι ι (Valued.integer (v.adicCompletion K)))ˣ)
    (h : numberFieldFiniteAdelicMatrixProjection K ι v M.val.val =
      Units.map (Valued.integer (v.adicCompletion K)).subtype.mapMatrix.toMonoidHom g) :
    cmFiniteAdelicIntegralLocalMap K H v M = g := by
  have he := (cmFiniteAdelicIntegralLocalMap_compatibility K H v M).trans h
  apply Units.ext
  apply Matrix.ext
  intro i j
  apply Subtype.ext
  exact congrArg (fun M => M.val i j) he

end
end Dubon2026
