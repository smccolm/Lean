import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! DUB-17/18 -> Picard torsion injectivity -> unramified Kummer-cover
genus. The actual nonzero j differential remains nonzero after the finite
separable cover. Native etale base change and faithful flatness discharge
this premise; no new derivation kernel or coordinate differential basis
theory is needed. -/
namespace Dubon2026.SourceCurve
noncomputable section
open KaehlerDifferential
open scoped TensorProduct

theorem D_algebraMap_ne_zero_of_separable
    {K F E : Type*} [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
    [Algebra.IsSeparable F E] {x : F} (hx : D K F x ≠ 0) :
    D K E (algebraMap F E x) ≠ 0 := by
  letI : Algebra.FormallyEtale F E := Algebra.FormallyEtale.of_isSeparable F E
  intro h
  have he := tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap K F E x
  rw [h, map_zero] at he
  exact hx ((Module.FaithfullyFlat.one_tmul_eq_zero_iff (R := F)
    (M := Ω[F⁄K]) (A := E) (D K F x)).mp he.symm)

end
end Dubon2026.SourceCurve
