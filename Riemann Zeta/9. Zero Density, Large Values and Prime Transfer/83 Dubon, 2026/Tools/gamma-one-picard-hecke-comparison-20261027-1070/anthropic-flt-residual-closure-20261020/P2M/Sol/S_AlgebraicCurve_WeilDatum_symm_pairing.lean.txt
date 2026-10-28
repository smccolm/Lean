import Definitions.Def_AlgebraicCurve_WeilDatum
import P2M.Util
namespace P2MW.S_AlgebraicCurve_WeilDatum_symm_pairing

open AlgebraicCurve

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ} (d : WeilDatum K F n) : d.symm.pairing = d.pairing⁻¹ := by
  rw [WeilDatum.pairing, WeilDatum.pairing, inv_div]
  rfl
