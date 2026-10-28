import Mathlib
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Definitions.Def_WeierstrassCurve_ReduceHom
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_map_eq_veluQuotient_and_map_residue_eq_veluQuotient_reduceHom

set_option autoImplicit false

open WeierstrassCurve IsLocalRing

theorem WeierstrassCurve.exists_map_eq_veluQuotient_and_map_residue_eq_veluQuotient_reduceHom
    {L : Type*} [Field L] [DecidableEq L] (A : ValuationSubring L) [DecidableEq (ResidueField A)]
    (W : WeierstrassCurve A) (hΔ : (W.map (residue A)).Δ ≠ 0)
    {ℓ : ℕ} (hℓ : (ℓ : ResidueField A) ≠ 0)
    (Q : (W.map A.subtype).toAffine.Point) (hQ : addOrderOf Q = ℓ) {n : ℕ} (hn : n < ℓ) :
    ∃ V : WeierstrassCurve A,
      V.map A.subtype = (W.map A.subtype).veluQuotient ((W.map A.subtype).oddOrderSummingSet Q n) ∧
      V.map (residue A) =
        (W.map (residue A)).veluQuotient ((W.map (residue A)).oddOrderSummingSet (reduceHom hΔ Q) n) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_map_eq_veluQuotient_and_map_residue_eq_veluQuotient_reduceHom.solution
