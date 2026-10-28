import Mathlib
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow
attribute [-simp] WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.veluY_empty
open WeierstrassCurve
theorem WeierstrassCurve.veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow
    {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
    {n : ℕ} (Q : W.toAffine.Point) (hQ : addOrderOf Q = 2 * n + 1) :
    (W.veluQuotient (W.oddOrderSummingSet Q n)).Δ *
        (∏ P ∈ W.oddOrderSummingSet Q n, W.veluU P.1 P.2) ^ 4
      = W.Δ ^ (2 * n + 1) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow.solution
