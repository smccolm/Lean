import Mathlib
import Definitions.Def_Isogeny_ConditionalCurrency
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_IsogenyEndDatum_pointEnd_apply_eq_sub

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

universe u
theorem WeierstrassCurve.Affine.IsogenyEndDatum.pointEnd_apply_eq_sub
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    {W : WeierstrassCurve.Affine F} [W.IsElliptic] [GenusOnePlaceGate W] [AbelTheorem W]
    (D : IsogenyEndDatum W) (hN : NormFormulaAlong F D.ι D.hfin) (P : W.Point) :
    D.pointEnd hN P
      = (pointEquivPlace (W := W)).symm ((placeOfPoint P).restrictAlong D.ι D.hι)
        - (pointEquivPlace (W := W)).symm ((placeOfPoint (0 : W.Point)).restrictAlong D.ι D.hι) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_IsogenyEndDatum_pointEnd_apply_eq_sub.solution
