import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
open scoped Polynomial.Bivariate
theorem WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain {K : Type*} [Field K] [IsAlgClosed K] (W : WeierstrassCurve K) [W.IsElliptic] : IsDedekindDomain W.toAffine.CoordinateRing := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain.solution
