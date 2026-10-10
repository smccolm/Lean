import Dubon2026.CompactOpenImageSeparation
import Dubon2026.FixedResidualRepresentationFactors

/-! # Actual closed normal quotients retain their genuine profinite topology -/

namespace Dubon2026

noncomputable section

/-- The original quotient by a genuine closed normal subgroup is totally disconnected in its actual quotient topology. -/
theorem closedProfiniteQuotient_totallyDisconnected (G : ProfiniteGrp)
    (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) :
    TotallyDisconnectedSpace (G ⧸ N) := by
  letI : IsClosed (N : Set G) := hN
  letI := compactOpenSurjection_totallySeparated (QuotientGroup.mk' N)
    QuotientGroup.continuous_mk QuotientGroup.isOpenMap_coe
    (QuotientGroup.mk'_surjective N)
  infer_instance

/-- The genuine closed normal quotient bundled with its original quotient topology. -/
def closedProfiniteQuotient (G : ProfiniteGrp)
    (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) : ProfiniteGrp := by
  letI : IsClosed (N : Set G) := hN
  letI := closedProfiniteQuotient_totallyDisconnected G N hN
  exact ProfiniteGrp.of (G ⧸ N)

/-- The actual fixed ambient residual quotient carries its genuine proved profinite topology. -/
def fixedResidualProfiniteQuotient (p : ℕ) (G : ProfiniteGrp) (K : Subgroup G)
    [K.Normal] (hK : IsClosed (K : Set G)) : ProfiniteGrp :=
  closedProfiniteQuotient G (fixedResidualProPKernel p G K hK)
    (fixedResidualProPKernel_isClosed p G K hK)

/-- The original ambient projection to its genuine fixed residual quotient is continuous. -/
theorem fixedResidualProfiniteQuotient_projection_continuous
    (p : ℕ) (G : ProfiniteGrp) (K : Subgroup G) [K.Normal]
    (hK : IsClosed (K : Set G)) :
    Continuous (QuotientGroup.mk' (fixedResidualProPKernel p G K hK) :
      G → fixedResidualProfiniteQuotient p G K hK) :=
  QuotientGroup.continuous_mk

end
end Dubon2026
