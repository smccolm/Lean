import Dubon2026.SourceEllipticCyclicAbscissaBaseChange
import Dubon2026.SourceCyclicPrimeKernel

/-! The intrinsic next kernel commutes with the actual field point map.
Together with intrinsic quotient coefficient specialization, this fixes both
the kernel and target curve for composite field-map compatibility on the
DUB-17/18 all-level inertia-census chain. -/

namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve OddDiscriminant SourceEllipticCyclicCount
noncomputable section

/-- The literal next p-torsion kernel is transported by the original field point map. -/
theorem cyclicPrimeKernel_pointMap
    {F K : Type*} [Field F] [Field K] [DecidableEq F] [DecidableEq K]
    (f : F →+* K) (W : WeierstrassCurve F) (H : AddSubgroup W.toAffine.Point) (p : ℕ) :
    (cyclicPrimeKernel H p).map (pointMapHom f W) =
      cyclicPrimeKernel (H.map (pointMapHom f W)) p := by
  ext R
  rw [AddSubgroup.mem_map, mem_cyclicPrimeKernel]
  constructor
  · rintro ⟨P, hP, rfl⟩
    rw [mem_cyclicPrimeKernel] at hP
    refine ⟨⟨P, hP.1, rfl⟩, ?_⟩
    rw [← map_nsmul, hP.2, map_zero]
  · rintro ⟨⟨P, hPH, rfl⟩, hpP⟩
    refine ⟨P, (mem_cyclicPrimeKernel H p P).mpr ⟨hPH, ?_⟩, rfl⟩
    apply pointMapHom_injective f W
    rw [map_nsmul, map_zero]
    exact hpP

end
end Dubon2026.SourceEllipticVelu
