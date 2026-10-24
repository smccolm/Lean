import Dubon2026.SourceEllipticCyclicVariableQuotient
import Dubon2026.SourceEllipticCompositeQuotientTransport

/-! The literal least-prime torsion kernel is preserved by the original
coordinate-change equivalence. This supplies the recursive kernel identity
for composite model transport and the all-level cyclic-root bijection. -/

namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve SourceEllipticVariableChange SourceEllipticCyclicCount
noncomputable section
variable {F : Type*} [Field F] [DecidableEq F]

/-- The next literal torsion kernel commutes with the actual change of model. -/
theorem cyclicPrimeKernel_variableChange
    (C : VariableChange F) (W : WeierstrassCurve F) (H : AddSubgroup W.toAffine.Point) (p : ℕ) :
    let e := (variableChangeAddEquiv C W.toAffine).symm
    (cyclicPrimeKernel H p).map e.toAddMonoidHom =
      cyclicPrimeKernel (H.map e.toAddMonoidHom) p := by
  intro e
  ext R
  rw [AddSubgroup.mem_map, mem_cyclicPrimeKernel]
  constructor
  · rintro ⟨P, hP, rfl⟩
    rw [mem_cyclicPrimeKernel] at hP
    refine ⟨⟨P, hP.1, rfl⟩, ?_⟩
    rw [← map_nsmul, hP.2, map_zero]
  · rintro ⟨⟨P, hPH, rfl⟩, hpP⟩
    refine ⟨P, (mem_cyclicPrimeKernel H p P).mpr ⟨hPH, ?_⟩, rfl⟩
    apply e.injective
    rw [map_nsmul, map_zero]
    exact hpP

/-- The original least-prime kernel subtype transports with its cyclicity and exact order derived. -/
theorem cyclicQuotientLeastKernel_variableChange
    (C : VariableChange F) (W : WeierstrassCurve F)
    (N : ℕ) (hN : (N : F) ≠ 0) (hN1 : N ≠ 1)
    (H : AddSubgroup W.toAffine.Point) (hcyc : IsAddCyclic H) (hcard : Nat.card H = N) :
    let H' := cyclicKernelVariableChange C W N ⟨H, hcyc, hcard⟩
    cyclicKernelVariableChange C W N.minFac (cyclicQuotientLeastKernel W N hN hN1 H hcyc hcard) =
      cyclicQuotientLeastKernel (C • W) N hN hN1 H'.1 H'.2.1 H'.2.2 := by
  apply Subtype.ext
  exact cyclicPrimeKernel_variableChange C W H N.minFac

end
end Dubon2026.SourceEllipticVelu
