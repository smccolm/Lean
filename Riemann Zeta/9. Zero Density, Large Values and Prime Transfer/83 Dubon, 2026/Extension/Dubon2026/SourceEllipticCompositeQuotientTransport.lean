import Dubon2026.SourceEllipticCompositeCyclicQuotient
import Dubon2026.SourceEllipticCanonicalKernelBaseChange

/-! Transport the actual least-prime kernel and composite quotient input.
These equalities are used in the induction proving field-map compatibility
of the successive cyclic quotient, on the DUB-17/18 all-level census chain. -/

namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve SourceEllipticCyclicCount OddDiscriminant
open SourceFunctionField.IntegralJCoordinate
noncomputable section
variable {F K : Type*} [Field F] [Field K] [DecidableEq F] [DecidableEq K]

/-- The actual least-prime cyclic kernel commutes with the original field point map. -/
theorem cyclicQuotientLeastKernel_map (f : F →+* K) (W : WeierstrassCurve F)
    (N : ℕ) (hNF : (N : F) ≠ 0) (hNK : (N : K) ≠ 0) (hN1 : N ≠ 1)
    (H : AddSubgroup W.toAffine.Point) (hcyc : IsAddCyclic H) (hcard : Nat.card H = N) :
    let H' := primeCyclicKernelMap f W N ⟨H, hcyc, hcard⟩
    primeCyclicKernelMap f W N.minFac (cyclicQuotientLeastKernel W N hNF hN1 H hcyc hcard) =
      cyclicQuotientLeastKernel (W.map f) N hNK hN1 H'.1 H'.2.1 H'.2.2 := by
  apply Subtype.ext
  exact cyclicPrimeKernel_pointMap f W H N.minFac

variable [IsAlgClosed F]

/-- Equality transport of the actual input curve and subgroup preserves the composite quotient. -/
theorem cyclicQuotientCurve_cast (N : ℕ) (hN : (N : F) ≠ 0)
    (W V : WeierstrassCurve F) [W.IsElliptic] [V.IsElliptic] (h : W = V)
    (H : AddSubgroup W.toAffine.Point) (hcyc : IsAddCyclic H) (hcard : Nat.card H = N) :
    let e := AddEquiv.cast (M := fun E : WeierstrassCurve F => E.toAffine.Point) h
    let hs := isAddCyclic_map_and_card_of_injective N e.toAddMonoidHom e.injective ⟨hcyc, hcard⟩
    (cyclicQuotientCurve N hN V (H.map e.toAddMonoidHom) hs.1 hs.2.1).1 =
      (cyclicQuotientCurve N hN W H hcyc hcard).1 := by
  subst V
  have he : (AddEquiv.cast (M := fun E : WeierstrassCurve F => E.toAffine.Point)
      (rfl : W = W)).toAddMonoidHom = AddMonoidHom.id W.toAffine.Point := rfl
  simp only [he, AddSubgroup.map_id]

end
end Dubon2026.SourceEllipticVelu
