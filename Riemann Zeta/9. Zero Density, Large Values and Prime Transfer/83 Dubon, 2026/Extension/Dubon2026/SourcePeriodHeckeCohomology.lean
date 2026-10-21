import Dubon2026.SourceHeckePeriodTransition
import Dubon2026.SourceOriginalPeriodCohomology

/-! Hecke compatibility of the original analytic period class.
DUB-17/18 -> residual modular Galois association -> original H1 Hecke
eigensystem. The exact finite-coset period formula differs from the native
Hecke cocycle by the displayed period coboundary, so the H1 classes agree.
-/

namespace Dubon2026
noncomputable section
open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {p Q : ℕ} [NeZero p] [NeZero Q] {k : ℤ} {w : ℕ}

private local instance sourcePeriodHeckeCohomologyFintype :
    Fintype (Gamma0 Q ⧸ heckeUpperSubgroup Q p) :=
  sourceHeckeUpperFintype Q p

/-- The actual period correction for the base cusps moved by the Hecke correspondence. -/
def sourceHeckePeriodCorrection
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : k = w + 2) (α : OnePoint ℚ) :
    sourcePeriodDualRep (Gamma0 Q) w :=
  ∑ q : Gamma0 Q ⧸ heckeUpperSubgroup Q p,
    (sourcePeriodDualRep (Gamma0 Q) w).ρ q.out
      (sourceHeckeDualDiagonal w p
        (sourcePeriodBetween f hk (sourceHeckeCuspRepresentative q • α) α))

/-- The analytic prime period cocycle and the full H1 Hecke cocycle differ by an explicit coboundary. -/
theorem sourcePeriodCocycle_hecke (hp : Nat.Prime p) (hpQ : Nat.Coprime p Q)
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : k = w + 2)
    (α : OnePoint ℚ) (γ : Gamma0 Q) :
    sourcePeriodCocycle (cuspHeckePrime hp f) hk α γ =
      sourceHeckeCocycle hp w (sourcePeriodCocycle f hk α) γ +
        (sourcePeriodDualRep (Gamma0 Q) w).ρ γ (sourceHeckePeriodCorrection (p := p) f hk α) -
        sourceHeckePeriodCorrection (p := p) f hk α := by
  change sourcePeriodBetween (cuspHeckePrime hp f) hk (mapGL ℚ γ.val • α) α = _
  rw [sourcePeriodBetween_hecke hp hpQ]
  rw [← (Equiv.sum_comp (MulAction.toPerm γ)
    (fun q : Gamma0 Q ⧸ heckeUpperSubgroup Q p =>
      (sourcePeriodDualRep (Gamma0 Q) w).ρ q.out
        (sourceHeckeDualDiagonal w p
          (sourcePeriodBetween f hk (sourceHeckeCuspRepresentative q • (mapGL ℚ γ.val • α))
            (sourceHeckeCuspRepresentative q • α)))))]
  change (∑ q : Gamma0 Q ⧸ heckeUpperSubgroup Q p,
    (sourcePeriodDualRep (Gamma0 Q) w).ρ (γ • q).out
      (sourceHeckeDualDiagonal w p
        (sourcePeriodBetween f hk
          (sourceHeckeCuspRepresentative (γ • q) • (mapGL ℚ γ.val • α))
          (sourceHeckeCuspRepresentative (γ • q) • α)))) = _
  simp_rw [sourceHeckePeriod_transition hp f hk α γ]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← map_sum]
  have hr := Equiv.sum_comp (MulAction.toPerm γ)
    (fun q : Gamma0 Q ⧸ heckeUpperSubgroup Q p =>
      (sourcePeriodDualRep (Gamma0 Q) w).ρ q.out
        (sourceHeckeDualDiagonal w p
          (sourcePeriodBetween f hk (sourceHeckeCuspRepresentative q • α) α)))
  change (∑ q : Gamma0 Q ⧸ heckeUpperSubgroup Q p,
    (sourcePeriodDualRep (Gamma0 Q) w).ρ (γ • q).out
      (sourceHeckeDualDiagonal w p
        (sourcePeriodBetween f hk (sourceHeckeCuspRepresentative (γ • q) • α) α))) =
      sourceHeckePeriodCorrection (p := p) f hk α at hr
  change (sourcePeriodDualRep (Gamma0 Q) w).ρ γ (sourceHeckePeriodCorrection (p := p) f hk α) +
    sourceHeckeCocycle hp w (sourcePeriodCocycle f hk α) γ -
    (∑ q : Gamma0 Q ⧸ heckeUpperSubgroup Q p,
      (sourcePeriodDualRep (Gamma0 Q) w).ρ (γ • q).out
        (sourceHeckeDualDiagonal w p
          (sourcePeriodBetween f hk (sourceHeckeCuspRepresentative (γ • q) • α) α))) = _
  rw [hr, add_comm]

/-- The original analytic prime Hecke action agrees with the actual full native H1 correspondence. -/
theorem sourcePeriodH1_hecke (hp : Nat.Prime p) (hpQ : Nat.Coprime p Q)
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : k = w + 2) (α : OnePoint ℚ) :
    sourcePeriodH1 (cuspHeckePrime hp f) hk α =
      sourceHeckeH1 hp w (sourcePeriodH1 f hk α) := by
  change groupCohomology.H1π _ (sourcePeriodCocycle (cuspHeckePrime hp f) hk α) =
    sourceHeckeH1 hp w (groupCohomology.H1π _ (sourcePeriodCocycle f hk α))
  rw [sourceHeckeH1_cocycle]
  apply (groupCohomology.H1π_eq_iff _ _).mpr
  refine ⟨sourceHeckePeriodCorrection (p := p) f hk α, ?_⟩
  funext γ
  change (sourcePeriodDualRep (Gamma0 Q) w).ρ γ (sourceHeckePeriodCorrection (p := p) f hk α) -
    sourceHeckePeriodCorrection (p := p) f hk α =
      sourcePeriodCocycle (cuspHeckePrime hp f) hk α γ -
        sourceHeckeCocycle hp w (sourcePeriodCocycle f hk α) γ
  rw [sourcePeriodCocycle_hecke hp hpQ]
  abel

end
end Dubon2026
