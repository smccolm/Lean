import Dubon2026.SourceHeckePeriodCosets

/-! The explicit period correction in the actual Hecke cocycle formula.
DUB-17/18 -> residual modular Galois association -> original H1 Hecke
eigenclass. The existing period addition and equivariance identities show
that differing base cusps contribute a genuine coboundary.
-/

namespace Dubon2026
noncomputable section
open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {p Q : ℕ} [NeZero p] [NeZero Q] {k : ℤ} {w : ℕ}

/-- One original period-coset term has the exact trace cocycle and base-cusp corrections. -/
theorem sourceHeckePeriod_transition (hp : Nat.Prime p)
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : k = w + 2)
    (α : OnePoint ℚ) (γ : Gamma0 Q)
    (q : Gamma0 Q ⧸ heckeUpperSubgroup Q p) :
    (sourcePeriodDualRep (Gamma0 Q) w).ρ (γ • q).out
        (sourceHeckeDualDiagonal w p
          (sourcePeriodBetween f hk
            (sourceHeckeCuspRepresentative (γ • q) • (mapGL ℚ γ.val • α))
            (sourceHeckeCuspRepresentative (γ • q) • α))) =
      (sourcePeriodDualRep (Gamma0 Q) w).ρ γ
          ((sourcePeriodDualRep (Gamma0 Q) w).ρ q.out
            (sourceHeckeDualDiagonal w p
              (sourcePeriodBetween f hk (sourceHeckeCuspRepresentative q • α) α))) +
        (sourcePeriodDualRep (Gamma0 Q) w).ρ (γ • q).out
          (sourceHeckeDualDiagonal w p
            (sourcePeriodCocycle f hk α
              (sourceHeckeConjugation hp (cosetTransition (heckeUpperSubgroup Q p) γ q)))) -
        (sourcePeriodDualRep (Gamma0 Q) w).ρ (γ • q).out
          (sourceHeckeDualDiagonal w p
            (sourcePeriodBetween f hk (sourceHeckeCuspRepresentative (γ • q) • α) α)) := by
  let t := cosetTransition (heckeUpperSubgroup Q p) γ q
  let δ := sourceHeckeConjugation hp t
  have hper :
      sourcePeriodBetween f hk
          (sourceHeckeCuspRepresentative (γ • q) • (mapGL ℚ γ.val • α))
          (sourceHeckeCuspRepresentative (γ • q) • α) =
        (sourcePeriodDualRep (Gamma0 Q) w).ρ δ
            (sourcePeriodBetween f hk (sourceHeckeCuspRepresentative q • α) α) +
          sourcePeriodCocycle f hk α δ -
          sourcePeriodBetween f hk (sourceHeckeCuspRepresentative (γ • q) • α) α := by
    rw [← mul_smul, sourceHeckeCuspRepresentative_transition hp, mul_smul]
    have h₁ := sourcePeriodBetween_add f hk
      (mapGL ℚ δ.val • (sourceHeckeCuspRepresentative q • α)) (mapGL ℚ δ.val • α) α
    rw [sourcePeriodBetween_equivariant] at h₁
    have h₂ := sourcePeriodBetween_add f hk
      (mapGL ℚ δ.val • (sourceHeckeCuspRepresentative q • α))
      (sourceHeckeCuspRepresentative (γ • q) • α) α
    exact eq_sub_of_add_eq (h₂.trans h₁.symm)
  rw [hper, map_sub, map_add, map_sub, map_add]
  have hi := congrArg
    (fun L => L (sourcePeriodBetween f hk (sourceHeckeCuspRepresentative q • α) α))
    (sourceHeckeDualDiagonal_intertwine hp w t)
  change sourceHeckeDualDiagonal w p
      ((sourcePeriodDualRep (Gamma0 Q) w).ρ δ
        (sourcePeriodBetween f hk (sourceHeckeCuspRepresentative q • α) α)) =
    (sourcePeriodDualRep (Gamma0 Q) w).ρ t.val
      (sourceHeckeDualDiagonal w p
        (sourcePeriodBetween f hk (sourceHeckeCuspRepresentative q • α) α)) at hi
  rw [hi, cosetTransition_action]

end
end Dubon2026
