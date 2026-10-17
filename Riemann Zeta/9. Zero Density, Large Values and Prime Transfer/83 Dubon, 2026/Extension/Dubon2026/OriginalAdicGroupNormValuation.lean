import Dubon2026.OriginalAdicUnitCohomology

/-! # Valuation of an actual completion group norm

Every original decomposition transport preserves the actual completed
valuation. The literal finite group norm therefore multiplies its order
by the group size. This is the valuation input for integral norm-class
representatives in DUB-17's local inertia image calculation.
-/
namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField BigOperators
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (w : HeightOneSpectrum (𝓞 L))

/-- The literal norm for a finite group acting through the actual
decomposition group raises the completed valuation to its group order. -/
theorem originalAdicUnit_restricted_norm_valuation
    {H : Type} [Group H] [Fintype H]
    (f : H →* OriginalFiniteDecompositionGroup K L w)
    (x : originalAdicUnitRep K L w) :
    Valued.v (((Rep.res f (originalAdicUnitRep K L w)).ρ.norm x).toMul.val) =
      (Valued.v x.toMul.val : WithZero (Multiplicative ℤ)) ^ Fintype.card H := by
  simp only [Representation.norm, LinearMap.sum_apply]
  change Valued.v ((∏ g : H, (show (w.adicCompletion L)ˣ from
    ((originalAdicUnitRep K L w).ρ (f g) x).toMul)).val) = _
  rw [Units.coe_prod, map_prod]
  calc
    _ = ∏ _g : H, (Valued.v x.toMul.val : WithZero (Multiplicative ℤ)) := by
      apply Finset.prod_congr rfl
      intro g _
      exact numberFieldGaloisLocalTransport_valuation K L (f g).val w w (f g).property x.toMul.val
    _ = _ := by simp

end
end Dubon2026
