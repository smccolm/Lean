import Dubon2026.SourceCurveProjectedMultiplication

/-! The Leibniz rule for the local Tate trace. The failure of the operator
identity is an explicit sum of commutators with finite-rank factors. Their
traces vanish by proved cyclicity. This is the algebraic input for factoring
the local residue through actual Kaehler differentials in DUB-17/18. -/

noncomputable section

namespace Dubon2026.SourceCurve.ResidueTrace

open LinearMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The Leibniz defect is a sum of four explicitly identified error commutators. -/
theorem tateComm_leibniz_defect (p f g h : V →ₗ[K] V) :
    tateCommRestrict p f (g ∘ₗ h) - tateCommRestrict p (f ∘ₗ g) h -
      tateCommRestrict p (f ∘ₗ h) g =
    (piRestrict p g ∘ₗ tateCommRestrict p f h -
      tateCommRestrict p f h ∘ₗ piRestrict p g) +
    (piRestrict p f ∘ₗ epsRestrict p g h - epsRestrict p g h ∘ₗ piRestrict p f) -
    (epsRestrict p f g ∘ₗ piRestrict p h - piRestrict p h ∘ₗ epsRestrict p f g) -
    (epsRestrict p f h ∘ₗ piRestrict p g - piRestrict p g ∘ₗ epsRestrict p f h) := by
  simp only [tateCommRestrict_eq_bracket, piRestrict_comp_eq]
  let F := piRestrict p f
  let G := piRestrict p g
  let H := piRestrict p h
  let U := epsRestrict p g h
  let W := epsRestrict p f g
  let Z := epsRestrict p f h
  change (F * (G * H + U) - (G * H + U) * F) -
      ((F * G + W) * H - H * (F * G + W)) -
      ((F * H + Z) * G - G * (F * H + Z)) =
    (G * (F * H - H * F) - (F * H - H * F) * G) +
      (F * U - U * F) - (W * H - H * W) - (Z * G - G * Z)
  simp only [mul_add, add_mul, mul_sub, sub_mul, mul_assoc]
  abel

attribute [local instance] finite_range_add finite_range_sub
  finite_range_comp_left finite_range_comp_right

/-- Finite principal-part defects give the exact Leibniz rule for the actual trace. -/
theorem tateCommTrace_leibniz_snd (p f g h : V →ₗ[K] V)
    [FiniteDimensional K (LinearMap.range (tateCommRestrict p f h))]
    [FiniteDimensional K (LinearMap.range (epsRestrict p g h))]
    [FiniteDimensional K (LinearMap.range (epsRestrict p f g))]
    [FiniteDimensional K (LinearMap.range (epsRestrict p f h))]
    [FiniteDimensional K (LinearMap.range (tateCommRestrict p f (g ∘ₗ h)))]
    [FiniteDimensional K (LinearMap.range (tateCommRestrict p (f ∘ₗ g) h))]
    [FiniteDimensional K (LinearMap.range (tateCommRestrict p (f ∘ₗ h) g))] :
    tateCommTrace p f (g ∘ₗ h) =
      tateCommTrace p (f ∘ₗ g) h + tateCommTrace p (f ∘ₗ h) g := by
  have hz : finrankTrace
      (tateCommRestrict p f (g ∘ₗ h) - tateCommRestrict p (f ∘ₗ g) h -
        tateCommRestrict p (f ∘ₗ h) g) = 0 := by
    rw [tateComm_leibniz_defect, finrankTrace_sub, finrankTrace_sub, finrankTrace_add,
      finrankTrace_commutator_eq_zero, finrankTrace_commutator_eq_zero,
      finrankTrace_commutator_eq_zero_left, finrankTrace_commutator_eq_zero_left]
    simp
  rw [finrankTrace_sub, finrankTrace_sub] at hz
  unfold tateCommTrace
  exact (eq_add_of_sub_eq (eq_of_sub_eq_zero hz)).trans (add_comm _ _)

end Dubon2026.SourceCurve.ResidueTrace
