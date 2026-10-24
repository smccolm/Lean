import Dubon2026.SourceSeparableChartPolynomialGenerators
import Dubon2026.SourceJointChartComponentConstants

/-! DUB-17/18 -> Kummer power lifting -> common residue constants -> finite
localized overlap. Joint chart integrality embeds the actual residue chart
in the product of finite integral closures of the separating residue
coordinates. Their polynomial generators give one finite ambient module.
This is the required finiteness input to the polynomial basis construction.
The finite product assembly adapts Apache-2.0 FLT commit
6e837e75355538c7f80bab5b956861e86c4eacc2. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
noncomputable section
open Polynomial IsLocalRing

theorem exists_joint_integral_polynomial_generators
    {k : Type*} [Field k] {ι : Type*} [Fintype ι] (Fb : ι → Type*)
    [∀ i, Field (Fb i)] [∀ i, Algebra k (Fb i)] (x : ∀ i, Fb i)
    (hx : ∀ i, Transcendental k (x i))
    [∀ i, FiniteDimensional (IntermediateField.adjoin k ({x i} : Set (Fb i))) (Fb i)]
    [∀ i, Algebra.IsSeparable (IntermediateField.adjoin k ({x i} : Set (Fb i))) (Fb i)] :
    ∃ (m : ℕ) (g : Fin m → ∀ i, Fb i), ∀ h : ∀ i, Fb i,
      (∀ i, IsIntegral (Algebra.adjoin k ({x i} : Set (Fb i))) (h i)) →
        ∃ q : Fin m → k[X], h = ∑ c, aeval x (q c) * g c := by
  classical
  choose m s hs using fun i => exists_integral_chart_polynomial_generators (x i) (hx i)
  let Γ := Σ i, Fin (m i)
  let eΓ := Fintype.equivFin Γ
  refine ⟨Fintype.card Γ, fun c => Pi.single (eΓ.symm c).1 (s _ (eΓ.symm c).2), ?_⟩
  intro h hh
  choose q hq using fun i => hs i (h i) (hh i)
  refine ⟨fun c => q (eΓ.symm c).1 (eΓ.symm c).2, ?_⟩
  let φ : Γ → ∀ i, Fb i := fun c => aeval x (q c.1 c.2) * Pi.single c.1 (s c.1 c.2)
  change h = ∑ c, φ (eΓ.symm c)
  rw [Equiv.sum_comp eΓ.symm φ]
  change h = ∑ c : Γ, aeval x (q c.1 c.2) * Pi.single c.1 (s c.1 c.2)
  rw [Fintype.sum_sigma]
  conv_lhs => rw [← Finset.univ_sum_single h]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hterm : ∀ a : Fin (m i), aeval x (q i a) * Pi.single i (s i a) =
      Pi.single i (aeval (x i) (q i a) * s i a) := by
    intro a
    funext j
    rw [Pi.mul_apply, ← Pi.single_mul_right_apply, aeval_pi_apply₂]
  simp_rw [hterm]
  rw [hq i]
  exact map_sum (AddMonoidHom.single Fb i) _ Finset.univ

end
end Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
