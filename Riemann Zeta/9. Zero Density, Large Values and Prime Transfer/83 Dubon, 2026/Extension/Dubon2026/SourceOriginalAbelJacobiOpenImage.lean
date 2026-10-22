import Dubon2026.SourceOriginalAbelJacobiImage
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi -> Jacobi inversion.
An independent frame of actual original differential evaluations makes
the derivative of the sum of local primitives invertible. The native
inverse-function theorem gives a neighborhood in the actual image of
degree-zero divisors modulo loop periods. The following consumer derives
the frame from the proved evaluation-separation theorem.
Adapted from S_AlgebraicCurve_exists_degree_eq_zero_and_abelJacobiDiv_sub_mem_pathPeriodLattice,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N]

theorem abelJacobiImage_mem_nhds_of_frame {n : ℕ}
    (b : Fin n → Ω[modularFunctionFieldOver N ℂ⁄ℂ])
    (hb : ∀ i, b i ∈ regularDifferentials ℂ (modularFunctionFieldOver N ℂ))
    (P₀ : Place ℂ (modularFunctionFieldOver N ℂ)) {κ : Type*} [Fintype κ]
    (a : κ → Place ℂ (modularFunctionFieldOver N ℂ))
    (β : Module.Basis κ ℂ (Fin n → ℂ))
    (hβ : ∀ k, β k = fun i => readDifferential N (a k) (b i) 0) :
    (abelJacobiImage N b P₀ : Set (Fin n → ℂ)) ∈ 𝓝 (0 : Fin n → ℂ) := by
  classical
  choose Φ hΦ using fun k i => exists_readDifferential_primitive_on_chart N (a k) (b i) (hb i)
  let G : (κ → ℂ) → (Fin n → ℂ) := fun w => ∑ k, fun i => Φ k i (w k) - Φ k i 0
  have hG0 : G 0 = 0 := by
    ext i
    simp only [G, Finset.sum_apply, Pi.zero_apply, sub_self, Finset.sum_const_zero]
  have hderiv : ∀ k i, HasStrictDerivAt (Φ k i) (readDifferential N (a k) (b i) 0) 0 := by
    intro k i
    have hd : DifferentiableOn ℂ (Φ k i) (ball 0 (placeRadius N (a k))) :=
      fun z hz => (hΦ k i z hz).differentiableAt.differentiableWithinAt
    have ha : AnalyticAt ℂ (Φ k i) 0 := hd.analyticAt (ball_mem_nhds _ (place_spec N (a k)).1)
    have hs := ha.hasStrictDerivAt
    rwa [(hΦ k i 0 (mem_ball_self (place_spec N (a k)).1)).deriv] at hs
  let e : (κ → ℂ) ≃L[ℂ] (Fin n → ℂ) := β.equivFun.symm.toContinuousLinearEquiv
  have he : ∀ w : κ → ℂ, e w = ∑ k, w k • (fun i => readDifferential N (a k) (b i) 0) := by
    intro w
    simp only [e, LinearEquiv.coe_toContinuousLinearEquiv', Module.Basis.equivFun_symm_apply, hβ]
  have hGderiv : HasStrictFDerivAt G (e : (κ → ℂ) →L[ℂ] (Fin n → ℂ)) 0 := by
    rw [hasStrictFDerivAt_pi']
    intro i
    have hsum : HasStrictFDerivAt (fun w : κ → ℂ => ∑ k, (Φ k i (w k) - Φ k i 0))
        (∑ k, (ContinuousLinearMap.toSpanSingleton ℂ (readDifferential N (a k) (b i) 0)).comp
          (ContinuousLinearMap.proj k)) 0 := by
      refine HasStrictFDerivAt.fun_sum fun k _ => ?_
      exact ((hderiv k i).hasStrictFDerivAt.comp (f := fun w : κ → ℂ => w k)
        (0 : κ → ℂ) (hasStrictFDerivAt_apply k (0 : κ → ℂ))).sub_const _
    have hfun : (fun w : κ → ℂ => G w i) = fun w => ∑ k, (Φ k i (w k) - Φ k i 0) := by
      funext w
      simp only [G, Finset.sum_apply]
    rw [hfun]
    refine hsum.congr_fderiv ?_
    ext w
    simp [he, ContinuousLinearMap.sum_apply]
  have hmap := hGderiv.map_nhds_eq_of_equiv
  rw [hG0] at hmap
  let U : Set (κ → ℂ) := Set.pi Set.univ fun k => ball (0 : ℂ) (placeRadius N (a k))
  have hU : U ∈ 𝓝 (0 : κ → ℂ) :=
    set_pi_mem_nhds Set.finite_univ fun k _ => ball_mem_nhds _ (place_spec N (a k)).1
  have hGU : G '' U ∈ 𝓝 (0 : Fin n → ℂ) := by
    rw [← hmap]
    exact Filter.image_mem_map hU
  apply Filter.mem_of_superset hGU
  rintro _ ⟨w, hw, rfl⟩
  exact local_primitive_sum_mem_abelJacobiImage N b hb P₀ a Φ hΦ w
    (fun k => hw k (mem_univ k))

end
end Dubon2026.SourceFunctionField.OriginalChart
