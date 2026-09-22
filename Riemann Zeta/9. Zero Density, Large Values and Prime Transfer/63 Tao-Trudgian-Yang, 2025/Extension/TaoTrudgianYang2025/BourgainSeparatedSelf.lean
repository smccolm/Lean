import TaoTrudgianYang2025.MixedDoubleZeta

/-!
# Heath--Brown on arbitrary separated sets and the actual closed support

The auxiliary integer slice is not a large-value pattern for the original
polynomial. This theorem therefore consumes arbitrary separated sets, retaining
the source pattern only to identify its exact closed support and physical scale.
-/

open Complex Finset RiemannZeta.GuthMaynard
open scoped Classical

noncomputable section

namespace TaoTrudgianYang2025

def bourgainSelfMoment (P : LargeValuePattern) (W : Finset ℝ) : ℝ :=
  ∑ t ∈ W, ∑ u ∈ W, ‖∑ n ∈ P.indices, dirichletPhase n (t-u)‖^2

def bourgainSecondBudget (N H R : ℝ) : ℝ :=
  R^2*N+R*N^2+R^(5/4 : ℝ)*H^(1/2 : ℝ)*N

theorem bourgainSelfMoment_nonneg (P : LargeValuePattern) (W : Finset ℝ) :
    0 ≤ bourgainSelfMoment P W := by
  unfold bourgainSelfMoment
  positivity

theorem bourgainSecondBudget_nonneg {N H R : ℝ}
    (hN : 0 ≤ N) (hH : 0 ≤ H) (hR : 0 ≤ R) :
    0 ≤ bourgainSecondBudget N H R := by
  unfold bourgainSecondBudget
  positivity

/-- The original closed-support self moment is controlled by the native
reflected half-open moment, with its endpoint error retained. -/
theorem bourgainSelfMoment_le_native (P : LargeValuePattern) (W : Finset ℝ) (c : ℝ) :
    bourgainSelfMoment P W ≤
      2*gmDiscreteRatioMoment 2 P.scale (W.image (fun t => c-t))+
        2*(W.card : ℝ)^2 := by
  have himage :
      (∑ t ∈ W, ∑ u ∈ W,
        ‖sourceDirichletPoly P.scale (fun _ => 1) ((c-t)-(c-u))‖^2) =
        gmDiscreteRatioMoment 2 P.scale (W.image (fun t => c-t)) := by
    rw [gmDiscreteRatioMoment_eq_iterated,
      ← sourceCoefficientOne_differenceMoment_eq_gmR_ratioMoment]
    rw [Finset.sum_image (fun x _ y _ hxy => by linarith)]
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.sum_image (fun x _ y _ hxy => by linarith)]
  have hpoint (t u : ℝ) :
      ‖∑ n ∈ P.indices, dirichletPhase n (t-u)‖^2 ≤
        2*‖sourceDirichletPoly P.scale (fun _ => 1) ((c-t)-(c-u))‖^2+2 := by
    have heq : (P.intervalRight-t)-(P.intervalRight-u) = (c-t)-(c-u) := by ring
    simpa only [heq] using P.phaseSum_sq_le_reflected_source t u
  calc
    _ ≤ ∑ t ∈ W, ∑ u ∈ W,
        (2*‖sourceDirichletPoly P.scale (fun _ => 1) ((c-t)-(c-u))‖^2+2) :=
      Finset.sum_le_sum (fun t _ => Finset.sum_le_sum (fun u _ => hpoint t u))
    _ = 2*(∑ t ∈ W, ∑ u ∈ W,
        ‖sourceDirichletPoly P.scale (fun _ => 1) ((c-t)-(c-u))‖^2)+
        2*(W.card : ℝ)^2 := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      ring
    _ = _ := by rw [himage]

/-- Uniform finite self-moment estimate for an arbitrary one-separated set
in any interval of length at most H. No large-values premise is imposed on W. -/
theorem bourgain_separated_self_moment {ε : ℝ} (hε : 0 < ε) :
    ∃ C H₀ : ℝ, 0 < C ∧ 1 ≤ H₀ ∧
      ∀ (P : LargeValuePattern) (W : Finset ℝ) (a H : ℝ),
        H₀ ≤ H → IsSeparated 1 W →
        (∀ t ∈ W, a ≤ t ∧ t ≤ a+H) →
        bourgainSelfMoment P W ≤
          C*H^ε*bourgainSecondBudget P.N H (W.card : ℝ) := by
  obtain ⟨C, H₀, hC, hH₀, hHB⟩ := gmDiscreteRatioSecondMoment_native ε hε
  refine ⟨2*C+2, H₀, by positivity, hH₀, ?_⟩
  intro P W a H hH hsep hloc
  let U := W.image (fun t => a+H-t)
  have hcard : U.card = W.card :=
    Finset.card_image_of_injective _ (fun x y hxy => by linarith)
  have hU : IsSeparated 1 U := by
    intro x hx y hy hxy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hy
    have htu : t ≠ u := by intro h; exact hxy (congrArg (fun v => a+H-v) h)
    have hd : dist (a+H-t) (a+H-u) = dist t u := by
      rw [Real.dist_eq, Real.dist_eq, show a+H-t-(a+H-u) = -(t-u) by ring, abs_neg]
    rw [hd]
    exact hsep t ht u hu htu
  have hbase : InBaseInterval H U := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    have htloc := hloc t ht
    constructor <;> linarith
  have hbound := hHB P.scale H U P.scale_pos hH hU hbase
  rw [hcard, ← P.N_eq_scale] at hbound
  change gmDiscreteRatioMoment 2 P.scale U ≤
    C*H^ε*bourgainSecondBudget P.N H (W.card : ℝ) at hbound
  have hN := zero_lt_one.trans P.one_lt_N
  have hHone := hH₀.trans hH
  have hHpow : 1 ≤ H^ε := Real.one_le_rpow hHone hε.le
  have hB : (W.card : ℝ)^2 ≤ bourgainSecondBudget P.N H (W.card : ℝ) := by
    unfold bourgainSecondBudget
    have hRN : (W.card : ℝ)^2 ≤ (W.card : ℝ)^2*P.N :=
      le_mul_of_one_le_right (sq_nonneg _) P.one_lt_N.le
    have hrest₁ : 0 ≤ (W.card : ℝ)*P.N^2 := by positivity
    have hrest₂ : 0 ≤ (W.card : ℝ)^(5/4 : ℝ)*H^(1/2 : ℝ)*P.N := by positivity
    linarith
  have hBH : (W.card : ℝ)^2 ≤ H^ε*bourgainSecondBudget P.N H (W.card : ℝ) :=
    hB.trans (le_mul_of_one_le_left ((sq_nonneg _).trans hB) hHpow)
  have hfin := (bourgainSelfMoment_le_native P W (a+H)).trans
    (add_le_add (mul_le_mul_of_nonneg_left hbound (by norm_num : (0 : ℝ) ≤ 2)) le_rfl)
  change bourgainSelfMoment P W ≤
    2*(C*H^ε*bourgainSecondBudget P.N H (W.card : ℝ))+2*(W.card : ℝ)^2 at hfin
  nlinarith

end TaoTrudgianYang2025
