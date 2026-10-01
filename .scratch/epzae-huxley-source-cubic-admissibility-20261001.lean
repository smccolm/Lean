import TaoTrudgianYang2025.HuxleyLinearForms
open Set TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase
open scoped BigOperators Classical ContDiff
namespace HuxleySourceCubicAdmissibilityScratch
private theorem actual_source_dyadic_cubic_admissibility
    (F : ℝ → ℝ) {σ c J η y z T M R : ℝ} {N Q A K₀ : ℕ} {a r : ℚ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : y∈Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hM : 2 ≤ M) (hN : 1 ≤ N) (hR : 0 < R) (hz : z∈Icc M (2*M))
    (hphase : T*(N:ℝ)*R^2=M^3)
    (hQN : Q ≤ N) (hden : r.den ≤ Q) (hhalf : Q ≤ 2*r.den)
    (hcut : 2*a.den ≤ Q) (hmajor : 128*σ*R^2 ≤ c*(Q:ℝ)*a.den)
    (hAlow : N ≤ A) (hAhigh : A ≤ 3*N)
    (hmesh : 63*(J/(2*σ*(N:ℝ)*R^2))*(Q:ℝ)*(N:ℝ)^2 ≤ K₀) :
    let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let μ := iteratedDeriv 3 f (round z)/6
    1 ≤ A ∧ r.den ≤ A ∧ 1 ≤ μ*(r.den:ℝ)^2*A ∧
      7*(μ*(r.den:ℝ)*(A:ℝ)^2) ≤ K₀ := by
  intro f μ
  have hNp : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hμ := positive_difference_rounded_cubic_scales F hσ hc hJ hη hηmax hy
    hf hbound hnegative hM hNp hR hz hphase
  let lambda := c/(12*σ*(N:ℝ)*R^2)
  let U₃ := J/(2*σ*(N:ℝ)*R^2)
  have hμbounds : lambda ≤ μ ∧ μ ≤ U₃ := hμ
  have hlambda : 0 < lambda := by dsimp only [lambda]; positivity
  have hU₃ : 0 < U₃ := by dsimp only [U₃]; positivity
  have hcutR : 2*(a.den:ℝ) ≤ Q := by exact_mod_cast hcut
  have hqR : (Q:ℝ) ≤ 2*(r.den:ℝ) := by exact_mod_cast hhalf
  have haq : (a.den:ℝ) ≤ r.den := by linarith only [hcutR,hqR]
  have hprod : c*(Q:ℝ)*a.den ≤ 2*c*(r.den:ℝ)^2 := by
    calc
      _ ≤ c*(2*(r.den:ℝ))*(r.den:ℝ) := by gcongr
      _ = _ := by ring
  have hbudget : 12*σ*R^2 ≤ c*(r.den:ℝ)^2 := by
    have hpositive : 0 < σ*R^2 := by positivity
    nlinarith only [hmajor,hprod,hpositive]
  have hbase : 1 ≤ lambda*(r.den:ℝ)^2*N := by
    have heq : lambda*(r.den:ℝ)^2*N=c*(r.den:ℝ)^2/(12*σ*R^2) := by
      dsimp only [lambda]
      field_simp
    rw [heq]
    exact (one_le_div (by positivity : 0 < 12*σ*R^2)).mpr hbudget
  have hAlowR : (N:ℝ) ≤ A := by exact_mod_cast hAlow
  have hAhighR : (A:ℝ) ≤ 3*(N:ℝ) := by exact_mod_cast hAhigh
  have hdenR : (r.den:ℝ) ≤ Q := by exact_mod_cast hden
  have hμnonneg : 0 ≤ μ := hlambda.le.trans hμbounds.1
  refine ⟨hN.trans hAlow,hden.trans (hQN.trans hAlow),hbase.trans ?_,?_⟩
  · exact mul_le_mul (mul_le_mul_of_nonneg_right hμbounds.1 (sq_nonneg _))
      hAlowR hNp.le (mul_nonneg hμnonneg (sq_nonneg _))
  · calc
      7*(μ*(r.den:ℝ)*(A:ℝ)^2) ≤ 7*(U₃*(Q:ℝ)*(3*(N:ℝ))^2) := by
        gcongr
        exact hμbounds.2
      _ = 63*U₃*(Q:ℝ)*(N:ℝ)^2 := by ring
      _ ≤ K₀ := hmesh

example
    (F : ℝ → ℝ) {σ c J η y z T M R : ℝ} {N Q A K₀ : ℕ} {a r : ℚ}
    (hσ : 0 < σ) (hc : 0 < c) (hJ : 0 < J)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : y∈Icc (1:ℝ) 2)
    (hf : ∀ w, 0 < w → ContDiffAt ℝ ∞ F w)
    (hbound : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) F w| ≤ J)
    (hnegative : ∀ w∈Icc (1/2:ℝ) 3, iteratedDeriv 4 F w ≤ -c)
    (hM : 2 ≤ M) (hN : 1 ≤ N) (hR : 0 < R) (hz : z∈Icc M (2*M))
    (hphase : T*(N:ℝ)*R^2=M^3)
    (hQN : Q ≤ N) (hden : r.den ≤ Q) (hhalf : Q ≤ 2*r.den)
    (hcut : 2*a.den ≤ Q) (hmajor : 128*σ*R^2 ≤ c*(Q:ℝ)*a.den)
    (hAlow : N ≤ A) (hAhigh : A ≤ 3*N)
    (hmesh : 63*(J/(2*σ*(N:ℝ)*R^2))*(Q:ℝ)*(N:ℝ)^2 ≤ K₀) :
    let f := fun w => T*(F (w/M)-F (w/M+η*y))/(σ*η)
    let μ := iteratedDeriv 3 f (round z)/6
    1 ≤ A ∧ r.den ≤ A ∧ 1 ≤ μ*(r.den:ℝ)^2*A ∧
      7*(μ*(r.den:ℝ)*(A:ℝ)^2) ≤ K₀ :=
  HuxleySourceCubicAdmissibilityScratch.actual_source_dyadic_cubic_admissibility F (σ:=σ) (c:=c) (J:=J) (η:=η) (y:=y) (z:=z) (T:=T) (M:=M) (R:=R) (N:=N) (Q:=Q) (A:=A) (K₀:=K₀) (a:=a) (r:=r) hσ hc hJ hη hηmax hy hf hbound hnegative hM hN hR hz hphase hQN hden hhalf hcut hmajor hAlow hAhigh hmesh


#print axioms actual_source_dyadic_cubic_admissibility
end HuxleySourceCubicAdmissibilityScratch
