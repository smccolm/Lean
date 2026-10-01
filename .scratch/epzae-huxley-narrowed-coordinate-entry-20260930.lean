import TaoTrudgianYang2025.HuxleyLinearForms
open Set TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase
namespace HuxleyNarrowedCoordinateScratch

theorem fourier_matrix_narrowed_coordinate_entry_bound
    (q e vinv : Fin 2 → ℤ) (A : Fin 4 → ℤ) {Q K V N R : ℝ}
    (hq : ∀ i, 0 < q i) (hK : 1 ≤ K) (hV : 1 ≤ V)
    (hN : 0 < N)
    (hmesh : Q*N ≤ K*R^2)
    (hband : ∀ i, (q i:ℝ) ≤ Q ∧ Q ≤ 2*q i)
    (hinv : ∀ i, q i ∣ e i*vinv i-1)
    (hdet : A 0*A 3-A 1*A 2=1)
    (ht : (A 2:ℝ)*((e 0:ℝ)/q 0)+A 3=(q 1:ℝ)/q 0)
    (hmap : ((A 0:ℝ)*((e 0:ℝ)/q 0)+A 1)/
      ((A 2:ℝ)*((e 0:ℝ)/q 0)+A 3)=(e 1:ℝ)/q 1)
    (hgamma : |(A 2:ℝ)| ≤ Q^2/(6*K^2))
    (hnear : |Int.fract (-(vinv 0:ℝ)/q 0)-
      Int.fract (-(vinv 1:ℝ)/q 1)| ≤ 1/(6*K^2*V)) :
    |(A 2:ℝ)| ≤ Q^2/(6*K^2*V) ∧ |(A 2:ℝ)| ≤ R^4/(6*N^2*V) := by
  have hKp : 0 < K := zero_lt_one.trans_le hK
  have hVp : 0 < V := zero_lt_one.trans_le hV
  have hqr i : (0:ℝ) < q i := by exact_mod_cast hq i
  have hQp : 0 < Q := (hqr 0).trans_le (hband 0).1
  have hnear₀ : |Int.fract (-(vinv 0:ℝ)/q 0)-
      Int.fract (-(vinv 1:ℝ)/q 1)| ≤ 1/(6*K^2) := by
    apply hnear.trans
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    nlinarith only [mul_le_mul_of_nonneg_left hV (show 0 ≤ 6*K^2 by positivity)]
  obtain ⟨v,hv,hs,htransport⟩ := fourier_matrix_normalized_chart_transport
    q e vinv A (Q:=Q) (K:=K) hq hK hband hinv hdet ht hmap hgamma hnear₀
  let s := fun i => -vinv i-q i*⌊-(vinv i:ℝ)/q i⌋
  have hc : A 2=q 0*s 1-s 0*q 1 := by
    have hden := (htransport 1 0).2
    have hcomp := (htransport 0 1).2
    simp only [mul_one,mul_zero,add_zero,zero_add] at hden hcomp
    change A 2*v 0+A 3*s 0=s 1 at hcomp
    linear_combination -(A 2)*(hv 0)+(q 0)*hcomp-(s 0)*hden
  have hcR : (A 2:ℝ)=(q 0:ℝ)*s 1-(s 0:ℝ)*q 1 := by exact_mod_cast hc
  have hp : 0 < (q 0:ℝ)*q 1 := mul_pos (hqr 0) (hqr 1)
  have hentry : |(A 2:ℝ)| ≤ Q^2/(6*K^2*V) := by
    calc
      _ = |(s 1:ℝ)/q 1-(s 0:ℝ)/q 0| *((q 0:ℝ)*q 1) := by
        rw [←abs_of_pos hp,←abs_mul,hcR]
        congr 1
        field_simp [(hqr 0).ne',(hqr 1).ne']
      _ ≤ (1/(6*K^2*V))*((q 0:ℝ)*q 1) := by
        apply mul_le_mul_of_nonneg_right _ hp.le
        rw [hs 0,hs 1,abs_sub_comm]
        exact hnear
      _ ≤ (1/(6*K^2*V))*Q^2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith only [mul_le_mul (hband 0).1 (hband 1).1 (hqr 1).le hQp.le]
      _ = _ := by ring
  refine ⟨hentry,hentry.trans ?_⟩
  apply (div_le_div_iff₀ (by positivity : 0 < 6*K^2*V)
    (by positivity : 0 < 6*N^2*V)).mpr
  have hsq := pow_le_pow_left₀ (mul_pos hQp hN).le hmesh 2
  have hm := mul_le_mul_of_nonneg_right hsq (show 0 ≤ 6*V by positivity)
  nlinarith only [hm]

example
    (q e vinv : Fin 2 → ℤ) (A : Fin 4 → ℤ) {Q K V N R : ℝ}
    (hq : ∀ i, 0 < q i) (hK : 1 ≤ K) (hV : 1 ≤ V)
    (hN : 0 < N)
    (hmesh : Q*N ≤ K*R^2)
    (hband : ∀ i, (q i:ℝ) ≤ Q ∧ Q ≤ 2*q i)
    (hinv : ∀ i, q i ∣ e i*vinv i-1)
    (hdet : A 0*A 3-A 1*A 2=1)
    (ht : (A 2:ℝ)*((e 0:ℝ)/q 0)+A 3=(q 1:ℝ)/q 0)
    (hmap : ((A 0:ℝ)*((e 0:ℝ)/q 0)+A 1)/
      ((A 2:ℝ)*((e 0:ℝ)/q 0)+A 3)=(e 1:ℝ)/q 1)
    (hgamma : |(A 2:ℝ)| ≤ Q^2/(6*K^2))
    (hnear : |Int.fract (-(vinv 0:ℝ)/q 0)-
      Int.fract (-(vinv 1:ℝ)/q 1)| ≤ 1/(6*K^2*V)) :
    |(A 2:ℝ)| ≤ Q^2/(6*K^2*V) ∧ |(A 2:ℝ)| ≤ R^4/(6*N^2*V) :=
  HuxleyNarrowedCoordinateScratch.fourier_matrix_narrowed_coordinate_entry_bound q e vinv A (Q:=Q) (K:=K) (V:=V) (N:=N) (R:=R) hq hK hV hN hmesh hband hinv hdet ht hmap hgamma hnear



#print axioms fourier_matrix_narrowed_coordinate_entry_bound
end HuxleyNarrowedCoordinateScratch
