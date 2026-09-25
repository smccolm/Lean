import TaoTrudgianYang2025.PrimitiveCongruenceCount

/-! Gcd decomposition of actual primitive integer solutions of a linear equation.
No counting estimate is assumed by these arithmetic reductions. -/

namespace TaoTrudgianYang2025

theorem primitive_linear_triple_gcd_dvd {a b c u v w : ℤ}
    (hprim : Int.gcd (Int.gcd u v : ℤ) w = 1)
    (hline : a*u+b*v+c*w = 0) :
    (Int.gcd u v : ℤ) ∣ c := by
  have hs : (Int.gcd u v : ℤ) ∣ a*u+b*v :=
    dvd_add (dvd_mul_of_dvd_right (Int.gcd_dvd_left u v) a)
      (dvd_mul_of_dvd_right (Int.gcd_dvd_right u v) b)
  have hp : (Int.gcd u v : ℤ) ∣ c*w := by
    have he : c*w = -(a*u+b*v) := by linarith
    rw [he]
    exact dvd_neg.mpr hs
  exact Int.dvd_of_dvd_mul_left_of_gcd_one hp hprim

theorem primitive_coefficients_of_modulus_dvd {a b c m : ℤ}
    (hprim : Int.gcd (Int.gcd a b : ℤ) c = 1) (hm : m ∣ c) :
    Int.gcd (Int.gcd a b : ℤ) m = 1 := by
  apply Nat.dvd_one.mp
  rw [← hprim]
  exact Int.gcd_dvd_gcd_of_dvd_right _ hm

theorem primitive_linear_triple_normalized {a b c u v w : ℤ}
    (hv : 0 < v) (hprim : Int.gcd (Int.gcd u v : ℤ) w = 1)
    (hline : a*u+b*v+c*w = 0) :
    a*(u/(Int.gcd u v : ℤ))+b*(v/(Int.gcd u v : ℤ))+
      (c/(Int.gcd u v : ℤ))*w = 0 := by
  have hg : (Int.gcd u v : ℤ) ≠ 0 := by
    exact_mod_cast (Int.gcd_pos_of_ne_zero_right u hv.ne').ne'
  have hc := primitive_linear_triple_gcd_dvd hprim hline
  apply (mul_eq_zero.mp ?_).resolve_right hg
  calc
    (a*(u/(Int.gcd u v : ℤ))+b*(v/(Int.gcd u v : ℤ))+
        (c/(Int.gcd u v : ℤ))*w)*(Int.gcd u v : ℤ) =
      a*(u/(Int.gcd u v : ℤ)*(Int.gcd u v : ℤ))+
      b*(v/(Int.gcd u v : ℤ)*(Int.gcd u v : ℤ))+
      (c/(Int.gcd u v : ℤ)*(Int.gcd u v : ℤ))*w := by ring
    _ = 0 := by
      rw [Int.ediv_mul_cancel (Int.gcd_dvd_left u v),
        Int.ediv_mul_cancel (Int.gcd_dvd_right u v),Int.ediv_mul_cancel hc]
      exact hline

theorem primitive_linear_triple_normalized_congruence {a b c u v w : ℤ}
    (hv : 0 < v) (hprim : Int.gcd (Int.gcd u v : ℤ) w = 1)
    (hline : a*u+b*v+c*w = 0) :
    (c/(Int.gcd u v : ℤ)) ∣
      a*(u/(Int.gcd u v : ℤ))+b*(v/(Int.gcd u v : ℤ)) := by
  refine ⟨-w, ?_⟩
  have he := primitive_linear_triple_normalized hv hprim hline
  nlinarith only [he]

end TaoTrudgianYang2025

