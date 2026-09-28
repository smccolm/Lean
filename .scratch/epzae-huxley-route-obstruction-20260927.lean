import TaoTrudgianYang2025.SquareProductCount
import TaoTrudgianYang2025.GeneratedCertificates

open TaoTrudgianYang2025
namespace HuxleyRouteDiagnostic

/- These are comparisons of available majorants, not lower bounds for beta
or counterexamples to any analytic exponent-pair statement. -/

theorem current_pair_majorants_miss_first_target :
    exponentPairLine (89/1282) (997/1282) (3/8) <
      min (exponentPairLine (13/194) (76/97) (3/8))
        (exponentPairLine (18/199) (593/796) (3/8)) := by
  norm_num [exponentPairLine]

/- The retained P^12*U^3 term with P=T^alpha and U=T^(1-3*alpha)
has twelfth-root exponent (1+alpha)/4. Retaining sqrt(q) in the
separate Gauss error does not remove this term. -/
theorem retained_joint_count_cost_misses_first_target :
    exponentPairLine (89/1282) (997/1282) (3/8) <
      (12*(3/8)+3*(1-3*(3/8)))/12 ∧
    (12*(3/8:ℝ)+3*(1-3*(3/8)))/12 = 11/32 := by
  norm_num [exponentPairLine]

theorem classical_density_majorants_miss_piece_four :
    (356:ℝ)/(2742*(19/20)-2279) <
      min (3/(10*(19/20)-7))
        (min (3/(3*(19/20)-1)) (15/(3+5*(19/20)))) := by
  norm_num

#print axioms current_pair_majorants_miss_first_target
#print axioms retained_joint_count_cost_misses_first_target
#print axioms classical_density_majorants_miss_piece_four
end HuxleyRouteDiagnostic

