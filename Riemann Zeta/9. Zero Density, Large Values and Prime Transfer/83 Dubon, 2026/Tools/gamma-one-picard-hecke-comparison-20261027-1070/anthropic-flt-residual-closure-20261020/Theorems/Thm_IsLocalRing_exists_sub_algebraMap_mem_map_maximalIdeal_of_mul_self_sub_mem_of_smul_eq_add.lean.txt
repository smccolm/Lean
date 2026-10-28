import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_sub_algebraMap_mem_map_maximalIdeal_of_mul_self_sub_mem_of_smul_eq_add

open IsLocalRing

theorem IsLocalRing.exists_sub_algebraMap_mem_map_maximalIdeal_of_mul_self_sub_mem_of_smul_eq_add
    {R : Type*} [CommRing R] [IsLocalRing R]
    {P P' P'' : Type*} [CommRing P] [CommRing P'] [CommRing P'']
    [Algebra R P] [Algebra R P'] [Algebra R P'']
    (u : P →ₐ[R] P'') (u' : P' →ₐ[R] P'')
    (h0 : ∀ (x : P) (x' : P'), u x = u' x' →
      ∃ r : R, x = algebraMap R P r ∧ x' = algebraMap R P' r)
    (a π : R) (hπ : π ∈ maximalIdeal R)
    (hnil : ∀ c ∈ maximalIdeal R, ∃ n : ℕ, a * π ∣ c ^ n)
    (htor : ∀ y : P'', (∃ (p : P) (p' : P'), (a * π) • y = u p + u' p') →
      ∃ (p : P) (p' : P'), a • y = u p + u' p')
    (e : P) (e' : P')
    (he : e * e - e ∈ (maximalIdeal R).map (algebraMap R P))
    (he' : e' * e' - e' ∈ (maximalIdeal R).map (algebraMap R P'))
    (hu : u e - u' e' ∈ (maximalIdeal R).map (algebraMap R P'')) :
    ∃ r : R, e - algebraMap R P r ∈ (maximalIdeal R).map (algebraMap R P) ∧
      e' - algebraMap R P' r ∈ (maximalIdeal R).map (algebraMap R P') := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_sub_algebraMap_mem_map_maximalIdeal_of_mul_self_sub_mem_of_smul_eq_add.solution
