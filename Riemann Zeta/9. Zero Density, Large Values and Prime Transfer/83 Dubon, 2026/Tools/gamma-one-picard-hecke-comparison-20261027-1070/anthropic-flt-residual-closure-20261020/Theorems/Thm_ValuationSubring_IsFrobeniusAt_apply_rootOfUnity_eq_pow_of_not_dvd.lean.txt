import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_FrobeniusTrace
import P2M.Util
import P2M.Sol.S_ValuationSubring_IsFrobeniusAt_apply_rootOfUnity_eq_pow_of_not_dvd

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point ValuationSubring
theorem ValuationSubring.IsFrobeniusAt.apply_rootOfUnity_eq_pow_of_not_dvd
    {q : ℕ} (hq : q.Prime)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : A.IsFrobeniusAt σ q)
    {m : ℕ} (hm : ¬ q ∣ m) (ζ : AlgebraicClosure ℚ) (hζ : ζ ^ m = 1) :
    σ ζ = ζ ^ q := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_IsFrobeniusAt_apply_rootOfUnity_eq_pow_of_not_dvd.solution
