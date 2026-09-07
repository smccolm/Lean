import GafniTao.HeathBrownAtkinsonFractionalScale

/-!
# Heath--Brown equations (43), (46), (61), and (7)

This file records the exact real-variable calculation at the end of the
first case in Heath--Brown's proof of the discrete twelfth-moment theorem.
The two terms in equation (61) are `A` and `A^2`, where
`A = T * G^(-3) * L^2`.  The equation-(46) range makes `1 <= A`; equation
(43), `B * G * L^2 = V^2`, then converts `A^2` into the equation-(7)
monomial.  No asymptotic comparison is hidden in the definitions.
-/

namespace GafniTao

noncomputable section

/-- The first term in Heath--Brown (1978), equation (61), with `L` standing
for `log T`. -/
def heathBrownEquation61First (T G L : Real) : Real :=
  T / G ^ (3 : Nat) * L ^ (2 : Nat)

/-- The second term in equation (61). -/
def heathBrownEquation61Second (T G L : Real) : Real :=
  T ^ (2 : Nat) / G ^ (6 : Nat) * L ^ (4 : Nat)

/-- The second term in equation (61) is literally the square of the first
term. -/
theorem heathBrownEquation61Second_eq_sq
    {T G L : Real} :
    heathBrownEquation61Second T G L =
      heathBrownEquation61First T G L ^ (2 : Nat) := by
  unfold heathBrownEquation61First heathBrownEquation61Second
  ring

/-- Equation (46) supplies precisely the condition needed to absorb the
linear equation-(61) term into its square. -/
theorem heathBrownEquation61First_le_second
    {T G L : Real}
    (hfirst : 1 <= heathBrownEquation61First T G L) :
    heathBrownEquation61First T G L <=
      heathBrownEquation61Second T G L := by
  rw [heathBrownEquation61Second_eq_sq]
  nlinarith

/-- Consequently the full equation-(61) expression is at most twice its
quadratic term. -/
theorem heathBrownEquation61_add_le_two_second
    {T G L : Real}
    (hfirst : 1 <= heathBrownEquation61First T G L) :
    heathBrownEquation61First T G L +
        heathBrownEquation61Second T G L <=
      2 * heathBrownEquation61Second T G L := by
  linarith [heathBrownEquation61First_le_second hfirst]

/-- Exact substitution of equation (43) into the quadratic term of equation
(61).  The sixth power of the fixed numerical constant `B` is deliberately
retained; it is absorbed only when the final Vinogradov constant is chosen. -/
theorem heathBrownEquation43_substitution
    {T G L V B : Real}
    (hG : 0 < G) (hV : 0 < V)
    (hscale : B * G * L ^ (2 : Nat) = V ^ (2 : Nat)) :
    heathBrownEquation61Second T G L =
      B ^ (6 : Nat) * T ^ (2 : Nat) /
          V ^ (12 : Nat) * L ^ (16 : Nat) := by
  have hp := congrArg (fun x : Real => x ^ (6 : Nat)) hscale
  have hp' :
      B ^ (6 : Nat) * G ^ (6 : Nat) * L ^ (12 : Nat) =
        V ^ (12 : Nat) := by
    calc
      B ^ (6 : Nat) * G ^ (6 : Nat) * L ^ (12 : Nat) =
          (B * G * L ^ (2 : Nat)) ^ (6 : Nat) := by ring
      _ = (V ^ (2 : Nat)) ^ (6 : Nat) := hp
      _ = V ^ (12 : Nat) := by ring
  unfold heathBrownEquation61Second
  field_simp [hG.ne', hV.ne']
  rw [← hp']
  ring

/-- Literal equation-(61)-to-equation-(7) conversion, before absorbing the
fixed source constants. -/
theorem heathBrownEquation61_to_equation7
    {R C T G L V B : Real}
    (hC : 0 <= C) (hG : 0 < G) (hV : 0 < V)
    (hfirst : 1 <= heathBrownEquation61First T G L)
    (hscale : B * G * L ^ (2 : Nat) = V ^ (2 : Nat))
    (h61 : R <= C *
      (heathBrownEquation61First T G L +
        heathBrownEquation61Second T G L)) :
    R <= 2 * C * B ^ (6 : Nat) * T ^ (2 : Nat) /
        V ^ (12 : Nat) * L ^ (16 : Nat) := by
  have habsorb := heathBrownEquation61_add_le_two_second hfirst
  have hmul := mul_le_mul_of_nonneg_left habsorb hC
  calc
    R <= C * (heathBrownEquation61First T G L +
        heathBrownEquation61Second T G L) := h61
    _ <= C * (2 * heathBrownEquation61Second T G L) := hmul
    _ = 2 * C * B ^ (6 : Nat) * T ^ (2 : Nat) /
        V ^ (12 : Nat) * L ^ (16 : Nat) := by
      rw [heathBrownEquation43_substitution hG hV hscale]
      ring


end

end GafniTao
