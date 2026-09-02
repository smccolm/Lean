import GafniTao.FordLemma34Final

/-!
# Ford Lemma 3.5: canonical `phi` schedule

Ford defines the `phi_i` backwards from `phi_j=1/r`.  This module turns that
finite recursion into an actual `FordPhiSchedule`; later estimates therefore
do not receive the schedule as an independent certificate.
-/

namespace GafniTao

noncomputable section

def fordPhiBackwardAux (k r j : ℕ) (delta : ℝ) : ℕ → ℝ
  | 0 => 1 / (r : ℝ)
  | n + 1 => fordPhiStep k r (j - 1 - n) delta
      (fordPhiBackwardAux k r j delta n)

@[simp] theorem fordPhiBackwardAux_zero
    (k r j : ℕ) (delta : ℝ) :
    fordPhiBackwardAux k r j delta 0 = 1 / (r : ℝ) := rfl

@[simp] theorem fordPhiBackwardAux_succ
    (k r j n : ℕ) (delta : ℝ) :
    fordPhiBackwardAux k r j delta (n + 1) =
      fordPhiStep k r (j - 1 - n) delta
        (fordPhiBackwardAux k r j delta n) := rfl

/-- The literal source recursion, made into a total finite schedule. -/
def fordCanonicalPhiSchedule
    (k r j : ℕ) (delta : ℝ) : FordPhiSchedule k r j delta where
  phi J := fordPhiBackwardAux k r j delta (j - J)
  terminal := by simp
  recurrence J hJ hJj := by
    have hsub : j - J = (j - (J + 1)) + 1 := by omega
    have hindex : j - 1 - (j - (J + 1)) = J := by omega
    simp only [hsub, fordPhiBackwardAux_succ, hindex]

@[simp] theorem fordCanonicalPhiSchedule_apply
    (k r j : ℕ) (delta : ℝ) (J : ℕ) :
    (fordCanonicalPhiSchedule k r j delta).phi J =
      fordPhiBackwardAux k r j delta (j - J) := rfl

#print axioms fordCanonicalPhiSchedule_apply

end

end GafniTao
