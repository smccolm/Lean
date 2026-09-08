import GafniTao.FordExplicitData.Values

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

def fordPositiveTaylorPower1 : Polynomial ℚ :=
  ((((((Polynomial.C (7 / 7653143520 : ℚ) * Polynomial.X + Polynomial.C (-1 / 19326120 : ℚ)) * Polynomial.X + Polynomial.C (1 / 351384 : ℚ)) * Polynomial.X + Polynomial.C (-1 / 7986 : ℚ)) * Polynomial.X + Polynomial.C (1 / 242 : ℚ)) * Polynomial.X + Polynomial.C (-1 / 11 : ℚ)) * Polynomial.X + Polynomial.C (1 : ℚ))

end

end GafniTao
