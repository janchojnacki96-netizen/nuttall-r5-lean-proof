import W5.VerifiedIntervalRealSemantics
import Mathlib.Data.Rat.Floor

namespace Nuttall

open W5

theorem compactContainsReal_of_endpoints {A B : QInterval} {x : ℝ}
    (hlo : B.lo ≤ A.lo) (hhi : A.hi ≤ B.hi) (h : A.ContainsReal x) : B.ContainsReal x :=
  ⟨(Rat.cast_mono hlo).trans h.1, h.2.trans (Rat.cast_mono hhi)⟩

/-- Round an interval outwards to the grid with the specified denominator. -/
def compactRoundInterval (scale : ℚ) (I : QInterval) : QInterval :=
  ⟨(⌊I.lo * scale⌋ : ℤ) / scale, (⌈I.hi * scale⌉ : ℤ) / scale⟩

theorem compactRoundInterval_containsReal {scale : ℚ} (hscale : 0 < scale)
    {I : QInterval} {x : ℝ} (h : I.ContainsReal x) :
    (compactRoundInterval scale I).ContainsReal x :=
  compactContainsReal_of_endpoints ((div_le_iff₀ hscale).mpr (Int.floor_le _))
    ((le_div_iff₀ hscale).mpr (Int.le_ceil _)) h

end Nuttall
