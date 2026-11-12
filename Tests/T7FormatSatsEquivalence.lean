import BitcoinLedger.FreestandingKernels

namespace Tests.T7FormatSatsEquivalence

open BitcoinLedger.FreestandingKernels

theorem bnot_decide_eq {α : Type} [DecidableEq α] (x y : α) :
    bnot (decide (x = y)) = decide (x ≠ y) := by
  by_cases h : x = y <;> simp [h, bnot]

theorem formatter_conditions_eq_parent (padFrac8 : UInt8) (frac tickerLen : UInt32) :
    (bnot (decide (padFrac8 = 0)),
      bor (bnot (decide (padFrac8 = 0))) (bnot (decide (frac = 0))),
      bnot (decide (tickerLen = 0))) =
    (decide (padFrac8 ≠ 0),
      bor (decide (padFrac8 ≠ 0)) (decide (frac ≠ 0)),
      decide (tickerLen ≠ 0)) := by
  simp only [bnot_decide_eq]

#print axioms bnot_decide_eq
#print axioms formatter_conditions_eq_parent

end Tests.T7FormatSatsEquivalence
