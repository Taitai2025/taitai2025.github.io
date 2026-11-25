import Init

namespace ADMMAlternatingPenalty

-- Integer numerator of k^3 F(k + k^{-1}) for k > 0.
def thresholdNumerator (k : Int) : Int :=
  let u := k * k + 1
  u * u * u - 123 * u * u * k - 400 * u * k * k - 316 * k * k * k

theorem exactLowerSign : thresholdNumerator 126 < 0 := by decide
theorem exactUpperSign : 0 < thresholdNumerator 127 := by decide
theorem exactExampleSign : 0 < thresholdNumerator 199 := by decide

-- Common-denominator identity for 1 + trace + determinant at k = 199.
theorem exactExampleCharacteristicIdentity :
    ((6368000 * 6400000000 - 14467601 * 6400000000 + 888099601 * 6368000 : Int)
      * 1273600000000) =
      -1443188379401 * (6368000 * 6400000000) := by decide

end ADMMAlternatingPenalty

#print axioms ADMMAlternatingPenalty.exactLowerSign
#print axioms ADMMAlternatingPenalty.exactUpperSign
#print axioms ADMMAlternatingPenalty.exactExampleSign
#print axioms ADMMAlternatingPenalty.exactExampleCharacteristicIdentity
