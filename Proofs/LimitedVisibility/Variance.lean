import LimitedVisibility.HittingTime
import LimitedVisibility.SecondMoment

namespace LimitedVisibility
open Matrix
variable {U : Type*} [Fintype U] [DecidableEq U]
variable {Q : Matrix U U ℝ}
local notation "N" => (1 - Q)⁻¹

theorem hittingMean_formula (hN : IsUnit (1 - Q).det) (h : HittingRegular Q)
    (hn : ∀ n i, 0 ≤ hittingMass Q n i) : hittingMean Q = meanVector N :=
  firstMoment_unique hN (hittingMean_firstStep h hn)

theorem hittingSecond_formula (hN : IsUnit (1 - Q).det) (h : HittingRegular Q)
    (hn : ∀ n i, 0 ≤ hittingMass Q n i) : hittingSecond Q = secondVector N :=
  secondMoment_unique hN (hittingMean_firstStep h hn) (hittingSecond_firstStep h hn)

theorem hittingVariance_formula (hN : IsUnit (1 - Q).det) (h : HittingRegular Q)
    (hn : ∀ n i, 0 ≤ hittingMass Q n i) (i : U) :
    (hittingLaw h hn i).variance (fun n => (n : ℝ)) =
      secondVector N i - (meanVector N i) ^ 2 := by
  rw [DiscreteLaw.variance_eq_second_sub_sq (hittingLaw h hn i) (X := fun n => (n : ℝ)) (h.first hn i) (h.second i)]
  rw [DiscreteLaw.expect_eq_tsum (hittingLaw h hn i) (X := fun n => (n : ℝ) ^ 2) (h.second i), DiscreteLaw.expect_eq_tsum (hittingLaw h hn i) (X := fun n => (n : ℝ)) (h.first hn i)]
  change hittingSecond Q i - (hittingMean Q i) ^ 2 = _
  rw [hittingMean_formula hN h hn, hittingSecond_formula hN h hn]

theorem shifted_hitting_statistics (hN : IsUnit (1 - Q).det) (h : HittingRegular Q)
    (hn : ∀ n i, 0 ≤ hittingMass Q n i) (i : U) (c : ℝ) :
    (hittingLaw h hn i).expect (fun n => (n : ℝ) + c) = c + meanVector N i ∧
    (hittingLaw h hn i).variance (fun n => (n : ℝ) + c) =
      secondVector N i - (meanVector N i) ^ 2 := by
  constructor
  · rw [DiscreteLaw.expect_add_const (hittingLaw h hn i) (X := fun n => (n : ℝ)) (h.first hn i)]
    rw [DiscreteLaw.expect_eq_tsum (hittingLaw h hn i) (X := fun n => (n : ℝ)) (h.first hn i)]
    change hittingMean Q i + c = _
    rw [hittingMean_formula hN h hn, add_comm]
  · rw [DiscreteLaw.variance_add_const (hittingLaw h hn i) (X := fun n => (n : ℝ)) (h.first hn i)]
    exact hittingVariance_formula hN h hn i

end LimitedVisibility
