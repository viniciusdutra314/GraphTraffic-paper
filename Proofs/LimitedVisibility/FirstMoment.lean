import LimitedVisibility.FundamentalMatrix

namespace LimitedVisibility
open Matrix
variable {U : Type*} [Fintype U] [DecidableEq U]
variable {Q : Matrix U U ℝ}
local notation "N" => (1 - Q)⁻¹

theorem meanVector_equation (hN : IsUnit (1 - Q).det) :
    meanVector N = ones + Q *ᵥ meanVector N := by
  have h : (1 - Q) *ᵥ meanVector N = ones := by
    simp only [meanVector, mulVec_mulVec, Matrix.mul_nonsing_inv _ hN, one_mulVec]
  rw [sub_mulVec, one_mulVec] at h
  exact sub_eq_iff_eq_add.mp h

/-- Theorem A: existence and uniqueness of the first-step solution. -/
theorem firstMoment_unique (hN : IsUnit (1 - Q).det) {m : U → ℝ}
    (hm : m = ones + Q *ᵥ m) : m = meanVector N := by
  letI := Matrix.invertibleOfIsUnitDet (1 - Q) hN
  apply (Matrix.inv_mulVec_eq_vec ?_).symm
  symm
  rw [sub_mulVec, one_mulVec]
  exact sub_eq_iff_eq_add.mpr hm

theorem firstMoment_existsUnique (hN : IsUnit (1 - Q).det) :
    ∃! m : U → ℝ, m = ones + Q *ᵥ m :=
  ⟨meanVector N, meanVector_equation hN, fun _ h => firstMoment_unique hN h⟩

end LimitedVisibility
