import LimitedVisibility.FirstMoment

namespace LimitedVisibility
open Matrix
variable {U : Type*} [Fintype U] [DecidableEq U]
variable {Q : Matrix U U ℝ}
local notation "N" => (1 - Q)⁻¹

/-- Explicit reduction of N(1 + 2 Q N 1) to (2N-I)N1. -/
theorem secondMoment_simplify (hN : IsUnit (1 - Q).det) :
    N *ᵥ (ones + (2 : ℝ) • (Q *ᵥ meanVector N)) = secondVector N := by
  have hQ : Q *ᵥ meanVector N = meanVector N - ones :=
    eq_sub_of_add_eq (by simpa [add_comm] using (meanVector_equation hN).symm)
  rw [hQ, mulVec_add, mulVec_smul, mulVec_sub]
  unfold secondVector meanVector
  rw [sub_mulVec, smul_mulVec_assoc, one_mulVec]
  module

theorem secondMoment_unique (hN : IsUnit (1 - Q).det) {m z : U → ℝ}
    (hm : m = ones + Q *ᵥ m)
    (hz : z = ones + (2 : ℝ) • (Q *ᵥ m) + Q *ᵥ z) :
    z = secondVector N := by
  have hlin : (1 - Q) *ᵥ z = ones + (2 : ℝ) • (Q *ᵥ m) := by
    rw [sub_mulVec, one_mulVec]
    exact sub_eq_iff_eq_add.mpr hz
  letI := Matrix.invertibleOfIsUnitDet (1 - Q) hN
  rw [← Matrix.inv_mulVec_eq_vec hlin.symm, firstMoment_unique hN hm]
  exact secondMoment_simplify hN

end LimitedVisibility
