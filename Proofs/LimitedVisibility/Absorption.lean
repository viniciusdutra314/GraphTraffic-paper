import LimitedVisibility.MaximumPrinciple
import LimitedVisibility.Summability
import LimitedVisibility.HittingTime

/-! Absorption and finite moments follow from the Dirichlet comparison principle.
We apply the same summability lemma to p(n), n p(n), and n² p(n). -/
namespace LimitedVisibility
open Matrix
open scoped BigOperators
variable {U : Type*} [Fintype U] [DecidableEq U]

/- Weight the first-step equation. The exit term disappears because f(0)=0. -/
omit [DecidableEq U] in
theorem hittingMass_weighted_step (Q : Matrix U U ℝ) (f : ℕ → ℝ) (hf : f 0 = 0) (n : ℕ) :
    (fun i => hittingMass Q (n + 1) i * f (n + 1)) =
      (fun i => hittingMass Q (n + 1) i * (f (n + 1) - f n)) +
        Q *ᵥ (fun i => hittingMass Q n i * f n) := by
  ext i
  have he : (if n = 0 then exitWeight Q i else 0) * f n = 0 := by
    by_cases hn : n = 0 <;> simp [hn, hf]
  have hmul : hittingMass Q (n + 1) i * f n = ∑ j, Q i j * (hittingMass Q n j * f n) := by
    rw [hittingMass, add_mul, he, zero_add, Finset.sum_mul]
    simp only [mul_assoc]
  change _ = _ + ∑ j, Q i j * (hittingMass Q n j * f n)
  rw [← hmul]
  ring

/-- A finite nonnegative substochastic chain with the comparison principle
absorbs with probability one and has finite second moment. -/
theorem regular_of_comparison {Q : Matrix U U ℝ} (hN : IsUnit (1 - Q).det)
    (comparison : ∀ x, 0 ≤ (1 - Q) *ᵥ x → 0 ≤ x)
    (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j ≤ 1) : HittingRegular Q := by
  have hp := hittingMass_nonneg hQ hrow
  -- First sum the probabilities themselves.
  have hmass : ∀ i, Summable (fun n => hittingMass Q n i) := by
    apply summable_recurrence hN comparison (hittingMass Q)
      (fun n i => if n = 0 then exitWeight Q i else 0) hp
    · intro n i; split_ifs <;> simp_all [exitWeight, sub_nonneg]
    · intro i; exact (hasSum_ite_eq 0 (exitWeight Q i)).summable
    · rfl
    · intro n; rfl
  -- The total mass solves the same Dirichlet problem as the constant one.
  have htotal : ∀ i, HasSum (fun n => hittingMass Q n i) 1 := by
    let s : U → ℝ := fun i => ∑' n, hittingMass Q n i
    have hs : (1 - Q) *ᵥ s = (1 - Q) *ᵥ ones := by
      simp only [sub_mulVec, one_mulVec]
      ext i
      have hstep := hasSum_hitting_step Q (fun _ => 1) s
        (fun j => by simpa using (hmass j).hasSum) i
      have hshift := (hasSum_nat_add_iff' 1).mpr (hmass i).hasSum
      simp only [Finset.sum_range_one, hittingMass, sub_zero] at hshift
      have he := hshift.unique (by simpa using hstep)
      simp only [sub_mulVec, one_mulVec, Pi.sub_apply, mulVec, dotProduct, ones, mul_one]
      change s i - ∑ j, Q i j * s j = 1 - ∑ j, Q i j
      change s i = exitWeight Q i + ∑ j, Q i j * s j at he
      dsimp [exitWeight] at he
      linarith
    have hs1 : s = ones :=
      Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr hN) hs
    intro i
    convert (hmass i).hasSum using 1
    exact (congrFun hs1 i).symm
  -- Apply the same lemma to the first and second weighted masses.
  have hfirst : ∀ i, Summable (fun n => hittingMass Q n i * (n : ℝ)) := by
    apply summable_recurrence hN comparison
      (fun n i => hittingMass Q n i * (n : ℝ)) (fun n => hittingMass Q (n + 1))
    · intro n i; exact mul_nonneg (hp n i) (Nat.cast_nonneg n)
    · intro n; exact hp (n + 1)
    · intro i; exact (summable_nat_add_iff (f := fun n => hittingMass Q n i) 1).mpr (hmass i)
    · ext i; simp
    · intro n
      simpa using hittingMass_weighted_step Q (fun n => (n : ℝ)) (by simp) n
  refine ⟨htotal, ?_⟩
  apply summable_recurrence hN comparison
    (fun n i => hittingMass Q n i * (n : ℝ) ^ 2)
    (fun n i => hittingMass Q (n + 1) i * (2 * (n : ℝ) + 1))
  · intro n i; exact mul_nonneg (hp n i) (sq_nonneg _)
  · intro n i; exact mul_nonneg (hp (n + 1) i) (by positivity)
  · intro i
    convert (((summable_nat_add_iff (f := fun n => hittingMass Q n i * (n : ℝ)) 1).mpr (hfirst i)).mul_left 2).sub
      ((summable_nat_add_iff (f := fun n => hittingMass Q n i) 1).mpr (hmass i)) using 1
    ext n; push_cast; ring
  · ext i; simp
  · intro n
    convert hittingMass_weighted_step Q (fun n => (n : ℝ) ^ 2) (by simp) n using 1
    ext i
    simp only [Pi.add_apply, Nat.cast_add, Nat.cast_one]
    ring

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- No probabilistic assumption: a finite connected graph supplies regularity. -/
theorem graph_regular (hG : G.Connected) (t : V) (r : ℕ) :
    HittingRegular (transition G t r) :=
  regular_of_comparison (transition_det_isUnit G hG t r)
    (transition_comparison G hG t r) (transition_nonneg G t r)
    (transition_substochastic G hG t r)

end LimitedVisibility
