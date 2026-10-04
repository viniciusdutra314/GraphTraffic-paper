import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Variance
import Mathlib.Tactic

namespace LimitedVisibility

/-- A countable probability law, with real weights and explicit normalization. -/
structure DiscreteLaw where
  mass : ℕ → ℝ
  nonneg : ∀ n, 0 ≤ mass n
  total : HasSum mass 1

namespace DiscreteLaw

noncomputable def toPMF (p : DiscreteLaw) : PMF ℕ :=
  ⟨fun n => ENNReal.ofReal (p.mass n), by
    have he : (∑' n, ENNReal.ofReal (p.mass n)) = 1 := by
      rw [← ENNReal.ofReal_tsum_of_nonneg p.nonneg p.total.summable, p.total.tsum_eq]
      simp
    exact he ▸ ENNReal.summable.hasSum⟩

@[simp] theorem toPMF_real (p : DiscreteLaw) (n : ℕ) :
    (p.toPMF n).toReal = p.mass n := ENNReal.toReal_ofReal (p.nonneg n)

/-- Use mathlib's expectation and variance directly. -/
noncomputable def expect (p : DiscreteLaw) (X : ℕ → ℝ) : ℝ :=
  ∫ n, X n ∂p.toPMF.toMeasure

noncomputable def variance (p : DiscreteLaw) (X : ℕ → ℝ) : ℝ :=
  ProbabilityTheory.variance X p.toPMF.toMeasure

/-- Summability of real weights is exactly the needed integrability condition. -/
theorem integrable_of_summable (p : DiscreteLaw) {X : ℕ → ℝ}
    (hX : Summable (fun n => p.mass n * X n)) :
    MeasureTheory.Integrable X p.toPMF.toMeasure := by
  refine ⟨(measurable_of_countable X).aestronglyMeasurable, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_norm, MeasureTheory.lintegral_countable']
  have hn : Summable (fun n => p.mass n * ‖X n‖) := by
    simpa only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (p.nonneg _)] using hX.norm
  simp_rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  change (∑' n, ENNReal.ofReal ‖X n‖ * ENNReal.ofReal (p.mass n)) < ⊤
  simp_rw [mul_comm (ENNReal.ofReal ‖X _‖), ← ENNReal.ofReal_mul (p.nonneg _)]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (p.nonneg n) (norm_nonneg _)) hn]
  exact ENNReal.ofReal_lt_top

theorem expect_eq_tsum (p : DiscreteLaw) {X : ℕ → ℝ}
    (hX : Summable (fun n => p.mass n * X n)) :
    p.expect X = ∑' n, p.mass n * X n := by
  rw [expect, PMF.integral_eq_tsum _ _ (p.integrable_of_summable hX)]
  simp [smul_eq_mul]

theorem expect_const (p : DiscreteLaw) (c : ℝ) : p.expect (fun _ => c) = c := by
  simp [expect]

theorem expect_add_const (p : DiscreteLaw) {X : ℕ → ℝ}
    (hX : Summable (fun n => p.mass n * X n)) (c : ℝ) :
    p.expect (fun n => X n + c) = p.expect X + c := by
  simp [expect, MeasureTheory.integral_add (p.integrable_of_summable hX)
    (MeasureTheory.integrable_const c)]

theorem variance_eq_second_sub_sq (p : DiscreteLaw) {X : ℕ → ℝ}
    (hX : Summable (fun n => p.mass n * X n))
    (hX2 : Summable (fun n => p.mass n * (X n) ^ 2)) :
    p.variance X = p.expect (fun n => (X n) ^ 2) - (p.expect X) ^ 2 := by
  exact ProbabilityTheory.variance_def' ((MeasureTheory.memLp_two_iff_integrable_sq
    (p.integrable_of_summable hX).aestronglyMeasurable).mpr (p.integrable_of_summable hX2))

theorem variance_add_const (p : DiscreteLaw) {X : ℕ → ℝ}
    (hX : Summable (fun n => p.mass n * X n)) (c : ℝ) :
    p.variance (fun n => X n + c) = p.variance X := by
  simp only [variance, ProbabilityTheory.variance_eq_integral
    (measurable_of_countable _).aemeasurable]
  change (∫ n, (X n + c - p.expect (fun n => X n + c)) ^ 2 ∂p.toPMF.toMeasure) = _
  rw [p.expect_add_const hX c]
  congr 1
  ext n
  congr 1
  simp only [expect]
  ring

theorem variance_const (p : DiscreteLaw) (c : ℝ) : p.variance (fun _ => c) = 0 := by
  simp [variance, ProbabilityTheory.variance_eq_integral (measurable_of_countable _).aemeasurable]

/-- A degenerate probability space for an already visible source. -/
noncomputable def point : DiscreteLaw :=
  ⟨fun n => if n = 0 then 1 else 0, by intro n; dsimp only; split_ifs <;> norm_num,
    hasSum_ite_eq 0 1⟩

theorem deterministic_statistics (p : DiscreteLaw) (c : ℝ) :
    p.expect (fun _ => c) = c ∧ p.variance (fun _ => c) = 0 :=
  ⟨p.expect_const c, p.variance_const c⟩

end DiscreteLaw
end LimitedVisibility
