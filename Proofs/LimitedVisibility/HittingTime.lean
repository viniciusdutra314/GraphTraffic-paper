import LimitedVisibility.DiscreteProbability
import LimitedVisibility.FirstMoment

/-! A killed finite chain, constructed from its first-hit probabilities.  No
moment equation is postulated: they are derived from this recursion. -/
namespace LimitedVisibility
open Matrix
open scoped BigOperators

variable {U : Type*} [Fintype U]

noncomputable def exitWeight (Q : Matrix U U ℝ) (i : U) : ℝ := 1 - ∑ j, Q i j

/-- Probability of first absorption at exactly time n, starting in i.
The exit term is nonzero only for absorption on the very first step. -/
noncomputable def hittingMass (Q : Matrix U U ℝ) : ℕ → U → ℝ
  | 0, _ => 0
  | n + 1, i => (if n = 0 then exitWeight Q i else 0) + ∑ j, Q i j * hittingMass Q n j

theorem hittingMass_nonneg {Q : Matrix U U ℝ}
    (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j ≤ 1) :
    ∀ n i, 0 ≤ hittingMass Q n i := by
  intro n
  induction n with
  | zero => intro i; rfl
  | succ n ih =>
    intro i
    apply add_nonneg
    · split_ifs
      · exact sub_nonneg.mpr (hrow i)
      · rfl
    · exact Finset.sum_nonneg (fun j _ => mul_nonneg (hQ i j) (ih j))

/-- Analytic properties of the hitting law, proved for every finite connected
graph by `graph_regular`; packaged for reuse in the moment lemmas. -/
structure HittingRegular (Q : Matrix U U ℝ) : Prop where
  total : ∀ i, HasSum (fun n => hittingMass Q n i) 1
  second : ∀ i, Summable (fun n => hittingMass Q n i * (n : ℝ) ^ 2)

noncomputable def hittingMean (Q : Matrix U U ℝ) (i : U) : ℝ :=
  ∑' n, hittingMass Q n i * (n : ℝ)

noncomputable def hittingSecond (Q : Matrix U U ℝ) (i : U) : ℝ :=
  ∑' n, hittingMass Q n i * (n : ℝ) ^ 2

theorem HittingRegular.first {Q : Matrix U U ℝ} (h : HittingRegular Q)
    (hn : ∀ n i, 0 ≤ hittingMass Q n i) (i : U) :
    Summable (fun n => hittingMass Q n i * (n : ℝ)) := by
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (hn n i) (Nat.cast_nonneg n))
    (fun n => ?_) (h.second i)
  apply mul_le_mul_of_nonneg_left _ (hn n i)
  exact_mod_cast Nat.le_self_pow (by decide : 2 ≠ 0) n

noncomputable def hittingLaw {Q : Matrix U U ℝ} (h : HittingRegular Q)
    (hn : ∀ n i, 0 ≤ hittingMass Q n i) (i : U) : DiscreteLaw :=
  ⟨fun n => hittingMass Q n i, fun n => hn n i, h.total i⟩

/-- Summing the concrete one-step law against any shifted observable. -/
theorem hasSum_hitting_step (Q : Matrix U U ℝ) (f : ℕ → ℝ) (b : U → ℝ)
    (hb : ∀ j, HasSum (fun n => hittingMass Q n j * f (n + 1)) (b j)) (i : U) :
    HasSum (fun n => hittingMass Q (n + 1) i * f (n + 1))
      (exitWeight Q i * f 1 + ∑ j, Q i j * b j) := by
  have he : HasSum (fun n : ℕ => (if n = 0 then exitWeight Q i else 0) * f (n + 1))
      (exitWeight Q i * f 1) := by
    convert hasSum_ite_eq 0 (exitWeight Q i * f 1) using 1
    ext n
    by_cases hn : n = 0 <;> simp [hn]
  simpa only [hittingMass, add_mul, Finset.sum_mul, mul_assoc] using
    he.add (hasSum_sum (s := Finset.univ) (fun j _ => (hb j).mul_left (Q i j)))

/-- Theorem B: first-step analysis, proved from the first-hit distribution. -/
theorem hittingMean_firstStep {Q : Matrix U U ℝ} (h : HittingRegular Q)
    (hn : ∀ n i, 0 ≤ hittingMass Q n i) :
    hittingMean Q = ones + Q *ᵥ hittingMean Q := by
  have hb : ∀ j, HasSum (fun n => hittingMass Q n j * ((n + 1 : ℕ) : ℝ))
      (1 + hittingMean Q j) := by
    intro j
    convert (h.total j).add (h.first hn j).hasSum using 1
    · ext n; push_cast; ring
  ext i
  have hs := hasSum_hitting_step Q (fun n => (n : ℝ)) _ hb i
  have hm := (hasSum_nat_add_iff' 1).mpr (h.first hn i).hasSum
  simp only [Finset.sum_range_one, hittingMass, zero_mul, sub_zero] at hm
  have he := hm.unique hs
  simp only [exitWeight, Nat.cast_one, mul_one, mul_add, Finset.sum_add_distrib] at he
  change hittingMean Q i = 1 + ∑ j, Q i j * hittingMean Q j
  dsimp [hittingMean] at he ⊢
  linarith

theorem hittingSecond_firstStep {Q : Matrix U U ℝ} (h : HittingRegular Q)
    (hn : ∀ n i, 0 ≤ hittingMass Q n i) :
    hittingSecond Q = ones + (2 : ℝ) • (Q *ᵥ hittingMean Q) + Q *ᵥ hittingSecond Q := by
  have hb : ∀ j, HasSum (fun n => hittingMass Q n j * (((n + 1 : ℕ) : ℝ) ^ 2))
      (1 + 2 * hittingMean Q j + hittingSecond Q j) := by
    intro j
    convert ((h.total j).add ((h.first hn j).hasSum.mul_left 2)).add
      (h.second j).hasSum using 1
    · ext n; push_cast; ring
  ext i
  have hs := hasSum_hitting_step Q (fun n => (n : ℝ) ^ 2) _ hb i
  have hz := (hasSum_nat_add_iff' 1).mpr (h.second i).hasSum
  simp only [Finset.sum_range_one, hittingMass, zero_mul, sub_zero] at hz
  have he := hz.unique hs
  simp only [exitWeight, Nat.cast_one, one_pow, mul_one, mul_add, Finset.sum_add_distrib] at he
  simp_rw [mul_left_comm (Q i _) 2, ← Finset.mul_sum] at he
  change hittingSecond Q i = 1 + 2 * (∑ j, Q i j * hittingMean Q j) +
    ∑ j, Q i j * hittingSecond Q j
  dsimp [hittingSecond] at he ⊢
  linarith

end LimitedVisibility
