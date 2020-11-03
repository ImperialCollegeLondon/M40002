
import tactic
import data.real.basic
import data.real.irrational

-- Q1) what's the biggest element of {x ∈ ℝ | x < 1}?

theorem soln1 : ∀ a ∈ {x : ℝ | x < 1}, ∃ b ∈ {x : ℝ | x < 1}, a < b :=
begin
  intro a,
  rintro (ha : a < 1),
  use (a + 1) / 2,
  split,
  { simp,
    linarith },
  linarith,
end

open real

-- Q2) Prove that for every positive intger n ≠ 3, √n - √3 is irrational
theorem soln2 : ∀ n : ℕ, 0 < n ∧ n ≠ 3 → irrational (sqrt (n : ℝ) - sqrt 3) :=
begin
  rintros n ⟨hn0, hn3⟩ hq,
  rw set.mem_range at hq,
  cases hq with q hq,
  have hq1 := add_eq_of_eq_sub hq,
  apply_fun (λ x, x * x) at hq1,
  have h3 : (0 : ℝ) ≤ 3 := by norm_num,
  simp [mul_add, add_mul, h3] at hq1,
  have hq2 : (2 : ℝ) * q * sqrt 3 = n - q * q - 3,
    rw ← hq1, ring,
  let r : ℚ := n - q * q - 3,
  have hq3 : (2 : ℝ) * q * sqrt 3 = r,
    convert hq2,
    norm_cast,
  clear hq1,
  clear hq2,
  have s3 : irrational (sqrt ((3 : ℕ) : ℝ)),
    apply nat.prime.irrational_sqrt,
    norm_num,
  simp at s3,
  have temp : (2 : ℝ) * q * sqrt 3 = sqrt 3 * ((2 : ℚ) * q : ℚ),
    rw mul_comm ((2 : ℝ) * _),
    norm_cast,
  rw temp at hq3,
  apply irrational.mul_rat s3,
  swap,
  use r,
  exact hq3.symm,
  clear hq3 r s3 temp,
  intro h,
  rw mul_eq_zero at h,
  cases h, linarith,
  rw h at hq,
  simp at hq,
  symmetry' at hq,
  rw sub_eq_zero at hq,
  apply hn3,
  apply_fun (λ x, x * x) at hq,
  simp [h3] at hq,
  norm_cast at hq,
end

-- show x = 1.23454545454... is rational
-- 10000 x = 12345.4545454545...
-- 9999 x = 12344.22
-- 999900 x = 123422

