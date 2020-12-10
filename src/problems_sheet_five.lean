import tactic
import data.real.basic
import data.pnat.basic

local notation `|` x `|` := abs x

def is_limit (a : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, | a n - l | < ε

def tends_to_plus_infinity (a : ℕ → ℝ) : Prop :=
∀ B, ∃ N, ∀ n ≥ N, B < a n 

def is_convergent (a : ℕ → ℝ) : Prop :=
∃ l : ℝ, is_limit a l

namespace sheet_five

theorem Q1a (x : ℝ) (hx : 0 < x) (n : ℕ) : (1 : ℝ) + n * x ≤ (1 + x)^n :=
begin
  sorry
end

theorem Q1b (x : ℝ) (hx : 0 < x) : is_limit (λ n, (1 + x) ^ (-(n : ℤ))) 0 :=
begin
  sorry
end

theorem Q1c (r : ℝ) (hr : r ∈ set.Ioo (0 : ℝ) 1) : is_limit (λ n, r ^ n) 0 :=
begin
  sorry
end

theorem Q1d (r : ℝ) (hr : 1 < r) : tends_to_plus_infinity (λ n, r ^ n) :=
begin
  sorry
end
