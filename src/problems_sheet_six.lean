import tactic
import data.real.basic
import data.pnat.basic
import measure_theory.interval_integral

local notation `|` x `|` := abs x

def is_limit (a : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, | a n - l | < ε

def is_convergent (a : ℕ → ℝ) : Prop :=
∃ l : ℝ, is_limit a l

open real

noncomputable def question1a : ℕ → ℝ
| 0 := 1
| (n+1) := sqrt(2*(question1a n))

-- guess : converges to 2
theorem question1 : is_convergent question1a :=
begin
  sorry
end

-- Q2 -- need to know what ratio test is

-- Q3 -- should be possible

-- for each part, precisely one of 1 and 2 is true. Prove the true one
-- and delete the other one

theorem q4a1 (an : ℕ → ℝ) : 
  (∃ a : ℝ, ∀ ε > 0, ∀ N : ℕ, ∃ n ≥ N, | an n - a | < ε) → 
  (∃ a : ℝ, ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, | an n - a | < ε) 
:= sorry

theorem q4a2 (an : ℕ → ℝ) : 
  (∃ a : ℝ, ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, | an n - a | < ε) → 
  (∃ a : ℝ, ∀ ε > 0, ∀ N : ℕ, ∃ n ≥ N, | an n - a | < ε)
:= sorry

theorem q4b1 (an : ℕ → ℝ) : 
  (∃ a : ℝ, ∀ ε > 0, ∀ N : ℕ, ∃ n ≥ N, | an n - a | < ε) → 
  (∃ a : ℝ, ∃ ε > 0, ∀ N : ℕ, ∀ n ≥ N, | an n - a | < ε) 
:= sorry

theorem q4b2 (an : ℕ → ℝ) : 
  (∃ a : ℝ, ∃ ε > 0, ∀ N : ℕ, ∀ n ≥ N, | an n - a | < ε) →
  (∃ a : ℝ, ∀ ε > 0, ∀ N : ℕ, ∃ n ≥ N, | an n - a | < ε)
:= sorry

theorem q4c1 (an : ℕ → ℝ) : 
  (∃ a : ℝ, ∀ ε > 0, ∀ N : ℕ, ∃ n ≥ N, | an n - a | < ε) → 
  (∀ a : ℝ, ∃ ε > 0, ∀ N : ℕ, ∀ n ≥ N, | an n - a | < ε) 
:= sorry

theorem q4c2 (an : ℕ → ℝ) : 
  (∀ a : ℝ, ∃ ε > 0, ∀ N : ℕ, ∀ n ≥ N, | an n - a | < ε) →
  (∃ a : ℝ, ∀ ε > 0, ∀ N : ℕ, ∃ n ≥ N, | an n - a | < ε)
:= sorry

theorem q4d1 (an : ℕ → ℝ) : 
  (∃ a : ℝ, ∀ ε > 0, ∀ N : ℕ, ∃ n ≥ N, | an n - a | < ε) →
  (∃ a : ℝ, ∃ N : ℕ, ∀ ε > 0, ∀ n ≥ N, | an n - a | < ε) 
:= sorry

theorem q4d2 (an : ℕ → ℝ) : 
  (∃ a : ℝ, ∃ N : ℕ, ∀ ε > 0, ∀ n ≥ N, | an n - a | < ε) →
  (∃ a : ℝ, ∀ ε > 0, ∀ N : ℕ, ∃ n ≥ N, | an n - a | < ε)
:= sorry

open_locale big_operators

open finset

def is_sum (a : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, | (∑ i in range n, a i) - l | < ε

def sum_is_convergent (a : ℕ → ℝ) : Prop :=
∃ l : ℝ, is_sum a l

theorem Q7 (a : ℕ → ℝ) (c : ℝ) (l : ℝ) : is_sum a l → is_sum (λ n, c * a n) (c * l) :=
begin
  sorry
end

