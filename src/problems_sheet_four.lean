import tactic
import data.real.basic
import data.pnat.basic

local notation `|` x `|` := abs x

def is_limit (a : ℕ+ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, | a n - l | < ε

def is_convergent (a : ℕ+ → ℝ) : Prop :=
∃ l : ℝ, is_limit a l


/-
1. Consider the following properties of a sequence of real numbers (a n ) n≥0 :
(i) a_n → a, or
(ii) “a_n eventually equals a” – i.e. ∃N ∈ N such that ∀n ≥ N, a n = a, or
(iii) “(a_n ) is bounded” – i.e. ∃ R ∈ R such that |a n | < R ∀n ∈ N.
For each statement (a-e) below, which of (i-iii) is it equivalent to? Proof?
(a) ∃ N ∈ N such that ∀n ≥ N, ∀ε > 0, |a n − a| < ε.
(b) ∀ε > 0 there are only finitely many n ∈ N for which |a n − a| ≥ ε.
(c) ∀N ∈ N, ∃ ε > 0 such that n ≥ N ⇒ |a n − a| < ε.
(d) ∃ ε > 0 such that ∀N ∈ N, |a n − a| < ε ∀n ≥ N .
(e) ∀R > 0 ∃ N ∈ N such that n ≥ N ⇒ a n ∈ (a − 1/R , a + 1/R ).
-/

namespace sheet4

section Q1

def Q1i (an : ℕ+ → ℝ) (a : ℝ) := is_limit an a
def Q1ii (an : ℕ+ → ℝ) (a : ℝ) := ∃ N : ℕ+, ∀ n, N ≤ n → an n = a
def Q1iii (an : ℕ+ → ℝ) := ∃ R : ℝ, ∀ n : ℕ+, |an n| < R

-- instructions: change thing on RHS of ↔ to `Q1ii an a` or `Q1iii an`
-- as appropriate, then prove
theorem Q1a (an : ℕ+ → ℝ) (a : ℝ) :
  (∃ N : ℕ+, ∀ n, N ≤ n → ∀ ε, 0 < ε → |an n - a| < ε) ↔ Q1i an a :=
begin
  sorry
end

theorem Q1b (an : ℕ+ → ℝ) (a : ℝ) :
  (∀ ε, 0 < ε → {n : ℕ+ | ε ≤ |an n - a|}.finite) ↔ Q1i an a :=
begin
  sorry
end

theorem Q1c (an : ℕ+ → ℝ) (a : ℝ) :
  (∀ N : ℕ+, ∃ ε > 0, ∀ n ≥ N, |an n - a| < ε) ↔ Q1i an a :=
begin
  sorry
end

theorem Q1d (an : ℕ+ → ℝ) (a : ℝ) :
  (∃ ε > 0, ∀ N : ℕ+, ∀ n ≥ N, |an n - a| < ε) ↔ Q1i an a :=
begin
  sorry
end

open set

theorem Q1e (an : ℕ+ → ℝ) (a : ℝ) :
  (∀R > 0, ∃ N : ℕ+, ∀ n ≥ N, an n ∈ Ioo (a - 1/R) (a + 1/R)) ↔ Q1i an a :=
begin
  sorry
end
 
end Q1

section Q3
/-
3. Suppose that a n ≤ b n ≤ c n ∀n and that a n → a and c n → a. Prove that b n → a.
-/

theorem Q3sandwich (a b c : ℕ+ → ℝ) (l : ℝ) (hab : ∀ n, a n ≤ b n)
  (hbc : ∀ n, b n ≤ c n) (ha : is_limit a l) (hc : is_limit c l) :
  is_limit b l :=
begin
  sorry
end

end Q3

/-
4. Suppose that aₙ → 0 and (bₙ) is bounded. Prove that aₙ bₙ → 0.
-/

/-- A sequence (aₙ) is bounded if there's some R such that |aₙ|≤ R for all n. -/
def is_bounded (a : ℕ+ → ℝ) := ∃ R : ℝ, ∀ n, |a n| ≤ R

section Q4 

theorem Q4 (a b : ℕ+ → ℝ) (l : ℝ) (ha : is_limit a 0) (hb : is_bounded b) :
  is_limit (λ n, a n * b n) 0 :=
begin
  sorry
end

end Q4

section Q5
-- let's do it properly

theorem is_bounded_of_is_convergent {a : ℕ+ → ℝ} (ha : is_convergent a) :
  is_bounded a :=
begin
  sorry
end

theorem limit_add_const {a : ℕ+ → ℝ} (l t : ℝ) (hal : is_limit a l) :
  is_limit (λ n, t + a n) (t + l) :=
begin
  sorry
end

theorem limit_mul_const {a : ℕ+ → ℝ} {l : ℝ} (hal : is_limit a l) (t : ℝ) :
  is_limit (λ n, t * a n) (t * l) :=
begin
  sorry
end

theorem limit_add {a b : ℕ+ → ℝ} {l m : ℝ} (hal : is_limit a l) (hbm : is_limit b m) :
  is_limit (λ n, a n + b n) (l + m) :=
begin
  sorry
end

theorem limit_zero_mul_limit_zero {a b : ℕ+ → ℝ} (hal : is_limit a 0)
  (hbm : is_limit b 0) : is_limit (λ n, a n * b n) 0 :=
begin
  sorry
end

theorem mul_limit {a b : ℕ+ → ℝ} {l m : ℝ} (hal : is_limit a l)
  (hb : is_limit b m) : is_limit (λ n, a n * b n) (l * m) :=
begin
  sorry
end

theorem inv_limit {a : ℕ+ → ℝ} {l : ℝ} (hl : l ≠ 0) (hal : is_limit a l) :
  is_limit (λ n, (a n)⁻¹) l⁻¹ :=
begin
  sorry
end

theorem div_limit {a b : ℕ+ → ℝ} {l m : ℝ} (hl : m ≠ 0) (hal : is_limit a l)
  (hb : is_limit b m) : is_limit (λ n, a n / b n) (l / m) :=
begin
  sorry
end

end Q5

end sheet4

