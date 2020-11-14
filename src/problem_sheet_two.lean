import tactic
import data.real.basic
import data.nat.choose.sum -- binomial theorem

/-!

# Q3 

Take bounded, nonempty `S, T ⊆ ℝ`.
Define `S + T := { s + t : s ∈ S, t ∈ T}`.
Prove `sup(S + T) = sup(S) + sup(T)`

-/

-- useful for rewriting
theorem is_lub_def {S : set ℝ} {a : ℝ} :
  is_lub S a ↔ a ∈ upper_bounds S ∧ ∀ x, x ∈ upper_bounds S → a ≤ x :=
begin
  refl
end

#check mem_upper_bounds -- a ∈ upper_bounds S ↔ ∀ x, x ∈ S → x ≤ a

/-
Useful tactics for this one: push_neg, specialize, have
-/
theorem useful_lemma {S : set ℝ} {a : ℝ} (haS : is_lub S a) (t : ℝ)
  (ht : t < a) : ∃ s, s ∈ S ∧ t < s :=
begin
  sorry
end

/-
Useful tactics for this one:
`rcases h with ⟨s, t, hsS, htT, rfl⟩` if h : x ∈ S + T
`linarith`
`by_contra`
`set ε := a + b - x with hε`
-/
theorem Q3 (S T : set ℝ) (a b : ℝ) :
  is_lub S a → is_lub T b → is_lub (S + T) (a + b) :=
begin
  sorry
end

/-!

# Q6

-/

-- We introduce the usual mathematical notation for absolute value
local notation `|` x `|` := abs x

/-
Useful for this one: `unfold`, `split_ifs` if you want to prove
from first principles, or guessing the name of the library function
if you want to use the library.
-/
theorem Q6a (x y : ℝ) : | x + y | ≤ | x | + | y | :=
begin
  sorry
end

-- all the rest you're supposed to do using Q6a somehow:
-- `simp` and `linarith` are useful.

theorem Q6b (x y : ℝ) : |x + y| ≥ |x| - |y| :=
begin
  sorry
end

theorem Q6c (x y : ℝ) : |x + y| ≥ |y| - |x| :=
begin
  sorry
end

theorem Q6d (x y : ℝ) : |x - y| ≥ | |x| - |y| | :=
begin
  sorry,
end

theorem Q6e (x y : ℝ) : |x| ≤ |y| + |x - y| :=
begin
  sorry
end

theorem Q6f (x y : ℝ) : |x| ≥ |y| - |x - y| :=
begin
  sorry
end

theorem Q6g (x y z : ℝ) : |x - y| ≤ |x - z| + |y - z| :=
begin
  sorry
end



/-!

# Q4

Fix `a ∈ (0,∞)` and `n : ℕ`. We will prove
`∃ x : ℝ, x^n = a`. 

-/

section Q4

noncomputable theory

section one

-- this first section, a and n are going to be variables
variables {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 0 < n)

include ha hn

-- Note: We do part 1 after parts 2,3,4 because on the problem sheet
-- parts 2,3,4 are written for the specific x=Sup(S) but
-- part 4 for x needs part 3 for 1/x so you can't use part 3 to
-- do part 4 the way it's been set up on the sheet. We prove
-- 2,3,4 for arbitrary 0 ≤ x (or 0 < x for 4)

/-
2) For `ε ∈ (0,1)` and arbitrary `x ≥ 0` show `(x+ε)ⁿ ≤ x^n + ε[(x + 1)ⁿ − xⁿ].`
(Hint: multiply out.)
-/

theorem part2 {x : ℝ} (x_nonneg : 0 ≤ x) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
  (x + ε)^n ≤ x^n + ε * ((x + 1)^n - x^n) :=
begin
  sorry,
end

/-
3) Hence show that if `x ≥ 0` and `xⁿ < a` then
`∃ ε ∈ (0,1)` such that `(x+ε)ⁿ < a.` (*)
-/

theorem part3 {x : ℝ} (x_nonneg : 0 ≤ x) (h : x ^ n < a) :
  ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ (x+ε)^n < a :=
begin
  sorry
end

/-
4) If `x > 0` is arbitrary and `xⁿ > a`, deduce from (∗) (i.e. part 3) that
`∃ ε ∈ (0,1)` such that `(1/x+ε)ⁿ < 1/a`. (∗∗)
-/

theorem part4 {x : ℝ} (hx : 0 < x) (h : a < x^n) : ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ (1/x + ε)^n < 1/a :=
begin
  sorry,
end

end one

section two

-- in this section, a and n are going to be fixed parameters

parameters {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 0 < n)

include ha hn
/-
1) Set `Sₐ := {s ∈ [0,∞) : s^n < a}` and show `Sₐ` is nonempty and
bounded above, so we may define `x := sup Sₐ` BUT WE WILL NOT DEFINE
x TO BE THIS YET.
-/

def S := {s : ℝ | 0 ≤ s ∧ s ^ n < a}

theorem part1 : (∃ s : ℝ, s ∈ S) ∧ (∃ B : ℝ, ∀ s ∈ S, s ≤ B ) :=
begin
  sorry
end


def x := Sup S

-- x is a least upper bound for X
theorem is_lub_x : is_lub S x :=
begin
  sorry,
end

lemma x_nonneg : 0 ≤ x :=
begin
  rcases is_lub_x with ⟨h, -⟩,
  apply h,
  split, refl,
  convert ha,
  simp [hn],
end

lemma easy (h : a < x^n) : x ≠ 0 :=
begin
  intro hx,
  rw hx at h,
  suffices : a < 0,
    linarith,
  convert h,
  symmetry,
  simp [hn],
end

/-
5) Deduce contradictions from (∗) (part 3) and (∗∗) (part 4) to show that `xⁿ = a`.
-/

-- lemma le_of_pow_le_pow (n : ℕ) (hn : 0 < n) (x y : ℝ) (h : x^n ≤ y^n) : x ≤ y :=
-- begin
--   by_contra hxy,
--   push_neg at hxy,
--   sorry,
-- --  have h2 : pow_lt_pow
-- end

theorem part5 : x^n = a :=
begin
  sorry,
end

end two

end Q4