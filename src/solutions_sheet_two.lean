import data.real.basic
import data.nat.choose.sum -- binomial theorem
import data.real.ereal
import data.pnat.basic

-- namespace problem_sheet_two
section Q2

/-!

# Q2

-/

/-
2.  Fix nonempty sets S_n ⊆ R, n= 1,2,3,....  
Prove that sup{sup S1,sup S2,sup S3,...} = sup(⋃_{n=1}^{infty} S_n),
in the sense that if either exists then so does the other, and they are equal.
-/

/-
Let's first answer a better question with fewer restrictions,
using extended reals.
Then Sup {Sup (S_i) : i ∈ I} = Sup (⋃_{i ∈ I} S_i) is *always* true
-/

example (I : Type) (S : I → set (ereal)) :
  Sup (set.range (λ i, Sup (S i))) = Sup (⋃ i, S i) :=
begin
  apply le_antisymm,
  { rw Sup_le_iff,
    rintro - ⟨i, rfl⟩,
    dsimp only,
    refine Sup_le_Sup _,
    exact set.subset_Union S i },
  { rw Sup_le_iff,
    rintros x ⟨-, ⟨i, rfl⟩, (hix : x ∈ S i)⟩,
    apply le_trans (le_Sup hix),
    apply le_Sup _,
    use i }
end

lemma exists_lub (S : set ℝ) :
  S.nonempty ∧ (upper_bounds S).nonempty → (∃ B, is_lub S B) :=
begin
  rintros ⟨h1, h2⟩,
  cases real.exists_sup S h1 h2 with B hB,
  use B,
  split,
  { apply (hB B).1,
    refl },
  { intros x hx,
    rw hB,
    exact hx }
end

-- "All the S_i have a sup and the set {sup S1, sup S2, ...} has a sup, if and 
-- only if the union of the S_i has a sup"
theorem Q2a (S : ℕ+ → set ℝ)
  (hS : ∀ i : ℕ+, (S i).nonempty) :
  (∀ n : ℕ+, ∃ B, is_lub (S n) B) ∧ (∃ B, is_lub (set.range (λ i, Sup (S i))) B) ↔ 
  ∃ B, is_lub (⋃ i, S i) B :=
begin
  split,
  { rintro ⟨h1, B, hB1, hB2⟩,
    apply exists_lub,
    cases hS 37 with x hx,
    use [x, S 37, 37, hx],
    use B,
    rintros y ⟨-, ⟨i, rfl⟩, (hiY : y ∈ S i)⟩,
    specialize hB1 ⟨i, rfl⟩,
    refine le_trans _ hB1,
    apply real.le_Sup _ _ hiY,
    rcases h1 i with ⟨C, hC1, hC2⟩,
    use C,
    exact hC1 },
  { rintro ⟨B, hB1, hB2⟩,
    split,
    { intro n,
      apply exists_lub,
      use hS n,
      use B,
      apply upper_bounds_mono_set _ hB1,
      exact set.subset_Union S n },
    { apply exists_lub,
      split,
      { apply set.range_nonempty },
      { use B,
        rintro - ⟨i, rfl⟩,
        dsimp only,
        rw real.Sup_le _ (hS i),
        { intros z hz,
          apply hB1,
          use [S i, i, hz] },
        { use B,
          intros z hz,
          apply hB1,
          use [S i, i, hz] } } } }
end

-- assuming both sides make sense, prove the sups are equal
theorem Q2b (S : ℕ+ → set ℝ)
  (hS : ∀ i : ℕ+, (S i).nonempty)
  (hLHS: ∀ n : ℕ+, ∃ B, is_lub (S n) B) (hLHS' : ∃ B, is_lub (set.range (λ i, Sup (S i))) B)
  (hRHS : ∃ B, is_lub (⋃ i, S i) B) :
  Sup (set.range (λ i, Sup (S i))) = Sup (⋃ i, S i) :=
begin
  -- suffices to prove LHS ≤ RHS and RHS ≤ LHS
  apply le_antisymm,
  { -- to prove Sup ≤ something, suffices to prove all elements are ≤ it
    rw real.Sup_le,
    rintro - ⟨j, rfl⟩,
    dsimp only,
    -- so it suffices to prove Sup (S j) ≤ Sup (⋃_i S i)
    rw real.Sup_le,
    -- so it even suffices to prove every element of S j is ≤ the Sup
    intros x hx,
    -- but this is clear because the elements are in the set
    apply real.le_Sup, swap,
    use [S j, j, hx],
    -- now just check that all sets were nonempty and had least upper bounds,
    -- this follows from our assumptions.
    { rcases hRHS with ⟨B, hB1, hB2⟩,
      use B,
      exact hB1 },
    { exact hS j},
    { rcases hLHS j with ⟨B, hB1, hB2⟩,
      use B,
      exact hB1 },
    { apply set.range_nonempty },
    { rcases hLHS' with ⟨B, hB1, hB2⟩,
      use B,
      exact hB1 } },
  { -- to prove Sup ≤ somthing, suffices to prove all elements are ≤ it
    rw real.Sup_le,
    -- so assume z is in one of the S i's, call it S j
    rintro z ⟨-, ⟨j, rfl⟩, (hzj : z ∈ S j)⟩,
    -- then z ≤ Sup (S j)
    apply le_trans (real.le_Sup _ _ hzj),
    -- so it's certainly ≤ Sup of a set containing Sup (S j)
    apply real.le_Sup,
    -- now tidy up
    { rcases hLHS' with ⟨B, hB1, hB2⟩,
      use B,
      exact hB1 },
    { use j },
    { rcases hLHS j with ⟨B, hB1, hB2⟩,
      use B,
      exact hB1 },
    { cases hS 37 with x hx,
      use [x, S 37, 37, hx],
    }, 
    { rcases hRHS with ⟨B, hB1, hB2⟩,
      use B,
      exact hB1 } }
end

end Q2

/-!

# Q3 

Take bounded, nonempty `S, T ⊆ ℝ`.
Define `S + T := { s + t : s ∈ S, t ∈ T}`.
Prove `sup(S+T)  =  sup(S)+ sup(T)`

-/

theorem is_lub_def {S : set ℝ} {a : ℝ} :
  is_lub S a ↔ a ∈ upper_bounds S ∧ ∀ x, x ∈ upper_bounds S → a ≤ x :=
begin
  refl
end

-- #check mem_upper_bounds -- a ∈ upper_bounds S ↔ ∀ x, x ∈ S → x ≤ a

--example (P Q : Prop) : P → Q ↔ ¬ Q → ¬ P :=
--by library_search

theorem useful_lemma {S : set ℝ} {a : ℝ} (haS : is_lub S a) (t : ℝ)
  (ht : t < a) : ∃ s, s ∈ S ∧ t < s :=
begin
  rw is_lub_def at haS,
  cases haS with haS1 haS2,
  specialize haS2 t,
  replace haS2 := mt haS2,
  push_neg at haS2,
  specialize haS2 ht,
  rw mem_upper_bounds at haS2, 
  push_neg at haS2,
  exact haS2,
end


theorem problem_sheet_two.Q3 (S T : set ℝ) (a b : ℝ) :
  is_lub S a → is_lub T b → is_lub (S + T) (a + b) :=
begin
  intros hSa hTb,
  rw is_lub_def,
  split,
  { rw mem_upper_bounds,
    intro x,
    intro hx,
    rcases hx with ⟨s, t, hsS, htT, rfl⟩,
    rw is_lub_def at hSa hTb,
    rcases hSa with ⟨ha1, ha2⟩,
    rcases hTb with ⟨hb1, hb2⟩,
    rw mem_upper_bounds at ha1 hb1,
    specialize ha1 s hsS,
    specialize hb1 t htT,
    linarith,
  },
  { intro x,
    intro hx,
    rw mem_upper_bounds at hx,
    by_contra,
    push_neg at h,
    set ε := a + b - x with hε,
    have hε2 : 0 < ε,
      linarith,
    set a' := a - ε/2 with ha',
    set b' := b - ε/2 with hb',
    rcases useful_lemma hSa a' (by linarith) with ⟨s', hs', hs'2⟩,
    rcases useful_lemma hTb b' (by linarith) with ⟨t', ht', ht'2⟩,
    specialize hx (s' + t') ⟨s', t', hs', ht', rfl⟩,
    linarith,
  }
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

/- Note: We do things in a slightly different order to the question
on the sheet, because the way it's set up on the sheet, `x` is
defined to be `Sup(S_a)` very early on, which technically forces
us to prove that `1/x` is `Sup(S_{1/a})` -- this is unnecessary
with the approach below. I broke this question into five "parts".
-/

/-
2) For `ε ∈ (0,1)` and arbitrary `x ≥ 0` show `(x+ε)ⁿ ≤ x^n + ε[(x + 1)ⁿ − xⁿ].`
(Hint: multiply out.)
-/

theorem part2 {x : ℝ} (x_nonneg : 0 ≤ x) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
  (x + ε)^n ≤ x^n + ε * ((x + 1)^n - x^n) :=
begin
  rw [ add_pow, add_pow ],
  simp_rw [one_pow, mul_one],
  rw [finset.sum_range_succ, nat.sub_self, pow_zero, mul_one],
  rw [nat.choose_self, nat.cast_one, mul_one],
  apply add_le_add_left,
  rw [finset.sum_range_succ, nat.choose_self, nat.cast_one, mul_one],
  rw [add_sub_cancel', finset.mul_sum],
  apply finset.sum_le_sum,
  intros i hi,
  rw [finset.mem_range, nat.lt_iff_add_one_le, le_iff_exists_add] at hi,
  -- rcases hi with ⟨c, rfl⟩, -- rcases bug?
  cases hi with c hc,
  have hni : n - i = c + 1,
    omega,
  rw [hni, mul_comm (x ^ i), mul_assoc, pow_succ, mul_comm ε, mul_assoc],
  apply mul_le_of_le_one_left,
  { apply mul_nonneg (le_of_lt hε0),
    apply mul_nonneg (pow_nonneg x_nonneg i),
    norm_cast, simp },
  { apply pow_le_one; linarith }
end

/-
3) Hence show that if `x ≥ 0` and `xⁿ < a` then
`∃ ε ∈ (0,1)` such that `(x+ε)ⁿ < a.` (*)
-/

theorem part3 {x : ℝ} (x_nonneg : 0 ≤ x) (h : x ^ n < a) :
  ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ (x+ε)^n < a :=
begin
  set ε := min (1 / 2) ((a - x ^ n) / ((x + 1) ^ n - x ^ n) / 2) with hε,
  use ε,
  have hx1 : 0 < (x + 1) ^ n - x ^ n,
    rw sub_pos,
    apply pow_lt_pow_of_lt_left (lt_add_one _) x_nonneg hn, 
  have hε0 : 0 < ε,
    rw [hε, lt_min_iff],
    split, { linarith },
    refine div_pos _ (by linarith),
    refine div_pos (by linarith) hx1,
  use hε0,
  have hε1 : ε < 1,
    suffices : ε ≤ 1/2, linarith,
    rw hε,
    exact min_le_left _ _,
  use hε1,
  apply lt_of_le_of_lt (part2 ha hn x_nonneg ε hε0 hε1),
  rw ← lt_sub_iff_add_lt',
  rw ← lt_div_iff hx1,
  apply lt_of_le_of_lt (min_le_right _ _),
  apply div_two_lt_of_pos,
  exact div_pos (by linarith) hx1,
end

/-
4) If `x > 0` is arbitrary and `xⁿ > a`, deduce from (∗) (i.e. part 3) that
`∃ ε ∈ (0,1)` such that `(1/x+ε)ⁿ < 1/a`. (∗∗)

Note that here it makes life much easier to have x a variable and not
the fixed Sup(S_a); with the approach on the sheet one would have to
technical prove that 1/x is Sup(S_{1/a}), which is not necessary
with this approach.
-/

theorem part4 {x : ℝ} (hx : 0 < x) (h : a < x^n) :
  ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ (1/x + ε)^n < 1/a :=
begin
  have h1x_pos : 0 < 1/x,
    rwa one_div_pos,
  have h1xa : (1/x)^n < 1/a,
    rw [div_pow, one_pow],
    apply div_lt_div_of_lt_left ha h zero_lt_one,
  exact part3 (one_div_pos.2 ha) hn (le_of_lt h1x_pos) h1xa,
end

end one

section two

-- in this section, a and n are going to be fixed parameters

parameters {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 0 < n)

include ha hn
/-
1) Set `Sₐ := {s ∈ [0,∞) : s^n < a}` and show `Sₐ` is nonempty and
bounded above, so we may define `x := sup Sₐ` 
-/

def S := {s : ℝ | 0 ≤ s ∧ s ^ n < a}

theorem part1 : (∃ s : ℝ, s ∈ S) ∧ (∃ B : ℝ, ∀ s ∈ S, s ≤ B ) :=
begin
  split,
  { use 0,
    split, { refl },
    convert ha,
    simp [hn] },
  { use a + 1,
    rintro s ⟨hs1, hs2⟩,
    by_contra hsa,
    push_neg at hsa,
    have hs3 : 1 ≤ s,
      linarith,
    have hs4 : s ≤ s ^ n,
      cases n, cases hn,
      suffices : 1 ≤ s ^ n,
        convert mul_le_mul (le_refl s) this (by linarith) hs1,
        { simp },
      exact one_le_pow_of_one_le hs3 _,
    linarith, }
end


def x := Sup S

theorem is_lub_x : is_lub S x :=
begin
  cases part1 with nonempty bdd,
  cases nonempty with x hx,
  cases bdd with y hy,
  exact real.is_lub_Sup hx hy,
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
  symmetry, -- todo add simp lemma to mathlib
  simp [hn],
end

/-
5) Deduce contradictions from (∗) and (∗∗) to show that `xⁿ = a`.
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
  rcases lt_trichotomy (x^n) a with (hlt | heq | hgt),
  { exfalso,
    obtain ⟨ε, hε0, -, hε⟩ := part3 ha hn (x_nonneg) hlt,
    have ZZZ := is_lub_x.1 ⟨_, hε⟩, linarith,
    linarith [x_nonneg] },
  { assumption },
  { exfalso,
    have hxpow : 0 < x,
      rw lt_iff_le_and_ne,
      exact ⟨x_nonneg, (easy hgt).symm⟩,
    obtain ⟨ε, hε0, -, hε⟩ := part4 ha hn hxpow hgt,
    have huseful : 0 < 1 / x + ε,
      refine add_pos _ hε0,
      exact one_div_pos.mpr hxpow,   
    have ha' : a < (1 / (1 / x + ε)) ^ n,
    { rw [div_pow, one_pow],
      rwa lt_one_div _ ha at hε,
      apply pow_pos,
      assumption },
    have hproblem : (1 / (1 / x + ε)) ∈ upper_bounds S,
    { rintro t ⟨ht0, hta⟩,
      apply le_of_lt,
      apply lt_of_pow_lt_pow n,
      { apply le_of_lt,
        rwa one_div_pos },
      { linarith } },
    have ZZZ := is_lub_x.2 hproblem,
      rw le_one_div at ZZZ,
      { linarith },
      { assumption },
      { assumption } }
end

end two

end Q4

section Q6

/-!

# Q6

"Do (a) from first principles and then do parts (b)-(g) from (a)"

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
  unfold abs max,
  split_ifs;
  linarith
end

-- all the rest you're supposed to do using Q6a somehow:
-- `simp` and `linarith` are useful.

theorem Q6b (x y : ℝ) : |x + y| ≥ |x| - |y| :=
begin
  have h := Q6a (x + y) (-y),
  simp at h,
  linarith,
end

theorem Q6c (x y : ℝ) : |x + y| ≥ |y| - |x| :=
begin
  have h := Q6a (x + y) (-x),
  simp at h,
  linarith,
end

theorem Q6d (x y : ℝ) : |x - y| ≥ | |x| - |y| | :=
begin
  show _ ≤ _,
  rw abs_le,
  split,
  { -- |y|<=|x|+|y-x|
    have h := Q6a x (y-x),
    simp at h,
    rw abs_sub,
    linarith },
  { have h := Q6a (x-y) y,
    simp at h,
    linarith }
end

theorem Q6e (x y : ℝ) : |x| ≤ |y| + |x - y| :=
begin
  have h := Q6a y (x-y),
  convert h,
  ring,
end

theorem Q6f (x y : ℝ) : |x| ≥ |y| - |x - y| :=
begin
  have h := Q6a x (y-x),
  simp at h,
  rw abs_sub at h,
  linarith,
end

theorem Q6g (x y z : ℝ) : |x - y| ≤ |x - z| + |y - z| :=
begin
  have h := Q6a (x-z) (z-y),
  rw abs_sub z y at h,
  convert h,
  ring,
end

end Q6