import data.real.basic

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

#check mem_upper_bounds -- a ∈ upper_bounds S ↔ ∀ x, x ∈ S → x ≤ a

example (P Q : Prop) : P → Q ↔ ¬ Q → ¬ P :=
by library_search

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


example (S T : set ℝ) (a b : ℝ) :
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

# Q6

-/

-- We introduce the usual mathematical notation for absolute value
local notation `|` x `|` := abs x

theorem Q6a (x y : ℝ) : | x + y | ≤ | x | + | y | :=
begin
  -- Lean's definition of abs is abs x = max (x, -x)
  -- [or max x (-x), as the computer scientists would write it]
  unfold abs,
  -- lean's definition of max a b is "if a<=b then b else a"
  unfold max,
  -- We now have a complicated statement with three "if"s in.
  split_ifs,
  -- We now have 2^3=8 goals corresponding to all the possibilities
  -- x>=0 or x<0, y>=0 or y<0, (x+y)>=0 or (x+y)<0.
  repeat {linarith},
  -- all of them are easily solvable using the linarith tactic.
end

-- We can solve the remaining parts using part (a).
theorem Q6b (x y : ℝ) : |x + y| ≥ |x| - |y| :=
begin
  -- Apply Q6a to x+y and -y, then follow your nose.
  have h := Q6a (x + y) (-y),
  simp at h,
  linarith,
end

theorem Q6c (x y : ℝ) : |x + y| ≥ |y| - |x| :=
begin
  -- Apply Q6a to x+y and -x, then follow your nose.
  have h := Q6a (x + y) (-x),
  simp at h,
  linarith,
end

theorem Q6d (x y : ℝ) : |x - y| ≥ | |x| - |y| | :=
begin
  -- Lean prefers ≤ to ≥
  show _ ≤ _,
  -- for this one we need to apply the result that |X| ≤ B ↔ -B ≤ X and X ≤ B 
  rw abs_le,
  -- Now we have two goals:
  -- first -|x - y| ≤ |x| - |y|
  -- and second |x| - |y| ≤ |x - y|.
  -- So we need to split.
  split,
  { -- -|x - y| ≤ |x| - |y|
    have h := Q6a (x - y) (-x),
    simp [sub_eq_add_neg] at *,
    linarith },
  { -- |x| - |y| ≤ |x - y|
    have h := Q6a (x - y) y,
    simp at *,
    linarith}
end

theorem Q6e (x y : ℝ) : |x| ≤ |y| + |x - y| :=
begin
  have h := Q6a y (x - y),
  simp * at *,
end

theorem Q6f (x y : ℝ) : |x| ≥ |y| - |x - y| :=
begin
  have h := Q6a (x - y) (-x),
  simp [*, sub_eq_add_neg] at *,
end

theorem Q1g (x y z : ℝ) : |x - y| ≤ |x - z| + |y - z| :=
begin
  have h := Q6a (x - z) (z - y),
  -- Lean needs more hints with this one.
  -- First let's change that y - z into z - y,
  rw ←abs_neg (y - z),
  -- now use automation
  simp * at *,
  convert h,
  ring,
end



/-!

# Q4

Fix `a ∈ (0,∞)` and `n : ℕ`. We will prove
`∃ x : ℝ, x^n = a`. 

-/

section Q4

noncomputable theory

parameters {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 0 < n)

/-
1) Set `Sₐ := {s ∈ [0,∞) : s^n < a}` and show `Sₐ` is nonempty and
bounded above, so we may define `x := sup Sₐ`.
-/

def S := {s : ℝ | 0 ≤ s ∧ s ^ n < a}

include ha hn

theorem part1 : (∃ s : ℝ, s ∈ S) ∧ (∃ B : ℝ, ∀ s ∈ S, s ≤ B ) :=
sorry

def x := Sup S

theorem is_lub_x : is_lub S x :=
begin
  cases part1 with nonempty bdd,
  cases nonempty with x hx,
  cases bdd with y hy,
  exact real.is_lub_Sup hx hy,
end

/-
2) For `ε ∈ (0,1)` show `(x+ε)ⁿ ≤ x^n + ε[(x + 1)ⁿ − xⁿ].`
(Hint: multiply out.)
-/

lemma x_nonneg : 0 ≤ x :=
begin
  rcases is_lub_x with ⟨h, -⟩,
  apply h,
  split, refl,
  convert ha,
  simp [hn],
end

theorem part2 (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) : (x + ε)^n ≤ x^n + ε*((x+1)^n - x^n) :=
begin
  sorry
end

/-
3) Hence show that if `xⁿ < a` then
`∃ ε ∈ (0,1)` such that `(x+ε)ⁿ < a.` (*)
-/

theorem part3 (h : x ^ n < a) : ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ (x+ε)^n < a :=
begin
  sorry
end

/-
4) If `xⁿ > a`, deduce from (∗) that
`∃ ε ∈ (0,1)` such that `(1/x+ε)ⁿ < 1/a`. (∗∗)
-/

-- part 4 doesn't quite make sense because we didn't show x ≠ 0 yet

lemma easy (h : a < x^n) : x ≠ 0 :=
begin
  intro hx,
  rw hx at h,
  suffices : a < 0,
    linarith,
  convert h,
  symmetry, -- ??
  simp [hn],
end

theorem part4 (h : a < x^n) : ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ (1/x + ε)^n < 1/a :=
begin
  sorry
end

/-
5) Deduce contradictions from (∗) and (∗∗) to show that `xⁿ = a`.
-/

theorem part5 : x^n = a :=
begin
  sorry
end

end Q4