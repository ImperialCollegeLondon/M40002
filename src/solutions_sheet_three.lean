import data.real.basic
import data.pnat.basic
import solutions_sheet_two

local notation `|` x `|` := abs x

def is_limit (a : ℕ+ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, | a n - l | < ε

def is_convergent (a : ℕ+ → ℝ) : Prop :=
∃ l : ℝ, is_limit a l

def is_not_convergent (a : ℕ+ → ℝ) : Prop := ¬ is_convergent a

/-!

# Q1

-/

/-

Which of the following sequences are convergent and which are not?
What's the limit of the convergent ones?

-/

theorem Q1a : is_limit (λ n, (n+7)/n) 1 :=
begin
  intros ε hε,
  use (ceil ((37 : ℝ) / ε)).nat_abs,
  { apply int.nat_abs_pos_of_ne_zero,
    apply norm_num.ne_zero_of_pos,
    rw ceil_pos,
    refine div_pos _ hε,
    norm_num },
  rintros ⟨n, hn0⟩ hn,
  simp only [pnat.mk_coe, coe_coe],
  rw add_div,
  rw div_self (show (n : ℝ) ≠ 0, by norm_cast; linarith),
  simp only [add_sub_cancel'],
  rw abs_lt,
  split,
  { refine lt_trans (show -ε < 0, by linarith) _,
    refine div_pos (by norm_num) _,
    assumption_mod_cast },
  { rw div_lt_iff, swap, assumption_mod_cast,
    simp at hn,

    replace hn := le_trans int.le_nat_abs (int.coe_nat_le.mpr hn),
    rw ceil_le at hn,
    norm_cast at hn,
    rw div_le_iff hε at hn,
    linarith }
end

theorem Q1b : is_limit (λ n, n/(n+7)) 1 :=
begin
  sorry
end

theorem Q1c : is_limit (λ n, (n^2+5*n+6)/(n^3-2)) 0 :=
begin
  sorry
end

theorem Q1d : is_not_convergent (λ n, (n^3-2)/(n^2+5*n+6)) :=
begin
  sorry
end

def is_cauchy (a : ℕ+ → ℝ) : Prop :=
∀ ε > 0, ∃ N : ℕ+, ∀ m n ≥ N, |a m - a n| < ε

theorem is_cauchy_of_is_convergent {a : ℕ+ → ℝ} : is_convergent a → is_cauchy a :=
begin
  rintro ⟨l, hl⟩,
  intros ε hε,
  specialize hl (ε/2) (by linarith),
  rcases hl with ⟨B, hB1⟩,
  use B,
  intros m n hmB hnB,
  have hm := hB1 m hmB, 
  have hn := hB1 n hnB,
  have h := abs_add (a m - l) (l - a n),
  have h2 : a m - l + (l - a n) = a m - a n := by ring,
  rw h2 at h,
  rw abs_sub l at h,
  linarith,
end


theorem Q1e : is_not_convergent (λ n, (1 - n*(-1)^n.1)/n) :=
begin
  intro h,
  replace h := is_cauchy_of_is_convergent h,
  -- 1/n + (-1)^{n+1}
  specialize h 0.1 (by linarith),
  cases h with N hN,
  have htemp : N ≤ N + 1,
    cases N with N hN,
    change N ≤ _,
    simp,
  specialize hN N (N + 1) (le_refl N) htemp,
  rw abs_lt at hN,
  dsimp only at hN,
  cases hN with hN1 hN2,
  cases N with N hN,
  simp at *,
  sorry
end

/-!

# Q3

-/

/-

Let a_n be a sequence converging to a ∈ ℝ. Suppose b_n is another
sequence which is different than a_n but only differs from a_n
in finitely many terms, that is the set {n : ℕ | a_n ≠ b_n} is
non-empty and finite. Prove b_n converges to a
-/

theorem Q3 (a : ℕ+ → ℝ) (b : ℕ+ → ℝ) (h_never_used : {n : ℕ+ | a n ≠ b n}.nonempty)
  (h : {n : ℕ+ | a n ≠ b n}.finite) (l : ℝ) (ha : is_limit a l) : is_limit b l :=
begin
  intros ε hε,
  cases ha ε hε with B hB,
  let S : finset ℕ+ := h.to_finset,
  have hS : S.nonempty,
    simp only [h_never_used, set.finite.to_finset.nonempty],
  let m := finset.max' S hS,
  use max B (m + 1),
  intros n hn,
  convert hB n _,
  { suffices : n ∉ {n | a n ≠ b n},
      symmetry,
      by_contra htemp,
      apply this,
      exact htemp,
    intro htemp,
    have hS : n ∈ S,
      simp [htemp],
      exact htemp,
    have ZZZ : n ≤ m := finset.le_max' S n hS,
    change max _ _ ≤ n at hn,
    rw max_le_iff at hn,
    cases hn,
    have YYY := le_trans hn_right ZZZ,
    change m.1 + 1 ≤ m.1 at YYY,
    linarith },
  change _ ≤ _ at hn,
  rw max_le_iff at hn,
  exact hn.1,
end

/-!

# Q4

-/

/-

Let S ⊆ ℝ be a nonempty bounded above set. show that there exists
a sequence of numbers s_n ∈ S, n = 1, 2, 3,… such that sₙ → Sup S


-/

--theorem useful_lemma {S : set ℝ} {a : ℝ} (haS : is_lub S a) (t : ℝ)
--  (ht : t < a) : ∃ s, s ∈ S ∧ t < s :=

theorem useful_lemma2 (S : set ℝ) (hS1 : S.nonempty) (hS2 : bdd_above S) :
  is_lub S (Sup S) :=
begin
  cases hS1 with a ha,
  cases hS2 with b hb,
  apply real.is_lub_Sup ha hb,
end

theorem pnat_aux_lemma {ε : ℝ} (hε : 0 < ε) {a : ℝ} (ha : 0 < a) : 0 < ⌈a / ε⌉.nat_abs :=
begin
  apply int.nat_abs_pos_of_ne_zero,
  apply norm_num.ne_zero_of_pos,
  rw ceil_pos,
  refine div_pos _ hε,
  exact ha,
end


theorem Q4 (S : set ℝ) (hS1 : S.nonempty) (hS2 : bdd_above S) :
  ∃ s : ℕ+ → ℝ, (∀ n, s n ∈ S) ∧ is_limit s (Sup S) :=
begin
  have h := useful_lemma (useful_lemma2 S hS1 hS2),
--  by_contra h2,
--  unfold is_limit at h2,
--  push_neg at h2,
  let s : ℕ+ → ℝ :=
  λ n, classical.some (h (Sup S - 1/n) (show Sup S - 1/n < Sup S, from _)),
  have hs : ∀ n : ℕ+, _ :=
  λ n, classical.some_spec (h (Sup S - 1/n) (show Sup S - 1/n < Sup S, from _)),
  use s,
  swap,
  { cases n with n hn,
    rw sub_lt_self_iff,
    rw one_div_pos,
    simp [hn] },
  have hs2 : ∀ (n : ℕ+), s n ∈ S,
  { intro n,
    dsimp at hs,
    exact (hs n).1 },
  use hs2,
  intros ε hε,
  use (ceil (2/ε)).nat_abs,
    exact pnat_aux_lemma hε (show (0 : ℝ) < 2, by norm_num),
  intros n hn,
  have hn2 : Sup S - 1/n < s n,
    exact (hs n).2,
  rw sub_lt at hn2,
  have hS3 := useful_lemma2 S hS1 hS2,
  rw abs_lt,
  split,
  { suffices : (1 : ℝ) / n < ε,
      linarith,
    cases n with n hn3, -- 
    show (1 : ℝ) / n < _,
    rw div_lt_iff (show 0 < (n : ℝ), by assumption_mod_cast),
    simp at hn,
    replace hn := le_trans (int.le_nat_abs) (int.coe_nat_le.mpr hn),
    rw ceil_le at hn,
    norm_cast at hn,
    rw div_le_iff at hn;
    linarith },
  { refine lt_of_le_of_lt _ hε,
    specialize hs2 n,
    rw sub_nonpos,
    cases hS3 with hS4 hS5,
    apply hS4 hs2 },
end