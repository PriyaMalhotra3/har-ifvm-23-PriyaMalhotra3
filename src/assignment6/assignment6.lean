import data.set.lattice

/- Good work!
90/90 Correctness
10/10 Style
-/


/- This assignment is due by 11:59pm on Friday, March 3, 2023 . -/

/-
EXERCISE 1.

A function `F : set α → set α` is called a *monotone operator* if for every
pair of sets `s ⊆ t`, we have `F s ⊆ F t`.

Every such operator has a *least fixed point*, i.e. a set `s` satisfying:
- `F s = s`
- For every `t`, if `F t = t`, then `s ⊆ t`.

This exercise has you prove that fact. In fact, the least fixed point is
the intersection of all sets `s` such that `F s ⊆ s`.

This theorem, or the generalization to monotone operators on a complete lattice,
is called *Tarski's theorem* or the *Knaster-Tarski Theorem*. Feel free to use
Google to find more information.
-/
namespace monotone_set_operator
open set

-- You will need these. The full names are `set.mem_sInter`, etc.
#check @mem_sInter
#check @subset_sInter
#check @subset_sInter_iff

variable {α : Type*}

def lfp (F : set α → set α) := ⋂₀ { t | F t ⊆ t }

variable {F : set α → set α}
-- The monotonicity assumption:
variable (monoF : ∀ ⦃s t⦄, s ⊆ t → F s ⊆ F t)

/-
This follows immediately from the definition of `lfp F`.
-/
-- Exercise 1a. [8pts]
lemma aux0 {s : set α} (h : F s ⊆ s) : lfp F ⊆ s :=
begin
  apply sInter_subset_of_mem,
  exact h
end

/-
All the remaining theorems in this section need the monotonicity assumption.
After you prove `aux1`, you have to write `aux1 monoF` to use it in a
later theorem.
-/
include monoF

/-
To show this next statement, it suffices to show that `F (lfp F)` is contained
in every set `t` such that `F t ⊆ t`. So suppose `t` has this property.
Then by `aux0`, `lfp F ⊆ t`, and by monotonicity, we have `F (lfp F) ⊆ F t ⊆ t`.
-/
-- Exercise 1b. [10pts]
lemma aux1 : F (lfp F) ⊆ lfp F :=
begin
  apply subset_sInter,
  intros t ht,
  apply subset_trans _ ht,
  apply monoF,
  exact aux0 ht,
end

-- Hint: The remaining exercise 1 proofs below can be done in at most three
-- lines each.

/- To show this, use `aux0`. -/
-- Exercise 1c. [5pts]
lemma aux2 : lfp F ⊆ F (lfp F) :=
begin
  apply aux0,
  apply monoF,
  exact aux1 monoF,
end

/- Follows from `aux1` and `aux2`. -/
-- Exercise 1d. [5pts]
theorem lfp_fixed_point : F (lfp F) = lfp F :=
begin
  apply subset_antisymm,
  { -- F (lfp F) ⊆ lfp F
    exact aux1 monoF },
  { -- lfp F ⊆ F (lfp F)
    exact aux2 monoF },
end

-- Exercise 1e. [5pts]
theorem lfp_least_fixed_point (s : set α) (h : F s = s) : lfp F ⊆ s :=
begin
  apply aux0,
  exact eq.subset h
end

end monotone_set_operator

/-
EXERCISE 2.

A `complete lattice` is a partial order such that every subset has a greatest
lower bound (`Inf`) and a least upper bound (`Sup`). In fact, the existence
of either implies the other.

The proofs above carry over to this more general setting, if you replace
`α` by `set α`, `⊆` by `≤`, `⋂₀` by `Inf`, and make some small adjustments
to the proof.

Really, start by cutting and pasting the proofs above.
-/

namespace monotone_operator

#check @le_Inf
#check @le_Inf_iff
#check @Inf_le

variables {α : Type*} [complete_lattice α]

def lfp (F : α → α) := Inf { s | F s ≤ s }

variables {F : α → α} (monoF : ∀ ⦃s t⦄, s ≤ t → F s ≤ F t)

-- Exercise 2a. [5pts]
lemma aux0 {s : α} (h : F s ≤ s) : lfp F ≤ s :=
begin
  apply Inf_le,
  exact h
end

include monoF

-- Exercise 2b. [5pts]
lemma aux1 : F (lfp F) ≤ lfp F :=
begin
  apply le_Inf,
  intros t ht,
  apply le_trans,
  { -- F (lfp F) ≤ F t
    apply monoF,
    apply aux0 ht },
  { -- F t ≤ t
    exact ht },
end

-- Exercise 2c. [3pts]
lemma aux2 : lfp F ≤ F (lfp F) :=
begin
  apply aux0,
  apply monoF,
  exact aux1 monoF,
end

-- Exercise 2d. [2pts]
theorem lfp_fixed_point : F (lfp F) = lfp F :=
begin
  apply le_antisymm,
  { -- F (lfp F) ≤ lfp F
    exact aux1 monoF },
  { -- lfp F ≤ F (lfp F)
    exact aux2 monoF },
end

-- Exercise 2e. [2pts]
theorem lfp_least_fixed_point (s : α) (h : F s = s) : lfp F ≤ s :=
begin
  apply aux0,
  exact eq.le h
end

end monotone_operator

/-
EXERCISE 3.

Suppose `A 0, A 1, A 2, ...` is a sequence of sets. For each `n`, suppose
`B n = ⋃ i < n, A i`. Then the sequence `B 0, B 1, B 2, ...` is a monotone
sequence with the same union.
-/

namespace set_sequences

variable  {α : Type*}
variables (A B : ℕ → set α)
variable (B_def : ∀ n, B n = ⋃ i < n, A i)

/-
Remember, a (bounded) union corresponds to a (bounded) existential quantifier.
Use the simplifier with `simp only [set.mem_Union]` to do the translation for
you. You can also write `simp only [set.mem_Union] at h` to simplify a
hypothesis. You can also just use `simp`. However, mathlib conventions
discourage "non-terminal" calls, i.e. ones which don't close a goal, to `simp`
without `only`.
-/
example (x : α) (n : ℕ) : (x ∈ ⋃ i < n, A i) ↔ ∃ i < n, x ∈ A i :=
  by simp only [set.mem_Union]

-- This might be helpful to you:
example (i : ℕ) : i < i + 1 := nat.lt_succ_self _

include B_def

-- Exercise 3a. [10pts]
theorem monotone_B : ∀ i j, i ≤ j → B i ⊆ B j :=
begin
  intros,
  rw B_def i,
  rw B_def j,
  apply set.Union_mono,
  intro k,
  apply set.Union_subset_Union_const,
  intros,
  apply lt_of_lt_of_le,
  repeat { assumption },
end

-- Exercise 3b. [15pts]
theorem Union_B_eq_Union_A : (⋃ i, B i) = (⋃ i, A i) :=
begin
  apply subset_antisymm,
  { -- (⋃ i, B i) ⊆ (⋃ i, A i)
    intro x,
    rw [set.mem_Union, exists_imp_distrib],
    intros _ hx,
    rw [B_def, set.mem_Union] at hx,
    cases hx with _ hx,
    rw set.mem_Union at hx,
    cases hx with _ hx,
    apply set.mem_Union_of_mem,
    exact hx, },
  { -- (⋃ i, A i) ⊆ (⋃ i, B i)
    apply set.Union_mono',
    intros i,
    use i + 1,
    rw B_def,
    repeat { apply set.subset_Union_of_subset },
    apply nat.lt_succ_self,
    refl },
end

end set_sequences

/-
EXERCISE 4.

Suppose `A 0, A 1, A 2, ...` is a sequence of sets. For each `n`, suppose
`C n = A n \ (⋃ i < n, A i)`. Then whenever `i ≠ j`, the sets `C i` and `C j` are
disjoint, but the sequence still has the same union.
-/

namespace set_sequences

variable  {α : Type*}
variables (A C : ℕ → set α)
variable (C_def : ∀ n, C n = A n \ (⋃ i < n, A i))

-- This may be useful.
-- #check @set.eq_empty_of_forall_not_mem

/-
Use the lemma `aux` below to show that if `x` is in some `A i`, then there
is a least `i` with that property.
-/
section
open_locale classical

lemma aux {A : ℕ → set α} {x : α} (h : ∃ i, x ∈ A i) :
  ∃ i, x ∈ A i ∧ ∀ j < i, x ∉ A j :=
subtype.exists_of_subtype (nat.find_x h)
end

include C_def

-- Exercise 4a. [10pts]
theorem disjoint_C_of_lt : ∀ i j, i < j → C i ∩ C j = ∅ :=
begin
  intros,
  rw [C_def, C_def, set.eq_empty_iff_forall_not_mem],
  by_contra hx,
  push_neg at hx,
  rcases hx with ⟨x, ⟨⟨xinCi, _⟩, ⟨_, xinCj⟩⟩⟩,
  apply xinCj,
  repeat { apply set.mem_Union_of_mem <|> assumption },
end

-- Exercise 4b. [15pts]
theorem Union_C_eq_Union_A : (⋃ i, C i) = (⋃ i, A i) :=
begin
  apply subset_antisymm,
  { -- (⋃ i, C i) ⊆ (⋃ i, A i)
    apply set.Union_mono,
    intro i,
    rw C_def,
    apply set.diff_subset },
  { -- (⋃ i, A i) ⊆ (⋃ i, C i)
    intro x,
    rw set.mem_Union,
    intro xinUnionA,
    rw set.mem_Union,
    obtain ⟨i, ⟨xinAi, hj⟩⟩ := aux xinUnionA,
    use i,
    rw C_def,
    split, { by exact xinAi },
    by_contra h,
    rw set.mem_Union at h,
    cases h with j h,
    rw set.mem_Union at h,
    cases h,
    apply hj,
    repeat { assumption } },
end

end set_sequences