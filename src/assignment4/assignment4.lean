import data.real.basic

/- Good work!
Correctness 90/90
Style 10/10
-/


/-
EXERCISE 1.

Prove the following without using automation, i.e. only with basic tactics
such as `intros`, `apply`, `split`, `cases`, `left`, `right`, and `use`.
-/

section

variables {α β : Type} (p q : α → Prop) (r : α → β → Prop)

-- Exercise 1a. [10pts]
example : (∀ x, p x) ∧ (∀ x, q x) → ∀ x, p x ∧ q x :=
begin
  intro h,
  intro x,
  split,
  apply h.left,
  apply h.right,
end

-- Exercise 1b. [10pts]
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
begin
  intros h x,
  cases h,
  {
    left, -- changes goal to just LHS
    apply h,
  },
  {
    right,
    apply h,
  }
end

-- Exercise 1c. [10pts]
example : (∃ x, ∀ y, r x y) → ∀ y, ∃ x, r x y :=
begin
  intros h y,
  cases h with x,
  use x,
  apply h_h,
end

end

/-
EXERCISE 2.

Suppose two pairs of real numbers {a, b} and {c, d} have the same sum
and product. The following theorem shows that either a = c and b = d,
or a = d and b = c. Fill in the details. You can use `ring`, `ring_nf`
and `linarith` freely.
-/

-- Exercise 2. [20pts]
theorem sum_product_magic (a b c d : ℝ)
    (sumeq : a + b = c + d) (prodeq : a * b = c * d) :
  (a = c ∧ b = d) ∨ (a = d ∧ b = c) :=
begin
  have : (a - c) * (a - d) = 0,
  { ring_nf,
    nth_rewrite 1 mul_comm,
    rw ← prodeq,
    rw ← neg_add',
    rw ← sumeq,
    ring_nf,
},
  have := eq_zero_or_eq_zero_of_mul_eq_zero this,
  cases this with h h,
  { left,
    split;
    linarith,},
  { right,
    split;
    linarith,}
    --Nicely done!
end

/-
EXERCISE 3.

The predicate `approaches_at f b a` should be read "f(x) approaches b as x
approaches a", and the predicate `continuous f` says that f is continuous.

Prove the following two theorems.

Note that bounded quantification such as `∀ ε > 0, ..` really means `∀ ε, ε > 0 → ..`
and `∃ δ > 0, ..` really means `∃ δ, δ > 0 ∧ ..`.
-/

def approaches_at (f : ℝ → ℝ) (b : ℝ) (a : ℝ) :=
∀ ε > 0, ∃ δ > 0, ∀ x, abs (x - a) < δ → abs (f x - b) < ε

-- Exercise 3a. [10pts]
theorem approaches_at_add_right  {f : ℝ → ℝ} {a b c: ℝ}
    (hf : approaches_at f b a) :
  approaches_at (λ x, f x + c) (b + c) a :=
begin
  intros ε he,
  unfold approaches_at at hf,
  unfold approaches_at,
  cases (hf ε he) with δ hf,
  cases hf with hd hf,
  use δ,
  split,
  exact hd,
  intros x hxaδ,
  ring_nf,
  exact (hf x hxaδ),
end

-- Exercise 3b. [10pts]
theorem approaches_at_comp {f g : ℝ → ℝ} {a b c : ℝ}
  (hf : approaches_at f b a) (hg : approaches_at g c b) :
    approaches_at (g ∘ f) c a :=
begin
  unfold approaches_at at hf hg,
  unfold approaches_at,
  intros ε he,
  cases (hg ε he) with dg hg,
  cases hg with hdg hg,
  cases (hf dg hdg) with δ hf,
  cases hf with hd hf,
  use δ,
  split,
  exact hd,
  intros x hxaδ,
  dsimp,
  exact (hg (f x) (hf x hxaδ)),
end

def continuous (f : ℝ → ℝ) := ∀ x, approaches_at f (f x) x

-- Exercise 3c. [10pts]
theorem continuous_add_right {f : ℝ → ℝ} (ctsf : continuous f) (r : ℝ) :
  continuous (λ x, f x + r) :=
begin
  unfold continuous,
  intros x,
  unfold continuous at ctsf,
  apply approaches_at_add_right,
  dsimp,
  exact ctsf x,
end

-- Since `f x - r` is the same as `f x + (- r)`, the following is an instance
-- of the previous theorem.
theorem continuous_sub {f : ℝ → ℝ} (ctsf : continuous f) (r : ℝ) :
  continuous (λ x, f x - r) :=
continuous_add_right ctsf (-r)

/-
EXERCISE 4.

In class, I will prove the intermediate value theorem in the form `ivt`.
Use that version to prove the more general one that comes after.
-/

/- We'll do this in class! You don't have to prove it,
   and you can leave the `sorry` and apply the theorem 
   as a black box. -/
theorem ivt {f : ℝ → ℝ} {a b : ℝ} (aleb : a ≤ b)
    (ctsf : continuous f) (hfa : f a < 0) (hfb : 0 < f b) :
  ∃ x, a ≤ x ∧ x ≤ b ∧ f x = 0 :=
sorry

-- Use `ivt` to prove `ivt'` below.

-- Exercise 4. [20pts]
theorem ivt' {f : ℝ → ℝ} {a b c : ℝ} (aleb : a ≤ b)
    (ctsf : continuous f) (hfa : f a < c) (hfb : c < f b) :
  ∃ x, a ≤ x ∧ x ≤ b ∧ f x = c :=
begin
  let g := λ x, f x - c,
  have : ∃ x, a ≤ x ∧ x ≤ b ∧ g x = 0,
  { dsimp [g],
    apply ivt aleb,
    apply continuous_sub ctsf,
    linarith,
    linarith,},
  dsimp [g] at this,
  cases this with x this,
  use x,
  rw sub_eq_zero at this,
  exact this,
end

