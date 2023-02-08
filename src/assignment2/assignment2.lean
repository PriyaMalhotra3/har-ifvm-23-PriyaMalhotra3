import analysis.inner_product_space.pi_L2

/- Good work Priya!
90/90 Correctness
10/10 Style
-/

/-
This assignment is due midnight on Wednesday, February 1.

Copy this file to `src/assignment2/assignment2.lean` in your personal `har-ifvm-23-{username}`
directory, and fill in the proofs. When you are done, push it to Github:
```
  git add assignment2.lean
  git commit -m "my assignment2 solutions"
  git push
```
Feel free to push any preliminary commits.
-/

/-
FIRST EXERCISE: the parallelogram law
-/

namespace parallelogram_exercise
open_locale real_inner_product_space

/-
In the following variable declaration, `euclidean_space ℝ (fin 2)` represents
the Euclidean plane, ℝ × ℝ, with the usual definition of inner product.
-/

variables x y z : euclidean_space ℝ (fin 2)

#check ⟪x, y⟫    -- the inner product
#check ‖x‖       -- the norm
#check x + y
#check 3 • x

/-
Hovering over the brackets in VS Code shows that the angle brackets for the inner product can be
written as `\<<` and `\>>`, and the bars for the norm can be written `\||`.

They satisfy the following identities:
-/

example : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x, z⟫ := inner_add_right
example : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫ := inner_add_left
example : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x, z⟫ := inner_sub_right
example : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z⟫ := inner_sub_left

example :  ⟪x, x⟫ = ‖x‖^2 := real_inner_self_eq_norm_sq x

/-
The following identity is known as the *parallelogram law*. It says that the sum of the squares
of the lengths of the four sides of a parallegram is equal to the sum of the squares of the
lengths of the diagonals.

You can read a proof of it on Wikipedia: https://en.wikipedia.org/wiki/Parallelogram_law.

Formalize it using only the four identities above as well as the `ring` tactic.
-/

example :
  ‖x + y‖^2 + ‖x - y‖^2  = 2 * (‖x‖^2 + ‖y‖^2) :=
begin
  rw ← real_inner_self_eq_norm_sq,
  rw ← real_inner_self_eq_norm_sq,
  rw inner_add_right,
  rw inner_add_left,
  rw real_inner_self_eq_norm_sq x,
  rw inner_add_left,
  rw real_inner_self_eq_norm_sq y,
  ring,
  rw inner_sub_right,
  rw inner_sub_left,
  rw inner_sub_left,
  rw real_inner_self_eq_norm_sq,
  rw real_inner_self_eq_norm_sq,
  ring,
end

/-
In fact, the theorem holds for arbitrary inner product spaces, with exactly the same proof.
You can check this by replacing the variable declaration above by the following:

variables {E : Type*} [inner_product_space ℝ E]
variables x y z : E
-/

end parallelogram_exercise

/-
SECOND EXERCISE: Boolean rings
-/

namespace boolean_ring_exercise

/-
The notion of a ring is discussed in the textbook:
https://leanprover-community.github.io/mathematics_in_lean/02_Basics.html#proving-identities-in-algebraic-structures

A *Boolean* ring satisfies the additional property that for every `x`, `x^2 = x`.
You can read about Boolean rings here:
https://en.wikipedia.org/wiki/Boolean_ring
-/

variables {R : Type*} [ring R]

-- This is the assumption that makes `R` a Boolean ring:
variable (idem : ∀ x : R, x^2 = x)

-- This adds `idem` as a hypothesis to every theorem:
include idem

/-
This exercise asks you to prove that every Boolean ring is commutative, i.e.
satisfies `x * y = y * x` for every `x` and `y`. Unfortunately, we cannot use the
`ring` tactic along the way, since it only works once we know a ring is commutative.
So you will have to rely on theorems like `mul_add`, `add_mul`, etc. in the textbook.
-/

-- This is useful:
theorem mul_idem (x : R) : x * x = x :=
by rw [←pow_two, idem]

-- Unfortunately, you have to write `mul_idem idem` to use it.
example (x y : R) : (x + y) * (x + y) = x + y :=
by rw [mul_idem idem]

/-
Prove the following theorem, following the calculation in Wikipedia:
x + x = (x+x)^2 = x^2 + x^2 + x^2 + x^2 = (x + x) + (x + x).
-/

theorem add_self (x : R) : x + x = 0 :=
begin
  have h1 : x + x = (x + x) + (x + x),
  calc
    x + x = (x + x)^2 :
      begin
        rw idem,
      end
    ... = x + x + (x + x) :
      begin
        rw pow_two,
        rw mul_add,
        rw add_mul,
        rw ← add_assoc,
        rw mul_idem idem,
        rw add_assoc,
      end,
  have h2 : (x + x) + (x + x) - (x + x) = (x + x) - (x + x),
    by rw ←h1,
  rw [add_sub_cancel, sub_self] at h2,
  exact h2
end

-- Note: again, to use this theorem you have to mention `idem` explicitly
example (y : R) : y + y = 0 :=
add_self idem y

/-
Prove `neg_eq_self` using the calculation `-x = 0 - x = x + x - x = x`. You can use the theorems
`zero_sub` and `add_sub_cancel`, as well as `add_self idem`.
-/

theorem neg_eq_self (x : R) : -x = x :=
begin
  rw ← zero_sub,
  rw ← add_self idem x,
  rw add_sub_cancel,
end

/-
This is a corollary.
-/

theorem sub_eq_add (x y : R) : x - y = x + y :=
by rw [sub_eq_add_neg, neg_eq_self idem]

/-
Prove this, using the calculation `x = x + y - y = 0 - y = -y = y`.
-/
theorem eq_of_add_eq_zero {x y : R} (h : x + y = 0) :
  x = y :=
begin
  rw ← add_zero x,
  rw ← sub_self y,
  rw ← add_sub_assoc,
  rw h,
  rw zero_sub,
  rw neg_eq_self idem,
end

/- Finally, prove `mul_comm` using the following argument from Wikipedia:

`0 + x + y = x + y = (x + y)^2 = x^2 + xy + yx + y^2 = xy + yx + x + y`

You can use the `abel` tactic to rearrange sums.
-/

example (x y : R) : x + x * y + y * x + y = x * y + y * x + x + y :=
by abel

theorem mul_comm (x y : R) : x * y = y * x :=
begin
  have h1 : 0 + (x + y) = (x * y + y * x) + (x + y),
  calc
    0 + (x + y) = (x + y)^2 :
      begin
        rw zero_add,
        rw idem,
      end
    ... = x * y + y * x + (x + y) :
      begin
        rw pow_two,
        rw mul_add,
        rw add_mul,
        rw add_mul,
        rw ← add_assoc,
        rw mul_idem idem,
        rw mul_idem idem,
        abel,
      end,
  have h2 : 0 = x * y + y * x,
    exact add_right_cancel h1,
  show x * y = y * x,
    exact eq_of_add_eq_zero idem h2.symm
end

end boolean_ring_exercise

/-
THIRD EXERCISE: absolute values
-/

namespace absolute_value_exercise

variables x y z w : ℝ

/-
Bounding sums often boils down to using transitivity and inequalities. Step through the
next example and make sure you understand what is going on. `swap` switches the order of the goals,
and `norm_num` does a numeric calculation.

The `transitivity` tactic lets you state the intermediate expression. In contrast, applying
`le_trans` lets you make Lean figure it out from context. With the `transitivity` tactic,
we have to specify that the numerals are real numbers, because otherwise Lean assumes that they
are natural numbers.
-/

example
    (hx : abs x ≤ 10)
    (hy : abs y ≤ 5)
    (hz : abs z ≤ 4) :
  abs (x + y + z) ≤ 19 :=
begin
  transitivity ((10 : ℝ) + 5 + 4),
  swap, { by norm_num },
  apply le_trans,
  apply abs_add,
  apply add_le_add,
  { -- first goal
    apply le_trans,
    apply abs_add,
    exact add_le_add hx hy },
  -- second goal
  exact hz,
end

/-
We can finish the second goal earlier by giving `hz` right away.
-/

example
    (hx : abs x ≤ 10)
    (hy : abs y ≤ 5)
    (hz : abs z ≤ 4) :
  abs (x + y + z) ≤ 19 :=
begin
  transitivity ((10 : ℝ) + 5 + 4),
  swap, { by norm_num },
  apply le_trans,
  apply abs_add,
  -- the underscore means: figure it out or leave it as another goal
  apply add_le_add _ hz,
  apply le_trans,
  apply abs_add,
  exact add_le_add hx hy,
end

/-
Prove the following. You can also use the theorems `abs_sub`, `pow_two` to expand `w^2` to `w * w`,
`sq_abs`, and `mul_le_mul`. For the last theorem, you'll need to know that an absolute value is
nonnegative, which is the theorem `abs_nonneg`. You can also use `norm_num` to show that
`(9 : ℝ) = 3 * 3`.
-/

example
    (hx : abs x ≤ 10)
    (hy : abs y ≤ 5)
    (hz : abs z ≤ 4)
    (hw : abs w ≤ 3) :
  abs (x - y + z) + w^2 ≤ 28 :=
begin
  have h1 : w^2 ≤ 9,
  begin
    rw ← sq_abs,
    rw pow_two,
    transitivity ((3 : ℝ) * 3),
    swap, { norm_num },
    apply mul_le_mul,
    exact hw,
    exact hw,
    apply abs_nonneg,
    norm_num,
  end,
  transitivity ((10 : ℝ) + 5 + 4 + 9),
  apply add_le_add,
  swap, { exact h1 },
  swap, { norm_num },
  apply le_trans,
  apply abs_add,
  apply add_le_add,
  swap, { exact hz },
  apply le_trans,
  apply abs_sub,
  apply add_le_add,
  exact hx,
  exact hy,
end

end absolute_value_exercise
