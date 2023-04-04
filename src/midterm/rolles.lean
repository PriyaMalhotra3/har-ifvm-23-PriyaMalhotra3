import data.real.basic
import data.set.intervals.basic
import topology.continuous_on
import analysis.inner_product_space.pi_L2


/- Great work Priya!
100/100
One small comment: It is nice if you can break a long proof
into smaller pieces, since that can help Lean compile much
more quickly.  With a long proof, Lean will start over 
compiling from scratch whenever a small change is made,
which can be slow.
-/

namespace rolle

example {a b c : ℝ} (h1 : b < 0) (h : a / b ≤ 0) : a ≥ 0 * b :=
begin
  exact (div_le_iff_of_neg h1).mp h,
end

def lim (c : ℝ) (f : ℝ → ℝ) (L : ℝ) := 
  ∀ ε > 0, ∃ δ > 0, ∀ x, 0 < |x - c| ∧ |x - c| < δ → |f x - L| < ε
def derivative (c : ℝ) (f : ℝ → ℝ) (D : ℝ) := lim 0 (λ Δh, (f (c + Δh) - f c)/Δh) D
def differentiable_at (c : ℝ) (f : ℝ → ℝ) := ∃ D, derivative c f D
def differentiable_on (f : ℝ → ℝ) (s : set ℝ) := continuous_on f s ∧ ∀ c ∈ s, differentiable_at c f

variables {f : ℝ → ℝ}

theorem fermat
  {c : ℝ}
  (hextreme : ∃ δ > 0, ∀x, |x - c| < δ → (f c ≥ f x ∨ f c ≤ f x))
  : derivative c f 0 := sorry

variables {a b : ℝ}

theorem extreme_value
  (haleb : a ≤ b)
  (hcont : continuous_on f (set.Icc a b))
  : (∃ (minimum ≤ b) (_ : a ≤ minimum), ∀ x, a ≤ x ∧ x ≤ b → f minimum ≤ f x)
  ∧ (∃ (maximum ≤ b) (_ : a ≤ maximum), ∀ x, a ≤ x ∧ x ≤ b → f maximum ≥ f x) :=
begin
  let interval := set.Icc a b,
  have hfull : interval.nonempty,
  { rw set.nonempty_Icc,
    exact haleb },
  have hcompact := @compact_Icc_space.is_compact_Icc _ _ _ _ a b,
  split,
  { have := is_compact.exists_forall_le hcompact hfull hcont,
    rcases this with ⟨minimum, hminimum, this⟩,
    simp at hminimum,
    use [minimum, hminimum.right, hminimum.left],
    intros x hx,
    specialize this x,
    simp at this,
    exact this hx.left hx.right },
  { have := is_compact.exists_forall_ge hcompact hfull hcont,
    rcases this with ⟨maximum, hmaximum, this⟩,
    simp at hmaximum,
    use [maximum, hmaximum.right, hmaximum.left],
    intros x hx,
    specialize this x,
    simp at this,
    exact this hx.left hx.right }
end

theorem rolle
  (haltb : a < b)
  (hcont : continuous_on f (set.Icc a b))
  (hdiff : differentiable_on f (set.Ioo a b))
  (heq : f a = f b)
  : ∃ (c < b) (_ : a < c), derivative c f 0 :=
begin
  by_cases h : ∃ k, ∀ x, a ≤ x ∧ x ≤ b → f x = k,
  { -- constant case
    rcases (exists_between haltb) with ⟨c, ⟨hac, hcb⟩⟩,
    use [c, hcb, hac],
    cases h with k h,
    dsimp [derivative, lim],
    intros ε hε,
    let δ := min (c - a) (b - c),
    use δ,
    have hδ : δ > 0,
    { simp [δ],
      split,
      repeat { linarith } },
    use hδ,
    intros Δh hΔh,
    have : f c = k,
    { apply h,
      split,
      repeat { apply le_of_lt <|> assumption } },
    rw this,
    have : f (c + Δh) = k,
    { simp at hΔh,
      rcases hΔh with ⟨hΔh0, hΔhac, hΔhcb⟩,
      rw abs_lt at *,
      apply h,
      split,
      repeat { linarith } },
    rw this,
    simp,
    apply hε },
  { -- nonconstant case
    push_neg at h,
    obtain ⟨⟨u, ⟨hub, hua, hu⟩⟩, ⟨o, ⟨hob, hoa, ho⟩⟩⟩ := extreme_value (le_of_lt haltb) hcont,
    by_cases h₂ : f u < f a,
    { -- minimum case
      use u,
      have hultb : u < b,
      { apply lt_of_le_of_ne, { exact hub },
        by_contra hueq,
        apply not_le.mpr h₂,
        apply le_of_eq,
        rw hueq,
        exact heq },
      have haltu : a < u,
      { apply lt_of_le_of_ne, { exact hua },
        by_contra hueq,
        apply not_le.mpr h₂,
        apply le_of_eq,
        rw hueq },
      use [hultb, haltu],
      apply fermat,
      let δ := min (u - a) (b - u),
      use δ,
      have hδ : δ > 0,
      { simp [δ],
        use ⟨haltu, hultb⟩ },
      use hδ,
      intros x hx,
      apply or.inr,
      apply hu,
      rw abs_lt at hx,
      simp [δ] at hx,
      split,
      cases hx with hxl hxr,
      have : u - x < δ := by linarith,
      simp [δ] at this,
      repeat { linarith } },
    { by_cases h₃ : f o > f a,
      { -- maximum case
        use o,
        have holtb : o < b,
        { apply lt_of_le_of_ne, { exact hob },
          by_contra hoeq,
          apply not_le.mpr h₃,
          apply le_of_eq,
          rw hoeq,
          rw eq_comm,
          exact heq },
        have halto : a < o,
        { apply lt_of_le_of_ne, { exact hoa },
          by_contra hoeq,
          apply not_le.mpr h₃,
          apply le_of_eq,
          rw hoeq },
        use [holtb, halto],
        apply fermat,
        let δ := min (o - a) (b - o),
        use δ,
        have hδ : δ > 0,
        { simp [δ],
          use ⟨halto, holtb⟩ },
        use hδ,
        intros x hx,
        apply or.inl,
        apply ho,
        rw abs_lt at hx,
        simp [δ] at hx,
        split,
        cases hx with hxl hxr,
        have : o - x < δ := by linarith,
        simp [δ] at this,
        repeat { linarith } },
      { -- no other possibilities
        exfalso,
        specialize h (f a),
        push_neg at h₂,
        push_neg at h₃,
        have : f u = f a,
        { specialize hu a,
          simp at hu,
          specialize hu (le_of_lt haltb),
          apply le_antisymm,
          repeat { assumption } },
        rw this at hu,
        have : f o = f a,
        { specialize ho a,
          simp at ho,
          specialize ho (le_of_lt haltb),
          apply le_antisymm,
          repeat { assumption } },
        rw this at ho,
        rcases h with ⟨x, ⟨hx, hconst⟩⟩,
        specialize hu x hx,
        specialize ho x hx,
        apply hconst,
        apply le_antisymm,
        repeat { assumption } } } }
end

end rolle