import data.set.basic
import data.polynomial.coeff
import number_theory.arithmetic_function
import ring_theory.power_series.well_known
import ring_theory.power_basis
import field_theory.finite.basic
import field_theory.finite.galois_field
import field_theory.ratfunc
import linear_algebra.finite_dimensional
import linear_algebra.finrank
import order.filter.basic

noncomputable theory

open polynomial
open power_series
open finset
open_locale polynomial

-- Part 1:

section degree

variables (R : Type) [semiring R]

-- Set of all polynomials in R[X] of degree d.
def degree_eq (d : ℕ) : set R[X] := { f | f.nat_degree = d }
-- Set of all monic polynomials in R[X] of degree d.
def monic_degree_eq (d : ℕ) := degree_eq R d ∩ { f | f.monic }
-- Set of all irreducible, monic polynomials in R[X] of degree d.
def irreducible_degree_eq (d : ℕ) := monic_degree_eq R d ∩ { f | irreducible f }

-- Bijection between monic polynomials of degree d and polynomials of degree < d: easy for a human to see by removing the leading term of a monic polynomial.
def monic_degree_lt_equiv {d : ℕ} : monic_degree_eq R d ≃ degree_lt R d := sorry

end degree

open_locale classical cardinal big_operators arithmetic_function

variables {F : Type} [field F] [fintype F]

lemma card_degree_lt (d : ℕ) : #(degree_lt F d) = #F ^ d :=
begin
  haveI : finite_dimensional F (degree_lt F d),
  { rw [degree_lt_eq_span_X_pow],
    apply finite_dimensional.span_of_finite,
    rw coe_image,
    apply set.finite.image,
    apply finite_to_set },
  rw cardinal_mk_eq_cardinal_mk_field_pow_rank F,
  congr,
  rw [degree_lt_eq_span_X_pow, rank_span_set],
  swap,
  { rw coe_image,
    -- apply linear_independent.image_subtype,
    rw linear_independent_subtype,
    -- simp only [coe_range],
    -- apply linear_independent.image,
    introv hmem hzero,
    dsimp [finsupp.supported] at hmem,
    dsimp [finsupp.total] at hzero,
    sorry },
  rw_mod_cast [cardinal.mk_coe_finset, card_image_of_injective],
  swap,
  { simp_rw X_pow_eq_monomial,
    unfold function.injective,
    introv,
    apply monomial_one_eq_iff.mp,
    apply is_field.nontrivial,
    apply field.to_is_field },
  { rw card_range }
end

-- q = p^n
variables (p : ℕ) [fact p.prime] (n : ℕ+)

-- The number of monic polynomials of degree d in 𝔽_(p^n)[X]:
def monics (d : ℕ) : ℤ := (#(monic_degree_eq (galois_field p n) d)).to_nat
-- The number of irreducible, monic polynomials of degree d in 𝔽_(p^n)[X]:
def irreducibles (d : ℕ) := (#(irreducible_degree_eq (galois_field p n) d)).to_nat

def power_series.comp_pow {R : Type} [semiring R] (x : ℕ) (f : power_series R) : power_series R :=
  mk (λ i, if x ∣ i then coeff R (i / x) f else 0)

-- A(x) = 1/(1-QC)
lemma monic_generating_function : mk (monics p n) = rescale ↑(p ^ (n : ℕ)) (inv_units_sub 1) :=
calc mk (monics p n) = mk (pow ↑(p ^ (n : ℕ))) : -- A(x) = ∑_{i=0}^∞ q^i x^i
  begin
    apply power_series.ext,
    simp only [coeff_mk],
    intro d,
    unfold monics,
    norm_cast,
    rw [cardinal.mk_congr (monic_degree_lt_equiv (galois_field p n)), card_degree_lt d],
    swap,
    { apply_instance },
    rw cardinal.mk_fintype,
    rw galois_field.card,
    swap,
    { simp only [ne.def, pnat.ne_zero, not_false_iff] },
    norm_cast,
    rw cardinal.to_nat_cast
  end
...                               = _ : -- ∑_{i=0}^∞ q^i x^i = 1/(1-qx)
  begin
    apply power_series.ext,
    simp only [coeff_mk, coeff_rescale, coeff_inv_units_sub, one_pow, one_divp, int.units_inv_eq_self, units.coe_one, mul_one, eq_self_iff_true, forall_const]
  end

-- Needed for defining an infinite product of power series (not in mathlib):
section infinite_product

section convolution

variables {i : Type} (s : finset i)

def convolution (n : ℕ) : finset (i → ℕ) :=
finset.filter (λ f, s.sum f = n) ((s.pi (λ _, range (n + 1))).map
  ⟨λ f i, if h : i ∈ s then f i h else 0,
   λ f g h, by { ext i hi, simpa [dif_pos hi] using congr_fun h i }⟩)

lemma mem_convolution (n : ℕ) (f : i → ℕ) :
  f ∈ convolution s n ↔ s.sum f = n ∧ ∀ i ∉ s, f i = 0 :=
begin
  rw [convolution, mem_filter, and_comm, and_congr_right],
  intro h,
  simp only [mem_map, exists_prop, function.embedding.coe_fn_mk, mem_pi],
  split,
  { rintro ⟨_, _, rfl⟩ _ _,
    simp [dif_neg H] },
  { intro hf,
    refine ⟨λ i hi, f i, λ i hi, _, _⟩,
    { rw [mem_range, nat.lt_succ_iff, ← h],
      apply single_le_sum _ hi,
      simp },
    { ext,
      rw [dite_eq_ite, ite_eq_left_iff, eq_comm],
      exact hf x } }
end

lemma convolution_insert (n : ℕ) (a : i) (h : a ∉ s) :
  convolution (insert a s) n =
  (nat.antidiagonal n).bUnion
    (λ (p : ℕ × ℕ), (convolution s p.snd).map
      ⟨λ f, f + λ t, if t = a then p.fst else 0, add_left_injective _⟩) :=
begin
  ext f,
  rw [mem_convolution, mem_bUnion, sum_insert h],
  split,
  { rintro ⟨rfl, h₁⟩,
    simp only [exists_prop, function.embedding.coe_fn_mk, mem_map,
               nat.mem_antidiagonal, prod.exists],
    refine ⟨f a, s.sum f, rfl, λ i, if i = a then 0 else f i, _, _⟩,
    { rw [mem_convolution],
      refine ⟨_, _⟩,
      { rw [sum_ite],
        have : (filter (λ x, x ≠ a) s) = s,
        { apply filter_true_of_mem,
          rintro i hi rfl,
          apply h hi },
        simp [this] },
      { intros i hi,
        rw ite_eq_left_iff,
        intro hne,
        apply h₁,
        simp [not_or_distrib, hne, hi] } },
    { ext,
      obtain rfl | h := eq_or_ne x a,
      { simp },
      { simp [if_neg h] } } },
  { simp only [mem_insert, function.embedding.coe_fn_mk, mem_map, nat.mem_antidiagonal, prod.exists, exists_prop, mem_convolution, not_or_distrib],
    rintro ⟨p, q, rfl, g, ⟨rfl, hg₂⟩, rfl⟩,
    refine ⟨_, _⟩,
    { simp [sum_add_distrib, if_neg h, hg₂ _ h, add_comm] },
    { rintro i ⟨h₁, h₂⟩,
      simp [if_neg h₁, hg₂ _ h₂] } }
end

lemma convolution_zero : convolution s 0 = {0} :=
begin
  rw [convolution, range_one, pi_const_singleton, map_singleton, function.embedding.coe_fn_mk, filter_singleton, if_pos, singleton_inj],
  { ext, split_ifs; refl },
  rw sum_eq_zero_iff,
  intros x hx,
  apply dif_pos hx
end

end convolution

theorem prod_coeff
  {α : Type}
  [comm_semiring α] {i : Type} (s : finset i) (f : i → power_series α) (n : ℕ) :
  coeff α n (∏j in s, f j) = ∑l in convolution s n, ∏i in s, coeff α (l i) (f i) :=
begin
  revert n,
  apply finset.induction_on s,
  { rintro ⟨_ | n⟩,
    { simp only [prod_empty, power_series.coeff_one, eq_self_iff_true, if_true, convolution_zero, sum_const, card_singleton, nat.smul_one_eq_coe, algebra_map.coe_one] },
    have : convolution (∅ : finset i) (n + 1) = ∅,
    { apply eq_empty_of_forall_not_mem,
      intros x hx,
      rw [mem_convolution, sum_empty] at hx,
      cases hx.1 },
    simp [this, if_neg (nat.succ_ne_zero _)] },
  intros a s hi ih n,
  rw [convolution_insert _ _ _ hi, prod_insert hi, power_series.coeff_mul, sum_bUnion],
  { congrm finset.sum _ (λ i, _),
    simp only [sum_map, pi.add_apply, function.embedding.coe_fn_mk, prod_insert hi, if_pos rfl, ih, mul_sum],
    apply sum_congr rfl _,
    intros x hx,
    rw mem_convolution at hx,
    rw [hx.2 a hi, zero_add],
    congrm _ * _,
    apply prod_congr rfl,
    intros k hk,
    rw [if_neg, add_zero],
    exact ne_of_mem_of_not_mem hk hi },
  { simp only [set.pairwise_disjoint, set.pairwise, prod.forall, not_and, ne.def, nat.mem_antidiagonal, disjoint_left, mem_map, exists_prop, function.embedding.coe_fn_mk, exists_imp_distrib, not_exists, finset.mem_coe, function.on_fun, mem_convolution, and_imp],
    rintro p₁ q₁ rfl p₂ q₂ h t x p hp hp2 hp3 q hq hq2 hq3,
    have z := hp3.trans hq3.symm,
    have := sum_congr (eq.refl s) (λ x _, function.funext_iff.1 z x),
    obtain rfl : q₁ = q₂,
    { simpa [sum_add_distrib, hp, hq, if_neg hi] using this },
    obtain rfl : p₂ = p₁,
    { simpa using h },
    exact (t rfl).elim }
end

end infinite_product

-- Part 2:

-- A(X) = ∏^∞_{d=0}(1/(1-x^d))^{r_d}
lemma monic_generating_function' (i : ℕ)
  : (trunc i $ mk $ monics p n)
    = trunc i (∏d in range i, power_series.comp_pow d (inv_units_sub 1) ^ (irreducibles p n d)) := 
begin
  ext j,
  simp_rw power_series.coeff_trunc,
  split_ifs,
  swap,
  { refl },
  rw prod_coeff,
  sorry
end

-- Part 3:

-- q^m = ∑_{d|m}d*r_d
lemma irreducibles_arithmetic_function : ∀ m > (0 : ℕ), (p ^ (n : ℕ)) ^ m = ∑d in m.divisors, d * irreducibles p n d :=
begin
  have := monic_generating_function' p,
  simp_rw monic_generating_function at this,
  sorry
end

-- r_d = (1/d)∑_{y|d}μ(y)q^(d/y)
theorem irreducibles_closed_form
  (d : ℕ) (h : 0 < d)
  : ↑(irreducibles p n d) = (∑x in d.divisors_antidiagonal, μ x.fst * (p ^ (n : ℕ)) ^ x.snd) / d :=
begin
  let f : ℕ → ℤ := (λ d, d * irreducibles p n d),
  let g : ℕ → ℤ := pow (p ^ (n : ℕ)),
  suffices : ∑x in d.divisors_antidiagonal, ↑(μ x.fst) * g x.snd = f d,
  { dsimp [f, g] at this,
    norm_cast at this,
    rw_mod_cast this,
    ring_nf,
    rw [nat.mul_div_assoc _ (dvd_refl d), nat.div_self h, mul_one] },
  apply nat.arithmetic_function.sum_eq_iff_sum_mul_moebius_eq.mp,
  swap,
  { exact h },
  intros d hd,
  dsimp [f, g],
  rw_mod_cast (irreducibles_arithmetic_function p n d hd)
end