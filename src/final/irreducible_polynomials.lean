import data.set.basic
import data.polynomial.coeff
import number_theory.arithmetic_function
import ring_theory.power_series.well_known
import ring_theory.power_basis
import field_theory.finite.basic
import field_theory.ratfunc
import linear_algebra.finite_dimensional

open_locale polynomial cardinal big_operators arithmetic_function

variables (R : Type) [comm_ring R] {d : ℕ}

lemma card_degree_lt (F : Type) [field F] (d : ℕ) : #(polynomial.degree_lt F d) = #F ^ d :=
begin
  let M := polynomial.degree_lt F d,
  have : finite_dimensional F M,
  {
    dsimp [M],
    rw polynomial.degree_lt_eq_span_X_pow,
    apply finite_dimensional.span_of_finite,
    rw finset.coe_image,
    apply set.finite.image,
    sorry
  },
  -- apply cardinal_mk_eq_cardinal_mk_field_pow_rank,
  sorry
end

def degree_eq (d : ℕ) : set R[X] := { f | f.nat_degree = d }
def monic_degree_eq (d : ℕ) := degree_eq R d ∩ { f | f.monic }
def irreducible_degree_eq (d : ℕ) := monic_degree_eq R d ∩ { f | irreducible f }

lemma finite_degree_eq (h : fintype R) : set.finite (degree_eq R d) := 
begin
  dsimp [degree_eq],
  sorry
end

instance [fintype R] (d : ℕ) : fintype (degree_eq R d) := sorry

variables (p : ℕ) [fact p.prime]

def 𝔽 (p : ℕ) := zmod p
instance : comm_ring (𝔽 p) := by apply zmod.comm_ring

instance (d : ℕ) : fintype (monic_degree_eq (𝔽 p) d) := sorry
def monics (d : ℕ) := (monic_degree_eq (𝔽 p) d).to_finset.card
instance (d : ℕ) : fintype (irreducible_degree_eq (𝔽 p) d) := sorry
def irreducibles (d : ℕ) := (irreducible_degree_eq (𝔽 p) d).to_finset.card

lemma monic_generating_function : @power_series.mk ℤ ↑(monics p) = power_series.rescale ↑p (power_series.inv_units_sub 1) :=
begin
  transitivity @power_series.mk ℤ (pow ↑p),
  {
    apply power_series.ext,
    simp only [power_series.coeff_mk],
    intros n,
    sorry
  },
  {
    apply power_series.ext,
    simp only [power_series.coeff_mk],
    sorry
  },
  -- ext,
  -- simp,
  -- sorry
end

def infinite_product {K : Type} (f : ℕ → power_series K) (start : ℕ) 
  -- [∀ n ≥ start, power_series.constant_coeff R (f n) = 1]
  : power_series K := sorry

lemma monic_generating_function' : @power_series.mk ℤ ↑(monics p) = infinite_product (λ d, (power_series.inv_units_sub 1) ^ (irreducibles p d)) 0 := sorry
-- cardinal_mk_eq_cardinal_mk_field_pow_rank
-- bijection between degree d monic polynomials and degree_lt d submodule

-- noncomputable def logarithmic_derivative {K : Type} [comm_ring K] [is_domain K] (f : K[X]) : ratfunc K := ratfunc.mk (polynomial.derivative f) f

noncomputable def derivative {K : Type} [semiring K] (ϕ : power_series K) : power_series K :=
  power_series.mk (λ n, (n + 1) * power_series.coeff K (n + 1) ϕ)

noncomputable def logarithmic_derivative {k : Type} [field k] (ϕ : power_series k) : power_series k :=
  derivative ϕ * ϕ⁻¹

-- lemma logarithmic_derivative_of_infinite_product {K : Type} {f : ℕ → K} : logarithmic_derivative (infinite_product f) = power_series.mk f := sorry

lemma irreducibles_arithmetic_function : ∀ n > (0 : ℕ), p^n = ∑d in n.divisors, d * irreducibles p d :=
begin
  have := monic_generating_function p,
  rw monic_generating_function' at this,
  have : infinite_product (λ (d : ℕ), power_series.inv_units_sub 1 ^ irreducibles p d) 0 = (power_series.rescale ↑p) (power_series.inv_units_sub 1) := sorry,
  have := congr_arg logarithmic_derivative this,
  repeat { sorry }
end

-- set_option pp.all true

theorem irreducibles_closed_form 
  : ∀ n > (0 : ℕ),
    ↑(irreducibles p n) = (∑x in n.divisors_antidiagonal, μ x.fst * p^x.snd) / n :=
begin
  let f : ℕ → ℤ := (λ d, d * irreducibles p d),
  let g : ℕ → ℤ := pow p,
  suffices : ∀ n, (0 : ℕ) < n → ∑x in n.divisors_antidiagonal, ↑(μ x.fst) * g x.snd = f n,
  { intros n hn,
    specialize this n hn,
    dsimp [f, g] at this,
    norm_cast at this,
    rw_mod_cast this,
    ring_nf,
    rw [nat.mul_div_assoc _ (dvd_refl n), nat.div_self hn, mul_one] },
  apply nat.arithmetic_function.sum_eq_iff_sum_mul_moebius_eq.mp,
  intros n hn,
  dsimp [g],
  rw_mod_cast (irreducibles_arithmetic_function p n hn),
  have := (nat.cast_ring_hom ℤ).map_sum (λ d, d * irreducibles p d) n.divisors,
  dsimp at this,
  -- norm_cast at this,
  -- rw_mod_cast this,
  sorry
end