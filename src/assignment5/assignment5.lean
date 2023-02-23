import data.real.basic
import data.nat.prime

/-
# Assignment 5

- Homework 5 is due on Friday, February 24. 
- It is worth 62 points total.
- Goal: get a working copy of the proof of the ivt

# The intermediate value theorem
-/

def approaches_at (f : ℝ → ℝ) (b : ℝ) (a : ℝ) :=
∀ ε > 0, ∃ δ > 0, ∀ x, abs (x - a) < δ → abs (f x - b) < ε

def continuous (f : ℝ → ℝ) := ∀ a, approaches_at f (f a) a

section
variables (a b : ℝ) (f : ℝ → ℝ) (S : set ℝ)

#check Sup S

#check @Sup
#check Sup { x : ℝ | a ≤ x ∧ x ≤ b ∧ f x < 0 }

#check le_cSup
#check @le_cSup 

#check cSup_le
--#check @cSup_le

--#print bdd_above.   
--#print upper_bounds.

#check exists_lt_of_lt_cSup
--#check @exists_lt_of_lt_cSup

#check tactic.linarith



theorem ivt {f : ℝ → ℝ} {a b : ℝ} (aleb : a ≤ b)
    (ctsf : continuous f) (hfa : f a < 0) (hfb : 0 < f b) :
  ∃ x, a ≤ x ∧ x ≤ b ∧ f x = 0 :=
begin
  let S := {x : ℝ | a ≤ x ∧ x ≤ b ∧ f x < 0 },
  have ainS : a ∈ S, 
  { --dsimp,
    exact ⟨le_refl a, aleb, hfa⟩,  
  },
  
  have bddS : bdd_above S,
  { unfold bdd_above,
  use b,
  intros s sinS,
  exact sinS.2.1,
  },
  have Sfull : S.nonempty,
  { 
  use a, exact ainS,
  },
  
  have e := Sup S,-- not the same
  let d := Sup S,-- same, but no eqn
  set c :=  Sup S with cdef,

  have cleb: c ≤ b,
  { apply cSup_le Sfull,
    intros s sinS,
    exact sinS.2.1,
  },

  have alec: a ≤ c,
  { exact le_cSup bddS ainS,
  },




  rcases trichotomous_of (<) (f c) 0 with h | h | h,
  {-- case where f c < 0, going for a contradiction  
  exfalso,
  specialize ctsf c,
  set ε := - f c / 2 with εdef,
  have εpos : ε > 0 , linarith,
  specialize ctsf ε εpos,
  rcases ctsf with ⟨δ, δpos, hδ⟩, 
  -- We need to check that c+δ/2 is _in_ S
  by_cases hcb: c+δ/2 > b,
  { have bnearc : | b - c | < δ,
    { rw abs_lt,
      split; linarith,-- note the ; 
    },
    specialize hδ b bnearc,
    rw abs_lt at hδ,
    linarith, --deduces false from the inequalities
  },
  push_neg at hcb,
  -- now in the case where c+δ/2 ≤ b.
  have c2nearc: | c+ δ/2 -c | < δ,
  { simp,
    rw abs_lt,
    split; --; says "apply next command to all goals"
    linarith,
  },
  specialize hδ (c+δ/2) c2nearc,
  rw abs_lt at hδ,
  have fc2lt0 : f (c+δ/2) <0,
  { linarith,
  },
  have c2inS: c+δ/2 ∈ S,  --added after lecture
  { exact ⟨ by linarith,hcb, fc2lt0⟩, 
  },
  have c2lec : c+δ/2 ≤c,  --added after lecture
  { exact le_cSup bddS c2inS,
  },
  linarith   /-PROBLEM 1 [2pts]: replace `sorry` with
             a single command on this line, using one 
             that will work with linear equaltions and/or
             inequalities and derive a contradiction. 
             Hint: it has closed 5 subgoals above already!-/
  },

  {/- case where f c = 0
      PROBLEM 2 [8pts]: complete the proof in this case.
      We wrote `Done!` for this case on the board-/
    exact ⟨c, alec, cleb, h⟩ --can be done in one line using angle braces like these: ⟨ , , ⟩
  },

  --case where 0 < f c , also for a contradiction
  /- PROBLEM 3 [52pts]: Fill in all the `sorry` commands below.
     OR, if you are looking for a challenge, delete the rest of the
     proof below and try to fill it in from scratch (or you 
     can try a middle ground, where you comment out the proof,
     and only refer to it when you get stuck).  You get full credit
     either way, so it is fine to use the outline.
   -/



  exfalso,
  set ε := f c /2 with εdef, -- define a new ε = (f c)/2
  have εpos : 0 < ε, -- ε is positive
  { --[2pts]
    linarith
  },
  specialize ctsf c,  -- we are inerested in continuity at c 
  specialize ctsf ε (εpos), -- use ε = (f c) / 2 in continuity at c
  rcases ctsf with ⟨ δ, δpos, hδ⟩, -- that produces a δ >0, which we study next
  
  have find_s : ∃ s ∈ S , c-δ/2 < s,
  { --[10pts] -- if you get stuck, look through the #check statements above.
    apply exists_lt_of_lt_cSup,
    apply Sfull,
    linarith
  },
  
  rcases find_s with ⟨ s, sinS, hs ⟩,-- pick a particular s ∈ S with c-δ/2 < s
  
  have slec : s ≤ c,
  { --[10pts]
    apply le_cSup,
    apply bddS,
    apply sinS
  },

  have snearc : |s - c| < δ,
  { --[10pts]
    have : |s - c| = c - s,
    {
      nth_rewrite 1 ←neg_sub,
      apply abs_of_nonpos,
      linarith
    },
    linarith
  },

  have fspos : 0 < f s,
  { --[15pts]
    by_contra fspos',
    push_neg at fspos',
    specialize (hδ s snearc),
    rw ←not_le at hδ,
    apply hδ,
    have : f s - f c ≤ 0, { linarith },
    rw abs_of_nonpos this,
    linarith
  },
  --[5pts]
  /- Verify that `linarith` alone does not work below.
     What is missing?
     It turns out the missing equation is f s < 0. 
     We essentially want to type:
     linarith [f s < 0],
     which tells linarith to run its usual plan, but also 
     use the inequality f s < 0.  However, we do not actually
     write an inequality in the square brackets; we instead
     write a _proof_ of the relevant inequality.  
     So enter below the command 
     linarith [something], 
     where you replace the `something` with a proof term
     for  f s < 0.  
     (Hint: use the fact that s ∈ S.)  
  -/
  linarith [sinS.right.right]

end


end