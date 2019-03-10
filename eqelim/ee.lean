import .sat

open list

def symdiv (i j : int) : int := 
if (2 * (i % j)) < j
then i / j
else (i / j) + 1

def symmod (i j : int) : int := 
if (2 * (i % j)) < j
then i % j
else (i % j) - j

-- Requires : t1.coeffs[m] = 1
def cancel (m : nat) (t1 t2 : term) : term := 
term.add (t1.mul (-t2.coeffs.get m)) t2

/- Given a term t such that 0 = t and t = b + a₀ * x₀ + ... aₘ * xₘ,
   solve for the nth variable xₙ, obtain equation of the form xₙ = r,
   and return r (the rhs r has no occurrences of xₙ and includes a new 
   variable σ, which is assigned the index n which is no longer used). -/
def rhs : nat → term → term 
| n ⟨b,as⟩ := 
  let m := as.get n + 1 in
  ⟨-(symmod b m), (as.map (λ x, symmod x m)){n ↦ -m}⟩ 

def reduce_aux (m a : int) : int := 
symdiv a m + symmod a m

-- Requires : 0 < as[n]
def reduce : nat → term → term 
| n ⟨b,as⟩ := 
  let a := as.get n in
  let m := a + 1 in 
  ⟨reduce_aux m b, (as.map (reduce_aux m)){n ↦ -a}⟩ 

def subst (n : nat) (t1 t2 : term) : term := 
term.add (t1.mul (t2.coeffs.get n)) ({t2 with coeffs := t2.coeffs{n ↦ 0}})

@[derive has_reflect]
inductive ee : Type 
| drop   : ee 
-- | contra : ee
| nondiv : int → ee
| factor : int → ee
| neg    : ee
| reduce : nat → ee
| cancel : nat → ee 

namespace ee

def repr : ee → string 
| drop   := "↓" 
-- | contra := "⊥"
| (nondiv i) := i.repr ++ "∤" 
| (factor i) := "/" ++ i.repr
| neg    := "-"
| (reduce n) := "≻" ++ n.repr
| (cancel n) := "∓" ++ n.repr 

instance has_repr : has_repr ee := ⟨repr⟩ 

meta instance has_to_format : has_to_format ee := ⟨λ x, x.repr⟩ 

end ee 

@[reducible] def conc : list term → list term → 
  list ee → (list term × list term)
| [] les []     := ([],les)
| [] les (_::_) := ([],[])
| (_::_) les [] := ([],[])
| (eq::eqs) les (ee.drop::es) := conc eqs les es
-- | (eq::eqs) les (ee.contra::es) := 
--   if eq.const ≠ 0 ∧ ∀ x ∈ eq.coeffs, x = (0 : int)
--   then ([],[⟨-1,[]⟩])
--   else ([],[])
| (eq::eqs) les (ee.neg::es) := conc (eq.neg::eqs) les es
| (eq::eqs) les (ee.nondiv i::es) := 
  if ¬(i ∣ eq.const) ∧ (∀ x ∈ eq.coeffs, i ∣ x)
  then ([],[⟨-1,[]⟩])
  else ([],[])
| (eq::eqs) les (ee.factor i::es) := 
  if (i ∣ eq.const) ∧ (∀ x ∈ eq.coeffs, i ∣ x)
  then conc (term.div i eq::eqs) les es
  else ([],[])
| (eq::eqs) les (ee.reduce m::es) :=
  let eq' := _root_.reduce m eq in
  let r := rhs m eq in 
  let eqs' := eqs.map (subst m r) in
  let les' := les.map (subst m r) in
  conc (eq'::eqs') les' es
| (eq::eqs) les (ee.cancel m::es) := 
  conc (eqs.map (_root_.cancel m eq)) (les.map (_root_.cancel m eq)) es


open tactic

lemma sat_empty_consts : sat [] [] := 
⟨λ _,0, ⟨dec_trivial, dec_trivial⟩⟩ 

lemma sat_conc : ∀ {eqs les : list term}, sat eqs les → 
  ∀ {es}, sat' (conc eqs les es)
| [] les h []     := h
| [] les h (_::_) := sat_empty_consts
| (_::_) les h [] := sat_empty_consts
| (eq::eqs) les h (ee.drop::es) := 
  begin
    apply (@sat_conc _ _ _ es), 
    apply sat_of_weaker _ _ h,
    apply list.subset_cons,
    apply list.subset.refl
  end
-- | (eq::eqs) les h1 (ee.contra::es) := 
--   begin
--     simp only [conc], apply ite.rec; intro h2, 
--     cases eq with b as, 
--     { cases h1 with v h1, have h3 := h1.left _ (or.inl rfl),
--       simp_omega at h3, rw [val_aux_eq_zero h2.right, add_zero] at h3,
--       subst h3, exfalso, apply h2.left rfl }, 
--     { apply sat_empty_consts }
--   end
| (eq::eqs) les h (ee.neg::es) := sorry
| (eq::eqs) les h (ee.nondiv i::es) := sorry
| (eq::eqs) les h (ee.factor i::es) :=  sorry
| (eq::eqs) les h (ee.reduce m::es) := sorry
| (eq::eqs) les h (ee.cancel m::es) := sorry


lemma unsat_of_unsat_conc {eqs les} (ee) :
  unsat (conc eqs les ee).fst (conc eqs les ee).snd → 
  unsat eqs les :=
begin intros h1 h2, apply h1, apply sat_conc h2 end
