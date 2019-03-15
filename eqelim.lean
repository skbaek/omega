import .ee .int 

variables {α β : Type}

open tactic
   
meta structure ee_state :=
    (eqs : list term)
    (les : list term)
    (ees : list ee)

@[reducible] meta def eqelim := state_t ee_state tactic

meta def abort {α : Type} : eqelim α := ⟨λ x, failed⟩ 

private meta def mk_eqelim_state (eqs les : list term) : tactic ee_state := 
return (ee_state.mk eqs les [])-- ⟨eqs,les,[]⟩ 

meta def get_eqs : eqelim (list term) := ee_state.eqs <$> get
meta def get_les : eqelim (list term) := ee_state.les <$> get
meta def get_ees : eqelim (list ee)   := ee_state.ees <$> get

meta def set_eqs (eqs : list term) : eqelim unit := modify $ λ s, {eqs := eqs, ..s}
meta def set_les (les : list term) : eqelim unit := modify $ λ s, {les := les, ..s}
meta def set_ees (es : list ee) : eqelim unit := modify $ λ s, {ees := es, ..s}

meta def add_ee (e : ee) : eqelim unit := do
es ← get_ees, set_ees (es ++ [e])

meta def head_eq : eqelim term := 
do eqs ← get_eqs,
   match eqs with 
   | []         := abort
   | (eq::eqs') := set_eqs eqs' >> pure eq
   end

meta def run {α : Type} (eqs les : list term) (r : eqelim α) : tactic α := 
prod.fst <$> (mk_eqelim_state eqs les >>= r.run)

meta def ee_commit (t1 : eqelim α) (t2 : eqelim β)
  (t3 : α → eqelim β) : eqelim β := 
do x ← ((t1 >>= return ∘ some) <|> return none),
   match x with 
   | none     := t2 
   | (some a) := t3 a
   end

notation t1 `!>>=` t2 `;` t3 := ee_commit t1 t2 t3

private meta def of_tactic {α : Type} : tactic α → eqelim α := state_t.lift 

meta def get_gcd (t : term) : eqelim int :=
pure ↑(ints.gcd t.snd) 

meta def factor (i : int) (t : term) : eqelim term :=
if i ∣ t.fst 
then add_ee (ee.factor i) >> pure (t.div i) 
else abort

/- If list has a nonzero element, return that element 
   with its index. Otherwise, return none. -/
meta def find_min_coeff_core : list int → eqelim (int × nat) 
| []      := abort 
| (i::is) := (do 
  (j,n) ← find_min_coeff_core is,
  if i ≠ 0 ∧ i.nat_abs ≤ j.nat_abs 
  then pure (i,0)
  else pure (j,n+1)) <|>
  (if i = (0 : int) then abort else pure (i,0))
   
-- Returns (s,m,i), where
--   s = term equivalent to t
--   m = index of nonzero coefficient with smallest absolute value
--   i = nonzero coefficient with smallest absolute value (positive)
meta def find_min_coeff (t : term) : eqelim (int × nat × term) :=
do (i,n) ← find_min_coeff_core t.snd,
   if 0 < i
   then pure (i,n,t)
   else add_ee (ee.neg) >> pure (-i,n,t.neg)

meta def elim_eq : eqelim unit := do
t ← head_eq,
i ← get_gcd t,
    factor i t !>>= (set_eqs [] >> add_ee (ee.nondiv i)) ; 
λ s, find_min_coeff s !>>= add_ee ee.drop ; 
λ x, let i : int := x.fst in 
     let n : nat := x.snd.fst in
     let u : term := x.snd.snd in 
if i = 1
then do eqs ← get_eqs, 
        les ← get_les,
              set_eqs (eqs.map (cancel n u)),
              set_les (les.map (cancel n u)),
              add_ee (ee.cancel n)
else let v : term := coeffs_reduce n u.fst u.snd in 
     let r : term := rhs n u.fst u.snd in 
     do eqs ← get_eqs, 
        les ← get_les,
              set_eqs (v::eqs.map (subst n r)),
              set_les (les.map (subst n r)),
              add_ee (ee.reduce n),
              elim_eq

meta def elim_eqs : eqelim (list ee) :=
elim_eq !>>= get_ees ; λ _, elim_eqs

meta def find_ees : clause → tactic (list ee) | (eqs,les) :=
run eqs les elim_eqs