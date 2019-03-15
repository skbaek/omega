import .clause 

open tactic

meta def trisect (m : nat) :  
  list (list nat × term) → (list (list nat × term) × 
  list (list nat × term) × list (list nat × term)) 
| [] := ([],[],[])
| ((p,t)::pts) := 
  let (neg,zero,pos) := trisect pts in 
  if t.snd.get m < 0 
  then ((p,t)::neg,zero,pos)
  else if t.snd.get m = 0 
       then (neg,(p,t)::zero,pos)
       else (neg,zero,(p,t)::pos)

meta def elim_var_aux (m : nat) : 
  ((list nat × term) × (list nat × term)) → tactic (list nat × term) 
| ((p1,t1), (p2,t2)) := 
  let n := int.nat_abs (t1.snd.get m) in
  let o := int.nat_abs (t2.snd.get m) in
  let lcm := (nat.lcm n o) in
  let n' := lcm / n in
  let o' := lcm / o in
  return (list.add (n' *₁ p1) (o' *₁ p2), 
          term.add (t1.mul n') (t2.mul o'))

meta def elim_var (m) (neg pos : list (list nat × term)) : 
  tactic (list (list nat × term)) :=
let pairs := list.product neg pos in 
monad.mapm (elim_var_aux m) pairs

meta def find_contra : list (list nat × term) → tactic (list nat)
| []            := failed
| ((π,⟨c,_⟩)::l) := if c < 0 then return π else find_contra l

meta def search_core : nat → list (list nat × term) → tactic (list nat) 
| 0 pts     := find_contra pts
| (m+1) pts :=
  let (neg,zero,pos) := trisect m pts in
  do new ← elim_var m neg pos,
     search_core m (new ++ zero)

meta def search (ts : list term) : tactic (list nat) :=
search_core 
  (ts.map (λ t : term, t.snd.length)).max  
  (ts.map_with_idx (λ m t, ([]{m ↦ 1}, t)))

@[omega] def comb : list term → list nat → term 
| [] []     := ⟨0,[]⟩ 
| [] (_::_) := ⟨0,[]⟩ 
| (_::_) [] := ⟨0,[]⟩ 
| (t::ts) (n::ns) := term.add (t.mul ↑n) (comb ts ns)

lemma comb_holds {v} :
  ∀ {ts} ns, (∀ t ∈ ts, 0 ≤ term.val v t) → (0 ≤ (comb ts ns).val v) 
| [] []     h := by simp_omega
| [] (_::_) h := by simp_omega
| (_::_) [] h := by simp_omega
| (t::ts) (n::ns) h :=
  begin
    simp_omega, apply add_nonneg, 
    { apply mul_nonneg,
      apply int.coe_nat_nonneg,
      apply h _ (or.inl rfl) },
    { apply comb_holds, 
      apply list.forall_mem_of_forall_mem_cons h }
  end

def unsat_comb (ts ns) : Prop :=
(comb ts ns).fst < 0 ∧ ∀ x ∈ (comb ts ns).snd, x = (0 : int)

lemma unsat_comb_of (ts ns) : 
(comb ts ns).fst < 0 → 
(∀ x ∈ (comb ts ns).snd, x = (0 : int)) → 
unsat_comb ts ns := 
begin intros h1 h2, exact ⟨h1,h2⟩ end

lemma unsat_of_unsat_comb (ns les) :
  (unsat_comb les ns) → clause.unsat ([], les) :=
begin
  intros h1 h2, cases h2 with v h2, 
  have h3 := comb_holds ns h2.right,
  cases h1 with hl hr, 
  cases (comb les ns) with b as,
  simp_omega at h3, 
  rw [coeffs.val_eq_zero hr, add_zero, ← not_lt] at h3,
  apply h3 hl 
end

#exit
lemma unsat_of_unsat_comb' (ts : polytope) (ns : list nat) :
  (unsat_comb' ts ns) → ts.unsat :=
begin
  intro h1, apply unsat_of_unsat_comb ns,
  simp only [unsat_comb'] at h1, 
  simp only [unsat_comb], 
  rw if_pos h1, trivial
end