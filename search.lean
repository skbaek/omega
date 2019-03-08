import .proof

open tactic

meta def find_contra : list (proof × term) → tactic proof
| []            := failed
| ((π,⟨c,_⟩)::l) := if c < 0 then return π else find_contra l

meta def trisect (m : nat) :  
  list (proof × term) → (list (proof × term) × 
  list (proof × term) × list (proof × term)) 
| [] := ([],[],[])
| ((p,t)::pts) := 
  let (neg,zero,pos) := trisect pts in 
  if t.coeffs[m] < 0 
  then ((p,t)::neg,zero,pos)
  else if t.coeffs[m] = 0 
       then (neg,(p,t)::zero,pos)
       else (neg,zero,(p,t)::pos)

meta def elim_var_aux (m : nat) : 
  ((proof × term) × (proof × term)) → tactic (proof × term) 
| ((p1,t1), (p2,t2)) := 
  let n := int.nat_abs (t1.coeffs[m]) in
  let o := int.nat_abs (t2.coeffs[m]) in
  let lcm := (nat.lcm n o) in
  let n' := lcm / n in
  let o' := lcm / o in
  return (proof.elim (p1.mul n') (p2.mul o'), term.add (t1.mul n') (t2.mul o'))

meta def elim_var (m) (neg pos : list (proof × term)) : 
  tactic (list (proof × term)) :=
let pairs := list.product neg pos in 
monad.mapm (elim_var_aux m) pairs

meta def search_core : nat → list (proof × term) → tactic proof 
| 0 pts     := find_contra pts
| (m+1) pts :=
  let (neg,zero,pos) := trisect m pts in
  do new ← elim_var m neg pos,
     search_core m (new ++ zero)

meta def search (ts : list term) : tactic proof :=
search_core 
  (ts.map (λ t : term, t.coeffs.length)).max  
  (ts.map_with_idx (λ m t, (proof.hyp m, t)))