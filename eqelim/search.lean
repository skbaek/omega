import ..term 

open tactic

meta def find_contra : list (list nat × term) → tactic (list nat)
| []            := failed
| ((π,⟨c,_⟩)::l) := if c < 0 then return π else find_contra l

meta def trisect (m : nat) :  
  list (list nat × term) → (list (list nat × term) × 
  list (list nat × term) × list (list nat × term)) 
| [] := ([],[],[])
| ((p,t)::pts) := 
  let (neg,zero,pos) := trisect pts in 
  if t.coeffs.get m < 0 
  then ((p,t)::neg,zero,pos)
  else if t.coeffs.get m = 0 
       then (neg,(p,t)::zero,pos)
       else (neg,zero,(p,t)::pos)

meta def elim_var_aux (m : nat) : 
  ((list nat × term) × (list nat × term)) → tactic (list nat × term) 
| ((p1,t1), (p2,t2)) := 
  let n := int.nat_abs (t1.coeffs.get m) in
  let o := int.nat_abs (t2.coeffs.get m) in
  let lcm := (nat.lcm n o) in
  let n' := lcm / n in
  let o' := lcm / o in
  return (list.add (n' *₁ p1) (o' *₁ p2), 
          term.add (t1.mul n') (t2.mul o'))

meta def elim_var (m) (neg pos : list (list nat × term)) : 
  tactic (list (list nat × term)) :=
let pairs := list.product neg pos in 
monad.mapm (elim_var_aux m) pairs

meta def search_core : nat → list (list nat × term) → tactic (list nat) 
| 0 pts     := find_contra pts
| (m+1) pts :=
  let (neg,zero,pos) := trisect m pts in
  do new ← elim_var m neg pos,
     search_core m (new ++ zero)

meta def search (ts : list term) : tactic (list nat) :=
search_core 
  (ts.map (λ t : term, t.coeffs.length)).max  
  (ts.map_with_idx (λ m t, ([]{m ↦ 1}, t)))