import .int .simp_omega

@[derive has_reflect]
inductive preterm : Type
| cst : int → preterm 
| var : int → nat → preterm
| add : preterm → preterm → preterm 

notation `&` k := preterm.cst k
infix `**` : 300 := preterm.var 
notation t `+*` s := preterm.add t s
-- | (& i) := sorry
-- | (i ** n) := sorry
-- | (t1 +* t2) := sorry

namespace preterm 

@[omega] def val (v : nat → int) : preterm → int 
| (& i) := i
| (i ** n) := 
  if i = 1 
  then v n
  else if i = -1 
       then -(v n) 
       else (v n) * i
| (t1 +* t2) := t1.val + t2.val 

def fresh_idx : preterm → nat 
| (& _) := 0
| (i ** n) := n + 1
| (t1 +* t2) := max t1.fresh_idx t2.fresh_idx 

@[omega] def succ (t : preterm) : preterm := t +* (&1)

def repr : preterm → string 
| (& i) := i.repr
| (i ** n) := i.repr ++ "*x" ++ n.repr
| (t1 +* t2) := "(" ++ t1.repr ++ " + " ++ t2.repr ++ ")"

end preterm
