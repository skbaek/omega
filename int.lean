import .list data.int.basic

def ints.gcd : list int → nat
| []      := 0
| (i::is) := nat.gcd i.nat_abs (ints.gcd is)

namespace int 

meta instance has_reflect : has_reflect int := by tactic.mk_has_reflect_instance

#exit

def lcm (x y : int) : int :=
  (nat.lcm (nat_abs x) (nat_abs y))

def lt' : int → int → Prop 
| (of_nat m) (of_nat n) := m < n 
| (of_nat _) -[1+ _]    := false
| -[1+ _]    (of_nat _) := true
| -[1+ m]    -[1+ n]    := n < m

instance decidable_lt' : ∀ i j : int, decidable (lt' i j)
| (of_nat m) (of_nat n) := nat.decidable_lt _ _
| (of_nat _) -[1+ _]    := decidable.false
| -[1+ _]    (of_nat _) := decidable.true
| -[1+ m]    -[1+ n]    := nat.decidable_lt _ _

def le' : int → int → Prop 
| (of_nat m) (of_nat n) := m ≤ n 
| (of_nat _) -[1+ _]    := false
| -[1+ _]    (of_nat _) := true
| -[1+ m]    -[1+ n]    := n ≤ m

def sub' : int → int → int 
| (of_nat m) (of_nat n) := 
  if n ≤ m 
  then of_nat (m-n)
  else -[1+ n-m-1]
| (of_nat m) -[1+ n]    := of_nat (m+n)
| -[1+ m]    (of_nat n) := -[1+ (m+n)]
| -[1+ m]    -[1+ n]    := 
  if n ≤ m 
  then -[1+ (m-n-1)]
  else of_nat (n-m)

-- lemma sub'_eq_sub {i j : int} : sub' i j = i - j := sorry

instance decidable_le' : ∀ i j : int, decidable (le' i j)
| (of_nat m) (of_nat n) := nat.decidable_le _ _
| (of_nat _) -[1+ _]    := decidable.false
| -[1+ _]    (of_nat _) := decidable.true
| -[1+ m]    -[1+ n]    := nat.decidable_le _ _


end int

def ints.sub : list int → list int → list int 
| [] []        := []
| [] (a2::as2) := list.neg (a2::as2)
| (a1::as1) [] := a1::as1
| (a1::as1) (a2::as2) := (int.sub' a1 a2)::(ints.sub as1 as2) 