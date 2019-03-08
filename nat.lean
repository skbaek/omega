

namespace nat

def max' : nat → nat → nat 
| 0 0 := 0 
| (m+1) 0 := m+1
| 0 (n+1) := n+1
| (m+1) (n+1) := max' m n

def gcd' : nat → nat → nat
| 0        y := y
| (succ x) y := have y % succ x < succ x, from mod_lt _ $ succ_pos _,
                gcd' (y % succ x) (succ x)



#print axioms gcd'
#print axioms nat.mod
#print axioms nat.succ_pos

end nat