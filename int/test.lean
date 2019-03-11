import ..int

open int tactic

meta def all_zeroes (as : list int) : tactic expr :=
do tx ← return `(trivial),
   return `(@of_as_true (∀ x : int, x ∈ %%`(as) → x = (0 : int)) _ %%tx)

