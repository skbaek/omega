open tactic

variables {α β : Type}

meta def intro_fresh : tactic expr := 
do n ← get_unused_name, intro n

meta def pexpr.apply (x : pexpr) : tactic (list (name × expr)) :=
to_expr x >>= apply

meta def trace_target : tactic unit :=
target >>= trace

open expr

meta def split_or_core : list expr → tactic unit 
| [] := failed 
| (x::xs) := 
  do t ← infer_type x,
     match t with 
     | `(%%px ∨ %%qx) := 
       (cases x >> skip) 
       --trace "disj found" >> cases_core x >> trace "disj removed" >> skip
       -- seq (pexpr.apply ``(or.elim %%x _ _) >> skip) (intro_fresh >> skip)
     | _              := split_or_core xs
     end

meta def split_or : tactic unit := 
local_context >>= split_or_core

meta def split_and_core : list expr → tactic unit 
| [] := failed 
| (x::xs) := 
  do t ← infer_type x,
     match t with 
     | `(%%px ∧ %%qx) := 
       do np ← get_unused_name, 
          nq ← get_unused_name, 
          assertv np px (app (app (app `(@and.elim_left).to_expr px) qx) x),
          assertv nq qx (app (app (app `(@and.elim_right).to_expr px) qx) x),
          clear x
     | _ := split_and_core xs
     end

meta def split_and : tactic unit := 
local_context >>= split_and_core

local attribute [inline] interaction_monad_orelse

meta def commit (t1 t2 t3 : tactic unit) :=
monad.cond ((t1 >> return tt) <|> return ff) t2 t3
notation t1 `!>>` t2 `|` t3 := commit t1 t2 t3

-- meta def try_solve (t1 t2 : tactic unit) : tactic unit := 
-- t1 !>> (do n ← num_goals, if n = 0 then skip else t2), t2 
-- infixr `?>>` : 500 := try_solve 

meta def commit_seq (t1 t2 t3 : tactic unit) : tactic unit :=
 do g::gs ← get_goals,
    set_goals [g],
    (t1 !>> (all_goals t2) | t3),
    gs' ← get_goals,
    set_goals (gs' ++ gs)

notation t1 `!;` t2 `|` t3 : 500 := commit_seq t1 t2 t3


