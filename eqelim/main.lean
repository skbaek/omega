import .univ_close .reify ..term .eqelim .proof .search

def preunsat (eqs les : list preatom) : Prop := 
¬ ∃ v : nat → int, (eqs_hold v eqs ∧ les_hold v les)

lemma uniclo_of_preunsat {eqs les : list preatom} : 
  ∀ {m v}, preunsat eqs les → uniclo eqs les m v 
| 0 v h1     := λ h2, h1 ⟨v, h2⟩ 
| (m+1) v h1 := λ i,  uniclo_of_preunsat h1

def preatom_to_term : preatom → term
| (s,t) := term.sub (canonize t) (canonize s)

def preunsat_of_unsat {eqs les : list preatom} : 
  unsat (eqs.map preatom_to_term) (les.map preatom_to_term) → preunsat eqs les := sorry

lemma uniclo_of_unsat {eqs les : list preatom} : 
  unsat (eqs.map preatom_to_term) (les.map preatom_to_term) → 
  ∀ {m v}, uniclo eqs les m v := 
begin
  intros h1 m v, apply uniclo_of_preunsat,
  apply preunsat_of_unsat h1 
end

open tactic

meta def get_consts : tactic (list term × list term) :=
do `(unsat %%eqsx %%lesx) ← target, 
    eqs ← eval_expr (list term) eqsx,
    les ← eval_expr (list term) lesx,
    return (eqs,les)

meta def apply_ees : tactic unit :=
do (eqs,les) ← get_consts,
   ees ← find_ees eqs les,
   trace ees,
   pexpr.apply ``(unsat_of_unsat_conc %%`(ees) _),
   skip

meta def discharge : tactic unit :=
do ([],eqs) ← get_consts,
   ns ← search eqs,
   pexpr.apply ``(unsat_of_unsat_comb %%`(ns) _), 
   to_expr ``(trivial) >>= apply,
   skip 

meta def omega_core : tactic unit :=
do univ_close, 
   reify,
   pexpr.apply ``(uniclo_of_unsat _),
   (eqs,les) ← get_consts, 
   apply_ees,
   discharge
