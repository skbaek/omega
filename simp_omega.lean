import logic.basic data.list.basic

variables {α : Type} {p q : Prop}
run_cmd mk_simp_attr `omega 

attribute [omega]
  list.map 
  list.length_map 
  zero_mul
  mul_zero
  zero_add
  add_zero
  neg_zero
  zero_sub
  sub_zero
  false_and
  and_false
  true_or
  or_true
  list.forall_mem_nil
  sub_self

open lean
open lean.parser
open interactive
open tactic

meta def tactic.interactive.simp_omega 
  (use_iota_eqn : parse $ optional (tk "!")) 
  --(no_dflt : parse types.only_flag) 
  (hs : parse simp_arg_list) 
  (attr_names : parse types.with_ident_list)
  (locat : parse types.location) 
  (cfg : simp_config_ext := {}) : tactic unit :=
let cfg := if use_iota_eqn.is_none then cfg else {iota_eqn := tt, ..cfg} in
tactic.interactive.propagate_tags 
  (tactic.interactive.simp_core cfg.to_simp_config cfg.discharger tt hs [`omega] locat) 