import ..tactic

lemma add_lit_left {p q r : Prop} : 
  ¬((p ∧ q) ∧ r) → (p → (¬(q ∧ r))) := 
begin
  intros h1 h2 h3, cases h3 with h3 h4, 
  apply h1, exact ⟨⟨h2,h3⟩,h4⟩ 
end

lemma add_lit_right {p q r : Prop} : 
  ¬(q ∧ (p ∧ r)) → (p → (¬(q ∧ r))) := 
begin
  intros h1 h2 h3, cases h3 with h3 h4, 
  apply h1, exact ⟨h3,⟨h2,h4⟩⟩
end

open tactic


meta def revert_lit (x : expr) : tactic unit :=
do tx ← infer_type x,
   match tx with
   | `(@eq int _ _) :=
     do revert x, pexpr.apply ``(add_lit_left _), skip
   | `(@has_le.le int _ _ _) := 
     do revert x, pexpr.apply ``(add_lit_right _), skip
   | _          := skip
   end

meta def revert_int (x : expr) : tactic unit :=
do `(int) ← infer_type x | skip,
   revert x, skip

meta def univ_close : tactic unit :=
do local_context >>= list.mmap revert_lit, 
   local_context >>= list.mmap revert_int, 
   skip
