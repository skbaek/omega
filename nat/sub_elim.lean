import .form ..list

namespace nat

def update (m n) (v : nat → nat) : nat → nat 
| x := if x = m then n else v x

lemma update_eq (m n v) : update m n v m = n :=
begin simp only [update, if_pos rfl] end

lemma update_eq_of_ne {m n v k} : 
  m ≠ k → update m n v k = v k :=
begin
  intro h1, simp only [update],
  rw if_neg h1.symm
end

namespace preterm

def sub_terms : preterm → option (preterm × preterm)
| (& i)      := none
| (i ** n)   := none
| (t +* s) := t.sub_terms <|> s.sub_terms
| (t -* s) := t.sub_terms <|> s.sub_terms <|> some (t,s)

def sub_subst (t s : preterm) (k : nat) : preterm → preterm 
| t@(& m)    := t
| t@(m ** n) := t
| (x +* y) := x.sub_subst +* y.sub_subst
| (x -* y) := 
  if x = t ∧ y = s then (1 ** k)
  else x.sub_subst -* y.sub_subst

lemma val_sub_subst {k x y v} :
  ∀ {t : preterm}, t.fresh_idx ≤ k → 
  (sub_subst x y k t).val 
  (update k (x.val v - y.val v) v) = t.val v 
| (& m)    h1 := rfl
| (m ** n) h1 := 
  begin 
    simp_omega [sub_subst], apply congr_arg,
    apply update_eq_of_ne (ne_of_gt _),
    apply lt_iff_add_one_le.elim_right h1,
 end
| (t +* s) h1 := 
  begin
    simp_omega [sub_subst], apply fun_mono_2;
    apply val_sub_subst (le_trans _ h1), 
    apply le_max_left, apply le_max_right
  end
| (t -* s) h1 := 
  begin
    simp_omega [sub_subst], 
    by_cases h2 : t = x ∧ s = y,
    { rw if_pos h2, simp_omega,
      rw [update_eq, h2.left, h2.right, one_mul] },
    { rw if_neg h2, simp_omega [sub_subst],
      apply fun_mono_2;
      apply val_sub_subst (le_trans _ h1), 
      apply le_max_left, apply le_max_right, }
  end

end preterm

namespace form

def sub_terms : form → option (preterm × preterm)
| (t =* s) := t.sub_terms <|> s.sub_terms
| (t ≤* s) := t.sub_terms <|> s.sub_terms
| (¬* p)   := p.sub_terms
| (p ∨* q) := p.sub_terms <|> q.sub_terms
| (p ∧* q) := p.sub_terms <|> q.sub_terms

@[omega] def sub_subst (x y : preterm) (k : nat) : form → form 
| (t =* s) := preterm.sub_subst x y k t =* preterm.sub_subst x y k s
| (t ≤* s) := preterm.sub_subst x y k t ≤* preterm.sub_subst x y k s
| (¬* p)   := ¬* p.sub_subst
| (p ∨* q) := p.sub_subst ∨* q.sub_subst
| (p ∧* q) := p.sub_subst ∧* q.sub_subst

end form

def is_diff (t s k) : form := 
((t =* (s +* (1 ** k))) ∨* (t ≤* s ∧* ((1 ** k) =* &0))) 

lemma holds_is_diff {t s : preterm} {k} {v : nat → nat} :
  v k = t.val v - s.val v → (is_diff t s k).holds v := 
begin
  intro h1, simp_omega [is_diff, if_pos (eq.refl 1)],
  by_cases h2 : t.val v ≤ s.val v, 
  { right, refine ⟨h2,_⟩, 
    rw [h1, one_mul, nat.sub_eq_zero_iff_le], exact h2 },
  { left, rw [h1, one_mul, add_comm, nat.sub_add_cancel _], 
    rw not_le at h2, apply le_of_lt h2 }
end

def sub_elim_core (t s k) (p : form) : form := 
(form.sub_subst t s k p) ∧* (is_diff t s k)

def sub_fresh_idx (t s : preterm) (p : form) : nat :=
max p.fresh_idx (max t.fresh_idx s.fresh_idx) 

def sub_elim (t s) (p : form) : form := 
-- sub_elim_core t s p.fresh_idx p
sub_elim_core t s (sub_fresh_idx t s p) p

lemma sub_subst_equiv {k} {x y : preterm} {v} :
  ∀ p : form, p.fresh_idx ≤ k → ((form.sub_subst x y k p).holds 
    (update k (x.val v - y.val v) v) ↔ (p.holds v)) 
| (t =* s) h1 := 
  begin
    simp_omega, apply pred_mono_2;
    apply preterm.val_sub_subst (le_trans _ h1),
    apply le_max_left, apply le_max_right
  end
| (t ≤* s) h1 := 
  begin
    simp_omega, apply pred_mono_2;
    apply preterm.val_sub_subst (le_trans _ h1),
    apply le_max_left, apply le_max_right
  end
| (¬* p) h1 :=  
  by { apply not_iff_not_of_iff, apply sub_subst_equiv p h1 } 
| (p ∨* q) h1 := 
  begin
    simp_omega, apply pred_mono_2; apply propext;
    apply sub_subst_equiv _ (le_trans _ h1),
    apply le_max_left, apply le_max_right
  end
| (p ∧* q) h1 := 
  begin
    simp_omega, apply pred_mono_2; apply propext;
    apply sub_subst_equiv _ (le_trans _ h1),
    apply le_max_left, apply le_max_right
  end

lemma sat_sub_elim {t s} {p : form} :
  p.sat → (sub_elim t s p).sat := 
begin
  intro h1, simp only [sub_elim, sub_elim_core], 
  cases h1 with v h1, 
  refine ⟨update (sub_fresh_idx t s p) (t.val v - s.val v) v, _⟩, 
  constructor,
  { apply (sub_subst_equiv p _).elim_right h1,
    apply le_max_left },
  { apply holds_is_diff, rw update_eq, 
    apply sub_eq_sub_of_eq_of_eq;
    apply preterm.val_constant; intros x h2;
    rw update_eq_of_ne; apply ne_of_gt;
    apply lt_of_lt_of_le h2;
    apply le_trans _ (le_max_right _ _),
    apply le_max_left, apply le_max_right }
end

lemma unsat_of_unsat_sub_elim (t s p) :
  (sub_elim t s p).unsat → p.unsat := 
not_of_imp_of_not sat_sub_elim

#exit


#exit

def sub_elim (o : nat) : 
  preterm → list (preterm × preterm) → 
  (preterm × list (preterm × preterm)) 
| (&m)     ds := (&m, ds)
| (m ** n) ds := (m ** n, ds)
| (t +* s) ds := 
  let (t',ds') := sub_elim t ds in
  let (s',ds'') := sub_elim s ds' in
  (t' +* s', ds'')
| (t -* s) ds := 
  let (t',ds') := sub_elim t ds in
  let (s',ds'') := sub_elim s ds' in
  let m := ds''.index_of (t',s') in
  (1 ** (m + o), list.snoc_if_oob m (t',s') ds'')

end preterm

namespace form

def sub_elim_core (o : nat) : 
  form → list (preterm × preterm) → 
  (form × list (preterm × preterm)) 
| (t =* s) ds := 
  let (t',ds') := preterm.sub_elim o t ds in
  let (s',ds'') := preterm.sub_elim o t ds' in
  (t' =* s', ds'')
| (t ≤* s) ds := 
  let (t',ds') := preterm.sub_elim o t ds in
  let (s',ds'') := preterm.sub_elim o t ds' in
  (t' ≤* s', ds'')
| (¬* p)   ds := 
  let (p',ds') := sub_elim_core p ds in 
  (¬*p',ds')
| (p ∨* q) ds := 
  let (p',ds') := sub_elim_core p ds in 
  let (q',ds'') := sub_elim_core q ds' in 
  (p' ∨* q', ds'')
| (p ∧* q) ds := 
  let (p',ds') := sub_elim_core p ds in 
  let (q',ds'') := sub_elim_core q ds' in 
  (p' ∧* q', ds'')

def is_diff : nat → (preterm × preterm) → form 
| m (t,s) := 
  let r : preterm := 1 ** m in 
  (t =* (s +* r)) ∨* (t ≤* s ∧* (r =* &0))

def are_diffs : nat → list (preterm × preterm) → form 
| m []      := (&0 =* &0)
| m (d::ds) := is_diff m d ∧* are_diffs (m+1) ds

lemma sat_sub_elim_core (o v) :
  ∀ (p : form) ds, 
  p.fresh_idx ≤ o → 
  (∀ (d : preterm × preterm), d ∈ ds →  
    (d.fst.fresh_idx ≤ o ∧ d.snd.fresh_idx ≤ o)) → 
  p.holds v → 
  (are_diffs o ds).holds v → 
  ∃ w : nat → nat, (
    (∀ n < (o + ds.length), v n = w n) ∧ 
    (sub_elim_core o p ds).fst.holds w  ∧ 
    (are_diffs o (sub_elim_core o p ds).snd).holds w  
  ) := sorry

def sub_elim (p : form) : form := 
let o := p.fresh_idx in
let pds := sub_elim_core o p [] in
pds.fst ∧* are_diffs o pds.snd 

#check @le_max_left
lemma sat_sub_elim_aux :
 ∀ p m ds, 
 neg_free p → 
 sat (p ∧* are_diffs m ds) → 
 p.fresh_idx ≤ m → 
 (∀ (d : preterm × preterm), d ∈ ds →  
   (d.fst.fresh_idx ≤ m ∧ d.snd.fresh_idx ≤ m)) → 
 sat ((sub_elim_core m p ds).fst ∧* 
   are_diffs m (sub_elim_core m p ds).snd) 
| (t =* s) m ds h0 h1 h2 h3 := sorry
| (t ≤* s) m ds h0 h1 h2 h3 := sorry
| (¬* p)   m ds h0 h1 h2 h3 := sorry
| (p ∨* q) m ds h0 h1 h2 h3 := sorry 
| (p ∧* q) m ds h0 h1 h2 h3 := 
  begin
    cases h1 with v h1, cases h1 with h1 hds,
    cases h1 with hp hq,
    cases (sat_sub_elim_core m v p ds 
      (le_trans (le_max_left _ _) h2) h3 hp hds) with u h4,
    have h5 := sat_sub_elim_core m u q (sub_elim_core m p ds).snd 
      (le_trans (le_max_right _ _) h2),
    --cases (sat_sub_elim_core m v p ds 
    --  (le_trans (le_max_left _ _) h2) h3 hp hds) with u h4,

  end 

#exit
#exit
lemma sat_sub_elim {p : form} :
  p.sat → (sub_elim p).sat :=
begin 
  intro h1, apply sat_sub_elim_aux 
    p p.fresh_idx [] h1 (le_refl _)
end

#exit
#exit



#exit
def sub_count : form → nat 
| (t =* s) := t.sub_count + s.sub_count
| (t ≤* s) := t.sub_count + s.sub_count
| (¬* p)   := p.sub_count
| (p ∨* q) := p.sub_count + q.sub_count
| (p ∧* q) := p.sub_count + q.sub_count


open tactic

lemma sub_terms_is_none' :
  ∀ p, (sub_terms p).is_none' ↔ sub_free p :=
by form.induce $ try_all [ 
    `[apply ih],  
    `[simp only [sub_terms, sub_free, option.orelse_is_none'], 
      apply and_iff_and], 
    `[apply preterm.sub_terms_is_none'],
    `[apply ihp], `[apply ihq] 
   ]

def sub_occurs (x y : preterm) : form → Prop 
| (t =* s) := preterm.sub_occurs x y t ∨ preterm.sub_occurs x y s
| (t ≤* s) := preterm.sub_occurs x y t ∨ preterm.sub_occurs x y s
| (¬* p)   := p.sub_occurs
| (p ∨* q) := p.sub_occurs ∨ q.sub_occurs
| (p ∧* q) := p.sub_occurs ∨ q.sub_occurs


end form 

open form 


def sub_elim_core : nat → form → form 
| 0 p := p
| (m+1) p := 
  match sub_terms p with 
  | none       := p 
  | some (t,s) := sub_elim_core m (sub_equiv t s p)
  end


lemma sub_free_of_sub_count_zero : 
  ∀ p, sub_count p = 0 → sub_free p 
| (t =* s) h := 
  begin
    simp only [sub_count, add_eq_zero_iff] at h,
    cases h, constructor;
    apply preterm.sub_free_of_sub_count_zero;
    assumption
  end
| (t ≤* s) h :=
  begin
    simp only [sub_count, add_eq_zero_iff] at h,
    cases h, constructor;
    apply preterm.sub_free_of_sub_count_zero;
    assumption
  end
| (¬* p)   h := sub_free_of_sub_count_zero p h
| (p ∨* q) h := 
  begin
    simp only [sub_count, add_eq_zero_iff] at h, cases h,
    constructor; apply sub_free_of_sub_count_zero; assumption
  end
| (p ∧* q) h := 
  begin
    simp only [sub_count, add_eq_zero_iff] at h, cases h,
    constructor; apply sub_free_of_sub_count_zero; assumption
  end

lemma sub_occurs_of_sub_terms_eq {t s} :
  ∀ p : form, sub_terms p = some (t,s) → sub_occurs t s p 
| (x =* y) h1 := 
  begin
    cases (option.orelse_eq' h1) with h2 h2; [left,right]; 
    apply preterm.sub_occurs_of_sub_terms_eq; assumption
  end 
| (x ≤* y) h1 :=
  begin
    cases (option.orelse_eq' h1) with h2 h2; [left,right]; 
    apply preterm.sub_occurs_of_sub_terms_eq; assumption
  end 
| (¬* p) h1 := sub_occurs_of_sub_terms_eq p h1
| (p ∨* q) h1 := 
  begin
    cases (option.orelse_eq' h1) with h2 h2; [left,right];
    apply sub_occurs_of_sub_terms_eq; assumption
  end
| (p ∧* q) h1 := 
  begin
    cases (option.orelse_eq' h1) with h2 h2; [left,right];
    apply sub_occurs_of_sub_terms_eq; assumption
  end

lemma sub_count_sub_subst_le {x y z : preterm} :
  ∀ r : form, z.sub_count ≤ 1 → 
  sub_count (sub_subst x y z r) ≤ sub_count r 
| (t =* s) h1 := 
  begin
    simp only [sub_subst, sub_count], apply add_le_add; 
    apply preterm.sub_count_sub_subst_le; assumption,
  end
| (t ≤* s) h1 := 
  begin
    simp only [sub_subst, sub_count], apply add_le_add; 
    apply preterm.sub_count_sub_subst_le; assumption,
  end
| (¬* p)   h1 := sub_count_sub_subst_le p h1
| (p ∨* q) h1 := 
  begin
    simp only [sub_subst, sub_count], apply add_le_add; 
    apply sub_count_sub_subst_le; assumption
  end
| (p ∧* q) h1 := 
  begin
    simp only [sub_subst, sub_count], apply add_le_add; 
    apply sub_count_sub_subst_le; assumption
  end


open tactic

lemma sub_count_sub_subst_lt {x y z : preterm} :
  ∀ r : form, z.sub_count = 0 → sub_occurs x y r → 
  sub_count (sub_subst x y z r) < sub_count r 
| (t =* s) h1 h2 := 
  begin
    apply nat.add_lt_add_of_le_of_le_of_lt_or_lt,
    repeat { apply preterm.sub_count_sub_subst_le, 
      rw h1, exact_dec_trivial },
    apply or_of_or _ _ h2,
    repeat {apply preterm.sub_count_sub_subst_lt _ h1},
  end
| (t ≤* s) h1 h2 := 
  begin
    apply nat.add_lt_add_of_le_of_le_of_lt_or_lt,
    repeat { apply preterm.sub_count_sub_subst_le, 
      rw h1, exact_dec_trivial },
    apply or_of_or _ _ h2,
    repeat {apply preterm.sub_count_sub_subst_lt _ h1},
  end
| (¬* p) h1 h2 := sub_count_sub_subst_lt p h1 h2
| (p ∨* q) h1 h2 :=
  begin
    apply nat.add_lt_add_of_le_of_le_of_lt_or_lt,
    repeat { apply sub_count_sub_subst_le, 
      rw h1, exact_dec_trivial },
    apply or_of_or _ _ h2,
    repeat {apply sub_count_sub_subst_lt _ h1},
  end
| (p ∧* q) h1 h2 :=
  begin
    apply nat.add_lt_add_of_le_of_le_of_lt_or_lt,
    repeat { apply sub_count_sub_subst_le, 
      rw h1, exact_dec_trivial },
    apply or_of_or _ _ h2,
    repeat {apply sub_count_sub_subst_lt _ h1},
  end

lemma sub_count_sub_equiv_lt {t s p} :
  sub_terms p = some (t, s) → 
  sub_count (sub_equiv t s p) < sub_count p :=
begin
  intros h1, simp only [sub_equiv, sub_count],
  have h2 : t.sub_count = 0 := sorry,
  have h3 : s.sub_count = 0 := sorry,
  simp only [preterm.sub_count, h2, h3, zero_add, add_zero],
  apply sub_count_sub_subst_lt; try {assumption}, refl,
  apply sub_occurs_of_sub_terms_eq _ h1
end

#exit
lemma sub_free_sub_elim_core : 
  ∀ m p, sub_count p ≤ m → (sub_elim_core m p).sub_free 
| 0 p h1 := 
  begin 
    apply sub_free_of_sub_count_zero,
    simp only [sub_elim_core], 
    cases (sub_count p), refl, cases h1,
  end
| (m+1) p h1 := 
  begin
    simp only [sub_elim_core],
    cases h2 : (sub_terms p) with ts, 
    { rw [← option.is_none_iff_eq_none',
      sub_terms_is_none'] at h2, apply h2 },
    { cases ts with t s, 
      apply sub_free_sub_elim_core m (sub_equiv t s p),
      rw ← lt_succ_iff, 
      apply lt_of_lt_of_le (sub_count_sub_equiv_lt h2) h1 }
  end

def sub_elim (p : form) : form := 
sub_elim_core (sub_count p) p

lemma sub_free_sub_elim {p} : 
  (sub_elim p).sub_free :=
begin
  simp only [sub_elim], 
  apply sub_free_sub_elim_core,
  apply le_refl,
end

lemma neg_free_sub_elim : ∀ p, neg_free p → neg_free (sub_elim p) := sorry



end nat