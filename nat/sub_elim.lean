import .form ..list

namespace nat

namespace preterm

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

def sub_terms : form → option (preterm × preterm)
| (t =* s) := t.sub_terms <|> s.sub_terms
| (t ≤* s) := t.sub_terms <|> s.sub_terms
| (¬* p)   := p.sub_terms
| (p ∨* q) := p.sub_terms <|> q.sub_terms
| (p ∧* q) := p.sub_terms <|> q.sub_terms

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

def sub_subst (x y z : preterm) : form → form 
| (t =* s) := preterm.sub_subst x y z t =* preterm.sub_subst x y z s
| (t ≤* s) := preterm.sub_subst x y z t ≤* preterm.sub_subst x y z s
| (¬* p)   := ¬* p.sub_subst
| (p ∨* q) := p.sub_subst ∨* q.sub_subst
| (p ∧* q) := p.sub_subst ∧* q.sub_subst

end form 

open form 


def sub_equiv (t s) (p : form) : form := 
let m := p.fresh_idx in
let r := 1 ** m in
(sub_subst t s r p) ∧* 
((t =* (s +* r)) ∨* (t ≤* s ∧* (r =* &0))) 

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


lemma unsat_of_unsat_sub_elim {p : form} :
  (sub_elim p).unsat → p.unsat := sorry

end nat