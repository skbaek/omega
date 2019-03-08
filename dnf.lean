import .form .polytope

@[omega] def push_neg : form → form 
| (p ∨* q) := (push_neg p) ∧* (push_neg q)
| (p ∧* q) := (push_neg p) ∨* (push_neg q)
| (¬*p)    := p
| p        := ¬* p

lemma push_neg_equiv : 
  ∀ {p}, form.equiv (push_neg p) (¬* p) :=
begin
  form.induce `[intros v; try {refl}], 
  { simp_omega [classical.not_not] },
  { simp only [form.holds, push_neg, not_or_distrib, ihp v, ihq v] },
  { simp only [form.holds, push_neg, classical.not_and_distrib, ihp v, ihq v] }
end

def nnf : form → form 
| (¬* p)   := push_neg (nnf p)
| (p ∨* q) := (nnf p) ∨* (nnf q)
| (p ∧* q) := (nnf p) ∧* (nnf q)
| a        := a

def is_nnf : form → Prop 
| (t =* s) := true
| (t ≤* s) := true
| ¬*(t =* s) := true
| ¬*(t ≤* s) := true
| (p ∨* q) := is_nnf p ∧ is_nnf q
| (p ∧* q) := is_nnf p ∧ is_nnf q
| _ := false

lemma is_nnf_push_neg : ∀ p, is_nnf p → is_nnf (push_neg p) :=
begin
  form.induce `[intro h1; try {trivial}],
  { cases p; try {cases h1}; trivial },
  { cases h1, constructor; [{apply ihp}, {apply ihq}]; assumption },
  { cases h1, constructor; [{apply ihp}, {apply ihq}]; assumption }
end

def is_nf : form → Prop 
| (t =* s) := true
| (t ≤* s) := true
| (p ∨* q) := is_nf p ∧ is_nf q
| (p ∧* q) := is_nf p ∧ is_nf q
| _        := false

lemma is_nnf_nnf : ∀ p, is_nnf (nnf p) := 
begin
  form.induce `[try {trivial}],
  { apply is_nnf_push_neg _ ih },
  { constructor; assumption },
  { constructor; assumption }
end

lemma nnf_equiv : ∀ {p : form}, form.equiv (nnf p) p :=
begin
  form.induce `[intros v; try {refl}; simp only [nnf]], 
  { rw push_neg_equiv,
    apply not_iff_not_of_iff, apply ih },
  { apply or_iff_or (ihp v) (ihq v) },
  { apply and_iff_and (ihp v) (ihq v) }
end

@[omega] def nf : form → form 
| (¬* (t =* s)) := (t.succ ≤* s) ∨* (s.succ ≤* t)
| (¬* (t ≤* s)) := s.succ ≤* t
| (p ∨* q) := (nf p) ∨* (nf q)
| (p ∧* q) := (nf p) ∧* (nf q)
| p        := p

lemma is_nf_nf : ∀ p, is_nnf p → is_nf (nf p) := 
begin
  form.induce `[intro h1, try {simp only [is_nf, nf]}, try {trivial}],
  { cases p; try {cases h1}; try {trivial},
    constructor; trivial },
  { cases h1, constructor; [{apply ihp}, {apply ihq}]; assumption },
  { cases h1, constructor; [{apply ihp}, {apply ihq}]; assumption }
end

lemma le_and_le_iff_eq {α : Type} [partial_order α] {a b : α} : 
  (a ≤ b ∧ b ≤ a) ↔ a = b := 
begin
  constructor; intro h1,
  { cases h1, apply le_antisymm; assumption },
  { constructor; apply le_of_eq; rw h1  }
end

lemma implies_nf : ∀ {p : form}, form.implies p (nf p) :=
begin
  form.induce `[intros v h, try {apply h}],
  { cases p with t s t s; try {apply h},
    { simp_omega [le_and_le_iff_eq.symm, 
        classical.not_and_distrib, not_le] at h,
      simp_omega [int.add_one_le_iff], rw or.comm, assumption },
    { simp_omega [not_le, int.add_one_le_iff] at *, assumption} },
  { simp only [nf], cases h; [{left, apply ihp}, 
    {right, apply ihq}]; assumption }, 
  { apply and_of_and (ihp _) (ihq _) h }
end

@[omega] def dnf_core : form → list polytope 
| (p ∨* q) := (dnf_core p) ++ (dnf_core q)
| (p ∧* q) := 
  (list.product (dnf_core p) (dnf_core q)).map (λ pq, pq.fst ++ pq.snd)
| (t =* s) := 
  [[term.sub (canonize s) (canonize t),
    term.sub (canonize t) (canonize s)]]
| (t ≤* s) := [[term.sub (canonize s) (canonize t)]]
| (¬* _)   := []

def dnf (p : form) : list polytope := 
dnf_core $ nf $ nnf p

lemma exists_polytope_holds {v} : 
  ∀ {p : form}, is_nf p → p.holds v → ∃ c ∈ (dnf_core p), polytope.holds v c := 
begin
  form.induce `[intros h1 h2],
  { apply list.exists_mem_cons_of, --constructor, 
    simp only [polytope.holds], rw list.forall_mem_cons, constructor,
    { simp_omega at *, rw [h2, sub_self] },
    { rw list.forall_mem_singleton, simp_omega at *, rw [h2, sub_self] } },
  { apply list.exists_mem_cons_of, 
    simp only [polytope.holds], rw list.forall_mem_singleton,
    simp_omega at *, rw [le_sub, sub_zero], assumption },
    { cases h1 },
    { cases h2 with h2 h2;
      [ {cases (ihp h1.left h2) with c h3},
        {cases (ihq h1.right h2) with c h3}];
      cases h3 with h3 h4; 
      refine ⟨c, list.mem_append.elim_right _, h4⟩;
      [left,right]; assumption }, 
    { rcases (ihp h1.left h2.left) with ⟨cp, hp1, hp2⟩,  
      rcases (ihq h1.right h2.right) with ⟨cq, hq1, hq2⟩, 
      constructor, constructor,
      simp_omega, rw list.mem_map, 
      constructor, constructor, 
      rw list.mem_product, constructor; assumption, refl,
      simp only [polytope.holds, list.forall_mem_append],
      apply and.intro hp2 hq2 }
end

lemma exists_polytope_sat {p : form} : 
  is_nf p → p.sat → ∃ c ∈ (dnf_core p), polytope.sat c := 
begin
  intros h1 h2, cases h2 with v h2,
  rcases (exists_polytope_holds h1 h2) with ⟨c,h3,h4⟩,
  refine ⟨c,h3,v,h4⟩
end

lemma form_unsat_of_polytopes_unsat {p : form} : 
polytopes.unsat (dnf p) → p.unsat := 
begin
  intros h1 h2, 
  dsimp only [polytopes.unsat] at h1,
  rw ← list.not_exists_mem_not at h1,
  apply h1, 
  simp only [polytope.unsat, classical.not_not], 
  apply exists_polytope_sat (is_nf_nf _ (is_nnf_nnf _)),
  apply form.sat_of_implies_of_sat implies_nf,
  have hrw := exists_iff_exists (@nnf_equiv p),
  apply hrw.elim_right h2
end


