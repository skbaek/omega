import .form

namespace nat

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

@[omega] def neg_elim_core : form → form 
| (¬* (t =* s)) := (t.succ ≤* s) ∨* (s.succ ≤* t)
| (¬* (t ≤* s)) := s.succ ≤* t
| (p ∨* q) := (neg_elim_core p) ∨* (neg_elim_core q)
| (p ∧* q) := (neg_elim_core p) ∧* (neg_elim_core q)
| p        := p

lemma neg_free_neg_elim_core : ∀ p, is_nnf p → (neg_elim_core p).neg_free := 
begin
  form.induce `[intro h1, try {simp only [neg_free, neg_elim_core]}, try {trivial}],
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

lemma implies_neg_elim_core : ∀ {p : form}, form.implies p (neg_elim_core p) :=
begin
  form.induce `[intros v h, try {apply h}],
  { cases p with t s t s; try {apply h},
    { simp_omega [le_and_le_iff_eq.symm, 
        classical.not_and_distrib, not_le] at h,
      simp_omega [int.add_one_le_iff], rw or.comm, assumption },
    { simp_omega [not_le, int.add_one_le_iff] at *, assumption} },
  { simp only [neg_elim_core], cases h; [{left, apply ihp}, 
    {right, apply ihq}]; assumption }, 
  { apply and_of_and (ihp _) (ihq _) h }
end

def neg_elim : form → form := neg_elim_core ∘ nnf

lemma neg_free_neg_elim {p} : (neg_elim p).neg_free := 
neg_free_neg_elim_core _ (is_nnf_nnf _)

lemma implies_neg_elim {p : form} : form.implies p (neg_elim p) :=
begin
  intros v h1, apply implies_neg_elim_core,
  apply (nnf_equiv v).elim_right h1
end

end nat