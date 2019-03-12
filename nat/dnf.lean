import .sub_elim ..polytope

namespace nat

@[omega] def dnf_core : form → list polytope 
| (p ∨* q) := (dnf_core p) ++ (dnf_core q)
| (p ∧* q) := 
  (list.product (dnf_core p) (dnf_core q)).map (λ pq, pq.fst ++ pq.snd)
| (t =* s) := 
  [[term.sub (canonize s) (canonize t),
    term.sub (canonize t) (canonize s)]]
| (t ≤* s) := [[term.sub (canonize s) (canonize t)]]
| (¬* _)   := []

lemma exists_polytope_holds_core {v} : 
  ∀ {p : form}, p.neg_free → p.sub_free → p.holds v → 
  ∃ c ∈ (dnf_core p), polytope.holds (λ x, ↑(v x)) c := 
begin
  form.induce `[intros h1 h0 h2],
  { apply list.exists_mem_cons_of, 
    simp only [polytope.holds], rw list.forall_mem_cons, constructor,
    { cases h0 with ht hs,
      simp_omega [val_canonize ht, val_canonize hs] at *, 
      rw [h2, sub_self] },
    { rw list.forall_mem_singleton, cases h0 with ht hs,
      simp_omega [val_canonize ht, val_canonize hs] at *, 
      rw [h2, sub_self] } }, --
  { apply list.exists_mem_cons_of, 
    simp only [polytope.holds], rw list.forall_mem_singleton,
    simp_omega [val_canonize h0.left, val_canonize h0.right] at *, 
    rw [le_sub, sub_zero, int.coe_nat_le], assumption },
  { cases h1 },
  { cases h2 with h2 h2;
    [ {cases (ihp h1.left h0.left h2) with c h3},
      {cases (ihq h1.right h0.right h2) with c h3}];
    cases h3 with h3 h4; 
    refine ⟨c, list.mem_append.elim_right _, h4⟩;
    [left,right]; assumption }, 
  { rcases (ihp h1.left h0.left h2.left) with ⟨cp, hp1, hp2⟩,  
    rcases (ihq h1.right h0.right h2.right) with ⟨cq, hq1, hq2⟩, 
    constructor, constructor,
    simp_omega, rw list.mem_map, 
    constructor, constructor, 
    rw list.mem_product, constructor; assumption, refl,
    simp only [polytope.holds, list.forall_mem_append],
    apply and.intro hp2 hq2 }
end


def term.vars_core (is : list int) : list bool := 
is.map (λ i, if i = 0 then ff else tt)

def term.vars (t : term) : list bool := 
term.vars_core t.coeffs

def bools.or : list bool → list bool → list bool 
| []        bs2       := bs2 
| bs1       []        := bs1 
| (b1::bs1) (b2::bs2) := (b1 || b2)::(bools.or bs1 bs2)

def polytope.vars : polytope → list bool 
| []      := [] 
| (t::ts) := bools.or (term.vars t) (polytope.vars ts)

def nonneg_consts_core : nat → list bool → list term 
| _ [] := [] 
| k (ff::bs) := nonneg_consts_core (k+1) bs 
| k (tt::bs) := ⟨0, []{k ↦ 1}⟩::nonneg_consts_core (k+1) bs 

def nonneg_consts (bs : list bool) : list term :=
nonneg_consts_core 0 bs

def nonnegate (ts : polytope) : polytope := 
nonneg_consts (polytope.vars ts) ++ ts

def dnf (p : form) : list polytope := 
(dnf_core p).map nonnegate

lemma holds_nonneg_consts_core {v : nat → int} (h1 : ∀ x, 0 ≤ v x) :
  ∀ m bs, polytope.holds v (nonneg_consts_core m bs) 
| _ []       := λ _ h2, by cases h2
| k (ff::bs) := holds_nonneg_consts_core (k+1) bs
| k (tt::bs) :=
  begin
    apply list.forall_mem_cons_of,
    { simp_omega [one_mul], apply h1 },
    { apply holds_nonneg_consts_core (k+1) bs }
  end

lemma holds_nonneg_consts {v : nat → int} {bs} : 
  (∀ x, 0 ≤ v x) → polytope.holds v (nonneg_consts bs) | h1 := 
by apply holds_nonneg_consts_core h1

lemma exists_polytope_holds {v} {p : form} : 
  p.neg_free → p.sub_free → p.holds v → 
  ∃ c ∈ (dnf p), polytope.holds (λ x, ↑(v x)) c := 
begin
  intros h1 h2 h3, 
  rcases (exists_polytope_holds_core h1 h2 h3) with ⟨c,h4,h5⟩,
  existsi (nonnegate c),
  have h6 : nonnegate c ∈ dnf p, 
  { simp only [dnf], rw list.mem_map, 
    refine ⟨c,h4,rfl⟩ }, refine ⟨h6,_⟩, 
  simp only [nonnegate, polytope.holds],
  rw list.forall_mem_append, 
  apply and.intro (holds_nonneg_consts _) h5,
  apply int.coe_nat_nonneg
end

lemma exists_polytope_sat {p : form} : 
  p.neg_free → p.sub_free →  
  p.sat → ∃ c ∈ (dnf p), polytope.sat c := 
begin
  intros h1 h2 h3, cases h3 with v h3,
  rcases (exists_polytope_holds h1 h2 h3) with ⟨c,h4,h5⟩,
  refine ⟨c,h4,_,h5⟩
end

lemma unsat_of_unsat_dnf (p : form) : 
  p.neg_free → p.sub_free → polytopes.unsat (dnf p) → p.unsat := 
begin
  intros hnf hsf h1 h2, apply h1, 
  apply exists_polytope_sat hnf hsf h2
end

end nat