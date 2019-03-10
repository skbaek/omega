import .sat

@[omega] def comb : list term → list nat → term 
| [] []     := ⟨0,[]⟩ 
| [] (_::_) := ⟨0,[]⟩ 
| (_::_) [] := ⟨0,[]⟩ 
| (t::ts) (n::ns) := term.add (t.mul ↑n) (comb ts ns)

lemma comb_holds {v} :
  ∀ {ts} ns, (∀ t ∈ ts, 0 ≤ term.val v t) → (0 ≤ (comb ts ns).val v) 
| [] []     h := by simp_omega
| [] (_::_) h := by simp_omega
| (_::_) [] h := by simp_omega
| (t::ts) (n::ns) h :=
  begin
    simp_omega, apply add_nonneg, 
    { apply mul_nonneg,
      apply int.coe_nat_nonneg,
      apply h _ (or.inl rfl) },
    { apply comb_holds, 
      apply list.forall_mem_of_forall_mem_cons h }
  end

def unsat_comb (ts ns) : Prop :=
let t := comb ts ns in 
if t.const < 0 ∧ ∀ x ∈ t.coeffs, x = (0 : int)
then true
else false

lemma unsat_of_unsat_comb {eqs les : list term} (ns : list nat) :
  (unsat_comb les ns) → unsat eqs les :=
begin
  intros h1 h2, cases h2 with v h2, 
  have h3 := comb_holds ns h2.right,
  by_cases h4 : (comb les ns).const < 0 ∧ 
             ∀ x ∈ (comb les ns).coeffs, x = (0 : int),
  { cases h4 with hl hr, 
    cases (comb les ns) with b as,
    simp_omega at h3, 
    rw [val_aux_eq_zero hr, add_zero, ← not_lt] at h3,
    apply h3 hl },
  { simp only [unsat_comb] at h1, 
    rw if_neg h4 at h1, exact h1 }
end


  #exit
begin
  intros h1 h2, simp only [correct] at h1,
  cases h3 : comb_core ts p with t; rw h3 at h1, 
  { cases h1 }, 
  { simp at h1, cases h2 with v h2, 
    have h5 := holds_comb h2 p _ h3, 
    cases t with b as, simp_omega at h5,
    rw [val_aux_eq_zero h1.right, add_zero, ← not_lt] at h5, 
    apply h5 (int.neg_of_negative h1.left) }
end



#exit
def correct (ts is) : Prop :=
@option.rec_on _ (λ _, Prop) (comb_core ts p) false 
(λ t, if t.const.negative ∧ (∀ x ∈ t.coeffs, x = (0 : int))
      then true
      else false)

      #exit
@[derive has_reflect]
inductive proof : Type 
| hyp   : nat → proof 
| mul   : nat → proof → proof 
| elim  : proof → proof → proof 

-- | (proof.hyp m) :=
-- | (proof.mul m p) :=
-- | (proof.elim m p1 p2) := 

def olc_rec : option term → (term → option term) → option term 
| none      f := none 
| (some lc) f := f lc

lemma olc_rec_some (lc : term) (f) :
  olc_rec (some lc) f = f lc := by refl 

def comb_core (lcs : list term) : proof → option term 
| (proof.hyp k)   := lcs.nth k
| (proof.mul k p) := 
  do lc ← comb_core p | none, some (lc.mul ↑k)
| (proof.elim p1 p2) := 
   do t1 ← comb_core p1, 
      t2 ← comb_core p2, 
      (some (term.add t1 t2))

def int.negative : int → Prop 
| (int.of_nat _) := false
| -[1+ _]        := true

lemma int.neg_of_negative {i : int} :
  i.negative → i < 0 :=
begin
  cases i with m m; intro h1, cases h1,
  cases m with m; tactic.exact_dec_trivial
end

instance int.decidable_negative : ∀ i : int, decidable i.negative 
| (int.of_nat _) := decidable.false
| -[1+ _]        := decidable.true


lemma holds_comb {v lcs} (h0 : polytope.holds v lcs) : 
  ∀ p t, comb_core lcs p = some t → 0 ≤ t.val v 
| (proof.hyp m) t h1 := h0 _ (list.nth_mem h1)
| (proof.mul m p) t h1 :=
  begin
    simp only [comb_core] at h1,
    cases h3 : (comb_core lcs p) with s; rw h3 at h1,
    { cases h1 },
    { have h4 := holds_comb p s h3,
      simp at h1, subst h1, simp only [term.val_mul],
      apply int.mul_nonneg (int.coe_nat_nonneg _) h4 }
  end
| (proof.elim p1 p2) t h1 :=
  begin
    simp only [comb_core] at h1,
    cases h3 : (comb_core lcs p1) with s; rw h3 at h1, cases h1,
    cases h4 : (comb_core lcs p2) with u; rw h4 at h1, cases h1,
    cases h1, rw term.val_add,
    apply add_nonneg (holds_comb p1 s h3) (holds_comb p2 u h4), 
  end

lemma unsat_nil {t : term} :
  false → 
  polytope.unsat ([] : polytope) := λ h1, by cases h1

lemma unsat_zero_le_neg {t : term} :
  t.const < 0 → (∀ x : int, x ∈ t.coeffs → x = 0) → 
  polytope.unsat ([t] : polytope) :=
begin
  intros h1 h2 h3, cases h3 with v h3,
  have h4 := h3 _ (or.inl rfl),
  cases t with c cfs,
  simp only [term.val] at h4,
  rw (val_aux_eq_zero h2) at h4,
  simp at h4,
  rw ← not_le at h1, apply (h1 h4),
end

def comb (lcs : list term) (p : proof) : list term :=
option.rec_on (comb_core lcs p) ([] : list term) (λ t, [t])

lemma unsat_of_unsat_comb {ts : list term} (p : proof) :
  polytope.unsat (comb ts p) → polytope.unsat ts := 
begin
  intros h1 h2, apply h1, cases h2 with v h2, refine ⟨v,_⟩, 
  simp only [comb], cases h3 : comb_core ts p, 
  apply list.forall_mem_nil, simp [polytope.holds],
  apply holds_comb h2 _ _ h3,
end

lemma unsat_of_correct {ts : list term} (p : proof) :
  correct ts p → polytope.unsat ts :=
begin
  intros h1 h2, simp only [correct] at h1,
  cases h3 : comb_core ts p with t; rw h3 at h1, 
  { cases h1 }, 
  { simp at h1, cases h2 with v h2, 
    have h5 := holds_comb h2 p _ h3, 
    cases t with b as, simp_omega at h5,
    rw [val_aux_eq_zero h1.right, add_zero, ← not_lt] at h5, 
    apply h5 (int.neg_of_negative h1.left) }
end