import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1380

section Matching

variable {A B : Type} [DecidableEq A] [DecidableEq B]

def IsMatching (P : A → B → Prop) (M : Finset (A × B)) : Prop :=
  Set.InjOn Prod.fst (↑M : Set (A × B)) ∧ Set.InjOn Prod.snd (↑M : Set (A × B)) ∧
    ∀ e ∈ M, P e.1 e.2

def left (M : Finset (A × B)) : Finset (A ⊕ B) := M.image (fun e => Sum.inl e.1)
def right (M : Finset (A × B)) : Finset (A ⊕ B) := M.image (fun e => Sum.inr e.2)
def support (M : Finset (A × B)) : Finset (A ⊕ B) := left M ∪ right M

@[simp] theorem inl_support {a : A} {M : Finset (A × B)} :
    Sum.inl a ∈ support M ↔ ∃ e ∈ M, e.1 = a := by
  simp [support, left, right, Finset.mem_image]

@[simp] theorem inr_support {b : B} {M : Finset (A × B)} :
    Sum.inr b ∈ support M ↔ ∃ e ∈ M, e.2 = b := by
  simp [support, left, right, Finset.mem_image]

theorem support_card {P : A → B → Prop} {M : Finset (A × B)} (h : IsMatching P M) :
    (support M).card = 2*M.card := by
  have hl : (left M).card = M.card := Finset.card_image_of_injOn (fun _ hx _ hy he => h.1 hx hy (Sum.inl.inj he))
  have hr : (right M).card = M.card := Finset.card_image_of_injOn (fun _ hx _ hy he => h.2.1 hx hy (Sum.inr.inj he))
  have hd : Disjoint (left M) (right M) := by
    rw [Finset.disjoint_left]
    intro v hv hw
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨f, _, h⟩ := Finset.mem_image.mp hw
    cases h
  rw [support, Finset.card_union_of_disjoint hd, hl, hr]
  omega

theorem exclusive_edge {P : A → B → Prop} {M N : Finset (A × B)} (hM : IsMatching P M)
    (h : ((support M) ∩ (support N)).card < M.card) :
    ∃ e ∈ M, Sum.inl e.1 ∉ support N ∧ Sum.inr e.2 ∉ support N := by
  classical
  by_contra! bad
  let choice : A × B → A ⊕ B := fun e =>
    if Sum.inl e.1 ∈ support N then Sum.inl e.1 else Sum.inr e.2
  have hinj : Set.InjOn choice (↑M : Set (A × B)) := by
    intro e he f hf eq
    by_cases el : Sum.inl e.1 ∈ support N <;> by_cases fl : Sum.inl f.1 ∈ support N
    · exact hM.1 he hf (Sum.inl.inj (by simpa only [choice, if_pos el, if_pos fl] using eq))
    · simp only [choice, if_pos el, if_neg fl, Sum.inl_ne_inr] at eq
    · simp only [choice, if_neg el, if_pos fl, Sum.inr_ne_inl] at eq
    · exact hM.2.1 he hf (Sum.inr.inj (by simpa only [choice, if_neg el, if_neg fl] using eq))
  have sub : M.image choice ⊆ support M ∩ support N := by
    intro v hv
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hv
    rw [Finset.mem_inter]
    by_cases yes : Sum.inl e.1 ∈ support N
    · simp only [choice, if_pos yes]
      exact ⟨inl_support.mpr ⟨e, he, rfl⟩, yes⟩
    · have no := bad e he yes
      simp only [choice, if_neg yes]
      exact ⟨inr_support.mpr ⟨e, he, rfl⟩, no⟩
  have count := Finset.card_le_card sub
  rw [Finset.card_image_of_injOn hinj] at count
  omega

theorem replace_edge {P : A → B → Prop} {M : Finset (A × B)} {old new : A × B}
    (hM : IsMatching P M) (hold : old ∈ M) (hnew : P new.1 new.2)
    (hf : ∀ f ∈ M.erase old, f.1 ≠ new.1 ∧ f.2 ≠ new.2) :
    IsMatching P (insert new (M.erase old)) ∧ (insert new (M.erase old)).card = M.card := by
  have hnot : new ∉ M.erase old := fun h => (hf new h).1 rfl
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro e he f hff eq
    rcases Finset.mem_insert.mp he with hen | he' <;> rcases Finset.mem_insert.mp hff with hfn | hf'
    · exact hen.trans hfn.symm
    · subst e
      exact False.elim ((hf f hf').1 eq.symm)
    · subst f
      exact False.elim ((hf e he').1 eq)
    · exact hM.1 (Finset.mem_of_mem_erase he') (Finset.mem_of_mem_erase hf') eq
  · intro e he f hff eq
    rcases Finset.mem_insert.mp he with hen | he' <;> rcases Finset.mem_insert.mp hff with hfn | hf'
    · exact hen.trans hfn.symm
    · subst e
      exact False.elim ((hf f hf').2 eq.symm)
    · subst f
      exact False.elim ((hf e he').2 eq)
    · exact hM.2.1 (Finset.mem_of_mem_erase he') (Finset.mem_of_mem_erase hf') eq
  · intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact hnew
    · exact hM.2.2 e (Finset.mem_of_mem_erase he)
  · rw [Finset.card_insert_of_notMem hnot, Finset.card_erase_add_one hold]

theorem overlap_persists {M N : Finset (A × B)} {old new : A × B}
    (ha : Sum.inl old.1 ∉ support N) (hb : Sum.inr old.2 ∉ support N) :
    support M ∩ support N ⊆ support (insert new (M.erase old)) ∩ support N := by
  intro v hv
  obtain ⟨hm, hn⟩ := Finset.mem_inter.mp hv
  refine Finset.mem_inter.mpr ⟨?_, hn⟩
  cases v with
  | inl a =>
    obtain ⟨e, he, rfl⟩ := inl_support.mp hm
    have hd : e ≠ old := fun h => ha (h ▸ hn)
    exact inl_support.mpr ⟨e, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hd, he⟩), rfl⟩
  | inr b =>
    obtain ⟨e, he, rfl⟩ := inr_support.mp hm
    have hd : e ≠ old := fun h => hb (h ▸ hn)
    exact inr_support.mpr ⟨e, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hd, he⟩), rfl⟩

theorem matching_pair [Fintype A] [Fintype B] (color : A → B → Bool) (q : Nat)
    (hred : ∃ M : Finset (A × B), M.card = q ∧ IsMatching (fun a b => color a b = true) M)
    (hblue : ∃ M : Finset (A × B), M.card = q ∧ IsMatching (fun a b => color a b = false) M) :
    ∃ R T : Finset (A × B), R.card = q ∧ T.card = q ∧
      IsMatching (fun a b => color a b = true) R ∧ IsMatching (fun a b => color a b = false) T ∧
      (support R ∪ support T).card ≤ 3*q := by
  classical
  let candidates : Finset (Finset (A × B) × Finset (A × B)) := Finset.univ.filter fun p =>
    p.1.card = q ∧ p.2.card = q ∧
    IsMatching (fun a b => color a b = true) p.1 ∧ IsMatching (fun a b => color a b = false) p.2
  let score : Finset (A × B) × Finset (A × B) → Nat := fun p => (support p.1 ∩ support p.2).card
  have nonempty : candidates.Nonempty := by
    obtain ⟨R, hR, hr⟩ := hred
    obtain ⟨T, hT, ht⟩ := hblue
    exact ⟨(R,T), by simp [candidates, hR, hT, hr, ht]⟩
  obtain ⟨⟨R,T⟩, ok, max_score⟩ := Finset.exists_max_image candidates score nonempty
  have ⟨hR,hT,hr,ht⟩ : R.card = q ∧ T.card = q ∧
      IsMatching (fun a b => color a b = true) R ∧ IsMatching (fun a b => color a b = false) T := by
    simpa [candidates] using ok
  refine ⟨R,T,hR,hT,hr,ht, ?_⟩
  have count := Finset.card_union_add_card_inter (support R) (support T)
  rw [support_card hr, support_card ht, hR, hT] at count
  by_contra! large
  have hsmall : (support R ∩ support T).card < q := by omega
  obtain ⟨r, rmem, ra, rb⟩ := exclusive_edge hr (by simpa [hR] using hsmall)
  obtain ⟨t, tmem, ta, tb⟩ := exclusive_edge (N := R) ht (by rwa [hT, Finset.inter_comm])
  let cross := (r.1,t.2)
  by_cases red_cross : color r.1 t.2 = true
  · let U := insert cross (R.erase r)
    have fresh : ∀ f ∈ R.erase r, f.1 ≠ cross.1 ∧ f.2 ≠ cross.2 := by
      intro f hf
      refine ⟨?_, ?_⟩
      · intro h
        exact (Finset.mem_erase.mp hf).1 (hr.1 (Finset.mem_of_mem_erase hf) rmem h)
      · intro h
        exact tb (inr_support.mpr ⟨f, Finset.mem_of_mem_erase hf, h⟩)
    have ⟨hU, hUc⟩ := replace_edge hr rmem red_cross fresh
    have member : (U,T) ∈ candidates := by simp [candidates, U, hU, hUc, hR, hT, ht]
    have bigger : insert (Sum.inr t.2) (support R ∩ support T) ⊆ support U ∩ support T := by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact Finset.mem_inter.mpr ⟨inr_support.mpr ⟨cross, Finset.mem_insert_self _ _, rfl⟩,
          inr_support.mpr ⟨t, tmem, rfl⟩⟩
      · exact overlap_persists ra rb hv
    have c := Finset.card_le_card bigger
    rw [Finset.card_insert_of_notMem (fun h => tb (Finset.mem_inter.mp h).1)] at c
    have le := max_score (U,T) member
    change (support U ∩ support T).card ≤ (support R ∩ support T).card at le
    omega
  · have blue_cross : color r.1 t.2 = false := by cases h : color r.1 t.2 <;> simp_all
    let U := insert cross (T.erase t)
    have fresh : ∀ f ∈ T.erase t, f.1 ≠ cross.1 ∧ f.2 ≠ cross.2 := by
      intro f hf
      refine ⟨?_, ?_⟩
      · intro h
        exact ra (inl_support.mpr ⟨f, Finset.mem_of_mem_erase hf, h⟩)
      · intro h
        exact (Finset.mem_erase.mp hf).1 (ht.2.1 (Finset.mem_of_mem_erase hf) tmem h)
    have ⟨hU, hUc⟩ := replace_edge ht tmem blue_cross fresh
    have member : (R,U) ∈ candidates := by simp [candidates, U, hU, hUc, hT, hR, hr]
    have bigger : insert (Sum.inl r.1) (support R ∩ support T) ⊆ support R ∩ support U := by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact Finset.mem_inter.mpr ⟨inl_support.mpr ⟨r, rmem, rfl⟩,
          inl_support.mpr ⟨cross, Finset.mem_insert_self _ _, rfl⟩⟩
      · rw [Finset.inter_comm] at hv ⊢
        exact overlap_persists ta tb hv
    have c := Finset.card_le_card bigger
    rw [Finset.card_insert_of_notMem (fun h => ra (Finset.mem_inter.mp h).2)] at c
    have le := max_score (R,U) member
    change (support R ∩ support U).card ≤ (support R ∩ support T).card at le
    omega

end Matching

end PEqualNP.Outside.L_lib_1380
namespace PEqualNP.Outside.L_lib_1380

section Ordered

variable {A B : Type} [DecidableEq A] [DecidableEq B]

theorem erase_filter_card {X : Type} [DecidableEq X] (S : Finset X) (x : X) (P : X → Prop)
    [DecidablePred P] (hx : x ∈ S) :
    ((S.erase x).filter P).card + (if P x then 1 else 0) = (S.filter P).card := by
  by_cases hp : P x
  · have hx' : x ∈ S.filter P := Finset.mem_filter.mpr ⟨hx,hp⟩
    have he : (S.erase x).filter P = (S.filter P).erase x := by ext y; simp [and_assoc]
    simpa [he, hp] using Finset.card_erase_add_one hx'
  · have he : (S.erase x).filter P = S.filter P := by
      ext y
      by_cases hy : y=x
      · subst y
        simp [hp]
      · simp [hy]
    simp [he,hp]

theorem ordered_matching (leftRow : A → Nat) (rightRow : B → Nat) (N : Nat)
    (q : Nat) (L : Finset A) (R : Finset B)
    (hL : ∀ a ∈ L, leftRow a < N) (hR : ∀ b ∈ R, rightRow b < N)
    (distinct : ∀ a ∈ L, ∀ b ∈ R, leftRow a ≠ rightRow b)
    (caps : ∀ k ≤ N, q ≤ (L.filter (fun a => leftRow a < k)).card +
      (R.filter (fun b => k ≤ rightRow b)).card) :
    ∃ M : Finset (A × B), M.card = q ∧
      IsMatching (fun a b => leftRow a < rightRow b) M ∧ ∀ e ∈ M, e.1 ∈ L ∧ e.2 ∈ R := by
  classical
  induction q generalizing L R with
  | zero => exact ⟨∅, by simp [IsMatching, Set.InjOn]⟩
  | succ q ih =>
    have nonempty : L.Nonempty := by
      by_contra! h
      have hzero : R.filter (fun b => N ≤ rightRow b) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro b hb
        obtain ⟨hb,hb'⟩ := Finset.mem_filter.mp hb
        have := hR b hb
        omega
      have bound := caps N (Nat.le_refl _)
      simp [h, hzero] at bound
    obtain ⟨a, ha, hamin⟩ := Finset.exists_min_image L leftRow nonempty
    let admissible := R.filter (fun b => leftRow a ≤ rightRow b)
    have zero : L.filter (fun a' => leftRow a' < leftRow a) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro a' hx
      obtain ⟨hx,hlt⟩ := Finset.mem_filter.mp hx
      exact (Nat.not_lt_of_ge (hamin a' hx)) hlt
    have size : q+1 ≤ admissible.card := by
      have bound := caps (leftRow a) (Nat.le_of_lt (hL a ha))
      simpa [admissible,zero] using bound
    obtain ⟨b,hb, hbmin⟩ := Finset.exists_min_image admissible rightRow
      (Finset.card_pos.mp (by omega))
    have hb0 := (Finset.mem_filter.mp hb).1
    have order : leftRow a < rightRow b :=
      lt_of_le_of_ne (Finset.mem_filter.mp hb).2 (distinct a ha b hb0)
    have caps' : ∀ k ≤ N, q ≤ ((L.erase a).filter (fun a' => leftRow a' < k)).card +
        ((R.erase b).filter (fun b' => k ≤ rightRow b')).card := by
      intro k hk
      have h := caps k hk
      have dl := erase_filter_card L a (fun a' => leftRow a' < k) ha
      have dr := erase_filter_card R b (fun b' => k ≤ rightRow b') hb0
      by_cases hl : leftRow a < k <;> by_cases hr : k ≤ rightRow b <;>
        simp only [ite_eq_left, ite_eq_right, hl, hr, if_false, if_true] at dl dr
      · have lpos : 0 < (L.filter (fun a' => leftRow a' < k)).card :=
          Finset.card_pos.mpr ⟨a, Finset.mem_filter.mpr ⟨ha,hl⟩⟩
        have sub : admissible ⊆ R.filter (fun b' => k ≤ rightRow b') := by
          intro b' hmem
          exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hmem).1, hr.trans (hbmin b' hmem)⟩
        have hsub := Finset.card_le_card sub
        omega
      · omega
      · omega
      · omega
    obtain ⟨M, hc, hm, endpoints⟩ := ih (L.erase a) (R.erase b)
      (fun i hi => hL i (Finset.mem_of_mem_erase hi)) (fun i hi => hR i (Finset.mem_of_mem_erase hi))
      (fun i hi j hj => distinct i (Finset.mem_of_mem_erase hi) j (Finset.mem_of_mem_erase hj)) caps'
    have notin : (a,b) ∉ M := fun h => (Finset.mem_erase.mp (endpoints _ h).1).1 rfl
    refine ⟨insert (a,b) M, ?_, ⟨?_,?_,?_⟩, ?_⟩
    · simp [Finset.card_insert_of_notMem notin, hc]
    · intro e he f hf eq
      rcases Finset.mem_insert.mp he with hen | he' <;> rcases Finset.mem_insert.mp hf with hfn | hf'
      · exact hen.trans hfn.symm
      · subst e
        exact False.elim ((Finset.mem_erase.mp (endpoints _ hf').1).1 eq.symm)
      · subst f
        exact False.elim ((Finset.mem_erase.mp (endpoints _ he').1).1 eq)
      · exact hm.1 he' hf' eq
    · intro e he f hf eq
      rcases Finset.mem_insert.mp he with hen | he' <;> rcases Finset.mem_insert.mp hf with hfn | hf'
      · exact hen.trans hfn.symm
      · subst e
        exact False.elim ((Finset.mem_erase.mp (endpoints _ hf').2).1 eq.symm)
      · subst f
        exact False.elim ((Finset.mem_erase.mp (endpoints _ he').2).1 eq)
      · exact hm.2.1 he' hf' eq
    · intro e he
      rcases Finset.mem_insert.mp he with rfl | he
      · exact order
      · exact hm.2.2 e he
    · intro e he
      rcases Finset.mem_insert.mp he with rfl | he
      · exact ⟨ha,hb0⟩
      · exact ⟨Finset.mem_of_mem_erase (endpoints _ he).1, Finset.mem_of_mem_erase (endpoints _ he).2⟩

end Ordered

end PEqualNP.Outside.L_lib_1380
namespace PEqualNP.Outside.L_lib_1380

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)
open PEqualNP.NotBracket (notCount)

def inputsAt (n : Nat) (t : Fin (n+1)) : List Bool :=
  (List.ofFn (fun j : Fin n => decide (j.val < t.val))) ++ [false,true]

theorem prefix_length (n : Nat) (t : Fin (n+1)) : (inputsAt n t).length = n+2 := by
  simp [inputsAt]

theorem prefix_read (n : Nat) (t : Fin (n+1)) (i : Nat) (hi : i < n+2) :
    (inputsAt n t).getD i false = if i<n then decide (i < t.val) else decide (i = n+1) := by
  unfold inputsAt
  have h : (List.ofFn (fun j : Fin n => decide (j.val < t.val))).length = n := by simp
  by_cases lt : i < n
  · have inList : i < (List.ofFn (fun j : Fin n => decide (j.val < t.val))).length := by simpa [h] using lt
    rw [List.getD_append _ _ _ _ inList, if_pos lt]
    rw [List.getD_eq_getElem _ _ inList]
    simp
  · have outside : (List.ofFn (fun j : Fin n => decide (j.val < t.val))).length ≤ i := by simpa [h] using Nat.le_of_not_gt lt
    rw [List.getD_append_right _ _ _ _ outside, h, if_neg lt]
    have cases : i = n ∨ i = n+1 := by omega
    rcases cases with rfl | rfl <;> simp

def fits (n p b s : Nat) (word : Fin (n+1) → Bool) : Prop :=
  ∃ C : Circuit, FanInTwo C ∧ ReadsBack (n+2) C ∧ C.size-notCount C ≤ p ∧
    notCount C ≤ b ∧ C.size ≤ s ∧ C.output < n+2+C.size ∧
    ∀ t, C.eval (inputsAt n t) = word t

def assign (n m : Nat) (f : Nat → Nat) (j : Nat) : Nat :=
  if j < n then f j else m+(j-n)

def relocateGate (n m : Nat) (f : Nat → Nat) (g : Gate) : Gate :=
  ⟨g.op,g.inputs.map (assign n m f)⟩

def relocate (n m : Nat) (f : Nat → Nat) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relocateGate n m f), assign n m f C.output⟩

theorem assign_bound {n m : Nat} {f : Nat → Nat} (hf : ∀ j < n, f j < m)
    {i k : Nat} (h : i < n+k) : assign n m f i < m+k := by
  unfold assign
  split
  · have := hf i ‹i<n›
    omega
  · omega

theorem notCount_relocate (n m : Nat) (f : Nat → Nat) (C : Circuit) :
    notCount (relocate n m f C) = notCount C := by
  simp only [notCount, relocate]
  generalize C.gates = gs
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    change ((relocateGate n m f g :: gs.map (relocateGate n m f)).filter _).length = _
    simp only [List.filter_cons, relocateGate]
    split <;> simp_all

theorem relocate_size (n m : Nat) (f : Nat → Nat) (C : Circuit) :
    (relocate n m f C).size = C.size := by simp [relocate, Circuit.size]

theorem relocate_fanin {n m : Nat} {f : Nat → Nat} {C : Circuit} (h : FanInTwo C) :
    FanInTwo (relocate n m f C) := by
  intro g hg
  change g ∈ C.gates.map (relocateGate n m f) at hg
  obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hg
  simpa only [relocateGate, List.length_map] using h old ho

theorem relocate_reads {n m : Nat} {f : Nat → Nat} {C : Circuit}
    (hf : ∀ j < n, f j < m) (h : ReadsBack n C) : ReadsBack m (relocate n m f C) := by
  intro j hj i hi
  simp only [relocate, List.length_map] at hj
  have mapped : j < (relocate n m f C).gates.length := by simpa [relocate] using hj
  have heq : gateAt (relocate n m f C) j = relocateGate n m f (gateAt C j) := by
    simp only [gateAt, List.getD_eq_getElem _ _ mapped, List.getD_eq_getElem _ _ hj]
    simp [relocate]
  rw [heq] at hi
  obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hi
  exact assign_bound hf (h j hj old ho)

def pushGate (xs : List Bool) (g : Gate) : List Bool :=
  xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]

theorem getD_snoc (xs : List Bool) (x : Bool) (i : Nat) :
    (xs++[x]).getD i false = if i=xs.length then x else xs.getD i false := by
  by_cases h : i<xs.length
  · rw [List.getD_append _ _ _ _ h, if_neg (by omega)]
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_eq_default xs false (Nat.le_of_not_gt h)]
    by_cases he : i=xs.length
    · simp [he]
    · have positive : 0 < i-xs.length := by omega
      rw [if_neg he, List.getD_eq_default [x] false (show [x].length ≤ i-xs.length from positive)]

theorem fold_relocate {n m : Nat} {f : Nat → Nat} (hf : ∀ j < n, f j < m)
    (gs : List Gate) (k : Nat) (xs ys : List Bool)
    (hx : xs.length = n+k) (hy : ys.length = m+k)
    (data : ∀ i, xs.getD i false = ys.getD (assign n m f i) false) :
    ∀ i, (gs.foldl pushGate xs).getD i false =
      ((gs.map (relocateGate n m f)).foldl pushGate ys).getD (assign n m f i) false := by
  induction gs generalizing k xs ys with
  | nil => exact data
  | cons g gs ih =>
    simp only [List.foldl_cons, List.map_cons]
    apply ih (k+1) _ _ (by simp [pushGate,hx,Nat.add_assoc]) (by simp [pushGate,hy,Nat.add_assoc])
    intro i
    have values : g.inputs.map (fun j => xs.getD j false) =
        (relocateGate n m f g).inputs.map (fun j => ys.getD j false) := by
      simp only [relocateGate, List.map_map, Function.comp_def]
      exact List.map_congr_left (fun j _ => data j)
    have same : i=xs.length ↔ assign n m f i=ys.length := by
      simp only [hx, hy, assign]
      split
      · have := hf i ‹i<n›
        omega
      · omega
    simp only [pushGate, getD_snoc, same, values]
    simp only [relocateGate, data]

theorem fits_relabel {n m p b s : Nat} {word : Fin (n+1) → Bool}
    (h : fits n p b s word) (f : Nat → Nat) (tmap : Fin (m+1) → Fin (n+1))
    (hf : ∀ i < n+2, f i < m+2)
    (hw : ∀ t i, i < n+2 → (inputsAt n (tmap t)).getD i false = (inputsAt m t).getD (f i) false) :
    fits m p b s (word ∘ tmap) := by
  obtain ⟨C, hfan, hr, hp, hb, hs, ho, he⟩ := h
  let D := relocate (n+2) (m+2) f C
  refine ⟨D, relocate_fanin hfan, relocate_reads hf hr, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [D, relocate_size, notCount_relocate] using hp
  · simpa [D, notCount_relocate] using hb
  · simpa [D, relocate_size] using hs
  · have hdo := assign_bound hf ho
    rw [show D.size = C.size from relocate_size _ _ _ _]
    exact hdo
  · intro t
    have init : ∀ i, (inputsAt n (tmap t)).getD i false = (inputsAt m t).getD (assign (n+2) (m+2) f i) false := by
      intro i
      by_cases yes : i < n+2
      · simpa only [assign, if_pos yes] using hw t i yes
      · rw [List.getD_eq_default _ _ (by rw [prefix_length]; omega),
            List.getD_eq_default _ _ (by rw [prefix_length]; simp [assign,yes])]
    have transfer := fold_relocate hf C.gates 0 (inputsAt n (tmap t)) (inputsAt m t)
      (by simp [prefix_length]) (by simp [prefix_length]) init C.output
    change C.eval (inputsAt n (tmap t)) = D.eval (inputsAt m t) at transfer
    exact transfer.symm.trans (he (tmap t))

end PEqualNP.Outside.L_lib_1380
namespace PEqualNP.Outside.L_lib_1380

def zig (z : Bool) (i : Nat) : Bool := if i % 2 = 0 then z else !z

def oneChange (n : Nat) (z : Bool) (cut : Nat) (t : Fin (n+1)) : Bool :=
  if t.val < cut then z else !z

theorem compress_three {n p b s : Nat} {word : Fin (n+1) → Bool}
    (h : fits n p b s word) (a c d : Fin (n+1)) (hac : a.val < c.val) (hcd : c.val < d.val) :
    fits 2 p b s (fun t => word (if t=0 then a else if t=1 then c else d)) := by
  let mapStep : Fin 3 → Fin (n+1) := fun t => if t=0 then a else if t=1 then c else d
  let source : Nat → Nat := fun i =>
    if i<n then
      if i<a.val then 3 else if i<c.val then 0 else if i<d.val then 1 else 2
    else if i=n then 2 else 3
  have bound : ∀ i < n+2, source i < 2+2 := by
    intro i hi
    simp only [source]
    split_ifs <;> decide
  exact fits_relabel h source mapStep bound (by
    intro t i hi
    rw [prefix_read n _ i hi, prefix_read 2 _ _ (bound i hi)]
    fin_cases t <;> simp (disch := omega) [mapStep,source] <;> split_ifs <;> simp_all <;> omega)

theorem no_alternating_triple {n p b s : Nat} {word : Fin (n+1) → Bool}
    (only : ∀ (z : Bool) (k : Nat), fits k p b s (fun t => zig z t.val) ↔ k ≤ 1)
    (h : fits n p b s word) {a c d : Fin (n+1)} (hac : a.val < c.val) (hcd : c.val < d.val)
    (hdiff : word a ≠ word c) (hsame : word a = word d) : False := by
  have hfit := compress_three h a c d hac hcd
  have same : (fun t : Fin 3 => word (if t=0 then a else if t=1 then c else d)) =
      (fun t => zig (word a) t.val) := by
    funext t
    fin_cases t
    · simp [zig]
    · have hc : word c = !word a := by cases ha : word a <;> cases hc : word c <;> simp_all
      simpa [zig] using hc
    · simp [zig,hsame]
  rw [same] at hfit
  have := (only (word a) 2).mp hfit
  omega

theorem fits_has_one_change {n p b s : Nat} {word : Fin (n+1) → Bool}
    (only : ∀ (z : Bool) (k : Nat), fits k p b s (fun t => zig z t.val) ↔ k ≤ 1)
    (h : fits n p b s word) : ∃ z cut, word = oneChange n z cut := by
  classical
  let z := word ⟨0, Nat.zero_lt_succ n⟩
  let changes := Finset.univ.filter (fun t => word t ≠ z)
  by_cases empty : changes.Nonempty
  · obtain ⟨c,hc,first⟩ := Finset.exists_min_image changes (fun t : Fin (n+1) => t.val) empty
    have different : word c ≠ z := (Finset.mem_filter.mp hc).2
    have pos : 0 < c.val := by
      by_contra! hn
      have hc0 : c = ⟨0, Nat.zero_lt_succ n⟩ := Fin.ext (show c.val = 0 by omega)
      exact different (by simp [hc0,z])
    refine ⟨z,c.val,?_⟩
    funext t
    by_cases ht : t.val<c.val
    · have equal : word t = z := by
        by_contra never
        have member : t ∈ changes := Finset.mem_filter.mpr ⟨Finset.mem_univ _,never⟩
        exact (Nat.not_lt_of_ge (first _ member)) ht
      simp [oneChange, ht, equal]
    · have different' : word t ≠ z := by
        by_contra! equal
        have strict : c.val<t.val := by
          by_contra! hle
          have eq : c=t := Fin.ext (by omega)
          exact different (by simpa only [eq] using equal)
        exact no_alternating_triple only h (a := ⟨0, Nat.zero_lt_succ n⟩) pos strict different.symm equal.symm
      have flip : word t = !z := by cases hz : z <;> cases ht' : word t <;> simp_all
      simp [oneChange,ht,flip]
  · have none : changes = ∅ := Finset.not_nonempty_iff_eq_empty.mp empty
    refine ⟨z,n+1,?_⟩
    funext t
    have equal : word t = z := by
      by_contra bad
      have member : t ∈ changes := Finset.mem_filter.mpr ⟨Finset.mem_univ _,bad⟩
      simp [none] at member
    simp [oneChange,t.isLt,equal]

theorem fits_constant (n p b s : Nat) (z : Bool) : fits n p b s (fun _ => z) := by
  open PEqualNP.CircuitLowerBounds in
  let C : Circuit := ⟨[], if z then n+1 else n⟩
  refine ⟨C, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [C, PEqualNP.MetaComplexity.FanInTwo]
  · simp [C, PEqualNP.MetaComplexity.NestedCover.ReadsBack]
  · simp [C, Circuit.size, PEqualNP.NotBracket.notCount]
  · simp [C, PEqualNP.NotBracket.notCount]
  · simp [C, Circuit.size]
  · cases z <;> simp [C, Circuit.size] <;> omega
  · intro t
    change (inputsAt n t).getD (if z then n+1 else n) false = z
    cases z <;> simp only [Bool.false_eq_true, if_false, if_true] <;>
      rw [prefix_read n t _ (by omega)] <;> simp (disch := omega)

theorem one_change_fits (n p b s : Nat)
    (only : ∀ (z : Bool) (k : Nat), fits k p b s (fun t => zig z t.val) ↔ k ≤ 1)
    (z : Bool) (cut : Nat) : fits n p b s (oneChange n z cut) := by
  by_cases zero : cut = 0
  · subst cut
    have same : oneChange n z 0 = fun _ => !z := by
      funext t
      exact ite_eq_right (Nat.not_lt_zero _)
    rw [same]
    exact fits_constant n p b s (!z)
  by_cases beyond : n < cut
  · have he : oneChange n z cut = fun _ => z := by
      funext t
      have ht : t.val < cut := by have := t.isLt; omega
      simp [oneChange,ht]
    rw [he]
    exact fits_constant n p b s z
  let f : Nat → Nat := fun i => if i=0 then cut-1 else if i=1 then n else n+1
  let tmap : Fin (n+1) → Fin 2 := fun t => if t.val<cut then 0 else 1
  have bound : ∀ i<1+2, f i<n+2 := by intro i hi; simp only [f]; split_ifs <;> omega
  have old : fits 1 p b s (fun t => zig z t.val) := (only z 1).mpr (by omega)
  have transport := fits_relabel old f tmap bound (by
    intro t i hi
    rw [prefix_read 1 _ i hi, prefix_read n _ _ (bound i hi)]
    interval_cases i <;> simp (disch := omega) [f,tmap] <;> split_ifs <;> simp_all <;> omega)
  have eq : ((fun t : Fin 2 => zig z t.val) ∘ tmap) = oneChange n z cut := by
    funext t
    by_cases ht : t.val<cut <;> simp [tmap,oneChange,zig,ht]
  rwa [eq] at transport

end PEqualNP.Outside.L_lib_1380
namespace PEqualNP.Outside.L_lib_1380

section Certificate

open scoped BigOperators

abbrev Copy {n : Nat} (weight : Fin (n+1) → Nat) := Σ t : Fin (n+1), Fin (weight t)

abbrev OfBit {n : Nat} (preferred : Fin (n+1) → Bool) (weight : Fin (n+1) → Nat) (b : Bool) :=
  {x : Copy weight // preferred x.1 = b}

theorem copy_count {n : Nat} (weight : Fin (n+1) → Nat) (P : Fin (n+1) → Prop)
    [DecidablePred P] : (Finset.univ.filter (fun x : Copy weight => P x.1)).card =
      ∑ t : Fin (n+1), if P t then weight t else 0 := by
  classical
  have hs : (Finset.univ.filter (fun x : Copy weight => P x.1)) =
      (Finset.univ.filter P).sigma (fun t => (Finset.univ : Finset (Fin (weight t)))) := by
    ext x
    simp
  rw [hs, Finset.card_sigma, Finset.sum_filter]
  simp

theorem bit_copy_count {n : Nat} (preferred : Fin (n+1) → Bool) (weight : Fin (n+1) → Nat)
    (bit : Bool) (P : Fin (n+1) → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun x : OfBit preferred weight bit => P x.val.1)).card =
      ∑ t : Fin (n+1), if preferred t = bit ∧ P t then weight t else 0 := by
  classical
  let f : OfBit preferred weight bit ↪ Copy weight := ⟨Subtype.val, Subtype.val_injective⟩
  have hs : (Finset.univ.filter (fun x : OfBit preferred weight bit => P x.val.1)).map f =
      Finset.univ.filter (fun x : Copy weight => preferred x.1 = bit ∧ P x.1) := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, y.property, (Finset.mem_filter.mp hy).2⟩
    · intro hx
      obtain ⟨_,hb,hp⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_map.mpr ⟨⟨x,hb⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩, rfl⟩
  rw [← Finset.card_map (f := f), hs]
  exact copy_count weight (fun t => preferred t = bit ∧ P t)

def mismatch {n : Nat} (preferred : Fin (n+1) → Bool) (weight : Fin (n+1) → Nat)
    (S : Finset (Fin (n+1))) (w : Fin (n+1) → Bool) : Nat :=
  S.sum fun t => if w t ≠ preferred t then weight t else 0

theorem oriented_count {n : Nat} (preferred : Fin (n+1) → Bool) (weight : Fin (n+1) → Nat)
    (z : Bool) (k : Nat) :
    (Finset.univ.filter (fun x : OfBit preferred weight (!z) => x.val.1.val < k)).card +
      (Finset.univ.filter (fun x : OfBit preferred weight z => k ≤ x.val.1.val)).card =
    mismatch preferred weight Finset.univ (oneChange n z k) := by
  classical
  unfold mismatch
  rw [bit_copy_count preferred weight (!z) (fun t => t.val < k),
      bit_copy_count preferred weight z (fun t => k ≤ t.val), ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases before : t.val<k <;> cases z <;> cases h : preferred t <;>
    simp [oneChange, before, h, Nat.not_le_of_gt, Nat.le_of_not_gt]

theorem swap_matching {A B : Type} [DecidableEq A] [DecidableEq B] {P : B → A → Prop}
    {M : Finset (B × A)} (h : IsMatching P M) :
    IsMatching (fun a b => P b a) (M.map (Equiv.prodComm B A).toEmbedding) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e he f hf same
    obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp he
    obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp hf
    exact congrArg _ (h.2.1 hx hy same)
  · intro e he f hf same
    obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp he
    obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp hf
    exact congrArg _ (h.1 hx hy same)
  · intro e he
    obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp he
    exact h.2.2 x hx

theorem support_loss {n : Nat} (preferred : Fin (n+1) → Bool) (weight : Fin (n+1) → Nat)
    (z : Bool) (cut : Nat) (S : Finset (Fin (n+1)))
    {M : Finset (OfBit preferred weight (!z) × OfBit preferred weight z)}
    (hM : IsMatching (fun a b => a.val.1.val < b.val.1.val) M)
    (hS : ∀ e ∈ M, e.1.val.1 ∈ S ∧ e.2.val.1 ∈ S) :
    M.card ≤ mismatch preferred weight S (oneChange n z cut) := by
  classical
  let bad (x : Copy weight) := x.1 ∈ S ∧ oneChange n z cut x.1 ≠ preferred x.1
  let choose (e : OfBit preferred weight (!z) × OfBit preferred weight z) : Copy weight :=
    if e.1.val.1.val < cut then e.1.val else e.2.val
  have different {a : OfBit preferred weight (!z)} {b : OfBit preferred weight z} : a.val ≠ b.val := by
    intro same
    have step := congrArg (fun x : Copy weight => preferred x.1) same
    rw [a.property,b.property] at step
    cases z <;> simp_all
  have inject : Set.InjOn choose (↑M : Set _) := by
    intro e he f hf eq
    by_cases ae : e.1.val.1.val<cut <;> by_cases af : f.1.val.1.val<cut
    · refine hM.1 he hf (Subtype.ext ?_)
      simpa only [choose,ite_eq_left ae,ite_eq_left af] using eq
    · exact False.elim (different (by simpa only [choose,ite_eq_left ae,ite_eq_right af] using eq))
    · exact False.elim (different (by simpa only [choose,ite_eq_right ae,ite_eq_left af] using eq.symm))
    · refine hM.2.1 he hf (Subtype.ext ?_)
      simpa only [choose,ite_eq_right ae,ite_eq_right af] using eq
  have subset : M.image choose ⊆ Finset.univ.filter bad := by
    intro v hv
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hv
    have order := hM.2.2 e he
    have ha := e.1.property
    have hb := e.2.property
    by_cases before : e.1.val.1.val<cut
    · simp only [choose, ite_eq_left before]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hS e he).1, by
        rw [oneChange, ite_eq_left before, ha]
        cases z <;> decide⟩
    · have after : ¬e.2.val.1.val<cut := by omega
      simp only [choose, ite_eq_right before]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hS e he).2, by
        rw [oneChange, ite_eq_right after, hb]
        cases z <;> decide⟩
  have counts : (Finset.univ.filter bad).card = mismatch preferred weight S (oneChange n z cut) := by
    rw [copy_count weight (fun t => t ∈ S ∧ oneChange n z cut t ≠ preferred t)]
    simp [bad, mismatch, ← Finset.sum_filter, ite_and]
  have h := Finset.card_le_card subset
  rwa [Finset.card_image_of_injOn inject, counts] at h

theorem bounded_certificate {n : Nat} (preferred : Fin (n+1) → Bool) (weight : Fin (n+1) → Nat)
    (q : Nat) (h : ∀ z k, q ≤ mismatch preferred weight Finset.univ (oneChange n z k)) :
    ∃ S : Finset (Fin (n+1)), S.card ≤ 3*q ∧
      ∀ z k, q ≤ mismatch preferred weight S (oneChange n z k) := by
  classical
  let A := OfBit preferred weight true
  let B := OfBit preferred weight false
  let arow (a : A) := a.val.1.val
  let brow (b : B) := b.val.1.val
  have distinct (a : A) (b : B) : arow a ≠ brow b := by
    intro eq
    have he : a.val.1 = b.val.1 := Fin.ext eq
    have ha := a.property
    have hb := b.property
    rw [he,hb] at ha
    contradiction
  let color (a : A) (b : B) := decide (arow a < brow b)
  have red : ∃ M : Finset (A × B), M.card=q ∧ IsMatching (fun a b => color a b = true) M := by
    obtain ⟨M, hc, hm, _⟩ := ordered_matching arow brow (n+1) q Finset.univ Finset.univ
      (fun a _ => a.val.1.isLt) (fun b _ => b.val.1.isLt) (fun a _ b _ => distinct a b) (by
        intro k hk
        calc
          q ≤ mismatch preferred weight Finset.univ (oneChange n false k) := h false k
          _ = _ := (oriented_count preferred weight false k).symm)
    exact ⟨M,hc,hm.1,hm.2.1,fun e he => decide_eq_true (hm.2.2 e he)⟩
  have blue : ∃ M : Finset (A × B), M.card=q ∧ IsMatching (fun a b => color a b = false) M := by
    obtain ⟨M, hc, hm, _⟩ := ordered_matching brow arow (n+1) q Finset.univ Finset.univ
      (fun b _ => b.val.1.isLt) (fun a _ => a.val.1.isLt) (fun b _ a _ => (distinct a b).symm) (by
        intro k hk
        calc
          q ≤ mismatch preferred weight Finset.univ (oneChange n true k) := h true k
          _ = _ := (oriented_count preferred weight true k).symm)
    have rel : IsMatching (fun b a => color a b = false) M :=
      ⟨hm.1,hm.2.1,fun e he => decide_eq_false (Nat.not_lt_of_ge (Nat.le_of_lt (hm.2.2 e he)))⟩
    exact ⟨M.map (Equiv.prodComm B A).toEmbedding, by simpa using hc, swap_matching rel⟩
  obtain ⟨R,T,hr,ht,hrm,htm,hcard⟩ := matching_pair color q red blue
  let row : A ⊕ B → Fin (n+1) := Sum.elim (fun a => a.val.1) (fun b => b.val.1)
  let S := (support R ∪ support T).image row
  refine ⟨S, (Finset.card_image_le).trans hcard, ?_⟩
  have rrows : ∀ e ∈ R, e.1.val.1 ∈ S ∧ e.2.val.1 ∈ S := by
    intro e he
    exact ⟨Finset.mem_image.mpr ⟨Sum.inl e.1, Finset.mem_union_left _ (inl_support.mpr ⟨e,he,rfl⟩), rfl⟩,
      Finset.mem_image.mpr ⟨Sum.inr e.2, Finset.mem_union_left _ (inr_support.mpr ⟨e,he,rfl⟩), rfl⟩⟩
  have trows : ∀ e ∈ T, e.1.val.1 ∈ S ∧ e.2.val.1 ∈ S := by
    intro e he
    exact ⟨Finset.mem_image.mpr ⟨Sum.inl e.1, Finset.mem_union_right _ (inl_support.mpr ⟨e,he,rfl⟩), rfl⟩,
      Finset.mem_image.mpr ⟨Sum.inr e.2, Finset.mem_union_right _ (inr_support.mpr ⟨e,he,rfl⟩), rfl⟩⟩
  intro z k
  cases z
  · have rel : IsMatching (fun a b => arow a < brow b) R :=
      ⟨hrm.1,hrm.2.1,fun e he => of_decide_eq_true (hrm.2.2 e he)⟩
    rw [← hr]
    exact support_loss preferred weight false k S rel rrows
  · let U := T.map (Equiv.prodComm A B).toEmbedding
    have rel : IsMatching (fun a b => brow b < arow a) T := by
      refine ⟨htm.1,htm.2.1,?_⟩
      intro e he
      have hn : ¬ arow e.1 < brow e.2 := of_decide_eq_false (htm.2.2 e he)
      exact lt_of_le_of_ne (Nat.le_of_not_gt hn) (distinct e.1 e.2).symm
    have urows : ∀ e ∈ U, e.1.val.1 ∈ S ∧ e.2.val.1 ∈ S := by
      intro e he
      obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp he
      exact (trows j hj).symm
    have hc : U.card=q := by simp [U,ht]
    rw [← hc]
    exact support_loss preferred weight true k S (swap_matching rel) urows

end Certificate

end PEqualNP.Outside.L_lib_1380
namespace PEqualNP.Outside.L_lib_1380

open scoped BigOperators

def afford (n p b s e : Nat) (cost : Fin (n+1) → Bool → Nat) (S : Finset (Fin (n+1))) : Prop :=
  ∃ w : Fin (n+1) → Bool, fits n p b s w ∧ S.sum (fun t => cost t (w t)) ≤ e

theorem sum_positive {α : Type} (S : Finset α) (f : α → Nat) :
    ((S.filter (fun t => 0<f t)).sum f) = S.sum f := by
  classical
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  split <;> omega

theorem positive_card {α : Type} (S : Finset α) (f : α → Nat) (positive : ∀ t ∈ S, 0<f t) :
    S.card ≤ S.sum f := by
  simpa using (Finset.sum_le_sum (f := fun _ : α => (1 : Nat)) (g := f)
    (s := S) (fun t ht => positive t ht))

theorem sample_base {α : Type} (S : Finset α) (f : α → Nat) (r : Nat) (h : r ≤ S.sum f) :
    ∃ T ⊆ S, T.card ≤ r ∧ r ≤ T.sum f := by
  classical
  let U := S.filter (fun t => 0<f t)
  have hU : U.sum f = S.sum f := sum_positive S f
  by_cases few : U.card ≤ r
  · exact ⟨U,Finset.filter_subset _ _,few,by rwa [hU]⟩
  · obtain ⟨T,hs,hc⟩ := Finset.exists_subset_card_eq (s := U) (show r ≤ U.card by omega)
    have bound := positive_card T f (fun t ht => (Finset.mem_filter.mp (hs ht)).2)
    exact ⟨T,hs.trans (Finset.filter_subset _ _),hc.le,by rwa [hc] at bound⟩

theorem weighted_upper (p b s : Nat)
    (only : ∀ (z : Bool) (k : Nat), fits k p b s (fun t => zig z t.val) ↔ k ≤ 1)
    (n E : Nat) (cost : Fin (n+1) → Bool → Nat) :
    ∃ S : Finset (Fin (n+1)), S.card ≤ 3*(E+1) ∧
      ∀ e ≤ E, afford n p b s e cost Finset.univ ↔ afford n p b s e cost S := by
  classical
  let preferred (t : Fin (n+1)) := decide (cost t true < cost t false)
  let base (t : Fin (n+1)) := min (cost t false) (cost t true)
  let extra (t : Fin (n+1)) := max (cost t false) (cost t true) - base t
  have split_cost (t : Fin (n+1)) (z : Bool) :
      cost t z = base t + (if z ≠ preferred t then extra t else 0) := by
    by_cases h : cost t true < cost t false
    · cases z <;> simp [base, extra, preferred, h, min_eq_right (Nat.le_of_lt h),
        max_eq_left (Nat.le_of_lt h)] <;> omega
    · have hle : cost t false ≤ cost t true := Nat.le_of_not_gt h
      cases z <;> simp [base, extra, preferred, h, min_eq_left hle, max_eq_right hle] <;> omega
  have sum_split (S : Finset (Fin (n+1))) (w : Fin (n+1) → Bool) :
      S.sum (fun t => cost t (w t)) = S.sum base + mismatch preferred extra S w := by
    simp only [mismatch, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun t _ => split_cost t (w t))
  have feasible : ∃ e, afford n p b s e cost Finset.univ :=
    ⟨Finset.univ.sum (fun t => cost t false), (fun _ => false), fits_constant n p b s false, le_rfl⟩
  let minimum := Nat.find feasible
  have opt : afford n p b s minimum cost Finset.univ := Nat.find_spec feasible
  have min_le (w : Fin (n+1) → Bool) (hw : fits n p b s w) :
      minimum ≤ Finset.univ.sum (fun t => cost t (w t)) := Nat.find_min' feasible ⟨w, hw, le_rfl⟩
  let r := min minimum (E+1)
  let B := Finset.univ.sum base
  have certificate : ∃ S : Finset (Fin (n+1)), S.card ≤ 3*r ∧
      ∀ w, fits n p b s w → r ≤ S.sum (fun t => cost t (w t)) := by
    by_cases enough : r ≤ B
    · obtain ⟨S,hs,hc,hbase⟩ := sample_base Finset.univ base r enough
      refine ⟨S, by omega, fun w _ => ?_⟩
      rw [sum_split]
      omega
    · let q := r-B
      have all (z : Bool) (k : Nat) : q ≤ mismatch preferred extra Finset.univ (oneChange n z k) := by
        have low := min_le (oneChange n z k) (one_change_fits n p b s only z k)
        rw [sum_split] at low
        have hr : r ≤ minimum := min_le_left _ _
        dsimp only [q,B] at *
        omega
      obtain ⟨T,ht,cert⟩ := bounded_certificate preferred extra q all
      let U := Finset.univ.filter (fun t => 0<base t)
      let S := U ∪ T
      have base_sum : U.sum base = B := sum_positive _ _
      have ucard : U.card ≤ B := by
        rw [← base_sum]
        exact positive_card U base (fun t ht => (Finset.mem_filter.mp ht).2)
      refine ⟨S, ?_, ?_⟩
      · have bound := Finset.card_union_le U T
        change (U ∪ T).card ≤ _
        dsimp only [q] at ht
        omega
      · intro w hw
        obtain ⟨z,k,rfl⟩ := fits_has_one_change only hw
        have hb : B ≤ S.sum base := by
          rw [← base_sum]
          exact Finset.sum_le_sum_of_subset (Finset.subset_union_left)
        have hd : mismatch preferred extra T (oneChange n z k) ≤ mismatch preferred extra S (oneChange n z k) :=
          Finset.sum_le_sum_of_subset (Finset.subset_union_right)
        have low := cert z k
        dsimp only [q] at low
        rw [sum_split]
        omega
  obtain ⟨S, sz, low⟩ := certificate
  have cap : r ≤ E+1 := min_le_right _ _
  refine ⟨S, by omega, fun e he => ⟨?_, ?_⟩⟩
  · rintro ⟨w,hw,hc⟩
    exact ⟨w,hw,(Finset.sum_le_sum_of_subset (Finset.subset_univ S)).trans hc⟩
  · rintro ⟨w,hw,hc⟩
    have hr := (low w hw).trans hc
    have hmin : minimum ≤ e := by
      change min minimum (E+1) ≤ e at hr
      omega
    obtain ⟨v,hv,hv'⟩ := opt
    exact ⟨v,hv,hv'.trans hmin⟩

end PEqualNP.Outside.L_lib_1380
namespace PEqualNP.Outside.L_lib_1380

theorem weighted_lower (p b s : Nat)
    (only : ∀ (z : Bool) (k : Nat), fits k p b s (fun t => zig z t.val) ↔ k ≤ 1)
    (E n : Nat) (size : n+1 = 3*(E+1)) :
    ∃ z : Bool,
      let cost := fun (t : Fin (n+1)) (v : Bool) => if v = zig z (t.val/(E+1)) then 0 else 1
      (¬ afford n p b s E cost Finset.univ) ∧
        ∀ S : Finset (Fin (n+1)), S ≠ Finset.univ → afford n p b s E cost S := by
  classical
  let r := E+1
  have rpos : 0<r := by omega
  have rows : n+1 = 3*r := size
  let wanted (t : Fin (n+1)) := zig false (t.val/r)
  let cost (t : Fin (n+1)) (v : Bool) : Nat := if v = wanted t then 0 else 1
  let block (i : Fin 3) (j : Fin r) : Fin (n+1) := ⟨i.val*r + j.val, by
    have hi := i.isLt
    have hj := j.isLt
    have hbound := Nat.mul_le_mul_right r (show i.val ≤ 2 by omega)
    omega⟩
  have block_div (i : Fin 3) (j : Fin r) : (block i j).val/r = i.val := by
    change (i.val*r + j.val)/r = i.val
    rw [Nat.add_comm, Nat.mul_comm i.val r, Nat.add_mul_div_left _ _ rpos, Nat.div_eq_of_lt j.isLt, Nat.zero_add]
  have block_mod (i : Fin 3) (j : Fin r) : (block i j).val % r = j.val := by
    change (i.val*r + j.val) % r = j.val
    rw [Nat.add_comm, Nat.mul_comm i.val r, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt j.isLt]
  have block_ord (i k : Fin 3) (j : Fin r) (h : i.val < k.val) :
      (block i j).val < (block k j).val := by
    exact Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_right h rpos) j.val
  have block_want (i : Fin 3) (j : Fin r) : wanted (block i j) = zig false i.val := by
    simp only [wanted,block_div]
  refine ⟨false, ?_⟩
  change (¬ afford n p b s E cost Finset.univ) ∧ _
  constructor
  · rintro ⟨w,hw,hcap⟩
    have bad (j : Fin r) : w (block 0 j) ≠ false ∨ w (block 1 j) ≠ true ∨ w (block 2 j) ≠ false := by
      by_contra! h
      obtain ⟨ha,hb,hc⟩ := h
      exact no_alternating_triple only hw (block_ord 0 1 j (by decide)) (block_ord 1 2 j (by decide))
        (by rw [ha,hb]; decide) (ha.trans hc.symm)
    let choice (j : Fin r) : Fin 3 := if w (block 0 j) ≠ false then 0 else
      if w (block 1 j) ≠ true then 1 else 2
    let pick (j : Fin r) := block (choice j) j
    have inject : Function.Injective pick := by
      intro j k h
      apply Fin.ext
      have m := congrArg (fun t : Fin (n+1) => t.val % r) h
      simpa only [pick,block_mod] using m
    have cost_one (j : Fin r) : cost (pick j) (w (pick j))=1 := by
      simp only [pick, cost, block_want]
      by_cases h0 : w (block 0 j) ≠ false
      · rw [show choice j = 0 from ite_eq_left h0]
        exact ite_eq_right h0
      · by_cases h1 : w (block 1 j) ≠ true
        · have index : choice j = 1 := by unfold choice; rw [ite_eq_right h0, ite_eq_left h1]
          rw [index]
          exact ite_eq_right h1
        · have h2 : w (block 2 j) ≠ false := (bad j).resolve_left h0 |>.resolve_left h1
          have index : choice j = 2 := by unfold choice; rw [ite_eq_right h0, ite_eq_right h1]
          rw [index]
          exact ite_eq_right h2
    let used : Finset (Fin (n+1)) := Finset.univ.image pick
    have used_card : used.card = r := by
      simp [used, Finset.card_image_of_injective _ inject]
    have used_sum : used.sum (fun t => cost t (w t)) = used.card := by
      calc
        _ = used.sum (fun _ => (1 : Nat)) := by
          apply Finset.sum_congr rfl
          intro t ht
          obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp ht
          exact cost_one j
        _ = _ := by simp
    have low := Finset.sum_le_sum_of_subset (f := fun t => cost t (w t)) (Finset.subset_univ used)
    omega
  · intro S hproper
    have missing : ∃ t : Fin (n+1), t ∉ S := by
      by_contra! all
      exact hproper (Finset.eq_univ_of_forall all)
    obtain ⟨t,ht⟩ := missing
    have range (u : Fin (n+1)) : u.val/r < 3 := (Nat.div_lt_iff_lt_mul rpos).mpr (by
      calc
        u.val < n+1 := u.isLt
        _ = 3*r := rows)
    let i : Fin 3 := ⟨t.val/r,range t⟩
    let params : Bool × Nat := if i=0 then (true,2*r) else if i=1 then (false,n+1) else (false,r)
    let w := oneChange n params.1 params.2
    have hw : fits n p b s w := one_change_fits n p b s only _ _
    let patternSet : Finset (Fin (n+1)) := Finset.univ.image (block i)
    have eq_block (u : Fin (n+1)) : u ∈ patternSet ↔ u.val/r = i.val := by
      constructor
      · intro h
        obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp h
        exact block_div i j
      · intro h
        let j : Fin r := ⟨u.val % r,Nat.mod_lt _ rpos⟩
        refine Finset.mem_image.mpr ⟨j,Finset.mem_univ _,Fin.ext ?_⟩
        change i.val*r + u.val % r = u.val
        rw [← h, Nat.mul_comm, Nat.add_comm, Nat.mod_add_div]
    have cost_block (u : Fin (n+1)) : cost u (w u) = if u.val/r = i.val then 1 else 0 := by
      let j : Fin 3 := ⟨u.val/r,range u⟩
      have uj : u.val/r = j.val := rfl
      have h1 : u.val < r ↔ j.val < 1 := by
        rw [← uj, Nat.div_lt_iff_lt_mul rpos, Nat.one_mul]
      have h2 : u.val < 2*r ↔ j.val < 2 := by
        rw [← uj, Nat.div_lt_iff_lt_mul rpos]
      have h3 := u.isLt
      change (if w u = zig false (u.val/r) then 0 else 1) = _
      rw [uj]
      revert h1 h2
      generalize hi : i = v
      generalize hj : j = y
      fin_cases v <;> fin_cases y <;>
        simp (disch := omega) [w,params,oneChange,zig,hi,hj,h3] <;> grind
    have size_block : patternSet.card = r := by
      have inj : Function.Injective (block i) := by
        intro j k eq
        exact Fin.ext (by simpa only [block_mod] using congrArg (fun u : Fin (n+1) => u.val % r) eq)
      simp [patternSet,Finset.card_image_of_injective _ inj]
    have t_mem : t ∈ patternSet := (eq_block t).mpr rfl
    have subset : (S.filter (fun u => u.val/r = i.val)) ⊆ patternSet.erase t := by
      intro u hu
      obtain ⟨hu,hi⟩ := Finset.mem_filter.mp hu
      exact Finset.mem_erase.mpr ⟨fun e => ht (e ▸ hu),(eq_block u).mpr hi⟩
    have le := Finset.card_le_card subset
    have smaller := Finset.card_erase_add_one t_mem
    refine ⟨w,hw,?_⟩
    calc
      _ = (S.filter (fun u => u.val/r = i.val)).sum (fun _ => (1 : Nat)) := by
        rw [Finset.sum_filter]
        exact Finset.sum_congr rfl (fun u _ => cost_block u)
      _ = (S.filter (fun u => u.val/r = i.val)).card := by simp
      _ ≤ E := by omega

theorem finish (p b s : Nat)
    (only : ∀ (z : Bool) (k : Nat), fits k p b s (fun t => zig z t.val) ↔ k ≤ 1) :
    (∀ (n E : Nat) (cost : Fin (n+1) → Bool → Nat),
      ∃ S : Finset (Fin (n+1)), S.card ≤ 3*(E+1) ∧
        ∀ e ≤ E, afford n p b s e cost Finset.univ ↔ afford n p b s e cost S) ∧
    ∀ E n : Nat, n+1 = 3*(E+1) → ∃ z : Bool,
      let cost := fun (t : Fin (n+1)) (v : Bool) => if v = zig z (t.val/(E+1)) then 0 else 1
      (¬ afford n p b s E cost Finset.univ) ∧
        ∀ S : Finset (Fin (n+1)), S ≠ Finset.univ → afford n p b s E cost S :=
  ⟨weighted_upper p b s only, weighted_lower p b s only⟩

end PEqualNP.Outside.L_lib_1380

theorem PEqualNP.Outside.L_lib_1380 :
  let fits := fun (n p b s : Nat) (word : Fin (n+1) → Bool) =>
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
      C.size-PEqualNP.NotBracket.notCount C ≤ p ∧ PEqualNP.NotBracket.notCount C ≤ b ∧
      C.size ≤ s ∧ C.output < n+2+C.size ∧ ∀ t : Fin (n+1),
        C.eval ((List.ofFn (fun j : Fin n => decide (j.val < t.val))) ++ [false,true]) = word t
  let zig := fun (z : Bool) (i : Nat) => if i % 2 = 0 then z else !z
  let afford := fun (n p b s e : Nat) (cost : Fin (n+1) → Bool → Nat) (S : Finset (Fin (n+1))) =>
    ∃ word : Fin (n+1) → Bool, fits n p b s word ∧ S.sum (fun t => cost t (word t)) ≤ e
  ∀ p b s : Nat,
    (∀ (z : Bool) (k : Nat), fits k p b s (fun t => zig z t.val) ↔ k ≤ 1) →
    (∀ (n E : Nat) (cost : Fin (n+1) → Bool → Nat),
      ∃ S : Finset (Fin (n+1)), S.card ≤ 3*(E+1) ∧
        ∀ e ≤ E, afford n p b s e cost Finset.univ ↔ afford n p b s e cost S) ∧
    ∀ E n : Nat, n+1 = 3*(E+1) → ∃ z : Bool,
      let cost := fun (t : Fin (n+1)) (v : Bool) => if v = zig z (t.val/(E+1)) then 0 else 1
      (¬ afford n p b s E cost Finset.univ) ∧
      ∀ S : Finset (Fin (n+1)), S ≠ Finset.univ → afford n p b s E cost S :=
  PEqualNP.Outside.L_lib_1380.finish
