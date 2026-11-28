import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1192
open PEqualNP.CircuitLowerBounds

def wiresL (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresL C.gates x := rfl

theorem wiresL_append (gs hs : List Gate) (x : List Bool) :
    wiresL (gs ++ hs) x = wiresL hs (wiresL gs x) := by
  simp [wiresL, List.foldl_append]

theorem wiresL_front (gs : List Gate) (x : List Bool) :
    ∃ t, wiresL gs x = x ++ t ∧ t.length = gs.length := by
  induction gs generalizing x with
  | nil => exact ⟨[], by simp [wiresL]⟩
  | cons g gs ih =>
    obtain ⟨t, ht, hl⟩ := ih (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => x.getD i false) :: t, ?_, by simp [hl]⟩
    simpa [wiresL] using ht

theorem wiresL_length (gs : List Gate) (x : List Bool) :
    (wiresL gs x).length = x.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresL_front gs x
  simp [ht, hl]

theorem wiresL_getD_lt (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (wiresL gs x).getD i false = x.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresL_front gs x
  rw [ht]
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wiresL_append_getD_lt (gs hs : List Gate) (x : List Bool) (i : ℕ)
    (hi : i < x.length + gs.length) :
    (wiresL (gs ++ hs) x).getD i false = (wiresL gs x).getD i false := by
  rw [wiresL_append]
  exact wiresL_getD_lt hs _ i (by rw [wiresL_length]; exact hi)

theorem wiresL_snoc_getD (gs : List Gate) (g : Gate) (x : List Bool) :
    (wiresL (gs ++ [g]) x).getD (x.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (wiresL gs x).getD i false) := by
  rw [wiresL_append]
  have hl := wiresL_length gs x
  simp [wiresL, List.getD_eq_getElem?_getD, ← hl]

def gAnd (i j : ℕ) : Gate := ⟨GateOp.and, [i, j]⟩

def gOr (i j : ℕ) : Gate := ⟨GateOp.or, [i, j]⟩

theorem gAnd_eval (w : List Bool) (i j : ℕ) :
    (gAnd i j).op.eval ((gAnd i j).inputs.map fun k => w.getD k false) =
      (w.getD i false && w.getD j false) := by
  simp [gAnd, GateOp.eval]

theorem gOr_eval (w : List Bool) (i j : ℕ) :
    (gOr i j).op.eval ((gOr i j).inputs.map fun k => w.getD k false) =
      (w.getD i false || w.getD j false) := by
  simp [gOr, GateOp.eval]

def Good (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j (hj : j < gs.length), (gs[j].op = GateOp.and ∨ gs[j].op = GateOp.or) ∧
    gs[j].inputs.length ≤ 2 ∧ ∀ i ∈ gs[j].inputs, i < n + j

theorem Good.nil (n : ℕ) : Good n [] := by
  intro j hj; simp at hj

theorem Good.snoc {n : ℕ} {gs : List Gate} (h : Good n gs) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length ≤ 2)
    (hin : ∀ i ∈ g.inputs, i < n + gs.length) : Good n (gs ++ [g]) := by
  intro j hj
  by_cases hlt : j < gs.length
  · simpa [List.getElem_append_left hlt] using h j hlt
  · have hj' : j = gs.length := by
      simp at hj; omega
    subst hj'
    simpa using ⟨hop, hlen, hin⟩

theorem Good.fanInTwo {n : ℕ} {gs : List Gate} (h : Good n gs) (o : ℕ) :
    PEqualNP.MetaComplexity.FanInTwo ⟨gs, o⟩ := by
  intro g hg
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
  obtain ⟨hop, hlen, _⟩ := h j hj
  refine ⟨?_, hlen⟩
  rcases hop with hop | hop <;> simp [hop]

theorem Good.readsBack {n : ℕ} {gs : List Gate} (h : Good n gs) (o : ℕ) :
    PEqualNP.MetaComplexity.NestedCover.ReadsBack n ⟨gs, o⟩ := by
  intro j hj i hi
  have hj' : j < gs.length := hj
  have : PEqualNP.MetaComplexity.NestedCover.gateAt ⟨gs, o⟩ j = gs[j] := by
    simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hj']
  rw [this] at hi
  exact (h j hj').2.2 i hi

theorem Good.notCount {n : ℕ} {gs : List Gate} (h : Good n gs) (o : ℕ) :
    PEqualNP.NotBracket.notCount ⟨gs, o⟩ = 0 := by
  unfold PEqualNP.NotBracket.notCount
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro g hg
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
  rcases (h j hj).1 with hop | hop <;> simp [hop]

theorem twoSat {V : Type} [Fintype V] (E : V × Bool → V × Bool → Prop)
    (skew : ∀ l l', E l l' → E (l'.1, !l'.2) (l.1, !l.2))
    (hno : ∀ v, ¬ (Relation.ReflTransGen E (v, true) (v, false) ∧
      Relation.ReflTransGen E (v, false) (v, true))) :
    ∃ σ : V → Bool, ∀ l l', E l l' → σ l.1 = l.2 → σ l'.1 = l'.2 := by
  classical
  have skewT : ∀ l l', Relation.ReflTransGen E l l' →
      Relation.ReflTransGen E (l'.1, !l'.2) (l.1, !l.2) := by
    intro l l' h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih => exact Relation.ReflTransGen.head (skew _ _ hbc) ih
  have main : ∀ n, ∀ A : Set (V × Bool),
      (∀ v, ¬ ((v, true) ∈ A ∧ (v, false) ∈ A)) →
      (∀ l l', l ∈ A → E l l' → l' ∈ A) →
      (Finset.univ.filter (fun v : V => (v, true) ∉ A ∧ (v, false) ∉ A)).card = n →
      ∃ A' : Set (V × Bool), (∀ v, ¬ ((v, true) ∈ A' ∧ (v, false) ∈ A')) ∧
        (∀ l l', l ∈ A' → E l l' → l' ∈ A') ∧ ∀ v, (v, true) ∈ A' ∨ (v, false) ∈ A' := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro A hc hcl hn
      by_cases htot : ∀ v, (v, true) ∈ A ∨ (v, false) ∈ A
      · exact ⟨A, hc, hcl, htot⟩
      · push Not at htot
        obtain ⟨v, hv1, hv2⟩ := htot
        obtain ⟨s, hs⟩ : ∃ s : Bool, ¬ Relation.ReflTransGen E (v, s) (v, !s) := by
          by_contra hcon
          push Not at hcon
          exact hno v ⟨hcon true, hcon false⟩
        have hvA : ∀ t, (v, t) ∉ A := by intro t; cases t <;> assumption
        have hclT : ∀ l l', l ∈ A → Relation.ReflTransGen E l l' → l' ∈ A := by
          intro l l' hl h
          induction h with
          | refl => exact hl
          | tail _ hbc ih => exact hcl _ _ ih hbc
        obtain ⟨A', hA'⟩ : ∃ A' : Set (V × Bool),
            ∀ l, l ∈ A' ↔ (l ∈ A ∨ Relation.ReflTransGen E (v, s) l) :=
          ⟨{l | l ∈ A ∨ Relation.ReflTransGen E (v, s) l}, fun l => Iff.rfl⟩
        have hc' : ∀ w, ¬ ((w, true) ∈ A' ∧ (w, false) ∈ A') := by
          intro w hw
          rw [hA', hA'] at hw
          rcases hw with ⟨h1 | h1, h2 | h2⟩
          · exact hc w ⟨h1, h2⟩
          · have h3 : Relation.ReflTransGen E (w, true) (v, !s) := skewT _ _ h2
            exact hvA _ (hclT _ _ h1 h3)
          · have h3 : Relation.ReflTransGen E (w, false) (v, !s) := skewT _ _ h1
            exact hvA _ (hclT _ _ h2 h3)
          · have h3 : Relation.ReflTransGen E (w, true) (v, !s) := skewT _ _ h2
            exact hs (h1.trans h3)
        have hcl' : ∀ l l', l ∈ A' → E l l' → l' ∈ A' := by
          intro l l' hl he
          rw [hA'] at hl ⊢
          rcases hl with hl | hl
          · exact Or.inl (hcl _ _ hl he)
          · exact Or.inr (Relation.ReflTransGen.tail hl he)
        have hvs : (v, s) ∈ A' := (hA' _).2 (Or.inr Relation.ReflTransGen.refl)
        have hlt : (Finset.univ.filter
            (fun w : V => (w, true) ∉ A' ∧ (w, false) ∉ A')).card < n := by
          rw [← hn]
          apply Finset.card_lt_card
          rw [Finset.ssubset_iff_of_subset]
          · refine ⟨v, by simp [hv1, hv2], ?_⟩
            intro hmem
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
            cases s
            · exact hmem.2 hvs
            · exact hmem.1 hvs
          · intro w hw
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
            exact ⟨fun h => hw.1 ((hA' _).2 (Or.inl h)), fun h => hw.2 ((hA' _).2 (Or.inl h))⟩
        exact ih _ hlt A' hc' hcl' rfl
  obtain ⟨A, hc, hcl, htot⟩ := main _ (∅ : Set (V × Bool)) (by simp) (by simp) rfl
  refine ⟨fun v => decide ((v, true) ∈ A), ?_⟩
  rintro ⟨u, s⟩ ⟨u', t⟩ he hσ
  have hl : (u, s) ∈ A := by
    cases s
    · have : (u, true) ∉ A := by simpa using hσ
      exact (htot u).resolve_left this
    · simpa using hσ
  have hl' := hcl _ _ hl he
  cases t
  · have : (u', true) ∉ A := fun h => hc u' ⟨h, hl'⟩
    simpa using this
  · simpa using hl'

inductive Imp {α β : Type} (bad : α → Bool → β → Bool → Prop) :
    (α ⊕ β) × Bool → (α ⊕ β) × Bool → Prop
  | pq (e : α) (s : Bool) (f : β) (t : Bool) : bad e s f t → Imp bad (Sum.inl e, s) (Sum.inr f, !t)
  | qp (e : α) (s : Bool) (f : β) (t : Bool) : bad e s f t → Imp bad (Sum.inr f, t) (Sum.inl e, !s)

theorem choice_iff {α β : Type} [Fintype α] [Fintype β] (bad : α → Bool → β → Bool → Prop) :
    (∃ (a : α → Bool) (b : β → Bool), ∀ e f, ¬ bad e (a e) f (b f)) ↔
      ∀ v : α ⊕ β, ¬ (Relation.ReflTransGen (Imp bad) (v, true) (v, false) ∧
        Relation.ReflTransGen (Imp bad) (v, false) (v, true)) := by
  constructor
  · rintro ⟨a, b, hab⟩ v ⟨h1, h2⟩
    have step : ∀ l l', Imp bad l l' → Sum.elim a b l.1 = l.2 → Sum.elim a b l'.1 = l'.2 := by
      intro l l' h
      cases h with
      | pq e s f t hb =>
        intro hs
        simp only [Sum.elim_inl, Sum.elim_inr] at hs ⊢
        subst hs
        have : b f ≠ t := fun hbt => hab e f (hbt ▸ hb)
        cases hbf : b f <;> cases t <;> simp_all
      | qp e s f t hb =>
        intro ht
        simp only [Sum.elim_inl, Sum.elim_inr] at ht ⊢
        subst ht
        have : a e ≠ s := fun has => hab e f (has ▸ hb)
        cases hae : a e <;> cases s <;> simp_all
    have stepT : ∀ l l', Relation.ReflTransGen (Imp bad) l l' →
        Sum.elim a b l.1 = l.2 → Sum.elim a b l'.1 = l'.2 := by
      intro l l' h
      induction h with
      | refl => exact id
      | tail _ hbc ih => exact fun hl => step _ _ hbc (ih hl)
    have e1 := stepT _ _ h1
    have e2 := stepT _ _ h2
    cases hv : Sum.elim a b v <;> simp_all
  · intro hno
    have skew : ∀ l l', Imp bad l l' → Imp bad (l'.1, !l'.2) (l.1, !l.2) := by
      intro l l' h
      cases h with
      | pq e s f t hb => simpa using Imp.qp e s f t hb
      | qp e s f t hb => simpa using Imp.pq e s f t hb
    obtain ⟨σ, hσ⟩ := twoSat (Imp bad) skew hno
    refine ⟨fun e => σ (Sum.inl e), fun f => σ (Sum.inr f), ?_⟩
    intro e f hb
    have := hσ _ _ (Imp.pq e _ f _ hb) rfl
    simp at this

def warsh (E : ℕ → ℕ → Bool) : ℕ → ℕ → ℕ → Bool
  | 0, i, j => E i j
  | k + 1, i, j => warsh E k i j || (warsh E k i k && warsh E k k j)

theorem warsh_of_E (E : ℕ → ℕ → Bool) (k i j : ℕ) (h : E i j = true) : warsh E k i j = true := by
  induction k with
  | zero => exact h
  | succ k ih => simp [warsh, ih]

theorem warsh_sound (E : ℕ → ℕ → Bool) (k : ℕ) : ∀ i j, warsh E k i j = true →
    Relation.TransGen (fun a b => E a b = true) i j := by
  induction k with
  | zero => intro i j h; exact Relation.TransGen.single h
  | succ k ih =>
    intro i j h
    simp only [warsh, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨h1, h2⟩
    · exact ih _ _ h
    · exact (ih _ _ h1).trans (ih _ _ h2)

theorem warsh_inv (E : ℕ → ℕ → Bool) (k : ℕ) : ∀ i j c, c < k → warsh E k i c = true →
    warsh E k c j = true → warsh E k i j = true := by
  induction k with
  | zero => intro i j c hc; omega
  | succ k ih =>
    intro i j c hc h1 h2
    simp only [warsh, Bool.or_eq_true, Bool.and_eq_true] at h1 h2 ⊢
    by_cases hck : c < k
    · rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
      · exact Or.inl (ih _ _ c hck h1 h2)
      · exact Or.inr ⟨ih _ _ c hck h1 h2, h2'⟩
      · exact Or.inr ⟨h1, ih _ _ c hck h1' h2⟩
      · exact Or.inr ⟨h1, h2'⟩
    · have hc' : c = k := by omega
      subst hc'
      have a1 : warsh E c i c = true := by
        rcases h1 with h1 | ⟨h1, _⟩ <;> exact h1
      have a2 : warsh E c c j = true := by
        rcases h2 with h2 | ⟨_, h2⟩ <;> exact h2
      exact Or.inr ⟨a1, a2⟩

theorem warsh_complete (E : ℕ → ℕ → Bool) (N : ℕ) (hE : ∀ a b, E a b = true → a < N ∧ b < N)
    (i j : ℕ) (h : Relation.TransGen (fun a b => E a b = true) i j) : warsh E N i j = true := by
  induction h with
  | single h => exact warsh_of_E E N _ _ h
  | tail _ hbc ih => exact warsh_inv E N _ _ _ (hE _ _ hbc).1 ih (warsh_of_E E N _ _ hbc)

theorem warsh_iff (E : ℕ → ℕ → Bool) (N : ℕ) (hE : ∀ a b, E a b = true → a < N ∧ b < N)
    (i j : ℕ) : warsh E N i j = true ↔ Relation.TransGen (fun a b => E a b = true) i j :=
  ⟨warsh_sound E N i j, warsh_complete E N hE i j⟩

def mkG (p : Bool × ℕ × ℕ) : Gate := if p.1 then gAnd p.2.1 p.2.2 else gOr p.2.1 p.2.2

def opB (b u v : Bool) : Bool := if b then u && v else u || v

theorem mkG_eval (w : List Bool) (p : Bool × ℕ × ℕ) :
    (mkG p).op.eval ((mkG p).inputs.map fun k => w.getD k false) =
      opB p.1 (w.getD p.2.1 false) (w.getD p.2.2 false) := by
  unfold mkG opB
  split
  · exact gAnd_eval w _ _
  · exact gOr_eval w _ _

theorem circSpec (n : ℕ) (x : List Bool) (hx : x.length = n) (ps : List (Bool × ℕ × ℕ))
    (hps : ∀ k (hk : k < ps.length), ps[k].2.1 < n + k ∧ ps[k].2.2 < n + k) :
    Good n (ps.map mkG) ∧
    (∀ i < n, (wiresL (ps.map mkG) x).getD i false = x.getD i false) ∧
    ∀ k (hk : k < ps.length), (wiresL (ps.map mkG) x).getD (n + k) false =
      opB ps[k].1 ((wiresL (ps.map mkG) x).getD ps[k].2.1 false)
        ((wiresL (ps.map mkG) x).getD ps[k].2.2 false) := by
  subst hx
  refine ⟨?_, fun i hi => wiresL_getD_lt _ _ i hi, ?_⟩
  · intro j hj
    have hj' : j < ps.length := by simpa using hj
    have h := hps j hj'
    simp only [List.getElem_map]
    unfold mkG
    split <;> simp [gAnd, gOr, h.1, h.2]
  · induction ps using List.reverseRecOn with
    | nil => intro k hk; simp at hk
    | append_singleton ps p ih =>
      have hps' : ∀ k (hk : k < ps.length), ps[k].2.1 < x.length + k ∧ ps[k].2.2 < x.length + k := by
        intro k hk
        have := hps k (by simp; omega)
        simpa [List.getElem_append_left hk] using this
      have ih' := ih hps'
      have hold : ∀ i, i < x.length + ps.length →
          (wiresL ((ps ++ [p]).map mkG) x).getD i false = (wiresL (ps.map mkG) x).getD i false := by
        intro i hi
        rw [List.map_append]
        exact wiresL_append_getD_lt _ _ x i (by simpa using hi)
      intro k hk
      by_cases hlt : k < ps.length
      · have h := hps' k hlt
        have e : (ps ++ [p])[k] = ps[k] := List.getElem_append_left hlt
        rw [e, hold _ (by omega), hold _ (by omega), hold _ (by omega), ih' k hlt]
      · have hk' : k = ps.length := by simp at hk; omega
        subst hk'
        have h := hps ps.length (by simp)
        simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_cons_zero] at h ⊢
        rw [hold _ h.1, hold _ h.2]
        have := wiresL_snoc_getD (ps.map mkG) (mkG p) x
        rw [List.length_map] at this
        rw [List.map_append, List.map_singleton, this, mkG_eval]

theorem desc_circuit (n : ℕ) (ps : List (Bool × ℕ × ℕ))
    (hps : ∀ k (hk : k < ps.length), ps[k].2.1 < n + k ∧ ps[k].2.2 < n + k)
    (o : ℕ) (ho : o < n + ps.length) :
    ∃ C : Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧ C.output < n + C.size ∧
      PEqualNP.NotBracket.notCount C = 0 ∧ C.size = ps.length ∧
      ∀ x : List Bool, x.length = n → ∃ w : ℕ → Bool, C.eval x = w o ∧
        (∀ i < n, w i = x.getD i false) ∧
        ∀ k (hk : k < ps.length), w (n + k) = opB ps[k].1 (w ps[k].2.1) (w ps[k].2.2) := by
  have hgood : Good n (ps.map mkG) :=
    (circSpec n (List.replicate n false) (by simp) ps hps).1
  refine ⟨⟨ps.map mkG, o⟩, hgood.fanInTwo o, hgood.readsBack o, by simpa [Circuit.size] using ho,
    hgood.notCount o, by simp [Circuit.size], ?_⟩
  intro x hx
  obtain ⟨_, h1, h2⟩ := circSpec n x hx ps hps
  exact ⟨fun i => (wiresL (ps.map mkG) x).getD i false, rfl, h1, h2⟩

def lay {α : Type} (E : α → α → Prop) (s : α) : ℕ → α → Prop
  | 0, v => v = s
  | k + 1, v => lay E s k v ∨ ∃ u, lay E s k u ∧ E u v

theorem lay_mono_le {α : Type} (E : α → α → Prop) (s : α) {j k : ℕ} (hjk : j ≤ k) (v : α)
    (h : lay E s j v) : lay E s k v := by
  induction hjk with
  | refl => exact h
  | step _ ih => exact Or.inl ih

theorem lay_sound {α : Type} (E : α → α → Prop) (s : α) (k : ℕ) :
    ∀ v, lay E s k v → Relation.ReflTransGen E s v := by
  induction k with
  | zero => intro v h; cases h; exact Relation.ReflTransGen.refl
  | succ k ih =>
    intro v h
    rcases h with h | ⟨u, hu, he⟩
    · exact ih v h
    · exact Relation.ReflTransGen.tail (ih u hu) he

theorem lay_closed {α : Type} (E : α → α → Prop) (s : α) (j : ℕ)
    (hst : ∀ v, lay E s (j + 1) v → lay E s j v) (v : α)
    (h : Relation.ReflTransGen E s v) : lay E s j v := by
  induction h with
  | refl => exact lay_mono_le E s (Nat.zero_le j) s rfl
  | tail _ hbc ih => exact hst _ (Or.inr ⟨_, ih, hbc⟩)

theorem lay_iff {α : Type} [Fintype α] (E : α → α → Prop) (s v : α) (k : ℕ)
    (hk : Fintype.card α ≤ k) : lay E s k v ↔ Relation.ReflTransGen E s v := by
  classical
  refine ⟨lay_sound E s k v, fun h => ?_⟩
  have claim : ∀ n, (∃ j ≤ n, ∀ v, lay E s (j + 1) v → lay E s j v) ∨
      n + 1 ≤ (Finset.univ.filter (fun v => lay E s n v)).card := by
    intro n
    induction n with
    | zero =>
      right
      exact Finset.card_pos.mpr ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ s, rfl⟩⟩
    | succ n ih =>
      rcases ih with ⟨j, hj, hst⟩ | hc
      · exact Or.inl ⟨j, Nat.le_succ_of_le hj, hst⟩
      · by_cases hst : ∀ v, lay E s (n + 1) v → lay E s n v
        · exact Or.inl ⟨n, Nat.le_succ n, hst⟩
        · right
          push Not at hst
          obtain ⟨w, h1, h2⟩ := hst
          have hlt : (Finset.univ.filter (fun v => lay E s n v)).card <
              (Finset.univ.filter (fun v => lay E s (n + 1) v)).card := by
            apply Finset.card_lt_card
            rw [Finset.ssubset_iff_of_subset]
            · exact ⟨w, by simpa using h1, by simpa using h2⟩
            · intro u hu
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
              exact Or.inl hu
          omega
  rcases claim (Fintype.card α) with ⟨j, hj, hst⟩ | hc
  · exact lay_mono_le E s (hj.trans hk) v (lay_closed E s j hst v h)
  · have := Finset.card_filter_le (Finset.univ : Finset α)
      (fun v => lay E s (Fintype.card α) v)
    rw [Finset.card_univ] at this
    omega

def Valid (n : ℕ) (ps : List (Bool × ℕ × ℕ)) : Prop :=
  ∀ k (hk : k < ps.length), ps[k].2.1 < n + k ∧ ps[k].2.2 < n + k

def Sat (n : ℕ) (x : List Bool) (ps : List (Bool × ℕ × ℕ)) (w : ℕ → Bool) : Prop :=
  (∀ i < n, w i = x.getD i false) ∧
    ∀ k (hk : k < ps.length), w (n + k) = opB ps[k].1 (w ps[k].2.1) (w ps[k].2.2)

theorem Valid.snoc {n : ℕ} {ps : List (Bool × ℕ × ℕ)} (h : Valid n ps) (p : Bool × ℕ × ℕ)
    (h1 : p.2.1 < n + ps.length) (h2 : p.2.2 < n + ps.length) : Valid n (ps ++ [p]) := by
  intro k hk
  by_cases hlt : k < ps.length
  · have e : (ps ++ [p])[k] = ps[k] := List.getElem_append_left hlt
    rw [e]; exact h k hlt
  · have hk' : k = ps.length := by simp at hk; omega
    subst hk'
    simpa using ⟨h1, h2⟩

theorem Sat.front {n : ℕ} {x : List Bool} {ps qs : List (Bool × ℕ × ℕ)} {w : ℕ → Bool}
    (h : Sat n x (ps ++ qs) w) : Sat n x ps w := by
  refine ⟨h.1, fun k hk => ?_⟩
  have := h.2 k (by simp; omega)
  have e : (ps ++ qs)[k]'(by simp; omega) = ps[k] := List.getElem_append_left hk
  rwa [e] at this

theorem Sat.last {n : ℕ} {x : List Bool} {ps : List (Bool × ℕ × ℕ)} {p : Bool × ℕ × ℕ}
    {w : ℕ → Bool} (h : Sat n x (ps ++ [p]) w) :
    w (n + ps.length) = opB p.1 (w p.2.1) (w p.2.2) := by
  have := h.2 ps.length (by simp)
  simpa using this

theorem build_or_list (n : ℕ) : ∀ (is : List ℕ) (ps : List (Bool × ℕ × ℕ)) (i0 : ℕ),
    Valid n ps → i0 < n + ps.length → (∀ i ∈ is, i < n + ps.length) →
    ∃ (qs : List (Bool × ℕ × ℕ)) (o : ℕ), Valid n (ps ++ qs) ∧ qs.length = is.length ∧
      o < n + (ps ++ qs).length ∧
      ∀ x w, Sat n x (ps ++ qs) w → w o = (w i0 || is.any w) := by
  intro is
  induction is with
  | nil =>
    intro ps i0 hv h0 _
    exact ⟨[], i0, by simpa using hv, rfl, by simpa using h0, by simp⟩
  | cons i is ih =>
    intro ps i0 hv h0 his
    have hv' : Valid n (ps ++ [(false, i0, i)]) :=
      hv.snoc _ h0 (his i (by simp))
    obtain ⟨qs, o, hvq, hlen, ho, hsem⟩ := ih (ps ++ [(false, i0, i)]) (n + ps.length) hv'
      (by simp) (fun j hj => by have := his j (by simp [hj]); simp; omega)
    refine ⟨(false, i0, i) :: qs, o, by simpa using hvq, by simp [hlen], by simpa using ho, ?_⟩
    intro x w hs
    have hs' : Sat n x ((ps ++ [(false, i0, i)]) ++ qs) w := by simpa using hs
    rw [hsem x w hs', hs'.front.last]
    simp [opB, Bool.or_assoc]

theorem build_family (n : ℕ) {ι : Type} (c : ι → ℕ) (F : ι → List Bool → Bool)
    (ps₀ : List (Bool × ℕ × ℕ)) : ∀ (l : List ι),
    (∀ a ∈ l, ∀ t, Valid n (ps₀ ++ t) → ∃ (qs : List (Bool × ℕ × ℕ)) (o : ℕ),
      Valid n (ps₀ ++ t ++ qs) ∧ qs.length ≤ c a ∧ o < n + (ps₀ ++ t ++ qs).length ∧
      ∀ x w, Sat n x (ps₀ ++ t ++ qs) w → w o = F a x) →
    ∀ t, Valid n (ps₀ ++ t) → ∃ (qs : List (Bool × ℕ × ℕ)) (out : ι → ℕ),
      Valid n (ps₀ ++ t ++ qs) ∧ qs.length ≤ (l.map c).sum ∧
      ∀ a ∈ l, out a < n + (ps₀ ++ t ++ qs).length ∧
        ∀ x w, Sat n x (ps₀ ++ t ++ qs) w → w (out a) = F a x := by
  classical
  intro l
  induction l with
  | nil =>
    intro _ t hv
    exact ⟨[], fun _ => 0, by simpa using hv, by simp, by simp⟩
  | cons a l ih =>
    intro hstep t hv
    obtain ⟨qs1, o1, hv1, hc1, ho1, hs1⟩ := hstep a (by simp) t hv
    have hv1' : Valid n (ps₀ ++ (t ++ qs1)) := by simpa [List.append_assoc] using hv1
    obtain ⟨qs2, out2, hv2, hc2, hout2⟩ :=
      ih (fun b hb => hstep b (by simp [hb])) (t ++ qs1) hv1'
    have eqL : ps₀ ++ t ++ (qs1 ++ qs2) = ps₀ ++ (t ++ qs1) ++ qs2 := by
      simp [List.append_assoc]
    have eqL' : ps₀ ++ (t ++ qs1) ++ qs2 = (ps₀ ++ t ++ qs1) ++ qs2 := by
      simp [List.append_assoc]
    refine ⟨qs1 ++ qs2, fun b => if b = a then o1 else out2 b, ?_, ?_, ?_⟩
    · rw [eqL]; exact hv2
    · simp only [List.length_append, List.map_cons, List.sum_cons]; omega
    · intro b hb
      rw [eqL]
      by_cases hba : b = a
      · subst hba
        simp only [↓reduceIte]
        refine ⟨?_, fun x w hs => ?_⟩
        · simp only [List.length_append] at ho1 ⊢; omega
        · rw [eqL'] at hs
          exact hs1 x w hs.front
      · simp only [hba, ↓reduceIte]
        have hb' : b ∈ l := by
          rcases List.mem_cons.mp hb with h | h
          · exact absurd h hba
          · exact h
        exact hout2 b hb'

theorem build_gate (n : ℕ) (ps : List (Bool × ℕ × ℕ)) (b : Bool) (i j : ℕ) (hv : Valid n ps)
    (hi : i < n + ps.length) (hj : j < n + ps.length) :
    ∃ (qs : List (Bool × ℕ × ℕ)) (o : ℕ), Valid n (ps ++ qs) ∧ qs.length = 1 ∧
      o < n + (ps ++ qs).length ∧ ∀ x w, Sat n x (ps ++ qs) w → w o = opB b (w i) (w j) :=
  ⟨[(b, i, j)], n + ps.length, hv.snoc _ hi hj, rfl, by simp, fun _ _ hs => hs.last⟩

theorem build_vertex (n : ℕ) (ps : List (Bool × ℕ × ℕ)) (zi i0 : ℕ) (is : List ℕ)
    (hv : Valid n ps) (hz : zi < n + ps.length) (h0 : i0 < n + ps.length)
    (his : ∀ i ∈ is, i < n + ps.length) :
    ∃ (qs : List (Bool × ℕ × ℕ)) (o : ℕ), Valid n (ps ++ qs) ∧ qs.length = is.length + 1 ∧
      o < n + (ps ++ qs).length ∧
      ∀ x w, Sat n x (ps ++ qs) w → w o = (w zi && (w i0 || is.any w)) := by
  obtain ⟨qs1, o1, hv1, hl1, ho1, hs1⟩ := build_or_list n is ps i0 hv h0 his
  obtain ⟨qs2, o2, hv2, hl2, ho2, hs2⟩ := build_gate n (ps ++ qs1) true zi o1 hv1
    (by simp only [List.length_append]; omega) ho1
  have eqL : ps ++ (qs1 ++ qs2) = ps ++ qs1 ++ qs2 := by simp [List.append_assoc]
  refine ⟨qs1 ++ qs2, o2, by rw [eqL]; exact hv2, by simp [hl1, hl2],
    by rw [eqL]; exact ho2, ?_⟩
  intro x w hs
  rw [eqL] at hs
  rw [hs2 x w hs, hs1 x w hs.front]
  simp [opB]

theorem sum_indeg (m : ℕ) (L : List (Fin m × Fin m)) :
    ∑ v : Fin m, (L.filter (fun e => decide (e.2 = v))).length = L.length := by
  induction L with
  | nil => simp
  | cons e L ih =>
    have h : ∀ v : Fin m, ((e :: L).filter (fun e => decide (e.2 = v))).length =
        (L.filter (fun e => decide (e.2 = v))).length + (if e.2 = v then 1 else 0) := by
      intro v
      by_cases h : e.2 = v <;> simp [h]
    simp only [h, Finset.sum_add_distrib, ih]
    simp

theorem build_round (m : ℕ) (L : List (Fin m × Fin m)) (ps₀ : List (Bool × ℕ × ℕ))
    (hv₀ : Valid (m + 2) ps₀) (r : Fin m → ℕ) (hr : ∀ v, r v < m + 2 + ps₀.length)
    (R : Fin m → List Bool → Bool)
    (hR : ∀ v x w, Sat (m + 2) x ps₀ w → w (r v) = R v x) :
    ∃ (qs : List (Bool × ℕ × ℕ)) (r' : Fin m → ℕ), Valid (m + 2) (ps₀ ++ qs) ∧
      qs.length ≤ m + L.length ∧
      ∀ v, r' v < m + 2 + (ps₀ ++ qs).length ∧
        ∀ x w, Sat (m + 2) x (ps₀ ++ qs) w → w (r' v) =
          (x.getD v false && (R v x || L.any (fun e => decide (e.2 = v) && R e.1 x))) := by
  have key := build_family (m + 2)
    (fun v : Fin m => (L.filter (fun e => decide (e.2 = v))).length + 1)
    (fun v x => (x.getD v false && (R v x || L.any (fun e => decide (e.2 = v) && R e.1 x))))
    ps₀ (List.finRange m) (by
      intro v _ t hvt
      obtain ⟨qs, o, hvq, hl, ho, hs⟩ := build_vertex (m + 2) (ps₀ ++ t) v.val (r v)
        ((L.filter (fun e => decide (e.2 = v))).map (fun e => r e.1)) hvt
        (by have := v.isLt; omega)
        (by have := hr v; simp only [List.length_append]; omega)
        (by
          intro i hi
          obtain ⟨e, _, rfl⟩ := List.mem_map.mp hi
          have := hr e.1; simp only [List.length_append]; omega)
      refine ⟨qs, o, hvq, by simp [hl], ho, ?_⟩
      intro x w hsat
      have hsat0 : Sat (m + 2) x ps₀ w := by
        have : Sat (m + 2) x (ps₀ ++ (t ++ qs)) w := by simpa [List.append_assoc] using hsat
        exact this.front
      have hRw : ∀ u, w (r u) = R u x := fun u => hR u x w hsat0
      have hz : w v.val = x.getD v.val false := hsat.1 v.val (by have := v.isLt; omega)
      rw [hs x w hsat, hz, hRw v]
      simp [List.any_map, List.any_filter, hRw, Function.comp_def]) [] (by simpa using hv₀)
  obtain ⟨qs, r', hvq, hlen, hout⟩ := key
  refine ⟨qs, r', by simpa using hvq, ?_, ?_⟩
  · have hsum := sum_indeg m L
    rw [Fin.sum_univ_def] at hsum
    have : ((List.finRange m).map
        (fun v : Fin m => (L.filter (fun e => decide (e.2 = v))).length + 1)).sum =
        ((List.finRange m).map
          (fun v : Fin m => (L.filter (fun e => decide (e.2 = v))).length)).sum + m := by
      rw [← Fin.sum_univ_def, ← Fin.sum_univ_def, Finset.sum_add_distrib]
      simp
    omega
  · intro v
    simpa using hout v (List.mem_finRange v)

def RK (m : ℕ) (L : List (Fin m × Fin m)) (s : Fin m) : ℕ → Fin m → List Bool → Bool
  | 0, v, x => if v = s then x.getD s false else x.getD m false
  | k + 1, v, x => x.getD v false &&
      (RK m L s k v x || L.any (fun e => decide (e.2 = v) && RK m L s k e.1 x))

theorem build_reach (m : ℕ) (L : List (Fin m × Fin m)) (s : Fin m) : ∀ (k : ℕ)
    (ps₀ : List (Bool × ℕ × ℕ)), Valid (m + 2) ps₀ →
    ∃ (qs : List (Bool × ℕ × ℕ)) (r : Fin m → ℕ), Valid (m + 2) (ps₀ ++ qs) ∧
      qs.length ≤ k * (m + L.length) ∧
      ∀ v, r v < m + 2 + (ps₀ ++ qs).length ∧
        ∀ x w, Sat (m + 2) x (ps₀ ++ qs) w → w (r v) = RK m L s k v x := by
  intro k
  induction k with
  | zero =>
    intro ps₀ hv
    refine ⟨[], fun v => if v = s then s.val else m, by simpa using hv, by simp, ?_⟩
    intro v
    have := s.isLt
    by_cases h : v = s
    · refine ⟨by simp only [h, ↓reduceIte]; omega, fun x w hs => ?_⟩
      simp only [h, ↓reduceIte, RK]
      exact hs.1 _ (by omega)
    · refine ⟨by simp only [h, ↓reduceIte]; omega, fun x w hs => ?_⟩
      simp only [h, ↓reduceIte, RK]
      exact hs.1 _ (by omega)
  | succ k ih =>
    intro ps₀ hv
    obtain ⟨qs1, r1, hv1, hl1, hr1⟩ := ih ps₀ hv
    obtain ⟨qs2, r2, hv2, hl2, hr2⟩ := build_round m L (ps₀ ++ qs1) hv1 r1
      (fun v => (hr1 v).1) (RK m L s k) (fun v x w hs => (hr1 v).2 x w hs)
    have eqL : ps₀ ++ (qs1 ++ qs2) = ps₀ ++ qs1 ++ qs2 := by simp [List.append_assoc]
    refine ⟨qs1 ++ qs2, r2, by rw [eqL]; exact hv2, ?_, ?_⟩
    · simp only [List.length_append, Nat.succ_mul]; omega
    · intro v
      rw [eqL]
      refine ⟨(hr2 v).1, fun x w hs => ?_⟩
      rw [(hr2 v).2 x w hs]
      rfl

theorem getD_z {m : ℕ} (z : Fin m → Bool) (v : Fin m) :
    (List.ofFn z ++ [false, true]).getD v.val false = z v := by
  have h : v.val < (List.ofFn z).length := by simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  simp

theorem getD_m {m : ℕ} (z : Fin m → Bool) :
    (List.ofFn z ++ [false, true]).getD m false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp

theorem getD_m1 {m : ℕ} (z : Fin m → Bool) :
    (List.ofFn z ++ [false, true]).getD (m + 1) false = true := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp

theorem RK_spec (m : ℕ) (L : List (Fin m × Fin m)) (s : Fin m) (z : Fin m → Bool) (k : ℕ) :
    ∀ v, RK m L s k v (List.ofFn z ++ [false, true]) = true ↔
      z s = true ∧ z v = true ∧
        lay (fun u v => (u, v) ∈ L ∧ z u = true ∧ z v = true) s k v := by
  induction k with
  | zero =>
    intro v
    by_cases h : v = s
    · subst h
      simp only [RK, lay, ↓reduceIte, getD_z]
      simp
    · simp only [RK, lay, h, ↓reduceIte, getD_m]
      simp
  | succ k ih =>
    intro v
    simp only [RK, Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq, ih,
      lay, getD_z]
    constructor
    · rintro ⟨hzv, ⟨hs, _, hl⟩ | ⟨e, he, rfl, hs, hu, hl⟩⟩
      · exact ⟨hs, hzv, Or.inl hl⟩
      · exact ⟨hs, hzv, Or.inr ⟨e.1, hl, he, hu, hzv⟩⟩
    · rintro ⟨hs, hzv, hl | ⟨u, hl, he, hu, _⟩⟩
      · exact ⟨hzv, Or.inl ⟨hs, hzv, hl⟩⟩
      · exact ⟨hzv, Or.inr ⟨(u, v), he, rfl, hs, hu, hl⟩⟩

theorem build_warsh_layer (n N k : ℕ) (hk : k < N) (ps₀ : List (Bool × ℕ × ℕ))
    (hv₀ : Valid n ps₀) (T : ℕ → ℕ → ℕ) (Wk : ℕ → ℕ → List Bool → Bool)
    (hT : ∀ i j, i < N → j < N → T i j < n + ps₀.length ∧
      ∀ x w, Sat n x ps₀ w → w (T i j) = Wk i j x) :
    ∃ (qs : List (Bool × ℕ × ℕ)) (T' : ℕ → ℕ → ℕ), Valid n (ps₀ ++ qs) ∧
      qs.length ≤ 2 * N * N ∧
      ∀ i j, i < N → j < N → T' i j < n + (ps₀ ++ qs).length ∧
        ∀ x w, Sat n x (ps₀ ++ qs) w →
          w (T' i j) = (Wk i j x || (Wk i k x && Wk k j x)) := by
  have key := build_family n (fun _ : ℕ × ℕ => 2)
    (fun p x => (Wk p.1 p.2 x || (Wk p.1 k x && Wk k p.2 x)))
    ps₀ ((List.range N).product (List.range N)) (by
      rintro ⟨a, b⟩ hp t hvt
      have hab : a < N ∧ b < N := by simpa using hp
      have hlen : ps₀.length ≤ (ps₀ ++ t).length := by simp
      obtain ⟨qs1, o1, hv1, hl1, ho1, hs1⟩ := build_gate n (ps₀ ++ t) true (T a k) (T k b) hvt
        (by have := (hT a k hab.1 hk).1; omega) (by have := (hT k b hk hab.2).1; omega)
      obtain ⟨qs2, o2, hv2, hl2, ho2, hs2⟩ := build_gate n (ps₀ ++ t ++ qs1) false (T a b) o1 hv1
        (by have := (hT a b hab.1 hab.2).1; simp only [List.length_append] at hlen ⊢; omega) ho1
      have eqL : ps₀ ++ t ++ (qs1 ++ qs2) = ps₀ ++ t ++ qs1 ++ qs2 := by
        simp [List.append_assoc]
      refine ⟨qs1 ++ qs2, o2, by rw [eqL]; exact hv2, by simp [hl1, hl2],
        by rw [eqL]; exact ho2, ?_⟩
      intro x w hsat
      rw [eqL] at hsat
      have hsat0 : Sat n x ps₀ w := by
        have : Sat n x (ps₀ ++ (t ++ qs1 ++ qs2)) w := by simpa [List.append_assoc] using hsat
        exact this.front
      rw [hs2 x w hsat, hs1 x w hsat.front, (hT a b hab.1 hab.2).2 x w hsat0,
        (hT a k hab.1 hk).2 x w hsat0, (hT k b hk hab.2).2 x w hsat0]
      simp [opB]) [] (by simpa using hv₀)
  obtain ⟨qs, out, hvq, hlen, hout⟩ := key
  refine ⟨qs, fun i j => out (i, j), by simpa using hvq, ?_, ?_⟩
  · have : (((List.range N).product (List.range N)).map (fun _ : ℕ × ℕ => 2)).sum = 2 * N * N := by
      have hl : ((List.range N).product (List.range N)).length = N * N := by
        exact (List.length_product (List.range N) (List.range N)).trans (by simp)
      simp only [List.map_const', List.sum_replicate, hl, smul_eq_mul]
      ring
    omega
  · intro i j hi hj
    simpa using hout (i, j) (by simp [hi, hj])

theorem build_warsh (n N : ℕ) (E : ℕ → ℕ → List Bool → Bool) : ∀ (k : ℕ), k ≤ N →
    ∀ (ps₀ : List (Bool × ℕ × ℕ)), Valid n ps₀ → ∀ (T0 : ℕ → ℕ → ℕ),
    (∀ i j, i < N → j < N → T0 i j < n + ps₀.length ∧
      ∀ x w, Sat n x ps₀ w → w (T0 i j) = E i j x) →
    ∃ (qs : List (Bool × ℕ × ℕ)) (T : ℕ → ℕ → ℕ), Valid n (ps₀ ++ qs) ∧
      qs.length ≤ k * (2 * N * N) ∧
      ∀ i j, i < N → j < N → T i j < n + (ps₀ ++ qs).length ∧
        ∀ x w, Sat n x (ps₀ ++ qs) w → w (T i j) = warsh (fun a b => E a b x) k i j := by
  intro k
  induction k with
  | zero =>
    intro _ ps₀ hv T0 hT0
    refine ⟨[], T0, by simpa using hv, by simp, ?_⟩
    intro i j hi hj
    simpa [warsh] using hT0 i j hi hj
  | succ k ih =>
    intro hk ps₀ hv T0 hT0
    obtain ⟨qs1, T1, hv1, hl1, hT1⟩ := ih (Nat.le_of_succ_le hk) ps₀ hv T0 hT0
    obtain ⟨qs2, T2, hv2, hl2, hT2⟩ := build_warsh_layer n N k hk (ps₀ ++ qs1) hv1 T1
      (fun i j x => warsh (fun a b => E a b x) k i j) hT1
    have eqL : ps₀ ++ (qs1 ++ qs2) = ps₀ ++ qs1 ++ qs2 := by simp [List.append_assoc]
    refine ⟨qs1 ++ qs2, T2, by rw [eqL]; exact hv2, ?_, ?_⟩
    · rw [List.length_append, Nat.succ_mul]; exact Nat.add_le_add hl1 hl2
    · intro i j hi hj
      rw [eqL]
      refine ⟨(hT2 i j hi hj).1, fun x w hs => ?_⟩
      rw [(hT2 i j hi hj).2 x w hs]
      rfl

theorem build_allL (n : ℕ) {ι κ : Type} (c : ℕ) (F : ι → κ → List Bool → Bool)
    (ps₀ : List (Bool × ℕ × ℕ))
    (hstep : ∀ a : ι, ∀ t, Valid n (ps₀ ++ t) → ∃ (qs : List (Bool × ℕ × ℕ)) (o : κ → ℕ),
      Valid n (ps₀ ++ t ++ qs) ∧ qs.length ≤ c ∧ ∀ b, o b < n + (ps₀ ++ t ++ qs).length ∧
      ∀ x w, Sat n x (ps₀ ++ t ++ qs) w → w (o b) = F a b x) : ∀ (l : List ι),
    ∀ t, Valid n (ps₀ ++ t) → ∃ (qs : List (Bool × ℕ × ℕ)) (out : ι → κ → ℕ),
      Valid n (ps₀ ++ t ++ qs) ∧ qs.length ≤ l.length * c ∧
      ∀ a ∈ l, ∀ b, out a b < n + (ps₀ ++ t ++ qs).length ∧
        ∀ x w, Sat n x (ps₀ ++ t ++ qs) w → w (out a b) = F a b x := by
  classical
  intro l
  induction l with
  | nil =>
    intro t hv
    exact ⟨[], fun _ _ => 0, by simpa using hv, by simp, by simp⟩
  | cons a l ih =>
    intro t hv
    obtain ⟨qs1, o1, hv1, hc1, ho1⟩ := hstep a t hv
    have hv1' : Valid n (ps₀ ++ (t ++ qs1)) := by simpa [List.append_assoc] using hv1
    obtain ⟨qs2, out2, hv2, hc2, hout2⟩ := ih (t ++ qs1) hv1'
    have eqL : ps₀ ++ t ++ (qs1 ++ qs2) = ps₀ ++ (t ++ qs1) ++ qs2 := by
      simp [List.append_assoc]
    have eqL' : ps₀ ++ (t ++ qs1) ++ qs2 = (ps₀ ++ t ++ qs1) ++ qs2 := by
      simp [List.append_assoc]
    refine ⟨qs1 ++ qs2, fun b => if b = a then o1 else out2 b, ?_, ?_, ?_⟩
    · rw [eqL]; exact hv2
    · rw [List.length_append, List.length_cons, Nat.succ_mul, Nat.add_comm]
      exact Nat.add_le_add hc2 hc1
    · intro b hb k
      rw [eqL]
      by_cases hba : b = a
      · subst hba
        simp only [↓reduceIte]
        refine ⟨?_, fun x w hs => ?_⟩
        · have := (ho1 k).1
          simp only [List.length_append] at this ⊢; omega
        · rw [eqL'] at hs
          exact (ho1 k).2 x w hs.front
      · simp only [hba, ↓reduceIte]
        have hb' : b ∈ l := by
          rcases List.mem_cons.mp hb with h | h
          · exact absurd h hba
          · exact h
        exact hout2 b hb' k

theorem build_all (n : ℕ) {ι κ : Type} [Fintype ι] (c : ℕ) (F : ι → κ → List Bool → Bool)
    (ps₀ : List (Bool × ℕ × ℕ)) (hv₀ : Valid n ps₀)
    (hstep : ∀ a : ι, ∀ t, Valid n (ps₀ ++ t) → ∃ (qs : List (Bool × ℕ × ℕ)) (o : κ → ℕ),
      Valid n (ps₀ ++ t ++ qs) ∧ qs.length ≤ c ∧ ∀ b, o b < n + (ps₀ ++ t ++ qs).length ∧
      ∀ x w, Sat n x (ps₀ ++ t ++ qs) w → w (o b) = F a b x) :
    ∃ (qs : List (Bool × ℕ × ℕ)) (out : ι → κ → ℕ),
      Valid n (ps₀ ++ qs) ∧ qs.length ≤ Fintype.card ι * c ∧
      ∀ a b, out a b < n + (ps₀ ++ qs).length ∧
        ∀ x w, Sat n x (ps₀ ++ qs) w → w (out a b) = F a b x := by
  obtain ⟨qs, out, hv, hl, hout⟩ := build_allL n c F ps₀ hstep
    (Finset.univ : Finset ι).toList [] (by simpa using hv₀)
  refine ⟨qs, out, by simpa using hv, ?_, ?_⟩
  · simpa [Finset.length_toList, Finset.card_univ] using hl
  · intro a b
    simpa using hout a (by simp) b

theorem Valid.nil (n : ℕ) : Valid n [] := by
  intro k hk; simp at hk

def tipF {m : ℕ} (e : Fin m × Fin m) (b : Bool) : Fin m := if b then e.2 else e.1

def badR {m p q : ℕ} (L : List (Fin m × Fin m)) (pe : Fin p → Fin m × Fin m)
    (qe : Fin q → Fin m × Fin m) (z : Fin m → Bool) (e : Fin p) (s : Bool) (f : Fin q)
    (t : Bool) : Prop :=
  (z (pe e).1 = true ∧ z (pe e).2 = true) ∧ (z (qe f).1 = true ∧ z (qe f).2 = true) ∧
    Relation.ReflTransGen (fun i j => (i, j) ∈ L ∧ z i = true ∧ z j = true)
      (tipF (pe e) s) (tipF (qe f) t)

def CL (m : ℕ) {p q : ℕ} (L : List (Fin m × Fin m)) (pe : Fin p → Fin m × Fin m)
    (qe : Fin q → Fin m × Fin m) (e : Fin p) (s : Bool) (f : Fin q) (t : Bool)
    (x : List Bool) : Bool :=
  (RK m L (tipF (pe e) s) m (tipF (qe f) t) x &&
    (x.getD (pe e).1.val false && x.getD (pe e).2.val false)) &&
    (x.getD (qe f).1.val false && x.getD (qe f).2.val false)

theorem CL_spec (m : ℕ) {p q : ℕ} (L : List (Fin m × Fin m)) (pe : Fin p → Fin m × Fin m)
    (qe : Fin q → Fin m × Fin m) (z : Fin m → Bool) (e : Fin p) (s : Bool) (f : Fin q)
    (t : Bool) :
    CL m L pe qe e s f t (List.ofFn z ++ [false, true]) = true ↔ badR L pe qe z e s f t := by
  simp only [CL, Bool.and_eq_true, getD_z, RK_spec,
    lay_iff _ _ _ m (by simp : Fintype.card (Fin m) ≤ m)]
  unfold badR
  constructor
  · rintro ⟨⟨⟨_, _, h⟩, hp⟩, hq⟩
    exact ⟨hp, hq, h⟩
  · rintro ⟨hp, hq, h⟩
    refine ⟨⟨⟨?_, ?_, h⟩, hp⟩, hq⟩
    · cases s <;> simp [tipF, hp.1, hp.2]
    · cases t <;> simp [tipF, hq.1, hq.2]

theorem build_clauses (m p q : ℕ) (L : List (Fin m × Fin m)) (pe : Fin p → Fin m × Fin m)
    (qe : Fin q → Fin m × Fin m) :
    ∃ (ps : List (Bool × ℕ × ℕ)) (cw : Fin p × Bool → Fin q × Bool → ℕ), Valid (m + 2) ps ∧
      ps.length ≤ (p * 2) * (m * (m + L.length)) + (p + q) + (p * 2 * (q * 2)) * 2 ∧
      ∀ a b, cw a b < m + 2 + ps.length ∧
        ∀ x w, Sat (m + 2) x ps w → w (cw a b) = CL m L pe qe a.1 a.2 b.1 b.2 x := by

  obtain ⟨qsA, rA, hvA, hlA, hA⟩ := build_all (m + 2) (ι := Fin p × Bool) (κ := Fin m)
    (m * (m + L.length)) (fun a v x => RK m L (tipF (pe a.1) a.2) m v x) [] (Valid.nil _)
    (fun a t hvt => by
      obtain ⟨qs, r, h1, h2, h3⟩ := build_reach m L (tipF (pe a.1) a.2) m ([] ++ t) hvt
      exact ⟨qs, r, h1, h2, h3⟩)
  simp only [List.nil_append, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at hvA hlA hA

  obtain ⟨qsB, lv, hvB, hlB, hB⟩ := build_all (m + 2) (ι := Fin p ⊕ Fin q) (κ := Unit) 1
    (fun a _ x => (x.getD (Sum.elim pe qe a).1.val false && x.getD (Sum.elim pe qe a).2.val false))
    qsA hvA
    (fun a t hvt => by
      have h1 := (Sum.elim pe qe a).1.isLt
      have h2 := (Sum.elim pe qe a).2.isLt
      obtain ⟨qs, o, hv, hl, ho, hs⟩ := build_gate (m + 2) (qsA ++ t) true
        (Sum.elim pe qe a).1.val (Sum.elim pe qe a).2.val hvt (by omega) (by omega)
      refine ⟨qs, fun _ => o, hv, by omega, fun _ => ⟨ho, fun x w hsat => ?_⟩⟩
      rw [hs x w hsat, hsat.1 _ (by omega), hsat.1 _ (by omega)]
      rfl)
  simp only [Fintype.card_sum, Fintype.card_fin, Nat.mul_one] at hlB

  obtain ⟨qsC, cw, hvC, hlC, hC⟩ := build_all (m + 2) (ι := (Fin p × Bool) × (Fin q × Bool))
    (κ := Unit) 2
    (fun ab _ x => CL m L pe qe ab.1.1 ab.1.2 ab.2.1 ab.2.2 x) (qsA ++ qsB) hvB
    (fun ab t hvt => by
      have hlen : (qsA ++ qsB).length ≤ (qsA ++ qsB ++ t).length := by simp
      have hlenA : qsA.length ≤ (qsA ++ qsB).length := by simp
      obtain ⟨qs1, o1, hv1, hl1, ho1, hs1⟩ := build_gate (m + 2) (qsA ++ qsB ++ t) true
        (rA ab.1 (tipF (qe ab.2.1) ab.2.2)) (lv (Sum.inl ab.1.1) ()) hvt
        (by have := (hA ab.1 (tipF (qe ab.2.1) ab.2.2)).1; omega)
        (by have := (hB (Sum.inl ab.1.1) ()).1; omega)
      obtain ⟨qs2, o2, hv2, hl2, ho2, hs2⟩ := build_gate (m + 2) (qsA ++ qsB ++ t ++ qs1) true
        o1 (lv (Sum.inr ab.2.1) ()) hv1 ho1
        (by have := (hB (Sum.inr ab.2.1) ()).1; simp only [List.length_append] at this ⊢; omega)
      have eqL : qsA ++ qsB ++ t ++ (qs1 ++ qs2) = qsA ++ qsB ++ t ++ qs1 ++ qs2 := by
        simp [List.append_assoc]
      refine ⟨qs1 ++ qs2, fun _ => o2, by rw [eqL]; exact hv2, by simp [hl1, hl2],
        fun _ => ⟨by rw [eqL]; exact ho2, fun x w hsat => ?_⟩⟩
      rw [eqL] at hsat
      have hsatB : Sat (m + 2) x (qsA ++ qsB) w := by
        have : Sat (m + 2) x (qsA ++ qsB ++ (t ++ qs1 ++ qs2)) w := by
          simpa [List.append_assoc] using hsat
        exact this.front
      rw [hs2 x w hsat, hs1 x w hsat.front, (hA _ _).2 x w hsatB.front,
        (hB _ _).2 x w hsatB, (hB _ _).2 x w hsatB]
      rfl)
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at hlC
  refine ⟨qsA ++ qsB ++ qsC, fun a b => cw (a, b) (), hvC, ?_, fun a b => hC (a, b) ()⟩
  simp only [List.length_append]
  omega

theorem transGen_enc {Λ : Type} (enc : Λ → ℕ) (hinj : Function.Injective enc)
    (R : Λ → Λ → Prop) (EN : ℕ → ℕ → Prop)
    (hE : ∀ a b, EN a b ↔ ∃ l l', enc l = a ∧ enc l' = b ∧ R l l') (l l' : Λ) :
    Relation.TransGen EN (enc l) (enc l') ↔ Relation.TransGen R l l' := by
  constructor
  · intro h
    have key : ∀ a b, Relation.TransGen EN a b → ∀ l, enc l = a →
        ∃ l', enc l' = b ∧ Relation.TransGen R l l' := by
      intro a b h
      induction h with
      | single hab =>
        intro l hl
        obtain ⟨l1, l2, h1, h2, hr⟩ := (hE _ _).1 hab
        have : l1 = l := hinj (h1.trans hl.symm)
        subst this
        exact ⟨l2, h2, Relation.TransGen.single hr⟩
      | tail _ hbc ih =>
        intro l hl
        obtain ⟨lb, hb, hlb⟩ := ih l hl
        obtain ⟨l1, l2, h1, h2, hr⟩ := (hE _ _).1 hbc
        have : l1 = lb := hinj (h1.trans hb.symm)
        subst this
        exact ⟨l2, h2, Relation.TransGen.tail hlb hr⟩
    obtain ⟨l2, h2, hr⟩ := key _ _ h l rfl
    have : l2 = l' := hinj h2
    subst this
    exact hr
  · intro h
    induction h with
    | single hab => exact Relation.TransGen.single ((hE _ _).2 ⟨_, _, rfl, rfl, hab⟩)
    | tail _ hbc ih => exact Relation.TransGen.tail ih ((hE _ _).2 ⟨_, _, rfl, rfl, hbc⟩)

def vi {p q : ℕ} : Fin p ⊕ Fin q → ℕ
  | Sum.inl e => e.val
  | Sum.inr f => p + f.val

def enc {p q : ℕ} (l : (Fin p ⊕ Fin q) × Bool) : ℕ := 2 * vi l.1 + l.2.toNat

theorem vi_lt {p q : ℕ} (v : Fin p ⊕ Fin q) : vi v < p + q := by
  cases v with
  | inl e => have := e.isLt; simp only [vi]; omega
  | inr f => have := f.isLt; simp only [vi]; omega

theorem vi_inj {p q : ℕ} : Function.Injective (vi : Fin p ⊕ Fin q → ℕ) := by
  intro a b h
  cases a with
  | inl e =>
    cases b with
    | inl e' => simp only [vi] at h; rw [Fin.ext h]
    | inr f' => have := e.isLt; simp only [vi] at h; omega
  | inr f =>
    cases b with
    | inl e' => have := e'.isLt; simp only [vi] at h; omega
    | inr f' =>
      simp only [vi] at h
      have : f = f' := Fin.ext (by omega)
      rw [this]

theorem enc_inj {p q : ℕ} : Function.Injective (enc : (Fin p ⊕ Fin q) × Bool → ℕ) := by
  rintro ⟨v, s⟩ ⟨v', s'⟩ h
  simp only [enc] at h
  have h2 : vi v = vi v' ∧ s = s' := by
    cases s <;> cases s' <;> simp only [Bool.toNat_false, Bool.toNat_true] at h <;>
      first | exact ⟨by omega, rfl⟩ | omega
  rw [vi_inj h2.1, h2.2]

theorem enc_lt {p q : ℕ} (l : (Fin p ⊕ Fin q) × Bool) : enc l < 2 * (p + q) := by
  have := vi_lt l.1
  have h2 : l.2.toNat ≤ 1 := Bool.toNat_le l.2
  simp only [enc]; omega

theorem dec_div (v : ℕ) (s : Bool) : (2 * v + s.toNat) / 2 = v := by
  cases s <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

theorem dec_mod (v : ℕ) (s : Bool) : ((2 * v + s.toNat) % 2 == 1) = s := by
  cases s
  · have : (2 * v + 0) % 2 = 0 := by omega
    simp [this]
  · have : (2 * v + 1) % 2 = 1 := by omega
    simp [this]

theorem enc_dec (i : ℕ) : 2 * (i / 2) + (i % 2 == 1).toNat = i := by
  rcases Nat.mod_two_eq_zero_or_one i with h | h
  · simp only [h]; simp; omega
  · simp only [h]; simp; omega

def ext {β : Type} (p q : ℕ) (g : Fin p × Bool → Fin q × Bool → β) (d : β) (e : ℕ) (s : Bool)
    (f : ℕ) (t : Bool) : β :=
  if h : e < p ∧ f < q then g (⟨e, h.1⟩, s) (⟨f, h.2⟩, t) else d

def sel {β : Type} (p q : ℕ) (g : ℕ → Bool → ℕ → Bool → β) (d : β) (i j : ℕ) : β :=
  if i < 2 * p ∧ 2 * p ≤ j ∧ j < 2 * (p + q) then
    g (i / 2) (i % 2 == 1) ((j - 2 * p) / 2) (!(j % 2 == 1))
  else if 2 * p ≤ i ∧ i < 2 * (p + q) ∧ j < 2 * p then
    g (j / 2) (!(j % 2 == 1)) ((i - 2 * p) / 2) (i % 2 == 1)
  else d

theorem sel_map {β γ : Type} (φ : β → γ) (p q : ℕ) (g : Fin p × Bool → Fin q × Bool → β)
    (d : β) (i j : ℕ) :
    φ (sel p q (ext p q g d) d i j) =
      sel p q (ext p q (fun a b => φ (g a b)) (φ d)) (φ d) i j := by
  unfold sel ext
  split_ifs <;> rfl

theorem sel_prop {β : Type} (P : β → Prop) (p q : ℕ) (g : Fin p × Bool → Fin q × Bool → β)
    (d : β) (hd : P d) (hg : ∀ a b, P (g a b)) (i j : ℕ) : P (sel p q (ext p q g d) d i j) := by
  unfold sel ext
  split_ifs <;> first | exact hd | exact hg _ _

theorem sel_edge (p q : ℕ) (G : Fin p × Bool → Fin q × Bool → Bool)
    (bad : Fin p → Bool → Fin q → Bool → Prop)
    (hG : ∀ a b, G a b = true ↔ bad a.1 a.2 b.1 b.2) (i j : ℕ) :
    sel p q (ext p q G false) false i j = true ↔
      ∃ l l' : (Fin p ⊕ Fin q) × Bool, enc l = i ∧ enc l' = j ∧ Imp bad l l' := by
  constructor
  · unfold sel
    split_ifs with h1 h2
    · intro hg
      have hb : i / 2 < p ∧ (j - 2 * p) / 2 < q := by omega
      unfold ext at hg
      rw [dif_pos hb] at hg
      have hbad := (hG _ _).1 hg
      refine ⟨(Sum.inl ⟨i / 2, hb.1⟩, i % 2 == 1),
        (Sum.inr ⟨(j - 2 * p) / 2, hb.2⟩, !!(j % 2 == 1)), enc_dec i, ?_,
        Imp.pq _ _ _ _ hbad⟩
      have := enc_dec j
      simp only [enc, vi, Bool.not_not]
      omega
    · intro hg
      have hb : j / 2 < p ∧ (i - 2 * p) / 2 < q := by omega
      unfold ext at hg
      rw [dif_pos hb] at hg
      have hbad := (hG _ _).1 hg
      refine ⟨(Sum.inr ⟨(i - 2 * p) / 2, hb.2⟩, i % 2 == 1),
        (Sum.inl ⟨j / 2, hb.1⟩, !!(j % 2 == 1)), ?_, ?_, Imp.qp _ _ _ _ hbad⟩
      · have := enc_dec i
        simp only [enc, vi]
        omega
      · have := enc_dec j
        simp only [enc, vi, Bool.not_not]
        omega
    · intro h; cases h
  · rintro ⟨l, l', rfl, rfl, h⟩
    cases h with
    | pq e s f t hb =>
      have he := e.isLt
      have hf := f.isLt
      have hs1 := Bool.toNat_le s
      have ht1 := Bool.toNat_le (!t)
      have a1 := dec_div e.val s
      have a2 := dec_mod e.val s
      have a3 : (2 * (p + f.val) + (!t).toNat - 2 * p) / 2 = f.val := by omega
      have a4 := dec_mod (p + f.val) (!t)
      simp only [enc, vi]
      unfold sel
      rw [if_pos (by omega), a1, a2, a3, a4, Bool.not_not]
      unfold ext
      rw [dif_pos ⟨he, hf⟩]
      exact (hG _ _).2 hb
    | qp e s f t hb =>
      have he := e.isLt
      have hf := f.isLt
      have hs1 := Bool.toNat_le (!s)
      have ht1 := Bool.toNat_le t
      have a1 := dec_div e.val (!s)
      have a2 := dec_mod e.val (!s)
      have a3 : (2 * (p + f.val) + t.toNat - 2 * p) / 2 = f.val := by omega
      have a4 := dec_mod (p + f.val) t
      simp only [enc, vi]
      unfold sel
      rw [if_neg (by omega), if_pos (by omega), a1, a2, a3, a4, Bool.not_not]
      unfold ext
      rw [dif_pos ⟨he, hf⟩]
      exact (hG _ _).2 hb

theorem vi_surj {p q : ℕ} (v : ℕ) (hv : v < p + q) : ∃ u : Fin p ⊕ Fin q, vi u = v := by
  by_cases h : v < p
  · exact ⟨Sum.inl ⟨v, h⟩, rfl⟩
  · exact ⟨Sum.inr ⟨v - p, by omega⟩, by simp only [vi]; omega⟩

theorem loops_iff (p q : ℕ) (G : Fin p × Bool → Fin q × Bool → Bool)
    (bad : Fin p → Bool → Fin q → Bool → Prop)
    (hG : ∀ a b, G a b = true ↔ bad a.1 a.2 b.1 b.2) :
    (∃ v, v < p + q ∧
      warsh (sel p q (ext p q G false) false) (2 * (p + q)) (2 * v + 1) (2 * v) = true ∧
      warsh (sel p q (ext p q G false) false) (2 * (p + q)) (2 * v) (2 * v + 1) = true) ↔
    ∃ v : Fin p ⊕ Fin q, Relation.ReflTransGen (Imp bad) (v, true) (v, false) ∧
      Relation.ReflTransGen (Imp bad) (v, false) (v, true) := by
  have hedge := sel_edge p q G bad hG
  have hE : ∀ a b, sel p q (ext p q G false) false a b = true →
      a < 2 * (p + q) ∧ b < 2 * (p + q) := by
    intro a b h
    obtain ⟨l, l', rfl, rfl, _⟩ := (hedge a b).1 h
    exact ⟨enc_lt l, enc_lt l'⟩
  have hT : ∀ l l' : (Fin p ⊕ Fin q) × Bool,
      warsh (sel p q (ext p q G false) false) (2 * (p + q)) (enc l) (enc l') = true ↔
        Relation.TransGen (Imp bad) l l' := fun l l' =>
    (warsh_iff _ _ hE _ _).trans
      (transGen_enc enc enc_inj (Imp bad)
        (fun a b => sel p q (ext p q G false) false a b = true) hedge l l')
  have hR1 : ∀ v : Fin p ⊕ Fin q, Relation.ReflTransGen (Imp bad) (v, true) (v, false) ↔
      Relation.TransGen (Imp bad) (v, true) (v, false) := by
    intro v
    rw [Relation.reflTransGen_iff_eq_or_transGen]
    simp
  have hR2 : ∀ v : Fin p ⊕ Fin q, Relation.ReflTransGen (Imp bad) (v, false) (v, true) ↔
      Relation.TransGen (Imp bad) (v, false) (v, true) := by
    intro v
    rw [Relation.reflTransGen_iff_eq_or_transGen]
    simp
  have e1 : ∀ v : Fin p ⊕ Fin q, enc (v, true) = 2 * vi v + 1 := fun v => by simp [enc]
  have e0 : ∀ v : Fin p ⊕ Fin q, enc (v, false) = 2 * vi v := fun v => by simp [enc]
  constructor
  · rintro ⟨v, hv, h1, h2⟩
    obtain ⟨u, rfl⟩ := vi_surj (p := p) (q := q) v hv
    rw [← e1, ← e0, hT] at h1
    rw [← e1, ← e0, hT] at h2
    exact ⟨u, (hR1 u).2 h1, (hR2 u).2 h2⟩
  · rintro ⟨u, h1, h2⟩
    refine ⟨vi u, vi_lt u, ?_, ?_⟩
    · rw [← e1, ← e0, hT]; exact (hR1 u).1 h1
    · rw [← e1, ← e0, hT]; exact (hR2 u).1 h2

theorem core (m p q : ℕ) (L : List (Fin m × Fin m)) (pe : Fin p → Fin m × Fin m)
    (qe : Fin q → Fin m × Fin m) :
    ∃ C : Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (m + 2) C ∧ C.output < m + 2 + C.size ∧
      PEqualNP.NotBracket.notCount C = 0 ∧
      C.size ≤ 2 * p * m * (m + L.length) + 16 * (p + q) ^ 3 + 8 * p * q + 3 * (p + q) ∧
      ∀ z : Fin m → Bool, C.eval (List.ofFn z ++ [false, true]) = true ↔
        ¬ ∃ (a : Fin p → Bool) (b : Fin q → Bool), ∀ e f, ¬ badR L pe qe z e (a e) f (b f) := by
  obtain ⟨ps1, cw, hv1, hl1, hcw⟩ := build_clauses m p q L pe qe
  have hT0 : ∀ i j, i < 2 * (p + q) → j < 2 * (p + q) →
      sel p q (ext p q cw m) m i j < m + 2 + ps1.length ∧
      ∀ x w, Sat (m + 2) x ps1 w → w (sel p q (ext p q cw m) m i j) =
        sel p q (ext p q (fun a b => CL m L pe qe a.1 a.2 b.1 b.2 x) (x.getD m false))
          (x.getD m false) i j := by
    intro i j _ _
    refine ⟨sel_prop (fun k => k < m + 2 + ps1.length) p q cw m (by omega)
      (fun a b => (hcw a b).1) i j, fun x w hs => ?_⟩
    rw [sel_map w]
    have h1 : (fun a b => w (cw a b)) = fun a b => CL m L pe qe a.1 a.2 b.1 b.2 x :=
      funext fun a => funext fun b => (hcw a b).2 x w hs
    rw [h1, hs.1 m (by omega)]
  obtain ⟨qs2, T, hv2, hl2, hT⟩ := build_warsh (m + 2) (2 * (p + q))
    (fun i j x => sel p q (ext p q (fun a b => CL m L pe qe a.1 a.2 b.1 b.2 x) (x.getD m false))
      (x.getD m false) i j) (2 * (p + q)) (Nat.le_refl _) ps1 hv1
    (fun i j => sel p q (ext p q cw m) m i j) hT0
  obtain ⟨qs3, dv, hv3, hl3, hD⟩ := build_all (m + 2) (ι := Fin (p + q)) (κ := Unit) 1
    (fun v _ x =>
      (warsh (fun a b => sel p q (ext p q (fun a b => CL m L pe qe a.1 a.2 b.1 b.2 x)
          (x.getD m false)) (x.getD m false) a b) (2 * (p + q)) (2 * v.val + 1) (2 * v.val) &&
        warsh (fun a b => sel p q (ext p q (fun a b => CL m L pe qe a.1 a.2 b.1 b.2 x)
          (x.getD m false)) (x.getD m false) a b) (2 * (p + q)) (2 * v.val) (2 * v.val + 1)))
    (ps1 ++ qs2) hv2
    (fun v t hvt => by
      have hvlt := v.isLt
      have hlen : (ps1 ++ qs2).length ≤ (ps1 ++ qs2 ++ t).length := by simp
      have b1 := hT (2 * v.val + 1) (2 * v.val) (by omega) (by omega)
      have b2 := hT (2 * v.val) (2 * v.val + 1) (by omega) (by omega)
      obtain ⟨qs, o, hv, hl, ho, hs⟩ := build_gate (m + 2) (ps1 ++ qs2 ++ t) true
        (T (2 * v.val + 1) (2 * v.val)) (T (2 * v.val) (2 * v.val + 1)) hvt
        (by have := b1.1; omega) (by have := b2.1; omega)
      refine ⟨qs, fun _ => o, hv, by omega, fun _ => ⟨ho, fun x w hsat => ?_⟩⟩
      have hsat0 : Sat (m + 2) x (ps1 ++ qs2) w := by
        have : Sat (m + 2) x (ps1 ++ qs2 ++ (t ++ qs)) w := by
          simpa [List.append_assoc] using hsat
        exact this.front
      rw [hs x w hsat, b1.2 x w hsat0, b2.2 x w hsat0]
      rfl)
  simp only [Fintype.card_fin, Nat.mul_one] at hl3
  obtain ⟨qs4, o, hv4, hl4, ho, hsem⟩ := build_or_list (m + 2)
    ((List.finRange (p + q)).map (fun v => dv v ())) (ps1 ++ qs2 ++ qs3) m hv3 (by omega)
    (by
      intro i hi
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hi
      exact (hD v ()).1)
  simp only [List.length_map, List.length_finRange] at hl4
  obtain ⟨C, hC1, hC2, hC3, hC4, hC5, hC6⟩ :=
    desc_circuit (m + 2) (ps1 ++ qs2 ++ qs3 ++ qs4) hv4 o ho
  refine ⟨C, hC1, hC2, hC3, hC4, ?_, ?_⟩
  · have hsz : (ps1 ++ qs2 ++ qs3 ++ qs4).length ≤
        ((p * 2) * (m * (m + L.length)) + (p + q) + (p * 2 * (q * 2)) * 2) +
          2 * (p + q) * (2 * (2 * (p + q)) * (2 * (p + q))) + (p + q) + (p + q) := by
      simp only [List.length_append]
      omega
    rw [hC5]
    refine hsz.trans (le_of_eq ?_)
    ring
  · intro z
    obtain ⟨w, hev, hin, hgates⟩ := hC6 (List.ofFn z ++ [false, true]) (by simp)
    have hsat : Sat (m + 2) (List.ofFn z ++ [false, true]) (ps1 ++ qs2 ++ qs3 ++ qs4) w :=
      ⟨hin, hgates⟩
    have hsat3 : Sat (m + 2) (List.ofFn z ++ [false, true]) (ps1 ++ qs2 ++ qs3) w := hsat.front
    have hG : ∀ (a : Fin p × Bool) (b : Fin q × Bool),
        CL m L pe qe a.1 a.2 b.1 b.2 (List.ofFn z ++ [false, true]) = true ↔
          badR L pe qe z a.1 a.2 b.1 b.2 := fun a b => CL_spec m L pe qe z a.1 a.2 b.1 b.2
    have hloop := loops_iff p q
      (fun a b => CL m L pe qe a.1 a.2 b.1 b.2 (List.ofFn z ++ [false, true]))
      (badR L pe qe z) hG
    have hch := choice_iff (badR L pe qe z)
    rw [hev, hsem _ w hsat, hin m (by omega), getD_m, Bool.false_or, hch, not_forall_not,
      ← hloop, List.any_eq_true]
    constructor
    · rintro ⟨i, hi, hw⟩
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hi
      rw [(hD v ()).2 _ w hsat3] at hw
      simp only [getD_m, Bool.and_eq_true] at hw
      exact ⟨v.val, v.isLt, hw.1, hw.2⟩
    · rintro ⟨v, hv, h1, h2⟩
      refine ⟨dv ⟨v, hv⟩ (), List.mem_map.mpr ⟨⟨v, hv⟩, List.mem_finRange _, rfl⟩, ?_⟩
      rw [(hD ⟨v, hv⟩ ()).2 _ w hsat3]
      simp only [getD_m, Bool.and_eq_true]
      exact ⟨h1, h2⟩

theorem badR_swap {m p q : ℕ} (L : List (Fin m × Fin m)) (pe : Fin p → Fin m × Fin m)
    (qe : Fin q → Fin m × Fin m) (z : Fin m → Bool) (e : Fin p) (s : Bool) (f : Fin q)
    (t : Bool) :
    badR (L.map Prod.swap) qe pe z f t e s ↔ badR L pe qe z e s f t := by
  have hrel : (fun i j => (i, j) ∈ L.map Prod.swap ∧ z i = true ∧ z j = true) =
      Function.swap (fun i j => (i, j) ∈ L ∧ z i = true ∧ z j = true) := by
    funext i j
    apply propext
    simp only [Function.swap, List.mem_map, Prod.exists, Prod.swap_prod_mk, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨a, b, hab, rfl, rfl⟩, hi, hj⟩
      exact ⟨hab, hj, hi⟩
    · rintro ⟨hab, hj, hi⟩
      exact ⟨⟨j, i, hab, rfl, rfl⟩, hi, hj⟩
  unfold badR
  rw [hrel, Relation.reflTransGen_swap]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1, h3⟩

theorem circuit_main (m p q : ℕ) (L : List (Fin m × Fin m)) (pe : Fin p → Fin m × Fin m)
    (qe : Fin q → Fin m × Fin m) :
    ∃ C : Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (m + 2) C ∧ C.output < m + 2 + C.size ∧
      PEqualNP.NotBracket.notCount C = 0 ∧
      C.size ≤ 2 * min p q * m * (m + L.length) + 16 * (p + q) ^ 3 + 8 * p * q + 3 * (p + q) ∧
      ∀ z : Fin m → Bool, C.eval (List.ofFn z ++ [false, true]) = true ↔
        ¬ ∃ (a : Fin p → Bool) (b : Fin q → Bool), ∀ e f, ¬ badR L pe qe z e (a e) f (b f) := by
  by_cases hpq : p ≤ q
  · obtain ⟨C, h1, h2, h3, h4, h5, h6⟩ := core m p q L pe qe
    exact ⟨C, h1, h2, h3, h4, by rw [Nat.min_eq_left hpq]; exact h5, h6⟩
  · obtain ⟨C, h1, h2, h3, h4, h5, h6⟩ := core m q p (L.map Prod.swap) qe pe
    refine ⟨C, h1, h2, h3, h4, ?_, ?_⟩
    · rw [Nat.min_eq_right (by omega)]
      rw [List.length_map] at h5
      refine h5.trans (le_of_eq ?_)
      ring
    · intro z
      rw [h6 z]
      apply not_congr
      constructor
      · rintro ⟨a, b, h⟩
        exact ⟨b, a, fun e f hb => h f e ((badR_swap L pe qe z e (b e) f (a f)).2 hb)⟩
      · rintro ⟨a, b, h⟩
        exact ⟨b, a, fun f e hb => h e f ((badR_swap L pe qe z e (a e) f (b f)).1 hb)⟩

theorem bridge (m : ℕ) (D P Q : Finset (Fin m × Fin m)) (z : Fin m → Bool) :
    (∃ (a : Fin P.card → Bool) (b : Fin Q.card → Bool), ∀ e f,
      ¬ badR D.toList (fun i => (P.equivFin.symm i).val) (fun i => (Q.equivFin.symm i).val) z
        e (a e) f (b f)) ↔
    ∃ (a : ↥P → Bool) (b : ↥Q → Bool), ∀ (e : ↥P) (f : ↥Q),
      (z e.val.1 = true ∧ z e.val.2 = true) → (z f.val.1 = true ∧ z f.val.2 = true) →
      ¬ Relation.ReflTransGen (fun i j => (i, j) ∈ D ∧ z i = true ∧ z j = true)
        (if a e then e.val.2 else e.val.1) (if b f then f.val.2 else f.val.1) := by
  have hrel : (fun i j => (i, j) ∈ D.toList ∧ z i = true ∧ z j = true) =
      (fun i j => (i, j) ∈ D ∧ z i = true ∧ z j = true) := by
    funext i j; simp
  simp only [badR, tipF, hrel]
  constructor
  · rintro ⟨a, b, h⟩
    refine ⟨fun e => a (P.equivFin e), fun f => b (Q.equivFin f), ?_⟩
    intro e f hle hlf hr
    apply h (P.equivFin e) (Q.equivFin f)
    simp only [Equiv.symm_apply_apply]
    exact ⟨hle, hlf, hr⟩
  · rintro ⟨a, b, h⟩
    refine ⟨fun e => a (P.equivFin.symm e), fun f => b (Q.equivFin.symm f), ?_⟩
    rintro e f ⟨hle, hlf, hr⟩
    exact h _ _ hle hlf hr

end PEqualNP.Outside.L_lib_1192

theorem PEqualNP.Outside.L_lib_1192 : ∀ (m : Nat) (D P Q : Finset (Fin m × Fin m)),
  (∀ e ∈ P ∪ Q, e.1 < e.2) →
  let pair := fun (x : Fin m → Bool → Bool) (i : Fin m) => x i false = true ∨ x i true = true
  let cover := fun (x : Fin m → Bool → Bool) =>
    (∀ i, pair x i) ∧
    (∀ e ∈ D, x e.1 true = true ∨ x e.2 false = true) ∧
    (∀ e ∈ P, x e.1 false = true ∨ x e.2 false = true) ∧
    (∀ e ∈ Q, x e.1 true = true ∨ x e.2 true = true)
  let feasible := fun (z : Fin m → Bool) => ∃ x, cover x ∧
    ∀ i, xor (x i false) (x i true) = z i
  let tip := fun (e : Fin m × Fin m) (b : Bool) => if b then e.2 else e.1
  let live := fun (z : Fin m → Bool) (e : Fin m × Fin m) => z e.1 = true ∧ z e.2 = true
  let reach := fun (z : Fin m → Bool) => Relation.ReflTransGen
    (fun (i j : Fin m) => (i,j) ∈ D ∧ z i = true ∧ z j = true)
  let h := P.card + Q.card
  (∀ z, feasible z ↔ ∃ (a : ↥P → Bool) (b : ↥Q → Bool),
    ∀ e f, live z e.val → live z f.val → ¬ reach z (tip e.val (a e)) (tip f.val (b f))) ∧
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (m+2) C ∧ C.output < m+2+C.size ∧
    PEqualNP.NotBracket.notCount C = 0 ∧
    C.size ≤ 2 * min P.card Q.card * m * (m + D.card) +
      16 * h^3 + 8 * P.card * Q.card + 3*h ∧
    ∀ z, C.eval (List.ofFn z ++ [false,true]) = true ↔ ¬ feasible z := by
  classical
  intro m D P Q _hlt pair cover feasible tip live reach h
  have part1 : ∀ z, feasible z ↔ ∃ (a : ↥P → Bool) (b : ↥Q → Bool),
      ∀ e f, live z e.val → live z f.val → ¬ reach z (tip e.val (a e)) (tip f.val (b f)) := by
    intro z
    constructor
    · rintro ⟨x, ⟨_hpair, hD, hP, hQ⟩, hx⟩
      refine ⟨fun e => if x e.val.1 false = true then false else true,
        fun f => if x f.val.1 true = true then false else true, ?_⟩
      intro e f _hle hlf hr
      have hstart : x (tip e.val (if x e.val.1 false = true then false else true)) false = true := by
        by_cases h1 : x e.val.1 false = true
        · simp [tip, h1]
        · have := hP e.val e.property
          simpa [tip, h1] using this
      have hend : x (tip f.val (if x f.val.1 true = true then false else true)) true = true := by
        by_cases h1 : x f.val.1 true = true
        · simp [tip, h1]
        · have := hQ f.val f.property
          simpa [tip, h1] using this
      have hzend : z (tip f.val (if x f.val.1 true = true then false else true)) = true := by
        by_cases h1 : x f.val.1 true = true
        · simpa [tip, h1] using hlf.1
        · simpa [tip, h1] using hlf.2
      have key : ∀ u v, reach z u v → x u false = true → x v false = true := by
        intro u v huv
        induction huv with
        | refl => exact id
        | @tail p q _ hstep ih =>
          intro hu
          have hi := ih hu
          obtain ⟨hmem, hzi, _⟩ := hstep
          have hxi := hx p
          rw [hi, hzi] at hxi
          rcases hD (p, q) hmem with h2 | h2
          · have h2' : x p true = true := h2
            rw [h2'] at hxi; simp at hxi
          · exact h2
      have hfin := key _ _ hr hstart
      have hxv := hx (tip f.val (if x f.val.1 true = true then false else true))
      rw [hfin, hend, hzend] at hxv
      simp at hxv
    · rintro ⟨a, b, hab⟩
      let S : Fin m → Prop := fun v => ∃ e : ↥P, live z e.val ∧ reach z (tip e.val (a e)) v
      refine ⟨fun i s => decide (z i = false ∨ (S i ↔ s = false)), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
      · intro i
        by_cases hS : S i <;> simp [pair, hS]
      · intro e he
        by_cases hz1 : z e.1 = true
        · by_cases hz2 : z e.2 = true
          · by_cases hS : S e.1
            · right
              obtain ⟨p, hlp, hrp⟩ := hS
              have : S e.2 := ⟨p, hlp, Relation.ReflTransGen.tail hrp ⟨he, hz1, hz2⟩⟩
              simp [this]
            · left; simp [hS]
          · right; simp [hz2]
        · left; simp [hz1]
      · intro e he
        by_cases hz1 : z e.1 = true
        · by_cases hz2 : z e.2 = true
          · have hS : S (tip e (a ⟨e, he⟩)) :=
              ⟨⟨e, he⟩, ⟨hz1, hz2⟩, Relation.ReflTransGen.refl⟩
            cases hab' : a ⟨e, he⟩
            · left
              rw [hab'] at hS
              have hS' : S e.1 := by simpa [tip] using hS
              simp [hS']
            · right
              rw [hab'] at hS
              have hS' : S e.2 := by simpa [tip] using hS
              simp [hS']
          · right; simp [hz2]
        · left; simp [hz1]
      · intro f hf
        by_cases hz1 : z f.1 = true
        · by_cases hz2 : z f.2 = true
          · have hS : ¬ S (tip f (b ⟨f, hf⟩)) := by
              rintro ⟨e, hle, hre⟩
              exact hab e ⟨f, hf⟩ hle ⟨hz1, hz2⟩ hre
            cases hab' : b ⟨f, hf⟩
            · left
              rw [hab'] at hS
              have hS' : ¬ S f.1 := by simpa [tip] using hS
              simp [hS']
            · right
              rw [hab'] at hS
              have hS' : ¬ S f.2 := by simpa [tip] using hS
              simp [hS']
          · right; simp [hz2]
        · left; simp [hz1]
      · intro i
        by_cases hS : S i <;> cases hz : z i <;> simp [hS, hz]
  refine ⟨part1, ?_⟩
  obtain ⟨C, h1, h2, h3, h4, h5, h6⟩ := PEqualNP.Outside.L_lib_1192.circuit_main m P.card Q.card
    D.toList (fun i => (P.equivFin.symm i).val) (fun i => (Q.equivFin.symm i).val)
  refine ⟨C, h1, h2, h3, h4, ?_, ?_⟩
  · rw [Finset.length_toList] at h5
    exact h5
  · intro z
    exact (h6 z).trans (not_congr
      ((PEqualNP.Outside.L_lib_1192.bridge m D P Q z).trans (part1 z).symm))
