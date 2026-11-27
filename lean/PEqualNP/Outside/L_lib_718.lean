import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_718_aux

private abbrev RawT (n : ℕ) (w : Fin n → ℕ) := (i : Fin n) × Fin (w i)

private def parityFn {n : ℕ} {w : Fin n → ℕ} (y : RawT n w → Bool) (i : Fin n) : Bool :=
  decide (Odd ((Finset.univ : Finset (Fin (w i))).filter (fun j => y ⟨i, j⟩ = true)).card)

private def shapePred (N J : Finset (List Bool)) : Prop :=
  [] ∈ N ∧ J ⊆ N ∧
  (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
  ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N

private def traceFn {V : Type} (ask : List Bool → V) (p : List Bool) : List V :=
  List.ofFn (fun j : Fin p.length => ask (p.take j.val))

private def consistentPred {V : Type} (ask : List Bool → V) (p : List Bool) (x : V → Bool) : Prop :=
  ∀ j : Fin p.length, x (ask (p.take j.val)) = p.get j

private inductive DTree (α β : Type) : Type
  | leaf (val : β) : DTree α β
  | branch (q : α) (left right : DTree α β) : DTree α β

private def DTree.height {α β : Type} : DTree α β → ℕ
  | .leaf _ => 0
  | .branch _ l r => 1 + max l.height r.height

private def DTree.toNodes {α β : Type} : DTree α β → Finset (List Bool)
  | .leaf _ => {[]}
  | .branch _ l r =>
    insert [] (l.toNodes.image (List.cons false) ∪ r.toNodes.image (List.cons true))

private def DTree.toIntern {α β : Type} : DTree α β → Finset (List Bool)
  | .leaf _ => ∅
  | .branch _ l r =>
    insert [] (l.toIntern.image (List.cons false) ∪ r.toIntern.image (List.cons true))

private def DTree.toLeaves {α β : Type} : DTree α β → Finset (List Bool)
  | .leaf _ => {[]}
  | .branch _ l r =>
    l.toLeaves.image (List.cons false) ∪ r.toLeaves.image (List.cons true)

private def DTree.toQuery {α β : Type} (d : α) : DTree α β → List Bool → α
  | .leaf _, _ => d
  | .branch a _ _, [] => a
  | .branch _ l _, false :: p => l.toQuery d p
  | .branch _ _ r, true :: p => r.toQuery d p

private def DTree.toOut {α β : Type} (d : β) : DTree α β → List Bool → β
  | .leaf v, _ => v
  | .branch _ _ _, [] => d
  | .branch _ l _, false :: p => l.toOut d p
  | .branch _ _ r, true :: p => r.toOut d p

private theorem DTree.nil_mem_toNodes {α β : Type} (t : DTree α β) : [] ∈ t.toNodes := by
  cases t <;> simp [DTree.toNodes]

private theorem DTree.toIntern_subset_toNodes {α β : Type} (t : DTree α β) :
    t.toIntern ⊆ t.toNodes := by
  induction t with
  | leaf _ => simp [DTree.toIntern, DTree.toNodes]
  | branch _ l r ihl ihr =>
    intro p hp
    simp only [DTree.toIntern, DTree.toNodes, Finset.mem_insert, Finset.mem_union,
      Finset.mem_image] at hp ⊢
    rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨q, ihl hq, rfl⟩)
    · exact Or.inr (Or.inr ⟨q, ihr hq, rfl⟩)

private theorem DTree.toNodes_sdiff_toIntern {α β : Type} (t : DTree α β) :
    t.toNodes \ t.toIntern = t.toLeaves := by
  induction t with
  | leaf _ => simp [DTree.toNodes, DTree.toIntern, DTree.toLeaves]
  | branch _ l r ihl ihr =>
    ext p
    simp only [Finset.mem_sdiff, DTree.toNodes, DTree.toIntern, DTree.toLeaves,
      Finset.mem_insert, Finset.mem_union, Finset.mem_image]
    cases p with
    | nil => simp
    | cons b q =>
      cases b
      · simp only [reduceCtorEq, List.cons.injEq, true_and, false_and, false_or, exists_eq_right]
        have h := Finset.ext_iff.mp ihl q
        simpa [Finset.mem_sdiff] using h
      · simp only [reduceCtorEq, List.cons.injEq, true_and, false_and, false_or, exists_eq_right]
        have h := Finset.ext_iff.mp ihr q
        simpa [Finset.mem_sdiff] using h

private theorem DTree.toShape {α β : Type} (t : DTree α β) :
    shapePred t.toNodes t.toIntern := by
  refine ⟨t.nil_mem_toNodes, t.toIntern_subset_toNodes, ?_, ?_⟩
  · induction t with
    | leaf _ =>
      intro p b h
      simp [DTree.toNodes] at h
    | branch _ l r ihl ihr =>
      intro p b h
      cases p with
      | nil => simp [DTree.toIntern]
      | cons b0 q =>
        simp only [List.cons_append, DTree.toNodes, Finset.mem_insert, Finset.mem_union,
          Finset.mem_image, reduceCtorEq, false_or] at h
        simp only [DTree.toIntern, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
        cases b0
        · rcases h with ⟨q', hq', heq⟩ | ⟨q', _, heq⟩
          · injection heq with _ hqeq
            rw [hqeq] at hq'
            exact Or.inr (Or.inl ⟨q, ihl q b hq', rfl⟩)
          · exact Bool.noConfusion (List.cons.inj heq).1
        · rcases h with ⟨q', _, heq⟩ | ⟨q', hq', heq⟩
          · exact Bool.noConfusion (List.cons.inj heq).1
          · injection heq with _ hqeq
            rw [hqeq] at hq'
            exact Or.inr (Or.inr ⟨q, ihr q b hq', rfl⟩)
  · induction t with
    | leaf _ =>
      intro p hp
      simp [DTree.toIntern] at hp
    | branch _ l r ihl ihr =>
      intro p hp
      cases p with
      | nil =>
        simp only [List.nil_append, DTree.toNodes, Finset.mem_insert, Finset.mem_union,
          Finset.mem_image]
        exact ⟨Or.inr (Or.inl ⟨[], l.nil_mem_toNodes, rfl⟩),
          Or.inr (Or.inr ⟨[], r.nil_mem_toNodes, rfl⟩)⟩
      | cons b0 q =>
        simp only [DTree.toIntern, Finset.mem_insert, Finset.mem_union, Finset.mem_image,
          reduceCtorEq, false_or] at hp
        simp only [List.cons_append, DTree.toNodes, Finset.mem_insert, Finset.mem_union,
          Finset.mem_image]
        cases b0
        · rcases hp with ⟨q', hq', heq⟩ | ⟨q', _, heq⟩
          · injection heq with _ hqeq
            rw [hqeq] at hq'
            rcases ihl q hq' with ⟨hf, ht⟩
            exact ⟨Or.inr (Or.inl ⟨q ++ [false], hf, rfl⟩),
              Or.inr (Or.inl ⟨q ++ [true], ht, rfl⟩)⟩
          · exact Bool.noConfusion (List.cons.inj heq).1
        · rcases hp with ⟨q', _, heq⟩ | ⟨q', hq', heq⟩
          · exact Bool.noConfusion (List.cons.inj heq).1
          · injection heq with _ hqeq
            rw [hqeq] at hq'
            rcases ihr q hq' with ⟨hf, ht⟩
            exact ⟨Or.inr (Or.inr ⟨q ++ [false], hf, rfl⟩),
              Or.inr (Or.inr ⟨q ++ [true], ht, rfl⟩)⟩

private theorem traceFn_cons_branch {α β : Type} (d : α) (a : α) (l r : DTree α β)
    (b : Bool) (p : List Bool) :
    traceFn (DTree.toQuery d (DTree.branch a l r)) (b :: p) =
      a :: traceFn (DTree.toQuery d (if b = false then l else r)) p := by
  apply List.ext_getElem
  · simp [traceFn]
  · intro i hi1 hi2
    cases i with
    | zero => simp [traceFn, DTree.toQuery]
    | succ k => cases b <;> simp [traceFn, DTree.toQuery]

private theorem traceFn_append_one {V : Type} (ask : List Bool → V) (p : List Bool) (b : Bool) :
    traceFn ask (p ++ [b]) = traceFn ask p ++ [ask p] := by
  apply List.ext_getElem
  · simp [traceFn]
  · intro i hi1 hi2
    simp only [traceFn, List.getElem_ofFn, List.getElem_append, List.length_ofFn]
    by_cases hlt : i < p.length
    · simp only [hlt, ↓reduceDIte]
      congr 1
      rw [List.take_append_of_le_length (le_of_lt hlt)]
    · simp only [hlt, ↓reduceDIte]
      have hieq : i = p.length := by
        simp only [traceFn, List.length_ofFn, List.length_append, List.length_singleton] at hi1
        omega
      subst hieq
      simp only [Nat.sub_self, List.getElem_singleton]
      congr 1
      rw [List.take_append_of_le_length le_rfl, List.take_length]

private def outerPriceWeight {n m : ℕ} (w : Fin n → ℕ) (price : Fin m → ℕ) :
    DTree (Fin n) (Fin m) → ℕ
  | .leaf a => price a
  | .branch i l r => 2 ^ (w i - 1) * (outerPriceWeight w price l + outerPriceWeight w price r)

private def weightedHeight {n : ℕ} {β : Type} (w : Fin n → ℕ) : DTree (Fin n) β → ℕ
  | .leaf _ => 0
  | .branch i l r => w i + max (weightedHeight w l) (weightedHeight w r)

private theorem outerPriceWeight_eq_sum_toLeaves {n m : ℕ} (w : Fin n → ℕ) (hw : ∀ i, 0 < w i)
    (price : Fin m → ℕ) (dq : Fin n) (dout : Fin m) (t : DTree (Fin n) (Fin m)) :
    t.toLeaves.sum (fun p => price (t.toOut dout p) * 2 ^ (((traceFn (t.toQuery dq) p).map w).sum - p.length)) =
      outerPriceWeight w price t := by
  induction t with
  | leaf a =>
    simp [DTree.toLeaves, DTree.toOut, outerPriceWeight, traceFn]
  | branch a l r ihl ihr =>
    have hdisj : Disjoint (l.toLeaves.image (List.cons false)) (r.toLeaves.image (List.cons true)) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      rcases Finset.mem_image.mp hx1 with ⟨_, _, rfl⟩
      rcases Finset.mem_image.mp hx2 with ⟨_, _, heq⟩
      exact Bool.noConfusion (List.cons.inj heq).1
    have hle_sum : ∀ (q : List Bool → Fin n) (p : List Bool),
        p.length ≤ ((traceFn q p).map w).sum := by
      intro q p
      have hlen : p.length = ((traceFn q p).map w).length := by simp [traceFn]
      rw [hlen]
      have hge1 : ∀ x ∈ (traceFn q p).map w, 1 ≤ x := by
        intro x hx
        rcases List.mem_map.mp hx with ⟨i, _, rfl⟩
        exact hw i
      clear hlen
      generalize hL : (traceFn q p).map w = L at hge1 ⊢
      clear hL
      induction L with
      | nil => simp
      | cons hd tl ih =>
        have h1 : 1 ≤ hd := hge1 hd List.mem_cons_self
        have h2 : tl.length ≤ tl.sum := ih (fun x hx => hge1 x (List.mem_cons_of_mem hd hx))
        simp only [List.length_cons, List.sum_cons]
        omega
    simp only [DTree.toLeaves, outerPriceWeight]
    rw [Finset.sum_union hdisj,
      Finset.sum_image (fun _ _ _ _ h => (List.cons.inj h).2),
      Finset.sum_image (fun _ _ _ _ h => (List.cons.inj h).2)]
    have hl_eq :
        ∑ p ∈ l.toLeaves,
            price ((DTree.branch a l r).toOut dout (false :: p)) *
              2 ^ (((traceFn ((DTree.branch a l r).toQuery dq) (false :: p)).map w).sum -
                (false :: p).length) =
          2 ^ (w a - 1) * outerPriceWeight w price l := by
      rw [← ihl, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      rw [traceFn_cons_branch]
      simp only [DTree.toOut, ↓reduceIte, List.map_cons, List.sum_cons, List.length_cons]
      have hwa : 1 ≤ w a := hw a
      have hp : p.length ≤ ((traceFn (l.toQuery dq) p).map w).sum := hle_sum _ p
      have hexp : w a + ((traceFn (l.toQuery dq) p).map w).sum - (p.length + 1) =
          (w a - 1) + (((traceFn (l.toQuery dq) p).map w).sum - p.length) := by omega
      rw [hexp, Nat.pow_add]
      ring
    have hr_eq :
        ∑ p ∈ r.toLeaves,
            price ((DTree.branch a l r).toOut dout (true :: p)) *
              2 ^ (((traceFn ((DTree.branch a l r).toQuery dq) (true :: p)).map w).sum -
                (true :: p).length) =
          2 ^ (w a - 1) * outerPriceWeight w price r := by
      rw [← ihr, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      rw [traceFn_cons_branch]
      simp only [DTree.toOut, Bool.true_eq_false, ↓reduceIte, List.map_cons, List.sum_cons,
        List.length_cons]
      have hwa : 1 ≤ w a := hw a
      have hp : p.length ≤ ((traceFn (r.toQuery dq) p).map w).sum := hle_sum _ p
      have hexp : w a + ((traceFn (r.toQuery dq) p).map w).sum - (p.length + 1) =
          (w a - 1) + (((traceFn (r.toQuery dq) p).map w).sum - p.length) := by omega
      rw [hexp, Nat.pow_add]
      ring
    rw [hl_eq, hr_eq, Nat.mul_add]

private theorem weightedHeight_ge_path {n : ℕ} {β : Type} (w : Fin n → ℕ) (d : Fin n)
    (t : DTree (Fin n) β) :
    ∀ p ∈ t.toNodes, ((traceFn (t.toQuery d) p).map w).sum ≤ weightedHeight w t := by
  induction t with
  | leaf _ =>
    intro p hp
    have : p = [] := Finset.mem_singleton.mp hp
    subst this
    simp [traceFn, weightedHeight]
  | branch a l r ihl ihr =>
    intro p hp
    simp only [DTree.toNodes, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp
    rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · simp [traceFn]
    · rw [traceFn_cons_branch]
      simp only [↓reduceIte, List.map_cons, List.sum_cons, weightedHeight]
      have := ihl q hq
      omega
    · rw [traceFn_cons_branch]
      simp only [Bool.true_eq_false, ↓reduceIte, List.map_cons, List.sum_cons, weightedHeight]
      have := ihr q hq
      omega

private def DTree.NoRep {α β : Type} (avoid : α → Prop) : DTree α β → Prop
  | .leaf _ => True
  | .branch a l r => ¬ avoid a ∧ l.NoRep (fun x => avoid x ∨ x = a) ∧ r.NoRep (fun x => avoid x ∨ x = a)

private theorem DTree.NoRep.mono {α β : Type} {av1 av2 : α → Prop} {t : DTree α β}
    (h : t.NoRep av2) (himp : ∀ x, av1 x → av2 x) : t.NoRep av1 := by
  induction t generalizing av1 av2 with
  | leaf _ => trivial
  | branch a l r ihl ihr =>
    rcases h with ⟨hna, hl, hr⟩
    refine ⟨fun ha => hna (himp a ha), ?_, ?_⟩
    · exact ihl hl (fun x hx => hx.elim (fun h1 => Or.inl (himp x h1)) Or.inr)
    · exact ihr hr (fun x hx => hx.elim (fun h1 => Or.inl (himp x h1)) Or.inr)

private theorem DTree.not_mem_trace_of_noRep {α β : Type} (d : α) (t : DTree α β)
    (av : α → Prop) (h : t.NoRep av) :
    ∀ p ∈ t.toNodes, ∀ x ∈ traceFn (t.toQuery d) p, ¬ av x := by
  induction t generalizing av with
  | leaf _ =>
    intro p hp x hx
    have : p = [] := Finset.mem_singleton.mp hp
    subst this
    simp [traceFn] at hx
  | branch a l r ihl ihr =>
    rcases h with ⟨hna, hl, hr⟩
    intro p hp x hx
    simp only [DTree.toNodes, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp
    rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · simp [traceFn] at hx
    · rw [traceFn_cons_branch] at hx
      simp only [↓reduceIte, List.mem_cons] at hx
      rcases hx with rfl | hx'
      · exact hna
      · exact fun ha => ihl _ hl q hq x hx' (Or.inl ha)
    · rw [traceFn_cons_branch] at hx
      simp only [Bool.true_eq_false, ↓reduceIte, List.mem_cons] at hx
      rcases hx with rfl | hx'
      · exact hna
      · exact fun ha => ihr _ hr q hq x hx' (Or.inl ha)

private theorem DTree.trace_nodup_of_noRep {α β : Type} (d : α) (t : DTree α β)
    (av : α → Prop) (h : t.NoRep av) :
    ∀ p ∈ t.toNodes, (traceFn (t.toQuery d) p).Nodup := by
  induction t generalizing av with
  | leaf _ =>
    intro p hp
    have : p = [] := Finset.mem_singleton.mp hp
    subst this
    simp [traceFn]
  | branch a l r ihl ihr =>
    rcases h with ⟨hna, hl, hr⟩
    intro p hp
    simp only [DTree.toNodes, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp
    rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · simp [traceFn]
    · rw [traceFn_cons_branch]
      simp only [↓reduceIte, List.nodup_cons]
      refine ⟨?_, ihl _ hl q hq⟩
      intro hmem
      exact DTree.not_mem_trace_of_noRep d l _ hl q hq a hmem (Or.inr rfl)
    · rw [traceFn_cons_branch]
      simp only [Bool.true_eq_false, ↓reduceIte, List.nodup_cons]
      refine ⟨?_, ihr _ hr q hq⟩
      intro hmem
      exact DTree.not_mem_trace_of_noRep d r _ hr q hq a hmem (Or.inr rfl)

private def cntOf {n : ℕ} {w : Fin n → ℕ} (ρ : RawT n w → Option Bool) (i : Fin n) : ℕ :=
  ((Finset.univ : Finset (Fin (w i))).filter (fun j => (ρ ⟨i, j⟩).isSome)).card

private def accOf {n : ℕ} {w : Fin n → ℕ} (ρ : RawT n w → Option Bool) (i : Fin n) : Bool :=
  decide (Odd ((Finset.univ : Finset (Fin (w i))).filter (fun j => ρ ⟨i, j⟩ = some true)).card)

private theorem cntOf_le {n : ℕ} {w : Fin n → ℕ} (ρ : RawT n w → Option Bool) (i : Fin n) :
    cntOf ρ i ≤ w i := by
  unfold cntOf
  exact (Finset.card_filter_le _ _).trans (by simp)

private theorem cntOf_lt_of_none {n : ℕ} {w : Fin n → ℕ} (ρ : RawT n w → Option Bool)
    (b : RawT n w) (hb : ¬ (ρ b).isSome) : cntOf ρ b.1 < w b.1 := by
  unfold cntOf
  have hlt : (Finset.univ.filter (fun j : Fin (w b.1) => (ρ ⟨b.1, j⟩).isSome)) ⊂ Finset.univ := by
    rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
    refine ⟨b.2, Finset.mem_univ _, ?_⟩
    simpa using hb
  have hc := Finset.card_lt_card hlt
  simpa using hc

private theorem cntOf_update {n : ℕ} {w : Fin n → ℕ} (ρ : RawT n w → Option Bool)
    (b : RawT n w) (v : Bool) (hb : ¬ (ρ b).isSome) :
    cntOf (Function.update ρ b (some v)) = Function.update (cntOf ρ) b.1 (cntOf ρ b.1 + 1) := by
  funext i
  by_cases hi : i = b.1
  · subst hi
    simp only [Function.update_self, cntOf]
    have hset :
        Finset.univ.filter (fun j : Fin (w b.1) => (Function.update ρ b (some v) ⟨b.1, j⟩).isSome) =
        insert b.2 (Finset.univ.filter (fun j : Fin (w b.1) => (ρ ⟨b.1, j⟩).isSome)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      by_cases hj : j = b.2
      · subst hj
        have hbe : (⟨b.1, b.2⟩ : RawT n w) = b := rfl
        rw [hbe]; simp
      · have hne : (⟨b.1, j⟩ : RawT n w) ≠ b := fun h => hj (by cases b; cases h; rfl)
        simp [hne, hj]
    rw [hset, Finset.card_insert_of_notMem]
    simpa using hb
  · simp only [Function.update_of_ne hi, cntOf]
    congr 1
    ext j
    have hne : (⟨i, j⟩ : RawT n w) ≠ b := fun h => hi (congrArg Sigma.fst h)
    simp [hne]

private theorem accOf_update {n : ℕ} {w : Fin n → ℕ} (ρ : RawT n w → Option Bool)
    (b : RawT n w) (v : Bool) (hb : ¬ (ρ b).isSome) :
    accOf (Function.update ρ b (some v)) = Function.update (accOf ρ) b.1 (accOf ρ b.1 ^^ v) := by
  funext i
  by_cases hi : i = b.1
  · subst hi
    simp only [Function.update_self, accOf]
    cases v
    · have hset :
          Finset.univ.filter (fun j : Fin (w b.1) => Function.update ρ b (some false) ⟨b.1, j⟩ = some true) =
          Finset.univ.filter (fun j : Fin (w b.1) => ρ ⟨b.1, j⟩ = some true) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases hj : j = b.2
        · subst hj
          have hbe : (⟨b.1, b.2⟩ : RawT n w) = b := rfl
          rw [hbe, Function.update_self]
          have hnb : ρ b ≠ some true := fun h => by rw [h] at hb; simp at hb
          simp [hnb]
        · have hne : (⟨b.1, j⟩ : RawT n w) ≠ b := fun h => hj (by cases b; cases h; rfl)
          simp [hne]
      rw [hset, Bool.xor_false]
    · have hset :
          Finset.univ.filter (fun j : Fin (w b.1) => Function.update ρ b (some true) ⟨b.1, j⟩ = some true) =
          insert b.2 (Finset.univ.filter (fun j : Fin (w b.1) => ρ ⟨b.1, j⟩ = some true)) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        by_cases hj : j = b.2
        · subst hj
          have hbe : (⟨b.1, b.2⟩ : RawT n w) = b := rfl
          rw [hbe, Function.update_self]; simp
        · have hne : (⟨b.1, j⟩ : RawT n w) ≠ b := fun h => hj (by cases b; cases h; rfl)
          simp [hne, hj]
      have hnotmem : b.2 ∉ Finset.univ.filter (fun j : Fin (w b.1) => ρ ⟨b.1, j⟩ = some true) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro h; rw [h] at hb; simp at hb
      rw [hset, Finset.card_insert_of_notMem hnotmem, Bool.xor_true]
      by_cases ho : Odd (Finset.univ.filter (fun j : Fin (w b.1) => ρ ⟨b.1, j⟩ = some true)).card
      · have hno : ¬ Odd ((Finset.univ.filter (fun j : Fin (w b.1) => ρ ⟨b.1, j⟩ = some true)).card + 1) := by
          rw [Nat.odd_add_one]; exact not_not.mpr ho
        rw [decide_eq_true ho, decide_eq_false hno]; rfl
      · have hyo : Odd ((Finset.univ.filter (fun j : Fin (w b.1) => ρ ⟨b.1, j⟩ = some true)).card + 1) := by
          rw [Nat.odd_add_one]; exact ho
        rw [decide_eq_false ho, decide_eq_true hyo]; rfl
  · simp only [Function.update_of_ne hi, accOf]
    congr 1
    have hset :
        Finset.univ.filter (fun j : Fin (w i) => Function.update ρ b (some v) ⟨i, j⟩ = some true) =
        Finset.univ.filter (fun j : Fin (w i) => ρ ⟨i, j⟩ = some true) := by
      ext j
      have hne : (⟨i, j⟩ : RawT n w) ≠ b := fun h => hi (congrArg Sigma.fst h)
      simp [hne]
    rw [hset]

private def incSum {n : ℕ} (w : Fin n → ℕ) (cnt : Fin n → ℕ) : ℕ :=
  ∑ i : Fin n, if cnt i < w i then cnt i else 0

private theorem incSum_le_sum_w {n : ℕ} (w : Fin n → ℕ) (cnt : Fin n → ℕ) :
    incSum w cnt ≤ ∑ i : Fin n, w i := by
  unfold incSum
  apply Finset.sum_le_sum
  intro i _
  split_ifs with h
  · exact le_of_lt h
  · exact Nat.zero_le _

private theorem incSum_zero {n : ℕ} (w : Fin n → ℕ) (hw : ∀ i, 0 < w i) :
    incSum w (fun _ => 0) = 0 := by
  unfold incSum
  apply Finset.sum_eq_zero
  intro i _
  simp [hw i]

private theorem incSum_step_lt {n : ℕ} (w : Fin n → ℕ) (cnt : Fin n → ℕ) (i : Fin n)
    (h : cnt i + 1 < w i) :
    incSum w (Function.update cnt i (cnt i + 1)) = incSum w cnt + 1 := by
  unfold incSum
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
  have hrest :
      ∑ j ∈ Finset.univ.erase i,
          (if Function.update cnt i (cnt i + 1) j < w j then
            Function.update cnt i (cnt i + 1) j else 0) =
        ∑ j ∈ Finset.univ.erase i, (if cnt j < w j then cnt j else 0) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hne : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [hne]
  rw [hrest]
  have h1 : cnt i < w i := by omega
  simp only [Function.update_self, h, h1, ↓reduceIte]
  omega

private theorem incSum_step_eq {n : ℕ} (w : Fin n → ℕ) (cnt : Fin n → ℕ) (i : Fin n)
    (h : cnt i + 1 = w i) :
    incSum w cnt = (w i - 1) + incSum w (Function.update cnt i (w i)) := by
  unfold incSum
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
  have hrest :
      ∑ j ∈ Finset.univ.erase i,
          (if Function.update cnt i (w i) j < w j then
            Function.update cnt i (w i) j else 0) =
        ∑ j ∈ Finset.univ.erase i, (if cnt j < w j then cnt j else 0) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hne : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [hne]
  rw [hrest]
  have hlt : cnt i < w i := by omega
  simp only [Function.update_self, hlt, lt_irrefl, ↓reduceIte]
  omega

private def pot {n : ℕ} (w : Fin n → ℕ) (cnt : Fin n → ℕ) : ℕ :=
  ∏ i : Fin n, 2 ^ (if cnt i < w i then cnt i else 0)

private theorem pot_eq_two_pow_incSum {n : ℕ} (w : Fin n → ℕ) (cnt : Fin n → ℕ) :
    pot w cnt = 2 ^ incSum w cnt := by
  unfold pot incSum
  rw [Finset.prod_pow_eq_pow_sum]

private theorem pot_zero {n : ℕ} (w : Fin n → ℕ) (hw : ∀ i, 0 < w i) :
    pot w (fun _ => 0) = 1 := by
  rw [pot_eq_two_pow_incSum, incSum_zero w hw, Nat.pow_zero]

private theorem pot_step_lt {n : ℕ} (w : Fin n → ℕ) (cnt : Fin n → ℕ) (i : Fin n)
    (h : cnt i + 1 < w i) :
    pot w (Function.update cnt i (cnt i + 1)) = 2 * pot w cnt := by
  rw [pot_eq_two_pow_incSum, pot_eq_two_pow_incSum, incSum_step_lt w cnt i h, Nat.pow_succ]
  ring

private theorem pot_step_eq {n : ℕ} (w : Fin n → ℕ) (cnt : Fin n → ℕ) (i : Fin n)
    (h : cnt i + 1 = w i) :
    pot w cnt = 2 ^ (w i - 1) * pot w (Function.update cnt i (w i)) := by
  rw [pot_eq_two_pow_incSum, pot_eq_two_pow_incSum, incSum_step_eq w cnt i h, Nat.pow_add]

private def rawPriceWeight {n m : ℕ} (w : Fin n → ℕ) (price : Fin m → ℕ)
    (cnt : Fin n → ℕ) : DTree (RawT n w) (Fin m) → ℕ
  | .leaf a => price a * 2 ^ ((∑ i, w i) - incSum w cnt)
  | .branch b l r =>
    let cnt' := Function.update cnt b.1 (cnt b.1 + 1)
    rawPriceWeight w price cnt' l + rawPriceWeight w price cnt' r

private abbrev CoinTape (n : ℕ) (w : Fin n → ℕ) := (i : Fin n) → Fin (w i - 1) → Bool

private def projTree {n : ℕ} {w : Fin n → ℕ} {β : Type}
    (c : CoinTape n w) (cnt : Fin n → ℕ) (acc : Fin n → Bool) :
    DTree (RawT n w) β → DTree (Fin n) β
  | .leaf v => .leaf v
  | .branch b l r =>
    let i := b.1
    if h : cnt i + 1 < w i then
      let bit := c i ⟨cnt i, by omega⟩
      let cnt' := Function.update cnt i (cnt i + 1)
      let acc' := Function.update acc i (acc i ^^ bit)
      if bit = false then projTree c cnt' acc' l else projTree c cnt' acc' r
    else
      let cnt' := Function.update cnt i (w i)
      let leftChild :=
        if acc i = false then projTree c cnt' (Function.update acc i false) l
        else projTree c cnt' (Function.update acc i false) r
      let rightChild :=
        if acc i = false then projTree c cnt' (Function.update acc i true) r
        else projTree c cnt' (Function.update acc i true) l
      DTree.branch i leftChild rightChild

private theorem projTree_congr_unused {n : ℕ} {w : Fin n → ℕ} {β : Type}
    (c1 c2 : CoinTape n w) (cnt : Fin n → ℕ) (acc : Fin n → Bool)
    (t : DTree (RawT n w) β)
    (hagree : ∀ (i : Fin n) (s : Fin (w i - 1)), cnt i ≤ s.val → c1 i s = c2 i s) :
    projTree c1 cnt acc t = projTree c2 cnt acc t := by
  induction t generalizing cnt acc with
  | leaf _ => rfl
  | branch b l r ihl ihr =>
    simp only [projTree]
    by_cases h1 : cnt b.1 + 1 < w b.1
    · simp only [h1, ↓reduceDIte]
      have hbit : c1 b.1 ⟨cnt b.1, by omega⟩ = c2 b.1 ⟨cnt b.1, by omega⟩ :=
        hagree b.1 ⟨cnt b.1, by omega⟩ le_rfl
      rw [hbit]
      have hnext : ∀ (i : Fin n) (s : Fin (w i - 1)),
          Function.update cnt b.1 (cnt b.1 + 1) i ≤ s.val → c1 i s = c2 i s := by
        intro i s hs
        by_cases hi : i = b.1
        · subst hi
          simp only [Function.update_self] at hs
          exact hagree b.1 s (by omega)
        · simp only [Function.update_of_ne hi] at hs
          exact hagree i s hs
      split_ifs
      · exact ihl _ _ hnext
      · exact ihr _ _ hnext
    · simp only [h1, ↓reduceDIte]
      have hnext : ∀ (i : Fin n) (s : Fin (w i - 1)),
          Function.update cnt b.1 (w b.1) i ≤ s.val → c1 i s = c2 i s := by
        intro i s hs
        by_cases hi : i = b.1
        · subst hi
          simp only [Function.update_self] at hs
          omega
        · simp only [Function.update_of_ne hi] at hs
          exact hagree i s hs
      congr 1
      · split_ifs
        · exact ihl _ _ hnext
        · exact ihr _ _ hnext
      · split_ifs
        · exact ihr _ _ hnext
        · exact ihl _ _ hnext

private theorem sum_outerPriceWeight_projTree_eq {n m : ℕ} {w : Fin n → ℕ}
    (price : Fin m → ℕ) (t : DTree (RawT n w) (Fin m)) :
    ∀ (ρ : RawT n w → Option Bool),
      t.NoRep (fun b => (ρ b).isSome) →
      2 ^ (∑ i, w i) *
        (∑ c : CoinTape n w, outerPriceWeight w price (projTree c (cntOf ρ) (accOf ρ) t)) =
      Fintype.card (CoinTape n w) * pot w (cntOf ρ) * rawPriceWeight w price (cntOf ρ) t := by
  classical
  induction t with
  | leaf a =>
    intro ρ _
    simp only [projTree, outerPriceWeight, rawPriceWeight, Finset.sum_const, Finset.card_univ,
      smul_eq_mul]
    rw [pot_eq_two_pow_incSum]
    have hle : incSum w (cntOf ρ) ≤ ∑ i, w i := incSum_le_sum_w w (cntOf ρ)
    have hpow : 2 ^ incSum w (cntOf ρ) * 2 ^ ((∑ i, w i) - incSum w (cntOf ρ)) = 2 ^ (∑ i, w i) := by
      rw [← Nat.pow_add, Nat.add_sub_of_le hle]
    calc 2 ^ (∑ i, w i) * (Fintype.card (CoinTape n w) * price a)
        = Fintype.card (CoinTape n w) * price a * 2 ^ (∑ i, w i) := by ring
      _ = Fintype.card (CoinTape n w) * price a *
            (2 ^ incSum w (cntOf ρ) * 2 ^ ((∑ i, w i) - incSum w (cntOf ρ))) := by rw [hpow]
      _ = Fintype.card (CoinTape n w) * 2 ^ incSum w (cntOf ρ) *
            (price a * 2 ^ ((∑ i, w i) - incSum w (cntOf ρ))) := by ring
  | branch b l r ihl ihr =>
    intro ρ hnr
    rcases hnr with ⟨hb_not, hl_nr, hr_nr⟩
    have hlt : cntOf ρ b.1 < w b.1 := cntOf_lt_of_none ρ b hb_not
    let ρF := Function.update ρ b (some false)
    let ρT := Function.update ρ b (some true)
    have hnrF : l.NoRep (fun x => (ρF x).isSome) := hl_nr.mono (fun x hx => by
      by_cases hxb : x = b
      · exact Or.inr hxb
      · simp [ρF, hxb] at hx; exact Or.inl hx)
    have hnrT : r.NoRep (fun x => (ρT x).isSome) := hr_nr.mono (fun x hx => by
      by_cases hxb : x = b
      · exact Or.inr hxb
      · simp [ρT, hxb] at hx; exact Or.inl hx)
    have hcntF : cntOf ρF = Function.update (cntOf ρ) b.1 (cntOf ρ b.1 + 1) :=
      cntOf_update ρ b false hb_not
    have hcntT : cntOf ρT = Function.update (cntOf ρ) b.1 (cntOf ρ b.1 + 1) :=
      cntOf_update ρ b true hb_not
    have haccF : accOf ρF = Function.update (accOf ρ) b.1 (accOf ρ b.1 ^^ false) :=
      accOf_update ρ b false hb_not
    have haccT : accOf ρT = Function.update (accOf ρ) b.1 (accOf ρ b.1 ^^ true) :=
      accOf_update ρ b true hb_not
    by_cases h1 : cntOf ρ b.1 + 1 < w b.1
    · let slot : Fin (w b.1 - 1) := ⟨cntOf ρ b.1, by omega⟩
      let flip : CoinTape n w → CoinTape n w := fun c =>
        Function.update c b.1 (Function.update (c b.1) slot (!(c b.1 slot)))
      have hflip_inv : Function.Involutive flip := by
        intro c
        funext i s
        by_cases hi : i = b.1
        · subst hi
          by_cases hs : s = slot
          · subst hs; simp [flip]
          · simp [flip, hs]
        · simp [flip, hi]
      have hflip_agree : ∀ (c : CoinTape n w) (i : Fin n) (s : Fin (w i - 1)),
          Function.update (cntOf ρ) b.1 (cntOf ρ b.1 + 1) i ≤ s.val →
          flip c i s = c i s := by
        intro c i s hs
        by_cases hi : i = b.1
        · subst hi
          simp only [Function.update_self] at hs
          have hne : s ≠ slot := fun h => by rw [h] at hs; dsimp only [slot] at hs; omega
          simp [flip, hne]
        · simp [flip, hi]
      have h2sum :
          2 * ∑ c : CoinTape n w, outerPriceWeight w price (projTree c (cntOf ρ) (accOf ρ) (DTree.branch b l r)) =
            ∑ c : CoinTape n w, outerPriceWeight w price (projTree c (cntOf ρF) (accOf ρF) l) +
            ∑ c : CoinTape n w, outerPriceWeight w price (projTree c (cntOf ρT) (accOf ρT) r) := by
        have hswap :
            ∑ c : CoinTape n w, outerPriceWeight w price (projTree (flip c) (cntOf ρ) (accOf ρ) (DTree.branch b l r)) =
            ∑ c : CoinTape n w, outerPriceWeight w price (projTree c (cntOf ρ) (accOf ρ) (DTree.branch b l r)) :=
          Fintype.sum_equiv (Equiv.ofBijective flip hflip_inv.bijective) _ _ (fun _ => rfl)
        conv_lhs => rw [two_mul]; arg 2; rw [← hswap]
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro c _
        have hfc : flip c b.1 ⟨cntOf ρ b.1, by omega⟩ = !(c b.1 ⟨cntOf ρ b.1, by omega⟩) := by
          simp [flip, slot]
        have heql : projTree (flip c) (cntOf ρF) (accOf ρF) l = projTree c (cntOf ρF) (accOf ρF) l :=
          projTree_congr_unused (flip c) c _ _ l (fun i s hs => hflip_agree c i s (by rwa [← hcntF]))
        have heqr : projTree (flip c) (cntOf ρT) (accOf ρT) r = projTree c (cntOf ρT) (accOf ρT) r :=
          projTree_congr_unused (flip c) c _ _ r (fun i s hs => hflip_agree c i s (by rwa [← hcntT]))
        simp only [projTree, h1, ↓reduceDIte]
        rw [hfc]
        have hcnt_eq : cntOf ρF = cntOf ρT := hcntF.trans hcntT.symm
        cases hbval : c b.1 ⟨cntOf ρ b.1, by omega⟩
        · simp only [↓reduceIte, Bool.not_false, Bool.true_eq_false]
          rw [← hcntF, ← haccF, ← haccT, hcnt_eq, heqr]
        · simp only [Bool.true_eq_false, ↓reduceIte, Bool.not_true]
          rw [← hcntF, ← haccF, ← haccT, heql, hcnt_eq, add_comm]
      have hihF := ihl ρF hnrF
      have hihT := ihr ρT hnrT
      have hpot := pot_step_lt w (cntOf ρ) b.1 h1
      rw [hcntF, hpot] at hihF
      rw [hcntT, hpot] at hihT
      simp only [rawPriceWeight]
      have h2eq :
          2 * ((2 ^ ∑ i, w i) * ∑ c : CoinTape n w,
            outerPriceWeight w price (projTree c (cntOf ρ) (accOf ρ) (DTree.branch b l r))) =
          2 * (Fintype.card (CoinTape n w) * pot w (cntOf ρ) *
            (rawPriceWeight w price (Function.update (cntOf ρ) b.1 (cntOf ρ b.1 + 1)) l +
             rawPriceWeight w price (Function.update (cntOf ρ) b.1 (cntOf ρ b.1 + 1)) r)) := by
        calc 2 * ((2 ^ ∑ i, w i) * ∑ c : CoinTape n w,
              outerPriceWeight w price (projTree c (cntOf ρ) (accOf ρ) (DTree.branch b l r)))
            = (2 ^ ∑ i, w i) * (2 * ∑ c : CoinTape n w,
                outerPriceWeight w price (projTree c (cntOf ρ) (accOf ρ) (DTree.branch b l r))) := by ring
          _ = (2 ^ ∑ i, w i) * ∑ c : CoinTape n w, outerPriceWeight w price (projTree c (cntOf ρF) (accOf ρF) l) +
              (2 ^ ∑ i, w i) * ∑ c : CoinTape n w, outerPriceWeight w price (projTree c (cntOf ρT) (accOf ρT) r) := by
              rw [h2sum, Nat.mul_add]
          _ = Fintype.card (CoinTape n w) * (2 * pot w (cntOf ρ)) *
                rawPriceWeight w price (Function.update (cntOf ρ) b.1 (cntOf ρ b.1 + 1)) l +
              Fintype.card (CoinTape n w) * (2 * pot w (cntOf ρ)) *
                rawPriceWeight w price (Function.update (cntOf ρ) b.1 (cntOf ρ b.1 + 1)) r := by
              rw [hcntF, hcntT, hihF, hihT]
          _ = 2 * (Fintype.card (CoinTape n w) * pot w (cntOf ρ) *
                (rawPriceWeight w price (Function.update (cntOf ρ) b.1 (cntOf ρ b.1 + 1)) l +
                 rawPriceWeight w price (Function.update (cntOf ρ) b.1 (cntOf ρ b.1 + 1)) r)) := by ring
      exact Nat.eq_of_mul_eq_mul_left (by omega) h2eq
    · have heq : cntOf ρ b.1 + 1 = w b.1 := by omega
      have hcntF' : cntOf ρF = Function.update (cntOf ρ) b.1 (w b.1) := by rw [hcntF, heq]
      have hcntT' : cntOf ρT = Function.update (cntOf ρ) b.1 (w b.1) := by rw [hcntT, heq]
      have hcnt_eq : cntOf ρF = cntOf ρT := hcntF'.trans hcntT'.symm
      have hsum_eq :
          ∑ c : CoinTape n w, outerPriceWeight w price (projTree c (cntOf ρ) (accOf ρ) (DTree.branch b l r)) =
            2 ^ (w b.1 - 1) *
              (∑ c : CoinTape n w, outerPriceWeight w price (projTree c (cntOf ρF) (accOf ρF) l) +
               ∑ c : CoinTape n w, outerPriceWeight w price (projTree c (cntOf ρT) (accOf ρT) r)) := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro c _
        simp only [projTree, h1, ↓reduceDIte, outerPriceWeight]
        congr 1
        cases ha : accOf ρ b.1
        · simp only [↓reduceIte]
          have h1f : Function.update (accOf ρ) b.1 false = accOf ρF := by rw [haccF, ha]; rfl
          have h1t : Function.update (accOf ρ) b.1 true = accOf ρT := by rw [haccT, ha]; rfl
          rw [← hcntF', h1f, h1t, hcnt_eq]
        · simp only [Bool.true_eq_false, ↓reduceIte]
          have h1f : Function.update (accOf ρ) b.1 false = accOf ρT := by rw [haccT, ha]; rfl
          have h1t : Function.update (accOf ρ) b.1 true = accOf ρF := by rw [haccF, ha]; rfl
          rw [← hcntF', h1f, h1t, hcnt_eq, add_comm]
      have hihF := ihl ρF hnrF
      have hihT := ihr ρT hnrT
      have hpot := pot_step_eq w (cntOf ρ) b.1 heq
      rw [hcntF'] at hihF
      rw [hcntT'] at hihT
      simp only [rawPriceWeight, heq]
      calc 2 ^ (∑ i, w i) *
            ∑ c : CoinTape n w, outerPriceWeight w price (projTree c (cntOf ρ) (accOf ρ) (DTree.branch b l r))
          = 2 ^ (w b.1 - 1) *
              (2 ^ (∑ i, w i) * ∑ c : CoinTape n w, outerPriceWeight w price (projTree c (cntOf ρF) (accOf ρF) l) +
               2 ^ (∑ i, w i) * ∑ c : CoinTape n w, outerPriceWeight w price (projTree c (cntOf ρT) (accOf ρT) r)) := by
            rw [hsum_eq]; ring
        _ = 2 ^ (w b.1 - 1) *
              (Fintype.card (CoinTape n w) * pot w (Function.update (cntOf ρ) b.1 (w b.1)) *
                rawPriceWeight w price (Function.update (cntOf ρ) b.1 (w b.1)) l +
               Fintype.card (CoinTape n w) * pot w (Function.update (cntOf ρ) b.1 (w b.1)) *
                rawPriceWeight w price (Function.update (cntOf ρ) b.1 (w b.1)) r) := by
            rw [hcntF', hcntT', hihF, hihT]
        _ = Fintype.card (CoinTape n w) * pot w (cntOf ρ) *
              (rawPriceWeight w price (Function.update (cntOf ρ) b.1 (w b.1)) l +
               rawPriceWeight w price (Function.update (cntOf ρ) b.1 (w b.1)) r) := by
            rw [hpot]; ring

private def DTree.LeafValid {n m : ℕ} {w : Fin n → ℕ}
    (R : (Fin n → Bool) → Fin m → Prop) (ρ : RawT n w → Option Bool) :
    DTree (RawT n w) (Fin m) → Prop
  | .leaf a => ∀ y : RawT n w → Bool, (∀ b v, ρ b = some v → y b = v) → R (parityFn y) a
  | .branch b l r =>
    l.LeafValid R (Function.update ρ b (some false)) ∧
    r.LeafValid R (Function.update ρ b (some true))

private theorem extend_partial_with_parity {n : ℕ} {w : Fin n → ℕ}
    (ρ : RawT n w → Option Bool) (x : Fin n → Bool)
    (hcomp : ∀ i : Fin n, cntOf ρ i = w i → x i = accOf ρ i) :
    ∃ y : RawT n w → Bool, (∀ b v, ρ b = some v → y b = v) ∧ parityFn y = x := by
  classical
  have hex_block : ∀ i : Fin n,
      ∃ f : Fin (w i) → Bool,
        (∀ j v, ρ ⟨i, j⟩ = some v → f j = v) ∧
        decide (Odd (Finset.univ.filter (fun j : Fin (w i) => f j = true)).card) = x i := by
    intro i
    by_cases hfull : cntOf ρ i = w i
    · refine ⟨fun j => (ρ ⟨i, j⟩).getD false, ?_, ?_⟩
      · intro j v hv; simp [hv]
      · rw [hcomp i hfull]
        unfold accOf
        congr 3
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        cases h : ρ ⟨i, j⟩ with
        | none => simp
        | some b => cases b <;> simp
    · have hlt : cntOf ρ i < w i := lt_of_le_of_ne (cntOf_le ρ i) hfull
      have hex_none : ∃ j0 : Fin (w i), ρ ⟨i, j0⟩ = none := by
        by_contra hall
        push Not at hall
        have hfull' : Finset.univ.filter (fun j : Fin (w i) => (ρ ⟨i, j⟩).isSome) = Finset.univ := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
          cases h : ρ ⟨i, j⟩ with
          | none => exact absurd h (hall j)
          | some _ => rfl
        have : cntOf ρ i = w i := by unfold cntOf; rw [hfull', Finset.card_univ, Fintype.card_fin]
        exact hfull this
      rcases hex_none with ⟨j0, hj0⟩
      let f : Fin (w i) → Bool := fun j =>
        if j = j0 then (accOf ρ i ^^ x i) else (ρ ⟨i, j⟩).getD false
      refine ⟨f, ?_, ?_⟩
      · intro j v hv
        have hne : j ≠ j0 := fun heq => by rw [heq, hj0] at hv; simp at hv
        simp [f, hne, hv]
      · cases hflip : (accOf ρ i ^^ x i)
        · have hset : Finset.univ.filter (fun j : Fin (w i) => f j = true) =
              Finset.univ.filter (fun j : Fin (w i) => ρ ⟨i, j⟩ = some true) := by
            ext j
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            by_cases hj : j = j0
            · subst hj; simp [f, hflip, hj0]
            · simp only [f, hj, ↓reduceIte]
              cases h : ρ ⟨i, j⟩ with
              | none => simp
              | some b => cases b <;> simp
          rw [hset]
          change accOf ρ i = x i
          cases ha : accOf ρ i <;> cases hx : x i <;> simp [ha, hx] at hflip ⊢
        · have hset : Finset.univ.filter (fun j : Fin (w i) => f j = true) =
              insert j0 (Finset.univ.filter (fun j : Fin (w i) => ρ ⟨i, j⟩ = some true)) := by
            ext j
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
            by_cases hj : j = j0
            · subst hj; simp [f, hflip]
            · simp only [f, hj, ↓reduceIte, false_or]
              cases h : ρ ⟨i, j⟩ with
              | none => simp
              | some b => cases b <;> simp
          have hnm : j0 ∉ Finset.univ.filter (fun j : Fin (w i) => ρ ⟨i, j⟩ = some true) := by
            simp [hj0]
          rw [hset, Finset.card_insert_of_notMem hnm]
          have hpar_neg :
              decide (Odd ((Finset.univ.filter (fun j : Fin (w i) => ρ ⟨i, j⟩ = some true)).card + 1)) =
              !(accOf ρ i) := by
            unfold accOf
            by_cases ho : Odd (Finset.univ.filter (fun j : Fin (w i) => ρ ⟨i, j⟩ = some true)).card
            · have hno : ¬ Odd ((Finset.univ.filter (fun j : Fin (w i) => ρ ⟨i, j⟩ = some true)).card + 1) := by
                rw [Nat.odd_add_one]; exact not_not.mpr ho
              rw [decide_eq_true ho, decide_eq_false hno]; rfl
            · have hyo : Odd ((Finset.univ.filter (fun j : Fin (w i) => ρ ⟨i, j⟩ = some true)).card + 1) := by
                rw [Nat.odd_add_one]; exact ho
              rw [decide_eq_false ho, decide_eq_true hyo]; rfl
          rw [hpar_neg]
          cases ha : accOf ρ i <;> cases hx : x i <;> simp [ha, hx] at hflip ⊢
  refine ⟨fun b => Classical.choose (hex_block b.1) b.2, ?_, ?_⟩
  · intro ⟨i, j⟩ v hv
    exact (Classical.choose_spec (hex_block i)).1 j v hv
  · funext i
    exact (Classical.choose_spec (hex_block i)).2

private theorem projTree_props {n m : ℕ} {w : Fin n → ℕ} (hw : ∀ i, 0 < w i)
    (R : (Fin n → Bool) → Fin m → Prop) (c : CoinTape n w) (dq : Fin n) (dout : Fin m)
    (t : DTree (RawT n w) (Fin m)) :
    ∀ (ρ : RawT n w → Option Bool),
      t.NoRep (fun b => (ρ b).isSome) →
      t.LeafValid R ρ →
      (projTree c (cntOf ρ) (accOf ρ) t).NoRep (fun i => cntOf ρ i = w i) ∧
      weightedHeight w (projTree c (cntOf ρ) (accOf ρ) t) ≤ t.height + incSum w (cntOf ρ) ∧
      ∀ p ∈ (projTree c (cntOf ρ) (accOf ρ) t).toLeaves,
        ∀ x : Fin n → Bool,
          (∀ i : Fin n, cntOf ρ i = w i → x i = accOf ρ i) →
          consistentPred ((projTree c (cntOf ρ) (accOf ρ) t).toQuery dq) p x →
          R x ((projTree c (cntOf ρ) (accOf ρ) t).toOut dout p) := by
  classical
  induction t with
  | leaf a =>
    intro ρ _ hval
    refine ⟨trivial, Nat.zero_le _, ?_⟩
    intro p hp x hcomp _
    have hp0 : p = [] := Finset.mem_singleton.mp hp
    subst hp0
    rcases extend_partial_with_parity ρ x hcomp with ⟨y, hy_ext, hy_par⟩
    rw [← hy_par]
    exact hval y hy_ext
  | branch b l r ihl ihr =>
    intro ρ hnr ⟨hvalL, hvalR⟩
    rcases hnr with ⟨hb_not, hl_nr, hr_nr⟩
    have hlt : cntOf ρ b.1 < w b.1 := cntOf_lt_of_none ρ b hb_not
    let ρF := Function.update ρ b (some false)
    let ρT := Function.update ρ b (some true)
    have hnrF : l.NoRep (fun x => (ρF x).isSome) := hl_nr.mono (fun x hx => by
      by_cases hxb : x = b
      · exact Or.inr hxb
      · simp [ρF, hxb] at hx; exact Or.inl hx)
    have hnrT : r.NoRep (fun x => (ρT x).isSome) := hr_nr.mono (fun x hx => by
      by_cases hxb : x = b
      · exact Or.inr hxb
      · simp [ρT, hxb] at hx; exact Or.inl hx)
    have hcntF : cntOf ρF = Function.update (cntOf ρ) b.1 (cntOf ρ b.1 + 1) :=
      cntOf_update ρ b false hb_not
    have hcntT : cntOf ρT = Function.update (cntOf ρ) b.1 (cntOf ρ b.1 + 1) :=
      cntOf_update ρ b true hb_not
    have haccF : accOf ρF = Function.update (accOf ρ) b.1 (accOf ρ b.1 ^^ false) :=
      accOf_update ρ b false hb_not
    have haccT : accOf ρT = Function.update (accOf ρ) b.1 (accOf ρ b.1 ^^ true) :=
      accOf_update ρ b true hb_not
    rcases ihl ρF hnrF hvalL with ⟨hL_nr, hL_ht, hL_ok⟩
    rcases ihr ρT hnrT hvalR with ⟨hR_nr, hR_ht, hR_ok⟩
    by_cases h1 : cntOf ρ b.1 + 1 < w b.1
    · have hinc := incSum_step_lt w (cntOf ρ) b.1 h1
      have hincF : incSum w (cntOf ρF) = incSum w (cntOf ρ) + 1 := by rw [hcntF, hinc]
      have hincT : incSum w (cntOf ρT) = incSum w (cntOf ρ) + 1 := by rw [hcntT, hinc]
      simp only [projTree, h1, ↓reduceDIte]
      cases hbit : c b.1 ⟨cntOf ρ b.1, by omega⟩
      · simp only [↓reduceIte]
        rw [← hcntF, ← haccF]
        refine ⟨hL_nr.mono (fun i hi => by
            by_cases hib : i = b.1
            · subst hib; omega
            · rw [hcntF, Function.update_of_ne hib]; exact hi), ?_, ?_⟩
        · simp only [DTree.height]; omega
        · intro p hp x hcomp hcons
          refine hL_ok p hp x (fun i hi => ?_) hcons
          have hne : i ≠ b.1 := fun heq => by rw [heq, hcntF, Function.update_self] at hi; omega
          rw [hcntF, Function.update_of_ne hne] at hi
          rw [haccF, Function.update_of_ne hne]
          exact hcomp i hi
      · simp only [Bool.true_eq_false, ↓reduceIte]
        rw [← hcntT, ← haccT]
        refine ⟨hR_nr.mono (fun i hi => by
            by_cases hib : i = b.1
            · subst hib; omega
            · rw [hcntT, Function.update_of_ne hib]; exact hi), ?_, ?_⟩
        · simp only [DTree.height]; omega
        · intro p hp x hcomp hcons
          refine hR_ok p hp x (fun i hi => ?_) hcons
          have hne : i ≠ b.1 := fun heq => by rw [heq, hcntT, Function.update_self] at hi; omega
          rw [hcntT, Function.update_of_ne hne] at hi
          rw [haccT, Function.update_of_ne hne]
          exact hcomp i hi
    · have heq : cntOf ρ b.1 + 1 = w b.1 := by omega
      have hcntF' : cntOf ρF = Function.update (cntOf ρ) b.1 (w b.1) := by rw [hcntF, heq]
      have hcntT' : cntOf ρT = Function.update (cntOf ρ) b.1 (w b.1) := by rw [hcntT, heq]
      have hcnt_eq : cntOf ρF = cntOf ρT := hcntF'.trans hcntT'.symm
      have hinc := incSum_step_eq w (cntOf ρ) b.1 heq
      have hincF : incSum w (cntOf ρ) = w b.1 - 1 + incSum w (cntOf ρF) := by rw [hcntF', hinc]
      have hincT : incSum w (cntOf ρ) = w b.1 - 1 + incSum w (cntOf ρT) := by rw [hcntT', hinc]
      have hwa : 1 ≤ w b.1 := hw b.1
      simp only [projTree, h1, ↓reduceDIte]
      have hL_nr' : (projTree c (cntOf ρF) (accOf ρF) l).NoRep (fun i => cntOf ρ i = w i ∨ i = b.1) :=
        hL_nr.mono (fun i hi => by
          rcases hi with hi1 | rfl
          · by_cases hib : i = b.1
            · subst hib; rw [hcntF', Function.update_self]
            · rw [hcntF', Function.update_of_ne hib]; exact hi1
          · rw [hcntF', Function.update_self])
      have hR_nr' : (projTree c (cntOf ρT) (accOf ρT) r).NoRep (fun i => cntOf ρ i = w i ∨ i = b.1) :=
        hR_nr.mono (fun i hi => by
          rcases hi with hi1 | rfl
          · by_cases hib : i = b.1
            · subst hib; rw [hcntT', Function.update_self]
            · rw [hcntT', Function.update_of_ne hib]; exact hi1
          · rw [hcntT', Function.update_self])
      cases ha : accOf ρ b.1
      · simp only [↓reduceIte]
        have h1f : Function.update (accOf ρ) b.1 false = accOf ρF := by rw [haccF, ha]; rfl
        have h1t : Function.update (accOf ρ) b.1 true = accOf ρT := by rw [haccT, ha]; rfl
        rw [← hcntF', h1f, h1t]
        refine ⟨⟨by omega, hL_nr', by rw [hcnt_eq]; exact hR_nr'⟩, ?_, ?_⟩
        · simp only [weightedHeight, DTree.height]
          rw [← hcnt_eq] at hR_ht
          omega
        · intro p hp x hcomp hcons
          simp only [DTree.toLeaves, Finset.mem_union, Finset.mem_image] at hp
          rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
          · have hx0 : x b.1 = false := by
              have h0 := hcons ⟨0, by simp⟩
              simpa [DTree.toQuery] using h0
            have hcons_q : consistentPred ((projTree c (cntOf ρF) (accOf ρF) l).toQuery dq) q x := by
              intro j
              have hj := hcons ⟨j.val + 1, by simp [j.isLt]⟩
              simpa [DTree.toQuery] using hj
            have hcomp_F : ∀ i : Fin n, cntOf ρF i = w i → x i = accOf ρF i := by
              intro i hi
              by_cases hib : i = b.1
              · subst hib; rw [haccF, Function.update_self, ha]; exact hx0
              · rw [hcntF', Function.update_of_ne hib] at hi
                rw [haccF, Function.update_of_ne hib]
                exact hcomp i hi
            simpa [DTree.toOut] using hL_ok q hq x hcomp_F hcons_q
          · rw [hcnt_eq] at hq
            have hx0 : x b.1 = true := by
              have h0 := hcons ⟨0, by simp⟩
              simpa [DTree.toQuery] using h0
            have hcons_q : consistentPred ((projTree c (cntOf ρT) (accOf ρT) r).toQuery dq) q x := by
              intro j
              have hj := hcons ⟨j.val + 1, by simp [j.isLt]⟩
              rw [hcnt_eq] at hj
              simpa [DTree.toQuery] using hj
            have hcomp_T : ∀ i : Fin n, cntOf ρT i = w i → x i = accOf ρT i := by
              intro i hi
              by_cases hib : i = b.1
              · subst hib; rw [haccT, Function.update_self, ha]; exact hx0
              · rw [hcntT', Function.update_of_ne hib] at hi
                rw [haccT, Function.update_of_ne hib]
                exact hcomp i hi
            simpa [DTree.toOut, hcnt_eq] using hR_ok q hq x hcomp_T hcons_q
      · simp only [Bool.true_eq_false, ↓reduceIte]
        have h1f : Function.update (accOf ρ) b.1 false = accOf ρT := by rw [haccT, ha]; rfl
        have h1t : Function.update (accOf ρ) b.1 true = accOf ρF := by rw [haccF, ha]; rfl
        rw [← hcntF', h1f, h1t]
        refine ⟨⟨by omega, by rw [hcnt_eq]; exact hR_nr', hL_nr'⟩, ?_, ?_⟩
        · simp only [weightedHeight, DTree.height]
          rw [← hcnt_eq] at hR_ht
          omega
        · intro p hp x hcomp hcons
          simp only [DTree.toLeaves, Finset.mem_union, Finset.mem_image] at hp
          rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
          · rw [hcnt_eq] at hq
            have hx0 : x b.1 = false := by
              have h0 := hcons ⟨0, by simp⟩
              simpa [DTree.toQuery] using h0
            have hcons_q : consistentPred ((projTree c (cntOf ρT) (accOf ρT) r).toQuery dq) q x := by
              intro j
              have hj := hcons ⟨j.val + 1, by simp [j.isLt]⟩
              rw [hcnt_eq] at hj
              simpa [DTree.toQuery] using hj
            have hcomp_T : ∀ i : Fin n, cntOf ρT i = w i → x i = accOf ρT i := by
              intro i hi
              by_cases hib : i = b.1
              · subst hib; rw [haccT, Function.update_self, ha]; exact hx0
              · rw [hcntT', Function.update_of_ne hib] at hi
                rw [haccT, Function.update_of_ne hib]
                exact hcomp i hi
            simpa [DTree.toOut, hcnt_eq] using hR_ok q hq x hcomp_T hcons_q
          · have hx0 : x b.1 = true := by
              have h0 := hcons ⟨0, by simp⟩
              simpa [DTree.toQuery] using h0
            have hcons_q : consistentPred ((projTree c (cntOf ρF) (accOf ρF) l).toQuery dq) q x := by
              intro j
              have hj := hcons ⟨j.val + 1, by simp [j.isLt]⟩
              simpa [DTree.toQuery] using hj
            have hcomp_F : ∀ i : Fin n, cntOf ρF i = w i → x i = accOf ρF i := by
              intro i hi
              by_cases hib : i = b.1
              · subst hib; rw [haccF, Function.update_self, ha]; exact hx0
              · rw [hcntF', Function.update_of_ne hib] at hi
                rw [haccF, Function.update_of_ne hib]
                exact hcomp i hi
            simpa [DTree.toOut] using hL_ok q hq x hcomp_F hcons_q

private def subLeaves (N J : Finset (List Bool)) (u : List Bool) : Finset (List Bool) :=
  (N \ J).filter (fun p => u <+: p)

private theorem subLeaves_nil (N J : Finset (List Bool)) :
    subLeaves N J [] = N \ J := by
  ext p; simp [subLeaves]

private theorem shapePred_prefix_mem (N J : Finset (List Bool)) (hsh : shapePred N J) :
    ∀ (suf u : List Bool), u ++ suf ∈ N → u ∈ N := by
  intro suf
  induction suf with
  | nil => intro u h; simpa using h
  | cons b tl ih =>
    intro u h
    have h1 : (u ++ [b]) ++ tl ∈ N := by simpa [List.append_assoc] using h
    have h2 : u ++ [b] ∈ N := ih (u ++ [b]) h1
    exact hsh.2.1 (hsh.2.2.1 u b h2)

private theorem subLeaves_leaf (N J : Finset (List Bool)) (hsh : shapePred N J)
    (u : List Bool) (huN : u ∈ N) (huJ : u ∉ J) :
    subLeaves N J u = {u} := by
  ext p
  simp only [subLeaves, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hpN, _⟩, ⟨suf, rfl⟩⟩
    cases suf with
    | nil => simp
    | cons b suf' =>
      exfalso
      have h1 : (u ++ [b]) ++ suf' ∈ N := by simpa [List.append_assoc] using hpN
      have hpre : u ++ [b] ∈ N := shapePred_prefix_mem N J hsh suf' (u ++ [b]) h1
      exact huJ (hsh.2.2.1 u b hpre)
  · rintro rfl
    exact ⟨⟨huN, huJ⟩, List.prefix_refl _⟩

private theorem subLeaves_branch (N J : Finset (List Bool)) (_hsh : shapePred N J)
    (u : List Bool) (huJ : u ∈ J) :
    subLeaves N J u = subLeaves N J (u ++ [false]) ∪ subLeaves N J (u ++ [true]) ∧
    Disjoint (subLeaves N J (u ++ [false])) (subLeaves N J (u ++ [true])) := by
  constructor
  · ext p
    simp only [subLeaves, Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨hpN, hpJ⟩, ⟨suf, rfl⟩⟩
      cases suf with
      | nil =>
        rw [List.append_nil] at hpJ
        exact absurd huJ hpJ
      | cons b suf' =>
        cases b
        · exact Or.inl ⟨⟨hpN, hpJ⟩, ⟨suf', by simp [List.append_assoc]⟩⟩
        · exact Or.inr ⟨⟨hpN, hpJ⟩, ⟨suf', by simp [List.append_assoc]⟩⟩
    · rintro (⟨hp, ⟨suf, rfl⟩⟩ | ⟨hp, ⟨suf, rfl⟩⟩)
      · exact ⟨hp, ⟨false :: suf, by simp [List.append_assoc]⟩⟩
      · exact ⟨hp, ⟨true :: suf, by simp [List.append_assoc]⟩⟩
  · rw [Finset.disjoint_left]
    intro p hp1 hp2
    rcases (Finset.mem_filter.mp hp1).2 with ⟨s1, rfl⟩
    rcases (Finset.mem_filter.mp hp2).2 with ⟨s2, heq⟩
    have htail : false :: s1 = true :: s2 := by
      have h1 : u ++ (false :: s1) = u ++ (true :: s2) := by
        simpa [List.append_assoc] using heq.symm
      exact List.append_cancel_left h1
    exact Bool.noConfusion (List.cons.inj htail).1

private theorem bank_count_eq_cntOf {n : ℕ} {w : Fin n → ℕ}
    (L : List (RawT n w)) (hnd : L.Nodup) (ρ : RawT n w → Option Bool)
    (hdom : ∀ b, (ρ b).isSome ↔ b ∈ L) (i : Fin n) :
    (L.map Sigma.fst).count i = cntOf ρ i := by
  classical
  have hcnt_list : ∀ (M : List (RawT n w)), M.Nodup →
      (M.map Sigma.fst).count i =
        ((Finset.univ : Finset (Fin (w i))).filter (fun j => (⟨i, j⟩ : RawT n w) ∈ M)).card := by
    intro M
    induction M with
    | nil => intro _; simp
    | cons hd tl ih =>
      intro hM
      rcases List.nodup_cons.mp hM with ⟨hnot, htl⟩
      rw [List.map_cons, List.count_cons, ih htl]
      by_cases hhi : hd.1 = i
      · cases hd with | mk i0 j0 =>
        dsimp only at hhi
        subst hhi
        simp only [beq_self_eq_true, ↓reduceIte]
        have hset :
            Finset.univ.filter (fun j : Fin (w i0) => (⟨i0, j⟩ : RawT n w) ∈ ⟨i0, j0⟩ :: tl) =
            insert j0 (Finset.univ.filter (fun j : Fin (w i0) => (⟨i0, j⟩ : RawT n w) ∈ tl)) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, List.mem_cons]
          constructor
          · rintro (heq | htl')
            · left; cases heq; rfl
            · right; exact htl'
          · rintro (rfl | htl')
            · exact Or.inl rfl
            · exact Or.inr htl'
        have hnm : j0 ∉ Finset.univ.filter (fun j : Fin (w i0) => (⟨i0, j⟩ : RawT n w) ∈ tl) := by
          simpa using hnot
        rw [hset, Finset.card_insert_of_notMem hnm]
      · have hbeq : (hd.1 == i) = false := beq_false_of_ne hhi
        simp only [hbeq, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        congr 1
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_cons]
        have hne : (⟨i, j⟩ : RawT n w) ≠ hd := fun h => hhi (congrArg Sigma.fst h.symm)
        simp [hne]
  rw [hcnt_list L hnd]
  unfold cntOf
  congr 1
  ext j
  simp [hdom ⟨i, j⟩]

private theorem solve_718 (n : ℕ) (hn : 0 < n) (w : Fin n → ℕ) (hw : ∀ i, 0 < w i)
    (m : ℕ) (R : (Fin n → Bool) → Fin m → Prop) (price : Fin m → ℕ) (H : ℕ)
    (N J : Finset (List Bool)) (ask : List Bool → RawT n w) (ans : List Bool → Fin m)
    (hsh : shapePred N J) (hN : ∀ p ∈ N, (traceFn ask p).Nodup ∧ p.length ≤ H)
    (hleaf : ∀ p ∈ N \ J, ∀ y, consistentPred ask p y → R (parityFn y) (ans p)) :
    let D := ∑ i, w i
    let waste := fun p : List Bool =>
      let bank := (traceFn ask p).map Sigma.fst
      ∑ i : Fin n, if bank.count i < w i then bank.count i else 0
    ∃ (M A : Finset (List Bool)) (q : List Bool → Fin n) (out : List Bool → Fin m),
      shapePred M A ∧ (∀ p ∈ M, (traceFn q p).Nodup ∧ ((traceFn q p).map w).sum ≤ H) ∧
      (∀ p ∈ M \ A, ∀ x, consistentPred q p x → R x (out p)) ∧
      2 ^ D * (M \ A).sum (fun p => price (out p) * 2 ^ (((traceFn q p).map w).sum - p.length)) ≤
        (N \ J).sum (fun p => price (ans p) * 2 ^ (D - waste p)) := by
  classical
  dsimp only
  let D := ∑ i, w i
  let waste : List Bool → ℕ := fun p =>
    let bank := (traceFn ask p).map Sigma.fst
    ∑ i : Fin n, if bank.count i < w i then bank.count i else 0
  have hbuild : ∀ (k : ℕ) (u : List Bool) (ρ : RawT n w → Option Bool),
      H - u.length ≤ k →
      u ∈ N →
      (∀ b, (ρ b).isSome ↔ b ∈ traceFn ask u) →
      (∀ y : RawT n w → Bool, (∀ b v, ρ b = some v → y b = v) → consistentPred ask u y) →
      ∃ t : DTree (RawT n w) (Fin m),
        t.NoRep (fun b => (ρ b).isSome) ∧
        t.height ≤ H - u.length ∧
        t.LeafValid R ρ ∧
        rawPriceWeight w price (cntOf ρ) t =
          (subLeaves N J u).sum (fun p => price (ans p) * 2 ^ (D - waste p)) := by
    intro k
    induction k with
    | zero =>
      intro u ρ hk huN hdom hcons
      by_cases huJ : u ∈ J
      · exfalso
        have hlen := (hN (u ++ [false]) (hsh.2.2.2 u huJ).1).2
        simp only [List.length_append, List.length_singleton] at hlen
        omega
      · refine ⟨DTree.leaf (ans u), trivial, Nat.zero_le _, ?_, ?_⟩
        · intro y hy
          exact hleaf u (Finset.mem_sdiff.mpr ⟨huN, huJ⟩) y (hcons y hy)
        · rw [subLeaves_leaf N J hsh u huN huJ, Finset.sum_singleton]
          simp only [rawPriceWeight, D, waste]
          congr 2
          congr 1
          unfold incSum
          apply Finset.sum_congr rfl
          intro i _
          rw [bank_count_eq_cntOf (traceFn ask u) (hN u huN).1 ρ hdom i]
    | succ k ih =>
      intro u ρ hk huN hdom hcons
      by_cases huJ : u ∈ J
      · have huF_N : u ++ [false] ∈ N := (hsh.2.2.2 u huJ).1
        have huT_N : u ++ [true] ∈ N := (hsh.2.2.2 u huJ).2
        have hlenF := (hN (u ++ [false]) huF_N).2
        simp only [List.length_append, List.length_singleton] at hlenF
        have hndF : (traceFn ask u ++ [ask u]).Nodup := by
          rw [← traceFn_append_one]; exact (hN (u ++ [false]) huF_N).1
        have hnotmem : ask u ∉ traceFn ask u := by
          intro hm
          exact (List.nodup_append.mp hndF).2.2 (ask u) hm (ask u) (List.mem_singleton_self _) rfl
        have hnone : ¬ (ρ (ask u)).isSome := fun h => hnotmem ((hdom _).mp h)
        let ρF := Function.update ρ (ask u) (some false)
        let ρT := Function.update ρ (ask u) (some true)
        have hdomF : ∀ b, (ρF b).isSome ↔ b ∈ traceFn ask (u ++ [false]) := by
          intro b
          rw [traceFn_append_one, List.mem_append, List.mem_singleton]
          by_cases hb : b = ask u
          · subst hb; simp [ρF]
          · simp [ρF, hb, hdom b]
        have hdomT : ∀ b, (ρT b).isSome ↔ b ∈ traceFn ask (u ++ [true]) := by
          intro b
          rw [traceFn_append_one, List.mem_append, List.mem_singleton]
          by_cases hb : b = ask u
          · subst hb; simp [ρT]
          · simp [ρT, hb, hdom b]
        have hconsF : ∀ y, (∀ b v, ρF b = some v → y b = v) → consistentPred ask (u ++ [false]) y := by
          intro y hy j
          by_cases hj : j.val < u.length
          · have ht : (u ++ [false]).take j.val = u.take j.val :=
              List.take_append_of_le_length (le_of_lt hj)
            have hg : (u ++ [false]).get j = u.get ⟨j.val, hj⟩ := by
              simp [List.getElem_append_left hj]
            rw [ht, hg]
            refine hcons y (fun b v hv => hy b v ?_) ⟨j.val, hj⟩
            have hne : b ≠ ask u := fun h => by subst h; rw [hv] at hnone; simp at hnone
            simp [ρF, hne, hv]
          · have hjeq : j.val = u.length := by
              have hlt := j.isLt; simp only [List.length_append, List.length_singleton] at hlt; omega
            have ht : (u ++ [false]).take j.val = u := by
              rw [hjeq, List.take_append_of_le_length le_rfl, List.take_length]
            have hg : (u ++ [false]).get j = false := by
              simp [hjeq]
            rw [ht, hg]
            exact hy (ask u) false (by simp [ρF])
        have hconsT : ∀ y, (∀ b v, ρT b = some v → y b = v) → consistentPred ask (u ++ [true]) y := by
          intro y hy j
          by_cases hj : j.val < u.length
          · have ht : (u ++ [true]).take j.val = u.take j.val :=
              List.take_append_of_le_length (le_of_lt hj)
            have hg : (u ++ [true]).get j = u.get ⟨j.val, hj⟩ := by
              simp [List.getElem_append_left hj]
            rw [ht, hg]
            refine hcons y (fun b v hv => hy b v ?_) ⟨j.val, hj⟩
            have hne : b ≠ ask u := fun h => by subst h; rw [hv] at hnone; simp at hnone
            simp [ρT, hne, hv]
          · have hjeq : j.val = u.length := by
              have hlt := j.isLt; simp only [List.length_append, List.length_singleton] at hlt; omega
            have ht : (u ++ [true]).take j.val = u := by
              rw [hjeq, List.take_append_of_le_length le_rfl, List.take_length]
            have hg : (u ++ [true]).get j = true := by
              simp [hjeq]
            rw [ht, hg]
            exact hy (ask u) true (by simp [ρT])
        rcases ih (u ++ [false]) ρF (by simp; omega) huF_N hdomF hconsF with
          ⟨tF, hnrF, hhF, hvF, hwF⟩
        rcases ih (u ++ [true]) ρT (by simp; omega) huT_N hdomT hconsT with
          ⟨tT, hnrT, hhT, hvT, hwT⟩
        have hcntF := cntOf_update ρ (ask u) false hnone
        have hcntT := cntOf_update ρ (ask u) true hnone
        have hcnt_eq : cntOf ρF = cntOf ρT := hcntF.trans hcntT.symm
        have hsub := subLeaves_branch N J hsh u huJ
        refine ⟨DTree.branch (ask u) tF tT, ?_, ?_, ⟨hvF, hvT⟩, ?_⟩
        · refine ⟨hnone, ?_, ?_⟩
          · exact hnrF.mono (fun x hx => by
              rcases hx with hx1 | rfl
              · by_cases hxu : x = ask u
                · subst hxu; simp [ρF]
                · simp [ρF, hxu, hx1]
              · simp [ρF])
          · exact hnrT.mono (fun x hx => by
              rcases hx with hx1 | rfl
              · by_cases hxu : x = ask u
                · subst hxu; simp [ρT]
                · simp [ρT, hxu, hx1]
              · simp [ρT])
        · simp only [DTree.height, List.length_append, List.length_singleton] at hhF hhT ⊢
          omega
        · simp only [rawPriceWeight]
          rw [← hcntF, hwF, hcnt_eq, hwT, ← Finset.sum_union hsub.2, ← hsub.1]
      · refine ⟨DTree.leaf (ans u), trivial, Nat.zero_le _, ?_, ?_⟩
        · intro y hy
          exact hleaf u (Finset.mem_sdiff.mpr ⟨huN, huJ⟩) y (hcons y hy)
        · rw [subLeaves_leaf N J hsh u huN huJ, Finset.sum_singleton]
          simp only [rawPriceWeight, D, waste]
          congr 2
          congr 1
          unfold incSum
          apply Finset.sum_congr rfl
          intro i _
          rw [bank_count_eq_cntOf (traceFn ask u) (hN u huN).1 ρ hdom i]
  let ρ0 : RawT n w → Option Bool := fun _ => none
  have hρ0_cnt : cntOf ρ0 = fun _ => 0 := by funext i; simp [cntOf, ρ0]
  rcases hbuild H [] ρ0 (by simp) hsh.1 (by simp [ρ0, traceFn])
      (fun _ _ j => Fin.elim0 j) with ⟨T_raw, hnr, hht, hval, hraw_eq⟩
  rw [subLeaves_nil] at hraw_eq
  have hsum_eq :
      2 ^ D * (∑ c : CoinTape n w, outerPriceWeight w price (projTree c (cntOf ρ0) (accOf ρ0) T_raw)) =
      Fintype.card (CoinTape n w) * (N \ J).sum (fun p => price (ans p) * 2 ^ (D - waste p)) := by
    have h := sum_outerPriceWeight_projTree_eq price T_raw ρ0 hnr
    rw [hρ0_cnt, pot_zero w hw, mul_one] at h
    rw [← hρ0_cnt, hraw_eq] at h
    exact h
  have hex_c : ∃ c : CoinTape n w,
      2 ^ D * outerPriceWeight w price (projTree c (cntOf ρ0) (accOf ρ0) T_raw) ≤
        (N \ J).sum (fun p => price (ans p) * 2 ^ (D - waste p)) := by
    by_contra hno
    push Not at hno
    have hlt_sum :
        ∑ _ : CoinTape n w, (N \ J).sum (fun p => price (ans p) * 2 ^ (D - waste p)) <
        ∑ c : CoinTape n w, 2 ^ D * outerPriceWeight w price (projTree c (cntOf ρ0) (accOf ρ0) T_raw) := by
      apply Finset.sum_lt_sum_of_nonempty
      · exact ⟨fun _ _ => false, Finset.mem_univ _⟩
      · intro c _; exact hno c
    rw [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, smul_eq_mul, hsum_eq] at hlt_sum
    omega
  rcases hex_c with ⟨c, hc_le⟩
  let dq : Fin n := ⟨0, hn⟩
  let dout : Fin m := ans []
  let T_out := projTree c (cntOf ρ0) (accOf ρ0) T_raw
  rcases projTree_props hw R c dq dout T_raw ρ0 hnr hval with ⟨hout_nr, hout_ht, hout_ok⟩
  refine ⟨T_out.toNodes, T_out.toIntern, T_out.toQuery dq, T_out.toOut dout, T_out.toShape, ?_, ?_, ?_⟩
  · intro p hp
    constructor
    · exact DTree.trace_nodup_of_noRep dq T_out _ hout_nr p hp
    · have h1 := weightedHeight_ge_path w dq T_out p hp
      have hinc0 : incSum w (cntOf ρ0) = 0 := by rw [hρ0_cnt, incSum_zero w hw]
      rw [hinc0, add_zero] at hout_ht
      simp only [List.length_nil, Nat.sub_zero] at hht
      dsimp only [T_out] at h1 ⊢
      omega
  · intro p hp x hcons
    rw [DTree.toNodes_sdiff_toIntern] at hp
    refine hout_ok p hp x (fun i hi => ?_) hcons
    exfalso
    rw [hρ0_cnt] at hi
    dsimp only at hi
    have := hw i
    omega
  · rw [DTree.toNodes_sdiff_toIntern, outerPriceWeight_eq_sum_toLeaves w hw price dq dout T_out]
    exact hc_le

end PEqualNP.Outside.L_lib_718_aux

theorem PEqualNP.Outside.L_lib_718 : (
∀ (n : ℕ) (hn : 0 < n) (w : Fin n → ℕ), (∀ i, 0 < w i) →
  let Raw := (i : Fin n) × Fin (w i)
  let parity := fun (y : Raw → Bool) (i : Fin n) =>
    decide (Odd ((Finset.univ : Finset (Fin (w i))).filter (fun j => y ⟨i,j⟩ = true)).card)
  let shape := fun (N J : Finset (List Bool)) =>
    [] ∈ N ∧ J ⊆ N ∧
    (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
    ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N
  let trace := fun {V : Type} (ask : List Bool → V) (p : List Bool) =>
    List.ofFn (fun j : Fin p.length => ask (p.take j.val))
  let consistent := fun {V : Type} (ask : List Bool → V) (p : List Bool) (x : V → Bool) =>
    ∀ j : Fin p.length, x (ask (p.take j.val)) = p.get j
  ∀ (m : ℕ) (R : (Fin n → Bool) → Fin m → Prop) (price : Fin m → ℕ) (H : ℕ)
    (N J : Finset (List Bool)) (ask : List Bool → Raw) (ans : List Bool → Fin m),
    shape N J → (∀ p ∈ N, (trace ask p).Nodup ∧ p.length ≤ H) →
    (∀ p ∈ N \ J, ∀ y, consistent ask p y → R (parity y) (ans p)) →
    let D := ∑ i, w i
    let waste := fun p : List Bool =>
      let bank := (trace ask p).map Sigma.fst
      ∑ i : Fin n, if bank.count i < w i then bank.count i else 0
    ∃ (M A : Finset (List Bool)) (q : List Bool → Fin n) (out : List Bool → Fin m),
      shape M A ∧ (∀ p ∈ M, (trace q p).Nodup ∧ ((trace q p).map w).sum ≤ H) ∧
      (∀ p ∈ M \ A, ∀ x, consistent q p x → R x (out p)) ∧
      2^D * (M \ A).sum (fun p => price (out p) * 2^(((trace q p).map w).sum - p.length)) ≤
        (N \ J).sum (fun p => price (ans p) * 2^(D-waste p))
) := by
  intro n hn w hw Raw parity shape trace consistent m R price H N J ask ans hsh hN hleaf
  exact PEqualNP.Outside.L_lib_718_aux.solve_718 n hn w hw m R price H N J ask ans hsh hN hleaf
