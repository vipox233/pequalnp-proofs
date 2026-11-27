import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25472_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover

def compute (x : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => x.getD i false)

def step (x : List Bool) (g : Gate) : List Bool := x ++ [compute x g]

theorem snoc (l : List Bool) (b : Bool) (i : ℕ) :
    (l ++ [b]).getD i false =
      if i < l.length then l.getD i false else if i = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2
    simp
  · rw [List.getElem?_eq_none (by simp; omega)]
    rfl

def Below (x y : List Bool) : Prop := ∀ i, x.getD i false = true → y.getD i false = true

theorem compute_monotone {x y : List Bool} (h : Below x y) {g : Gate}
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
    compute x g = true → compute y g = true := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with e | e
  · simp only [compute, e, GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
    intro h0 a ha
    obtain ⟨i, hi, rfl⟩ := ha
    exact h i (h0 _ ⟨i, hi, rfl⟩)
  · simp only [compute, e, GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨a, ⟨i, hi, rfl⟩, ea⟩
    exact ⟨y.getD i false, ⟨i, hi, rfl⟩, h i ea⟩

theorem fold_monotone (gs : List Gate) (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    {x y : List Bool} (he : x.length = y.length) (h : Below x y) :
    Below (gs.foldl step x) (gs.foldl step y) := by
  induction gs generalizing x y with
  | nil => exact h
  | cons g gs ih =>
    have hnext : Below (step x g) (step y g) := by
      intro i hi
      simp only [step, snoc, ← he] at hi ⊢
      split_ifs at hi ⊢
      · exact h i hi
      · exact compute_monotone h (hg g (by simp)) hi
    exact ih (fun a ha => hg a (List.mem_cons_of_mem _ ha)) (by simp [step, he]) hnext


theorem len (gs : List Gate) (x : List Bool) : (gs.foldl step x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih => simp [List.foldl_append, step, ih]; omega


theorem setD (l : List Bool) (k i : ℕ) :
    (l.set k false).getD i false = if i = k then false else l.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set, List.getD_eq_getElem?_getD]
  by_cases h : k = i
  · subst h; simp only [ite_true]; split_ifs <;> rfl
  · simp [h, Ne.symm h]


theorem each_value {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) :
    (oneEach u v).getD i false = decide (i = u.val ∨ i = n + v.val) := by
  have hu := u.isLt
  have hv := v.isLt
  apply Bool.eq_iff_iff.2
  simp only [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_ofFn,
    List.getElem?_ofFn]
  split_ifs <;> simp [Fin.ext_iff] <;> omega

theorem getD_ge (W : List Bool) (i : ℕ) (h : W.length ≤ i) : W.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem pre (gs : List Gate) : ∀ (x : List Bool) (w : ℕ), w < x.length →
    (gs.foldl step x).getD w false = x.getD w false := by
  induction gs with
  | nil => intro x w _; rfl
  | cons g gs ih =>
    intro x w h
    rw [List.foldl_cons, ih _ _ (by simp [step]; omega), step, snoc, ite_eq_left h]

lemma foldl_char (gs : List Gate) (w : List Bool) :
    ∀ j, j < gs.length → (gs.foldl step w).getD (w.length + j) false =
      (gs.getD j ⟨GateOp.or, []⟩).op.eval ((gs.getD j ⟨GateOp.or, []⟩).inputs.map fun i =>
        if i < w.length + j then (gs.foldl step w).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen := len gs w
    simp only [List.length_append, List.length_singleton] at hj
    have key : ∀ i, i < w.length + gs.length →
        (step (gs.foldl step w) g).getD i false = (gs.foldl step w).getD i false := by
      intro i hi
      simp only [step, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_or_ge j gs.length with h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [e1, key _ (by omega), ih j h]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i (by omega)]
      · rfl
    · have hj' : j = gs.length := by omega
      subst hj'
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      have e2 : (step (gs.foldl step w) g).getD (w.length + gs.length) false =
          g.op.eval (g.inputs.map fun i => (gs.foldl step w).getD i false) := by
        simp only [step, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen, compute, List.getD_eq_getElem?_getD]
      rw [e2]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i hi]
      · simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by omega)]
        rfl




theorem gate_formula (C : Circuit) {N j : ℕ} (x : List Bool)
    (hx : x.length = N) (hj : j < C.gates.length) :
    (C.gates.foldl step x).getD (N + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
        if i < N + j then (C.gates.foldl step x).getD i false else false) := by
  have h := foldl_char C.gates x j hj
  rw [hx] at h
  exact h

def before (C : Circuit) (N j w : ℕ) : Prop := w ∈ (gateAt C j).inputs ∧ w < N + j

def closed (N : ℕ) (C : Circuit) (L : Finset ℕ) : Prop :=
  (∀ j ∈ L, j < C.gates.length) ∧
    ∀ j ∈ L, ∀ i, before C N j (N + i) → i ∈ L

theorem minimal_closed (N : ℕ) (C : Circuit) (r : ℕ) (hr : r < C.gates.length) :
    ∃ L : Finset ℕ, r ∈ L ∧ closed N C L ∧
      ∀ i ∈ L, i ≠ r → ∃ j ∈ L, before C N j (N + i) := by
  classical
  let A := Finset.range C.gates.length
  have hc : closed N C A := by
    refine ⟨fun j hj => Finset.mem_range.mp hj, ?_⟩
    intro j hj i hi
    have hlt := Finset.mem_range.mp hj
    have hs := hi.2
    exact Finset.mem_range.mpr (by omega)
  let candidates := A.powerset.filter fun L => r ∈ L ∧ closed N C L
  have hA : A ∈ candidates := Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.Subset.refl _), Finset.mem_range.mpr hr, hc⟩
  obtain ⟨L, hL, hmin⟩ := candidates.exists_min_image Finset.card ⟨A, hA⟩
  obtain ⟨hsub, hrL, hclose⟩ := Finset.mem_filter.mp hL
  refine ⟨L, hrL, hclose, ?_⟩
  intro i hi hir
  by_contra hn
  have hs : L.erase i ∈ candidates := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, Finset.mem_erase.mpr ⟨Ne.symm hir, hrL⟩, ?_⟩
    · exact (Finset.erase_subset _ _).trans (Finset.mem_powerset.mp hsub)
    · constructor
      · intro j hj
        exact hclose.1 j (Finset.mem_of_mem_erase hj)
      · intro j hj k hkj
        have hj' := Finset.mem_of_mem_erase hj
        refine Finset.mem_erase.mpr ⟨?_, hclose.2 j hj' k hkj⟩
        rintro rfl
        exact hn ⟨j, hj', hkj⟩
  have h := hmin _ hs
  have hpos := Finset.card_pos.mpr ⟨i, hi⟩
  rw [Finset.card_erase_of_mem hi] at h
  omega

def inputSlots (N : ℕ) (C : Circuit) (j : ℕ) : Finset (ℕ × ℕ) :=
  ((gateAt C j).inputs.toFinset.filter (· < N + j)).image (Prod.mk j)

def slots (N : ℕ) (C : Circuit) (L : Finset ℕ) : Finset (ℕ × ℕ) :=
  L.biUnion (inputSlots N C)

theorem mem_slot {N : ℕ} {C : Circuit} {L : Finset ℕ} {j w : ℕ} :
    (j,w) ∈ slots N C L ↔ j ∈ L ∧ before C N j w := by
  constructor
  · intro h
    obtain ⟨j', hj', hh⟩ := Finset.mem_biUnion.mp h
    obtain ⟨w', hw', he⟩ := Finset.mem_image.mp hh
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl,rfl⟩ := he
    have ⟨hi,hl⟩ := Finset.mem_filter.mp hw'
    exact ⟨hj', List.mem_toFinset.mp hi, hl⟩
  · rintro ⟨hj, hw, hl⟩
    exact Finset.mem_biUnion.mpr
      ⟨j,hj,Finset.mem_image.mpr ⟨w,Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hw,hl⟩,rfl⟩⟩

def used (N : ℕ) (C : Circuit) (L : Finset ℕ) : Finset ℕ :=
  (slots N C L).image Prod.snd

theorem mem_used {N : ℕ} {C : Circuit} {L : Finset ℕ} {w : ℕ} :
    w ∈ used N C L ↔ ∃ j ∈ L, before C N j w := by
  constructor
  · intro h
    obtain ⟨⟨j,i⟩, hslot, e⟩ := Finset.mem_image.mp h
    change i = w at e
    subst i
    exact ⟨j,(mem_slot.mp hslot).1,(mem_slot.mp hslot).2⟩
  · rintro ⟨j,hj,hw⟩
    exact Finset.mem_image.mpr ⟨(j,w),mem_slot.mpr ⟨hj,hw⟩,rfl⟩

theorem closed_values {N : ℕ} {C : Circuit} {L : Finset ℕ}
    (hL : closed N C L) (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (he : ∀ i ∈ used N C L, x.getD i false = y.getD i false) :
    ∀ j ∈ L, (C.gates.foldl step x).getD (N + j) false =
      (C.gates.foldl step y).getD (N + j) false := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj
    rw [gate_formula C x hx (hL.1 j hj), gate_formula C y hy (hL.1 j hj)]
    congr 1
    apply List.map_congr_left
    intro w hw
    split_ifs with hb <;> try rfl
    by_cases hi : w < N
    · rw [pre _ _ _ (by omega : w < x.length), pre _ _ _ (by omega : w < y.length)]
      exact he w (mem_used.mpr ⟨j,hj,hw,hb⟩)
    · let i := w - N
      have e : N + i = w := by dsimp [i]; omega
      have hil : i < j := by omega
      rw [← e] at hw hb ⊢
      exact ih i hil (hL.2 j hj i ⟨hw,hb⟩)

theorem needed {N : ℕ} {C : Circuit} (hC : Monotone2 C) {L : Finset ℕ}
    (hL : closed N C L) {r : ℕ} (hr : r ∈ L) (hout : C.output = N + r)
    {x y : List Bool} (hx : x.length = N) (hy : y.length = N) (i : ℕ)
    (he : Below (x.set i false) y) (ht : C.eval x = true) (hf : C.eval y = false) :
    i ∈ used N C L := by
  by_contra h
  have hr' : C.eval x = C.eval (x.set i false) := by
    change (C.gates.foldl step x).getD C.output false =
      (C.gates.foldl step (x.set i false)).getD C.output false
    rw [hout]
    refine closed_values hL x (x.set i false) hx (by simp [hx]) ?_ r hr
    intro a ha
    have hn : a ≠ i := fun e => h (e ▸ ha)
    rw [setD, ite_eq_right hn]
  have hmono := fold_monotone C.gates (fun a ha => (hC a ha).1)
    (show (x.set i false).length = y.length by simp [hx, hy]) he C.output
  have hv : C.eval y = true := hmono (hr'.symm.trans ht)
  rw [hf] at hv
  contradiction

theorem inputSlots_card (N : ℕ) (C : Circuit) (j : ℕ) :
    (inputSlots N C j).card = ((gateAt C j).inputs.toFinset.filter (· < N + j)).card :=
  Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h)

theorem output_shape {n m : ℕ} (C : Circuit) (hC : Monotone2 C)
    (hsmall : C.gates.length ≤ n + m - 1) (hraw : n + m ≤ C.output)
    (hout : C.output < n + m + C.gates.length)
    (hsupport : ∀ (L : Finset ℕ) (r : ℕ), closed (n + m) C L → r ∈ L →
      C.output = n + m + r → Finset.range (n + m) ⊆ used (n + m) C L) :
    (∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
      ReadsBack (n + m) C ∧ (∀ i, readsIn C (Finset.range C.gates.length) i ≤ 1) ∧
      C.output < (n + m) + C.gates.length ∧ readsIn C (Finset.range C.gates.length) C.output = 0 := by
  classical
  let r := C.output - (n + m)
  have er : C.output = (n + m) + r := by dsimp [r]; omega
  have hr : r < C.gates.length := by dsimp [r]; omega
  obtain ⟨L, hrL, hL, huse⟩ := minimal_closed (n + m) C r hr
  have hused := hsupport L r hL hrL er
  let necessary := Finset.range (n + m)
  let inside : Finset ℕ := (L.erase r).image ((n + m) + ·)
  let required := necessary ∪ inside
  have hnec : ∀ w ∈ necessary, w < n + m := fun _ h => Finset.mem_range.mp h
  have hdis : Disjoint necessary inside := by
    apply Finset.disjoint_left.mpr
    intro w hw hi
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
    have := hnec _ hw
    omega
  have hreq : required ⊆ used (n + m) C L := by
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact hused hw
    · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hj
      exact mem_used.mpr (huse j hmem hne)
  have hsize : required.card = n + m + (L.card - 1) := by
    unfold required inside
    rw [Finset.card_union_of_disjoint hdis,
      Finset.card_image_of_injective _ (fun a b hi => by omega), Finset.card_erase_of_mem hrL]
    exact congrArg (· + (L.card - 1)) (Finset.card_range (n + m))
  have hfit (j : ℕ) (hj : j < C.gates.length) :
      (gateAt C j).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ (gateAt C j).inputs.length ≤ 2 := by
    apply hC
    rw [gateAt, List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem _
  have hwsize (j : ℕ) (hj : j ∈ L) : (inputSlots (n + m) C j).card ≤ 2 := by
    rw [inputSlots_card]
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans
      ((List.toFinset_card_le _).trans (hfit _ (hL.1 j hj)).2)
  have hle := Finset.card_biUnion_le_card_mul L (inputSlots (n + m) C) 2 hwsize
  change (slots (n + m) C L).card ≤ L.card * 2 at hle
  have hcap := Finset.card_image_le (s := slots (n + m) C L) (f := Prod.snd)
  change (used (n + m) C L).card ≤ (slots (n + m) C L).card at hcap
  have hn := Finset.card_le_card hreq
  have hLsub : L ⊆ Finset.range C.gates.length := fun j hj => Finset.mem_range.mpr (hL.1 j hj)
  have hLc : L.card ≤ C.gates.length := by simpa using Finset.card_le_card hLsub
  have hp := Finset.card_pos.mpr ⟨r, hrL⟩
  have heL : L.card = n + m - 1 := by omega
  have hfull : L = Finset.range C.gates.length :=
    Finset.eq_of_subset_of_card_le hLsub (by rw [Finset.card_range]; omega)
  have hunique : Set.InjOn Prod.snd (slots (n + m) C L : Set (ℕ × ℕ)) :=
    Finset.injOn_of_card_image_eq (show (used (n + m) C L).card = (slots (n + m) C L).card by omega)
  have heUsed : required = used (n + m) C L := Finset.eq_of_subset_of_card_le hreq (by omega)
  have slot_full (j : ℕ) (hj : j ∈ L) : (inputSlots (n + m) C j).card = 2 := by
    have hsum := Finset.card_biUnion_le (s := L) (t := inputSlots (n + m) C)
    change (slots (n + m) C L).card ≤ ∑ k ∈ L, (inputSlots (n + m) C k).card at hsum
    have hsum' : (∑ k ∈ L.erase j, (inputSlots (n + m) C k).card) ≤
        (L.erase j).card * 2 := by
      calc
        _ ≤ ∑ _ ∈ L.erase j, (2 : ℕ) := by
          exact Finset.sum_le_sum fun k hk => hwsize k (Finset.mem_of_mem_erase hk)
        _ = _ := by simp
    have hsplit := Finset.sum_erase_add L (fun k => (inputSlots (n + m) C k).card) hj
    rw [Finset.card_erase_of_mem hj] at hsum'
    have h2 := hwsize j hj
    omega
  have local_size (j : ℕ) (hj : j < C.gates.length) :
      (gateAt C j).inputs.length = 2 ∧ (gateAt C j).inputs.Nodup ∧
        ∀ w ∈ (gateAt C j).inputs, w < (n + m) + j := by
    have hm : j ∈ L := hfull.symm ▸ Finset.mem_range.mpr hj
    have ha := slot_full j hm
    rw [inputSlots_card] at ha
    let us := (gateAt C j).inputs.toFinset
    have hb := List.toFinset_card_le (gateAt C j).inputs
    have hc := Finset.card_le_card (Finset.filter_subset (· < (n + m) + j) us)
    have hl := (hfit j hj).2
    change us.card ≤ (gateAt C j).inputs.length at hb
    change (us.filter (· < (n + m) + j)).card = 2 at ha
    have he : (gateAt C j).inputs.length = 2 := by omega
    have heq := Finset.eq_of_subset_of_card_le (Finset.filter_subset (· < (n + m) + j) us)
      (by omega : us.card ≤ (us.filter (· < (n + m) + j)).card)
    obtain ⟨a,b,hlist⟩ := List.length_eq_two.mp he
    refine ⟨he, ?_, ?_⟩
    · have hne : a ≠ b := by
        rintro rfl
        simp [us,hlist] at hc ha
        omega
      simp [hlist, hne]
    · intro w hw
      have hi : w ∈ us := List.mem_toFinset.mpr hw
      rw [← heq] at hi
      exact (Finset.mem_filter.mp hi).2
  have unique_gate {j k w : ℕ} (hj : j < C.gates.length) (hk : k < C.gates.length)
      (hw : w ∈ (gateAt C j).inputs) (hv : w ∈ (gateAt C k).inputs) : j = k := by
    have h1 : (j,w) ∈ slots (n + m) C L :=
      mem_slot.mpr ⟨hfull.symm ▸ Finset.mem_range.mpr hj, hw, (local_size j hj).2.2 w hw⟩
    have h2 : (k,w) ∈ slots (n + m) C L :=
      mem_slot.mpr ⟨hfull.symm ▸ Finset.mem_range.mpr hk, hv, (local_size k hk).2.2 w hv⟩
    exact congrArg Prod.fst (hunique h1 h2 rfl)
  refine ⟨?_, fun j hj => (local_size j hj).2.2, ?_, hout, ?_⟩
  · intro g hg
    obtain ⟨j, hj, hgj⟩ := List.mem_iff_getElem.mp hg
    have hgj' : gateAt C j = g := by rw [gateAt, List.getD_eq_getElem _ _ hj, hgj]
    have hop := (hfit j hj).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, hgj'] at hop
    exact ⟨hop, hgj' ▸ (local_size j hj).1⟩
  · intro w
    unfold readsIn
    by_cases h : ∃ j < C.gates.length, w ∈ (gateAt C j).inputs
    · obtain ⟨j,hj,hw⟩ := h
      rw [Finset.sum_eq_single j]
      · exact List.nodup_iff_count_le_one.mp (local_size j hj).2.1 w
      · intro k hk hkj
        exact List.count_eq_zero.mpr fun hn => hkj (unique_gate (Finset.mem_range.mp hk) hj hn hw)
      · intro hn
        exact (hn (Finset.mem_range.mpr hj)).elim
    · have hz : ∑ j ∈ Finset.range C.gates.length, (gateAt C j).inputs.count w = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        exact List.count_eq_zero.mpr fun hw => h ⟨j, Finset.mem_range.mp hj, hw⟩
      rw [hz]
      decide
  · unfold readsIn
    apply Finset.sum_eq_zero
    intro j hj
    apply List.count_eq_zero.mpr
    intro he
    have hj' := Finset.mem_range.mp hj
    have hh : C.output ∈ used (n + m) C L :=
      mem_used.mpr ⟨j, hfull.symm ▸ hj, he, (local_size j hj').2.2 _ he⟩
    rw [← heUsed] at hh
    rcases Finset.mem_union.mp hh with hh | hh
    · have := hnec _ hh
      omega
    · obtain ⟨i, hi, e⟩ := Finset.mem_image.mp hh
      have hn := (Finset.mem_erase.mp hi).1
      omega

variable {α : Type} [DecidableEq α]

def bits (s : Finset α) (i : α) : Bool := decide (i ∈ s)

def Local (s : Finset α) (f : (α → Bool) → Bool) : Prop :=
  ∀ x y, (∀ i ∈ s, x i = y i) → f x = f y

def hits (f : (α → Bool) → Bool) (a : α) : Prop := f (bits {a}) = true

def edge (f : (α → Bool) → Bool) (a b : α) : Prop := f (bits {a, b}) = true

def Rectangles (f : (α → Bool) → Bool) : Prop :=
  ∀ a b c d, f (bits {a}) = false → f (bits {b}) = false →
    f (bits {c}) = false → f (bits {d}) = false →
    edge f a b → edge f c b → edge f c d → edge f a d

def Spec (s : Finset α) (f : (α → Bool) → Bool) : Prop :=
  s.Nonempty ∧ Local s f ∧ f (bits ∅) = false ∧ f (fun _ => true) = true ∧ Rectangles f

theorem pair_without {s : Finset α} {f : (α → Bool) → Bool} (hf : Local s f) {a b : α}
    (ha : a ∉ s) : f (bits {a, b}) = f (bits {b}) := by
  apply hf
  intro i hi
  have hia : i ≠ a := fun h => ha (h ▸ hi)
  simp [bits, hia]

theorem single_without {s : Finset α} {f : (α → Bool) → Bool} (hf : Local s f) {a : α}
    (ha : a ∉ s) : f (bits {a}) = f (bits ∅) := by
  apply hf
  intro i hi
  have hia : i ≠ a := fun h => ha (h ▸ hi)
  simp [bits, hia]

theorem hit_in {s : Finset α} {f : (α → Bool) → Bool} (hf : Local s f)
    (hzero : f (bits ∅) = false) {a : α} (ha : hits f a) : a ∈ s := by
  by_contra h
  change f (bits {a}) = true at ha
  rw [single_without hf h, hzero] at ha
  contradiction

theorem edge_comm {f : (α → Bool) → Bool} {a b : α} : edge f a b ↔ edge f b a := by
  simp only [edge, Finset.pair_comm a b]

theorem edge_inside {s : Finset α} {f : (α → Bool) → Bool} (hf : Local s f)
    {a b : α} (ha : f (bits {a}) = false) (hb : f (bits {b}) = false)
    (hab : edge f a b) : a ∈ s ∧ b ∈ s := by
  have left {i j : α} (h0 : f (bits {j}) = false) (h : edge f i j) : i ∈ s := by
    by_contra hi
    change f (bits {i, j}) = true at h
    rw [pair_without hf hi, h0] at h
    contradiction
  exact ⟨left hb hab, left ha (edge_comm.mp hab)⟩

theorem or_rectangles {s t : Finset α} {f g : (α → Bool) → Bool}
    (hdis : Disjoint s t) (hf : Local s f) (hg : Local t g)
    (rf : Rectangles f) (rg : Rectangles g) : Rectangles (fun x => f x || g x) := by
  intro a b c d ha hb hc hd hab hcb hcd
  have sf {i : α} (h : (f (bits {i}) || g (bits {i})) = false) :
      f (bits {i}) = false := (Bool.or_eq_false_iff.mp h).1
  have sg {i : α} (h : (f (bits {i}) || g (bits {i})) = false) :
      g (bits {i}) = false := (Bool.or_eq_false_iff.mp h).2
  have hnot {i : α} (hi : i ∈ s) (hj : i ∈ t) : False := Finset.disjoint_left.mp hdis hi hj
  change (f (bits {a, b}) || g (bits {a, b})) = true at hab
  change (f (bits {c, b}) || g (bits {c, b})) = true at hcb
  change (f (bits {c, d}) || g (bits {c, d})) = true at hcd
  have hresult : edge f a d ∨ edge g a d := by
    rcases Bool.or_eq_true_iff.mp hab with hab | hab
    · have hb' := (edge_inside hf (sf ha) (sf hb) hab).2
      have hcb' : edge f c b := (Bool.or_eq_true_iff.mp hcb).resolve_right
        (fun h => hnot hb' (edge_inside hg (sg hc) (sg hb) h).2)
      have hc' := (edge_inside hf (sf hc) (sf hb) hcb').1
      have hcd' : edge f c d := (Bool.or_eq_true_iff.mp hcd).resolve_right
        (fun h => hnot hc' (edge_inside hg (sg hc) (sg hd) h).1)
      exact Or.inl (rf a b c d (sf ha) (sf hb) (sf hc) (sf hd) hab hcb' hcd')
    · have hb' := (edge_inside hg (sg ha) (sg hb) hab).2
      have hcb' : edge g c b := (Bool.or_eq_true_iff.mp hcb).resolve_left
        (fun h => hnot (edge_inside hf (sf hc) (sf hb) h).2 hb')
      have hc' := (edge_inside hg (sg hc) (sg hb) hcb').1
      have hcd' : edge g c d := (Bool.or_eq_true_iff.mp hcd).resolve_left
        (fun h => hnot (edge_inside hf (sf hc) (sf hd) h).1 hc')
      exact Or.inr (rg a b c d (sg ha) (sg hb) (sg hc) (sg hd) hab hcb' hcd')
  exact Bool.or_eq_true_iff.mpr hresult

theorem and_edge {s t : Finset α} {f g : (α → Bool) → Bool}
    (hdis : Disjoint s t) (hf : Local s f) (hg : Local t g)
    (zf : f (bits ∅) = false) (zg : g (bits ∅) = false) (a b : α) :
    edge (fun x => f x && g x) a b ↔
      (hits f a ∧ hits g b) ∨ (hits f b ∧ hits g a) := by
  have dis {i : α} (hs : i ∈ s) (ht : i ∈ t) : False := Finset.disjoint_left.mp hdis hs ht
  have lands {r : Finset α} {h : (α → Bool) → Bool} (hl : Local r h)
      (hz : h (bits ∅) = false) {i j : α} (hij : edge h i j) : i ∈ r ∨ j ∈ r := by
    by_contra hn
    change h (bits {i, j}) = true at hij
    rw [pair_without hl (fun hi => hn (Or.inl hi)),
      single_without hl (fun hj => hn (Or.inr hj)), hz] at hij
    contradiction
  have align {i j : α} (hi : i ∈ s) (hj : j ∈ t) :
      (edge f i j ∧ edge g i j) ↔ hits f i ∧ hits g j := by
    have e₁ : f (bits {i, j}) = f (bits {i}) := by
      rw [Finset.pair_comm i j, pair_without hf (fun hs => dis hs hj)]
    have e₂ : g (bits {i, j}) = g (bits {j}) := pair_without hg (fun ht => dis hi ht)
    unfold edge hits
    rw [e₁, e₂]
  change (f (bits {a, b}) && g (bits {a, b})) = true ↔ _
  rw [Bool.and_eq_true]
  constructor
  · intro h
    rcases lands hf zf h.1 with ha | hb
    · have hb' := (lands hg zg h.2).resolve_left (fun ha' => dis ha ha')
      exact Or.inl ((align ha hb').mp h)
    · have ha' := (lands hg zg h.2).resolve_right (fun hb' => dis hb hb')
      exact Or.inr ((align hb ha').mp ⟨edge_comm.mp h.1, edge_comm.mp h.2⟩)
  · rintro (h | h)
    · exact (align (hit_in hf zf h.1) (hit_in hg zg h.2)).mpr h
    · have hh := (align (hit_in hf zf h.1) (hit_in hg zg h.2)).mpr h
      exact ⟨edge_comm.mp hh.1, edge_comm.mp hh.2⟩

theorem and_rectangles {s t : Finset α} {f g : (α → Bool) → Bool}
    (hdis : Disjoint s t) (hf : Local s f) (hg : Local t g)
    (zf : f (bits ∅) = false) (zg : g (bits ∅) = false) :
    Rectangles (fun x => f x && g x) := by
  intro a b c d _ _ _ _ hab hcb hcd
  have ha (i j : α) := and_edge hdis hf hg zf zg i j
  have hn {i : α} (h₁ : hits f i) (h₂ : hits g i) : False :=
    Finset.disjoint_left.mp hdis (hit_in hf zf h₁) (hit_in hg zg h₂)
  apply (ha a d).mpr
  rcases (ha a b).mp hab with hab | hab
  · have hcb := ((ha c b).mp hcb).resolve_right (fun h => hn h.1 hab.2)
    have hcd := ((ha c d).mp hcd).resolve_right (fun h => hn hcb.1 h.2)
    exact Or.inl ⟨hab.1, hcd.2⟩
  · have hcb := ((ha c b).mp hcb).resolve_left (fun h => hn hab.1 h.2)
    have hcd := ((ha c d).mp hcd).resolve_left (fun h => hn h.1 hcb.2)
    exact Or.inr ⟨hcd.1, hab.2⟩

def connect (isAnd : Bool) (f g : (α → Bool) → Bool) (x : α → Bool) : Bool :=
  if isAnd then f x && g x else f x || g x

theorem combined_spec {s t : Finset α} {f g : (α → Bool) → Bool}
    (isAnd : Bool) (hdis : Disjoint s t) (hf : Spec s f) (hg : Spec t g) :
    Spec (s ∪ t) (connect isAnd f g) := by
  rcases hf with ⟨⟨a, ha⟩, lf, zf, onesF, rf⟩
  rcases hg with ⟨_, lg, zg, onesG, rg⟩
  refine ⟨⟨a, Finset.mem_union_left _ ha⟩, ?_, ?_, ?_, ?_⟩
  · intro x y h
    simp only [connect, lf x y (fun i hi => h i (Finset.mem_union_left _ hi)),
      lg x y (fun i hi => h i (Finset.mem_union_right _ hi))]
  · cases isAnd <;> simp [connect, zf, zg]
  · cases isAnd <;> simp [connect, onesF, onesG]
  · cases isAnd with
    | false => exact or_rectangles hdis lf lg rf rg
    | true => exact and_rectangles hdis lf lg zf zg

theorem foldl_snoc_keeps {α β : Type _} (F : List α → β → α) (gs : List β) (init : List α) :
    init <+: gs.foldl (fun R g => R ++ [F R g]) init := by
  induction gs generalizing init with
  | nil => exact List.prefix_refl _
  | cons g gs ih => exact (List.prefix_append init [F init g]).trans (ih _)

theorem foldl_snoc_length {α β : Type _} (F : List α → β → α) (gs : List β) (init : List α) :
    (gs.foldl (fun R g => R ++ [F R g]) init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih => simp [ih]; omega

theorem getD_of_initial {α : Type _} {P L : List α} (h : P <+: L) {i : ℕ} (hi : i < P.length)
    (d : α) : L.getD i d = P.getD i d := by
  obtain ⟨t, rfl⟩ := h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem foldl_snoc_split {α β : Type _} (F : List α → β → α) (gs : List β) (init : List α)
    (j : ℕ) (hj : j < gs.length) (d : α) :
    (gs.foldl (fun R g => R ++ [F R g]) init).getD (init.length + j) d
      = F ((gs.take j).foldl (fun R g => R ++ [F R g]) init) gs[j] ∧
    ((gs.take j).foldl (fun R g => R ++ [F R g]) init) <+:
      gs.foldl (fun R g => R ++ [F R g]) init ∧
    ((gs.take j).foldl (fun R g => R ++ [F R g]) init).length = init.length + j := by
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by simp
  set P := (gs.take j).foldl (fun R g => R ++ [F R g]) init with hP
  have hPl : P.length = init.length + j := by
    rw [hP, foldl_snoc_length F]; simp; omega
  have hpre : (P ++ [F P gs[j]]) <+: gs.foldl (fun R g => R ++ [F R g]) init := by
    conv_rhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
    exact foldl_snoc_keeps F _ _
  refine ⟨?_, (List.prefix_append P _).trans hpre, hPl⟩
  rw [getD_of_initial hpre (by simp; omega), ← hPl]
  simp

def readGate (w : List Bool) (g : Gate) := g.op.eval (g.inputs.map fun i => w.getD i false)

theorem wireAt (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false = C.gates[j].op.eval
      (C.gates[j].inputs.map fun i => if i < x.length + j then (C.wires x).getD i false else false) := by
  obtain ⟨value,pre,len⟩ := foldl_snoc_split readGate C.gates x j hj false
  rw [show (C.wires x).getD (x.length + j) false = _ from value]
  unfold readGate
  congr 1
  apply List.map_congr_left
  intro i _
  split
  · exact (getD_of_initial pre (by omega) false).symm
  · apply List.getD_eq_default
    unfold readGate at len
    omega

def wire (N : ℕ) (C : Circuit) (i : ℕ) (x : Fin N → Bool) : Bool :=
  (C.wires (List.ofFn x)).getD i false

theorem wire_input (N : ℕ) (C : Circuit) (i : ℕ) (hi : i < N) :
    wire N C i = fun x => x ⟨i, hi⟩ := by
  funext x
  have hl : i < (List.ofFn x).length := by simpa using hi
  have hp : List.ofFn x <+: C.wires (List.ofFn x) := foldl_snoc_keeps readGate C.gates _
  rw [wire, getD_of_initial hp hl false, List.getD_eq_getElem _ _ hl]
  exact List.getElem_ofFn hl

theorem wire_gate {N : ℕ} (C : Circuit) (hback : ReadsBack N C) (j a b : ℕ)
    (hj : j < C.gates.length) (hins : (gateAt C j).inputs = [a, b])
    (hop : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) :
    ∃ isAnd, wire N C (N + j) = connect isAnd (wire N C a) (wire N C b) := by
  have ha := hback j hj a (by simp [hins])
  have hb := hback j hj b (by simp [hins])
  have hat : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  have ev (x : Fin N → Bool) :
      wire N C (N + j) x =
        (gateAt C j).op.eval [wire N C a x, wire N C b x] := by
    have he := wireAt C (List.ofFn x) j hj
    rw [List.length_ofFn, ← hat, hins] at he
    simpa only [wire, List.map_cons, List.map_nil, ite_eq_left ha, ite_eq_left hb] using he
  rcases hop with h | h
  · refine ⟨true, funext fun x => ?_⟩
    rw [ev, h]
    simp [GateOp.eval, connect]
  · refine ⟨false, funext fun x => ?_⟩
    rw [ev, h]
    simp [GateOp.eval, connect]

theorem variable_spec (i : α) : Spec {i} (fun x => x i) := by
  refine ⟨⟨i, by simp⟩, fun x y h => h i (by simp), by simp [bits], rfl, ?_⟩
  intro a b c d ha hb _ _ hab _ _
  simp [bits, edge] at ha hb hab
  tauto

theorem read_mono (C : Circuit) {p q : ℕ} (hpq : p ≤ q) (i : ℕ) :
    readsIn C (Finset.range p) i ≤ readsIn C (Finset.range q) i := by
  unfold readsIn
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hpq) (fun _ _ _ => Nat.zero_le _)

def Live (N : ℕ) (C : Circuit) (k i : ℕ) : Prop :=
  i < N + k ∧ readsIn C (Finset.range k) i = 0

theorem label_invariant (N : ℕ) (C : Circuit)
    (hgate : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hback : ReadsBack N C)
    (hbound : ∀ i < N + C.gates.length, readsIn C (Finset.range C.gates.length) i ≤ 1) :
    ∀ k ≤ C.gates.length, ∃ label : ℕ → Finset (Fin N),
      (∀ i, Live N C k i → Spec (label i) (wire N C i)) ∧
      (∀ i j, Live N C k i → Live N C k j → i ≠ j → Disjoint (label i) (label j)) := by
  intro k
  induction k with
  | zero =>
    intro _
    let label (i : ℕ) : Finset (Fin N) := if h : i < N then {⟨i, h⟩} else ∅
    have singleton (i : ℕ) (hi : Live N C 0 i) :
        label i = {⟨i, by simpa using hi.1⟩} := by
      have h : i < N := by simpa using hi.1
      simp [label, h]
    refine ⟨label, ?_, ?_⟩
    · intro i hi
      have hi' : i < N := by simpa using hi.1
      rw [singleton i hi, wire_input N C i hi']
      exact variable_spec _
    · intro i j hi hj hij
      rw [singleton i hi, singleton j hj]
      apply Finset.disjoint_left.mpr
      intro a ha hb
      exact hij (congrArg Fin.val ((Finset.mem_singleton.mp ha).symm.trans (Finset.mem_singleton.mp hb)))
  | succ k ih =>
    intro hk
    obtain ⟨label, hlabel, hd⟩ := ih (by omega)
    have hg : k < C.gates.length := by omega
    have hat : gateAt C k = C.gates[k] := List.getD_eq_getElem _ _ hg
    have good := hgate (gateAt C k) (by rw [hat]; exact List.getElem_mem _)
    obtain ⟨a, b, hin⟩ := List.length_eq_two.mp good.2
    have count_step (i : ℕ) : readsIn C (Finset.range (k + 1)) i =
        readsIn C (Finset.range k) i + ([a, b] : List ℕ).count i := by
      rw [readsIn, Finset.sum_range_succ]
      change readsIn C (Finset.range k) i + (gateAt C k).inputs.count i = _
      rw [hin]
    have aEarlier := hback k hg a (by simp [hin])
    have bEarlier := hback k hg b (by simp [hin])
    have readBound (i : ℕ) (hi : i < N + k) :
        readsIn C (Finset.range (k + 1)) i ≤ 1 :=
      (read_mono C hk i).trans (hbound i (by omega))
    have ac := readBound a aEarlier
    have bc := readBound b bEarlier
    rw [count_step] at ac bc
    have ap : 0 < ([a, b] : List ℕ).count a := List.count_pos_iff.mpr (by simp)
    have bp : 0 < ([a, b] : List ℕ).count b := List.count_pos_iff.mpr (by simp)
    have ha : Live N C k a := ⟨aEarlier, by omega⟩
    have hb : Live N C k b := ⟨bEarlier, by omega⟩
    have hab : a ≠ b := by
      intro h
      subst b
      simp at ac
    have hdis := hd a b ha hb hab
    obtain ⟨isAnd, hwire⟩ := wire_gate C hback k a b hg hin good.1
    have vertex (i : ℕ) (hi : Live N C (k + 1) i) :
        i ≠ a ∧ i ≠ b := by
      have hcount := hi.2
      rw [count_step] at hcount
      constructor
      · intro h; subst i; omega
      · intro h; subst i; omega
    have earlier (i : ℕ) (hi : Live N C (k + 1) i) (he : i ≠ N + k) :
        Live N C k i := by
      obtain ⟨hl, hr⟩ := hi
      rw [count_step] at hr
      exact ⟨by omega, by omega⟩
    let next (i : ℕ) := if i = N + k then label a ∪ label b else label i
    have root : Spec (label a ∪ label b) (wire N C (N + k)) := by
      rw [hwire]
      exact combined_spec isAnd hdis (hlabel a ha) (hlabel b hb)
    refine ⟨next, ?_, ?_⟩
    · intro i hi
      by_cases he : i = N + k
      · subst i
        simpa [next] using root
      · simpa [next, he] using hlabel i (earlier i hi he)
    · intro i j hi hj hij
      have join_disjoint (p : ℕ) (hp : Live N C (k + 1) p) (he : p ≠ N + k) :
          Disjoint (label a ∪ label b) (label p) :=
        Finset.disjoint_union_left.mpr
          ⟨hd a p ha (earlier p hp he) (vertex p hp).1.symm,
            hd b p hb (earlier p hp he) (vertex p hp).2.symm⟩
      by_cases hi' : i = N + k
      · subst i
        simpa [next, hij.symm] using join_disjoint j hj hij.symm
      · by_cases hj' : j = N + k
        · subst j
          simpa [next, hi'] using (join_disjoint i hi hi').symm
        · simpa [next, hi', hj'] using hd i j (earlier i hi hi') (earlier j hj hj') hij

def row {n m : ℕ} (u : Fin n) : Fin (n + m) := ⟨u.val, by have := u.isLt; omega⟩

def col {n m : ℕ} (v : Fin m) : Fin (n + m) := ⟨n + v.val, by have := v.isLt; omega⟩

theorem oneEach_bits {n m : ℕ} (u : Fin n) (v : Fin m) :
    oneEach u v = List.ofFn (bits {row u, col v}) := by
  apply List.ext_getElem (by simp [oneEach])
  intro i hi hj
  rw [← List.getD_eq_getElem _ false hi, ← List.getD_eq_getElem _ false hj, each_value]
  have hlt : i < n + m := by simpa using hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [hlt, bits, row, col, Fin.ext_iff]

theorem wire_mono {N : ℕ} (C : Circuit) (hC : Monotone2 C) (i : ℕ)
    {S T : Finset (Fin N)} (hs : S ⊆ T) :
    wire N C i (bits S) = true → wire N C i (bits T) = true := by
  apply fold_monotone C.gates (fun g hg => (hC g hg).1) (by simp) _ i
  intro j hj
  by_cases h : j < N
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos h,
      Option.getD_some, bits, decide_eq_true_eq] at hj ⊢
    exact hs hj
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_neg h,
      Option.getD_none, Bool.false_eq_true] at hj


theorem support_all {n m : ℕ} {A : Fin n → Fin m → Bool}
    (hrow : ∀ a : Fin n, ∃ b : Fin n, b ≠ a ∧ ∃ v : Fin m, A a v = true ∧ A b v = false)
    (hcol : ∀ v : Fin m, ∃ w : Fin m, w ≠ v ∧ ∃ a : Fin n, A a v = true ∧ A a w = false)
    (C : Circuit) (hC : Monotone2 C) (hG : Represents A C)
    {L : Finset ℕ} {r : ℕ} (hL : closed (n + m) C L) (hr : r ∈ L)
    (hout : C.output = n + m + r) :
    Finset.range (n + m) ⊆ used (n + m) C L := by
  intro i hi
  have hil := Finset.mem_range.mp hi
  by_cases hin : i < n
  · let a : Fin n := ⟨i, hin⟩
    obtain ⟨b, _, v, ht, hf⟩ := hrow a
    refine needed hC hL hr hout (x := oneEach a v) (y := oneEach b v)
      (by simp [oneEach]) (by simp [oneEach]) i ?_ ((hG a v).trans ht) ((hG b v).trans hf)
    intro w hw
    rw [setD] at hw
    by_cases e : w = i
    · simp [e] at hw
    · simp only [ite_eq_right e, each_value, decide_eq_true_eq] at hw
      rw [each_value, decide_eq_true_eq]
      rcases hw with hw | hw
      · exact (e hw).elim
      · exact Or.inr hw
  · let v : Fin m := ⟨i - n, by omega⟩
    have ev : n + v.val = i := by dsimp [v]; omega
    obtain ⟨w, _, a, ht, hf⟩ := hcol v
    refine needed hC hL hr hout (x := oneEach a v) (y := oneEach a w)
      (by simp [oneEach]) (by simp [oneEach]) i ?_ ((hG a v).trans ht) ((hG a w).trans hf)
    intro j hj
    rw [setD] at hj
    by_cases e : j = i
    · simp [e] at hj
    · simp only [ite_eq_right e, each_value, decide_eq_true_eq, ev] at hj
      rw [each_value, decide_eq_true_eq]
      rcases hj with hj | hj
      · exact Or.inl hj
      · exact (e hj).elim

theorem root_bounds {n m : ℕ} {A : Fin n → Fin m → Bool}
    (hn : 2 ≤ n)
    (hrow : ∀ a : Fin n, ∃ b : Fin n, b ≠ a ∧ ∃ v : Fin m, A a v = true ∧ A b v = false)
    (hcol : ∀ v : Fin m, ∃ w : Fin m, w ≠ v ∧ ∃ a : Fin n, A a v = true ∧ A a w = false)
    (C : Circuit) (hG : Represents A C) :
    n + m ≤ C.output ∧ C.output < n + m + C.gates.length := by
  have raw (u : Fin n) (v : Fin m) (hi : C.output < n + m) :
      C.eval (oneEach u v) = (oneEach u v).getD C.output false := by
    exact pre _ _ _ (by simpa [oneEach] using hi)
  constructor
  · by_contra! h
    by_cases hin : C.output < n
    · let a : Fin n := ⟨C.output, hin⟩
      obtain ⟨b, hne, _, _⟩ := hrow a
      obtain ⟨_, _, v, ht, _⟩ := hrow b
      have he := (hG b v).trans ht
      rw [raw _ _ h, each_value, decide_eq_true_eq] at he
      rcases he with he | he
      · exact hne (Fin.ext he.symm)
      · omega
    · let v : Fin m := ⟨C.output - n, by omega⟩
      have ev : n + v.val = C.output := by dsimp [v]; omega
      obtain ⟨w, hne, _, _⟩ := hcol v
      obtain ⟨_, _, a, ht, _⟩ := hcol w
      have he := (hG a w).trans ht
      rw [raw _ _ h, each_value, decide_eq_true_eq] at he
      rcases he with he | he
      · have := a.isLt; omega
      · exact hne (Fin.ext (by omega))
  · by_contra! h
    let a : Fin n := ⟨0, by omega⟩
    obtain ⟨_, _, v, ht, _⟩ := hrow a
    have he := (hG a v).trans ht
    change (C.gates.foldl step (oneEach a v)).getD C.output false = true at he
    rw [getD_ge _ _ (by rw [len]; simpa [oneEach] using h)] at he
    contradiction

theorem assign {n m : ℕ} (A : Fin n → Fin m → Bool) (U : Fin n → Bool) (V : Fin m → Bool)
    (hu : ∀ u v, U u = true → A u v = true) (hv : ∀ u v, V v = true → A u v = true)
    (rect : ∀ a b c d, U a = false → V b = false → U c = false → V d = false →
      A a b = true → A c b = true → A c d = true → A a d = true) :
    ∃ (P : Fin n → ℕ) (K : Fin m → ℕ), ∀ (u : Fin n) (v : Fin m),
      A u v = true ↔ P u = 0 ∨ K v = 0 ∨ (2 ≤ P u ∧ P u = K v) := by
  classical
  let nbr (u : Fin n) : Finset (Fin m) := Finset.univ.filter fun v => V v = false ∧ A u v = true
  have mem (u : Fin n) (v : Fin m) : v ∈ nbr u ↔ V v = false ∧ A u v = true := by simp [nbr]
  have same (u a : Fin n) (v : Fin m) (hU : U u = false) (hA : U a = false)
      (h1 : v ∈ nbr u) (h2 : v ∈ nbr a) : nbr u = nbr a := by
    rw [mem] at h1 h2
    ext w
    rw [mem, mem]
    exact ⟨fun ⟨hw, he⟩ => ⟨hw, rect a v u w hA h2.1 hU hw h2.2 h1.2 he⟩,
      fun ⟨hw, he⟩ => ⟨hw, rect u v a w hU h1.1 hA hw h1.2 h2.2 he⟩⟩
  let code := Fintype.equivFin (Finset (Fin m))
  let enc (u : Fin n) : ℕ := 2 + (code (nbr u)).val
  let P (u : Fin n) : ℕ := if U u then 0 else enc u
  let K (v : Fin m) : ℕ := if V v then 0
    else if h : ∃ a, U a = false ∧ v ∈ nbr a then enc (Classical.choose h) else 1
  have henc (u : Fin n) : 2 ≤ enc u := by dsimp [enc]; omega
  refine ⟨P, K, ?_⟩
  intro u v
  cases eU : U u with
  | true => simp [P, eU, hu u v eU]
  | false =>
    cases eV : V v with
    | true => simp [K, eV, hv u v eV]
    | false =>
      have hpu : P u = enc u := by simp [P, eU]
      rw [hpu]
      by_cases he : ∃ a, U a = false ∧ v ∈ nbr a
      · let a := Classical.choose he
        obtain ⟨ha, hm⟩ : U a = false ∧ v ∈ nbr a := Classical.choose_spec he
        have hkv : K v = enc a := by simp [K, eV, he, a]
        rw [hkv]
        simp only [show enc u ≠ 0 by have := henc u; omega, show enc a ≠ 0 by have := henc a; omega,
          false_or, henc u, true_and]
        constructor
        · intro h
          have e := same u a v eU ha ((mem u v).2 ⟨eV, h⟩) hm
          simp [enc, e]
        · intro h
          have e : nbr u = nbr a := code.injective (Fin.ext (by dsimp [enc] at h; omega))
          exact ((mem u v).1 (e.symm ▸ hm)).2
      · have hkv : K v = 1 := by simp [K, eV, he]
        have ht : A u v ≠ true := fun h => he ⟨u, eU, (mem u v).2 ⟨eV, h⟩⟩
        have hne : enc u ≠ 0 ∧ enc u ≠ 1 := by have := henc u; omega
        simp [hkv, ht, hne.1, hne.2]

end PEqualNP.Outside.L_meta_25472_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.Outside.L_meta_25472_aux

theorem PEqualNP.Outside.L_meta_25472 : ∀ (n m : ℕ) (A : Fin n → Fin m → Bool), 2 ≤ n → 2 ≤ m → (∀ a : Fin n, ∃ b : Fin n, b ≠ a ∧ ∃ v : Fin m, A a v = true ∧ A b v = false) → (∀ v : Fin m, ∃ w : Fin m, w ≠ v ∧ ∃ a : Fin n, A a v = true ∧ A a w = false) → PEqualNP.Represents.RepSizeAtMost A (n + m - 1) → ∃ (P : Fin n → ℕ) (K : Fin m → ℕ), ∀ (u : Fin n) (v : Fin m), (A u v = true ↔ (P u = 0 ∨ K v = 0 ∨ (2 ≤ P u ∧ P u = K v))) := by
  intro n m A hn _ hrow hcol ⟨C, hC, hsize, hG⟩
  obtain ⟨hraw, hout⟩ := root_bounds hn hrow hcol C hG
  obtain ⟨hgate, hback, hread, hvalid, hunread⟩ := output_shape C hC hsize hraw hout
    (fun L r hL hr he => support_all hrow hcol C hC hG hL hr he)
  obtain ⟨label, hs, _⟩ := label_invariant (n + m) C hgate hback (fun i _ => hread i) _ le_rfl
  let F := wire (n + m) C C.output
  have rect := (hs C.output ⟨hvalid, hunread⟩).2.2.2.2
  have edge_eq (u : Fin n) (v : Fin m) : F (bits {row u, col v}) = A u v := by
    change C.eval (List.ofFn (bits {row u, col v})) = _
    rw [← oneEach_bits]
    exact hG u v
  let U (u : Fin n) := F (bits ({row u} : Finset (Fin (n + m))))
  let V (v : Fin m) := F (bits ({col v} : Finset (Fin (n + m))))
  apply assign A U V
  · intro u v hu
    rw [← edge_eq]
    exact wire_mono C hC C.output (Finset.singleton_subset_iff.mpr (by simp)) hu
  · intro u v hv
    rw [← edge_eq]
    exact wire_mono C hC C.output (Finset.singleton_subset_iff.mpr (by simp)) hv
  · intro a b c d ha hb hc hd hab hcb hcd
    have he (u : Fin n) (v : Fin m) : edge F (row u) (col v) ↔ A u v = true := by
      unfold edge
      rw [edge_eq]
    exact (he a d).1 (rect (row a) (col b) (row c) (col d) ha hb hc hd
      ((he a b).2 hab) ((he c b).2 hcb) ((he c d).2 hcd))
