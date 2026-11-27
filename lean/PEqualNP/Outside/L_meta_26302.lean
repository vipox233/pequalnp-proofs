import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_26302_aux
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
    C.gates.length = n + m - 1 ∧
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
  refine ⟨by omega, ?_, fun j hj => (local_size j hj).2.2, ?_, hout, ?_⟩
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

def comparable {ι κ : Type} (A : ι → κ → Bool) (a b : ι) : Prop :=
  (∀ j, A a j = true → A b j = true) ∨ (∀ j, A b j = true → A a j = true)

theorem incomparable_partner {ι κ : Type} [Fintype ι] (A : ι → κ → Bool)
    (hι : 3 ≤ Fintype.card ι)
    (sparse : ∀ i k l, k ≠ i → l ≠ i → comparable A i k → comparable A i l → k = l)
    (i : ι) : ∃ j, j ≠ i ∧ ¬ comparable A i j := by
  classical
  by_contra! h
  let S := (Finset.univ : Finset ι).erase i
  have hs : 1 < S.card := by
    dsimp [S]
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hs
  have hai := (Finset.mem_erase.mp ha).1
  have hbi := (Finset.mem_erase.mp hb).1
  exact hab (sparse i a b hai hbi (h a hai) (h b hbi))

theorem line_witness {ι κ : Type} [Fintype ι] (A : ι → κ → Bool)
    (hι : 3 ≤ Fintype.card ι)
    (sparse : ∀ i k l, k ≠ i → l ≠ i → comparable A i k → comparable A i l → k = l)
    (i : ι) : ∃ k, k ≠ i ∧ ∃ j, A i j = true ∧ A k j = false := by
  obtain ⟨k, hk, hic⟩ := incomparable_partner A hι sparse i
  refine ⟨k, hk, ?_⟩
  by_contra! h
  apply hic
  left
  intro j hj
  by_cases h' : A k j = true
  · exact h'
  · exact False.elim (h j hj (Bool.eq_false_iff.mpr h'))


theorem monotone_lower {n m : ℕ} (A : Fin n → Fin m → Bool)
    (hn : 3 ≤ n) (hm : 3 ≤ m)
    (sr : ∀ i k l, k ≠ i → l ≠ i → comparable A i k → comparable A i l → k = l)
    (sc : ∀ j k l, k ≠ j → l ≠ j → comparable (fun j i => A i j) j k →
      comparable (fun j i => A i j) j l → k = l)
    (C : Circuit) (mono : Monotone2 C) (repr : Represents A C)
    (small : C.size ≤ n + m - 1) : n + m - 1 ≤ C.size := by
  have hr := line_witness A (by simpa using hn) sr
  have hc := line_witness (fun j i => A i j) (by simpa using hm) sc
  obtain ⟨hraw, hout⟩ := root_bounds (by omega) hr hc C repr
  have eq := (output_shape C mono small hraw hout
      (fun L r hL hmem he => support_all hr hc C mono repr hL hmem he)).1
  exact le_of_eq eq.symm
end PEqualNP.Outside.L_meta_26302_aux

namespace PEqualNP.Outside.L_meta_26302_aux
namespace Network

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover

def trimGate (g : Gate) : Gate :=
  match g.op with
  | .not => ⟨.not, g.inputs.take 1⟩
  | _ => g

def trim (C : Circuit) : Circuit :=
  ⟨C.gates.map trimGate, C.output⟩

theorem trimGate_eval (g : Gate) (x : List Bool) :
    compute x (trimGate g) = compute x g := by
  cases g with
  | mk op inp =>
    cases op <;> try rfl
    cases inp <;> rfl

theorem trim_eval (C : Circuit) (x : List Bool) :
    (trim C).eval x = C.eval x := by
  have h (gs : List Gate) (v : List Bool) :
      (gs.map trimGate).foldl step v = gs.foldl step v := by
    induction gs generalizing v with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.map_cons, List.foldl_cons, ih, step, trimGate_eval]
  change ((C.gates.map trimGate).foldl step x).getD C.output false = _
  rw [h]
  rfl

theorem trim_fan (C : Circuit) (h : FanInTwo C) : FanInTwo (trim C) := by
  intro g hg
  change g ∈ C.gates.map trimGate at hg
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
  obtain ⟨ha', hs⟩ := h a ha
  rcases a with ⟨o, l⟩
  cases o <;> simp_all [trimGate]

theorem trim_unary (C : Circuit) :
    ∀ g ∈ (trim C).gates, g.op = GateOp.not → g.inputs.length ≤ 1 := by
  intro g hg he
  change g ∈ C.gates.map trimGate at hg
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hg
  rcases a with ⟨o, l⟩
  cases o <;> simp_all [trimGate]

def edgeTo (N : ℕ) (C : Circuit) (L : Finset ℕ) (w v : ℕ) : Prop :=
  ∃ j ∈ L, v = N + j ∧ before C N j w

abbrev reaches (N : ℕ) (C : Circuit) (L : Finset ℕ) :=
  Relation.ReflTransGen (edgeTo N C L)

theorem edgeIncreases {N : ℕ} {C : Circuit} {L : Finset ℕ} {w v : ℕ}
    (h : edgeTo N C L w v) : w < v := by
  obtain ⟨j, _, rfl, _, h⟩ := h
  exact h

theorem reachIncreases {N : ℕ} {C : Circuit} {L : Finset ℕ} {w v : ℕ}
    (h : reaches N C L w v) : w ≤ v := by
  induction h with
  | refl => exact le_rfl
  | tail _ e ih => exact ih.trans (Nat.le_of_lt (edgeIncreases e))

def value (N : ℕ) (C : Circuit) (x : ℕ → Bool) (override : ℕ → Option Bool)
    (w : ℕ) : Bool :=
  match override w with
  | some b => b
  | none =>
    if w < N then x w
    else if w - N < C.gates.length then
      let g := gateAt C (w - N)
      g.op.eval (g.inputs.map fun u => if h : u < w then value N C x override u else false)
    else false
termination_by w

def relay (f : ℕ) (b : Bool) (w : ℕ) : Option Bool :=
  if w = f then some b else none

theorem val_raw {N : ℕ} {C : Circuit} {x : ℕ → Bool} {O : ℕ → Option Bool}
    {w : ℕ} (hw : w < N) (ho : O w = none) :
    value N C x O w = x w := by
  rw [value, ho, if_pos hw]

theorem val_gate {N : ℕ} {C : Circuit} {x : ℕ → Bool} {O : ℕ → Option Bool}
    {j : ℕ} (hj : j < C.gates.length) (ho : O (N+j) = none) :
    value N C x O (N+j) =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun u =>
        if u < N+j then value N C x O u else false) := by
  rw [value, ho, if_neg (by omega : ¬ N+j < N)]
  simp only [Nat.add_sub_cancel_left, if_pos hj]
  rfl

theorem val_relay (N : ℕ) (C : Circuit) (x : ℕ → Bool) (f : ℕ) (b : Bool) :
    value N C x (relay f b) f = b := by
  rw [value]
  simp [relay]

theorem val_fold (N : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = N) (w : ℕ) :
    value N C (fun i => x.getD i false) (fun _ => none) w =
      (C.gates.foldl step x).getD w false := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w < N
    · rw [val_raw hw rfl, pre _ _ _ (by omega)]
    · by_cases hreal : w - N < C.gates.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = N + j := ⟨w-N, by omega⟩
        have hj : j < C.gates.length := by omega
        rw [val_gate hj rfl, gate_formula C x hx hj]
        congr 1
        apply List.map_congr_left
        intro u _
        split_ifs with h
        · exact ih u h
        · rfl
      · rw [value, if_neg hw, if_neg hreal, getD_ge]
        rw [len, hx]
        omega

theorem val_original (N : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = N) :
    value N C (fun i => x.getD i false) (fun _ => none) C.output = C.eval x :=
  val_fold N C x hx C.output

end Network
end PEqualNP.Outside.L_meta_26302_aux

namespace PEqualNP.Outside.L_meta_26302_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover
open scoped BigOperators

def rawUsed (N : ℕ) (C : Circuit) (L : Finset ℕ) : Finset ℕ :=
  (used N C L).filter (· < N)

def missingRows (n m : ℕ) (C : Circuit) (L : Finset ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun u => u.val ∉ used (n+m) C L

def missingCols (n m : ℕ) (C : Circuit) (L : Finset ℕ) : Finset (Fin m) :=
  Finset.univ.filter fun v => n + v.val ∉ used (n+m) C L

noncomputable def activeNot (C : Circuit) (L : Finset ℕ) : Finset ℕ := by
  classical
  exact L.filter fun j => (gateAt C j).op = .not

theorem closed_eval_eq {N : ℕ} {C : Circuit} {L : Finset ℕ} {r : ℕ}
    (hL : closed N C L) (hr : r ∈ L) (ho : C.output = N+r)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (he : ∀ i ∈ used N C L, x.getD i false = y.getD i false) : C.eval x = C.eval y := by
  change (C.gates.foldl step x).getD C.output false = (C.gates.foldl step y).getD C.output false
  rw [ho]
  exact closed_values hL x y hx hy he r hr

theorem missing_rows_le {n m : ℕ} {A : Fin n → Fin m → Bool} {C : Circuit} {L : Finset ℕ} {r : ℕ}
    (hi : Function.Injective A) (hA : Represents A C) (hL : closed (n+m) C L)
    (hr : r ∈ L) (ho : C.output = n+m+r) : (missingRows n m C L).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro u hu v hv
  have hui := (Finset.mem_filter.mp hu).2
  have hvi := (Finset.mem_filter.mp hv).2
  apply hi
  funext j
  rw [← hA u j, ← hA v j]
  apply closed_eval_eq hL hr ho _ _ (by simp [oneEach]) (by simp [oneEach])
  intro w hw
  rw [each_value, each_value]
  have hu' : w ≠ u.val := fun h => hui (h ▸ hw)
  have hv' : w ≠ v.val := fun h => hvi (h ▸ hw)
  simp [hu',hv']

theorem missing_cols_le {n m : ℕ} {A : Fin n → Fin m → Bool} {C : Circuit} {L : Finset ℕ} {r : ℕ}
    (hi : Function.Injective (fun j i => A i j)) (hA : Represents A C) (hL : closed (n+m) C L)
    (hr : r ∈ L) (ho : C.output = n+m+r) : (missingCols n m C L).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro u hu v hv
  have hui := (Finset.mem_filter.mp hu).2
  have hvi := (Finset.mem_filter.mp hv).2
  apply hi
  funext i
  change A i u = A i v
  rw [← hA i u, ← hA i v]
  apply closed_eval_eq hL hr ho _ _ (by simp [oneEach]) (by simp [oneEach])
  intro w hw
  rw [each_value, each_value]
  have hu' : w ≠ n+u.val := fun h => hui (h ▸ hw)
  have hv' : w ≠ n+v.val := fun h => hvi (h ▸ hw)
  simp [hu',hv']

theorem input_partition (n m : ℕ) (C : Circuit) (L : Finset ℕ) :
    (rawUsed (n+m) C L).card + (missingRows n m C L).card + (missingCols n m C L).card = n+m := by
  let R := rawUsed (n+m) C L
  let A := (missingRows n m C L).image Fin.val
  let B := (missingCols n m C L).image (fun f => n+f.val)
  have hA (w : ℕ) : w ∈ A ↔ w < n ∧ w ∉ used (n+m) C L := by
    constructor
    · intro h
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp h
      exact ⟨u.isLt, (Finset.mem_filter.mp hu).2⟩
    · rintro ⟨h,hn⟩
      exact Finset.mem_image.mpr ⟨⟨w,h⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩,rfl⟩
  have hB (w : ℕ) : w ∈ B ↔ n ≤ w ∧ w < n+m ∧ w ∉ used (n+m) C L := by
    constructor
    · intro h
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp h
      exact ⟨by omega, by have := v.isLt; omega, (Finset.mem_filter.mp hv).2⟩
    · rintro ⟨h,hm,hn⟩
      let v : Fin m := ⟨w - n, by omega⟩
      have he : n + v.val = w := by dsimp [v]; omega
      exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [he]⟩,he⟩
  have hR (w : ℕ) : w ∈ R ↔ w ∈ used (n+m) C L ∧ w < n+m := Finset.mem_filter
  have hRA : Disjoint R A := Finset.disjoint_left.mpr fun w h1 h2 => ((hA w).1 h2).2 ((hR w).1 h1).1
  have hAB : Disjoint (R ∪ A) B := by
    apply Finset.disjoint_left.mpr
    intro w h1 h2
    rcases Finset.mem_union.mp h1 with h1 | h1
    · exact ((hB w).1 h2).2.2 ((hR w).1 h1).1
    · have := ((hA w).1 h1).1
      have := ((hB w).1 h2).1
      omega
  have hp : R ∪ A ∪ B = Finset.range (n+m) := by
    ext w
    simp only [Finset.mem_union, Finset.mem_range, hR, hA, hB]
    by_cases h : w ∈ used (n+m) C L
    · simp [h]
    · simp [h]; omega
  have hcA : A.card = (missingRows n m C L).card := Finset.card_image_of_injective _ Fin.val_injective
  have hcB : B.card = (missingCols n m C L).card :=
    Finset.card_image_of_injective _ (fun a b h => Fin.ext (by omega))
  rw [← hcA, ← hcB, ← Finset.card_union_of_disjoint hRA, ← Finset.card_union_of_disjoint hAB, hp, Finset.card_range]

theorem slots_count_low {N : ℕ} {C : Circuit} {L : Finset ℕ} {r : ℕ}
    (hr : r ∈ L) (huse : ∀ i ∈ L, i ≠ r → ∃ j ∈ L, before C N j (N+i)) :
    (rawUsed N C L).card + (L.card-1) ≤ (used N C L).card := by
  let I := (L.erase r).image (N + ·)
  have hdis : Disjoint (rawUsed N C L) I := by
    apply Finset.disjoint_left.mpr
    intro w hw hw'
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hw'
    have := (Finset.mem_filter.mp hw).2
    omega
  have hsub : rawUsed N C L ∪ I ⊆ used N C L := by
    intro w hw
    rcases Finset.mem_union.mp hw with h | h
    · exact (Finset.mem_filter.mp h).1
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp h
      obtain ⟨hn,hm⟩ := Finset.mem_erase.mp hi
      exact mem_used.mpr (huse i hm hn)
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis, Finset.card_image_of_injective _ (fun a b h => by omega),
    Finset.card_erase_of_mem hr] at hc
  exact hc

theorem slots_count_high {N : ℕ} {C : Circuit} {L : Finset ℕ} (hL : closed N C L)
    (hC : FanInTwo C) (hNot : ∀ g ∈ C.gates, g.op = .not → g.inputs.length ≤ 1) :
    (slots N C L).card + (activeNot C L).card ≤ 2*L.card := by
  classical
  have hmem (j : ℕ) (hj : j ∈ L) : gateAt C j ∈ C.gates := by
    have hb := hL.1 j hj
    rw [gateAt, List.getD_eq_getElem _ _ hb]
    exact List.getElem_mem _
  have hw (j : ℕ) : (inputSlots N C j).card ≤ (gateAt C j).inputs.length := by
    unfold inputSlots
    exact Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans (List.toFinset_card_le _))
  have hpoint (j : ℕ) (hj : j ∈ L) :
      (inputSlots N C j).card + (if (gateAt C j).op = .not then 1 else 0) ≤ 2 := by
    have hm := hmem j hj
    by_cases h : (gateAt C j).op = .not
    · have k := (hw j).trans (hNot _ hm h)
      simp [h]
      omega
    · simpa [h] using (hw j).trans (hC _ hm).2
  have hslots := Finset.card_biUnion_le (s := L) (t := inputSlots N C)
  have hn : (activeNot C L).card = ∑ j ∈ L, if (gateAt C j).op = .not then 1 else 0 := by
    unfold activeNot
    rw [Finset.card_filter]
  change (slots N C L).card ≤ ∑ j ∈ L, (inputSlots N C j).card at hslots
  have hsum : (∑ j ∈ L, ((inputSlots N C j).card + (if (gateAt C j).op = .not then 1 else 0))) ≤
      ∑ _j ∈ L, (2 : ℕ) := Finset.sum_le_sum hpoint
  rw [Finset.sum_add_distrib, ← hn] at hsum
  calc
    _ ≤ (∑ j ∈ L, (inputSlots N C j).card) + (activeNot C L).card := Nat.add_le_add_right hslots _
    _ ≤ ∑ _j ∈ L, (2 : ℕ) := hsum
    _ = _ := by simp [Nat.mul_comm]

theorem unique_reader_of_inj {N : ℕ} {C : Circuit} {L : Finset ℕ}
    (hinj : Set.InjOn Prod.snd (slots N C L : Set (ℕ × ℕ)))
    {j k w : ℕ} (hj : j ∈ L) (hk : k ∈ L) (he : before C N j w) (hf : before C N k w) : j = k := by
  exact congrArg Prod.fst (hinj (mem_slot.mpr ⟨hj,he⟩) (mem_slot.mpr ⟨hk,hf⟩) rfl)

theorem no_not_if_full {n m : ℕ} {C : Circuit} {L : Finset ℕ} {r : ℕ}
    (hr : r ∈ L) (hL : closed (n+m) C L)
    (huse : ∀ i ∈ L, i ≠ r → ∃ j ∈ L, before C (n+m) j (n+m+i))
    (hC : FanInTwo C) (hNot : ∀ g ∈ C.gates, g.op = .not → g.inputs.length ≤ 1)
    (hsmall : C.size ≤ n+m-1) (hrows : (missingRows n m C L).card = 0)
    (hcols : (missingCols n m C L).card = 0) :
    (activeNot C L).card = 0 ∧ L.card = C.size ∧ C.size = n+m-1 := by
  have hn := input_partition n m C L
  have hl := slots_count_low hr huse
  have hh := slots_count_high hL hC hNot
  have hm := Finset.card_image_le (s := slots (n+m) C L) (f := Prod.snd)
  change (used (n+m) C L).card ≤ (slots (n+m) C L).card at hm
  have hLf : L ⊆ Finset.range C.size := fun _ hj => Finset.mem_range.mpr (hL.1 _ hj)
  have hLc : L.card ≤ C.size := by simpa using Finset.card_le_card hLf
  have hpos := Finset.card_pos.mpr ⟨r,hr⟩
  omega

theorem collision_counts {n m : ℕ} {C : Circuit} {L : Finset ℕ} {r : ℕ}
    (hr : r ∈ L) (hL : closed (n+m) C L)
    (huse : ∀ i ∈ L, i ≠ r → ∃ j ∈ L, before C (n+m) j (n+m+i))
    (hC : FanInTwo C) (hNot : ∀ g ∈ C.gates, g.op = .not → g.inputs.length ≤ 1)
    (hsmall : C.size ≤ n+m-1)
    (hrows : (missingRows n m C L).card ≤ 1) (hcols : (missingCols n m C L).card ≤ 1)
    (hnpos : 0 < (activeNot C L).card)
    (hcollision : ¬ Set.InjOn Prod.snd (slots (n+m) C L : Set (ℕ × ℕ))) :
    (missingRows n m C L).card = 1 ∧ (missingCols n m C L).card = 1 ∧
    (activeNot C L).card = 1 ∧ L.card = C.size ∧ C.size = n+m-1 ∧
    (slots (n+m) C L).card = (used (n+m) C L).card+1 := by
  have hn := input_partition n m C L
  have hl := slots_count_low hr huse
  have hh := slots_count_high hL hC hNot
  have hm := Finset.card_image_le (s := slots (n+m) C L) (f := Prod.snd)
  change (used (n+m) C L).card ≤ (slots (n+m) C L).card at hm
  have hne : (used (n+m) C L).card ≠ (slots (n+m) C L).card := fun e =>
    hcollision (Finset.injOn_of_card_image_eq e)
  have hLf : L ⊆ Finset.range C.size := fun _ hj => Finset.mem_range.mpr (hL.1 _ hj)
  have hLc : L.card ≤ C.size := by simpa using Finset.card_le_card hLf
  have hpos := Finset.card_pos.mpr ⟨r,hr⟩
  omega

theorem collision_exists {N : ℕ} {C : Circuit} {L : Finset ℕ}
    (h : ¬ Set.InjOn Prod.snd (slots N C L : Set (ℕ × ℕ))) :
    ∃ j k w : ℕ, j ∈ L ∧ k ∈ L ∧ j ≠ k ∧ before C N j w ∧ before C N k w := by
  classical
  unfold Set.InjOn at h
  push Not at h
  obtain ⟨⟨j,v⟩, hj, ⟨k,w⟩, hk, e, hn⟩ := h
  change v = w at e
  subst v
  exact ⟨j,k,w,(mem_slot.mp hj).1,(mem_slot.mp hk).1,
    fun h => hn (Prod.ext h rfl),(mem_slot.mp hj).2,(mem_slot.mp hk).2⟩

end PEqualNP.Outside.L_meta_26302_aux

namespace PEqualNP.Outside.L_meta_26302_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover

def clearNotGate (g : Gate) : Gate :=
  match g.op with
  | .not => ⟨.or, []⟩
  | _ => g

def clearNots (C : Circuit) : Circuit := ⟨C.gates.map clearNotGate, C.output⟩

theorem clearNot_eq (g : Gate) (h : g.op ≠ .not) : clearNotGate g = g := by
  unfold clearNotGate
  split <;> simp_all

theorem clearNots_size (C : Circuit) : (clearNots C).size = C.size := by
  simp [clearNots, Circuit.size]

theorem clearNots_monotone (C : Circuit) (hC : FanInTwo C) : Monotone2 (clearNots C) := by
  intro g hg
  change g ∈ C.gates.map clearNotGate at hg
  obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hg
  have ⟨hop,hsize⟩ := hC h hh
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with hop | hop | hop
  · have hnot : h.op ≠ .not := by simp [hop]
    rw [clearNot_eq h hnot]
    exact ⟨by simp [hop],hsize⟩
  · have hnot : h.op ≠ .not := by simp [hop]
    rw [clearNot_eq h hnot]
    exact ⟨by simp [hop],hsize⟩
  · simp [clearNotGate,hop]

theorem clearNots_gateAt (C : Circuit) (j : ℕ) (h : j < C.gates.length) :
    gateAt (clearNots C) j = clearNotGate (gateAt C j) := by
  rw [gateAt,gateAt, List.getD_eq_getElem _ _ h]
  have h' : j < (clearNots C).gates.length := by simpa [clearNots] using h
  rw [List.getD_eq_getElem _ _ h']
  simp [clearNots]

theorem activeNot_mem {C : Circuit} {L : Finset ℕ} {j : ℕ} :
    j ∈ activeNot C L ↔ j ∈ L ∧ (gateAt C j).op = .not := by
  classical
  unfold activeNot
  exact Finset.mem_filter

theorem no_active_not_elim {C : Circuit} {L : Finset ℕ}
    (hno : (activeNot C L).card = 0) {j : ℕ} (hj : j ∈ L) : (gateAt C j).op ≠ .not := by
  intro he
  have hmem := Finset.card_pos.mpr ⟨j, activeNot_mem.mpr ⟨hj,he⟩⟩
  omega

theorem clearNots_wire {N : ℕ} {C : Circuit} {L : Finset ℕ} (hL : closed N C L)
    (hno : (activeNot C L).card = 0) (x : List Bool) (hx : x.length = N) :
    ∀ j ∈ L, ((clearNots C).gates.foldl step x).getD (N+j) false =
      (C.gates.foldl step x).getD (N+j) false := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj
    have hjC := hL.1 j hj
    have hjD : j < (clearNots C).gates.length := by simpa [clearNots] using hjC
    rw [gate_formula _ x hx hjD, gate_formula _ x hx hjC,
      clearNots_gateAt C j hjC, clearNot_eq _ (no_active_not_elim hno hj)]
    congr 1
    apply List.map_congr_left
    intro w hw
    split_ifs with hback
    · by_cases hraw : w < N
      · rw [pre _ _ _ (by omega : w < x.length), pre _ _ _ (by omega : w < x.length)]
      · let k := w - N
        have e : N + k = w := by dsimp [k]; omega
        have hk : k < j := by omega
        rw [← e] at hw hback ⊢
        exact ih k hk (hL.2 j hj k ⟨hw,hback⟩)
    · rfl

theorem clearNots_eval {N : ℕ} {C : Circuit} {L : Finset ℕ} {r : ℕ} (hL : closed N C L)
    (hr : r ∈ L) (hout : C.output = N+r) (hno : (activeNot C L).card = 0)
    (x : List Bool) (hx : x.length = N) : (clearNots C).eval x = C.eval x := by
  change ((clearNots C).gates.foldl step x).getD C.output false = (C.gates.foldl step x).getD C.output false
  rw [hout]
  exact clearNots_wire hL hno x hx r hr

theorem clearNots_represents {n m : ℕ} {A : Fin n → Fin m → Bool} {C : Circuit}
    {L : Finset ℕ} {r : ℕ} (hL : closed (n+m) C L) (hr : r ∈ L)
    (hout : C.output = n+m+r) (hno : (activeNot C L).card = 0)
    (hA : Represents A C) : Represents A (clearNots C) := by
  intro i j
  exact (clearNots_eval hL hr hout hno (oneEach i j) (by simp [oneEach])).trans (hA i j)

theorem noNotCircuit {n m : ℕ} {A : Fin n → Fin m → Bool} {C : Circuit}
    {L : Finset ℕ} {r : ℕ} (hC : FanInTwo C) (hL : closed (n+m) C L) (hr : r ∈ L)
    (hout : C.output = n+m+r) (hno : (activeNot C L).card = 0) (hA : Represents A C) :
    ∃ D : Circuit, Monotone2 D ∧ Represents A D ∧ D.size = C.size :=
  ⟨clearNots C, clearNots_monotone C hC, clearNots_represents hL hr hout hno hA, clearNots_size C⟩

end PEqualNP.Outside.L_meta_26302_aux

namespace PEqualNP.Outside.L_meta_26302_aux.Unate

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open Network

abbrev arc := edgeTo
abbrev Path := reaches

def Live (N : ℕ) (L : Finset ℕ) (w : ℕ) : Prop :=
  w < N ∨ ∃ j ∈ L, w = N + j

def Model (N : ℕ) (C : Circuit) (L : Finset ℕ) (skip : Option ℕ) (val : ℕ → Bool) : Prop :=
  ∀ j ∈ L, skip ≠ some (N + j) → val (N + j) =
    (gateAt C j).op.eval ((gateAt C j).inputs.map fun u => if u < N + j then val u else false)

def Changes (N i : ℕ) (skip : Option ℕ) (x y : ℕ → Bool) : Prop :=
  (∀ w < N, w ≠ i → x w = y w) ∧
    (∀ w, skip = some w → x w = y w) ∧
    (x i = true → y i = true)

def Sign (N : ℕ) (C : Circuit) (L : Finset ℕ) (skip : Option ℕ)
    (i w : ℕ) (positive : Bool) : Prop :=
  ∀ x y : ℕ → Bool, Model N C L skip x → Model N C L skip y → Changes N i skip x y →
    if positive then x w = true → y w = true else y w = true → x w = true

theorem eval_is_model {N : ℕ} {C : Circuit} {L : Finset ℕ}
    (hL : closed N C L) {x : List Bool} (hx : x.length = N) :
    Model N C L none (fun w => (C.gates.foldl step x).getD w false) := by
  intro j hj _
  exact gate_formula C x hx (hL.1 j hj)

theorem value_is_model {N : ℕ} {C : Circuit} {L : Finset ℕ}
    (hL : closed N C L) (x : ℕ → Bool) :
    Model N C L none (value N C x (fun _ => none)) := by
  intro j hj _
  exact val_gate (hL.1 j hj) rfl

theorem arc_lt {N : ℕ} {C : Circuit} {L : Finset ℕ} {x y : ℕ} :
    arc N C L x y → x < y := by
  rintro ⟨j, _, rfl, _, h⟩
  exact h

theorem path_mono {P : ℕ → ℕ → Prop} (hp : ∀ a b, P a b → a < b)
    {u v : ℕ} (h : Relation.ReflTransGen P u v) : u ≤ v := by
  induction h with
  | refl => exact le_rfl
  | tail _ he ih => exact ih.trans (hp _ _ he).le

theorem last_eq_deterministic {P : ℕ → ℕ → Prop} (hmono : ∀ a b, P a b → a < b)
    (unique : ∀ a b c, P a b → P a c → b = c)
    {s u v w : ℕ}
    (hu : Relation.ReflTransGen P s u) (hv : Relation.ReflTransGen P s v)
    (huw : P u w) (hvw : P v w) : u = v := by
  revert hv
  induction hu using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro hv
    rcases hv.cases_head with hv | ⟨a, ha, hv⟩
    · exact hv
    · have h := unique _ _ _ ha huw
      subst a
      have := path_mono hmono hv
      have := hmono _ _ hvw
      omega
  | @head s a ha _ ih =>
    intro hv
    rcases hv.cases_head with rfl | ⟨b, hb, hv⟩
    · have h := unique _ _ _ ha hvw
      subst a
      have := hmono _ _ huw
      have := path_mono hmono (show Relation.ReflTransGen P w u from ‹Relation.ReflTransGen P w u›)
      omega
    · have h := unique _ _ _ ha hb
      subst b
      exact ih hv

theorem last_eq {N : ℕ} {C : Circuit} {L : Finset ℕ} {s u v w : ℕ}
    (unique : ∀ a b c, Path N C L s a → arc N C L a b → arc N C L a c → b = c)
    (hu : Path N C L s u) (hv : Path N C L s v) (huw : arc N C L u w) (hvw : arc N C L v w) :
    u = v := by
  let P := fun a b => Path N C L s a ∧ arc N C L a b
  have establish {u} (h : Path N C L s u) : Relation.ReflTransGen P s u := by
    induction h with
    | refl => exact .refl
    | tail h hc ih => exact .tail ih ⟨h, hc⟩
  exact last_eq_deterministic (fun _ _ h => arc_lt h.2)
    (fun _ _ _ h₁ h₂ => unique _ _ _ h₁.1 h₁.2 h₂.2)
    (establish hu) (establish hv) ⟨hu, huw⟩ ⟨hv, hvw⟩

theorem parent_live {N : ℕ} {C : Circuit} {L : Finset ℕ} (hL : closed N C L)
    {j u : ℕ} (hj : j ∈ L) (hu : before C N j u) : Live N L u := by
  by_cases h : u < N
  · exact Or.inl h
  · have eq : u = N + (u - N) := by omega
    refine Or.inr ⟨u - N, hL.2 j hj _ ?_, eq⟩
    simpa only [← eq] using hu

theorem unchanged {N : ℕ} {C : Circuit} {L : Finset ℕ} (hL : closed N C L)
    {skip : Option ℕ} {i : ℕ} {x y : ℕ → Bool}
    (hx : Model N C L skip x) (hy : Model N C L skip y) (hc : Changes N i skip x y)
    {w : ℕ} (live : Live N L w) (away : ¬ Path N C L i w) : x w = y w := by
  revert live away
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro live away
    rcases live with low | ⟨j, hj, rfl⟩
    · exact hc.1 _ low (fun h => away (h ▸ Relation.ReflTransGen.refl))
    by_cases cut : skip = some (N + j)
    · exact hc.2.1 _ cut
    rw [hx j hj cut, hy j hj cut]
    congr 1
    apply List.map_congr_left
    intro u hu
    split_ifs with hlt
    · have e : arc N C L u (N + j) := ⟨j, hj, rfl, hu, hlt⟩
      exact ih u hlt (parent_live hL hj ⟨hu,hlt⟩) (fun hp => away (.tail hp e))
    · rfl

private theorem eval_positive (g : Gate) (op : g.op = .and ∨ g.op = .or)
    {x y : ℕ → Bool} (h : ∀ w ∈ g.inputs, x w = true → y w = true) :
    g.op.eval (g.inputs.map x) = true → g.op.eval (g.inputs.map y) = true := by
  rcases op with op | op
  · simp only [op, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id]
    exact fun hx w hw => h w hw (hx w hw)
  · simp only [op, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
    rintro ⟨w, hw, hx⟩
    exact ⟨w, hw, h w hw hx⟩

private theorem eval_negative (g : Gate) (op : g.op = .not)
    {x y : ℕ → Bool} (h : ∀ w ∈ g.inputs, x w = true → y w = true) :
    g.op.eval (g.inputs.map y) = true → g.op.eval (g.inputs.map x) = true := by
  rw [op]
  rcases eq : g.inputs with _ | ⟨w, ws⟩
  · simp [GateOp.eval]
  · have hxy := h w (by simp [eq])
    simp only [GateOp.eval, List.map_cons, List.headD_cons]
    intro hy
    cases hxx : x w
    · rfl
    · rw [hxy hxx] at hy
      cases hy

theorem fixed_polarity {N : ℕ} {C : Circuit} {L : Finset ℕ}
    (hL : closed N C L) (hC : FanInTwo C) {skip : Option ℕ} {i : ℕ}
    (unique : ∀ a b c, Path N C L i a → arc N C L a b → arc N C L a c → b = c)
    {w : ℕ} (live : Live N L w) : ∃ positive : Bool, Sign N C L skip i w positive := by
  classical
  revert live
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro live
    by_cases away : ¬ Path N C L i w
    · exact ⟨true, fun x y hx hy hxy => by
        simp only [ite_true, unchanged hL hx hy hxy live away, imp_self]⟩
    rcases live with low | ⟨j, hj, rfl⟩
    · refine ⟨true, fun x y hx hy hxy => ?_⟩
      simp only [ite_true]
      by_cases h : w = i
      · simpa only [h] using hxy.2.2
      · rw [hxy.1 w low h]
        exact id
    by_cases cut : skip = some (N + j)
    · exact ⟨true, fun x y hx hy hxy => by simp only [ite_true, hxy.2.1 _ cut, imp_self]⟩
    by_cases has : ∃ u, before C N j u ∧ Path N C L i u
    · obtain ⟨u, hu, hpu⟩ := has
      obtain ⟨s, hs⟩ := ih u hu.2 (parent_live hL hj hu)
      have eq {v : ℕ} (hv : before C N j v) (hpv : Path N C L i v) : v = u :=
        last_eq unique hpv hpu ⟨j, hj, rfl, hv⟩ ⟨j, hj, rfl, hu⟩
      have mem : gateAt C j ∈ C.gates := by
        rw [gateAt, List.getD_eq_getElem _ _ (hL.1 j hj)]
        exact List.getElem_mem _
      have hop := (hC _ mem).1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      let Tx (x : ℕ → Bool) v := if v < N + j then x v else false
      have directions (x y : ℕ → Bool) (hx : Model N C L skip x) (hy : Model N C L skip y)
          (hc : Changes N i skip x y) :
          (if s then ∀ v ∈ (gateAt C j).inputs, Tx x v = true → Tx y v = true
           else ∀ v ∈ (gateAt C j).inputs, Tx y v = true → Tx x v = true) := by
        have uniform := hs x y hx hy hc
        have equal (v : ℕ) (hv : before C N j v) (hv' : ¬ Path N C L i v) :
            x v = y v := unchanged hL hx hy hc (parent_live hL hj hv) hv'
        cases se : s <;> simp only [se, ite_true] at uniform ⊢
        · intro v hv
          unfold Tx
          split_ifs with hlt
          · by_cases p : Path N C L i v
            · rw [eq ⟨hv,hlt⟩ p]
              exact uniform
            · rw [equal v ⟨hv,hlt⟩ p]
              exact id
          · exact id
        · intro v hv
          unfold Tx
          split_ifs with hlt
          · by_cases p : Path N C L i v
            · rw [eq ⟨hv,hlt⟩ p]
              exact uniform
            · rw [equal v ⟨hv,hlt⟩ p]
              exact id
          · exact id
      rcases hop with ha | ho | hn
      · refine ⟨s, fun x y hx hy hc => ?_⟩
        rw [hx j hj cut, hy j hj cut]
        have hm := directions x y hx hy hc
        cases s
        · exact eval_positive _ (Or.inl ha) hm
        · exact eval_positive _ (Or.inl ha) hm
      · refine ⟨s, fun x y hx hy hc => ?_⟩
        rw [hx j hj cut, hy j hj cut]
        have hm := directions x y hx hy hc
        cases s
        · exact eval_positive _ (Or.inr ho) hm
        · exact eval_positive _ (Or.inr ho) hm
      · refine ⟨!s, fun x y hx hy hc => ?_⟩
        rw [hx j hj cut, hy j hj cut]
        have hm := directions x y hx hy hc
        cases s
        · exact eval_negative _ hn hm
        · exact eval_negative _ hn hm
    · refine ⟨true, fun x y hx hy hc => ?_⟩
      simp only [ite_true]
      have e : x (N + j) = y (N + j) := by
        rw [hx j hj cut, hy j hj cut]
        congr 1
        apply List.map_congr_left
        intro u hu
        split_ifs with hlt
        · exact unchanged hL hx hy hc (parent_live hL hj ⟨hu,hlt⟩) (fun p => has ⟨_, ⟨hu,hlt⟩, p⟩)
        · rfl
      rw [e]
      exact id

theorem outside_fork_unate {N : ℕ} {C : Circuit} {L : Finset ℕ}
    (hL : closed N C L) (hC : FanInTwo C) {fork skip : Option ℕ} {i : ℕ}
    (unique : ∀ a j k, fork ≠ some a → j ∈ L → k ∈ L →
      before C N j a → before C N k a → j = k)
    (away : ∀ f, fork = some f → ¬ Path N C L i f)
    {w : ℕ} (live : Live N L w) :
    ∃ positive : Bool, Sign N C L skip i w positive := by
  apply fixed_polarity hL hC _ live
  rintro a _ _ path ⟨j, hj, rfl, hb⟩ ⟨k, hk, rfl, hc⟩
  rw [unique a j k (fun h => away a h path) hj hk hb hc]

theorem value_changes {N i : ℕ} (hi : i < N) (C : Circuit) {x y : ℕ → Bool}
    (h : Changes N i none x y) :
    Changes N i none (value N C x (fun _ => none)) (value N C y (fun _ => none)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro w hw hn
    rw [val_raw hw rfl, val_raw hw rfl]
    exact h.1 w hw hn
  · intro w e
    cases e
  · rw [val_raw hi rfl, val_raw hi rfl]
    exact h.2.2

theorem original_unate {N : ℕ} {C : Circuit} {L : Finset ℕ}
    (hL : closed N C L) (hC : FanInTwo C) {fork : Option ℕ} {i : ℕ} (hi : i < N)
    (unique : ∀ a j k, fork ≠ some a → j ∈ L → k ∈ L →
      before C N j a → before C N k a → j = k)
    (away : ∀ f, fork = some f → ¬ Path N C L i f)
    {w : ℕ} (live : Live N L w) :
    ∃ pos : Bool, ∀ x y : ℕ → Bool, Changes N i none x y →
      if pos then value N C x (fun _ => none) w = true → value N C y (fun _ => none) w = true
      else value N C y (fun _ => none) w = true → value N C x (fun _ => none) w = true := by
  obtain ⟨s, hs⟩ := outside_fork_unate (skip := none) hL hC unique away live
  exact ⟨s, fun x y h =>
    hs _ _ (value_is_model hL x) (value_is_model hL y) (value_changes hi C h)⟩

theorem not_path_unused {N : ℕ} {C : Circuit} {L : Finset ℕ} {i w : ℕ}
    (unused : i ∉ used N C L) (ne : i ≠ w) : ¬ Path N C L i w := by
  intro path
  rcases path.cases_head with e | ⟨a, ⟨j, hj, _, h⟩, _⟩
  · exact ne e
  · exact unused (mem_used.mpr ⟨j,hj,h⟩)

theorem change_insert_input {N i t : ℕ} (ne : i ≠ t) :
    Changes N i none (fun k => decide (k = t)) (fun k => decide (k = i ∨ k = t)) := by
  refine ⟨?_,?_,?_⟩
  · intro k _ hk
    simp [hk]
  · intro w e
    cases e
  · simp [Ne.symm ne]

theorem omitted_row_comparable {n m : ℕ} {A : Fin n → Fin m → Bool}
    {C : Circuit} {L : Finset ℕ} (rep : PEqualNP.Represents.Represents A C)
    (hL : closed (n+m) C L) (live : Live (n+m) L C.output)
    {i₀ i : Fin n} (omitted : ¬ Path (n+m) C L i₀.val C.output)
    (polarity : ∃ pos : Bool, ∀ x y : ℕ → Bool, Changes (n+m) i.val none x y →
      if pos then value (n+m) C x (fun _ => none) C.output = true →
                   value (n+m) C y (fun _ => none) C.output = true
      else value (n+m) C y (fun _ => none) C.output = true →
           value (n+m) C x (fun _ => none) C.output = true) :
    (∀ j, A i₀ j = true → A i j = true) ∨ (∀ j, A i j = true → A i₀ j = true) := by
  have vi := i.isLt
  have vi₀ := i₀.isLt
  let bare (j : Fin m) (k : ℕ) : Bool := decide (k = n + j.val)
  let row (a : Fin n) (j : Fin m) (k : ℕ) : Bool := decide (k = a.val ∨ k = n + j.val)
  have rowEval (a : Fin n) (j : Fin m) :
      value (n+m) C (row a j) (fun _ => none) C.output = A a j := by
    let x := PEqualNP.Represents.oneEach a j
    have e : (fun k => x.getD k false) = row a j := funext (each_value a j)
    rw [← e, val_original (n+m) C x (by simp [x, PEqualNP.Represents.oneEach])]
    exact rep a j
  have bareEval (j : Fin m) :
      value (n+m) C (bare j) (fun _ => none) C.output = A i₀ j := by
    rw [← rowEval i₀ j]
    exact unchanged hL (value_is_model hL _) (value_is_model hL _)
      (value_changes (by omega) C (change_insert_input (by omega))) live omitted
  obtain ⟨sign, hs⟩ := polarity
  have relate (j : Fin m) := hs (bare j) (row i j) (change_insert_input (by omega))
  cases sign
  · right
    intro j
    rw [← rowEval i j, ← bareEval j]
    exact relate j
  · left
    intro j
    rw [← bareEval j, ← rowEval i j]
    exact relate j

theorem omitted_col_comparable {n m : ℕ} {A : Fin n → Fin m → Bool}
    {C : Circuit} {L : Finset ℕ} (rep : PEqualNP.Represents.Represents A C)
    (hL : closed (n+m) C L) (live : Live (n+m) L C.output)
    {j₀ j : Fin m} (omitted : ¬ Path (n+m) C L (n+j₀.val) C.output)
    (polarity : ∃ pos : Bool, ∀ x y : ℕ → Bool, Changes (n+m) (n+j.val) none x y →
      if pos then value (n+m) C x (fun _ => none) C.output = true →
                   value (n+m) C y (fun _ => none) C.output = true
      else value (n+m) C y (fun _ => none) C.output = true →
           value (n+m) C x (fun _ => none) C.output = true) :
    (∀ i, A i j₀ = true → A i j = true) ∨ (∀ i, A i j = true → A i j₀ = true) := by
  have vj := j.isLt
  have vj₀ := j₀.isLt
  let bare (i : Fin n) (k : ℕ) : Bool := decide (k = i.val)
  let col (i : Fin n) (a : Fin m) (k : ℕ) : Bool := decide (k = n + a.val ∨ k = i.val)
  have colEval (i : Fin n) (a : Fin m) :
      value (n+m) C (col i a) (fun _ => none) C.output = A i a := by
    let x := PEqualNP.Represents.oneEach i a
    have e : (fun k => x.getD k false) = col i a := by
      funext k
      rw [each_value]
      simp only [col, or_comm]
    rw [← e, val_original (n+m) C x (by simp [x, PEqualNP.Represents.oneEach])]
    exact rep i a
  have bareEval (i : Fin n) :
      value (n+m) C (bare i) (fun _ => none) C.output = A i j₀ := by
    have vi := i.isLt
    rw [← colEval i j₀]
    exact unchanged hL (value_is_model hL _) (value_is_model hL _)
      (value_changes (by omega) C (change_insert_input (by omega))) live omitted
  obtain ⟨sign, hs⟩ := polarity
  have relate (i : Fin n) := hs (bare i) (col i j) (change_insert_input (by have := i.isLt; omega))
  cases sign
  · right
    intro i
    rw [← colEval i j, ← bareEval i]
    exact relate i
  · left
    intro i
    rw [← bareEval i, ← colEval i j]
    exact relate i

end PEqualNP.Outside.L_meta_26302_aux.Unate

namespace PEqualNP.Outside.L_meta_26302_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem tight_equals_mono {n m : ℕ} (A : Fin n → Fin m → Bool)
    (hn : 3 ≤ n) (hm : 3 ≤ m)
    (hi : Function.Injective A) (hj : Function.Injective (fun j i => A i j))
    (sr : ∀ i k l, k ≠ i → l ≠ i → comparable A i k → comparable A i l → k = l)
    (sc : ∀ j k l, k ≠ j → l ≠ j → comparable (fun j i => A i j) j k →
      comparable (fun j i => A i j) j l → k = l)
    (C : Circuit) (fan : FanInTwo C) (repr : Represents A C)
    (strict : C.size < n+m-1) :
    ∃ D : Circuit, Monotone2 D ∧ Represents A D ∧ D.size = C.size := by
  let E := Network.trim C
  have eSize : E.size = C.size := by simp [E, Network.trim, Circuit.size]
  have eSmall : E.size ≤ n+m-1 := eSize ▸ Nat.le_of_lt strict
  have eFan : FanInTwo E := Network.trim_fan C fan
  have eRepr : Represents A E := fun i j => (Network.trim_eval C (oneEach i j)).trans (repr i j)
  have rowW := line_witness A (by simpa using hn) sr
  have colW := line_witness (fun j i => A i j) (by simpa using hm) sc
  obtain ⟨raw,out⟩ := root_bounds (by omega) rowW colW E eRepr
  let r := E.output - (n+m)
  have eout : E.output = n+m+r := by dsimp [r]; omega
  have rreal : r < E.gates.length := by dsimp [r]; omega
  obtain ⟨L,hr,hL,hnext⟩ := minimal_closed (n+m) E r rreal
  have live : Unate.Live (n+m) L E.output := Or.inr ⟨r,hr,eout⟩
  have hrows := missing_rows_le hi eRepr hL hr eout
  have hcols := missing_cols_le hj eRepr hL hr eout
  by_cases no : (activeNot E L).card = 0
  · obtain ⟨D,hDmono,hDrepr,hDsize⟩ := noNotCircuit eFan hL hr eout no eRepr
    exact ⟨D,hDmono,hDrepr,hDsize.trans eSize⟩
  · exfalso
    by_cases single : Set.InjOn Prod.snd (slots (n+m) E L : Set (ℕ × ℕ))
    · have uniq (a j k : ℕ) (_ : (none : Option ℕ) ≠ some a)
          (hj : j ∈ L) (hk : k ∈ L) (ha : before E (n+m) j a) (hb : before E (n+m) k a) :
          j = k := unique_reader_of_inj single hj hk ha hb
      have away (i f : ℕ) (h : (none : Option ℕ) = some f) : ¬ Unate.Path (n+m) E L i f := by cases h
      have row0 : (missingRows n m E L).card = 0 := by
        by_contra hne
        obtain ⟨i₀, hm₀⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hne)
        have hu : i₀.val ∉ used (n+m) E L := (Finset.mem_filter.mp hm₀).2
        have hi₀ := i₀.isLt
        have hp : ¬ Unate.Path (n+m) E L i₀.val E.output :=
          Unate.not_path_unused hu (by omega)
        obtain ⟨i,_,hnc⟩ := incomparable_partner A (by simpa using hn) sr i₀
        have pol := Unate.original_unate (fork := none) (i := i.val) hL eFan
          (by have := i.isLt; omega) uniq (away i.val) live
        exact hnc (Unate.omitted_row_comparable eRepr hL live hp pol)
      have col0 : (missingCols n m E L).card = 0 := by
        by_contra hne
        obtain ⟨j₀, hm₀⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hne)
        have hu : n+j₀.val ∉ used (n+m) E L := (Finset.mem_filter.mp hm₀).2
        have hj₀ := j₀.isLt
        have hp : ¬ Unate.Path (n+m) E L (n+j₀.val) E.output :=
          Unate.not_path_unused hu (by omega)
        obtain ⟨j,_,hnc⟩ := incomparable_partner (fun j i => A i j) (by simpa using hm) sc j₀
        have pol := Unate.original_unate (fork := none) (i := n+j.val) hL eFan
          (by have := j.isLt; omega) uniq (away (n+j.val)) live
        exact hnc (Unate.omitted_col_comparable eRepr hL live hp pol)
      exact no (no_not_if_full hr hL hnext eFan (Network.trim_unary C) eSmall row0 col0).1
    · obtain ⟨_,_,_,_,equal,_⟩ :=
        collision_counts hr hL hnext eFan (Network.trim_unary C) eSmall hrows hcols
          (Nat.pos_of_ne_zero no) single
      rw [eSize] at equal
      omega

end PEqualNP.Outside.L_meta_26302_aux

theorem PEqualNP.Outside.L_meta_26302 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([8, 4, 2, 1] : List ℕ).getD u.val 0).testBit v.val) C)) := by
  rintro ⟨C, fan, small, rep⟩
  let A (i j : Fin 4) : Bool := (([8,4,2,1] : List ℕ).getD i.val 0).testBit j.val
  let N : (Fin 4 → Fin 4 → Bool) → Fin 4 → Fin 4 → Prop :=
    PEqualNP.Outside.L_meta_26302_aux.comparable
  have hi : Function.Injective A := by
    intro i k h
    have finite : ∀ a b : Fin 4, (∀ j : Fin 4, A a j = A b j) → a = b := by
      dsimp only [A]
      decide
    exact finite i k (congrFun h)
  have hj : Function.Injective (fun j i => A i j) := by
    intro j l h
    have finite : ∀ a b : Fin 4, (∀ i : Fin 4, A i a = A i b) → a = b := by
      dsimp only [A]
      decide
    exact finite j l (congrFun h)
  have sr : ∀ i k l, k ≠ i → l ≠ i → N A i k → N A i l → k = l := by
    dsimp only [N, A, PEqualNP.Outside.L_meta_26302_aux.comparable]
    decide
  have sc : ∀ j k l, k ≠ j → l ≠ j → N (fun j i => A i j) j k →
      N (fun j i => A i j) j l → k = l := by
    dsimp only [N, A, PEqualNP.Outside.L_meta_26302_aux.comparable]
    decide
  have cap : C.size ≤ 4+4-1 := by omega
  have strict : C.size < 4+4-1 := by omega
  obtain ⟨D, mono, dRep, same⟩ :=
    PEqualNP.Outside.L_meta_26302_aux.tight_equals_mono A (by decide) (by decide) hi hj sr sc
      C fan rep strict
  have lo := PEqualNP.Outside.L_meta_26302_aux.monotone_lower A (by decide) (by decide)
    sr sc D mono dRep (same.trans_le cap)
  omega
