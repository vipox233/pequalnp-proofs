import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25902_aux
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

theorem line_not_full {ι κ : Type} [Fintype ι] (A : ι → κ → Bool)
    (hι : 3 ≤ Fintype.card ι)
    (sparse : ∀ i k l, k ≠ i → l ≠ i → comparable A i k → comparable A i l → k = l)
    (i : ι) : ¬ ∀ j, A i j = true := by
  intro full
  obtain ⟨k, _, hic⟩ := incomparable_partner A hι sparse i
  exact hic (.inr fun j _ => full j)

theorem deduce_matching {n m : ℕ} (A : Fin n → Fin m → Bool)
    (hrow : Function.Injective A) (hcol : Function.Injective (fun j i => A i j))
    (rowNonempty : ∀ i, ∃ j, A i j = true)
    (colNonempty : ∀ j, ∃ i, A i j = true)
    (rectangle : ∀ a b c d, A a b = true → A c b = true → A c d = true → A a d = true) :
    ∃ e : Fin n ≃ Fin m, ∀ i j, A i j = decide (e i = j) := by
  classical
  have sameRow (i k : Fin n) (j : Fin m) (hi : A i j = true) (hk : A k j = true) : i = k := by
    apply hrow
    funext l
    cases hi' : A i l <;> cases hk' : A k l <;> try rfl
    · exact hi'.symm.trans (rectangle i j k l hi hk hk')
    · exact (rectangle k j i l hk hi hi').symm.trans hk'
  have sameCol (j l : Fin m) (i : Fin n) (hj : A i j = true) (hl : A i l = true) : j = l := by
    apply hcol
    funext k
    change A k j = A k l
    cases hj' : A k j <;> cases hl' : A k l <;> try rfl
    · exact hj'.symm.trans (rectangle k l i j hl' hl hj)
    · exact (rectangle k j i l hj' hj hl).symm.trans hl'
  let f := fun i => Classical.choose (rowNonempty i)
  have hf (i : Fin n) : A i (f i) = true := Classical.choose_spec (rowNonempty i)
  have bij : Function.Bijective f := by
    constructor
    · intro i k h
      exact sameRow i k (f i) (hf i) (h.symm ▸ hf k)
    · intro j
      obtain ⟨i, hi⟩ := colNonempty j
      exact ⟨i, sameCol _ _ _ (hf i) hi⟩
  refine ⟨Equiv.ofBijective f bij, fun i j => ?_⟩
  change A i j = decide (f i = j)
  by_cases h : f i = j
  · simpa [h] using hf i
  · have hh : A i j = false := Bool.eq_false_iff.mpr fun h' => h (sameCol _ _ _ (hf i) h')
    simp [h,hh]

theorem monotone_tight {n m : ℕ} (A : Fin n → Fin m → Bool)
    (hn : 3 ≤ n) (hm : 3 ≤ m)
    (hi : Function.Injective A) (hj : Function.Injective (fun j i => A i j))
    (sr : ∀ i k l, k ≠ i → l ≠ i → comparable A i k → comparable A i l → k = l)
    (sc : ∀ j k l, k ≠ j → l ≠ j → comparable (fun j i => A i j) j k →
      comparable (fun j i => A i j) j l → k = l)
    (C : Circuit) (mono : Monotone2 C) (repr : Represents A C)
    (small : C.size ≤ n + m - 1) :
    n + m - 1 ≤ C.size ∧ ∃ e : Fin n ≃ Fin m, ∀ i j, A i j = decide (e i = j) := by
  have hr := line_witness A (by simpa using hn) sr
  have hc := line_witness (fun j i => A i j) (by simpa using hm) sc
  obtain ⟨hraw, hout⟩ := root_bounds (by omega) hr hc C repr
  obtain ⟨hsize, hgate, hback, hread, hvalid, hunread⟩ :=
    output_shape C mono small hraw hout
      (fun L r hL hmem he => support_all hr hc C mono repr hL hmem he)
  refine ⟨le_of_eq hsize.symm, ?_⟩
  obtain ⟨label, hs, _⟩ := label_invariant (n + m) C hgate hback (fun i _ => hread i) _ le_rfl
  let F := wire (n + m) C C.output
  have rect := (hs C.output ⟨hvalid, hunread⟩).2.2.2.2
  have edge_eq (u : Fin n) (v : Fin m) : F (bits {row u, col v}) = A u v := by
    change C.eval (List.ofFn (bits {row u, col v})) = _
    rw [← oneEach_bits]
    exact repr u v
  have rowFalse (u : Fin n) : F (bits ({row u} : Finset (Fin (n + m)))) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    apply line_not_full A (by simpa using hn) sr u
    intro v
    rw [← edge_eq u v]
    exact wire_mono C mono C.output (Finset.singleton_subset_iff.mpr (by simp)) h
  have colFalse (v : Fin m) : F (bits ({col v} : Finset (Fin (n + m)))) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    apply line_not_full (fun j i => A i j) (by simpa using hm) sc v
    intro u
    rw [← edge_eq u v]
    exact wire_mono C mono C.output (Finset.singleton_subset_iff.mpr (by simp)) h
  apply deduce_matching A hi hj
  · intro i
    obtain ⟨_, _, j, hj, _⟩ := hr i
    exact ⟨j, hj⟩
  · intro j
    obtain ⟨_, _, i, hi, _⟩ := hc j
    exact ⟨i, hi⟩
  · intro a b c d hab hcb hcd
    have he (u : Fin n) (v : Fin m) : edge F (row u) (col v) ↔ A u v = true := by
      unfold edge
      rw [edge_eq]
    exact (he a d).1 (rect (row a) (col b) (row c) (col d) (rowFalse a) (colFalse b)
      (rowFalse c) (colFalse d) ((he a b).2 hab) ((he c b).2 hcb) ((he c d).2 hcd))

end PEqualNP.Outside.L_meta_25902_aux

namespace PEqualNP.Outside.L_meta_25902_aux
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

def live (N : ℕ) (L : Finset ℕ) (w : ℕ) : Prop :=
  w < N ∨ ∃ j ∈ L, w = N+j

theorem prev_live {N : ℕ} {C : Circuit} {L : Finset ℕ} (closedL : closed N C L)
    {j u : ℕ} (hj : j ∈ L) (hb : before C N j u) : live N L u := by
  by_cases hu : u < N
  · exact .inl hu
  · have eq : u = N + (u-N) := by omega
    right
    refine ⟨u-N, closedL.2 j hj _ ?_, eq⟩
    rwa [← eq]

theorem path_head {N : ℕ} {C : Circuit} {L : Finset ℕ} {w v : ℕ}
    (p : reaches N C L w v) (neq : w ≠ v) :
    ∃ z, edgeTo N C L w z ∧ reaches N C L z v := by
  induction p with
  | refl => exact (neq rfl).elim
  | @tail b c p e ih =>
    by_cases h : w = b
    · subst b
      exact ⟨c,e,.refl⟩
    · obtain ⟨z,hz,hp⟩ := ih h
      exact ⟨z,hz,hp.tail e⟩

theorem every_gate_reaches_root {N : ℕ} {C : Circuit} {L : Finset ℕ}
    (cl : closed N C L) {r : ℕ}
    (next : ∀ j ∈ L, j ≠ r → ∃ k ∈ L, before C N k (N+j))
    (j : ℕ) (hj : j ∈ L) : reaches N C L (N+j) (N+r) := by
  by_cases e : j = r
  · subst j
    exact .refl
  · obtain ⟨k, hk, hb⟩ := next j hj e
    have hlt := hb.2
    have hkvalid := cl.1 k hk
    exact .head ⟨k, hk, rfl, hb⟩ (every_gate_reaches_root cl next k hk)
termination_by C.gates.length - j
decreasing_by omega

theorem value_agree {N : ℕ} {C : Circuit} {L : Finset ℕ} (cl : closed N C L)
    (w : ℕ) (hw : live N L w) (x y : ℕ → Bool) (O P : ℕ → Option Bool)
    (raw : ∀ u < N, reaches N C L u w → x u = y u)
    (hOverride : ∀ u, reaches N C L u w → O u = P u) :
    value N C x O w = value N C y P w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    have he := hOverride w (.refl)
    cases hO : O w with
    | some b =>
      have hP : P w = some b := he.symm.trans hO
      rw [value, hO]
      symm
      rw [value, hP]
    | none =>
      have hP : P w = none := he.symm.trans hO
      rcases hw with hw | ⟨j,hj,rfl⟩
      · rw [val_raw hw hO, val_raw hw hP, raw w hw .refl]
      · rw [val_gate (cl.1 j hj) hO, val_gate (cl.1 j hj) hP]
        congr 1
        apply List.map_congr_left
        intro u hu
        split_ifs with h
        · let E : edgeTo N C L u (N+j) := ⟨j, hj, rfl, hu, h⟩
          apply ih u h (prev_live cl hj ⟨hu,h⟩)
          · intro v hv p
            exact raw v hv (p.tail E)
          · intro v p
            exact hOverride v (p.tail E)
        · rfl

theorem replace_signal {N : ℕ} {C : Circuit} {L : Finset ℕ} (cl : closed N C L)
    (x : ℕ → Bool) (f w : ℕ) (hw : live N L w) :
    value N C x (fun _ => none) w =
      value N C x (relay f (value N C x (fun _ => none) f)) w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases h : w = f
    · subst w
      exact (val_relay N C x f _).symm
    · have ho : relay f (value N C x (fun _ => none) f) w = none := by simp [relay,h]
      rcases hw with hraw | ⟨j,hj,rfl⟩
      · rw [val_raw hraw ho, val_raw hraw rfl]
      · rw [val_gate (cl.1 j hj) ho, val_gate (cl.1 j hj) rfl]
        congr 1
        apply List.map_congr_left
        intro u hu
        split_ifs with hlt
        · exact ih u hlt (prev_live cl hj ⟨hu,hlt⟩)
        · rfl

theorem no_leak {N : ℕ} {C : Circuit} {L : Finset ℕ} {f u w : ℕ}
    (single : ∀ a, a ≠ f → ∀ b c, edgeTo N C L a b → edgeTo N C L a c → b = c)
    (e : edgeTo N C L u w) (inside : reaches N C L u f) (hne : u ≠ f) :
    reaches N C L w f := by
  obtain ⟨z, ez, p⟩ := path_head inside hne
  rwa [← single u hne w z e ez] at p

theorem cut_agree {N : ℕ} {C : Circuit} {L : Finset ℕ} (cl : closed N C L)
    (f : ℕ)
    (single : ∀ a, a ≠ f → ∀ b c, edgeTo N C L a b → edgeTo N C L a c → b = c)
    (b : Bool) (x y : ℕ → Bool)
    (raw : ∀ u < N, ¬ reaches N C L u f → x u = y u)
    (w : ℕ) (hw : live N L w) (out : w = f ∨ ¬ reaches N C L w f) :
    value N C x (relay f b) w = value N C y (relay f b) w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rcases out with rfl | out
    · rw [val_relay, val_relay]
    · have ne : w ≠ f := fun e => out (e ▸ .refl)
      have ho : relay f b w = none := by simp [relay,ne]
      rcases hw with hw | ⟨j,hj,rfl⟩
      · rw [val_raw hw ho, val_raw hw ho, raw w hw out]
      · rw [val_gate (cl.1 j hj) ho, val_gate (cl.1 j hj) ho]
        congr 1
        apply List.map_congr_left
        intro u hu
        split_ifs with h
        · let E : edgeTo N C L u (N+j) := ⟨j,hj,rfl,hu,h⟩
          apply ih u h (prev_live cl hj ⟨hu,h⟩)
          by_cases ef : u = f
          · exact .inl ef
          · exact .inr (fun p => out (no_leak single E p ef))
        · rfl

theorem gate_order (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (u v : ℕ → Bool) (h : ∀ i ∈ g.inputs, u i = true → v i = true) :
    g.op.eval (g.inputs.map u) = true → g.op.eval (g.inputs.map v) = true := by
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
    intro hm b hb
    obtain ⟨i, hi, rfl⟩ := hb
    exact h i hi (hm _ ⟨i,hi,rfl⟩)
  · simp only [hop, GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨b, ⟨i,hi,rfl⟩, hb⟩
    exact ⟨v i, ⟨i,hi,rfl⟩, h i hi hb⟩

theorem value_mono {N : ℕ} {C : Circuit} {L : Finset ℕ} (cl : closed N C L)
    (w : ℕ) (hw : live N L w) (x y : ℕ → Bool) (O P : ℕ → Option Bool)
    (raw : ∀ u < N, reaches N C L u w → x u = true → y u = true)
    (hOverride : ∀ u, reaches N C L u w → (O u = none ∧ P u = none) ∨
      ∃ b c, O u = some b ∧ P u = some c ∧ (b = true → c = true))
    (gates : ∀ j ∈ L, reaches N C L (N+j) w → O (N+j) = none →
      (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) :
    value N C x O w = true → value N C y P w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rcases hOverride w .refl with ⟨hO,hP⟩ | ⟨b,c,hO,hP,hle⟩
    · rcases hw with hw | ⟨j,hj,rfl⟩
      · rw [val_raw hw hO, val_raw hw hP]
        exact raw w hw .refl
      · rw [val_gate (cl.1 j hj) hO, val_gate (cl.1 j hj) hP]
        apply gate_order _ (gates j hj .refl hO)
        intro u hu
        split_ifs with h
        · let E : edgeTo N C L u (N+j) := ⟨j,hj,rfl,hu,h⟩
          apply ih u h (prev_live cl hj ⟨hu,h⟩)
          · intro v hv p
            exact raw v hv (p.tail E)
          · intro v p
            exact hOverride v (p.tail E)
          · intro k hk p
            exact gates k hk (p.tail E)
        · exact id
    · have hx : value N C x O w = b := by rw [value,hO]
      have hy : value N C y P w = c := by rw [value,hP]
      simpa only [hx,hy] using hle

end Network
end PEqualNP.Outside.L_meta_25902_aux

namespace PEqualNP.Outside.L_meta_25902_aux

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

theorem unique_collision {N : ℕ} {C : Circuit} {L : Finset ℕ}
    (hc : (slots N C L).card = (used N C L).card + 1)
    {j k w : ℕ} (hj : j ∈ L) (hk : k ∈ L) (hne : j ≠ k)
    (he : before C N j w) (hf : before C N k w) :
    ∀ {a b v : ℕ}, a ∈ L → b ∈ L → a ≠ b → before C N a v → before C N b v →
      v = w ∧ ((a=j ∧ b=k) ∨ (a=k ∧ b=j)) := by
  let S := slots N C L
  have hjs : (j,w) ∈ S := mem_slot.mpr ⟨hj,he⟩
  have hks : (k,w) ∈ S := mem_slot.mpr ⟨hk,hf⟩
  have hks' : (k,w) ∈ S.erase (j,w) := Finset.mem_erase.mpr
    ⟨fun h => hne (congrArg Prod.fst h).symm, hks⟩
  have him : (S.erase (j,w)).image Prod.snd = S.image Prod.snd := by
    apply Finset.Subset.antisymm (Finset.image_subset_image (Finset.erase_subset _ _))
    intro y hy
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hy
    by_cases e : p = (j,w)
    · subst p
      exact Finset.mem_image.mpr ⟨(k,w),hks',rfl⟩
    · exact Finset.mem_image.mpr ⟨p,Finset.mem_erase.mpr ⟨e,hp⟩,rfl⟩
  have hinj : Set.InjOn Prod.snd (S.erase (j,w) : Set (ℕ × ℕ)) := by
    apply Finset.injOn_of_card_image_eq
    rw [him, Finset.card_erase_of_mem hjs]
    change (used N C L).card = (slots N C L).card-1
    omega
  intro a b v ha hb hab hav hbv
  have has : (a,v) ∈ S := mem_slot.mpr ⟨ha,hav⟩
  have hbs : (b,v) ∈ S := mem_slot.mpr ⟨hb,hbv⟩
  by_cases ea : (a,v) = (j,w)
  · obtain ⟨rfl,rfl⟩ := Prod.mk.inj ea
    have hb' : (b,v) ∈ S.erase (a,v) := Finset.mem_erase.mpr ⟨fun h => hab (congrArg Prod.fst h).symm,hbs⟩
    have q := congrArg Prod.fst (hinj hb' hks' rfl)
    exact ⟨rfl,Or.inl ⟨rfl,q⟩⟩
  · have ha' := Finset.mem_erase.mpr ⟨ea,has⟩
    by_cases eb : (b,v) = (j,w)
    · obtain ⟨rfl,rfl⟩ := Prod.mk.inj eb
      have q := congrArg Prod.fst (hinj ha' hks' rfl)
      exact ⟨rfl,Or.inr ⟨q,rfl⟩⟩
    · have hb' := Finset.mem_erase.mpr ⟨eb,hbs⟩
      exact (hab (congrArg Prod.fst (hinj ha' hb' rfl))).elim

end PEqualNP.Outside.L_meta_25902_aux

namespace PEqualNP.Outside.L_meta_25902_aux

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

end PEqualNP.Outside.L_meta_25902_aux

namespace PEqualNP.Outside.L_meta_25902_aux

def implication (a b : Bool) : Prop := a = true → b = true

theorem readout_unate (H : Bool → Bool → Bool)
    (h : (∀ z, implication (H z false) (H z true)) ∨
         (∀ z, implication (H z true) (H z false))) :
    (∀ c, implication (H false c) (H true c)) ∨
    (∀ c, implication (H true c) (H false c)) := by
  have b : ∀ k : Bool → Prop, (∀ x, k x) ↔ k false ∧ k true := by
    intro k
    exact ⟨fun hk => ⟨hk false, hk true⟩, fun hk x => by cases x; exact hk.1; exact hk.2⟩
  simp only [b, implication] at h ⊢
  cases h00 : H false false <;> cases h01 : H false true <;>
    cases h10 : H true false <;> cases h11 : H true true <;>
    simp_all

theorem readout_rows_comparable {α : Type} (H : Bool → Bool → Bool)
    (h : (∀ z, implication (H z false) (H z true)) ∨
         (∀ z, implication (H z true) (H z false)))
    (u v selector : α → Bool) (mon : ∀ j, implication (u j) (v j)) :
    (∀ j, implication (H (u j) (selector j)) (H (v j) (selector j))) ∨
    (∀ j, implication (H (v j) (selector j)) (H (u j) (selector j))) := by
  rcases readout_unate H h with pos | neg
  · left
    intro j
    have hx := mon j
    rcases hu : u j <;> rcases hv : v j
    · exact id
    · exact pos (selector j)
    · exact False.elim (by simp [implication, hu, hv] at hx)
    · exact id
  · right
    intro j
    have hx := mon j
    rcases hu : u j <;> rcases hv : v j
    · exact id
    · exact neg (selector j)
    · exact False.elim (by simp [implication, hu, hv] at hx)
    · exact id

end PEqualNP.Outside.L_meta_25902_aux

namespace PEqualNP.Outside.L_meta_25902_aux.Unate

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

theorem relay_is_model {N : ℕ} {C : Circuit} {L : Finset ℕ}
    (hL : closed N C L) (x : ℕ → Bool) (f : ℕ) (b : Bool) :
    Model N C L (some f) (value N C x (relay f b)) := by
  intro j hj hs
  apply val_gate (hL.1 j hj)
  have ne : N + j ≠ f := fun e => hs (by rw [e])
  simp [relay, ne]

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

theorem relay_changes {N i f : ℕ} (hi : i < N) (hne : i ≠ f)
    (C : Circuit) (b : Bool) {x y : ℕ → Bool} (h : Changes N i none x y) :
    Changes N i (some f) (value N C x (relay f b)) (value N C y (relay f b)) := by
  have off (w) (e : w ≠ f) : relay f b w = none := by simp [relay,e]
  refine ⟨?_, ?_, ?_⟩
  · intro w hw hn
    by_cases e : w = f
    · subst w
      rw [val_relay, val_relay]
    · rw [val_raw hw (off w e), val_raw hw (off w e)]
      exact h.1 w hw hn
  · rintro w e
    obtain rfl : f = w := Option.some.inj e
    rw [val_relay, val_relay]
  · rw [val_raw hi (off i hne), val_raw hi (off i hne)]
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

theorem relay_unate {N : ℕ} {C : Circuit} {L : Finset ℕ}
    (hL : closed N C L) (hC : FanInTwo C) {f i : ℕ} (hi : i < N)
    (unique : ∀ a j k, a ≠ f → j ∈ L → k ∈ L →
      before C N j a → before C N k a → j = k)
    (away : ¬ Path N C L i f) {w : ℕ} (live : Live N L w) :
    ∃ pos : Bool, ∀ b : Bool, ∀ x y : ℕ → Bool, Changes N i none x y →
      if pos then value N C x (relay f b) w = true → value N C y (relay f b) w = true
      else value N C y (relay f b) w = true → value N C x (relay f b) w = true := by
  have hine : i ≠ f := fun e => away (e ▸ Relation.ReflTransGen.refl)
  have uq (a j k) (h : some f ≠ some a) (hj : j ∈ L) (hk : k ∈ L)
      (ha : before C N j a) (hb : before C N k a) : j = k :=
    unique a j k (fun e => h (congrArg some e.symm)) hj hk ha hb
  have out (g : ℕ) (h : some f = some g) : ¬ Path N C L i g :=
    Option.some.inj h ▸ away
  obtain ⟨s, hs⟩ := outside_fork_unate (skip := some f) hL hC uq out live
  exact ⟨s, fun b x y h =>
    hs _ _ (relay_is_model hL x f b) (relay_is_model hL y f b) (relay_changes hi hine C b h)⟩

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

end PEqualNP.Outside.L_meta_25902_aux.Unate

namespace PEqualNP.Outside.L_meta_25902_aux.Unate

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Network

theorem inner_unate {N : ℕ} {C : Circuit} {L : Finset ℕ} {f i : ℕ}
    (hL : closed N C L) (hC : FanInTwo C) (hi : i < N)
    (unique : ∀ a j k, a ≠ f → j ∈ L → k ∈ L →
      before C N j a → before C N k a → j = k)
    (hf : Live N L f) :
    ∃ pos : Bool, ∀ x y : ℕ → Bool, Changes N i none x y →
      if pos then value N C x (fun _ => none) f = true → value N C y (fun _ => none) f = true
      else value N C y (fun _ => none) f = true → value N C x (fun _ => none) f = true := by
  let L0 := L.filter (fun j => N + j ≤ f)
  have hclose : closed N C L0 := by
    constructor
    · intro j hj
      exact hL.1 j (Finset.mem_filter.mp hj).1
    · intro j hj k hkj
      obtain ⟨hjL,hjf⟩ := Finset.mem_filter.mp hj
      exact Finset.mem_filter.mpr ⟨hL.2 j hjL k hkj, hkj.2.le.trans hjf⟩
  have hf0 : Live N L0 f := by
    rcases hf with hf | ⟨j,hj,rfl⟩
    · exact Or.inl hf
    · exact Or.inr ⟨j,Finset.mem_filter.mpr ⟨hj,le_rfl⟩,rfl⟩
  apply original_unate (fork := none) hclose hC hi _ _ hf0
  · intro a j k _ hj hk hja hka
    obtain ⟨hjL,hjf⟩ := Finset.mem_filter.mp hj
    exact unique a j k (hja.2.trans_le hjf).ne hjL (Finset.mem_filter.mp hk).1 hja hka
  · intro g eg
    cases eg

end PEqualNP.Outside.L_meta_25902_aux.Unate

namespace PEqualNP.Outside.L_meta_25902_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def add (N : ℕ) (C : Circuit) (g : Gate) : Circuit := ⟨C.gates ++ [g], N + C.size⟩

def prodGate (p : ℕ × ℕ) : Gate := ⟨.and, [p.1,p.2]⟩

def orGate (a b : ℕ) : Gate := ⟨.or, [a,b]⟩

def matching (N : ℕ) : List (ℕ × ℕ) → Circuit
  | [] => ⟨[],N⟩
  | p :: ps =>
    let C := matching N ps
    let D := add N C (prodGate p)
    if ps.isEmpty then D else add N D (orGate C.output D.output)

theorem add_size (N : ℕ) (C : Circuit) (g : Gate) : (add N C g).size = C.size + 1 := by
  simp [add, Circuit.size]

theorem matching_size (N : ℕ) (ps : List (ℕ × ℕ)) : (matching N ps).size = 2 * ps.length - 1 := by
  induction ps with
  | nil => simp [matching, Circuit.size]
  | cons p ps ih =>
    cases ps with
    | nil => rfl
    | cons q qs =>
      change (add N (add N (matching N (q :: qs)) (prodGate p)) (orGate _ _)).size = _
      rw [add_size, add_size, ih]
      simp only [List.length_cons]
      omega

theorem add_ready (N : ℕ) (C : Circuit) (g : Gate) : (add N C g).output < N + (add N C g).size := by
  rw [add_size]
  change N + C.size < N + (C.size + 1)
  omega

theorem matching_ready (N : ℕ) (p : ℕ × ℕ) (ps : List (ℕ × ℕ)) :
    (matching N (p :: ps)).output < N + (matching N (p :: ps)).size := by
  simp only [matching]
  split <;> apply add_ready

theorem add_fanIn (N : ℕ) (C : Circuit) (g : Gate) (hC : FanInTwo C)
    (hg : g.op = .and ∨ g.op = .or) (hlen : g.inputs.length ≤ 2) : FanInTwo (add N C g) := by
  intro x hx
  change x ∈ C.gates ++ [g] at hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hC x hx
  · obtain rfl := List.mem_singleton.mp hx
    exact ⟨by rcases hg with h | h <;> simp [h], hlen⟩

theorem matching_fanIn (N : ℕ) (ps : List (ℕ × ℕ)) : FanInTwo (matching N ps) := by
  induction ps with
  | nil => simp [matching, FanInTwo]
  | cons p ps ih =>
    simp only [matching]
    split
    · exact add_fanIn _ _ _ ih (Or.inl rfl) (by rfl)
    · exact add_fanIn _ _ _ (add_fanIn _ _ _ ih (Or.inl rfl) (by rfl)) (Or.inr rfl) (by rfl)

theorem wireLen (C : Circuit) (x : List Bool) : (C.wires x).length = x.length + C.size := by
  obtain ⟨gs, o⟩ := C
  change ((⟨gs,o⟩ : Circuit).wires x).length = x.length + gs.length
  induction gs generalizing x with
  | nil => simp [Circuit.wires]
  | cons g gs ih =>
    simp only [Circuit.wires, List.foldl_cons, List.length_cons]
    rw [show gs.foldl _ (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) = (⟨gs,o⟩ : Circuit).wires (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) from rfl, ih]
    simp
    omega

theorem wireInput (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false := by
  obtain ⟨gs, o⟩ := C
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    let y := x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]
    have hy : i < y.length := by simp [y]; omega
    change ((⟨gs,o⟩ : Circuit).wires y).getD i false = _
    rw [ih y hy]
    exact List.getD_append _ _ _ _ hi

theorem wireAdd (N : ℕ) (C : Circuit) (g : Gate) (x : List Bool) :
    (add N C g).wires x = C.wires x ++ [g.op.eval (g.inputs.map fun i => (C.wires x).getD i false)] := by
  simp [add, Circuit.wires, List.foldl_append]

theorem addEval (C : Circuit) (g : Gate) (x : List Bool) :
    (add x.length C g).eval x = g.op.eval (g.inputs.map fun i => (C.wires x).getD i false) := by
  rw [Circuit.eval, wireAdd]
  change (C.wires x ++ [_]).getD (x.length + C.size) false = _
  rw [List.getD_append_right _ _ _ _ (by rw [wireLen]), wireLen, Nat.sub_self]
  rfl

theorem addProd_eval (C : Circuit) (p : ℕ × ℕ) (x : List Bool)
    (hP : p.1 < x.length ∧ p.2 < x.length) :
    (add x.length C (prodGate p)).eval x = (x.getD p.1 false && x.getD p.2 false) := by
  rw [addEval]
  simp only [prodGate, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
    Bool.and_true, id_eq]
  rw [wireInput C x _ hP.1, wireInput C x _ hP.2]

theorem addOr_eval (C : Circuit) (p : ℕ × ℕ) (x : List Bool)
    (hC : C.output < x.length + C.size) :
    let D := add x.length C (prodGate p)
    (add x.length D (orGate C.output D.output)).eval x = (C.eval x || D.eval x) := by
  dsimp only
  rw [addEval]
  have hc : C.output < (C.wires x).length := by rwa [wireLen]
  have hkeep : ((add x.length C (prodGate p)).wires x).getD C.output false = C.eval x := by
    rw [wireAdd, List.getD_append _ _ _ _ hc, Circuit.eval]
  simp only [orGate, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
    Bool.or_false, id_eq, hkeep]
  rfl

theorem matching_eval (ps : List (ℕ × ℕ)) (x : List Bool)
    (hP : ∀ p ∈ ps, p.1 < x.length ∧ p.2 < x.length) :
    (matching x.length ps).eval x = ps.any (fun p => x.getD p.1 false && x.getD p.2 false) := by
  induction ps with
  | nil => simp [matching, Circuit.eval, Circuit.wires, List.getD_eq_getElem?_getD]
  | cons p ps ih =>
    have hp := hP p (by simp)
    have hs := ih (fun p hp => hP p (List.mem_cons_of_mem _ hp))
    cases ps with
    | nil => simp [matching, addProd_eval _ _ _ hp]
    | cons q qs =>
      change (add x.length (add x.length (matching x.length (q :: qs)) (prodGate p)) (orGate _ _)).eval x = _
      rw [addOr_eval _ _ _ (matching_ready _ _ _), addProd_eval _ _ _ hp, hs]
      simp [Bool.or_comm]

theorem oneEach_length {n m : ℕ} (i : Fin n) (j : Fin m) : (oneEach i j).length = n + m := by
  simp [oneEach]

theorem oneEach_left {n m : ℕ} (i k : Fin n) (j : Fin m) :
    (oneEach i j).getD k false = decide (k = i) := by
  unfold oneEach
  rw [List.getD_append _ _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD, k.isLt]

theorem oneEach_right {n m : ℕ} (i : Fin n) (j k : Fin m) :
    (oneEach i j).getD (n+k) false = decide (k = j) := by
  unfold oneEach
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD, k.isLt]

theorem matching_upper {n m : ℕ} (A : Fin n → Fin m → Bool) (e : Fin n ≃ Fin m)
    (he : ∀ i j, A i j = decide (e i = j)) :
    ∃ C : Circuit, FanInTwo C ∧ Represents A C ∧ C.size ≤ n + m - 1 := by
  let pairs := (List.finRange n).map (fun k => (k.val,n+(e k).val))
  refine ⟨matching (n+m) pairs, matching_fanIn _ _, ?_, ?_⟩
  · intro i j
    rw [he, ← oneEach_length i j, matching_eval]
    · apply Bool.eq_iff_iff.mpr
      simp only [pairs, List.any_map, List.any_eq_true, List.mem_finRange, true_and,
        Function.comp_apply, Bool.and_eq_true, oneEach_left, oneEach_right, decide_eq_true_eq]
      exact ⟨fun ⟨k,hk,h⟩ => hk ▸ h, fun h => ⟨i,rfl,h⟩⟩
    · intro p hp
      obtain ⟨k, -, rfl⟩ := List.mem_map.mp hp
      rw [oneEach_length]
      have hi := k.isLt
      have hj := (e k).isLt
      omega
  · rw [matching_size]
    have q := Fintype.card_congr e
    simp only [Fintype.card_fin] at q
    simp [pairs, q]
    omega

end PEqualNP.Outside.L_meta_25902_aux

namespace PEqualNP.Outside.L_meta_25902_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open Network

def baseInput (n : ℕ) {m : ℕ} (omitted j : Fin m) (v : ℕ) : Bool :=
  decide (j ≠ omitted ∧ v = n + j.val)

def addRow {n m : ℕ} (omitted j : Fin m) (i : Fin n) (v : ℕ) : Bool :=
  baseInput n omitted j v || decide (v = i.val)

theorem fork_compare {n m : ℕ} {C : Circuit} {L : Finset ℕ}
    {A : Fin n → Fin m → Bool} {f : ℕ} {i₀ i : Fin n} {j₀ : Fin m}
    (cl : closed (n+m) C L) (fan : FanInTwo C)
    (livef : live (n+m) L f) (liver : live (n+m) L C.output)
    (out : C.output = f ∨ ¬ reaches (n+m) C L C.output f)
    (inside : reaches (n+m) C L i.val f)
    (single : ∀ a, a ≠ f → ∀ b c, edgeTo (n+m) C L a b → edgeTo (n+m) C L a c → b = c)
    (few : ∀ j k : Fin m, j ≠ j₀ → k ≠ j₀ →
      ¬ reaches (n+m) C L (n+j.val) f → ¬ reaches (n+m) C L (n+k.val) f → j = k)
    (repr0 : ∀ j : Fin m, value (n+m) C (baseInput n j₀ j) (fun _ => none) C.output = A i₀ j)
    (repr1 : ∀ j : Fin m, value (n+m) C (addRow j₀ j i) (fun _ => none) C.output = A i j) :
    (∀ j, A i₀ j = true → A i j = true) ∨ (∀ j, A i j = true → A i₀ j = true) := by
  classical
  let exterior (j : Fin m) := j ≠ j₀ ∧ ¬ reaches (n+m) C L (n+j.val) f
  obtain ⟨port, spec⟩ : ∃ port : Option (Fin m), ∀ j, port = some j ↔ exterior j := by
    by_cases h : ∃ j, exterior j
    · obtain ⟨q, hq⟩ := h
      refine ⟨some q, fun j => ⟨fun h => Option.some.inj h ▸ hq, fun hj => ?_⟩⟩
      exact congrArg some (few q j hq.1 hj.1 hq.2 hj.2)
    · refine ⟨none, fun j => ⟨?_, fun hj => (h ⟨j,hj⟩).elim⟩⟩
      intro h'
      cases h'
  let signal (b : Bool) (v : ℕ) : Bool :=
    b && decide (∃ j : Fin m, port = some j ∧ v = n+j.val)
  let select (j : Fin m) : Bool := decide (port = some j)
  let H (z b : Bool) := value (n+m) C (signal b) (relay f z) C.output
  have uq (a j k) (hne : a ≠ f) (hj : j ∈ L) (hk : k ∈ L)
      (ha : before C (n+m) j a) (hb : before C (n+m) k a) : j = k :=
    Nat.add_left_cancel (single a hne _ _ ⟨j,hj,rfl,ha⟩ ⟨k,hk,rfl,hb⟩)
  have hH : (∀ z, implication (H z false) (H z true)) ∨
      (∀ z, implication (H z true) (H z false)) := by
    cases hp : port with
    | none =>
      left
      intro z
      have e : signal false = signal true := by funext v; simp [signal,hp]
      unfold implication H
      rw [e]
      exact id
    | some q =>
      have hq : exterior q := (spec q).mp hp
      have qlt : n+q.val < n+m := by have := q.isLt; omega
      obtain ⟨s, hs⟩ := Unate.relay_unate cl fan qlt uq hq.2 liver
      have change : Unate.Changes (n+m) (n+q.val) none (signal false) (signal true) := by
        refine ⟨?_, ?_, ?_⟩
        · intro w _ hne
          simp [signal,hp,hne]
        · intro _ e
          cases e
        · simp [signal]
      cases s
      · exact Or.inr (fun z => hs z _ _ change)
      · exact Or.inl (fun z => hs z _ _ change)
  have off0 (j : Fin m) (v : ℕ) (_ : v < n+m)
      (away : ¬ reaches (n+m) C L v f) :
      baseInput n j₀ j v = signal (select j) v := by
    apply Bool.eq_iff_iff.mpr
    simp only [baseInput, signal, select, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨hj,rfl⟩
      have pj := (spec j).mpr ⟨hj,away⟩
      exact ⟨pj,j,pj,rfl⟩
    · rintro ⟨pj,q,pq,rfl⟩
      have e : q=j := Option.some.inj (pq.symm.trans pj)
      subst q
      exact ⟨((spec j).mp pj).1,rfl⟩
  have off1 (j : Fin m) (v : ℕ) (hv : v < n+m)
      (away : ¬ reaches (n+m) C L v f) :
      addRow j₀ j i v = signal (select j) v := by
    have ne : v ≠ i.val := fun e => away (e ▸ inside)
    simpa [addRow,ne] using off0 j v hv away
  let inner0 (j : Fin m) := value (n+m) C (baseInput n j₀ j) (fun _ => none) f
  let inner1 (j : Fin m) := value (n+m) C (addRow j₀ j i) (fun _ => none) f
  have ilt : i.val < n+m := by have := i.isLt; omega
  obtain ⟨sign, hs⟩ := Unate.inner_unate cl fan ilt uq livef
  have hchange (j : Fin m) : Unate.Changes (n+m) i.val none (baseInput n j₀ j) (addRow j₀ j i) := by
    refine ⟨?_, ?_, ?_⟩
    · intro w _ hw
      simp [addRow,hw]
    · intro w e
      cases e
    · simp [addRow]
  have order (j : Fin m) := hs _ _ (hchange j)
  have bridge0 (j : Fin m) : A i₀ j = H (inner0 j) (select j) :=
    (repr0 j).symm.trans ((replace_signal cl _ f C.output liver).trans
      (cut_agree cl f single _ _ _ (off0 j) _ liver out))
  have bridge1 (j : Fin m) : A i j = H (inner1 j) (select j) :=
    (repr1 j).symm.trans ((replace_signal cl _ f C.output liver).trans
      (cut_agree cl f single _ _ _ (off1 j) _ liver out))
  cases sign
  · rcases readout_rows_comparable H hH inner1 inner0 select (fun j => order j) with hh | hh
    · exact Or.inr (fun j => by rw [bridge1 j, bridge0 j]; exact hh j)
    · exact Or.inl (fun j => by rw [bridge0 j, bridge1 j]; exact hh j)
  · rcases readout_rows_comparable H hH inner0 inner1 select (fun j => order j) with hh | hh
    · exact Or.inl (fun j => by rw [bridge0 j, bridge1 j]; exact hh j)
    · exact Or.inr (fun j => by rw [bridge1 j, bridge0 j]; exact hh j)

end PEqualNP.Outside.L_meta_25902_aux

namespace PEqualNP.Outside.L_meta_25902_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def RejectCollision {n m : ℕ} (A : Fin n → Fin m → Bool) : Prop :=
  3 ≤ n → 3 ≤ m →
  (∀ i k l, k ≠ i → l ≠ i → comparable A i k → comparable A i l → k = l) →
  (∀ j k l, k ≠ j → l ≠ j → comparable (fun j i => A i j) j k →
    comparable (fun j i => A i j) j l → k = l) →
  ∀ (C : Circuit), FanInTwo C → Represents A C →
  ∀ (L : Finset ℕ), closed (n+m) C L →
  ∀ r : ℕ, r ∈ L → C.output = n+m+r →
  (∀ i ∈ L, i ≠ r → ∃ j ∈ L, before C (n+m) j (n+m+i)) →
  (activeNot C L).card = 1 →
  ∀ f : ℕ,
  (∀ a j k, a ≠ f → j ∈ L → k ∈ L → before C (n+m) j a → before C (n+m) k a → j = k) →
  (∃ j ∈ L, before C (n+m) j f) →
  (missingRows n m C L).card = 1 → (missingCols n m C L).card = 1 → False

theorem tight_equals_mono {n m : ℕ} (A : Fin n → Fin m → Bool)
    (hn : 3 ≤ n) (hm : 3 ≤ m)
    (hi : Function.Injective A) (hj : Function.Injective (fun j i => A i j))
    (sr : ∀ i k l, k ≠ i → l ≠ i → comparable A i k → comparable A i l → k = l)
    (sc : ∀ j k l, k ≠ j → l ≠ j → comparable (fun j i => A i j) j k →
      comparable (fun j i => A i j) j l → k = l)
    (reject_collision : RejectCollision A)
    (C : Circuit) (fan : FanInTwo C) (repr : Represents A C)
    (small : C.size ≤ n+m-1) :
    ∃ D : Circuit, Monotone2 D ∧ Represents A D ∧ D.size = C.size := by
  let E := Network.trim C
  have eSize : E.size = C.size := by simp [E, Network.trim, Circuit.size]
  have eSmall : E.size ≤ n+m-1 := eSize ▸ small
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
    · obtain ⟨row1,col1,not1,_,_,slots1⟩ :=
        collision_counts hr hL hnext eFan (Network.trim_unary C) eSmall hrows hcols
          (Nat.pos_of_ne_zero no) single
      obtain ⟨j,k,f,hj,hk,hjk,hjf,hkf⟩ := collision_exists single
      have uq (a p q : ℕ) (ha : a ≠ f) (hp : p ∈ L) (hq : q ∈ L)
          (h1 : before E (n+m) p a) (h2 : before E (n+m) q a) : p = q := by
        by_contra hn
        exact ha (unique_collision slots1 hj hk hjk hjf hkf hp hq hn h1 h2).1
      exact reject_collision hn hm sr sc E eFan eRepr L hL r hr eout hnext not1 f uq
        ⟨j,hj,hjf⟩ row1 col1

end PEqualNP.Outside.L_meta_25902_aux


namespace PEqualNP.Outside.L_meta_25902_aux
namespace CloseFork

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover
open Network

def column {n m : ℕ} (c₀ j : Fin m) (w : ℕ) : Bool :=
  decide (j ≠ c₀ ∧ w = n+j.val)

def inserted {n m : ℕ} (c₀ : Fin m) (i : Fin n) (j : Fin m) (w : ℕ) : Bool :=
  column (n := n) c₀ j w || decide (w = i.val)

theorem pair_eval {n m : ℕ} {A : Fin n → Fin m → Bool} {C : Circuit}
    (rep : Represents A C) (i : Fin n) (j : Fin m) :
    value (n+m) C (fun w => decide (w = i.val ∨ w = n+j.val))
      (fun _ => none) C.output = A i j := by
  have eq : (fun w => (oneEach i j).getD w false) =
      (fun w => decide (w = i.val ∨ w = n+j.val)) := funext (each_value i j)
  rw [← eq, val_original (n+m) C (oneEach i j) (by simp [oneEach])]
  exact rep i j

theorem erased_eval {n m : ℕ} {A : Fin n → Fin m → Bool} {C : Circuit} {L : Finset ℕ}
    (rep : Represents A C) (cl : closed (n+m) C L)
    (liveRoot : live (n+m) L C.output) (r₀ i : Fin n) (c₀ : Fin m)
    (absR : ¬ reaches (n+m) C L r₀.val C.output)
    (absC : ¬ reaches (n+m) C L (n+c₀.val) C.output) :
    (∀ j, value (n+m) C (column (n := n) c₀ j) (fun _ => none) C.output = A r₀ j) ∧
    (∀ j, value (n+m) C (inserted c₀ i j) (fun _ => none) C.output = A i j) := by
  constructor
  · intro j
    rw [← pair_eval rep r₀ j]
    apply value_agree cl C.output liveRoot
    · intro w _ p
      have wr : w ≠ r₀.val := fun e => absR (e ▸ p)
      by_cases eq : j = c₀
      · subst j
        have wc : w ≠ n+c₀.val := fun e => absC (e ▸ p)
        simp [column,wr,wc]
      · simp [column,wr,eq]
    · exact fun _ _ => rfl
  · intro j
    rw [← pair_eval rep i j]
    apply value_agree cl C.output liveRoot
    · intro w _ p
      apply Bool.eq_iff_iff.mpr
      by_cases eq : j = c₀
      · subst j
        have wc : w ≠ n+c₀.val := fun e => absC (e ▸ p)
        simp [inserted,column,wc]
      · simp [inserted,column,eq, Bool.or_eq_true,or_comm]
    · exact fun _ _ => rfl

theorem reject_collision {n m : ℕ} (A : Fin n → Fin m → Bool) : RejectCollision A := by
  classical
  intro hn hm sr sc C fan rep L cl root hr out next _ f unique successor hRows hCols
  let N := n + m
  obtain ⟨r₀, hr₀⟩ := Finset.card_eq_one.mp hRows
  obtain ⟨c₀, hc₀⟩ := Finset.card_eq_one.mp hCols
  have rawR : r₀.val ∉ used N C L :=
    (Finset.mem_filter.mp (show r₀ ∈ missingRows n m C L by rw [hr₀]; simp)).2
  have rawC : n+c₀.val ∉ used N C L :=
    (Finset.mem_filter.mp (show c₀ ∈ missingCols n m C L by rw [hc₀]; simp)).2
  have hrLow := r₀.isLt
  have hcLow := c₀.isLt
  have absR := Unate.not_path_unused rawR (by omega : r₀.val ≠ C.output)
  have absC := Unate.not_path_unused rawC (by omega : n+c₀.val ≠ C.output)
  have liveRoot : live N L C.output := .inr ⟨root,hr,out⟩
  have one (a j k : ℕ) (dis : some f ≠ some a) (hj : j ∈ L) (hk : k ∈ L)
      (ha : before C N j a) (hb : before C N k a) : j = k := by
    apply unique a j k _ hj hk ha hb
    intro eq
    exact dis (congrArg some eq.symm)
  have byRow (i : Fin n) (away : ¬ reaches N C L i.val f) : comparable A r₀ i := by
    have hi := i.isLt
    apply Unate.omitted_row_comparable rep cl liveRoot absR
    exact Unate.original_unate (fork := some f) cl fan (by omega) one
      (fun t eq => Option.some.inj eq ▸ away) liveRoot
  have byCol (j : Fin m) (away : ¬ reaches N C L (n+j.val) f) :
      comparable (fun j i => A i j) c₀ j := by
    have hj := j.isLt
    apply Unate.omitted_col_comparable rep cl liveRoot absC
    exact Unate.original_unate (fork := some f) cl fan (by omega) one
      (fun t eq => Option.some.inj eq ▸ away) liveRoot
  obtain ⟨i, _, conflict⟩ := incomparable_partner A (by simpa using hn) sr r₀
  have iInside : reaches N C L i.val f := by
    by_contra away
    exact conflict (byRow i away)
  have few (j k : Fin m) (hj : j ≠ c₀) (hk : k ≠ c₀)
      (offj : ¬ reaches N C L (n+j.val) f) (offk : ¬ reaches N C L (n+k.val) f) : j = k :=
    sc c₀ j k hj hk (byCol j offj) (byCol k offk)
  obtain ⟨j,hj,hbefore⟩ := successor
  have flive : live N L f := prev_live cl hj hbefore
  have f_lt : f < C.output := by
    have p := every_gate_reaches_root cl next j hj
    exact hbefore.2.trans_le (out ▸ reachIncreases p)
  have outerRoot : C.output = f ∨ ¬ reaches N C L C.output f :=
    .inr (fun p => (Nat.not_le_of_gt f_lt) (reachIncreases p))
  have he : ∀ a, a ≠ f → ∀ b c, edgeTo N C L a b → edgeTo N C L a c → b = c := by
    rintro a ha _ _ ⟨j,hj,rfl,hw⟩ ⟨k,hk,rfl,hv⟩
    rw [unique a j k ha hj hk hw hv]
  obtain ⟨eq0, eq1⟩ := erased_eval rep cl liveRoot r₀ i c₀ absR absC
  exact conflict (fork_compare cl fan flive liveRoot outerRoot iInside he few eq0 eq1)

end CloseFork
end PEqualNP.Outside.L_meta_25902_aux

theorem PEqualNP.Outside.L_meta_25902 : (∀ (n m : Nat) (A : Fin n → Fin m → Bool), 3 ≤ n → 3 ≤ m →
  let rowLE := fun i k : Fin n => ∀ j, A i j = true → A k j = true
  let colLE := fun j l : Fin m => ∀ i, A i j = true → A i l = true
  let rc := fun i k : Fin n => rowLE i k ∨ rowLE k i
  let cc := fun j l : Fin m => colLE j l ∨ colLE l j
  Function.Injective A → Function.Injective (fun j i => A i j) →
  (∀ i k l, k ≠ i → l ≠ i → rc i k → rc i l → k = l) →
  (∀ j k l, k ≠ j → l ≠ j → cc j k → cc j l → k = l) →
  (∀ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C →
    n + m - 1 ≤ C.size) ∧
  ((∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.Represents.Represents A C ∧
    C.size ≤ n + m - 1) ↔ ∃ e : Fin n ≃ Fin m, ∀ i j, A i j = decide (e i = j))) := by
  intro n m A hn hm
  dsimp only
  intro hi hj sr sc
  have tight (C : PEqualNP.CircuitLowerBounds.Circuit)
      (fan : PEqualNP.MetaComplexity.FanInTwo C) (repr : PEqualNP.Represents.Represents A C)
      (small : C.size ≤ n+m-1) :
      n+m-1 ≤ C.size ∧ ∃ e : Fin n ≃ Fin m, ∀ i j, A i j = decide (e i = j) := by
    obtain ⟨D,dmono,drepr,dsize⟩ := PEqualNP.Outside.L_meta_25902_aux.tight_equals_mono A hn hm hi hj sr sc
      (PEqualNP.Outside.L_meta_25902_aux.CloseFork.reject_collision A) C fan repr small
    rw [← dsize] at small ⊢
    exact PEqualNP.Outside.L_meta_25902_aux.monotone_tight A hn hm hi hj sr sc D dmono drepr small
  refine ⟨?_,?_⟩
  · intro C fan repr
    by_cases small : C.size ≤ n+m-1
    · exact (tight C fan repr small).1
    · omega
  · constructor
    · rintro ⟨C,fan,repr,small⟩
      exact (tight C fan repr small).2
    · rintro ⟨e,he⟩
      exact PEqualNP.Outside.L_meta_25902_aux.matching_upper A e he
