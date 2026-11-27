import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25446_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem len (gs : List Gate) (x : List Bool) : (gs.foldl stp x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp [stp]; omega

theorem getD_snoc (l : List Bool) (b : Bool) (w : ℕ) :
    (l ++ [b]).getD w false = if w < l.length then l.getD w false else if w = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp

theorem getD_ge (W : List Bool) (i : ℕ) (h : W.length ≤ i) : W.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem pre (gs : List Gate) : ∀ (x : List Bool) (w : ℕ), w < x.length →
    (gs.foldl stp x).getD w false = x.getD w false := by
  induction gs with
  | nil => intro x w _; rfl
  | cons g gs ih =>
    intro x w h
    rw [List.foldl_cons, ih _ _ (by simp [stp]; omega), stp, getD_snoc, ite_eq_left h]

lemma foldl_char (gs : List Gate) (w : List Bool) :
    ∀ j, j < gs.length → (gs.foldl stp w).getD (w.length + j) false =
      (gs.getD j ⟨GateOp.or, []⟩).op.eval ((gs.getD j ⟨GateOp.or, []⟩).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stp w).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen := len gs w
    simp only [List.length_append, List.length_singleton] at hj
    have key : ∀ i, i < w.length + gs.length →
        (stp (gs.foldl stp w) g).getD i false = (gs.foldl stp w).getD i false := by
      intro i hi
      simp only [stp, List.getD_eq_getElem?_getD]
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
      have e2 : (stp (gs.foldl stp w) g).getD (w.length + gs.length) false =
          g.op.eval (g.inputs.map fun i => (gs.foldl stp w).getD i false) := by
        simp only [stp, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i hi]
      · simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by omega)]
        rfl



def signal (C : Circuit) {N : ℕ} (w : ℕ) (p : Fin N) : Bool :=
  (C.wires (List.ofFn fun q : Fin N => decide (q = p))).getD w false

def support (C : Circuit) (N w : ℕ) : Finset (Fin N) :=
  Finset.univ.filter fun p => signal C w p = true

theorem mem_support {C : Circuit} {N w : ℕ} {p : Fin N} :
    p ∈ support C N w ↔ signal C w p = true := by simp [support]

def big (C : Circuit) (N w : ℕ) : Prop := 1 < (support C N w).card

def before (C : Circuit) (N j w : ℕ) : Prop :=
  w ∈ (gateAt C j).inputs ∧ w < N + j

theorem signal_input (C : Circuit) {N w : ℕ} (p : Fin N) (hw : w < N) :
    signal C w p = decide ((⟨w, hw⟩ : Fin N) = p) := by
  unfold signal
  change ((C.gates.foldl stp (List.ofFn _)).getD w false) = _
  rw [pre _ _ _ (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

theorem big_gate (C : Circuit) {N w : ℕ} (hb : big C N w) :
    N ≤ w ∧ w < N + C.gates.length := by
  by_cases hi : w < N
  · have eq : support C N w = {⟨w, hi⟩} := by
      ext p
      rw [mem_support, signal_input C p hi]
      simp [eq_comm]
    simp [big, eq] at hb
  refine ⟨by omega, ?_⟩
  by_contra! ho
  have eq : support C N w = ∅ := by
    ext p
    rw [mem_support]
    have hz : signal C w p = false := by
      unfold signal
      change ((C.gates.foldl stp (List.ofFn _)).getD w false) = false
      apply getD_ge
      simpa [len] using ho
    simp [hz]
  simp [big, eq] at hb

theorem wires_as_fold (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stp x := rfl

theorem signal_gate (C : Circuit) {N j : ℕ} (hj : j < C.gates.length) (p : Fin N) :
    signal C (N + j) p = (gateAt C j).op.eval
      ((gateAt C j).inputs.map fun w => if w < N + j then signal C w p else false) := by
  have h := foldl_char C.gates (List.ofFn fun q : Fin N => decide (q = p)) j hj
  simpa only [signal, wires_as_fold, gateAt, List.length_ofFn] using h

theorem signal_agrees (C : Circuit) (hC : Monotone2 C) {N j : ℕ} (hj : j < C.gates.length)
    {p q : Fin N}
    (h : ∀ w, before C N j w → signal C w p = true → signal C w q = true) :
    signal C (N + j) p = true → signal C (N + j) q = true := by
  have hg : gateAt C j ∈ C.gates := by
    rw [gateAt, List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem _
  have hOp := (hC _ hg).1
  rw [signal_gate C hj p, signal_gate C hj q]
  have on (w : ℕ) (hw : w ∈ (gateAt C j).inputs) :
      (if w < N + j then signal C w p else false) = true →
        (if w < N + j then signal C w q else false) = true := by
    split_ifs with hi
    · exact h w ⟨hw, hi⟩
    · simp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hOp
  rcases hOp with ho | ho
  · simp only [ho, GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
    intro hp a ha
    obtain ⟨w, hw, rfl⟩ := ha
    exact on w hw (hp _ ⟨w, hw, rfl⟩)
  · simp only [ho, GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨a, ⟨w, hw, rfl⟩, ha⟩
    exact ⟨_, ⟨w, hw, rfl⟩, on w hw ha⟩

def closed (C : Circuit) (N : ℕ) (L : Finset ℕ) : Prop :=
  (∀ j ∈ L, j < C.gates.length ∧ big C N (N + j)) ∧
    (∀ j ∈ L, ∀ i, before C N j (N + i) → big C N (N + i) → i ∈ L)

def singletonRead (C : Circuit) {N : ℕ} (p : Fin N) (j : ℕ) : Prop :=
  ∃ w, before C N j w ∧ support C N w = {p}

theorem propagate (C : Circuit) (hC : Monotone2 C) {N : ℕ} {L : Finset ℕ}
    (hL : closed C N L) {p q : Fin N}
    (hpq : ∀ j ∈ L, singletonRead C p j → signal C (N + j) q = true) :
    ∀ j ∈ L, signal C (N + j) p = true → signal C (N + j) q = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj ht
    by_cases hs : singletonRead C p j
    · exact hpq j hj hs
    refine signal_agrees C hC (hL.1 j hj).1 ?_ ht
    intro w hw hp
    have hp' := mem_support.mpr hp
    have hbig : big C N w := by
      by_contra h
      have hcard : (support C N w).card ≤ 1 := Nat.le_of_not_gt h
      have hsub : support C N w ⊆ {p} :=
        fun a ha => Finset.mem_singleton.mpr (Finset.card_le_one_iff.mp hcard ha hp')
      have he : support C N w = {p} :=
        Finset.Subset.antisymm hsub (Finset.singleton_subset_iff.mpr hp')
      exact hs ⟨w, hw, he⟩
    have hn := (big_gate C hbig).1
    let i := w - N
    have he : N + i = w := by dsimp [i]; omega
    have hi : i < j := by have h := hw.2; omega
    rw [← he] at hw hp hbig ⊢
    exact ih i hi (hL.2 j hj i hw hbig) hp

def Separates (C : Circuit) (N : ℕ) (L : Finset ℕ) : Prop :=
  ∀ p q : Fin N, p ≠ q → ∃ j ∈ L, signal C (N + j) p = true ∧ signal C (N + j) q = false

theorem two_reads (C : Circuit) (hC : Monotone2 C) {N : ℕ} (hN : 2 ≤ N)
    {L : Finset ℕ} (hL : closed C N L) (hsep : Separates C N L) (p : Fin N) :
    ∃ j ∈ L, ∃ j' ∈ L, j ≠ j' ∧ singletonRead C p j ∧ singletonRead C p j' := by
  classical
  by_contra hn
  have uniq : ∀ j ∈ L, ∀ j' ∈ L, singletonRead C p j → singletonRead C p j' → j = j' := by
    intro j hj j' hj' h1 h2
    by_contra h
    exact hn ⟨j, hj, j', hj', h, h1, h2⟩
  suffices ∃ q : Fin N, p ≠ q ∧ ∀ j ∈ L, singletonRead C p j → signal C (N + j) q = true by
    obtain ⟨q, hq, hab⟩ := this
    obtain ⟨j, hj, ht, hf⟩ := hsep p q hq
    have := propagate C hC hL hab j hj ht
    rw [hf] at this
    contradiction
  by_cases h : ∃ j ∈ L, singletonRead C p j
  · obtain ⟨j, hj, hs⟩ := h
    obtain ⟨a, ha, b, hb, hne⟩ := Finset.one_lt_card.mp (hL.1 j hj).2
    have hout : ∃ q, p ≠ q ∧ q ∈ support C N (N + j) := by
      by_cases hpa : p = a
      · exact ⟨b, hpa.symm ▸ hne, hb⟩
      · exact ⟨a, hpa, ha⟩
    obtain ⟨q, hpq, hq⟩ := hout
    exact ⟨q, hpq, fun j' hj' hs' => uniq j hj j' hj' hs hs' ▸ mem_support.mp hq⟩
  · let q : Fin N := if p.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
    have hpq : p ≠ q := by
      simp only [q]
      split_ifs with hzero
      · intro e; have := congrArg Fin.val e; simp at this; omega
      · intro e; have := congrArg Fin.val e; simp at this; omega
    exact ⟨q, hpq, fun j hj hs => (h ⟨j, hj, hs⟩).elim⟩

theorem closed_min (C : Circuit) (N : ℕ) (O : Finset ℕ)
    (hO : ∀ j ∈ O, j < C.gates.length ∧ big C N (N + j)) :
    ∃ L : Finset ℕ, O ⊆ L ∧ closed C N L ∧
      ∀ i ∈ L, i ∉ O → ∃ j ∈ L, before C N j (N + i) := by
  classical
  let A := (Finset.range C.gates.length).filter fun j => big C N (N + j)
  have ha : O ⊆ A := fun j hj => Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hO j hj).1, (hO j hj).2⟩
  have hc : closed C N A := by
    constructor
    · intro j hj
      exact ⟨Finset.mem_range.mp (Finset.mem_filter.mp hj).1, (Finset.mem_filter.mp hj).2⟩
    · intro j hj i hi hb
      have hlt := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
      have hs := hi.2
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hb⟩
  let candidates := A.powerset.filter fun L => O ⊆ L ∧ closed C N L
  have hA : A ∈ candidates := Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.Subset.refl _), ha, hc⟩
  obtain ⟨L, hL, hmin⟩ := candidates.exists_min_image Finset.card ⟨A, hA⟩
  obtain ⟨hsub, hOL, hclose⟩ := Finset.mem_filter.mp hL
  refine ⟨L, hOL, hclose, ?_⟩
  intro i hi hio
  by_contra hn
  have hs : L.erase i ∈ candidates := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ?_, ?_⟩
    · exact (Finset.erase_subset _ _).trans (Finset.mem_powerset.mp hsub)
    · intro j hj
      exact Finset.mem_erase.mpr ⟨fun e => hio (e ▸ hj), hOL hj⟩
    · constructor
      · intro j hj
        exact hclose.1 j (Finset.mem_of_mem_erase hj)
      · intro j hj k hkj hbig
        have hj' := Finset.mem_of_mem_erase hj
        refine Finset.mem_erase.mpr ⟨?_, hclose.2 j hj' k hkj hbig⟩
        rintro rfl
        exact hn ⟨j, hj', hkj⟩
  have h := hmin _ hs
  have hpos := Finset.card_pos.mpr ⟨i, hi⟩
  rw [Finset.card_erase_of_mem hi] at h
  omega


def inputSlots (C : Circuit) (j : ℕ) : Finset (ℕ × ℕ) :=
  (gateAt C j).inputs.toFinset.image (Prod.mk j)

def slots (C : Circuit) (L : Finset ℕ) : Finset (ℕ × ℕ) := L.biUnion (inputSlots C)

theorem chosen_slot {C : Circuit} {N : ℕ} {L : Finset ℕ} {j w : ℕ}
    (hj : j ∈ L) (hw : before C N j w) : (j,w) ∈ slots C L :=
  Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_image.mpr ⟨w, List.mem_toFinset.mpr hw.1, rfl⟩⟩

theorem slots_le (C : Circuit) (hC : Monotone2 C) {N : ℕ} {L : Finset ℕ}
    (hL : closed C N L) : (slots C L).card ≤ 2 * L.card := by
  rw [Nat.mul_comm]
  apply Finset.card_biUnion_le_card_mul L (inputSlots C) 2
  intro j hj
  have hg : gateAt C j ∈ C.gates := by
    rw [gateAt, List.getD_eq_getElem _ _ (hL.1 j hj).1]
    exact List.getElem_mem _
  exact Finset.card_image_le.trans (List.toFinset_card_le _ |>.trans ((hC _ hg).2))

theorem singletonSlots (C : Circuit) (hC : Monotone2 C) {N : ℕ} (hN : 2 ≤ N)
    {L : Finset ℕ} (hL : closed C N L) (hsep : Separates C N L) :
    ∃ X ⊆ slots C L, X.card = 2 * N ∧
      ∀ s ∈ X, ∃ p : Fin N, support C N s.2 = {p} := by
  classical
  have picks (p : Fin N) : ∃ a b : ℕ × ℕ, a ≠ b ∧ a ∈ slots C L ∧ b ∈ slots C L ∧
      support C N a.2 = {p} ∧ support C N b.2 = {p} := by
    obtain ⟨j, hj, k, hk, hne, ⟨w, hw, hs⟩, ⟨v, hv, ht⟩⟩ := two_reads C hC hN hL hsep p
    exact ⟨(j,w), (k,v), fun e => hne (congrArg Prod.fst e), chosen_slot hj hw,
      chosen_slot hk hv, hs, ht⟩
  choose a b h using picks
  let pick : Fin N × Bool → ℕ × ℕ := fun z => if z.2 then a z.1 else b z.1
  have hp (z : Fin N × Bool) : pick z ∈ slots C L ∧ support C N (pick z).2 = {z.1} := by
    rcases z with ⟨p, t⟩
    rcases h p with ⟨_, ha, hb, ea, eb⟩
    cases t
    · exact ⟨hb, eb⟩
    · exact ⟨ha, ea⟩
  have inj : Function.Injective pick := by
    rintro ⟨p,t⟩ ⟨q,u⟩ he
    have e1 := (hp (p,t)).2
    rw [he, (hp (q,u)).2] at e1
    have eq : p = q := by simpa using e1.symm
    subst q
    cases t <;> cases u
    · rfl
    · exact False.elim ((h p).1 he.symm)
    · exact False.elim ((h p).1 he)
    · rfl
  refine ⟨Finset.univ.image pick, ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hw
    exact (hp z).1
  · rw [Finset.card_image_of_injective _ inj]
    simp [Fintype.card_prod, Nat.mul_comm]
  · intro w hw
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hw
    exact ⟨z.1, (hp z).2⟩

theorem internalSlots (C : Circuit) {N : ℕ} {L O : Finset ℕ} (hL : closed C N L)
    (huse : ∀ i ∈ L, i ∉ O → ∃ j ∈ L, before C N j (N + i)) :
    ∃ Y ⊆ slots C L, Y.card = (L \ O).card ∧
      ∀ s ∈ Y, big C N s.2 := by
  classical
  have ex (i : {i // i ∈ L \ O}) : ∃ j ∈ L, before C N j (N + i.val) :=
    huse i.val (Finset.mem_sdiff.mp i.property).1 (Finset.mem_sdiff.mp i.property).2
  choose consumer h using ex
  let pick (i : {i // i ∈ L \ O}) : ℕ × ℕ := (consumer i, N + i.val)
  refine ⟨(L \ O).attach.image pick, ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
    exact chosen_slot (h i).1 (h i).2
  · rw [Finset.card_image_of_injective]
    · exact Finset.card_attach
    · intro i j he
      apply Subtype.ext
      have h := congrArg Prod.snd he
      change N + i.val = N + j.val at h
      omega
  · intro w hw
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
    exact (hL.1 _ (Finset.mem_sdiff.mp i.property).1).2

theorem separate_size (C : Circuit) (hC : Monotone2 C) {N : ℕ} (hN : 2 ≤ N) (O : Finset ℕ)
    (hO : ∀ j ∈ O, j < C.gates.length ∧ big C N (N + j))
    (hsep : Separates C N O) : 2 * N ≤ C.size + O.card := by
  obtain ⟨L, hOL, hL, huse⟩ := closed_min C N O hO
  have hsepL : Separates C N L := by
    intro p q h
    obtain ⟨j,hj,hp,hq⟩ := hsep p q h
    exact ⟨j,hOL hj,hp,hq⟩
  obtain ⟨X, hX, hx, hsingle⟩ := singletonSlots C hC hN hL hsepL
  obtain ⟨Y, hY, hy, hbig⟩ := internalSlots C hL huse
  have hd : Disjoint X Y := by
    apply Finset.disjoint_left.mpr
    intro s hs ht
    obtain ⟨p,hp⟩ := hsingle s hs
    have hb := hbig s ht
    simp [big, hp] at hb
  have hXY : X ∪ Y ⊆ slots C L := Finset.union_subset hX hY
  have hc := (Finset.card_le_card hXY).trans (slots_le C hC hL)
  rw [Finset.card_union_of_disjoint hd, hx, hy, Finset.card_sdiff_of_subset hOL] at hc
  have hCL : L.card ≤ C.size := by
    change L.card ≤ C.gates.length
    rw [← Finset.card_range C.gates.length]
    exact Finset.card_le_card fun j hj => Finset.mem_range.mpr (hL.1 j hj).1
  have hOLc := Finset.card_le_card hOL
  omega

def bitValue {k : ℕ} (v : Fin k) (b : Bool) (p : Fin (2 ^ k)) : Bool :=
  if b then p.val.testBit v.val else !(p.val.testBit v.val)

theorem bit_diff {k : ℕ} (p q : Fin (2 ^ k)) (h : p ≠ q) :
    ∃ v : Fin k, ∃ b : Bool, bitValue v b p = true ∧ bitValue v b q = false := by
  have hDiff : ∃ v : Fin k, p.val.testBit v.val ≠ q.val.testBit v.val := by
    by_contra! he
    apply h
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < k
    · exact he ⟨i,hi⟩
    · have hpow := Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (show k ≤ i by omega)
      rw [Nat.testBit_lt_two_pow (p.isLt.trans_le hpow), Nat.testBit_lt_two_pow (q.isLt.trans_le hpow)]
  obtain ⟨v, hDiff⟩ := hDiff
  cases hp : p.val.testBit v.val <;> cases hq : q.val.testBit v.val <;> simp [hp,hq] at hDiff
  · exact ⟨v,false,by simp [bitValue,hp],by simp [bitValue,hq]⟩
  · exact ⟨v,true,by simp [bitValue,hp],by simp [bitValue,hq]⟩

theorem bit_support {k : ℕ} (hk : 2 ≤ k) (v : Fin k) (b : Bool) :
    ∃ p q : Fin (2 ^ k), p ≠ q ∧ bitValue v b p = true ∧ bitValue v b q = true := by
  let t : ℕ := if v.val = 0 then 1 else 0
  have htv : t ≠ v.val := by
    dsimp [t]
    split_ifs <;> omega
  have ht : t < k := by dsimp [t]; split_ifs <;> omega
  let a : ℕ := 2 ^ v.val
  let c : ℕ := 2 ^ t
  have ha : a < 2 ^ k := Nat.pow_lt_pow_right (by decide) v.isLt
  have hc : c < 2 ^ k := Nat.pow_lt_pow_right (by decide) ht
  have haz : a.testBit v.val = true := by simp [a, Nat.testBit_two_pow]
  have hcv : c.testBit v.val = false := by
    simp [c, Nat.testBit_two_pow, htv, Ne.symm htv]
  cases b
  · refine ⟨⟨0,Nat.two_pow_pos _⟩,⟨c,hc⟩,?_,by simp [bitValue],by simp [bitValue,hcv]⟩
    intro he
    have hn := congrArg Fin.val he
    change 0 = c at hn
    exact (Nat.ne_of_gt (Nat.two_pow_pos t)) hn.symm
  · have hl : a ||| c < 2 ^ k := Nat.or_lt_two_pow ha hc
    have hne : a ≠ a ||| c := by
      intro he
      have hb := congrArg (fun i : ℕ => i.testBit t) he
      simp [a, c,Nat.testBit_or,Nat.testBit_two_pow,htv,Ne.symm htv] at hb
    exact ⟨⟨a,ha⟩,⟨a ||| c,hl⟩, (fun e => hne (congrArg Fin.val e)),
      by simp [bitValue,haz], by simp [bitValue,Nat.testBit_or,haz]⟩

theorem encoding_lower (k : ℕ) (hk : 2 ≤ k) (C : Circuit) (hC : Monotone2 C)
    (henc : ∀ v : Fin k, ∀ b : Bool, ∃ w : ℕ, ∀ p : Fin (2 ^ k), signal C w p = bitValue v b p) :
    2 * 2 ^ k ≤ C.size + 2 * k := by
  classical
  let N : ℕ := 2 ^ k
  have ex (s : Fin k × Bool) : ∃ w : ℕ, ∀ p : Fin N, signal C w p = bitValue s.1 s.2 p :=
    henc s.1 s.2
  choose wit hwit using ex
  have hbig (s : Fin k × Bool) : big C N (wit s) := by
    obtain ⟨p,q,hne,hp,hq⟩ := bit_support hk s.1 s.2
    refine Finset.one_lt_card.mpr ⟨p, mem_support.mpr ?_, q, mem_support.mpr ?_, hne⟩
    · rw [hwit]; exact hp
    · rw [hwit]; exact hq
  let out : Fin k × Bool → ℕ := fun a => wit a - N
  let O : Finset ℕ := Finset.univ.image out
  have haddr (a : Fin k × Bool) : N + out a = wit a := by
    have h := (big_gate C (hbig a)).1
    dsimp [out]
    omega
  have hO : ∀ j ∈ O, j < C.gates.length ∧ big C N (N + j) := by
    intro j hj
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hj
    refine ⟨?_, by rw [haddr]; exact hbig a⟩
    have h := (big_gate C (hbig a)).2
    rw [← haddr] at h
    omega
  have hsep : Separates C N O := by
    intro p q hne
    obtain ⟨v,b,hp,hq⟩ := bit_diff p q hne
    refine ⟨out (v,b), Finset.mem_image.mpr ⟨(v,b), Finset.mem_univ _, rfl⟩, ?_, ?_⟩
    · rw [haddr, hwit]; exact hp
    · rw [haddr, hwit]; exact hq
  have hN : 2 ≤ N := Nat.pow_le_pow_right (show 0 < (2 : ℕ) by decide) (show 1 ≤ k by omega)
  have hcount := separate_size C hC hN O hO hsep
  have hOc : O.card ≤ 2 * k := by
    have h := Finset.card_image_le (s := (Finset.univ : Finset (Fin k × Bool))) (f := out)
    simpa [O,Fintype.card_prod,Nat.mul_comm] using h
  change 2 * N ≤ C.size + 2 * k
  omega

end PEqualNP.Outside.L_meta_25446_aux

open PEqualNP.Outside.L_meta_25446_aux PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_25446 : ∀ k : ℕ, 2 ≤ k → ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ v : Fin k, (∃ w : ℕ, ∀ p : Fin (2 ^ k), (C.wires (List.ofFn (fun q : Fin (2 ^ k) => decide (q = p)))).getD w false = Nat.testBit p.val v.val) ∧ (∃ w : ℕ, ∀ p : Fin (2 ^ k), (C.wires (List.ofFn (fun q : Fin (2 ^ k) => decide (q = p)))).getD w false = !(Nat.testBit p.val v.val))) → 2 * 2 ^ k ≤ C.size + 2 * k := by
  intro k hk C hC henc
  exact encoding_lower k hk C hC (fun v b => by
    cases b
    · exact (henc v).2
    · exact (henc v).1)
