import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1328

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.NotBracket
open Classical

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def wiresOf (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl stepWire x

lemma wires_eq_wiresOf (C : Circuit) (x : List Bool) : C.wires x = wiresOf C.gates x := rfl

lemma wiresOf_nil (x : List Bool) : wiresOf [] x = x := rfl

lemma wiresOf_append (gs1 gs2 : List Gate) (x : List Bool) :
    wiresOf (gs1 ++ gs2) x = wiresOf gs2 (wiresOf gs1 x) :=
  List.foldl_append

lemma wiresOf_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    wiresOf (gs ++ [g]) x = stepWire (wiresOf gs x) g := by
  rw [wiresOf_append]
  rfl

lemma wiresOf_length (gs : List Gate) (x : List Bool) :
    (wiresOf gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [wiresOf]
  | cons g gs ih =>
    change (wiresOf gs (stepWire x g)).length = x.length + (gs.length + 1)
    rw [ih]
    simp [stepWire]
    omega

lemma getD_append_left {α : Type*} (l1 l2 : List α) (i : Nat) (d : α) (hi : i < l1.length) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_right_eq {α : Type*} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  simp [List.getD_eq_getElem?_getD]

lemma wiresOf_getD_prefix (gs : List Gate) (x : List Bool) (u : Nat) (hu : u < x.length) :
    (wiresOf gs x).getD u false = x.getD u false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    have hlen : u < (stepWire x g).length := by
      simp [stepWire]
      omega
    change (wiresOf gs (stepWire x g)).getD u false = x.getD u false
    rw [ih (stepWire x g) hlen]
    exact getD_append_left x _ u false hu

lemma wiresOf_append_left (gs1 gs2 : List Gate) (x : List Bool) (u : Nat)
    (hu : u < x.length + gs1.length) :
    (wiresOf (gs1 ++ gs2) x).getD u false = (wiresOf gs1 x).getD u false := by
  rw [wiresOf_append]
  apply wiresOf_getD_prefix
  rw [wiresOf_length]
  exact hu

lemma wiresOf_take_getD (gs : List Gate) (x : List Bool) (m u : Nat)
    (hm : m ≤ gs.length) (hu : u < x.length + m) :
    (wiresOf gs x).getD u false = (wiresOf (gs.take m) x).getD u false := by
  have hsplit : gs = gs.take m ++ gs.drop m := (List.take_append_drop m gs).symm
  conv_lhs => rw [hsplit, wiresOf_append]
  apply wiresOf_getD_prefix
  rw [wiresOf_length, List.length_take]
  omega

lemma gateAt_eq_getElem (C : Circuit) (j : Nat) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  unfold gateAt
  exact List.getD_eq_getElem C.gates ⟨GateOp.or, []⟩ hj

lemma take_succ_eq_append (C : Circuit) (m : Nat) (hm : m < C.gates.length) :
    C.gates.take (m + 1) = C.gates.take m ++ [gateAt C m] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hm, Option.toList_some, gateAt_eq_getElem C m hm]

lemma wires_getD_gate (C : Circuit) (x : List Bool) (hRB : ReadsBack x.length C)
    (j : Nat) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => (C.wires x).getD i false) := by
  rw [wires_eq_wiresOf]
  have h1 : (wiresOf C.gates x).getD (x.length + j) false =
      (wiresOf (C.gates.take (j + 1)) x).getD (x.length + j) false :=
    wiresOf_take_getD C.gates x (j + 1) (x.length + j) (by omega) (by omega)
  rw [h1, take_succ_eq_append C j hj, wiresOf_snoc]
  unfold stepWire
  have hlen : (wiresOf (C.gates.take j) x).length = x.length + j := by
    rw [wiresOf_length, List.length_take]
    omega
  rw [← hlen, getD_append_right_eq]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hilt : i < x.length + j := hRB j hj i hi
  exact (wiresOf_take_getD C.gates x j i (by omega) hilt).symm

lemma notCount_le_size (C : Circuit) : notCount C ≤ C.size := by
  unfold notCount Circuit.size
  exact List.length_filter_le _ _

lemma notCount_append (gs1 gs2 : List Gate) (o : Nat) :
    notCount ⟨gs1 ++ gs2, o⟩ = notCount ⟨gs1, 0⟩ + notCount ⟨gs2, 0⟩ := by
  simp [notCount, List.filter_append]

lemma notCount_all_and (gs : List Gate) (h : ∀ g ∈ gs, g.op = GateOp.and) :
    notCount ⟨gs, 0⟩ = 0 := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have hg : g.op = GateOp.and := h g (by simp)
    have hgs : ∀ x ∈ gs, x.op = GateOp.and := fun x hx => h x (by simp [hx])
    have hrec := ih hgs
    unfold notCount at hrec ⊢
    simp [hg, hrec]

lemma notCount_snoc (gs : List Gate) (g : Gate) :
    notCount ⟨gs ++ [g], 0⟩ = notCount ⟨gs, 0⟩ + if g.op = GateOp.not then 1 else 0 := by
  unfold notCount
  simp only [List.filter_append, List.length_append, List.filter_cons, List.filter_nil]
  by_cases h : g.op = GateOp.not
  · simp [h]
  · simp [h]

lemma notCount_map_remap (gs : List Gate) (f : Nat → Nat) :
    notCount ⟨gs.map (fun g => ⟨g.op, g.inputs.map f⟩), 0⟩ = notCount ⟨gs, 0⟩ := by
  unfold notCount
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, List.filter_cons]
    by_cases h : g.op = GateOp.not
    · simp [h, ih]
    · simp [h, ih]

lemma filter_range_nonNot_add_not (gs : List Gate) :
    ((Finset.range gs.length).filter (fun j => (gateAt ⟨gs, 0⟩ j).op ≠ GateOp.not)).card +
      notCount ⟨gs, 0⟩ = gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [notCount]
  | append_singleton gs g ih =>
    rw [List.length_append, List.length_singleton, Finset.range_add_one]
    rw [Finset.filter_insert]
    have hmem : gs.length ∉ Finset.range gs.length := Finset.notMem_range_self
    have hcongr : (Finset.range gs.length).filter
        (fun j => (gateAt ⟨gs ++ [g], 0⟩ j).op ≠ GateOp.not) =
        (Finset.range gs.length).filter (fun j => (gateAt ⟨gs, 0⟩ j).op ≠ GateOp.not) := by
      apply Finset.filter_congr
      intro j hj
      have hjlt : j < gs.length := Finset.mem_range.mp hj
      have hg : gateAt ⟨gs ++ [g], 0⟩ j = gateAt ⟨gs, 0⟩ j := by
        unfold gateAt
        exact List.getD_append _ _ _ _ hjlt
      rw [hg]
    have hlast : gateAt ⟨gs ++ [g], 0⟩ gs.length = g := by
      unfold gateAt
      rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self]
      rfl
    rw [hcongr, hlast]
    have hnotmem : gs.length ∉ (Finset.range gs.length).filter
        (fun j => (gateAt ⟨gs, 0⟩ j).op ≠ GateOp.not) := by
      intro hc
      exact hmem (Finset.mem_filter.mp hc).1
    rw [notCount_snoc]
    by_cases h : g.op = GateOp.not
    · have hne : ¬ g.op ≠ GateOp.not := fun c => c h
      rw [if_neg hne, if_pos h]
      omega
    · have hne : g.op ≠ GateOp.not := h
      rw [if_pos hne, if_neg h, Finset.card_insert_of_notMem hnotmem]
      omega

lemma nonNot_card_eq (C : Circuit) :
    ((Finset.range C.size).filter (fun j => (gateAt C j).op ≠ GateOp.not)).card =
      C.size - notCount C := by
  have hsum := filter_range_nonNot_add_not C.gates
  change ((Finset.range C.gates.length).filter (fun j => (gateAt C j).op ≠ GateOp.not)).card =
    C.gates.length - notCount C
  have h1 : ((Finset.range C.gates.length).filter (fun j => (gateAt C j).op ≠ GateOp.not)).card =
      ((Finset.range C.gates.length).filter
        (fun j => (gateAt ⟨C.gates, 0⟩ j).op ≠ GateOp.not)).card := rfl
  have h2 : notCount C = notCount ⟨C.gates, 0⟩ := rfl
  omega

noncomputable def inp (d : Nat) (s : Finset (Fin d)) : List Bool :=
  List.ofFn (fun z : Fin d => decide (z ∈ s)) ++ [false, true]

lemma inp_eq_ofFn_any {d : Nat} (s : Finset (Fin d)) (inst : ∀ P : Prop, Decidable P) :
    List.ofFn (fun z : Fin d => @decide (z ∈ s) (inst _)) ++ [false, true] = inp d s := by
  unfold inp
  congr 1
  congr 1
  funext z
  simp only [decide_eq_decide]

lemma inp_length (d : Nat) (s : Finset (Fin d)) : (inp d s).length = d + 2 := by
  simp [inp]

lemma inp_getD_lt (d : Nat) (s : Finset (Fin d)) (u : Nat) (hu : u < d) :
    (inp d s).getD u false = decide (⟨u, hu⟩ ∈ s) := by
  have h1 : (inp d s).getD u false =
      (List.ofFn (fun z : Fin d => decide (z ∈ s))).getD u false := by
    unfold inp
    apply getD_append_left
    simp [hu]
  rw [h1]
  have hlen : u < (List.ofFn (fun z : Fin d => decide (z ∈ s))).length := by simp [hu]
  rw [List.getD_eq_getElem _ _ hlen]
  simp

lemma inp_getD_d (d : Nat) (s : Finset (Fin d)) : (inp d s).getD d false = false := by
  simp [inp, List.getD_eq_getElem?_getD]

lemma inp_getD_d1 (d : Nat) (s : Finset (Fin d)) : (inp d s).getD (d + 1) false = true := by
  simp [inp, List.getD_eq_getElem?_getD]

def Ordered {k d : Nat} (Z : Fin k → Bool → Finset (Fin d)) : Prop :=
  (∀ i, ¬ Z i false ⊆ Z i true) ∧ (∀ i, ¬ Z i true ⊆ Z i false) ∧
  (∀ i j, i < j → ∀ s r, Z i s ⊆ Z j r)

noncomputable def cutsFinset {k d : Nat} (Z : Fin k → Bool → Finset (Fin d)) : Finset (Fin k) :=
  Finset.univ.filter (fun j : Fin k => 0 < j.val ∧ ∃ a : Fin d, ∀ i r, (a ∈ Z i r ↔ j ≤ i))

noncomputable def missingFinset {k n m : Nat}
    (X : Fin k → Bool → Finset (Fin n)) (Y : Fin k → Bool → Finset (Fin m)) : Finset (Fin k) :=
  cutsFinset X \ cutsFinset Y

noncomputable def reportFn {k n m : Nat}
    (X : Fin k → Bool → Finset (Fin n)) (Y : Fin k → Bool → Finset (Fin m)) :
    Fin k → Bool → Fin k → Bool :=
  fun i _ j => decide (j ∈ missingFinset X Y ∧ j ≤ i)

def Fits {k d : Nat} (Z : Fin k → Bool → Finset (Fin d)) (t : Nat)
    (f : Fin k → Bool → Fin t → Bool) (p b : Nat) : Prop :=
  ∃ (C : Circuit) (tap : Fin t → Nat),
    FanInTwo C ∧ ReadsBack (d + 2) C ∧
    C.output < d + 2 + C.size ∧ (∀ a, tap a < d + 2 + C.size) ∧
    C.size - notCount C ≤ p ∧ notCount C ≤ b ∧
    ∀ i r a, (C.wires (inp d (Z i r))).getD (tap a) false = f i r a

lemma fits_mono {k d t : Nat} {Z : Fin k → Bool → Finset (Fin d)}
    {f : Fin k → Bool → Fin t → Bool} {p1 p2 b1 b2 : Nat}
    (hp : p1 ≤ p2) (hb : b1 ≤ b2) (h : Fits Z t f p1 b1) : Fits Z t f p2 b2 := by
  rcases h with ⟨C, tap, hF, hRB, hO, htap, hsz, hnc, heval⟩
  exact ⟨C, tap, hF, hRB, hO, htap, le_trans hsz hp, le_trans hnc hb, heval⟩

lemma exists_splitFalse {k d : Nat} {Z : Fin k → Bool → Finset (Fin d)}
    (hZ : Ordered Z) (j : Fin k) :
    ∃ a : Fin d, ∀ i r, a ∈ Z i r ↔ (i = j ∧ r = false) ∨ j < i := by
  have hnot := hZ.1 j
  rw [Finset.not_subset] at hnot
  rcases hnot with ⟨a, haF, haT⟩
  refine ⟨a, fun i r => ?_⟩
  constructor
  · intro hai
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · exact False.elim (haT (hZ.2.2 i j hlt r true hai))
    · cases r
      · exact Or.inl ⟨rfl, rfl⟩
      · exact False.elim (haT hai)
    · exact Or.inr hgt
  · rintro (⟨rfl, rfl⟩ | hgt)
    · exact haF
    · exact hZ.2.2 j i hgt false r haF

lemma exists_splitTrue {k d : Nat} {Z : Fin k → Bool → Finset (Fin d)}
    (hZ : Ordered Z) (j : Fin k) :
    ∃ a : Fin d, ∀ i r, a ∈ Z i r ↔ (i = j ∧ r = true) ∨ j < i := by
  have hnot := hZ.2.1 j
  rw [Finset.not_subset] at hnot
  rcases hnot with ⟨a, haT, haF⟩
  refine ⟨a, fun i r => ?_⟩
  constructor
  · intro hai
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · exact False.elim (haF (hZ.2.2 i j hlt r false hai))
    · cases r
      · exact False.elim (haF hai)
      · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr hgt
  · rintro (⟨rfl, rfl⟩ | hgt)
    · exact haT
    · exact hZ.2.2 j i hgt true r haT

lemma classify_col {k d : Nat} {Z : Fin k → Bool → Finset (Fin d)}
    (hZ : Ordered Z) (a : Fin d) :
    (∀ i r, a ∉ Z i r) ∨
    (∀ i r, a ∈ Z i r) ∨
    (∃ j : Fin k, ∀ i r, a ∈ Z i r ↔ (i = j ∧ r = false) ∨ j < i) ∨
    (∃ j : Fin k, ∀ i r, a ∈ Z i r ↔ (i = j ∧ r = true) ∨ j < i) ∨
    (∃ j : Fin k, 0 < j.val ∧ ∀ i r, a ∈ Z i r ↔ j ≤ i) := by
  let S : Finset (Fin k) := Finset.univ.filter (fun i : Fin k => a ∈ Z i false ∨ a ∈ Z i true)
  by_cases hS : S.Nonempty
  · let j := S.min' hS
    have hjS : j ∈ S := Finset.min'_mem S hS
    have hj_in : a ∈ Z j false ∨ a ∈ Z j true := (Finset.mem_filter.mp hjS).2
    have hlt_not : ∀ i : Fin k, i < j → ∀ r, a ∉ Z i r := by
      intro i hilt r hair
      have hiS : i ∈ S := by
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        cases r
        · exact Or.inl hair
        · exact Or.inr hair
      have hle : j ≤ i := Finset.min'_le S i hiS
      exact not_lt_of_ge hle hilt
    have hgt_in : ∀ i : Fin k, j < i → ∀ r, a ∈ Z i r := by
      intro i hjlt r
      rcases hj_in with hF | hT
      · exact hZ.2.2 j i hjlt false r hF
      · exact hZ.2.2 j i hjlt true r hT
    by_cases hF : a ∈ Z j false
    · by_cases hT : a ∈ Z j true
      · have hstep : ∀ i r, a ∈ Z i r ↔ j ≤ i := by
          intro i r
          constructor
          · intro hai
            by_contra hnotle
            exact hlt_not i (lt_of_not_ge hnotle) r hai
          · intro hle
            rcases eq_or_lt_of_le hle with rfl | hjlt
            · cases r
              · exact hF
              · exact hT
            · exact hgt_in i hjlt r
        by_cases hj0 : 0 < j.val
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨j, hj0, hstep⟩)))
        · refine Or.inr (Or.inl fun i r => (hstep i r).mpr ?_)
          change j.val ≤ i.val
          omega
      · refine Or.inr (Or.inr (Or.inl ⟨j, fun i r => ?_⟩))
        constructor
        · intro hai
          rcases lt_trichotomy i j with hilt | rfl | hjlt
          · exact False.elim (hlt_not i hilt r hai)
          · cases r
            · exact Or.inl ⟨rfl, rfl⟩
            · exact False.elim (hT hai)
          · exact Or.inr hjlt
        · rintro (⟨rfl, rfl⟩ | hjlt)
          · exact hF
          · exact hgt_in i hjlt r
    · have hT : a ∈ Z j true := by
        rcases hj_in with h | h
        · exact False.elim (hF h)
        · exact h
      refine Or.inr (Or.inr (Or.inr (Or.inl ⟨j, fun i r => ?_⟩)))
      constructor
      · intro hai
        rcases lt_trichotomy i j with hilt | rfl | hjlt
        · exact False.elim (hlt_not i hilt r hai)
        · cases r
          · exact False.elim (hF hai)
          · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr hjlt
      · rintro (⟨rfl, rfl⟩ | hjlt)
        · exact hT
        · exact hgt_in i hjlt r
  · rw [Finset.not_nonempty_iff_eq_empty] at hS
    refine Or.inl fun i r hair => ?_
    have hiS : i ∈ S := by
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      cases r
      · exact Or.inl hair
      · exact Or.inr hair
    rw [hS] at hiS
    exact Finset.notMem_empty i hiS

def prevFin {k : Nat} (j : Fin k) (hj : 0 < j.val) : Fin k :=
  ⟨j.val - 1, by omega⟩

lemma prevFin_lt_iff {k : Nat} (j : Fin k) (hj : 0 < j.val) (i : Fin k) :
    prevFin j hj < i ↔ j ≤ i := by
  change j.val - 1 < i.val ↔ j.val ≤ i.val
  omega

noncomputable def uSplit {k m : Nat} {Y : Fin k → Bool → Finset (Fin m)}
    (hY : Ordered Y) (j : Fin k) : Fin m :=
  Classical.choose (exists_splitFalse hY j)

lemma uSplit_spec {k m : Nat} {Y : Fin k → Bool → Finset (Fin m)}
    (hY : Ordered Y) (j : Fin k) :
    ∀ i r, uSplit hY j ∈ Y i r ↔ (i = j ∧ r = false) ∨ j < i :=
  Classical.choose_spec (exists_splitFalse hY j)

noncomputable def vSplit {k m : Nat} {Y : Fin k → Bool → Finset (Fin m)}
    (hY : Ordered Y) (j : Fin k) : Fin m :=
  Classical.choose (exists_splitTrue hY j)

lemma vSplit_spec {k m : Nat} {Y : Fin k → Bool → Finset (Fin m)}
    (hY : Ordered Y) (j : Fin k) :
    ∀ i r, vSplit hY j ∈ Y i r ↔ (i = j ∧ r = true) ∨ j < i :=
  Classical.choose_spec (exists_splitTrue hY j)

lemma split_and_eq_step {k m : Nat} {Y : Fin k → Bool → Finset (Fin m)}
    (hY : Ordered Y) (j : Fin k) (hj : 0 < j.val) (i : Fin k) (r : Bool) :
    (decide (uSplit hY (prevFin j hj) ∈ Y i r) &&
      decide (vSplit hY (prevFin j hj) ∈ Y i r)) = decide (j ≤ i) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq, uSplit_spec hY, vSplit_spec hY, prevFin_lt_iff]
  constructor
  · rintro ⟨⟨rfl, rfl⟩ | h1, ⟨_, h2⟩ | h2⟩
    · cases h2
    · exact h2
    · exact h1
    · exact h1
  · intro h
    exact ⟨Or.inr h, Or.inr h⟩

noncomputable def prefixGates {k m : Nat} {Y : Fin k → Bool → Finset (Fin m)}
    (hY : Ordered Y) (L : List (Fin k)) : List Gate :=
  L.map fun j =>
    if hj : 0 < j.val then
      ⟨GateOp.and, [(uSplit hY (prevFin j hj)).val, (vSplit hY (prevFin j hj)).val]⟩
    else
      ⟨GateOp.and, [m, m]⟩

lemma prefixGates_length {k m : Nat} {Y : Fin k → Bool → Finset (Fin m)}
    (hY : Ordered Y) (L : List (Fin k)) :
    (prefixGates hY L).length = L.length := by
  simp [prefixGates]

lemma prefixGates_all_and {k m : Nat} {Y : Fin k → Bool → Finset (Fin m)}
    (hY : Ordered Y) (L : List (Fin k)) :
    ∀ g ∈ prefixGates hY L, g.op = GateOp.and ∧ g.inputs.length = 2 ∧ ∀ u ∈ g.inputs, u < m + 2 := by
  intro g hg
  simp only [prefixGates, List.mem_map] at hg
  rcases hg with ⟨j, _, rfl⟩
  split_ifs with hj
  · refine ⟨rfl, rfl, ?_⟩
    intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    · exact Nat.lt_trans (uSplit hY (prevFin j hj)).isLt (by omega)
    · exact Nat.lt_trans (vSplit hY (prevFin j hj)).isLt (by omega)
  · refine ⟨rfl, rfl, ?_⟩
    intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl <;> omega

lemma prefixGates_readsBack {k m : Nat} {Y : Fin k → Bool → Finset (Fin m)}
    (hY : Ordered Y) (L : List (Fin k)) :
    ReadsBack (m + 2) ⟨prefixGates hY L, 0⟩ := by
  intro idx hidx u hu
  have hge := gateAt_eq_getElem ⟨prefixGates hY L, 0⟩ idx hidx
  have hmem : gateAt ⟨prefixGates hY L, 0⟩ idx ∈ prefixGates hY L := by
    rw [hge]
    exact List.getElem_mem hidx
  have hlt := (prefixGates_all_and hY L _ hmem).2.2 u hu
  omega

lemma prefixGates_wire_val {k m : Nat} {Y : Fin k → Bool → Finset (Fin m)}
    (hY : Ordered Y) (L : List (Fin k)) (idx : Nat) (hidx : idx < L.length)
    (hj0 : 0 < (L[idx]).val) (i : Fin k) (r : Bool) :
    (wiresOf (prefixGates hY L) (inp m (Y i r))).getD (m + 2 + idx) false =
      decide (L[idx] ≤ i) := by
  have hlen : (inp m (Y i r)).length = m + 2 := inp_length m (Y i r)
  have hRB : ReadsBack (inp m (Y i r)).length ⟨prefixGates hY L, 0⟩ := by
    rw [hlen]
    exact prefixGates_readsBack hY L
  have hidx' : idx < (prefixGates hY L).length := by
    rw [prefixGates_length]
    exact hidx
  have hgate := wires_getD_gate ⟨prefixGates hY L, 0⟩ (inp m (Y i r)) hRB idx hidx'
  rw [wires_eq_wiresOf, hlen] at hgate
  rw [hgate]
  have hga : gateAt ⟨prefixGates hY L, 0⟩ idx =
      ⟨GateOp.and, [(uSplit hY (prevFin (L[idx]) hj0)).val,
        (vSplit hY (prevFin (L[idx]) hj0)).val]⟩ := by
    rw [gateAt_eq_getElem _ idx hidx']
    simp [prefixGates, hj0]
  rw [hga]
  have hu : (uSplit hY (prevFin (L[idx]) hj0)).val < m := (uSplit hY _).isLt
  have hv : (vSplit hY (prevFin (L[idx]) hj0)).val < m := (vSplit hY _).isLt
  have hpu : (wiresOf (prefixGates hY L) (inp m (Y i r))).getD
      (uSplit hY (prevFin (L[idx]) hj0)).val false =
      decide (uSplit hY (prevFin (L[idx]) hj0) ∈ Y i r) := by
    rw [wiresOf_getD_prefix _ _ _ (by rw [hlen]; omega), inp_getD_lt _ _ _ hu]
  have hpv : (wiresOf (prefixGates hY L) (inp m (Y i r))).getD
      (vSplit hY (prevFin (L[idx]) hj0)).val false =
      decide (vSplit hY (prevFin (L[idx]) hj0) ∈ Y i r) := by
    rw [wiresOf_getD_prefix _ _ _ (by rw [hlen]; omega), inp_getD_lt _ _ _ hv]
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq,
    Bool.and_true]
  rw [hpu, hpv]
  exact split_and_eq_step hY (L[idx]) hj0 i r

noncomputable def remapWire {k n m : Nat}
    {X : Fin k → Bool → Finset (Fin n)} {Y : Fin k → Bool → Finset (Fin m)}
    (hY : Ordered Y) (L : List (Fin k)) (w : Nat) : Nat :=
  if hw : w < n then
    let a : Fin n := ⟨w, hw⟩
    if ∀ i r, a ∉ X i r then m
    else if ∀ i r, a ∈ X i r then m + 1
    else if h3 : ∃ j : Fin k, ∀ i r, a ∈ X i r ↔ (i = j ∧ r = false) ∨ j < i then
      (uSplit hY (Classical.choose h3)).val
    else if h4 : ∃ j : Fin k, ∀ i r, a ∈ X i r ↔ (i = j ∧ r = true) ∨ j < i then
      (vSplit hY (Classical.choose h4)).val
    else if h5 : ∃ j : Fin k, 0 < j.val ∧ ∀ i r, a ∈ X i r ↔ j ≤ i then
      let j := Classical.choose h5
      if hYcut : ∃ a' : Fin m, ∀ i r, a' ∈ Y i r ↔ j ≤ i then
        (Classical.choose hYcut).val
      else if hL : ∃ idx : Nat, ∃ hidx : idx < L.length, L[idx] = j then
        m + 2 + Classical.choose hL
      else m
    else m
  else if w = n then m
  else if w = n + 1 then m + 1
  else m + 2 + L.length + (w - (n + 2))

lemma remapWire_lt_base {k n m : Nat}
    {X : Fin k → Bool → Finset (Fin n)} {Y : Fin k → Bool → Finset (Fin m)}
    (hY : Ordered Y) (L : List (Fin k)) (w : Nat) (hw : w < n + 2) :
    remapWire (X := X) hY L w < m + 2 + L.length := by
  unfold remapWire
  by_cases hwn : w < n
  · simp only [hwn, dite_true]
    let a : Fin n := ⟨w, hwn⟩
    by_cases h1 : ∀ i r, a ∉ X i r
    · rw [if_pos h1]; omega
    · rw [if_neg h1]
      by_cases h2 : ∀ i r, a ∈ X i r
      · rw [if_pos h2]; omega
      · rw [if_neg h2]
        by_cases h3 : ∃ j : Fin k, ∀ i r, a ∈ X i r ↔ (i = j ∧ r = false) ∨ j < i
        · rw [dif_pos h3]
          have := (uSplit hY (Classical.choose h3)).isLt
          omega
        · rw [dif_neg h3]
          by_cases h4 : ∃ j : Fin k, ∀ i r, a ∈ X i r ↔ (i = j ∧ r = true) ∨ j < i
          · rw [dif_pos h4]
            have := (vSplit hY (Classical.choose h4)).isLt
            omega
          · rw [dif_neg h4]
            by_cases h5 : ∃ j : Fin k, 0 < j.val ∧ ∀ i r, a ∈ X i r ↔ j ≤ i
            · rw [dif_pos h5]
              let j := Classical.choose h5
              by_cases hYcut : ∃ a' : Fin m, ∀ i r, a' ∈ Y i r ↔ j ≤ i
              · rw [dif_pos hYcut]
                have := (Classical.choose hYcut).isLt
                omega
              · rw [dif_neg hYcut]
                by_cases hL : ∃ idx : Nat, ∃ hidx : idx < L.length, L[idx] = j
                · rw [dif_pos hL]
                  have hidx := (Classical.choose_spec hL).1
                  omega
                · rw [dif_neg hL]
                  omega
            · rw [dif_neg h5]
              omega
  · simp only [hwn, dite_false]
    by_cases hweq : w = n
    · rw [if_pos hweq]; omega
    · rw [if_neg hweq]
      have hw1 : w = n + 1 := by omega
      rw [if_pos hw1]; omega

lemma remapWire_ge {k n m : Nat}
    {X : Fin k → Bool → Finset (Fin n)} {Y : Fin k → Bool → Finset (Fin m)}
    (hY : Ordered Y) (L : List (Fin k)) (w : Nat) (hw : n + 2 ≤ w) :
    remapWire (X := X) hY L w = m + 2 + L.length + (w - (n + 2)) := by
  unfold remapWire
  have h1 : ¬ w < n := by omega
  have h2 : w ≠ n := by omega
  have h3 : w ≠ n + 1 := by omega
  simp [h1, h2, h3]

lemma remapWire_lt_step {k n m : Nat}
    {X : Fin k → Bool → Finset (Fin n)} {Y : Fin k → Bool → Finset (Fin m)}
    (hY : Ordered Y) (L : List (Fin k)) (gIdx w : Nat) (hw : w < n + 2 + gIdx) :
    remapWire (X := X) hY L w < m + 2 + L.length + gIdx := by
  by_cases h : w < n + 2
  · have := remapWire_lt_base (X := X) hY L w h
    omega
  · rw [remapWire_ge (X := X) hY L w (by omega)]
    omega

lemma remapWire_base_val {k n m : Nat}
    {X : Fin k → Bool → Finset (Fin n)} {Y : Fin k → Bool → Finset (Fin m)}
    (hX : Ordered X) (hY : Ordered Y)
    (L : List (Fin k)) (hLmem : ∀ j : Fin k, j ∈ L ↔ j ∈ missingFinset X Y)
    (w : Nat) (hw : w < n + 2) (i : Fin k) (r : Bool) :
    (wiresOf (prefixGates hY L) (inp m (Y i r))).getD (remapWire (X := X) hY L w) false =
      (inp n (X i r)).getD w false := by
  have hlenY : (inp m (Y i r)).length = m + 2 := inp_length m (Y i r)
  by_cases hwn : w < n
  · rw [inp_getD_lt n (X i r) w hwn]
    let a : Fin n := ⟨w, hwn⟩
    unfold remapWire
    simp only [hwn, dite_true]
    by_cases h1 : ∀ i' r', a ∉ X i' r'
    · rw [if_pos h1, wiresOf_getD_prefix _ _ m (by rw [hlenY]; omega), inp_getD_d]
      simp [a, h1 i r]
    · rw [if_neg h1]
      by_cases h2 : ∀ i' r', a ∈ X i' r'
      · rw [if_pos h2, wiresOf_getD_prefix _ _ (m + 1) (by rw [hlenY]; omega), inp_getD_d1]
        simp [a, h2 i r]
      · rw [if_neg h2]
        by_cases h3 : ∃ j : Fin k, ∀ i' r', a ∈ X i' r' ↔ (i' = j ∧ r' = false) ∨ j < i'
        · rw [dif_pos h3]
          let j := Classical.choose h3
          have hj : ∀ i' r', a ∈ X i' r' ↔ (i' = j ∧ r' = false) ∨ j < i' :=
            Classical.choose_spec h3
          have hu := (uSplit hY j).isLt
          rw [wiresOf_getD_prefix _ _ _ (by rw [hlenY]; omega), inp_getD_lt m (Y i r) _ hu]
          apply Bool.eq_iff_iff.mpr
          simp only [decide_eq_true_eq, Fin.eta, uSplit_spec hY j]
          exact (hj i r).symm
        · rw [dif_neg h3]
          by_cases h4 : ∃ j : Fin k, ∀ i' r', a ∈ X i' r' ↔ (i' = j ∧ r' = true) ∨ j < i'
          · rw [dif_pos h4]
            let j := Classical.choose h4
            have hj : ∀ i' r', a ∈ X i' r' ↔ (i' = j ∧ r' = true) ∨ j < i' :=
              Classical.choose_spec h4
            have hv := (vSplit hY j).isLt
            rw [wiresOf_getD_prefix _ _ _ (by rw [hlenY]; omega), inp_getD_lt m (Y i r) _ hv]
            apply Bool.eq_iff_iff.mpr
            simp only [decide_eq_true_eq, Fin.eta, vSplit_spec hY j]
            exact (hj i r).symm
          · rw [dif_neg h4]
            have h5 : ∃ j : Fin k, 0 < j.val ∧ ∀ i' r', a ∈ X i' r' ↔ j ≤ i' := by
              rcases classify_col hX a with c1 | c2 | c3 | c4 | c5
              · exact False.elim (h1 c1)
              · exact False.elim (h2 c2)
              · exact False.elim (h3 c3)
              · exact False.elim (h4 c4)
              · exact c5
            rw [dif_pos h5]
            let j := Classical.choose h5
            have hj : 0 < j.val ∧ ∀ i' r', a ∈ X i' r' ↔ j ≤ i' := Classical.choose_spec h5
            by_cases hYcut : ∃ a' : Fin m, ∀ i' r', a' ∈ Y i' r' ↔ j ≤ i'
            · rw [dif_pos hYcut]
              let a' := Classical.choose hYcut
              have ha' : ∀ i' r', a' ∈ Y i' r' ↔ j ≤ i' := Classical.choose_spec hYcut
              rw [wiresOf_getD_prefix _ _ _ (by rw [hlenY]; omega), inp_getD_lt m (Y i r) _ a'.isLt]
              apply Bool.eq_iff_iff.mpr
              simp only [decide_eq_true_eq, Fin.eta, ha' i r]
              exact (hj.2 i r).symm
            · rw [dif_neg hYcut]
              have hjX : j ∈ cutsFinset X := by
                rw [cutsFinset, Finset.mem_filter]
                exact ⟨Finset.mem_univ _, hj.1, a, hj.2⟩
              have hjY : j ∉ cutsFinset Y := by
                intro hc
                rw [cutsFinset, Finset.mem_filter] at hc
                exact hYcut hc.2.2
              have hjL : j ∈ L := (hLmem j).mpr (Finset.mem_sdiff.mpr ⟨hjX, hjY⟩)
              have hEx : ∃ idx : Nat, ∃ hidx : idx < L.length, L[idx] = j :=
                List.mem_iff_getElem.mp hjL
              rw [dif_pos hEx]
              let idx := Classical.choose hEx
              have hidx : idx < L.length := (Classical.choose_spec hEx).1
              have hEq : L[idx] = j := (Classical.choose_spec hEx).2
              have hj0' : 0 < (L[idx]).val := by rw [hEq]; exact hj.1
              rw [prefixGates_wire_val hY L idx hidx hj0' i r, hEq]
              apply Bool.eq_iff_iff.mpr
              simp only [decide_eq_true_eq]
              exact (hj.2 i r).symm
  · by_cases hweq : w = n
    · subst hweq
      unfold remapWire
      simp only [lt_irrefl, dite_false, ite_true]
      rw [wiresOf_getD_prefix _ _ m (by rw [hlenY]; omega), inp_getD_d, inp_getD_d]
    · have hw1 : w = n + 1 := by omega
      subst hw1
      unfold remapWire
      have h1 : ¬ (n + 1 < n) := by omega
      have h2 : n + 1 ≠ n := by omega
      simp only [h1, h2, dite_false, ite_false, ite_true]
      rw [wiresOf_getD_prefix _ _ (m + 1) (by rw [hlenY]; omega), inp_getD_d1, inp_getD_d1]

lemma transfer_ub {k n m t p b q : Nat}
    {X : Fin k → Bool → Finset (Fin n)} {Y : Fin k → Bool → Finset (Fin m)}
    {f : Fin k → Bool → Fin t → Bool}
    (hX : Ordered X) (hY : Ordered Y)
    (hq : (missingFinset X Y).card ≤ q)
    (hfit : Fits X t f p b) :
    Fits Y t f (p + q) b := by
  rcases hfit with ⟨C, tap, hF, hRB, _, htap, hsz, hnc, heval⟩
  let L : List (Fin k) := (missingFinset X Y).toList
  have hLlen : L.length = (missingFinset X Y).card := Finset.length_toList (missingFinset X Y)
  have hLmem : ∀ j : Fin k, j ∈ L ↔ j ∈ missingFinset X Y := fun j => Finset.mem_toList
  let P : List Gate := prefixGates hY L
  let Q : List Gate := C.gates.map (fun g => ⟨g.op, g.inputs.map (remapWire (X := X) hY L)⟩)
  let C' : Circuit := ⟨P ++ Q, 0⟩
  let tap' : Fin t → Nat := fun a => remapWire (X := X) hY L (tap a)
  have hPlen : P.length = L.length := prefixGates_length hY L
  have hQlen : Q.length = C.gates.length := List.length_map _
  have hC'size : C'.size = L.length + C.size := by
    show (P ++ Q).length = L.length + C.gates.length
    rw [List.length_append, hPlen, hQlen]
  have hF' : FanInTwo C' := by
    intro g hg
    change g ∈ P ++ Q at hg
    rw [List.mem_append] at hg
    rcases hg with hgP | hgQ
    · have h := prefixGates_all_and hY L g hgP
      refine ⟨?_, by omega⟩
      simp [h.1]
    · rw [List.mem_map] at hgQ
      rcases hgQ with ⟨g0, hg0, rfl⟩
      have h0 := hF g0 hg0
      exact ⟨h0.1, by simp [h0.2]⟩
  have hRB' : ReadsBack (m + 2) C' := by
    intro idx hidx u hu
    change idx < (P ++ Q).length at hidx
    rw [List.length_append] at hidx
    by_cases hlt : idx < P.length
    · have hga : gateAt C' idx = gateAt ⟨P, 0⟩ idx := by
        unfold gateAt
        exact List.getD_append _ _ _ _ hlt
      rw [hga] at hu
      exact prefixGates_readsBack hY L idx hlt u hu
    · have hge : P.length ≤ idx := by omega
      let gIdx := idx - P.length
      have hgIdx : gIdx < C.gates.length := by omega
      have hga : gateAt C' idx =
          ⟨(gateAt C gIdx).op, (gateAt C gIdx).inputs.map (remapWire (X := X) hY L)⟩ := by
        unfold gateAt
        rw [List.getD_append_right _ _ _ _ hge]
        have hg1 : Q.getD gIdx ⟨GateOp.or, []⟩ = Q[gIdx] :=
          List.getD_eq_getElem Q _ (by rw [hQlen]; exact hgIdx)
        rw [hg1]
        simp only [Q, List.getElem_map]
        rw [List.getD_eq_getElem C.gates _ hgIdx]
      rw [hga] at hu
      simp only [List.mem_map] at hu
      rcases hu with ⟨u0, hu0, rfl⟩
      have hu0lt : u0 < n + 2 + gIdx := hRB gIdx hgIdx u0 hu0
      have hres := remapWire_lt_step (X := X) hY L gIdx u0 hu0lt
      omega
  have hO' : C'.output < m + 2 + C'.size := by
    change 0 < m + 2 + C'.size
    omega
  have htap' : ∀ a, tap' a < m + 2 + C'.size := by
    intro a
    rw [hC'size]
    have hlt := remapWire_lt_step (X := X) hY L C.size (tap a) (htap a)
    dsimp only [tap']
    omega
  have hnc' : notCount C' = notCount C := by
    have h1 : notCount C' = notCount ⟨P, 0⟩ + notCount ⟨Q, 0⟩ := notCount_append P Q 0
    have hP0 : notCount ⟨P, 0⟩ = 0 :=
      notCount_all_and P (fun g hg => (prefixGates_all_and hY L g hg).1)
    have hQeq : notCount ⟨Q, 0⟩ = notCount C := notCount_map_remap C.gates _
    omega
  have hsz' : C'.size - notCount C' ≤ p + q := by
    have hle := notCount_le_size C
    rw [hC'size, hnc', hLlen]
    omega
  have hsim : ∀ i r (w : Nat), w < n + 2 + C.size →
      (C'.wires (inp m (Y i r))).getD (remapWire (X := X) hY L w) false =
        (C.wires (inp n (X i r))).getD w false := by
    intro i r w
    induction w using Nat.strongRecOn with
    | ind w ih =>
      intro hw
      by_cases hbase : w < n + 2
      · have hrm : remapWire (X := X) hY L w < (inp m (Y i r)).length + P.length := by
          rw [inp_length, hPlen]
          exact remapWire_lt_base (X := X) hY L w hbase
        rw [wires_eq_wiresOf, wires_eq_wiresOf]
        change (wiresOf (P ++ Q) (inp m (Y i r))).getD (remapWire (X := X) hY L w) false =
          (wiresOf C.gates (inp n (X i r))).getD w false
        rw [wiresOf_append_left P Q (inp m (Y i r)) _ hrm]
        rw [wiresOf_getD_prefix C.gates (inp n (X i r)) w (by rw [inp_length]; exact hbase)]
        exact remapWire_base_val hX hY L hLmem w hbase i r
      · let gIdx := w - (n + 2)
        have hgIdx : gIdx < C.gates.length := by
          change w < n + 2 + C.gates.length at hw
          omega
        have hw_eq : w = n + 2 + gIdx := by omega
        have hrm_eq : remapWire (X := X) hY L w = m + 2 + P.length + gIdx := by
          rw [remapWire_ge (X := X) hY L w (by omega), hPlen]
        have hlenX : (inp n (X i r)).length = n + 2 := inp_length n (X i r)
        have hlenY : (inp m (Y i r)).length = m + 2 := inp_length m (Y i r)
        have hRBX : ReadsBack (inp n (X i r)).length C := by rw [hlenX]; exact hRB
        have hRBY : ReadsBack (inp m (Y i r)).length C' := by rw [hlenY]; exact hRB'
        have hgX := wires_getD_gate C (inp n (X i r)) hRBX gIdx hgIdx
        rw [hlenX, ← hw_eq] at hgX
        have hidx' : P.length + gIdx < C'.gates.length := by
          change P.length + gIdx < (P ++ Q).length
          rw [List.length_append, hQlen]
          omega
        have hgY := wires_getD_gate C' (inp m (Y i r)) hRBY (P.length + gIdx) hidx'
        rw [hlenY, ← Nat.add_assoc, ← hrm_eq] at hgY
        rw [hgY, hgX]
        have hga : gateAt C' (P.length + gIdx) =
            ⟨(gateAt C gIdx).op, (gateAt C gIdx).inputs.map (remapWire (X := X) hY L)⟩ := by
          unfold gateAt
          rw [List.getD_append_right _ _ _ _ (Nat.le_add_right _ _)]
          simp only [Nat.add_sub_cancel_left]
          have hg1 : Q.getD gIdx ⟨GateOp.or, []⟩ = Q[gIdx] :=
            List.getD_eq_getElem Q _ (by rw [hQlen]; exact hgIdx)
          rw [hg1]
          simp only [Q, List.getElem_map]
          rw [List.getD_eq_getElem C.gates _ hgIdx]
        rw [hga, List.map_map]
        congr 1
        apply List.map_congr_left
        intro u hu
        have hult : u < w := by
          have := hRB gIdx hgIdx u hu
          omega
        exact ih u hult (by omega)
  refine ⟨C', tap', hF', hRB', hO', htap', hsz', by omega, ?_⟩
  intro i r a
  dsimp only [tap']
  rw [hsim i r (tap a) (htap a)]
  exact heval i r a

lemma fits_report_X {k n m : Nat}
    (X : Fin k → Bool → Finset (Fin n)) (Y : Fin k → Bool → Finset (Fin m)) :
    Fits X k (reportFn X Y) 0 0 := by
  let C : Circuit := ⟨[], 0⟩
  let tap : Fin k → Nat := fun j =>
    if hj : j ∈ missingFinset X Y then
      (Classical.choose (Finset.mem_filter.mp (Finset.mem_sdiff.mp hj).1).2.2).val
    else n
  refine ⟨C, tap, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg; simp [C] at hg
  · intro j hj; simp [C] at hj
  · simp [C, Circuit.size]
  · intro j
    dsimp only [tap]
    split_ifs with hj
    · have := (Classical.choose (Finset.mem_filter.mp (Finset.mem_sdiff.mp hj).1).2.2).isLt
      simp [C, Circuit.size]
      omega
    · simp [C, Circuit.size]
  · simp [C, Circuit.size, notCount]
  · simp [C, notCount]
  · intro i r j
    rw [wires_eq_wiresOf]
    change (inp n (X i r)).getD (tap j) false = reportFn X Y i r j
    dsimp only [tap, reportFn]
    split_ifs with hj
    · let a := Classical.choose (Finset.mem_filter.mp (Finset.mem_sdiff.mp hj).1).2.2
      have ha : ∀ i' r', a ∈ X i' r' ↔ j ≤ i' :=
        Classical.choose_spec (Finset.mem_filter.mp (Finset.mem_sdiff.mp hj).1).2.2
      rw [inp_getD_lt n (X i r) a.val a.isLt]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, Fin.eta, hj, true_and, ha i r]
    · rw [inp_getD_d]
      simp [hj]

def stepFn {k : Nat} (j : Fin k) : Fin k → Bool → Bool :=
  fun i _ => decide (j ≤ i)

def SameClass {k : Nat} (g1 g2 : Fin k → Bool → Bool) : Prop :=
  g1 = g2 ∨ g1 = fun i r => !g2 i r

lemma sameClass_symm {k : Nat} {g1 g2 : Fin k → Bool → Bool} (h : SameClass g1 g2) :
    SameClass g2 g1 := by
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · refine Or.inr ?_
    funext i r
    simp

lemma sameClass_trans {k : Nat} {g1 g2 g3 : Fin k → Bool → Bool}
    (h12 : SameClass g1 g2) (h23 : SameClass g2 g3) : SameClass g1 g3 := by
  rcases h12 with rfl | rfl
  · exact h23
  · rcases h23 with rfl | rfl
    · exact Or.inr rfl
    · refine Or.inl ?_
      funext i r
      simp

lemma stepFn_not_sameClass {k : Nat} {j1 j2 : Fin k} (hne : j1 ≠ j2) :
    ¬ SameClass (stepFn j1) (stepFn j2) := by
  rintro (heq | heq)
  · rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h := congrFun (congrFun heq j1) false
      simp only [stepFn, le_refl, decide_true] at h
      have hn : ¬ j2 ≤ j1 := not_le_of_gt hlt
      simp [hn] at h
    · have h := congrFun (congrFun heq j2) false
      simp only [stepFn, le_refl, decide_true] at h
      have hn : ¬ j1 ≤ j2 := not_le_of_gt hgt
      simp [hn] at h
  · have h := congrFun (congrFun heq (max j1 j2)) false
    simp only [stepFn, le_max_left, le_max_right, decide_true, Bool.not_true] at h
    cases h

lemma not_input_sameClass {k n m : Nat}
    {X : Fin k → Bool → Finset (Fin n)} {Y : Fin k → Bool → Finset (Fin m)}
    (hY : Ordered Y) (C : Circuit) {j : Fin k}
    (hj : j ∈ missingFinset X Y) {w : Nat} (hw : w < m + 2) :
    ¬ SameClass (fun i r => (C.wires (inp m (Y i r))).getD w false) (stepFn j) := by
  have hjX : j ∈ cutsFinset X := (Finset.mem_sdiff.mp hj).1
  have hjY : j ∉ cutsFinset Y := (Finset.mem_sdiff.mp hj).2
  have hj0 : 0 < j.val := (Finset.mem_filter.mp hjX).2.1
  let z0 : Fin k := ⟨0, by omega⟩
  have hz0_lt : z0 < j := hj0
  have hnotle : ¬ j ≤ z0 := not_le_of_gt hz0_lt
  have hpre : ∀ i r, (C.wires (inp m (Y i r))).getD w false = (inp m (Y i r)).getD w false := by
    intro i r
    rw [wires_eq_wiresOf]
    exact wiresOf_getD_prefix C.gates (inp m (Y i r)) w (by rw [inp_length]; exact hw)
  intro hsc
  by_cases hwm : w < m
  · let a : Fin m := ⟨w, hwm⟩
    rcases hsc with heq | heq
    · apply hjY
      rw [cutsFinset, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, hj0, a, fun i r => ?_⟩
      have h := congrFun (congrFun heq i) r
      rw [hpre i r, inp_getD_lt m (Y i r) w hwm] at h
      simpa [stepFn, a] using congrArg (· = true) h
    · have h0 := congrFun (congrFun heq z0) false
      rw [hpre z0 false, inp_getD_lt m (Y z0 false) w hwm] at h0
      simp only [stepFn, hnotle, decide_false, Bool.not_false, decide_eq_true_eq] at h0
      have hjv := congrFun (congrFun heq j) false
      rw [hpre j false, inp_getD_lt m (Y j false) w hwm] at hjv
      simp only [stepFn, le_refl, decide_true, Bool.not_true, decide_eq_false_iff_not] at hjv
      exact hjv (hY.2.2 z0 j hz0_lt false false h0)
  · by_cases hweq : w = m
    · subst hweq
      rcases hsc with heq | heq
      · have h := congrFun (congrFun heq j) false
        rw [hpre j false, inp_getD_d] at h
        simp [stepFn] at h
      · have h := congrFun (congrFun heq z0) false
        rw [hpre z0 false, inp_getD_d] at h
        simp [stepFn, hnotle] at h
    · have hw1 : w = m + 1 := by omega
      subst hw1
      rcases hsc with heq | heq
      · have h := congrFun (congrFun heq z0) false
        rw [hpre z0 false, inp_getD_d1] at h
        simp [stepFn, hnotle] at h
      · have h := congrFun (congrFun heq j) false
        rw [hpre j false, inp_getD_d1] at h
        simp [stepFn] at h

lemma report_lb {k n m p b : Nat}
    {X : Fin k → Bool → Finset (Fin n)} {Y : Fin k → Bool → Finset (Fin m)}
    (hY : Ordered Y)
    (hfit : Fits Y k (reportFn X Y) p b) :
    (missingFinset X Y).card ≤ p := by
  rcases hfit with ⟨C, tap, _, hRB, _, htap, hsz, _, heval⟩
  let val : Nat → Fin k → Bool → Bool := fun w i r => (C.wires (inp m (Y i r))).getD w false
  let W : Fin k → Finset Nat := fun j =>
    (Finset.range (m + 2 + C.size)).filter (fun w => SameClass (val w) (stepFn j))
  have hWne : ∀ j ∈ missingFinset X Y, (W j).Nonempty := by
    intro j hj
    refine ⟨tap j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (htap j), ?_⟩⟩
    left
    funext i r
    dsimp only [val, stepFn]
    rw [heval i r j]
    simp [reportFn, hj]
  let firstW : Fin k → Nat := fun j => if h : (W j).Nonempty then (W j).min' h else 0
  let firstG : Fin k → Nat := fun j => firstW j - (m + 2)
  have hfirstW_mem : ∀ j ∈ missingFinset X Y, firstW j ∈ W j := by
    intro j hj
    dsimp only [firstW]
    simp only [hWne j hj, dite_true]
    exact Finset.min'_mem (W j) (hWne j hj)
  have hfirstW_le : ∀ j ∈ missingFinset X Y, ∀ w ∈ W j, firstW j ≤ w := by
    intro j hj w hw
    dsimp only [firstW]
    simp only [hWne j hj, dite_true]
    exact Finset.min'_le (W j) w hw
  have hfirstW_ge : ∀ j ∈ missingFinset X Y, m + 2 ≤ firstW j := by
    intro j hj
    by_contra hlt
    have hmem := Finset.mem_filter.mp (hfirstW_mem j hj)
    exact not_input_sameClass hY C hj (by omega) hmem.2
  have hmaps : Set.MapsTo firstG ((missingFinset X Y) : Set (Fin k))
      (((Finset.range C.size).filter (fun g => (gateAt C g).op ≠ GateOp.not) : Finset Nat) : Set Nat) := by
    intro j hj
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    have hmem := Finset.mem_filter.mp (hfirstW_mem j hj)
    have hlt := Finset.mem_range.mp hmem.1
    have hge := hfirstW_ge j hj
    have hglt : firstG j < C.size := by dsimp only [firstG]; omega
    refine ⟨hglt, ?_⟩
    intro hop
    have hweq : m + 2 + firstG j = firstW j := by dsimp only [firstG]; omega
    have hgate : ∀ i r, val (firstW j) i r =
        (gateAt C (firstG j)).op.eval ((gateAt C (firstG j)).inputs.map fun u => val u i r) := by
      intro i r
      dsimp only [val]
      rw [← hweq]
      have hlen : (inp m (Y i r)).length = m + 2 := inp_length m (Y i r)
      have hRB' : ReadsBack (inp m (Y i r)).length C := by rw [hlen]; exact hRB
      have h := wires_getD_gate C (inp m (Y i r)) hRB' (firstG j) hglt
      rw [hlen] at h
      exact h
    cases hins : (gateAt C (firstG j)).inputs with
    | nil =>
      have hconst : val (firstW j) = val (m + 1) := by
        funext i r
        rw [hgate i r, hop, hins]
        dsimp only [val]
        rw [wires_eq_wiresOf, wiresOf_getD_prefix C.gates (inp m (Y i r)) (m + 1)
          (by rw [inp_length]; omega), inp_getD_d1]
        rfl
      have hsc : SameClass (val (m + 1)) (stepFn j) := by
        rw [← hconst]
        exact hmem.2
      exact not_input_sameClass hY C hj (by omega) hsc
    | cons u rest =>
      have hu_mem : u ∈ (gateAt C (firstG j)).inputs := by rw [hins]; simp
      have hu_lt : u < firstW j := by
        have := hRB (firstG j) hglt u hu_mem
        omega
      have hneg : val (firstW j) = fun i r => !val u i r := by
        funext i r
        rw [hgate i r, hop, hins]
        rfl
      have hsc_u : SameClass (val u) (stepFn j) :=
        sameClass_trans (sameClass_symm (Or.inr hneg)) hmem.2
      have huW : u ∈ W j := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hsc_u⟩
      have hle := hfirstW_le j hj u huW
      omega
  have hinj : Set.InjOn firstG ((missingFinset X Y) : Set (Fin k)) := by
    intro j1 hj1 j2 hj2 hEq
    have hge1 := hfirstW_ge j1 hj1
    have hge2 := hfirstW_ge j2 hj2
    have hweq : firstW j1 = firstW j2 := by dsimp only [firstG] at hEq; omega
    have hsc1 : SameClass (val (firstW j1)) (stepFn j1) :=
      (Finset.mem_filter.mp (hfirstW_mem j1 hj1)).2
    have hsc2 : SameClass (val (firstW j2)) (stepFn j2) :=
      (Finset.mem_filter.mp (hfirstW_mem j2 hj2)).2
    rw [hweq] at hsc1
    have hsc12 : SameClass (stepFn j1) (stepFn j2) :=
      sameClass_trans (sameClass_symm hsc1) hsc2
    by_contra hne
    exact stepFn_not_sameClass hne hsc12
  have hcard := Finset.card_le_card_of_injOn firstG hmaps hinj
  rw [nonNot_card_eq C] at hcard
  exact le_trans hcard hsz

end PEqualNP.Outside.L_lib_1328

theorem PEqualNP.Outside.L_lib_1328 : letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ (k n m : Nat) (X : Fin k → Bool → Finset (Fin n)) (Y : Fin k → Bool → Finset (Fin m)),
  let ordered := fun (d : Nat) (Z : Fin k → Bool → Finset (Fin d)) =>
    (∀ i, ¬ Z i false ⊆ Z i true) ∧ (∀ i, ¬ Z i true ⊆ Z i false) ∧
    (∀ i j, i < j → ∀ s r, Z i s ⊆ Z j r)
  let cuts := fun (d : Nat) (Z : Fin k → Bool → Finset (Fin d)) =>
    Finset.univ.filter (fun j : Fin k => 0 < j.val ∧ ∃ a : Fin d,
      ∀ i r, (a ∈ Z i r ↔ j ≤ i))
  let fits := fun (d : Nat) (Z : Fin k → Bool → Finset (Fin d)) (t : Nat)
      (f : Fin k → Bool → Fin t → Bool) (p b : Nat) =>
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin t → Nat),
      PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (d+2) C ∧
      C.output < d+2+C.size ∧ (∀ a, tap a < d+2+C.size) ∧
      C.size - PEqualNP.NotBracket.notCount C ≤ p ∧ PEqualNP.NotBracket.notCount C ≤ b ∧
      ∀ i r a, (C.wires (List.ofFn (fun z : Fin d => decide (z ∈ Z i r)) ++ [false,true])).getD
        (tap a) false = f i r a
  let missing := cuts n X \ cuts m Y
  let report := fun (i : Fin k) (_ : Bool) (j : Fin k) => decide (j ∈ missing ∧ j ≤ i)
  ordered n X → ordered m Y →
    (∀ q : Nat, ((∀ t f p b, fits n X t f p b → fits m Y t f (p+q) b) ↔ missing.card ≤ q)) ∧
    (∀ p b : Nat, fits m Y k report p b ↔ missing.card ≤ p) := by
  intro k n m X Y ordered cuts fits missing report hX hY
  have hX' : PEqualNP.Outside.L_lib_1328.Ordered X := hX
  have hY' : PEqualNP.Outside.L_lib_1328.Ordered Y := hY
  have hmiss : missing = PEqualNP.Outside.L_lib_1328.missingFinset X Y := by
    ext j
    simp [missing, cuts, PEqualNP.Outside.L_lib_1328.missingFinset,
      PEqualNP.Outside.L_lib_1328.cutsFinset]
  have hrep : report = PEqualNP.Outside.L_lib_1328.reportFn X Y := by
    funext i r j
    apply Bool.eq_iff_iff.mpr
    simp [report, PEqualNP.Outside.L_lib_1328.reportFn, hmiss]
  have hfits_iff : ∀ (d : Nat) (Z : Fin k → Bool → Finset (Fin d)) (t : Nat)
      (f : Fin k → Bool → Fin t → Bool) (p b : Nat),
      fits d Z t f p b ↔ PEqualNP.Outside.L_lib_1328.Fits Z t f p b := by
    intro d Z t f p b
    constructor
    · rintro ⟨C, tap, h1, h2, h3, h4, h5, h6, h7⟩
      refine ⟨C, tap, h1, h2, h3, h4, h5, h6, fun i r a => ?_⟩
      rw [← PEqualNP.Outside.L_lib_1328.inp_eq_ofFn_any (Z i r) Classical.propDecidable]
      exact h7 i r a
    · rintro ⟨C, tap, h1, h2, h3, h4, h5, h6, h7⟩
      refine ⟨C, tap, h1, h2, h3, h4, h5, h6, fun i r a => ?_⟩
      rw [PEqualNP.Outside.L_lib_1328.inp_eq_ofFn_any (Z i r) Classical.propDecidable]
      exact h7 i r a
  have hrepX : fits n X k report 0 0 := by
    rw [hfits_iff, hrep]
    exact PEqualNP.Outside.L_lib_1328.fits_report_X X Y
  have hrepLB : ∀ p b : Nat, fits m Y k report p b → missing.card ≤ p := by
    intro p b hf
    rw [hfits_iff, hrep] at hf
    rw [hmiss]
    exact PEqualNP.Outside.L_lib_1328.report_lb hY' hf
  have htr : ∀ q : Nat, missing.card ≤ q → ∀ t f p b, fits n X t f p b → fits m Y t f (p + q) b := by
    intro q hq t f p b hf
    rw [hfits_iff] at hf ⊢
    rw [hmiss] at hq
    exact PEqualNP.Outside.L_lib_1328.transfer_ub hX' hY' hq hf
  constructor
  · intro q
    constructor
    · intro h
      have h1 := h k report 0 0 hrepX
      have h2 := hrepLB (0 + q) 0 h1
      simpa only [Nat.zero_add] using h2
    · exact htr q
  · intro p b
    constructor
    · exact hrepLB p b
    · intro hp
      have h1 := htr p hp k report 0 0 hrepX
      rw [hfits_iff] at h1 ⊢
      exact PEqualNP.Outside.L_lib_1328.fits_mono (Nat.le_of_eq (Nat.zero_add p)) (Nat.zero_le b) h1
