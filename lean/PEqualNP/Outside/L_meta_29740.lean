import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29740
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

theorem len (gs : List Gate) (x : List Bool) : (gs.foldl step x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih => simp [List.foldl_append, step, ih]; omega


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


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover

namespace Network
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

 
namespace Unate

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
    {pos : Bool} (polarity : ∀ x y : ℕ → Bool, Changes (n+m) i.val none x y →
      if pos then value (n+m) C x (fun _ => none) C.output = true →
                   value (n+m) C y (fun _ => none) C.output = true
      else value (n+m) C y (fun _ => none) C.output = true →
           value (n+m) C x (fun _ => none) C.output = true) :
    if pos then (∀ j, A i₀ j = true → A i j = true) else (∀ j, A i j = true → A i₀ j = true) := by
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
  have relate (j : Fin m) := polarity (bare j) (row i j) (change_insert_input (by omega))
  cases pos
  · simp only [Bool.false_eq_true, ↓reduceIte]
    intro j
    rw [← rowEval i j, ← bareEval j]
    exact relate j
  · simp only [↓reduceIte]
    intro j
    rw [← bareEval j, ← rowEval i j]
    exact relate j

theorem omitted_col_comparable {n m : ℕ} {A : Fin n → Fin m → Bool}
    {C : Circuit} {L : Finset ℕ} (rep : PEqualNP.Represents.Represents A C)
    (hL : closed (n+m) C L) (live : Live (n+m) L C.output)
    {j₀ j : Fin m} (omitted : ¬ Path (n+m) C L (n+j₀.val) C.output)
    {pos : Bool} (polarity : ∀ x y : ℕ → Bool, Changes (n+m) (n+j.val) none x y →
      if pos then value (n+m) C x (fun _ => none) C.output = true →
                   value (n+m) C y (fun _ => none) C.output = true
      else value (n+m) C y (fun _ => none) C.output = true →
           value (n+m) C x (fun _ => none) C.output = true) :
    if pos then (∀ i, A i j₀ = true → A i j = true) else (∀ i, A i j = true → A i j₀ = true) := by
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
  have relate (i : Fin n) := polarity (bare i) (col i j) (change_insert_input (by have := i.isLt; omega))
  cases pos
  · simp only [Bool.false_eq_true, ↓reduceIte]
    intro i
    rw [← colEval i j, ← bareEval i]
    exact relate i
  · simp only [↓reduceIte]
    intro i
    rw [← bareEval i, ← colEval i j]
    exact relate i

theorem positive_outside {N : ℕ} {C : Circuit} {L K : Finset ℕ} {f i w : ℕ}
    (cl : closed N C L) (ck : closed N C K) (hf : f ∈ K) (fan : FanInTwo C)
    (only : ∀ j ∈ L, (gateAt C j).op = .not → j = f)
    (hi : i < N) (unused : i ∉ used N C K) (hw : Live N L w)
    (x y : ℕ → Bool) (hxy : Changes N i none x y) :
    value N C x (fun _ => none) w = true → value N C y (fun _ => none) w = true := by
  have stable := unchanged ck (value_is_model ck x) (value_is_model ck y)
    (value_changes hi C hxy) (w := N+f) (Or.inr ⟨f,hf,rfl⟩) (not_path_unused unused (by omega))
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rcases hw with hw | ⟨j,hj,rfl⟩
    · rw [val_raw hw rfl, val_raw hw rfl]
      by_cases eq : w = i
      · simpa [eq] using hxy.2.2
      · rw [hxy.1 w hw eq]; exact id
    by_cases hn : (gateAt C j).op = .not
    · rw [only j hj hn, stable]; exact id
    have mem : gateAt C j ∈ C.gates := by
      rw [gateAt, List.getD_eq_getElem _ _ (cl.1 j hj)]; exact List.getElem_mem _
    have ops := (fan _ mem).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ops
    rw [val_gate (cl.1 j hj) rfl, val_gate (cl.1 j hj) rfl]
    apply eval_positive _ (ops.elim Or.inl (fun h => h.elim Or.inr (fun e => (hn e).elim)))
    intro u hu
    split_ifs with hb
    · exact ih u hb (parent_live cl hj ⟨hu,hb⟩)
    · exact id

end Unate

open Network Unate

theorem cone_capacity {N : ℕ} {C : Circuit} {L : Finset ℕ} {r : ℕ}
    (hr : r ∈ L) (cl : closed N C L)
    (next : ∀ i ∈ L, i ≠ r → ∃ j ∈ L, before C N j (N+i)) : L.card ≤ r+1 := by
  have nonempty : L.Nonempty := ⟨r,hr⟩
  have top : L.max' nonempty = r := by
    by_contra h
    obtain ⟨j,hj,hb⟩ := next _ (L.max'_mem nonempty) h
    have hlt := hb.2
    have le := L.le_max' j hj
    omega
  have bounded (i : ℕ) (hi : i ∈ L) : i ≤ r := top ▸ L.le_max' i hi
  have sub : L ⊆ Finset.range (r+1) := fun i hi => Finset.mem_range.mpr (by have := bounded i hi; omega)
  simpa using Finset.card_le_card sub

theorem count_cone {n m : ℕ} {C : Circuit} {L : Finset ℕ} {r : ℕ}
    (hr : r ∈ L) (cl : closed (n+m) C L)
    (next : ∀ i ∈ L, i ≠ r → ∃ j ∈ L, before C (n+m) j (n+m+i))
    (fan : FanInTwo C) (unary : ∀ g ∈ C.gates, g.op = .not → g.inputs.length ≤ 1)
    (rows : (missingRows n m C L).card ≤ 1) (cols : (missingCols n m C L).card ≤ 1)
    (hasNot : 0 < (activeNot C L).card) (small : C.size+2 ≤ n+m) :
    (activeNot C L).card = 1 ∧ (missingRows n m C L).card = 1 ∧
    (missingCols n m C L).card = 1 ∧ L = Finset.range C.size ∧ C.size = r+1 ∧
    Set.InjOn Prod.snd (slots (n+m) C L : Set (ℕ × ℕ)) := by
  have partition := input_partition n m C L
  have low := slots_count_low hr next
  have high := slots_count_high cl fan unary
  have image := Finset.card_image_le (s := slots (n+m) C L) (f := Prod.snd)
  change (used (n+m) C L).card ≤ (slots (n+m) C L).card at image
  have sub : L ⊆ Finset.range C.size := fun j hj => Finset.mem_range.mpr (cl.1 j hj)
  have le : L.card ≤ C.size := by simpa using Finset.card_le_card sub
  have pos := Finset.card_pos.mpr ⟨r,hr⟩
  have cap := cone_capacity hr cl next
  have real : r < C.size := cl.1 r hr
  refine ⟨by omega, by omega, by omega, Finset.eq_of_subset_of_card_le sub (by simp; omega), by omega, ?_⟩
  apply Finset.injOn_of_card_image_eq
  change (used (n+m) C L).card = (slots (n+m) C L).card
  omega

theorem bank_bound {ι κ : Type} {A : ι → κ → Bool} (inj : Function.Injective A)
    (full : ∀ r, (∀ i, (∀ j, A r j ≤ A i j) ∨ (∀ j, A i j ≤ A r j)) → ∀ j, A r j = true)
    (r : ι) (lines : ∀ i, ∃ pos : Bool, if pos then (∀ j, A r j = true → A i j = true)
      else (∀ j, A i j = true → A r j = true)) (S : Finset ι)
    (increasing : ∀ i ∈ S, ∀ j, A r j = true → A i j = true) : S.card ≤ 1 := by
  have top := full r (fun i => by
    obtain ⟨p,h⟩ := lines i
    cases p
    · exact Or.inr (fun j => Bool.le_iff_imp.mpr (h j))
    · exact Or.inl (fun j => Bool.le_iff_imp.mpr (h j)))
  apply Finset.card_le_one.mpr
  intro a ha b hb
  apply inj
  exact funext fun j => (increasing a ha j (top j)).trans (increasing b hb j (top j)).symm

theorem mono_fan {C : Circuit} (mono : Monotone2 C) : FanInTwo C := by
  intro g hg
  obtain ⟨op,len⟩ := mono g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at op ⊢
  exact ⟨by tauto, len⟩

theorem append_neg {n m : ℕ} {A : Fin n → Fin m → Bool} {b : ℕ}
    (h : RepSizeAtMost (fun i j => !(A i j)) b) :
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ b+1 ∧ Represents A C := by
  obtain ⟨D,hm,hs,hr⟩ := h
  let g : Gate := ⟨.not,[D.output]⟩
  let C : Circuit := ⟨D.gates ++ [g], n+m+D.size⟩
  refine ⟨C, ?_, by simpa [C,Circuit.size] using hs, ?_⟩
  · intro a ha
    change a ∈ D.gates ++ [g] at ha
    rcases List.mem_append.mp ha with ha | ha
    · exact mono_fan hm a ha
    · obtain rfl : a = g := by simpa using ha
      simp [g]
  · intro i j
    let x := oneEach i j
    have hl : (D.gates.foldl step x).length = n+m+D.size := by simp [len,x,oneEach,Circuit.size]
    change ((D.gates ++ [g]).foldl step x).getD (n+m+D.size) false = _
    simp only [List.foldl_append,List.foldl_cons,List.foldl_nil,step,snoc,hl,lt_self_iff_false,
      ↓reduceIte, compute,g,GateOp.eval,List.map_cons,List.map_nil,List.headD_cons]
    change (!(D.eval (oneEach i j))) = A i j
    simp [hr i j]

theorem peel {n m : ℕ} {A : Fin n → Fin m → Bool} {C : Circuit} {f : ℕ}
    (fan : FanInTwo C) (rep : Represents A C) (last : C.size = f+1)
    (out : C.output = n+m+f) (inv : (gateAt C f).op = .not)
    (only : ∀ j < f, (gateAt C j).op ≠ .not) :
    RepSizeAtMost (fun i j => !(A i j)) f := by
  let g := gateAt C f
  let gs := C.gates.take f
  have fl : f < C.gates.length := by change f < C.size; omega
  have gl : gs.length = f := by simp [gs, Nat.le_of_lt fl]
  have eqg : C.gates[f] = g := (List.getD_eq_getElem _ _ fl).symm
  have split : C.gates = gs ++ [g] := by
    rw [← eqg]
    change C.gates = C.gates.take f ++ [C.gates[f]]
    rw [← List.take_succ_eq_append_getElem]
    simp [show f+1 = C.gates.length from last.symm]
  let D : Circuit := ⟨gs,g.inputs.headD (n+m+f)⟩
  refine ⟨D, ?_, by change gs.length ≤ f; omega, ?_⟩
  · intro a ha
    change a ∈ gs at ha
    have mem : a ∈ C.gates := split ▸ List.mem_append_left _ ha
    obtain ⟨j,hj,he⟩ := List.mem_iff_getElem.mp ha
    have jf : j < f := by omega
    have eq : gateAt C j = a := by
      rw [gateAt, List.getD_eq_getElem _ _ (by omega)]
      simpa [gs] using he
    obtain ⟨op,hl⟩ := fan a mem
    have ne := only j jf
    rw [eq] at ne
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op ⊢
    exact ⟨by tauto,hl⟩
  · intro i j
    let x := oneEach i j
    let W := gs.foldl step x
    have hl : W.length = n+m+f := by simp [W,len,x,oneEach,gl]
    have e := rep i j
    change (C.gates.foldl step x).getD C.output false = A i j at e
    rw [split,out,List.foldl_append] at e
    change (W ++ [compute W g]).getD (n+m+f) false = _ at e
    rw [snoc,hl,if_neg (lt_irrefl _),if_pos rfl] at e
    change W.getD (g.inputs.headD (n+m+f)) false = !(A i j)
    rw [← e]
    simp only [compute,show g.op = .not from inv,GateOp.eval]
    cases g.inputs with
    | nil => exact getD_ge W (n+m+f) hl.le
    | cons u us => simp

theorem classify {n m : ℕ} {A : Fin n → Fin m → Bool}
    (hi : Function.Injective A) (hj : Function.Injective (fun j i => A i j))
    (rowFull : ∀ r, (∀ i, (∀ j, A r j ≤ A i j) ∨ (∀ j, A i j ≤ A r j)) → ∀ j, A r j = true)
    (colFull : ∀ c, (∀ j, (∀ i, A i c ≤ A i j) ∨ (∀ i, A i j ≤ A i c)) → ∀ i, A i c = true)
    {s : ℕ} (budget : s+2 ≤ n+m) {C : Circuit} (fan : FanInTwo C)
    (size : C.size ≤ s) (rep : Represents A C) :
    RepSizeAtMost A s ∨ ∃ b, b+1 ≤ s ∧ RepSizeAtMost (fun i j => !(A i j)) b := by
  classical
  let E := trim C
  have eSize : E.size = C.size := by simp [E,trim,Circuit.size]
  have eFan : FanInTwo E := trim_fan C fan
  have eUnary : ∀ g ∈ E.gates, g.op = .not → g.inputs.length ≤ 1 := trim_unary C
  have eRep : Represents A E := fun i j => (trim_eval C _).trans (rep i j)
  by_cases gate : n+m ≤ E.output ∧ E.output < n+m+E.gates.length
  swap
  · left
    let D : Circuit := ⟨[],E.output⟩
    refine ⟨D,by simp [Monotone2,D],Nat.zero_le _,?_⟩
    intro i j
    rw [← eRep i j]
    let x := oneEach i j
    have lx : x.length = n+m := by simp [x,oneEach]
    change x.getD E.output false = (E.gates.foldl step x).getD E.output false
    by_cases low : E.output < n+m
    · exact (pre _ _ _ (by omega)).symm
    · rw [getD_ge _ _ (by omega),getD_ge _ _ (by rw [len]; omega)]
  let r := E.output - (n+m)
  have out : E.output = n+m+r := by dsimp [r]; omega
  have real : r < E.gates.length := by omega
  obtain ⟨L,hr,cl,next⟩ := minimal_closed (n+m) E r real
  by_cases zero : (activeNot E L).card = 0
  · obtain ⟨D,hm,hd,hs⟩ := noNotCircuit eFan cl hr out zero eRep
    exact Or.inl ⟨D,hm,hs.trans_le (eSize.trans_le size),hd⟩
  obtain ⟨one,rows,cols,allL,last,inject⟩ := count_cone hr cl next eFan eUnary
    (missing_rows_le hi eRep cl hr out) (missing_cols_le hj eRep cl hr out)
    (Nat.pos_of_ne_zero zero) (by omega)
  obtain ⟨f,hf⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero zero)
  obtain ⟨hfL,inv⟩ := activeNot_mem.mp hf
  have only (j : ℕ) (mem : j ∈ L) (op : (gateAt E j).op = .not) : j = f :=
    Finset.card_le_one.mp one.le _ (activeNot_mem.mpr ⟨mem,op⟩) _ hf
  obtain ⟨K,hfK,ck,knext⟩ := minimal_closed (n+m) E f (cl.1 _ hfL)
  have live : Live (n+m) L E.output := Or.inr ⟨r,hr,out⟩
  have polarity (u : ℕ) (hu : u < n+m) := original_unate (fork := none) (i := u)
    cl eFan hu (fun _ _ _ _ h₁ h₂ a b => unique_reader_of_inj inject h₁ h₂ a b)
    (fun _ h => by cases h) live
  obtain ⟨r₀,h₀⟩ := Finset.card_pos.mp (show 0 < (missingRows n m E L).card by omega)
  obtain ⟨c₀,k₀⟩ := Finset.card_pos.mp (show 0 < (missingCols n m E L).card by omega)
  have awayR : ¬ Path (n+m) E L r₀.val E.output :=
    not_path_unused (Finset.mem_filter.mp h₀).2 (by have := r₀.isLt; omega)
  have awayC : ¬ Path (n+m) E L (n+c₀.val) E.output :=
    not_path_unused (Finset.mem_filter.mp k₀).2 (by have := c₀.isLt; omega)
  have kr : (missingRows n m E K).card ≤ 1 := by
    apply bank_bound hi rowFull r₀
    · intro i
      obtain ⟨p,h⟩ := polarity i.val (by have := i.isLt; omega)
      exact ⟨p,omitted_row_comparable eRep cl live awayR h⟩
    · intro i hm
      exact omitted_row_comparable (pos := true) eRep cl live awayR
        (positive_outside cl ck hfK eFan only (by have := i.isLt; omega) (Finset.mem_filter.mp hm).2 live)
  have kc : (missingCols n m E K).card ≤ 1 := by
    apply bank_bound hj colFull c₀
    · intro j
      obtain ⟨p,h⟩ := polarity (n+j.val) (by have := j.isLt; omega)
      exact ⟨p,omitted_col_comparable eRep cl live awayC h⟩
    · intro j hm
      exact omitted_col_comparable (pos := true) eRep cl live awayC
        (positive_outside cl ck hfK eFan only (by have := j.isLt; omega) (Finset.mem_filter.mp hm).2 live)
  obtain ⟨_,_,_,_,finalGate,_⟩ := count_cone hfK ck knext eFan eUnary kr kc
    (Finset.card_pos.mpr ⟨f,activeNot_mem.mpr ⟨hfK,inv⟩⟩) (by omega)
  have eq : r = f := by omega
  refine Or.inr ⟨f,by omega,peel eFan eRep finalGate (eq ▸ out) inv ?_⟩
  intro j bound op
  have mem : j ∈ L := allL ▸ Finset.mem_range.mpr (by omega)
  have := only j mem op
  omega

end PEqualNP.Outside.L_meta_29740

theorem PEqualNP.Outside.L_meta_29740 : (∀ (n m : Nat) (A : Fin n → Fin m → Bool),
  2 ≤ n → 2 ≤ m →
  Function.Injective A → Function.Injective (fun j i => A i j) →
  (∀ r : Fin n, (∀ i : Fin n, (∀ j, A r j ≤ A i j) ∨ (∀ j, A i j ≤ A r j)) →
    ∀ j, A r j = true) →
  (∀ c : Fin m, (∀ j : Fin m, (∀ i, A i c ≤ A i j) ∨ (∀ i, A i j ≤ A i c)) →
    ∀ i, A i c = true) →
  ∀ s : Nat, s + 2 ≤ n + m →
    ((∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧
      C.size ≤ s ∧ PEqualNP.Represents.Represents A C) ↔
    PEqualNP.Represents.RepSizeAtMost A s ∨
      ∃ b : Nat, b + 1 ≤ s ∧ PEqualNP.Represents.RepSizeAtMost (fun i j => !(A i j)) b)) := by
  intro n m A _ _ hi hj rowFull colFull s budget
  constructor
  · rintro ⟨C,fan,hs,rep⟩
    exact PEqualNP.Outside.L_meta_29740.classify hi hj rowFull colFull budget fan hs rep
  · rintro (⟨C,hm,hs,rep⟩ | ⟨b,hb,neg⟩)
    · exact ⟨C,PEqualNP.Outside.L_meta_29740.mono_fan hm,hs,rep⟩
    · obtain ⟨C,fan,hs,rep⟩ := PEqualNP.Outside.L_meta_29740.append_neg neg
      exact ⟨C,fan,hs.trans hb,rep⟩
