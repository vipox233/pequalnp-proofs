import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29776_aux
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


end PEqualNP.Outside.L_meta_29776_aux
namespace PEqualNP.Outside.L_meta_29776_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover

theorem tight_count {n m : ℕ} {A : Fin n → Fin m → Bool}
    {C : Circuit} {L : Finset ℕ} {r : ℕ}
    (hi : Function.Injective A) (hj : Function.Injective (fun j i => A i j))
    (hA : Represents A C) (hL : closed (n+m) C L)
    (hr : r ∈ L) (ho : C.output = n+m+r)
    (huse : ∀ i ∈ L, i ≠ r → ∃ j ∈ L, before C (n+m) j (n+m+i))
    (hC : FanInTwo C)
    (hNot : ∀ g ∈ C.gates, g.op = .not → g.inputs.length ≤ 1)
    (hsmall : C.size + 2 ≤ n+m) (hn : 0 < (activeNot C L).card) :
    (activeNot C L).card = 1 ∧
    (missingRows n m C L).card = 1 ∧
    (missingCols n m C L).card = 1 ∧
    L = Finset.range C.size ∧ C.size + 2 = n+m ∧
    Set.InjOn Prod.snd (slots (n+m) C L : Set (ℕ × ℕ)) ∧
    (slots (n+m) C L).card + 1 = 2 * L.card := by
  classical
  have hrows := missing_rows_le hi hA hL hr ho
  have hcols := missing_cols_le hj hA hL hr ho
  have hp := input_partition n m C L
  have hl := slots_count_low hr huse
  have hh := slots_count_high hL hC hNot
  have hm := Finset.card_image_le (s := slots (n+m) C L) (f := Prod.snd)
  change (used (n+m) C L).card ≤ (slots (n+m) C L).card at hm
  have hLf : L ⊆ Finset.range C.size := fun _ hj => Finset.mem_range.mpr (hL.1 _ hj)
  have hLc : L.card ≤ C.size := by simpa using Finset.card_le_card hLf
  have hpos := Finset.card_pos.mpr ⟨r,hr⟩
  refine ⟨by omega, by omega, by omega, ?_, by omega, ?_, by omega⟩
  · exact Finset.eq_of_subset_of_card_le hLf (by simp; omega)
  · exact Finset.injOn_of_card_image_eq (show
      (used (n+m) C L).card = (slots (n+m) C L).card by omega)

theorem positive_or_tight {n m s : ℕ} (A : Fin n → Fin m → Bool)
    (hi : Function.Injective A) (hj : Function.Injective (fun j i => A i j))
    (hsmall : s + 2 ≤ n+m) (C : Circuit) (hC : FanInTwo C)
    (hs : C.size ≤ s) (hA : Represents A C) :
    RepSizeAtMost A s ∨
    ∃ (D : Circuit) (r : ℕ),
      FanInTwo D ∧ Represents A D ∧ D.size = s ∧ s+2 = n+m ∧
      D.output = n+m+r ∧ r ∈ Finset.range D.size ∧
      closed (n+m) D (Finset.range D.size) ∧
      (∀ i ∈ Finset.range D.size, i ≠ r →
        ∃ j ∈ Finset.range D.size, before D (n+m) j (n+m+i)) ∧
      (∀ g ∈ D.gates, g.op = .not → g.inputs.length ≤ 1) ∧
      (activeNot D (Finset.range D.size)).card = 1 ∧
      (missingRows n m D (Finset.range D.size)).card = 1 ∧
      (missingCols n m D (Finset.range D.size)).card = 1 ∧
      Set.InjOn Prod.snd (slots (n+m) D (Finset.range D.size) : Set (ℕ × ℕ)) ∧
      (slots (n+m) D (Finset.range D.size)).card+1 = 2*D.size := by
  classical
  let D := trim C
  have ds : D.size = C.size := by simp [D, trim, Circuit.size]
  have df : FanInTwo D := trim_fan C hC
  have da : Represents A D := fun i j => (trim_eval C _).trans (hA i j)
  by_cases hraw : D.output < n+m
  · left
    refine ⟨⟨[], D.output⟩, by simp [Monotone2], by simp [Circuit.size], ?_⟩
    intro i j
    rw [← da i j]
    change (oneEach i j).getD D.output false =
      (D.gates.foldl step (oneEach i j)).getD D.output false
    exact (pre _ _ _ (by simpa [oneEach] using hraw)).symm
  by_cases hout : D.output < n+m+D.size
  · let r := D.output - (n+m)
    have ho : D.output = n+m+r := by dsimp [r]; omega
    have hr : r < D.gates.length := by change r < D.size; omega
    obtain ⟨L,hrL,hL,hu⟩ := minimal_closed (n+m) D r hr
    by_cases hn : (activeNot D L).card = 0
    · left
      obtain ⟨E,em,ea,es⟩ := noNotCircuit df hL hrL ho hn da
      exact ⟨E,em,by omega,ea⟩
    · right
      obtain ⟨nt,mr,mc,full,sz,inj,slots⟩ :=
        tight_count hi hj da hL hrL ho hu df (trim_unary C)
          (by omega) (Nat.pos_of_ne_zero hn)
      have eqs : D.size = s := by omega
      refine ⟨D,r,df,da,eqs,by omega,ho,?_,?_,?_,trim_unary C,?_,?_,?_,?_,?_⟩
      all_goals rw [← full]
      · exact hrL
      · exact hL
      · exact hu
      · exact nt
      · exact mr
      · exact mc
      · exact inj
      · simpa [full] using slots
  · left
    refine ⟨⟨[], n+m⟩, by simp [Monotone2], by simp [Circuit.size], ?_⟩
    intro i j
    rw [← da i j]
    change (oneEach i j).getD (n+m) false =
      (D.gates.foldl step (oneEach i j)).getD D.output false
    rw [getD_ge _ _ (by simp [oneEach]), getD_ge _ _ (by
      rw [len]; simp only [oneEach, List.length_append, List.length_ofFn]; exact Nat.le_of_not_gt hout)]

end PEqualNP.Outside.L_meta_29776_aux
namespace PEqualNP.Outside.L_meta_29776_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem mono_fan {C : Circuit} (h : Monotone2 C) : FanInTwo C := by
  intro g hg
  obtain ⟨hop, hs⟩ := h g hg
  refine ⟨?_, hs⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
  tauto

def shift (n i : ℕ) : ℕ := if i < n then i else i+1

def shiftGate (n : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (shift n)⟩

def shiftCircuit (n : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.map (shiftGate n), shift n C.output⟩

theorem shift_below {n i k : ℕ} (hn : n ≤ k) : shift n i < k+1 ↔ i < k := by
  unfold shift
  split_ifs <;> omega

theorem shift_at {n i k : ℕ} (hn : n ≤ k) : shift n i = k+1 ↔ i = k := by
  unfold shift
  split_ifs <;> omega

theorem shift_fold (n : ℕ) (gs : List Gate) (x y : List Bool)
    (hn : n ≤ x.length) (hl : y.length = x.length+1)
    (h : ∀ i, y.getD (shift n i) false = x.getD i false) :
    ∀ i, ((gs.map (shiftGate n)).foldl step y).getD (shift n i) false =
      (gs.foldl step x).getD i false := by
  induction gs generalizing x y with
  | nil => exact h
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    have hc : compute y (shiftGate n g) = compute x g := by
      simp only [compute, shiftGate, List.map_map, Function.comp_def, h]
    apply ih _ _ (by simp [step]; omega) (by simp [step, hl])
    intro i
    simp only [step, snoc, hl, hc, shift_below hn, shift_at hn]
    split_ifs <;> simp_all

theorem shift_eval (n : ℕ) (C : Circuit) (x y : List Bool)
    (hn : n ≤ x.length) (hl : y.length = x.length+1)
    (h : ∀ i, y.getD (shift n i) false = x.getD i false) :
    (shiftCircuit n C).eval y = C.eval x :=
  shift_fold n C.gates x y hn hl h C.output

theorem shift_fan (n : ℕ) {C : Circuit} (h : FanInTwo C) :
    FanInTwo (shiftCircuit n C) := by
  intro g hg
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
  simpa [shiftGate] using h a ha

theorem shift_snoc_pair (x : List Bool) (a b : Bool) (i : ℕ) :
    (x ++ [a,b]).getD (shift x.length i) false = (x ++ [b]).getD i false := by
  rw [show x ++ [a,b] = (x ++ [a]) ++ [b] by simp]
  simp only [snoc, List.length_append, List.length_singleton]
  by_cases hi : i < x.length
  · simp [shift,hi,show i < x.length+1 by omega]
  · simp only [shift, if_neg hi]
    split_ifs <;> simp_all <;> omega

def prependNot (w : ℕ) (C : Circuit) : Circuit :=
  ⟨⟨.not, [w]⟩ :: C.gates, C.output⟩

theorem prependNot_fan (w : ℕ) {C : Circuit} (h : FanInTwo C) :
    FanInTwo (prependNot w C) := by
  intro g hg
  rcases List.mem_cons.mp hg with rfl | hg
  · simp
  · exact h g hg

theorem prependNot_eval (w : ℕ) (C : Circuit) (x : List Bool) :
    (prependNot w C).eval x = C.eval (x ++ [!(x.getD w false)]) := rfl

def prependPairNot (n a b : ℕ) (C : Circuit) : Circuit :=
  ⟨⟨.or, [a,b]⟩ :: ⟨.not, [n]⟩ :: (shiftCircuit n C).gates,
    (shiftCircuit n C).output⟩

theorem prependPairNot_fan (n a b : ℕ) {C : Circuit} (h : FanInTwo C) :
    FanInTwo (prependPairNot n a b C) := by
  intro g hg
  rcases List.mem_cons.mp hg with rfl | hg
  · simp
  rcases List.mem_cons.mp hg with rfl | hg
  · simp
  · exact shift_fan n h g hg

theorem prependPairNot_eval (a b : ℕ) (C : Circuit) (x : List Bool) :
    (prependPairNot x.length a b C).eval x =
      C.eval (x ++ [!((x.getD a false) || (x.getD b false))]) := by
  let v := x.getD a false || x.getD b false
  have hv : compute x ⟨.or,[a,b]⟩ = v := by simp [compute, GateOp.eval,v]
  have hn : compute (x ++ [v]) ⟨.not,[x.length]⟩ = !v := by
    simp [compute,GateOp.eval]
  change (((shiftCircuit x.length C).gates).foldl step
    (step (step x ⟨.or,[a,b]⟩) ⟨.not,[x.length]⟩)).getD
      (shiftCircuit x.length C).output false = _
  simp only [step, hv, hn]
  rw [show (x ++ [v]) ++ [!v] = x ++ [v,!v] by simp]
  exact shift_eval x.length C (x ++ [!v]) (x ++ [v,!v])
    (by simp) (by simp) (shift_snoc_pair x v (!v))

def appendGate (n : ℕ) (C : Circuit) (g : Gate) : Circuit :=
  ⟨C.gates ++ [g], n+C.size⟩

theorem appendGate_size (n : ℕ) (C : Circuit) (g : Gate) :
    (appendGate n C g).size = C.size+1 := by simp [appendGate,Circuit.size]

theorem appendGate_fan (n : ℕ) {C : Circuit} (h : FanInTwo C) (g : Gate)
    (ho : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp))
    (hs : g.inputs.length ≤ 2) : FanInTwo (appendGate n C g) := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact h a ha
  · simpa using (List.mem_singleton.mp ha) ▸ And.intro ho hs

theorem appendGate_eval (C : Circuit) (g : Gate) (x : List Bool) :
    (appendGate x.length C g).eval x = compute (C.wires x) g := by
  change ((C.gates ++ [g]).foldl step x).getD (x.length+C.size) false = _
  rw [List.foldl_append]
  simp only [List.foldl_cons,List.foldl_nil,step,snoc,len,Circuit.size,lt_self_iff_false,
    if_false,ite_true]
  rfl

theorem appendNot_eval (C : Circuit) (x : List Bool) :
    (appendGate x.length C ⟨.not,[C.output]⟩).eval x = !(C.eval x) := by
  rw [appendGate_eval]
  rfl

theorem appendOr_eval (C : Circuit) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (appendGate x.length C ⟨.or,[C.output,w]⟩).eval x =
      (C.eval x || x.getD w false) := by
  rw [appendGate_eval]
  change ((C.wires x).getD C.output false || ((C.wires x).getD w false || false)) = _
  rw [Bool.or_false]
  change (C.eval x || (C.gates.foldl step x).getD w false) = _
  rw [pre _ _ _ hw]

theorem each_left {n m : ℕ} (i k : Fin n) (j : Fin m) :
    (oneEach i j).getD k.val false = decide (i = k) := by
  rw [each_value]
  have hk := k.isLt
  have hj := j.isLt
  simp [show k.val ≠ n+j.val by omega,Fin.ext_iff,eq_comm]

theorem each_right {n m : ℕ} (i : Fin n) (j k : Fin m) :
    (oneEach i j).getD (n+k.val) false = decide (j = k) := by
  rw [each_value]
  have hi := i.isLt
  simp [show n+k.val ≠ i.val by omega,Fin.ext_iff,eq_comm]

theorem small_finset {α : Type} (S : Finset α) (h : S.card ≤ 1) :
    S = ∅ ∨ ∃ a, S = {a} := by
  by_cases hz : S.card = 0
  · exact Or.inl (Finset.card_eq_zero.mp hz)
  · exact Or.inr (Finset.card_eq_one.mp (by omega))

theorem absence_converse {n m s : ℕ} {A : Fin n → Fin m → Bool}
    (R : Finset (Fin n)) (K : Finset (Fin m)) (G : Circuit)
    (hr : R.card ≤ 1) (hk : K.card ≤ 1) (hg : Monotone2 G)
    (hp : 0 < R.card+K.card) (hs : G.size+R.card+K.card ≤ s)
    (he : ∀ i j, A i j = G.eval (oneEach i j ++ [decide (i ∉ R ∧ j ∉ K)])) :
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ s ∧ Represents A C := by
  classical
  have rshape := small_finset R hr
  have kshape := small_finset K hk
  rcases rshape with rfl | ⟨r,rfl⟩
  · rcases kshape with rfl | ⟨k,rfl⟩
    · simp at hp
    · refine ⟨prependNot (n+k.val) G,prependNot_fan _ (mono_fan hg),?_,?_⟩
      · simpa [prependNot,Circuit.size] using hs
      · intro i j
        rw [he,prependNot_eval,each_right]
        congr 2
        simp
  · rcases kshape with rfl | ⟨k,rfl⟩
    · refine ⟨prependNot r.val G,prependNot_fan _ (mono_fan hg),?_,?_⟩
      · simpa [prependNot,Circuit.size] using hs
      · intro i j
        rw [he,prependNot_eval,each_left]
        congr 2
        simp
    · refine ⟨prependPairNot (n+m) r.val (n+k.val) G,
        prependPairNot_fan _ _ _ (mono_fan hg),?_,?_⟩
      · simpa [prependPairNot,shiftCircuit,Circuit.size,Nat.add_assoc,Nat.add_comm,
          Nat.add_left_comm] using hs
      · intro i j
        have hl : (oneEach i j).length = n+m := by simp [oneEach]
        rw [he,← hl,prependPairNot_eval,each_left,each_right]
        congr 2
        simp

def suffixOr (n : ℕ) (C : Circuit) : List ℕ → Circuit
  | [] => C
  | w :: ws => suffixOr n (appendGate n C ⟨.or,[C.output,w]⟩) ws

theorem suffixOr_size (n : ℕ) (ws : List ℕ) (C : Circuit) :
    (suffixOr n C ws).size = C.size+ws.length := by
  induction ws generalizing C with
  | nil => simp [suffixOr]
  | cons w ws ih => simp [suffixOr,ih,appendGate_size,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem suffixOr_fan (n : ℕ) (ws : List ℕ) (C : Circuit) (h : FanInTwo C) :
    FanInTwo (suffixOr n C ws) := by
  induction ws generalizing C with
  | nil => exact h
  | cons w ws ih => exact ih _ (appendGate_fan n h _ (by simp) (by simp))

theorem suffixOr_eval (ws : List ℕ) (C : Circuit) (x : List Bool)
    (h : ∀ w ∈ ws, w < x.length) :
    (suffixOr x.length C ws).eval x = (C.eval x || ws.any (fun w => x.getD w false)) := by
  induction ws generalizing C with
  | nil => simp [suffixOr]
  | cons w ws ih =>
    rw [suffixOr,ih _ (fun w hw => h w (by simp [hw])),appendOr_eval _ _ _ (h w (by simp))]
    simp [Bool.or_assoc]

theorem finalNot_converse {n m s : ℕ} {A : Fin n → Fin m → Bool}
    (R : Finset (Fin n)) (K : Finset (Fin m)) (G : Circuit)
    (hg : Monotone2 G) (hs : G.size+1+R.card+K.card ≤ s)
    (he : ∀ i j, A i j = (decide (i ∈ R ∨ j ∈ K) || !(G.eval (oneEach i j)))) :
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ s ∧ Represents A C := by
  classical
  let ws := R.toList.map Fin.val ++ K.toList.map (fun j => n+j.val)
  let C := appendGate (n+m) G ⟨.not,[G.output]⟩
  have cf : FanInTwo C := appendGate_fan _ (mono_fan hg) _ (by simp) (by simp)
  refine ⟨suffixOr (n+m) C ws,suffixOr_fan _ _ _ cf,?_,?_⟩
  · simpa [suffixOr_size,C,appendGate_size,ws,Nat.add_assoc] using hs
  · intro i j
    have hl : (oneEach i j).length = n+m := by simp [oneEach]
    have hw : ∀ w ∈ ws, w < (oneEach i j).length := by
      intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hw
        have := a.isLt
        omega
      · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hw
        have := a.isLt
        omega
    have any : ws.any (fun w => (oneEach i j).getD w false) = decide (i ∈ R ∨ j ∈ K) := by
      apply Bool.eq_iff_iff.mpr
      simp only [ws,List.any_append,List.any_map,Function.comp_def,each_left,each_right]
      simp
    rw [← hl,suffixOr_eval _ _ _ hw,any]
    have ce : C.eval (oneEach i j) = !(G.eval (oneEach i j)) := by
      dsimp [C]
      rw [← hl,appendNot_eval]
    rw [ce,he,Bool.or_comm]

theorem budget_reverse {n m s : ℕ} {A : Fin n → Fin m → Bool}
    (h : RepSizeAtMost A s ∨
      ∃ (R : Finset (Fin n)) (K : Finset (Fin m)) (G : Circuit),
        R.card ≤ 1 ∧ K.card ≤ 1 ∧ Monotone2 G ∧
        ((0 < R.card+K.card ∧ G.size+R.card+K.card ≤ s ∧
          ∀ i j, A i j = G.eval (oneEach i j ++ [decide (i ∉ R ∧ j ∉ K)])) ∨
         (G.size+1+R.card+K.card ≤ s ∧
          ∀ i j, A i j = (decide (i ∈ R ∨ j ∈ K) || !(G.eval (oneEach i j)))))) :
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ s ∧ Represents A C := by
  rcases h with ⟨C,hc,hs,ha⟩ | ⟨R,K,G,hr,hk,hg,h⟩
  · exact ⟨C,mono_fan hc,hs,ha⟩
  · rcases h with ⟨hp,hs,he⟩ | ⟨hs,he⟩
    · exact absence_converse R K G hr hk hg hp hs he
    · exact finalNot_converse R K G hg hs he

end PEqualNP.Outside.L_meta_29776_aux
namespace PEqualNP.Outside.L_meta_29776_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover

noncomputable def notCharge (g : Gate) : ℕ := by
  classical
  exact if g.op = .not then 1 else 0

theorem tight_local_shape {N : ℕ} {C : Circuit}
    (fan : FanInTwo C)
    (unary : ∀ g ∈ C.gates, g.op = .not → g.inputs.length ≤ 1)
    (not1 : (activeNot C (Finset.range C.size)).card = 1)
    (total : (slots N C (Finset.range C.size)).card+1 = 2*C.size) :
    ∀ j, j < C.size →
      (gateAt C j).inputs.length + notCharge (gateAt C j) = 2 ∧
      (gateAt C j).inputs.Nodup ∧
      ∀ w ∈ (gateAt C j).inputs, w < N+j := by
  classical
  change ∀ j, j < C.size →
    (gateAt C j).inputs.length + (if (gateAt C j).op = .not then 1 else 0) = 2 ∧
    (gateAt C j).inputs.Nodup ∧ ∀ w ∈ (gateAt C j).inputs, w < N+j
  let L := Finset.range C.size
  change (slots N C L).card+1 = 2*C.size at total
  have mem (j : ℕ) (hj : j < C.size) : gateAt C j ∈ C.gates := by
    rw [gateAt,List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem _
  have cap (j : ℕ) (hj : j < C.size) :
      (inputSlots N C j).card + (if (gateAt C j).op = .not then 1 else 0) ≤ 2 := by
    have hcard : (inputSlots N C j).card ≤ (gateAt C j).inputs.length := by
      unfold inputSlots
      exact Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans (List.toFinset_card_le _))
    by_cases hn : (gateAt C j).op = .not
    · have hlen := unary _ (mem j hj) hn
      simp only [if_pos hn]
      omega
    · simpa [hn] using hcard.trans (fan _ (mem j hj)).2
  have sumle := Finset.card_biUnion_le (s := L) (t := inputSlots N C)
  change (slots N C L).card ≤ ∑ j ∈ L, (inputSlots N C j).card at sumle
  have ns : (∑ j ∈ L, if (gateAt C j).op = .not then 1 else 0) = 1 := by
    rw [← Finset.card_filter]
    exact not1
  have sumtotal : 2*C.size ≤
      ∑ j ∈ L, ((inputSlots N C j).card + if (gateAt C j).op = .not then 1 else 0) := by
    rw [Finset.sum_add_distrib,ns]
    omega
  have full (j : ℕ) (hj : j < C.size) :
      (inputSlots N C j).card + (if (gateAt C j).op = .not then 1 else 0) = 2 := by
    have hjL : j ∈ L := Finset.mem_range.mpr hj
    have split := Finset.sum_erase_add L
      (fun j => (inputSlots N C j).card + if (gateAt C j).op = .not then 1 else 0) hjL
    have rest : (∑ j ∈ L.erase j, ((inputSlots N C j).card +
        if (gateAt C j).op = .not then 1 else 0)) ≤ (L.card-1)*2 := by
      calc
        _ ≤ ∑ _ ∈ L.erase j, (2 : ℕ) := Finset.sum_le_sum
          (fun k hk => cap k (Finset.mem_range.mp (Finset.mem_of_mem_erase hk)))
        _ = _ := by simp [Finset.card_erase_of_mem hjL]
    have := cap j hj
    have lc : L.card = C.size := Finset.card_range _
    omega
  intro j hj
  have hcard : (inputSlots N C j).card = ((gateAt C j).inputs.toFinset.filter (· < N+j)).card := by
    unfold inputSlots
    exact Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h)
  have hfilter := Finset.card_filter_le (gateAt C j).inputs.toFinset (· < N+j)
  have hnodup := List.toFinset_card_le (gateAt C j).inputs
  have hfull := full j hj
  have hlen := (fan _ (mem j hj)).2
  have exactlen : (gateAt C j).inputs.length +
      (if (gateAt C j).op = .not then 1 else 0) = 2 := by
    by_cases hn : (gateAt C j).op = .not
    · have h1 := unary _ (mem j hj) hn
      simp only [if_pos hn] at hfull ⊢
      omega
    · simp only [if_neg hn] at hfull ⊢
      omega
  have eqcard : (gateAt C j).inputs.toFinset.card = (gateAt C j).inputs.length := by omega
  have filtered : (gateAt C j).inputs.toFinset.filter (· < N+j) =
      (gateAt C j).inputs.toFinset :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
  refine ⟨exactlen, ?_, ?_⟩
  · exact Multiset.toFinset_card_eq_card_iff_nodup.mp eqcard
  · intro w hw
    have := List.mem_toFinset.mpr hw
    rw [← filtered] at this
    exact (Finset.mem_filter.mp this).2

end PEqualNP.Outside.L_meta_29776_aux
namespace PEqualNP.Outside.L_meta_29776_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover

def renamed (ρ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op,g.inputs.map ρ⟩

def emit (n : ℕ) : List (ℕ × Gate) → (ℕ → ℕ) → List Gate → (ℕ → ℕ) × List Gate
  | [], ρ, gs => (ρ,gs)
  | (w,g) :: ps, ρ, gs =>
    emit n ps (Function.update ρ w (n+gs.length)) (gs ++ [renamed ρ g])

def ready : Finset ℕ → List (ℕ × Gate) → Prop
  | _, [] => True
  | S, (w,g) :: ps => (∀ i ∈ g.inputs, i ∈ S) ∧ ready (insert w S) ps

def after : Finset ℕ → List (ℕ × Gate) → Finset ℕ
  | S, [] => S
  | S, (w,_) :: ps => after (insert w S) ps

theorem emit_length (n : ℕ) (ps : List (ℕ × Gate)) (ρ : ℕ → ℕ) (gs : List Gate) :
    (emit n ps ρ gs).2.length = gs.length+ps.length := by
  induction ps generalizing ρ gs with
  | nil => simp [emit]
  | cons p ps ih =>
    rcases p with ⟨w,g⟩
    simp [emit,ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem emit_monotone (n : ℕ) (ps : List (ℕ × Gate)) (ρ : ℕ → ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hp : ∀ p ∈ ps, p.2.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ p.2.inputs.length ≤ 2) :
    ∀ g ∈ (emit n ps ρ gs).2,
      g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction ps generalizing ρ gs with
  | nil => exact hg
  | cons p ps ih =>
    rcases p with ⟨w,g⟩
    apply ih
    · intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hg a ha
      · have he := List.mem_singleton.mp ha
        subst a
        simpa [renamed] using hp (w,g) (by simp)
    · intro p hp'
      exact hp p (List.mem_cons_of_mem _ hp')

theorem emit_sound (ps : List (ℕ × Gate)) (S : Finset ℕ)
    (ν : ℕ → Bool) (x : List Bool) (ρ : ℕ → ℕ) (gs : List Gate)
    (hr : ready S ps)
    (hv : ∀ p ∈ ps, ν p.1 = p.2.op.eval (p.2.inputs.map ν))
    (hρ : ∀ i ∈ S, ρ i < x.length+gs.length ∧
      (gs.foldl step x).getD (ρ i) false = ν i) :
    ∀ i ∈ after S ps,
      (emit x.length ps ρ gs).1 i < x.length+(emit x.length ps ρ gs).2.length ∧
      ((emit x.length ps ρ gs).2.foldl step x).getD ((emit x.length ps ρ gs).1 i) false = ν i := by
  induction ps generalizing S ρ gs with
  | nil => exact hρ
  | cons p ps ih =>
    rcases p with ⟨w,g⟩
    change ∀ i ∈ after (insert w S) ps, _
    apply ih _ _ _ hr.2 (fun p hp => hv p (List.mem_cons_of_mem _ hp))
    intro i hi
    have hcompute : compute (gs.foldl step x) (renamed ρ g) = ν w := by
      rw [hv (w,g) (by simp)]
      unfold compute renamed
      simp only [List.map_map,Function.comp_def]
      congr 1
      apply List.map_congr_left
      intro k hk
      exact (hρ k (hr.1 k hk)).2
    by_cases he : i = w
    · subst i
      simp only [Function.update_self,List.length_append,List.length_singleton,List.foldl_append,
        List.foldl_cons,List.foldl_nil,step,snoc,len,hcompute]
      constructor
      · omega
      · simp
    · have hiS : i ∈ S := (Finset.mem_insert.mp hi).resolve_left he
      have old := hρ i hiS
      rw [Function.update_of_ne he]
      constructor
      · simp only [List.length_append,List.length_singleton]
        omega
      · rw [List.foldl_append]
        simp only [List.foldl_cons,List.foldl_nil,step,snoc,len]
        rw [if_pos old.1]
        exact old.2

theorem extract_circuit (n : ℕ) (ps : List (ℕ × Gate)) (S : Finset ℕ) (ρ : ℕ → ℕ)
    (o : ℕ) (ho : o ∈ after S ps)
    (hr : ready S ps)
    (hp : ∀ p ∈ ps, p.2.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ p.2.inputs.length ≤ 2) :
    ∃ C : Circuit, Monotone2 C ∧ C.size = ps.length ∧
      ∀ (ν : ℕ → Bool) (x : List Bool), x.length = n →
        (∀ p ∈ ps, ν p.1 = p.2.op.eval (p.2.inputs.map ν)) →
        (∀ i ∈ S, ρ i < n ∧ x.getD (ρ i) false = ν i) →
        C.eval x = ν o := by
  let r := emit n ps ρ []
  refine ⟨⟨r.2,r.1 o⟩,?_,?_,?_⟩
  · exact emit_monotone n ps ρ [] (by simp) hp
  · simpa [Circuit.size,r] using emit_length n ps ρ []
  · intro ν x hx hv hρ
    have h := emit_sound ps S ν x ρ [] hr hv (by simpa [hx] using hρ) o ho
    change (r.2.foldl step x).getD (r.1 o) false = ν o
    simpa only [hx,r] using h.2

theorem after_eq (S : Finset ℕ) (ps : List (ℕ × Gate)) :
    after S ps = S ∪ (ps.map Prod.fst).toFinset := by
  induction ps generalizing S with
  | nil => simp [after]
  | cons p ps ih =>
    rcases p with ⟨w,g⟩
    simp [after,ih,Finset.insert_union,Finset.union_insert]

theorem ready_of_order (S : Finset ℕ) (ps : List (ℕ × Gate))
    (order : ps.Pairwise (fun p q => p.1 < q.1))
    (deps : ∀ p ∈ ps, ∀ w ∈ p.2.inputs,
      w ∈ S ∨ ∃ q ∈ ps, q.1 = w ∧ q.1 < p.1) : ready S ps := by
  induction ps generalizing S with
  | nil => trivial
  | cons p ps ih =>
    rcases p with ⟨u,g⟩
    obtain ⟨first,rest⟩ := List.pairwise_cons.mp order
    constructor
    · intro w hw
      rcases deps (u,g) (by simp) w hw with hw | ⟨q,hq,hqw,hqu⟩
      · exact hw
      · rcases List.mem_cons.mp hq with rfl | hq
        · omega
        · have := first q hq
          omega
    · apply ih _ rest
      intro p hp w hw
      rcases deps p (List.mem_cons_of_mem _ hp) w hw with hw | ⟨q,hq,hqw,hqp⟩
      · exact Or.inl (Finset.mem_insert_of_mem hw)
      · rcases List.mem_cons.mp hq with rfl | hq
        · left
          exact Finset.mem_insert.mpr (Or.inl hqw.symm)
        · exact Or.inr ⟨q,hq,hqw,hqp⟩

theorem extract_selected (N N' : ℕ) (C : Circuit) (J S : Finset ℕ) (ρ : ℕ → ℕ) (o : ℕ)
    (ho : o ∈ S ∨ ∃ j ∈ J, o = N+j)
    (dep : ∀ j ∈ J, ∀ w ∈ (gateAt C j).inputs,
      w ∈ S ∨ ∃ k ∈ J, w = N+k ∧ k < j)
    (mono : ∀ j ∈ J, (gateAt C j).op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧
      (gateAt C j).inputs.length ≤ 2) :
    ∃ G : Circuit, Monotone2 G ∧ G.size = J.card ∧
      ∀ (ν : ℕ → Bool) (x : List Bool), x.length = N' →
        (∀ j ∈ J, ν (N+j) = (gateAt C j).op.eval ((gateAt C j).inputs.map ν)) →
        (∀ i ∈ S, ρ i < N' ∧ x.getD (ρ i) false = ν i) →
        G.eval x = ν o := by
  classical
  let ps := J.sort.map (fun j => (N+j,gateAt C j))
  have mem (p : ℕ × Gate) : p ∈ ps ↔ ∃ j ∈ J, p = (N+j,gateAt C j) := by
    simp only [ps,List.mem_map,Finset.mem_sort]
    constructor
    · rintro ⟨j,hj,rfl⟩
      exact ⟨j,hj,rfl⟩
    · rintro ⟨j,hj,rfl⟩
      exact ⟨j,hj,rfl⟩
  have hp : ready S ps := by
    apply ready_of_order
    · rw [List.pairwise_map]
      exact (Finset.sortedLT_sort J).pairwise.imp (by intros; dsimp; omega)
    · intro p hp w hw
      obtain ⟨j,hj,rfl⟩ := (mem p).mp hp
      rcases dep j hj w hw with hw | ⟨k,hk,hkw,hkj⟩
      · exact Or.inl hw
      · exact Or.inr ⟨(N+k,gateAt C k),(mem _).mpr ⟨k,hk,rfl⟩,hkw.symm,by dsimp; omega⟩
  have hpo : o ∈ after S ps := by
    rw [after_eq]
    rcases ho with ho | ⟨j,hj,rfl⟩
    · exact Finset.mem_union_left _ ho
    · apply Finset.mem_union_right
      apply List.mem_toFinset.mpr
      exact List.mem_map.mpr ⟨(N+j,gateAt C j),(mem _).mpr ⟨j,hj,rfl⟩,rfl⟩
  obtain ⟨G,gm,gs,ge⟩ := extract_circuit N' ps S ρ o hpo hp (by
    intro p hp
    obtain ⟨j,hj,rfl⟩ := (mem p).mp hp
    exact mono j hj)
  refine ⟨G,gm,by simpa [ps] using gs,?_⟩
  intro ν x hx hv hi
  apply ge ν x hx _ hi
  intro p hp
  obtain ⟨j,hj,rfl⟩ := (mem p).mp hp
  exact hv j hj

end PEqualNP.Outside.L_meta_29776_aux

namespace PEqualNP.Outside.L_meta_29776_aux
namespace Network
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover
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
end PEqualNP.Outside.L_meta_29776_aux
namespace PEqualNP.Outside.L_meta_29776_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover Network

noncomputable def innerGates (N : ℕ) (C : Circuit) (f : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range C.size).filter fun j =>
    reaches N C (Finset.range C.size) (N+j) f ∧ N+j ≠ f

noncomputable def outerGates (N : ℕ) (C : Circuit) (f : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range C.size).filter fun j =>
    ¬ reaches N C (Finset.range C.size) (N+j) f

noncomputable def innerInputs (N : ℕ) (C : Circuit) (f : ℕ) : Finset ℕ := by
  classical
  exact (rawUsed N C (Finset.range C.size)).filter fun w =>
    reaches N C (Finset.range C.size) w f

noncomputable def outerInputs (N : ℕ) (C : Circuit) (f : ℕ) : Finset ℕ := by
  classical
  exact (rawUsed N C (Finset.range C.size)).filter fun w =>
    ¬ reaches N C (Finset.range C.size) w f

theorem cut_circuits (N : ℕ) (C : Circuit) (f u : ℕ)
    (hf : f < C.size) (fu : (gateAt C f).inputs = [u])
    (back : ∀ j, j < C.size → ∀ w ∈ (gateAt C j).inputs, w < N+j)
    (nonempty : ∀ j, j < C.size → (gateAt C j).inputs ≠ [])
    (fan : FanInTwo C)
    (onlyNot : ∀ j, j < C.size → j ≠ f →
      (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or)
    (unique : Set.InjOn Prod.snd (slots N C (Finset.range C.size) : Set (ℕ × ℕ)))
    (out : N+f ≤ C.output) (outreal : C.output < N+C.size) :
    ∃ I O : Circuit,
      Monotone2 I ∧ Monotone2 O ∧
      I.size = (innerGates N C (N+f)).card ∧
      O.size = (outerGates N C (N+f)).card ∧
      (∀ x : List Bool, x.length = N →
        I.eval x = value N C (fun i => x.getD i false) (fun _ => none) u) ∧
      (∀ (x : List Bool) (b : Bool), x.length = N →
        O.eval (x ++ [b]) =
          value N C (fun i => x.getD i false) (relay (N+f) b) C.output) ∧
      I.eval (List.replicate N false) = false ∧
      O.eval (List.replicate (N+1) false) = false ∧
      (∀ x y : List Bool, x.length = N → y.length = N →
        (∀ w ∈ innerInputs N C (N+f), x.getD w false = y.getD w false) →
        I.eval x = I.eval y) ∧
      (∀ (x y : List Bool) (b : Bool), x.length = N → y.length = N →
        (∀ w ∈ outerInputs N C (N+f), x.getD w false = y.getD w false) →
        O.eval (x ++ [b]) = O.eval (y ++ [b])) := by
  classical
  let L := Finset.range C.size
  let J := innerGates N C (N+f)
  let H := outerGates N C (N+f)
  let S := innerInputs N C (N+f)
  let T := outerInputs N C (N+f)
  have jm (j : ℕ) : j ∈ J ↔ j < C.size ∧ reaches N C L (N+j) (N+f) ∧ j ≠ f := by
    simp [J,innerGates,L]
  have hm (j : ℕ) : j ∈ H ↔ j < C.size ∧ ¬ reaches N C L (N+j) (N+f) := by
    simp [H,outerGates,L]
  have sm (w : ℕ) : w ∈ S ↔
      (w ∈ used N C L ∧ w < N) ∧ reaches N C L w (N+f) := by
    simp [S,innerInputs,rawUsed,L]
  have tm (w : ℕ) : w ∈ T ↔
      (w ∈ used N C L ∧ w < N) ∧ ¬ reaches N C L w (N+f) := by
    simp [T,outerInputs,rawUsed,L]
  have eu : edgeTo N C L u (N+f) :=
    ⟨f,Finset.mem_range.mpr hf,rfl,by simp [before,fu],back f hf u (by simp [fu])⟩
  have pu : reaches N C L u (N+f) := .single eu
  have ub : u < N+f := back f hf u (by simp [fu])
  have uniqueEdge (a b c : ℕ) (hb : edgeTo N C L a b) (hc : edgeTo N C L a c) : b = c := by
    obtain ⟨j,hj,rfl,hb⟩ := hb
    obtain ⟨k,hk,rfl,hc⟩ := hc
    have e := unique_reader_of_inj unique hj hk hb hc
    omega
  have jdep : ∀ j ∈ J, ∀ w ∈ (gateAt C j).inputs,
      w ∈ S ∨ ∃ k ∈ J, w = N+k ∧ k < j := by
    intro j hj w hw
    obtain ⟨hj,hp,ne⟩ := (jm j).mp hj
    have wb := back j hj w hw
    have ew : edgeTo N C L w (N+j) := ⟨j,Finset.mem_range.mpr hj,rfl,hw,wb⟩
    have wp : reaches N C L w (N+f) := .head ew hp
    have wu : w ∈ used N C L := mem_used.mpr ⟨j,Finset.mem_range.mpr hj,hw,wb⟩
    by_cases wn : w < N
    · exact Or.inl ((sm w).mpr ⟨⟨wu,wn⟩,wp⟩)
    · have klt : w-N < j := by omega
      have we : w = N+(w-N) := by omega
      have jf := reachIncreases hp
      right
      refine ⟨w-N,(jm _).mpr ⟨by omega,?_,by omega⟩,we,klt⟩
      simpa only [← we] using wp
  have hdep : ∀ j ∈ H, ∀ w ∈ (gateAt C j).inputs,
      w ∈ insert (N+f) T ∨ ∃ k ∈ H, w = N+k ∧ k < j := by
    intro j hj w hw
    obtain ⟨hj,hp⟩ := (hm j).mp hj
    have wb := back j hj w hw
    have ew : edgeTo N C L w (N+j) := ⟨j,Finset.mem_range.mpr hj,rfl,hw,wb⟩
    have wu : w ∈ used N C L := mem_used.mpr ⟨j,Finset.mem_range.mpr hj,hw,wb⟩
    by_cases wf : w = N+f
    · exact Or.inl (Finset.mem_insert.mpr (Or.inl wf))
    have wp : ¬ reaches N C L w (N+f) := fun p =>
      hp (no_leak (fun a _ b c => uniqueEdge a b c) ew p wf)
    by_cases wn : w < N
    · exact Or.inl (Finset.mem_insert_of_mem ((tm w).mpr ⟨⟨wu,wn⟩,wp⟩))
    · have klt : w-N < j := by omega
      have we : w = N+(w-N) := by omega
      refine Or.inr ⟨w-N,(hm _).mpr ⟨by omega,?_⟩,we,klt⟩
      simpa only [← we] using wp
  have jmono : ∀ j ∈ J, (gateAt C j).op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧
      (gateAt C j).inputs.length ≤ 2 := by
    intro j hj
    obtain ⟨hj,hp,ne⟩ := (jm j).mp hj
    have mem : gateAt C j ∈ C.gates := by
      rw [gateAt,List.getD_eq_getElem _ _ hj]; exact List.getElem_mem _
    exact ⟨by simpa using onlyNot j hj ne,(fan _ mem).2⟩
  have hmono : ∀ j ∈ H, (gateAt C j).op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧
      (gateAt C j).inputs.length ≤ 2 := by
    intro j hj
    obtain ⟨hj,hp⟩ := (hm j).mp hj
    have ne : j ≠ f := by rintro rfl; exact hp .refl
    have mem : gateAt C j ∈ C.gates := by
      rw [gateAt,List.getD_eq_getElem _ _ hj]; exact List.getElem_mem _
    exact ⟨by simpa using onlyNot j hj ne,(fan _ mem).2⟩
  have iu : u ∈ S ∨ ∃ j ∈ J, u = N+j := by
    by_cases un : u < N
    · exact Or.inl ((sm u).mpr ⟨⟨mem_used.mpr ⟨f,Finset.mem_range.mpr hf,by simp [before,fu],ub⟩,un⟩,pu⟩)
    · have ue : u = N+(u-N) := by omega
      exact Or.inr ⟨u-N,(jm _).mpr ⟨by omega,by simpa only [← ue] using pu,by omega⟩,ue⟩
  have oo : C.output ∈ insert (N+f) T ∨ ∃ j ∈ H, C.output = N+j := by
    by_cases of : C.output = N+f
    · exact Or.inl (Finset.mem_insert.mpr (Or.inl of))
    · have oe : C.output = N+(C.output-N) := by omega
      refine Or.inr ⟨C.output-N,(hm _).mpr ⟨by omega,?_⟩,oe⟩
      intro p
      have le := reachIncreases p
      omega
  obtain ⟨I,im,is,ie⟩ := extract_selected N N C J S id u iu jdep jmono
  let ρ := fun w => if w = N+f then N else w
  obtain ⟨O,om,os,oe⟩ := extract_selected N (N+1) C H (insert (N+f) T) ρ C.output oo hdep hmono
  have gateZero (j : ℕ) (hj : j < C.size)
      (pos : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) :
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun _ => false) = false := by
    have ne := nonempty j hj
    rcases hi : (gateAt C j).inputs with _ | ⟨a,as⟩
    · exact (ne hi).elim
    · rcases pos with pos | pos <;> simp [pos,GateOp.eval]
  have ih (x : List Bool) (hx : x.length = N) (y : List Bool) (hy : y.length = N)
      (agree : ∀ w ∈ S, y.getD w false = x.getD w false) :
      I.eval y = value N C (fun i => x.getD i false) (fun _ => none) u := by
    apply ie _ y hy
    · intro j hj
      have jh := ((jm j).mp hj).1
      rw [val_gate jh rfl]
      congr 1
      apply List.map_congr_left
      intro w hw
      rw [if_pos (back j jh w hw)]
    · intro w hw
      have wn := ((sm w).mp hw).1.2
      refine ⟨wn,?_⟩
      rw [val_raw wn rfl]
      exact agree w hw
  have oh (x : List Bool) (hx : x.length = N) (y : List Bool) (hy : y.length = N)
      (b : Bool) (agree : ∀ w ∈ T, y.getD w false = x.getD w false) :
      O.eval (y ++ [b]) = value N C (fun i => x.getD i false) (relay (N+f) b) C.output := by
    apply oe _ (y ++ [b]) (by simp [hy])
    · intro j hj
      have jh := ((hm j).mp hj).1
      have jn : j ≠ f := by intro eq; apply ((hm j).mp hj).2; rw [eq]
      rw [val_gate jh (by simp [relay,jn])]
      congr 1
      apply List.map_congr_left
      intro w hw
      rw [if_pos (back j jh w hw)]
    · intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · simp only [ρ,ite_true]
        refine ⟨by omega,?_⟩
        rw [val_relay,snoc,hy]
        simp
      · have wn := ((tm w).mp hw).1.2
        have ne : w ≠ N+f := by omega
        simp only [ρ,if_neg ne]
        refine ⟨by omega,?_⟩
        rw [val_raw wn (by simp [relay,ne]),snoc,hy,if_pos wn]
        exact agree w hw
  refine ⟨I,O,im,om,is,os,?_,?_,?_,?_,?_,?_⟩
  · intro x hx
    apply ie _ x hx
    · intro j hj
      have jh := ((jm j).mp hj).1
      rw [val_gate jh rfl]
      congr 1
      apply List.map_congr_left
      intro w hw
      rw [if_pos (back j jh w hw)]
    · intro w hw
      have wn := ((sm w).mp hw).1.2
      exact ⟨wn,by rw [val_raw wn rfl]; rfl⟩
  · intro x b hx
    apply oe _ (x ++ [b]) (by simp [hx])
    · intro j hj
      have jh := ((hm j).mp hj).1
      have jn : j ≠ f := by
        intro eq
        apply ((hm j).mp hj).2
        rw [eq]
      rw [val_gate jh (by simp [relay,jn])]
      congr 1
      apply List.map_congr_left
      intro w hw
      rw [if_pos (back j jh w hw)]
    · intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · simp only [ρ,ite_true]
        refine ⟨by omega,?_⟩
        rw [val_relay,snoc,hx]
        simp
      · have wn := ((tm w).mp hw).1.2
        have ne : w ≠ N+f := by omega
        simp only [ρ,if_neg ne]
        refine ⟨by omega,?_⟩
        rw [val_raw wn (by simp [relay,ne]),snoc,hx,if_pos wn]
  · apply ie (fun _ => false) _ (by simp)
    · intro j hj
      obtain ⟨jh,jp,jn⟩ := (jm j).mp hj
      exact (gateZero j jh (onlyNot j jh jn)).symm
    · intro w hw
      refine ⟨((sm w).mp hw).1.2,?_⟩
      simp [List.getD_eq_getElem?_getD]
  · apply oe (fun _ => false) _ (by simp)
    · intro j hj
      obtain ⟨jh,jp⟩ := (hm j).mp hj
      have jn : j ≠ f := by intro eq; apply jp; rw [eq]
      exact (gateZero j jh (onlyNot j jh jn)).symm
    · intro w hw
      have bound : ρ w < N+1 := by
        rcases Finset.mem_insert.mp hw with rfl | hw
        · simp [ρ]
        · have wn := ((tm w).mp hw).1.2
          simp only [ρ]
          split_ifs <;> omega
      exact ⟨bound,by simp [List.getD_eq_getElem?_getD]⟩
  · intro x y hx hy agree
    exact (ih x hx x hx (by simp)).trans (ih x hx y hy (fun w hw => (agree w hw).symm)).symm
  · intro x y b hx hy agree
    exact (oh x hx x hx b (by simp)).trans (oh x hx y hy b (fun w hw => (agree w hw).symm)).symm

end PEqualNP.Outside.L_meta_29776_aux
namespace PEqualNP.Outside.L_meta_29776_aux

def bits2 (S : Finset ℕ) (a b : ℕ) : Finset ℕ :=
  (if a ∈ S then {a} else ∅) ∪ (if b ∈ S then {b} else ∅)

theorem bits2_comm (S : Finset ℕ) (a b : ℕ) : bits2 S a b = bits2 S b a := by
  simp [bits2,Finset.union_comm]

theorem bits2_inter (S : Finset ℕ) (a b : ℕ) : bits2 S a b = {a,b} ∩ S := by
  ext w
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> simp [bits2,ha,hb] <;> tauto

theorem false_corner_line {α β : Type} (A : α → β → Bool) (a : α → ℕ) (b : β → ℕ)
    (S T : Finset ℕ) (F : Finset ℕ → Bool) (H : Finset ℕ → Bool → Bool)
    (dis : Disjoint S T) (i₀ : α) (a₀S : a i₀ ∉ S) (a₀T : a i₀ ∉ T)
    (inj : Function.Injective A) (fz : F ∅ = false)
    (hz : ∀ v, H ∅ v = false)
    (eval : ∀ i j, A i j = H (bits2 T (a i) (b j)) (!(F (bits2 S (a i) (b j))))) :
    (∀ i, a i ∈ S → F {a i} = true) ∧
      ∀ i k, a i ∈ S → a k ∈ S → i = k := by
  have noT : ∀ w ∈ S, w ∉ T := fun w hw => Finset.disjoint_left.mp dis hw
  have singles : ∀ i, a i ∈ S → F {a i} = true := by
    intro i hi
    cases e : F {a i} with
    | true => rfl
    | false =>
      have eq : A i = A i₀ := by
        funext j
        rw [eval,eval]
        by_cases bj : b j ∈ S
        · simp [bits2,hi,noT _ hi,bj,noT _ bj,a₀S,a₀T,hz]
        · simp [bits2,hi,noT _ hi,bj,a₀S,a₀T,e,fz]
      have same := inj eq
      exact (a₀S (same ▸ hi)).elim
  refine ⟨singles,?_⟩
  intro i k hi hk
  apply inj
  funext j
  rw [eval,eval]
  by_cases bj : b j ∈ S
  · simp [bits2,hi,hk,noT _ hi,noT _ hk,bj,noT _ bj,hz]
  · simp [bits2,hi,hk,noT _ hi,noT _ hk,bj,singles i hi,singles k hk]

theorem false_corner_eval (a b : ℕ) (S T : Finset ℕ)
    (F : Finset ℕ → Bool) (H : Finset ℕ → Bool → Bool)
    (dis : Disjoint S T) (fz : F ∅ = false)
    (hz : ∀ v, H ∅ v = false)
    (sa : a ∈ S → F {a} = true) (sb : b ∈ S → F {b} = true) :
    H (bits2 T a b) (!(F (bits2 S a b))) =
      H (bits2 T a b) (decide (a ∉ S ∧ b ∉ S)) := by
  have noT : ∀ w ∈ S, w ∉ T := fun w hw => Finset.disjoint_left.mp dis hw
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S
  · simp [bits2,ha,hb,noT _ ha,noT _ hb,hz]
  · simp [bits2,ha,hb,sa ha]
  · simp [bits2,ha,hb,sb hb]
  · simp [bits2,ha,hb,fz]

def increasingPort (H : Finset ℕ → Bool → Bool) : Prop :=
  ∀ X Y, X ⊆ Y → ∀ b c, (b = true → c = true) → H X b = true → H Y c = true

theorem true_corner_line {α β : Type} (A : α → β → Bool) (a : α → ℕ) (b : β → ℕ)
    (S T : Finset ℕ) (F : Finset ℕ → Bool) (H : Finset ℕ → Bool → Bool)
    (dis : Disjoint S T) (i₀ : α) (a₀S : a i₀ ∉ S) (a₀T : a i₀ ∉ T)
    (inj : Function.Injective A) (fz : F ∅ = false)
    (h00 : H ∅ false = false) (h01 : H ∅ true = true) (hm : increasingPort H)
    (eval : ∀ i j, A i j = H (bits2 T (a i) (b j)) (!(F (bits2 S (a i) (b j))))) :
    (∀ i, a i ∈ T → H {a i} false = true) ∧
      ∀ i k, a i ∈ T → a k ∈ T → i = k := by
  have noS : ∀ w ∈ T, w ∉ S := fun w hw hs => Finset.disjoint_left.mp dis hs hw
  have top (X : Finset ℕ) : H X true = true :=
    hm ∅ X (Finset.empty_subset _) true true id h01
  have singles : ∀ i, a i ∈ T → H {a i} false = true := by
    intro i hi
    cases e : H {a i} false with
    | true => rfl
    | false =>
      have singletonEq (v : Bool) : H {a i} v = H ∅ v := by
        cases v <;> simp [e,h00,top]
      have eq : A i = A i₀ := by
        funext j
        rw [eval,eval]
        by_cases bj : b j ∈ T
        · simp [bits2,hi,noS _ hi,bj,noS _ bj,a₀S,a₀T,fz,top]
        · simp [bits2,hi,noS _ hi,bj,a₀S,a₀T,singletonEq]
      have same := inj eq
      exact (a₀T (same ▸ hi)).elim
  refine ⟨singles,?_⟩
  have full (i : α) (hi : a i ∈ T) (j : β) : A i j = true := by
    rw [eval]
    apply hm {a i} _ (by simp [bits2,hi]) false _ (by simp) (singles i hi)
  intro i k hi hk
  apply inj
  funext j
  rw [full i hi j,full k hk j]

theorem true_corner_eval (a b : ℕ) (T : Finset ℕ) (v : Bool)
    (H : Finset ℕ → Bool → Bool) (h00 : H ∅ false = false) (h01 : H ∅ true = true)
    (hm : increasingPort H)
    (sa : a ∈ T → H {a} false = true) (sb : b ∈ T → H {b} false = true) :
    H (bits2 T a b) v = (decide (a ∈ T ∨ b ∈ T) || v) := by
  by_cases ha : a ∈ T
  · have hv : H (bits2 T a b) v = true :=
      hm {a} _ (by simp [bits2,ha]) false v (by simp) (sa ha)
    simp [hv,ha]
  by_cases hb : b ∈ T
  · have hv : H (bits2 T a b) v = true :=
      hm {b} _ (by simp [bits2,ha,hb]) false v (by simp) (sb hb)
    simp [hv,hb]
  · cases v <;> simp [bits2,ha,hb,h00,h01]

end PEqualNP.Outside.L_meta_29776_aux
namespace PEqualNP.Outside.L_meta_29776_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def inp (N : ℕ) (P : Finset ℕ) : List Bool := List.ofFn fun i : Fin N => decide (i.val ∈ P)

theorem inp_get (N : ℕ) (P : Finset ℕ) (i : ℕ) :
    (inp N P).getD i false = decide (i < N ∧ i ∈ P) := by
  unfold inp
  by_cases h : i < N <;> simp [List.getD_eq_getElem?_getD,h]

theorem inp_empty (N : ℕ) : inp N ∅ = List.replicate N false := by simp [inp]

theorem each_inp {n m : ℕ} (i : Fin n) (j : Fin m) :
    oneEach i j = inp (n+m) {i.val,n+j.val} := by
  apply List.ext_getElem
  · simp [oneEach,inp]
  · intro w hw hv
    rw [← List.getD_eq_getElem _ false hw,← List.getD_eq_getElem _ false hv,each_value,inp_get]
    have hi := i.isLt
    have hj := j.isLt
    simp only [Finset.mem_insert,Finset.mem_singleton,decide_eq_decide]
    omega

theorem inp_same (N : ℕ) (P Q : Finset ℕ) (h : ∀ i < N, i ∈ P ↔ i ∈ Q) :
    inp N P = inp N Q := by
  apply List.ofFn_inj.mpr
  funext i
  simp only [decide_eq_decide]
  exact h i.val i.isLt

theorem inp_succ (N : ℕ) (P : Finset ℕ) :
    inp (N+1) P = inp N P ++ [decide (N ∈ P)] := by
  apply List.ext_getElem
  · simp [inp]
  · intro i hi hj
    by_cases h : i < N
    · rw [List.getElem_append_left (by simpa [inp] using h)]
      simp only [inp,List.getElem_ofFn]
    · have eq : i = N := by simp [inp] at hi; omega
      subst i
      rw [List.getElem_append_right (by simp [inp])]
      simp only [inp,List.getElem_ofFn,List.length_ofFn,Nat.sub_self,List.getElem_cons_zero]

theorem input_mono (N : ℕ) (P Q : Finset ℕ) (h : P ⊆ Q) :
    Below (inp N P) (inp N Q) := by
  intro i
  rw [inp_get,inp_get]
  simp only [decide_eq_true_eq]
  exact fun ⟨hi,hp⟩ => ⟨hi,h hp⟩

theorem port_mono (N : ℕ) (O : Circuit) (ho : Monotone2 O) :
    increasingPort (fun P b => O.eval (inp N P ++ [b])) := by
  intro P Q hPQ b c hbc h
  apply fold_monotone O.gates (fun g hg => (ho g hg).1)
    (by simp [inp]) _ O.output h
  intro i hi
  have lenP : (inp N P).length = N := by simp [inp]
  have lenQ : (inp N Q).length = N := by simp [inp]
  simp only [snoc,lenP,lenQ] at hi ⊢
  split_ifs at hi ⊢
  · exact input_mono N P Q hPQ i hi
  · exact hbc hi

theorem needed_inputs (gs : List Gate) (hg : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (N : ℕ) (targets : Finset ℕ) :
    ∃ S : Finset ℕ, S.card ≤ targets.card+gs.length ∧
      ∀ x y : List Bool, x.length = N → y.length = N →
        (∀ i ∈ S, x.getD i false = y.getD i false) →
        ∀ i ∈ targets, (gs.foldl step x).getD i false = (gs.foldl step y).getD i false := by
  classical
  induction gs using List.reverseRecOn generalizing targets with
  | nil => exact ⟨targets,by simp,fun _ _ _ _ h => h⟩
  | append_singleton gs g ih =>
    have hgs : ∀ g ∈ gs, g.inputs.length ≤ 2 := fun a ha => hg a (List.mem_append_left _ ha)
    have hg2 := hg g (by simp)
    by_cases hm : N+gs.length ∈ targets
    · obtain ⟨S,hc,hs⟩ := ih hgs (targets.erase (N+gs.length) ∪ g.inputs.toFinset)
      refine ⟨S,?_,?_⟩
      · have h1 := Finset.card_union_le (targets.erase (N+gs.length)) g.inputs.toFinset
        have h2 := Finset.card_erase_of_mem hm
        have h3 := List.toFinset_card_le g.inputs
        have h4 : 0 < targets.card := Finset.card_pos.mpr ⟨_,hm⟩
        simp only [List.length_append,List.length_singleton]
        omega
      · intro x y hx hy h i hi
        have H := hs x y hx hy h
        simp only [List.foldl_append,List.foldl_cons,List.foldl_nil,step,snoc,len,hx,hy]
        split_ifs with hl he
        · exact H i (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨by omega,hi⟩))
        · unfold compute
          congr 1
          apply List.map_congr_left
          intro a ha
          exact H a (Finset.mem_union_right _ (List.mem_toFinset.mpr ha))
        · rfl
    · obtain ⟨S,hc,hs⟩ := ih hgs targets
      refine ⟨S,by simp only [List.length_append,List.length_singleton]; omega,?_⟩
      intro x y hx hy h i hi
      have H := hs x y hx hy h i hi
      have ne : i ≠ N+gs.length := fun e => hm (e ▸ hi)
      simp only [List.foldl_append,List.foldl_cons,List.foldl_nil,step,snoc,len,hx,hy,ne,if_false]
      split_ifs
      · exact H
      · rfl

theorem singleton_bound (N : ℕ) (C : Circuit) (hc : FanInTwo C) (S : Finset ℕ)
    (hz : C.eval (inp N ∅) = false)
    (hs : ∀ i ∈ S, C.eval (inp N {i}) = true) : S.card ≤ C.size+1 := by
  obtain ⟨U,hu,hU⟩ := needed_inputs C.gates (fun g hg => (hc g hg).2) N {C.output}
  have sub : S ⊆ U := by
    intro i hi
    by_contra hn
    have eq := hU (inp N {i}) (inp N ∅) (by simp [inp]) (by simp [inp])
      (fun j hj => by
        rw [inp_get,inp_get]
        have ne : j ≠ i := fun e => hn (e ▸ hj)
        simp [ne]) C.output (by simp)
    change C.eval (inp N {i}) = C.eval (inp N ∅) at eq
    rw [hs i hi,hz] at eq
    cases eq
  have := Finset.card_le_card sub
  simpa [Circuit.size,Nat.add_comm] using this.trans hu

def rowSet (n : ℕ) (S : Finset ℕ) : Finset (Fin n) := Finset.univ.filter fun i => i.val ∈ S
def colSet (n m : ℕ) (S : Finset ℕ) : Finset (Fin m) := Finset.univ.filter fun j => n+j.val ∈ S

theorem vertex_card (n m : ℕ) (S : Finset ℕ) (hs : ∀ w ∈ S, w < n+m) :
    (rowSet n S).card+(colSet n m S).card = S.card := by
  let R := (rowSet n S).image Fin.val
  let K := (colSet n m S).image (fun j => n+j.val)
  have union : R ∪ K = S := by
    ext w
    constructor
    · intro hw
      rcases Finset.mem_union.mp hw with hw | hw
      · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hw
        exact (Finset.mem_filter.mp hi).2
      · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hw
        exact (Finset.mem_filter.mp hj).2
    · intro hw
      by_cases hn : w < n
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr
          ⟨⟨w,hn⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw⟩,rfl⟩)
      · have hm := hs w hw
        have eq : n+(w-n) = w := by omega
        exact Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨⟨w-n,by omega⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa [eq] using hw⟩,eq⟩)
  have dis : Disjoint R K := by
    apply Finset.disjoint_left.mpr
    intro w hr hk
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨j,hj,eq⟩ := Finset.mem_image.mp hk
    have := i.isLt
    omega
  have cr : R.card = (rowSet n S).card :=
    Finset.card_image_of_injective _ Fin.val_injective
  have ck : K.card = (colSet n m S).card :=
    Finset.card_image_of_injective _ (fun a b h => Fin.ext (by omega))
  rw [← cr,← ck,← Finset.card_union_of_disjoint dis,union]

theorem raw_split_card (N : ℕ) (C : Circuit) (f : ℕ) (hf : f < C.size) :
    (innerGates N C (N+f)).card+(outerGates N C (N+f)).card+1 = C.size := by
  classical
  have fn : f ∉ outerGates N C (N+f) := by
    simp only [outerGates,Finset.mem_filter,Finset.mem_range,not_and]
    intro _
    exact not_not_intro Relation.ReflTransGen.refl
  have union : innerGates N C (N+f) ∪ insert f (outerGates N C (N+f)) = Finset.range C.size := by
    ext j
    by_cases jf : j = f
    · subst j
      simp [hf]
    · simp [innerGates,outerGates,jf]
      tauto
  have dis : Disjoint (innerGates N C (N+f)) (insert f (outerGates N C (N+f))) := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    simp only [innerGates,Finset.mem_filter,Finset.mem_range] at hj
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact hj.2.2 rfl
    · exact (Finset.mem_filter.mp hk).2 hj.2.1
  have eq := congrArg Finset.card union
  rw [Finset.card_union_of_disjoint dis,Finset.card_insert_of_notMem fn,Finset.card_range] at eq
  omega

end PEqualNP.Outside.L_meta_29776_aux
namespace PEqualNP.Outside.L_meta_29776_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def Normal {n m : ℕ} (A : Fin n → Fin m → Bool) (s : ℕ) : Prop :=
  RepSizeAtMost A s ∨
    ∃ (R : Finset (Fin n)) (K : Finset (Fin m)) (G : Circuit),
      R.card ≤ 1 ∧ K.card ≤ 1 ∧ Monotone2 G ∧
      ((0 < R.card+K.card ∧ G.size+R.card+K.card ≤ s ∧
        ∀ i j, A i j = G.eval (oneEach i j ++ [decide (i ∉ R ∧ j ∉ K)])) ∨
       (G.size+1+R.card+K.card ≤ s ∧
        ∀ i j, A i j = (decide (i ∈ R ∨ j ∈ K) || !(G.eval (oneEach i j)))))

theorem normal_from_split {n m s : ℕ} (A : Fin n → Fin m → Bool) (I O : Circuit) (S T : Finset ℕ)
    (im : Monotone2 I) (om : Monotone2 O) (cost : I.size+O.size+1 ≤ s)
    (hi : Function.Injective A) (hj : Function.Injective (fun j i => A i j))
    (sb : ∀ w ∈ S, w < n+m) (tb : ∀ w ∈ T, w < n+m) (dis : Disjoint S T)
    (i₀ : Fin n) (j₀ : Fin m)
    (is : i₀.val ∉ S) (it : i₀.val ∉ T) (js : n+j₀.val ∉ S) (jt : n+j₀.val ∉ T)
    (iz : I.eval (List.replicate (n+m) false) = false)
    (oz : O.eval (List.replicate (n+m+1) false) = false)
    (iloc : ∀ x y : List Bool, x.length = n+m → y.length = n+m →
      (∀ w ∈ S, x.getD w false = y.getD w false) → I.eval x = I.eval y)
    (oloc : ∀ (x y : List Bool) (b : Bool), x.length = n+m → y.length = n+m →
      (∀ w ∈ T, x.getD w false = y.getD w false) → O.eval (x ++ [b]) = O.eval (y ++ [b]))
    (he : ∀ i j, A i j = O.eval (oneEach i j ++ [!(I.eval (oneEach i j))])) :
    Normal A s := by
  classical
  by_cases empty : S = ∅
  · left
    let G : Circuit := ⟨⟨.and,[]⟩ :: O.gates,O.output⟩
    refine ⟨G,?_,?_,?_⟩
    · intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · simp
      · exact om g hg
    · simp only [G,Circuit.size,List.length_cons]
      change O.size+1 ≤ s
      omega
    · intro i j
      have ei : I.eval (oneEach i j) = false :=
        (iloc _ _ (by simp [oneEach]) (by simp) (by simp [empty])).trans iz
      rw [he,ei]
      rfl
  let F := fun P => I.eval (inp (n+m) P)
  let H := fun P b => O.eval (inp (n+m) P ++ [b])
  have fi (P : Finset ℕ) : F P = F (P ∩ S) := by
    apply iloc _ _ (by simp [inp]) (by simp [inp])
    intro w hw
    rw [inp_get,inp_get]
    simp [hw]
  have fo (P : Finset ℕ) (b : Bool) : H P b = H (P ∩ T) b := by
    apply oloc _ _ _ (by simp [inp]) (by simp [inp])
    intro w hw
    rw [inp_get,inp_get]
    simp [hw]
  have fz : F ∅ = false := by simpa [F,inp_empty] using iz
  have h00 : H ∅ false = false := by
    change O.eval (inp (n+m) ∅ ++ [false]) = false
    rw [inp_empty]
    have e : List.replicate (n+m+1) false = List.replicate (n+m) false ++ [false] := by
      rw [List.replicate_add]
      rfl
    rw [← e]
    exact oz
  have hm : increasingPort H := port_mono (n+m) O om
  have eval (i : Fin n) (j : Fin m) :
      A i j = H (bits2 T i.val (n+j.val)) (!(F (bits2 S i.val (n+j.val)))) := by
    have e := he i j
    rw [each_inp] at e
    change A i j = H {i.val,n+j.val} (!(F {i.val,n+j.val})) at e
    rw [fi,fo] at e
    simpa only [← bits2_inter] using e
  have transposed (j : Fin m) (i : Fin n) :
      A i j = H (bits2 T (n+j.val) i.val) (!(F (bits2 S (n+j.val) i.val))) := by
    rw [bits2_comm T,bits2_comm S]
    exact eval i j
  cases h01 : H ∅ true with
  | false =>
    have hz (b : Bool) : H ∅ b = false := by cases b <;> assumption
    obtain ⟨rs,rc⟩ := false_corner_line A Fin.val (fun j => n+j.val) S T F H
      dis i₀ is it hi fz hz eval
    obtain ⟨ks,kc⟩ := false_corner_line (fun j i => A i j) (fun j => n+j.val) Fin.val S T F H
      dis j₀ js jt hj fz hz transposed
    have singles (w : ℕ) (hw : w ∈ S) : F {w} = true := by
      by_cases wn : w < n
      · exact rs ⟨w,wn⟩ hw
      · have wb := sb w hw
        have we : n+(w-n) = w := by omega
        simpa [we] using ks ⟨w-n,by omega⟩ (by simpa [we] using hw)
    have bound := singleton_bound (n+m) I (mono_fan im) S fz singles
    have card := vertex_card n m S sb
    refine Or.inr ⟨rowSet n S,colSet n m S,O,?_,?_,om,Or.inl ⟨?_,?_,?_⟩⟩
    · apply Finset.card_le_one.mpr
      intro i hi k hk
      exact rc i k (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hk).2
    · apply Finset.card_le_one.mpr
      intro j hj k hk
      exact kc j k (Finset.mem_filter.mp hj).2 (Finset.mem_filter.mp hk).2
    · have hp := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr empty)
      omega
    · omega
    · intro i j
      have e := (eval i j).trans (false_corner_eval i.val (n+j.val) S T F H dis fz hz
        (rs i) (ks j))
      rw [each_inp]
      change A i j = H {i.val,n+j.val} _
      rw [fo,← bits2_inter]
      simpa only [rowSet,colSet,Finset.mem_filter,Finset.mem_univ,true_and] using e
  | true =>
    obtain ⟨rs,rc⟩ := true_corner_line A Fin.val (fun j => n+j.val) S T F H
      dis i₀ is it hi fz h00 h01 hm eval
    obtain ⟨ks,kc⟩ := true_corner_line (fun j i => A i j) (fun j => n+j.val) Fin.val S T F H
      dis j₀ js jt hj fz h00 h01 hm transposed
    have singles (w : ℕ) (hw : w ∈ T) : H {w} false = true := by
      by_cases wn : w < n
      · exact rs ⟨w,wn⟩ hw
      · have wb := tb w hw
        have we : n+(w-n) = w := by omega
        simpa [we] using ks ⟨w-n,by omega⟩ (by simpa [we] using hw)
    have notT : n+m ∉ T := by intro h; have := tb _ h; omega
    have bound : T.card ≤ O.size := by
      have h0 : O.eval (inp (n+m+1) ∅) = false := by simpa [inp_empty] using oz
      have hs (w : ℕ) (hw : w ∈ insert (n+m) T) :
          O.eval (inp (n+m+1) {w}) = true := by
        rw [inp_succ]
        rcases Finset.mem_insert.mp hw with rfl | hw
        · have e : inp (n+m) {n+m} = inp (n+m) ∅ := by
            apply inp_same
            intro i hi
            simp [show i ≠ n+m by omega]
          simpa only [e,Finset.mem_singleton,decide_true] using h01
        · have wn := tb w hw
          have ne : n+m ≠ w := by omega
          simpa [ne] using singles w hw
      have h := singleton_bound (n+m+1) O (mono_fan om) (insert (n+m) T) h0 hs
      rw [Finset.card_insert_of_notMem notT] at h
      omega
    have card := vertex_card n m T tb
    refine Or.inr ⟨rowSet n T,colSet n m T,I,?_,?_,im,Or.inr ⟨?_,?_⟩⟩
    · apply Finset.card_le_one.mpr
      intro i hi k hk
      exact rc i k (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hk).2
    · apply Finset.card_le_one.mpr
      intro j hj k hk
      exact kc j k (Finset.mem_filter.mp hj).2 (Finset.mem_filter.mp hk).2
    · omega
    · intro i j
      have e := (eval i j).trans (true_corner_eval i.val (n+j.val) T _ H h00 h01 hm
        (rs i) (ks j))
      rw [each_inp]
      change A i j = (_ || !(F {i.val,n+j.val}))
      rw [fi,← bits2_inter]
      simpa only [rowSet,colSet,Finset.mem_filter,Finset.mem_univ,true_and] using e

end PEqualNP.Outside.L_meta_29776_aux
namespace PEqualNP.Outside.L_meta_29776_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover Network

theorem forward_normal {n m s : ℕ} (A : Fin n → Fin m → Bool)
    (hi : Function.Injective A) (hj : Function.Injective (fun j i => A i j))
    (hsmall : s+2 ≤ n+m) (C : Circuit) (fan : FanInTwo C)
    (small : C.size ≤ s) (rep : Represents A C) : Normal A s := by
  classical
  rcases positive_or_tight A hi hj hsmall C fan small rep with positive | tight
  · exact Or.inl positive
  obtain ⟨D,r,df,da,ds,total,ho,hr,cl,next,unary,nt,mr,mc,unique,slots⟩ := tight
  obtain ⟨f,eqf⟩ := Finset.card_eq_one.mp nt
  have fm : f ∈ activeNot D (Finset.range D.size) := by rw [eqf]; simp
  obtain ⟨fL,fop⟩ := activeNot_mem.mp fm
  have flt : f < D.size := Finset.mem_range.mp fL
  have shape := tight_local_shape df unary nt slots
  have charge : notCharge (gateAt D f) = 1 := by simp [notCharge,fop]
  have fsize : (gateAt D f).inputs.length = 1 := by
    have := (shape f flt).1
    omega
  obtain ⟨u,fu⟩ := List.length_eq_one_iff.mp fsize
  have back := fun j hj => (shape j hj).2.2
  have nonempty (j : ℕ) (hj : j < D.size) : (gateAt D j).inputs ≠ [] := by
    have len := (shape j hj).1
    have charge : notCharge (gateAt D j) ≤ 1 := by
      unfold notCharge
      split_ifs <;> omega
    intro empty
    rw [empty] at len
    simp only [List.length_nil] at len
    omega
  have onlyNot (j : ℕ) (hj : j < D.size) (ne : j ≠ f) :
      (gateAt D j).op = GateOp.and ∨ (gateAt D j).op = GateOp.or := by
    have mem : gateAt D j ∈ D.gates := by
      rw [gateAt,List.getD_eq_getElem _ _ hj]
      exact List.getElem_mem _
    have h := (df _ mem).1
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
    rcases h with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · have jm : j ∈ activeNot D (Finset.range D.size) :=
        activeNot_mem.mpr ⟨Finset.mem_range.mpr hj,h⟩
      rw [eqf] at jm
      exact (ne (Finset.mem_singleton.mp jm)).elim
  have out : n+m+f ≤ D.output := by
    have p := every_gate_reaches_root cl next f fL
    have h := reachIncreases p
    omega
  have outreal : D.output < n+m+D.size := by
    have := Finset.mem_range.mp hr
    omega
  obtain ⟨I,O,im,om,ic,oc,ie,oe,iz,oz,iloc,oloc⟩ :=
    cut_circuits (n+m) D f u flt fu back nonempty df onlyNot unique out outreal
  let S := innerInputs (n+m) D (n+m+f)
  let T := outerInputs (n+m) D (n+m+f)
  have sb (w : ℕ) (hw : w ∈ S) : w < n+m :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).2
  have tb (w : ℕ) (hw : w ∈ T) : w < n+m :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).2
  have dis : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro w hs ht
    exact (Finset.mem_filter.mp ht).2 (Finset.mem_filter.mp hs).2
  obtain ⟨i₀,hi₀⟩ := Finset.card_pos.mp (show 0 < (missingRows n m D (Finset.range D.size)).card by omega)
  obtain ⟨j₀,hj₀⟩ := Finset.card_pos.mp (show 0 < (missingCols n m D (Finset.range D.size)).card by omega)
  have rowMissing := (Finset.mem_filter.mp hi₀).2
  have colMissing := (Finset.mem_filter.mp hj₀).2
  have is : i₀.val ∉ S := fun h =>
    rowMissing (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).1
  have it : i₀.val ∉ T := fun h =>
    rowMissing (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).1
  have js : n+j₀.val ∉ S := fun h =>
    colMissing (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).1
  have jt : n+j₀.val ∉ T := fun h =>
    colMissing (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).1
  have cost : I.size+O.size+1 ≤ s := by
    have h := raw_split_card (n+m) D f flt
    omega
  apply normal_from_split A I O S T im om cost hi hj sb tb dis i₀ j₀ is it js jt iz oz iloc oloc
  intro i j
  let x := oneEach i j
  have hx : x.length = n+m := by simp [x,oneEach]
  have ub : u < n+m+f := back f flt u (by simp [fu])
  have vn : value (n+m) D (fun w => x.getD w false) (fun _ => none) (n+m+f) =
      !(I.eval x) := by
    rw [val_gate flt rfl,fop,fu]
    simp only [List.map_cons,List.map_nil,GateOp.eval,List.headD_cons,if_pos ub]
    rw [ie x hx]
  have liveout : live (n+m) (Finset.range D.size) D.output := Or.inr ⟨r,hr,ho⟩
  rw [← da i j]
  change D.eval x = O.eval (x ++ [!(I.eval x)])
  rw [← val_original (n+m) D x hx,replace_signal cl _ (n+m+f) D.output liveout,vn]
  exact (oe x (!(I.eval x)) hx).symm

end PEqualNP.Outside.L_meta_29776_aux

theorem PEqualNP.Outside.L_meta_29776 : (∀ (n m : Nat) (A : Fin n → Fin m → Bool),
  2 ≤ n → 2 ≤ m → Function.Injective A → Function.Injective (fun j i => A i j) →
  ∀ s : Nat, s + 2 ≤ n+m →
  ((∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ s ∧ PEqualNP.Represents.Represents A C) ↔
    PEqualNP.Represents.RepSizeAtMost A s ∨
    ∃ (R : Finset (Fin n)) (K : Finset (Fin m)) (G : PEqualNP.CircuitLowerBounds.Circuit),
      R.card ≤ 1 ∧ K.card ≤ 1 ∧ PEqualNP.MetaComplexity.Monotone2 G ∧
      ((0 < R.card+K.card ∧ G.size+R.card+K.card ≤ s ∧
        ∀ i j, A i j = G.eval (PEqualNP.Represents.oneEach i j ++ [decide (i ∉ R ∧ j ∉ K)])) ∨
       (G.size+1+R.card+K.card ≤ s ∧
        ∀ i j, A i j = (decide (i ∈ R ∨ j ∈ K) || !(G.eval (PEqualNP.Represents.oneEach i j))))))) := by
  intro n m A hn hm hi hj s hs
  constructor
  · rintro ⟨C,hc,hsize,ha⟩
    exact PEqualNP.Outside.L_meta_29776_aux.forward_normal A hi hj hs C hc hsize ha
  · exact PEqualNP.Outside.L_meta_29776_aux.budget_reverse
