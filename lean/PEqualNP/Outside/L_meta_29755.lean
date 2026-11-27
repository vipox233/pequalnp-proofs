import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29755.CircuitFacts
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

theorem inputSlots_card (N : ℕ) (C : Circuit) (j : ℕ) :
    (inputSlots N C j).card = ((gateAt C j).inputs.toFinset.filter (· < N + j)).card :=
  Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h)

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

end PEqualNP.Outside.L_meta_29755.CircuitFacts

namespace PEqualNP.Outside.L_meta_29755.CircuitFacts
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
end PEqualNP.Outside.L_meta_29755.CircuitFacts
namespace PEqualNP.Outside.L_meta_29755.CircuitFacts

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

end PEqualNP.Outside.L_meta_29755.CircuitFacts
namespace PEqualNP.Outside.L_meta_29755.CircuitFacts

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover

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

end PEqualNP.Outside.L_meta_29755.CircuitFacts
namespace PEqualNP.Outside.L_meta_29755.CircuitFacts.Unate

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

end PEqualNP.Outside.L_meta_29755.CircuitFacts.Unate

namespace PEqualNP.Outside.L_meta_29755.ConeFacts

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership

def RG (n : ℕ) (gs : List Gate) (i j : ℕ) : Prop :=
  j < gs.length ∧ i < j ∧ n + i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs

theorem tg_last {α : Type} {R : α → α → Prop} {a b : α} (h : Relation.TransGen R a b) :
    ∃ c, R c b := by
  cases h with
  | single h => exact ⟨_, h⟩
  | tail _ h => exact ⟨_, h⟩

theorem cones_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih => simp only [List.foldl_cons, ih, coneStep, List.length_append,
      List.length_cons, List.length_nil]; omega

theorem RG_snoc (n : ℕ) (gs : List Gate) (g : Gate) (a b : ℕ) (hb : b < gs.length) :
    RG n (gs ++ [g]) a b ↔ RG n gs a b := by
  unfold RG
  have : (gs ++ [g]).getD b ⟨GateOp.or, []⟩ = gs.getD b ⟨GateOp.or, []⟩ := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hb]
  rw [this]
  simp only [List.length_append, List.length_cons, List.length_nil]
  constructor
  · rintro ⟨_, h2, h3⟩; exact ⟨hb, h2, h3⟩
  · rintro ⟨_, h2, h3⟩; exact ⟨by omega, h2, h3⟩

theorem tg_snoc (n : ℕ) (gs : List Gate) (g : Gate) (i j : ℕ) (hj : j < gs.length) :
    Relation.TransGen (RG n (gs ++ [g])) i j ↔ Relation.TransGen (RG n gs) i j := by
  constructor
  · intro h
    induction h with
    | single h => exact Relation.TransGen.single ((RG_snoc n gs g _ _ hj).mp h)
    | @tail b c _ hbc ih =>
      have hb : b < gs.length := by have := hbc.2.1; omega
      exact Relation.TransGen.tail (ih hb) ((RG_snoc n gs g _ _ hj).mp hbc)
  · intro h
    induction h with
    | single h => exact Relation.TransGen.single ((RG_snoc n gs g _ _ h.1).mpr h)
    | tail _ hbc ih => exact Relation.TransGen.tail (ih (lt_trans hbc.2.1 hbc.1)) ((RG_snoc n gs g _ _ hbc.1).mpr hbc)

theorem cone_list (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔ Relation.TransGen (RG n gs) i j := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i j
    simp only [List.foldl_nil, List.getD_nil, List.not_mem_nil, false_iff]
    intro h
    obtain ⟨c, hc⟩ := tg_last h
    exact absurd hc.1 (by simp)
  | append_singleton gs g ih =>
    intro i j
    have hL := cones_length n gs []
    simp only [List.length_nil, Nat.zero_add] at hL
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    set cs := gs.foldl (coneStep n) [] with hcs
    rcases Nat.lt_trichotomy j gs.length with h1 | h1 | h1
    · rw [tg_snoc n gs g i j h1, ← ih i j]
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    · subst h1
      have hget : (coneStep n cs g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
            (fun w => (w - n) :: cs.getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hL]
      rw [hget, hL]
      have hRL : ∀ c, RG n (gs ++ [g]) c gs.length ↔ c < gs.length ∧ n + c ∈ g.inputs := by
        intro c
        unfold RG
        have : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
          simp [List.getD_eq_getElem?_getD]
        rw [this]
        simp
      simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
      constructor
      · rintro ⟨w, ⟨hw, hw1, hw2⟩, hi | hi⟩
        · apply Relation.TransGen.single
          rw [hRL]
          refine ⟨by omega, ?_⟩
          have : n + i = w := by omega
          rw [this]; exact hw
        · have h2 := (ih i (w - n)).mp hi
          rw [← tg_snoc n gs g i (w - n) (by omega)] at h2
          refine Relation.TransGen.tail h2 ((hRL _).mpr ⟨by omega, ?_⟩)
          have : n + (w - n) = w := by omega
          rw [this]; exact hw
      · intro h
        cases h with
        | single h =>
          obtain ⟨hc, hm⟩ := (hRL i).mp h
          exact ⟨n + i, ⟨hm, by omega, by omega⟩, Or.inl (by omega)⟩
        | @tail c _ hic hc =>
          obtain ⟨hc1, hm⟩ := (hRL c).mp hc
          refine ⟨n + c, ⟨hm, by omega, by omega⟩, Or.inr ?_⟩
          have : n + c - n = c := by omega
          rw [this, ih]
          exact (tg_snoc n gs g i c hc1).mp hic
    · have hnil : (coneStep n cs g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [hnil]
      simp only [List.not_mem_nil, false_iff]
      intro h
      obtain ⟨c, hc⟩ := tg_last h
      have := hc.1
      simp at this
      omega

def RR (n : ℕ) (C : Circuit) (i j : ℕ) : Prop :=
  j < C.gates.length ∧ i < j ∧ n + i ∈ (gateAt C j).inputs

theorem cone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ Relation.TransGen (RR n C) i j := by
  unfold InCone cones
  rw [cone_list n C.gates i j]
  rfl

end PEqualNP.Outside.L_meta_29755.ConeFacts

namespace PEqualNP.Outside.L_meta_29755
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_29755.CircuitFacts
open PEqualNP.Outside.L_meta_29755.CircuitFacts.Network
open PEqualNP.Outside.L_meta_29755.CircuitFacts.Unate (Changes Path)

theorem witnesses {ι κ : Type} (A : ι → κ → Bool)
    (h : ∀ i, ∃ k, ¬ comparable A i k) (i : ι) :
    ∃ k, k ≠ i ∧ ∃ j, A i j = true ∧ A k j = false := by
  obtain ⟨k, hn⟩ := h i
  refine ⟨k, fun e => hn (e ▸ Or.inl (fun _ h => h)), ?_⟩
  by_contra! hz
  apply hn
  left
  intro j hj
  cases he : A k j
  · exact False.elim (hz j hj he)
  · rfl

theorem trimmedWires (C : Circuit) (x : List Bool) :
    (Network.trim C).wires x = C.wires x := by
  have h (gs : List Gate) (v : List Bool) :
      (gs.map trimGate).foldl step v = gs.foldl step v := by
    induction gs generalizing v with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.map_cons, List.foldl_cons, ih, step, trimGate_eval]
  exact h C.gates x

theorem trimGateAt (C : Circuit) (j : ℕ) (hj : j < C.size) :
    gateAt (Network.trim C) j = trimGate (gateAt C j) := by
  have ht : j < (Network.trim C).gates.length := by simpa [Network.trim, Circuit.size] using hj
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ ht]
  exact List.getElem_map _

theorem fullSlots [DecidableEq GateOp] {N : ℕ} {D : Circuit} {L : Finset ℕ} (cl : closed N D L)
    (fan : FanInTwo D) (unary : ∀ g ∈ D.gates, g.op = .not → g.inputs.length ≤ 1)
    (sat : (slots N D L).card + (activeNot D L).card = 2 * L.card) :
    ∀ j ∈ L, (gateAt D j).inputs.length = (if (gateAt D j).op = .not then 1 else 2) ∧
      (gateAt D j).inputs.Nodup ∧ ∀ w ∈ (gateAt D j).inputs, w < N + j := by
  classical
  let cost (j : ℕ) := (inputSlots N D j).card + (if (gateAt D j).op = .not then 1 else 0)
  have bound (j) (hj : j ∈ L) :
      (gateAt D j).inputs.length ≤ (if (gateAt D j).op = .not then 1 else 2) := by
    have mem : gateAt D j ∈ D.gates := by
      rw [gateAt, List.getD_eq_getElem _ _ (cl.1 j hj)]
      exact List.getElem_mem _
    split_ifs with h
    · exact unary _ mem h
    · exact (fan _ mem).2
  have count (j : ℕ) : (inputSlots N D j).card ≤ (gateAt D j).inputs.length := by
    rw [inputSlots_card]
    exact (Finset.card_filter_le _ _).trans (List.toFinset_card_le _)
  have costLe (j) (hj : j ∈ L) : cost j ≤ 2 := by
    have hh := bound j hj
    have hc := count j
    by_cases h : (gateAt D j).op = .not <;> simp [cost, h] at * <;> omega
  have sumLo : 2 * L.card ≤ ∑ j ∈ L, cost j := by
    have hslots := Finset.card_biUnion_le (s := L) (t := inputSlots N D)
    change (slots N D L).card ≤ _ at hslots
    have hn : (activeNot D L).card = ∑ j ∈ L, if (gateAt D j).op = .not then 1 else 0 := by
      unfold activeNot
      rw [Finset.card_filter]
      apply Finset.sum_congr rfl
      intro a _
      by_cases h : (gateAt D a).op = .not <;> simp [h]
    simpa only [cost, Finset.sum_add_distrib, ← hn, ← sat] using
      Nat.add_le_add_right hslots (activeNot D L).card
  intro j hj
  have splitSum := Finset.sum_erase_add L cost hj
  have eraseBound : ∑ k ∈ L.erase j, cost k ≤ (L.erase j).card * 2 := by
    simpa using Finset.sum_le_sum (s := L.erase j)
      (fun k hk => costLe k (Finset.mem_of_mem_erase hk))
  rw [Finset.card_erase_of_mem hj] at eraseBound
  have pos := Finset.card_pos.mpr ⟨j,hj⟩
  have eqCost : cost j = 2 := by have := costLe j hj; omega
  have filled : (inputSlots N D j).card =
      (if (gateAt D j).op = .not then 1 else 2) := by
    change (inputSlots N D j).card + (if (gateAt D j).op = .not then 1 else 0) = 2 at eqCost
    by_cases h : (gateAt D j).op = .not <;> simp [h] at eqCost ⊢ <;> omega
  have len := Nat.le_antisymm (bound j hj) (filled ▸ count j)
  have equality := filled.trans len.symm
  let S := (gateAt D j).inputs.toFinset
  rw [inputSlots_card] at equality
  change (S.filter (· < N + j)).card = (gateAt D j).inputs.length at equality
  have lo := Finset.card_le_card (Finset.filter_subset (· < N + j) S)
  have hi := List.toFinset_card_le (gateAt D j).inputs
  change S.card ≤ _ at hi
  have all : S.filter (· < N + j) = S :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
  have nodup : (gateAt D j).inputs.Nodup := by
    exact Multiset.toFinset_card_eq_card_iff_nodup (m := ((gateAt D j).inputs : Multiset ℕ)) |>.mp (by
      change S.card = (gateAt D j).inputs.length
      omega)
  refine ⟨len, nodup, ?_⟩
  intro w hw
  have hmem : w ∈ S := List.mem_toFinset.mpr hw
  rw [← all] at hmem
  exact (Finset.mem_filter.mp hmem).2

theorem used_has_reader {N : ℕ} {D : Circuit} {L : Finset ℕ} (back : ReadsBack N D)
    (valid : ∀ j ∈ L, j < D.size) (w : ℕ) :
    w ∈ used N D L ↔ ∃ j ∈ L, w ∈ (gateAt D j).inputs := by
  rw [mem_used]
  exact ⟨fun ⟨j,hj,hm,_⟩ => ⟨j,hj,hm⟩, fun ⟨j,hj,hm⟩ => ⟨j,hj,hm,back j (valid j hj) w hm⟩⟩

theorem reads_card (D : Circuit) (L : Finset ℕ) (w : ℕ)
    (nodup : ∀ j ∈ L, (gateAt D j).inputs.Nodup) :
    readsIn D L w = (L.filter fun j => w ∈ (gateAt D j).inputs).card := by
  rw [readsIn, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : w ∈ (gateAt D j).inputs
  · simp only [h, ite_true]
    have lo := List.count_pos_iff.mpr h
    have hi := List.nodup_iff_count_le_one.mp (nodup j hj) w
    omega
  · simpa [h] using List.count_eq_zero.mpr h

theorem gateReach {N : ℕ} {D : Circuit} {L : Finset ℕ}
    (full : L = Finset.range D.size) (a b : ℕ) :
    reaches N D L (N+a) (N+b) ↔ a = b ∨ PEqualNP.EdgeOwnership.InCone N D a b := by
  rw [PEqualNP.Outside.L_meta_29755.ConeFacts.cone_iff]
  have arc {i j : ℕ} : edgeTo N D L (N+i) (N+j) ↔ PEqualNP.Outside.L_meta_29755.ConeFacts.RR N D i j := by
    constructor
    · rintro ⟨k,hk,e,hm,lt⟩
      have he : j = k := by omega
      subst k
      exact ⟨Finset.mem_range.mp (full ▸ hk), by omega, hm⟩
    · rintro ⟨hj,hij,hm⟩
      exact ⟨j,full.symm ▸ Finset.mem_range.mpr hj,rfl,hm,by omega⟩
  constructor
  · intro p
    have lift {v : ℕ} (p : reaches N D L (N+a) v) :
        ∃ j, v = N+j ∧ (a = j ∨ Relation.TransGen (PEqualNP.Outside.L_meta_29755.ConeFacts.RR N D) a j) := by
      induction p with
      | refl => exact ⟨a,rfl,Or.inl rfl⟩
      | tail _ he ih =>
        obtain ⟨i,rfl,hi⟩ := ih
        obtain ⟨j,hj,rfl,hm,lt⟩ := he
        have edge := arc.mp ⟨j,hj,rfl,hm,lt⟩
        exact ⟨j,rfl,hi.elim (fun e => Or.inr (.single (e ▸ edge))) (fun p => Or.inr (.tail p edge))⟩
    obtain ⟨j,e,hj⟩ := lift p
    have eq : b = j := by omega
    exact eq ▸ hj
  · rintro (rfl | p)
    · exact .refl
    · induction p with
      | single he => exact .single (arc.mpr he)
      | tail _ he ih => exact .tail ih (arc.mpr he)

theorem sameCut {N : ℕ} {D : Circuit} {L : Finset ℕ} (cl : closed N D L)
    (stop : ℕ) (noLeak : ∀ a b, a ≠ stop → edgeTo N D L a b → reaches N D L a stop →
      reaches N D L b stop)
    (b : Bool) (x y : ℕ → Bool)
    (raw : ∀ u < N, ¬ reaches N D L u stop → x u = y u)
    (w : ℕ) (hw : live N L w) (out : w = stop ∨ ¬ reaches N D L w stop) :
    value N D x (relay stop b) w = value N D y (relay stop b) w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rcases out with rfl | out
    · rw [val_relay, val_relay]
    have ne : w ≠ stop := fun e => out (e ▸ .refl)
    have ho : relay stop b w = none := by simp [relay, ne]
    rcases hw with hw | ⟨j,hj,rfl⟩
    · rw [val_raw hw ho, val_raw hw ho, raw w hw out]
    · rw [val_gate (cl.1 j hj) ho, val_gate (cl.1 j hj) ho]
      congr 1
      apply List.map_congr_left
      intro u hu
      split_ifs with h
      · apply ih u h (prev_live cl hj ⟨hu,h⟩)
        by_cases ef : u = stop
        · exact .inl ef
        · exact .inr (fun p => out (noLeak u _ ef ⟨j,hj,rfl,hu,h⟩ p))
      · rfl

theorem orderCut {N : ℕ} {D : Circuit} {L : Finset ℕ} (cl : closed N D L)
    {t w : ℕ} (hw : live N L w)
    (ops : ∀ j ∈ L, j ≠ t → (gateAt D j).op = .and ∨ (gateAt D j).op = .or)
    {x y : ℕ → Bool} {b c : Bool}
    (raw : ∀ u < N, x u = true → y u = true) (hbc : b = true → c = true) :
    value N D x (relay (N+t) b) w = true → value N D y (relay (N+t) c) w = true := by
  apply value_mono cl w hw _ _ _ _ (fun u hu _ => raw u hu)
  · intro u _
    by_cases eq : u = N + t
    · exact Or.inr ⟨b,c,by simp [relay,eq],by simp [relay,eq],hbc⟩
    · exact Or.inl ⟨by simp [relay,eq],by simp [relay,eq]⟩
  · intro j hj _ hnone
    apply ops j hj
    rintro rfl
    simp [relay] at hnone

theorem unateWithClosedNot {N : ℕ} {D : Circuit} {L : Finset ℕ} (cl : closed N D L)
    {t u w i : ℕ} (ht : t ∈ L) (hu : before D N t u) (htail : (gateAt D t).inputs = [u])
    (hnot : (gateAt D t).op = .not) (hw : live N L w) (htw : N + t ≤ w)
    (ops : ∀ j ∈ L, j ≠ t → (gateAt D j).op = .and ∨ (gateAt D j).op = .or)
    (noLeak : ∀ a b, a ≠ N+t → edgeTo N D L a b → reaches N D L a (N+t) →
      reaches N D L b (N+t)) :
    ∃ pos : Bool, ∀ x y : ℕ → Bool, Changes N i none x y →
      if pos then value N D x (fun _ => none) w = true → value N D y (fun _ => none) w = true
      else value N D y (fun _ => none) w = true → value N D x (fun _ => none) w = true := by
  classical
  let V (x : ℕ → Bool) := value N D x (fun _ => none)
  have act (x : ℕ → Bool) : V x (N+t) = ! V x u := by
    dsimp only [V]
    rw [val_gate (cl.1 t ht) rfl, hnot, htail]
    simp [GateOp.eval, hu.2]
  have orient (x y : ℕ → Bool) (h : Changes N i none x y) :
      ∀ a < N, x a = true → y a = true := by
    intro a ha
    by_cases e : a = i
    · subst a
      exact h.2.2
    · rw [h.1 a ha e]
      exact id
  by_cases reach : reaches N D L i (N+t)
  · refine ⟨false, fun x y h => ?_⟩
    change V y w = true → V x w = true
    have up : V x u = true → V y u = true := by
      apply value_mono cl u (prev_live cl ht hu) _ _ _ _ (fun a ha _ => orient x y h a ha)
        (fun _ _ => Or.inl ⟨rfl,rfl⟩)
      intro j hj p _
      have hlt := reachIncreases p
      have huLt := hu.2
      exact ops j hj (by omega)
    have down : V y (N+t) = true → V x (N+t) = true := by
      rw [act, act]
      cases hx : V x u <;> cases hy : V y u <;> simp_all
    have eq : value N D y (relay (N+t) (V y (N+t))) w =
        value N D x (relay (N+t) (V y (N+t))) w := by
      refine sameCut cl (N+t) noLeak (V y (N+t)) y x ?_ w hw ?_
      · intro a ha away
        exact (h.1 a ha (fun e => away (e ▸ reach))).symm
      · by_cases e : w = N+t
        · exact Or.inl e
        · exact Or.inr (fun p => e (by have := reachIncreases p; omega))
    dsimp only [V] at eq ⊢
    rw [replace_signal cl y (N+t) w hw, replace_signal cl x (N+t) w hw, eq]
    exact orderCut cl hw ops (fun _ _ => id) down
  · refine ⟨true, fun x y h => ?_⟩
    change V x w = true → V y w = true
    have eq : V x (N+t) = V y (N+t) := by
      apply value_agree cl (N+t) (Or.inr ⟨t,ht,rfl⟩)
      · intro a ha p
        exact h.1 a ha (fun e => reach (e ▸ p))
      · intro a _
        rfl
    dsimp only [V] at eq ⊢
    rw [replace_signal cl x (N+t) w hw, replace_signal cl y (N+t) w hw, eq]
    exact orderCut cl hw ops (orient x y h) id

theorem trimReads {C : Circuit} {t : ℕ} (ht : t < C.size)
    (only : ∀ j < C.size, (gateAt (Network.trim C) j).op = .not ↔ j = t)
    (w : ℕ) :
    readsIn C (Finset.range C.size) w =
      readsIn (Network.trim C) (Finset.range (Network.trim C).size) w +
        ((gateAt C t).inputs.drop 1).count w := by
  have sizes : (Network.trim C).size = C.size := by simp [Network.trim, Circuit.size]
  rw [sizes, readsIn, readsIn]
  let tailCount := ((gateAt C t).inputs.drop 1).count w
  have takeCount (j : ℕ) (hj : j ∈ Finset.range C.size) :
      (gateAt C j).inputs.count w =
        (gateAt (Network.trim C) j).inputs.count w + if j = t then tailCount else 0 := by
    have hj' := Finset.mem_range.mp hj
    have op : (trimGate (gateAt C j)).op = (gateAt C j).op := by
      cases h : (gateAt C j).op <;> simp [trimGate,h]
    have only' : (gateAt C j).op = .not ↔ j = t := by
      simpa only [trimGateAt C j hj', op] using only j hj'
    rw [trimGateAt C j hj']
    by_cases e : j = t
    · have h := only'.mpr e
      subst j
      simp only [trimGate,h,tailCount]
      nth_rw 1 [← List.take_append_drop 1 (gateAt C t).inputs]
      exact List.count_append
    · have ne := fun h => e (only'.mp h)
      cases h : (gateAt C j).op <;> simp_all [trimGate]
  calc
    _ = ∑ j ∈ Finset.range C.size,
        ((gateAt (Network.trim C) j).inputs.count w + if j = t then tailCount else 0) :=
      Finset.sum_congr rfl takeCount
    _ = _ := by rw [Finset.sum_add_distrib]; simp [ht, tailCount]

end PEqualNP.Outside.L_meta_29755

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_29755.CircuitFacts
open PEqualNP.Outside.L_meta_29755.CircuitFacts.Network
open PEqualNP.Outside.L_meta_29755.CircuitFacts.Unate (Changes Path)
open PEqualNP.Outside.L_meta_29755

theorem PEqualNP.Outside.L_meta_29755 : (∀ (n m : Nat) (A : Fin n → Fin m → Bool), 3 ≤ n → 3 ≤ m →
  let rowLE := fun i k : Fin n => ∀ j, A i j = true → A k j = true
  let colLE := fun j l : Fin m => ∀ i, A i j = true → A i l = true
  let rc := fun i k : Fin n => rowLE i k ∨ rowLE k i
  let cc := fun j l : Fin m => colLE j l ∨ colLE l j
  Function.Injective A → Function.Injective (fun j i => A i j) →
  (∀ i, ∃ k, ¬ rc i k) → (∀ j, ∃ l, ¬ cc j l) →
  ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
  PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C →
  C.size ≤ n + m - 1 →
  (∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not) →
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  let N := n+m
  let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨C.gates.map (fun g =>
    if g.op = PEqualNP.CircuitLowerBounds.GateOp.not then ⟨g.op,g.inputs.take 1⟩ else g), C.output⟩
  let atGate := PEqualNP.MetaComplexity.NestedCover.gateAt D
  let reads := PEqualNP.MetaComplexity.NestedCover.readsIn D (Finset.range D.size)
  (∀ xs : List Bool, D.wires xs = C.wires xs) ∧
  C.size = N-1 ∧ D.output+1 = N+D.size ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack N D ∧
  (∀ g ∈ D.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨
    (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧
  ∃ (r : Fin n) (c : Fin m) (f t : Fin D.size), f < t ∧
    (∀ j : Fin D.size, (atGate j.val).op = PEqualNP.CircuitLowerBounds.GateOp.not ↔ j = t) ∧
    (∀ i : Fin n, reads i.val = if i = r then 0 else 1) ∧
    (∀ j : Fin m, reads (n+j.val) = if j = c then 0 else 1) ∧
    (∀ j : Fin D.size, reads (N+j.val) =
      if j = f then 2 else if j.val+1 = D.size then 0 else 1) ∧
    PEqualNP.EdgeOwnership.InCone N D f.val t.val ∧
    PEqualNP.MetaComplexity.NestedCover.readsIn D (insert t.val (((PEqualNP.EdgeOwnership.cones N D).getD t.val []).toFinset)) (N+f.val) = 1 ∧
    ∀ w : Nat, PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) w =
      reads w + (((PEqualNP.MetaComplexity.NestedCover.gateAt C t.val).inputs.drop 1).count w)) := by
  classical
  intro n m A hn hm
  dsimp only
  intro hi hj ri ci C fan rep small hnC
  let N := n+m
  let D := Network.trim C
  letI : DecidableEq GateOp := gateOpDecEq
  have dEq : D = ⟨C.gates.map (fun g =>
      if g.op = GateOp.not then ⟨g.op,g.inputs.take 1⟩ else g), C.output⟩ := by
    have emap : trimGate = (fun g : Gate =>
        if g.op = GateOp.not then ⟨g.op,g.inputs.take 1⟩ else g) := by
      funext g
      cases g with
      | mk op inp => cases op <;> simp [trimGate]
    change Circuit.mk (C.gates.map trimGate) C.output = _
    rw [emap]
  let goal (E : Circuit) : Prop :=
    let reads := readsIn E (Finset.range E.size)
    (∀ xs : List Bool, E.wires xs = C.wires xs) ∧
    C.size = N-1 ∧ E.output+1 = N+E.size ∧ ReadsBack N E ∧
    (∀ g ∈ E.gates, ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
      (g.op = .not ∧ g.inputs.length = 1)) ∧
    ∃ (r : Fin n) (c : Fin m) (f t : Fin E.size), f < t ∧
      (∀ j : Fin E.size, (gateAt E j.val).op = .not ↔ j = t) ∧
      (∀ i : Fin n, reads i.val = if i = r then 0 else 1) ∧
      (∀ j : Fin m, reads (n+j.val) = if j = c then 0 else 1) ∧
      (∀ j : Fin E.size, reads (N+j.val) =
        if j = f then 2 else if j.val+1 = E.size then 0 else 1) ∧
      PEqualNP.EdgeOwnership.InCone N E f.val t.val ∧
      readsIn E (insert t.val (((PEqualNP.EdgeOwnership.cones N E).getD t.val []).toFinset)) (N+f.val) = 1 ∧
      ∀ w : Nat, readsIn C (Finset.range C.size) w =
        reads w + (((gateAt C t.val).inputs.drop 1).count w)
  change goal _
  rw [← dEq]
  dsimp only [goal]
  have sizeD : D.size = C.size := by simp [D, Network.trim, Circuit.size]
  have dfan : FanInTwo D := trim_fan C fan
  have dunary : ∀ g ∈ D.gates, g.op = .not → g.inputs.length ≤ 1 := trim_unary C
  have drep : Represents A D := fun i j => (trim_eval C (oneEach i j)).trans (rep i j)
  have dsmall : D.size ≤ N - 1 := sizeD.trans_le small
  have dnot : ∃ g ∈ D.gates, g.op = GateOp.not := by
    obtain ⟨g,hg,hnot⟩ := hnC
    refine ⟨trimGate g, List.mem_map.mpr ⟨g,hg,rfl⟩, ?_⟩
    simp [trimGate,hnot]
  obtain ⟨outlo,outhi⟩ := root_bounds (by omega) (witnesses A ri)
    (witnesses (fun j i => A i j) ci) D drep
  let o := D.output - N
  have outEq : D.output = N+o := by dsimp [o,N]; omega
  have oLt : o < D.size := by dsimp [o,N,Circuit.size]; omega
  obtain ⟨L,ho,closedL,next⟩ := minimal_closed N D o oLt
  have liveOut : Network.live N L D.output := Or.inr ⟨o,ho,outEq⟩
  have nout : N ≤ D.output := outlo
  have rowLe := missing_rows_le hi drep closedL ho outEq
  have colLe := missing_cols_le hj drep closedL ho outEq
  have gmem (k : ℕ) (hk : k < D.size) : gateAt D k ∈ D.gates := by
    rw [gateAt,List.getD_eq_getElem _ _ hk]
    exact List.getElem_mem _
  have ops (k : ℕ) (hk : k ∈ L) (ne : (gateAt D k).op ≠ .not) :
      (gateAt D k).op = .and ∨ (gateAt D k).op = .or := by
    have h := (dfan _ (gmem k (closedL.1 k hk))).1
    simpa [Set.mem_insert_iff, ne] using h
  have needed (polarity : ∀ i < N, ∃ pos : Bool, ∀ x y : ℕ → Bool,
      Changes N i none x y →
      if pos then value N D x (fun _ => none) D.output = true →
                    value N D y (fun _ => none) D.output = true
      else value N D y (fun _ => none) D.output = true →
           value N D x (fun _ => none) D.output = true) :
      (missingRows n m D L).card = 0 ∧ (missingCols n m D L).card = 0 := by
    constructor
    · by_contra hne
      obtain ⟨r,hr⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hne)
      have unused := (Finset.mem_filter.mp hr).2
      have out := Unate.not_path_unused (w := D.output) unused (by
        have := r.isLt
        dsimp [N] at nout
        omega)
      obtain ⟨k,hk⟩ := ri r
      exact hk (Unate.omitted_row_comparable drep closedL liveOut out
        (polarity k.val (by have := k.isLt; dsimp [N]; omega)))
    · by_contra hne
      obtain ⟨c,hc⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hne)
      have unused := (Finset.mem_filter.mp hc).2
      have out := Unate.not_path_unused (w := D.output) unused (by
        have := c.isLt
        dsimp [N] at nout
        omega)
      obtain ⟨k,hk⟩ := ci c
      exact hk (Unate.omitted_col_comparable drep closedL liveOut out
        (polarity (n+k.val) (by have := k.isLt; dsimp [N]; omega)))
  have anyFullHasNot (full : L = Finset.range D.size) : 0 < (activeNot D L).card := by
    obtain ⟨g,hg,hnot⟩ := dnot
    obtain ⟨k,hk,he⟩ := List.mem_iff_getElem.mp hg
    refine Finset.card_pos.mpr ⟨k, activeNot_mem.mpr ⟨full.symm ▸ Finset.mem_range.mpr hk, ?_⟩⟩
    rw [gateAt,List.getD_eq_getElem _ _ hk,he,hnot]
  have activePos : 0 < (activeNot D L).card := by
    by_contra! hno
    have zero : (activeNot D L).card = 0 := by omega
    obtain ⟨r0,c0⟩ := needed (by
      intro i _
      refine ⟨true, fun x y changeXY => ?_⟩
      simp only [ite_true]
      apply value_mono closedL _ liveOut _ _ _ _ _ (fun _ _ => Or.inl ⟨rfl,rfl⟩)
        (fun j h _ _ => ops j h (no_active_not_elim zero h))
      intro w hw _
      by_cases e : w = i
      · subst w
        exact changeXY.2.2
      · rw [changeXY.1 w hw e]
        exact id)
    obtain ⟨_,sz,_⟩ := no_not_if_full ho closedL next dfan dunary dsmall r0 c0
    have full : L = Finset.range D.size :=
      Finset.eq_of_subset_of_card_le (fun k hk => Finset.mem_range.mpr (closedL.1 k hk))
        (by simp [sz])
    exact (Nat.not_lt_of_ge hno) (anyFullHasNot full)
  have collision : ¬ Set.InjOn Prod.snd (slots N D L : Set (ℕ × ℕ)) := by
    intro injective
    obtain ⟨r0,c0⟩ := needed (by
      intro i hilt
      exact Unate.original_unate (fork := none) closedL dfan hilt
        (fun _ _ _ _ hp hq h1 h2 => unique_reader_of_inj injective hp hq h1 h2)
        (fun _ h => by cases h) liveOut)
    have h0 := (no_not_if_full ho closedL next dfan dunary dsmall r0 c0).1
    omega
  obtain ⟨row1,col1,not1,lSize,tight,slots1⟩ :=
    collision_counts ho closedL next dfan dunary dsmall rowLe colLe activePos collision
  have full : L = Finset.range D.size :=
    Finset.eq_of_subset_of_card_le (fun k hk => Finset.mem_range.mpr (closedL.1 k hk))
      (by simp [lSize])
  have arity := fullSlots closedL dfan dunary (by
    have hpar : (rawUsed N D L).card + (missingRows n m D L).card +
        (missingCols n m D L).card = N := input_partition n m D L
    have hlo : (rawUsed N D L).card + (L.card-1) ≤ (used N D L).card :=
      slots_count_low ho next
    have hhi : (slots N D L).card + (activeNot D L).card ≤ 2*L.card :=
      slots_count_high closedL dfan dunary
    have hs : (slots N D L).card = (used N D L).card+1 := slots1
    have lc : L.card = N-1 := lSize.trans tight
    have hp := Finset.card_pos.mpr ⟨o,ho⟩
    omega)
  have back : ReadsBack N D :=
    fun k hk => (arity k (full.symm ▸ Finset.mem_range.mpr hk)).2.2
  obtain ⟨j,k,f,hjL,hkL,hjk,hjf,hkf⟩ := collision_exists collision
  have forkOnly (a p q : ℕ) (ha : a ≠ f) (hp : p ∈ L) (hq : q ∈ L)
      (h1 : before D N p a) (h2 : before D N q a) : p = q := by
    by_contra hne
    exact ha (unique_collision slots1 hjL hkL hjk hjf hkf hp hq hne h1 h2).1
  obtain ⟨t,htEq⟩ := Finset.card_eq_one.mp not1
  have htL : t ∈ L := (activeNot_mem.mp (htEq.symm ▸ Finset.mem_singleton_self t)).1
  have only (j : ℕ) (hj : j ∈ L) : (gateAt D j).op = .not ↔ j = t := by
    have eq := activeNot_mem (C := D) (L := L) (j := j)
    rw [htEq,Finset.mem_singleton] at eq
    exact ⟨fun h => eq.mpr ⟨hj,h⟩, fun h => (eq.mp h).2⟩
  have htNot := (only t htL).mpr rfl
  obtain ⟨u,huList⟩ := List.length_eq_one_iff.mp (by simpa [htNot] using (arity t htL).1)
  have huMem : u ∈ (gateAt D t).inputs := by simp [huList]
  have hu : before D N t u := ⟨huMem,(arity t htL).2.2 u huMem⟩
  obtain ⟨r,hrEq⟩ := Finset.card_eq_one.mp row1
  obtain ⟨c,hcEq⟩ := Finset.card_eq_one.mp col1
  have rowUnused (i : Fin n) : i.val ∉ used N D L ↔ i = r := by
    change i.val ∉ used (n+m) D L ↔ i = r
    rw [← Finset.mem_singleton, ← hrEq]
    simp [missingRows]
  have colUnused (i : Fin m) : n+i.val ∉ used N D L ↔ i = c := by
    change n+i.val ∉ used (n+m) D L ↔ i = c
    rw [← Finset.mem_singleton, ← hcEq]
    simp [missingCols]
  have badRow : ¬ Path N D L r.val D.output := Unate.not_path_unused ((rowUnused r).mpr rfl)
    (by have := r.isLt; dsimp [N] at nout; omega)
  have badCol : ¬ Path N D L (n+c.val) D.output := Unate.not_path_unused ((colUnused c).mpr rfl)
    (by have := c.isLt; dsimp [N] at nout; omega)
  obtain ⟨i,hiBad⟩ := ri r
  obtain ⟨v,hvBad⟩ := ci c
  have signsAway (a : ℕ) (ha : a < N) (away : ¬ Path N D L a f) :=
    Unate.original_unate (fork := some f) closedL dfan ha
      (fun a p q hs => forkOnly a p q (fun h => hs (congrArg some h.symm)))
      (fun g h => by have e := Option.some.inj h; simpa only [← e] using away) liveOut
  have rowFork : Path N D L i.val f := by
    by_contra p
    exact hiBad (Unate.omitted_row_comparable drep closedL liveOut badRow
      (signsAway i.val (by have := i.isLt; dsimp [N]; omega) p))
  have colFork : Path N D L (n+v.val) f := by
    by_contra p
    exact hvBad (Unate.omitted_col_comparable drep closedL liveOut badCol
      (signsAway (n+v.val) (by have := v.isLt; dsimp [N]; omega) p))
  have rawEnd {a : ℕ} (p : Path N D L a f) (hf : f < N) : a = f := by
    rcases p.cases_tail with he | ⟨b,_,⟨g,_,he,_⟩⟩
    · exact he.symm
    · omega
  have fge : N ≤ f := by
    by_contra! hf
    have h1 := rawEnd rowFork hf
    have h2 := rawEnd colFork hf
    have := i.isLt
    omega
  let fidx := f-N
  have feq : f = N+fidx := by dsimp [fidx]; omega
  have fLt : fidx < D.size := by
    have hb := hjf.2
    have hL : j < D.size := closedL.1 j hjL
    omega
  have allReach (a : ℕ) (ha : a ∈ L) :
      reaches N D L (N+a) D.output := outEq.symm ▸ every_gate_reaches_root closedL next a ha
  have tLe := reachIncreases (allReach t htL)
  have lastLt : D.size - 1 < D.size := by have := oLt; omega
  have outLast : D.output + 1 = N+D.size := by
    have hlast := reachIncreases (allReach (D.size-1) (full.symm ▸ Finset.mem_range.mpr lastLt))
    omega
  have atMostOne (w : ℕ) (hne : w ≠ f) :
      readsIn D L w = if w ∈ used N D L then 1 else 0 := by
    let S := L.filter fun q => w ∈ (gateAt D q).inputs
    have read := reads_card D L w (fun q hq => (arity q hq).2.1)
    change readsIn D L w = S.card at read
    rw [read]
    have s1 : S.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      obtain ⟨haL,haW⟩ := Finset.mem_filter.mp ha
      obtain ⟨hbL,hbW⟩ := Finset.mem_filter.mp hb
      exact forkOnly w a b hne haL hbL ⟨haW,back a (closedL.1 a haL) w haW⟩
        ⟨hbW,back b (closedL.1 b hbL) w hbW⟩
    have pos : 0 < S.card ↔ w ∈ used N D L := by
      rw [Finset.card_pos, used_has_reader back closedL.1]
      exact ⟨fun ⟨q,hq⟩ => ⟨q,Finset.mem_filter.mp hq⟩,
        fun ⟨q,hq⟩ => ⟨q,Finset.mem_filter.mpr hq⟩⟩
    by_cases h : w ∈ used N D L
    · rw [ite_eq_left h]
      exact Nat.le_antisymm s1 (pos.mpr h)
    · rw [ite_eq_right h]
      exact Nat.eq_zero_of_not_pos (mt pos.mp h)
  have forkReaders : L.filter (fun q => f ∈ (gateAt D q).inputs) = {j,k} := by
    ext a
    simp only [Finset.mem_filter,Finset.mem_insert,Finset.mem_singleton]
    constructor
    · rintro ⟨ha,hw⟩
      by_cases p : a = j
      · exact Or.inl p
      · exact Or.inr ((unique_collision slots1 hjL hkL hjk hjf hkf ha hjL p
          ⟨hw,back a (closedL.1 a ha) f hw⟩ hjf).2.resolve_left
            (fun h => p h.1)).1
    · rintro (rfl | rfl)
      · exact ⟨hjL,hjf.1⟩
      · exact ⟨hkL,hkf.1⟩
  have forkRead : readsIn D L f = 2 := by
    rw [reads_card D L f (fun q hq => (arity q hq).2.1),forkReaders]
    simp [hjk]
  let Q := insert t (((PEqualNP.EdgeOwnership.cones N D).getD t []).toFinset)
  have inQ (a : ℕ) : a ∈ Q ↔ reaches N D L (N+a) (N+t) := by
    rw [gateReach full]
    simp [Q, PEqualNP.EdgeOwnership.InCone]
  have qSub : Q ⊆ L := by
    intro a ha
    have hle := reachIncreases ((inQ a).mp ha)
    have ht := closedL.1 t htL
    exact full.symm ▸ Finset.mem_range.mpr (by change t < D.size at ht; omega)
  have oneToNot : readsIn D Q f = 1 := by
    by_contra hread
    let T := Q.filter fun a => f ∈ (gateAt D a).inputs
    have n1 : T.card ≠ 1 := by
      rw [reads_card D Q f (fun a ha => (arity a (qSub ha)).2.1)] at hread
      exact hread
    have sub : T ⊆ ({j,k} : Finset ℕ) := by
      intro a ha
      rw [← forkReaders]
      obtain ⟨ha,hm⟩ := Finset.mem_filter.mp ha
      exact Finset.mem_filter.mpr ⟨qSub ha,hm⟩
    have noLeak : ∀ a b, a ≠ N+t → edgeTo N D L a b → reaches N D L a (N+t) →
        reaches N D L b (N+t) := by
      intro a b ne ab p
      by_cases e : a = f
      · subst a
        obtain ⟨w,fw,wp⟩ := Network.path_head p ne
        obtain ⟨s,hs,rfl,hsw⟩ := fw
        have hsT : s ∈ T := Finset.mem_filter.mpr ⟨(inQ s).mpr wp,hsw.1⟩
        have hpos := Finset.card_pos.mpr ⟨s,hsT⟩
        have htwo : ({j,k} : Finset ℕ).card = 2 := by simp [hjk]
        have hbd := Finset.card_le_card sub
        have all := Finset.eq_of_subset_of_card_le sub (by omega)
        obtain ⟨d,hd,rfl,hdw⟩ := ab
        have hdT : d ∈ T := by
          rw [all,← forkReaders]
          exact Finset.mem_filter.mpr ⟨hd,hdw.1⟩
        exact (inQ d).mp (Finset.mem_filter.mp hdT).1
      · obtain ⟨w,aw,wp⟩ := Network.path_head p ne
        obtain ⟨j',hj',rfl,h1⟩ := aw
        obtain ⟨k',hk',rfl,h2⟩ := ab
        rwa [forkOnly a k' j' e hk' hj' h2 h1]
    exact hiBad (Unate.omitted_row_comparable drep closedL liveOut badRow
      (unateWithClosedNot closedL htL hu huList htNot liveOut tLe
        (fun a ha ne => ops a ha (fun h => ne ((only a ha).mp h))) noLeak))
  have fToNot : fidx < t ∧ PEqualNP.EdgeOwnership.InCone N D fidx t := by
    have one := reads_card D Q f (fun a ha => (arity a (qSub ha)).2.1)
    rw [oneToNot] at one
    have pos : 0 < (Q.filter fun a => f ∈ (gateAt D a).inputs).card := by omega
    obtain ⟨a,ha⟩ := Finset.card_pos.mp pos
    obtain ⟨haQ,haF⟩ := Finset.mem_filter.mp ha
    have ba := back a (closedL.1 a (qSub haQ)) f haF
    have path := Relation.ReflTransGen.head
      (show edgeTo N D L f (N+a) from ⟨a,qSub haQ,rfl,haF,ba⟩) ((inQ a).mp haQ)
    rw [feq] at path
    have lt : fidx < t := by
      have le := reachIncreases ((inQ a).mp haQ)
      omega
    exact ⟨lt, ((gateReach full fidx t).mp path).resolve_left (Nat.ne_of_lt lt)⟩
  have otherRead (a : ℕ) (ha : a < D.size) (hne : N+a ≠ f) :
      readsIn D L (N+a) = if a+1 = D.size then 0 else 1 := by
    rw [atMostOne _ hne]
    by_cases last : a+1 = D.size
    · have h0 : N+a ∉ used N D L := by
        intro hm
        obtain ⟨b,hb,hbefore⟩ := mem_used.mp hm
        have hbl := closedL.1 b hb
        have hlt := hbefore.2
        change b < D.size at hbl
        omega
      simp [last,h0]
    · have hao : a ≠ o := fun e => by omega
      obtain ⟨b,hb,hbefore⟩ := next a (full.symm ▸ Finset.mem_range.mpr ha) hao
      simp [last, mem_used.mpr ⟨b,hb,hbefore⟩]
  have opShape : ∀ g ∈ D.gates, ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
      (g.op = .not ∧ g.inputs.length = 1) := by
    intro g hg
    obtain ⟨a,ha,he⟩ := List.mem_iff_getElem.mp hg
    have ga : gateAt D a = g := by rw [gateAt,List.getD_eq_getElem _ _ ha,he]
    have hL : a ∈ L := full.symm ▸ Finset.mem_range.mpr ha
    rw [← ga]
    by_cases e : (gateAt D a).op = .not
    · exact Or.inr ⟨e,by simpa [e] using (arity a hL).1⟩
    · exact Or.inl ⟨ops a hL e,by simpa [e] using (arity a hL).1⟩
  let ff : Fin D.size := ⟨fidx,fLt⟩
  let tt : Fin D.size := ⟨t,closedL.1 _ htL⟩
  refine ⟨trimmedWires C, by omega, outLast, back, opShape, r,c,ff,tt,fToNot.1,?_,?_,?_,?_,fToNot.2,?_,?_⟩
  · intro a
    rw [only a.val (full.symm ▸ Finset.mem_range.mpr a.isLt)]
    exact ⟨fun h => Fin.ext h,fun h => congrArg Fin.val h⟩
  · intro a
    rw [← full,atMostOne _ (by have := a.isLt; dsimp [N] at fge; omega)]
    by_cases h : a = r
    · subst a
      simp [(rowUnused r).mpr rfl]
    · have : a.val ∈ used N D L := by simpa only [not_not] using mt (rowUnused a).mp h
      simp [h,this]
  · intro a
    rw [← full,atMostOne _ (by have := a.isLt; dsimp [N] at fge; omega)]
    by_cases h : a = c
    · subst a
      simp [(colUnused c).mpr rfl]
    · have : n+a.val ∈ used N D L := by simpa only [not_not] using mt (colUnused a).mp h
      simp [h,this]
  · intro a
    rw [← full]
    by_cases e : a = ff
    · subst a
      change readsIn D L (N+fidx) = _
      simp [← feq,forkRead]
    · have neq : N+a.val ≠ f := fun h => e (Fin.ext (by change a.val = fidx; omega))
      simpa [e] using otherRead a.val a.isLt neq
  · change readsIn D Q (N+fidx) = 1
    rwa [← feq]
  · intro w
    have htb : t < C.size := sizeD ▸ (show t < D.size from closedL.1 t htL)
    exact trimReads htb
      (fun a ha => only a (full.symm ▸ Finset.mem_range.mpr (sizeD.symm ▸ ha))) w
