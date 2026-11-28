import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

/-!
Every wire of such a circuit, read over the five inputs `t = 0..4`, is a 5-bit mask: the inputs
are the masks `30, 28, 24, 16, 0, 63`, and AND, OR, NOT act bitwise (NOT as `63 ^^^ ·`). A bounded
search over the SET of masks present (a new gate either repeats a mask, changing nothing, or adds
`a &&& b`, `a ||| b` or `63 ^^^ a` for masks `a, b` already present) shows that six gates with
at most two NOTs never make `4`, `5` and `22` all present; the kernel checks the search.
-/

namespace PEqualNP.Outside.L_meta_51366_aux

open PEqualNP.CircuitLowerBounds

local instance : DecidableEq GateOp := lineDegreeGateOpDecEq

/-- The mask a gate computes from the masks it reads (fan-in at most two). -/
def mev : GateOp → List Nat → Nat
  | .and, [] => 63
  | .and, [a] => a
  | .and, a :: b :: _ => a &&& b
  | .or, [] => 0
  | .or, [a] => a
  | .or, a :: b :: _ => a ||| b
  | .not, l => 63 ^^^ l.headD 0
  | _, _ => 0

/-- The masks of all wires after the gates `gs`, starting from the masks `w`. -/
def mwires (gs : List Gate) (w : List Nat) : List Nat :=
  gs.foldl (fun w g => w ++ [mev g.op (g.inputs.map fun i => w.getD i 0)]) w

def hasAll (L : List Nat) : Bool := L.contains 8 && L.contains 34 && L.contains 46

def opts (L : List Nat) (r : Nat) : List (Nat × Nat) :=
  L.flatMap (fun a => L.flatMap (fun b => [(a &&& b, r), (a ||| b, r)])) ++
    (if 0 < r then L.map (fun a => (63 ^^^ a, r - 1)) else [])

/-- How many of `8, 34, 46` are missing from `L`; one gate adds at most one of them. -/
def missing (L : List Nat) : Nat :=
  (if L.contains 8 then 0 else 1) + (if L.contains 34 then 0 else 1) + (if L.contains 46 then 0 else 1)

/-- The new masks one gate can add (each once). -/
def nexts (L : List Nat) (r : Nat) : List (Nat × Nat) :=
  ((opts L r).filter (fun p => !L.contains p.1)).eraseDups

/-- `true`: from the mask set `L`, `d` more gates with at most `r` more NOTs never make all
of `8, 34, 46` present. -/
def search : Nat → List Nat → Nat → Bool
  | 0, L, _ => !hasAll L
  | d + 1, L, r => !hasAll L && (decide (d + 1 < missing L) ||
      (nexts L r).all (fun p => search d (L ++ [p.1]) p.2))

theorem sstep (d : Nat) (L : List Nat) (r : Nat) : search (d + 1) L r =
    (!hasAll L && (decide (d + 1 < missing L) ||
      (nexts L r).all (fun p => search d (L ++ [p.1]) p.2))) := rfl

theorem sstep' (d : Nat) (L : List Nat) (r : Nat) : search (d + 1) L r = true ↔
    (hasAll L = false ∧ (d + 1 < missing L ∨
      ∀ p ∈ opts L r, L.contains p.1 = true ∨ search d (L ++ [p.1]) p.2 = true)) := by
  rw [sstep]
  simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, decide_eq_true_eq,
    List.all_eq_true, nexts, List.mem_eraseDups, List.mem_filter]
  constructor
  · rintro ⟨h1, h2 | h2⟩
    · exact ⟨h1, Or.inl h2⟩
    · refine ⟨h1, Or.inr fun p hp => ?_⟩
      by_cases hc : L.contains p.1 = true
      · exact Or.inl hc
      · exact Or.inr (h2 p ⟨hp, by simpa using hc⟩)
  · rintro ⟨h1, h2 | h2⟩
    · exact ⟨h1, Or.inl h2⟩
    · refine ⟨h1, Or.inr fun p hp => ?_⟩
      rcases h2 p hp.1 with h | h
      · have := hp.2; simp_all
      · exact h

theorem missing_append (L : List Nat) (v : Nat) : missing L ≤ missing (L ++ [v]) + 1 := by
  simp only [missing, List.contains_append, List.contains_cons, List.contains_nil, Bool.or_false]
  by_cases h4 : v = 8 <;> by_cases h5 : v = 34 <;> by_cases h22 : v = 46 <;>
    simp_all <;> split_ifs <;> simp_all <;> omega

theorem missing_zero (L : List Nat) (h4 : 8 ∈ L) (h5 : 34 ∈ L) (h22 : 46 ∈ L) : missing L = 0 := by
  simp [missing, h4, h5, h22]

theorem missing_congr {w L : List Nat} (h : ∀ x, x ∈ w ↔ x ∈ L) : missing w = missing L := by
  have hc : ∀ x, w.contains x = L.contains x := fun x => by
    rw [Bool.eq_iff_iff]; simp [h x]
  simp only [missing, hc]

theorem search_hasAll : ∀ d L r, search d L r = true → hasAll L = false := by
  intro d L r h
  cases d <;> simp_all [search]

theorem search_succ : ∀ d L r, search (d + 1) L r = true → search d L r = true := by
  intro d
  induction d with
  | zero => intro L r h; simp_all [search]
  | succ d ih =>
    intro L r h
    rw [sstep'] at h ⊢
    refine ⟨h.1, ?_⟩
    rcases h.2 with h2 | h2
    · exact Or.inl (by omega)
    · refine Or.inr (fun p hp => ?_)
      rcases h2 p hp with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (ih _ _ h1)

theorem opts_mono {L : List Nat} {r r' : Nat} (hr : r' ≤ r) :
    ∀ p ∈ opts L r', ∃ q ∈ opts L r, q.1 = p.1 ∧ p.2 ≤ q.2 := by
  intro p hp
  simp only [opts, List.mem_append, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
    or_false] at hp
  rcases hp with ⟨a, ha, b, hb, hp | hp⟩ | hp
  · exact ⟨(a &&& b, r), by simp only [opts, List.mem_append, List.mem_flatMap, List.mem_cons]; exact Or.inl ⟨a, ha, b, hb, Or.inl rfl⟩, by simp [hp], by simp [hp, hr]⟩
  · exact ⟨(a ||| b, r), by simp only [opts, List.mem_append, List.mem_flatMap, List.mem_cons]; exact Or.inl ⟨a, ha, b, hb, Or.inr (Or.inl rfl)⟩, by simp [hp], by simp [hp, hr]⟩
  · split at hp
    · rename_i h0
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hp
      refine ⟨(63 ^^^ a, r - 1), ?_, rfl, by simp; omega⟩
      simp only [opts, List.mem_append]
      right
      rw [if_pos (by omega)]
      exact List.mem_map.2 ⟨a, ha, rfl⟩
    · simp at hp

theorem search_budget : ∀ d L r r', r' ≤ r → search d L r = true → search d L r' = true := by
  intro d
  induction d with
  | zero => intro L r r' _ h; simpa [search] using h
  | succ d ih =>
    intro L r r' hr h
    rw [sstep'] at h ⊢
    refine ⟨h.1, ?_⟩
    rcases h.2 with h0 | h0
    · exact Or.inl h0
    · refine Or.inr (fun p hp => ?_)
      obtain ⟨q, hq, h1, h2⟩ := opts_mono hr p hp
      rcases h0 q hq with h3 | h3
      · exact Or.inl (h1 ▸ h3)
      · exact Or.inr (ih _ _ _ h2 (h1 ▸ h3))

theorem mwires_cons (g : Gate) (gs : List Gate) (w : List Nat) :
    mwires (g :: gs) w = mwires gs (w ++ [mev g.op (g.inputs.map fun i => w.getD i 0)]) := rfl

theorem missing_mwires : ∀ (gs : List Gate) (w : List Nat),
    missing w ≤ missing (mwires gs w) + gs.length := by
  intro gs
  induction gs with
  | nil => intro w; simp [mwires]
  | cons g gs ih =>
    intro w; rw [mwires_cons]
    have := ih (w ++ [mev g.op (g.inputs.map fun i => w.getD i 0)])
    have := missing_append w (mev g.op (g.inputs.map fun i => w.getD i 0))
    simp only [List.length_cons]; omega

theorem mwires_length : ∀ (gs : List Gate) (w : List Nat),
    (mwires gs w).length = w.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih => intro w; rw [mwires_cons, ih]; simp; omega

def Ok (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

theorem mev_lt (g : Gate) (hg : Ok g) (l : List Nat) (hl : l.length = g.inputs.length)
    (h : ∀ x ∈ l, x < 64) : mev g.op l < 64 := by
  obtain ⟨hop, hlen⟩ := hg
  have h32 : (64 : Nat) = 2 ^ 6 := rfl
  rcases hop with hop | hop | hop <;> rw [hop]
  · match l, h with
    | [], _ => decide
    | [a], h => exact h a (by simp)
    | a :: b :: _, h => exact lt_of_le_of_lt Nat.and_le_left (h a (by simp))
  · match l, h with
    | [], _ => decide
    | [a], h => exact h a (by simp)
    | a :: b :: _, h =>
      rw [h32] at h ⊢; exact Nat.or_lt_two_pow (h a (by simp)) (h b (by simp))
  · simp only [mev]
    have : l.headD 0 < 64 := by
      cases l with
      | nil => decide
      | cons a _ => exact h a (by simp)
    rw [h32] at this ⊢; exact Nat.xor_lt_two_pow (by decide) this

theorem getD_mem {w : List Nat} {i : Nat} (hi : i < w.length) : w.getD i 0 ∈ w := by
  rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi

theorem mwires_lt : ∀ (gs : List Gate) (w : List Nat), (∀ g ∈ gs, Ok g) →
    (∀ x ∈ w, x < 64) → ∀ x ∈ mwires gs w, x < 64 := by
  intro gs
  induction gs with
  | nil => intro w _ hw; exact hw
  | cons g gs ih =>
    intro w hok hw
    rw [mwires_cons]
    refine ih _ (fun g' hg' => hok g' (by simp [hg'])) ?_
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hw x hx
    · rw [List.mem_singleton.1 hx]
      refine mev_lt g (hok g (by simp)) _ (by simp) ?_
      intro y hy
      obtain ⟨i, _, rfl⟩ := List.mem_map.1 hy
      by_cases hi : i < w.length
      · exact hw _ (getD_mem hi)
      · rw [List.getD_eq_default _ _ (by omega)]; decide

/-- The new mask is one already present, or one of `opts`. -/
theorem mev_cases (g : Gate) (hg : Ok g) (w L : List Nat) (r : Nat)
    (hrd : ∀ i ∈ g.inputs, i < w.length) (h0 : 0 ∈ w) (h31 : 63 ∈ w) (hwL : ∀ x, x ∈ w ↔ x ∈ L)
    (hnot : g.op = GateOp.not → 0 < r) :
    let v := mev g.op (g.inputs.map fun i => w.getD i 0)
    v ∈ L ∨ ∃ p ∈ opts L r, p.1 = v ∧ (g.op = GateOp.not → p.2 = r - 1) ∧ (g.op ≠ GateOp.not → p.2 = r) := by
  intro v
  obtain ⟨hop, hlen⟩ := hg
  have hm : ∀ i ∈ g.inputs, w.getD i 0 ∈ L := fun i hi => (hwL _).1 (getD_mem (hrd i hi))
  have mAnd : ∀ a ∈ L, ∀ b ∈ L, (a &&& b, r) ∈ opts L r := fun a ha b hb => by
    simp only [opts, List.mem_append, List.mem_flatMap, List.mem_cons]
    exact Or.inl ⟨a, ha, b, hb, Or.inl rfl⟩
  have mOr : ∀ a ∈ L, ∀ b ∈ L, (a ||| b, r) ∈ opts L r := fun a ha b hb => by
    simp only [opts, List.mem_append, List.mem_flatMap, List.mem_cons]
    exact Or.inl ⟨a, ha, b, hb, Or.inr (Or.inl rfl)⟩
  rcases hop with hop | hop | hop
  · simp only [v, hop]
    match hgi : g.inputs, hm with
    | [], _ => left; exact (hwL _).1 h31
    | [i], hm => left; exact hm i (by simp)
    | i :: j :: _, hm =>
      right; exact ⟨_, mAnd _ (hm i (by simp)) _ (hm j (by simp)), rfl, (fun h => by cases h), fun _ => rfl⟩
  · simp only [v, hop]
    match hgi : g.inputs, hm with
    | [], _ => left; exact (hwL _).1 h0
    | [i], hm => left; exact hm i (by simp)
    | i :: j :: _, hm =>
      right; exact ⟨_, mOr _ (hm i (by simp)) _ (hm j (by simp)), rfl, (fun h => by cases h), fun _ => rfl⟩
  · have hr := hnot hop
    have ha : (g.inputs.map fun i => w.getD i 0).headD 0 ∈ L := by
      cases hgi : g.inputs with
      | nil => exact (hwL _).1 h0
      | cons i _ => simp only [List.map_cons, List.headD_cons]; exact hm i (by simp [hgi])
    right
    refine ⟨(63 ^^^ (g.inputs.map fun i => w.getD i 0).headD 0, r - 1), ?_, by simp [v, hop, mev], fun _ => rfl, fun h => absurd hop h⟩
    simp only [opts, List.mem_append]
    right; rw [if_pos hr]; exact List.mem_map.2 ⟨_, ha, rfl⟩

theorem main : ∀ (gs : List Gate) (w L : List Nat) (d r : Nat),
    (∀ g ∈ gs, Ok g) →
    (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < w.length + j) →
    (gs.filter fun g => decide (g.op = GateOp.not)).length ≤ r → gs.length ≤ d →
    0 ∈ w → 63 ∈ w → (∀ x, x ∈ w ↔ x ∈ L) →
    search d L r = true → ¬ (8 ∈ mwires gs w ∧ 34 ∈ mwires gs w ∧ 46 ∈ mwires gs w) := by
  intro gs
  induction gs with
  | nil =>
    intro w L d r _ _ _ _ _ _ hwL hs h
    have := search_hasAll _ _ _ hs
    simp only [mwires, List.foldl_nil] at h
    simp [hasAll, (hwL _).1 h.1, (hwL _).1 h.2.1, (hwL _).1 h.2.2] at this
  | cons g gs ih =>
    intro w L d r hok hrb hnc hlen h0 h31 hwL hs
    rw [mwires_cons]
    obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by simp at hlen; omega⟩
    have hrd : ∀ i ∈ g.inputs, i < w.length := fun i hi => by simpa using hrb 0 (by simp) i hi
    have hnc' : g.op = GateOp.not → 0 < r := fun h => by
      simp only [List.filter_cons, h, decide_true, if_true, List.length_cons] at hnc; omega
    have hgs : ∀ g' ∈ gs, Ok g' := fun g' h => hok g' (by simp [h])
    have hrb' : ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs,
        i < (w ++ [mev g.op (g.inputs.map fun i => w.getD i 0)]).length + j := by
      intro j hj i hi
      have := hrb (j + 1) (by simp; omega) i (by simpa using hi)
      simp; omega
    have hlen' : gs.length ≤ d := by simp at hlen; omega
    have h0' : 0 ∈ w ++ [mev g.op (g.inputs.map fun i => w.getD i 0)] := List.mem_append_left _ h0
    have h31' : 63 ∈ w ++ [mev g.op (g.inputs.map fun i => w.getD i 0)] := List.mem_append_left _ h31
    rw [sstep'] at hs
    obtain ⟨hsA, hprune | hsB⟩ := hs
    · -- too few gates left to add the missing targets
      rintro ⟨h4, h5, h22⟩
      have hm := missing_mwires gs (w ++ [mev g.op (g.inputs.map fun i => w.getD i 0)])
      have ha := missing_append w (mev g.op (g.inputs.map fun i => w.getD i 0))
      rw [missing_zero _ h4 h5 h22] at hm
      rw [missing_congr hwL] at ha
      simp only [List.length_cons] at hlen
      omega
    -- the NOT budget the rest of the gates may use
    have hncr : (gs.filter fun g => decide (g.op = GateOp.not)).length ≤
        (if g.op = GateOp.not then r - 1 else r) := by
      by_cases h : g.op = GateOp.not
      · simp only [List.filter_cons, h, decide_true, if_true, List.length_cons] at hnc; rw [if_pos h]; omega
      · simp only [List.filter_cons, h, decide_false, if_false] at hnc
        rw [if_neg h]; simpa using hnc
    rcases mev_cases g (hok g (by simp)) w L r hrd h0 h31 hwL hnc' with hv | ⟨p, hp, h1, h2, h3⟩
    · -- a repeated mask: the set is unchanged
      refine ih _ L d (if g.op = GateOp.not then r - 1 else r) hgs hrb' hncr hlen' h0' h31' ?_ ?_
      · intro x; constructor
        · intro hx; rcases List.mem_append.1 hx with hx | hx
          · exact (hwL x).1 hx
          · rw [List.mem_singleton.1 hx]; exact hv
        · intro hx; exact List.mem_append_left _ ((hwL x).2 hx)
      · refine search_budget _ _ r _ (by split <;> omega) (search_succ _ _ _ ?_)
        rw [sstep']
        exact ⟨hsA, Or.inr hsB⟩
    · have hpr : p.2 = (if g.op = GateOp.not then r - 1 else r) := by
        by_cases h : g.op = GateOp.not
        · rw [if_pos h]; exact h2 h
        · rw [if_neg h]; exact h3 h
      rcases hsB p hp with hc | hc
      · -- the mask was already present after all
        have hv : mev g.op (g.inputs.map fun i => w.getD i 0) ∈ L := by
          rw [← h1]; simpa using hc
        refine ih _ L d (if g.op = GateOp.not then r - 1 else r) hgs hrb' hncr hlen' h0' h31' ?_ ?_
        · intro x; constructor
          · intro hx; rcases List.mem_append.1 hx with hx | hx
            · exact (hwL x).1 hx
            · rw [List.mem_singleton.1 hx]; exact hv
          · intro hx; exact List.mem_append_left _ ((hwL x).2 hx)
        · refine search_budget _ _ r _ (by split <;> omega) (search_succ _ _ _ ?_)
          rw [sstep']
          exact ⟨hsA, Or.inr hsB⟩
      · refine ih _ (L ++ [p.1]) d p.2 hgs hrb' (hpr ▸ hncr) hlen' h0' h31' ?_ hc
        intro x; simp only [List.mem_append, List.mem_singleton, h1, hwL x]

/-- The bridge: the Boolean wires on input `t` are bit `t` of the masks. -/
theorem bridge (t : Nat) (ht : t < 6) : ∀ (gs : List Gate) (w : List Nat), (∀ g ∈ gs, Ok g) →
    gs.foldl (fun wb g => wb ++ [g.op.eval (g.inputs.map fun i => wb.getD i false)])
      (w.map (·.testBit t)) = (mwires gs w).map (·.testBit t) := by
  have h31 : (63 : Nat).testBit t = true := by interval_cases t <;> decide
  have hgd : ∀ (w : List Nat) (i : Nat), (w.map (·.testBit t)).getD i false = (w.getD i 0).testBit t := by
    intro w i
    have := List.getD_map (f := (·.testBit t)) (l := w) (n := i) (d := 0)
    simpa using this
  intro gs
  induction gs with
  | nil => intro w _; rfl
  | cons g gs ih =>
    intro w hok
    rw [mwires_cons, ← ih _ (fun g' h => hok g' (by simp [h]))]
    simp only [List.foldl_cons, List.map_append, List.map_cons, List.map_nil]
    congr 2
    simp only [hgd]
    obtain ⟨hop, hlen⟩ := hok g (by simp)
    generalize g.inputs = ins at hlen ⊢
    rcases hop with hop | hop | hop <;> rw [hop]
    · match ins, hlen with
      | [], _ => simp [GateOp.eval, mev, h31]
      | [i], _ => simp [GateOp.eval, mev]
      | [i, j], _ => simp [GateOp.eval, mev, Nat.testBit_and]
      | _ :: _ :: _ :: _, h => simp at h
    · match ins, hlen with
      | [], _ => simp [GateOp.eval, mev]
      | [i], _ => simp [GateOp.eval, mev]
      | [i, j], _ => simp [GateOp.eval, mev, Nat.testBit_or]
      | _ :: _ :: _ :: _, h => simp at h
    · cases ins with
      | nil => simp [GateOp.eval, mev, h31]
      | cons i _ => simp [GateOp.eval, mev, Nat.testBit_xor, h31]

theorem search_of (d : Nat) (L : List Nat) (r : Nat) (h1 : hasAll L = false)
    (h2 : ∀ p ∈ nexts L r, search d (L ++ [p.1]) p.2 = true) : search (d + 1) L r = true := by
  rw [sstep]
  simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, List.all_eq_true]
  exact ⟨h1, Or.inr h2⟩

theorem sk2 : search 5 [62, 60, 56, 48, 32, 0, 63, 1] 1 = true := by decide +kernel
theorem sk3 : search 5 [62, 60, 56, 48, 32, 0, 63, 3] 1 = true := by decide +kernel
theorem sk4 : search 5 [62, 60, 56, 48, 32, 0, 63, 7] 1 = true := by decide +kernel
theorem sk6 : search 4 [62, 60, 56, 48, 32, 0, 63, 15, 14] 1 = true := by decide +kernel
theorem sk7 : search 4 [62, 60, 56, 48, 32, 0, 63, 15, 12] 1 = true := by decide +kernel
theorem sk8 : search 4 [62, 60, 56, 48, 32, 0, 63, 15, 8] 1 = true := by decide +kernel
theorem sk9 : search 4 [62, 60, 56, 48, 32, 0, 63, 15, 47] 1 = true := by decide +kernel
theorem sk10 : search 4 [62, 60, 56, 48, 32, 0, 63, 15, 1] 0 = true := by decide +kernel
theorem sk11 : search 4 [62, 60, 56, 48, 32, 0, 63, 15, 3] 0 = true := by decide +kernel
theorem sk12 : search 4 [62, 60, 56, 48, 32, 0, 63, 15, 7] 0 = true := by decide +kernel
theorem sk13 : search 4 [62, 60, 56, 48, 32, 0, 63, 15, 31] 0 = true := by decide +kernel
theorem sk5 : search 5 [62, 60, 56, 48, 32, 0, 63, 15] 1 = true := by
  refine search_of _ _ _ (by decide) (fun p hp => ?_)
  have e : nexts [62, 60, 56, 48, 32, 0, 63, 15] 1 = [(14, 1), (12, 1), (8, 1), (47, 1), (1, 0), (3, 0), (7, 0), (31, 0)] := by decide +kernel
  rw [e] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [sk6, sk7, sk8, sk9, sk10, sk11, sk12, sk13]
theorem sk14 : search 5 [62, 60, 56, 48, 32, 0, 63, 31] 1 = true := by decide +kernel
theorem sk1 : search 6 [62, 60, 56, 48, 32, 0, 63] 2 = true := by
  refine search_of _ _ _ (by decide) (fun p hp => ?_)
  have e : nexts [62, 60, 56, 48, 32, 0, 63] 2 = [(1, 1), (3, 1), (7, 1), (15, 1), (31, 1)] := by decide +kernel
  rw [e] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  exacts [sk2, sk3, sk4, sk5, sk14]

theorem search_ok : search 6 [62, 60, 56, 48, 32, 0, 63] 2 = true := sk1

theorem eq_of_bits {m : Nat} (k : Nat) (hm : m < 64) (hk : k < 64)
    (h : ∀ t < 6, m.testBit t = k.testBit t) : m = k := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 6
  · exact h i hi
  · have h5 : (64 : Nat) ≤ 2 ^ i := by
      calc (64 : Nat) = 2 ^ 6 := rfl
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]

end PEqualNP.Outside.L_meta_51366_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_51366_aux in
theorem PEqualNP.Outside.L_meta_51366 : ¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 6 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (8 : Nat).testBit t.val ∧
    w.getD q.val false = (34 : Nat).testBit t.val ∧
    w.getD r.val false = (46 : Nat).testBit t.val) := by
  rintro ⟨D, p, q, r, hfan, hrb, hnot, hsize, hev⟩
  have hok : ∀ g ∈ D.gates, Ok g := by
    intro g hg
    obtain ⟨h1, h2⟩ := hfan g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    exact ⟨h1, h2⟩
  let w0 : List Nat := [62, 60, 56, 48, 32, 0, 63]
  have hxs : ∀ t : Fin 6, (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true] =
      w0.map (·.testBit t.val) := by decide
  have hlenM : (mwires D.gates w0).length = 7 + D.size := by
    rw [mwires_length]; rfl
  have hlt := mwires_lt D.gates w0 hok (by decide)
  -- each output wire carries the asked mask
  have key : ∀ (o : Fin (7 + D.size)) (k : Nat), k < 64 →
      (∀ t : Fin 6, (D.wires ((List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true])).getD o.val false = k.testBit t.val) →
      k ∈ mwires D.gates w0 := by
    intro o k hk ho
    have hin : o.val < (mwires D.gates w0).length := by rw [hlenM]; exact o.isLt
    have hm := getD_mem hin
    have : (mwires D.gates w0).getD o.val 0 = k := by
      refine eq_of_bits k (hlt _ hm) hk (fun t ht => ?_)
      have h := ho ⟨t, ht⟩
      rw [hxs, Circuit.wires, bridge t ht D.gates w0 hok] at h
      have := List.getD_map (f := (·.testBit t)) (l := mwires D.gates w0) (n := o.val) (d := 0)
      simp only [Nat.zero_testBit] at this
      rw [this] at h; exact h
    rw [← this]; exact hm
  have h4 := key p 8 (by decide) (fun t => (hev t).1)
  have h5 := key q 34 (by decide) (fun t => (hev t).2.1)
  have h22 := key r 46 (by decide) (fun t => (hev t).2.2)
  refine main D.gates w0 w0 6 2 hok ?_ ?_ hsize (by decide) (by decide) (fun _ => Iff.rfl) search_ok ⟨h4, h5, h22⟩
  · intro j hj i hi; exact hrb j hj i hi
  · exact hnot
