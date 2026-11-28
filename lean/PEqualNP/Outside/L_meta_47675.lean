import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_47675
open PEqualNP.CircuitLowerBounds
abbrev Row := Fin 128
abbrev Wire := Row → Bool
def bin (d a b : Nat) : Nat :=
  match d with
  | 0 => a &&& b
  | 1 => a ||| b
  | 2 => a ^^^ (a &&& b)
  | _ => b ^^^ (a &&& b)
def flipOp (d : Nat) : Nat :=
  match d with
  | 2 => 3
  | 3 => 2
  | _ => d
lemma bin_comm_flip (d : Nat) (hd : d < 4) (a b : Nat) : bin d a b = bin (flipOp d) b a := by
  interval_cases d <;> simp [bin, flipOp, Nat.and_comm, Nat.or_comm]
lemma flipOp_lt {d : Nat} (hd : d < 4) : flipOp d < 4 := by
  interval_cases d <;> decide
lemma testBit_bin (d a b r : Nat) :
    (bin d a b).testBit r =
      match d with
      | 0 => a.testBit r && b.testBit r
      | 1 => a.testBit r || b.testBit r
      | 2 => a.testBit r && !b.testBit r
      | _ => !a.testBit r && b.testBit r := by
  rcases d with _ | _ | _ | d <;>
    simp [bin, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor] <;>
    cases a.testBit r <;> cases b.testBit r <;> rfl
lemma bin_lt (d a b : Nat) (ha : a < 2^128) (hb : b < 2^128) : bin d a b < 2^128 := by
  have h1 : ∀ x y : Nat, x < 2^128 → y < 2^128 → (x &&& y) < 2^128 := fun x y hx _ =>
    Nat.lt_of_le_of_lt Nat.and_le_left hx
  have h2 : ∀ x y : Nat, x < 2^128 → y < 2^128 → (x ||| y) < 2^128 := fun x y hx hy =>
    Nat.or_lt_two_pow hx hy
  have h3 : ∀ x y : Nat, x < 2^128 → y < 2^128 → (x ^^^ y) < 2^128 := fun x y hx hy =>
    Nat.xor_lt_two_pow hx hy
  rcases d with _ | _ | _ | d
  · exact h1 a b ha hb
  · exact h2 a b ha hb
  · exact h3 a (a &&& b) ha (h1 a b ha hb)
  · exact h3 b (a &&& b) hb (h1 a b ha hb)
lemma bin_bit0 (d a b : Nat) (ha : a.testBit 0 = false) (hb : b.testBit 0 = false) :
    (bin d a b).testBit 0 = false := by
  rw [testBit_bin]
  rcases d with _ | _ | _ | d <;> simp [ha, hb]
def Live (T : Nat) : Nat → Finset Nat → Prop
  | 0, S => S = {T} ∧ T ≠ 0
  | k + 1, S => ∃ (U : Finset Nat) (a b d : Nat),
      d < 4 ∧ S = insert a (insert b U) ∧ a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live T k (insert (bin d a b) U)
lemma live_nonzero {T k S} (h : Live T k S) : ∀ a ∈ S, a ≠ 0 := by
  induction k generalizing S with
  | zero => obtain ⟨rfl, hT⟩ := h; simpa using hT
  | succ k ih =>
    obtain ⟨U, a, b, d, _, rfl, ha, hb, _, _, tail⟩ := h
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ha
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hb
    exact ih tail x (Finset.mem_insert_of_mem hx)
lemma live_size {T k S} (h : Live T k S) : S.card ≤ k + 1 := by
  induction k generalizing S with
  | zero => obtain ⟨rfl, _⟩ := h; simp
  | succ k ih =>
    obtain ⟨U, a, b, d, _, rfl, _, _, _, hf, tail⟩ := h
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    have ht := ih tail
    rw [Finset.card_insert_of_notMem hu] at ht
    have h1 := Finset.card_insert_le a (insert b U)
    have h2 := Finset.card_insert_le b U
    omega
lemma live_sep {T k S} (h : Live T k S) {r s : Nat} (hd : T.testBit r ≠ T.testBit s) :
    ∃ a ∈ S, a.testBit r ≠ a.testBit s := by
  induction k generalizing S with
  | zero => obtain ⟨rfl, _⟩ := h; exact ⟨T, by simp, hd⟩
  | succ k ih =>
    obtain ⟨U, a, b, d, _, rfl, _, _, _, _, tail⟩ := h
    obtain ⟨v, hv, hvd⟩ := ih tail
    rcases Finset.mem_insert.mp hv with rfl | hv
    · by_cases ha : a.testBit r = a.testBit s
      · refine ⟨b, by simp, fun hb => hvd ?_⟩
        rw [testBit_bin, testBit_bin, ha, hb]
      · exact ⟨a, by simp, ha⟩
    · exact ⟨v, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hv), hvd⟩
abbrev SWire := Bool × Nat
def swZero : SWire := (false, 0)
def swFlip (a : SWire) : SWire := (!a.1, a.2)
def opIdx (s t : Bool) : Nat := if s then (if t then 1 else 3) else (if t then 2 else 0)
def swMeet (a b : SWire) : SWire := (a.1 && b.1, bin (opIdx a.1 b.1) a.2 b.2)
def swJoin (a b : SWire) : SWire := swFlip (swMeet (swFlip a) (swFlip b))
def swRead (j : Nat) (a : SWire) : Bool := a.1 != a.2.testBit j
lemma swRead_zero (j : Nat) : swRead j swZero = false := by simp [swRead, swZero]
lemma swRead_flip (j : Nat) (a : SWire) : swRead j (swFlip a) = !(swRead j a) := by
  cases a with | mk s v => cases s <;> cases h : v.testBit j <;> simp [swRead, swFlip, h]
lemma swRead_meet (j : Nat) (a b : SWire) : swRead j (swMeet a b) = (swRead j a && swRead j b) := by
  obtain ⟨s, u⟩ := a; obtain ⟨t, v⟩ := b
  cases s <;> cases t <;> cases hu : u.testBit j <;> cases hv : v.testBit j <;>
    simp [swRead, swMeet, opIdx, testBit_bin, hu, hv]
lemma swRead_join (j : Nat) (a b : SWire) : swRead j (swJoin a b) = (swRead j a || swRead j b) := by
  simp only [swJoin, swRead_flip, swRead_meet]
  cases swRead j a <;> cases swRead j b <;> rfl
def swGate (w : List SWire) (g : Gate) : SWire :=
  let arg := fun i => w.getD i swZero
  match g.op, g.inputs with
  | .not, xs => swFlip (arg (xs.headD w.length))
  | .and, [] => swFlip swZero
  | .or, [] => swZero
  | .and, [i] | .or, [i] => arg i
  | .and, i :: j :: _ => swMeet (arg i) (arg j)
  | .or, i :: j :: _ => swJoin (arg i) (arg j)
  | _, _ => swZero
def swExec (gs : List Gate) (w : List SWire) : List SWire :=
  gs.foldl (fun w g => w ++ [swGate w g]) w
def isBin (g : Gate) : Bool := match g.op with | .not => false | _ => true
def reps (w : List SWire) : List Nat := w.map Prod.snd
def simple (w : List SWire) (z : Nat) : Prop := z = 0 ∨ z ∈ reps w
def priced (w : List SWire) (paid : Bool) (z : Nat) : Prop :=
  simple w z ∨ (paid = true ∧ ∃ d < 4, ∃ a ∈ reps w, ∃ b ∈ reps w, a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧ z = bin d a b)
lemma bin_eq_cases (d a b : Nat) (hd : d < 4) (h : a = 0 ∨ b = 0 ∨ a = b) :
    bin d a b = 0 ∨ bin d a b = a ∨ bin d a b = b := by
  rcases h with rfl | rfl | rfl <;> interval_cases d <;> simp [bin]
lemma opIdx_lt (s t : Bool) : opIdx s t < 4 := by cases s <;> cases t <;> decide
lemma get_simple (w : List SWire) (i : Nat) : simple w (w.getD i swZero).2 := by
  simp only [List.getD_eq_getElem?_getD]
  cases eq : w[i]? with
  | none => exact Or.inl rfl
  | some a => exact Or.inr (List.mem_map.mpr ⟨a, List.mem_of_getElem? eq, rfl⟩)
lemma made_priced (w : List SWire) (d : Nat) (a b : SWire) (hd : d < 4)
    (pa : simple w a.2) (pb : simple w b.2) : priced w true (bin d a.2 b.2) := by
  by_cases h : a.2 = 0 ∨ b.2 = 0 ∨ a.2 = b.2
  · rcases bin_eq_cases d a.2 b.2 hd h with e | e | e
    · exact Or.inl (Or.inl e)
    · rw [e]; exact Or.inl pa
    · rw [e]; exact Or.inl pb
  · push Not at h
    exact Or.inr ⟨rfl, d, hd, a.2, pa.resolve_left h.1, b.2, pb.resolve_left h.2.1, h.1, h.2.1, h.2.2, rfl⟩
lemma swGate_priced (w : List SWire) (g : Gate) : priced w (isBin g) (swGate w g).2 := by
  obtain ⟨op, xs⟩ := g
  cases op with
  | and =>
    rcases xs with _ | ⟨i, _ | ⟨j, t⟩⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (get_simple w i)
    · exact made_priced w _ _ _ (opIdx_lt _ _) (get_simple w i) (get_simple w j)
  | or =>
    rcases xs with _ | ⟨i, _ | ⟨j, t⟩⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (get_simple w i)
    · exact made_priced w _ _ _ (opIdx_lt _ _) (get_simple w i) (get_simple w j)
  | not => exact Or.inl (get_simple w _)
  | _ => exact Or.inl (Or.inl rfl)
lemma swGate_lt (w : List SWire) (hw : ∀ u ∈ w, u.2 < 2^128 ∧ u.2.testBit 0 = false) (g : Gate) :
    (swGate w g).2 < 2^128 ∧ (swGate w g).2.testBit 0 = false := by
  have hz : (0 : Nat) < 2^128 ∧ (0 : Nat).testBit 0 = false := ⟨by decide, by decide⟩
  have hg (i : Nat) : (w.getD i swZero).2 < 2^128 ∧ (w.getD i swZero).2.testBit 0 = false := by
    simp only [List.getD_eq_getElem?_getD]
    cases eq : w[i]? with
    | none => exact hz
    | some a => exact hw a (List.mem_of_getElem? eq)
  obtain ⟨op, xs⟩ := g
  cases op with
  | and =>
    rcases xs with _ | ⟨i, _ | ⟨j, t⟩⟩
    · exact hz
    · exact hg i
    · exact ⟨bin_lt _ _ _ (hg i).1 (hg j).1, bin_bit0 _ _ _ (hg i).2 (hg j).2⟩
  | or =>
    rcases xs with _ | ⟨i, _ | ⟨j, t⟩⟩
    · exact hz
    · exact hg i
    · exact ⟨bin_lt _ _ _ (hg i).1 (hg j).1, bin_bit0 _ _ _ (hg i).2 (hg j).2⟩
  | not => exact hg (xs.headD w.length)
  | _ => exact hz
lemma swExec_lt (gs : List Gate) (w : List SWire)
    (hw : ∀ u ∈ w, u.2 < 2^128 ∧ u.2.testBit 0 = false) :
    ∀ u ∈ swExec gs w, u.2 < 2^128 ∧ u.2.testBit 0 = false := by
  induction gs generalizing w with
  | nil => exact hw
  | cons g gs ih =>
    apply ih
    intro u hu
    rcases List.mem_append.mp hu with hu | hu
    · exact hw u hu
    · rw [List.mem_singleton.mp hu]; exact swGate_lt w hw g
lemma swRead_get (j : Nat) (w : List SWire) (i : Nat) :
    (w.map (swRead j)).getD i false = swRead j (w.getD i swZero) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[i]? <;> simp [swRead_zero]
lemma swGate_read (w : List SWire) (g : Gate)
    (legal : (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) (j : Nat) :
    swRead j (swGate w g) = g.op.eval (g.inputs.map fun i => (w.map (swRead j)).getD i false) := by
  simp_rw [swRead_get]
  obtain ⟨op, xs⟩ := g
  obtain ⟨hop, hlen⟩ := legal
  rcases hop with rfl | rfl | rfl <;>
    rcases xs with _ | ⟨i, _ | ⟨k, _ | ⟨h, rest⟩⟩⟩ <;>
    simp_all [swGate, GateOp.eval, swRead_flip, swRead_meet, swRead_join, swRead_zero]
lemma swExec_read (j : Nat) (gs : List Gate) (w : List SWire)
    (legal : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) :
    (swExec gs w).map (swRead j) =
      gs.foldl (fun l g => l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)]) (w.map (swRead j)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (swExec gs (w ++ [swGate w g])).map (swRead j) = _
    rw [ih _ (fun v hv => legal v (List.mem_cons_of_mem _ hv))]
    simp [swGate_read w g (legal g List.mem_cons_self) j]
lemma pull_live {T k S w z p} (h : Live T k S) (op : priced w p z)
    (sub : ∀ a ∈ S, a ∈ reps w ++ [z]) :
    ∃ l V, l ≤ k + p.toNat ∧ Live T l V ∧ ∀ a ∈ V, a ∈ reps w := by
  by_cases needed : z ∈ S
  · by_cases avail : z ∈ reps w
    · refine ⟨k, S, by omega, h, fun a ha => ?_⟩
      rcases (by simpa using sub a ha : a ∈ reps w ∨ a = z) with old | rfl
      · exact old
      · exact avail
    · rcases op with easy | ⟨rfl, d, hd, a, ha, b, hb, na, nb, ab, rfl⟩
      · rcases easy with rfl | hm
        · exact (live_nonzero h 0 needed rfl).elim
        · exact (avail hm).elim
      · let U := S.erase (bin d a b)
        have tail : Live T k (insert (bin d a b) U) := by
          simpa [U, Finset.insert_erase needed] using h
        have old (x : Nat) (hx : x ∈ U) : x ∈ reps w := by
          obtain ⟨ne, mem⟩ := Finset.mem_erase.mp hx
          exact (by simpa using sub x mem : x ∈ reps w ∨ x = bin d a b).resolve_right ne
        have fresh : bin d a b ∉ insert a (insert b U) := by
          intro eq
          rcases Finset.mem_insert.mp eq with e | h'
          · exact avail (e.symm ▸ ha)
          rcases Finset.mem_insert.mp h' with e | u
          · exact avail (e.symm ▸ hb)
          · exact avail (old _ u)
        exact ⟨k + 1, insert a (insert b U), by simp,
          ⟨U, a, b, d, hd, rfl, na, nb, ab, fresh, tail⟩, by simpa using And.intro ha (And.intro hb old)⟩
  · exact ⟨k, S, by omega, h, fun a ha => (by simpa [show a ≠ z from fun e => needed (e ▸ ha)] using sub a ha)⟩
lemma extract_live {T} (hT : T ≠ 0) (gs : List Gate) (w : List SWire)
    (found : T ∈ reps (swExec gs w)) :
    ∃ k S, k ≤ gs.countP isBin ∧ Live T k S ∧ ∀ a ∈ S, a ∈ reps w := by
  induction gs generalizing w with
  | nil => exact ⟨0, {T}, by simp, ⟨rfl, hT⟩, by simpa [swExec] using found⟩
  | cons g gs ih =>
    obtain ⟨k, S, lim, h, sub⟩ := ih (w ++ [swGate w g]) found
    have sub' : ∀ a ∈ S, a ∈ reps w ++ [(swGate w g).2] := by simpa [reps] using sub
    obtain ⟨l, V, cost, hl, raw⟩ := pull_live h (swGate_priced w g) sub'
    refine ⟨l, V, ?_, hl, raw⟩
    rw [List.countP_cons]
    cases e : isBin g <;> simp [e] at cost ⊢ <;> omega
def invW (a : Wire) : Wire := fun r => !(a r)
def comb2 (isOr : Bool) (a b : Wire) : Wire :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def comb4 (d : Nat) (a b : Wire) : Wire :=
  match d with
  | 0 => comb2 false a b
  | 1 => comb2 true a b
  | 2 => comb2 false a (invW b)
  | _ => comb2 false (invW a) b
def Constant (a : Wire) : Prop := ∃ b : Bool, a = fun _ => b
noncomputable def wcost (a : Wire) : Nat := by classical exact if Constant a then 1 else 0
noncomputable def wmass (xs : List Wire) : Nat := (xs.map wcost).sum
def Avail (pool : List Wire) (v : Wire) : Prop := v ∈ pool ∨ Constant v ∨ invW v ∈ pool
def Supply (pool xs : List Wire) : Prop := ∀ a ∈ xs, Avail pool a
def Reach (roots : List Wire) : Nat → List Wire → Prop
  | 0, b => b = roots
  | p + 1, c => ∃ (op : Bool) (bank : List Wire) (a b : Wire),
      Reach roots p bank ∧ Avail bank a ∧ Avail bank b ∧ c = comb2 op a b :: bank
def kept {α : Type} (save : Bool) (x : α) (xs : List α) : List α := if save then x :: xs else xs
def Run (goal : Wire) : Nat → List Wire → Prop
  | 0, zs => List.Perm [goal] zs
  | s + 1, zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire) (rest : List Wire),
      op < 4 ∧ (a :: b :: rest).Perm zs ∧ Run goal s (comb4 op a b :: kept ka a (kept kb b rest))
lemma invW_inv (a : Wire) : invW (invW a) = a := by funext r; simp [invW]
lemma invW_const {a : Wire} (h : Constant a) : Constant (invW a) := by
  obtain ⟨v, rfl⟩ := h; exact ⟨!v, rfl⟩
lemma wcost_inv (a : Wire) : wcost (invW a) = wcost a := by
  have h : Constant (invW a) ↔ Constant a := ⟨fun hc => invW_inv a ▸ invW_const hc, invW_const⟩
  by_cases hc : Constant a
  · simp [wcost, hc, h.mpr hc]
  · simp [wcost, hc, mt h.mp hc]
lemma avail_inv {bank : List Wire} {a : Wire} (h : Avail bank a) : Avail bank (invW a) := by
  rcases h with h | h | h
  · exact Or.inr (Or.inr (by rwa [invW_inv]))
  · exact Or.inr (Or.inl (invW_const h))
  · exact Or.inl h
lemma avail_cons {bank : List Wire} {v : Wire} (w : Wire) (h : Avail bank v) : Avail (w :: bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (List.mem_cons_of_mem _))
lemma from_const (op : Bool) {a b : Wire} {bank : List Wire} (h : Constant a ∨ Constant b)
    (ha : Avail bank a) (hb : Avail bank b) : Avail bank (comb2 op a b) := by
  rcases h with ⟨v, rfl⟩ | ⟨v, rfl⟩ <;> cases op <;> cases v
  · exact Or.inr (Or.inl ⟨false, funext fun _ => by simp [comb2]⟩)
  · simpa [comb2] using hb
  · simpa [comb2] using hb
  · exact Or.inr (Or.inl ⟨true, funext fun _ => by simp [comb2]⟩)
  · exact Or.inr (Or.inl ⟨false, funext fun _ => by simp [comb2]⟩)
  · simpa [comb2] using ha
  · simpa [comb2] using ha
  · exact Or.inr (Or.inl ⟨true, funext fun _ => by simp [comb2]⟩)
lemma both_const (op : Bool) {a b : Wire} (ha : Constant a) (hb : Constant b) :
    Constant (comb2 op a b) := by
  obtain ⟨v, rfl⟩ := ha; obtain ⟨w, rfl⟩ := hb; cases op <;> exact ⟨_, rfl⟩
lemma extend_comb (roots : List Wire) {p bank a b} (d : Nat) (hd : d < 4)
    (hp : Reach roots p bank) (ha : Avail bank a) (hb : Avail bank b) :
    ∃ q next, Reach roots q next ∧ Avail next (comb4 d a b) ∧
      (∀ v, Avail bank v → Avail next v) ∧ q + wcost a + wcost b ≤ p + 1 + wcost (comb4 d a b) := by
  have hprep : ∃ op x y, comb4 d a b = comb2 op x y ∧ Avail bank x ∧ Avail bank y ∧
      wcost x = wcost a ∧ wcost y = wcost b := by
    interval_cases d
    · exact ⟨false, a, b, rfl, ha, hb, rfl, rfl⟩
    · exact ⟨true, a, b, rfl, ha, hb, rfl, rfl⟩
    · exact ⟨false, a, invW b, rfl, ha, avail_inv hb, rfl, wcost_inv b⟩
    · exact ⟨false, invW a, b, rfl, avail_inv ha, hb, wcost_inv a, rfl⟩
  obtain ⟨op, x, y, eq, hx, hy, cx, cy⟩ := hprep
  rw [eq, ← cx, ← cy]
  classical
  by_cases c : Constant x ∨ Constant y
  · refine ⟨p, bank, hp, from_const op c hx hy, fun _ h => h, ?_⟩
    by_cases hcx : Constant x <;> by_cases hcy : Constant y
    · simp [wcost, hcx, hcy, both_const op hcx hcy]
    · simp [wcost, hcx, hcy]
    · simp [wcost, hcx, hcy]
    · exact (c.elim hcx hcy).elim
  · have hcx : ¬Constant x := fun h => c (Or.inl h)
    have hcy : ¬Constant y := fun h => c (Or.inr h)
    exact ⟨p + 1, _, ⟨op, bank, x, y, hp, hx, hy, rfl⟩, Or.inl (by simp),
      fun _ h => avail_cons _ h, by simp [wcost, hcx, hcy]⟩
lemma wmass_kept (a : Wire) (xs : List Wire) (k : Bool) : wmass xs ≤ wmass (kept k a xs) := by
  cases k <;> simp [kept, wmass]
lemma contraction {goal : Wire} (nc : ¬Constant goal) {s ws} (h : Run goal s ws)
    (roots : List Wire) {p bank} (hp : Reach roots p bank) (hs : Supply bank ws) :
    ∃ q next, Reach roots q next ∧ Avail next goal ∧ q + wmass ws ≤ p + s := by
  classical
  induction s generalizing ws p bank with
  | zero =>
    have hmem : goal ∈ ws := h.mem_iff.mp (by simp)
    have hlen : wmass ws = wcost goal := by
      have := (h.map wcost).sum_eq
      simpa [wmass] using this.symm
    exact ⟨p, bank, hp, hs goal hmem, by simp [hlen, wcost, nc]⟩
  | succ s ih =>
    obtain ⟨op, ka, kb, a, b, rest, hd, perm, tail⟩ := h
    have hsa : Avail bank a := hs a (perm.mem_iff.mp (by simp))
    have hsb : Avail bank b := hs b (perm.mem_iff.mp (by simp))
    obtain ⟨r, T, hT, hz, inc, le⟩ := extend_comb roots op hd hp hsa hsb
    have ht : Supply T (comb4 op a b :: kept ka a (kept kb b rest)) := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hz
      · apply inc; apply hs; apply perm.mem_iff.mp
        cases ka <;> cases kb <;> simp [kept] at hv ⊢ <;> tauto
    obtain ⟨q, W, hW, hv, hl⟩ := ih tail hT ht
    have hm1 := wmass_kept a (kept kb b rest) ka
    have hm2 := wmass_kept b rest kb
    have hp_eq : wmass ws = wcost a + wcost b + wmass rest := by
      have := (perm.map wcost).sum_eq
      simpa [wmass, Nat.add_assoc] using this.symm
    have hcons : wmass (comb4 op a b :: kept ka a (kept kb b rest)) =
        wcost (comb4 op a b) + wmass (kept ka a (kept kb b rest)) := rfl
    rw [hcons] at hl
    exact ⟨q, W, hW, hv, by omega⟩
def restrictW (f : Row → Row) (a : Wire) : Wire := fun r => a (f r)
lemma restrict_run (f : Row → Row) {goal s ws} (h : Run goal s ws) :
    Run (restrictW f goal) s (ws.map (restrictW f)) := by
  induction s generalizing ws with
  | zero => exact h.map _
  | succ s ih =>
    obtain ⟨op, ka, kb, a, b, rest, hd, perm, tail⟩ := h
    have htail := ih tail
    have hk : ∀ (k : Bool) (x : Wire) (l : List Wire),
        (kept k x l).map (restrictW f) = kept k (restrictW f x) (l.map (restrictW f)) := by
      intro k x l; cases k <;> rfl
    have hc : restrictW f (comb4 op a b) = comb4 op (restrictW f a) (restrictW f b) := by
      funext r; rcases op with _ | _ | _ | op <;> rfl
    simp only [List.map_cons, hk, hc] at htail
    exact ⟨op, ka, kb, restrictW f a, restrictW f b, rest.map (restrictW f), hd,
      by simpa using perm.map (restrictW f), htail⟩
def obs (a : Nat) : Wire := fun r => a.testBit r.val
lemma obs_bin (d a b : Nat) : obs (bin d a b) = comb4 d (obs a) (obs b) := by
  funext r
  simp only [obs, testBit_bin, comb4, comb2, invW]
  rcases d with _ | _ | _ | d <;> rfl
lemma kept_nodup {α : Type} (c : Bool) (x : α) (l : List α) (hl : l.Nodup) (hx : x ∉ l) :
    (kept c x l).Nodup := by
  cases c <;> simp [kept, hl, hx]
lemma live_to_run {T k S} (h : Live T k S) (v : List Nat) (nd : v.Nodup) (eqv : v.toFinset = S) :
    Run (obs T) k (v.map obs) := by
  classical
  induction k generalizing S v with
  | zero =>
    obtain ⟨rfl, _⟩ := h
    have hp : [T].Perm v := List.perm_of_nodup_nodup_toFinset_eq (by simp) nd (by simp [eqv])
    exact hp.map obs
  | succ k ih =>
    obtain ⟨U, a, b, d, hd, rfl, _, _, hab, fresh, tail⟩ := h
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tl := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm : mid.Nodup := kept_nodup kb b rest hr br
    have am : a ∉ mid := by cases hkb : kb <;> simp [mid, kept, hkb, hab, ar]
    have ntl : tl.Nodup := kept_nodup ka a mid bm am
    have htl : tl.toFinset = U := by
      have kf (c : Bool) (x : Nat) (l : List Nat) : (kept c x l).toFinset = if c then insert x l.toFinset else l.toFinset := by
        cases c <;> simp [kept]
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kf, kf, er]
      ext j
      by_cases ha' : a ∈ U <;> by_cases hb' : b ∈ U <;> by_cases ja : j = a <;> by_cases jb : j = b <;>
        simp_all [ka, kb]
    have hf : bin d a b ∉ tl := fun hm =>
      fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (htl ▸ List.mem_toFinset.mpr hm)))
    have prog := ih tail (bin d a b :: tl) (List.nodup_cons.mpr ⟨hf, ntl⟩) (by simp [htl])
    have hk : ∀ (c : Bool) (x : Nat) (l : List Nat), (kept c x l).map obs = kept c (obs x) (l.map obs) := by
      intro c x l; cases c <;> rfl
    change Run (obs T) k ((bin d a b :: kept ka a (kept kb b rest)).map obs) at prog
    rw [List.map_cons, hk, hk, obs_bin] at prog
    have perm : (a :: b :: rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab, ar, br, hr]) nd
      ext j
      by_cases ja : j = a <;> by_cases jb : j = b <;> simp_all
    exact ⟨d, ka, kb, obs a, obs b, rest.map obs, hd, by simpa using perm.map obs, prog⟩
def normPack (f : Wire) : Nat :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => f r != f 0))).cast List.length_ofFn).toNat
lemma testBit_normPack (f : Wire) (r : Nat) :
    (normPack f).testBit r = if h : r < 128 then (f ⟨r, h⟩ != f 0) else false := by
  change ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => f r != f 0))).cast List.length_ofFn).getLsbD r = _
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases h : r < 128 <;> simp [h]
lemma normPack_eq_of_obs {a : Nat} (ha : a < 2^128) (h0 : a.testBit 0 = false) :
    normPack (obs a) = a := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack]
  by_cases hr : r < 128
  · simp [hr, obs, h0]
  · simp only [hr, dite_false]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega)))).symm
lemma normPack_inv (f : Wire) : normPack (invW f) = normPack f := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack, testBit_normPack]
  by_cases hr : r < 128
  · simp only [hr, dite_true, invW]
    cases f ⟨r, hr⟩ <;> cases f 0 <;> rfl
  · simp [hr]
lemma normPack_const {f : Wire} (h : Constant f) : normPack f = 0 := by
  obtain ⟨b, rfl⟩ := h
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack]
  by_cases hr : r < 128 <;> simp [hr]
lemma normPack_comb2 (op : Bool) (a b : Wire) :
    ∃ d < 4, normPack (comb2 op a b) = bin d (normPack a) (normPack b) := by
  refine ⟨opIdx (if op then !(a 0) else a 0) (if op then !(b 0) else b 0), opIdx_lt _ _, ?_⟩
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack, testBit_bin, testBit_normPack, testBit_normPack]
  by_cases hr : r < 128
  · simp only [hr, dite_true]
    cases op <;> cases ha0 : a 0 <;> cases hb0 : b 0 <;>
      cases har : a ⟨r, hr⟩ <;> cases hbr : b ⟨r, hr⟩ <;>
      simp [comb2, opIdx, ha0, hb0, har, hbr]
  · simp only [hr, dite_false]
    rcases opIdx _ _ with _ | _ | _ | d <;> rfl
lemma avail_normPack {bank : List Wire} {v : Wire} (h : Avail bank v) :
    normPack v = 0 ∨ normPack v ∈ bank.map normPack := by
  rcases h with hm | hc | hi
  · exact Or.inr (List.mem_map_of_mem hm)
  · exact Or.inl (normPack_const hc)
  · exact Or.inr (by rw [← normPack_inv v]; exact List.mem_map_of_mem hi)
lemma reach_to_live_sub {roots : List Wire} {p bank} (h : Reach roots p bank)
    {T k S} (run : Live T k S) (sub : ∀ a ∈ S, a ∈ bank.map normPack) :
    ∃ l V, l ≤ p + k ∧ Live T l V ∧ ∀ a ∈ V, a ∈ roots.map normPack := by
  induction p generalizing bank k S with
  | zero =>
    rcases h with rfl
    exact ⟨k, S, by omega, run, sub⟩
  | succ p ih =>
    obtain ⟨op, prev, a, b, hr, ha, hb, rfl⟩ := h
    obtain ⟨d, hd, eq⟩ := normPack_comb2 op a b
    let w := prev.map (fun f => (false, normPack f))
    have hreps : reps w = prev.map normPack := by simp [w, reps, List.map_map, Function.comp_def]
    have hp : priced w true (normPack (comb2 op a b)) := by
      rw [eq]
      exact made_priced w d (false, normPack a) (false, normPack b) hd
        (by simpa [simple, hreps] using avail_normPack ha)
        (by simpa [simple, hreps] using avail_normPack hb)
    have hsub' : ∀ x ∈ S, x ∈ reps w ++ [normPack (comb2 op a b)] := by
      intro x hx
      rcases List.mem_cons.mp (sub x hx) with rfl | hm
      · simp
      · simp [hreps, hm]
    obtain ⟨k', S', hk', run', sub'⟩ := pull_live run hp hsub'
    obtain ⟨l, V, hl, run'', sub''⟩ := ih hr run' (by simpa [hreps] using sub')
    simp only [Bool.toNat_true] at hk'
    exact ⟨l, V, by omega, run'', sub''⟩
def Lower (roots : List Nat) (T : Nat) (L : Nat) : Prop :=
  ∀ p bank, Reach (roots.map obs) p bank → Avail bank (obs T) → L ≤ p
def Impossible (T : Nat) (cap : Nat) (S : Finset Nat) : Prop :=
  ∀ k ≤ cap, ¬Live T k S
def Essential (T : Nat) (roots : List Nat) (a : Nat) : Prop :=
  ∃ r s : Row, T.testBit r.val ≠ T.testBit s.val ∧ ∀ v ∈ roots, v ≠ a → v.testBit r.val = v.testBit s.val
lemma raw_required {T k S} (h : Live T k S) (roots : List Nat) (a : Nat)
    (sub : ∀ v ∈ S, v ∈ roots) (he : Essential T roots a) : a ∈ S := by
  obtain ⟨r, s, hd, hiso⟩ := he
  obtain ⟨v, hv, hvd⟩ := live_sep h hd
  by_cases veq : v = a
  · exact veq ▸ hv
  · exact (hvd (hiso v (sub v hv) veq)).elim
lemma lower_of_impossible {roots : List Nat} {T L : Nat}
    (hT0 : T ≠ 0) (hTlt : T < 2^128) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^128 ∧ a.testBit 0 = false)
    (ess : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible T L roots.toFinset) : Lower roots T (L + 1) := by
  intro p bank hr ha
  have hnormT : normPack (obs T) = T := normPack_eq_of_obs hTlt hTb0
  have hnz : normPack (obs T) ≠ 0 := by rwa [hnormT]
  have hm : T ∈ bank.map normPack := by
    have h1 := (avail_normPack ha).resolve_left hnz
    rwa [hnormT] at h1
  obtain ⟨k, S, hk, run, sub⟩ := reach_to_live_sub hr (T := T) (k := 0) (S := {T}) ⟨rfl, hT0⟩ (by simpa using hm)
  have hmap : (roots.map obs).map normPack = roots := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id roots]
    apply List.map_congr_left
    intro a ha'
    exact normPack_eq_of_obs (hR a ha').1 (hR a ha').2
  rw [hmap] at sub
  have heq : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    exact ⟨fun ha' => raw_required run roots a sub (ess a ha'), sub a⟩
  by_contra! small
  exact noRun k (by omega) (heq.symm ▸ run)
lemma obs_not_const {T : Nat} (hT0 : T ≠ 0) (hTlt : T < 2^128) (hTb0 : T.testBit 0 = false) :
    ¬Constant (obs T) := by
  intro hc
  have h := normPack_const hc
  rw [normPack_eq_of_obs hTlt hTb0] at h
  exact hT0 h
def Slice (raw : List Nat) (T d : Nat) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Nat),
    (∀ r : Row, d.testBit (f r).val = true) ∧
    (∀ a ∈ raw, Avail (roots.map obs) (restrictW f (obs a))) ∧
    ¬Constant (restrictW f (obs T)) ∧
    ∀ p bank, Reach (roots.map obs) p bank → Avail bank (restrictW f (obs T)) → L ≤ p
def isConstM (d a : Nat) : Bool := (a &&& d == 0) || (a &&& d == d)
def availM (d : Nat) (pm : List Nat) (a : Nat) : Bool :=
  let m := a &&& d
  m == 0 || m == d || pm.contains m || pm.contains (d ^^^ m)
lemma masked_eq_obs {f : Row → Row} {d a b : Nat} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (eq : (a &&& d) = (b &&& d)) : restrictW f (obs a) = restrictW f (obs b) := by
  funext r
  have h := congrArg (fun x => x.testBit (f r).val) eq
  simpa [restrictW, obs, Nat.testBit_and, dom r] using h
lemma masked_zero_obs {f : Row → Row} {d a : Nat} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (eq : (a &&& d) = 0) : restrictW f (obs a) = fun _ => false := by
  funext r
  have h := congrArg (fun x => x.testBit (f r).val) eq
  simpa [restrictW, obs, Nat.testBit_and, dom r] using h
lemma masked_one_obs {f : Row → Row} {d a : Nat} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (eq : (a &&& d) = d) : restrictW f (obs a) = fun _ => true := by
  funext r
  have h := congrArg (fun x => x.testBit (f r).val) eq
  simpa [restrictW, obs, Nat.testBit_and, dom r] using h
lemma masked_comp_obs {f : Row → Row} {d a b : Nat} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (eq : (a &&& d) = (d ^^^ (b &&& d))) : restrictW f (obs a) = invW (restrictW f (obs b)) := by
  funext r
  have h := congrArg (fun x => x.testBit (f r).val) eq
  simp only [Nat.testBit_and, Nat.testBit_xor, dom r, Bool.and_true] at h
  simp only [restrictW, obs, invW, h]
  cases b.testBit (f r).val <;> rfl
def poolSupply (f : Row → Row) (bank : List Wire) (pool : List Nat) : Prop :=
  ∀ a ∈ pool, Avail bank (restrictW f (obs a))
lemma availM_sound {f : Row → Row} {d a : Nat} {bank : List Wire} {pool : List Nat}
    (dom : ∀ r : Row, d.testBit (f r).val = true)
    (hs : poolSupply f bank pool)
    (ok : availM d (pool.map (· &&& d)) a = true) :
    Avail bank (restrictW f (obs a)) := by
  simp only [availM, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq, List.mem_map] at ok
  rcases ok with ((h0 | h1) | ⟨v, hv, he⟩) | ⟨v, hv, he⟩
  · exact Or.inr (Or.inl ⟨false, masked_zero_obs dom h0⟩)
  · exact Or.inr (Or.inl ⟨true, masked_one_obs dom h1⟩)
  · exact (masked_eq_obs dom he.symm) ▸ hs v hv
  · have hinv := avail_inv (hs v hv)
    have hcomp : restrictW f (obs a) = invW (restrictW f (obs v)) := by
      have hx : (a &&& d) = d ^^^ (v &&& d) := by
        have := congrArg (d ^^^ ·) he
        simpa [Nat.xor_assoc, Nat.xor_comm, Nat.xor_self] using this.symm
      exact masked_comp_obs dom hx
    exact hcomp ▸ hinv
abbrev Choice := Nat × Nat × Nat
def choiceVal (c : Choice) : Nat := bin c.1 c.2.1 c.2.2
def choiceOK (d : Nat) (pm : List Nat) (c : Choice) : Bool :=
  decide (c.1 < 4) && availM d pm c.2.1 && availM d pm c.2.2
def makePool (d : Nat) (pool : List Nat) : List Choice → Option (List Nat)
  | [] => some pool
  | c :: cs => if choiceOK d (pool.map (· &&& d)) c then makePool d (choiceVal c :: pool) cs else none
lemma pay_choice {f : Row → Row} {d : Nat} {roots bank q} {pool : List Nat}
    (dom : ∀ r : Row, d.testBit (f r).val = true)
    (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (c : Choice) (valid : choiceOK d (pool.map (· &&& d)) c = true) :
    ∃ next, Reach roots (q + 1) next ∧ poolSupply f next (choiceVal c :: pool) := by
  simp only [choiceOK, Bool.and_eq_true, decide_eq_true_eq] at valid
  have ha := availM_sound dom hs valid.1.2
  have hb := availM_sound dom hs valid.2
  have hprep : ∃ op x y, comb4 c.1 (restrictW f (obs c.2.1)) (restrictW f (obs c.2.2)) = comb2 op x y ∧
      Avail bank x ∧ Avail bank y := by
    have hd := valid.1.1
    interval_cases c.1
    · exact ⟨false, _, _, rfl, ha, hb⟩
    · exact ⟨true, _, _, rfl, ha, hb⟩
    · exact ⟨false, _, _, rfl, ha, avail_inv hb⟩
    · exact ⟨false, _, _, rfl, avail_inv ha, hb⟩
  obtain ⟨op, x, y, eq, hx, hy⟩ := hprep
  refine ⟨comb2 op x y :: bank, ⟨op, bank, x, y, hp, hx, hy, rfl⟩, fun v hv => ?_⟩
  rcases List.mem_cons.mp hv with rfl | hv
  · have hcv : restrictW f (obs (choiceVal c)) = comb2 op x y := by
      rw [← eq]; funext r; simp only [choiceVal, restrictW, obs, testBit_bin, comb4, comb2, invW]
      rcases c.1 with _ | _ | _ | d' <;> rfl
    exact hcv ▸ Or.inl (by simp)
  · exact avail_cons _ (hs v hv)
lemma makePool_sound {d : Nat} {f : Row → Row} (dom : ∀ r : Row, d.testBit (f r).val = true)
    {roots bank q pool} (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (cs : List Choice) {res} (ok : makePool d pool cs = some res) :
    ∃ next, Reach roots (q + cs.length) next ∧ poolSupply f next res := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨bank, hp, hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next, hr, sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out, hr', sh'⟩ := ih hr sh ok
      exact ⟨out, by simpa [Nat.add_assoc, Nat.add_comm 1] using hr', sh'⟩
    next => contradiction
lemma count_constM {d : Nat} {f : Row → Row} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (ws : List Nat) : ws.countP (isConstM d) ≤ wmass ((ws.map obs).map (restrictW f)) := by
  classical
  induction ws with
  | nil => simp [wmass]
  | cons a ws ih =>
    simp only [List.countP_cons, List.map_cons, wmass, List.sum_cons] at ih ⊢
    cases h : isConstM d a
    · simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
      exact ih.trans (Nat.le_add_left _ _)
    · have hc : Constant (restrictW f (obs a)) := by
        simp only [isConstM, Bool.or_eq_true, beq_iff_eq] at h
        rcases h with h0 | h1
        · exact ⟨false, masked_zero_obs dom h0⟩
        · exact ⟨true, masked_one_obs dom h1⟩
      simp only [ite_true, wcost, hc]
      omega
structure BoundPool where
  dom : Nat
  lb : Nat
  paid : Nat
  wires : List Nat
  pm : List Nat
def ValidPool (_raw : List Nat) (T : Nat) (c : BoundPool) : Prop :=
  c.pm = c.wires.map (· &&& c.dom) ∧
  ∃ (f : Row → Row) (roots : List Nat) (bank : List Wire),
    (∀ r : Row, c.dom.testBit (f r).val = true) ∧ ¬Constant (restrictW f (obs T)) ∧
    (∀ q ws, Reach (roots.map obs) q ws → Avail ws (restrictW f (obs T)) → c.lb ≤ q) ∧
    Reach (roots.map obs) c.paid bank ∧ poolSupply f bank c.wires
def materialize (raw : List Nat) (cs : List Choice) (d lb : Nat) : Option BoundPool :=
  (makePool d raw cs).map fun pool => ⟨d, lb, cs.length, pool, pool.map (· &&& d)⟩
lemma materialize_sound {raw T d L cs c} (sl : Slice raw T d L)
    (h : materialize raw cs d L = some c) : ValidPool raw T c := by
  unfold materialize at h
  cases he : makePool d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he, Option.map_some, Option.some.injEq] at h
    subst c
    obtain ⟨f, roots, dom, base, nc, lo⟩ := sl
    obtain ⟨bank, hr, hs⟩ := makePool_sound dom (show Reach (roots.map obs) 0 (roots.map obs) from rfl) base cs he
    exact ⟨rfl, f, roots, bank, dom, nc, lo, by simpa using hr, hs⟩
def scalarPoolCut (c : BoundPool) (k : Nat) (rest : List Nat) (op : Choice) : Bool :=
  let z := choiceVal op
  let extra := !(availM c.dom c.pm z)
  decide (k + c.paid + extra.toNat < c.lb + (z :: rest).countP (isConstM c.dom)) &&
    rest.all (availM c.dom c.pm) && (!extra || choiceOK c.dom c.pm op)
lemma scalarPoolCut_sound {raw T c} (valid : ValidPool raw T c) {k rest op}
    (nd : (choiceVal op :: rest).Nodup) (cut : scalarPoolCut c k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  obtain ⟨hpm, f, roots, bank, dom, nc, lo, hp, hs⟩ := valid
  simp only [scalarPoolCut, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true] at cut
  intro t ht run
  have finish (n : Nat) (out : List Wire) (hr : Reach (roots.map obs) n out)
      (hsup : poolSupply f out (choiceVal op :: rest))
      (hle : n = c.paid + (!(availM c.dom c.pm (choiceVal op))).toNat) : False := by
    have hcov : Supply out (((choiceVal op :: rest).map obs).map (restrictW f)) := by
      intro v hv
      obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hv
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
      exact hsup a ha
    obtain ⟨q, next, hq, hav, hbound⟩ :=
      contraction nc (restrict_run f (live_to_run run (choiceVal op :: rest) nd rfl)) (roots.map obs) hr hcov
    have hlo := lo q next hq hav
    have hcm := count_constM dom (choiceVal op :: rest)
    have hineq := cut.1.1
    omega
  cases hav : availM c.dom c.pm (choiceVal op) with
  | true =>
    apply finish c.paid bank hp _ (by simp [hav])
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact availM_sound dom hs (hpm ▸ hav)
    · exact availM_sound dom hs (hpm ▸ cut.1.2 a ha)
  | false =>
    have hok : choiceOK c.dom (c.wires.map (· &&& c.dom)) op = true := by
      have h2 := cut.2
      simp only [hav, Bool.not_false, Bool.not_true, Bool.false_eq_true, false_or] at h2
      exact hpm ▸ h2
    obtain ⟨out, hr, hc⟩ := pay_choice dom hp hs op hok
    apply finish (c.paid + 1) out hr _ (by simp [hav])
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hc (choiceVal op) (by simp)
    · have hpt : poolSupply f out c.wires := fun v hv => hc v (List.mem_cons_of_mem _ hv)
      exact availM_sound dom hpt (hpm ▸ cut.1.2 a ha)
def fixRow (z o : Nat) (r : Row) : Row :=
  ⟨((r.val &&& (127 ^^^ z)) ||| o) % 128, Nat.mod_lt _ (by decide)⟩
def renameW (f : Row → Row) (a : Nat) : Nat :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).toNat
lemma testBit_renameW (f : Row → Row) (a : Nat) (r : Row) :
    (renameW f a).testBit r.val = a.testBit (f r).val := by
  change ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).getLsbD r.val = _
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn, r.isLt, dite_true, Option.getD_some]
lemma renameW_lt (f : Row → Row) (a : Nat) : renameW f a < 2^128 :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).isLt
lemma obs_renameW (f : Row → Row) (a : Nat) : obs (renameW f a) = restrictW f (obs a) := by
  funext r; exact testBit_renameW f a r
lemma renameW_bin (f : Row → Row) (d a b : Nat) :
    renameW f (bin d a b) = bin d (renameW f a) (renameW f b) := by
  apply Nat.eq_of_testBit_eq
  intro r
  by_cases hr : r < 128
  · rw [testBit_renameW f _ ⟨r, hr⟩, testBit_bin, testBit_bin, testBit_renameW f _ ⟨r, hr⟩, testBit_renameW f _ ⟨r, hr⟩]
  · have hlt (x : Nat) : (renameW f x).testBit r = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt f x) (Nat.pow_le_pow_right (by decide) (by omega)))
    rw [hlt, testBit_bin, hlt, hlt]
    rcases d with _ | _ | _ | d <;> rfl
lemma renameW_zero (f : Row → Row) : renameW f 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 128
  · simpa using testBit_renameW f 0 ⟨r, hr⟩
  · rw [Nat.zero_testBit]
    exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt f 0) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 128 ≤ r)))
lemma renameW_inj (f : Row → Row) (onto : Function.Surjective f) {a b : Nat}
    (ha : a < 2^128) (hb : b < 2^128) (eq : renameW f a = renameW f b) : a = b := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 128
  · obtain ⟨q, hq⟩ := onto ⟨r, hr⟩
    have h := congrArg (fun x => x.testBit q.val) eq
    rw [testBit_renameW, testBit_renameW, hq] at h
    exact h
  · have hge : 128 ≤ r := by omega
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide : 0 < 2) hge)),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide : 0 < 2) hge))]
lemma live_renameW {T k S} (h : Live T k S) (hS : ∀ a ∈ S, a < 2^128) (f : Row → Row)
    (onto : Function.Surjective f) : Live (renameW f T) k (S.image (renameW f)) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl, hT⟩ := h
    have hTlt : T < 2^128 := hS T (by simp)
    refine ⟨by simp, fun hz => hT (renameW_inj f onto hTlt (by decide) (hz.trans (renameW_zero f).symm))⟩
  | succ k ih =>
    obtain ⟨U, a, b, d, hd, rfl, ha, hb, hab, fresh, tail⟩ := h
    have halt : a < 2^128 := hS a (by simp)
    have hblt : b < 2^128 := hS b (by simp)
    have hUlt : ∀ x ∈ U, x < 2^128 := fun x hx => hS x (by simp [hx])
    have hzlt : bin d a b < 2^128 := bin_lt d a b halt hblt
    have htail_lt : ∀ x ∈ insert (bin d a b) U, x < 2^128 := by
      intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx; exact hzlt; exact hUlt x hx
    have nr := ih tail htail_lt
    simp only [Finset.image_insert, renameW_bin] at nr ⊢
    refine ⟨U.image (renameW f), renameW f a, renameW f b, d, hd, rfl,
      fun hz => ha (renameW_inj f onto halt (by decide) (hz.trans (renameW_zero f).symm)),
      fun hz => hb (renameW_inj f onto hblt (by decide) (hz.trans (renameW_zero f).symm)),
      fun heq => hab (renameW_inj f onto halt hblt heq), ?_, nr⟩
    intro hm
    rw [← renameW_bin] at hm
    rcases Finset.mem_insert.mp hm with heq | hm
    · exact fresh (by rw [renameW_inj f onto hzlt halt heq]; simp)
    rcases Finset.mem_insert.mp hm with heq | hm
    · exact fresh (by rw [renameW_inj f onto hzlt hblt heq]; simp)
    obtain ⟨x, hx, heq⟩ := Finset.mem_image.mp hm
    exact fresh (by rw [renameW_inj f onto hzlt (hUlt x hx) heq.symm]; simp [hx])
lemma wmass_append (a b : List Wire) : wmass (a ++ b) = wmass a + wmass b := by simp [wmass]
lemma wmass_consts (xs : List Wire) (hc : ∀ x ∈ xs, Constant x) : wmass xs = xs.length := by
  classical
  induction xs with
  | nil => simp [wmass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [wmass, List.map_cons, List.sum_cons, List.length_cons, wcost, ha, ite_true]
    have := ih (fun x hx => hc x (by simp [hx]))
    simp only [wmass] at this
    omega
lemma lower_slice {roots other : List Nat} {T G : Nat}
    (hT0 : T ≠ 0) (hTlt : T < 2^128) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^128 ∧ a.testBit 0 = false)
    (hG0 : G ≠ 0) (hGlt : G < 2^128) (hGb0 : G.testBit 0 = false)
    (f : Row → Row) (eq : renameW f T = G)
    (covered : ∀ a ∈ roots, Avail (other.map obs) (restrictW f (obs a)))
    (singles : Finset Nat) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (restrictW f (obs a)))
    (L : Nat) (prior : Lower other G L) : Lower roots T (L + singles.card) := by
  classical
  intro p bank hr ha
  have hnormT : normPack (obs T) = T := normPack_eq_of_obs hTlt hTb0
  have hm : T ∈ bank.map normPack := by
    have h1 := (avail_normPack ha).resolve_left (by rwa [hnormT])
    rwa [hnormT] at h1
  obtain ⟨k, S, hk, run, sub⟩ := reach_to_live_sub hr (T := T) (k := 0) (S := {T}) ⟨rfl, hT0⟩ (by simpa using hm)
  have hmap : (roots.map obs).map normPack = roots := by
    rw [List.map_map]; conv_rhs => rw [← List.map_id roots]
    exact List.map_congr_left fun a ha' => normPack_eq_of_obs (hR a ha').1 (hR a ha').2
  rw [hmap] at sub
  have subS : singles ⊆ S := fun a hs => raw_required run roots a sub (necessary a hs)
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front, List.nodup_append]
    refine ⟨Finset.nodup_toList _, Finset.nodup_toList _, fun a ha b hb he => ?_⟩
    subst b; exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset = S := by ext a; simp [front, Finset.union_sdiff_of_subset subS]
  have gc : restrictW f (obs T) = obs G := (obs_renameW f T).symm.trans (congrArg obs eq)
  have hsup : Supply (other.map obs) ((front.map obs).map (restrictW f)) := by
    intro v hv
    obtain ⟨_, hm', rfl⟩ := List.mem_map.mp hv
    obtain ⟨a, ha', rfl⟩ := List.mem_map.mp hm'
    exact covered a (sub a (fe ▸ List.mem_toFinset.mpr ha'))
  obtain ⟨q, next, hq, hav, hbound⟩ :=
    contraction (gc ▸ obs_not_const hG0 hGlt hGb0) (restrict_run f (live_to_run run front nd fe))
      (other.map obs) (show Reach (other.map obs) 0 (other.map obs) from rfl) hsup
  have hlo := prior q next hq (gc ▸ hav)
  have hmass : singles.card ≤ wmass ((front.map obs).map (restrictW f)) := by
    simp only [front, List.map_append, wmass_append]
    let xs := (singles.toList.map obs).map (restrictW f)
    have hc : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_, hm', rfl⟩ := List.mem_map.mp hv
      obtain ⟨a, ha', rfl⟩ := List.mem_map.mp hm'
      exact constant a (Finset.mem_toList.mp ha')
    have hlen := wmass_consts xs hc
    simp only [xs, List.length_map, Finset.length_toList] at hlen
    change singles.card ≤ wmass xs + _
    rw [← hlen]
    exact Nat.le_add_right _ _
  have := hbound
  omega
def VAR (i : Nat) : Nat :=
  match i with
  | 0 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
  | 1 => 0xcccccccccccccccccccccccccccccccc
  | 2 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
  | 3 => 0xff00ff00ff00ff00ff00ff00ff00ff00
  | 4 => 0xffff0000ffff0000ffff0000ffff0000
  | 5 => 0xffffffff00000000ffffffff00000000
  | 6 => 0xffffffffffffffff0000000000000000
  | _ => 0
def ALL128 : Nat := 0xffffffffffffffffffffffffffffffff
def swapRow (i j : Nat) (r : Row) : Row :=
  let bi := r.val.testBit i
  let bj := r.val.testBit j
  if bi == bj then r
  else ⟨(r.val ^^^ (1 <<< i) ^^^ (1 <<< j)) % 128, Nat.mod_lt _ (by decide)⟩
def swapWord (i j : Nat) (w : Nat) : Nat :=
  let a := VAR i
  let b := VAR j
  let m10 := a ^^^ (a &&& b)
  let m01 := b ^^^ (a &&& b)
  let msame := ALL128 ^^^ (m10 ||| m01)
  let d := (1 <<< j) - (1 <<< i)
  (w &&& msame) ||| ((w &&& m10) <<< d) ||| ((w &&& m01) >>> d)
def permRow (swaps : List (Nat × Nat)) (r : Row) : Row :=
  swaps.foldl (fun x p => swapRow p.1 p.2 x) r
def permWord (swaps : List (Nat × Nat)) (w : Nat) : Nat :=
  swaps.foldr (fun p x => swapWord p.1 p.2 x) w
lemma swapRow_invol (i j : Nat) (hi : i < 7) (hj : j < 7) (r : Row) :
    swapRow i j (swapRow i j r) = r := by
  revert r
  interval_cases i <;> interval_cases j <;> decide +kernel
lemma swapWord_testBit (i j : Nat) (hij : i < j) (hj : j < 7) (w : Nat) (hw : w < 2^128) (r : Row) :
    (swapWord i j w).testBit r.val = w.testBit (swapRow i j r).val := by
  have hi : i < 7 := by omega
  have hspec : ∀ r : Row,
      let a := VAR i; let b := VAR j
      let m10 := a ^^^ (a &&& b); let m01 := b ^^^ (a &&& b); let msame := ALL128 ^^^ (m10 ||| m01)
      let d := (1 <<< j) - (1 <<< i)
      (msame.testBit r.val = true → (swapRow i j r).val = r.val ∧ (d ≤ r.val → m10.testBit (r.val - d) = false) ∧ m01.testBit (r.val + d) = false) ∧
      (msame.testBit r.val = false →
        (d ≤ r.val ∧ m10.testBit (r.val - d) = true ∧ (swapRow i j r).val = r.val - d ∧ m01.testBit (r.val + d) = false) ∨
        ((d ≤ r.val → m10.testBit (r.val - d) = false) ∧ m01.testBit (r.val + d) = true ∧ (swapRow i j r).val = r.val + d)) := by
    revert r; interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have hr := hspec r
  simp only [swapWord, Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Nat.add_comm]
  cases hms : (ALL128 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j)))).testBit r.val with
  | true =>
    obtain ⟨heq, h10, h01⟩ := hr.1 hms
    rw [heq]
    by_cases hd : (1 <<< j) - (1 <<< i) ≤ r.val
    · simp [hd, h10 hd, h01]
    · simp [hd, h01]
  | false =>
    rcases hr.2 hms with ⟨hd, h10, heq, h01⟩ | ⟨h10, h01, heq⟩
    · simp [hd, h10, heq, h01]
    · by_cases hd : (1 <<< j) - (1 <<< i) ≤ r.val
      · simp [hd, h10 hd, h01, heq]
      · simp [hd, h01, heq]
lemma swapWord_lt (i j : Nat) (hij : i < j) (hj : j < 7) (w : Nat) : swapWord i j w < 2^128 := by
  have hi : i < 7 := by omega
  have h1 : (ALL128 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j)))) < 2^128 := by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have h2 : ((VAR i ^^^ (VAR i &&& VAR j)) <<< ((1 <<< j) - (1 <<< i))) < 2^128 := by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have h3 : ((VAR j ^^^ (VAR i &&& VAR j)) >>> ((1 <<< j) - (1 <<< i))) < 2^128 := by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  unfold swapWord
  have e1 : (w &&& (ALL128 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j))))) < 2^128 :=
    Nat.lt_of_le_of_lt Nat.and_le_right h1
  have e2 : ((w &&& (VAR i ^^^ (VAR i &&& VAR j))) <<< ((1 <<< j) - (1 <<< i))) < 2^128 := by
    have hle : (w &&& (VAR i ^^^ (VAR i &&& VAR j))) ≤ (VAR i ^^^ (VAR i &&& VAR j)) := Nat.and_le_right
    calc ((w &&& (VAR i ^^^ (VAR i &&& VAR j))) <<< ((1 <<< j) - (1 <<< i)))
        = (w &&& (VAR i ^^^ (VAR i &&& VAR j))) * 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.shiftLeft_eq _ _
      _ ≤ (VAR i ^^^ (VAR i &&& VAR j)) * 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.mul_le_mul_right _ hle
      _ = ((VAR i ^^^ (VAR i &&& VAR j)) <<< ((1 <<< j) - (1 <<< i))) := (Nat.shiftLeft_eq _ _).symm
      _ < 2^128 := h2
  have e3 : ((w &&& (VAR j ^^^ (VAR i &&& VAR j))) >>> ((1 <<< j) - (1 <<< i))) < 2^128 := by
    have hle : (w &&& (VAR j ^^^ (VAR i &&& VAR j))) ≤ (VAR j ^^^ (VAR i &&& VAR j)) := Nat.and_le_right
    calc ((w &&& (VAR j ^^^ (VAR i &&& VAR j))) >>> ((1 <<< j) - (1 <<< i)))
        = (w &&& (VAR j ^^^ (VAR i &&& VAR j))) / 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.shiftRight_eq_div_pow _ _
      _ ≤ (VAR j ^^^ (VAR i &&& VAR j)) / 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.div_le_div_right hle
      _ = ((VAR j ^^^ (VAR i &&& VAR j)) >>> ((1 <<< j) - (1 <<< i))) := (Nat.shiftRight_eq_div_pow _ _).symm
      _ < 2^128 := h3
  exact Nat.or_lt_two_pow (Nat.or_lt_two_pow e1 e2) e3
lemma swapWord_eq_renameW (i j : Nat) (hij : i < j) (hj : j < 7) (w : Nat) (hw : w < 2^128) :
    swapWord i j w = renameW (swapRow i j) w := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 128
  · rw [swapWord_testBit i j hij hj w hw ⟨r, hr⟩, ← testBit_renameW (swapRow i j) w ⟨r, hr⟩]
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (swapWord_lt i j hij hj w) (Nat.pow_le_pow_right (by decide) (by omega))),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))]
def swapsValid (swaps : List (Nat × Nat)) : Bool :=
  swaps.all fun p => decide (p.1 < p.2) && decide (p.2 < 7)
lemma permWord_eq_renameW (swaps : List (Nat × Nat)) (hv : swapsValid swaps = true)
    (w : Nat) (hw : w < 2^128) : permWord swaps w = renameW (permRow swaps) w := by
  induction swaps generalizing w with
  | nil =>
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hr : r < 128
    · exact (testBit_renameW (permRow []) w ⟨r, hr⟩).symm
    · rw [show permWord [] w = w from rfl,
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))]
  | cons p ps ih =>
    simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hv
    have ihw := ih hv.2 w hw
    have hlt : permWord ps w < 2^128 := ihw ▸ renameW_lt _ w
    change swapWord p.1 p.2 (permWord ps w) = renameW (permRow (p :: ps)) w
    rw [swapWord_eq_renameW p.1 p.2 hv.1.1 hv.1.2 _ hlt, ihw]
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hr : r < 128
    · rw [testBit_renameW _ _ ⟨r, hr⟩, testBit_renameW _ _ (swapRow p.1 p.2 ⟨r, hr⟩), testBit_renameW _ _ ⟨r, hr⟩]
      rfl
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide) (by omega)))]
lemma permRow_surj (swaps : List (Nat × Nat)) (hv : swapsValid swaps = true) :
    Function.Surjective (permRow swaps) := by
  induction swaps with
  | nil => intro r; exact ⟨r, rfl⟩
  | cons p ps ih =>
    simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hv
    intro r
    obtain ⟨q, hq⟩ := ih hv.2 r
    refine ⟨swapRow p.1 p.2 q, ?_⟩
    change permRow ps (swapRow p.1 p.2 (swapRow p.1 p.2 q)) = r
    rw [swapRow_invol p.1 p.2 (by omega) hv.1.2, hq]
lemma permRow_rev_cancel (swaps : List (Nat × Nat)) (hv : swapsValid swaps = true) (r : Row) :
    permRow swaps.reverse (permRow swaps r) = r := by
  induction swaps generalizing r with
  | nil => rfl
  | cons p ps ih =>
    simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hv
    have h1 : permRow (p :: ps).reverse (permRow (p :: ps) r) =
        swapRow p.1 p.2 (permRow ps.reverse (permRow ps (swapRow p.1 p.2 r))) := by
      simp [permRow, List.reverse_cons, List.foldl_append]
    rw [h1, ih hv.2, swapRow_invol p.1 p.2 (by omega) hv.1.2]
lemma rotate_impossible {T n : Nat} {ws : List Nat} (hi : Impossible T n ws.toFinset)
    (swaps : List (Nat × Nat)) (hv : swapsValid swaps = true)
    (hT : T < 2^128) (hfix : permWord swaps T = T)
    (hw : ∀ a ∈ ws, a < 2^128) :
    Impossible T n (ws.map (permWord swaps)).toFinset := by
  intro k hk run
  have hr : ∀ a ∈ (ws.map (permWord swaps)).toFinset, a < 2^128 := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    rw [permWord_eq_renameW swaps hv x (hw x hx)]
    exact renameW_lt _ x
  have hvr : swapsValid swaps.reverse = true := by
    simp only [swapsValid, List.all_reverse]; exact hv
  have hinv_row2 : ∀ r : Row, permRow swaps (permRow swaps.reverse r) = r := by
    intro r; simpa using permRow_rev_cancel swaps.reverse hvr r
  have hinv_word : ∀ x : Nat, x < 2^128 → renameW (permRow swaps.reverse) (permWord swaps x) = x := by
    intro x hx
    rw [permWord_eq_renameW swaps hv x hx]
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hrr : r < 128
    · rw [testBit_renameW _ _ ⟨r, hrr⟩, testBit_renameW, hinv_row2]
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))]
  have run' := live_renameW run hr (permRow swaps.reverse) (permRow_surj swaps.reverse hvr)
  have hT' : renameW (permRow swaps.reverse) T = T := by
    conv_lhs => rw [← hfix]
    exact hinv_word T hT
  have hS' : (ws.map (permWord swaps)).toFinset.image (renameW (permRow swaps.reverse)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image, List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      rwa [hinv_word x (hw x hx)]
    · intro ha
      exact ⟨permWord swaps a, ⟨a, ha, rfl⟩, hinv_word a (hw a ha)⟩
  rw [hT', hS'] at run'
  exact hi k hk run'
abbrev Decor := Nat × Nat × Nat
def dbin (d : Nat) (x y : Decor) : Decor := (bin d x.1 y.1, bin d x.2.1 y.2.1, bin d x.2.2 y.2.2)
def dsep (x : Decor) : Nat := x.2.1 ^^^ x.2.2
def projBits (rows : List Nat) (w : Nat) : Nat :=
  rows.foldr (fun r acc => (acc <<< 1) ||| (if w.testBit r then 1 else 0)) 0
lemma testBit_projBits (rows : List Nat) (w i : Nat) :
    (projBits rows w).testBit i = match rows[i]? with | none => false | some r => w.testBit r := by
  induction rows generalizing i with
  | nil => simp [projBits]
  | cons r rs ih =>
    simp only [projBits, List.foldr_cons, Nat.testBit_or, Nat.testBit_shiftLeft]
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Nat.not_le.mpr (by decide : 0 < 1)]
      cases w.testBit r <;> rfl
    | succ i =>
      simp only [List.getElem?_cons_succ, Nat.le_add_left, decide_true, Bool.true_and, Nat.add_sub_cancel]
      have h0 : (if w.testBit r then (1 : Nat) else 0).testBit (i + 1) = false := by
        cases w.testBit r
        · simp
        · exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 1 < 2 ^ 1) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ i + 1)))
      rw [h0, Bool.or_false]
      exact ih i
lemma projBits_bin (rows : List Nat) (d a b : Nat) :
    projBits rows (bin d a b) = bin d (projBits rows a) (projBits rows b) := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [testBit_projBits, testBit_bin, testBit_projBits, testBit_projBits]
  cases rows[i]? with
  | none => rcases d with _ | _ | _ | d <;> rfl
  | some r => exact testBit_bin d a b r
def faithful (pos neg : List Nat) (x : Decor) : Prop :=
  x.2.1 = projBits pos x.1 ∧ x.2.2 = projBits neg x.1
lemma faithful_bin {pos neg x y} (d : Nat) (hx : faithful pos neg x) (hy : faithful pos neg y) :
    faithful pos neg (dbin d x y) :=
  ⟨by rw [dbin, hx.1, hy.1, projBits_bin], by rw [dbin, hx.2, hy.2, projBits_bin]⟩
def goodPairs (T : Nat) (pos neg : List Nat) : Prop :=
  pos.length = neg.length ∧ ∀ i < pos.length,
    T.testBit (pos.getD i 0) = true ∧ T.testBit (neg.getD i 0) = false
def fullMask (n : Nat) : Nat := (1 <<< n) - 1
abbrev Cov := Nat × Nat × Nat
def addCov (z : Nat) (c : Cov) : Cov :=
  (z ||| c.1, (z ^^^ (z &&& c.1)) ||| (c.2.1 ^^^ (c.2.1 &&& z)),
   (z &&& c.2.1) ||| (c.2.2 ^^^ (c.2.2 &&& z)))
def coverage (v : List Decor) : Cov := v.foldr (fun a c => addCov (dsep a) c) (0, 0, 0)
def takeOne (c : Cov) (a : Nat) : Nat := c.1 ^^^ (c.1 &&& (c.2.1 &&& a))
def takeTwo (c : Cov) (a b : Nat) : Nat :=
  c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
lemma cov_one (c : Cov) (a : Nat) : takeOne (addCov a c) a = c.1 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [takeOne, addCov, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor]
  cases a.testBit i <;> cases c.1.testBit i <;> cases c.2.1.testBit i <;> rfl
lemma cov_two (c : Cov) (a b : Nat) : takeTwo (addCov a (addCov b c)) a b = c.1 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [takeTwo, addCov, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
    cases c.2.1.testBit i <;> cases c.2.2.testBit i <;> rfl
lemma addCov_swap (c : Cov) (a b : Nat) : addCov a (addCov b c) = addCov b (addCov a c) := by
  apply Prod.ext
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [addCov, Nat.testBit_or]; cases a.testBit i <;> cases b.testBit i <;> rfl
  · apply Prod.ext <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
      simp only [addCov, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor] <;>
      cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
      cases c.2.1.testBit i <;> cases c.2.2.testBit i <;> rfl
lemma cov_perm {l r : List Decor} (h : l.Perm r) : coverage l = coverage r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (dsep a)) ih
  | swap _ _ _ => exact addCov_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2
def delOne (ws : List Decor) (a : Decor) (k : Bool) : List Decor := if k then ws else ws.erase a
def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) : List Decor := delOne (delOne ws a ka) b kb
def restCov (c : Cov) (a b : Nat) (ka kb : Bool) : Nat :=
  if ka then (if kb then c.1 else takeOne c b) else if kb then takeOne c a else takeTwo c a b
lemma cov_delOne {ws : List Decor} (a : Decor) (ha : a ∈ ws) (k : Bool) :
    (coverage (delOne ws a k)).1 = if k then (coverage ws).1 else takeOne (coverage ws) (dsep a) := by
  cases k
  · change (coverage (ws.erase a)).1 = _
    rw [cov_perm (List.perm_cons_erase ha)]
    exact (cov_one _ _).symm
  · rfl
lemma cov_delTwo {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) (ka kb : Bool) :
    (coverage (delTwo ws a b ka kb)).1 = restCov (coverage ws) (dsep a) (dsep b) ka kb := by
  cases ka <;> cases kb
  · have hbm : b ∈ ws.erase a := (List.mem_erase_of_ne ne.symm).mpr hb
    have hp : ws.Perm (a :: b :: (ws.erase a).erase b) :=
      (List.perm_cons_erase ha).trans (List.Perm.cons _ (List.perm_cons_erase hbm))
    change (coverage ((ws.erase a).erase b)).1 = takeTwo (coverage ws) _ _
    rw [cov_perm hp]
    exact (cov_two _ _ _).symm
  · exact cov_delOne a ha false
  · exact cov_delOne b hb false
  · rfl
lemma cov_testBit (ws : List Decor) (i : Nat) :
    (coverage ws).1.testBit i = true ↔ ∃ x ∈ ws, (dsep x).testBit i = true := by
  induction ws with
  | nil => simp [coverage]
  | cons a ws ih =>
    change (dsep a ||| (coverage ws).1).testBit i = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, ih]
    simp
lemma cov_required {T k pos neg} {ws : List Decor}
    (gp : goodPairs T pos neg) (hf : ∀ x ∈ ws, faithful pos neg x)
    (h : Live T k (ws.map Prod.fst).toFinset) :
    ((coverage ws).1 &&& fullMask pos.length) = fullMask pos.length := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and]
  have hfm : (fullMask pos.length).testBit i = decide (i < pos.length) := by
    simp [fullMask, Nat.shiftLeft_eq, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < pos.length
  · have ⟨hp, hn⟩ := gp.2 i hi
    have hsep : T.testBit (pos.getD i 0) ≠ T.testBit (neg.getD i 0) := by rw [hp, hn]; decide
    obtain ⟨v, hv, hvd⟩ := live_sep h hsep
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
    have hfx := hf x hx
    have hpi : pos[i]? = some (pos.getD i 0) := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    have hni : neg[i]? = some (neg.getD i 0) := by
      have hi' : i < neg.length := gp.1 ▸ hi
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
    have hbit : (dsep x).testBit i = true := by
      simp only [dsep, Nat.testBit_xor, hfx.1, hfx.2, testBit_projBits, hpi, hni]
      have h12 : x.1.testBit (pos.getD i 0) ≠ x.1.testBit (neg.getD i 0) := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
        exact hvd
      cases h1 : x.1.testBit (pos.getD i 0) <;> cases h2 : x.1.testBit (neg.getD i 0)
      · exact absurd (h1.trans h2.symm) h12
      · rfl
      · rfl
      · exact absurd (h1.trans h2.symm) h12
    have hc := (cov_testBit ws i).mpr ⟨x, hx, hbit⟩
    simp [hfm, hi, hc]
  · simp [hfm, hi]
def insertNat (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b :: bs => if a ≤ b then a :: b :: bs else b :: insertNat a bs
def sortNats : List Nat → List Nat
  | [] => []
  | a :: bs => insertNat a (sortNats bs)
lemma insertNat_perm (a : Nat) (l : List Nat) : (insertNat a l).Perm (a :: l) := by
  induction l with
  | nil => exact .refl _
  | cons b bs ih =>
    by_cases h : a ≤ b
    · simp [insertNat, h]
    · exact by simpa [insertNat, h] using (List.Perm.cons b ih).trans (.swap a b bs)
lemma sortNats_perm (l : List Nat) : (sortNats l).Perm l := by
  induction l with
  | nil => exact .refl _
  | cons a bs ih => exact (insertNat_perm a (sortNats bs)).trans (.cons a ih)
lemma sortNats_toFinset (l : List Nat) : (sortNats l).toFinset = l.toFinset := by
  ext x; simpa only [List.mem_toFinset] using (sortNats_perm l).mem_iff
def childTwo (ws : List Nat) (a b d : Nat) (ka kb : Bool) : List Nat :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))
lemma erase_toFinset {l : List Nat} (nd : l.Nodup) (a : Nat) :
    (l.erase a).toFinset = l.toFinset.erase a := by
  ext x; simp [nd.mem_erase_iff]
lemma enum_step {T cap : Nat} {ws : List Nat} (nd : ws.Nodup) (out : T ∉ ws)
    (stepOK : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d < 4, ∀ ka kb : Bool,
      a ≠ b → bin d a b ≠ 0 → bin d a b ∉ ws → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible T (cap - 1) (childTwo ws a b d ka kb).toFinset) :
    Impossible T cap ws.toFinset := by
  classical
  intro k hk h
  cases k with
  | zero =>
    obtain ⟨hS, _⟩ := h
    exact out (List.mem_toFinset.mp (hS ▸ Finset.mem_singleton_self T))
  | succ k =>
    obtain ⟨U, a, b, d, hd, he, _, _, hab, hf, tail⟩ := h
    have am : a ∈ ws := List.mem_toFinset.mp (he ▸ Finset.mem_insert_self a _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self b _))
    have fresh : bin d a b ∉ ws := fun hm => hf (he ▸ List.mem_toFinset.mpr hm)
    have hnz : bin d a b ≠ 0 := live_nonzero tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest = (ws.erase a).erase b from rfl, erase_toFinset (nd.erase _) b, erase_toFinset nd a]
    have kf (c : Bool) (x : Nat) (l : List Nat) : (kept c x l).toFinset = if c then insert x l.toFinset else l.toFinset := by
      cases c <;> simp [kept]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kf, kf, er, he]; ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j = a <;> by_cases jb : j = b <;> simp_all [ka, kb]
    have rn : rest.Nodup := (nd.erase _).erase _
    have ar : a ∉ rest := fun h => nd.not_mem_erase (List.mem_of_mem_erase h)
    have br : b ∉ rest := (nd.erase a).not_mem_erase
    have nk := kept_nodup kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept, ar, hab]
    have ndc : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr hm))),
        kept_nodup ka a _ nk ax⟩
    have eqc : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b :: kept ka a (kept kb b rest)).toFinset = _; simp [ke]
    have sc := live_size tail
    have hlen : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [← List.toFinset_card_of_nodup ndc, eqc]; omega
    exact stepOK a am b bm d hd ka kb hab hnz fresh hlen k (by omega) (eqc.symm ▸ tail)
lemma delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k; exact List.erase_sublist; exact List.Sublist.refl _
lemma delTwo_sub (ws : List Decor) (a b : Decor) (ka kb : Bool) : (delTwo ws a b ka kb).Sublist ws :=
  (delOne_sub _ _ _).trans (delOne_sub _ _ _)
lemma delTwo_len (ws : List Decor) (a b : Decor) (ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) :
    (delTwo ws a b ka kb).length = ws.length - (if ka then 0 else 1) - (if kb then 0 else 1) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne ne.symm).mpr hb
  cases ka <;> cases kb <;> simp [delTwo, delOne, List.length_erase_of_mem ha, List.length_erase_of_mem hb, List.length_erase_of_mem hm]
lemma unique_fst {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (eq : a.1 = b.1) : a = b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn, ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · rfl
    · exact (hn (eq ▸ List.mem_map_of_mem hb')).elim
    · exact (hn (eq.symm ▸ List.mem_map_of_mem ha')).elim
    · exact ih ht ha' hb'
lemma delTwo_map_toFinset {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (ne : a.1 ≠ b.1) (d : Nat) (ka kb : Bool) :
    ((dbin d a b).1 :: (delTwo ws a b ka kb).map Prod.fst).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  have wn : ws.Nodup := nd.of_map
  have dn : (delOne ws a ka).Nodup := wn.sublist (delOne_sub ws a ka)
  have m1 (l : List Decor) (hl : l.Nodup) (x y : Decor) (c : Bool) :
      y ∈ delOne l x c ↔ y ∈ l ∧ (y ≠ x ∨ c = true) := by
    cases c <;> simp [delOne, hl.mem_erase_iff, and_comm]
  have km (v : Nat) : v ∈ (delTwo ws a b ka kb).map Prod.fst ↔
      v ∈ ws.map Prod.fst ∧ (v ≠ a.1 ∨ ka = true) ∧ (v ≠ b.1 ∨ kb = true) := by
    simp only [delTwo, List.mem_map, m1 _ wn, m1 _ dn]
    constructor
    · rintro ⟨w, ⟨⟨hw, h1⟩, h2⟩, rfl⟩
      exact ⟨⟨w, hw, rfl⟩, h1.imp (fun h e => h (unique_fst nd hw ha e)) id,
        h2.imp (fun h e => h (unique_fst nd hw hb e)) id⟩
    · rintro ⟨⟨w, hw, rfl⟩, h1, h2⟩
      exact ⟨w, ⟨⟨hw, h1.imp (fun h e => h (congrArg Prod.fst e)) id⟩,
        h2.imp (fun h e => h (congrArg Prod.fst e)) id⟩, rfl⟩
  have av := List.mem_map_of_mem (f := Prod.fst) ha
  have bv := List.mem_map_of_mem (f := Prod.fst) hb
  have hkeep (c : Bool) (x : Nat) (l : List Nat) (v : Nat) : v ∈ kept c x l ↔ (v = x ∧ c = true) ∨ v ∈ l := by
    cases c <;> simp [kept]
  ext v
  simp only [childTwo, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, km, hkeep,
    (nd.erase _).mem_erase_iff, nd.mem_erase_iff, dbin]
  by_cases va : v = a.1 <;> by_cases vb : v = b.1 <;> cases ka <;> cases kb <;> simp_all
lemma childTwo_swap (v : List Nat) (nd : v.Nodup) (a b : Nat) (d : Nat) (hd : d < 4) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  have hkeep (c : Bool) (x : Nat) (l : List Nat) (y : Nat) : y ∈ kept c x l ↔ (y = x ∧ c = true) ∨ y ∈ l := by
    cases c <;> simp [kept]
  ext x
  simp only [childTwo, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, hkeep,
    (nd.erase _).mem_erase_iff, nd.mem_erase_iff, bin_comm_flip d hd a b]
  tauto
def varsOf (m : Nat) : List Nat :=
  (List.range 7).filterMap fun i => if m.testBit i then some (VAR i) else none
def subcube (z o : Nat) : Nat :=
  (List.range 128).foldr (fun r acc =>
    if (r &&& z == 0) && (r &&& o == o) then acc ||| (1 <<< r) else acc) 0
def fixWord (z o w : Nat) : Nat :=
  (List.range 128).foldr (fun r acc =>
    let fr := ((r &&& (127 ^^^ z)) ||| o) % 128
    if w.testBit fr then acc ||| (1 <<< r) else acc) 0
lemma testBit_foldr_bits (p : Nat → Bool) (l : List Nat) (r : Nat) :
    (l.foldr (fun i acc => if p i then acc ||| (1 <<< i) else acc) 0).testBit r =
      (decide (r ∈ l) && p r) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons]
    by_cases hpa : p a = true
    · simp only [hpa, ite_true, Nat.testBit_or, ih, Nat.testBit_shiftLeft]
      by_cases hra : r = a
      · subst hra; simp [hpa]
      · have h1 : (decide (a ≤ r) && (1 : Nat).testBit (r - a)) = false := by
          by_cases hle : a ≤ r
          · have hpos : r - a ≠ 0 := by omega
            simp only [hle, decide_true, Bool.true_and]
            exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 1 < 2 ^ 1) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ r - a)))
          · simp [hle]
        simp [h1, hra]
    · have hpf : p a = false := Bool.eq_false_iff.mpr hpa
      simp only [hpf, Bool.false_eq_true, ite_false, ih]
      by_cases hra : r = a
      · subst hra; simp [hpf]
      · simp [hra]
lemma fixWord_eq_renameW (z o w : Nat) : fixWord z o w = renameW (fixRow z o) w := by
  apply Nat.eq_of_testBit_eq; intro r
  unfold fixWord
  rw [testBit_foldr_bits]
  by_cases hr : r < 128
  · rw [testBit_renameW (fixRow z o) w ⟨r, hr⟩]
    simp [hr, fixRow]
  · simp only [List.mem_range, hr, decide_false, Bool.false_and]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))).symm
lemma subcube_fixRow (z o : Nat) (hz : z < 128) (ho : o < 128) (hzo : (z &&& o) = 0) (r : Row) :
    (subcube z o).testBit (fixRow z o r).val = true := by
  unfold subcube
  rw [testBit_foldr_bits]
  have hmem : (fixRow z o r).val ∈ List.range 128 := List.mem_range.mpr (fixRow z o r).isLt
  simp only [hmem, decide_true, Bool.true_and, Bool.and_eq_true, beq_iff_eq]
  have h127 : ((r.val &&& (127 ^^^ z)) ||| o) < 128 := by
    have hr := r.isLt
    have hlt1 : (r.val &&& (127 ^^^ z)) < 128 := Nat.lt_of_le_of_lt Nat.and_le_left hr
    exact Nat.or_lt_two_pow (n := 7) hlt1 ho
  have hval : (fixRow z o r).val = ((r.val &&& (127 ^^^ z)) ||| o) := Nat.mod_eq_of_lt h127
  rw [hval]
  constructor
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, Nat.zero_testBit]
    have hzi : (z.testBit i && o.testBit i) = false := by
      have := congrArg (fun x => x.testBit i) hzo; simpa [Nat.testBit_and] using this
    by_cases hi : i < 7
    · have h7 : (127 : Nat).testBit i = true := by interval_cases i <;> decide
      cases hzb : z.testBit i <;> cases hob : o.testBit i <;> simp_all [h7]
    · have hzf : z.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hz (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 7 ≤ i)))
      simp [hzf]
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_or]
    cases o.testBit i <;> simp
def checkEss1 (T : Nat) (roots : List Nat) (a r s : Nat) : Bool :=
  decide (r < 128) && decide (s < 128) && (T.testBit r != T.testBit s) &&
    roots.all fun v => v == a || (v.testBit r == v.testBit s)
lemma checkEss1_sound {T roots a r s} (h : checkEss1 T roots a r s = true) : Essential T roots a := by
  simp only [checkEss1, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  exact ⟨⟨r, h.1.1.1⟩, ⟨s, h.1.1.2⟩, h.1.2, fun v hv hne => (h.2 v hv).resolve_left hne⟩
def freeIn (other : List Nat) (w : Nat) : Bool := w == 0 || w == ALL128 || other.contains w
lemma freeIn_sound {other : List Nat} {f : Row → Row} {a : Nat} (ok : freeIn other (renameW f a) = true) :
    Avail (other.map obs) (restrictW f (obs a)) := by
  rw [← obs_renameW]
  simp only [freeIn, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at ok
  rcases ok with (h0 | h1) | hm
  · exact Or.inr (Or.inl ⟨false, by rw [h0]; funext r; simp [obs]⟩)
  · exact Or.inr (Or.inl ⟨true, by rw [h1]; funext r; simp only [obs, ALL128]; have := r.isLt; exact Nat.testBit_two_pow_sub_one 128 r.val |> fun e => by simpa [this] using e⟩)
  · exact Or.inl (List.mem_map_of_mem hm)
def checkProper (w : Nat) : Bool := w != 0 && decide (w < 2^128) && !w.testBit 0
lemma checkProper_sound {w : Nat} (h : checkProper w = true) : w ≠ 0 ∧ w < 2^128 ∧ w.testBit 0 = false := by
  simp only [checkProper, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq, Bool.not_eq_true'] at h
  exact ⟨h.1.1, h.1.2, h.2⟩
def checkRoots (rs : List Nat) : Bool := rs.all fun a => decide (a < 2^128) && !a.testBit 0
lemma checkRoots_sound {rs : List Nat} (h : checkRoots rs = true) :
    ∀ a ∈ rs, a < 2^128 ∧ a.testBit 0 = false := by
  simp only [checkRoots, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  exact h
def carryOK (swaps : List (Nat × Nat)) (roots1 : List Nat) (T1 : Nat) (roots2 : List Nat) (T2 : Nat) : Bool :=
  swapsValid swaps && checkProper T1 && checkRoots roots1 && checkProper T2 &&
    (permWord swaps T1 == T2) && roots1.all (fun a => freeIn roots2 (permWord swaps a))
lemma carry_of {swaps roots1 T1 roots2 T2 L} (ok : carryOK swaps roots1 T1 roots2 T2 = true)
    (hL : Lower roots2 T2 L) : Lower roots1 T1 L := by
  simp only [carryOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨hsv, hT1⟩, hR1⟩, hT2⟩, heq⟩, hcov⟩ := ok
  have ⟨p1a, p1b, p1c⟩ := checkProper_sound hT1
  have ⟨p2a, p2b, p2c⟩ := checkProper_sound hT2
  have hR1' := checkRoots_sound hR1
  have heq' : renameW (permRow swaps) T1 = T2 := (permWord_eq_renameW swaps hsv T1 p1b).symm.trans heq
  have hcov' : ∀ a ∈ roots1, Avail (roots2.map obs) (restrictW (permRow swaps) (obs a)) := fun a ha =>
    freeIn_sound (permWord_eq_renameW swaps hsv a (hR1' a ha).1 ▸ hcov a ha)
  simpa using lower_slice p1a p1b p1c hR1' p2a p2b p2c (permRow swaps) heq' hcov' ∅ (by simp) (by simp) L hL
def liftCheck (z o : Nat) (roots : List Nat) (T : Nat) (other : List Nat) (G : Nat)
    (essPairs : List (Nat × Nat × Nat)) : Bool :=
  checkProper T && checkRoots roots && checkProper G &&
    decide (essPairs.map Prod.fst).Nodup &&
    (fixWord z o T == G) &&
    roots.all (fun a => freeIn other (fixWord z o a)) &&
    essPairs.all (fun e => checkEss1 T roots e.1 e.2.1 e.2.2 &&
      (fixWord z o e.1 == 0 || fixWord z o e.1 == ALL128))
lemma lift_of {z o roots T other G essPairs L} (ok : liftCheck z o roots T other G essPairs = true)
    (hL : Lower other G L) : Lower roots T (L + essPairs.length) := by
  simp only [liftCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨⟨hT, hR⟩, hG⟩, hnd⟩, heq⟩, hcov⟩, hess⟩ := ok
  have ⟨p1a, p1b, p1c⟩ := checkProper_sound hT
  have ⟨p2a, p2b, p2c⟩ := checkProper_sound hG
  have hR' := checkRoots_sound hR
  have heq' : renameW (fixRow z o) T = G := (fixWord_eq_renameW z o T).symm.trans heq
  have hcov' : ∀ a ∈ roots, Avail (other.map obs) (restrictW (fixRow z o) (obs a)) := fun a ha =>
    freeIn_sound ((fixWord_eq_renameW z o a).symm ▸ hcov a ha)
  have hcard : (essPairs.map Prod.fst).toFinset.card = essPairs.length := by
    rw [List.toFinset_card_of_nodup hnd, List.length_map]
  rw [← hcard]
  apply lower_slice p1a p1b p1c hR' p2a p2b p2c (fixRow z o) heq' hcov' (essPairs.map Prod.fst).toFinset _ _ L hL
  · intro a ha
    obtain ⟨⟨v, r, s⟩, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    exact checkEss1_sound (hess (v, r, s) hm).1
  · intro a ha
    obtain ⟨⟨v, r, s⟩, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    have hc := (hess (v, r, s) hm).2
    simp only [Bool.or_eq_true, beq_iff_eq, fixWord_eq_renameW] at hc
    rw [← obs_renameW]
    rcases hc with h0 | h1
    · exact ⟨false, by rw [h0]; funext r'; simp [obs]⟩
    · exact ⟨true, by rw [h1]; funext r'; simp only [obs, ALL128]; have := r'.isLt; exact Nat.testBit_two_pow_sub_one 128 r'.val |> fun e => by simpa [this] using e⟩
def goodPairsCheck (T : Nat) (pos neg : List Nat) : Bool :=
  (pos.length == neg.length) &&
    (List.range pos.length).all fun i => T.testBit (pos.getD i 0) && !(T.testBit (neg.getD i 0))
lemma goodPairs_of {T pos neg} (ok : goodPairsCheck T pos neg = true) : goodPairs T pos neg := by
  simp only [goodPairsCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, Bool.not_eq_true'] at ok
  exact ok
def autosCheck (T : Nat) (autos : List (List (Nat × Nat))) : Bool :=
  autos.all fun sw => swapsValid sw && (permWord sw T == T)
lemma autos_of {T autos} (ok : autosCheck T autos = true) :
    ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T := by
  simp only [autosCheck, List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at ok
  exact ok
def baseCheck (pos neg : List Nat) (base : List Decor) : Bool :=
  base.all fun x => (x.2.1 == projBits pos x.1) && (x.2.2 == projBits neg x.1) && decide (x.1 < 2^128)
lemma base_of {pos neg base} (ok : baseCheck pos neg base = true) :
    ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^128 := by
  simp only [baseCheck, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ok
  intro x hx
  have h := ok x hx
  exact ⟨⟨h.1.1, h.1.2⟩, h.2⟩
def forestRootCheck (roots : List Nat) (T : Nat) (essPairs : List (Nat × Nat × Nat)) : Bool :=
  checkProper T && checkRoots roots &&
    roots.all fun a => essPairs.any fun e => (e.1 == a) && checkEss1 T roots e.1 e.2.1 e.2.2
lemma faithful_zero (pos neg : List Nat) : faithful pos neg (0, 0, 0) := by
  constructor
  · apply Nat.eq_of_testBit_eq; intro i; rw [testBit_projBits]; cases pos[i]? <;> simp
  · apply Nat.eq_of_testBit_eq; intro i; rw [testBit_projBits]; cases neg[i]? <;> simp
lemma forall_cons {α : Type} {P : α → Prop} {a : α} {l : List α} (ha : P a) (hl : ∀ x ∈ l, P x) :
    ∀ x ∈ a :: l, P x := by
  intro x hx; rcases List.mem_cons.mp hx with rfl | hx; exact ha; exact hl x hx
abbrev PoolSpec := Nat × List (Nat × Nat × Nat)
abbrev NodeSpec := List Nat × List Nat × List Nat

def nodesWithIdentity (entries : List (List Nat × List Nat)) : List NodeSpec :=
  entries.map (fun entry => (entry.1, entry.2, [0]))

lemma var_testBit (i : Fin 7) (r : Row) : (VAR i.val).testBit r.val = r.val.testBit i.val := by
  revert i r; decide +kernel
def sliceDirectCheck (z o zDead : Nat) (raw : List Nat) (T : Nat) (qRoots : List Nat) (qGoal : Nat) : Bool :=
  decide (z < 128) && decide (o < 128) && ((z &&& o) == 0) &&
    decide (zDead < 128) && (((z ||| zDead) &&& o) == 0) &&
    checkProper qGoal && checkRoots qRoots &&
    (fixWord (z ||| zDead) o T == qGoal) &&
    raw.all (fun a => freeIn qRoots (fixWord (z ||| zDead) o a))
lemma subcube_fixRow_sup (z o zDead : Nat) (hz : z < 128) (hd : zDead < 128) (ho : o < 128)
    (hzo : ((z ||| zDead) &&& o) = 0) (r : Row) :
    (subcube z o).testBit (fixRow (z ||| zDead) o r).val = true := by
  have hsub := subcube_fixRow (z ||| zDead) o (Nat.or_lt_two_pow (n := 7) hz hd) ho hzo r
  unfold subcube at hsub ⊢
  rw [testBit_foldr_bits] at hsub ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hsub ⊢
  refine ⟨hsub.1, ?_, hsub.2.2⟩
  apply Nat.eq_of_testBit_eq; intro i
  have h1 := congrArg (fun x => x.testBit i) hsub.2.1
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit] at h1 ⊢
  cases hfa : (fixRow (z ||| zDead) o r).val.testBit i <;> cases hzb : z.testBit i <;> simp_all
lemma slice_direct {z o zDead raw T qRoots qGoal qL}
    (ok : sliceDirectCheck z o zDead raw T qRoots qGoal = true)
    (hPrior : Lower qRoots qGoal qL) :
    Slice raw T (subcube z o) qL := by
  simp only [sliceDirectCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hz, ho⟩, _hzo0⟩, hd⟩, hzo⟩, hGp⟩, hQR⟩, heq⟩, hcov⟩ := ok
  have ⟨g0, glt, gb0⟩ := checkProper_sound hGp
  refine ⟨fixRow (z ||| zDead) o, qRoots, subcube_fixRow_sup z o zDead hz hd ho hzo,
    fun a ha => freeIn_sound ((fixWord_eq_renameW (z ||| zDead) o a).symm ▸ hcov a ha),
    by rw [← obs_renameW, ← fixWord_eq_renameW, heq]; exact obs_not_const g0 glt gb0, ?_⟩
  rw [← obs_renameW, ← fixWord_eq_renameW, heq]
  exact hPrior
def evalInput6 (r : Row) : Fin 6 → Bool := fun i => r.val.testBit i.val
def packInput6 (x : Fin 6 → Bool) : Row :=
  ⟨(x 0).toNat + 2 * (x 1).toNat + 4 * (x 2).toNat + 8 * (x 3).toNat +
    16 * (x 4).toNat + 32 * (x 5).toNat, by
    have h0 := Bool.toNat_le (x 0); have h1 := Bool.toNat_le (x 1); have h2 := Bool.toNat_le (x 2)
    have h3 := Bool.toNat_le (x 3); have h4 := Bool.toNat_le (x 4); have h5 := Bool.toNat_le (x 5)
    omega⟩
lemma evalInput6_packInput6 (x : Fin 6 → Bool) : evalInput6 (packInput6 x) = x := by
  funext i
  have h : ∀ (b0 b1 b2 b3 b4 b5 : Bool) (j : Fin 6),
      ((b0.toNat + 2 * b1.toNat + 4 * b2.toNat + 8 * b3.toNat +
        16 * b4.toNat + 32 * b5.toNat).testBit j.val) =
        ([b0, b1, b2, b3, b4, b5].getD j.val false) := by decide +kernel
  have hi := h (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) i
  fin_cases i <;> simpa [evalInput6, packInput6] using hi
lemma sum_eq_packInput6 (x : Fin 6 → Bool) :
    (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) = (packInput6 x).val := by
  simp only [Fin.sum_univ_six, Fin.val_zero, Fin.val_one, Fin.val_two, packInput6]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> cases x 4 <;> cases x 5 <;> decide
lemma testBit_rep64 (T6 : Nat) (hT6 : T6 < 2^64) (r : Row) :
    (T6 ||| (T6 <<< 64)).testBit r.val = T6.testBit (r.val % 64) := by
  have hr := r.isLt
  rw [Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases h64 : r.val < 64
  · have hn : ¬(64 ≤ r.val) := by omega
    rw [Nat.mod_eq_of_lt h64]
    simp [hn]
  · have hge : 64 ≤ r.val := by omega
    have hmod : r.val % 64 = r.val - 64 := by omega
    rw [hmod]
    have hhi : T6.testBit r.val = false → (T6.testBit r.val || (decide (64 ≤ r.val) && T6.testBit (r.val - 64))) = T6.testBit (r.val - 64) := by
      intro hf; simp [hf, hge]
    have hf : T6.testBit r.val = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hT6 (Nat.pow_le_pow_right (by decide : 0 < 2) hge))
    exact hhi hf
lemma sw_extract_full_6 (T : Nat) (hT0 : T ≠ 0) (hTlt : T < 2^128) (hTb0 : T.testBit 0 = false)
    (gs : List Gate) (o : Nat)
    (legal : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (he : ∀ r : Row, Circuit.eval ⟨gs, o⟩ (List.ofFn (evalInput6 r)) = T.testBit r.val) :
    ∃ k S, k ≤ gs.countP isBin ∧ Live T k S ∧ ∀ a ∈ S, a ∈ varsOf 63 := by
  let seeds : List SWire := (varsOf 63).map (fun v => (false, v))
  have hseeds_lt : ∀ u ∈ seeds, u.2 < 2^128 ∧ u.2.testBit 0 = false := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
    have hall : (varsOf 63).all (fun a => decide (a < 2^128) && !a.testBit 0) = true := by decide +kernel
    have h1 := List.all_eq_true.mp hall v hv
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h1
    exact h1
  let final := swExec gs seeds
  let out := final.getD o swZero
  have hfinal_lt : out.2 < 2^128 ∧ out.2.testBit 0 = false := by
    simp only [out, List.getD_eq_getElem?_getD]
    cases eq : final[o]? with
    | none => exact ⟨by decide, by decide⟩
    | some a => exact swExec_lt gs seeds hseeds_lt a (List.mem_of_getElem? eq)
  have hread_seeds (r : Row) : seeds.map (swRead r.val) = List.ofFn (evalInput6 r) := by
    apply List.ext_getElem
    · simp only [seeds, List.length_map, List.length_ofFn]; decide
    · intro i hi1 hi2
      have hi6 : i < 6 := by simpa using hi2
      have hv : (varsOf 63)[i]? = some (VAR i) := by interval_cases i <;> decide
      simp only [List.getElem_map, List.getElem_ofFn, seeds, evalInput6, swRead, Bool.false_bne]
      have hget : (varsOf 63)[i]'(by simpa [seeds] using hi1) = VAR i := (List.getElem?_eq_some_iff.mp hv).2
      rw [hget]
      exact var_testBit ⟨i, by omega⟩ r
  have hev (r : Row) : swRead r.val out = T.testBit r.val := by
    have h1 := (swRead_get r.val final o).symm
    rw [show final = swExec gs seeds from rfl, swExec_read r.val gs seeds legal, hread_seeds r] at h1
    exact h1.trans (he r)
  have hout0 : out.1 = false := by
    have h0 := hev 0
    simp only [swRead, Fin.val_zero, hfinal_lt.2, hTb0, Bool.bne_false] at h0
    exact h0
  have hout2 : out.2 = T := by
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hr : r < 128
    · have h := hev ⟨r, hr⟩; simpa [swRead, hout0] using h
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hfinal_lt.1 (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hTlt (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)))]
  have hfound : T ∈ reps final := by
    rw [← hout2]; exact (get_simple final o).resolve_left (hout2.symm ▸ hT0)
  obtain ⟨k, S, hk, hlive, hsub⟩ := extract_live hT0 gs seeds hfound
  refine ⟨k, S, hk, hlive, ?_⟩
  simpa [reps, seeds, List.map_map, Function.comp_def] using hsub
lemma table2_of_lower (T6 : Nat) (hT6lt : T6 < 2^64)
    (hT0 : (T6 ||| (T6 <<< 64)) ≠ 0) (hTlt : (T6 ||| (T6 <<< 64)) < 2^128) (hTb0 : (T6 ||| (T6 <<< 64)).testBit 0 = false)
    (L : Nat) (hLow : Lower (varsOf 63) (T6 ||| (T6 <<< 64)) L)
    (wit : List Gate) (wo : Nat) (hwLen : wit.length ≤ L + 1)
    (hwMono : PEqualNP.MetaComplexity.Monotone2 ⟨wit, wo⟩)
    (hwEvalR : ∀ r : Row, Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput6 r)) = (T6 ||| (T6 <<< 64)).testBit r.val)
    (s : ℕ)
    (hcs : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit T6 (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s) :
    ∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧
      ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit T6 (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  let T := T6 ||| (T6 <<< 64)
  obtain ⟨C, hfan, hsize, heval⟩ := hcs
  have hlegal : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    have ⟨hm, hl⟩ := hfan g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    exact ⟨hm, hl⟩
  by_cases hn : ∃ g ∈ C.gates, g.op = .not
  · have hlt : C.gates.countP isBin < C.gates.length := by
      apply Nat.lt_of_le_of_ne List.countP_le_length
      intro eq
      obtain ⟨g, hg, hop⟩ := hn
      have bad := List.countP_eq_length.mp eq g hg
      simp [isBin, hop] at bad
    have heR : ∀ r : Row, Circuit.eval ⟨C.gates, C.output⟩ (List.ofFn (evalInput6 r)) = T.testBit r.val := by
      intro r
      have h1 := heval (evalInput6 r)
      have hsum : (∑ i : Fin 6, if evalInput6 r i then 2 ^ (i : ℕ) else 0) = r.val % 64 := by
        rw [sum_eq_packInput6]
        have h : ∀ j : Row, (packInput6 (evalInput6 j)).val = j.val % 64 := by decide +kernel
        exact h r
      dsimp only at h1
      rw [hsum] at h1
      exact h1.trans (testBit_rep64 T6 hT6lt r).symm
    obtain ⟨k, S, hk, hlive, hsub⟩ := sw_extract_full_6 T hT0 hTlt hTb0 C.gates C.output hlegal heR
    have hrun := live_to_run hlive S.toList (Finset.nodup_toList S) (by simp)
    have hsup : Supply ((varsOf 63).map obs) (S.toList.map obs) := fun v hv => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
      exact Or.inl (List.mem_map_of_mem (hsub a (Finset.mem_toList.mp ha)))
    obtain ⟨q, next, hq, hav, hbound⟩ :=
      contraction (obs_not_const hT0 hTlt hTb0) hrun ((varsOf 63).map obs)
        (show Reach ((varsOf 63).map obs) 0 ((varsOf 63).map obs) from rfl) hsup
    have hlo := hLow q next hq hav
    have hwEval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wit, wo⟩ (List.ofFn x) = Nat.testBit T6 (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
      intro x
      rw [← evalInput6_packInput6 x, hwEvalR (packInput6 x), testBit_rep64 T6 hT6lt (packInput6 x)]
      rw [evalInput6_packInput6 x, sum_eq_packInput6 x]
      have hlt64 : (packInput6 x).val < 64 := by
        have h0 := Bool.toNat_le (x 0); have h1 := Bool.toNat_le (x 1); have h2 := Bool.toNat_le (x 2)
        have h3 := Bool.toNat_le (x 3); have h4 := Bool.toNat_le (x 4); have h5 := Bool.toNat_le (x 5)
        simp only [packInput6]; omega
      rw [Nat.mod_eq_of_lt hlt64]
    have hcsz : C.size = C.gates.length := rfl
    refine ⟨⟨wit, wo⟩, hwMono, ?_, hwEval⟩
    change wit.length ≤ s
    omega
  · refine ⟨C, ?_, hsize, heval⟩
    intro g hg
    have ⟨hm, hl⟩ := hlegal g hg
    refine ⟨?_, hl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases hm with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hn ⟨g, hg, h⟩).elim
inductive BT (α : Type) where
  | empty : BT α
  | leaf : α → BT α
  | node : BT α → BT α → BT α
def btGet {α : Type} (d : α) : BT α → Nat → α
  | .empty, _ => d
  | .leaf x, _ => x
  | .node l r, i => if i &&& 1 == 0 then btGet d l (i >>> 1) else btGet d r (i >>> 1)
def btSet {α : Type} : Nat → BT α → Nat → α → BT α
  | 0, _, _, v => .leaf v
  | d + 1, .empty, i, v =>
    if i &&& 1 == 0 then .node (btSet d .empty (i >>> 1) v) .empty
    else .node .empty (btSet d .empty (i >>> 1) v)
  | d + 1, .leaf x, i, v =>
    if i &&& 1 == 0 then .node (btSet d (.leaf x) (i >>> 1) v) .empty
    else .node .empty (btSet d (.leaf x) (i >>> 1) v)
  | d + 1, .node l r, i, v =>
    if i &&& 1 == 0 then .node (btSet d l (i >>> 1) v) r
    else .node l (btSet d r (i >>> 1) v)
def btUpdate {α : Type} (d0 : α) : Nat → BT α → Nat → (α → α) → BT α
  | 0, .leaf x, _, f => .leaf (f x)
  | 0, _, _, f => .leaf (f d0)
  | d + 1, .empty, i, f =>
    if i &&& 1 == 0 then .node (btUpdate d0 d .empty (i >>> 1) f) .empty
    else .node .empty (btUpdate d0 d .empty (i >>> 1) f)
  | d + 1, .leaf x, i, f =>
    if i &&& 1 == 0 then .node (btUpdate d0 d (.leaf x) (i >>> 1) f) .empty
    else .node .empty (btUpdate d0 d (.leaf x) (i >>> 1) f)
  | d + 1, .node l r, i, f =>
    if i &&& 1 == 0 then .node (btUpdate d0 d l (i >>> 1) f) r
    else .node l (btUpdate d0 d r (i >>> 1) f)
def btAll {α : Type} (P : α → Prop) : BT α → Prop
  | .empty => True
  | .leaf x => P x
  | .node l r => btAll P l ∧ btAll P r
lemma btAll_get {α : Type} {P : α → Prop} {d : α} {t : BT α} (ht : btAll P t) (hd : P d) (i : Nat) :
    P (btGet d t i) := by
  induction t generalizing i with
  | empty => exact hd
  | leaf x => exact ht
  | node l r ihl ihr =>
    unfold btGet
    split
    · exact ihl ht.1 _
    · exact ihr ht.2 _
lemma btAll_set {α : Type} {P : α → Prop} {depth : Nat} {t : BT α} {i : Nat} {v : α}
    (ht : btAll P t) (hv : P v) : btAll P (btSet depth t i v) := by
  induction depth generalizing t i with
  | zero => exact hv
  | succ d ih =>
    cases t with
    | empty =>
      unfold btSet; split
      · exact ⟨ih trivial, trivial⟩
      · exact ⟨trivial, ih trivial⟩
    | leaf x =>
      unfold btSet; split
      · exact ⟨ih ht, trivial⟩
      · exact ⟨trivial, ih ht⟩
    | node l r =>
      unfold btSet; split
      · exact ⟨ih ht.1, ht.2⟩
      · exact ⟨ht.1, ih ht.2⟩
lemma btAll_update {α : Type} {P : α → Prop} {d0 : α} {depth : Nat} {t : BT α} {i : Nat} {f : α → α}
    (ht : btAll P t) (hd0 : P d0) (hf : ∀ x, P x → P (f x)) : btAll P (btUpdate d0 depth t i f) := by
  induction depth generalizing t i with
  | zero =>
    cases t with
    | leaf x => exact hf x ht
    | empty => exact hf d0 hd0
    | node _ _ => exact hf d0 hd0
  | succ d ih =>
    cases t with
    | empty =>
      unfold btUpdate; split
      · exact ⟨ih trivial, trivial⟩
      · exact ⟨trivial, ih trivial⟩
    | leaf x =>
      unfold btUpdate; split
      · exact ⟨ih ht, trivial⟩
      · exact ⟨trivial, ih ht⟩
    | node l r =>
      unfold btUpdate; split
      · exact ⟨ih ht.1, ht.2⟩
      · exact ⟨ht.1, ih ht.2⟩
def btOfList {α : Type} (depth : Nat) (l : List α) : BT α :=
  (l.foldl (fun p x => (p.1 + 1, btSet depth p.2 p.1 x)) (0, BT.empty)).2
lemma btAll_ofList {α : Type} {P : α → Prop} {depth : Nat} {l : List α}
    (h : ∀ x ∈ l, P x) : btAll P (btOfList depth l) := by
  unfold btOfList
  have hgo : ∀ (xs : List α) (acc : Nat × BT α),
      (∀ x ∈ xs, P x) → btAll P acc.2 →
      btAll P (xs.foldl (fun p x => (p.1 + 1, btSet depth p.2 p.1 x)) acc).2 := by
    intro xs
    induction xs with
    | nil => intro acc _ hacc; exact hacc
    | cons x xs ih =>
      intro acc hx hacc
      exact ih (acc.1 + 1, btSet depth acc.2 acc.1 x)
        (fun y hy => hx y (List.mem_cons_of_mem _ hy))
        (btAll_set hacc (hx x (List.mem_cons_self ..)))
  exact hgo l (0, BT.empty) h trivial
def fastBitMask (z o i : Nat) : Nat :=
  if z.testBit i then ALL128 ^^^ VAR i else if o.testBit i then VAR i else ALL128
def subcubeFast (z o : Nat) : Nat :=
  fastBitMask z o 0 &&& fastBitMask z o 1 &&& fastBitMask z o 2 &&&
  fastBitMask z o 3 &&& fastBitMask z o 4 &&& fastBitMask z o 5 &&& fastBitMask z o 6
lemma fastBitMask_testBit (z o i : Nat) (hi : i < 7) (r : Row) :
    (fastBitMask z o i).testBit r.val =
      (if z.testBit i then !(r.val.testBit i) else if o.testBit i then r.val.testBit i else true) := by
  have hall : ALL128.testBit r.val = true := by
    simp only [ALL128]; have hr := r.isLt; simpa [hr] using Nat.testBit_two_pow_sub_one 128 r.val
  have hvar : (VAR i).testBit r.val = r.val.testBit i := var_testBit ⟨i, hi⟩ r
  unfold fastBitMask
  split
  · simp [Nat.testBit_xor, hall, hvar]
  · split
    · exact hvar
    · exact hall
lemma subcubeFast_eq_subcube (z o : Nat) (hz : z < 128) (ho : o < 128) (hzo : (z &&& o) = 0) :
    subcubeFast z o = subcube z o := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 128
  · have hsub : (subcube z o).testBit r = ((r &&& z == 0) && (r &&& o == o)) := by
      unfold subcube; rw [testBit_foldr_bits]; simp [hr]
    rw [hsub]
    unfold subcubeFast
    simp only [Nat.testBit_and,
      fastBitMask_testBit z o 0 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 1 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 2 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 3 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 4 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 5 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 6 (by decide) ⟨r, hr⟩]
    have hbit (i : Nat) (hi : i < 7) :
        ((r &&& z).testBit i = false ∧ (r &&& o).testBit i = o.testBit i) ↔
          (if z.testBit i then !r.testBit i else if o.testBit i then r.testBit i else true) = true := by
      have hzi : (z.testBit i && o.testBit i) = false := by
        have := congrArg (fun x => x.testBit i) hzo; simpa [Nat.testBit_and] using this
      simp only [Nat.testBit_and]
      cases hz' : z.testBit i <;> cases ho' : o.testBit i <;> cases hr' : r.testBit i <;> simp_all
    have heq_iff : (((r &&& z == 0) && (r &&& o == o)) = true) ↔
        ∀ i < 7, (r &&& z).testBit i = false ∧ (r &&& o).testBit i = o.testBit i := by
      simp only [Bool.and_eq_true, beq_iff_eq]
      constructor
      · rintro ⟨h1, h2⟩ i _; rw [h1, h2, Nat.zero_testBit]; exact ⟨rfl, rfl⟩
      · intro h
        constructor
        · apply Nat.eq_of_testBit_eq; intro i
          rw [Nat.zero_testBit]
          by_cases hi : i < 7
          · exact (h i hi).1
          · have hzf : z.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hz (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 7 ≤ i)))
            simp [Nat.testBit_and, hzf]
        · apply Nat.eq_of_testBit_eq; intro i
          by_cases hi : i < 7
          · exact (h i hi).2
          · have hof : o.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ho (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 7 ≤ i)))
            simp [Nat.testBit_and, hof]
    apply Bool.eq_iff_iff.mpr
    rw [heq_iff]
    simp only [Bool.and_eq_true]
    constructor
    · intro h i hi
      have := hbit i hi
      interval_cases i <;> tauto
    · intro h
      refine ⟨⟨⟨⟨⟨⟨(hbit 0 (by decide)).mp (h 0 (by decide)), (hbit 1 (by decide)).mp (h 1 (by decide))⟩,
        (hbit 2 (by decide)).mp (h 2 (by decide))⟩, (hbit 3 (by decide)).mp (h 3 (by decide))⟩,
        (hbit 4 (by decide)).mp (h 4 (by decide))⟩, (hbit 5 (by decide)).mp (h 5 (by decide))⟩,
        (hbit 6 (by decide)).mp (h 6 (by decide))⟩
  · have hlt_f (i : Nat) : (fastBitMask z o i).testBit r = false := by
      have hle : 128 ≤ r := by omega
      have ha : ALL128 < 2^128 := by decide
      have hv : VAR i < 2^128 := by
        unfold VAR; rcases i with _ | _ | _ | _ | _ | _ | _ | _
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · change (0 : Nat) < 2^128; decide
      have hlt_m : fastBitMask z o i < 2^128 := by
        unfold fastBitMask; split
        · exact Nat.xor_lt_two_pow ha hv
        · split; exact hv; exact ha
      exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hlt_m (Nat.pow_le_pow_right (by decide : 0 < 2) hle))
    have hsub : (subcube z o).testBit r = false := by
      unfold subcube; rw [testBit_foldr_bits]; simp [hr]
    rw [hsub]
    unfold subcubeFast
    simp only [Nat.testBit_and, hlt_f]
    rfl
lemma slice_fast_direct {z o zDead raw T qRoots qGoal qL}
    (ok : sliceDirectCheck z o zDead raw T qRoots qGoal = true)
    (hPrior : Lower qRoots qGoal qL) :
    Slice raw T (subcubeFast z o) qL := by
  have ok2 := ok
  simp only [sliceDirectCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at ok2
  rw [subcubeFast_eq_subcube z o ok2.1.1.1.1.1.1.1.1 ok2.1.1.1.1.1.1.1.2 ok2.1.1.1.1.1.1.2]
  exact slice_direct ok hPrior
def hashWs64 (ws : List Nat) : Nat :=
  (ws.foldl (fun h w => h + (w % 1000003) * 31) 0) &&& 63
def bucketContainsBT (bks : BT (List (List Nat))) (ws : List Nat) : Bool :=
  let s := sortNats ws
  (btGet [] bks (hashWs64 s)).contains s
def closeChildBT (pools : List BoundPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (k : Nat) (rest : List Nat) (op : Choice) : Bool :=
  let ws := choiceVal op :: rest
  pools.any (fun c => scalarPoolCut c k rest op) ||
    autos.any (fun sw => bucketContainsBT prevBks (ws.map (permWord sw)))
lemma closeChildBT_sound {raw T pools autos prevBks k rest op}
    (hT : T < 2^128)
    (hPools : ∀ c ∈ pools, ValidPool raw T c)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : btAll (fun b => ∀ xs ∈ b, Impossible T k xs.toFinset) prevBks)
    (nd : (choiceVal op :: rest).Nodup)
    (hlt : ∀ x ∈ choiceVal op :: rest, x < 2^128)
    (h : closeChildBT pools autos prevBks k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  simp only [closeChildBT, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with ⟨c, hc, hcut⟩ | ⟨sw, hsw, hhit⟩
  · exact scalarPoolCut_sound (hPools c hc) nd hcut
  · unfold bucketContainsBT at hhit
    have hmem := List.contains_iff_mem.mp hhit
    have hb : ∀ xs ∈ btGet [] prevBks (hashWs64 (sortNats ((choiceVal op :: rest).map (permWord sw)))),
        Impossible T k xs.toFinset :=
      btAll_get hPrev (fun _ hx => (List.not_mem_nil hx).elim) _
    have himp := hb _ hmem
    rw [sortNats_toFinset] at himp
    have ⟨hsv, hfix⟩ := hAutos sw hsw
    have hvr : swapsValid sw.reverse = true := by simp only [swapsValid, List.all_reverse]; exact hsv
    have hinv_row_gen : ∀ (l : List (Nat × Nat)), swapsValid l = true →
        ∀ r : Row, permRow l.reverse (permRow l r) = r := by
      intro l hl
      induction l with
      | nil => intro r; rfl
      | cons p ps ih =>
        simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hl
        intro r
        have h1 : permRow (p :: ps).reverse (permRow (p :: ps) r) =
            swapRow p.1 p.2 (permRow ps.reverse (permRow ps (swapRow p.1 p.2 r))) := by
          simp [permRow, List.reverse_cons, List.foldl_append]
        rw [h1, ih hl.2, swapRow_invol p.1 p.2 (by omega) hl.1.2]
    have hinv_row2 : ∀ r : Row, permRow sw (permRow sw.reverse r) = r := by
      simpa using hinv_row_gen sw.reverse hvr
    have hinv_w : ∀ x : Nat, x < 2^128 → permWord sw.reverse (permWord sw x) = x := by
      intro x hx
      have h1 := permWord_eq_renameW sw hsv x hx
      have h2 := permWord_eq_renameW sw.reverse hvr (permWord sw x) (h1 ▸ renameW_lt _ x)
      rw [h2, h1]
      apply Nat.eq_of_testBit_eq; intro r
      by_cases hrr : r < 128
      · rw [testBit_renameW _ _ ⟨r, hrr⟩, testBit_renameW, hinv_row2]
      · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))),
            Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)))]
    have hfixr : permWord sw.reverse T = T := by
      have := hinv_w T hT; rwa [hfix] at this
    have hmap_lt : ∀ a ∈ (choiceVal op :: rest).map (permWord sw), a < 2^128 := by
      intro a ha
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      rw [permWord_eq_renameW sw hsv x (hlt x hx)]
      exact renameW_lt _ x
    have hrot := rotate_impossible himp sw.reverse hvr hT hfixr hmap_lt
    have hback : (((choiceVal op :: rest).map (permWord sw)).map (permWord sw.reverse)) = (choiceVal op :: rest) := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id (choiceVal op :: rest)]
      exact List.map_congr_left fun x hx => hinv_w x (hlt x hx)
    rwa [hback] at hrot
abbrev FastPool := BoundPool × List Nat × Nat
def prepPool (vals : List Nat) (c : BoundPool) : Option FastPool :=
  let miss := vals.filter (fun w => !availM c.dom c.pm w)
  if miss.length > 2 then none
  else some (c, miss, vals.countP (isConstM c.dom))
def fastPoolCut (fp : FastPool) (k : Nat) (a b d : Nat) (ka kb : Bool) : Bool :=
  let c := fp.1
  let miss := fp.2.1
  let totC := fp.2.2
  if !miss.all (fun m => (!ka && m == a) || (!kb && m == b)) then false
  else
    let dropA := if !ka && isConstM c.dom a then 1 else 0
    let dropB := if !kb && isConstM c.dom b then 1 else 0
    let z := bin d a b
    let cRest := totC - dropA - dropB + (if isConstM c.dom z then 1 else 0)
    let zIn := availM c.dom c.pm z
    let extra := if zIn then 0 else 1
    decide (k + c.paid + extra < c.lb + cRest) && (zIn || choiceOK c.dom c.pm (d, a, b))
lemma countP_erase {α : Type} [BEq α] [LawfulBEq α] (p : α → Bool) {l : List α} {x : α} (hx : x ∈ l) :
    (l.erase x).countP p + (if p x then 1 else 0) = l.countP p := by
  have hp := List.perm_cons_erase hx
  have h1 := List.Perm.countP_eq p hp
  simp only [List.countP_cons] at h1
  omega
lemma countP_delTwo_fst (p : Nat → Bool) {ws : List Decor} {a b : Decor}
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws) (hab : a.1 ≠ b.1) (ka kb : Bool) :
    ((delTwo ws a b ka kb).map Prod.fst).countP p =
      (ws.map Prod.fst).countP p - (if !ka && p a.1 then 1 else 0) - (if !kb && p b.1 then 1 else 0) := by
  have hne : a ≠ b := fun e => hab (congrArg Prod.fst e)
  have hmap_erase : ∀ (l : List Decor) (x : Decor), (l.map Prod.fst).Nodup → x ∈ l →
      (l.erase x).map Prod.fst = (l.map Prod.fst).erase x.1 := by
    intro l x hnd hx
    induction l with
    | nil => simp at hx
    | cons y ys ih =>
      simp only [List.map_cons, List.nodup_cons] at hnd
      by_cases hyx : y = x
      · subst hyx; simp
      · have hne1 : y.1 ≠ x.1 := by
          intro eq; apply hnd.1; rw [eq]
          exact List.mem_map_of_mem ((List.mem_cons.mp hx).resolve_left (Ne.symm hyx))
        have h1 : (y == x) = false := beq_false_of_ne hyx
        have h2 : (y.1 == x.1) = false := beq_false_of_ne hne1
        simp only [List.erase_cons, h1, h2, List.map_cons]
        exact congrArg (y.1 :: ·) (ih hnd.2 ((List.mem_cons.mp hx).resolve_left (Ne.symm hyx)))
  cases ka <;> cases kb
  · have hbm : b ∈ ws.erase a := (List.mem_erase_of_ne hne.symm).mpr hb
    have hnd1 : ((ws.erase a).map Prod.fst).Nodup := ((List.erase_sublist).map Prod.fst).nodup nd
    change (((ws.erase a).erase b).map Prod.fst).countP p = _
    rw [hmap_erase _ b hnd1 hbm, hmap_erase ws a nd ha]
    have ha1 : a.1 ∈ ws.map Prod.fst := List.mem_map_of_mem ha
    have hb1 : b.1 ∈ (ws.map Prod.fst).erase a.1 := (List.mem_erase_of_ne hab.symm).mpr (List.mem_map_of_mem hb)
    have c1 := countP_erase p ha1
    have c2 := countP_erase p hb1
    cases hpa : p a.1 <;> cases hpb : p b.1 <;> simp [hpa, hpb] at c1 c2 ⊢ <;> omega
  · change ((ws.erase a).map Prod.fst).countP p = _
    rw [hmap_erase ws a nd ha]
    have c1 := countP_erase p (List.mem_map_of_mem (f := Prod.fst) ha)
    cases hpa : p a.1 <;> simp [hpa] at c1 ⊢ <;> omega
  · change ((ws.erase b).map Prod.fst).countP p = _
    rw [hmap_erase ws b nd hb]
    have c1 := countP_erase p (List.mem_map_of_mem (f := Prod.fst) hb)
    cases hpb : p b.1 <;> simp [hpb] at c1 ⊢ <;> omega
  · simp [delTwo, delOne]
lemma fastPoolCut_sound {raw T ws a b d ka kb k c fp}
    (hP : ValidPool raw T c) (hprep : prepPool (ws.map Prod.fst) c = some fp)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws) (hab : a.1 ≠ b.1)
    (ndc : (bin d a.1 b.1 :: (delTwo ws a b ka kb).map Prod.fst).Nodup)
    (hcut : fastPoolCut fp k a.1 b.1 d ka kb = true) :
    Impossible T k (bin d a.1 b.1 :: (delTwo ws a b ka kb).map Prod.fst).toFinset := by
  unfold prepPool at hprep
  dsimp only at hprep
  split at hprep
  · simp at hprep
  · simp only [Option.some.injEq] at hprep
    subst hprep
    unfold fastPoolCut at hcut
    dsimp only at hcut
    split at hcut
    · simp at hcut
    · next hmiss =>
      simp only [Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true, List.mem_filter, Bool.not_eq_true'] at hmiss
      have hsub := (delTwo_sub ws a b ka kb).map Prod.fst
      have h_all_avail : ((delTwo ws a b ka kb).map Prod.fst).all (availM c.dom c.pm) = true := by
        rw [List.all_eq_true]; intro w hw
        by_contra hna
        have hnf : availM c.dom c.pm w = false := Bool.eq_false_iff.mpr hna
        have hmem_ws : w ∈ ws.map Prod.fst := hsub.subset hw
        have hm := hmiss w ⟨hmem_ws, hnf⟩
        simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hm
        have hne_ab : a ≠ b := fun e => hab (congrArg Prod.fst e)
        have hnot_in : ∀ (x : Decor) (kx : Bool), kx = false → x ∈ ws → x.1 ∉ (delTwo ws a b ka kb).map Prod.fst → True := fun _ _ _ _ _ => trivial
        have hmem_del : ∀ u ∈ delTwo ws a b ka kb, u.1 = w → (ka = false → u ≠ a) ∧ (kb = false → u ≠ b) := by
          intro u hu _
          constructor
          · intro hka; subst hka
            have hsub1 : (delTwo ws a b false kb).Sublist (ws.erase a) := by
              cases kb <;> simp [delTwo, delOne, List.erase_sublist]
            have hu1 := hsub1.subset hu
            intro heq; subst heq
            have hnd_ws : ws.Nodup := List.Nodup.of_map Prod.fst nd
            exact List.Nodup.not_mem_erase hnd_ws hu1
          · intro hkb; subst hkb
            have hnd_ws : ws.Nodup := List.Nodup.of_map Prod.fst nd
            have hnd2 : (delOne ws a ka).Nodup := by cases ka; exact hnd_ws.erase a; exact hnd_ws
            have h2 := List.Nodup.not_mem_erase hnd2 (a := b)
            exact fun heq => h2 (heq ▸ hu)
        obtain ⟨u, hu, huw⟩ := List.mem_map.mp hw
        have ⟨hna', hnb'⟩ := hmem_del u hu huw
        rcases hm with ⟨hka, hwa⟩ | ⟨hkb, hwb⟩
        · have hu_eq : u = a := unique_fst nd ((delTwo_sub ws a b ka kb).subset hu) ha (huw.trans hwa)
          exact hna' hka hu_eq
        · have hu_eq : u = b := unique_fst nd ((delTwo_sub ws a b ka kb).subset hu) hb (huw.trans hwb)
          exact hnb' hkb hu_eq
      have hcnt := countP_delTwo_fst (isConstM c.dom) nd ha hb hab ka kb
      apply scalarPoolCut_sound (op := (d, a.1, b.1)) (rest := (delTwo ws a b ka kb).map Prod.fst) hP ndc
      unfold scalarPoolCut
      simp only [choiceVal, h_all_avail, Bool.true_and, Bool.and_true, List.countP_cons,
        Bool.and_eq_true, decide_eq_true_eq] at hcut ⊢
      rw [hcnt]
      rcases hcut with ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · cases hz : availM c.dom c.pm (bin d a.1 b.1) <;>
          cases hcz : isConstM c.dom (bin d a.1 b.1) <;>
          simp only [hz, hcz, Bool.not_true, Bool.not_false, Bool.toNat_true, Bool.toNat_false,
            Bool.and_eq_true, Bool.false_eq_true, ite_true, ite_false] at h1 ⊢ <;> omega
      · cases hz : availM c.dom c.pm (bin d a.1 b.1) <;>
          simp only [hz, Bool.not_true, Bool.not_false, Bool.true_or, Bool.false_or] at h2 ⊢ <;>
          exact h2
def evalMoveBT (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (fpools : List FastPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat)))
    (d : Nat) (a b z : Decor) (ka kb : Bool) : Bool :=
  let len := 1 + (n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len > cap then true else
    let rs := restCov cov (dsep a) (dsep b) ka kb
    if ((rs ||| dsep z) &&& fmask) != fmask then true else
    if z.1 == 0 || ws.any (fun v => v.1 == z.1) then true else
    if fpools.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 d ka kb) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChildBT [] autos prevBks (cap - 1) rest (d, a.1, b.1)
def testPairBT (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (fpools : List FastPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (a b : Decor) (d : Nat) : Bool :=
  let z := dbin d a b
  let go := evalMoveBT cap n fmask ws cov fpools autos prevBks d a b z
  go false false && go true false && go false true && go true true
def testAllBT (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (fpools : List FastPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) : List Decor → Bool
  | [] => true
  | a :: bs =>
    bs.all (fun b => [0, 1, 2, 3].all (testPairBT cap n fmask ws cov fpools autos prevBks a b)) &&
      testAllBT cap n fmask ws cov fpools autos prevBks bs
lemma evalMoveBT_sound {raw T pos neg ws fpools autos prevBks cap a b d ka kb}
    (hT : T < 2^128) (gp : goodPairs T pos neg) (hf : ∀ w ∈ ws, faithful pos neg w)
    (nd : (ws.map Prod.fst).Nodup) (hlt : ∀ w ∈ ws, w.1 < 2^128)
    (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) (hcap : 0 < cap) (_hd : d < 4)
    (hPools : ∀ fp ∈ fpools, ValidPool raw T fp.1 ∧ prepPool (ws.map Prod.fst) fp.1 = some fp)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (cap - 1) xs.toFinset) prevBks)
    (hnz : bin d a.1 b.1 ≠ 0) (hfr : bin d a.1 b.1 ∉ ws.map Prod.fst)
    (test : evalMoveBT cap ws.length (fullMask pos.length) ws (coverage ws) fpools autos prevBks d a b (dbin d a b) ka kb = true) :
    Impossible T (cap - 1) ((dbin d a b :: delTwo ws a b ka kb).map Prod.fst).toFinset := by
  let z := dbin d a b
  let rest := delTwo ws a b ka kb
  let child := (z :: rest).map Prod.fst
  have sub : rest.Sublist ws := delTwo_sub ws a b ka kb
  have ndc : child.Nodup := by
    simp only [child, List.map_cons, List.nodup_cons]
    exact ⟨fun hm => hfr ((sub.map Prod.fst).subset hm), (sub.map Prod.fst).nodup nd⟩
  have hltc : ∀ x ∈ child, x < 2^128 := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact bin_lt d a.1 b.1 (hlt a ha) (hlt b hb)
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx; exact hlt w (sub.subset hw)
  have hnz_b : (z.1 == 0) = false := beq_false_of_ne hnz
  have hfr_b : (ws.any (fun v => v.1 == z.1)) = false := by
    rw [Bool.eq_false_iff]; intro h; obtain ⟨v, hv, heq⟩ := List.any_eq_true.mp h
    have hvz : v.1 = bin d a.1 b.1 := beq_iff_eq.mp heq
    exact hfr (hvz ▸ List.mem_map_of_mem hv)
  have hleq : 1 + (ws.length - (if ka then 0 else 1) - (if kb then 0 else 1)) = child.length := by
    have hdl := delTwo_len ws a b ka kb ha hb ne
    simp only [child, rest, List.length_map, List.length_cons]
    omega
  intro k hk h
  have hsz := live_size h
  change child.toFinset.card ≤ k + 1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have hlen : child.length ≤ cap := by omega
  have hcov := cov_required gp (ws := z :: rest)
    (fun w hw => by rcases List.mem_cons.mp hw with rfl | hw; exact faithful_bin d (hf a ha) (hf b hb); exact hf w (sub.subset hw)) h
  have hcov_eq : (coverage (z :: rest)).1 = restCov (coverage ws) (dsep a) (dsep b) ka kb ||| dsep z := by
    change dsep z ||| (coverage rest).1 = _
    rw [cov_delTwo a b ha hb ne ka kb, Nat.or_comm]
  rw [hcov_eq] at hcov
  have hcov_b : (((restCov (coverage ws) (dsep a) (dsep b) ka kb ||| dsep z) &&& fullMask pos.length) != fullMask pos.length) = false := by
    simp [hcov]
  unfold evalMoveBT at test
  dsimp only at test
  have hnotgt : ¬(child.length > cap) := by omega
  dsimp only [z] at hcov_b hnz_b hfr_b
  simp only [hleq, hnotgt, ↓reduceIte, hcov_b, hnz_b, hfr_b, Bool.false_or, Bool.false_eq_true] at test
  have hab1 : a.1 ≠ b.1 := fun eq => ne (unique_fst nd ha hb eq)
  by_cases hfp : fpools.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 d ka kb) = true
  · obtain ⟨fp, hmem, hcut⟩ := List.any_eq_true.mp hfp
    have ⟨hv, hpr⟩ := hPools fp hmem
    exact fastPoolCut_sound hv hpr nd ha hb hab1 ndc hcut k hk h
  · have hfp_f : fpools.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 d ka kb) = false := Bool.eq_false_iff.mpr hfp
    simp only [hfp_f, Bool.false_eq_true, ↓reduceIte] at test
    exact closeChildBT_sound (raw := raw) (op := (d, a.1, b.1)) (rest := rest.map Prod.fst) hT (fun _ hm => (List.not_mem_nil hm).elim) hAutos hPrev ndc hltc test k hk h
lemma testAllBT_pair {cap n fmask ws cov fpools autos prevBks l}
    (h : testAllBT cap n fmask ws cov fpools autos prevBks l = true)
    {a b : Decor} (ha : a ∈ l) (hb : b ∈ l) (ne : a ≠ b) :
    (∀ d < 4, testPairBT cap n fmask ws cov fpools autos prevBks a b d = true) ∨
    (∀ d < 4, testPairBT cap n fmask ws cov fpools autos prevBks b a d = true) := by
  induction l with
  | nil => simp at ha
  | cons w l ih =>
    simp only [testAllBT, Bool.and_eq_true, List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | ha'
    · have bm := (List.mem_cons.mp hb).resolve_left ne.symm
      exact Or.inl fun d hd => h.1 b bm d (by interval_cases d <;> decide)
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact Or.inr fun d hd => h.1 a ha' d (by interval_cases d <;> decide)
      · exact ih h.2 ha' hb'
lemma nodeBT_sound {raw T pos neg ws fpools autos prevBks cap}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hf : ∀ w ∈ ws, faithful pos neg w) (nd : (ws.map Prod.fst).Nodup)
    (hlt : ∀ w ∈ ws, w.1 < 2^128) (out : T ∉ ws.map Prod.fst)
    (hPools : ∀ fp ∈ fpools, ValidPool raw T fp.1 ∧ prepPool (ws.map Prod.fst) fp.1 = some fp)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (cap - 1) xs.toFinset) prevBks)
    (checks : cap = 0 ∨ testAllBT cap ws.length (fullMask pos.length) ws (coverage ws) fpools autos prevBks ws = true) :
    Impossible T cap (ws.map Prod.fst).toFinset := by
  rcases checks with rfl | hcheck
  · intro k hk h
    have hk0 : k = 0 := by omega
    subst hk0
    obtain ⟨hS, _⟩ := h
    exact out (List.mem_toFinset.mp (hS ▸ Finset.mem_singleton_self T))
  by_cases h0 : cap = 0
  · subst h0
    intro k hk h
    have hk0 : k = 0 := by omega
    subst hk0
    obtain ⟨hS, _⟩ := h
    exact out (List.mem_toFinset.mp (hS ▸ Finset.mem_singleton_self T))
  have hcap : 0 < cap := by omega
  apply enum_step nd out
  intro a ha b hb d hd ka kb ne hnz hfr _
  obtain ⟨a, haW, rfl⟩ := List.mem_map.mp ha
  obtain ⟨b, hbW, rfl⟩ := List.mem_map.mp hb
  have ab : a ≠ b := fun e => ne (congrArg Prod.fst e)
  have one (x y : Decor) (d' : Nat) (hd' : d' < 4) (hx : x ∈ ws) (hy : y ∈ ws) (nxy : x.1 ≠ y.1)
      (k1 k2 : Bool) (hnz' : bin d' x.1 y.1 ≠ 0) (hfr' : bin d' x.1 y.1 ∉ ws.map Prod.fst)
      (ht : testPairBT cap ws.length (fullMask pos.length) ws (coverage ws) fpools autos prevBks x y d' = true) :
      Impossible T (cap - 1) (childTwo (ws.map Prod.fst) x.1 y.1 d' k1 k2).toFinset := by
    rw [← delTwo_map_toFinset nd hx hy nxy d' k1 k2]
    have hem : evalMoveBT cap ws.length (fullMask pos.length) ws (coverage ws) fpools autos prevBks d' x y (dbin d' x y) k1 k2 = true := by
      simp only [testPairBT, Bool.and_eq_true] at ht
      cases k1 <;> cases k2 <;> first | exact ht.1.1.1 | exact ht.1.2 | exact ht.1.1.2 | exact ht.2
    exact evalMoveBT_sound hT gp hf nd hlt hx hy (fun e => nxy (congrArg Prod.fst e)) hcap hd' hPools hAutos hPrev hnz' hfr' hem
  rcases testAllBT_pair hcheck haW hbW ab with hh | hh
  · exact one a b d hd haW hbW ne ka kb hnz hfr (hh d hd)
  · rw [childTwo_swap _ nd _ _ d hd]
    have hfl := flipOp_lt hd
    exact one b a (flipOp d) hfl hbW haW ne.symm kb ka
      (bin_comm_flip d hd a.1 b.1 ▸ hnz) (bin_comm_flip d hd a.1 b.1 ▸ hfr) (hh _ hfl)
def buildWiresBT (depth : Nat) (base : List Decor) (steps : List (Nat × Nat × Nat)) : BT Decor :=
  let init := (base.length, btOfList depth base)
  (steps.foldl (fun p s =>
    let a := btGet (0, 0, 0) p.2 s.2.1
    let b := btGet (0, 0, 0) p.2 s.2.2
    (p.1 + 1, btSet depth p.2 p.1 (dbin s.1 a b))) init).2
lemma buildWiresBT_faithful {depth pos neg base steps}
    (hbase : ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^128) :
    btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) (buildWiresBT depth base steps) := by
  have hdef : faithful pos neg (0, 0, 0) ∧ (0 : Nat) < 2^128 := ⟨faithful_zero pos neg, by decide⟩
  unfold buildWiresBT
  have h0 : btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) (btOfList depth base) := btAll_ofList hbase
  have hgo : ∀ (ss : List (Nat × Nat × Nat)) (acc : Nat × BT Decor),
      btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) acc.2 →
      btAll (fun x => faithful pos neg x ∧ x.1 < 2^128)
        (ss.foldl (fun p s => (p.1 + 1, btSet depth p.2 p.1 (dbin s.1 (btGet (0, 0, 0) p.2 s.2.1) (btGet (0, 0, 0) p.2 s.2.2)))) acc).2 := by
    intro ss
    induction ss with
    | nil => intro acc hacc; exact hacc
    | cons s ss ih =>
      intro acc hacc
      have ha := btAll_get hacc hdef s.2.1
      have hb := btAll_get hacc hdef s.2.2
      exact ih _ (btAll_set hacc ⟨faithful_bin s.1 ha.1 hb.1, bin_lt s.1 _ _ ha.2 hb.2⟩)
  exact hgo steps (base.length, btOfList depth base) h0
def buildPoolsBT (pdepth : Nat) (W : BT Decor) (raw : List Nat) (slices : BT (Option (Nat × Nat)))
    (pspecs : List PoolSpec) : BT (Option BoundPool) :=
  btOfList pdepth (pspecs.map fun (slIdx, chIdxs) =>
    match btGet none slices slIdx with
    | none => none
    | some (dom, lb) =>
      let cs := chIdxs.map fun (op, ia, ib) => (op, (btGet (0, 0, 0) W ia).1, (btGet (0, 0, 0) W ib).1)
      materialize raw cs dom lb)
lemma buildPoolsBT_sound {pdepth} {W : BT Decor} {raw T} {slices : BT (Option (Nat × Nat))} {pspecs : List PoolSpec}
    (hSlices : btAll (fun o => ∀ p, o = some p → Slice raw T p.1 p.2) slices) :
    btAll (fun o => ∀ c, o = some c → ValidPool raw T c) (buildPoolsBT pdepth W raw slices pspecs) := by
  apply btAll_ofList
  intro o ho c hc
  obtain ⟨⟨slIdx, chIdxs⟩, _, hmat⟩ := List.mem_map.mp ho
  dsimp only at hmat
  have hsl := btAll_get (d := none) hSlices (fun _ h => by simp at h) slIdx
  cases heq : btGet none slices slIdx with
  | none => rw [heq] at hmat; exact absurd (hmat.trans hc) (by simp)
  | some sl =>
    rw [heq] at hmat
    exact materialize_sound (hsl sl heq) (hmat.trans hc)
def checkNodeBT (W : BT Decor) (T fmask : Nat)
    (poolTable : BT (Option BoundPool)) (autosTable : BT (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (k : Nat) (ns : NodeSpec) : Bool :=
  let ws := ns.1.map fun idx => btGet (0, 0, 0) W idx
  let vals := ws.map Prod.fst
  let fpools := ns.2.1.filterMap fun pIdx =>
    match btGet none poolTable pIdx with
    | none => none
    | some c => prepPool vals c
  let nodeAutos := ns.2.2.map fun aIdx => btGet [] autosTable aIdx
  decide vals.Nodup && !(vals.contains T) &&
    (k == 0 || testAllBT k ws.length fmask ws (coverage ws) fpools nodeAutos prevBks ws)
def checkNodesBT (W : BT Decor) (T fmask : Nat)
    (poolTable : BT (Option BoundPool)) (autosTable : BT (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (k : Nat) (nodes : List NodeSpec) : Bool :=
  nodes.all (checkNodeBT W T fmask poolTable autosTable prevBks k)
lemma checkNodeBT_sound {W : BT Decor} {raw pos neg T poolTable autosTable prevBks k ns}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) W)
    (hPoolTable : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) poolTable)
    (hAutos : btAll (fun sw => swapsValid sw = true ∧ permWord sw T = T) autosTable)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (k - 1) xs.toFinset) prevBks)
    (ok : checkNodeBT W T (fullMask pos.length) poolTable autosTable prevBks k ns = true) :
    Impossible T k ((ns.1.map fun idx => (btGet (0, 0, 0) W idx).1).toFinset) := by
  have hdef : faithful pos neg (0, 0, 0) ∧ (0 : Nat) < 2^128 := ⟨faithful_zero pos neg, by decide⟩
  have hget (idx : Nat) : faithful pos neg (btGet (0, 0, 0) W idx) ∧ (btGet (0, 0, 0) W idx).1 < 2^128 :=
    btAll_get hW hdef idx
  unfold checkNodeBT at ok
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.contains_eq_mem, Bool.or_eq_true, beq_iff_eq] at ok
  let ws := ns.1.map fun idx => btGet (0, 0, 0) W idx
  have hmap : ws.map Prod.fst = ns.1.map fun idx => (btGet (0, 0, 0) W idx).1 := by simp [ws, List.map_map, Function.comp_def]
  rw [← hmap]
  apply nodeBT_sound hT gp
    (fun w hw => by obtain ⟨idx, _, rfl⟩ := List.mem_map.mp hw; exact (hget idx).1)
    ok.1.1
    (fun w hw => by obtain ⟨idx, _, rfl⟩ := List.mem_map.mp hw; exact (hget idx).2)
    (of_decide_eq_false ok.1.2)
    (fun fp hfp => by
      obtain ⟨pIdx, _, hmat⟩ := List.mem_filterMap.mp hfp
      cases heq : btGet none poolTable pIdx with
      | none => simp [heq] at hmat
      | some c =>
        simp only [heq] at hmat
        have hvc := btAll_get hPoolTable (fun _ h => by simp at h) pIdx c heq
        have hfp_eq : fp.1 = c := by
          unfold prepPool at hmat
          dsimp only at hmat
          split at hmat
          · simp at hmat
          · simp only [Option.some.injEq] at hmat; rw [← hmat]
        rw [hfp_eq]
        exact ⟨hvc, hmat⟩)
    (fun sw hsw => by
      obtain ⟨aIdx, _, rfl⟩ := List.mem_map.mp hsw
      exact btAll_get hAutos ⟨rfl, rfl⟩ aIdx)
    hPrev ok.2
def nodeValsBT (W : BT Decor) (ns : NodeSpec) : List Nat :=
  sortNats (ns.1.map fun idx => (btGet (0, 0, 0) W idx).1)
def buildBucketsBT (W : BT Decor) (nodes : List NodeSpec) : BT (List (List Nat)) :=
  nodes.foldl (fun acc ns =>
    let xs := nodeValsBT W ns
    btUpdate [] 6 acc (hashWs64 xs) (fun b => if b.contains xs then b else xs :: b)) BT.empty
lemma buildBucketsBT_sound {W : BT Decor} {raw pos neg T poolTable autosTable prevBks k}
    {nodes : List NodeSpec}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) W)
    (hPoolTable : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) poolTable)
    (hAutos : btAll (fun sw => swapsValid sw = true ∧ permWord sw T = T) autosTable)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (k - 1) xs.toFinset) prevBks)
    (hNodes : checkNodesBT W T (fullMask pos.length) poolTable autosTable prevBks k nodes = true) :
    btAll (fun bk => ∀ xs ∈ bk, Impossible T k xs.toFinset) (buildBucketsBT W nodes) := by
  have hmem : ∀ ns ∈ nodes, Impossible T k (nodeValsBT W ns).toFinset := fun ns hns => by
    unfold nodeValsBT; rw [sortNats_toFinset]
    exact checkNodeBT_sound hT gp hW hPoolTable hAutos hPrev (List.all_eq_true.mp hNodes ns hns)
  clear hNodes
  unfold buildBucketsBT
  have hinit : btAll (fun bk => ∀ xs ∈ bk, Impossible T k xs.toFinset) (BT.empty : BT (List (List Nat))) := trivial
  generalize (BT.empty : BT (List (List Nat))) = acc at hinit ⊢
  induction nodes generalizing acc with
  | nil => exact hinit
  | cons ns rest ih =>
    apply ih (fun x hx => hmem x (List.mem_cons_of_mem _ hx))
    apply btAll_update hinit (fun _ h => (List.not_mem_nil h).elim)
    intro b hb ys hys
    split at hys
    · exact hb ys hys
    · rcases List.mem_cons.mp hys with rfl | hys'
      · exact hmem ns (List.mem_cons_self ..)
      · exact hb ys hys'
lemma lower_of_forestBT {roots T cap} {topBks : BT (List (List Nat))} {essPairs : List (Nat × Nat × Nat)}
    (ok : forestRootCheck roots T essPairs = true)
    (hTop : btAll (fun bk => ∀ xs ∈ bk, Impossible T cap xs.toFinset) topBks)
    (hRoot : bucketContainsBT topBks roots = true) :
    Lower roots T (cap + 1) := by
  simp only [forestRootCheck, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq] at ok
  obtain ⟨⟨hT, hR⟩, hess⟩ := ok
  have ⟨p1, p2, p3⟩ := checkProper_sound hT
  have hR' := checkRoots_sound hR
  have hEss' : ∀ a ∈ roots, Essential T roots a := fun a ha => by
    obtain ⟨⟨v, r, s⟩, _, rfl, he⟩ := hess a ha
    exact checkEss1_sound he
  have hImp : Impossible T cap (sortNats roots).toFinset := by
    unfold bucketContainsBT at hRoot
    exact btAll_get hTop (fun _ h => (List.not_mem_nil h).elim) _ _ (List.contains_iff_mem.mp hRoot)
  rw [sortNats_toFinset] at hImp
  exact lower_of_impossible p1 p2 p3 hR' hEss' hImp
def h1R : List Nat := varsOf 28
def h1G : Nat := 0xfff0f000fff0f000fff0f000fff0f000
def h1Pos : List Nat := [20,24,12,12,24,20]
def h1Neg : List Nat := [16,16,4,8,8,4]
def h1Mask : Nat := fullMask 6
def h1Base : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,45,36),(0xff00ff00ff00ff00ff00ff00ff00ff00,30,24),(0xffff0000ffff0000ffff0000ffff0000,51,3)]
def h1Steps : List (Nat × Nat × Nat) := []
def h1W : BT Decor := buildWiresBT 2 h1Base h1Steps
def h1AutoList : List (List (Nat × Nat)) := [[],[(3,4)],[(2,3)],[(2,4)],[(3,4),(2,3)],[(3,4),(2,4)]]
def h1Autos : BT (List (Nat × Nat)) := btOfList 3 h1AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Pairs : goodPairs h1G h1Pos h1Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1BaseOk : ∀ x ∈ h1Base, faithful h1Pos h1Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1WOk : btAll (fun x => faithful h1Pos h1Neg x ∧ x.1 < 2^128) h1W := buildWiresBT_faithful h1BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h1G = h1G) h1Autos := btAll_ofList (autos_of (by decide +kernel))
def h1SliceList : List (Option (Nat × Nat)) := []
def h1Slices : BT (Option (Nat × Nat)) := btOfList 1 h1SliceList
def h1Specs : List PoolSpec := []
def h1Pools : BT (Option BoundPool) := buildPoolsBT 1 h1W h1R h1Slices h1Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h1R h1G p.1 p.2) h1Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h1R h1G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h1R h1G c) h1Pools := buildPoolsBT_sound h1SlicesOk
def h1Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h1G (3 - 1) xs.toFinset) h1Empty := trivial
def h1Block3_0 : List NodeSpec := nodesWithIdentity [([0,1,2],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test3_0 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Empty 3 h1Block3_0 = true := by decide +kernel
def h1Nodes3 : List NodeSpec := h1Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Check3 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Empty 3 h1Nodes3 = true := h1Test3_0
def h1Bucket3 : BT (List (List Nat)) := buildBucketsBT h1W h1Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h1G 3 xs.toFinset) h1Bucket3 := buildBucketsBT_sound (by decide) h1Pairs h1WOk h1PoolsOk h1AutosOk h1EmptyOk h1Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Bound : Lower h1R h1G 4 := lower_of_forestBT (essPairs := [(VAR 2,8,12),(VAR 3,4,12),(VAR 4,4,20)]) (by decide +kernel) h1Bucket3Ok (by decide +kernel)
def h2R : List Nat := varsOf 29
def h2G : Nat := 0xfffaf0a0fffaf0a0fffaf0a0fffaf0a0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h2Bound : Lower h2R h2G 5 := lift_of (z := 1) (o := 0) (essPairs := [(VAR 0,4,5)]) (by decide +kernel) h1Bound
def h4R : List Nat := varsOf 11
def h4G : Nat := 0xee88ee88ee88ee88ee88ee88ee88ee88
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4Bound : Lower h4R h4G 4 := carry_of (swaps := [(1,2),(2,3),(3,4),(0,1),(1,2)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h5R : List Nat := varsOf 15
def h5G : Nat := 0xe080e080e080e080e080e080e080e080
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Bound : Lower h5R h5G 5 := lift_of (z := 0) (o := 4) (essPairs := [(VAR 2,3,7)]) (by decide +kernel) h4Bound
def h6R : List Nat := varsOf 21
def h6G : Nat := 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Bound : Lower h6R h6G 4 := carry_of (swaps := [(1,2),(2,3),(0,1)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h7R : List Nat := varsOf 23
def h7G : Nat := 0xc8c88080c8c88080c8c88080c8c88080
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Bound : Lower h7R h7G 5 := carry_of (swaps := [(3,4),(1,2)]) (roots2 := h5R) (T2 := h5G) (by decide +kernel) h5Bound
def h8R : List Nat := varsOf 30
def h8G : Nat := 0xccc0c000ccc0c000ccc0c000ccc0c000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8Bound : Lower h8R h8G 5 := carry_of (swaps := [(3,4),(1,2),(2,3),(0,1),(1,2),(0,1)]) (roots2 := h5R) (T2 := h5G) (by decide +kernel) h5Bound
def h9R : List Nat := varsOf 15
def h9G : Nat := 0xecc8ecc8ecc8ecc8ecc8ecc8ecc8ecc8
def h9Pos : List Nat := [6,13,6,6,13,10,13,3,3,3,10,7,7]
def h9Neg : List Nat := [4,12,5,2,9,2,5,2,1,0,8,2,5]
def h9Mask : Nat := fullMask 13
def h9Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,7122,4436),(0xcccccccccccccccccccccccccccccccc,8109,2216),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,6239,4167),(0xff00ff00ff00ff00ff00ff00ff00ff00,1138,1042)]
def h9Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(3,0,1),(0,0,2),(1,0,2),(2,0,2),(1,2,4),(2,2,4),(0,2,5),(3,2,5),(1,3,10),(2,3,10)]
def h9W : BT Decor := buildWiresBT 5 h9Base h9Steps
def h9AutoList : List (List (Nat × Nat)) := [[],[(2,3)],[(0,2)],[(0,3)],[(2,3),(0,2)],[(2,3),(0,3)]]
def h9Autos : BT (List (Nat × Nat)) := btOfList 3 h9AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Pairs : goodPairs h9G h9Pos h9Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9BaseOk : ∀ x ∈ h9Base, faithful h9Pos h9Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9WOk : btAll (fun x => faithful h9Pos h9Neg x ∧ x.1 < 2^128) h9W := buildWiresBT_faithful h9BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h9G = h9G) h9Autos := btAll_ofList (autos_of (by decide +kernel))
def h9SliceList : List (Option (Nat × Nat)) := []
def h9Slices : BT (Option (Nat × Nat)) := btOfList 1 h9SliceList
def h9Specs : List PoolSpec := []
def h9Pools : BT (Option BoundPool) := buildPoolsBT 1 h9W h9R h9Slices h9Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h9R h9G p.1 p.2) h9Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h9R h9G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h9R h9G c) h9Pools := buildPoolsBT_sound h9SlicesOk
def h9Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h9G (3 - 1) xs.toFinset) h9Empty := trivial
def h9Block3_0 : List NodeSpec := nodesWithIdentity [([0,1,3,11],[]),([0,1,3,12],[]),([0,1,3,13],[]),([0,1,3,14],[]),([1,3,8,9],[]),([0,1,2,15],[]),([0,1,2,16],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test3_0 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Empty 3 h9Block3_0 = true := by decide +kernel
def h9Nodes3 : List NodeSpec := h9Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Check3 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Empty 3 h9Nodes3 = true := h9Test3_0
def h9Bucket3 : BT (List (List Nat)) := buildBucketsBT h9W h9Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h9G 3 xs.toFinset) h9Bucket3 := buildBucketsBT_sound (by decide) h9Pairs h9WOk h9PoolsOk h9AutosOk h9EmptyOk h9Check3
def h9Block4_0 : List NodeSpec := [([0,1,2,3,4],[],[0,1]),([0,1,2,3,5],[],[0,1]),([0,1,2,3,6],[],[0]),([0,1,2,3,7],[],[0]),([0,1,2,3,8],[],[0]),([0,1,2,3,9],[],[0]),([0,1,2,3,10],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test4_0 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket3 4 h9Block4_0 = true := by decide +kernel
def h9Nodes4 : List NodeSpec := h9Block4_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Check4 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket3 4 h9Nodes4 = true := h9Test4_0
def h9Bucket4 : BT (List (List Nat)) := buildBucketsBT h9W h9Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h9G 4 xs.toFinset) h9Bucket4 := buildBucketsBT_sound (by decide) h9Pairs h9WOk h9PoolsOk h9AutosOk h9Bucket3Ok h9Check4
def h9Block5_0 : List NodeSpec := [([0,1,2,3],[],[0,1,2,3,4,5])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test5_0 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket4 5 h9Block5_0 = true := by decide +kernel
def h9Nodes5 : List NodeSpec := h9Block5_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Check5 : checkNodesBT h9W h9G h9Mask h9Pools h9Autos h9Bucket4 5 h9Nodes5 = true := h9Test5_0
def h9Bucket5 : BT (List (List Nat)) := buildBucketsBT h9W h9Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h9G 5 xs.toFinset) h9Bucket5 := buildBucketsBT_sound (by decide) h9Pairs h9WOk h9PoolsOk h9AutosOk h9Bucket4Ok h9Check5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Bound : Lower h9R h9G 6 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,2,6),(VAR 3,2,10)]) (by decide +kernel) h9Bucket5Ok (by decide +kernel)
def h10R : List Nat := varsOf 23
def h10G : Nat := 0xecece0e0ecece0e0ecece0e0ecece0e0
def h10Pos : List Nat := [5,19,6,6,5,19,18,21]
def h10Neg : List Nat := [4,17,4,2,1,3,2,17]
def h10Mask : Nat := fullMask 8
def h10Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,179,178),(0xcccccccccccccccccccccccccccccccc,110,104),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,157,5),(0xffff0000ffff0000ffff0000ffff0000,226,130)]
def h10Steps : List (Nat × Nat × Nat) := []
def h10W : BT Decor := buildWiresBT 2 h10Base h10Steps
def h10AutoList : List (List (Nat × Nat)) := [[],[(1,2),(0,4)]]
def h10Autos : BT (List (Nat × Nat)) := btOfList 1 h10AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h10Pairs : goodPairs h10G h10Pos h10Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h10BaseOk : ∀ x ∈ h10Base, faithful h10Pos h10Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h10WOk : btAll (fun x => faithful h10Pos h10Neg x ∧ x.1 < 2^128) h10W := buildWiresBT_faithful h10BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h10AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h10G = h10G) h10Autos := btAll_ofList (autos_of (by decide +kernel))
def h10SliceList : List (Option (Nat × Nat)) := []
def h10Slices : BT (Option (Nat × Nat)) := btOfList 1 h10SliceList
def h10Specs : List PoolSpec := []
def h10Pools : BT (Option BoundPool) := buildPoolsBT 1 h10W h10R h10Slices h10Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h10SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h10R h10G p.1 p.2) h10Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h10R h10G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h10PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h10R h10G c) h10Pools := buildPoolsBT_sound h10SlicesOk
def h10Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h10EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h10G (3 - 1) xs.toFinset) h10Empty := trivial
def h10Block3_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h10Test3_0 : checkNodesBT h10W h10G h10Mask h10Pools h10Autos h10Empty 3 h10Block3_0 = true := by decide +kernel
def h10Nodes3 : List NodeSpec := h10Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h10Check3 : checkNodesBT h10W h10G h10Mask h10Pools h10Autos h10Empty 3 h10Nodes3 = true := h10Test3_0
def h10Bucket3 : BT (List (List Nat)) := buildBucketsBT h10W h10Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h10Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h10G 3 xs.toFinset) h10Bucket3 := buildBucketsBT_sound (by decide) h10Pairs h10WOk h10PoolsOk h10AutosOk h10EmptyOk h10Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h10Bound : Lower h10R h10G 4 := lower_of_forestBT (essPairs := [(VAR 0,4,5),(VAR 1,4,6),(VAR 2,1,5),(VAR 4,2,18)]) (by decide +kernel) h10Bucket3Ok (by decide +kernel)
def h11R : List Nat := varsOf 27
def h11G : Nat := 0xeeccee88eeccee88eeccee88eeccee88
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Bound : Lower h11R h11G 5 := lift_of (z := 16) (o := 0) (essPairs := [(VAR 4,2,18)]) (by decide +kernel) h4Bound
def h12R : List Nat := varsOf 30
def h12G : Nat := 0xfcccf0c0fcccf0c0fcccf0c0fcccf0c0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h12Bound : Lower h12R h12G 4 := carry_of (swaps := [(0,1),(1,2),(2,3),(1,2),(0,1)]) (roots2 := h10R) (T2 := h10G) (by decide +kernel) h10Bound
def h3R : List Nat := varsOf 31
def h3G : Nat := 0xecc8e080ecc8e080ecc8e080ecc8e080
def h3Pos : List Nat := [13,14,22,14,7,13,26,13,22,14,19,7,26,22,29,19,26,22,29,7,7,14,7,15,19,19,13,13,29,22,26,27,13,27,23,7,14,13,22,13,13,13,27,19,7,7,13,19,22,30,26,19,26]
def h3Neg : List Nat := [12,12,21,10,3,9,24,5,20,6,3,5,18,6,25,18,10,18,28,2,6,11,11,11,25,17,1,25,21,2,2,11,21,25,21,4,2,4,28,0,8,11,18,21,1,21,28,2,16,28,11,1,25]
def h3Mask : Nat := fullMask 53
def h3Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x8ffaf9fdcccb1,0x1c3a079fe04cb4),(0xcccccccccccccccccccccccccccccccc,0x1fbc5ee3fbbf5e,0x48610e0fbb618),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x373fd3cfe6bbf,0x2686d10142b87),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x1647b3dca552eb,0x16434289e5406b),(0xffff0000ffff0000ffff0000ffff0000,0x1f8c46f307f544,0x136c471b06d144)]
def h3Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(3,0,1),(0,0,2),(1,0,2),(2,0,2),(3,0,2),(0,1,2),(1,1,2),(2,1,2),(3,1,2),(0,1,4),(2,1,4),(3,1,4),(0,1,12),(2,1,12),(0,2,3),(1,2,3),(2,2,3),(0,2,4),(3,2,4),(2,2,5),(3,3,4),(1,3,5),(0,1,29),(2,1,29),(0,2,29),(0,1,32),(2,1,32),(0,4,29),(2,4,32),(2,12,29),(2,29,32),(1,3,12),(2,3,12),(2,3,5),(1,5,12),(0,1,42),(0,2,42),(0,0,3),(1,0,3),(2,0,3),(0,0,4),(3,0,4),(3,0,23),(0,1,23),(3,5,23),(1,0,24),(3,3,53),(1,5,24),(1,0,25),(2,1,25),(1,5,25),(0,1,58),(1,0,26),(0,1,60),(2,1,26),(1,5,26),(1,0,28),(1,5,28),(1,0,32),(0,2,6),(1,0,67),(0,4,67),(2,4,67),(3,2,6),(0,3,6),(3,3,6),(0,4,6),(2,6,25),(2,6,26),(1,0,71),(1,0,74),(2,4,7),(1,7,25),(1,7,26),(1,8,12),(2,2,31),(0,2,46),(3,2,46),(2,4,9),(0,4,46),(3,9,46),(3,24,46),(1,3,9),(1,4,84),(2,4,84),(2,1,54),(2,10,18),(3,0,94),(2,3,11),(2,2,30),(1,17,46),(3,17,46),(1,12,18),(1,18,46),(3,18,46),(1,12,24),(2,2,47),(1,12,47),(0,1,39),(2,1,37),(1,3,95),(1,25,45),(3,25,46),(3,45,46),(1,26,45),(3,26,46),(0,46,103),(2,46,103),(2,2,114),(1,17,84),(1,17,33),(3,13,46),(3,15,46),(3,3,78),(0,2,117),(1,18,84),(1,3,87),(1,25,47),(1,26,47),(2,1,49),(1,3,49),(0,1,128),(0,0,14),(0,4,14),(2,4,16)]
def h3W : BT Decor := buildWiresBT 8 h3Base h3Steps
def h3AutoList : List (List (Nat × Nat)) := [[],[(0,3)]]
def h3Autos : BT (List (Nat × Nat)) := btOfList 1 h3AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Pairs : goodPairs h3G h3Pos h3Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3BaseOk : ∀ x ∈ h3Base, faithful h3Pos h3Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3WOk : btAll (fun x => faithful h3Pos h3Neg x ∧ x.1 < 2^128) h3W := buildWiresBT_faithful h3BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h3G = h3G) h3Autos := btAll_ofList (autos_of (by decide +kernel))
def h3SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,4),some (subcubeFast 0 2,5),some (subcubeFast 0 4,5),some (subcubeFast 0 8,4),some (subcubeFast 0 16,6),some (subcubeFast 1 0,5),some (subcubeFast 1 2,4),some (subcubeFast 8 0,5),some (subcubeFast 8 2,4),some (subcubeFast 16 0,5),some (subcubeFast 16 4,4)]
def h3Slices : BT (Option (Nat × Nat)) := btOfList 4 h3SliceList
def h3Specs : List PoolSpec := [(5,[]),(1,[]),(6,[]),(0,[]),(2,[]),(1,[(1,3,5)]),(7,[(0,0,1)]),(8,[]),(9,[(3,0,2)]),(4,[(0,0,1)]),(3,[]),(7,[]),(9,[]),(4,[]),(4,[(0,0,1),(2,2,5)]),(4,[(0,0,1),(1,3,5)]),(4,[(0,0,1),(2,3,5)]),(1,[(2,3,5)]),(4,[(1,0,1)]),(5,[(0,2,6)]),(5,[(0,3,6)]),(4,[(1,0,1),(0,2,6)]),(5,[(3,2,6)]),(4,[(1,0,1),(3,2,6)]),(4,[(1,0,1),(0,3,6)]),(5,[(3,3,6)]),(4,[(1,0,1),(3,3,6)]),(5,[(0,4,6)]),(4,[(2,0,1)]),(7,[(3,0,1)]),(4,[(3,0,1)]),(5,[(0,1,12)]),(5,[(2,1,29)]),(1,[(1,0,3)]),(9,[(0,0,2)]),(4,[(0,0,2)]),(10,[]),(4,[(0,2,3)]),(4,[(2,2,3),(1,0,24)]),(4,[(2,2,3)]),(4,[(3,0,2)]),(2,[(2,4,9)]),(4,[(1,0,2)]),(5,[(2,1,4)]),(2,[(2,1,4)]),(7,[(2,1,4)]),(5,[(0,1,42)]),(4,[(2,0,2)]),(4,[(2,0,2),(2,3,11)]),(7,[(0,1,4),(0,0,1)]),(7,[(0,1,4)]),(2,[(0,1,4)]),(1,[(2,0,3)]),(5,[(0,1,2)]),(5,[(0,1,4)]),(5,[(2,1,12)]),(4,[(3,0,2),(1,3,12)]),(4,[(0,0,3),(1,0,3)]),(4,[(0,0,3)]),(4,[(1,0,3)]),(5,[(0,1,4),(0,1,29)]),(5,[(0,1,29)]),(4,[(2,0,3)]),(4,[(2,0,3),(2,2,47)]),(5,[(2,1,49)]),(4,[(2,1,49)]),(4,[(1,3,49)]),(4,[(0,1,2)]),(5,[(0,1,2),(0,1,4)]),(9,[(0,1,2)]),(4,[(2,1,26)]),(4,[(1,1,2)]),(4,[(1,1,2),(0,0,14)]),(4,[(2,1,2)]),(4,[(2,1,25)]),(7,[(0,1,2)]),(4,[(3,1,2)]),(9,[(3,1,2)]),(2,[(2,4,16)]),(4,[(1,0,25)]),(2,[(1,0,25)]),(2,[(2,1,25)]),(4,[(1,0,26)])]
def h3Pools : BT (Option BoundPool) := buildPoolsBT 7 h3W h3R h3Slices h3Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Slice10 : Slice h3R h3G (subcubeFast 16 4) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h4Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Slice9 : Slice h3R h3G (subcubeFast 16 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h5Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Slice8 : Slice h3R h3G (subcubeFast 8 2) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h6Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Slice7 : Slice h3R h3G (subcubeFast 8 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h7Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Slice6 : Slice h3R h3G (subcubeFast 1 2) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h1Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Slice5 : Slice h3R h3G (subcubeFast 1 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h8Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Slice4 : Slice h3R h3G (subcubeFast 0 16) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h9Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Slice3 : Slice h3R h3G (subcubeFast 0 8) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h10Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Slice2 : Slice h3R h3G (subcubeFast 0 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h11Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Slice1 : Slice h3R h3G (subcubeFast 0 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h2Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Slice0 : Slice h3R h3G (subcubeFast 0 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h12Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h3R h3G p.1 p.2) h3Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h3R h3G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h3Slice0) (forall_cons (fun _ h => by cases h; exact h3Slice1) (forall_cons (fun _ h => by cases h; exact h3Slice2) (forall_cons (fun _ h => by cases h; exact h3Slice3) (forall_cons (fun _ h => by cases h; exact h3Slice4) (forall_cons (fun _ h => by cases h; exact h3Slice5) (forall_cons (fun _ h => by cases h; exact h3Slice6) (forall_cons (fun _ h => by cases h; exact h3Slice7) (forall_cons (fun _ h => by cases h; exact h3Slice8) (forall_cons (fun _ h => by cases h; exact h3Slice9) (forall_cons (fun _ h => by cases h; exact h3Slice10) (fun _ h => (List.not_mem_nil h).elim))))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h3R h3G c) h3Pools := buildPoolsBT_sound h3SlicesOk
def h3Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h3G (4 - 1) xs.toFinset) h3Empty := trivial
def h3Block4_0 : List NodeSpec := nodesWithIdentity [([1,4,12,29,32],[]),([1,4,12,29,38],[]),([1,2,4,29,60],[]),([0,1,2,29,36],[]),([2,3,12,17,30],[49]),([0,2,3,17,107],[]),([0,1,2,18,108],[]),([1,2,4,45,110],[]),([1,2,4,46,112],[]),([1,4,46,84,103],[]),([1,4,46,85,103],[]),([1,2,4,46,114],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Test4_0 : checkNodesBT h3W h3G h3Mask h3Pools h3Autos h3Empty 4 h3Block4_0 = true := by decide +kernel
def h3Block4_1 : List NodeSpec := nodesWithIdentity [([1,2,4,46,115],[]),([1,2,45,46,92],[]),([1,2,4,46,116],[]),([0,3,13,17,84],[]),([0,2,3,17,33],[13]),([0,2,3,17,119],[]),([2,3,17,30,78],[49]),([0,2,3,17,97],[]),([0,1,2,3,117],[13]),([0,1,3,17,122],[]),([0,1,2,3,123],[]),([0,2,3,84,118],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Test4_1 : checkNodesBT h3W h3G h3Mask h3Pools h3Autos h3Empty 4 h3Block4_1 = true := by decide +kernel
def h3Nodes4 : List NodeSpec := h3Block4_0 ++ h3Block4_1
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Check4 : checkNodesBT h3W h3G h3Mask h3Pools h3Autos h3Empty 4 h3Nodes4 = true := by
  unfold h3Nodes4 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h3Test4_0,h3Test4_1⟩
def h3Bucket4 : BT (List (List Nat)) := buildBucketsBT h3W h3Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h3G 4 xs.toFinset) h3Bucket4 := buildBucketsBT_sound (by decide) h3Pairs h3WOk h3PoolsOk h3AutosOk h3EmptyOk h3Check4
def h3Block5_0 : List NodeSpec := nodesWithIdentity [([1,2,4,12,29],[0,2,5,6,7]),([1,2,3,4,12,29],[6,7]),([1,2,3,4,12,42],[]),([1,2,3,4,5,50],[10]),([0,2,3,4,5,51],[4]),([0,1,2,3,4,52],[0]),([1,2,3,4,5,53],[10]),([0,1,2,3,4,55],[0]),([0,1,2,4,25,29],[]),([0,1,2,4,25,41],[]),([0,1,2,3,4,58],[]),([1,2,3,4,5,60],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Test5_0 : checkNodesBT h3W h3G h3Mask h3Pools h3Autos h3Bucket4 5 h3Block5_0 = true := by decide +kernel
def h3Block5_1 : List NodeSpec := nodesWithIdentity [([0,1,2,4,26,29],[0]),([0,1,2,4,26,41],[]),([0,1,2,3,4,63],[]),([1,2,3,4,5,64],[10]),([0,1,2,3,4,65],[0]),([0,1,2,4,29,32],[0,6,10,15]),([0,1,2,4,29,38],[0,7]),([0,1,2,4,29,35],[]),([0,1,2,3,4,32],[0,10,12,13]),([0,1,3,4,25,67],[3,13,19]),([0,1,2,4,25,72],[3,20]),([0,1,2,4,25,73],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Test5_1 : checkNodesBT h3W h3G h3Mask h3Pools h3Autos h3Bucket4 5 h3Block5_1 = true := by decide +kernel
def h3Block5_2 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,75],[1,13]),([0,1,3,4,26,67],[]),([0,1,2,4,26,72],[]),([0,1,2,4,26,73],[]),([0,1,2,3,4,76],[1,13]),([0,1,3,4,67,69],[3,19]),([0,1,3,4,67,70],[]),([1,2,3,4,7,56],[12]),([0,1,2,3,4,80],[13]),([0,1,2,3,4,81],[13]),([0,1,2,3,4,83],[12,13]),([1,2,4,9,22,46],[0,4])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Test5_2 : checkNodesBT h3W h3G h3Mask h3Pools h3Autos h3Bucket4 5 h3Block5_2 = true := by decide +kernel
def h3Block5_3 : List NodeSpec := nodesWithIdentity [([1,2,4,9,24,46],[0]),([1,2,3,4,46,88],[0]),([1,2,3,4,9,66],[]),([0,1,2,3,4,84],[12,13]),([1,2,3,4,9,53],[38]),([0,1,2,3,18,54],[]),([0,1,2,3,18,94],[42]),([0,1,2,3,4,93],[0]),([1,2,3,12,17,46],[50,51]),([1,2,3,12,18,46],[44,45]),([1,2,3,4,12,30],[0,6]),([1,2,4,12,24,46],[0,4])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Test5_3 : checkNodesBT h3W h3G h3Mask h3Pools h3Autos h3Bucket4 5 h3Block5_3 = true := by decide +kernel
def h3Block5_4 : List NodeSpec := nodesWithIdentity [([1,2,3,4,12,105],[0]),([0,2,3,4,13,21],[13]),([0,1,2,3,17,39],[]),([0,1,2,3,17,37],[1]),([0,1,2,3,18,39],[]),([0,1,2,3,18,37],[]),([0,1,2,3,18,100],[]),([0,1,2,3,18,95],[45]),([0,1,2,3,4,106],[0]),([0,1,2,3,4,107],[]),([1,2,4,25,45,46],[3]),([1,2,4,26,45,46],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Test5_4 : checkNodesBT h3W h3G h3Mask h3Pools h3Autos h3Bucket4 5 h3Block5_4 = true := by decide +kernel
def h3Block5_5 : List NodeSpec := nodesWithIdentity [([1,2,4,46,103],[0,2,33]),([1,2,4,45,46,84],[0,3,57]),([1,2,4,45,46,85],[0]),([1,2,4,45,46,87],[57]),([1,2,4,46,111],[0,2,33]),([1,2,3,4,45,56],[3]),([0,1,2,3,4,109],[]),([0,1,2,3,4,112],[]),([0,2,3,13,17,46],[2,7,51]),([0,2,3,4,13,30],[2,4,7]),([0,1,3,4,13,84],[1,3,10]),([0,1,2,3,4,33],[0,11,12,13])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Test5_5 : checkNodesBT h3W h3G h3Mask h3Pools h3Autos h3Bucket4 5 h3Block5_5 = true := by decide +kernel
def h3Block5_6 : List NodeSpec := [([0,1,2,3,4,119],[],[0]),([0,1,3,4,15,84],[],[0]),([0,1,2,3,4,120],[12,13],[0]),([1,2,3,17,46,78],[12,50],[0]),([0,2,3,17,30],[2,5,7,13,49,60],[0,1]),([0,2,3,17,30,46],[1,2,49,60],[0]),([0,1,2,3,17,84],[1,12],[0]),([0,1,2,3,17,98],[1,13,51],[0]),([0,1,2,3,17,99],[1,13],[0]),([0,2,3,4,17,30],[2,13],[0]),([0,1,2,3,4,99],[1],[0]),([0,1,2,3,18,84],[13],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Test5_6 : checkNodesBT h3W h3G h3Mask h3Pools h3Autos h3Bucket4 5 h3Block5_6 = true := by decide +kernel
def h3Block5_7 : List NodeSpec := nodesWithIdentity [([0,1,2,3,18,101],[]),([0,1,2,3,18,102],[59]),([0,1,2,3,4,97],[]),([0,1,3,4,25,84],[13]),([0,1,2,3,4,110],[]),([0,1,3,4,26,84],[13]),([0,1,2,3,4,113],[12]),([0,1,2,3,4,34],[12,13]),([0,1,2,3,84,91],[12]),([0,1,2,3,84,92],[13]),([0,1,2,3,46,92],[]),([0,1,2,3,4,125],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Test5_7 : checkNodesBT h3W h3G h3Mask h3Pools h3Autos h3Bucket4 5 h3Block5_7 = true := by decide +kernel
def h3Block5_8 : List NodeSpec := nodesWithIdentity [([1,2,3,4,47,60],[]),([0,1,2,3,4,126],[]),([0,1,2,3,4,129],[0]),([0,2,3,13,17,68],[1,2,68]),([0,2,3,13,17,20],[2]),([0,1,2,3,18,62],[70]),([0,1,2,3,18,57],[74]),([0,1,2,3,17,121],[]),([0,1,2,3,4,59],[10,11,12]),([0,1,2,3,4,61],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Test5_8 : checkNodesBT h3W h3G h3Mask h3Pools h3Autos h3Bucket4 5 h3Block5_8 = true := by decide +kernel
def h3Nodes5 : List NodeSpec := h3Block5_0 ++ h3Block5_1 ++ h3Block5_2 ++ h3Block5_3 ++ h3Block5_4 ++ h3Block5_5 ++ h3Block5_6 ++ h3Block5_7 ++ h3Block5_8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Check5 : checkNodesBT h3W h3G h3Mask h3Pools h3Autos h3Bucket4 5 h3Nodes5 = true := by
  unfold h3Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨h3Test5_0,h3Test5_1⟩,h3Test5_2⟩,h3Test5_3⟩,h3Test5_4⟩,h3Test5_5⟩,h3Test5_6⟩,h3Test5_7⟩,h3Test5_8⟩
def h3Bucket5 : BT (List (List Nat)) := buildBucketsBT h3W h3Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h3G 5 xs.toFinset) h3Bucket5 := buildBucketsBT_sound (by decide) h3Pairs h3WOk h3PoolsOk h3AutosOk h3Bucket4Ok h3Check5
def h3Block6_0 : List NodeSpec := nodesWithIdentity [([1,2,3,4,5,12],[0,1,2,3,4,6,8]),([0,1,2,3,4,5,23],[0,1,4,10,11]),([0,1,2,3,4,5,24],[0,7,10,11]),([0,1,2,3,4,5,25],[0,12]),([0,1,2,3,4,5,26],[0,4,12,13]),([0,1,2,3,4,27],[0,1,2,3,10,11,12,13,14]),([0,1,2,3,4,5,28],[0,10,11,12]),([0,1,2,4,29],[0,2,5,7,10,15]),([0,1,2,3,4,29],[0,1,2,3,4,5,6,7,10,12,13,15]),([0,1,2,4,41],[0,2,11,16,17]),([0,1,2,3,4,6,25],[0,1,3,4,12,13]),([0,1,2,3,4,6,26],[1,4,12,13])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Test6_0 : checkNodesBT h3W h3G h3Mask h3Pools h3Autos h3Bucket5 6 h3Block6_0 = true := by decide +kernel
def h3Block6_1 : List NodeSpec := nodesWithIdentity [([0,1,3,4,67],[1,2,3,7,19,21]),([0,1,2,3,4,67],[0,1,2,3,7,10,11,12,13,19,21]),([0,1,3,4,71],[1,3,4,7,22,23]),([0,1,2,4,72],[1,3,11,20,24]),([0,1,2,4,73],[1,3,7,10,25,26]),([0,1,2,3,74],[1,3,7,12,13,18,27]),([0,1,2,3,4,7,25],[0,12,13]),([0,1,2,3,4,7,26],[0,4,12,13]),([0,1,2,3,4,44],[0,1,7,10,11,12,13]),([0,1,2,3,79],[0,1,7,12,13,28]),([1,2,3,4,8,12],[0,1,2,3,4,8,29]),([0,1,2,3,4,8,23],[0,2,3,4])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Test6_1 : checkNodesBT h3W h3G h3Mask h3Pools h3Autos h3Bucket5 6 h3Block6_1 = true := by decide +kernel
def h3Block6_2 : List NodeSpec := [([0,1,2,3,4,8,24],[0,2,3,7,10,11],[0]),([0,1,2,3,4,8,25],[2,3,12],[0]),([0,1,2,3,4,8,26],[0,2,3,4,12,13],[0]),([0,1,2,3,4,20],[2,3,10,11,12,13,31],[0]),([0,1,2,3,4,8,28],[0,2,3,12],[0]),([0,1,2,3,4,31],[2,3,4,5,7,10,12,13,32],[0]),([1,2,3,4,9,46],[0,2,3,4,11,33,34],[0]),([0,1,2,3,4,9,22],[0,4,11,35,36,37],[0,1]),([0,1,2,3,4,9,24],[0,3,10,11,36,39],[0]),([0,1,2,3,4,12],[0,1,2,3,4,10,11,12,13,40],[0]),([0,1,2,3,4,90],[0,1,2,3,4,10,12,13],[0,1]),([0,1,2,3,86],[0,2,12,35,36,41],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Test6_2 : checkNodesBT h3W h3G h3Mask h3Pools h3Autos h3Bucket5 6 h3Block6_2 = true := by decide +kernel
def h3Block6_3 : List NodeSpec := [([0,1,2,3,10,18],[1,2,13,42,43,44,45],[0]),([0,1,2,3,4,43],[0,1,2,3,4,10,11,12,13,36,46],[0,1]),([0,1,2,3,4,54],[0,1,3,4,10,12,13,36],[0,1]),([0,1,2,4,89],[0,2,4,10,36],[0]),([0,1,2,3,4,89],[0,1,2,4,10,12,13,36],[0]),([0,1,2,4,96],[0,2,4,11,48],[0]),([1,2,3,4,12,46],[0,2,3,4,8,11,33],[0,1]),([1,2,3,4,12,47],[0,2,3,4,8,11,52],[0]),([0,1,2,3,4,12,13],[0,1,3,36,53],[0]),([0,1,2,3,12,17],[1,2,8,12,36,40,50,51,54],[0]),([0,1,2,3,12,18],[1,2,13,40,43,44,45],[0]),([0,1,2,3,4,21],[0,1,2,3,4,10,11,12,13,55],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Test6_3 : checkNodesBT h3W h3G h3Mask h3Pools h3Autos h3Bucket5 6 h3Block6_3 = true := by decide +kernel
def h3Block6_4 : List NodeSpec := [([0,1,2,3,4,12,21],[0,1,3,4,55],[0]),([0,1,2,3,4,12,24],[0,3,10,11],[0]),([0,1,2,3,4,39],[0,1,3,4,10,12,13,56],[0,1]),([0,1,2,3,4,12,39],[0,3,4,11],[0]),([0,1,2,3,4,12,40],[0,3,4,10,11],[0]),([0,1,2,3,4,37],[1,3,10,12,13],[0]),([1,2,4,45,46],[0,2,3,33,57],[0]),([0,1,2,3,4,25,45],[0,11,12],[0,1]),([0,1,2,3,4,26,45],[0,4,12,13],[0]),([0,1,2,3,4,103],[0,1,2,4,11,12,13],[0]),([0,1,2,3,4,13,46],[0,1,2,3,4,7,10,11],[0]),([0,1,2,3,4,15,46],[0,2,3,4,7,10,11],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Test6_4 : checkNodesBT h3W h3G h3Mask h3Pools h3Autos h3Bucket5 6 h3Block6_4 = true := by decide +kernel
def h3Block6_5 : List NodeSpec := [([0,1,2,3,17,46],[1,2,7,12,33,50,51,54,59],[0,1]),([0,1,2,3,4,17,46],[0,1,2,3,10,11,12,13,59],[0]),([0,1,2,3,18,46],[1,2,7,13,33,43,44,45,59],[0,1]),([0,1,2,3,4,30],[0,1,2,3,4,5,6,7,10,11,12,13,61],[0,1]),([0,1,2,3,4,30,46],[0,1,2,3,6,10,11,33,61],[0]),([0,1,2,3,4,25,46],[3,4,12,13],[0]),([0,1,2,3,4,26,46],[0,3,4,10,11,12,13],[0]),([0,1,2,3,4,84],[0,1,3,4,10,11,12,13],[0]),([0,1,2,3,4,46,84],[0,3,4,10,11,59],[0]),([0,1,2,3,4,46,85],[0,3,4,10,11],[0]),([0,1,2,3,4,46,87],[12,13,59],[0]),([0,1,2,3,4,25,47],[0,10,11,12],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Test6_5 : checkNodesBT h3W h3G h3Mask h3Pools h3Autos h3Bucket5 6 h3Block6_5 = true := by decide +kernel
def h3Block6_6 : List NodeSpec := [([0,1,2,3,4,26,47],[0,4,12,13],[0]),([0,1,2,3,4,104],[0,1,2,3,4,10,12,13,63],[0]),([0,1,2,3,4,46],[0,1,2,3,4,10,11,12,13,33,59],[0]),([0,1,2,3,4,124],[0,1,2,4,10,12,13,36,59],[0]),([0,1,2,3,4,127],[0,2,3,4,10,11,12,13,36,64,65],[0]),([0,1,2,3,4,128],[0,1,3,4,10,12,13,36,66],[0,1]),([0,1,2,3,4,68],[0,1,2,3,4,10,11,12,13,19],[0]),([0,1,2,3,4,13,68],[0,1,2,3,53],[0]),([0,1,2,3,4,13,20],[0,2,3],[0]),([0,2,3,13,17],[1,2,7,13,36,51,67,69],[0,1]),([0,1,2,3,13,17],[1,2,7,12,13,36,50,51,54,67],[0]),([0,1,2,3,13,18],[1,2,7,12,13,36,43,44,45,67],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Test6_6 : checkNodesBT h3W h3G h3Mask h3Pools h3Autos h3Bucket5 6 h3Block6_6 = true := by decide +kernel
def h3Block6_7 : List NodeSpec := nodesWithIdentity [([1,2,3,4,130],[0,1,4,7,72]),([1,2,3,4,82],[1,2,3,4,7]),([0,1,2,3,131],[1,2,4,12,13,71]),([0,1,2,3,4,77],[0,1,2,3,4,10,11,12,13,22]),([0,1,2,3,15,18],[1,2,7,13,43,44,45,73]),([0,1,2,3,4,13],[0,1,3,4,10,11,12,13,36,53,67,75]),([0,2,3,16,17],[1,2,7,36,51,77]),([0,1,2,3,132],[1,2,7,12,13,76,78]),([0,1,2,3,17,78],[1,2,12,13,18,27,36,50,51,54]),([0,1,2,3,4,78],[0,1,2,3,4,10,11,12,13,18,27,36]),([0,1,2,3,17],[1,2,7,12,13,36,50,51,54]),([0,1,2,3,4,56],[0,1,3,4,10,11,12,13,36,79,80])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Test6_7 : checkNodesBT h3W h3G h3Mask h3Pools h3Autos h3Bucket5 6 h3Block6_7 = true := by decide +kernel
def h3Block6_8 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,57],[0,1,3,4,10,11,12,13,36,74,81]),([0,1,2,3,4,60],[0,1,3,4,10,11,12,13,82]),([0,1,2,3,4,62],[0,1,3,4,10,11,12,13,70])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Test6_8 : checkNodesBT h3W h3G h3Mask h3Pools h3Autos h3Bucket5 6 h3Block6_8 = true := by decide +kernel
def h3Nodes6 : List NodeSpec := h3Block6_0 ++ h3Block6_1 ++ h3Block6_2 ++ h3Block6_3 ++ h3Block6_4 ++ h3Block6_5 ++ h3Block6_6 ++ h3Block6_7 ++ h3Block6_8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Check6 : checkNodesBT h3W h3G h3Mask h3Pools h3Autos h3Bucket5 6 h3Nodes6 = true := by
  unfold h3Nodes6 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨h3Test6_0,h3Test6_1⟩,h3Test6_2⟩,h3Test6_3⟩,h3Test6_4⟩,h3Test6_5⟩,h3Test6_6⟩,h3Test6_7⟩,h3Test6_8⟩
def h3Bucket6 : BT (List (List Nat)) := buildBucketsBT h3W h3Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h3G 6 xs.toFinset) h3Bucket6 := buildBucketsBT_sound (by decide) h3Pairs h3WOk h3PoolsOk h3AutosOk h3Bucket5Ok h3Check6
def h3Block7_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,4,7,9,11,12,13],[0]),([0,1,2,3,4,6],[0,1,2,3,4,7,11,12,13,18],[0]),([0,1,2,3,4,7],[0,1,4,7,11,12,13,28],[0]),([0,1,2,3,4,8],[0,1,2,3,4,7,11,12,13,30],[0]),([0,1,2,3,4,9],[0,1,2,4,11,12,13,35,36],[0]),([0,1,2,3,4,10],[0,1,2,3,4,11,12,13,36,42],[0,1]),([0,1,2,3,4,11],[0,1,2,4,11,12,13,36,47],[0]),([0,1,2,3,4,12],[0,1,2,3,4,11,12,13,36,40],[0,1]),([0,1,2,3,4,45],[0,1,2,4,11,12,13,58],[0]),([0,1,2,3,4,46],[0,1,2,3,4,7,10,11,12,13,59],[0,1]),([0,1,2,3,4,47],[0,1,2,4,10,11,12,13,62],[0]),([0,1,2,3,4,48],[0,1,2,4,11,12,13,36],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Test7_0 : checkNodesBT h3W h3G h3Mask h3Pools h3Autos h3Bucket6 7 h3Block7_0 = true := by decide +kernel
def h3Block7_1 : List NodeSpec := [([0,1,2,3,4,49],[0,1,2,3,4,11,12,13,36],[0,1]),([0,1,2,3,4,13],[0,1,2,4,7,11,12,13,36,67],[0,1]),([0,1,2,3,4,14],[0,1,2,4,7,11,12,13,71],[0,1]),([0,1,2,3,4,15],[0,1,2,4,7,11,12,13,36,73],[0,1]),([0,1,2,3,4,16],[0,1,2,4,7,11,12,13,36,76],[0]),([0,1,2,3,17],[1,2,7,12,13,36],[0,1]),([0,1,2,3,4,17],[0,1,2,4,7,11,12,13,36],[0,1]),([0,1,2,3,18],[1,2,7,13],[0,1]),([0,1,2,3,4,19],[0,1,2,4,7,11,13,36],[0]),([0,1,2,3,4,25],[0,1,4,11,12,13,36],[0,1]),([0,1,2,3,4,26],[0,1,4,11,12,13],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Test7_1 : checkNodesBT h3W h3G h3Mask h3Pools h3Autos h3Bucket6 7 h3Block7_1 = true := by decide +kernel
def h3Nodes7 : List NodeSpec := h3Block7_0 ++ h3Block7_1
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Check7 : checkNodesBT h3W h3G h3Mask h3Pools h3Autos h3Bucket6 7 h3Nodes7 = true := by
  unfold h3Nodes7 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h3Test7_0,h3Test7_1⟩
def h3Bucket7 : BT (List (List Nat)) := buildBucketsBT h3W h3Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h3G 7 xs.toFinset) h3Bucket7 := buildBucketsBT_sound (by decide) h3Pairs h3WOk h3PoolsOk h3AutosOk h3Bucket6Ok h3Check7
def h3Block8_0 : List NodeSpec := [([0,1,2,3,4],[13],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Test8_0 : checkNodesBT h3W h3G h3Mask h3Pools h3Autos h3Bucket7 8 h3Block8_0 = true := by decide +kernel
def h3Nodes8 : List NodeSpec := h3Block8_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Check8 : checkNodesBT h3W h3G h3Mask h3Pools h3Autos h3Bucket7 8 h3Nodes8 = true := h3Test8_0
def h3Bucket8 : BT (List (List Nat)) := buildBucketsBT h3W h3Nodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h3G 8 xs.toFinset) h3Bucket8 := buildBucketsBT_sound (by decide) h3Pairs h3WOk h3PoolsOk h3AutosOk h3Bucket7Ok h3Check8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Bound : Lower h3R h3G 9 := lower_of_forestBT (essPairs := [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,5,13),(VAR 4,3,19)]) (by decide +kernel) h3Bucket8Ok (by decide +kernel)
def h13R : List Nat := varsOf 38
def h13G : Nat := 0xfcfcfcfcc0c0c0c0fcfcfcfcc0c0c0c0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13Bound : Lower h13R h13G 4 := carry_of (swaps := [(4,5),(1,2),(2,3)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h14R : List Nat := varsOf 39
def h14G : Nat := 0xa8a8a8a880808080a8a8a8a880808080
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14Bound : Lower h14R h14G 5 := carry_of (swaps := [(3,4),(4,5),(1,2),(0,1)]) (roots2 := h5R) (T2 := h5G) (by decide +kernel) h5Bound
def h15R : List Nat := varsOf 44
def h15G : Nat := 0xfff0fff0f000f000fff0fff0f000f000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Bound : Lower h15R h15G 4 := carry_of (swaps := [(4,5)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h16R : List Nat := varsOf 45
def h16G : Nat := 0xaaa0aaa0a000a000aaa0aaa0a000a000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Bound : Lower h16R h16G 5 := carry_of (swaps := [(3,4),(4,5),(1,2),(2,3),(0,1),(1,2)]) (roots2 := h5R) (T2 := h5G) (by decide +kernel) h5Bound
def h17R : List Nat := varsOf 15
def h17G : Nat := 0xeaa8eaa8eaa8eaa8eaa8eaa8eaa8eaa8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h17Bound : Lower h17R h17G 6 := carry_of (swaps := [(0,1)]) (roots2 := h9R) (T2 := h9G) (by decide +kernel) h9Bound
def h18R : List Nat := varsOf 43
def h18G : Nat := 0xeeaaeeaaee88ee88eeaaeeaaee88ee88
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18Bound : Lower h18R h18G 5 := carry_of (swaps := [(4,5),(0,1)]) (roots2 := h11R) (T2 := h11G) (by decide +kernel) h11Bound
def h19R : List Nat := varsOf 45
def h19G : Nat := 0xfaaafaaaf0a0f0a0faaafaaaf0a0f0a0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h19Bound : Lower h19R h19G 4 := carry_of (swaps := [(4,5),(0,1),(1,2),(2,3),(1,2)]) (roots2 := h10R) (T2 := h10G) (by decide +kernel) h10Bound
def h20R : List Nat := varsOf 46
def h20G : Nat := 0xfffcfffcf0c0f0c0fffcfffcf0c0f0c0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h20Bound : Lower h20R h20G 5 := carry_of (swaps := [(4,5),(0,1)]) (roots2 := h2R) (T2 := h2G) (by decide +kernel) h2Bound
def h21R : List Nat := varsOf 47
def h21G : Nat := 0xeaa8eaa8e080e080eaa8eaa8e080e080
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Bound : Lower h21R h21G 9 := carry_of (swaps := [(4,5),(0,1)]) (roots2 := h3R) (T2 := h3G) (by decide +kernel) h3Bound
def h23R : List Nat := varsOf 7
def h23G : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h23Bound : Lower h23R h23G 4 := carry_of (swaps := [(1,2),(2,3),(3,4),(0,1),(1,2),(2,3)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h22R : List Nat := varsOf 39
def h22G : Nat := 0xe8e8e8e8c8c8c8c8e8e8e8e8c8c8c8c8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Bound : Lower h22R h22G 5 := lift_of (z := 0) (o := 32) (essPairs := [(VAR 5,5,37)]) (by decide +kernel) h23Bound
def h24R : List Nat := varsOf 53
def h24G : Nat := 0xfafaaaaafafaa0a0fafaaaaafafaa0a0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h24Bound : Lower h24R h24G 5 := carry_of (swaps := [(4,5),(3,4),(0,1),(1,2)]) (roots2 := h11R) (T2 := h11G) (by decide +kernel) h11Bound
def h25R : List Nat := varsOf 54
def h25G : Nat := 0xfcfcfcfcccccc0c0fcfcfcfcccccc0c0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h25Bound : Lower h25R h25G 5 := carry_of (swaps := [(3,4),(4,5),(3,4),(0,1),(1,2),(0,1)]) (roots2 := h11R) (T2 := h11G) (by decide +kernel) h11Bound
def h27R : List Nat := varsOf 23
def h27G : Nat := 0xe8e8a8a8e8e8a8a8e8e8a8a8e8e8a8a8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27Bound : Lower h27R h27G 5 := carry_of (swaps := [(4,5),(0,1)]) (roots2 := h22R) (T2 := h22G) (by decide +kernel) h22Bound
def h28R : List Nat := varsOf 51
def h28G : Nat := 0xeeeeaaaacccc8888eeeeaaaacccc8888
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h28Bound : Lower h28R h28G 4 := carry_of (swaps := [(4,5),(0,1),(1,2),(2,3),(3,4)]) (roots2 := h10R) (T2 := h10G) (by decide +kernel) h10Bound
def h26R : List Nat := varsOf 55
def h26G : Nat := 0xe8e8a8a8c8c88080e8e8a8a8c8c88080
def h26Pos : List Nat := [22,37,22,22,19,53,35,22,53,54,19,7,35,7,19,53,54,7,35,54,35,19,37,23,7]
def h26Neg : List Nat := [20,36,21,18,3,21,3,6,49,50,21,6,38,5,18,52,52,3,33,38,34,17,33,21,2]
def h26Mask : Nat := fullMask 25
def h26Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x1f6fd72,0xe62574),(0xcccccccccccccccccccccccccccccccc,0x1bf7edd,0x11a5ad8),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x1cbabaf,0x89bca7),(0xffff0000ffff0000ffff0000ffff0000,0xa9c7bd,0xa1c72d),(0xffffffff00000000ffffffff00000000,0x5d9362,0x5d9302)]
def h26Steps : List (Nat × Nat × Nat) := [(0,0,1),(0,0,2),(0,1,2),(1,3,6),(0,5,6),(2,1,2),(2,1,3),(2,1,6),(2,2,5),(2,0,2),(0,0,4),(2,0,4),(1,6,11),(2,1,14)]
def h26W : BT Decor := buildWiresBT 5 h26Base h26Steps
def h26AutoList : List (List (Nat × Nat)) := [[],[(4,5),(0,1)]]
def h26Autos : BT (List (Nat × Nat)) := btOfList 1 h26AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Pairs : goodPairs h26G h26Pos h26Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26BaseOk : ∀ x ∈ h26Base, faithful h26Pos h26Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26WOk : btAll (fun x => faithful h26Pos h26Neg x ∧ x.1 < 2^128) h26W := buildWiresBT_faithful h26BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h26G = h26G) h26Autos := btAll_ofList (autos_of (by decide +kernel))
def h26SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,5),some (subcubeFast 0 2,5),some (subcubeFast 0 4,4),some (subcubeFast 0 16,5),some (subcubeFast 0 32,5),some (subcubeFast 0 48,4),some (subcubeFast 16 0,5),some (subcubeFast 16 1,4),some (subcubeFast 32 0,5),some (subcubeFast 32 2,4)]
def h26Slices : BT (Option (Nat × Nat)) := btOfList 4 h26SliceList
def h26Specs : List PoolSpec := [(0,[]),(1,[]),(7,[]),(9,[]),(8,[(0,0,1)]),(6,[(0,0,1)]),(3,[]),(6,[]),(4,[]),(8,[]),(2,[]),(6,[(0,0,2)]),(6,[(2,0,2)]),(1,[(0,0,4)]),(6,[(0,0,4)]),(3,[(0,0,4)]),(1,[(2,0,4)]),(6,[(2,0,4)]),(5,[]),(3,[(2,0,4)])]
def h26Pools : BT (Option BoundPool) := buildPoolsBT 5 h26W h26R h26Slices h26Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Slice9 : Slice h26R h26G (subcubeFast 32 2) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h6Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Slice8 : Slice h26R h26G (subcubeFast 32 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h7Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Slice7 : Slice h26R h26G (subcubeFast 16 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h13Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Slice6 : Slice h26R h26G (subcubeFast 16 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h14Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Slice5 : Slice h26R h26G (subcubeFast 0 48) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h23Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Slice4 : Slice h26R h26G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h27Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Slice3 : Slice h26R h26G (subcubeFast 0 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h22Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Slice2 : Slice h26R h26G (subcubeFast 0 4) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h28Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Slice1 : Slice h26R h26G (subcubeFast 0 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h24Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Slice0 : Slice h26R h26G (subcubeFast 0 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h25Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h26R h26G p.1 p.2) h26Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h26R h26G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h26Slice0) (forall_cons (fun _ h => by cases h; exact h26Slice1) (forall_cons (fun _ h => by cases h; exact h26Slice2) (forall_cons (fun _ h => by cases h; exact h26Slice3) (forall_cons (fun _ h => by cases h; exact h26Slice4) (forall_cons (fun _ h => by cases h; exact h26Slice5) (forall_cons (fun _ h => by cases h; exact h26Slice6) (forall_cons (fun _ h => by cases h; exact h26Slice7) (forall_cons (fun _ h => by cases h; exact h26Slice8) (forall_cons (fun _ h => by cases h; exact h26Slice9) (fun _ h => (List.not_mem_nil h).elim)))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h26R h26G c) h26Pools := buildPoolsBT_sound h26SlicesOk
def h26Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h26G (4 - 1) xs.toFinset) h26Empty := trivial
def h26Block4_0 : List NodeSpec := nodesWithIdentity [([3,4,5,6,7],[]),([0,1,2,4,17],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test4_0 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Empty 4 h26Block4_0 = true := by decide +kernel
def h26Nodes4 : List NodeSpec := h26Block4_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Check4 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Empty 4 h26Nodes4 = true := h26Test4_0
def h26Bucket4 : BT (List (List Nat)) := buildBucketsBT h26W h26Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h26G 4 xs.toFinset) h26Bucket4 := buildBucketsBT_sound (by decide) h26Pairs h26WOk h26PoolsOk h26AutosOk h26EmptyOk h26Check4
def h26Block5_0 : List NodeSpec := nodesWithIdentity [([1,2,3,4,5,6],[1,2]),([0,1,2,3,4,9],[6,7,8,9]),([0,1,2,3,4,13],[]),([0,1,3,4,6,7],[0]),([0,1,3,4,6,10],[]),([0,1,2,4,6,11],[6]),([0,1,2,3,4,12],[6,7]),([0,1,2,4,6,8],[7]),([0,1,2,4,11,14],[]),([0,1,2,3,4,18],[8,9])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test5_0 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket4 5 h26Block5_0 = true := by decide +kernel
def h26Nodes5 : List NodeSpec := h26Block5_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Check5 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket4 5 h26Nodes5 = true := h26Test5_0
def h26Bucket5 : BT (List (List Nat)) := buildBucketsBT h26W h26Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h26G 5 xs.toFinset) h26Bucket5 := buildBucketsBT_sound (by decide) h26Pairs h26WOk h26PoolsOk h26AutosOk h26Bucket4Ok h26Check5
def h26Block6_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,4,5,6,7,8,9,10],[0,1]),([0,1,2,3,4,6],[0,1,2,6,7,8,9,10,11],[0]),([0,1,2,3,4,14],[0,1,2,6,7,8,9,10,12],[0,1]),([0,1,2,3,15],[0,2,3,9,13,14,15],[0]),([0,1,2,3,16],[0,2,8,9,16,17,18,19],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test6_0 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket5 6 h26Block6_0 = true := by decide +kernel
def h26Nodes6 : List NodeSpec := h26Block6_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Check6 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket5 6 h26Nodes6 = true := h26Test6_0
def h26Bucket6 : BT (List (List Nat)) := buildBucketsBT h26W h26Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h26G 6 xs.toFinset) h26Bucket6 := buildBucketsBT_sound (by decide) h26Pairs h26WOk h26PoolsOk h26AutosOk h26Bucket5Ok h26Check6
def h26Block7_0 : List NodeSpec := [([0,1,2,3,4],[0,1,6,7,8,9],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test7_0 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket6 7 h26Block7_0 = true := by decide +kernel
def h26Nodes7 : List NodeSpec := h26Block7_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Check7 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket6 7 h26Nodes7 = true := h26Test7_0
def h26Bucket7 : BT (List (List Nat)) := buildBucketsBT h26W h26Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h26G 7 xs.toFinset) h26Bucket7 := buildBucketsBT_sound (by decide) h26Pairs h26WOk h26PoolsOk h26AutosOk h26Bucket6Ok h26Check7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Bound : Lower h26R h26G 8 := lower_of_forestBT (essPairs := [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 4,3,19),(VAR 5,3,35)]) (by decide +kernel) h26Bucket7Ok (by decide +kernel)
def h29R : List Nat := varsOf 27
def h29G : Nat := 0xee88aa88ee88aa88ee88aa88ee88aa88
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Bound : Lower h29R h29G 5 := carry_of (swaps := [(4,5),(2,3),(0,1)]) (roots2 := h22R) (T2 := h22G) (by decide +kernel) h22Bound
def h30R : List Nat := varsOf 43
def h30G : Nat := 0xee88ee88cc88cc88ee88ee88cc88cc88
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h30Bound : Lower h30R h30G 5 := carry_of (swaps := [(2,3)]) (roots2 := h22R) (T2 := h22G) (by decide +kernel) h22Bound
def h31R : List Nat := varsOf 57
def h31G : Nat := 0xffaaaaaaffaa0000ffaaaaaaffaa0000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Bound : Lower h31R h31G 4 := carry_of (swaps := [(4,5),(2,3),(3,4),(0,1),(1,2),(2,3)]) (roots2 := h10R) (T2 := h10G) (by decide +kernel) h10Bound
def h32R : List Nat := varsOf 58
def h32G : Nat := 0xffccffcccccc0000ffccffcccccc0000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h32Bound : Lower h32R h32G 4 := carry_of (swaps := [(2,3),(3,4),(4,5),(3,4),(0,1),(1,2),(2,3),(0,1)]) (roots2 := h10R) (T2 := h10G) (by decide +kernel) h10Bound
def h33R : List Nat := varsOf 59
def h33G : Nat := 0xee88aa88cc880000ee88aa88cc880000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Bound : Lower h33R h33G 6 := lift_of (z := 0) (o := 48) (essPairs := [(VAR 4,3,19),(VAR 5,3,35)]) (by decide +kernel) h4Bound
def h34R : List Nat := varsOf 29
def h34G : Nat := 0xfaa0aaa0faa0aaa0faa0aaa0faa0aaa0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34Bound : Lower h34R h34G 5 := carry_of (swaps := [(4,5),(2,3),(0,1),(1,2)]) (roots2 := h22R) (T2 := h22G) (by decide +kernel) h22Bound
def h35R : List Nat := varsOf 41
def h35G : Nat := 0xffaaffaaaa00aa00ffaaffaaaa00aa00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Bound : Lower h35R h35G 4 := carry_of (swaps := [(4,5),(1,2),(0,1)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
namespace Cofactor12058
def G_0 : Nat := 0xfffff0f0f0f00000fffff0f0f0f00000
def R_0 : List Nat := varsOf 52
def pos_0 : List Nat := [20,20,36,36,48,48,20,36,48]
def neg_0 : List Nat := [16,4,32,4,32,16,32,16,4]
def fmask_0 : Nat := fullMask 9
def base_0 : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xcf,0x10a),(0xffff0000ffff0000ffff0000ffff0000,0x173,0xa1),(0xffffffff00000000ffffffff00000000,0x1bc,0x54)]
def steps_0 : List (Nat × Nat × Nat) := []
def W_0 : BT Decor := buildWiresBT 2 base_0 steps_0
def autosL_0 : List (List (Nat × Nat)) := []
def autos_0 : BT (List (Nat × Nat)) := btOfList 1 autosL_0
def slicesL_0 : List (Option (Nat × Nat)) := []
def slices_0 : BT (Option (Nat × Nat)) := btOfList 1 slicesL_0
def ps_0 : List PoolSpec := []
def P_0 : BT (Option BoundPool) := buildPoolsBT 1 W_0 R_0 slices_0 ps_0
lemma gp_0 : goodPairs G_0 pos_0 neg_0 := goodPairs_of (by decide +kernel)
lemma base_0_ok : ∀ x ∈ base_0, faithful pos_0 neg_0 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_0_ok : btAll (fun x => faithful pos_0 neg_0 x ∧ x.1 < 2^128) W_0 := buildWiresBT_faithful base_0_ok
set_option maxRecDepth 500000 in
lemma autos_0_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_0 = G_0) autos_0 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma slices_0_ok : btAll (fun o => ∀ p, o = some p → Slice R_0 G_0 p.1 p.2) slices_0 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_0 G_0 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 500000 in
lemma P_0_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_0 G_0 c) P_0 := buildPoolsBT_sound slices_0_ok
def bk_0_init : BT (List (List Nat)) := BT.empty
lemma bk_0_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 (0 - 1) xs.toFinset) bk_0_init := trivial
def nodes_0_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_0 : checkNodesBT W_0 G_0 fmask_0 P_0 autos_0 bk_0_init 0 nodes_0_0 = true := by decide +kernel
def bk_0_0 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_0
set_option maxRecDepth 500000 in
lemma bk_0_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 0 xs.toFinset) bk_0_0 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_init_ok chk_0_0
def nodes_0_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_1 : checkNodesBT W_0 G_0 fmask_0 P_0 autos_0 bk_0_0 1 nodes_0_1 = true := by decide +kernel
def bk_0_1 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_1
set_option maxRecDepth 500000 in
lemma bk_0_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 1 xs.toFinset) bk_0_1 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_0_ok chk_0_1
def nodes_0_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_2 : checkNodesBT W_0 G_0 fmask_0 P_0 autos_0 bk_0_1 2 nodes_0_2 = true := by decide +kernel
def bk_0_2 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_2
set_option maxRecDepth 500000 in
lemma bk_0_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 2 xs.toFinset) bk_0_2 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_1_ok chk_0_2
def nodes_0_3 : List NodeSpec := [([0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_3 : checkNodesBT W_0 G_0 fmask_0 P_0 autos_0 bk_0_2 3 nodes_0_3 = true := by decide +kernel
def bk_0_3 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_3
set_option maxRecDepth 500000 in
lemma bk_0_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 3 xs.toFinset) bk_0_3 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_2_ok chk_0_3
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_0_ok : forestRootCheck R_0 G_0 [(VAR 2,20,16),(VAR 4,20,4),(VAR 5,36,4)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_0_in : bucketContainsBT bk_0_3 R_0 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_0 : Lower R_0 G_0 4 := lower_of_forestBT root_0_ok bk_0_3_ok root_0_in

def G_6 : Nat := 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0
def R_6 : List Nat := varsOf 22
lemma low_6_ok : carryOK [(3,5),(1,3),(1,4),(1,2)] R_6 G_6 R_0 G_0 = true := by decide +kernel
lemma low_6 : Lower R_6 G_6 4 := carry_of low_6_ok low_0

def G_7 : Nat := 0xfcfcfcfcc0c0c0c0fcfcfcfcc0c0c0c0
def R_7 : List Nat := varsOf 38
lemma low_7_ok : carryOK [(1,3),(1,4),(1,2)] R_7 G_7 R_0 G_0 = true := by decide +kernel
lemma low_7 : Lower R_7 G_7 4 := carry_of low_7_ok low_0

def G_9 : Nat := 0xffffcccccccc0000ffffcccccccc0000
def R_9 : List Nat := varsOf 50
lemma low_9_ok : carryOK [(1,2)] R_9 G_9 R_0 G_0 = true := by decide +kernel
lemma low_9 : Lower R_9 G_9 4 := carry_of low_9_ok low_0

def G_10 : Nat := 0xfcfcc0c0c0c00000fcfcc0c0c0c00000
def R_10 : List Nat := varsOf 54
def pos_10 : List Nat := [22,22,22,38,38,38,50,50,50,52,52,52,22,22,22,38,38,38,50,50,50,52,52,52]
def neg_10 : List Nat := [20,18,6,36,34,6,48,34,18,48,36,20,34,36,48,18,20,48,6,20,36,6,18,34]
def fmask_10 : Nat := fullMask 24
def base_10 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0x1ff1ff,0xe491b6),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xe3fe3f,0x3d2c2d),(0xffff0000ffff0000ffff0000ffff0000,0xfc7fc7,0x4bcb43),(0xffffffff00000000ffffffff00000000,0xff8ff8,0x9276d8)]
def steps_10 : List (Nat × Nat × Nat) := [(0,0,1),(3,4,2),(0,0,2),(0,4,2),(0,1,2),(3,7,3)]
def W_10 : BT Decor := buildWiresBT 4 base_10 steps_10
def autosL_10 : List (List (Nat × Nat)) := [[],[(4,5)],[(1,2)],[(4,5),(1,2)],[(2,4)],[(2,5),(2,4)],[(1,2),(1,4)],[(2,5),(1,2),(1,4)],[(2,5),(1,4)]]
def autos_10 : BT (List (Nat × Nat)) := btOfList 4 autosL_10
def slicesL_10 : List (Option (Nat × Nat)) := [some (subcubeFast 0 16,4),some (subcubeFast 0 2,4),some (subcubeFast 0 4,4),some (subcubeFast 0 32,4)]
def slices_10 : BT (Option (Nat × Nat)) := btOfList 2 slicesL_10
def ps_10 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[])]
def P_10 : BT (Option BoundPool) := buildPoolsBT 2 W_10 R_10 slices_10 ps_10
lemma gp_10 : goodPairs G_10 pos_10 neg_10 := goodPairs_of (by decide +kernel)
lemma base_10_ok : ∀ x ∈ base_10, faithful pos_10 neg_10 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_10_ok : btAll (fun x => faithful pos_10 neg_10 x ∧ x.1 < 2^128) W_10 := buildWiresBT_faithful base_10_ok
set_option maxRecDepth 500000 in
lemma autos_10_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_10 = G_10) autos_10 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_10_0_ok : sliceDirectCheck 0 16 0 R_10 G_10 R_7 G_7 = true := by decide +kernel
lemma sl_10_0 : Slice R_10 G_10 (subcubeFast 0 16) 4 := slice_fast_direct sl_10_0_ok low_7
lemma sl_10_1_ok : sliceDirectCheck 0 2 0 R_10 G_10 R_0 G_0 = true := by decide +kernel
lemma sl_10_1 : Slice R_10 G_10 (subcubeFast 0 2) 4 := slice_fast_direct sl_10_1_ok low_0
lemma sl_10_2_ok : sliceDirectCheck 0 4 0 R_10 G_10 R_9 G_9 = true := by decide +kernel
lemma sl_10_2 : Slice R_10 G_10 (subcubeFast 0 4) 4 := slice_fast_direct sl_10_2_ok low_9
lemma sl_10_3_ok : sliceDirectCheck 0 32 0 R_10 G_10 R_6 G_6 = true := by decide +kernel
lemma sl_10_3 : Slice R_10 G_10 (subcubeFast 0 32) 4 := slice_fast_direct sl_10_3_ok low_6
set_option maxRecDepth 500000 in
lemma slices_10_ok : btAll (fun o => ∀ p, o = some p → Slice R_10 G_10 p.1 p.2) slices_10 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_10 G_10 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_10_0) (forall_cons (fun _ h => by cases h; exact sl_10_1) (forall_cons (fun _ h => by cases h; exact sl_10_2) (forall_cons (fun _ h => by cases h; exact sl_10_3) (fun _ h => (List.not_mem_nil h).elim)))))
set_option maxRecDepth 500000 in
lemma P_10_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_10 G_10 c) P_10 := buildPoolsBT_sound slices_10_ok
def bk_10_init : BT (List (List Nat)) := BT.empty
lemma bk_10_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_10 (0 - 1) xs.toFinset) bk_10_init := trivial
def nodes_10_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_10_0 : checkNodesBT W_10 G_10 fmask_10 P_10 autos_10 bk_10_init 0 nodes_10_0 = true := by decide +kernel
def bk_10_0 : BT (List (List Nat)) := buildBucketsBT W_10 nodes_10_0
set_option maxRecDepth 500000 in
lemma bk_10_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_10 0 xs.toFinset) bk_10_0 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok P_10_ok autos_10_ok bk_10_init_ok chk_10_0
def nodes_10_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_10_1 : checkNodesBT W_10 G_10 fmask_10 P_10 autos_10 bk_10_0 1 nodes_10_1 = true := by decide +kernel
def bk_10_1 : BT (List (List Nat)) := buildBucketsBT W_10 nodes_10_1
set_option maxRecDepth 500000 in
lemma bk_10_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_10 1 xs.toFinset) bk_10_1 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok P_10_ok autos_10_ok bk_10_0_ok chk_10_1
def nodes_10_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_10_2 : checkNodesBT W_10 G_10 fmask_10 P_10 autos_10 bk_10_1 2 nodes_10_2 = true := by decide +kernel
def bk_10_2 : BT (List (List Nat)) := buildBucketsBT W_10 nodes_10_2
set_option maxRecDepth 500000 in
lemma bk_10_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_10 2 xs.toFinset) bk_10_2 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok P_10_ok autos_10_ok bk_10_1_ok chk_10_2
def nodes_10_3 : List NodeSpec := [([4,6,8,3],[0,1],[]),([9,0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_10_3 : checkNodesBT W_10 G_10 fmask_10 P_10 autos_10 bk_10_2 3 nodes_10_3 = true := by decide +kernel
def bk_10_3 : BT (List (List Nat)) := buildBucketsBT W_10 nodes_10_3
set_option maxRecDepth 500000 in
lemma bk_10_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_10 3 xs.toFinset) bk_10_3 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok P_10_ok autos_10_ok bk_10_2_ok chk_10_3
def nodes_10_4 : List NodeSpec := [([5,0,1,2,3],[],[]),([4,6,1,2,3],[0,2],[0]),([7,0,1,2,3],[3],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_10_4 : checkNodesBT W_10 G_10 fmask_10 P_10 autos_10 bk_10_3 4 nodes_10_4 = true := by decide +kernel
def bk_10_4 : BT (List (List Nat)) := buildBucketsBT W_10 nodes_10_4
set_option maxRecDepth 500000 in
lemma bk_10_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_10 4 xs.toFinset) bk_10_4 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok P_10_ok autos_10_ok bk_10_3_ok chk_10_4
def nodes_10_5 : List NodeSpec := [([4,0,1,2,3],[2,1,0,3],[0,1,2,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_10_5 : checkNodesBT W_10 G_10 fmask_10 P_10 autos_10 bk_10_4 5 nodes_10_5 = true := by decide +kernel
def bk_10_5 : BT (List (List Nat)) := buildBucketsBT W_10 nodes_10_5
set_option maxRecDepth 500000 in
lemma bk_10_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_10 5 xs.toFinset) bk_10_5 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok P_10_ok autos_10_ok bk_10_4_ok chk_10_5
def nodes_10_6 : List NodeSpec := [([0,1,2,3],[1,2,0,3],[0,4,5,6,7,8])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_10_6 : checkNodesBT W_10 G_10 fmask_10 P_10 autos_10 bk_10_5 6 nodes_10_6 = true := by decide +kernel
def bk_10_6 : BT (List (List Nat)) := buildBucketsBT W_10 nodes_10_6
set_option maxRecDepth 500000 in
lemma bk_10_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_10 6 xs.toFinset) bk_10_6 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok P_10_ok autos_10_ok bk_10_5_ok chk_10_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_10_ok : forestRootCheck R_10 G_10 [(VAR 1,22,20),(VAR 2,22,18),(VAR 4,22,6),(VAR 5,38,6)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_10_in : bucketContainsBT bk_10_6 R_10 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_10 : Lower R_10 G_10 7 := lower_of_forestBT root_10_ok bk_10_6_ok root_10_in

end Cofactor12058
def h36R : List Nat := varsOf 45
def h36G : Nat := 0xfaa0faa0a000a000faa0faa0a000a000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h36Bound : Lower h36R h36G 7 := carry_of (swaps := [(3,4),(0,1)]) (roots2 := Cofactor12058.R_10) (T2 := Cofactor12058.G_10) (by decide +kernel) Cofactor12058.low_10
def h37R : List Nat := varsOf 53
def h37G : Nat := 0xfafaaaaaa0a0a0a0fafaaaaaa0a0a0a0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Bound : Lower h37R h37G 5 := carry_of (swaps := [(2,3),(3,4),(4,5),(0,1),(1,2)]) (roots2 := h22R) (T2 := h22G) (by decide +kernel) h22Bound
def h38R : List Nat := varsOf 57
def h38G : Nat := 0xffaaaaaaaa00aa00ffaaaaaaaa00aa00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38Bound : Lower h38R h38G 5 := carry_of (swaps := [(2,3),(3,4),(4,5),(0,1),(1,2),(2,3)]) (roots2 := h22R) (T2 := h22G) (by decide +kernel) h22Bound
namespace Cofactor12116
def G_0 : Nat := 0xfff0fff0f000f000fff0fff0f000f000
def R_0 : List Nat := varsOf 44
def pos_0 : List Nat := [12,12,36,36,40,40,12,36,40]
def neg_0 : List Nat := [8,4,32,4,32,8,32,8,4]
def fmask_0 : Nat := fullMask 9
def base_0 : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xcf,0x10a),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x173,0xa1),(0xffffffff00000000ffffffff00000000,0x1bc,0x54)]
def steps_0 : List (Nat × Nat × Nat) := []
def W_0 : BT Decor := buildWiresBT 2 base_0 steps_0
def autosL_0 : List (List (Nat × Nat)) := []
def autos_0 : BT (List (Nat × Nat)) := btOfList 1 autosL_0
def slicesL_0 : List (Option (Nat × Nat)) := []
def slices_0 : BT (Option (Nat × Nat)) := btOfList 1 slicesL_0
def ps_0 : List PoolSpec := []
def P_0 : BT (Option BoundPool) := buildPoolsBT 1 W_0 R_0 slices_0 ps_0
lemma gp_0 : goodPairs G_0 pos_0 neg_0 := goodPairs_of (by decide +kernel)
lemma base_0_ok : ∀ x ∈ base_0, faithful pos_0 neg_0 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_0_ok : btAll (fun x => faithful pos_0 neg_0 x ∧ x.1 < 2^128) W_0 := buildWiresBT_faithful base_0_ok
set_option maxRecDepth 500000 in
lemma autos_0_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_0 = G_0) autos_0 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma slices_0_ok : btAll (fun o => ∀ p, o = some p → Slice R_0 G_0 p.1 p.2) slices_0 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_0 G_0 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 500000 in
lemma P_0_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_0 G_0 c) P_0 := buildPoolsBT_sound slices_0_ok
def bk_0_init : BT (List (List Nat)) := BT.empty
lemma bk_0_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 (0 - 1) xs.toFinset) bk_0_init := trivial
def nodes_0_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_0 : checkNodesBT W_0 G_0 fmask_0 P_0 autos_0 bk_0_init 0 nodes_0_0 = true := by decide +kernel
def bk_0_0 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_0
set_option maxRecDepth 500000 in
lemma bk_0_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 0 xs.toFinset) bk_0_0 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_init_ok chk_0_0
def nodes_0_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_1 : checkNodesBT W_0 G_0 fmask_0 P_0 autos_0 bk_0_0 1 nodes_0_1 = true := by decide +kernel
def bk_0_1 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_1
set_option maxRecDepth 500000 in
lemma bk_0_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 1 xs.toFinset) bk_0_1 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_0_ok chk_0_1
def nodes_0_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_2 : checkNodesBT W_0 G_0 fmask_0 P_0 autos_0 bk_0_1 2 nodes_0_2 = true := by decide +kernel
def bk_0_2 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_2
set_option maxRecDepth 500000 in
lemma bk_0_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 2 xs.toFinset) bk_0_2 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_1_ok chk_0_2
def nodes_0_3 : List NodeSpec := [([0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_3 : checkNodesBT W_0 G_0 fmask_0 P_0 autos_0 bk_0_2 3 nodes_0_3 = true := by decide +kernel
def bk_0_3 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_3
set_option maxRecDepth 500000 in
lemma bk_0_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 3 xs.toFinset) bk_0_3 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_2_ok chk_0_3
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_0_ok : forestRootCheck R_0 G_0 [(VAR 2,12,8),(VAR 3,12,4),(VAR 5,36,4)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_0_in : bucketContainsBT bk_0_3 R_0 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_0 : Lower R_0 G_0 4 := lower_of_forestBT root_0_ok bk_0_3_ok root_0_in

def G_8 : Nat := 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0
def R_8 : List Nat := varsOf 14
lemma low_8_ok : carryOK [(1,4),(1,5),(1,3),(1,2)] R_8 G_8 R_0 G_0 = true := by decide +kernel
lemma low_8 : Lower R_8 G_8 4 := carry_of low_8_ok low_0

def G_10 : Nat := 0xfcfcfcfcc0c0c0c0fcfcfcfcc0c0c0c0
def R_10 : List Nat := varsOf 38
lemma low_10_ok : carryOK [(1,3),(1,2)] R_10 G_10 R_0 G_0 = true := by decide +kernel
lemma low_10 : Lower R_10 G_10 4 := carry_of low_10_ok low_0

def G_14 : Nat := 0xffccffcccc00cc00ffccffcccc00cc00
def R_14 : List Nat := varsOf 42
lemma low_14_ok : carryOK [(1,2)] R_14 G_14 R_0 G_0 = true := by decide +kernel
lemma low_14 : Lower R_14 G_14 4 := carry_of low_14_ok low_0

def G_20 : Nat := 0xfcc0fcc0c000c000fcc0fcc0c000c000
def R_20 : List Nat := varsOf 46
def pos_20 : List Nat := [14,14,14,38,38,38,42,42,42,44,44,44,14,14,14,38,38,38,42,42,42,44,44,44]
def neg_20 : List Nat := [12,10,6,36,34,6,40,34,10,40,36,12,34,36,40,10,12,40,6,12,36,6,10,34]
def fmask_20 : Nat := fullMask 24
def base_20 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0x1ff1ff,0xe491b6),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xe3fe3f,0x3d2c2d),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xfc7fc7,0x4bcb43),(0xffffffff00000000ffffffff00000000,0xff8ff8,0x9276d8)]
def steps_20 : List (Nat × Nat × Nat) := [(0,0,1),(0,0,2),(3,4,2),(0,4,2),(0,1,2),(3,7,3)]
def W_20 : BT Decor := buildWiresBT 4 base_20 steps_20
def autosL_20 : List (List (Nat × Nat)) := [[],[(3,5)],[(1,2)],[(3,5),(1,2)],[(2,3)],[(2,5),(2,3)],[(1,2),(1,3)],[(2,5),(1,2),(1,3)],[(2,5),(1,3)]]
def autos_20 : BT (List (Nat × Nat)) := btOfList 4 autosL_20
def slicesL_20 : List (Option (Nat × Nat)) := [some (subcubeFast 0 8,4),some (subcubeFast 0 2,4),some (subcubeFast 0 4,4),some (subcubeFast 0 32,4)]
def slices_20 : BT (Option (Nat × Nat)) := btOfList 2 slicesL_20
def ps_20 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[])]
def P_20 : BT (Option BoundPool) := buildPoolsBT 2 W_20 R_20 slices_20 ps_20
lemma gp_20 : goodPairs G_20 pos_20 neg_20 := goodPairs_of (by decide +kernel)
lemma base_20_ok : ∀ x ∈ base_20, faithful pos_20 neg_20 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_20_ok : btAll (fun x => faithful pos_20 neg_20 x ∧ x.1 < 2^128) W_20 := buildWiresBT_faithful base_20_ok
set_option maxRecDepth 500000 in
lemma autos_20_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_20 = G_20) autos_20 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_20_0_ok : sliceDirectCheck 0 8 0 R_20 G_20 R_10 G_10 = true := by decide +kernel
lemma sl_20_0 : Slice R_20 G_20 (subcubeFast 0 8) 4 := slice_fast_direct sl_20_0_ok low_10
lemma sl_20_1_ok : sliceDirectCheck 0 2 0 R_20 G_20 R_0 G_0 = true := by decide +kernel
lemma sl_20_1 : Slice R_20 G_20 (subcubeFast 0 2) 4 := slice_fast_direct sl_20_1_ok low_0
lemma sl_20_2_ok : sliceDirectCheck 0 4 0 R_20 G_20 R_14 G_14 = true := by decide +kernel
lemma sl_20_2 : Slice R_20 G_20 (subcubeFast 0 4) 4 := slice_fast_direct sl_20_2_ok low_14
lemma sl_20_3_ok : sliceDirectCheck 0 32 0 R_20 G_20 R_8 G_8 = true := by decide +kernel
lemma sl_20_3 : Slice R_20 G_20 (subcubeFast 0 32) 4 := slice_fast_direct sl_20_3_ok low_8
set_option maxRecDepth 500000 in
lemma slices_20_ok : btAll (fun o => ∀ p, o = some p → Slice R_20 G_20 p.1 p.2) slices_20 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_20 G_20 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_20_0) (forall_cons (fun _ h => by cases h; exact sl_20_1) (forall_cons (fun _ h => by cases h; exact sl_20_2) (forall_cons (fun _ h => by cases h; exact sl_20_3) (fun _ h => (List.not_mem_nil h).elim)))))
set_option maxRecDepth 500000 in
lemma P_20_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_20 G_20 c) P_20 := buildPoolsBT_sound slices_20_ok
def bk_20_init : BT (List (List Nat)) := BT.empty
lemma bk_20_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_20 (0 - 1) xs.toFinset) bk_20_init := trivial
def nodes_20_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_20_0 : checkNodesBT W_20 G_20 fmask_20 P_20 autos_20 bk_20_init 0 nodes_20_0 = true := by decide +kernel
def bk_20_0 : BT (List (List Nat)) := buildBucketsBT W_20 nodes_20_0
set_option maxRecDepth 500000 in
lemma bk_20_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_20 0 xs.toFinset) bk_20_0 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok P_20_ok autos_20_ok bk_20_init_ok chk_20_0
def nodes_20_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_20_1 : checkNodesBT W_20 G_20 fmask_20 P_20 autos_20 bk_20_0 1 nodes_20_1 = true := by decide +kernel
def bk_20_1 : BT (List (List Nat)) := buildBucketsBT W_20 nodes_20_1
set_option maxRecDepth 500000 in
lemma bk_20_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_20 1 xs.toFinset) bk_20_1 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok P_20_ok autos_20_ok bk_20_0_ok chk_20_1
def nodes_20_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_20_2 : checkNodesBT W_20 G_20 fmask_20 P_20 autos_20 bk_20_1 2 nodes_20_2 = true := by decide +kernel
def bk_20_2 : BT (List (List Nat)) := buildBucketsBT W_20 nodes_20_2
set_option maxRecDepth 500000 in
lemma bk_20_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_20 2 xs.toFinset) bk_20_2 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok P_20_ok autos_20_ok bk_20_1_ok chk_20_2
def nodes_20_3 : List NodeSpec := [([4,5,8,3],[0,1],[]),([9,0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_20_3 : checkNodesBT W_20 G_20 fmask_20 P_20 autos_20 bk_20_2 3 nodes_20_3 = true := by decide +kernel
def bk_20_3 : BT (List (List Nat)) := buildBucketsBT W_20 nodes_20_3
set_option maxRecDepth 500000 in
lemma bk_20_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_20 3 xs.toFinset) bk_20_3 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok P_20_ok autos_20_ok bk_20_2_ok chk_20_3
def nodes_20_4 : List NodeSpec := [([4,5,1,2,3],[0,2],[0]),([6,0,1,2,3],[],[]),([7,0,1,2,3],[3],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_20_4 : checkNodesBT W_20 G_20 fmask_20 P_20 autos_20 bk_20_3 4 nodes_20_4 = true := by decide +kernel
def bk_20_4 : BT (List (List Nat)) := buildBucketsBT W_20 nodes_20_4
set_option maxRecDepth 500000 in
lemma bk_20_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_20 4 xs.toFinset) bk_20_4 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok P_20_ok autos_20_ok bk_20_3_ok chk_20_4
def nodes_20_5 : List NodeSpec := [([4,0,1,2,3],[2,1,0,3],[0,1,2,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_20_5 : checkNodesBT W_20 G_20 fmask_20 P_20 autos_20 bk_20_4 5 nodes_20_5 = true := by decide +kernel
def bk_20_5 : BT (List (List Nat)) := buildBucketsBT W_20 nodes_20_5
set_option maxRecDepth 500000 in
lemma bk_20_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_20 5 xs.toFinset) bk_20_5 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok P_20_ok autos_20_ok bk_20_4_ok chk_20_5
def nodes_20_6 : List NodeSpec := [([0,1,2,3],[1,2,0,3],[0,4,5,6,7,8])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_20_6 : checkNodesBT W_20 G_20 fmask_20 P_20 autos_20 bk_20_5 6 nodes_20_6 = true := by decide +kernel
def bk_20_6 : BT (List (List Nat)) := buildBucketsBT W_20 nodes_20_6
set_option maxRecDepth 500000 in
lemma bk_20_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_20 6 xs.toFinset) bk_20_6 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok P_20_ok autos_20_ok bk_20_5_ok chk_20_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_20_ok : forestRootCheck R_20 G_20 [(VAR 1,14,12),(VAR 2,14,10),(VAR 3,14,6),(VAR 5,38,6)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_20_in : bucketContainsBT bk_20_6 R_20 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_20 : Lower R_20 G_20 7 := lower_of_forestBT root_20_ok bk_20_6_ok root_20_in

def G_25 : Nat := 0xe880e880e880e880e880e880e880e880
def R_25 : List Nat := varsOf 15
lemma low_25_ok : carryOK [(0,4),(0,5),(0,3),(0,2),(0,1)] R_25 G_25 R_20 G_20 = true := by decide +kernel
lemma low_25 : Lower R_25 G_25 7 := carry_of low_25_ok low_20

def G_55 : Nat := 0xe880e880e800e800e880e880e800e800
def R_55 : List Nat := varsOf 47
lemma low_55_ok : liftCheck 0 32 R_55 G_55 R_25 G_25 [(VAR 5,39,7)] = true := by decide +kernel
lemma low_55 : Lower R_55 G_55 8 := lift_of low_55_ok low_25

end Cofactor12116
def h39R : List Nat := varsOf 61
def h39G : Nat := 0xfaa0aaa0a000a000faa0aaa0a000a000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h39Bound : Lower h39R h39G 8 := carry_of (swaps := [(2,3),(3,4),(4,5),(1,2),(2,3),(0,1),(1,2)]) (roots2 := Cofactor12116.R_55) (T2 := Cofactor12116.G_55) (by decide +kernel) Cofactor12116.low_55
def h40R : List Nat := varsOf 26
def h40G : Nat := 0xffcccc00ffcccc00ffcccc00ffcccc00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h40Bound : Lower h40R h40G 4 := carry_of (swaps := [(1,2)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h41R : List Nat := varsOf 30
def h41G : Nat := 0xfcc0c000fcc0c000fcc0c000fcc0c000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h41Bound : Lower h41R h41G 7 := carry_of (swaps := [(4,5),(0,1)]) (roots2 := h36R) (T2 := h36G) (by decide +kernel) h36Bound
def h42R : List Nat := varsOf 46
def h42G : Nat := 0xfcc0fcc0ccc0ccc0fcc0fcc0ccc0ccc0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h42Bound : Lower h42R h42G 5 := carry_of (swaps := [(2,3),(0,1),(1,2),(0,1)]) (roots2 := h22R) (T2 := h22G) (by decide +kernel) h22Bound
def h43R : List Nat := varsOf 54
def h43G : Nat := 0xfcfcc0c0ccccc0c0fcfcc0c0ccccc0c0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Bound : Lower h43R h43G 5 := carry_of (swaps := [(2,3),(3,4),(0,1),(1,2),(0,1)]) (roots2 := h22R) (T2 := h22G) (by decide +kernel) h22Bound
def h44R : List Nat := varsOf 58
def h44G : Nat := 0xffcccc00cccccc00ffcccc00cccccc00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h44Bound : Lower h44R h44G 5 := carry_of (swaps := [(2,3),(3,4),(0,1),(1,2),(2,3),(0,1)]) (roots2 := h22R) (T2 := h22G) (by decide +kernel) h22Bound
def h45R : List Nat := varsOf 62
def h45G : Nat := 0xfcc0c000ccc0c000fcc0c000ccc0c000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45Bound : Lower h45R h45G 8 := carry_of (swaps := [(4,5),(0,1)]) (roots2 := h39R) (T2 := h39G) (by decide +kernel) h39Bound
def h46R : List Nat := varsOf 29
def h46G : Nat := 0xfffafaaafffafaaafffafaaafffafaaa
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Bound : Lower h46R h46G 5 := lift_of (z := 1) (o := 0) (essPairs := [(VAR 0,0,1)]) (by decide +kernel) h1Bound
namespace Cofactor12086
def G_0 : Nat := 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0
def R_0 : List Nat := varsOf 22
def pos_0 : List Nat := [6,6,18,18,20,20,6,18,20]
def neg_0 : List Nat := [4,2,16,2,16,4,16,4,2]
def fmask_0 : Nat := fullMask 9
def base_0 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xcf,0x10a),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x173,0xa1),(0xffff0000ffff0000ffff0000ffff0000,0x1bc,0x54)]
def steps_0 : List (Nat × Nat × Nat) := []
def W_0 : BT Decor := buildWiresBT 2 base_0 steps_0
def autosL_0 : List (List (Nat × Nat)) := []
def autos_0 : BT (List (Nat × Nat)) := btOfList 1 autosL_0
def slicesL_0 : List (Option (Nat × Nat)) := []
def slices_0 : BT (Option (Nat × Nat)) := btOfList 1 slicesL_0
def ps_0 : List PoolSpec := []
def P_0 : BT (Option BoundPool) := buildPoolsBT 1 W_0 R_0 slices_0 ps_0
lemma gp_0 : goodPairs G_0 pos_0 neg_0 := goodPairs_of (by decide +kernel)
lemma base_0_ok : ∀ x ∈ base_0, faithful pos_0 neg_0 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_0_ok : btAll (fun x => faithful pos_0 neg_0 x ∧ x.1 < 2^128) W_0 := buildWiresBT_faithful base_0_ok
set_option maxRecDepth 500000 in
lemma autos_0_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_0 = G_0) autos_0 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma slices_0_ok : btAll (fun o => ∀ p, o = some p → Slice R_0 G_0 p.1 p.2) slices_0 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_0 G_0 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 500000 in
lemma P_0_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_0 G_0 c) P_0 := buildPoolsBT_sound slices_0_ok
def bk_0_init : BT (List (List Nat)) := BT.empty
lemma bk_0_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 (0 - 1) xs.toFinset) bk_0_init := trivial
def nodes_0_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_0 : checkNodesBT W_0 G_0 fmask_0 P_0 autos_0 bk_0_init 0 nodes_0_0 = true := by decide +kernel
def bk_0_0 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_0
set_option maxRecDepth 500000 in
lemma bk_0_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 0 xs.toFinset) bk_0_0 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_init_ok chk_0_0
def nodes_0_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_1 : checkNodesBT W_0 G_0 fmask_0 P_0 autos_0 bk_0_0 1 nodes_0_1 = true := by decide +kernel
def bk_0_1 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_1
set_option maxRecDepth 500000 in
lemma bk_0_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 1 xs.toFinset) bk_0_1 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_0_ok chk_0_1
def nodes_0_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_2 : checkNodesBT W_0 G_0 fmask_0 P_0 autos_0 bk_0_1 2 nodes_0_2 = true := by decide +kernel
def bk_0_2 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_2
set_option maxRecDepth 500000 in
lemma bk_0_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 2 xs.toFinset) bk_0_2 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_1_ok chk_0_2
def nodes_0_3 : List NodeSpec := [([0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_3 : checkNodesBT W_0 G_0 fmask_0 P_0 autos_0 bk_0_2 3 nodes_0_3 = true := by decide +kernel
def bk_0_3 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_3
set_option maxRecDepth 500000 in
lemma bk_0_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 3 xs.toFinset) bk_0_3 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_2_ok chk_0_3
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_0_ok : forestRootCheck R_0 G_0 [(VAR 1,6,4),(VAR 2,6,2),(VAR 4,18,2)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_0_in : bucketContainsBT bk_0_3 R_0 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_0 : Lower R_0 G_0 4 := lower_of_forestBT root_0_ok bk_0_3_ok root_0_in

def G_1 : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def R_1 : List Nat := varsOf 7
lemma low_1_ok : carryOK [(0,3),(0,4),(0,2),(0,1)] R_1 G_1 R_0 G_0 = true := by decide +kernel
lemma low_1 : Lower R_1 G_1 4 := carry_of low_1_ok low_0

def G_3 : Nat := 0xeeee8888eeee8888eeee8888eeee8888
def R_3 : List Nat := varsOf 19
lemma low_3_ok : carryOK [(0,2),(0,1)] R_3 G_3 R_0 G_0 = true := by decide +kernel
lemma low_3 : Lower R_3 G_3 4 := carry_of low_3_ok low_0

def G_6 : Nat := 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0
def R_6 : List Nat := varsOf 21
lemma low_6_ok : carryOK [(0,1)] R_6 G_6 R_0 G_0 = true := by decide +kernel
lemma low_6 : Lower R_6 G_6 4 := carry_of low_6_ok low_0

def G_7 : Nat := 0xfafafafaa0a0a0a0fafafafaa0a0a0a0
def R_7 : List Nat := varsOf 37
lemma low_7_ok : carryOK [(4,5),(0,1)] R_7 G_7 R_0 G_0 = true := by decide +kernel
lemma low_7 : Lower R_7 G_7 4 := carry_of low_7_ok low_0

def G_8 : Nat := 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0
def R_8 : List Nat := varsOf 14
lemma low_8_ok : carryOK [(3,4)] R_8 G_8 R_0 G_0 = true := by decide +kernel
lemma low_8 : Lower R_8 G_8 4 := carry_of low_8_ok low_0

def G_9 : Nat := 0xfcfcfcfcc0c0c0c0fcfcfcfcc0c0c0c0
def R_9 : List Nat := varsOf 38
lemma low_9_ok : carryOK [(4,5)] R_9 G_9 R_0 G_0 = true := by decide +kernel
lemma low_9 : Lower R_9 G_9 4 := carry_of low_9_ok low_0

def G_11 : Nat := 0xffccffcccc00cc00ffccffcccc00cc00
def R_11 : List Nat := varsOf 42
lemma low_11_ok : carryOK [(4,5),(2,3)] R_11 G_11 R_0 G_0 = true := by decide +kernel
lemma low_11 : Lower R_11 G_11 4 := carry_of low_11_ok low_0

def G_12 : Nat := 0xfff0fff0f000f000fff0fff0f000f000
def R_12 : List Nat := varsOf 44
lemma low_12_ok : carryOK [(4,5),(1,2),(1,3)] R_12 G_12 R_0 G_0 = true := by decide +kernel
lemma low_12 : Lower R_12 G_12 4 := carry_of low_12_ok low_0

def G_14 : Nat := 0xfcc0fcc0c000c000fcc0fcc0c000c000
def R_14 : List Nat := varsOf 46
def pos_14 : List Nat := [14,14,14,38,38,38,42,42,42,44,44,44,14,14,14,38,38,38,42,42,42,44,44,44]
def neg_14 : List Nat := [12,10,6,36,34,6,40,34,10,40,36,12,34,36,40,10,12,40,6,12,36,6,10,34]
def fmask_14 : Nat := fullMask 24
def base_14 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0x1ff1ff,0xe491b6),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xe3fe3f,0x3d2c2d),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xfc7fc7,0x4bcb43),(0xffffffff00000000ffffffff00000000,0xff8ff8,0x9276d8)]
def steps_14 : List (Nat × Nat × Nat) := [(0,0,1),(0,0,2),(3,4,2),(0,4,2),(0,1,2),(3,7,3)]
def W_14 : BT Decor := buildWiresBT 4 base_14 steps_14
def autosL_14 : List (List (Nat × Nat)) := [[],[(3,5)],[(1,2)],[(3,5),(1,2)],[(2,3)],[(2,5),(2,3)],[(1,2),(1,3)],[(2,5),(1,2),(1,3)],[(2,5),(1,3)]]
def autos_14 : BT (List (Nat × Nat)) := btOfList 4 autosL_14
def slicesL_14 : List (Option (Nat × Nat)) := [some (subcubeFast 0 8,4),some (subcubeFast 0 2,4),some (subcubeFast 0 4,4),some (subcubeFast 0 32,4)]
def slices_14 : BT (Option (Nat × Nat)) := btOfList 2 slicesL_14
def ps_14 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[])]
def P_14 : BT (Option BoundPool) := buildPoolsBT 2 W_14 R_14 slices_14 ps_14
lemma gp_14 : goodPairs G_14 pos_14 neg_14 := goodPairs_of (by decide +kernel)
lemma base_14_ok : ∀ x ∈ base_14, faithful pos_14 neg_14 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_14_ok : btAll (fun x => faithful pos_14 neg_14 x ∧ x.1 < 2^128) W_14 := buildWiresBT_faithful base_14_ok
set_option maxRecDepth 500000 in
lemma autos_14_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_14 = G_14) autos_14 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_14_0_ok : sliceDirectCheck 0 8 0 R_14 G_14 R_9 G_9 = true := by decide +kernel
lemma sl_14_0 : Slice R_14 G_14 (subcubeFast 0 8) 4 := slice_fast_direct sl_14_0_ok low_9
lemma sl_14_1_ok : sliceDirectCheck 0 2 0 R_14 G_14 R_12 G_12 = true := by decide +kernel
lemma sl_14_1 : Slice R_14 G_14 (subcubeFast 0 2) 4 := slice_fast_direct sl_14_1_ok low_12
lemma sl_14_2_ok : sliceDirectCheck 0 4 0 R_14 G_14 R_11 G_11 = true := by decide +kernel
lemma sl_14_2 : Slice R_14 G_14 (subcubeFast 0 4) 4 := slice_fast_direct sl_14_2_ok low_11
lemma sl_14_3_ok : sliceDirectCheck 0 32 0 R_14 G_14 R_8 G_8 = true := by decide +kernel
lemma sl_14_3 : Slice R_14 G_14 (subcubeFast 0 32) 4 := slice_fast_direct sl_14_3_ok low_8
set_option maxRecDepth 500000 in
lemma slices_14_ok : btAll (fun o => ∀ p, o = some p → Slice R_14 G_14 p.1 p.2) slices_14 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_14 G_14 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_14_0) (forall_cons (fun _ h => by cases h; exact sl_14_1) (forall_cons (fun _ h => by cases h; exact sl_14_2) (forall_cons (fun _ h => by cases h; exact sl_14_3) (fun _ h => (List.not_mem_nil h).elim)))))
set_option maxRecDepth 500000 in
lemma P_14_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_14 G_14 c) P_14 := buildPoolsBT_sound slices_14_ok
def bk_14_init : BT (List (List Nat)) := BT.empty
lemma bk_14_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_14 (0 - 1) xs.toFinset) bk_14_init := trivial
def nodes_14_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_14_0 : checkNodesBT W_14 G_14 fmask_14 P_14 autos_14 bk_14_init 0 nodes_14_0 = true := by decide +kernel
def bk_14_0 : BT (List (List Nat)) := buildBucketsBT W_14 nodes_14_0
set_option maxRecDepth 500000 in
lemma bk_14_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_14 0 xs.toFinset) bk_14_0 :=
  buildBucketsBT_sound (by decide) gp_14 W_14_ok P_14_ok autos_14_ok bk_14_init_ok chk_14_0
def nodes_14_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_14_1 : checkNodesBT W_14 G_14 fmask_14 P_14 autos_14 bk_14_0 1 nodes_14_1 = true := by decide +kernel
def bk_14_1 : BT (List (List Nat)) := buildBucketsBT W_14 nodes_14_1
set_option maxRecDepth 500000 in
lemma bk_14_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_14 1 xs.toFinset) bk_14_1 :=
  buildBucketsBT_sound (by decide) gp_14 W_14_ok P_14_ok autos_14_ok bk_14_0_ok chk_14_1
def nodes_14_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_14_2 : checkNodesBT W_14 G_14 fmask_14 P_14 autos_14 bk_14_1 2 nodes_14_2 = true := by decide +kernel
def bk_14_2 : BT (List (List Nat)) := buildBucketsBT W_14 nodes_14_2
set_option maxRecDepth 500000 in
lemma bk_14_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_14 2 xs.toFinset) bk_14_2 :=
  buildBucketsBT_sound (by decide) gp_14 W_14_ok P_14_ok autos_14_ok bk_14_1_ok chk_14_2
def nodes_14_3 : List NodeSpec := [([4,5,8,3],[0,1],[]),([9,0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_14_3 : checkNodesBT W_14 G_14 fmask_14 P_14 autos_14 bk_14_2 3 nodes_14_3 = true := by decide +kernel
def bk_14_3 : BT (List (List Nat)) := buildBucketsBT W_14 nodes_14_3
set_option maxRecDepth 500000 in
lemma bk_14_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_14 3 xs.toFinset) bk_14_3 :=
  buildBucketsBT_sound (by decide) gp_14 W_14_ok P_14_ok autos_14_ok bk_14_2_ok chk_14_3
def nodes_14_4 : List NodeSpec := [([4,5,1,2,3],[0,2],[0]),([6,0,1,2,3],[],[]),([7,0,1,2,3],[3],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_14_4 : checkNodesBT W_14 G_14 fmask_14 P_14 autos_14 bk_14_3 4 nodes_14_4 = true := by decide +kernel
def bk_14_4 : BT (List (List Nat)) := buildBucketsBT W_14 nodes_14_4
set_option maxRecDepth 500000 in
lemma bk_14_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_14 4 xs.toFinset) bk_14_4 :=
  buildBucketsBT_sound (by decide) gp_14 W_14_ok P_14_ok autos_14_ok bk_14_3_ok chk_14_4
def nodes_14_5 : List NodeSpec := [([4,0,1,2,3],[2,1,0,3],[0,1,2,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_14_5 : checkNodesBT W_14 G_14 fmask_14 P_14 autos_14 bk_14_4 5 nodes_14_5 = true := by decide +kernel
def bk_14_5 : BT (List (List Nat)) := buildBucketsBT W_14 nodes_14_5
set_option maxRecDepth 500000 in
lemma bk_14_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_14 5 xs.toFinset) bk_14_5 :=
  buildBucketsBT_sound (by decide) gp_14 W_14_ok P_14_ok autos_14_ok bk_14_4_ok chk_14_5
def nodes_14_6 : List NodeSpec := [([0,1,2,3],[1,2,0,3],[0,4,5,6,7,8])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_14_6 : checkNodesBT W_14 G_14 fmask_14 P_14 autos_14 bk_14_5 6 nodes_14_6 = true := by decide +kernel
def bk_14_6 : BT (List (List Nat)) := buildBucketsBT W_14 nodes_14_6
set_option maxRecDepth 500000 in
lemma bk_14_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_14 6 xs.toFinset) bk_14_6 :=
  buildBucketsBT_sound (by decide) gp_14 W_14_ok P_14_ok autos_14_ok bk_14_5_ok chk_14_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_14_ok : forestRootCheck R_14 G_14 [(VAR 1,14,12),(VAR 2,14,10),(VAR 3,14,6),(VAR 5,38,6)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_14_in : bucketContainsBT bk_14_6 R_14 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_14 : Lower R_14 G_14 7 := lower_of_forestBT root_14_ok bk_14_6_ok root_14_in

def G_15 : Nat := 0xfcfcc0c0fcfc0000fcfcc0c0fcfc0000
def R_15 : List Nat := varsOf 54
lemma low_15_ok : liftCheck 0 32 R_15 G_15 R_0 G_0 [(VAR 5,38,6)] = true := by decide +kernel
lemma low_15 : Lower R_15 G_15 5 := lift_of low_15_ok low_0

def G_16 : Nat := 0xfefe8080fefe8080fefe8080fefe8080
def R_16 : List Nat := varsOf 23
def pos_16 : List Nat := [7,7,7,17,17,18,18,19,20,20,21,22,7,17,17,17,18,18,18,20,20,20]
def neg_16 : List Nat := [6,5,3,16,1,16,2,3,16,4,5,6,16,3,5,6,3,5,6,3,5,6]
def fmask_16 : Nat := fullMask 22
def base_16 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf49f,0x1b6496),(0xcccccccccccccccccccccccccccccccc,0x718e7,0x2da8c5),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x381f07,0x36ce03),(0xffff0000ffff0000ffff0000ffff0000,0x3feff8,0x1128)]
def steps_16 : List (Nat × Nat × Nat) := [(3,0,3),(2,0,3),(1,0,3),(1,0,1),(0,0,3),(2,0,1),(0,0,1),(3,1,6),(0,1,6),(1,8,1),(3,8,1),(3,9,2),(1,9,2),(3,0,1),(3,10,7)]
def W_16 : BT Decor := buildWiresBT 5 base_16 steps_16
def autosL_16 : List (List (Nat × Nat)) := [[],[(1,2)],[(0,1)],[(0,2),(0,1)],[(0,1),(0,2)],[(0,2)]]
def autos_16 : BT (List (Nat × Nat)) := btOfList 3 autosL_16
def slicesL_16 : List (Option (Nat × Nat)) := []
def slices_16 : BT (Option (Nat × Nat)) := btOfList 1 slicesL_16
def ps_16 : List PoolSpec := []
def P_16 : BT (Option BoundPool) := buildPoolsBT 1 W_16 R_16 slices_16 ps_16
lemma gp_16 : goodPairs G_16 pos_16 neg_16 := goodPairs_of (by decide +kernel)
lemma base_16_ok : ∀ x ∈ base_16, faithful pos_16 neg_16 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_16_ok : btAll (fun x => faithful pos_16 neg_16 x ∧ x.1 < 2^128) W_16 := buildWiresBT_faithful base_16_ok
set_option maxRecDepth 500000 in
lemma autos_16_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_16 = G_16) autos_16 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma slices_16_ok : btAll (fun o => ∀ p, o = some p → Slice R_16 G_16 p.1 p.2) slices_16 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_16 G_16 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 500000 in
lemma P_16_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_16 G_16 c) P_16 := buildPoolsBT_sound slices_16_ok
def bk_16_init : BT (List (List Nat)) := BT.empty
lemma bk_16_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_16 (0 - 1) xs.toFinset) bk_16_init := trivial
def nodes_16_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_16_0 : checkNodesBT W_16 G_16 fmask_16 P_16 autos_16 bk_16_init 0 nodes_16_0 = true := by decide +kernel
def bk_16_0 : BT (List (List Nat)) := buildBucketsBT W_16 nodes_16_0
set_option maxRecDepth 500000 in
lemma bk_16_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_16 0 xs.toFinset) bk_16_0 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok P_16_ok autos_16_ok bk_16_init_ok chk_16_0
def nodes_16_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_16_1 : checkNodesBT W_16 G_16 fmask_16 P_16 autos_16 bk_16_0 1 nodes_16_1 = true := by decide +kernel
def bk_16_1 : BT (List (List Nat)) := buildBucketsBT W_16 nodes_16_1
set_option maxRecDepth 500000 in
lemma bk_16_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_16 1 xs.toFinset) bk_16_1 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok P_16_ok autos_16_ok bk_16_0_ok chk_16_1
def nodes_16_2 : List NodeSpec := [([18,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_16_2 : checkNodesBT W_16 G_16 fmask_16 P_16 autos_16 bk_16_1 2 nodes_16_2 = true := by decide +kernel
def bk_16_2 : BT (List (List Nat)) := buildBucketsBT W_16 nodes_16_2
set_option maxRecDepth 500000 in
lemma bk_16_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_16 2 xs.toFinset) bk_16_2 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok P_16_ok autos_16_ok bk_16_1_ok chk_16_2
def nodes_16_3 : List NodeSpec := [([5,4,1,2],[],[]),([11,0,2,3],[],[]),([0,12,2,3],[],[]),([0,13,2,3],[],[]),([14,0,2,3],[],[]),([0,1,15,3],[],[]),([0,1,16,3],[],[]),([9,17,2,3],[],[0]),([10,7,2,3],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_16_3 : checkNodesBT W_16 G_16 fmask_16 P_16 autos_16 bk_16_2 3 nodes_16_3 = true := by decide +kernel
def bk_16_3 : BT (List (List Nat)) := buildBucketsBT W_16 nodes_16_3
set_option maxRecDepth 500000 in
lemma bk_16_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_16 3 xs.toFinset) bk_16_3 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok P_16_ok autos_16_ok bk_16_2_ok chk_16_3
def nodes_16_4 : List NodeSpec := [([4,0,1,2,3],[],[0]),([5,0,1,2,3],[],[0]),([0,1,2,3,6],[],[0,1]),([0,1,7,2,3],[],[0]),([8,0,1,2,3],[],[0,1]),([9,0,1,2,3],[],[0]),([10,0,1,2,3],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_16_4 : checkNodesBT W_16 G_16 fmask_16 P_16 autos_16 bk_16_3 4 nodes_16_4 = true := by decide +kernel
def bk_16_4 : BT (List (List Nat)) := buildBucketsBT W_16 nodes_16_4
set_option maxRecDepth 500000 in
lemma bk_16_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_16 4 xs.toFinset) bk_16_4 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok P_16_ok autos_16_ok bk_16_3_ok chk_16_4
def nodes_16_5 : List NodeSpec := [([0,1,2,3],[],[0,2,1,3,4,5])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_16_5 : checkNodesBT W_16 G_16 fmask_16 P_16 autos_16 bk_16_4 5 nodes_16_5 = true := by decide +kernel
def bk_16_5 : BT (List (List Nat)) := buildBucketsBT W_16 nodes_16_5
set_option maxRecDepth 500000 in
lemma bk_16_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_16 5 xs.toFinset) bk_16_5 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok P_16_ok autos_16_ok bk_16_4_ok chk_16_5
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_16_ok : forestRootCheck R_16 G_16 [(VAR 0,7,6),(VAR 1,7,5),(VAR 2,7,3),(VAR 4,17,1)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_16_in : bucketContainsBT bk_16_5 R_16 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_16 : Lower R_16 G_16 6 := lower_of_forestBT root_16_ok bk_16_5_ok root_16_in

def G_17 : Nat := 0xfefee8e8fefee8e8fefee8e8fefee8e8
def R_17 : List Nat := varsOf 23
def pos_17 : List Nat := [3,3,5,5,6,6,17,17,18,18,20,20,3,3,5,5,6,6,17,17,18,18,20,20]
def neg_17 : List Nat := [2,1,4,1,4,2,16,1,16,2,16,4,4,16,2,16,1,16,2,4,1,4,1,2]
def fmask_17 : Nat := fullMask 24
def base_17 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcf0cf,0x51008a),(0xcccccccccccccccccccccccccccccccc,0x333333,0x844221),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xc3cc3c,0x281814),(0xffff0000ffff0000ffff0000ffff0000,0xfc0fc0,0x2a540)]
def steps_17 : List (Nat × Nat × Nat) := [(1,0,1),(2,4,2),(1,4,2),(1,0,2),(2,6,3),(1,1,2)]
def W_17 : BT Decor := buildWiresBT 4 base_17 steps_17
def autosL_17 : List (List (Nat × Nat)) := [[],[(2,4)],[(0,1)],[(2,4),(0,1)],[(1,2)],[(1,4),(1,2)],[(0,1),(0,2)],[(1,4),(0,1),(0,2)],[(1,4),(0,2)]]
def autos_17 : BT (List (Nat × Nat)) := btOfList 4 autosL_17
def slicesL_17 : List (Option (Nat × Nat)) := [some (subcubeFast 2 0,4),some (subcubeFast 1 0,4),some (subcubeFast 16 0,4),some (subcubeFast 4 0,4)]
def slices_17 : BT (Option (Nat × Nat)) := btOfList 2 slicesL_17
def ps_17 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[])]
def P_17 : BT (Option BoundPool) := buildPoolsBT 2 W_17 R_17 slices_17 ps_17
lemma gp_17 : goodPairs G_17 pos_17 neg_17 := goodPairs_of (by decide +kernel)
lemma base_17_ok : ∀ x ∈ base_17, faithful pos_17 neg_17 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_17_ok : btAll (fun x => faithful pos_17 neg_17 x ∧ x.1 < 2^128) W_17 := buildWiresBT_faithful base_17_ok
set_option maxRecDepth 500000 in
lemma autos_17_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_17 = G_17) autos_17 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_17_0_ok : sliceDirectCheck 2 0 0 R_17 G_17 R_6 G_6 = true := by decide +kernel
lemma sl_17_0 : Slice R_17 G_17 (subcubeFast 2 0) 4 := slice_fast_direct sl_17_0_ok low_6
lemma sl_17_1_ok : sliceDirectCheck 1 0 0 R_17 G_17 R_0 G_0 = true := by decide +kernel
lemma sl_17_1 : Slice R_17 G_17 (subcubeFast 1 0) 4 := slice_fast_direct sl_17_1_ok low_0
lemma sl_17_2_ok : sliceDirectCheck 16 0 0 R_17 G_17 R_1 G_1 = true := by decide +kernel
lemma sl_17_2 : Slice R_17 G_17 (subcubeFast 16 0) 4 := slice_fast_direct sl_17_2_ok low_1
lemma sl_17_3_ok : sliceDirectCheck 4 0 0 R_17 G_17 R_3 G_3 = true := by decide +kernel
lemma sl_17_3 : Slice R_17 G_17 (subcubeFast 4 0) 4 := slice_fast_direct sl_17_3_ok low_3
set_option maxRecDepth 500000 in
lemma slices_17_ok : btAll (fun o => ∀ p, o = some p → Slice R_17 G_17 p.1 p.2) slices_17 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_17 G_17 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_17_0) (forall_cons (fun _ h => by cases h; exact sl_17_1) (forall_cons (fun _ h => by cases h; exact sl_17_2) (forall_cons (fun _ h => by cases h; exact sl_17_3) (fun _ h => (List.not_mem_nil h).elim)))))
set_option maxRecDepth 500000 in
lemma P_17_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_17 G_17 c) P_17 := buildPoolsBT_sound slices_17_ok
def bk_17_init : BT (List (List Nat)) := BT.empty
lemma bk_17_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_17 (0 - 1) xs.toFinset) bk_17_init := trivial
def nodes_17_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_17_0 : checkNodesBT W_17 G_17 fmask_17 P_17 autos_17 bk_17_init 0 nodes_17_0 = true := by decide +kernel
def bk_17_0 : BT (List (List Nat)) := buildBucketsBT W_17 nodes_17_0
set_option maxRecDepth 500000 in
lemma bk_17_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_17 0 xs.toFinset) bk_17_0 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok P_17_ok autos_17_ok bk_17_init_ok chk_17_0
def nodes_17_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_17_1 : checkNodesBT W_17 G_17 fmask_17 P_17 autos_17 bk_17_0 1 nodes_17_1 = true := by decide +kernel
def bk_17_1 : BT (List (List Nat)) := buildBucketsBT W_17 nodes_17_1
set_option maxRecDepth 500000 in
lemma bk_17_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_17 1 xs.toFinset) bk_17_1 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok P_17_ok autos_17_ok bk_17_0_ok chk_17_1
def nodes_17_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_17_2 : checkNodesBT W_17 G_17 fmask_17 P_17 autos_17 bk_17_1 2 nodes_17_2 = true := by decide +kernel
def bk_17_2 : BT (List (List Nat)) := buildBucketsBT W_17 nodes_17_2
set_option maxRecDepth 500000 in
lemma bk_17_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_17 2 xs.toFinset) bk_17_2 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok P_17_ok autos_17_ok bk_17_1_ok chk_17_2
def nodes_17_3 : List NodeSpec := [([8,0,1,2],[],[]),([4,7,9,3],[0,1],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_17_3 : checkNodesBT W_17 G_17 fmask_17 P_17 autos_17 bk_17_2 3 nodes_17_3 = true := by decide +kernel
def bk_17_3 : BT (List (List Nat)) := buildBucketsBT W_17 nodes_17_3
set_option maxRecDepth 500000 in
lemma bk_17_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_17 3 xs.toFinset) bk_17_3 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok P_17_ok autos_17_ok bk_17_2_ok chk_17_3
def nodes_17_4 : List NodeSpec := [([5,0,1,2,3],[],[]),([0,1,2,6,3],[2],[0]),([1,4,2,7,3],[0,3],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_17_4 : checkNodesBT W_17 G_17 fmask_17 P_17 autos_17 bk_17_3 4 nodes_17_4 = true := by decide +kernel
def bk_17_4 : BT (List (List Nat)) := buildBucketsBT W_17 nodes_17_4
set_option maxRecDepth 500000 in
lemma bk_17_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_17 4 xs.toFinset) bk_17_4 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok P_17_ok autos_17_ok bk_17_3_ok chk_17_4
def nodes_17_5 : List NodeSpec := [([0,1,4,2,3],[0,1,3,2],[0,1,2,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_17_5 : checkNodesBT W_17 G_17 fmask_17 P_17 autos_17 bk_17_4 5 nodes_17_5 = true := by decide +kernel
def bk_17_5 : BT (List (List Nat)) := buildBucketsBT W_17 nodes_17_5
set_option maxRecDepth 500000 in
lemma bk_17_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_17 5 xs.toFinset) bk_17_5 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok P_17_ok autos_17_ok bk_17_4_ok chk_17_5
def nodes_17_6 : List NodeSpec := [([0,1,2,3],[0,1,3,2],[0,4,5,6,7,8])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_17_6 : checkNodesBT W_17 G_17 fmask_17 P_17 autos_17 bk_17_5 6 nodes_17_6 = true := by decide +kernel
def bk_17_6 : BT (List (List Nat)) := buildBucketsBT W_17 nodes_17_6
set_option maxRecDepth 500000 in
lemma bk_17_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_17 6 xs.toFinset) bk_17_6 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok P_17_ok autos_17_ok bk_17_5_ok chk_17_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_17_ok : forestRootCheck R_17 G_17 [(VAR 0,3,2),(VAR 1,3,1),(VAR 2,5,1),(VAR 4,17,1)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_17_in : bucketContainsBT bk_17_6 R_17 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_17 : Lower R_17 G_17 7 := lower_of_forestBT root_17_ok bk_17_6_ok root_17_in

def G_19 : Nat := 0xfffffcfcffffc0c0fffffcfcffffc0c0
def R_19 : List Nat := varsOf 54
lemma low_19_ok : liftCheck 16 0 R_19 G_19 R_9 G_9 [(VAR 4,16,0)] = true := by decide +kernel
lemma low_19 : Lower R_19 G_19 5 := lift_of low_19_ok low_9

def G_21 : Nat := 0xe8e8e8e880808080e8e8e8e880808080
def R_21 : List Nat := varsOf 39
lemma low_21_ok : carryOK [(0,3),(0,2),(0,1)] R_21 G_21 R_14 G_14 = true := by decide +kernel
lemma low_21 : Lower R_21 G_21 7 := carry_of low_21_ok low_14

def G_24 : Nat := 0xeeee8888eeee0000eeee8888eeee0000
def R_24 : List Nat := varsOf 51
lemma low_24_ok : carryOK [(0,2),(0,1)] R_24 G_24 R_15 G_15 = true := by decide +kernel
lemma low_24 : Lower R_24 G_24 5 := carry_of low_24_ok low_15

def G_27 : Nat := 0xfafaa0a0fafa0000fafaa0a0fafa0000
def R_27 : List Nat := varsOf 53
lemma low_27_ok : carryOK [(0,1)] R_27 G_27 R_15 G_15 = true := by decide +kernel
lemma low_27 : Lower R_27 G_27 5 := carry_of low_27_ok low_15

def G_34 : Nat := 0xffffeeeeffff8888ffffeeeeffff8888
def R_34 : List Nat := varsOf 51
lemma low_34_ok : carryOK [(0,2),(0,1)] R_34 G_34 R_19 G_19 = true := by decide +kernel
lemma low_34 : Lower R_34 G_34 5 := carry_of low_34_ok low_19

def G_35 : Nat := 0xfffffafaffffa0a0fffffafaffffa0a0
def R_35 : List Nat := varsOf 53
lemma low_35_ok : carryOK [(0,1)] R_35 G_35 R_19 G_19 = true := by decide +kernel
lemma low_35 : Lower R_35 G_35 5 := carry_of low_35_ok low_19

def G_41 : Nat := 0xfefee8e8fefe8080fefee8e8fefe8080
def R_41 : List Nat := varsOf 55
def pos_41 : List Nat := [7,7,7,17,17,18,18,19,20,20,21,22,35,35,35,37,37,37,38,38,38,49,49,50,50,52,52,7,7,7,7,17,17,17,17,17,17,17,18,18,18,18,18,18,18,20,20,20,20,20,20,20,35,35,35,35,37,37,37,37,38,38,38,38]
def neg_41 : List Nat := [6,5,3,16,1,16,2,3,16,4,5,6,34,33,3,36,33,5,36,34,6,48,33,48,34,48,36,33,34,36,48,3,5,6,33,34,36,48,3,5,6,33,34,36,48,3,5,6,33,34,36,48,5,6,36,48,3,6,34,48,3,5,33,48]
def fmask_41 : Nat := fullMask 64
def base_41 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff0003ff863f49f,0x711162c588436496),(0xcccccccccccccccccccccccccccccccc,0xf0f01fc0799c78e7,0x1722a54a911858c5),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff0fe0007e1f8f07,0x2274c99324168e03),(0xffff0000ffff0000ffff0000ffff0000,0xfffff87e00ff8,0x8888102042a00128),(0xffffffff00000000ffffffff00000000,0xfff0000007fff000,0xcccf1e3c7fedb000)]
def steps_41 : List (Nat × Nat × Nat) := [(2,0,1),(1,0,1),(0,0,1),(3,0,1),(3,7,6),(2,9,2),(1,9,2),(3,9,2),(0,9,2),(3,13,11)]
def W_41 : BT Decor := buildWiresBT 4 base_41 steps_41
def autosL_41 : List (List (Nat × Nat)) := [[],[(0,1)],[(1,2)],[(0,2),(0,1)],[(0,1),(0,2)],[(0,2)]]
def autos_41 : BT (List (Nat × Nat)) := btOfList 3 autosL_41
def slicesL_41 : List (Option (Nat × Nat)) := [some (subcubeFast 2 32,4),some (subcubeFast 32 0,6),some (subcubeFast 16 2,4),some (subcubeFast 0 2,5),some (subcubeFast 0 1,5),some (subcubeFast 2 0,5),some (subcubeFast 0 4,5),some (subcubeFast 4 0,5),some (subcubeFast 0 32,7),some (subcubeFast 1 0,5),some (subcubeFast 1 32,4),some (subcubeFast 16 0,7)]
def slices_41 : BT (Option (Nat × Nat)) := btOfList 4 slicesL_41
def ps_41 : List PoolSpec := [(0,[]),(1,[(0,0,1),(1,0,1),(3,7,6)]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(8,[]),(1,[]),(9,[]),(10,[]),(8,[(1,0,1)]),(11,[(0,0,1)]),(11,[])]
def P_41 : BT (Option BoundPool) := buildPoolsBT 4 W_41 R_41 slices_41 ps_41
lemma gp_41 : goodPairs G_41 pos_41 neg_41 := goodPairs_of (by decide +kernel)
lemma base_41_ok : ∀ x ∈ base_41, faithful pos_41 neg_41 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_41_ok : btAll (fun x => faithful pos_41 neg_41 x ∧ x.1 < 2^128) W_41 := buildWiresBT_faithful base_41_ok
set_option maxRecDepth 500000 in
lemma autos_41_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_41 = G_41) autos_41 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_41_0_ok : sliceDirectCheck 2 32 0 R_41 G_41 R_6 G_6 = true := by decide +kernel
lemma sl_41_0 : Slice R_41 G_41 (subcubeFast 2 32) 4 := slice_fast_direct sl_41_0_ok low_6
lemma sl_41_1_ok : sliceDirectCheck 32 0 0 R_41 G_41 R_16 G_16 = true := by decide +kernel
lemma sl_41_1 : Slice R_41 G_41 (subcubeFast 32 0) 6 := slice_fast_direct sl_41_1_ok low_16
lemma sl_41_2_ok : sliceDirectCheck 16 2 0 R_41 G_41 R_7 G_7 = true := by decide +kernel
lemma sl_41_2 : Slice R_41 G_41 (subcubeFast 16 2) 4 := slice_fast_direct sl_41_2_ok low_7
lemma sl_41_3_ok : sliceDirectCheck 0 2 0 R_41 G_41 R_35 G_35 = true := by decide +kernel
lemma sl_41_3 : Slice R_41 G_41 (subcubeFast 0 2) 5 := slice_fast_direct sl_41_3_ok low_35
lemma sl_41_4_ok : sliceDirectCheck 0 1 0 R_41 G_41 R_19 G_19 = true := by decide +kernel
lemma sl_41_4 : Slice R_41 G_41 (subcubeFast 0 1) 5 := slice_fast_direct sl_41_4_ok low_19
lemma sl_41_5_ok : sliceDirectCheck 2 0 0 R_41 G_41 R_27 G_27 = true := by decide +kernel
lemma sl_41_5 : Slice R_41 G_41 (subcubeFast 2 0) 5 := slice_fast_direct sl_41_5_ok low_27
lemma sl_41_6_ok : sliceDirectCheck 0 4 0 R_41 G_41 R_34 G_34 = true := by decide +kernel
lemma sl_41_6 : Slice R_41 G_41 (subcubeFast 0 4) 5 := slice_fast_direct sl_41_6_ok low_34
lemma sl_41_7_ok : sliceDirectCheck 4 0 0 R_41 G_41 R_24 G_24 = true := by decide +kernel
lemma sl_41_7 : Slice R_41 G_41 (subcubeFast 4 0) 5 := slice_fast_direct sl_41_7_ok low_24
lemma sl_41_8_ok : sliceDirectCheck 0 32 0 R_41 G_41 R_17 G_17 = true := by decide +kernel
lemma sl_41_8 : Slice R_41 G_41 (subcubeFast 0 32) 7 := slice_fast_direct sl_41_8_ok low_17
lemma sl_41_9_ok : sliceDirectCheck 1 0 0 R_41 G_41 R_15 G_15 = true := by decide +kernel
lemma sl_41_9 : Slice R_41 G_41 (subcubeFast 1 0) 5 := slice_fast_direct sl_41_9_ok low_15
lemma sl_41_10_ok : sliceDirectCheck 1 32 0 R_41 G_41 R_0 G_0 = true := by decide +kernel
lemma sl_41_10 : Slice R_41 G_41 (subcubeFast 1 32) 4 := slice_fast_direct sl_41_10_ok low_0
lemma sl_41_11_ok : sliceDirectCheck 16 0 0 R_41 G_41 R_21 G_21 = true := by decide +kernel
lemma sl_41_11 : Slice R_41 G_41 (subcubeFast 16 0) 7 := slice_fast_direct sl_41_11_ok low_21
set_option maxRecDepth 500000 in
lemma slices_41_ok : btAll (fun o => ∀ p, o = some p → Slice R_41 G_41 p.1 p.2) slices_41 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_41 G_41 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_41_0) (forall_cons (fun _ h => by cases h; exact sl_41_1) (forall_cons (fun _ h => by cases h; exact sl_41_2) (forall_cons (fun _ h => by cases h; exact sl_41_3) (forall_cons (fun _ h => by cases h; exact sl_41_4) (forall_cons (fun _ h => by cases h; exact sl_41_5) (forall_cons (fun _ h => by cases h; exact sl_41_6) (forall_cons (fun _ h => by cases h; exact sl_41_7) (forall_cons (fun _ h => by cases h; exact sl_41_8) (forall_cons (fun _ h => by cases h; exact sl_41_9) (forall_cons (fun _ h => by cases h; exact sl_41_10) (forall_cons (fun _ h => by cases h; exact sl_41_11) (fun _ h => (List.not_mem_nil h).elim)))))))))))))
set_option maxRecDepth 500000 in
lemma P_41_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_41 G_41 c) P_41 := buildPoolsBT_sound slices_41_ok
def bk_41_init : BT (List (List Nat)) := BT.empty
lemma bk_41_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 (0 - 1) xs.toFinset) bk_41_init := trivial
def nodes_41_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_41_0 : checkNodesBT W_41 G_41 fmask_41 P_41 autos_41 bk_41_init 0 nodes_41_0 = true := by decide +kernel
def bk_41_0 : BT (List (List Nat)) := buildBucketsBT W_41 nodes_41_0
set_option maxRecDepth 500000 in
lemma bk_41_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 0 xs.toFinset) bk_41_0 :=
  buildBucketsBT_sound (by decide) gp_41 W_41_ok P_41_ok autos_41_ok bk_41_init_ok chk_41_0
def nodes_41_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_41_1 : checkNodesBT W_41 G_41 fmask_41 P_41 autos_41 bk_41_0 1 nodes_41_1 = true := by decide +kernel
def bk_41_1 : BT (List (List Nat)) := buildBucketsBT W_41 nodes_41_1
set_option maxRecDepth 500000 in
lemma bk_41_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 1 xs.toFinset) bk_41_1 :=
  buildBucketsBT_sound (by decide) gp_41 W_41_ok P_41_ok autos_41_ok bk_41_0_ok chk_41_1
def nodes_41_2 : List NodeSpec := [([14,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_41_2 : checkNodesBT W_41 G_41 fmask_41 P_41 autos_41 bk_41_1 2 nodes_41_2 = true := by decide +kernel
def bk_41_2 : BT (List (List Nat)) := buildBucketsBT W_41 nodes_41_2
set_option maxRecDepth 500000 in
lemma bk_41_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 2 xs.toFinset) bk_41_2 :=
  buildBucketsBT_sound (by decide) gp_41 W_41_ok P_41_ok autos_41_ok bk_41_1_ok chk_41_2
def nodes_41_3 : List NodeSpec := nodesWithIdentity [([10,12,3,4],[]),([13,11,3,4],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_41_3 : checkNodesBT W_41 G_41 fmask_41 P_41 autos_41 bk_41_2 3 nodes_41_3 = true := by decide +kernel
def bk_41_3 : BT (List (List Nat)) := buildBucketsBT W_41 nodes_41_3
set_option maxRecDepth 500000 in
lemma bk_41_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 3 xs.toFinset) bk_41_3 :=
  buildBucketsBT_sound (by decide) gp_41 W_41_ok P_41_ok autos_41_ok bk_41_2_ok chk_41_3
def nodes_41_4 : List NodeSpec := nodesWithIdentity [([10,9,2,3,4],[0,1]),([9,2,11,3,4],[]),([9,12,2,3,4],[]),([13,9,2,3,4],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_41_4 : checkNodesBT W_41 G_41 fmask_41 P_41 autos_41 bk_41_3 4 nodes_41_4 = true := by decide +kernel
def bk_41_4 : BT (List (List Nat)) := buildBucketsBT W_41 nodes_41_4
set_option maxRecDepth 500000 in
lemma bk_41_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 4 xs.toFinset) bk_41_4 :=
  buildBucketsBT_sound (by decide) gp_41 W_41_ok P_41_ok autos_41_ok bk_41_3_ok chk_41_4
def nodes_41_5 : List NodeSpec := nodesWithIdentity [([9,2,3,4],[2,0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_41_5 : checkNodesBT W_41 G_41 fmask_41 P_41 autos_41 bk_41_4 5 nodes_41_5 = true := by decide +kernel
def bk_41_5 : BT (List (List Nat)) := buildBucketsBT W_41 nodes_41_5
set_option maxRecDepth 500000 in
lemma bk_41_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 5 xs.toFinset) bk_41_5 :=
  buildBucketsBT_sound (by decide) gp_41 W_41_ok P_41_ok autos_41_ok bk_41_4_ok chk_41_5
def nodes_41_6 : List NodeSpec := nodesWithIdentity [([5,8,2,3,4],[3,4,2,0]),([7,6,2,3,4],[5,4,2,0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_41_6 : checkNodesBT W_41 G_41 fmask_41 P_41 autos_41 bk_41_5 6 nodes_41_6 = true := by decide +kernel
def bk_41_6 : BT (List (List Nat)) := buildBucketsBT W_41 nodes_41_6
set_option maxRecDepth 500000 in
lemma bk_41_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 6 xs.toFinset) bk_41_6 :=
  buildBucketsBT_sound (by decide) gp_41 W_41_ok P_41_ok autos_41_ok bk_41_5_ok chk_41_6
def nodes_41_7 : List NodeSpec := nodesWithIdentity [([5,0,1,2,3,4],[5,4,3,6,7,2,8,9,10,11]),([0,1,6,2,3,4],[4,5,2,7,6,9,8,12]),([7,0,1,2,3,4],[5,3,6,7,13,8,9,4,10,0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_41_7 : checkNodesBT W_41 G_41 fmask_41 P_41 autos_41 bk_41_6 7 nodes_41_7 = true := by decide +kernel
def bk_41_7 : BT (List (List Nat)) := buildBucketsBT W_41 nodes_41_7
set_option maxRecDepth 500000 in
lemma bk_41_7_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 7 xs.toFinset) bk_41_7 :=
  buildBucketsBT_sound (by decide) gp_41 W_41_ok P_41_ok autos_41_ok bk_41_6_ok chk_41_7
def nodes_41_8 : List NodeSpec := [([0,1,2,3,4],[14,8],[0,1,2,3,4,5])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_41_8 : checkNodesBT W_41 G_41 fmask_41 P_41 autos_41 bk_41_7 8 nodes_41_8 = true := by decide +kernel
def bk_41_8 : BT (List (List Nat)) := buildBucketsBT W_41 nodes_41_8
set_option maxRecDepth 500000 in
lemma bk_41_8_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 8 xs.toFinset) bk_41_8 :=
  buildBucketsBT_sound (by decide) gp_41 W_41_ok P_41_ok autos_41_ok bk_41_7_ok chk_41_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_41_ok : forestRootCheck R_41 G_41 [(VAR 0,7,6),(VAR 1,7,5),(VAR 2,7,3),(VAR 4,17,1),(VAR 5,35,3)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_41_in : bucketContainsBT bk_41_8 R_41 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_41 : Lower R_41 G_41 9 := lower_of_forestBT root_41_ok bk_41_8_ok root_41_in

end Cofactor12086
def h47R : List Nat := varsOf 31
def h47G : Nat := 0xfee8eaa8fee8eaa8fee8eaa8fee8eaa8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h47Bound : Lower h47R h47G 9 := carry_of (swaps := [(3,4),(4,5),(2,3),(1,2),(0,1)]) (roots2 := Cofactor12086.R_41) (T2 := Cofactor12086.G_41) (by decide +kernel) Cofactor12086.low_41
def h48R : List Nat := varsOf 43
def h48G : Nat := 0xffeeffeeeecceeccffeeffeeeecceecc
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Bound : Lower h48R h48G 5 := carry_of (swaps := [(4,5),(1,2),(0,1)]) (roots2 := h46R) (T2 := h46G) (by decide +kernel) h46Bound
def h49R : List Nat := varsOf 46
def h49G : Nat := 0xfffcfffcfcccfcccfffcfffcfcccfccc
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Bound : Lower h49R h49G 5 := carry_of (swaps := [(4,5),(0,1)]) (roots2 := h46R) (T2 := h46G) (by decide +kernel) h46Bound
def h50R : List Nat := varsOf 47
def h50G : Nat := 0xfee8fee8ecc8ecc8fee8fee8ecc8ecc8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50Bound : Lower h50R h50G 9 := carry_of (swaps := [(4,5),(0,1)]) (roots2 := h47R) (T2 := h47G) (by decide +kernel) h47Bound
def h52R : List Nat := varsOf 39
def h52G : Nat := 0xeaeaeaeae0e0e0e0eaeaeaeae0e0e0e0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h52Bound : Lower h52R h52G 4 := carry_of (swaps := [(4,5),(0,1)]) (roots2 := h10R) (T2 := h10G) (by decide +kernel) h10Bound
def h53R : List Nat := varsOf 37
def h53G : Nat := 0xfafafafaa0a0a0a0fafafafaa0a0a0a0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Bound : Lower h53R h53G 4 := carry_of (swaps := [(4,5),(1,2),(2,3),(0,1)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h54R : List Nat := varsOf 22
def h54G : Nat := 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h54Bound : Lower h54R h54G 4 := carry_of (swaps := [(1,2),(2,3)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h55R : List Nat := varsOf 23
def h55G : Nat := 0xfefeeaeafefeeaeafefeeaeafefeeaea
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Bound : Lower h55R h55G 5 := carry_of (swaps := [(1,2),(2,3)]) (roots2 := h46R) (T2 := h46G) (by decide +kernel) h46Bound
def h56R : List Nat := varsOf 39
def h56G : Nat := 0xfefefefeececececfefefefeecececec
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h56Bound : Lower h56R h56G 5 := carry_of (swaps := [(4,5),(1,2),(2,3),(0,1)]) (roots2 := h46R) (T2 := h46G) (by decide +kernel) h46Bound
def h51R : List Nat := varsOf 55
def h51G : Nat := 0xfefeeaeaecece0e0fefeeaeaecece0e0
def h51Pos : List Nat := [5,6,19,35,18,6,5,7,52,18,35,33,52,33,19,21,38,52,18,33,18,5,21,37,38,49,19,22,22,5,50,49,50,52,52,18]
def h51Neg : List Nat := [4,4,17,34,17,2,1,3,36,2,3,1,20,36,3,17,34,48,20,32,16,0,20,36,36,48,2,2,20,17,34,17,48,32,16,34]
def h51Mask : Nat := fullMask 36
def h51Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xa6e8eccd,0xa000ccd4),(0xcccccccccccccccccccccccccccccccc,0x95d1546be,0x84c0146a8),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x639e391e3,0x11c43103),(0xffff0000ffff0000ffff0000ffff0000,0xfde56d314,0x5b2569014),(0xffffffff00000000ffffffff00000000,0x7c38b3d08,0xb438b2108)]
def h51Steps : List (Nat × Nat × Nat) := [(1,0,1),(1,0,2),(1,1,6),(3,1,6),(0,2,3),(3,2,3),(0,2,5),(2,2,5),(3,2,5),(0,3,4),(0,4,6),(3,0,2),(3,0,3),(1,1,12),(1,2,17),(2,2,17),(1,0,9),(1,0,10),(1,2,14),(2,2,14)]
def h51W : BT Decor := buildWiresBT 5 h51Base h51Steps
def h51AutoList : List (List (Nat × Nat)) := [[],[(4,5),(0,1)]]
def h51Autos : BT (List (Nat × Nat)) := btOfList 1 h51AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Pairs : goodPairs h51G h51Pos h51Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51BaseOk : ∀ x ∈ h51Base, faithful h51Pos h51Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51WOk : btAll (fun x => faithful h51Pos h51Neg x ∧ x.1 < 2^128) h51W := buildWiresBT_faithful h51BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h51G = h51G) h51Autos := btAll_ofList (autos_of (by decide +kernel))
def h51SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 16,5),some (subcubeFast 0 32,5),some (subcubeFast 1 0,5),some (subcubeFast 1 32,4),some (subcubeFast 2 0,5),some (subcubeFast 2 16,4),some (subcubeFast 16 0,4),some (subcubeFast 32 0,4)]
def h51Slices : BT (Option (Nat × Nat)) := btOfList 3 h51SliceList
def h51Specs : List PoolSpec := [(2,[]),(4,[]),(0,[(1,0,1)]),(3,[]),(5,[]),(1,[(1,0,1)]),(0,[]),(6,[]),(1,[]),(7,[]),(1,[(1,0,2)]),(2,[(0,4,6)]),(1,[(3,0,2)]),(4,[(3,0,3)]),(1,[(3,0,3)]),(4,[(0,2,3)]),(2,[(0,3,4)]),(4,[(0,3,4)])]
def h51Pools : BT (Option BoundPool) := buildPoolsBT 5 h51W h51R h51Slices h51Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Slice7 : Slice h51R h51G (subcubeFast 32 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h10Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Slice6 : Slice h51R h51G (subcubeFast 16 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h52Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Slice5 : Slice h51R h51G (subcubeFast 2 16) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h53Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Slice4 : Slice h51R h51G (subcubeFast 2 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h37Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Slice3 : Slice h51R h51G (subcubeFast 1 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h54Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Slice2 : Slice h51R h51G (subcubeFast 1 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h43Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Slice1 : Slice h51R h51G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h55Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Slice0 : Slice h51R h51G (subcubeFast 0 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h56Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h51R h51G p.1 p.2) h51Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h51R h51G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h51Slice0) (forall_cons (fun _ h => by cases h; exact h51Slice1) (forall_cons (fun _ h => by cases h; exact h51Slice2) (forall_cons (fun _ h => by cases h; exact h51Slice3) (forall_cons (fun _ h => by cases h; exact h51Slice4) (forall_cons (fun _ h => by cases h; exact h51Slice5) (forall_cons (fun _ h => by cases h; exact h51Slice6) (forall_cons (fun _ h => by cases h; exact h51Slice7) (fun _ h => (List.not_mem_nil h).elim)))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h51R h51G c) h51Pools := buildPoolsBT_sound h51SlicesOk
def h51Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h51G (4 - 1) xs.toFinset) h51Empty := trivial
def h51Block4_0 : List NodeSpec := nodesWithIdentity [([1,2,3,5,15],[]),([1,2,3,15,16],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test4_0 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Empty 4 h51Block4_0 = true := by decide +kernel
def h51Nodes4 : List NodeSpec := h51Block4_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Check4 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Empty 4 h51Nodes4 = true := h51Test4_0
def h51Bucket4 : BT (List (List Nat)) := buildBucketsBT h51W h51Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h51G 4 xs.toFinset) h51Bucket4 := buildBucketsBT_sound (by decide) h51Pairs h51WOk h51PoolsOk h51AutosOk h51EmptyOk h51Check4
def h51Block5_0 : List NodeSpec := nodesWithIdentity [([1,2,3,4,5,6],[1]),([0,1,2,3,4,11],[0,1,6,7,8,9]),([0,1,2,3,4,7],[6,7,8,9]),([0,1,2,3,4,12],[]),([0,1,2,3,4,13],[]),([1,2,3,4,6,16],[0]),([0,1,2,3,4,8],[]),([0,1,2,3,15],[10,11]),([0,1,2,3,6,15],[8]),([0,1,2,3,4,18],[6,7]),([0,1,2,3,4,19],[]),([0,1,2,3,4,20],[0,8,9])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test5_0 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket4 5 h51Block5_0 = true := by decide +kernel
def h51Block5_1 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,21],[8,9]),([0,1,2,3,4,22],[]),([0,1,2,3,4,23],[]),([0,1,2,3,4,24],[6,8])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test5_1 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket4 5 h51Block5_1 = true := by decide +kernel
def h51Nodes5 : List NodeSpec := h51Block5_0 ++ h51Block5_1
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Check5 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket4 5 h51Nodes5 = true := by
  unfold h51Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h51Test5_0,h51Test5_1⟩
def h51Bucket5 : BT (List (List Nat)) := buildBucketsBT h51W h51Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h51G 5 xs.toFinset) h51Bucket5 := buildBucketsBT_sound (by decide) h51Pairs h51WOk h51PoolsOk h51AutosOk h51Bucket4Ok h51Check5
def h51Block6_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,4,5,6,7,8,9],[0,1]),([0,1,2,3,4,6],[0,1,3,6,7,8,9,10],[0]),([0,1,2,3,4,16],[0,1,3,6,7,8,9,12],[0]),([0,1,2,3,4,17],[0,1,4,6,7,8,9,13,14],[0]),([0,1,2,3,4,9],[0,1,4,6,7,8,9,15],[0]),([0,1,2,3,4,10],[0,1,4,6,7,8,9],[0]),([0,1,2,3,4,14],[0,1,3,4,6,7,8,9,16,17],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test6_0 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket5 6 h51Block6_0 = true := by decide +kernel
def h51Nodes6 : List NodeSpec := h51Block6_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Check6 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket5 6 h51Nodes6 = true := h51Test6_0
def h51Bucket6 : BT (List (List Nat)) := buildBucketsBT h51W h51Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h51G 6 xs.toFinset) h51Bucket6 := buildBucketsBT_sound (by decide) h51Pairs h51WOk h51PoolsOk h51AutosOk h51Bucket5Ok h51Check6
def h51Block7_0 : List NodeSpec := [([0,1,2,3,4],[0,1,3,4,6,8],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Test7_0 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket6 7 h51Block7_0 = true := by decide +kernel
def h51Nodes7 : List NodeSpec := h51Block7_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Check7 : checkNodesBT h51W h51G h51Mask h51Pools h51Autos h51Bucket6 7 h51Nodes7 = true := h51Test7_0
def h51Bucket7 : BT (List (List Nat)) := buildBucketsBT h51W h51Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h51G 7 xs.toFinset) h51Bucket7 := buildBucketsBT_sound (by decide) h51Pairs h51WOk h51PoolsOk h51AutosOk h51Bucket6Ok h51Check7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Bound : Lower h51R h51G 8 := lower_of_forestBT (essPairs := [(VAR 0,4,5),(VAR 1,4,6),(VAR 2,1,5),(VAR 4,2,18),(VAR 5,1,33)]) (by decide +kernel) h51Bucket7Ok (by decide +kernel)
def h58R : List Nat := varsOf 27
def h58G : Nat := 0xffeeeeaaffeeeeaaffeeeeaaffeeeeaa
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h58Bound : Lower h58R h58G 5 := carry_of (swaps := [(1,2)]) (roots2 := h46R) (T2 := h46G) (by decide +kernel) h46Bound
def h57R : List Nat := varsOf 59
def h57G : Nat := 0xffeeeeaaeeccee88ffeeeeaaeeccee88
def h57Pos : List Nat := [9,10,3,3,18,10,9,18,49,33,25,56,19,41,35,56,18,33,25,42,56,33,42,18,50,9,49]
def h57Neg : List Nat := [8,8,1,2,17,2,1,2,17,1,24,40,17,40,34,24,24,40,17,34,48,32,40,16,48,0,48]
def h57Mask : Nat := fullMask 27
def h57Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x626774d,0x41354),(0xcccccccccccccccccccccccccccccccc,0x1c950be,0x840a8),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x25cac63,0x43ac03),(0xffff0000ffff0000ffff0000ffff0000,0x5959d90,0x5959510),(0xffffffff00000000ffffffff00000000,0x57aeb00,0x57a6800)]
def h57Steps : List (Nat × Nat × Nat) := [(1,0,1),(1,0,2),(1,1,2),(0,4,6),(1,5,6),(3,1,2),(3,1,4),(3,1,6),(3,2,5),(3,0,2),(1,0,3),(3,0,3),(2,6,11),(1,1,14)]
def h57W : BT Decor := buildWiresBT 5 h57Base h57Steps
def h57AutoList : List (List (Nat × Nat)) := [[],[(4,5),(0,1)]]
def h57Autos : BT (List (Nat × Nat)) := btOfList 1 h57AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h57Pairs : goodPairs h57G h57Pos h57Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h57BaseOk : ∀ x ∈ h57Base, faithful h57Pos h57Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h57WOk : btAll (fun x => faithful h57Pos h57Neg x ∧ x.1 < 2^128) h57W := buildWiresBT_faithful h57BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h57AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h57G = h57G) h57Autos := btAll_ofList (autos_of (by decide +kernel))
def h57SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 16,5),some (subcubeFast 0 32,5),some (subcubeFast 1 0,5),some (subcubeFast 1 32,4),some (subcubeFast 2 0,5),some (subcubeFast 2 16,4),some (subcubeFast 8 0,4),some (subcubeFast 16 0,5),some (subcubeFast 32 0,5),some (subcubeFast 48 0,4)]
def h57Slices : BT (Option (Nat × Nat)) := btOfList 4 h57SliceList
def h57Specs : List PoolSpec := [(2,[]),(4,[]),(3,[]),(5,[]),(0,[(1,0,1)]),(1,[(1,0,1)]),(6,[]),(7,[]),(0,[]),(8,[]),(1,[]),(1,[(1,0,2)]),(1,[(3,0,2)]),(4,[(1,0,3)]),(1,[(1,0,3)]),(8,[(1,0,3)]),(4,[(3,0,3)]),(1,[(3,0,3)]),(9,[]),(8,[(3,0,3)])]
def h57Pools : BT (Option BoundPool) := buildPoolsBT 5 h57W h57R h57Slices h57Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h57Slice9 : Slice h57R h57G (subcubeFast 48 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h4Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h57Slice8 : Slice h57R h57G (subcubeFast 32 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h11Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h57Slice7 : Slice h57R h57G (subcubeFast 16 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h18Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h57Slice6 : Slice h57R h57G (subcubeFast 8 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h28Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h57Slice5 : Slice h57R h57G (subcubeFast 2 16) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h35Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h57Slice4 : Slice h57R h57G (subcubeFast 2 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h38Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h57Slice3 : Slice h57R h57G (subcubeFast 1 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h40Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h57Slice2 : Slice h57R h57G (subcubeFast 1 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h44Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h57Slice1 : Slice h57R h57G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h58Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h57Slice0 : Slice h57R h57G (subcubeFast 0 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h48Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h57SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h57R h57G p.1 p.2) h57Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h57R h57G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h57Slice0) (forall_cons (fun _ h => by cases h; exact h57Slice1) (forall_cons (fun _ h => by cases h; exact h57Slice2) (forall_cons (fun _ h => by cases h; exact h57Slice3) (forall_cons (fun _ h => by cases h; exact h57Slice4) (forall_cons (fun _ h => by cases h; exact h57Slice5) (forall_cons (fun _ h => by cases h; exact h57Slice6) (forall_cons (fun _ h => by cases h; exact h57Slice7) (forall_cons (fun _ h => by cases h; exact h57Slice8) (forall_cons (fun _ h => by cases h; exact h57Slice9) (fun _ h => (List.not_mem_nil h).elim)))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h57PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h57R h57G c) h57Pools := buildPoolsBT_sound h57SlicesOk
def h57Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h57EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h57G (4 - 1) xs.toFinset) h57Empty := trivial
def h57Block4_0 : List NodeSpec := nodesWithIdentity [([3,4,5,6,7],[]),([0,1,2,3,17],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h57Test4_0 : checkNodesBT h57W h57G h57Mask h57Pools h57Autos h57Empty 4 h57Block4_0 = true := by decide +kernel
def h57Nodes4 : List NodeSpec := h57Block4_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h57Check4 : checkNodesBT h57W h57G h57Mask h57Pools h57Autos h57Empty 4 h57Nodes4 = true := h57Test4_0
def h57Bucket4 : BT (List (List Nat)) := buildBucketsBT h57W h57Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h57Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h57G 4 xs.toFinset) h57Bucket4 := buildBucketsBT_sound (by decide) h57Pairs h57WOk h57PoolsOk h57AutosOk h57EmptyOk h57Check4
def h57Block5_0 : List NodeSpec := nodesWithIdentity [([1,2,3,4,5,6],[1,2]),([0,1,2,3,4,9],[7,8,9,10]),([0,1,2,3,4,13],[]),([0,1,3,4,6,7],[0]),([0,1,3,4,6,10],[]),([0,1,2,3,6,11],[9]),([0,1,2,3,4,12],[9,10]),([0,1,2,3,6,8],[10]),([0,1,2,3,11,14],[]),([0,1,2,3,4,18],[7,8])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h57Test5_0 : checkNodesBT h57W h57G h57Mask h57Pools h57Autos h57Bucket4 5 h57Block5_0 = true := by decide +kernel
def h57Nodes5 : List NodeSpec := h57Block5_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h57Check5 : checkNodesBT h57W h57G h57Mask h57Pools h57Autos h57Bucket4 5 h57Nodes5 = true := h57Test5_0
def h57Bucket5 : BT (List (List Nat)) := buildBucketsBT h57W h57Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h57Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h57G 5 xs.toFinset) h57Bucket5 := buildBucketsBT_sound (by decide) h57Pairs h57WOk h57PoolsOk h57AutosOk h57Bucket4Ok h57Check5
def h57Block6_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,4,5,6,7,8,9,10],[0,1]),([0,1,2,3,4,6],[0,1,2,6,7,8,9,10,11],[0]),([0,1,2,3,4,14],[0,1,2,6,7,8,9,10,12],[0,1]),([0,1,2,4,15],[0,2,3,7,8,13,14,15],[0]),([0,1,2,4,16],[0,2,7,16,17,18,19],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h57Test6_0 : checkNodesBT h57W h57G h57Mask h57Pools h57Autos h57Bucket5 6 h57Block6_0 = true := by decide +kernel
def h57Nodes6 : List NodeSpec := h57Block6_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h57Check6 : checkNodesBT h57W h57G h57Mask h57Pools h57Autos h57Bucket5 6 h57Nodes6 = true := h57Test6_0
def h57Bucket6 : BT (List (List Nat)) := buildBucketsBT h57W h57Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h57Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h57G 6 xs.toFinset) h57Bucket6 := buildBucketsBT_sound (by decide) h57Pairs h57WOk h57PoolsOk h57AutosOk h57Bucket5Ok h57Check6
def h57Block7_0 : List NodeSpec := [([0,1,2,3,4],[0,1,7,8,9,10],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h57Test7_0 : checkNodesBT h57W h57G h57Mask h57Pools h57Autos h57Bucket6 7 h57Block7_0 = true := by decide +kernel
def h57Nodes7 : List NodeSpec := h57Block7_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h57Check7 : checkNodesBT h57W h57G h57Mask h57Pools h57Autos h57Bucket6 7 h57Nodes7 = true := h57Test7_0
def h57Bucket7 : BT (List (List Nat)) := buildBucketsBT h57W h57Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h57Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h57G 7 xs.toFinset) h57Bucket7 := buildBucketsBT_sound (by decide) h57Pairs h57WOk h57PoolsOk h57AutosOk h57Bucket6Ok h57Check7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h57Bound : Lower h57R h57G 8 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 3,1,9),(VAR 4,2,18),(VAR 5,1,33)]) (by decide +kernel) h57Bucket7Ok (by decide +kernel)
def h59R : List Nat := varsOf 61
def h59G : Nat := 0xfffafaaafffaf0a0fffafaaafffaf0a0
def h59Pos : List Nat := [12,17,5,5,12,41,20,17,33,24,20,52,41,52,44,24]
def h59Neg : List Nat := [8,16,1,4,4,40,4,1,1,16,16,48,9,36,36,8]
def h59Mask : Nat := fullMask 16
def h59Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,4526,4484),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x6c5d,0x6058),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xd231,0x9021),(0xffff0000ffff0000ffff0000ffff0000,0xaec2,3586),(0xffffffff00000000ffffffff00000000,0x7920,0x6820)]
def h59Steps : List (Nat × Nat × Nat) := [(1,1,3),(3,2,5)]
def h59W : BT Decor := buildWiresBT 3 h59Base h59Steps
def h59AutoList : List (List (Nat × Nat)) := [[],[(2,4)]]
def h59Autos : BT (List (Nat × Nat)) := btOfList 1 h59AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Pairs : goodPairs h59G h59Pos h59Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59BaseOk : ∀ x ∈ h59Base, faithful h59Pos h59Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59WOk : btAll (fun x => faithful h59Pos h59Neg x ∧ x.1 < 2^128) h59W := buildWiresBT_faithful h59BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h59G = h59G) h59Autos := btAll_ofList (autos_of (by decide +kernel))
def h59SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 32,5),some (subcubeFast 1 0,4),some (subcubeFast 4 0,4),some (subcubeFast 8 0,5),some (subcubeFast 16 0,4),some (subcubeFast 32 0,5),some (subcubeFast 33 0,4)]
def h59Slices : BT (Option (Nat × Nat)) := btOfList 3 h59SliceList
def h59Specs : List PoolSpec := [(1,[]),(6,[]),(2,[]),(3,[]),(4,[]),(5,[]),(0,[])]
def h59Pools : BT (Option BoundPool) := buildPoolsBT 3 h59W h59R h59Slices h59Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Slice6 : Slice h59R h59G (subcubeFast 33 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h1Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Slice5 : Slice h59R h59G (subcubeFast 32 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h2Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Slice4 : Slice h59R h59G (subcubeFast 16 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h19Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Slice3 : Slice h59R h59G (subcubeFast 8 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h24Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Slice2 : Slice h59R h59G (subcubeFast 4 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h31Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Slice1 : Slice h59R h59G (subcubeFast 1 0) 4 := slice_fast_direct (zDead := 32) (by decide +kernel) h1Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Slice0 : Slice h59R h59G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h46Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h59R h59G p.1 p.2) h59Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h59R h59G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h59Slice0) (forall_cons (fun _ h => by cases h; exact h59Slice1) (forall_cons (fun _ h => by cases h; exact h59Slice2) (forall_cons (fun _ h => by cases h; exact h59Slice3) (forall_cons (fun _ h => by cases h; exact h59Slice4) (forall_cons (fun _ h => by cases h; exact h59Slice5) (forall_cons (fun _ h => by cases h; exact h59Slice6) (fun _ h => (List.not_mem_nil h).elim))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h59R h59G c) h59Pools := buildPoolsBT_sound h59SlicesOk
def h59Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h59G (4 - 1) xs.toFinset) h59Empty := trivial
def h59Block4_0 : List NodeSpec := nodesWithIdentity [([0,1,3,4,6],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test4_0 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Empty 4 h59Block4_0 = true := by decide +kernel
def h59Nodes4 : List NodeSpec := h59Block4_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Check4 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Empty 4 h59Nodes4 = true := h59Test4_0
def h59Bucket4 : BT (List (List Nat)) := buildBucketsBT h59W h59Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h59G 4 xs.toFinset) h59Bucket4 := buildBucketsBT_sound (by decide) h59Pairs h59WOk h59PoolsOk h59AutosOk h59EmptyOk h59Check4
def h59Block5_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5],[2,3,5,6])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test5_0 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket4 5 h59Block5_0 = true := by decide +kernel
def h59Nodes5 : List NodeSpec := h59Block5_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Check5 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket4 5 h59Nodes5 = true := h59Test5_0
def h59Bucket5 : BT (List (List Nat)) := buildBucketsBT h59W h59Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h59G 5 xs.toFinset) h59Bucket5 := buildBucketsBT_sound (by decide) h59Pairs h59WOk h59PoolsOk h59AutosOk h59Bucket4Ok h59Check5
def h59Block6_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4],[0,1,2,3,4,5,6])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test6_0 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket5 6 h59Block6_0 = true := by decide +kernel
def h59Nodes6 : List NodeSpec := h59Block6_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Check6 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket5 6 h59Nodes6 = true := h59Test6_0
def h59Bucket6 : BT (List (List Nat)) := buildBucketsBT h59W h59Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h59G 6 xs.toFinset) h59Bucket6 := buildBucketsBT_sound (by decide) h59Pairs h59WOk h59PoolsOk h59AutosOk h59Bucket5Ok h59Check6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Bound : Lower h59R h59G 7 := lower_of_forestBT (essPairs := [(VAR 0,4,5),(VAR 2,1,5),(VAR 3,4,12),(VAR 4,1,17),(VAR 5,1,33)]) (by decide +kernel) h59Bucket6Ok (by decide +kernel)
def h60R : List Nat := varsOf 62
def h60G : Nat := 0xfffcfffcfcccf0c0fffcfffcfcccf0c0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h60Bound : Lower h60R h60G 7 := carry_of (swaps := [(4,5),(0,1)]) (roots2 := h59R) (T2 := h59G) (by decide +kernel) h59Bound
def h0R : List Nat := varsOf 63
def h0G : Nat := 0xfee8eaa8ecc8e080fee8eaa8ecc8e080
def h0Pos : List Nat := [13,14,22,14,41,7,14,37,13,22,19,29,60,35,7,13,26,22,60,46,7,26,22,41,37,7,15,37,29,19,29,35,46,46,19,13,26,41,27,43,35,60,41,26,60,60,7,45,14,35,39,14,19,43,53,7,19,53,14,23,54,13,58,27,26,53,54,58,7,37,13,7,30,35,13,22,57,19,14,58,35,13,57]
def h0Neg : List Nat := [12,12,21,10,40,3,6,36,5,6,3,28,28,3,6,9,24,20,44,44,5,18,18,33,33,11,11,5,25,18,21,34,42,38,17,1,10,9,25,42,33,56,44,28,52,48,4,44,11,38,38,8,25,11,52,2,21,49,4,21,52,11,42,11,2,21,50,56,21,32,8,1,28,42,25,2,25,1,44,50,1,4,56]
def h0Mask : Nat := fullMask 83
def h0Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x736f2abf6c5ecff90edb1,0x13492ab31016c5f90a524),(0xcccccccccccccccccccccccccccccccc,0x1eb9dddbf49d7a67b666e,0x8a05e0a70093a6606668),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x24df63ecdf20b5f5edbef,0x241121d46dc02481e5bc7),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x6d549e429befb54ad995b,0x45748e0398ef1160d981b),(0xffff0000ffff0000ffff0000ffff0000,0x4b90fdb503a5470671e04,0x4951e1b503a4470631804),(0xffffffff00000000ffffffff00000000,0x5922e5266b7a3898c3090,0x4c22c5246b783818c0090)]
def h0Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(0,0,2),(1,0,2),(2,0,2),(3,0,2),(0,0,3),(1,0,3),(2,0,3),(3,0,3),(0,1,2),(3,1,2),(0,1,3),(1,1,3),(2,1,3),(3,1,3),(0,1,4),(3,1,4),(0,1,5),(3,1,5),(0,2,3),(1,0,27),(1,1,27),(1,2,3),(2,2,3),(3,2,3),(0,2,4),(3,2,4),(2,2,6),(3,3,4),(1,3,6),(2,3,6),(1,6,27),(3,0,30),(3,1,40),(1,3,40),(3,6,30),(1,0,31),(1,1,31),(1,6,31),(1,0,32),(1,6,32),(2,1,35),(0,2,7),(1,0,50),(1,1,50),(1,3,50),(2,3,50),(2,2,7),(3,2,7),(0,3,7),(3,3,7),(2,7,27),(1,0,55),(1,1,55),(2,30,55),(0,7,30),(1,0,57),(1,1,57),(2,2,57),(1,7,31),(2,7,31),(2,7,32),(1,1,58),(1,1,56),(2,2,8),(0,2,28),(1,8,27),(3,8,30),(1,8,31),(1,8,32),(3,1,60),(1,9,19),(3,0,20),(1,1,80),(0,2,80),(0,2,20),(2,3,12),(3,12,20),(3,9,20),(1,9,21),(2,2,22),(1,9,22),(1,31,52),(3,31,52),(0,2,44),(2,10,19),(0,10,20),(2,10,21),(2,10,22),(2,5,23),(1,11,19),(1,11,83),(3,11,20),(1,11,21),(1,11,22),(1,12,19),(1,1,85),(1,12,21),(1,12,22),(1,12,27),(1,12,31),(0,2,104),(3,1,14),(2,2,110),(1,1,73),(2,1,73),(1,23,73),(0,4,114),(0,2,70),(0,2,81),(2,1,92),(1,23,92)]
def h0W : BT Decor := buildWiresBT 7 h0Base h0Steps
def h0AutoList : List (List (Nat × Nat)) := [[],[(4,5),(0,1)]]
def h0Autos : BT (List (Nat × Nat)) := btOfList 1 h0AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Pairs : goodPairs h0G h0Pos h0Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0BaseOk : ∀ x ∈ h0Base, faithful h0Pos h0Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0WOk : btAll (fun x => faithful h0Pos h0Neg x ∧ x.1 < 2^128) h0W := buildWiresBT_faithful h0BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h0G = h0G) h0Autos := btAll_ofList (autos_of (by decide +kernel))
def h0SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,7),some (subcubeFast 0 2,7),some (subcubeFast 0 4,8),some (subcubeFast 0 8,8),some (subcubeFast 0 16,9),some (subcubeFast 0 17,5),some (subcubeFast 0 20,5),some (subcubeFast 0 32,9),some (subcubeFast 0 34,5),some (subcubeFast 1 0,8),some (subcubeFast 1 4,5),some (subcubeFast 1 8,5),some (subcubeFast 1 16,5),some (subcubeFast 1 32,7),some (subcubeFast 1 36,4),some (subcubeFast 2 0,8),some (subcubeFast 2 4,5),some (subcubeFast 2 8,5),some (subcubeFast 2 16,7),some (subcubeFast 2 17,4),some (subcubeFast 2 20,4),some (subcubeFast 2 32,5),some (subcubeFast 4 0,6),some (subcubeFast 4 1,4),some (subcubeFast 4 2,4),some (subcubeFast 4 16,5),some (subcubeFast 4 32,5),some (subcubeFast 4 48,4),some (subcubeFast 8 0,8),some (subcubeFast 8 1,5),some (subcubeFast 8 2,5),some (subcubeFast 8 16,5),some (subcubeFast 16 0,9),some (subcubeFast 16 1,5),some (subcubeFast 16 2,4),some (subcubeFast 16 4,5),some (subcubeFast 16 32,6),some (subcubeFast 18 0,5),some (subcubeFast 18 1,4),some (subcubeFast 24 0,5),some (subcubeFast 24 1,4),some (subcubeFast 32 0,9),some (subcubeFast 32 2,5),some (subcubeFast 33 2,4)]
def h0Slices : BT (Option (Nat × Nat)) := btOfList 6 h0SliceList
def h0Specs : List PoolSpec := [(9,[]),(15,[]),(32,[(0,0,1)]),(4,[(0,0,1)]),(41,[(0,0,1)]),(7,[(0,0,1)]),(9,[(0,2,3)]),(15,[(0,2,3)]),(32,[(0,0,1),(0,2,3)]),(4,[(0,0,1),(0,2,3)]),(41,[(0,0,1),(0,2,3)]),(7,[(0,0,1),(0,2,3)]),(0,[]),(28,[(0,0,1)]),(1,[]),(2,[(0,0,1)]),(2,[]),(22,[]),(3,[(0,0,1)]),(3,[]),(28,[]),(32,[(0,2,3)]),(4,[(0,2,3)]),(41,[(0,2,3)]),(7,[(0,2,3)]),(32,[(0,0,1),(0,2,3),(1,6,27)]),(4,[(0,0,1),(0,2,3),(1,6,27)]),(41,[(0,0,1),(0,2,3),(1,6,27)]),(7,[(0,0,1),(0,2,3),(1,6,27)]),(2,[(0,0,1),(1,6,27)]),(3,[(0,0,1),(1,6,27)]),(32,[]),(4,[]),(41,[]),(7,[]),(9,[(1,2,3)]),(15,[(1,2,3)]),(32,[(0,0,1),(1,2,3)]),(4,[(0,0,1),(1,2,3)]),(41,[(0,0,1),(1,2,3)]),(7,[(0,0,1),(1,2,3)]),(15,[(1,2,3),(3,0,30)]),(32,[(0,0,1),(1,2,3),(3,0,30)]),(4,[(0,0,1),(1,2,3),(3,0,30)]),(41,[(0,0,1),(1,2,3),(3,0,30)]),(7,[(0,0,1),(1,2,3),(3,0,30)]),(10,[]),(32,[(1,2,3)]),(4,[(1,2,3)]),(41,[(1,2,3)]),(7,[(1,2,3)]),(32,[(0,0,1),(1,2,3),(3,6,30)]),(4,[(0,0,1),(1,2,3),(3,6,30)]),(41,[(0,0,1),(1,2,3),(3,6,30)]),(7,[(0,0,1),(1,2,3),(3,6,30)]),(9,[(2,2,3)]),(15,[(2,2,3)]),(32,[(0,0,1),(2,2,3)]),(4,[(0,0,1),(2,2,3)]),(41,[(0,0,1),(2,2,3)]),(7,[(0,0,1),(2,2,3)]),(32,[(2,2,3)]),(4,[(2,2,3)]),(41,[(2,2,3)]),(7,[(2,2,3)]),(32,[(0,0,1),(2,2,3),(1,6,31)]),(4,[(0,0,1),(2,2,3),(1,6,31)]),(41,[(0,0,1),(2,2,3),(1,6,31)]),(7,[(0,0,1),(2,2,3),(1,6,31)]),(28,[(0,0,1),(1,6,31)]),(2,[(0,0,1),(1,6,31)]),(11,[]),(9,[(3,2,3)]),(15,[(3,2,3)]),(32,[(0,0,1),(3,2,3)]),(4,[(0,0,1),(3,2,3)]),(41,[(0,0,1),(3,2,3)]),(7,[(0,0,1),(3,2,3)]),(32,[(3,2,3)]),(4,[(3,2,3)]),(41,[(3,2,3)]),(7,[(3,2,3)]),(32,[(0,0,1),(3,2,3),(1,6,32)]),(4,[(0,0,1),(3,2,3),(1,6,32)]),(41,[(0,0,1),(3,2,3),(1,6,32)]),(7,[(0,0,1),(3,2,3),(1,6,32)]),(32,[(0,0,1),(2,2,6)]),(4,[(0,0,1),(2,2,6)]),(41,[(0,0,1),(2,2,6)]),(7,[(0,0,1),(2,2,6)]),(32,[(0,0,1),(1,3,6)]),(4,[(0,0,1),(1,3,6)]),(41,[(0,0,1),(1,3,6)]),(7,[(0,0,1),(1,3,6)]),(32,[(0,0,1),(2,3,6)]),(4,[(0,0,1),(2,3,6)]),(41,[(0,0,1),(2,3,6)]),(7,[(0,0,1),(2,3,6)]),(32,[(1,0,1)]),(4,[(1,0,1)]),(41,[(1,0,1)]),(7,[(1,0,1)]),(2,[(1,0,1)]),(0,[(0,2,3)]),(28,[(1,0,1)]),(32,[(1,0,1),(0,2,3)]),(4,[(1,0,1),(0,2,3)]),(41,[(1,0,1),(0,2,3)]),(7,[(1,0,1),(0,2,3)]),(1,[(0,2,3)]),(9,[(0,2,3),(0,2,7)]),(28,[(1,0,1),(0,2,7)]),(15,[(0,2,3),(0,2,7)]),(32,[(0,2,3),(1,0,1),(0,2,7)]),(4,[(0,2,3),(1,0,1),(0,2,7)]),(41,[(0,2,3),(1,0,1),(0,2,7)]),(7,[(0,2,3),(1,0,1),(0,2,7)]),(32,[(1,0,1),(0,2,7)]),(41,[(1,0,1),(0,2,7)]),(29,[]),(3,[(1,0,1)]),(9,[(0,2,3),(2,7,27)]),(15,[(0,2,3),(2,7,27)]),(2,[(1,0,1),(2,7,27)]),(32,[(1,0,1),(0,2,3),(2,7,27)]),(4,[(1,0,1),(0,2,3),(2,7,27)]),(41,[(1,0,1),(0,2,3),(2,7,27)]),(7,[(1,0,1),(0,2,3),(2,7,27)]),(3,[(1,0,1),(2,7,27)]),(32,[(1,0,1),(1,2,3)]),(4,[(1,0,1),(1,2,3)]),(41,[(1,0,1),(1,2,3)]),(7,[(1,0,1),(1,2,3)]),(9,[(0,2,7)]),(15,[(0,2,7)]),(32,[(1,2,3),(1,0,1),(0,2,7)]),(41,[(1,2,3),(1,0,1),(0,2,7)]),(0,[(1,2,3)]),(4,[(1,0,1),(0,2,7)]),(7,[(1,0,1),(0,2,7)]),(9,[(2,2,7)]),(15,[(2,2,7)]),(1,[(1,2,3)]),(32,[(1,0,1),(2,2,7)]),(4,[(1,0,1),(2,2,7)]),(41,[(1,0,1),(2,2,7)]),(7,[(1,0,1),(2,2,7)]),(9,[(1,2,3),(0,7,30)]),(15,[(1,2,3),(0,7,30)]),(28,[(1,0,1),(0,7,30)]),(32,[(1,0,1),(1,2,3),(0,7,30)]),(4,[(1,0,1),(1,2,3),(0,7,30)]),(41,[(1,0,1),(1,2,3),(0,7,30)]),(7,[(1,0,1),(1,2,3),(0,7,30)]),(9,[(1,2,3),(3,1,40)]),(2,[(3,1,40)]),(32,[(1,2,3),(3,0,30),(3,1,40)]),(4,[(1,2,3),(3,0,30),(3,1,40)]),(41,[(1,2,3),(3,0,30),(3,1,40)]),(7,[(1,2,3),(3,0,30),(3,1,40)]),(0,[(2,2,3)]),(32,[(1,0,1),(2,2,3)]),(4,[(1,0,1),(2,2,3)]),(41,[(1,0,1),(2,2,3)]),(7,[(1,0,1),(2,2,3)]),(1,[(2,2,3)]),(23,[]),(9,[(2,2,3),(0,3,7)]),(15,[(2,2,3),(0,3,7)]),(2,[(1,0,1),(0,3,7)]),(32,[(2,2,3),(1,0,1),(0,3,7)]),(4,[(2,2,3),(1,0,1),(0,3,7)]),(32,[(1,0,1),(0,3,7)]),(41,[(2,2,3),(1,0,1),(0,3,7)]),(7,[(2,2,3),(1,0,1),(0,3,7)]),(41,[(1,0,1),(0,3,7)]),(9,[(2,2,3),(1,7,31)]),(15,[(2,2,3),(1,7,31)]),(28,[(1,0,1),(1,7,31)]),(2,[(1,0,1),(1,7,31)]),(32,[(1,0,1),(2,2,3),(1,7,31)]),(4,[(1,0,1),(2,2,3),(1,7,31)]),(41,[(1,0,1),(2,2,3),(1,7,31)]),(7,[(1,0,1),(2,2,3),(1,7,31)]),(28,[(1,0,1),(2,7,31)]),(2,[(1,0,1),(2,7,31)]),(9,[(2,2,3),(2,7,31)]),(15,[(2,2,3),(2,7,31)]),(32,[(1,0,1),(2,2,3),(2,7,31)]),(4,[(1,0,1),(2,2,3),(2,7,31)]),(41,[(1,0,1),(2,2,3),(2,7,31)]),(7,[(1,0,1),(2,2,3),(2,7,31)]),(32,[(1,0,1),(3,2,3)]),(4,[(1,0,1),(3,2,3)]),(41,[(1,0,1),(3,2,3)]),(7,[(1,0,1),(3,2,3)]),(9,[(3,2,3),(0,2,7)]),(15,[(3,2,3),(0,2,7)]),(32,[(3,2,3),(1,0,1),(0,2,7)]),(4,[(3,2,3),(1,0,1),(0,2,7)]),(41,[(3,2,3),(1,0,1),(0,2,7)]),(7,[(3,2,3),(1,0,1),(0,2,7)]),(28,[(1,0,1),(2,2,7),(2,30,55)]),(0,[(3,2,3)]),(9,[(3,2,3),(2,7,32)]),(15,[(3,2,3),(2,7,32)]),(32,[(1,0,1),(3,2,3),(2,7,32)]),(4,[(1,0,1),(3,2,3),(2,7,32)]),(41,[(1,0,1),(3,2,3),(2,7,32)]),(7,[(1,0,1),(3,2,3),(2,7,32)]),(0,[(1,3,50)]),(9,[(0,2,7),(1,3,50)]),(15,[(0,2,7),(1,3,50)]),(3,[(1,0,1),(0,2,7)]),(1,[(1,3,50)]),(32,[(1,0,1),(0,2,7),(1,3,50)]),(41,[(1,0,1),(0,2,7),(1,3,50)]),(4,[(1,0,1),(0,2,7),(1,3,50)]),(7,[(1,0,1),(0,2,7),(1,3,50)]),(0,[(2,3,50)]),(9,[(0,2,7),(2,3,50)]),(15,[(0,2,7),(2,3,50)]),(1,[(2,3,50)]),(32,[(1,0,1),(0,2,7),(2,3,50)]),(41,[(1,0,1),(0,2,7),(2,3,50)]),(4,[(1,0,1),(0,2,7),(2,3,50)]),(7,[(1,0,1),(0,2,7),(2,3,50)]),(9,[(0,2,7),(0,3,7)]),(15,[(0,2,7),(0,3,7)]),(9,[(0,3,7)]),(15,[(0,3,7)]),(32,[(1,0,1),(0,2,7),(0,3,7)]),(41,[(1,0,1),(0,2,7),(0,3,7)]),(4,[(1,0,1),(0,3,7)]),(7,[(1,0,1),(0,3,7)]),(9,[(3,3,7)]),(15,[(3,3,7)]),(32,[(1,0,1),(0,2,7),(3,3,7)]),(41,[(1,0,1),(0,2,7),(3,3,7)]),(32,[(1,0,1),(3,3,7)]),(4,[(1,0,1),(3,3,7)]),(41,[(1,0,1),(3,3,7)]),(7,[(1,0,1),(3,3,7)]),(2,[(1,0,1),(3,3,7)]),(2,[(1,0,1),(1,3,50)]),(9,[(3,2,7)]),(15,[(3,2,7)]),(32,[(1,0,1),(3,2,7)]),(4,[(1,0,1),(3,2,7)]),(41,[(1,0,1),(3,2,7)]),(7,[(1,0,1),(3,2,7)]),(9,[(0,2,7),(3,2,7)]),(15,[(0,2,7),(3,2,7)]),(32,[(1,0,1),(0,2,7),(3,2,7)]),(41,[(1,0,1),(0,2,7),(3,2,7)]),(28,[(1,0,1),(3,2,7)]),(3,[(1,0,1),(3,2,7)]),(32,[(1,0,1),(3,2,7),(0,3,7)]),(41,[(1,0,1),(3,2,7),(0,3,7)]),(32,[(1,0,1),(3,2,7),(3,3,7)]),(41,[(1,0,1),(3,2,7),(3,3,7)]),(9,[(0,3,7),(2,2,57)]),(15,[(0,3,7),(2,2,57)]),(0,[(2,2,57)]),(3,[(1,0,1),(2,2,57)]),(32,[(1,0,1),(0,3,7),(2,2,57)]),(4,[(1,0,1),(0,3,7),(2,2,57)]),(41,[(1,0,1),(0,3,7),(2,2,57)]),(7,[(1,0,1),(0,3,7),(2,2,57)]),(32,[(2,0,1)]),(4,[(2,0,1)]),(41,[(2,0,1)]),(7,[(2,0,1)]),(32,[(2,0,1),(0,2,3)]),(4,[(2,0,1),(0,2,3)]),(41,[(2,0,1),(0,2,3)]),(7,[(2,0,1),(0,2,3)]),(15,[(0,2,3),(1,0,27)]),(2,[(2,0,1),(1,0,27)]),(1,[(0,2,3),(1,0,27)]),(28,[(2,0,1)]),(32,[(2,0,1),(0,2,3),(1,0,27)]),(4,[(2,0,1),(0,2,3),(1,0,27)]),(41,[(2,0,1),(0,2,3),(1,0,27)]),(7,[(2,0,1),(0,2,3),(1,0,27)]),(3,[(2,0,1),(1,0,27)]),(30,[]),(2,[(2,0,1)]),(3,[(2,0,1)]),(32,[(2,0,1),(0,2,3),(1,8,27)]),(4,[(2,0,1),(0,2,3),(1,8,27)]),(41,[(2,0,1),(0,2,3),(1,8,27)]),(7,[(2,0,1),(0,2,3),(1,8,27)]),(15,[(0,2,3),(1,8,27)]),(2,[(2,0,1),(1,8,27)]),(3,[(2,0,1),(1,8,27)]),(32,[(2,0,1),(1,2,3)]),(4,[(2,0,1),(1,2,3)]),(41,[(2,0,1),(1,2,3)]),(7,[(2,0,1),(1,2,3)]),(15,[(1,2,3),(3,8,30)]),(32,[(2,0,1),(1,2,3),(3,8,30)]),(4,[(2,0,1),(1,2,3),(3,8,30)]),(41,[(2,0,1),(1,2,3),(3,8,30)]),(7,[(2,0,1),(1,2,3),(3,8,30)]),(28,[(2,0,1),(3,8,30)]),(32,[(2,0,1),(2,2,3)]),(4,[(2,0,1),(2,2,3)]),(41,[(2,0,1),(2,2,3)]),(7,[(2,0,1),(2,2,3)]),(32,[(2,0,1),(2,2,3),(1,8,31)]),(4,[(2,0,1),(2,2,3),(1,8,31)]),(41,[(2,0,1),(2,2,3),(1,8,31)]),(7,[(2,0,1),(2,2,3),(1,8,31)]),(15,[(2,2,3),(1,8,31)]),(2,[(2,0,1),(1,8,31)]),(28,[(2,0,1),(1,8,31)]),(32,[(2,0,1),(3,2,3)]),(4,[(2,0,1),(3,2,3)]),(41,[(2,0,1),(3,2,3)]),(7,[(2,0,1),(3,2,3)]),(32,[(2,0,1),(3,2,3),(1,8,32)]),(4,[(2,0,1),(3,2,3),(1,8,32)]),(41,[(2,0,1),(3,2,3),(1,8,32)]),(7,[(2,0,1),(3,2,3),(1,8,32)]),(15,[(3,2,3),(1,8,32)]),(1,[(3,2,3)]),(32,[(2,0,1),(2,2,8)]),(4,[(2,0,1),(2,2,8)]),(41,[(2,0,1),(2,2,8)]),(7,[(2,0,1),(2,2,8)]),(15,[(2,2,8)]),(32,[(0,0,2)]),(4,[(0,0,2)]),(41,[(0,0,2)]),(7,[(0,0,2)]),(9,[(0,1,2)]),(32,[(0,0,2),(0,1,2)]),(4,[(0,0,2),(0,1,2)]),(41,[(0,0,2),(0,1,2)]),(7,[(0,0,2),(0,1,2)]),(15,[(0,0,2)]),(18,[(0,0,2)]),(13,[(0,2,7)]),(17,[]),(18,[]),(4,[(1,0,1),(0,2,7),(1,0,50)]),(3,[(0,1,2)]),(28,[(0,1,2)]),(3,[(0,0,2)]),(28,[(0,0,2)]),(32,[(0,1,2)]),(4,[(0,1,2)]),(41,[(0,1,2)]),(7,[(0,1,2)]),(9,[(3,1,2)]),(32,[(0,0,2),(3,1,2)]),(4,[(0,0,2),(3,1,2)]),(41,[(0,0,2),(3,1,2)]),(7,[(0,0,2),(3,1,2)]),(2,[(1,0,1),(1,0,55)]),(1,[(0,0,2)]),(16,[]),(33,[]),(5,[]),(13,[(2,2,7)]),(3,[(3,1,2)]),(28,[(3,1,2)]),(32,[(3,1,2)]),(4,[(3,1,2)]),(41,[(3,1,2)]),(7,[(3,1,2)]),(9,[(0,1,3)]),(2,[(0,1,3)]),(32,[(0,0,2),(0,1,3)]),(4,[(0,0,2),(0,1,3)]),(41,[(0,0,2),(0,1,3)]),(7,[(0,0,2),(0,1,3)]),(32,[(0,1,3)]),(4,[(0,1,3)]),(41,[(0,1,3)]),(7,[(0,1,3)]),(2,[(0,1,3),(1,9,19)]),(32,[(0,0,2),(0,1,3),(1,9,19)]),(4,[(0,0,2),(0,1,3),(1,9,19)]),(41,[(0,0,2),(0,1,3),(1,9,19)]),(7,[(0,0,2),(0,1,3),(1,9,19)]),(0,[(0,1,3)]),(9,[(1,1,3)]),(2,[(1,1,3)]),(32,[(0,0,2),(1,1,3)]),(4,[(0,0,2),(1,1,3)]),(41,[(0,0,2),(1,1,3)]),(7,[(0,0,2),(1,1,3)]),(15,[(0,0,2),(3,0,20)]),(2,[(1,1,3),(3,0,20)]),(28,[(0,0,2),(3,0,20)]),(32,[(0,0,2),(1,1,3),(3,0,20)]),(4,[(0,0,2),(1,1,3),(3,0,20)]),(41,[(0,0,2),(1,1,3),(3,0,20)]),(7,[(0,0,2),(1,1,3),(3,0,20)]),(41,[(1,1,3),(3,0,20)]),(3,[(3,0,2)]),(15,[(3,0,2)]),(28,[(3,0,2)]),(0,[(1,1,3)]),(32,[(1,1,3)]),(4,[(1,1,3)]),(32,[(3,0,2)]),(32,[(3,0,2),(1,1,3)]),(4,[(3,0,2)]),(4,[(3,0,2),(1,1,3)]),(41,[(1,1,3)]),(7,[(1,1,3)]),(41,[(3,0,2)]),(7,[(3,0,2)]),(9,[(1,1,3),(0,2,20)]),(32,[(0,0,2),(1,1,3),(0,2,20)]),(4,[(0,0,2),(1,1,3),(0,2,20)]),(41,[(0,0,2),(1,1,3),(0,2,20)]),(7,[(0,0,2),(1,1,3),(0,2,20)]),(15,[(0,0,2),(0,2,20)]),(28,[(0,0,2),(0,2,20)]),(41,[(1,1,3),(0,2,20)]),(32,[(0,0,2),(1,1,3),(3,9,20)]),(4,[(0,0,2),(1,1,3),(3,9,20)]),(41,[(0,0,2),(1,1,3),(3,9,20)]),(7,[(0,0,2),(1,1,3),(3,9,20)]),(15,[(0,0,2),(3,9,20)]),(2,[(1,1,3),(3,9,20)]),(28,[(0,0,2),(3,9,20)]),(9,[(2,1,3)]),(2,[(2,1,3)]),(32,[(0,0,2),(2,1,3)]),(4,[(0,0,2),(2,1,3)]),(41,[(0,0,2),(2,1,3)]),(7,[(0,0,2),(2,1,3)]),(2,[(2,1,3),(1,0,1)]),(3,[(1,0,1),(0,2,7),(1,1,50)]),(18,[(0,2,7)]),(13,[(2,1,3)]),(7,[(1,0,1),(0,2,7),(1,1,50)]),(38,[]),(32,[(2,1,3)]),(4,[(2,1,3)]),(41,[(2,1,3)]),(7,[(2,1,3)]),(32,[(0,0,2),(2,1,3),(1,9,21)]),(4,[(0,0,2),(2,1,3),(1,9,21)]),(41,[(0,0,2),(2,1,3),(1,9,21)]),(7,[(0,0,2),(2,1,3),(1,9,21)]),(28,[(0,0,2),(1,9,21)]),(2,[(2,1,3),(1,9,21)]),(9,[(3,1,3)]),(2,[(3,1,3)]),(32,[(0,0,2),(3,1,3)]),(4,[(0,0,2),(3,1,3)]),(41,[(0,0,2),(3,1,3)]),(7,[(0,0,2),(3,1,3)]),(32,[(3,1,3)]),(4,[(3,1,3)]),(41,[(3,1,3)]),(7,[(3,1,3)]),(32,[(0,0,2),(3,1,3),(1,9,22)]),(4,[(0,0,2),(3,1,3),(1,9,22)]),(41,[(0,0,2),(3,1,3),(1,9,22)]),(7,[(0,0,2),(3,1,3),(1,9,22)]),(15,[(0,0,2),(1,9,22)]),(2,[(3,1,3),(1,9,22)]),(3,[(0,0,2),(1,9,22)]),(43,[]),(13,[]),(0,[(1,1,50)]),(13,[(2,2,3)]),(32,[(1,0,1),(0,2,7),(1,1,50)]),(4,[(1,0,1),(0,2,7),(1,1,50)]),(41,[(1,0,1),(0,2,7),(1,1,50)]),(2,[(1,0,1),(3,31,52)]),(9,[(2,2,3),(3,31,52)]),(9,[(0,2,4)]),(20,[]),(15,[(0,2,4),(0,2,7)]),(1,[(0,2,4)]),(13,[(0,2,4)]),(15,[(0,2,4)]),(0,[(0,2,4)]),(28,[(0,2,4)]),(3,[(0,2,4)]),(41,[(0,2,4)]),(7,[(0,2,4)]),(9,[(3,3,4)]),(1,[(3,3,4)]),(13,[(3,3,4)]),(15,[(3,3,4)]),(0,[(3,3,4)]),(41,[(3,3,4)]),(7,[(3,3,4)]),(31,[]),(32,[(0,0,2),(0,2,3)]),(4,[(0,0,2),(0,2,3)]),(41,[(0,0,2),(0,2,3)]),(7,[(0,0,2),(0,2,3)]),(2,[(1,0,27)]),(32,[(0,0,2),(0,2,3),(1,0,27)]),(4,[(0,0,2),(0,2,3),(1,0,27)]),(41,[(0,0,2),(0,2,3),(1,0,27)]),(7,[(0,0,2),(0,2,3),(1,0,27)]),(32,[(0,0,2),(2,2,3)]),(4,[(0,0,2),(2,2,3)]),(41,[(0,0,2),(2,2,3)]),(7,[(0,0,2),(2,2,3)]),(2,[(1,0,31)]),(28,[(0,0,2),(1,0,31)]),(32,[(0,0,2),(2,2,3),(1,0,31)]),(4,[(0,0,2),(2,2,3),(1,0,31)]),(41,[(0,0,2),(2,2,3),(1,0,31)]),(7,[(0,0,2),(2,2,3),(1,0,31)]),(32,[(1,0,2)]),(4,[(1,0,2)]),(41,[(1,0,2)]),(7,[(1,0,2)]),(15,[(1,0,2)]),(28,[(1,0,2)]),(32,[(1,0,2),(0,1,3)]),(4,[(1,0,2),(0,1,3)]),(41,[(1,0,2),(0,1,3)]),(7,[(1,0,2),(0,1,3)]),(9,[(0,1,3),(2,2,7)]),(15,[(2,2,7),(1,0,55)]),(18,[(2,2,7),(1,0,55)]),(13,[(0,1,3),(2,2,7)]),(42,[]),(9,[(0,1,3),(2,10,19)]),(32,[(1,0,2),(0,1,3),(2,10,19)]),(4,[(1,0,2),(0,1,3),(2,10,19)]),(41,[(1,0,2),(0,1,3),(2,10,19)]),(7,[(1,0,2),(0,1,3),(2,10,19)]),(3,[(1,0,2)]),(32,[(1,0,2),(1,1,3)]),(4,[(1,0,2),(1,1,3)]),(41,[(1,0,2),(1,1,3)]),(7,[(1,0,2),(1,1,3)]),(15,[(0,2,20)]),(41,[(1,0,2),(1,1,3),(0,2,20)]),(32,[(1,1,3),(0,2,20)]),(4,[(1,1,3),(0,2,20)]),(7,[(1,1,3),(0,2,20)]),(9,[(1,1,3),(0,10,20)]),(15,[(1,0,2),(0,10,20)]),(28,[(1,0,2),(0,10,20)]),(32,[(1,0,2),(1,1,3),(0,10,20)]),(4,[(1,0,2),(1,1,3),(0,10,20)]),(41,[(1,0,2),(1,1,3),(0,10,20)]),(7,[(1,0,2),(1,1,3),(0,10,20)]),(32,[(1,0,2),(2,1,3)]),(4,[(1,0,2),(2,1,3)]),(41,[(1,0,2),(2,1,3)]),(7,[(1,0,2),(2,1,3)]),(9,[(2,1,3),(2,10,21)]),(28,[(1,0,2),(2,10,21)]),(32,[(1,0,2),(2,1,3),(2,10,21)]),(4,[(1,0,2),(2,1,3),(2,10,21)]),(41,[(1,0,2),(2,1,3),(2,10,21)]),(7,[(1,0,2),(2,1,3),(2,10,21)]),(0,[(2,1,3)]),(0,[(3,1,3)]),(32,[(1,0,2),(3,1,3)]),(4,[(1,0,2),(3,1,3)]),(41,[(1,0,2),(3,1,3)]),(7,[(1,0,2),(3,1,3)]),(9,[(3,1,3),(2,2,22)]),(15,[(2,2,22)]),(7,[(1,0,2),(3,1,3),(2,2,22)]),(32,[(3,1,3),(2,2,22)]),(4,[(3,1,3),(2,2,22)]),(41,[(3,1,3),(2,2,22)]),(7,[(3,1,3),(2,2,22)]),(9,[(3,1,3),(2,10,22)]),(15,[(1,0,2),(2,10,22)]),(32,[(1,0,2),(3,1,3),(2,10,22)]),(4,[(1,0,2),(3,1,3),(2,10,22)]),(41,[(1,0,2),(3,1,3),(2,10,22)]),(7,[(1,0,2),(3,1,3),(2,10,22)]),(3,[(1,0,2),(2,10,22)]),(9,[(0,1,4),(2,2,7)]),(2,[(0,1,4)]),(0,[(0,1,4)]),(13,[(0,1,4),(2,2,7)]),(19,[]),(32,[(2,0,2)]),(4,[(2,0,2)]),(41,[(2,0,2)]),(7,[(2,0,2)]),(32,[(2,0,2),(0,1,3)]),(4,[(2,0,2),(0,1,3)]),(41,[(2,0,2),(0,1,3)]),(7,[(2,0,2),(0,1,3)]),(15,[(2,0,2)]),(28,[(2,0,2)]),(2,[(1,0,1),(0,3,7),(1,0,57)]),(18,[(2,0,2)]),(13,[(0,3,7)]),(4,[(1,0,1),(0,3,7),(1,0,57)]),(41,[(1,0,1),(0,3,7),(1,0,57)]),(32,[(2,0,2),(0,1,3),(1,11,19)]),(4,[(2,0,2),(0,1,3),(1,11,19)]),(41,[(2,0,2),(0,1,3),(1,11,19)]),(7,[(2,0,2),(0,1,3),(1,11,19)]),(32,[(2,0,2),(1,1,3)]),(4,[(2,0,2),(1,1,3)]),(41,[(2,0,2),(1,1,3)]),(7,[(2,0,2),(1,1,3)]),(3,[(2,0,2)]),(32,[(2,0,2),(1,1,3),(0,2,20)]),(4,[(2,0,2),(1,1,3),(0,2,20)]),(41,[(2,0,2),(1,1,3),(0,2,20)]),(7,[(2,0,2),(1,1,3),(0,2,20)]),(15,[(2,0,2),(0,2,20)]),(28,[(2,0,2),(0,2,20)]),(13,[(1,1,3),(0,2,20)]),(32,[(2,0,2),(1,1,3),(3,11,20)]),(4,[(2,0,2),(1,1,3),(3,11,20)]),(41,[(2,0,2),(1,1,3),(3,11,20)]),(7,[(2,0,2),(1,1,3),(3,11,20)]),(15,[(2,0,2),(3,11,20)]),(28,[(2,0,2),(3,11,20)]),(32,[(2,0,2),(2,1,3)]),(4,[(2,0,2),(2,1,3)]),(41,[(2,0,2),(2,1,3)]),(7,[(2,0,2),(2,1,3)]),(32,[(2,0,2),(2,1,3),(1,11,21)]),(4,[(2,0,2),(2,1,3),(1,11,21)]),(41,[(2,0,2),(2,1,3),(1,11,21)]),(7,[(2,0,2),(2,1,3),(1,11,21)]),(32,[(2,0,2),(3,1,3)]),(4,[(2,0,2),(3,1,3)]),(41,[(2,0,2),(3,1,3)]),(7,[(2,0,2),(3,1,3)]),(32,[(2,0,2),(3,1,3),(2,2,22)]),(41,[(2,0,2),(3,1,3),(2,2,22)]),(32,[(2,0,2),(3,1,3),(1,11,22)]),(4,[(2,0,2),(3,1,3),(1,11,22)]),(41,[(2,0,2),(3,1,3),(1,11,22)]),(7,[(2,0,2),(3,1,3),(1,11,22)]),(15,[(2,0,2),(1,11,22)]),(3,[(2,0,2),(1,11,22)]),(18,[(3,2,7)]),(32,[(1,0,1),(3,2,7),(1,1,56)]),(0,[(1,1,56)]),(2,[(3,3,4)]),(35,[]),(4,[(1,0,1),(3,2,7),(1,1,56)]),(7,[(1,0,1),(3,2,7),(1,1,56)]),(41,[(1,0,1),(3,2,7),(1,1,56)]),(0,[(3,1,2)]),(32,[(3,0,2),(3,1,2)]),(4,[(3,0,2),(3,1,2)]),(41,[(3,0,2),(3,1,2)]),(7,[(3,0,2),(3,1,2)]),(1,[(3,0,2)]),(32,[(3,0,2),(0,1,3)]),(4,[(3,0,2),(0,1,3)]),(41,[(3,0,2),(0,1,3)]),(7,[(3,0,2),(0,1,3)]),(9,[(0,1,3),(1,12,19)]),(2,[(0,1,3),(1,12,19)]),(32,[(3,0,2),(0,1,3),(1,12,19)]),(4,[(3,0,2),(0,1,3),(1,12,19)]),(41,[(3,0,2),(0,1,3),(1,12,19)]),(7,[(3,0,2),(0,1,3),(1,12,19)]),(41,[(3,0,2),(1,1,3)]),(7,[(3,0,2),(1,1,3)]),(9,[(1,1,3),(0,2,80)]),(3,[(0,2,80)]),(15,[(3,0,20),(0,2,80)]),(28,[(3,0,20),(0,2,80)]),(32,[(1,1,3),(3,0,20),(0,2,80)]),(4,[(1,1,3),(3,0,20),(0,2,80)]),(41,[(1,1,3),(3,0,20),(0,2,80)]),(7,[(1,1,3),(3,0,20),(0,2,80)]),(9,[(1,1,3),(3,12,20)]),(15,[(3,0,2),(3,12,20)]),(2,[(1,1,3),(3,12,20)]),(28,[(3,0,2),(3,12,20)]),(32,[(3,0,2),(1,1,3),(3,12,20)]),(4,[(3,0,2),(1,1,3),(3,12,20)]),(41,[(3,0,2),(1,1,3),(3,12,20)]),(7,[(3,0,2),(1,1,3),(3,12,20)]),(32,[(3,0,2),(2,1,3)]),(4,[(3,0,2),(2,1,3)]),(41,[(3,0,2),(2,1,3)]),(7,[(3,0,2),(2,1,3)]),(9,[(2,1,3),(1,12,21)]),(2,[(2,1,3),(1,12,21)]),(28,[(3,0,2),(1,12,21)]),(32,[(3,0,2),(2,1,3),(1,12,21)]),(4,[(3,0,2),(2,1,3),(1,12,21)]),(41,[(3,0,2),(2,1,3),(1,12,21)]),(7,[(3,0,2),(2,1,3),(1,12,21)]),(32,[(3,0,2),(3,1,3)]),(4,[(3,0,2),(3,1,3)]),(41,[(3,0,2),(3,1,3)]),(7,[(3,0,2),(3,1,3)]),(9,[(3,1,3),(1,12,22)]),(15,[(3,0,2),(1,12,22)]),(2,[(3,1,3),(1,12,22)]),(32,[(3,0,2),(3,1,3),(1,12,22)]),(4,[(3,0,2),(3,1,3),(1,12,22)]),(41,[(3,0,2),(3,1,3),(1,12,22)]),(7,[(3,0,2),(3,1,3),(1,12,22)]),(3,[(3,0,2),(1,12,22)]),(18,[(2,2,7)]),(9,[(2,2,7),(1,1,55)]),(2,[(1,0,1),(1,1,55)]),(32,[(1,0,1),(2,2,7),(1,1,55)]),(4,[(1,0,1),(2,2,7),(1,1,55)]),(41,[(1,0,1),(2,2,7),(1,1,55)]),(7,[(1,0,1),(2,2,7),(1,1,55)]),(8,[]),(18,[(3,0,2)]),(26,[]),(9,[(2,1,35)]),(13,[(2,1,35)]),(14,[]),(32,[(3,0,2),(0,2,3)]),(4,[(3,0,2),(0,2,3)]),(41,[(3,0,2),(0,2,3)]),(7,[(3,0,2),(0,2,3)]),(0,[(0,2,3),(1,1,27)]),(9,[(0,2,3),(1,1,27)]),(2,[(1,1,27)]),(3,[(1,1,27)]),(32,[(0,2,3),(1,1,27)]),(4,[(0,2,3),(1,1,27)]),(41,[(0,2,3),(1,1,27)]),(7,[(0,2,3),(1,1,27)]),(24,[]),(32,[(3,0,2),(2,2,3)]),(4,[(3,0,2),(2,2,3)]),(41,[(3,0,2),(2,2,3)]),(7,[(3,0,2),(2,2,3)]),(9,[(2,2,3),(1,1,31)]),(2,[(1,1,31)]),(7,[(3,0,2),(2,2,3),(1,1,31)]),(28,[(1,1,31)]),(32,[(2,2,3),(1,1,31)]),(4,[(2,2,3),(1,1,31)]),(41,[(2,2,3),(1,1,31)]),(7,[(2,2,3),(1,1,31)]),(2,[(1,3,40)]),(13,[(1,2,3)]),(28,[(3,0,30)]),(9,[(2,3,12)]),(2,[(2,3,12)]),(32,[(3,0,2),(2,3,12)]),(4,[(3,0,2),(2,3,12)]),(41,[(3,0,2),(2,3,12)]),(7,[(3,0,2),(2,3,12)]),(33,[(1,1,3)]),(3,[(3,0,2),(1,1,85)]),(18,[(3,0,2),(3,12,20)]),(32,[(0,0,3)]),(4,[(0,0,3)]),(41,[(0,0,3)]),(7,[(0,0,3)]),(9,[(0,1,4)]),(32,[(1,0,1),(0,3,7),(1,1,57)]),(28,[(0,1,4)]),(18,[(0,3,7)]),(13,[(0,1,4)]),(7,[(1,0,1),(0,3,7),(1,1,57)]),(12,[]),(0,[(1,1,57)]),(15,[(0,2,4),(0,3,7)]),(4,[(1,0,1),(0,3,7),(1,1,57)]),(41,[(1,0,1),(0,3,7),(1,1,57)]),(6,[]),(9,[(3,2,4)]),(2,[(1,0,1),(0,3,7),(1,1,57)]),(28,[(3,2,4)]),(1,[(3,2,4)]),(13,[(3,2,4)]),(15,[(3,2,4)]),(41,[(3,2,4)]),(7,[(3,2,4)]),(25,[]),(34,[]),(28,[(0,2,104)]),(2,[(1,12,31)]),(32,[(3,0,2),(2,2,3),(1,12,31)]),(4,[(3,0,2),(2,2,3),(1,12,31)]),(22,[(0,1,4)]),(7,[(3,0,2),(2,2,3),(1,12,31)]),(9,[(0,1,4),(2,5,23)]),(1,[(2,5,23)]),(28,[(0,1,4),(2,5,23)]),(41,[(3,0,2),(2,2,3),(1,12,31)]),(2,[(0,1,4),(2,5,23)]),(4,[(2,5,23)]),(36,[]),(41,[(0,1,4)]),(7,[(0,1,4)]),(39,[]),(9,[(3,1,4)]),(28,[(3,1,4)]),(13,[(3,1,4)]),(2,[(3,1,4)]),(41,[(3,1,4)]),(7,[(3,1,4)]),(32,[(1,0,3)]),(4,[(1,0,3)]),(41,[(1,0,3)]),(7,[(1,0,3)]),(15,[(1,0,3)]),(32,[(1,0,3),(3,1,3)]),(4,[(1,0,3),(3,1,3)]),(41,[(1,0,3),(3,1,3)]),(7,[(1,0,3),(3,1,3)]),(1,[(1,0,3)]),(9,[(3,1,14)]),(28,[(3,1,14)]),(32,[(1,0,3),(3,1,14)]),(4,[(1,0,3),(3,1,14)]),(41,[(1,0,3),(3,1,14)]),(7,[(1,0,3),(3,1,14)]),(9,[(3,1,14),(2,2,110)]),(0,[(2,2,110)]),(15,[(1,0,3),(2,2,110)]),(2,[(1,0,3),(3,1,14)]),(3,[(2,2,110)]),(28,[(3,1,14),(2,2,110)]),(32,[(1,0,3),(3,1,14),(2,2,110)]),(4,[(1,0,3),(3,1,14),(2,2,110)]),(41,[(1,0,3),(3,1,14),(2,2,110)]),(7,[(1,0,3),(3,1,14),(2,2,110)]),(28,[(0,2,28)]),(32,[(0,2,3),(1,0,27),(0,2,28)]),(15,[(0,2,3),(1,0,27),(0,2,28)]),(4,[(0,2,3),(1,0,27),(0,2,28)]),(3,[(0,1,4)]),(28,[(0,1,4),(0,2,28)]),(13,[(0,2,3)]),(7,[(0,2,3),(1,0,27),(0,2,28)]),(0,[(0,1,4),(2,5,23)]),(3,[(0,1,4),(2,5,23)]),(41,[(0,2,3),(1,0,27),(0,2,28)]),(0,[(0,1,4),(1,23,73)]),(3,[(0,1,4),(1,23,73)]),(28,[(0,1,4),(0,2,28),(1,23,73)]),(0,[(3,1,4)]),(18,[(0,2,3),(1,0,27),(0,2,28)]),(3,[(3,1,4)]),(0,[(0,1,5)]),(9,[(0,1,5)]),(28,[(0,1,5)]),(3,[(0,1,5)]),(2,[(0,1,5)]),(32,[(0,1,5)]),(4,[(0,1,5)]),(0,[(3,1,5)]),(9,[(3,1,5),(0,2,3)]),(9,[(3,1,5)]),(28,[(3,1,5)]),(3,[(3,1,5)]),(2,[(3,1,5),(1,0,27)]),(2,[(3,1,5)]),(32,[(3,1,5)]),(4,[(3,1,5)]),(21,[]),(0,[(1,1,73)]),(9,[(0,2,3),(1,1,73)]),(28,[(0,2,28),(1,1,73)]),(3,[(1,1,73)]),(2,[(1,0,27),(1,1,73)]),(17,[(0,4,114)]),(3,[(0,1,4),(1,23,73),(0,4,114)]),(13,[(0,2,3),(1,1,73)]),(0,[(2,1,73)]),(9,[(0,2,3),(2,1,73)]),(28,[(0,2,28),(2,1,73)]),(3,[(2,1,73)]),(2,[(1,0,27),(2,1,73)]),(37,[]),(13,[(0,2,3),(2,1,73)]),(9,[(0,2,4),(0,2,3)]),(28,[(0,2,4),(0,2,28)]),(13,[(0,2,4),(0,2,3)]),(9,[(3,2,4),(0,2,3)]),(0,[(3,2,4)]),(28,[(3,2,4),(0,2,28)]),(3,[(3,2,4)]),(13,[(3,2,4),(0,2,3)]),(27,[]),(32,[(2,0,3)]),(4,[(2,0,3)]),(41,[(2,0,3)]),(7,[(2,0,3)]),(40,[]),(18,[(3,3,7)]),(9,[(0,2,70)]),(15,[(3,3,7),(0,2,70)]),(3,[(0,2,70)]),(28,[(1,0,1),(0,2,70)]),(18,[(3,3,7),(0,2,70)]),(13,[(0,2,70)]),(2,[(1,12,27)]),(32,[(3,0,3)]),(4,[(3,0,3)]),(41,[(3,0,3)]),(7,[(3,0,3)]),(15,[(3,0,20)]),(3,[(1,1,80)]),(18,[(3,0,20)]),(13,[(1,1,3)]),(9,[(1,1,3),(0,2,81)]),(0,[(0,2,81)]),(15,[(3,0,20),(0,2,81)]),(28,[(0,2,81)]),(18,[(3,0,20),(0,2,81)]),(13,[(1,1,3),(0,2,81)]),(3,[(0,2,44)]),(32,[(2,2,3),(1,0,31),(0,2,44)]),(4,[(2,2,3),(1,0,31),(0,2,44)]),(7,[(2,2,3),(1,0,31),(0,2,44)]),(41,[(2,2,3),(1,0,31),(0,2,44)]),(0,[(0,1,4),(1,23,92)]),(9,[(3,1,5),(2,2,3)]),(2,[(3,1,5),(1,0,31)]),(9,[(2,2,3),(1,31,52)]),(2,[(1,0,1),(1,31,52)]),(13,[(2,2,3),(1,31,52)]),(0,[(2,1,92)]),(9,[(2,2,3),(2,1,92)]),(3,[(0,2,44),(2,1,92)]),(28,[(2,1,92)]),(2,[(1,0,31),(2,1,92)]),(13,[(2,2,3),(2,1,92)]),(32,[(0,2,3),(1,0,27)]),(4,[(0,2,3),(1,0,27)]),(41,[(0,2,3),(1,0,27)]),(7,[(0,2,3),(1,0,27)]),(3,[(1,0,27)]),(32,[(1,2,3),(3,0,30)]),(4,[(1,2,3),(3,0,30)]),(41,[(1,2,3),(3,0,30)]),(7,[(1,2,3),(3,0,30)]),(28,[(1,0,31)]),(32,[(2,2,3),(1,0,31)]),(4,[(2,2,3),(1,0,31)]),(41,[(2,2,3),(1,0,31)]),(7,[(2,2,3),(1,0,31)]),(32,[(3,2,3),(1,0,32)]),(4,[(3,2,3),(1,0,32)]),(41,[(3,2,3),(1,0,32)]),(7,[(3,2,3),(1,0,32)])]
def h0Pools : BT (Option BoundPool) := buildPoolsBT 10 h0W h0R h0Slices h0Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice43 : Slice h0R h0G (subcubeFast 33 2) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h1Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice42 : Slice h0R h0G (subcubeFast 32 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h2Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice41 : Slice h0R h0G (subcubeFast 32 0) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h3Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice40 : Slice h0R h0G (subcubeFast 24 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h13Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice39 : Slice h0R h0G (subcubeFast 24 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h14Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice38 : Slice h0R h0G (subcubeFast 18 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h15Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice37 : Slice h0R h0G (subcubeFast 18 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h16Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice36 : Slice h0R h0G (subcubeFast 16 32) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h17Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice35 : Slice h0R h0G (subcubeFast 16 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h18Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice34 : Slice h0R h0G (subcubeFast 16 2) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h19Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice33 : Slice h0R h0G (subcubeFast 16 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h20Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice32 : Slice h0R h0G (subcubeFast 16 0) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h21Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice31 : Slice h0R h0G (subcubeFast 8 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h22Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice30 : Slice h0R h0G (subcubeFast 8 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h24Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice29 : Slice h0R h0G (subcubeFast 8 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h25Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice28 : Slice h0R h0G (subcubeFast 8 0) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h26Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice27 : Slice h0R h0G (subcubeFast 4 48) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h4Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice26 : Slice h0R h0G (subcubeFast 4 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h29Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice25 : Slice h0R h0G (subcubeFast 4 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h30Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice24 : Slice h0R h0G (subcubeFast 4 2) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h31Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice23 : Slice h0R h0G (subcubeFast 4 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h32Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice22 : Slice h0R h0G (subcubeFast 4 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h33Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice21 : Slice h0R h0G (subcubeFast 2 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h34Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice20 : Slice h0R h0G (subcubeFast 2 20) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h35Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice19 : Slice h0R h0G (subcubeFast 2 17) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h15Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice18 : Slice h0R h0G (subcubeFast 2 16) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h36Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice17 : Slice h0R h0G (subcubeFast 2 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h37Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice16 : Slice h0R h0G (subcubeFast 2 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h38Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice15 : Slice h0R h0G (subcubeFast 2 0) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h39Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice14 : Slice h0R h0G (subcubeFast 1 36) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h40Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice13 : Slice h0R h0G (subcubeFast 1 32) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h41Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice12 : Slice h0R h0G (subcubeFast 1 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h42Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice11 : Slice h0R h0G (subcubeFast 1 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h43Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice10 : Slice h0R h0G (subcubeFast 1 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h44Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice9 : Slice h0R h0G (subcubeFast 1 0) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h45Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice8 : Slice h0R h0G (subcubeFast 0 34) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h46Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice7 : Slice h0R h0G (subcubeFast 0 32) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h47Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice6 : Slice h0R h0G (subcubeFast 0 20) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h48Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice5 : Slice h0R h0G (subcubeFast 0 17) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h49Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice4 : Slice h0R h0G (subcubeFast 0 16) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h50Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice3 : Slice h0R h0G (subcubeFast 0 8) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h51Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice2 : Slice h0R h0G (subcubeFast 0 4) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h57Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice1 : Slice h0R h0G (subcubeFast 0 2) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h59Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice0 : Slice h0R h0G (subcubeFast 0 1) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h60Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h0R h0G p.1 p.2) h0Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h0R h0G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h0Slice0) (forall_cons (fun _ h => by cases h; exact h0Slice1) (forall_cons (fun _ h => by cases h; exact h0Slice2) (forall_cons (fun _ h => by cases h; exact h0Slice3) (forall_cons (fun _ h => by cases h; exact h0Slice4) (forall_cons (fun _ h => by cases h; exact h0Slice5) (forall_cons (fun _ h => by cases h; exact h0Slice6) (forall_cons (fun _ h => by cases h; exact h0Slice7) (forall_cons (fun _ h => by cases h; exact h0Slice8) (forall_cons (fun _ h => by cases h; exact h0Slice9) (forall_cons (fun _ h => by cases h; exact h0Slice10) (forall_cons (fun _ h => by cases h; exact h0Slice11) (forall_cons (fun _ h => by cases h; exact h0Slice12) (forall_cons (fun _ h => by cases h; exact h0Slice13) (forall_cons (fun _ h => by cases h; exact h0Slice14) (forall_cons (fun _ h => by cases h; exact h0Slice15) (forall_cons (fun _ h => by cases h; exact h0Slice16) (forall_cons (fun _ h => by cases h; exact h0Slice17) (forall_cons (fun _ h => by cases h; exact h0Slice18) (forall_cons (fun _ h => by cases h; exact h0Slice19) (forall_cons (fun _ h => by cases h; exact h0Slice20) (forall_cons (fun _ h => by cases h; exact h0Slice21) (forall_cons (fun _ h => by cases h; exact h0Slice22) (forall_cons (fun _ h => by cases h; exact h0Slice23) (forall_cons (fun _ h => by cases h; exact h0Slice24) (forall_cons (fun _ h => by cases h; exact h0Slice25) (forall_cons (fun _ h => by cases h; exact h0Slice26) (forall_cons (fun _ h => by cases h; exact h0Slice27) (forall_cons (fun _ h => by cases h; exact h0Slice28) (forall_cons (fun _ h => by cases h; exact h0Slice29) (forall_cons (fun _ h => by cases h; exact h0Slice30) (forall_cons (fun _ h => by cases h; exact h0Slice31) (forall_cons (fun _ h => by cases h; exact h0Slice32) (forall_cons (fun _ h => by cases h; exact h0Slice33) (forall_cons (fun _ h => by cases h; exact h0Slice34) (forall_cons (fun _ h => by cases h; exact h0Slice35) (forall_cons (fun _ h => by cases h; exact h0Slice36) (forall_cons (fun _ h => by cases h; exact h0Slice37) (forall_cons (fun _ h => by cases h; exact h0Slice38) (forall_cons (fun _ h => by cases h; exact h0Slice39) (forall_cons (fun _ h => by cases h; exact h0Slice40) (forall_cons (fun _ h => by cases h; exact h0Slice41) (forall_cons (fun _ h => by cases h; exact h0Slice42) (forall_cons (fun _ h => by cases h; exact h0Slice43) (fun _ h => (List.not_mem_nil h).elim)))))))))))))))))))))))))))))))))))))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h0R h0G c) h0Pools := buildPoolsBT_sound h0SlicesOk
def h0Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G (7 - 1) xs.toFinset) h0Empty := trivial
def h0Block7_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,62],[0,1,12,14,16,19,20,31,32,33,34,102]),([0,1,2,3,4,5,63],[0,1,12,16,19,20,31,32,33,34,102,147,148]),([0,1,2,3,4,5,68],[0,1,16,20,31,32,33,34,184,185]),([0,1,3,4,5,50,62],[12,14,102,111,117,118,202]),([0,1,2,4,5,50,53,57],[17,19,20,111]),([0,1,3,4,5,56,66],[12,14,20,119,169,247,249,255]),([0,1,2,3,4,5,91],[0,1,20,31,32,33,34,438,477,478]),([0,1,3,4,5,83,99],[14,19,389,416,423,619]),([0,1,2,3,4,5,99],[0,1,12,14,16,19,31,32,33,34,389,416]),([0,1,2,3,4,97,108],[1,31,33,793,794,795,796,797,798,799]),([0,1,2,3,4,73,97],[1,31,33,793,794,795,797,798,799,836,837,843,844,845]),([0,1,2,3,4,5,114],[0,12,14,16,19,31,32,33,34,344,785,791,836,837,846,847,848])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Empty 7 h0Block7_0 = true := by decide +kernel
def h0Block7_1 : List NodeSpec := nodesWithIdentity [([0,1,2,3,5,73,115],[14,31,286,363,531,791,799,836,874,875]),([0,1,2,3,4,92,97],[1,31,33,793,794,795,797,798,799,843,844]),([0,1,2,3,4,5,119],[0,12,14,16,20,31,32,33,34,791,921,925])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_1 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Empty 7 h0Block7_1 = true := by decide +kernel
def h0Nodes7 : List NodeSpec := h0Block7_0 ++ h0Block7_1
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Check7 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Empty 7 h0Nodes7 = true := by
  unfold h0Nodes7 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h0Test7_0,h0Test7_1⟩
def h0Bucket7 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 7 xs.toFinset) h0Bucket7 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0EmptyOk h0Check7
def h0Block8_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,39],[0,1,6,7,13,16,19,20,25,26,27,28,29,30,31,32,33,34]),([0,1,2,3,4,5,6,39],[0,1,2,3,4,5,6,13,15,18,20,25,26,27,28]),([0,1,2,3,4,5,27,39],[0,6,7,13,16,19,21,22,23,24,25,26,27,28,29]),([1,2,3,4,5,6,40],[12,14,15,16,18,19,35,41,42,43,44,45,46]),([0,1,2,3,4,5,43],[0,1,15,16,18,19,31,32,33,34,35,36,51,52,53,54]),([0,1,2,3,4,5,46],[0,1,16,19,20,31,32,33,34,55,56,65,66,67,68,69,70]),([0,1,2,3,4,5,48],[0,1,13,15,16,20,31,32,33,34,72,73,82,83,84,85]),([0,1,3,4,5,27,50],[12,14,17,19,102,103,109,110,111,112,113,114,115,116,117,118]),([0,1,2,3,4,5,59],[0,1,16,19,31,32,33,34,103,104,109,119,121,122,123,124,125,126,127,128]),([0,1,2,3,4,5,30,50],[19,20,35,36,46,47,48,49,50,102,117,118,119,133,134,135,136,137,138,139]),([0,1,2,3,4,5,30,55],[17,19,20,46,47,48,49,50,102,137,140,141,142,143,144,145,146]),([0,1,2,3,4,5,63],[0,1,12,16,19,20,31,32,33,34,102,120,147,148,149,150,151,152,153])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_0 = true := by decide +kernel
def h0Block8_1 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,7,63],[0,1,16,98,99,100,101,102,104,120,147,148,149,150,151,152,153]),([0,1,2,3,4,5,30,63],[12,16,17,19,20,35,36,47,48,49,50,102,137,147,148,150,151,152,153]),([0,1,2,3,4,5,30,41],[16,17,19,20,41,46,47,48,49,50,137,142,154,155,156,157,158,159]),([0,1,2,4,5,7,31,57],[12,14,19,102,104,120,160,166,167,168,169,170,171,172,173,174,175]),([0,1,2,3,4,5,31,67],[16,20,61,62,63,64,71,120,160,165,176,177,178,179,180,181,182,183]),([0,1,2,3,4,5,68],[0,1,16,20,31,32,33,34,120,160,165,166,184,185,186,187,188,189,190,191]),([0,1,2,3,4,5,7,68],[0,1,19,98,99,100,101,102,104,120,160,166,184,185,186,187,188,189,190,191]),([0,1,2,3,4,5,31,68],[12,16,20,55,56,61,62,63,64,120,160,184,185,186,187,188,189,190,191]),([0,1,3,4,5,32,50],[12,14,19,102,111,117,118,119,196,197,198,199,200,201]),([0,1,2,3,4,5,32,50],[19,20,46,72,73,78,79,80,81,102,117,118,133,134,138,139,196,197,198,199,200,201,203]),([0,1,2,3,4,5,69],[0,1,12,16,19,20,31,32,33,34,102,104,204,205,206,207,208,209]),([0,1,2,3,4,5,50,53],[12,14,17,19,20,102,111,117,118,133,134,138,139,210,211,212,213,214,215,216,217,218])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_1 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_1 = true := by decide +kernel
def h0Block8_2 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,50,54],[12,14,17,19,20,102,111,117,118,133,134,138,139,213,219,220,221,222,223,224,225,226]),([0,1,2,3,4,5,50,57],[12,14,16,17,19,20,102,111,117,118,120,133,134,138,139,166,169,172,175,213,227,228,229,230,231,232,233,234]),([0,1,2,3,4,5,50,58],[12,14,16,17,19,20,102,104,111,117,118,119,133,134,138,139,213,235,236,237,238,239,240,241,242,243]),([0,1,2,3,4,5,7,50,53],[12,102,104,111,119,120,210,213,244]),([0,1,2,3,4,5,50],[0,1,12,19,20,31,32,33,34,102,111,117,118,133,134,213]),([0,1,2,3,4,5,50,56],[0,12,102,117,118,133,134,138,139,245,246,247,248,249,250,251,252,253,254,255,256]),([0,1,2,3,4,5,56,57],[12,14,16,20,120,166,169,172,175,229,230,233,234,245,246,247,248,249,250,255,257,258]),([0,1,2,3,4,5,56,58],[12,14,16,19,104,119,235,236,239,240,241,242,243,245,246,247,248,249,250,255,256,259,260]),([0,1,2,3,4,5,7,66],[0,1,12,14,16,17,19,20,98,99,100,101,102,104,120,166,169,261,262,263,264,265,266,267,268]),([1,2,3,4,5,8,28],[1,6,12,17,20,277,278,279,280,281,282,283,284,285,286]),([0,1,2,3,4,5,74],[0,1,6,12,16,19,20,31,32,33,34,109,280,289,290,291,292,293,294,295]),([0,1,2,3,4,5,7,30],[0,1,12,16,17,19,20,35,36,46,47,48,49,50,98,99,100,101,102,137])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_2 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_2 = true := by decide +kernel
def h0Block8_3 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,75],[0,1,12,16,19,31,32,33,34,35,142,287,288,300,301,302,303,304,305]),([0,1,2,3,4,5,7,31],[0,1,12,16,17,19,20,55,56,61,62,63,64,71,98,99,100,101,102,104,120,160]),([0,1,2,3,4,5,76],[0,1,12,16,19,20,31,32,33,34,55,165,288,310,311,312,313,314,315,316]),([0,1,2,3,4,5,77],[0,1,12,16,20,31,32,33,34,72,280,287,321,322,323,324,325,326]),([1,2,3,4,5,9,51],[0,1,12,17,102,133,341,342,343,344,345,346]),([1,2,3,4,5,9,60],[0,12,14,17,119,140,360,361,362,363,364,365]),([0,1,2,3,4,5,79],[0,1,12,20,31,32,33,34,119,341,350,372,382,383,384,385,386]),([0,1,2,3,4,5,9,79],[0,1,12,332,333,334,335,341,350,372,383,384,385,386]),([0,1,2,3,4,5,19,79],[0,1,20,119,341,372,378,379,380,381,383,384,385,386,387]),([1,2,3,4,5,9,80],[12,14,16,19,71,349,361,388,394,395,396,397,398,399,400,401]),([0,1,2,3,4,5,12,20],[0,1,12,14,16,19,20,46,71,388,389,402,403,404,405,406,407,408,409,410,411,412,413,414,415]),([0,1,3,4,5,9,83],[12,14,17,19,349,361,389,416,417,418,419,420,421,422,423])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_3 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_3 = true := by decide +kernel
def h0Block8_4 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,86],[0,1,12,16,19,20,31,32,33,34,71,349,361,388,424,425,426,427,428,429,430]),([0,2,3,4,5,21,52],[0,14,17,20,71,134,431,437,438,439,440,441]),([0,1,2,3,4,5,87],[0,1,12,19,31,32,33,34,71,341,349,431,447,448,449,450,451,452]),([0,1,2,3,4,5,89],[0,1,12,16,19,20,31,32,33,34,119,350,361,453,463,464,465,466,467,468,469]),([0,1,2,3,4,5,31,52],[0,14,17,19,20,55,56,61,62,63,64,102,134,160,165,286,438,441,472,473,474,475,476]),([0,1,2,3,4,5,33,52],[0,14,17,31,32,71,102,134,286,345,439,441,472,474,475,476,479,480,481,482,483,484,485,486,487,488,489]),([0,1,2,3,4,5,36,52],[0,14,17,19,20,31,32,71,102,134,286,363,438,439,441,472,474,475,476,490,491,492,493,494,495,496,497]),([1,2,3,4,5,9,28],[0,6,12,17,20,286,350,502,503,504,505,506]),([1,2,3,4,5,9,44],[0,12,17,19,55,349,511,512,513,514,515,516]),([0,2,3,4,5,19,78],[12,14,16,19,119,363,373,387,527,528,529,530,531]),([0,1,2,3,4,5,93],[0,1,12,16,20,31,32,33,34,373,387,521,522,532,533,534,535,536]),([0,1,2,3,4,5,10,83],[0,12,16,71,389,416,423,517,518,519,520,521,522,537,542,543,544,545,546])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_4 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_4 = true := by decide +kernel
def h0Block8_5 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,94],[0,1,12,16,19,20,31,32,33,34,389,405,537,547,548,549,550,551,552,553]),([0,1,2,3,4,5,10,94],[0,12,16,19,389,517,518,519,520,521,522,537,547,548,550,551,552,553]),([0,1,2,3,4,5,20,94],[1,16,20,388,389,405,406,407,412,413,537,547,548,549,550,551,552,553]),([0,1,2,3,4,5,95],[0,1,12,16,19,31,32,33,34,432,521,537,558,559,560,561,562,563,564]),([0,1,2,3,4,5,10,88],[0,12,16,119,454,470,517,518,519,520,521,522,537,570,571,572,573,574,575,576]),([0,1,2,3,4,5,96],[0,1,12,16,19,20,31,32,33,34,454,522,565,577,578,579,580,581,582,583]),([0,2,3,4,5,23,78],[12,14,16,32,119,286,363,528,529,531,584,585,586,587]),([1,2,3,4,5,11,64],[1,12,17,20,229,362,597,598,599,600,601,602,603]),([0,1,2,3,4,5,98],[0,1,16,20,31,32,33,34,372,373,597,598,604,605,606,607]),([0,1,3,4,5,11,83],[12,14,19,71,389,416,423,613,614,615,616,617,618]),([0,1,2,3,4,5,11,83],[0,12,16,71,389,416,423,542,544,545,546,589,590,591,592,597,598,612,613,614,615,616,617]),([0,1,2,3,4,5,100],[0,1,16,19,20,31,32,33,34,388,389,620,621,622,623,624,625])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_5 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_5 = true := by decide +kernel
def h0Block8_6 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,101],[0,1,16,19,31,32,33,34,431,432,597,612,630,631,632,633]),([0,1,2,3,4,5,11,88],[0,12,16,119,454,570,571,573,574,575,576,589,590,591,592,597,598,612,638,639]),([0,1,2,3,4,5,102],[0,1,16,19,20,31,32,33,34,453,454,598,640,641,642,643,644,645]),([0,1,2,3,4,5,36,71],[0,14,16,19,20,31,32,71,246,362,490,491,493,495,496,646,647,648,649,650,651,652,653]),([0,1,2,3,4,5,103],[0,1,12,16,19,20,31,32,33,34,403,404,664,665,666,667,668,669]),([0,1,2,3,4,5,20,82],[1,20,46,71,395,405,406,407,412,413,672,673,674,675,676,677,678,679]),([0,1,2,3,4,5,85],[0,1,16,20,31,32,33,34,402,405,659,680,681,682,683,684,685,686,687]),([0,1,2,3,4,5,20,85],[1,12,20,388,389,402,405,406,407,412,413,680,681,682,683,684,685,686,687]),([0,1,2,3,4,5,105],[0,1,12,16,19,20,31,32,33,34,402,403,692,693,694,695,696,697,698]),([0,1,2,3,4,5,106],[0,1,16,19,31,32,33,34,404,565,659,703,704,705,706,707,708,709,710]),([0,1,2,3,4,5,31,61],[0,12,14,16,17,19,20,46,55,56,61,62,63,64,141,160,165,442,712,713,714,715,716,717]),([0,1,2,3,4,5,12,29],[0,7,12,14,16,17,19,20,46,402,403,404,408,410,414,415,659,728,729,730,731,732,733,734,735,736])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_6 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_6 = true := by decide +kernel
def h0Block8_7 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,12,45],[0,12,14,16,17,19,20,46,56,344,402,403,404,408,410,414,415,659,741,742,743,744,745,746,747,748]),([0,1,2,3,4,5,12,104],[0,1,12,14,16,17,19,20,46,402,403,404,405,408,410,414,415,659,681,758,759,760]),([0,2,3,4,5,23,65],[0,14,20,32,46,230,471,765,766,767,768,769,770,771]),([0,1,2,3,4,5,33,65],[0,14,16,17,20,31,32,120,230,479,482,483,484,486,488,489,736,766,768,770,772,773,774,775,776]),([0,1,2,3,4,5,34,65],[0,14,16,17,20,31,32,46,120,230,766,768,770,772,774,775,777,778,779,780,781,782,783,784,785,786]),([0,1,2,3,4,5,109],[0,1,14,17,20,31,32,33,34,46,531,718,785,787]),([0,1,2,3,4,5,23,108],[0,1,14,17,20,31,32,46,160,286,402,471,585,765,767,769,785,788,789,790,791,792,796,800,801,802]),([0,1,2,3,4,5,24,108],[0,1,14,17,20,31,32,46,160,286,345,402,788,789,790,792,796,803,804,805,806,807,808]),([0,1,2,3,4,5,111],[0,1,12,14,17,19,31,32,33,34,825,826,827,828,829,830,831,832,833,834]),([0,1,2,3,4,5,23,73],[1,6,12,14,17,19,31,32,344,363,502,585,586,765,767,785,791,800,801,835,836,837,838,839,840,841,842,845]),([0,1,2,3,4,5,24,73],[1,6,12,14,17,19,31,32,344,345,502,785,803,804,806,807,808,835,836,838,842,845,849,850,851]),([0,1,2,3,4,5,25,73],[1,6,12,14,17,19,33,34,344,442,502,718,720,835,836,837,838,841,842,845,852,853,854,855,856,857,858])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_7 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_7 = true := by decide +kernel
def h0Block8_8 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,26,73],[1,6,12,14,17,19,33,34,344,442,502,720,835,836,838,841,842,845,859,860,861,862,863,864,865,866,867,868]),([0,1,2,3,4,5,73,112],[1,6,12,14,17,19,344,502,531,736,785,836,838,842,845,869,870,871,872,873,876]),([0,1,2,3,4,5,73,113],[1,6,12,14,17,19,344,345,502,720,785,836,837,838,842,845,877,878,879,880,881,882,883]),([0,1,3,4,5,33,73],[12,17,19,32,344,485,487,502,720,785,836,884,885,886]),([0,1,3,4,5,34,73],[12,17,19,32,344,363,364,442,502,785,836,887,888,889,890,891]),([0,1,2,3,4,5,116],[0,1,14,17,19,31,32,33,34,899,900,901,902,903,904]),([0,1,2,3,4,5,117],[0,1,12,14,17,20,31,32,33,34,531,914,915,916,917,918,919]),([0,1,2,3,4,5,23,92],[1,12,14,17,20,31,32,55,286,363,473,511,585,586,765,767,785,791,800,801,839,920,921,922,923,924]),([0,1,2,3,4,5,24,92],[1,12,14,17,20,31,32,55,286,345,511,785,803,804,806,807,808,849,851,920,921,922,923,924]),([0,1,2,3,4,5,25,92],[1,12,14,17,20,33,34,55,473,511,718,720,852,853,854,855,856,857,858,920,921,922,923,924]),([0,1,2,3,4,5,26,92],[1,12,14,17,20,33,34,55,286,473,511,720,859,861,862,863,865,866,867,868,920,921,922,923,924,926,927]),([0,1,2,3,4,5,90,92],[1,12,14,17,20,55,71,286,511,531,785,921,922,923,924,928,929,930])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_8 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_8 = true := by decide +kernel
def h0Block8_9 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,92,118],[1,12,14,17,20,55,286,345,511,720,882,921,922,923,924,931,932,933,934,935,936])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_9 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_9 = true := by decide +kernel
def h0Nodes8 : List NodeSpec := h0Block8_0 ++ h0Block8_1 ++ h0Block8_2 ++ h0Block8_3 ++ h0Block8_4 ++ h0Block8_5 ++ h0Block8_6 ++ h0Block8_7 ++ h0Block8_8 ++ h0Block8_9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Check8 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Nodes8 = true := by
  unfold h0Nodes8 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨h0Test8_0,h0Test8_1⟩,h0Test8_2⟩,h0Test8_3⟩,h0Test8_4⟩,h0Test8_5⟩,h0Test8_6⟩,h0Test8_7⟩,h0Test8_8⟩,h0Test8_9⟩
def h0Bucket8 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 8 xs.toFinset) h0Bucket8 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0Bucket7Ok h0Check8
def h0Block9_0 : List NodeSpec := [([0,1,2,3,4,5,6,27],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24],[0]),([0,1,2,3,4,5,6,30],[0,1,2,3,4,5,12,13,14,15,16,18,19,20,35,36,37,38,39,40,46,47,48,49,50],[0,1]),([0,1,2,3,4,5,6,31],[0,1,2,3,4,5,12,13,14,15,16,17,18,19,20,55,56,57,58,59,60,61,62,63,64,71],[0]),([0,1,2,3,4,5,6,32],[0,1,2,3,4,5,12,13,14,15,16,19,20,46,72,73,74,75,76,77,78,79,80,81],[0]),([0,1,2,3,4,5,35],[0,1,15,17,19,20,31,32,33,34,46,86,87,88,89],[0]),([0,1,2,4,5,37],[0,1,19,90,91,92,93],[0]),([0,1,2,4,5,38],[0,1,20,94,95,96,97],[0]),([0,1,2,3,4,5,7,27],[0,1,6,7,12,14,16,17,19,20,21,22,23,24,98,99,100,101,102,103,104,105,106,107,108,109,119,120],[0]),([0,1,2,3,4,5,7,30],[0,1,12,14,16,19,20,35,36,47,48,49,50,98,99,100,101,102,104,120,129,130,131,132],[0]),([0,1,2,3,4,5,7,31],[0,1,12,14,16,17,19,20,55,56,61,62,63,64,98,99,100,101,102,104,120,160,161,162,163,164,165,166],[0]),([0,1,2,3,4,5,7,32],[0,1,12,14,16,19,20,72,73,78,79,80,81,98,99,100,101,102,104,119,192,193,194,195],[0]),([0,1,2,3,4,5,50],[0,1,12,14,17,19,20,31,32,33,34,102,117,118,133,134,138,139],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_0 = true := by decide +kernel
def h0Block9_1 : List NodeSpec := [([0,1,2,3,4,5,7,50],[0,1,12,14,16,98,99,100,101,102,104,117,118,119,120,133,134,138,139,166],[0]),([0,1,2,3,4,5,55],[12,14,17,19,20,31,32,33,34,102,140,141,143,144,145,146],[0]),([0,1,2,3,4,5,7,56],[0,1,12,14,16,98,99,100,101,102,104,119,120,245,246,247,248,249,250],[0]),([0,1,2,3,4,5,7,57],[0,1,12,14,19,20,98,99,100,101,102,104,120,172,175,229,230,233,234],[0]),([0,1,2,3,4,5,7,58],[0,1,12,14,19,20,98,99,100,101,102,104,119,120,235,236,239,240,241,242],[0]),([0,1,2,3,4,5,7],[0,1,12,16,19,20,31,32,33,34,98,100,102,104,120],[0]),([0,1,2,3,4,5,8,27],[0,1,6,7,12,14,16,17,19,20,21,22,23,24,109,119,269,270,271,272,273,274,275,276,280,286,287,288],[0]),([0,1,2,3,4,5,8,30],[0,1,12,14,16,19,20,35,36,46,47,48,49,50,269,270,271,272,280,287,288,296,297,298,299],[0]),([0,1,2,3,4,5,8,31],[0,1,12,14,16,17,19,20,55,56,61,62,63,64,71,165,269,270,271,272,280,287,288,306,307,308,309],[0]),([0,1,2,3,4,5,8,32],[0,1,12,14,16,19,20,46,72,73,78,79,80,81,119,269,270,271,272,280,287,317,318,319,320],[0]),([0,1,2,3,4,5,72],[0,1,12,14,17,19,20,31,32,33,34,46,287,327,328,329,330,331],[0]),([0,1,2,3,4,5,9,17],[0,1,12,14,16,17,332,333,334,335,336,337,338,339,340,341,347,348,349,350,351,352,353,354],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_1 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_1 = true := by decide +kernel
def h0Block9_2 : List NodeSpec := [([0,1,2,3,4,5,9,18],[0,1,12,14,16,17,332,333,334,335,341,349,350,355,356,357,358,359,361,366,367,368,369,370,371],[0]),([0,1,2,3,4,5,9,19],[0,1,12,14,16,17,19,20,119,332,333,334,335,341,350,372,373,374,375,376,377,378,379,380,381],[0]),([0,1,2,3,4,5,9,20],[0,1,12,14,16,17,19,20,71,332,333,334,335,341,349,350,361,388,389,390,391,392,393,406,407,412,413],[0]),([0,1,2,3,4,5,9,21],[0,1,12,14,16,17,19,20,71,332,333,334,335,341,349,350,431,432,433,434,435,436,442,443,444,445,446],[0]),([0,1,2,3,4,5,9,22],[0,1,12,14,16,17,19,20,119,332,333,334,335,341,344,349,350,361,453,454,455,456,457,458,459,460,461,462,470],[0]),([0,1,2,3,4,5,52],[0,1,12,14,19,20,31,32,33,34,102,134,286,439,471],[0,1]),([0,1,2,3,4,5,9,27],[0,6,7,12,16,17,19,20,21,22,23,24,286,332,333,334,335,341,350,470,498,499,500,501],[0]),([0,1,2,3,4,5,9,31],[0,12,16,17,19,20,55,56,61,62,63,64,332,333,334,335,341,349,350,470,507,508,509,510],[0]),([0,1,2,3,4,5,12],[0,1,12,14,16,19,20,31,32,33,34,402,403,404,408,414],[0]),([0,1,2,3,4,5,10,19],[0,1,12,14,16,19,20,119,362,372,373,378,379,380,381,517,518,519,520,521,522,523,524,525,526],[0]),([0,1,2,3,4,5,10,20],[0,1,12,14,16,19,20,388,389,405,406,407,412,413,517,518,519,520,521,522,537,538,539,540,541],[0]),([0,1,2,3,4,5,10,21],[0,1,12,14,16,19,20,362,431,432,442,443,444,445,446,517,518,519,520,521,522,537,554,555,556,557],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_2 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_2 = true := by decide +kernel
def h0Block9_3 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,10,22],[0,1,12,14,16,19,20,119,453,454,459,460,461,462,517,518,519,520,521,522,537,565,566,567,568,569]),([0,1,2,3,4,5,78],[0,1,12,14,16,19,20,31,32,33,34,140,286,365,442,531,588]),([0,1,2,3,4,5,11,19],[0,1,12,14,16,19,20,362,372,373,378,379,380,381,589,590,591,592,593,594,595,596,597,598]),([0,1,2,3,4,5,11,20],[0,1,12,14,16,19,20,71,388,389,406,407,412,413,589,590,591,592,597,598,608,609,610,611,612]),([0,1,2,3,4,5,11,21],[0,1,12,14,16,19,20,71,362,431,432,443,444,445,446,589,590,591,592,597,598,612,626,627,628,629]),([0,1,2,3,4,5,11,22],[0,1,12,14,16,19,20,344,453,454,459,460,461,462,470,589,590,591,592,597,598,612,634,635,636,637]),([0,1,2,3,4,5,71],[0,1,14,16,19,20,31,32,33,34,246,286,471,646]),([0,1,2,3,4,5,12,18],[0,1,12,14,16,17,355,366,367,368,369,370,371,402,403,404,408,410,414,415,654,655,656,657,658,659]),([0,1,2,3,4,5,12,19],[0,1,12,14,16,17,19,20,46,119,372,373,378,379,380,381,403,404,408,410,414,415,660,661,662,663]),([0,1,2,3,4,5,12,20],[0,1,12,14,16,17,19,20,46,388,389,402,403,404,405,406,407,408,409,410,411,412,413,414,415,659,670,671]),([0,1,2,3,4,5,12,21],[0,1,12,14,16,17,19,20,46,286,402,403,404,408,410,414,415,431,432,443,444,445,446,688,689,690,691]),([0,1,2,3,4,5,12,22],[0,1,12,14,16,17,19,20,46,119,402,403,404,408,410,414,415,453,454,459,460,461,462,565,659,699,700,701,702])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_3 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_3 = true := by decide +kernel
def h0Block9_4 : List NodeSpec := [([0,1,2,3,4,5,61],[0,1,12,14,16,19,20,31,32,33,34,46,141,286,442,531,711,718],[0,1]),([0,1,2,3,4,5,12,61],[0,1,12,16,17,46,119,141,363,402,403,404,408,410,414,415,470,659,711,719,720],[0]),([0,1,2,3,4,5,12,49],[0,1,12,14,15,16,17,46,119,345,402,403,404,408,410,414,415,719,721,722,723],[0]),([0,1,2,3,4,5,12,27],[0,6,7,12,16,17,19,20,21,22,23,24,103,286,402,403,404,408,410,414,415,724,725,726,727],[0]),([0,1,2,3,4,5,12,31],[0,12,16,17,19,20,55,56,61,62,63,64,160,402,403,404,408,410,414,415,737,738,739,740],[0]),([0,1,2,3,4,5,12,42],[0,12,16,17,19,20,35,46,119,363,364,402,403,404,408,410,414,415,442,723,749,750,751],[0]),([0,1,2,3,4,5,12,84],[0,12,16,17,19,20,46,402,403,404,408,410,414,415,752,753,754,755,756,757],[0]),([0,1,2,3,4,5,65],[0,1,14,16,20,31,32,33,34,230,471,768],[0,1]),([0,1,2,3,4,5,108],[0,1,14,16,17,20,31,32,33,34,46,471,785,788],[0]),([0,1,2,4,5,14,22],[0,1,19,20,453,565,813,814,815,816,817,818],[0]),([0,1,2,3,4,5,110],[0,1,12,14,16,19,20,31,32,33,34,813,819,820,821,822,823,824],[0,1]),([0,1,2,3,4,5,73],[0,1,6,12,14,16,17,19,20,31,32,33,34,502,720,785,835,841,892],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_4 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_4 = true := by decide +kernel
def h0Block9_5 : List NodeSpec := [([0,1,2,3,4,5,70],[0,1,14,16,19,31,32,33,34,104,236,471,897,898],[0]),([0,1,2,3,4,5,107],[0,1,14,16,17,19,31,32,33,34,46,404,471,785,897,905],[0]),([0,1,2,3,4,5,81],[0,1,12,14,16,19,20,31,32,33,34,388,442,531,910,911,912,913],[0]),([0,1,2,3,4,5,92],[0,1,12,14,16,17,19,20,31,32,33,34,55,473,511,720,785,892,920],[0]),([0,1,2,3,4,5,28],[0,1,6,12,14,16,19,20,31,32,33,34,442,502,937,938,939,940,941],[0,1]),([0,1,2,3,4,5,40],[0,1,12,14,16,19,31,32,33,34,35,751,942,943,944,945],[0]),([0,1,2,3,4,5,44],[0,1,12,14,16,19,20,31,32,33,34,55,442,511,946,947,948,949,950],[0,1]),([0,1,2,3,4,5,47],[0,1,12,14,16,20,31,32,33,34,72,951,952,953,954],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_5 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_5 = true := by decide +kernel
def h0Nodes9 : List NodeSpec := h0Block9_0 ++ h0Block9_1 ++ h0Block9_2 ++ h0Block9_3 ++ h0Block9_4 ++ h0Block9_5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Check9 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Nodes9 = true := by
  unfold h0Nodes9 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨h0Test9_0,h0Test9_1⟩,h0Test9_2⟩,h0Test9_3⟩,h0Test9_4⟩,h0Test9_5⟩
def h0Bucket9 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket9Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 9 xs.toFinset) h0Bucket9 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0Bucket8Ok h0Check9
def h0Block10_0 : List NodeSpec := [([0,1,2,3,4,5,6],[0,1,2,3,4,5,16,19,20,31,32,33,34],[0]),([0,1,2,3,4,5,7],[0,1,12,14,16,19,20,31,32,33,34,98,99,100,101],[0]),([0,1,2,3,4,5,8],[0,1,14,16,19,20,31,32,33,34,269,270,271,272],[0]),([0,1,2,3,4,5,9],[0,1,16,19,20,31,32,33,34,332,333,334,335],[0]),([0,1,2,3,4,5,10],[0,1,12,16,19,20,31,32,33,34,517,518,519,520],[0]),([0,1,2,3,4,5,11],[0,1,16,19,20,31,32,33,34,589,590,591,592],[0]),([0,1,2,3,4,5,12],[0,1,12,16,19,20,31,32,33,34,408,410,414,415],[0,1]),([0,1,2,3,4,5,13],[0,1,16,20,31,32,33,34,761,762,763,764],[0,1]),([0,1,2,3,4,5,14],[0,1,12,16,19,20,31,32,33,34,809,810,811,812],[0,1]),([0,1,2,3,4,5,15],[0,1,16,19,20,31,32,33,34,893,894,895,896],[0,1]),([0,1,2,3,4,5,16],[0,1,12,16,19,20,31,32,33,34,906,907,908,909],[0,1]),([0,1,2,3,4,5,27],[0,1,16,19,20,21,22,23,24,31,32,33,34],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test10_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket9 10 h0Block10_0 = true := by decide +kernel
def h0Block10_1 : List NodeSpec := [([0,1,2,3,4,5,30],[0,1,16,19,20,31,32,33,34,47,48,49,50],[0,1]),([0,1,2,3,4,5,31],[0,1,16,19,20,31,32,33,34,61,62,63,64],[0,1]),([0,1,2,3,4,5,32],[0,1,16,20,31,32,33,34,78,79,80,81],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test10_1 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket9 10 h0Block10_1 = true := by decide +kernel
def h0Nodes10 : List NodeSpec := h0Block10_0 ++ h0Block10_1
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Check10 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket9 10 h0Nodes10 = true := by
  unfold h0Nodes10 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h0Test10_0,h0Test10_1⟩
def h0Bucket10 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes10
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket10Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 10 xs.toFinset) h0Bucket10 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0Bucket9Ok h0Check10
def h0Block11_0 : List NodeSpec := [([0,1,2,3,4,5],[31,32,33,34],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test11_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket10 11 h0Block11_0 = true := by decide +kernel
def h0Nodes11 : List NodeSpec := h0Block11_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Check11 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket10 11 h0Nodes11 = true := h0Test11_0
def h0Bucket11 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes11
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket11Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 11 xs.toFinset) h0Bucket11 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0Bucket10Ok h0Check11
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bound : Lower h0R h0G 12 := lower_of_forestBT (essPairs := [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,5,13),(VAR 4,3,19),(VAR 5,3,35)]) (by decide +kernel) h0Bucket11Ok (by decide +kernel)
def wit : List PEqualNP.CircuitLowerBounds.Gate := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 6]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 7]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 5]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 1]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 5]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 11]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 12]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 13]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 14]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 15]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 16]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 17]⟩]
def wo : Nat := 18
lemma wit_mono : PEqualNP.MetaComplexity.Monotone2 ⟨wit, wo⟩ := by simp [PEqualNP.MetaComplexity.Monotone2, wit]
set_option maxRecDepth 100000 in set_option maxHeartbeats 0 in
lemma wit_eval : ∀ r : Row, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput6 r)) = ((4276677288 * 2 ^ 32 + 3972587648) ||| ((4276677288 * 2 ^ 32 + 3972587648) <<< 64)).testBit r.val := by decide +kernel
lemma low_root : Lower (varsOf 63) ((4276677288 * 2 ^ 32 + 3972587648) ||| ((4276677288 * 2 ^ 32 + 3972587648) <<< 64)) 12 := h0Bound
end PEqualNP.Outside.L_meta_47675
theorem PEqualNP.Outside.L_meta_47675 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276677288 * 2 ^ 32 + 3972587648) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276677288 * 2 ^ 32 + 3972587648) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hcs
  exact PEqualNP.Outside.L_meta_47675.table2_of_lower (4276677288 * 2 ^ 32 + 3972587648) (by decide) (by decide) (by decide) (by decide)
    12 PEqualNP.Outside.L_meta_47675.low_root
    PEqualNP.Outside.L_meta_47675.wit PEqualNP.Outside.L_meta_47675.wo (by decide)
    PEqualNP.Outside.L_meta_47675.wit_mono PEqualNP.Outside.L_meta_47675.wit_eval s hcs
