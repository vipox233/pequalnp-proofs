import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_49061
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
lemma normPack_lt (f : Wire) : normPack f < 2^128 :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => f r != f 0))).cast List.length_ofFn).isLt
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
lemma lower_count {roots : List Nat} {T : Nat}
    (hT0 : T ≠ 0) (hTlt : T < 2^128) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^128 ∧ a.testBit 0 = false)
    (singles : Finset Nat) (ess : ∀ a ∈ singles, Essential T roots a) :
    Lower roots T (singles.card - 1) := by
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
  have hsub : singles ⊆ S := fun a ha' => raw_required run roots a sub (ess a ha')
  have hle := (Finset.card_le_card hsub).trans (live_size run)
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
def countCheck (roots : List Nat) (T L : Nat) (essPairs : List (Nat × Nat × Nat)) : Bool :=
  checkProper T && checkRoots roots &&
    decide (essPairs.map Prod.fst).Nodup &&
    essPairs.all (fun e => checkEss1 T roots e.1 e.2.1 e.2.2) &&
    decide (L ≤ essPairs.length - 1)
lemma count_of {roots T L essPairs} (ok : countCheck roots T L essPairs = true) :
    Lower roots T L := by
  simp only [countCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨hT, hR⟩, hnd⟩, hess⟩, hle⟩ := ok
  have ⟨p1, p2, p3⟩ := checkProper_sound hT
  have hR' := checkRoots_sound hR
  have hl := lower_count p1 p2 p3 hR' (essPairs.map Prod.fst).toFinset (fun a ha => by
    obtain ⟨⟨v, r, s⟩, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    exact checkEss1_sound (hess (v, r, s) hm))
  have hcard : (essPairs.map Prod.fst).toFinset.card = essPairs.length := by
    rw [List.toFinset_card_of_nodup hnd, List.length_map]
  rw [hcard] at hl
  exact fun p bank hr hav => hle.trans (hl p bank hr hav)
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
def sliceCheck (z o zDrop : Nat) (raw : List Nat) (T : Nat) (freeRoots : List Nat) (qRoots : List Nat) (qGoal : Nat)
    (qL : Nat) (lEss : List (Nat × Nat × Nat)) (sliceL : Nat) : Bool :=
  let G := fixWord z o T
  decide (z < 128) && decide (o < 128) && ((z &&& o) == 0) &&
    checkProper G && checkRoots freeRoots &&
    raw.all (fun a => freeIn freeRoots (fixWord z o a)) &&
    (if qGoal == 0 then
       decide (lEss.map Prod.fst).Nodup &&
       lEss.all (fun e => checkEss1 G freeRoots e.1 e.2.1 e.2.2) &&
       decide (sliceL ≤ lEss.length - 1)
     else
       liftCheck zDrop 0 freeRoots G qRoots qGoal lEss &&
       decide (sliceL ≤ qL + lEss.length))
lemma slice_of {z o zDrop raw T freeRoots qRoots qGoal qL lEss sliceL}
    (ok : sliceCheck z o zDrop raw T freeRoots qRoots qGoal qL lEss sliceL = true)
    (hPrior : qGoal ≠ 0 → Lower qRoots qGoal qL) :
    Slice raw T (subcube z o) sliceL := by
  simp only [sliceCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨⟨hz, ho⟩, hzo⟩, hGp⟩, hFR⟩, hcov⟩, htail⟩ := ok
  have ⟨g0, glt, gb0⟩ := checkProper_sound hGp
  have hFR' := checkRoots_sound hFR
  refine ⟨fixRow z o, freeRoots, subcube_fixRow z o hz ho hzo,
    fun a ha => freeIn_sound ((fixWord_eq_renameW z o a).symm ▸ hcov a ha),
    by rw [← obs_renameW, ← fixWord_eq_renameW]; exact obs_not_const g0 glt gb0, ?_⟩
  rw [← obs_renameW, ← fixWord_eq_renameW]
  by_cases hq : qGoal = 0
  · simp only [hq, ite_true, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at htail
    have hl := lower_count g0 glt gb0 hFR' (lEss.map Prod.fst).toFinset (fun a ha => by
      obtain ⟨⟨v, r, s⟩, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
      exact checkEss1_sound (htail.1.2 _ hm))
    have hcard : (lEss.map Prod.fst).toFinset.card = lEss.length := by
      rw [List.toFinset_card_of_nodup htail.1.1, List.length_map]
    rw [hcard] at hl
    exact fun p bank hr hav => htail.2.trans (hl p bank hr hav)
  · simp only [hq, ite_false, Bool.and_eq_true, decide_eq_true_eq] at htail
    have hl := lift_of htail.1 (hPrior hq)
    exact fun p bank hr hav => htail.2.trans (hl p bank hr hav)
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
def evalInput (r : Row) : Fin 7 → Bool := fun i => r.val.testBit i.val
def packInput (x : Fin 7 → Bool) : Row :=
  ⟨(x 0).toNat + 2 * (x 1).toNat + 4 * (x 2).toNat + 8 * (x 3).toNat +
    16 * (x 4).toNat + 32 * (x 5).toNat + 64 * (x 6).toNat, by
    have h0 := Bool.toNat_le (x 0); have h1 := Bool.toNat_le (x 1); have h2 := Bool.toNat_le (x 2)
    have h3 := Bool.toNat_le (x 3); have h4 := Bool.toNat_le (x 4); have h5 := Bool.toNat_le (x 5)
    have h6 := Bool.toNat_le (x 6); omega⟩
lemma evalInput_packInput (x : Fin 7 → Bool) : evalInput (packInput x) = x := by
  funext i
  have h : ∀ (b0 b1 b2 b3 b4 b5 b6 : Bool) (j : Fin 7),
      ((b0.toNat + 2 * b1.toNat + 4 * b2.toNat + 8 * b3.toNat +
        16 * b4.toNat + 32 * b5.toNat + 64 * b6.toNat).testBit j.val) =
        ([b0, b1, b2, b3, b4, b5, b6].getD j.val false) := by decide +kernel
  have hi := h (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) i
  fin_cases i <;> simpa [evalInput, packInput] using hi
lemma var_testBit (i : Fin 7) (r : Row) : (VAR i.val).testBit r.val = r.val.testBit i.val := by
  revert i r; decide +kernel
lemma sw_extract_full (T : Nat) (hT0 : T ≠ 0) (hTlt : T < 2^128) (hTb0 : T.testBit 0 = false)
    (gs : List Gate) (o : Nat)
    (legal : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (he : ∀ r : Row, Circuit.eval ⟨gs, o⟩ (List.ofFn (evalInput r)) = T.testBit r.val) :
    ∃ k S, k ≤ gs.countP isBin ∧ Live T k S ∧ ∀ a ∈ S, a ∈ varsOf 127 := by
  let seeds : List SWire := (varsOf 127).map (fun v => (false, v))
  have hseeds_lt : ∀ u ∈ seeds, u.2 < 2^128 ∧ u.2.testBit 0 = false := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
    have hall : (varsOf 127).all (fun a => decide (a < 2^128) && !a.testBit 0) = true := by decide +kernel
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
  have hread_seeds (r : Row) : seeds.map (swRead r.val) = List.ofFn (evalInput r) := by
    apply List.ext_getElem
    · simp only [seeds, List.length_map, List.length_ofFn]; decide
    · intro i hi1 hi2
      have hi7 : i < 7 := by simpa using hi2
      have hv : (varsOf 127)[i]? = some (VAR i) := by
        interval_cases i <;> decide
      simp only [List.getElem_map, List.getElem_ofFn, seeds, evalInput, swRead, Bool.false_bne]
      have hget : (varsOf 127)[i]'(by simpa [seeds] using hi1) = VAR i := by
        have := List.getElem?_eq_some_iff.mp hv; exact this.2
      rw [hget]
      exact var_testBit ⟨i, hi7⟩ r
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
    · have h := hev ⟨r, hr⟩
      simpa [swRead, hout0] using h
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hfinal_lt.1 (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hTlt (Nat.pow_le_pow_right (by decide) (by omega)))]
  have hfound : T ∈ reps final := by
    rw [← hout2]
    exact (get_simple final o).resolve_left (hout2.symm ▸ hT0)
  obtain ⟨k, S, hk, hlive, hsub⟩ := extract_live hT0 gs seeds hfound
  refine ⟨k, S, hk, hlive, ?_⟩
  simpa [reps, seeds, List.map_map, Function.comp_def] using hsub
lemma replace_of_lower (T : Nat) (hT0 : T ≠ 0) (hTlt : T < 2^128) (hTb0 : T.testBit 0 = false)
    (L : Nat) (hLow : Lower (varsOf 127) T L)
    (wit : List Gate) (wo : Nat) (hwLen : wit.length ≤ L + 1)
    (hwMono : ∀ g ∈ wit, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (edgeFn : (Fin 7 → Bool) → Bool)
    (hEdgeT : ∀ r : Row, edgeFn (evalInput r) = T.testBit r.val)
    (hwEvalR : ∀ r : Row, Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput r)) = T.testBit r.val)
    (gates : List Gate) (o : Nat)
    (legal : ∀ g ∈ gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (spec : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = edgeFn x) :
    ∃ (gates' : List Gate) (o' : Nat),
      (∀ g ∈ gates', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧
      ∀ x : Fin 7 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = edgeFn x := by
  have hwEval : ∀ x : Fin 7 → Bool, Circuit.eval ⟨wit, wo⟩ (List.ofFn x) = edgeFn x := by
    intro x
    have hx := evalInput_packInput x
    rw [← hx]
    exact (hwEvalR (packInput x)).trans (hEdgeT (packInput x)).symm
  by_cases hn : ∃ g ∈ gates, g.op = .not
  · have hlt : gates.countP isBin < gates.length := by
      apply Nat.lt_of_le_of_ne List.countP_le_length
      intro eq
      obtain ⟨g, hg, hop⟩ := hn
      have bad := List.countP_eq_length.mp eq g hg
      simp [isBin, hop] at bad
    obtain ⟨k, S, hk, hlive, hsub⟩ := sw_extract_full T hT0 hTlt hTb0 gates o legal (fun r => (spec (evalInput r)).trans (hEdgeT r))
    have hnd : S.toList.Nodup := Finset.nodup_toList S
    have hrun := live_to_run hlive S.toList hnd (by simp)
    have hsup : Supply ((varsOf 127).map obs) (S.toList.map obs) := fun v hv => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
      exact Or.inl (List.mem_map_of_mem (hsub a (Finset.mem_toList.mp ha)))
    obtain ⟨q, next, hq, hav, hbound⟩ :=
      contraction (obs_not_const hT0 hTlt hTb0) hrun ((varsOf 127).map obs)
        (show Reach ((varsOf 127).map obs) 0 ((varsOf 127).map obs) from rfl) hsup
    have hlo := hLow q next hq hav
    refine ⟨wit, wo, hwMono, by omega, hwEval⟩
  · refine ⟨gates, o, ?_, le_rfl, spec⟩
    intro g hg
    obtain ⟨hop, hlen⟩ := legal g hg
    refine ⟨?_, hlen⟩
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hn ⟨g, hg, h⟩).elim
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
lemma slice_fast_of {z o zDrop raw T freeRoots qRoots qGoal qL lEss sliceL}
    (ok : sliceCheck z o zDrop raw T freeRoots qRoots qGoal qL lEss sliceL = true)
    (hPrior : qGoal ≠ 0 → Lower qRoots qGoal qL) :
    Slice raw T (subcubeFast z o) sliceL := by
  have ok2 := ok
  simp only [sliceCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at ok2
  rw [subcubeFast_eq_subcube z o ok2.1.1.1.1.1.1 ok2.1.1.1.1.1.2 ok2.1.1.1.1.2]
  exact slice_of ok hPrior
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
def hashWs (nb : Nat) (ws : List Nat) : Nat :=
  (ws.foldl (fun h w => h + (w % 1000003) * 31) 0) % nb
def bucketContains (buckets : Array (List (List Nat))) (ws : List Nat) : Bool :=
  let s := sortNats ws
  (buckets.getD (hashWs buckets.size s) []).contains s
def closeChild (pools : List BoundPool) (autos : List (List (Nat × Nat)))
    (prevBuckets : Array (List (List Nat))) (k : Nat) (rest : List Nat) (op : Choice) : Bool :=
  let ws := choiceVal op :: rest
  pools.any (fun c => scalarPoolCut c k rest op) ||
    autos.any (fun sw => bucketContains prevBuckets (ws.map (permWord sw)))
lemma closeChild_sound {raw T pools autos prevBuckets k rest op}
    (hT : T < 2^128)
    (hPools : ∀ c ∈ pools, ValidPool raw T c)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : ∀ i (hi : i < prevBuckets.size), ∀ xs ∈ prevBuckets[i], Impossible T k xs.toFinset)
    (nd : (choiceVal op :: rest).Nodup)
    (hlt : ∀ x ∈ choiceVal op :: rest, x < 2^128)
    (h : closeChild pools autos prevBuckets k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with ⟨c, hc, hcut⟩ | ⟨sw, hsw, hhit⟩
  · exact scalarPoolCut_sound (hPools c hc) nd hcut
  · unfold bucketContains at hhit
    simp only [Array.getD, List.contains_eq_mem, decide_eq_true_eq] at hhit
    split at hhit
    next hlt_b =>
      have himp := hPrev _ hlt_b _ hhit
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
        · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide) (by omega))),
              Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))]
      have hfix_r : permWord sw.reverse T = T := by
        conv_lhs => rw [← hfix]
        exact hinv_w T hT
      have hmap_lt : ∀ a ∈ (choiceVal op :: rest).map (permWord sw), a < 2^128 := by
        intro a ha
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
        rw [permWord_eq_renameW sw hsv x (hlt x hx)]
        exact renameW_lt _ x
      have hrot := rotate_impossible himp sw.reverse hvr hT hfix_r hmap_lt
      have hback : (((choiceVal op :: rest).map (permWord sw)).map (permWord sw.reverse)) = (choiceVal op :: rest) := by
        rw [List.map_map]
        conv_rhs => rw [← List.map_id (choiceVal op :: rest)]
        exact List.map_congr_left fun x hx => hinv_w x (hlt x hx)
      rwa [hback] at hrot
    next => simp at hhit
def evalMove (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (pools : List BoundPool) (autos : List (List (Nat × Nat)))
    (prevBuckets : Array (List (List Nat)))
    (d : Nat) (a b z : Decor) (ka kb : Bool) : Bool :=
  let len := 1 + (n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len > cap then true else
    let rs := restCov cov (dsep a) (dsep b) ka kb
    if ((rs ||| dsep z) &&& fmask) != fmask then true else
    if z.1 == 0 || ws.any (fun v => v.1 == z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChild pools autos prevBuckets (cap - 1) rest (d, a.1, b.1)
def testPair (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (pools : List BoundPool) (autos : List (List (Nat × Nat)))
    (prevBuckets : Array (List (List Nat))) (a b : Decor) (d : Nat) : Bool :=
  let z := dbin d a b
  let go := evalMove cap n fmask ws cov pools autos prevBuckets d a b z
  go false false && go true false && go false true && go true true
def testAll (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (pools : List BoundPool) (autos : List (List (Nat × Nat)))
    (prevBuckets : Array (List (List Nat))) : List Decor → Bool
  | [] => true
  | a :: bs =>
    bs.all (fun b => [0, 1, 2, 3].all (testPair cap n fmask ws cov pools autos prevBuckets a b)) &&
      testAll cap n fmask ws cov pools autos prevBuckets bs
lemma evalMove_sound {raw T pos neg ws pools autos prevBuckets cap a b d ka kb}
    (hT : T < 2^128)
    (gp : goodPairs T pos neg) (hf : ∀ w ∈ ws, faithful pos neg w)
    (nd : (ws.map Prod.fst).Nodup) (hlt : ∀ w ∈ ws, w.1 < 2^128)
    (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) (hcap : 0 < cap) (hd : d < 4)
    (hPools : ∀ c ∈ pools, ValidPool raw T c)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : ∀ i (hi : i < prevBuckets.size), ∀ xs ∈ prevBuckets[i], Impossible T (cap - 1) xs.toFinset)
    (hnz : (dbin d a b).1 ≠ 0) (hfr : (dbin d a b).1 ∉ ws.map Prod.fst)
    (test : evalMove cap ws.length (fullMask pos.length) ws (coverage ws) pools autos prevBuckets
      d a b (dbin d a b) ka kb = true) :
    Impossible T (cap - 1) ((dbin d a b).1 :: (delTwo ws a b ka kb).map Prod.fst).toFinset := by
  let z := dbin d a b
  let rest := delTwo ws a b ka kb
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := delTwo_sub ws a b ka kb
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => hfr ((sub.map _).subset hm), nd.sublist (sub.map _)⟩
  have hltc : ∀ x ∈ child, x < 2^128 := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact bin_lt d a.1 b.1 (hlt a ha) (hlt b hb)
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
      exact hlt w (sub.subset hw)
  have hfr_b : ws.any (fun v => v.1 == z.1) = false := by
    apply Bool.eq_false_iff.mpr; intro hh
    obtain ⟨x, hx, he⟩ := List.any_eq_true.mp hh
    exact hfr (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have hnz_b : (z.1 == 0) = false := beq_false_of_ne hnz
  have hleq : 1 + (ws.length - (if ka then 0 else 1) - (if kb then 0 else 1)) = child.length := by
    change _ = (z.1 :: rest.map Prod.fst).length
    rw [List.length_cons, List.length_map, delTwo_len ws a b ka kb ha hb ne, Nat.add_comm 1]
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
  unfold evalMove at test
  dsimp only at test
  have hnotgt : ¬(child.length > cap) := by omega
  dsimp only [z] at hcov_b hnz_b hfr_b
  simp only [hleq, hnotgt, ↓reduceIte, hcov_b, hnz_b, hfr_b, Bool.false_or, Bool.false_eq_true] at test
  exact closeChild_sound (op := (d, a.1, b.1)) (rest := rest.map Prod.fst) hT hPools hAutos hPrev ndc hltc test k hk h
lemma testAll_pair {cap n fmask ws cov pools autos prevBuckets l}
    (h : testAll cap n fmask ws cov pools autos prevBuckets l = true)
    {a b : Decor} (ha : a ∈ l) (hb : b ∈ l) (ne : a ≠ b) :
    (∀ d < 4, testPair cap n fmask ws cov pools autos prevBuckets a b d = true) ∨
    (∀ d < 4, testPair cap n fmask ws cov pools autos prevBuckets b a d = true) := by
  induction l with
  | nil => simp at ha
  | cons w l ih =>
    simp only [testAll, Bool.and_eq_true, List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | ha'
    · have bm := (List.mem_cons.mp hb).resolve_left ne.symm
      exact Or.inl fun d hd => h.1 b bm d (by interval_cases d <;> decide)
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact Or.inr fun d hd => h.1 a ha' d (by interval_cases d <;> decide)
      · exact ih h.2 ha' hb'
lemma node_sound {raw T pos neg ws pools autos prevBuckets cap}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hf : ∀ w ∈ ws, faithful pos neg w) (nd : (ws.map Prod.fst).Nodup)
    (hlt : ∀ w ∈ ws, w.1 < 2^128) (out : T ∉ ws.map Prod.fst)
    (hPools : ∀ c ∈ pools, ValidPool raw T c)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : ∀ i (hi : i < prevBuckets.size), ∀ xs ∈ prevBuckets[i], Impossible T (cap - 1) xs.toFinset)
    (checks : cap = 0 ∨ testAll cap ws.length (fullMask pos.length) ws (coverage ws) pools autos prevBuckets ws = true) :
    Impossible T cap (ws.map Prod.fst).toFinset := by
  rcases checks with rfl | hcheck
  · intro k hk h
    have hk0 : k = 0 := by omega
    subst hk0
    obtain ⟨hS, _⟩ := h
    exact out (List.mem_toFinset.mp (hS ▸ Finset.mem_singleton_self T))
  by_cases h0 : cap = 0
  · subst h0; intro k hk h
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
      (ht : testPair cap ws.length (fullMask pos.length) ws (coverage ws) pools autos prevBuckets x y d' = true) :
      Impossible T (cap - 1) (childTwo (ws.map Prod.fst) x.1 y.1 d' k1 k2).toFinset := by
    rw [← delTwo_map_toFinset nd hx hy nxy d' k1 k2]
    have hem : evalMove cap ws.length (fullMask pos.length) ws (coverage ws) pools autos prevBuckets d' x y (dbin d' x y) k1 k2 = true := by
      simp only [testPair, Bool.and_eq_true] at ht
      cases k1 <;> cases k2 <;> first | exact ht.1.1.1 | exact ht.1.2 | exact ht.1.1.2 | exact ht.2
    exact evalMove_sound hT gp hf nd hlt hx hy (fun e => nxy (congrArg Prod.fst e)) hcap hd' hPools hAutos hPrev hnz' hfr' hem
  rcases testAll_pair hcheck haW hbW ab with hh | hh
  · exact one a b d hd haW hbW ne ka kb hnz hfr (hh d hd)
  · rw [childTwo_swap _ nd _ _ d hd]
    have hfl := flipOp_lt hd
    exact one b a (flipOp d) hfl hbW haW ne.symm kb ka
      (bin_comm_flip d hd a.1 b.1 ▸ hnz) (bin_comm_flip d hd a.1 b.1 ▸ hfr) (hh _ hfl)
lemma lower_of_forest {roots T cap} {topBuckets : Array (List (List Nat))} {essPairs : List (Nat × Nat × Nat)}
    (ok : forestRootCheck roots T essPairs = true)
    (hTop : ∀ i (hi : i < topBuckets.size), ∀ xs ∈ topBuckets[i], Impossible T cap xs.toFinset)
    (hRoot : bucketContains topBuckets roots = true) :
    Lower roots T (cap + 1) := by
  simp only [forestRootCheck, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq] at ok
  obtain ⟨⟨hT, hR⟩, hess⟩ := ok
  have ⟨p1, p2, p3⟩ := checkProper_sound hT
  have hR' := checkRoots_sound hR
  have hEss' : ∀ a ∈ roots, Essential T roots a := fun a ha => by
    obtain ⟨⟨v, r, s⟩, _, rfl, he⟩ := hess a ha
    exact checkEss1_sound he
  have hImp : Impossible T cap (sortNats roots).toFinset := by
    unfold bucketContains Array.getD at hRoot
    dsimp only at hRoot
    split at hRoot
    next hi => exact hTop _ hi _ (List.contains_iff_mem.mp hRoot)
    next => simp at hRoot
  rw [sortNats_toFinset] at hImp
  exact lower_of_impossible p1 p2 p3 hR' hEss' hImp
def buildWires (base : List Decor) (steps : List (Nat × Nat × Nat)) : Array Decor :=
  steps.foldl (fun arr s =>
    let a := arr.getD s.2.1 (0, 0, 0)
    let b := arr.getD s.2.2 (0, 0, 0)
    arr.push (dbin s.1 a b)) base.toArray
lemma buildWires_faithful {pos neg base steps}
    (hbase : ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^128) :
    ∀ x ∈ (buildWires base steps).toList, faithful pos neg x ∧ x.1 < 2^128 := by
  have hdef : faithful pos neg (0, 0, 0) ∧ (0 : Nat) < 2^128 := ⟨faithful_zero pos neg, by decide⟩
  have hstep : ∀ (arr : Array Decor) (s : Nat × Nat × Nat),
      (∀ x ∈ arr.toList, faithful pos neg x ∧ x.1 < 2^128) →
      ∀ x ∈ (arr.push (dbin s.1 (arr.getD s.2.1 (0, 0, 0)) (arr.getD s.2.2 (0, 0, 0)))).toList,
        faithful pos neg x ∧ x.1 < 2^128 := by
    intro arr s harr x hx
    rw [Array.toList_push, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact harr x hx
    · have hget (i : Nat) : faithful pos neg (arr.getD i (0, 0, 0)) ∧ (arr.getD i (0, 0, 0)).1 < 2^128 := by
        unfold Array.getD
        split
        next hi => exact harr arr[i] (Array.getElem_mem_toList hi)
        next => exact hdef
      exact ⟨faithful_bin s.1 (hget s.2.1).1 (hget s.2.2).1, bin_lt s.1 _ _ (hget s.2.1).2 (hget s.2.2).2⟩
  unfold buildWires
  have hinit : ∀ x ∈ base.toArray.toList, faithful pos neg x ∧ x.1 < 2^128 := by simpa using hbase
  clear hbase
  generalize base.toArray = acc at hinit ⊢
  induction steps generalizing acc with
  | nil => exact hinit
  | cons s ss ih => exact ih _ (hstep acc s hinit)
lemma array_forall_of_list {α : Type} {P : α → Prop} {l : List α} (h : ∀ x ∈ l, P x) :
    ∀ i (hi : i < l.toArray.size), P l.toArray[i] :=
  fun i hi => h l.toArray[i] (Array.getElem_mem_toList hi)
def buildPools (W : Array Decor) (raw : List Nat) (slices : Array (Nat × Nat))
    (pspecs : List PoolSpec) : Array (Option BoundPool) :=
  (pspecs.map fun (slIdx, chIdxs) =>
    match slices[slIdx]? with
    | none => none
    | some (dom, lb) =>
      let cs := chIdxs.map fun (op, ia, ib) => (op, (W.getD ia (0, 0, 0)).1, (W.getD ib (0, 0, 0)).1)
      materialize raw cs dom lb).toArray
lemma buildPools_sound {W : Array Decor} {raw T} {slices : Array (Nat × Nat)} {pspecs : List PoolSpec}
    (hSlices : ∀ i (hi : i < slices.size), Slice raw T slices[i].1 slices[i].2) :
    ∀ i (hi : i < (buildPools W raw slices pspecs).size),
      ∀ c, (buildPools W raw slices pspecs)[i] = some c → ValidPool raw T c := by
  intro i hi c hc
  unfold buildPools at hi hc
  have hmem : some c ∈ pspecs.map (fun (slIdx, chIdxs) =>
      match slices[slIdx]? with
      | none => none
      | some (dom, lb) =>
        let cs := chIdxs.map fun (op, ia, ib) => (op, (W.getD ia (0, 0, 0)).1, (W.getD ib (0, 0, 0)).1)
        materialize raw cs dom lb) := by
    rw [← hc]
    exact Array.getElem_mem_toList hi
  obtain ⟨⟨slIdx, chIdxs⟩, _, hmat⟩ := List.mem_map.mp hmem
  cases hget_sl : slices[slIdx]? with
  | none => simp [hget_sl] at hmat
  | some sl =>
    simp only [hget_sl] at hmat
    have ⟨hsi, hval⟩ := Array.getElem?_eq_some_iff.mp hget_sl
    exact materialize_sound (hval ▸ hSlices slIdx hsi) hmat
def checkNode (W : Array Decor) (T fmask : Nat)
    (poolTable : Array (Option BoundPool)) (autosTable : Array (List (Nat × Nat)))
    (prevBuckets : Array (List (List Nat))) (k : Nat) (ns : NodeSpec) : Bool :=
  let ws := ns.1.map fun idx => W.getD idx (0, 0, 0)
  let vals := ws.map Prod.fst
  let pools := ns.2.1.filterMap fun pIdx => poolTable.getD pIdx none
  let nodeAutos := ns.2.2.filterMap fun aIdx => autosTable[aIdx]?
  decide vals.Nodup && !(vals.contains T) &&
    (k == 0 || testAll k ws.length fmask ws (coverage ws) pools nodeAutos prevBuckets ws)
def checkNodes (W : Array Decor) (T fmask : Nat)
    (poolTable : Array (Option BoundPool)) (autosTable : Array (List (Nat × Nat)))
    (prevBuckets : Array (List (List Nat))) (k : Nat) (nodes : List NodeSpec) : Bool :=
  nodes.all (checkNode W T fmask poolTable autosTable prevBuckets k)
lemma checkNode_sound {W : Array Decor} {raw pos neg T poolTable autosTable prevBuckets k ns}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hW : ∀ x ∈ W.toList, faithful pos neg x ∧ x.1 < 2^128)
    (hPoolTable : ∀ i (hi : i < poolTable.size), ∀ c, poolTable[i] = some c → ValidPool raw T c)
    (hAutos : ∀ sw ∈ autosTable.toList, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : ∀ i (hi : i < prevBuckets.size), ∀ xs ∈ prevBuckets[i], Impossible T (k - 1) xs.toFinset)
    (ok : checkNode W T (fullMask pos.length) poolTable autosTable prevBuckets k ns = true) :
    Impossible T k ((ns.1.map fun idx => (W.getD idx (0, 0, 0)).1).toFinset) := by
  have hdef : faithful pos neg (0, 0, 0) ∧ (0 : Nat) < 2^128 := ⟨faithful_zero pos neg, by decide⟩
  have hget (idx : Nat) : faithful pos neg (W.getD idx (0, 0, 0)) ∧ (W.getD idx (0, 0, 0)).1 < 2^128 := by
    unfold Array.getD; split
    next hi => exact hW W[idx] (Array.getElem_mem_toList hi)
    next => exact hdef
  unfold checkNode at ok
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.contains_eq_mem, Bool.or_eq_true, beq_iff_eq] at ok
  let ws := ns.1.map fun idx => W.getD idx (0, 0, 0)
  have hmap : ws.map Prod.fst = ns.1.map fun idx => (W.getD idx (0, 0, 0)).1 := by simp [ws, List.map_map, Function.comp_def]
  rw [← hmap]
  apply node_sound hT gp
    (fun w hw => by obtain ⟨idx, _, rfl⟩ := List.mem_map.mp hw; exact (hget idx).1)
    ok.1.1
    (fun w hw => by obtain ⟨idx, _, rfl⟩ := List.mem_map.mp hw; exact (hget idx).2)
    (of_decide_eq_false ok.1.2)
    (fun c hc => by
      obtain ⟨pIdx, _, hmat⟩ := List.mem_filterMap.mp hc
      unfold Array.getD at hmat
      split at hmat
      next hi => exact hPoolTable pIdx hi c hmat
      next => simp at hmat)
    (fun sw hsw => by
      obtain ⟨aIdx, _, ha⟩ := List.mem_filterMap.mp hsw
      have ⟨hi, hval⟩ := Array.getElem?_eq_some_iff.mp ha
      exact hAutos sw (hval ▸ Array.getElem_mem_toList hi))
    hPrev ok.2
def nodeVals (W : Array Decor) (ns : NodeSpec) : List Nat :=
  sortNats (ns.1.map fun idx => (W.getD idx (0, 0, 0)).1)
def insertBucket (buckets : Array (List (List Nat))) (xs : List Nat) : Array (List (List Nat)) :=
  let idx := hashWs buckets.size xs
  if h : idx < buckets.size then
    let b := buckets[idx]
    if b.contains xs then buckets else buckets.set idx (xs :: b) h
  else buckets
def buildBuckets (nb : Nat) (W : Array Decor) (nodes : List NodeSpec) : Array (List (List Nat)) :=
  nodes.foldl (fun acc ns => insertBucket acc (nodeVals W ns)) (Array.replicate nb [])
lemma insertBucket_mem {bks : Array (List (List Nat))} {P : List Nat → Prop} {xs : List Nat}
    (hb : ∀ i (hi : i < bks.size), ∀ ys ∈ bks[i], P ys) (hxs : P xs) :
    ∀ i (hi : i < (insertBucket bks xs).size), ∀ ys ∈ (insertBucket bks xs)[i], P ys := by
  unfold insertBucket
  dsimp only
  split
  next hidx =>
    split
    · exact hb
    · intro i hi ys hys
      rw [Array.size_set] at hi
      rw [Array.getElem_set] at hys
      split at hys
      next =>
        rcases List.mem_cons.mp hys with rfl | hys'
        · exact hxs
        · exact hb _ hidx ys hys'
      next => exact hb i hi ys hys
  next => exact hb
lemma buildBuckets_sound {W : Array Decor} {raw pos neg T poolTable autosTable prevBuckets k nb}
    {nodes : List NodeSpec}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hW : ∀ x ∈ W.toList, faithful pos neg x ∧ x.1 < 2^128)
    (hPoolTable : ∀ i (hi : i < poolTable.size), ∀ c, poolTable[i] = some c → ValidPool raw T c)
    (hAutos : ∀ sw ∈ autosTable.toList, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : ∀ i (hi : i < prevBuckets.size), ∀ xs ∈ prevBuckets[i], Impossible T (k - 1) xs.toFinset)
    (hNodes : checkNodes W T (fullMask pos.length) poolTable autosTable prevBuckets k nodes = true) :
    ∀ i (hi : i < (buildBuckets nb W nodes).size), ∀ xs ∈ (buildBuckets nb W nodes)[i], Impossible T k xs.toFinset := by
  have hmem : ∀ ns ∈ nodes, Impossible T k (nodeVals W ns).toFinset := fun ns hns => by
    unfold nodeVals
    rw [sortNats_toFinset]
    exact checkNode_sound hT gp hW hPoolTable hAutos hPrev (List.all_eq_true.mp hNodes ns hns)
  clear hNodes
  unfold buildBuckets
  have hinit : ∀ i (hi : i < (Array.replicate nb ([] : List (List Nat))).size),
      ∀ xs ∈ (Array.replicate nb ([] : List (List Nat)))[i], Impossible T k xs.toFinset := by
    intro i hi xs hxs; simp at hxs
  generalize Array.replicate nb ([] : List (List Nat)) = acc at hinit ⊢
  induction nodes generalizing acc with
  | nil => exact hinit
  | cons ns rest ih =>
    exact ih (fun x hx => hmem x (List.mem_cons_of_mem _ hx))
      (insertBucket acc (nodeVals W ns)) (insertBucket_mem hinit (hmem ns (List.mem_cons_self ..)))
lemma checkNodesBT_mem {W : BT Decor} {raw pos neg T poolTable autosTable prevBks k nodes}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) W)
    (hPoolTable : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) poolTable)
    (hAutos : btAll (fun sw => swapsValid sw = true ∧ permWord sw T = T) autosTable)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (k - 1) xs.toFinset) prevBks)
    (hNodes : checkNodesBT W T (fullMask pos.length) poolTable autosTable prevBks k nodes = true) :
    ∀ ns ∈ nodes, Impossible T k (nodeValsBT W ns).toFinset := by
  intro ns hns
  unfold nodeValsBT; rw [sortNats_toFinset]
  exact checkNodeBT_sound hT gp hW hPoolTable hAutos hPrev (List.all_eq_true.mp hNodes ns hns)
lemma forall_append {α : Type} {P : α → Prop} {l1 l2 : List α}
    (h1 : ∀ x ∈ l1, P x) (h2 : ∀ x ∈ l2, P x) : ∀ x ∈ l1 ++ l2, P x := by
  intro x hx; rcases List.mem_append.mp hx with h | h; exact h1 x h; exact h2 x h
lemma buildBucketsBT_of_mem {W : BT Decor} {T k nodes}
    (hmem : ∀ ns ∈ nodes, Impossible T k (nodeValsBT W ns).toFinset) :
    btAll (fun bk => ∀ xs ∈ bk, Impossible T k xs.toFinset) (buildBucketsBT W nodes) := by
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
def buildPoolsSubBT (pdepth : Nat) (W : BT Decor) (raw : List Nat) (slices : BT (Option (Nat × Nat)))
    (pspecs : BT (Option PoolSpec)) (used : List Nat) : BT (Option BoundPool) :=
  used.foldl (fun acc pIdx =>
    match btGet none pspecs pIdx with
    | none => acc
    | some (slIdx, chIdxs) =>
      match btGet none slices slIdx with
      | none => acc
      | some (dom, lb) =>
        let cs := chIdxs.map fun (op, ia, ib) => (op, (btGet (0, 0, 0) W ia).1, (btGet (0, 0, 0) W ib).1)
        btSet pdepth acc pIdx (materialize raw cs dom lb)) BT.empty
lemma buildPoolsSubBT_sound {pdepth} {W : BT Decor} {raw T} {slices : BT (Option (Nat × Nat))}
    {pspecs : BT (Option PoolSpec)} {used : List Nat}
    (hSlices : btAll (fun o => ∀ p, o = some p → Slice raw T p.1 p.2) slices) :
    btAll (fun o => ∀ c, o = some c → ValidPool raw T c) (buildPoolsSubBT pdepth W raw slices pspecs used) := by
  unfold buildPoolsSubBT
  have hinit : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) (BT.empty : BT (Option BoundPool)) := trivial
  generalize (BT.empty : BT (Option BoundPool)) = acc at hinit ⊢
  induction used generalizing acc with
  | nil => exact hinit
  | cons pIdx rest ih =>
    apply ih
    dsimp only
    cases hps : btGet none pspecs pIdx with
    | none => simp only [hps]; exact hinit
    | some spec =>
      cases hsl : btGet none slices spec.1 with
      | none => simp only [hps, hsl]; exact hinit
      | some sl =>
        simp only [hps, hsl]
        apply btAll_set hinit
        intro c hc
        exact materialize_sound (btAll_get (d := none) hSlices (fun _ h => by simp at h) spec.1 sl hsl) hc

def dualRow (r : Row) : Row := ⟨(r.val ^^^ 63) % 128, Nat.mod_lt _ (by decide)⟩

lemma map_available (f : Row → Row) {b c : List Wire}
    (cover : ∀ w ∈ b, Avail c (restrictW f w)) {w : Wire} (hw : Avail b w) :
    Avail c (restrictW f w) := by
  rcases hw with hb | ⟨bit,rfl⟩ | hi
  · exact cover _ hb
  · exact Or.inr (Or.inl ⟨bit,rfl⟩)
  · have h : Avail c (invW (restrictW f w)) := cover _ hi
    simpa only [invW_inv] using avail_inv h

lemma map_reach (f : Row → Row) {R S : List Wire}
    (cover : ∀ w ∈ R, Avail S (restrictW f w)) {p b} (hr : Reach R p b) :
    ∃ c, Reach S p c ∧ ∀ w ∈ b, Avail c (restrictW f w) := by
  induction p generalizing b with
  | zero =>
    have hb : b = R := hr
    exact ⟨S,rfl,hb.symm ▸ cover⟩
  | succ p ih =>
    obtain ⟨op,b,a,d,prev,ha,hd,rfl⟩ := hr
    obtain ⟨c,hc,hmap⟩ := ih prev
    let w := comb2 op (restrictW f a) (restrictW f d)
    have eq : restrictW f (comb2 op a d) = w := by cases op <;> rfl
    refine ⟨w :: c,⟨op,c,_,_,hc,map_available f hmap ha,map_available f hmap hd,rfl⟩,?_⟩
    intro t ht
    rcases List.mem_cons.mp ht with rfl | hold
    · rw [eq]
      exact Or.inl List.mem_cons_self
    · exact avail_cons w (hmap t hold)

lemma dualLower {roots : List Nat} {T G L : Nat}
    (hvars : ∀ r : Row, roots.all (fun a => decide (obs a (dualRow r) = !(obs a r))) = true)
    (hgoal : ∀ r : Row, (!(obs T (dualRow r))) = obs G r)
    (prior : Lower roots G L) : Lower roots T L := by
  intro p bank hr hav
  have maps (w : Wire) (hw : w ∈ roots.map obs) : Avail (roots.map obs) (restrictW dualRow w) := by
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hw
    have eq : restrictW dualRow (obs a) = invW (obs a) :=
      funext fun r => of_decide_eq_true (List.all_eq_true.mp (hvars r) a ha)
    rw [eq]
    exact avail_inv (Or.inl (List.mem_map.mpr ⟨a,ha,rfl⟩))
  obtain ⟨c,hc,hmap⟩ := map_reach dualRow maps hr
  have eq : invW (restrictW dualRow (obs T)) = obs G := funext hgoal
  exact prior p c hc (eq ▸ avail_inv (map_available dualRow hmap hav))

def face0_G_0 : Nat := 0xffffff00ff000000ffffff00ff000000
def face0_R_0 : List Nat := varsOf 56
def face0_pos_0 : List Nat := [24,24,40,40,48,48,24,40,48]
def face0_neg_0 : List Nat := [16,8,32,8,32,16,32,16,8]
def face0_fmask_0 : Nat := fullMask 9
def face0_base_0 : List Decor := [(0xff00ff00ff00ff00ff00ff00ff00ff00,0xcf,0x10a),(0xffff0000ffff0000ffff0000ffff0000,0x173,0xa1),(0xffffffff00000000ffffffff00000000,0x1bc,0x54)]
def face0_steps_0 : List (Nat × Nat × Nat) := []
def face0_W_0 : Array Decor := buildWires face0_base_0 face0_steps_0
def face0_autos_0 : Array (List (Nat × Nat)) := #[]
def face0_slicesL_0 : List (Nat × Nat) := []
def face0_slices_0 : Array (Nat × Nat) := face0_slicesL_0.toArray
def face0_ps_0 : List PoolSpec := []
def face0_P_0 : Array (Option BoundPool) := buildPools face0_W_0 face0_R_0 face0_slices_0 face0_ps_0
lemma face0_gp_0 : goodPairs face0_G_0 face0_pos_0 face0_neg_0 := goodPairs_of (by decide +kernel)
lemma face0_base_0_ok : ∀ x ∈ face0_base_0, faithful face0_pos_0 face0_neg_0 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma face0_W_0_ok : ∀ x ∈ face0_W_0.toList, faithful face0_pos_0 face0_neg_0 x ∧ x.1 < 2^128 := buildWires_faithful face0_base_0_ok
lemma face0_autos_0_ok : ∀ sw ∈ face0_autos_0.toList, swapsValid sw = true ∧ permWord sw face0_G_0 = face0_G_0 := autos_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma face0_slices_0_ok : ∀ i (hi : i < face0_slices_0.size), Slice face0_R_0 face0_G_0 face0_slices_0[i].1 face0_slices_0[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice face0_R_0 face0_G_0 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma face0_P_0_ok : ∀ i (hi : i < face0_P_0.size), ∀ c, face0_P_0[i] = some c → ValidPool face0_R_0 face0_G_0 c := buildPools_sound face0_slices_0_ok
def face0_bk_0_init : Array (List (List Nat)) := #[]
lemma face0_bk_0_init_ok : ∀ i (hi : i < face0_bk_0_init.size), ∀ xs ∈ face0_bk_0_init[i], Impossible face0_G_0 (0 - 1) xs.toFinset := by intro i hi; simp [face0_bk_0_init] at hi
def face0_nodes_0_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_chk_0_0 : checkNodes face0_W_0 face0_G_0 face0_fmask_0 face0_P_0 face0_autos_0 face0_bk_0_init 0 face0_nodes_0_0 = true := by decide +kernel
def face0_bk_0_0 : Array (List (List Nat)) := buildBuckets 1 face0_W_0 face0_nodes_0_0
lemma face0_bk_0_0_ok : ∀ i (hi : i < face0_bk_0_0.size), ∀ xs ∈ face0_bk_0_0[i], Impossible face0_G_0 0 xs.toFinset :=
  buildBuckets_sound (by decide) face0_gp_0 face0_W_0_ok face0_P_0_ok face0_autos_0_ok face0_bk_0_init_ok face0_chk_0_0
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_chk_0_1 : checkNodes face0_W_0 face0_G_0 face0_fmask_0 face0_P_0 face0_autos_0 face0_bk_0_0 1 face0_nodes_0_0 = true := by decide +kernel
lemma face0_bk_0_1_ok : ∀ i (hi : i < face0_bk_0_0.size), ∀ xs ∈ face0_bk_0_0[i], Impossible face0_G_0 1 xs.toFinset :=
  buildBuckets_sound (by decide) face0_gp_0 face0_W_0_ok face0_P_0_ok face0_autos_0_ok face0_bk_0_0_ok face0_chk_0_1
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_chk_0_2 : checkNodes face0_W_0 face0_G_0 face0_fmask_0 face0_P_0 face0_autos_0 face0_bk_0_0 2 face0_nodes_0_0 = true := by decide +kernel
lemma face0_bk_0_2_ok : ∀ i (hi : i < face0_bk_0_0.size), ∀ xs ∈ face0_bk_0_0[i], Impossible face0_G_0 2 xs.toFinset :=
  buildBuckets_sound (by decide) face0_gp_0 face0_W_0_ok face0_P_0_ok face0_autos_0_ok face0_bk_0_1_ok face0_chk_0_2
def face0_nodes_0_3 : List NodeSpec := [([0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_chk_0_3 : checkNodes face0_W_0 face0_G_0 face0_fmask_0 face0_P_0 face0_autos_0 face0_bk_0_0 3 face0_nodes_0_3 = true := by decide +kernel
def face0_bk_0_3 : Array (List (List Nat)) := buildBuckets 1 face0_W_0 face0_nodes_0_3
lemma face0_bk_0_3_ok : ∀ i (hi : i < face0_bk_0_3.size), ∀ xs ∈ face0_bk_0_3[i], Impossible face0_G_0 3 xs.toFinset :=
  buildBuckets_sound (by decide) face0_gp_0 face0_W_0_ok face0_P_0_ok face0_autos_0_ok face0_bk_0_2_ok face0_chk_0_3
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_forestRoot_0_ok : forestRootCheck face0_R_0 face0_G_0 [(VAR 3,24,16),(VAR 4,24,8),(VAR 5,40,8)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_forestRoot_0_in : bucketContains face0_bk_0_3 face0_R_0 = true := by decide +kernel
lemma face0_low_0 : Lower face0_R_0 face0_G_0 4 := lower_of_forest face0_forestRoot_0_ok face0_bk_0_3_ok face0_forestRoot_0_in
def face0_G_7 : Nat := 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0
def face0_R_7 : List Nat := varsOf 14
lemma face0_low_7_ok : carryOK [(1,2),(1,5),(2,4),(1,3)] face0_R_7 face0_G_7 face0_R_0 face0_G_0 = true := by decide +kernel
lemma face0_low_7 : Lower face0_R_7 face0_G_7 4 := carry_of face0_low_7_ok face0_low_0
def face0_G_9 : Nat := 0xfcfcfcfcc0c0c0c0fcfcfcfcc0c0c0c0
def face0_R_9 : List Nat := varsOf 38
lemma face0_low_9_ok : carryOK [(2,4),(1,3)] face0_R_9 face0_G_9 face0_R_0 face0_G_0 = true := by decide +kernel
lemma face0_low_9 : Lower face0_R_9 face0_G_9 4 := carry_of face0_low_9_ok face0_low_0
def face0_G_13 : Nat := 0xffccffcccc00cc00ffccffcccc00cc00
def face0_R_13 : List Nat := varsOf 42
lemma face0_low_13_ok : carryOK [(2,4),(1,2),(1,3)] face0_R_13 face0_G_13 face0_R_0 face0_G_0 = true := by decide +kernel
lemma face0_low_13 : Lower face0_R_13 face0_G_13 4 := carry_of face0_low_13_ok face0_low_0
def face0_G_14 : Nat := 0xfff0f000fff0f000fff0f000fff0f000
def face0_R_14 : List Nat := varsOf 28
lemma face0_low_14_ok : carryOK [(2,5),(2,4),(2,3)] face0_R_14 face0_G_14 face0_R_0 face0_G_0 = true := by decide +kernel
lemma face0_low_14 : Lower face0_R_14 face0_G_14 4 := carry_of face0_low_14_ok face0_low_0
def face0_G_15 : Nat := 0xfff0fff0f000f000fff0fff0f000f000
def face0_R_15 : List Nat := varsOf 44
lemma face0_low_15_ok : carryOK [(2,4),(2,3)] face0_R_15 face0_G_15 face0_R_0 face0_G_0 = true := by decide +kernel
lemma face0_low_15 : Lower face0_R_15 face0_G_15 4 := carry_of face0_low_15_ok face0_low_0
def face0_G_17 : Nat := 0xffffcccccccc0000ffffcccccccc0000
def face0_R_17 : List Nat := varsOf 50
lemma face0_low_17_ok : carryOK [(1,2),(1,3)] face0_R_17 face0_G_17 face0_R_0 face0_G_0 = true := by decide +kernel
lemma face0_low_17 : Lower face0_R_17 face0_G_17 4 := carry_of face0_low_17_ok face0_low_0
def face0_G_18 : Nat := 0xfffff0f0f0f00000fffff0f0f0f00000
def face0_R_18 : List Nat := varsOf 52
lemma face0_low_18_ok : carryOK [(2,3)] face0_R_18 face0_G_18 face0_R_0 face0_G_0 = true := by decide +kernel
lemma face0_low_18 : Lower face0_R_18 face0_G_18 4 := carry_of face0_low_18_ok face0_low_0
def face0_G_21 : Nat := 0xfff0f000f0000000fff0f000f0000000
def face0_R_21 : List Nat := varsOf 60
def face0_pos_21 : List Nat := [28,28,28,44,44,44,52,52,52,56,56,56,28,28,28,44,44,44,52,52,52,56,56,56]
def face0_neg_21 : List Nat := [24,20,12,40,36,12,48,36,20,48,40,24,36,40,48,20,24,48,12,24,40,12,20,36]
def face0_fmask_21 : Nat := fullMask 24
def face0_base_21 : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x1ff1ff,0xe491b6),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xe3fe3f,0x3d2c2d),(0xffff0000ffff0000ffff0000ffff0000,0xfc7fc7,0x4bcb43),(0xffffffff00000000ffffffff00000000,0xff8ff8,0x9276d8)]
def face0_steps_21 : List (Nat × Nat × Nat) := [(0,0,1),(0,0,2),(3,4,2),(0,4,2),(0,1,2),(3,7,3)]
def face0_W_21 : Array Decor := buildWires face0_base_21 face0_steps_21
def face0_autos_21 : Array (List (Nat × Nat)) := #[[],[(4,5)],[(2,3)],[(4,5),(2,3)],[(3,4)],[(3,5),(3,4)],[(2,3),(2,4)],[(3,5),(2,3),(2,4)],[(3,5),(2,4)]]
def face0_slicesL_21 : List (Nat × Nat) := [(subcube 0 16,4),(subcube 0 4,4),(subcube 0 8,4),(subcube 0 32,4)]
def face0_slices_21 : Array (Nat × Nat) := face0_slicesL_21.toArray
def face0_ps_21 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[])]
def face0_P_21 : Array (Option BoundPool) := buildPools face0_W_21 face0_R_21 face0_slices_21 face0_ps_21
lemma face0_gp_21 : goodPairs face0_G_21 face0_pos_21 face0_neg_21 := goodPairs_of (by decide +kernel)
lemma face0_base_21_ok : ∀ x ∈ face0_base_21, faithful face0_pos_21 face0_neg_21 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma face0_W_21_ok : ∀ x ∈ face0_W_21.toList, faithful face0_pos_21 face0_neg_21 x ∧ x.1 < 2^128 := buildWires_faithful face0_base_21_ok
lemma face0_autos_21_ok : ∀ sw ∈ face0_autos_21.toList, swapsValid sw = true ∧ permWord sw face0_G_21 = face0_G_21 := autos_of (by decide +kernel)
lemma face0_sl_21_0_ok : sliceDirectCheck 0 16 0 face0_R_21 face0_G_21 face0_R_15 face0_G_15 = true := by decide +kernel
lemma face0_sl_21_0 : Slice face0_R_21 face0_G_21 (subcube 0 16) 4 := slice_direct face0_sl_21_0_ok face0_low_15
lemma face0_sl_21_1_ok : sliceDirectCheck 0 4 0 face0_R_21 face0_G_21 face0_R_0 face0_G_0 = true := by decide +kernel
lemma face0_sl_21_1 : Slice face0_R_21 face0_G_21 (subcube 0 4) 4 := slice_direct face0_sl_21_1_ok face0_low_0
lemma face0_sl_21_2_ok : sliceDirectCheck 0 8 0 face0_R_21 face0_G_21 face0_R_18 face0_G_18 = true := by decide +kernel
lemma face0_sl_21_2 : Slice face0_R_21 face0_G_21 (subcube 0 8) 4 := slice_direct face0_sl_21_2_ok face0_low_18
lemma face0_sl_21_3_ok : sliceDirectCheck 0 32 0 face0_R_21 face0_G_21 face0_R_14 face0_G_14 = true := by decide +kernel
lemma face0_sl_21_3 : Slice face0_R_21 face0_G_21 (subcube 0 32) 4 := slice_direct face0_sl_21_3_ok face0_low_14
set_option maxRecDepth 200000 in
lemma face0_slices_21_ok : ∀ i (hi : i < face0_slices_21.size), Slice face0_R_21 face0_G_21 face0_slices_21[i].1 face0_slices_21[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice face0_R_21 face0_G_21 p.1 p.2) (forall_cons face0_sl_21_0 (forall_cons face0_sl_21_1 (forall_cons face0_sl_21_2 (forall_cons face0_sl_21_3 (fun _ h => (List.not_mem_nil h).elim)))))
lemma face0_P_21_ok : ∀ i (hi : i < face0_P_21.size), ∀ c, face0_P_21[i] = some c → ValidPool face0_R_21 face0_G_21 c := buildPools_sound face0_slices_21_ok
lemma face0_bk_21_init_ok : ∀ i (hi : i < face0_bk_0_init.size), ∀ xs ∈ face0_bk_0_init[i], Impossible face0_G_21 (0 - 1) xs.toFinset := by intro i hi; simp [face0_bk_0_init] at hi
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_chk_21_0 : checkNodes face0_W_21 face0_G_21 face0_fmask_21 face0_P_21 face0_autos_21 face0_bk_0_init 0 face0_nodes_0_0 = true := by decide +kernel
def face0_bk_21_0 : Array (List (List Nat)) := buildBuckets 1 face0_W_21 face0_nodes_0_0
lemma face0_bk_21_0_ok : ∀ i (hi : i < face0_bk_21_0.size), ∀ xs ∈ face0_bk_21_0[i], Impossible face0_G_21 0 xs.toFinset :=
  buildBuckets_sound (by decide) face0_gp_21 face0_W_21_ok face0_P_21_ok face0_autos_21_ok face0_bk_21_init_ok face0_chk_21_0
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_chk_21_1 : checkNodes face0_W_21 face0_G_21 face0_fmask_21 face0_P_21 face0_autos_21 face0_bk_21_0 1 face0_nodes_0_0 = true := by decide +kernel
lemma face0_bk_21_1_ok : ∀ i (hi : i < face0_bk_21_0.size), ∀ xs ∈ face0_bk_21_0[i], Impossible face0_G_21 1 xs.toFinset :=
  buildBuckets_sound (by decide) face0_gp_21 face0_W_21_ok face0_P_21_ok face0_autos_21_ok face0_bk_21_0_ok face0_chk_21_1
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_chk_21_2 : checkNodes face0_W_21 face0_G_21 face0_fmask_21 face0_P_21 face0_autos_21 face0_bk_21_0 2 face0_nodes_0_0 = true := by decide +kernel
lemma face0_bk_21_2_ok : ∀ i (hi : i < face0_bk_21_0.size), ∀ xs ∈ face0_bk_21_0[i], Impossible face0_G_21 2 xs.toFinset :=
  buildBuckets_sound (by decide) face0_gp_21 face0_W_21_ok face0_P_21_ok face0_autos_21_ok face0_bk_21_1_ok face0_chk_21_2
def face0_nodes_21_3 : List NodeSpec := [([4,5,8,3],[0,1],[]),([9,0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_chk_21_3 : checkNodes face0_W_21 face0_G_21 face0_fmask_21 face0_P_21 face0_autos_21 face0_bk_21_0 3 face0_nodes_21_3 = true := by decide +kernel
def face0_bk_21_3 : Array (List (List Nat)) := buildBuckets 1 face0_W_21 face0_nodes_21_3
lemma face0_bk_21_3_ok : ∀ i (hi : i < face0_bk_21_3.size), ∀ xs ∈ face0_bk_21_3[i], Impossible face0_G_21 3 xs.toFinset :=
  buildBuckets_sound (by decide) face0_gp_21 face0_W_21_ok face0_P_21_ok face0_autos_21_ok face0_bk_21_2_ok face0_chk_21_3
def face0_nodes_21_4 : List NodeSpec := [([4,5,1,2,3],[0,2],[0]),([6,0,1,2,3],[],[]),([7,0,1,2,3],[3],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_chk_21_4 : checkNodes face0_W_21 face0_G_21 face0_fmask_21 face0_P_21 face0_autos_21 face0_bk_21_3 4 face0_nodes_21_4 = true := by decide +kernel
def face0_bk_21_4 : Array (List (List Nat)) := buildBuckets 2 face0_W_21 face0_nodes_21_4
lemma face0_bk_21_4_ok : ∀ i (hi : i < face0_bk_21_4.size), ∀ xs ∈ face0_bk_21_4[i], Impossible face0_G_21 4 xs.toFinset :=
  buildBuckets_sound (by decide) face0_gp_21 face0_W_21_ok face0_P_21_ok face0_autos_21_ok face0_bk_21_3_ok face0_chk_21_4
def face0_nodes_21_5 : List NodeSpec := [([4,0,1,2,3],[2,1,0,3],[0,1,2,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_chk_21_5 : checkNodes face0_W_21 face0_G_21 face0_fmask_21 face0_P_21 face0_autos_21 face0_bk_21_4 5 face0_nodes_21_5 = true := by decide +kernel
def face0_bk_21_5 : Array (List (List Nat)) := buildBuckets 1 face0_W_21 face0_nodes_21_5
lemma face0_bk_21_5_ok : ∀ i (hi : i < face0_bk_21_5.size), ∀ xs ∈ face0_bk_21_5[i], Impossible face0_G_21 5 xs.toFinset :=
  buildBuckets_sound (by decide) face0_gp_21 face0_W_21_ok face0_P_21_ok face0_autos_21_ok face0_bk_21_4_ok face0_chk_21_5
def face0_nodes_21_6 : List NodeSpec := [([0,1,2,3],[1,2,0,3],[0,4,5,6,7,8])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_chk_21_6 : checkNodes face0_W_21 face0_G_21 face0_fmask_21 face0_P_21 face0_autos_21 face0_bk_21_5 6 face0_nodes_21_6 = true := by decide +kernel
def face0_bk_21_6 : Array (List (List Nat)) := buildBuckets 1 face0_W_21 face0_nodes_21_6
lemma face0_bk_21_6_ok : ∀ i (hi : i < face0_bk_21_6.size), ∀ xs ∈ face0_bk_21_6[i], Impossible face0_G_21 6 xs.toFinset :=
  buildBuckets_sound (by decide) face0_gp_21 face0_W_21_ok face0_P_21_ok face0_autos_21_ok face0_bk_21_5_ok face0_chk_21_6
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_forestRoot_21_ok : forestRootCheck face0_R_21 face0_G_21 [(VAR 2,28,24),(VAR 3,28,20),(VAR 4,28,12),(VAR 5,44,12)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_forestRoot_21_in : bucketContains face0_bk_21_6 face0_R_21 = true := by decide +kernel
lemma face0_low_21 : Lower face0_R_21 face0_G_21 7 := lower_of_forest face0_forestRoot_21_ok face0_bk_21_6_ok face0_forestRoot_21_in
def face0_G_31 : Nat := 0xfcc0c000fcc0c000fcc0c000fcc0c000
def face0_R_31 : List Nat := varsOf 30
lemma face0_low_31_ok : carryOK [(1,5),(1,4),(1,3),(1,2)] face0_R_31 face0_G_31 face0_R_21 face0_G_21 = true := by decide +kernel
lemma face0_low_31 : Lower face0_R_31 face0_G_31 7 := carry_of face0_low_31_ok face0_low_21
def face0_G_32 : Nat := 0xfcc0fcc0c000c000fcc0fcc0c000c000
def face0_R_32 : List Nat := varsOf 46
lemma face0_low_32_ok : carryOK [(1,4),(1,3),(1,2)] face0_R_32 face0_G_32 face0_R_21 face0_G_21 = true := by decide +kernel
lemma face0_low_32 : Lower face0_R_32 face0_G_32 7 := carry_of face0_low_32_ok face0_low_21
def face0_G_33 : Nat := 0xfcfcc0c0c0c00000fcfcc0c0c0c00000
def face0_R_33 : List Nat := varsOf 54
lemma face0_low_33_ok : carryOK [(1,3),(1,2)] face0_R_33 face0_G_33 face0_R_21 face0_G_21 = true := by decide +kernel
lemma face0_low_33 : Lower face0_R_33 face0_G_33 7 := carry_of face0_low_33_ok face0_low_21
def face0_G_37 : Nat := 0xffcccc00cc000000ffcccc00cc000000
def face0_R_37 : List Nat := varsOf 58
lemma face0_low_37_ok : carryOK [(1,2)] face0_R_37 face0_G_37 face0_R_21 face0_G_21 = true := by decide +kernel
lemma face0_low_37 : Lower face0_R_37 face0_G_37 7 := carry_of face0_low_37_ok face0_low_21
def face0_G_47 : Nat := 0xfcc0c000c0000000fcc0c000c0000000
def face0_R_47 : List Nat := varsOf 62
def face0_pos_47 : List Nat := [30,30,30,30,46,46,46,46,54,54,54,54,58,58,58,58,60,60,60,60,30,30,30,30,30,30,46,46,46,46,46,46,54,54,54,54,54,54,58,58,58,58,58,58,60,60,60,60,60,60]
def face0_neg_47 : List Nat := [28,26,22,14,44,42,38,14,52,50,38,22,56,50,42,26,56,52,44,28,38,42,44,50,52,56,22,26,28,50,52,56,14,26,28,42,44,56,14,22,28,38,44,52,14,22,26,38,42,50]
def face0_fmask_47 : Nat := fullMask 50
def face0_base_47 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xffffff0ffff,0x3f2cb2cb0eeee),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x3f03fffff0fff,0xbfd5555e0ddd),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x3ffc0fffff0ff,0x1557f9a6dd0bb),(0xffff0000ffff0000ffff0000ffff0000,0x3ffff03ffff0f,0x269a6ff8bbb07),(0xffffffff00000000ffffffff00000000,0x3fffffc0ffff0,0x38e38e3f77770)]
def face0_steps_47 : List (Nat × Nat × Nat) := [(0,0,1),(0,2,3),(0,0,2),(3,5,2),(0,5,2),(0,1,3),(0,3,4),(3,8,3),(2,5,6),(0,9,3),(0,1,2),(0,0,3),(3,9,3),(0,5,3),(3,13,0),(0,1,4),(0,2,4),(3,12,4),(3,16,4),(3,14,4),(0,0,4),(3,14,0),(0,12,4),(1,14,4),(2,2,11),(0,17,4),(0,14,4),(0,16,4),(3,17,4),(3,14,1),(3,31,0)]
def face0_W_47 : Array Decor := buildWires face0_base_47 face0_steps_47
def face0_autos_47 : Array (List (Nat × Nat)) := #[[],[(1,2)],[(1,3),(1,2)],[(1,2),(2,4),(1,5)],[(4,5)],[(1,5),(1,4),(1,3),(1,2)],[(3,5),(3,4)],[(3,5),(2,3),(2,4)],[(3,5),(1,2),(1,4)],[(2,3),(1,3),(2,5),(1,4)],[(2,3),(3,5),(2,4)],[(3,4),(3,5)],[(3,4)],[(3,4),(2,3),(2,5)],[(2,3),(2,4)],[(3,4),(2,3),(1,2),(1,5)],[(2,3),(1,2),(1,4)],[(3,5),(2,3),(1,2),(1,4)],[(3,5),(2,4)],[(2,5),(2,4),(2,3)],[(2,4)],[(2,3),(3,5),(1,2),(1,4)],[(2,3)],[(1,4),(1,3),(1,2)],[(2,4),(2,3)],[(4,5),(1,2),(1,3)],[(2,5),(1,4)],[(4,5),(1,2)],[(4,5),(2,3)],[(1,2),(1,4)],[(3,4),(1,2)],[(4,5),(1,3),(1,2)],[(2,5),(2,4)],[(3,5),(3,4),(1,2)],[(1,3),(1,4),(1,2)],[(3,5),(1,3),(1,4),(1,2)],[(2,4),(1,3)],[(1,2),(2,3),(1,4)],[(1,2),(1,3)],[(2,4),(1,2),(1,3)],[(2,3),(2,5),(1,4)],[(2,5),(2,4),(1,2),(1,3)],[(2,5),(2,4),(1,3)],[(1,2),(1,5),(2,4),(1,3)]]
def face0_slicesL_47 : List (Nat × Nat) := [(subcube 0 12,4),(subcube 0 6,4),(subcube 0 32,7),(subcube 0 48,4),(subcube 0 2,7),(subcube 0 24,4),(subcube 0 20,4),(subcube 0 10,4),(subcube 0 8,7),(subcube 0 16,7),(subcube 0 4,7),(subcube 0 34,4),(subcube 0 18,4)]
def face0_slices_47 : Array (Nat × Nat) := face0_slicesL_47.toArray
def face0_ps_47 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(2,[(0,0,1),(0,0,2),(0,1,2)]),(8,[(0,0,1),(0,0,3),(0,1,3)]),(9,[]),(4,[(0,5,2),(0,9,3),(3,14,4)]),(2,[(0,0,1),(0,5,2),(3,9,3)]),(4,[(0,5,2),(0,5,3),(0,2,3)]),(10,[]),(9,[(0,0,1),(0,0,2)]),(8,[(0,0,1),(0,1,3)]),(2,[(0,0,1),(3,5,2)]),(8,[(0,0,1),(3,8,3)]),(9,[(0,0,1),(3,5,2)]),(4,[(0,2,3),(2,5,6)]),(8,[]),(9,[(0,0,1),(0,5,2)]),(4,[(0,5,2),(0,2,3)]),(2,[(0,0,1),(0,5,2)]),(4,[(0,1,2)]),(9,[(0,0,1),(0,0,2),(0,1,2)]),(10,[(0,5,2),(0,0,3)]),(8,[(0,0,1),(0,0,3)]),(11,[]),(4,[(0,5,2),(0,9,3)]),(4,[(0,5,2),(3,9,3)]),(10,[(0,5,2),(3,9,3)]),(8,[(0,0,1),(3,9,3)]),(2,[(0,0,1),(0,0,2)]),(10,[(0,5,2),(0,9,3)]),(8,[(0,0,1),(0,9,3)]),(4,[(0,5,2),(0,5,3)]),(12,[]),(8,[(0,0,1)]),(9,[(0,0,1)]),(4,[(0,2,3)]),(10,[(0,2,3)]),(10,[(0,0,2)]),(4,[(0,5,2)]),(10,[(0,5,2)]),(2,[(0,0,1)])]
def face0_P_47 : Array (Option BoundPool) := buildPools face0_W_47 face0_R_47 face0_slices_47 face0_ps_47
lemma face0_gp_47 : goodPairs face0_G_47 face0_pos_47 face0_neg_47 := goodPairs_of (by decide +kernel)
lemma face0_base_47_ok : ∀ x ∈ face0_base_47, faithful face0_pos_47 face0_neg_47 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma face0_W_47_ok : ∀ x ∈ face0_W_47.toList, faithful face0_pos_47 face0_neg_47 x ∧ x.1 < 2^128 := buildWires_faithful face0_base_47_ok
lemma face0_autos_47_ok : ∀ sw ∈ face0_autos_47.toList, swapsValid sw = true ∧ permWord sw face0_G_47 = face0_G_47 := autos_of (by decide +kernel)
lemma face0_sl_47_0_ok : sliceDirectCheck 0 12 0 face0_R_47 face0_G_47 face0_R_17 face0_G_17 = true := by decide +kernel
lemma face0_sl_47_0 : Slice face0_R_47 face0_G_47 (subcube 0 12) 4 := slice_direct face0_sl_47_0_ok face0_low_17
lemma face0_sl_47_1_ok : sliceDirectCheck 0 6 0 face0_R_47 face0_G_47 face0_R_0 face0_G_0 = true := by decide +kernel
lemma face0_sl_47_1 : Slice face0_R_47 face0_G_47 (subcube 0 6) 4 := slice_direct face0_sl_47_1_ok face0_low_0
lemma face0_sl_47_2_ok : sliceDirectCheck 0 32 0 face0_R_47 face0_G_47 face0_R_31 face0_G_31 = true := by decide +kernel
lemma face0_sl_47_2 : Slice face0_R_47 face0_G_47 (subcube 0 32) 7 := slice_direct face0_sl_47_2_ok face0_low_31
lemma face0_sl_47_3_ok : sliceDirectCheck 0 48 0 face0_R_47 face0_G_47 face0_R_7 face0_G_7 = true := by decide +kernel
lemma face0_sl_47_3 : Slice face0_R_47 face0_G_47 (subcube 0 48) 4 := slice_direct face0_sl_47_3_ok face0_low_7
lemma face0_sl_47_4_ok : sliceDirectCheck 0 2 0 face0_R_47 face0_G_47 face0_R_21 face0_G_21 = true := by decide +kernel
lemma face0_sl_47_4 : Slice face0_R_47 face0_G_47 (subcube 0 2) 7 := slice_direct face0_sl_47_4_ok face0_low_21
lemma face0_sl_47_5_ok : sliceDirectCheck 0 24 0 face0_R_47 face0_G_47 face0_R_9 face0_G_9 = true := by decide +kernel
lemma face0_sl_47_5 : Slice face0_R_47 face0_G_47 (subcube 0 24) 4 := slice_direct face0_sl_47_5_ok face0_low_9
lemma face0_sl_47_6_ok : sliceDirectCheck 0 20 0 face0_R_47 face0_G_47 face0_R_13 face0_G_13 = true := by decide +kernel
lemma face0_sl_47_6 : Slice face0_R_47 face0_G_47 (subcube 0 20) 4 := slice_direct face0_sl_47_6_ok face0_low_13
lemma face0_sl_47_7_ok : sliceDirectCheck 0 10 0 face0_R_47 face0_G_47 face0_R_18 face0_G_18 = true := by decide +kernel
lemma face0_sl_47_7 : Slice face0_R_47 face0_G_47 (subcube 0 10) 4 := slice_direct face0_sl_47_7_ok face0_low_18
lemma face0_sl_47_8_ok : sliceDirectCheck 0 8 0 face0_R_47 face0_G_47 face0_R_33 face0_G_33 = true := by decide +kernel
lemma face0_sl_47_8 : Slice face0_R_47 face0_G_47 (subcube 0 8) 7 := slice_direct face0_sl_47_8_ok face0_low_33
lemma face0_sl_47_9_ok : sliceDirectCheck 0 16 0 face0_R_47 face0_G_47 face0_R_32 face0_G_32 = true := by decide +kernel
lemma face0_sl_47_9 : Slice face0_R_47 face0_G_47 (subcube 0 16) 7 := slice_direct face0_sl_47_9_ok face0_low_32
lemma face0_sl_47_10_ok : sliceDirectCheck 0 4 0 face0_R_47 face0_G_47 face0_R_37 face0_G_37 = true := by decide +kernel
lemma face0_sl_47_10 : Slice face0_R_47 face0_G_47 (subcube 0 4) 7 := slice_direct face0_sl_47_10_ok face0_low_37
lemma face0_sl_47_11_ok : sliceDirectCheck 0 34 0 face0_R_47 face0_G_47 face0_R_14 face0_G_14 = true := by decide +kernel
lemma face0_sl_47_11 : Slice face0_R_47 face0_G_47 (subcube 0 34) 4 := slice_direct face0_sl_47_11_ok face0_low_14
lemma face0_sl_47_12_ok : sliceDirectCheck 0 18 0 face0_R_47 face0_G_47 face0_R_15 face0_G_15 = true := by decide +kernel
lemma face0_sl_47_12 : Slice face0_R_47 face0_G_47 (subcube 0 18) 4 := slice_direct face0_sl_47_12_ok face0_low_15
set_option maxRecDepth 200000 in
lemma face0_slices_47_ok : ∀ i (hi : i < face0_slices_47.size), Slice face0_R_47 face0_G_47 face0_slices_47[i].1 face0_slices_47[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice face0_R_47 face0_G_47 p.1 p.2) (forall_cons face0_sl_47_0 (forall_cons face0_sl_47_1 (forall_cons face0_sl_47_2 (forall_cons face0_sl_47_3 (forall_cons face0_sl_47_4 (forall_cons face0_sl_47_5 (forall_cons face0_sl_47_6 (forall_cons face0_sl_47_7 (forall_cons face0_sl_47_8 (forall_cons face0_sl_47_9 (forall_cons face0_sl_47_10 (forall_cons face0_sl_47_11 (forall_cons face0_sl_47_12 (fun _ h => (List.not_mem_nil h).elim))))))))))))))
lemma face0_P_47_ok : ∀ i (hi : i < face0_P_47.size), ∀ c, face0_P_47[i] = some c → ValidPool face0_R_47 face0_G_47 c := buildPools_sound face0_slices_47_ok
lemma face0_bk_47_init_ok : ∀ i (hi : i < face0_bk_0_init.size), ∀ xs ∈ face0_bk_0_init[i], Impossible face0_G_47 (0 - 1) xs.toFinset := by intro i hi; simp [face0_bk_0_init] at hi
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_chk_47_0 : checkNodes face0_W_47 face0_G_47 face0_fmask_47 face0_P_47 face0_autos_47 face0_bk_0_init 0 face0_nodes_0_0 = true := by decide +kernel
def face0_bk_47_0 : Array (List (List Nat)) := buildBuckets 1 face0_W_47 face0_nodes_0_0
lemma face0_bk_47_0_ok : ∀ i (hi : i < face0_bk_47_0.size), ∀ xs ∈ face0_bk_47_0[i], Impossible face0_G_47 0 xs.toFinset :=
  buildBuckets_sound (by decide) face0_gp_47 face0_W_47_ok face0_P_47_ok face0_autos_47_ok face0_bk_47_init_ok face0_chk_47_0
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_chk_47_1 : checkNodes face0_W_47 face0_G_47 face0_fmask_47 face0_P_47 face0_autos_47 face0_bk_47_0 1 face0_nodes_0_0 = true := by decide +kernel
lemma face0_bk_47_1_ok : ∀ i (hi : i < face0_bk_47_0.size), ∀ xs ∈ face0_bk_47_0[i], Impossible face0_G_47 1 xs.toFinset :=
  buildBuckets_sound (by decide) face0_gp_47 face0_W_47_ok face0_P_47_ok face0_autos_47_ok face0_bk_47_0_ok face0_chk_47_1
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_chk_47_2 : checkNodes face0_W_47 face0_G_47 face0_fmask_47 face0_P_47 face0_autos_47 face0_bk_47_0 2 face0_nodes_0_0 = true := by decide +kernel
lemma face0_bk_47_2_ok : ∀ i (hi : i < face0_bk_47_0.size), ∀ xs ∈ face0_bk_47_0[i], Impossible face0_G_47 2 xs.toFinset :=
  buildBuckets_sound (by decide) face0_gp_47 face0_W_47_ok face0_P_47_ok face0_autos_47_ok face0_bk_47_1_ok face0_chk_47_2
def face0_nodes_47_3 : List NodeSpec := [([29,8,16,20],[],[]),([29,12,25,1],[],[]),([9,32,10,21],[0],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_chk_47_3 : checkNodes face0_W_47 face0_G_47 face0_fmask_47 face0_P_47 face0_autos_47 face0_bk_47_0 3 face0_nodes_47_3 = true := by decide +kernel
def face0_bk_47_3 : Array (List (List Nat)) := buildBuckets 2 face0_W_47 face0_nodes_47_3
lemma face0_bk_47_3_ok : ∀ i (hi : i < face0_bk_47_3.size), ∀ xs ∈ face0_bk_47_3[i], Impossible face0_G_47 3 xs.toFinset :=
  buildBuckets_sound (by decide) face0_gp_47 face0_W_47_ok face0_P_47_ok face0_autos_47_ok face0_bk_47_2_ok face0_chk_47_3
def face0_nodes_47_4 : List NodeSpec := [([8,16,20,2,11],[1],[0]),([23,8,10,2,4],[],[]),([29,12,0,1,4],[],[0,1]),([12,25,1,2,11],[2],[0]),([12,25,20,2,3],[],[]),([26,34,2,3,4],[],[]),([26,1,2,3,28],[],[]),([9,16,20,2,11],[3],[2]),([23,9,10,2,4],[],[]),([17,25,20,2,3],[],[]),([35,1,2,3,4],[],[]),([9,32,10,2,4],[0],[0]),([9,16,10,21,4],[],[0,1]),([5,7,10,21,11],[],[]),([29,8,16,1,4],[],[3,4,0]),([14,25,20,2,3],[2],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_chk_47_4 : checkNodes face0_W_47 face0_G_47 face0_fmask_47 face0_P_47 face0_autos_47 face0_bk_47_3 4 face0_nodes_47_4 = true := by decide +kernel
def face0_bk_47_4 : Array (List (List Nat)) := buildBuckets 6 face0_W_47 face0_nodes_47_4
lemma face0_bk_47_4_ok : ∀ i (hi : i < face0_bk_47_4.size), ∀ xs ∈ face0_bk_47_4[i], Impossible face0_G_47 4 xs.toFinset :=
  buildBuckets_sound (by decide) face0_gp_47 face0_W_47_ok face0_P_47_ok face0_autos_47_ok face0_bk_47_3_ok face0_chk_47_4
def face0_nodes_47_5 : List NodeSpec := [([5,19,1,2,3,4],[4],[]),([14,0,1,2,3,4],[2],[5]),([5,7,10,6,4],[5,1,6,7],[6,7,8,9]),([8,16,1,2,11,4],[1],[4,8,0]),([8,16,20,2,3,4],[],[10,8,0]),([5,7,15,11,3,4],[5,1,6,7,0,8],[11,12,6,13,14,7,15,16,17]),([8,16,10,2,4],[5,1,9],[4,18,8]),([5,7,10,21,3,4],[],[19,20,15,21,9,0]),([12,0,1,2,11,4],[2],[0,1]),([22,0,1,2,3,4],[],[]),([23,8,1,2,3,4],[],[0]),([9,16,10,2,4],[10,0,7,1,9],[4,0,1]),([9,5,16,10,2,4],[0,6,7,1],[]),([24,5,0,1,2,3],[11],[]),([9,5,16,1,6,4],[0,7,6,1],[]),([17,25,1,2,3,4],[2,12],[0,22]),([17,5,16,1,2,4],[10,7],[]),([26,5,1,2,3,4],[4],[]),([12,25,1,2,3,4],[2],[0]),([27,0,1,2,3,4],[],[2]),([24,0,1,2,3,4],[],[]),([14,0,1,2,3,28],[],[0,1,2,23,5]),([9,16,1,2,11,4],[3],[19,1,0,2,22]),([26,9,1,2,3,4],[4],[24]),([14,25,1,2,3,4],[2],[0,22,24]),([9,16,20,2,3,4],[],[4,1,22,25,0]),([26,14,1,2,3,4],[4],[0,22,24]),([29,8,0,1,3,4],[],[2,26,3,0,4,27]),([30,0,1,2,3,4],[12],[]),([17,9,16,1,2,4],[10,7,1],[]),([24,14,0,1,2,3],[2],[]),([9,18,0,1,6,4],[0,6,13],[]),([24,9,0,1,2,3],[],[]),([23,9,1,2,3,4],[],[0,22]),([24,0,1,2,3],[],[]),([31,0,1,2,3,4],[],[0,1,2,23,5]),([9,32,1,2,3,4],[0],[0,4,22,28]),([33,0,1,2,3,4],[12],[23])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_chk_47_5 : checkNodes face0_W_47 face0_G_47 face0_fmask_47 face0_P_47 face0_autos_47 face0_bk_47_4 5 face0_nodes_47_5 = true := by decide +kernel
def face0_bk_47_5 : Array (List (List Nat)) := buildBuckets 13 face0_W_47 face0_nodes_47_5
lemma face0_bk_47_5_ok : ∀ i (hi : i < face0_bk_47_5.size), ∀ xs ∈ face0_bk_47_5[i], Impossible face0_G_47 5 xs.toFinset :=
  buildBuckets_sound (by decide) face0_gp_47 face0_W_47_ok face0_P_47_ok face0_autos_47_ok face0_bk_47_4_ok face0_chk_47_5
def face0_nodes_47_6 : List NodeSpec := [([5,7,10,2,3,4],[14,4,1,6,7,15,16],[6,20,14,7,16,29,8,0,30]),([8,0,1,2,11,3,4],[1,3,0,17],[0,4,18,8,1,27]),([12,0,1,2,3,4],[6,4,1,18,2,19],[0,1]),([13,5,0,1,2,3,4],[20],[0,1]),([9,5,0,1,6,3,4],[21,0,7,6,1,22,23],[0,1]),([14,9,0,1,2,3,4],[10,24,22],[0,1,2,23]),([9,0,1,2,11,3,4],[3,1,0,24],[0,23,5,4,1,27,2,31]),([5,7,15,3,4],[25,14,21,1,0,26,8,7],[12,6,14,7,16,17,0]),([9,16,1,2,3,4],[10,0,7,1,22,27,28],[0,4,22]),([17,9,0,1,2,3,4],[10,0,1,7,22],[23,0,1,2]),([14,5,0,1,2,3,4],[5,29,30],[0,1]),([17,5,0,1,2,3,4],[21,10,6,0,7,22,31],[23,0,1]),([8,16,1,2,3,4],[5,4,1,28,19],[4,18,0]),([17,0,1,2,3,4],[0,4,7,1,22,2,31,32,33,12],[23,0,1,2]),([5,7,1,2,11,3,4],[5,1,6,7,34],[11,24,19,13,20,32,0,8,30,33,9,34,35]),([14,0,1,2,3,4],[30,35,36,22,2],[0,1,2,23]),([9,5,16,1,2,3,4],[0,7,6,1],[0]),([9,18,0,1,2,3,4],[22,21,0,37],[23,2,0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_chk_47_6 : checkNodes face0_W_47 face0_G_47 face0_fmask_47 face0_P_47 face0_autos_47 face0_bk_47_5 6 face0_nodes_47_6 = true := by decide +kernel
def face0_bk_47_6 : Array (List (List Nat)) := buildBuckets 7 face0_W_47 face0_nodes_47_6
lemma face0_bk_47_6_ok : ∀ i (hi : i < face0_bk_47_6.size), ∀ xs ∈ face0_bk_47_6[i], Impossible face0_G_47 6 xs.toFinset :=
  buildBuckets_sound (by decide) face0_gp_47 face0_W_47_ok face0_P_47_ok face0_autos_47_ok face0_bk_47_5_ok face0_chk_47_6
def face0_nodes_47_7 : List NodeSpec := [([5,0,1,6,2,3,4],[0,38,5,1,39,40,3,41,42,29],[0,36,2,23,12,6,14,22,24,16,37,38,39,33,9,40]),([5,7,1,2,3,4],[43,21,0,4,1,15,34,7,39],[12,6,14,7,0,4,22,28]),([8,0,1,2,3,4],[14,0,4,1,39,10,2,17,19],[0,4,1,27]),([9,5,0,1,2,3,4],[21,0,7,1,6,29,22,24,44,45,39],[0,4,1,27]),([9,0,1,2,3,4],[0,7,1,10,22,2,24,44,45,39],[0,4,1,27,2,31])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_chk_47_7 : checkNodes face0_W_47 face0_G_47 face0_fmask_47 face0_P_47 face0_autos_47 face0_bk_47_6 7 face0_nodes_47_7 = true := by decide +kernel
def face0_bk_47_7 : Array (List (List Nat)) := buildBuckets 2 face0_W_47 face0_nodes_47_7
lemma face0_bk_47_7_ok : ∀ i (hi : i < face0_bk_47_7.size), ∀ xs ∈ face0_bk_47_7[i], Impossible face0_G_47 7 xs.toFinset :=
  buildBuckets_sound (by decide) face0_gp_47 face0_W_47_ok face0_P_47_ok face0_autos_47_ok face0_bk_47_6_ok face0_chk_47_7
def face0_nodes_47_8 : List NodeSpec := [([5,0,1,2,3,4],[14,4,21,1,39,10,40,2,46],[0,12,6,1,30,33,11])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_chk_47_8 : checkNodes face0_W_47 face0_G_47 face0_fmask_47 face0_P_47 face0_autos_47 face0_bk_47_7 8 face0_nodes_47_8 = true := by decide +kernel
def face0_bk_47_8 : Array (List (List Nat)) := buildBuckets 1 face0_W_47 face0_nodes_47_8
lemma face0_bk_47_8_ok : ∀ i (hi : i < face0_bk_47_8.size), ∀ xs ∈ face0_bk_47_8[i], Impossible face0_G_47 8 xs.toFinset :=
  buildBuckets_sound (by decide) face0_gp_47 face0_W_47_ok face0_P_47_ok face0_autos_47_ok face0_bk_47_7_ok face0_chk_47_8
def face0_nodes_47_9 : List NodeSpec := [([0,1,2,3,4],[4,14,21,10,2],[0,22,24,19,38,39,41,36,42,43])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_chk_47_9 : checkNodes face0_W_47 face0_G_47 face0_fmask_47 face0_P_47 face0_autos_47 face0_bk_47_8 9 face0_nodes_47_9 = true := by decide +kernel
def face0_bk_47_9 : Array (List (List Nat)) := buildBuckets 1 face0_W_47 face0_nodes_47_9
lemma face0_bk_47_9_ok : ∀ i (hi : i < face0_bk_47_9.size), ∀ xs ∈ face0_bk_47_9[i], Impossible face0_G_47 9 xs.toFinset :=
  buildBuckets_sound (by decide) face0_gp_47 face0_W_47_ok face0_P_47_ok face0_autos_47_ok face0_bk_47_8_ok face0_chk_47_9
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_forestRoot_47_ok : forestRootCheck face0_R_47 face0_G_47 [(VAR 1,30,28),(VAR 2,30,26),(VAR 3,30,22),(VAR 4,30,14),(VAR 5,46,14)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_forestRoot_47_in : bucketContains face0_bk_47_9 face0_R_47 = true := by decide +kernel
lemma face0_low_47 : Lower face0_R_47 face0_G_47 10 := lower_of_forest face0_forestRoot_47_ok face0_bk_47_9_ok face0_forestRoot_47_in
def face1_G_1 : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def face1_R_1 : List Nat := varsOf 7
lemma face1_low_1_ok : carryOK [(2,5),(1,4),(0,3)] face1_R_1 face1_G_1 face0_R_0 face0_G_0 = true := by decide +kernel
lemma face1_low_1 : Lower face1_R_1 face1_G_1 4 := carry_of face1_low_1_ok face0_low_0
def face1_G_3 : Nat := 0xeeeeeeee88888888eeeeeeee88888888
def face1_R_3 : List Nat := varsOf 35
lemma face1_low_3_ok : carryOK [(1,2),(0,2),(1,4),(0,3)] face1_R_3 face1_G_3 face0_R_0 face0_G_0 = true := by decide +kernel
lemma face1_low_3 : Lower face1_R_3 face1_G_3 4 := carry_of face1_low_3_ok face0_low_0
def face1_G_6 : Nat := 0xfafafafaa0a0a0a0fafafafaa0a0a0a0
def face1_R_6 : List Nat := varsOf 37
lemma face1_low_6_ok : carryOK [(2,4),(0,1),(0,3)] face1_R_6 face1_G_6 face0_R_0 face0_G_0 = true := by decide +kernel
lemma face1_low_6 : Lower face1_R_6 face1_G_6 4 := carry_of face1_low_6_ok face0_low_0
def face1_G_8 : Nat := 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0
def face1_R_8 : List Nat := varsOf 22
lemma face1_low_8_ok : carryOK [(2,5),(2,4),(1,3)] face1_R_8 face1_G_8 face0_R_0 face0_G_0 = true := by decide +kernel
lemma face1_low_8 : Lower face1_R_8 face1_G_8 4 := carry_of face1_low_8_ok face0_low_0
def face1_G_16 : Nat := 0xffffaaaaaaaa0000ffffaaaaaaaa0000
def face1_R_16 : List Nat := varsOf 49
lemma face1_low_16_ok : carryOK [(1,2),(0,1),(0,3)] face1_R_16 face1_G_16 face0_R_0 face0_G_0 = true := by decide +kernel
lemma face1_low_16 : Lower face1_R_16 face1_G_16 4 := carry_of face1_low_16_ok face0_low_0
def face1_G_19 : Nat := 0xe8e8e8e800000000e8e8e8e800000000
def face1_R_19 : List Nat := varsOf 39
lemma face1_low_19_ok : liftCheck 0 32 face1_R_19 face1_G_19 face1_R_1 face1_G_1 [(VAR 5,35,3)] = true := by decide +kernel
lemma face1_low_19 : Lower face1_R_19 face1_G_19 5 := lift_of face1_low_19_ok face1_low_1
def face1_G_20 : Nat := 0xfefefefee8e8e8e8fefefefee8e8e8e8
def face1_pos_20 : List Nat := [3,3,5,5,6,6,33,33,34,34,36,36,3,3,5,5,6,6,33,33,34,34,36,36]
def face1_neg_20 : List Nat := [2,1,4,1,4,2,32,1,32,2,32,4,4,32,2,32,1,32,2,4,1,4,1,2]
def face1_base_20 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcf0cf,0x51008a),(0xcccccccccccccccccccccccccccccccc,0x333333,0x844221),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xc3cc3c,0x281814),(0xffffffff00000000ffffffff00000000,0xfc0fc0,0x2a540)]
def face1_steps_20 : List (Nat × Nat × Nat) := [(1,0,1),(2,4,2),(1,4,2),(1,0,2),(2,6,3),(1,1,2)]
def face1_W_20 : Array Decor := buildWires face1_base_20 face1_steps_20
def face1_autos_20 : Array (List (Nat × Nat)) := #[[],[(2,5)],[(0,1)],[(2,5),(0,1)],[(1,2)],[(1,5),(1,2)],[(0,1),(0,2)],[(1,5),(0,1),(0,2)],[(1,5),(0,2)]]
def face1_slicesL_20 : List (Nat × Nat) := [(subcube 2 0,4),(subcube 1 0,4),(subcube 32 0,4),(subcube 4 0,4)]
def face1_slices_20 : Array (Nat × Nat) := face1_slicesL_20.toArray
def face1_P_20 : Array (Option BoundPool) := buildPools face1_W_20 face1_R_19 face1_slices_20 face0_ps_21
lemma face1_gp_20 : goodPairs face1_G_20 face1_pos_20 face1_neg_20 := goodPairs_of (by decide +kernel)
lemma face1_base_20_ok : ∀ x ∈ face1_base_20, faithful face1_pos_20 face1_neg_20 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma face1_W_20_ok : ∀ x ∈ face1_W_20.toList, faithful face1_pos_20 face1_neg_20 x ∧ x.1 < 2^128 := buildWires_faithful face1_base_20_ok
lemma face1_autos_20_ok : ∀ sw ∈ face1_autos_20.toList, swapsValid sw = true ∧ permWord sw face1_G_20 = face1_G_20 := autos_of (by decide +kernel)
lemma face1_sl_20_0_ok : sliceDirectCheck 2 0 0 face1_R_19 face1_G_20 face1_R_6 face1_G_6 = true := by decide +kernel
lemma face1_sl_20_0 : Slice face1_R_19 face1_G_20 (subcube 2 0) 4 := slice_direct face1_sl_20_0_ok face1_low_6
lemma face1_sl_20_1_ok : sliceDirectCheck 1 0 0 face1_R_19 face1_G_20 face0_R_9 face0_G_9 = true := by decide +kernel
lemma face1_sl_20_1 : Slice face1_R_19 face1_G_20 (subcube 1 0) 4 := slice_direct face1_sl_20_1_ok face0_low_9
lemma face1_sl_20_2_ok : sliceDirectCheck 32 0 0 face1_R_19 face1_G_20 face1_R_1 face1_G_1 = true := by decide +kernel
lemma face1_sl_20_2 : Slice face1_R_19 face1_G_20 (subcube 32 0) 4 := slice_direct face1_sl_20_2_ok face1_low_1
lemma face1_sl_20_3_ok : sliceDirectCheck 4 0 0 face1_R_19 face1_G_20 face1_R_3 face1_G_3 = true := by decide +kernel
lemma face1_sl_20_3 : Slice face1_R_19 face1_G_20 (subcube 4 0) 4 := slice_direct face1_sl_20_3_ok face1_low_3
set_option maxRecDepth 200000 in
lemma face1_slices_20_ok : ∀ i (hi : i < face1_slices_20.size), Slice face1_R_19 face1_G_20 face1_slices_20[i].1 face1_slices_20[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice face1_R_19 face1_G_20 p.1 p.2) (forall_cons face1_sl_20_0 (forall_cons face1_sl_20_1 (forall_cons face1_sl_20_2 (forall_cons face1_sl_20_3 (fun _ h => (List.not_mem_nil h).elim)))))
lemma face1_P_20_ok : ∀ i (hi : i < face1_P_20.size), ∀ c, face1_P_20[i] = some c → ValidPool face1_R_19 face1_G_20 c := buildPools_sound face1_slices_20_ok
lemma face1_bk_20_init_ok : ∀ i (hi : i < face0_bk_0_init.size), ∀ xs ∈ face0_bk_0_init[i], Impossible face1_G_20 (0 - 1) xs.toFinset := by intro i hi; simp [face0_bk_0_init] at hi
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face1_chk_20_0 : checkNodes face1_W_20 face1_G_20 face0_fmask_21 face1_P_20 face1_autos_20 face0_bk_0_init 0 face0_nodes_0_0 = true := by decide +kernel
def face1_bk_20_0 : Array (List (List Nat)) := buildBuckets 1 face1_W_20 face0_nodes_0_0
lemma face1_bk_20_0_ok : ∀ i (hi : i < face1_bk_20_0.size), ∀ xs ∈ face1_bk_20_0[i], Impossible face1_G_20 0 xs.toFinset :=
  buildBuckets_sound (by decide) face1_gp_20 face1_W_20_ok face1_P_20_ok face1_autos_20_ok face1_bk_20_init_ok face1_chk_20_0
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face1_chk_20_1 : checkNodes face1_W_20 face1_G_20 face0_fmask_21 face1_P_20 face1_autos_20 face1_bk_20_0 1 face0_nodes_0_0 = true := by decide +kernel
lemma face1_bk_20_1_ok : ∀ i (hi : i < face1_bk_20_0.size), ∀ xs ∈ face1_bk_20_0[i], Impossible face1_G_20 1 xs.toFinset :=
  buildBuckets_sound (by decide) face1_gp_20 face1_W_20_ok face1_P_20_ok face1_autos_20_ok face1_bk_20_0_ok face1_chk_20_1
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face1_chk_20_2 : checkNodes face1_W_20 face1_G_20 face0_fmask_21 face1_P_20 face1_autos_20 face1_bk_20_0 2 face0_nodes_0_0 = true := by decide +kernel
lemma face1_bk_20_2_ok : ∀ i (hi : i < face1_bk_20_0.size), ∀ xs ∈ face1_bk_20_0[i], Impossible face1_G_20 2 xs.toFinset :=
  buildBuckets_sound (by decide) face1_gp_20 face1_W_20_ok face1_P_20_ok face1_autos_20_ok face1_bk_20_1_ok face1_chk_20_2
def face1_nodes_20_3 : List NodeSpec := [([8,0,1,2],[],[]),([4,7,9,3],[0,1],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face1_chk_20_3 : checkNodes face1_W_20 face1_G_20 face0_fmask_21 face1_P_20 face1_autos_20 face1_bk_20_0 3 face1_nodes_20_3 = true := by decide +kernel
def face1_bk_20_3 : Array (List (List Nat)) := buildBuckets 1 face1_W_20 face1_nodes_20_3
lemma face1_bk_20_3_ok : ∀ i (hi : i < face1_bk_20_3.size), ∀ xs ∈ face1_bk_20_3[i], Impossible face1_G_20 3 xs.toFinset :=
  buildBuckets_sound (by decide) face1_gp_20 face1_W_20_ok face1_P_20_ok face1_autos_20_ok face1_bk_20_2_ok face1_chk_20_3
def face1_nodes_20_4 : List NodeSpec := [([5,0,1,2,3],[],[]),([0,1,2,6,3],[2],[0]),([1,4,2,7,3],[0,3],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face1_chk_20_4 : checkNodes face1_W_20 face1_G_20 face0_fmask_21 face1_P_20 face1_autos_20 face1_bk_20_3 4 face1_nodes_20_4 = true := by decide +kernel
def face1_bk_20_4 : Array (List (List Nat)) := buildBuckets 2 face1_W_20 face1_nodes_20_4
lemma face1_bk_20_4_ok : ∀ i (hi : i < face1_bk_20_4.size), ∀ xs ∈ face1_bk_20_4[i], Impossible face1_G_20 4 xs.toFinset :=
  buildBuckets_sound (by decide) face1_gp_20 face1_W_20_ok face1_P_20_ok face1_autos_20_ok face1_bk_20_3_ok face1_chk_20_4
def face1_nodes_20_5 : List NodeSpec := [([0,1,4,2,3],[0,1,3,2],[0,1,2,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face1_chk_20_5 : checkNodes face1_W_20 face1_G_20 face0_fmask_21 face1_P_20 face1_autos_20 face1_bk_20_4 5 face1_nodes_20_5 = true := by decide +kernel
def face1_bk_20_5 : Array (List (List Nat)) := buildBuckets 1 face1_W_20 face1_nodes_20_5
lemma face1_bk_20_5_ok : ∀ i (hi : i < face1_bk_20_5.size), ∀ xs ∈ face1_bk_20_5[i], Impossible face1_G_20 5 xs.toFinset :=
  buildBuckets_sound (by decide) face1_gp_20 face1_W_20_ok face1_P_20_ok face1_autos_20_ok face1_bk_20_4_ok face1_chk_20_5
def face1_nodes_20_6 : List NodeSpec := [([0,1,2,3],[0,1,3,2],[0,4,5,6,7,8])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face1_chk_20_6 : checkNodes face1_W_20 face1_G_20 face0_fmask_21 face1_P_20 face1_autos_20 face1_bk_20_5 6 face1_nodes_20_6 = true := by decide +kernel
def face1_bk_20_6 : Array (List (List Nat)) := buildBuckets 1 face1_W_20 face1_nodes_20_6
lemma face1_bk_20_6_ok : ∀ i (hi : i < face1_bk_20_6.size), ∀ xs ∈ face1_bk_20_6[i], Impossible face1_G_20 6 xs.toFinset :=
  buildBuckets_sound (by decide) face1_gp_20 face1_W_20_ok face1_P_20_ok face1_autos_20_ok face1_bk_20_5_ok face1_chk_20_6
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face1_forestRoot_20_ok : forestRootCheck face1_R_19 face1_G_20 [(VAR 0,3,2),(VAR 1,3,1),(VAR 2,5,1),(VAR 5,33,1)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face1_forestRoot_20_in : bucketContains face1_bk_20_6 face1_R_19 = true := by decide +kernel
lemma face1_low_20 : Lower face1_R_19 face1_G_20 7 := lower_of_forest face1_forestRoot_20_ok face1_bk_20_6_ok face1_forestRoot_20_in
def face1_G_22 : Nat := 0xfffffcfcfcfc0000fffffcfcfcfc0000
lemma face1_low_22_ok : liftCheck 2 0 face0_R_33 face1_G_22 face0_R_18 face0_G_18 [(VAR 1,18,16)] = true := by decide +kernel
lemma face1_low_22 : Lower face0_R_33 face1_G_22 5 := lift_of face1_low_22_ok face0_low_18
def face1_G_24 : Nat := 0xe8e80000e8e80000e8e80000e8e80000
def face1_R_24 : List Nat := varsOf 23
lemma face1_low_24_ok : carryOK [(4,5)] face1_R_24 face1_G_24 face1_R_19 face1_G_19 = true := by decide +kernel
lemma face1_low_24 : Lower face1_R_24 face1_G_24 5 := carry_of face1_low_24_ok face1_low_19
def face1_G_27 : Nat := 0xeeee888888880000eeee888888880000
def face1_R_27 : List Nat := varsOf 51
lemma face1_low_27_ok : carryOK [(1,3),(0,2)] face1_R_27 face1_G_27 face0_R_21 face0_G_21 = true := by decide +kernel
lemma face1_low_27 : Lower face1_R_27 face1_G_27 7 := carry_of face1_low_27_ok face0_low_21
def face1_G_30 : Nat := 0xfafaa0a0a0a00000fafaa0a0a0a00000
def face1_R_30 : List Nat := varsOf 53
lemma face1_low_30_ok : carryOK [(1,3),(0,1),(0,2)] face1_R_30 face1_G_30 face0_R_21 face0_G_21 = true := by decide +kernel
lemma face1_low_30 : Lower face1_R_30 face1_G_30 7 := carry_of face1_low_30_ok face0_low_21
def face1_G_35 : Nat := 0xfefee8e8fefee8e8fefee8e8fefee8e8
lemma face1_low_35_ok : carryOK [(4,5)] face1_R_24 face1_G_35 face1_R_19 face1_G_20 = true := by decide +kernel
lemma face1_low_35 : Lower face1_R_24 face1_G_35 7 := carry_of face1_low_35_ok face1_low_20
def face1_G_44 : Nat := 0xffffeeeeeeee0000ffffeeeeeeee0000
lemma face1_low_44_ok : carryOK [(0,2),(0,1)] face1_R_27 face1_G_44 face0_R_33 face1_G_22 = true := by decide +kernel
lemma face1_low_44 : Lower face1_R_27 face1_G_44 5 := carry_of face1_low_44_ok face1_low_22
def face1_G_45 : Nat := 0xfffffafafafa0000fffffafafafa0000
lemma face1_low_45_ok : carryOK [(0,1)] face1_R_30 face1_G_45 face0_R_33 face1_G_22 = true := by decide +kernel
lemma face1_low_45 : Lower face1_R_30 face1_G_45 5 := carry_of face1_low_45_ok face1_low_22
def face1_G_48 : Nat := 0xfefee8e8e8e80000fefee8e8e8e80000
def face1_R_48 : List Nat := varsOf 55
def face1_pos_48 : List Nat := [19,19,19,21,21,21,22,22,22,23,35,35,35,37,37,37,38,38,38,39,49,49,49,50,50,50,52,52,52,19,19,19,19,19,19,21,21,21,21,21,21,22,22,22,22,22,22,35,35,35,35,35,35,37,37,37,37,37,37,38,38,38,38,38,38,49,49,49,49,49,50,50,50,50,50,52,52,52,52,52]
def face1_neg_48 : List Nat := [18,17,3,20,17,5,20,18,6,7,34,33,3,36,33,5,36,34,6,7,48,33,17,48,34,18,48,36,20,7,20,33,34,36,48,7,18,33,34,36,48,7,17,33,34,36,48,7,17,18,20,36,48,7,17,18,20,34,48,7,17,18,20,33,48,7,18,20,34,36,7,17,20,33,36,7,17,18,33,34]
def face1_fmask_48 : Nat := fullMask 80
def face1_base_48 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x3e07ff81ffe078fe3f,0x5ac298618e28a068da36),(0xcccccccccccccccccccccccccccccccc,0x7c1f81ffe07e38f1fc7,0xa8562aa29259230e1785),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf801ffe07ff81c0fe3f8,0xd6a492ca28a780da368),(0xffff0000ffff0000ffff0000ffff0000,0xfffe00007ffffff003ff,0x318d75d7451456d000db),(0xffffffff00000000ffffffff00000000,0xffffffff80001ffffc00,0xc631861879e78db36c00)]
def face1_steps_48 : List (Nat × Nat × Nat) := [(0,3,4),(3,0,3),(1,0,1),(1,0,5),(3,1,4),(3,0,4),(3,6,4),(1,6,1),(0,6,4),(3,7,3),(0,7,3),(3,2,3),(1,0,2),(2,7,2),(1,7,2),(3,1,8),(1,1,5),(2,7,5),(1,7,5),(0,19,3),(0,7,4),(0,15,4),(3,16,4),(3,15,4),(1,1,2),(3,2,23),(2,19,5)]
def face1_W_48 : Array Decor := buildWires face1_base_48 face1_steps_48
def face1_autos_48 : Array (List (Nat × Nat)) := #[[],[(1,2)],[(0,1),(0,2)],[(0,1)],[(4,5)],[(0,2),(0,1)],[(4,5),(0,1)],[(4,5),(0,2),(0,1)]]
def face1_slicesL_48 : List (Nat × Nat) := [(subcube 32 0,5),(subcube 0 16,7),(subcube 1 32,4),(subcube 2 0,7),(subcube 0 1,5),(subcube 0 2,5),(subcube 0 32,7),(subcube 4 0,7),(subcube 4 16,4),(subcube 4 2,4),(subcube 4 1,4),(subcube 2 1,4),(subcube 2 16,4),(subcube 1 0,7),(subcube 0 4,5),(subcube 16 0,5),(subcube 1 4,4),(subcube 16 32,4),(subcube 1 16,4),(subcube 32 16,4),(subcube 2 4,4)]
def face1_slices_48 : Array (Nat × Nat) := face1_slicesL_48.toArray
def face1_ps_48 : List PoolSpec := [(0,[]),(1,[(1,0,1),(1,0,5),(1,1,5)]),(2,[]),(1,[(1,0,1),(1,7,5),(3,2,23)]),(3,[(0,7,3),(0,7,4),(0,3,4)]),(4,[]),(5,[]),(1,[]),(6,[]),(1,[(1,0,1),(1,7,2),(2,19,5)]),(7,[]),(8,[]),(9,[]),(10,[]),(1,[(1,0,1),(1,0,2),(1,1,2)]),(11,[]),(1,[(1,0,5),(3,1,8)]),(12,[]),(1,[(1,0,5),(1,1,5)]),(13,[]),(3,[]),(14,[]),(13,[(0,3,4),(2,7,5)]),(3,[(0,3,4),(2,7,5)]),(1,[(1,0,1),(1,7,5)]),(15,[]),(1,[(1,0,1),(1,0,5)]),(3,[(0,7,3),(0,7,4)]),(3,[(0,7,3),(0,15,4)]),(16,[]),(17,[]),(1,[(1,0,1),(2,7,2)]),(1,[(1,0,1),(1,7,2)]),(3,[(0,7,3),(0,3,4)]),(1,[(1,0,1),(1,0,2)]),(1,[(1,0,1),(2,7,5)]),(3,[(0,7,3),(3,15,4)]),(6,[(1,0,1),(1,0,2),(1,1,2)]),(13,[(0,3,4)]),(1,[(1,0,5)]),(18,[]),(19,[]),(20,[]),(3,[(0,3,4)]),(1,[(1,0,1)]),(6,[(1,0,1)]),(3,[(0,7,3)]),(6,[(1,0,1),(1,0,2)]),(6,[(1,0,1),(2,7,2)]),(6,[(1,0,1),(1,7,2)]),(7,[(0,3,4)])]
def face1_P_48 : Array (Option BoundPool) := buildPools face1_W_48 face1_R_48 face1_slices_48 face1_ps_48
lemma face1_gp_48 : goodPairs face1_G_48 face1_pos_48 face1_neg_48 := goodPairs_of (by decide +kernel)
lemma face1_base_48_ok : ∀ x ∈ face1_base_48, faithful face1_pos_48 face1_neg_48 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma face1_W_48_ok : ∀ x ∈ face1_W_48.toList, faithful face1_pos_48 face1_neg_48 x ∧ x.1 < 2^128 := buildWires_faithful face1_base_48_ok
lemma face1_autos_48_ok : ∀ sw ∈ face1_autos_48.toList, swapsValid sw = true ∧ permWord sw face1_G_48 = face1_G_48 := autos_of (by decide +kernel)
lemma face1_sl_48_0_ok : sliceDirectCheck 32 0 0 face1_R_48 face1_G_48 face1_R_24 face1_G_24 = true := by decide +kernel
lemma face1_sl_48_0 : Slice face1_R_48 face1_G_48 (subcube 32 0) 5 := slice_direct face1_sl_48_0_ok face1_low_24
lemma face1_sl_48_1_ok : sliceDirectCheck 0 16 0 face1_R_48 face1_G_48 face1_R_19 face1_G_20 = true := by decide +kernel
lemma face1_sl_48_1 : Slice face1_R_48 face1_G_48 (subcube 0 16) 7 := slice_direct face1_sl_48_1_ok face1_low_20
lemma face1_sl_48_2_ok : sliceDirectCheck 1 32 0 face1_R_48 face1_G_48 face1_R_8 face1_G_8 = true := by decide +kernel
lemma face1_sl_48_2 : Slice face1_R_48 face1_G_48 (subcube 1 32) 4 := slice_direct face1_sl_48_2_ok face1_low_8
lemma face1_sl_48_3_ok : sliceDirectCheck 2 0 0 face1_R_48 face1_G_48 face1_R_30 face1_G_30 = true := by decide +kernel
lemma face1_sl_48_3 : Slice face1_R_48 face1_G_48 (subcube 2 0) 7 := slice_direct face1_sl_48_3_ok face1_low_30
lemma face1_sl_48_4_ok : sliceDirectCheck 0 1 0 face1_R_48 face1_G_48 face0_R_33 face1_G_22 = true := by decide +kernel
lemma face1_sl_48_4 : Slice face1_R_48 face1_G_48 (subcube 0 1) 5 := slice_direct face1_sl_48_4_ok face1_low_22
lemma face1_sl_48_5_ok : sliceDirectCheck 0 2 0 face1_R_48 face1_G_48 face1_R_30 face1_G_45 = true := by decide +kernel
lemma face1_sl_48_5 : Slice face1_R_48 face1_G_48 (subcube 0 2) 5 := slice_direct face1_sl_48_5_ok face1_low_45
lemma face1_sl_48_6_ok : sliceDirectCheck 0 32 0 face1_R_48 face1_G_48 face1_R_24 face1_G_35 = true := by decide +kernel
lemma face1_sl_48_6 : Slice face1_R_48 face1_G_48 (subcube 0 32) 7 := slice_direct face1_sl_48_6_ok face1_low_35
lemma face1_sl_48_7_ok : sliceDirectCheck 4 0 0 face1_R_48 face1_G_48 face1_R_27 face1_G_27 = true := by decide +kernel
lemma face1_sl_48_7 : Slice face1_R_48 face1_G_48 (subcube 4 0) 7 := slice_direct face1_sl_48_7_ok face1_low_27
lemma face1_sl_48_8_ok : sliceDirectCheck 4 16 0 face1_R_48 face1_G_48 face1_R_3 face1_G_3 = true := by decide +kernel
lemma face1_sl_48_8 : Slice face1_R_48 face1_G_48 (subcube 4 16) 4 := slice_direct face1_sl_48_8_ok face1_low_3
lemma face1_sl_48_9_ok : sliceDirectCheck 4 2 0 face1_R_48 face1_G_48 face1_R_16 face1_G_16 = true := by decide +kernel
lemma face1_sl_48_9 : Slice face1_R_48 face1_G_48 (subcube 4 2) 4 := slice_direct face1_sl_48_9_ok face1_low_16
lemma face1_sl_48_10_ok : sliceDirectCheck 4 1 0 face1_R_48 face1_G_48 face0_R_17 face0_G_17 = true := by decide +kernel
lemma face1_sl_48_10 : Slice face1_R_48 face1_G_48 (subcube 4 1) 4 := slice_direct face1_sl_48_10_ok face0_low_17
lemma face1_sl_48_11_ok : sliceDirectCheck 2 1 0 face1_R_48 face1_G_48 face0_R_18 face0_G_18 = true := by decide +kernel
lemma face1_sl_48_11 : Slice face1_R_48 face1_G_48 (subcube 2 1) 4 := slice_direct face1_sl_48_11_ok face0_low_18
lemma face1_sl_48_12_ok : sliceDirectCheck 2 16 0 face1_R_48 face1_G_48 face1_R_6 face1_G_6 = true := by decide +kernel
lemma face1_sl_48_12 : Slice face1_R_48 face1_G_48 (subcube 2 16) 4 := slice_direct face1_sl_48_12_ok face1_low_6
lemma face1_sl_48_13_ok : sliceDirectCheck 1 0 0 face1_R_48 face1_G_48 face0_R_33 face0_G_33 = true := by decide +kernel
lemma face1_sl_48_13 : Slice face1_R_48 face1_G_48 (subcube 1 0) 7 := slice_direct face1_sl_48_13_ok face0_low_33
lemma face1_sl_48_14_ok : sliceDirectCheck 0 4 0 face1_R_48 face1_G_48 face1_R_27 face1_G_44 = true := by decide +kernel
lemma face1_sl_48_14 : Slice face1_R_48 face1_G_48 (subcube 0 4) 5 := slice_direct face1_sl_48_14_ok face1_low_44
lemma face1_sl_48_15_ok : sliceDirectCheck 16 0 0 face1_R_48 face1_G_48 face1_R_19 face1_G_19 = true := by decide +kernel
lemma face1_sl_48_15 : Slice face1_R_48 face1_G_48 (subcube 16 0) 5 := slice_direct face1_sl_48_15_ok face1_low_19
lemma face1_sl_48_16_ok : sliceDirectCheck 1 4 0 face1_R_48 face1_G_48 face0_R_17 face0_G_17 = true := by decide +kernel
lemma face1_sl_48_16 : Slice face1_R_48 face1_G_48 (subcube 1 4) 4 := slice_direct face1_sl_48_16_ok face0_low_17
lemma face1_sl_48_17_ok : sliceDirectCheck 16 32 0 face1_R_48 face1_G_48 face1_R_1 face1_G_1 = true := by decide +kernel
lemma face1_sl_48_17 : Slice face1_R_48 face1_G_48 (subcube 16 32) 4 := slice_direct face1_sl_48_17_ok face1_low_1
lemma face1_sl_48_18_ok : sliceDirectCheck 1 16 0 face1_R_48 face1_G_48 face0_R_9 face0_G_9 = true := by decide +kernel
lemma face1_sl_48_18 : Slice face1_R_48 face1_G_48 (subcube 1 16) 4 := slice_direct face1_sl_48_18_ok face0_low_9
lemma face1_sl_48_19_ok : sliceDirectCheck 32 16 0 face1_R_48 face1_G_48 face1_R_1 face1_G_1 = true := by decide +kernel
lemma face1_sl_48_19 : Slice face1_R_48 face1_G_48 (subcube 32 16) 4 := slice_direct face1_sl_48_19_ok face1_low_1
lemma face1_sl_48_20_ok : sliceDirectCheck 2 4 0 face1_R_48 face1_G_48 face1_R_16 face1_G_16 = true := by decide +kernel
lemma face1_sl_48_20 : Slice face1_R_48 face1_G_48 (subcube 2 4) 4 := slice_direct face1_sl_48_20_ok face1_low_16
set_option maxRecDepth 200000 in
lemma face1_slices_48_ok : ∀ i (hi : i < face1_slices_48.size), Slice face1_R_48 face1_G_48 face1_slices_48[i].1 face1_slices_48[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice face1_R_48 face1_G_48 p.1 p.2) (forall_cons face1_sl_48_0 (forall_cons face1_sl_48_1 (forall_cons face1_sl_48_2 (forall_cons face1_sl_48_3 (forall_cons face1_sl_48_4 (forall_cons face1_sl_48_5 (forall_cons face1_sl_48_6 (forall_cons face1_sl_48_7 (forall_cons face1_sl_48_8 (forall_cons face1_sl_48_9 (forall_cons face1_sl_48_10 (forall_cons face1_sl_48_11 (forall_cons face1_sl_48_12 (forall_cons face1_sl_48_13 (forall_cons face1_sl_48_14 (forall_cons face1_sl_48_15 (forall_cons face1_sl_48_16 (forall_cons face1_sl_48_17 (forall_cons face1_sl_48_18 (forall_cons face1_sl_48_19 (forall_cons face1_sl_48_20 (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))))))
lemma face1_P_48_ok : ∀ i (hi : i < face1_P_48.size), ∀ c, face1_P_48[i] = some c → ValidPool face1_R_48 face1_G_48 c := buildPools_sound face1_slices_48_ok
lemma face1_bk_48_init_ok : ∀ i (hi : i < face0_bk_0_init.size), ∀ xs ∈ face0_bk_0_init[i], Impossible face1_G_48 (0 - 1) xs.toFinset := by intro i hi; simp [face0_bk_0_init] at hi
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face1_chk_48_0 : checkNodes face1_W_48 face1_G_48 face1_fmask_48 face1_P_48 face1_autos_48 face0_bk_0_init 0 face0_nodes_0_0 = true := by decide +kernel
def face1_bk_48_0 : Array (List (List Nat)) := buildBuckets 1 face1_W_48 face0_nodes_0_0
lemma face1_bk_48_0_ok : ∀ i (hi : i < face1_bk_48_0.size), ∀ xs ∈ face1_bk_48_0[i], Impossible face1_G_48 0 xs.toFinset :=
  buildBuckets_sound (by decide) face1_gp_48 face1_W_48_ok face1_P_48_ok face1_autos_48_ok face1_bk_48_init_ok face1_chk_48_0
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face1_chk_48_1 : checkNodes face1_W_48 face1_G_48 face1_fmask_48 face1_P_48 face1_autos_48 face1_bk_48_0 1 face0_nodes_0_0 = true := by decide +kernel
lemma face1_bk_48_1_ok : ∀ i (hi : i < face1_bk_48_0.size), ∀ xs ∈ face1_bk_48_0[i], Impossible face1_G_48 1 xs.toFinset :=
  buildBuckets_sound (by decide) face1_gp_48 face1_W_48_ok face1_P_48_ok face1_autos_48_ok face1_bk_48_0_ok face1_chk_48_1
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face1_chk_48_2 : checkNodes face1_W_48 face1_G_48 face1_fmask_48 face1_P_48 face1_autos_48 face1_bk_48_0 2 face0_nodes_0_0 = true := by decide +kernel
lemma face1_bk_48_2_ok : ∀ i (hi : i < face1_bk_48_0.size), ∀ xs ∈ face1_bk_48_0[i], Impossible face1_G_48 2 xs.toFinset :=
  buildBuckets_sound (by decide) face1_gp_48 face1_W_48_ok face1_P_48_ok face1_autos_48_ok face1_bk_48_1_ok face1_chk_48_2
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face1_chk_48_3 : checkNodes face1_W_48 face1_G_48 face1_fmask_48 face1_P_48 face1_autos_48 face1_bk_48_0 3 face0_nodes_0_0 = true := by decide +kernel
lemma face1_bk_48_3_ok : ∀ i (hi : i < face1_bk_48_0.size), ∀ xs ∈ face1_bk_48_0[i], Impossible face1_G_48 3 xs.toFinset :=
  buildBuckets_sound (by decide) face1_gp_48 face1_W_48_ok face1_P_48_ok face1_autos_48_ok face1_bk_48_2_ok face1_chk_48_3
def face1_nodes_48_4 : List NodeSpec := [([22,17,29,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face1_chk_48_4 : checkNodes face1_W_48 face1_G_48 face1_fmask_48 face1_P_48 face1_autos_48 face1_bk_48_0 4 face1_nodes_48_4 = true := by decide +kernel
def face1_bk_48_4 : Array (List (List Nat)) := buildBuckets 1 face1_W_48 face1_nodes_48_4
lemma face1_bk_48_4_ok : ∀ i (hi : i < face1_bk_48_4.size), ∀ xs ∈ face1_bk_48_4[i], Impossible face1_G_48 4 xs.toFinset :=
  buildBuckets_sound (by decide) face1_gp_48 face1_W_48_ok face1_P_48_ok face1_autos_48_ok face1_bk_48_3_ok face1_chk_48_4
def face1_nodes_48_5 : List NodeSpec := [([7,2,3,8,21,4],[0,1,2],[]),([30,0,1,5,3,4],[3],[]),([0,1,15,25,2,5],[4,5,6,2],[]),([22,0,1,2,3,4],[],[]),([31,0,1,2,3,4],[7,8,9],[]),([22,1,2,17,3,4],[10],[0]),([7,17,29,5,3,4],[11,12,2,13,14],[0,1,2])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face1_chk_48_5 : checkNodes face1_W_48 face1_G_48 face1_fmask_48 face1_P_48 face1_autos_48 face1_bk_48_4 5 face1_nodes_48_5 = true := by decide +kernel
def face1_bk_48_5 : Array (List (List Nat)) := buildBuckets 3 face1_W_48 face1_nodes_48_5
lemma face1_bk_48_5_ok : ∀ i (hi : i < face1_bk_48_5.size), ∀ xs ∈ face1_bk_48_5[i], Impossible face1_G_48 5 xs.toFinset :=
  buildBuckets_sound (by decide) face1_gp_48 face1_W_48_ok face1_P_48_ok face1_autos_48_ok face1_bk_48_4_ok face1_chk_48_5
def face1_nodes_48_6 : List NodeSpec := [([20,0,1,2,5,3,4],[0,2,6,15,16],[]),([0,1,2,3,8,21,4],[2,5,17,6,18],[0]),([22,0,1,2,3,4],[19,20,10,21,8,7,22,23],[0,3]),([0,1,2,5,3,23,4],[11,8,24],[0]),([0,1,2,24,4],[5,21,6,25],[]),([1,7,2,5,3,8,4],[15,17,0,25,19,26],[0]),([0,1,15,25,2,3,4],[27,0,2,17,25],[0]),([0,1,26,7,2,3,4],[28,19,29,12],[0]),([0,1,7,2,27,3,4],[29,11,5,30,0],[]),([18,0,1,2,5,3,4],[21,12,5,29,15,31],[]),([0,1,2,19,5,3,4],[5,29,6,15,12,0,25,7,8,32],[0]),([22,0,1,7,2,3,4],[19,20,0,23],[]),([0,1,15,7,2,5,4],[33,5,6,7,2,30],[0]),([1,7,2,17,5,3,4],[17,12,15,11,29,34],[0,1]),([22,0,1,2,5,3,4],[5,8,7,35],[]),([28,0,1,7,2,3,4],[7,8,5,17,36,0,30],[]),([7,17,29,3,4],[20,10,12,19,13,14,37],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face1_chk_48_6 : checkNodes face1_W_48 face1_G_48 face1_fmask_48 face1_P_48 face1_autos_48 face1_bk_48_5 6 face1_nodes_48_6 = true := by decide +kernel
def face1_bk_48_6 : Array (List (List Nat)) := buildBuckets 6 face1_W_48 face1_nodes_48_6
lemma face1_bk_48_6_ok : ∀ i (hi : i < face1_bk_48_6.size), ∀ xs ∈ face1_bk_48_6[i], Impossible face1_G_48 6 xs.toFinset :=
  buildBuckets_sound (by decide) face1_gp_48 face1_W_48_ok face1_P_48_ok face1_autos_48_ok face1_bk_48_5_ok face1_chk_48_6
def face1_nodes_48_7 : List NodeSpec := [([0,1,2,5,3,8,4],[38,5,0,25,15,17,13,11,39],[0,1]),([0,1,2,3,8,4],[5,15,13,25,0,7,2],[]),([9,6,0,1,2,3,4],[5,0,40,41,2,29,11,20,6,12,42,30],[]),([6,10,1,2,3,4],[5,7,19,8,13,30],[]),([0,11,1,2,3,4],[8,0,7,2,5,6,20,21,10,19,13,15,30],[2]),([0,1,12,2,3,4],[6,5,20,12,25,17,40,0,8],[]),([0,1,7,2,5,3,4],[43,2,38,5,6,11,0,25,7,44,8,45,12,29],[0,3,4]),([13,0,1,2,3,4],[5,6,20,21,10,25,0,13],[]),([14,0,1,2,3,4],[5,6,21,10,25,8,0,12],[]),([0,1,15,7,2,3,4],[46,5,12,7,17,2,30,44],[0]),([0,1,15,2,3,4],[17,5,6,7,25,12,40,21,8,0,30],[]),([16,0,1,7,2,3,4],[19,5,20,6,21,12,11,17,29,2,25,41,30],[0]),([1,7,2,17,3,4],[19,12,20,5,10,34,47],[0]),([18,0,1,2,3,4],[10,21,20,19,7,25,8,0,12,13,31,48],[0]),([0,1,2,19,3,4],[5,21,6,25,7,0,8,32,49],[0,4])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face1_chk_48_7 : checkNodes face1_W_48 face1_G_48 face1_fmask_48 face1_P_48 face1_autos_48 face1_bk_48_6 7 face1_nodes_48_7 = true := by decide +kernel
def face1_bk_48_7 : Array (List (List Nat)) := buildBuckets 6 face1_W_48 face1_nodes_48_7
lemma face1_bk_48_7_ok : ∀ i (hi : i < face1_bk_48_7.size), ∀ xs ∈ face1_bk_48_7[i], Impossible face1_G_48 7 xs.toFinset :=
  buildBuckets_sound (by decide) face1_gp_48 face1_W_48_ok face1_P_48_ok face1_autos_48_ok face1_bk_48_6_ok face1_chk_48_7
def face1_nodes_48_8 : List NodeSpec := [([0,1,2,5,3,4],[43,38,50,0,7,8],[0,1,2,5]),([6,0,1,2,3,4],[7,20,5,40,10,19,8,13,15,30],[0,1,2]),([0,1,7,2,3,4],[20,19,10,12,7,44,8,45],[0,3,4])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face1_chk_48_8 : checkNodes face1_W_48 face1_G_48 face1_fmask_48 face1_P_48 face1_autos_48 face1_bk_48_7 8 face1_nodes_48_8 = true := by decide +kernel
def face1_bk_48_8 : Array (List (List Nat)) := buildBuckets 2 face1_W_48 face1_nodes_48_8
lemma face1_bk_48_8_ok : ∀ i (hi : i < face1_bk_48_8.size), ∀ xs ∈ face1_bk_48_8[i], Impossible face1_G_48 8 xs.toFinset :=
  buildBuckets_sound (by decide) face1_gp_48 face1_W_48_ok face1_P_48_ok face1_autos_48_ok face1_bk_48_7_ok face1_chk_48_8
def face1_nodes_48_9 : List NodeSpec := [([0,1,2,3,4],[20,19,10,7,8],[0,1,4,2,6,5,7])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face1_chk_48_9 : checkNodes face1_W_48 face1_G_48 face1_fmask_48 face1_P_48 face1_autos_48 face1_bk_48_8 9 face1_nodes_48_9 = true := by decide +kernel
def face1_bk_48_9 : Array (List (List Nat)) := buildBuckets 1 face1_W_48 face1_nodes_48_9
lemma face1_bk_48_9_ok : ∀ i (hi : i < face1_bk_48_9.size), ∀ xs ∈ face1_bk_48_9[i], Impossible face1_G_48 9 xs.toFinset :=
  buildBuckets_sound (by decide) face1_gp_48 face1_W_48_ok face1_P_48_ok face1_autos_48_ok face1_bk_48_8_ok face1_chk_48_9
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face1_forestRoot_48_ok : forestRootCheck face1_R_48 face1_G_48 [(VAR 0,19,18),(VAR 1,19,17),(VAR 2,21,17),(VAR 4,19,3),(VAR 5,35,3)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face1_forestRoot_48_in : bucketContains face1_bk_48_9 face1_R_48 = true := by decide +kernel
lemma face1_low_48 : Lower face1_R_48 face1_G_48 10 := lower_of_forest face1_forestRoot_48_ok face1_bk_48_9_ok face1_forestRoot_48_in
def face2_pos_0 : List Nat := [20,20,36,36,48,48,20,36,48]
def face2_neg_0 : List Nat := [16,4,32,4,32,16,32,16,4]
def face2_base_0 : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xcf,0x10a),(0xffff0000ffff0000ffff0000ffff0000,0x173,0xa1),(0xffffffff00000000ffffffff00000000,0x1bc,0x54)]
def face2_W_0 : BT Decor := buildWiresBT 2 face2_base_0 face0_steps_0
def face2_autosL_0 : List (List (Nat × Nat)) := []
def face2_autos_0 : BT (List (Nat × Nat)) := btOfList 1 face2_autosL_0
def face2_slicesL_0 : List (Option (Nat × Nat)) := []
def face2_slices_0 : BT (Option (Nat × Nat)) := btOfList 1 face2_slicesL_0
def face2_P_0 : BT (Option BoundPool) := buildPoolsBT 1 face2_W_0 face0_R_18 face2_slices_0 face0_ps_0
lemma face2_gp_0 : goodPairs face0_G_18 face2_pos_0 face2_neg_0 := goodPairs_of (by decide +kernel)
lemma face2_base_0_ok : ∀ x ∈ face2_base_0, faithful face2_pos_0 face2_neg_0 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma face2_W_0_ok : btAll (fun x => faithful face2_pos_0 face2_neg_0 x ∧ x.1 < 2^128) face2_W_0 := buildWiresBT_faithful face2_base_0_ok
set_option maxRecDepth 500000 in
lemma face2_autos_0_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw face0_G_18 = face0_G_18) face2_autos_0 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma face2_slices_0_ok : btAll (fun o => ∀ p, o = some p → Slice face0_R_18 face0_G_18 p.1 p.2) face2_slices_0 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice face0_R_18 face0_G_18 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 500000 in
lemma face2_P_0_ok : btAll (fun o => ∀ c, o = some c → ValidPool face0_R_18 face0_G_18 c) face2_P_0 := buildPoolsBT_sound face2_slices_0_ok
def face2_bk_0_init : BT (List (List Nat)) := BT.empty
lemma face2_bk_0_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face0_G_18 (0 - 1) xs.toFinset) face2_bk_0_init := trivial
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face2_chk_0_0 : checkNodesBT face2_W_0 face0_G_18 face0_fmask_0 face2_P_0 face2_autos_0 face2_bk_0_init 0 face0_nodes_0_0 = true := by decide +kernel
def face2_bk_0_0 : BT (List (List Nat)) := buildBucketsBT face2_W_0 face0_nodes_0_0
set_option maxRecDepth 500000 in
lemma face2_bk_0_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face0_G_18 0 xs.toFinset) face2_bk_0_0 :=
  buildBucketsBT_sound (by decide) face2_gp_0 face2_W_0_ok face2_P_0_ok face2_autos_0_ok face2_bk_0_init_ok face2_chk_0_0
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face2_chk_0_1 : checkNodesBT face2_W_0 face0_G_18 face0_fmask_0 face2_P_0 face2_autos_0 face2_bk_0_0 1 face0_nodes_0_0 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma face2_bk_0_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face0_G_18 1 xs.toFinset) face2_bk_0_0 :=
  buildBucketsBT_sound (by decide) face2_gp_0 face2_W_0_ok face2_P_0_ok face2_autos_0_ok face2_bk_0_0_ok face2_chk_0_1
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face2_chk_0_2 : checkNodesBT face2_W_0 face0_G_18 face0_fmask_0 face2_P_0 face2_autos_0 face2_bk_0_0 2 face0_nodes_0_0 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma face2_bk_0_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face0_G_18 2 xs.toFinset) face2_bk_0_0 :=
  buildBucketsBT_sound (by decide) face2_gp_0 face2_W_0_ok face2_P_0_ok face2_autos_0_ok face2_bk_0_1_ok face2_chk_0_2
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face2_chk_0_3 : checkNodesBT face2_W_0 face0_G_18 face0_fmask_0 face2_P_0 face2_autos_0 face2_bk_0_0 3 face0_nodes_0_3 = true := by decide +kernel
def face2_bk_0_3 : BT (List (List Nat)) := buildBucketsBT face2_W_0 face0_nodes_0_3
set_option maxRecDepth 500000 in
lemma face2_bk_0_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face0_G_18 3 xs.toFinset) face2_bk_0_3 :=
  buildBucketsBT_sound (by decide) face2_gp_0 face2_W_0_ok face2_P_0_ok face2_autos_0_ok face2_bk_0_2_ok face2_chk_0_3
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma face2_forestRoot_0_ok : forestRootCheck face0_R_18 face0_G_18 [(VAR 2,20,16),(VAR 4,20,4),(VAR 5,36,4)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma face2_forestRoot_0_in : bucketContainsBT face2_bk_0_3 face0_R_18 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma face2_low_0 : Lower face0_R_18 face0_G_18 4 := lower_of_forestBT face2_forestRoot_0_ok face2_bk_0_3_ok face2_forestRoot_0_in
lemma face2_low_6_ok : carryOK [(3,5),(1,3),(1,4),(1,2)] face1_R_8 face1_G_8 face0_R_18 face0_G_18 = true := by decide +kernel
lemma face2_low_6 : Lower face1_R_8 face1_G_8 4 := carry_of face2_low_6_ok face2_low_0
lemma face2_low_7_ok : carryOK [(1,3),(1,4),(1,2)] face0_R_9 face0_G_9 face0_R_18 face0_G_18 = true := by decide +kernel
lemma face2_low_7 : Lower face0_R_9 face0_G_9 4 := carry_of face2_low_7_ok face2_low_0
lemma face2_low_9_ok : carryOK [(1,2)] face0_R_17 face0_G_17 face0_R_18 face0_G_18 = true := by decide +kernel
lemma face2_low_9 : Lower face0_R_17 face0_G_17 4 := carry_of face2_low_9_ok face2_low_0
def face2_G_11 : Nat := 0xff00f000f0000000ff00f000f0000000
lemma face2_low_11_ok : liftCheck 0 8 face0_R_21 face2_G_11 face0_R_18 face0_G_18 [(VAR 3,28,20)] = true := by decide +kernel
lemma face2_low_11 : Lower face0_R_21 face2_G_11 5 := lift_of face2_low_11_ok face2_low_0
def face2_G_12 : Nat := 0xfff0ff00ff00f000fff0ff00ff00f000
def face2_pos_12 : List Nat := [12,12,24,24,28,40,40,44,52,52,52,56,12,12,12,24,24,24,40,40,40,52]
def face2_neg_12 : List Nat := [8,4,16,8,20,32,8,36,48,36,20,48,20,36,48,20,36,48,20,36,48,8]
def face2_fmask_12 : Nat := fullMask 22
def face2_base_12 : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x207793,0xdb692),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x1ff8ff,0x200049),(0xffff0000ffff0000ffff0000ffff0000,0x238f1c,0x16dd14),(0xffffffff00000000ffffffff00000000,0x3c0fe0,0x1b6ba0)]
def face2_steps_12 : List (Nat × Nat × Nat) := [(2,0,2),(1,0,2),(2,0,1),(0,0,2),(3,0,1),(1,0,1),(0,0,1),(3,0,2),(3,4,3),(2,9,2),(0,9,2),(1,4,3),(3,10,2),(1,10,2),(3,7,5)]
def face2_W_12 : BT Decor := buildWiresBT 5 face2_base_12 face2_steps_12
def face2_autosL_12 : List (List (Nat × Nat)) := [[],[(4,5)],[(2,4)],[(2,5),(2,4)],[(2,4),(2,5)],[(2,5)]]
def face2_autos_12 : BT (List (Nat × Nat)) := btOfList 3 face2_autosL_12
def face2_P_12 : BT (Option BoundPool) := buildPoolsBT 1 face2_W_12 face0_R_21 face2_slices_0 face0_ps_0
lemma face2_gp_12 : goodPairs face2_G_12 face2_pos_12 face2_neg_12 := goodPairs_of (by decide +kernel)
lemma face2_base_12_ok : ∀ x ∈ face2_base_12, faithful face2_pos_12 face2_neg_12 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma face2_W_12_ok : btAll (fun x => faithful face2_pos_12 face2_neg_12 x ∧ x.1 < 2^128) face2_W_12 := buildWiresBT_faithful face2_base_12_ok
set_option maxRecDepth 500000 in
lemma face2_autos_12_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw face2_G_12 = face2_G_12) face2_autos_12 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma face2_slices_12_ok : btAll (fun o => ∀ p, o = some p → Slice face0_R_21 face2_G_12 p.1 p.2) face2_slices_0 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice face0_R_21 face2_G_12 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 500000 in
lemma face2_P_12_ok : btAll (fun o => ∀ c, o = some c → ValidPool face0_R_21 face2_G_12 c) face2_P_12 := buildPoolsBT_sound face2_slices_12_ok
lemma face2_bk_12_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face2_G_12 (0 - 1) xs.toFinset) face2_bk_0_init := trivial
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face2_chk_12_0 : checkNodesBT face2_W_12 face2_G_12 face2_fmask_12 face2_P_12 face2_autos_12 face2_bk_0_init 0 face0_nodes_0_0 = true := by decide +kernel
def face2_bk_12_0 : BT (List (List Nat)) := buildBucketsBT face2_W_12 face0_nodes_0_0
set_option maxRecDepth 500000 in
lemma face2_bk_12_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face2_G_12 0 xs.toFinset) face2_bk_12_0 :=
  buildBucketsBT_sound (by decide) face2_gp_12 face2_W_12_ok face2_P_12_ok face2_autos_12_ok face2_bk_12_init_ok face2_chk_12_0
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face2_chk_12_1 : checkNodesBT face2_W_12 face2_G_12 face2_fmask_12 face2_P_12 face2_autos_12 face2_bk_12_0 1 face0_nodes_0_0 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma face2_bk_12_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face2_G_12 1 xs.toFinset) face2_bk_12_0 :=
  buildBucketsBT_sound (by decide) face2_gp_12 face2_W_12_ok face2_P_12_ok face2_autos_12_ok face2_bk_12_0_ok face2_chk_12_1
def face2_nodes_12_2 : List NodeSpec := [([18,1,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face2_chk_12_2 : checkNodesBT face2_W_12 face2_G_12 face2_fmask_12 face2_P_12 face2_autos_12 face2_bk_12_0 2 face2_nodes_12_2 = true := by decide +kernel
def face2_bk_12_2 : BT (List (List Nat)) := buildBucketsBT face2_W_12 face2_nodes_12_2
set_option maxRecDepth 500000 in
lemma face2_bk_12_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face2_G_12 2 xs.toFinset) face2_bk_12_2 :=
  buildBucketsBT_sound (by decide) face2_gp_12 face2_W_12_ok face2_P_12_ok face2_autos_12_ok face2_bk_12_1_ok face2_chk_12_2
def face2_nodes_12_3 : List NodeSpec := [([4,11,1,3],[],[0]),([0,1,2,12],[],[]),([7,1,5,3],[],[0]),([13,0,1,3],[],[]),([0,1,14,3],[],[]),([6,8,2,3],[],[]),([0,1,2,15],[],[]),([16,0,1,3],[],[]),([0,1,17,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face2_chk_12_3 : checkNodesBT face2_W_12 face2_G_12 face2_fmask_12 face2_P_12 face2_autos_12 face2_bk_12_2 3 face2_nodes_12_3 = true := by decide +kernel
def face2_bk_12_3 : BT (List (List Nat)) := buildBucketsBT face2_W_12 face2_nodes_12_3
set_option maxRecDepth 500000 in
lemma face2_bk_12_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face2_G_12 3 xs.toFinset) face2_bk_12_3 :=
  buildBucketsBT_sound (by decide) face2_gp_12 face2_W_12_ok face2_P_12_ok face2_autos_12_ok face2_bk_12_2_ok face2_chk_12_3
def face2_nodes_12_4 : List NodeSpec := [([4,0,1,2,3],[],[0]),([0,1,2,5,3],[],[0]),([6,0,1,2,3],[],[0]),([7,0,1,2,3],[],[0]),([8,0,1,2,3],[],[0]),([0,1,9,2,3],[],[0,1]),([10,0,1,2,3],[],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face2_chk_12_4 : checkNodesBT face2_W_12 face2_G_12 face2_fmask_12 face2_P_12 face2_autos_12 face2_bk_12_3 4 face2_nodes_12_4 = true := by decide +kernel
def face2_bk_12_4 : BT (List (List Nat)) := buildBucketsBT face2_W_12 face2_nodes_12_4
set_option maxRecDepth 500000 in
lemma face2_bk_12_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face2_G_12 4 xs.toFinset) face2_bk_12_4 :=
  buildBucketsBT_sound (by decide) face2_gp_12 face2_W_12_ok face2_P_12_ok face2_autos_12_ok face2_bk_12_3_ok face2_chk_12_4
def face2_nodes_12_5 : List NodeSpec := [([0,1,2,3],[],[0,2,1,3,4,5])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face2_chk_12_5 : checkNodesBT face2_W_12 face2_G_12 face2_fmask_12 face2_P_12 face2_autos_12 face2_bk_12_4 5 face2_nodes_12_5 = true := by decide +kernel
def face2_bk_12_5 : BT (List (List Nat)) := buildBucketsBT face2_W_12 face2_nodes_12_5
set_option maxRecDepth 500000 in
lemma face2_bk_12_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face2_G_12 5 xs.toFinset) face2_bk_12_5 :=
  buildBucketsBT_sound (by decide) face2_gp_12 face2_W_12_ok face2_P_12_ok face2_autos_12_ok face2_bk_12_4_ok face2_chk_12_5
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma face2_forestRoot_12_ok : forestRootCheck face0_R_21 face2_G_12 [(VAR 2,12,8),(VAR 3,12,4),(VAR 4,24,8),(VAR 5,40,8)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma face2_forestRoot_12_in : bucketContainsBT face2_bk_12_5 face0_R_21 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma face2_low_12 : Lower face0_R_21 face2_G_12 6 := lower_of_forestBT face2_forestRoot_12_ok face2_bk_12_5_ok face2_forestRoot_12_in
def face2_G_13 : Nat := 0xfffffcfcfcfcc0c0fffffcfcfcfcc0c0
def face2_pos_13 : List Nat := [6,6,18,18,20,20,34,34,36,36,48,48,6,6,18,18,20,20,34,34,36,36,48,48]
def face2_neg_13 : List Nat := [4,2,16,2,16,4,32,2,32,4,32,16,16,32,4,32,2,32,4,16,2,16,2,4]
def face2_base_13 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xcf0cf,0x51008a),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x333333,0x844221),(0xffff0000ffff0000ffff0000ffff0000,0xc3cc3c,0x281814),(0xffffffff00000000ffffffff00000000,0xfc0fc0,0x2a540)]
def face2_W_13 : BT Decor := buildWiresBT 4 face2_base_13 face1_steps_20
def face2_autosL_13 : List (List (Nat × Nat)) := [[],[(4,5)],[(1,2)],[(4,5),(1,2)],[(2,4)],[(2,5),(2,4)],[(1,2),(1,4)],[(2,5),(1,2),(1,4)],[(2,5),(1,4)]]
def face2_autos_13 : BT (List (Nat × Nat)) := btOfList 4 face2_autosL_13
def face2_slicesL_13 : List (Option (Nat × Nat)) := [some (subcubeFast 4 0,4),some (subcubeFast 2 0,4),some (subcubeFast 32 0,4),some (subcubeFast 16 0,4)]
def face2_slices_13 : BT (Option (Nat × Nat)) := btOfList 2 face2_slicesL_13
def face2_P_13 : BT (Option BoundPool) := buildPoolsBT 2 face2_W_13 face0_R_33 face2_slices_13 face0_ps_21
lemma face2_gp_13 : goodPairs face2_G_13 face2_pos_13 face2_neg_13 := goodPairs_of (by decide +kernel)
lemma face2_base_13_ok : ∀ x ∈ face2_base_13, faithful face2_pos_13 face2_neg_13 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma face2_W_13_ok : btAll (fun x => faithful face2_pos_13 face2_neg_13 x ∧ x.1 < 2^128) face2_W_13 := buildWiresBT_faithful face2_base_13_ok
set_option maxRecDepth 500000 in
lemma face2_autos_13_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw face2_G_13 = face2_G_13) face2_autos_13 := btAll_ofList (autos_of (by decide +kernel))
lemma face2_sl_13_0_ok : sliceDirectCheck 4 0 0 face0_R_33 face2_G_13 face0_R_17 face0_G_17 = true := by decide +kernel
lemma face2_sl_13_0 : Slice face0_R_33 face2_G_13 (subcubeFast 4 0) 4 := slice_fast_direct face2_sl_13_0_ok face2_low_9
lemma face2_sl_13_1_ok : sliceDirectCheck 2 0 0 face0_R_33 face2_G_13 face0_R_18 face0_G_18 = true := by decide +kernel
lemma face2_sl_13_1 : Slice face0_R_33 face2_G_13 (subcubeFast 2 0) 4 := slice_fast_direct face2_sl_13_1_ok face2_low_0
lemma face2_sl_13_2_ok : sliceDirectCheck 32 0 0 face0_R_33 face2_G_13 face1_R_8 face1_G_8 = true := by decide +kernel
lemma face2_sl_13_2 : Slice face0_R_33 face2_G_13 (subcubeFast 32 0) 4 := slice_fast_direct face2_sl_13_2_ok face2_low_6
lemma face2_sl_13_3_ok : sliceDirectCheck 16 0 0 face0_R_33 face2_G_13 face0_R_9 face0_G_9 = true := by decide +kernel
lemma face2_sl_13_3 : Slice face0_R_33 face2_G_13 (subcubeFast 16 0) 4 := slice_fast_direct face2_sl_13_3_ok face2_low_7
set_option maxRecDepth 500000 in
lemma face2_slices_13_ok : btAll (fun o => ∀ p, o = some p → Slice face0_R_33 face2_G_13 p.1 p.2) face2_slices_13 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice face0_R_33 face2_G_13 p.1 p.2) (forall_cons (fun _ h => by cases h; exact face2_sl_13_0) (forall_cons (fun _ h => by cases h; exact face2_sl_13_1) (forall_cons (fun _ h => by cases h; exact face2_sl_13_2) (forall_cons (fun _ h => by cases h; exact face2_sl_13_3) (fun _ h => (List.not_mem_nil h).elim)))))
set_option maxRecDepth 500000 in
lemma face2_P_13_ok : btAll (fun o => ∀ c, o = some c → ValidPool face0_R_33 face2_G_13 c) face2_P_13 := buildPoolsBT_sound face2_slices_13_ok
lemma face2_bk_13_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face2_G_13 (0 - 1) xs.toFinset) face2_bk_0_init := trivial
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face2_chk_13_0 : checkNodesBT face2_W_13 face2_G_13 face0_fmask_21 face2_P_13 face2_autos_13 face2_bk_0_init 0 face0_nodes_0_0 = true := by decide +kernel
def face2_bk_13_0 : BT (List (List Nat)) := buildBucketsBT face2_W_13 face0_nodes_0_0
set_option maxRecDepth 500000 in
lemma face2_bk_13_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face2_G_13 0 xs.toFinset) face2_bk_13_0 :=
  buildBucketsBT_sound (by decide) face2_gp_13 face2_W_13_ok face2_P_13_ok face2_autos_13_ok face2_bk_13_init_ok face2_chk_13_0
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face2_chk_13_1 : checkNodesBT face2_W_13 face2_G_13 face0_fmask_21 face2_P_13 face2_autos_13 face2_bk_13_0 1 face0_nodes_0_0 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma face2_bk_13_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face2_G_13 1 xs.toFinset) face2_bk_13_0 :=
  buildBucketsBT_sound (by decide) face2_gp_13 face2_W_13_ok face2_P_13_ok face2_autos_13_ok face2_bk_13_0_ok face2_chk_13_1
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face2_chk_13_2 : checkNodesBT face2_W_13 face2_G_13 face0_fmask_21 face2_P_13 face2_autos_13 face2_bk_13_0 2 face0_nodes_0_0 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma face2_bk_13_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face2_G_13 2 xs.toFinset) face2_bk_13_0 :=
  buildBucketsBT_sound (by decide) face2_gp_13 face2_W_13_ok face2_P_13_ok face2_autos_13_ok face2_bk_13_1_ok face2_chk_13_2
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face2_chk_13_3 : checkNodesBT face2_W_13 face2_G_13 face0_fmask_21 face2_P_13 face2_autos_13 face2_bk_13_0 3 face1_nodes_20_3 = true := by decide +kernel
def face2_bk_13_3 : BT (List (List Nat)) := buildBucketsBT face2_W_13 face1_nodes_20_3
set_option maxRecDepth 500000 in
lemma face2_bk_13_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face2_G_13 3 xs.toFinset) face2_bk_13_3 :=
  buildBucketsBT_sound (by decide) face2_gp_13 face2_W_13_ok face2_P_13_ok face2_autos_13_ok face2_bk_13_2_ok face2_chk_13_3
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face2_chk_13_4 : checkNodesBT face2_W_13 face2_G_13 face0_fmask_21 face2_P_13 face2_autos_13 face2_bk_13_3 4 face1_nodes_20_4 = true := by decide +kernel
def face2_bk_13_4 : BT (List (List Nat)) := buildBucketsBT face2_W_13 face1_nodes_20_4
set_option maxRecDepth 500000 in
lemma face2_bk_13_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face2_G_13 4 xs.toFinset) face2_bk_13_4 :=
  buildBucketsBT_sound (by decide) face2_gp_13 face2_W_13_ok face2_P_13_ok face2_autos_13_ok face2_bk_13_3_ok face2_chk_13_4
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face2_chk_13_5 : checkNodesBT face2_W_13 face2_G_13 face0_fmask_21 face2_P_13 face2_autos_13 face2_bk_13_4 5 face1_nodes_20_5 = true := by decide +kernel
def face2_bk_13_5 : BT (List (List Nat)) := buildBucketsBT face2_W_13 face1_nodes_20_5
set_option maxRecDepth 500000 in
lemma face2_bk_13_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face2_G_13 5 xs.toFinset) face2_bk_13_5 :=
  buildBucketsBT_sound (by decide) face2_gp_13 face2_W_13_ok face2_P_13_ok face2_autos_13_ok face2_bk_13_4_ok face2_chk_13_5
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face2_chk_13_6 : checkNodesBT face2_W_13 face2_G_13 face0_fmask_21 face2_P_13 face2_autos_13 face2_bk_13_5 6 face1_nodes_20_6 = true := by decide +kernel
def face2_bk_13_6 : BT (List (List Nat)) := buildBucketsBT face2_W_13 face1_nodes_20_6
set_option maxRecDepth 500000 in
lemma face2_bk_13_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face2_G_13 6 xs.toFinset) face2_bk_13_6 :=
  buildBucketsBT_sound (by decide) face2_gp_13 face2_W_13_ok face2_P_13_ok face2_autos_13_ok face2_bk_13_5_ok face2_chk_13_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma face2_forestRoot_13_ok : forestRootCheck face0_R_33 face2_G_13 [(VAR 1,6,4),(VAR 2,6,2),(VAR 4,18,2),(VAR 5,34,2)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma face2_forestRoot_13_in : bucketContainsBT face2_bk_13_6 face0_R_33 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma face2_low_13 : Lower face0_R_33 face2_G_13 7 := lower_of_forestBT face2_forestRoot_13_ok face2_bk_13_6_ok face2_forestRoot_13_in
def face2_G_23 : Nat := 0xfc00c000fc00c000fc00c000fc00c000
lemma face2_low_23_ok : carryOK [(1,5),(1,4),(1,2)] face0_R_31 face2_G_23 face0_R_21 face2_G_11 = true := by decide +kernel
lemma face2_low_23 : Lower face0_R_31 face2_G_23 5 := carry_of face2_low_23_ok face2_low_11
def face2_G_24 : Nat := 0xfc00fc00c000c000fc00fc00c000c000
lemma face2_low_24_ok : carryOK [(1,4),(1,2)] face0_R_32 face2_G_24 face0_R_21 face2_G_11 = true := by decide +kernel
lemma face2_low_24 : Lower face0_R_32 face2_G_24 5 := carry_of face2_low_24_ok face2_low_11
def face2_G_29 : Nat := 0xff00cc00cc000000ff00cc00cc000000
lemma face2_low_29_ok : carryOK [(1,2)] face0_R_37 face2_G_29 face0_R_21 face2_G_11 = true := by decide +kernel
lemma face2_low_29 : Lower face0_R_37 face2_G_29 5 := carry_of face2_low_29_ok face2_low_11
def face2_G_35 : Nat := 0xffc0fc00ffc0fc00ffc0fc00ffc0fc00
lemma face2_low_35_ok : carryOK [(1,5),(1,4),(1,2)] face0_R_31 face2_G_35 face0_R_21 face2_G_12 = true := by decide +kernel
lemma face2_low_35 : Lower face0_R_31 face2_G_35 6 := carry_of face2_low_35_ok face2_low_12
def face2_G_36 : Nat := 0xffc0ffc0fc00fc00ffc0ffc0fc00fc00
lemma face2_low_36_ok : carryOK [(1,4),(1,2)] face0_R_32 face2_G_36 face0_R_21 face2_G_12 = true := by decide +kernel
lemma face2_low_36 : Lower face0_R_32 face2_G_36 6 := carry_of face2_low_36_ok face2_low_12
def face2_G_37 : Nat := 0xffccff00ff00cc00ffccff00ff00cc00
lemma face2_low_37_ok : carryOK [(1,2)] face0_R_37 face2_G_37 face0_R_21 face2_G_12 = true := by decide +kernel
lemma face2_low_37 : Lower face0_R_37 face2_G_37 6 := carry_of face2_low_37_ok face2_low_12
def face2_G_42 : Nat := 0xffc0fc00fc00c000ffc0fc00fc00c000
def face2_pos_42 : List Nat := [14,14,14,26,26,26,28,28,28,30,42,42,42,44,44,44,46,54,54,54,54,56,56,56,58,60,14,14,14,14,14,14,26,26,26,26,26,26,28,28,28,28,28,28,42,42,42,42,42,42,44,44,44,44,44,44,54,54,54,54,56,56,56,56,56,56]
def face2_neg_42 : List Nat := [12,10,6,24,18,10,24,20,12,22,40,34,10,40,36,12,38,52,50,38,22,48,40,24,50,52,22,24,38,40,50,52,12,22,38,40,50,52,10,22,38,40,50,52,12,22,24,38,50,52,10,22,24,38,50,52,10,12,24,40,10,12,22,38,50,52]
def face2_fmask_42 : Nat := fullMask 66
def face2_base_42 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xf03f03ffd1f1e3f,0x1d16da5d6551d1a36),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffc0fc0fe1fe3c7,0x2e2aab9a7961bc385),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x3f0ffffffffe1ffff,0x3f14524928c0b56b),(0xffff0000ffff0000ffff0000ffff0000,0x3ff000fff03fe03f8,0x344db6cb2cfb602d8),(0xffffffff00000000ffffffff00000000,0x3fffff00003fffc00,0x388e38f3cf36f6c00)]
def face2_steps_42 : List (Nat × Nat × Nat) := [(0,0,1),(0,3,4),(1,5,6)]
def face2_W_42 : BT Decor := buildWiresBT 3 face2_base_42 face2_steps_42
def face2_autosL_42 : List (List (Nat × Nat)) := [[],[(2,4)],[(2,5),(2,4)],[(1,2),(1,4)],[(2,5),(1,2),(1,4)],[(2,5),(1,4)]]
def face2_autos_42 : BT (List (Nat × Nat)) := btOfList 3 face2_autosL_42
def face2_slicesL_42 : List (Option (Nat × Nat)) := [some (subcubeFast 4 0,5),some (subcubeFast 32 0,5),some (subcubeFast 0 16,6),some (subcubeFast 16 0,5),some (subcubeFast 0 32,6),some (subcubeFast 0 2,6),some (subcubeFast 2 0,5),some (subcubeFast 0 4,6),some (subcubeFast 0 8,7),some (subcubeFast 4 8,4)]
def face2_slices_42 : BT (Option (Nat × Nat)) := btOfList 4 face2_slicesL_42
def face2_ps_42 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[(0,3,4)]),(6,[]),(7,[]),(4,[(0,0,1)]),(5,[]),(8,[]),(9,[]),(2,[(0,0,1)])]
def face2_P_42 : BT (Option BoundPool) := buildPoolsBT 4 face2_W_42 face0_R_47 face2_slices_42 face2_ps_42
lemma face2_gp_42 : goodPairs face2_G_42 face2_pos_42 face2_neg_42 := goodPairs_of (by decide +kernel)
lemma face2_base_42_ok : ∀ x ∈ face2_base_42, faithful face2_pos_42 face2_neg_42 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma face2_W_42_ok : btAll (fun x => faithful face2_pos_42 face2_neg_42 x ∧ x.1 < 2^128) face2_W_42 := buildWiresBT_faithful face2_base_42_ok
set_option maxRecDepth 500000 in
lemma face2_autos_42_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw face2_G_42 = face2_G_42) face2_autos_42 := btAll_ofList (autos_of (by decide +kernel))
lemma face2_sl_42_0_ok : sliceDirectCheck 4 0 0 face0_R_47 face2_G_42 face0_R_37 face2_G_29 = true := by decide +kernel
lemma face2_sl_42_0 : Slice face0_R_47 face2_G_42 (subcubeFast 4 0) 5 := slice_fast_direct face2_sl_42_0_ok face2_low_29
lemma face2_sl_42_1_ok : sliceDirectCheck 32 0 0 face0_R_47 face2_G_42 face0_R_31 face2_G_23 = true := by decide +kernel
lemma face2_sl_42_1 : Slice face0_R_47 face2_G_42 (subcubeFast 32 0) 5 := slice_fast_direct face2_sl_42_1_ok face2_low_23
lemma face2_sl_42_2_ok : sliceDirectCheck 0 16 0 face0_R_47 face2_G_42 face0_R_32 face2_G_36 = true := by decide +kernel
lemma face2_sl_42_2 : Slice face0_R_47 face2_G_42 (subcubeFast 0 16) 6 := slice_fast_direct face2_sl_42_2_ok face2_low_36
lemma face2_sl_42_3_ok : sliceDirectCheck 16 0 0 face0_R_47 face2_G_42 face0_R_32 face2_G_24 = true := by decide +kernel
lemma face2_sl_42_3 : Slice face0_R_47 face2_G_42 (subcubeFast 16 0) 5 := slice_fast_direct face2_sl_42_3_ok face2_low_24
lemma face2_sl_42_4_ok : sliceDirectCheck 0 32 0 face0_R_47 face2_G_42 face0_R_31 face2_G_35 = true := by decide +kernel
lemma face2_sl_42_4 : Slice face0_R_47 face2_G_42 (subcubeFast 0 32) 6 := slice_fast_direct face2_sl_42_4_ok face2_low_35
lemma face2_sl_42_5_ok : sliceDirectCheck 0 2 0 face0_R_47 face2_G_42 face0_R_21 face2_G_12 = true := by decide +kernel
lemma face2_sl_42_5 : Slice face0_R_47 face2_G_42 (subcubeFast 0 2) 6 := slice_fast_direct face2_sl_42_5_ok face2_low_12
lemma face2_sl_42_6_ok : sliceDirectCheck 2 0 0 face0_R_47 face2_G_42 face0_R_21 face2_G_11 = true := by decide +kernel
lemma face2_sl_42_6 : Slice face0_R_47 face2_G_42 (subcubeFast 2 0) 5 := slice_fast_direct face2_sl_42_6_ok face2_low_11
lemma face2_sl_42_7_ok : sliceDirectCheck 0 4 0 face0_R_47 face2_G_42 face0_R_37 face2_G_37 = true := by decide +kernel
lemma face2_sl_42_7 : Slice face0_R_47 face2_G_42 (subcubeFast 0 4) 6 := slice_fast_direct face2_sl_42_7_ok face2_low_37
lemma face2_sl_42_8_ok : sliceDirectCheck 0 8 0 face0_R_47 face2_G_42 face0_R_33 face2_G_13 = true := by decide +kernel
lemma face2_sl_42_8 : Slice face0_R_47 face2_G_42 (subcubeFast 0 8) 7 := slice_fast_direct face2_sl_42_8_ok face2_low_13
lemma face2_sl_42_9_ok : sliceDirectCheck 4 8 0 face0_R_47 face2_G_42 face0_R_17 face0_G_17 = true := by decide +kernel
lemma face2_sl_42_9 : Slice face0_R_47 face2_G_42 (subcubeFast 4 8) 4 := slice_fast_direct face2_sl_42_9_ok face2_low_9
set_option maxRecDepth 500000 in
lemma face2_slices_42_ok : btAll (fun o => ∀ p, o = some p → Slice face0_R_47 face2_G_42 p.1 p.2) face2_slices_42 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice face0_R_47 face2_G_42 p.1 p.2) (forall_cons (fun _ h => by cases h; exact face2_sl_42_0) (forall_cons (fun _ h => by cases h; exact face2_sl_42_1) (forall_cons (fun _ h => by cases h; exact face2_sl_42_2) (forall_cons (fun _ h => by cases h; exact face2_sl_42_3) (forall_cons (fun _ h => by cases h; exact face2_sl_42_4) (forall_cons (fun _ h => by cases h; exact face2_sl_42_5) (forall_cons (fun _ h => by cases h; exact face2_sl_42_6) (forall_cons (fun _ h => by cases h; exact face2_sl_42_7) (forall_cons (fun _ h => by cases h; exact face2_sl_42_8) (forall_cons (fun _ h => by cases h; exact face2_sl_42_9) (fun _ h => (List.not_mem_nil h).elim)))))))))))
set_option maxRecDepth 500000 in
lemma face2_P_42_ok : btAll (fun o => ∀ c, o = some c → ValidPool face0_R_47 face2_G_42 c) face2_P_42 := buildPoolsBT_sound face2_slices_42_ok
lemma face2_bk_42_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face2_G_42 (0 - 1) xs.toFinset) face2_bk_0_init := trivial
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face2_chk_42_0 : checkNodesBT face2_W_42 face2_G_42 face2_fmask_42 face2_P_42 face2_autos_42 face2_bk_0_init 0 face0_nodes_0_0 = true := by decide +kernel
def face2_bk_42_0 : BT (List (List Nat)) := buildBucketsBT face2_W_42 face0_nodes_0_0
set_option maxRecDepth 500000 in
lemma face2_bk_42_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face2_G_42 0 xs.toFinset) face2_bk_42_0 :=
  buildBucketsBT_sound (by decide) face2_gp_42 face2_W_42_ok face2_P_42_ok face2_autos_42_ok face2_bk_42_init_ok face2_chk_42_0
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face2_chk_42_1 : checkNodesBT face2_W_42 face2_G_42 face2_fmask_42 face2_P_42 face2_autos_42 face2_bk_42_0 1 face0_nodes_0_0 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma face2_bk_42_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face2_G_42 1 xs.toFinset) face2_bk_42_0 :=
  buildBucketsBT_sound (by decide) face2_gp_42 face2_W_42_ok face2_P_42_ok face2_autos_42_ok face2_bk_42_0_ok face2_chk_42_1
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face2_chk_42_2 : checkNodesBT face2_W_42 face2_G_42 face2_fmask_42 face2_P_42 face2_autos_42 face2_bk_42_0 2 face0_nodes_0_0 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma face2_bk_42_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face2_G_42 2 xs.toFinset) face2_bk_42_0 :=
  buildBucketsBT_sound (by decide) face2_gp_42 face2_W_42_ok face2_P_42_ok face2_autos_42_ok face2_bk_42_1_ok face2_chk_42_2
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face2_chk_42_3 : checkNodesBT face2_W_42 face2_G_42 face2_fmask_42 face2_P_42 face2_autos_42 face2_bk_42_0 3 face0_nodes_0_0 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma face2_bk_42_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face2_G_42 3 xs.toFinset) face2_bk_42_0 :=
  buildBucketsBT_sound (by decide) face2_gp_42 face2_W_42_ok face2_P_42_ok face2_autos_42_ok face2_bk_42_2_ok face2_chk_42_3
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face2_chk_42_4 : checkNodesBT face2_W_42 face2_G_42 face2_fmask_42 face2_P_42 face2_autos_42 face2_bk_42_0 4 face0_nodes_0_0 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma face2_bk_42_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face2_G_42 4 xs.toFinset) face2_bk_42_0 :=
  buildBucketsBT_sound (by decide) face2_gp_42 face2_W_42_ok face2_P_42_ok face2_autos_42_ok face2_bk_42_3_ok face2_chk_42_4
def face2_nodes_42_5 : List NodeSpec := [([0,1,2,3,7,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face2_chk_42_5 : checkNodesBT face2_W_42 face2_G_42 face2_fmask_42 face2_P_42 face2_autos_42 face2_bk_42_0 5 face2_nodes_42_5 = true := by decide +kernel
def face2_bk_42_5 : BT (List (List Nat)) := buildBucketsBT face2_W_42 face2_nodes_42_5
set_option maxRecDepth 500000 in
lemma face2_bk_42_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face2_G_42 5 xs.toFinset) face2_bk_42_5 :=
  buildBucketsBT_sound (by decide) face2_gp_42 face2_W_42_ok face2_P_42_ok face2_autos_42_ok face2_bk_42_4_ok face2_chk_42_5
def face2_nodes_42_6 : List NodeSpec := [([5,0,1,2,6,3,4],[0,1,2,3,4,5,6,7,8],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face2_chk_42_6 : checkNodesBT face2_W_42 face2_G_42 face2_fmask_42 face2_P_42 face2_autos_42 face2_bk_42_5 6 face2_nodes_42_6 = true := by decide +kernel
def face2_bk_42_6 : BT (List (List Nat)) := buildBucketsBT face2_W_42 face2_nodes_42_6
set_option maxRecDepth 500000 in
lemma face2_bk_42_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face2_G_42 6 xs.toFinset) face2_bk_42_6 :=
  buildBucketsBT_sound (by decide) face2_gp_42 face2_W_42_ok face2_P_42_ok face2_autos_42_ok face2_bk_42_5_ok face2_chk_42_6
def face2_nodes_42_7 : List NodeSpec := [([5,0,1,2,3,4],[7,9,0,10,11,2,3,4,1,8,12],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face2_chk_42_7 : checkNodesBT face2_W_42 face2_G_42 face2_fmask_42 face2_P_42 face2_autos_42 face2_bk_42_6 7 face2_nodes_42_7 = true := by decide +kernel
def face2_bk_42_7 : BT (List (List Nat)) := buildBucketsBT face2_W_42 face2_nodes_42_7
set_option maxRecDepth 500000 in
lemma face2_bk_42_7_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face2_G_42 7 xs.toFinset) face2_bk_42_7 :=
  buildBucketsBT_sound (by decide) face2_gp_42 face2_W_42_ok face2_P_42_ok face2_autos_42_ok face2_bk_42_6_ok face2_chk_42_7
def face2_nodes_42_8 : List NodeSpec := [([0,1,2,3,4],[9,7,10,2,4],[0,1,2,3,4,5])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face2_chk_42_8 : checkNodesBT face2_W_42 face2_G_42 face2_fmask_42 face2_P_42 face2_autos_42 face2_bk_42_7 8 face2_nodes_42_8 = true := by decide +kernel
def face2_bk_42_8 : BT (List (List Nat)) := buildBucketsBT face2_W_42 face2_nodes_42_8
set_option maxRecDepth 500000 in
lemma face2_bk_42_8_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face2_G_42 8 xs.toFinset) face2_bk_42_8 :=
  buildBucketsBT_sound (by decide) face2_gp_42 face2_W_42_ok face2_P_42_ok face2_autos_42_ok face2_bk_42_7_ok face2_chk_42_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma face2_forestRoot_42_ok : forestRootCheck face0_R_47 face2_G_42 [(VAR 1,14,12),(VAR 2,14,10),(VAR 3,14,6),(VAR 4,26,10),(VAR 5,42,10)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma face2_forestRoot_42_in : bucketContainsBT face2_bk_42_8 face0_R_47 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma face2_low_42 : Lower face0_R_47 face2_G_42 9 := lower_of_forestBT face2_forestRoot_42_ok face2_bk_42_8_ok face2_forestRoot_42_in
def face3_pos_0 : List Nat := [6,6,10,10,12,12,6,10,12]
def face3_neg_0 : List Nat := [4,2,8,2,8,4,8,4,2]
def face3_base_0 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xcf,0x10a),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x173,0xa1),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x1bc,0x54)]
def face3_W_0 : Array Decor := buildWires face3_base_0 face0_steps_0
def face3_P_0 : Array (Option BoundPool) := buildPools face3_W_0 face0_R_7 face0_slices_0 face0_ps_0
lemma face3_gp_0 : goodPairs face0_G_7 face3_pos_0 face3_neg_0 := goodPairs_of (by decide +kernel)
lemma face3_base_0_ok : ∀ x ∈ face3_base_0, faithful face3_pos_0 face3_neg_0 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma face3_W_0_ok : ∀ x ∈ face3_W_0.toList, faithful face3_pos_0 face3_neg_0 x ∧ x.1 < 2^128 := buildWires_faithful face3_base_0_ok
lemma face3_autos_0_ok : ∀ sw ∈ face0_autos_0.toList, swapsValid sw = true ∧ permWord sw face0_G_7 = face0_G_7 := autos_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma face3_slices_0_ok : ∀ i (hi : i < face0_slices_0.size), Slice face0_R_7 face0_G_7 face0_slices_0[i].1 face0_slices_0[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice face0_R_7 face0_G_7 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma face3_P_0_ok : ∀ i (hi : i < face3_P_0.size), ∀ c, face3_P_0[i] = some c → ValidPool face0_R_7 face0_G_7 c := buildPools_sound face3_slices_0_ok
lemma face3_bk_0_init_ok : ∀ i (hi : i < face0_bk_0_init.size), ∀ xs ∈ face0_bk_0_init[i], Impossible face0_G_7 (0 - 1) xs.toFinset := by intro i hi; simp [face0_bk_0_init] at hi
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face3_chk_0_0 : checkNodes face3_W_0 face0_G_7 face0_fmask_0 face3_P_0 face0_autos_0 face0_bk_0_init 0 face0_nodes_0_0 = true := by decide +kernel
def face3_bk_0_0 : Array (List (List Nat)) := buildBuckets 1 face3_W_0 face0_nodes_0_0
lemma face3_bk_0_0_ok : ∀ i (hi : i < face3_bk_0_0.size), ∀ xs ∈ face3_bk_0_0[i], Impossible face0_G_7 0 xs.toFinset :=
  buildBuckets_sound (by decide) face3_gp_0 face3_W_0_ok face3_P_0_ok face3_autos_0_ok face3_bk_0_init_ok face3_chk_0_0
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face3_chk_0_1 : checkNodes face3_W_0 face0_G_7 face0_fmask_0 face3_P_0 face0_autos_0 face3_bk_0_0 1 face0_nodes_0_0 = true := by decide +kernel
lemma face3_bk_0_1_ok : ∀ i (hi : i < face3_bk_0_0.size), ∀ xs ∈ face3_bk_0_0[i], Impossible face0_G_7 1 xs.toFinset :=
  buildBuckets_sound (by decide) face3_gp_0 face3_W_0_ok face3_P_0_ok face3_autos_0_ok face3_bk_0_0_ok face3_chk_0_1
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face3_chk_0_2 : checkNodes face3_W_0 face0_G_7 face0_fmask_0 face3_P_0 face0_autos_0 face3_bk_0_0 2 face0_nodes_0_0 = true := by decide +kernel
lemma face3_bk_0_2_ok : ∀ i (hi : i < face3_bk_0_0.size), ∀ xs ∈ face3_bk_0_0[i], Impossible face0_G_7 2 xs.toFinset :=
  buildBuckets_sound (by decide) face3_gp_0 face3_W_0_ok face3_P_0_ok face3_autos_0_ok face3_bk_0_1_ok face3_chk_0_2
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face3_chk_0_3 : checkNodes face3_W_0 face0_G_7 face0_fmask_0 face3_P_0 face0_autos_0 face3_bk_0_0 3 face0_nodes_0_3 = true := by decide +kernel
def face3_bk_0_3 : Array (List (List Nat)) := buildBuckets 1 face3_W_0 face0_nodes_0_3
lemma face3_bk_0_3_ok : ∀ i (hi : i < face3_bk_0_3.size), ∀ xs ∈ face3_bk_0_3[i], Impossible face0_G_7 3 xs.toFinset :=
  buildBuckets_sound (by decide) face3_gp_0 face3_W_0_ok face3_P_0_ok face3_autos_0_ok face3_bk_0_2_ok face3_chk_0_3
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face3_forestRoot_0_ok : forestRootCheck face0_R_7 face0_G_7 [(VAR 1,6,4),(VAR 2,6,2),(VAR 3,10,2)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face3_forestRoot_0_in : bucketContains face3_bk_0_3 face0_R_7 = true := by decide +kernel
lemma face3_low_0 : Lower face0_R_7 face0_G_7 4 := lower_of_forest face3_forestRoot_0_ok face3_bk_0_3_ok face3_forestRoot_0_in
def face3_G_7 : Nat := 0xffaaffaaaa00aa00ffaaffaaaa00aa00
def face3_R_7 : List Nat := varsOf 41
lemma face3_low_7_ok : carryOK [(3,5),(2,3),(2,4),(0,1)] face3_R_7 face3_G_7 face0_R_7 face0_G_7 = true := by decide +kernel
lemma face3_low_7 : Lower face3_R_7 face3_G_7 4 := carry_of face3_low_7_ok face3_low_0
lemma face3_low_8_ok : carryOK [(3,5),(2,3),(2,4)] face0_R_13 face0_G_13 face0_R_7 face0_G_7 = true := by decide +kernel
lemma face3_low_8 : Lower face0_R_13 face0_G_13 4 := carry_of face3_low_8_ok face3_low_0
lemma face3_low_9_ok : carryOK [(3,5),(2,3),(1,2),(1,4)] face0_R_15 face0_G_15 face0_R_7 face0_G_7 = true := by decide +kernel
lemma face3_low_9 : Lower face0_R_15 face0_G_15 4 := carry_of face3_low_9_ok face3_low_0
def face3_G_14 : Nat := 0xffc0ffc0c000c000ffc0ffc0c000c000
lemma face3_low_14_ok : liftCheck 0 2 face0_R_32 face3_G_14 face0_R_15 face0_G_15 [(VAR 1,14,12)] = true := by decide +kernel
lemma face3_low_14 : Lower face0_R_32 face3_G_14 5 := lift_of face3_low_14_ok face3_low_9
def face3_G_16 : Nat := 0xfffcc000fffcc000fffcc000fffcc000
def face3_pos_16 : List Nat := [14,14,14,18,18,20,20,22,24,24,26,28,14,18,18,18,20,20,20,24,24,24]
def face3_neg_16 : List Nat := [12,10,6,16,2,16,4,6,16,8,10,12,16,6,10,12,6,10,12,6,10,12]
def face3_base_16 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xf49f,0x1b6496),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x718e7,0x2da8c5),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x381f07,0x36ce03),(0xffff0000ffff0000ffff0000ffff0000,0x3feff8,0x1128)]
def face3_steps_16 : List (Nat × Nat × Nat) := [(3,0,3),(2,0,3),(0,0,3),(2,0,1),(1,0,1),(1,0,3),(0,0,1),(3,1,9),(0,1,9),(1,6,1),(3,0,1),(3,7,2),(1,7,2),(3,6,1),(3,10,8)]
def face3_W_16 : Array Decor := buildWires face3_base_16 face3_steps_16
def face3_autos_16 : Array (List (Nat × Nat)) := #[[],[(2,3)],[(1,2)],[(1,3),(1,2)],[(1,2),(1,3)],[(1,3)]]
def face3_P_16 : Array (Option BoundPool) := buildPools face3_W_16 face0_R_31 face0_slices_0 face0_ps_0
lemma face3_gp_16 : goodPairs face3_G_16 face3_pos_16 face3_neg_16 := goodPairs_of (by decide +kernel)
lemma face3_base_16_ok : ∀ x ∈ face3_base_16, faithful face3_pos_16 face3_neg_16 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma face3_W_16_ok : ∀ x ∈ face3_W_16.toList, faithful face3_pos_16 face3_neg_16 x ∧ x.1 < 2^128 := buildWires_faithful face3_base_16_ok
lemma face3_autos_16_ok : ∀ sw ∈ face3_autos_16.toList, swapsValid sw = true ∧ permWord sw face3_G_16 = face3_G_16 := autos_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma face3_slices_16_ok : ∀ i (hi : i < face0_slices_0.size), Slice face0_R_31 face3_G_16 face0_slices_0[i].1 face0_slices_0[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice face0_R_31 face3_G_16 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma face3_P_16_ok : ∀ i (hi : i < face3_P_16.size), ∀ c, face3_P_16[i] = some c → ValidPool face0_R_31 face3_G_16 c := buildPools_sound face3_slices_16_ok
lemma face3_bk_16_init_ok : ∀ i (hi : i < face0_bk_0_init.size), ∀ xs ∈ face0_bk_0_init[i], Impossible face3_G_16 (0 - 1) xs.toFinset := by intro i hi; simp [face0_bk_0_init] at hi
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face3_chk_16_0 : checkNodes face3_W_16 face3_G_16 face2_fmask_12 face3_P_16 face3_autos_16 face0_bk_0_init 0 face0_nodes_0_0 = true := by decide +kernel
def face3_bk_16_0 : Array (List (List Nat)) := buildBuckets 1 face3_W_16 face0_nodes_0_0
lemma face3_bk_16_0_ok : ∀ i (hi : i < face3_bk_16_0.size), ∀ xs ∈ face3_bk_16_0[i], Impossible face3_G_16 0 xs.toFinset :=
  buildBuckets_sound (by decide) face3_gp_16 face3_W_16_ok face3_P_16_ok face3_autos_16_ok face3_bk_16_init_ok face3_chk_16_0
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face3_chk_16_1 : checkNodes face3_W_16 face3_G_16 face2_fmask_12 face3_P_16 face3_autos_16 face3_bk_16_0 1 face0_nodes_0_0 = true := by decide +kernel
lemma face3_bk_16_1_ok : ∀ i (hi : i < face3_bk_16_0.size), ∀ xs ∈ face3_bk_16_0[i], Impossible face3_G_16 1 xs.toFinset :=
  buildBuckets_sound (by decide) face3_gp_16 face3_W_16_ok face3_P_16_ok face3_autos_16_ok face3_bk_16_0_ok face3_chk_16_1
def face3_nodes_16_2 : List NodeSpec := [([18,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face3_chk_16_2 : checkNodes face3_W_16 face3_G_16 face2_fmask_12 face3_P_16 face3_autos_16 face3_bk_16_0 2 face3_nodes_16_2 = true := by decide +kernel
def face3_bk_16_2 : Array (List (List Nat)) := buildBuckets 1 face3_W_16 face3_nodes_16_2
lemma face3_bk_16_2_ok : ∀ i (hi : i < face3_bk_16_2.size), ∀ xs ∈ face3_bk_16_2[i], Impossible face3_G_16 2 xs.toFinset :=
  buildBuckets_sound (by decide) face3_gp_16 face3_W_16_ok face3_P_16_ok face3_autos_16_ok face3_bk_16_1_ok face3_chk_16_2
def face3_nodes_16_3 : List NodeSpec := [([5,4,1,2],[],[]),([11,0,2,3],[],[]),([0,12,2,3],[],[]),([0,13,2,3],[],[]),([7,14,2,3],[],[0]),([0,1,15,3],[],[]),([0,1,16,3],[],[]),([17,0,2,3],[],[]),([10,8,2,3],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face3_chk_16_3 : checkNodes face3_W_16 face3_G_16 face2_fmask_12 face3_P_16 face3_autos_16 face3_bk_16_2 3 face3_nodes_16_3 = true := by decide +kernel
def face3_bk_16_3 : Array (List (List Nat)) := buildBuckets 4 face3_W_16 face3_nodes_16_3
lemma face3_bk_16_3_ok : ∀ i (hi : i < face3_bk_16_3.size), ∀ xs ∈ face3_bk_16_3[i], Impossible face3_G_16 3 xs.toFinset :=
  buildBuckets_sound (by decide) face3_gp_16 face3_W_16_ok face3_P_16_ok face3_autos_16_ok face3_bk_16_2_ok face3_chk_16_3
def face3_nodes_16_4 : List NodeSpec := [([4,0,1,2,3],[],[0]),([5,0,1,2,3],[],[0]),([6,0,1,2,3],[],[0,1]),([7,0,1,2,3],[],[0]),([0,1,8,2,3],[],[0]),([0,1,2,3,9],[],[0,1]),([10,0,1,2,3],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face3_chk_16_4 : checkNodes face3_W_16 face3_G_16 face2_fmask_12 face3_P_16 face3_autos_16 face3_bk_16_3 4 face3_nodes_16_4 = true := by decide +kernel
def face3_bk_16_4 : Array (List (List Nat)) := buildBuckets 3 face3_W_16 face3_nodes_16_4
lemma face3_bk_16_4_ok : ∀ i (hi : i < face3_bk_16_4.size), ∀ xs ∈ face3_bk_16_4[i], Impossible face3_G_16 4 xs.toFinset :=
  buildBuckets_sound (by decide) face3_gp_16 face3_W_16_ok face3_P_16_ok face3_autos_16_ok face3_bk_16_3_ok face3_chk_16_4
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face3_chk_16_5 : checkNodes face3_W_16 face3_G_16 face2_fmask_12 face3_P_16 face3_autos_16 face3_bk_16_4 5 face2_nodes_12_5 = true := by decide +kernel
def face3_bk_16_5 : Array (List (List Nat)) := buildBuckets 1 face3_W_16 face2_nodes_12_5
lemma face3_bk_16_5_ok : ∀ i (hi : i < face3_bk_16_5.size), ∀ xs ∈ face3_bk_16_5[i], Impossible face3_G_16 5 xs.toFinset :=
  buildBuckets_sound (by decide) face3_gp_16 face3_W_16_ok face3_P_16_ok face3_autos_16_ok face3_bk_16_4_ok face3_chk_16_5
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face3_forestRoot_16_ok : forestRootCheck face0_R_31 face3_G_16 [(VAR 1,14,12),(VAR 2,14,10),(VAR 3,14,6),(VAR 4,18,2)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face3_forestRoot_16_in : bucketContains face3_bk_16_5 face0_R_31 = true := by decide +kernel
lemma face3_low_16 : Lower face0_R_31 face3_G_16 6 := lower_of_forest face3_forestRoot_16_ok face3_bk_16_5_ok face3_forestRoot_16_in
def face3_G_26 : Nat := 0xfe80fe80fe80fe80fe80fe80fe80fe80
def face3_R_26 : List Nat := varsOf 15
lemma face3_low_26_ok : carryOK [(0,4),(0,3),(0,2),(0,1)] face3_R_26 face3_G_26 face0_R_31 face3_G_16 = true := by decide +kernel
lemma face3_low_26 : Lower face3_R_26 face3_G_26 6 := carry_of face3_low_26_ok face3_low_16
def face3_G_28 : Nat := 0xfefefefe80808080fefefefe80808080
lemma face3_low_28_ok : carryOK [(4,5),(0,3),(0,2),(0,1)] face1_R_19 face3_G_28 face0_R_31 face3_G_16 = true := by decide +kernel
lemma face3_low_28 : Lower face1_R_19 face3_G_28 6 := carry_of face3_low_28_ok face3_low_16
def face3_G_29 : Nat := 0xff88ff8888008800ff88ff8888008800
def face3_R_29 : List Nat := varsOf 43
lemma face3_low_29_ok : carryOK [(0,2),(0,1)] face3_R_29 face3_G_29 face0_R_32 face3_G_14 = true := by decide +kernel
lemma face3_low_29 : Lower face3_R_29 face3_G_29 5 := carry_of face3_low_29_ok face3_low_14
def face3_G_30 : Nat := 0xffa0ffa0a000a000ffa0ffa0a000a000
def face3_R_30 : List Nat := varsOf 45
lemma face3_low_30_ok : carryOK [(0,1)] face3_R_30 face3_G_30 face0_R_32 face3_G_14 = true := by decide +kernel
lemma face3_low_30 : Lower face3_R_30 face3_G_30 5 := carry_of face3_low_30_ok face3_low_14
def face3_G_41 : Nat := 0xfe80fe8080008000fe80fe8080008000
def face3_R_41 : List Nat := varsOf 47
def face3_pos_41 : List Nat := [15,15,15,15,39,39,39,39,41,41,41,42,42,42,43,43,44,44,44,45,45,46,46,15,15,15,15,39,39,39,39,41,41,41,41,41,41,41,42,42,42,42,42,42,42,44,44,44,44,44,44,44]
def face3_neg_41 : List Nat := [14,13,11,7,38,37,35,7,40,33,9,40,34,10,35,11,40,36,12,37,13,38,14,35,37,38,40,11,13,14,40,7,11,13,14,35,37,38,7,11,13,14,35,37,38,7,11,13,14,35,37,38]
def face3_fmask_41 : Nat := fullMask 52
def face3_base_41 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x3fff98c7ff,0x6eddb9998c6ee),(0xcccccccccccccccccccccccccccccccc,0x1fc07fe0f8ff,0xb76edaae0f0dd),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfe0007fff00ff,0xdbb76b37e00bb),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xfffff87ffff0f,0x1c3877c55ad07),(0xffffffff00000000ffffffff00000000,0xffffff87ffff0,0xe1c3847ab5b70)]
def face3_steps_41 : List (Nat × Nat × Nat) := [(0,3,4),(0,0,3),(3,0,3),(2,0,1),(1,0,1),(0,0,1),(2,0,5),(1,0,5),(0,0,5),(3,7,4),(3,0,4),(3,6,4),(0,1,4),(3,6,1),(0,2,3),(0,0,4),(3,8,3),(3,8,2),(1,8,2),(0,1,3),(3,0,5),(0,9,3),(3,0,1),(0,6,1),(0,10,2),(3,25,3),(1,13,1),(3,13,1),(3,13,3),(3,28,2),(3,18,4),(3,18,2),(3,28,0),(3,24,4),(0,24,4),(2,10,19),(0,26,4),(0,21,4),(2,9,5),(3,11,1),(3,16,1),(2,0,19),(1,6,17),(3,1,12),(0,29,3),(3,28,4),(1,15,6),(3,10,9),(3,21,4),(3,26,4),(2,10,5),(1,8,24),(3,29,3),(1,8,5),(0,18,4),(0,1,12),(0,28,4),(3,44,2),(3,13,2),(3,13,12),(3,61,0),(3,11,9),(3,61,2),(3,41,2),(3,49,4),(3,55,9)]
def face3_W_41 : Array Decor := buildWires face3_base_41 face3_steps_41
def face3_autos_41 : Array (List (Nat × Nat)) := #[[],[(0,1)],[(0,2),(0,1)],[(1,2)],[(3,5)],[(3,5),(1,2)],[(3,5),(0,1)],[(0,1),(0,2)],[(3,5),(0,2),(0,1)],[(0,2)]]
def face3_slicesL_41 : List (Nat × Nat) := [(subcube 0 3,4),(subcube 0 5,4),(subcube 0 6,4),(subcube 0 8,6),(subcube 0 32,6),(subcube 0 2,5),(subcube 0 4,5),(subcube 0 1,5)]
def face3_slices_41 : Array (Nat × Nat) := face3_slicesL_41.toArray
def face3_ps_41 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(3,[(0,0,1),(1,0,1),(3,10,9)]),(3,[(2,0,5),(3,0,5)]),(5,[]),(6,[]),(3,[(0,0,5),(1,13,1)]),(7,[]),(4,[(0,0,3),(3,6,1)]),(3,[(2,0,1),(3,0,1)]),(3,[(2,0,1),(3,8,2)]),(3,[(0,0,5),(3,13,1)]),(3,[(0,0,1),(1,0,1)]),(3,[(1,0,5),(3,1,12)]),(3,[(2,0,1),(1,8,2)]),(4,[(0,0,1),(1,0,1),(3,10,9)]),(3,[(1,0,5),(0,1,12)]),(3,[(2,0,5)]),(4,[(2,0,5)]),(3,[(1,0,5)]),(3,[(0,0,5)]),(3,[(3,7,4)]),(4,[(0,0,3)]),(3,[(0,0,1)]),(3,[(3,6,4)]),(3,[(0,6,4)]),(3,[(3,6,1)]),(3,[(2,0,1)]),(3,[(0,0,4)]),(4,[(2,0,1),(3,8,2)]),(4,[(2,0,1),(1,8,2)]),(3,[(3,0,5)]),(3,[(1,0,1)]),(4,[(2,0,1),(3,0,1)]),(4,[(0,0,1),(1,0,1)]),(4,[(2,0,1)]),(4,[(1,0,1)]),(4,[(0,0,1)])]
def face3_P_41 : Array (Option BoundPool) := buildPools face3_W_41 face3_R_41 face3_slices_41 face3_ps_41
lemma face3_gp_41 : goodPairs face3_G_41 face3_pos_41 face3_neg_41 := goodPairs_of (by decide +kernel)
lemma face3_base_41_ok : ∀ x ∈ face3_base_41, faithful face3_pos_41 face3_neg_41 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma face3_W_41_ok : ∀ x ∈ face3_W_41.toList, faithful face3_pos_41 face3_neg_41 x ∧ x.1 < 2^128 := buildWires_faithful face3_base_41_ok
lemma face3_autos_41_ok : ∀ sw ∈ face3_autos_41.toList, swapsValid sw = true ∧ permWord sw face3_G_41 = face3_G_41 := autos_of (by decide +kernel)
lemma face3_sl_41_0_ok : sliceDirectCheck 0 3 0 face3_R_41 face3_G_41 face0_R_15 face0_G_15 = true := by decide +kernel
lemma face3_sl_41_0 : Slice face3_R_41 face3_G_41 (subcube 0 3) 4 := slice_direct face3_sl_41_0_ok face3_low_9
lemma face3_sl_41_1_ok : sliceDirectCheck 0 5 0 face3_R_41 face3_G_41 face0_R_13 face0_G_13 = true := by decide +kernel
lemma face3_sl_41_1 : Slice face3_R_41 face3_G_41 (subcube 0 5) 4 := slice_direct face3_sl_41_1_ok face3_low_8
lemma face3_sl_41_2_ok : sliceDirectCheck 0 6 0 face3_R_41 face3_G_41 face3_R_7 face3_G_7 = true := by decide +kernel
lemma face3_sl_41_2 : Slice face3_R_41 face3_G_41 (subcube 0 6) 4 := slice_direct face3_sl_41_2_ok face3_low_7
lemma face3_sl_41_3_ok : sliceDirectCheck 0 8 0 face3_R_41 face3_G_41 face1_R_19 face3_G_28 = true := by decide +kernel
lemma face3_sl_41_3 : Slice face3_R_41 face3_G_41 (subcube 0 8) 6 := slice_direct face3_sl_41_3_ok face3_low_28
lemma face3_sl_41_4_ok : sliceDirectCheck 0 32 0 face3_R_41 face3_G_41 face3_R_26 face3_G_26 = true := by decide +kernel
lemma face3_sl_41_4 : Slice face3_R_41 face3_G_41 (subcube 0 32) 6 := slice_direct face3_sl_41_4_ok face3_low_26
lemma face3_sl_41_5_ok : sliceDirectCheck 0 2 0 face3_R_41 face3_G_41 face3_R_30 face3_G_30 = true := by decide +kernel
lemma face3_sl_41_5 : Slice face3_R_41 face3_G_41 (subcube 0 2) 5 := slice_direct face3_sl_41_5_ok face3_low_30
lemma face3_sl_41_6_ok : sliceDirectCheck 0 4 0 face3_R_41 face3_G_41 face3_R_29 face3_G_29 = true := by decide +kernel
lemma face3_sl_41_6 : Slice face3_R_41 face3_G_41 (subcube 0 4) 5 := slice_direct face3_sl_41_6_ok face3_low_29
lemma face3_sl_41_7_ok : sliceDirectCheck 0 1 0 face3_R_41 face3_G_41 face0_R_32 face3_G_14 = true := by decide +kernel
lemma face3_sl_41_7 : Slice face3_R_41 face3_G_41 (subcube 0 1) 5 := slice_direct face3_sl_41_7_ok face3_low_14
set_option maxRecDepth 200000 in
lemma face3_slices_41_ok : ∀ i (hi : i < face3_slices_41.size), Slice face3_R_41 face3_G_41 face3_slices_41[i].1 face3_slices_41[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice face3_R_41 face3_G_41 p.1 p.2) (forall_cons face3_sl_41_0 (forall_cons face3_sl_41_1 (forall_cons face3_sl_41_2 (forall_cons face3_sl_41_3 (forall_cons face3_sl_41_4 (forall_cons face3_sl_41_5 (forall_cons face3_sl_41_6 (forall_cons face3_sl_41_7 (fun _ h => (List.not_mem_nil h).elim)))))))))
lemma face3_P_41_ok : ∀ i (hi : i < face3_P_41.size), ∀ c, face3_P_41[i] = some c → ValidPool face3_R_41 face3_G_41 c := buildPools_sound face3_slices_41_ok
lemma face3_bk_41_init_ok : ∀ i (hi : i < face0_bk_0_init.size), ∀ xs ∈ face0_bk_0_init[i], Impossible face3_G_41 (0 - 1) xs.toFinset := by intro i hi; simp [face0_bk_0_init] at hi
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face3_chk_41_0 : checkNodes face3_W_41 face3_G_41 face3_fmask_41 face3_P_41 face3_autos_41 face0_bk_0_init 0 face0_nodes_0_0 = true := by decide +kernel
def face3_bk_41_0 : Array (List (List Nat)) := buildBuckets 1 face3_W_41 face0_nodes_0_0
lemma face3_bk_41_0_ok : ∀ i (hi : i < face3_bk_41_0.size), ∀ xs ∈ face3_bk_41_0[i], Impossible face3_G_41 0 xs.toFinset :=
  buildBuckets_sound (by decide) face3_gp_41 face3_W_41_ok face3_P_41_ok face3_autos_41_ok face3_bk_41_init_ok face3_chk_41_0
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face3_chk_41_1 : checkNodes face3_W_41 face3_G_41 face3_fmask_41 face3_P_41 face3_autos_41 face3_bk_41_0 1 face0_nodes_0_0 = true := by decide +kernel
lemma face3_bk_41_1_ok : ∀ i (hi : i < face3_bk_41_0.size), ∀ xs ∈ face3_bk_41_0[i], Impossible face3_G_41 1 xs.toFinset :=
  buildBuckets_sound (by decide) face3_gp_41 face3_W_41_ok face3_P_41_ok face3_autos_41_ok face3_bk_41_0_ok face3_chk_41_1
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face3_chk_41_2 : checkNodes face3_W_41 face3_G_41 face3_fmask_41 face3_P_41 face3_autos_41 face3_bk_41_0 2 face0_nodes_0_0 = true := by decide +kernel
lemma face3_bk_41_2_ok : ∀ i (hi : i < face3_bk_41_0.size), ∀ xs ∈ face3_bk_41_0[i], Impossible face3_G_41 2 xs.toFinset :=
  buildBuckets_sound (by decide) face3_gp_41 face3_W_41_ok face3_P_41_ok face3_autos_41_ok face3_bk_41_1_ok face3_chk_41_2
def face3_nodes_41_3 : List NodeSpec := [([10,47,2,5],[],[]),([70,2,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face3_chk_41_3 : checkNodes face3_W_41 face3_G_41 face3_fmask_41 face3_P_41 face3_autos_41 face3_bk_41_0 3 face3_nodes_41_3 = true := by decide +kernel
def face3_bk_41_3 : Array (List (List Nat)) := buildBuckets 1 face3_W_41 face3_nodes_41_3
lemma face3_bk_41_3_ok : ∀ i (hi : i < face3_bk_41_3.size), ∀ xs ∈ face3_bk_41_3[i], Impossible face3_G_41 3 xs.toFinset :=
  buildBuckets_sound (by decide) face3_gp_41 face3_W_41_ok face3_P_41_ok face3_autos_41_ok face3_bk_41_2_ok face3_chk_41_3
def face3_nodes_41_4 : List NodeSpec := [([62,0,1,3,4],[],[]),([13,60,2,3,4],[0,1],[]),([6,60,2,5,4],[],[]),([33,16,0,1,2],[],[]),([32,63,0,3,4],[],[]),([11,33,1,2,4],[],[]),([0,24,22,5,4],[],[]),([11,1,23,3,4],[],[]),([38,0,22,3,4],[],[]),([64,1,2,3,4],[],[]),([0,39,22,3,4],[0,2],[]),([11,31,2,3,4],[],[]),([65,1,2,3,4],[],[]),([0,17,21,2,5],[],[]),([1,66,2,3,4],[],[]),([18,20,1,2,5],[],[]),([10,26,2,5,4],[0],[]),([10,6,17,2,5],[],[0]),([63,0,31,3,4],[],[]),([55,9,2,3,4],[],[0]),([67,0,1,3,4],[],[]),([8,44,2,3,4],[],[0]),([11,1,21,2,4],[],[]),([0,1,47,2,5],[3,4],[0]),([54,10,2,3,4],[],[]),([10,41,2,3,4],[0,2],[]),([52,2,5,3,4],[5],[]),([28,20,1,2,5],[4],[]),([10,47,2,3,4],[],[0]),([37,18,2,3,4],[],[]),([68,0,1,3,4],[],[]),([69,0,1,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face3_chk_41_4 : checkNodes face3_W_41 face3_G_41 face3_fmask_41 face3_P_41 face3_autos_41 face3_bk_41_3 4 face3_nodes_41_4 = true := by decide +kernel
def face3_bk_41_4 : Array (List (List Nat)) := buildBuckets 11 face3_W_41 face3_nodes_41_4
lemma face3_bk_41_4_ok : ∀ i (hi : i < face3_bk_41_4.size), ∀ xs ∈ face3_bk_41_4[i], Impossible face3_G_41 4 xs.toFinset :=
  buildBuckets_sound (by decide) face3_gp_41 face3_W_41_ok face3_P_41_ok face3_autos_41_ok face3_bk_41_3_ok face3_chk_41_4
def face3_nd_41_5_0 : List NodeSpec := [([30,0,1,2,5,4],[3],[]),([11,25,1,2,3,4],[6],[0]),([13,0,1,2,3,4],[7,8],[1,2]),([13,1,2,3,12,4],[0,1],[0,3]),([0,31,2,5,3,4],[0,9],[0]),([11,6,1,2,5,4],[3],[]),([6,1,2,5,12,4],[3],[0,3]),([6,0,17,1,2,5],[],[0,1,4]),([6,20,0,1,2,5],[3,4,10],[]),([6,20,1,2,5],[3,4,10],[0,3,4,5]),([16,6,0,1,2,5],[4,3],[]),([16,6,20,1,2,3],[10],[]),([32,6,0,2,3,4],[],[]),([11,6,1,2,3,4],[3],[4]),([33,13,0,1,2,4],[3],[0]),([32,13,0,2,3,4],[7],[3]),([13,0,31,2,3,4],[2],[0,1]),([34,0,1,2,3,4],[],[]),([11,0,1,2,3,4],[],[]),([28,0,1,2,5,4],[4],[0,1]),([0,35,1,2,3,4],[11],[1]),([0,36,1,2,3,4],[10],[]),([11,8,1,2,3,4],[],[0,4]),([32,0,2,3,4],[],[]),([37,28,1,2,3,4],[3,0],[0]),([8,38,0,2,3,4],[],[0]),([8,0,39,2,3,4],[10,2],[1,0]),([8,27,2,5,3,4],[12],[0]),([40,0,1,2,3,4],[],[]),([10,13,1,2,3,4],[7,2],[]),([0,1,41,2,3,4],[10,7,8],[0]),([11,13,1,2,3,4],[3],[0,3,4]),([0,1,21,2,5,4],[4],[0]),([8,0,24,2,5,4],[],[0,4]),([0,1,42,2,3,4],[],[0]),([33,0,1,2,5,4],[3],[0]),([0,1,22,5,3,4],[7,13],[0,4]),([43,0,1,2,3,4],[],[]),([18,0,1,2,5,4],[4,11],[0]),([37,6,1,2,3,4],[3],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face3_chk_41_5_0 : checkNodes face3_W_41 face3_G_41 face3_fmask_41 face3_P_41 face3_autos_41 face3_bk_41_4 5 face3_nd_41_5_0 = true := by decide +kernel
def face3_nd_41_5_1 : List NodeSpec := [([0,24,22,3,4],[0,2,13],[0]),([11,1,9,2,3,4],[],[0]),([0,44,1,2,3,4],[8],[0]),([18,20,1,2,3,4],[],[0]),([32,0,2,5,3,4],[14],[]),([10,6,17,2,3,4],[],[0]),([10,6,1,2,5,4],[],[4,0]),([16,10,1,2,3,4],[7],[]),([18,10,6,2,3,4],[7],[]),([45,0,1,2,3,4],[],[]),([46,10,1,2,3,4],[7],[]),([0,1,47,2,3,4],[3,4],[0]),([10,9,2,5,3,4],[0,15],[0,4]),([48,0,2,5,3,4],[16],[]),([49,0,1,2,3,4],[4],[0]),([32,0,1,2,3,4],[],[]),([50,0,1,2,3,4],[],[]),([10,26,2,3,4],[0,2,15],[0]),([6,1,2,3,51,4],[10],[]),([0,1,23,5,3,4],[0,17],[0]),([28,20,1,2,3,4],[4],[0]),([33,6,0,1,2,4],[3],[0]),([0,1,26,2,5,4],[4],[0]),([52,2,3,4],[0,2,5,18],[0]),([53,0,1,2,3,4],[],[]),([54,0,1,2,3,4],[],[0]),([55,0,1,2,3,4],[],[0]),([29,6,1,2,3,4],[3,0,2],[]),([0,24,56,2,3,4],[7],[]),([0,17,21,2,3,4],[],[0]),([57,0,1,2,3,4],[],[]),([0,1,2,3,58,4],[10],[]),([59,0,1,2,3,4],[],[]),([0,60,2,5,3,4],[10,19],[0,4]),([61,0,1,2,3,4],[8],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face3_chk_41_5_1 : checkNodes face3_W_41 face3_G_41 face3_fmask_41 face3_P_41 face3_autos_41 face3_bk_41_4 5 face3_nd_41_5_1 = true := by decide +kernel
def face3_nodes_41_5 : List NodeSpec := face3_nd_41_5_0 ++ face3_nd_41_5_1
lemma face3_chk_41_5 : checkNodes face3_W_41 face3_G_41 face3_fmask_41 face3_P_41 face3_autos_41 face3_bk_41_4 5 face3_nodes_41_5 = true := by
  unfold face3_nodes_41_5 checkNodes
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨face3_chk_41_5_0, face3_chk_41_5_1⟩
def face3_bk_41_5 : Array (List (List Nat)) := buildBuckets 26 face3_W_41 face3_nodes_41_5
lemma face3_bk_41_5_ok : ∀ i (hi : i < face3_bk_41_5.size), ∀ xs ∈ face3_bk_41_5[i], Impossible face3_G_41 5 xs.toFinset :=
  buildBuckets_sound (by decide) face3_gp_41 face3_W_41_ok face3_P_41_ok face3_autos_41_ok face3_bk_41_4_ok face3_chk_41_5
def face3_nodes_41_6 : List NodeSpec := [([11,0,1,2,5,3,4],[10,4,3,20],[0,4]),([11,0,1,2,3,4],[7,8,4,3,20,21],[0,3,4]),([0,1,2,5,3,12,4],[10,4,3,22],[0,4,3]),([13,0,1,2,5,3,4],[10,23],[0,3,4]),([0,14,1,2,3,4],[4,3,0,1,24],[]),([6,0,1,2,5,4],[3,4,10,25],[0,3,1,2]),([15,6,1,2,3,4],[10,0,1,3,25],[0]),([10,6,1,2,3,4],[3,7,10,0,2,1,26],[0,4]),([16,0,1,2,3,4],[3,4,7,8,10,25,27],[0,3,4,1,2]),([6,0,17,1,2,3,4],[7,10],[0,6,1,4]),([16,6,0,1,2,3,4],[4,3,10,25],[4,0]),([13,6,0,1,2,3,4],[4,0,1,25],[0,3,4]),([13,0,1,2,3,4],[7,8,28,25],[0,3,4,1,2]),([18,6,0,1,2,3,4],[7,3,10,0],[1,0]),([18,0,1,2,3,4],[3,10,0,8,4,11,29],[1,7,0]),([10,0,1,19,2,3,4],[0,8,2,1],[0,2,1]),([8,0,1,2,5,3,4],[7,3,4,10,30],[0,4]),([6,20,1,2,3,4],[3,4,10,25,31],[0,3,4,5]),([10,0,1,2,5,3,4],[0,3,4,26],[0,4,1,6]),([0,1,21,2,3,4],[7,0,2,4,30],[0]),([0,1,22,3,4],[7,0,2,13,32],[0,4]),([0,1,23,3,4],[7,8,0,17,33],[0]),([8,0,24,2,3,4],[7,0,2,3,30],[0,4]),([25,0,1,2,5,3,4],[10,34],[0,4]),([0,1,9,2,5,3,4],[10,7,3,4,35],[0,1,4]),([0,1,26,2,3,4],[10,7,2,4,35],[0]),([8,27,2,3,4],[7,10,2,12,36],[0]),([10,9,2,3,4],[0,2,15,37],[0,4]),([28,6,0,1,2,3,4],[7,0],[0,1]),([28,0,1,2,3,4],[0,8,4,26],[0,1]),([6,20,0,1,2,3,4],[31,4,10],[4,0]),([29,0,1,2,3,4],[2,1,0,3,4],[0,4,1,6,2,8])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face3_chk_41_6 : checkNodes face3_W_41 face3_G_41 face3_fmask_41 face3_P_41 face3_autos_41 face3_bk_41_5 6 face3_nodes_41_6 = true := by decide +kernel
def face3_bk_41_6 : Array (List (List Nat)) := buildBuckets 11 face3_W_41 face3_nodes_41_6
lemma face3_bk_41_6_ok : ∀ i (hi : i < face3_bk_41_6.size), ∀ xs ∈ face3_bk_41_6[i], Impossible face3_G_41 6 xs.toFinset :=
  buildBuckets_sound (by decide) face3_gp_41 face3_W_41_ok face3_P_41_ok face3_autos_41_ok face3_bk_41_5_ok face3_chk_41_6
def face3_nodes_41_7 : List NodeSpec := [([0,1,2,5,3,4],[10,3,4,7,8],[0,1,3,2,4,7,9,6,8]),([6,0,1,2,3,4],[3,7,0,8,1,4,25],[0,3,1,2,7]),([7,0,1,2,3,4],[3,10,7,0,8,1,4],[0,4]),([8,0,1,2,3,4],[7,0,8,2,3,4,30,38],[0,4]),([0,1,9,2,3,4],[10,7,2,3,4,35,39],[0,4]),([10,0,1,2,3,4],[7,10,0,8,3,4,2,1,26,40],[0,4,1,6])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face3_chk_41_7 : checkNodes face3_W_41 face3_G_41 face3_fmask_41 face3_P_41 face3_autos_41 face3_bk_41_6 7 face3_nodes_41_7 = true := by decide +kernel
def face3_bk_41_7 : Array (List (List Nat)) := buildBuckets 3 face3_W_41 face3_nodes_41_7
lemma face3_bk_41_7_ok : ∀ i (hi : i < face3_bk_41_7.size), ∀ xs ∈ face3_bk_41_7[i], Impossible face3_G_41 7 xs.toFinset :=
  buildBuckets_sound (by decide) face3_gp_41 face3_W_41_ok face3_P_41_ok face3_autos_41_ok face3_bk_41_6_ok face3_chk_41_7
def face3_nodes_41_8 : List NodeSpec := [([0,1,2,3,4],[3,4],[0,1,3,2,4,7,9,6,8])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face3_chk_41_8 : checkNodes face3_W_41 face3_G_41 face3_fmask_41 face3_P_41 face3_autos_41 face3_bk_41_7 8 face3_nodes_41_8 = true := by decide +kernel
def face3_bk_41_8 : Array (List (List Nat)) := buildBuckets 1 face3_W_41 face3_nodes_41_8
lemma face3_bk_41_8_ok : ∀ i (hi : i < face3_bk_41_8.size), ∀ xs ∈ face3_bk_41_8[i], Impossible face3_G_41 8 xs.toFinset :=
  buildBuckets_sound (by decide) face3_gp_41 face3_W_41_ok face3_P_41_ok face3_autos_41_ok face3_bk_41_7_ok face3_chk_41_8
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face3_forestRoot_41_ok : forestRootCheck face3_R_41 face3_G_41 [(VAR 0,15,14),(VAR 1,15,13),(VAR 2,15,11),(VAR 3,15,7),(VAR 5,39,7)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face3_forestRoot_41_in : bucketContains face3_bk_41_8 face3_R_41 = true := by decide +kernel
lemma face3_low_41 : Lower face3_R_41 face3_G_41 9 := lower_of_forest face3_forestRoot_41_ok face3_bk_41_8_ok face3_forestRoot_41_in
def face6_pos_8 : List Nat := [10,10,12,12,14,22,22,22,24,24,26,28,10,10,10,12,12,12,22,24,24,24]
def face6_neg_8 : List Nat := [8,2,8,4,6,20,18,6,16,8,18,20,6,18,20,6,18,20,8,6,18,20]
def face6_base_8 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0x474f3,0x19b4d2),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x788fc,0x2ad8b8),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x3bff1f,0x40205),(0xffff0000ffff0000ffff0000ffff0000,0x3c0fe0,0x336d60)]
def face6_steps_8 : List (Nat × Nat × Nat) := [(3,0,2),(2,0,1),(2,0,2),(1,0,2),(1,0,1),(0,0,2),(0,0,1),(0,1,7),(3,0,1),(1,5,3),(1,9,1),(3,5,3),(3,1,7),(3,9,1),(3,10,8)]
def face6_W_8 : Array Decor := buildWires face6_base_8 face6_steps_8
def face6_autos_8 : Array (List (Nat × Nat)) := #[[],[(2,4)],[(1,2)],[(1,4),(1,2)],[(1,2),(1,4)],[(1,4)]]
def face6_P_8 : Array (Option BoundPool) := buildPools face6_W_8 face0_R_31 face0_slices_0 face0_ps_0
lemma face6_gp_8 : goodPairs face2_G_35 face6_pos_8 face6_neg_8 := goodPairs_of (by decide +kernel)
lemma face6_base_8_ok : ∀ x ∈ face6_base_8, faithful face6_pos_8 face6_neg_8 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma face6_W_8_ok : ∀ x ∈ face6_W_8.toList, faithful face6_pos_8 face6_neg_8 x ∧ x.1 < 2^128 := buildWires_faithful face6_base_8_ok
lemma face6_autos_8_ok : ∀ sw ∈ face6_autos_8.toList, swapsValid sw = true ∧ permWord sw face2_G_35 = face2_G_35 := autos_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma face6_slices_8_ok : ∀ i (hi : i < face0_slices_0.size), Slice face0_R_31 face2_G_35 face0_slices_0[i].1 face0_slices_0[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice face0_R_31 face2_G_35 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma face6_P_8_ok : ∀ i (hi : i < face6_P_8.size), ∀ c, face6_P_8[i] = some c → ValidPool face0_R_31 face2_G_35 c := buildPools_sound face6_slices_8_ok
lemma face6_bk_8_init_ok : ∀ i (hi : i < face0_bk_0_init.size), ∀ xs ∈ face0_bk_0_init[i], Impossible face2_G_35 (0 - 1) xs.toFinset := by intro i hi; simp [face0_bk_0_init] at hi
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face6_chk_8_0 : checkNodes face6_W_8 face2_G_35 face2_fmask_12 face6_P_8 face6_autos_8 face0_bk_0_init 0 face0_nodes_0_0 = true := by decide +kernel
def face6_bk_8_0 : Array (List (List Nat)) := buildBuckets 1 face6_W_8 face0_nodes_0_0
lemma face6_bk_8_0_ok : ∀ i (hi : i < face6_bk_8_0.size), ∀ xs ∈ face6_bk_8_0[i], Impossible face2_G_35 0 xs.toFinset :=
  buildBuckets_sound (by decide) face6_gp_8 face6_W_8_ok face6_P_8_ok face6_autos_8_ok face6_bk_8_init_ok face6_chk_8_0
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face6_chk_8_1 : checkNodes face6_W_8 face2_G_35 face2_fmask_12 face6_P_8 face6_autos_8 face6_bk_8_0 1 face0_nodes_0_0 = true := by decide +kernel
lemma face6_bk_8_1_ok : ∀ i (hi : i < face6_bk_8_0.size), ∀ xs ∈ face6_bk_8_0[i], Impossible face2_G_35 1 xs.toFinset :=
  buildBuckets_sound (by decide) face6_gp_8 face6_W_8_ok face6_P_8_ok face6_autos_8_ok face6_bk_8_0_ok face6_chk_8_1
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face6_chk_8_2 : checkNodes face6_W_8 face2_G_35 face2_fmask_12 face6_P_8 face6_autos_8 face6_bk_8_0 2 face3_nodes_16_2 = true := by decide +kernel
def face6_bk_8_2 : Array (List (List Nat)) := buildBuckets 1 face6_W_8 face3_nodes_16_2
lemma face6_bk_8_2_ok : ∀ i (hi : i < face6_bk_8_2.size), ∀ xs ∈ face6_bk_8_2[i], Impossible face2_G_35 2 xs.toFinset :=
  buildBuckets_sound (by decide) face6_gp_8 face6_W_8_ok face6_P_8_ok face6_autos_8_ok face6_bk_8_1_ok face6_chk_8_2
def face6_nodes_8_3 : List NodeSpec := [([6,4,1,3],[],[]),([0,11,2,3],[],[]),([5,12,2,3],[],[0]),([0,1,2,13],[],[]),([0,14,2,3],[],[]),([0,1,15,2],[],[]),([16,0,2,3],[],[]),([17,0,2,3],[],[]),([10,8,2,3],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face6_chk_8_3 : checkNodes face6_W_8 face2_G_35 face2_fmask_12 face6_P_8 face6_autos_8 face6_bk_8_2 3 face6_nodes_8_3 = true := by decide +kernel
def face6_bk_8_3 : Array (List (List Nat)) := buildBuckets 4 face6_W_8 face6_nodes_8_3
lemma face6_bk_8_3_ok : ∀ i (hi : i < face6_bk_8_3.size), ∀ xs ∈ face6_bk_8_3[i], Impossible face2_G_35 3 xs.toFinset :=
  buildBuckets_sound (by decide) face6_gp_8 face6_W_8_ok face6_P_8_ok face6_autos_8_ok face6_bk_8_2_ok face6_chk_8_3
def face6_nodes_8_4 : List NodeSpec := [([4,0,1,2,3],[],[0]),([5,0,1,2,3],[],[0]),([6,0,1,2,3],[],[0]),([0,1,2,7,3],[],[0,1]),([0,1,8,2,3],[],[0]),([9,0,1,2,3],[],[0,1]),([10,0,1,2,3],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face6_chk_8_4 : checkNodes face6_W_8 face2_G_35 face2_fmask_12 face6_P_8 face6_autos_8 face6_bk_8_3 4 face6_nodes_8_4 = true := by decide +kernel
def face6_bk_8_4 : Array (List (List Nat)) := buildBuckets 3 face6_W_8 face6_nodes_8_4
lemma face6_bk_8_4_ok : ∀ i (hi : i < face6_bk_8_4.size), ∀ xs ∈ face6_bk_8_4[i], Impossible face2_G_35 4 xs.toFinset :=
  buildBuckets_sound (by decide) face6_gp_8 face6_W_8_ok face6_P_8_ok face6_autos_8_ok face6_bk_8_3_ok face6_chk_8_4
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face6_chk_8_5 : checkNodes face6_W_8 face2_G_35 face2_fmask_12 face6_P_8 face6_autos_8 face6_bk_8_4 5 face2_nodes_12_5 = true := by decide +kernel
def face6_bk_8_5 : Array (List (List Nat)) := buildBuckets 1 face6_W_8 face2_nodes_12_5
lemma face6_bk_8_5_ok : ∀ i (hi : i < face6_bk_8_5.size), ∀ xs ∈ face6_bk_8_5[i], Impossible face2_G_35 5 xs.toFinset :=
  buildBuckets_sound (by decide) face6_gp_8 face6_W_8_ok face6_P_8_ok face6_autos_8_ok face6_bk_8_4_ok face6_chk_8_5
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face6_forestRoot_8_ok : forestRootCheck face0_R_31 face2_G_35 [(VAR 1,10,8),(VAR 2,12,8),(VAR 3,10,2),(VAR 4,22,6)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face6_forestRoot_8_in : bucketContains face6_bk_8_5 face0_R_31 = true := by decide +kernel
lemma face6_low_8 : Lower face0_R_31 face2_G_35 6 := lower_of_forest face6_forestRoot_8_ok face6_bk_8_5_ok face6_forestRoot_8_in
lemma face7_low_0 : Lower face0_R_7 face0_G_7 4 := lower_of_forest face3_forestRoot_0_ok face3_bk_0_3_ok face3_forestRoot_0_in

def h0R : List Nat := varsOf 63
def h0G : Nat := 0xfee8e888e8888880fee8e888e8888880
def h0Pos : List Nat := [7,7,7,7,7,11,11,11,11,15,15,19,19,19,29,29,29,29,30,30,30,30,35,35,35,45,45,45,46,46,46,51,51,53,53,53,54,54,54,54,57,57,58,58,60,60,60,60]
def h0Neg : List Nat := [1,2,3,5,6,1,3,9,10,13,14,3,17,18,13,21,25,28,14,22,26,28,3,33,34,13,37,44,14,38,44,49,50,21,37,49,22,38,50,52,49,56,50,56,28,44,52,56]
def h0Mask : Nat := fullMask 48
def h0Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x30f8fc3ffff,0x10e86c1daed),(0xcccccccccccccccccccccccccccccccc,0xcf1f1fc3fff,0x471315c2d56),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf0fe7e3fc61f,0x70b67e2ec618),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xff007e3fc7e0,0xba005a374780),(0xffff0000ffff0000ffff0000ffff0000,0xffff803ff800,0xdfdb803bb000),(0xffffffff00000000ffffffff00000000,0xffffffc00000,0xefeded800000)]
def h0Steps : List (Nat × Nat × Nat) := [(1,0,1),(0,2,3),(0,6,4),(0,6,5),(0,4,5),(0,2,4),(0,2,5),(0,3,4),(0,3,5),(3,0,2),(3,1,3),(1,16,15),(3,1,4),(3,1,5),(3,15,5),(3,0,3),(3,0,4),(3,0,5),(3,1,2),(3,24,5)]
def h0W : BT Decor := buildWiresBT 5 h0Base h0Steps
def h0AutoList : List (List (Nat × Nat)) := [[],[(4,5)],[(3,4)],[(3,4),(4,5)],[(3,5),(4,5)],[(3,5)],[(2,3)],[(2,3),(4,5)],[(2,3),(3,4)],[(2,3),(3,4),(4,5)],[(2,3),(3,5),(4,5)],[(2,3),(3,5)],[(2,4),(3,4)],[(2,4),(3,4),(4,5)],[(2,4)],[(2,4),(4,5)],[(2,4),(3,5)],[(2,4),(3,5),(4,5)],[(2,5),(3,5),(4,5)],[(2,5),(3,5)],[(2,5),(4,5)],[(2,5)],[(2,5),(3,4),(4,5)],[(2,5),(3,4)]]
def h0Autos : BT (List (Nat × Nat)) := btOfList 5 h0AutoList
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
def h0SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 1 0,10),some (subcubeFast 2 0,10),some (subcubeFast 0 4,10),some (subcubeFast 0 8,10),some (subcubeFast 0 16,10),some (subcubeFast 0 32,10),some (subcubeFast 0 1,9),some (subcubeFast 0 2,9),some (subcubeFast 4 0,9),some (subcubeFast 8 0,9),some (subcubeFast 16 0,9),some (subcubeFast 32 0,9),some (subcubeFast 1 4,7),some (subcubeFast 2 4,7),some (subcubeFast 2 8,7),some (subcubeFast 0 12,7),some (subcubeFast 0 24,7),some (subcubeFast 0 36,7),some (subcubeFast 4 1,6),some (subcubeFast 4 2,6),some (subcubeFast 8 1,6),some (subcubeFast 8 2,6),some (subcubeFast 16 1,6),some (subcubeFast 16 2,6),some (subcubeFast 32 1,6),some (subcubeFast 32 2,6),some (subcubeFast 1 20,4),some (subcubeFast 16 12,4),some (subcubeFast 2 40,4),some (subcubeFast 32 12,4),some (subcubeFast 4 48,4),some (subcubeFast 8 48,4),some (subcubeFast 32 24,4)]
def h0Slices : BT (Option (Nat × Nat)) := btOfList 6 h0SliceList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput0Map : Lower (varsOf 62) 0xfcc0c000c0000000fcc0c000c0000000 10 := by
  apply carry_of (swaps := []) (roots2 := face0_R_47) (T2 := face0_G_47) _ face0_low_47
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice0 : Slice h0R h0G (subcubeFast 1 0) 10 := slice_fast_direct (zDead := 0) (qRoots := varsOf 62) (qGoal := 0xfcc0c000c0000000fcc0c000c0000000) (by decide +kernel) sliceInput0Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput1Map : Lower (varsOf 61) 0xfaa0a000a0000000faa0a000a0000000 10 := by
  apply carry_of (swaps := [(0, 1)]) (roots2 := face0_R_47) (T2 := face0_G_47) _ face0_low_47
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice1 : Slice h0R h0G (subcubeFast 2 0) 10 := slice_fast_direct (zDead := 0) (qRoots := varsOf 61) (qGoal := 0xfaa0a000a0000000faa0a000a0000000) (by decide +kernel) sliceInput1Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput2Map : Lower (varsOf 59) 0xeeeeee88ee888800eeeeee88ee888800 10 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (1, 2), (2, 3), (3, 4), (0, 1), (1, 2), (2, 3), (0, 1), (1, 2)]) (roots2 := face1_R_48) (T2 := face1_G_48) _ face1_low_48
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput2Flip : Lower (varsOf 59) 0xffeeee88ee888888ffeeee88ee888888 10 := dualLower (by decide +kernel) (by decide +kernel) sliceInput2Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice2 : Slice h0R h0G (subcubeFast 0 4) 10 := slice_fast_direct (zDead := 0) (qRoots := varsOf 59) (qGoal := 0xffeeee88ee888888ffeeee88ee888888) (by decide +kernel) sliceInput2Flip
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput3Map : Lower (varsOf 55) 0xeeeee8e8e8e88080eeeee8e8e8e88080 10 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (1, 2), (2, 3), (3, 4), (1, 2), (2, 3), (0, 1), (1, 2)]) (roots2 := face1_R_48) (T2 := face1_G_48) _ face1_low_48
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput3Flip : Lower (varsOf 55) 0xfefee8e8e8e88888fefee8e8e8e88888 10 := dualLower (by decide +kernel) (by decide +kernel) sliceInput3Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice3 : Slice h0R h0G (subcubeFast 0 8) 10 := slice_fast_direct (zDead := 0) (qRoots := varsOf 55) (qGoal := 0xfefee8e8e8e88888fefee8e8e8e88888) (by decide +kernel) sliceInput3Flip
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput4Map : Lower (varsOf 47) 0xeee8eee8e880e880eee8eee8e880e880 10 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (2, 3), (3, 4), (1, 2), (2, 3), (0, 1), (1, 2)]) (roots2 := face1_R_48) (T2 := face1_G_48) _ face1_low_48
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput4Flip : Lower (varsOf 47) 0xfee8fee8e888e888fee8fee8e888e888 10 := dualLower (by decide +kernel) (by decide +kernel) sliceInput4Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice4 : Slice h0R h0G (subcubeFast 0 16) 10 := slice_fast_direct (zDead := 0) (qRoots := varsOf 47) (qGoal := 0xfee8fee8e888e888fee8fee8e888e888) (by decide +kernel) sliceInput4Flip
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput5Map : Lower (varsOf 31) 0xeee8e880eee8e880eee8e880eee8e880 10 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (2, 3), (3, 4), (1, 2), (2, 3), (0, 1), (1, 2)]) (roots2 := face1_R_48) (T2 := face1_G_48) _ face1_low_48
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput5Flip : Lower (varsOf 31) 0xfee8e888fee8e888fee8e888fee8e888 10 := dualLower (by decide +kernel) (by decide +kernel) sliceInput5Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice5 : Slice h0R h0G (subcubeFast 0 32) 10 := slice_fast_direct (zDead := 0) (qRoots := varsOf 31) (qGoal := 0xfee8e888fee8e888fee8e888fee8e888) (by decide +kernel) sliceInput5Flip
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput6Map : Lower (varsOf 62) 0xfcccccc0ccc0c000fcccccc0ccc0c000 9 := by
  apply carry_of (swaps := [(2, 3), (1, 2)]) (roots2 := face0_R_47) (T2 := face2_G_42) _ face2_low_42
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput6Flip : Lower (varsOf 62) 0xfffcfcccfcccccc0fffcfcccfcccccc0 9 := dualLower (by decide +kernel) (by decide +kernel) sliceInput6Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice6 : Slice h0R h0G (subcubeFast 0 1) 9 := slice_fast_direct (zDead := 0) (qRoots := varsOf 62) (qGoal := 0xfffcfcccfcccccc0fffcfcccfcccccc0) (by decide +kernel) sliceInput6Flip
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput7Map : Lower (varsOf 61) 0xfaaaaaa0aaa0a000faaaaaa0aaa0a000 9 := by
  apply carry_of (swaps := [(2, 3), (1, 2), (0, 1)]) (roots2 := face0_R_47) (T2 := face2_G_42) _ face2_low_42
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput7Flip : Lower (varsOf 61) 0xfffafaaafaaaaaa0fffafaaafaaaaaa0 9 := dualLower (by decide +kernel) (by decide +kernel) sliceInput7Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice7 : Slice h0R h0G (subcubeFast 0 2) 9 := slice_fast_direct (zDead := 0) (qRoots := varsOf 61) (qGoal := 0xfffafaaafaaaaaa0fffafaaafaaaaaa0) (by decide +kernel) sliceInput7Flip
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput8Map : Lower (varsOf 59) 0xee88888888888800ee88888888888800 9 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (1, 2), (2, 3), (3, 4), (0, 1), (1, 2), (2, 3), (1, 2)]) (roots2 := face3_R_41) (T2 := face3_G_41) _ face3_low_41
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice8 : Slice h0R h0G (subcubeFast 4 0) 9 := slice_fast_direct (zDead := 0) (qRoots := varsOf 59) (qGoal := 0xee88888888888800ee88888888888800) (by decide +kernel) sliceInput8Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput9Map : Lower (varsOf 55) 0xe8e8888888888080e8e8888888888080 9 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (1, 2), (2, 3), (3, 4), (2, 3), (0, 1), (1, 2)]) (roots2 := face3_R_41) (T2 := face3_G_41) _ face3_low_41
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice9 : Slice h0R h0G (subcubeFast 8 0) 9 := slice_fast_direct (zDead := 0) (qRoots := varsOf 55) (qGoal := 0xe8e8888888888080e8e8888888888080) (by decide +kernel) sliceInput9Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput10Map : Lower (varsOf 47) 0xe888e88888808880e888e88888808880 9 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (3, 4), (1, 2), (2, 3), (0, 1), (1, 2)]) (roots2 := face3_R_41) (T2 := face3_G_41) _ face3_low_41
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice10 : Slice h0R h0G (subcubeFast 16 0) 9 := slice_fast_direct (zDead := 0) (qRoots := varsOf 47) (qGoal := 0xe888e88888808880e888e88888808880) (by decide +kernel) sliceInput10Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput11Map : Lower (varsOf 31) 0xe8888880e8888880e8888880e8888880 9 := by
  apply carry_of (swaps := [(4, 5), (2, 3), (3, 4), (1, 2), (2, 3), (0, 1), (1, 2)]) (roots2 := face3_R_41) (T2 := face3_G_41) _ face3_low_41
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice11 : Slice h0R h0G (subcubeFast 32 0) 9 := slice_fast_direct (zDead := 0) (qRoots := varsOf 31) (qGoal := 0xe8888880e8888880e8888880e8888880) (by decide +kernel) sliceInput11Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput12Map : Lower (varsOf 58) 0xffcccc00cc000000ffcccc00cc000000 7 := by
  apply carry_of (swaps := [(1, 2)]) (roots2 := face0_R_21) (T2 := face0_G_21) _ face0_low_21
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice12 : Slice h0R h0G (subcubeFast 1 4) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 58) (qGoal := 0xffcccc00cc000000ffcccc00cc000000) (by decide +kernel) sliceInput12Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput13Map : Lower (varsOf 57) 0xffaaaa00aa000000ffaaaa00aa000000 7 := by
  apply carry_of (swaps := [(1, 2), (0, 1)]) (roots2 := face0_R_21) (T2 := face0_G_21) _ face0_low_21
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice13 : Slice h0R h0G (subcubeFast 2 4) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 57) (qGoal := 0xffaaaa00aa000000ffaaaa00aa000000) (by decide +kernel) sliceInput13Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput14Map : Lower (varsOf 53) 0xfafaa0a0a0a00000fafaa0a0a0a00000 7 := by
  apply carry_of (swaps := [(1, 2), (2, 3), (0, 1)]) (roots2 := face0_R_21) (T2 := face0_G_21) _ face0_low_21
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice14 : Slice h0R h0G (subcubeFast 2 8) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 53) (qGoal := 0xfafaa0a0a0a00000fafaa0a0a0a00000) (by decide +kernel) sliceInput14Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput15Map : Lower (varsOf 51) 0xffffeeeeeeee8888ffffeeeeeeee8888 7 := by
  apply carry_of (swaps := [(2, 3), (3, 4)]) (roots2 := face1_R_19) (T2 := face1_G_20) _ face1_low_20
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice15 : Slice h0R h0G (subcubeFast 0 12) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 51) (qGoal := 0xffffeeeeeeee8888ffffeeeeeeee8888) (by decide +kernel) sliceInput15Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput16Map : Lower (varsOf 39) 0xfefefefee8e8e8e8fefefefee8e8e8e8 7 := by
  apply carry_of (swaps := []) (roots2 := face1_R_19) (T2 := face1_G_20) _ face1_low_20
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice16 : Slice h0R h0G (subcubeFast 0 24) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 39) (qGoal := 0xfefefefee8e8e8e8fefefefee8e8e8e8) (by decide +kernel) sliceInput16Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput17Map : Lower (varsOf 27) 0xffeeee88ffeeee88ffeeee88ffeeee88 7 := by
  apply carry_of (swaps := [(4, 5), (2, 3)]) (roots2 := face1_R_19) (T2 := face1_G_20) _ face1_low_20
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice17 : Slice h0R h0G (subcubeFast 0 36) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 27) (qGoal := 0xffeeee88ffeeee88ffeeee88ffeeee88) (by decide +kernel) sliceInput17Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput18Map : Lower (varsOf 58) 0xffcccccccccccc00ffcccccccccccc00 6 := by
  apply carry_of (swaps := [(4, 5), (2, 3), (3, 4), (1, 2), (2, 3)]) (roots2 := face0_R_31) (T2 := face2_G_35) _ face6_low_8
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice18 : Slice h0R h0G (subcubeFast 4 1) 6 := slice_fast_direct (zDead := 0) (qRoots := varsOf 58) (qGoal := 0xffcccccccccccc00ffcccccccccccc00) (by decide +kernel) sliceInput18Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput19Map : Lower (varsOf 57) 0xffaaaaaaaaaaaa00ffaaaaaaaaaaaa00 6 := by
  apply carry_of (swaps := [(4, 5), (2, 3), (3, 4), (1, 2), (2, 3), (0, 1)]) (roots2 := face0_R_31) (T2 := face2_G_35) _ face6_low_8
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice19 : Slice h0R h0G (subcubeFast 4 2) 6 := slice_fast_direct (zDead := 0) (qRoots := varsOf 57) (qGoal := 0xffaaaaaaaaaaaa00ffaaaaaaaaaaaa00) (by decide +kernel) sliceInput19Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput20Map : Lower (varsOf 54) 0xfcfcccccccccc0c0fcfcccccccccc0c0 6 := by
  apply carry_of (swaps := [(4, 5), (2, 3), (3, 4), (1, 2)]) (roots2 := face0_R_31) (T2 := face2_G_35) _ face6_low_8
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice20 : Slice h0R h0G (subcubeFast 8 1) 6 := slice_fast_direct (zDead := 0) (qRoots := varsOf 54) (qGoal := 0xfcfcccccccccc0c0fcfcccccccccc0c0) (by decide +kernel) sliceInput20Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput21Map : Lower (varsOf 53) 0xfafaaaaaaaaaa0a0fafaaaaaaaaaa0a0 6 := by
  apply carry_of (swaps := [(4, 5), (2, 3), (3, 4), (1, 2), (0, 1)]) (roots2 := face0_R_31) (T2 := face2_G_35) _ face6_low_8
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice21 : Slice h0R h0G (subcubeFast 8 2) 6 := slice_fast_direct (zDead := 0) (qRoots := varsOf 53) (qGoal := 0xfafaaaaaaaaaa0a0fafaaaaaaaaaa0a0) (by decide +kernel) sliceInput21Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput22Map : Lower (varsOf 46) 0xfcccfcccccc0ccc0fcccfcccccc0ccc0 6 := by
  apply carry_of (swaps := [(4, 5), (2, 3), (1, 2)]) (roots2 := face0_R_31) (T2 := face2_G_35) _ face6_low_8
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice22 : Slice h0R h0G (subcubeFast 16 1) 6 := slice_fast_direct (zDead := 0) (qRoots := varsOf 46) (qGoal := 0xfcccfcccccc0ccc0fcccfcccccc0ccc0) (by decide +kernel) sliceInput22Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput23Map : Lower (varsOf 45) 0xfaaafaaaaaa0aaa0faaafaaaaaa0aaa0 6 := by
  apply carry_of (swaps := [(4, 5), (2, 3), (1, 2), (0, 1)]) (roots2 := face0_R_31) (T2 := face2_G_35) _ face6_low_8
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice23 : Slice h0R h0G (subcubeFast 16 2) 6 := slice_fast_direct (zDead := 0) (qRoots := varsOf 45) (qGoal := 0xfaaafaaaaaa0aaa0faaafaaaaaa0aaa0) (by decide +kernel) sliceInput23Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput24Map : Lower (varsOf 30) 0xfcccccc0fcccccc0fcccccc0fcccccc0 6 := by
  apply carry_of (swaps := [(2, 3), (1, 2)]) (roots2 := face0_R_31) (T2 := face2_G_35) _ face6_low_8
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice24 : Slice h0R h0G (subcubeFast 32 1) 6 := slice_fast_direct (zDead := 0) (qRoots := varsOf 30) (qGoal := 0xfcccccc0fcccccc0fcccccc0fcccccc0) (by decide +kernel) sliceInput24Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput25Map : Lower (varsOf 29) 0xfaaaaaa0faaaaaa0faaaaaa0faaaaaa0 6 := by
  apply carry_of (swaps := [(2, 3), (1, 2), (0, 1)]) (roots2 := face0_R_31) (T2 := face2_G_35) _ face6_low_8
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice25 : Slice h0R h0G (subcubeFast 32 2) 6 := slice_fast_direct (zDead := 0) (qRoots := varsOf 29) (qGoal := 0xfaaaaaa0faaaaaa0faaaaaa0faaaaaa0) (by decide +kernel) sliceInput25Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput26Map : Lower (varsOf 42) 0xffccffcccc00cc00ffccffcccc00cc00 4 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (2, 3)]) (roots2 := face0_R_7) (T2 := face0_G_7) _ face7_low_0
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice26 : Slice h0R h0G (subcubeFast 1 20) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 42) (qGoal := 0xffccffcccc00cc00ffccffcccc00cc00) (by decide +kernel) sliceInput26Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput27Map : Lower (varsOf 35) 0xeeeeeeee88888888eeeeeeee88888888 4 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (0, 1), (1, 2)]) (roots2 := face0_R_7) (T2 := face0_G_7) _ face7_low_0
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice27 : Slice h0R h0G (subcubeFast 16 12) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 35) (qGoal := 0xeeeeeeee88888888eeeeeeee88888888) (by decide +kernel) sliceInput27Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput28Map : Lower (varsOf 21) 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0 4 := by
  apply carry_of (swaps := [(3, 4), (0, 1)]) (roots2 := face0_R_7) (T2 := face0_G_7) _ face7_low_0
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice28 : Slice h0R h0G (subcubeFast 2 40) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 21) (qGoal := 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0) (by decide +kernel) sliceInput28Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput29Map : Lower (varsOf 19) 0xeeee8888eeee8888eeee8888eeee8888 4 := by
  apply carry_of (swaps := [(3, 4), (0, 1), (1, 2)]) (roots2 := face0_R_7) (T2 := face0_G_7) _ face7_low_0
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice29 : Slice h0R h0G (subcubeFast 32 12) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 19) (qGoal := 0xeeee8888eeee8888eeee8888eeee8888) (by decide +kernel) sliceInput29Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput30Map : Lower (varsOf 11) 0xee88ee88ee88ee88ee88ee88ee88ee88 4 := by
  apply carry_of (swaps := [(0, 1), (1, 2)]) (roots2 := face0_R_7) (T2 := face0_G_7) _ face7_low_0
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice30 : Slice h0R h0G (subcubeFast 4 48) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 11) (qGoal := 0xee88ee88ee88ee88ee88ee88ee88ee88) (by decide +kernel) sliceInput30Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput31Map : Lower (varsOf 7) 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8 4 := by
  apply carry_of (swaps := [(0, 1), (1, 2), (2, 3)]) (roots2 := face0_R_7) (T2 := face0_G_7) _ face7_low_0
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice31 : Slice h0R h0G (subcubeFast 8 48) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 7) (qGoal := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8) (by decide +kernel) sliceInput31Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice32 : Slice h0R h0G (subcubeFast 32 24) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 7) (qGoal := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8) (by decide +kernel) sliceInput31Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h0R h0G p.1 p.2) h0Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h0R h0G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h0Slice0) (forall_cons (fun _ h => by cases h; exact h0Slice1) (forall_cons (fun _ h => by cases h; exact h0Slice2) (forall_cons (fun _ h => by cases h; exact h0Slice3) (forall_cons (fun _ h => by cases h; exact h0Slice4) (forall_cons (fun _ h => by cases h; exact h0Slice5) (forall_cons (fun _ h => by cases h; exact h0Slice6) (forall_cons (fun _ h => by cases h; exact h0Slice7) (forall_cons (fun _ h => by cases h; exact h0Slice8) (forall_cons (fun _ h => by cases h; exact h0Slice9) (forall_cons (fun _ h => by cases h; exact h0Slice10) (forall_cons (fun _ h => by cases h; exact h0Slice11) (forall_cons (fun _ h => by cases h; exact h0Slice12) (forall_cons (fun _ h => by cases h; exact h0Slice13) (forall_cons (fun _ h => by cases h; exact h0Slice14) (forall_cons (fun _ h => by cases h; exact h0Slice15) (forall_cons (fun _ h => by cases h; exact h0Slice16) (forall_cons (fun _ h => by cases h; exact h0Slice17) (forall_cons (fun _ h => by cases h; exact h0Slice18) (forall_cons (fun _ h => by cases h; exact h0Slice19) (forall_cons (fun _ h => by cases h; exact h0Slice20) (forall_cons (fun _ h => by cases h; exact h0Slice21) (forall_cons (fun _ h => by cases h; exact h0Slice22) (forall_cons (fun _ h => by cases h; exact h0Slice23) (forall_cons (fun _ h => by cases h; exact h0Slice24) (forall_cons (fun _ h => by cases h; exact h0Slice25) (forall_cons (fun _ h => by cases h; exact h0Slice26) (forall_cons (fun _ h => by cases h; exact h0Slice27) (forall_cons (fun _ h => by cases h; exact h0Slice28) (forall_cons (fun _ h => by cases h; exact h0Slice29) (forall_cons (fun _ h => by cases h; exact h0Slice30) (forall_cons (fun _ h => by cases h; exact h0Slice31) (forall_cons (fun _ h => by cases h; exact h0Slice32) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))))))))))))))))))
def h0Empty : BT (List (List Nat)) := BT.empty
lemma h0EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G (8 - 1) xs.toFinset) h0Empty := trivial
def h0Block8_0Specs : List PoolSpec := [(26,[]),(28,[]),(19,[(0,4,5)])]
def h0Block8_0Pools : BT (Option BoundPool) := buildPoolsBT 2 h0W h0R h0Slices h0Block8_0Specs
def h0Block8_0 : List NodeSpec := [([17,0,1,2,3,10,4,5],[0,1,2],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_0Ok : checkNodesBT h0W h0G h0Mask h0Block8_0Pools h0Autos h0Empty 8 h0Block8_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_0Mem : ∀ ns ∈ h0Block8_0, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0EmptyOk h0Block8_0Ok
def h0Nodes8 : List NodeSpec := h0Block8_0
def h0Bucket8 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 8 xs.toFinset) h0Bucket8 := buildBucketsBT_of_mem h0Block8_0Mem
def h0Block9_0Specs : List PoolSpec := [(30,[]),(31,[]),(21,[]),(19,[(0,4,5)]),(22,[(3,1,3)]),(25,[(3,0,2)]),(20,[(0,4,5)]),(4,[(3,0,2),(3,1,3)]),(20,[]),(32,[]),(12,[(0,3,4)]),(14,[]),(16,[]),(3,[(3,0,2),(3,15,5)]),(13,[(0,3,4)]),(3,[(3,1,2),(3,24,5)])]
def h0Block9_0Pools : BT (Option BoundPool) := buildPoolsBT 4 h0W h0R h0Slices h0Block9_0Specs
def h0Block9_0 : List NodeSpec := [([16,15,0,1,2,3,10,4,5],[0,1,3,4,5,6,7],[0]),([0,20,1,2,13,3,4,5],[2,8,9,10,11,12,13],[]),([0,1,25,2,13,3,4,5],[2,8,9,10,12,14,15],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_0Ok : checkNodesBT h0W h0G h0Mask h0Block9_0Pools h0Autos h0Bucket8 9 h0Block9_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_0Mem : ∀ ns ∈ h0Block9_0, Impossible h0G 9 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket8Ok h0Block9_0Ok
def h0Block9_1Specs : List PoolSpec := [(27,[]),(18,[]),(19,[]),(15,[]),(17,[]),(29,[]),(2,[(1,0,1),(0,6,4)]),(4,[(1,0,1),(0,2,3)]),(18,[(0,4,5)]),(23,[(0,2,3)]),(3,[(1,0,1),(0,4,5)]),(5,[(1,0,1),(0,2,3)]),(30,[]),(31,[]),(15,[(1,0,1)]),(0,[(0,2,3),(0,4,5)])]
def h0Block9_1Pools : BT (Option BoundPool) := buildPoolsBT 4 h0W h0R h0Slices h0Block9_1Specs
def h0Block9_1 : List NodeSpec := [([0,1,8,7,2,3,4,5],[0,1,2,3,4,5,6,7],[]),([0,1,6,7,2,3,10,4,5],[0,5,8,9,10,11,12,13,14,15],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_1Ok : checkNodesBT h0W h0G h0Mask h0Block9_1Pools h0Autos h0Bucket8 9 h0Block9_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_1Mem : ∀ ns ∈ h0Block9_1, Impossible h0G 9 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket8Ok h0Block9_1Ok
def h0Nodes9 : List NodeSpec := h0Block9_0 ++ h0Block9_1
def h0Bucket9 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket9Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 9 xs.toFinset) h0Bucket9 := buildBucketsBT_of_mem (forall_append h0Block9_0Mem h0Block9_1Mem)
def h0Block10_0Specs : List PoolSpec := [(18,[]),(19,[]),(21,[]),(22,[]),(24,[]),(6,[]),(4,[(3,0,2),(3,1,3)]),(20,[]),(5,[(3,0,2),(3,1,3)]),(12,[]),(23,[]),(25,[]),(8,[(0,3,4)]),(4,[(3,0,2)]),(1,[(3,0,2),(0,3,4)]),(5,[(3,0,2),(0,3,4)]),(4,[(3,1,2)]),(0,[(3,1,2),(0,3,4)]),(5,[(3,1,2),(0,3,4)]),(13,[])]
def h0Block10_0Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block10_0Specs
def h0Block10_0 : List NodeSpec := [([24,0,1,2,13,3,4,5],[0,2,7,11,12,16,17,18,19],[0,9]),([16,15,0,1,2,3,4,5],[1,3,4,5,6,7,8,9,10,11],[0]),([15,0,1,2,13,3,4,5],[1,2,4,7,9,12,13,14,15],[0,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block10_0Ok : checkNodesBT h0W h0G h0Mask h0Block10_0Pools h0Autos h0Bucket9 10 h0Block10_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block10_0Mem : ∀ ns ∈ h0Block10_0, Impossible h0G 10 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket9Ok h0Block10_0Ok
def h0Block10_1Specs : List PoolSpec := [(18,[]),(19,[]),(15,[]),(4,[(1,0,1),(0,2,3)]),(5,[(1,0,1),(0,2,3)]),(0,[(0,2,3),(0,4,5)]),(21,[]),(8,[]),(9,[]),(22,[]),(24,[]),(0,[(0,2,3)]),(2,[(1,0,1)]),(23,[]),(8,[(0,4,5)]),(10,[(0,2,3)]),(3,[(0,4,5)]),(5,[(0,2,3)]),(1,[(0,2,3),(0,4,5)])]
def h0Block10_1Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block10_1Specs
def h0Block10_1 : List NodeSpec := [([0,1,6,7,2,3,4,5],[0,2,3,4,6,7,8,9,10,11,12],[0,1]),([0,1,7,2,3,10,4,5],[0,1,2,5,9,13,14,15,16,17,18],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block10_1Ok : checkNodesBT h0W h0G h0Mask h0Block10_1Pools h0Autos h0Bucket9 10 h0Block10_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block10_1Mem : ∀ ns ∈ h0Block10_1, Impossible h0G 10 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket9Ok h0Block10_1Ok
def h0Nodes10 : List NodeSpec := h0Block10_0 ++ h0Block10_1
def h0Bucket10 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes10
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket10Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 10 xs.toFinset) h0Bucket10 := buildBucketsBT_of_mem (forall_append h0Block10_0Mem h0Block10_1Mem)
def h0Block11_0Specs : List PoolSpec := [(8,[]),(9,[]),(2,[(1,0,1)]),(6,[]),(1,[]),(3,[(1,0,1)]),(4,[(1,0,1)]),(5,[(1,0,1)]),(10,[]),(11,[]),(4,[(3,0,2)]),(1,[(3,0,2)]),(3,[(3,0,2)]),(5,[(3,0,2)]),(7,[]),(4,[(3,1,2)]),(0,[(3,1,2)]),(3,[(3,1,2)]),(5,[(3,1,2)])]
def h0Block11_0Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block11_0Specs
def h0Block11_0 : List NodeSpec := [([24,0,1,2,3,4,5],[0,1,3,8,9,14,15,16,17,18],[0,1,4,6,8,9]),([15,0,1,2,3,4,5],[0,1,3,8,9,10,11,12,13,14],[0,1,2,3,4]),([0,1,6,2,3,4,5],[0,1,2,3,4,5,6,7,8,9],[0,2,3,12,13,16])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block11_0Ok : checkNodesBT h0W h0G h0Mask h0Block11_0Pools h0Autos h0Bucket10 11 h0Block11_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block11_0Mem : ∀ ns ∈ h0Block11_0, Impossible h0G 11 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket10Ok h0Block11_0Ok
def h0Block11_1Specs : List PoolSpec := [(8,[]),(0,[(0,2,3)]),(6,[]),(10,[]),(11,[]),(7,[]),(5,[(0,2,3)]),(3,[]),(1,[(0,2,3)]),(4,[(0,2,3)])]
def h0Block11_1Pools : BT (Option BoundPool) := buildPoolsBT 4 h0W h0R h0Slices h0Block11_1Specs
def h0Block11_1 : List NodeSpec := [([0,1,7,2,3,4,5],[0,1,2,3,4,5,6,7,8,9],[0,8,9])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block11_1Ok : checkNodesBT h0W h0G h0Mask h0Block11_1Pools h0Autos h0Bucket10 11 h0Block11_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block11_1Mem : ∀ ns ∈ h0Block11_1, Impossible h0G 11 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket10Ok h0Block11_1Ok
def h0Nodes11 : List NodeSpec := h0Block11_0 ++ h0Block11_1
def h0Bucket11 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes11
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket11Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 11 xs.toFinset) h0Bucket11 := buildBucketsBT_of_mem (forall_append h0Block11_0Mem h0Block11_1Mem)
def h0Block12_0Specs : List PoolSpec := [(1,[]),(3,[]),(0,[]),(2,[]),(4,[]),(5,[])]
def h0Block12_0Pools : BT (Option BoundPool) := buildPoolsBT 3 h0W h0R h0Slices h0Block12_0Specs
def h0Block12_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,4,5],[0,2,3,6,8,9,12,13,16])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block12_0Ok : checkNodesBT h0W h0G h0Mask h0Block12_0Pools h0Autos h0Bucket11 12 h0Block12_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block12_0Mem : ∀ ns ∈ h0Block12_0, Impossible h0G 12 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket11Ok h0Block12_0Ok
def h0Nodes12 : List NodeSpec := h0Block12_0
def h0Bucket12 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes12
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket12Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 12 xs.toFinset) h0Bucket12 := buildBucketsBT_of_mem h0Block12_0Mem
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lifted : Lower h0R h0G 13 := lower_of_forestBT (essPairs := [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11),(VAR 4,3,19),(VAR 5,3,35)]) (by decide +kernel) h0Bucket12Ok (by decide +kernel)
def wit : List PEqualNP.CircuitLowerBounds.Gate := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [14, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 18]⟩]
def wo : Nat := 19
lemma wit_mono : PEqualNP.MetaComplexity.Monotone2 ⟨wit, wo⟩ := by simp [PEqualNP.MetaComplexity.Monotone2, wit]
set_option maxRecDepth 100000 in set_option maxHeartbeats 0 in
lemma wit_eval : ∀ r : Row, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput6 r)) = ((4276676744 * 2 ^ 32 + 3901261952) ||| ((4276676744 * 2 ^ 32 + 3901261952) <<< 64)).testBit r.val := by decide +kernel
lemma low_root : Lower (varsOf 63) ((4276676744 * 2 ^ 32 + 3901261952) ||| ((4276676744 * 2 ^ 32 + 3901261952) <<< 64)) 13 := lifted
end PEqualNP.Outside.L_meta_49061
theorem PEqualNP.Outside.L_meta_49061 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676744 * 2 ^ 32 + 3901261952) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676744 * 2 ^ 32 + 3901261952) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hcs
  exact PEqualNP.Outside.L_meta_49061.table2_of_lower (4276676744 * 2 ^ 32 + 3901261952) (by decide) (by decide) (by decide) (by decide)
    13 PEqualNP.Outside.L_meta_49061.low_root
    PEqualNP.Outside.L_meta_49061.wit PEqualNP.Outside.L_meta_49061.wo (by decide)
    PEqualNP.Outside.L_meta_49061.wit_mono PEqualNP.Outside.L_meta_49061.wit_eval s hcs
