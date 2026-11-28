import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_49123
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

def identifyRow (z o i j : Nat) (r : Row) : Row :=
  let mask := if r.val.testBit i then 1 <<< j else 0
  ⟨((fixRow z o r).val &&& (127 ^^^ (1 <<< j)) ||| mask) % 128, Nat.mod_lt _ (by decide)⟩
lemma mappedSlice {f : Row → Row} {raw R : List Nat} {T G D L : Nat}
    (proper : checkProper G = true) (inDomain : ∀ r : Row, D.testBit (f r).val = true)
    (covered : raw.all (fun v => freeIn R (renameW f v)) = true)
    (mapped : renameW f T = G) (bound : Lower R G L) : Slice raw T D L := by
  have ⟨g0,glt,gb0⟩ := checkProper_sound proper
  refine ⟨f, R, inDomain, fun a ha => freeIn_sound (List.all_eq_true.mp covered a ha), ?_, ?_⟩
  · rw [← obs_renameW, mapped]
    exact obs_not_const g0 glt gb0
  · rw [← obs_renameW, mapped]
    exact bound

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
def face0_G_1 : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def face0_R_1 : List Nat := varsOf 7
lemma face0_low_1_ok : carryOK [(2,5),(1,4),(0,3)] face0_R_1 face0_G_1 face0_R_0 face0_G_0 = true := by decide +kernel
lemma face0_low_1 : Lower face0_R_1 face0_G_1 4 := carry_of face0_low_1_ok face0_low_0
def face0_G_3 : Nat := 0xeeeeeeee88888888eeeeeeee88888888
def face0_R_3 : List Nat := varsOf 35
lemma face0_low_3_ok : carryOK [(1,2),(0,2),(1,4),(0,3)] face0_R_3 face0_G_3 face0_R_0 face0_G_0 = true := by decide +kernel
lemma face0_low_3 : Lower face0_R_3 face0_G_3 4 := carry_of face0_low_3_ok face0_low_0
def face0_G_6 : Nat := 0xfafafafaa0a0a0a0fafafafaa0a0a0a0
def face0_R_6 : List Nat := varsOf 37
lemma face0_low_6_ok : carryOK [(2,4),(0,1),(0,3)] face0_R_6 face0_G_6 face0_R_0 face0_G_0 = true := by decide +kernel
lemma face0_low_6 : Lower face0_R_6 face0_G_6 4 := carry_of face0_low_6_ok face0_low_0
def face0_G_8 : Nat := 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0
def face0_R_8 : List Nat := varsOf 22
lemma face0_low_8_ok : carryOK [(2,5),(2,4),(1,3)] face0_R_8 face0_G_8 face0_R_0 face0_G_0 = true := by decide +kernel
lemma face0_low_8 : Lower face0_R_8 face0_G_8 4 := carry_of face0_low_8_ok face0_low_0
def face0_G_9 : Nat := 0xfcfcfcfcc0c0c0c0fcfcfcfcc0c0c0c0
def face0_R_9 : List Nat := varsOf 38
lemma face0_low_9_ok : carryOK [(2,4),(1,3)] face0_R_9 face0_G_9 face0_R_0 face0_G_0 = true := by decide +kernel
lemma face0_low_9 : Lower face0_R_9 face0_G_9 4 := carry_of face0_low_9_ok face0_low_0
def face0_G_14 : Nat := 0xfff0f000fff0f000fff0f000fff0f000
def face0_R_14 : List Nat := varsOf 28
lemma face0_low_14_ok : carryOK [(2,5),(2,4),(2,3)] face0_R_14 face0_G_14 face0_R_0 face0_G_0 = true := by decide +kernel
lemma face0_low_14 : Lower face0_R_14 face0_G_14 4 := carry_of face0_low_14_ok face0_low_0
def face0_G_15 : Nat := 0xfff0fff0f000f000fff0fff0f000f000
def face0_R_15 : List Nat := varsOf 44
lemma face0_low_15_ok : carryOK [(2,4),(2,3)] face0_R_15 face0_G_15 face0_R_0 face0_G_0 = true := by decide +kernel
lemma face0_low_15 : Lower face0_R_15 face0_G_15 4 := carry_of face0_low_15_ok face0_low_0
def face0_G_16 : Nat := 0xffffaaaaaaaa0000ffffaaaaaaaa0000
def face0_R_16 : List Nat := varsOf 49
lemma face0_low_16_ok : carryOK [(1,2),(0,1),(0,3)] face0_R_16 face0_G_16 face0_R_0 face0_G_0 = true := by decide +kernel
lemma face0_low_16 : Lower face0_R_16 face0_G_16 4 := carry_of face0_low_16_ok face0_low_0
def face0_G_17 : Nat := 0xffffcccccccc0000ffffcccccccc0000
def face0_R_17 : List Nat := varsOf 50
lemma face0_low_17_ok : carryOK [(1,2),(1,3)] face0_R_17 face0_G_17 face0_R_0 face0_G_0 = true := by decide +kernel
lemma face0_low_17 : Lower face0_R_17 face0_G_17 4 := carry_of face0_low_17_ok face0_low_0
def face0_G_18 : Nat := 0xfffff0f0f0f00000fffff0f0f0f00000
def face0_R_18 : List Nat := varsOf 52
lemma face0_low_18_ok : carryOK [(2,3)] face0_R_18 face0_G_18 face0_R_0 face0_G_0 = true := by decide +kernel
lemma face0_low_18 : Lower face0_R_18 face0_G_18 4 := carry_of face0_low_18_ok face0_low_0
def face0_G_19 : Nat := 0xe8e8e8e800000000e8e8e8e800000000
def face0_R_19 : List Nat := varsOf 39
lemma face0_low_19_ok : liftCheck 0 32 face0_R_19 face0_G_19 face0_R_1 face0_G_1 [(VAR 5,35,3)] = true := by decide +kernel
lemma face0_low_19 : Lower face0_R_19 face0_G_19 5 := lift_of face0_low_19_ok face0_low_1
def face0_G_20 : Nat := 0xfefefefee8e8e8e8fefefefee8e8e8e8
def face0_pos_20 : List Nat := [3,3,5,5,6,6,33,33,34,34,36,36,3,3,5,5,6,6,33,33,34,34,36,36]
def face0_neg_20 : List Nat := [2,1,4,1,4,2,32,1,32,2,32,4,4,32,2,32,1,32,2,4,1,4,1,2]
def face0_fmask_20 : Nat := fullMask 24
def face0_base_20 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcf0cf,0x51008a),(0xcccccccccccccccccccccccccccccccc,0x333333,0x844221),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xc3cc3c,0x281814),(0xffffffff00000000ffffffff00000000,0xfc0fc0,0x2a540)]
def face0_steps_20 : List (Nat × Nat × Nat) := [(1,0,1),(2,4,2),(1,4,2),(1,0,2),(2,6,3),(1,1,2)]
def face0_W_20 : Array Decor := buildWires face0_base_20 face0_steps_20
def face0_autos_20 : Array (List (Nat × Nat)) := #[[],[(2,5)],[(0,1)],[(2,5),(0,1)],[(1,2)],[(1,5),(1,2)],[(0,1),(0,2)],[(1,5),(0,1),(0,2)],[(1,5),(0,2)]]
def face0_slicesL_20 : List (Nat × Nat) := [(subcube 2 0,4),(subcube 1 0,4),(subcube 32 0,4),(subcube 4 0,4)]
def face0_slices_20 : Array (Nat × Nat) := face0_slicesL_20.toArray
def face0_ps_20 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[])]
def face0_P_20 : Array (Option BoundPool) := buildPools face0_W_20 face0_R_19 face0_slices_20 face0_ps_20
lemma face0_gp_20 : goodPairs face0_G_20 face0_pos_20 face0_neg_20 := goodPairs_of (by decide +kernel)
lemma face0_base_20_ok : ∀ x ∈ face0_base_20, faithful face0_pos_20 face0_neg_20 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma face0_W_20_ok : ∀ x ∈ face0_W_20.toList, faithful face0_pos_20 face0_neg_20 x ∧ x.1 < 2^128 := buildWires_faithful face0_base_20_ok
lemma face0_autos_20_ok : ∀ sw ∈ face0_autos_20.toList, swapsValid sw = true ∧ permWord sw face0_G_20 = face0_G_20 := autos_of (by decide +kernel)
lemma face0_sl_20_0_ok : sliceDirectCheck 2 0 0 face0_R_19 face0_G_20 face0_R_6 face0_G_6 = true := by decide +kernel
lemma face0_sl_20_0 : Slice face0_R_19 face0_G_20 (subcube 2 0) 4 := slice_direct face0_sl_20_0_ok face0_low_6
lemma face0_sl_20_1_ok : sliceDirectCheck 1 0 0 face0_R_19 face0_G_20 face0_R_9 face0_G_9 = true := by decide +kernel
lemma face0_sl_20_1 : Slice face0_R_19 face0_G_20 (subcube 1 0) 4 := slice_direct face0_sl_20_1_ok face0_low_9
lemma face0_sl_20_2_ok : sliceDirectCheck 32 0 0 face0_R_19 face0_G_20 face0_R_1 face0_G_1 = true := by decide +kernel
lemma face0_sl_20_2 : Slice face0_R_19 face0_G_20 (subcube 32 0) 4 := slice_direct face0_sl_20_2_ok face0_low_1
lemma face0_sl_20_3_ok : sliceDirectCheck 4 0 0 face0_R_19 face0_G_20 face0_R_3 face0_G_3 = true := by decide +kernel
lemma face0_sl_20_3 : Slice face0_R_19 face0_G_20 (subcube 4 0) 4 := slice_direct face0_sl_20_3_ok face0_low_3
set_option maxRecDepth 200000 in
lemma face0_slices_20_ok : ∀ i (hi : i < face0_slices_20.size), Slice face0_R_19 face0_G_20 face0_slices_20[i].1 face0_slices_20[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice face0_R_19 face0_G_20 p.1 p.2) (forall_cons face0_sl_20_0 (forall_cons face0_sl_20_1 (forall_cons face0_sl_20_2 (forall_cons face0_sl_20_3 (fun _ h => (List.not_mem_nil h).elim)))))
lemma face0_P_20_ok : ∀ i (hi : i < face0_P_20.size), ∀ c, face0_P_20[i] = some c → ValidPool face0_R_19 face0_G_20 c := buildPools_sound face0_slices_20_ok
lemma face0_bk_20_init_ok : ∀ i (hi : i < face0_bk_0_init.size), ∀ xs ∈ face0_bk_0_init[i], Impossible face0_G_20 (0 - 1) xs.toFinset := by intro i hi; simp [face0_bk_0_init] at hi
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_chk_20_0 : checkNodes face0_W_20 face0_G_20 face0_fmask_20 face0_P_20 face0_autos_20 face0_bk_0_init 0 face0_nodes_0_0 = true := by decide +kernel
def face0_bk_20_0 : Array (List (List Nat)) := buildBuckets 1 face0_W_20 face0_nodes_0_0
lemma face0_bk_20_0_ok : ∀ i (hi : i < face0_bk_20_0.size), ∀ xs ∈ face0_bk_20_0[i], Impossible face0_G_20 0 xs.toFinset :=
  buildBuckets_sound (by decide) face0_gp_20 face0_W_20_ok face0_P_20_ok face0_autos_20_ok face0_bk_20_init_ok face0_chk_20_0
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_chk_20_1 : checkNodes face0_W_20 face0_G_20 face0_fmask_20 face0_P_20 face0_autos_20 face0_bk_20_0 1 face0_nodes_0_0 = true := by decide +kernel
lemma face0_bk_20_1_ok : ∀ i (hi : i < face0_bk_20_0.size), ∀ xs ∈ face0_bk_20_0[i], Impossible face0_G_20 1 xs.toFinset :=
  buildBuckets_sound (by decide) face0_gp_20 face0_W_20_ok face0_P_20_ok face0_autos_20_ok face0_bk_20_0_ok face0_chk_20_1
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_chk_20_2 : checkNodes face0_W_20 face0_G_20 face0_fmask_20 face0_P_20 face0_autos_20 face0_bk_20_0 2 face0_nodes_0_0 = true := by decide +kernel
lemma face0_bk_20_2_ok : ∀ i (hi : i < face0_bk_20_0.size), ∀ xs ∈ face0_bk_20_0[i], Impossible face0_G_20 2 xs.toFinset :=
  buildBuckets_sound (by decide) face0_gp_20 face0_W_20_ok face0_P_20_ok face0_autos_20_ok face0_bk_20_1_ok face0_chk_20_2
def face0_nodes_20_3 : List NodeSpec := [([8,0,1,2],[],[]),([4,7,9,3],[0,1],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_chk_20_3 : checkNodes face0_W_20 face0_G_20 face0_fmask_20 face0_P_20 face0_autos_20 face0_bk_20_0 3 face0_nodes_20_3 = true := by decide +kernel
def face0_bk_20_3 : Array (List (List Nat)) := buildBuckets 1 face0_W_20 face0_nodes_20_3
lemma face0_bk_20_3_ok : ∀ i (hi : i < face0_bk_20_3.size), ∀ xs ∈ face0_bk_20_3[i], Impossible face0_G_20 3 xs.toFinset :=
  buildBuckets_sound (by decide) face0_gp_20 face0_W_20_ok face0_P_20_ok face0_autos_20_ok face0_bk_20_2_ok face0_chk_20_3
def face0_nodes_20_4 : List NodeSpec := [([5,0,1,2,3],[],[]),([0,1,2,6,3],[2],[0]),([1,4,2,7,3],[0,3],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_chk_20_4 : checkNodes face0_W_20 face0_G_20 face0_fmask_20 face0_P_20 face0_autos_20 face0_bk_20_3 4 face0_nodes_20_4 = true := by decide +kernel
def face0_bk_20_4 : Array (List (List Nat)) := buildBuckets 2 face0_W_20 face0_nodes_20_4
lemma face0_bk_20_4_ok : ∀ i (hi : i < face0_bk_20_4.size), ∀ xs ∈ face0_bk_20_4[i], Impossible face0_G_20 4 xs.toFinset :=
  buildBuckets_sound (by decide) face0_gp_20 face0_W_20_ok face0_P_20_ok face0_autos_20_ok face0_bk_20_3_ok face0_chk_20_4
def face0_nodes_20_5 : List NodeSpec := [([0,1,4,2,3],[0,1,3,2],[0,1,2,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_chk_20_5 : checkNodes face0_W_20 face0_G_20 face0_fmask_20 face0_P_20 face0_autos_20 face0_bk_20_4 5 face0_nodes_20_5 = true := by decide +kernel
def face0_bk_20_5 : Array (List (List Nat)) := buildBuckets 1 face0_W_20 face0_nodes_20_5
lemma face0_bk_20_5_ok : ∀ i (hi : i < face0_bk_20_5.size), ∀ xs ∈ face0_bk_20_5[i], Impossible face0_G_20 5 xs.toFinset :=
  buildBuckets_sound (by decide) face0_gp_20 face0_W_20_ok face0_P_20_ok face0_autos_20_ok face0_bk_20_4_ok face0_chk_20_5
def face0_nodes_20_6 : List NodeSpec := [([0,1,2,3],[0,1,3,2],[0,4,5,6,7,8])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_chk_20_6 : checkNodes face0_W_20 face0_G_20 face0_fmask_20 face0_P_20 face0_autos_20 face0_bk_20_5 6 face0_nodes_20_6 = true := by decide +kernel
def face0_bk_20_6 : Array (List (List Nat)) := buildBuckets 1 face0_W_20 face0_nodes_20_6
lemma face0_bk_20_6_ok : ∀ i (hi : i < face0_bk_20_6.size), ∀ xs ∈ face0_bk_20_6[i], Impossible face0_G_20 6 xs.toFinset :=
  buildBuckets_sound (by decide) face0_gp_20 face0_W_20_ok face0_P_20_ok face0_autos_20_ok face0_bk_20_5_ok face0_chk_20_6
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_forestRoot_20_ok : forestRootCheck face0_R_19 face0_G_20 [(VAR 0,3,2),(VAR 1,3,1),(VAR 2,5,1),(VAR 5,33,1)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_forestRoot_20_in : bucketContains face0_bk_20_6 face0_R_19 = true := by decide +kernel
lemma face0_low_20 : Lower face0_R_19 face0_G_20 7 := lower_of_forest face0_forestRoot_20_ok face0_bk_20_6_ok face0_forestRoot_20_in
def face0_G_21 : Nat := 0xfff0f000f0000000fff0f000f0000000
def face0_R_21 : List Nat := varsOf 60
def face0_pos_21 : List Nat := [28,28,28,44,44,44,52,52,52,56,56,56,28,28,28,44,44,44,52,52,52,56,56,56]
def face0_neg_21 : List Nat := [24,20,12,40,36,12,48,36,20,48,40,24,36,40,48,20,24,48,12,24,40,12,20,36]
def face0_base_21 : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x1ff1ff,0xe491b6),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xe3fe3f,0x3d2c2d),(0xffff0000ffff0000ffff0000ffff0000,0xfc7fc7,0x4bcb43),(0xffffffff00000000ffffffff00000000,0xff8ff8,0x9276d8)]
def face0_steps_21 : List (Nat × Nat × Nat) := [(0,0,1),(0,0,2),(3,4,2),(0,4,2),(0,1,2),(3,7,3)]
def face0_W_21 : Array Decor := buildWires face0_base_21 face0_steps_21
def face0_autos_21 : Array (List (Nat × Nat)) := #[[],[(4,5)],[(2,3)],[(4,5),(2,3)],[(3,4)],[(3,5),(3,4)],[(2,3),(2,4)],[(3,5),(2,3),(2,4)],[(3,5),(2,4)]]
def face0_slicesL_21 : List (Nat × Nat) := [(subcube 0 16,4),(subcube 0 4,4),(subcube 0 8,4),(subcube 0 32,4)]
def face0_slices_21 : Array (Nat × Nat) := face0_slicesL_21.toArray
def face0_P_21 : Array (Option BoundPool) := buildPools face0_W_21 face0_R_21 face0_slices_21 face0_ps_20
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
lemma face0_chk_21_0 : checkNodes face0_W_21 face0_G_21 face0_fmask_20 face0_P_21 face0_autos_21 face0_bk_0_init 0 face0_nodes_0_0 = true := by decide +kernel
def face0_bk_21_0 : Array (List (List Nat)) := buildBuckets 1 face0_W_21 face0_nodes_0_0
lemma face0_bk_21_0_ok : ∀ i (hi : i < face0_bk_21_0.size), ∀ xs ∈ face0_bk_21_0[i], Impossible face0_G_21 0 xs.toFinset :=
  buildBuckets_sound (by decide) face0_gp_21 face0_W_21_ok face0_P_21_ok face0_autos_21_ok face0_bk_21_init_ok face0_chk_21_0
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_chk_21_1 : checkNodes face0_W_21 face0_G_21 face0_fmask_20 face0_P_21 face0_autos_21 face0_bk_21_0 1 face0_nodes_0_0 = true := by decide +kernel
lemma face0_bk_21_1_ok : ∀ i (hi : i < face0_bk_21_0.size), ∀ xs ∈ face0_bk_21_0[i], Impossible face0_G_21 1 xs.toFinset :=
  buildBuckets_sound (by decide) face0_gp_21 face0_W_21_ok face0_P_21_ok face0_autos_21_ok face0_bk_21_0_ok face0_chk_21_1
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_chk_21_2 : checkNodes face0_W_21 face0_G_21 face0_fmask_20 face0_P_21 face0_autos_21 face0_bk_21_0 2 face0_nodes_0_0 = true := by decide +kernel
lemma face0_bk_21_2_ok : ∀ i (hi : i < face0_bk_21_0.size), ∀ xs ∈ face0_bk_21_0[i], Impossible face0_G_21 2 xs.toFinset :=
  buildBuckets_sound (by decide) face0_gp_21 face0_W_21_ok face0_P_21_ok face0_autos_21_ok face0_bk_21_1_ok face0_chk_21_2
def face0_nodes_21_3 : List NodeSpec := [([4,5,8,3],[0,1],[]),([9,0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_chk_21_3 : checkNodes face0_W_21 face0_G_21 face0_fmask_20 face0_P_21 face0_autos_21 face0_bk_21_0 3 face0_nodes_21_3 = true := by decide +kernel
def face0_bk_21_3 : Array (List (List Nat)) := buildBuckets 1 face0_W_21 face0_nodes_21_3
lemma face0_bk_21_3_ok : ∀ i (hi : i < face0_bk_21_3.size), ∀ xs ∈ face0_bk_21_3[i], Impossible face0_G_21 3 xs.toFinset :=
  buildBuckets_sound (by decide) face0_gp_21 face0_W_21_ok face0_P_21_ok face0_autos_21_ok face0_bk_21_2_ok face0_chk_21_3
def face0_nodes_21_4 : List NodeSpec := [([4,5,1,2,3],[0,2],[0]),([6,0,1,2,3],[],[]),([7,0,1,2,3],[3],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_chk_21_4 : checkNodes face0_W_21 face0_G_21 face0_fmask_20 face0_P_21 face0_autos_21 face0_bk_21_3 4 face0_nodes_21_4 = true := by decide +kernel
def face0_bk_21_4 : Array (List (List Nat)) := buildBuckets 2 face0_W_21 face0_nodes_21_4
lemma face0_bk_21_4_ok : ∀ i (hi : i < face0_bk_21_4.size), ∀ xs ∈ face0_bk_21_4[i], Impossible face0_G_21 4 xs.toFinset :=
  buildBuckets_sound (by decide) face0_gp_21 face0_W_21_ok face0_P_21_ok face0_autos_21_ok face0_bk_21_3_ok face0_chk_21_4
def face0_nodes_21_5 : List NodeSpec := [([4,0,1,2,3],[2,1,0,3],[0,1,2,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_chk_21_5 : checkNodes face0_W_21 face0_G_21 face0_fmask_20 face0_P_21 face0_autos_21 face0_bk_21_4 5 face0_nodes_21_5 = true := by decide +kernel
def face0_bk_21_5 : Array (List (List Nat)) := buildBuckets 1 face0_W_21 face0_nodes_21_5
lemma face0_bk_21_5_ok : ∀ i (hi : i < face0_bk_21_5.size), ∀ xs ∈ face0_bk_21_5[i], Impossible face0_G_21 5 xs.toFinset :=
  buildBuckets_sound (by decide) face0_gp_21 face0_W_21_ok face0_P_21_ok face0_autos_21_ok face0_bk_21_4_ok face0_chk_21_5
def face0_nodes_21_6 : List NodeSpec := [([0,1,2,3],[1,2,0,3],[0,4,5,6,7,8])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_chk_21_6 : checkNodes face0_W_21 face0_G_21 face0_fmask_20 face0_P_21 face0_autos_21 face0_bk_21_5 6 face0_nodes_21_6 = true := by decide +kernel
def face0_bk_21_6 : Array (List (List Nat)) := buildBuckets 1 face0_W_21 face0_nodes_21_6
lemma face0_bk_21_6_ok : ∀ i (hi : i < face0_bk_21_6.size), ∀ xs ∈ face0_bk_21_6[i], Impossible face0_G_21 6 xs.toFinset :=
  buildBuckets_sound (by decide) face0_gp_21 face0_W_21_ok face0_P_21_ok face0_autos_21_ok face0_bk_21_5_ok face0_chk_21_6
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_forestRoot_21_ok : forestRootCheck face0_R_21 face0_G_21 [(VAR 2,28,24),(VAR 3,28,20),(VAR 4,28,12),(VAR 5,44,12)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_forestRoot_21_in : bucketContains face0_bk_21_6 face0_R_21 = true := by decide +kernel
lemma face0_low_21 : Lower face0_R_21 face0_G_21 7 := lower_of_forest face0_forestRoot_21_ok face0_bk_21_6_ok face0_forestRoot_21_in
def face0_G_22 : Nat := 0xfffffcfcfcfc0000fffffcfcfcfc0000
def face0_R_22 : List Nat := varsOf 54
lemma face0_low_22_ok : liftCheck 2 0 face0_R_22 face0_G_22 face0_R_18 face0_G_18 [(VAR 1,18,16)] = true := by decide +kernel
lemma face0_low_22 : Lower face0_R_22 face0_G_22 5 := lift_of face0_low_22_ok face0_low_18
def face0_G_24 : Nat := 0xe8e80000e8e80000e8e80000e8e80000
def face0_R_24 : List Nat := varsOf 23
lemma face0_low_24_ok : carryOK [(4,5)] face0_R_24 face0_G_24 face0_R_19 face0_G_19 = true := by decide +kernel
lemma face0_low_24 : Lower face0_R_24 face0_G_24 5 := carry_of face0_low_24_ok face0_low_19
def face0_G_27 : Nat := 0xeeee888888880000eeee888888880000
def face0_R_27 : List Nat := varsOf 51
lemma face0_low_27_ok : carryOK [(1,3),(0,2)] face0_R_27 face0_G_27 face0_R_21 face0_G_21 = true := by decide +kernel
lemma face0_low_27 : Lower face0_R_27 face0_G_27 7 := carry_of face0_low_27_ok face0_low_21
def face0_G_30 : Nat := 0xfafaa0a0a0a00000fafaa0a0a0a00000
def face0_R_30 : List Nat := varsOf 53
lemma face0_low_30_ok : carryOK [(1,3),(0,1),(0,2)] face0_R_30 face0_G_30 face0_R_21 face0_G_21 = true := by decide +kernel
lemma face0_low_30 : Lower face0_R_30 face0_G_30 7 := carry_of face0_low_30_ok face0_low_21
def face0_G_33 : Nat := 0xfcfcc0c0c0c00000fcfcc0c0c0c00000
lemma face0_low_33_ok : carryOK [(1,3),(1,2)] face0_R_22 face0_G_33 face0_R_21 face0_G_21 = true := by decide +kernel
lemma face0_low_33 : Lower face0_R_22 face0_G_33 7 := carry_of face0_low_33_ok face0_low_21
def face0_G_35 : Nat := 0xfefee8e8fefee8e8fefee8e8fefee8e8
lemma face0_low_35_ok : carryOK [(4,5)] face0_R_24 face0_G_35 face0_R_19 face0_G_20 = true := by decide +kernel
lemma face0_low_35 : Lower face0_R_24 face0_G_35 7 := carry_of face0_low_35_ok face0_low_20
def face0_G_44 : Nat := 0xffffeeeeeeee0000ffffeeeeeeee0000
lemma face0_low_44_ok : carryOK [(0,2),(0,1)] face0_R_27 face0_G_44 face0_R_22 face0_G_22 = true := by decide +kernel
lemma face0_low_44 : Lower face0_R_27 face0_G_44 5 := carry_of face0_low_44_ok face0_low_22
def face0_G_45 : Nat := 0xfffffafafafa0000fffffafafafa0000
lemma face0_low_45_ok : carryOK [(0,1)] face0_R_30 face0_G_45 face0_R_22 face0_G_22 = true := by decide +kernel
lemma face0_low_45 : Lower face0_R_30 face0_G_45 5 := carry_of face0_low_45_ok face0_low_22
def face0_G_48 : Nat := 0xfefee8e8e8e80000fefee8e8e8e80000
def face0_R_48 : List Nat := varsOf 55
def face0_pos_48 : List Nat := [19,19,19,21,21,21,22,22,22,23,35,35,35,37,37,37,38,38,38,39,49,49,49,50,50,50,52,52,52,19,19,19,19,19,19,21,21,21,21,21,21,22,22,22,22,22,22,35,35,35,35,35,35,37,37,37,37,37,37,38,38,38,38,38,38,49,49,49,49,49,50,50,50,50,50,52,52,52,52,52]
def face0_neg_48 : List Nat := [18,17,3,20,17,5,20,18,6,7,34,33,3,36,33,5,36,34,6,7,48,33,17,48,34,18,48,36,20,7,20,33,34,36,48,7,18,33,34,36,48,7,17,33,34,36,48,7,17,18,20,36,48,7,17,18,20,34,48,7,17,18,20,33,48,7,18,20,34,36,7,17,20,33,36,7,17,18,33,34]
def face0_fmask_48 : Nat := fullMask 80
def face0_base_48 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x3e07ff81ffe078fe3f,0x5ac298618e28a068da36),(0xcccccccccccccccccccccccccccccccc,0x7c1f81ffe07e38f1fc7,0xa8562aa29259230e1785),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf801ffe07ff81c0fe3f8,0xd6a492ca28a780da368),(0xffff0000ffff0000ffff0000ffff0000,0xfffe00007ffffff003ff,0x318d75d7451456d000db),(0xffffffff00000000ffffffff00000000,0xffffffff80001ffffc00,0xc631861879e78db36c00)]
def face0_steps_48 : List (Nat × Nat × Nat) := [(0,3,4),(3,0,3),(1,0,1),(1,0,5),(3,1,4),(3,0,4),(3,6,4),(1,6,1),(0,6,4),(3,7,3),(0,7,3),(3,2,3),(1,0,2),(2,7,2),(1,7,2),(3,1,8),(1,1,5),(2,7,5),(1,7,5),(0,19,3),(0,7,4),(0,15,4),(3,16,4),(3,15,4),(1,1,2),(3,2,23),(2,19,5)]
def face0_W_48 : Array Decor := buildWires face0_base_48 face0_steps_48
def face0_autos_48 : Array (List (Nat × Nat)) := #[[],[(1,2)],[(0,1),(0,2)],[(0,1)],[(4,5)],[(0,2),(0,1)],[(4,5),(0,1)],[(4,5),(0,2),(0,1)]]
def face0_slicesL_48 : List (Nat × Nat) := [(subcube 32 0,5),(subcube 0 16,7),(subcube 1 32,4),(subcube 2 0,7),(subcube 0 1,5),(subcube 0 2,5),(subcube 0 32,7),(subcube 4 0,7),(subcube 4 16,4),(subcube 4 2,4),(subcube 4 1,4),(subcube 2 1,4),(subcube 2 16,4),(subcube 1 0,7),(subcube 0 4,5),(subcube 16 0,5),(subcube 1 4,4),(subcube 16 32,4),(subcube 1 16,4),(subcube 32 16,4),(subcube 2 4,4)]
def face0_slices_48 : Array (Nat × Nat) := face0_slicesL_48.toArray
def face0_ps_48 : List PoolSpec := [(0,[]),(1,[(1,0,1),(1,0,5),(1,1,5)]),(2,[]),(1,[(1,0,1),(1,7,5),(3,2,23)]),(3,[(0,7,3),(0,7,4),(0,3,4)]),(4,[]),(5,[]),(1,[]),(6,[]),(1,[(1,0,1),(1,7,2),(2,19,5)]),(7,[]),(8,[]),(9,[]),(10,[]),(1,[(1,0,1),(1,0,2),(1,1,2)]),(11,[]),(1,[(1,0,5),(3,1,8)]),(12,[]),(1,[(1,0,5),(1,1,5)]),(13,[]),(3,[]),(14,[]),(13,[(0,3,4),(2,7,5)]),(3,[(0,3,4),(2,7,5)]),(1,[(1,0,1),(1,7,5)]),(15,[]),(1,[(1,0,1),(1,0,5)]),(3,[(0,7,3),(0,7,4)]),(3,[(0,7,3),(0,15,4)]),(16,[]),(17,[]),(1,[(1,0,1),(2,7,2)]),(1,[(1,0,1),(1,7,2)]),(3,[(0,7,3),(0,3,4)]),(1,[(1,0,1),(1,0,2)]),(1,[(1,0,1),(2,7,5)]),(3,[(0,7,3),(3,15,4)]),(6,[(1,0,1),(1,0,2),(1,1,2)]),(13,[(0,3,4)]),(1,[(1,0,5)]),(18,[]),(19,[]),(20,[]),(3,[(0,3,4)]),(1,[(1,0,1)]),(6,[(1,0,1)]),(3,[(0,7,3)]),(6,[(1,0,1),(1,0,2)]),(6,[(1,0,1),(2,7,2)]),(6,[(1,0,1),(1,7,2)]),(7,[(0,3,4)])]
def face0_P_48 : Array (Option BoundPool) := buildPools face0_W_48 face0_R_48 face0_slices_48 face0_ps_48
lemma face0_gp_48 : goodPairs face0_G_48 face0_pos_48 face0_neg_48 := goodPairs_of (by decide +kernel)
lemma face0_base_48_ok : ∀ x ∈ face0_base_48, faithful face0_pos_48 face0_neg_48 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma face0_W_48_ok : ∀ x ∈ face0_W_48.toList, faithful face0_pos_48 face0_neg_48 x ∧ x.1 < 2^128 := buildWires_faithful face0_base_48_ok
lemma face0_autos_48_ok : ∀ sw ∈ face0_autos_48.toList, swapsValid sw = true ∧ permWord sw face0_G_48 = face0_G_48 := autos_of (by decide +kernel)
lemma face0_sl_48_0_ok : sliceDirectCheck 32 0 0 face0_R_48 face0_G_48 face0_R_24 face0_G_24 = true := by decide +kernel
lemma face0_sl_48_0 : Slice face0_R_48 face0_G_48 (subcube 32 0) 5 := slice_direct face0_sl_48_0_ok face0_low_24
lemma face0_sl_48_1_ok : sliceDirectCheck 0 16 0 face0_R_48 face0_G_48 face0_R_19 face0_G_20 = true := by decide +kernel
lemma face0_sl_48_1 : Slice face0_R_48 face0_G_48 (subcube 0 16) 7 := slice_direct face0_sl_48_1_ok face0_low_20
lemma face0_sl_48_2_ok : sliceDirectCheck 1 32 0 face0_R_48 face0_G_48 face0_R_8 face0_G_8 = true := by decide +kernel
lemma face0_sl_48_2 : Slice face0_R_48 face0_G_48 (subcube 1 32) 4 := slice_direct face0_sl_48_2_ok face0_low_8
lemma face0_sl_48_3_ok : sliceDirectCheck 2 0 0 face0_R_48 face0_G_48 face0_R_30 face0_G_30 = true := by decide +kernel
lemma face0_sl_48_3 : Slice face0_R_48 face0_G_48 (subcube 2 0) 7 := slice_direct face0_sl_48_3_ok face0_low_30
lemma face0_sl_48_4_ok : sliceDirectCheck 0 1 0 face0_R_48 face0_G_48 face0_R_22 face0_G_22 = true := by decide +kernel
lemma face0_sl_48_4 : Slice face0_R_48 face0_G_48 (subcube 0 1) 5 := slice_direct face0_sl_48_4_ok face0_low_22
lemma face0_sl_48_5_ok : sliceDirectCheck 0 2 0 face0_R_48 face0_G_48 face0_R_30 face0_G_45 = true := by decide +kernel
lemma face0_sl_48_5 : Slice face0_R_48 face0_G_48 (subcube 0 2) 5 := slice_direct face0_sl_48_5_ok face0_low_45
lemma face0_sl_48_6_ok : sliceDirectCheck 0 32 0 face0_R_48 face0_G_48 face0_R_24 face0_G_35 = true := by decide +kernel
lemma face0_sl_48_6 : Slice face0_R_48 face0_G_48 (subcube 0 32) 7 := slice_direct face0_sl_48_6_ok face0_low_35
lemma face0_sl_48_7_ok : sliceDirectCheck 4 0 0 face0_R_48 face0_G_48 face0_R_27 face0_G_27 = true := by decide +kernel
lemma face0_sl_48_7 : Slice face0_R_48 face0_G_48 (subcube 4 0) 7 := slice_direct face0_sl_48_7_ok face0_low_27
lemma face0_sl_48_8_ok : sliceDirectCheck 4 16 0 face0_R_48 face0_G_48 face0_R_3 face0_G_3 = true := by decide +kernel
lemma face0_sl_48_8 : Slice face0_R_48 face0_G_48 (subcube 4 16) 4 := slice_direct face0_sl_48_8_ok face0_low_3
lemma face0_sl_48_9_ok : sliceDirectCheck 4 2 0 face0_R_48 face0_G_48 face0_R_16 face0_G_16 = true := by decide +kernel
lemma face0_sl_48_9 : Slice face0_R_48 face0_G_48 (subcube 4 2) 4 := slice_direct face0_sl_48_9_ok face0_low_16
lemma face0_sl_48_10_ok : sliceDirectCheck 4 1 0 face0_R_48 face0_G_48 face0_R_17 face0_G_17 = true := by decide +kernel
lemma face0_sl_48_10 : Slice face0_R_48 face0_G_48 (subcube 4 1) 4 := slice_direct face0_sl_48_10_ok face0_low_17
lemma face0_sl_48_11_ok : sliceDirectCheck 2 1 0 face0_R_48 face0_G_48 face0_R_18 face0_G_18 = true := by decide +kernel
lemma face0_sl_48_11 : Slice face0_R_48 face0_G_48 (subcube 2 1) 4 := slice_direct face0_sl_48_11_ok face0_low_18
lemma face0_sl_48_12_ok : sliceDirectCheck 2 16 0 face0_R_48 face0_G_48 face0_R_6 face0_G_6 = true := by decide +kernel
lemma face0_sl_48_12 : Slice face0_R_48 face0_G_48 (subcube 2 16) 4 := slice_direct face0_sl_48_12_ok face0_low_6
lemma face0_sl_48_13_ok : sliceDirectCheck 1 0 0 face0_R_48 face0_G_48 face0_R_22 face0_G_33 = true := by decide +kernel
lemma face0_sl_48_13 : Slice face0_R_48 face0_G_48 (subcube 1 0) 7 := slice_direct face0_sl_48_13_ok face0_low_33
lemma face0_sl_48_14_ok : sliceDirectCheck 0 4 0 face0_R_48 face0_G_48 face0_R_27 face0_G_44 = true := by decide +kernel
lemma face0_sl_48_14 : Slice face0_R_48 face0_G_48 (subcube 0 4) 5 := slice_direct face0_sl_48_14_ok face0_low_44
lemma face0_sl_48_15_ok : sliceDirectCheck 16 0 0 face0_R_48 face0_G_48 face0_R_19 face0_G_19 = true := by decide +kernel
lemma face0_sl_48_15 : Slice face0_R_48 face0_G_48 (subcube 16 0) 5 := slice_direct face0_sl_48_15_ok face0_low_19
lemma face0_sl_48_16_ok : sliceDirectCheck 1 4 0 face0_R_48 face0_G_48 face0_R_17 face0_G_17 = true := by decide +kernel
lemma face0_sl_48_16 : Slice face0_R_48 face0_G_48 (subcube 1 4) 4 := slice_direct face0_sl_48_16_ok face0_low_17
lemma face0_sl_48_17_ok : sliceDirectCheck 16 32 0 face0_R_48 face0_G_48 face0_R_1 face0_G_1 = true := by decide +kernel
lemma face0_sl_48_17 : Slice face0_R_48 face0_G_48 (subcube 16 32) 4 := slice_direct face0_sl_48_17_ok face0_low_1
lemma face0_sl_48_18_ok : sliceDirectCheck 1 16 0 face0_R_48 face0_G_48 face0_R_9 face0_G_9 = true := by decide +kernel
lemma face0_sl_48_18 : Slice face0_R_48 face0_G_48 (subcube 1 16) 4 := slice_direct face0_sl_48_18_ok face0_low_9
lemma face0_sl_48_19_ok : sliceDirectCheck 32 16 0 face0_R_48 face0_G_48 face0_R_1 face0_G_1 = true := by decide +kernel
lemma face0_sl_48_19 : Slice face0_R_48 face0_G_48 (subcube 32 16) 4 := slice_direct face0_sl_48_19_ok face0_low_1
lemma face0_sl_48_20_ok : sliceDirectCheck 2 4 0 face0_R_48 face0_G_48 face0_R_16 face0_G_16 = true := by decide +kernel
lemma face0_sl_48_20 : Slice face0_R_48 face0_G_48 (subcube 2 4) 4 := slice_direct face0_sl_48_20_ok face0_low_16
set_option maxRecDepth 200000 in
lemma face0_slices_48_ok : ∀ i (hi : i < face0_slices_48.size), Slice face0_R_48 face0_G_48 face0_slices_48[i].1 face0_slices_48[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice face0_R_48 face0_G_48 p.1 p.2) (forall_cons face0_sl_48_0 (forall_cons face0_sl_48_1 (forall_cons face0_sl_48_2 (forall_cons face0_sl_48_3 (forall_cons face0_sl_48_4 (forall_cons face0_sl_48_5 (forall_cons face0_sl_48_6 (forall_cons face0_sl_48_7 (forall_cons face0_sl_48_8 (forall_cons face0_sl_48_9 (forall_cons face0_sl_48_10 (forall_cons face0_sl_48_11 (forall_cons face0_sl_48_12 (forall_cons face0_sl_48_13 (forall_cons face0_sl_48_14 (forall_cons face0_sl_48_15 (forall_cons face0_sl_48_16 (forall_cons face0_sl_48_17 (forall_cons face0_sl_48_18 (forall_cons face0_sl_48_19 (forall_cons face0_sl_48_20 (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))))))
lemma face0_P_48_ok : ∀ i (hi : i < face0_P_48.size), ∀ c, face0_P_48[i] = some c → ValidPool face0_R_48 face0_G_48 c := buildPools_sound face0_slices_48_ok
lemma face0_bk_48_init_ok : ∀ i (hi : i < face0_bk_0_init.size), ∀ xs ∈ face0_bk_0_init[i], Impossible face0_G_48 (0 - 1) xs.toFinset := by intro i hi; simp [face0_bk_0_init] at hi
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_chk_48_0 : checkNodes face0_W_48 face0_G_48 face0_fmask_48 face0_P_48 face0_autos_48 face0_bk_0_init 0 face0_nodes_0_0 = true := by decide +kernel
def face0_bk_48_0 : Array (List (List Nat)) := buildBuckets 1 face0_W_48 face0_nodes_0_0
lemma face0_bk_48_0_ok : ∀ i (hi : i < face0_bk_48_0.size), ∀ xs ∈ face0_bk_48_0[i], Impossible face0_G_48 0 xs.toFinset :=
  buildBuckets_sound (by decide) face0_gp_48 face0_W_48_ok face0_P_48_ok face0_autos_48_ok face0_bk_48_init_ok face0_chk_48_0
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_chk_48_1 : checkNodes face0_W_48 face0_G_48 face0_fmask_48 face0_P_48 face0_autos_48 face0_bk_48_0 1 face0_nodes_0_0 = true := by decide +kernel
lemma face0_bk_48_1_ok : ∀ i (hi : i < face0_bk_48_0.size), ∀ xs ∈ face0_bk_48_0[i], Impossible face0_G_48 1 xs.toFinset :=
  buildBuckets_sound (by decide) face0_gp_48 face0_W_48_ok face0_P_48_ok face0_autos_48_ok face0_bk_48_0_ok face0_chk_48_1
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_chk_48_2 : checkNodes face0_W_48 face0_G_48 face0_fmask_48 face0_P_48 face0_autos_48 face0_bk_48_0 2 face0_nodes_0_0 = true := by decide +kernel
lemma face0_bk_48_2_ok : ∀ i (hi : i < face0_bk_48_0.size), ∀ xs ∈ face0_bk_48_0[i], Impossible face0_G_48 2 xs.toFinset :=
  buildBuckets_sound (by decide) face0_gp_48 face0_W_48_ok face0_P_48_ok face0_autos_48_ok face0_bk_48_1_ok face0_chk_48_2
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_chk_48_3 : checkNodes face0_W_48 face0_G_48 face0_fmask_48 face0_P_48 face0_autos_48 face0_bk_48_0 3 face0_nodes_0_0 = true := by decide +kernel
lemma face0_bk_48_3_ok : ∀ i (hi : i < face0_bk_48_0.size), ∀ xs ∈ face0_bk_48_0[i], Impossible face0_G_48 3 xs.toFinset :=
  buildBuckets_sound (by decide) face0_gp_48 face0_W_48_ok face0_P_48_ok face0_autos_48_ok face0_bk_48_2_ok face0_chk_48_3
def face0_nodes_48_4 : List NodeSpec := [([22,17,29,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_chk_48_4 : checkNodes face0_W_48 face0_G_48 face0_fmask_48 face0_P_48 face0_autos_48 face0_bk_48_0 4 face0_nodes_48_4 = true := by decide +kernel
def face0_bk_48_4 : Array (List (List Nat)) := buildBuckets 1 face0_W_48 face0_nodes_48_4
lemma face0_bk_48_4_ok : ∀ i (hi : i < face0_bk_48_4.size), ∀ xs ∈ face0_bk_48_4[i], Impossible face0_G_48 4 xs.toFinset :=
  buildBuckets_sound (by decide) face0_gp_48 face0_W_48_ok face0_P_48_ok face0_autos_48_ok face0_bk_48_3_ok face0_chk_48_4
def face0_nodes_48_5 : List NodeSpec := [([7,2,3,8,21,4],[0,1,2],[]),([30,0,1,5,3,4],[3],[]),([0,1,15,25,2,5],[4,5,6,2],[]),([22,0,1,2,3,4],[],[]),([31,0,1,2,3,4],[7,8,9],[]),([22,1,2,17,3,4],[10],[0]),([7,17,29,5,3,4],[11,12,2,13,14],[0,1,2])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_chk_48_5 : checkNodes face0_W_48 face0_G_48 face0_fmask_48 face0_P_48 face0_autos_48 face0_bk_48_4 5 face0_nodes_48_5 = true := by decide +kernel
def face0_bk_48_5 : Array (List (List Nat)) := buildBuckets 3 face0_W_48 face0_nodes_48_5
lemma face0_bk_48_5_ok : ∀ i (hi : i < face0_bk_48_5.size), ∀ xs ∈ face0_bk_48_5[i], Impossible face0_G_48 5 xs.toFinset :=
  buildBuckets_sound (by decide) face0_gp_48 face0_W_48_ok face0_P_48_ok face0_autos_48_ok face0_bk_48_4_ok face0_chk_48_5
def face0_nodes_48_6 : List NodeSpec := [([20,0,1,2,5,3,4],[0,2,6,15,16],[]),([0,1,2,3,8,21,4],[2,5,17,6,18],[0]),([22,0,1,2,3,4],[19,20,10,21,8,7,22,23],[0,3]),([0,1,2,5,3,23,4],[11,8,24],[0]),([0,1,2,24,4],[5,21,6,25],[]),([1,7,2,5,3,8,4],[15,17,0,25,19,26],[0]),([0,1,15,25,2,3,4],[27,0,2,17,25],[0]),([0,1,26,7,2,3,4],[28,19,29,12],[0]),([0,1,7,2,27,3,4],[29,11,5,30,0],[]),([18,0,1,2,5,3,4],[21,12,5,29,15,31],[]),([0,1,2,19,5,3,4],[5,29,6,15,12,0,25,7,8,32],[0]),([22,0,1,7,2,3,4],[19,20,0,23],[]),([0,1,15,7,2,5,4],[33,5,6,7,2,30],[0]),([1,7,2,17,5,3,4],[17,12,15,11,29,34],[0,1]),([22,0,1,2,5,3,4],[5,8,7,35],[]),([28,0,1,7,2,3,4],[7,8,5,17,36,0,30],[]),([7,17,29,3,4],[20,10,12,19,13,14,37],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_chk_48_6 : checkNodes face0_W_48 face0_G_48 face0_fmask_48 face0_P_48 face0_autos_48 face0_bk_48_5 6 face0_nodes_48_6 = true := by decide +kernel
def face0_bk_48_6 : Array (List (List Nat)) := buildBuckets 6 face0_W_48 face0_nodes_48_6
lemma face0_bk_48_6_ok : ∀ i (hi : i < face0_bk_48_6.size), ∀ xs ∈ face0_bk_48_6[i], Impossible face0_G_48 6 xs.toFinset :=
  buildBuckets_sound (by decide) face0_gp_48 face0_W_48_ok face0_P_48_ok face0_autos_48_ok face0_bk_48_5_ok face0_chk_48_6
def face0_nodes_48_7 : List NodeSpec := [([0,1,2,5,3,8,4],[38,5,0,25,15,17,13,11,39],[0,1]),([0,1,2,3,8,4],[5,15,13,25,0,7,2],[]),([9,6,0,1,2,3,4],[5,0,40,41,2,29,11,20,6,12,42,30],[]),([6,10,1,2,3,4],[5,7,19,8,13,30],[]),([0,11,1,2,3,4],[8,0,7,2,5,6,20,21,10,19,13,15,30],[2]),([0,1,12,2,3,4],[6,5,20,12,25,17,40,0,8],[]),([0,1,7,2,5,3,4],[43,2,38,5,6,11,0,25,7,44,8,45,12,29],[0,3,4]),([13,0,1,2,3,4],[5,6,20,21,10,25,0,13],[]),([14,0,1,2,3,4],[5,6,21,10,25,8,0,12],[]),([0,1,15,7,2,3,4],[46,5,12,7,17,2,30,44],[0]),([0,1,15,2,3,4],[17,5,6,7,25,12,40,21,8,0,30],[]),([16,0,1,7,2,3,4],[19,5,20,6,21,12,11,17,29,2,25,41,30],[0]),([1,7,2,17,3,4],[19,12,20,5,10,34,47],[0]),([18,0,1,2,3,4],[10,21,20,19,7,25,8,0,12,13,31,48],[0]),([0,1,2,19,3,4],[5,21,6,25,7,0,8,32,49],[0,4])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_chk_48_7 : checkNodes face0_W_48 face0_G_48 face0_fmask_48 face0_P_48 face0_autos_48 face0_bk_48_6 7 face0_nodes_48_7 = true := by decide +kernel
def face0_bk_48_7 : Array (List (List Nat)) := buildBuckets 6 face0_W_48 face0_nodes_48_7
lemma face0_bk_48_7_ok : ∀ i (hi : i < face0_bk_48_7.size), ∀ xs ∈ face0_bk_48_7[i], Impossible face0_G_48 7 xs.toFinset :=
  buildBuckets_sound (by decide) face0_gp_48 face0_W_48_ok face0_P_48_ok face0_autos_48_ok face0_bk_48_6_ok face0_chk_48_7
def face0_nodes_48_8 : List NodeSpec := [([0,1,2,5,3,4],[43,38,50,0,7,8],[0,1,2,5]),([6,0,1,2,3,4],[7,20,5,40,10,19,8,13,15,30],[0,1,2]),([0,1,7,2,3,4],[20,19,10,12,7,44,8,45],[0,3,4])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_chk_48_8 : checkNodes face0_W_48 face0_G_48 face0_fmask_48 face0_P_48 face0_autos_48 face0_bk_48_7 8 face0_nodes_48_8 = true := by decide +kernel
def face0_bk_48_8 : Array (List (List Nat)) := buildBuckets 2 face0_W_48 face0_nodes_48_8
lemma face0_bk_48_8_ok : ∀ i (hi : i < face0_bk_48_8.size), ∀ xs ∈ face0_bk_48_8[i], Impossible face0_G_48 8 xs.toFinset :=
  buildBuckets_sound (by decide) face0_gp_48 face0_W_48_ok face0_P_48_ok face0_autos_48_ok face0_bk_48_7_ok face0_chk_48_8
def face0_nodes_48_9 : List NodeSpec := [([0,1,2,3,4],[20,19,10,7,8],[0,1,4,2,6,5,7])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_chk_48_9 : checkNodes face0_W_48 face0_G_48 face0_fmask_48 face0_P_48 face0_autos_48 face0_bk_48_8 9 face0_nodes_48_9 = true := by decide +kernel
def face0_bk_48_9 : Array (List (List Nat)) := buildBuckets 1 face0_W_48 face0_nodes_48_9
lemma face0_bk_48_9_ok : ∀ i (hi : i < face0_bk_48_9.size), ∀ xs ∈ face0_bk_48_9[i], Impossible face0_G_48 9 xs.toFinset :=
  buildBuckets_sound (by decide) face0_gp_48 face0_W_48_ok face0_P_48_ok face0_autos_48_ok face0_bk_48_8_ok face0_chk_48_9
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_forestRoot_48_ok : forestRootCheck face0_R_48 face0_G_48 [(VAR 0,19,18),(VAR 1,19,17),(VAR 2,21,17),(VAR 4,19,3),(VAR 5,35,3)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face0_forestRoot_48_in : bucketContains face0_bk_48_9 face0_R_48 = true := by decide +kernel
lemma face0_low_48 : Lower face0_R_48 face0_G_48 10 := lower_of_forest face0_forestRoot_48_ok face0_bk_48_9_ok face0_forestRoot_48_in
def face1_Cofactor12086_pos_0 : List Nat := [6,6,18,18,20,20,6,18,20]
def face1_Cofactor12086_neg_0 : List Nat := [4,2,16,2,16,4,16,4,2]
def face1_Cofactor12086_base_0 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xcf,0x10a),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x173,0xa1),(0xffff0000ffff0000ffff0000ffff0000,0x1bc,0x54)]
def face1_Cofactor12086_W_0 : BT Decor := buildWiresBT 2 face1_Cofactor12086_base_0 face0_steps_0
def face1_Cofactor12086_autosL_0 : List (List (Nat × Nat)) := []
def face1_Cofactor12086_autos_0 : BT (List (Nat × Nat)) := btOfList 1 face1_Cofactor12086_autosL_0
def face1_Cofactor12086_slicesL_0 : List (Option (Nat × Nat)) := []
def face1_Cofactor12086_slices_0 : BT (Option (Nat × Nat)) := btOfList 1 face1_Cofactor12086_slicesL_0
def face1_Cofactor12086_P_0 : BT (Option BoundPool) := buildPoolsBT 1 face1_Cofactor12086_W_0 face0_R_8 face1_Cofactor12086_slices_0 face0_ps_0
lemma face1_Cofactor12086_gp_0 : goodPairs face0_G_8 face1_Cofactor12086_pos_0 face1_Cofactor12086_neg_0 := goodPairs_of (by decide +kernel)
lemma face1_Cofactor12086_base_0_ok : ∀ x ∈ face1_Cofactor12086_base_0, faithful face1_Cofactor12086_pos_0 face1_Cofactor12086_neg_0 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma face1_Cofactor12086_W_0_ok : btAll (fun x => faithful face1_Cofactor12086_pos_0 face1_Cofactor12086_neg_0 x ∧ x.1 < 2^128) face1_Cofactor12086_W_0 := buildWiresBT_faithful face1_Cofactor12086_base_0_ok
set_option maxRecDepth 500000 in
lemma face1_Cofactor12086_autos_0_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw face0_G_8 = face0_G_8) face1_Cofactor12086_autos_0 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma face1_Cofactor12086_slices_0_ok : btAll (fun o => ∀ p, o = some p → Slice face0_R_8 face0_G_8 p.1 p.2) face1_Cofactor12086_slices_0 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice face0_R_8 face0_G_8 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 500000 in
lemma face1_Cofactor12086_P_0_ok : btAll (fun o => ∀ c, o = some c → ValidPool face0_R_8 face0_G_8 c) face1_Cofactor12086_P_0 := buildPoolsBT_sound face1_Cofactor12086_slices_0_ok
def face1_Cofactor12086_bk_0_init : BT (List (List Nat)) := BT.empty
lemma face1_Cofactor12086_bk_0_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face0_G_8 (0 - 1) xs.toFinset) face1_Cofactor12086_bk_0_init := trivial
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face1_Cofactor12086_chk_0_0 : checkNodesBT face1_Cofactor12086_W_0 face0_G_8 face0_fmask_0 face1_Cofactor12086_P_0 face1_Cofactor12086_autos_0 face1_Cofactor12086_bk_0_init 0 face0_nodes_0_0 = true := by decide +kernel
def face1_Cofactor12086_bk_0_0 : BT (List (List Nat)) := buildBucketsBT face1_Cofactor12086_W_0 face0_nodes_0_0
set_option maxRecDepth 500000 in
lemma face1_Cofactor12086_bk_0_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face0_G_8 0 xs.toFinset) face1_Cofactor12086_bk_0_0 :=
  buildBucketsBT_sound (by decide) face1_Cofactor12086_gp_0 face1_Cofactor12086_W_0_ok face1_Cofactor12086_P_0_ok face1_Cofactor12086_autos_0_ok face1_Cofactor12086_bk_0_init_ok face1_Cofactor12086_chk_0_0
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face1_Cofactor12086_chk_0_1 : checkNodesBT face1_Cofactor12086_W_0 face0_G_8 face0_fmask_0 face1_Cofactor12086_P_0 face1_Cofactor12086_autos_0 face1_Cofactor12086_bk_0_0 1 face0_nodes_0_0 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma face1_Cofactor12086_bk_0_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face0_G_8 1 xs.toFinset) face1_Cofactor12086_bk_0_0 :=
  buildBucketsBT_sound (by decide) face1_Cofactor12086_gp_0 face1_Cofactor12086_W_0_ok face1_Cofactor12086_P_0_ok face1_Cofactor12086_autos_0_ok face1_Cofactor12086_bk_0_0_ok face1_Cofactor12086_chk_0_1
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face1_Cofactor12086_chk_0_2 : checkNodesBT face1_Cofactor12086_W_0 face0_G_8 face0_fmask_0 face1_Cofactor12086_P_0 face1_Cofactor12086_autos_0 face1_Cofactor12086_bk_0_0 2 face0_nodes_0_0 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma face1_Cofactor12086_bk_0_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face0_G_8 2 xs.toFinset) face1_Cofactor12086_bk_0_0 :=
  buildBucketsBT_sound (by decide) face1_Cofactor12086_gp_0 face1_Cofactor12086_W_0_ok face1_Cofactor12086_P_0_ok face1_Cofactor12086_autos_0_ok face1_Cofactor12086_bk_0_1_ok face1_Cofactor12086_chk_0_2
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face1_Cofactor12086_chk_0_3 : checkNodesBT face1_Cofactor12086_W_0 face0_G_8 face0_fmask_0 face1_Cofactor12086_P_0 face1_Cofactor12086_autos_0 face1_Cofactor12086_bk_0_0 3 face0_nodes_0_3 = true := by decide +kernel
def face1_Cofactor12086_bk_0_3 : BT (List (List Nat)) := buildBucketsBT face1_Cofactor12086_W_0 face0_nodes_0_3
set_option maxRecDepth 500000 in
lemma face1_Cofactor12086_bk_0_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face0_G_8 3 xs.toFinset) face1_Cofactor12086_bk_0_3 :=
  buildBucketsBT_sound (by decide) face1_Cofactor12086_gp_0 face1_Cofactor12086_W_0_ok face1_Cofactor12086_P_0_ok face1_Cofactor12086_autos_0_ok face1_Cofactor12086_bk_0_2_ok face1_Cofactor12086_chk_0_3
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma face1_Cofactor12086_treeRoot_0_ok : forestRootCheck face0_R_8 face0_G_8 [(VAR 1,6,4),(VAR 2,6,2),(VAR 4,18,2)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma face1_Cofactor12086_treeRoot_0_in : bucketContainsBT face1_Cofactor12086_bk_0_3 face0_R_8 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma face1_Cofactor12086_low_0 : Lower face0_R_8 face0_G_8 4 := lower_of_forestBT face1_Cofactor12086_treeRoot_0_ok face1_Cofactor12086_bk_0_3_ok face1_Cofactor12086_treeRoot_0_in

def face1_h4Pos : List Nat := [34,36,6,6,36,34]
def face1_h4Neg : List Nat := [32,32,2,4,4,2]
def face1_h4Mask : Nat := fullMask 6
def face1_h4Base : List Decor := [(0xcccccccccccccccccccccccccccccccc,45,36),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,30,24),(0xffffffff00000000ffffffff00000000,51,3)]
def face1_h4W : BT Decor := buildWiresBT 2 face1_h4Base face0_steps_0
def face1_h4AutoList : List (List (Nat × Nat)) := [[]]
def face1_h4Autos : BT (List (Nat × Nat)) := btOfList 1 face1_h4AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h4Pairs : goodPairs face0_G_9 face1_h4Pos face1_h4Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h4BaseOk : ∀ x ∈ face1_h4Base, faithful face1_h4Pos face1_h4Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h4WOk : btAll (fun x => faithful face1_h4Pos face1_h4Neg x ∧ x.1 < 2^128) face1_h4W := buildWiresBT_faithful face1_h4BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h4AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw face0_G_9 = face0_G_9) face1_h4Autos := btAll_ofList (autos_of (by decide +kernel))
def face1_h4Pools : BT (Option BoundPool) := buildPoolsBT 1 face1_h4W face0_R_9 face1_Cofactor12086_slices_0 face0_ps_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h4SlicesOk : btAll (fun o => ∀ p, o = some p → Slice face0_R_9 face0_G_9 p.1 p.2) face1_Cofactor12086_slices_0 := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice face0_R_9 face0_G_9 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h4PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool face0_R_9 face0_G_9 c) face1_h4Pools := buildPoolsBT_sound face1_h4SlicesOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h4EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible face0_G_9 (3 - 1) xs.toFinset) face1_Cofactor12086_bk_0_init := trivial
def face1_h4Block3_0 : List NodeSpec := [([0,1,2],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h4Test3_0 : checkNodesBT face1_h4W face0_G_9 face1_h4Mask face1_h4Pools face1_h4Autos face1_Cofactor12086_bk_0_init 3 face1_h4Block3_0 = true := by decide +kernel
def face1_h4Nodes3 : List NodeSpec := face1_h4Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h4Check3 : checkNodesBT face1_h4W face0_G_9 face1_h4Mask face1_h4Pools face1_h4Autos face1_Cofactor12086_bk_0_init 3 face1_h4Nodes3 = true := face1_h4Test3_0
def face1_h4Bucket3 : BT (List (List Nat)) := buildBucketsBT face1_h4W face1_h4Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h4Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face0_G_9 3 xs.toFinset) face1_h4Bucket3 := buildBucketsBT_sound (by decide) face1_h4Pairs face1_h4WOk face1_h4PoolsOk face1_h4AutosOk face1_h4EmptyOk face1_h4Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h4Bound : Lower face0_R_9 face0_G_9 4 := lower_of_forestBT (essPairs := [(VAR 1,4,6),(VAR 2,2,6),(VAR 5,2,34)]) (by decide +kernel) face1_h4Bucket3Ok (by decide +kernel)
def face1_Cofactor12086_G_8 : Nat := 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0
def face1_Cofactor12086_R_8 : List Nat := varsOf 14
lemma face1_Cofactor12086_low_8_ok : carryOK [(3,4)] face1_Cofactor12086_R_8 face1_Cofactor12086_G_8 face0_R_8 face0_G_8 = true := by decide +kernel
lemma face1_Cofactor12086_low_8 : Lower face1_Cofactor12086_R_8 face1_Cofactor12086_G_8 4 := carry_of face1_Cofactor12086_low_8_ok face1_Cofactor12086_low_0

lemma face1_Cofactor12086_low_9_ok : carryOK [(4,5)] face0_R_9 face0_G_9 face0_R_8 face0_G_8 = true := by decide +kernel
lemma face1_Cofactor12086_low_9 : Lower face0_R_9 face0_G_9 4 := carry_of face1_Cofactor12086_low_9_ok face1_Cofactor12086_low_0

def face1_Cofactor12086_G_11 : Nat := 0xffccffcccc00cc00ffccffcccc00cc00
def face1_Cofactor12086_R_11 : List Nat := varsOf 42
lemma face1_Cofactor12086_low_11_ok : carryOK [(4,5),(2,3)] face1_Cofactor12086_R_11 face1_Cofactor12086_G_11 face0_R_8 face0_G_8 = true := by decide +kernel
lemma face1_Cofactor12086_low_11 : Lower face1_Cofactor12086_R_11 face1_Cofactor12086_G_11 4 := carry_of face1_Cofactor12086_low_11_ok face1_Cofactor12086_low_0

lemma face1_Cofactor12086_low_12_ok : carryOK [(4,5),(1,2),(1,3)] face0_R_15 face0_G_15 face0_R_8 face0_G_8 = true := by decide +kernel
lemma face1_Cofactor12086_low_12 : Lower face0_R_15 face0_G_15 4 := carry_of face1_Cofactor12086_low_12_ok face1_Cofactor12086_low_0

def face1_Cofactor12086_G_14 : Nat := 0xfcc0fcc0c000c000fcc0fcc0c000c000
def face1_Cofactor12086_R_14 : List Nat := varsOf 46
def face1_Cofactor12086_pos_14 : List Nat := [14,14,14,38,38,38,42,42,42,44,44,44,14,14,14,38,38,38,42,42,42,44,44,44]
def face1_Cofactor12086_neg_14 : List Nat := [12,10,6,36,34,6,40,34,10,40,36,12,34,36,40,10,12,40,6,12,36,6,10,34]
def face1_Cofactor12086_base_14 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0x1ff1ff,0xe491b6),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xe3fe3f,0x3d2c2d),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xfc7fc7,0x4bcb43),(0xffffffff00000000ffffffff00000000,0xff8ff8,0x9276d8)]
def face1_Cofactor12086_W_14 : BT Decor := buildWiresBT 4 face1_Cofactor12086_base_14 face0_steps_21
def face1_Cofactor12086_autosL_14 : List (List (Nat × Nat)) := [[],[(3,5)],[(1,2)],[(3,5),(1,2)],[(2,3)],[(2,5),(2,3)],[(1,2),(1,3)],[(2,5),(1,2),(1,3)],[(2,5),(1,3)]]
def face1_Cofactor12086_autos_14 : BT (List (Nat × Nat)) := btOfList 4 face1_Cofactor12086_autosL_14
def face1_Cofactor12086_slicesL_14 : List (Option (Nat × Nat)) := [some (subcubeFast 0 8,4),some (subcubeFast 0 2,4),some (subcubeFast 0 4,4),some (subcubeFast 0 32,4)]
def face1_Cofactor12086_slices_14 : BT (Option (Nat × Nat)) := btOfList 2 face1_Cofactor12086_slicesL_14
def face1_Cofactor12086_P_14 : BT (Option BoundPool) := buildPoolsBT 2 face1_Cofactor12086_W_14 face1_Cofactor12086_R_14 face1_Cofactor12086_slices_14 face0_ps_20
lemma face1_Cofactor12086_gp_14 : goodPairs face1_Cofactor12086_G_14 face1_Cofactor12086_pos_14 face1_Cofactor12086_neg_14 := goodPairs_of (by decide +kernel)
lemma face1_Cofactor12086_base_14_ok : ∀ x ∈ face1_Cofactor12086_base_14, faithful face1_Cofactor12086_pos_14 face1_Cofactor12086_neg_14 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma face1_Cofactor12086_W_14_ok : btAll (fun x => faithful face1_Cofactor12086_pos_14 face1_Cofactor12086_neg_14 x ∧ x.1 < 2^128) face1_Cofactor12086_W_14 := buildWiresBT_faithful face1_Cofactor12086_base_14_ok
set_option maxRecDepth 500000 in
lemma face1_Cofactor12086_autos_14_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw face1_Cofactor12086_G_14 = face1_Cofactor12086_G_14) face1_Cofactor12086_autos_14 := btAll_ofList (autos_of (by decide +kernel))
lemma face1_Cofactor12086_sl_14_0_ok : sliceDirectCheck 0 8 0 face1_Cofactor12086_R_14 face1_Cofactor12086_G_14 face0_R_9 face0_G_9 = true := by decide +kernel
lemma face1_Cofactor12086_sl_14_0 : Slice face1_Cofactor12086_R_14 face1_Cofactor12086_G_14 (subcubeFast 0 8) 4 := slice_fast_direct face1_Cofactor12086_sl_14_0_ok face1_Cofactor12086_low_9
lemma face1_Cofactor12086_sl_14_1_ok : sliceDirectCheck 0 2 0 face1_Cofactor12086_R_14 face1_Cofactor12086_G_14 face0_R_15 face0_G_15 = true := by decide +kernel
lemma face1_Cofactor12086_sl_14_1 : Slice face1_Cofactor12086_R_14 face1_Cofactor12086_G_14 (subcubeFast 0 2) 4 := slice_fast_direct face1_Cofactor12086_sl_14_1_ok face1_Cofactor12086_low_12
lemma face1_Cofactor12086_sl_14_2_ok : sliceDirectCheck 0 4 0 face1_Cofactor12086_R_14 face1_Cofactor12086_G_14 face1_Cofactor12086_R_11 face1_Cofactor12086_G_11 = true := by decide +kernel
lemma face1_Cofactor12086_sl_14_2 : Slice face1_Cofactor12086_R_14 face1_Cofactor12086_G_14 (subcubeFast 0 4) 4 := slice_fast_direct face1_Cofactor12086_sl_14_2_ok face1_Cofactor12086_low_11
lemma face1_Cofactor12086_sl_14_3_ok : sliceDirectCheck 0 32 0 face1_Cofactor12086_R_14 face1_Cofactor12086_G_14 face1_Cofactor12086_R_8 face1_Cofactor12086_G_8 = true := by decide +kernel
lemma face1_Cofactor12086_sl_14_3 : Slice face1_Cofactor12086_R_14 face1_Cofactor12086_G_14 (subcubeFast 0 32) 4 := slice_fast_direct face1_Cofactor12086_sl_14_3_ok face1_Cofactor12086_low_8
set_option maxRecDepth 500000 in
lemma face1_Cofactor12086_slices_14_ok : btAll (fun o => ∀ p, o = some p → Slice face1_Cofactor12086_R_14 face1_Cofactor12086_G_14 p.1 p.2) face1_Cofactor12086_slices_14 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice face1_Cofactor12086_R_14 face1_Cofactor12086_G_14 p.1 p.2) (forall_cons (fun _ h => by cases h; exact face1_Cofactor12086_sl_14_0) (forall_cons (fun _ h => by cases h; exact face1_Cofactor12086_sl_14_1) (forall_cons (fun _ h => by cases h; exact face1_Cofactor12086_sl_14_2) (forall_cons (fun _ h => by cases h; exact face1_Cofactor12086_sl_14_3) (fun _ h => (List.not_mem_nil h).elim)))))
set_option maxRecDepth 500000 in
lemma face1_Cofactor12086_P_14_ok : btAll (fun o => ∀ c, o = some c → ValidPool face1_Cofactor12086_R_14 face1_Cofactor12086_G_14 c) face1_Cofactor12086_P_14 := buildPoolsBT_sound face1_Cofactor12086_slices_14_ok
lemma face1_Cofactor12086_bk_14_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face1_Cofactor12086_G_14 (0 - 1) xs.toFinset) face1_Cofactor12086_bk_0_init := trivial
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face1_Cofactor12086_chk_14_0 : checkNodesBT face1_Cofactor12086_W_14 face1_Cofactor12086_G_14 face0_fmask_20 face1_Cofactor12086_P_14 face1_Cofactor12086_autos_14 face1_Cofactor12086_bk_0_init 0 face0_nodes_0_0 = true := by decide +kernel
def face1_Cofactor12086_bk_14_0 : BT (List (List Nat)) := buildBucketsBT face1_Cofactor12086_W_14 face0_nodes_0_0
set_option maxRecDepth 500000 in
lemma face1_Cofactor12086_bk_14_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face1_Cofactor12086_G_14 0 xs.toFinset) face1_Cofactor12086_bk_14_0 :=
  buildBucketsBT_sound (by decide) face1_Cofactor12086_gp_14 face1_Cofactor12086_W_14_ok face1_Cofactor12086_P_14_ok face1_Cofactor12086_autos_14_ok face1_Cofactor12086_bk_14_init_ok face1_Cofactor12086_chk_14_0
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face1_Cofactor12086_chk_14_1 : checkNodesBT face1_Cofactor12086_W_14 face1_Cofactor12086_G_14 face0_fmask_20 face1_Cofactor12086_P_14 face1_Cofactor12086_autos_14 face1_Cofactor12086_bk_14_0 1 face0_nodes_0_0 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma face1_Cofactor12086_bk_14_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face1_Cofactor12086_G_14 1 xs.toFinset) face1_Cofactor12086_bk_14_0 :=
  buildBucketsBT_sound (by decide) face1_Cofactor12086_gp_14 face1_Cofactor12086_W_14_ok face1_Cofactor12086_P_14_ok face1_Cofactor12086_autos_14_ok face1_Cofactor12086_bk_14_0_ok face1_Cofactor12086_chk_14_1
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face1_Cofactor12086_chk_14_2 : checkNodesBT face1_Cofactor12086_W_14 face1_Cofactor12086_G_14 face0_fmask_20 face1_Cofactor12086_P_14 face1_Cofactor12086_autos_14 face1_Cofactor12086_bk_14_0 2 face0_nodes_0_0 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma face1_Cofactor12086_bk_14_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face1_Cofactor12086_G_14 2 xs.toFinset) face1_Cofactor12086_bk_14_0 :=
  buildBucketsBT_sound (by decide) face1_Cofactor12086_gp_14 face1_Cofactor12086_W_14_ok face1_Cofactor12086_P_14_ok face1_Cofactor12086_autos_14_ok face1_Cofactor12086_bk_14_1_ok face1_Cofactor12086_chk_14_2
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face1_Cofactor12086_chk_14_3 : checkNodesBT face1_Cofactor12086_W_14 face1_Cofactor12086_G_14 face0_fmask_20 face1_Cofactor12086_P_14 face1_Cofactor12086_autos_14 face1_Cofactor12086_bk_14_0 3 face0_nodes_21_3 = true := by decide +kernel
def face1_Cofactor12086_bk_14_3 : BT (List (List Nat)) := buildBucketsBT face1_Cofactor12086_W_14 face0_nodes_21_3
set_option maxRecDepth 500000 in
lemma face1_Cofactor12086_bk_14_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face1_Cofactor12086_G_14 3 xs.toFinset) face1_Cofactor12086_bk_14_3 :=
  buildBucketsBT_sound (by decide) face1_Cofactor12086_gp_14 face1_Cofactor12086_W_14_ok face1_Cofactor12086_P_14_ok face1_Cofactor12086_autos_14_ok face1_Cofactor12086_bk_14_2_ok face1_Cofactor12086_chk_14_3
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face1_Cofactor12086_chk_14_4 : checkNodesBT face1_Cofactor12086_W_14 face1_Cofactor12086_G_14 face0_fmask_20 face1_Cofactor12086_P_14 face1_Cofactor12086_autos_14 face1_Cofactor12086_bk_14_3 4 face0_nodes_21_4 = true := by decide +kernel
def face1_Cofactor12086_bk_14_4 : BT (List (List Nat)) := buildBucketsBT face1_Cofactor12086_W_14 face0_nodes_21_4
set_option maxRecDepth 500000 in
lemma face1_Cofactor12086_bk_14_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face1_Cofactor12086_G_14 4 xs.toFinset) face1_Cofactor12086_bk_14_4 :=
  buildBucketsBT_sound (by decide) face1_Cofactor12086_gp_14 face1_Cofactor12086_W_14_ok face1_Cofactor12086_P_14_ok face1_Cofactor12086_autos_14_ok face1_Cofactor12086_bk_14_3_ok face1_Cofactor12086_chk_14_4
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face1_Cofactor12086_chk_14_5 : checkNodesBT face1_Cofactor12086_W_14 face1_Cofactor12086_G_14 face0_fmask_20 face1_Cofactor12086_P_14 face1_Cofactor12086_autos_14 face1_Cofactor12086_bk_14_4 5 face0_nodes_21_5 = true := by decide +kernel
def face1_Cofactor12086_bk_14_5 : BT (List (List Nat)) := buildBucketsBT face1_Cofactor12086_W_14 face0_nodes_21_5
set_option maxRecDepth 500000 in
lemma face1_Cofactor12086_bk_14_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face1_Cofactor12086_G_14 5 xs.toFinset) face1_Cofactor12086_bk_14_5 :=
  buildBucketsBT_sound (by decide) face1_Cofactor12086_gp_14 face1_Cofactor12086_W_14_ok face1_Cofactor12086_P_14_ok face1_Cofactor12086_autos_14_ok face1_Cofactor12086_bk_14_4_ok face1_Cofactor12086_chk_14_5
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face1_Cofactor12086_chk_14_6 : checkNodesBT face1_Cofactor12086_W_14 face1_Cofactor12086_G_14 face0_fmask_20 face1_Cofactor12086_P_14 face1_Cofactor12086_autos_14 face1_Cofactor12086_bk_14_5 6 face0_nodes_21_6 = true := by decide +kernel
def face1_Cofactor12086_bk_14_6 : BT (List (List Nat)) := buildBucketsBT face1_Cofactor12086_W_14 face0_nodes_21_6
set_option maxRecDepth 500000 in
lemma face1_Cofactor12086_bk_14_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face1_Cofactor12086_G_14 6 xs.toFinset) face1_Cofactor12086_bk_14_6 :=
  buildBucketsBT_sound (by decide) face1_Cofactor12086_gp_14 face1_Cofactor12086_W_14_ok face1_Cofactor12086_P_14_ok face1_Cofactor12086_autos_14_ok face1_Cofactor12086_bk_14_5_ok face1_Cofactor12086_chk_14_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma face1_Cofactor12086_treeRoot_14_ok : forestRootCheck face1_Cofactor12086_R_14 face1_Cofactor12086_G_14 [(VAR 1,14,12),(VAR 2,14,10),(VAR 3,14,6),(VAR 5,38,6)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma face1_Cofactor12086_treeRoot_14_in : bucketContainsBT face1_Cofactor12086_bk_14_6 face1_Cofactor12086_R_14 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma face1_Cofactor12086_low_14 : Lower face1_Cofactor12086_R_14 face1_Cofactor12086_G_14 7 := lower_of_forestBT face1_Cofactor12086_treeRoot_14_ok face1_Cofactor12086_bk_14_6_ok face1_Cofactor12086_treeRoot_14_in

def face1_h5G : Nat := 0xe8e8e8e880808080e8e8e8e880808080
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h5Bound : Lower face0_R_19 face1_h5G 7 := carry_of (swaps := [(0,1),(1,2),(2,3)]) (roots2 := face1_Cofactor12086_R_14) (T2 := face1_Cofactor12086_G_14) (by decide +kernel) face1_Cofactor12086_low_14
def face1_h6Pos : List Nat := [36,40,12,12,40,36]
def face1_h6Neg : List Nat := [32,32,4,8,8,4]
def face1_h6Base : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,45,36),(0xff00ff00ff00ff00ff00ff00ff00ff00,30,24),(0xffffffff00000000ffffffff00000000,51,3)]
def face1_h6W : BT Decor := buildWiresBT 2 face1_h6Base face0_steps_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h6Pairs : goodPairs face0_G_15 face1_h6Pos face1_h6Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h6BaseOk : ∀ x ∈ face1_h6Base, faithful face1_h6Pos face1_h6Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h6WOk : btAll (fun x => faithful face1_h6Pos face1_h6Neg x ∧ x.1 < 2^128) face1_h6W := buildWiresBT_faithful face1_h6BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h6AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw face0_G_15 = face0_G_15) face1_h4Autos := btAll_ofList (autos_of (by decide +kernel))
def face1_h6Pools : BT (Option BoundPool) := buildPoolsBT 1 face1_h6W face0_R_15 face1_Cofactor12086_slices_0 face0_ps_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h6SlicesOk : btAll (fun o => ∀ p, o = some p → Slice face0_R_15 face0_G_15 p.1 p.2) face1_Cofactor12086_slices_0 := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice face0_R_15 face0_G_15 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h6PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool face0_R_15 face0_G_15 c) face1_h6Pools := buildPoolsBT_sound face1_h6SlicesOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h6EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible face0_G_15 (3 - 1) xs.toFinset) face1_Cofactor12086_bk_0_init := trivial
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h6Test3_0 : checkNodesBT face1_h6W face0_G_15 face1_h4Mask face1_h6Pools face1_h4Autos face1_Cofactor12086_bk_0_init 3 face1_h4Block3_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h6Check3 : checkNodesBT face1_h6W face0_G_15 face1_h4Mask face1_h6Pools face1_h4Autos face1_Cofactor12086_bk_0_init 3 face1_h4Nodes3 = true := face1_h6Test3_0
def face1_h6Bucket3 : BT (List (List Nat)) := buildBucketsBT face1_h6W face1_h4Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h6Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face0_G_15 3 xs.toFinset) face1_h6Bucket3 := buildBucketsBT_sound (by decide) face1_h6Pairs face1_h6WOk face1_h6PoolsOk face1_h6AutosOk face1_h6EmptyOk face1_h6Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h6Bound : Lower face0_R_15 face0_G_15 4 := lower_of_forestBT (essPairs := [(VAR 2,8,12),(VAR 3,4,12),(VAR 5,4,36)]) (by decide +kernel) face1_h6Bucket3Ok (by decide +kernel)
def face1_h7G : Nat := 0xccc0ccc0c000c000ccc0ccc0c000c000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h7Bound : Lower face1_Cofactor12086_R_14 face1_h7G 5 := lift_of (z := 0) (o := 2) (essPairs := [(VAR 1,12,14)]) (by decide +kernel) face1_h6Bound
def face1_h8G : Nat := 0xfcfcfcfcf0c0f0c0fcfcfcfcf0c0f0c0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h8Bound : Lower face1_Cofactor12086_R_14 face1_h8G 5 := lift_of (z := 8) (o := 0) (essPairs := [(VAR 3,4,12)]) (by decide +kernel) face1_h4Bound
def face1_h10R : List Nat := varsOf 11
def face1_h10G : Nat := 0xee88ee88ee88ee88ee88ee88ee88ee88
def face1_h10Pos : List Nat := [9,10,3,3,10,9]
def face1_h10Neg : List Nat := [8,8,1,2,2,1]
def face1_h10Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,45,36),(0xcccccccccccccccccccccccccccccccc,30,24),(0xff00ff00ff00ff00ff00ff00ff00ff00,51,3)]
def face1_h10W : BT Decor := buildWiresBT 2 face1_h10Base face0_steps_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h10Pairs : goodPairs face1_h10G face1_h10Pos face1_h10Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h10BaseOk : ∀ x ∈ face1_h10Base, faithful face1_h10Pos face1_h10Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h10WOk : btAll (fun x => faithful face1_h10Pos face1_h10Neg x ∧ x.1 < 2^128) face1_h10W := buildWiresBT_faithful face1_h10BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h10AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw face1_h10G = face1_h10G) face1_h4Autos := btAll_ofList (autos_of (by decide +kernel))
def face1_h10Pools : BT (Option BoundPool) := buildPoolsBT 1 face1_h10W face1_h10R face1_Cofactor12086_slices_0 face0_ps_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h10SlicesOk : btAll (fun o => ∀ p, o = some p → Slice face1_h10R face1_h10G p.1 p.2) face1_Cofactor12086_slices_0 := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice face1_h10R face1_h10G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h10PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool face1_h10R face1_h10G c) face1_h10Pools := buildPoolsBT_sound face1_h10SlicesOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h10EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible face1_h10G (3 - 1) xs.toFinset) face1_Cofactor12086_bk_0_init := trivial
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h10Test3_0 : checkNodesBT face1_h10W face1_h10G face1_h4Mask face1_h10Pools face1_h4Autos face1_Cofactor12086_bk_0_init 3 face1_h4Block3_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h10Check3 : checkNodesBT face1_h10W face1_h10G face1_h4Mask face1_h10Pools face1_h4Autos face1_Cofactor12086_bk_0_init 3 face1_h4Nodes3 = true := face1_h10Test3_0
def face1_h10Bucket3 : BT (List (List Nat)) := buildBucketsBT face1_h10W face1_h4Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h10Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face1_h10G 3 xs.toFinset) face1_h10Bucket3 := buildBucketsBT_sound (by decide) face1_h10Pairs face1_h10WOk face1_h10PoolsOk face1_h10AutosOk face1_h10EmptyOk face1_h10Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h10Bound : Lower face1_h10R face1_h10G 4 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 3,1,9)]) (by decide +kernel) face1_h10Bucket3Ok (by decide +kernel)
def face1_h11R : List Nat := varsOf 15
def face1_h11G : Nat := 0xe080e080e080e080e080e080e080e080
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h11Bound : Lower face1_h11R face1_h11G 5 := lift_of (z := 0) (o := 4) (essPairs := [(VAR 2,3,7)]) (by decide +kernel) face1_h10Bound
def face1_h12Pos : List Nat := [5,6,3,3,6,5]
def face1_h12Neg : List Nat := [4,4,1,2,2,1]
def face1_h12Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,45,36),(0xcccccccccccccccccccccccccccccccc,30,24),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,51,3)]
def face1_h12W : BT Decor := buildWiresBT 2 face1_h12Base face0_steps_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h12Pairs : goodPairs face0_G_1 face1_h12Pos face1_h12Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h12BaseOk : ∀ x ∈ face1_h12Base, faithful face1_h12Pos face1_h12Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h12WOk : btAll (fun x => faithful face1_h12Pos face1_h12Neg x ∧ x.1 < 2^128) face1_h12W := buildWiresBT_faithful face1_h12BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h12AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw face0_G_1 = face0_G_1) face1_h4Autos := btAll_ofList (autos_of (by decide +kernel))
def face1_h12Pools : BT (Option BoundPool) := buildPoolsBT 1 face1_h12W face0_R_1 face1_Cofactor12086_slices_0 face0_ps_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h12SlicesOk : btAll (fun o => ∀ p, o = some p → Slice face0_R_1 face0_G_1 p.1 p.2) face1_Cofactor12086_slices_0 := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice face0_R_1 face0_G_1 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h12PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool face0_R_1 face0_G_1 c) face1_h12Pools := buildPoolsBT_sound face1_h12SlicesOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h12EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible face0_G_1 (3 - 1) xs.toFinset) face1_Cofactor12086_bk_0_init := trivial
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h12Test3_0 : checkNodesBT face1_h12W face0_G_1 face1_h4Mask face1_h12Pools face1_h4Autos face1_Cofactor12086_bk_0_init 3 face1_h4Block3_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h12Check3 : checkNodesBT face1_h12W face0_G_1 face1_h4Mask face1_h12Pools face1_h4Autos face1_Cofactor12086_bk_0_init 3 face1_h4Nodes3 = true := face1_h12Test3_0
def face1_h12Bucket3 : BT (List (List Nat)) := buildBucketsBT face1_h12W face1_h4Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h12Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face0_G_1 3 xs.toFinset) face1_h12Bucket3 := buildBucketsBT_sound (by decide) face1_h12Pairs face1_h12WOk face1_h12PoolsOk face1_h12AutosOk face1_h12EmptyOk face1_h12Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h12Bound : Lower face0_R_1 face0_G_1 4 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5)]) (by decide +kernel) face1_h12Bucket3Ok (by decide +kernel)
def face1_h13Pos : List Nat := [33,34,3,3,34,33]
def face1_h13Neg : List Nat := [32,32,1,2,2,1]
def face1_h13Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,45,36),(0xcccccccccccccccccccccccccccccccc,30,24),(0xffffffff00000000ffffffff00000000,51,3)]
def face1_h13W : BT Decor := buildWiresBT 2 face1_h13Base face0_steps_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h13Pairs : goodPairs face0_G_3 face1_h13Pos face1_h13Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h13BaseOk : ∀ x ∈ face1_h13Base, faithful face1_h13Pos face1_h13Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h13WOk : btAll (fun x => faithful face1_h13Pos face1_h13Neg x ∧ x.1 < 2^128) face1_h13W := buildWiresBT_faithful face1_h13BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h13AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw face0_G_3 = face0_G_3) face1_h4Autos := btAll_ofList (autos_of (by decide +kernel))
def face1_h13Pools : BT (Option BoundPool) := buildPoolsBT 1 face1_h13W face0_R_3 face1_Cofactor12086_slices_0 face0_ps_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h13SlicesOk : btAll (fun o => ∀ p, o = some p → Slice face0_R_3 face0_G_3 p.1 p.2) face1_Cofactor12086_slices_0 := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice face0_R_3 face0_G_3 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h13PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool face0_R_3 face0_G_3 c) face1_h13Pools := buildPoolsBT_sound face1_h13SlicesOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h13EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible face0_G_3 (3 - 1) xs.toFinset) face1_Cofactor12086_bk_0_init := trivial
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h13Test3_0 : checkNodesBT face1_h13W face0_G_3 face1_h4Mask face1_h13Pools face1_h4Autos face1_Cofactor12086_bk_0_init 3 face1_h4Block3_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h13Check3 : checkNodesBT face1_h13W face0_G_3 face1_h4Mask face1_h13Pools face1_h4Autos face1_Cofactor12086_bk_0_init 3 face1_h4Nodes3 = true := face1_h13Test3_0
def face1_h13Bucket3 : BT (List (List Nat)) := buildBucketsBT face1_h13W face1_h4Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h13Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face0_G_3 3 xs.toFinset) face1_h13Bucket3 := buildBucketsBT_sound (by decide) face1_h13Pairs face1_h13WOk face1_h13PoolsOk face1_h13AutosOk face1_h13EmptyOk face1_h13Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h13Bound : Lower face0_R_3 face0_G_3 4 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 5,1,33)]) (by decide +kernel) face1_h13Bucket3Ok (by decide +kernel)
def face1_h14Pos : List Nat := [33,36,5,5,36,33]
def face1_h14Neg : List Nat := [32,32,1,4,4,1]
def face1_h14Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,45,36),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,30,24),(0xffffffff00000000ffffffff00000000,51,3)]
def face1_h14W : BT Decor := buildWiresBT 2 face1_h14Base face0_steps_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h14Pairs : goodPairs face0_G_6 face1_h14Pos face1_h14Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h14BaseOk : ∀ x ∈ face1_h14Base, faithful face1_h14Pos face1_h14Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h14WOk : btAll (fun x => faithful face1_h14Pos face1_h14Neg x ∧ x.1 < 2^128) face1_h14W := buildWiresBT_faithful face1_h14BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h14AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw face0_G_6 = face0_G_6) face1_h4Autos := btAll_ofList (autos_of (by decide +kernel))
def face1_h14Pools : BT (Option BoundPool) := buildPoolsBT 1 face1_h14W face0_R_6 face1_Cofactor12086_slices_0 face0_ps_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h14SlicesOk : btAll (fun o => ∀ p, o = some p → Slice face0_R_6 face0_G_6 p.1 p.2) face1_Cofactor12086_slices_0 := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice face0_R_6 face0_G_6 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h14PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool face0_R_6 face0_G_6 c) face1_h14Pools := buildPoolsBT_sound face1_h14SlicesOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h14EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible face0_G_6 (3 - 1) xs.toFinset) face1_Cofactor12086_bk_0_init := trivial
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h14Test3_0 : checkNodesBT face1_h14W face0_G_6 face1_h4Mask face1_h14Pools face1_h4Autos face1_Cofactor12086_bk_0_init 3 face1_h4Block3_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h14Check3 : checkNodesBT face1_h14W face0_G_6 face1_h4Mask face1_h14Pools face1_h4Autos face1_Cofactor12086_bk_0_init 3 face1_h4Nodes3 = true := face1_h14Test3_0
def face1_h14Bucket3 : BT (List (List Nat)) := buildBucketsBT face1_h14W face1_h4Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h14Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face0_G_6 3 xs.toFinset) face1_h14Bucket3 := buildBucketsBT_sound (by decide) face1_h14Pairs face1_h14WOk face1_h14PoolsOk face1_h14AutosOk face1_h14EmptyOk face1_h14Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h14Bound : Lower face0_R_6 face0_G_6 4 := lower_of_forestBT (essPairs := [(VAR 0,4,5),(VAR 2,1,5),(VAR 5,1,33)]) (by decide +kernel) face1_h14Bucket3Ok (by decide +kernel)
def face1_h15G : Nat := 0xece8ece8ece8ece8ece8ece8ece8ece8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h15Bound : Lower face1_h11R face1_h15G 5 := lift_of (z := 8) (o := 0) (essPairs := [(VAR 3,2,10)]) (by decide +kernel) face1_h12Bound
def face1_h16G : Nat := 0xecececece0e0e0e0ecececece0e0e0e0
def face1_h16Pos : List Nat := [5,35,6,6,5,35,34,37]
def face1_h16Neg : List Nat := [4,33,4,2,1,3,2,33]
def face1_h16Mask : Nat := fullMask 8
def face1_h16Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,179,178),(0xcccccccccccccccccccccccccccccccc,110,104),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,157,5),(0xffffffff00000000ffffffff00000000,226,130)]
def face1_h16W : BT Decor := buildWiresBT 2 face1_h16Base face0_steps_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h16Pairs : goodPairs face1_h16G face1_h16Pos face1_h16Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h16BaseOk : ∀ x ∈ face1_h16Base, faithful face1_h16Pos face1_h16Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h16WOk : btAll (fun x => faithful face1_h16Pos face1_h16Neg x ∧ x.1 < 2^128) face1_h16W := buildWiresBT_faithful face1_h16BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h16AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw face1_h16G = face1_h16G) face1_h4Autos := btAll_ofList (autos_of (by decide +kernel))
def face1_h16Pools : BT (Option BoundPool) := buildPoolsBT 1 face1_h16W face0_R_19 face1_Cofactor12086_slices_0 face0_ps_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h16SlicesOk : btAll (fun o => ∀ p, o = some p → Slice face0_R_19 face1_h16G p.1 p.2) face1_Cofactor12086_slices_0 := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice face0_R_19 face1_h16G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h16PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool face0_R_19 face1_h16G c) face1_h16Pools := buildPoolsBT_sound face1_h16SlicesOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h16EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible face1_h16G (3 - 1) xs.toFinset) face1_Cofactor12086_bk_0_init := trivial
def face1_h16Block3_0 : List NodeSpec := [([0,1,2,3],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h16Test3_0 : checkNodesBT face1_h16W face1_h16G face1_h16Mask face1_h16Pools face1_h4Autos face1_Cofactor12086_bk_0_init 3 face1_h16Block3_0 = true := by decide +kernel
def face1_h16Nodes3 : List NodeSpec := face1_h16Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h16Check3 : checkNodesBT face1_h16W face1_h16G face1_h16Mask face1_h16Pools face1_h4Autos face1_Cofactor12086_bk_0_init 3 face1_h16Nodes3 = true := face1_h16Test3_0
def face1_h16Bucket3 : BT (List (List Nat)) := buildBucketsBT face1_h16W face1_h16Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h16Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face1_h16G 3 xs.toFinset) face1_h16Bucket3 := buildBucketsBT_sound (by decide) face1_h16Pairs face1_h16WOk face1_h16PoolsOk face1_h16AutosOk face1_h16EmptyOk face1_h16Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h16Bound : Lower face0_R_19 face1_h16G 4 := lower_of_forestBT (essPairs := [(VAR 0,4,5),(VAR 1,4,6),(VAR 2,1,5),(VAR 5,2,34)]) (by decide +kernel) face1_h16Bucket3Ok (by decide +kernel)
def face1_h17R : List Nat := varsOf 43
def face1_h17G : Nat := 0xeeeeeeeeee88ee88eeeeeeeeee88ee88
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h17Bound : Lower face1_h17R face1_h17G 5 := lift_of (z := 8) (o := 0) (essPairs := [(VAR 3,1,9)]) (by decide +kernel) face1_h13Bound
def face1_h18R : List Nat := varsOf 45
def face1_h18G : Nat := 0xfffafffaf0a0f0a0fffafffaf0a0f0a0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h18Bound : Lower face1_h18R face1_h18G 5 := lift_of (z := 1) (o := 0) (essPairs := [(VAR 0,4,5)]) (by decide +kernel) face1_h6Bound
def face1_h9R : List Nat := varsOf 47
def face1_h9G : Nat := 0xece8ece8e080e080ece8ece8e080e080
def face1_h9Pos : List Nat := [13,14,42,14,7,13,13,38,14,37,35,7,42,37,35,42,37,38,7,42,13,38,13,15,43,37,35,43,37,13,45,45,42,46,42,7,14,7,13,35,13,14,35,7,13,35,14]
def face1_h9Neg : List Nat := [12,12,41,10,3,9,5,36,6,5,3,5,34,33,34,10,36,6,6,40,41,34,11,11,11,1,33,41,41,1,44,41,2,44,44,4,11,2,8,1,44,44,2,1,4,41,4]
def face1_h9Mask : Nat := fullMask 47
def face1_h9Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x3de8ffd56e71,0x2890bfd02e74),(0xcccccccccccccccccccccccccccccccc,0x6ebf0daedd9e,0x43101e6d518),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x5b7af2f72bfb,0x530e40070bc3),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x5357e9d8916f,0x2356d9d8802f),(0xffffffff00000000ffffffff00000000,0x2487df2bf684,0x2306dc397084)]
def face1_h9Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(3,0,1),(0,0,2),(1,0,2),(2,0,2),(3,0,2),(0,1,2),(1,1,2),(2,1,2),(3,1,2),(0,1,4),(1,1,4),(2,1,4),(3,1,4),(0,1,12),(2,1,12),(0,2,4),(1,2,4),(2,2,4),(3,2,4),(2,2,5),(1,3,5),(0,2,28),(3,2,28),(0,4,28),(3,4,28),(0,0,4),(1,0,4),(2,0,4),(3,0,4),(2,1,23),(3,23,28),(1,3,23),(0,0,39),(3,0,39),(0,1,39),(3,1,39),(3,5,39),(1,5,23),(0,0,24),(3,0,24),(0,1,24),(0,0,48),(1,0,48),(2,0,48),(3,0,48),(1,4,48),(3,4,48),(3,1,24),(3,3,24),(0,24,28),(1,4,57),(3,5,24),(2,1,26),(1,5,26),(2,4,29),(0,2,6),(1,0,63),(0,4,63),(1,4,63),(2,4,63),(3,4,63),(3,2,6),(2,2,37),(3,3,6),(0,4,6),(3,4,6),(0,6,39),(1,0,74),(2,6,23),(0,6,24),(2,6,26),(1,3,65),(3,3,66),(2,2,7),(1,7,23),(3,7,24),(1,7,26),(1,3,9),(0,1,10),(1,3,11),(1,3,13),(3,3,13),(1,12,19),(1,3,33),(0,1,34),(0,2,92),(2,2,92),(0,2,34),(2,1,95),(3,13,34),(2,2,35),(2,1,36),(0,2,53),(0,0,14),(3,0,14),(3,3,14),(0,4,14),(3,4,14),(1,3,17),(1,3,20),(2,0,42),(1,3,49),(3,3,50)]
def face1_h9W : BT Decor := buildWiresBT 7 face1_h9Base face1_h9Steps
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9Pairs : goodPairs face1_h9G face1_h9Pos face1_h9Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9BaseOk : ∀ x ∈ face1_h9Base, faithful face1_h9Pos face1_h9Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9WOk : btAll (fun x => faithful face1_h9Pos face1_h9Neg x ∧ x.1 < 2^128) face1_h9W := buildWiresBT_faithful face1_h9BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw face1_h9G = face1_h9G) face1_h4Autos := btAll_ofList (autos_of (by decide +kernel))
def face1_h9SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,5),some (subcubeFast 0 2,5),some (subcubeFast 0 4,5),some (subcubeFast 0 8,4),some (subcubeFast 0 32,5),some (subcubeFast 1 0,5),some (subcubeFast 1 2,4),some (subcubeFast 8 0,7),some (subcubeFast 8 1,4),some (subcubeFast 8 2,4),some (subcubeFast 8 4,4),some (subcubeFast 8 32,4),some (subcubeFast 32 0,5),some (subcubeFast 32 4,4)]
def face1_h9Slices : BT (Option (Nat × Nat)) := btOfList 4 face1_h9SliceList
def face1_h9Specs : List PoolSpec := [(5,[]),(1,[]),(0,[]),(2,[]),(1,[(1,3,5)]),(0,[(1,3,5)]),(8,[]),(7,[(0,0,1),(3,0,2)]),(12,[(3,0,2)]),(7,[(0,0,1)]),(6,[]),(3,[]),(7,[(0,2,4)]),(7,[]),(12,[]),(7,[(1,2,4),(0,1,24)]),(4,[]),(12,[(0,1,24)]),(7,[(1,2,4)]),(10,[]),(7,[(2,2,4)]),(13,[]),(7,[(3,2,4)]),(7,[(1,0,1)]),(5,[(0,2,6)]),(7,[(1,0,1),(0,2,6)]),(2,[(1,3,23)]),(4,[(1,3,23)]),(5,[(3,3,6)]),(12,[(3,3,24)]),(5,[(3,2,6)]),(7,[(1,0,1),(3,2,6)]),(5,[(0,4,6)]),(7,[(1,0,1),(0,4,6)]),(5,[(3,4,6)]),(7,[(1,0,1),(3,4,6)]),(7,[(2,0,1)]),(7,[(2,0,1),(2,2,7)]),(9,[]),(7,[(3,0,1)]),(7,[(0,0,2)]),(7,[(1,0,2)]),(5,[(0,1,10)]),(7,[(1,0,2),(0,1,10)]),(7,[(2,0,2)]),(0,[(1,3,11)]),(7,[(3,0,2)]),(5,[(0,1,2)]),(5,[(2,1,12)]),(7,[(0,0,4)]),(0,[(1,3,33)]),(7,[(1,0,4)]),(5,[(0,1,34)]),(7,[(1,0,4),(0,1,34)]),(12,[(0,2,34)]),(7,[(1,0,4),(0,2,34)]),(7,[(2,0,4)]),(12,[(2,2,35)]),(11,[]),(7,[(3,0,4)]),(5,[(2,1,36)]),(7,[(0,1,2)]),(12,[(0,1,2)]),(7,[(1,1,2)]),(7,[(1,1,2),(0,0,14)]),(7,[(1,1,2),(3,0,14)]),(7,[(1,1,2),(0,4,14)]),(7,[(1,1,2),(3,4,14)]),(7,[(2,1,2)]),(7,[(3,1,2)]),(7,[(0,1,4)]),(7,[(1,1,4)]),(7,[(2,1,4)]),(5,[(2,1,4)]),(7,[(2,1,4),(0,2,4)]),(12,[(2,2,37)]),(7,[(3,1,4)]),(7,[(1,2,4),(0,0,24)]),(12,[(0,0,24)]),(7,[(1,2,4),(3,0,24)]),(12,[(3,0,24)]),(7,[(1,2,4),(3,1,24)]),(12,[(3,1,24)]),(7,[(3,2,4),(2,1,26)])]
def face1_h9Pools : BT (Option BoundPool) := buildPoolsBT 7 face1_h9W face1_h9R face1_h9Slices face1_h9Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9Slice13 : Slice face1_h9R face1_h9G (subcubeFast 32 4) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) face1_h10Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9Slice12 : Slice face1_h9R face1_h9G (subcubeFast 32 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) face1_h11Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9Slice11 : Slice face1_h9R face1_h9G (subcubeFast 8 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) face1_h12Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9Slice10 : Slice face1_h9R face1_h9G (subcubeFast 8 4) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) face1_h13Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9Slice9 : Slice face1_h9R face1_h9G (subcubeFast 8 2) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) face1_h14Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9Slice8 : Slice face1_h9R face1_h9G (subcubeFast 8 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) face1_h4Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9Slice7 : Slice face1_h9R face1_h9G (subcubeFast 8 0) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) face1_h5Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9Slice6 : Slice face1_h9R face1_h9G (subcubeFast 1 2) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) face1_h6Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9Slice5 : Slice face1_h9R face1_h9G (subcubeFast 1 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) face1_h7Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9Slice4 : Slice face1_h9R face1_h9G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) face1_h15Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9Slice3 : Slice face1_h9R face1_h9G (subcubeFast 0 8) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) face1_h16Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9Slice2 : Slice face1_h9R face1_h9G (subcubeFast 0 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) face1_h17Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9Slice1 : Slice face1_h9R face1_h9G (subcubeFast 0 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) face1_h18Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9Slice0 : Slice face1_h9R face1_h9G (subcubeFast 0 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) face1_h8Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9SlicesOk : btAll (fun o => ∀ p, o = some p → Slice face1_h9R face1_h9G p.1 p.2) face1_h9Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice face1_h9R face1_h9G p.1 p.2) (forall_cons (fun _ h => by cases h; exact face1_h9Slice0) (forall_cons (fun _ h => by cases h; exact face1_h9Slice1) (forall_cons (fun _ h => by cases h; exact face1_h9Slice2) (forall_cons (fun _ h => by cases h; exact face1_h9Slice3) (forall_cons (fun _ h => by cases h; exact face1_h9Slice4) (forall_cons (fun _ h => by cases h; exact face1_h9Slice5) (forall_cons (fun _ h => by cases h; exact face1_h9Slice6) (forall_cons (fun _ h => by cases h; exact face1_h9Slice7) (forall_cons (fun _ h => by cases h; exact face1_h9Slice8) (forall_cons (fun _ h => by cases h; exact face1_h9Slice9) (forall_cons (fun _ h => by cases h; exact face1_h9Slice10) (forall_cons (fun _ h => by cases h; exact face1_h9Slice11) (forall_cons (fun _ h => by cases h; exact face1_h9Slice12) (forall_cons (fun _ h => by cases h; exact face1_h9Slice13) (fun _ h => (List.not_mem_nil h).elim)))))))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool face1_h9R face1_h9G c) face1_h9Pools := buildPoolsBT_sound face1_h9SlicesOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible face1_h9G (4 - 1) xs.toFinset) face1_Cofactor12086_bk_0_init := trivial
def face1_h9Block4_0 : List NodeSpec := [([0,1,2,4,38],[],[0]),([0,1,2,4,44],[],[0]),([0,3,4,27,48],[],[0]),([0,2,4,28,48],[],[0]),([0,1,2,4,57],[],[0]),([0,1,2,28,58],[],[0]),([0,1,2,28,62],[],[0]),([0,3,4,37,63],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9Test4_0 : checkNodesBT face1_h9W face1_h9G face1_h9Mask face1_h9Pools face1_h4Autos face1_Cofactor12086_bk_0_init 4 face1_h9Block4_0 = true := by decide +kernel
def face1_h9Block4_1 : List NodeSpec := [([0,1,4,39,63],[],[0]),([0,1,2,4,74],[],[0]),([0,3,4,48,63],[],[0]),([0,2,4,48,71],[],[0]),([0,1,4,56,63],[],[0]),([0,1,4,63,79],[],[0]),([0,1,4,63,80],[],[0]),([1,2,4,39,75],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9Test4_1 : checkNodesBT face1_h9W face1_h9G face1_h9Mask face1_h9Pools face1_h4Autos face1_Cofactor12086_bk_0_init 4 face1_h9Block4_1 = true := by decide +kernel
def face1_h9Block4_2 : List NodeSpec := [([1,2,4,39,108],[],[0]),([0,2,4,48,109],[],[0]),([0,2,4,48,110],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9Test4_2 : checkNodesBT face1_h9W face1_h9G face1_h9Mask face1_h9Pools face1_h4Autos face1_Cofactor12086_bk_0_init 4 face1_h9Block4_2 = true := by decide +kernel
def face1_h9Nodes4 : List NodeSpec := face1_h9Block4_0 ++ face1_h9Block4_1 ++ face1_h9Block4_2
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9Check4 : checkNodesBT face1_h9W face1_h9G face1_h9Mask face1_h9Pools face1_h4Autos face1_Cofactor12086_bk_0_init 4 face1_h9Nodes4 = true := by
  unfold face1_h9Nodes4 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨face1_h9Test4_0,face1_h9Test4_1⟩,face1_h9Test4_2⟩
def face1_h9Bucket4 : BT (List (List Nat)) := buildBucketsBT face1_h9W face1_h9Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face1_h9G 4 xs.toFinset) face1_h9Bucket4 := buildBucketsBT_sound (by decide) face1_h9Pairs face1_h9WOk face1_h9PoolsOk face1_h9AutosOk face1_h9EmptyOk face1_h9Check4
def face1_h9Block5_0 : List NodeSpec := [([1,2,4,12,28],[0,4,5],[0]),([0,1,2,4,23,28],[11],[0]),([0,1,2,4,5,39],[11],[0]),([0,1,2,3,4,45],[11,13],[0]),([0,2,3,4,5,48],[2,15,16,17],[0]),([0,1,3,4,24,27],[0],[0]),([0,1,2,4,24,28],[0,4,5,11],[0]),([0,1,2,4,5,56],[11,19],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9Test5_0 : checkNodesBT face1_h9W face1_h9G face1_h9Mask face1_h9Pools face1_h4Autos face1_h9Bucket4 5 face1_h9Block5_0 = true := by decide +kernel
def face1_h9Block5_1 : List NodeSpec := [([0,1,2,3,4,59],[1,2,11,13],[0]),([0,1,3,4,25,27],[0],[0]),([0,1,2,4,25,28],[],[0]),([0,1,2,4,26,28],[0,5],[0]),([0,1,2,3,4,61],[],[0]),([0,1,2,4,28,29],[],[0]),([0,1,2,4,28,30],[0,9],[0]),([0,1,2,4,28,31],[11],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9Test5_1 : checkNodesBT face1_h9W face1_h9G face1_h9Mask face1_h9Pools face1_h4Autos face1_h9Bucket4 5 face1_h9Block5_1 = true := by decide +kernel
def face1_h9Block5_2 : List NodeSpec := [([0,1,2,4,28,32],[],[0]),([0,1,2,3,4,29],[0,14,16],[0]),([0,2,3,4,6,37],[14],[0]),([0,1,3,4,23,63],[2,24,25],[0]),([0,1,2,4,23,71],[6,11],[0]),([0,1,2,4,6,39],[11,14,26,27],[0]),([0,1,2,3,4,76],[2,11,13],[0]),([0,2,3,4,6,48],[3,15,16,17],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9Test5_2 : checkNodesBT face1_h9W face1_h9G face1_h9Mask face1_h9Pools face1_h4Autos face1_h9Bucket4 5 face1_h9Block5_2 = true := by decide +kernel
def face1_h9Block5_3 : List NodeSpec := [([0,1,3,4,24,63],[1,2,24,25],[0]),([0,1,2,4,24,71],[1,2,6,11,28],[0]),([0,1,2,4,6,56],[3,11,16,19,29],[0]),([0,1,2,3,4,77],[0,2,3,11,13],[0]),([0,1,3,4,25,63],[2],[0]),([0,1,2,4,25,71],[],[0]),([0,1,3,4,26,63],[],[0]),([0,1,2,4,26,71],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9Test5_3 : checkNodesBT face1_h9W face1_h9G face1_h9Mask face1_h9Pools face1_h4Autos face1_h9Bucket4 5 face1_h9Block5_3 = true := by decide +kernel
def face1_h9Block5_4 : List NodeSpec := [([0,1,2,3,4,78],[2],[0]),([0,1,3,4,63,65],[2,24,25],[0]),([0,1,3,4,63,66],[1,2,24,25],[0]),([0,1,3,4,63,67],[],[0]),([0,1,3,4,63,68],[],[0]),([0,1,2,4,7,39],[14,27],[0]),([0,1,2,3,4,82],[],[0]),([0,2,3,4,7,48],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9Test5_4 : checkNodesBT face1_h9W face1_h9G face1_h9Mask face1_h9Pools face1_h4Autos face1_h9Bucket4 5 face1_h9Block5_4 = true := by decide +kernel
def face1_h9Block5_5 : List NodeSpec := [([0,1,2,4,7,56],[],[0]),([0,1,2,3,4,83],[2,3],[0]),([0,1,2,3,4,84],[],[0]),([0,2,3,4,8,37],[0],[0]),([0,1,2,4,8,39],[],[0]),([0,2,3,4,8,48],[0],[0]),([0,1,2,4,8,56],[],[0]),([0,2,3,4,13,22],[2,13],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9Test5_5 : checkNodesBT face1_h9W face1_h9G face1_h9Mask face1_h9Pools face1_h4Autos face1_h9Bucket4 5 face1_h9Block5_5 = true := by decide +kernel
def face1_h9Block5_6 : List NodeSpec := [([0,1,2,3,4,90],[],[0]),([0,2,3,4,13,92],[2],[0]),([0,1,3,4,13,95],[2,16],[0]),([0,1,2,3,4,93],[0,2,11,13],[0]),([0,1,2,3,4,97],[],[0]),([0,1,2,3,4,94],[],[0]),([0,1,2,3,4,96],[],[0]),([0,1,3,4,13,70],[13,16],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9Test5_6 : checkNodesBT face1_h9W face1_h9G face1_h9Mask face1_h9Pools face1_h4Autos face1_h9Bucket4 5 face1_h9Block5_6 = true := by decide +kernel
def face1_h9Block5_7 : List NodeSpec := [([0,1,2,19,39],[14,26],[0]),([0,1,2,4,39,40],[11],[0]),([0,1,2,4,39,41],[],[0]),([0,1,2,4,39,42],[],[0]),([0,1,2,4,39,43],[12,14],[0]),([0,1,2,3,4,42],[0,2,14],[0]),([0,2,3,4,48,49],[3,15,16,17],[0]),([0,2,3,4,48,50],[3,15,16,17],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9Test5_7 : checkNodesBT face1_h9W face1_h9G face1_h9Mask face1_h9Pools face1_h4Autos face1_h9Bucket4 5 face1_h9Block5_7 = true := by decide +kernel
def face1_h9Block5_8 : List NodeSpec := [([0,2,3,4,48,51],[],[0]),([0,2,3,4,48,52],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9Test5_8 : checkNodesBT face1_h9W face1_h9G face1_h9Mask face1_h9Pools face1_h4Autos face1_h9Bucket4 5 face1_h9Block5_8 = true := by decide +kernel
def face1_h9Nodes5 : List NodeSpec := face1_h9Block5_0 ++ face1_h9Block5_1 ++ face1_h9Block5_2 ++ face1_h9Block5_3 ++ face1_h9Block5_4 ++ face1_h9Block5_5 ++ face1_h9Block5_6 ++ face1_h9Block5_7 ++ face1_h9Block5_8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9Check5 : checkNodesBT face1_h9W face1_h9G face1_h9Mask face1_h9Pools face1_h4Autos face1_h9Bucket4 5 face1_h9Nodes5 = true := by
  unfold face1_h9Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨face1_h9Test5_0,face1_h9Test5_1⟩,face1_h9Test5_2⟩,face1_h9Test5_3⟩,face1_h9Test5_4⟩,face1_h9Test5_5⟩,face1_h9Test5_6⟩,face1_h9Test5_7⟩,face1_h9Test5_8⟩
def face1_h9Bucket5 : BT (List (List Nat)) := buildBucketsBT face1_h9W face1_h9Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face1_h9G 5 xs.toFinset) face1_h9Bucket5 := buildBucketsBT_sound (by decide) face1_h9Pairs face1_h9WOk face1_h9PoolsOk face1_h9AutosOk face1_h9Bucket4Ok face1_h9Check5
def face1_h9Block6_0 : List NodeSpec := [([1,2,3,4,5,12],[0,1,2,3,6,7,8],[0]),([0,1,2,3,4,5,23],[0,9,12,14],[0]),([0,1,2,3,4,5,24],[0,1,2,3,9,14,16,18],[0]),([0,1,2,3,4,5,25],[0,3,16,20,21],[0]),([0,1,2,3,4,5,26],[0,2,3,14,16,22],[0]),([0,1,2,3,4,27],[0,1,2,10,11,13,14,16],[0]),([0,1,2,4,28],[0,4,5,9,10,11],[0]),([0,1,2,3,4,28],[0,2,3,9,11,13,14,16],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9Test6_0 : checkNodesBT face1_h9W face1_h9G face1_h9Mask face1_h9Pools face1_h4Autos face1_h9Bucket5 6 face1_h9Block6_0 = true := by decide +kernel
def face1_h9Block6_1 : List NodeSpec := [([0,1,2,3,4,6,23],[0,1,2,3,12,14,16,23],[0]),([0,1,2,3,4,6,24],[0,1,2,3,14,16,18,23],[0]),([0,1,2,3,4,6,25],[2,3,14,16,20,21],[0]),([0,1,2,3,4,6,26],[2,3,14,16,22],[0]),([0,1,3,4,63],[1,2,24,25],[0]),([0,1,2,3,4,63],[0,1,2,11,13,14,16,24,25],[0]),([0,1,3,4,69],[1,2,3,30,31],[0]),([0,1,2,4,71],[1,2,6,11,23,28],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9Test6_1 : checkNodesBT face1_h9W face1_h9G face1_h9Mask face1_h9Pools face1_h4Autos face1_h9Bucket5 6 face1_h9Block6_1 = true := by decide +kernel
def face1_h9Block6_2 : List NodeSpec := [([0,1,2,3,72],[1,2,14,32,33],[0]),([0,1,2,3,73],[1,2,16,34,35],[0]),([0,1,2,3,4,7,23],[0,2,14,16,36],[0]),([0,1,2,3,4,7,24],[0,1,2,3,36],[0]),([0,1,2,3,4,7,25],[0,14,16,21],[0]),([0,1,2,3,4,7,26],[0,3],[0]),([0,1,2,3,4,81],[0,1,2,11,13,14,16,37],[0]),([0,1,2,3,4,8,23],[1,2,10,14,39],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9Test6_2 : checkNodesBT face1_h9W face1_h9G face1_h9Mask face1_h9Pools face1_h4Autos face1_h9Bucket5 6 face1_h9Block6_2 = true := by decide +kernel
def face1_h9Block6_3 : List NodeSpec := [([0,1,2,3,4,8,24],[0,1,2,3,10,39],[0]),([0,1,2,3,4,8,25],[2,10,16],[0]),([0,1,2,3,4,8,26],[0,2,3,10],[0]),([0,1,2,3,4,85],[0,1,2,10,11,13,14,16,40],[0]),([0,1,2,3,4,86],[0,1,2,3,10,11,13,14,16,21,42,43],[0]),([0,1,2,4,87],[0,3,10,11,19,44,45],[0]),([0,1,2,3,4,12,13],[0,1,2,47],[0]),([0,1,2,3,4,12,19],[0,2,10,14,16],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9Test6_3 : checkNodesBT face1_h9W face1_h9G face1_h9Mask face1_h9Pools face1_h4Autos face1_h9Bucket5 6 face1_h9Block6_3 = true := by decide +kernel
def face1_h9Block6_4 : List NodeSpec := [([0,1,2,3,4,22],[0,1,2,10,11,13,14,16,48],[0]),([0,1,2,4,91],[0,10,11,14,21,49,50],[0]),([0,1,2,3,4,91],[0,1,2,3,10,11,13,21,49],[0]),([0,1,2,3,4,13,34],[0,1,2,3,14,16],[0]),([0,1,2,3,4,92],[0,1,2,3,10,11,13,16,52,53],[0]),([0,1,2,3,4,95],[0,1,2,3,11,13,16,21,54,55],[0]),([0,1,2,3,4,98],[0,1,2,3,10,11,13,16,57],[0]),([0,1,2,3,4,99],[0,1,2,3,10,11,13,14,21,60],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9Test6_4 : checkNodesBT face1_h9W face1_h9G face1_h9Mask face1_h9Pools face1_h4Autos face1_h9Bucket5 6 face1_h9Block6_4 = true := by decide +kernel
def face1_h9Block6_5 : List NodeSpec := [([0,1,2,3,4,13,64],[0,1,2,10,47],[0]),([0,1,2,3,4,13,21],[0,2,10],[0]),([0,1,2,3,4,13,19],[3,14,16,62],[0]),([0,1,2,3,4,88],[0,1,2,3,11,13,14,16,61],[0]),([0,1,2,3,4,89],[0,2,11,14,16,38,61],[0]),([0,1,2,3,4,13,53],[1,3,14,16,21],[0]),([0,1,2,3,4,13,54],[14,16,21],[0]),([1,2,3,4,101],[0,1,3,64],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9Test6_5 : checkNodesBT face1_h9W face1_h9G face1_h9Mask face1_h9Pools face1_h4Autos face1_h9Bucket5 6 face1_h9Block6_5 = true := by decide +kernel
def face1_h9Block6_6 : List NodeSpec := [([1,2,3,4,102],[1,2,3,65],[0]),([0,1,2,4,103],[1,3,10,11,38,63],[0]),([0,1,2,3,104],[1,3,14,66],[0]),([0,1,2,3,105],[1,3,16,67],[0]),([0,1,2,3,4,13],[0,1,2,11,13,14,16,61],[0]),([0,1,2,3,4,106],[0,1,2,3,11,13,14,16,21,70],[0]),([0,1,2,3,4,100],[0,1,2,3,10,11,13,16,17,38],[0]),([0,1,2,3,19,23],[1,3,14,16,58,73,74],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9Test6_6 : checkNodesBT face1_h9W face1_h9G face1_h9Mask face1_h9Pools face1_h4Autos face1_h9Bucket5 6 face1_h9Block6_6 = true := by decide +kernel
def face1_h9Block6_7 : List NodeSpec := [([0,1,2,3,4,70],[0,1,2,3,11,13,14,16,21,75],[0]),([0,1,2,4,107],[1,10,11,14,38,76],[0]),([0,1,2,3,4,37],[0,1,2,3,11,13,14,16,21],[0]),([0,1,2,4,39],[11,12,14,21,26,27],[0]),([0,1,2,3,4,39],[0,1,2,3,11,12,13,14,16],[0]),([1,2,3,4,46],[0,3,16,77,78],[0]),([1,2,3,4,47],[2,3,16,79,80],[0]),([0,2,3,4,48],[3,15,16,17],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9Test6_7 : checkNodesBT face1_h9W face1_h9G face1_h9Mask face1_h9Pools face1_h4Autos face1_h9Bucket5 6 face1_h9Block6_7 = true := by decide +kernel
def face1_h9Block6_8 : List NodeSpec := [([0,1,2,3,4,48],[0,1,2,3,11,13,15,16,17],[0]),([0,2,3,4,55],[1,3,16,81,82],[0]),([0,1,2,4,56],[3,11,16,18,19,29],[0]),([0,1,2,3,4,60],[0,1,2,3,11,13,14,83],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9Test6_8 : checkNodesBT face1_h9W face1_h9G face1_h9Mask face1_h9Pools face1_h4Autos face1_h9Bucket5 6 face1_h9Block6_8 = true := by decide +kernel
def face1_h9Nodes6 : List NodeSpec := face1_h9Block6_0 ++ face1_h9Block6_1 ++ face1_h9Block6_2 ++ face1_h9Block6_3 ++ face1_h9Block6_4 ++ face1_h9Block6_5 ++ face1_h9Block6_6 ++ face1_h9Block6_7 ++ face1_h9Block6_8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9Check6 : checkNodesBT face1_h9W face1_h9G face1_h9Mask face1_h9Pools face1_h4Autos face1_h9Bucket5 6 face1_h9Nodes6 = true := by
  unfold face1_h9Nodes6 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨face1_h9Test6_0,face1_h9Test6_1⟩,face1_h9Test6_2⟩,face1_h9Test6_3⟩,face1_h9Test6_4⟩,face1_h9Test6_5⟩,face1_h9Test6_6⟩,face1_h9Test6_7⟩,face1_h9Test6_8⟩
def face1_h9Bucket6 : BT (List (List Nat)) := buildBucketsBT face1_h9W face1_h9Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face1_h9G 6 xs.toFinset) face1_h9Bucket6 := buildBucketsBT_sound (by decide) face1_h9Pairs face1_h9WOk face1_h9PoolsOk face1_h9AutosOk face1_h9Bucket5Ok face1_h9Check6
def face1_h9Block7_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,9,10,13,14,16],[0]),([0,1,2,3,4,6],[0,1,2,3,6,13,14,16,23],[0]),([0,1,2,3,4,7],[0,1,2,3,13,14,16,36,38],[0]),([0,1,2,3,4,8],[0,1,2,3,10,13,14,16,39],[0]),([0,1,2,3,4,9],[0,1,2,3,10,13,14,16,21,40],[0]),([0,1,2,3,4,10],[0,1,2,3,6,10,13,14,16,21,41],[0]),([0,1,2,3,4,11],[0,1,2,3,10,13,14,16,19,44],[0]),([0,1,2,3,4,12],[0,1,2,3,6,10,13,14,16,21,46],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9Test7_0 : checkNodesBT face1_h9W face1_h9G face1_h9Mask face1_h9Pools face1_h4Autos face1_h9Bucket6 7 face1_h9Block7_0 = true := by decide +kernel
def face1_h9Block7_1 : List NodeSpec := [([0,1,2,3,4,33],[0,1,2,3,10,13,14,21,49],[0]),([0,1,2,3,4,34],[0,1,2,3,6,10,13,14,16,21,51],[0]),([0,1,2,3,4,35],[0,1,2,3,10,13,14,16,56,58],[0]),([0,1,2,3,4,36],[0,1,2,3,6,10,13,14,21,59],[0]),([0,1,2,3,4,13],[0,1,2,3,10,13,14,16,21,61],[0]),([0,1,2,3,4,14],[0,1,2,3,10,13,14,16,38,63],[0]),([0,1,2,3,4,15],[0,1,2,3,10,13,14,16,19,21,68],[0]),([0,1,2,3,4,16],[0,1,2,3,10,13,14,16,21,38,69],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9Test7_1 : checkNodesBT face1_h9W face1_h9G face1_h9Mask face1_h9Pools face1_h4Autos face1_h9Bucket6 7 face1_h9Block7_1 = true := by decide +kernel
def face1_h9Block7_2 : List NodeSpec := [([0,1,2,3,4,17],[0,1,2,3,10,13,14,16,21,70],[0]),([0,1,2,3,4,18],[0,1,2,3,10,13,14,16,38,71],[0]),([0,1,2,3,4,19],[0,1,2,3,10,13,14,16,21,58,72],[0]),([0,1,2,3,4,20],[0,1,2,3,10,13,14,21,38,76],[0]),([0,1,2,3,4,23],[0,1,2,3,12,13,14,16,21],[0]),([0,1,2,3,4,24],[0,1,2,3,13,14,16,18,19],[0]),([0,1,2,3,4,25],[0,1,2,3,13,14,16,20,21],[0]),([0,1,2,3,4,26],[0,1,2,3,13,14,19,22],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9Test7_2 : checkNodesBT face1_h9W face1_h9G face1_h9Mask face1_h9Pools face1_h4Autos face1_h9Bucket6 7 face1_h9Block7_2 = true := by decide +kernel
def face1_h9Nodes7 : List NodeSpec := face1_h9Block7_0 ++ face1_h9Block7_1 ++ face1_h9Block7_2
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9Check7 : checkNodesBT face1_h9W face1_h9G face1_h9Mask face1_h9Pools face1_h4Autos face1_h9Bucket6 7 face1_h9Nodes7 = true := by
  unfold face1_h9Nodes7 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨face1_h9Test7_0,face1_h9Test7_1⟩,face1_h9Test7_2⟩
def face1_h9Bucket7 : BT (List (List Nat)) := buildBucketsBT face1_h9W face1_h9Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face1_h9G 7 xs.toFinset) face1_h9Bucket7 := buildBucketsBT_sound (by decide) face1_h9Pairs face1_h9WOk face1_h9PoolsOk face1_h9AutosOk face1_h9Bucket6Ok face1_h9Check7
def face1_h9Block8_0 : List NodeSpec := [([0,1,2,3,4],[13],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9Test8_0 : checkNodesBT face1_h9W face1_h9G face1_h9Mask face1_h9Pools face1_h4Autos face1_h9Bucket7 8 face1_h9Block8_0 = true := by decide +kernel
def face1_h9Nodes8 : List NodeSpec := face1_h9Block8_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9Check8 : checkNodesBT face1_h9W face1_h9G face1_h9Mask face1_h9Pools face1_h4Autos face1_h9Bucket7 8 face1_h9Nodes8 = true := face1_h9Test8_0
def face1_h9Bucket8 : BT (List (List Nat)) := buildBucketsBT face1_h9W face1_h9Nodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face1_h9G 8 xs.toFinset) face1_h9Bucket8 := buildBucketsBT_sound (by decide) face1_h9Pairs face1_h9WOk face1_h9PoolsOk face1_h9AutosOk face1_h9Bucket7Ok face1_h9Check8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma face1_h9Bound : Lower face1_h9R face1_h9G 9 := lower_of_forestBT (essPairs := [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,5,13),(VAR 5,3,35)]) (by decide +kernel) face1_h9Bucket8Ok (by decide +kernel)
def face2_pos_0 : List Nat := [12,12,36,36,40,40,12,36,40]
def face2_neg_0 : List Nat := [8,4,32,4,32,8,32,8,4]
def face2_base_0 : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xcf,0x10a),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x173,0xa1),(0xffffffff00000000ffffffff00000000,0x1bc,0x54)]
def face2_W_0 : BT Decor := buildWiresBT 2 face2_base_0 face0_steps_0
def face2_P_0 : BT (Option BoundPool) := buildPoolsBT 1 face2_W_0 face0_R_15 face1_Cofactor12086_slices_0 face0_ps_0
lemma face2_gp_0 : goodPairs face0_G_15 face2_pos_0 face2_neg_0 := goodPairs_of (by decide +kernel)
lemma face2_base_0_ok : ∀ x ∈ face2_base_0, faithful face2_pos_0 face2_neg_0 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma face2_W_0_ok : btAll (fun x => faithful face2_pos_0 face2_neg_0 x ∧ x.1 < 2^128) face2_W_0 := buildWiresBT_faithful face2_base_0_ok
set_option maxRecDepth 500000 in
lemma face2_autos_0_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw face0_G_15 = face0_G_15) face1_Cofactor12086_autos_0 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma face2_slices_0_ok : btAll (fun o => ∀ p, o = some p → Slice face0_R_15 face0_G_15 p.1 p.2) face1_Cofactor12086_slices_0 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice face0_R_15 face0_G_15 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 500000 in
lemma face2_P_0_ok : btAll (fun o => ∀ c, o = some c → ValidPool face0_R_15 face0_G_15 c) face2_P_0 := buildPoolsBT_sound face2_slices_0_ok
lemma face2_bk_0_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face0_G_15 (0 - 1) xs.toFinset) face1_Cofactor12086_bk_0_init := trivial
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face2_chk_0_0 : checkNodesBT face2_W_0 face0_G_15 face0_fmask_0 face2_P_0 face1_Cofactor12086_autos_0 face1_Cofactor12086_bk_0_init 0 face0_nodes_0_0 = true := by decide +kernel
def face2_bk_0_0 : BT (List (List Nat)) := buildBucketsBT face2_W_0 face0_nodes_0_0
set_option maxRecDepth 500000 in
lemma face2_bk_0_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face0_G_15 0 xs.toFinset) face2_bk_0_0 :=
  buildBucketsBT_sound (by decide) face2_gp_0 face2_W_0_ok face2_P_0_ok face2_autos_0_ok face2_bk_0_init_ok face2_chk_0_0
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face2_chk_0_1 : checkNodesBT face2_W_0 face0_G_15 face0_fmask_0 face2_P_0 face1_Cofactor12086_autos_0 face2_bk_0_0 1 face0_nodes_0_0 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma face2_bk_0_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face0_G_15 1 xs.toFinset) face2_bk_0_0 :=
  buildBucketsBT_sound (by decide) face2_gp_0 face2_W_0_ok face2_P_0_ok face2_autos_0_ok face2_bk_0_0_ok face2_chk_0_1
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face2_chk_0_2 : checkNodesBT face2_W_0 face0_G_15 face0_fmask_0 face2_P_0 face1_Cofactor12086_autos_0 face2_bk_0_0 2 face0_nodes_0_0 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma face2_bk_0_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face0_G_15 2 xs.toFinset) face2_bk_0_0 :=
  buildBucketsBT_sound (by decide) face2_gp_0 face2_W_0_ok face2_P_0_ok face2_autos_0_ok face2_bk_0_1_ok face2_chk_0_2
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face2_chk_0_3 : checkNodesBT face2_W_0 face0_G_15 face0_fmask_0 face2_P_0 face1_Cofactor12086_autos_0 face2_bk_0_0 3 face0_nodes_0_3 = true := by decide +kernel
def face2_bk_0_3 : BT (List (List Nat)) := buildBucketsBT face2_W_0 face0_nodes_0_3
set_option maxRecDepth 500000 in
lemma face2_bk_0_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face0_G_15 3 xs.toFinset) face2_bk_0_3 :=
  buildBucketsBT_sound (by decide) face2_gp_0 face2_W_0_ok face2_P_0_ok face2_autos_0_ok face2_bk_0_2_ok face2_chk_0_3
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma face2_forestRoot_0_ok : forestRootCheck face0_R_15 face0_G_15 [(VAR 2,12,8),(VAR 3,12,4),(VAR 5,36,4)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma face2_forestRoot_0_in : bucketContainsBT face2_bk_0_3 face0_R_15 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma face2_low_0 : Lower face0_R_15 face0_G_15 4 := lower_of_forestBT face2_forestRoot_0_ok face2_bk_0_3_ok face2_forestRoot_0_in
lemma face2_low_8_ok : carryOK [(1,4),(1,5),(1,3),(1,2)] face1_Cofactor12086_R_8 face1_Cofactor12086_G_8 face0_R_15 face0_G_15 = true := by decide +kernel
lemma face2_low_8 : Lower face1_Cofactor12086_R_8 face1_Cofactor12086_G_8 4 := carry_of face2_low_8_ok face2_low_0
lemma face2_low_10_ok : carryOK [(1,3),(1,2)] face0_R_9 face0_G_9 face0_R_15 face0_G_15 = true := by decide +kernel
lemma face2_low_10 : Lower face0_R_9 face0_G_9 4 := carry_of face2_low_10_ok face2_low_0
lemma face2_low_14_ok : carryOK [(1,2)] face1_Cofactor12086_R_11 face1_Cofactor12086_G_11 face0_R_15 face0_G_15 = true := by decide +kernel
lemma face2_low_14 : Lower face1_Cofactor12086_R_11 face1_Cofactor12086_G_11 4 := carry_of face2_low_14_ok face2_low_0
lemma face2_sl_20_0 : Slice face1_Cofactor12086_R_14 face1_Cofactor12086_G_14 (subcubeFast 0 8) 4 := slice_fast_direct face1_Cofactor12086_sl_14_0_ok face2_low_10
lemma face2_sl_20_1 : Slice face1_Cofactor12086_R_14 face1_Cofactor12086_G_14 (subcubeFast 0 2) 4 := slice_fast_direct face1_Cofactor12086_sl_14_1_ok face2_low_0
lemma face2_sl_20_2 : Slice face1_Cofactor12086_R_14 face1_Cofactor12086_G_14 (subcubeFast 0 4) 4 := slice_fast_direct face1_Cofactor12086_sl_14_2_ok face2_low_14
lemma face2_sl_20_3 : Slice face1_Cofactor12086_R_14 face1_Cofactor12086_G_14 (subcubeFast 0 32) 4 := slice_fast_direct face1_Cofactor12086_sl_14_3_ok face2_low_8
set_option maxRecDepth 500000 in
lemma face2_slices_20_ok : btAll (fun o => ∀ p, o = some p → Slice face1_Cofactor12086_R_14 face1_Cofactor12086_G_14 p.1 p.2) face1_Cofactor12086_slices_14 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice face1_Cofactor12086_R_14 face1_Cofactor12086_G_14 p.1 p.2) (forall_cons (fun _ h => by cases h; exact face2_sl_20_0) (forall_cons (fun _ h => by cases h; exact face2_sl_20_1) (forall_cons (fun _ h => by cases h; exact face2_sl_20_2) (forall_cons (fun _ h => by cases h; exact face2_sl_20_3) (fun _ h => (List.not_mem_nil h).elim)))))
set_option maxRecDepth 500000 in
lemma face2_P_20_ok : btAll (fun o => ∀ c, o = some c → ValidPool face1_Cofactor12086_R_14 face1_Cofactor12086_G_14 c) face1_Cofactor12086_P_14 := buildPoolsBT_sound face2_slices_20_ok
set_option maxRecDepth 500000 in
lemma face2_bk_20_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face1_Cofactor12086_G_14 0 xs.toFinset) face1_Cofactor12086_bk_14_0 :=
  buildBucketsBT_sound (by decide) face1_Cofactor12086_gp_14 face1_Cofactor12086_W_14_ok face2_P_20_ok face1_Cofactor12086_autos_14_ok face1_Cofactor12086_bk_14_init_ok face1_Cofactor12086_chk_14_0
set_option maxRecDepth 500000 in
lemma face2_bk_20_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face1_Cofactor12086_G_14 1 xs.toFinset) face1_Cofactor12086_bk_14_0 :=
  buildBucketsBT_sound (by decide) face1_Cofactor12086_gp_14 face1_Cofactor12086_W_14_ok face2_P_20_ok face1_Cofactor12086_autos_14_ok face2_bk_20_0_ok face1_Cofactor12086_chk_14_1
set_option maxRecDepth 500000 in
lemma face2_bk_20_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face1_Cofactor12086_G_14 2 xs.toFinset) face1_Cofactor12086_bk_14_0 :=
  buildBucketsBT_sound (by decide) face1_Cofactor12086_gp_14 face1_Cofactor12086_W_14_ok face2_P_20_ok face1_Cofactor12086_autos_14_ok face2_bk_20_1_ok face1_Cofactor12086_chk_14_2
set_option maxRecDepth 500000 in
lemma face2_bk_20_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face1_Cofactor12086_G_14 3 xs.toFinset) face1_Cofactor12086_bk_14_3 :=
  buildBucketsBT_sound (by decide) face1_Cofactor12086_gp_14 face1_Cofactor12086_W_14_ok face2_P_20_ok face1_Cofactor12086_autos_14_ok face2_bk_20_2_ok face1_Cofactor12086_chk_14_3
set_option maxRecDepth 500000 in
lemma face2_bk_20_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face1_Cofactor12086_G_14 4 xs.toFinset) face1_Cofactor12086_bk_14_4 :=
  buildBucketsBT_sound (by decide) face1_Cofactor12086_gp_14 face1_Cofactor12086_W_14_ok face2_P_20_ok face1_Cofactor12086_autos_14_ok face2_bk_20_3_ok face1_Cofactor12086_chk_14_4
set_option maxRecDepth 500000 in
lemma face2_bk_20_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face1_Cofactor12086_G_14 5 xs.toFinset) face1_Cofactor12086_bk_14_5 :=
  buildBucketsBT_sound (by decide) face1_Cofactor12086_gp_14 face1_Cofactor12086_W_14_ok face2_P_20_ok face1_Cofactor12086_autos_14_ok face2_bk_20_4_ok face1_Cofactor12086_chk_14_5
set_option maxRecDepth 500000 in
lemma face2_bk_20_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face1_Cofactor12086_G_14 6 xs.toFinset) face1_Cofactor12086_bk_14_6 :=
  buildBucketsBT_sound (by decide) face1_Cofactor12086_gp_14 face1_Cofactor12086_W_14_ok face2_P_20_ok face1_Cofactor12086_autos_14_ok face2_bk_20_5_ok face1_Cofactor12086_chk_14_6
set_option maxRecDepth 500000 in
lemma face2_low_20 : Lower face1_Cofactor12086_R_14 face1_Cofactor12086_G_14 7 := lower_of_forestBT face1_Cofactor12086_treeRoot_14_ok face2_bk_20_6_ok face1_Cofactor12086_treeRoot_14_in
def face2_G_57 : Nat := 0xfcc0c000c000c000fcc0c000c000c000
def face2_R_57 : List Nat := varsOf 62
lemma face2_low_57_ok : liftCheck 0 16 face2_R_57 face2_G_57 face1_Cofactor12086_R_14 face1_Cofactor12086_G_14 [(VAR 4,54,38)] = true := by decide +kernel
lemma face2_low_57 : Lower face2_R_57 face2_G_57 8 := lift_of face2_low_57_ok face2_low_20
def face4_G_0 : Nat := 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0
def face4_R_0 : List Nat := varsOf 21
def face4_pos_0 : List Nat := [5,5,17,17,20,20,5,17,20]
def face4_neg_0 : List Nat := [4,1,16,1,16,4,16,4,1]
def face4_base_0 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcf,0x10a),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x173,0xa1),(0xffff0000ffff0000ffff0000ffff0000,0x1bc,0x54)]
def face4_W_0 : BT Decor := buildWiresBT 2 face4_base_0 face0_steps_0
def face4_ps_0 : BT (Option PoolSpec) := btOfList 1 []
lemma face4_gp_0 : goodPairs face4_G_0 face4_pos_0 face4_neg_0 := goodPairs_of (by decide +kernel)
lemma face4_base_0_ok : ∀ x ∈ face4_base_0, faithful face4_pos_0 face4_neg_0 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma face4_W_0_ok : btAll (fun x => faithful face4_pos_0 face4_neg_0 x ∧ x.1 < 2^128) face4_W_0 := buildWiresBT_faithful face4_base_0_ok
set_option maxRecDepth 500000 in
lemma face4_autos_0_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw face4_G_0 = face4_G_0) face1_Cofactor12086_autos_0 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma face4_slices_0_ok : btAll (fun o => ∀ p, o = some p → Slice face4_R_0 face4_G_0 p.1 p.2) face1_Cofactor12086_slices_0 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice face4_R_0 face4_G_0 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma face4_bk_0_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face4_G_0 (0 - 1) xs.toFinset) face1_Cofactor12086_bk_0_init := trivial
lemma face4_bk_0_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face4_G_0 0 xs.toFinset) face1_Cofactor12086_bk_0_init := trivial
lemma face4_bk_0_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face4_G_0 1 xs.toFinset) face1_Cofactor12086_bk_0_init := trivial
lemma face4_bk_0_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face4_G_0 2 xs.toFinset) face1_Cofactor12086_bk_0_init := trivial
def face4_P_0_3 : BT (Option BoundPool) := buildPoolsSubBT 1 face4_W_0 face4_R_0 face1_Cofactor12086_slices_0 face4_ps_0 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face4_chk_0_3 : checkNodesBT face4_W_0 face4_G_0 face0_fmask_0 face4_P_0_3 face1_Cofactor12086_autos_0 face1_Cofactor12086_bk_0_init 3 face0_nodes_0_3 = true := by decide +kernel
def face4_bk_0_3 : BT (List (List Nat)) := buildBucketsBT face4_W_0 face0_nodes_0_3
set_option maxRecDepth 500000 in
lemma face4_bk_0_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible face4_G_0 3 xs.toFinset) face4_bk_0_3 :=
  buildBucketsBT_sound (by decide) face4_gp_0 face4_W_0_ok (buildPoolsSubBT_sound face4_slices_0_ok) face4_autos_0_ok face4_bk_0_2_ok face4_chk_0_3
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma face4_forestRoot_0_ok : forestRootCheck face4_R_0 face4_G_0 [(VAR 0,5,4),(VAR 2,5,1),(VAR 4,17,1)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma face4_forestRoot_0_in : bucketContainsBT face4_bk_0_3 face4_R_0 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma face4_low_0 : Lower face4_R_0 face4_G_0 4 := lower_of_forestBT face4_forestRoot_0_ok face4_bk_0_3_ok face4_forestRoot_0_in
def face4_G_3 : Nat := 0xfaa0faa0faa0faa0faa0faa0faa0faa0
def face4_R_3 : List Nat := varsOf 13
lemma face4_low_3_ok : carryOK [(3,4)] face4_R_3 face4_G_3 face4_R_0 face4_G_0 = true := by decide +kernel
lemma face4_low_3 : Lower face4_R_3 face4_G_3 4 := carry_of face4_low_3_ok face4_low_0
def face4_G_5 : Nat := 0xfaa0faa0fa00fa00faa0faa0fa00fa00
lemma face4_low_5_ok : liftCheck 0 32 face1_h18R face4_G_5 face4_R_3 face4_G_3 [(VAR 5,37,5)] = true := by decide +kernel
lemma face4_low_5 : Lower face1_h18R face4_G_5 5 := lift_of face4_low_5_ok face4_low_3
def face4_G_9 : Nat := 0xeeee8888cccc8888eeee8888cccc8888
lemma face4_low_9_ok : carryOK [(2,4),(1,2),(1,3)] face0_R_27 face4_G_9 face1_h18R face4_G_5 = true := by decide +kernel
lemma face4_low_9 : Lower face0_R_27 face4_G_9 5 := carry_of face4_low_9_ok face4_low_5
def face5_W_0 : Array Decor := buildWires face1_Cofactor12086_base_0 face0_steps_0
def face5_P_0 : Array (Option BoundPool) := buildPools face5_W_0 face0_R_8 face0_slices_0 face0_ps_0
lemma face5_W_0_ok : ∀ x ∈ face5_W_0.toList, faithful face1_Cofactor12086_pos_0 face1_Cofactor12086_neg_0 x ∧ x.1 < 2^128 := buildWires_faithful face1_Cofactor12086_base_0_ok
lemma face5_autos_0_ok : ∀ sw ∈ face0_autos_0.toList, swapsValid sw = true ∧ permWord sw face0_G_8 = face0_G_8 := autos_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma face5_slices_0_ok : ∀ i (hi : i < face0_slices_0.size), Slice face0_R_8 face0_G_8 face0_slices_0[i].1 face0_slices_0[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice face0_R_8 face0_G_8 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma face5_P_0_ok : ∀ i (hi : i < face5_P_0.size), ∀ c, face5_P_0[i] = some c → ValidPool face0_R_8 face0_G_8 c := buildPools_sound face5_slices_0_ok
lemma face5_bk_0_init_ok : ∀ i (hi : i < face0_bk_0_init.size), ∀ xs ∈ face0_bk_0_init[i], Impossible face0_G_8 (0 - 1) xs.toFinset := by intro i hi; simp [face0_bk_0_init] at hi
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face5_chk_0_0 : checkNodes face5_W_0 face0_G_8 face0_fmask_0 face5_P_0 face0_autos_0 face0_bk_0_init 0 face0_nodes_0_0 = true := by decide +kernel
def face5_bk_0_0 : Array (List (List Nat)) := buildBuckets 1 face5_W_0 face0_nodes_0_0
lemma face5_bk_0_0_ok : ∀ i (hi : i < face5_bk_0_0.size), ∀ xs ∈ face5_bk_0_0[i], Impossible face0_G_8 0 xs.toFinset :=
  buildBuckets_sound (by decide) face1_Cofactor12086_gp_0 face5_W_0_ok face5_P_0_ok face5_autos_0_ok face5_bk_0_init_ok face5_chk_0_0
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face5_chk_0_1 : checkNodes face5_W_0 face0_G_8 face0_fmask_0 face5_P_0 face0_autos_0 face5_bk_0_0 1 face0_nodes_0_0 = true := by decide +kernel
lemma face5_bk_0_1_ok : ∀ i (hi : i < face5_bk_0_0.size), ∀ xs ∈ face5_bk_0_0[i], Impossible face0_G_8 1 xs.toFinset :=
  buildBuckets_sound (by decide) face1_Cofactor12086_gp_0 face5_W_0_ok face5_P_0_ok face5_autos_0_ok face5_bk_0_0_ok face5_chk_0_1
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face5_chk_0_2 : checkNodes face5_W_0 face0_G_8 face0_fmask_0 face5_P_0 face0_autos_0 face5_bk_0_0 2 face0_nodes_0_0 = true := by decide +kernel
lemma face5_bk_0_2_ok : ∀ i (hi : i < face5_bk_0_0.size), ∀ xs ∈ face5_bk_0_0[i], Impossible face0_G_8 2 xs.toFinset :=
  buildBuckets_sound (by decide) face1_Cofactor12086_gp_0 face5_W_0_ok face5_P_0_ok face5_autos_0_ok face5_bk_0_1_ok face5_chk_0_2
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face5_chk_0_3 : checkNodes face5_W_0 face0_G_8 face0_fmask_0 face5_P_0 face0_autos_0 face5_bk_0_0 3 face0_nodes_0_3 = true := by decide +kernel
def face5_bk_0_3 : Array (List (List Nat)) := buildBuckets 1 face5_W_0 face0_nodes_0_3
lemma face5_bk_0_3_ok : ∀ i (hi : i < face5_bk_0_3.size), ∀ xs ∈ face5_bk_0_3[i], Impossible face0_G_8 3 xs.toFinset :=
  buildBuckets_sound (by decide) face1_Cofactor12086_gp_0 face5_W_0_ok face5_P_0_ok face5_autos_0_ok face5_bk_0_2_ok face5_chk_0_3
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face5_forestRoot_0_ok : forestRootCheck face0_R_8 face0_G_8 [(VAR 1,6,4),(VAR 2,6,2),(VAR 4,18,2)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face5_forestRoot_0_in : bucketContains face5_bk_0_3 face0_R_8 = true := by decide +kernel
lemma face5_low_0 : Lower face0_R_8 face0_G_8 4 := lower_of_forest face5_forestRoot_0_ok face5_bk_0_3_ok face5_forestRoot_0_in
def face5_G_5 : Nat := 0xfc00c000fc00c000fc00c000fc00c000
def face5_R_5 : List Nat := varsOf 30
lemma face5_low_5_ok : liftCheck 0 8 face5_R_5 face5_G_5 face0_R_8 face0_G_8 [(VAR 3,14,6)] = true := by decide +kernel
lemma face5_low_5 : Lower face5_R_5 face5_G_5 5 := lift_of face5_low_5_ok face5_low_0
def face6_pos_0 : List Nat := [6,6,10,10,12,12,6,10,12]
def face6_neg_0 : List Nat := [4,2,8,2,8,4,8,4,2]
def face6_base_0 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xcf,0x10a),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x173,0xa1),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x1bc,0x54)]
def face6_W_0 : Array Decor := buildWires face6_base_0 face0_steps_0
def face6_P_0 : Array (Option BoundPool) := buildPools face6_W_0 face1_Cofactor12086_R_8 face0_slices_0 face0_ps_0
lemma face6_gp_0 : goodPairs face1_Cofactor12086_G_8 face6_pos_0 face6_neg_0 := goodPairs_of (by decide +kernel)
lemma face6_base_0_ok : ∀ x ∈ face6_base_0, faithful face6_pos_0 face6_neg_0 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma face6_W_0_ok : ∀ x ∈ face6_W_0.toList, faithful face6_pos_0 face6_neg_0 x ∧ x.1 < 2^128 := buildWires_faithful face6_base_0_ok
lemma face6_autos_0_ok : ∀ sw ∈ face0_autos_0.toList, swapsValid sw = true ∧ permWord sw face1_Cofactor12086_G_8 = face1_Cofactor12086_G_8 := autos_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma face6_slices_0_ok : ∀ i (hi : i < face0_slices_0.size), Slice face1_Cofactor12086_R_8 face1_Cofactor12086_G_8 face0_slices_0[i].1 face0_slices_0[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice face1_Cofactor12086_R_8 face1_Cofactor12086_G_8 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma face6_P_0_ok : ∀ i (hi : i < face6_P_0.size), ∀ c, face6_P_0[i] = some c → ValidPool face1_Cofactor12086_R_8 face1_Cofactor12086_G_8 c := buildPools_sound face6_slices_0_ok
lemma face6_bk_0_init_ok : ∀ i (hi : i < face0_bk_0_init.size), ∀ xs ∈ face0_bk_0_init[i], Impossible face1_Cofactor12086_G_8 (0 - 1) xs.toFinset := by intro i hi; simp [face0_bk_0_init] at hi
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face6_chk_0_0 : checkNodes face6_W_0 face1_Cofactor12086_G_8 face0_fmask_0 face6_P_0 face0_autos_0 face0_bk_0_init 0 face0_nodes_0_0 = true := by decide +kernel
def face6_bk_0_0 : Array (List (List Nat)) := buildBuckets 1 face6_W_0 face0_nodes_0_0
lemma face6_bk_0_0_ok : ∀ i (hi : i < face6_bk_0_0.size), ∀ xs ∈ face6_bk_0_0[i], Impossible face1_Cofactor12086_G_8 0 xs.toFinset :=
  buildBuckets_sound (by decide) face6_gp_0 face6_W_0_ok face6_P_0_ok face6_autos_0_ok face6_bk_0_init_ok face6_chk_0_0
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face6_chk_0_1 : checkNodes face6_W_0 face1_Cofactor12086_G_8 face0_fmask_0 face6_P_0 face0_autos_0 face6_bk_0_0 1 face0_nodes_0_0 = true := by decide +kernel
lemma face6_bk_0_1_ok : ∀ i (hi : i < face6_bk_0_0.size), ∀ xs ∈ face6_bk_0_0[i], Impossible face1_Cofactor12086_G_8 1 xs.toFinset :=
  buildBuckets_sound (by decide) face6_gp_0 face6_W_0_ok face6_P_0_ok face6_autos_0_ok face6_bk_0_0_ok face6_chk_0_1
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face6_chk_0_2 : checkNodes face6_W_0 face1_Cofactor12086_G_8 face0_fmask_0 face6_P_0 face0_autos_0 face6_bk_0_0 2 face0_nodes_0_0 = true := by decide +kernel
lemma face6_bk_0_2_ok : ∀ i (hi : i < face6_bk_0_0.size), ∀ xs ∈ face6_bk_0_0[i], Impossible face1_Cofactor12086_G_8 2 xs.toFinset :=
  buildBuckets_sound (by decide) face6_gp_0 face6_W_0_ok face6_P_0_ok face6_autos_0_ok face6_bk_0_1_ok face6_chk_0_2
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face6_chk_0_3 : checkNodes face6_W_0 face1_Cofactor12086_G_8 face0_fmask_0 face6_P_0 face0_autos_0 face6_bk_0_0 3 face0_nodes_0_3 = true := by decide +kernel
def face6_bk_0_3 : Array (List (List Nat)) := buildBuckets 1 face6_W_0 face0_nodes_0_3
lemma face6_bk_0_3_ok : ∀ i (hi : i < face6_bk_0_3.size), ∀ xs ∈ face6_bk_0_3[i], Impossible face1_Cofactor12086_G_8 3 xs.toFinset :=
  buildBuckets_sound (by decide) face6_gp_0 face6_W_0_ok face6_P_0_ok face6_autos_0_ok face6_bk_0_2_ok face6_chk_0_3
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face6_forestRoot_0_ok : forestRootCheck face1_Cofactor12086_R_8 face1_Cofactor12086_G_8 [(VAR 1,6,4),(VAR 2,6,2),(VAR 3,10,2)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face6_forestRoot_0_in : bucketContains face6_bk_0_3 face1_Cofactor12086_R_8 = true := by decide +kernel
lemma face6_low_0 : Lower face1_Cofactor12086_R_8 face1_Cofactor12086_G_8 4 := lower_of_forest face6_forestRoot_0_ok face6_bk_0_3_ok face6_forestRoot_0_in
def face7_G_15 : Nat := 0xfff0ff00fff00000fff0ff00fff00000
def face7_pos_15 : List Nat := [20,20,24,24,28,40,40,44,44,52,52,56,20,20,20,24,24,24,40,40,40]
def face7_neg_15 : List Nat := [16,4,16,8,12,32,8,36,12,48,36,48,12,36,48,12,36,48,12,36,48]
def face7_fmask_15 : Nat := fullMask 21
def face7_base_15 : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x7793,0xdb592),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x1f89fc,0x49158),(0xffff0000ffff0000ffff0000ffff0000,0x3fe1f,0x124a05),(0xffffffff00000000ffffffff00000000,0x1c0fe0,0x1b6ea0)]
def face7_W_15 : Array Decor := buildWires face7_base_15 face0_steps_0
def face7_P_15 : Array (Option BoundPool) := buildPools face7_W_15 face0_R_21 face0_slices_0 face0_ps_0
lemma face7_gp_15 : goodPairs face7_G_15 face7_pos_15 face7_neg_15 := goodPairs_of (by decide +kernel)
lemma face7_base_15_ok : ∀ x ∈ face7_base_15, faithful face7_pos_15 face7_neg_15 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma face7_W_15_ok : ∀ x ∈ face7_W_15.toList, faithful face7_pos_15 face7_neg_15 x ∧ x.1 < 2^128 := buildWires_faithful face7_base_15_ok
lemma face7_autos_15_ok : ∀ sw ∈ face0_autos_0.toList, swapsValid sw = true ∧ permWord sw face7_G_15 = face7_G_15 := autos_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma face7_slices_15_ok : ∀ i (hi : i < face0_slices_0.size), Slice face0_R_21 face7_G_15 face0_slices_0[i].1 face0_slices_0[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice face0_R_21 face7_G_15 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma face7_P_15_ok : ∀ i (hi : i < face7_P_15.size), ∀ c, face7_P_15[i] = some c → ValidPool face0_R_21 face7_G_15 c := buildPools_sound face7_slices_15_ok
lemma face7_bk_15_init_ok : ∀ i (hi : i < face0_bk_0_init.size), ∀ xs ∈ face0_bk_0_init[i], Impossible face7_G_15 (0 - 1) xs.toFinset := by intro i hi; simp [face0_bk_0_init] at hi
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face7_chk_15_0 : checkNodes face7_W_15 face7_G_15 face7_fmask_15 face7_P_15 face0_autos_0 face0_bk_0_init 0 face0_nodes_0_0 = true := by decide +kernel
def face7_bk_15_0 : Array (List (List Nat)) := buildBuckets 1 face7_W_15 face0_nodes_0_0
lemma face7_bk_15_0_ok : ∀ i (hi : i < face7_bk_15_0.size), ∀ xs ∈ face7_bk_15_0[i], Impossible face7_G_15 0 xs.toFinset :=
  buildBuckets_sound (by decide) face7_gp_15 face7_W_15_ok face7_P_15_ok face7_autos_15_ok face7_bk_15_init_ok face7_chk_15_0
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face7_chk_15_1 : checkNodes face7_W_15 face7_G_15 face7_fmask_15 face7_P_15 face0_autos_0 face7_bk_15_0 1 face0_nodes_0_0 = true := by decide +kernel
lemma face7_bk_15_1_ok : ∀ i (hi : i < face7_bk_15_0.size), ∀ xs ∈ face7_bk_15_0[i], Impossible face7_G_15 1 xs.toFinset :=
  buildBuckets_sound (by decide) face7_gp_15 face7_W_15_ok face7_P_15_ok face7_autos_15_ok face7_bk_15_0_ok face7_chk_15_1
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face7_chk_15_2 : checkNodes face7_W_15 face7_G_15 face7_fmask_15 face7_P_15 face0_autos_0 face7_bk_15_0 2 face0_nodes_0_0 = true := by decide +kernel
lemma face7_bk_15_2_ok : ∀ i (hi : i < face7_bk_15_0.size), ∀ xs ∈ face7_bk_15_0[i], Impossible face7_G_15 2 xs.toFinset :=
  buildBuckets_sound (by decide) face7_gp_15 face7_W_15_ok face7_P_15_ok face7_autos_15_ok face7_bk_15_1_ok face7_chk_15_2
def face7_nodes_15_3 : List NodeSpec := [([0,1,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face7_chk_15_3 : checkNodes face7_W_15 face7_G_15 face7_fmask_15 face7_P_15 face0_autos_0 face7_bk_15_0 3 face7_nodes_15_3 = true := by decide +kernel
def face7_bk_15_3 : Array (List (List Nat)) := buildBuckets 1 face7_W_15 face7_nodes_15_3
lemma face7_bk_15_3_ok : ∀ i (hi : i < face7_bk_15_3.size), ∀ xs ∈ face7_bk_15_3[i], Impossible face7_G_15 3 xs.toFinset :=
  buildBuckets_sound (by decide) face7_gp_15 face7_W_15_ok face7_P_15_ok face7_autos_15_ok face7_bk_15_2_ok face7_chk_15_3
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face7_forestRoot_15_ok : forestRootCheck face0_R_21 face7_G_15 [(VAR 2,20,16),(VAR 3,24,16),(VAR 4,20,4),(VAR 5,40,8)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma face7_forestRoot_15_in : bucketContains face7_bk_15_3 face0_R_21 = true := by decide +kernel
lemma face7_low_15 : Lower face0_R_21 face7_G_15 4 := lower_of_forest face7_forestRoot_15_ok face7_bk_15_3_ok face7_forestRoot_15_in

def h0R : List Nat := varsOf 63
def h0G : Nat := 0xfee8e888e8a0c080fee8e888e8a0c080
def h0Pos : List Nat := [7,7,7,7,7,7,7,7,7,14,14,14,14,14,14,14,14,14,14,14,15,15,15,21,21,21,21,21,21,21,21,23,23,23,27,27,27,27,27,29,29,29,29,30,30,30,35,35,35,35,35,35,35,35,39,39,43,43,43,43,45,45,45,45,45,46,46,46,51,51,51,53,53,53,54,54,54,54,57,57,57,57,58,58,58,58,60,60,60,60]
def h0Neg : List Nat := [3,4,5,6,11,13,19,22,37,2,4,6,10,12,13,26,28,38,42,44,6,11,13,1,4,5,13,17,20,25,28,5,19,22,11,18,19,25,26,13,17,25,28,22,26,28,1,3,19,33,34,41,49,50,37,38,9,11,41,42,9,13,37,41,44,38,42,44,19,49,50,37,49,52,22,38,50,52,25,41,49,56,26,42,50,56,28,44,52,56]
def h0Mask : Nat := fullMask 90
def h0Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x3c3f1ffffc7fffff001ff,0x1c1b0f75bc3b5aee04175),(0xcccccccccccccccccccccccccccccccc,0x3c3c7e0ffff87f807fffff,0x1c1c560aa5985f00369ad9),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x3c03f8ff0c03f83ffffffff,0x1c02e8b60c02c82d75b6dae),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x3ffc00fff003ffc007ffe00,0x2eec00dbf0836e4646df030),(0xffff0000ffff0000ffff0000ffff0000,0x3fffff000003fffff800000,0x377777000313f7b780180c0),(0xffffffff00000000ffffffff00000000,0x3ffffffffffc00000000000,0x3bbbbefccfe0000000e0100)]
def h0Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,6,2),(3,6,2),(0,6,2),(3,9,3),(3,9,4),(3,9,5),(3,8,5),(0,6,3),(3,6,3),(0,15,4),(0,15,5),(0,2,4),(3,2,3),(3,19,4),(3,18,5),(0,3,4),(3,2,4),(0,2,5),(3,2,5),(3,25,4),(0,4,5),(0,6,4),(3,6,4),(0,6,5),(3,30,2),(3,30,3),(3,30,4),(3,6,5),(0,34,4),(0,2,3),(0,36,4),(3,36,4),(1,6,36),(0,39,5),(0,39,4),(0,41,5),(3,41,5),(3,40,4),(2,39,27),(1,6,37),(0,46,5),(3,46,5),(3,37,5),(0,36,5),(1,6,50),(3,36,5),(1,52,6),(3,52,4),(1,6,20),(3,19,5),(1,19,6),(3,24,3),(0,24,4),(3,24,4),(1,25,6),(3,25,3),(1,6,62),(0,62,4),(2,2,22),(3,2,22),(3,66,5),(1,65,6),(3,65,5),(0,22,5),(1,6,70),(1,8,70),(1,2,70),(2,2,70),(0,2,71),(1,2,71),(3,75,76),(2,2,71),(3,2,71),(3,6,73),(3,22,5),(1,81,6),(0,3,5),(3,2,83),(2,2,83),(1,85,6),(3,83,4),(1,87,6),(1,0,1),(0,89,2),(3,90,5),(0,89,3),(0,92,4),(0,92,5),(0,89,4),(0,89,5),(1,96,2),(0,97,3),(0,97,4),(3,96,2),(3,100,3),(3,100,4),(3,96,3),(3,96,4),(0,96,4),(1,96,36),(2,0,36),(2,89,36),(2,89,37),(2,89,2),(2,89,50),(3,52,89),(2,89,20),(3,19,89),(3,25,89),(2,89,62),(3,65,89),(1,90,70),(2,89,70),(3,81,89),(3,85,89),(3,87,89),(2,0,1),(3,123,2),(3,124,5),(3,123,3),(1,126,2),(3,126,2),(3,126,4),(0,126,4),(3,126,5),(0,126,5),(1,126,18),(1,25,126),(3,123,4),(0,135,5),(3,123,5),(3,18,3),(3,23,3),(1,123,36),(1,0,36),(1,123,37),(1,123,50),(1,52,123),(1,123,20),(1,19,123),(1,123,18),(1,123,59),(1,21,123),(1,123,139),(3,23,5),(1,23,123),(1,25,123),(1,123,62),(1,123,26),(1,123,2),(1,65,123),(1,123,70),(1,81,123),(1,85,123),(1,87,123),(2,2,27),(1,162,123),(2,3,27),(1,164,123),(3,0,1),(0,0,2),(1,0,2),(2,0,2),(3,0,2),(0,0,3),(3,171,1),(3,172,4),(1,172,18),(3,172,5),(0,171,2),(3,171,2),(0,171,4),(0,1,2),(1,1,2),(2,1,2),(3,1,2),(3,171,4),(0,1,5),(3,1,5),(0,171,5),(3,171,5),(0,1,4),(1,171,2),(3,188,5),(3,1,4),(3,191,5),(3,191,189),(1,25,191),(3,184,4),(3,185,4),(3,0,3),(3,197,1),(3,198,4),(1,198,18),(3,198,5),(3,197,2),(3,197,4),(1,203,1),(3,203,1),(1,203,2),(0,206,3),(3,203,2),(3,203,5),(0,203,5),(1,203,184),(0,203,2),(1,25,203),(3,197,5),(1,191,197),(1,197,2),(3,191,216),(1,25,197),(1,197,184),(3,184,3),(1,197,18),(1,195,197),(1,184,18),(1,23,197),(0,0,4),(1,225,1),(1,225,2),(0,1,227),(3,225,2),(3,229,1),(3,225,3),(3,231,1),(0,226,3),(1,233,2),(3,225,1),(0,235,3),(1,236,225),(3,235,3),(3,229,3),(0,1,3),(3,240,2),(3,240,227),(3,1,3),(1,229,240),(1,240,2),(0,225,2),(3,229,5),(1,229,184),(0,184,3),(1,231,1),(1,231,2),(0,251,4),(3,231,2),(3,231,5),(0,231,5),(1,231,184),(0,231,2),(0,225,5),(3,258,3),(1,258,240),(3,225,5),(2,225,240),(0,237,5),(2,225,2),(1,264,240),(3,240,5),(1,243,225),(3,243,5),(1,225,268),(1,225,184),(0,270,3),(1,19,225),(3,185,3),(1,225,273),(3,19,1),(1,225,275),(0,226,5),(2,225,1),(2,1,83),(1,2,83),(0,226,280),(1,225,249),(3,1,83),(1,279,225),(1,225,50),(3,0,4),(3,286,1),(3,286,2),(3,288,5),(3,286,3),(3,286,5),(3,291,3),(1,286,2),(1,286,1),(0,0,5),(3,0,5),(3,178,5),(3,0,22),(3,298,5),(2,0,22),(0,1,22),(3,1,22),(2,1,22),(1,0,70),(1,1,70),(2,0,70),(2,1,70)]
def h0W : BT Decor := buildWiresBT 9 h0Base h0Steps
def h0AutoList : List (List (Nat × Nat)) := [[],[(1,2),(4,5)],[(0,1),(3,4)],[(0,1),(1,2),(3,4),(4,5)],[(0,2),(1,2),(3,5),(4,5)],[(0,2),(3,5)]]
def h0Autos : BT (List (Nat × Nat)) := btOfList 3 h0AutoList
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
def h0SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 8,10),some (subcubeFast 0 16,10),some (subcubeFast 0 32,10),some (subcubeFast 0 1,9),some (subcubeFast 0 2,9),some (subcubeFast 0 4,9),some (subcubeFast 1 0,8),some (subcubeFast 4 0,8),some (subcubeFast 0 9,7),some (subcubeFast 2 8,7),some (subcubeFast 4 8,7),some (subcubeFast 1 16,7),some (subcubeFast 0 18,7),some (subcubeFast 4 16,7),some (subcubeFast 0 24,7),some (subcubeFast 1 32,7),some (subcubeFast 2 32,7),some (subcubeFast 0 36,7),some (subcubeFast 0 40,7),some (subcubeFast 0 48,7),some (0xff0000ff00000000ff0000ff,7),some (0xff00000000ff0000ff00000000ff,7),some (0xff0000000000ff00ff0000000000ff,7),some (subcubeFast 16 1,5),some (subcubeFast 0 20,5),some (subcubeFast 16 4,5),some (subcubeFast 0 33,5),some (subcubeFast 2 9,4),some (subcubeFast 4 9,4),some (subcubeFast 2 12,4),some (subcubeFast 4 10,4),some (subcubeFast 1 18,4),some (subcubeFast 1 20,4),some (subcubeFast 4 17,4),some (subcubeFast 4 18,4),some (subcubeFast 1 24,4),some (subcubeFast 16 9,4),some (subcubeFast 8 18,4),some (subcubeFast 4 24,4),some (subcubeFast 1 34,4),some (subcubeFast 2 33,4),some (subcubeFast 32 4,4),some (subcubeFast 1 36,4),some (subcubeFast 2 36,4),some (subcubeFast 1 40,4),some (subcubeFast 32 9,4),some (subcubeFast 2 40,4),some (subcubeFast 4 40,4),some (subcubeFast 8 36,4),some (subcubeFast 1 48,4),some (subcubeFast 2 48,4),some (subcubeFast 32 18,4),some (subcubeFast 4 48,4),some (subcubeFast 16 36,4),some (subcubeFast 8 48,4),some (subcubeFast 16 40,4),some (subcubeFast 32 24,4)]
def h0Slices : BT (Option (Nat × Nat)) := btOfList 6 h0SliceList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput0Map : Lower (varsOf 55) 0xfcfce8e8e8e88080fcfce8e8e8e88080 10 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (1, 2), (2, 3), (3, 4), (1, 2), (2, 3)]) (roots2 := face0_R_48) (T2 := face0_G_48) _ face0_low_48
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput0Flip : Lower (varsOf 55) 0xfefee8e8e8e8c0c0fefee8e8e8e8c0c0 10 := dualLower (by decide +kernel) (by decide +kernel) sliceInput0Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice0 : Slice h0R h0G (subcubeFast 0 8) 10 := slice_fast_direct (zDead := 0) (qRoots := varsOf 55) (qGoal := 0xfefee8e8e8e8c0c0fefee8e8e8e8c0c0) (by decide +kernel) sliceInput0Flip
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput1Map : Lower (varsOf 47) 0xfae8fae8e880e880fae8fae8e880e880 10 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (2, 3), (3, 4), (1, 2), (2, 3), (0, 1)]) (roots2 := face0_R_48) (T2 := face0_G_48) _ face0_low_48
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput1Flip : Lower (varsOf 47) 0xfee8fee8e8a0e8a0fee8fee8e8a0e8a0 10 := dualLower (by decide +kernel) (by decide +kernel) sliceInput1Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice1 : Slice h0R h0G (subcubeFast 0 16) 10 := slice_fast_direct (zDead := 0) (qRoots := varsOf 47) (qGoal := 0xfee8fee8e8a0e8a0fee8fee8e8a0e8a0) (by decide +kernel) sliceInput1Flip
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput2Map : Lower (varsOf 31) 0xeee8e880eee8e880eee8e880eee8e880 10 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (2, 3), (3, 4), (1, 2), (2, 3), (0, 1), (1, 2)]) (roots2 := face0_R_48) (T2 := face0_G_48) _ face0_low_48
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput2Flip : Lower (varsOf 31) 0xfee8e888fee8e888fee8e888fee8e888 10 := dualLower (by decide +kernel) (by decide +kernel) sliceInput2Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice2 : Slice h0R h0G (subcubeFast 0 32) 10 := slice_fast_direct (zDead := 0) (qRoots := varsOf 31) (qGoal := 0xfee8e888fee8e888fee8e888fee8e888) (by decide +kernel) sliceInput2Flip
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput3Map : Lower (varsOf 62) 0xfcfcf0c0ccc0c000fcfcf0c0ccc0c000 9 := by
  apply carry_of (swaps := [(0, 1), (1, 2), (2, 3), (3, 4), (2, 3), (0, 1), (1, 2), (0, 1)]) (roots2 := face1_h9R) (T2 := face1_h9G) _ face1_h9Bound
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput3Flip : Lower (varsOf 62) 0xfffcfcccfcf0c0c0fffcfcccfcf0c0c0 9 := dualLower (by decide +kernel) (by decide +kernel) sliceInput3Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice3 : Slice h0R h0G (subcubeFast 0 1) 9 := slice_fast_direct (zDead := 0) (qRoots := varsOf 62) (qGoal := 0xfffcfcccfcf0c0c0fffcfcccfcf0c0c0) (by decide +kernel) sliceInput3Flip
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput4Map : Lower (varsOf 61) 0xfaf0faa0aaa0a000faf0faa0aaa0a000 9 := by
  apply carry_of (swaps := [(3, 4), (0, 1), (1, 2), (2, 3), (0, 1), (1, 2)]) (roots2 := face1_h9R) (T2 := face1_h9G) _ face1_h9Bound
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput4Flip : Lower (varsOf 61) 0xfffafaaafaa0f0a0fffafaaafaa0f0a0 9 := dualLower (by decide +kernel) (by decide +kernel) sliceInput4Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice4 : Slice h0R h0G (subcubeFast 0 2) 9 := slice_fast_direct (zDead := 0) (qRoots := varsOf 61) (qGoal := 0xfffafaaafaa0f0a0fffafaaafaa0f0a0) (by decide +kernel) sliceInput4Flip
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput5Map : Lower (varsOf 59) 0xeeccaa88ee888800eeccaa88ee888800 9 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (0, 1), (1, 2), (2, 3), (0, 1)]) (roots2 := face1_h9R) (T2 := face1_h9G) _ face1_h9Bound
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput5Flip : Lower (varsOf 59) 0xffeeee88eeaacc88ffeeee88eeaacc88 9 := dualLower (by decide +kernel) (by decide +kernel) sliceInput5Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice5 : Slice h0R h0G (subcubeFast 0 4) 9 := slice_fast_direct (zDead := 0) (qRoots := varsOf 59) (qGoal := 0xffeeee88eeaacc88ffeeee88eeaacc88) (by decide +kernel) sliceInput5Flip
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput6Map : Lower (varsOf 62) 0xfcc0c000c000c000fcc0c000c000c000 8 := by
  apply carry_of (swaps := []) (roots2 := face2_R_57) (T2 := face2_G_57) _ face2_low_57
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice6 : Slice h0R h0G (subcubeFast 1 0) 8 := slice_fast_direct (zDead := 0) (qRoots := varsOf 62) (qGoal := 0xfcc0c000c000c000fcc0c000c000c000) (by decide +kernel) sliceInput6Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput7Map : Lower (varsOf 59) 0xee88888888000000ee88888888000000 8 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (0, 1), (1, 2)]) (roots2 := face2_R_57) (T2 := face2_G_57) _ face2_low_57
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice7 : Slice h0R h0G (subcubeFast 4 0) 8 := slice_fast_direct (zDead := 0) (qRoots := varsOf 59) (qGoal := 0xee88888888000000ee88888888000000) (by decide +kernel) sliceInput7Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput8Map : Lower (varsOf 54) 0xfcfcc0c0c0c00000fcfcc0c0c0c00000 7 := by
  apply carry_of (swaps := [(1, 2), (2, 3)]) (roots2 := face0_R_21) (T2 := face0_G_21) _ face0_low_21
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput8Flip : Lower (varsOf 54) 0xfffffcfcfcfcc0c0fffffcfcfcfcc0c0 7 := dualLower (by decide +kernel) (by decide +kernel) sliceInput8Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice8 : Slice h0R h0G (subcubeFast 0 9) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 54) (qGoal := 0xfffffcfcfcfcc0c0fffffcfcfcfcc0c0) (by decide +kernel) sliceInput8Flip
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput9Map : Lower (varsOf 53) 0xfafaa0a0a0a00000fafaa0a0a0a00000 7 := by
  apply carry_of (swaps := [(1, 2), (2, 3), (0, 1)]) (roots2 := face0_R_21) (T2 := face0_G_21) _ face0_low_21
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice9 : Slice h0R h0G (subcubeFast 2 8) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 53) (qGoal := 0xfafaa0a0a0a00000fafaa0a0a0a00000) (by decide +kernel) sliceInput9Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput10Map : Lower (varsOf 51) 0xeeee888888880000eeee888888880000 7 := by
  apply carry_of (swaps := [(1, 2), (2, 3), (0, 1), (1, 2)]) (roots2 := face0_R_21) (T2 := face0_G_21) _ face0_low_21
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice10 : Slice h0R h0G (subcubeFast 4 8) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 51) (qGoal := 0xeeee888888880000eeee888888880000) (by decide +kernel) sliceInput10Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput11Map : Lower (varsOf 46) 0xfcc0fcc0c000c000fcc0fcc0c000c000 7 := by
  apply carry_of (swaps := [(1, 2), (2, 3), (3, 4)]) (roots2 := face0_R_21) (T2 := face0_G_21) _ face0_low_21
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice11 : Slice h0R h0G (subcubeFast 1 16) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 46) (qGoal := 0xfcc0fcc0c000c000fcc0fcc0c000c000) (by decide +kernel) sliceInput11Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput12Map : Lower (varsOf 45) 0xfaa0faa0a000a000faa0faa0a000a000 7 := by
  apply carry_of (swaps := [(1, 2), (2, 3), (3, 4), (0, 1)]) (roots2 := face0_R_21) (T2 := face0_G_21) _ face0_low_21
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput12Flip : Lower (varsOf 45) 0xfffafffafaa0faa0fffafffafaa0faa0 7 := dualLower (by decide +kernel) (by decide +kernel) sliceInput12Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice12 : Slice h0R h0G (subcubeFast 0 18) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 45) (qGoal := 0xfffafffafaa0faa0fffafffafaa0faa0) (by decide +kernel) sliceInput12Flip
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput13Map : Lower (varsOf 43) 0xee88ee8888008800ee88ee8888008800 7 := by
  apply carry_of (swaps := [(1, 2), (2, 3), (3, 4), (0, 1), (1, 2)]) (roots2 := face0_R_21) (T2 := face0_G_21) _ face0_low_21
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice13 : Slice h0R h0G (subcubeFast 4 16) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 43) (qGoal := 0xee88ee8888008800ee88ee8888008800) (by decide +kernel) sliceInput13Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput14Map : Lower (varsOf 39) 0xe8e8e8e880808080e8e8e8e880808080 7 := by
  apply carry_of (swaps := [(1, 2), (2, 3), (3, 4), (0, 1), (1, 2), (2, 3)]) (roots2 := face0_R_21) (T2 := face0_G_21) _ face0_low_21
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput14Flip : Lower (varsOf 39) 0xfefefefee8e8e8e8fefefefee8e8e8e8 7 := dualLower (by decide +kernel) (by decide +kernel) sliceInput14Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice14 : Slice h0R h0G (subcubeFast 0 24) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 39) (qGoal := 0xfefefefee8e8e8e8fefefefee8e8e8e8) (by decide +kernel) sliceInput14Flip
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput15Map : Lower (varsOf 30) 0xfcc0c000fcc0c000fcc0c000fcc0c000 7 := by
  apply carry_of (swaps := [(1, 2), (2, 3), (3, 4), (4, 5)]) (roots2 := face0_R_21) (T2 := face0_G_21) _ face0_low_21
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice15 : Slice h0R h0G (subcubeFast 1 32) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 30) (qGoal := 0xfcc0c000fcc0c000fcc0c000fcc0c000) (by decide +kernel) sliceInput15Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput16Map : Lower (varsOf 29) 0xfaa0a000faa0a000faa0a000faa0a000 7 := by
  apply carry_of (swaps := [(1, 2), (2, 3), (3, 4), (4, 5), (0, 1)]) (roots2 := face0_R_21) (T2 := face0_G_21) _ face0_low_21
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice16 : Slice h0R h0G (subcubeFast 2 32) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 29) (qGoal := 0xfaa0a000faa0a000faa0a000faa0a000) (by decide +kernel) sliceInput16Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput17Map : Lower (varsOf 27) 0xee888800ee888800ee888800ee888800 7 := by
  apply carry_of (swaps := [(1, 2), (2, 3), (3, 4), (4, 5), (0, 1), (1, 2)]) (roots2 := face0_R_21) (T2 := face0_G_21) _ face0_low_21
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput17Flip : Lower (varsOf 27) 0xffeeee88ffeeee88ffeeee88ffeeee88 7 := dualLower (by decide +kernel) (by decide +kernel) sliceInput17Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice17 : Slice h0R h0G (subcubeFast 0 36) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 27) (qGoal := 0xffeeee88ffeeee88ffeeee88ffeeee88) (by decide +kernel) sliceInput17Flip
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput18Map : Lower (varsOf 23) 0xe8e88080e8e88080e8e88080e8e88080 7 := by
  apply carry_of (swaps := [(1, 2), (2, 3), (3, 4), (4, 5), (0, 1), (1, 2), (2, 3)]) (roots2 := face0_R_21) (T2 := face0_G_21) _ face0_low_21
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput18Flip : Lower (varsOf 23) 0xfefee8e8fefee8e8fefee8e8fefee8e8 7 := dualLower (by decide +kernel) (by decide +kernel) sliceInput18Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice18 : Slice h0R h0G (subcubeFast 0 40) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 23) (qGoal := 0xfefee8e8fefee8e8fefee8e8fefee8e8) (by decide +kernel) sliceInput18Flip
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput19Map : Lower (varsOf 15) 0xe880e880e880e880e880e880e880e880 7 := by
  apply carry_of (swaps := [(1, 2), (2, 3), (3, 4), (4, 5), (0, 1), (1, 2), (2, 3), (3, 4)]) (roots2 := face0_R_21) (T2 := face0_G_21) _ face0_low_21
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput19Flip : Lower (varsOf 15) 0xfee8fee8fee8fee8fee8fee8fee8fee8 7 := dualLower (by decide +kernel) (by decide +kernel) sliceInput19Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice19 : Slice h0R h0G (subcubeFast 0 48) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 15) (qGoal := 0xfee8fee8fee8fee8fee8fee8fee8fee8) (by decide +kernel) sliceInput19Flip
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput20Map : Lower (varsOf 15) 0xe880e880e880e880e880e880e880e880 7 := by
  apply carry_of (swaps := [(1, 2), (2, 3), (3, 4), (4, 5), (0, 1), (1, 2), (2, 3), (3, 4)]) (roots2 := face0_R_21) (T2 := face0_G_21) _ face0_low_21
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice20 : Slice h0R h0G 0xff0000ff00000000ff0000ff 7 := mappedSlice (f := identifyRow 32 0 3 4) (R := varsOf 15) (G := 0xe880e880e880e880e880e880e880e880) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) sliceInput20Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice21 : Slice h0R h0G 0xff00000000ff0000ff00000000ff 7 := mappedSlice (f := identifyRow 16 0 3 5) (R := varsOf 15) (G := 0xe880e880e880e880e880e880e880e880) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) sliceInput20Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput21Map : Lower (varsOf 23) 0xe8e88080e8e88080e8e88080e8e88080 7 := by
  apply carry_of (swaps := [(1, 2), (2, 3), (3, 4), (4, 5), (0, 1), (1, 2), (2, 3)]) (roots2 := face0_R_21) (T2 := face0_G_21) _ face0_low_21
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice22 : Slice h0R h0G 0xff0000000000ff00ff0000000000ff 7 := mappedSlice (f := identifyRow 8 0 4 5) (R := varsOf 23) (G := 0xe8e88080e8e88080e8e88080e8e88080) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) sliceInput21Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput22Map : Lower (varsOf 46) 0xfcccfcccc0c0c0c0fcccfcccc0c0c0c0 5 := by
  apply carry_of (swaps := [(4, 5), (3, 4), (0, 1), (1, 2), (0, 1)]) (roots2 := face0_R_27) (T2 := face4_G_9) _ face4_low_9
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice23 : Slice h0R h0G (subcubeFast 16 1) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 46) (qGoal := 0xfcccfcccc0c0c0c0fcccfcccc0c0c0c0) (by decide +kernel) sliceInput22Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput23Map : Lower (varsOf 43) 0xaa88aa8888008800aa88aa8888008800 5 := by
  apply carry_of (swaps := [(4, 5), (2, 3), (0, 1), (1, 2), (0, 1)]) (roots2 := face5_R_5) (T2 := face5_G_5) _ face5_low_5
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput23Flip : Lower (varsOf 43) 0xffeeffeeeeaaeeaaffeeffeeeeaaeeaa 5 := dualLower (by decide +kernel) (by decide +kernel) sliceInput23Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice24 : Slice h0R h0G (subcubeFast 0 20) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 43) (qGoal := 0xffeeffeeeeaaeeaaffeeffeeeeaaeeaa) (by decide +kernel) sliceInput23Flip
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput24Map : Lower (varsOf 43) 0xee88ee88cc88cc88ee88ee88cc88cc88 5 := by
  apply carry_of (swaps := [(3, 4)]) (roots2 := face0_R_27) (T2 := face4_G_9) _ face4_low_9
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice25 : Slice h0R h0G (subcubeFast 16 4) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 43) (qGoal := 0xee88ee88cc88cc88ee88ee88cc88cc88) (by decide +kernel) sliceInput24Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput25Map : Lower (varsOf 30) 0xccc0c000ccc0c000ccc0c000ccc0c000 5 := by
  apply carry_of (swaps := [(2, 3), (1, 2)]) (roots2 := face5_R_5) (T2 := face5_G_5) _ face5_low_5
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput25Flip : Lower (varsOf 30) 0xfffcfcccfffcfcccfffcfcccfffcfccc 5 := dualLower (by decide +kernel) (by decide +kernel) sliceInput25Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice26 : Slice h0R h0G (subcubeFast 0 33) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 30) (qGoal := 0xfffcfcccfffcfcccfffcfcccfffcfccc) (by decide +kernel) sliceInput25Flip
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput26Map : Lower (varsOf 52) 0xfffff0f0f0f00000fffff0f0f0f00000 4 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (2, 3), (3, 4), (1, 2)]) (roots2 := face1_Cofactor12086_R_8) (T2 := face1_Cofactor12086_G_8) _ face6_low_0
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice27 : Slice h0R h0G (subcubeFast 2 9) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 52) (qGoal := 0xfffff0f0f0f00000fffff0f0f0f00000) (by decide +kernel) sliceInput26Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput27Map : Lower (varsOf 50) 0xffffcccccccc0000ffffcccccccc0000 4 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (2, 3), (3, 4)]) (roots2 := face1_Cofactor12086_R_8) (T2 := face1_Cofactor12086_G_8) _ face6_low_0
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice28 : Slice h0R h0G (subcubeFast 4 9) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 50) (qGoal := 0xffffcccccccc0000ffffcccccccc0000) (by decide +kernel) sliceInput27Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput28Map : Lower (varsOf 49) 0xffffaaaaaaaa0000ffffaaaaaaaa0000 4 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (2, 3), (3, 4), (0, 1)]) (roots2 := face1_Cofactor12086_R_8) (T2 := face1_Cofactor12086_G_8) _ face6_low_0
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice29 : Slice h0R h0G (subcubeFast 2 12) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 49) (qGoal := 0xffffaaaaaaaa0000ffffaaaaaaaa0000) (by decide +kernel) sliceInput28Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice30 : Slice h0R h0G (subcubeFast 4 10) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 49) (qGoal := 0xffffaaaaaaaa0000ffffaaaaaaaa0000) (by decide +kernel) sliceInput28Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput29Map : Lower (varsOf 44) 0xfff0fff0f000f000fff0fff0f000f000 4 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (2, 3), (1, 2)]) (roots2 := face1_Cofactor12086_R_8) (T2 := face1_Cofactor12086_G_8) _ face6_low_0
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice31 : Slice h0R h0G (subcubeFast 1 18) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 44) (qGoal := 0xfff0fff0f000f000fff0fff0f000f000) (by decide +kernel) sliceInput29Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput30Map : Lower (varsOf 42) 0xffccffcccc00cc00ffccffcccc00cc00 4 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (2, 3)]) (roots2 := face1_Cofactor12086_R_8) (T2 := face1_Cofactor12086_G_8) _ face6_low_0
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice32 : Slice h0R h0G (subcubeFast 1 20) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 42) (qGoal := 0xffccffcccc00cc00ffccffcccc00cc00) (by decide +kernel) sliceInput30Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice33 : Slice h0R h0G (subcubeFast 4 17) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 42) (qGoal := 0xffccffcccc00cc00ffccffcccc00cc00) (by decide +kernel) sliceInput30Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput31Map : Lower (varsOf 41) 0xffaaffaaaa00aa00ffaaffaaaa00aa00 4 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (2, 3), (0, 1)]) (roots2 := face1_Cofactor12086_R_8) (T2 := face1_Cofactor12086_G_8) _ face6_low_0
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice34 : Slice h0R h0G (subcubeFast 4 18) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 41) (qGoal := 0xffaaffaaaa00aa00ffaaffaaaa00aa00) (by decide +kernel) sliceInput31Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput32Map : Lower (varsOf 38) 0xfcfcfcfcc0c0c0c0fcfcfcfcc0c0c0c0 4 := by
  apply carry_of (swaps := [(3, 4), (4, 5)]) (roots2 := face1_Cofactor12086_R_8) (T2 := face1_Cofactor12086_G_8) _ face6_low_0
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice35 : Slice h0R h0G (subcubeFast 1 24) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 38) (qGoal := 0xfcfcfcfcc0c0c0c0fcfcfcfcc0c0c0c0) (by decide +kernel) sliceInput32Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice36 : Slice h0R h0G (subcubeFast 16 9) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 38) (qGoal := 0xfcfcfcfcc0c0c0c0fcfcfcfcc0c0c0c0) (by decide +kernel) sliceInput32Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput33Map : Lower (varsOf 37) 0xfafafafaa0a0a0a0fafafafaa0a0a0a0 4 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (0, 1)]) (roots2 := face1_Cofactor12086_R_8) (T2 := face1_Cofactor12086_G_8) _ face6_low_0
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice37 : Slice h0R h0G (subcubeFast 8 18) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 37) (qGoal := 0xfafafafaa0a0a0a0fafafafaa0a0a0a0) (by decide +kernel) sliceInput33Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput34Map : Lower (varsOf 35) 0xeeeeeeee88888888eeeeeeee88888888 4 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (0, 1), (1, 2)]) (roots2 := face1_Cofactor12086_R_8) (T2 := face1_Cofactor12086_G_8) _ face6_low_0
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice38 : Slice h0R h0G (subcubeFast 4 24) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 35) (qGoal := 0xeeeeeeee88888888eeeeeeee88888888) (by decide +kernel) sliceInput34Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput35Map : Lower (varsOf 28) 0xfff0f000fff0f000fff0f000fff0f000 4 := by
  apply carry_of (swaps := [(3, 4), (2, 3), (1, 2)]) (roots2 := face1_Cofactor12086_R_8) (T2 := face1_Cofactor12086_G_8) _ face6_low_0
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice39 : Slice h0R h0G (subcubeFast 1 34) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 28) (qGoal := 0xfff0f000fff0f000fff0f000fff0f000) (by decide +kernel) sliceInput35Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice40 : Slice h0R h0G (subcubeFast 2 33) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 28) (qGoal := 0xfff0f000fff0f000fff0f000fff0f000) (by decide +kernel) sliceInput35Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput36Map : Lower (varsOf 27) 0xeeaacc88eeaacc88eeaacc88eeaacc88 4 := by
  apply carry_of (swaps := [(1, 2), (2, 3), (3, 4), (4, 5), (1, 2), (2, 3), (0, 1), (1, 2)]) (roots2 := face0_R_21) (T2 := face7_G_15) _ face7_low_15
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice41 : Slice h0R h0G (subcubeFast 32 4) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 27) (qGoal := 0xeeaacc88eeaacc88eeaacc88eeaacc88) (by decide +kernel) sliceInput36Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput37Map : Lower (varsOf 26) 0xffcccc00ffcccc00ffcccc00ffcccc00 4 := by
  apply carry_of (swaps := [(3, 4), (2, 3)]) (roots2 := face1_Cofactor12086_R_8) (T2 := face1_Cofactor12086_G_8) _ face6_low_0
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice42 : Slice h0R h0G (subcubeFast 1 36) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 26) (qGoal := 0xffcccc00ffcccc00ffcccc00ffcccc00) (by decide +kernel) sliceInput37Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput38Map : Lower (varsOf 25) 0xffaaaa00ffaaaa00ffaaaa00ffaaaa00 4 := by
  apply carry_of (swaps := [(3, 4), (2, 3), (0, 1)]) (roots2 := face1_Cofactor12086_R_8) (T2 := face1_Cofactor12086_G_8) _ face6_low_0
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice43 : Slice h0R h0G (subcubeFast 2 36) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 25) (qGoal := 0xffaaaa00ffaaaa00ffaaaa00ffaaaa00) (by decide +kernel) sliceInput38Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput39Map : Lower (varsOf 22) 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0 4 := by
  apply carry_of (swaps := [(3, 4)]) (roots2 := face1_Cofactor12086_R_8) (T2 := face1_Cofactor12086_G_8) _ face6_low_0
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice44 : Slice h0R h0G (subcubeFast 1 40) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 22) (qGoal := 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0) (by decide +kernel) sliceInput39Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice45 : Slice h0R h0G (subcubeFast 32 9) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 22) (qGoal := 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0) (by decide +kernel) sliceInput39Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput40Map : Lower (varsOf 21) 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0 4 := by
  apply carry_of (swaps := [(3, 4), (0, 1)]) (roots2 := face1_Cofactor12086_R_8) (T2 := face1_Cofactor12086_G_8) _ face6_low_0
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice46 : Slice h0R h0G (subcubeFast 2 40) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 21) (qGoal := 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0) (by decide +kernel) sliceInput40Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput41Map : Lower (varsOf 19) 0xeeee8888eeee8888eeee8888eeee8888 4 := by
  apply carry_of (swaps := [(3, 4), (0, 1), (1, 2)]) (roots2 := face1_Cofactor12086_R_8) (T2 := face1_Cofactor12086_G_8) _ face6_low_0
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice47 : Slice h0R h0G (subcubeFast 4 40) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 19) (qGoal := 0xeeee8888eeee8888eeee8888eeee8888) (by decide +kernel) sliceInput41Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice48 : Slice h0R h0G (subcubeFast 8 36) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 19) (qGoal := 0xeeee8888eeee8888eeee8888eeee8888) (by decide +kernel) sliceInput41Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput42Map : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0 4 := by
  apply carry_of (swaps := []) (roots2 := face1_Cofactor12086_R_8) (T2 := face1_Cofactor12086_G_8) _ face6_low_0
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice49 : Slice h0R h0G (subcubeFast 1 48) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 14) (qGoal := 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0) (by decide +kernel) sliceInput42Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput43Map : Lower (varsOf 13) 0xfaa0faa0faa0faa0faa0faa0faa0faa0 4 := by
  apply carry_of (swaps := [(0, 1)]) (roots2 := face1_Cofactor12086_R_8) (T2 := face1_Cofactor12086_G_8) _ face6_low_0
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice50 : Slice h0R h0G (subcubeFast 2 48) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 13) (qGoal := 0xfaa0faa0faa0faa0faa0faa0faa0faa0) (by decide +kernel) sliceInput43Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice51 : Slice h0R h0G (subcubeFast 32 18) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 13) (qGoal := 0xfaa0faa0faa0faa0faa0faa0faa0faa0) (by decide +kernel) sliceInput43Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput44Map : Lower (varsOf 11) 0xee88ee88ee88ee88ee88ee88ee88ee88 4 := by
  apply carry_of (swaps := [(0, 1), (1, 2)]) (roots2 := face1_Cofactor12086_R_8) (T2 := face1_Cofactor12086_G_8) _ face6_low_0
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice52 : Slice h0R h0G (subcubeFast 4 48) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 11) (qGoal := 0xee88ee88ee88ee88ee88ee88ee88ee88) (by decide +kernel) sliceInput44Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice53 : Slice h0R h0G (subcubeFast 16 36) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 11) (qGoal := 0xee88ee88ee88ee88ee88ee88ee88ee88) (by decide +kernel) sliceInput44Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sliceInput45Map : Lower (varsOf 7) 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8 4 := by
  apply carry_of (swaps := [(0, 1), (1, 2), (2, 3)]) (roots2 := face1_Cofactor12086_R_8) (T2 := face1_Cofactor12086_G_8) _ face6_low_0
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice54 : Slice h0R h0G (subcubeFast 8 48) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 7) (qGoal := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8) (by decide +kernel) sliceInput45Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice55 : Slice h0R h0G (subcubeFast 16 40) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 7) (qGoal := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8) (by decide +kernel) sliceInput45Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice56 : Slice h0R h0G (subcubeFast 32 24) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 7) (qGoal := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8) (by decide +kernel) sliceInput45Map
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h0R h0G p.1 p.2) h0Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h0R h0G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h0Slice0) (forall_cons (fun _ h => by cases h; exact h0Slice1) (forall_cons (fun _ h => by cases h; exact h0Slice2) (forall_cons (fun _ h => by cases h; exact h0Slice3) (forall_cons (fun _ h => by cases h; exact h0Slice4) (forall_cons (fun _ h => by cases h; exact h0Slice5) (forall_cons (fun _ h => by cases h; exact h0Slice6) (forall_cons (fun _ h => by cases h; exact h0Slice7) (forall_cons (fun _ h => by cases h; exact h0Slice8) (forall_cons (fun _ h => by cases h; exact h0Slice9) (forall_cons (fun _ h => by cases h; exact h0Slice10) (forall_cons (fun _ h => by cases h; exact h0Slice11) (forall_cons (fun _ h => by cases h; exact h0Slice12) (forall_cons (fun _ h => by cases h; exact h0Slice13) (forall_cons (fun _ h => by cases h; exact h0Slice14) (forall_cons (fun _ h => by cases h; exact h0Slice15) (forall_cons (fun _ h => by cases h; exact h0Slice16) (forall_cons (fun _ h => by cases h; exact h0Slice17) (forall_cons (fun _ h => by cases h; exact h0Slice18) (forall_cons (fun _ h => by cases h; exact h0Slice19) (forall_cons (fun _ h => by cases h; exact h0Slice20) (forall_cons (fun _ h => by cases h; exact h0Slice21) (forall_cons (fun _ h => by cases h; exact h0Slice22) (forall_cons (fun _ h => by cases h; exact h0Slice23) (forall_cons (fun _ h => by cases h; exact h0Slice24) (forall_cons (fun _ h => by cases h; exact h0Slice25) (forall_cons (fun _ h => by cases h; exact h0Slice26) (forall_cons (fun _ h => by cases h; exact h0Slice27) (forall_cons (fun _ h => by cases h; exact h0Slice28) (forall_cons (fun _ h => by cases h; exact h0Slice29) (forall_cons (fun _ h => by cases h; exact h0Slice30) (forall_cons (fun _ h => by cases h; exact h0Slice31) (forall_cons (fun _ h => by cases h; exact h0Slice32) (forall_cons (fun _ h => by cases h; exact h0Slice33) (forall_cons (fun _ h => by cases h; exact h0Slice34) (forall_cons (fun _ h => by cases h; exact h0Slice35) (forall_cons (fun _ h => by cases h; exact h0Slice36) (forall_cons (fun _ h => by cases h; exact h0Slice37) (forall_cons (fun _ h => by cases h; exact h0Slice38) (forall_cons (fun _ h => by cases h; exact h0Slice39) (forall_cons (fun _ h => by cases h; exact h0Slice40) (forall_cons (fun _ h => by cases h; exact h0Slice41) (forall_cons (fun _ h => by cases h; exact h0Slice42) (forall_cons (fun _ h => by cases h; exact h0Slice43) (forall_cons (fun _ h => by cases h; exact h0Slice44) (forall_cons (fun _ h => by cases h; exact h0Slice45) (forall_cons (fun _ h => by cases h; exact h0Slice46) (forall_cons (fun _ h => by cases h; exact h0Slice47) (forall_cons (fun _ h => by cases h; exact h0Slice48) (forall_cons (fun _ h => by cases h; exact h0Slice49) (forall_cons (fun _ h => by cases h; exact h0Slice50) (forall_cons (fun _ h => by cases h; exact h0Slice51) (forall_cons (fun _ h => by cases h; exact h0Slice52) (forall_cons (fun _ h => by cases h; exact h0Slice53) (forall_cons (fun _ h => by cases h; exact h0Slice54) (forall_cons (fun _ h => by cases h; exact h0Slice55) (forall_cons (fun _ h => by cases h; exact h0Slice56) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def h0Empty : BT (List (List Nat)) := BT.empty
lemma h0EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G (5 - 1) xs.toFinset) h0Empty := trivial
def h0Block5_0Specs : List PoolSpec := []
def h0Block5_0Pools : BT (Option BoundPool) := buildPoolsBT 1 h0W h0R h0Slices h0Block5_0Specs
def h0Block5_0 : List NodeSpec := [([77,0,1,3,4,5],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block5_0Ok : checkNodesBT h0W h0G h0Mask h0Block5_0Pools h0Autos h0Empty 5 h0Block5_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block5_0Mem : ∀ ns ∈ h0Block5_0, Impossible h0G 5 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0EmptyOk h0Block5_0Ok
def h0Nodes5 : List NodeSpec := h0Block5_0
def h0Bucket5 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 5 xs.toFinset) h0Bucket5 := buildBucketsBT_of_mem h0Block5_0Mem
def h0Block6_0Specs : List PoolSpec := []
def h0Block6_0Pools : BT (Option BoundPool) := buildPoolsBT 1 h0W h0R h0Slices h0Block6_0Specs
def h0Block6_0 : List NodeSpec := [([78,79,0,1,3,4,5],[],[0]),([44,0,1,2,39,22,5],[],[]),([0,1,75,3,76,4,5],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block6_0Ok : checkNodesBT h0W h0G h0Mask h0Block6_0Pools h0Autos h0Bucket5 6 h0Block6_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block6_0Mem : ∀ ns ∈ h0Block6_0, Impossible h0G 6 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket5Ok h0Block6_0Ok
def h0Nodes6 : List NodeSpec := h0Block6_0
def h0Bucket6 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 6 xs.toFinset) h0Bucket6 := buildBucketsBT_of_mem h0Block6_0Mem
def h0Block7_0Specs : List PoolSpec := [(7,[]),(20,[]),(10,[]),(21,[]),(37,[]),(5,[]),(15,[(0,2,3),(0,36,4)]),(42,[]),(25,[]),(15,[(0,2,3),(0,39,4)]),(11,[(0,2,3),(0,39,5)]),(35,[]),(23,[]),(45,[]),(9,[(0,22,5)]),(9,[(0,22,5),(1,2,70)])]
def h0Block7_0Pools : BT (Option BoundPool) := buildPoolsBT 4 h0W h0R h0Slices h0Block7_0Specs
def h0Block7_0 : List NodeSpec := [([45,0,1,2,39,3,4,5],[1],[]),([78,0,1,2,3,71,4,5],[0,5],[0]),([74,0,1,2,3,71,4,5],[0,8],[]),([44,0,1,2,39,3,4,5],[3,4,10],[0]),([48,0,1,2,46,3,4,5],[1,6],[]),([43,0,1,2,39,3,4,5],[1,9],[]),([138,0,1,219,2,4,5],[2,3],[]),([79,0,1,2,3,71,4,5],[0,5],[0]),([8,0,1,70,3,73,4,5],[0,1],[]),([80,0,1,2,70,3,4,5],[0,15],[]),([0,1,281,2,3,4,5],[4,7],[]),([0,1,75,2,3,71,4,5],[0,4,5,11,12,13,14],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block7_0Ok : checkNodesBT h0W h0G h0Mask h0Block7_0Pools h0Autos h0Bucket6 7 h0Block7_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block7_0Mem : ∀ ns ∈ h0Block7_0, Impossible h0G 7 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket6Ok h0Block7_0Ok
def h0Block7_1Specs : List PoolSpec := [(9,[]),(7,[]),(2,[]),(20,[]),(21,[]),(37,[]),(32,[]),(10,[(0,0,1)]),(29,[]),(54,[]),(5,[]),(15,[(0,2,3),(0,36,4)]),(15,[(0,2,3),(0,39,4)]),(44,[]),(35,[]),(23,[]),(51,[]),(36,[]),(38,[]),(9,[(0,22,5),(1,2,70)])]
def h0Block7_1Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block7_1Specs
def h0Block7_1 : List NodeSpec := [([0,1,2,42,39,3,4,5],[0,5,6,7,9],[]),([0,1,2,41,40,3,4,5],[3,4,6,12],[]),([0,1,2,47,46,3,4,5],[3,5,7,8,11,15],[]),([0,1,2,40,39,22,4,5],[5,6,7],[0]),([0,1,2,40,39,3,27,4],[2,8],[]),([0,1,2,70,3,72,4,5],[1],[]),([0,1,2,3,71,73,4,5],[5,10,14,15,18,19],[]),([0,1,2,3,71,76,4,5],[1,5,10,13,14,15],[0]),([0,1,2,3,118,4,5],[16,17],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block7_1Ok : checkNodesBT h0W h0G h0Mask h0Block7_1Pools h0Autos h0Bucket6 7 h0Block7_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block7_1Mem : ∀ ns ∈ h0Block7_1, Impossible h0G 7 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket6Ok h0Block7_1Ok
def h0Nodes7 : List NodeSpec := h0Block7_0 ++ h0Block7_1
def h0Bucket7 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 7 xs.toFinset) h0Bucket7 := buildBucketsBT_of_mem (forall_append h0Block7_0Mem h0Block7_1Mem)
def h0Block8_0Specs : List PoolSpec := [(7,[]),(20,[]),(48,[]),(37,[]),(29,[]),(5,[]),(25,[]),(44,[]),(35,[]),(23,[]),(51,[]),(36,[]),(10,[(0,0,1),(0,22,5)]),(9,[(0,22,5),(2,2,70)]),(34,[]),(28,[]),(15,[(0,3,4),(2,1,70)]),(10,[(0,22,5),(2,0,70)])]
def h0Block8_0Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block8_0Specs
def h0Block8_0 : List NodeSpec := [([306,307,0,1,2,3,4,5],[6,11,16,17],[]),([279,0,226,2,3,4,5],[3,7],[]),([119,0,1,2,3,4,5],[0,5,10,11],[]),([85,0,1,92,2,4,5],[2,14],[]),([85,0,1,96,2,3,4],[1,14,15],[]),([65,0,1,92,2,4,5],[2,14],[]),([65,0,1,7,3,4,5],[2,8],[]),([74,6,0,1,2,70,3,4,5],[4,6,9,12,13],[0]),([87,0,1,92,2,4,5],[10,11],[]),([87,0,1,96,2,3,4],[10,11],[]),([81,0,1,92,2,4,5],[2,10],[]),([113,0,1,2,3,4,5],[3,15],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_0Ok : checkNodesBT h0W h0G h0Mask h0Block8_0Pools h0Autos h0Bucket7 8 h0Block8_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_0Mem : ∀ ns ∈ h0Block8_0, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_0Ok
def h0Block8_1Specs : List PoolSpec := [(2,[]),(20,[]),(10,[]),(48,[]),(37,[]),(15,[(3,2,3)]),(29,[]),(56,[]),(42,[]),(45,[]),(51,[]),(36,[]),(34,[]),(30,[]),(39,[]),(28,[]),(33,[]),(41,[]),(9,[(0,0,4)])]
def h0Block8_1Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block8_1Specs
def h0Block8_1 : List NodeSpec := [([110,38,0,1,3,4,5],[6,16],[]),([110,0,1,37,3,4,5],[9,12,15],[]),([110,0,1,36,22,4,5],[3,16],[]),([116,0,1,2,3,4,5],[4,6,7],[]),([108,0,1,2,22,4,5],[4,16],[]),([108,0,1,2,3,27,4,5],[6,9,11,12],[]),([111,0,1,2,3,4,5],[10,15],[]),([109,0,1,2,3,4,5],[0,1,12,15],[]),([19,231,0,184,1,2,4,5],[3,4,5,14],[]),([19,0,1,277,2,3,4,5],[4,8,13],[]),([19,0,1,270,2,3,4,5],[2,8,16,18],[]),([19,0,1,96,2,3,27,4],[4,11,15,17],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_1Ok : checkNodesBT h0W h0G h0Mask h0Block8_1Pools h0Autos h0Bucket7 8 h0Block8_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_1Mem : ∀ ns ∈ h0Block8_1, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_1Ok
def h0Block8_2Specs : List PoolSpec := [(20,[]),(13,[]),(48,[]),(37,[]),(32,[]),(9,[(0,2,4),(3,18,5)]),(29,[]),(56,[]),(15,[(0,2,3),(3,36,4)]),(42,[]),(43,[]),(44,[]),(35,[]),(23,[]),(45,[]),(36,[]),(34,[]),(30,[]),(28,[]),(50,[]),(5,[(3,0,3),(3,1,4),(1,191,197)])]
def h0Block8_2Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block8_2Specs
def h0Block8_2 : List NodeSpec := [([58,0,1,96,2,3,4],[3,18],[]),([138,0,1,137,2,3,4,5],[4,17],[]),([23,0,1,219,2,3,4,5],[1,2,6,12],[]),([23,0,1,137,2,83,3,4],[3,9],[]),([25,215,0,1,2,3,4,5],[11,13,19,20],[]),([21,15,0,1,2,3,4,5],[2,4,5],[]),([21,198,0,1,2,3,4,5],[3,10,14,19],[]),([21,0,1,126,2,3,4,5],[2,4,17],[]),([38,34,0,1,2,3,4,5],[6,7,8],[]),([38,0,1,137,2,3,4,5],[0,3,8,16],[]),([38,0,1,92,2,4,5],[15,16],[]),([38,0,1,96,2,3,4,5],[15,16],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_2Ok : checkNodesBT h0W h0G h0Mask h0Block8_2Pools h0Autos h0Bucket7 8 h0Block8_2 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_2Mem : ∀ ns ∈ h0Block8_2, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_2Ok
def h0Block8_3Specs : List PoolSpec := [(48,[]),(37,[]),(32,[]),(29,[]),(56,[]),(13,[(0,0,1)]),(44,[]),(35,[]),(45,[]),(16,[(0,2,3),(0,36,4)]),(51,[]),(47,[]),(36,[]),(34,[]),(28,[]),(27,[]),(40,[])]
def h0Block8_3Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block8_3Specs
def h0Block8_3 : List NodeSpec := [([52,225,0,1,2,83,3,4],[1,3,6,11],[]),([52,0,1,92,2,4,5],[0,10],[]),([49,6,0,1,2,22,3,4,5],[0,4,7,12],[]),([49,6,0,1,2,3,4,5],[0,5,8,9],[]),([103,0,1,18,2,3,4,5],[1,4,14],[]),([123,0,1,26,2,22,3,5],[2,10,12],[]),([123,1,2,141,3,27,4,5],[12,13,15],[]),([163,0,1,2,3,4,5],[13,15],[]),([165,0,1,2,3,4,5],[1,16],[]),([160,0,1,2,3,4,5],[13,15],[]),([157,0,1,2,3,4,5],[13,15],[]),([161,0,1,2,3,4,5],[6,10,15],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_3Ok : checkNodesBT h0W h0G h0Mask h0Block8_3Pools h0Autos h0Bucket7 8 h0Block8_3 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_3Mem : ∀ ns ∈ h0Block8_3, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_3Ok
def h0Block8_4Specs : List PoolSpec := [(10,[]),(13,[]),(48,[]),(37,[]),(24,[]),(32,[]),(29,[]),(42,[]),(43,[]),(25,[]),(51,[]),(47,[]),(38,[]),(12,[]),(30,[]),(39,[]),(33,[]),(27,[]),(10,[(0,1,5)]),(3,[(0,1,5),(3,184,3),(0,2,4)]),(9,[(0,0,4),(3,225,2)]),(9,[(0,0,4),(1,225,2)]),(6,[(0,1,3),(3,240,2)]),(15,[(0,1,3),(3,240,227)]),(0,[(0,0,4),(1,225,2),(3,240,227)]),(13,[(0,1,3),(3,240,227)]),(8,[(1,225,2),(3,240,227)]),(13,[(0,1,5),(3,184,3)]),(11,[(0,1,3),(3,240,227)])]
def h0Block8_4Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block8_4Specs
def h0Block8_4 : List NodeSpec := [([159,0,1,2,3,4,5],[10,17],[]),([146,0,1,2,3,27,4,5],[3,7,12],[]),([152,0,1,2,83,3,4,5],[1,3,7],[]),([153,0,1,2,22,3,4,5],[5,11,17],[]),([149,0,1,2,3,4,5],[5,17],[]),([144,0,1,2,3,4,5],[10,17],[]),([241,225,0,240,1,227,3,4,5],[0,3,4,16,21,22],[]),([242,225,0,240,1,2,3,4,5],[4,13,14,21],[]),([242,225,0,1,2,3,4,5],[6,9,14,23,24,25,26],[]),([242,0,1,2,3,4,5],[8,14,28],[]),([220,229,0,1,2,3,4,5],[15,20,27],[]),([220,197,0,1,18,2,4,5],[2,3,5,18,19],[1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_4Ok : checkNodesBT h0W h0G h0Mask h0Block8_4Pools h0Autos h0Bucket7 8 h0Block8_4 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_4Mem : ∀ ns ∈ h0Block8_4, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_4Ok
def h0Block8_5Specs : List PoolSpec := [(15,[]),(9,[]),(37,[]),(32,[]),(22,[]),(29,[]),(8,[]),(42,[]),(25,[]),(44,[]),(35,[]),(51,[]),(53,[]),(47,[]),(18,[]),(34,[]),(30,[]),(39,[]),(28,[]),(33,[]),(3,[(0,1,5),(3,203,2)]),(3,[(0,1,5),(0,2,4),(1,184,18)]),(31,[]),(9,[(0,0,4),(3,225,2)]),(10,[(0,0,4),(3,225,1)]),(16,[(0,0,4),(3,225,2)]),(1,[(3,225,2),(0,1,5),(0,184,3)]),(15,[(0,184,3)]),(1,[(3,225,2),(0,1,5),(0,3,5)]),(15,[(0,231,2)]),(9,[(0,0,4),(0,231,2)])]
def h0Block8_5Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block8_5Specs
def h0Block8_5 : List NodeSpec := [([266,225,0,1,2,83,3,4],[5,9,11,14,16],[]),([194,171,0,1,2,3,4,5],[3,6,13,17],[]),([235,0,239,1,2,3,4,5],[3,7,24],[]),([257,0,184,1,2,3,4,5],[2,13,17,29,30],[]),([208,0,184,1,2,3,4,5],[2,12,20],[]),([229,232,0,1,2,3,4,5],[8,10,19,25],[]),([229,0,238,1,2,3,4,5],[17,22,23],[]),([229,0,249,1,2,3,4,5],[8,16,25,26,27],[]),([229,0,184,1,2,83,3,4],[0,13,23,28],[]),([229,0,1,268,2,3,4,5],[1,15,16,17],[]),([197,0,1,2,223,3,4,5],[3,4,10,17,21],[]),([231,0,1,2,252,3,5],[9,18],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_5Ok : checkNodesBT h0W h0G h0Mask h0Block8_5Pools h0Autos h0Bucket7 8 h0Block8_5 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_5Mem : ∀ ns ∈ h0Block8_5, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_5Ok
def h0Block8_6Specs : List PoolSpec := [(15,[]),(20,[]),(48,[]),(37,[]),(15,[(0,2,4)]),(10,[(0,0,1),(0,15,5)]),(24,[]),(32,[]),(10,[(0,0,1)]),(9,[(0,2,4)]),(29,[]),(56,[]),(15,[(0,2,3),(0,36,4)]),(9,[(0,36,4)]),(7,[(0,0,1),(3,6,5)]),(15,[(0,2,3),(0,3,4)]),(13,[(0,0,1),(3,6,5)]),(43,[]),(44,[]),(35,[]),(23,[]),(49,[]),(47,[]),(36,[]),(15,[(3,25,3),(0,62,4)]),(11,[(0,22,5)]),(9,[(0,22,5)]),(52,[]),(50,[]),(3,[(0,2,4),(3,198,5)])]
def h0Block8_6Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block8_6Specs
def h0Block8_6 : List NodeSpec := [([224,0,184,1,2,3,4,5],[7,10,20,27],[]),([8,0,1,2,70,3,4,5],[1,10,19,21,22,25,26],[0]),([17,0,1,18,2,3,4,5],[3,4,5,6],[]),([15,0,1,18,2,22,5],[2,8,9],[]),([15,0,1,26,2,3,4,5],[2,7,10],[]),([15,0,1,2,20,4,5],[0,3,7],[]),([222,0,1,2,3,4,5],[18,20,28],[]),([201,0,1,18,2,3,4,5],[3,17,29],[]),([34,0,1,37,2,3,4,5],[11,12,13,14],[]),([34,0,1,36,2,22,4,5],[11,15,16],[]),([34,0,1,2,20,3,4,5],[7,11,17],[]),([6,0,1,64,2,3,4,5],[3,10,11,23,24],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_6Ok : checkNodesBT h0W h0G h0Mask h0Block8_6Pools h0Autos h0Bucket7 8 h0Block8_6 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_6Mem : ∀ ns ∈ h0Block8_6, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_6Ok
def h0Block8_7Specs : List PoolSpec := [(48,[]),(37,[]),(32,[]),(10,[(0,0,1)]),(29,[]),(8,[]),(56,[]),(25,[]),(13,[(0,0,1)]),(44,[]),(35,[]),(23,[]),(45,[]),(51,[]),(53,[]),(47,[]),(36,[]),(9,[(0,22,5),(1,2,70)]),(18,[]),(46,[]),(30,[]),(33,[])]
def h0Block8_7Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block8_7Specs
def h0Block8_7 : List NodeSpec := [([6,0,1,54,2,3,4,5],[4,11,13],[]),([6,0,1,62,2,22,4,5],[1,4,6,12,14],[]),([6,0,1,62,2,83,4,5],[1,4,18,19],[]),([6,0,1,2,67,22,3,4,5],[0,6,10,16],[]),([6,0,1,2,70,3,73,4,5],[1,3,7,10,11,17],[0]),([6,0,1,2,3,69,4,5],[3,10,13,15],[]),([232,0,226,2,3,4,5],[16,21],[]),([86,0,1,2,3,4,5],[5,8,9],[]),([68,0,1,2,3,4,5],[0,10],[]),([88,0,1,2,3,4,5],[1,9],[]),([82,0,1,2,3,4,5],[0,10],[]),([230,0,226,2,3,4,5],[2,20],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_7Ok : checkNodesBT h0W h0G h0Mask h0Block8_7Pools h0Autos h0Bucket7 8 h0Block8_7 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_7Mem : ∀ ns ∈ h0Block8_7, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_7Ok
def h0Block8_8Specs : List PoolSpec := [(9,[]),(20,[]),(48,[]),(37,[]),(24,[]),(32,[]),(22,[]),(29,[]),(54,[]),(42,[]),(43,[]),(25,[]),(44,[]),(53,[]),(47,[]),(9,[(3,2,5)]),(36,[]),(34,[]),(30,[]),(39,[]),(33,[]),(27,[]),(55,[]),(6,[(0,226,3),(1,233,2)]),(9,[(0,0,4),(3,225,2)]),(6,[(0,1,3),(0,227,3)]),(5,[(0,0,4),(0,1,3)]),(13,[(0,1,3)]),(15,[(3,231,2)])]
def h0Block8_8Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block8_8Specs
def h0Block8_8 : List NodeSpec := [([57,0,1,2,3,27,4,5],[5,10,14],[]),([61,0,1,2,22,3,4,5],[5,6,14,15],[]),([53,0,1,2,3,4,5],[7,8],[]),([212,0,184,1,2,3,4,5],[0,1,12,17,19],[]),([253,0,184,1,2,3,4,5],[1,2,18,22,28],[]),([225,0,240,1,244,2,3,4,5],[18,21,24,27],[]),([225,0,240,1,2,207,4,5],[3,8,20,25,26],[]),([225,0,1,233,2,234,3,4,5],[4,16,20,23],[]),([225,0,1,62,2,83,4,5],[3,13],[]),([0,284,1,2,3,4,5],[12,20],[]),([0,203,1,2,207,4,5],[8,11,20],[]),([0,239,184,1,2,3,4,5],[3,9,18],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_8Ok : checkNodesBT h0W h0G h0Mask h0Block8_8Pools h0Autos h0Bucket7 8 h0Block8_8 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_8Mem : ∀ ns ∈ h0Block8_8, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_8Ok
def h0Block8_9Specs : List PoolSpec := [(11,[]),(0,[]),(48,[]),(37,[]),(15,[(0,2,4)]),(24,[]),(32,[]),(22,[]),(29,[]),(42,[]),(43,[]),(25,[]),(51,[]),(53,[]),(47,[]),(36,[]),(11,[(0,22,5)]),(11,[(0,3,5)]),(30,[]),(39,[]),(28,[]),(33,[]),(50,[]),(16,[(0,0,4)]),(10,[(0,0,4)]),(9,[(0,0,4),(1,225,2)]),(5,[(0,0,4),(0,1,3),(1,225,240)])]
def h0Block8_9Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block8_9Specs
def h0Block8_9 : List NodeSpec := [([0,272,184,1,2,3,4,5],[9,13,18],[]),([0,213,1,2,3,4,5],[11,14,21],[]),([0,175,1,18,2,3,4,5],[3,10,20],[]),([0,217,1,2,3,4,5],[20,22],[]),([0,193,1,2,3,4,5],[15,22],[]),([0,228,226,2,3,4,5],[21,23],[]),([0,240,1,237,2,227,3,4,5],[0,3,18,21,24,25,26],[]),([0,1,265,2,3,4,5],[8,21],[]),([0,1,124,2,70,3,4,5],[3,6,14,16],[]),([0,1,248,2,3,4,5],[1,6,7,19],[]),([0,1,132,18,2,3,4,5],[4,5,12,18],[]),([0,1,126,18,2,83,4,5],[2,6,17,18],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_9Ok : checkNodesBT h0W h0G h0Mask h0Block8_9Pools h0Autos h0Bucket7 8 h0Block8_9 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_9Mem : ∀ ns ∈ h0Block8_9, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_9Ok
def h0Block8_10Specs : List PoolSpec := [(11,[]),(7,[]),(48,[]),(24,[]),(32,[]),(9,[(0,2,4)]),(29,[]),(5,[]),(56,[]),(15,[(0,2,3),(0,36,4)]),(42,[]),(11,[(0,2,3)]),(44,[]),(35,[]),(45,[]),(51,[]),(47,[]),(36,[]),(11,[(0,3,5)]),(34,[]),(30,[]),(39,[]),(27,[]),(10,[(0,1,5),(1,197,184)]),(2,[(3,0,3),(1,197,184),(0,2,4)])]
def h0Block8_10Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block8_10Specs
def h0Block8_10 : List NodeSpec := [([0,1,126,26,2,3,4,5],[2,4,17],[]),([0,1,219,18,2,3,4,5],[3,5,13,23,24],[0]),([0,1,256,2,3,4,5],[1,7,13,21],[]),([0,1,136,36,2,3,4,5],[6,14,19,22],[]),([0,1,137,37,2,3,4,5],[8,9,20],[]),([0,1,137,36,2,22,4,5],[8,11,19],[]),([0,1,137,139,2,3,4,5],[8,10,19],[]),([0,1,137,18,2,22,3,5],[0,8,20],[]),([0,1,137,18,2,83,3,4],[4,15,18,20],[]),([0,1,137,2,20,3,4,5],[4,20],[]),([0,1,134,2,3,4,5],[12,13,20],[]),([0,1,112,2,3,4,5],[15,16],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_10Ok : checkNodesBT h0W h0G h0Mask h0Block8_10Pools h0Autos h0Bucket7 8 h0Block8_10 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_10Mem : ∀ ns ∈ h0Block8_10, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_10Ok
def h0Block8_11Specs : List PoolSpec := [(7,[]),(48,[]),(37,[]),(24,[]),(22,[]),(54,[]),(23,[]),(45,[]),(51,[]),(53,[]),(47,[]),(36,[]),(38,[]),(30,[]),(39,[]),(28,[]),(33,[]),(8,[(3,2,5)]),(27,[]),(16,[(0,0,4)])]
def h0Block8_11Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block8_11Specs
def h0Block8_11 : List NodeSpec := [([0,1,90,2,70,3,4,5],[2,10,11],[0]),([0,1,115,2,22,3,4,5],[4,8,10,17],[]),([0,1,114,2,3,27,4,5],[2,11,12],[]),([0,1,276,2,3,4,5],[2,16,19],[]),([0,1,120,2,3,4,5],[1,5,7],[]),([0,1,271,270,2,3,4,5],[14,16,18],[]),([0,1,94,18,2,3,4,5],[0,3,8,11],[]),([0,1,92,18,2,22,5],[1,11],[]),([0,1,92,18,2,83,4,5],[8,11,13],[]),([0,1,122,2,3,4,5],[2,5,6],[]),([0,1,117,2,3,4,5],[9,15],[]),([0,1,121,2,3,4,5],[1,16],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_11Ok : checkNodesBT h0W h0G h0Mask h0Block8_11Pools h0Autos h0Bucket7 8 h0Block8_11 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_11Mem : ∀ ns ∈ h0Block8_11, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_11Ok
def h0Block8_12Specs : List PoolSpec := [(20,[]),(10,[]),(17,[]),(37,[]),(32,[]),(8,[]),(56,[]),(42,[]),(44,[]),(45,[]),(34,[]),(30,[]),(26,[]),(28,[]),(33,[]),(16,[(0,0,4)]),(15,[(0,1,3)]),(11,[(0,1,3)])]
def h0Block8_12Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block8_12Specs
def h0Block8_12 : List NodeSpec := [([0,1,263,237,2,3,4,5],[11,14,15],[]),([0,1,282,2,83,3,4,5],[1,2,3,8],[]),([0,1,260,2,3,4,5],[11,16,17],[]),([0,1,237,2,3,4,5],[11,14,15],[]),([0,1,274,2,3,4,5],[0,11,14],[]),([0,1,226,2,3,280,4,5],[4,7,11],[0]),([0,1,96,101,2,3,4,5],[3,13],[]),([0,1,96,37,2,3,4,5],[6,10,12,13],[]),([0,1,96,36,2,106,3,4,5],[9,13],[]),([0,1,96,36,2,22,4,5],[5,6,10],[]),([0,1,96,36,2,3,27,4],[9,10,14],[]),([0,1,96,2,20,3,4,5],[3,13],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_12Ok : checkNodesBT h0W h0G h0Mask h0Block8_12Pools h0Autos h0Bucket7 8 h0Block8_12 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_12Mem : ∀ ns ∈ h0Block8_12, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_12Ok
def h0Block8_13Specs : List PoolSpec := [(37,[]),(24,[]),(22,[]),(29,[]),(42,[]),(13,[(0,0,1),(0,39,5)]),(45,[]),(34,[]),(30,[]),(26,[]),(39,[]),(33,[]),(27,[]),(40,[])]
def h0Block8_13Pools : BT (Option BoundPool) := buildPoolsBT 4 h0W h0R h0Slices h0Block8_13Specs
def h0Block8_13 : List NodeSpec := [([0,1,96,2,98,3,4,5],[0,6,9],[]),([0,1,211,2,3,4,5],[2,10,11],[]),([0,1,269,2,3,4,5],[2,10,11],[]),([0,1,36,2,40,3,4,5],[3,4,5],[]),([0,1,2,142,3,4,5],[7,12],[]),([0,1,2,143,3,4,5],[7,12],[]),([0,1,2,140,3,27,4,5],[0,7,13],[]),([0,1,2,154,3,4,5],[0,13],[]),([0,1,2,150,3,4,5],[7,12],[]),([0,1,2,148,3,4,5],[7,12],[]),([0,1,2,147,83,3,4,5],[0,8,13],[]),([0,1,2,155,3,4,5],[1,12,13],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_13Ok : checkNodesBT h0W h0G h0Mask h0Block8_13Pools h0Autos h0Bucket7 8 h0Block8_13 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_13Mem : ∀ ns ∈ h0Block8_13, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_13Ok
def h0Block8_14Specs : List PoolSpec := [(9,[]),(2,[]),(20,[]),(37,[]),(24,[]),(32,[]),(10,[(0,0,1)]),(29,[]),(54,[]),(56,[]),(15,[(0,2,3),(0,36,4)]),(9,[(0,36,4)]),(15,[(0,2,3),(0,3,4)]),(15,[(0,2,3)]),(42,[]),(13,[(0,0,1)]),(15,[(0,2,3),(0,39,4)]),(11,[(0,2,3)]),(44,[]),(35,[]),(16,[(0,2,3)]),(23,[]),(45,[]),(9,[(0,36,5)]),(46,[]),(30,[]),(28,[]),(27,[])]
def h0Block8_14Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block8_14Specs
def h0Block8_14 : List NodeSpec := [([0,1,2,145,3,4,5],[4,25,27],[]),([0,1,2,174,3,4,5],[3,26],[]),([0,1,2,41,39,3,4,5],[7,16,17],[0]),([0,1,2,46,22,3,4,5],[2,3,18,19,21],[]),([0,1,2,46,3,4,5],[2,6,10,11,17],[0]),([0,1,2,40,39,3,4,5],[7,9,13,14,15,18],[0]),([0,1,2,51,83,3,4,5],[3,24],[]),([0,1,2,51,3,4,5],[13,15,23],[]),([0,1,2,39,22,4,5],[0,3,7,12,15,17,19],[0]),([0,1,2,39,3,27,4,5],[3,7,8,9,15,17,20],[0]),([0,1,2,63,3,4,5],[7,9,22],[]),([0,1,2,200,3,4,5],[1,2,3,5],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_14Ok : checkNodesBT h0W h0G h0Mask h0Block8_14Pools h0Autos h0Bucket7 8 h0Block8_14 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_14Mem : ∀ ns ∈ h0Block8_14, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_14Ok
def h0Block8_15Specs : List PoolSpec := [(7,[]),(10,[]),(21,[]),(17,[]),(37,[]),(24,[]),(32,[]),(29,[]),(54,[]),(5,[]),(25,[]),(15,[(0,3,4)]),(44,[]),(35,[]),(23,[]),(51,[]),(49,[]),(36,[]),(38,[]),(11,[(0,22,5)]),(9,[(0,22,5)]),(16,[(0,3,4)]),(46,[]),(12,[]),(30,[]),(26,[]),(28,[]),(27,[])]
def h0Block8_15Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block8_15Specs
def h0Block8_15 : List NodeSpec := [([0,1,2,55,3,4,5],[4,6,8],[]),([0,1,2,285,83,3,4,5],[4,12],[]),([0,1,2,133,3,4,5],[6,12,24],[]),([0,1,2,106,3,4,5],[2,7,23,25],[]),([0,1,2,70,3,71,4,5],[10,12,13,16,17,18,21],[0]),([0,1,2,22,3,71,4,5],[1,4,5,13,14],[]),([0,1,2,83,3,71,4,5],[1,3,4,22],[]),([0,1,2,3,158,4,5],[15,27],[]),([0,1,2,3,71,4,5],[0,9,11,19,20],[0]),([0,1,2,3,304,305,4,5],[10,15,17,19,20,24,26],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_15Ok : checkNodesBT h0W h0G h0Mask h0Block8_15Pools h0Autos h0Bucket7 8 h0Block8_15 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block8_15Mem : ∀ ns ∈ h0Block8_15, Impossible h0G 8 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket7Ok h0Block8_15Ok
def h0Nodes8 : List NodeSpec := h0Block8_0 ++ h0Block8_1 ++ h0Block8_2 ++ h0Block8_3 ++ h0Block8_4 ++ h0Block8_5 ++ h0Block8_6 ++ h0Block8_7 ++ h0Block8_8 ++ h0Block8_9 ++ h0Block8_10 ++ h0Block8_11 ++ h0Block8_12 ++ h0Block8_13 ++ h0Block8_14 ++ h0Block8_15
def h0Bucket8 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 8 xs.toFinset) h0Bucket8 := buildBucketsBT_of_mem (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append h0Block8_0Mem h0Block8_1Mem) h0Block8_2Mem) h0Block8_3Mem) h0Block8_4Mem) h0Block8_5Mem) h0Block8_6Mem) h0Block8_7Mem) h0Block8_8Mem) h0Block8_9Mem) h0Block8_10Mem) h0Block8_11Mem) h0Block8_12Mem) h0Block8_13Mem) h0Block8_14Mem) h0Block8_15Mem)
def h0Block9_0Specs : List PoolSpec := [(15,[]),(11,[]),(7,[]),(20,[]),(13,[]),(48,[]),(17,[]),(37,[]),(32,[]),(10,[(0,0,1)]),(29,[]),(56,[]),(25,[]),(15,[(0,3,4)]),(13,[(0,0,1)]),(44,[]),(35,[]),(45,[]),(51,[]),(49,[]),(47,[]),(14,[]),(36,[]),(9,[(2,2,22)]),(2,[(0,0,1),(0,3,4),(2,2,22)]),(18,[]),(9,[(2,2,83)]),(3,[]),(4,[]),(34,[]),(30,[]),(28,[]),(12,[(2,2,22)]),(2,[(1,0,1),(0,3,4),(2,2,22)]),(18,[(1,0,1)]),(27,[]),(19,[]),(55,[]),(52,[]),(9,[(0,0,4)]),(31,[])]
def h0Block9_0Pools : BT (Option BoundPool) := buildPoolsBT 6 h0W h0R h0Slices h0Block9_0Specs
def h0Block9_0 : List NodeSpec := [([162,123,0,1,2,3,4,5],[2,19,28,30],[0]),([164,123,0,1,2,3,4,5],[5,7,8,19,28,30,36,38],[0]),([306,0,1,2,70,3,4,5],[3,7,8,12,13,22,27,40],[0,1,4]),([279,286,0,1,2,3,4,5],[1,4,10,12,20,27,35,37],[]),([279,225,0,1,2,3,4,5],[1,4,10,12,15,20,37,39],[0]),([85,123,0,1,2,3,4,5],[2,15,28,29],[0]),([85,6,0,1,2,3,4,5],[6,14,15,26],[0]),([85,0,1,89,2,3,4,5],[27,29,31,34],[0]),([65,123,0,1,2,3,4,5],[0,2,11,16,18,20,30],[0]),([65,6,0,1,2,3,4,5],[9,11,16,23,24],[0]),([65,0,1,89,2,3,4,5],[11,17,21,31,32,33],[0,2]),([87,123,0,1,2,3,4,5],[7,12,15,20,25,28],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_0Ok : checkNodesBT h0W h0G h0Mask h0Block9_0Pools h0Autos h0Bucket8 9 h0Block9_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_0Mem : ∀ ns ∈ h0Block9_0, Impossible h0G 9 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket8Ok h0Block9_0Ok
def h0Block9_1Specs : List PoolSpec := [(15,[]),(9,[]),(11,[]),(7,[]),(20,[]),(21,[]),(48,[]),(32,[]),(22,[]),(10,[(0,0,1)]),(29,[]),(8,[]),(5,[]),(43,[]),(25,[]),(11,[(0,2,3)]),(44,[]),(35,[]),(45,[]),(51,[]),(47,[]),(14,[]),(36,[]),(38,[]),(16,[(0,3,4)]),(18,[]),(9,[(3,83,4)]),(1,[(0,0,1),(0,3,5)]),(3,[]),(4,[]),(5,[(1,0,1)]),(12,[]),(30,[]),(39,[]),(28,[]),(33,[]),(4,[(0,2,3),(2,0,36)]),(12,[(3,22,5)]),(11,[(0,1,3)]),(11,[(3,1,3)])]
def h0Block9_1Pools : BT (Option BoundPool) := buildPoolsBT 6 h0W h0R h0Slices h0Block9_1Specs
def h0Block9_1 : List NodeSpec := [([87,6,0,1,2,3,4,5],[5,9,10,14,16,20,26,27],[0]),([87,0,1,89,2,3,4,5],[14,19,20,22,25,28],[0]),([81,123,0,1,2,3,4,5],[6,7,17,19,21,23,29,32],[0]),([81,6,0,1,2,3,4,5],[4,6,9,10,17,23,24,25],[0]),([81,0,1,89,2,3,4,5],[6,18,21,23,30,34,37],[0,2]),([264,243,0,1,2,3,4,5],[1,10,29,33,39],[]),([264,0,240,1,2,3,4,5],[1,10,13,38],[0]),([107,123,1,36,2,3,4,5],[3,10,15,28,32],[]),([107,1,89,36,2,3,4,5],[3,8,10,28,32,35],[]),([107,1,89,2,3,4,5],[0,2,3,11,36],[]),([110,0,1,2,22,3,4,5],[5,6,8,11,12,21,31],[0,2]),([108,0,1,36,2,3,4,5],[10,11,12,35],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_1Ok : checkNodesBT h0W h0G h0Mask h0Block9_1Pools h0Autos h0Bucket8 9 h0Block9_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_1Mem : ∀ ns ∈ h0Block9_1, Impossible h0G 9 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket8Ok h0Block9_1Ok
def h0Block9_2Specs : List PoolSpec := [(9,[]),(11,[]),(7,[]),(0,[]),(20,[]),(10,[]),(16,[]),(21,[]),(48,[]),(17,[]),(37,[]),(32,[]),(22,[]),(15,[(3,2,3)]),(10,[(0,0,1)]),(29,[]),(54,[]),(8,[]),(5,[]),(56,[]),(42,[]),(43,[]),(25,[]),(15,[(0,3,4)]),(13,[(0,0,1)]),(44,[]),(23,[]),(45,[]),(51,[]),(14,[(0,0,1)]),(49,[]),(53,[]),(47,[]),(36,[]),(38,[]),(34,[]),(30,[]),(39,[]),(28,[]),(33,[]),(2,[(1,0,1),(0,2,3),(2,89,36)]),(16,[(0,0,4)]),(10,[(0,0,4)]),(9,[(0,0,4)]),(31,[]),(0,[(0,0,4),(3,225,5)])]
def h0Block9_2Pools : BT (Option BoundPool) := buildPoolsBT 6 h0W h0R h0Slices h0Block9_2Specs
def h0Block9_2 : List NodeSpec := [([108,0,1,2,3,4,5],[1,4,6,7,15,17,35,40],[0]),([66,6,0,1,2,22,3,4,5],[8,14,15,19,23,24,29,33,34],[0]),([84,6,0,1,2,83,3,4,5],[10,14,20,25,32],[0]),([84,225,0,1,2,83,3,4,5],[9,25,28,32,42],[0]),([19,278,0,1,2,3,4,5],[5,12,20,22,36],[]),([19,123,0,1,2,3,27,4,5],[10,11,13,16,22,26,30,36],[0]),([19,185,286,0,1,2,3,4,5],[10,11,27,31,36,38],[]),([19,185,225,0,1,2,3,4,5],[10,20,21,36,42],[]),([19,235,225,0,1,2,3,4,5],[11,13,36,39,43,44],[]),([19,231,225,0,1,2,4,5],[3,11,13,39],[]),([19,231,0,1,2,4,5],[2,7,10,11,12,13,17,39],[0]),([19,261,0,1,2,3,4,5],[0,5,18,20,31,36,37,41,45],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_2Ok : checkNodesBT h0W h0G h0Mask h0Block9_2Pools h0Autos h0Bucket8 9 h0Block9_2 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_2Mem : ∀ ns ∈ h0Block9_2, Impossible h0G 9 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket8Ok h0Block9_2Ok
def h0Block9_3Specs : List PoolSpec := [(15,[]),(9,[]),(20,[]),(10,[]),(13,[]),(16,[]),(48,[]),(17,[]),(37,[]),(32,[]),(22,[]),(15,[(3,2,3)]),(10,[(0,0,1)]),(54,[]),(9,[(0,4,5)]),(8,[]),(5,[]),(56,[]),(42,[]),(25,[]),(23,[]),(49,[]),(53,[]),(17,[(0,0,1)]),(14,[]),(36,[]),(4,[]),(12,[]),(30,[]),(26,[]),(39,[]),(17,[(1,0,1)]),(28,[]),(33,[]),(12,[(3,2,3)]),(40,[]),(9,[(3,123,5)]),(0,[(2,0,1),(3,123,5)]),(16,[(0,0,4)]),(10,[(0,0,4)]),(9,[(0,0,4)]),(31,[]),(0,[(0,0,4),(0,4,5)])]
def h0Block9_3Pools : BT (Option BoundPool) := buildPoolsBT 6 h0W h0R h0Slices h0Block9_3Specs
def h0Block9_3 : List NodeSpec := [([19,15,0,1,2,4,5],[1,6,9,10,11],[0]),([19,34,0,1,2,3,4,5],[0,1,2,4,18,19],[0]),([19,6,0,1,2,3,27,4,5],[9,12,13,14,19,20,21,23,24],[0]),([19,225,0,184,1,2,3,4,5],[7,18,22,30,40],[0]),([19,225,0,1,226,2,3,4,5],[1,8,9,11,33,39],[]),([19,225,0,1,2,3,27,5],[15,18,19,27,38,42],[]),([19,0,291,1,2,3,4,5],[3,9,15,16,22,35,41],[]),([19,0,1,135,2,3,4,5],[3,8,9,16,22],[]),([19,0,1,137,2,3,4,5],[0,2,8,18,19,26,36,37],[0]),([19,0,1,226,2,3,4,5],[3,8,15,16,18,28],[0]),([19,0,1,96,2,3,4,5],[2,3,5,15,17,19,29,31,34],[0]),([19,0,1,89,2,3,27,4,5],[4,8,13,19,25,31,32],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_3Ok : checkNodesBT h0W h0G h0Mask h0Block9_3Pools h0Autos h0Bucket8 9 h0Block9_3 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_3Mem : ∀ ns ∈ h0Block9_3, Impossible h0G 9 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket8Ok h0Block9_3Ok
def h0Block9_4Specs : List PoolSpec := [(11,[]),(10,[]),(13,[]),(21,[]),(48,[]),(17,[]),(37,[]),(32,[]),(22,[]),(10,[(0,0,1)]),(9,[(3,2,4)]),(9,[(0,2,5)]),(29,[]),(5,[]),(42,[]),(43,[]),(23,[]),(53,[]),(47,[]),(14,[]),(36,[]),(4,[]),(34,[]),(30,[]),(17,[(1,0,1)]),(28,[]),(33,[]),(55,[]),(13,[(0,0,3)]),(1,[(3,0,3),(3,197,1)]),(3,[(3,2,4)]),(1,[(3,0,3),(0,1,5)]),(3,[(0,1,5),(3,2,4)]),(3,[(3,1,5),(3,2,4)])]
def h0Block9_4Pools : BT (Option BoundPool) := buildPoolsBT 6 h0W h0R h0Slices h0Block9_4Specs
def h0Block9_4 : List NodeSpec := [([58,123,0,1,2,3,4,5],[1,5,6,14,21],[]),([58,6,0,1,2,3,4,5],[2,8,9,11,14,17],[]),([58,0,1,89,2,3,4,5],[1,6,24,25],[0]),([138,123,0,1,2,3,4,5],[1,7,8,18,23],[0]),([138,0,1,2,22,4,5],[1,3,4,6,7,16,19],[4]),([23,123,0,1,2,83,3,4,5],[4,6,14,22,27],[0]),([23,185,197,0,1,2,3,4,5],[4,6,15,22,26,33],[]),([23,185,171,0,1,2,3,4,5],[6,14,15,22,28],[]),([23,172,0,1,2,3,4,5],[2,13,15,20],[]),([23,197,0,184,1,2,3,4,5],[1,4,12,26,31,32],[0]),([23,15,0,1,2,3,4,5],[0,4,8,10],[]),([23,198,0,1,2,3,4,5],[2,12,13,15,29,30],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_4Ok : checkNodesBT h0W h0G h0Mask h0Block9_4Pools h0Autos h0Bucket8 9 h0Block9_4 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_4Mem : ∀ ns ∈ h0Block9_4, Impossible h0G 9 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket8Ok h0Block9_4Ok
def h0Block9_5Specs : List PoolSpec := [(15,[]),(9,[]),(11,[]),(20,[]),(10,[]),(13,[]),(16,[]),(48,[]),(17,[]),(37,[]),(32,[]),(22,[]),(29,[]),(54,[]),(8,[]),(5,[]),(56,[]),(42,[]),(25,[]),(15,[(0,3,4)]),(35,[]),(23,[]),(45,[]),(51,[]),(36,[]),(1,[(0,0,1),(3,2,5)]),(4,[]),(12,[]),(34,[]),(30,[]),(39,[]),(27,[]),(55,[]),(0,[(2,0,1),(3,2,5)]),(11,[(0,1,5)]),(0,[(3,1,4),(3,2,5)]),(3,[(3,1,4),(3,2,5)]),(4,[(3,0,3),(3,2,5)]),(5,[(3,0,3),(3,1,4)])]
def h0Block9_5Pools : BT (Option BoundPool) := buildPoolsBT 6 h0W h0R h0Slices h0Block9_5Specs
def h0Block9_5 : List NodeSpec := [([23,171,0,184,1,2,3,4,5],[12,17,24,30,31,34],[]),([23,0,1,126,2,3,4,5],[2,5,7,15,27],[]),([23,0,1,137,2,3,4,5],[0,3,4,7,17,27],[0]),([23,0,1,92,2,3,4,5],[7,11,14,24,27],[]),([60,123,0,1,2,3,4,5],[4,5,7,8,17,26,28],[]),([25,123,0,1,2,22,3,4,5],[9,10,16,18,20,23,33],[0]),([25,191,197,0,1,2,3,4,5],[10,12,13,16,29,32,36,37,38],[0,1,4]),([25,191,171,0,1,2,3,4,5],[10,18,22,24,30,35],[0]),([25,183,0,1,2,3,4,5],[2,9,10,14,15,22,31],[]),([25,15,0,1,2,3,4,5],[0,1,7,11,12],[0]),([25,34,0,1,2,3,4],[0,3,6,10,12],[]),([25,6,0,1,2,22,3,4,5],[7,12,16,18,19,20,21,25],[0,2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_5Ok : checkNodesBT h0W h0G h0Mask h0Block9_5Pools h0Autos h0Bucket8 9 h0Block9_5 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_5Mem : ∀ ns ∈ h0Block9_5, Impossible h0G 9 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket8Ok h0Block9_5Ok
def h0Block9_6Specs : List PoolSpec := [(15,[]),(11,[]),(2,[]),(20,[]),(10,[]),(13,[]),(16,[]),(21,[]),(48,[]),(17,[]),(37,[]),(32,[]),(22,[]),(29,[]),(54,[]),(8,[]),(5,[]),(56,[]),(15,[(0,2,3)]),(25,[]),(13,[(0,0,1)]),(11,[(0,2,3)]),(45,[]),(51,[]),(53,[]),(47,[]),(36,[]),(4,[]),(3,[(3,2,5)]),(5,[(1,0,1)]),(34,[]),(30,[]),(4,[(3,2,5)]),(14,[(1,0,1)]),(12,[(3,2,5)]),(5,[(1,0,1),(0,3,4)]),(27,[]),(13,[(2,0,1)]),(2,[(2,0,1),(0,2,3),(3,36,4)]),(10,[(2,0,1)]),(15,[(0,1,4)]),(9,[(3,197,4)]),(0,[(3,197,4),(3,2,5)])]
def h0Block9_6Pools : BT (Option BoundPool) := buildPoolsBT 6 h0W h0R h0Slices h0Block9_6Specs
def h0Block9_6 : List NodeSpec := [([25,171,0,188,1,2,3,4,5],[10,11,13,22,36,40],[]),([25,0,203,1,2,3,4,5],[6,7,10,16,23,24,28,41,42],[0]),([25,0,1,126,2,3,4,5],[0,3,8,12,19,32],[0]),([25,0,1,135,2,3,4,5],[1,3,7,10,11,19,23],[]),([25,0,1,90,3,4,5],[2,4,5,23,27,28,29],[]),([25,0,1,92,2,3,4,5],[8,12,15,22,26,32],[]),([25,0,1,89,2,22,3,4,5],[4,8,10,17,19,22,26,33,34,35],[0]),([21,123,0,1,2,3,4,5],[3,9,10,11,23,27,39],[0]),([38,123,0,1,2,3,4,5],[5,7,10,21,23,30,38],[0]),([38,6,0,1,2,3,4,5],[7,13,14,20,21],[0]),([38,0,1,89,2,3,4,5],[4,5,7,24,26,30],[0]),([52,123,0,1,36,2,3,4,5],[13,18,25,31,37],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_6Ok : checkNodesBT h0W h0G h0Mask h0Block9_6Pools h0Autos h0Bucket8 9 h0Block9_6 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_6Mem : ∀ ns ∈ h0Block9_6, Impossible h0G 9 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket8Ok h0Block9_6Ok
def h0Block9_7Specs : List PoolSpec := [(15,[]),(7,[]),(20,[]),(10,[]),(13,[]),(21,[]),(48,[]),(17,[]),(37,[]),(22,[]),(29,[]),(8,[]),(5,[]),(56,[]),(15,[(0,2,3)]),(13,[(0,0,1)]),(11,[(0,2,3)]),(44,[]),(35,[]),(23,[]),(45,[]),(51,[]),(14,[]),(3,[]),(3,[(3,90,5)]),(4,[(3,90,5)]),(34,[]),(30,[]),(39,[]),(17,[(1,0,1)]),(28,[]),(4,[(3,96,3)]),(2,[(1,0,1),(0,2,3)]),(13,[(1,0,1)]),(2,[(2,0,1),(0,2,3),(0,36,4)]),(10,[(2,0,1)])]
def h0Block9_7Pools : BT (Option BoundPool) := buildPoolsBT 6 h0W h0R h0Slices h0Block9_7Specs
def h0Block9_7 : List NodeSpec := [([52,123,0,1,2,3,4,5],[1,2,9,10,14,21],[0]),([52,6,0,1,2,3,4,5],[2,7,10,14,15],[0,2]),([52,0,1,89,36,2,3,4,5],[0,6,10,20,27,33],[]),([52,0,1,89,2,3,4,5],[2,3,7,11,20,21,32],[0]),([49,0,1,2,22,3,4,5],[5,6,8,13,19,22],[0]),([100,0,1,96,2,3,4,5],[0,2,13,28,29,30],[0,2]),([103,0,1,96,2,3,4,5],[2,11,13,28],[]),([103,0,1,2,3,4,5],[2,4,6,8,9,11,12,28,31],[0]),([91,0,1,2,3,4,5],[2,3,4,24,25],[]),([128,0,1,126,2,3,4,5],[9,12,17,18,27],[]),([123,0,1,37,2,3,4,5],[1,16,21,23,27,34],[0]),([123,0,1,50,2,3,4,5],[14,23,26,35],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_7Ok : checkNodesBT h0W h0G h0Mask h0Block9_7Pools h0Autos h0Bucket8 9 h0Block9_7 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_7Mem : ∀ ns ∈ h0Block9_7, Impossible h0G 9 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket8Ok h0Block9_7Ok
def h0Block9_8Specs : List PoolSpec := [(11,[]),(10,[]),(13,[]),(21,[]),(48,[]),(17,[]),(37,[]),(15,[(0,2,4)]),(32,[]),(22,[]),(54,[]),(8,[]),(15,[(0,2,3)]),(42,[]),(15,[(0,3,4)]),(11,[(0,2,3)]),(35,[]),(23,[]),(51,[]),(49,[]),(47,[]),(36,[]),(15,[(3,25,3)]),(38,[]),(18,[]),(11,[(0,3,5)]),(3,[]),(4,[]),(34,[]),(30,[]),(19,[]),(17,[(2,0,1)]),(13,[(2,0,1)]),(5,[(2,0,1)]),(14,[(2,0,1)]),(11,[(3,23,3)]),(0,[(2,0,1),(3,2,5),(3,25,4)])]
def h0Block9_8Pools : BT (Option BoundPool) := buildPoolsBT 6 h0W h0R h0Slices h0Block9_8Specs
def h0Block9_8 : List NodeSpec := [([123,0,1,36,2,22,4,5],[6,15,24,28],[0]),([123,0,1,36,2,3,27,4,5],[6,10,12,18,19,21,28],[0]),([123,0,1,62,2,3,4,5],[6,9,22,33],[0]),([123,0,1,139,2,3,4,5],[2,6,18,28,31,35],[0]),([123,0,1,59,2,3,4,5],[7,26,29,32],[0]),([123,0,1,18,2,22,3,5],[0,11,17,29,30,34],[0]),([123,0,1,18,2,83,3,4,5],[8,18,20,25,29],[0]),([123,0,1,26,2,3,4,5],[3,6,8,18,27,36],[0]),([123,0,1,24,2,22,3,4,5],[4,6,14,16,23,29,32],[]),([123,0,1,2,151,3,4,5],[2,4,5,13,23,27,28],[]),([123,0,1,2,20,3,4,5],[1,5,8,27,29],[0]),([123,0,1,2,56,3,4,5],[1,5,13,18,27,29],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_8Ok : checkNodesBT h0W h0G h0Mask h0Block9_8Pools h0Autos h0Bucket8 9 h0Block9_8 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_8Mem : ∀ ns ∈ h0Block9_8, Impossible h0G 9 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket8Ok h0Block9_8Ok
def h0Block9_9Specs : List PoolSpec := [(15,[]),(9,[]),(11,[]),(7,[]),(0,[]),(20,[]),(10,[]),(13,[]),(21,[]),(48,[]),(17,[]),(37,[]),(32,[]),(22,[]),(29,[]),(5,[]),(42,[]),(25,[]),(15,[(0,3,4)]),(44,[]),(51,[]),(46,[]),(3,[]),(4,[]),(12,[]),(30,[]),(39,[]),(33,[]),(41,[]),(12,[(3,2,5)]),(4,[(3,124,5)]),(27,[]),(40,[]),(12,[(3,126,5)]),(13,[(2,0,1)]),(5,[(2,0,1)]),(16,[(0,0,4)]),(10,[(0,0,4)]),(9,[(0,0,4)]),(31,[]),(15,[(3,1,3)]),(0,[(0,0,4),(0,225,5)]),(13,[(0,225,5)]),(0,[(0,0,4),(3,225,5)])]
def h0Block9_9Pools : BT (Option BoundPool) := buildPoolsBT 6 h0W h0R h0Slices h0Block9_9Specs
def h0Block9_9 : List NodeSpec := [([123,0,1,2,70,3,4,5],[5,11,12,17,18,22,25],[0]),([123,1,36,2,141,3,4,5],[2,14,25,34],[]),([129,0,1,126,2,3,4,5],[2,8,11,19],[]),([129,0,1,2,3,4,5],[2,3,5,8,10,17,24,25],[]),([131,0,1,126,2,3,4,5],[0,13,25,32],[]),([131,0,1,2,3,4,5],[0,5,6,8,9,15,25,33],[]),([125,0,1,2,3,4,5],[0,5,6,7,30],[]),([153,0,1,2,3,4,5],[0,4,8,12,13,29,31,35],[0]),([283,225,0,1,2,83,3,4,5],[16,19,20,21,25,28,36,37,38],[]),([243,229,225,0,1,2,3,4,5],[14,17,27,37,39,40],[]),([243,261,0,1,2,3,4,5],[1,16,20,23,26,27,43],[]),([243,258,0,1,2,3,4,5],[1,6,13,14,17,39,40,41,42],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_9Ok : checkNodesBT h0W h0G h0Mask h0Block9_9Pools h0Autos h0Bucket8 9 h0Block9_9 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_9Mem : ∀ ns ∈ h0Block9_9, Impossible h0G 9 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket8Ok h0Block9_9Ok
def h0Block9_10Specs : List PoolSpec := [(15,[]),(9,[]),(11,[]),(10,[]),(13,[]),(16,[]),(21,[]),(48,[]),(17,[]),(37,[]),(32,[]),(29,[]),(54,[]),(8,[]),(5,[]),(25,[]),(51,[]),(53,[]),(36,[]),(3,[]),(4,[]),(12,[]),(34,[]),(30,[]),(39,[]),(33,[]),(19,[]),(4,[(0,0,3),(1,171,2)]),(4,[(3,0,3),(1,197,2)]),(0,[(3,1,4),(1,197,2)]),(3,[(3,1,4)]),(3,[(0,1,5),(3,184,3)]),(2,[(3,0,3),(3,184,3)]),(2,[(3,0,3),(3,184,4)]),(16,[(0,0,4)]),(12,[(1,225,2)]),(9,[(0,0,4)]),(31,[]),(0,[(0,0,4),(1,225,2)]),(15,[(3,1,3)]),(5,[(0,0,4),(3,1,3)]),(0,[(0,0,4),(3,1,5)]),(13,[(3,286,5)])]
def h0Block9_10Pools : BT (Option BoundPool) := buildPoolsBT 6 h0W h0R h0Slices h0Block9_10Specs
def h0Block9_10 : List NodeSpec := [([243,225,0,1,2,227,3,4,5],[3,25,36,37,38,39,40],[]),([243,225,0,1,2,3,27,5],[4,12,13,15,18,21,24,26,34],[]),([243,0,291,1,2,3,4,5],[1,3,10,11,13,16,20,37,42],[]),([243,0,1,2,293,3,4,5],[1,7,20,37],[]),([243,0,1,2,227,3,4,5],[1,7,11,13,24,35],[]),([220,197,0,1,2,4,5],[1,7,9,31,32],[0]),([191,0,1,2,216,3,4,5],[14,17,28,29,30],[0]),([191,0,1,2,189,3,4,5],[14,17,18,27],[0]),([195,197,0,1,2,3,4,5],[1,3,6,7,15,18,19,33],[0,1]),([195,171,0,1,2,3,4,5],[2,3,6,10,13,18,21,24],[]),([185,229,0,1,2,3,4,5],[0,5,20,22,23],[]),([185,231,0,1,2,3,4,5],[0,5,7,8,9,20,23,25,41],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_10Ok : checkNodesBT h0W h0G h0Mask h0Block9_10Pools h0Autos h0Bucket8 9 h0Block9_10 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_10Mem : ∀ ns ∈ h0Block9_10, Impossible h0G 9 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket8Ok h0Block9_10Ok
def h0Block9_11Specs : List PoolSpec := [(15,[]),(9,[]),(11,[]),(7,[]),(20,[]),(10,[]),(13,[]),(16,[]),(21,[]),(17,[]),(37,[]),(32,[]),(22,[]),(9,[(0,2,4)]),(29,[]),(54,[]),(8,[]),(5,[]),(25,[]),(45,[]),(4,[]),(12,[]),(30,[]),(28,[]),(33,[]),(50,[]),(4,[(0,0,3)]),(2,[(3,0,3),(3,197,4)]),(3,[(3,1,5)]),(16,[(0,0,4)]),(5,[(0,0,4)]),(9,[(0,0,4)]),(31,[]),(9,[(0,0,4),(3,225,2)]),(0,[(0,0,4),(3,225,2)]),(2,[(3,0,4),(3,286,2)])]
def h0Block9_11Pools : BT (Option BoundPool) := buildPoolsBT 6 h0W h0R h0Slices h0Block9_11Specs
def h0Block9_11 : List NodeSpec := [([185,183,0,1,2,3,4,5],[7,10,18,19,20,23],[]),([185,288,0,1,2,3,4,5],[4,7,22,32,35],[]),([185,290,0,1,2,3,4,5],[7,11,19,20,23,32],[]),([185,0,203,1,2,3,4,5],[7,9,10,18,20,22,24,27,28],[]),([236,225,0,1,2,3,4,5],[24,29,31],[0]),([205,0,203,1,2,3,4,5],[8,15,20,24],[]),([235,229,0,1,2,3,4,5],[0,1,5,21,24,30,33],[0]),([235,231,0,1,2,3,4,5],[0,12,16,21,24,31],[]),([235,0,1,2,227,3,4,5],[0,1,6,14,17,21,24],[]),([172,0,1,18,2,3,4,5],[2,3,9,13,19,23,25,26],[0]),([208,0,203,1,2,3,4,5],[8,15,17,18,24],[]),([229,231,0,1,2,3,4,5],[0,3,10,12,22,24,30,31,34],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_11Ok : checkNodesBT h0W h0G h0Mask h0Block9_11Pools h0Autos h0Bucket8 9 h0Block9_11 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_11Mem : ∀ ns ∈ h0Block9_11, Impossible h0G 9 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket8Ok h0Block9_11Ok
def h0Block9_12Specs : List PoolSpec := [(15,[]),(9,[]),(7,[]),(20,[]),(16,[]),(21,[]),(48,[]),(17,[]),(37,[]),(22,[]),(9,[(0,2,4)]),(29,[]),(8,[]),(5,[]),(25,[]),(44,[]),(35,[]),(3,[]),(4,[]),(12,[]),(34,[]),(30,[]),(39,[]),(33,[]),(40,[]),(10,[(0,1,5)]),(3,[(0,1,5),(0,2,4)]),(19,[(3,0,3)]),(1,[(3,0,3),(0,1,5)]),(2,[(3,0,3),(0,2,4)]),(5,[(0,0,4)]),(10,[(0,0,4)]),(9,[(0,0,4)]),(9,[(0,0,4),(3,225,2)]),(15,[(0,1,3)]),(11,[(0,1,3)]),(12,[(3,225,2)]),(13,[(0,1,5)]),(5,[(0,0,4),(3,225,3)]),(1,[(3,225,3),(0,1,5)])]
def h0Block9_12Pools : BT (Option BoundPool) := buildPoolsBT 6 h0W h0R h0Slices h0Block9_12Specs
def h0Block9_12 : List NodeSpec := [([229,225,0,240,1,2,3,4,5],[11,14,21,23,31,33,34,35,36],[0,2]),([229,0,184,1,2,3,4,5],[0,1,21,22,30,33,37],[0]),([229,0,1,226,2,3,4,5],[0,2,18,21,23,30],[0]),([292,0,1,2,3,4,5],[1,2,5,6,8,12,13,18,24],[]),([197,0,196,1,2,3,4,5],[4,8,14,17,19,20,24],[]),([197,0,184,1,18,2,3,4,5],[10,25,26,27,28,29],[0,1]),([255,0,1,2,3,4,5],[0,1,2,3,6,8,13,17,19,23],[]),([231,232,0,1,2,3,4,5],[8,9,15,16,18],[]),([231,253,0,1,2,3,4,5],[6,9,15,23,38],[]),([231,0,254,1,2,3,4,5],[0,3,6,16],[]),([231,0,184,1,2,3,4,5],[0,6,7,9,12,16,23,32,39],[0]),([231,0,1,250,2,3,4,5],[1,6,8,9,15,16,23],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_12Ok : checkNodesBT h0W h0G h0Mask h0Block9_12Pools h0Autos h0Bucket8 9 h0Block9_12 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_12Mem : ∀ ns ∈ h0Block9_12, Impossible h0G 9 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket8Ok h0Block9_12Ok
def h0Block9_13Specs : List PoolSpec := [(15,[]),(9,[]),(11,[]),(7,[]),(2,[]),(20,[]),(10,[]),(13,[]),(21,[]),(48,[]),(37,[]),(22,[]),(29,[]),(8,[]),(5,[]),(56,[]),(15,[(0,2,3)]),(42,[]),(25,[]),(15,[(0,3,4)]),(44,[]),(53,[]),(14,[]),(4,[]),(39,[]),(28,[]),(33,[]),(27,[]),(11,[(0,1,5)]),(11,[(0,2,5)]),(2,[(3,0,3),(3,197,4)]),(3,[(3,203,5)]),(16,[(0,0,4)]),(12,[(1,225,2)]),(0,[(0,0,4),(1,225,1)]),(9,[(0,0,4)]),(0,[(0,0,4),(1,225,2)]),(15,[(0,1,3)]),(0,[(0,0,4),(0,225,5)]),(0,[(0,0,4),(3,225,5)]),(1,[(3,225,5),(0,1,3)])]
def h0Block9_13Pools : BT (Option BoundPool) := buildPoolsBT 6 h0W h0R h0Slices h0Block9_13Specs
def h0Block9_13 : List NodeSpec := [([231,0,1,226,2,3,4,5],[0,10,11,23,26,34],[0]),([231,0,1,2,251,3,4,5],[3,11,13,20,26],[0]),([231,0,1,2,227,3,4,5],[7,9,10,11,12,14,26,33,35,36],[]),([231,0,1,2,22,4,5],[2,6,8,9,10,11,22,26],[4]),([259,0,1,2,3,4,5],[0,1,2,3,9,10,11,14,23,38],[4]),([209,0,203,1,2,3,4,5],[4,11,20,26],[]),([209,0,1,2,3,4,5],[1,3,10,11,14,21,23,26,30,31],[]),([261,0,240,1,2,3,4,5],[5,6,12,17,26,32,37,39,40],[3]),([261,0,1,36,2,3,4,5],[5,16,24,26,32,39],[]),([183,0,184,1,2,3,4,5],[0,8,18,25,27,28],[]),([183,0,1,24,2,3,4,5],[8,21,25,29],[]),([297,0,1,2,22,3,4,5],[5,9,15,19],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_13Ok : checkNodesBT h0W h0G h0Mask h0Block9_13Pools h0Autos h0Bucket8 9 h0Block9_13 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_13Mem : ∀ ns ∈ h0Block9_13, Impossible h0G 9 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket8Ok h0Block9_13Ok
def h0Block9_14Specs : List PoolSpec := [(15,[]),(9,[]),(11,[]),(7,[]),(20,[]),(10,[]),(13,[]),(16,[]),(21,[]),(48,[]),(17,[]),(15,[(0,2,4)]),(11,[(0,15,5)]),(22,[]),(10,[(0,0,1)]),(9,[(0,2,4)]),(9,[(0,2,5)]),(29,[]),(5,[(0,0,1),(3,6,3)]),(54,[]),(9,[(0,4,5)]),(5,[]),(13,[(0,0,1),(3,6,5)]),(15,[(0,2,3)]),(42,[]),(44,[]),(35,[]),(23,[]),(4,[]),(3,[(3,198,4)]),(4,[(3,0,3)]),(0,[(3,1,4),(1,191,197)]),(2,[(3,0,4),(3,286,2)])]
def h0Block9_14Pools : BT (Option BoundPool) := buildPoolsBT 6 h0W h0R h0Slices h0Block9_14Specs
def h0Block9_14 : List NodeSpec := [([289,0,1,2,3,4,5],[1,2,4,5,28,32],[]),([31,0,1,3,4,5],[1,2,3],[]),([16,0,1,2,3,4,5],[1,2,3,4,8,9,10],[]),([17,0,1,2,3,4,5],[0,1,3,4,8,9,10,12],[0]),([15,0,1,18,2,3,4,5],[2,11,13,14,15],[0]),([15,0,1,24,2,3,4,5],[0,9,13,14,16],[]),([15,0,1,2,22,4,5],[0,1,2,9,13,18],[0]),([15,0,1,2,3,27,4,5],[2,13,14,17,19,20],[]),([32,0,1,2,4,5],[0,1,2],[]),([199,0,1,2,3,4,5],[1,3,7,8,21,29],[]),([215,0,1,2,3,4,5],[4,6,7,21,25,26,27,30,31],[0,3]),([34,0,1,36,2,3,4,5],[1,4,17,22,23,24],[0,2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_14Ok : checkNodesBT h0W h0G h0Mask h0Block9_14Pools h0Autos h0Bucket8 9 h0Block9_14 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_14Mem : ∀ ns ∈ h0Block9_14, Impossible h0G 9 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket8Ok h0Block9_14Ok
def h0Block9_15Specs : List PoolSpec := [(9,[]),(11,[]),(7,[]),(20,[]),(10,[]),(48,[]),(17,[]),(37,[]),(32,[]),(22,[]),(10,[(0,0,1)]),(9,[(0,2,5)]),(29,[]),(54,[]),(9,[(0,4,5)]),(56,[]),(9,[(0,36,4)]),(15,[(0,2,3)]),(42,[]),(15,[(0,3,4)]),(13,[(0,0,1)]),(11,[(0,2,3)]),(44,[]),(35,[]),(23,[]),(45,[]),(2,[(0,0,1),(0,2,3),(0,36,4)]),(9,[(0,36,5)]),(51,[]),(14,[(0,0,1)]),(49,[]),(9,[(3,19,4)]),(9,[(3,19,5)]),(53,[]),(47,[]),(17,[(0,0,1)]),(14,[]),(15,[(3,25,3)]),(1,[(0,0,1),(3,2,5),(3,25,3)])]
def h0Block9_15Pools : BT (Option BoundPool) := buildPoolsBT 6 h0W h0R h0Slices h0Block9_15Specs
def h0Block9_15 : List NodeSpec := [([34,0,1,2,22,3,4,5],[0,3,15,18,19],[0,2]),([10,0,1,2,4,5],[0,1,2],[]),([6,0,1,37,2,22,3,4,5],[7,8,10,12,15,22,23,33,36],[0]),([6,0,1,37,2,3,4,5],[16,20,21,26],[0]),([6,0,1,50,2,83,3,4,5],[7,12,22,34,35],[0]),([6,0,1,50,2,3,4,5],[17,20,27],[0]),([6,0,1,36,2,22,4,5],[0,5,7,20,21,29],[0,2]),([6,0,1,36,2,3,27,4,5],[12,13,14,17,20,21,25,30],[0,2]),([6,0,1,62,2,3,4,5],[4,9,12,37,38],[0,2]),([6,0,1,24,2,22,3,4,5],[5,10,11,15,18,19,20,23,24,33],[]),([6,0,1,2,20,3,4,5],[6,8,10,31],[0]),([6,0,1,2,56,3,4,5],[6,10,18,28,32,33],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_15Ok : checkNodesBT h0W h0G h0Mask h0Block9_15Pools h0Autos h0Bucket8 9 h0Block9_15 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_15Mem : ∀ ns ∈ h0Block9_15, Impossible h0G 9 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket8Ok h0Block9_15Ok
def h0Block9_16Specs : List PoolSpec := [(15,[]),(20,[]),(10,[]),(13,[]),(16,[]),(21,[]),(48,[]),(37,[]),(15,[(0,2,4)]),(32,[]),(22,[]),(10,[(0,0,1)]),(9,[(0,2,4)]),(9,[(0,2,5)]),(29,[]),(8,[]),(56,[]),(42,[]),(25,[]),(15,[(0,3,4)]),(44,[]),(35,[]),(23,[]),(45,[]),(49,[]),(53,[]),(47,[]),(14,[]),(36,[]),(38,[]),(11,[(0,22,5)]),(9,[(0,22,5)]),(18,[]),(46,[]),(11,[(0,3,5)]),(39,[]),(28,[]),(27,[]),(11,[(0,1,5)]),(13,[(0,0,3)]),(15,[(0,1,4)]),(11,[(3,191,5)]),(10,[(0,1,5)]),(15,[(3,185,4)]),(10,[(3,197,1)]),(3,[(0,2,4)]),(1,[(3,0,3),(3,197,1)]),(2,[(3,0,3),(3,197,1),(0,2,4)]),(5,[(0,0,4)]),(9,[(0,0,4)]),(11,[(3,229,1)]),(11,[(3,231,1)])]
def h0Block9_16Pools : BT (Option BoundPool) := buildPoolsBT 6 h0W h0R h0Slices h0Block9_16Specs
def h0Block9_16 : List NodeSpec := [([6,0,1,2,70,22,3,4,5],[7,11,14,16,20,21,22,24,25,29],[0]),([6,0,1,2,70,83,3,4,5],[6,7,11,14,21,24,26,32,33,34],[0]),([6,0,1,2,70,3,4,5],[1,11,14,18,19,20,21,22,24,30,31],[0]),([232,225,0,1,2,3,4,5],[3,14,15,18,20,49,51],[0]),([198,0,1,18,2,3,4,5],[12,44,45,46,47],[0]),([230,225,0,1,2,3,4,5],[17,48,49,50],[0]),([13,0,1,2,3,4,5],[0,1,2,3,4],[]),([61,0,1,2,3,4,5],[0,4,5,9,10,14,27],[0]),([171,0,188,1,24,2,3,4,5],[7,13,36,37,39,40],[]),([171,0,196,1,2,3,4,5],[7,15,28,43],[]),([171,0,184,1,18,2,3,4,5],[8,9,12,36,37,38,42],[]),([171,0,1,192,2,3,4,5],[15,23,35,41],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_16Ok : checkNodesBT h0W h0G h0Mask h0Block9_16Pools h0Autos h0Bucket8 9 h0Block9_16 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_16Mem : ∀ ns ∈ h0Block9_16, Impossible h0G 9 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket8Ok h0Block9_16Ok
def h0Block9_17Specs : List PoolSpec := [(11,[]),(10,[]),(13,[]),(37,[]),(22,[]),(29,[]),(8,[]),(5,[]),(42,[]),(43,[]),(25,[]),(44,[]),(51,[]),(47,[]),(18,[]),(4,[]),(12,[]),(30,[]),(39,[]),(33,[]),(55,[]),(16,[(0,0,4)]),(12,[(1,225,2)]),(5,[(0,0,4)]),(10,[(0,0,4)]),(9,[(0,0,4)]),(11,[(3,235,3)]),(0,[(0,0,4),(1,225,2)]),(15,[(0,1,227)]),(1,[(1,225,2),(0,1,227)]),(9,[(0,0,4),(1,225,2)]),(5,[(0,0,4),(0,1,3)]),(15,[(0,1,3)]),(11,[(0,1,3)]),(11,[(3,229,3)]),(0,[(0,0,4),(3,1,5)]),(0,[(0,0,4),(0,225,5)]),(13,[(0,225,5)]),(15,[(3,185,3)]),(1,[(3,2,3),(3,19,1)]),(8,[(3,19,1)])]
def h0Block9_17Pools : BT (Option BoundPool) := buildPoolsBT 6 h0W h0R h0Slices h0Block9_17Specs
def h0Block9_17 : List NodeSpec := [([258,0,240,1,2,3,4,5],[1,5,10,21,33,36,37],[0]),([225,0,239,1,2,3,4,5],[4,8,17,24,34],[0]),([225,0,272,1,2,3,4,5],[7,8,19,24],[]),([225,0,238,1,2,3,4,5],[4,5,18,25,26],[0]),([225,0,267,1,2,3,4,5],[15,18,19],[]),([225,0,275,1,2,3,4,5],[0,19,21,24,39,40],[0]),([225,0,228,1,2,3,4,5],[2,23,25,28,29],[0]),([225,0,249,1,2,83,3,4,5],[5,8,11,12,13,14,18,24],[0]),([225,0,240,1,237,2,3,4,5],[17,19,24,25,31,32,33],[0,2]),([225,0,240,1,2,227,3,4,5],[1,19,22,25,27,30,31,32,33],[0]),([225,0,240,1,2,83,4,5],[1,3,6,9,14,20,21,32],[]),([225,0,273,1,2,3,4,5],[2,9,10,16,17,21,35,38],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_17Ok : checkNodesBT h0W h0G h0Mask h0Block9_17Pools h0Autos h0Bucket8 9 h0Block9_17 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_17Mem : ∀ ns ∈ h0Block9_17, Impossible h0G 9 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket8Ok h0Block9_17Ok
def h0Block9_18Specs : List PoolSpec := [(15,[]),(9,[]),(11,[]),(7,[]),(20,[]),(10,[]),(21,[]),(48,[]),(17,[]),(37,[]),(22,[]),(29,[]),(54,[]),(8,[]),(5,[]),(15,[(0,2,3)]),(42,[]),(43,[]),(25,[]),(44,[]),(35,[]),(23,[]),(51,[]),(53,[]),(47,[]),(14,[]),(18,[]),(4,[]),(12,[]),(30,[]),(39,[]),(28,[]),(33,[]),(27,[]),(55,[]),(0,[(3,197,4),(0,203,5)]),(2,[(3,0,3),(3,197,4)]),(9,[(3,197,4)]),(3,[(0,1,5)]),(5,[(0,0,4)]),(0,[(0,0,4),(1,225,1)]),(15,[(0,226,3)]),(10,[(0,0,4)]),(9,[(0,0,4)]),(0,[(0,0,4),(1,225,2)]),(15,[(0,227,3)]),(11,[(0,227,3)]),(13,[(0,1,5)]),(17,[(0,0,4)])]
def h0Block9_18Pools : BT (Option BoundPool) := buildPoolsBT 6 h0W h0R h0Slices h0Block9_18Specs
def h0Block9_18 : List NodeSpec := [([225,0,184,1,36,2,3,4,5],[11,15,30,32,43,47],[]),([225,0,184,1,2,83,3,4],[0,8,9,13,26,33,34,43],[0]),([225,0,1,268,2,3,4,5],[2,11,28,30,43],[0]),([225,0,1,233,2,3,4,5],[7,9,10,18,28,29,32,40,41],[0]),([225,0,1,50,2,83,3,4,5],[19,22,24,48],[0]),([225,0,1,2,56,3,4,5],[8,16,17,22,31,42],[]),([225,0,1,2,207,3,4,5],[9,10,11,28,39,43,44,45,46],[0]),([0,210,1,2,3,4,5],[1,2,3,4,6,14,18,20,21,22,27,35],[4]),([0,203,184,1,2,3,4,5],[6,8,23,32,36,37,38],[0]),([0,203,1,204,2,3,4,5],[1,6,12,32],[]),([0,203,1,2,206,3,4,5],[3,6,9,12,13,32],[0]),([0,203,1,2,22,3,5],[5,6,9,10,13,23,25],[4])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_18Ok : checkNodesBT h0W h0G h0Mask h0Block9_18Pools h0Autos h0Bucket8 9 h0Block9_18 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_18Mem : ∀ ns ∈ h0Block9_18, Impossible h0G 9 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket8Ok h0Block9_18Ok
def h0Block9_19Specs : List PoolSpec := [(15,[]),(9,[]),(11,[]),(7,[]),(20,[]),(10,[]),(13,[]),(16,[]),(21,[]),(48,[]),(17,[]),(37,[]),(22,[]),(8,[]),(5,[]),(43,[]),(35,[]),(51,[]),(53,[]),(14,[]),(4,[]),(12,[]),(30,[]),(39,[]),(27,[]),(2,[(3,0,3),(3,197,4)]),(3,[(0,4,5)]),(0,[(3,197,4),(0,4,5)]),(16,[(0,0,4)]),(9,[(0,0,4)]),(0,[(0,0,4),(1,225,2)]),(11,[(0,1,3)]),(13,[(0,1,5)]),(1,[(0,1,3),(1,225,2)]),(8,[(1,225,2)]),(1,[(0,1,5),(1,225,184)])]
def h0Block9_19Pools : BT (Option BoundPool) := buildPoolsBT 6 h0W h0R h0Slices h0Block9_19Specs
def h0Block9_19 : List NodeSpec := [([0,203,1,2,3,27,5],[8,18,25,26,27],[4,5]),([0,254,1,2,3,4,5],[0,1,3,8,9,14,16,17,20],[4]),([0,299,1,2,22,3,4,5],[8,9,16,19],[]),([0,247,1,2,3,4,5],[0,1,4,5,6,20],[]),([0,173,1,2,3,4,5],[3,7,8,13,14],[]),([0,240,1,237,2,3,4,5],[22,28,31],[]),([0,240,1,2,227,3,4,5],[6,12,14,15,30,31,33,34],[0]),([0,188,1,2,189,3,4,5],[5,8,14,18,21,24],[]),([0,184,1,270,2,3,4,5],[2,10,23,29,32,35],[]),([0,1,130,2,3,4,5],[2,3,4,8,9,10,21,24],[]),([0,1,132,2,3,4,5],[0,1,3,4,8,9,11,14,21,24],[0]),([0,1,126,18,2,3,4,5],[2,8,12,13,22],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_19Ok : checkNodesBT h0W h0G h0Mask h0Block9_19Pools h0Autos h0Bucket8 9 h0Block9_19 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_19Mem : ∀ ns ∈ h0Block9_19, Impossible h0G 9 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket8Ok h0Block9_19Ok
def h0Block9_20Specs : List PoolSpec := [(15,[]),(9,[]),(11,[]),(7,[]),(20,[]),(10,[]),(13,[]),(21,[]),(48,[]),(17,[]),(37,[]),(15,[(0,2,4)]),(32,[]),(22,[]),(29,[]),(54,[]),(8,[]),(5,[]),(15,[(0,2,3)]),(42,[]),(25,[]),(11,[(0,2,3)]),(44,[]),(35,[]),(51,[]),(53,[]),(18,[]),(12,[]),(34,[]),(30,[]),(4,[(0,3,5)]),(27,[]),(19,[]),(0,[(2,0,1),(3,123,4),(0,135,5)]),(55,[]),(9,[(3,123,5)]),(17,[(2,0,1)]),(0,[(2,0,1),(3,123,5)]),(2,[(3,0,3),(1,197,184)]),(2,[(3,0,4),(1,286,1)])]
def h0Block9_20Pools : BT (Option BoundPool) := buildPoolsBT 6 h0W h0R h0Slices h0Block9_20Specs
def h0Block9_20 : List NodeSpec := [([0,1,126,24,2,3,4,5],[0,3,8,9,29],[]),([0,1,126,2,127,3,4,5],[3,13,22,23,29],[]),([0,1,126,2,83,4,5],[0,8,10,13,30],[0]),([0,1,126,2,3,27,4,5],[2,4,6,8,9,15,27,29,32],[]),([0,1,219,2,3,4,5],[1,6,7,17,23,31,38],[0]),([0,1,136,2,3,4,5],[2,3,4,13,17,20,27,33],[0]),([0,1,135,36,2,3,4,5],[7,9,10,21,24,28],[0]),([0,1,135,24,2,3,4,5],[0,3,9,25,28],[]),([0,1,135,2,83,3,4,5],[0,2,7,10,34],[]),([0,1,294,2,83,3,4,5],[4,5,9,10,12,13,16,26,29,39],[]),([0,1,137,36,2,3,4,5],[3,4,10,14,18,27,29,35,36,37],[0]),([0,1,137,18,2,3,4,5],[4,11,12,19,27,29],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_20Ok : checkNodesBT h0W h0G h0Mask h0Block9_20Pools h0Autos h0Bucket8 9 h0Block9_20 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_20Mem : ∀ ns ∈ h0Block9_20, Impossible h0G 9 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket8Ok h0Block9_20Ok
def h0Block9_21Specs : List PoolSpec := [(15,[]),(7,[]),(1,[]),(20,[]),(10,[]),(21,[]),(48,[]),(17,[]),(37,[]),(22,[]),(54,[]),(8,[]),(5,[]),(56,[]),(42,[]),(15,[(0,3,4)]),(45,[]),(4,[(0,2,3)]),(47,[]),(36,[]),(3,[(3,2,5)]),(5,[(1,0,1)]),(12,[]),(4,[(0,92,5)]),(12,[(0,92,5)]),(34,[]),(30,[]),(8,[(0,2,5)]),(4,[(0,3,5)]),(33,[]),(12,[(3,2,5)]),(16,[(3,25,89)]),(18,[(2,0,1)]),(9,[(0,0,4)]),(15,[(0,1,3)]),(1,[(0,1,3),(1,225,240)]),(0,[(0,0,4),(1,225,240)])]
def h0Block9_21Pools : BT (Option BoundPool) := buildPoolsBT 6 h0W h0R h0Slices h0Block9_21Specs
def h0Block9_21 : List NodeSpec := [([0,1,137,2,22,3,4,5],[3,13,14,15,22],[0]),([0,1,137,2,83,3,4],[0,8,28,32],[0]),([0,1,115,2,3,4,5],[4,5,9,16,18,20,21,30,31],[0]),([0,1,93,2,3,4,5],[1,3,5,6,7,9,11,22],[]),([0,1,94,2,3,4,5],[1,3,5,6,11,12,23,24],[0]),([0,1,92,36,2,4,5],[6,9,11,17,25],[0]),([0,1,92,18,2,3,4,5],[2,5,9,11,16,19,26],[0]),([0,1,92,24,2,3,4,5],[6,9,26,27],[]),([0,1,92,2,22,4,5],[6,9,11,22],[0]),([0,1,92,2,83,4,5],[6,8,9,11,28],[0]),([0,1,92,2,3,27,4,5],[9,10,11,19,22],[]),([0,1,237,2,3,4,5],[1,3,12,26,29,33,34,35,36],[0,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_21Ok : checkNodesBT h0W h0G h0Mask h0Block9_21Pools h0Autos h0Bucket8 9 h0Block9_21 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_21Mem : ∀ ns ∈ h0Block9_21, Impossible h0G 9 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket8Ok h0Block9_21Ok
def h0Block9_22Specs : List PoolSpec := [(15,[]),(9,[]),(11,[]),(7,[]),(20,[]),(10,[]),(13,[]),(16,[]),(21,[]),(48,[]),(17,[]),(37,[]),(22,[]),(29,[]),(54,[]),(8,[]),(5,[]),(56,[]),(25,[]),(45,[]),(47,[]),(14,[]),(18,[]),(3,[]),(4,[]),(12,[]),(34,[]),(30,[]),(4,[(0,3,5)]),(39,[]),(17,[(1,0,1)]),(28,[]),(33,[]),(2,[(1,0,1),(0,2,3)]),(4,[(0,2,5)]),(2,[(1,0,1),(0,3,4)]),(12,[(0,2,3)]),(19,[(1,0,1)]),(12,[(1,225,2)]),(0,[(0,0,4),(1,225,1),(1,225,2)]),(9,[(0,0,4)]),(1,[(0,1,5),(1,225,184)])]
def h0Block9_22Pools : BT (Option BoundPool) := buildPoolsBT 6 h0W h0R h0Slices h0Block9_22Specs
def h0Block9_22 : List NodeSpec := [([0,1,270,2,3,4,5],[0,3,12,16,29,32,40,41],[0]),([0,1,226,2,227,3,4,5],[0,6,9,11,16,32,38,39],[0]),([0,1,226,2,83,3,4,5],[0,4,5,10,11,12,22,24,27],[0,4]),([0,1,96,36,2,3,4,5],[3,4,7,13,15,17,26,29,30,33],[0,2]),([0,1,96,24,2,3,4],[0,4,16,23,31,32,34],[0,2]),([0,1,96,2,97,3,4,5],[0,3,4,17,29,30],[0,2]),([0,1,96,2,22,3,4,5],[4,5,8,15,17,18,21,25,30,35],[0,2]),([0,1,96,2,83,3,4],[4,11,15,28],[0,2]),([0,1,89,37,2,3,4,5],[0,1,5,6,8,12,19,20,23,31,36],[0]),([0,1,89,50,2,3,4,5],[1,2,4,5,10,12,23,24,27,32,33],[0]),([0,1,89,36,2,22,4,5],[2,6,11,12,21,22,32],[0,2]),([0,1,89,36,2,3,27,4,5],[2,6,10,14,19,21,26,32,37],[0,2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_22Ok : checkNodesBT h0W h0G h0Mask h0Block9_22Pools h0Autos h0Bucket8 9 h0Block9_22 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_22Mem : ∀ ns ∈ h0Block9_22, Impossible h0G 9 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket8Ok h0Block9_22Ok
def h0Block9_23Specs : List PoolSpec := [(9,[]),(11,[]),(0,[]),(20,[]),(10,[]),(13,[]),(21,[]),(48,[]),(17,[]),(37,[]),(15,[(0,2,4)]),(24,[]),(32,[]),(22,[]),(29,[]),(5,[]),(15,[(0,2,3)]),(25,[]),(13,[(0,0,1)]),(5,[(0,0,1),(1,6,36)]),(23,[]),(45,[]),(51,[]),(53,[]),(14,[]),(36,[]),(38,[]),(18,[]),(3,[]),(4,[]),(5,[(1,0,1)]),(12,[]),(34,[]),(30,[]),(28,[]),(14,[(1,0,1)]),(27,[]),(0,[(2,0,1),(1,123,36)])]
def h0Block9_23Pools : BT (Option BoundPool) := buildPoolsBT 6 h0W h0R h0Slices h0Block9_23Specs
def h0Block9_23 : List NodeSpec := [([0,1,89,62,2,3,4,5],[4,9,13,15,21,28],[0]),([0,1,89,24,2,22,3,4,5],[3,7,20,22,23,26,34,35],[]),([0,1,89,2,20,3,4,5],[4,5,6,8,9,28,34],[0]),([0,1,89,2,56,3,4,5],[3,4,8,22,34],[]),([0,1,89,2,70,3,4,5],[0,1,3,6,13,17,22,24,25,27,28,29,30,34],[0]),([0,1,36,2,140,3,4,5],[14,16,32],[]),([0,1,36,2,39,3,4,5],[14,16,18,19],[0]),([0,1,18,2,147,3,4,5],[12,29,33],[]),([0,1,2,67,22,3,4,5],[6,7,9,20,24,26],[0]),([0,1,2,140,3,4,5],[3,5,6,14,16,28,32,36,37],[0]),([0,1,2,147,3,4,5],[1,2,3,10,11,13,31,33],[0]),([0,1,2,156,22,3,4,5],[1,6,7,13,24,31],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_23Ok : checkNodesBT h0W h0G h0Mask h0Block9_23Pools h0Autos h0Bucket8 9 h0Block9_23 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_23Mem : ∀ ns ∈ h0Block9_23, Impossible h0G 9 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket8Ok h0Block9_23Ok
def h0Block9_24Specs : List PoolSpec := [(9,[]),(11,[]),(7,[]),(20,[]),(10,[]),(13,[]),(21,[]),(48,[]),(37,[]),(22,[]),(10,[(0,0,1)]),(29,[]),(5,[]),(15,[(0,2,3)]),(25,[]),(5,[(0,0,1),(1,6,36)]),(11,[(0,2,3)]),(45,[]),(51,[]),(14,[]),(36,[]),(9,[(0,22,5)]),(3,[]),(4,[]),(28,[]),(27,[]),(10,[(0,22,5)])]
def h0Block9_24Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block9_24Specs
def h0Block9_24 : List NodeSpec := [([0,1,2,39,3,4,5],[0,2,3,6,10,11,13,15,16],[0]),([0,1,2,7,22,3,4,5],[0,1,6,7,9,12,19],[0]),([0,1,2,70,3,304,4,5],[1,3,8,14,20,21,24,25,26],[0,1,4]),([0,1,2,3,69,4,5],[0,1,3,4,5,17,18,22,23],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_24Ok : checkNodesBT h0W h0G h0Mask h0Block9_24Pools h0Autos h0Bucket8 9 h0Block9_24 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block9_24Mem : ∀ ns ∈ h0Block9_24, Impossible h0G 9 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket8Ok h0Block9_24Ok
def h0Nodes9 : List NodeSpec := h0Block9_0 ++ h0Block9_1 ++ h0Block9_2 ++ h0Block9_3 ++ h0Block9_4 ++ h0Block9_5 ++ h0Block9_6 ++ h0Block9_7 ++ h0Block9_8 ++ h0Block9_9 ++ h0Block9_10 ++ h0Block9_11 ++ h0Block9_12 ++ h0Block9_13 ++ h0Block9_14 ++ h0Block9_15 ++ h0Block9_16 ++ h0Block9_17 ++ h0Block9_18 ++ h0Block9_19 ++ h0Block9_20 ++ h0Block9_21 ++ h0Block9_22 ++ h0Block9_23 ++ h0Block9_24
def h0Bucket9 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket9Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 9 xs.toFinset) h0Bucket9 := buildBucketsBT_of_mem (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append h0Block9_0Mem h0Block9_1Mem) h0Block9_2Mem) h0Block9_3Mem) h0Block9_4Mem) h0Block9_5Mem) h0Block9_6Mem) h0Block9_7Mem) h0Block9_8Mem) h0Block9_9Mem) h0Block9_10Mem) h0Block9_11Mem) h0Block9_12Mem) h0Block9_13Mem) h0Block9_14Mem) h0Block9_15Mem) h0Block9_16Mem) h0Block9_17Mem) h0Block9_18Mem) h0Block9_19Mem) h0Block9_20Mem) h0Block9_21Mem) h0Block9_22Mem) h0Block9_23Mem) h0Block9_24Mem)
def h0Block10_0Specs : List PoolSpec := [(15,[]),(9,[]),(11,[]),(5,[(0,0,1)]),(7,[]),(2,[]),(10,[]),(13,[]),(16,[]),(21,[]),(17,[]),(37,[]),(15,[(3,2,3)]),(8,[]),(5,[]),(23,[]),(51,[]),(14,[]),(1,[(0,0,1),(3,2,3)]),(4,[(3,2,3)]),(1,[(0,0,1),(3,2,5)]),(0,[(0,0,1),(3,2,5)]),(3,[]),(4,[]),(3,[(3,2,5)]),(5,[(1,0,1)]),(12,[]),(4,[(3,2,5)]),(2,[(1,0,1)]),(1,[(1,0,1),(3,2,3)]),(2,[(1,0,1),(3,2,3)]),(0,[(1,0,1),(3,2,5)]),(0,[(2,0,1)]),(5,[(2,0,1)]),(1,[(2,0,1),(3,2,3)]),(0,[(2,0,1),(3,2,4)]),(2,[(2,0,1),(3,2,4)]),(0,[(2,0,1),(3,2,5)]),(1,[(2,0,1),(3,2,5)]),(5,[(0,0,4)]),(0,[(0,0,4)]),(1,[(3,2,3)]),(5,[(0,3,4)]),(2,[(0,3,4),(3,2,22)]),(2,[(0,3,4),(2,2,22)]),(2,[(0,3,4)])]
def h0Block10_0Pools : BT (Option BoundPool) := buildPoolsBT 6 h0W h0R h0Slices h0Block10_0Specs
def h0Block10_0 : List NodeSpec := [([300,0,1,2,3,4,5],[0,1,4,14,17,23],[4,5]),([65,0,1,2,3,4,5],[1,2,4,17,22,23,44],[0,1,2,4]),([81,0,1,2,3,4,5],[1,2,4,14,17,22,23,45],[0,1,2,3,4,5]),([66,0,1,2,22,3,4,5],[1,2,6,7,9,11,13,15,17,26,42,43],[0,1,4]),([19,123,0,1,2,3,4,5],[1,6,10,12,13,19,32,33,34],[0]),([19,6,0,1,2,3,4,5],[1,3,6,10,12,13,18,19],[0,2]),([19,225,0,1,2,3,4,5],[1,6,10,12,13,26,39,40,41],[0,1]),([19,0,1,89,2,3,4,5],[6,13,19,25,29,30],[0,2]),([23,123,0,1,2,3,4,5],[2,7,26,33,35,36],[0]),([25,123,0,1,2,3,4,5],[0,27,33,37,38],[0]),([25,6,0,1,2,3,4,5],[0,3,5,8,20,21],[0,2]),([25,0,1,89,2,3,4,5],[0,7,8,16,24,25,26,28,31],[0,2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block10_0Ok : checkNodesBT h0W h0G h0Mask h0Block10_0Pools h0Autos h0Bucket9 10 h0Block10_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block10_0Mem : ∀ ns ∈ h0Block10_0, Impossible h0G 10 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket9Ok h0Block10_0Ok
def h0Block10_1Specs : List PoolSpec := [(15,[]),(9,[]),(11,[]),(7,[]),(20,[]),(10,[]),(13,[]),(16,[]),(21,[]),(17,[]),(37,[]),(32,[]),(22,[]),(8,[]),(15,[(0,2,3)]),(44,[]),(51,[]),(4,[(0,2,3)]),(14,[]),(18,[]),(3,[]),(12,[]),(30,[]),(4,[(0,3,5)]),(4,[(0,2,5)]),(19,[]),(0,[(2,0,1)]),(13,[(2,0,1)]),(5,[(2,0,1)]),(14,[(2,0,1)]),(2,[(2,0,1),(0,2,4)]),(0,[(2,0,1),(0,2,5)]),(2,[(2,0,1),(0,3,4)]),(1,[(2,0,1),(0,3,5)]),(0,[(2,0,1),(0,4,5)]),(19,[(2,0,1)]),(4,[(0,0,3)]),(5,[(0,0,3)]),(0,[(3,1,4)]),(2,[(0,0,3),(3,1,4)]),(0,[(3,1,5)]),(3,[(3,1,5)]),(1,[(3,0,3)]),(4,[(3,0,3)]),(3,[(3,1,4)]),(2,[(3,0,3),(3,1,4)]),(5,[(3,0,3)]),(2,[(3,0,3)]),(1,[(3,0,3),(3,1,5)]),(5,[(0,0,4)]),(15,[(3,1,3)]),(0,[(0,0,4)]),(2,[(3,0,4)]),(2,[(3,0,4),(3,1,3)]),(5,[(3,0,4)]),(0,[(3,0,4),(3,1,5)])]
def h0Block10_1Pools : BT (Option BoundPool) := buildPoolsBT 6 h0W h0R h0Slices h0Block10_1Specs
def h0Block10_1 : List NodeSpec := [([123,0,1,36,2,3,4,5],[1,2,3,9,13,14,17,20,26,27,28],[0]),([123,0,1,18,2,3,4,5],[2,5,11,13,21,22,28,30],[0]),([123,0,1,24,2,3,4,5],[0,2,3,9,22,24,27,28,31],[0]),([123,0,1,2,22,3,4,5],[2,5,8,10,18,21,26,28,29,32],[0]),([123,0,1,2,83,3,4,5],[0,1,5,9,10,12,15,19,23,28,33],[0]),([123,0,1,2,3,27,4,5],[0,2,4,6,9,16,21,25,28,34,35],[0]),([243,286,0,1,2,3,4,5],[1,5,6,13,21,53,54],[0,2,3]),([243,225,0,1,2,3,4,5],[1,5,6,7,13,21,49,50,51],[0,3]),([191,197,0,1,2,3,4,5],[5,6,18,38,42,43,44,45,46],[0,1,3,4]),([191,171,0,1,2,3,4,5],[2,5,6,13,36,37,38,39],[0,1]),([185,197,0,1,2,3,4,5],[5,7,9,10,19,40,41,43,46,47,48],[0,1]),([185,286,0,1,2,3,4,5],[2,6,9,21,41,52,54,55],[0,3,4])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block10_1Ok : checkNodesBT h0W h0G h0Mask h0Block10_1Pools h0Autos h0Bucket9 10 h0Block10_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block10_1Mem : ∀ ns ∈ h0Block10_1, Impossible h0G 10 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket9Ok h0Block10_1Ok
def h0Block10_2Specs : List PoolSpec := [(15,[]),(9,[]),(11,[]),(7,[]),(0,[]),(20,[]),(10,[]),(13,[]),(16,[]),(21,[]),(48,[]),(17,[]),(37,[]),(22,[]),(54,[]),(8,[]),(5,[]),(35,[]),(45,[]),(14,[]),(18,[]),(4,[]),(12,[]),(33,[]),(19,[]),(4,[(0,0,3)]),(5,[(0,0,3)]),(0,[(3,1,5)]),(1,[(0,0,3),(3,1,5)]),(0,[(0,4,5)]),(3,[(0,1,5)]),(3,[(0,4,5)]),(1,[(3,0,3)]),(4,[(3,0,3)]),(5,[(3,0,3)]),(1,[(3,0,3),(0,1,5)]),(2,[(3,0,3)]),(5,[(0,0,4)]),(9,[(0,0,4)]),(1,[(3,225,1)]),(3,[(3,225,1)]),(0,[(0,0,4),(3,225,2)]),(3,[(3,225,2)]),(0,[(0,0,4)]),(0,[(0,0,4),(3,1,5)]),(1,[(3,225,3)]),(5,[(0,3,4)])]
def h0Block10_2Pools : BT (Option BoundPool) := buildPoolsBT 6 h0W h0R h0Slices h0Block10_2Specs
def h0Block10_2 : List NodeSpec := [([185,171,0,1,2,3,4,5],[0,6,11,15,25,26,27,28],[0,1]),([185,225,0,1,2,3,4,5],[0,7,8,11,22,37,44],[0,3]),([235,225,0,1,2,3,4,5],[0,2,7,15,22,23,37,38],[0,4]),([235,0,1,2,3,4,5],[0,1,3,8,16,39,40],[4]),([172,0,1,2,3,4,5],[2,3,8,15,16],[0]),([229,225,0,1,2,3,4,5],[0,2,7,16,22,41],[0]),([229,0,1,2,3,4,5],[0,1,6,7,21,42],[0]),([298,0,1,2,22,3,4,5],[1,2,6,9,10,12,13,15,19,20,22,46],[0,4]),([197,0,184,1,2,3,4,5],[1,4,6,11,30,34,35,36],[0,1]),([197,0,1,2,3,27,4,5],[1,5,6,7,8,11,14,18,20,22,24,29,31,32,33,34],[0,1,4,5]),([231,225,0,1,2,3,4,5],[0,2,7,17,22,23,37,43],[0,4]),([231,0,1,2,3,4,5],[0,1,3,13,15,16,21,43,45],[0,3,4,5])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block10_2Ok : checkNodesBT h0W h0G h0Mask h0Block10_2Pools h0Autos h0Bucket9 10 h0Block10_2 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block10_2Mem : ∀ ns ∈ h0Block10_2, Impossible h0G 10 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket9Ok h0Block10_2Ok
def h0Block10_3Specs : List PoolSpec := [(15,[]),(9,[]),(11,[]),(5,[(0,0,1)]),(7,[]),(0,[]),(1,[]),(2,[]),(20,[]),(10,[]),(13,[]),(16,[]),(3,[(3,6,2)]),(17,[]),(10,[(0,0,1)]),(29,[]),(8,[]),(5,[]),(15,[(0,2,3)]),(13,[(0,0,1)]),(45,[]),(4,[(0,2,3)]),(4,[]),(12,[]),(0,[(0,0,4),(3,225,5)]),(1,[(3,225,5)]),(1,[(0,3,5)]),(2,[(3,0,4)]),(5,[(3,0,4)]),(18,[(3,0,4)])]
def h0Block10_3Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block10_3Specs
def h0Block10_3 : List NodeSpec := [([286,0,1,2,83,3,4,5],[1,2,8,9,10,13,16,20,23,26,27,28,29],[0,2,4,5]),([261,0,1,2,3,4,5],[0,1,4,17,22,24,25],[0,3,4,5]),([183,0,1,2,3,4,5],[0,2,16],[0,4,5]),([8,6,0,1,2,3,4,5],[0,1,2,3],[]),([8,0,1,2,3,4,5],[0,3,9,10,11,12],[0]),([15,0,1,2,3,4,5],[0,1,2,4,13,16],[0]),([34,0,1,2,3,4,5],[0,1,2,4,11,17],[0,2]),([9,0,1,2,3,4,5],[0,1,2,4,5,6,7],[0,2,3]),([14,0,1,2,3,4,5],[1,2,3,4,11],[]),([30,0,1,2,3,4,5],[0,1,2,4,5,6,17],[0,2]),([6,0,1,36,2,3,4,5],[1,2,3,4,13,15,16,18,19,21],[0,2]),([6,0,1,24,2,3,4,5],[0,2,3,4,11,13,14,16,19],[0,2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block10_3Ok : checkNodesBT h0W h0G h0Mask h0Block10_3Pools h0Autos h0Bucket9 10 h0Block10_3 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block10_3Mem : ∀ ns ∈ h0Block10_3, Impossible h0G 10 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket9Ok h0Block10_3Ok
def h0Block10_4Specs : List PoolSpec := [(15,[]),(9,[]),(11,[]),(5,[(0,0,1)]),(7,[]),(20,[]),(10,[]),(13,[]),(16,[]),(21,[]),(48,[]),(17,[]),(37,[]),(22,[]),(8,[]),(5,[]),(35,[]),(14,[]),(36,[]),(18,[]),(2,[(0,0,1),(0,3,4)]),(1,[(0,0,1),(0,3,5)]),(18,[(0,0,1)]),(3,[]),(4,[]),(12,[]),(4,[(0,0,3)]),(0,[(0,171,4)]),(2,[(0,0,3),(0,1,4)]),(5,[(0,0,3)]),(1,[(0,0,3),(0,1,5)]),(0,[(0,4,5)]),(19,[(0,0,3)]),(1,[(3,0,3),(3,197,1)]),(2,[(3,0,4),(3,286,2)]),(5,[(0,3,4)])]
def h0Block10_4Pools : BT (Option BoundPool) := buildPoolsBT 6 h0W h0R h0Slices h0Block10_4Specs
def h0Block10_4 : List NodeSpec := [([6,0,1,2,7,3,4,5],[0,1,2,3,4],[]),([6,0,1,2,22,3,4,5],[1,2,3,6,9,16,17,20],[0,2]),([6,0,1,2,83,3,4,5],[0,1,3,5,6,11,19,21,22],[0,2]),([6,0,1,2,3,4,5],[0,1,2,4,15],[]),([287,0,1,2,3,4,5],[1,2,4,8,15],[]),([198,0,1,2,3,4,5],[1,4,8,15,23,33],[0]),([288,0,1,2,3,4,5],[1,2,6,24,34],[0,4]),([178,0,1,2,22,3,4,5],[1,2,6,9,10,12,13,14,17,19,25,35],[0,4]),([178,0,1,2,3,4,5],[0,1,2,4,15,24,27],[4,5]),([171,0,188,1,2,3,4,5],[1,2,6,7,14,28,29],[0,1,4]),([171,0,184,1,2,3,4,5],[0,1,6,11,14,29,30],[0,1]),([171,0,1,2,3,27,4,5],[0,1,2,5,6,7,8,11,14,18,25,26,29,31,32],[4,5])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block10_4Ok : checkNodesBT h0W h0G h0Mask h0Block10_4Pools h0Autos h0Bucket9 10 h0Block10_4 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block10_4Mem : ∀ ns ∈ h0Block10_4, Impossible h0G 10 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket9Ok h0Block10_4Ok
def h0Block10_5Specs : List PoolSpec := [(15,[]),(9,[]),(11,[]),(7,[]),(1,[]),(2,[]),(20,[]),(10,[]),(13,[]),(21,[]),(17,[]),(22,[]),(8,[]),(5,[]),(18,[]),(3,[]),(4,[]),(12,[]),(39,[]),(33,[]),(19,[]),(0,[(2,0,1)]),(2,[(3,0,3),(3,197,4)]),(1,[(3,0,3)]),(0,[(3,197,4)]),(16,[(0,0,4)]),(5,[(0,0,4)]),(0,[(0,0,4),(1,225,1)]),(9,[(0,0,4)]),(0,[(0,0,4),(1,225,2)]),(15,[(0,1,3)]),(0,[(0,0,4)]),(0,[(0,0,4),(0,225,5)]),(1,[(0,1,3)]),(1,[(0,1,5)]),(0,[(0,0,4),(0,4,5)]),(1,[(0,3,5)]),(18,[(0,0,4)]),(2,[(3,0,4),(3,286,3)]),(2,[(3,0,4)])]
def h0Block10_5Pools : BT (Option BoundPool) := buildPoolsBT 6 h0W h0R h0Slices h0Block10_5Specs
def h0Block10_5 : List NodeSpec := [([290,0,1,2,3,4,5],[2,12,38],[0,3,4,5]),([258,0,1,2,3,4,5],[0,1,2,3,13,16,32],[0,1,4,5]),([225,0,240,1,2,3,4,5],[1,2,7,8,12,17,25,26,30,31,33],[0,2,3]),([225,0,184,1,2,3,4,5],[0,1,8,10,12,17,18,26,28,34],[0,2,4]),([225,0,1,226,2,3,4,5],[0,1,2,8,17,19,26,27],[0,4]),([225,0,1,2,227,3,4,5],[0,2,3,17,26,29],[0]),([225,0,1,2,83,3,4,5],[0,1,6,7,8,10,14,17,26,31,36,37],[0,2,4,5]),([225,0,1,2,3,27,5],[0,4,5,9,20,35],[0,2,3,4,5]),([0,291,1,2,3,4,5],[1,2,3,12,13,16,39],[0,2,3,4,5]),([0,203,1,2,3,4,5],[1,3,9,13,15,16,22,23,24],[0,3,4,5]),([0,1,124,2,3,4,5],[0,2,7,8,15,16],[0]),([0,1,126,2,3,4,5],[0,2,3,11,12,13,16,21],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block10_5Ok : checkNodesBT h0W h0G h0Mask h0Block10_5Pools h0Autos h0Bucket9 10 h0Block10_5 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block10_5Mem : ∀ ns ∈ h0Block10_5, Impossible h0G 10 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket9Ok h0Block10_5Ok
def h0Block10_6Specs : List PoolSpec := [(15,[]),(9,[]),(11,[]),(7,[]),(2,[]),(20,[]),(10,[]),(13,[]),(16,[]),(21,[]),(17,[]),(37,[]),(22,[]),(8,[]),(5,[]),(25,[]),(23,[]),(51,[]),(4,[(0,2,3)]),(14,[]),(18,[]),(3,[]),(4,[]),(5,[(1,0,1)]),(12,[]),(34,[]),(4,[(0,3,5)]),(2,[(1,0,1),(0,89,3)]),(28,[]),(2,[(1,0,1),(0,2,3)]),(4,[(0,2,5)]),(2,[(1,0,1),(0,3,4)]),(2,[(1,0,1)]),(13,[(1,0,1)]),(1,[(1,0,1),(0,2,3)]),(14,[(1,0,1)]),(3,[(0,2,5)]),(18,[(1,0,1)]),(1,[(1,0,1),(0,3,5)]),(19,[]),(0,[(2,0,1),(3,123,4)]),(0,[(2,0,1),(3,123,5)]),(5,[(0,3,4)]),(2,[(0,3,4),(0,2,22)]),(2,[(0,3,4)]),(0,[(0,22,5)])]
def h0Block10_6Pools : BT (Option BoundPool) := buildPoolsBT 6 h0W h0R h0Slices h0Block10_6Specs
def h0Block10_6 : List NodeSpec := [([0,1,135,2,3,4,5],[0,2,3,14,22,40],[0]),([0,1,137,2,3,4,5],[0,2,3,14,22,41],[0]),([0,1,90,2,3,4,5],[4,6,7,21,22],[0]),([0,1,92,2,3,4,5],[3,13,14,22,24,27],[0]),([0,1,96,2,3,4,5],[3,5,13,14,21,22,24,32],[0,2]),([0,1,89,36,2,3,4,5],[6,13,14,18,23,25,29,34],[0,2]),([0,1,89,24,2,3,4,5],[2,6,10,13,23,28,30,32,33,36],[0,2]),([0,1,89,2,22,3,4,5],[6,9,13,16,19,23,24,31,35],[0,2]),([0,1,89,2,83,3,4,5],[5,6,8,10,13,17,20,23,26,37,38],[0,2]),([0,1,37,2,22,3,4,5],[1,2,6,9,11,13,14,16,19,24,43],[0,1,2,4]),([0,1,2,70,22,3,4,5],[1,2,6,9,11,12,13,15,16,19,20,24,39,42,44],[0,1,4]),([0,1,2,70,3,4,5],[1,2,3,9,14,19,20,21,22,39,44,45],[0,1,2,3,4,5])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block10_6Ok : checkNodesBT h0W h0G h0Mask h0Block10_6Pools h0Autos h0Bucket9 10 h0Block10_6 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block10_6Mem : ∀ ns ∈ h0Block10_6, Impossible h0G 10 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket9Ok h0Block10_6Ok
def h0Nodes10 : List NodeSpec := h0Block10_0 ++ h0Block10_1 ++ h0Block10_2 ++ h0Block10_3 ++ h0Block10_4 ++ h0Block10_5 ++ h0Block10_6
def h0Bucket10 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes10
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket10Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 10 xs.toFinset) h0Bucket10 := buildBucketsBT_of_mem (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append h0Block10_0Mem h0Block10_1Mem) h0Block10_2Mem) h0Block10_3Mem) h0Block10_4Mem) h0Block10_5Mem) h0Block10_6Mem)
def h0Block11_0Specs : List PoolSpec := [(15,[]),(9,[]),(11,[]),(0,[]),(1,[]),(2,[]),(8,[]),(5,[]),(14,[]),(3,[]),(4,[]),(2,[(0,0,1)]),(2,[(1,0,1)]),(0,[(1,0,1)]),(1,[(1,0,1)]),(0,[(2,0,1)]),(2,[(2,0,1)]),(2,[(0,0,3)]),(1,[(3,0,3)]),(2,[(3,0,3)]),(0,[(0,0,4)]),(2,[(3,0,4)]),(0,[(3,0,4)]),(2,[(0,3,4)])]
def h0Block11_0Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Block11_0Specs
def h0Block11_0 : List NodeSpec := [([123,0,1,2,3,4,5],[2,4,7,9,10,15,16],[0]),([197,0,1,2,3,4,5],[3,7,9,10,18,19],[0,1,2,3,4,5]),([286,0,1,2,3,4,5],[4,7,9,10,21,22],[0,2,3,4,5]),([6,0,1,2,3,4,5],[0,1,2,3,4,7,9,10,11],[0,2]),([171,0,1,2,3,4,5],[2,3,4,6,7,9,10,17],[0,1,4,5]),([225,0,1,2,3,4,5],[0,4,5,7,9,10,20],[0,1,2,3,4,5]),([0,1,89,2,3,4,5],[7,9,10,12,13,14],[0,2]),([0,1,2,22,3,4,5],[3,4,7,8,9,10,23],[0,1,2,3,4,5])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block11_0Ok : checkNodesBT h0W h0G h0Mask h0Block11_0Pools h0Autos h0Bucket10 11 h0Block11_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Block11_0Mem : ∀ ns ∈ h0Block11_0, Impossible h0G 11 (nodeValsBT h0W ns).toFinset := checkNodesBT_mem (by decide) h0Pairs h0WOk (buildPoolsBT_sound h0SlicesOk) h0AutosOk h0Bucket10Ok h0Block11_0Ok
def h0Nodes11 : List NodeSpec := h0Block11_0
def h0Bucket11 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes11
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket11Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 11 xs.toFinset) h0Bucket11 := buildBucketsBT_of_mem h0Block11_0Mem
def h0Block12_0Specs : List PoolSpec := [(0,[]),(1,[]),(2,[])]
def h0Block12_0Pools : BT (Option BoundPool) := buildPoolsBT 2 h0W h0R h0Slices h0Block12_0Specs
def h0Block12_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2],[0,1,2,3,4,5])]
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
lemma lifted : Lower h0R h0G 13 := lower_of_forestBT (essPairs := [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,6,14),(VAR 4,5,21),(VAR 5,3,35)]) (by decide +kernel) h0Bucket12Ok (by decide +kernel)
def wit : List PEqualNP.CircuitLowerBounds.Gate := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [17, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 12]⟩]
def wo : Nat := 19
lemma wit_mono : PEqualNP.MetaComplexity.Monotone2 ⟨wit, wo⟩ := by simp [PEqualNP.MetaComplexity.Monotone2, wit]
set_option maxRecDepth 100000 in set_option maxHeartbeats 0 in
lemma wit_eval : ∀ r : Row, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput6 r)) = ((4276676744 * 2 ^ 32 + 3902849152) ||| ((4276676744 * 2 ^ 32 + 3902849152) <<< 64)).testBit r.val := by decide +kernel
lemma low_root : Lower (varsOf 63) ((4276676744 * 2 ^ 32 + 3902849152) ||| ((4276676744 * 2 ^ 32 + 3902849152) <<< 64)) 13 := lifted
end PEqualNP.Outside.L_meta_49123
theorem PEqualNP.Outside.L_meta_49123 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676744 * 2 ^ 32 + 3902849152) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676744 * 2 ^ 32 + 3902849152) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hcs
  exact PEqualNP.Outside.L_meta_49123.table2_of_lower (4276676744 * 2 ^ 32 + 3902849152) (by decide) (by decide) (by decide) (by decide)
    13 PEqualNP.Outside.L_meta_49123.low_root
    PEqualNP.Outside.L_meta_49123.wit PEqualNP.Outside.L_meta_49123.wo (by decide)
    PEqualNP.Outside.L_meta_49123.wit_mono PEqualNP.Outside.L_meta_49123.wit_eval s hcs
