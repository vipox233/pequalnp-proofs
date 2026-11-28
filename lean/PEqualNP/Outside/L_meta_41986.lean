import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_41986
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
lemma faithful_zero (pos neg : List Nat) : faithful pos neg (0, 0, 0) := by
  constructor
  · apply Nat.eq_of_testBit_eq; intro i; rw [testBit_projBits]; cases pos[i]? <;> simp
  · apply Nat.eq_of_testBit_eq; intro i; rw [testBit_projBits]; cases neg[i]? <;> simp
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
lemma forall_cons {α : Type} {P : α → Prop} {a : α} {l : List α} (ha : P a) (hl : ∀ x ∈ l, P x) :
    ∀ x ∈ a :: l, P x := by
  intro x hx; rcases List.mem_cons.mp hx with rfl | hx; exact ha; exact hl x hx
lemma array_forall_of_list {α : Type} {P : α → Prop} {l : List α} (h : ∀ x ∈ l, P x) :
    ∀ i (hi : i < l.toArray.size), P l.toArray[i] :=
  fun i hi => h l.toArray[i] (Array.getElem_mem_toList hi)
abbrev PoolSpec := Nat × List (Nat × Nat × Nat)
abbrev NodeSpec := List Nat × List Nat × List Nat
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
def h1R : List Nat := varsOf 28
def h1G : Nat := 0xfff0f000fff0f000fff0f000fff0f000
def h1Pos : List Nat := [20,24,12,12,24,20]
def h1Neg : List Nat := [16,16,4,8,8,4]
def h1Mask : Nat := fullMask 6
def h1Base : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,45,36),(0xff00ff00ff00ff00ff00ff00ff00ff00,30,24),(0xffff0000ffff0000ffff0000ffff0000,51,3)]
def h1Steps : List (Nat × Nat × Nat) := []
def h1W : Array Decor := buildWires h1Base h1Steps
def h1Autos : Array (List (Nat × Nat)) := #[[]]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Pairs : goodPairs h1G h1Pos h1Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1BaseOk : ∀ x ∈ h1Base, faithful h1Pos h1Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1WOk : ∀ x ∈ h1W.toList, faithful h1Pos h1Neg x ∧ x.1 < 2^128 := buildWires_faithful h1BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1AutosOk : ∀ sw ∈ h1Autos.toList, swapsValid sw = true ∧ permWord sw h1G = h1G := autos_of (by decide +kernel)
def h1SliceList : List (Nat × Nat) := []
def h1Slices : Array (Nat × Nat) := h1SliceList.toArray
def h1Specs : List PoolSpec := []
def h1Pools : Array (Option BoundPool) := buildPools h1W h1R h1Slices h1Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1SlicesOk : ∀ i (hi : i < h1Slices.size), Slice h1R h1G h1Slices[i].1 h1Slices[i].2 := array_forall_of_list (P := fun (p : Nat × Nat) => Slice h1R h1G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1PoolsOk : ∀ i (hi : i < h1Pools.size), ∀ c, h1Pools[i] = some c → ValidPool h1R h1G c := buildPools_sound h1SlicesOk
def h1Empty : Array (List (List Nat)) := #[]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1EmptyOk : ∀ i (hi : i < h1Empty.size), ∀ xs ∈ h1Empty[i], Impossible h1G (3 - 1) xs.toFinset := by intro i hi; simp [h1Empty] at hi
def h1Block3_0 : List NodeSpec := [([0,1,2],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test3_0 : checkNodes h1W h1G h1Mask h1Pools h1Autos h1Empty 3 h1Block3_0 = true := by decide +kernel
def h1Nodes3 : List NodeSpec := h1Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Check3 : checkNodes h1W h1G h1Mask h1Pools h1Autos h1Empty 3 h1Nodes3 = true := h1Test3_0
def h1Bucket3 : Array (List (List Nat)) := buildBuckets 1 h1W h1Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Bucket3Ok : ∀ i (hi : i < h1Bucket3.size), ∀ xs ∈ h1Bucket3[i], Impossible h1G 3 xs.toFinset := buildBuckets_sound (by decide) h1Pairs h1WOk h1PoolsOk h1AutosOk h1EmptyOk h1Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Bound : Lower h1R h1G 4 := lower_of_forest (essPairs := [(VAR 2,8,12),(VAR 3,4,12),(VAR 4,4,20)]) (by decide +kernel) h1Bucket3Ok (by decide +kernel)
def h3R : List Nat := varsOf 14
def h3G : Nat := 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0
def h3Pos : List Nat := [10,12,6,6,12,10]
def h3Neg : List Nat := [8,8,2,4,4,2]
def h3Mask : Nat := fullMask 6
def h3Base : List Decor := [(0xcccccccccccccccccccccccccccccccc,45,36),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,30,24),(0xff00ff00ff00ff00ff00ff00ff00ff00,51,3)]
def h3Steps : List (Nat × Nat × Nat) := []
def h3W : Array Decor := buildWires h3Base h3Steps
def h3Autos : Array (List (Nat × Nat)) := #[[]]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Pairs : goodPairs h3G h3Pos h3Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3BaseOk : ∀ x ∈ h3Base, faithful h3Pos h3Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3WOk : ∀ x ∈ h3W.toList, faithful h3Pos h3Neg x ∧ x.1 < 2^128 := buildWires_faithful h3BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3AutosOk : ∀ sw ∈ h3Autos.toList, swapsValid sw = true ∧ permWord sw h3G = h3G := autos_of (by decide +kernel)
def h3SliceList : List (Nat × Nat) := []
def h3Slices : Array (Nat × Nat) := h3SliceList.toArray
def h3Specs : List PoolSpec := []
def h3Pools : Array (Option BoundPool) := buildPools h3W h3R h3Slices h3Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3SlicesOk : ∀ i (hi : i < h3Slices.size), Slice h3R h3G h3Slices[i].1 h3Slices[i].2 := array_forall_of_list (P := fun (p : Nat × Nat) => Slice h3R h3G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3PoolsOk : ∀ i (hi : i < h3Pools.size), ∀ c, h3Pools[i] = some c → ValidPool h3R h3G c := buildPools_sound h3SlicesOk
def h3Empty : Array (List (List Nat)) := #[]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3EmptyOk : ∀ i (hi : i < h3Empty.size), ∀ xs ∈ h3Empty[i], Impossible h3G (3 - 1) xs.toFinset := by intro i hi; simp [h3Empty] at hi
def h3Block3_0 : List NodeSpec := [([0,1,2],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Test3_0 : checkNodes h3W h3G h3Mask h3Pools h3Autos h3Empty 3 h3Block3_0 = true := by decide +kernel
def h3Nodes3 : List NodeSpec := h3Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Check3 : checkNodes h3W h3G h3Mask h3Pools h3Autos h3Empty 3 h3Nodes3 = true := h3Test3_0
def h3Bucket3 : Array (List (List Nat)) := buildBuckets 1 h3W h3Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Bucket3Ok : ∀ i (hi : i < h3Bucket3.size), ∀ xs ∈ h3Bucket3[i], Impossible h3G 3 xs.toFinset := buildBuckets_sound (by decide) h3Pairs h3WOk h3PoolsOk h3AutosOk h3EmptyOk h3Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Bound : Lower h3R h3G 4 := lower_of_forest (essPairs := [(VAR 1,4,6),(VAR 2,2,6),(VAR 3,2,10)]) (by decide +kernel) h3Bucket3Ok (by decide +kernel)
def h2R : List Nat := varsOf 30
def h2G : Nat := 0xfcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h2Bound : Lower h2R h2G 5 := lift_of (z := 0) (o := 16) (essPairs := [(VAR 4,12,28)]) (by decide +kernel) h3Bound
namespace Cofactor12319
def G_0 : Nat := 0xfcfcfcfcc0c0c0c0fcfcfcfcc0c0c0c0
def R_0 : List Nat := varsOf 38
def pos_0 : List Nat := [6,6,34,34,36,36,6,34,36]
def neg_0 : List Nat := [4,2,32,2,32,4,32,4,2]
def fmask_0 : Nat := fullMask 9
def base_0 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xcf,0x10a),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x173,0xa1),(0xffffffff00000000ffffffff00000000,0x1bc,0x54)]
def steps_0 : List (Nat × Nat × Nat) := []
def W_0 : Array Decor := buildWires base_0 steps_0
def autos_0 : Array (List (Nat × Nat)) := #[]
def slicesL_0 : List (Nat × Nat) := []
def slices_0 : Array (Nat × Nat) := slicesL_0.toArray
def ps_0 : List PoolSpec := []
def P_0 : Array (Option BoundPool) := buildPools W_0 R_0 slices_0 ps_0
lemma gp_0 : goodPairs G_0 pos_0 neg_0 := goodPairs_of (by decide +kernel)
lemma base_0_ok : ∀ x ∈ base_0, faithful pos_0 neg_0 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma W_0_ok : ∀ x ∈ W_0.toList, faithful pos_0 neg_0 x ∧ x.1 < 2^128 := buildWires_faithful base_0_ok
lemma autos_0_ok : ∀ sw ∈ autos_0.toList, swapsValid sw = true ∧ permWord sw G_0 = G_0 := autos_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma slices_0_ok : ∀ i (hi : i < slices_0.size), Slice R_0 G_0 slices_0[i].1 slices_0[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice R_0 G_0 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma P_0_ok : ∀ i (hi : i < P_0.size), ∀ c, P_0[i] = some c → ValidPool R_0 G_0 c := buildPools_sound slices_0_ok
def bk_0_init : Array (List (List Nat)) := #[]
lemma bk_0_init_ok : ∀ i (hi : i < bk_0_init.size), ∀ xs ∈ bk_0_init[i], Impossible G_0 (0 - 1) xs.toFinset := by intro i hi; simp [bk_0_init] at hi
def nodes_0_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_0 : checkNodes W_0 G_0 fmask_0 P_0 autos_0 bk_0_init 0 nodes_0_0 = true := by decide +kernel
def bk_0_0 : Array (List (List Nat)) := buildBuckets 1 W_0 nodes_0_0
lemma bk_0_0_ok : ∀ i (hi : i < bk_0_0.size), ∀ xs ∈ bk_0_0[i], Impossible G_0 0 xs.toFinset :=
  buildBuckets_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_init_ok chk_0_0
def nodes_0_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_1 : checkNodes W_0 G_0 fmask_0 P_0 autos_0 bk_0_0 1 nodes_0_1 = true := by decide +kernel
def bk_0_1 : Array (List (List Nat)) := buildBuckets 1 W_0 nodes_0_1
lemma bk_0_1_ok : ∀ i (hi : i < bk_0_1.size), ∀ xs ∈ bk_0_1[i], Impossible G_0 1 xs.toFinset :=
  buildBuckets_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_0_ok chk_0_1
def nodes_0_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_2 : checkNodes W_0 G_0 fmask_0 P_0 autos_0 bk_0_1 2 nodes_0_2 = true := by decide +kernel
def bk_0_2 : Array (List (List Nat)) := buildBuckets 1 W_0 nodes_0_2
lemma bk_0_2_ok : ∀ i (hi : i < bk_0_2.size), ∀ xs ∈ bk_0_2[i], Impossible G_0 2 xs.toFinset :=
  buildBuckets_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_1_ok chk_0_2
def nodes_0_3 : List NodeSpec := [([0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_3 : checkNodes W_0 G_0 fmask_0 P_0 autos_0 bk_0_2 3 nodes_0_3 = true := by decide +kernel
def bk_0_3 : Array (List (List Nat)) := buildBuckets 1 W_0 nodes_0_3
lemma bk_0_3_ok : ∀ i (hi : i < bk_0_3.size), ∀ xs ∈ bk_0_3[i], Impossible G_0 3 xs.toFinset :=
  buildBuckets_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_2_ok chk_0_3
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma root_0_ok : forestRootCheck R_0 G_0 [(VAR 1,6,4),(VAR 2,6,2),(VAR 5,34,2)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma root_0_in : bucketContains bk_0_3 R_0 = true := by decide +kernel
lemma low_0 : Lower R_0 G_0 4 := lower_of_forest root_0_ok bk_0_3_ok root_0_in

def G_7 : Nat := 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0
def R_7 : List Nat := varsOf 14
lemma low_7_ok : carryOK [(3,4),(3,5)] R_7 G_7 R_0 G_0 = true := by decide +kernel
lemma low_7 : Lower R_7 G_7 4 := carry_of low_7_ok low_0

def G_8 : Nat := 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0
def R_8 : List Nat := varsOf 22
lemma low_8_ok : carryOK [(4,5)] R_8 G_8 R_0 G_0 = true := by decide +kernel
lemma low_8 : Lower R_8 G_8 4 := carry_of low_8_ok low_0

def G_9 : Nat := 0xfc00fc00c000c000fc00fc00c000c000
def R_9 : List Nat := varsOf 46
lemma low_9_ok : liftCheck 0 8 R_9 G_9 R_0 G_0 [(VAR 3,14,6)] = true := by decide +kernel
lemma low_9 : Lower R_9 G_9 5 := lift_of low_9_ok low_0

def G_10 : Nat := 0xfcc0fcc0fc00fc00fcc0fcc0fc00fc00
def R_10 : List Nat := varsOf 46
lemma low_10_ok : liftCheck 0 32 R_10 G_10 R_7 G_7 [(VAR 5,38,6)] = true := by decide +kernel
lemma low_10 : Lower R_10 G_10 5 := lift_of low_10_ok low_7

def G_11 : Nat := 0xfcfcfcfcfcfcc0c0fcfcfcfcfcfcc0c0
def R_11 : List Nat := varsOf 54
lemma low_11_ok : liftCheck 16 0 R_11 G_11 R_0 G_0 [(VAR 4,18,2)] = true := by decide +kernel
lemma low_11 : Lower R_11 G_11 5 := lift_of low_11_ok low_0

def G_13 : Nat := 0xfff0ff00ff00f000fff0ff00ff00f000
def R_13 : List Nat := varsOf 60
def pos_13 : List Nat := [12,12,24,24,28,40,40,44,52,52,52,56,12,12,12,24,24,24,40,40,40,52]
def neg_13 : List Nat := [8,4,16,8,20,32,8,36,48,36,20,48,20,36,48,20,36,48,20,36,48,8]
def fmask_13 : Nat := fullMask 22
def base_13 : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x207793,0xdb692),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x1ff8ff,0x200049),(0xffff0000ffff0000ffff0000ffff0000,0x238f1c,0x16dd14),(0xffffffff00000000ffffffff00000000,0x3c0fe0,0x1b6ba0)]
def steps_13 : List (Nat × Nat × Nat) := [(2,0,2),(1,0,2),(2,0,1),(0,0,2),(3,0,1),(1,0,1),(0,0,1),(3,0,2),(3,4,3),(2,9,2),(0,9,2),(1,4,3),(3,10,2),(1,10,2),(3,7,5)]
def W_13 : Array Decor := buildWires base_13 steps_13
def autos_13 : Array (List (Nat × Nat)) := #[[],[(4,5)],[(2,4)],[(2,5),(2,4)],[(2,4),(2,5)],[(2,5)]]
def slicesL_13 : List (Nat × Nat) := []
def slices_13 : Array (Nat × Nat) := slicesL_13.toArray
def ps_13 : List PoolSpec := []
def P_13 : Array (Option BoundPool) := buildPools W_13 R_13 slices_13 ps_13
lemma gp_13 : goodPairs G_13 pos_13 neg_13 := goodPairs_of (by decide +kernel)
lemma base_13_ok : ∀ x ∈ base_13, faithful pos_13 neg_13 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma W_13_ok : ∀ x ∈ W_13.toList, faithful pos_13 neg_13 x ∧ x.1 < 2^128 := buildWires_faithful base_13_ok
lemma autos_13_ok : ∀ sw ∈ autos_13.toList, swapsValid sw = true ∧ permWord sw G_13 = G_13 := autos_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma slices_13_ok : ∀ i (hi : i < slices_13.size), Slice R_13 G_13 slices_13[i].1 slices_13[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice R_13 G_13 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma P_13_ok : ∀ i (hi : i < P_13.size), ∀ c, P_13[i] = some c → ValidPool R_13 G_13 c := buildPools_sound slices_13_ok
def bk_13_init : Array (List (List Nat)) := #[]
lemma bk_13_init_ok : ∀ i (hi : i < bk_13_init.size), ∀ xs ∈ bk_13_init[i], Impossible G_13 (0 - 1) xs.toFinset := by intro i hi; simp [bk_13_init] at hi
def nodes_13_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_13_0 : checkNodes W_13 G_13 fmask_13 P_13 autos_13 bk_13_init 0 nodes_13_0 = true := by decide +kernel
def bk_13_0 : Array (List (List Nat)) := buildBuckets 1 W_13 nodes_13_0
lemma bk_13_0_ok : ∀ i (hi : i < bk_13_0.size), ∀ xs ∈ bk_13_0[i], Impossible G_13 0 xs.toFinset :=
  buildBuckets_sound (by decide) gp_13 W_13_ok P_13_ok autos_13_ok bk_13_init_ok chk_13_0
def nodes_13_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_13_1 : checkNodes W_13 G_13 fmask_13 P_13 autos_13 bk_13_0 1 nodes_13_1 = true := by decide +kernel
def bk_13_1 : Array (List (List Nat)) := buildBuckets 1 W_13 nodes_13_1
lemma bk_13_1_ok : ∀ i (hi : i < bk_13_1.size), ∀ xs ∈ bk_13_1[i], Impossible G_13 1 xs.toFinset :=
  buildBuckets_sound (by decide) gp_13 W_13_ok P_13_ok autos_13_ok bk_13_0_ok chk_13_1
def nodes_13_2 : List NodeSpec := [([18,1,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_13_2 : checkNodes W_13 G_13 fmask_13 P_13 autos_13 bk_13_1 2 nodes_13_2 = true := by decide +kernel
def bk_13_2 : Array (List (List Nat)) := buildBuckets 1 W_13 nodes_13_2
lemma bk_13_2_ok : ∀ i (hi : i < bk_13_2.size), ∀ xs ∈ bk_13_2[i], Impossible G_13 2 xs.toFinset :=
  buildBuckets_sound (by decide) gp_13 W_13_ok P_13_ok autos_13_ok bk_13_1_ok chk_13_2
def nodes_13_3 : List NodeSpec := [([4,11,1,3],[],[0]),([0,1,2,12],[],[]),([7,1,5,3],[],[0]),([13,0,1,3],[],[]),([0,1,14,3],[],[]),([6,8,2,3],[],[]),([0,1,2,15],[],[]),([16,0,1,3],[],[]),([0,1,17,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_13_3 : checkNodes W_13 G_13 fmask_13 P_13 autos_13 bk_13_2 3 nodes_13_3 = true := by decide +kernel
def bk_13_3 : Array (List (List Nat)) := buildBuckets 4 W_13 nodes_13_3
lemma bk_13_3_ok : ∀ i (hi : i < bk_13_3.size), ∀ xs ∈ bk_13_3[i], Impossible G_13 3 xs.toFinset :=
  buildBuckets_sound (by decide) gp_13 W_13_ok P_13_ok autos_13_ok bk_13_2_ok chk_13_3
def nodes_13_4 : List NodeSpec := [([4,0,1,2,3],[],[0]),([0,1,2,5,3],[],[0]),([6,0,1,2,3],[],[0]),([7,0,1,2,3],[],[0]),([8,0,1,2,3],[],[0]),([0,1,9,2,3],[],[0,1]),([10,0,1,2,3],[],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_13_4 : checkNodes W_13 G_13 fmask_13 P_13 autos_13 bk_13_3 4 nodes_13_4 = true := by decide +kernel
def bk_13_4 : Array (List (List Nat)) := buildBuckets 3 W_13 nodes_13_4
lemma bk_13_4_ok : ∀ i (hi : i < bk_13_4.size), ∀ xs ∈ bk_13_4[i], Impossible G_13 4 xs.toFinset :=
  buildBuckets_sound (by decide) gp_13 W_13_ok P_13_ok autos_13_ok bk_13_3_ok chk_13_4
def nodes_13_5 : List NodeSpec := [([0,1,2,3],[],[0,2,1,3,4,5])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_13_5 : checkNodes W_13 G_13 fmask_13 P_13 autos_13 bk_13_4 5 nodes_13_5 = true := by decide +kernel
def bk_13_5 : Array (List (List Nat)) := buildBuckets 1 W_13 nodes_13_5
lemma bk_13_5_ok : ∀ i (hi : i < bk_13_5.size), ∀ xs ∈ bk_13_5[i], Impossible G_13 5 xs.toFinset :=
  buildBuckets_sound (by decide) gp_13 W_13_ok P_13_ok autos_13_ok bk_13_4_ok chk_13_5
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma root_13_ok : forestRootCheck R_13 G_13 [(VAR 2,12,8),(VAR 3,12,4),(VAR 4,24,8),(VAR 5,40,8)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma root_13_in : bucketContains bk_13_5 R_13 = true := by decide +kernel
lemma low_13 : Lower R_13 G_13 6 := lower_of_forest root_13_ok bk_13_5_ok root_13_in

def G_27 : Nat := 0xfc00c000fc00c000fc00c000fc00c000
def R_27 : List Nat := varsOf 30
lemma low_27_ok : carryOK [(4,5)] R_27 G_27 R_9 G_9 = true := by decide +kernel
lemma low_27 : Lower R_27 G_27 5 := carry_of low_27_ok low_9

def G_28 : Nat := 0xfcc0fc00fcc0fc00fcc0fc00fcc0fc00
def R_28 : List Nat := varsOf 30
lemma low_28_ok : carryOK [(4,5)] R_28 G_28 R_10 G_10 = true := by decide +kernel
lemma low_28 : Lower R_28 G_28 5 := carry_of low_28_ok low_10

def G_32 : Nat := 0xffccff00ff00cc00ffccff00ff00cc00
def R_32 : List Nat := varsOf 58
lemma low_32_ok : carryOK [(1,2)] R_32 G_32 R_13 G_13 = true := by decide +kernel
lemma low_32 : Lower R_32 G_32 6 := carry_of low_32_ok low_13

def G_34 : Nat := 0xfcc0fc00fc00c000fcc0fc00fc00c000
def R_34 : List Nat := varsOf 62
def pos_34 : List Nat := [14,14,14,26,26,26,28,28,28,30,42,42,42,44,44,44,46,54,54,54,54,58,58,60,60,14,14,14,14,14,26,26,26,26,26,26,28,28,28,28,28,28,42,42,42,42,42,42,44,44,44,44,44,44,54,54,54]
def neg_34 : List Nat := [12,10,6,24,18,10,24,20,12,22,40,34,10,40,36,12,38,52,50,38,22,56,50,56,52,22,38,50,52,56,12,22,38,50,52,56,10,22,38,50,52,56,12,22,38,50,52,56,10,22,38,50,52,56,10,12,56]
def fmask_34 : Nat := fullMask 57
def base_34 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0x1c0fc0ffe7f1e3f,0x4f38f38e5d1a36),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x1ff03f03f9fe3c7,0x965d65d71bc385),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x3fffffffe1ffff,0x1e1861860a0b56b),(0xffff0000ffff0000ffff0000ffff0000,0x1c003ffc1fe03f8,0x13aebaebbf602d8),(0xffffffff00000000ffffffff00000000,0x1fffc0001fffc00,0x13cf3cf3def6c00)]
def steps_34 : List (Nat × Nat × Nat) := [(1,3,4),(0,3,4),(3,2,3),(2,0,3),(0,2,3),(0,0,3),(2,0,2),(2,3,4),(0,0,1),(2,2,3),(1,2,3),(0,0,2),(0,2,5),(0,0,5),(0,15,4),(3,8,1),(0,0,15),(3,12,0),(3,9,4),(2,0,9),(3,13,2),(2,1,3),(3,8,2),(2,1,2),(3,7,0),(0,1,2),(0,1,4),(2,16,3),(1,13,3),(0,13,2),(3,16,1),(3,10,1),(3,3,4),(3,11,1),(1,13,2),(1,9,4),(1,16,3),(2,13,3),(3,13,3),(2,15,4),(0,13,3),(2,13,2),(2,0,17),(3,21,1),(3,29,1),(2,1,9),(3,22,1),(3,20,2),(1,10,31),(3,16,5),(1,28,16),(0,1,5),(0,16,5),(1,34,3),(3,34,0),(3,12,13),(3,13,5),(3,7,13),(3,46,0),(2,13,9),(3,18,2),(0,21,1),(3,26,0),(1,12,13),(1,13,9),(3,45,0),(3,26,16),(3,24,1),(3,42,4),(1,43,4),(1,26,16),(0,39,3),(1,42,4),(0,13,5),(1,7,13),(3,18,1),(3,43,4),(2,1,27),(2,39,3),(3,34,3),(3,6,5),(3,13,15),(3,57,1),(3,34,4),(3,45,33),(3,34,39),(2,0,31)]
def W_34 : Array Decor := buildWires base_34 steps_34
def autos_34 : Array (List (Nat × Nat)) := #[[],[(4,5),(1,2)],[(1,2)],[(4,5)]]
def slicesL_34 : List (Nat × Nat) := [(subcube 0 48,4),(subcube 0 2,6),(subcube 0 16,5),(subcube 0 4,6),(subcube 16 0,5),(subcube 32 0,5),(subcube 16 8,4),(subcube 32 8,4),(subcube 0 8,5),(subcube 0 32,5)]
def slices_34 : Array (Nat × Nat) := slicesL_34.toArray
def ps_34 : List PoolSpec := [(0,[]),(1,[(0,3,4),(1,3,4),(3,6,5)]),(1,[(0,13,3),(1,13,3),(3,45,33)]),(2,[]),(3,[(1,2,3),(0,0,15)]),(4,[]),(3,[(2,3,4),(3,12,0)]),(5,[]),(1,[]),(6,[]),(7,[]),(8,[]),(3,[]),(3,[(0,0,2),(1,34,3)]),(9,[]),(1,[(2,3,4),(3,12,13)]),(1,[(1,2,3),(2,15,4)]),(1,[(2,13,2),(3,13,2)]),(1,[(2,2,3),(3,2,3)]),(1,[(0,3,4),(1,3,4)]),(1,[(0,2,3),(1,9,4)]),(1,[(1,2,3),(0,15,4)]),(1,[(0,2,3),(3,9,4)]),(1,[(0,2,3),(2,13,9)]),(1,[(2,3,4),(1,12,13)]),(1,[(0,2,3),(1,13,9)]),(3,[(0,2,3),(2,0,9)]),(1,[(2,13,3),(3,42,4)]),(1,[(3,13,3),(1,43,4)]),(1,[(1,13,2),(0,39,3)]),(1,[(0,13,3),(1,13,3)]),(1,[(2,13,3),(1,42,4)]),(1,[(1,2,3),(0,13,15)]),(1,[(0,13,2),(1,34,3)]),(1,[(2,13,3),(3,13,3)]),(1,[(3,13,3),(3,43,4)]),(1,[(1,13,2),(2,39,3)]),(1,[(0,13,2),(3,34,3)]),(1,[(2,3,4),(3,3,4)]),(3,[(0,3,4),(1,3,4),(3,6,5)]),(1,[(1,2,3),(3,13,15)]),(1,[(1,3,4)]),(3,[(2,2,3),(3,2,3)]),(3,[(1,2,3),(0,15,4)]),(1,[(3,8,1)]),(3,[(2,0,3)]),(1,[(1,2,3)]),(1,[(2,3,4)]),(3,[(0,2,3),(3,9,4)]),(1,[(0,2,3)]),(1,[(3,13,2)]),(1,[(0,3,4)]),(3,[(0,0,2)]),(1,[(3,2,3)]),(1,[(1,13,3)]),(1,[(0,13,2)]),(3,[(0,3,4),(1,3,4)]),(1,[(0,1,2)]),(1,[(3,16,1)]),(1,[(3,10,1)]),(3,[(0,0,3)]),(3,[(2,3,4),(3,3,4)]),(1,[(3,11,1)]),(1,[(1,13,2)]),(3,[(0,2,3),(1,9,4)]),(1,[(2,13,3)]),(3,[(3,13,2)]),(1,[(3,13,3)]),(3,[(1,2,3),(2,15,4)]),(1,[(0,13,3)]),(3,[(0,13,2)]),(1,[(2,2,3)]),(1,[(2,13,2)]),(3,[(1,3,4)]),(3,[(0,3,4)]),(3,[(3,2,3)]),(3,[(0,2,3)]),(3,[(2,3,4)]),(3,[(2,2,3)]),(3,[(1,2,3)])]
def P_34 : Array (Option BoundPool) := buildPools W_34 R_34 slices_34 ps_34
lemma gp_34 : goodPairs G_34 pos_34 neg_34 := goodPairs_of (by decide +kernel)
lemma base_34_ok : ∀ x ∈ base_34, faithful pos_34 neg_34 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma W_34_ok : ∀ x ∈ W_34.toList, faithful pos_34 neg_34 x ∧ x.1 < 2^128 := buildWires_faithful base_34_ok
lemma autos_34_ok : ∀ sw ∈ autos_34.toList, swapsValid sw = true ∧ permWord sw G_34 = G_34 := autos_of (by decide +kernel)
lemma sl_34_0_ok : sliceDirectCheck 0 48 0 R_34 G_34 R_7 G_7 = true := by decide +kernel
lemma sl_34_0 : Slice R_34 G_34 (subcube 0 48) 4 := slice_direct sl_34_0_ok low_7
lemma sl_34_1_ok : sliceDirectCheck 0 2 0 R_34 G_34 R_13 G_13 = true := by decide +kernel
lemma sl_34_1 : Slice R_34 G_34 (subcube 0 2) 6 := slice_direct sl_34_1_ok low_13
lemma sl_34_2_ok : sliceDirectCheck 0 16 0 R_34 G_34 R_10 G_10 = true := by decide +kernel
lemma sl_34_2 : Slice R_34 G_34 (subcube 0 16) 5 := slice_direct sl_34_2_ok low_10
lemma sl_34_3_ok : sliceDirectCheck 0 4 0 R_34 G_34 R_32 G_32 = true := by decide +kernel
lemma sl_34_3 : Slice R_34 G_34 (subcube 0 4) 6 := slice_direct sl_34_3_ok low_32
lemma sl_34_4_ok : sliceDirectCheck 16 0 0 R_34 G_34 R_9 G_9 = true := by decide +kernel
lemma sl_34_4 : Slice R_34 G_34 (subcube 16 0) 5 := slice_direct sl_34_4_ok low_9
lemma sl_34_5_ok : sliceDirectCheck 32 0 0 R_34 G_34 R_27 G_27 = true := by decide +kernel
lemma sl_34_5 : Slice R_34 G_34 (subcube 32 0) 5 := slice_direct sl_34_5_ok low_27
lemma sl_34_6_ok : sliceDirectCheck 16 8 0 R_34 G_34 R_0 G_0 = true := by decide +kernel
lemma sl_34_6 : Slice R_34 G_34 (subcube 16 8) 4 := slice_direct sl_34_6_ok low_0
lemma sl_34_7_ok : sliceDirectCheck 32 8 0 R_34 G_34 R_8 G_8 = true := by decide +kernel
lemma sl_34_7 : Slice R_34 G_34 (subcube 32 8) 4 := slice_direct sl_34_7_ok low_8
lemma sl_34_8_ok : sliceDirectCheck 0 8 0 R_34 G_34 R_11 G_11 = true := by decide +kernel
lemma sl_34_8 : Slice R_34 G_34 (subcube 0 8) 5 := slice_direct sl_34_8_ok low_11
lemma sl_34_9_ok : sliceDirectCheck 0 32 0 R_34 G_34 R_28 G_28 = true := by decide +kernel
lemma sl_34_9 : Slice R_34 G_34 (subcube 0 32) 5 := slice_direct sl_34_9_ok low_28
set_option maxRecDepth 200000 in
lemma slices_34_ok : ∀ i (hi : i < slices_34.size), Slice R_34 G_34 slices_34[i].1 slices_34[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice R_34 G_34 p.1 p.2) (forall_cons sl_34_0 (forall_cons sl_34_1 (forall_cons sl_34_2 (forall_cons sl_34_3 (forall_cons sl_34_4 (forall_cons sl_34_5 (forall_cons sl_34_6 (forall_cons sl_34_7 (forall_cons sl_34_8 (forall_cons sl_34_9 (fun _ h => (List.not_mem_nil h).elim)))))))))))
lemma P_34_ok : ∀ i (hi : i < P_34.size), ∀ c, P_34[i] = some c → ValidPool R_34 G_34 c := buildPools_sound slices_34_ok
def bk_34_init : Array (List (List Nat)) := #[]
lemma bk_34_init_ok : ∀ i (hi : i < bk_34_init.size), ∀ xs ∈ bk_34_init[i], Impossible G_34 (0 - 1) xs.toFinset := by intro i hi; simp [bk_34_init] at hi
def nodes_34_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_34_0 : checkNodes W_34 G_34 fmask_34 P_34 autos_34 bk_34_init 0 nodes_34_0 = true := by decide +kernel
def bk_34_0 : Array (List (List Nat)) := buildBuckets 1 W_34 nodes_34_0
lemma bk_34_0_ok : ∀ i (hi : i < bk_34_0.size), ∀ xs ∈ bk_34_0[i], Impossible G_34 0 xs.toFinset :=
  buildBuckets_sound (by decide) gp_34 W_34_ok P_34_ok autos_34_ok bk_34_init_ok chk_34_0
def nodes_34_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_34_1 : checkNodes W_34 G_34 fmask_34 P_34 autos_34 bk_34_0 1 nodes_34_1 = true := by decide +kernel
def bk_34_1 : Array (List (List Nat)) := buildBuckets 1 W_34 nodes_34_1
lemma bk_34_1_ok : ∀ i (hi : i < bk_34_1.size), ∀ xs ∈ bk_34_1[i], Impossible G_34 1 xs.toFinset :=
  buildBuckets_sound (by decide) gp_34 W_34_ok P_34_ok autos_34_ok bk_34_0_ok chk_34_1
def nodes_34_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_34_2 : checkNodes W_34 G_34 fmask_34 P_34 autos_34 bk_34_1 2 nodes_34_2 = true := by decide +kernel
def bk_34_2 : Array (List (List Nat)) := buildBuckets 1 W_34 nodes_34_2
lemma bk_34_2_ok : ∀ i (hi : i < bk_34_2.size), ∀ xs ∈ bk_34_2[i], Impossible G_34 2 xs.toFinset :=
  buildBuckets_sound (by decide) gp_34 W_34_ok P_34_ok autos_34_ok bk_34_1_ok chk_34_2
def nodes_34_3 : List NodeSpec := [([91,36,2,5],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_34_3 : checkNodes W_34 G_34 fmask_34 P_34 autos_34 bk_34_2 3 nodes_34_3 = true := by decide +kernel
def bk_34_3 : Array (List (List Nat)) := buildBuckets 1 W_34 nodes_34_3
lemma bk_34_3_ok : ∀ i (hi : i < bk_34_3.size), ∀ xs ∈ bk_34_3[i], Impossible G_34 3 xs.toFinset :=
  buildBuckets_sound (by decide) gp_34 W_34_ok P_34_ok autos_34_ok bk_34_2_ok chk_34_3
def nodes_34_4 : List NodeSpec := [([87,0,2,3,4],[],[]),([61,0,1,2,6],[0],[]),([85,13,0,1,2],[1],[]),([88,0,1,2,58],[],[]),([43,0,1,2,73],[0],[]),([89,0,1,2,4],[2],[]),([90,0,1,3,4],[],[]),([36,0,31,2,5],[],[0]),([91,36,2,3,4],[],[0]),([84,88,0,1,2],[],[]),([59,1,2,58,4],[],[]),([59,25,1,3,4],[],[]),([35,67,2,3,4],[],[]),([59,35,2,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_34_4 : checkNodes W_34 G_34 fmask_34 P_34 autos_34 bk_34_3 4 nodes_34_4 = true := by decide +kernel
def bk_34_4 : Array (List (List Nat)) := buildBuckets 5 W_34 nodes_34_4
lemma bk_34_4_ok : ∀ i (hi : i < bk_34_4.size), ∀ xs ∈ bk_34_4[i], Impossible G_34 4 xs.toFinset :=
  buildBuckets_sound (by decide) gp_34 W_34_ok P_34_ok autos_34_ok bk_34_3_ok chk_34_4
def nd_34_5_0 : List NodeSpec := [([47,0,1,2,3,4],[],[]),([48,0,1,2,3,4],[3,4],[]),([48,21,1,2,3,4],[4],[]),([49,0,1,2,3,4],[],[]),([8,50,0,1,2,4],[],[]),([0,20,1,9,2,4],[0],[]),([51,0,1,2,3,4],[5,6],[]),([52,0,1,2,3,4],[],[]),([10,0,31,1,2,5],[5],[0,1]),([0,1,53,2,3,4],[],[]),([36,0,1,2,4,5],[7],[0]),([16,0,1,17,3,4],[8,9,10],[]),([54,0,1,2,3,4],[],[]),([16,0,55,1,3,4],[11],[]),([16,0,1,27,3,4],[8],[]),([10,0,56,1,2,4],[8],[]),([35,16,0,30,3,4],[11],[]),([57,0,1,2,3,4],[12,7,5],[0]),([26,35,0,2,3,4],[5],[0]),([16,0,1,2,58,4],[13],[2]),([25,16,0,1,3,4],[8],[2]),([59,16,1,2,3,4],[8],[0]),([60,0,1,2,3,4],[14,15],[]),([13,18,1,2,3,4],[12],[]),([44,13,0,1,2,3],[16],[]),([61,0,1,2,3,4],[7,5],[0]),([13,29,1,2,3,4],[12,5],[]),([46,25,0,1,3,4],[17],[0]),([14,7,13,0,1,4],[18],[]),([13,0,1,2,6,5],[5,0,19],[0]),([13,16,1,39,3,4],[8],[]),([13,0,1,2,3,40],[5,0,20],[]),([62,0,1,2,3,4],[5,14,7],[]),([13,0,1,2,3,19],[3,9,21],[]),([13,21,1,2,3,4],[12,3,9],[]),([13,63,1,2,3,4],[8],[]),([23,13,0,1,2,3],[22],[]),([64,0,1,2,3,4],[23],[]),([65,0,1,2,3,4],[],[]),([66,21,1,2,3,4],[3,9,4],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_34_5_0 : checkNodes W_34 G_34 fmask_34 P_34 autos_34 bk_34_4 5 nd_34_5_0 = true := by decide +kernel
def nd_34_5_1 : List NodeSpec := [([16,67,1,2,3,4],[3],[0]),([68,0,1,2,3,4],[5,24],[]),([0,1,2,69,3,4],[25,5],[]),([70,13,1,2,3,4],[8,5],[]),([13,16,30,3,4],[12,11,8,9,10],[]),([71,0,1,2,3,4],[5],[]),([35,13,16,2,3,4],[12,8],[]),([0,72,1,2,3,4],[5,26],[]),([13,0,1,2,3,73],[3,27],[0]),([13,0,1,2,3,74],[5,0,28],[]),([75,0,1,2,3,4],[12],[]),([13,0,1,2,76,4],[29],[]),([45,0,1,2,33,4],[30],[0]),([13,67,1,2,3,4],[8,3],[]),([13,0,1,2,3,77],[31],[]),([25,0,1,2,3,4],[],[]),([78,0,1,2,3,4],[],[]),([66,0,1,2,3,4],[3,32],[]),([25,13,16,1,3,4],[8],[]),([25,34,0,1,3,4],[8],[0,2]),([34,0,1,2,3,4],[3,5,14,7],[]),([13,16,30,2,3,4],[12,8,11],[]),([13,0,1,2,58,4],[33],[]),([42,43,0,1,2,4],[0,34],[0]),([16,18,1,2,3,4],[14,3],[]),([79,0,1,2,3,4],[],[]),([34,0,1,39,3,4],[],[0]),([80,0,1,2,3,4],[],[]),([13,81,0,1,2,3],[35],[]),([82,0,1,2,3,4],[],[]),([36,0,31,2,3,4],[5],[0]),([83,13,0,1,2,4],[36],[]),([34,0,1,2,58,4],[5,0],[0,2]),([84,13,0,1,2,4],[37],[]),([12,37,13,0,1,2],[38],[0]),([59,13,1,2,3,4],[8],[0]),([85,0,1,2],[0,1,39,10],[0]),([59,34,1,2,3,4],[8],[0,3]),([86,0,1,2,3,4],[8,12,40],[]),([84,34,0,1,2,4],[3],[3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_34_5_1 : checkNodes W_34 G_34 fmask_34 P_34 autos_34 bk_34_4 5 nd_34_5_1 = true := by decide +kernel
def nodes_34_5 : List NodeSpec := nd_34_5_0 ++ nd_34_5_1
lemma chk_34_5 : checkNodes W_34 G_34 fmask_34 P_34 autos_34 bk_34_4 5 nodes_34_5 = true := by
  unfold nodes_34_5 checkNodes
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨chk_34_5_0, chk_34_5_1⟩
def bk_34_5 : Array (List (List Nat)) := buildBuckets 27 W_34 nodes_34_5
lemma bk_34_5_ok : ∀ i (hi : i < bk_34_5.size), ∀ xs ∈ bk_34_5[i], Impossible G_34 5 xs.toFinset :=
  buildBuckets_sound (by decide) gp_34 W_34_ok P_34_ok autos_34_ok bk_34_4_ok chk_34_5
def nd_34_6_0 : List NodeSpec := [([0,1,17,2,3,4],[8,10,9,3,14,12],[0,2]),([18,0,1,2,3,4],[14,12,11,8,7,41,3],[0,2,1]),([14,7,0,1,4],[3,5,18,42,0],[0]),([0,1,2,3,19],[21,43,11,3,7],[0]),([0,20,1,2,3,4],[5,8,44,3,11,7,14,45,0],[2,0]),([21,0,1,2,3,4],[3,12,8,5,7,14,46,4,11,0],[0]),([22,0,1,2,3,4],[5,12,9,8,14,47,6,0],[0]),([23,0,1,2,3],[7,22,48,10,5],[0]),([24,0,1,2,3,4],[5,12,3,8,7,14,49,26,9],[0,2]),([21,1,2,3,4],[4,11,3,0],[0]),([25,13,0,1,2,3,4],[11,12,8,50],[0,2]),([8,0,1,9,2,4],[5,3,11,0,8],[0]),([26,16,0,1,2,3,4],[3,8,12,5,9],[0]),([0,1,27,2,3,4],[5,8,9,12,3,7,14],[0,2]),([13,0,1,2,6,3,4],[5,0,7,51],[0]),([16,0,1,2,3,4,5],[3,5,14,7,9,10,8],[0]),([28,16,0,1,3,4],[11,8,52,9,10],[0]),([29,0,1,2,3,4],[5,12,8,3,7,14,53,11,10],[0]),([16,0,30,1,2,3,4],[8,12,11],[0,2]),([10,0,31,1,2,3,4],[5,7,12,14,8,3],[0,1]),([7,13,0,1,2,3,4],[5,8,12,3,53],[0,2]),([32,16,0,1,2,3,4],[5,9,3],[0]),([13,0,1,2,3,33,4],[3,5,54],[0]),([34,13,0,1,2,3,4],[11,55],[0,2,3]),([35,16,0,1,2,3,4],[12,11,8,52],[2,0]),([10,0,1,2,4,5],[5,3,10,9,41,0],[0]),([26,10,0,1,2,4],[3,5,8,9,0,12],[]),([0,1,2,6,5],[19,56,10,0],[0]),([16,0,30,1,3,4],[11,8,12,52,57,9,10],[0,2]),([35,0,1,2,3,4],[11,8,5,3,7,14,58,52],[2,0,3]),([36,0,1,2,3,4],[3,8,5,9,7,14,59,60],[2,0]),([34,16,0,1,2,3,4],[12,9,10,52],[0,3,2]),([12,13,0,1,2,3,4],[5,3,14,7,47],[0]),([13,16,1,2,3,4],[12,11,8,9,10,52],[0]),([12,37,0,1,2],[5,7,38,61,10],[0]),([13,0,1,2,3,4,5],[5,3,7,14,41,12],[0,2]),([0,38,1,2,3,4],[8,62,11,5,3,7,14,9,10],[0]),([13,0,1,2,39,3,4],[11,63,12],[0,2,3]),([13,0,1,2,3,15,4],[3,5,46,12],[0,2]),([0,1,2,3,40],[20,64,9,0],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_34_6_0 : checkNodes W_34 G_34 fmask_34 P_34 autos_34 bk_34_5 6 nd_34_6_0 = true := by decide +kernel
def nd_34_6_1 : List NodeSpec := [([16,0,1,2,3,41,4],[9,3],[]),([42,13,0,1,2,3,4],[5,3,65],[0,2]),([13,0,1,9,2,3,4],[5,3,49],[0]),([25,0,1,2,3,4],[12,8,5,3,7,14,50,66],[0]),([43,13,0,1,2,3,4],[3,5,67],[0]),([44,0,1,2,3],[14,16,68,11,3],[0]),([45,13,0,1,2,3,4],[3,5,69],[0,2]),([34,0,1,2,3,4],[55,70,5,3,7,14],[0,2,3]),([14,13,0,1,2,3,4],[3,9,71],[0]),([46,13,0,1,2,3,4],[11,72],[0,2])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_34_6_1 : checkNodes W_34 G_34 fmask_34 P_34 autos_34 bk_34_5 6 nd_34_6_1 = true := by decide +kernel
def nodes_34_6 : List NodeSpec := nd_34_6_0 ++ nd_34_6_1
lemma chk_34_6 : checkNodes W_34 G_34 fmask_34 P_34 autos_34 bk_34_5 6 nodes_34_6 = true := by
  unfold nodes_34_6 checkNodes
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨chk_34_6_0, chk_34_6_1⟩
def bk_34_6 : Array (List (List Nat)) := buildBuckets 17 W_34 nodes_34_6
lemma bk_34_6_ok : ∀ i (hi : i < bk_34_6.size), ∀ xs ∈ bk_34_6[i], Impossible G_34 6 xs.toFinset :=
  buildBuckets_sound (by decide) gp_34 W_34_ok P_34_ok autos_34_ok bk_34_5_ok chk_34_6
def nodes_34_7 : List NodeSpec := [([0,1,2,3,4,5],[41,73,10,5,3,14,9],[0,3,2,1]),([0,1,2,6,3,4],[51,74,10,0],[0]),([7,0,1,2,3,4],[5,8,12,3,14,7,53,75,11,10],[0,2]),([8,0,1,2,3,4],[5,3,12,11,14,7,8,9,45,0],[0,2]),([0,1,9,2,3,4],[49,76,5,9,10,0],[0,2]),([10,0,1,2,3,4],[5,8,12,11,9,14,7,0,60],[0]),([11,0,1,2,3,4],[11,8,12,3,5,14,7,9,10],[0,2]),([12,0,1,2,3,4],[5,8,12,11,9,14,47,77,0],[0,2]),([13,0,1,2,3,4],[12,8,11,5,3,7,14],[0,3,2]),([14,0,1,2,3,4],[3,8,9,71,78,0],[0]),([0,1,2,3,15,4],[46,79,11,5,3,8,0,12],[0,2]),([16,0,1,2,3,4],[11,12,52,8,5,9,3,7,10,14],[0,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_34_7 : checkNodes W_34 G_34 fmask_34 P_34 autos_34 bk_34_6 7 nodes_34_7 = true := by decide +kernel
def bk_34_7 : Array (List (List Nat)) := buildBuckets 5 W_34 nodes_34_7
lemma bk_34_7_ok : ∀ i (hi : i < bk_34_7.size), ∀ xs ∈ bk_34_7[i], Impossible G_34 7 xs.toFinset :=
  buildBuckets_sound (by decide) gp_34 W_34_ok P_34_ok autos_34_ok bk_34_6_ok chk_34_7
def nodes_34_8 : List NodeSpec := [([0,1,2,3,4],[8,12],[0,3,2,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_34_8 : checkNodes W_34 G_34 fmask_34 P_34 autos_34 bk_34_7 8 nodes_34_8 = true := by decide +kernel
def bk_34_8 : Array (List (List Nat)) := buildBuckets 1 W_34 nodes_34_8
lemma bk_34_8_ok : ∀ i (hi : i < bk_34_8.size), ∀ xs ∈ bk_34_8[i], Impossible G_34 8 xs.toFinset :=
  buildBuckets_sound (by decide) gp_34 W_34_ok P_34_ok autos_34_ok bk_34_7_ok chk_34_8
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma root_34_ok : forestRootCheck R_34 G_34 [(VAR 1,14,12),(VAR 2,14,10),(VAR 3,14,6),(VAR 4,26,10),(VAR 5,42,10)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma root_34_in : bucketContains bk_34_8 R_34 = true := by decide +kernel
lemma low_34 : Lower R_34 G_34 9 := lower_of_forest root_34_ok bk_34_8_ok root_34_in

end Cofactor12319
def h4R : List Nat := varsOf 31
def h4G : Nat := 0xecc0c880ecc0c880ecc0c880ecc0c880
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4Bound : Lower h4R h4G 9 := carry_of (swaps := [(0,1),(1,2),(2,3),(3,4),(4,5),(1,2),(2,3),(0,1),(1,2),(0,1)]) (roots2 := Cofactor12319.R_34) (T2 := Cofactor12319.G_34) (by decide +kernel) Cofactor12319.low_34
def h7R : List Nat := varsOf 13
def h7G : Nat := 0xfaa0faa0faa0faa0faa0faa0faa0faa0
def h7Pos : List Nat := [9,12,5,5,12,9]
def h7Neg : List Nat := [8,8,1,4,4,1]
def h7Mask : Nat := fullMask 6
def h7Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,45,36),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,30,24),(0xff00ff00ff00ff00ff00ff00ff00ff00,51,3)]
def h7Steps : List (Nat × Nat × Nat) := []
def h7W : Array Decor := buildWires h7Base h7Steps
def h7Autos : Array (List (Nat × Nat)) := #[[]]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Pairs : goodPairs h7G h7Pos h7Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7BaseOk : ∀ x ∈ h7Base, faithful h7Pos h7Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7WOk : ∀ x ∈ h7W.toList, faithful h7Pos h7Neg x ∧ x.1 < 2^128 := buildWires_faithful h7BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7AutosOk : ∀ sw ∈ h7Autos.toList, swapsValid sw = true ∧ permWord sw h7G = h7G := autos_of (by decide +kernel)
def h7SliceList : List (Nat × Nat) := []
def h7Slices : Array (Nat × Nat) := h7SliceList.toArray
def h7Specs : List PoolSpec := []
def h7Pools : Array (Option BoundPool) := buildPools h7W h7R h7Slices h7Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7SlicesOk : ∀ i (hi : i < h7Slices.size), Slice h7R h7G h7Slices[i].1 h7Slices[i].2 := array_forall_of_list (P := fun (p : Nat × Nat) => Slice h7R h7G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7PoolsOk : ∀ i (hi : i < h7Pools.size), ∀ c, h7Pools[i] = some c → ValidPool h7R h7G c := buildPools_sound h7SlicesOk
def h7Empty : Array (List (List Nat)) := #[]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7EmptyOk : ∀ i (hi : i < h7Empty.size), ∀ xs ∈ h7Empty[i], Impossible h7G (3 - 1) xs.toFinset := by intro i hi; simp [h7Empty] at hi
def h7Block3_0 : List NodeSpec := [([0,1,2],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Test3_0 : checkNodes h7W h7G h7Mask h7Pools h7Autos h7Empty 3 h7Block3_0 = true := by decide +kernel
def h7Nodes3 : List NodeSpec := h7Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Check3 : checkNodes h7W h7G h7Mask h7Pools h7Autos h7Empty 3 h7Nodes3 = true := h7Test3_0
def h7Bucket3 : Array (List (List Nat)) := buildBuckets 1 h7W h7Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Bucket3Ok : ∀ i (hi : i < h7Bucket3.size), ∀ xs ∈ h7Bucket3[i], Impossible h7G 3 xs.toFinset := buildBuckets_sound (by decide) h7Pairs h7WOk h7PoolsOk h7AutosOk h7EmptyOk h7Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Bound : Lower h7R h7G 4 := lower_of_forest (essPairs := [(VAR 0,4,5),(VAR 2,1,5),(VAR 3,1,9)]) (by decide +kernel) h7Bucket3Ok (by decide +kernel)
def h6R : List Nat := varsOf 15
def h6G : Nat := 0xc880c880c880c880c880c880c880c880
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Bound : Lower h6R h6G 5 := lift_of (z := 0) (o := 2) (essPairs := [(VAR 1,5,7)]) (by decide +kernel) h7Bound
def h8R : List Nat := varsOf 39
def h8G : Nat := 0xeaeaeaeac8c8c8c8eaeaeaeac8c8c8c8
def h8Pos : List Nat := [6,3,3,37,38,6,37,33]
def h8Neg : List Nat := [4,1,2,36,36,2,5,1]
def h8Mask : Nat := fullMask 8
def h8Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,206,194),(0xcccccccccccccccccccccccccccccccc,55,36),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,121,89),(0xffffffff00000000ffffffff00000000,216,24)]
def h8Steps : List (Nat × Nat × Nat) := []
def h8W : Array Decor := buildWires h8Base h8Steps
def h8Autos : Array (List (Nat × Nat)) := #[[]]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8Pairs : goodPairs h8G h8Pos h8Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8BaseOk : ∀ x ∈ h8Base, faithful h8Pos h8Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8WOk : ∀ x ∈ h8W.toList, faithful h8Pos h8Neg x ∧ x.1 < 2^128 := buildWires_faithful h8BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8AutosOk : ∀ sw ∈ h8Autos.toList, swapsValid sw = true ∧ permWord sw h8G = h8G := autos_of (by decide +kernel)
def h8SliceList : List (Nat × Nat) := []
def h8Slices : Array (Nat × Nat) := h8SliceList.toArray
def h8Specs : List PoolSpec := []
def h8Pools : Array (Option BoundPool) := buildPools h8W h8R h8Slices h8Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8SlicesOk : ∀ i (hi : i < h8Slices.size), Slice h8R h8G h8Slices[i].1 h8Slices[i].2 := array_forall_of_list (P := fun (p : Nat × Nat) => Slice h8R h8G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8PoolsOk : ∀ i (hi : i < h8Pools.size), ∀ c, h8Pools[i] = some c → ValidPool h8R h8G c := buildPools_sound h8SlicesOk
def h8Empty : Array (List (List Nat)) := #[]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8EmptyOk : ∀ i (hi : i < h8Empty.size), ∀ xs ∈ h8Empty[i], Impossible h8G (3 - 1) xs.toFinset := by intro i hi; simp [h8Empty] at hi
def h8Block3_0 : List NodeSpec := [([0,1,2,3],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8Test3_0 : checkNodes h8W h8G h8Mask h8Pools h8Autos h8Empty 3 h8Block3_0 = true := by decide +kernel
def h8Nodes3 : List NodeSpec := h8Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8Check3 : checkNodes h8W h8G h8Mask h8Pools h8Autos h8Empty 3 h8Nodes3 = true := h8Test3_0
def h8Bucket3 : Array (List (List Nat)) := buildBuckets 1 h8W h8Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8Bucket3Ok : ∀ i (hi : i < h8Bucket3.size), ∀ xs ∈ h8Bucket3[i], Impossible h8G 3 xs.toFinset := buildBuckets_sound (by decide) h8Pairs h8WOk h8PoolsOk h8AutosOk h8EmptyOk h8Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8Bound : Lower h8R h8G 4 := lower_of_forest (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,2,6),(VAR 5,1,33)]) (by decide +kernel) h8Bucket3Ok (by decide +kernel)
def h9R : List Nat := varsOf 43
def h9G : Nat := 0xeeaaeeaacc88cc88eeaaeeaacc88cc88
def h9Pos : List Nat := [10,3,3,41,42,10,41,33]
def h9Neg : List Nat := [8,1,2,40,40,2,9,1]
def h9Mask : Nat := fullMask 8
def h9Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,206,194),(0xcccccccccccccccccccccccccccccccc,55,36),(0xff00ff00ff00ff00ff00ff00ff00ff00,121,89),(0xffffffff00000000ffffffff00000000,216,24)]
def h9Steps : List (Nat × Nat × Nat) := []
def h9W : Array Decor := buildWires h9Base h9Steps
def h9Autos : Array (List (Nat × Nat)) := #[[]]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Pairs : goodPairs h9G h9Pos h9Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9BaseOk : ∀ x ∈ h9Base, faithful h9Pos h9Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9WOk : ∀ x ∈ h9W.toList, faithful h9Pos h9Neg x ∧ x.1 < 2^128 := buildWires_faithful h9BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9AutosOk : ∀ sw ∈ h9Autos.toList, swapsValid sw = true ∧ permWord sw h9G = h9G := autos_of (by decide +kernel)
def h9SliceList : List (Nat × Nat) := []
def h9Slices : Array (Nat × Nat) := h9SliceList.toArray
def h9Specs : List PoolSpec := []
def h9Pools : Array (Option BoundPool) := buildPools h9W h9R h9Slices h9Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9SlicesOk : ∀ i (hi : i < h9Slices.size), Slice h9R h9G h9Slices[i].1 h9Slices[i].2 := array_forall_of_list (P := fun (p : Nat × Nat) => Slice h9R h9G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9PoolsOk : ∀ i (hi : i < h9Pools.size), ∀ c, h9Pools[i] = some c → ValidPool h9R h9G c := buildPools_sound h9SlicesOk
def h9Empty : Array (List (List Nat)) := #[]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9EmptyOk : ∀ i (hi : i < h9Empty.size), ∀ xs ∈ h9Empty[i], Impossible h9G (3 - 1) xs.toFinset := by intro i hi; simp [h9Empty] at hi
def h9Block3_0 : List NodeSpec := [([0,1,2,3],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Test3_0 : checkNodes h9W h9G h9Mask h9Pools h9Autos h9Empty 3 h9Block3_0 = true := by decide +kernel
def h9Nodes3 : List NodeSpec := h9Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Check3 : checkNodes h9W h9G h9Mask h9Pools h9Autos h9Empty 3 h9Nodes3 = true := h9Test3_0
def h9Bucket3 : Array (List (List Nat)) := buildBuckets 1 h9W h9Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Bucket3Ok : ∀ i (hi : i < h9Bucket3.size), ∀ xs ∈ h9Bucket3[i], Impossible h9G 3 xs.toFinset := buildBuckets_sound (by decide) h9Pairs h9WOk h9PoolsOk h9AutosOk h9EmptyOk h9Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Bound : Lower h9R h9G 4 := lower_of_forest (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 3,2,10),(VAR 5,1,33)]) (by decide +kernel) h9Bucket3Ok (by decide +kernel)
def h10R : List Nat := varsOf 45
def h10G : Nat := 0xfaaafaaafaa0faa0faaafaaafaa0faa0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h10Bound : Lower h10R h10G 5 := lift_of (z := 32) (o := 0) (essPairs := [(VAR 5,1,33)]) (by decide +kernel) h7Bound
def h5R : List Nat := varsOf 47
def h5G : Nat := 0xeaaaeaaac880c880eaaaeaaac880c880
def h5Pos : List Nat := [14,33,7,7,14,33,11,11,11,35,33,14,37,7,41,7,33,11,35,37,41,46,45,45,46,46]
def h5Neg : List Nat := [12,32,5,6,10,36,3,10,9,3,1,6,5,3,9,2,40,2,34,36,40,44,44,13,42,38]
def h5Mask : Nat := fullMask 26
def h5Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xdff7ee,0x807744),(0xcccccccccccccccccccccccccccccccc,0x326abdd,0x306aad8),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x3e8b81d,0x2e8182d),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x3f249d1,0x1f14191),(0xffffffff00000000ffffffff00000000,0x3fd5622,0x37d0022)]
def h5Steps : List (Nat × Nat × Nat) := [(0,0,2),(3,0,2),(0,0,3),(3,0,3),(2,0,4),(0,2,3),(2,3,5),(1,4,6),(2,2,7),(1,4,8)]
def h5W : Array Decor := buildWires h5Base h5Steps
def h5Autos : Array (List (Nat × Nat)) := #[[]]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Pairs : goodPairs h5G h5Pos h5Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5BaseOk : ∀ x ∈ h5Base, faithful h5Pos h5Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5WOk : ∀ x ∈ h5W.toList, faithful h5Pos h5Neg x ∧ x.1 < 2^128 := buildWires_faithful h5BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5AutosOk : ∀ sw ∈ h5Autos.toList, swapsValid sw = true ∧ permWord sw h5G = h5G := autos_of (by decide +kernel)
def h5SliceList : List (Nat × Nat) := [(subcube 0 2,5),(subcube 0 4,4),(subcube 0 8,4),(subcube 32 0,5)]
def h5Slices : Array (Nat × Nat) := h5SliceList.toArray
def h5Specs : List PoolSpec := [(0,[]),(2,[]),(1,[]),(3,[]),(0,[(2,0,4)])]
def h5Pools : Array (Option BoundPool) := buildPools h5W h5R h5Slices h5Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Slice3 : Slice h5R h5G (subcube 32 0) 5 := slice_direct (zDead := 0) (by decide +kernel) h6Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Slice2 : Slice h5R h5G (subcube 0 8) 4 := slice_direct (zDead := 0) (by decide +kernel) h8Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Slice1 : Slice h5R h5G (subcube 0 4) 4 := slice_direct (zDead := 0) (by decide +kernel) h9Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Slice0 : Slice h5R h5G (subcube 0 2) 5 := slice_direct (zDead := 0) (by decide +kernel) h10Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5SlicesOk : ∀ i (hi : i < h5Slices.size), Slice h5R h5G h5Slices[i].1 h5Slices[i].2 := array_forall_of_list (P := fun (p : Nat × Nat) => Slice h5R h5G p.1 p.2) (forall_cons h5Slice0 (forall_cons h5Slice1 (forall_cons h5Slice2 (forall_cons h5Slice3 (fun _ h => (List.not_mem_nil h).elim)))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5PoolsOk : ∀ i (hi : i < h5Pools.size), ∀ c, h5Pools[i] = some c → ValidPool h5R h5G c := buildPools_sound h5SlicesOk
def h5Empty : Array (List (List Nat)) := #[]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5EmptyOk : ∀ i (hi : i < h5Empty.size), ∀ xs ∈ h5Empty[i], Impossible h5G (4 - 1) xs.toFinset := by intro i hi; simp [h5Empty] at hi
def h5Block4_0 : List NodeSpec := [([0,1,2,4,11],[],[0]),([0,1,2,3,12],[],[0]),([0,1,3,4,13],[],[0]),([0,1,2,3,14],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Test4_0 : checkNodes h5W h5G h5Mask h5Pools h5Autos h5Empty 4 h5Block4_0 = true := by decide +kernel
def h5Nodes4 : List NodeSpec := h5Block4_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Check4 : checkNodes h5W h5G h5Mask h5Pools h5Autos h5Empty 4 h5Nodes4 = true := h5Test4_0
def h5Bucket4 : Array (List (List Nat)) := buildBuckets 4 h5W h5Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Bucket4Ok : ∀ i (hi : i < h5Bucket4.size), ∀ xs ∈ h5Bucket4[i], Impossible h5G 4 xs.toFinset := buildBuckets_sound (by decide) h5Pairs h5WOk h5PoolsOk h5AutosOk h5EmptyOk h5Check4
def h5Block5_0 : List NodeSpec := [([0,1,2,3,4,5],[1],[0]),([0,1,2,3,4,6],[3],[0]),([0,1,2,3,4,7],[2],[0]),([0,1,2,3,4,8],[3],[0]),([0,1,2,3,9],[3,4],[0]),([0,1,2,3,4,10],[2],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Test5_0 : checkNodes h5W h5G h5Mask h5Pools h5Autos h5Bucket4 5 h5Block5_0 = true := by decide +kernel
def h5Nodes5 : List NodeSpec := h5Block5_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Check5 : checkNodes h5W h5G h5Mask h5Pools h5Autos h5Bucket4 5 h5Nodes5 = true := h5Test5_0
def h5Bucket5 : Array (List (List Nat)) := buildBuckets 6 h5W h5Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Bucket5Ok : ∀ i (hi : i < h5Bucket5.size), ∀ xs ∈ h5Bucket5[i], Impossible h5G 5 xs.toFinset := buildBuckets_sound (by decide) h5Pairs h5WOk h5PoolsOk h5AutosOk h5Bucket4Ok h5Check5
def h5Block6_0 : List NodeSpec := [([0,1,2,3,4],[0,1,2,3],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Test6_0 : checkNodes h5W h5G h5Mask h5Pools h5Autos h5Bucket5 6 h5Block6_0 = true := by decide +kernel
def h5Nodes6 : List NodeSpec := h5Block6_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Check6 : checkNodes h5W h5G h5Mask h5Pools h5Autos h5Bucket5 6 h5Nodes6 = true := h5Test6_0
def h5Bucket6 : Array (List (List Nat)) := buildBuckets 1 h5W h5Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Bucket6Ok : ∀ i (hi : i < h5Bucket6.size), ∀ xs ∈ h5Bucket6[i], Impossible h5G 6 xs.toFinset := buildBuckets_sound (by decide) h5Pairs h5WOk h5PoolsOk h5AutosOk h5Bucket5Ok h5Check6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Bound : Lower h5R h5G 7 := lower_of_forest (essPairs := [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11),(VAR 5,1,33)]) (by decide +kernel) h5Bucket6Ok (by decide +kernel)
def h12R : List Nat := varsOf 53
def h12G : Nat := 0xfafaaaaaf0f0a0a0fafaaaaaf0f0a0a0
def h12Pos : List Nat := [20,5,5,49,52,20,49,33]
def h12Neg : List Nat := [16,1,4,48,48,4,17,1]
def h12Mask : Nat := fullMask 8
def h12Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,206,194),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,55,36),(0xffff0000ffff0000ffff0000ffff0000,121,89),(0xffffffff00000000ffffffff00000000,216,24)]
def h12Steps : List (Nat × Nat × Nat) := []
def h12W : Array Decor := buildWires h12Base h12Steps
def h12Autos : Array (List (Nat × Nat)) := #[[]]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h12Pairs : goodPairs h12G h12Pos h12Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h12BaseOk : ∀ x ∈ h12Base, faithful h12Pos h12Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h12WOk : ∀ x ∈ h12W.toList, faithful h12Pos h12Neg x ∧ x.1 < 2^128 := buildWires_faithful h12BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h12AutosOk : ∀ sw ∈ h12Autos.toList, swapsValid sw = true ∧ permWord sw h12G = h12G := autos_of (by decide +kernel)
def h12SliceList : List (Nat × Nat) := []
def h12Slices : Array (Nat × Nat) := h12SliceList.toArray
def h12Specs : List PoolSpec := []
def h12Pools : Array (Option BoundPool) := buildPools h12W h12R h12Slices h12Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h12SlicesOk : ∀ i (hi : i < h12Slices.size), Slice h12R h12G h12Slices[i].1 h12Slices[i].2 := array_forall_of_list (P := fun (p : Nat × Nat) => Slice h12R h12G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h12PoolsOk : ∀ i (hi : i < h12Pools.size), ∀ c, h12Pools[i] = some c → ValidPool h12R h12G c := buildPools_sound h12SlicesOk
def h12Empty : Array (List (List Nat)) := #[]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h12EmptyOk : ∀ i (hi : i < h12Empty.size), ∀ xs ∈ h12Empty[i], Impossible h12G (3 - 1) xs.toFinset := by intro i hi; simp [h12Empty] at hi
def h12Block3_0 : List NodeSpec := [([0,1,2,3],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h12Test3_0 : checkNodes h12W h12G h12Mask h12Pools h12Autos h12Empty 3 h12Block3_0 = true := by decide +kernel
def h12Nodes3 : List NodeSpec := h12Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h12Check3 : checkNodes h12W h12G h12Mask h12Pools h12Autos h12Empty 3 h12Nodes3 = true := h12Test3_0
def h12Bucket3 : Array (List (List Nat)) := buildBuckets 1 h12W h12Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h12Bucket3Ok : ∀ i (hi : i < h12Bucket3.size), ∀ xs ∈ h12Bucket3[i], Impossible h12G 3 xs.toFinset := buildBuckets_sound (by decide) h12Pairs h12WOk h12PoolsOk h12AutosOk h12EmptyOk h12Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h12Bound : Lower h12R h12G 4 := lower_of_forest (essPairs := [(VAR 0,4,5),(VAR 2,1,5),(VAR 4,4,20),(VAR 5,1,33)]) (by decide +kernel) h12Bucket3Ok (by decide +kernel)
def h11R : List Nat := varsOf 55
def h11G : Nat := 0xeaeaaaaac0c08080eaeaaaaac0c08080
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Bound : Lower h11R h11G 5 := lift_of (z := 0) (o := 2) (essPairs := [(VAR 1,5,7)]) (by decide +kernel) h12Bound
def h14R : List Nat := varsOf 57
def h14G : Nat := 0xffaaaaaaff00aa00ffaaaaaaff00aa00
def h14Pos : List Nat := [24,9,9,49,56,24,49,33]
def h14Neg : List Nat := [16,1,8,48,48,8,17,1]
def h14Mask : Nat := fullMask 8
def h14Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,206,194),(0xff00ff00ff00ff00ff00ff00ff00ff00,55,36),(0xffff0000ffff0000ffff0000ffff0000,121,89),(0xffffffff00000000ffffffff00000000,216,24)]
def h14Steps : List (Nat × Nat × Nat) := []
def h14W : Array Decor := buildWires h14Base h14Steps
def h14Autos : Array (List (Nat × Nat)) := #[[]]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14Pairs : goodPairs h14G h14Pos h14Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14BaseOk : ∀ x ∈ h14Base, faithful h14Pos h14Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14WOk : ∀ x ∈ h14W.toList, faithful h14Pos h14Neg x ∧ x.1 < 2^128 := buildWires_faithful h14BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14AutosOk : ∀ sw ∈ h14Autos.toList, swapsValid sw = true ∧ permWord sw h14G = h14G := autos_of (by decide +kernel)
def h14SliceList : List (Nat × Nat) := []
def h14Slices : Array (Nat × Nat) := h14SliceList.toArray
def h14Specs : List PoolSpec := []
def h14Pools : Array (Option BoundPool) := buildPools h14W h14R h14Slices h14Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14SlicesOk : ∀ i (hi : i < h14Slices.size), Slice h14R h14G h14Slices[i].1 h14Slices[i].2 := array_forall_of_list (P := fun (p : Nat × Nat) => Slice h14R h14G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14PoolsOk : ∀ i (hi : i < h14Pools.size), ∀ c, h14Pools[i] = some c → ValidPool h14R h14G c := buildPools_sound h14SlicesOk
def h14Empty : Array (List (List Nat)) := #[]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14EmptyOk : ∀ i (hi : i < h14Empty.size), ∀ xs ∈ h14Empty[i], Impossible h14G (3 - 1) xs.toFinset := by intro i hi; simp [h14Empty] at hi
def h14Block3_0 : List NodeSpec := [([0,1,2,3],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14Test3_0 : checkNodes h14W h14G h14Mask h14Pools h14Autos h14Empty 3 h14Block3_0 = true := by decide +kernel
def h14Nodes3 : List NodeSpec := h14Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14Check3 : checkNodes h14W h14G h14Mask h14Pools h14Autos h14Empty 3 h14Nodes3 = true := h14Test3_0
def h14Bucket3 : Array (List (List Nat)) := buildBuckets 1 h14W h14Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14Bucket3Ok : ∀ i (hi : i < h14Bucket3.size), ∀ xs ∈ h14Bucket3[i], Impossible h14G 3 xs.toFinset := buildBuckets_sound (by decide) h14Pairs h14WOk h14PoolsOk h14AutosOk h14EmptyOk h14Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14Bound : Lower h14R h14G 4 := lower_of_forest (essPairs := [(VAR 0,8,9),(VAR 3,1,9),(VAR 4,8,24),(VAR 5,1,33)]) (by decide +kernel) h14Bucket3Ok (by decide +kernel)
def h13R : List Nat := varsOf 59
def h13G : Nat := 0xeeaaaaaacc008800eeaaaaaacc008800
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13Bound : Lower h13R h13G 5 := lift_of (z := 0) (o := 2) (essPairs := [(VAR 1,9,11)]) (by decide +kernel) h14Bound
def h15R : List Nat := varsOf 37
def h15G : Nat := 0xfafafafaa0a0a0a0fafafafaa0a0a0a0
def h15Pos : List Nat := [33,36,5,5,36,33]
def h15Neg : List Nat := [32,32,1,4,4,1]
def h15Mask : Nat := fullMask 6
def h15Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,45,36),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,30,24),(0xffffffff00000000ffffffff00000000,51,3)]
def h15Steps : List (Nat × Nat × Nat) := []
def h15W : Array Decor := buildWires h15Base h15Steps
def h15Autos : Array (List (Nat × Nat)) := #[[]]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Pairs : goodPairs h15G h15Pos h15Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15BaseOk : ∀ x ∈ h15Base, faithful h15Pos h15Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15WOk : ∀ x ∈ h15W.toList, faithful h15Pos h15Neg x ∧ x.1 < 2^128 := buildWires_faithful h15BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15AutosOk : ∀ sw ∈ h15Autos.toList, swapsValid sw = true ∧ permWord sw h15G = h15G := autos_of (by decide +kernel)
def h15SliceList : List (Nat × Nat) := []
def h15Slices : Array (Nat × Nat) := h15SliceList.toArray
def h15Specs : List PoolSpec := []
def h15Pools : Array (Option BoundPool) := buildPools h15W h15R h15Slices h15Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15SlicesOk : ∀ i (hi : i < h15Slices.size), Slice h15R h15G h15Slices[i].1 h15Slices[i].2 := array_forall_of_list (P := fun (p : Nat × Nat) => Slice h15R h15G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15PoolsOk : ∀ i (hi : i < h15Pools.size), ∀ c, h15Pools[i] = some c → ValidPool h15R h15G c := buildPools_sound h15SlicesOk
def h15Empty : Array (List (List Nat)) := #[]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15EmptyOk : ∀ i (hi : i < h15Empty.size), ∀ xs ∈ h15Empty[i], Impossible h15G (3 - 1) xs.toFinset := by intro i hi; simp [h15Empty] at hi
def h15Block3_0 : List NodeSpec := [([0,1,2],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Test3_0 : checkNodes h15W h15G h15Mask h15Pools h15Autos h15Empty 3 h15Block3_0 = true := by decide +kernel
def h15Nodes3 : List NodeSpec := h15Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Check3 : checkNodes h15W h15G h15Mask h15Pools h15Autos h15Empty 3 h15Nodes3 = true := h15Test3_0
def h15Bucket3 : Array (List (List Nat)) := buildBuckets 1 h15W h15Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Bucket3Ok : ∀ i (hi : i < h15Bucket3.size), ∀ xs ∈ h15Bucket3[i], Impossible h15G 3 xs.toFinset := buildBuckets_sound (by decide) h15Pairs h15WOk h15PoolsOk h15AutosOk h15EmptyOk h15Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Bound : Lower h15R h15G 4 := lower_of_forest (essPairs := [(VAR 0,4,5),(VAR 2,1,5),(VAR 5,1,33)]) (by decide +kernel) h15Bucket3Ok (by decide +kernel)
def h16R : List Nat := varsOf 41
def h16G : Nat := 0xffaaffaaaa00aa00ffaaffaaaa00aa00
def h16Pos : List Nat := [33,40,9,9,40,33]
def h16Neg : List Nat := [32,32,1,8,8,1]
def h16Mask : Nat := fullMask 6
def h16Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,45,36),(0xff00ff00ff00ff00ff00ff00ff00ff00,30,24),(0xffffffff00000000ffffffff00000000,51,3)]
def h16Steps : List (Nat × Nat × Nat) := []
def h16W : Array Decor := buildWires h16Base h16Steps
def h16Autos : Array (List (Nat × Nat)) := #[[]]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Pairs : goodPairs h16G h16Pos h16Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16BaseOk : ∀ x ∈ h16Base, faithful h16Pos h16Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16WOk : ∀ x ∈ h16W.toList, faithful h16Pos h16Neg x ∧ x.1 < 2^128 := buildWires_faithful h16BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16AutosOk : ∀ sw ∈ h16Autos.toList, swapsValid sw = true ∧ permWord sw h16G = h16G := autos_of (by decide +kernel)
def h16SliceList : List (Nat × Nat) := []
def h16Slices : Array (Nat × Nat) := h16SliceList.toArray
def h16Specs : List PoolSpec := []
def h16Pools : Array (Option BoundPool) := buildPools h16W h16R h16Slices h16Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16SlicesOk : ∀ i (hi : i < h16Slices.size), Slice h16R h16G h16Slices[i].1 h16Slices[i].2 := array_forall_of_list (P := fun (p : Nat × Nat) => Slice h16R h16G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16PoolsOk : ∀ i (hi : i < h16Pools.size), ∀ c, h16Pools[i] = some c → ValidPool h16R h16G c := buildPools_sound h16SlicesOk
def h16Empty : Array (List (List Nat)) := #[]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16EmptyOk : ∀ i (hi : i < h16Empty.size), ∀ xs ∈ h16Empty[i], Impossible h16G (3 - 1) xs.toFinset := by intro i hi; simp [h16Empty] at hi
def h16Block3_0 : List NodeSpec := [([0,1,2],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Test3_0 : checkNodes h16W h16G h16Mask h16Pools h16Autos h16Empty 3 h16Block3_0 = true := by decide +kernel
def h16Nodes3 : List NodeSpec := h16Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Check3 : checkNodes h16W h16G h16Mask h16Pools h16Autos h16Empty 3 h16Nodes3 = true := h16Test3_0
def h16Bucket3 : Array (List (List Nat)) := buildBuckets 1 h16W h16Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Bucket3Ok : ∀ i (hi : i < h16Bucket3.size), ∀ xs ∈ h16Bucket3[i], Impossible h16G 3 xs.toFinset := buildBuckets_sound (by decide) h16Pairs h16WOk h16PoolsOk h16AutosOk h16EmptyOk h16Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Bound : Lower h16R h16G 4 := lower_of_forest (essPairs := [(VAR 0,8,9),(VAR 3,1,9),(VAR 5,1,33)]) (by decide +kernel) h16Bucket3Ok (by decide +kernel)
def h17R : List Nat := varsOf 45
def h17G : Nat := 0xfaaafaaaa000a000faaafaaaa000a000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h17Bound : Lower h17R h17G 5 := lift_of (z := 0) (o := 4) (essPairs := [(VAR 2,9,13)]) (by decide +kernel) h16Bound
def h18R : List Nat := varsOf 49
def h18G : Nat := 0xffffaaaaaaaa0000ffffaaaaaaaa0000
def h18Pos : List Nat := [33,48,17,17,48,33]
def h18Neg : List Nat := [32,32,1,16,16,1]
def h18Mask : Nat := fullMask 6
def h18Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,45,36),(0xffff0000ffff0000ffff0000ffff0000,30,24),(0xffffffff00000000ffffffff00000000,51,3)]
def h18Steps : List (Nat × Nat × Nat) := []
def h18W : Array Decor := buildWires h18Base h18Steps
def h18Autos : Array (List (Nat × Nat)) := #[[]]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18Pairs : goodPairs h18G h18Pos h18Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18BaseOk : ∀ x ∈ h18Base, faithful h18Pos h18Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18WOk : ∀ x ∈ h18W.toList, faithful h18Pos h18Neg x ∧ x.1 < 2^128 := buildWires_faithful h18BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18AutosOk : ∀ sw ∈ h18Autos.toList, swapsValid sw = true ∧ permWord sw h18G = h18G := autos_of (by decide +kernel)
def h18SliceList : List (Nat × Nat) := []
def h18Slices : Array (Nat × Nat) := h18SliceList.toArray
def h18Specs : List PoolSpec := []
def h18Pools : Array (Option BoundPool) := buildPools h18W h18R h18Slices h18Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18SlicesOk : ∀ i (hi : i < h18Slices.size), Slice h18R h18G h18Slices[i].1 h18Slices[i].2 := array_forall_of_list (P := fun (p : Nat × Nat) => Slice h18R h18G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18PoolsOk : ∀ i (hi : i < h18Pools.size), ∀ c, h18Pools[i] = some c → ValidPool h18R h18G c := buildPools_sound h18SlicesOk
def h18Empty : Array (List (List Nat)) := #[]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18EmptyOk : ∀ i (hi : i < h18Empty.size), ∀ xs ∈ h18Empty[i], Impossible h18G (3 - 1) xs.toFinset := by intro i hi; simp [h18Empty] at hi
def h18Block3_0 : List NodeSpec := [([0,1,2],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18Test3_0 : checkNodes h18W h18G h18Mask h18Pools h18Autos h18Empty 3 h18Block3_0 = true := by decide +kernel
def h18Nodes3 : List NodeSpec := h18Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18Check3 : checkNodes h18W h18G h18Mask h18Pools h18Autos h18Empty 3 h18Nodes3 = true := h18Test3_0
def h18Bucket3 : Array (List (List Nat)) := buildBuckets 1 h18W h18Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18Bucket3Ok : ∀ i (hi : i < h18Bucket3.size), ∀ xs ∈ h18Bucket3[i], Impossible h18G 3 xs.toFinset := buildBuckets_sound (by decide) h18Pairs h18WOk h18PoolsOk h18AutosOk h18EmptyOk h18Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18Bound : Lower h18R h18G 4 := lower_of_forest (essPairs := [(VAR 0,16,17),(VAR 4,1,17),(VAR 5,1,33)]) (by decide +kernel) h18Bucket3Ok (by decide +kernel)
def h19R : List Nat := varsOf 53
def h19G : Nat := 0xfafaaaaaa0a00000fafaaaaaa0a00000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h19Bound : Lower h19R h19G 5 := lift_of (z := 0) (o := 4) (essPairs := [(VAR 2,17,21)]) (by decide +kernel) h18Bound
def h20R : List Nat := varsOf 57
def h20G : Nat := 0xffaaaaaaaa000000ffaaaaaaaa000000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h20Bound : Lower h20R h20G 5 := lift_of (z := 0) (o := 8) (essPairs := [(VAR 3,17,25)]) (by decide +kernel) h18Bound
def h21R : List Nat := varsOf 61
def h21G : Nat := 0xfaaaaaaaa0000000faaaaaaaa0000000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Bound : Lower h21R h21G 6 := lift_of (z := 0) (o := 12) (essPairs := [(VAR 2,25,29),(VAR 3,21,29)]) (by decide +kernel) h18Bound
namespace Cofactor12196
def G_0 : Nat := 0xfcfcfcfcc0c0c0c0fcfcfcfcc0c0c0c0
def R_0 : List Nat := varsOf 38
def pos_0 : List Nat := [6,6,34,34,36,36,6,34,36]
def neg_0 : List Nat := [4,2,32,2,32,4,32,4,2]
def fmask_0 : Nat := fullMask 9
def base_0 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xcf,0x10a),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x173,0xa1),(0xffffffff00000000ffffffff00000000,0x1bc,0x54)]
def steps_0 : List (Nat × Nat × Nat) := []
def W_0 : Array Decor := buildWires base_0 steps_0
def autos_0 : Array (List (Nat × Nat)) := #[]
def slicesL_0 : List (Nat × Nat) := []
def slices_0 : Array (Nat × Nat) := slicesL_0.toArray
def ps_0 : List PoolSpec := []
def P_0 : Array (Option BoundPool) := buildPools W_0 R_0 slices_0 ps_0
lemma gp_0 : goodPairs G_0 pos_0 neg_0 := goodPairs_of (by decide +kernel)
lemma base_0_ok : ∀ x ∈ base_0, faithful pos_0 neg_0 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma W_0_ok : ∀ x ∈ W_0.toList, faithful pos_0 neg_0 x ∧ x.1 < 2^128 := buildWires_faithful base_0_ok
lemma autos_0_ok : ∀ sw ∈ autos_0.toList, swapsValid sw = true ∧ permWord sw G_0 = G_0 := autos_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma slices_0_ok : ∀ i (hi : i < slices_0.size), Slice R_0 G_0 slices_0[i].1 slices_0[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice R_0 G_0 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma P_0_ok : ∀ i (hi : i < P_0.size), ∀ c, P_0[i] = some c → ValidPool R_0 G_0 c := buildPools_sound slices_0_ok
def bk_0_init : Array (List (List Nat)) := #[]
lemma bk_0_init_ok : ∀ i (hi : i < bk_0_init.size), ∀ xs ∈ bk_0_init[i], Impossible G_0 (0 - 1) xs.toFinset := by intro i hi; simp [bk_0_init] at hi
def nodes_0_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_0 : checkNodes W_0 G_0 fmask_0 P_0 autos_0 bk_0_init 0 nodes_0_0 = true := by decide +kernel
def bk_0_0 : Array (List (List Nat)) := buildBuckets 1 W_0 nodes_0_0
lemma bk_0_0_ok : ∀ i (hi : i < bk_0_0.size), ∀ xs ∈ bk_0_0[i], Impossible G_0 0 xs.toFinset :=
  buildBuckets_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_init_ok chk_0_0
def nodes_0_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_1 : checkNodes W_0 G_0 fmask_0 P_0 autos_0 bk_0_0 1 nodes_0_1 = true := by decide +kernel
def bk_0_1 : Array (List (List Nat)) := buildBuckets 1 W_0 nodes_0_1
lemma bk_0_1_ok : ∀ i (hi : i < bk_0_1.size), ∀ xs ∈ bk_0_1[i], Impossible G_0 1 xs.toFinset :=
  buildBuckets_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_0_ok chk_0_1
def nodes_0_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_2 : checkNodes W_0 G_0 fmask_0 P_0 autos_0 bk_0_1 2 nodes_0_2 = true := by decide +kernel
def bk_0_2 : Array (List (List Nat)) := buildBuckets 1 W_0 nodes_0_2
lemma bk_0_2_ok : ∀ i (hi : i < bk_0_2.size), ∀ xs ∈ bk_0_2[i], Impossible G_0 2 xs.toFinset :=
  buildBuckets_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_1_ok chk_0_2
def nodes_0_3 : List NodeSpec := [([0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_3 : checkNodes W_0 G_0 fmask_0 P_0 autos_0 bk_0_2 3 nodes_0_3 = true := by decide +kernel
def bk_0_3 : Array (List (List Nat)) := buildBuckets 1 W_0 nodes_0_3
lemma bk_0_3_ok : ∀ i (hi : i < bk_0_3.size), ∀ xs ∈ bk_0_3[i], Impossible G_0 3 xs.toFinset :=
  buildBuckets_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_2_ok chk_0_3
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma root_0_ok : forestRootCheck R_0 G_0 [(VAR 1,6,4),(VAR 2,6,2),(VAR 5,34,2)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma root_0_in : bucketContains bk_0_3 R_0 = true := by decide +kernel
lemma low_0 : Lower R_0 G_0 4 := lower_of_forest root_0_ok bk_0_3_ok root_0_in

def G_1 : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def R_1 : List Nat := varsOf 7
lemma low_1_ok : carryOK [(3,4),(0,3),(0,5),(0,2),(0,1)] R_1 G_1 R_0 G_0 = true := by decide +kernel
lemma low_1 : Lower R_1 G_1 4 := carry_of low_1_ok low_0

def G_2 : Nat := 0xeeeeeeee88888888eeeeeeee88888888
def R_2 : List Nat := varsOf 35
lemma low_2_ok : carryOK [(0,2),(0,1)] R_2 G_2 R_0 G_0 = true := by decide +kernel
lemma low_2 : Lower R_2 G_2 4 := carry_of low_2_ok low_0

def G_3 : Nat := 0xfafafafaa0a0a0a0fafafafaa0a0a0a0
def R_3 : List Nat := varsOf 37
lemma low_3_ok : carryOK [(0,1)] R_3 G_3 R_0 G_0 = true := by decide +kernel
lemma low_3 : Lower R_3 G_3 4 := carry_of low_3_ok low_0

def G_6 : Nat := 0xe8e8e8e880808080e8e8e8e880808080
def R_6 : List Nat := varsOf 39
def pos_6 : List Nat := [7,7,7,35,35,35,37,37,37,38,38,38,7,7,7,35,35,35,37,37,37,38,38,38]
def neg_6 : List Nat := [6,5,3,34,33,3,36,33,5,36,34,6,33,34,36,5,6,36,3,6,34,3,5,33]
def fmask_6 : Nat := fullMask 24
def base_6 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x1ff1ff,0xe491b6),(0xcccccccccccccccccccccccccccccccc,0xe3fe3f,0x3d2c2d),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfc7fc7,0x4bcb43),(0xffffffff00000000ffffffff00000000,0xff8ff8,0x9276d8)]
def steps_6 : List (Nat × Nat × Nat) := [(0,0,1),(3,4,2),(0,0,2),(0,4,2),(0,1,2),(3,7,3)]
def W_6 : Array Decor := buildWires base_6 steps_6
def autos_6 : Array (List (Nat × Nat)) := #[[],[(2,5)],[(0,1)],[(2,5),(0,1)],[(1,2)],[(1,5),(1,2)],[(0,1),(0,2)],[(1,5),(0,1),(0,2)],[(1,5),(0,2)]]
def slicesL_6 : List (Nat × Nat) := [(subcube 0 4,4),(subcube 0 1,4),(subcube 0 2,4),(subcube 0 32,4)]
def slices_6 : Array (Nat × Nat) := slicesL_6.toArray
def ps_6 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[])]
def P_6 : Array (Option BoundPool) := buildPools W_6 R_6 slices_6 ps_6
lemma gp_6 : goodPairs G_6 pos_6 neg_6 := goodPairs_of (by decide +kernel)
lemma base_6_ok : ∀ x ∈ base_6, faithful pos_6 neg_6 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma W_6_ok : ∀ x ∈ W_6.toList, faithful pos_6 neg_6 x ∧ x.1 < 2^128 := buildWires_faithful base_6_ok
lemma autos_6_ok : ∀ sw ∈ autos_6.toList, swapsValid sw = true ∧ permWord sw G_6 = G_6 := autos_of (by decide +kernel)
lemma sl_6_0_ok : sliceDirectCheck 0 4 0 R_6 G_6 R_2 G_2 = true := by decide +kernel
lemma sl_6_0 : Slice R_6 G_6 (subcube 0 4) 4 := slice_direct sl_6_0_ok low_2
lemma sl_6_1_ok : sliceDirectCheck 0 1 0 R_6 G_6 R_0 G_0 = true := by decide +kernel
lemma sl_6_1 : Slice R_6 G_6 (subcube 0 1) 4 := slice_direct sl_6_1_ok low_0
lemma sl_6_2_ok : sliceDirectCheck 0 2 0 R_6 G_6 R_3 G_3 = true := by decide +kernel
lemma sl_6_2 : Slice R_6 G_6 (subcube 0 2) 4 := slice_direct sl_6_2_ok low_3
lemma sl_6_3_ok : sliceDirectCheck 0 32 0 R_6 G_6 R_1 G_1 = true := by decide +kernel
lemma sl_6_3 : Slice R_6 G_6 (subcube 0 32) 4 := slice_direct sl_6_3_ok low_1
set_option maxRecDepth 200000 in
lemma slices_6_ok : ∀ i (hi : i < slices_6.size), Slice R_6 G_6 slices_6[i].1 slices_6[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice R_6 G_6 p.1 p.2) (forall_cons sl_6_0 (forall_cons sl_6_1 (forall_cons sl_6_2 (forall_cons sl_6_3 (fun _ h => (List.not_mem_nil h).elim)))))
lemma P_6_ok : ∀ i (hi : i < P_6.size), ∀ c, P_6[i] = some c → ValidPool R_6 G_6 c := buildPools_sound slices_6_ok
def bk_6_init : Array (List (List Nat)) := #[]
lemma bk_6_init_ok : ∀ i (hi : i < bk_6_init.size), ∀ xs ∈ bk_6_init[i], Impossible G_6 (0 - 1) xs.toFinset := by intro i hi; simp [bk_6_init] at hi
def nodes_6_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_6_0 : checkNodes W_6 G_6 fmask_6 P_6 autos_6 bk_6_init 0 nodes_6_0 = true := by decide +kernel
def bk_6_0 : Array (List (List Nat)) := buildBuckets 1 W_6 nodes_6_0
lemma bk_6_0_ok : ∀ i (hi : i < bk_6_0.size), ∀ xs ∈ bk_6_0[i], Impossible G_6 0 xs.toFinset :=
  buildBuckets_sound (by decide) gp_6 W_6_ok P_6_ok autos_6_ok bk_6_init_ok chk_6_0
def nodes_6_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_6_1 : checkNodes W_6 G_6 fmask_6 P_6 autos_6 bk_6_0 1 nodes_6_1 = true := by decide +kernel
def bk_6_1 : Array (List (List Nat)) := buildBuckets 1 W_6 nodes_6_1
lemma bk_6_1_ok : ∀ i (hi : i < bk_6_1.size), ∀ xs ∈ bk_6_1[i], Impossible G_6 1 xs.toFinset :=
  buildBuckets_sound (by decide) gp_6 W_6_ok P_6_ok autos_6_ok bk_6_0_ok chk_6_1
def nodes_6_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_6_2 : checkNodes W_6 G_6 fmask_6 P_6 autos_6 bk_6_1 2 nodes_6_2 = true := by decide +kernel
def bk_6_2 : Array (List (List Nat)) := buildBuckets 1 W_6 nodes_6_2
lemma bk_6_2_ok : ∀ i (hi : i < bk_6_2.size), ∀ xs ∈ bk_6_2[i], Impossible G_6 2 xs.toFinset :=
  buildBuckets_sound (by decide) gp_6 W_6_ok P_6_ok autos_6_ok bk_6_1_ok chk_6_2
def nodes_6_3 : List NodeSpec := [([4,6,8,3],[0,1],[]),([9,0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_6_3 : checkNodes W_6 G_6 fmask_6 P_6 autos_6 bk_6_2 3 nodes_6_3 = true := by decide +kernel
def bk_6_3 : Array (List (List Nat)) := buildBuckets 1 W_6 nodes_6_3
lemma bk_6_3_ok : ∀ i (hi : i < bk_6_3.size), ∀ xs ∈ bk_6_3[i], Impossible G_6 3 xs.toFinset :=
  buildBuckets_sound (by decide) gp_6 W_6_ok P_6_ok autos_6_ok bk_6_2_ok chk_6_3
def nodes_6_4 : List NodeSpec := [([5,0,1,2,3],[],[]),([4,6,1,2,3],[0,2],[0]),([7,0,1,2,3],[3],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_6_4 : checkNodes W_6 G_6 fmask_6 P_6 autos_6 bk_6_3 4 nodes_6_4 = true := by decide +kernel
def bk_6_4 : Array (List (List Nat)) := buildBuckets 2 W_6 nodes_6_4
lemma bk_6_4_ok : ∀ i (hi : i < bk_6_4.size), ∀ xs ∈ bk_6_4[i], Impossible G_6 4 xs.toFinset :=
  buildBuckets_sound (by decide) gp_6 W_6_ok P_6_ok autos_6_ok bk_6_3_ok chk_6_4
def nodes_6_5 : List NodeSpec := [([4,0,1,2,3],[2,1,0,3],[0,1,2,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_6_5 : checkNodes W_6 G_6 fmask_6 P_6 autos_6 bk_6_4 5 nodes_6_5 = true := by decide +kernel
def bk_6_5 : Array (List (List Nat)) := buildBuckets 1 W_6 nodes_6_5
lemma bk_6_5_ok : ∀ i (hi : i < bk_6_5.size), ∀ xs ∈ bk_6_5[i], Impossible G_6 5 xs.toFinset :=
  buildBuckets_sound (by decide) gp_6 W_6_ok P_6_ok autos_6_ok bk_6_4_ok chk_6_5
def nodes_6_6 : List NodeSpec := [([0,1,2,3],[1,2,0,3],[0,4,5,6,7,8])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_6_6 : checkNodes W_6 G_6 fmask_6 P_6 autos_6 bk_6_5 6 nodes_6_6 = true := by decide +kernel
def bk_6_6 : Array (List (List Nat)) := buildBuckets 1 W_6 nodes_6_6
lemma bk_6_6_ok : ∀ i (hi : i < bk_6_6.size), ∀ xs ∈ bk_6_6[i], Impossible G_6 6 xs.toFinset :=
  buildBuckets_sound (by decide) gp_6 W_6_ok P_6_ok autos_6_ok bk_6_5_ok chk_6_6
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma root_6_ok : forestRootCheck R_6 G_6 [(VAR 0,7,6),(VAR 1,7,5),(VAR 2,7,3),(VAR 5,35,3)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma root_6_in : bucketContains bk_6_6 R_6 = true := by decide +kernel
lemma low_6 : Lower R_6 G_6 7 := lower_of_forest root_6_ok bk_6_6_ok root_6_in

end Cofactor12196
def h22R : List Nat := varsOf 30
def h22G : Nat := 0xfcc0c000fcc0c000fcc0c000fcc0c000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Bound : Lower h22R h22G 7 := carry_of (swaps := [(4,5),(2,3),(1,2),(0,1)]) (roots2 := Cofactor12196.R_6) (T2 := Cofactor12196.G_6) (by decide +kernel) Cofactor12196.low_6
def h23R : List Nat := varsOf 46
def h23G : Nat := 0xfcc0fcc0ccc0ccc0fcc0fcc0ccc0ccc0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h23Bound : Lower h23R h23G 5 := lift_of (z := 0) (o := 32) (essPairs := [(VAR 5,12,44)]) (by decide +kernel) h3Bound
namespace Cofactor12160
def G_0 : Nat := 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0
def R_0 : List Nat := varsOf 14
def pos_0 : List Nat := [6,6,10,10,12,12,6,10,12]
def neg_0 : List Nat := [4,2,8,2,8,4,8,4,2]
def fmask_0 : Nat := fullMask 9
def base_0 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xcf,0x10a),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x173,0xa1),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x1bc,0x54)]
def steps_0 : List (Nat × Nat × Nat) := []
def W_0 : Array Decor := buildWires base_0 steps_0
def autos_0 : Array (List (Nat × Nat)) := #[]
def slicesL_0 : List (Nat × Nat) := []
def slices_0 : Array (Nat × Nat) := slicesL_0.toArray
def ps_0 : List PoolSpec := []
def P_0 : Array (Option BoundPool) := buildPools W_0 R_0 slices_0 ps_0
lemma gp_0 : goodPairs G_0 pos_0 neg_0 := goodPairs_of (by decide +kernel)
lemma base_0_ok : ∀ x ∈ base_0, faithful pos_0 neg_0 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma W_0_ok : ∀ x ∈ W_0.toList, faithful pos_0 neg_0 x ∧ x.1 < 2^128 := buildWires_faithful base_0_ok
lemma autos_0_ok : ∀ sw ∈ autos_0.toList, swapsValid sw = true ∧ permWord sw G_0 = G_0 := autos_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma slices_0_ok : ∀ i (hi : i < slices_0.size), Slice R_0 G_0 slices_0[i].1 slices_0[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice R_0 G_0 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma P_0_ok : ∀ i (hi : i < P_0.size), ∀ c, P_0[i] = some c → ValidPool R_0 G_0 c := buildPools_sound slices_0_ok
def bk_0_init : Array (List (List Nat)) := #[]
lemma bk_0_init_ok : ∀ i (hi : i < bk_0_init.size), ∀ xs ∈ bk_0_init[i], Impossible G_0 (0 - 1) xs.toFinset := by intro i hi; simp [bk_0_init] at hi
def nodes_0_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_0 : checkNodes W_0 G_0 fmask_0 P_0 autos_0 bk_0_init 0 nodes_0_0 = true := by decide +kernel
def bk_0_0 : Array (List (List Nat)) := buildBuckets 1 W_0 nodes_0_0
lemma bk_0_0_ok : ∀ i (hi : i < bk_0_0.size), ∀ xs ∈ bk_0_0[i], Impossible G_0 0 xs.toFinset :=
  buildBuckets_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_init_ok chk_0_0
def nodes_0_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_1 : checkNodes W_0 G_0 fmask_0 P_0 autos_0 bk_0_0 1 nodes_0_1 = true := by decide +kernel
def bk_0_1 : Array (List (List Nat)) := buildBuckets 1 W_0 nodes_0_1
lemma bk_0_1_ok : ∀ i (hi : i < bk_0_1.size), ∀ xs ∈ bk_0_1[i], Impossible G_0 1 xs.toFinset :=
  buildBuckets_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_0_ok chk_0_1
def nodes_0_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_2 : checkNodes W_0 G_0 fmask_0 P_0 autos_0 bk_0_1 2 nodes_0_2 = true := by decide +kernel
def bk_0_2 : Array (List (List Nat)) := buildBuckets 1 W_0 nodes_0_2
lemma bk_0_2_ok : ∀ i (hi : i < bk_0_2.size), ∀ xs ∈ bk_0_2[i], Impossible G_0 2 xs.toFinset :=
  buildBuckets_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_1_ok chk_0_2
def nodes_0_3 : List NodeSpec := [([0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_3 : checkNodes W_0 G_0 fmask_0 P_0 autos_0 bk_0_2 3 nodes_0_3 = true := by decide +kernel
def bk_0_3 : Array (List (List Nat)) := buildBuckets 1 W_0 nodes_0_3
lemma bk_0_3_ok : ∀ i (hi : i < bk_0_3.size), ∀ xs ∈ bk_0_3[i], Impossible G_0 3 xs.toFinset :=
  buildBuckets_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_2_ok chk_0_3
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma root_0_ok : forestRootCheck R_0 G_0 [(VAR 1,6,4),(VAR 2,6,2),(VAR 3,10,2)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma root_0_in : bucketContains bk_0_3 R_0 = true := by decide +kernel
lemma low_0 : Lower R_0 G_0 4 := lower_of_forest root_0_ok bk_0_3_ok root_0_in

def G_1 : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def R_1 : List Nat := varsOf 7
lemma low_1_ok : carryOK [(0,3),(0,2),(0,1)] R_1 G_1 R_0 G_0 = true := by decide +kernel
lemma low_1 : Lower R_1 G_1 4 := carry_of low_1_ok low_0

def G_3 : Nat := 0xeeee8888eeee8888eeee8888eeee8888
def R_3 : List Nat := varsOf 19
lemma low_3_ok : carryOK [(3,4),(0,2),(0,1)] R_3 G_3 R_0 G_0 = true := by decide +kernel
lemma low_3 : Lower R_3 G_3 4 := carry_of low_3_ok low_0

def G_5 : Nat := 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0
def R_5 : List Nat := varsOf 21
lemma low_5_ok : carryOK [(3,4),(0,1)] R_5 G_5 R_0 G_0 = true := by decide +kernel
lemma low_5 : Lower R_5 G_5 4 := carry_of low_5_ok low_0

def G_6 : Nat := 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0
def R_6 : List Nat := varsOf 22
lemma low_6_ok : carryOK [(3,4)] R_6 G_6 R_0 G_0 = true := by decide +kernel
lemma low_6 : Lower R_6 G_6 4 := carry_of low_6_ok low_0

def G_10 : Nat := 0xe8e88080e8e88080e8e88080e8e88080
def R_10 : List Nat := varsOf 23
def pos_10 : List Nat := [7,7,7,19,19,19,21,21,21,22,22,22,7,7,7,19,19,19,21,21,21,22,22,22]
def neg_10 : List Nat := [6,5,3,18,17,3,20,17,5,20,18,6,17,18,20,5,6,20,3,6,18,3,5,17]
def fmask_10 : Nat := fullMask 24
def base_10 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x1ff1ff,0xe491b6),(0xcccccccccccccccccccccccccccccccc,0xe3fe3f,0x3d2c2d),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfc7fc7,0x4bcb43),(0xffff0000ffff0000ffff0000ffff0000,0xff8ff8,0x9276d8)]
def steps_10 : List (Nat × Nat × Nat) := [(0,0,1),(0,0,2),(3,4,2),(0,4,2),(0,1,2),(3,7,3)]
def W_10 : Array Decor := buildWires base_10 steps_10
def autos_10 : Array (List (Nat × Nat)) := #[[],[(2,4)],[(0,1)],[(2,4),(0,1)],[(1,2)],[(1,4),(1,2)],[(0,1),(0,2)],[(1,4),(0,1),(0,2)],[(1,4),(0,2)]]
def slicesL_10 : List (Nat × Nat) := [(subcube 0 4,4),(subcube 0 1,4),(subcube 0 2,4),(subcube 0 16,4)]
def slices_10 : Array (Nat × Nat) := slicesL_10.toArray
def ps_10 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[])]
def P_10 : Array (Option BoundPool) := buildPools W_10 R_10 slices_10 ps_10
lemma gp_10 : goodPairs G_10 pos_10 neg_10 := goodPairs_of (by decide +kernel)
lemma base_10_ok : ∀ x ∈ base_10, faithful pos_10 neg_10 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma W_10_ok : ∀ x ∈ W_10.toList, faithful pos_10 neg_10 x ∧ x.1 < 2^128 := buildWires_faithful base_10_ok
lemma autos_10_ok : ∀ sw ∈ autos_10.toList, swapsValid sw = true ∧ permWord sw G_10 = G_10 := autos_of (by decide +kernel)
lemma sl_10_0_ok : sliceDirectCheck 0 4 0 R_10 G_10 R_3 G_3 = true := by decide +kernel
lemma sl_10_0 : Slice R_10 G_10 (subcube 0 4) 4 := slice_direct sl_10_0_ok low_3
lemma sl_10_1_ok : sliceDirectCheck 0 1 0 R_10 G_10 R_6 G_6 = true := by decide +kernel
lemma sl_10_1 : Slice R_10 G_10 (subcube 0 1) 4 := slice_direct sl_10_1_ok low_6
lemma sl_10_2_ok : sliceDirectCheck 0 2 0 R_10 G_10 R_5 G_5 = true := by decide +kernel
lemma sl_10_2 : Slice R_10 G_10 (subcube 0 2) 4 := slice_direct sl_10_2_ok low_5
lemma sl_10_3_ok : sliceDirectCheck 0 16 0 R_10 G_10 R_1 G_1 = true := by decide +kernel
lemma sl_10_3 : Slice R_10 G_10 (subcube 0 16) 4 := slice_direct sl_10_3_ok low_1
set_option maxRecDepth 200000 in
lemma slices_10_ok : ∀ i (hi : i < slices_10.size), Slice R_10 G_10 slices_10[i].1 slices_10[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice R_10 G_10 p.1 p.2) (forall_cons sl_10_0 (forall_cons sl_10_1 (forall_cons sl_10_2 (forall_cons sl_10_3 (fun _ h => (List.not_mem_nil h).elim)))))
lemma P_10_ok : ∀ i (hi : i < P_10.size), ∀ c, P_10[i] = some c → ValidPool R_10 G_10 c := buildPools_sound slices_10_ok
def bk_10_init : Array (List (List Nat)) := #[]
lemma bk_10_init_ok : ∀ i (hi : i < bk_10_init.size), ∀ xs ∈ bk_10_init[i], Impossible G_10 (0 - 1) xs.toFinset := by intro i hi; simp [bk_10_init] at hi
def nodes_10_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_10_0 : checkNodes W_10 G_10 fmask_10 P_10 autos_10 bk_10_init 0 nodes_10_0 = true := by decide +kernel
def bk_10_0 : Array (List (List Nat)) := buildBuckets 1 W_10 nodes_10_0
lemma bk_10_0_ok : ∀ i (hi : i < bk_10_0.size), ∀ xs ∈ bk_10_0[i], Impossible G_10 0 xs.toFinset :=
  buildBuckets_sound (by decide) gp_10 W_10_ok P_10_ok autos_10_ok bk_10_init_ok chk_10_0
def nodes_10_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_10_1 : checkNodes W_10 G_10 fmask_10 P_10 autos_10 bk_10_0 1 nodes_10_1 = true := by decide +kernel
def bk_10_1 : Array (List (List Nat)) := buildBuckets 1 W_10 nodes_10_1
lemma bk_10_1_ok : ∀ i (hi : i < bk_10_1.size), ∀ xs ∈ bk_10_1[i], Impossible G_10 1 xs.toFinset :=
  buildBuckets_sound (by decide) gp_10 W_10_ok P_10_ok autos_10_ok bk_10_0_ok chk_10_1
def nodes_10_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_10_2 : checkNodes W_10 G_10 fmask_10 P_10 autos_10 bk_10_1 2 nodes_10_2 = true := by decide +kernel
def bk_10_2 : Array (List (List Nat)) := buildBuckets 1 W_10 nodes_10_2
lemma bk_10_2_ok : ∀ i (hi : i < bk_10_2.size), ∀ xs ∈ bk_10_2[i], Impossible G_10 2 xs.toFinset :=
  buildBuckets_sound (by decide) gp_10 W_10_ok P_10_ok autos_10_ok bk_10_1_ok chk_10_2
def nodes_10_3 : List NodeSpec := [([4,5,8,3],[0,1],[]),([9,0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_10_3 : checkNodes W_10 G_10 fmask_10 P_10 autos_10 bk_10_2 3 nodes_10_3 = true := by decide +kernel
def bk_10_3 : Array (List (List Nat)) := buildBuckets 1 W_10 nodes_10_3
lemma bk_10_3_ok : ∀ i (hi : i < bk_10_3.size), ∀ xs ∈ bk_10_3[i], Impossible G_10 3 xs.toFinset :=
  buildBuckets_sound (by decide) gp_10 W_10_ok P_10_ok autos_10_ok bk_10_2_ok chk_10_3
def nodes_10_4 : List NodeSpec := [([4,5,1,2,3],[0,2],[0]),([6,0,1,2,3],[],[]),([7,0,1,2,3],[3],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_10_4 : checkNodes W_10 G_10 fmask_10 P_10 autos_10 bk_10_3 4 nodes_10_4 = true := by decide +kernel
def bk_10_4 : Array (List (List Nat)) := buildBuckets 2 W_10 nodes_10_4
lemma bk_10_4_ok : ∀ i (hi : i < bk_10_4.size), ∀ xs ∈ bk_10_4[i], Impossible G_10 4 xs.toFinset :=
  buildBuckets_sound (by decide) gp_10 W_10_ok P_10_ok autos_10_ok bk_10_3_ok chk_10_4
def nodes_10_5 : List NodeSpec := [([4,0,1,2,3],[2,1,0,3],[0,1,2,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_10_5 : checkNodes W_10 G_10 fmask_10 P_10 autos_10 bk_10_4 5 nodes_10_5 = true := by decide +kernel
def bk_10_5 : Array (List (List Nat)) := buildBuckets 1 W_10 nodes_10_5
lemma bk_10_5_ok : ∀ i (hi : i < bk_10_5.size), ∀ xs ∈ bk_10_5[i], Impossible G_10 5 xs.toFinset :=
  buildBuckets_sound (by decide) gp_10 W_10_ok P_10_ok autos_10_ok bk_10_4_ok chk_10_5
def nodes_10_6 : List NodeSpec := [([0,1,2,3],[1,2,0,3],[0,4,5,6,7,8])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_10_6 : checkNodes W_10 G_10 fmask_10 P_10 autos_10 bk_10_5 6 nodes_10_6 = true := by decide +kernel
def bk_10_6 : Array (List (List Nat)) := buildBuckets 1 W_10 nodes_10_6
lemma bk_10_6_ok : ∀ i (hi : i < bk_10_6.size), ∀ xs ∈ bk_10_6[i], Impossible G_10 6 xs.toFinset :=
  buildBuckets_sound (by decide) gp_10 W_10_ok P_10_ok autos_10_ok bk_10_5_ok chk_10_6
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma root_10_ok : forestRootCheck R_10 G_10 [(VAR 0,7,6),(VAR 1,7,5),(VAR 2,7,3),(VAR 4,19,3)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma root_10_in : bucketContains bk_10_6 R_10 = true := by decide +kernel
lemma low_10 : Lower R_10 G_10 7 := lower_of_forest root_10_ok bk_10_6_ok root_10_in

def G_39 : Nat := 0xe8e88080e8e80000e8e88080e8e80000
def R_39 : List Nat := varsOf 55
lemma low_39_ok : liftCheck 0 32 R_39 G_39 R_10 G_10 [(VAR 5,39,7)] = true := by decide +kernel
lemma low_39 : Lower R_39 G_39 8 := lift_of low_39_ok low_10

end Cofactor12160
def h24R : List Nat := varsOf 62
def h24G : Nat := 0xfcc0c000ccc0c000fcc0c000ccc0c000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h24Bound : Lower h24R h24G 8 := carry_of (swaps := [(2,3),(3,4),(1,2),(2,3),(0,1),(1,2)]) (roots2 := Cofactor12160.R_39) (T2 := Cofactor12160.G_39) (by decide +kernel) Cofactor12160.low_39
def h25R : List Nat := varsOf 31
def h25G : Nat := 0xfeeaeaaafeeaeaaafeeaeaaafeeaeaaa
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h25Bound : Lower h25R h25G 8 := lift_of (z := 1) (o := 0) (essPairs := [(VAR 0,0,1)]) (by decide +kernel) h22Bound
def h26R : List Nat := varsOf 46
def h26G : Nat := 0xfffffffffcc0fcc0fffffffffcc0fcc0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Bound : Lower h26R h26G 5 := lift_of (z := 32) (o := 0) (essPairs := [(VAR 5,0,32)]) (by decide +kernel) h3Bound
def h28R : List Nat := varsOf 15
def h28G : Nat := 0xecc0ecc0ecc0ecc0ecc0ecc0ecc0ecc0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h28Bound : Lower h28R h28G 5 := lift_of (z := 0) (o := 1) (essPairs := [(VAR 0,12,13)]) (by decide +kernel) h3Bound
def h29R : List Nat := varsOf 15
def h29G : Nat := 0xfeeafeeafeeafeeafeeafeeafeeafeea
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Bound : Lower h29R h29G 5 := lift_of (z := 1) (o := 0) (essPairs := [(VAR 0,0,1)]) (by decide +kernel) h3Bound
def h30R : List Nat := varsOf 39
def h30G : Nat := 0xfefefefeececececfefefefeecececec
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h30Bound : Lower h30R h30G 5 := lift_of (z := 2) (o := 0) (essPairs := [(VAR 1,0,2)]) (by decide +kernel) h15Bound
def h31R : List Nat := varsOf 43
def h31G : Nat := 0xffeeffeeeecceeccffeeffeeeecceecc
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Bound : Lower h31R h31G 5 := lift_of (z := 2) (o := 0) (essPairs := [(VAR 1,0,2)]) (by decide +kernel) h16Bound
def h27R : List Nat := varsOf 47
def h27G : Nat := 0xfeeafeeaecc0ecc0feeafeeaecc0ecc0
def h27Pos : List Nat := [6,13,7,35,6,7,10,11,44,33,10,13,13,35,38,14,38,42]
def h27Neg : List Nat := [4,12,5,34,2,3,2,3,12,1,8,9,5,3,36,12,34,34]
def h27Mask : Nat := fullMask 18
def h27Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x3aae,0x3aa4),(0xcccccccccccccccccccccccccccccccc,0x3e4fd,0x320f8),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x1d937,0xd107),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x29dc2,0x8d02),(0xffffffff00000000ffffffff00000000,0x36308,0x34008)]
def h27Steps : List (Nat × Nat × Nat) := [(0,2,3)]
def h27W : Array Decor := buildWires h27Base h27Steps
def h27Autos : Array (List (Nat × Nat)) := #[[]]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27Pairs : goodPairs h27G h27Pos h27Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27BaseOk : ∀ x ∈ h27Base, faithful h27Pos h27Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27WOk : ∀ x ∈ h27W.toList, faithful h27Pos h27Neg x ∧ x.1 < 2^128 := buildWires_faithful h27BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27AutosOk : ∀ sw ∈ h27Autos.toList, swapsValid sw = true ∧ permWord sw h27G = h27G := autos_of (by decide +kernel)
def h27SliceList : List (Nat × Nat) := [(subcube 0 1,5),(subcube 0 4,5),(subcube 0 8,5),(subcube 0 32,5),(subcube 1 0,5),(subcube 2 0,5),(subcube 2 4,4),(subcube 2 8,4),(subcube 32 0,5)]
def h27Slices : Array (Nat × Nat) := h27SliceList.toArray
def h27Specs : List PoolSpec := [(4,[]),(0,[]),(5,[]),(1,[]),(6,[]),(2,[]),(7,[]),(3,[]),(8,[]),(5,[(0,2,3)])]
def h27Pools : Array (Option BoundPool) := buildPools h27W h27R h27Slices h27Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27Slice8 : Slice h27R h27G (subcube 32 0) 5 := slice_direct (zDead := 0) (by decide +kernel) h28Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27Slice7 : Slice h27R h27G (subcube 2 8) 4 := slice_direct (zDead := 0) (by decide +kernel) h15Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27Slice6 : Slice h27R h27G (subcube 2 4) 4 := slice_direct (zDead := 0) (by decide +kernel) h16Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27Slice5 : Slice h27R h27G (subcube 2 0) 5 := slice_direct (zDead := 0) (by decide +kernel) h17Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27Slice4 : Slice h27R h27G (subcube 1 0) 5 := slice_direct (zDead := 0) (by decide +kernel) h23Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27Slice3 : Slice h27R h27G (subcube 0 32) 5 := slice_direct (zDead := 0) (by decide +kernel) h29Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27Slice2 : Slice h27R h27G (subcube 0 8) 5 := slice_direct (zDead := 0) (by decide +kernel) h30Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27Slice1 : Slice h27R h27G (subcube 0 4) 5 := slice_direct (zDead := 0) (by decide +kernel) h31Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27Slice0 : Slice h27R h27G (subcube 0 1) 5 := slice_direct (zDead := 0) (by decide +kernel) h26Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27SlicesOk : ∀ i (hi : i < h27Slices.size), Slice h27R h27G h27Slices[i].1 h27Slices[i].2 := array_forall_of_list (P := fun (p : Nat × Nat) => Slice h27R h27G p.1 p.2) (forall_cons h27Slice0 (forall_cons h27Slice1 (forall_cons h27Slice2 (forall_cons h27Slice3 (forall_cons h27Slice4 (forall_cons h27Slice5 (forall_cons h27Slice6 (forall_cons h27Slice7 (forall_cons h27Slice8 (fun _ h => (List.not_mem_nil h).elim))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27PoolsOk : ∀ i (hi : i < h27Pools.size), ∀ c, h27Pools[i] = some c → ValidPool h27R h27G c := buildPools_sound h27SlicesOk
def h27Empty : Array (List (List Nat)) := #[]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27EmptyOk : ∀ i (hi : i < h27Empty.size), ∀ xs ∈ h27Empty[i], Impossible h27G (6 - 1) xs.toFinset := by intro i hi; simp [h27Empty] at hi
def h27Block6_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,4,5,7,8,9],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27Test6_0 : checkNodes h27W h27G h27Mask h27Pools h27Autos h27Empty 6 h27Block6_0 = true := by decide +kernel
def h27Nodes6 : List NodeSpec := h27Block6_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27Check6 : checkNodes h27W h27G h27Mask h27Pools h27Autos h27Empty 6 h27Nodes6 = true := h27Test6_0
def h27Bucket6 : Array (List (List Nat)) := buildBuckets 1 h27W h27Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27Bucket6Ok : ∀ i (hi : i < h27Bucket6.size), ∀ xs ∈ h27Bucket6[i], Impossible h27G 6 xs.toFinset := buildBuckets_sound (by decide) h27Pairs h27WOk h27PoolsOk h27AutosOk h27EmptyOk h27Check6
def h27Block7_0 : List NodeSpec := [([0,1,2,3,4],[0,1,2,3,4,5,6,7,8],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27Test7_0 : checkNodes h27W h27G h27Mask h27Pools h27Autos h27Bucket6 7 h27Block7_0 = true := by decide +kernel
def h27Nodes7 : List NodeSpec := h27Block7_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27Check7 : checkNodes h27W h27G h27Mask h27Pools h27Autos h27Bucket6 7 h27Nodes7 = true := h27Test7_0
def h27Bucket7 : Array (List (List Nat)) := buildBuckets 1 h27W h27Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27Bucket7Ok : ∀ i (hi : i < h27Bucket7.size), ∀ xs ∈ h27Bucket7[i], Impossible h27G 7 xs.toFinset := buildBuckets_sound (by decide) h27Pairs h27WOk h27PoolsOk h27AutosOk h27Bucket6Ok h27Check7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27Bound : Lower h27R h27G 8 := lower_of_forest (essPairs := [(VAR 0,12,13),(VAR 1,4,6),(VAR 2,2,6),(VAR 3,2,10),(VAR 5,1,33)]) (by decide +kernel) h27Bucket7Ok (by decide +kernel)
namespace Cofactor12160
def G_8 : Nat := 0xffccffcccc00cc00ffccffcccc00cc00
def R_8 : List Nat := varsOf 42
lemma low_8_ok : carryOK [(3,5),(2,3),(2,4)] R_8 G_8 R_0 G_0 = true := by decide +kernel
lemma low_8 : Lower R_8 G_8 4 := carry_of low_8_ok low_0

def G_9 : Nat := 0xfff0fff0f000f000fff0fff0f000f000
def R_9 : List Nat := varsOf 44
lemma low_9_ok : carryOK [(3,5),(2,3),(1,2),(1,4)] R_9 G_9 R_0 G_0 = true := by decide +kernel
lemma low_9 : Lower R_9 G_9 4 := carry_of low_9_ok low_0

def G_12 : Nat := 0xfcc0fc00fcc0fc00fcc0fc00fcc0fc00
def R_12 : List Nat := varsOf 30
lemma low_12_ok : liftCheck 0 16 R_12 G_12 R_0 G_0 [(VAR 4,22,6)] = true := by decide +kernel
lemma low_12 : Lower R_12 G_12 5 := lift_of low_12_ok low_0

def G_14 : Nat := 0xffc0ffc0c000c000ffc0ffc0c000c000
def R_14 : List Nat := varsOf 46
lemma low_14_ok : liftCheck 0 2 R_14 G_14 R_9 G_9 [(VAR 1,14,12)] = true := by decide +kernel
lemma low_14 : Lower R_14 G_14 5 := lift_of low_14_ok low_9

def G_15 : Nat := 0xfff0ff00fff00000fff0ff00fff00000
def R_15 : List Nat := varsOf 60
def pos_15 : List Nat := [20,20,24,24,28,40,40,44,44,52,52,56,20,20,20,24,24,24,40,40,40]
def neg_15 : List Nat := [16,4,16,8,12,32,8,36,12,48,36,48,12,36,48,12,36,48,12,36,48]
def fmask_15 : Nat := fullMask 21
def base_15 : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x7793,0xdb592),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x1f89fc,0x49158),(0xffff0000ffff0000ffff0000ffff0000,0x3fe1f,0x124a05),(0xffffffff00000000ffffffff00000000,0x1c0fe0,0x1b6ea0)]
def steps_15 : List (Nat × Nat × Nat) := []
def W_15 : Array Decor := buildWires base_15 steps_15
def autos_15 : Array (List (Nat × Nat)) := #[]
def slicesL_15 : List (Nat × Nat) := []
def slices_15 : Array (Nat × Nat) := slicesL_15.toArray
def ps_15 : List PoolSpec := []
def P_15 : Array (Option BoundPool) := buildPools W_15 R_15 slices_15 ps_15
lemma gp_15 : goodPairs G_15 pos_15 neg_15 := goodPairs_of (by decide +kernel)
lemma base_15_ok : ∀ x ∈ base_15, faithful pos_15 neg_15 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma W_15_ok : ∀ x ∈ W_15.toList, faithful pos_15 neg_15 x ∧ x.1 < 2^128 := buildWires_faithful base_15_ok
lemma autos_15_ok : ∀ sw ∈ autos_15.toList, swapsValid sw = true ∧ permWord sw G_15 = G_15 := autos_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma slices_15_ok : ∀ i (hi : i < slices_15.size), Slice R_15 G_15 slices_15[i].1 slices_15[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice R_15 G_15 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma P_15_ok : ∀ i (hi : i < P_15.size), ∀ c, P_15[i] = some c → ValidPool R_15 G_15 c := buildPools_sound slices_15_ok
def bk_15_init : Array (List (List Nat)) := #[]
lemma bk_15_init_ok : ∀ i (hi : i < bk_15_init.size), ∀ xs ∈ bk_15_init[i], Impossible G_15 (0 - 1) xs.toFinset := by intro i hi; simp [bk_15_init] at hi
def nodes_15_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_15_0 : checkNodes W_15 G_15 fmask_15 P_15 autos_15 bk_15_init 0 nodes_15_0 = true := by decide +kernel
def bk_15_0 : Array (List (List Nat)) := buildBuckets 1 W_15 nodes_15_0
lemma bk_15_0_ok : ∀ i (hi : i < bk_15_0.size), ∀ xs ∈ bk_15_0[i], Impossible G_15 0 xs.toFinset :=
  buildBuckets_sound (by decide) gp_15 W_15_ok P_15_ok autos_15_ok bk_15_init_ok chk_15_0
def nodes_15_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_15_1 : checkNodes W_15 G_15 fmask_15 P_15 autos_15 bk_15_0 1 nodes_15_1 = true := by decide +kernel
def bk_15_1 : Array (List (List Nat)) := buildBuckets 1 W_15 nodes_15_1
lemma bk_15_1_ok : ∀ i (hi : i < bk_15_1.size), ∀ xs ∈ bk_15_1[i], Impossible G_15 1 xs.toFinset :=
  buildBuckets_sound (by decide) gp_15 W_15_ok P_15_ok autos_15_ok bk_15_0_ok chk_15_1
def nodes_15_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_15_2 : checkNodes W_15 G_15 fmask_15 P_15 autos_15 bk_15_1 2 nodes_15_2 = true := by decide +kernel
def bk_15_2 : Array (List (List Nat)) := buildBuckets 1 W_15 nodes_15_2
lemma bk_15_2_ok : ∀ i (hi : i < bk_15_2.size), ∀ xs ∈ bk_15_2[i], Impossible G_15 2 xs.toFinset :=
  buildBuckets_sound (by decide) gp_15 W_15_ok P_15_ok autos_15_ok bk_15_1_ok chk_15_2
def nodes_15_3 : List NodeSpec := [([0,1,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_15_3 : checkNodes W_15 G_15 fmask_15 P_15 autos_15 bk_15_2 3 nodes_15_3 = true := by decide +kernel
def bk_15_3 : Array (List (List Nat)) := buildBuckets 1 W_15 nodes_15_3
lemma bk_15_3_ok : ∀ i (hi : i < bk_15_3.size), ∀ xs ∈ bk_15_3[i], Impossible G_15 3 xs.toFinset :=
  buildBuckets_sound (by decide) gp_15 W_15_ok P_15_ok autos_15_ok bk_15_2_ok chk_15_3
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma root_15_ok : forestRootCheck R_15 G_15 [(VAR 2,20,16),(VAR 3,24,16),(VAR 4,20,4),(VAR 5,40,8)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma root_15_in : bucketContains bk_15_3 R_15 = true := by decide +kernel
lemma low_15 : Lower R_15 G_15 4 := lower_of_forest root_15_ok bk_15_3_ok root_15_in

def G_16 : Nat := 0xfffcc000fffcc000fffcc000fffcc000
def R_16 : List Nat := varsOf 30
def pos_16 : List Nat := [14,14,14,18,18,20,20,22,24,24,26,28,14,18,18,18,20,20,20,24,24,24]
def neg_16 : List Nat := [12,10,6,16,2,16,4,6,16,8,10,12,16,6,10,12,6,10,12,6,10,12]
def fmask_16 : Nat := fullMask 22
def base_16 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xf49f,0x1b6496),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x718e7,0x2da8c5),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x381f07,0x36ce03),(0xffff0000ffff0000ffff0000ffff0000,0x3feff8,0x1128)]
def steps_16 : List (Nat × Nat × Nat) := [(3,0,3),(2,0,3),(0,0,3),(2,0,1),(1,0,1),(1,0,3),(0,0,1),(3,1,9),(0,1,9),(1,6,1),(3,0,1),(3,7,2),(1,7,2),(3,6,1),(3,10,8)]
def W_16 : Array Decor := buildWires base_16 steps_16
def autos_16 : Array (List (Nat × Nat)) := #[[],[(2,3)],[(1,2)],[(1,3),(1,2)],[(1,2),(1,3)],[(1,3)]]
def slicesL_16 : List (Nat × Nat) := []
def slices_16 : Array (Nat × Nat) := slicesL_16.toArray
def ps_16 : List PoolSpec := []
def P_16 : Array (Option BoundPool) := buildPools W_16 R_16 slices_16 ps_16
lemma gp_16 : goodPairs G_16 pos_16 neg_16 := goodPairs_of (by decide +kernel)
lemma base_16_ok : ∀ x ∈ base_16, faithful pos_16 neg_16 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma W_16_ok : ∀ x ∈ W_16.toList, faithful pos_16 neg_16 x ∧ x.1 < 2^128 := buildWires_faithful base_16_ok
lemma autos_16_ok : ∀ sw ∈ autos_16.toList, swapsValid sw = true ∧ permWord sw G_16 = G_16 := autos_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma slices_16_ok : ∀ i (hi : i < slices_16.size), Slice R_16 G_16 slices_16[i].1 slices_16[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice R_16 G_16 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma P_16_ok : ∀ i (hi : i < P_16.size), ∀ c, P_16[i] = some c → ValidPool R_16 G_16 c := buildPools_sound slices_16_ok
def bk_16_init : Array (List (List Nat)) := #[]
lemma bk_16_init_ok : ∀ i (hi : i < bk_16_init.size), ∀ xs ∈ bk_16_init[i], Impossible G_16 (0 - 1) xs.toFinset := by intro i hi; simp [bk_16_init] at hi
def nodes_16_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_16_0 : checkNodes W_16 G_16 fmask_16 P_16 autos_16 bk_16_init 0 nodes_16_0 = true := by decide +kernel
def bk_16_0 : Array (List (List Nat)) := buildBuckets 1 W_16 nodes_16_0
lemma bk_16_0_ok : ∀ i (hi : i < bk_16_0.size), ∀ xs ∈ bk_16_0[i], Impossible G_16 0 xs.toFinset :=
  buildBuckets_sound (by decide) gp_16 W_16_ok P_16_ok autos_16_ok bk_16_init_ok chk_16_0
def nodes_16_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_16_1 : checkNodes W_16 G_16 fmask_16 P_16 autos_16 bk_16_0 1 nodes_16_1 = true := by decide +kernel
def bk_16_1 : Array (List (List Nat)) := buildBuckets 1 W_16 nodes_16_1
lemma bk_16_1_ok : ∀ i (hi : i < bk_16_1.size), ∀ xs ∈ bk_16_1[i], Impossible G_16 1 xs.toFinset :=
  buildBuckets_sound (by decide) gp_16 W_16_ok P_16_ok autos_16_ok bk_16_0_ok chk_16_1
def nodes_16_2 : List NodeSpec := [([18,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_16_2 : checkNodes W_16 G_16 fmask_16 P_16 autos_16 bk_16_1 2 nodes_16_2 = true := by decide +kernel
def bk_16_2 : Array (List (List Nat)) := buildBuckets 1 W_16 nodes_16_2
lemma bk_16_2_ok : ∀ i (hi : i < bk_16_2.size), ∀ xs ∈ bk_16_2[i], Impossible G_16 2 xs.toFinset :=
  buildBuckets_sound (by decide) gp_16 W_16_ok P_16_ok autos_16_ok bk_16_1_ok chk_16_2
def nodes_16_3 : List NodeSpec := [([5,4,1,2],[],[]),([11,0,2,3],[],[]),([0,12,2,3],[],[]),([0,13,2,3],[],[]),([7,14,2,3],[],[0]),([0,1,15,3],[],[]),([0,1,16,3],[],[]),([17,0,2,3],[],[]),([10,8,2,3],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_16_3 : checkNodes W_16 G_16 fmask_16 P_16 autos_16 bk_16_2 3 nodes_16_3 = true := by decide +kernel
def bk_16_3 : Array (List (List Nat)) := buildBuckets 4 W_16 nodes_16_3
lemma bk_16_3_ok : ∀ i (hi : i < bk_16_3.size), ∀ xs ∈ bk_16_3[i], Impossible G_16 3 xs.toFinset :=
  buildBuckets_sound (by decide) gp_16 W_16_ok P_16_ok autos_16_ok bk_16_2_ok chk_16_3
def nodes_16_4 : List NodeSpec := [([4,0,1,2,3],[],[0]),([5,0,1,2,3],[],[0]),([6,0,1,2,3],[],[0,1]),([7,0,1,2,3],[],[0]),([0,1,8,2,3],[],[0]),([0,1,2,3,9],[],[0,1]),([10,0,1,2,3],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_16_4 : checkNodes W_16 G_16 fmask_16 P_16 autos_16 bk_16_3 4 nodes_16_4 = true := by decide +kernel
def bk_16_4 : Array (List (List Nat)) := buildBuckets 3 W_16 nodes_16_4
lemma bk_16_4_ok : ∀ i (hi : i < bk_16_4.size), ∀ xs ∈ bk_16_4[i], Impossible G_16 4 xs.toFinset :=
  buildBuckets_sound (by decide) gp_16 W_16_ok P_16_ok autos_16_ok bk_16_3_ok chk_16_4
def nodes_16_5 : List NodeSpec := [([0,1,2,3],[],[0,2,1,3,4,5])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_16_5 : checkNodes W_16 G_16 fmask_16 P_16 autos_16 bk_16_4 5 nodes_16_5 = true := by decide +kernel
def bk_16_5 : Array (List (List Nat)) := buildBuckets 1 W_16 nodes_16_5
lemma bk_16_5_ok : ∀ i (hi : i < bk_16_5.size), ∀ xs ∈ bk_16_5[i], Impossible G_16 5 xs.toFinset :=
  buildBuckets_sound (by decide) gp_16 W_16_ok P_16_ok autos_16_ok bk_16_4_ok chk_16_5
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma root_16_ok : forestRootCheck R_16 G_16 [(VAR 1,14,12),(VAR 2,14,10),(VAR 3,14,6),(VAR 4,18,2)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma root_16_in : bucketContains bk_16_5 R_16 = true := by decide +kernel
lemma low_16 : Lower R_16 G_16 6 := lower_of_forest root_16_ok bk_16_5_ok root_16_in

def G_17 : Nat := 0xfffffff0fffff000fffffff0fffff000
def R_17 : List Nat := varsOf 60
lemma low_17_ok : liftCheck 16 0 R_17 G_17 R_9 G_9 [(VAR 4,16,0)] = true := by decide +kernel
lemma low_17 : Lower R_17 G_17 5 := lift_of low_17_ok low_9

def G_25 : Nat := 0xfcfcc0c0fcfc0000fcfcc0c0fcfc0000
def R_25 : List Nat := varsOf 54
lemma low_25_ok : carryOK [(3,4),(3,5)] R_25 G_25 R_12 G_12 = true := by decide +kernel
lemma low_25 : Lower R_25 G_25 5 := carry_of low_25_ok low_12

def G_32 : Nat := 0xffccff00ffcc0000ffccff00ffcc0000
def R_32 : List Nat := varsOf 58
lemma low_32_ok : carryOK [(1,2)] R_32 G_32 R_15 G_15 = true := by decide +kernel
lemma low_32 : Lower R_32 G_32 4 := carry_of low_32_ok low_15

def G_37 : Nat := 0xfffcffc0fffcffc0fffcffc0fffcffc0
def R_37 : List Nat := varsOf 30
lemma low_37_ok : carryOK [(1,5),(1,4),(1,3),(1,2)] R_37 G_37 R_17 G_17 = true := by decide +kernel
lemma low_37 : Lower R_37 G_37 5 := carry_of low_37_ok low_17

def G_38 : Nat := 0xffffffccffffcc00ffffffccffffcc00
def R_38 : List Nat := varsOf 58
lemma low_38_ok : carryOK [(1,2)] R_38 G_38 R_17 G_17 = true := by decide +kernel
lemma low_38 : Lower R_38 G_38 5 := carry_of low_38_ok low_17

def G_45 : Nat := 0xfffcffc0fffcc000fffcffc0fffcc000
def R_45 : List Nat := varsOf 62
def pos_45 : List Nat := [14,14,14,18,18,20,20,22,24,24,26,28,38,38,38,40,40,42,42,44,44,50,50,52,52,56,14,14,14,18,18,18,18,18,18,20,20,20,20,20,20,24,24,24,24,24,24,38,38,38,40,40,40,40,40,40]
def neg_45 : List Nat := [12,10,6,16,2,16,4,6,16,8,10,12,36,34,6,32,8,34,10,36,12,48,34,48,36,48,34,36,48,6,10,12,34,36,48,6,10,12,34,36,48,6,10,12,34,36,48,10,12,48,6,10,12,34,36,48]
def fmask_45 : Nat := fullMask 56
def base_45 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0x38007fc66749f,0x2c965964466496),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x381f81d9878e7,0x552aaaa91858c5),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xfc7e001e1f8f07,0x198c30c0150e03),(0xffff0000ffff0000ffff0000ffff0000,0x7fffe3e00ff8,0x82410412a00128),(0xffffffff00000000ffffffff00000000,0xff800003fff000,0xe271c71feab000)]
def steps_45 : List (Nat × Nat × Nat) := [(1,2,3),(2,0,4),(3,0,3),(0,2,3),(1,0,4),(1,0,3),(0,0,3),(1,3,4),(3,0,2),(3,3,4),(2,2,3),(0,0,2),(2,0,2),(1,2,4),(1,0,2),(2,3,4),(2,2,4),(0,0,1),(1,0,1),(3,2,3),(2,0,3),(2,0,1),(1,21,3),(3,21,0),(3,3,18),(1,1,2),(3,15,0),(2,1,2),(2,0,5),(0,0,5),(1,0,8),(0,1,9),(0,0,12),(2,0,8),(1,7,4),(1,7,2),(1,26,2),(2,22,2),(3,16,1),(3,13,1),(3,2,10),(2,1,4),(1,11,2),(3,11,1),(2,22,3),(1,11,1),(0,0,18),(0,1,19),(1,13,1),(1,1,3),(2,23,2),(1,17,1),(1,11,4),(2,19,4),(3,11,2),(2,1,3),(1,22,2),(3,22,2),(1,8,4),(3,6,1),(1,22,3),(0,1,10),(1,17,3),(3,17,1),(1,24,4),(3,1,10),(3,0,1),(1,22,4),(1,6,3),(1,16,3),(1,28,3),(1,51,3),(1,21,7),(3,7,18),(3,21,10),(0,10,18),(3,46,10),(3,11,18),(2,47,4),(1,66,4),(1,47,4),(3,37,1),(2,61,4),(1,66,2),(1,17,13),(3,17,54),(3,17,10),(1,21,26),(3,22,23),(3,16,54),(3,32,0),(3,46,0),(0,0,30),(1,64,3),(1,68,3),(1,43,3),(3,21,1),(1,21,11),(3,26,18),(1,32,26),(3,21,23),(3,22,12),(1,21,22),(0,23,18),(3,66,2),(3,22,5),(3,22,19),(3,2,65),(0,22,12),(1,42,3),(3,22,18),(1,49,2),(1,61,3),(2,61,3),(0,61,4),(1,15,22),(2,88,4),(1,113,2),(1,93,2),(2,93,4),(3,93,2),(1,119,3),(1,93,4),(3,14,61),(2,23,61),(0,93,2),(0,61,12),(3,62,23),(3,124,2),(1,129,4),(1,124,2)]
def W_45 : Array Decor := buildWires base_45 steps_45
def autos_45 : Array (List (Nat × Nat)) := #[[],[(1,2)]]
def slicesL_45 : List (Nat × Nat) := [(subcube 0 2,5),(subcube 32 0,6),(subcube 16 4,4),(subcube 0 32,5),(subcube 4 0,4),(subcube 0 4,5),(subcube 8 0,5),(subcube 2 0,4),(subcube 16 2,4),(subcube 8 32,4),(subcube 16 0,5)]
def slices_45 : Array (Nat × Nat) := slicesL_45.toArray
def ps_45 : List PoolSpec := [(0,[]),(1,[(0,0,1),(1,0,1),(3,22,23)]),(2,[]),(1,[]),(3,[]),(4,[]),(5,[]),(1,[(2,0,3),(3,0,3)]),(6,[]),(7,[]),(8,[]),(1,[(0,0,3),(1,11,2)]),(1,[(1,0,3),(0,1,10)]),(9,[]),(1,[(0,0,3),(1,11,1)]),(1,[(0,0,3),(3,11,1)]),(1,[(2,1,2),(3,32,0)]),(10,[]),(1,[(0,0,3),(1,21,11)]),(1,[(1,0,3),(3,1,10)]),(1,[(0,0,1),(1,0,1)]),(1,[(1,21,3)]),(1,[(3,21,0)]),(1,[(3,3,18)]),(1,[(2,2,3)]),(1,[(1,1,2)]),(1,[(1,0,2)]),(1,[(1,2,3)]),(1,[(1,0,1)]),(1,[(2,0,1),(1,26,2)]),(1,[(1,0,3)]),(1,[(1,0,3),(3,2,10)]),(1,[(0,0,3)]),(1,[(2,1,2)]),(1,[(0,0,18)]),(1,[(2,0,2)]),(1,[(0,0,1)]),(1,[(0,0,2)]),(1,[(2,0,1)]),(1,[(2,0,3)]),(1,[(3,6,1)]),(1,[(2,0,2),(3,17,1)]),(1,[(3,0,3)]),(1,[(2,0,1),(3,0,1)])]
def P_45 : Array (Option BoundPool) := buildPools W_45 R_45 slices_45 ps_45
lemma gp_45 : goodPairs G_45 pos_45 neg_45 := goodPairs_of (by decide +kernel)
lemma base_45_ok : ∀ x ∈ base_45, faithful pos_45 neg_45 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma W_45_ok : ∀ x ∈ W_45.toList, faithful pos_45 neg_45 x ∧ x.1 < 2^128 := buildWires_faithful base_45_ok
lemma autos_45_ok : ∀ sw ∈ autos_45.toList, swapsValid sw = true ∧ permWord sw G_45 = G_45 := autos_of (by decide +kernel)
lemma sl_45_0_ok : sliceDirectCheck 0 2 0 R_45 G_45 R_17 G_17 = true := by decide +kernel
lemma sl_45_0 : Slice R_45 G_45 (subcube 0 2) 5 := slice_direct sl_45_0_ok low_17
lemma sl_45_1_ok : sliceDirectCheck 32 0 0 R_45 G_45 R_16 G_16 = true := by decide +kernel
lemma sl_45_1 : Slice R_45 G_45 (subcube 32 0) 6 := slice_direct sl_45_1_ok low_16
lemma sl_45_2_ok : sliceDirectCheck 16 4 0 R_45 G_45 R_8 G_8 = true := by decide +kernel
lemma sl_45_2 : Slice R_45 G_45 (subcube 16 4) 4 := slice_direct sl_45_2_ok low_8
lemma sl_45_3_ok : sliceDirectCheck 0 32 0 R_45 G_45 R_37 G_37 = true := by decide +kernel
lemma sl_45_3 : Slice R_45 G_45 (subcube 0 32) 5 := slice_direct sl_45_3_ok low_37
lemma sl_45_4_ok : sliceDirectCheck 4 0 0 R_45 G_45 R_32 G_32 = true := by decide +kernel
lemma sl_45_4 : Slice R_45 G_45 (subcube 4 0) 4 := slice_direct sl_45_4_ok low_32
lemma sl_45_5_ok : sliceDirectCheck 0 4 0 R_45 G_45 R_38 G_38 = true := by decide +kernel
lemma sl_45_5 : Slice R_45 G_45 (subcube 0 4) 5 := slice_direct sl_45_5_ok low_38
lemma sl_45_6_ok : sliceDirectCheck 8 0 0 R_45 G_45 R_25 G_25 = true := by decide +kernel
lemma sl_45_6 : Slice R_45 G_45 (subcube 8 0) 5 := slice_direct sl_45_6_ok low_25
lemma sl_45_7_ok : sliceDirectCheck 2 0 0 R_45 G_45 R_15 G_15 = true := by decide +kernel
lemma sl_45_7 : Slice R_45 G_45 (subcube 2 0) 4 := slice_direct sl_45_7_ok low_15
lemma sl_45_8_ok : sliceDirectCheck 16 2 0 R_45 G_45 R_9 G_9 = true := by decide +kernel
lemma sl_45_8 : Slice R_45 G_45 (subcube 16 2) 4 := slice_direct sl_45_8_ok low_9
lemma sl_45_9_ok : sliceDirectCheck 8 32 0 R_45 G_45 R_6 G_6 = true := by decide +kernel
lemma sl_45_9 : Slice R_45 G_45 (subcube 8 32) 4 := slice_direct sl_45_9_ok low_6
lemma sl_45_10_ok : sliceDirectCheck 16 0 0 R_45 G_45 R_14 G_14 = true := by decide +kernel
lemma sl_45_10 : Slice R_45 G_45 (subcube 16 0) 5 := slice_direct sl_45_10_ok low_14
set_option maxRecDepth 200000 in
lemma slices_45_ok : ∀ i (hi : i < slices_45.size), Slice R_45 G_45 slices_45[i].1 slices_45[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice R_45 G_45 p.1 p.2) (forall_cons sl_45_0 (forall_cons sl_45_1 (forall_cons sl_45_2 (forall_cons sl_45_3 (forall_cons sl_45_4 (forall_cons sl_45_5 (forall_cons sl_45_6 (forall_cons sl_45_7 (forall_cons sl_45_8 (forall_cons sl_45_9 (forall_cons sl_45_10 (fun _ h => (List.not_mem_nil h).elim))))))))))))
lemma P_45_ok : ∀ i (hi : i < P_45.size), ∀ c, P_45[i] = some c → ValidPool R_45 G_45 c := buildPools_sound slices_45_ok
def bk_45_init : Array (List (List Nat)) := #[]
lemma bk_45_init_ok : ∀ i (hi : i < bk_45_init.size), ∀ xs ∈ bk_45_init[i], Impossible G_45 (0 - 1) xs.toFinset := by intro i hi; simp [bk_45_init] at hi
def nodes_45_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_45_0 : checkNodes W_45 G_45 fmask_45 P_45 autos_45 bk_45_init 0 nodes_45_0 = true := by decide +kernel
def bk_45_0 : Array (List (List Nat)) := buildBuckets 1 W_45 nodes_45_0
lemma bk_45_0_ok : ∀ i (hi : i < bk_45_0.size), ∀ xs ∈ bk_45_0[i], Impossible G_45 0 xs.toFinset :=
  buildBuckets_sound (by decide) gp_45 W_45_ok P_45_ok autos_45_ok bk_45_init_ok chk_45_0
def nodes_45_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_45_1 : checkNodes W_45 G_45 fmask_45 P_45 autos_45 bk_45_0 1 nodes_45_1 = true := by decide +kernel
def bk_45_1 : Array (List (List Nat)) := buildBuckets 1 W_45 nodes_45_1
lemma bk_45_1_ok : ∀ i (hi : i < bk_45_1.size), ∀ xs ∈ bk_45_1[i], Impossible G_45 1 xs.toFinset :=
  buildBuckets_sound (by decide) gp_45 W_45_ok P_45_ok autos_45_ok bk_45_0_ok chk_45_1
def nodes_45_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_45_2 : checkNodes W_45 G_45 fmask_45 P_45 autos_45 bk_45_1 2 nodes_45_2 = true := by decide +kernel
def bk_45_2 : Array (List (List Nat)) := buildBuckets 1 W_45 nodes_45_2
lemma bk_45_2_ok : ∀ i (hi : i < bk_45_2.size), ∀ xs ∈ bk_45_2[i], Impossible G_45 2 xs.toFinset :=
  buildBuckets_sound (by decide) gp_45 W_45_ok P_45_ok autos_45_ok bk_45_1_ok chk_45_2
def nodes_45_3 : List NodeSpec := [([93,133,3,4],[],[]),([93,2,3,134],[],[]),([93,135,3,4],[],[]),([129,125,3,4],[],[]),([62,123,3,4],[],[]),([87,93,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_45_3 : checkNodes W_45 G_45 fmask_45 P_45 autos_45 bk_45_2 3 nodes_45_3 = true := by decide +kernel
def bk_45_3 : Array (List (List Nat)) := buildBuckets 3 W_45 nodes_45_3
lemma bk_45_3_ok : ∀ i (hi : i < bk_45_3.size), ∀ xs ∈ bk_45_3[i], Impossible G_45 3 xs.toFinset :=
  buildBuckets_sound (by decide) gp_45 W_45_ok P_45_ok autos_45_ok bk_45_2_ok chk_45_3
def nodes_45_4 : List NodeSpec := [([121,0,66,2,3],[],[]),([17,66,88,3,4],[],[]),([89,1,56,3,4],[],[]),([0,1,122,3,12],[],[]),([110,0,1,2,12],[],[]),([22,105,2,3,4],[],[]),([115,23,2,3,4],[],[]),([22,2,123,3,4],[0],[0]),([21,93,2,3,4],[],[]),([93,2,3,4,18],[],[]),([124,93,2,3,4],[1],[0]),([28,66,2,3,4],[],[]),([93,125,2,3,4],[],[0]),([93,2,123,3,4],[],[]),([0,1,2,61,126],[],[]),([93,2,3,4,72],[],[]),([112,0,1,2,12],[],[]),([93,2,3,4,127],[],[]),([17,1,2,65,12],[2],[]),([17,109,66,3,4],[],[]),([0,1,2,128,3],[],[]),([93,2,61,3,4],[1],[0]),([55,62,22,3,4],[],[]),([37,1,2,65,12],[2],[]),([0,1,2,117,12],[3],[]),([129,22,2,3,4],[],[]),([93,62,2,3,4],[0],[0]),([55,22,61,3,4],[],[]),([129,93,2,3,4],[1],[0]),([87,22,23,2,3],[],[0]),([0,1,2,114,12],[],[]),([130,93,2,3,4],[],[]),([0,1,2,131,3],[3],[]),([22,132,2,3,4],[],[]),([0,1,61,5,12],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_45_4 : checkNodes W_45 G_45 fmask_45 P_45 autos_45 bk_45_3 4 nodes_45_4 = true := by decide +kernel
def bk_45_4 : Array (List (List Nat)) := buildBuckets 12 W_45 nodes_45_4
lemma bk_45_4_ok : ∀ i (hi : i < bk_45_4.size), ∀ xs ∈ bk_45_4[i], Impossible G_45 4 xs.toFinset :=
  buildBuckets_sound (by decide) gp_45 W_45_ok P_45_ok autos_45_ok bk_45_3_ok chk_45_4
def nd_45_5_0 : List NodeSpec := [([0,1,2,3,75,4],[],[]),([0,1,2,3,76,4],[4,5,6],[]),([77,0,1,2,3,4],[3],[]),([7,51,1,2,3,4],[4],[]),([0,78,1,2,3,4],[3],[]),([0,1,2,3,79,4],[],[]),([0,1,2,3,80,4],[],[]),([0,1,2,3,81,4],[0],[]),([21,25,7,1,2,4],[7],[]),([0,1,2,67,5,4],[3],[]),([82,0,1,2,3,4],[8,3],[]),([21,0,1,47,3,4],[3],[]),([0,1,47,3,4,18],[9,10],[]),([32,22,2,19,3,4],[0,8],[]),([83,0,1,47,3,4],[11],[]),([0,66,2,3,4,84],[],[]),([0,1,47,3,4,85],[9,10],[]),([86,0,1,2,3,12],[],[]),([14,42,0,1,2,3],[],[]),([28,1,2,3,10,4],[],[0]),([87,0,1,2,61,3],[3],[]),([22,23,2,3,4,72],[5],[0]),([0,1,2,88,3,4],[5,3,4],[]),([48,0,2,3,4,18],[],[]),([0,50,2,3,4,18],[9,10],[]),([26,71,2,3,4,18],[],[0]),([0,66,2,88,3,4],[0,2,5,12],[0]),([17,89,1,3,4],[0,9,10,13],[0]),([0,1,2,90,3,4],[0],[]),([17,1,2,91,3,4],[],[]),([21,0,50,2,3,4],[14],[]),([21,48,0,2,3,4],[15],[]),([14,0,68,1,2,3],[],[]),([0,68,2,3,54,4],[9],[]),([92,0,1,2,3,4],[],[]),([93,22,2,3,4],[0,2,5,1],[0]),([94,0,1,2,3,4],[0],[]),([17,13,1,56,3,4],[9],[0]),([95,1,2,19,3,4],[16],[]),([33,0,1,2,5,12],[10],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_45_5_0 : checkNodes W_45 G_45 fmask_45 P_45 autos_45 bk_45_4 5 nd_45_5_0 = true := by decide +kernel
def nd_45_5_1 : List NodeSpec := [([96,1,2,3,10,4],[5],[]),([97,1,2,19,3,4],[],[]),([25,7,1,2,4,18],[],[]),([0,1,2,3,98,4],[0],[]),([0,1,2,74,54,4],[8],[]),([0,68,1,2,3,12],[],[]),([0,1,2,3,99,4],[0],[]),([14,43,0,1,2,3],[],[]),([43,0,2,3,54,4],[9],[]),([17,66,2,3,4],[2,0,10],[0]),([0,1,2,3,100,4],[0],[]),([26,0,101,2,3,4],[],[]),([102,0,1,2,3,4],[17,18],[]),([0,1,103,2,3,4],[],[]),([32,104,0,2,3,4],[6],[]),([0,1,105,2,3,4],[],[0]),([106,0,1,2,3,4],[4],[]),([22,0,1,2,5,12],[13,2,10],[0]),([107,0,1,2,3,4],[4],[]),([0,1,108,2,3,4],[],[]),([17,66,1,2,3,4],[2,8],[]),([109,0,66,2,3,4],[0,2,5],[0]),([110,0,1,2,3,4],[],[0]),([14,17,22,1,2,3],[13,2],[]),([51,1,23,2,3,4],[5],[]),([21,70,0,2,3,4],[19],[]),([17,22,1,2,3,12],[13,2],[0]),([22,23,2,61,3,4],[5,0,20],[0]),([17,32,22,2,3,4],[0,6,8],[]),([22,23,2,3,4,18],[5],[0]),([111,22,1,2,3,4],[0],[]),([55,22,2,3,4],[0,2],[0]),([34,0,1,2,5,12],[17,13,10],[]),([22,0,1,2,65,12],[2,10],[]),([0,1,2,65,5,4],[2,10,8],[]),([112,0,1,2,3,4],[],[0]),([113,0,1,2,3,12],[13,3,17],[0]),([0,1,2,65,4,12],[2,3],[]),([17,1,2,3,65,4],[2,0],[0]),([0,1,2,3,114,4],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_45_5_1 : checkNodes W_45 G_45 fmask_45 P_45 autos_45 bk_45_4 5 nd_45_5_1 = true := by decide +kernel
def nd_45_5_2 : List NodeSpec := [([21,26,71,2,3,4],[],[0]),([0,1,2,65,12],[2,10,3],[0,1]),([115,0,1,2,3,4],[],[0]),([21,22,23,2,3,4],[0,20],[0]),([87,22,0,1,2,3],[],[0]),([15,0,1,61,3,4],[],[]),([0,1,2,116,3,4],[3,4],[]),([17,13,68,1,3,4],[9],[]),([62,22,23,2,3,4],[0,5],[0]),([42,0,1,2,3,12],[17],[0]),([0,66,2,3,4,18],[],[]),([21,0,66,2,3,4],[0,12],[0]),([14,0,1,2,61,3],[3],[0]),([0,1,2,61,3,12],[17,4],[0]),([0,1,2,3,117,4],[6,0,3,4],[0]),([22,37,1,2,3,12],[4,2],[0]),([0,1,2,61,3,4],[3,4],[]),([93,2,3,4],[2,1],[0]),([70,0,2,3,4,18],[],[]),([106,0,1,2,3,12],[17,3],[]),([118,0,1,2,3,4],[3,4],[]),([0,1,2,119,61,3],[4],[0]),([120,0,1,2,3,4],[3,4],[]),([0,1,61,3,5,4],[9,5],[0]),([22,2,19,30,3,4],[8,0],[]),([21,0,1,61,3,4],[3],[]),([0,1,61,3,4,18],[3],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_45_5_2 : checkNodes W_45 G_45 fmask_45 P_45 autos_45 bk_45_4 5 nd_45_5_2 = true := by decide +kernel
def nodes_45_5 : List NodeSpec := nd_45_5_0 ++ nd_45_5_1 ++ nd_45_5_2
lemma chk_45_5 : checkNodes W_45 G_45 fmask_45 P_45 autos_45 bk_45_4 5 nodes_45_5 = true := by
  unfold nodes_45_5 checkNodes
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨chk_45_5_0, chk_45_5_1⟩, chk_45_5_2⟩
def bk_45_5 : Array (List (List Nat)) := buildBuckets 36 W_45 nodes_45_5
lemma bk_45_5_ok : ∀ i (hi : i < bk_45_5.size), ∀ xs ∈ bk_45_5[i], Impossible G_45 5 xs.toFinset :=
  buildBuckets_sound (by decide) gp_45 W_45_ok P_45_ok autos_45_ok bk_45_4_ok chk_45_5
def nd_45_6_0 : List NodeSpec := [([0,1,2,3,27,4],[9,0,21,4,5,6,8],[]),([28,0,1,2,3,4],[4,5,6,3,0,17,9,8,22],[0,1]),([29,0,1,2,3,4],[9,0,5,6,8,3,4,23,13],[]),([15,14,0,1,2,3],[3,24,13,10,2],[]),([22,0,1,2,3,5,4],[8,17,5,2,10,9],[0]),([0,1,2,19,30,3,4],[8,0,6,25,13,26],[0,1]),([15,24,0,1,4],[8,17,2,13],[]),([31,0,1,2,3,4],[8,5,6,9,10,4,3],[]),([14,0,1,2,3,5],[27,13,10,2],[]),([17,32,0,1,2,3,4],[5,0,6,9,8],[0]),([0,1,2,5,12],[2,10,13],[0,1]),([33,0,1,2,3,5,4],[10,9],[0]),([34,0,1,2,3,4],[9,6,5,17,0,8,4,3,10],[]),([32,26,0,2,3,4],[6,0,2,5,8,13],[0]),([0,1,2,3,5,4],[10,2,8,13],[]),([1,2,35,3,4],[8,0,17,13],[]),([21,0,1,23,2,3,4],[4,0,3,28],[0]),([0,36,1,2,3,4],[0,13,17,10],[]),([37,0,1,2,3,4],[4,5,6,8,13,0,3,9,10],[]),([15,22,0,1,2,3,4],[8,5,0,9,6,2,10],[0]),([38,1,2,3,4],[9,2,8,13],[]),([7,0,1,2,3,4,18],[4,3,0],[0]),([0,1,2,3,39],[0,13,17],[]),([0,1,2,40,3,4],[2,0,3,4],[]),([25,0,1,2,3,4,18],[9,4,10],[0]),([25,7,1,2,4],[10,2,7],[0]),([0,1,2,41,3,4],[6,9,0,2,29,4],[]),([21,0,1,2,3,10,4],[0,4,30],[0]),([42,0,1,2,3,4],[5,9,17,4,3],[0]),([0,1,2,3,10,4,18],[0,4],[0]),([43,0,1,2,3,4],[5,0,9,6,17,4,3,8,13],[0]),([44,0,1,2,3,4],[0,8,17,10,3,4,5,13],[]),([45,0,1,2,3,4],[0,5,6,8,10,3,4,31],[]),([46,0,1,2,3,10,4],[0,4,5,6,2],[0]),([21,11,0,1,2,3,4],[4,17,8,3,32],[0]),([24,0,1,2,12],[17,13,2],[]),([11,0,1,2,3,4,18],[8,4,3,17,9,0],[0]),([0,1,2,47,3,4],[2,9,10,11,4],[0]),([32,0,1,2,19,3,4],[0,5,6,8,33,13],[0]),([0,1,47,3,4],[2,9,10,11],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_45_6_0 : checkNodes W_45 G_45 fmask_45 P_45 autos_45 bk_45_5 6 nd_45_6_0 = true := by decide +kernel
def nd_45_6_1 : List NodeSpec := [([46,25,0,1,2,3,4],[4,10,9,2],[]),([25,17,1,2,3,4],[8,17,9,10,2],[]),([48,0,2,3,4],[5,2,9,10,15],[0]),([49,0,1,2,3,4],[5,9,8,2,4,3,10],[0]),([0,50,2,3,4],[6,9,10,14],[0]),([51,0,1,2,3,4],[4,5,6,0,3,17,9,13,34],[0]),([0,52,1,2,3,4],[0,6,5,10,4,3],[0,1]),([0,53,2,3,4],[0,6,8,2],[]),([14,17,0,1,2,3],[3,35,13,2,10],[0]),([0,1,2,3,12],[2,13],[]),([17,0,1,2,3,12],[13,2,10],[0]),([17,0,1,2,3,5,4],[10,9,13],[0]),([16,0,1,2,3,54,4],[6,17,8,9,0],[0]),([55,0,1,2,3,4],[0,6,17,2,3,4],[0]),([17,0,1,56,2,3,4],[9,5,0],[0]),([0,1,2,3,57],[9,2,13],[]),([58,0,1,2,3],[0,4,10,13],[]),([22,0,1,2,3,12],[2,10,13,36],[0,1]),([17,0,1,2,3,54,4],[6,9,10],[0]),([14,16,0,1,2,3],[3,37,13,10,2],[0]),([17,0,1,2,3,4],[8,5,6,0,17,10,3,4,9],[]),([59,0,1,3,4],[8,9,2,13],[]),([21,26,0,1,2,3,4],[4,6,3,38],[0]),([21,22,0,1,2,3,4],[4,5,0,9,6,8,3,36],[0]),([60,17,0,1,2,3,4],[5,2,9,0,10],[]),([26,0,1,2,3,4,18],[6,4,9,0],[0]),([17,13,1,3,4],[0,9,10,13],[0]),([21,25,0,1,2,3,4],[4,10,9,3,39],[0]),([0,1,2,61,3,4],[9,0,5,6,17,3,4],[0]),([0,1,23,2,3,4,18],[0,6,4],[0,1]),([62,22,0,1,2,3,4],[0,6,8,5,9],[0]),([0,1,2,3,63],[2,8,4],[]),([17,1,2,3,10,4],[2,0,8,9,10,13],[0]),([22,0,1,2,3,4,12],[17,3,4,5,2,9,0,36],[0]),([0,64,1,2,3,4],[3,0,5,9,13,17,40],[0,1]),([22,0,1,2,3,65,4],[2,10,5],[0]),([0,66,1,2,3,4],[0,5,2,8,4,3],[0]),([33,0,1,2,3,4],[9,6,5,10,4,3],[]),([22,0,1,2,3,4],[6,0,8,5,2,4,3,9],[0]),([22,0,1,2,61,3,4],[5,8,9,0,6,36],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_45_6_1 : checkNodes W_45 G_45 fmask_45 P_45 autos_45 bk_45_5 6 nd_45_6_1 = true := by decide +kernel
def nd_45_6_2 : List NodeSpec := [([0,1,2,3,67,4],[10,5,6,9,3,4],[0]),([17,0,68,1,2,3,4],[6,5,9,0],[0]),([0,1,2,3,69],[2,13],[]),([22,0,1,2,3,4,18],[8,4,3,5],[0]),([60,16,0,1,2,3,4],[8,2,5,10],[]),([14,22,0,1,2,3],[3,36,2,10,13],[0,1]),([22,23,2,3,4],[0,5,2,20],[0]),([0,68,1,2,3,4],[8,0,5,9,17,4,3,41],[0,1]),([0,1,2,3,5,12],[10,2,13],[]),([21,7,0,1,2,3,4],[0,4,3,42],[0]),([22,1,2,19,3,4],[0,8,10,13,6,9],[0]),([70,0,2,3,4],[0,6,2,19],[0]),([0,66,2,3,4],[0,2,5,10,12],[0]),([26,71,2,3,4],[6,0,2,43],[0]),([0,1,2,3,65,4],[2,10,8,5,3,4],[0,1]),([34,0,1,2,3,5,4],[17,8,0,10,9],[0]),([17,0,1,2,3,67,4],[10,9],[]),([44,0,2,3,4],[0,8,5,10,13],[]),([22,0,1,2,3,4,72],[5,3],[0]),([37,0,1,2,3,12],[4,2,13,3,10],[0]),([0,1,2,3,73,4],[13,9,0,10,5,6],[]),([0,1,2,3,74,4],[10,8,5,6,13],[0]),([17,22,1,2,3,4],[6,8,9,0,2,13,10],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_45_6_2 : checkNodes W_45 G_45 fmask_45 P_45 autos_45 bk_45_5 6 nd_45_6_2 = true := by decide +kernel
def nodes_45_6 : List NodeSpec := nd_45_6_0 ++ nd_45_6_1 ++ nd_45_6_2
lemma chk_45_6 : checkNodes W_45 G_45 fmask_45 P_45 autos_45 bk_45_5 6 nodes_45_6 = true := by
  unfold nodes_45_6 checkNodes
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨chk_45_6_0, chk_45_6_1⟩, chk_45_6_2⟩
def bk_45_6 : Array (List (List Nat)) := buildBuckets 35 W_45 nodes_45_6
lemma bk_45_6_ok : ∀ i (hi : i < bk_45_6.size), ∀ xs ∈ bk_45_6[i], Impossible G_45 6 xs.toFinset :=
  buildBuckets_sound (by decide) gp_45 W_45_ok P_45_ok autos_45_ok bk_45_5_ok chk_45_6
def nodes_45_7 : List NodeSpec := [([0,1,2,3,5,4],[2,10,8,27,13],[0,1]),([6,0,1,2,3,4],[3,4,6,13,17,9,0,10],[0,1]),([7,0,1,2,3,4],[0,6,2,8,4,3,42],[0]),([0,1,8,2,3,4],[2,0,10,8,4,3],[0,1]),([0,1,2,3,4,9],[0,13,10,6],[0]),([0,1,2,3,10,4],[0,2,30,10,8,4],[0,1]),([11,0,1,2,3,4],[17,10,6,2,8,4,3,32],[0]),([0,1,2,3,4,12],[2,10,13,3],[0,1]),([13,0,1,2,3,4],[0,6,8,10,4,3,13],[0]),([14,0,1,2,3],[3,2,10],[0,1]),([15,0,1,2,3,4],[8,0,6,4,3,2,10,13],[0,1]),([16,0,1,2,3,4],[8,6,17,4,3,9,0,10,13],[0]),([17,0,1,2,3,4],[8,9,6,0,17,10,3,4,13,35],[0,1]),([0,1,2,3,4,18],[8,13,0,6,3,17],[0,1]),([0,1,2,19,3,4],[0,8,10,13,6,26,3],[0]),([20,0,1,2,3,4],[4,0,10,6,2,13,3],[0]),([0,1,2,3,12],[2,10,13,3],[0,1]),([21,0,1,2,3,4],[4,0,6,3,17,8],[0,1]),([22,0,1,2,3,4],[6,0,8,5,17,2,3,4,36,9,10],[0,1]),([0,1,23,2,3,4],[0,6,2,8,3,4,28],[0]),([24,0,1,2,3,4],[17,0,10,6,2,4,3,8,13],[0]),([25,0,1,2,3,4],[17,9,6,2,10,8,3,4,39],[0,1]),([26,0,1,2,3,4],[6,8,2,4,3,0,9,38],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_45_7 : checkNodes W_45 G_45 fmask_45 P_45 autos_45 bk_45_6 7 nodes_45_7 = true := by decide +kernel
def bk_45_7 : Array (List (List Nat)) := buildBuckets 8 W_45 nodes_45_7
lemma bk_45_7_ok : ∀ i (hi : i < bk_45_7.size), ∀ xs ∈ bk_45_7[i], Impossible G_45 7 xs.toFinset :=
  buildBuckets_sound (by decide) gp_45 W_45_ok P_45_ok autos_45_ok bk_45_6_ok chk_45_7
def nodes_45_8 : List NodeSpec := [([0,1,2,3,4],[3],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_45_8 : checkNodes W_45 G_45 fmask_45 P_45 autos_45 bk_45_7 8 nodes_45_8 = true := by decide +kernel
def bk_45_8 : Array (List (List Nat)) := buildBuckets 1 W_45 nodes_45_8
lemma bk_45_8_ok : ∀ i (hi : i < bk_45_8.size), ∀ xs ∈ bk_45_8[i], Impossible G_45 8 xs.toFinset :=
  buildBuckets_sound (by decide) gp_45 W_45_ok P_45_ok autos_45_ok bk_45_7_ok chk_45_8
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma root_45_ok : forestRootCheck R_45 G_45 [(VAR 1,14,12),(VAR 2,14,10),(VAR 3,14,6),(VAR 4,18,2),(VAR 5,38,6)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma root_45_in : bucketContains bk_45_8 R_45 = true := by decide +kernel
lemma low_45 : Lower R_45 G_45 9 := lower_of_forest root_45_ok bk_45_8_ok root_45_in

end Cofactor12160
def h32R : List Nat := varsOf 55
def h32G : Nat := 0xfefeeaeaececc8c8fefeeaeaececc8c8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h32Bound : Lower h32R h32G 9 := carry_of (swaps := [(2,3),(3,4),(0,1),(1,2),(2,3),(0,1),(1,2)]) (roots2 := Cofactor12160.R_45) (T2 := Cofactor12160.G_45) (by decide +kernel) Cofactor12160.low_45
def h33R : List Nat := varsOf 59
def h33G : Nat := 0xffeeeeaaeecccc88ffeeeeaaeecccc88
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Bound : Lower h33R h33G 9 := carry_of (swaps := [(2,3),(3,4),(1,2),(2,3),(0,1),(1,2)]) (roots2 := Cofactor12160.R_45) (T2 := Cofactor12160.G_45) (by decide +kernel) Cofactor12160.low_45
def h35R : List Nat := varsOf 29
def h35G : Nat := 0xfff0faa0fff0faa0fff0faa0fff0faa0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Bound : Lower h35R h35G 5 := lift_of (z := 1) (o := 0) (essPairs := [(VAR 0,4,5)]) (by decide +kernel) h1Bound
def h36R : List Nat := varsOf 29
def h36G : Nat := 0xfffafaaafffafaaafffafaaafffafaaa
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h36Bound : Lower h36R h36G 5 := lift_of (z := 1) (o := 0) (essPairs := [(VAR 0,0,1)]) (by decide +kernel) h1Bound
def h34R : List Nat := varsOf 61
def h34G : Nat := 0xfffafaaafff0faa0fffafaaafff0faa0
def h34Pos : List Nat := [9,12,5,5,12,9,20,49,33,24,44,44,49,20,52,24]
def h34Neg : List Nat := [8,8,1,4,4,1,4,48,1,8,40,36,17,16,36,16]
def h34Mask : Nat := fullMask 16
def h34Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,4525,4388),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x6c5e,0x4858),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x8e33,1539),(0xffff0000ffff0000ffff0000ffff0000,0xf2c0,0xb080),(0xffffffff00000000ffffffff00000000,0x5d80,0x4c80)]
def h34Steps : List (Nat × Nat × Nat) := [(1,1,2),(3,3,5)]
def h34W : Array Decor := buildWires h34Base h34Steps
def h34Autos : Array (List (Nat × Nat)) := #[[]]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34Pairs : goodPairs h34G h34Pos h34Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34BaseOk : ∀ x ∈ h34Base, faithful h34Pos h34Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34WOk : ∀ x ∈ h34W.toList, faithful h34Pos h34Neg x ∧ x.1 < 2^128 := buildWires_faithful h34BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34AutosOk : ∀ sw ∈ h34Autos.toList, swapsValid sw = true ∧ permWord sw h34G = h34G := autos_of (by decide +kernel)
def h34SliceList : List (Nat × Nat) := [(subcube 0 32,5),(subcube 1 0,4),(subcube 4 0,4),(subcube 8 0,4),(subcube 16 0,5),(subcube 32 0,5),(subcube 33 0,4)]
def h34Slices : Array (Nat × Nat) := h34SliceList.toArray
def h34Specs : List PoolSpec := [(1,[]),(6,[]),(2,[]),(3,[]),(4,[]),(5,[]),(0,[])]
def h34Pools : Array (Option BoundPool) := buildPools h34W h34R h34Slices h34Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34Slice6 : Slice h34R h34G (subcube 33 0) 4 := slice_direct (zDead := 0) (by decide +kernel) h1Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34Slice5 : Slice h34R h34G (subcube 32 0) 5 := slice_direct (zDead := 0) (by decide +kernel) h35Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34Slice4 : Slice h34R h34G (subcube 16 0) 5 := slice_direct (zDead := 0) (by decide +kernel) h10Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34Slice3 : Slice h34R h34G (subcube 8 0) 4 := slice_direct (zDead := 0) (by decide +kernel) h12Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34Slice2 : Slice h34R h34G (subcube 4 0) 4 := slice_direct (zDead := 0) (by decide +kernel) h14Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34Slice1 : Slice h34R h34G (subcube 1 0) 4 := slice_direct (zDead := 32) (by decide +kernel) h1Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34Slice0 : Slice h34R h34G (subcube 0 32) 5 := slice_direct (zDead := 0) (by decide +kernel) h36Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34SlicesOk : ∀ i (hi : i < h34Slices.size), Slice h34R h34G h34Slices[i].1 h34Slices[i].2 := array_forall_of_list (P := fun (p : Nat × Nat) => Slice h34R h34G p.1 p.2) (forall_cons h34Slice0 (forall_cons h34Slice1 (forall_cons h34Slice2 (forall_cons h34Slice3 (forall_cons h34Slice4 (forall_cons h34Slice5 (forall_cons h34Slice6 (fun _ h => (List.not_mem_nil h).elim))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34PoolsOk : ∀ i (hi : i < h34Pools.size), ∀ c, h34Pools[i] = some c → ValidPool h34R h34G c := buildPools_sound h34SlicesOk
def h34Empty : Array (List (List Nat)) := #[]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34EmptyOk : ∀ i (hi : i < h34Empty.size), ∀ xs ∈ h34Empty[i], Impossible h34G (4 - 1) xs.toFinset := by intro i hi; simp [h34Empty] at hi
def h34Block4_0 : List NodeSpec := [([0,1,2,4,6],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34Test4_0 : checkNodes h34W h34G h34Mask h34Pools h34Autos h34Empty 4 h34Block4_0 = true := by decide +kernel
def h34Nodes4 : List NodeSpec := h34Block4_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34Check4 : checkNodes h34W h34G h34Mask h34Pools h34Autos h34Empty 4 h34Nodes4 = true := h34Test4_0
def h34Bucket4 : Array (List (List Nat)) := buildBuckets 1 h34W h34Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34Bucket4Ok : ∀ i (hi : i < h34Bucket4.size), ∀ xs ∈ h34Bucket4[i], Impossible h34G 4 xs.toFinset := buildBuckets_sound (by decide) h34Pairs h34WOk h34PoolsOk h34AutosOk h34EmptyOk h34Check4
def h34Block5_0 : List NodeSpec := [([0,1,2,3,4,5],[2,4,5,6],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34Test5_0 : checkNodes h34W h34G h34Mask h34Pools h34Autos h34Bucket4 5 h34Block5_0 = true := by decide +kernel
def h34Nodes5 : List NodeSpec := h34Block5_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34Check5 : checkNodes h34W h34G h34Mask h34Pools h34Autos h34Bucket4 5 h34Nodes5 = true := h34Test5_0
def h34Bucket5 : Array (List (List Nat)) := buildBuckets 1 h34W h34Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34Bucket5Ok : ∀ i (hi : i < h34Bucket5.size), ∀ xs ∈ h34Bucket5[i], Impossible h34G 5 xs.toFinset := buildBuckets_sound (by decide) h34Pairs h34WOk h34PoolsOk h34AutosOk h34Bucket4Ok h34Check5
def h34Block6_0 : List NodeSpec := [([0,1,2,3,4],[0,1,2,3,4,5,6],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34Test6_0 : checkNodes h34W h34G h34Mask h34Pools h34Autos h34Bucket5 6 h34Block6_0 = true := by decide +kernel
def h34Nodes6 : List NodeSpec := h34Block6_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34Check6 : checkNodes h34W h34G h34Mask h34Pools h34Autos h34Bucket5 6 h34Nodes6 = true := h34Test6_0
def h34Bucket6 : Array (List (List Nat)) := buildBuckets 1 h34W h34Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34Bucket6Ok : ∀ i (hi : i < h34Bucket6.size), ∀ xs ∈ h34Bucket6[i], Impossible h34G 6 xs.toFinset := buildBuckets_sound (by decide) h34Pairs h34WOk h34PoolsOk h34AutosOk h34Bucket5Ok h34Check6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34Bound : Lower h34R h34G 7 := lower_of_forest (essPairs := [(VAR 0,4,5),(VAR 2,1,5),(VAR 3,1,9),(VAR 4,4,20),(VAR 5,1,33)]) (by decide +kernel) h34Bucket6Ok (by decide +kernel)
def h37R : List Nat := varsOf 62
def h37G : Nat := 0xfffffffffcc0ccc0fffffffffcc0ccc0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Bound : Lower h37R h37G 6 := lift_of (z := 32) (o := 16) (essPairs := [(VAR 4,12,28),(VAR 5,0,32)]) (by decide +kernel) h3Bound
def h0R : List Nat := varsOf 63
def h0G : Nat := 0xfeeaeaaaecc0c880feeaeaaaecc0c880
def h0Pos : List Nat := [14,29,7,7,14,11,14,7,14,11,22,29,51,60,33,11,29,29,23,35,26,46,60,26,33,58,46,26,60,15,54,45,22,54,60,7,22,23,22,58,46,33,33,7,23,54,27,58,51,49]
def h0Neg : List Nat := [12,28,5,6,13,10,10,3,6,3,6,13,50,28,1,9,25,21,21,3,10,42,56,24,32,56,38,18,52,13,38,13,20,52,44,4,18,6,4,42,44,36,40,21,19,50,19,50,19,48]
def h0Mask : Nat := fullMask 50
def h0Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x35e28a10fdaae,0x15800a00fca94),(0xcccccccccccccccccccccccccccccccc,0x1f9fb6ebc97fd,0x1f0b04c3817e8),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x397ff4672ddf,0xb6ff4062d1f),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xc184bef3ab73,0x584a2f1a873),(0xffff0000ffff0000ffff0000ffff0000,0x3f0f75ad73c02,0x3f8131ac73002),(0xffffffff00000000ffffffff00000000,0x3a786d7687000,0x2a78657601000)]
def h0Steps : List (Nat × Nat × Nat) := [(1,0,1),(3,0,1),(3,0,4),(0,1,4),(3,1,4),(0,2,6),(3,0,11),(0,3,11),(2,2,13),(2,3,13),(0,3,6),(3,0,16),(2,2,12),(2,3,17),(2,1,8),(2,2,8),(2,3,21),(2,3,8),(2,2,23),(1,0,9),(0,2,25),(0,3,25),(2,2,9),(2,3,9),(1,0,10),(2,2,10),(2,3,10)]
def h0W : Array Decor := buildWires h0Base h0Steps
def h0Autos : Array (List (Nat × Nat)) := #[[]]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Pairs : goodPairs h0G h0Pos h0Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0BaseOk : ∀ x ∈ h0Base, faithful h0Pos h0Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0WOk : ∀ x ∈ h0W.toList, faithful h0Pos h0Neg x ∧ x.1 < 2^128 := buildWires_faithful h0BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0AutosOk : ∀ sw ∈ h0Autos.toList, swapsValid sw = true ∧ permWord sw h0G = h0G := autos_of (by decide +kernel)
def h0SliceList : List (Nat × Nat) := [(subcube 0 1,6),(subcube 0 2,7),(subcube 0 4,9),(subcube 0 8,9),(subcube 0 16,8),(subcube 0 17,5),(subcube 0 32,8),(subcube 1 0,8),(subcube 1 16,5),(subcube 1 32,7),(subcube 2 0,6),(subcube 2 4,5),(subcube 2 8,5),(subcube 2 12,4),(subcube 2 16,5),(subcube 2 20,4),(subcube 2 24,4),(subcube 4 0,5),(subcube 8 0,5),(subcube 16 0,7),(subcube 32 0,9),(subcube 32 1,5),(subcube 33 2,4)]
def h0Slices : Array (Nat × Nat) := h0SliceList.toArray
def h0Specs : List PoolSpec := [(7,[]),(1,[]),(2,[(1,0,1)]),(3,[(1,0,1)]),(20,[(1,0,1)]),(4,[(1,0,1)]),(2,[]),(0,[]),(2,[(1,0,1),(0,3,11)]),(10,[]),(17,[]),(18,[]),(19,[]),(4,[]),(20,[]),(6,[]),(3,[]),(2,[(1,0,1),(0,3,11),(2,3,13)]),(2,[(1,0,1),(0,3,6)]),(2,[(3,0,1)]),(3,[(3,0,1)]),(20,[(3,0,1)]),(4,[(3,0,1)]),(7,[(0,2,6)]),(2,[(1,0,1),(3,0,11)]),(3,[(1,0,1),(0,2,6),(3,0,11)]),(20,[(1,0,1),(0,2,6),(3,0,11)]),(1,[(3,0,11)]),(9,[(0,2,6)]),(11,[]),(5,[]),(12,[]),(7,[(0,2,6),(2,2,12)]),(9,[(0,2,6),(2,2,12)]),(21,[]),(13,[]),(22,[]),(7,[(0,3,6)]),(3,[(1,0,1),(3,0,16)]),(2,[(1,0,1),(0,3,6),(3,0,16)]),(20,[(1,0,1),(0,3,6),(3,0,16)]),(1,[(3,0,16)]),(9,[(0,3,6)]),(7,[(0,3,6),(2,3,17)]),(9,[(0,3,6),(2,3,17)]),(9,[]),(2,[(3,0,4)]),(3,[(3,0,4)]),(20,[(3,0,4)]),(7,[(2,1,8)]),(2,[(3,0,4),(2,1,8)]),(3,[(3,0,4),(2,1,8)]),(20,[(3,0,4),(2,1,8)]),(4,[(2,1,8)]),(1,[(3,0,4)]),(8,[]),(2,[(3,0,4),(2,3,21)]),(2,[(3,0,4),(2,3,8)]),(7,[(0,1,4)]),(2,[(0,1,4)]),(3,[(0,1,4)]),(20,[(0,1,4)]),(2,[(0,1,4),(1,0,9)]),(3,[(0,1,4),(1,0,9)]),(4,[(1,0,9)]),(20,[(0,1,4),(1,0,9)]),(1,[(1,0,9)]),(2,[(0,1,4),(1,0,9),(0,3,25)]),(2,[(0,1,4),(2,3,9)]),(7,[(3,1,4)]),(2,[(3,1,4)]),(3,[(3,1,4)]),(20,[(3,1,4)]),(2,[(3,1,4),(1,0,10)]),(3,[(3,1,4),(1,0,10)]),(4,[(1,0,10)]),(20,[(3,1,4),(1,0,10)]),(9,[(3,1,4)]),(14,[]),(16,[]),(2,[(3,1,4),(2,3,10)]),(15,[])]
def h0Pools : Array (Option BoundPool) := buildPools h0W h0R h0Slices h0Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice22 : Slice h0R h0G (subcube 33 2) 4 := slice_direct (zDead := 0) (by decide +kernel) h1Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice21 : Slice h0R h0G (subcube 32 1) 5 := slice_direct (zDead := 0) (by decide +kernel) h2Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice20 : Slice h0R h0G (subcube 32 0) 9 := slice_direct (zDead := 0) (by decide +kernel) h4Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice19 : Slice h0R h0G (subcube 16 0) 7 := slice_direct (zDead := 0) (by decide +kernel) h5Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice18 : Slice h0R h0G (subcube 8 0) 5 := slice_direct (zDead := 0) (by decide +kernel) h11Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice17 : Slice h0R h0G (subcube 4 0) 5 := slice_direct (zDead := 0) (by decide +kernel) h13Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice16 : Slice h0R h0G (subcube 2 24) 4 := slice_direct (zDead := 0) (by decide +kernel) h15Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice15 : Slice h0R h0G (subcube 2 20) 4 := slice_direct (zDead := 0) (by decide +kernel) h16Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice14 : Slice h0R h0G (subcube 2 16) 5 := slice_direct (zDead := 0) (by decide +kernel) h17Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice13 : Slice h0R h0G (subcube 2 12) 4 := slice_direct (zDead := 0) (by decide +kernel) h18Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice12 : Slice h0R h0G (subcube 2 8) 5 := slice_direct (zDead := 0) (by decide +kernel) h19Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice11 : Slice h0R h0G (subcube 2 4) 5 := slice_direct (zDead := 0) (by decide +kernel) h20Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice10 : Slice h0R h0G (subcube 2 0) 6 := slice_direct (zDead := 0) (by decide +kernel) h21Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice9 : Slice h0R h0G (subcube 1 32) 7 := slice_direct (zDead := 0) (by decide +kernel) h22Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice8 : Slice h0R h0G (subcube 1 16) 5 := slice_direct (zDead := 0) (by decide +kernel) h23Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice7 : Slice h0R h0G (subcube 1 0) 8 := slice_direct (zDead := 0) (by decide +kernel) h24Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice6 : Slice h0R h0G (subcube 0 32) 8 := slice_direct (zDead := 0) (by decide +kernel) h25Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice5 : Slice h0R h0G (subcube 0 17) 5 := slice_direct (zDead := 0) (by decide +kernel) h26Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice4 : Slice h0R h0G (subcube 0 16) 8 := slice_direct (zDead := 0) (by decide +kernel) h27Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice3 : Slice h0R h0G (subcube 0 8) 9 := slice_direct (zDead := 0) (by decide +kernel) h32Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice2 : Slice h0R h0G (subcube 0 4) 9 := slice_direct (zDead := 0) (by decide +kernel) h33Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice1 : Slice h0R h0G (subcube 0 2) 7 := slice_direct (zDead := 0) (by decide +kernel) h34Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice0 : Slice h0R h0G (subcube 0 1) 6 := slice_direct (zDead := 0) (by decide +kernel) h37Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0SlicesOk : ∀ i (hi : i < h0Slices.size), Slice h0R h0G h0Slices[i].1 h0Slices[i].2 := array_forall_of_list (P := fun (p : Nat × Nat) => Slice h0R h0G p.1 p.2) (forall_cons h0Slice0 (forall_cons h0Slice1 (forall_cons h0Slice2 (forall_cons h0Slice3 (forall_cons h0Slice4 (forall_cons h0Slice5 (forall_cons h0Slice6 (forall_cons h0Slice7 (forall_cons h0Slice8 (forall_cons h0Slice9 (forall_cons h0Slice10 (forall_cons h0Slice11 (forall_cons h0Slice12 (forall_cons h0Slice13 (forall_cons h0Slice14 (forall_cons h0Slice15 (forall_cons h0Slice16 (forall_cons h0Slice17 (forall_cons h0Slice18 (forall_cons h0Slice19 (forall_cons h0Slice20 (forall_cons h0Slice21 (forall_cons h0Slice22 (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0PoolsOk : ∀ i (hi : i < h0Pools.size), ∀ c, h0Pools[i] = some c → ValidPool h0R h0G c := buildPools_sound h0SlicesOk
def h0Empty : Array (List (List Nat)) := #[]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0EmptyOk : ∀ i (hi : i < h0Empty.size), ∀ xs ∈ h0Empty[i], Impossible h0G (7 - 1) xs.toFinset := by intro i hi; simp [h0Empty] at hi
def h0Block7_0 : List NodeSpec := [([0,1,2,3,4,5,13],[0,7,8,9,10,11,12,13,14,15],[0]),([0,1,2,3,4,5,15],[1,6,7,10,12,13,14,15,17],[0]),([0,1,2,3,4,5,14],[1,6,7,8,10,12,13,14,15,16],[0]),([0,1,2,3,4,5,22],[1,6,7,9,10,12,14,15,56],[0]),([0,1,2,3,4,5,24],[1,6,7,9,10,12,14,15,16,57],[0]),([0,1,2,3,4,5,26],[0,6,7,9,10,11,12,14,15,16,62],[0]),([0,1,2,3,4,5,27],[0,6,7,9,10,12,14,15,16,63,67],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_0 : checkNodes h0W h0G h0Mask h0Pools h0Autos h0Empty 7 h0Block7_0 = true := by decide +kernel
def h0Nodes7 : List NodeSpec := h0Block7_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Check7 : checkNodes h0W h0G h0Mask h0Pools h0Autos h0Empty 7 h0Nodes7 = true := h0Test7_0
def h0Bucket7 : Array (List (List Nat)) := buildBuckets 7 h0W h0Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket7Ok : ∀ i (hi : i < h0Bucket7.size), ∀ xs ∈ h0Bucket7[i], Impossible h0G 7 xs.toFinset := buildBuckets_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0EmptyOk h0Check7
def h0Block8_0 : List NodeSpec := [([0,1,2,3,4,5,11],[0,1,2,6,7,12,13,14,15,16],[0]),([0,1,2,3,4,5,16],[0,1,3,6,7,12,13,14,15,16,18],[0]),([0,1,2,3,4,5,12],[7,9,12,13,14,15,16,23,24,25,26,27,28,29,30,31],[0]),([0,1,2,3,4,5,18],[0,1,6,7,9,10,12,13,14,15,16,24,29,30,31,32,33,34,35,36],[0]),([0,1,2,3,4,5,17],[6,7,9,12,13,14,15,29,30,31,37,38,39,40,41,42],[0]),([0,1,2,3,4,5,19],[0,1,6,7,9,11,12,13,14,15,16,29,30,31,34,35,36,38,43,44],[0]),([0,1,2,3,4,5,20],[0,6,9,12,13,14,15,16,29,31,49,50,51,52,53,54],[0]),([0,1,2,3,4,5,21],[0,1,6,9,12,13,14,15,16,46,55],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_0 : checkNodes h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_0 = true := by decide +kernel
def h0Block8_1 : List NodeSpec := [([0,1,2,3,4,5,23],[0,1,6,9,12,13,14,15,16,47,55,57],[0]),([0,1,2,3,4,5,25],[0,1,6,7,12,13,14,15,16,58,62,63,64,65,66],[0]),([0,1,2,3,4,5,28],[0,1,6,7,12,13,14,15,16,29,35,59],[0]),([0,1,2,3,4,5,29],[0,1,6,7,12,13,14,15,16,31,35,60,68],[0]),([0,1,2,3,4,5,30],[0,1,6,7,12,13,14,15,16,36,69,73,74,75,76,77],[0]),([0,1,2,3,4,5,31],[0,1,6,7,12,13,14,15,16,70,78,79],[0]),([0,1,2,3,4,5,32],[0,1,6,7,12,13,14,15,16,71,78,80,81],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_1 : checkNodes h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_1 = true := by decide +kernel
def h0Nodes8 : List NodeSpec := h0Block8_0 ++ h0Block8_1
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Check8 : checkNodes h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Nodes8 = true := by
  unfold h0Nodes8 checkNodes
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h0Test8_0,h0Test8_1⟩
def h0Bucket8 : Array (List (List Nat)) := buildBuckets 15 h0W h0Nodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket8Ok : ∀ i (hi : i < h0Bucket8.size), ∀ xs ∈ h0Bucket8[i], Impossible h0G 8 xs.toFinset := buildBuckets_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0Bucket7Ok h0Check8
def h0Block9_0 : List NodeSpec := [([0,1,2,3,4,5,6],[0,1,2,3,4,5,6,12,13,14,15,16],[0]),([0,1,2,3,4,5,7],[0,1,6,7,9,12,13,14,15,16,19,20,21,22,30,45],[0]),([0,1,2,3,4,5,8],[0,1,6,12,13,14,15,16,46,47,48],[0]),([0,1,2,3,4,5,9],[0,1,6,9,12,13,14,15,16,58,59,60,61],[0]),([0,1,2,3,4,5,10],[0,1,6,12,13,14,15,16,69,70,71,72],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_0 : checkNodes h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_0 = true := by decide +kernel
def h0Nodes9 : List NodeSpec := h0Block9_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Check9 : checkNodes h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Nodes9 = true := h0Test9_0
def h0Bucket9 : Array (List (List Nat)) := buildBuckets 5 h0W h0Nodes9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket9Ok : ∀ i (hi : i < h0Bucket9.size), ∀ xs ∈ h0Bucket9[i], Impossible h0G 9 xs.toFinset := buildBuckets_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0Bucket8Ok h0Check9
def h0Block10_0 : List NodeSpec := [([0,1,2,3,4,5],[0,6,13,14,16],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test10_0 : checkNodes h0W h0G h0Mask h0Pools h0Autos h0Bucket9 10 h0Block10_0 = true := by decide +kernel
def h0Nodes10 : List NodeSpec := h0Block10_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Check10 : checkNodes h0W h0G h0Mask h0Pools h0Autos h0Bucket9 10 h0Nodes10 = true := h0Test10_0
def h0Bucket10 : Array (List (List Nat)) := buildBuckets 1 h0W h0Nodes10
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket10Ok : ∀ i (hi : i < h0Bucket10.size), ∀ xs ∈ h0Bucket10[i], Impossible h0G 10 xs.toFinset := buildBuckets_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0Bucket9Ok h0Check10
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bound : Lower h0R h0G 11 := lower_of_forest (essPairs := [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11),(VAR 4,6,22),(VAR 5,1,33)]) (by decide +kernel) h0Bucket10Ok (by decide +kernel)
def wit : List PEqualNP.CircuitLowerBounds.Gate := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 5]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 8]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 5]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 10]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 11]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 12]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 13]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 14]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 15]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 16]⟩]
def wo : Nat := 17
lemma wit_mono : PEqualNP.MetaComplexity.Monotone2 ⟨wit, wo⟩ := by simp [PEqualNP.MetaComplexity.Monotone2, wit]
set_option maxRecDepth 100000 in set_option maxHeartbeats 0 in
lemma wit_eval : ∀ r : Row, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput6 r)) = ((4276808362 * 2 ^ 32 + 3972057216) ||| ((4276808362 * 2 ^ 32 + 3972057216) <<< 64)).testBit r.val := by decide +kernel
lemma low_root : Lower (varsOf 63) ((4276808362 * 2 ^ 32 + 3972057216) ||| ((4276808362 * 2 ^ 32 + 3972057216) <<< 64)) 11 := h0Bound
end PEqualNP.Outside.L_meta_41986
theorem PEqualNP.Outside.L_meta_41986 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808362 * 2 ^ 32 + 3972057216) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808362 * 2 ^ 32 + 3972057216) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hcs
  exact PEqualNP.Outside.L_meta_41986.table2_of_lower (4276808362 * 2 ^ 32 + 3972057216) (by decide) (by decide) (by decide) (by decide)
    11 PEqualNP.Outside.L_meta_41986.low_root
    PEqualNP.Outside.L_meta_41986.wit PEqualNP.Outside.L_meta_41986.wo (by decide)
    PEqualNP.Outside.L_meta_41986.wit_mono PEqualNP.Outside.L_meta_41986.wit_eval s hcs
