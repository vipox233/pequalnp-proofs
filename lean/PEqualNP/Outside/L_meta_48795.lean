import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_48795
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
def h1R : List Nat := varsOf 19
def h1G : Nat := 0xeeee8888eeee8888eeee8888eeee8888
def h1Pos : List Nat := [17,18,3,3,18,17]
def h1Neg : List Nat := [16,16,1,2,2,1]
def h1Mask : Nat := fullMask 6
def h1Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,45,36),(0xcccccccccccccccccccccccccccccccc,30,24),(0xffff0000ffff0000ffff0000ffff0000,51,3)]
def h1Steps : List (Nat × Nat × Nat) := []
def h1W : BT Decor := buildWiresBT 2 h1Base h1Steps
def h1AutoList : List (List (Nat × Nat)) := [[]]
def h1Autos : BT (List (Nat × Nat)) := btOfList 1 h1AutoList
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
def h1Block3_0 : List NodeSpec := [([0,1,2],[],[0])]
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
lemma h1Bound : Lower h1R h1G 4 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 4,1,17)]) (by decide +kernel) h1Bucket3Ok (by decide +kernel)
def h2R : List Nat := varsOf 23
def h2G : Nat := 0xe0e08080e0e08080e0e08080e0e08080
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h2Bound : Lower h2R h2G 5 := lift_of (z := 0) (o := 4) (essPairs := [(VAR 2,3,7)]) (by decide +kernel) h1Bound
def h4R : List Nat := varsOf 14
def h4G : Nat := 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0
def h4Pos : List Nat := [10,12,6,6,12,10]
def h4Neg : List Nat := [8,8,2,4,4,2]
def h4Mask : Nat := fullMask 6
def h4Base : List Decor := [(0xcccccccccccccccccccccccccccccccc,45,36),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,30,24),(0xff00ff00ff00ff00ff00ff00ff00ff00,51,3)]
def h4Steps : List (Nat × Nat × Nat) := []
def h4W : BT Decor := buildWiresBT 2 h4Base h4Steps
def h4AutoList : List (List (Nat × Nat)) := [[]]
def h4Autos : BT (List (Nat × Nat)) := btOfList 1 h4AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4Pairs : goodPairs h4G h4Pos h4Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4BaseOk : ∀ x ∈ h4Base, faithful h4Pos h4Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4WOk : btAll (fun x => faithful h4Pos h4Neg x ∧ x.1 < 2^128) h4W := buildWiresBT_faithful h4BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h4G = h4G) h4Autos := btAll_ofList (autos_of (by decide +kernel))
def h4SliceList : List (Option (Nat × Nat)) := []
def h4Slices : BT (Option (Nat × Nat)) := btOfList 1 h4SliceList
def h4Specs : List PoolSpec := []
def h4Pools : BT (Option BoundPool) := buildPoolsBT 1 h4W h4R h4Slices h4Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h4R h4G p.1 p.2) h4Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h4R h4G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h4R h4G c) h4Pools := buildPoolsBT_sound h4SlicesOk
def h4Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h4G (3 - 1) xs.toFinset) h4Empty := trivial
def h4Block3_0 : List NodeSpec := [([0,1,2],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4Test3_0 : checkNodesBT h4W h4G h4Mask h4Pools h4Autos h4Empty 3 h4Block3_0 = true := by decide +kernel
def h4Nodes3 : List NodeSpec := h4Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4Check3 : checkNodesBT h4W h4G h4Mask h4Pools h4Autos h4Empty 3 h4Nodes3 = true := h4Test3_0
def h4Bucket3 : BT (List (List Nat)) := buildBucketsBT h4W h4Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h4G 3 xs.toFinset) h4Bucket3 := buildBucketsBT_sound (by decide) h4Pairs h4WOk h4PoolsOk h4AutosOk h4EmptyOk h4Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4Bound : Lower h4R h4G 4 := lower_of_forestBT (essPairs := [(VAR 1,4,6),(VAR 2,2,6),(VAR 3,2,10)]) (by decide +kernel) h4Bucket3Ok (by decide +kernel)
def h3R : List Nat := varsOf 30
def h3G : Nat := 0xfcf0fcc0fcf0fcc0fcf0fcc0fcf0fcc0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Bound : Lower h3R h3G 5 := lift_of (z := 16) (o := 0) (essPairs := [(VAR 4,4,20)]) (by decide +kernel) h4Bound
def h6R : List Nat := varsOf 15
def h6G : Nat := 0xa880a880a880a880a880a880a880a880
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Bound : Lower h6R h6G 5 := lift_of (z := 0) (o := 1) (essPairs := [(VAR 0,6,7)]) (by decide +kernel) h4Bound
def h7R : List Nat := varsOf 15
def h7G : Nat := 0xece0ece0ece0ece0ece0ece0ece0ece0
def h7Pos : List Nat := [5,11,6,6,5,11,10,13]
def h7Neg : List Nat := [4,9,4,2,1,3,2,9]
def h7Mask : Nat := fullMask 8
def h7Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,179,178),(0xcccccccccccccccccccccccccccccccc,110,104),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,157,5),(0xff00ff00ff00ff00ff00ff00ff00ff00,226,130)]
def h7Steps : List (Nat × Nat × Nat) := []
def h7W : BT Decor := buildWiresBT 2 h7Base h7Steps
def h7AutoList : List (List (Nat × Nat)) := [[]]
def h7Autos : BT (List (Nat × Nat)) := btOfList 1 h7AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Pairs : goodPairs h7G h7Pos h7Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7BaseOk : ∀ x ∈ h7Base, faithful h7Pos h7Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7WOk : btAll (fun x => faithful h7Pos h7Neg x ∧ x.1 < 2^128) h7W := buildWiresBT_faithful h7BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h7G = h7G) h7Autos := btAll_ofList (autos_of (by decide +kernel))
def h7SliceList : List (Option (Nat × Nat)) := []
def h7Slices : BT (Option (Nat × Nat)) := btOfList 1 h7SliceList
def h7Specs : List PoolSpec := []
def h7Pools : BT (Option BoundPool) := buildPoolsBT 1 h7W h7R h7Slices h7Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h7R h7G p.1 p.2) h7Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h7R h7G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h7R h7G c) h7Pools := buildPoolsBT_sound h7SlicesOk
def h7Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h7G (3 - 1) xs.toFinset) h7Empty := trivial
def h7Block3_0 : List NodeSpec := [([0,1,2,3],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Test3_0 : checkNodesBT h7W h7G h7Mask h7Pools h7Autos h7Empty 3 h7Block3_0 = true := by decide +kernel
def h7Nodes3 : List NodeSpec := h7Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Check3 : checkNodesBT h7W h7G h7Mask h7Pools h7Autos h7Empty 3 h7Nodes3 = true := h7Test3_0
def h7Bucket3 : BT (List (List Nat)) := buildBucketsBT h7W h7Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h7G 3 xs.toFinset) h7Bucket3 := buildBucketsBT_sound (by decide) h7Pairs h7WOk h7PoolsOk h7AutosOk h7EmptyOk h7Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Bound : Lower h7R h7G 4 := lower_of_forestBT (essPairs := [(VAR 0,4,5),(VAR 1,4,6),(VAR 2,1,5),(VAR 3,2,10)]) (by decide +kernel) h7Bucket3Ok (by decide +kernel)
def h8R : List Nat := varsOf 23
def h8G : Nat := 0xececa8a8ececa8a8ececa8a8ececa8a8
def h8Pos : List Nat := [5,3,3,21,22,5,21]
def h8Neg : List Nat := [4,1,2,20,20,1,17]
def h8Mask : Nat := fullMask 7
def h8Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,111,98),(0xcccccccccccccccccccccccccccccccc,22,4),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,121,25),(0xffff0000ffff0000ffff0000ffff0000,88,88)]
def h8Steps : List (Nat × Nat × Nat) := []
def h8W : BT Decor := buildWiresBT 2 h8Base h8Steps
def h8AutoList : List (List (Nat × Nat)) := [[]]
def h8Autos : BT (List (Nat × Nat)) := btOfList 1 h8AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8Pairs : goodPairs h8G h8Pos h8Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8BaseOk : ∀ x ∈ h8Base, faithful h8Pos h8Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8WOk : btAll (fun x => faithful h8Pos h8Neg x ∧ x.1 < 2^128) h8W := buildWiresBT_faithful h8BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h8G = h8G) h8Autos := btAll_ofList (autos_of (by decide +kernel))
def h8SliceList : List (Option (Nat × Nat)) := []
def h8Slices : BT (Option (Nat × Nat)) := btOfList 1 h8SliceList
def h8Specs : List PoolSpec := []
def h8Pools : BT (Option BoundPool) := buildPoolsBT 1 h8W h8R h8Slices h8Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h8R h8G p.1 p.2) h8Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h8R h8G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h8R h8G c) h8Pools := buildPoolsBT_sound h8SlicesOk
def h8Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h8G (3 - 1) xs.toFinset) h8Empty := trivial
def h8Block3_0 : List NodeSpec := [([0,1,2,3],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8Test3_0 : checkNodesBT h8W h8G h8Mask h8Pools h8Autos h8Empty 3 h8Block3_0 = true := by decide +kernel
def h8Nodes3 : List NodeSpec := h8Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8Check3 : checkNodesBT h8W h8G h8Mask h8Pools h8Autos h8Empty 3 h8Nodes3 = true := h8Test3_0
def h8Bucket3 : BT (List (List Nat)) := buildBucketsBT h8W h8Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h8G 3 xs.toFinset) h8Bucket3 := buildBucketsBT_sound (by decide) h8Pairs h8WOk h8PoolsOk h8AutosOk h8EmptyOk h8Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8Bound : Lower h8R h8G 4 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 4,2,18)]) (by decide +kernel) h8Bucket3Ok (by decide +kernel)
def h9R : List Nat := varsOf 27
def h9G : Nat := 0xeeeeaa88eeeeaa88eeeeaa88eeeeaa88
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Bound : Lower h9R h9G 5 := lift_of (z := 8) (o := 0) (essPairs := [(VAR 3,1,9)]) (by decide +kernel) h1Bound
def h5R : List Nat := varsOf 31
def h5G : Nat := 0xece0a880ece0a880ece0a880ece0a880
def h5Pos : List Nat := [13,22,13,13,7,11,13,21,22,7,21,26,7,22,26,7,11,11,21,26,27,21,11,29,11,7,11,30,22,11,22,29,21,27,30,11]
def h5Neg : List Nat := [12,20,14,9,3,3,5,5,6,4,17,10,6,18,24,5,14,10,20,18,25,19,2,28,1,1,9,28,28,25,4,25,1,19,14,19]
def h5Mask : Nat := fullMask 36
def h5Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xba7f796fd,0xba73084f8),(0xcccccccccccccccccccccccccccccccc,0xe7f5bfb32,0xe006b3934),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x5daa4b7df,0x4588593c7),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xeaddb486d,0x4bc93480d),(0xffff0000ffff0000ffff0000ffff0000,0x7d8bc6d82,0xab8bc6402)]
def h5Steps : List (Nat × Nat × Nat) := [(0,0,1),(2,0,1),(0,1,2),(3,1,2),(1,1,3),(2,1,3),(1,1,4),(2,1,4),(2,2,4),(0,2,5),(2,2,5),(0,2,6),(2,2,6),(1,3,4),(1,4,5),(0,0,2),(1,1,20),(2,1,20),(2,0,3),(2,0,14),(2,0,15),(1,3,7),(1,1,23),(2,1,23),(0,0,9),(2,0,10),(0,2,11),(2,2,12),(1,1,13),(2,1,13),(0,1,18),(3,1,18)]
def h5W : BT Decor := buildWiresBT 6 h5Base h5Steps
def h5AutoList : List (List (Nat × Nat)) := [[]]
def h5Autos : BT (List (Nat × Nat)) := btOfList 1 h5AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Pairs : goodPairs h5G h5Pos h5Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5BaseOk : ∀ x ∈ h5Base, faithful h5Pos h5Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5WOk : btAll (fun x => faithful h5Pos h5Neg x ∧ x.1 < 2^128) h5W := buildWiresBT_faithful h5BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h5G = h5G) h5Autos := btAll_ofList (autos_of (by decide +kernel))
def h5SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,5),some (subcubeFast 0 4,5),some (subcubeFast 0 8,4),some (subcubeFast 0 16,4),some (subcubeFast 8 0,5),some (subcubeFast 8 4,4),some (subcubeFast 16 0,5),some (subcubeFast 16 1,4)]
def h5Slices : BT (Option (Nat × Nat)) := btOfList 3 h5SliceList
def h5Specs : List PoolSpec := [(0,[]),(1,[]),(6,[(0,0,1)]),(2,[]),(4,[]),(3,[]),(6,[]),(0,[(1,4,5)]),(7,[]),(6,[(2,0,1)]),(4,[(0,0,2)]),(5,[]),(6,[(0,0,2)]),(1,[(2,0,3)]),(6,[(2,0,3)]),(4,[(0,1,2)]),(1,[(1,3,7)]),(4,[(3,1,2)]),(1,[(1,1,3)]),(0,[(1,1,4)]),(0,[(2,2,4)]),(4,[(2,2,4)]),(0,[(1,3,4)]),(1,[(1,3,4)])]
def h5Pools : BT (Option BoundPool) := buildPoolsBT 5 h5W h5R h5Slices h5Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Slice7 : Slice h5R h5G (subcubeFast 16 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h4Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Slice6 : Slice h5R h5G (subcubeFast 16 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h6Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Slice5 : Slice h5R h5G (subcubeFast 8 4) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h1Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Slice4 : Slice h5R h5G (subcubeFast 8 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h2Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Slice3 : Slice h5R h5G (subcubeFast 0 16) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h7Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Slice2 : Slice h5R h5G (subcubeFast 0 8) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h8Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Slice1 : Slice h5R h5G (subcubeFast 0 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h9Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Slice0 : Slice h5R h5G (subcubeFast 0 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h3Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h5R h5G p.1 p.2) h5Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h5R h5G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h5Slice0) (forall_cons (fun _ h => by cases h; exact h5Slice1) (forall_cons (fun _ h => by cases h; exact h5Slice2) (forall_cons (fun _ h => by cases h; exact h5Slice3) (forall_cons (fun _ h => by cases h; exact h5Slice4) (forall_cons (fun _ h => by cases h; exact h5Slice5) (forall_cons (fun _ h => by cases h; exact h5Slice6) (forall_cons (fun _ h => by cases h; exact h5Slice7) (fun _ h => (List.not_mem_nil h).elim)))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h5R h5G c) h5Pools := buildPoolsBT_sound h5SlicesOk
def h5Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h5G (4 - 1) xs.toFinset) h5Empty := trivial
def h5Block4_0 : List NodeSpec := [([1,2,3,6,19],[],[0]),([1,2,3,19,20],[],[0]),([0,1,4,20,26],[],[0]),([0,1,4,8,26],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Test4_0 : checkNodesBT h5W h5G h5Mask h5Pools h5Autos h5Empty 4 h5Block4_0 = true := by decide +kernel
def h5Nodes4 : List NodeSpec := h5Block4_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Check4 : checkNodesBT h5W h5G h5Mask h5Pools h5Autos h5Empty 4 h5Nodes4 = true := h5Test4_0
def h5Bucket4 : BT (List (List Nat)) := buildBucketsBT h5W h5Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h5G 4 xs.toFinset) h5Bucket4 := buildBucketsBT_sound (by decide) h5Pairs h5WOk h5PoolsOk h5AutosOk h5EmptyOk h5Check4
def h5Block5_0 : List NodeSpec := [([1,2,3,4,5,6],[0],[0]),([1,2,3,4,5,20],[1],[0]),([0,1,2,3,4,14],[3,4,5,6],[0]),([0,1,2,3,4,15],[],[0]),([0,1,2,3,19],[2,7],[0]),([0,1,2,3,5,19],[6],[0]),([0,1,2,3,4,16],[],[0]),([0,1,2,3,4,17],[3,4],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Test5_0 : checkNodesBT h5W h5G h5Mask h5Pools h5Autos h5Bucket4 5 h5Block5_0 = true := by decide +kernel
def h5Block5_1 : List NodeSpec := [([0,1,3,4,7,20],[0],[0]),([0,1,2,3,4,21],[0,1,3,4,5,6],[0]),([0,1,2,3,4,22],[],[0]),([0,1,2,3,4,27],[0,5,6],[0]),([0,1,2,3,4,28],[],[0]),([0,1,2,3,4,24],[],[0]),([0,1,3,4,7,8],[0],[0]),([0,1,2,4,26],[15,16],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Test5_1 : checkNodesBT h5W h5G h5Mask h5Pools h5Autos h5Bucket4 5 h5Block5_1 = true := by decide +kernel
def h5Block5_2 : List NodeSpec := [([0,1,2,4,7,26],[4],[0]),([0,1,2,3,4,25],[5,6],[0]),([0,1,2,3,4,29],[5,6],[0]),([0,1,2,3,4,30],[],[0]),([0,1,2,3,4,31],[3,4],[0]),([0,1,2,3,4,32],[],[0]),([0,1,2,3,4,33],[1,3,4],[0]),([0,1,2,3,4,34],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Test5_2 : checkNodesBT h5W h5G h5Mask h5Pools h5Autos h5Bucket4 5 h5Block5_2 = true := by decide +kernel
def h5Block5_3 : List NodeSpec := [([0,1,2,3,4,35],[],[0]),([0,1,2,3,4,36],[4,6],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Test5_3 : checkNodesBT h5W h5G h5Mask h5Pools h5Autos h5Bucket4 5 h5Block5_3 = true := by decide +kernel
def h5Nodes5 : List NodeSpec := h5Block5_0 ++ h5Block5_1 ++ h5Block5_2 ++ h5Block5_3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Check5 : checkNodesBT h5W h5G h5Mask h5Pools h5Autos h5Bucket4 5 h5Nodes5 = true := by
  unfold h5Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨h5Test5_0,h5Test5_1⟩,h5Test5_2⟩,h5Test5_3⟩
def h5Bucket5 : BT (List (List Nat)) := buildBucketsBT h5W h5Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h5G 5 xs.toFinset) h5Bucket5 := buildBucketsBT_sound (by decide) h5Pairs h5WOk h5PoolsOk h5AutosOk h5Bucket4Ok h5Check5
def h5Block6_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,4,5,6,8],[0]),([0,1,2,3,4,6],[0,1,3,4,5,6,8,9],[0]),([0,1,2,3,4,20],[0,1,3,4,5,6,8,10,11,12],[0]),([0,1,2,3,4,23],[0,1,3,4,5,6,11,13,14],[0]),([0,1,2,3,4,7],[0,1,3,4,5,6,11,15],[0]),([0,1,2,3,4,8],[0,1,3,4,5,6,11,17],[0]),([0,1,2,3,4,9],[0,1,3,4,5,6,11,18],[0]),([0,1,2,3,4,10],[0,1,3,4,5,6,11],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Test6_0 : checkNodesBT h5W h5G h5Mask h5Pools h5Autos h5Bucket5 6 h5Block6_0 = true := by decide +kernel
def h5Block6_1 : List NodeSpec := [([0,1,2,3,4,11],[0,1,3,4,5,6,8,19],[0]),([0,1,2,3,4,12],[0,1,3,4,5,6,8],[0]),([0,1,2,3,4,13],[0,1,3,4,5,6,8,20,21],[0]),([0,1,2,3,4,18],[0,1,3,4,5,6,8,11,22,23],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Test6_1 : checkNodesBT h5W h5G h5Mask h5Pools h5Autos h5Bucket5 6 h5Block6_1 = true := by decide +kernel
def h5Nodes6 : List NodeSpec := h5Block6_0 ++ h5Block6_1
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Check6 : checkNodesBT h5W h5G h5Mask h5Pools h5Autos h5Bucket5 6 h5Nodes6 = true := by
  unfold h5Nodes6 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h5Test6_0,h5Test6_1⟩
def h5Bucket6 : BT (List (List Nat)) := buildBucketsBT h5W h5Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h5G 6 xs.toFinset) h5Bucket6 := buildBucketsBT_sound (by decide) h5Pairs h5WOk h5PoolsOk h5AutosOk h5Bucket5Ok h5Check6
def h5Block7_0 : List NodeSpec := [([0,1,2,3,4],[0,1,4,6,8,11],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Test7_0 : checkNodesBT h5W h5G h5Mask h5Pools h5Autos h5Bucket6 7 h5Block7_0 = true := by decide +kernel
def h5Nodes7 : List NodeSpec := h5Block7_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Check7 : checkNodesBT h5W h5G h5Mask h5Pools h5Autos h5Bucket6 7 h5Nodes7 = true := h5Test7_0
def h5Bucket7 : BT (List (List Nat)) := buildBucketsBT h5W h5Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h5G 7 xs.toFinset) h5Bucket7 := buildBucketsBT_sound (by decide) h5Pairs h5WOk h5PoolsOk h5AutosOk h5Bucket6Ok h5Check7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Bound : Lower h5R h5G 8 := lower_of_forestBT (essPairs := [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11),(VAR 4,5,21)]) (by decide +kernel) h5Bucket7Ok (by decide +kernel)
def h10R : List Nat := varsOf 42
def h10G : Nat := 0xffccffcccc00cc00ffccffcccc00cc00
def h10Pos : List Nat := [34,40,10,10,40,34]
def h10Neg : List Nat := [32,32,2,8,8,2]
def h10Mask : Nat := fullMask 6
def h10Base : List Decor := [(0xcccccccccccccccccccccccccccccccc,45,36),(0xff00ff00ff00ff00ff00ff00ff00ff00,30,24),(0xffffffff00000000ffffffff00000000,51,3)]
def h10Steps : List (Nat × Nat × Nat) := []
def h10W : BT Decor := buildWiresBT 2 h10Base h10Steps
def h10AutoList : List (List (Nat × Nat)) := [[]]
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
def h10Block3_0 : List NodeSpec := [([0,1,2],[],[0])]
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
lemma h10Bound : Lower h10R h10G 4 := lower_of_forestBT (essPairs := [(VAR 1,8,10),(VAR 3,2,10),(VAR 5,2,34)]) (by decide +kernel) h10Bucket3Ok (by decide +kernel)
def h11R : List Nat := varsOf 45
def h11G : Nat := 0xfaaafaaaaaa0aaa0faaafaaaaaa0aaa0
def h11Pos : List Nat := [9,44,9,33,5,9,44,33,44,5,5,5,9,5,33,13,13,37,37,41,41]
def h11Neg : List Nat := [8,40,12,32,4,1,36,1,12,1,0,12,0,36,0,12,1,36,1,40,1]
def h11Mask : Nat := fullMask 21
def h11Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x1ffebd,0x1502a0),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x7af52,0x2a954),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x199167,0x88907),(0xffffffff00000000ffffffff00000000,0x1e41ca,0xa204a)]
def h11Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(3,0,1),(0,0,2),(1,0,2),(2,0,2),(3,0,2),(0,0,3),(1,0,3),(2,0,3),(3,0,3),(0,1,2),(1,1,2),(2,1,2),(3,1,2),(0,1,3),(1,1,3),(2,1,3),(3,1,3),(0,2,3),(1,2,3),(2,2,3),(3,2,3),(1,2,4),(0,1,28),(2,2,4),(1,3,4),(0,1,31),(2,3,4),(0,2,5),(1,1,34),(3,2,5),(0,3,5),(1,1,37),(3,3,5),(2,1,8),(1,3,8),(0,2,41),(2,3,8),(3,1,9),(0,3,9),(1,2,45),(3,3,9),(2,1,12),(2,2,12),(3,1,13),(3,2,13),(1,3,18),(0,1,52),(2,3,18),(1,2,54),(1,3,19),(0,2,56),(2,3,19),(1,1,58),(1,2,22),(0,1,60),(2,2,23),(1,1,62)]
def h11W : BT Decor := buildWiresBT 6 h11Base h11Steps
def h11AutoList : List (List (Nat × Nat)) := [[]]
def h11Autos : BT (List (Nat × Nat)) := btOfList 1 h11AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Pairs : goodPairs h11G h11Pos h11Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11BaseOk : ∀ x ∈ h11Base, faithful h11Pos h11Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11WOk : btAll (fun x => faithful h11Pos h11Neg x ∧ x.1 < 2^128) h11W := buildWiresBT_faithful h11BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h11G = h11G) h11Autos := btAll_ofList (autos_of (by decide +kernel))
def h11SliceList : List (Option (Nat × Nat)) := []
def h11Slices : BT (Option (Nat × Nat)) := btOfList 1 h11SliceList
def h11Specs : List PoolSpec := []
def h11Pools : BT (Option BoundPool) := buildPoolsBT 1 h11W h11R h11Slices h11Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h11R h11G p.1 p.2) h11Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h11R h11G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h11R h11G c) h11Pools := buildPoolsBT_sound h11SlicesOk
def h11Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h11G (3 - 1) xs.toFinset) h11Empty := trivial
def h11Block3_0 : List NodeSpec := [([0,1,3,28],[],[0]),([0,1,3,30],[],[0]),([0,1,2,31],[],[0]),([0,1,2,33],[],[0]),([0,1,3,34],[],[0]),([0,1,3,36],[],[0]),([0,1,2,37],[],[0]),([0,1,2,39],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Test3_0 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Empty 3 h11Block3_0 = true := by decide +kernel
def h11Block3_1 : List NodeSpec := [([0,2,3,35],[],[0]),([0,2,3,40],[],[0]),([0,1,2,41],[],[0]),([0,1,2,43],[],[0]),([0,2,3,29],[],[0]),([0,2,3,44],[],[0]),([0,1,2,45],[],[0]),([0,1,2,47],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Test3_1 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Empty 3 h11Block3_1 = true := by decide +kernel
def h11Block3_2 : List NodeSpec := [([0,2,3,38],[],[0]),([0,2,3,48],[],[0]),([0,1,3,46],[],[0]),([0,1,3,49],[],[0]),([0,2,3,32],[],[0]),([0,2,3,50],[],[0]),([0,1,3,42],[],[0]),([0,1,3,51],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Test3_2 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Empty 3 h11Block3_2 = true := by decide +kernel
def h11Block3_3 : List NodeSpec := [([0,3,16,17],[],[0]),([0,1,2,52],[],[0]),([0,1,2,54],[],[0]),([0,1,2,56],[],[0]),([0,1,2,58],[],[0]),([0,2,20,21],[],[0]),([0,1,3,60],[],[0]),([0,1,3,57],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Test3_3 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Empty 3 h11Block3_3 = true := by decide +kernel
def h11Block3_4 : List NodeSpec := [([0,1,3,55],[],[0]),([0,1,3,62],[],[0]),([0,1,24,25],[],[0]),([0,2,3,63],[],[0]),([0,2,3,53],[],[0]),([0,2,3,59],[],[0]),([0,2,3,61],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Test3_4 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Empty 3 h11Block3_4 = true := by decide +kernel
def h11Nodes3 : List NodeSpec := h11Block3_0 ++ h11Block3_1 ++ h11Block3_2 ++ h11Block3_3 ++ h11Block3_4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Check3 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Empty 3 h11Nodes3 = true := by
  unfold h11Nodes3 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨h11Test3_0,h11Test3_1⟩,h11Test3_2⟩,h11Test3_3⟩,h11Test3_4⟩
def h11Bucket3 : BT (List (List Nat)) := buildBucketsBT h11W h11Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h11G 3 xs.toFinset) h11Bucket3 := buildBucketsBT_sound (by decide) h11Pairs h11WOk h11PoolsOk h11AutosOk h11EmptyOk h11Check3
def h11Block4_0 : List NodeSpec := [([0,1,2,3,4],[],[0]),([0,1,2,3,5],[],[0]),([0,1,2,3,6],[],[0]),([0,1,2,3,7],[],[0]),([0,1,2,3,8],[],[0]),([0,1,2,3,9],[],[0]),([0,1,2,3,10],[],[0]),([0,1,2,3,11],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Test4_0 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Bucket3 4 h11Block4_0 = true := by decide +kernel
def h11Block4_1 : List NodeSpec := [([0,1,2,3,12],[],[0]),([0,1,2,3,13],[],[0]),([0,1,2,3,14],[],[0]),([0,1,2,3,15],[],[0]),([0,1,2,3,16],[],[0]),([0,1,2,3,17],[],[0]),([0,1,2,3,18],[],[0]),([0,1,2,3,19],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Test4_1 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Bucket3 4 h11Block4_1 = true := by decide +kernel
def h11Block4_2 : List NodeSpec := [([0,1,2,3,20],[],[0]),([0,1,2,3,21],[],[0]),([0,1,2,3,22],[],[0]),([0,1,2,3,23],[],[0]),([0,1,2,3,24],[],[0]),([0,1,2,3,25],[],[0]),([0,1,2,3,26],[],[0]),([0,1,2,3,27],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Test4_2 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Bucket3 4 h11Block4_2 = true := by decide +kernel
def h11Nodes4 : List NodeSpec := h11Block4_0 ++ h11Block4_1 ++ h11Block4_2
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Check4 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Bucket3 4 h11Nodes4 = true := by
  unfold h11Nodes4 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨h11Test4_0,h11Test4_1⟩,h11Test4_2⟩
def h11Bucket4 : BT (List (List Nat)) := buildBucketsBT h11W h11Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h11G 4 xs.toFinset) h11Bucket4 := buildBucketsBT_sound (by decide) h11Pairs h11WOk h11PoolsOk h11AutosOk h11Bucket3Ok h11Check4
def h11Block5_0 : List NodeSpec := [([0,1,2,3],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Test5_0 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Bucket4 5 h11Block5_0 = true := by decide +kernel
def h11Nodes5 : List NodeSpec := h11Block5_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Check5 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Bucket4 5 h11Nodes5 = true := h11Test5_0
def h11Bucket5 : BT (List (List Nat)) := buildBucketsBT h11W h11Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h11G 5 xs.toFinset) h11Bucket5 := buildBucketsBT_sound (by decide) h11Pairs h11WOk h11PoolsOk h11AutosOk h11Bucket4Ok h11Check5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Bound : Lower h11R h11G 6 := lower_of_forestBT (essPairs := [(VAR 0,4,5),(VAR 2,1,5),(VAR 3,1,9),(VAR 5,1,33)]) (by decide +kernel) h11Bucket5Ok (by decide +kernel)
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

end Cofactor12086
def h12R : List Nat := varsOf 46
def h12G : Nat := 0xfffcfffcfcc0fcc0fffcfffcfcc0fcc0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h12Bound : Lower h12R h12G 7 := carry_of (swaps := [(4,5),(2,3),(1,2),(0,1)]) (roots2 := Cofactor12086.R_17) (T2 := Cofactor12086.G_17) (by decide +kernel) Cofactor12086.low_17
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

def G_11 : Nat := 0xff00f000f0000000ff00f000f0000000
def R_11 : List Nat := varsOf 60
lemma low_11_ok : liftCheck 0 8 R_11 G_11 R_0 G_0 [(VAR 3,28,20)] = true := by decide +kernel
lemma low_11 : Lower R_11 G_11 5 := lift_of low_11_ok low_0

def G_12 : Nat := 0xfff0ff00ff00f000fff0ff00ff00f000
def R_12 : List Nat := varsOf 60
def pos_12 : List Nat := [12,12,24,24,28,40,40,44,52,52,52,56,12,12,12,24,24,24,40,40,40,52]
def neg_12 : List Nat := [8,4,16,8,20,32,8,36,48,36,20,48,20,36,48,20,36,48,20,36,48,8]
def fmask_12 : Nat := fullMask 22
def base_12 : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x207793,0xdb692),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x1ff8ff,0x200049),(0xffff0000ffff0000ffff0000ffff0000,0x238f1c,0x16dd14),(0xffffffff00000000ffffffff00000000,0x3c0fe0,0x1b6ba0)]
def steps_12 : List (Nat × Nat × Nat) := [(2,0,2),(1,0,2),(2,0,1),(0,0,2),(3,0,1),(1,0,1),(0,0,1),(3,0,2),(3,4,3),(2,9,2),(0,9,2),(1,4,3),(3,10,2),(1,10,2),(3,7,5)]
def W_12 : BT Decor := buildWiresBT 5 base_12 steps_12
def autosL_12 : List (List (Nat × Nat)) := [[],[(4,5)],[(2,4)],[(2,5),(2,4)],[(2,4),(2,5)],[(2,5)]]
def autos_12 : BT (List (Nat × Nat)) := btOfList 3 autosL_12
def slicesL_12 : List (Option (Nat × Nat)) := []
def slices_12 : BT (Option (Nat × Nat)) := btOfList 1 slicesL_12
def ps_12 : List PoolSpec := []
def P_12 : BT (Option BoundPool) := buildPoolsBT 1 W_12 R_12 slices_12 ps_12
lemma gp_12 : goodPairs G_12 pos_12 neg_12 := goodPairs_of (by decide +kernel)
lemma base_12_ok : ∀ x ∈ base_12, faithful pos_12 neg_12 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_12_ok : btAll (fun x => faithful pos_12 neg_12 x ∧ x.1 < 2^128) W_12 := buildWiresBT_faithful base_12_ok
set_option maxRecDepth 500000 in
lemma autos_12_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_12 = G_12) autos_12 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma slices_12_ok : btAll (fun o => ∀ p, o = some p → Slice R_12 G_12 p.1 p.2) slices_12 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_12 G_12 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 500000 in
lemma P_12_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_12 G_12 c) P_12 := buildPoolsBT_sound slices_12_ok
def bk_12_init : BT (List (List Nat)) := BT.empty
lemma bk_12_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_12 (0 - 1) xs.toFinset) bk_12_init := trivial
def nodes_12_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_12_0 : checkNodesBT W_12 G_12 fmask_12 P_12 autos_12 bk_12_init 0 nodes_12_0 = true := by decide +kernel
def bk_12_0 : BT (List (List Nat)) := buildBucketsBT W_12 nodes_12_0
set_option maxRecDepth 500000 in
lemma bk_12_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_12 0 xs.toFinset) bk_12_0 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok P_12_ok autos_12_ok bk_12_init_ok chk_12_0
def nodes_12_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_12_1 : checkNodesBT W_12 G_12 fmask_12 P_12 autos_12 bk_12_0 1 nodes_12_1 = true := by decide +kernel
def bk_12_1 : BT (List (List Nat)) := buildBucketsBT W_12 nodes_12_1
set_option maxRecDepth 500000 in
lemma bk_12_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_12 1 xs.toFinset) bk_12_1 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok P_12_ok autos_12_ok bk_12_0_ok chk_12_1
def nodes_12_2 : List NodeSpec := [([18,1,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_12_2 : checkNodesBT W_12 G_12 fmask_12 P_12 autos_12 bk_12_1 2 nodes_12_2 = true := by decide +kernel
def bk_12_2 : BT (List (List Nat)) := buildBucketsBT W_12 nodes_12_2
set_option maxRecDepth 500000 in
lemma bk_12_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_12 2 xs.toFinset) bk_12_2 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok P_12_ok autos_12_ok bk_12_1_ok chk_12_2
def nodes_12_3 : List NodeSpec := [([4,11,1,3],[],[0]),([0,1,2,12],[],[]),([7,1,5,3],[],[0]),([13,0,1,3],[],[]),([0,1,14,3],[],[]),([6,8,2,3],[],[]),([0,1,2,15],[],[]),([16,0,1,3],[],[]),([0,1,17,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_12_3 : checkNodesBT W_12 G_12 fmask_12 P_12 autos_12 bk_12_2 3 nodes_12_3 = true := by decide +kernel
def bk_12_3 : BT (List (List Nat)) := buildBucketsBT W_12 nodes_12_3
set_option maxRecDepth 500000 in
lemma bk_12_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_12 3 xs.toFinset) bk_12_3 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok P_12_ok autos_12_ok bk_12_2_ok chk_12_3
def nodes_12_4 : List NodeSpec := [([4,0,1,2,3],[],[0]),([0,1,2,5,3],[],[0]),([6,0,1,2,3],[],[0]),([7,0,1,2,3],[],[0]),([8,0,1,2,3],[],[0]),([0,1,9,2,3],[],[0,1]),([10,0,1,2,3],[],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_12_4 : checkNodesBT W_12 G_12 fmask_12 P_12 autos_12 bk_12_3 4 nodes_12_4 = true := by decide +kernel
def bk_12_4 : BT (List (List Nat)) := buildBucketsBT W_12 nodes_12_4
set_option maxRecDepth 500000 in
lemma bk_12_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_12 4 xs.toFinset) bk_12_4 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok P_12_ok autos_12_ok bk_12_3_ok chk_12_4
def nodes_12_5 : List NodeSpec := [([0,1,2,3],[],[0,2,1,3,4,5])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_12_5 : checkNodesBT W_12 G_12 fmask_12 P_12 autos_12 bk_12_4 5 nodes_12_5 = true := by decide +kernel
def bk_12_5 : BT (List (List Nat)) := buildBucketsBT W_12 nodes_12_5
set_option maxRecDepth 500000 in
lemma bk_12_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_12 5 xs.toFinset) bk_12_5 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok P_12_ok autos_12_ok bk_12_4_ok chk_12_5
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_12_ok : forestRootCheck R_12 G_12 [(VAR 2,12,8),(VAR 3,12,4),(VAR 4,24,8),(VAR 5,40,8)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_12_in : bucketContainsBT bk_12_5 R_12 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_12 : Lower R_12 G_12 6 := lower_of_forestBT root_12_ok bk_12_5_ok root_12_in

def G_13 : Nat := 0xfffffcfcfcfcc0c0fffffcfcfcfcc0c0
def R_13 : List Nat := varsOf 54
def pos_13 : List Nat := [6,6,18,18,20,20,34,34,36,36,48,48,6,6,18,18,20,20,34,34,36,36,48,48]
def neg_13 : List Nat := [4,2,16,2,16,4,32,2,32,4,32,16,16,32,4,32,2,32,4,16,2,16,2,4]
def fmask_13 : Nat := fullMask 24
def base_13 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xcf0cf,0x51008a),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x333333,0x844221),(0xffff0000ffff0000ffff0000ffff0000,0xc3cc3c,0x281814),(0xffffffff00000000ffffffff00000000,0xfc0fc0,0x2a540)]
def steps_13 : List (Nat × Nat × Nat) := [(1,0,1),(2,4,2),(1,4,2),(1,0,2),(2,6,3),(1,1,2)]
def W_13 : BT Decor := buildWiresBT 4 base_13 steps_13
def autosL_13 : List (List (Nat × Nat)) := [[],[(4,5)],[(1,2)],[(4,5),(1,2)],[(2,4)],[(2,5),(2,4)],[(1,2),(1,4)],[(2,5),(1,2),(1,4)],[(2,5),(1,4)]]
def autos_13 : BT (List (Nat × Nat)) := btOfList 4 autosL_13
def slicesL_13 : List (Option (Nat × Nat)) := [some (subcubeFast 4 0,4),some (subcubeFast 2 0,4),some (subcubeFast 32 0,4),some (subcubeFast 16 0,4)]
def slices_13 : BT (Option (Nat × Nat)) := btOfList 2 slicesL_13
def ps_13 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[])]
def P_13 : BT (Option BoundPool) := buildPoolsBT 2 W_13 R_13 slices_13 ps_13
lemma gp_13 : goodPairs G_13 pos_13 neg_13 := goodPairs_of (by decide +kernel)
lemma base_13_ok : ∀ x ∈ base_13, faithful pos_13 neg_13 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_13_ok : btAll (fun x => faithful pos_13 neg_13 x ∧ x.1 < 2^128) W_13 := buildWiresBT_faithful base_13_ok
set_option maxRecDepth 500000 in
lemma autos_13_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_13 = G_13) autos_13 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_13_0_ok : sliceDirectCheck 4 0 0 R_13 G_13 R_9 G_9 = true := by decide +kernel
lemma sl_13_0 : Slice R_13 G_13 (subcubeFast 4 0) 4 := slice_fast_direct sl_13_0_ok low_9
lemma sl_13_1_ok : sliceDirectCheck 2 0 0 R_13 G_13 R_0 G_0 = true := by decide +kernel
lemma sl_13_1 : Slice R_13 G_13 (subcubeFast 2 0) 4 := slice_fast_direct sl_13_1_ok low_0
lemma sl_13_2_ok : sliceDirectCheck 32 0 0 R_13 G_13 R_6 G_6 = true := by decide +kernel
lemma sl_13_2 : Slice R_13 G_13 (subcubeFast 32 0) 4 := slice_fast_direct sl_13_2_ok low_6
lemma sl_13_3_ok : sliceDirectCheck 16 0 0 R_13 G_13 R_7 G_7 = true := by decide +kernel
lemma sl_13_3 : Slice R_13 G_13 (subcubeFast 16 0) 4 := slice_fast_direct sl_13_3_ok low_7
set_option maxRecDepth 500000 in
lemma slices_13_ok : btAll (fun o => ∀ p, o = some p → Slice R_13 G_13 p.1 p.2) slices_13 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_13 G_13 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_13_0) (forall_cons (fun _ h => by cases h; exact sl_13_1) (forall_cons (fun _ h => by cases h; exact sl_13_2) (forall_cons (fun _ h => by cases h; exact sl_13_3) (fun _ h => (List.not_mem_nil h).elim)))))
set_option maxRecDepth 500000 in
lemma P_13_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_13 G_13 c) P_13 := buildPoolsBT_sound slices_13_ok
def bk_13_init : BT (List (List Nat)) := BT.empty
lemma bk_13_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_13 (0 - 1) xs.toFinset) bk_13_init := trivial
def nodes_13_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_13_0 : checkNodesBT W_13 G_13 fmask_13 P_13 autos_13 bk_13_init 0 nodes_13_0 = true := by decide +kernel
def bk_13_0 : BT (List (List Nat)) := buildBucketsBT W_13 nodes_13_0
set_option maxRecDepth 500000 in
lemma bk_13_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_13 0 xs.toFinset) bk_13_0 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok P_13_ok autos_13_ok bk_13_init_ok chk_13_0
def nodes_13_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_13_1 : checkNodesBT W_13 G_13 fmask_13 P_13 autos_13 bk_13_0 1 nodes_13_1 = true := by decide +kernel
def bk_13_1 : BT (List (List Nat)) := buildBucketsBT W_13 nodes_13_1
set_option maxRecDepth 500000 in
lemma bk_13_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_13 1 xs.toFinset) bk_13_1 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok P_13_ok autos_13_ok bk_13_0_ok chk_13_1
def nodes_13_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_13_2 : checkNodesBT W_13 G_13 fmask_13 P_13 autos_13 bk_13_1 2 nodes_13_2 = true := by decide +kernel
def bk_13_2 : BT (List (List Nat)) := buildBucketsBT W_13 nodes_13_2
set_option maxRecDepth 500000 in
lemma bk_13_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_13 2 xs.toFinset) bk_13_2 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok P_13_ok autos_13_ok bk_13_1_ok chk_13_2
def nodes_13_3 : List NodeSpec := [([8,0,1,2],[],[]),([4,7,9,3],[0,1],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_13_3 : checkNodesBT W_13 G_13 fmask_13 P_13 autos_13 bk_13_2 3 nodes_13_3 = true := by decide +kernel
def bk_13_3 : BT (List (List Nat)) := buildBucketsBT W_13 nodes_13_3
set_option maxRecDepth 500000 in
lemma bk_13_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_13 3 xs.toFinset) bk_13_3 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok P_13_ok autos_13_ok bk_13_2_ok chk_13_3
def nodes_13_4 : List NodeSpec := [([5,0,1,2,3],[],[]),([0,1,2,6,3],[2],[0]),([1,4,2,7,3],[0,3],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_13_4 : checkNodesBT W_13 G_13 fmask_13 P_13 autos_13 bk_13_3 4 nodes_13_4 = true := by decide +kernel
def bk_13_4 : BT (List (List Nat)) := buildBucketsBT W_13 nodes_13_4
set_option maxRecDepth 500000 in
lemma bk_13_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_13 4 xs.toFinset) bk_13_4 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok P_13_ok autos_13_ok bk_13_3_ok chk_13_4
def nodes_13_5 : List NodeSpec := [([0,1,4,2,3],[0,1,3,2],[0,1,2,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_13_5 : checkNodesBT W_13 G_13 fmask_13 P_13 autos_13 bk_13_4 5 nodes_13_5 = true := by decide +kernel
def bk_13_5 : BT (List (List Nat)) := buildBucketsBT W_13 nodes_13_5
set_option maxRecDepth 500000 in
lemma bk_13_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_13 5 xs.toFinset) bk_13_5 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok P_13_ok autos_13_ok bk_13_4_ok chk_13_5
def nodes_13_6 : List NodeSpec := [([0,1,2,3],[0,1,3,2],[0,4,5,6,7,8])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_13_6 : checkNodesBT W_13 G_13 fmask_13 P_13 autos_13 bk_13_5 6 nodes_13_6 = true := by decide +kernel
def bk_13_6 : BT (List (List Nat)) := buildBucketsBT W_13 nodes_13_6
set_option maxRecDepth 500000 in
lemma bk_13_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_13 6 xs.toFinset) bk_13_6 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok P_13_ok autos_13_ok bk_13_5_ok chk_13_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_13_ok : forestRootCheck R_13 G_13 [(VAR 1,6,4),(VAR 2,6,2),(VAR 4,18,2),(VAR 5,34,2)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_13_in : bucketContainsBT bk_13_6 R_13 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_13 : Lower R_13 G_13 7 := lower_of_forestBT root_13_ok bk_13_6_ok root_13_in

def G_23 : Nat := 0xfc00c000fc00c000fc00c000fc00c000
def R_23 : List Nat := varsOf 30
lemma low_23_ok : carryOK [(1,5),(1,4),(1,2)] R_23 G_23 R_11 G_11 = true := by decide +kernel
lemma low_23 : Lower R_23 G_23 5 := carry_of low_23_ok low_11

def G_24 : Nat := 0xfc00fc00c000c000fc00fc00c000c000
def R_24 : List Nat := varsOf 46
lemma low_24_ok : carryOK [(1,4),(1,2)] R_24 G_24 R_11 G_11 = true := by decide +kernel
lemma low_24 : Lower R_24 G_24 5 := carry_of low_24_ok low_11

def G_29 : Nat := 0xff00cc00cc000000ff00cc00cc000000
def R_29 : List Nat := varsOf 58
lemma low_29_ok : carryOK [(1,2)] R_29 G_29 R_11 G_11 = true := by decide +kernel
lemma low_29 : Lower R_29 G_29 5 := carry_of low_29_ok low_11

def G_35 : Nat := 0xffc0fc00ffc0fc00ffc0fc00ffc0fc00
def R_35 : List Nat := varsOf 30
lemma low_35_ok : carryOK [(1,5),(1,4),(1,2)] R_35 G_35 R_12 G_12 = true := by decide +kernel
lemma low_35 : Lower R_35 G_35 6 := carry_of low_35_ok low_12

def G_36 : Nat := 0xffc0ffc0fc00fc00ffc0ffc0fc00fc00
def R_36 : List Nat := varsOf 46
lemma low_36_ok : carryOK [(1,4),(1,2)] R_36 G_36 R_12 G_12 = true := by decide +kernel
lemma low_36 : Lower R_36 G_36 6 := carry_of low_36_ok low_12

def G_37 : Nat := 0xffccff00ff00cc00ffccff00ff00cc00
def R_37 : List Nat := varsOf 58
lemma low_37_ok : carryOK [(1,2)] R_37 G_37 R_12 G_12 = true := by decide +kernel
lemma low_37 : Lower R_37 G_37 6 := carry_of low_37_ok low_12

def G_42 : Nat := 0xffc0fc00fc00c000ffc0fc00fc00c000
def R_42 : List Nat := varsOf 62
def pos_42 : List Nat := [14,14,14,26,26,26,28,28,28,30,42,42,42,44,44,44,46,54,54,54,54,56,56,56,58,60,14,14,14,14,14,14,26,26,26,26,26,26,28,28,28,28,28,28,42,42,42,42,42,42,44,44,44,44,44,44,54,54,54,54,56,56,56,56,56,56]
def neg_42 : List Nat := [12,10,6,24,18,10,24,20,12,22,40,34,10,40,36,12,38,52,50,38,22,48,40,24,50,52,22,24,38,40,50,52,12,22,38,40,50,52,10,22,38,40,50,52,12,22,24,38,50,52,10,22,24,38,50,52,10,12,24,40,10,12,22,38,50,52]
def fmask_42 : Nat := fullMask 66
def base_42 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xf03f03ffd1f1e3f,0x1d16da5d6551d1a36),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffc0fc0fe1fe3c7,0x2e2aab9a7961bc385),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x3f0ffffffffe1ffff,0x3f14524928c0b56b),(0xffff0000ffff0000ffff0000ffff0000,0x3ff000fff03fe03f8,0x344db6cb2cfb602d8),(0xffffffff00000000ffffffff00000000,0x3fffff00003fffc00,0x388e38f3cf36f6c00)]
def steps_42 : List (Nat × Nat × Nat) := [(0,0,1),(0,3,4),(1,5,6)]
def W_42 : BT Decor := buildWiresBT 3 base_42 steps_42
def autosL_42 : List (List (Nat × Nat)) := [[],[(2,4)],[(2,5),(2,4)],[(1,2),(1,4)],[(2,5),(1,2),(1,4)],[(2,5),(1,4)]]
def autos_42 : BT (List (Nat × Nat)) := btOfList 3 autosL_42
def slicesL_42 : List (Option (Nat × Nat)) := [some (subcubeFast 4 0,5),some (subcubeFast 32 0,5),some (subcubeFast 0 16,6),some (subcubeFast 16 0,5),some (subcubeFast 0 32,6),some (subcubeFast 0 2,6),some (subcubeFast 2 0,5),some (subcubeFast 0 4,6),some (subcubeFast 0 8,7),some (subcubeFast 4 8,4)]
def slices_42 : BT (Option (Nat × Nat)) := btOfList 4 slicesL_42
def ps_42 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[(0,3,4)]),(6,[]),(7,[]),(4,[(0,0,1)]),(5,[]),(8,[]),(9,[]),(2,[(0,0,1)])]
def P_42 : BT (Option BoundPool) := buildPoolsBT 4 W_42 R_42 slices_42 ps_42
lemma gp_42 : goodPairs G_42 pos_42 neg_42 := goodPairs_of (by decide +kernel)
lemma base_42_ok : ∀ x ∈ base_42, faithful pos_42 neg_42 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_42_ok : btAll (fun x => faithful pos_42 neg_42 x ∧ x.1 < 2^128) W_42 := buildWiresBT_faithful base_42_ok
set_option maxRecDepth 500000 in
lemma autos_42_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_42 = G_42) autos_42 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_42_0_ok : sliceDirectCheck 4 0 0 R_42 G_42 R_29 G_29 = true := by decide +kernel
lemma sl_42_0 : Slice R_42 G_42 (subcubeFast 4 0) 5 := slice_fast_direct sl_42_0_ok low_29
lemma sl_42_1_ok : sliceDirectCheck 32 0 0 R_42 G_42 R_23 G_23 = true := by decide +kernel
lemma sl_42_1 : Slice R_42 G_42 (subcubeFast 32 0) 5 := slice_fast_direct sl_42_1_ok low_23
lemma sl_42_2_ok : sliceDirectCheck 0 16 0 R_42 G_42 R_36 G_36 = true := by decide +kernel
lemma sl_42_2 : Slice R_42 G_42 (subcubeFast 0 16) 6 := slice_fast_direct sl_42_2_ok low_36
lemma sl_42_3_ok : sliceDirectCheck 16 0 0 R_42 G_42 R_24 G_24 = true := by decide +kernel
lemma sl_42_3 : Slice R_42 G_42 (subcubeFast 16 0) 5 := slice_fast_direct sl_42_3_ok low_24
lemma sl_42_4_ok : sliceDirectCheck 0 32 0 R_42 G_42 R_35 G_35 = true := by decide +kernel
lemma sl_42_4 : Slice R_42 G_42 (subcubeFast 0 32) 6 := slice_fast_direct sl_42_4_ok low_35
lemma sl_42_5_ok : sliceDirectCheck 0 2 0 R_42 G_42 R_12 G_12 = true := by decide +kernel
lemma sl_42_5 : Slice R_42 G_42 (subcubeFast 0 2) 6 := slice_fast_direct sl_42_5_ok low_12
lemma sl_42_6_ok : sliceDirectCheck 2 0 0 R_42 G_42 R_11 G_11 = true := by decide +kernel
lemma sl_42_6 : Slice R_42 G_42 (subcubeFast 2 0) 5 := slice_fast_direct sl_42_6_ok low_11
lemma sl_42_7_ok : sliceDirectCheck 0 4 0 R_42 G_42 R_37 G_37 = true := by decide +kernel
lemma sl_42_7 : Slice R_42 G_42 (subcubeFast 0 4) 6 := slice_fast_direct sl_42_7_ok low_37
lemma sl_42_8_ok : sliceDirectCheck 0 8 0 R_42 G_42 R_13 G_13 = true := by decide +kernel
lemma sl_42_8 : Slice R_42 G_42 (subcubeFast 0 8) 7 := slice_fast_direct sl_42_8_ok low_13
lemma sl_42_9_ok : sliceDirectCheck 4 8 0 R_42 G_42 R_9 G_9 = true := by decide +kernel
lemma sl_42_9 : Slice R_42 G_42 (subcubeFast 4 8) 4 := slice_fast_direct sl_42_9_ok low_9
set_option maxRecDepth 500000 in
lemma slices_42_ok : btAll (fun o => ∀ p, o = some p → Slice R_42 G_42 p.1 p.2) slices_42 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_42 G_42 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_42_0) (forall_cons (fun _ h => by cases h; exact sl_42_1) (forall_cons (fun _ h => by cases h; exact sl_42_2) (forall_cons (fun _ h => by cases h; exact sl_42_3) (forall_cons (fun _ h => by cases h; exact sl_42_4) (forall_cons (fun _ h => by cases h; exact sl_42_5) (forall_cons (fun _ h => by cases h; exact sl_42_6) (forall_cons (fun _ h => by cases h; exact sl_42_7) (forall_cons (fun _ h => by cases h; exact sl_42_8) (forall_cons (fun _ h => by cases h; exact sl_42_9) (fun _ h => (List.not_mem_nil h).elim)))))))))))
set_option maxRecDepth 500000 in
lemma P_42_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_42 G_42 c) P_42 := buildPoolsBT_sound slices_42_ok
def bk_42_init : BT (List (List Nat)) := BT.empty
lemma bk_42_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_42 (0 - 1) xs.toFinset) bk_42_init := trivial
def nodes_42_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_42_0 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_init 0 nodes_42_0 = true := by decide +kernel
def bk_42_0 : BT (List (List Nat)) := buildBucketsBT W_42 nodes_42_0
set_option maxRecDepth 500000 in
lemma bk_42_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_42 0 xs.toFinset) bk_42_0 :=
  buildBucketsBT_sound (by decide) gp_42 W_42_ok P_42_ok autos_42_ok bk_42_init_ok chk_42_0
def nodes_42_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_42_1 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_0 1 nodes_42_1 = true := by decide +kernel
def bk_42_1 : BT (List (List Nat)) := buildBucketsBT W_42 nodes_42_1
set_option maxRecDepth 500000 in
lemma bk_42_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_42 1 xs.toFinset) bk_42_1 :=
  buildBucketsBT_sound (by decide) gp_42 W_42_ok P_42_ok autos_42_ok bk_42_0_ok chk_42_1
def nodes_42_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_42_2 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_1 2 nodes_42_2 = true := by decide +kernel
def bk_42_2 : BT (List (List Nat)) := buildBucketsBT W_42 nodes_42_2
set_option maxRecDepth 500000 in
lemma bk_42_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_42 2 xs.toFinset) bk_42_2 :=
  buildBucketsBT_sound (by decide) gp_42 W_42_ok P_42_ok autos_42_ok bk_42_1_ok chk_42_2
def nodes_42_3 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_42_3 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_2 3 nodes_42_3 = true := by decide +kernel
def bk_42_3 : BT (List (List Nat)) := buildBucketsBT W_42 nodes_42_3
set_option maxRecDepth 500000 in
lemma bk_42_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_42 3 xs.toFinset) bk_42_3 :=
  buildBucketsBT_sound (by decide) gp_42 W_42_ok P_42_ok autos_42_ok bk_42_2_ok chk_42_3
def nodes_42_4 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_42_4 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_3 4 nodes_42_4 = true := by decide +kernel
def bk_42_4 : BT (List (List Nat)) := buildBucketsBT W_42 nodes_42_4
set_option maxRecDepth 500000 in
lemma bk_42_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_42 4 xs.toFinset) bk_42_4 :=
  buildBucketsBT_sound (by decide) gp_42 W_42_ok P_42_ok autos_42_ok bk_42_3_ok chk_42_4
def nodes_42_5 : List NodeSpec := [([0,1,2,3,7,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_42_5 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_4 5 nodes_42_5 = true := by decide +kernel
def bk_42_5 : BT (List (List Nat)) := buildBucketsBT W_42 nodes_42_5
set_option maxRecDepth 500000 in
lemma bk_42_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_42 5 xs.toFinset) bk_42_5 :=
  buildBucketsBT_sound (by decide) gp_42 W_42_ok P_42_ok autos_42_ok bk_42_4_ok chk_42_5
def nodes_42_6 : List NodeSpec := [([5,0,1,2,6,3,4],[0,1,2,3,4,5,6,7,8],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_42_6 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_5 6 nodes_42_6 = true := by decide +kernel
def bk_42_6 : BT (List (List Nat)) := buildBucketsBT W_42 nodes_42_6
set_option maxRecDepth 500000 in
lemma bk_42_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_42 6 xs.toFinset) bk_42_6 :=
  buildBucketsBT_sound (by decide) gp_42 W_42_ok P_42_ok autos_42_ok bk_42_5_ok chk_42_6
def nodes_42_7 : List NodeSpec := [([5,0,1,2,3,4],[7,9,0,10,11,2,3,4,1,8,12],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_42_7 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_6 7 nodes_42_7 = true := by decide +kernel
def bk_42_7 : BT (List (List Nat)) := buildBucketsBT W_42 nodes_42_7
set_option maxRecDepth 500000 in
lemma bk_42_7_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_42 7 xs.toFinset) bk_42_7 :=
  buildBucketsBT_sound (by decide) gp_42 W_42_ok P_42_ok autos_42_ok bk_42_6_ok chk_42_7
def nodes_42_8 : List NodeSpec := [([0,1,2,3,4],[9,7,10,2,4],[0,1,2,3,4,5])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_42_8 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_7 8 nodes_42_8 = true := by decide +kernel
def bk_42_8 : BT (List (List Nat)) := buildBucketsBT W_42 nodes_42_8
set_option maxRecDepth 500000 in
lemma bk_42_8_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_42 8 xs.toFinset) bk_42_8 :=
  buildBucketsBT_sound (by decide) gp_42 W_42_ok P_42_ok autos_42_ok bk_42_7_ok chk_42_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_42_ok : forestRootCheck R_42 G_42 [(VAR 1,14,12),(VAR 2,14,10),(VAR 3,14,6),(VAR 4,26,10),(VAR 5,42,10)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_42_in : bucketContainsBT bk_42_8 R_42 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_42 : Lower R_42 G_42 9 := lower_of_forestBT root_42_ok bk_42_8_ok root_42_in

end Cofactor12058
def h13R : List Nat := varsOf 47
def h13G : Nat := 0xeaa8eaa8a880a880eaa8eaa8a880a880
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13Bound : Lower h13R h13G 9 := carry_of (swaps := [(0,1),(1,2),(2,3),(3,4),(1,2),(0,1)]) (roots2 := Cofactor12058.R_42) (T2 := Cofactor12058.G_42) (by decide +kernel) Cofactor12058.low_42
def h15R : List Nat := varsOf 38
def h15G : Nat := 0xfcfcfcfcc0c0c0c0fcfcfcfcc0c0c0c0
def h15Pos : List Nat := [34,36,6,6,36,34]
def h15Neg : List Nat := [32,32,2,4,4,2]
def h15Mask : Nat := fullMask 6
def h15Base : List Decor := [(0xcccccccccccccccccccccccccccccccc,45,36),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,30,24),(0xffffffff00000000ffffffff00000000,51,3)]
def h15Steps : List (Nat × Nat × Nat) := []
def h15W : BT Decor := buildWiresBT 2 h15Base h15Steps
def h15AutoList : List (List (Nat × Nat)) := [[]]
def h15Autos : BT (List (Nat × Nat)) := btOfList 1 h15AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Pairs : goodPairs h15G h15Pos h15Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15BaseOk : ∀ x ∈ h15Base, faithful h15Pos h15Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15WOk : btAll (fun x => faithful h15Pos h15Neg x ∧ x.1 < 2^128) h15W := buildWiresBT_faithful h15BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h15G = h15G) h15Autos := btAll_ofList (autos_of (by decide +kernel))
def h15SliceList : List (Option (Nat × Nat)) := []
def h15Slices : BT (Option (Nat × Nat)) := btOfList 1 h15SliceList
def h15Specs : List PoolSpec := []
def h15Pools : BT (Option BoundPool) := buildPoolsBT 1 h15W h15R h15Slices h15Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h15R h15G p.1 p.2) h15Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h15R h15G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h15R h15G c) h15Pools := buildPoolsBT_sound h15SlicesOk
def h15Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h15G (3 - 1) xs.toFinset) h15Empty := trivial
def h15Block3_0 : List NodeSpec := [([0,1,2],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Test3_0 : checkNodesBT h15W h15G h15Mask h15Pools h15Autos h15Empty 3 h15Block3_0 = true := by decide +kernel
def h15Nodes3 : List NodeSpec := h15Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Check3 : checkNodesBT h15W h15G h15Mask h15Pools h15Autos h15Empty 3 h15Nodes3 = true := h15Test3_0
def h15Bucket3 : BT (List (List Nat)) := buildBucketsBT h15W h15Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h15G 3 xs.toFinset) h15Bucket3 := buildBucketsBT_sound (by decide) h15Pairs h15WOk h15PoolsOk h15AutosOk h15EmptyOk h15Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Bound : Lower h15R h15G 4 := lower_of_forestBT (essPairs := [(VAR 1,4,6),(VAR 2,2,6),(VAR 5,2,34)]) (by decide +kernel) h15Bucket3Ok (by decide +kernel)
def h14R : List Nat := varsOf 54
def h14G : Nat := 0xfcfcfcfcf0f0c0c0fcfcfcfcf0f0c0c0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14Bound : Lower h14R h14G 5 := lift_of (z := 16) (o := 0) (essPairs := [(VAR 4,4,20)]) (by decide +kernel) h15Bound
def h17R : List Nat := varsOf 39
def h17G : Nat := 0xa8a8a8a880808080a8a8a8a880808080
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h17Bound : Lower h17R h17G 5 := lift_of (z := 0) (o := 1) (essPairs := [(VAR 0,6,7)]) (by decide +kernel) h15Bound
def h18R : List Nat := varsOf 7
def h18G : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def h18Pos : List Nat := [5,6,3,3,6,5]
def h18Neg : List Nat := [4,4,1,2,2,1]
def h18Mask : Nat := fullMask 6
def h18Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,45,36),(0xcccccccccccccccccccccccccccccccc,30,24),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,51,3)]
def h18Steps : List (Nat × Nat × Nat) := []
def h18W : BT Decor := buildWiresBT 2 h18Base h18Steps
def h18AutoList : List (List (Nat × Nat)) := [[]]
def h18Autos : BT (List (Nat × Nat)) := btOfList 1 h18AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18Pairs : goodPairs h18G h18Pos h18Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18BaseOk : ∀ x ∈ h18Base, faithful h18Pos h18Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18WOk : btAll (fun x => faithful h18Pos h18Neg x ∧ x.1 < 2^128) h18W := buildWiresBT_faithful h18BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h18G = h18G) h18Autos := btAll_ofList (autos_of (by decide +kernel))
def h18SliceList : List (Option (Nat × Nat)) := []
def h18Slices : BT (Option (Nat × Nat)) := btOfList 1 h18SliceList
def h18Specs : List PoolSpec := []
def h18Pools : BT (Option BoundPool) := buildPoolsBT 1 h18W h18R h18Slices h18Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h18R h18G p.1 p.2) h18Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h18R h18G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h18R h18G c) h18Pools := buildPoolsBT_sound h18SlicesOk
def h18Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h18G (3 - 1) xs.toFinset) h18Empty := trivial
def h18Block3_0 : List NodeSpec := [([0,1,2],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18Test3_0 : checkNodesBT h18W h18G h18Mask h18Pools h18Autos h18Empty 3 h18Block3_0 = true := by decide +kernel
def h18Nodes3 : List NodeSpec := h18Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18Check3 : checkNodesBT h18W h18G h18Mask h18Pools h18Autos h18Empty 3 h18Nodes3 = true := h18Test3_0
def h18Bucket3 : BT (List (List Nat)) := buildBucketsBT h18W h18Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h18G 3 xs.toFinset) h18Bucket3 := buildBucketsBT_sound (by decide) h18Pairs h18WOk h18PoolsOk h18AutosOk h18EmptyOk h18Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18Bound : Lower h18R h18G 4 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5)]) (by decide +kernel) h18Bucket3Ok (by decide +kernel)
def h19R : List Nat := varsOf 23
def h19G : Nat := 0xe8e8a8a8e8e8a8a8e8e8a8a8e8e8a8a8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h19Bound : Lower h19R h19G 5 := lift_of (z := 0) (o := 16) (essPairs := [(VAR 4,6,22)]) (by decide +kernel) h18Bound
def h20R : List Nat := varsOf 39
def h20G : Nat := 0xe8e8e8e8e0e0e0e0e8e8e8e8e0e0e0e0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h20Bound : Lower h20R h20G 5 := lift_of (z := 0) (o := 32) (essPairs := [(VAR 5,3,35)]) (by decide +kernel) h18Bound
def h21R : List Nat := varsOf 51
def h21G : Nat := 0xeeeeaaaaeeee8888eeeeaaaaeeee8888
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Bound : Lower h21R h21G 5 := lift_of (z := 32) (o := 0) (essPairs := [(VAR 5,1,33)]) (by decide +kernel) h1Bound
def h22R : List Nat := varsOf 53
def h22G : Nat := 0xfafaaaaaf0f0a0a0fafaaaaaf0f0a0a0
def h22Pos : List Nat := [20,5,5,49,52,20,49,33]
def h22Neg : List Nat := [16,1,4,48,48,4,17,1]
def h22Mask : Nat := fullMask 8
def h22Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,206,194),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,55,36),(0xffff0000ffff0000ffff0000ffff0000,121,89),(0xffffffff00000000ffffffff00000000,216,24)]
def h22Steps : List (Nat × Nat × Nat) := []
def h22W : BT Decor := buildWiresBT 2 h22Base h22Steps
def h22AutoList : List (List (Nat × Nat)) := [[]]
def h22Autos : BT (List (Nat × Nat)) := btOfList 1 h22AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Pairs : goodPairs h22G h22Pos h22Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22BaseOk : ∀ x ∈ h22Base, faithful h22Pos h22Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22WOk : btAll (fun x => faithful h22Pos h22Neg x ∧ x.1 < 2^128) h22W := buildWiresBT_faithful h22BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h22G = h22G) h22Autos := btAll_ofList (autos_of (by decide +kernel))
def h22SliceList : List (Option (Nat × Nat)) := []
def h22Slices : BT (Option (Nat × Nat)) := btOfList 1 h22SliceList
def h22Specs : List PoolSpec := []
def h22Pools : BT (Option BoundPool) := buildPoolsBT 1 h22W h22R h22Slices h22Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h22R h22G p.1 p.2) h22Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h22R h22G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h22R h22G c) h22Pools := buildPoolsBT_sound h22SlicesOk
def h22Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h22G (3 - 1) xs.toFinset) h22Empty := trivial
def h22Block3_0 : List NodeSpec := [([0,1,2,3],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test3_0 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Empty 3 h22Block3_0 = true := by decide +kernel
def h22Nodes3 : List NodeSpec := h22Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Check3 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Empty 3 h22Nodes3 = true := h22Test3_0
def h22Bucket3 : BT (List (List Nat)) := buildBucketsBT h22W h22Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h22G 3 xs.toFinset) h22Bucket3 := buildBucketsBT_sound (by decide) h22Pairs h22WOk h22PoolsOk h22AutosOk h22EmptyOk h22Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Bound : Lower h22R h22G 4 := lower_of_forestBT (essPairs := [(VAR 0,4,5),(VAR 2,1,5),(VAR 4,4,20),(VAR 5,1,33)]) (by decide +kernel) h22Bucket3Ok (by decide +kernel)
def h16R : List Nat := varsOf 55
def h16G : Nat := 0xe8e8a8a8e0e08080e8e8a8a8e0e08080
def h16Pos : List Nat := [21,22,37,22,21,51,35,51,35,22,37,54,21,22,35,7,51,37,21,37,54,7,23,54,7,7,39,7]
def h16Neg : List Nat := [20,20,38,18,5,19,3,49,33,6,5,50,19,19,34,3,50,36,17,33,52,5,19,38,6,4,38,1]
def h16Mask : Nat := fullMask 28
def h16Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf6fd5f5,0x86cb5f0),(0xcccccccccccccccccccccccccccccccc,0xff1ebea,0x5c1fa6c),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffebe1f,0x7b20617),(0xffff0000ffff0000ffff0000ffff0000,0xd53abb,0x5538ab),(0xffffffff00000000ffffffff00000000,0x49b4de4,0x49b4984)]
def h16Steps : List (Nat × Nat × Nat) := [(0,0,1),(2,0,1),(0,0,2),(0,1,2),(1,3,5),(1,4,8),(0,5,7),(3,1,2),(2,1,7),(0,2,3),(2,2,3),(2,2,5),(0,0,4),(2,0,4),(2,0,8),(2,0,12),(1,5,15),(2,2,6),(1,8,18)]
def h16W : BT Decor := buildWiresBT 5 h16Base h16Steps
def h16AutoList : List (List (Nat × Nat)) := [[]]
def h16Autos : BT (List (Nat × Nat)) := btOfList 1 h16AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Pairs : goodPairs h16G h16Pos h16Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16BaseOk : ∀ x ∈ h16Base, faithful h16Pos h16Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16WOk : btAll (fun x => faithful h16Pos h16Neg x ∧ x.1 < 2^128) h16W := buildWiresBT_faithful h16BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h16G = h16G) h16Autos := btAll_ofList (autos_of (by decide +kernel))
def h16SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,5),some (subcubeFast 0 2,4),some (subcubeFast 0 4,5),some (subcubeFast 0 16,5),some (subcubeFast 0 32,5),some (subcubeFast 0 48,4),some (subcubeFast 16 0,5),some (subcubeFast 16 1,4),some (subcubeFast 32 0,5),some (subcubeFast 32 4,4)]
def h16Slices : BT (Option (Nat × Nat)) := btOfList 4 h16SliceList
def h16Specs : List PoolSpec := [(0,[]),(1,[]),(7,[]),(2,[]),(6,[(0,0,1)]),(3,[]),(6,[]),(4,[]),(8,[]),(6,[(2,0,1)]),(9,[]),(8,[(0,0,2)]),(6,[(0,0,2)]),(2,[(0,0,4)]),(6,[(0,0,4)]),(3,[(0,0,4)]),(2,[(2,0,4)]),(6,[(2,0,4)]),(3,[(2,0,4)]),(5,[]),(8,[(0,1,2)]),(8,[(3,1,2)]),(0,[(0,2,3)]),(8,[(0,2,3)]),(4,[(0,2,3)]),(0,[(2,2,3)]),(8,[(2,2,3)]),(4,[(2,2,3)])]
def h16Pools : BT (Option BoundPool) := buildPoolsBT 5 h16W h16R h16Slices h16Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Slice9 : Slice h16R h16G (subcubeFast 32 4) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h1Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Slice8 : Slice h16R h16G (subcubeFast 32 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h2Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Slice7 : Slice h16R h16G (subcubeFast 16 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h15Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Slice6 : Slice h16R h16G (subcubeFast 16 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h17Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Slice5 : Slice h16R h16G (subcubeFast 0 48) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h18Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Slice4 : Slice h16R h16G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h19Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Slice3 : Slice h16R h16G (subcubeFast 0 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h20Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Slice2 : Slice h16R h16G (subcubeFast 0 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h21Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Slice1 : Slice h16R h16G (subcubeFast 0 2) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h22Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Slice0 : Slice h16R h16G (subcubeFast 0 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h14Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h16R h16G p.1 p.2) h16Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h16R h16G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h16Slice0) (forall_cons (fun _ h => by cases h; exact h16Slice1) (forall_cons (fun _ h => by cases h; exact h16Slice2) (forall_cons (fun _ h => by cases h; exact h16Slice3) (forall_cons (fun _ h => by cases h; exact h16Slice4) (forall_cons (fun _ h => by cases h; exact h16Slice5) (forall_cons (fun _ h => by cases h; exact h16Slice6) (forall_cons (fun _ h => by cases h; exact h16Slice7) (forall_cons (fun _ h => by cases h; exact h16Slice8) (forall_cons (fun _ h => by cases h; exact h16Slice9) (fun _ h => (List.not_mem_nil h).elim)))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h16R h16G c) h16Pools := buildPoolsBT_sound h16SlicesOk
def h16Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h16G (4 - 1) xs.toFinset) h16Empty := trivial
def h16Block4_0 : List NodeSpec := [([3,4,5,7,8],[],[0]),([0,1,2,4,21],[],[0]),([0,1,2,3,23],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Test4_0 : checkNodesBT h16W h16G h16Mask h16Pools h16Autos h16Empty 4 h16Block4_0 = true := by decide +kernel
def h16Nodes4 : List NodeSpec := h16Block4_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Check4 : checkNodesBT h16W h16G h16Mask h16Pools h16Autos h16Empty 4 h16Nodes4 = true := h16Test4_0
def h16Bucket4 : BT (List (List Nat)) := buildBucketsBT h16W h16Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h16G 4 xs.toFinset) h16Bucket4 := buildBucketsBT_sound (by decide) h16Pairs h16WOk h16PoolsOk h16AutosOk h16EmptyOk h16Check4
def h16Block5_0 : List NodeSpec := [([1,2,3,4,5,7],[2,3],[0]),([0,2,3,4,5,8],[0],[0]),([0,2,3,4,5,12],[],[0]),([0,1,2,4,5,15],[5],[0]),([0,1,2,3,4,11],[5,6,7,8],[0]),([0,1,2,3,4,16],[5,6],[0]),([0,1,2,4,5,9],[6],[0]),([0,2,3,4,6,8],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Test5_0 : checkNodesBT h16W h16G h16Mask h16Pools h16Autos h16Bucket4 5 h16Block5_0 = true := by decide +kernel
def h16Block5_1 : List NodeSpec := [([0,1,2,4,6,15],[],[0]),([0,1,2,3,4,22],[7,8],[0]),([0,1,3,4,7,8],[0,10],[0]),([0,1,2,3,4,13],[],[0]),([0,1,2,3,8,18],[7],[0]),([0,1,2,3,12,18],[],[0]),([0,1,2,3,4,19],[7,8],[0]),([0,1,2,3,8,10],[8],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Test5_1 : checkNodesBT h16W h16G h16Mask h16Pools h16Autos h16Bucket4 5 h16Block5_1 = true := by decide +kernel
def h16Block5_2 : List NodeSpec := [([0,1,2,3,4,20],[5,6],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Test5_2 : checkNodesBT h16W h16G h16Mask h16Pools h16Autos h16Bucket4 5 h16Block5_2 = true := by decide +kernel
def h16Nodes5 : List NodeSpec := h16Block5_0 ++ h16Block5_1 ++ h16Block5_2
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Check5 : checkNodesBT h16W h16G h16Mask h16Pools h16Autos h16Bucket4 5 h16Nodes5 = true := by
  unfold h16Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨h16Test5_0,h16Test5_1⟩,h16Test5_2⟩
def h16Bucket5 : BT (List (List Nat)) := buildBucketsBT h16W h16Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h16G 5 xs.toFinset) h16Bucket5 := buildBucketsBT_sound (by decide) h16Pairs h16WOk h16PoolsOk h16AutosOk h16Bucket4Ok h16Check5
def h16Block6_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,4,5,6,7,8],[0]),([0,1,2,3,4,6],[0,1,2,3,5,6,7,8,9],[0]),([0,1,2,3,4,7],[0,1,2,3,5,6,7,8,10,11,12],[0]),([0,1,2,3,17],[0,2,8,10,13,14,15],[0]),([0,1,2,3,18],[0,2,7,8,16,17,18,19],[0]),([0,1,2,3,4,8],[0,1,3,5,6,7,8,10,20],[0]),([0,1,2,3,4,12],[0,1,3,5,6,7,8,10,21],[0]),([0,1,2,4,14],[2,3,6,22,23,24],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Test6_0 : checkNodesBT h16W h16G h16Mask h16Pools h16Autos h16Bucket5 6 h16Block6_0 = true := by decide +kernel
def h16Block6_1 : List NodeSpec := [([0,1,2,4,15],[3,5,6,10,19,25,26,27],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Test6_1 : checkNodesBT h16W h16G h16Mask h16Pools h16Autos h16Bucket5 6 h16Block6_1 = true := by decide +kernel
def h16Nodes6 : List NodeSpec := h16Block6_0 ++ h16Block6_1
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Check6 : checkNodesBT h16W h16G h16Mask h16Pools h16Autos h16Bucket5 6 h16Nodes6 = true := by
  unfold h16Nodes6 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h16Test6_0,h16Test6_1⟩
def h16Bucket6 : BT (List (List Nat)) := buildBucketsBT h16W h16Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h16G 6 xs.toFinset) h16Bucket6 := buildBucketsBT_sound (by decide) h16Pairs h16WOk h16PoolsOk h16AutosOk h16Bucket5Ok h16Check6
def h16Block7_0 : List NodeSpec := [([0,1,2,3,4],[0,3,5,6,7,8],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Test7_0 : checkNodesBT h16W h16G h16Mask h16Pools h16Autos h16Bucket6 7 h16Block7_0 = true := by decide +kernel
def h16Nodes7 : List NodeSpec := h16Block7_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Check7 : checkNodesBT h16W h16G h16Mask h16Pools h16Autos h16Bucket6 7 h16Nodes7 = true := h16Test7_0
def h16Bucket7 : BT (List (List Nat)) := buildBucketsBT h16W h16Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h16G 7 xs.toFinset) h16Bucket7 := buildBucketsBT_sound (by decide) h16Pairs h16WOk h16PoolsOk h16AutosOk h16Bucket6Ok h16Check7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Bound : Lower h16R h16G 8 := lower_of_forestBT (essPairs := [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 4,5,21),(VAR 5,3,35)]) (by decide +kernel) h16Bucket7Ok (by decide +kernel)
def h24R : List Nat := varsOf 11
def h24G : Nat := 0xee88ee88ee88ee88ee88ee88ee88ee88
def h24Pos : List Nat := [9,10,3,3,10,9]
def h24Neg : List Nat := [8,8,1,2,2,1]
def h24Mask : Nat := fullMask 6
def h24Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,45,36),(0xcccccccccccccccccccccccccccccccc,30,24),(0xff00ff00ff00ff00ff00ff00ff00ff00,51,3)]
def h24Steps : List (Nat × Nat × Nat) := []
def h24W : BT Decor := buildWiresBT 2 h24Base h24Steps
def h24AutoList : List (List (Nat × Nat)) := [[]]
def h24Autos : BT (List (Nat × Nat)) := btOfList 1 h24AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h24Pairs : goodPairs h24G h24Pos h24Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h24BaseOk : ∀ x ∈ h24Base, faithful h24Pos h24Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h24WOk : btAll (fun x => faithful h24Pos h24Neg x ∧ x.1 < 2^128) h24W := buildWiresBT_faithful h24BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h24AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h24G = h24G) h24Autos := btAll_ofList (autos_of (by decide +kernel))
def h24SliceList : List (Option (Nat × Nat)) := []
def h24Slices : BT (Option (Nat × Nat)) := btOfList 1 h24SliceList
def h24Specs : List PoolSpec := []
def h24Pools : BT (Option BoundPool) := buildPoolsBT 1 h24W h24R h24Slices h24Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h24SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h24R h24G p.1 p.2) h24Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h24R h24G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h24PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h24R h24G c) h24Pools := buildPoolsBT_sound h24SlicesOk
def h24Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h24EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h24G (3 - 1) xs.toFinset) h24Empty := trivial
def h24Block3_0 : List NodeSpec := [([0,1,2],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h24Test3_0 : checkNodesBT h24W h24G h24Mask h24Pools h24Autos h24Empty 3 h24Block3_0 = true := by decide +kernel
def h24Nodes3 : List NodeSpec := h24Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h24Check3 : checkNodesBT h24W h24G h24Mask h24Pools h24Autos h24Empty 3 h24Nodes3 = true := h24Test3_0
def h24Bucket3 : BT (List (List Nat)) := buildBucketsBT h24W h24Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h24Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h24G 3 xs.toFinset) h24Bucket3 := buildBucketsBT_sound (by decide) h24Pairs h24WOk h24PoolsOk h24AutosOk h24EmptyOk h24Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h24Bound : Lower h24R h24G 4 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 3,1,9)]) (by decide +kernel) h24Bucket3Ok (by decide +kernel)
def h23R : List Nat := varsOf 27
def h23G : Nat := 0xee88aa88ee88aa88ee88aa88ee88aa88
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h23Bound : Lower h23R h23G 5 := lift_of (z := 0) (o := 16) (essPairs := [(VAR 4,10,26)]) (by decide +kernel) h24Bound
def h25R : List Nat := varsOf 57
def h25G : Nat := 0xffaaaaaaff00aa00ffaaaaaaff00aa00
def h25Pos : List Nat := [24,9,9,49,56,24,49,33]
def h25Neg : List Nat := [16,1,8,48,48,8,17,1]
def h25Mask : Nat := fullMask 8
def h25Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,206,194),(0xff00ff00ff00ff00ff00ff00ff00ff00,55,36),(0xffff0000ffff0000ffff0000ffff0000,121,89),(0xffffffff00000000ffffffff00000000,216,24)]
def h25Steps : List (Nat × Nat × Nat) := []
def h25W : BT Decor := buildWiresBT 2 h25Base h25Steps
def h25AutoList : List (List (Nat × Nat)) := [[]]
def h25Autos : BT (List (Nat × Nat)) := btOfList 1 h25AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h25Pairs : goodPairs h25G h25Pos h25Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h25BaseOk : ∀ x ∈ h25Base, faithful h25Pos h25Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h25WOk : btAll (fun x => faithful h25Pos h25Neg x ∧ x.1 < 2^128) h25W := buildWiresBT_faithful h25BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h25AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h25G = h25G) h25Autos := btAll_ofList (autos_of (by decide +kernel))
def h25SliceList : List (Option (Nat × Nat)) := []
def h25Slices : BT (Option (Nat × Nat)) := btOfList 1 h25SliceList
def h25Specs : List PoolSpec := []
def h25Pools : BT (Option BoundPool) := buildPoolsBT 1 h25W h25R h25Slices h25Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h25SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h25R h25G p.1 p.2) h25Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h25R h25G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h25PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h25R h25G c) h25Pools := buildPoolsBT_sound h25SlicesOk
def h25Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h25EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h25G (3 - 1) xs.toFinset) h25Empty := trivial
def h25Block3_0 : List NodeSpec := [([0,1,2,3],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h25Test3_0 : checkNodesBT h25W h25G h25Mask h25Pools h25Autos h25Empty 3 h25Block3_0 = true := by decide +kernel
def h25Nodes3 : List NodeSpec := h25Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h25Check3 : checkNodesBT h25W h25G h25Mask h25Pools h25Autos h25Empty 3 h25Nodes3 = true := h25Test3_0
def h25Bucket3 : BT (List (List Nat)) := buildBucketsBT h25W h25Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h25Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h25G 3 xs.toFinset) h25Bucket3 := buildBucketsBT_sound (by decide) h25Pairs h25WOk h25PoolsOk h25AutosOk h25EmptyOk h25Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h25Bound : Lower h25R h25G 4 := lower_of_forestBT (essPairs := [(VAR 0,8,9),(VAR 3,1,9),(VAR 4,8,24),(VAR 5,1,33)]) (by decide +kernel) h25Bucket3Ok (by decide +kernel)
def h27R : List Nat := varsOf 43
def h27G : Nat := 0xaa88aa8888008800aa88aa8888008800
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27Bound : Lower h27R h27G 5 := lift_of (z := 0) (o := 1) (essPairs := [(VAR 0,10,11)]) (by decide +kernel) h10Bound
def h28R : List Nat := varsOf 43
def h28G : Nat := 0xee88ee88cc00cc00ee88ee88cc00cc00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h28Bound : Lower h28R h28G 5 := lift_of (z := 0) (o := 1) (essPairs := [(VAR 0,34,35)]) (by decide +kernel) h10Bound
def h29R : List Nat := varsOf 51
def h29G : Nat := 0xeeeeaaaacccc8888eeeeaaaacccc8888
def h29Pos : List Nat := [18,3,3,49,50,18,49,33]
def h29Neg : List Nat := [16,1,2,48,48,2,17,1]
def h29Mask : Nat := fullMask 8
def h29Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,206,194),(0xcccccccccccccccccccccccccccccccc,55,36),(0xffff0000ffff0000ffff0000ffff0000,121,89),(0xffffffff00000000ffffffff00000000,216,24)]
def h29Steps : List (Nat × Nat × Nat) := []
def h29W : BT Decor := buildWiresBT 2 h29Base h29Steps
def h29AutoList : List (List (Nat × Nat)) := [[]]
def h29Autos : BT (List (Nat × Nat)) := btOfList 1 h29AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Pairs : goodPairs h29G h29Pos h29Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29BaseOk : ∀ x ∈ h29Base, faithful h29Pos h29Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29WOk : btAll (fun x => faithful h29Pos h29Neg x ∧ x.1 < 2^128) h29W := buildWiresBT_faithful h29BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h29G = h29G) h29Autos := btAll_ofList (autos_of (by decide +kernel))
def h29SliceList : List (Option (Nat × Nat)) := []
def h29Slices : BT (Option (Nat × Nat)) := btOfList 1 h29SliceList
def h29Specs : List PoolSpec := []
def h29Pools : BT (Option BoundPool) := buildPoolsBT 1 h29W h29R h29Slices h29Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h29R h29G p.1 p.2) h29Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h29R h29G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h29R h29G c) h29Pools := buildPoolsBT_sound h29SlicesOk
def h29Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h29G (3 - 1) xs.toFinset) h29Empty := trivial
def h29Block3_0 : List NodeSpec := [([0,1,2,3],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Test3_0 : checkNodesBT h29W h29G h29Mask h29Pools h29Autos h29Empty 3 h29Block3_0 = true := by decide +kernel
def h29Nodes3 : List NodeSpec := h29Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Check3 : checkNodesBT h29W h29G h29Mask h29Pools h29Autos h29Empty 3 h29Nodes3 = true := h29Test3_0
def h29Bucket3 : BT (List (List Nat)) := buildBucketsBT h29W h29Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h29G 3 xs.toFinset) h29Bucket3 := buildBucketsBT_sound (by decide) h29Pairs h29WOk h29PoolsOk h29AutosOk h29EmptyOk h29Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Bound : Lower h29R h29G 4 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 4,2,18),(VAR 5,1,33)]) (by decide +kernel) h29Bucket3Ok (by decide +kernel)
def h26R : List Nat := varsOf 59
def h26G : Nat := 0xee88aa88cc008800ee88aa88cc008800
def h26Pos : List Nat := [26,41,11,11,26,35,11,26,51,35,35,41,51,41,57,51,58]
def h26Neg : List Nat := [24,40,9,10,18,34,3,10,50,3,33,33,49,9,49,19,42]
def h26Mask : Nat := fullMask 17
def h26Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff6e,0xfe44),(0xcccccccccccccccccccccccccccccccc,0x197fd,0x183f8),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x168df,0x1208f),(0xffff0000ffff0000ffff0000ffff0000,0x1d191,0xd111),(0xffffffff00000000ffffffff00000000,0x1ff22,0x15d22)]
def h26Steps : List (Nat × Nat × Nat) := [(0,1,2),(2,4,5)]
def h26W : BT Decor := buildWiresBT 3 h26Base h26Steps
def h26AutoList : List (List (Nat × Nat)) := [[]]
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
def h26SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,4),some (subcubeFast 0 2,4),some (subcubeFast 0 8,4),some (subcubeFast 0 16,5),some (subcubeFast 0 32,5),some (subcubeFast 16 0,5),some (subcubeFast 16 1,4)]
def h26Slices : BT (Option (Nat × Nat)) := btOfList 3 h26SliceList
def h26Specs : List PoolSpec := [(6,[]),(0,[]),(1,[]),(2,[]),(5,[]),(3,[]),(4,[])]
def h26Pools : BT (Option BoundPool) := buildPoolsBT 3 h26W h26R h26Slices h26Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Slice6 : Slice h26R h26G (subcubeFast 16 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h10Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Slice5 : Slice h26R h26G (subcubeFast 16 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h27Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Slice4 : Slice h26R h26G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h23Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Slice3 : Slice h26R h26G (subcubeFast 0 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h28Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Slice2 : Slice h26R h26G (subcubeFast 0 8) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h29Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Slice1 : Slice h26R h26G (subcubeFast 0 2) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h25Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Slice0 : Slice h26R h26G (subcubeFast 0 1) 4 := slice_fast_direct (zDead := 16) (by decide +kernel) h10Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h26R h26G p.1 p.2) h26Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h26R h26G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h26Slice0) (forall_cons (fun _ h => by cases h; exact h26Slice1) (forall_cons (fun _ h => by cases h; exact h26Slice2) (forall_cons (fun _ h => by cases h; exact h26Slice3) (forall_cons (fun _ h => by cases h; exact h26Slice4) (forall_cons (fun _ h => by cases h; exact h26Slice5) (forall_cons (fun _ h => by cases h; exact h26Slice6) (fun _ h => (List.not_mem_nil h).elim))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h26R h26G c) h26Pools := buildPoolsBT_sound h26SlicesOk
def h26Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h26G (4 - 1) xs.toFinset) h26Empty := trivial
def h26Block4_0 : List NodeSpec := [([0,1,2,3,6],[],[0])]
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
def h26Block5_0 : List NodeSpec := [([0,1,2,3,4,5],[2,4,5,6],[0])]
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
def h26Block6_0 : List NodeSpec := [([0,1,2,3,4],[0,1,2,3,4,5,6],[0])]
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
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Bound : Lower h26R h26G 7 := lower_of_forestBT (essPairs := [(VAR 0,10,11),(VAR 1,9,11),(VAR 3,3,11),(VAR 4,10,26),(VAR 5,3,35)]) (by decide +kernel) h26Bucket6Ok (by decide +kernel)
def h31R : List Nat := varsOf 13
def h31G : Nat := 0xfaa0faa0faa0faa0faa0faa0faa0faa0
def h31Pos : List Nat := [9,12,5,5,12,9]
def h31Neg : List Nat := [8,8,1,4,4,1]
def h31Mask : Nat := fullMask 6
def h31Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,45,36),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,30,24),(0xff00ff00ff00ff00ff00ff00ff00ff00,51,3)]
def h31Steps : List (Nat × Nat × Nat) := []
def h31W : BT Decor := buildWiresBT 2 h31Base h31Steps
def h31AutoList : List (List (Nat × Nat)) := [[]]
def h31Autos : BT (List (Nat × Nat)) := btOfList 1 h31AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Pairs : goodPairs h31G h31Pos h31Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31BaseOk : ∀ x ∈ h31Base, faithful h31Pos h31Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31WOk : btAll (fun x => faithful h31Pos h31Neg x ∧ x.1 < 2^128) h31W := buildWiresBT_faithful h31BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h31G = h31G) h31Autos := btAll_ofList (autos_of (by decide +kernel))
def h31SliceList : List (Option (Nat × Nat)) := []
def h31Slices : BT (Option (Nat × Nat)) := btOfList 1 h31SliceList
def h31Specs : List PoolSpec := []
def h31Pools : BT (Option BoundPool) := buildPoolsBT 1 h31W h31R h31Slices h31Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h31R h31G p.1 p.2) h31Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h31R h31G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h31R h31G c) h31Pools := buildPoolsBT_sound h31SlicesOk
def h31Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h31G (3 - 1) xs.toFinset) h31Empty := trivial
def h31Block3_0 : List NodeSpec := [([0,1,2],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Test3_0 : checkNodesBT h31W h31G h31Mask h31Pools h31Autos h31Empty 3 h31Block3_0 = true := by decide +kernel
def h31Nodes3 : List NodeSpec := h31Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Check3 : checkNodesBT h31W h31G h31Mask h31Pools h31Autos h31Empty 3 h31Nodes3 = true := h31Test3_0
def h31Bucket3 : BT (List (List Nat)) := buildBucketsBT h31W h31Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h31G 3 xs.toFinset) h31Bucket3 := buildBucketsBT_sound (by decide) h31Pairs h31WOk h31PoolsOk h31AutosOk h31EmptyOk h31Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Bound : Lower h31R h31G 4 := lower_of_forestBT (essPairs := [(VAR 0,4,5),(VAR 2,1,5),(VAR 3,1,9)]) (by decide +kernel) h31Bucket3Ok (by decide +kernel)
def h30R : List Nat := varsOf 29
def h30G : Nat := 0xfaa0aaa0faa0aaa0faa0aaa0faa0aaa0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h30Bound : Lower h30R h30G 5 := lift_of (z := 0) (o := 16) (essPairs := [(VAR 4,12,28)]) (by decide +kernel) h31Bound
def h33R : List Nat := varsOf 37
def h33G : Nat := 0xfafafafaa0a0a0a0fafafafaa0a0a0a0
def h33Pos : List Nat := [33,36,5,5,36,33]
def h33Neg : List Nat := [32,32,1,4,4,1]
def h33Mask : Nat := fullMask 6
def h33Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,45,36),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,30,24),(0xffffffff00000000ffffffff00000000,51,3)]
def h33Steps : List (Nat × Nat × Nat) := []
def h33W : BT Decor := buildWiresBT 2 h33Base h33Steps
def h33AutoList : List (List (Nat × Nat)) := [[]]
def h33Autos : BT (List (Nat × Nat)) := btOfList 1 h33AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Pairs : goodPairs h33G h33Pos h33Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33BaseOk : ∀ x ∈ h33Base, faithful h33Pos h33Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33WOk : btAll (fun x => faithful h33Pos h33Neg x ∧ x.1 < 2^128) h33W := buildWiresBT_faithful h33BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h33G = h33G) h33Autos := btAll_ofList (autos_of (by decide +kernel))
def h33SliceList : List (Option (Nat × Nat)) := []
def h33Slices : BT (Option (Nat × Nat)) := btOfList 1 h33SliceList
def h33Specs : List PoolSpec := []
def h33Pools : BT (Option BoundPool) := buildPoolsBT 1 h33W h33R h33Slices h33Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h33R h33G p.1 p.2) h33Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h33R h33G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h33R h33G c) h33Pools := buildPoolsBT_sound h33SlicesOk
def h33Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h33G (3 - 1) xs.toFinset) h33Empty := trivial
def h33Block3_0 : List NodeSpec := [([0,1,2],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Test3_0 : checkNodesBT h33W h33G h33Mask h33Pools h33Autos h33Empty 3 h33Block3_0 = true := by decide +kernel
def h33Nodes3 : List NodeSpec := h33Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Check3 : checkNodesBT h33W h33G h33Mask h33Pools h33Autos h33Empty 3 h33Nodes3 = true := h33Test3_0
def h33Bucket3 : BT (List (List Nat)) := buildBucketsBT h33W h33Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h33G 3 xs.toFinset) h33Bucket3 := buildBucketsBT_sound (by decide) h33Pairs h33WOk h33PoolsOk h33AutosOk h33EmptyOk h33Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Bound : Lower h33R h33G 4 := lower_of_forestBT (essPairs := [(VAR 0,4,5),(VAR 2,1,5),(VAR 5,1,33)]) (by decide +kernel) h33Bucket3Ok (by decide +kernel)
def h32R : List Nat := varsOf 53
def h32G : Nat := 0xfafaaaaaa0a0a0a0fafaaaaaa0a0a0a0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h32Bound : Lower h32R h32G 5 := lift_of (z := 0) (o := 16) (essPairs := [(VAR 4,36,52)]) (by decide +kernel) h33Bound
def h34R : List Nat := varsOf 57
def h34G : Nat := 0xffaaaaaaaaaaaa00ffaaaaaaaaaaaa00
def h34Pos : List Nat := [17,56,17,33,9,17,56,33,56,9,9,9,17,9,33,25,25,41,41,49,49]
def h34Neg : List Nat := [16,48,24,32,8,1,40,1,24,1,0,24,0,40,0,24,1,40,1,48,1]
def h34Mask : Nat := fullMask 21
def h34Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x1ffebd,0x1502a0),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x7af52,0x2a954),(0xffff0000ffff0000ffff0000ffff0000,0x199167,0x88907),(0xffffffff00000000ffffffff00000000,0x1e41ca,0xa204a)]
def h34Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(3,0,1),(0,0,2),(1,0,2),(2,0,2),(3,0,2),(0,0,3),(1,0,3),(2,0,3),(3,0,3),(0,1,2),(1,1,2),(2,1,2),(3,1,2),(0,1,3),(1,1,3),(2,1,3),(3,1,3),(0,2,3),(1,2,3),(2,2,3),(3,2,3),(1,2,4),(0,1,28),(2,2,4),(1,3,4),(0,1,31),(2,3,4),(0,2,5),(1,1,34),(3,2,5),(0,3,5),(1,1,37),(3,3,5),(2,1,8),(1,3,8),(0,2,41),(2,3,8),(3,1,9),(0,3,9),(1,2,45),(3,3,9),(2,1,12),(2,2,12),(3,1,13),(3,2,13),(1,3,18),(0,1,52),(2,3,18),(1,2,54),(1,3,19),(0,2,56),(2,3,19),(1,1,58),(1,2,22),(0,1,60),(2,2,23),(1,1,62)]
def h34W : BT Decor := buildWiresBT 6 h34Base h34Steps
def h34AutoList : List (List (Nat × Nat)) := [[]]
def h34Autos : BT (List (Nat × Nat)) := btOfList 1 h34AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34Pairs : goodPairs h34G h34Pos h34Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34BaseOk : ∀ x ∈ h34Base, faithful h34Pos h34Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34WOk : btAll (fun x => faithful h34Pos h34Neg x ∧ x.1 < 2^128) h34W := buildWiresBT_faithful h34BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h34G = h34G) h34Autos := btAll_ofList (autos_of (by decide +kernel))
def h34SliceList : List (Option (Nat × Nat)) := []
def h34Slices : BT (Option (Nat × Nat)) := btOfList 1 h34SliceList
def h34Specs : List PoolSpec := []
def h34Pools : BT (Option BoundPool) := buildPoolsBT 1 h34W h34R h34Slices h34Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h34R h34G p.1 p.2) h34Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h34R h34G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h34R h34G c) h34Pools := buildPoolsBT_sound h34SlicesOk
def h34Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h34G (3 - 1) xs.toFinset) h34Empty := trivial
def h34Block3_0 : List NodeSpec := [([0,1,3,28],[],[0]),([0,1,3,30],[],[0]),([0,1,2,31],[],[0]),([0,1,2,33],[],[0]),([0,1,3,34],[],[0]),([0,1,3,36],[],[0]),([0,1,2,37],[],[0]),([0,1,2,39],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34Test3_0 : checkNodesBT h34W h34G h34Mask h34Pools h34Autos h34Empty 3 h34Block3_0 = true := by decide +kernel
def h34Block3_1 : List NodeSpec := [([0,2,3,35],[],[0]),([0,2,3,40],[],[0]),([0,1,2,41],[],[0]),([0,1,2,43],[],[0]),([0,2,3,29],[],[0]),([0,2,3,44],[],[0]),([0,1,2,45],[],[0]),([0,1,2,47],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34Test3_1 : checkNodesBT h34W h34G h34Mask h34Pools h34Autos h34Empty 3 h34Block3_1 = true := by decide +kernel
def h34Block3_2 : List NodeSpec := [([0,2,3,38],[],[0]),([0,2,3,48],[],[0]),([0,1,3,46],[],[0]),([0,1,3,49],[],[0]),([0,2,3,32],[],[0]),([0,2,3,50],[],[0]),([0,1,3,42],[],[0]),([0,1,3,51],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34Test3_2 : checkNodesBT h34W h34G h34Mask h34Pools h34Autos h34Empty 3 h34Block3_2 = true := by decide +kernel
def h34Block3_3 : List NodeSpec := [([0,3,16,17],[],[0]),([0,1,2,52],[],[0]),([0,1,2,54],[],[0]),([0,1,2,56],[],[0]),([0,1,2,58],[],[0]),([0,2,20,21],[],[0]),([0,1,3,60],[],[0]),([0,1,3,57],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34Test3_3 : checkNodesBT h34W h34G h34Mask h34Pools h34Autos h34Empty 3 h34Block3_3 = true := by decide +kernel
def h34Block3_4 : List NodeSpec := [([0,1,3,55],[],[0]),([0,1,3,62],[],[0]),([0,1,24,25],[],[0]),([0,2,3,63],[],[0]),([0,2,3,53],[],[0]),([0,2,3,59],[],[0]),([0,2,3,61],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34Test3_4 : checkNodesBT h34W h34G h34Mask h34Pools h34Autos h34Empty 3 h34Block3_4 = true := by decide +kernel
def h34Nodes3 : List NodeSpec := h34Block3_0 ++ h34Block3_1 ++ h34Block3_2 ++ h34Block3_3 ++ h34Block3_4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34Check3 : checkNodesBT h34W h34G h34Mask h34Pools h34Autos h34Empty 3 h34Nodes3 = true := by
  unfold h34Nodes3 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨h34Test3_0,h34Test3_1⟩,h34Test3_2⟩,h34Test3_3⟩,h34Test3_4⟩
def h34Bucket3 : BT (List (List Nat)) := buildBucketsBT h34W h34Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h34G 3 xs.toFinset) h34Bucket3 := buildBucketsBT_sound (by decide) h34Pairs h34WOk h34PoolsOk h34AutosOk h34EmptyOk h34Check3
def h34Block4_0 : List NodeSpec := [([0,1,2,3,4],[],[0]),([0,1,2,3,5],[],[0]),([0,1,2,3,6],[],[0]),([0,1,2,3,7],[],[0]),([0,1,2,3,8],[],[0]),([0,1,2,3,9],[],[0]),([0,1,2,3,10],[],[0]),([0,1,2,3,11],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34Test4_0 : checkNodesBT h34W h34G h34Mask h34Pools h34Autos h34Bucket3 4 h34Block4_0 = true := by decide +kernel
def h34Block4_1 : List NodeSpec := [([0,1,2,3,12],[],[0]),([0,1,2,3,13],[],[0]),([0,1,2,3,14],[],[0]),([0,1,2,3,15],[],[0]),([0,1,2,3,16],[],[0]),([0,1,2,3,17],[],[0]),([0,1,2,3,18],[],[0]),([0,1,2,3,19],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34Test4_1 : checkNodesBT h34W h34G h34Mask h34Pools h34Autos h34Bucket3 4 h34Block4_1 = true := by decide +kernel
def h34Block4_2 : List NodeSpec := [([0,1,2,3,20],[],[0]),([0,1,2,3,21],[],[0]),([0,1,2,3,22],[],[0]),([0,1,2,3,23],[],[0]),([0,1,2,3,24],[],[0]),([0,1,2,3,25],[],[0]),([0,1,2,3,26],[],[0]),([0,1,2,3,27],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34Test4_2 : checkNodesBT h34W h34G h34Mask h34Pools h34Autos h34Bucket3 4 h34Block4_2 = true := by decide +kernel
def h34Nodes4 : List NodeSpec := h34Block4_0 ++ h34Block4_1 ++ h34Block4_2
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34Check4 : checkNodesBT h34W h34G h34Mask h34Pools h34Autos h34Bucket3 4 h34Nodes4 = true := by
  unfold h34Nodes4 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨h34Test4_0,h34Test4_1⟩,h34Test4_2⟩
def h34Bucket4 : BT (List (List Nat)) := buildBucketsBT h34W h34Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h34G 4 xs.toFinset) h34Bucket4 := buildBucketsBT_sound (by decide) h34Pairs h34WOk h34PoolsOk h34AutosOk h34Bucket3Ok h34Check4
def h34Block5_0 : List NodeSpec := [([0,1,2,3],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34Test5_0 : checkNodesBT h34W h34G h34Mask h34Pools h34Autos h34Bucket4 5 h34Block5_0 = true := by decide +kernel
def h34Nodes5 : List NodeSpec := h34Block5_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34Check5 : checkNodesBT h34W h34G h34Mask h34Pools h34Autos h34Bucket4 5 h34Nodes5 = true := h34Test5_0
def h34Bucket5 : BT (List (List Nat)) := buildBucketsBT h34W h34Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h34G 5 xs.toFinset) h34Bucket5 := buildBucketsBT_sound (by decide) h34Pairs h34WOk h34PoolsOk h34AutosOk h34Bucket4Ok h34Check5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34Bound : Lower h34R h34G 6 := lower_of_forestBT (essPairs := [(VAR 0,8,9),(VAR 3,1,9),(VAR 4,1,17),(VAR 5,1,33)]) (by decide +kernel) h34Bucket5Ok (by decide +kernel)
def h36R : List Nat := varsOf 44
def h36G : Nat := 0xfff0fff0f000f000fff0fff0f000f000
def h36Pos : List Nat := [36,40,12,12,40,36]
def h36Neg : List Nat := [32,32,4,8,8,4]
def h36Mask : Nat := fullMask 6
def h36Base : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,45,36),(0xff00ff00ff00ff00ff00ff00ff00ff00,30,24),(0xffffffff00000000ffffffff00000000,51,3)]
def h36Steps : List (Nat × Nat × Nat) := []
def h36W : BT Decor := buildWiresBT 2 h36Base h36Steps
def h36AutoList : List (List (Nat × Nat)) := [[]]
def h36Autos : BT (List (Nat × Nat)) := btOfList 1 h36AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h36Pairs : goodPairs h36G h36Pos h36Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h36BaseOk : ∀ x ∈ h36Base, faithful h36Pos h36Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h36WOk : btAll (fun x => faithful h36Pos h36Neg x ∧ x.1 < 2^128) h36W := buildWiresBT_faithful h36BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h36AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h36G = h36G) h36Autos := btAll_ofList (autos_of (by decide +kernel))
def h36SliceList : List (Option (Nat × Nat)) := []
def h36Slices : BT (Option (Nat × Nat)) := btOfList 1 h36SliceList
def h36Specs : List PoolSpec := []
def h36Pools : BT (Option BoundPool) := buildPoolsBT 1 h36W h36R h36Slices h36Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h36SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h36R h36G p.1 p.2) h36Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h36R h36G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h36PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h36R h36G c) h36Pools := buildPoolsBT_sound h36SlicesOk
def h36Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h36EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h36G (3 - 1) xs.toFinset) h36Empty := trivial
def h36Block3_0 : List NodeSpec := [([0,1,2],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h36Test3_0 : checkNodesBT h36W h36G h36Mask h36Pools h36Autos h36Empty 3 h36Block3_0 = true := by decide +kernel
def h36Nodes3 : List NodeSpec := h36Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h36Check3 : checkNodesBT h36W h36G h36Mask h36Pools h36Autos h36Empty 3 h36Nodes3 = true := h36Test3_0
def h36Bucket3 : BT (List (List Nat)) := buildBucketsBT h36W h36Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h36Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h36G 3 xs.toFinset) h36Bucket3 := buildBucketsBT_sound (by decide) h36Pairs h36WOk h36PoolsOk h36AutosOk h36EmptyOk h36Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h36Bound : Lower h36R h36G 4 := lower_of_forestBT (essPairs := [(VAR 2,8,12),(VAR 3,4,12),(VAR 5,4,36)]) (by decide +kernel) h36Bucket3Ok (by decide +kernel)
def h35R : List Nat := varsOf 60
def h35G : Nat := 0xfff0fff0f0f0f000fff0fff0f0f0f000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Bound : Lower h35R h35G 5 := lift_of (z := 16) (o := 0) (essPairs := [(VAR 4,4,20)]) (by decide +kernel) h36Bound
def h38R : List Nat := varsOf 45
def h38G : Nat := 0xaaa0aaa0a000a000aaa0aaa0a000a000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38Bound : Lower h38R h38G 5 := lift_of (z := 0) (o := 1) (essPairs := [(VAR 0,12,13)]) (by decide +kernel) h36Bound
def h39R : List Nat := varsOf 45
def h39G : Nat := 0xfaa0faa0a0a0a0a0faa0faa0a0a0a0a0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h39Bound : Lower h39R h39G 5 := lift_of (z := 0) (o := 8) (essPairs := [(VAR 3,33,41)]) (by decide +kernel) h33Bound
def h37R : List Nat := varsOf 61
def h37G : Nat := 0xfaa0aaa0a0a0a000faa0aaa0a0a0a000
def h37Pos : List Nat := [41,60,13,13,21,60,21,37,60,21,60,37,21,41,37,13,41,29,37,13,53,45]
def h37Neg : List Nat := [40,56,9,12,20,52,28,36,44,5,28,5,17,9,33,5,33,25,44,44,49,44]
def h37Mask : Nat := fullMask 22
def h37Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x3ffadd,0x13fa04),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x3edffe,0x2c8ff8),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x2ba52f,0x2e254f),(0xffff0000ffff0000ffff0000ffff0000,0x121772,0x121472),(0xffffffff00000000ffffffff00000000,0x356da3,0x3d41a3)]
def h37Steps : List (Nat × Nat × Nat) := [(0,0,2),(0,0,4),(0,1,5),(2,1,7),(0,2,4),(2,4,7),(0,0,9),(2,0,9),(0,1,9),(2,1,9),(2,4,5),(2,1,11),(2,2,11),(0,1,6),(2,1,18),(2,2,18)]
def h37W : BT Decor := buildWiresBT 5 h37Base h37Steps
def h37AutoList : List (List (Nat × Nat)) := [[]]
def h37Autos : BT (List (Nat × Nat)) := btOfList 1 h37AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Pairs : goodPairs h37G h37Pos h37Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37BaseOk : ∀ x ∈ h37Base, faithful h37Pos h37Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37WOk : btAll (fun x => faithful h37Pos h37Neg x ∧ x.1 < 2^128) h37W := buildWiresBT_faithful h37BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h37G = h37G) h37Autos := btAll_ofList (autos_of (by decide +kernel))
def h37SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,5),some (subcubeFast 0 4,6),some (subcubeFast 0 8,5),some (subcubeFast 0 16,5),some (subcubeFast 0 24,4),some (subcubeFast 0 32,5),some (subcubeFast 0 48,4),some (subcubeFast 16 0,5),some (subcubeFast 16 1,4)]
def h37Slices : BT (Option (Nat × Nat)) := btOfList 4 h37SliceList
def h37Specs : List PoolSpec := [(1,[]),(1,[(0,0,2)]),(0,[]),(2,[]),(3,[]),(7,[]),(5,[]),(7,[(0,0,2)]),(3,[(0,2,4)]),(4,[]),(8,[]),(1,[(0,0,4)]),(7,[(0,0,4)]),(6,[]),(1,[(0,2,4)])]
def h37Pools : BT (Option BoundPool) := buildPoolsBT 4 h37W h37R h37Slices h37Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Slice8 : Slice h37R h37G (subcubeFast 16 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h36Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Slice7 : Slice h37R h37G (subcubeFast 16 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h38Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Slice6 : Slice h37R h37G (subcubeFast 0 48) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h31Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Slice5 : Slice h37R h37G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h30Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Slice4 : Slice h37R h37G (subcubeFast 0 24) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h33Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Slice3 : Slice h37R h37G (subcubeFast 0 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h39Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Slice2 : Slice h37R h37G (subcubeFast 0 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h32Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Slice1 : Slice h37R h37G (subcubeFast 0 4) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h34Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Slice0 : Slice h37R h37G (subcubeFast 0 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h35Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h37R h37G p.1 p.2) h37Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h37R h37G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h37Slice0) (forall_cons (fun _ h => by cases h; exact h37Slice1) (forall_cons (fun _ h => by cases h; exact h37Slice2) (forall_cons (fun _ h => by cases h; exact h37Slice3) (forall_cons (fun _ h => by cases h; exact h37Slice4) (forall_cons (fun _ h => by cases h; exact h37Slice5) (forall_cons (fun _ h => by cases h; exact h37Slice6) (forall_cons (fun _ h => by cases h; exact h37Slice7) (forall_cons (fun _ h => by cases h; exact h37Slice8) (fun _ h => (List.not_mem_nil h).elim))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h37R h37G c) h37Pools := buildPoolsBT_sound h37SlicesOk
def h37Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h37G (4 - 1) xs.toFinset) h37Empty := trivial
def h37Block4_0 : List NodeSpec := [([0,1,2,3,10],[],[0]),([0,2,3,4,16],[],[0]),([0,1,3,4,20],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test4_0 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Empty 4 h37Block4_0 = true := by decide +kernel
def h37Nodes4 : List NodeSpec := h37Block4_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Check4 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Empty 4 h37Nodes4 = true := h37Test4_0
def h37Bucket4 : BT (List (List Nat)) := buildBucketsBT h37W h37Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h37G 4 xs.toFinset) h37Bucket4 := buildBucketsBT_sound (by decide) h37Pairs h37WOk h37PoolsOk h37AutosOk h37EmptyOk h37Check4
def h37Block5_0 : List NodeSpec := [([0,1,2,3,4,7],[4,5,6],[0]),([0,1,2,3,4,8],[4,5],[0]),([0,1,3,4,5,9],[2,6,8],[0]),([0,1,2,3,4,11],[0,4,5],[0]),([0,1,2,3,4,15],[],[0]),([0,1,2,3,4,18],[3,4,5],[0]),([0,1,2,3,4,19],[4,5],[0]),([0,1,2,3,6,9],[2,3,8],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test5_0 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket4 5 h37Block5_0 = true := by decide +kernel
def h37Block5_1 : List NodeSpec := [([0,1,2,3,4,17],[],[0]),([0,1,2,3,4,12],[],[0]),([0,1,2,3,4,13],[],[0]),([0,1,2,3,4,14],[14],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test5_1 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket4 5 h37Block5_1 = true := by decide +kernel
def h37Nodes5 : List NodeSpec := h37Block5_0 ++ h37Block5_1
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Check5 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket4 5 h37Nodes5 = true := by
  unfold h37Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h37Test5_0,h37Test5_1⟩
def h37Bucket5 : BT (List (List Nat)) := buildBucketsBT h37W h37Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h37G 5 xs.toFinset) h37Bucket5 := buildBucketsBT_sound (by decide) h37Pairs h37WOk h37PoolsOk h37AutosOk h37Bucket4Ok h37Check5
def h37Block6_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,4,5,6,7,9,10],[0]),([0,1,2,3,4,6],[0,2,3,4,5,6,10,11,12,13],[0]),([0,1,2,3,4,9],[0,2,3,4,5,6,8,14],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test6_0 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket5 6 h37Block6_0 = true := by decide +kernel
def h37Nodes6 : List NodeSpec := h37Block6_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Check6 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket5 6 h37Nodes6 = true := h37Test6_0
def h37Bucket6 : BT (List (List Nat)) := buildBucketsBT h37W h37Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h37G 6 xs.toFinset) h37Bucket6 := buildBucketsBT_sound (by decide) h37Pairs h37WOk h37PoolsOk h37AutosOk h37Bucket5Ok h37Check6
def h37Block7_0 : List NodeSpec := [([0,1,2,3,4],[0,2,3,4,5,6],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test7_0 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket6 7 h37Block7_0 = true := by decide +kernel
def h37Nodes7 : List NodeSpec := h37Block7_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Check7 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket6 7 h37Nodes7 = true := h37Test7_0
def h37Bucket7 : BT (List (List Nat)) := buildBucketsBT h37W h37Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h37G 7 xs.toFinset) h37Bucket7 := buildBucketsBT_sound (by decide) h37Pairs h37WOk h37PoolsOk h37AutosOk h37Bucket6Ok h37Check7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Bound : Lower h37R h37G 8 := lower_of_forestBT (essPairs := [(VAR 0,12,13),(VAR 2,9,13),(VAR 3,5,13),(VAR 4,5,21),(VAR 5,5,37)]) (by decide +kernel) h37Bucket7Ok (by decide +kernel)
def h40R : List Nat := varsOf 28
def h40G : Nat := 0xfff0f000fff0f000fff0f000fff0f000
def h40Pos : List Nat := [20,24,12,12,24,20]
def h40Neg : List Nat := [16,16,4,8,8,4]
def h40Mask : Nat := fullMask 6
def h40Base : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,45,36),(0xff00ff00ff00ff00ff00ff00ff00ff00,30,24),(0xffff0000ffff0000ffff0000ffff0000,51,3)]
def h40Steps : List (Nat × Nat × Nat) := []
def h40W : BT Decor := buildWiresBT 2 h40Base h40Steps
def h40AutoList : List (List (Nat × Nat)) := [[]]
def h40Autos : BT (List (Nat × Nat)) := btOfList 1 h40AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h40Pairs : goodPairs h40G h40Pos h40Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h40BaseOk : ∀ x ∈ h40Base, faithful h40Pos h40Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h40WOk : btAll (fun x => faithful h40Pos h40Neg x ∧ x.1 < 2^128) h40W := buildWiresBT_faithful h40BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h40AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h40G = h40G) h40Autos := btAll_ofList (autos_of (by decide +kernel))
def h40SliceList : List (Option (Nat × Nat)) := []
def h40Slices : BT (Option (Nat × Nat)) := btOfList 1 h40SliceList
def h40Specs : List PoolSpec := []
def h40Pools : BT (Option BoundPool) := buildPoolsBT 1 h40W h40R h40Slices h40Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h40SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h40R h40G p.1 p.2) h40Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h40R h40G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h40PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h40R h40G c) h40Pools := buildPoolsBT_sound h40SlicesOk
def h40Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h40EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h40G (3 - 1) xs.toFinset) h40Empty := trivial
def h40Block3_0 : List NodeSpec := [([0,1,2],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h40Test3_0 : checkNodesBT h40W h40G h40Mask h40Pools h40Autos h40Empty 3 h40Block3_0 = true := by decide +kernel
def h40Nodes3 : List NodeSpec := h40Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h40Check3 : checkNodesBT h40W h40G h40Mask h40Pools h40Autos h40Empty 3 h40Nodes3 = true := h40Test3_0
def h40Bucket3 : BT (List (List Nat)) := buildBucketsBT h40W h40Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h40Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h40G 3 xs.toFinset) h40Bucket3 := buildBucketsBT_sound (by decide) h40Pairs h40WOk h40PoolsOk h40AutosOk h40EmptyOk h40Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h40Bound : Lower h40R h40G 4 := lower_of_forestBT (essPairs := [(VAR 2,8,12),(VAR 3,4,12),(VAR 4,4,20)]) (by decide +kernel) h40Bucket3Ok (by decide +kernel)
namespace Cofactor12058
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
def h41R : List Nat := varsOf 30
def h41G : Nat := 0xfcc0c000fcc0c000fcc0c000fcc0c000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h41Bound : Lower h41R h41G 7 := carry_of (swaps := [(3,4),(4,5)]) (roots2 := Cofactor12058.R_10) (T2 := Cofactor12058.G_10) (by decide +kernel) Cofactor12058.low_10
def h42R : List Nat := varsOf 50
def h42G : Nat := 0xffffcccccccc0000ffffcccccccc0000
def h42Pos : List Nat := [34,48,18,18,48,34]
def h42Neg : List Nat := [32,32,2,16,16,2]
def h42Mask : Nat := fullMask 6
def h42Base : List Decor := [(0xcccccccccccccccccccccccccccccccc,45,36),(0xffff0000ffff0000ffff0000ffff0000,30,24),(0xffffffff00000000ffffffff00000000,51,3)]
def h42Steps : List (Nat × Nat × Nat) := []
def h42W : BT Decor := buildWiresBT 2 h42Base h42Steps
def h42AutoList : List (List (Nat × Nat)) := [[]]
def h42Autos : BT (List (Nat × Nat)) := btOfList 1 h42AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h42Pairs : goodPairs h42G h42Pos h42Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h42BaseOk : ∀ x ∈ h42Base, faithful h42Pos h42Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h42WOk : btAll (fun x => faithful h42Pos h42Neg x ∧ x.1 < 2^128) h42W := buildWiresBT_faithful h42BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h42AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h42G = h42G) h42Autos := btAll_ofList (autos_of (by decide +kernel))
def h42SliceList : List (Option (Nat × Nat)) := []
def h42Slices : BT (Option (Nat × Nat)) := btOfList 1 h42SliceList
def h42Specs : List PoolSpec := []
def h42Pools : BT (Option BoundPool) := buildPoolsBT 1 h42W h42R h42Slices h42Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h42SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h42R h42G p.1 p.2) h42Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h42R h42G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h42PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h42R h42G c) h42Pools := buildPoolsBT_sound h42SlicesOk
def h42Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h42EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h42G (3 - 1) xs.toFinset) h42Empty := trivial
def h42Block3_0 : List NodeSpec := [([0,1,2],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h42Test3_0 : checkNodesBT h42W h42G h42Mask h42Pools h42Autos h42Empty 3 h42Block3_0 = true := by decide +kernel
def h42Nodes3 : List NodeSpec := h42Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h42Check3 : checkNodesBT h42W h42G h42Mask h42Pools h42Autos h42Empty 3 h42Nodes3 = true := h42Test3_0
def h42Bucket3 : BT (List (List Nat)) := buildBucketsBT h42W h42Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h42Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h42G 3 xs.toFinset) h42Bucket3 := buildBucketsBT_sound (by decide) h42Pairs h42WOk h42PoolsOk h42AutosOk h42EmptyOk h42Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h42Bound : Lower h42R h42G 4 := lower_of_forestBT (essPairs := [(VAR 1,16,18),(VAR 4,2,18),(VAR 5,2,34)]) (by decide +kernel) h42Bucket3Ok (by decide +kernel)
def h43R : List Nat := varsOf 54
def h43G : Nat := 0xfcfcc0c0cccc0000fcfcc0c0cccc0000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Bound : Lower h43R h43G 5 := lift_of (z := 0) (o := 4) (essPairs := [(VAR 2,34,38)]) (by decide +kernel) h42Bound
def h44R : List Nat := varsOf 58
def h44G : Nat := 0xffcccc00cccc0000ffcccc00cccc0000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h44Bound : Lower h44R h44G 5 := lift_of (z := 0) (o := 8) (essPairs := [(VAR 3,34,42)]) (by decide +kernel) h42Bound
def h45R : List Nat := varsOf 60
def h45G : Nat := 0xfff0f000fff00000fff0f000fff00000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45Bound : Lower h45R h45G 5 := lift_of (z := 0) (o := 32) (essPairs := [(VAR 5,12,44)]) (by decide +kernel) h40Bound
def h46R : List Nat := varsOf 62
def h46G : Nat := 0xfcc0c000ccc00000fcc0c000ccc00000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Bound : Lower h46R h46G 8 := lift_of (z := 0) (o := 32) (essPairs := [(VAR 5,14,46)]) (by decide +kernel) h41Bound
def h48R : List Nat := varsOf 22
def h48G : Nat := 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0
def h48Pos : List Nat := [18,20,6,6,20,18]
def h48Neg : List Nat := [16,16,2,4,4,2]
def h48Mask : Nat := fullMask 6
def h48Base : List Decor := [(0xcccccccccccccccccccccccccccccccc,45,36),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,30,24),(0xffff0000ffff0000ffff0000ffff0000,51,3)]
def h48Steps : List (Nat × Nat × Nat) := []
def h48W : BT Decor := buildWiresBT 2 h48Base h48Steps
def h48AutoList : List (List (Nat × Nat)) := [[]]
def h48Autos : BT (List (Nat × Nat)) := btOfList 1 h48AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Pairs : goodPairs h48G h48Pos h48Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48BaseOk : ∀ x ∈ h48Base, faithful h48Pos h48Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48WOk : btAll (fun x => faithful h48Pos h48Neg x ∧ x.1 < 2^128) h48W := buildWiresBT_faithful h48BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h48G = h48G) h48Autos := btAll_ofList (autos_of (by decide +kernel))
def h48SliceList : List (Option (Nat × Nat)) := []
def h48Slices : BT (Option (Nat × Nat)) := btOfList 1 h48SliceList
def h48Specs : List PoolSpec := []
def h48Pools : BT (Option BoundPool) := buildPoolsBT 1 h48W h48R h48Slices h48Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h48R h48G p.1 p.2) h48Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h48R h48G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h48R h48G c) h48Pools := buildPoolsBT_sound h48SlicesOk
def h48Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h48G (3 - 1) xs.toFinset) h48Empty := trivial
def h48Block3_0 : List NodeSpec := [([0,1,2],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Test3_0 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Empty 3 h48Block3_0 = true := by decide +kernel
def h48Nodes3 : List NodeSpec := h48Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Check3 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Empty 3 h48Nodes3 = true := h48Test3_0
def h48Bucket3 : BT (List (List Nat)) := buildBucketsBT h48W h48Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h48G 3 xs.toFinset) h48Bucket3 := buildBucketsBT_sound (by decide) h48Pairs h48WOk h48PoolsOk h48AutosOk h48EmptyOk h48Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Bound : Lower h48R h48G 4 := lower_of_forestBT (essPairs := [(VAR 1,4,6),(VAR 2,2,6),(VAR 4,2,18)]) (by decide +kernel) h48Bucket3Ok (by decide +kernel)
def h47R : List Nat := varsOf 23
def h47G : Nat := 0xfefeeaeafefeeaeafefeeaeafefeeaea
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h47Bound : Lower h47R h47G 5 := lift_of (z := 1) (o := 0) (essPairs := [(VAR 0,0,1)]) (by decide +kernel) h48Bound
def h50R : List Nat := varsOf 26
def h50G : Nat := 0xffcccc00ffcccc00ffcccc00ffcccc00
def h50Pos : List Nat := [18,24,10,10,24,18]
def h50Neg : List Nat := [16,16,2,8,8,2]
def h50Mask : Nat := fullMask 6
def h50Base : List Decor := [(0xcccccccccccccccccccccccccccccccc,45,36),(0xff00ff00ff00ff00ff00ff00ff00ff00,30,24),(0xffff0000ffff0000ffff0000ffff0000,51,3)]
def h50Steps : List (Nat × Nat × Nat) := []
def h50W : BT Decor := buildWiresBT 2 h50Base h50Steps
def h50AutoList : List (List (Nat × Nat)) := [[]]
def h50Autos : BT (List (Nat × Nat)) := btOfList 1 h50AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50Pairs : goodPairs h50G h50Pos h50Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50BaseOk : ∀ x ∈ h50Base, faithful h50Pos h50Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50WOk : btAll (fun x => faithful h50Pos h50Neg x ∧ x.1 < 2^128) h50W := buildWiresBT_faithful h50BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h50G = h50G) h50Autos := btAll_ofList (autos_of (by decide +kernel))
def h50SliceList : List (Option (Nat × Nat)) := []
def h50Slices : BT (Option (Nat × Nat)) := btOfList 1 h50SliceList
def h50Specs : List PoolSpec := []
def h50Pools : BT (Option BoundPool) := buildPoolsBT 1 h50W h50R h50Slices h50Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h50R h50G p.1 p.2) h50Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h50R h50G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h50R h50G c) h50Pools := buildPoolsBT_sound h50SlicesOk
def h50Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h50G (3 - 1) xs.toFinset) h50Empty := trivial
def h50Block3_0 : List NodeSpec := [([0,1,2],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50Test3_0 : checkNodesBT h50W h50G h50Mask h50Pools h50Autos h50Empty 3 h50Block3_0 = true := by decide +kernel
def h50Nodes3 : List NodeSpec := h50Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50Check3 : checkNodesBT h50W h50G h50Mask h50Pools h50Autos h50Empty 3 h50Nodes3 = true := h50Test3_0
def h50Bucket3 : BT (List (List Nat)) := buildBucketsBT h50W h50Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h50G 3 xs.toFinset) h50Bucket3 := buildBucketsBT_sound (by decide) h50Pairs h50WOk h50PoolsOk h50AutosOk h50EmptyOk h50Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50Bound : Lower h50R h50G 4 := lower_of_forestBT (essPairs := [(VAR 1,8,10),(VAR 3,2,10),(VAR 4,2,18)]) (by decide +kernel) h50Bucket3Ok (by decide +kernel)
def h49R : List Nat := varsOf 27
def h49G : Nat := 0xffeeeeaaffeeeeaaffeeeeaaffeeeeaa
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Bound : Lower h49R h49G 5 := lift_of (z := 1) (o := 0) (essPairs := [(VAR 0,0,1)]) (by decide +kernel) h50Bound
def h51R : List Nat := varsOf 29
def h51G : Nat := 0xfffafaaafffafaaafffafaaafffafaaa
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h51Bound : Lower h51R h51G 5 := lift_of (z := 1) (o := 0) (essPairs := [(VAR 0,0,1)]) (by decide +kernel) h40Bound
namespace Cofactor12086
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
def nodes_41_3 : List NodeSpec := [([10,12,3,4],[],[0]),([13,11,3,4],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_41_3 : checkNodesBT W_41 G_41 fmask_41 P_41 autos_41 bk_41_2 3 nodes_41_3 = true := by decide +kernel
def bk_41_3 : BT (List (List Nat)) := buildBucketsBT W_41 nodes_41_3
set_option maxRecDepth 500000 in
lemma bk_41_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 3 xs.toFinset) bk_41_3 :=
  buildBucketsBT_sound (by decide) gp_41 W_41_ok P_41_ok autos_41_ok bk_41_2_ok chk_41_3
def nodes_41_4 : List NodeSpec := [([10,9,2,3,4],[0,1],[0]),([9,2,11,3,4],[],[0]),([9,12,2,3,4],[],[0]),([13,9,2,3,4],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_41_4 : checkNodesBT W_41 G_41 fmask_41 P_41 autos_41 bk_41_3 4 nodes_41_4 = true := by decide +kernel
def bk_41_4 : BT (List (List Nat)) := buildBucketsBT W_41 nodes_41_4
set_option maxRecDepth 500000 in
lemma bk_41_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 4 xs.toFinset) bk_41_4 :=
  buildBucketsBT_sound (by decide) gp_41 W_41_ok P_41_ok autos_41_ok bk_41_3_ok chk_41_4
def nodes_41_5 : List NodeSpec := [([9,2,3,4],[2,0],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_41_5 : checkNodesBT W_41 G_41 fmask_41 P_41 autos_41 bk_41_4 5 nodes_41_5 = true := by decide +kernel
def bk_41_5 : BT (List (List Nat)) := buildBucketsBT W_41 nodes_41_5
set_option maxRecDepth 500000 in
lemma bk_41_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 5 xs.toFinset) bk_41_5 :=
  buildBucketsBT_sound (by decide) gp_41 W_41_ok P_41_ok autos_41_ok bk_41_4_ok chk_41_5
def nodes_41_6 : List NodeSpec := [([5,8,2,3,4],[3,4,2,0],[0]),([7,6,2,3,4],[5,4,2,0],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_41_6 : checkNodesBT W_41 G_41 fmask_41 P_41 autos_41 bk_41_5 6 nodes_41_6 = true := by decide +kernel
def bk_41_6 : BT (List (List Nat)) := buildBucketsBT W_41 nodes_41_6
set_option maxRecDepth 500000 in
lemma bk_41_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 6 xs.toFinset) bk_41_6 :=
  buildBucketsBT_sound (by decide) gp_41 W_41_ok P_41_ok autos_41_ok bk_41_5_ok chk_41_6
def nodes_41_7 : List NodeSpec := [([5,0,1,2,3,4],[5,4,3,6,7,2,8,9,10,11],[0]),([0,1,6,2,3,4],[4,5,2,7,6,9,8,12],[0]),([7,0,1,2,3,4],[5,3,6,7,13,8,9,4,10,0],[0])]
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
def h52R : List Nat := varsOf 31
def h52G : Nat := 0xfee8eaa8fee8eaa8fee8eaa8fee8eaa8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h52Bound : Lower h52R h52G 9 := carry_of (swaps := [(3,4),(4,5),(2,3),(1,2),(0,1)]) (roots2 := Cofactor12086.R_41) (T2 := Cofactor12086.G_41) (by decide +kernel) Cofactor12086.low_41
def h54R : List Nat := varsOf 46
def h54G : Nat := 0xfcc0fcc0ccc0ccc0fcc0fcc0ccc0ccc0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h54Bound : Lower h54R h54G 5 := lift_of (z := 0) (o := 32) (essPairs := [(VAR 5,12,44)]) (by decide +kernel) h4Bound
def h55R : List Nat := varsOf 15
def h55G : Nat := 0xfee8fee8fee8fee8fee8fee8fee8fee8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h55Bound : Lower h55R h55G 7 := carry_of (swaps := [(3,4),(4,5),(0,1),(1,2),(2,3),(3,4)]) (roots2 := Cofactor12058.R_13) (T2 := Cofactor12058.G_13) (by decide +kernel) Cofactor12058.low_13
def h56R : List Nat := varsOf 39
def h56G : Nat := 0xfefefefeececececfefefefeecececec
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h56Bound : Lower h56R h56G 5 := lift_of (z := 2) (o := 0) (essPairs := [(VAR 1,0,2)]) (by decide +kernel) h33Bound
def h57R : List Nat := varsOf 46
def h57G : Nat := 0xfffcfffcfcf0fcf0fffcfffcfcf0fcf0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h57Bound : Lower h57R h57G 5 := lift_of (z := 4) (o := 0) (essPairs := [(VAR 2,0,4)]) (by decide +kernel) h10Bound
def h53R : List Nat := varsOf 47
def h53G : Nat := 0xfee8fee8ece0ece0fee8fee8ece0ece0
def h53Pos : List Nat := [5,6,10,6,41,5,10,11,44,35,35,10,41,38,11,13,44,37,7,41,35,44,13,7,37,10,13,6,6,5,10,42,11,6,35,41,5,7,14,5,5,11,14,38,6,42,35,6,38]
def h53Neg : List Nat := [4,4,9,2,40,1,2,3,12,3,34,8,33,36,9,9,36,33,3,9,33,40,12,4,36,12,1,3,12,3,0,40,1,36,1,1,0,2,12,12,9,2,2,34,0,34,2,34,2]
def h53Mask : Nat := fullMask 49
def h53Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x43bd25ded6b1,0x10d2c1ed2a4),(0xcccccccccccccccccccccccccccccccc,0x1fe67da946ece,0x1ee20280406c8),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x19df23de7a12b,0xc213c12103),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x2649c669d9d4,0x1c09268c914),(0xffffffff00000000ffffffff00000000,0x1680c813b3710,0xa80281333410)]
def h53Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(3,0,1),(0,0,2),(1,0,2),(2,0,2),(3,0,2),(0,0,3),(1,0,3),(2,0,3),(3,0,3),(0,1,2),(1,1,2),(2,1,2),(3,1,2),(0,1,3),(1,1,3),(2,1,3),(3,1,3),(0,2,3),(1,2,3),(2,2,3),(3,2,3),(1,2,5),(0,0,29),(2,0,29),(0,4,6),(3,1,10),(1,2,7),(0,4,10),(1,1,35),(2,1,35),(1,3,35),(2,3,35),(0,3,18),(2,3,18),(0,4,18),(2,4,18),(3,7,18),(1,1,28),(1,7,28),(2,4,8),(1,0,21),(2,0,21),(1,1,9),(1,2,21),(0,0,51),(1,0,51),(2,0,51),(3,0,51),(0,3,50),(1,3,50),(2,3,50),(3,3,50),(2,2,21),(2,4,21),(2,1,9),(1,3,9),(2,3,9),(2,4,9),(1,9,21),(3,2,22),(0,4,22),(1,0,68),(2,0,68),(1,2,68),(2,2,68),(1,9,68),(0,0,73),(3,9,22),(1,2,23),(1,9,23),(2,4,56),(0,4,57),(1,21,35),(0,3,80),(2,10,21),(2,22,35),(2,10,68),(0,10,22),(2,10,23),(3,3,36),(1,12,21),(3,12,22),(1,12,23),(1,1,13),(1,2,91),(3,2,91),(1,2,13),(3,1,94),(3,13,18),(0,4,14),(1,2,15),(1,1,16),(1,0,17),(2,0,17),(1,3,17),(2,3,17),(2,4,17),(1,1,40),(2,4,52),(0,4,53),(3,0,71),(0,4,26),(2,4,27)]
def h53W : BT Decor := buildWiresBT 7 h53Base h53Steps
def h53AutoList : List (List (Nat × Nat)) := [[]]
def h53Autos : BT (List (Nat × Nat)) := btOfList 1 h53AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Pairs : goodPairs h53G h53Pos h53Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53BaseOk : ∀ x ∈ h53Base, faithful h53Pos h53Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53WOk : btAll (fun x => faithful h53Pos h53Neg x ∧ x.1 < 2^128) h53W := buildWiresBT_faithful h53BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h53G = h53G) h53Autos := btAll_ofList (autos_of (by decide +kernel))
def h53SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,5),some (subcubeFast 0 8,5),some (subcubeFast 0 32,7),some (subcubeFast 1 0,5),some (subcubeFast 1 32,4),some (subcubeFast 2 0,5),some (subcubeFast 2 8,4),some (subcubeFast 2 32,4),some (subcubeFast 4 0,5),some (subcubeFast 4 1,4),some (subcubeFast 4 32,4),some (subcubeFast 8 0,5),some (subcubeFast 8 32,4),some (subcubeFast 32 0,4)]
def h53Slices : BT (Option (Nat × Nat)) := btOfList 4 h53SliceList
def h53Specs : List PoolSpec := [(3,[]),(5,[]),(2,[(0,0,1)]),(0,[]),(9,[]),(6,[]),(2,[(0,0,1),(1,2,5)]),(11,[]),(1,[]),(13,[]),(2,[]),(8,[]),(4,[]),(2,[(1,0,1)]),(1,[(2,0,1)]),(3,[(0,4,10)]),(8,[(0,4,10)]),(2,[(2,0,1),(1,0,2)]),(2,[(2,0,1)]),(0,[(1,1,2)]),(2,[(3,0,1)]),(3,[(2,4,8)]),(7,[]),(2,[(0,0,2)]),(0,[(1,1,9)]),(2,[(0,0,2),(1,1,9)]),(1,[(1,2,21)]),(2,[(0,1,3),(1,2,21)]),(2,[(0,1,3)]),(0,[(2,4,9)]),(1,[(2,4,21)]),(2,[(1,1,3)]),(5,[(0,4,22)]),(11,[(0,4,22)]),(2,[(2,1,3)]),(2,[(3,1,3)]),(2,[(0,0,2),(2,1,9)]),(0,[(2,1,9)]),(2,[(0,0,2),(1,3,9)]),(0,[(1,3,9)]),(2,[(0,0,2),(2,3,9)]),(0,[(2,3,9)]),(2,[(1,0,2)]),(2,[(2,0,2)]),(2,[(3,0,2)]),(10,[]),(2,[(0,0,3)]),(2,[(0,0,3),(1,1,13)]),(2,[(0,0,3),(1,2,13)]),(2,[(1,0,3)]),(3,[(0,4,14)]),(11,[(0,4,14)]),(2,[(2,0,3)]),(2,[(3,0,3)]),(12,[]),(2,[(0,1,2)]),(2,[(0,1,2),(1,0,17)]),(2,[(0,1,2),(2,0,17)]),(2,[(0,1,2),(1,3,17)]),(2,[(0,1,2),(2,3,17)]),(2,[(1,1,2)]),(1,[(1,1,2)]),(2,[(2,1,2)]),(2,[(3,1,2)]),(2,[(0,1,3),(1,0,21)]),(2,[(0,1,3),(2,0,21)]),(2,[(0,1,3),(2,2,21)]),(0,[(3,2,3)]),(2,[(1,1,3),(3,2,3)]),(2,[(2,1,3),(1,2,23)]),(2,[(0,2,3)]),(2,[(1,1,2),(0,3,18),(1,1,40)]),(2,[(1,2,3)]),(2,[(2,2,3)]),(11,[(2,4,27)]),(2,[(3,2,3)])]
def h53Pools : BT (Option BoundPool) := buildPoolsBT 7 h53W h53R h53Slices h53Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Slice13 : Slice h53R h53G (subcubeFast 32 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h7Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Slice12 : Slice h53R h53G (subcubeFast 8 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h18Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Slice11 : Slice h53R h53G (subcubeFast 8 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h20Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Slice10 : Slice h53R h53G (subcubeFast 4 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h24Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Slice9 : Slice h53R h53G (subcubeFast 4 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h10Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Slice8 : Slice h53R h53G (subcubeFast 4 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h28Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Slice7 : Slice h53R h53G (subcubeFast 2 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h31Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Slice6 : Slice h53R h53G (subcubeFast 2 8) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h33Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Slice5 : Slice h53R h53G (subcubeFast 2 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h39Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Slice4 : Slice h53R h53G (subcubeFast 1 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h4Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Slice3 : Slice h53R h53G (subcubeFast 1 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h54Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Slice2 : Slice h53R h53G (subcubeFast 0 32) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h55Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Slice1 : Slice h53R h53G (subcubeFast 0 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h56Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Slice0 : Slice h53R h53G (subcubeFast 0 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h57Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h53R h53G p.1 p.2) h53Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h53R h53G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h53Slice0) (forall_cons (fun _ h => by cases h; exact h53Slice1) (forall_cons (fun _ h => by cases h; exact h53Slice2) (forall_cons (fun _ h => by cases h; exact h53Slice3) (forall_cons (fun _ h => by cases h; exact h53Slice4) (forall_cons (fun _ h => by cases h; exact h53Slice5) (forall_cons (fun _ h => by cases h; exact h53Slice6) (forall_cons (fun _ h => by cases h; exact h53Slice7) (forall_cons (fun _ h => by cases h; exact h53Slice8) (forall_cons (fun _ h => by cases h; exact h53Slice9) (forall_cons (fun _ h => by cases h; exact h53Slice10) (forall_cons (fun _ h => by cases h; exact h53Slice11) (forall_cons (fun _ h => by cases h; exact h53Slice12) (forall_cons (fun _ h => by cases h; exact h53Slice13) (fun _ h => (List.not_mem_nil h).elim)))))))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h53R h53G c) h53Pools := buildPoolsBT_sound h53SlicesOk
def h53Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h53G (4 - 1) xs.toFinset) h53Empty := trivial
def h53Block4_0 : List NodeSpec := [([0,3,4,50,51],[],[0]),([0,2,3,50,61],[],[0]),([0,1,3,51,65],[],[0]),([0,3,4,50,67],[],[0]),([0,2,3,50,68],[],[0]),([0,1,2,3,73],[],[0]),([0,2,3,50,78],[],[0]),([0,2,3,50,79],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Test4_0 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Empty 4 h53Block4_0 = true := by decide +kernel
def h53Block4_1 : List NodeSpec := [([0,3,4,33,51],[],[0]),([0,1,3,35,51],[],[0]),([0,1,2,3,80],[],[0]),([0,1,2,3,83],[],[0]),([0,1,2,3,84],[],[0]),([0,1,2,35,81],[],[0]),([0,1,2,35,87],[],[0]),([0,1,3,51,106],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Test4_1 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Empty 4 h53Block4_1 = true := by decide +kernel
def h53Block4_2 : List NodeSpec := [([0,1,3,51,107],[],[0]),([1,2,3,68,74],[],[0]),([1,2,3,68,108],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Test4_2 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Empty 4 h53Block4_2 = true := by decide +kernel
def h53Nodes4 : List NodeSpec := h53Block4_0 ++ h53Block4_1 ++ h53Block4_2
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Check4 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Empty 4 h53Nodes4 = true := by
  unfold h53Nodes4 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨h53Test4_0,h53Test4_1⟩,h53Test4_2⟩
def h53Bucket4 : BT (List (List Nat)) := buildBucketsBT h53W h53Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h53G 4 xs.toFinset) h53Bucket4 := buildBucketsBT_sound (by decide) h53Pairs h53WOk h53PoolsOk h53AutosOk h53EmptyOk h53Check4
def h53Block5_0 : List NodeSpec := [([1,2,3,7,35],[3,15,16],[0]),([0,1,3,4,18,34],[0,10],[0]),([0,1,2,3,4,46],[],[0]),([0,2,3,4,21,50],[0,11,24,25],[0]),([0,1,3,4,9,51],[1,7,26,27],[0]),([0,1,2,3,21,65],[0,9,11,12,29],[0]),([0,1,2,3,9,61],[1,7,9,22,30],[0]),([0,1,2,3,4,66],[0,1,3,9,10],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Test5_0 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket4 5 h53Block5_0 = true := by decide +kernel
def h53Block5_1 : List NodeSpec := [([0,2,3,4,22,50],[0,24,25],[0]),([0,1,3,4,9,67],[8],[0]),([0,1,2,3,22,65],[9,12],[0]),([0,1,2,3,9,68],[8,9,32,33],[0]),([0,1,2,3,4,75],[0,9,10],[0]),([0,2,3,4,23,50],[],[0]),([0,1,2,3,23,65],[],[0]),([0,1,2,3,4,77],[0],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Test5_1 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket4 5 h53Block5_1 = true := by decide +kernel
def h53Block5_2 : List NodeSpec := [([0,2,3,4,24,50],[0],[0]),([0,1,2,3,24,65],[],[0]),([0,2,3,4,50,56],[0,11,24,25],[0]),([0,2,3,4,50,57],[0,24,25],[0]),([0,2,3,4,50,58],[],[0]),([0,2,3,4,50,59],[],[0]),([0,2,3,4,21,33],[3],[0]),([0,1,3,4,10,51],[0,7,26,27],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Test5_2 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket4 5 h53Block5_2 = true := by decide +kernel
def h53Block5_3 : List NodeSpec := [([0,1,2,3,21,35],[3,9,15,16],[0]),([0,1,2,3,10,61],[9,22],[0]),([0,1,2,3,4,82],[0,1,9,10],[0]),([0,1,2,3,22,35],[9],[0]),([0,1,2,3,10,68],[9],[0]),([0,1,2,3,4,85],[9,10],[0]),([0,1,2,3,23,35],[3,15],[0]),([0,1,2,3,4,86],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Test5_3 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket4 5 h53Block5_3 = true := by decide +kernel
def h53Block5_4 : List NodeSpec := [([0,2,3,4,24,33],[3],[0]),([0,1,2,3,24,35],[],[0]),([0,1,2,3,35,36],[],[0]),([0,1,2,3,35,37],[3,42],[0]),([0,1,2,3,35,38],[9],[0]),([0,1,2,3,35,39],[],[0]),([0,1,2,3,4,36],[3,7,8],[0]),([0,1,3,4,11,51],[3],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Test5_4 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket4 5 h53Block5_4 = true := by decide +kernel
def h53Block5_5 : List NodeSpec := [([0,1,2,3,11,61],[],[0]),([0,1,3,4,11,67],[3],[0]),([0,1,2,3,11,68],[],[0]),([0,1,3,4,12,51],[],[0]),([0,1,2,3,12,61],[],[0]),([0,1,2,3,4,88],[0,1],[0]),([0,1,2,3,12,68],[8,33],[0]),([0,1,2,3,4,89],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Test5_5 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket4 5 h53Block5_5 = true := by decide +kernel
def h53Block5_6 : List NodeSpec := [([0,1,2,3,4,90],[],[0]),([0,2,3,4,18,91],[0,7],[0]),([0,1,3,4,18,94],[0],[0]),([0,1,2,3,4,92],[0,3,9,10],[0]),([0,1,2,3,4,96],[],[0]),([0,1,2,3,4,93],[],[0]),([0,1,2,3,4,95],[],[0]),([0,2,3,4,18,45],[7,10],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Test5_6 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket4 5 h53Block5_6 = true := by decide +kernel
def h53Block5_7 : List NodeSpec := [([0,1,3,4,51,52],[1,7,26,27],[0]),([0,1,3,4,51,53],[1,7,26,27],[0]),([0,1,3,4,51,54],[],[0]),([0,1,3,4,51,55],[],[0]),([0,1,2,28,68],[8,32,33],[0]),([0,1,2,3,68,69],[9],[0]),([0,1,2,3,68,70],[],[0]),([0,1,2,3,68,71],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Test5_7 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket4 5 h53Block5_7 = true := by decide +kernel
def h53Block5_8 : List NodeSpec := [([0,1,2,3,68,72],[8,31],[0]),([0,1,2,3,4,71],[0,3,8],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Test5_8 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket4 5 h53Block5_8 = true := by decide +kernel
def h53Nodes5 : List NodeSpec := h53Block5_0 ++ h53Block5_1 ++ h53Block5_2 ++ h53Block5_3 ++ h53Block5_4 ++ h53Block5_5 ++ h53Block5_6 ++ h53Block5_7 ++ h53Block5_8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Check5 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket4 5 h53Nodes5 = true := by
  unfold h53Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨h53Test5_0,h53Test5_1⟩,h53Test5_2⟩,h53Test5_3⟩,h53Test5_4⟩,h53Test5_5⟩,h53Test5_6⟩,h53Test5_7⟩,h53Test5_8⟩
def h53Bucket5 : BT (List (List Nat)) := buildBucketsBT h53W h53Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h53G 5 xs.toFinset) h53Bucket5 := buildBucketsBT_sound (by decide) h53Pairs h53WOk h53PoolsOk h53AutosOk h53Bucket4Ok h53Check5
def h53Block6_0 : List NodeSpec := [([0,1,2,3,4,29],[0,1,3,4,5,6,7,8,9,10],[0]),([0,1,2,3,4,32],[0,3,4,7,8,9,10,11,13],[0]),([1,2,3,4,7,10],[0,1,3,11,12,14,17],[0]),([0,1,2,3,4,7,18],[0,3,11,19],[0]),([0,1,2,3,4,7,28],[0,3,4,7,8],[0]),([0,1,2,3,4,34],[0,1,3,4,7,8,9,10],[0]),([0,1,2,3,47],[1,3,4,5,9,20,21],[0]),([0,1,2,3,4,9,21],[0,1,3,7,8,11,23,28],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Test6_0 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket5 6 h53Block6_0 = true := by decide +kernel
def h53Block6_1 : List NodeSpec := [([0,1,2,3,4,9,22],[0,1,3,7,8,11,23,31],[0]),([0,1,2,3,4,9,23],[0,1,7,8,34],[0]),([0,1,2,3,4,9,24],[0,1,5,7,8,35],[0]),([0,2,3,4,50],[0,11,24,25],[0]),([0,1,2,3,4,50],[0,1,3,7,8,9,10,11,25],[0]),([0,2,3,4,62],[0,1,11,36,37],[0]),([0,1,2,4,63],[0,8,11,38,39],[0]),([0,1,2,4,64],[0,7,11,40,41],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Test6_1 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket5 6 h53Block6_1 = true := by decide +kernel
def h53Block6_2 : List NodeSpec := [([0,1,2,3,65],[0,9,11,12,23,29],[0]),([0,1,2,3,4,10,21],[0,1,3,7,8,11,28,42],[0]),([0,1,2,3,4,10,22],[3,8,31,42],[0]),([0,1,2,3,4,10,23],[0,1,3,7,8,34],[0]),([0,1,2,3,4,10,24],[1,3,5,7,35],[0]),([0,1,2,3,4,33],[0,1,3,4,7,8,9,10],[0]),([0,1,2,3,35],[3,4,9,15,16,42],[0]),([0,1,2,3,4,35],[0,1,3,7,8,9,10,42],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Test6_2 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket5 6 h53Block6_2 = true := by decide +kernel
def h53Block6_3 : List NodeSpec := [([0,1,2,3,4,11,21],[0,1,3,4,11,43],[0]),([0,1,2,3,4,11,22],[0,4,8,11,43],[0]),([0,1,2,3,4,11,23],[0,1,3,4],[0]),([0,1,2,3,4,11,24],[0,4,7],[0]),([0,1,2,3,4,12,21],[0,1,3,11,44],[0]),([0,1,2,3,4,12,22],[0,3,7,8,44],[0]),([0,1,2,3,4,12,23],[1,3],[0]),([0,1,2,3,4,12,24],[3,5,7,8],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Test6_3 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket5 6 h53Block6_3 = true := by decide +kernel
def h53Block6_4 : List NodeSpec := [([0,1,2,3,4,44],[0,1,3,7,8,9,10,11,45],[0]),([0,1,2,3,4,13,18],[0,1,3,7,8,11],[0]),([0,1,2,3,4,91],[0,1,3,5,7,9,10,11,47],[0]),([0,1,2,3,4,94],[0,1,3,4,7,9,10,11,48],[0]),([0,1,2,3,97],[3,4,5,8,9,49,50,51],[0]),([0,1,2,3,4,97],[0,1,3,4,5,9,10,11,49],[0]),([0,1,2,3,4,98],[0,1,3,4,5,8,9,10,11],[0]),([0,1,2,3,4,99],[0,1,3,4,7,9,10,11],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Test6_4 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket5 6 h53Block6_4 = true := by decide +kernel
def h53Block6_5 : List NodeSpec := [([1,2,3,4,100],[1,3,11,56],[0]),([1,2,3,4,101],[0,1,11,57],[0]),([0,1,2,4,102],[1,8,11,58],[0]),([0,1,2,4,103],[1,7,11,59],[0]),([0,1,2,3,104],[1,4,5,9,11,55],[0]),([0,1,2,3,4,18,30],[0,3,4,11,19],[0]),([0,1,2,3,4,18,31],[0,3,4],[0]),([0,1,2,3,4,18,28],[1,7,8,61],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Test6_5 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket5 6 h53Block6_5 = true := by decide +kernel
def h53Block6_6 : List NodeSpec := [([0,1,2,3,4,18,40],[1,5,7,8,11],[0]),([0,1,2,3,4,18,41],[5,7,8],[0]),([0,1,2,3,4,42],[0,1,3,7,8,9,10,11,60],[0]),([0,1,2,3,4,43],[0,3,7,8,9,22,60],[0]),([0,1,2,3,4,18],[0,1,3,7,8,9,10,60],[0]),([1,2,3,4,48],[1,3,7,64],[0]),([1,2,3,4,49],[0,1,7,65],[0]),([0,1,3,4,51],[1,7,27],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Test6_6 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket5 6 h53Block6_6 = true := by decide +kernel
def h53Block6_7 : List NodeSpec := [([0,1,2,3,4,51],[0,1,3,7,9,10,11,27],[0]),([0,1,3,4,60],[1,7,11,66],[0]),([0,1,2,3,61],[1,7,9,22,28],[0]),([0,1,2,4,22,28],[1,7,8,11,54,67,68],[0]),([0,1,2,3,4,67],[0,1,3,5,7,8,9,10,11],[0]),([0,1,2,3,68],[5,8,9,31,32,33],[0]),([0,1,2,3,4,68],[0,1,3,7,8,9,10,11,31],[0]),([0,1,2,3,4,76],[0,1,3,8,9,10,11,69],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Test6_7 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket5 6 h53Block6_7 = true := by decide +kernel
def h53Block6_8 : List NodeSpec := [([0,1,2,3,4,105],[0,1,3,4,7,9,10,11,71],[0]),([0,1,2,3,4,109],[0,1,3,5,7,8,9,10,11,72],[0]),([0,1,2,3,110],[4,5,8,9,11,73,74],[0]),([0,1,2,3,4,45],[0,1,3,5,7,8,9,10,11],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Test6_8 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket5 6 h53Block6_8 = true := by decide +kernel
def h53Nodes6 : List NodeSpec := h53Block6_0 ++ h53Block6_1 ++ h53Block6_2 ++ h53Block6_3 ++ h53Block6_4 ++ h53Block6_5 ++ h53Block6_6 ++ h53Block6_7 ++ h53Block6_8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Check6 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket5 6 h53Nodes6 = true := by
  unfold h53Nodes6 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨h53Test6_0,h53Test6_1⟩,h53Test6_2⟩,h53Test6_3⟩,h53Test6_4⟩,h53Test6_5⟩,h53Test6_6⟩,h53Test6_7⟩,h53Test6_8⟩
def h53Bucket6 : BT (List (List Nat)) := buildBucketsBT h53W h53Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h53G 6 xs.toFinset) h53Bucket6 := buildBucketsBT_sound (by decide) h53Pairs h53WOk h53PoolsOk h53AutosOk h53Bucket5Ok h53Check6
def h53Block7_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,4,5,7,8,10,11,12],[0]),([0,1,2,3,4,6],[0,1,3,4,5,7,8,10,11,13],[0]),([0,1,2,3,4,7],[0,1,3,4,5,7,8,10,11,12,18],[0]),([0,1,2,3,4,8],[0,1,3,4,7,8,10,11,20,22],[0]),([0,1,2,3,4,9],[0,1,3,7,8,10,11,12,23],[0]),([0,1,2,3,4,10],[0,1,3,4,7,8,10,11,42],[0]),([0,1,2,3,4,11],[0,1,3,4,7,8,10,11,43],[0]),([0,1,2,3,4,12],[0,1,3,7,8,10,11,44,45],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Test7_0 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket6 7 h53Block7_0 = true := by decide +kernel
def h53Block7_1 : List NodeSpec := [([0,1,2,3,4,13],[0,1,3,4,5,7,10,11,12,46],[0]),([0,1,2,3,4,14],[0,1,3,4,5,7,8,10,11,49],[0]),([0,1,2,3,4,15],[0,1,3,4,5,7,8,10,11,12,52],[0]),([0,1,2,3,4,16],[0,1,3,4,7,10,11,53,54],[0]),([0,1,2,3,4,17],[0,1,3,4,7,8,10,11,22,55],[0]),([0,1,2,3,4,18],[0,1,3,4,5,7,8,10,11,60],[0]),([0,1,2,3,4,19],[0,1,3,4,5,7,8,10,11,22,62],[0]),([0,1,2,3,4,20],[0,1,3,4,5,7,8,10,11,45,63],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Test7_1 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket6 7 h53Block7_1 = true := by decide +kernel
def h53Block7_2 : List NodeSpec := [([0,1,2,3,4,21],[0,1,3,7,10,11,22,28],[0]),([0,1,2,3,4,22],[0,1,3,5,7,8,10,11,31],[0]),([0,1,2,3,4,23],[0,1,3,7,8,10,11,22,34],[0]),([0,1,2,3,4,24],[0,1,3,5,7,8,10,11,35],[0]),([0,1,2,3,4,25],[0,1,3,4,7,10,11,45,70],[0]),([0,1,2,3,4,26],[0,1,3,4,5,7,8,10,11,72],[0]),([0,1,2,3,4,27],[0,1,3,4,5,7,8,10,11,45,73],[0]),([0,1,2,3,4,28],[0,1,3,4,5,7,8,10,11,54,75],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Test7_2 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket6 7 h53Block7_2 = true := by decide +kernel
def h53Nodes7 : List NodeSpec := h53Block7_0 ++ h53Block7_1 ++ h53Block7_2
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Check7 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket6 7 h53Nodes7 = true := by
  unfold h53Nodes7 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨h53Test7_0,h53Test7_1⟩,h53Test7_2⟩
def h53Bucket7 : BT (List (List Nat)) := buildBucketsBT h53W h53Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h53G 7 xs.toFinset) h53Bucket7 := buildBucketsBT_sound (by decide) h53Pairs h53WOk h53PoolsOk h53AutosOk h53Bucket6Ok h53Check7
def h53Block8_0 : List NodeSpec := [([0,1,2,3,4],[10],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Test8_0 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket7 8 h53Block8_0 = true := by decide +kernel
def h53Nodes8 : List NodeSpec := h53Block8_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Check8 : checkNodesBT h53W h53G h53Mask h53Pools h53Autos h53Bucket7 8 h53Nodes8 = true := h53Test8_0
def h53Bucket8 : BT (List (List Nat)) := buildBucketsBT h53W h53Nodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h53G 8 xs.toFinset) h53Bucket8 := buildBucketsBT_sound (by decide) h53Pairs h53WOk h53PoolsOk h53AutosOk h53Bucket7Ok h53Check8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h53Bound : Lower h53R h53G 9 := lower_of_forestBT (essPairs := [(VAR 0,4,5),(VAR 1,4,6),(VAR 2,1,5),(VAR 3,2,10),(VAR 5,3,35)]) (by decide +kernel) h53Bucket8Ok (by decide +kernel)
def h58R : List Nat := varsOf 51
def h58G : Nat := 0xffffeeeeeeeeaaaaffffeeeeeeeeaaaa
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h58Bound : Lower h58R h58G 5 := lift_of (z := 1) (o := 0) (essPairs := [(VAR 0,0,1)]) (by decide +kernel) h42Bound
def h60R : List Nat := varsOf 39
def h60G : Nat := 0xeaeaeaeaa8a8a8a8eaeaeaeaa8a8a8a8
def h60Pos : List Nat := [5,38,5,33,3,5,38,33,38,3,3,3,5,3,33,7,7,35,35,37,37]
def h60Neg : List Nat := [4,36,6,32,2,1,34,1,6,1,0,6,0,34,0,6,1,34,1,36,1]
def h60Mask : Nat := fullMask 21
def h60Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x1ffebd,0x1502a0),(0xcccccccccccccccccccccccccccccccc,0x7af52,0x2a954),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x199167,0x88907),(0xffffffff00000000ffffffff00000000,0x1e41ca,0xa204a)]
def h60Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(3,0,1),(0,0,2),(1,0,2),(2,0,2),(3,0,2),(0,0,3),(1,0,3),(2,0,3),(3,0,3),(0,1,2),(1,1,2),(2,1,2),(3,1,2),(0,1,3),(1,1,3),(2,1,3),(3,1,3),(0,2,3),(1,2,3),(2,2,3),(3,2,3),(1,2,4),(0,1,28),(2,2,4),(1,3,4),(0,1,31),(2,3,4),(0,2,5),(1,1,34),(3,2,5),(0,3,5),(1,1,37),(3,3,5),(2,1,8),(1,3,8),(0,2,41),(2,3,8),(3,1,9),(0,3,9),(1,2,45),(3,3,9),(2,1,12),(2,2,12),(3,1,13),(3,2,13),(1,3,18),(0,1,52),(2,3,18),(1,2,54),(1,3,19),(0,2,56),(2,3,19),(1,1,58),(1,2,22),(0,1,60),(2,2,23),(1,1,62)]
def h60W : BT Decor := buildWiresBT 6 h60Base h60Steps
def h60AutoList : List (List (Nat × Nat)) := [[]]
def h60Autos : BT (List (Nat × Nat)) := btOfList 1 h60AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h60Pairs : goodPairs h60G h60Pos h60Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h60BaseOk : ∀ x ∈ h60Base, faithful h60Pos h60Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h60WOk : btAll (fun x => faithful h60Pos h60Neg x ∧ x.1 < 2^128) h60W := buildWiresBT_faithful h60BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h60AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h60G = h60G) h60Autos := btAll_ofList (autos_of (by decide +kernel))
def h60SliceList : List (Option (Nat × Nat)) := []
def h60Slices : BT (Option (Nat × Nat)) := btOfList 1 h60SliceList
def h60Specs : List PoolSpec := []
def h60Pools : BT (Option BoundPool) := buildPoolsBT 1 h60W h60R h60Slices h60Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h60SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h60R h60G p.1 p.2) h60Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h60R h60G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h60PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h60R h60G c) h60Pools := buildPoolsBT_sound h60SlicesOk
def h60Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h60EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h60G (3 - 1) xs.toFinset) h60Empty := trivial
def h60Block3_0 : List NodeSpec := [([0,1,3,28],[],[0]),([0,1,3,30],[],[0]),([0,1,2,31],[],[0]),([0,1,2,33],[],[0]),([0,1,3,34],[],[0]),([0,1,3,36],[],[0]),([0,1,2,37],[],[0]),([0,1,2,39],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h60Test3_0 : checkNodesBT h60W h60G h60Mask h60Pools h60Autos h60Empty 3 h60Block3_0 = true := by decide +kernel
def h60Block3_1 : List NodeSpec := [([0,2,3,35],[],[0]),([0,2,3,40],[],[0]),([0,1,2,41],[],[0]),([0,1,2,43],[],[0]),([0,2,3,29],[],[0]),([0,2,3,44],[],[0]),([0,1,2,45],[],[0]),([0,1,2,47],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h60Test3_1 : checkNodesBT h60W h60G h60Mask h60Pools h60Autos h60Empty 3 h60Block3_1 = true := by decide +kernel
def h60Block3_2 : List NodeSpec := [([0,2,3,38],[],[0]),([0,2,3,48],[],[0]),([0,1,3,46],[],[0]),([0,1,3,49],[],[0]),([0,2,3,32],[],[0]),([0,2,3,50],[],[0]),([0,1,3,42],[],[0]),([0,1,3,51],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h60Test3_2 : checkNodesBT h60W h60G h60Mask h60Pools h60Autos h60Empty 3 h60Block3_2 = true := by decide +kernel
def h60Block3_3 : List NodeSpec := [([0,3,16,17],[],[0]),([0,1,2,52],[],[0]),([0,1,2,54],[],[0]),([0,1,2,56],[],[0]),([0,1,2,58],[],[0]),([0,2,20,21],[],[0]),([0,1,3,60],[],[0]),([0,1,3,57],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h60Test3_3 : checkNodesBT h60W h60G h60Mask h60Pools h60Autos h60Empty 3 h60Block3_3 = true := by decide +kernel
def h60Block3_4 : List NodeSpec := [([0,1,3,55],[],[0]),([0,1,3,62],[],[0]),([0,1,24,25],[],[0]),([0,2,3,63],[],[0]),([0,2,3,53],[],[0]),([0,2,3,59],[],[0]),([0,2,3,61],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h60Test3_4 : checkNodesBT h60W h60G h60Mask h60Pools h60Autos h60Empty 3 h60Block3_4 = true := by decide +kernel
def h60Nodes3 : List NodeSpec := h60Block3_0 ++ h60Block3_1 ++ h60Block3_2 ++ h60Block3_3 ++ h60Block3_4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h60Check3 : checkNodesBT h60W h60G h60Mask h60Pools h60Autos h60Empty 3 h60Nodes3 = true := by
  unfold h60Nodes3 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨h60Test3_0,h60Test3_1⟩,h60Test3_2⟩,h60Test3_3⟩,h60Test3_4⟩
def h60Bucket3 : BT (List (List Nat)) := buildBucketsBT h60W h60Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h60Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h60G 3 xs.toFinset) h60Bucket3 := buildBucketsBT_sound (by decide) h60Pairs h60WOk h60PoolsOk h60AutosOk h60EmptyOk h60Check3
def h60Block4_0 : List NodeSpec := [([0,1,2,3,4],[],[0]),([0,1,2,3,5],[],[0]),([0,1,2,3,6],[],[0]),([0,1,2,3,7],[],[0]),([0,1,2,3,8],[],[0]),([0,1,2,3,9],[],[0]),([0,1,2,3,10],[],[0]),([0,1,2,3,11],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h60Test4_0 : checkNodesBT h60W h60G h60Mask h60Pools h60Autos h60Bucket3 4 h60Block4_0 = true := by decide +kernel
def h60Block4_1 : List NodeSpec := [([0,1,2,3,12],[],[0]),([0,1,2,3,13],[],[0]),([0,1,2,3,14],[],[0]),([0,1,2,3,15],[],[0]),([0,1,2,3,16],[],[0]),([0,1,2,3,17],[],[0]),([0,1,2,3,18],[],[0]),([0,1,2,3,19],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h60Test4_1 : checkNodesBT h60W h60G h60Mask h60Pools h60Autos h60Bucket3 4 h60Block4_1 = true := by decide +kernel
def h60Block4_2 : List NodeSpec := [([0,1,2,3,20],[],[0]),([0,1,2,3,21],[],[0]),([0,1,2,3,22],[],[0]),([0,1,2,3,23],[],[0]),([0,1,2,3,24],[],[0]),([0,1,2,3,25],[],[0]),([0,1,2,3,26],[],[0]),([0,1,2,3,27],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h60Test4_2 : checkNodesBT h60W h60G h60Mask h60Pools h60Autos h60Bucket3 4 h60Block4_2 = true := by decide +kernel
def h60Nodes4 : List NodeSpec := h60Block4_0 ++ h60Block4_1 ++ h60Block4_2
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h60Check4 : checkNodesBT h60W h60G h60Mask h60Pools h60Autos h60Bucket3 4 h60Nodes4 = true := by
  unfold h60Nodes4 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨h60Test4_0,h60Test4_1⟩,h60Test4_2⟩
def h60Bucket4 : BT (List (List Nat)) := buildBucketsBT h60W h60Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h60Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h60G 4 xs.toFinset) h60Bucket4 := buildBucketsBT_sound (by decide) h60Pairs h60WOk h60PoolsOk h60AutosOk h60Bucket3Ok h60Check4
def h60Block5_0 : List NodeSpec := [([0,1,2,3],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h60Test5_0 : checkNodesBT h60W h60G h60Mask h60Pools h60Autos h60Bucket4 5 h60Block5_0 = true := by decide +kernel
def h60Nodes5 : List NodeSpec := h60Block5_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h60Check5 : checkNodesBT h60W h60G h60Mask h60Pools h60Autos h60Bucket4 5 h60Nodes5 = true := h60Test5_0
def h60Bucket5 : BT (List (List Nat)) := buildBucketsBT h60W h60Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h60Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h60G 5 xs.toFinset) h60Bucket5 := buildBucketsBT_sound (by decide) h60Pairs h60WOk h60PoolsOk h60AutosOk h60Bucket4Ok h60Check5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h60Bound : Lower h60R h60G 6 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 5,1,33)]) (by decide +kernel) h60Bucket5Ok (by decide +kernel)
def h59R : List Nat := varsOf 55
def h59G : Nat := 0xfefeeaeaececa8a8fefeeaeaececa8a8
def h59Pos : List Nat := [5,18,5,33,38,5,18,21,38,33,3,22,38,52,3,21,7,49,19,35,49,52,52,21,49,18,33,7,5,35,37,18,50,22,18,50,3,22,38,3,18,38,3,19,49,33,18,18,5,19,3,21,5,37,38,38,52]
def h59Neg : List Nat := [4,16,6,32,34,1,2,20,6,1,2,20,36,36,1,17,6,17,17,34,48,20,48,16,16,17,36,1,36,1,36,20,48,6,48,34,0,16,4,17,0,32,34,1,1,17,6,34,20,2,6,1,17,1,0,2,16]
def h59Mask : Nat := fullMask 57
def h59Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x3f3c907d9fc6ad,0x3838802a06c220),(0xcccccccccccccccccccccccccccccccc,0xc6cfffaa0d5d52,0x86c40a00090554),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x1f9026258e1b9b5,0x54042d4213985),(0xffff0000ffff0000ffff0000ffff0000,0x10ad92f83f6a8c2,0x11120a583f68882),(0xffffffff00000000ffffffff00000000,0x1e03249657a3318,0x860d54583018)]
def h59Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(3,0,1),(0,0,2),(1,0,2),(2,0,2),(3,0,2),(1,0,3),(2,0,3),(3,0,3),(0,0,4),(1,0,4),(2,0,4),(3,0,4),(0,1,2),(1,1,2),(2,1,2),(3,1,2),(0,1,3),(1,1,3),(2,1,3),(3,1,3),(0,1,4),(1,1,4),(2,1,4),(3,1,4),(1,2,3),(2,2,3),(0,2,4),(1,2,4),(2,2,4),(3,2,4),(1,2,5),(1,3,4),(3,3,4),(2,2,5),(1,3,5),(1,4,5),(2,4,5),(1,1,34),(0,2,6),(2,2,6),(0,2,13),(0,2,45),(0,4,6),(2,4,6),(0,4,13),(0,4,45),(0,6,13),(1,6,45),(0,13,45),(2,1,34),(3,1,34),(3,1,55),(0,13,55),(2,6,34),(0,13,34),(2,13,34),(1,1,46),(1,1,50),(2,6,15),(1,0,23),(3,1,67),(0,2,67),(1,4,23),(2,4,23),(2,6,23),(1,0,31),(3,1,73),(0,4,73),(1,2,31),(2,2,31),(2,6,31),(1,0,34),(0,2,79),(0,4,79),(3,0,34),(3,0,45),(0,3,45),(3,3,45),(1,3,34),(1,0,46),(1,0,50),(1,3,7),(1,8,15),(1,8,34),(2,1,69),(2,1,75),(0,2,25),(0,3,64),(1,3,64),(2,3,64),(3,3,64),(0,4,25),(1,3,9),(1,4,9),(2,4,9),(3,9,25),(2,2,26),(2,4,26),(1,9,26),(2,4,95),(2,2,24),(2,4,24),(1,1,81),(1,3,81),(2,3,81),(0,3,110),(3,3,110),(3,81,110),(3,4,10),(2,10,23),(1,2,81),(0,10,25),(1,0,119),(1,0,104),(2,10,26),(2,2,28),(1,0,123),(2,10,28),(1,0,77),(1,1,77),(2,4,77),(2,10,31),(1,0,40),(2,2,40),(1,0,131),(2,10,40),(1,24,81),(2,2,115),(0,2,111),(1,3,11),(3,11,25),(1,11,26),(1,1,82),(1,0,58),(1,0,71),(1,1,71),(1,31,34),(2,4,48),(2,2,52),(1,1,56),(1,3,52),(1,0,128),(1,15,20),(2,2,150),(1,15,23),(1,15,34),(3,15,34),(2,4,151),(1,15,28),(2,4,156),(1,15,31),(2,2,157),(3,15,45),(0,3,65),(1,3,65),(2,3,65),(3,3,65),(2,2,16),(3,16,25),(1,16,26),(2,2,161),(3,24,118),(3,2,17),(2,17,20),(2,17,23),(1,1,80),(2,1,80),(1,3,80),(2,3,80),(0,17,25),(1,0,177),(1,0,105),(2,17,26),(0,3,173),(3,3,173),(2,17,31),(1,0,33),(2,4,33),(1,0,185),(2,17,33),(1,24,80),(0,4,175),(1,3,18),(3,18,25),(1,18,26),(3,3,21),(3,3,29),(2,21,34),(2,29,34),(1,4,22),(1,23,31),(1,23,37),(2,25,34),(0,25,35),(3,34,35),(2,25,36),(2,25,37),(1,26,34),(3,26,35),(1,26,36),(1,26,37),(1,2,30),(1,31,36),(1,34,198),(3,34,198),(1,1,212)]
def h59W : BT Decor := buildWiresBT 8 h59Base h59Steps
def h59AutoList : List (List (Nat × Nat)) := [[]]
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
def h59SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 4,5),some (subcubeFast 0 16,5),some (subcubeFast 0 32,5),some (subcubeFast 1 0,5),some (subcubeFast 1 4,4),some (subcubeFast 1 32,4),some (subcubeFast 2 0,5),some (subcubeFast 2 16,4),some (subcubeFast 4 0,4),some (subcubeFast 16 0,6),some (subcubeFast 32 0,4)]
def h59Slices : BT (Option (Nat × Nat)) := btOfList 4 h59SliceList
def h59Specs : List PoolSpec := [(3,[]),(6,[]),(9,[(0,0,1)]),(4,[]),(9,[(0,0,1),(1,2,5)]),(5,[]),(0,[]),(9,[(0,0,1),(2,2,5)]),(8,[]),(9,[]),(1,[]),(9,[(0,0,1),(1,4,5)]),(2,[]),(9,[(0,0,1),(2,4,5)]),(10,[]),(9,[(1,0,1)]),(6,[(1,0,3)]),(7,[]),(1,[(1,0,1)]),(0,[(1,0,3)]),(2,[(1,0,3)]),(6,[(3,0,3)]),(0,[(3,0,3)]),(2,[(3,0,3)]),(0,[(1,0,1)]),(2,[(1,0,1)]),(9,[(1,0,1),(0,2,6)]),(9,[(1,0,1),(0,4,6)]),(9,[(2,0,1)]),(1,[(2,0,1)]),(6,[(1,3,7)]),(9,[(3,0,1)]),(0,[(1,0,23)]),(2,[(1,0,31)]),(9,[(0,0,2)]),(0,[(1,4,9)]),(0,[(1,3,9)]),(9,[(0,0,2),(1,4,9)]),(9,[(0,0,2),(2,4,9)]),(0,[(2,4,9)]),(9,[(1,0,2)]),(1,[(3,1,2)]),(3,[(0,2,4)]),(2,[(1,0,34)]),(2,[(1,0,2)]),(3,[(3,4,10)]),(9,[(1,0,2),(3,4,10)]),(9,[(2,0,2)]),(9,[(3,0,2)]),(2,[(3,0,2)]),(0,[(3,0,34)]),(2,[(3,0,34)]),(9,[(3,1,2)]),(2,[(1,0,3),(1,0,34)]),(9,[(3,1,4)]),(0,[(1,0,3),(1,0,34)]),(1,[(3,1,4)]),(9,[(0,2,4)]),(9,[(0,2,13)]),(9,[(0,4,13)]),(9,[(0,1,2)]),(9,[(0,1,4)]),(9,[(0,0,4)]),(9,[(0,0,4),(2,2,16)]),(2,[(2,2,16)]),(9,[(1,0,4)]),(0,[(1,0,34)]),(0,[(1,0,4)]),(3,[(3,2,17)]),(9,[(1,0,4),(3,2,17)]),(9,[(2,0,4)]),(9,[(3,0,4)]),(0,[(3,0,4)]),(9,[(1,1,2)]),(9,[(1,1,4)]),(9,[(3,1,4),(2,2,31)]),(1,[(1,1,2)]),(6,[(3,3,21)]),(9,[(2,1,2)]),(9,[(2,1,2),(1,4,22)]),(9,[(3,1,2),(2,4,23)]),(3,[(3,2,4)]),(9,[(0,2,25)]),(6,[(0,2,25)]),(9,[(0,4,25)]),(6,[(0,4,25)]),(9,[(2,2,26)]),(9,[(2,4,26)]),(1,[(1,1,4)]),(6,[(3,3,29)]),(9,[(2,1,4)]),(9,[(2,1,4),(1,2,30)]),(3,[(2,2,4)]),(9,[(1,0,33)]),(0,[(1,0,33)]),(9,[(2,4,33)]),(9,[(0,2,4),(1,2,4)]),(9,[(1,2,4),(0,2,4)]),(9,[(1,2,4)]),(9,[(2,2,4)]),(9,[(3,2,4)]),(9,[(1,0,40)]),(9,[(2,2,40)])]
def h59Pools : BT (Option BoundPool) := buildPoolsBT 7 h59W h59R h59Slices h59Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Slice10 : Slice h59R h59G (subcubeFast 32 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h8Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Slice9 : Slice h59R h59G (subcubeFast 16 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h60Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Slice8 : Slice h59R h59G (subcubeFast 4 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h29Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Slice7 : Slice h59R h59G (subcubeFast 2 16) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h33Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Slice6 : Slice h59R h59G (subcubeFast 2 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h32Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Slice5 : Slice h59R h59G (subcubeFast 1 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h48Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Slice4 : Slice h59R h59G (subcubeFast 1 4) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h42Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Slice3 : Slice h59R h59G (subcubeFast 1 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h43Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Slice2 : Slice h59R h59G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h47Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Slice1 : Slice h59R h59G (subcubeFast 0 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h56Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Slice0 : Slice h59R h59G (subcubeFast 0 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h58Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h59R h59G p.1 p.2) h59Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h59R h59G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h59Slice0) (forall_cons (fun _ h => by cases h; exact h59Slice1) (forall_cons (fun _ h => by cases h; exact h59Slice2) (forall_cons (fun _ h => by cases h; exact h59Slice3) (forall_cons (fun _ h => by cases h; exact h59Slice4) (forall_cons (fun _ h => by cases h; exact h59Slice5) (forall_cons (fun _ h => by cases h; exact h59Slice6) (forall_cons (fun _ h => by cases h; exact h59Slice7) (forall_cons (fun _ h => by cases h; exact h59Slice8) (forall_cons (fun _ h => by cases h; exact h59Slice9) (forall_cons (fun _ h => by cases h; exact h59Slice10) (fun _ h => (List.not_mem_nil h).elim))))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h59R h59G c) h59Pools := buildPoolsBT_sound h59SlicesOk
def h59Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h59G (3 - 1) xs.toFinset) h59Empty := trivial
def h59Block3_0 : List NodeSpec := [([1,2,60,81],[],[0]),([1,4,60,80],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test3_0 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Empty 3 h59Block3_0 = true := by decide +kernel
def h59Nodes3 : List NodeSpec := h59Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Check3 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Empty 3 h59Nodes3 = true := h59Test3_0
def h59Bucket3 : BT (List (List Nat)) := buildBucketsBT h59W h59Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h59G 3 xs.toFinset) h59Bucket3 := buildBucketsBT_sound (by decide) h59Pairs h59WOk h59PoolsOk h59AutosOk h59EmptyOk h59Check3
def h59Block4_0 : List NodeSpec := [([2,4,6,13,45],[],[0]),([1,2,4,13,55],[9],[0]),([1,2,4,13,61],[],[0]),([2,3,4,54,64],[],[0]),([0,2,3,64,107],[],[0]),([0,2,3,64,109],[],[0]),([0,3,23,81,110],[],[0]),([0,3,23,81,115],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test4_0 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket3 4 h59Block4_0 = true := by decide +kernel
def h59Block4_1 : List NodeSpec := [([0,1,3,81,104],[],[0]),([2,3,4,54,68],[],[0]),([1,2,3,54,81],[],[0]),([0,1,3,81,108],[],[0]),([0,1,2,3,134],[],[0]),([0,1,2,81,113],[],[0]),([0,1,2,81,114],[],[0]),([1,4,13,23,79],[53],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test4_1 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket3 4 h59Block4_1 = true := by decide +kernel
def h59Block4_2 : List NodeSpec := [([1,2,4,13,141],[],[0]),([1,2,13,31,79],[55],[0]),([1,2,4,13,59],[],[0]),([1,4,13,48,79],[53],[0]),([1,2,13,52,79],[55],[0]),([0,1,2,4,56],[9],[0]),([0,2,4,13,147],[],[0]),([0,1,2,15,155],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test4_2 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket3 4 h59Block4_2 = true := by decide +kernel
def h59Block4_3 : List NodeSpec := [([0,1,4,15,159],[],[0]),([0,1,2,4,160],[],[0]),([2,3,4,54,65],[],[0]),([0,3,4,65,168],[],[0]),([0,3,4,65,108],[],[0]),([1,3,4,54,118],[],[0]),([0,1,3,4,169],[],[0]),([0,1,3,80,105],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test4_3 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket3 4 h59Block4_3 = true := by decide +kernel
def h59Block4_4 : List NodeSpec := [([0,3,31,80,173],[],[0]),([0,3,31,80,174],[],[0]),([2,3,4,54,74],[],[0]),([1,3,4,54,80],[],[0]),([0,1,3,80,109],[],[0]),([0,1,3,4,188],[],[0]),([0,1,4,80,181],[],[0]),([0,1,4,80,182],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test4_4 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket3 4 h59Block4_4 = true := by decide +kernel
def h59Block4_5 : List NodeSpec := [([0,1,3,35,200],[],[0]),([0,1,3,34,206],[],[0]),([1,2,4,45,60],[],[0]),([0,3,34,45,198],[],[0]),([0,1,34,35,85],[],[0]),([0,1,3,34,212],[],[0]),([0,3,34,57,198],[],[0]),([0,1,3,34,211],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test4_5 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket3 4 h59Block4_5 = true := by decide +kernel
def h59Block4_6 : List NodeSpec := [([0,1,3,34,213],[],[0]),([2,3,4,54,127],[],[0]),([2,3,4,54,143],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test4_6 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket3 4 h59Block4_6 = true := by decide +kernel
def h59Nodes4 : List NodeSpec := h59Block4_0 ++ h59Block4_1 ++ h59Block4_2 ++ h59Block4_3 ++ h59Block4_4 ++ h59Block4_5 ++ h59Block4_6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Check4 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket3 4 h59Nodes4 = true := by
  unfold h59Nodes4 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨h59Test4_0,h59Test4_1⟩,h59Test4_2⟩,h59Test4_3⟩,h59Test4_4⟩,h59Test4_5⟩,h59Test4_6⟩
def h59Bucket4 : BT (List (List Nat)) := buildBucketsBT h59W h59Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h59G 4 xs.toFinset) h59Bucket4 := buildBucketsBT_sound (by decide) h59Pairs h59WOk h59PoolsOk h59AutosOk h59Bucket3Ok h59Check4
def h59Block5_0 : List NodeSpec := [([1,2,4,6,13,34],[3,5,16],[0]),([1,2,4,6,13,46],[0,3,16],[0]),([1,2,4,6,13,47],[3],[0]),([1,2,4,6,13,50],[0,5,16],[0]),([1,2,4,6,13,51],[5],[0]),([0,1,2,4,15,66],[15],[0]),([1,2,3,4,6,67],[9],[0]),([1,2,3,4,6,73],[9],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test5_0 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket4 5 h59Block5_0 = true := by decide +kernel
def h59Block5_1 : List NodeSpec := [([1,2,3,4,6,79],[1,3,5],[0]),([0,2,3,4,6,45],[0,8,14],[0]),([0,1,2,3,4,55],[6,9,10,12],[0]),([0,1,2,3,4,61],[],[0]),([0,1,2,4,15,90],[31],[0]),([0,2,3,4,8,45],[],[0]),([0,1,2,3,4,91],[9,10],[0]),([0,2,3,4,25,64],[8,9,24],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test5_1 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket4 5 h59Block5_1 = true := by decide +kernel
def h59Block5_2 : List NodeSpec := [([0,1,2,3,25,101],[8,35],[0]),([0,1,2,3,25,102],[],[0]),([0,1,2,3,4,103],[0,9],[0]),([0,2,3,4,26,64],[],[0]),([0,1,2,3,26,101],[],[0]),([0,1,2,3,26,102],[],[0]),([0,1,2,3,4,106],[0,9],[0]),([0,2,3,4,64,95],[0,5,8,24],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test5_2 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket4 5 h59Block5_2 = true := by decide +kernel
def h59Block5_3 : List NodeSpec := [([0,2,3,4,64,96],[8,24],[0]),([0,2,3,4,64,97],[],[0]),([0,2,3,4,64,98],[],[0]),([0,2,3,4,24,64],[0,5,8,24],[0]),([0,2,3,4,27,64],[0],[0]),([0,1,3,23,81],[3,5,6,42,43],[0]),([0,1,3,4,23,81],[5,43],[0]),([0,1,3,4,23,117],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test5_3 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket4 5 h59Block5_3 = true := by decide +kernel
def h59Block5_4 : List NodeSpec := [([0,1,2,3,25,81],[],[0]),([0,1,2,3,25,116],[],[0]),([0,1,2,3,4,119],[],[0]),([0,1,3,4,10,104],[],[0]),([0,1,2,3,26,81],[6],[0]),([0,1,2,3,26,116],[],[0]),([0,1,2,3,4,122],[],[0]),([1,2,3,4,10,88],[1],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test5_4 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket4 5 h59Block5_4 = true := by decide +kernel
def h59Block5_5 : List NodeSpec := [([0,1,3,4,10,123],[14],[0]),([0,1,2,3,4,125],[6],[0]),([0,1,3,4,10,77],[14],[0]),([0,1,2,3,4,129],[6],[0]),([0,2,3,4,24,68],[6],[0]),([0,2,3,4,27,68],[6],[0]),([0,1,3,4,10,131],[14],[0]),([0,1,2,3,4,133],[6],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test5_5 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket4 5 h59Block5_5 = true := by decide +kernel
def h59Block5_6 : List NodeSpec := [([0,1,2,3,24,81],[6,14,42],[0]),([0,1,2,3,27,81],[],[0]),([0,1,2,3,81,110],[6,14,43],[0]),([0,1,2,3,81,115],[5,6],[0]),([0,1,2,3,81,111],[],[0]),([0,1,2,3,81,112],[],[0]),([0,1,2,3,4,110],[6,9,10,14],[0]),([0,1,3,4,11,94],[10],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test5_6 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket4 5 h59Block5_6 = true := by decide +kernel
def h59Block5_7 : List NodeSpec := [([0,1,2,3,4,138],[9],[0]),([0,1,2,3,4,139],[9],[0]),([0,1,2,3,4,140],[9,10],[0]),([0,1,4,13,23,34],[16,20],[0]),([0,1,2,4,13,58],[0],[0]),([0,1,2,4,13,71],[],[0]),([0,1,2,13,31,34],[16,19],[0]),([0,1,2,4,13,77],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test5_7 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket4 5 h59Block5_7 = true := by decide +kernel
def h59Block5_8 : List NodeSpec := [([1,2,4,13,79],[3,5,9,42,53,55],[0]),([1,2,4,13,34,79],[0,3,53,55],[0]),([0,1,2,4,13,45],[0,10],[0]),([0,1,4,13,34,48],[10,20],[0]),([0,1,2,13,34,52],[10,19],[0]),([0,1,2,4,13,62],[0,9,16],[0]),([0,1,2,4,13,63],[0,9],[0]),([0,1,2,4,13,145],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test5_8 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket4 5 h59Block5_8 = true := by decide +kernel
def h59Block5_9 : List NodeSpec := [([0,1,2,4,13,146],[],[0]),([1,2,3,4,13,79],[3,9],[0]),([0,1,2,3,4,63],[0],[0]),([0,1,2,4,15,128],[],[0]),([0,1,2,4,15,150],[60],[0]),([0,1,4,15,23,34],[21,23],[0]),([0,1,2,4,15,58],[],[0]),([0,1,2,4,15,71],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test5_9 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket4 5 h59Block5_9 = true := by decide +kernel
def h59Block5_10 : List NodeSpec := [([0,1,2,4,15,152],[],[0]),([0,1,2,4,15,151],[23],[0]),([0,1,2,4,15,123],[],[0]),([0,1,2,4,15,156],[61],[0]),([0,1,2,15,31,34],[21,22],[0]),([0,1,2,4,15,77],[],[0]),([0,1,2,4,15,158],[],[0]),([0,1,2,4,15,157],[22],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test5_10 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket4 5 h59Block5_10 = true := by decide +kernel
def h59Block5_11 : List NodeSpec := [([0,1,2,4,15,45],[9],[0]),([0,1,2,4,15,153],[57],[0]),([0,1,2,4,15,154],[],[0]),([0,2,3,4,25,65],[9,14,25],[0]),([0,1,3,4,25,118],[14,43],[0]),([0,1,3,4,25,165],[],[0]),([0,1,2,3,4,166],[0,9],[0]),([0,2,3,4,26,65],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test5_11 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket4 5 h59Block5_11 = true := by decide +kernel
def h59Block5_12 : List NodeSpec := [([0,1,3,4,26,118],[],[0]),([0,1,3,4,26,165],[],[0]),([0,1,2,3,4,167],[0,9],[0]),([0,2,3,4,65,161],[0,3,14,25],[0]),([0,2,3,4,65,162],[14,25],[0]),([0,2,3,4,65,163],[],[0]),([0,2,3,4,65,164],[],[0]),([0,2,3,4,24,65],[0,3,14,25],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test5_12 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket4 5 h59Block5_12 = true := by decide +kernel
def h59Block5_13 : List NodeSpec := [([0,2,3,4,27,65],[0],[0]),([0,1,3,4,24,118],[0,6,14,43],[0]),([0,1,3,4,27,118],[],[0]),([1,2,3,4,17,87],[1],[0]),([0,1,2,3,17,128],[8],[0]),([0,1,2,3,4,171],[6],[0]),([0,1,2,3,17,71],[8],[0]),([0,1,2,3,4,172],[6],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test5_13 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket4 5 h59Block5_13 = true := by decide +kernel
def h59Block5_14 : List NodeSpec := [([0,1,3,4,25,80],[],[0]),([0,1,3,4,25,170],[],[0]),([0,1,2,3,4,177],[],[0]),([0,1,3,4,26,80],[12],[0]),([0,1,3,4,26,170],[],[0]),([0,1,2,3,17,105],[],[0]),([0,1,2,3,4,180],[],[0]),([0,1,3,31,80],[3,5,12,42,66],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test5_14 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket4 5 h59Block5_14 = true := by decide +kernel
def h59Block5_15 : List NodeSpec := [([0,1,2,3,31,80],[3,66],[0]),([0,1,2,3,31,183],[],[0]),([0,2,3,4,24,74],[12],[0]),([0,2,3,4,27,74],[10],[0]),([0,1,2,3,17,185],[8],[0]),([0,1,2,3,4,187],[6],[0]),([0,1,3,4,24,80],[8,12,42],[0]),([0,1,3,4,27,80],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test5_15 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket4 5 h59Block5_15 = true := by decide +kernel
def h59Block5_16 : List NodeSpec := [([0,1,3,4,80,173],[8,12,66],[0]),([0,1,3,4,80,174],[3,12],[0]),([0,1,3,4,80,175],[],[0]),([0,1,3,4,80,176],[],[0]),([0,1,2,3,4,173],[8,9,10,12],[0]),([0,1,2,3,18,99],[10],[0]),([0,1,2,3,4,191],[9],[0]),([0,1,2,3,4,192],[9],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test5_16 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket4 5 h59Block5_16 = true := by decide +kernel
def h59Block5_17 : List NodeSpec := [([0,1,2,3,4,149],[6],[0]),([0,1,3,21,29,34],[1,6],[0]),([0,1,3,4,21,49],[],[0]),([0,1,2,3,29,53],[],[0]),([0,1,2,3,4,45],[9,10],[0]),([0,1,3,21,31,34],[1,6],[0]),([0,1,3,4,21,77],[75],[0]),([0,1,3,4,34,195],[6],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test5_17 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket4 5 h59Block5_17 = true := by decide +kernel
def h59Block5_18 : List NodeSpec := [([0,1,3,23,29,34],[1,6],[0]),([0,1,2,3,29,71],[80],[0]),([0,1,3,23,31,34],[1,6],[0]),([0,1,3,4,23,79],[6,43],[0]),([0,1,3,4,23,199],[6],[0]),([0,1,2,3,4,141],[],[0]),([0,1,2,3,4,142],[6],[0]),([0,2,3,4,25,45],[9],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test5_18 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket4 5 h59Block5_18 = true := by decide +kernel
def h59Block5_19 : List NodeSpec := [([0,1,3,25,34,35],[8],[0]),([0,1,2,3,4,200],[],[0]),([0,1,3,4,35,94],[8],[0]),([0,1,2,3,35,99],[8],[0]),([0,1,2,3,4,201],[],[0]),([0,1,2,3,4,203],[],[0]),([0,1,2,3,4,204],[],[0]),([0,1,2,3,4,120],[10,12,14],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test5_19 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket4 5 h59Block5_19 = true := by decide +kernel
def h59Block5_20 : List NodeSpec := [([0,1,2,3,4,178],[6,8,10],[0]),([0,2,3,4,26,45],[9],[0]),([0,1,3,26,34,35],[6],[0]),([0,1,2,3,4,205],[10],[0]),([0,1,2,3,4,206],[],[0]),([0,1,2,3,36,105],[],[0]),([0,1,2,3,4,207],[],[0]),([0,1,3,4,37,104],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test5_20 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket4 5 h59Block5_20 = true := by decide +kernel
def h59Block5_21 : List NodeSpec := [([0,1,2,3,4,208],[],[0]),([0,1,2,3,4,121],[],[0]),([0,1,2,3,4,179],[],[0]),([0,1,2,3,4,124],[6],[0]),([0,1,2,3,34,196],[6],[0]),([0,1,2,3,31,79],[12,66],[0]),([0,1,2,3,31,210],[12],[0]),([0,1,2,3,4,126],[6],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test5_21 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket4 5 h59Block5_21 = true := by decide +kernel
def h59Block5_22 : List NodeSpec := [([0,1,2,3,4,186],[6],[0]),([0,1,2,3,4,59],[],[0]),([0,1,2,3,4,83],[9,10],[0]),([0,1,2,4,45,84],[10],[0]),([0,1,2,4,45,85],[9],[0]),([0,1,3,34,35,45],[6,8,96],[0]),([0,1,2,4,34,85],[],[0]),([0,1,3,34,35,57],[6],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test5_22 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket4 5 h59Block5_22 = true := by decide +kernel
def h59Block5_23 : List NodeSpec := [([0,1,3,34,198],[3,6,42],[0]),([0,1,3,34,35,86],[97],[0]),([0,1,3,34,202],[3,6,42],[0]),([0,2,3,4,24,127],[8,12],[0]),([0,2,3,4,27,127],[10],[0]),([0,2,3,4,24,143],[6,14],[0]),([0,2,3,4,27,143],[6],[0]),([0,1,2,3,4,132],[6],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test5_23 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket4 5 h59Block5_23 = true := by decide +kernel
def h59Nodes5 : List NodeSpec := h59Block5_0 ++ h59Block5_1 ++ h59Block5_2 ++ h59Block5_3 ++ h59Block5_4 ++ h59Block5_5 ++ h59Block5_6 ++ h59Block5_7 ++ h59Block5_8 ++ h59Block5_9 ++ h59Block5_10 ++ h59Block5_11 ++ h59Block5_12 ++ h59Block5_13 ++ h59Block5_14 ++ h59Block5_15 ++ h59Block5_16 ++ h59Block5_17 ++ h59Block5_18 ++ h59Block5_19 ++ h59Block5_20 ++ h59Block5_21 ++ h59Block5_22 ++ h59Block5_23
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Check5 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket4 5 h59Nodes5 = true := by
  unfold h59Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h59Test5_0,h59Test5_1⟩,h59Test5_2⟩,h59Test5_3⟩,h59Test5_4⟩,h59Test5_5⟩,h59Test5_6⟩,h59Test5_7⟩,h59Test5_8⟩,h59Test5_9⟩,h59Test5_10⟩,h59Test5_11⟩,h59Test5_12⟩,h59Test5_13⟩,h59Test5_14⟩,h59Test5_15⟩,h59Test5_16⟩,h59Test5_17⟩,h59Test5_18⟩,h59Test5_19⟩,h59Test5_20⟩,h59Test5_21⟩,h59Test5_22⟩,h59Test5_23⟩
def h59Bucket5 : BT (List (List Nat)) := buildBucketsBT h59W h59Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h59G 5 xs.toFinset) h59Bucket5 := buildBucketsBT_sound (by decide) h59Pairs h59WOk h59PoolsOk h59AutosOk h59Bucket4Ok h59Check5
def h59Block6_0 : List NodeSpec := [([0,1,3,4,38],[0,1,4,5,6],[0]),([0,1,3,4,41],[0,1,3,5,7,8],[0]),([0,1,2,4,42],[0,1,2,3,9,10],[0]),([0,1,2,3,43],[0,1,3,11,12],[0]),([0,1,2,3,44],[0,1,3,5,13,14],[0]),([1,2,4,6,13],[0,3,5,9,15,16,17,18],[0]),([0,1,2,4,6,13],[0,3,5,9,10,15,16,17,19,20],[0]),([0,1,2,4,6,15],[0,3,5,9,10,15,17,21,22,23],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test6_0 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket5 6 h59Block6_0 = true := by decide +kernel
def h59Block6_1 : List NodeSpec := [([0,1,2,3,4,6,23],[0,6,8,17,24],[0]),([0,1,2,3,4,6,31],[0,12,14,17,25],[0]),([0,1,2,3,4,6,34],[0,1,3,5,6,8,12,14],[0]),([0,1,2,3,4,46],[0,1,3,8,9,10,12,14,24,26],[0]),([0,1,2,3,4,6,46],[0,1,3,6,8],[0]),([0,1,2,3,4,47],[3,8,9,10,12,14,24],[0]),([0,1,2,3,4,6,47],[3,6,8],[0]),([0,1,2,3,4,50],[0,1,5,6,8,9,10,14,25,27],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test6_1 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket5 6 h59Block6_1 = true := by decide +kernel
def h59Block6_2 : List NodeSpec := [([0,1,2,3,4,6,50],[0,1,5,12,14],[0]),([0,1,2,3,4,51],[5,6,8,9,10,14,25],[0]),([0,1,2,3,4,6,51],[5,12,14],[0]),([1,2,4,7,13],[0,3,5,16,17,29],[0]),([0,1,2,3,4,6],[0,1,6,8,9,10,12,14,15,17,24,25],[0]),([0,1,2,4,89],[0,3,5,9,10,28,30],[0]),([0,1,2,4,8,15],[0,3,5,9,21,22,23,31],[0]),([0,1,2,3,4,8,34],[1,3,5,6,8,12,14],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test6_2 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket5 6 h59Block6_2 = true := by decide +kernel
def h59Block6_3 : List NodeSpec := [([0,1,2,3,4,69],[0,1,3,8,9,10,12,14,32],[0]),([0,1,2,3,4,75],[0,1,5,6,8,9,10,14,33],[0]),([0,1,2,3,4,9,25],[0,1,6,8,9,10],[0]),([0,1,2,3,4,9,26],[0,1,9,10],[0]),([0,2,3,4,64],[0,3,5,8,24],[0]),([0,1,2,3,4,64],[0,1,3,5,8,9,10,12,14,24],[0]),([0,2,3,4,92],[0,1,5,8,32],[0]),([0,1,2,4,100],[0,5,8,9,10,34,36],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test6_3 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket5 6 h59Block6_3 = true := by decide +kernel
def h59Block6_4 : List NodeSpec := [([0,1,2,3,101],[0,8,12,35,37],[0]),([0,1,2,3,102],[0,5,8,14,38,39],[0]),([0,1,3,4,10,23],[0,1,3,6,8,41,44],[0]),([0,1,2,3,4,10,25],[6,10],[0]),([0,1,2,3,4,10,26],[1,6,9,10],[0]),([0,1,2,3,4,10,28],[0,1,6,12,14],[0]),([0,1,2,3,4,10,31],[5,6,12,14],[0]),([0,1,2,3,4,68],[0,1,3,6,8,9,10,12,14],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test6_4 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket5 6 h59Block6_4 = true := by decide +kernel
def h59Block6_5 : List NodeSpec := [([0,1,2,3,4,10,40],[6,10,12,14],[0]),([0,1,2,3,81],[3,5,6,14,42],[0]),([0,1,2,3,4,81],[0,1,3,5,6,8,9,10,14,42,43],[0]),([0,1,2,3,116],[3,6,12,45,46],[0]),([0,1,2,3,4,11,25],[0,6,9,10],[0]),([0,1,2,3,4,11,26],[0,1,9,10],[0]),([0,1,2,3,4,72],[0,1,5,6,9,10,12,14],[0]),([0,1,2,4,137],[0,5,6,9,10,47],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test6_5 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket5 6 h59Block6_5 = true := by decide +kernel
def h59Block6_6 : List NodeSpec := [([0,1,3,4,12,23],[0,1,3,6,8,41,49],[0]),([0,1,2,3,4,12,25],[3,8,10],[0]),([0,1,2,3,4,12,26],[1,3,6,8,9,10],[0]),([0,1,2,3,4,12,28],[1,3,6,8],[0]),([0,1,2,3,4,12,31],[3,5,6,8,12,14],[0]),([0,1,2,3,4,12,40],[3,6,8,10],[0]),([0,1,2,3,4,82],[1,3,5,8,9,10,14,42,50,51],[0]),([0,1,2,4,13,23],[0,3,10,16,17,19,20,41,52],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test6_6 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket5 6 h59Block6_6 = true := by decide +kernel
def h59Block6_7 : List NodeSpec := [([0,1,2,4,13,31],[0,5,10,16,17,19,20,54,56],[0]),([0,1,2,4,13,34],[0,3,5,10,16,19,20,42,57],[0]),([0,1,2,4,13,48],[0,3,9,10,16,17,19,20,58],[0]),([0,1,2,4,13,52],[0,5,9,10,16,17,19,20,59],[0]),([0,1,2,3,4,13,34],[0,3,6,8,9,10,12,14,57],[0]),([0,1,2,3,4,48],[0,1,3,8,9,10,12,14,17,19,58],[0]),([0,1,2,3,4,52],[0,1,5,6,8,9,10,14,17,59],[0]),([0,1,2,4,13],[0,3,5,9,10,16,17,19,20],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test6_7 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket5 6 h59Block6_7 = true := by decide +kernel
def h59Block6_8 : List NodeSpec := [([0,1,2,4,15,20],[0,3,9,21,22,23,60],[0]),([0,1,2,4,15,23],[0,3,9,21,22,23,52],[0]),([0,1,2,4,15,28],[0,5,9,21,22,23,61],[0]),([0,1,2,4,15,31],[0,5,9,21,22,23,54],[0]),([0,1,2,4,15,34],[0,3,5,9,21,22,23,42,57],[0]),([0,1,2,3,4,16,25],[0,1,9,10,12,14],[0]),([0,1,2,3,4,16,26],[0,1,9,10],[0]),([0,2,3,4,65],[0,3,14,25],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test6_8 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket5 6 h59Block6_8 = true := by decide +kernel
def h59Block6_9 : List NodeSpec := [([0,1,2,3,4,65],[0,1,3,6,8,9,10,14,25],[0]),([0,2,3,4,93],[0,1,3,14,33],[0]),([0,1,3,4,118],[0,6,14,43],[0]),([0,1,3,4,165],[0,3,8,14,63,64],[0]),([0,1,2,4,148],[0,3,9,10,14,20,59],[0]),([0,1,2,3,4,17,20],[0,1,6,8,12],[0]),([0,1,2,3,4,17,23],[3,6,8,12],[0]),([0,1,2,3,4,17,25],[10,12],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test6_9 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket5 6 h59Block6_9 = true := by decide +kernel
def h59Block6_10 : List NodeSpec := [([0,1,2,3,4,17,26],[1,9,10,12],[0]),([0,1,2,3,17,31],[0,1,5,12,14,56,67],[0]),([0,1,2,3,4,74],[0,1,5,6,8,9,10,12,14],[0]),([0,1,2,3,4,17,33],[6,8,10,12],[0]),([0,1,3,4,80],[3,5,8,12,42],[0]),([0,1,2,3,4,80],[0,1,3,6,8,9,10,12,42,66],[0]),([0,1,3,4,170],[3,6,12,68,69],[0]),([0,1,2,3,4,18,25],[0,9,10,12],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test6_10 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket5 6 h59Block6_10 = true := by decide +kernel
def h59Block6_11 : List NodeSpec := [([0,1,2,3,4,18,26],[0,1,9,10],[0]),([0,1,2,3,4,78],[0,1,3,6,8,9,10,12],[0]),([0,1,2,4,190],[0,3,9,10,12,70],[0]),([0,1,2,3,4,19,20],[1,5,12,14],[0]),([0,1,2,3,4,19,23],[3,5,6,8,12,14],[0]),([0,1,2,3,4,19,25],[5,10,14],[0]),([0,1,2,3,4,19,26],[1,5,9,10,12,14],[0]),([0,1,2,3,19,31],[0,1,5,12,14,56,72],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test6_11 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket5 6 h59Block6_11 = true := by decide +kernel
def h59Block6_12 : List NodeSpec := [([0,1,2,3,4,19,33],[5,10,12,14],[0]),([0,1,2,3,4,87],[0,1,3,8,9,10,12,14,17,24],[0]),([0,1,2,3,4,23],[0,1,3,6,8,9,10,12,14,52],[0]),([0,1,2,3,4,128],[0,1,6,8,9,10,14,17],[0]),([0,1,2,3,4,21,29],[1,6,12,17,73,74],[0]),([0,1,2,3,4,21,31],[6,8,12,14,17,54],[0]),([0,1,3,4,21,34],[1,3,6,8,12,42,76],[0]),([0,1,2,4,193],[3,6,10,17,73,77],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test6_12 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket5 6 h59Block6_12 = true := by decide +kernel
def h59Block6_13 : List NodeSpec := [([0,1,2,3,4,53],[0,1,3,6,8,9,10,14],[0]),([0,1,2,3,197],[1,3,6,12,79],[0]),([0,1,2,3,144],[1,3,6,14,17],[0]),([0,1,2,3,4,144],[0,1,3,6,9,10,14,17],[0]),([0,1,2,3,4,67],[0,1,3,6,8,9,10,12,14,32],[0]),([0,1,2,3,4,23,67],[0,1,6,8,32],[0]),([0,1,2,3,4,23,29],[6,8,12,17,52],[0]),([0,1,2,3,4,23,31],[6,8,12,14],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test6_13 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket5 6 h59Block6_13 = true := by decide +kernel
def h59Block6_14 : List NodeSpec := [([0,1,3,4,23,34],[1,3,6,8,12,41,42],[0]),([0,1,3,4,23,37],[1,3,6,8,12,41,81],[0]),([0,1,2,3,4,58],[0,8,9,10,14],[0]),([0,1,2,3,4,23,70],[1,6,8,12,14],[0]),([0,1,2,3,4,71],[0,1,6,8,9,10,14,80],[0]),([0,1,2,3,4,23,71],[1,6,8,12],[0]),([0,1,2,3,4,90],[0,1,6,8,9,10,12,14,17,21,31],[0]),([0,1,2,3,4,25,34],[1,8,9,10],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test6_14 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket5 6 h59Block6_14 = true := by decide +kernel
def h59Block6_15 : List NodeSpec := [([0,1,2,3,4,25,35],[6,10,12],[0]),([0,1,2,3,4,25,36],[6,8,10,12],[0]),([0,1,2,3,4,25,37],[6,10,12,14],[0]),([0,1,2,3,4,94],[0,1,8,9,10,12,14,17,82,83],[0]),([0,1,2,3,4,99],[0,1,6,8,9,10,14,17,84,85],[0]),([0,1,2,3,4,66],[0,1,6,8,9,10,12,14,15],[0]),([0,1,2,3,4,26,34],[1,6,8,9,10,12,14],[0]),([0,1,2,3,4,26,35],[1,6,9,10],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test6_15 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket5 6 h59Block6_15 = true := by decide +kernel
def h59Block6_16 : List NodeSpec := [([0,1,2,3,4,26,36],[1,9,10,12],[0]),([0,1,2,3,4,26,37],[1,6,9,10],[0]),([0,1,2,3,4,104],[0,1,8,9,10,12,14,86],[0]),([0,1,2,3,4,105],[0,1,6,8,9,10,14,87],[0]),([0,1,2,3,4,88],[0,1,5,6,8,9,10,14,17,25],[0]),([0,1,2,3,4,123],[0,1,6,8,9,10,14,17],[0]),([0,1,2,3,4,31],[0,1,5,6,8,9,10,12,14,54],[0]),([0,1,2,3,29,34],[1,5,6,12,14,42,88],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test6_16 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket5 6 h59Block6_16 = true := by decide +kernel
def h59Block6_17 : List NodeSpec := [([0,1,2,3,4,49],[0,1,5,6,8,9,10,12],[0]),([0,1,2,4,194],[5,10,12,17,74,89],[0]),([0,1,3,4,209],[1,3,6,12,91],[0]),([0,1,3,4,135],[1,5,8,12,17],[0]),([0,1,2,3,4,135],[0,1,5,6,8,9,10,12,17],[0]),([0,1,2,3,4,73],[0,1,5,6,8,9,10,12,14,33],[0]),([0,1,2,3,4,31,73],[0,1,12,14,33],[0]),([0,1,2,3,31,34],[1,5,6,12,14,42,56],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test6_17 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket5 6 h59Block6_17 = true := by decide +kernel
def h59Block6_18 : List NodeSpec := [([0,1,2,3,31,36],[1,5,6,12,14,56,92],[0]),([0,1,2,3,4,31,76],[1,6,8,12,14],[0]),([0,1,2,3,4,77],[0,1,6,8,9,10,12,14,75],[0]),([0,1,2,3,4,31,77],[1,6,8,12,14],[0]),([0,1,2,3,4,189],[0,1,3,6,9,10,14,17],[0]),([0,1,2,3,4,184],[0,1,3,6,8,9,10,12,14,17,93,94],[0]),([0,1,2,3,4,185],[0,1,6,8,9,10,14,17,95],[0]),([0,1,2,3,4,79],[0,1,3,5,6,8,9,10,12,14,42,43,66],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test6_18 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket5 6 h59Block6_18 = true := by decide +kernel
def h59Block6_19 : List NodeSpec := [([0,1,2,3,4,34,79],[0,3,6,8,12,14,42,43,66],[0]),([0,1,2,3,4,45],[0,1,6,8,9,10,12,14],[0]),([0,1,2,3,4,34,45],[1,6,8,12,14,57],[0]),([0,1,2,3,4,34,57],[1,6,8,12,14],[0]),([0,1,3,34,35],[3,6,8,42,96],[0]),([0,1,2,3,4,34,86],[9,10,57],[0]),([0,1,2,3,4,198],[0,1,3,6,9,10,12],[0]),([0,1,2,3,4,127],[0,1,5,6,8,9,10,12],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test6_19 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket5 6 h59Block6_19 = true := by decide +kernel
def h59Block6_20 : List NodeSpec := [([0,1,2,3,4,34],[0,1,3,6,8,9,10,12,14,42,57],[0]),([0,1,2,3,4,143],[0,1,3,6,8,9,10,14],[0]),([0,1,2,3,4,136],[0,1,5,6,8,9,10,12,17],[0]),([0,1,2,3,4,130],[0,1,5,6,8,9,10,14,17,101],[0]),([0,1,2,3,4,131],[0,1,6,8,9,10,14,17,102],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test6_20 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket5 6 h59Block6_20 = true := by decide +kernel
def h59Nodes6 : List NodeSpec := h59Block6_0 ++ h59Block6_1 ++ h59Block6_2 ++ h59Block6_3 ++ h59Block6_4 ++ h59Block6_5 ++ h59Block6_6 ++ h59Block6_7 ++ h59Block6_8 ++ h59Block6_9 ++ h59Block6_10 ++ h59Block6_11 ++ h59Block6_12 ++ h59Block6_13 ++ h59Block6_14 ++ h59Block6_15 ++ h59Block6_16 ++ h59Block6_17 ++ h59Block6_18 ++ h59Block6_19 ++ h59Block6_20
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Check6 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket5 6 h59Nodes6 = true := by
  unfold h59Nodes6 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h59Test6_0,h59Test6_1⟩,h59Test6_2⟩,h59Test6_3⟩,h59Test6_4⟩,h59Test6_5⟩,h59Test6_6⟩,h59Test6_7⟩,h59Test6_8⟩,h59Test6_9⟩,h59Test6_10⟩,h59Test6_11⟩,h59Test6_12⟩,h59Test6_13⟩,h59Test6_14⟩,h59Test6_15⟩,h59Test6_16⟩,h59Test6_17⟩,h59Test6_18⟩,h59Test6_19⟩,h59Test6_20⟩
def h59Bucket6 : BT (List (List Nat)) := buildBucketsBT h59W h59Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h59G 6 xs.toFinset) h59Bucket6 := buildBucketsBT_sound (by decide) h59Pairs h59WOk h59PoolsOk h59AutosOk h59Bucket5Ok h59Check6
def h59Block7_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,5,6,9,10,12],[0]),([0,1,2,3,4,6],[0,1,3,5,6,9,10,12,15,17],[0]),([0,1,2,3,4,7],[0,1,3,5,6,9,10,12,17,28],[0]),([0,1,2,3,4,8],[0,1,3,5,6,9,10,12,17,31],[0]),([0,1,2,3,4,9],[0,1,3,5,6,8,9,10,12,34],[0]),([0,1,2,3,4,10],[0,1,3,5,6,9,10,12,40],[0]),([0,1,2,3,4,11],[0,1,5,6,9,10,12,47],[0]),([0,1,2,3,4,12],[0,1,3,5,6,8,9,10,12,48],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test7_0 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket6 7 h59Block7_0 = true := by decide +kernel
def h59Block7_1 : List NodeSpec := [([0,1,2,4,13],[0,3,5,9,10,17],[0]),([0,1,2,3,4,13],[0,1,3,5,6,9,10,12,17],[0]),([0,1,2,3,4,14],[0,1,3,5,6,9,12,17],[0]),([0,1,2,4,15],[0,3,5,9],[0]),([0,1,2,3,4,16],[0,1,3,5,6,9,10,12,14,62],[0]),([0,1,2,3,4,17],[0,1,3,5,6,9,10,12,65],[0]),([0,1,2,3,4,18],[0,1,3,6,9,10,12,70],[0]),([0,1,2,3,4,19],[0,1,3,5,6,9,10,12,14,71],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test7_1 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket6 7 h59Block7_1 = true := by decide +kernel
def h59Block7_2 : List NodeSpec := [([0,1,2,3,4,20],[0,1,3,6,8,9,10,12,17,60],[0]),([0,1,2,3,4,21],[0,1,3,6,9,10,12,17,73],[0]),([0,1,2,3,4,22],[0,1,3,6,9,10,12,17,78],[0]),([0,1,2,3,4,23],[0,1,3,6,8,9,10,12,17,52],[0]),([0,1,2,3,4,25],[0,1,6,9,10,12,17],[0]),([0,1,2,3,4,26],[0,1,6,9,10,12],[0]),([0,1,2,3,4,28],[0,1,5,6,9,10,12,14,17,61],[0]),([0,1,2,3,4,29],[0,1,5,6,9,10,12,17,74],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test7_2 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket6 7 h59Block7_2 = true := by decide +kernel
def h59Block7_3 : List NodeSpec := [([0,1,2,3,4,30],[0,1,5,6,9,10,12,17,90],[0]),([0,1,2,3,4,31],[0,1,5,6,9,10,12,14,17,54],[0]),([0,1,2,3,4,32],[0,1,3,6,9,10,12,17],[0]),([0,1,2,3,4,33],[0,1,3,6,8,9,10,12,17],[0]),([0,1,2,3,4,34],[0,1,3,5,6,8,9,10,12,14,57],[0]),([0,1,2,3,4,35],[0,1,3,6,9,10,12,98],[0]),([0,1,2,3,4,36],[0,1,3,5,6,8,9,10,12,99],[0]),([0,1,2,3,4,37],[0,1,3,6,9,10,12,14,100],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test7_3 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket6 7 h59Block7_3 = true := by decide +kernel
def h59Block7_4 : List NodeSpec := [([0,1,2,3,4,39],[0,1,5,6,9,10,12,17],[0]),([0,1,2,3,4,40],[0,1,5,6,9,10,12,14,17],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test7_4 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket6 7 h59Block7_4 = true := by decide +kernel
def h59Nodes7 : List NodeSpec := h59Block7_0 ++ h59Block7_1 ++ h59Block7_2 ++ h59Block7_3 ++ h59Block7_4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Check7 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket6 7 h59Nodes7 = true := by
  unfold h59Nodes7 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨h59Test7_0,h59Test7_1⟩,h59Test7_2⟩,h59Test7_3⟩,h59Test7_4⟩
def h59Bucket7 : BT (List (List Nat)) := buildBucketsBT h59W h59Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h59G 7 xs.toFinset) h59Bucket7 := buildBucketsBT_sound (by decide) h59Pairs h59WOk h59PoolsOk h59AutosOk h59Bucket6Ok h59Check7
def h59Block8_0 : List NodeSpec := [([0,1,2,3,4],[9],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Test8_0 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket7 8 h59Block8_0 = true := by decide +kernel
def h59Nodes8 : List NodeSpec := h59Block8_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Check8 : checkNodesBT h59W h59G h59Mask h59Pools h59Autos h59Bucket7 8 h59Nodes8 = true := h59Test8_0
def h59Bucket8 : BT (List (List Nat)) := buildBucketsBT h59W h59Nodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h59G 8 xs.toFinset) h59Bucket8 := buildBucketsBT_sound (by decide) h59Pairs h59WOk h59PoolsOk h59AutosOk h59Bucket7Ok h59Check8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h59Bound : Lower h59R h59G 9 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 4,2,18),(VAR 5,1,33)]) (by decide +kernel) h59Bucket8Ok (by decide +kernel)
def h62R : List Nat := varsOf 43
def h62G : Nat := 0xeeaaeeaaaa88aa88eeaaeeaaaa88aa88
def h62Pos : List Nat := [9,42,9,33,3,9,42,33,42,3,3,3,9,3,33,11,11,35,35,41,41]
def h62Neg : List Nat := [8,40,10,32,2,1,34,1,10,1,0,10,0,34,0,10,1,34,1,40,1]
def h62Mask : Nat := fullMask 21
def h62Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x1ffebd,0x1502a0),(0xcccccccccccccccccccccccccccccccc,0x7af52,0x2a954),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x199167,0x88907),(0xffffffff00000000ffffffff00000000,0x1e41ca,0xa204a)]
def h62Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(3,0,1),(0,0,2),(1,0,2),(2,0,2),(3,0,2),(0,0,3),(1,0,3),(2,0,3),(3,0,3),(0,1,2),(1,1,2),(2,1,2),(3,1,2),(0,1,3),(1,1,3),(2,1,3),(3,1,3),(0,2,3),(1,2,3),(2,2,3),(3,2,3),(1,2,4),(0,1,28),(2,2,4),(1,3,4),(0,1,31),(2,3,4),(0,2,5),(1,1,34),(3,2,5),(0,3,5),(1,1,37),(3,3,5),(2,1,8),(1,3,8),(0,2,41),(2,3,8),(3,1,9),(0,3,9),(1,2,45),(3,3,9),(2,1,12),(2,2,12),(3,1,13),(3,2,13),(1,3,18),(0,1,52),(2,3,18),(1,2,54),(1,3,19),(0,2,56),(2,3,19),(1,1,58),(1,2,22),(0,1,60),(2,2,23),(1,1,62)]
def h62W : BT Decor := buildWiresBT 6 h62Base h62Steps
def h62AutoList : List (List (Nat × Nat)) := [[]]
def h62Autos : BT (List (Nat × Nat)) := btOfList 1 h62AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h62Pairs : goodPairs h62G h62Pos h62Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h62BaseOk : ∀ x ∈ h62Base, faithful h62Pos h62Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h62WOk : btAll (fun x => faithful h62Pos h62Neg x ∧ x.1 < 2^128) h62W := buildWiresBT_faithful h62BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h62AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h62G = h62G) h62Autos := btAll_ofList (autos_of (by decide +kernel))
def h62SliceList : List (Option (Nat × Nat)) := []
def h62Slices : BT (Option (Nat × Nat)) := btOfList 1 h62SliceList
def h62Specs : List PoolSpec := []
def h62Pools : BT (Option BoundPool) := buildPoolsBT 1 h62W h62R h62Slices h62Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h62SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h62R h62G p.1 p.2) h62Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h62R h62G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h62PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h62R h62G c) h62Pools := buildPoolsBT_sound h62SlicesOk
def h62Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h62EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h62G (3 - 1) xs.toFinset) h62Empty := trivial
def h62Block3_0 : List NodeSpec := [([0,1,3,28],[],[0]),([0,1,3,30],[],[0]),([0,1,2,31],[],[0]),([0,1,2,33],[],[0]),([0,1,3,34],[],[0]),([0,1,3,36],[],[0]),([0,1,2,37],[],[0]),([0,1,2,39],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h62Test3_0 : checkNodesBT h62W h62G h62Mask h62Pools h62Autos h62Empty 3 h62Block3_0 = true := by decide +kernel
def h62Block3_1 : List NodeSpec := [([0,2,3,35],[],[0]),([0,2,3,40],[],[0]),([0,1,2,41],[],[0]),([0,1,2,43],[],[0]),([0,2,3,29],[],[0]),([0,2,3,44],[],[0]),([0,1,2,45],[],[0]),([0,1,2,47],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h62Test3_1 : checkNodesBT h62W h62G h62Mask h62Pools h62Autos h62Empty 3 h62Block3_1 = true := by decide +kernel
def h62Block3_2 : List NodeSpec := [([0,2,3,38],[],[0]),([0,2,3,48],[],[0]),([0,1,3,46],[],[0]),([0,1,3,49],[],[0]),([0,2,3,32],[],[0]),([0,2,3,50],[],[0]),([0,1,3,42],[],[0]),([0,1,3,51],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h62Test3_2 : checkNodesBT h62W h62G h62Mask h62Pools h62Autos h62Empty 3 h62Block3_2 = true := by decide +kernel
def h62Block3_3 : List NodeSpec := [([0,3,16,17],[],[0]),([0,1,2,52],[],[0]),([0,1,2,54],[],[0]),([0,1,2,56],[],[0]),([0,1,2,58],[],[0]),([0,2,20,21],[],[0]),([0,1,3,60],[],[0]),([0,1,3,57],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h62Test3_3 : checkNodesBT h62W h62G h62Mask h62Pools h62Autos h62Empty 3 h62Block3_3 = true := by decide +kernel
def h62Block3_4 : List NodeSpec := [([0,1,3,55],[],[0]),([0,1,3,62],[],[0]),([0,1,24,25],[],[0]),([0,2,3,63],[],[0]),([0,2,3,53],[],[0]),([0,2,3,59],[],[0]),([0,2,3,61],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h62Test3_4 : checkNodesBT h62W h62G h62Mask h62Pools h62Autos h62Empty 3 h62Block3_4 = true := by decide +kernel
def h62Nodes3 : List NodeSpec := h62Block3_0 ++ h62Block3_1 ++ h62Block3_2 ++ h62Block3_3 ++ h62Block3_4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h62Check3 : checkNodesBT h62W h62G h62Mask h62Pools h62Autos h62Empty 3 h62Nodes3 = true := by
  unfold h62Nodes3 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨h62Test3_0,h62Test3_1⟩,h62Test3_2⟩,h62Test3_3⟩,h62Test3_4⟩
def h62Bucket3 : BT (List (List Nat)) := buildBucketsBT h62W h62Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h62Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h62G 3 xs.toFinset) h62Bucket3 := buildBucketsBT_sound (by decide) h62Pairs h62WOk h62PoolsOk h62AutosOk h62EmptyOk h62Check3
def h62Block4_0 : List NodeSpec := [([0,1,2,3,4],[],[0]),([0,1,2,3,5],[],[0]),([0,1,2,3,6],[],[0]),([0,1,2,3,7],[],[0]),([0,1,2,3,8],[],[0]),([0,1,2,3,9],[],[0]),([0,1,2,3,10],[],[0]),([0,1,2,3,11],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h62Test4_0 : checkNodesBT h62W h62G h62Mask h62Pools h62Autos h62Bucket3 4 h62Block4_0 = true := by decide +kernel
def h62Block4_1 : List NodeSpec := [([0,1,2,3,12],[],[0]),([0,1,2,3,13],[],[0]),([0,1,2,3,14],[],[0]),([0,1,2,3,15],[],[0]),([0,1,2,3,16],[],[0]),([0,1,2,3,17],[],[0]),([0,1,2,3,18],[],[0]),([0,1,2,3,19],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h62Test4_1 : checkNodesBT h62W h62G h62Mask h62Pools h62Autos h62Bucket3 4 h62Block4_1 = true := by decide +kernel
def h62Block4_2 : List NodeSpec := [([0,1,2,3,20],[],[0]),([0,1,2,3,21],[],[0]),([0,1,2,3,22],[],[0]),([0,1,2,3,23],[],[0]),([0,1,2,3,24],[],[0]),([0,1,2,3,25],[],[0]),([0,1,2,3,26],[],[0]),([0,1,2,3,27],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h62Test4_2 : checkNodesBT h62W h62G h62Mask h62Pools h62Autos h62Bucket3 4 h62Block4_2 = true := by decide +kernel
def h62Nodes4 : List NodeSpec := h62Block4_0 ++ h62Block4_1 ++ h62Block4_2
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h62Check4 : checkNodesBT h62W h62G h62Mask h62Pools h62Autos h62Bucket3 4 h62Nodes4 = true := by
  unfold h62Nodes4 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨h62Test4_0,h62Test4_1⟩,h62Test4_2⟩
def h62Bucket4 : BT (List (List Nat)) := buildBucketsBT h62W h62Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h62Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h62G 4 xs.toFinset) h62Bucket4 := buildBucketsBT_sound (by decide) h62Pairs h62WOk h62PoolsOk h62AutosOk h62Bucket3Ok h62Check4
def h62Block5_0 : List NodeSpec := [([0,1,2,3],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h62Test5_0 : checkNodesBT h62W h62G h62Mask h62Pools h62Autos h62Bucket4 5 h62Block5_0 = true := by decide +kernel
def h62Nodes5 : List NodeSpec := h62Block5_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h62Check5 : checkNodesBT h62W h62G h62Mask h62Pools h62Autos h62Bucket4 5 h62Nodes5 = true := h62Test5_0
def h62Bucket5 : BT (List (List Nat)) := buildBucketsBT h62W h62Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h62Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h62G 5 xs.toFinset) h62Bucket5 := buildBucketsBT_sound (by decide) h62Pairs h62WOk h62PoolsOk h62AutosOk h62Bucket4Ok h62Check5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h62Bound : Lower h62R h62G 6 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 3,1,9),(VAR 5,1,33)]) (by decide +kernel) h62Bucket5Ok (by decide +kernel)
def h61R : List Nat := varsOf 59
def h61G : Nat := 0xffeeeeaaeeeeaa88ffeeeeaaeeeeaa88
def h61Pos : List Nat := [9,18,3,3,9,42,9,11,18,17,33,42,56,25,56,49,35,9,42,56,18,18,3,26,26,50,50,33,26,25,33,41,9,50,49,17,33,26,9,11,33,35,50,50,33,18,18,41,18,18]
def h61Neg : List Nat := [8,16,1,2,10,34,1,10,2,1,1,10,48,24,24,48,34,24,40,40,1,0,0,10,24,34,48,34,8,1,40,40,40,32,1,0,32,16,0,1,48,1,16,2,0,24,34,1,48,10]
def h61Mask : Nat := fullMask 50
def h61Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x93dde843a6dd,0x828420100644),(0xcccccccccccccccccccccccccccccccc,0x36ea217f509ae,0x248000a8109b8),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x80e1b18e78f1,0x22001d18e6891),(0xffff0000ffff0000ffff0000ffff0000,0x36c2e37b8f302,0x125200502f002),(0xffffffff00000000ffffffff00000000,0x9f16ce0ddc20,0x14113ce0d9020)]
def h61Steps : List (Nat × Nat × Nat) := [(1,0,1),(2,0,1),(0,0,2),(1,0,2),(2,0,2),(3,0,2),(1,0,3),(1,1,2),(3,1,2),(0,1,3),(1,1,3),(0,2,4),(1,2,4),(2,2,4),(3,2,4),(0,2,5),(2,2,5),(0,2,11),(2,2,11),(0,2,15),(1,2,15),(2,2,15),(3,2,15),(0,4,5),(2,4,5),(0,4,11),(2,4,11),(0,4,15),(1,4,15),(2,4,15),(3,4,15),(0,5,11),(1,5,11),(2,5,15),(2,1,3),(3,1,3),(1,1,4),(3,1,4),(3,1,11),(1,2,3),(2,2,3),(1,3,4),(3,3,4),(3,3,5),(3,3,11),(1,3,43),(1,1,48),(0,0,4),(1,0,4),(2,0,4),(3,0,4),(0,0,15),(3,0,15),(0,2,37),(3,2,37),(0,4,37),(3,4,37),(2,5,49),(1,2,56),(2,2,56),(1,4,56),(2,4,56),(1,0,45),(1,1,45),(1,0,68),(3,0,68),(3,3,68),(3,1,69),(2,5,45),(1,0,16),(1,1,74),(3,1,74),(0,2,74),(1,3,74),(3,3,74),(0,4,74),(1,1,16),(3,0,81),(1,3,81),(3,3,81),(1,3,16),(3,3,75),(2,5,16),(1,1,20),(1,0,21),(3,1,89),(1,3,89),(3,3,89),(1,0,47),(1,1,47),(1,0,94),(3,0,94),(3,3,94),(3,1,95),(2,5,47),(1,1,28),(1,0,29),(3,1,101),(1,3,101),(3,3,101),(3,6,11),(0,3,88),(1,3,88),(2,3,88),(3,3,88),(1,3,7),(3,1,110),(1,4,7),(2,4,7),(3,7,15),(3,3,8),(1,1,115),(3,1,115),(1,3,13),(3,0,118),(3,1,118),(3,4,8),(1,2,80),(1,14,80),(0,8,15),(1,3,117),(1,1,9),(1,3,126),(3,3,126),(1,3,9),(3,1,129),(3,9,15),(2,11,13),(1,3,42),(3,0,133),(3,1,133),(2,11,42),(3,0,85),(3,1,85),(3,1,78),(2,11,16),(1,3,30),(3,3,93),(0,3,100),(1,3,100),(2,3,100),(3,3,100),(2,2,52),(0,1,141),(2,1,141),(3,1,141),(2,15,52),(1,14,77),(3,2,53),(0,15,53),(3,15,53),(1,1,155),(1,3,155),(1,1,54),(1,3,158),(3,3,158),(1,3,54),(3,1,161),(2,15,54),(0,12,46),(2,37,56),(2,15,16),(2,2,166),(2,4,166),(1,1,18),(1,3,18),(1,15,18),(3,1,171),(0,2,171),(3,3,171),(2,15,18),(1,4,175),(1,1,19),(1,3,19),(1,15,19),(3,1,179),(3,3,179),(0,4,179),(2,15,19),(1,2,183),(3,24,25),(1,4,26),(1,2,168),(1,14,168),(3,32,33),(1,14,167),(0,41,44)]
def h61W : BT Decor := buildWiresBT 8 h61Base h61Steps
def h61AutoList : List (List (Nat × Nat)) := [[]]
def h61Autos : BT (List (Nat × Nat)) := btOfList 1 h61AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Pairs : goodPairs h61G h61Pos h61Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61BaseOk : ∀ x ∈ h61Base, faithful h61Pos h61Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61WOk : btAll (fun x => faithful h61Pos h61Neg x ∧ x.1 < 2^128) h61W := buildWiresBT_faithful h61BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h61G = h61G) h61Autos := btAll_ofList (autos_of (by decide +kernel))
def h61SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 8,5),some (subcubeFast 0 32,5),some (subcubeFast 1 0,5),some (subcubeFast 1 8,4),some (subcubeFast 1 32,4),some (subcubeFast 2 0,6),some (subcubeFast 8 0,5),some (subcubeFast 16 0,6),some (subcubeFast 32 0,5),some (subcubeFast 40 0,4)]
def h61Slices : BT (Option (Nat × Nat)) := btOfList 4 h61SliceList
def h61Specs : List PoolSpec := [(5,[]),(2,[]),(3,[]),(7,[(1,0,1)]),(5,[(1,0,3)]),(0,[(1,0,1),(1,0,3)]),(1,[(1,0,1),(1,0,3)]),(7,[]),(4,[]),(6,[]),(0,[]),(8,[]),(1,[]),(0,[(1,0,1)]),(1,[(1,0,1)]),(9,[]),(7,[(1,0,1),(0,2,37)]),(7,[(1,0,1),(0,4,37)]),(5,[(3,3,5)]),(7,[(2,0,1)]),(7,[(3,1,11)]),(5,[(0,0,2)]),(7,[(0,0,2)]),(0,[(1,3,7)]),(5,[(0,0,2),(1,4,7)]),(0,[(1,4,7)]),(5,[(0,0,2),(2,4,7)]),(5,[(0,2,5),(1,3,88)]),(5,[(0,0,2),(3,7,15)]),(5,[(0,2,5)]),(5,[(0,0,2),(1,3,7)]),(7,[(0,0,2),(1,4,7)]),(7,[(0,0,2),(2,4,7)]),(5,[(1,0,2)]),(7,[(1,0,2)]),(8,[(3,1,2)]),(1,[(1,0,2)]),(6,[(0,4,74)]),(5,[(1,0,2),(3,4,8)]),(5,[(1,0,2),(0,8,15)]),(5,[(1,0,2),(3,3,8)]),(8,[(2,2,3)]),(2,[(0,2,4)]),(2,[(3,4,8)]),(6,[(3,4,8)]),(7,[(1,0,2),(3,4,8)]),(5,[(2,0,2)]),(7,[(2,0,2)]),(5,[(3,0,2)]),(7,[(3,0,2)]),(0,[(1,0,3)]),(1,[(1,0,3)]),(5,[(1,0,3),(0,2,37)]),(5,[(1,0,3),(0,4,37)]),(5,[(0,0,4)]),(7,[(0,0,4)]),(1,[(1,0,16)]),(5,[(0,0,4),(2,2,52)]),(5,[(0,4,5),(1,3,100)]),(5,[(0,0,4),(2,15,52)]),(5,[(0,4,5)]),(7,[(0,0,4),(2,2,52)]),(7,[(0,4,11)]),(5,[(1,0,4)]),(7,[(1,0,4)]),(8,[(0,2,74)]),(5,[(1,0,4),(3,2,53)]),(5,[(1,0,4),(0,15,53)]),(5,[(1,0,4),(3,15,53)]),(0,[(1,0,4)]),(6,[(3,1,4)]),(2,[(3,2,53)]),(7,[(1,0,4),(3,2,53)]),(8,[(3,2,53)]),(6,[(3,3,4)]),(7,[(1,0,47)]),(5,[(2,0,4)]),(7,[(2,0,4)]),(5,[(3,0,4)]),(7,[(3,0,4)]),(7,[(1,1,2)]),(5,[(2,2,3)]),(8,[(1,1,2)]),(5,[(0,2,4)]),(7,[(1,1,45)]),(7,[(3,1,2)]),(5,[(1,2,3)]),(8,[(1,2,3)]),(5,[(1,3,13)]),(5,[(0,0,15)]),(5,[(0,0,15),(1,2,56)]),(5,[(0,0,15),(2,2,56)]),(5,[(0,0,15),(1,4,56)]),(5,[(0,0,15),(2,4,56)]),(5,[(1,0,3),(3,2,37)]),(5,[(1,0,3),(3,4,37)]),(5,[(2,5,15)]),(5,[(3,0,15)]),(7,[(3,0,15)]),(5,[(0,2,4),(1,2,4)]),(5,[(1,2,4)]),(5,[(2,2,4)]),(5,[(2,2,4),(1,15,18)]),(5,[(2,2,4),(2,15,18)]),(5,[(3,2,4)]),(5,[(3,2,4),(1,15,19)]),(5,[(3,2,4),(2,15,19)]),(5,[(0,2,15)]),(5,[(0,2,15),(1,2,15)]),(5,[(1,2,15)]),(5,[(2,2,15)]),(5,[(2,2,15),(1,4,26)]),(5,[(3,2,15)]),(5,[(0,4,15)]),(5,[(0,4,15),(1,4,15)]),(5,[(1,4,15)]),(5,[(2,4,15)]),(7,[(1,1,47)]),(5,[(1,3,42)]),(5,[(3,4,15)]),(7,[(1,1,4)]),(6,[(1,1,4)]),(5,[(3,3,4)]),(7,[(3,1,4)]),(5,[(1,3,4)]),(6,[(1,3,4)]),(7,[(0,2,4)]),(7,[(1,0,45)]),(7,[(0,2,4),(1,2,4)]),(7,[(1,2,4)]),(7,[(2,2,4)]),(7,[(2,2,4),(1,1,18)]),(8,[(1,1,18)]),(5,[(2,2,4),(1,3,18)]),(8,[(1,3,18)]),(7,[(3,2,4)]),(7,[(3,2,4),(1,1,19)]),(6,[(1,1,19)]),(5,[(3,2,4),(1,3,19)]),(6,[(1,3,19)])]
def h61Pools : BT (Option BoundPool) := buildPoolsBT 8 h61W h61R h61Slices h61Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Slice9 : Slice h61R h61G (subcubeFast 40 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h1Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Slice8 : Slice h61R h61G (subcubeFast 32 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h9Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Slice7 : Slice h61R h61G (subcubeFast 16 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h62Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Slice6 : Slice h61R h61G (subcubeFast 8 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h21Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Slice5 : Slice h61R h61G (subcubeFast 2 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h34Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Slice4 : Slice h61R h61G (subcubeFast 1 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h50Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Slice3 : Slice h61R h61G (subcubeFast 1 8) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h42Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Slice2 : Slice h61R h61G (subcubeFast 1 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h44Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Slice1 : Slice h61R h61G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h49Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Slice0 : Slice h61R h61G (subcubeFast 0 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h58Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h61R h61G p.1 p.2) h61Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h61R h61G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h61Slice0) (forall_cons (fun _ h => by cases h; exact h61Slice1) (forall_cons (fun _ h => by cases h; exact h61Slice2) (forall_cons (fun _ h => by cases h; exact h61Slice3) (forall_cons (fun _ h => by cases h; exact h61Slice4) (forall_cons (fun _ h => by cases h; exact h61Slice5) (forall_cons (fun _ h => by cases h; exact h61Slice6) (forall_cons (fun _ h => by cases h; exact h61Slice7) (forall_cons (fun _ h => by cases h; exact h61Slice8) (forall_cons (fun _ h => by cases h; exact h61Slice9) (fun _ h => (List.not_mem_nil h).elim)))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h61R h61G c) h61Pools := buildPoolsBT_sound h61SlicesOk
def h61Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h61G (3 - 1) xs.toFinset) h61Empty := trivial
def h61Block3_0 : List NodeSpec := [([2,15,36,80],[],[0]),([0,2,15,123],[],[0]),([2,4,36,117],[],[0]),([4,15,36,122],[],[0]),([4,15,36,77],[],[0]),([0,4,15,152],[],[0]),([2,4,36,155],[],[0]),([2,15,36,182],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test3_0 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Empty 3 h61Block3_0 = true := by decide +kernel
def h61Block3_1 : List NodeSpec := [([2,15,36,176],[],[0]),([2,15,36,168],[],[0]),([0,2,15,188],[],[0]),([4,15,36,187],[],[0]),([4,15,36,173],[],[0]),([4,15,36,184],[],[0]),([4,15,36,167],[],[0]),([0,4,15,190],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test3_1 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Empty 3 h61Block3_1 = true := by decide +kernel
def h61Nodes3 : List NodeSpec := h61Block3_0 ++ h61Block3_1
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Check3 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Empty 3 h61Nodes3 = true := by
  unfold h61Nodes3 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h61Test3_0,h61Test3_1⟩
def h61Bucket3 : BT (List (List Nat)) := buildBucketsBT h61W h61Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h61G 3 xs.toFinset) h61Bucket3 := buildBucketsBT_sound (by decide) h61Pairs h61WOk h61PoolsOk h61AutosOk h61EmptyOk h61Check3
def h61Block4_0 : List NodeSpec := [([0,1,2,4,86],[],[0]),([0,3,4,43,58],[],[0]),([0,2,3,43,60],[],[0]),([0,1,4,48,58],[],[0]),([0,1,3,58,61],[],[0]),([0,1,3,59,60],[],[0]),([0,1,3,59,61],[],[0]),([0,1,2,48,60],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test4_0 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket3 4 h61Block4_0 = true := by decide +kernel
def h61Block4_1 : List NodeSpec := [([0,2,4,106,107],[27],[0]),([0,2,14,15,80],[],[0]),([2,3,4,36,90],[],[0]),([0,2,4,14,117],[40],[0]),([1,2,3,36,80],[],[0]),([0,1,2,3,123],[],[0]),([0,2,3,4,139],[],[0]),([0,4,14,15,122],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test4_1 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket3 4 h61Block4_1 = true := by decide +kernel
def h61Block4_2 : List NodeSpec := [([0,2,4,143,144],[58],[0]),([1,3,4,36,122],[],[0]),([0,2,4,144,148],[58],[0]),([0,4,14,15,77],[],[0]),([2,3,4,36,102],[],[0]),([0,2,4,14,155],[68],[0]),([1,3,4,36,77],[],[0]),([0,1,3,4,152],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test4_2 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket3 4 h61Block4_2 = true := by decide +kernel
def h61Block4_3 : List NodeSpec := [([0,3,12,16,135],[],[0]),([0,1,16,46,71],[],[0]),([1,2,3,4,165],[],[0]),([0,1,3,17,166],[15],[0]),([0,1,3,4,185],[],[0]),([0,1,3,27,186],[15],[0]),([0,2,14,15,182],[],[0]),([0,2,14,15,176],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test4_3 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket3 4 h61Block4_3 = true := by decide +kernel
def h61Block4_4 : List NodeSpec := [([0,2,14,15,168],[],[0]),([0,1,2,3,189],[],[0]),([0,4,14,15,187],[],[0]),([0,1,3,35,187],[15],[0]),([0,4,14,15,173],[],[0]),([0,4,14,15,184],[],[0]),([0,4,14,15,167],[],[0]),([0,3,16,41,120],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test4_4 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket3 4 h61Block4_4 = true := by decide +kernel
def h61Block4_5 : List NodeSpec := [([0,1,16,44,97],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test4_5 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket3 4 h61Block4_5 = true := by decide +kernel
def h61Nodes4 : List NodeSpec := h61Block4_0 ++ h61Block4_1 ++ h61Block4_2 ++ h61Block4_3 ++ h61Block4_4 ++ h61Block4_5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Check4 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket3 4 h61Nodes4 = true := by
  unfold h61Nodes4 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨h61Test4_0,h61Test4_1⟩,h61Test4_2⟩,h61Test4_3⟩,h61Test4_4⟩,h61Test4_5⟩
def h61Bucket4 : BT (List (List Nat)) := buildBucketsBT h61W h61Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h61G 4 xs.toFinset) h61Bucket4 := buildBucketsBT_sound (by decide) h61Pairs h61WOk h61PoolsOk h61AutosOk h61Bucket3Ok h61Check4
def h61Block5_0 : List NodeSpec := [([2,4,5,11,15],[0,1,3,4,5,6,7],[0]),([2,3,4,5,11,43],[1],[0]),([1,2,4,5,11,48],[1],[0]),([0,2,4,5,11,15],[0,1,7],[0]),([0,2,3,4,5,43],[0],[0]),([0,1,2,4,11,48],[0],[0]),([0,1,2,3,4,37],[9,10,11,12],[0]),([1,2,3,4,5,62],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test5_0 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket4 5 h61Block5_0 = true := by decide +kernel
def h61Block5_1 : List NodeSpec := [([2,3,4,5,15,56],[0],[0]),([2,3,4,5,15,57],[0],[0]),([0,2,4,5,15,48],[0,7],[0]),([0,2,3,4,5,68],[1],[0]),([0,1,2,4,45,48],[10],[0]),([0,1,2,3,4,69],[10],[0]),([0,1,2,3,4,73],[7],[0]),([1,2,3,4,5,74],[0,2,8],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test5_1 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket4 5 h61Block5_1 = true := by decide +kernel
def h61Block5_2 : List NodeSpec := [([0,2,3,4,5,81],[1,9,11],[0]),([0,1,2,3,4,75],[7,9,10],[0]),([0,1,2,3,4,87],[],[0]),([1,2,3,4,5,89],[0],[0]),([0,2,3,4,5,94],[1],[0]),([0,1,2,4,47,48],[12],[0]),([0,1,2,3,4,95],[12],[0]),([0,1,2,3,4,99],[7],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test5_2 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket4 5 h61Block5_2 = true := by decide +kernel
def h61Block5_3 : List NodeSpec := [([0,1,2,3,4,57],[],[0]),([1,2,3,4,37,57],[0],[0]),([0,1,2,3,4,43],[],[0]),([0,2,3,4,37,43],[0],[0]),([0,1,3,4,37,58],[10,15],[0]),([0,1,3,4,37,59],[9],[0]),([0,1,2,3,4,48],[],[0]),([0,1,2,4,37,48],[0],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test5_3 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket4 5 h61Block5_3 = true := by decide +kernel
def h61Block5_4 : List NodeSpec := [([0,1,2,3,37,60],[12,15],[0]),([0,1,2,3,37,61],[11],[0]),([1,2,3,4,5,57],[0],[0]),([0,1,3,4,5,58],[16],[0]),([0,1,2,3,5,60],[17],[0]),([1,2,3,4,5,101],[0],[0]),([1,2,3,4,11,105],[],[0]),([0,2,3,4,15,88],[7,9,13],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test5_4 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket4 5 h61Block5_4 = true := by decide +kernel
def h61Block5_5 : List NodeSpec := [([0,1,2,4,15,110],[0,9,23],[0]),([0,1,2,3,15,112],[9,24,25],[0]),([0,1,2,3,15,113],[26],[0]),([0,1,2,3,4,107],[9,27],[0]),([0,1,2,3,4,114],[0,7,28],[0]),([0,2,3,4,88,106],[1,8,9,15,29],[0]),([0,2,3,4,88,107],[9,13],[0]),([0,2,3,4,88,108],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test5_5 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket4 5 h61Block5_5 = true := by decide +kernel
def h61Block5_6 : List NodeSpec := [([0,2,3,4,88,109],[],[0]),([0,2,3,4,40,88],[1],[0]),([0,1,2,3,4,109],[1],[0]),([0,1,2,4,107,110],[9,23,27],[0]),([0,1,2,4,110,111],[],[0]),([0,1,2,3,4,111],[1],[0]),([0,1,3,4,13,115],[],[0]),([0,1,3,4,8,118],[15],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test5_6 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket4 5 h61Block5_6 = true := by decide +kernel
def h61Block5_7 : List NodeSpec := [([0,1,2,3,15,80],[10,37],[0]),([0,1,2,3,15,121],[38],[0]),([0,1,2,3,4,124],[1,39],[0]),([0,1,2,3,4,117],[40],[0]),([0,2,3,4,14,90],[10],[0]),([0,2,3,4,40,90],[10],[0]),([0,1,3,4,45,90],[],[0]),([0,1,2,3,4,125],[10],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test5_7 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket4 5 h61Block5_7 = true := by decide +kernel
def h61Block5_8 : List NodeSpec := [([0,1,3,4,8,68],[15],[0]),([0,1,2,3,4,116],[10],[0]),([0,1,2,3,14,80],[10,11,37,42],[0]),([0,1,2,3,39,80],[10,37],[0]),([0,1,2,3,40,80],[10,37],[0]),([0,2,3,4,15,126],[7],[0]),([0,1,2,4,15,129],[0],[0]),([0,1,2,3,4,127],[10,11,12],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test5_8 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket4 5 h61Block5_8 = true := by decide +kernel
def h61Block5_9 : List NodeSpec := [([0,1,2,3,4,131],[],[0]),([0,1,2,3,4,128],[],[0]),([0,1,2,3,4,130],[],[0]),([0,2,3,4,13,43],[10],[0]),([0,1,2,4,11,118],[1],[0]),([0,1,2,3,4,91],[10],[0]),([0,1,2,3,4,132],[0],[0]),([1,2,4,11,15,56],[7],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test5_9 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket4 5 h61Block5_9 = true := by decide +kernel
def h61Block5_10 : List NodeSpec := [([1,2,4,11,15,57],[7],[0]),([0,2,4,11,15,43],[0,7],[0]),([0,2,3,4,42,43],[12],[0]),([0,1,2,4,11,133],[1],[0]),([0,1,2,3,4,103],[12],[0]),([0,1,2,3,4,136],[0],[0]),([1,2,3,4,11,57],[0],[0]),([0,1,3,4,11,58],[52],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test5_10 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket4 5 h61Block5_10 = true := by decide +kernel
def h61Block5_11 : List NodeSpec := [([0,1,2,3,11,60],[53],[0]),([1,2,3,4,11,74],[2,7,8],[0]),([0,1,2,4,11,85],[1,9,11],[0]),([0,1,2,3,4,78],[0,9,10],[0]),([0,1,2,3,4,140],[],[0]),([1,2,3,4,11,67],[0],[0]),([1,2,3,4,11,93],[0],[0]),([0,2,3,4,15,100],[7,11,14],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test5_11 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket4 5 h61Block5_11 = true := by decide +kernel
def h61Block5_12 : List NodeSpec := [([0,1,3,4,15,122],[11,56],[0]),([0,1,3,4,15,147],[57],[0]),([0,1,2,4,15,141],[0,11,51],[0]),([0,1,2,3,4,144],[11,58],[0]),([0,1,2,3,4,151],[0,7,59],[0]),([0,2,3,4,100,143],[1,2,11,15,60],[0]),([0,2,3,4,100,144],[11,14],[0]),([0,2,3,4,100,145],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test5_12 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket4 5 h61Block5_12 = true := by decide +kernel
def h61Block5_13 : List NodeSpec := [([0,2,3,4,100,146],[],[0]),([0,2,3,4,40,100],[1],[0]),([0,1,2,3,4,146],[1],[0]),([0,1,3,4,14,122],[1,10,11,15,56],[0]),([0,1,3,4,39,122],[],[0]),([0,1,3,4,40,122],[],[0]),([0,1,2,4,141,148],[1,2,11,15,62],[0]),([0,1,2,4,141,144],[11,51,58],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test5_13 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket4 5 h61Block5_13 = true := by decide +kernel
def h61Block5_14 : List NodeSpec := [([0,1,2,4,141,149],[],[0]),([0,1,2,4,141,150],[],[0]),([0,1,2,4,39,141],[1],[0]),([0,1,2,3,4,150],[1],[0]),([0,1,3,4,15,77],[12,65],[0]),([0,1,3,4,15,153],[66],[0]),([0,1,2,3,4,154],[1,67],[0]),([0,1,2,3,4,155],[68],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test5_14 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket4 5 h61Block5_14 = true := by decide +kernel
def h61Block5_15 : List NodeSpec := [([0,1,2,3,53,133],[15],[0]),([0,1,2,3,42,142],[],[0]),([0,2,3,4,14,102],[12],[0]),([0,2,3,4,40,102],[12],[0]),([0,1,2,3,47,102],[],[0]),([0,1,2,3,4,157],[12],[0]),([0,1,3,4,14,77],[9,12,42,65],[0]),([0,1,3,4,39,77],[12,65],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test5_15 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket4 5 h61Block5_15 = true := by decide +kernel
def h61Block5_16 : List NodeSpec := [([0,1,3,4,40,77],[12,65],[0]),([0,1,2,3,53,94],[15],[0]),([0,1,2,4,39,142],[12],[0]),([0,1,2,3,4,156],[12],[0]),([0,2,3,4,15,158],[7],[0]),([0,1,2,4,15,161],[0],[0]),([0,1,2,3,4,159],[9,10,12],[0]),([0,1,2,3,4,163],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test5_16 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket4 5 h61Block5_16 = true := by decide +kernel
def h61Block5_17 : List NodeSpec := [([0,1,2,3,4,160],[],[0]),([0,1,2,3,4,162],[],[0]),([0,1,3,12,16,46],[10],[0]),([0,1,3,4,16,71],[12],[0]),([0,1,3,4,12,85],[0],[0]),([0,2,3,4,12,135],[9],[0]),([0,1,2,4,46,71],[10],[0]),([0,1,2,3,4,164],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test5_17 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket4 5 h61Block5_17 = true := by decide +kernel
def h61Block5_18 : List NodeSpec := [([0,1,2,3,4,92],[],[0]),([0,1,2,3,4,119],[],[0]),([1,2,3,4,37,56],[],[0]),([0,1,3,4,15,63],[90],[0]),([0,1,3,4,15,64],[91],[0]),([0,1,2,3,15,65],[92],[0]),([0,1,2,3,15,66],[93],[0]),([0,2,3,4,15,43],[0],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test5_18 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket4 5 h61Block5_18 = true := by decide +kernel
def h61Block5_19 : List NodeSpec := [([0,1,3,4,15,58],[52],[0]),([0,1,3,4,15,59],[94],[0]),([0,1,2,4,15,48],[0],[0]),([0,1,2,3,15,60],[53],[0]),([0,1,2,3,15,61],[95],[0]),([1,2,3,4,38,57],[],[0]),([0,2,3,4,15,51],[0],[0]),([0,1,2,4,15,50],[0],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test5_19 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket4 5 h61Block5_19 = true := by decide +kernel
def h61Block5_20 : List NodeSpec := [([0,2,3,4,15,81],[7],[0]),([0,1,3,15,16,17],[9,10,15,99],[0]),([0,1,2,4,15,85],[0],[0]),([0,1,2,3,4,83],[],[0]),([0,1,2,3,4,166],[9,10],[0]),([0,1,2,3,4,171],[9,102],[0]),([0,1,2,3,4,175],[10,103],[0]),([0,1,2,3,4,179],[9,105],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test5_20 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket4 5 h61Block5_20 = true := by decide +kernel
def h61Block5_21 : List NodeSpec := [([0,1,2,3,4,183],[10,106],[0]),([0,1,3,4,24,25],[108],[0]),([0,2,3,4,15,120],[0],[0]),([0,1,2,4,15,71],[0],[0]),([0,2,3,4,15,68],[0,84],[0]),([0,1,3,4,26,27],[15],[0]),([0,1,2,4,15,118],[0,88],[0]),([0,1,2,3,15,186],[9,111],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test5_21 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket4 5 h61Block5_21 = true := by decide +kernel
def h61Block5_22 : List NodeSpec := [([0,1,2,3,15,182],[],[0]),([0,1,2,3,15,176],[],[0]),([0,1,2,3,15,168],[10,15],[0]),([0,1,2,3,32,33],[114],[0]),([0,2,3,4,15,135],[0],[0]),([0,1,2,4,15,97],[0],[0]),([0,2,3,4,15,94],[0,117],[0]),([0,1,3,4,15,187],[11],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test5_22 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket4 5 h61Block5_22 = true := by decide +kernel
def h61Block5_23 : List NodeSpec := [([0,1,3,4,15,173],[],[0]),([0,1,2,4,15,133],[0,118],[0]),([0,1,2,3,34,35],[15],[0]),([0,1,3,4,15,184],[],[0]),([0,1,3,4,15,167],[12,15],[0]),([0,2,3,4,41,120],[10],[0]),([0,1,3,16,41,44],[10],[0]),([0,1,2,4,44,97],[9],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test5_23 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket4 5 h61Block5_23 = true := by decide +kernel
def h61Block5_24 : List NodeSpec := [([0,1,2,3,4,191],[],[0]),([0,1,2,3,41,85],[0],[0]),([0,1,2,3,16,97],[10],[0]),([0,1,2,3,4,104],[],[0]),([0,1,2,3,4,134],[],[0]),([0,1,3,4,16,120],[12],[0]),([0,1,3,4,44,81],[7],[0]),([0,1,2,3,4,72],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test5_24 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket4 5 h61Block5_24 = true := by decide +kernel
def h61Block5_25 : List NodeSpec := [([0,1,2,3,4,70],[],[0]),([0,1,2,3,4,76],[],[0]),([0,1,2,3,4,79],[],[0]),([0,1,2,3,4,82],[],[0]),([0,1,2,3,46,81],[7],[0]),([0,1,2,3,4,84],[],[0]),([0,1,2,3,16,135],[10],[0]),([0,1,2,3,4,137],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test5_25 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket4 5 h61Block5_25 = true := by decide +kernel
def h61Block5_26 : List NodeSpec := [([0,1,2,3,4,138],[],[0]),([0,1,2,3,4,174],[9],[0]),([0,1,2,3,4,172],[9],[0]),([0,1,2,3,4,181],[10],[0]),([0,1,2,3,4,180],[10],[0]),([0,1,2,3,4,98],[],[0]),([0,1,2,3,4,96],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test5_26 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket4 5 h61Block5_26 = true := by decide +kernel
def h61Nodes5 : List NodeSpec := h61Block5_0 ++ h61Block5_1 ++ h61Block5_2 ++ h61Block5_3 ++ h61Block5_4 ++ h61Block5_5 ++ h61Block5_6 ++ h61Block5_7 ++ h61Block5_8 ++ h61Block5_9 ++ h61Block5_10 ++ h61Block5_11 ++ h61Block5_12 ++ h61Block5_13 ++ h61Block5_14 ++ h61Block5_15 ++ h61Block5_16 ++ h61Block5_17 ++ h61Block5_18 ++ h61Block5_19 ++ h61Block5_20 ++ h61Block5_21 ++ h61Block5_22 ++ h61Block5_23 ++ h61Block5_24 ++ h61Block5_25 ++ h61Block5_26
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Check5 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket4 5 h61Nodes5 = true := by
  unfold h61Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h61Test5_0,h61Test5_1⟩,h61Test5_2⟩,h61Test5_3⟩,h61Test5_4⟩,h61Test5_5⟩,h61Test5_6⟩,h61Test5_7⟩,h61Test5_8⟩,h61Test5_9⟩,h61Test5_10⟩,h61Test5_11⟩,h61Test5_12⟩,h61Test5_13⟩,h61Test5_14⟩,h61Test5_15⟩,h61Test5_16⟩,h61Test5_17⟩,h61Test5_18⟩,h61Test5_19⟩,h61Test5_20⟩,h61Test5_21⟩,h61Test5_22⟩,h61Test5_23⟩,h61Test5_24⟩,h61Test5_25⟩,h61Test5_26⟩
def h61Bucket5 : BT (List (List Nat)) := buildBucketsBT h61W h61Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h61G 5 xs.toFinset) h61Bucket5 := buildBucketsBT_sound (by decide) h61Pairs h61WOk h61PoolsOk h61AutosOk h61Bucket4Ok h61Check5
def h61Block6_0 : List NodeSpec := [([1,2,3,4,5,11],[0,1,2,3,4,7,8],[0]),([0,1,2,3,4,5,11],[0,1,3,4,7],[0]),([1,2,3,4,5,49],[0,1,2,3,7,8],[0]),([0,2,3,4,5,15],[0,1,3,7,13,14],[0]),([0,1,2,3,4,5,45],[0,2,7,9,10],[0]),([0,1,2,3,4,5,16],[0,1,2,8,9,10,11,12],[0]),([0,1,2,3,4,5,20],[0,1,2,9,10],[0]),([0,1,2,3,4,5,21],[2,9,10],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test6_0 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket5 6 h61Block6_0 = true := by decide +kernel
def h61Block6_1 : List NodeSpec := [([0,1,2,3,4,5,47],[0,7,8,11,12],[0]),([0,1,2,3,4,37],[9,10,11,12],[0]),([0,1,2,3,4,5,37],[2,3,7,8],[0]),([0,1,2,3,4,48],[0,1,3,7,9,10,11,12,18],[0]),([0,1,2,3,4,5,48],[0,1,3,7],[0]),([0,1,2,3,4,5,28],[0,1,8,11,12],[0]),([0,1,2,3,4,5,29],[8,11,12],[0]),([1,2,3,4,6,11],[0,1,2,4,7,8,19],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test6_1 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket5 6 h61Block6_1 = true := by decide +kernel
def h61Block6_2 : List NodeSpec := [([0,1,2,3,4,50],[0,1,2,4,7,8,9,10,11,12,20],[0]),([0,1,2,3,4,7,15],[0,1,7,9,10,21],[0]),([0,2,3,4,88],[1,2,8,9,29],[0]),([0,1,2,3,4,88],[0,1,2,7,8,9,11,12,29],[0]),([0,1,2,4,110],[1,2,8,9,22,30],[0]),([0,1,2,3,4,110],[0,1,2,7,8,9,11,12,22,30],[0]),([0,1,2,3,112],[1,9,12,24,31],[0]),([0,1,2,3,113],[1,9,11,26,32],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test6_2 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket5 6 h61Block6_2 = true := by decide +kernel
def h61Block6_3 : List NodeSpec := [([0,1,3,4,8,13],[0,1,9,10,15,33,35,36],[0]),([0,1,2,3,4,8,15],[9,10,33],[0]),([0,1,2,3,4,90],[0,1,2,7,9,10,11,12],[0]),([0,1,3,4,8,45],[1,7,9,10,15,34,36,41],[0]),([0,1,2,3,4,115],[0,1,2,7,9,10,11,12,34,40],[0]),([0,1,2,3,80],[2,10,11,15,37,42],[0]),([0,1,2,3,121],[2,10,12,38,43,44,45],[0]),([0,1,2,3,4,9,15],[0,1,7,9,10,46],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test6_3 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket5 6 h61Block6_3 = true := by decide +kernel
def h61Block6_4 : List NodeSpec := [([0,1,2,3,4,126],[0,1,7,8,10,11,12,46],[0]),([0,1,2,3,4,129],[0,1,7,8,10,11,12,47],[0]),([0,1,2,3,4,10,15],[2,9,10,48],[0]),([0,1,2,3,4,11,13],[0,2,7,9,10],[0]),([0,1,2,4,11,15],[0,1,4,7,50,51],[0]),([0,1,2,3,4,11,42],[0,7,8,11,12],[0]),([0,1,2,3,4,11,37],[0,2,4,8],[0]),([0,1,2,3,4,43],[0,1,4,7,9,10,11,12,20],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test6_4 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket5 6 h61Block6_4 = true := by decide +kernel
def h61Block6_5 : List NodeSpec := [([0,1,2,3,4,11,43],[0,1,4,7],[0]),([0,1,2,3,4,11,16],[1,2,7,8,9,10,11,12],[0]),([0,1,2,3,4,11,22],[1,2,7,9,10],[0]),([0,1,2,3,4,11,23],[2,9,10],[0]),([0,1,2,3,4,11,30],[1,7,8,11,12],[0]),([0,1,2,3,4,11,31],[8,11,12],[0]),([0,1,2,3,4,51],[0,1,2,3,7,8,9,10,11,12,18],[0]),([0,1,2,3,4,15,52],[0,1,7,11,12,54],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test6_5 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket5 6 h61Block6_5 = true := by decide +kernel
def h61Block6_6 : List NodeSpec := [([0,2,3,4,100],[1,2,11,60],[0]),([0,1,2,3,4,100],[0,1,2,7,9,10,11,60],[0]),([0,1,3,4,122],[1,10,11],[0]),([0,1,3,4,147],[1,9,11,57,61],[0]),([0,1,2,4,141],[1,2,11,62],[0]),([0,1,2,3,4,141],[0,1,2,7,9,10,11,62],[0]),([0,1,2,3,4,15,53],[11,12,63],[0]),([0,1,2,3,42,53],[0,1,11,12,15,63,69,70],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test6_6 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket5 6 h61Block6_6 = true := by decide +kernel
def h61Block6_7 : List NodeSpec := [([0,1,2,3,4,102],[0,1,7,8,9,10,11,12],[0]),([0,1,3,4,77],[8,9,12,15,42,65],[0]),([0,1,3,4,153],[2,10,12,66,71,72,73],[0]),([0,1,2,3,47,53],[1,7,11,12,15,64,69,74],[0]),([0,1,2,3,4,142],[0,1,7,8,9,10,11,12,75],[0]),([0,1,2,3,4,15,54],[0,1,7,11,12,76],[0]),([0,1,2,3,4,158],[0,1,2,7,9,10,12,76],[0]),([0,1,2,3,4,161],[0,1,2,7,9,10,12,77],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test6_7 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket5 6 h61Block6_7 = true := by decide +kernel
def h61Block6_8 : List NodeSpec := [([0,1,2,3,4,15,55],[8,11,12,78],[0]),([0,1,3,4,12,45],[0,2,7,9,10,41,80,81,82],[0]),([0,1,3,4,12,16],[0,2,9,10,12,42,82,83],[0]),([0,1,2,3,4,12,46],[0,7,9,10,11,12],[0]),([0,1,2,3,4,71],[0,1,2,7,9,10,11,12,81,84],[0]),([0,1,2,3,4,89],[0,1,2,7,9,10,11,12],[0]),([0,1,3,4,13,44],[0,2,7,9,10,35,85,86,87],[0]),([0,1,2,3,4,118],[0,1,7,9,10,11,12,15,85,88],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test6_8 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket5 6 h61Block6_8 = true := by decide +kernel
def h61Block6_9 : List NodeSpec := [([0,1,2,3,4,15,56],[0,1,7,89],[0]),([0,1,2,3,4,15,37],[1,4],[0]),([0,1,2,3,4,15,38],[1,96],[0]),([0,1,2,3,4,57],[0,7,9,10,11,12,97,98],[0]),([0,1,2,3,4,15,57],[0,1,7,97],[0]),([0,1,2,3,4,15,16],[0,7,9,10,11,12,83],[0]),([0,1,2,3,4,15,17],[9,10,11,12,15,100],[0]),([0,1,2,3,4,15,18],[9,10,11,12,101],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test6_9 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket5 6 h61Block6_9 = true := by decide +kernel
def h61Block6_10 : List NodeSpec := [([0,1,2,3,4,15,19],[9,10,11,12,104],[0]),([0,1,2,3,4,15,24],[9,10,107],[0]),([0,1,2,3,4,15,25],[9,10,109],[0]),([0,1,2,3,4,15,26],[9,10,110],[0]),([0,1,2,3,4,15,27],[9,10,112],[0]),([0,1,2,3,4,15,32],[11,12,113],[0]),([0,1,2,3,4,15,33],[11,12,115],[0]),([0,1,2,3,4,15,34],[11,12,116],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test6_10 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket5 6 h61Block6_10 = true := by decide +kernel
def h61Block6_11 : List NodeSpec := [([0,1,2,3,4,15,35],[11,12,119],[0]),([0,1,2,3,4,41,44],[0,7,9,10,11,12],[0]),([0,1,2,3,16,41],[0,8,10,11,12,42,83,121],[0]),([0,1,2,3,41,47],[0,7,8,11,12,74,120,121,122],[0]),([0,1,2,3,4,97],[0,1,7,8,9,10,11,12,117,122],[0]),([0,1,2,3,4,101],[0,1,7,8,9,10,11,12],[0]),([0,1,2,3,42,46],[0,7,8,11,12,70,123,124,125],[0]),([0,1,2,3,4,133],[0,1,7,9,10,11,12,15,118,123],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test6_11 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket5 6 h61Block6_11 = true := by decide +kernel
def h61Block6_12 : List NodeSpec := [([0,1,2,3,4,120],[0,1,2,7,9,10,11,12,85,88],[0]),([0,1,3,4,16,44],[2,7,9,10,12,42,87,126],[0]),([0,1,2,3,4,67],[0,1,2,7,9,10,11,12,127],[0]),([0,1,2,3,4,68],[0,1,7,9,10,11,12,15,81,84],[0]),([0,1,2,3,4,74],[0,1,2,7,8,9,10,11,42],[0]),([0,1,2,3,4,81],[0,1,7,9,10,11,83],[0]),([0,1,3,16,17],[2,9,10,15,42,99,128],[0]),([0,1,2,3,16,46],[7,8,10,11,12,42,125,126],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test6_12 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket5 6 h61Block6_12 = true := by decide +kernel
def h61Block6_13 : List NodeSpec := [([0,1,2,3,4,85],[0,1,7,9,10,11,126],[0]),([0,1,2,3,4,169],[0,1,7,8,9,10,12,15,101,131,132],[0]),([0,1,2,3,4,170],[0,1,7,8,9,10,12,15,130,133,134],[0]),([0,1,2,3,4,177],[0,1,2,7,9,10,11,15,104,136,137],[0]),([0,1,2,3,4,178],[0,1,2,7,9,10,11,15,135,138,139],[0]),([0,1,2,3,4,135],[0,1,7,8,9,10,11,12,118,123],[0]),([0,1,2,3,4,93],[0,1,7,8,9,10,11,12,75],[0]),([0,1,2,3,4,94],[0,1,7,9,10,11,12,15,117,122],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test6_13 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket5 6 h61Block6_13 = true := by decide +kernel
def h61Nodes6 : List NodeSpec := h61Block6_0 ++ h61Block6_1 ++ h61Block6_2 ++ h61Block6_3 ++ h61Block6_4 ++ h61Block6_5 ++ h61Block6_6 ++ h61Block6_7 ++ h61Block6_8 ++ h61Block6_9 ++ h61Block6_10 ++ h61Block6_11 ++ h61Block6_12 ++ h61Block6_13
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Check6 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket5 6 h61Nodes6 = true := by
  unfold h61Nodes6 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h61Test6_0,h61Test6_1⟩,h61Test6_2⟩,h61Test6_3⟩,h61Test6_4⟩,h61Test6_5⟩,h61Test6_6⟩,h61Test6_7⟩,h61Test6_8⟩,h61Test6_9⟩,h61Test6_10⟩,h61Test6_11⟩,h61Test6_12⟩,h61Test6_13⟩
def h61Bucket6 : BT (List (List Nat)) := buildBucketsBT h61W h61Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h61G 6 xs.toFinset) h61Bucket6 := buildBucketsBT_sound (by decide) h61Pairs h61WOk h61PoolsOk h61AutosOk h61Bucket5Ok h61Check6
def h61Block7_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,7,8,9,10,11,12],[0]),([0,1,2,3,4,6],[0,1,2,7,8,9,10,11,12,19],[0]),([0,1,2,3,4,7],[0,1,2,7,8,9,11,12,21,22],[0]),([0,1,2,3,4,8],[0,1,2,7,8,9,10,11,12,15,33,34],[0]),([0,1,2,3,4,9],[0,1,7,8,9,10,11,12,46,47],[0]),([0,1,2,3,4,10],[0,1,2,7,8,9,10,11,12,15,48,49],[0]),([0,1,2,3,4,11],[0,1,2,4,7,8,9,10,11,12],[0]),([0,1,2,3,4,49],[0,1,2,7,8,9,10,11,12],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test7_0 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket6 7 h61Block7_0 = true := by decide +kernel
def h61Block7_1 : List NodeSpec := [([0,1,2,3,4,52],[0,1,2,7,9,10,11,54,55],[0]),([0,1,2,3,4,53],[0,1,2,7,8,9,10,11,12,15,63,64],[0]),([0,1,2,3,4,54],[0,1,2,7,9,10,11,12,76,77],[0]),([0,1,2,3,4,55],[0,1,2,7,8,9,10,11,12,15,78,79],[0]),([0,1,2,3,4,12],[0,1,2,7,9,10,11,12,15,80],[0]),([0,1,2,3,4,13],[0,1,2,7,9,11,12,15,85],[0]),([0,1,2,3,4,15],[0,1,7,9,10,11,12],[0]),([0,1,2,3,4,41],[0,1,7,8,9,10,11,12,15,120],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test7_1 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket6 7 h61Block7_1 = true := by decide +kernel
def h61Block7_2 : List NodeSpec := [([0,1,2,3,4,42],[0,1,7,8,9,10,11,15,123],[0]),([0,1,2,3,4,44],[0,1,2,7,9,10,11,12,15,86],[0]),([0,1,2,3,4,45],[0,1,2,7,9,11,12,15,81],[0]),([0,1,2,3,4,16],[0,1,2,7,8,9,10,11,83,126],[0]),([0,1,2,3,4,17],[0,1,2,7,9,10,11,12,15,100,129],[0]),([0,1,2,3,4,18],[0,1,2,7,8,9,10,11,12,15,101,130],[0]),([0,1,2,3,4,19],[0,1,2,7,9,10,11,15,104,135],[0]),([0,1,2,3,4,46],[0,1,7,8,9,10,11,12,15,124],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test7_2 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket6 7 h61Block7_2 = true := by decide +kernel
def h61Block7_3 : List NodeSpec := [([0,1,2,3,4,47],[0,1,7,8,9,10,11,15,122],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test7_3 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket6 7 h61Block7_3 = true := by decide +kernel
def h61Nodes7 : List NodeSpec := h61Block7_0 ++ h61Block7_1 ++ h61Block7_2 ++ h61Block7_3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Check7 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket6 7 h61Nodes7 = true := by
  unfold h61Nodes7 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨h61Test7_0,h61Test7_1⟩,h61Test7_2⟩,h61Test7_3⟩
def h61Bucket7 : BT (List (List Nat)) := buildBucketsBT h61W h61Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h61G 7 xs.toFinset) h61Bucket7 := buildBucketsBT_sound (by decide) h61Pairs h61WOk h61PoolsOk h61AutosOk h61Bucket6Ok h61Check7
def h61Block8_0 : List NodeSpec := [([0,1,2,3,4],[0,7],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test8_0 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket7 8 h61Block8_0 = true := by decide +kernel
def h61Nodes8 : List NodeSpec := h61Block8_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Check8 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket7 8 h61Nodes8 = true := h61Test8_0
def h61Bucket8 : BT (List (List Nat)) := buildBucketsBT h61W h61Nodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h61G 8 xs.toFinset) h61Bucket8 := buildBucketsBT_sound (by decide) h61Pairs h61WOk h61PoolsOk h61AutosOk h61Bucket7Ok h61Check8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Bound : Lower h61R h61G 9 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 3,1,9),(VAR 4,1,17),(VAR 5,1,33)]) (by decide +kernel) h61Bucket8Ok (by decide +kernel)
def h63R : List Nat := varsOf 61
def h63G : Nat := 0xfffafaaafff0aaa0fffafaaafff0aaa0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h63Bound : Lower h63R h63G 7 := lift_of (z := 16) (o := 0) (essPairs := [(VAR 4,4,20)]) (by decide +kernel) h11Bound
def h64R : List Nat := varsOf 62
def h64G : Nat := 0xfffcfffcfcf0fcc0fffcfffcfcf0fcc0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h64Bound : Lower h64R h64G 8 := lift_of (z := 16) (o := 0) (essPairs := [(VAR 4,4,20)]) (by decide +kernel) h12Bound
def h0R : List Nat := varsOf 63
def h0G : Nat := 0xfee8eaa8ece0a880fee8eaa8ece0a880
def h0Pos : List Nat := [13,22,13,22,41,7,21,26,11,22,21,46,35,7,13,26,13,46,37,7,21,41,21,26,37,51,54,30,15,11,11,23,51,27,35,60,60,60,60,39,41,21,37,58,26,43,7,46,46,30,54,11,22,11,7,22,35,45,7,21,7,29,11,27,7,51,53,35,54,58]
def h0Neg : List Nat := [12,20,14,18,40,3,20,18,3,6,5,14,3,6,9,24,5,44,5,5,17,33,25,10,33,19,38,14,14,9,10,19,50,25,33,44,28,52,56,38,9,49,36,56,50,42,4,38,42,28,52,14,28,1,2,52,1,44,14,19,1,25,2,19,38,49,49,2,50,50]
def h0Mask : Nat := fullMask 70
def h0Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xfff686787f37d7575,0x6b9200306a37d5520),(0xcccccccccccccccccccccccccccccccc,0x3bd5fff887fe8abbaa,0x39cc49b081de803bac),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x153ed7c6f89d5f6e6f,0x1069ec4b81c0f2e47),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x20e22bb97a78a3c995,0x261b295a78c2c815),(0xffff0000ffff0000ffff0000ffff0000,0x36a8961a7b8ed086ca,0x36a8961a73825080ca),(0xffffffff00000000ffffffff00000000,0x3e0305adfd07261810,0x370285beed05220010)]
def h0Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(3,0,1),(0,0,2),(3,0,2),(0,0,3),(3,0,3),(0,0,5),(3,0,5),(0,1,2),(3,1,2),(0,1,3),(2,1,3),(3,1,3),(0,1,5),(3,1,5),(0,2,3),(1,1,23),(0,2,5),(2,2,6),(0,3,5),(1,6,23),(0,2,7),(2,7,23),(1,1,25),(2,7,25),(1,1,29),(1,1,27),(2,2,27),(2,7,27),(2,2,8),(1,8,23),(1,1,37),(2,2,9),(1,9,23),(1,9,25),(1,9,27),(2,2,18),(1,10,18),(2,2,20),(1,10,20),(1,11,18),(1,11,20),(2,2,21),(1,11,21),(2,2,22),(1,11,22),(1,11,27),(1,1,12),(2,2,12),(1,12,16),(1,1,13),(2,2,13),(1,13,16),(1,13,21),(1,13,22),(1,13,25),(1,1,14),(2,2,14),(1,14,16),(1,14,18),(1,14,20),(1,14,23),(1,16,27),(1,18,25),(1,20,25),(1,21,23),(1,22,23)]
def h0W : BT Decor := buildWiresBT 7 h0Base h0Steps
def h0AutoList : List (List (Nat × Nat)) := [[]]
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
def h0SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,8),some (subcubeFast 0 2,7),some (subcubeFast 0 4,9),some (subcubeFast 0 8,9),some (subcubeFast 0 12,5),some (subcubeFast 0 16,9),some (subcubeFast 0 32,9),some (subcubeFast 0 34,5),some (subcubeFast 0 36,5),some (subcubeFast 0 40,5),some (subcubeFast 1 0,8),some (subcubeFast 1 2,5),some (subcubeFast 1 4,5),some (subcubeFast 1 8,5),some (subcubeFast 1 12,4),some (subcubeFast 1 32,7),some (subcubeFast 1 34,4),some (subcubeFast 2 0,8),some (subcubeFast 2 1,5),some (subcubeFast 2 4,6),some (subcubeFast 2 8,5),some (subcubeFast 2 32,5),some (subcubeFast 4 0,7),some (subcubeFast 4 2,4),some (subcubeFast 4 32,5),some (subcubeFast 8 0,8),some (subcubeFast 8 1,5),some (subcubeFast 16 0,9),some (subcubeFast 16 1,7),some (subcubeFast 16 2,6),some (subcubeFast 20 1,4),some (subcubeFast 32 0,8),some (subcubeFast 32 1,5),some (subcubeFast 40 0,5),some (subcubeFast 40 4,4)]
def h0Slices : BT (Option (Nat × Nat)) := btOfList 6 h0SliceList
def h0Specs : List PoolSpec := [(10,[]),(17,[]),(2,[(0,0,1)]),(3,[(0,0,1)]),(27,[(0,0,1)]),(5,[(0,0,1)]),(6,[(0,0,1)]),(0,[]),(10,[(0,2,3)]),(17,[(0,2,3)]),(27,[(0,0,1),(0,2,3)]),(5,[(0,0,1),(0,2,3)]),(6,[(0,0,1),(0,2,3)]),(0,[(0,2,3)]),(1,[]),(25,[(0,0,1)]),(2,[]),(22,[]),(3,[]),(25,[]),(27,[(0,2,3)]),(5,[(0,2,3)]),(6,[(0,2,3)]),(31,[(0,2,3)]),(31,[(0,0,1)]),(2,[(0,0,1),(1,6,23)]),(3,[(0,0,1),(1,6,23)]),(27,[(0,0,1),(0,2,3),(1,6,23)]),(5,[(0,0,1),(0,2,3),(1,6,23)]),(6,[(0,0,1),(0,2,3),(1,6,23)]),(0,[(0,2,3),(1,6,23)]),(27,[]),(5,[]),(31,[]),(15,[(0,2,3)]),(6,[]),(19,[]),(4,[]),(15,[]),(3,[(0,0,1),(2,2,6)]),(27,[(0,0,1),(2,2,6)]),(5,[(0,0,1),(2,2,6)]),(6,[(0,0,1),(2,2,6)]),(0,[(2,2,6)]),(2,[(1,0,1)]),(3,[(1,0,1)]),(27,[(1,0,1)]),(5,[(1,0,1)]),(6,[(1,0,1)]),(27,[(1,0,1),(0,2,3)]),(5,[(1,0,1),(0,2,3)]),(6,[(1,0,1),(0,2,3)]),(1,[(0,2,3)]),(25,[(1,0,1)]),(31,[(1,0,1)]),(10,[(0,2,3),(2,7,23)]),(2,[(1,0,1),(2,7,23)]),(3,[(1,0,1),(2,7,23)]),(27,[(1,0,1),(0,2,3),(2,7,23)]),(5,[(1,0,1),(0,2,3),(2,7,23)]),(6,[(1,0,1),(0,2,3),(2,7,23)]),(17,[(0,2,3),(2,7,23)]),(26,[]),(10,[(0,2,5)]),(17,[(0,2,5)]),(0,[(0,2,5)]),(3,[(1,0,1),(0,2,5)]),(27,[(1,0,1),(0,2,5)]),(5,[(1,0,1),(0,2,5)]),(1,[(0,2,5)]),(25,[(0,2,5)]),(3,[(0,2,5)]),(27,[(0,2,5)]),(5,[(0,2,5)]),(10,[(0,2,5),(2,7,25)]),(2,[(1,0,1),(2,7,25)]),(3,[(1,0,1),(0,2,5),(2,7,25)]),(27,[(1,0,1),(0,2,5),(2,7,25)]),(5,[(1,0,1),(0,2,5),(2,7,25)]),(6,[(1,0,1),(2,7,25)]),(17,[(0,2,5),(2,7,25)]),(32,[]),(10,[(0,2,7)]),(3,[(1,0,1),(0,2,7)]),(27,[(1,0,1),(0,2,7)]),(5,[(1,0,1),(0,2,7)]),(6,[(1,0,1),(0,2,7)]),(17,[(0,2,7)]),(2,[(0,3,5),(1,0,1)]),(0,[(0,3,5)]),(10,[(0,3,5),(0,2,7)]),(2,[(0,3,5)]),(1,[(0,3,5)]),(25,[(1,0,1),(0,2,7)]),(10,[(0,3,5)]),(27,[(0,3,5),(1,0,1),(0,2,7)]),(27,[(0,3,5)]),(5,[(0,3,5)]),(9,[]),(24,[]),(22,[(0,3,5)]),(17,[(0,3,5)]),(2,[(1,0,1),(0,3,5)]),(27,[(1,0,1),(0,3,5)]),(5,[(1,0,1),(0,3,5)]),(30,[]),(10,[(0,3,5),(2,7,27)]),(3,[(1,0,1),(2,7,27)]),(2,[(1,0,1),(0,3,5),(2,7,27)]),(27,[(1,0,1),(0,3,5),(2,7,27)]),(5,[(1,0,1),(0,3,5),(2,7,27)]),(6,[(1,0,1),(2,7,27)]),(17,[(0,3,5),(2,7,27)]),(2,[(2,0,1)]),(3,[(2,0,1)]),(27,[(2,0,1)]),(5,[(2,0,1)]),(6,[(2,0,1)]),(27,[(2,0,1),(0,2,3)]),(5,[(2,0,1),(0,2,3)]),(6,[(2,0,1),(0,2,3)]),(25,[(2,0,1)]),(31,[(2,0,1)]),(2,[(2,0,1),(1,8,23)]),(3,[(2,0,1),(1,8,23)]),(27,[(2,0,1),(0,2,3),(1,8,23)]),(5,[(2,0,1),(0,2,3),(1,8,23)]),(6,[(2,0,1),(0,2,3),(1,8,23)]),(17,[(0,2,3),(1,8,23)]),(0,[(0,2,3),(1,8,23)]),(18,[]),(3,[(2,0,1),(2,2,8)]),(27,[(2,0,1),(2,2,8)]),(5,[(2,0,1),(2,2,8)]),(6,[(2,0,1),(2,2,8)]),(17,[(2,2,8)]),(0,[(2,2,8)]),(2,[(3,0,1)]),(3,[(3,0,1)]),(27,[(3,0,1)]),(5,[(3,0,1)]),(6,[(3,0,1)]),(27,[(3,0,1),(0,2,3)]),(5,[(3,0,1),(0,2,3)]),(6,[(3,0,1),(0,2,3)]),(2,[(3,0,1),(1,1,23)]),(3,[(3,0,1),(1,1,23)]),(27,[(3,0,1),(0,2,3),(1,1,23)]),(5,[(3,0,1),(0,2,3),(1,1,23)]),(10,[(0,2,3),(1,1,23)]),(6,[(3,0,1),(0,2,3),(1,1,23)]),(0,[(0,2,3),(1,1,23)]),(25,[(3,0,1)]),(31,[(3,0,1)]),(10,[(0,2,3),(1,9,23)]),(2,[(3,0,1),(1,9,23)]),(3,[(3,0,1),(1,9,23)]),(27,[(3,0,1),(0,2,3),(1,9,23)]),(5,[(3,0,1),(0,2,3),(1,9,23)]),(6,[(3,0,1),(0,2,3),(1,9,23)]),(11,[]),(3,[(3,0,1),(0,2,5)]),(27,[(3,0,1),(0,2,5)]),(5,[(3,0,1),(0,2,5)]),(2,[(3,0,1),(1,1,25)]),(10,[(0,2,5),(1,1,25)]),(3,[(3,0,1),(0,2,5),(1,1,25)]),(0,[(0,2,5),(1,1,25)]),(27,[(3,0,1),(0,2,5),(1,1,25)]),(5,[(3,0,1),(0,2,5),(1,1,25)]),(6,[(3,0,1),(1,1,25)]),(10,[(0,2,5),(1,9,25)]),(2,[(3,0,1),(1,9,25)]),(3,[(3,0,1),(0,2,5),(1,9,25)]),(27,[(3,0,1),(0,2,5),(1,9,25)]),(5,[(3,0,1),(0,2,5),(1,9,25)]),(6,[(3,0,1),(1,9,25)]),(10,[(2,2,9)]),(3,[(3,0,1),(2,2,9)]),(27,[(3,0,1),(2,2,9)]),(5,[(3,0,1),(2,2,9)]),(6,[(3,0,1),(2,2,9)]),(2,[(0,3,5),(3,0,1)]),(10,[(0,3,5),(2,2,9)]),(1,[(2,2,9)]),(25,[(3,0,1),(2,2,9)]),(19,[(0,3,5)]),(2,[(3,0,1),(0,3,5)]),(27,[(3,0,1),(0,3,5)]),(5,[(3,0,1),(0,3,5)]),(10,[(0,3,5),(1,1,27)]),(2,[(3,0,1),(0,3,5),(1,1,27)]),(0,[(0,3,5),(1,1,27)]),(3,[(3,0,1),(1,1,27)]),(27,[(3,0,1),(0,3,5),(1,1,27)]),(5,[(3,0,1),(0,3,5),(1,1,27)]),(6,[(3,0,1),(1,1,27)]),(10,[(0,3,5),(1,9,27)]),(3,[(3,0,1),(1,9,27)]),(2,[(3,0,1),(0,3,5),(1,9,27)]),(27,[(3,0,1),(0,3,5),(1,9,27)]),(5,[(3,0,1),(0,3,5),(1,9,27)]),(6,[(3,0,1),(1,9,27)]),(3,[(0,0,2)]),(27,[(0,0,2)]),(5,[(0,0,2)]),(6,[(0,0,2)]),(10,[(0,1,3)]),(2,[(0,1,3)]),(27,[(0,0,2),(0,1,3)]),(5,[(0,0,2),(0,1,3)]),(6,[(0,0,2),(0,1,3)]),(17,[(0,0,2)]),(27,[(0,1,3)]),(5,[(0,1,3)]),(6,[(0,1,3)]),(31,[(0,1,3)]),(31,[(0,0,2)]),(2,[(0,1,3),(1,10,18)]),(3,[(0,0,2),(1,10,18)]),(27,[(0,0,2),(0,1,3),(1,10,18)]),(5,[(0,0,2),(0,1,3),(1,10,18)]),(6,[(0,0,2),(0,1,3),(1,10,18)]),(15,[(0,1,3)]),(25,[(0,0,2)]),(10,[(3,1,3)]),(2,[(3,1,3)]),(27,[(0,0,2),(3,1,3)]),(5,[(0,0,2),(3,1,3)]),(6,[(0,0,2),(3,1,3)]),(1,[(0,0,2)]),(27,[(3,1,3)]),(5,[(3,1,3)]),(6,[(3,1,3)]),(31,[(3,1,3)]),(2,[(3,1,3),(1,10,20)]),(3,[(0,0,2),(1,10,20)]),(27,[(0,0,2),(3,1,3),(1,10,20)]),(5,[(0,0,2),(3,1,3),(1,10,20)]),(6,[(0,0,2),(3,1,3),(1,10,20)]),(17,[(0,0,2),(1,10,20)]),(15,[(3,1,3)]),(2,[(2,1,3),(1,0,1)]),(3,[(1,0,1),(0,2,7),(1,1,29)]),(10,[(2,1,3)]),(28,[(2,1,3),(1,1,29)]),(15,[(2,1,3)]),(5,[(1,0,1),(0,2,7),(1,1,29)]),(6,[(1,0,1),(0,2,7),(1,1,29)]),(29,[]),(28,[(1,1,29)]),(3,[(3,0,2)]),(27,[(3,0,2)]),(5,[(3,0,2)]),(6,[(3,0,2)]),(0,[(0,1,3)]),(27,[(3,0,2),(0,1,3)]),(5,[(3,0,2),(0,1,3)]),(6,[(3,0,2),(0,1,3)]),(17,[(3,0,2)]),(31,[(3,0,2)]),(10,[(0,1,3),(1,11,18)]),(2,[(0,1,3),(1,11,18)]),(3,[(3,0,2),(1,11,18)]),(27,[(3,0,2),(0,1,3),(1,11,18)]),(5,[(3,0,2),(0,1,3),(1,11,18)]),(6,[(3,0,2),(0,1,3),(1,11,18)]),(0,[(3,1,3)]),(27,[(3,0,2),(3,1,3)]),(5,[(3,0,2),(3,1,3)]),(6,[(3,0,2),(3,1,3)]),(1,[(3,0,2)]),(25,[(3,0,2)]),(10,[(3,1,3),(1,11,20)]),(2,[(3,1,3),(1,11,20)]),(3,[(3,0,2),(1,11,20)]),(27,[(3,0,2),(3,1,3),(1,11,20)]),(5,[(3,0,2),(3,1,3),(1,11,20)]),(6,[(3,0,2),(3,1,3),(1,11,20)]),(17,[(3,0,2),(1,11,20)]),(12,[]),(10,[(0,1,5)]),(0,[(0,1,5)]),(2,[(0,1,5)]),(3,[(3,0,2),(0,1,5)]),(27,[(3,0,2),(0,1,5)]),(5,[(3,0,2),(0,1,5)]),(3,[(0,1,5)]),(25,[(0,1,5)]),(27,[(0,1,5)]),(5,[(0,1,5)]),(10,[(0,1,5),(1,11,21)]),(2,[(0,1,5),(1,11,21)]),(3,[(3,0,2),(0,1,5),(1,11,21)]),(27,[(3,0,2),(0,1,5),(1,11,21)]),(5,[(3,0,2),(0,1,5),(1,11,21)]),(6,[(3,0,2),(1,11,21)]),(10,[(3,1,5)]),(0,[(3,1,5)]),(2,[(3,1,5)]),(3,[(3,0,2),(3,1,5)]),(27,[(3,0,2),(3,1,5)]),(5,[(3,0,2),(3,1,5)]),(3,[(3,1,5)]),(25,[(3,1,5)]),(27,[(3,1,5)]),(5,[(3,1,5)]),(10,[(3,1,5),(1,11,22)]),(2,[(3,1,5),(1,11,22)]),(3,[(3,0,2),(3,1,5),(1,11,22)]),(27,[(3,0,2),(3,1,5),(1,11,22)]),(5,[(3,0,2),(3,1,5),(1,11,22)]),(6,[(3,0,2),(1,11,22)]),(17,[(3,0,2),(1,11,22)]),(10,[(1,1,37)]),(28,[]),(10,[(0,3,5),(1,1,37)]),(2,[(0,3,5),(2,0,1)]),(3,[(2,0,1),(2,2,8),(1,1,37)]),(6,[(2,0,1),(2,2,8),(1,1,37)]),(27,[(2,0,1),(2,2,8),(1,1,37)]),(5,[(2,0,1),(2,2,8),(1,1,37)]),(15,[(1,1,37)]),(14,[]),(27,[(3,0,2),(0,3,5)]),(5,[(3,0,2),(0,3,5)]),(2,[(0,3,5),(1,1,27)]),(3,[(3,0,2),(1,1,27)]),(6,[(3,0,2),(1,1,27)]),(3,[(1,1,27)]),(27,[(0,3,5),(1,1,27)]),(5,[(0,3,5),(1,1,27)]),(6,[(1,1,27)]),(10,[(0,3,5),(1,11,27)]),(2,[(0,3,5),(1,11,27)]),(3,[(3,0,2),(1,11,27)]),(27,[(3,0,2),(0,3,5),(1,11,27)]),(5,[(3,0,2),(0,3,5),(1,11,27)]),(6,[(3,0,2),(1,11,27)]),(2,[(0,0,3)]),(27,[(0,0,3)]),(5,[(0,0,3)]),(6,[(0,0,3)]),(10,[(0,1,2)]),(3,[(0,1,2)]),(27,[(0,0,3),(0,1,2)]),(5,[(0,0,3),(0,1,2)]),(6,[(0,0,3),(0,1,2)]),(17,[(0,0,3)]),(27,[(0,1,2)]),(5,[(0,1,2)]),(6,[(0,1,2)]),(31,[(0,1,2)]),(31,[(0,0,3)]),(2,[(0,0,3),(1,12,16)]),(3,[(0,1,2),(1,12,16)]),(27,[(0,0,3),(0,1,2),(1,12,16)]),(5,[(0,0,3),(0,1,2),(1,12,16)]),(6,[(0,0,3),(0,1,2),(1,12,16)]),(15,[(0,1,2)]),(22,[(0,0,3)]),(1,[(0,0,3)]),(0,[(0,1,2)]),(10,[(3,1,2)]),(3,[(3,1,2)]),(27,[(0,0,3),(3,1,2)]),(5,[(0,0,3),(3,1,2)]),(6,[(0,0,3),(3,1,2)]),(27,[(3,1,2)]),(5,[(3,1,2)]),(6,[(3,1,2)]),(31,[(3,1,2)]),(15,[(3,1,2)]),(3,[(1,1,12)]),(2,[(0,0,3),(1,1,12)]),(27,[(0,0,3),(1,1,12)]),(5,[(0,0,3),(1,1,12)]),(6,[(0,0,3),(1,1,12)]),(3,[(2,2,12)]),(27,[(0,0,3),(2,2,12)]),(5,[(0,0,3),(2,2,12)]),(6,[(0,0,3),(2,2,12)]),(2,[(3,0,3)]),(27,[(3,0,3)]),(5,[(3,0,3)]),(6,[(3,0,3)]),(27,[(3,0,3),(0,1,2)]),(5,[(3,0,3),(0,1,2)]),(6,[(3,0,3),(0,1,2)]),(17,[(3,0,3)]),(31,[(3,0,3)]),(10,[(0,1,2),(1,13,16)]),(2,[(3,0,3),(1,13,16)]),(3,[(0,1,2),(1,13,16)]),(27,[(3,0,3),(0,1,2),(1,13,16)]),(5,[(3,0,3),(0,1,2),(1,13,16)]),(6,[(3,0,3),(0,1,2),(1,13,16)]),(0,[(3,1,2)]),(27,[(3,0,3),(3,1,2)]),(5,[(3,0,3),(3,1,2)]),(6,[(3,0,3),(3,1,2)]),(1,[(3,0,3)]),(19,[(3,0,3)]),(13,[]),(2,[(3,0,3),(0,1,5)]),(27,[(3,0,3),(0,1,5)]),(5,[(3,0,3),(0,1,5)]),(34,[]),(10,[(0,1,5),(1,13,21)]),(2,[(3,0,3),(0,1,5),(1,13,21)]),(3,[(0,1,5),(1,13,21)]),(27,[(3,0,3),(0,1,5),(1,13,21)]),(5,[(3,0,3),(0,1,5),(1,13,21)]),(6,[(3,0,3),(1,13,21)]),(2,[(3,0,3),(3,1,5)]),(27,[(3,0,3),(3,1,5)]),(5,[(3,0,3),(3,1,5)]),(10,[(3,1,5),(1,13,22)]),(2,[(3,0,3),(3,1,5),(1,13,22)]),(3,[(3,1,5),(1,13,22)]),(27,[(3,0,3),(3,1,5),(1,13,22)]),(5,[(3,0,3),(3,1,5),(1,13,22)]),(6,[(3,0,3),(1,13,22)]),(17,[(3,0,3),(1,13,22)]),(10,[(1,1,13)]),(3,[(1,1,13)]),(2,[(3,0,3),(1,1,13)]),(27,[(3,0,3),(1,1,13)]),(5,[(3,0,3),(1,1,13)]),(6,[(3,0,3),(1,1,13)]),(10,[(0,2,5),(1,1,13)]),(3,[(0,2,5),(1,1,13)]),(31,[(3,0,3),(1,1,13)]),(27,[(3,0,3),(0,2,5)]),(5,[(3,0,3),(0,2,5)]),(3,[(0,2,5),(1,1,25)]),(2,[(3,0,3),(1,1,25)]),(6,[(3,0,3),(1,1,25)]),(2,[(1,1,25)]),(27,[(0,2,5),(1,1,25)]),(5,[(0,2,5),(1,1,25)]),(6,[(1,1,25)]),(10,[(0,2,5),(1,13,25)]),(2,[(3,0,3),(1,13,25)]),(3,[(0,2,5),(1,13,25)]),(27,[(3,0,3),(0,2,5),(1,13,25)]),(5,[(3,0,3),(0,2,5),(1,13,25)]),(6,[(3,0,3),(1,13,25)]),(10,[(2,2,13)]),(3,[(2,2,13)]),(27,[(3,0,3),(2,2,13)]),(5,[(3,0,3),(2,2,13)]),(6,[(3,0,3),(2,2,13)]),(2,[(0,0,5)]),(3,[(0,0,5)]),(27,[(0,0,5)]),(5,[(0,0,5)]),(3,[(0,0,5),(0,1,2)]),(27,[(0,0,5),(0,1,2)]),(5,[(0,0,5),(0,1,2)]),(17,[(0,0,5)]),(25,[(0,1,2)]),(25,[(0,0,5)]),(2,[(0,0,5),(1,14,16)]),(3,[(0,0,5),(0,1,2),(1,14,16)]),(27,[(0,0,5),(0,1,2),(1,14,16)]),(5,[(0,0,5),(0,1,2),(1,14,16)]),(6,[(0,1,2),(1,14,16)]),(22,[(0,0,5)]),(1,[(0,0,5)]),(3,[(0,0,5),(3,1,2)]),(27,[(0,0,5),(3,1,2)]),(5,[(0,0,5),(3,1,2)]),(25,[(3,1,2)]),(19,[(0,0,5)]),(2,[(0,0,5),(0,1,3)]),(27,[(0,0,5),(0,1,3)]),(5,[(0,0,5),(0,1,3)]),(2,[(0,0,5),(0,1,3),(1,14,18)]),(3,[(0,0,5),(1,14,18)]),(27,[(0,0,5),(0,1,3),(1,14,18)]),(5,[(0,0,5),(0,1,3),(1,14,18)]),(6,[(0,1,3),(1,14,18)]),(33,[]),(2,[(0,0,5),(3,1,3)]),(27,[(0,0,5),(3,1,3)]),(5,[(0,0,5),(3,1,3)]),(2,[(0,0,5),(3,1,3),(1,14,20)]),(3,[(0,0,5),(1,14,20)]),(27,[(0,0,5),(3,1,3),(1,14,20)]),(5,[(0,0,5),(3,1,3),(1,14,20)]),(6,[(3,1,3),(1,14,20)]),(17,[(0,0,5),(1,14,20)]),(6,[(1,1,14)]),(2,[(0,0,5),(1,1,14)]),(3,[(0,0,5),(1,1,14)]),(27,[(0,0,5),(1,1,14)]),(5,[(0,0,5),(1,1,14)]),(0,[(1,1,14)]),(6,[(0,2,3),(1,1,14)]),(25,[(0,0,5),(1,1,14)]),(23,[]),(27,[(0,0,5),(0,2,3)]),(5,[(0,0,5),(0,2,3)]),(2,[(0,0,5),(1,14,23)]),(3,[(0,0,5),(1,14,23)]),(27,[(0,0,5),(0,2,3),(1,14,23)]),(5,[(0,0,5),(0,2,3),(1,14,23)]),(6,[(0,2,3),(1,14,23)]),(3,[(0,0,5),(2,2,14)]),(27,[(0,0,5),(2,2,14)]),(5,[(0,0,5),(2,2,14)]),(6,[(2,2,14)]),(2,[(3,0,5)]),(3,[(3,0,5)]),(27,[(3,0,5)]),(5,[(3,0,5)]),(3,[(3,0,5),(0,1,2)]),(27,[(3,0,5),(0,1,2)]),(5,[(3,0,5),(0,1,2)]),(17,[(3,0,5)]),(25,[(3,0,5)]),(3,[(3,0,5),(3,1,2)]),(27,[(3,0,5),(3,1,2)]),(5,[(3,0,5),(3,1,2)]),(1,[(3,0,5)]),(19,[(3,0,5)]),(2,[(3,0,5),(0,1,3)]),(27,[(3,0,5),(0,1,3)]),(5,[(3,0,5),(0,1,3)]),(2,[(3,0,5),(3,1,3)]),(27,[(3,0,5),(3,1,3)]),(5,[(3,0,5),(3,1,3)]),(27,[(3,0,5),(0,2,3)]),(5,[(3,0,5),(0,2,3)]),(16,[]),(27,[(0,1,2),(0,3,5)]),(5,[(0,1,2),(0,3,5)]),(2,[(0,3,5),(1,16,27)]),(3,[(0,1,2),(1,16,27)]),(27,[(0,1,2),(0,3,5),(1,16,27)]),(5,[(0,1,2),(0,3,5),(1,16,27)]),(6,[(0,1,2),(1,16,27)]),(15,[(0,1,2),(1,16,27)]),(27,[(3,1,2),(0,3,5)]),(5,[(3,1,2),(0,3,5)]),(27,[(0,1,3),(0,2,5)]),(5,[(0,1,3),(0,2,5)]),(2,[(0,1,3),(1,18,25)]),(3,[(0,2,5),(1,18,25)]),(27,[(0,1,3),(0,2,5),(1,18,25)]),(5,[(0,1,3),(0,2,5),(1,18,25)]),(6,[(0,1,3),(1,18,25)]),(15,[(0,1,3),(1,18,25)]),(8,[]),(3,[(2,2,18)]),(27,[(0,1,3),(2,2,18)]),(5,[(0,1,3),(2,2,18)]),(6,[(0,1,3),(2,2,18)]),(27,[(3,1,3),(0,2,5)]),(5,[(3,1,3),(0,2,5)]),(17,[(0,2,5),(1,20,25)]),(2,[(3,1,3),(1,20,25)]),(3,[(0,2,5),(1,20,25)]),(27,[(3,1,3),(0,2,5),(1,20,25)]),(5,[(3,1,3),(0,2,5),(1,20,25)]),(6,[(3,1,3),(1,20,25)]),(15,[(3,1,3),(1,20,25)]),(20,[]),(17,[(2,2,20)]),(3,[(2,2,20)]),(27,[(3,1,3),(2,2,20)]),(5,[(3,1,3),(2,2,20)]),(6,[(3,1,3),(2,2,20)]),(27,[(0,1,5),(0,2,3)]),(5,[(0,1,5),(0,2,3)]),(2,[(0,1,5),(1,21,23)]),(3,[(0,1,5),(1,21,23)]),(27,[(0,1,5),(0,2,3),(1,21,23)]),(5,[(0,1,5),(0,2,3),(1,21,23)]),(6,[(0,2,3),(1,21,23)]),(15,[(0,2,3),(1,21,23)]),(7,[]),(15,[(2,2,21)]),(3,[(0,1,5),(2,2,21)]),(27,[(0,1,5),(2,2,21)]),(5,[(0,1,5),(2,2,21)]),(6,[(2,2,21)]),(27,[(3,1,5),(0,2,3)]),(5,[(3,1,5),(0,2,3)]),(17,[(0,2,3),(1,22,23)]),(2,[(3,1,5),(1,22,23)]),(3,[(3,1,5),(1,22,23)]),(27,[(3,1,5),(0,2,3),(1,22,23)]),(5,[(3,1,5),(0,2,3),(1,22,23)]),(6,[(0,2,3),(1,22,23)]),(15,[(0,2,3),(1,22,23)]),(21,[]),(17,[(2,2,22)]),(15,[(2,2,22)]),(3,[(3,1,5),(2,2,22)]),(27,[(3,1,5),(2,2,22)]),(5,[(3,1,5),(2,2,22)]),(6,[(2,2,22)]),(2,[(1,1,23)]),(3,[(1,1,23)]),(27,[(0,2,3),(1,1,23)]),(5,[(0,2,3),(1,1,23)]),(6,[(0,2,3),(1,1,23)]),(15,[(1,1,25)]),(15,[(1,1,27)]),(15,[(2,2,27)]),(3,[(2,2,27)]),(27,[(0,3,5),(2,2,27)]),(5,[(0,3,5),(2,2,27)]),(6,[(2,2,27)])]
def h0Pools : BT (Option BoundPool) := buildPoolsBT 10 h0W h0R h0Slices h0Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice34 : Slice h0R h0G (subcubeFast 40 4) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h1Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice33 : Slice h0R h0G (subcubeFast 40 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h2Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice32 : Slice h0R h0G (subcubeFast 32 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h3Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice31 : Slice h0R h0G (subcubeFast 32 0) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h5Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice30 : Slice h0R h0G (subcubeFast 20 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h10Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice29 : Slice h0R h0G (subcubeFast 16 2) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h11Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice28 : Slice h0R h0G (subcubeFast 16 1) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h12Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice27 : Slice h0R h0G (subcubeFast 16 0) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h13Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice26 : Slice h0R h0G (subcubeFast 8 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h14Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice25 : Slice h0R h0G (subcubeFast 8 0) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h16Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice24 : Slice h0R h0G (subcubeFast 4 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h23Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice23 : Slice h0R h0G (subcubeFast 4 2) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h25Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice22 : Slice h0R h0G (subcubeFast 4 0) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h26Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice21 : Slice h0R h0G (subcubeFast 2 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h30Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice20 : Slice h0R h0G (subcubeFast 2 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h32Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice19 : Slice h0R h0G (subcubeFast 2 4) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h34Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice18 : Slice h0R h0G (subcubeFast 2 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h35Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice17 : Slice h0R h0G (subcubeFast 2 0) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h37Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice16 : Slice h0R h0G (subcubeFast 1 34) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h40Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice15 : Slice h0R h0G (subcubeFast 1 32) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h41Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice14 : Slice h0R h0G (subcubeFast 1 12) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h42Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice13 : Slice h0R h0G (subcubeFast 1 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h43Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice12 : Slice h0R h0G (subcubeFast 1 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h44Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice11 : Slice h0R h0G (subcubeFast 1 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h45Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice10 : Slice h0R h0G (subcubeFast 1 0) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h46Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice9 : Slice h0R h0G (subcubeFast 0 40) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h47Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice8 : Slice h0R h0G (subcubeFast 0 36) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h49Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice7 : Slice h0R h0G (subcubeFast 0 34) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h51Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice6 : Slice h0R h0G (subcubeFast 0 32) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h52Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice5 : Slice h0R h0G (subcubeFast 0 16) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h53Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice4 : Slice h0R h0G (subcubeFast 0 12) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h58Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice3 : Slice h0R h0G (subcubeFast 0 8) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h59Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice2 : Slice h0R h0G (subcubeFast 0 4) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h61Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice1 : Slice h0R h0G (subcubeFast 0 2) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h63Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice0 : Slice h0R h0G (subcubeFast 0 1) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h64Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h0R h0G p.1 p.2) h0Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h0R h0G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h0Slice0) (forall_cons (fun _ h => by cases h; exact h0Slice1) (forall_cons (fun _ h => by cases h; exact h0Slice2) (forall_cons (fun _ h => by cases h; exact h0Slice3) (forall_cons (fun _ h => by cases h; exact h0Slice4) (forall_cons (fun _ h => by cases h; exact h0Slice5) (forall_cons (fun _ h => by cases h; exact h0Slice6) (forall_cons (fun _ h => by cases h; exact h0Slice7) (forall_cons (fun _ h => by cases h; exact h0Slice8) (forall_cons (fun _ h => by cases h; exact h0Slice9) (forall_cons (fun _ h => by cases h; exact h0Slice10) (forall_cons (fun _ h => by cases h; exact h0Slice11) (forall_cons (fun _ h => by cases h; exact h0Slice12) (forall_cons (fun _ h => by cases h; exact h0Slice13) (forall_cons (fun _ h => by cases h; exact h0Slice14) (forall_cons (fun _ h => by cases h; exact h0Slice15) (forall_cons (fun _ h => by cases h; exact h0Slice16) (forall_cons (fun _ h => by cases h; exact h0Slice17) (forall_cons (fun _ h => by cases h; exact h0Slice18) (forall_cons (fun _ h => by cases h; exact h0Slice19) (forall_cons (fun _ h => by cases h; exact h0Slice20) (forall_cons (fun _ h => by cases h; exact h0Slice21) (forall_cons (fun _ h => by cases h; exact h0Slice22) (forall_cons (fun _ h => by cases h; exact h0Slice23) (forall_cons (fun _ h => by cases h; exact h0Slice24) (forall_cons (fun _ h => by cases h; exact h0Slice25) (forall_cons (fun _ h => by cases h; exact h0Slice26) (forall_cons (fun _ h => by cases h; exact h0Slice27) (forall_cons (fun _ h => by cases h; exact h0Slice28) (forall_cons (fun _ h => by cases h; exact h0Slice29) (forall_cons (fun _ h => by cases h; exact h0Slice30) (forall_cons (fun _ h => by cases h; exact h0Slice31) (forall_cons (fun _ h => by cases h; exact h0Slice32) (forall_cons (fun _ h => by cases h; exact h0Slice33) (forall_cons (fun _ h => by cases h; exact h0Slice34) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))))))))))))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h0R h0G c) h0Pools := buildPoolsBT_sound h0SlicesOk
def h0Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G (8 - 1) xs.toFinset) h0Empty := trivial
def h0Block8_0 : List NodeSpec := [([0,1,2,3,4,5,28],[0,7,8,9,16,18,19,25,26,27,28,29,30,31,32,33,34,35],[0]),([0,1,2,3,4,5,30],[0,1,7,13,16,18,31,32,33,35,52,53,55,56,57,58,59,60,61,62],[0]),([0,1,2,3,4,5,32],[0,1,7,16,18,19,31,32,35,54,65,69,74,75,76,77,78,79,80,81],[0]),([0,1,2,3,4,5,27,29],[7,14,17,18,19,33,35,44,62,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100],[0]),([0,1,2,3,4,5,36],[0,1,7,16,17,18,31,32,35,53,62,89,92,106,107,108,109,110,111,112],[0]),([0,1,2,3,4,5,38],[0,1,7,8,16,18,31,32,33,34,35,52,121,123,124,125,126,127,128,129],[0]),([0,2,3,4,5,9,24],[0,14,17,19,36,145,146,147,148,149,150,151],[0]),([0,1,2,3,4,5,41],[0,7,9,13,16,18,19,31,32,33,35,154,155,156,157,158,159,160],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Empty 8 h0Block8_0 = true := by decide +kernel
def h0Block8_1 : List NodeSpec := [([0,2,3,4,5,9,31],[0,14,17,33,36,164,165,166,167,168,169,170],[0]),([0,1,2,3,4,5,42],[0,7,16,18,19,31,32,33,35,64,65,160,171,172,173,174,175,176],[0]),([0,1,2,3,4,5,27,40],[1,7,17,18,19,33,35,36,89,91,94,96,97,100,101,137,177,178,179,180,181,182,183,184,185,186],[0]),([0,2,3,4,5,9,34],[0,14,19,33,160,190,191,192,193,194,195,196],[0]),([0,1,2,3,4,5,43],[0,7,16,17,18,19,31,32,35,89,101,160,197,198,199,200,201,202],[0]),([0,1,2,3,4,5,45],[0,7,16,18,19,31,32,33,35,207,212,218,219,220,221,222,223],[0]),([0,1,2,3,4,5,10,45],[0,1,7,16,203,204,205,206,207,212,217,218,219,220,221,222,224],[0]),([0,1,2,3,4,5,47],[0,1,7,16,18,31,32,33,35,225,230,235,236,237,238,239,240,241],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_1 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Empty 8 h0Block8_1 = true := by decide +kernel
def h0Block8_2 : List NodeSpec := [([0,2,3,4,5,19,33],[0,14,17,19,36,242,243,244,245,246,247,248],[0]),([0,1,2,3,4,5,48],[0,7,16,18,19,31,32,33,35,130,255,259,261,262,263,264,265,266],[0]),([0,1,2,3,4,5,49],[0,1,7,16,18,31,32,33,35,267,271,273,274,275,276,277,278,279,280],[0]),([0,1,2,3,4,5,51],[0,7,16,18,19,31,32,33,35,130,259,282,291,292,293,294,295,296],[0]),([0,1,2,3,4,5,53],[0,1,7,16,18,19,31,32,35,271,280,298,307,308,309,310,311,312,313],[0]),([0,1,2,3,4,5,27,39],[7,14,17,18,19,33,35,62,89,91,92,94,96,97,113,130,135,314,316,317,318,319,320,321],[0]),([0,1,2,3,4,5,11,34],[0,7,14,16,17,19,33,101,160,190,192,251,252,253,254,271,272,280,326,327,328,329,330,331,332],[0]),([0,1,2,3,4,5,54],[0,1,14,16,18,31,32,35,89,280,333,334,335,336,337,338],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_2 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Empty 8 h0Block8_2 = true := by decide +kernel
def h0Block8_3 : List NodeSpec := [([0,1,2,3,4,5,57],[0,7,14,16,18,31,32,33,35,343,348,354,355,356,357,358,359],[0]),([0,1,2,3,4,5,12,57],[0,1,7,18,339,340,341,342,343,348,353,354,355,356,357,358,360,361],[0]),([0,1,2,3,4,5,16,57],[0,14,16,343,344,348,349,350,351,352,354,355,356,357,358,362],[0]),([0,1,2,3,4,5,60],[0,7,14,16,18,31,32,33,35,130,362,389,391,392,393,394,395,396],[0]),([0,1,2,3,4,5,61],[0,7,16,17,18,31,32,33,35,130,282,389,408,409,410,411,412,413],[0]),([0,1,2,3,4,5,62],[0,1,7,16,17,18,31,32,35,298,401,403,417,418,419,420,421,422,423],[0]),([0,1,2,3,4,5,25,58],[7,14,16,17,19,33,35,63,65,69,71,72,73,81,130,389,424,425,426,427,428,429,430,431,432],[0]),([0,1,2,3,4,5,13,31],[0,7,14,17,18,19,33,64,160,165,167,382,383,384,385,390,401,403,435,436,437,438,439,440,441],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_3 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Empty 8 h0Block8_3 = true := by decide +kernel
def h0Block8_4 : List NodeSpec := [([0,1,2,3,4,5,63],[0,1,14,16,18,31,32,35,65,403,442,443,444,445,446,447],[0]),([0,1,2,3,4,5,66],[0,7,14,16,18,19,31,32,35,343,352,407,460,463,464,465,466,467],[0]),([0,1,2,3,4,5,14,66],[0,1,7,35,343,453,454,455,456,460,462,463,464,465,466,467,468,469],[0]),([0,1,2,3,4,5,16,66],[0,14,16,343,344,349,350,351,362,460,461,463,464,465,466,467],[0]),([0,1,2,3,4,5,67],[0,7,16,17,18,19,31,32,35,207,216,460,478,479,480,481,482,483],[0]),([0,1,2,3,4,5,68],[0,1,7,16,17,18,31,32,35,160,225,469,487,488,489,490,491,492],[0]),([0,1,2,3,4,5,23,64],[0,8,13,14,16,17,18,19,20,21,22,33,37,52,460,493,494,495,496,497,498,499,500,501],[0]),([0,1,2,3,4,5,69],[1,7,8,14,16,18,31,32,35,37,462,504,505,506,507,508],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_4 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Empty 8 h0Block8_4 = true := by decide +kernel
def h0Block8_5 : List NodeSpec := [([0,1,2,3,4,5,70],[0,7,14,16,18,19,31,32,35,98,101,538,539,540,541,542,543],[0]),([0,1,2,3,4,5,16,70],[14,16,19,101,343,344,349,350,351,362,461,538,539,540,541,542],[0]),([0,1,2,3,4,5,71],[0,7,16,18,19,31,32,33,35,64,548,549,550,551,552,553,554],[0]),([0,1,2,3,4,5,72],[0,1,7,16,18,31,32,35,69,561,562,563,564,565,566,567,568],[0]),([0,1,2,3,4,5,73],[0,7,9,16,18,19,31,32,33,35,576,577,578,579,580,581,582],[0]),([0,1,2,3,4,5,74],[0,1,7,16,18,31,32,35,52,590,591,592,593,594,595,596,597],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_5 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Empty 8 h0Block8_5 = true := by decide +kernel
def h0Nodes8 : List NodeSpec := h0Block8_0 ++ h0Block8_1 ++ h0Block8_2 ++ h0Block8_3 ++ h0Block8_4 ++ h0Block8_5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Check8 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Empty 8 h0Nodes8 = true := by
  unfold h0Nodes8 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨h0Test8_0,h0Test8_1⟩,h0Test8_2⟩,h0Test8_3⟩,h0Test8_4⟩,h0Test8_5⟩
def h0Bucket8 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 8 xs.toFinset) h0Bucket8 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0EmptyOk h0Check8
def h0Block9_0 : List NodeSpec := [([0,1,2,3,4,5,6,23],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,36,37],[0]),([0,1,2,3,4,5,26],[0,1,2,7,16,17,18,19,31,32,33,35,38,39,40,41,42,43],[0]),([0,1,2,3,4,5,7,23],[0,1,7,8,9,13,14,16,17,18,19,20,21,22,23,44,45,46,47,48,49,50,51,52,53,54,62],[0]),([0,1,2,3,4,5,7,25],[0,1,7,14,16,17,33,35,44,45,46,47,48,53,54,63,64,65,66,67,68,69,70,71,72,73,81],[0]),([0,1,2,3,4,5,29],[0,7,14,16,17,18,19,31,32,33,35,44,82,83,84,85,86,87],[0]),([0,1,2,3,4,5,7,27],[0,1,7,14,18,19,33,35,44,45,46,47,48,53,62,89,91,92,94,96,97,101,102,103,104,105],[0]),([0,1,2,3,4,5,8,23],[0,1,7,8,9,13,14,16,17,18,19,20,21,22,23,37,52,113,114,115,116,117,118,119,120,121,122,130],[0]),([0,1,2,3,4,5,37],[0,7,14,16,17,18,19,31,32,33,35,38,113,131,132,133,134,135,136],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_0 = true := by decide +kernel
def h0Block9_1 : List NodeSpec := [([0,1,2,3,4,5,9,23],[0,1,7,8,9,13,14,16,17,18,19,20,21,22,23,36,62,137,138,139,140,141,142,143,144,152,153],[0]),([0,1,2,3,4,5,9,25],[0,1,7,14,16,17,33,35,36,63,64,65,70,71,72,73,81,137,138,139,140,141,152,153,161,162,163],[0]),([0,1,2,3,4,5,40],[0,1,7,16,17,18,19,31,32,33,35,137,177,178,179,180,181],[0]),([0,1,2,3,4,5,9,27],[0,1,7,14,18,19,33,35,62,89,91,94,96,97,101,105,137,138,139,140,141,152,160,187,188,189],[0]),([0,1,2,3,4,5,10,18],[0,1,7,14,16,17,18,19,36,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217],[0]),([0,1,2,3,4,5,10,20],[0,1,7,14,16,17,18,19,160,203,204,205,206,212,217,224,225,226,227,228,229,230,231,232,233,234],[0]),([0,1,2,3,4,5,33],[0,7,14,16,18,19,31,32,33,35,38,44,87,249,250],[0]),([0,1,2,3,4,5,11,18],[0,1,7,14,16,17,18,19,36,130,207,208,213,214,215,216,251,252,253,254,255,256,257,258,259,260],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_1 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_1 = true := by decide +kernel
def h0Block9_2 : List NodeSpec := [([0,1,2,3,4,5,11,20],[0,1,7,14,16,17,18,19,62,225,226,231,232,233,234,251,252,253,254,259,260,267,268,269,270,271,272,280],[0]),([0,1,2,3,4,5,11,21],[0,1,7,14,16,17,33,35,36,130,251,252,253,254,259,272,281,282,283,284,285,286,287,288,289,290],[0]),([0,1,2,3,4,5,11,22],[0,1,7,14,16,17,33,35,81,251,252,253,254,259,260,271,272,280,297,298,299,300,301,302,303,304,305,306],[0]),([0,1,2,3,4,5,39],[0,7,14,16,18,19,31,32,33,35,113,135,314,315,322,323],[0]),([0,1,2,3,4,5,11,27],[0,7,16,17,18,19,33,35,62,89,91,94,96,97,101,251,252,253,254,259,272,280,324,325],[0]),([0,1,2,3,4,5,12,16],[0,1,7,14,16,17,18,19,339,340,341,342,343,344,345,346,347,348,349,350,351,352,353],[0]),([0,1,2,3,4,5,12,17],[0,1,7,14,16,17,18,19,36,160,339,340,341,342,348,353,361,363,364,365,366,367,368,369,370,371,372],[0]),([0,1,2,3,4,5,55],[0,7,14,16,17,18,31,32,33,35,38,348,373,374,375,376,377],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_2 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_2 = true := by decide +kernel
def h0Block9_3 : List NodeSpec := [([0,1,2,3,4,5,56],[0,1,7,14,16,17,18,31,32,33,35,38,339,378,379,380,381],[0]),([0,1,2,3,4,5,13,16],[0,1,7,14,16,17,18,19,130,343,344,349,350,351,352,362,382,383,384,385,386,387,388,389,390],[0]),([0,1,2,3,4,5,13,17],[0,1,7,14,16,17,18,19,36,363,364,368,369,370,371,382,383,384,385,389,390,397,398,399,400,401,402,403],[0]),([0,1,2,3,4,5,13,21],[0,1,7,14,18,19,33,35,105,130,281,282,283,287,289,290,382,383,384,385,389,404,405,406,407],[0]),([0,1,2,3,4,5,13,22],[0,1,7,14,18,19,33,35,81,105,297,298,299,303,305,306,382,383,384,385,389,390,401,403,407,414,415,416],[0]),([0,1,2,3,4,5,58],[0,7,14,16,17,18,31,32,33,35,389,424,425,426,427,428,429],[0]),([0,1,2,3,4,5,13,25],[0,7,16,17,18,19,33,35,63,64,65,70,71,72,73,81,382,383,384,385,389,390,403,433,434],[0]),([0,1,2,3,4,5,59],[0,1,7,14,16,17,18,31,32,33,35,382,407,448,449,450,451,452],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_3 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_3 = true := by decide +kernel
def h0Block9_4 : List NodeSpec := [([0,1,2,3,4,5,14,16],[0,1,7,14,16,17,33,35,343,344,349,350,351,352,453,454,455,456,457,458,459,460,461,462],[0]),([0,1,2,3,4,5,14,17],[0,1,7,14,16,17,33,35,36,160,363,364,368,369,370,371,453,454,455,456,460,462,469,470,471,472,473,474],[0]),([0,1,2,3,4,5,14,18],[0,1,7,14,18,19,33,35,207,208,213,214,215,216,407,453,454,455,456,460,475,476,477,483],[0]),([0,1,2,3,4,5,14,20],[0,1,7,14,18,19,33,35,160,225,226,231,232,233,234,407,453,454,455,456,460,462,469,484,485,486],[0]),([0,1,2,3,4,5,64],[0,7,14,16,17,18,19,31,32,35,460,493,494,495,496,497],[0]),([0,1,2,3,4,5,14,23],[0,7,8,9,16,17,18,19,20,21,22,33,35,37,160,453,454,455,456,460,462,483,502,503],[0]),([0,1,2,3,4,5,65],[0,1,7,14,16,17,18,19,31,32,35,407,453,509,510,511,512],[0]),([0,1,2,3,4,5,15,16],[0,1,7,14,16,17,33,35,38,343,344,349,350,351,359,362,461,513,514,515,516,517,518,519,520,521],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_4 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_4 = true := by decide +kernel
def h0Block9_5 : List NodeSpec := [([0,1,2,3,4,5,15,17],[0,1,7,14,16,17,33,35,38,363,364,368,369,370,372,397,473,513,514,515,516,520,521,522,523,524,525,526],[0]),([0,1,2,3,4,5,15,18],[0,1,7,14,18,19,33,35,38,105,207,208,213,214,215,223,255,513,514,515,516,520,527,528,529],[0]),([0,1,2,3,4,5,15,20],[0,1,7,14,18,19,33,35,38,105,225,226,231,232,233,241,267,513,514,515,516,520,521,525,530,531,532],[0]),([0,1,2,3,4,5,15,23],[0,7,8,9,13,16,17,18,19,20,21,22,33,34,35,38,513,514,515,516,520,521,533,534,535],[0]),([0,1,2,3,4,5,16,27],[1,14,16,17,18,19,33,35,89,91,94,96,97,98,101,343,344,349,350,351,352,362,461,536,537],[0]),([0,1,2,3,4,5,17,27],[1,14,16,17,18,19,33,35,36,89,91,92,94,96,97,98,101,186,363,364,368,369,370,371,372,397,473,544,545],[0]),([0,1,2,3,4,5,18,25],[1,14,16,17,18,19,33,35,36,63,64,65,71,72,73,207,208,213,214,215,216,255,546,547,554],[0]),([0,1,2,3,4,5,44],[0,1,7,16,17,18,19,31,32,33,35,105,208,407,555,556,557,558],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_5 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_5 = true := by decide +kernel
def h0Block9_6 : List NodeSpec := [([0,1,2,3,4,5,20,25],[1,14,16,17,18,19,33,35,63,64,65,69,70,71,72,73,225,226,231,232,233,234,267,554,559,560,568],[0]),([0,1,2,3,4,5,46],[0,1,7,14,16,17,18,19,31,32,33,35,105,226,407,569,570,571,572,573],[0]),([0,1,2,3,4,5,21,23],[1,8,9,13,14,16,17,18,19,20,21,22,33,35,36,37,281,282,283,287,288,289,290,574,575],[0]),([0,1,2,3,4,5,50],[0,1,7,16,17,18,19,31,32,33,35,105,283,583,584,585,586,587],[0]),([0,1,2,3,4,5,22,23],[1,8,9,13,14,16,17,18,19,20,21,22,23,33,35,37,52,297,298,299,303,304,305,306,588,589,597],[0]),([0,1,2,3,4,5,52],[0,1,7,14,16,17,18,19,31,32,33,35,105,299,598,599,600,601,602,603],[0]),([0,1,2,3,4,5,24],[0,7,9,14,16,18,19,31,32,33,35,160,535,604,605,606,607,608],[0]),([0,1,2,3,4,5,31],[0,7,14,16,18,19,31,32,33,35,64,435,438,439,440,441,609],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_6 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_6 = true := by decide +kernel
def h0Block9_7 : List NodeSpec := [([0,1,2,3,4,5,34],[0,7,14,16,17,18,19,31,32,35,101,326,329,330,331,332,610],[0]),([0,1,2,3,4,5,35],[0,1,7,14,16,17,18,19,31,32,33,35,91,105,611,612,613,614,615],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_7 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_7 = true := by decide +kernel
def h0Nodes9 : List NodeSpec := h0Block9_0 ++ h0Block9_1 ++ h0Block9_2 ++ h0Block9_3 ++ h0Block9_4 ++ h0Block9_5 ++ h0Block9_6 ++ h0Block9_7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Check9 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Nodes9 = true := by
  unfold h0Nodes9 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨h0Test9_0,h0Test9_1⟩,h0Test9_2⟩,h0Test9_3⟩,h0Test9_4⟩,h0Test9_5⟩,h0Test9_6⟩,h0Test9_7⟩
def h0Bucket9 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket9Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 9 xs.toFinset) h0Bucket9 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0Bucket8Ok h0Check9
def h0Block10_0 : List NodeSpec := [([0,1,2,3,4,5,6],[0,1,2,3,4,5,6,7,16,18,19,31,32,33,35,38],[0]),([0,1,2,3,4,5,7],[0,1,7,14,16,18,19,31,32,33,35,44,45,46,47,48],[0]),([0,1,2,3,4,5,8],[0,1,7,14,16,18,19,31,32,33,35,38,113,114,115,116,117],[0]),([0,1,2,3,4,5,9],[0,1,7,16,18,19,31,32,33,35,137,138,139,140,141],[0]),([0,1,2,3,4,5,10],[0,1,16,18,19,31,32,33,35,38,203,204,205,206],[0]),([0,1,2,3,4,5,11],[0,1,7,16,18,19,31,32,33,35,251,252,253,254],[0]),([0,1,2,3,4,5,12],[0,1,16,18,31,32,33,35,38,339,340,341,342],[0]),([0,1,2,3,4,5,13],[0,1,7,16,18,31,32,33,35,382,383,384,385],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test10_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket9 10 h0Block10_0 = true := by decide +kernel
def h0Block10_1 : List NodeSpec := [([0,1,2,3,4,5,14],[0,1,16,18,19,31,32,33,35,453,454,455,456],[0]),([0,1,2,3,4,5,15],[0,1,7,16,18,19,31,32,35,38,513,514,515,516],[0]),([0,1,2,3,4,5,16],[0,1,7,16,18,19,31,32,33,35,344,349,350,351],[0]),([0,1,2,3,4,5,17],[0,1,7,14,16,18,19,31,32,33,35,36,364,368,369,370],[0]),([0,1,2,3,4,5,18],[0,1,7,16,18,31,32,33,35,208,213,214,215],[0]),([0,1,2,3,4,5,20],[0,1,7,14,16,18,19,31,32,33,35,226,231,232,233],[0]),([0,1,2,3,4,5,21],[0,1,7,16,18,19,31,32,35,38,283,287,289,290],[0]),([0,1,2,3,4,5,22],[0,1,7,14,16,18,19,31,32,33,35,38,299,303,305,306],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test10_1 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket9 10 h0Block10_1 = true := by decide +kernel
def h0Block10_2 : List NodeSpec := [([0,1,2,3,4,5,23],[0,1,7,16,18,19,20,21,22,31,32,33,35],[0]),([0,1,2,3,4,5,25],[0,1,7,16,18,19,31,32,33,35,38,71,72,73],[0]),([0,1,2,3,4,5,27],[0,1,7,16,18,19,31,32,33,35,38,91,96,97],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test10_2 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket9 10 h0Block10_2 = true := by decide +kernel
def h0Nodes10 : List NodeSpec := h0Block10_0 ++ h0Block10_1 ++ h0Block10_2
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Check10 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket9 10 h0Nodes10 = true := by
  unfold h0Nodes10 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨h0Test10_0,h0Test10_1⟩,h0Test10_2⟩
def h0Bucket10 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes10
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket10Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 10 xs.toFinset) h0Bucket10 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0Bucket9Ok h0Check10
def h0Block11_0 : List NodeSpec := [([0,1,2,3,4,5],[16,18,31,32,35],[0])]
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
lemma h0Bound : Lower h0R h0G 12 := lower_of_forestBT (essPairs := [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11),(VAR 4,5,21),(VAR 5,3,35)]) (by decide +kernel) h0Bucket11Ok (by decide +kernel)
def wit : List PEqualNP.CircuitLowerBounds.Gate := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 1]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 1]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 5]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 7]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [9, 6]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 0]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 4]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 12]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 11]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [9, 14]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 13]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [17, 16]⟩]
def wo : Nat := 18
lemma wit_mono : PEqualNP.MetaComplexity.Monotone2 ⟨wit, wo⟩ := by simp [PEqualNP.MetaComplexity.Monotone2, wit]
set_option maxRecDepth 100000 in set_option maxHeartbeats 0 in
lemma wit_eval : ∀ r : Row, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput6 r)) = ((4276677288 * 2 ^ 32 + 3974146176) ||| ((4276677288 * 2 ^ 32 + 3974146176) <<< 64)).testBit r.val := by decide +kernel
lemma low_root : Lower (varsOf 63) ((4276677288 * 2 ^ 32 + 3974146176) ||| ((4276677288 * 2 ^ 32 + 3974146176) <<< 64)) 12 := h0Bound
end PEqualNP.Outside.L_meta_48795
theorem PEqualNP.Outside.L_meta_48795 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276677288 * 2 ^ 32 + 3974146176) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276677288 * 2 ^ 32 + 3974146176) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hcs
  exact PEqualNP.Outside.L_meta_48795.table2_of_lower (4276677288 * 2 ^ 32 + 3974146176) (by decide) (by decide) (by decide) (by decide)
    12 PEqualNP.Outside.L_meta_48795.low_root
    PEqualNP.Outside.L_meta_48795.wit PEqualNP.Outside.L_meta_48795.wo (by decide)
    PEqualNP.Outside.L_meta_48795.wit_mono PEqualNP.Outside.L_meta_48795.wit_eval s hcs
