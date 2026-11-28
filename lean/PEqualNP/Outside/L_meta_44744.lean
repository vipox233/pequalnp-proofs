import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_44744
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
def h1R : List Nat := varsOf 15
def h1G : Nat := 0xeaa8eaa8eaa8eaa8eaa8eaa8eaa8eaa8
def h1Pos : List Nat := [5,14,5,9,3,5,14,9,14,3,3,7,7]
def h1Neg : List Nat := [4,12,6,8,2,1,10,1,6,1,0,6,1]
def h1Mask : Nat := fullMask 13
def h1Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,7869,4768),(0xcccccccccccccccccccccccccccccccc,8018,2388),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,6503,2311),(0xff00ff00ff00ff00ff00ff00ff00ff00,458,74)]
def h1Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(3,0,1),(0,1,2),(1,1,2),(2,1,2),(1,2,4),(2,2,4),(0,2,5),(3,2,5),(1,3,10),(2,3,10)]
def h1W : BT Decor := buildWiresBT 5 h1Base h1Steps
def h1AutoList : List (List (Nat × Nat)) := [[],[(2,3)],[(1,2)],[(1,3)],[(2,3),(1,2)],[(2,3),(1,3)]]
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
def h1Block3_0 : List NodeSpec := nodesWithIdentity [([0,1,3,11],[]),([0,1,3,12],[]),([0,1,3,13],[]),([0,1,3,14],[]),([0,3,8,9],[]),([0,1,2,15],[]),([0,1,2,16],[])]
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
def h1Block4_0 : List NodeSpec := [([0,1,2,3,4],[],[0,1]),([0,1,2,3,5],[],[0,1]),([0,1,2,3,6],[],[0]),([0,1,2,3,7],[],[0]),([0,1,2,3,8],[],[0]),([0,1,2,3,9],[],[0]),([0,1,2,3,10],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test4_0 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket3 4 h1Block4_0 = true := by decide +kernel
def h1Nodes4 : List NodeSpec := h1Block4_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Check4 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket3 4 h1Nodes4 = true := h1Test4_0
def h1Bucket4 : BT (List (List Nat)) := buildBucketsBT h1W h1Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h1G 4 xs.toFinset) h1Bucket4 := buildBucketsBT_sound (by decide) h1Pairs h1WOk h1PoolsOk h1AutosOk h1Bucket3Ok h1Check4
def h1Block5_0 : List NodeSpec := [([0,1,2,3],[],[0,1,2,3,4,5])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test5_0 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket4 5 h1Block5_0 = true := by decide +kernel
def h1Nodes5 : List NodeSpec := h1Block5_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Check5 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket4 5 h1Nodes5 = true := h1Test5_0
def h1Bucket5 : BT (List (List Nat)) := buildBucketsBT h1W h1Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h1G 5 xs.toFinset) h1Bucket5 := buildBucketsBT_sound (by decide) h1Pairs h1WOk h1PoolsOk h1AutosOk h1Bucket4Ok h1Check5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Bound : Lower h1R h1G 6 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 3,1,9)]) (by decide +kernel) h1Bucket5Ok (by decide +kernel)
def h2R : List Nat := varsOf 23
def h2G : Nat := 0xeaeaa8a8eaeaa8a8eaeaa8a8eaeaa8a8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h2Bound : Lower h2R h2G 6 := carry_of (swaps := [(3,4)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h3R : List Nat := varsOf 27
def h3G : Nat := 0xeeaaaa88eeaaaa88eeaaaa88eeaaaa88
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Bound : Lower h3R h3G 6 := carry_of (swaps := [(3,4),(2,3)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h4R : List Nat := varsOf 28
def h4G : Nat := 0xfff0f000fff0f000fff0f000fff0f000
def h4Pos : List Nat := [20,24,12,12,24,20]
def h4Neg : List Nat := [16,16,4,8,8,4]
def h4Mask : Nat := fullMask 6
def h4Base : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,45,36),(0xff00ff00ff00ff00ff00ff00ff00ff00,30,24),(0xffff0000ffff0000ffff0000ffff0000,51,3)]
def h4Steps : List (Nat × Nat × Nat) := []
def h4W : BT Decor := buildWiresBT 2 h4Base h4Steps
def h4AutoList : List (List (Nat × Nat)) := [[],[(3,4)],[(2,3)],[(2,4)],[(3,4),(2,3)],[(3,4),(2,4)]]
def h4Autos : BT (List (Nat × Nat)) := btOfList 3 h4AutoList
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
def h4Block3_0 : List NodeSpec := nodesWithIdentity [([0,1,2],[])]
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
lemma h4Bound : Lower h4R h4G 4 := lower_of_forestBT (essPairs := [(VAR 2,8,12),(VAR 3,4,12),(VAR 4,4,20)]) (by decide +kernel) h4Bucket3Ok (by decide +kernel)
def h5R : List Nat := varsOf 29
def h5G : Nat := 0xfffafaaafffafaaafffafaaafffafaaa
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Bound : Lower h5R h5G 5 := lift_of (z := 1) (o := 0) (essPairs := [(VAR 0,0,1)]) (by decide +kernel) h4Bound
def h7R : List Nat := varsOf 30
def h7G : Nat := 0xccc0c000ccc0c000ccc0c000ccc0c000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Bound : Lower h7R h7G 5 := lift_of (z := 0) (o := 2) (essPairs := [(VAR 1,12,14)]) (by decide +kernel) h4Bound
def h6R : List Nat := varsOf 31
def h6G : Nat := 0xeeeaeaa8eeeaeaa8eeeaeaa8eeeaeaa8
def h6Pos : List Nat := [5,14,5,9,14,5,14,9,22,17,17,3,26,22,3,26,22,7,26,13,11,19,26,3,7,22,9,7,3,13,9,5,17,14,21,11,22,9,25,13,21,14,14,14,25,21,14]
def h6Neg : List Nat := [4,12,6,8,10,1,6,1,6,1,16,2,24,20,1,10,18,6,18,1,10,18,28,0,1,16,10,2,6,12,12,12,28,2,20,1,28,0,1,8,1,8,4,0,24,4,28]
def h6Mask : Nat := fullMask 47
def h6Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x31edfdba4ead,0x148010842a0),(0xcccccccccccccccccccccccccccccccc,0x4e1a1bf7f952,0x21c378954),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x6f96ab0b2177,0x6415f0422147),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x5eea645c90da,0x5291e450901a),(0xffff0000ffff0000ffff0000ffff0000,0x31550265b700,0x501502653400)]
def h6Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(3,0,1),(1,0,2),(2,0,2),(1,0,3),(1,1,2),(2,1,2),(0,1,3),(2,1,3),(0,2,3),(1,2,3),(0,0,17),(1,0,17),(2,0,17),(3,0,17),(0,1,17),(1,0,22),(3,0,22),(2,2,3),(1,2,4),(2,2,4),(1,2,5),(1,3,4),(2,3,4),(1,3,28),(3,3,28),(1,4,22),(1,4,5),(1,5,22),(1,3,35),(3,3,35),(1,1,17),(2,1,17),(3,1,17),(0,1,28),(2,1,28),(1,4,17),(3,4,17),(2,1,31),(3,5,17),(2,1,46),(2,1,32),(1,0,13),(1,3,13),(3,4,6),(1,4,13),(3,4,13),(2,6,13),(0,6,17),(1,13,55),(2,6,17),(3,2,6),(3,0,50),(3,2,50),(1,4,50),(3,4,50),(1,0,39),(1,2,39),(1,4,39),(2,4,39),(3,4,39),(2,6,39),(1,2,54),(1,3,58),(1,3,69),(3,3,69),(3,1,71),(3,4,71),(1,0,74),(2,1,74),(3,7,17),(3,3,49),(1,8,39),(1,3,42),(1,4,45),(1,4,9),(3,4,9),(0,9,11),(3,2,11),(0,3,9),(3,3,9),(1,3,85),(0,4,19),(1,4,19),(3,4,19),(3,3,91),(1,9,15),(2,9,15),(3,3,64),(1,2,87),(1,4,87),(1,4,18),(1,4,21),(0,1,29),(0,1,82),(0,29,82),(0,9,29),(3,9,29),(3,0,43),(0,1,43),(3,3,43),(3,2,29),(0,1,90),(0,1,108),(1,4,88),(3,4,88),(0,1,111),(3,10,29),(2,12,108),(1,4,95),(3,4,95),(0,12,29),(1,4,40),(3,13,29),(3,18,19),(1,4,16),(1,4,47),(3,4,23),(3,22,38)]
def h6W : BT Decor := buildWiresBT 7 h6Base h6Steps
def h6AutoList : List (List (Nat × Nat)) := [[],[(3,4)],[(2,3)],[(2,4)],[(3,4),(2,3)],[(3,4),(2,4)]]
def h6Autos : BT (List (Nat × Nat)) := btOfList 3 h6AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Pairs : goodPairs h6G h6Pos h6Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6BaseOk : ∀ x ∈ h6Base, faithful h6Pos h6Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6WOk : btAll (fun x => faithful h6Pos h6Neg x ∧ x.1 < 2^128) h6W := buildWiresBT_faithful h6BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h6G = h6G) h6Autos := btAll_ofList (autos_of (by decide +kernel))
def h6SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 2,5),some (subcubeFast 1 0,5),some (subcubeFast 1 2,4),some (subcubeFast 4 0,6),some (subcubeFast 8 0,6),some (subcubeFast 16 0,6)]
def h6Slices : BT (Option (Nat × Nat)) := btOfList 3 h6SliceList
def h6Specs : List PoolSpec := [(1,[]),(0,[]),(3,[(0,0,1)]),(4,[(0,0,1)]),(5,[(0,0,1)]),(2,[]),(0,[(1,2,5)]),(4,[]),(3,[]),(0,[(1,4,5)]),(3,[(0,0,1),(1,4,5)]),(5,[(1,2,3)]),(3,[(0,0,1),(1,3,28)]),(3,[(0,0,1),(3,5,17)]),(4,[(0,0,1),(1,2,5)]),(5,[(0,0,1),(1,2,5)]),(5,[]),(3,[(1,0,1)]),(4,[(1,0,1)]),(5,[(1,0,1)]),(1,[(2,1,2)]),(3,[(1,0,1),(3,4,6)]),(3,[(1,0,1),(0,6,17)]),(3,[(1,0,1),(2,6,17)]),(1,[(3,2,6)]),(4,[(1,0,1),(3,2,6)]),(5,[(1,0,1),(3,2,6)]),(4,[(1,0,1),(2,6,17)]),(3,[(2,0,1)]),(4,[(2,0,1)]),(5,[(2,0,1)]),(3,[(3,0,1)]),(4,[(3,0,1)]),(5,[(3,0,1)]),(0,[(1,0,13)]),(1,[(2,1,28)]),(4,[(1,0,2)]),(5,[(1,0,2)]),(1,[(0,1,28)]),(0,[(1,0,2)]),(4,[(1,0,2),(3,4,9)]),(4,[(1,0,2),(0,9,29)]),(4,[(1,0,17),(3,4,19)]),(3,[(1,0,17)]),(5,[(1,0,3),(3,2,11)]),(4,[(1,0,17)]),(3,[(3,3,9)]),(5,[(1,0,2),(3,3,9)]),(4,[(2,0,2)]),(5,[(2,0,2)]),(3,[(1,0,3)]),(4,[(3,2,11)]),(4,[(1,1,2)]),(5,[(1,1,2)]),(3,[(2,1,17)]),(4,[(2,1,2)]),(5,[(2,1,2)]),(3,[(1,0,13)]),(4,[(2,1,2),(1,4,13)]),(4,[(2,1,2),(1,4,50)]),(4,[(2,1,2),(3,13,29)]),(3,[(1,3,13)]),(5,[(2,1,2),(1,3,13)]),(4,[(2,1,17)]),(3,[(0,1,17)]),(3,[(0,0,17)]),(3,[(0,0,17),(1,4,18)]),(3,[(1,0,17),(3,4,19)]),(3,[(2,0,17)]),(3,[(3,0,17)]),(4,[(3,0,17)]),(4,[(0,1,17)]),(3,[(0,1,17),(1,1,17)]),(3,[(1,1,17)]),(3,[(2,1,17),(1,4,39)]),(3,[(3,1,17)]),(3,[(3,1,17),(1,4,40)]),(4,[(1,2,4)]),(3,[(1,3,4)]),(3,[(1,4,17)]),(4,[(1,4,17)]),(3,[(3,4,17)]),(4,[(3,4,17)])]
def h6Pools : BT (Option BoundPool) := buildPoolsBT 7 h6W h6R h6Slices h6Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Slice5 : Slice h6R h6G (subcubeFast 16 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h1Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Slice4 : Slice h6R h6G (subcubeFast 8 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h2Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Slice3 : Slice h6R h6G (subcubeFast 4 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h3Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Slice2 : Slice h6R h6G (subcubeFast 1 2) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h4Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Slice1 : Slice h6R h6G (subcubeFast 1 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h7Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Slice0 : Slice h6R h6G (subcubeFast 0 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h5Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h6R h6G p.1 p.2) h6Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h6R h6G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h6Slice0) (forall_cons (fun _ h => by cases h; exact h6Slice1) (forall_cons (fun _ h => by cases h; exact h6Slice2) (forall_cons (fun _ h => by cases h; exact h6Slice3) (forall_cons (fun _ h => by cases h; exact h6Slice4) (forall_cons (fun _ h => by cases h; exact h6Slice5) (fun _ h => (List.not_mem_nil h).elim)))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h6R h6G c) h6Pools := buildPoolsBT_sound h6SlicesOk
def h6Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h6G (3 - 1) xs.toFinset) h6Empty := trivial
def h6Block3_0 : List NodeSpec := nodesWithIdentity [([0,17,29,101],[]),([0,2,35,102],[]),([4,17,56,84],[]),([0,17,56,122],[]),([0,17,79,122],[]),([0,17,35,122],[]),([0,17,73,122],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Test3_0 : checkNodesBT h6W h6G h6Mask h6Pools h6Autos h6Empty 3 h6Block3_0 = true := by decide +kernel
def h6Nodes3 : List NodeSpec := h6Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Check3 : checkNodesBT h6W h6G h6Mask h6Pools h6Autos h6Empty 3 h6Nodes3 = true := h6Test3_0
def h6Bucket3 : BT (List (List Nat)) := buildBucketsBT h6W h6Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h6G 3 xs.toFinset) h6Bucket3 := buildBucketsBT_sound (by decide) h6Pairs h6WOk h6PoolsOk h6AutosOk h6EmptyOk h6Check3
def h6Block4_0 : List NodeSpec := nodesWithIdentity [([0,3,4,22,28],[]),([0,2,3,22,34],[]),([0,2,3,4,35],[]),([0,3,4,28,35],[]),([0,3,4,13,55],[]),([0,2,3,6,65],[]),([0,2,3,4,68],[]),([0,1,2,3,74],[]),([0,2,3,8,65],[]),([0,1,2,3,81],[]),([0,1,2,3,91],[]),([0,1,4,17,94],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Test4_0 : checkNodesBT h6W h6G h6Mask h6Pools h6Autos h6Bucket3 4 h6Block4_0 = true := by decide +kernel
def h6Block4_1 : List NodeSpec := nodesWithIdentity [([0,4,14,17,41],[]),([0,1,17,29,82],[7]),([0,1,4,17,103],[7]),([0,3,4,17,101],[]),([0,2,3,4,109],[]),([0,3,4,27,35],[]),([0,3,4,35,85],[]),([0,2,3,35,89],[]),([0,2,3,35,91],[]),([0,2,3,73,89],[]),([0,2,3,73,91],[]),([0,1,3,85,89],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Test4_1 : checkNodesBT h6W h6G h6Mask h6Pools h6Autos h6Bucket3 4 h6Block4_1 = true := by decide +kernel
def h6Block4_2 : List NodeSpec := nodesWithIdentity [([0,2,4,35,86],[]),([0,2,3,4,113],[]),([0,1,3,4,115],[]),([0,4,13,17,100],[]),([0,1,17,29,53],[7]),([0,1,4,17,120],[7]),([0,2,4,22,50],[]),([0,2,3,22,65],[]),([0,1,3,64,66],[]),([1,2,3,4,121],[]),([0,4,16,17,56],[]),([0,4,16,17,79],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Test4_2 : checkNodesBT h6W h6G h6Mask h6Pools h6Autos h6Bucket3 4 h6Block4_2 = true := by decide +kernel
def h6Block4_3 : List NodeSpec := nodesWithIdentity [([0,4,16,17,35],[]),([0,4,16,17,73],[]),([0,1,2,3,123],[]),([0,1,21,26,29],[]),([0,1,2,3,124],[]),([0,1,22,26,29],[]),([0,2,3,4,125],[]),([0,2,3,40,65],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Test4_3 : checkNodesBT h6W h6G h6Mask h6Pools h6Autos h6Bucket3 4 h6Block4_3 = true := by decide +kernel
def h6Nodes4 : List NodeSpec := h6Block4_0 ++ h6Block4_1 ++ h6Block4_2 ++ h6Block4_3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Check4 : checkNodesBT h6W h6G h6Mask h6Pools h6Autos h6Bucket3 4 h6Nodes4 = true := by
  unfold h6Nodes4 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨h6Test4_0,h6Test4_1⟩,h6Test4_2⟩,h6Test4_3⟩
def h6Bucket4 : BT (List (List Nat)) := buildBucketsBT h6W h6Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h6G 4 xs.toFinset) h6Bucket4 := buildBucketsBT_sound (by decide) h6Pairs h6WOk h6PoolsOk h6AutosOk h6Bucket3Ok h6Check4
def h6Block5_0 : List NodeSpec := [([0,2,3,4,5,22],[],[0,2]),([0,1,3,4,17,28],[6,7],[0]),([0,1,2,3,17,34],[9,10],[0]),([0,1,2,3,4,31],[12],[0]),([0,1,2,3,4,46],[7,8,13],[0]),([0,1,3,4,28,31],[6,14],[0]),([0,1,3,4,28,32],[],[0]),([0,1,2,3,4,32],[0],[0]),([0,3,4,6,13,17],[],[0]),([0,2,3,4,6,50],[],[0]),([0,2,3,4,6,39],[],[0]),([0,2,3,4,13,54],[8],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Test5_0 : checkNodesBT h6W h6G h6Mask h6Pools h6Autos h6Bucket4 5 h6Block5_0 = true := by decide +kernel
def h6Block5_1 : List NodeSpec := [([0,1,3,4,17,58],[7],[0]),([0,1,2,3,17,51],[21],[0]),([0,1,2,3,4,55],[0,7,8,22],[0,2]),([0,1,2,3,4,57],[23],[0]),([0,1,3,4,58,70],[],[0]),([0,1,3,4,57,58],[27],[0]),([0,1,2,3,4,70],[1],[0]),([0,2,3,4,7,22],[],[0]),([0,1,3,4,17,69],[7],[0]),([0,1,2,3,4,71],[1,16],[0]),([0,1,2,3,4,77],[],[0]),([0,1,3,4,25,69],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Test5_1 : checkNodesBT h6W h6G h6Mask h6Pools h6Autos h6Bucket4 5 h6Block5_1 = true := by decide +kernel
def h6Block5_2 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,72],[]),([2,3,4,8,13,49],[34]),([0,3,4,8,13,17],[]),([0,2,3,4,8,50],[]),([0,2,3,4,8,39],[0]),([0,1,3,4,17,42],[7]),([0,1,2,3,4,24],[]),([0,1,2,3,4,45],[16]),([1,2,3,4,42,49],[8]),([0,2,3,4,41,42],[8]),([0,1,3,4,25,42],[]),([0,1,2,3,4,80],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Test5_2 : checkNodesBT h6W h6G h6Mask h6Pools h6Autos h6Bucket4 5 h6Block5_2 = true := by decide +kernel
def h6Block5_3 : List NodeSpec := nodesWithIdentity [([0,1,4,9,11,17],[7,8]),([0,1,3,4,9,85],[8]),([0,1,2,3,4,19],[1,16]),([0,1,4,9,15,17],[7,8]),([0,1,3,4,9,64],[0]),([0,1,2,4,15,87],[1]),([0,1,2,3,4,37],[0]),([0,1,2,3,4,93],[1]),([0,1,2,3,4,94],[]),([0,2,3,4,14,41],[]),([0,1,3,4,17,41],[6,7]),([0,1,2,3,4,36],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Test5_3 : checkNodesBT h6W h6G h6Mask h6Pools h6Autos h6Bucket4 5 h6Block5_3 = true := by decide +kernel
def h6Block5_4 : List NodeSpec := [([1,2,3,4,9,49],[8],[0]),([1,3,4,9,17,18],[],[0]),([1,3,4,9,17,21],[],[0]),([0,1,4,9,17,29],[],[0]),([0,1,4,9,17,87],[7],[0]),([0,1,3,4,17,82],[7],[0]),([0,1,3,4,17,83],[7,40],[0]),([0,1,3,4,9,43],[0],[0]),([0,1,3,4,9,44],[],[0]),([0,1,2,3,4,103],[0,7,16,41],[0,1]),([0,1,2,3,4,90],[1],[0,1,3]),([0,1,2,3,4,92],[42],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Test5_4 : checkNodesBT h6W h6G h6Mask h6Pools h6Autos h6Bucket4 5 h6Block5_4 = true := by decide +kernel
def h6Block5_5 : List NodeSpec := [([0,1,2,3,4,104],[],[0]),([0,1,2,3,4,21],[],[0]),([1,2,3,4,19,21],[8],[0]),([0,2,3,4,35],[],[0,1,2,4]),([0,1,2,3,4,35],[],[0]),([0,2,3,4,19,35],[1],[0,2]),([0,2,3,4,19,73],[],[0]),([0,1,2,3,4,85],[],[0]),([0,1,3,4,19,85],[8,44],[0]),([0,1,2,3,19,89],[],[0,2]),([0,1,2,3,91],[],[0]),([0,1,2,3,4,91],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Test5_5 : checkNodesBT h6W h6G h6Mask h6Pools h6Autos h6Bucket4 5 h6Block5_5 = true := by decide +kernel
def h6Block5_6 : List NodeSpec := [([0,1,2,3,19,91],[16],[0]),([1,2,3,4,9,21],[8],[0]),([0,2,3,4,9,35],[],[0,2]),([0,1,2,3,9,91],[],[0]),([0,1,2,3,4,48],[],[0]),([0,1,2,3,4,97],[],[0,1]),([0,1,3,4,10,108],[],[0,3]),([0,1,2,4,29,88],[16],[0]),([0,1,2,3,4,111],[1],[0,3]),([0,1,2,3,4,114],[],[0]),([0,1,2,3,4,112],[],[0]),([0,2,3,4,12,100],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Test5_6 : checkNodesBT h6W h6G h6Mask h6Pools h6Autos h6Bucket4 5 h6Block5_6 = true := by decide +kernel
def h6Block5_7 : List NodeSpec := [([0,1,3,4,12,108],[],[0]),([0,1,2,4,29,95],[16],[0]),([0,1,2,3,4,118],[],[0]),([0,1,2,3,4,117],[8],[0]),([0,1,2,3,4,64],[],[0]),([0,1,2,3,4,39],[16],[0,3]),([0,1,2,4,30,95],[],[0]),([0,1,2,3,4,116],[],[0]),([0,1,3,4,17,49],[7],[0]),([0,1,2,3,4,78],[],[0]),([0,2,3,4,13,41],[8],[0]),([0,1,4,13,15,17],[7,8],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Test5_7 : checkNodesBT h6W h6G h6Mask h6Pools h6Autos h6Bucket4 5 h6Block5_7 = true := by decide +kernel
def h6Block5_8 : List NodeSpec := [([0,1,3,4,13,64],[8],[0]),([0,3,4,13,17,22],[],[0]),([0,3,4,13,17,40],[],[0]),([0,1,4,13,17,29],[],[0]),([0,1,4,13,17,50],[7],[0]),([0,1,3,4,17,52],[7,58],[0]),([0,1,3,4,17,53],[7],[0]),([0,1,3,4,13,43],[1],[0]),([0,1,3,4,13,44],[],[0]),([0,2,3,4,13,100],[8],[0,1]),([0,1,2,3,4,110],[],[0]),([0,1,2,3,4,61],[8,59],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Test5_8 : checkNodesBT h6W h6G h6Mask h6Pools h6Autos h6Bucket4 5 h6Block5_8 = true := by decide +kernel
def h6Block5_9 : List NodeSpec := [([0,1,2,3,4,67],[],[0,2,3]),([0,1,2,3,4,120],[1,7,16,60],[0,1]),([0,1,2,3,4,59],[],[0]),([0,1,2,4,39,50],[8,62],[0]),([0,1,2,3,4,62],[],[0,2]),([0,1,2,3,4,63],[],[0]),([0,1,2,3,4,22],[],[0]),([0,2,3,4,22,39],[8],[0,2]),([0,1,2,3,65],[],[0]),([0,1,2,3,4,65],[],[0]),([0,1,2,3,39,65],[16],[0]),([0,1,2,3,39,66],[],[0,2,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Test5_9 : checkNodesBT h6W h6G h6Mask h6Pools h6Autos h6Bucket4 5 h6Block5_9 = true := by decide +kernel
def h6Block5_10 : List NodeSpec := nodesWithIdentity [([0,2,3,4,13,22],[8,64]),([0,1,2,3,13,65],[]),([1,2,3,4,18,19],[]),([0,2,3,4,17,56],[]),([0,2,3,4,17,79],[]),([0,1,2,3,17,98],[66]),([0,2,3,4,17,35],[]),([0,2,3,4,17,73],[]),([0,1,3,4,17,85],[8]),([0,1,2,3,17,91],[67]),([1,2,3,4,20,21],[]),([0,1,3,4,17,96],[8])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Test5_10 : checkNodesBT h6W h6G h6Mask h6Pools h6Autos h6Bucket4 5 h6Block5_10 = true := by decide +kernel
def h6Block5_11 : List NodeSpec := [([0,1,2,3,4,47],[7,8,16],[0]),([0,1,3,4,21,26],[16],[0]),([0,1,2,3,4,99],[],[0]),([0,1,2,3,4,23],[7,8,16],[0]),([0,1,3,4,22,26],[16],[0,5]),([0,1,2,3,4,33],[],[0]),([0,2,3,4,22,38],[72],[0]),([0,1,3,4,17,60],[8],[0]),([0,2,3,4,39,40],[],[0]),([0,1,3,4,17,64],[8],[0,2]),([0,1,2,3,17,65],[74],[0]),([0,1,2,3,17,119],[76],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Test5_11 : checkNodesBT h6W h6G h6Mask h6Pools h6Autos h6Bucket4 5 h6Block5_11 = true := by decide +kernel
def h6Block5_12 : List NodeSpec := [([0,1,17,26,29],[7,8,16,77,78],[0,1,2,3]),([0,1,4,17,26,107],[7,8],[0]),([0,1,2,3,4,105],[],[0]),([0,1,2,3,4,106],[],[0]),([0,1,2,3,4,108],[],[0]),([0,1,3,4,43,108],[8],[0]),([0,1,3,4,17,108],[8],[0]),([0,1,2,3,4,75],[],[0]),([0,1,2,3,4,76],[],[0,3]),([0,1,2,3,4,43],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Test5_12 : checkNodesBT h6W h6G h6Mask h6Pools h6Autos h6Bucket4 5 h6Block5_12 = true := by decide +kernel
def h6Nodes5 : List NodeSpec := h6Block5_0 ++ h6Block5_1 ++ h6Block5_2 ++ h6Block5_3 ++ h6Block5_4 ++ h6Block5_5 ++ h6Block5_6 ++ h6Block5_7 ++ h6Block5_8 ++ h6Block5_9 ++ h6Block5_10 ++ h6Block5_11 ++ h6Block5_12
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Check5 : checkNodesBT h6W h6G h6Mask h6Pools h6Autos h6Bucket4 5 h6Nodes5 = true := by
  unfold h6Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h6Test5_0,h6Test5_1⟩,h6Test5_2⟩,h6Test5_3⟩,h6Test5_4⟩,h6Test5_5⟩,h6Test5_6⟩,h6Test5_7⟩,h6Test5_8⟩,h6Test5_9⟩,h6Test5_10⟩,h6Test5_11⟩,h6Test5_12⟩
def h6Bucket5 : BT (List (List Nat)) := buildBucketsBT h6W h6Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h6G 5 xs.toFinset) h6Bucket5 := buildBucketsBT_sound (by decide) h6Pairs h6WOk h6PoolsOk h6AutosOk h6Bucket4Ok h6Check5
def h6Block6_0 : List NodeSpec := [([0,1,2,3,4,5,17],[0,1,2,7,8,11],[0,2]),([0,1,3,4,28],[0,2,5,6,14,15],[0,1,3]),([0,1,2,3,4,28],[0,2,5,6,7,8,14,15,16],[0,1]),([0,2,3,4,6,13],[0,1,5,8,17,20],[0,1]),([0,1,2,3,4,6,17],[1,7,8,11,17],[0,2]),([0,1,3,4,58],[1,5,17,24,25,26],[0,1,3]),([0,1,2,3,4,58],[0,1,5,7,8,16,17,24,25,26],[0,1]),([0,1,2,3,4,7,17],[0,1,7,8,28],[0,2]),([0,1,2,3,4,69],[0,1,7,8,16],[0,1]),([0,2,3,4,8,13],[0,1,5,8,20,31],[0,1]),([0,1,2,3,4,8,17],[1,5,7,8,31],[0,2]),([0,1,2,3,4,42],[5,6,7,16,35],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Test6_0 : checkNodesBT h6W h6G h6Mask h6Pools h6Autos h6Bucket5 6 h6Block6_0 = true := by decide +kernel
def h6Block6_1 : List NodeSpec := [([0,1,2,3,4,9,11],[7,8],[0,2]),([0,1,2,3,4,9,15],[7,8],[0]),([0,1,2,3,4,41],[0,2,5,6,7,8,16,38],[0,1]),([0,1,2,3,4,9,41],[0,1,5,8,38],[0]),([0,1,2,3,4,9,42],[1,5,35],[0]),([0,1,3,4,9,17],[0,7,8,36,39],[0]),([0,1,2,3,4,9,29],[7,8,16,36],[0,1,3,4]),([0,1,2,3,4,19],[1,16,43,45],[0,1,2,4]),([0,1,2,3,4,9,19],[5,7,37,45],[0,2]),([0,1,2,3,4,87],[0,1,7,8,16,36,46,47],[0,1,2]),([0,1,2,3,4,9,87],[0,7,8,36],[0,2]),([0,1,2,3,4,10,29],[0,7,8,16,48],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Test6_1 : checkNodesBT h6W h6G h6Mask h6Pools h6Autos h6Bucket5 6 h6Block6_1 = true := by decide +kernel
def h6Block6_2 : List NodeSpec := [([0,1,2,3,4,88],[0,1,5,7,8,16,50,51],[0]),([0,1,2,3,4,12,29],[1,7,8,16,52],[0,1]),([0,1,2,3,4,95],[0,1,5,7,8,16,54],[0]),([0,1,2,3,4,49],[0,1,5,7,8,16,20,34,57],[0,1,2,5]),([0,1,2,3,4,13,49],[0,1,5,8,34],[0]),([0,1,2,3,4,13,42],[0,5,6],[0]),([0,1,2,3,4,13,15],[7,8],[0,2]),([0,1,3,4,13,17],[1,7,8,20,55],[0,2]),([0,1,2,3,4,13,29],[1,7,8,16,55],[0,1,3,4]),([0,1,2,3,4,50],[0,1,7,8,16,55,61,62],[0,1,2]),([0,1,2,3,4,13,50],[1,7,8,55],[0]),([0,1,2,3,4,39],[0,16,54,63],[0,1,2,4])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Test6_2 : checkNodesBT h6W h6G h6Mask h6Pools h6Autos h6Bucket5 6 h6Block6_2 = true := by decide +kernel
def h6Block6_3 : List NodeSpec := [([0,1,2,3,4,13,39],[7,56,63],[0]),([0,1,2,3,4,17,18],[0,7,8,11,65],[0,2]),([0,1,2,3,4,17,19],[0,11,43],[0,2]),([0,1,2,3,4,17,20],[0,68],[0,2]),([0,1,2,3,4,21],[1,7,8,16,69,70],[0,2,3]),([0,1,2,3,4,17,21],[0,7,8,69],[0,2]),([0,1,2,3,4,22],[0,7,8,16,64,71],[0,2,3]),([0,1,2,3,4,17,22],[1,7,8,64],[0,2]),([0,1,2,3,4,17,38],[1,73],[0,2]),([0,1,2,3,4,17,39],[1,11,54],[0,2]),([0,1,2,3,4,17,40],[1,7,8,11,75],[0,2]),([0,1,3,4,17,26],[7,8,11,16,77],[0,1,2,5])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Test6_3 : checkNodesBT h6W h6G h6Mask h6Pools h6Autos h6Bucket5 6 h6Block6_3 = true := by decide +kernel
def h6Block6_4 : List NodeSpec := [([0,1,2,3,4,43],[0,1,11,79,80],[0,2,3]),([0,1,2,3,4,17,43],[11,16,79],[0,2,3]),([0,1,2,3,4,44],[0,1,7,8,11,81,82],[0,2,3]),([0,1,2,3,4,17,44],[7,8,11,16,81],[0,1,3,4])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Test6_4 : checkNodesBT h6W h6G h6Mask h6Pools h6Autos h6Bucket5 6 h6Block6_4 = true := by decide +kernel
def h6Nodes6 : List NodeSpec := h6Block6_0 ++ h6Block6_1 ++ h6Block6_2 ++ h6Block6_3 ++ h6Block6_4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Check6 : checkNodesBT h6W h6G h6Mask h6Pools h6Autos h6Bucket5 6 h6Nodes6 = true := by
  unfold h6Nodes6 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨h6Test6_0,h6Test6_1⟩,h6Test6_2⟩,h6Test6_3⟩,h6Test6_4⟩
def h6Bucket6 : BT (List (List Nat)) := buildBucketsBT h6W h6Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h6G 6 xs.toFinset) h6Bucket6 := buildBucketsBT_sound (by decide) h6Pairs h6WOk h6PoolsOk h6AutosOk h6Bucket5Ok h6Check6
def h6Block7_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,4,5,7,8,16],[0,1,2,3]),([0,1,2,3,4,6],[0,1,5,7,8,16,17,18,19],[0,1,2,3]),([0,1,2,3,4,7],[0,1,7,8,16,28,29,30],[0,1,2,3]),([0,1,2,3,4,8],[0,1,5,7,8,16,31,32,33],[0,1,2,3]),([0,1,2,3,4,9],[0,1,5,7,8,16,36,37],[0,1]),([0,1,2,3,4,10],[0,1,5,7,8,16,48,49],[0,1]),([0,1,2,3,4,12],[0,1,5,7,8,16,52,53],[0,1]),([0,1,2,3,4,13],[0,1,5,7,8,16,55,56],[0,1,2,5]),([0,1,2,3,4,17],[0,1,7,8,11,16],[0,2,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Test7_0 : checkNodesBT h6W h6G h6Mask h6Pools h6Autos h6Bucket6 7 h6Block7_0 = true := by decide +kernel
def h6Nodes7 : List NodeSpec := h6Block7_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Check7 : checkNodesBT h6W h6G h6Mask h6Pools h6Autos h6Bucket6 7 h6Nodes7 = true := h6Test7_0
def h6Bucket7 : BT (List (List Nat)) := buildBucketsBT h6W h6Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h6G 7 xs.toFinset) h6Bucket7 := buildBucketsBT_sound (by decide) h6Pairs h6WOk h6PoolsOk h6AutosOk h6Bucket6Ok h6Check7
def h6Block8_0 : List NodeSpec := [([0,1,2,3,4],[7,8,16],[0,1,2,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Test8_0 : checkNodesBT h6W h6G h6Mask h6Pools h6Autos h6Bucket7 8 h6Block8_0 = true := by decide +kernel
def h6Nodes8 : List NodeSpec := h6Block8_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Check8 : checkNodesBT h6W h6G h6Mask h6Pools h6Autos h6Bucket7 8 h6Nodes8 = true := h6Test8_0
def h6Bucket8 : BT (List (List Nat)) := buildBucketsBT h6W h6Nodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h6G 8 xs.toFinset) h6Bucket8 := buildBucketsBT_sound (by decide) h6Pairs h6WOk h6PoolsOk h6AutosOk h6Bucket7Ok h6Check8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Bound : Lower h6R h6G 9 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 3,1,9),(VAR 4,1,17)]) (by decide +kernel) h6Bucket8Ok (by decide +kernel)
def h8R : List Nat := varsOf 7
def h8G : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8Bound : Lower h8R h8G 4 := carry_of (swaps := [(1,2),(2,3),(3,4),(0,1),(1,2),(2,3)]) (roots2 := h4R) (T2 := h4G) (by decide +kernel) h4Bound
def h9R : List Nat := varsOf 39
def h9G : Nat := 0xe8e8e8e8a8a8a8a8e8e8e8e8a8a8a8a8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Bound : Lower h9R h9G 5 := lift_of (z := 0) (o := 32) (essPairs := [(VAR 5,6,38)]) (by decide +kernel) h8Bound
def h10R : List Nat := varsOf 11
def h10G : Nat := 0xee88ee88ee88ee88ee88ee88ee88ee88
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h10Bound : Lower h10R h10G 4 := carry_of (swaps := [(1,2),(2,3),(3,4),(0,1),(1,2)]) (roots2 := h4R) (T2 := h4G) (by decide +kernel) h4Bound
def h11R : List Nat := varsOf 43
def h11G : Nat := 0xee88ee88aa88aa88ee88ee88aa88aa88
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Bound : Lower h11R h11G 5 := carry_of (swaps := [(2,3)]) (roots2 := h9R) (T2 := h9G) (by decide +kernel) h9Bound
def h12R : List Nat := varsOf 44
def h12G : Nat := 0xfff0fff0f000f000fff0fff0f000f000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h12Bound : Lower h12R h12G 4 := carry_of (swaps := [(4,5)]) (roots2 := h4R) (T2 := h4G) (by decide +kernel) h4Bound
def h13R : List Nat := varsOf 46
def h13G : Nat := 0xccc0ccc0c000c000ccc0ccc0c000c000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13Bound : Lower h13R h13G 5 := carry_of (swaps := [(4,5)]) (roots2 := h7R) (T2 := h7G) (by decide +kernel) h7Bound
def h14R : List Nat := varsOf 15
def h14G : Nat := 0xeee8eee8eee8eee8eee8eee8eee8eee8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14Bound : Lower h14R h14G 5 := lift_of (z := 4) (o := 0) (essPairs := [(VAR 2,1,5)]) (by decide +kernel) h10Bound
def h15R : List Nat := varsOf 45
def h15G : Nat := 0xfffafffafaaafaaafffafffafaaafaaa
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Bound : Lower h15R h15G 5 := carry_of (swaps := [(4,5)]) (roots2 := h5R) (T2 := h5G) (by decide +kernel) h5Bound
def h16R : List Nat := varsOf 47
def h16G : Nat := 0xeee8eee8eaa8eaa8eee8eee8eaa8eaa8
def h16Pos : List Nat := [5,14,3,3,14,5,7,3,14,9,13,38,37,35,42,42,37,41,42,38,35,41,7,38]
def h16Neg : List Nat := [4,12,1,2,10,1,6,6,6,1,12,6,36,33,40,10,33,33,34,34,34,40,1,36]
def h16Mask : Nat := fullMask 24
def h16Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x7336ed,0x432224),(0xcccccccccccccccccccccccccccccccc,0xdce9de,0x1c89d8),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xc91d73,0x801dc3),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x26c712,0x20c412),(0xffffffff00000000ffffffff00000000,0xbff800,0xbf7000)]
def h16Steps : List (Nat × Nat × Nat) := [(1,0,2),(1,0,4),(2,1,2),(2,1,4),(1,2,3),(1,0,9),(3,0,9),(0,1,9),(2,1,9),(3,3,5),(0,1,10),(1,3,7)]
def h16W : BT Decor := buildWiresBT 5 h16Base h16Steps
def h16AutoList : List (List (Nat × Nat)) := [[],[(2,3)]]
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
def h16SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 2,5),some (subcubeFast 0 32,5),some (subcubeFast 1 0,5),some (subcubeFast 1 2,4),some (subcubeFast 4 0,5),some (subcubeFast 4 32,4),some (subcubeFast 8 0,5),some (subcubeFast 32 0,6)]
def h16Slices : BT (Option (Nat × Nat)) := btOfList 3 h16SliceList
def h16Specs : List PoolSpec := [(2,[]),(0,[]),(3,[]),(4,[]),(7,[(1,0,2)]),(0,[(1,0,2)]),(6,[]),(7,[]),(1,[]),(4,[(1,0,4)]),(0,[(1,0,4)]),(6,[(1,0,4)]),(5,[]),(2,[(2,1,2)]),(7,[(2,1,2)]),(2,[(2,1,4)]),(4,[(2,1,4)]),(6,[(2,1,4)]),(7,[(1,2,3)])]
def h16Pools : BT (Option BoundPool) := buildPoolsBT 5 h16W h16R h16Slices h16Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Slice7 : Slice h16R h16G (subcubeFast 32 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h1Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Slice6 : Slice h16R h16G (subcubeFast 8 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h9Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Slice5 : Slice h16R h16G (subcubeFast 4 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h10Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Slice4 : Slice h16R h16G (subcubeFast 4 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h11Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Slice3 : Slice h16R h16G (subcubeFast 1 2) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h12Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Slice2 : Slice h16R h16G (subcubeFast 1 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h13Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Slice1 : Slice h16R h16G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h14Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Slice0 : Slice h16R h16G (subcubeFast 0 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h15Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h16R h16G p.1 p.2) h16Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h16R h16G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h16Slice0) (forall_cons (fun _ h => by cases h; exact h16Slice1) (forall_cons (fun _ h => by cases h; exact h16Slice2) (forall_cons (fun _ h => by cases h; exact h16Slice3) (forall_cons (fun _ h => by cases h; exact h16Slice4) (forall_cons (fun _ h => by cases h; exact h16Slice5) (forall_cons (fun _ h => by cases h; exact h16Slice6) (forall_cons (fun _ h => by cases h; exact h16Slice7) (fun _ h => (List.not_mem_nil h).elim)))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h16R h16G c) h16Pools := buildPoolsBT_sound h16SlicesOk
def h16Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h16G (4 - 1) xs.toFinset) h16Empty := trivial
def h16Block4_0 : List NodeSpec := nodesWithIdentity [([0,2,3,4,15],[])]
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
def h16Block5_0 : List NodeSpec := nodesWithIdentity [([0,1,3,4,5,9],[0,6]),([0,1,2,3,4,10],[1,7,8]),([0,1,2,3,4,14],[]),([0,1,3,4,7,9],[1,6]),([0,1,2,3,4,16],[]),([0,1,2,3,4,13],[7,8]),([0,1,2,3,4,11],[7,8]),([0,1,2,3,4,12],[7,8])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Test5_0 : checkNodesBT h16W h16G h16Mask h16Pools h16Autos h16Bucket4 5 h16Block5_0 = true := by decide +kernel
def h16Nodes5 : List NodeSpec := h16Block5_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Check5 : checkNodesBT h16W h16G h16Mask h16Pools h16Autos h16Bucket4 5 h16Nodes5 = true := h16Test5_0
def h16Bucket5 : BT (List (List Nat)) := buildBucketsBT h16W h16Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h16G 5 xs.toFinset) h16Bucket5 := buildBucketsBT_sound (by decide) h16Pairs h16WOk h16PoolsOk h16AutosOk h16Bucket4Ok h16Check5
def h16Block6_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,4,5,6,7,8],[0]),([0,1,2,3,6],[0,2,7,8,9,10,11,12],[0]),([0,1,2,3,4,7],[0,1,2,3,6,7,8,13,14],[0]),([0,1,2,3,8],[1,2,7,8,12,15,16,17],[0]),([0,1,2,3,4,9],[0,1,3,6,7,8,12,18],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Test6_0 : checkNodesBT h16W h16G h16Mask h16Pools h16Autos h16Bucket5 6 h16Block6_0 = true := by decide +kernel
def h16Nodes6 : List NodeSpec := h16Block6_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Check6 : checkNodesBT h16W h16G h16Mask h16Pools h16Autos h16Bucket5 6 h16Nodes6 = true := h16Test6_0
def h16Bucket6 : BT (List (List Nat)) := buildBucketsBT h16W h16Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h16G 6 xs.toFinset) h16Bucket6 := buildBucketsBT_sound (by decide) h16Pairs h16WOk h16PoolsOk h16AutosOk h16Bucket5Ok h16Check6
def h16Block7_0 : List NodeSpec := [([0,1,2,3,4],[0,1,2,3,6,7],[0,1])]
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
lemma h16Bound : Lower h16R h16G 8 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 3,1,9),(VAR 5,6,38)]) (by decide +kernel) h16Bucket7Ok (by decide +kernel)
def h17R : List Nat := varsOf 19
def h17G : Nat := 0xeeee8888eeee8888eeee8888eeee8888
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h17Bound : Lower h17R h17G 4 := carry_of (swaps := [(1,2),(2,3),(0,1),(1,2)]) (roots2 := h4R) (T2 := h4G) (by decide +kernel) h4Bound
def h18R : List Nat := varsOf 51
def h18G : Nat := 0xeeee8888aaaa8888eeee8888aaaa8888
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18Bound : Lower h18R h18G 5 := carry_of (swaps := [(2,3),(3,4)]) (roots2 := h9R) (T2 := h9G) (by decide +kernel) h9Bound
def h19R : List Nat := varsOf 52
def h19G : Nat := 0xfffff0f0f0f00000fffff0f0f0f00000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h19Bound : Lower h19R h19G 4 := carry_of (swaps := [(4,5),(3,4)]) (roots2 := h4R) (T2 := h4G) (by decide +kernel) h4Bound
def h20R : List Nat := varsOf 54
def h20G : Nat := 0xccccc0c0c0c00000ccccc0c0c0c00000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h20Bound : Lower h20R h20G 5 := carry_of (swaps := [(4,5),(3,4)]) (roots2 := h7R) (T2 := h7G) (by decide +kernel) h7Bound
def h21R : List Nat := varsOf 53
def h21G : Nat := 0xfffffafafafaaaaafffffafafafaaaaa
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Bound : Lower h21R h21G 5 := carry_of (swaps := [(4,5),(3,4)]) (roots2 := h5R) (T2 := h5G) (by decide +kernel) h5Bound
def h22R : List Nat := varsOf 55
def h22G : Nat := 0xeeeee8e8eaeaa8a8eeeee8e8eaeaa8a8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Bound : Lower h22R h22G 8 := carry_of (swaps := [(3,4)]) (roots2 := h16R) (T2 := h16G) (by decide +kernel) h16Bound
def h23R : List Nat := varsOf 56
def h23G : Nat := 0xffffff00ff000000ffffff00ff000000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h23Bound : Lower h23R h23G 4 := carry_of (swaps := [(4,5),(3,4),(2,3)]) (roots2 := h4R) (T2 := h4G) (by decide +kernel) h4Bound
def h24R : List Nat := varsOf 58
def h24G : Nat := 0xcccccc00cc000000cccccc00cc000000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h24Bound : Lower h24R h24G 5 := carry_of (swaps := [(4,5),(3,4),(2,3)]) (roots2 := h7R) (T2 := h7G) (by decide +kernel) h7Bound
def h25R : List Nat := varsOf 57
def h25G : Nat := 0xffffffaaffaaaaaaffffffaaffaaaaaa
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h25Bound : Lower h25R h25G 5 := carry_of (swaps := [(4,5),(3,4),(2,3)]) (roots2 := h5R) (T2 := h5G) (by decide +kernel) h5Bound
def h26R : List Nat := varsOf 59
def h26G : Nat := 0xeeeeee88eeaaaa88eeeeee88eeaaaa88
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Bound : Lower h26R h26G 8 := carry_of (swaps := [(3,4),(2,3)]) (roots2 := h16R) (T2 := h16G) (by decide +kernel) h16Bound
def h27R : List Nat := varsOf 29
def h27G : Nat := 0xfaaaaaa0faaaaaa0faaaaaa0faaaaaa0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27Bound : Lower h27R h27G 6 := carry_of (swaps := [(3,4),(2,3),(1,2)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
namespace Cofactor12086
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

def G_28 : Nat := 0xfe80fe80fe80fe80fe80fe80fe80fe80
def R_28 : List Nat := varsOf 15
lemma low_28_ok : carryOK [(3,4)] R_28 G_28 R_16 G_16 = true := by decide +kernel
lemma low_28 : Lower R_28 G_28 6 := carry_of low_28_ok low_16

def G_40 : Nat := 0xfe80fe80fe00fe00fe80fe80fe00fe00
def R_40 : List Nat := varsOf 47
lemma low_40_ok : liftCheck 0 32 R_40 G_40 R_28 G_28 [(VAR 5,39,7)] = true := by decide +kernel
lemma low_40 : Lower R_40 G_40 7 := lift_of low_40_ok low_28

end Cofactor12086
def h28R : List Nat := varsOf 61
def h28G : Nat := 0xfaaaaaa0aaaaaaa0faaaaaa0aaaaaaa0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h28Bound : Lower h28R h28G 7 := carry_of (swaps := [(2,3),(3,4),(1,2),(2,3),(0,1),(1,2)]) (roots2 := Cofactor12086.R_40) (T2 := Cofactor12086.G_40) (by decide +kernel) Cofactor12086.low_40
def h29R : List Nat := varsOf 30
def h29G : Nat := 0xfcccccc0fcccccc0fcccccc0fcccccc0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Bound : Lower h29R h29G 6 := carry_of (swaps := [(3,4),(2,3),(1,2),(0,1)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h30R : List Nat := varsOf 46
def h30G : Nat := 0xfcccfcccccc0ccc0fcccfcccccc0ccc0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h30Bound : Lower h30R h30G 6 := carry_of (swaps := [(3,4),(4,5),(2,3),(1,2),(0,1)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h31R : List Nat := varsOf 54
def h31G : Nat := 0xfcfcccccccccc0c0fcfcccccccccc0c0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Bound : Lower h31R h31G 6 := carry_of (swaps := [(3,4),(4,5),(2,3),(3,4),(1,2),(0,1)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h32R : List Nat := varsOf 58
def h32G : Nat := 0xffcccccccccccc00ffcccccccccccc00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h32Bound : Lower h32R h32G 6 := carry_of (swaps := [(3,4),(4,5),(2,3),(3,4),(1,2),(2,3),(0,1)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
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
def h33R : List Nat := varsOf 60
def h33G : Nat := 0xfffffff0fff0f000fffffff0fff0f000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Bound : Lower h33R h33G 7 := carry_of (swaps := [(4,5),(2,3),(3,4),(1,2),(2,3),(0,1),(1,2)]) (roots2 := Cofactor12086.R_17) (T2 := Cofactor12086.G_17) (by decide +kernel) Cofactor12086.low_17
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
def nodes_42_6 : List NodeSpec := nodesWithIdentity [([5,0,1,2,6,3,4],[0,1,2,3,4,5,6,7,8])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_42_6 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_5 6 nodes_42_6 = true := by decide +kernel
def bk_42_6 : BT (List (List Nat)) := buildBucketsBT W_42 nodes_42_6
set_option maxRecDepth 500000 in
lemma bk_42_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_42 6 xs.toFinset) bk_42_6 :=
  buildBucketsBT_sound (by decide) gp_42 W_42_ok P_42_ok autos_42_ok bk_42_5_ok chk_42_6
def nodes_42_7 : List NodeSpec := nodesWithIdentity [([5,0,1,2,3,4],[7,9,0,10,11,2,3,4,1,8,12])]
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
def h34R : List Nat := varsOf 62
def h34G : Nat := 0xfcccccc0ccc0c000fcccccc0ccc0c000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34Bound : Lower h34R h34G 9 := carry_of (swaps := [(2,3),(1,2)]) (roots2 := Cofactor12058.R_42) (T2 := Cofactor12058.G_42) (by decide +kernel) Cofactor12058.low_42
def h36R : List Nat := varsOf 23
def h36G : Nat := 0xeeeee8e8eeeee8e8eeeee8e8eeeee8e8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h36Bound : Lower h36R h36G 5 := carry_of (swaps := [(3,4)]) (roots2 := h14R) (T2 := h14G) (by decide +kernel) h14Bound
def h37R : List Nat := varsOf 27
def h37G : Nat := 0xeeeeee88eeeeee88eeeeee88eeeeee88
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Bound : Lower h37R h37G 5 := carry_of (swaps := [(3,4),(2,3)]) (roots2 := h14R) (T2 := h14G) (by decide +kernel) h14Bound
def h35R : List Nat := varsOf 31
def h35G : Nat := 0xfeeeeee8feeeeee8feeeeee8feeeeee8
def h35Pos : List Nat := [5,6,3,3,6,5,9,17,28,28,13,10,18,9,18,28,21,9,3,17,10,14,5,14,17,18,13,14,3,5,22,6,7,6,11]
def h35Neg : List Nat := [4,4,1,2,2,1,1,1,12,20,12,2,2,8,20,24,20,12,4,20,8,2,12,12,16,16,4,4,0,0,20,0,4,12,2]
def h35Mask : Nat := fullMask 35
def h35Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x5354f24ed,228),(0xcccccccccccccccccccccccccccccccc,0x7dab4581e,0x400201818),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x3ece18733,0x34ccf4703),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x40cb2af40,0x200d2a500),(0xffff0000ffff0000ffff0000ffff0000,0x4309d380,0x4309c200)]
def h35Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(1,0,2),(1,1,2),(1,3,4),(3,3,6),(1,3,8),(3,3,12),(1,4,12),(3,4,12),(1,6,9),(3,6,9),(1,6,12),(1,4,13),(3,4,13),(1,6,13),(0,8,9),(0,2,3),(1,2,3),(2,2,3),(0,2,6),(3,2,6),(3,1,2),(1,1,3),(1,4,24),(2,6,24),(0,8,29),(1,6,32),(2,8,29),(3,3,29),(3,1,8),(1,3,36),(1,1,25),(1,4,25),(2,4,25),(2,6,25),(2,8,25),(1,3,26),(2,3,26),(1,3,27),(3,1,12),(3,2,12),(1,13,35),(1,1,13),(3,0,2),(1,0,23),(3,1,51),(3,4,33),(2,6,23),(1,23,27),(0,3,55),(3,0,16),(3,4,16),(3,2,18),(3,4,18),(1,0,25),(3,1,61),(2,16,26),(1,1,57),(1,4,5),(1,5,56),(3,5,48),(1,0,17),(3,4,45),(2,8,28),(3,0,30),(3,1,14)]
def h35W : BT Decor := buildWiresBT 7 h35Base h35Steps
def h35AutoList : List (List (Nat × Nat)) := [[],[(3,4)],[(2,3)],[(2,4)],[(0,1)],[(3,4),(2,3)],[(3,4),(2,4)],[(3,4),(0,1)],[(2,3),(0,1)],[(2,4),(0,1)],[(3,4),(2,3),(0,1)],[(3,4),(2,4),(0,1)]]
def h35Autos : BT (List (Nat × Nat)) := btOfList 4 h35AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Pairs : goodPairs h35G h35Pos h35Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35BaseOk : ∀ x ∈ h35Base, faithful h35Pos h35Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35WOk : btAll (fun x => faithful h35Pos h35Neg x ∧ x.1 < 2^128) h35W := buildWiresBT_faithful h35BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h35G = h35G) h35Autos := btAll_ofList (autos_of (by decide +kernel))
def h35SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 1 0,6),some (subcubeFast 2 0,6),some (subcubeFast 4 0,5),some (subcubeFast 8 0,5),some (subcubeFast 12 0,4),some (subcubeFast 16 0,5),some (subcubeFast 20 0,4),some (subcubeFast 24 0,4)]
def h35Slices : BT (Option (Nat × Nat)) := btOfList 3 h35SliceList
def h35Specs : List PoolSpec := [(0,[]),(1,[]),(1,[(1,0,2)]),(2,[]),(0,[(1,1,2)]),(0,[(0,2,3)]),(4,[]),(0,[(0,2,3),(1,2,3)]),(5,[(1,2,3)]),(3,[]),(5,[]),(0,[(1,2,3)]),(0,[(2,2,3)]),(5,[(2,2,3)]),(3,[(1,4,25)]),(6,[]),(0,[(2,2,3),(1,4,25)]),(0,[(2,2,3),(2,4,25)]),(3,[(2,4,25)]),(0,[(0,2,6)]),(0,[(0,2,6),(1,3,26)]),(0,[(0,2,6),(2,3,26)]),(7,[]),(1,[(3,6,9)]),(0,[(3,2,6)]),(1,[(3,2,6)]),(0,[(3,1,2)]),(1,[(1,6,9)]),(0,[(3,1,8)]),(3,[(1,4,24)]),(0,[(1,3,8)]),(1,[(3,0,2)]),(1,[(0,2,3)]),(0,[(1,2,3),(0,2,3)]),(1,[(0,2,3),(1,2,3)]),(1,[(1,2,3)]),(2,[(1,4,24)]),(1,[(2,2,3)]),(1,[(2,2,3),(1,4,25)]),(1,[(2,2,3),(2,4,25)])]
def h35Pools : BT (Option BoundPool) := buildPoolsBT 6 h35W h35R h35Slices h35Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Slice7 : Slice h35R h35G (subcubeFast 24 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h8Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Slice6 : Slice h35R h35G (subcubeFast 20 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h10Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Slice5 : Slice h35R h35G (subcubeFast 16 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h14Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Slice4 : Slice h35R h35G (subcubeFast 12 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h17Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Slice3 : Slice h35R h35G (subcubeFast 8 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h36Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Slice2 : Slice h35R h35G (subcubeFast 4 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h37Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Slice1 : Slice h35R h35G (subcubeFast 2 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h27Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Slice0 : Slice h35R h35G (subcubeFast 1 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h29Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h35R h35G p.1 p.2) h35Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h35R h35G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h35Slice0) (forall_cons (fun _ h => by cases h; exact h35Slice1) (forall_cons (fun _ h => by cases h; exact h35Slice2) (forall_cons (fun _ h => by cases h; exact h35Slice3) (forall_cons (fun _ h => by cases h; exact h35Slice4) (forall_cons (fun _ h => by cases h; exact h35Slice5) (forall_cons (fun _ h => by cases h; exact h35Slice6) (forall_cons (fun _ h => by cases h; exact h35Slice7) (fun _ h => (List.not_mem_nil h).elim)))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h35R h35G c) h35Pools := buildPoolsBT_sound h35SlicesOk
def h35Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h35G (3 - 1) xs.toFinset) h35Empty := trivial
def h35Block3_0 : List NodeSpec := nodesWithIdentity [([4,6,24,32],[]),([4,6,22,56],[]),([2,6,56,65],[]),([2,4,6,66],[]),([4,6,22,48],[]),([2,6,48,65],[]),([2,4,6,67],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Test3_0 : checkNodesBT h35W h35G h35Mask h35Pools h35Autos h35Empty 3 h35Block3_0 = true := by decide +kernel
def h35Nodes3 : List NodeSpec := h35Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Check3 : checkNodesBT h35W h35G h35Mask h35Pools h35Autos h35Empty 3 h35Nodes3 = true := h35Test3_0
def h35Bucket3 : BT (List (List Nat)) := buildBucketsBT h35W h35Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h35G 3 xs.toFinset) h35Bucket3 := buildBucketsBT_sound (by decide) h35Pairs h35WOk h35PoolsOk h35AutosOk h35EmptyOk h35Check3
def h35Block4_0 : List NodeSpec := nodesWithIdentity [([3,4,6,9,12],[1]),([3,4,6,9,13],[]),([4,6,8,24,29],[]),([2,3,4,6,32],[0,1]),([3,4,6,8,38],[]),([1,3,6,8,39],[]),([1,4,6,8,43],[]),([2,4,6,13,35],[]),([1,4,6,24,51],[6]),([0,1,4,24,33],[6,8]),([0,1,4,23,31],[]),([0,1,3,4,55],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Test4_0 : checkNodesBT h35W h35G h35Mask h35Pools h35Autos h35Bucket3 4 h35Block4_0 = true := by decide +kernel
def h35Block4_1 : List NodeSpec := nodesWithIdentity [([0,1,2,3,53],[]),([0,1,3,4,59],[]),([0,1,2,3,60],[]),([0,1,3,16,39],[14,15]),([0,1,2,11,40],[]),([0,1,4,16,43],[6,15]),([0,1,3,4,63],[]),([0,1,4,27,56],[]),([0,1,2,56,58],[]),([0,1,2,48,58],[]),([2,4,5,6,56],[]),([2,4,5,6,48],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Test4_1 : checkNodesBT h35W h35G h35Mask h35Pools h35Autos h35Bucket3 4 h35Block4_1 = true := by decide +kernel
def h35Block4_2 : List NodeSpec := nodesWithIdentity [([0,1,2,3,69],[]),([0,1,4,24,32],[]),([0,1,3,36,39],[]),([0,2,3,4,72],[]),([0,1,4,24,52],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Test4_2 : checkNodesBT h35W h35G h35Mask h35Pools h35Autos h35Bucket3 4 h35Block4_2 = true := by decide +kernel
def h35Nodes4 : List NodeSpec := h35Block4_0 ++ h35Block4_1 ++ h35Block4_2
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Check4 : checkNodesBT h35W h35G h35Mask h35Pools h35Autos h35Bucket3 4 h35Nodes4 = true := by
  unfold h35Nodes4 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨h35Test4_0,h35Test4_1⟩,h35Test4_2⟩
def h35Bucket4 : BT (List (List Nat)) := buildBucketsBT h35W h35Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h35G 4 xs.toFinset) h35Bucket4 := buildBucketsBT_sound (by decide) h35Pairs h35WOk h35PoolsOk h35AutosOk h35Bucket3Ok h35Check4
def h35Block5_0 : List NodeSpec := [([3,4,6,8,9],[0,1,2,3,4],[0,1,4,7]),([2,3,4,6,8,9],[0,1,3],[0]),([2,3,4,6,8,29],[],[0,2,4]),([2,3,4,6,8,36],[0,1],[0]),([1,3,4,6,8,24],[],[0,4]),([1,3,4,6,8,25],[],[0]),([1,3,4,6,8,26],[0],[0,1]),([1,3,4,6,8,27],[0],[0]),([1,2,3,4,6,12],[1],[0,2]),([1,2,3,4,6,13],[1],[0]),([1,2,3,4,6,51],[1],[0]),([0,1,4,6,23,24],[3,6,7],[0,4])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Test5_0 : checkNodesBT h35W h35G h35Mask h35Pools h35Autos h35Bucket4 5 h35Block5_0 = true := by decide +kernel
def h35Block5_1 : List NodeSpec := [([0,1,3,4,23,27],[],[0]),([0,1,2,3,4,33],[3,9,10],[0]),([0,1,2,3,4,54],[],[0]),([0,1,3,4,16,24],[8,9],[0]),([0,1,2,3,4,18],[10],[0,2]),([0,1,2,3,4,31],[],[0]),([1,2,3,4,6,61],[1],[0,4]),([0,1,3,4,16,25],[9,13],[0]),([0,1,2,4,11,25],[],[0,2]),([0,1,2,3,6,39],[3,16],[0,4]),([0,1,2,3,6,40],[17,18],[0]),([0,1,2,3,4,21],[],[0,2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Test5_1 : checkNodesBT h35W h35G h35Mask h35Pools h35Autos h35Bucket4 5 h35Block5_1 = true := by decide +kernel
def h35Block5_2 : List NodeSpec := [([0,1,2,3,4,41],[3],[0]),([0,1,3,4,16,26],[6,15],[0,1]),([0,1,2,4,6,43],[3,20],[0,4]),([0,1,2,4,6,44],[21],[0]),([0,1,2,3,4,27],[],[0]),([0,1,2,3,4,57],[],[0]),([1,2,3,4,16,57],[0],[0]),([0,1,3,4,16,27],[0],[0,1]),([0,1,2,4,16,56],[22],[0,2]),([0,1,2,4,48],[],[0]),([0,1,2,3,4,48],[],[0]),([0,1,2,4,16,48],[9],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Test5_2 : checkNodesBT h35W h35G h35Mask h35Pools h35Autos h35Bucket4 5 h35Block5_2 = true := by decide +kernel
def h35Block5_3 : List NodeSpec := [([1,2,3,4,6,57],[0],[0]),([0,1,2,4,6,56],[6],[0]),([0,1,2,4,6,48],[],[0]),([1,2,3,4,6,68],[0],[0]),([0,1,3,4,17,27],[],[0]),([0,1,2,3,4,16],[9,10],[0,2,6]),([0,1,2,3,4,45],[10],[0]),([1,3,4,8,9,57],[3],[0]),([0,1,3,4,9,12],[1],[0]),([0,1,3,4,9,13],[],[0]),([1,2,3,4,8,57],[0],[0]),([0,1,3,4,8,70],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Test5_3 : checkNodesBT h35W h35G h35Mask h35Pools h35Autos h35Bucket4 5 h35Block5_3 = true := by decide +kernel
def h35Block5_4 : List NodeSpec := nodesWithIdentity [([0,1,4,8,24,29],[]),([0,1,2,3,4,32],[0,1]),([0,1,2,3,4,34],[]),([0,1,3,4,8,27],[0]),([0,1,2,4,8,48],[]),([0,1,3,4,24,36],[9]),([0,1,3,4,25,36],[]),([0,1,2,3,4,37],[]),([0,1,4,8,13,24],[9]),([0,1,3,4,8,30],[0,6,8,29]),([0,1,3,4,8,38],[]),([0,1,3,8,39],[3,13,14,15,16])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Test5_4 : checkNodesBT h35W h35G h35Mask h35Pools h35Autos h35Bucket4 5 h35Block5_4 = true := by decide +kernel
def h35Block5_5 : List NodeSpec := [([0,1,3,4,8,42],[],[0]),([0,1,2,4,10,13],[10],[0]),([0,1,2,3,4,14],[1],[0]),([0,1,2,3,4,20],[],[0]),([0,1,2,3,4,46],[],[0]),([0,1,3,4,12,47],[0],[0]),([0,1,2,3,4,15],[],[0]),([0,1,3,4,8,47],[0],[0]),([1,2,3,4,7,13],[],[0]),([0,1,2,4,13,35],[],[0,2]),([0,1,2,3,4,49],[],[0,2]),([0,1,2,3,4,19],[3],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Test5_5 : checkNodesBT h35W h35G h35Mask h35Pools h35Autos h35Bucket4 5 h35Block5_5 = true := by decide +kernel
def h35Block5_6 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,52],[]),([0,1,4,24,51],[3,6,8,15,33]),([0,1,2,3,4,71],[]),([0,1,2,3,4,62],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Test5_6 : checkNodesBT h35W h35G h35Mask h35Pools h35Autos h35Bucket4 5 h35Block5_6 = true := by decide +kernel
def h35Nodes5 : List NodeSpec := h35Block5_0 ++ h35Block5_1 ++ h35Block5_2 ++ h35Block5_3 ++ h35Block5_4 ++ h35Block5_5 ++ h35Block5_6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Check5 : checkNodesBT h35W h35G h35Mask h35Pools h35Autos h35Bucket4 5 h35Nodes5 = true := by
  unfold h35Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨h35Test5_0,h35Test5_1⟩,h35Test5_2⟩,h35Test5_3⟩,h35Test5_4⟩,h35Test5_5⟩,h35Test5_6⟩
def h35Bucket5 : BT (List (List Nat)) := buildBucketsBT h35W h35Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h35G 5 xs.toFinset) h35Bucket5 := buildBucketsBT_sound (by decide) h35Pairs h35WOk h35PoolsOk h35AutosOk h35Bucket4Ok h35Check5
def h35Block6_0 : List NodeSpec := [([1,2,3,4,6,8],[0,1,2,3],[0,1]),([0,1,2,3,4,6,23],[0,1,3,5,9],[0,2,4]),([0,1,2,3,4,6,24],[0,1,3,6,9,11],[0,2,4,8]),([0,1,2,3,4,6,25],[0,1,3,9,12],[0,4]),([0,1,2,3,4,6,26],[0,1,3,19],[0,1,4]),([0,1,2,3,4,16],[9,10],[0,1,4]),([0,1,2,3,4,6,16],[3,4],[0,1,4]),([0,1,2,3,4,6,17],[3,23],[0,4]),([0,1,2,3,4,27],[0,1,9,10,24,25],[0,1,2,6]),([0,1,2,3,4,6,27],[0,1,3,24],[0,4]),([0,1,3,4,8,9],[0,1,2,3,4],[0,1,4,7]),([0,1,2,3,4,8,9],[0,1,2,3,4],[0,4])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Test6_0 : checkNodesBT h35W h35G h35Mask h35Pools h35Autos h35Bucket5 6 h35Block6_0 = true := by decide +kernel
def h35Block6_1 : List NodeSpec := [([0,1,3,4,8,28],[0,1,2,3,6,15,26],[0]),([0,1,2,3,4,8,29],[3,9],[0,2,4,8]),([0,1,2,3,4,8,16],[1,6,15,27],[0,1,4]),([0,1,2,3,4,36],[0,1,2,3,9,10,28],[0,1,4]),([0,1,2,3,4,8,36],[0,1,2,3],[0,4]),([0,1,3,4,8,24],[0,3,6,8,9,11,15],[0,4]),([0,1,3,4,8,25],[0,3,6,9,12,13,15],[0]),([0,1,2,3,4,8,10],[3,6,9,10,15,22],[0,1]),([0,1,2,3,4,12],[1,6,10,30],[0,2]),([0,1,2,3,4,8,12],[6,9],[0,2]),([0,1,2,3,4,13],[0,1,3,6,10],[0,2]),([0,1,2,3,4,8,13],[0,3,6,9],[0,2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Test6_1 : checkNodesBT h35W h35G h35Mask h35Pools h35Autos h35Bucket5 6 h35Block6_1 = true := by decide +kernel
def h35Block6_2 : List NodeSpec := [([0,1,2,3,4,64],[0,1,3,4,6,9,10,15],[0]),([0,1,2,3,4,51],[0,1,3,5,9,10,15],[0]),([0,1,4,23,24],[3,6,7,8,15,34],[0,4]),([0,1,2,3,4,30],[0,1,6,8,15,22,29,36],[0,2,3,4,8,9]),([0,1,2,3,4,61],[0,1,3,6,10,12,15],[0,4]),([0,1,2,3,39],[3,6,14,15,16,38],[0,4]),([0,1,2,3,40],[3,6,10,17,18,39],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Test6_2 : checkNodesBT h35W h35G h35Mask h35Pools h35Autos h35Bucket5 6 h35Block6_2 = true := by decide +kernel
def h35Nodes6 : List NodeSpec := h35Block6_0 ++ h35Block6_1 ++ h35Block6_2
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Check6 : checkNodesBT h35W h35G h35Mask h35Pools h35Autos h35Bucket5 6 h35Nodes6 = true := by
  unfold h35Nodes6 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨h35Test6_0,h35Test6_1⟩,h35Test6_2⟩
def h35Bucket6 : BT (List (List Nat)) := buildBucketsBT h35W h35Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h35G 6 xs.toFinset) h35Bucket6 := buildBucketsBT_sound (by decide) h35Pairs h35WOk h35PoolsOk h35AutosOk h35Bucket5Ok h35Check6
def h35Block7_0 : List NodeSpec := [([0,1,2,3,4,6],[0,1,3,9,10],[0,1,2,3,4,5,6,8,9]),([0,1,2,3,4,8],[0,1,2,3,6,9,10,15],[0,1]),([0,1,2,3,4,50],[0,1,3,6,9,10,15,31],[0,4]),([0,1,2,3,4,23],[0,1,3,5,9,10,15,32],[0,4]),([0,1,2,3,4,24],[0,1,3,6,9,10,11,15,22,35],[0,2,3,4,8,9]),([0,1,2,3,4,25],[0,1,3,6,9,10,12,15,37],[0,4])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Test7_0 : checkNodesBT h35W h35G h35Mask h35Pools h35Autos h35Bucket6 7 h35Block7_0 = true := by decide +kernel
def h35Nodes7 : List NodeSpec := h35Block7_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Check7 : checkNodesBT h35W h35G h35Mask h35Pools h35Autos h35Bucket6 7 h35Nodes7 = true := h35Test7_0
def h35Bucket7 : BT (List (List Nat)) := buildBucketsBT h35W h35Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h35G 7 xs.toFinset) h35Bucket7 := buildBucketsBT_sound (by decide) h35Pairs h35WOk h35PoolsOk h35AutosOk h35Bucket6Ok h35Check7
def h35Block8_0 : List NodeSpec := [([0,1,2,3,4],[0,1],[0,1,2,3,4,5,6,8,9])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Test8_0 : checkNodesBT h35W h35G h35Mask h35Pools h35Autos h35Bucket7 8 h35Block8_0 = true := by decide +kernel
def h35Nodes8 : List NodeSpec := h35Block8_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Check8 : checkNodesBT h35W h35G h35Mask h35Pools h35Autos h35Bucket7 8 h35Nodes8 = true := h35Test8_0
def h35Bucket8 : BT (List (List Nat)) := buildBucketsBT h35W h35Nodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h35G 8 xs.toFinset) h35Bucket8 := buildBucketsBT_sound (by decide) h35Pairs h35WOk h35PoolsOk h35AutosOk h35Bucket7Ok h35Check8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Bound : Lower h35R h35G 9 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 3,1,9),(VAR 4,1,17)]) (by decide +kernel) h35Bucket8Ok (by decide +kernel)
def h38R : List Nat := varsOf 47
def h38G : Nat := 0xfeeefeeeeeeaeeeafeeefeeeeeeaeeea
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38Bound : Lower h38R h38G 7 := lift_of (z := 1) (o := 0) (essPairs := [(VAR 0,0,1)]) (by decide +kernel) h30Bound
def h39R : List Nat := varsOf 55
def h39G : Nat := 0xfefeeeeeeeeeeaeafefeeeeeeeeeeaea
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h39Bound : Lower h39R h39G 7 := carry_of (swaps := [(3,4)]) (roots2 := h38R) (T2 := h38G) (by decide +kernel) h38Bound
def h40R : List Nat := varsOf 59
def h40G : Nat := 0xffeeeeeeeeeeeeaaffeeeeeeeeeeeeaa
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h40Bound : Lower h40R h40G 7 := carry_of (swaps := [(3,4),(2,3)]) (roots2 := h38R) (T2 := h38G) (by decide +kernel) h38Bound
def h41R : List Nat := varsOf 61
def h41G : Nat := 0xfffffffafffafaaafffffffafffafaaa
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h41Bound : Lower h41R h41G 8 := lift_of (z := 1) (o := 0) (essPairs := [(VAR 0,0,1)]) (by decide +kernel) h33Bound
def h0R : List Nat := varsOf 63
def h0G : Nat := 0xfeeeeee8eeeaeaa8feeeeee8eeeaeaa8
def h0Pos : List Nat := [5,14,3,3,5,14,5,7,14,9,11,22,17,19,38,35,60,42,25,60,38,35,41,26,60,42,49,50,26,30,25,26,60,22,17,45,13,17,49,29,50,37,9,5,46,13,50,17,22,3,14,38,22,3,9,17,5,21,42,11,26,26,30,3,37,9,41,5,25,58,14,3,50,53,19,3,3,35,50,49,17,29,57,37,17,5,57,7,7,30,60,50,14,30,45,60,37,49]
def h0Neg : List Nat := [4,12,1,2,6,10,1,6,6,1,10,6,1,18,6,34,56,10,24,28,36,33,33,24,44,34,33,34,10,28,1,18,52,18,33,44,12,28,1,28,18,33,12,12,44,1,48,16,20,0,8,34,28,10,10,20,20,4,40,1,28,2,6,6,36,33,1,0,28,56,28,18,32,52,1,34,33,1,2,48,18,24,56,44,24,28,33,1,2,10,36,52,2,18,33,48,52,32]
def h0Mask : Nat := fullMask 98
def h0Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x341ffbe9f8be2aefc4464b6dd,0x40c034060800224444601244),(0xcccccccccccccccccccccccccccccccc,0x3b807de0fc3f5102bab2edae,0x33014880e06801029a02edb8),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x1f7aa0249431d3a9b211949f3,0x10c280251d3911cb921184993),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xf64600767c443499f3cf0722,0x23e007014741cb8318f0422),(0xffff0000ffff0000ffff0000ffff0000,0x2ae57c7307291c1e7fd8d3800,0x1a83782f01191c1a3a08d2000),(0xffffffff00000000ffffffff00000000,0x3cc4ce325040853490f7bc000,0x3cc4c9b230408520d0f718000)]
def h0Steps : List (Nat × Nat × Nat) := [(1,0,1),(3,0,1),(1,0,2),(3,0,2),(1,0,3),(1,0,4),(1,0,5),(3,0,5),(0,1,2),(1,1,2),(2,1,2),(1,0,16),(3,0,16),(0,2,3),(1,2,3),(2,2,3),(1,2,4),(2,2,4),(3,2,6),(0,3,4),(1,0,25),(1,2,26),(1,3,4),(1,2,28),(0,6,28),(3,16,28),(1,26,28),(2,3,4),(0,3,5),(3,3,5),(1,3,16),(2,3,16),(3,3,16),(0,4,5),(1,4,5),(2,4,5),(3,4,5),(3,4,6),(1,2,25),(3,0,28),(1,16,25),(2,16,25),(3,25,28),(1,0,30),(1,0,33),(1,2,33),(1,16,33),(2,16,33),(3,1,2),(0,1,3),(2,1,3),(0,1,4),(1,1,4),(2,1,4),(3,1,4),(0,1,5),(1,1,5),(2,1,5),(3,1,5),(1,0,19),(0,1,20),(3,1,20),(0,1,40),(0,4,20),(3,4,20),(1,4,65),(2,4,65),(0,6,20),(1,20,65),(2,1,41),(2,4,75),(0,3,65),(2,1,19),(1,0,78),(3,0,20),(3,0,43),(1,4,19),(3,19,20),(2,6,19),(1,0,73),(1,0,21),(2,1,21),(1,0,87),(1,4,21),(2,6,21),(2,1,18),(1,0,55),(3,3,8),(1,4,8),(3,4,8),(1,4,92),(2,4,92),(1,8,92),(2,8,55),(2,22,55),(1,23,55),(1,55,93),(3,55,94),(1,55,95),(2,8,56),(3,56,94),(1,0,91),(2,1,25),(0,1,28),(1,0,48),(1,2,48),(2,2,48),(1,28,91),(2,28,91),(1,48,91),(1,0,115),(3,0,115),(1,25,91),(1,0,118),(1,3,107),(2,3,107),(1,4,107),(2,4,107),(1,32,107),(2,32,107),(2,32,91),(1,0,126),(3,0,113),(2,1,33),(1,33,91),(1,0,130),(2,8,25),(0,8,28),(2,8,33),(1,34,91),(2,8,21),(0,2,49),(1,8,49),(2,49,137),(3,109,138),(1,0,57),(0,5,58),(3,5,58),(0,58,74),(3,57,58),(3,57,74),(1,4,142),(2,74,142),(1,4,143),(3,60,74),(1,0,61),(3,41,74),(1,0,41),(3,61,74),(2,74,76),(0,4,62),(2,74,156),(3,4,62),(0,62,74),(1,0,63),(1,0,39),(2,1,39),(2,4,63),(3,39,74),(3,63,74),(0,1,149),(2,74,163),(1,4,64),(2,4,64),(2,74,169),(3,64,74),(3,0,40),(3,39,40),(0,40,74),(1,0,68),(3,68,74),(1,0,42),(3,42,74),(2,1,9),(1,3,9),(1,4,9),(1,9,109),(3,4,120),(1,4,125),(2,0,14),(1,3,14),(1,14,28),(3,14,28),(2,12,19),(0,12,20),(2,12,21),(1,14,25),(1,4,127),(1,14,33),(1,4,66),(3,25,32),(1,0,121),(1,16,48),(2,16,48),(1,14,48),(0,5,15),(3,5,15),(2,15,25),(3,28,203),(0,15,28),(2,15,48),(3,3,15),(1,0,205),(3,14,15),(2,15,33),(1,4,31),(3,4,52),(1,3,54),(1,28,54),(2,28,54),(1,48,54),(1,25,54),(1,0,215),(1,33,54),(1,0,72),(1,0,195),(3,0,195),(3,19,195),(1,0,223),(3,0,224),(1,4,67),(2,1,69),(1,0,227),(2,1,70),(1,0,229),(1,19,230),(3,0,231),(1,19,229),(1,1,83),(2,1,83),(1,4,83),(1,0,236),(3,0,236),(0,1,236),(3,4,234),(0,5,236),(2,4,83),(1,0,235),(3,0,243),(1,0,242),(2,1,242),(1,4,235),(0,4,85),(0,5,221),(2,5,248),(2,221,248),(2,4,85),(3,4,85),(1,0,249),(1,0,252)]
def h0W : BT Decor := buildWiresBT 8 h0Base h0Steps
def h0AutoList : List (List (Nat × Nat)) := [[],[(3,4)],[(2,3)],[(2,4)],[(3,4),(2,3)],[(3,4),(2,4)]]
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
def h0SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 2,8),some (subcubeFast 0 4,7),some (subcubeFast 0 8,7),some (subcubeFast 0 16,7),some (subcubeFast 0 32,9),some (subcubeFast 1 0,9),some (subcubeFast 1 2,7),some (subcubeFast 1 4,6),some (subcubeFast 1 8,6),some (subcubeFast 1 16,6),some (subcubeFast 1 32,6),some (subcubeFast 2 0,7),some (subcubeFast 2 32,6),some (subcubeFast 4 0,8),some (subcubeFast 4 2,5),some (subcubeFast 5 0,5),some (subcubeFast 5 2,4),some (subcubeFast 8 0,8),some (subcubeFast 8 2,5),some (subcubeFast 9 0,5),some (subcubeFast 9 2,4),some (subcubeFast 12 0,5),some (subcubeFast 12 32,4),some (subcubeFast 16 0,8),some (subcubeFast 16 2,5),some (subcubeFast 16 32,5),some (subcubeFast 17 0,5),some (subcubeFast 17 2,4),some (subcubeFast 20 0,5),some (subcubeFast 20 32,4),some (subcubeFast 24 0,5),some (subcubeFast 24 32,4),some (subcubeFast 32 0,9),some (subcubeFast 32 2,5),some (subcubeFast 33 2,4),some (subcubeFast 36 0,6),some (subcubeFast 40 0,6),some (subcubeFast 48 0,6)]
def h0Slices : BT (Option (Nat × Nat)) := btOfList 6 h0SliceList
def h0Specs : List PoolSpec := [(5,[]),(0,[]),(5,[(2,1,2)]),(13,[(1,0,1)]),(1,[(1,0,1)]),(32,[(1,0,1),(2,1,2)]),(4,[(1,0,1),(2,1,2)]),(13,[]),(5,[(2,1,2),(0,3,4)]),(0,[(0,3,4)]),(5,[(0,3,4)]),(0,[(0,3,4),(1,0,25)]),(19,[(2,1,2)]),(7,[(0,3,4)]),(0,[(0,3,4),(1,0,25),(1,3,4)]),(7,[(0,3,4),(1,3,4)]),(18,[]),(8,[(2,1,2)]),(19,[]),(2,[(1,0,1),(1,0,25)]),(17,[(1,0,1),(2,1,2)]),(23,[(1,0,1),(2,1,2)]),(3,[(1,0,1),(1,0,25)]),(11,[]),(20,[]),(13,[(0,3,4)]),(5,[(2,1,2),(0,3,4),(1,3,4)]),(0,[(0,3,4),(1,3,4)]),(5,[(0,3,4),(1,3,4)]),(13,[(0,3,4),(1,3,4)]),(2,[(1,0,1)]),(3,[(1,0,1)]),(14,[]),(5,[(2,1,2),(1,3,4)]),(0,[(1,3,4)]),(5,[(1,3,4)]),(13,[(1,3,4)]),(7,[(1,3,4)]),(5,[(2,1,2),(2,3,4)]),(0,[(2,3,4)]),(5,[(2,3,4)]),(9,[(2,1,2)]),(13,[(2,3,4)]),(7,[(2,3,4)]),(8,[]),(7,[]),(9,[]),(32,[(1,0,1)]),(4,[(1,0,1)]),(5,[(0,2,3)]),(0,[(0,2,3)]),(0,[(0,2,3),(1,0,19)]),(17,[(1,0,1)]),(32,[(1,0,1),(0,2,3),(1,0,19)]),(4,[(1,0,1),(0,2,3),(1,0,19)]),(15,[]),(0,[(1,2,3),(0,2,3),(1,0,19)]),(5,[(1,2,3),(0,2,3)]),(1,[(1,0,1),(1,0,19)]),(35,[(1,0,1)]),(16,[]),(17,[]),(32,[(1,0,1),(0,2,3)]),(4,[(1,0,1),(0,2,3)]),(5,[(0,2,3),(2,1,19)]),(32,[(1,0,1),(0,2,3),(2,1,19)]),(4,[(1,0,1),(0,2,3),(2,1,19)]),(5,[(0,2,3),(1,2,3)]),(0,[(0,2,3),(1,2,3)]),(32,[(1,0,1),(0,2,3),(1,2,3)]),(4,[(1,0,1),(0,2,3),(1,2,3)]),(23,[(0,2,3),(1,2,3)]),(5,[(0,2,3),(1,2,3),(3,4,6)]),(7,[(3,4,6)]),(13,[(1,0,1),(3,4,6)]),(6,[(0,2,3),(1,2,3)]),(11,[(0,2,3),(1,2,3)]),(35,[(1,0,1),(3,4,6)]),(3,[(0,2,3),(1,2,3)]),(32,[(0,2,3),(1,2,3)]),(4,[(0,2,3),(1,2,3)]),(1,[]),(21,[]),(5,[(0,2,3),(1,2,3),(0,6,20)]),(13,[(1,0,1),(0,6,20)]),(35,[(1,0,1),(0,6,20)]),(22,[]),(5,[(0,2,3),(3,2,6)]),(32,[(0,2,3),(1,0,1),(3,2,6)]),(4,[(0,2,3),(1,0,1),(3,2,6)]),(17,[(1,0,1),(3,2,6)]),(2,[]),(23,[(1,0,1),(3,2,6)]),(32,[(1,0,1),(3,2,6)]),(23,[(0,2,3)]),(5,[(0,2,3),(3,4,6)]),(5,[(3,4,6)]),(6,[(0,2,3)]),(11,[(0,2,3)]),(11,[(3,4,6)]),(17,[(1,0,1),(3,4,6)]),(32,[(0,2,3),(1,0,1),(3,4,6)]),(3,[]),(23,[(1,0,1)]),(32,[(1,0,1),(3,4,6)]),(4,[(1,0,1),(3,4,6)]),(32,[(0,2,3)]),(4,[(0,2,3)]),(24,[]),(3,[(0,2,3)]),(5,[(0,2,3),(2,6,19)]),(32,[(1,0,1),(0,2,3),(2,6,19)]),(4,[(1,0,1),(0,2,3),(2,6,19)]),(23,[]),(32,[]),(4,[]),(5,[(1,2,3)]),(0,[(1,2,3)]),(32,[(1,0,1),(1,2,3)]),(4,[(1,0,1),(1,2,3)]),(23,[(1,2,3)]),(5,[(1,2,3),(3,4,6)]),(6,[(1,2,3)]),(11,[(1,2,3)]),(32,[(1,2,3),(1,0,1),(3,4,6)]),(3,[(1,2,3)]),(32,[(1,2,3)]),(4,[(1,2,3)]),(5,[(1,2,3),(0,6,20)]),(32,[(1,0,1),(1,2,3),(0,6,20)]),(4,[(1,0,1),(1,2,3),(0,6,20)]),(17,[(1,0,1),(0,6,20)]),(5,[(2,2,3)]),(0,[(2,2,3)]),(32,[(1,0,1),(2,2,3)]),(4,[(1,0,1),(2,2,3)]),(5,[(2,2,3),(2,1,21)]),(32,[(1,0,1),(2,2,3),(2,1,21)]),(4,[(1,0,1),(2,2,3),(2,1,21)]),(17,[(1,0,1),(2,1,21)]),(23,[(2,2,3)]),(5,[(2,2,3),(3,4,6)]),(8,[(3,4,6)]),(6,[(2,2,3)]),(11,[(2,2,3)]),(32,[(2,2,3),(1,0,1),(3,4,6)]),(32,[(2,2,3)]),(4,[(2,2,3)]),(3,[(2,2,3)]),(5,[(2,2,3),(2,6,21)]),(32,[(1,0,1),(2,2,3),(2,6,21)]),(4,[(1,0,1),(2,2,3),(2,6,21)]),(17,[(1,0,1),(2,6,21)]),(5,[(3,2,6)]),(6,[]),(4,[(1,0,1),(3,2,6)]),(13,[(3,0,1)]),(1,[(3,0,1)]),(32,[(3,0,1),(2,1,2)]),(4,[(3,0,1),(2,1,2)]),(11,[(0,3,4)]),(17,[(3,0,1),(2,1,2)]),(11,[(0,3,4),(1,3,4)]),(2,[(3,0,1)]),(23,[(3,0,1),(2,1,2)]),(3,[(3,0,1)]),(11,[(1,3,4)]),(11,[(2,3,4)]),(32,[(3,0,1)]),(4,[(3,0,1)]),(17,[(3,0,1)]),(32,[(3,0,1),(0,2,3)]),(4,[(3,0,1),(0,2,3)]),(32,[(3,0,1),(0,2,3),(1,2,3)]),(4,[(3,0,1),(0,2,3),(1,2,3)]),(0,[(0,2,3),(1,2,3),(3,0,43)]),(0,[(0,2,3),(3,0,43)]),(0,[(3,0,43)]),(23,[(1,0,1),(3,0,43)]),(32,[(1,0,1),(3,4,6),(3,0,43)]),(4,[(1,0,1),(3,4,6),(3,0,43)]),(27,[]),(23,[(3,0,1)]),(32,[(3,0,1),(1,2,3)]),(4,[(3,0,1),(1,2,3)]),(0,[(1,2,3),(3,0,43)]),(32,[(3,0,1),(2,2,3)]),(4,[(3,0,1),(2,2,3)]),(0,[(2,2,3),(3,0,43)]),(13,[(3,0,16)]),(0,[(3,0,16)]),(32,[(2,1,2),(3,0,16)]),(4,[(2,1,2),(3,0,16)]),(5,[(0,1,3)]),(13,[(0,1,3)]),(13,[(0,1,3),(1,0,55)]),(0,[(1,0,2),(1,0,55)]),(11,[(1,0,2)]),(17,[(1,0,2)]),(32,[(1,0,2),(0,1,3),(1,0,55)]),(4,[(1,0,2),(0,1,3),(1,0,55)]),(0,[(1,0,2),(1,2,4),(1,0,55)]),(17,[(1,0,2),(1,2,4)]),(1,[(0,1,3),(1,0,55)]),(2,[(1,0,2),(1,0,55)]),(9,[(0,1,3)]),(28,[]),(0,[(1,0,2),(2,2,4),(1,0,55)]),(17,[(1,0,2),(2,2,4)]),(15,[(0,1,3)]),(0,[(1,0,55),(1,0,2),(1,4,8)]),(17,[(1,0,2),(1,4,8)]),(3,[(0,1,3),(1,0,55)]),(4,[(0,1,3),(1,0,55)]),(0,[(1,0,55),(1,0,2),(3,4,8)]),(17,[(1,0,2),(3,4,8)]),(11,[(1,0,2),(3,4,8)]),(17,[(1,4,92)]),(17,[(2,4,92)]),(0,[(1,0,2)]),(32,[(1,0,2),(0,1,3)]),(4,[(1,0,2),(0,1,3)]),(5,[(1,2,4),(0,1,3)]),(1,[(0,1,3)]),(5,[(1,2,4)]),(6,[(1,2,4)]),(0,[(1,0,2),(1,2,4)]),(2,[(1,0,2)]),(23,[(0,1,3)]),(3,[(1,0,2)]),(23,[(1,0,2)]),(32,[(1,0,2),(1,2,4)]),(4,[(1,0,2),(1,2,4)]),(5,[(1,2,4),(0,1,3),(2,8,55)]),(13,[(0,1,3),(2,8,55)]),(9,[(0,1,3),(2,8,55)]),(17,[(1,2,4),(1,0,2)]),(5,[(1,2,4),(0,1,3),(2,22,55)]),(13,[(0,1,3),(2,22,55)]),(5,[(2,2,4),(0,1,3)]),(5,[(2,2,4)]),(6,[(2,2,4)]),(0,[(1,0,2),(2,2,4)]),(32,[(1,0,2),(2,2,4)]),(4,[(1,0,2),(2,2,4)]),(5,[(2,2,4),(0,1,3),(1,23,55)]),(5,[(0,1,3),(3,3,8)]),(6,[(3,3,8)]),(13,[(0,1,3),(3,3,8)]),(0,[(1,0,2),(3,3,8)]),(11,[(1,0,2),(3,3,8)]),(32,[(0,1,3),(1,0,2),(3,3,8)]),(4,[(0,1,3),(1,0,2),(3,3,8)]),(5,[(0,1,3),(3,3,8),(1,55,93)]),(13,[(0,1,3),(3,3,8),(1,55,93)]),(5,[(0,1,3),(1,4,8)]),(5,[(1,4,8)]),(6,[(1,4,8)]),(7,[(0,1,3)]),(0,[(1,0,2),(1,4,8)]),(13,[(1,4,8)]),(3,[(0,1,3)]),(32,[(1,0,2),(1,4,8)]),(4,[(1,0,2),(1,4,8)]),(32,[(0,1,3)]),(4,[(0,1,3)]),(5,[(0,1,3),(1,4,8),(3,55,94)]),(5,[(0,1,3),(3,4,8)]),(5,[(3,4,8)]),(6,[(3,4,8)]),(0,[(1,0,2),(3,4,8)]),(13,[(3,4,8)]),(32,[(1,0,2),(3,4,8)]),(4,[(1,0,2),(3,4,8)]),(5,[(0,1,3),(3,4,8),(1,55,95)]),(1,[(0,1,3),(1,55,95)]),(32,[(1,0,2)]),(4,[(1,0,2)]),(5,[(0,1,3),(1,8,92)]),(5,[(0,1,3),(2,8,55)]),(0,[(1,0,2),(2,8,55)]),(32,[(1,0,2),(0,1,3),(2,8,55)]),(4,[(1,0,2),(0,1,3),(2,8,55)]),(5,[(2,1,3)]),(13,[(2,1,3)]),(32,[(1,0,2),(2,1,3)]),(4,[(1,0,2),(2,1,3)]),(1,[(2,1,3)]),(5,[(1,2,4),(2,1,3)]),(23,[(2,1,3)]),(8,[(1,2,4)]),(18,[(1,0,2)]),(5,[(2,2,4),(2,1,3)]),(15,[(2,1,3)]),(8,[(2,2,4)]),(5,[(2,1,3),(1,4,8)]),(7,[(2,1,3)]),(3,[(2,1,3)]),(32,[(2,1,3)]),(4,[(2,1,3)]),(8,[(1,4,8)]),(5,[(2,1,3),(3,4,8)]),(8,[(3,4,8)]),(5,[(2,1,3),(2,8,56)]),(13,[(2,1,3),(2,8,56)]),(0,[(1,0,2),(2,8,56)]),(17,[(1,0,2),(2,8,56)]),(32,[(1,0,2),(2,1,3),(2,8,56)]),(4,[(1,0,2),(2,1,3),(2,8,56)]),(5,[(2,1,2),(2,1,18)]),(12,[]),(6,[(0,3,4)]),(0,[(0,3,4),(3,0,16)]),(1,[(0,3,4)]),(13,[(3,0,16),(2,1,18)]),(6,[(0,3,4),(1,3,4)]),(0,[(0,3,4),(1,3,4),(3,0,16)]),(1,[(0,3,4),(1,3,4)]),(32,[(0,3,4),(1,3,4)]),(4,[(0,3,4),(1,3,4)]),(5,[(1,3,4),(0,3,4),(3,25,28)]),(30,[]),(6,[(1,3,4),(0,3,4),(1,25,91)]),(11,[(1,3,4),(0,3,4)]),(32,[(2,1,2),(3,0,16),(2,1,18)]),(4,[(2,1,2),(3,0,16),(2,1,18)]),(32,[(0,3,4)]),(4,[(0,3,4)]),(6,[(0,3,4),(1,25,91)]),(0,[(0,3,4),(3,0,16),(1,25,91)]),(6,[(1,3,4)]),(17,[(1,26,28)]),(23,[(1,26,28)]),(17,[(3,0,28)]),(23,[(3,0,28)]),(0,[(1,3,4),(3,0,16)]),(1,[(1,3,4)]),(32,[(1,3,4)]),(4,[(1,3,4)]),(6,[(2,3,4)]),(0,[(2,3,4),(3,0,16)]),(1,[(2,3,4)]),(32,[(2,3,4)]),(4,[(2,3,4)]),(6,[(2,3,4),(1,33,91)]),(0,[(1,0,2),(0,3,4)]),(0,[(1,0,2),(0,3,4),(1,3,4)]),(0,[(1,0,2),(1,3,4)]),(0,[(1,0,2),(2,3,4)]),(1,[(0,3,5)]),(5,[(0,3,5)]),(0,[(1,0,2),(0,3,5)]),(0,[(0,3,5)]),(12,[(1,0,2)]),(1,[(3,3,5)]),(5,[(3,3,5)]),(0,[(1,0,2),(3,3,5)]),(0,[(3,3,5)]),(32,[(1,0,2),(1,2,3)]),(4,[(1,0,2),(1,2,3)]),(32,[(1,0,2),(2,2,3)]),(4,[(1,0,2),(2,2,3)]),(5,[(2,2,3),(2,8,21)]),(17,[(1,0,2),(2,8,21)]),(6,[(2,2,3),(2,8,21)]),(32,[(1,0,2),(2,2,3),(2,8,21)]),(4,[(1,0,2),(2,2,3),(2,8,21)]),(32,[(1,0,2),(0,3,4)]),(4,[(1,0,2),(0,3,4)]),(5,[(0,3,4),(2,1,25)]),(13,[(0,3,4),(2,1,25)]),(2,[(2,1,25)]),(3,[(2,1,25)]),(32,[(0,3,4),(2,1,25)]),(4,[(0,3,4),(2,1,25)]),(32,[(1,0,2),(0,3,4),(1,3,4)]),(4,[(1,0,2),(0,3,4),(1,3,4)]),(5,[(0,3,4),(1,2,26),(1,3,4)]),(17,[(1,2,26)]),(13,[(0,3,4),(1,0,25),(1,3,4)]),(5,[(0,3,4),(1,3,4),(2,8,25)]),(5,[(1,3,4),(0,3,4),(2,8,25)]),(5,[(0,3,4),(1,2,26)]),(13,[(0,3,4),(1,0,25)]),(32,[(0,3,4),(1,0,25),(1,2,26)]),(4,[(0,3,4),(1,0,25),(1,2,26)]),(5,[(0,3,4),(2,8,25)]),(13,[(0,3,4),(2,8,25)]),(6,[(0,3,4),(2,8,25)]),(32,[(1,0,2),(0,3,4),(2,8,25)]),(4,[(1,0,2),(0,3,4),(2,8,25)]),(32,[(1,0,2),(1,3,4)]),(4,[(1,0,2),(1,3,4)]),(5,[(1,3,4),(0,1,28)]),(13,[(1,3,4),(0,1,28)]),(0,[(1,0,2),(1,3,4),(1,0,30)]),(2,[(1,0,2),(1,0,1)]),(3,[(1,0,2),(1,0,1)]),(5,[(1,3,4),(0,6,28)]),(17,[(0,1,28)]),(23,[(0,1,28)]),(32,[(1,3,4),(0,1,28)]),(4,[(1,3,4),(0,1,28)]),(5,[(1,3,4),(0,8,28)]),(13,[(1,3,4),(0,8,28)]),(17,[(1,0,2),(0,8,28)]),(23,[(1,0,2),(0,8,28)]),(32,[(1,0,2),(1,3,4),(0,8,28)]),(4,[(1,0,2),(1,3,4),(0,8,28)]),(6,[(1,3,4),(0,8,28)]),(32,[(1,0,2),(2,3,4)]),(4,[(1,0,2),(2,3,4)]),(5,[(2,3,4),(2,1,33)]),(13,[(2,3,4),(2,1,33)]),(2,[(2,1,33)]),(23,[(2,1,33)]),(32,[(2,3,4),(2,1,33)]),(4,[(2,3,4),(2,1,33)]),(5,[(2,3,4),(2,8,33)]),(13,[(2,3,4),(2,8,33)]),(23,[(1,0,2),(2,8,33)]),(32,[(1,0,2),(2,3,4),(2,8,33)]),(4,[(1,0,2),(2,3,4),(2,8,33)]),(6,[(2,3,4),(2,8,33)]),(13,[(0,3,65)]),(36,[(1,0,2)]),(36,[]),(13,[(1,20,65)]),(17,[(1,20,65)]),(6,[(1,2,3),(0,2,3)]),(7,[(1,1,4)]),(1,[(1,1,4)]),(2,[(1,1,4)]),(1,[(2,1,4)]),(7,[(1,1,4),(0,5,58)]),(1,[(1,1,4),(0,5,58)]),(11,[(0,5,58)]),(2,[(1,1,4),(0,5,58)]),(23,[(0,5,58)]),(35,[(1,20,65)]),(7,[(1,1,4),(3,5,58)]),(1,[(1,1,4),(3,5,58)]),(11,[(3,5,58)]),(2,[(1,1,4),(3,5,58)]),(23,[(3,5,58)]),(33,[]),(32,[(1,1,4)]),(4,[(1,1,4)]),(7,[(3,1,4)]),(1,[(3,1,4)]),(2,[(3,1,4)]),(1,[(0,1,4)]),(32,[(3,1,4)]),(4,[(3,1,4)]),(7,[(0,1,5)]),(1,[(0,1,5),(1,0,61)]),(13,[(1,20,65),(0,1,5),(1,0,61)]),(17,[(1,20,65),(0,1,5),(1,0,61)]),(2,[(0,1,5),(1,0,61)]),(11,[(2,4,5)]),(3,[(0,1,5),(1,0,61)]),(0,[(1,0,61)]),(4,[(1,0,61)]),(1,[(0,1,5)]),(13,[(0,1,5),(1,20,65)]),(17,[(0,1,5),(1,20,65)]),(2,[(0,1,5)]),(0,[(2,4,5)]),(37,[]),(3,[(2,1,41)]),(4,[(2,4,75)]),(23,[(0,1,5)]),(3,[(0,1,5)]),(7,[(1,1,5)]),(1,[(1,1,5)]),(2,[(1,1,5)]),(3,[(1,1,5)]),(23,[(1,1,5)]),(35,[(1,20,65),(0,62,74)]),(7,[(2,1,5)]),(32,[(1,0,63)]),(1,[(2,1,5)]),(13,[(2,1,5),(1,20,65)]),(17,[(2,1,5),(1,20,65)]),(2,[(2,1,5)]),(23,[(2,1,5)]),(3,[(2,1,5)]),(25,[]),(32,[(2,4,63)]),(7,[(3,1,5)]),(1,[(3,1,5)]),(2,[(3,1,5)]),(23,[(3,1,5)]),(11,[(2,4,64)]),(3,[(3,1,5)]),(7,[(0,4,5)]),(3,[(1,0,39)]),(4,[(1,0,39)]),(1,[(0,4,5)]),(3,[(2,1,39)]),(4,[(2,1,39)]),(11,[(0,4,5)]),(0,[(0,4,5)]),(2,[(0,4,5)]),(7,[(1,4,5)]),(1,[(1,4,5)]),(0,[(1,4,5)]),(11,[(1,4,5)]),(2,[(1,4,5)]),(7,[(2,4,5)]),(32,[(1,0,41)]),(1,[(2,4,5)]),(32,[(2,1,41)]),(2,[(2,4,5)]),(35,[(1,20,65),(3,41,74)]),(7,[(3,4,5)]),(23,[(1,0,42)]),(1,[(3,4,5)]),(0,[(1,4,143)]),(11,[(3,4,5)]),(0,[(3,4,5)]),(2,[(3,4,5)]),(5,[(3,3,8)]),(13,[(3,3,8)]),(32,[(1,0,2),(3,3,8)]),(4,[(1,0,2),(3,3,8)]),(17,[(3,0,2)]),(0,[(3,0,2)]),(11,[(3,0,2)]),(32,[(3,0,2),(0,1,3)]),(4,[(3,0,2),(0,1,3)]),(17,[(3,0,2),(1,2,4)]),(0,[(3,0,2),(1,2,4)]),(2,[(3,0,2)]),(3,[(3,0,2)]),(23,[(3,0,2)]),(32,[(3,0,2),(1,2,4)]),(4,[(3,0,2),(1,2,4)]),(5,[(0,1,3),(1,4,9)]),(5,[(1,4,9)]),(6,[(1,4,9)]),(17,[(3,0,2),(1,4,9)]),(0,[(3,0,2),(1,4,9)]),(1,[(1,4,9)]),(32,[(3,0,2),(1,4,9)]),(4,[(3,0,2),(1,4,9)]),(32,[(3,0,2)]),(4,[(3,0,2)]),(32,[(3,0,2),(2,1,3)]),(4,[(3,0,2),(2,1,3)]),(18,[(3,0,2)]),(5,[(2,1,3),(1,4,9)]),(8,[(1,4,9)]),(5,[(2,1,9)]),(32,[(3,0,2),(2,1,9)]),(4,[(3,0,2),(2,1,9)]),(5,[(0,3,4),(2,1,9)]),(17,[(3,0,2),(2,1,9)]),(0,[(0,3,4),(3,0,2)]),(1,[(2,1,9)]),(5,[(0,3,4),(1,3,4),(2,1,9)]),(8,[(2,1,9)]),(0,[(0,3,4),(1,3,4),(3,0,2)]),(23,[(3,0,2),(2,1,9)]),(5,[(1,3,4),(2,1,9)]),(0,[(1,3,4),(3,0,2)]),(5,[(2,3,4),(2,1,9)]),(9,[(2,1,9)]),(0,[(2,3,4),(3,0,2)]),(32,[(3,0,2),(1,2,3)]),(4,[(3,0,2),(1,2,3)]),(32,[(3,0,2),(0,3,4)]),(4,[(3,0,2),(0,3,4)]),(0,[(3,0,2),(0,3,4)]),(32,[(3,0,2),(0,3,4),(1,3,4)]),(4,[(3,0,2),(0,3,4),(1,3,4)]),(32,[(3,0,2),(1,3,4)]),(4,[(3,0,2),(1,3,4)]),(0,[(3,0,2),(1,3,4)]),(32,[(3,0,2),(2,3,4)]),(4,[(3,0,2),(2,3,4)]),(0,[(3,0,2),(2,3,4)]),(5,[(1,3,9)]),(6,[(1,3,9)]),(32,[(3,0,2),(1,3,9)]),(4,[(3,0,2),(1,3,9)]),(5,[(0,1,2)]),(32,[(0,1,2)]),(13,[(1,0,5)]),(0,[(1,0,5),(3,0,16)]),(11,[(1,0,5)]),(0,[(1,0,5),(1,3,4),(3,0,16)]),(13,[(1,0,5),(1,3,4)]),(12,[(1,3,4)]),(1,[(1,0,5),(1,0,91)]),(21,[(1,0,5)]),(28,[(1,0,5)]),(29,[]),(34,[]),(35,[]),(0,[(1,0,5),(3,0,16),(1,3,107)]),(13,[(1,0,5),(1,3,107)]),(5,[(2,1,2),(2,1,18),(1,3,107)]),(12,[(1,3,107)]),(0,[(1,0,5)]),(4,[(0,1,2)]),(5,[(0,1,2),(1,3,4)]),(32,[(0,1,2),(1,3,4)]),(8,[(0,1,2)]),(0,[(1,0,5),(1,3,4)]),(4,[(0,1,2),(1,3,4)]),(1,[(1,0,5)]),(17,[(1,0,5),(0,1,2)]),(23,[(1,0,5),(0,1,2)]),(2,[(1,0,5)]),(17,[(1,0,5)]),(3,[(1,0,5)]),(23,[(1,0,5)]),(31,[]),(30,[(1,0,5)]),(32,[(2,1,2)]),(4,[(2,1,2)]),(32,[(2,1,2),(0,3,4)]),(17,[(1,0,5),(2,1,2)]),(13,[(1,0,5),(0,3,4)]),(0,[(1,0,5),(0,3,4)]),(4,[(2,1,2),(0,3,4)]),(32,[(2,1,2),(0,3,4),(1,3,4)]),(13,[(1,0,5),(0,3,4),(1,3,4)]),(0,[(1,0,5),(0,3,4),(1,3,4)]),(4,[(2,1,2),(0,3,4),(1,3,4)]),(12,[(0,3,4),(1,3,4)]),(23,[(1,0,5),(2,1,2)]),(12,[(0,3,4)]),(14,[(1,0,5)]),(32,[(2,1,2),(1,3,4)]),(4,[(2,1,2),(1,3,4)]),(32,[(2,1,2),(2,3,4)]),(13,[(1,0,5),(2,3,4)]),(0,[(1,0,5),(2,3,4)]),(4,[(2,1,2),(2,3,4)]),(12,[(2,3,4)]),(5,[(0,2,3),(2,12,19)]),(32,[(0,2,3),(2,12,19)]),(5,[(1,2,3),(0,12,20)]),(32,[(1,2,3),(0,12,20)]),(5,[(2,2,3),(2,12,21)]),(32,[(2,2,3),(2,12,21)]),(13,[(3,0,5)]),(0,[(3,0,5)]),(11,[(3,0,5)]),(5,[(0,1,2),(0,3,4)]),(32,[(0,1,2),(0,3,4)]),(13,[(3,0,5),(0,3,4)]),(17,[(3,0,5),(0,1,2)]),(0,[(3,0,5),(0,3,4)]),(1,[(3,0,5)]),(5,[(0,1,2),(0,3,4),(1,3,4)]),(32,[(0,1,2),(0,3,4),(1,3,4)]),(13,[(3,0,5),(0,3,4),(1,3,4)]),(0,[(3,0,5),(0,3,4),(1,3,4)]),(10,[(0,3,4),(1,3,4)]),(6,[(1,3,4),(0,3,4),(1,14,25)]),(12,[(1,3,4),(0,3,4)]),(21,[(3,0,5)]),(13,[(3,0,5),(1,3,4),(0,3,4)]),(30,[(3,0,5)]),(17,[(3,0,5)]),(2,[(3,0,5)]),(23,[(3,0,5),(0,1,2)]),(3,[(3,0,5)]),(23,[(3,0,5)]),(10,[(0,3,4)]),(10,[(0,1,2)]),(5,[(0,1,2),(0,3,4),(1,14,25)]),(32,[(0,1,2),(0,3,4),(1,14,25)]),(0,[(3,0,5),(0,3,4),(1,14,25)]),(10,[]),(13,[(3,0,5),(1,3,4)]),(0,[(3,0,5),(1,3,4)]),(10,[(1,3,4)]),(5,[(0,1,2),(1,3,4),(3,14,28)]),(32,[(0,1,2),(1,3,4),(3,14,28)]),(5,[(0,1,2),(2,3,4)]),(32,[(0,1,2),(2,3,4)]),(13,[(3,0,5),(2,3,4)]),(9,[(0,1,2)]),(0,[(3,0,5),(2,3,4)]),(10,[(2,3,4)]),(5,[(0,1,2),(2,3,4),(1,14,33)]),(32,[(0,1,2),(2,3,4),(1,14,33)]),(17,[(3,0,5),(2,1,2)]),(23,[(3,0,5),(2,1,2)]),(10,[(2,1,2)]),(14,[(3,0,5)]),(32,[(0,2,3),(2,1,19)]),(0,[(3,0,5),(0,2,3)]),(5,[(1,2,3),(0,1,20)]),(32,[(1,2,3),(0,1,20)]),(13,[(3,0,5),(0,1,20)]),(0,[(3,0,5),(1,2,3)]),(17,[(3,0,5),(0,1,20)]),(32,[(2,2,3),(2,1,21)]),(0,[(3,0,5),(2,2,3)]),(17,[(3,0,5),(2,1,21)]),(0,[(0,3,4),(1,0,25),(3,0,16)]),(1,[(1,0,91)]),(13,[(1,0,4)]),(0,[(2,3,4),(1,0,33),(3,0,16)]),(13,[(2,3,4),(1,0,33)]),(11,[(1,3,107)]),(13,[(1,3,107)]),(6,[(1,3,107)]),(0,[(3,0,16),(1,3,107)]),(0,[(3,0,16),(1,4,107)]),(0,[(3,0,16),(2,4,107)]),(35,[(1,3,107)]),(11,[(2,3,107)]),(13,[(2,3,107)]),(6,[(2,3,107)]),(12,[(2,3,107)]),(0,[(3,0,16),(2,3,107),(1,0,121)]),(13,[(2,3,107),(1,0,121)]),(5,[(2,1,2),(2,1,18),(2,3,107)]),(0,[(3,0,16),(2,3,107)]),(35,[(2,3,107)]),(17,[(2,1,2)]),(2,[(2,1,2)]),(23,[(2,1,2)]),(17,[(0,1,2)]),(23,[(0,1,2)]),(4,[(0,1,2),(0,3,4)]),(19,[(0,1,2)]),(32,[(0,3,4),(1,0,25),(1,3,4)]),(4,[(0,3,4),(1,0,25),(1,3,4)]),(2,[(1,0,25)]),(3,[(1,0,25)]),(32,[(0,3,4),(1,0,25)]),(4,[(0,3,4),(1,0,25)]),(4,[(0,1,2),(0,3,4),(1,3,4)]),(2,[(0,1,2)]),(0,[(1,3,4),(0,3,4),(1,14,25)]),(13,[(1,3,4),(0,3,4)]),(35,[(1,3,4),(0,3,4)]),(2,[(0,1,2),(1,14,25)]),(8,[(0,1,2),(1,14,25)]),(13,[(1,3,4),(0,3,4),(3,25,28)]),(0,[(1,3,4),(0,3,4),(3,25,28)]),(32,[(1,3,4),(0,3,4),(3,25,28)]),(4,[(1,3,4),(0,3,4),(3,25,28)]),(8,[(0,1,2),(1,14,48)]),(13,[(0,3,4),(1,3,4),(3,25,28)]),(0,[(0,3,4),(1,14,25)]),(4,[(0,1,2),(0,3,4),(1,14,25)]),(3,[(0,1,2)]),(13,[(1,3,4),(3,0,28)]),(0,[(1,3,4),(3,0,28)]),(32,[(1,3,4),(3,0,28)]),(4,[(1,3,4),(3,0,28)]),(5,[(0,1,2),(1,3,4),(1,14,28)]),(0,[(1,3,4),(1,14,28)]),(32,[(0,1,2),(1,3,4),(1,14,28)]),(4,[(0,1,2),(1,3,4),(1,14,28)]),(0,[(1,3,4),(3,14,28)]),(17,[(0,1,2),(3,14,28)]),(23,[(0,1,2),(3,14,28)]),(4,[(0,1,2),(1,3,4),(3,14,28)]),(4,[(0,1,2),(2,3,4)]),(0,[(2,3,4),(1,0,33)]),(2,[(1,0,33)]),(23,[(1,0,33)]),(32,[(2,3,4),(1,0,33)]),(4,[(2,3,4),(1,0,33)]),(5,[(0,1,2),(2,3,4),(1,2,33)]),(0,[(2,3,4),(1,2,33)]),(11,[(2,3,4),(1,2,33)]),(23,[(0,1,2),(1,2,33)]),(4,[(0,1,2),(2,3,4),(1,2,33)]),(32,[(0,1,2),(2,3,4),(1,2,33)]),(4,[(2,3,4),(1,2,33)]),(5,[(2,3,4),(0,1,2),(1,3,14)]),(0,[(2,3,4),(1,3,14)]),(3,[(0,1,2),(1,3,14)]),(23,[(0,1,2),(1,3,14)]),(4,[(2,3,4),(0,1,2),(1,3,14)]),(32,[(2,3,4),(0,1,2),(1,3,14)]),(4,[(0,1,2),(1,3,14)]),(0,[(2,3,4),(1,14,33)]),(23,[(0,1,2),(1,14,33)]),(4,[(0,1,2),(2,3,4),(1,14,33)]),(5,[(0,1,2),(1,3,14)]),(0,[(1,3,14)]),(32,[(0,1,2),(1,3,14)]),(5,[(1,1,2)]),(4,[(1,1,2)]),(32,[(1,1,2)]),(5,[(1,1,2),(0,3,4)]),(17,[(1,1,2)]),(23,[(1,1,2)]),(4,[(1,1,2),(0,3,4)]),(32,[(1,1,2),(0,3,4)]),(5,[(1,1,2),(0,3,4),(1,3,4)]),(4,[(1,1,2),(0,3,4),(1,3,4)]),(32,[(1,1,2),(0,3,4),(1,3,4)]),(2,[(1,1,2)]),(0,[(1,3,4),(0,3,4)]),(6,[(1,3,4),(0,3,4)]),(13,[(1,3,4),(0,3,4),(2,15,25)]),(1,[(1,3,4),(0,3,4)]),(2,[(1,1,2),(2,15,25)]),(36,[(1,1,2)]),(6,[(1,3,4),(0,3,4),(3,25,28)]),(8,[(1,1,2)]),(0,[(0,3,4),(1,3,4),(3,25,28)]),(5,[(1,1,2),(0,3,4),(2,15,25)]),(13,[(0,3,4),(2,15,25)]),(4,[(1,1,2),(0,3,4),(2,15,25)]),(32,[(1,1,2),(0,3,4),(2,15,25)]),(5,[(1,1,2),(1,3,4)]),(3,[(1,1,2)]),(4,[(1,1,2),(1,3,4)]),(32,[(1,1,2),(1,3,4)]),(5,[(1,1,2),(1,3,4),(0,15,28)]),(13,[(1,3,4),(0,15,28)]),(17,[(1,1,2),(0,15,28)]),(23,[(1,1,2),(0,15,28)]),(4,[(1,1,2),(1,3,4),(0,15,28)]),(32,[(1,1,2),(1,3,4),(0,15,28)]),(0,[(1,3,4),(1,0,205)]),(17,[(1,1,2),(3,28,203)]),(23,[(1,1,2),(3,28,203)]),(5,[(1,1,2),(0,5,15)]),(8,[(1,1,2),(0,5,15)]),(2,[(1,1,2),(0,5,15)]),(11,[(0,5,15)]),(13,[(0,5,15)]),(3,[(1,1,2),(0,5,15)]),(5,[(1,1,2),(3,5,15)]),(8,[(1,1,2),(3,5,15)]),(2,[(1,1,2),(3,5,15)]),(11,[(3,5,15)]),(13,[(3,5,15)]),(3,[(1,1,2),(3,5,15)]),(5,[(1,1,2),(2,3,4)]),(4,[(1,1,2),(2,3,4)]),(32,[(1,1,2),(2,3,4)]),(5,[(2,3,4),(1,1,2),(3,3,15)]),(13,[(2,3,4),(3,3,15)]),(3,[(1,1,2),(3,3,15)]),(23,[(1,1,2),(3,3,15)]),(4,[(2,3,4),(1,1,2),(3,3,15)]),(32,[(2,3,4),(1,1,2),(3,3,15)]),(5,[(1,1,2),(3,3,15)]),(5,[(1,1,2),(2,3,4),(2,15,33)]),(13,[(2,3,4),(2,15,33)]),(23,[(1,1,2),(2,15,33)]),(4,[(1,1,2),(2,3,4),(2,15,33)]),(32,[(1,1,2),(2,3,4),(2,15,33)]),(13,[(3,3,15)]),(4,[(1,1,2),(3,3,15)]),(32,[(1,1,2),(3,3,15)]),(13,[(1,0,16)]),(0,[(1,0,16)]),(32,[(2,1,2),(1,0,16)]),(4,[(2,1,2),(1,0,16)]),(0,[(1,0,16),(0,3,4),(1,0,25)]),(17,[(2,1,2),(1,0,16)]),(23,[(2,1,2),(1,0,16)]),(0,[(1,0,16),(0,3,4)]),(0,[(1,0,16),(0,3,4),(1,3,4)]),(0,[(1,0,16),(1,3,4)]),(0,[(1,0,16),(2,3,4)]),(0,[(0,3,4),(1,3,4),(1,16,25)]),(0,[(0,3,4),(1,3,4),(2,16,25)]),(0,[(1,3,4),(0,3,4),(2,16,25)]),(13,[(1,3,4),(0,3,4),(2,16,25)]),(5,[(2,1,2),(0,3,4),(1,16,25)]),(0,[(0,3,4),(1,16,25)]),(13,[(0,3,4),(1,16,25)]),(4,[(2,1,2),(0,3,4),(1,16,25)]),(32,[(2,1,2),(0,3,4),(1,16,25)]),(5,[(2,1,2),(0,3,4),(2,16,25)]),(0,[(0,3,4),(2,16,25)]),(13,[(0,3,4),(2,16,25)]),(32,[(2,1,2),(0,3,4),(2,16,25)]),(4,[(2,1,2),(0,3,4),(2,16,25)]),(3,[(2,1,2)]),(5,[(2,1,2),(1,3,4),(3,16,28)]),(0,[(1,3,4),(3,16,28)]),(13,[(1,3,4),(3,16,28)]),(17,[(2,1,2),(3,16,28)]),(23,[(2,1,2),(3,16,28)]),(4,[(2,1,2),(1,3,4),(3,16,28)]),(32,[(2,1,2),(1,3,4),(3,16,28)]),(5,[(2,1,2),(2,3,4),(1,16,33)]),(0,[(2,3,4),(1,16,33)]),(13,[(2,3,4),(1,16,33)]),(23,[(2,1,2),(1,16,33)]),(4,[(2,1,2),(2,3,4),(1,16,33)]),(32,[(2,1,2),(2,3,4),(1,16,33)]),(5,[(2,1,2),(2,3,4),(2,16,33)]),(0,[(2,3,4),(2,16,33)]),(13,[(2,3,4),(2,16,33)]),(32,[(2,1,2),(2,3,4),(2,16,33)]),(4,[(2,1,2),(2,3,4),(2,16,33)]),(5,[(2,1,2),(1,3,16)]),(0,[(1,3,16)]),(13,[(1,3,16)]),(4,[(2,1,2),(1,3,16)]),(32,[(2,1,2),(1,3,16)]),(17,[(2,1,2),(3,4,52)]),(5,[(2,1,2),(2,3,16)]),(0,[(2,3,16)]),(13,[(2,3,16)]),(4,[(2,1,2),(2,3,16)]),(32,[(2,1,2),(2,3,16)]),(5,[(2,1,2),(3,3,16)]),(0,[(3,3,16)]),(13,[(3,3,16)]),(4,[(2,1,2),(3,3,16)]),(32,[(2,1,2),(3,3,16)]),(5,[(3,1,2)]),(4,[(3,1,2)]),(32,[(3,1,2)]),(5,[(0,3,4),(3,1,2)]),(17,[(3,1,2)]),(23,[(3,1,2)]),(4,[(0,3,4),(3,1,2)]),(32,[(0,3,4),(3,1,2)]),(5,[(0,3,4),(1,2,25),(3,1,2)]),(0,[(0,3,4),(1,2,25)]),(6,[(0,3,4),(1,2,25)]),(4,[(0,3,4),(1,2,25),(3,1,2)]),(32,[(0,3,4),(1,2,25),(3,1,2)]),(32,[(0,3,4),(1,2,25)]),(5,[(0,3,4),(1,3,4),(3,1,2)]),(4,[(0,3,4),(1,3,4),(3,1,2)]),(32,[(0,3,4),(1,3,4),(3,1,2)]),(2,[(3,1,2)]),(8,[(3,1,2)]),(17,[(3,1,2),(2,28,54)]),(35,[(0,3,4),(1,3,4)]),(5,[(0,3,4),(3,1,2),(1,3,54)]),(23,[(3,1,2),(1,3,54)]),(4,[(0,3,4),(3,1,2),(1,3,54)]),(32,[(0,3,4),(3,1,2),(1,3,54)]),(32,[(3,1,2),(1,3,54)]),(5,[(0,3,4),(3,1,2),(1,25,54)]),(4,[(0,3,4),(3,1,2),(1,25,54)]),(32,[(0,3,4),(3,1,2),(1,25,54)]),(5,[(1,3,4),(3,1,2)]),(3,[(3,1,2)]),(4,[(1,3,4),(3,1,2)]),(32,[(1,3,4),(3,1,2)]),(5,[(1,3,4),(3,1,2),(1,28,54)]),(32,[(1,3,4),(3,1,2),(1,28,54)]),(4,[(1,3,4),(3,1,2),(1,28,54)]),(5,[(1,3,4),(3,1,2),(2,28,54)]),(23,[(3,1,2),(2,28,54)]),(4,[(1,3,4),(3,1,2),(2,28,54)]),(32,[(1,3,4),(3,1,2),(2,28,54)]),(13,[(1,3,4),(1,0,215)]),(5,[(2,3,4),(3,1,2)]),(4,[(2,3,4),(3,1,2)]),(32,[(2,3,4),(3,1,2)]),(5,[(2,3,4),(3,1,2),(1,33,54)]),(23,[(3,1,2),(1,33,54)]),(4,[(2,3,4),(3,1,2),(1,33,54)]),(32,[(2,3,4),(3,1,2),(1,33,54)]),(5,[(3,1,2),(1,3,54)]),(4,[(3,1,2),(1,3,54)]),(32,[(0,2,3),(1,0,19)]),(4,[(0,2,3),(1,0,19)]),(32,[(1,2,3),(0,2,3),(1,0,19)]),(4,[(1,2,3),(0,2,3),(1,0,19)]),(1,[(1,0,19)]),(5,[(1,2,3),(0,2,3),(1,4,65)]),(7,[(1,4,65)]),(13,[(1,4,65)]),(9,[(1,2,3),(0,2,3)]),(6,[(1,2,3),(0,2,3),(1,4,65)]),(23,[(1,2,3),(0,2,3),(1,0,19)]),(35,[(1,4,65)]),(5,[(1,2,3),(0,2,3),(2,4,65)]),(7,[(2,4,65)]),(13,[(2,4,65)]),(6,[(1,2,3),(0,2,3),(2,4,65)]),(25,[(1,2,3)]),(5,[(0,2,3),(1,4,65)]),(17,[(1,4,65)]),(9,[(0,2,3)]),(6,[(0,2,3),(1,4,65)]),(2,[(1,0,19)]),(23,[(0,2,3),(1,0,19)]),(32,[(0,2,3),(1,0,19),(1,4,65)]),(4,[(0,2,3),(1,0,19),(1,4,65)]),(5,[(0,2,3),(2,4,65)]),(17,[(2,4,65)]),(6,[(0,2,3),(2,4,65)]),(13,[(2,4,65),(1,0,72)]),(17,[(2,4,65),(1,0,72)]),(32,[(0,2,3),(1,0,19),(2,4,65)]),(4,[(0,2,3),(1,0,19),(2,4,65)]),(4,[(0,2,3),(2,1,19)]),(13,[(1,0,78)]),(0,[(0,2,3),(1,0,78)]),(17,[(1,0,78)]),(32,[(0,2,3),(2,1,19),(1,0,78)]),(4,[(0,2,3),(2,1,19),(1,0,78)]),(5,[(0,2,3),(1,2,3),(0,1,20)]),(4,[(0,2,3),(1,2,3),(0,1,20)]),(32,[(0,2,3),(1,2,3),(0,1,20)]),(13,[(0,1,20)]),(7,[(1,4,66)]),(13,[(0,1,20),(1,4,66)]),(9,[(0,2,3),(1,2,3)]),(12,[(0,2,3),(1,2,3)]),(1,[(1,4,66)]),(3,[(1,2,3),(0,2,3)]),(7,[(1,4,66),(3,19,195)]),(1,[(1,4,66),(3,19,195)]),(5,[(0,2,3),(1,2,3),(3,1,20)]),(4,[(0,2,3),(1,2,3),(3,1,20)]),(32,[(0,2,3),(1,2,3),(3,1,20)]),(13,[(3,1,20)]),(7,[(1,4,67)]),(13,[(3,1,20),(1,4,67)]),(1,[(1,4,67)]),(35,[(3,1,20),(1,4,67)]),(5,[(0,2,3),(1,2,3),(0,4,20)]),(4,[(0,2,3),(1,2,3),(0,4,20)]),(32,[(0,2,3),(1,2,3),(0,4,20)]),(13,[(0,4,20)]),(7,[(2,1,69)]),(13,[(0,4,20),(2,1,69)]),(1,[(2,1,69)]),(5,[(0,2,3),(1,2,3),(3,4,20)]),(4,[(0,2,3),(1,2,3),(3,4,20)]),(32,[(0,2,3),(1,2,3),(3,4,20)]),(13,[(3,4,20)]),(7,[(2,1,70)]),(13,[(3,4,20),(2,1,70)]),(1,[(2,1,70)]),(7,[(2,1,70),(1,19,229)]),(11,[(1,2,3),(0,2,3)]),(1,[(2,1,70),(1,19,229)]),(5,[(1,2,3),(0,2,3),(3,19,20)]),(4,[(1,2,3),(0,2,3),(3,19,20)]),(32,[(1,2,3),(0,2,3),(3,19,20)]),(0,[(1,2,3),(0,2,3),(3,19,20)]),(6,[(1,2,3),(0,2,3),(3,19,20)]),(7,[(1,1,83)]),(1,[(1,1,83)]),(23,[(1,2,3),(0,2,3),(3,19,20)]),(13,[(1,1,83)]),(0,[(0,2,3),(1,2,3),(3,19,20)]),(7,[(2,1,83)]),(1,[(2,1,83)]),(35,[(2,1,83)]),(13,[(2,1,83)]),(7,[(1,4,83)]),(1,[(1,4,83)]),(35,[(1,4,83)]),(13,[(1,4,83)]),(7,[(2,4,83)]),(1,[(2,4,83)]),(13,[(2,4,83)]),(5,[(0,2,3),(1,4,19)]),(4,[(0,2,3),(1,4,19)]),(32,[(0,2,3),(1,4,19)]),(13,[(3,0,20)]),(17,[(3,0,20)]),(32,[(1,2,3),(3,0,20)]),(4,[(1,2,3),(3,0,20)]),(17,[(0,1,20)]),(4,[(1,2,3),(0,1,20)]),(0,[(1,2,3),(1,0,73)]),(12,[(0,4,85)]),(12,[(1,0,195)]),(12,[(2,4,85)]),(12,[(3,4,85)]),(2,[(1,4,66)]),(5,[(1,2,3),(0,1,20),(1,4,66)]),(9,[(1,2,3)]),(0,[(1,2,3),(1,4,66)]),(17,[(0,1,20),(1,4,66)]),(4,[(1,2,3),(0,1,20),(1,4,66)]),(23,[(1,2,3),(0,1,20)]),(32,[(1,2,3),(0,1,20),(1,4,66)]),(5,[(1,2,3),(3,1,20)]),(17,[(3,1,20)]),(4,[(1,2,3),(3,1,20)]),(32,[(1,2,3),(3,1,20)]),(2,[(1,4,67)]),(5,[(1,2,3),(3,1,20),(1,4,67)]),(17,[(3,1,20),(1,4,67)]),(32,[(1,2,3),(3,1,20),(1,4,67)]),(23,[(1,2,3),(3,1,20)]),(4,[(1,2,3),(3,1,20),(1,4,67)]),(5,[(1,2,3),(0,4,20)]),(17,[(0,4,20)]),(4,[(1,2,3),(0,4,20)]),(32,[(1,2,3),(0,4,20)]),(2,[(2,1,69)]),(5,[(1,2,3),(0,4,20),(2,1,69)]),(0,[(1,2,3),(0,4,20)]),(17,[(0,4,20),(2,1,69)]),(32,[(1,2,3),(0,4,20),(2,1,69)]),(4,[(1,2,3),(0,4,20),(2,1,69)]),(5,[(1,3,4),(1,2,28)]),(17,[(1,2,28)]),(23,[(1,2,28)]),(4,[(1,3,4),(1,2,28)]),(32,[(1,3,4),(1,2,28)]),(5,[(1,2,3),(3,4,20)]),(17,[(3,4,20)]),(4,[(1,2,3),(3,4,20)]),(32,[(1,2,3),(3,4,20)]),(2,[(2,1,70)]),(5,[(1,2,3),(3,4,20),(2,1,70)]),(1,[(2,1,70),(1,0,229)]),(2,[(2,1,70),(1,0,229)]),(26,[]),(0,[(1,2,3),(3,4,20)]),(17,[(3,4,20),(2,1,70)]),(23,[(1,2,3),(2,1,70)]),(32,[(1,2,3),(3,4,20),(2,1,70)]),(4,[(1,2,3),(3,4,20),(2,1,70)]),(17,[(1,0,21)]),(32,[(2,2,3),(1,0,21)]),(4,[(2,2,3),(1,0,21)]),(17,[(2,1,21)]),(4,[(2,2,3),(2,1,21)]),(13,[(1,0,87)]),(0,[(2,2,3),(1,0,87)]),(17,[(2,1,21),(1,0,87)]),(2,[(1,0,87)]),(32,[(2,2,3),(2,1,21),(1,0,87)]),(4,[(2,2,3),(2,1,21),(1,0,87)]),(5,[(2,2,3),(1,4,21)]),(17,[(1,4,21)]),(4,[(2,2,3),(1,4,21)]),(32,[(2,2,3),(1,4,21)])]
def h0Pools : BT (Option BoundPool) := buildPoolsBT 11 h0W h0R h0Slices h0Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice37 : Slice h0R h0G (subcubeFast 48 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h1Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice36 : Slice h0R h0G (subcubeFast 40 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h2Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice35 : Slice h0R h0G (subcubeFast 36 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h3Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice34 : Slice h0R h0G (subcubeFast 33 2) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h4Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice33 : Slice h0R h0G (subcubeFast 32 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h5Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice32 : Slice h0R h0G (subcubeFast 32 0) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h6Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice31 : Slice h0R h0G (subcubeFast 24 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h8Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice30 : Slice h0R h0G (subcubeFast 24 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h9Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice29 : Slice h0R h0G (subcubeFast 20 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h10Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice28 : Slice h0R h0G (subcubeFast 20 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h11Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice27 : Slice h0R h0G (subcubeFast 17 2) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h12Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice26 : Slice h0R h0G (subcubeFast 17 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h13Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice25 : Slice h0R h0G (subcubeFast 16 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h14Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice24 : Slice h0R h0G (subcubeFast 16 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h15Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice23 : Slice h0R h0G (subcubeFast 16 0) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h16Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice22 : Slice h0R h0G (subcubeFast 12 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h17Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice21 : Slice h0R h0G (subcubeFast 12 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h18Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice20 : Slice h0R h0G (subcubeFast 9 2) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h19Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice19 : Slice h0R h0G (subcubeFast 9 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h20Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice18 : Slice h0R h0G (subcubeFast 8 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h21Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice17 : Slice h0R h0G (subcubeFast 8 0) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h22Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice16 : Slice h0R h0G (subcubeFast 5 2) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h23Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice15 : Slice h0R h0G (subcubeFast 5 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h24Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice14 : Slice h0R h0G (subcubeFast 4 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h25Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice13 : Slice h0R h0G (subcubeFast 4 0) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h26Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice12 : Slice h0R h0G (subcubeFast 2 32) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h27Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice11 : Slice h0R h0G (subcubeFast 2 0) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h28Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice10 : Slice h0R h0G (subcubeFast 1 32) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h29Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice9 : Slice h0R h0G (subcubeFast 1 16) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h30Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice8 : Slice h0R h0G (subcubeFast 1 8) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h31Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice7 : Slice h0R h0G (subcubeFast 1 4) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h32Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice6 : Slice h0R h0G (subcubeFast 1 2) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h33Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice5 : Slice h0R h0G (subcubeFast 1 0) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h34Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice4 : Slice h0R h0G (subcubeFast 0 32) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h35Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice3 : Slice h0R h0G (subcubeFast 0 16) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h38Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice2 : Slice h0R h0G (subcubeFast 0 8) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h39Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice1 : Slice h0R h0G (subcubeFast 0 4) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h40Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice0 : Slice h0R h0G (subcubeFast 0 2) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h41Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h0R h0G p.1 p.2) h0Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h0R h0G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h0Slice0) (forall_cons (fun _ h => by cases h; exact h0Slice1) (forall_cons (fun _ h => by cases h; exact h0Slice2) (forall_cons (fun _ h => by cases h; exact h0Slice3) (forall_cons (fun _ h => by cases h; exact h0Slice4) (forall_cons (fun _ h => by cases h; exact h0Slice5) (forall_cons (fun _ h => by cases h; exact h0Slice6) (forall_cons (fun _ h => by cases h; exact h0Slice7) (forall_cons (fun _ h => by cases h; exact h0Slice8) (forall_cons (fun _ h => by cases h; exact h0Slice9) (forall_cons (fun _ h => by cases h; exact h0Slice10) (forall_cons (fun _ h => by cases h; exact h0Slice11) (forall_cons (fun _ h => by cases h; exact h0Slice12) (forall_cons (fun _ h => by cases h; exact h0Slice13) (forall_cons (fun _ h => by cases h; exact h0Slice14) (forall_cons (fun _ h => by cases h; exact h0Slice15) (forall_cons (fun _ h => by cases h; exact h0Slice16) (forall_cons (fun _ h => by cases h; exact h0Slice17) (forall_cons (fun _ h => by cases h; exact h0Slice18) (forall_cons (fun _ h => by cases h; exact h0Slice19) (forall_cons (fun _ h => by cases h; exact h0Slice20) (forall_cons (fun _ h => by cases h; exact h0Slice21) (forall_cons (fun _ h => by cases h; exact h0Slice22) (forall_cons (fun _ h => by cases h; exact h0Slice23) (forall_cons (fun _ h => by cases h; exact h0Slice24) (forall_cons (fun _ h => by cases h; exact h0Slice25) (forall_cons (fun _ h => by cases h; exact h0Slice26) (forall_cons (fun _ h => by cases h; exact h0Slice27) (forall_cons (fun _ h => by cases h; exact h0Slice28) (forall_cons (fun _ h => by cases h; exact h0Slice29) (forall_cons (fun _ h => by cases h; exact h0Slice30) (forall_cons (fun _ h => by cases h; exact h0Slice31) (forall_cons (fun _ h => by cases h; exact h0Slice32) (forall_cons (fun _ h => by cases h; exact h0Slice33) (forall_cons (fun _ h => by cases h; exact h0Slice34) (forall_cons (fun _ h => by cases h; exact h0Slice35) (forall_cons (fun _ h => by cases h; exact h0Slice36) (forall_cons (fun _ h => by cases h; exact h0Slice37) (fun _ h => (List.not_mem_nil h).elim)))))))))))))))))))))))))))))))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h0R h0G c) h0Pools := buildPoolsBT_sound h0SlicesOk
def h0Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G (5 - 1) xs.toFinset) h0Empty := trivial
def h0Block5_0 : List NodeSpec := nodesWithIdentity [([4,5,6,20,65,75],[]),([0,1,2,5,28,115],[]),([2,3,4,5,141,144],[]),([1,2,3,4,151,152],[]),([1,2,5,28,107,196],[]),([1,2,5,28,107,110],[]),([0,1,2,5,28,116],[]),([0,1,2,5,28,117],[]),([0,1,4,5,20,224],[]),([0,1,4,5,20,225],[]),([0,1,4,5,20,231],[]),([0,1,4,5,20,232],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test5_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Empty 5 h0Block5_0 = true := by decide +kernel
def h0Block5_1 : List NodeSpec := nodesWithIdentity [([0,1,5,20,242,247],[]),([0,1,2,3,5,251],[]),([1,2,3,4,85,254],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test5_1 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Empty 5 h0Block5_1 = true := by decide +kernel
def h0Nodes5 : List NodeSpec := h0Block5_0 ++ h0Block5_1
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Check5 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Empty 5 h0Nodes5 = true := by
  unfold h0Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h0Test5_0,h0Test5_1⟩
def h0Bucket5 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 5 xs.toFinset) h0Bucket5 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0EmptyOk h0Check5
def h0Block6_0 : List NodeSpec := nodesWithIdentity [([2,5,6,16,26,28],[12,14,15,16,17,18,19]),([1,4,5,6,20,40,65],[]),([1,4,5,6,20,41,65],[56]),([1,3,5,8,22,92,97],[]),([0,1,2,5,28,48,91],[320,321]),([0,1,2,5,28,118],[82,321,322,323]),([0,1,2,5,28,91,118],[61,323]),([1,2,3,4,5,32,107],[7]),([0,1,2,3,4,5,126],[]),([0,1,2,5,8,28,118],[]),([1,3,4,5,8,49,137],[396,397,398]),([1,3,4,5,8,49,139],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test6_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket5 6 h0Block6_0 = true := by decide +kernel
def h0Block6_1 : List NodeSpec := nodesWithIdentity [([2,3,4,5,58,74,141],[]),([0,2,3,4,5,74,145],[]),([0,2,3,4,5,57,144],[]),([0,1,2,3,4,142,148],[]),([0,1,2,3,4,5,146],[]),([1,2,3,4,41,74,151],[114,456,457,459]),([0,1,2,3,4,61,152],[]),([0,1,2,3,4,41,154],[]),([0,1,2,3,4,5,155],[114]),([0,1,2,3,4,5,157],[]),([0,1,2,3,4,63,164],[]),([0,1,2,3,4,5,167],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test6_1 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket5 6 h0Block6_1 = true := by decide +kernel
def h0Block6_2 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,170],[]),([0,1,2,3,4,74,173],[]),([1,2,3,4,5,74,175],[23]),([0,1,2,3,4,5,176],[]),([1,2,4,12,28,107,120],[55,596]),([1,2,3,4,12,107,124],[310,589,590,594,599]),([1,2,3,4,12,107,125],[]),([1,2,3,4,12,107,183],[]),([0,1,2,13,28,192],[24,662,663,664,665,666]),([0,1,2,3,4,13,127],[]),([1,2,5,26,28,107],[24,28,61,315,321,379]),([1,2,5,25,28,32,107],[29])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test6_2 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket5 6 h0Block6_2 = true := by decide +kernel
def h0Block6_3 : List NodeSpec := nodesWithIdentity [([0,1,2,5,28,48,107],[86,321]),([0,1,2,5,28,119],[24,82,321,322]),([0,1,2,5,28,107,119],[61,82,86]),([1,2,3,4,12,32,107],[588,589,590,594]),([1,2,3,4,13,32,107],[648]),([1,2,5,11,28,107,120],[55,82]),([0,1,2,5,28,120,122],[55,82]),([0,1,2,5,28,120,123],[61,113]),([1,2,4,5,28,107,197],[]),([1,2,3,4,5,107,128],[0,310]),([1,2,3,4,5,107,127],[0]),([1,2,3,5,11,28,107],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test6_3 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket5 6 h0Block6_3 = true := by decide +kernel
def h0Block6_4 : List NodeSpec := nodesWithIdentity [([1,2,3,4,5,11,131],[7]),([0,1,2,3,5,123,183],[]),([1,2,3,5,11,107,183],[]),([1,2,3,4,5,107,193],[7]),([1,2,3,5,11,107,184],[]),([0,1,2,5,16,28,48],[]),([0,1,5,14,28,48,111],[321]),([0,1,2,5,28,200],[61,750]),([0,1,2,5,28,48,200],[]),([1,2,3,4,5,127,185],[]),([0,1,2,5,28,206],[24,61,747,811]),([0,1,2,5,28,48,206],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test6_4 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket5 6 h0Block6_4 = true := by decide +kernel
def h0Block6_5 : List NodeSpec := nodesWithIdentity [([0,2,3,4,5,204,209],[23]),([1,2,5,17,26,28],[12,15,28,61,315,321]),([0,1,2,5,17,28,48],[]),([0,1,2,5,18,28,48],[]),([0,1,5,16,28,48,111],[747]),([0,1,5,16,28,48,112],[321]),([0,1,2,5,28,48,198],[]),([0,1,2,5,28,48,199],[748,749]),([0,1,2,5,28,48,216],[813]),([1,4,5,20,65,220],[55,56,57,82,981,986]),([0,1,4,5,20,223],[32,1018,1019,1020]),([0,1,4,5,20,195,223],[7,1018])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test6_5 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket5 6 h0Block6_5 = true := by decide +kernel
def h0Block6_6 : List NodeSpec := nodesWithIdentity [([0,1,4,5,19,20,228],[81,1033]),([0,1,4,5,19,20,230],[7,81,1040]),([0,1,4,5,20,233],[82,1043,1044,1045]),([0,1,4,5,20,229,233],[7]),([0,1,4,5,20,234,236],[86,206]),([0,1,4,5,20,83,240],[]),([0,1,4,5,20,83,243],[45,1056]),([0,1,4,5,20,83,244],[]),([0,1,4,5,20,235,242],[32]),([0,1,4,5,20,83,247],[32]),([0,1,4,5,20,83,237],[1047,1048]),([0,1,4,5,20,83,238],[45,1047,1048,1060])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test6_6 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket5 6 h0Block6_6 = true := by decide +kernel
def h0Block6_7 : List NodeSpec := nodesWithIdentity [([0,1,4,5,20,83,239],[206]),([0,1,4,20,83,236,241],[1047]),([0,1,4,5,20,83,245],[45,1064]),([0,1,4,5,20,83,246],[]),([0,1,2,3,5,221,248],[468]),([0,1,2,3,4,85,250],[310]),([1,2,3,4,5,85,222],[0,310]),([0,1,2,3,4,85,249],[102,468]),([1,2,3,4,5,85,255],[0]),([0,1,2,3,5,252,253],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test6_7 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket5 6 h0Block6_7 = true := by decide +kernel
def h0Nodes6 : List NodeSpec := h0Block6_0 ++ h0Block6_1 ++ h0Block6_2 ++ h0Block6_3 ++ h0Block6_4 ++ h0Block6_5 ++ h0Block6_6 ++ h0Block6_7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Check6 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket5 6 h0Nodes6 = true := by
  unfold h0Nodes6 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨h0Test6_0,h0Test6_1⟩,h0Test6_2⟩,h0Test6_3⟩,h0Test6_4⟩,h0Test6_5⟩,h0Test6_6⟩,h0Test6_7⟩
def h0Bucket6 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 6 xs.toFinset) h0Bucket6 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0Bucket5Ok h0Check6
def h0Block7_0 : List NodeSpec := [([2,3,4,5,6,16,26],[11,12,13,18,19,20,21,22,23],[0]),([0,2,5,6,16,25,28],[15,16,17,20,26,27,28,29,30],[0]),([0,2,3,4,5,6,16,30],[3,4,23,30,34],[0]),([1,4,5,6,20,65],[7,32,45,55,56,57,58,59,60],[0,3]),([0,1,4,5,19,20,43],[7,32,67,68,72,73,74,75,76,77,78,79,80,81,82],[0]),([0,1,4,5,19,73],[4,32,45,68,82,83,84,85,86],[0]),([0,2,5,7,16,25,28],[17,24,26,27,28,29,161,162,163],[0]),([0,1,4,5,19,20,81],[7,60,72,73,75,76,78,79,80,81,82,175],[0]),([1,3,4,5,8,22,92],[7,18,193,195,196,201,202,203,204,205,206],[0]),([1,3,4,5,8,23,92],[7,18,44,60,195,196,203,204,207,208,209],[0]),([1,2,3,4,5,92,94],[23,61,203,206,210,211,212,213],[0]),([1,2,3,4,5,92,95],[18,23,61,193,203,212,213,214,215,216],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Block7_0 = true := by decide +kernel
def h0Block7_1 : List NodeSpec := nodesWithIdentity [([1,2,3,4,5,8,92,96],[44,195,196,203,205,217]),([1,2,3,4,5,8,92,97],[195,203,218]),([0,1,3,4,5,22,99],[7,55,113,206,233,234,235]),([0,1,3,4,5,22,55,99],[81,228,236]),([0,1,3,4,5,8,100],[0,7,55,81,206,219,237,238]),([0,1,3,4,5,8,55,100],[81,202,237]),([0,1,3,4,5,8,101],[0,7,55,81,194,208,209,219,245]),([0,1,2,4,5,55,102],[1,198,223,253,254]),([0,1,2,3,4,5,103],[0,1,7,23,61,81,102,114,115,206,266]),([0,1,2,3,4,5,55,103],[1,23,81,223]),([0,1,2,3,4,5,94,103],[61,81,102,206,211,256,260]),([0,1,2,3,4,5,104],[0,1,7,23,61,81,82,91,114,115,216,274,275])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_1 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Block7_1 = true := by decide +kernel
def h0Block7_2 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,55,104],[102]),([0,1,2,3,4,5,94,106],[23]),([0,1,2,5,25,28,91],[24,27,28,29,61,91,162,315,316,317,318,319,321]),([0,1,2,3,4,5,118],[0,1,23,24,61,81,82,113,114,115,160,181,328,329]),([0,1,2,3,4,5,91,118],[61,160,329]),([0,1,2,3,4,5,32,91],[7,23,28,81,91,102,190,314,331,332]),([0,1,2,3,4,5,45,91],[7,23,35,44,91,102,190,321,333,334]),([0,1,2,3,4,5,91,113],[23,166,190,321,324,325]),([0,1,2,3,4,5,91,114],[23,91,166,190]),([0,1,2,3,4,5,28,91],[23,35,61,91,113,166,190,321]),([0,1,2,3,4,5,130],[0,1,23,24,61,81,82,91,113,114,115,167,344]),([0,1,2,3,4,5,91,130],[61,81,167,190])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_2 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Block7_2 = true := by decide +kernel
def h0Block7_3 : List NodeSpec := nodesWithIdentity [([0,1,2,5,8,25,28,91],[27,28,162,198,317,346]),([0,1,2,3,4,5,8,118],[1,61,81,154,219]),([0,1,2,3,4,5,8,114],[1,81,154,219]),([0,1,2,3,4,5,8,130],[1,61,81,154,219]),([0,1,2,3,4,5,8,135],[1,81,114,154,219]),([0,1,2,5,25,27,28],[15,18,27,91,162,317,318,319,321,377,378,379]),([0,1,2,5,25,28,132],[27,28,29,91,162,198,317,318,319,321,380,381]),([1,2,3,4,5,8,49],[7,23,197,310,330,395,396,397,398]),([0,1,2,3,4,5,109,138],[23,34,55,91,102,401,402]),([0,1,2,3,4,5,109,140],[23,34,81]),([0,2,3,4,5,57,58,74],[1,102,113]),([0,1,2,3,4,5,59,74],[23,81,108,113,433])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_3 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Block7_3 = true := by decide +kernel
def h0Block7_4 : List NodeSpec := [([0,1,2,3,4,74,142],[1,102,114,429,434,435,436,437,438],[0]),([0,1,2,3,4,74,143],[1,102,115,429,440,441,442,443,444,445],[0]),([0,1,2,3,4,5,144],[0,1,23,81,82,91,113,114,115,429],[0]),([0,1,2,3,4,5,74,144],[1,431],[0]),([0,2,3,4,5,59,60,74],[23,108],[0]),([0,1,2,3,4,5,57,74],[1,23,57,81,91,113,427,428,451],[0,3]),([0,1,2,3,4,5,150],[0,1,23,81,82,91,113,114,115,429],[0]),([0,1,2,3,4,5,74,150],[1,449],[0]),([1,2,3,4,5,74,151],[23,82,114,429,439,454,455,456,457,458,460],[0]),([0,1,2,3,4,5,74,151],[23,57,81,82,114,454,461,462],[0]),([0,1,2,3,4,41,61,74],[114,115,459,464,465,467],[0]),([0,1,2,3,4,5,74,147],[81,102,429,438,439,468],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_4 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Block7_4 = true := by decide +kernel
def h0Block7_5 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,74,76],[23,81,113,114,467,469,470]),([0,1,2,3,4,5,154],[0,1,81,82,91,102,113,114,115,439,454]),([0,1,2,3,4,5,61,154],[1,81,114,115]),([0,1,2,3,4,5,74,154],[57,81,82,91,114,427,428]),([0,1,2,3,4,5,74,156],[81,113,476]),([0,1,2,3,4,5,74,158],[81,102,108,477]),([0,1,2,3,4,5,159],[0,23,81,82,91,102,113,114,115,429,478]),([0,1,2,3,4,5,74,159],[115,474]),([0,1,2,3,4,5,74,160],[57,81,115,445,479,480]),([0,1,2,3,4,39,63,74],[114,115,445,485,486]),([0,1,2,3,4,5,74,149],[81,102,429,444,487]),([0,1,2,3,4,5,74,163],[81,113,115,486,488])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_5 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Block7_5 = true := by decide +kernel
def h0Block7_6 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,74,165],[115]),([0,1,2,3,4,5,74,168],[81,102,468,492]),([0,1,2,3,4,5,74,169],[1,81,91,113,427,428,493,494]),([0,1,2,3,4,5,74,171],[114,490]),([0,1,2,3,4,5,74,161],[57,81,82,113,114,495,496,497]),([0,1,2,3,4,5,74,162],[23,81,108,113,114,499,500]),([0,1,2,3,4,39,40,74],[102,113,115,468]),([0,1,2,3,4,5,164],[0,1,23,81,82,91,114,115,439,495]),([0,1,2,3,4,5,39,164],[81,114,115,498]),([0,1,2,3,4,5,74,164],[114,498]),([0,1,2,3,4,5,74,172],[57,81,115,468,504]),([0,1,2,3,4,5,68,74],[23,57,81,91,427,428,506])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_6 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Block7_6 = true := by decide +kernel
def h0Block7_7 : List NodeSpec := [([0,1,2,3,4,5,74,174],[115,505],[0]),([0,1,2,3,4,5,74,153],[57,81,82,115,509,510],[0]),([0,1,2,3,4,5,74,75],[23,81,108,115,467,512],[0]),([0,1,2,3,4,41,42,74],[114,487],[0]),([0,1,2,3,4,5,152],[0,1,23,81,82,86,91,114,115,509,514],[0]),([0,1,2,3,4,5,74,152],[81,91,115,427,428],[0]),([0,1,2,3,4,5,74,177],[57,81,82,102,114,515,516],[0]),([0,1,2,3,4,5,74,166],[23,81,102,444,445,518],[0]),([0,1,2,3,4,5,74,178],[114],[0]),([0,1,2,5,25,28,179],[27,28,29,61,82,91,162,315,318,319,321,557,560,561,562],[0]),([0,1,2,3,4,5,109,182],[7,401,402],[0]),([1,2,3,4,12,28,107],[55,86,310,337,588,589,590,591,592,593,594,595,596,597,598],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_7 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Block7_7 = true := by decide +kernel
def h0Block7_8 : List NodeSpec := nodesWithIdentity [([1,2,3,4,12,107,120],[24,45,55,86,310,589,590,594,595,596,599,600,601,602,603]),([0,1,2,12,16,25,28],[15,17,24,26,28,315,319,614,615,619,623,627,628,629,630,631]),([0,1,2,13,14,25,28],[28,315,318,608,654,657,658,659,660,661,664,666,667,668]),([0,1,2,3,4,13,192],[0,24,114,648,649,650,654,664,667,669,671,674,675,676,677]),([0,1,2,3,4,13,188],[0,114,648,649,650,656,666,667,671,677,681,682]),([0,1,2,3,4,13,14,188],[668]),([0,1,2,3,4,13,194],[0,24,114,648,649,650,654,664,667,668,677,689,690]),([0,1,2,13,16,25,28],[15,17,24,26,28,315,318,627,659,660,661,666,667,668,691]),([1,2,3,4,5,26,107],[7,10,23,24,61,82,113,206,309,310,383,705]),([0,1,2,5,25,28,107],[24,27,28,29,61,82,86,91,162,315,316,318,319,321,631]),([0,1,2,3,4,5,119],[1,23,24,61,81,82,91,102,113,114,115,206,328,329]),([0,1,2,3,4,5,107,119],[61,82,86,190,706])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_8 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Block7_8 = true := by decide +kernel
def h0Block7_9 : List NodeSpec := [([1,2,3,4,5,10,28,107],[24,36,55,61,82,309,321],[0]),([0,1,2,3,4,5,32,107],[7,23,91,190,321,706],[0]),([1,2,3,4,5,28,32,107],[24,36,181,309,321],[0]),([0,1,2,3,4,5,45,107],[7,91,321,330],[0]),([0,1,2,4,5,28,107,120],[55,61,82,91,206],[0]),([0,1,2,4,5,28,107,121],[55,82,86,91,321],[0,1,5]),([0,1,2,3,4,5,107,124],[23,190,310,321,599,706],[0]),([0,1,2,3,4,5,107,125],[91],[0]),([1,2,3,4,5,11,33,107],[42,45,55,181,309,707],[0]),([1,2,3,4,5,50,107],[7,23,24,61,82,102,309,310,708,709],[0]),([0,1,2,4,5,33,107,120],[55,61,82,86],[0]),([0,1,2,3,4,5,28,107],[36,55,91,309,321],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_9 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Block7_9 = true := by decide +kernel
def h0Block7_10 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,131],[1,23,61,81,82,91,113,114,115,344]),([0,1,2,3,4,5,107,131],[61,82,86]),([0,1,2,3,4,5,120,122],[61,82,91,102,113,206,713,714]),([0,1,2,3,4,5,120,123],[61,82,91,113,715]),([0,1,2,3,4,5,107,183],[61,82,102,113,309]),([1,2,3,4,5,107,197],[0,7,23,24,55,61,82,309,310,719,721,722,723]),([0,1,2,3,4,5,107,184],[86,91,102,113,309,321]),([0,1,2,5,14,26,28],[14,18,24,28,82,315,321,379,608,657,729,732,733,734,735]),([0,1,2,5,16,25,28],[16,26,27,28,29,61,91,162,315,318,319,321,726]),([0,1,2,5,28,192],[82,86,321,323,662,663,729,741,742,743,744,745]),([0,1,2,5,14,28,48],[82,91,320,321,608,729,746,747,748,749,751]),([0,1,2,3,4,5,14,125],[44])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_10 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Block7_10 = true := by decide +kernel
def h0Block7_11 : List NodeSpec := [([0,1,2,3,4,5,127],[1,7,23,81,91,102,114,115,321,618],[0]),([0,1,2,3,4,5,14,127],[0,1,7,23,81,91],[0,3]),([0,1,2,5,28,203],[16,24,86,321,797,805,806,807,808,809,810],[0]),([0,1,2,5,15,28,48],[16,91,320,321,746,747,748,749,797,811,812,813],[0]),([0,1,2,3,4,5,208],[1,7,23,81,91,102,114,115,321,330,822,828],[0]),([0,2,3,4,5,14,15,204],[7,23],[0]),([0,1,2,3,4,5,16,204],[7,23],[0]),([0,1,2,3,4,201,204],[1,114,794,805,806,831,832,833,834,835,836],[0]),([0,1,2,3,4,5,201,204],[114,115,310,794],[0]),([0,1,2,3,4,202,204],[1,115,795,805,806,837,838,839,840,841,842],[0]),([0,1,2,3,4,5,202,204],[114,115,599,795],[0]),([0,1,2,3,4,5,204,205],[1,34],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_11 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Block7_11 = true := by decide +kernel
def h0Block7_12 : List NodeSpec := nodesWithIdentity [([1,2,3,4,5,17,26],[10,12,13,23,61,81,113,865,866,867]),([0,1,2,5,17,25,28],[15,17,24,26,27,28,29,61,91,162,317,318,319,321,866,869]),([0,1,2,5,16,26,28],[12,14,15,17,18,24,26,28,315,321,379,726,733,734,735]),([0,1,2,5,25,28,46],[24,27,28,29,91,162,318,319,321,726,872]),([0,1,2,5,25,28,47],[15,16,28,91,162,317,318,319,321,726,873,874,875]),([0,1,2,5,16,25,28,31],[91,162]),([0,1,2,5,16,28,48],[17,91,320,321,726,746,747,748,749]),([0,1,2,5,28,48,54],[91,320,321,746,747,748,749,811,813,925,939]),([0,1,2,5,25,215],[16,24,27,29,315,321,940,941]),([0,1,2,3,4,5,218],[1,7,23,81,91,102,114,115,321,330,957,961]),([0,1,4,5,20,65,71],[55,56,60,82,206,973,974,975,976,977,978,979,980,981,982]),([0,1,4,5,20,65,72],[55,56,60,82,973,974,975,979,981,983,984,985,986,987])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_12 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Block7_12 = true := by decide +kernel
def h0Block7_13 : List NodeSpec := [([1,2,3,4,5,65,220],[0,7,49,51,55,61,113,993,996,998,999,1000],[0]),([0,1,4,5,19,20,195],[7,67,68,71,76,78,79,80,82,1013,1014,1015,1016,1017],[0]),([0,1,4,5,19,20,226],[7,32,67,68,71,75,76,78,79,80,82,1025,1026,1027,1028],[0]),([0,1,4,5,19,20,227],[7,67,68,71,76,79,80,82,1033,1034,1035],[0]),([0,1,4,5,19,20,229],[7,67,68,71,76,78,79,80,81,82,1040,1041,1042],[0]),([0,1,4,5,20,83,234],[7,32,81,82,86,1046,1047,1048,1049,1050,1051,1052,1053,1054,1055],[0]),([0,1,4,5,20,83,235],[7,81,82,1046,1047,1048,1049,1053,1056,1057,1058,1059],[0,3]),([0,1,4,5,20,83,236],[7,81,82,86,1046,1047,1048,1049,1053,1060,1061,1062,1063],[0,3]),([0,1,4,5,20,83,242],[7,81,82,86,206,987,1046,1047,1048,1049,1053,1064,1065,1066],[0,3]),([0,1,2,3,4,5,85,248],[4,23,30,82,102,113,128,310,1077],[0,3]),([0,1,2,3,4,5,85,221],[4,23,30,102,113,310,1076,1078],[0]),([0,1,2,3,4,5,85,252],[102,113,1079],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_13 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Block7_13 = true := by decide +kernel
def h0Block7_14 : List NodeSpec := [([0,1,2,3,4,5,85,253],[23,102,113,128,1080],[0,3]),([0,1,2,3,4,5,20,228],[1,46,81,108,1033],[0]),([0,1,2,3,4,5,20,230],[1,7,61,81,82,91,1040,1119,1120,1121,1122],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_14 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Block7_14 = true := by decide +kernel
def h0Nodes7 : List NodeSpec := h0Block7_0 ++ h0Block7_1 ++ h0Block7_2 ++ h0Block7_3 ++ h0Block7_4 ++ h0Block7_5 ++ h0Block7_6 ++ h0Block7_7 ++ h0Block7_8 ++ h0Block7_9 ++ h0Block7_10 ++ h0Block7_11 ++ h0Block7_12 ++ h0Block7_13 ++ h0Block7_14
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Check7 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Nodes7 = true := by
  unfold h0Nodes7 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0Test7_0,h0Test7_1⟩,h0Test7_2⟩,h0Test7_3⟩,h0Test7_4⟩,h0Test7_5⟩,h0Test7_6⟩,h0Test7_7⟩,h0Test7_8⟩,h0Test7_9⟩,h0Test7_10⟩,h0Test7_11⟩,h0Test7_12⟩,h0Test7_13⟩,h0Test7_14⟩
def h0Bucket7 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 7 xs.toFinset) h0Bucket7 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0Bucket6Ok h0Check7
def h0Block8_0 : List NodeSpec := [([0,2,3,4,5,6,16,25],[1,2,3,4,5,6,8,9,10,13,16,20,21,23,24,25,30,31,32],[0]),([0,2,3,4,5,6,16,28],[1,2,3,4,5,6,17,20,21,23,30,31,32,33,34,35,36,37],[0]),([0,2,3,4,5,6,16,33],[1,2,3,4,5,6,16,17,20,21,23,30,31,32,38,39,40,41,42,43],[0]),([1,2,3,4,5,6,65],[3,7,23,49,51,52,53,54,55,60,61],[0,3]),([0,2,3,4,5,6,78],[0,1,3,7,23,31,50,52,55,61,64,65,66],[0]),([0,1,4,5,6,19,20],[3,4,7,32,45,67,68,69,70,71,79,80,81],[0,3]),([0,1,3,4,5,19,24],[1,3,32,45,50,81,87,88,89,90,91,92,93],[0]),([0,1,2,3,4,5,19,43],[1,7,32,49,50,60,61,74,81,91,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109],[0]),([0,1,2,3,4,5,84],[0,1,3,7,23,32,50,52,61,102,110,111,112,113,114,115],[0]),([0,1,2,3,4,5,20,43],[1,7,61,73,74,81,82,91,96,99,100,102,103,104,105,108,116,117,121,122,123,124,125,126,127],[0]),([0,1,2,3,4,5,73],[0,1,4,7,23,30,61,82,84,102,113,114,115,117,128,129,130,131],[0]),([0,1,2,3,4,5,6,73],[0,1,3,4,23,31,47,48,52,81,103,117,128,129,130],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_0 = true := by decide +kernel
def h0Block8_1 : List NodeSpec := [([0,2,3,4,5,6,87],[0,1,3,7,23,30,31,44,91,133,136,137,138,139],[0]),([0,1,2,3,4,5,21,43],[1,7,32,61,73,74,81,91,96,99,100,102,103,104,105,108,132,133,141,142,143,144,145,146,147,148],[0]),([0,1,2,3,4,5,90],[0,1,3,7,23,30,32,81,102,113,114,115,133,149,150,151,152],[0]),([0,2,3,4,5,7,16,25],[2,8,9,10,23,24,25,32,60,154,156,157,158,159,160,161,163,164,165],[0]),([0,2,3,4,5,7,16,28],[2,17,23,32,33,34,35,36,154,156,157,158,159,161,163,164,165,166],[0]),([0,2,3,4,5,7,16,33],[2,17,23,24,32,38,39,40,41,42,60,154,156,157,158,159,161,163,164,165,167],[0]),([0,1,4,5,7,19,20],[7,45,60,67,68,71,75,76,79,80,81,156,157,173,174],[0,3]),([0,1,2,3,4,5,19,81],[7,23,60,61,73,81,91,95,96,97,98,102,106,107,109,142,176,177,178,179,180,181],[0]),([0,1,2,3,4,5,20,81],[7,23,61,73,81,82,91,96,102,121,122,123,125,126,127,142,177,178,179,180,181,185],[0]),([0,1,2,3,4,5,21,81],[7,23,60,61,73,81,91,96,102,141,142,143,144,146,147,148,177,178,179,180,181,188],[0]),([1,2,3,4,5,8,92],[7,18,23,60,61,193,195,196,197,198,199,200,203,213],[0]),([0,1,3,4,5,8,22,55],[55,81,193,194,202,206,219,222,223,224,225,226,227,228,229,230,231,232],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_1 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_1 = true := by decide +kernel
def h0Block8_2 : List NodeSpec := nodesWithIdentity [([0,1,3,4,5,8,23,55],[7,44,55,60,81,82,193,194,208,209,219,223,227,228,229,230,239,240,241,242,243,244]),([0,1,2,4,5,55,93],[1,81,91,198,223,246,247,248,249,250,251,252]),([0,1,2,3,4,5,55,94],[1,23,61,81,91,102,211,223,230,255,256,257,258,259,260,261,262,263,264,265]),([0,1,2,3,4,5,55,95],[1,23,60,61,81,91,102,193,194,215,216,223,230,261,264,265,267,268,269,270,271,272,273]),([0,1,2,3,4,5,55,98],[1,18,23,55,91,195,198,223,228,258,261,264,265,278]),([0,1,2,3,4,5,99],[0,1,7,23,55,81,102,113,114,115,197,198,223,234,279,280,281,282]),([0,1,2,3,4,5,55,99],[1,23,81,91,193,194,198,223,228,234,261,264,265,279,280,281,282]),([0,1,3,4,5,8,22,56],[24,55,81,202,206,219,224,225,226,227,229,230,231,232,283,284,287,288,289,290,291]),([0,1,3,4,5,8,23,56],[7,24,55,60,81,208,219,227,229,230,240,241,242,243,244,283,284,287,289,291,292,293,294]),([0,1,2,3,4,5,56,94],[1,16,23,61,81,91,102,211,230,256,257,259,260,262,263,287,295,296,297,298,299,300]),([0,1,2,3,4,5,56,95],[1,16,23,60,61,81,91,102,215,216,230,268,269,270,271,272,273,283,284,287,297,298,299,301,302]),([0,1,2,3,4,5,105],[0,1,7,55,61,102,113,114,115,197,227,287,303,304,305,306,307,308])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_2 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_2 = true := by decide +kernel
def h0Block8_3 : List NodeSpec := [([0,1,2,3,4,5,25,91],[9,10,23,24,25,61,81,91,102,113,160,181,190,309,311,312,313,314,324,325,326,327],[0]),([0,1,2,3,4,5,28,91],[23,24,34,35,36,61,81,91,102,113,166,181,190,309,314,321,324,325,330,335,336,337,338],[0]),([0,1,2,3,4,5,33,91],[23,24,39,40,42,55,61,81,91,102,113,167,181,190,309,314,324,325,339,340,341,342,343],[0]),([0,1,2,3,4,5,8,25,91],[9,10,55,81,160,197,198,313,345],[0]),([0,1,2,3,4,5,8,28,91],[34,35,55,81,166,197,198,219,227,229,230,336,347],[0]),([0,1,2,3,4,5,8,33,91],[39,40,44,55,81,167,197,198,341,348],[0]),([0,1,2,3,4,5,8,34,91],[55,81,197,276,324,349,350,351,352],[0]),([0,1,2,3,4,5,8,35,91],[55,81,86,197,276,277,324,354,355,356,357],[0]),([0,1,3,4,5,8,136],[0,7,55,60,81,219,227,229,362,363,364,365,366],[0]),([0,1,2,3,4,5,8,26],[0,7,10,61,81,197,198,219,230,276,277],[0]),([0,1,2,3,4,5,8,108],[0,7,9,16,23,24,55,61,81,113,197,198,219,230,276,277,345,369,370,371,372,373,374],[0]),([0,1,2,5,8,25,28],[27,28,29,44,61,91,198,227,315,317,318,319,375,376],[0,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_3 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_3 = true := by decide +kernel
def h0Block8_4 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,25,27],[9,13,18,55,61,91,102,113,160,313,326,327,378,382,383,384,385]),([0,1,2,3,4,5,132],[0,1,7,23,55,61,81,113,114,115,198,230,313,386,387,388,389,390]),([0,1,2,3,4,5,25,132],[9,10,25,61,81,91,102,113,160,198,313,326,327,386,387,389,390]),([0,1,2,3,4,5,8,109],[0,7,23,34,44,55,81,91,102,197,198,219,227,229,230,276,277,330,347,393,394,399,400,401,402]),([0,1,2,3,4,5,133],[0,1,7,23,55,61,113,114,115,227,229,336,403,404,405,406,407,408,409]),([0,1,2,3,4,5,8,129],[0,7,16,23,39,46,55,61,81,102,197,198,219,229,276,277,348,412,413,414,415,416,417]),([0,1,2,3,4,5,134],[0,1,7,23,55,61,81,91,113,114,115,198,229,341,418,419,420,421,422,423]),([0,1,2,3,4,5,58,74],[1,23,57,60,81,86,91,102,113,427,428,429,430,431,432,439,446,447]),([0,1,2,3,4,5,60,74],[1,23,57,60,81,86,91,102,113,427,428,429,439,448,449,450,452,453]),([0,1,2,3,4,5,61,74],[1,23,57,81,86,91,114,115,427,428,429,439,454,463,464,465,466,471,472]),([0,1,2,3,4,5,62,74],[1,23,57,60,81,86,91,114,115,427,428,429,439,473,474,475,476,477]),([0,1,2,3,4,5,63,74],[1,23,57,81,86,91,114,115,427,428,429,439,445,479,481,482,483,484,485,486])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_4 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_4 = true := by decide +kernel
def h0Block8_5 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,64,74],[1,23,57,81,91,114,115,310,427,428,429,439,489,490,491,492,494]),([0,1,2,3,4,5,39,74],[57,81,86,91,102,113,114,115,427,428,429,439,495,498,501,502,503]),([0,1,2,3,4,5,40,74],[57,81,86,91,102,113,114,115,427,428,429,439,468,504,505,506,507,508]),([0,1,2,3,4,5,41,74],[57,81,86,91,102,113,114,115,427,428,429,439,459,467,509,511,513]),([0,1,2,3,4,5,42,74],[57,81,86,91,102,113,114,115,427,428,429,439,487,515,517,519,520,521]),([0,1,3,4,5,9,22,55],[7,45,81,82,193,194,206,222,224,225,228,258,527,531,532,533,534,535,536,537]),([0,1,2,3,4,5,55,181],[1,7,23,45,61,82,91,102,193,194,206,223,258,261,264,265,535,538,539,540,541,542,543,544,545]),([0,1,3,4,5,9,22,56],[7,45,81,206,224,225,283,284,288,289,290,296,527,531,532,533,534,535,536,537,550]),([0,1,2,3,4,5,56,181],[1,7,16,23,61,91,102,206,283,284,287,296,297,298,299,535,539,540,541,542,543,544,545,551,552]),([0,1,2,3,4,5,25,179],[7,9,10,23,24,25,32,61,82,91,102,113,160,311,326,327,527,553,554,555,556,557,558,559,563]),([0,1,2,3,4,5,28,179],[7,23,32,34,35,36,61,91,102,113,166,321,330,337,338,527,553,554,555,557,559,561,563,564,565]),([0,1,2,3,4,5,33,179],[7,23,32,39,40,42,45,61,82,91,102,113,167,339,342,343,527,553,554,555,557,559,561,563,566,567,568])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_5 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_5 = true := by decide +kernel
def h0Block8_6 : List NodeSpec := [([0,1,2,3,4,5,9,26],[0,7,10,61,81,526,527,528,535,546,547],[0]),([0,1,2,3,4,5,9,108],[0,7,9,16,23,24,45,61,81,113,369,370,371,372,373,374,526,527,528,535,546,547,573],[0]),([0,1,2,5,9,25,28],[27,28,29,44,61,82,91,315,318,319,526,533,574,575],[0]),([0,1,2,3,4,5,9,109],[0,7,23,34,44,45,81,91,102,393,394,399,400,401,402,526,527,528,533,534,535,546,547,578],[0]),([0,1,2,3,4,5,9,129],[0,7,16,23,39,45,46,61,81,102,412,413,414,415,416,417,526,527,528,534,546,547,581],[0]),([1,2,3,4,12,107],[55,86,114,309,310,588,589,590,597],[0,1]),([0,1,2,3,4,12,14,28],[35,86,330,338,586,588,590,592,593,598,604,605,606,607,608,609,610,611,612,613,614,615,616,617,618,619],[0]),([0,1,2,3,4,12,16,25],[2,8,10,13,24,60,311,327,588,590,598,604,611,614,615,616,617,621,622,623,624,625,626,632,633,634],[0]),([0,1,2,3,4,12,16,28],[2,17,33,35,37,60,330,338,588,590,592,593,598,604,609,611,614,615,616,617,619,621,623,632,634,635,636],[0]),([0,1,2,3,4,12,16,33],[2,17,24,38,40,41,43,60,339,343,588,590,598,604,611,614,615,616,617,621,623,632,634,637,638,639,640,641],[0]),([0,1,2,3,4,12,65],[0,49,114,115,588,590,604,615,616,617],[0]),([0,1,4,12,19,20],[45,67,75,79,80,588,597,611],[0,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_6 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_6 = true := by decide +kernel
def h0Block8_7 : List NodeSpec := [([0,1,2,3,4,12,189],[0,107,114,115,588,590,604,615,616,617,642,643],[0]),([0,1,2,3,4,12,190],[0,114,115,127,588,590,604,611,615,616,617,644,645],[0]),([0,1,2,3,4,12,191],[0,114,115,147,588,590,604,611,614,616,617,646,647],[0]),([0,1,2,3,4,13,14,25],[10,24,311,326,586,587,648,649,650,651,652,653,654,655,656,664,667,668,669,670,671,672,673],[0]),([0,1,2,3,4,13,14,28],[35,330,337,586,587,606,607,608,648,649,650,654,656,666,667,668,669,670,671,673,678,679,680],[0]),([0,1,2,3,4,13,14,33],[40,44,45,339,342,586,587,608,648,649,650,654,656,664,667,668,669,670,671,673,683,684,685,686,687,688],[0]),([0,1,2,3,4,13,16,25],[2,8,10,13,24,60,311,326,620,622,648,649,650,653,655,656,667,668,670,671,672,691,692,693,694],[0]),([0,1,2,3,4,13,16,28],[2,17,33,35,37,60,330,337,620,635,648,649,650,656,666,667,668,670,671,678,679,680,691,692,693,694],[0]),([0,1,2,3,4,13,16,33],[2,17,24,38,40,41,43,60,339,342,620,637,648,649,650,656,667,668,670,671,685,687,688,691,692,693,694],[0]),([0,1,2,3,4,13,65],[0,49,114,115,648,649,650,667,670,671],[0]),([0,1,2,3,4,13,78],[0,60,64,114,648,649,650,667,670,671,677,695,696],[0]),([0,1,4,13,19,20],[45,67,75,79,648,656],[0,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_7 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_7 = true := by decide +kernel
def h0Block8_8 : List NodeSpec := [([0,1,2,3,4,13,66],[0,45,114,648,649,650,656,667,668,670,671,677,697,698,699,700,701],[0]),([0,1,2,3,4,13,87],[0,44,114,136,648,649,650,668,670,671,677,702,703,704],[0]),([0,1,2,3,4,5,25,107],[7,9,10,23,24,25,55,61,82,86,91,102,113,160,190,206,309,310,311,312,326,327,599,633,706],[0]),([0,1,2,3,4,5,28,107],[7,23,34,35,36,55,61,82,91,102,113,166,190,206,309,310,321,330,335,337,338,593,599,706],[0,1,2,5]),([0,1,2,3,4,5,33,107],[7,23,24,39,40,42,45,55,61,82,86,91,102,113,167,190,206,309,310,339,340,342,343,599,641,706],[0,2]),([0,1,2,3,4,5,107,120],[23,24,45,55,61,82,91,190,206,310,599,602,603,706,710,711,712,713,716],[0,5]),([0,1,2,3,4,5,107,121],[23,55,61,82,86,91,190,206,310,321,599,706,717,718,719,720,723,724,725],[0,1,5]),([0,1,2,3,4,5,16,28],[1,2,7,17,23,32,33,34,35,36,61,81,91,102,113,166,321,330,337,338,620,621,726,727,728],[0]),([0,1,2,3,4,5,14,26],[1,7,10,11,18,23,24,61,81,82,113,311,383,586,587,605,651,729,730,732,735,736,737,738],[0]),([0,1,2,3,4,5,16,25],[1,2,7,8,9,10,16,23,25,32,61,91,102,113,160,311,326,327,620,621,726],[0]),([0,1,2,5,14,25,28],[27,28,29,61,82,86,91,162,318,319,321,608,657,658,729,739,740],[0]),([0,1,2,3,4,5,192],[0,1,7,23,25,61,82,86,113,114,115,160,674,675,729,730,752,753],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_8 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_8 = true := by decide +kernel
def h0Block8_9 : List NodeSpec := [([0,1,2,3,4,5,14,45],[1,7,23,35,44,81,91,102,321,330,333,334,586,587,605,606,608,729,730,740,754,755,756,757,758],[0]),([0,1,2,3,4,5,14,187],[1,23,36,81,82,321,586,587,605,608,740,754,759,760,761,762],[0]),([0,1,2,3,4,5,188],[0,1,7,23,36,61,81,113,114,115,166,321,618,681,682,740,754,763,764,765,766],[0,2,5]),([0,1,2,3,4,5,14,188],[1,7,23,36,81,91,586,587,605,681,682,729,730,740,763,766],[0]),([0,1,2,3,4,5,14,50],[1,7,23,24,40,44,46,61,81,82,102,339,586,587,605,683,686,709,729,740,754,768,769,770,771,772],[0]),([0,1,2,3,4,5,16,33],[1,2,7,16,23,32,38,39,40,42,61,91,102,113,167,339,342,343,620,621,726],[0]),([0,1,3,4,5,14,51],[1,16,42,45,61,81,102,729,754,773,774,775,776,777,778,779],[0]),([0,1,2,4,5,33,186],[7,23,42,44,82,91,113,167,729,780,781,782,783,784,785,786],[0]),([0,1,2,3,4,5,14,28],[1,7,23,34,35,36,81,82,91,321,337,338,586,587,605,606,608,729,740],[0]),([0,1,2,3,4,5,194],[0,1,7,23,42,61,82,86,91,114,115,167,689,690,729,754,787,788,789],[0,2]),([0,1,2,5,15,25,28],[16,24,27,28,29,61,91,315,317,318,319,321,797,801,802,803,804],[0]),([0,1,2,3,4,5,203],[0,1,7,9,16,23,24,61,113,114,115,311,313,797,798,814,815,816,817],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_9 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_9 = true := by decide +kernel
def h0Block8_10 : List NodeSpec := [([0,1,2,3,4,5,15,45],[1,7,23,24,35,44,81,91,102,321,330,333,334,755,756,757,758,793,794,795,797,798,804,812,818,819],[0]),([0,1,2,3,4,5,205],[0,1,7,23,34,61,113,114,115,321,330,336,804,819,822,823,824,825,826,827],[0]),([0,1,2,3,4,5,15,205],[1,7,23,24,34,91,793,794,795,797,798,804,822,826,827],[0]),([0,1,2,3,4,5,15,204],[1,7,16,23,91,102,321,793,794,795,804,805,806,812,819,829,830],[0]),([0,1,2,4,5,33,207],[1,16,39,81,91,113,339,341,797,846,847,848,849,850,851,852],[0]),([0,1,2,3,4,5,15,28],[1,7,16,23,34,35,81,91,321,337,338,793,794,795,797,804,812,818,820,821],[0]),([0,1,2,3,4,5,210],[0,1,7,16,23,24,39,61,91,114,115,339,341,797,819,853,854,855,856,857],[0]),([0,1,2,3,4,5,17,25],[2,8,9,10,13,23,24,25,32,45,61,81,91,102,113,160,313,326,327,861,862,863,864,866,867,868],[0]),([0,1,2,3,4,5,17,28],[2,17,23,32,33,34,35,36,37,45,61,81,91,102,113,166,321,336,337,338,861,862,863,864,866,867,870],[0]),([0,1,2,3,4,5,17,33],[2,17,23,24,32,38,39,40,41,42,43,45,61,81,91,102,113,167,341,342,343,861,862,863,864,866,867,871],[0]),([0,1,2,3,4,5,16,26],[1,2,7,8,10,11,12,13,18,23,24,32,61,81,113,311,383,620,621,726,728,735,736,737,738],[0]),([0,1,2,5,16,25,28],[15,17,26,27,28,29,61,91,162,317,318,319,321,627,630,726,727],[0,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_10 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_10 = true := by decide +kernel
def h0Block8_11 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,46],[0,1,7,23,32,60,61,113,114,115,160,313,726,728,876,877,878,879,880]),([0,1,2,3,4,5,25,46],[9,10,23,24,25,61,91,102,113,160,326,327,726,876,877,878,879,880]),([0,1,2,3,4,5,25,47],[10,13,16,32,61,91,102,113,160,313,326,327,726,881,882,883,884,885]),([0,1,2,3,4,5,16,45],[1,2,7,17,23,32,33,35,37,44,81,91,102,321,330,333,334,620,621,726,727,728,755,756,757,758,886]),([0,1,2,3,4,5,31],[0,1,7,32,60,61,113,114,115,166,321,336,727,886,887,888,889,890,891,892,893]),([0,1,2,3,4,5,16,28,31],[23,91,166,727]),([0,1,2,3,4,5,16,50],[1,2,7,23,24,32,38,40,41,43,46,61,81,102,339,620,621,709,726,727,768,769,770,771,772,886]),([0,1,2,3,4,5,52],[0,1,7,23,32,60,61,91,113,114,115,167,341,726,886,894,895,896,897,898,899]),([0,1,2,3,4,5,33,52],[23,24,39,40,42,61,91,113,167,342,343,726,894,895,896,898,899]),([0,1,2,3,4,5,33,53],[16,32,40,43,61,91,113,167,341,342,343,726,900,901,902,903,904]),([0,1,2,3,4,5,16,212],[1,2,7,23,32,41,43,61,81,91,102,113,167,341,620,621,641,726,727,728,886,897,910]),([0,1,2,3,4,5,16,211],[1,2,7,23,32,37,41,61,81,91,102,113,166,336,593,620,621,726,727,728,886,891])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_11 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_11 = true := by decide +kernel
def h0Block8_12 : List NodeSpec := [([0,1,3,4,5,44,54],[16,23,25,45,61,81,113,925,926,929,930,931,932,933,934],[0]),([0,1,2,5,25,28,54],[16,24,27,28,29,61,91,315,318,319,321,925,935,936,937,938],[0]),([0,1,2,4,5,25,213],[1,7,9,16,25,44,91,102,311,925,942,943,944,945,946],[0]),([0,1,2,3,4,5,217],[0,1,7,9,16,24,25,61,113,114,115,311,925,926,947,948,949],[0]),([0,1,2,3,4,5,45,54],[1,7,23,24,35,44,81,91,102,321,330,333,334,755,756,757,758,921,922,923,925,926,938,939,950,951],[0]),([0,1,2,3,4,5,54,214],[1,7,16,23,34,81,321,921,922,923,938,939,951,954,955,956],[0]),([0,1,2,3,4,5,215],[0,1,7,23,34,36,61,81,113,114,115,321,330,938,940,951,957,958,959,960],[0]),([0,1,2,3,4,5,54,215],[1,7,23,24,34,81,91,921,922,923,925,926,938,957,959,960],[0]),([0,1,2,3,4,5,28,54],[1,7,16,23,34,35,81,91,321,337,338,921,922,923,925,938,939,950],[0]),([0,1,2,3,4,5,219],[0,1,7,16,24,39,42,61,91,114,115,339,925,951,965,966,967,968],[0]),([0,1,4,5,20,65],[7,45,55,57,60,429,973,974,975],[0,3]),([0,1,2,3,4,5,65,71],[7,51,55,60,61,102,113,206,971,972,975,978,988,989,990,991,992,993,994,995],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_12 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_12 = true := by decide +kernel
def h0Block8_13 : List NodeSpec := [([0,1,2,3,4,5,65,72],[7,51,55,60,61,102,113,971,972,975,985,990,992,993,996,997,998,1001,1002],[0]),([0,1,2,3,4,5,79],[0,1,7,23,32,61,64,102,113,114,115,1004,1005,1006,1007,1008],[0]),([0,1,4,5,19,20,66],[7,45,67,68,71,76,79,80,81,82,1009,1010,1011,1012],[0]),([0,1,4,5,19,20,67],[7,32,45,67,68,71,75,79,80,81,1021,1022,1023,1024],[0]),([0,1,4,5,19,20,69],[7,45,67,68,71,79,80,81,82,1029,1030,1031,1032],[0]),([0,1,4,5,19,20,70],[7,45,67,68,71,78,79,80,81,82,1036,1037,1038,1039],[0]),([0,1,4,5,20,83],[7,45,81,82,1046,1047,1048],[0,3]),([0,1,2,3,4,5,85],[0,1,4,23,30,44,45,81,91,102,113,114,115,122,128,310,1076],[0,3]),([0,1,2,3,4,5,20,195],[1,23,81,82,91,102,113,116,117,120,123,125,126,127,1013,1014,1017,1081,1082,1083,1084,1085,1086,1087,1088],[0]),([0,1,2,3,4,5,20,226],[1,7,23,61,81,82,91,102,108,113,116,117,120,122,123,125,126,127,1025,1026,1027,1093,1094,1095,1096,1097,1098],[0]),([0,1,2,3,4,5,20,227],[1,7,23,61,81,82,91,108,113,116,117,120,123,126,127,1033,1034,1035,1103,1104,1105,1106,1107,1108],[0]),([0,1,2,3,4,5,20,229],[1,7,23,61,81,82,91,102,113,116,117,120,123,125,126,127,1040,1041,1042,1118,1119,1123,1124,1125,1126,1127],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_13 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_13 = true := by decide +kernel
def h0Block8_14 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,88],[0,1,7,23,32,91,102,113,114,115,136,1133,1134,1135,1136,1137,1138])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_14 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_14 = true := by decide +kernel
def h0Nodes8 : List NodeSpec := h0Block8_0 ++ h0Block8_1 ++ h0Block8_2 ++ h0Block8_3 ++ h0Block8_4 ++ h0Block8_5 ++ h0Block8_6 ++ h0Block8_7 ++ h0Block8_8 ++ h0Block8_9 ++ h0Block8_10 ++ h0Block8_11 ++ h0Block8_12 ++ h0Block8_13 ++ h0Block8_14
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Check8 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Nodes8 = true := by
  unfold h0Nodes8 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0Test8_0,h0Test8_1⟩,h0Test8_2⟩,h0Test8_3⟩,h0Test8_4⟩,h0Test8_5⟩,h0Test8_6⟩,h0Test8_7⟩,h0Test8_8⟩,h0Test8_9⟩,h0Test8_10⟩,h0Test8_11⟩,h0Test8_12⟩,h0Test8_13⟩,h0Test8_14⟩
def h0Bucket8 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 8 xs.toFinset) h0Bucket8 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0Bucket7Ok h0Check8
def h0Block9_0 : List NodeSpec := [([0,2,3,4,5,6,16],[0,1,2,3,4,5,6,7,23,44,45,46],[0,1]),([0,1,2,3,4,5,6,19],[0,1,3,7,23,32,46,47,48,49,50,52,60,61,62,63,81,91,94,103,106,107],[0,2,3]),([0,1,2,3,4,5,6,20],[0,1,3,4,7,23,30,45,46,47,48,52,61,81,91,103,116,117,118,119,120,126,127],[0,3]),([0,1,2,3,4,5,6,21],[0,1,3,7,23,30,32,44,45,46,47,48,52,61,81,91,103,132,133,134,135,140,146,147],[0,5]),([0,1,2,3,4,5,24],[0,1,3,23,61,81,91,93,102,113,114,115,153,154,155],[0,1,3,4]),([0,2,3,4,5,7,16],[0,1,2,7,23,44,46,156,157,158,159],[0,1]),([0,1,2,3,4,5,7,19],[0,1,7,23,46,49,50,60,61,81,91,94,97,98,106,107,154,156,168,169,170,171,172,182],[0,3]),([0,1,2,3,4,5,7,20],[0,1,7,23,45,46,61,81,91,116,117,120,122,123,126,127,154,156,157,163,168,169,170,182,183,184],[0,3]),([0,1,2,3,4,5,7,21],[0,1,7,23,44,45,46,61,81,91,132,133,140,143,144,146,147,154,156,163,168,169,170,182,186,187],[0,5]),([0,1,2,3,4,5,18],[2,23,61,81,91,102,113,114,115,154,189,190,191,192],[0,3,4]),([0,1,2,3,4,5,8,55],[0,1,7,23,46,55,60,61,81,91,154,193,194,197,198,219,220,221,223,228,230,264,265,276,277],[0]),([0,1,2,3,4,5,8,56],[0,1,7,23,44,46,55,60,61,81,91,154,197,198,219,227,230,276,277,283,284,285,286,287,289,298,299],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_0 = true := by decide +kernel
def h0Block9_1 : List NodeSpec := [([0,1,2,3,4,5,91],[0,1,7,23,55,61,81,91,102,113,114,115,154,190,309,310],[0,1]),([0,1,2,3,4,5,8,91],[0,1,7,23,44,46,55,81,154,190,197,198,219,230,276,277,309,310,353],[0,1]),([0,1,3,4,5,8,20],[0,7,46,61,81,116,122,198,219,227,358,359],[0,1]),([0,1,3,4,5,8,21],[0,7,46,55,61,81,132,143,198,219,227,360,361],[0,1]),([0,1,2,3,4,5,8,25],[0,7,9,10,25,55,61,81,91,102,113,198,219,230,276,277,311,313,326,327,367,368],[0,3]),([0,1,2,3,4,5,8,28],[0,7,34,35,36,44,55,61,81,91,102,113,198,219,227,229,230,276,277,330,336,337,338,391,392],[0,3]),([0,1,2,3,4,5,8,33],[0,7,39,40,42,44,46,55,61,81,91,102,113,198,219,229,230,276,277,339,341,342,343,410,411],[0,4]),([0,1,2,3,4,5,8,77],[0,7,44,46,49,55,60,61,81,86,91,97,198,219,230,276,277,424,425,426],[0]),([0,1,2,3,4,5,74],[1,23,45,57,81,91,102,113,114,115,427,428],[0,1]),([0,1,2,3,4,5,93],[0,1,7,23,81,91,102,113,114,115,198,247,522,523,524,525],[0,1]),([0,1,2,3,4,5,8,93],[0,7,44,46,55,60,61,81,198,219,227,230,247,276,277,522,523,524,525],[0]),([0,1,2,3,4,5,9,55],[0,1,7,23,45,46,61,81,82,91,154,193,194,228,264,265,526,527,528,529,530,535,546,547],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_1 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_1 = true := by decide +kernel
def h0Block9_2 : List NodeSpec := [([0,1,2,3,4,5,9,56],[0,1,7,23,44,45,46,61,81,91,154,283,284,289,298,299,526,527,528,533,535,546,547,548,549],[0]),([0,1,2,3,4,5,179],[0,1,7,23,61,91,102,113,114,115,154,527,553,554,555],[0,1]),([0,1,3,4,5,9,20],[0,7,45,46,61,81,116,122,526,527,533,569,570],[0,1]),([0,1,2,3,4,5,9,25],[0,7,9,10,25,45,61,81,82,91,102,113,311,326,327,526,527,535,546,547,571,572],[0]),([0,1,2,3,4,5,9,28],[0,7,34,35,36,44,45,61,81,91,102,113,330,337,338,526,527,533,534,535,546,547,576,577],[0]),([0,1,2,3,4,5,9,33],[0,7,39,40,42,44,45,46,61,81,91,102,113,339,342,343,526,527,534,535,546,547,579,580],[0]),([0,1,2,3,4,5,180],[0,1,7,23,45,81,91,102,113,114,115,526,582,583,584,585],[0,1]),([0,1,2,3,4,12,14],[0,44,46,86,115,154,310,586,587,588,590,597,604,605,615,617],[0]),([0,1,2,3,4,12,16],[0,2,44,45,46,115,154,310,588,590,604,611,615,617,620,621],[0,1]),([0,1,2,3,4,12,19],[0,46,49,97,106,107,115,310,588,597,604,615,617],[0,3]),([0,1,2,3,4,12,20],[0,45,46,115,116,122,126,127,310,588,604,611,614,615,617],[0,3]),([0,1,2,3,4,12,21],[0,44,45,46,115,132,143,146,147,310,588,597,604,614,615,617],[0,5])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_2 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_2 = true := by decide +kernel
def h0Block9_3 : List NodeSpec := [([0,1,2,3,4,13,14],[0,44,46,114,154,586,587,648,649,650,667,671,677],[0,1]),([0,1,2,3,4,13,16],[0,2,44,45,46,114,154,620,648,649,650,656,667,671,677],[0,1]),([0,1,2,3,4,13,19],[0,46,49,97,106,114,648,649,667,671,677],[0,3]),([0,1,2,3,4,13,20],[0,45,46,114,116,122,126,648,649,656,667,668,671,677],[0,3]),([0,1,2,3,4,13,21],[0,44,45,46,114,132,143,146,648,649,667,668,671,677],[0,5]),([0,1,2,3,4,5,107],[0,1,7,23,55,61,91,102,113,114,115,154,190,309,310,599],[0,1,2,5]),([0,1,2,3,4,5,16],[0,1,2,7,23,61,91,102,113,114,115,154,620,726,728],[0]),([0,1,2,3,4,5,14,25],[1,7,9,10,23,25,61,81,82,86,91,102,113,160,326,327,586,587,605,651,652,729,730,731],[0]),([0,1,2,3,4,5,14,28],[1,7,23,34,35,36,61,81,91,102,113,166,321,337,338,586,587,605,606,607,608,610,729,730,740,754],[0,2,5]),([0,1,2,3,4,5,14,33],[1,7,23,39,40,42,61,81,82,86,91,102,113,167,342,343,586,587,605,683,684,729,730,754,767],[0,2]),([0,1,2,3,4,5,186],[0,1,7,23,44,91,102,113,114,115,729,786,790,791,792],[0]),([0,1,2,3,4,5,15,25],[1,7,9,10,16,23,24,25,61,81,91,102,113,311,313,326,327,793,794,795,796,797,798,799,800],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_3 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_3 = true := by decide +kernel
def h0Block9_4 : List NodeSpec := [([0,1,2,3,4,5,15,28],[1,7,23,34,35,36,61,81,91,102,113,321,330,336,337,338,793,794,795,797,798,804,818,819,820,821],[0,3]),([0,1,2,3,4,5,15,33],[1,7,16,23,24,39,40,42,61,81,91,102,113,339,341,342,343,793,794,795,797,798,819,843,844,845],[0]),([0,1,2,3,4,5,207],[0,1,7,23,81,91,102,113,114,115,154,797,852,858,859,860],[0]),([0,1,2,3,4,5,17],[0,1,2,7,23,45,61,81,91,102,113,114,115,861,862,863,864],[0,1]),([0,1,2,3,4,5,16,25],[1,2,7,8,9,10,13,23,25,32,61,81,91,102,113,160,313,326,327,620,621,622,626,726,728],[0,3]),([0,1,2,3,4,5,16,28],[1,2,7,17,23,32,33,34,35,36,37,61,81,91,102,113,166,321,336,337,338,620,621,635,636,726,727,728,886],[0,2,3,5]),([0,1,2,3,4,5,16,33],[1,2,7,23,32,38,39,40,42,43,61,81,91,102,113,167,341,342,343,620,621,637,640,726,728,886],[0,2,4]),([0,1,2,3,4,5,36],[0,1,7,23,44,81,91,102,113,114,115,726,905,906,907,908,909],[0]),([0,1,2,3,4,5,16,36],[1,2,7,23,32,45,61,81,620,621,726,727,728,905,906,907,908,909],[0]),([0,1,2,3,4,5,16,37],[1,2,7,23,32,45,61,81,91,620,621,726,728,911,912,913,914,915],[0]),([0,1,2,3,4,5,38],[0,23,45,81,91,102,113,114,115,726,916,917,918,919,920],[0]),([0,1,2,3,4,5,25,54],[1,7,9,10,16,23,24,25,61,81,91,102,113,311,326,327,921,922,923,924,925,926,927,928],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_4 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_4 = true := by decide +kernel
def h0Block9_5 : List NodeSpec := [([0,1,2,3,4,5,28,54],[1,7,23,34,35,36,61,81,91,102,113,321,330,337,338,921,922,923,925,926,938,950,951,952,953],[0,3]),([0,1,2,3,4,5,33,54],[1,7,16,23,24,39,40,42,61,81,91,102,113,339,342,343,921,922,923,925,926,951,962,963,964],[0]),([0,1,2,3,4,5,213],[0,1,7,91,102,113,114,115,154,925,946,969,970],[0]),([0,1,2,3,4,5,65],[0,1,7,23,49,55,60,61,97,102,113,114,115,971,972],[0,3]),([0,1,2,3,4,5,78],[0,1,7,23,50,61,64,102,113,114,115,310,695,1003],[0,3]),([0,1,4,5,19,20],[7,45,67,79,80,81],[0,3]),([0,1,2,3,4,5,82],[0,1,7,23,46,61,94,102,114,115,1067,1068,1069],[0,3]),([0,1,2,3,4,5,80],[0,1,7,23,45,61,81,91,102,113,114,115,116,122,1070,1071,1072,1073],[0,3]),([0,1,2,3,4,5,66],[0,1,7,23,61,81,91,102,113,114,115,117,310,697,698,1012,1074,1075],[0,3]),([0,1,2,3,4,5,20,66],[1,7,23,45,61,81,82,91,116,117,120,123,126,127,697,698,1012,1074,1075],[0]),([0,1,2,3,4,5,20,67],[1,7,23,45,61,81,82,91,108,116,117,120,122,126,127,1024,1089,1090,1091,1092],[0]),([0,1,2,3,4,5,20,69],[7,45,61,81,82,91,102,108,113,116,117,120,126,127,1032,1099,1100,1101,1102],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_5 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_5 = true := by decide +kernel
def h0Block9_6 : List NodeSpec := [([0,1,2,3,4,5,29],[0,1,23,36,45,81,91,102,114,115,1109,1110,1111,1112,1113],[0]),([0,1,2,3,4,5,70],[0,1,7,23,46,61,81,91,102,114,115,120,1039,1114,1115,1116,1117],[0]),([0,1,2,3,4,5,20,70],[7,45,61,81,82,91,113,116,117,120,125,126,127,1039,1114,1115,1116,1117],[0]),([0,1,2,3,4,5,86],[0,1,7,23,44,81,91,102,113,114,115,132,143,1128,1129,1130],[0,5]),([0,1,2,3,4,5,87],[0,1,7,23,91,102,113,114,115,133,136,310,702,1131,1132],[0,5]),([0,1,2,3,4,5,20],[0,1,7,23,45,61,81,102,113,114,115,116,117,120,126],[0,3]),([0,1,2,3,4,5,89],[0,1,7,23,46,61,81,91,102,114,115,140,1139,1140,1141,1142],[0,5])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_6 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_6 = true := by decide +kernel
def h0Nodes9 : List NodeSpec := h0Block9_0 ++ h0Block9_1 ++ h0Block9_2 ++ h0Block9_3 ++ h0Block9_4 ++ h0Block9_5 ++ h0Block9_6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Check9 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Nodes9 = true := by
  unfold h0Nodes9 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨h0Test9_0,h0Test9_1⟩,h0Test9_2⟩,h0Test9_3⟩,h0Test9_4⟩,h0Test9_5⟩,h0Test9_6⟩
def h0Bucket9 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket9Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 9 xs.toFinset) h0Bucket9 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0Bucket8Ok h0Check9
def h0Block10_0 : List NodeSpec := [([0,1,2,3,4,5,6],[0,1,7,47,48,61,113,114,115],[0,1,2,3,4,5]),([0,1,2,3,4,5,7],[0,1,7,23,61,113,114,115,154,168,169],[0,1,2,3,4,5]),([0,1,2,3,4,5,8],[0,1,7,61,81,113,114,115,154,276,277],[0,1]),([0,1,2,3,4,5,9],[0,1,7,61,113,114,115,154,546,547],[0,1]),([0,1,2,3,4,12],[0,114,115,154],[0,1,2,3,4,5]),([0,1,2,3,4,13],[0,114,154],[0,1,2,3,4,5]),([0,1,2,3,4,5,14],[0,1,7,23,61,113,114,115,586,587,605],[0,1,2,5]),([0,1,2,3,4,5,15],[0,1,7,61,81,113,114,115,154,793,794,795],[0,1]),([0,1,2,3,4,5,16],[0,1,2,7,23,45,61,81,113,114,115,620,621],[0,1,2,5]),([0,1,2,3,4,5,54],[0,1,7,61,113,114,115,154,921,922,923],[0,1]),([0,1,2,3,4,5,19],[0,1,7,49,61,106,107,113,114,115],[0,3]),([0,1,2,3,4,5,20],[0,1,7,45,61,81,91,113,114,115,116,126,127],[0,2,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test10_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket9 10 h0Block10_0 = true := by decide +kernel
def h0Block10_1 : List NodeSpec := [([0,1,2,3,4,5,21],[0,1,7,61,91,113,114,115,132,146,147],[0,5])]
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
def h0Block11_0 : List NodeSpec := [([0,1,2,3,4,5],[0,114,115],[0,1,2,3,4,5])]
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
lemma h0Bound : Lower h0R h0G 12 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 3,1,9),(VAR 4,1,17),(VAR 5,6,38)]) (by decide +kernel) h0Bucket11Ok (by decide +kernel)
def wit : List PEqualNP.CircuitLowerBounds.Gate := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 7]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 5]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 0]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 2]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [9, 11]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 12]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 11]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 14]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 4]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 16]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 17]⟩]
def wo : Nat := 18
lemma wit_mono : PEqualNP.MetaComplexity.Monotone2 ⟨wit, wo⟩ := by simp [PEqualNP.MetaComplexity.Monotone2, wit]
set_option maxRecDepth 100000 in set_option maxHeartbeats 0 in
lemma wit_eval : ∀ r : Row, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput6 r)) = ((4277071592 * 2 ^ 32 + 4008372904) ||| ((4277071592 * 2 ^ 32 + 4008372904) <<< 64)).testBit r.val := by decide +kernel
lemma low_root : Lower (varsOf 63) ((4277071592 * 2 ^ 32 + 4008372904) ||| ((4277071592 * 2 ^ 32 + 4008372904) <<< 64)) 12 := h0Bound
end PEqualNP.Outside.L_meta_44744
theorem PEqualNP.Outside.L_meta_44744 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071592 * 2 ^ 32 + 4008372904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071592 * 2 ^ 32 + 4008372904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hcs
  exact PEqualNP.Outside.L_meta_44744.table2_of_lower (4277071592 * 2 ^ 32 + 4008372904) (by decide) (by decide) (by decide) (by decide)
    12 PEqualNP.Outside.L_meta_44744.low_root
    PEqualNP.Outside.L_meta_44744.wit PEqualNP.Outside.L_meta_44744.wo (by decide)
    PEqualNP.Outside.L_meta_44744.wit_mono PEqualNP.Outside.L_meta_44744.wit_eval s hcs
