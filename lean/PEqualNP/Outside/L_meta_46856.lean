import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_46856
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

def sliceSpec (raw : List Nat) (target : Nat) (o : Option (Nat × Nat)) : Prop :=
  ∀ pair, o = some pair → Slice raw target pair.1 pair.2
lemma sliceSpecCons {raw target d k xs} (head : Slice raw target d k)
    (tail : ∀ o ∈ xs, sliceSpec raw target o) :
    ∀ o ∈ some (d,k) :: xs, sliceSpec raw target o :=
  forall_cons (fun _ eq => by cases eq; exact head) tail
lemma sliceSpecNil {raw target} : ∀ o ∈ [], sliceSpec raw target o :=
  fun _ h => (List.not_mem_nil h).elim

def poolSteps (steps : List (Nat × Nat × Nat)) (rows : List (Nat × List Nat)) : List PoolSpec :=
  let table := steps.toArray
  rows.map (fun row => (row.1, row.2.map (fun i => table[i]?.getD (0,0,0))))

abbrev NodeSpec := List Nat × List Nat × List Nat

def readIndexMask : Nat → Nat → Nat → List Nat
  | 0, _, _ => []
  | fuel+1, base, bits =>
      if bits = 0 then [] else
      let zeros := (bits ^^^ (bits-1)).log2
      let index := base + zeros
      index :: readIndexMask fuel (index+1) (bits >>> (zeros+1))
def readIndexGaps : Nat → Nat → Nat → List Nat
  | 0, _, _ => []
  | fuel+1, start, bits =>
      if bits ≤ 1 then [] else
      let width := (bits ^^^ (bits-1)).log2
      let tail := bits >>> (width+1)
      let gap := (1 <<< width) + (tail &&& ((1 <<< width)-1))
      (start+gap-1) :: readIndexGaps fuel (start+gap) (tail >>> width)
def decodeIndices (n : Nat) : List Nat :=
  let data := n >>> 1
  if n.testBit 0 then readIndexGaps (data.log2+1) 0 data
  else readIndexMask (data.log2+1) 0 data
def priorityIndices (bits : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | fuel+1, x => if x ≤ 1 then [] else
    (x &&& ((1 <<< bits) - 1)) :: priorityIndices bits fuel (x >>> bits)
def priorityNodes (bits : Nat) (rr : List (Nat × Nat × Nat)) : List NodeSpec :=
  rr.map fun t => (decodeIndices t.1, priorityIndices bits (t.2.1.log2+1) t.2.1, decodeIndices t.2.2)
def indexPairNodes (rows : List (Nat × Nat)) : List NodeSpec :=
  rows.map fun row => (decodeIndices row.1, decodeIndices row.2, [0])
def indexTripleNodes (rows : List (Nat × Nat × Nat)) : List NodeSpec :=
  rows.map fun row => (decodeIndices row.1, decodeIndices row.2.1, decodeIndices row.2.2)

def nodesWithIdentity (entries : List (List Nat × List Nat)) : List NodeSpec :=
  entries.map (fun entry => (entry.1, entry.2, [0]))

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
def startDecor (roots pos neg : List Nat) : List Decor :=
  roots.map fun x => (x, projBits pos x, projBits neg x)
def startWires (roots pos neg : List Nat) : BT Decor :=
  buildWiresBT 4 (startDecor roots pos neg) []
def startNodes (roots : List Nat) : List NodeSpec := [(List.range roots.length, [], [0])]
def singleLayerCheck (roots : List Nat) (T k : Nat) (pos neg : List Nat)
    (essentialPairs : List (Nat × Nat × Nat)) : Bool :=
  forestRootCheck roots T essentialPairs && decide (T < 2^128) &&
  goodPairsCheck T pos neg && baseCheck pos neg (startDecor roots pos neg) &&
  checkNodesBT (startWires roots pos neg) T (fullMask pos.length)
    BT.empty BT.empty BT.empty k (startNodes roots) &&
  bucketContainsBT (buildBucketsBT (startWires roots pos neg) (startNodes roots)) roots
lemma lower_from_single_layer {roots T k pos neg essentialPairs}
    (h : singleLayerCheck roots T k pos neg essentialPairs = true) :
    Lower roots T (k+1) := by
  simp only [singleLayerCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hr,hT⟩,hp⟩,hb⟩,hn⟩,hm⟩ := h
  apply lower_of_forestBT hr _ hm
  apply buildBucketsBT_sound (raw := roots) hT (goodPairs_of hp) _ _ _ _ hn
  · exact buildWiresBT_faithful (base_of hb)
  · trivial
  · trivial
  · trivial
def identifyRow (i j keep : Nat) (r : Row) : Row :=
  let x := r.val &&& keep
  ⟨(if x.testBit j then x ||| (2^i) else x) % 128, Nat.mod_lt _ (by decide)⟩
lemma mapped_slice {raw : List Nat} {T d : Nat} {roots : List Nat} {G cost : Nat}
    (f : Row → Row) (hd : ∀ r : Row, d.testBit (f r).val = true)
    (hc : raw.all (fun a => freeIn roots (renameW f a)) = true)
    (ht : renameW f T = G) (proper : checkProper G = true)
    (low : Lower roots G cost) : Slice raw T d cost := by
  obtain ⟨ne, lt, bit⟩ := checkProper_sound proper
  have eq : restrictW f (obs T) = obs G := (obs_renameW f T).symm.trans (congrArg obs ht)
  refine ⟨f, roots, hd, ?_, ?_, ?_⟩
  · exact fun a ha => freeIn_sound (List.all_eq_true.mp hc a ha)
  · rw [eq]
    exact obs_not_const ne lt bit
  · rw [eq]
    exact low
def oppositeRow (i j keep : Nat) (r : Row) : Row :=
  let x := r.val &&& keep
  ⟨(if x.testBit j then x else x ||| (2^i)) % 128, Nat.mod_lt _ (by decide)⟩
def freeSigned (roots : List Nat) (w : Nat) : Bool :=
  freeIn roots w || roots.any (fun b => w == (ALL128 ^^^ b))
lemma freeSigned_sound {roots : List Nat} {f : Row → Row} {a : Nat}
    (ok : freeSigned roots (renameW f a) = true) :
    Avail (roots.map obs) (restrictW f (obs a)) := by
  simp only [freeSigned, Bool.or_eq_true, List.any_eq_true, beq_iff_eq] at ok
  rcases ok with h | ⟨b, hb, heq⟩
  · exact freeIn_sound h
  · have eq : restrictW f (obs a) = invW (obs b) := by
      rw [← obs_renameW, heq]
      funext r
      have hall : ALL128.testBit r.val = true := by
        simp only [ALL128]; have h := r.isLt
        simpa [h] using Nat.testBit_two_pow_sub_one 128 r.val
      simp [obs, invW, Nat.testBit_xor, hall]
    rw [eq]
    exact avail_inv (Or.inl (List.mem_map_of_mem hb))
lemma opposite_slice {raw : List Nat} {T d : Nat} {roots : List Nat} {G cost : Nat}
    (f : Row → Row) (hd : ∀ r : Row, d.testBit (f r).val = true)
    (hc : raw.all (fun a => freeSigned roots (renameW f a)) = true)
    (ht : renameW f T = G) (proper : checkProper G = true)
    (low : Lower roots G cost) : Slice raw T d cost := by
  obtain ⟨ne, lt, bit⟩ := checkProper_sound proper
  have eq : restrictW f (obs T) = obs G := (obs_renameW f T).symm.trans (congrArg obs ht)
  refine ⟨f, roots, hd, ?_, ?_, ?_⟩
  · exact fun a ha => freeSigned_sound (List.all_eq_true.mp hc a ha)
  · rw [eq]; exact obs_not_const ne lt bit
  · rw [eq]; exact low
def h3R : List Nat := varsOf 44
def h3G : Nat := 0xfff0fff0f000f000fff0fff0f000f000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Bound : Lower h3R h3G 4 := lower_from_single_layer (k := 3) (pos := [36,40,12,12,40,36]) (neg := [32,32,4,8,8,4]) (essentialPairs := [(VAR 2,8,12),(VAR 3,4,12),(VAR 5,4,36)]) (by decide +kernel)
def h4R : List Nat := varsOf 13
def h4G : Nat := 0xfa0afa0afa0afa0afa0afa0afa0afa0a
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4Bound : Lower h4R h4G 3 := lower_from_single_layer (k := 2) (pos := [1,1,12,9]) (neg := [0,5,8,8]) (essentialPairs := [(VAR 0,0,1),(VAR 2,1,5),(VAR 3,4,12)]) (by decide +kernel)
def h6R : List Nat := varsOf 36
def h6G : Nat := 0xf0f0f0ff0f0f0f00f0f0f0ff0f0f0f0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Bound : Lower h6R h6G 3 := lower_from_single_layer (k := 2) (pos := [4,32,4,32]) (neg := [0,0,36,36]) (essentialPairs := [(VAR 2,0,4),(VAR 5,0,32)]) (by decide +kernel)
def h5R : List Nat := varsOf 44
def h5G : Nat := 0xf000f00f000f0000f000f00f000f000
lemma h5Bound : Lower h5R h5G 4 := lift_of (z := 0) (o := 8) (essPairs := [(VAR 3,4,12)]) (by decide +kernel) h6Bound
def h7R : List Nat := varsOf 37
def h7G : Nat := 0xafafafaffafafafaafafafaffafafafa
lemma h7Bound : Lower h7R h7G 4 := lift_of (z := 1) (o := 0) (essPairs := [(VAR 0,0,1)]) (by decide +kernel) h6Bound
def h8R : List Nat := varsOf 41
def h8G : Nat := 0xaaaaaaaaff00ff00aaaaaaaaff00ff00
lemma h8Bound : Lower h8R h8G 3 := carry_of (swaps := [(2,3),(3,4),(4,5),(0,1),(1,2),(2,3),(0,1)]) (roots2 := h4R) (T2 := h4G) (by decide +kernel) h4Bound
def h2R : List Nat := varsOf 45
def h2G : Nat := 0xafaaafaafa0afa0aafaaafaafa0afa0a
def h2Pos : List Nat := [1,12,1,37,12,9,13,12,37,40,40,40]
def h2Neg : List Nat := [0,8,5,36,4,8,5,44,5,32,8,44]
def h2Mask : Nat := fullMask 12
def h2Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,365,324),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,474,2524),(0xff00ff00ff00ff00ff00ff00ff00ff00,3826,3234),(0xffffffff00000000ffffffff00000000,3848,2696)]
def h2Steps : List (Nat × Nat × Nat) := [(2,1,3)]
def h2W : BT Decor := buildWiresBT 3 h2Base h2Steps
def h2AutoList : List (List (Nat × Nat)) := [[]]
def h2Autos : BT (List (Nat × Nat)) := btOfList 1 h2AutoList
lemma h2Pairs : goodPairs h2G h2Pos h2Neg := goodPairs_of (by decide +kernel)
lemma h2BaseOk : ∀ x ∈ h2Base, faithful h2Pos h2Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma h2WOk : btAll (fun x => faithful h2Pos h2Neg x ∧ x.1 < 2^128) h2W := buildWiresBT_faithful h2BaseOk
lemma h2AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h2G = h2G) h2Autos := btAll_ofList (autos_of (by decide +kernel))
def h2SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 4,3),some (subcubeFast 0 8,4),some (subcubeFast 1 0,4),some (subcubeFast 32 0,3),some (0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5,4)]
def h2Slices : BT (Option (Nat × Nat)) := btOfList 3 h2SliceList
def h2Specs : List PoolSpec := [(2,[]),(1,[]),(3,[]),(0,[]),(4,[])]
def h2Pools : BT (Option BoundPool) := buildPoolsBT 3 h2W h2R h2Slices h2Specs
set_option maxRecDepth 200000 in
lemma h2Slice4 : Slice h2R h2G (0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5) 4 := mapped_slice (identifyRow 0 2 44) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h3Bound
set_option maxRecDepth 200000 in
lemma h2Slice3 : Slice h2R h2G (subcubeFast 32 0) 3 := slice_fast_direct (zDead := 0) (by decide +kernel) h4Bound
set_option maxRecDepth 200000 in
lemma h2Slice2 : Slice h2R h2G (subcubeFast 1 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h5Bound
set_option maxRecDepth 200000 in
lemma h2Slice1 : Slice h2R h2G (subcubeFast 0 8) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h7Bound
set_option maxRecDepth 200000 in
lemma h2Slice0 : Slice h2R h2G (subcubeFast 0 4) 3 := slice_fast_direct (zDead := 0) (by decide +kernel) h8Bound
lemma h2SlicesOk : btAll (sliceSpec h2R h2G) h2Slices := btAll_ofList (P := sliceSpec h2R h2G) (sliceSpecCons h2Slice0 (sliceSpecCons h2Slice1 (sliceSpecCons h2Slice2 (sliceSpecCons h2Slice3 (sliceSpecCons h2Slice4 sliceSpecNil)))))
lemma h2PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h2R h2G c) h2Pools := buildPoolsBT_sound h2SlicesOk
def h2Empty : BT (List (List Nat)) := BT.empty
lemma h2EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h2G (4 - 1) xs.toFinset) h2Empty := trivial
def h2Block4_0 : List NodeSpec := priorityNodes 3 [(62,792,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h2Test4_0 : checkNodesBT h2W h2G h2Mask h2Pools h2Autos h2Empty 4 h2Block4_0 = true := by decide +kernel
def h2Nodes4 : List NodeSpec := h2Block4_0
lemma h2Check4 : checkNodesBT h2W h2G h2Mask h2Pools h2Autos h2Empty 4 h2Nodes4 = true := h2Test4_0
def h2Bucket4 : BT (List (List Nat)) := buildBucketsBT h2W h2Nodes4
lemma h2Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h2G 4 xs.toFinset) h2Bucket4 := buildBucketsBT_sound (by decide) h2Pairs h2WOk h2PoolsOk h2AutosOk h2EmptyOk h2Check4
def h2Block5_0 : List NodeSpec := priorityNodes 3 [(30,5768,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h2Test5_0 : checkNodesBT h2W h2G h2Mask h2Pools h2Autos h2Bucket4 5 h2Block5_0 = true := by decide +kernel
def h2Nodes5 : List NodeSpec := h2Block5_0
lemma h2Check5 : checkNodesBT h2W h2G h2Mask h2Pools h2Autos h2Bucket4 5 h2Nodes5 = true := h2Test5_0
def h2Bucket5 : BT (List (List Nat)) := buildBucketsBT h2W h2Nodes5
lemma h2Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h2G 5 xs.toFinset) h2Bucket5 := buildBucketsBT_sound (by decide) h2Pairs h2WOk h2PoolsOk h2AutosOk h2Bucket4Ok h2Check5
lemma h2Bound : Lower h2R h2G 6 := lower_of_forestBT (essPairs := [(VAR 0,0,1),(VAR 2,1,5),(VAR 3,4,12),(VAR 5,5,37)]) (by decide +kernel) h2Bucket5Ok (by decide +kernel)
def h10R : List Nat := varsOf 42
def h10G : Nat := 0xcc00cc00ffccffcccc00cc00ffccffcc
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h10Bound : Lower h10R h10G 4 := lower_from_single_layer (k := 3) (pos := [2,8,42,42,8,2]) (neg := [0,0,34,40,40,34]) (essentialPairs := [(VAR 1,0,2),(VAR 3,0,8),(VAR 5,2,34)]) (by decide +kernel)
def h9R : List Nat := varsOf 46
def h9G : Nat := 0xccc0ccc0ffccffccccc0ccc0ffccffcc
lemma h9Bound : Lower h9R h9G 5 := lift_of (z := 4) (o := 0) (essPairs := [(VAR 2,34,38)]) (by decide +kernel) h10Bound
def h11R : List Nat := varsOf 46
def h11G : Nat := 0xccfcccfcf0ccf0ccccfcccfcf0ccf0cc
lemma h11Bound : Lower h11R h11G 6 := carry_of (swaps := [(2,3),(0,1)]) (roots2 := h2R) (T2 := h2G) (by decide +kernel) h2Bound
def h13R : List Nat := varsOf 14
def h13G : Nat := 0xf3c0f3c0f3c0f3c0f3c0f3c0f3c0f3c0
lemma h13Bound : Lower h13R h13G 3 := carry_of (swaps := [(0,1),(1,2),(2,3)]) (roots2 := h4R) (T2 := h4G) (by decide +kernel) h4Bound
def h12R : List Nat := varsOf 46
def h12G : Nat := 0xfff0fff0f3c0f3c0fff0fff0f3c0f3c0
def h12Pos : List Nat := [8,36,6,6,8,42,36,42,12,14]
def h12Neg : List Nat := [10,32,2,4,0,34,4,10,4,10]
def h12Mask : Nat := fullMask 10
def h12Base : List Decor := [(0xcccccccccccccccccccccccccccccccc,684,677),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,846,328),(0xff00ff00ff00ff00ff00ff00ff00ff00,945,641),(0xffffffff00000000ffffffff00000000,226,34)]
def h12Steps : List (Nat × Nat × Nat) := []
def h12W : BT Decor := buildWiresBT 2 h12Base h12Steps
def h12AutoList : List (List (Nat × Nat)) := [[]]
def h12Autos : BT (List (Nat × Nat)) := btOfList 1 h12AutoList
lemma h12Pairs : goodPairs h12G h12Pos h12Neg := goodPairs_of (by decide +kernel)
lemma h12BaseOk : ∀ x ∈ h12Base, faithful h12Pos h12Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma h12WOk : btAll (fun x => faithful h12Pos h12Neg x ∧ x.1 < 2^128) h12W := buildWiresBT_faithful h12BaseOk
lemma h12AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h12G = h12G) h12Autos := btAll_ofList (autos_of (by decide +kernel))
def h12SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 32 0,3)]
def h12Slices : BT (Option (Nat × Nat)) := btOfList 1 h12SliceList
def h12Specs : List PoolSpec := [(0,[])]
def h12Pools : BT (Option BoundPool) := buildPoolsBT 1 h12W h12R h12Slices h12Specs
set_option maxRecDepth 200000 in
lemma h12Slice0 : Slice h12R h12G (subcubeFast 32 0) 3 := slice_fast_direct (zDead := 0) (by decide +kernel) h13Bound
lemma h12SlicesOk : btAll (sliceSpec h12R h12G) h12Slices := btAll_ofList (P := sliceSpec h12R h12G) (sliceSpecCons h12Slice0 sliceSpecNil)
lemma h12PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h12R h12G c) h12Pools := buildPoolsBT_sound h12SlicesOk
def h12Empty : BT (List (List Nat)) := BT.empty
lemma h12EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h12G (4 - 1) xs.toFinset) h12Empty := trivial
def h12Block4_0 : List NodeSpec := priorityNodes 1 [(30,2,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h12Test4_0 : checkNodesBT h12W h12G h12Mask h12Pools h12Autos h12Empty 4 h12Block4_0 = true := by decide +kernel
def h12Nodes4 : List NodeSpec := h12Block4_0
lemma h12Check4 : checkNodesBT h12W h12G h12Mask h12Pools h12Autos h12Empty 4 h12Nodes4 = true := h12Test4_0
def h12Bucket4 : BT (List (List Nat)) := buildBucketsBT h12W h12Nodes4
lemma h12Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h12G 4 xs.toFinset) h12Bucket4 := buildBucketsBT_sound (by decide) h12Pairs h12WOk h12PoolsOk h12AutosOk h12EmptyOk h12Check4
lemma h12Bound : Lower h12R h12G 5 := lower_of_forestBT (essPairs := [(VAR 1,4,6),(VAR 2,2,6),(VAR 3,0,8),(VAR 5,4,36)]) (by decide +kernel) h12Bucket4Ok (by decide +kernel)
def h15R : List Nat := varsOf 35
def h15G : Nat := 0xeeeeeeee88888888eeeeeeee88888888
lemma h15Bound : Lower h15R h15G 4 := carry_of (swaps := [(1,2),(2,3),(0,1),(1,2)]) (roots2 := h3R) (T2 := h3G) (by decide +kernel) h3Bound
def h14R : List Nat := varsOf 39
def h14G : Nat := 0xeeeeeeeec8c8c8c8eeeeeeeec8c8c8c8
lemma h14Bound : Lower h14R h14G 5 := lift_of (z := 4) (o := 0) (essPairs := [(VAR 2,2,6)]) (by decide +kernel) h15Bound
def h16R : List Nat := varsOf 43
def h16G : Nat := 0xeeeeeeeeaa88aa88eeeeeeeeaa88aa88
lemma h16Bound : Lower h16R h16G 5 := carry_of (swaps := [(2,3),(0,1)]) (roots2 := h14R) (T2 := h14G) (by decide +kernel) h14Bound
def h17R : List Nat := varsOf 45
def h17G : Nat := 0xfffafffafa00fa00fffafffafa00fa00
lemma h17Bound : Lower h17R h17G 5 := lift_of (z := 1) (o := 0) (essPairs := [(VAR 0,8,9)]) (by decide +kernel) h3Bound
def h19R : List Nat := varsOf 37
def h19G : Nat := 0xa0a0a0a0fafafafaa0a0a0a0fafafafa
lemma h19Bound : Lower h19R h19G 4 := carry_of (swaps := [(2,3),(0,1)]) (roots2 := h10R) (T2 := h10G) (by decide +kernel) h10Bound
def h20R : List Nat := varsOf 41
def h20G : Nat := 0xffaaffaaaa00aa00ffaaffaaaa00aa00
lemma h20Bound : Lower h20R h20G 4 := carry_of (swaps := [(1,2),(0,1)]) (roots2 := h3R) (T2 := h3G) (by decide +kernel) h3Bound
def h18R : List Nat := varsOf 45
def h18G : Nat := 0xffa0ffa0fa00fa00ffa0ffa0fa00fa00
def h18Pos : List Nat := [9,12,12,9,37,40,37,37,13,40,9]
def h18Neg : List Nat := [8,8,4,1,5,8,36,33,5,32,0]
def h18Mask : Nat := fullMask 11
def h18Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,1497,408),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,470,340),(0xff00ff00ff00ff00ff00ff00ff00ff00,1839,35),(0xffffffff00000000ffffffff00000000,752,704)]
def h18Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,2),(3,0,2)]
def h18W : BT Decor := buildWiresBT 3 h18Base h18Steps
def h18AutoList : List (List (Nat × Nat)) := [[],[(2,5)],[(0,2)],[(0,5)],[(2,5),(0,2)],[(2,5),(0,5)]]
def h18Autos : BT (List (Nat × Nat)) := btOfList 3 h18AutoList
lemma h18Pairs : goodPairs h18G h18Pos h18Neg := goodPairs_of (by decide +kernel)
lemma h18BaseOk : ∀ x ∈ h18Base, faithful h18Pos h18Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma h18WOk : btAll (fun x => faithful h18Pos h18Neg x ∧ x.1 < 2^128) h18W := buildWiresBT_faithful h18BaseOk
lemma h18AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h18G = h18G) h18Autos := btAll_ofList (autos_of (by decide +kernel))
def h18SliceList : List (Option (Nat × Nat)) := [some (0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5,4),some (0xaaaaaaaa55555555aaaaaaaa55555555,4),some (0xf0f0f0f00f0f0f0ff0f0f0f00f0f0f0f,4),some (0x55aa55aa55aa55aa55aa55aa55aa55aa,4),some (0xff00ff00ff00ff00ff00ff00ff00ff0,4),some (0xff00ffff00ff0000ff00ffff00ff00,4)]
def h18Slices : BT (Option (Nat × Nat)) := btOfList 3 h18SliceList
def h18Specs : List PoolSpec := [(0,[]),(3,[]),(1,[]),(4,[]),(2,[]),(5,[])]
def h18Pools : BT (Option BoundPool) := buildPoolsBT 3 h18W h18R h18Slices h18Specs
set_option maxRecDepth 200000 in
lemma h18Slice5 : Slice h18R h18G (0xff00ffff00ff0000ff00ffff00ff00) 4 := opposite_slice (oppositeRow 3 5 37) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h19Bound
set_option maxRecDepth 200000 in
lemma h18Slice4 : Slice h18R h18G (0xff00ff00ff00ff00ff00ff00ff00ff0) 4 := opposite_slice (oppositeRow 2 3 41) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h20Bound
set_option maxRecDepth 200000 in
lemma h18Slice3 : Slice h18R h18G (0x55aa55aa55aa55aa55aa55aa55aa55aa) 4 := opposite_slice (oppositeRow 0 3 44) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h3Bound
set_option maxRecDepth 200000 in
lemma h18Slice2 : Slice h18R h18G (0xf0f0f0f00f0f0f0ff0f0f0f00f0f0f0f) 4 := mapped_slice (identifyRow 2 5 41) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h20Bound
set_option maxRecDepth 200000 in
lemma h18Slice1 : Slice h18R h18G (0xaaaaaaaa55555555aaaaaaaa55555555) 4 := mapped_slice (identifyRow 0 5 44) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h3Bound
set_option maxRecDepth 200000 in
lemma h18Slice0 : Slice h18R h18G (0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5) 4 := mapped_slice (identifyRow 0 2 44) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h3Bound
lemma h18SlicesOk : btAll (sliceSpec h18R h18G) h18Slices := btAll_ofList (P := sliceSpec h18R h18G) (sliceSpecCons h18Slice0 (sliceSpecCons h18Slice1 (sliceSpecCons h18Slice2 (sliceSpecCons h18Slice3 (sliceSpecCons h18Slice4 (sliceSpecCons h18Slice5 sliceSpecNil))))))
lemma h18PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h18R h18G c) h18Pools := buildPoolsBT_sound h18SlicesOk
def h18Empty : BT (List (List Nat)) := BT.empty
lemma h18EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h18G (4 - 1) xs.toFinset) h18Empty := trivial
def h18Block4_0 : List NodeSpec := priorityNodes 3 [(62,8,2),(94,8,2),(158,1,2),(286,1,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18Test4_0 : checkNodesBT h18W h18G h18Mask h18Pools h18Autos h18Empty 4 h18Block4_0 = true := by decide +kernel
def h18Nodes4 : List NodeSpec := h18Block4_0
lemma h18Check4 : checkNodesBT h18W h18G h18Mask h18Pools h18Autos h18Empty 4 h18Nodes4 = true := h18Test4_0
def h18Bucket4 : BT (List (List Nat)) := buildBucketsBT h18W h18Nodes4
lemma h18Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h18G 4 xs.toFinset) h18Bucket4 := buildBucketsBT_sound (by decide) h18Pairs h18WOk h18PoolsOk h18AutosOk h18EmptyOk h18Check4
def h18Block5_0 : List NodeSpec := priorityNodes 3 [(30,444040,30)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18Test5_0 : checkNodesBT h18W h18G h18Mask h18Pools h18Autos h18Bucket4 5 h18Block5_0 = true := by decide +kernel
def h18Nodes5 : List NodeSpec := h18Block5_0
lemma h18Check5 : checkNodesBT h18W h18G h18Mask h18Pools h18Autos h18Bucket4 5 h18Nodes5 = true := h18Test5_0
def h18Bucket5 : BT (List (List Nat)) := buildBucketsBT h18W h18Nodes5
lemma h18Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h18G 5 xs.toFinset) h18Bucket5 := buildBucketsBT_sound (by decide) h18Pairs h18WOk h18PoolsOk h18AutosOk h18Bucket4Ok h18Check5
lemma h18Bound : Lower h18R h18G 6 := lower_of_forestBT (essPairs := [(VAR 0,8,9),(VAR 2,8,12),(VAR 3,1,9),(VAR 5,5,37)]) (by decide +kernel) h18Bucket5Ok (by decide +kernel)
def h21R : List Nat := varsOf 46
def h21G : Nat := 0xfffcfffcf0c0f0c0fffcfffcf0c0f0c0
lemma h21Bound : Lower h21R h21G 5 := carry_of (swaps := [(2,3),(0,1)]) (roots2 := h17R) (T2 := h17G) (by decide +kernel) h17Bound
def h22R : List Nat := varsOf 46
def h22G : Nat := 0xfcf0fcf0f0c0f0c0fcf0fcf0f0c0f0c0
lemma h22Bound : Lower h22R h22G 6 := carry_of (swaps := [(2,3),(0,1)]) (roots2 := h18R) (T2 := h18G) (by decide +kernel) h18Bound
def h23R : List Nat := varsOf 7
def h23G : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
lemma h23Bound : Lower h23R h23G 4 := carry_of (swaps := [(4,5),(1,2),(2,3),(3,4),(0,1),(1,2),(2,3)]) (roots2 := h3R) (T2 := h3G) (by decide +kernel) h3Bound
def h24R : List Nat := varsOf 39
def h24G : Nat := 0xe8e8e8e8c8c8c8c8e8e8e8e8c8c8c8c8
lemma h24Bound : Lower h24R h24G 5 := lift_of (z := 0) (o := 32) (essPairs := [(VAR 5,5,37)]) (by decide +kernel) h23Bound
def h25R : List Nat := varsOf 11
def h25G : Nat := 0xee88ee88ee88ee88ee88ee88ee88ee88
lemma h25Bound : Lower h25R h25G 4 := carry_of (swaps := [(4,5),(1,2),(2,3),(3,4),(0,1),(1,2)]) (roots2 := h3R) (T2 := h3G) (by decide +kernel) h3Bound
def h26R : List Nat := varsOf 43
def h26G : Nat := 0xee88ee88aa88aa88ee88ee88aa88aa88
lemma h26Bound : Lower h26R h26G 5 := carry_of (swaps := [(2,3),(0,1)]) (roots2 := h24R) (T2 := h24G) (by decide +kernel) h24Bound
def h27R : List Nat := varsOf 45
def h27G : Nat := 0xaaa0aaa0fa00fa00aaa0aaa0fa00fa00
def h27Pos : List Nat := [9,12,37,37,12,9,12,37,41]
def h27Neg : List Nat := [8,8,33,36,4,1,44,5,33]
def h27Mask : Nat := fullMask 9
def h27Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,429,420),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,222,216),(0xff00ff00ff00ff00ff00ff00ff00ff00,371,67),(0xffffffff00000000ffffffff00000000,396,332)]
def h27Steps : List (Nat × Nat × Nat) := []
def h27W : BT Decor := buildWiresBT 2 h27Base h27Steps
def h27AutoList : List (List (Nat × Nat)) := [[]]
def h27Autos : BT (List (Nat × Nat)) := btOfList 1 h27AutoList
lemma h27Pairs : goodPairs h27G h27Pos h27Neg := goodPairs_of (by decide +kernel)
lemma h27BaseOk : ∀ x ∈ h27Base, faithful h27Pos h27Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma h27WOk : btAll (fun x => faithful h27Pos h27Neg x ∧ x.1 < 2^128) h27W := buildWiresBT_faithful h27BaseOk
lemma h27AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h27G = h27G) h27Autos := btAll_ofList (autos_of (by decide +kernel))
def h27SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 4,3)]
def h27Slices : BT (Option (Nat × Nat)) := btOfList 1 h27SliceList
def h27Specs : List PoolSpec := [(0,[])]
def h27Pools : BT (Option BoundPool) := buildPoolsBT 1 h27W h27R h27Slices h27Specs
set_option maxRecDepth 200000 in
lemma h27Slice0 : Slice h27R h27G (subcubeFast 0 4) 3 := slice_fast_direct (zDead := 0) (by decide +kernel) h8Bound
lemma h27SlicesOk : btAll (sliceSpec h27R h27G) h27Slices := btAll_ofList (P := sliceSpec h27R h27G) (sliceSpecCons h27Slice0 sliceSpecNil)
lemma h27PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h27R h27G c) h27Pools := buildPoolsBT_sound h27SlicesOk
def h27Empty : BT (List (List Nat)) := BT.empty
lemma h27EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h27G (4 - 1) xs.toFinset) h27Empty := trivial
def h27Block4_0 : List NodeSpec := priorityNodes 1 [(30,2,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27Test4_0 : checkNodesBT h27W h27G h27Mask h27Pools h27Autos h27Empty 4 h27Block4_0 = true := by decide +kernel
def h27Nodes4 : List NodeSpec := h27Block4_0
lemma h27Check4 : checkNodesBT h27W h27G h27Mask h27Pools h27Autos h27Empty 4 h27Nodes4 = true := h27Test4_0
def h27Bucket4 : BT (List (List Nat)) := buildBucketsBT h27W h27Nodes4
lemma h27Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h27G 4 xs.toFinset) h27Bucket4 := buildBucketsBT_sound (by decide) h27Pairs h27WOk h27PoolsOk h27AutosOk h27EmptyOk h27Check4
lemma h27Bound : Lower h27R h27G 5 := lower_of_forestBT (essPairs := [(VAR 0,8,9),(VAR 2,8,12),(VAR 3,1,9),(VAR 5,5,37)]) (by decide +kernel) h27Bucket4Ok (by decide +kernel)
def h28R : List Nat := varsOf 38
def h28G : Nat := 0xccccccccf0f0f0f0ccccccccf0f0f0f0
lemma h28Bound : Lower h28R h28G 3 := carry_of (swaps := [(2,3),(3,4),(4,5),(0,1),(1,2)]) (roots2 := h4R) (T2 := h4G) (by decide +kernel) h4Bound
def h29R : List Nat := varsOf 46
def h29G : Nat := 0xccc0ccc0f0c0f0c0ccc0ccc0f0c0f0c0
lemma h29Bound : Lower h29R h29G 5 := carry_of (swaps := [(2,3),(0,1)]) (roots2 := h27R) (T2 := h27G) (by decide +kernel) h27Bound
def h30R : List Nat := varsOf 15
def h30G : Nat := 0xeee8eee8eee8eee8eee8eee8eee8eee8
lemma h30Bound : Lower h30R h30G 5 := carry_of (swaps := [(4,5),(1,2),(2,3),(3,4),(1,2),(2,3),(0,1),(1,2)]) (roots2 := h17R) (T2 := h17G) (by decide +kernel) h17Bound
def h31R : List Nat := varsOf 39
def h31G : Nat := 0xeeeeeeeefafafafaeeeeeeeefafafafa
lemma h31Bound : Lower h31R h31G 4 := lift_of (z := 1) (o := 0) (essPairs := [(VAR 0,0,1)]) (by decide +kernel) h28Bound
def h32R : List Nat := varsOf 43
def h32G : Nat := 0xeeeeeeeeffccffcceeeeeeeeffccffcc
lemma h32Bound : Lower h32R h32G 4 := carry_of (swaps := [(2,3),(0,1)]) (roots2 := h31R) (T2 := h31G) (by decide +kernel) h31Bound
def h1R : List Nat := varsOf 47
def h1G : Nat := 0xeee8eee8fac8fac8eee8eee8fac8fac8
def h1Pos : List Nat := [6,9,6,6,37,37,12,9,12,37,3,42,42,42,3,45,46,6,12,6,37,7,35,35,11,9,6,41,38,13,41,3,7,3,11,3,35,12,14,13,12,13,37,7,12,6,14,35,38,41,9,41,38,3,41,14,12,12,37,38,37,9,42,13,35,38]
def h1Neg : List Nat := [4,8,5,2,33,36,4,1,44,5,2,40,34,10,1,44,44,10,8,34,1,5,33,34,10,10,36,44,34,5,40,0,2,10,2,34,2,5,10,4,0,44,4,4,10,0,4,32,4,33,33,1,44,33,8,8,36,40,32,2,0,40,2,8,1,36]
def h1Mask : Nat := fullMask 66
def h1Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x1b46e8e9febf0c6b2,0x1002e002020704294),(0xcccccccccccccccccccccccccccccccc,0x348b1e85f95eb7c0d,0x4800105f138a3408),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x29f917fe1343f837d,0x201114ea02c218365),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xe3ce53e46b05b9c2,0xa2d012424b07a902),(0xffffffff00000000ffffffff00000000,0x35c5b841058d1ba30,0x2273682085cc99930)]
def h1Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(0,0,2),(1,0,2),(2,0,2),(3,0,2),(0,0,3),(1,0,3),(2,0,3),(3,0,3),(0,0,4),(1,0,4),(2,0,4),(3,0,4),(0,1,2),(1,1,2),(2,1,2),(3,1,2),(0,1,3),(1,1,3),(3,1,3),(0,1,4),(1,1,4),(3,1,4),(0,2,3),(1,0,30),(1,2,3),(2,2,3),(3,2,3),(0,2,4),(1,2,4),(2,2,4),(3,2,4),(1,2,5),(0,3,4),(1,3,4),(2,3,4),(3,3,4),(0,3,39),(0,4,39),(3,4,39),(2,2,5),(1,3,5),(1,4,5),(2,4,5),(2,0,50),(2,1,50),(0,2,50),(2,2,50),(1,5,30),(1,0,35),(1,1,35),(1,3,35),(2,3,35),(3,35,48),(1,5,59),(1,5,35),(1,0,37),(0,1,63),(1,1,63),(2,1,63),(3,1,63),(2,0,37),(1,1,37),(1,5,37),(0,0,45),(2,3,45),(2,3,53),(0,2,6),(3,2,6),(0,3,9),(3,3,9),(0,4,6),(2,4,6),(3,4,6),(0,4,9),(2,4,9),(0,6,9),(0,6,25),(0,9,25),(3,1,9),(1,1,33),(2,6,33),(2,9,33),(0,4,57),(0,1,58),(3,1,58),(0,4,58),(2,4,58),(1,1,78),(2,9,35),(2,6,35),(1,1,74),(1,1,79),(1,1,10),(1,3,10),(1,4,10),(2,4,10),(2,6,10),(1,1,11),(1,3,11),(2,4,75),(3,1,13),(3,2,13),(0,4,13),(1,0,110),(0,1,110),(1,1,110),(2,1,110),(3,1,110),(0,2,110),(1,2,110),(2,2,110),(3,2,110),(1,3,110),(3,4,13),(1,1,15),(1,2,15),(3,1,17),(1,0,78),(1,2,19),(1,3,19),(3,1,31),(2,6,30),(3,0,32),(3,1,32),(1,0,93),(3,0,93),(1,2,93),(3,4,32),(0,6,32),(1,0,33),(3,1,56),(3,0,57),(3,0,36),(3,1,36),(0,6,36),(2,6,37),(1,1,107),(3,1,107),(1,0,79),(1,1,80),(1,3,7),(2,4,7),(1,7,35),(1,2,7),(3,0,21),(0,4,152),(3,4,21),(1,0,26),(1,2,26),(0,4,148),(3,0,28),(1,7,30),(1,7,34),(0,4,151),(3,7,36),(1,1,162),(1,7,37),(1,1,161),(3,0,134),(2,2,40),(1,0,167),(1,7,40),(1,1,42),(1,7,42),(1,3,8),(1,8,24),(3,1,172),(0,4,172),(1,8,26),(1,2,16),(2,9,40),(2,9,29),(2,9,93),(0,9,32),(3,19,32),(1,19,43),(2,9,26),(1,1,184),(1,2,179),(3,0,87),(2,9,38),(1,2,77),(2,4,77),(1,10,29),(3,1,101),(0,4,101),(0,3,103),(2,3,103),(1,10,26),(1,10,40),(2,3,145),(1,1,198),(2,4,109),(3,11,21),(1,11,26),(3,1,202),(0,2,84),(1,2,84),(2,2,84),(3,2,84),(2,1,12),(2,2,12),(1,4,12),(3,20,183),(1,12,20),(0,21,183),(1,12,90),(3,12,21),(1,12,22),(2,4,204),(0,4,205),(0,21,110),(1,2,219),(2,21,110),(0,13,21),(2,13,22),(2,4,108),(2,13,27),(2,13,29),(2,13,35),(2,2,112),(1,1,14),(2,4,14),(1,14,22),(1,14,27),(0,4,232),(1,1,230),(1,14,29),(0,4,189),(1,14,35),(0,4,123),(1,16,42),(3,1,120),(2,17,29),(2,2,18),(1,3,52),(3,0,69),(1,19,37),(3,1,41),(3,1,127),(1,3,64),(3,3,65)]
def h1W : BT Decor := buildWiresBT 8 h1Base h1Steps
def h1AutoList : List (List (Nat × Nat)) := [[],[(2,3),(0,1)]]
def h1Autos : BT (List (Nat × Nat)) := btOfList 1 h1AutoList
lemma h1Pairs : goodPairs h1G h1Pos h1Neg := goodPairs_of (by decide +kernel)
lemma h1BaseOk : ∀ x ∈ h1Base, faithful h1Pos h1Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma h1WOk : btAll (fun x => faithful h1Pos h1Neg x ∧ x.1 < 2^128) h1W := buildWiresBT_faithful h1BaseOk
lemma h1AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h1G = h1G) h1Autos := btAll_ofList (autos_of (by decide +kernel))
def h1SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 4,4),some (subcubeFast 0 8,4),some (subcubeFast 0 32,5),some (subcubeFast 1 0,5),some (subcubeFast 1 8,3),some (subcubeFast 2 0,5),some (subcubeFast 2 4,3),some (subcubeFast 4 0,5),some (subcubeFast 4 32,4),some (subcubeFast 8 0,5),some (subcubeFast 8 32,4),some (0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5,6),some (0xaaaaaaaa55555555aaaaaaaa55555555,5),some (0xcc33cc33cc33cc33cc33cc33cc33cc33,6),some (0xcccccccc33333333cccccccc33333333,5),some (0xf0f0f0f00f0f0f0ff0f0f0f00f0f0f0f,5),some (0xff00ff0000ff00ffff00ff0000ff00ff,5),some (0x66666666666666666666666666666666,5),some (0x55aa55aa55aa55aa55aa55aa55aa55aa,6),some (0x55555555aaaaaaaa55555555aaaaaaaa,5),some (0x3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c,6)]
def h1Slices : BT (Option (Nat × Nat)) := btOfList 5 h1SliceList
def h1Specs : List PoolSpec := poolSteps h1Steps [(3,[]),(5,[]),(7,[]),(9,[]),(8,[]),(11,[]),(13,[]),(4,[]),(6,[]),(1,[]),(10,[]),(2,[54]),(2,[]),(19,[]),(0,[]),(16,[]),(15,[]),(11,[1]),(17,[]),(9,[116]),(12,[]),(20,[]),(18,[]),(14,[]),(7,[85]),(3,[35]),(3,[37]),(3,[170]),(7,[170]),(9,[105]),(7,[14]),(7,[88]),(2,[53]),(11,[14]),(16,[4]),(7,[98]),(7,[97]),(20,[6]),(16,[6]),(5,[30]),(3,[105]),(3,[116]),(9,[233]),(7,[35]),(9,[24]),(12,[238]),(9,[30]),(5,[32]),(7,[130]),(9,[130])]
def h1Pools : BT (Option BoundPool) := buildPoolsBT 6 h1W h1R h1Slices h1Specs
set_option maxRecDepth 200000 in
lemma h1Slice20 : Slice h1R h1G (0x3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c) 6 := opposite_slice (oppositeRow 1 2 45) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h2Bound
set_option maxRecDepth 200000 in
lemma h1Slice19 : Slice h1R h1G (0x55555555aaaaaaaa55555555aaaaaaaa) 5 := opposite_slice (oppositeRow 0 5 46) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h9Bound
set_option maxRecDepth 200000 in
lemma h1Slice18 : Slice h1R h1G (0x55aa55aa55aa55aa55aa55aa55aa55aa) 6 := opposite_slice (oppositeRow 0 3 46) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h11Bound
set_option maxRecDepth 200000 in
lemma h1Slice17 : Slice h1R h1G (0x66666666666666666666666666666666) 5 := opposite_slice (oppositeRow 0 1 46) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h12Bound
set_option maxRecDepth 200000 in
lemma h1Slice16 : Slice h1R h1G (0xff00ff0000ff00ffff00ff0000ff00ff) 5 := mapped_slice (identifyRow 3 5 39) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h14Bound
set_option maxRecDepth 200000 in
lemma h1Slice15 : Slice h1R h1G (0xf0f0f0f00f0f0f0ff0f0f0f00f0f0f0f) 5 := mapped_slice (identifyRow 2 5 43) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h16Bound
set_option maxRecDepth 200000 in
lemma h1Slice14 : Slice h1R h1G (0xcccccccc33333333cccccccc33333333) 5 := mapped_slice (identifyRow 1 5 45) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h17Bound
set_option maxRecDepth 200000 in
lemma h1Slice13 : Slice h1R h1G (0xcc33cc33cc33cc33cc33cc33cc33cc33) 6 := mapped_slice (identifyRow 1 3 45) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h18Bound
set_option maxRecDepth 200000 in
lemma h1Slice12 : Slice h1R h1G (0xaaaaaaaa55555555aaaaaaaa55555555) 5 := mapped_slice (identifyRow 0 5 46) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h21Bound
set_option maxRecDepth 200000 in
lemma h1Slice11 : Slice h1R h1G (0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5) 6 := mapped_slice (identifyRow 0 2 46) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h22Bound
set_option maxRecDepth 200000 in
lemma h1Slice10 : Slice h1R h1G (subcubeFast 8 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h23Bound
set_option maxRecDepth 200000 in
lemma h1Slice9 : Slice h1R h1G (subcubeFast 8 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h24Bound
set_option maxRecDepth 200000 in
lemma h1Slice8 : Slice h1R h1G (subcubeFast 4 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h25Bound
set_option maxRecDepth 200000 in
lemma h1Slice7 : Slice h1R h1G (subcubeFast 4 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h26Bound
set_option maxRecDepth 200000 in
lemma h1Slice6 : Slice h1R h1G (subcubeFast 2 4) 3 := slice_fast_direct (zDead := 0) (by decide +kernel) h8Bound
set_option maxRecDepth 200000 in
lemma h1Slice5 : Slice h1R h1G (subcubeFast 2 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h27Bound
set_option maxRecDepth 200000 in
lemma h1Slice4 : Slice h1R h1G (subcubeFast 1 8) 3 := slice_fast_direct (zDead := 0) (by decide +kernel) h28Bound
set_option maxRecDepth 200000 in
lemma h1Slice3 : Slice h1R h1G (subcubeFast 1 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h29Bound
set_option maxRecDepth 200000 in
lemma h1Slice2 : Slice h1R h1G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h30Bound
set_option maxRecDepth 200000 in
lemma h1Slice1 : Slice h1R h1G (subcubeFast 0 8) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h31Bound
set_option maxRecDepth 200000 in
lemma h1Slice0 : Slice h1R h1G (subcubeFast 0 4) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h32Bound
lemma h1SlicesOk : btAll (sliceSpec h1R h1G) h1Slices := btAll_ofList (P := sliceSpec h1R h1G) (sliceSpecCons h1Slice0 (sliceSpecCons h1Slice1 (sliceSpecCons h1Slice2 (sliceSpecCons h1Slice3 (sliceSpecCons h1Slice4 (sliceSpecCons h1Slice5 (sliceSpecCons h1Slice6 (sliceSpecCons h1Slice7 (sliceSpecCons h1Slice8 (sliceSpecCons h1Slice9 (sliceSpecCons h1Slice10 (sliceSpecCons h1Slice11 (sliceSpecCons h1Slice12 (sliceSpecCons h1Slice13 (sliceSpecCons h1Slice14 (sliceSpecCons h1Slice15 (sliceSpecCons h1Slice16 (sliceSpecCons h1Slice17 (sliceSpecCons h1Slice18 (sliceSpecCons h1Slice19 (sliceSpecCons h1Slice20 sliceSpecNil)))))))))))))))))))))
set_option maxRecDepth 200000 in
lemma h1PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h1R h1G c) h1Pools := buildPoolsBT_sound h1SlicesOk
def h1Empty : BT (List (List Nat)) := BT.empty
lemma h1EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h1G (4 - 1) xs.toFinset) h1Empty := trivial
def h1Block4_0 : List NodeSpec := priorityNodes 6 [(85997623,1,2),(462895,1,2),(4997647,1,2),(471087,1,2),(130228309,1,2),(281032759,1,2),(24658447,1,2),(5210301,71,2),(25434441,1,2),(25958757,1,2),(5839850021,1,2),(20473359,1,2),(105308325,1,2),(32622645,1,2),(30737238565,71,2),(275779855,1,2),(313528591,1,2),(5570093079,1,2),(4999906889,1,2),(1250019877,1,2),(4798450213,1,2),(4999776805,6110,2),(363859109,1,2),(1292012069,1,2),(662782085,6151,2),(5201103397,1,2),(5242489381,88,2),(136374389285,1,2),(86983838245,6087,2),(5872242711,95,2),(1447035957,1,2),(1602300943,1,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test4_0 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Empty 4 h1Block4_0 = true := by decide +kernel
def h1Block4_1 : List NodeSpec := priorityNodes 6 [(6476304427,1,2),(1132585287,1,2),(1699901,1,2),(6744576053,1,2),(1708063,1,2),(4597092413,1,2),(27406379,1,2),(1724447,1,2),(1732639,1,2),(17918210091,1,2),(18052427819,1,2),(1773599,1,2),(1789983,1,2),(7415885847,1,2),(7952756759,1,2),(1963290677,1,2),(338231298085,1,2),(73553281671,96,2),(4932718615,1,2),(89124254471,1,2),(24897839189,1,2),(25032056917,1,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test4_1 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Empty 4 h1Block4_1 = true := by decide +kernel
def h1Nodes4 : List NodeSpec := h1Block4_0 ++ h1Block4_1
lemma h1Check4 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Empty 4 h1Nodes4 = true := by
  unfold h1Nodes4 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h1Test4_0,h1Test4_1⟩
def h1Bucket4 : BT (List (List Nat)) := buildBucketsBT h1W h1Nodes4
set_option maxRecDepth 200000 in
lemma h1Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h1G 4 xs.toFinset) h1Bucket4 := buildBucketsBT_sound (by decide) h1Pairs h1WOk h1PoolsOk h1AutosOk h1EmptyOk h1Check4
def h1Block5_0 : List NodeSpec := priorityNodes 6 [(10004567,1,2),(10759711,1,2),(211007,4485,2),(2422871,71,2),(14219311,73,2),(893103,307394,2),(16253983,71,2),(239679,299200,2),(958709,20205706,2),(2633815,4416,2),(48246831,64,2),(14160927,4928,2),(544831,4416,2),(11563095,1,2),(13660247,71,2),(15757399,4416,2),(170047,323907,2),(949279,71,2),(2391071,4928,2),(2165949,71,2),(12858021,1,2),(13906597,1,2),(137376421,1,2),(36439669,1,2),(36963957,69,2),(35916405,1,2),(36440693,69,2),(12910965,1,2),(33820247,1,2),(3424479,71,2),(3784927,5321,2),(16125215,1,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test5_0 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket4 5 h1Block5_0 = true := by decide +kernel
def h1Block5_1 : List NodeSpec := priorityNodes 6 [(835957,69,2),(190883927,1,2),(1028159,1,2),(2867423,4615,2),(8487135,1,2),(2170943,4615,2),(34472309,69,2),(692287,1,2),(3309941,69,2),(3375467,64,2),(3440943,1,2),(3506479,75,2),(182453279,84,2),(766015,1,2),(2269247,1,2),(3768693,69,2),(645935191,1,2),(174068767,1,2),(2285631,64,2),(847935,345027,2),(2334783,1,2),(610367,1,2),(13899429,71,2),(147326581,1,2),(38142837,1,2),(10944671,5640,2),(38666399,1,2),(38929269,1,2),(1027631151,1,2),(39715701,1,2),(254813727,1,2),(36569973,1,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test5_1 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket4 5 h1Block5_1 = true := by decide +kernel
def h1Block5_2 : List NodeSpec := priorityNodes 6 [(803701,1,2),(2547775,1,2),(2564159,1,2),(3244917,1,2),(977336407,71,2),(3441455,1,2),(960496671,71,2),(2400319,1,2),(35259243,76,2),(2596927,1,2),(3703669,1,2),(943723551,64,2),(2629695,69,2),(2580543,1,2),(13697909,1,2),(16712535,1,2),(42074967,1,2),(2711615,79,2),(42861419,70,2),(2744383,76,2),(1265695,73,2),(2515007,1,2),(2777151,1,2),(2457888815,1,2),(2826303,1,2),(2793535,1,2),(1413151,24179291,2),(13304479,5961,2),(4326452,1,2),(45352565,1,2),(51438901,1,2),(5243956,1,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test5_2 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket4 5 h1Block5_2 = true := by decide +kernel
def h1Block5_3 : List NodeSpec := priorityNodes 6 [(44123445,94,2),(47449717,1,2),(226823333,68,2),(276990501,19951646,2),(14428736677,97,2),(205604149,94,2),(1048659253,94,2),(138495255,71,2),(21366039,5640,2),(42731095,1,2),(667711,71,2),(253782123,78,2),(2957375,65,2),(241211499,76,2),(2875455,4424,2),(22152471,401864,2),(44303959,403463,2),(41158231,1,2),(42206807,1,2),(12715607,78,2),(46826775,78,2),(6488887,4359,2),(45876823,69,2),(629182511,78,2),(174074911,84,2),(2859071,66,2),(2973759,78,2),(3055679,66,2),(2646079,84,2),(44091189,1,2),(46926453,1,2),(633366575,1,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test5_3 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket4 5 h1Block5_3 = true := by decide +kernel
def h1Block5_4 : List NodeSpec := priorityNodes 6 [(162536991,1,2),(3153983,1,2),(156248607,6352,2),(3072063,64,2),(266349599,6352,2),(3170367,4418,2),(3088447,1,2),(3104831,66,2),(696403999,1,2),(713181215,406535,2),(3070380063,6352,2),(3103934495,72,2),(2302015,69,2),(51646039,1,2),(52166943,1,2),(83362327,78,2),(3028293719,68,2),(13879095,1,2),(152571479,1,2),(3252287,1,2),(63180375,1,2),(86508055,26797063,2),(3268671,1,2),(149947509,282692,2),(685770271,4743,2),(3416127,311685,2),(589300853,78,2),(266344555,4554,2),(681576991,74,2),(41157407,423438,2),(3465279,4864,2),(262154347,1,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test5_4 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket4 5 h1Block5_4 = true := by decide +kernel
def h1Block5_5 : List NodeSpec := priorityNodes 6 [(677383711,1,2),(3481663,64,2),(257964139,69,2),(673190431,1,2),(16173506667,286730,2),(16307724395,4743,2),(16441942123,1,2),(16576159851,1,2),(187697695,1,2),(3579967,76,2),(185601567,5961,2),(3596351,1,2),(717240427,78,2),(183505439,1,2),(235932789,65,6),(175120927,427855,6),(3629119,76,2),(170928671,70,6),(3645503,76,2),(3612735,1,2),(633340959,5972,2),(3661887,4866,2),(608181279,69,2),(3219519,66,2),(964639,1,2),(2799647,6685,6),(3848223,1,2),(9615391,5961,2),(11712543,1,6),(13809695,6685,2),(15906847,1,2),(35829791,104,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test5_5 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket4 5 h1Block5_5 = true := by decide +kernel
def h1Block5_6 : List NodeSpec := priorityNodes 6 [(40024095,1,2),(897087,84,2),(3727423,1,2),(233837685,1,2),(3743807,1,2),(845163039,70,2),(3792959,1,2),(3760191,1,2),(2592143447,73,2),(3279946783,79,2),(3825727,66,2),(3809343,66,2),(3776575,1,2),(1929247,330375,2),(229647477,1,2),(547366005,1,2),(2753055,64,2),(232795167,71,2),(224410655,1,2),(1937439,68,2),(3874879,1,2),(891300383,1,2),(63083643957,1,2),(3021210677,1,2),(941636655,109,6),(156238367,28964751,2),(2924607,76,2),(40370719,1,2),(196495279127,76,2),(20710159,395143,2),(52953631,72,2),(950010399,64,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test5_6 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket4 5 h1Block5_6 = true := by decide +kernel
def h1Block5_7 : List NodeSpec := priorityNodes 6 [(954204703,1,2),(924844575,1,2),(3989567,84,2),(1019967,1,2),(662808607,390023,2),(679585823,392071,2),(1392726039,452552,2),(2105407,84,2),(370719,20487071,2),(3006527,1,2),(2203711,1,2),(2220095,1,2),(36711455,1,2),(562221103,73,2),(578998319,1,6),(725055,66,2),(2613311,1,2),(1011829,20205706,2),(2846837,4426,2),(3895413,1,2),(9662581,1,2),(260159,69,2),(3940415,1,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test5_7 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket4 5 h1Block5_7 = true := by decide +kernel
def h1Nodes5 : List NodeSpec := h1Block5_0 ++ h1Block5_1 ++ h1Block5_2 ++ h1Block5_3 ++ h1Block5_4 ++ h1Block5_5 ++ h1Block5_6 ++ h1Block5_7
lemma h1Check5 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket4 5 h1Nodes5 = true := by
  unfold h1Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨h1Test5_0,h1Test5_1⟩,h1Test5_2⟩,h1Test5_3⟩,h1Test5_4⟩,h1Test5_5⟩,h1Test5_6⟩,h1Test5_7⟩
def h1Bucket5 : BT (List (List Nat)) := buildBucketsBT h1W h1Nodes5
set_option maxRecDepth 200000 in
lemma h1Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h1G 5 xs.toFinset) h1Bucket5 := buildBucketsBT_sound (by decide) h1Pairs h1WOk h1PoolsOk h1AutosOk h1Bucket4Ok h1Check5
def h1Block6_0 : List NodeSpec := priorityNodes 6 [(104575,274436,6),(125055,303554,2),(266367,270346,2),(290903,20475905,6),(145471,81656545358,2),(356439,266244,2),(95263,266244,2),(97311,18903104,6),(190527,71976382528,6),(1212,262216,2),(1214,1310007360,2),(2236,4552,2),(4286,18896001,2),(16574,21500103,2),(65726,4295,2),(94399,19924097,2),(110783,22070401,2),(401599,1376522242,6),(434367,336391,2),(450751,21508105,2),(483519,1378881538,2),(499903,336014,2),(516287,21544962,2),(1065151,4360,2),(4489407,21553233,2),(585791,81756696648,2),(4554943,336200,2),(610367,383601833676820,6),(4751551,4882,2),(618559,1448370516,6),(4882623,82,2),(1340,290824,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test6_0 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket5 6 h1Block6_0 = true := by decide +kernel
def h1Block6_1 : List NodeSpec := priorityNodes 6 [(119231,262280,2),(270783,4232,2),(319935,352640,2),(352703,4864,6),(369087,357120,2),(190,90397233671,2),(385471,4224,2),(451007,4288,2),(467391,311431,2),(483775,311360,2),(500159,4864,2),(516543,4360,2),(2416703,1276391880,2),(1098175,4313,2),(1163711,274522,2),(2367551,5925008621577,2),(2383935,4481849323527,6),(1081663,4160,2),(1212735,4099,2),(774207,18350532,2),(2760767,18386948,2),(17470,19149700,2),(66622,4295,2),(132156,290820,2),(689781,4100,2),(344895,1412489536,2),(820823,18620744,2),(951895,4360,2),(1082175,319687,2),(1147711,17571912,2),(1344319,1460146184,2),(675903,5991631946888,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test6_1 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket5 6 h1Block6_1 = true := by decide +kernel
def h1Block6_2 : List NodeSpec := priorityNodes 6 [(3081815,18104776,2),(3212887,4548,2),(3475031,295364,2),(3868247,4612,2),(2065215,19932035,2),(4522815,20456073,2),(17695551,299150,2),(602175,19931655,2),(17957695,274574,2),(634943,93753455108,2),(19006271,19923086,2),(643135,19149064,2),(625269,290820,2),(1082687,4426,2),(1279295,1463337088,2),(790591,93618466824,2),(1086,19149064,2),(2000191,1496330382,2),(798783,81705623561,2),(407583,26271754,2),(411679,25981440,2),(815167,93465903556,2),(20542,299204,2),(69694,4295,2),(691799,20476197,2),(509759,4290,6),(831551,91270440068,6),(2821719,4359,2),(839743,286983,6),(2105406,19431876,6),(4202558,1094230279,2),(8396862,20447489,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test6_2 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket5 6 h1Block6_2 = true := by decide +kernel
def h1Block6_3 : List NodeSpec := priorityNodes 6 [(1507903,4612,2),(1319019,4106,2),(659519,20455434,6),(6701163,266250,2),(5816407,294922,2),(2908223,283272,2),(6733911,274436,2),(1699871,274436,2),(1478687,4106,2),(427583,22069827,2),(4210750,20488457,6),(8405054,17621257,2),(1377855,4612,2),(1902143,1275858953,6),(4326975,357129,6),(856127,383882231284105,6),(5899839,19935369,2),(6686271,5124,2),(864319,1275891848,2),(440351,426589,6),(872511,7171860865098,6),(485407,27603524,6),(8421438,4160,2),(1247807,4610,2),(1772095,4160,2),(2034239,22855881,2),(3694655,5993829769792,2),(5638719,19935810,2),(6425151,4996,2),(3039295,1275629896,2),(3711039,93650948106,2),(1117759,291010,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test6_3 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket5 6 h1Block6_3 = true := by decide +kernel
def h1Block6_4 : List NodeSpec := priorityNodes 6 [(970815,20456071,2),(979007,295559,2),(1511999,4160,6),(1774143,356416,2),(749631,4481899655616,6),(2842687,19149064,2),(3214111,28140167,2),(3476255,4548,2),(954431,5925008573065,2),(15935,17081604,6),(822559,17039626,2),(987199,16851588,6),(2351167,20455434,2),(6045783,303108,2),(7815255,270346,2),(2753055,4514515829248,6),(1383999,1459930368,2),(782399,383601884053522,6),(84418111,19927060,6),(17571391,263434,6),(1777215,1412997700,2),(8651295,1203400708,2),(9699871,29099914,2),(1003583,1226060040,2),(112729663,18170624,2),(11797023,262788,2),(12845599,4743,2),(1011775,1310204553,2),(113778239,344263,2),(56383,21500100,2),(1036351,90499449351,6),(370719,86163190279,6)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test6_4 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket5 6 h1Block6_4 = true := by decide +kernel
def h1Block6_5 : List NodeSpec := priorityNodes 6 [(733247,93753209476,6),(64501279,19415559,2),(129000511,299652,2),(741439,295559,2),(1085471,1908457991,2),(217069087,295559,2),(2187327,21500167,2),(684095,1375994436,2),(58431,295175,2),(215103,1378103364,2),(219199,7100959055876,6),(2884639,27103876,6),(446511,4548,6),(223295,18367111,2),(454703,4292,6),(2236479,21500548,6),(2252863,21496456,2),(487541,4234,2),(243775,21500042,6),(1056885,270346,2),(536639,1388052618,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test6_5 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket5 6 h1Block6_5 = true := by decide +kernel
def h1Nodes6 : List NodeSpec := h1Block6_0 ++ h1Block6_1 ++ h1Block6_2 ++ h1Block6_3 ++ h1Block6_4 ++ h1Block6_5
lemma h1Check6 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket5 6 h1Nodes6 = true := by
  unfold h1Nodes6 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨h1Test6_0,h1Test6_1⟩,h1Test6_2⟩,h1Test6_3⟩,h1Test6_4⟩,h1Test6_5⟩
def h1Bucket6 : BT (List (List Nat)) := buildBucketsBT h1W h1Nodes6
set_option maxRecDepth 200000 in
lemma h1Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h1G 6 xs.toFinset) h1Bucket6 := buildBucketsBT_sound (by decide) h1Pairs h1WOk h1PoolsOk h1AutosOk h1Bucket5Ok h1Check6
def h1Block7_0 : List NodeSpec := priorityNodes 6 [(126,5225937137728,6),(190,379688044798016,6),(318,81655263296,2),(574,1124364292,2),(1086,5932474171908,2),(2110,71959347456,2),(4158,17567748,6),(8254,17305610,2),(9791,70886097558,6),(32830,92375650944,6),(65598,1443368970,6),(12863,1092395264,6),(13887,17040004,6),(14911,17055754,2),(15935,92363857924,6),(54335,17039556,6),(58431,379676184846788,6),(60479,1090531780,6),(64575,17040004,6),(133183,1090552074,6),(137279,17039498,6),(141375,91284865668,6)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test7_0 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket6 7 h1Block7_0 = true := by decide +kernel
def h1Nodes7 : List NodeSpec := h1Block7_0
lemma h1Check7 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket6 7 h1Nodes7 = true := h1Test7_0
def h1Bucket7 : BT (List (List Nat)) := buildBucketsBT h1W h1Nodes7
set_option maxRecDepth 200000 in
lemma h1Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h1G 7 xs.toFinset) h1Bucket7 := buildBucketsBT_sound (by decide) h1Pairs h1WOk h1PoolsOk h1AutosOk h1Bucket6Ok h1Check7
def h1Block8_0 : List NodeSpec := priorityNodes 6 [(62,1,6)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test8_0 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket7 8 h1Block8_0 = true := by decide +kernel
def h1Nodes8 : List NodeSpec := h1Block8_0
lemma h1Check8 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket7 8 h1Nodes8 = true := h1Test8_0
def h1Bucket8 : BT (List (List Nat)) := buildBucketsBT h1W h1Nodes8
set_option maxRecDepth 200000 in
lemma h1Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h1G 8 xs.toFinset) h1Bucket8 := buildBucketsBT_sound (by decide) h1Pairs h1WOk h1PoolsOk h1AutosOk h1Bucket7Ok h1Check8
set_option maxRecDepth 200000 in
lemma h1Bound : Lower h1R h1G 9 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,2,6),(VAR 3,1,9),(VAR 5,5,37)]) (by decide +kernel) h1Bucket8Ok (by decide +kernel)
def h34R : List Nat := varsOf 53
def h34G : Nat := 0xfafaffff0000aaaafafaffff0000aaaa
lemma h34Bound : Lower h34R h34G 5 := carry_of (swaps := [(1,2),(2,3),(3,4),(4,5),(1,2),(0,1)]) (roots2 := h9R) (T2 := h9G) (by decide +kernel) h9Bound
def h36R : List Nat := varsOf 52
def h36G : Nat := 0xf0f0ffff0000f0f0f0f0ffff0000f0f0
lemma h36Bound : Lower h36R h36G 4 := carry_of (swaps := [(3,4),(4,5),(1,2)]) (roots2 := h10R) (T2 := h10G) (by decide +kernel) h10Bound
def h37R : List Nat := varsOf 56
def h37G : Nat := 0xffffff00ff000000ffffff00ff000000
lemma h37Bound : Lower h37R h37G 4 := carry_of (swaps := [(3,4),(2,3)]) (roots2 := h3R) (T2 := h3G) (by decide +kernel) h3Bound
def h35R : List Nat := varsOf 60
def h35G : Nat := 0xf0f0fff0f000f0f0f0f0fff0f000f0f0
def h35Pos : List Nat := [4,40,4,4,40,36,12,52,40,28,12,4,28,52,60]
def h35Neg : List Nat := [0,32,8,20,56,32,8,20,8,20,0,16,24,48,56]
def h35Mask : Nat := fullMask 15
def h35Base : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x7eed,648),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x5752,0x5154),(0xffff0000ffff0000ffff0000ffff0000,0x7280,0x7a98),(0xffffffff00000000ffffffff00000000,0x61b2,0x6032)]
def h35Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(3,0,1),(0,0,2),(1,0,2),(2,1,2),(3,1,2),(0,1,3),(1,1,3),(2,3,4),(3,3,5)]
def h35W : BT Decor := buildWiresBT 4 h35Base h35Steps
def h35AutoList : List (List (Nat × Nat)) := [[],[(3,5)]]
def h35Autos : BT (List (Nat × Nat)) := btOfList 1 h35AutoList
lemma h35Pairs : goodPairs h35G h35Pos h35Neg := goodPairs_of (by decide +kernel)
lemma h35BaseOk : ∀ x ∈ h35Base, faithful h35Pos h35Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma h35WOk : btAll (fun x => faithful h35Pos h35Neg x ∧ x.1 < 2^128) h35W := buildWiresBT_faithful h35BaseOk
lemma h35AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h35G = h35G) h35Autos := btAll_ofList (autos_of (by decide +kernel))
def h35SliceList : List (Option (Nat × Nat)) := [some (0xf0f00f0ff0f00f0ff0f00f0ff0f00f0f,4),some (0xff00ff0000ff00ffff00ff0000ff00ff,4),some (0xffff0000ffff0000ffff0000ffff00,4),some (0xffffffff00000000ffffffff0000,4)]
def h35Slices : BT (Option (Nat × Nat)) := btOfList 2 h35SliceList
def h35Specs : List PoolSpec := [(0,[]),(2,[]),(1,[]),(3,[])]
def h35Pools : BT (Option BoundPool) := buildPoolsBT 2 h35W h35R h35Slices h35Specs
set_option maxRecDepth 200000 in
lemma h35Slice3 : Slice h35R h35G (0xffffffff00000000ffffffff0000) 4 := opposite_slice (oppositeRow 4 5 44) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h3Bound
set_option maxRecDepth 200000 in
lemma h35Slice2 : Slice h35R h35G (0xffff0000ffff0000ffff0000ffff00) 4 := opposite_slice (oppositeRow 3 4 52) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h36Bound
set_option maxRecDepth 200000 in
lemma h35Slice1 : Slice h35R h35G (0xff00ff0000ff00ffff00ff0000ff00ff) 4 := mapped_slice (identifyRow 3 5 52) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h36Bound
set_option maxRecDepth 200000 in
lemma h35Slice0 : Slice h35R h35G (0xf0f00f0ff0f00f0ff0f00f0ff0f00f0f) 4 := mapped_slice (identifyRow 2 4 56) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h37Bound
lemma h35SlicesOk : btAll (sliceSpec h35R h35G) h35Slices := btAll_ofList (P := sliceSpec h35R h35G) (sliceSpecCons h35Slice0 (sliceSpecCons h35Slice1 (sliceSpecCons h35Slice2 (sliceSpecCons h35Slice3 sliceSpecNil))))
set_option maxRecDepth 200000 in
lemma h35PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h35R h35G c) h35Pools := buildPoolsBT_sound h35SlicesOk
def h35Empty : BT (List (List Nat)) := BT.empty
lemma h35EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h35G (3 - 1) xs.toFinset) h35Empty := trivial
def h35Block3_0 : List NodeSpec := priorityNodes 2 [(3215,1,2),(3471,1,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Test3_0 : checkNodesBT h35W h35G h35Mask h35Pools h35Autos h35Empty 3 h35Block3_0 = true := by decide +kernel
def h35Nodes3 : List NodeSpec := h35Block3_0
lemma h35Check3 : checkNodesBT h35W h35G h35Mask h35Pools h35Autos h35Empty 3 h35Nodes3 = true := h35Test3_0
def h35Bucket3 : BT (List (List Nat)) := buildBucketsBT h35W h35Nodes3
set_option maxRecDepth 200000 in
lemma h35Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h35G 3 xs.toFinset) h35Bucket3 := buildBucketsBT_sound (by decide) h35Pairs h35WOk h35PoolsOk h35AutosOk h35EmptyOk h35Check3
def h35Block4_0 : List NodeSpec := priorityNodes 2 [(62,100,2),(94,100,2),(158,1,2),(286,1,2),(542,1,2),(1054,1,2),(2078,5,2),(4126,5,2),(8222,6,2),(5407,6,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Test4_0 : checkNodesBT h35W h35G h35Mask h35Pools h35Autos h35Bucket3 4 h35Block4_0 = true := by decide +kernel
def h35Nodes4 : List NodeSpec := h35Block4_0
lemma h35Check4 : checkNodesBT h35W h35G h35Mask h35Pools h35Autos h35Bucket3 4 h35Nodes4 = true := h35Test4_0
def h35Bucket4 : BT (List (List Nat)) := buildBucketsBT h35W h35Nodes4
set_option maxRecDepth 200000 in
lemma h35Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h35G 4 xs.toFinset) h35Bucket4 := buildBucketsBT_sound (by decide) h35Pairs h35WOk h35PoolsOk h35AutosOk h35Bucket3Ok h35Check4
def h35Block5_0 : List NodeSpec := priorityNodes 2 [(30,484,6)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Test5_0 : checkNodesBT h35W h35G h35Mask h35Pools h35Autos h35Bucket4 5 h35Block5_0 = true := by decide +kernel
def h35Nodes5 : List NodeSpec := h35Block5_0
lemma h35Check5 : checkNodesBT h35W h35G h35Mask h35Pools h35Autos h35Bucket4 5 h35Nodes5 = true := h35Test5_0
def h35Bucket5 : BT (List (List Nat)) := buildBucketsBT h35W h35Nodes5
set_option maxRecDepth 200000 in
lemma h35Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h35G 5 xs.toFinset) h35Bucket5 := buildBucketsBT_sound (by decide) h35Pairs h35WOk h35PoolsOk h35AutosOk h35Bucket4Ok h35Check5
set_option maxRecDepth 200000 in
lemma h35Bound : Lower h35R h35G 6 := lower_of_forestBT (essPairs := [(VAR 2,0,4),(VAR 3,20,28),(VAR 4,4,20),(VAR 5,8,40)]) (by decide +kernel) h35Bucket5Ok (by decide +kernel)
def h38R : List Nat := varsOf 29
def h38G : Nat := 0xfa00faaafa00faaafa00faaafa00faaa
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38Bound : Lower h38R h38G 4 := lower_from_single_layer (k := 3) (pos := [1,5,9,1,25,25,12,5]) (neg := [0,4,8,17,24,17,4,21]) (essentialPairs := [(VAR 0,0,1),(VAR 2,8,12),(VAR 3,4,12),(VAR 4,1,17)]) (by decide +kernel)
def h39R : List Nat := varsOf 45
def h39G : Nat := 0xfffafffafaaafaaafffafffafaaafaaa
lemma h39Bound : Lower h39R h39G 5 := lift_of (z := 1) (o := 0) (essPairs := [(VAR 0,0,1)]) (by decide +kernel) h3Bound
def h40R : List Nat := varsOf 49
def h40G : Nat := 0xaaaaffff0000aaaaaaaaffff0000aaaa
lemma h40Bound : Lower h40R h40G 4 := carry_of (swaps := [(3,4),(4,5),(0,1)]) (roots2 := h10R) (T2 := h10G) (by decide +kernel) h10Bound
def h41R : List Nat := varsOf 53
def h41G : Nat := 0xaaaafafa0000aaaaaaaafafa0000aaaa
lemma h41Bound : Lower h41R h41G 5 := lift_of (z := 0) (o := 4) (essPairs := [(VAR 2,32,36)]) (by decide +kernel) h40Bound
def h42R : List Nat := varsOf 57
def h42G : Nat := 0xaaaaffaaaa00aaaaaaaaffaaaa00aaaa
lemma h42Bound : Lower h42R h42G 6 := carry_of (swaps := [(1,2),(0,1)]) (roots2 := h35R) (T2 := h35G) (by decide +kernel) h35Bound
def h43R : List Nat := varsOf 28
def h43G : Nat := 0xf000fff0f000fff0f000fff0f000fff0
lemma h43Bound : Lower h43R h43G 4 := carry_of (swaps := [(4,5),(1,2)]) (roots2 := h10R) (T2 := h10G) (by decide +kernel) h10Bound
def h44R : List Nat := varsOf 60
def h44G : Nat := 0xf000fff0f000f000f000fff0f000f000
lemma h44Bound : Lower h44R h44G 5 := lift_of (z := 0) (o := 32) (essPairs := [(VAR 5,4,36)]) (by decide +kernel) h43Bound
def h45R : List Nat := varsOf 29
def h45G : Nat := 0xfaaafffafaaafffafaaafffafaaafffa
lemma h45Bound : Lower h45R h45G 5 := lift_of (z := 1) (o := 0) (essPairs := [(VAR 0,0,1)]) (by decide +kernel) h43Bound
def h46R : List Nat := varsOf 45
def h46G : Nat := 0xfaaafaaafa00fa00faaafaaafa00fa00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Bound : Lower h46R h46G 4 := lower_from_single_layer (k := 3) (pos := [9,37,9,12,12,37,33,44]) (neg := [8,36,1,4,8,5,1,36]) (essentialPairs := [(VAR 0,8,9),(VAR 2,8,12),(VAR 3,1,9),(VAR 5,1,33)]) (by decide +kernel)
def h47R : List Nat := varsOf 57
def h47G : Nat := 0xffaaffffff00ffaaffaaffffff00ffaa
lemma h47Bound : Lower h47R h47G 5 := carry_of (swaps := [(3,4),(4,5),(3,4),(0,1),(1,2),(2,3),(0,1)]) (roots2 := h45R) (T2 := h45G) (by decide +kernel) h45Bound
def h33R : List Nat := varsOf 61
def h33G : Nat := 0xfaaafffafa00faaafaaafffafa00faaa
def h33Pos : List Nat := [1,12,5,12,25,1,40,36,40,36,49,53,1,25,40,36,28,5,57,37,28,28,9,60,40,60,40,33,28,28,1,5,53,49,1,5,9,9,49,28,28,29,57,25,12,36,25,49,5,25,29,1,33,40,36,40]
def h33Neg : List Nat := [0,8,4,4,17,17,56,4,8,32,17,52,8,24,32,52,20,20,56,4,21,24,17,52,48,56,0,32,8,56,4,21,21,32,32,0,8,0,48,4,52,21,17,21,0,0,56,21,17,8,17,21,17,16,20,24]
def h33Mask : Nat := fullMask 56
def h33Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x1fce7fc84e3c35,0x1d8e0180500430),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x453389b2bb8a8e,0x488b81c09b888c),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xa65fb037f5615a,0x82401032243142),(0xffff0000ffff0000ffff0000ffff0000,0x6cfc332b52c10,0xfdcf41a3f7ac70),(0xffffffff00000000ffffffff00000000,0xf0a4430f8ccfc0,0x41462b84ca40)]
def h33Steps : List (Nat × Nat × Nat) := [(1,0,1),(0,0,2),(1,0,2),(0,2,3),(1,2,3),(2,2,3),(3,2,3),(0,2,4),(1,2,4),(2,2,4),(3,2,4),(3,2,7),(0,3,4),(1,3,4),(2,3,4),(3,3,4),(1,2,20),(3,3,5),(1,3,7),(3,3,7),(3,3,21),(0,4,5),(0,4,7),(2,4,7),(0,4,21),(0,5,7),(0,5,21),(1,7,21),(2,2,20),(3,2,20),(0,5,20),(2,5,20),(3,2,32),(0,5,32),(2,7,20),(1,2,24),(1,2,27),(3,0,2),(0,0,3),(1,0,3),(2,0,3),(3,0,3),(0,0,4),(1,0,4),(2,0,4),(3,0,4),(3,0,5),(3,0,9),(1,0,20),(0,4,9),(3,4,9),(0,4,53),(3,0,20),(2,9,20),(1,0,54),(1,2,54),(1,3,54),(1,0,34),(1,3,34),(1,0,15),(2,3,15),(3,3,53),(1,15,20),(3,0,63),(3,2,63),(0,4,63),(2,4,22),(1,3,26),(3,0,21),(1,2,31),(2,0,1),(0,1,2),(1,1,2),(2,1,2),(3,1,2),(0,1,3),(1,1,3),(3,1,3),(1,1,4),(3,1,4),(1,1,20),(1,1,22),(1,1,26),(2,7,51),(1,3,42),(2,4,42),(1,42,51),(1,9,51),(2,9,51),(1,20,51),(2,20,51),(0,4,92),(1,0,10),(1,0,70),(1,10,51),(1,0,12),(3,0,61),(1,12,51),(2,4,102),(1,15,51),(1,3,103),(2,21,51),(1,1,6),(1,3,6),(2,3,6),(1,4,6),(2,4,6),(1,2,52),(0,7,9),(3,2,64),(2,7,15),(0,1,21),(3,1,21),(1,1,16),(1,20,42),(0,2,89),(2,2,90),(1,1,43),(3,3,77),(1,0,123),(0,4,77),(3,43,77),(1,3,79),(2,4,79),(1,43,79),(1,0,84),(1,3,84),(1,2,57),(0,1,40),(1,1,40),(2,1,40),(3,1,40),(1,4,45),(2,4,45),(3,45,77),(1,45,79),(2,4,133),(1,3,76),(2,4,76),(1,4,46),(1,1,56),(2,1,56),(1,2,56),(2,2,56),(2,3,56),(3,46,77),(3,0,127),(1,46,79),(3,0,131),(1,46,84),(0,1,147),(3,1,147),(2,9,46),(1,12,46),(1,15,46),(1,56,76),(3,3,145),(0,1,41),(1,1,41),(2,1,41),(3,1,41),(1,3,47),(3,47,77),(1,47,79),(1,3,162),(1,76,149),(0,3,48),(1,1,66),(2,1,66),(1,2,66),(2,2,66),(0,48,77),(1,0,176),(1,0,128),(2,48,79),(3,0,81),(0,4,81),(1,0,181),(0,48,81),(0,9,48),(3,10,48),(0,1,174),(3,1,174),(3,15,48),(1,66,76),(0,4,172),(1,1,49),(3,49,77),(1,49,79),(3,17,77),(0,18,77),(1,2,19),(3,19,77),(3,20,77),(1,17,79),(2,18,79),(1,19,79),(1,20,79),(1,4,8),(3,1,13),(2,13,20),(2,9,17),(1,1,11),(2,1,11),(1,11,20),(2,3,14),(3,15,18)]
def h33W : BT Decor := buildWiresBT 8 h33Base h33Steps
def h33AutoList : List (List (Nat × Nat)) := [[]]
def h33Autos : BT (List (Nat × Nat)) := btOfList 1 h33AutoList
lemma h33Pairs : goodPairs h33G h33Pos h33Neg := goodPairs_of (by decide +kernel)
lemma h33BaseOk : ∀ x ∈ h33Base, faithful h33Pos h33Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma h33WOk : btAll (fun x => faithful h33Pos h33Neg x ∧ x.1 < 2^128) h33W := buildWiresBT_faithful h33BaseOk
lemma h33AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h33G = h33G) h33Autos := btAll_ofList (autos_of (by decide +kernel))
def h33SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 4,5),some (subcubeFast 0 16,4),some (subcubeFast 0 32,5),some (subcubeFast 1 0,5),some (subcubeFast 1 32,4),some (subcubeFast 4 0,6),some (subcubeFast 8 0,5),some (subcubeFast 8 4,4),some (subcubeFast 16 0,5),some (subcubeFast 17 0,4),some (subcubeFast 32 0,4),some (0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5,6),some (0xff00ff0000ff00ffff00ff0000ff00ff,5),some (0xffffffff00000000ffffffff0000,5)]
def h33Slices : BT (Option (Nat × Nat)) := btOfList 4 h33SliceList
def h33Specs : List PoolSpec := poolSteps h33Steps [(5,[]),(3,[]),(9,[]),(6,[0]),(7,[]),(4,[]),(5,[2]),(8,[0]),(2,[0]),(0,[]),(5,[4]),(2,[0,48]),(0,[4]),(5,[10]),(8,[0,48]),(0,[10]),(3,[15]),(5,[15]),(11,[]),(6,[]),(8,[]),(1,[]),(10,[]),(2,[]),(12,[]),(5,[37]),(5,[5]),(5,[7]),(8,[2]),(2,[2]),(8,[37]),(2,[37]),(5,[38]),(5,[39]),(2,[39]),(5,[40]),(8,[132]),(5,[40,132]),(5,[40,133]),(8,[133]),(5,[41]),(2,[41]),(2,[48]),(5,[41,139]),(5,[42]),(5,[42,161]),(2,[161]),(5,[43]),(8,[43]),(8,[48]),(5,[43,166]),(5,[44]),(5,[45]),(8,[45]),(5,[118]),(5,[120]),(5,[122]),(5,[123]),(5,[176]),(5,[126]),(8,[47]),(5,[4,49]),(5,[6]),(5,[8]),(0,[6]),(0,[8]),(2,[59]),(5,[12]),(5,[13]),(5,[14]),(13,[]),(5,[14,15])]
def h33Pools : BT (Option BoundPool) := buildPoolsBT 7 h33W h33R h33Slices h33Specs
set_option maxRecDepth 200000 in
lemma h33Slice13 : Slice h33R h33G (0xffffffff00000000ffffffff0000) 5 := opposite_slice (oppositeRow 4 5 45) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h17Bound
set_option maxRecDepth 200000 in
lemma h33Slice12 : Slice h33R h33G (0xff00ff0000ff00ffff00ff0000ff00ff) 5 := mapped_slice (identifyRow 3 5 53) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h34Bound
set_option maxRecDepth 200000 in
lemma h33Slice11 : Slice h33R h33G (0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5) 6 := mapped_slice (identifyRow 0 2 60) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h35Bound
set_option maxRecDepth 200000 in
lemma h33Slice10 : Slice h33R h33G (subcubeFast 32 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h38Bound
set_option maxRecDepth 200000 in
lemma h33Slice9 : Slice h33R h33G (subcubeFast 17 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h3Bound
set_option maxRecDepth 200000 in
lemma h33Slice8 : Slice h33R h33G (subcubeFast 16 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h39Bound
set_option maxRecDepth 200000 in
lemma h33Slice7 : Slice h33R h33G (subcubeFast 8 4) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h40Bound
set_option maxRecDepth 200000 in
lemma h33Slice6 : Slice h33R h33G (subcubeFast 8 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h41Bound
set_option maxRecDepth 200000 in
lemma h33Slice5 : Slice h33R h33G (subcubeFast 4 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h42Bound
set_option maxRecDepth 200000 in
lemma h33Slice4 : Slice h33R h33G (subcubeFast 1 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h43Bound
set_option maxRecDepth 200000 in
lemma h33Slice3 : Slice h33R h33G (subcubeFast 1 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h44Bound
set_option maxRecDepth 200000 in
lemma h33Slice2 : Slice h33R h33G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h45Bound
set_option maxRecDepth 200000 in
lemma h33Slice1 : Slice h33R h33G (subcubeFast 0 16) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h46Bound
set_option maxRecDepth 200000 in
lemma h33Slice0 : Slice h33R h33G (subcubeFast 0 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h47Bound
lemma h33SlicesOk : btAll (sliceSpec h33R h33G) h33Slices := btAll_ofList (P := sliceSpec h33R h33G) (sliceSpecCons h33Slice0 (sliceSpecCons h33Slice1 (sliceSpecCons h33Slice2 (sliceSpecCons h33Slice3 (sliceSpecCons h33Slice4 (sliceSpecCons h33Slice5 (sliceSpecCons h33Slice6 (sliceSpecCons h33Slice7 (sliceSpecCons h33Slice8 (sliceSpecCons h33Slice9 (sliceSpecCons h33Slice10 (sliceSpecCons h33Slice11 (sliceSpecCons h33Slice12 (sliceSpecCons h33Slice13 sliceSpecNil))))))))))))))
set_option maxRecDepth 200000 in
lemma h33PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h33R h33G c) h33Pools := buildPoolsBT_sound h33SlicesOk
def h33Empty : BT (List (List Nat)) := BT.empty
lemma h33EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h33G (3 - 1) xs.toFinset) h33Empty := trivial
def h33Block3_0 : List NodeSpec := priorityNodes 7 [(38804509,1,2),(239095853,1,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Test3_0 : checkNodesBT h33W h33G h33Mask h33Pools h33Autos h33Empty 3 h33Block3_0 = true := by decide +kernel
def h33Nodes3 : List NodeSpec := h33Block3_0
lemma h33Check3 : checkNodesBT h33W h33G h33Mask h33Pools h33Autos h33Empty 3 h33Nodes3 = true := h33Test3_0
def h33Bucket3 : BT (List (List Nat)) := buildBucketsBT h33W h33Nodes3
set_option maxRecDepth 200000 in
lemma h33Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h33G 3 xs.toFinset) h33Bucket3 := buildBucketsBT_sound (by decide) h33Pairs h33WOk h33PoolsOk h33AutosOk h33EmptyOk h33Check3
def h33Block4_0 : List NodeSpec := priorityNodes 7 [(475849,1,2),(112765,128,2),(282749,1,2),(23332013,139,2),(471165,1,2),(80750685,142,2),(266365,1,2),(132133037,139,2),(115388509,142,2),(112747,128,2),(1138811,1,2),(381749291,1,2),(1828970571,1,2),(1679467,1,2),(22106277,1,2),(1702909975,1,2),(1736464407,1,2),(299915791,1,2),(24562860103,1,2),(24831295559,1,2),(1384206501,1,2),(27810869,1,2),(362830351,1,2),(1290271,1,2),(1669421099,1,2),(1686198315,1,2),(24203429,1,2),(4311767095,1,2),(1702910007,1,2),(2004963413,1,2),(5455919,1,2),(524289039,1,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Test4_0 : checkNodesBT h33W h33G h33Mask h33Pools h33Autos h33Bucket3 4 h33Block4_0 = true := by decide +kernel
def h33Block4_1 : List NodeSpec := priorityNodes 7 [(29126525767,1,2),(29394961223,1,2),(1417760933,1,2),(306270293,1,2),(1300235279,1,2),(6078511,1,2),(8087117899,1,2),(8154226763,1,2),(376439567,1,2),(380634383,1,2),(19529130059,1,2),(128012453,1,2),(331436197,1,2),(368055175,1,2),(21944959879,1,2),(408962571,1,2),(18353213,1,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Test4_1 : checkNodesBT h33W h33G h33Mask h33Pools h33Autos h33Bucket3 4 h33Block4_1 = true := by decide +kernel
def h33Nodes4 : List NodeSpec := h33Block4_0 ++ h33Block4_1
lemma h33Check4 : checkNodesBT h33W h33G h33Mask h33Pools h33Autos h33Bucket3 4 h33Nodes4 = true := by
  unfold h33Nodes4 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h33Test4_0,h33Test4_1⟩
def h33Bucket4 : BT (List (List Nat)) := buildBucketsBT h33W h33Nodes4
set_option maxRecDepth 200000 in
lemma h33Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h33G 4 xs.toFinset) h33Bucket4 := buildBucketsBT_sound (by decide) h33Pairs h33WOk h33PoolsOk h33AutosOk h33Bucket3Ok h33Check4
def h33Block5_0 : List NodeSpec := priorityNodes 7 [(221565,2179458,2),(541053,130,2),(573821,130,2),(672125,133,2),(704893,133,2),(2098282,136,2),(811243,1,2),(241899,129,2),(2162778,135,2),(958699,1,2),(397437,2097794,2),(35142781,17794,2),(135403,17537,2),(717131,17544,2),(3469483,17543,2),(250091,2146432,2),(258283,16512,2),(2179307,1,2),(2212075,1,2),(794869,16640,2),(133183,146,2),(629272683,134,2),(679604331,153,2),(1057426507,133,2),(3797099,1,2),(36759659,1,2),(696381547,133,2),(713158763,1,2),(163704939,1,2),(813822059,154,2),(44167275,1,2),(864153707,155,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Test5_0 : checkNodesBT h33W h33G h33Mask h33Pools h33Autos h33Bucket4 5 h33Block5_0 = true := by decide +kernel
def h33Block5_1 : List NodeSpec := priorityNodes 7 [(264344107,130,2),(52555883,1,2),(897708139,1,2),(880930923,130,2),(63969387,128,2),(729935979,145,2),(746713195,1,2),(2982773,128,2),(3769205,128,2),(3048309,2409090,2),(238423,19477,2),(58431,316998784,2),(145471,1,2),(45094999,1,2),(946239,17536,2),(2701193263,137,2),(1003583,128,2),(1028159,128,2),(2105407,17536,2),(629182551,19989,2),(1015064607,21013,2),(1031841823,1,2),(2220095,129,2),(662736983,1,2),(981518367,1,2),(998295583,1,2),(2236479,129,2),(3137376343,2558597,2),(3170930775,19989,2),(3204485207,1,2),(3238039639,1,2),(612405335,2558597,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Test5_1 : checkNodesBT h33W h33G h33Mask h33Pools h33Autos h33Bucket4 5 h33Block5_1 = true := by decide +kernel
def h33Block5_2 : List NodeSpec := priorityNodes 7 [(645959767,146,2),(2264967199,1,2),(45132831,1,2),(2400319,1,2),(2734772271,1,2),(2197866527,1,2),(49327135,148,2),(2433087,1,2),(2868989999,150,2),(2465855,148,2),(1556943,17026,2),(12453423,133,2),(155715119,1,2),(914444405,147,2),(65097775,150,2),(2531391,148,2),(146886703,150,2),(2547775,148,2),(2449612887,148,2),(2315427927,137,2),(43035679,2460176,2),(47229983,1,2),(750824479,1,2),(759213087,1,2),(767601695,2788116,2),(775990303,18949,2),(2351167,2244632,2),(612413527,20120,2),(12012642351,1,2),(9730940975,21782,2),(2678847,129,2),(645967959,1,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Test5_2 : checkNodesBT h33W h33G h33Mask h33Pools h33Autos h33Bucket4 5 h33Block5_2 = true := by decide +kernel
def h33Block5_3 : List NodeSpec := priorityNodes 7 [(11744239663,1,2),(9462538287,1,2),(2695231,129,2),(4076908631,2575106,2),(4110463063,20120,2),(4144017495,1,2),(4177571927,1,2),(595636311,2575106,2),(629190743,146,2),(9865142319,356878849,2),(9596739631,1,2),(12683730991,1,2),(48484399,1,2),(2826303,1,2),(12415328303,1,2),(56873007,151,2),(675310623,1,2),(2875455,1,2),(2239786015,149,2),(2940991,148,2),(3435551,149,2),(2957375,148,2),(830574709,147,2),(47213599,149,2),(2973759,148,2),(6751631,16645,2),(13502751,130,2),(181930271,1,2),(2583830615,151,2),(2449645655,137,2),(44290095,2476688,2),(52678703,1,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Test5_3 : checkNodesBT h33W h33G h33Mask h33Pools h33Autos h33Bucket4 5 h33Block5_3 = true := by decide +kernel
def h33Block5_4 : List NodeSpec := priorityNodes 7 [(3573796911,1,2),(3607351343,1,2),(3640905775,2902933,2),(3674460207,19330,2),(2793535,2244629,2),(641758239,137,2),(3088447,128,2),(3104831,128,2),(3121215,1,2),(3137599,1,2),(60302095,149,2),(219167791,149,2),(223347231,149,2),(3170367,1,2),(236984407,128,2),(3186751,1,2),(987199,2476809,2),(2842687,2443785,2),(231746607,1,2),(3203135,1,2),(57937695,1,2),(3219519,1,2),(62399247,148,2),(3235903,1,2),(245373015,128,2),(3252287,137,2),(2416703,1,2),(2859071,1,2),(2924607,148,2),(2449471,148,2),(985551,18963,2),(10880287,189,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Test5_4 : checkNodesBT h33W h33G h33Mask h33Pools h33Autos h33Bucket4 5 h33Block5_4 = true := by decide +kernel
def h33Block5_5 : List NodeSpec := priorityNodes 7 [(731599,18963,2),(207095343,148,2),(11666991,21780,2),(227391,148,2),(239679,1,2),(35903,17536,2),(774207,148,2),(987535,18963,2),(953903,1,2),(2163999,1,2),(2166798,148,2),(13766191,1,2),(3179284527,148,2),(798783,148,2),(778044959,148,2),(206047519,151,2),(10094879,22679,2),(528447,148,2),(147025967,1,2),(138612823,19220,2),(155390039,137,2),(62939223,19349,2),(159408215,137,2),(370148623,25346,2),(137372431,199,2),(58127,418482836,2),(3547919,25364,2),(137279,1,2),(569407,17536,2),(801118315,137,2),(809506923,128,2),(817891435,1,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Test5_5 : checkNodesBT h33W h33G h33Mask h33Pools h33Autos h33Bucket4 5 h33Block5_5 = true := by decide +kernel
def h33Nodes5 : List NodeSpec := h33Block5_0 ++ h33Block5_1 ++ h33Block5_2 ++ h33Block5_3 ++ h33Block5_4 ++ h33Block5_5
lemma h33Check5 : checkNodesBT h33W h33G h33Mask h33Pools h33Autos h33Bucket4 5 h33Nodes5 = true := by
  unfold h33Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨h33Test5_0,h33Test5_1⟩,h33Test5_2⟩,h33Test5_3⟩,h33Test5_4⟩,h33Test5_5⟩
def h33Bucket5 : BT (List (List Nat)) := buildBucketsBT h33W h33Nodes5
set_option maxRecDepth 200000 in
lemma h33Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h33G 5 xs.toFinset) h33Bucket5 := buildBucketsBT_sound (by decide) h33Pairs h33WOk h33PoolsOk h33AutosOk h33Bucket4Ok h33Check5
def h33Block6_0 : List NodeSpec := priorityNodes 7 [(376,2179332,2),(378,2179586,2),(23677,16898,2),(1146,2228484,2),(65658,2212484,2),(63723,38942065282,2),(143595,2228484,2),(176363,2212484,2),(31871,5194270392585,2),(37951,40580235778,2),(46143,40039186949,2),(122,16644,2),(2917227,276906754,2),(39899243,320946436,2),(11142763,278988034,2),(10881643,279347460,2),(41419883,273072772,2),(38280299,276858501,2),(66062443,276908162,2),(1695851,2247042,2),(1712175,2409090,2),(1728559,2427269,2),(440351,2476418,2),(444447,2409090,2),(1342,41884666369,2),(65854,42153151361,2),(111039,40305248898,2),(39999,5194244948245,2),(270783,19074,2),(42047,5194244950658,2),(287167,19074,2),(48191,5124988603141,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Test6_0 : checkNodesBT h33W h33G h33Mask h33Pools h33Autos h33Bucket5 6 h33Block6_0 = true := by decide +kernel
def h33Block6_1 : List NodeSpec := priorityNodes 7 [(336319,19461,2),(50239,5124988600982,2),(352703,19461,2),(1876075,2245250,2),(318,5159659176068,2),(23594047,40309442946,2),(700479,5194244950658,2),(708671,5124988603141,2),(289437759,2099721,2),(306214975,2113545,2),(1941611,2425989,2),(897087,287312389,2),(281053247,19074,2),(297830463,287312514,2),(339773503,19074,2),(9307695,2656898,2),(17039935,19074,2),(7736895,314657410,2),(219199,660362238102146,2),(272668735,39768296073,2),(289445951,308297737,2),(1351787,312591493,2),(299095,16645,2),(149567,287310085,2),(1908823,331696517,2),(1101855,44367694721,2),(1110047,348768901,2),(132163647,18953,2),(281061439,2099721,2),(323004479,2476820,2),(9831983,308483202,2),(18088511,316689172,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Test6_1 : checkNodesBT h33W h33G h33Mask h33Pools h33Autos h33Bucket5 6 h33Block6_1 = true := by decide +kernel
def h33Block6_2 : List NodeSpec := priorityNodes 7 [(8261183,2458260,2),(888895,40580038658,2),(1159199,2804610,2),(109599,2181890,2),(215103,5053301656325,2),(127973439,40573602569,2),(272676927,308297737,2),(1368171,314705026,2),(307287,2575106,2),(153663,36776135426,2),(1925207,333810050,2),(5324847,363563778,2),(4767791,356878849,2),(123783231,19337,2),(132171839,2100105,2),(281069631,2427797,2),(5178175,2474261,2),(5047615,310397845,2),(8784159,308533253,2),(905279,40038973445,2),(5488687,2919298,2),(512047,2132613,2),(256063,5193439644290,2),(119593023,2100105,2),(127981631,2113545,2),(6144107,2475138,2),(913471,287312770,2),(115402815,19205,2),(123791423,287312645,2),(132180031,19205,2),(5440319,312511237,2),(5309759,19205,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Test6_2 : checkNodesBT h33W h33G h33Mask h33Pools h33Autos h33Bucket5 6 h33Block6_2 = true := by decide +kernel
def h33Block6_3 : List NodeSpec := priorityNodes 7 [(9308447,2968325,2),(716863,5194270444676,2),(31725119,2475158,2),(31201855,2426005,2),(30678591,2475156,2),(120587327,312786953,2),(979007,6259692554884,2),(995391,6293511228164,2),(692287,664866616820870,2),(32773695,2099721,2),(32250431,2100105,2),(31727167,2424841,2),(124781631,664866345978505,2),(1011775,664863355755541,2),(1019967,655998543256726,2),(2891839,317030914,2),(2908223,6396282489604,2),(3055679,16898,2),(2580543,17028,2),(1036351,312803972,2),(1044543,6430642244228,2),(1642527,2476418,2),(264223,16898,2),(260159,16898,2),(198719,5125821317122,2),(5702463,394592405,2),(17470,40554793620,2),(66622,319146644,2),(263214,40036928386,2),(755247,39485554965,2),(206911,655618564491670,2),(5964607,2476565,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Test6_3 : checkNodesBT h33W h33G h33Mask h33Pools h33Autos h33Bucket5 6 h33Block6_3 = true := by decide +kernel
def h33Block6_4 : List NodeSpec := priorityNodes 7 [(62527,40284209173,2),(6095679,2460181,2),(766015,317030914,2),(1086,40580057730,2),(544831,39730891524,2),(6668395,16898,2),(20542,51401574916,2),(69694,37858184084,2),(626223,40578845058,2),(52287,39478889218,2),(790591,312803972,2),(235583,39730907780,2),(65598,40039041797,2),(6570091,16901,2),(247071,40308328837,2),(44095,39478889093,2),(446511,17028,2),(223295,17028,2),(6766639,2476418,2),(247871,5159639990277,2),(25955903,407224470,2),(59679,40305412613,2),(182559,39491797654,2),(243775,660016483125653,2),(25431615,2476566,2),(26480191,2476694,2),(231487,39478889218,2),(33855,5194266200706,2),(536639,39478889093,2),(3153983,287312770,2),(25359,416402050,2),(202815,5124720165506,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Test6_4 : checkNodesBT h33W h33G h33Mask h33Pools h33Autos h33Bucket5 6 h33Block6_4 = true := by decide +kernel
def h33Block6_5 : List NodeSpec := priorityNodes 7 [(70255679,2787970,2),(274727999,17553,2),(35903,4434822531477,2),(99391,5194266200597,2),(7078975,317032981,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Test6_5 : checkNodesBT h33W h33G h33Mask h33Pools h33Autos h33Bucket5 6 h33Block6_5 = true := by decide +kernel
def h33Nodes6 : List NodeSpec := h33Block6_0 ++ h33Block6_1 ++ h33Block6_2 ++ h33Block6_3 ++ h33Block6_4 ++ h33Block6_5
lemma h33Check6 : checkNodesBT h33W h33G h33Mask h33Pools h33Autos h33Bucket5 6 h33Nodes6 = true := by
  unfold h33Nodes6 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨h33Test6_0,h33Test6_1⟩,h33Test6_2⟩,h33Test6_3⟩,h33Test6_4⟩,h33Test6_5⟩
def h33Bucket6 : BT (List (List Nat)) := buildBucketsBT h33W h33Nodes6
set_option maxRecDepth 200000 in
lemma h33Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h33G 6 xs.toFinset) h33Bucket6 := buildBucketsBT_sound (by decide) h33Pairs h33WOk h33PoolsOk h33AutosOk h33Bucket5Ok h33Check6
def h33Block7_0 : List NodeSpec := priorityNodes 7 [(122,268517890,2),(126,278921476,2),(585791,2179332,2),(389227,2179328,2),(190,36775969410,2),(318,281100802,2),(12863,268517890,2),(157759,2179332,2),(161855,5053297986053,2),(165951,39479427714,2),(170047,5053298032901,2),(174143,39479542402,2),(178239,5053298180738,2),(182335,39479656709,2),(186431,5053298297730,2),(190527,39479738629,2),(602175,40575713284,2),(618559,5193691302281,2),(634943,40577794308,2),(643135,2474498,2),(651327,2425476,2),(659519,39774585476,2),(574,2474498,2),(1086,40577958148,2),(2110,317014276,2),(4158,40534770178,2),(8254,310739588,2),(9791,39729480197,2),(32830,2425349,2),(65598,39774798468,2),(13887,5053438331778,2),(14911,5053440409861,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Test7_0 : checkNodesBT h33W h33G h33Mask h33Pools h33Autos h33Bucket6 7 h33Block7_0 = true := by decide +kernel
def h33Block7_1 : List NodeSpec := priorityNodes 7 [(15935,39480019842,2),(33855,646828024676994,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Test7_1 : checkNodesBT h33W h33G h33Mask h33Pools h33Autos h33Bucket6 7 h33Block7_1 = true := by decide +kernel
def h33Nodes7 : List NodeSpec := h33Block7_0 ++ h33Block7_1
lemma h33Check7 : checkNodesBT h33W h33G h33Mask h33Pools h33Autos h33Bucket6 7 h33Nodes7 = true := by
  unfold h33Nodes7 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h33Test7_0,h33Test7_1⟩
def h33Bucket7 : BT (List (List Nat)) := buildBucketsBT h33W h33Nodes7
set_option maxRecDepth 200000 in
lemma h33Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h33G 7 xs.toFinset) h33Bucket7 := buildBucketsBT_sound (by decide) h33Pairs h33WOk h33PoolsOk h33AutosOk h33Bucket6Ok h33Check7
def h33Block8_0 : List NodeSpec := priorityNodes 7 [(62,128,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Test8_0 : checkNodesBT h33W h33G h33Mask h33Pools h33Autos h33Bucket7 8 h33Block8_0 = true := by decide +kernel
def h33Nodes8 : List NodeSpec := h33Block8_0
lemma h33Check8 : checkNodesBT h33W h33G h33Mask h33Pools h33Autos h33Bucket7 8 h33Nodes8 = true := h33Test8_0
def h33Bucket8 : BT (List (List Nat)) := buildBucketsBT h33W h33Nodes8
set_option maxRecDepth 200000 in
lemma h33Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h33G 8 xs.toFinset) h33Bucket8 := buildBucketsBT_sound (by decide) h33Pairs h33WOk h33PoolsOk h33AutosOk h33Bucket7Ok h33Check8
set_option maxRecDepth 200000 in
lemma h33Bound : Lower h33R h33G 9 := lower_of_forestBT (essPairs := [(VAR 0,0,1),(VAR 2,8,12),(VAR 3,4,12),(VAR 4,1,17),(VAR 5,4,36)]) (by decide +kernel) h33Bucket8Ok (by decide +kernel)
namespace Cofactor12068
def R_0 : List Nat := varsOf 22
def G_0 : Nat := 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0
lemma low_0 : Lower R_0 G_0 4 := carry_of (swaps := [(4,5),(1,2),(2,3)]) (roots2 := h3R) (T2 := h3G) (by decide +kernel) h3Bound

def G_1 : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def R_1 : List Nat := varsOf 7
lemma low_1_ok : carryOK [(0,3),(0,4),(0,2),(0,1)] R_1 G_1 R_0 G_0 = true := by decide +kernel
lemma low_1 : Lower R_1 G_1 4 := carry_of low_1_ok low_0

def G_2 : Nat := 0xeeee8888eeee8888eeee8888eeee8888
def R_2 : List Nat := varsOf 19
lemma low_2_ok : carryOK [(0,2),(0,1)] R_2 G_2 R_0 G_0 = true := by decide +kernel
lemma low_2 : Lower R_2 G_2 4 := carry_of low_2_ok low_0

def G_3 : Nat := 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0
def R_3 : List Nat := varsOf 21
lemma low_3_ok : carryOK [(0,1)] R_3 G_3 R_0 G_0 = true := by decide +kernel
lemma low_3 : Lower R_3 G_3 4 := carry_of low_3_ok low_0

def G_7 : Nat := 0xfefee8e8fefee8e8fefee8e8fefee8e8
def R_7 : List Nat := varsOf 23
def pos_7 : List Nat := [3,3,5,5,6,6,17,17,18,18,20,20,3,3,5,5,6,6,17,17,18,18,20,20]
def neg_7 : List Nat := [2,1,4,1,4,2,16,1,16,2,16,4,4,16,2,16,1,16,2,4,1,4,1,2]
def fmask_7 : Nat := fullMask 24
def base_7 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcf0cf,0x51008a),(0xcccccccccccccccccccccccccccccccc,0x333333,0x844221),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xc3cc3c,0x281814),(0xffff0000ffff0000ffff0000ffff0000,0xfc0fc0,0x2a540)]
def steps_7 : List (Nat × Nat × Nat) := [(1,0,1),(2,4,2),(1,4,2),(1,0,2),(2,6,3),(1,1,2)]
def W_7 : Array Decor := buildWires base_7 steps_7
def autos_7 : Array (List (Nat × Nat)) := #[[],[(2,4)],[(0,1)],[(2,4),(0,1)],[(1,2)],[(1,4),(1,2)],[(0,1),(0,2)],[(1,4),(0,1),(0,2)],[(1,4),(0,2)]]
def slicesL_7 : List (Nat × Nat) := [(subcube 2 0,4),(subcube 1 0,4),(subcube 16 0,4),(subcube 4 0,4)]
def slices_7 : Array (Nat × Nat) := slicesL_7.toArray
def ps_7 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[])]
def P_7 : Array (Option BoundPool) := buildPools W_7 R_7 slices_7 ps_7
lemma gp_7 : goodPairs G_7 pos_7 neg_7 := goodPairs_of (by decide +kernel)
lemma base_7_ok : ∀ x ∈ base_7, faithful pos_7 neg_7 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma W_7_ok : ∀ x ∈ W_7.toList, faithful pos_7 neg_7 x ∧ x.1 < 2^128 := buildWires_faithful base_7_ok
lemma autos_7_ok : ∀ sw ∈ autos_7.toList, swapsValid sw = true ∧ permWord sw G_7 = G_7 := autos_of (by decide +kernel)
lemma sl_7_0_ok : sliceDirectCheck 2 0 0 R_7 G_7 R_3 G_3 = true := by decide +kernel
lemma sl_7_0 : Slice R_7 G_7 (subcube 2 0) 4 := slice_direct sl_7_0_ok low_3
lemma sl_7_1_ok : sliceDirectCheck 1 0 0 R_7 G_7 R_0 G_0 = true := by decide +kernel
lemma sl_7_1 : Slice R_7 G_7 (subcube 1 0) 4 := slice_direct sl_7_1_ok low_0
lemma sl_7_2_ok : sliceDirectCheck 16 0 0 R_7 G_7 R_1 G_1 = true := by decide +kernel
lemma sl_7_2 : Slice R_7 G_7 (subcube 16 0) 4 := slice_direct sl_7_2_ok low_1
lemma sl_7_3_ok : sliceDirectCheck 4 0 0 R_7 G_7 R_2 G_2 = true := by decide +kernel
lemma sl_7_3 : Slice R_7 G_7 (subcube 4 0) 4 := slice_direct sl_7_3_ok low_2
set_option maxRecDepth 200000 in
lemma slices_7_ok : ∀ i (hi : i < slices_7.size), Slice R_7 G_7 slices_7[i].1 slices_7[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice R_7 G_7 p.1 p.2) (forall_cons sl_7_0 (forall_cons sl_7_1 (forall_cons sl_7_2 (forall_cons sl_7_3 (fun _ h => (List.not_mem_nil h).elim)))))
lemma P_7_ok : ∀ i (hi : i < P_7.size), ∀ c, P_7[i] = some c → ValidPool R_7 G_7 c := buildPools_sound slices_7_ok
def bk_7_init : Array (List (List Nat)) := #[]
lemma bk_7_init_ok : ∀ i (hi : i < bk_7_init.size), ∀ xs ∈ bk_7_init[i], Impossible G_7 (0 - 1) xs.toFinset := by intro i hi; simp [bk_7_init] at hi
def nodes_7_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_7_0 : checkNodes W_7 G_7 fmask_7 P_7 autos_7 bk_7_init 0 nodes_7_0 = true := by decide +kernel
def bk_7_0 : Array (List (List Nat)) := buildBuckets 1 W_7 nodes_7_0
lemma bk_7_0_ok : ∀ i (hi : i < bk_7_0.size), ∀ xs ∈ bk_7_0[i], Impossible G_7 0 xs.toFinset :=
  buildBuckets_sound (by decide) gp_7 W_7_ok P_7_ok autos_7_ok bk_7_init_ok chk_7_0
def nodes_7_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_7_1 : checkNodes W_7 G_7 fmask_7 P_7 autos_7 bk_7_0 1 nodes_7_1 = true := by decide +kernel
def bk_7_1 : Array (List (List Nat)) := buildBuckets 1 W_7 nodes_7_1
lemma bk_7_1_ok : ∀ i (hi : i < bk_7_1.size), ∀ xs ∈ bk_7_1[i], Impossible G_7 1 xs.toFinset :=
  buildBuckets_sound (by decide) gp_7 W_7_ok P_7_ok autos_7_ok bk_7_0_ok chk_7_1
def nodes_7_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_7_2 : checkNodes W_7 G_7 fmask_7 P_7 autos_7 bk_7_1 2 nodes_7_2 = true := by decide +kernel
def bk_7_2 : Array (List (List Nat)) := buildBuckets 1 W_7 nodes_7_2
lemma bk_7_2_ok : ∀ i (hi : i < bk_7_2.size), ∀ xs ∈ bk_7_2[i], Impossible G_7 2 xs.toFinset :=
  buildBuckets_sound (by decide) gp_7 W_7_ok P_7_ok autos_7_ok bk_7_1_ok chk_7_2
def nodes_7_3 : List NodeSpec := [([8,0,1,2],[],[]),([4,7,9,3],[0,1],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_7_3 : checkNodes W_7 G_7 fmask_7 P_7 autos_7 bk_7_2 3 nodes_7_3 = true := by decide +kernel
def bk_7_3 : Array (List (List Nat)) := buildBuckets 1 W_7 nodes_7_3
lemma bk_7_3_ok : ∀ i (hi : i < bk_7_3.size), ∀ xs ∈ bk_7_3[i], Impossible G_7 3 xs.toFinset :=
  buildBuckets_sound (by decide) gp_7 W_7_ok P_7_ok autos_7_ok bk_7_2_ok chk_7_3
def nodes_7_4 : List NodeSpec := [([5,0,1,2,3],[],[]),([0,1,2,6,3],[2],[0]),([1,4,2,7,3],[0,3],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_7_4 : checkNodes W_7 G_7 fmask_7 P_7 autos_7 bk_7_3 4 nodes_7_4 = true := by decide +kernel
def bk_7_4 : Array (List (List Nat)) := buildBuckets 2 W_7 nodes_7_4
lemma bk_7_4_ok : ∀ i (hi : i < bk_7_4.size), ∀ xs ∈ bk_7_4[i], Impossible G_7 4 xs.toFinset :=
  buildBuckets_sound (by decide) gp_7 W_7_ok P_7_ok autos_7_ok bk_7_3_ok chk_7_4
def nodes_7_5 : List NodeSpec := [([0,1,4,2,3],[0,1,3,2],[0,1,2,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_7_5 : checkNodes W_7 G_7 fmask_7 P_7 autos_7 bk_7_4 5 nodes_7_5 = true := by decide +kernel
def bk_7_5 : Array (List (List Nat)) := buildBuckets 1 W_7 nodes_7_5
lemma bk_7_5_ok : ∀ i (hi : i < bk_7_5.size), ∀ xs ∈ bk_7_5[i], Impossible G_7 5 xs.toFinset :=
  buildBuckets_sound (by decide) gp_7 W_7_ok P_7_ok autos_7_ok bk_7_4_ok chk_7_5
def nodes_7_6 : List NodeSpec := [([0,1,2,3],[0,1,3,2],[0,4,5,6,7,8])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_7_6 : checkNodes W_7 G_7 fmask_7 P_7 autos_7 bk_7_5 6 nodes_7_6 = true := by decide +kernel
def bk_7_6 : Array (List (List Nat)) := buildBuckets 1 W_7 nodes_7_6
lemma bk_7_6_ok : ∀ i (hi : i < bk_7_6.size), ∀ xs ∈ bk_7_6[i], Impossible G_7 6 xs.toFinset :=
  buildBuckets_sound (by decide) gp_7 W_7_ok P_7_ok autos_7_ok bk_7_5_ok chk_7_6
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma root_7_ok : forestRootCheck R_7 G_7 [(VAR 0,3,2),(VAR 1,3,1),(VAR 2,5,1),(VAR 4,17,1)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma root_7_in : bucketContains bk_7_6 R_7 = true := by decide +kernel
lemma low_7 : Lower R_7 G_7 7 := lower_of_forest root_7_ok bk_7_6_ok root_7_in

end Cofactor12068
def h49R : List Nat := varsOf 53
def h49G : Nat := 0xfffffafafafaa0a0fffffafafafaa0a0
lemma h49Bound : Lower h49R h49G 7 := carry_of (swaps := [(4,5),(2,3),(3,4),(1,2)]) (roots2 := Cofactor12068.R_7) (T2 := Cofactor12068.G_7) (by decide +kernel) Cofactor12068.low_7
def h50R : List Nat := varsOf 60
def h50G : Nat := 0xfffffff0fff0f000fffffff0fff0f000
lemma h50Bound : Lower h50R h50G 7 := carry_of (swaps := [(2,3),(0,1),(1,2)]) (roots2 := h49R) (T2 := h49G) (by decide +kernel) h49Bound
def h51R : List Nat := varsOf 21
def h51G : Nat := 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0
lemma h51Bound : Lower h51R h51G 4 := carry_of (swaps := [(4,5),(1,2),(2,3),(0,1)]) (roots2 := h3R) (T2 := h3G) (by decide +kernel) h3Bound
def h52R : List Nat := varsOf 29
def h52G : Nat := 0xfafaa0aafafaa0aafafaa0aafafaa0aa
lemma h52Bound : Lower h52R h52G 5 := lift_of (z := 0) (o := 8) (essPairs := [(VAR 3,1,9)]) (by decide +kernel) h51Bound
def h53R : List Nat := varsOf 45
def h53G : Nat := 0xaafaaafaa0aaa0aaaafaaafaa0aaa0aa
lemma h53Bound : Lower h53R h53G 6 := carry_of (swaps := [(1,2),(2,3),(3,4),(0,1)]) (roots2 := h35R) (T2 := h35G) (by decide +kernel) h35Bound
def h54R : List Nat := varsOf 52
def h54G : Nat := 0xfffff0f0f0f00000fffff0f0f0f00000
lemma h54Bound : Lower h54R h54G 4 := carry_of (swaps := [(3,4)]) (roots2 := h3R) (T2 := h3G) (by decide +kernel) h3Bound
def h55R : List Nat := varsOf 53
def h55G : Nat := 0xfffffafafafaaaaafffffafafafaaaaa
lemma h55Bound : Lower h55R h55G 5 := carry_of (swaps := [(3,4)]) (roots2 := h39R) (T2 := h39G) (by decide +kernel) h39Bound
def h56R : List Nat := varsOf 57
def h56G : Nat := 0xaaffaaaaaaaa00aaaaffaaaaaaaa00aa
lemma h56Bound : Lower h56R h56G 6 := carry_of (swaps := [(3,4),(1,2),(0,1)]) (roots2 := h35R) (T2 := h35G) (by decide +kernel) h35Bound
def h57R : List Nat := varsOf 28
def h57G : Nat := 0xf0ff00f0f0ff00f0f0ff00f0f0ff00f0
lemma h57Bound : Lower h57R h57G 4 := carry_of (swaps := [(4,5),(3,4),(1,2)]) (roots2 := h10R) (T2 := h10G) (by decide +kernel) h10Bound
def h58R : List Nat := varsOf 60
def h58G : Nat := 0xf0ff00f0f0f00000f0ff00f0f0f00000
lemma h58Bound : Lower h58R h58G 5 := carry_of (swaps := [(3,4)]) (roots2 := h44R) (T2 := h44G) (by decide +kernel) h44Bound
def h59R : List Nat := varsOf 29
def h59G : Nat := 0xfaffaafafaffaafafaffaafafaffaafa
lemma h59Bound : Lower h59R h59G 5 := carry_of (swaps := [(3,4)]) (roots2 := h45R) (T2 := h45G) (by decide +kernel) h45Bound
def h60R : List Nat := varsOf 53
def h60G : Nat := 0xfafaaaaafafaa0a0fafaaaaafafaa0a0
lemma h60Bound : Lower h60R h60G 5 := carry_of (swaps := [(2,3),(3,4),(4,5),(0,1),(1,2)]) (roots2 := h14R) (T2 := h14G) (by decide +kernel) h14Bound
def h48R : List Nat := varsOf 61
def h48G : Nat := 0xfaffaafafafaa0aafaffaafafafaa0aa
def h48Pos : List Nat := [1,20,5,13,1,36,1,13,20,25,36,41,48,25,48,57,45,1,36,17,28,20,48,28,5,28,60,60,41,17,33,41,1,52,48,52,17,1,5,41,52,33,45,28,28,28,28]
def h48Neg : List Nat := [0,16,4,9,4,44,9,12,4,9,4,9,56,24,16,56,44,16,32,16,9,0,32,12,0,24,44,56,44,9,32,32,32,32,0,4,0,8,9,40,16,0,9,16,8,44,56]
def h48Mask : Nat := fullMask 47
def h48Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x6f1f10baadd,0x44020100a48),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x7d4a0fb505ae,0x2008148105b4),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x7c809e91aa88,0x74e03e91bae8),(0xffff0000ffff0000ffff0000ffff0000,0x791e2ef8f302,0x49000a0af002),(0xffffffff00000000ffffffff00000000,0x78edc45dc20,0x6083dc459020)]
def h48Steps : List (Nat × Nat × Nat) := [(1,0,1),(2,0,1),(0,0,2),(1,0,2),(1,0,3),(1,1,2),(3,1,2),(0,1,3),(1,1,3),(2,2,4),(3,2,4),(1,2,5),(3,2,5),(0,2,13),(1,2,13),(2,2,13),(3,2,13),(0,4,5),(2,4,5),(0,4,13),(1,4,13),(2,4,13),(3,4,13),(0,5,9),(1,5,9),(2,5,13),(3,1,3),(1,1,4),(3,1,4),(3,1,9),(1,2,3),(2,2,3),(1,3,4),(3,3,4),(3,3,5),(3,3,9),(1,3,34),(0,0,4),(1,0,4),(2,0,4),(3,0,4),(0,0,13),(3,0,13),(0,2,29),(3,2,29),(0,4,29),(3,4,29),(1,1,40),(2,5,40),(2,2,46),(1,4,46),(2,4,46),(3,1,35),(3,0,57),(1,3,57),(0,5,35),(1,0,15),(1,1,61),(3,1,61),(1,1,15),(3,0,64),(1,3,64),(3,3,64),(1,3,15),(3,3,62),(2,5,15),(3,0,16),(1,3,71),(1,1,38),(1,0,73),(3,3,73),(2,5,38),(1,1,22),(1,0,23),(3,1,78),(3,3,78),(1,1,7),(1,3,81),(3,3,81),(3,7,13),(0,3,77),(1,3,77),(2,3,77),(3,3,77),(2,13,42),(3,3,43),(0,13,43),(3,13,43),(1,3,92),(1,3,33),(3,0,94),(3,1,94),(1,1,44),(1,3,97),(3,3,97),(2,13,44),(1,1,36),(3,3,10),(1,0,102),(3,11,37),(2,29,46),(2,13,15),(1,4,18),(0,4,19),(3,18,19),(3,24,25),(1,2,26),(2,2,27)]
def h48W : BT Decor := buildWiresBT 7 h48Base h48Steps
def h48AutoList : List (List (Nat × Nat)) := [[],[(2,4)]]
def h48Autos : BT (List (Nat × Nat)) := btOfList 1 h48AutoList
lemma h48Pairs : goodPairs h48G h48Pos h48Neg := goodPairs_of (by decide +kernel)
lemma h48BaseOk : ∀ x ∈ h48Base, faithful h48Pos h48Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma h48WOk : btAll (fun x => faithful h48Pos h48Neg x ∧ x.1 < 2^128) h48W := buildWiresBT_faithful h48BaseOk
lemma h48AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h48G = h48G) h48Autos := btAll_ofList (autos_of (by decide +kernel))
def h48SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 8,5),some (subcubeFast 0 32,5),some (subcubeFast 1 0,5),some (subcubeFast 1 32,4),some (subcubeFast 4 0,6),some (subcubeFast 8 0,5),some (subcubeFast 9 0,4),some (subcubeFast 16 0,6),some (subcubeFast 32 0,5),some (subcubeFast 32 8,4),some (0xaa55aa55aa55aa55aa55aa55aa55aa55,7),some (0xff00ffff00ff0000ff00ffff00ff00,7)]
def h48Slices : BT (Option (Nat × Nat)) := btOfList 4 h48SliceList
def h48Specs : List PoolSpec := poolSteps h48Steps [(4,[]),(2,[]),(6,[]),(10,[0]),(7,[0]),(4,[4]),(5,[0,4]),(1,[0,4]),(7,[]),(3,[]),(10,[]),(0,[]),(8,[]),(1,[]),(5,[0]),(1,[0]),(9,[]),(7,[0,44]),(7,[0,45]),(4,[34]),(5,[]),(4,[2]),(7,[2]),(4,[3]),(7,[3]),(4,[37]),(7,[37]),(10,[8]),(11,[8]),(4,[17,81]),(4,[37,84]),(4,[17]),(11,[]),(4,[38]),(7,[38]),(4,[38,86]),(4,[38,87]),(4,[39]),(7,[39]),(4,[40]),(7,[40]),(10,[5]),(7,[5]),(8,[31]),(8,[5]),(10,[5,97]),(4,[97]),(7,[6]),(4,[10]),(8,[6]),(4,[30]),(7,[52]),(4,[41]),(4,[41,49]),(4,[41,50]),(4,[41,51]),(4,[4,44]),(4,[4,45]),(4,[4,46]),(4,[25]),(4,[42]),(7,[42]),(4,[9]),(11,[8,101]),(4,[13]),(11,[8,13]),(4,[13,102]),(4,[14]),(4,[14,103]),(4,[15]),(4,[15,16]),(4,[16]),(4,[19]),(4,[19,20]),(4,[20]),(4,[21]),(7,[68]),(4,[21,106]),(11,[8,22]),(4,[22]),(4,[22,107]),(7,[27]),(0,[27]),(4,[33]),(0,[33]),(7,[28]),(4,[89]),(7,[9]),(7,[10])]
def h48Pools : BT (Option BoundPool) := buildPoolsBT 7 h48W h48R h48Slices h48Specs
set_option maxRecDepth 200000 in
lemma h48Slice11 : Slice h48R h48G (0xff00ffff00ff0000ff00ffff00ff00) 7 := opposite_slice (oppositeRow 3 5 53) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h49Bound
set_option maxRecDepth 200000 in
lemma h48Slice10 : Slice h48R h48G (0xaa55aa55aa55aa55aa55aa55aa55aa55) 7 := mapped_slice (identifyRow 0 3 60) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h50Bound
set_option maxRecDepth 200000 in
lemma h48Slice9 : Slice h48R h48G (subcubeFast 32 8) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h51Bound
set_option maxRecDepth 200000 in
lemma h48Slice8 : Slice h48R h48G (subcubeFast 32 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h52Bound
set_option maxRecDepth 200000 in
lemma h48Slice7 : Slice h48R h48G (subcubeFast 16 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h53Bound
set_option maxRecDepth 200000 in
lemma h48Slice6 : Slice h48R h48G (subcubeFast 9 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h54Bound
set_option maxRecDepth 200000 in
lemma h48Slice5 : Slice h48R h48G (subcubeFast 8 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h55Bound
set_option maxRecDepth 200000 in
lemma h48Slice4 : Slice h48R h48G (subcubeFast 4 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h56Bound
set_option maxRecDepth 200000 in
lemma h48Slice3 : Slice h48R h48G (subcubeFast 1 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h57Bound
set_option maxRecDepth 200000 in
lemma h48Slice2 : Slice h48R h48G (subcubeFast 1 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h58Bound
set_option maxRecDepth 200000 in
lemma h48Slice1 : Slice h48R h48G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h59Bound
set_option maxRecDepth 200000 in
lemma h48Slice0 : Slice h48R h48G (subcubeFast 0 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h60Bound
lemma h48SlicesOk : btAll (sliceSpec h48R h48G) h48Slices := btAll_ofList (P := sliceSpec h48R h48G) (sliceSpecCons h48Slice0 (sliceSpecCons h48Slice1 (sliceSpecCons h48Slice2 (sliceSpecCons h48Slice3 (sliceSpecCons h48Slice4 (sliceSpecCons h48Slice5 (sliceSpecCons h48Slice6 (sliceSpecCons h48Slice7 (sliceSpecCons h48Slice8 (sliceSpecCons h48Slice9 (sliceSpecCons h48Slice10 (sliceSpecCons h48Slice11 sliceSpecNil))))))))))))
set_option maxRecDepth 200000 in
lemma h48PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h48R h48G c) h48Pools := buildPoolsBT_sound h48SlicesOk
def h48Empty : BT (List (List Nat)) := BT.empty
lemma h48EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h48G (3 - 1) xs.toFinset) h48Empty := trivial
def h48Block3_0 : List NodeSpec := priorityNodes 7 [(541100077,1,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Test3_0 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Empty 3 h48Block3_0 = true := by decide +kernel
def h48Nodes3 : List NodeSpec := h48Block3_0
lemma h48Check3 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Empty 3 h48Nodes3 = true := h48Test3_0
def h48Bucket3 : BT (List (List Nat)) := buildBucketsBT h48W h48Nodes3
set_option maxRecDepth 200000 in
lemma h48Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h48G 3 xs.toFinset) h48Bucket3 := buildBucketsBT_sound (by decide) h48Pairs h48WOk h48PoolsOk h48AutosOk h48EmptyOk h48Check3
def h48Block4_0 : List NodeSpec := priorityNodes 7 [(1073199,1,2),(8156219,1,2),(17333291,1,2),(1366039,1,2),(1890327,1,2),(1370135,1,2),(6864971,157,2),(108020797,1,2),(337643595,164,2),(1367359771,1,2),(377701191,1,2),(1663093,1,2),(1728599,1,2),(440351,1,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Test4_0 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Bucket3 4 h48Block4_0 = true := by decide +kernel
def h48Nodes4 : List NodeSpec := h48Block4_0
lemma h48Check4 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Bucket3 4 h48Nodes4 = true := h48Test4_0
def h48Bucket4 : BT (List (List Nat)) := buildBucketsBT h48W h48Nodes4
set_option maxRecDepth 200000 in
lemma h48Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h48G 4 xs.toFinset) h48Bucket4 := buildBucketsBT_sound (by decide) h48Pairs h48WOk h48PoolsOk h48AutosOk h48Bucket3Ok h48Check4
def h48Block5_0 : List NodeSpec := priorityNodes 7 [(17512,36251386500,2),(3342973,129,2),(17514,16385,2),(241899,138,2),(52287,295896458,2),(794869,1,2),(35128445,128,2),(36177021,128,2),(55578955,17408,2),(860395,138,2),(2422831,138,2),(231487,136,2),(223295,138,2),(925941,2244610,2),(975083,17931,2),(239679,2278664,2),(544831,1,2),(2179317,138,2),(2244843,129,2),(806959,141,2),(577599,141,2),(593983,136,2),(178239,1,2),(38836341,138,2),(62527,1,2),(2922603,138,2),(40933463,139,2),(43030615,18442,6),(11282975,18445,6),(11807263,140,2),(696565,138,2),(729303,145,6)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Test5_0 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Bucket4 5 h48Block5_0 = true := by decide +kernel
def h48Block5_1 : List NodeSpec := priorityNodes 7 [(745567,146,6),(2408693,138,2),(143658091,136,2),(643135,2311690,2),(659519,1,2),(651327,1,2),(135269483,2344456,2),(675903,20108,2),(700479,158,2),(142762091,2607106,2),(159539307,18316,2),(176316523,1,2),(193093739,1,2),(195082347,129,2),(692287,129,2),(716863,20865,2),(725055,164,2),(216024095,144,2),(60307999,1,2),(141558891,141,2),(203470955,141,2),(733247,141,2),(177212523,136,2),(774207,2426507,2),(790591,1,2),(782399,1,2),(561215,1,2),(815167,1,2),(188776983,148,2),(46668887,141,2),(15076951,128,2),(44830315,139,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Test5_1 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Bucket4 5 h48Block5_1 = true := by decide +kernel
def h48Block5_2 : List NodeSpec := priorityNodes 7 [(188756015,148,2),(823359,1,2),(36739189,1,2),(43519063,181,2),(11142431,182,2),(11404575,183,2),(11275371,128,2),(38276183,184,2),(9831711,185,2),(10093855,186,2),(36743285,1,2),(41421931,128,2),(54004843,136,2),(256063,1,2),(839743,191,2),(62551,24720,2),(49546527,194,2),(46664811,179,2),(50070815,196,2),(185601131,128,2),(198743,198,2),(54815,201,2),(175115371,128,2),(63442027,204,2),(206572631,205,2),(56863,26384,2),(208669783,208,2),(38286879,128,2),(15862047,148,6),(626751,1,2),(749631,1,2),(243775,1,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Test5_2 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Bucket4 5 h48Block5_2 = true := by decide +kernel
def h48Block5_3 : List NodeSpec := priorityNodes 7 [(251967,1,2),(260159,1,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Test5_3 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Bucket4 5 h48Block5_3 = true := by decide +kernel
def h48Nodes5 : List NodeSpec := h48Block5_0 ++ h48Block5_1 ++ h48Block5_2 ++ h48Block5_3
lemma h48Check5 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Bucket4 5 h48Nodes5 = true := by
  unfold h48Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨h48Test5_0,h48Test5_1⟩,h48Test5_2⟩,h48Test5_3⟩
def h48Bucket5 : BT (List (List Nat)) := buildBucketsBT h48W h48Nodes5
set_option maxRecDepth 200000 in
lemma h48Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h48G 5 xs.toFinset) h48Bucket5 := buildBucketsBT_sound (by decide) h48Pairs h48WOk h48PoolsOk h48AutosOk h48Bucket4Ok h48Check5
def h48Block6_0 : List NodeSpec := priorityNodes 7 [(1148,287343236,6),(1150,2097284,6),(581877,268583426,2),(16506,38415646724,2),(125055,285212939,2),(65662,37581112706,2),(23679,17794,2),(25727,17794,2),(274559,285213836,2),(52287,295896458,6),(100479,2244996,6),(145471,5088756287876,6),(282751,2113540,6),(71807,17929,2),(75903,17929,2),(153663,2245250,2),(16702,291637908,6),(634943,312609289,2),(16958,2475394,2),(7734847,5367394339980,6),(1204331,17922,2),(602175,333579778,2),(7996991,43277272589,2),(2767391,270534288,2),(618559,310559753,6),(8259135,293737101,6),(766015,346162818,2),(17040959,2737673,2),(553023,37874746370,6),(3476055,5921434502530,2),(806975,46527436560,6),(69686,2889858,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Test6_0 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Bucket5 6 h48Block6_0 = true := by decide +kernel
def h48Block6_1 : List NodeSpec := priorityNodes 7 [(1738559,4813332941325,2),(227391,48077412610,2),(17565247,325076020,6),(4326975,2540161,6),(4589119,23937,6),(178239,4847967575740,2),(18089535,2228412,6),(49214,51061786256,2),(81982,686785965463563,6),(540734,403114507,2),(427583,409405963,6),(493119,3230219,6),(4210750,3262987,2),(1508927,3278476,2),(1639999,3311244,6),(1771071,426182284,6),(1902143,434570892,2),(2296095,2894089,6),(865823,7306293020169,2),(585791,54802966921,6),(610367,37604197385,6),(741439,446720784,6),(235583,4812511036546,6),(247871,36509517232,6)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Test6_1 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Bucket5 6 h48Block6_1 = true := by decide +kernel
def h48Nodes6 : List NodeSpec := h48Block6_0 ++ h48Block6_1
lemma h48Check6 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Bucket5 6 h48Nodes6 = true := by
  unfold h48Nodes6 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h48Test6_0,h48Test6_1⟩
def h48Bucket6 : BT (List (List Nat)) := buildBucketsBT h48W h48Nodes6
set_option maxRecDepth 200000 in
lemma h48Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h48G 6 xs.toFinset) h48Bucket6 := buildBucketsBT_sound (by decide) h48Pairs h48WOk h48PoolsOk h48AutosOk h48Bucket5Ok h48Check6
def h48Block7_0 : List NodeSpec := priorityNodes 7 [(126,4813324697602,2),(190,285360130,6),(318,314919433,6),(574,319144208,2),(157759,90186685371270658,6),(161855,704040235434249,6),(165951,348735106,6),(170047,352961680,2),(2110,45453705232,6),(4158,37948227586,6),(9791,0x9c365068c1604400,6),(58431,39898578953,6),(60479,446840848,6),(32830,57781749762,2),(65598,704020402439691,6)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Test7_0 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Bucket6 7 h48Block7_0 = true := by decide +kernel
def h48Nodes7 : List NodeSpec := h48Block7_0
lemma h48Check7 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Bucket6 7 h48Nodes7 = true := h48Test7_0
def h48Bucket7 : BT (List (List Nat)) := buildBucketsBT h48W h48Nodes7
set_option maxRecDepth 200000 in
lemma h48Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h48G 7 xs.toFinset) h48Bucket7 := buildBucketsBT_sound (by decide) h48Pairs h48WOk h48PoolsOk h48AutosOk h48Bucket6Ok h48Check7
def h48Block8_0 : List NodeSpec := priorityNodes 7 [(62,335709184,6)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Test8_0 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Bucket7 8 h48Block8_0 = true := by decide +kernel
def h48Nodes8 : List NodeSpec := h48Block8_0
lemma h48Check8 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Bucket7 8 h48Nodes8 = true := h48Test8_0
def h48Bucket8 : BT (List (List Nat)) := buildBucketsBT h48W h48Nodes8
set_option maxRecDepth 200000 in
lemma h48Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h48G 8 xs.toFinset) h48Bucket8 := buildBucketsBT_sound (by decide) h48Pairs h48WOk h48PoolsOk h48AutosOk h48Bucket7Ok h48Check8
set_option maxRecDepth 200000 in
lemma h48Bound : Lower h48R h48G 9 := lower_of_forestBT (essPairs := [(VAR 0,0,1),(VAR 2,9,13),(VAR 3,1,9),(VAR 4,4,20),(VAR 5,4,36)]) (by decide +kernel) h48Bucket8Ok (by decide +kernel)
def h62R : List Nat := varsOf 53
def h62G : Nat := 0xafafaaaafafaaaaaafafaaaafafaaaaa
lemma h62Bound : Lower h62R h62G 5 := lift_of (z := 1) (o := 16) (essPairs := [(VAR 0,0,1),(VAR 4,4,20)]) (by decide +kernel) h6Bound
def h63R : List Nat := varsOf 57
def h63G : Nat := 0xffffffaaff00aa00ffffffaaff00aa00
lemma h63Bound : Lower h63R h63G 5 := carry_of (swaps := [(2,3),(3,4),(2,3)]) (roots2 := h17R) (T2 := h17G) (by decide +kernel) h17Bound
def h64R : List Nat := varsOf 53
def h64G : Nat := 0xffffafaf0a0a0a0affffafaf0a0a0a0a
lemma h64Bound : Lower h64R h64G 5 := carry_of (swaps := [(1,2),(2,3),(3,4),(4,5),(1,2),(2,3),(3,4),(2,3),(0,1)]) (roots2 := h9R) (T2 := h9G) (by decide +kernel) h9Bound
def h65R : List Nat := varsOf 57
def h65G : Nat := 0xffaaffaaff00aaaaffaaffaaff00aaaa
lemma h65Bound : Lower h65R h65G 5 := carry_of (swaps := [(1,2),(2,3),(3,4),(1,2),(2,3),(0,1)]) (roots2 := h12R) (T2 := h12G) (by decide +kernel) h12Bound
def h66R : List Nat := varsOf 60
def h66G : Nat := 0xfffffff0f000f000fffffff0f000f000
lemma h66Bound : Lower h66R h66G 5 := carry_of (swaps := [(1,2),(2,3),(3,4),(4,5),(1,2),(2,3),(3,4),(0,1),(1,2)]) (roots2 := h14R) (T2 := h14G) (by decide +kernel) h14Bound
def h67R : List Nat := varsOf 29
def h67G : Nat := 0xfa0aaa0afa0aaa0afa0aaa0afa0aaa0a
lemma h67Bound : Lower h67R h67G 4 := lift_of (z := 0) (o := 16) (essPairs := [(VAR 4,12,28)]) (by decide +kernel) h4Bound
def h68R : List Nat := varsOf 45
def h68G : Nat := 0xafaaafaaaa0aaa0aafaaafaaaa0aaa0a
lemma h68Bound : Lower h68R h68G 6 := carry_of (swaps := [(1,2),(2,3),(3,4),(2,3),(0,1)]) (roots2 := h35R) (T2 := h35G) (by decide +kernel) h35Bound
def h69R : List Nat := varsOf 37
def h69G : Nat := 0xafafafaf0a0a0a0aafafafaf0a0a0a0a
lemma h69Bound : Lower h69R h69G 4 := carry_of (swaps := [(3,4),(4,5),(3,4),(2,3),(0,1)]) (roots2 := h10R) (T2 := h10G) (by decide +kernel) h10Bound
def h70R : List Nat := varsOf 53
def h70G : Nat := 0xafafaaaa0a0a0a0aafafaaaa0a0a0a0a
lemma h70Bound : Lower h70R h70G 5 := carry_of (swaps := [(2,3),(3,4),(2,3)]) (roots2 := h41R) (T2 := h41G) (by decide +kernel) h41Bound
def h71R : List Nat := varsOf 28
def h71G : Nat := 0xff0f0f00ff0f0f00ff0f0f00ff0f0f00
lemma h71Bound : Lower h71R h71G 4 := carry_of (swaps := [(4,5),(3,4),(1,2),(2,3)]) (roots2 := h10R) (T2 := h10G) (by decide +kernel) h10Bound
def h72R : List Nat := varsOf 44
def h72G : Nat := 0xff0fff0ff000f000ff0fff0ff000f000
lemma h72Bound : Lower h72R h72G 3 := carry_of (swaps := [(0,1),(1,2),(2,3),(3,4),(4,5),(2,3),(1,2)]) (roots2 := h4R) (T2 := h4G) (by decide +kernel) h4Bound
def h73R : List Nat := varsOf 52
def h73G : Nat := 0xffff0f0ff0f00000ffff0f0ff0f00000
lemma h73Bound : Lower h73R h73G 3 := carry_of (swaps := [(0,1),(1,2),(2,3),(3,4),(4,5),(2,3),(3,4),(1,2)]) (roots2 := h4R) (T2 := h4G) (by decide +kernel) h4Bound
def h74R : List Nat := varsOf 60
def h74G : Nat := 0xff0f0f00f0000000ff0f0f00f0000000
def h74Pos : List Nat := [40,48,40,48,28,40,28,40,48,28,28,56]
def h74Neg : List Nat := [32,52,36,32,12,8,20,44,16,16,24,24]
def h74Mask : Nat := fullMask 12
def h74Base : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,1616,214),(0xff00ff00ff00ff00ff00ff00ff00ff00,3829,3248),(0xffff0000ffff0000ffff0000ffff0000,3930,3906),(0xffffffff00000000ffffffff00000000,2479,143)]
def h74Steps : List (Nat × Nat × Nat) := [(0,0,1),(3,0,1),(3,0,3),(0,1,2),(2,2,5)]
def h74W : BT Decor := buildWiresBT 4 h74Base h74Steps
def h74AutoList : List (List (Nat × Nat)) := [[],[(3,4)]]
def h74Autos : BT (List (Nat × Nat)) := btOfList 1 h74AutoList
lemma h74Pairs : goodPairs h74G h74Pos h74Neg := goodPairs_of (by decide +kernel)
lemma h74BaseOk : ∀ x ∈ h74Base, faithful h74Pos h74Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma h74WOk : btAll (fun x => faithful h74Pos h74Neg x ∧ x.1 < 2^128) h74W := buildWiresBT_faithful h74BaseOk
lemma h74AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h74G = h74G) h74Autos := btAll_ofList (autos_of (by decide +kernel))
def h74SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 8,3),some (subcubeFast 0 16,3),some (subcubeFast 0 32,4),some (0xf0f0f0ff0f0f0f00f0f0f0ff0f0f0f0,4)]
def h74Slices : BT (Option (Nat × Nat)) := btOfList 2 h74SliceList
def h74Specs : List PoolSpec := [(2,[]),(3,[]),(0,[]),(1,[])]
def h74Pools : BT (Option BoundPool) := buildPoolsBT 2 h74W h74R h74Slices h74Specs
set_option maxRecDepth 200000 in
lemma h74Slice3 : Slice h74R h74G (0xf0f0f0ff0f0f0f00f0f0f0ff0f0f0f0) 4 := opposite_slice (oppositeRow 2 5 56) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h37Bound
set_option maxRecDepth 200000 in
lemma h74Slice2 : Slice h74R h74G (subcubeFast 0 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h71Bound
set_option maxRecDepth 200000 in
lemma h74Slice1 : Slice h74R h74G (subcubeFast 0 16) 3 := slice_fast_direct (zDead := 0) (by decide +kernel) h72Bound
set_option maxRecDepth 200000 in
lemma h74Slice0 : Slice h74R h74G (subcubeFast 0 8) 3 := slice_fast_direct (zDead := 0) (by decide +kernel) h73Bound
lemma h74SlicesOk : btAll (sliceSpec h74R h74G) h74Slices := btAll_ofList (P := sliceSpec h74R h74G) (sliceSpecCons h74Slice0 (sliceSpecCons h74Slice1 (sliceSpecCons h74Slice2 (sliceSpecCons h74Slice3 sliceSpecNil))))
lemma h74PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h74R h74G c) h74Pools := buildPoolsBT_sound h74SlicesOk
def h74Empty : BT (List (List Nat)) := BT.empty
lemma h74EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h74G (2 - 1) xs.toFinset) h74Empty := trivial
def h74Block2_0 : List NodeSpec := priorityNodes 2 [(644,1,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h74Test2_0 : checkNodesBT h74W h74G h74Mask h74Pools h74Autos h74Empty 2 h74Block2_0 = true := by decide +kernel
def h74Nodes2 : List NodeSpec := h74Block2_0
lemma h74Check2 : checkNodesBT h74W h74G h74Mask h74Pools h74Autos h74Empty 2 h74Nodes2 = true := h74Test2_0
def h74Bucket2 : BT (List (List Nat)) := buildBucketsBT h74W h74Nodes2
lemma h74Bucket2Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h74G 2 xs.toFinset) h74Bucket2 := buildBucketsBT_sound (by decide) h74Pairs h74WOk h74PoolsOk h74AutosOk h74EmptyOk h74Check2
def h74Block3_0 : List NodeSpec := priorityNodes 2 [(172,1,2),(204,1,2),(534,1,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h74Test3_0 : checkNodesBT h74W h74G h74Mask h74Pools h74Autos h74Bucket2 3 h74Block3_0 = true := by decide +kernel
def h74Nodes3 : List NodeSpec := h74Block3_0
lemma h74Check3 : checkNodesBT h74W h74G h74Mask h74Pools h74Autos h74Bucket2 3 h74Nodes3 = true := h74Test3_0
def h74Bucket3 : BT (List (List Nat)) := buildBucketsBT h74W h74Nodes3
lemma h74Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h74G 3 xs.toFinset) h74Bucket3 := buildBucketsBT_sound (by decide) h74Pairs h74WOk h74PoolsOk h74AutosOk h74Bucket2Ok h74Check3
def h74Block4_0 : List NodeSpec := priorityNodes 2 [(62,20,2),(94,7,2),(142,4,6),(286,6,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h74Test4_0 : checkNodesBT h74W h74G h74Mask h74Pools h74Autos h74Bucket3 4 h74Block4_0 = true := by decide +kernel
def h74Nodes4 : List NodeSpec := h74Block4_0
lemma h74Check4 : checkNodesBT h74W h74G h74Mask h74Pools h74Autos h74Bucket3 4 h74Nodes4 = true := h74Test4_0
def h74Bucket4 : BT (List (List Nat)) := buildBucketsBT h74W h74Nodes4
lemma h74Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h74G 4 xs.toFinset) h74Bucket4 := buildBucketsBT_sound (by decide) h74Pairs h74WOk h74PoolsOk h74AutosOk h74Bucket3Ok h74Check4
def h74Block5_0 : List NodeSpec := priorityNodes 2 [(30,120,6)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h74Test5_0 : checkNodesBT h74W h74G h74Mask h74Pools h74Autos h74Bucket4 5 h74Block5_0 = true := by decide +kernel
def h74Nodes5 : List NodeSpec := h74Block5_0
lemma h74Check5 : checkNodesBT h74W h74G h74Mask h74Pools h74Autos h74Bucket4 5 h74Nodes5 = true := h74Test5_0
def h74Bucket5 : BT (List (List Nat)) := buildBucketsBT h74W h74Nodes5
lemma h74Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h74G 5 xs.toFinset) h74Bucket5 := buildBucketsBT_sound (by decide) h74Pairs h74WOk h74PoolsOk h74AutosOk h74Bucket4Ok h74Check5
lemma h74Bound : Lower h74R h74G 6 := lower_of_forestBT (essPairs := [(VAR 2,24,28),(VAR 3,20,28),(VAR 4,12,28),(VAR 5,8,40)]) (by decide +kernel) h74Bucket5Ok (by decide +kernel)
def h75R : List Nat := varsOf 29
def h75G : Nat := 0xffafafaaffafafaaffafafaaffafafaa
lemma h75Bound : Lower h75R h75G 5 := carry_of (swaps := [(3,4),(2,3)]) (roots2 := h45R) (T2 := h45G) (by decide +kernel) h45Bound
def h76R : List Nat := varsOf 45
def h76G : Nat := 0xffafffaffa0afa0affafffaffa0afa0a
def h76Pos : List Nat := [1,12,1,37,1,13,12,32,37,32,40,13,9,44]
def h76Neg : List Nat := [0,8,5,36,4,5,4,0,5,36,8,8,8,36]
def h76Mask : Nat := fullMask 14
def h76Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,6461,292),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x296a,9084),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x3c62,7170),(0xffffffff00000000ffffffff00000000,0x2788,8712)]
def h76Steps : List (Nat × Nat × Nat) := [(1,0,1),(3,0,1),(1,0,3),(2,1,2),(1,3,5)]
def h76W : BT Decor := buildWiresBT 4 h76Base h76Steps
def h76AutoList : List (List (Nat × Nat)) := [[],[(0,5)]]
def h76Autos : BT (List (Nat × Nat)) := btOfList 1 h76AutoList
lemma h76Pairs : goodPairs h76G h76Pos h76Neg := goodPairs_of (by decide +kernel)
lemma h76BaseOk : ∀ x ∈ h76Base, faithful h76Pos h76Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma h76WOk : btAll (fun x => faithful h76Pos h76Neg x ∧ x.1 < 2^128) h76W := buildWiresBT_faithful h76BaseOk
lemma h76AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h76G = h76G) h76Autos := btAll_ofList (autos_of (by decide +kernel))
def h76SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 1 0,3),some (subcubeFast 8 0,4),some (subcubeFast 32 0,3),some (0xff00ff00ff00ff00ff00ff00ff00ff0,4)]
def h76Slices : BT (Option (Nat × Nat)) := btOfList 2 h76SliceList
def h76Specs : List PoolSpec := [(0,[]),(1,[]),(3,[]),(2,[])]
def h76Pools : BT (Option BoundPool) := buildPoolsBT 2 h76W h76R h76Slices h76Specs
set_option maxRecDepth 200000 in
lemma h76Slice3 : Slice h76R h76G (0xff00ff00ff00ff00ff00ff00ff00ff0) 4 := opposite_slice (oppositeRow 2 3 41) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h20Bound
set_option maxRecDepth 200000 in
lemma h76Slice2 : Slice h76R h76G (subcubeFast 32 0) 3 := slice_fast_direct (zDead := 0) (by decide +kernel) h4Bound
set_option maxRecDepth 200000 in
lemma h76Slice1 : Slice h76R h76G (subcubeFast 8 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h69Bound
set_option maxRecDepth 200000 in
lemma h76Slice0 : Slice h76R h76G (subcubeFast 1 0) 3 := slice_fast_direct (zDead := 0) (by decide +kernel) h72Bound
lemma h76SlicesOk : btAll (sliceSpec h76R h76G) h76Slices := btAll_ofList (P := sliceSpec h76R h76G) (sliceSpecCons h76Slice0 (sliceSpecCons h76Slice1 (sliceSpecCons h76Slice2 (sliceSpecCons h76Slice3 sliceSpecNil))))
lemma h76PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h76R h76G c) h76Pools := buildPoolsBT_sound h76SlicesOk
def h76Empty : BT (List (List Nat)) := BT.empty
lemma h76EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h76G (2 - 1) xs.toFinset) h76Empty := trivial
def h76Block2_0 : List NodeSpec := priorityNodes 2 [(770,1,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h76Test2_0 : checkNodesBT h76W h76G h76Mask h76Pools h76Autos h76Empty 2 h76Block2_0 = true := by decide +kernel
def h76Nodes2 : List NodeSpec := h76Block2_0
lemma h76Check2 : checkNodesBT h76W h76G h76Mask h76Pools h76Autos h76Empty 2 h76Nodes2 = true := h76Test2_0
def h76Bucket2 : BT (List (List Nat)) := buildBucketsBT h76W h76Nodes2
lemma h76Bucket2Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h76G 2 xs.toFinset) h76Bucket2 := buildBucketsBT_sound (by decide) h76Pairs h76WOk h76PoolsOk h76AutosOk h76EmptyOk h76Check2
def h76Block3_0 : List NodeSpec := priorityNodes 2 [(306,1,2),(338,1,2),(526,1,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h76Test3_0 : checkNodesBT h76W h76G h76Mask h76Pools h76Autos h76Bucket2 3 h76Block3_0 = true := by decide +kernel
def h76Nodes3 : List NodeSpec := h76Block3_0
lemma h76Check3 : checkNodesBT h76W h76G h76Mask h76Pools h76Autos h76Bucket2 3 h76Nodes3 = true := h76Test3_0
def h76Bucket3 : BT (List (List Nat)) := buildBucketsBT h76W h76Nodes3
lemma h76Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h76G 3 xs.toFinset) h76Bucket3 := buildBucketsBT_sound (by decide) h76Pairs h76WOk h76PoolsOk h76AutosOk h76Bucket2Ok h76Check3
def h76Block4_0 : List NodeSpec := priorityNodes 2 [(62,25,2),(94,7,2),(158,4,2),(278,5,6)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h76Test4_0 : checkNodesBT h76W h76G h76Mask h76Pools h76Autos h76Bucket3 4 h76Block4_0 = true := by decide +kernel
def h76Nodes4 : List NodeSpec := h76Block4_0
lemma h76Check4 : checkNodesBT h76W h76G h76Mask h76Pools h76Autos h76Bucket3 4 h76Nodes4 = true := h76Test4_0
def h76Bucket4 : BT (List (List Nat)) := buildBucketsBT h76W h76Nodes4
lemma h76Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h76G 4 xs.toFinset) h76Bucket4 := buildBucketsBT_sound (by decide) h76Pairs h76WOk h76PoolsOk h76AutosOk h76Bucket3Ok h76Check4
def h76Block5_0 : List NodeSpec := priorityNodes 2 [(30,113,6)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h76Test5_0 : checkNodesBT h76W h76G h76Mask h76Pools h76Autos h76Bucket4 5 h76Block5_0 = true := by decide +kernel
def h76Nodes5 : List NodeSpec := h76Block5_0
lemma h76Check5 : checkNodesBT h76W h76G h76Mask h76Pools h76Autos h76Bucket4 5 h76Nodes5 = true := h76Test5_0
def h76Bucket5 : BT (List (List Nat)) := buildBucketsBT h76W h76Nodes5
lemma h76Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h76G 5 xs.toFinset) h76Bucket5 := buildBucketsBT_sound (by decide) h76Pairs h76WOk h76PoolsOk h76AutosOk h76Bucket4Ok h76Check5
lemma h76Bound : Lower h76R h76G 6 := lower_of_forestBT (essPairs := [(VAR 0,0,1),(VAR 2,1,5),(VAR 3,4,12),(VAR 5,0,32)]) (by decide +kernel) h76Bucket5Ok (by decide +kernel)
def h77R : List Nat := varsOf 53
def h77G : Nat := 0xffffafaffafaaaaaffffafaffafaaaaa
lemma h77Bound : Lower h77R h77G 4 := carry_of (swaps := [(2,3),(3,4),(4,5),(1,2),(2,3),(3,4),(2,3)]) (roots2 := h31R) (T2 := h31G) (by decide +kernel) h31Bound
def h78R : List Nat := varsOf 57
def h78G : Nat := 0xffaaaaaaff00aa00ffaaaaaaff00aa00
lemma h78Bound : Lower h78R h78G 4 := carry_of (swaps := [(2,3),(3,4),(2,3)]) (roots2 := h46R) (T2 := h46G) (by decide +kernel) h46Bound
def h61R : List Nat := varsOf 61
def h61G : Nat := 0xffafafaafa0aaa0affafafaafa0aaa0a
def h61Pos : List Nat := [1,28,1,13,1,40,13,28,48,37,40,9,37,17,37,28,48,17,53,33,9,48,60,40,40,45,60,28,9,33,28,40,40,60,53,13,13,29,48,1,25,13,28,1,17,17,1,56,33,37,25,45,60,48,28,28,13]
def h61Neg : List Nat := [0,24,5,12,4,32,5,12,32,5,8,8,36,21,32,20,16,16,52,32,5,52,52,36,44,44,44,16,12,5,52,0,12,24,21,8,44,21,24,8,24,4,21,32,20,5,21,24,0,4,21,5,20,36,8,4,21]
def h61Mask : Nat := fullMask 57
def h61Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x10f7bbc321e7a5d,0x10c642420102244),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x1da063e4e44d2ca,0x1be763577f4b2dc),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x1dc873bdfd08cea,0x4081db17000c8a),(0xffff0000ffff0000ffff0000ffff0000,0xf4b5664c67a182,0x114d5664867a002),(0xffffffff00000000ffffffff00000000,0x3b8047a7ed5720,0x20081047ec5120)]
def h61Steps : List (Nat × Nat × Nat) := [(1,0,1),(3,0,1),(0,1,2),(1,1,2),(2,1,2),(0,2,3),(2,2,3),(0,2,4),(1,2,4),(2,2,4),(3,2,4),(0,2,5),(1,2,5),(3,2,5),(1,2,6),(2,2,6),(3,2,6),(1,3,9),(2,3,9),(0,4,5),(2,4,5),(0,4,6),(1,4,6),(2,4,6),(0,4,9),(1,4,9),(2,4,9),(2,5,9),(3,1,2),(0,1,3),(2,1,3),(3,1,3),(0,1,4),(1,1,4),(2,1,4),(3,1,4),(1,0,2),(3,0,2),(1,0,3),(3,0,3),(1,0,4),(2,0,4),(3,0,4),(1,0,7),(1,4,7),(2,4,7),(1,0,50),(2,1,50),(2,2,50),(3,0,8),(0,4,8),(2,4,8),(3,4,8),(1,0,9),(1,0,12),(2,5,12),(1,9,12),(1,0,37),(1,2,37),(2,2,37),(1,1,12),(2,1,12),(1,0,66),(1,0,15),(3,0,15),(1,1,15),(1,0,52),(1,2,52),(2,5,15),(2,4,73),(3,1,17),(1,0,25),(1,2,28),(2,2,28),(3,6,8),(1,0,79),(0,4,59),(1,6,12),(3,20,27),(1,9,33),(2,4,33),(1,2,40),(0,1,59),(3,0,65),(0,2,65),(3,0,70),(3,2,70),(2,1,21),(2,4,21),(1,0,93),(2,1,93),(3,1,77),(1,1,78),(2,1,69),(3,7,41),(3,37,41),(3,1,76),(3,40,41),(2,44,75),(1,1,42),(2,1,42),(2,4,42),(2,1,106),(3,9,43),(0,43,70),(1,7,15),(1,0,55),(1,9,44),(1,33,44),(1,0,85),(0,1,45),(3,7,45),(3,2,45),(2,1,117),(0,8,45),(3,9,45),(3,33,45),(3,37,45),(0,1,63),(3,7,38),(3,15,38),(1,3,91),(2,3,91),(1,7,40),(2,8,37),(2,8,39),(1,9,37),(3,40,63)]
def h61W : BT Decor := buildWiresBT 8 h61Base h61Steps
def h61AutoList : List (List (Nat × Nat)) := [[]]
def h61Autos : BT (List (Nat × Nat)) := btOfList 1 h61AutoList
lemma h61Pairs : goodPairs h61G h61Pos h61Neg := goodPairs_of (by decide +kernel)
lemma h61BaseOk : ∀ x ∈ h61Base, faithful h61Pos h61Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma h61WOk : btAll (fun x => faithful h61Pos h61Neg x ∧ x.1 < 2^128) h61W := buildWiresBT_faithful h61BaseOk
lemma h61AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h61G = h61G) h61Autos := btAll_ofList (autos_of (by decide +kernel))
def h61SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 4,4),some (subcubeFast 0 8,4),some (subcubeFast 0 16,6),some (subcubeFast 0 32,5),some (subcubeFast 1 0,6),some (subcubeFast 1 8,3),some (subcubeFast 1 16,3),some (subcubeFast 1 32,4),some (subcubeFast 8 0,5),some (subcubeFast 8 16,4),some (subcubeFast 16 0,6),some (subcubeFast 32 0,4),some (subcubeFast 32 16,3),some (0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5,5),some (0xf0f00f0ff0f00f0ff0f00f0ff0f00f0f,5),some (0xff00ff0000ff00ffff00ff0000ff00ff,5),some (0xff00ff00ff00ff00ff00ff00ff00ff0,4),some (0xf0f0f0ff0f0f0f00f0f0f0ff0f0f0f0,5),some (0xff00ffff00ff0000ff00ffff00ff00,5)]
def h61Slices : BT (Option (Nat × Nat)) := btOfList 5 h61SliceList
def h61Specs : List PoolSpec := poolSteps h61Steps [(4,[]),(0,[]),(7,[]),(13,[]),(5,[]),(8,[]),(3,[0]),(4,[4]),(2,[0,4]),(2,[0]),(10,[0]),(3,[]),(11,[]),(1,[]),(15,[]),(10,[]),(2,[]),(2,[0,13]),(4,[20]),(18,[]),(3,[1]),(2,[1,4]),(2,[4,1,22]),(4,[22]),(4,[23]),(2,[1]),(10,[1]),(2,[1,22]),(10,[1,22]),(2,[1,23]),(10,[1,23]),(4,[35]),(10,[1,14]),(4,[16,88]),(4,[2]),(2,[2]),(3,[36]),(3,[64]),(2,[4]),(3,[54]),(10,[36]),(2,[36]),(8,[38]),(14,[]),(6,[]),(4,[7]),(9,[]),(3,[37]),(10,[37]),(2,[37]),(10,[3]),(2,[3]),(12,[]),(3,[38]),(10,[4]),(4,[32]),(10,[32]),(2,[32]),(10,[35]),(2,[35]),(10,[10]),(2,[10]),(8,[39]),(10,[2]),(3,[39]),(4,[2,45]),(10,[2,45]),(4,[4,107]),(4,[28]),(10,[28]),(10,[7]),(2,[40]),(10,[40]),(10,[40,110]),(4,[32,117]),(17,[]),(10,[40,112]),(2,[42]),(10,[42]),(16,[]),(3,[63]),(2,[2,44]),(10,[2,44]),(2,[4,34]),(2,[33]),(10,[33]),(2,[34]),(10,[34]),(8,[18]),(4,[4,26]),(3,[57]),(10,[32,58]),(10,[34,35]),(2,[35,81]),(2,[8]),(10,[8]),(2,[9]),(10,[9]),(10,[10,65])]
def h61Pools : BT (Option BoundPool) := buildPoolsBT 7 h61W h61R h61Slices h61Specs
set_option maxRecDepth 200000 in
lemma h61Slice18 : Slice h61R h61G (0xff00ffff00ff0000ff00ffff00ff00) 5 := opposite_slice (oppositeRow 3 5 53) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h62Bound
set_option maxRecDepth 200000 in
lemma h61Slice17 : Slice h61R h61G (0xf0f0f0ff0f0f0f00f0f0f0ff0f0f0f0) 5 := opposite_slice (oppositeRow 2 5 57) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h63Bound
set_option maxRecDepth 200000 in
lemma h61Slice16 : Slice h61R h61G (0xff00ff00ff00ff00ff00ff00ff00ff0) 4 := opposite_slice (oppositeRow 2 3 41) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h20Bound
set_option maxRecDepth 200000 in
lemma h61Slice15 : Slice h61R h61G (0xff00ff0000ff00ffff00ff0000ff00ff) 5 := mapped_slice (identifyRow 3 5 53) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h64Bound
set_option maxRecDepth 200000 in
lemma h61Slice14 : Slice h61R h61G (0xf0f00f0ff0f00f0ff0f00f0ff0f00f0f) 5 := mapped_slice (identifyRow 2 4 57) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h65Bound
set_option maxRecDepth 200000 in
lemma h61Slice13 : Slice h61R h61G (0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5) 5 := mapped_slice (identifyRow 0 2 60) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h66Bound
set_option maxRecDepth 200000 in
lemma h61Slice12 : Slice h61R h61G (subcubeFast 32 16) 3 := slice_fast_direct (zDead := 0) (by decide +kernel) h4Bound
set_option maxRecDepth 200000 in
lemma h61Slice11 : Slice h61R h61G (subcubeFast 32 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h67Bound
set_option maxRecDepth 200000 in
lemma h61Slice10 : Slice h61R h61G (subcubeFast 16 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h68Bound
set_option maxRecDepth 200000 in
lemma h61Slice9 : Slice h61R h61G (subcubeFast 8 16) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h69Bound
set_option maxRecDepth 200000 in
lemma h61Slice8 : Slice h61R h61G (subcubeFast 8 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h70Bound
set_option maxRecDepth 200000 in
lemma h61Slice7 : Slice h61R h61G (subcubeFast 1 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h71Bound
set_option maxRecDepth 200000 in
lemma h61Slice6 : Slice h61R h61G (subcubeFast 1 16) 3 := slice_fast_direct (zDead := 0) (by decide +kernel) h72Bound
set_option maxRecDepth 200000 in
lemma h61Slice5 : Slice h61R h61G (subcubeFast 1 8) 3 := slice_fast_direct (zDead := 0) (by decide +kernel) h73Bound
set_option maxRecDepth 200000 in
lemma h61Slice4 : Slice h61R h61G (subcubeFast 1 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h74Bound
set_option maxRecDepth 200000 in
lemma h61Slice3 : Slice h61R h61G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h75Bound
set_option maxRecDepth 200000 in
lemma h61Slice2 : Slice h61R h61G (subcubeFast 0 16) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h76Bound
set_option maxRecDepth 200000 in
lemma h61Slice1 : Slice h61R h61G (subcubeFast 0 8) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h77Bound
set_option maxRecDepth 200000 in
lemma h61Slice0 : Slice h61R h61G (subcubeFast 0 4) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h78Bound
lemma h61SlicesOk : btAll (sliceSpec h61R h61G) h61Slices := btAll_ofList (P := sliceSpec h61R h61G) (sliceSpecCons h61Slice0 (sliceSpecCons h61Slice1 (sliceSpecCons h61Slice2 (sliceSpecCons h61Slice3 (sliceSpecCons h61Slice4 (sliceSpecCons h61Slice5 (sliceSpecCons h61Slice6 (sliceSpecCons h61Slice7 (sliceSpecCons h61Slice8 (sliceSpecCons h61Slice9 (sliceSpecCons h61Slice10 (sliceSpecCons h61Slice11 (sliceSpecCons h61Slice12 (sliceSpecCons h61Slice13 (sliceSpecCons h61Slice14 (sliceSpecCons h61Slice15 (sliceSpecCons h61Slice16 (sliceSpecCons h61Slice17 (sliceSpecCons h61Slice18 sliceSpecNil)))))))))))))))))))
set_option maxRecDepth 200000 in
lemma h61PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h61R h61G c) h61Pools := buildPoolsBT_sound h61SlicesOk
def h61Empty : BT (List (List Nat)) := BT.empty
lemma h61EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h61G (4 - 1) xs.toFinset) h61Empty := trivial
def h61Block4_0 : List NodeSpec := priorityNodes 7 [(108022827,1,2),(26483017,1,2),(7922331,150,2),(27345563,150,2),(99634219,1,2),(1728559,1,2),(478273621,1,2),(339773495,1,2),(27394871,1,2),(285488139,1,2),(1451237531,1,2),(128982071,1,2),(80747575,1,2),(102832171,180,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test4_0 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Empty 4 h61Block4_0 = true := by decide +kernel
def h61Nodes4 : List NodeSpec := h61Block4_0
lemma h61Check4 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Empty 4 h61Nodes4 = true := h61Test4_0
def h61Bucket4 : BT (List (List Nat)) := buildBucketsBT h61W h61Nodes4
set_option maxRecDepth 200000 in
lemma h61Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h61G 4 xs.toFinset) h61Bucket4 := buildBucketsBT_sound (by decide) h61Pairs h61WOk h61PoolsOk h61AutosOk h61EmptyOk h61Check4
def h61Block5_0 : List NodeSpec := priorityNodes 7 [(1272,1,2),(745567,1,2),(9330,1,2),(225515,17152,2),(58431,2295168,2),(1007851,1,2),(532534,1,2),(231487,1,2),(778475,140,2),(569407,133,2),(2277471,1,2),(205655,1,2),(671903,18827,2),(704671,18188,2),(729311,130,2),(2557355,1,2),(2688427,1,2),(9634155,1,2),(639391,1,2),(672159,1,2),(618559,18447,2),(9394,1,2),(756923,149,2),(2428331,151,2),(2559403,152,2),(3214523,149,2),(606879,19995,2),(639647,331828227,2),(860703,19995,2),(730655,20253,2),(3506549,133,2),(3899755,140,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test5_0 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket4 5 h61Block5_0 = true := by decide +kernel
def h61Block5_1 : List NodeSpec := priorityNodes 7 [(3965291,128,2),(643135,139,2),(8454507,18956,2),(3047787,140,2),(651327,302237060,2),(2228767,1,2),(2490911,1,2),(984607,2559383,2),(2229791,2592408,2),(725055,1,2),(370719,161,2),(26143,152,2),(51914271,20253,2),(52962847,1,2),(9765719,142,2),(4096855,165,2),(981512279,1,2),(38012503,167,2),(931147883,139,2),(645935211,1,2),(790591,1,2),(595636341,17026,2),(880840811,1,2),(806975,1,2),(2867435,1,2),(830533679,170,2),(813764655,1,2),(245426283,144,2),(947916907,141,2),(9109867,128,2),(545321007,2803712,2),(264310831,18348,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test5_1 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket4 5 h61Block5_1 = true := by decide +kernel
def h61Block5_2 : List NodeSpec := priorityNodes 7 [(174123115,144,2),(749631,131,2),(774207,1,2),(847935,140,2),(1712175,22276,2),(1124196437,16692,2),(230748207,18436,2),(39907375,16436,2),(9506863,162,2),(2393015,1,2),(61870519,192,2),(1714703,24897,2),(13701167,1,2),(48304175,1,2),(193495863,1,2),(34091831,1,2),(14202927,1,2),(1777711,195,2),(612438063,18447,2),(696324143,1,2),(1794095,24336,2),(9637391,128,2),(38372751,190,2),(180424751,190,2),(188813359,1,2),(222367791,2819972,2),(35721263,190,2),(14222187,139,2),(12387179,139,2),(255869207,1,2),(14484311,139,2),(2905119,1,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test5_2 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket4 5 h61Block5_2 = true := by decide +kernel
def h61Block5_3 : List NodeSpec := priorityNodes 7 [(921663,133,2),(11031583,1,2),(946239,1,2),(954431,128,2),(595669109,133,2),(692115563,201,2),(169890847,1,2),(962623,1,2),(489503,202,2),(717231135,1,2),(566290539,1,2),(45353247,203,2),(3953695,203,2),(938047,17797,2),(545276183,130,2),(48328821,139,2),(2909215,17922,2),(3113815,1,2),(3179351,1,2),(1318999,26542,2),(3703639,140,2),(197148951,147,2),(11076439,25995,2),(987199,147,2),(12648747,140,2),(8586071,139,2),(12067871,1,2),(198719,140,2),(213926167,142,2),(1019967,2361230,2),(4031319,208,2),(200285271,133,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test5_3 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket4 5 h61Block5_3 = true := by decide +kernel
def h61Block5_4 : List NodeSpec := priorityNodes 7 [(228383,1,2),(687135,140,2),(194623,133,2),(12191319,1,2),(1028159,1,2),(1036351,1,2),(880703,1,2),(37488215,21249,2),(55083835,211,2),(44254007,166,2),(40109655,129,2),(39585367,174,2),(49325335,142,2),(2241055,203,2),(53519639,147,2),(13239895,174,2),(3027767,1,2),(13764183,1,2),(8061755,16516,2),(8923183,141,2),(3946543,141,2),(8927279,1,2),(741439,180,2),(578900085,1,2),(788733999,174,2),(905279,1,2),(165680159,23058,2),(49294367,1,2),(57936159,133,2),(241231959,1,2),(237041751,1,2),(2382749783,1,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test5_4 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket4 5 h61Block5_4 = true := by decide +kernel
def h61Block5_5 : List NodeSpec := priorityNodes 7 [(2449858647,1,2),(42732119,1,2),(42208855,1,2),(136326175,140,2),(16124191,180,2),(700460063,133,2),(775957535,1,2),(26236971,26036,2),(13118495,203,2),(684095,1,2),(692287,139,2),(260159,1,2),(708671,302237060,2),(553023,1,2),(38856811,140,2),(138416235,141,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test5_5 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket4 5 h61Block5_5 = true := by decide +kernel
def h61Nodes5 : List NodeSpec := h61Block5_0 ++ h61Block5_1 ++ h61Block5_2 ++ h61Block5_3 ++ h61Block5_4 ++ h61Block5_5
lemma h61Check5 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket4 5 h61Nodes5 = true := by
  unfold h61Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨h61Test5_0,h61Test5_1⟩,h61Test5_2⟩,h61Test5_3⟩,h61Test5_4⟩,h61Test5_5⟩
def h61Bucket5 : BT (List (List Nat)) := buildBucketsBT h61W h61Nodes5
set_option maxRecDepth 200000 in
lemma h61Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h61G 5 xs.toFinset) h61Bucket5 := buildBucketsBT_sound (by decide) h61Pairs h61WOk h61PoolsOk h61AutosOk h61Bucket4Ok h61Check5
def h61Block6_0 : List NodeSpec := priorityNodes 7 [(252,2113922,2),(382,2130433,2),(634,281018500,2),(1146,285311108,2),(1150,2262145,2),(266367,16514,2),(8318,17025,2),(65662,37591482500,2),(23679,2130433,2),(13887,4951854203012,2),(14911,81680899137323140,2),(27775,37063049729,2),(42047,4951856201858,2),(79999,17153,2),(44095,4951856201996,2),(446,278987138,2),(698,2424964,2),(702,16897,2),(1210,312803332,2),(1214,5298116887172,2),(450751,2526340,2),(516287,39753793920,2),(1130687,20354,2),(8382,291553292,2),(65726,293650692,2),(15935,633733969350660,2),(110783,2179460,2),(118975,41391489539,2),(35903,37614765444,2),(46143,4951856201996,2),(25119,327599511,2),(176351,327598466,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test6_0 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket5 6 h61Block6_0 = true := by decide +kernel
def h61Block6_1 : List NodeSpec := priorityNodes 7 [(26143,37585653400,2),(50239,4951856203266,2),(184543,42473655299,2),(368831,16770,2),(2261847,4854189670661,2),(8521303,5713390748557,2),(4724799,2294413,2),(411711,37591662849,2),(725055,73817331282739853,2),(432035903,2179213,2),(585791,79429102274166785,2),(289429567,355074701,2),(634943,38686180866,2),(339761215,2278029,2),(536639,4951856136460,2),(8783447,2867844,2),(5773375,17028,2),(1329215,293634692,2),(823359,4951854203524,2),(831551,38411622148,2),(839743,633837325402372,2),(9306671,380442372,2),(9045551,380442372,2),(13643823,356581684,2),(3706927,356581684,2),(14949423,377526020,2),(2458415,35438711102,2),(9568815,403675396,2),(9307695,403675908,2),(12113967,52747641518,2),(15740975,398531586,2),(9474095,398531842,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test6_1 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket5 6 h61Block6_1 = true := by decide +kernel
def h61Block6_2 : List NodeSpec := priorityNodes 7 [(34079791,3244350,2),(15473711,3080452,2),(1262015,17797,2),(4915519,16523,2),(4784959,53836169860,2),(6581311,53835990401,2),(8918047,270605195,2),(913471,38682059906,2),(798783,4951856201858,2),(4000031,17796,2),(929855,38658049666,2),(1327551,2180610,2),(5177663,17922,2),(5047103,7098800881924,2),(7629887,433276418,2),(11015199,37320940428,2),(8522015,2294274,2),(182335,37604086062,2),(822,16558,2),(500159,2295173,2),(516543,54625092997,2),(1065407,17797,2),(1098175,2295169,2),(1086,4916687504004,2),(65846,295878830,2),(95263,441729666,2),(97311,426788398,2),(190527,426788398,2),(206911,633837337968772,2),(1590,2720388,2),(1933631,1,2),(2064703,1,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test6_2 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket5 6 h61Block6_2 = true := by decide +kernel
def h61Block6_3 : List NodeSpec := priorityNodes 7 [(211007,34387181748,2),(6226239,17793,2),(215103,38686359684,2),(6488383,17921,2),(223295,616104502477188,2),(3212887,2719918,2),(1868607,6371609331333,2),(1934143,0xd5a92db261a2c281,2),(1999679,57894160005,2),(2065215,50319263105,2),(9270,295716270,2),(66614,44562563716,2),(574,4951854203012,2),(886319,377739012,2),(951855,3543812,2),(52287,54526199300,2),(1409855,2294413,2),(56383,37499388596,2),(1475391,377668237,2),(626751,4916686880942,2),(1207359,23736,2),(1731647,3533569,2),(667711,37312546350,2),(239679,0x1b44078d18141b7,2),(106960959,3578764,2),(922655,2606516,2),(243775,893356341396100,2),(111155263,17036,2),(115349567,18060,2),(149567,4951856203266,2),(3082527,294830722,2),(1400919,22274,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test6_3 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket5 6 h61Block6_3 = true := by decide +kernel
def h61Block6_4 : List NodeSpec := priorityNodes 7 [(1433687,2310274,2),(716863,4951839360642,2),(205855,462602370,2),(137279,4951856201858,2),(561215,38686246530,2),(593983,567970529106434,2),(306202687,2136594,2),(3605791,2294402,2),(3344671,333628084,2),(675903,972522086547588,2),(390088767,50319245964,2),(28330047,2311564,2),(227391,5738906801838,2),(251967,37312725166,2),(256063,35188114990,2),(65598,633837593839106,2),(979007,38686246530,2),(757823,4951839555714,2),(766015,22274,2),(1044543,22274,2),(528447,633834902390276,2),(544831,0xe21a300101e14581,2),(29101631,6510124025228,2),(198719,0x8c160c80f00342cb,2),(19664447,37859902860,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test6_4 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket5 6 h61Block6_4 = true := by decide +kernel
def h61Nodes6 : List NodeSpec := h61Block6_0 ++ h61Block6_1 ++ h61Block6_2 ++ h61Block6_3 ++ h61Block6_4
lemma h61Check6 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket5 6 h61Nodes6 = true := by
  unfold h61Nodes6 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨h61Test6_0,h61Test6_1⟩,h61Test6_2⟩,h61Test6_3⟩,h61Test6_4⟩
def h61Bucket6 : BT (List (List Nat)) := buildBucketsBT h61W h61Nodes6
set_option maxRecDepth 200000 in
lemma h61Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h61G 6 xs.toFinset) h61Bucket6 := buildBucketsBT_sound (by decide) h61Pairs h61WOk h61PoolsOk h61AutosOk h61Bucket5Ok h61Check6
def h61Block7_0 : List NodeSpec := priorityNodes 7 [(126,4572548448258,2),(190,4570705444866,2),(153663,4409136464514,2),(157759,47613771781,2),(323631,364939264,2),(331823,2131840,2),(170047,35854073867,2),(178239,280209026,2),(318,2281774,2),(574,611328841253508,2),(1086,81131142061326980,2),(60479,4951851950638,2),(137279,892990659609996,2),(141375,0x196407850356a02,2),(145471,280357634,2),(149567,585368462348161,2),(8254,363005358,2),(9791,633859792388738,2),(32830,473432706,2),(65598,563378770854532,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test7_0 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket6 7 h61Block7_0 = true := by decide +kernel
def h61Nodes7 : List NodeSpec := h61Block7_0
lemma h61Check7 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket6 7 h61Nodes7 = true := h61Test7_0
def h61Bucket7 : BT (List (List Nat)) := buildBucketsBT h61W h61Nodes7
set_option maxRecDepth 200000 in
lemma h61Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h61G 7 xs.toFinset) h61Bucket7 := buildBucketsBT_sound (by decide) h61Pairs h61WOk h61PoolsOk h61AutosOk h61Bucket6Ok h61Check7
def h61Block8_0 : List NodeSpec := priorityNodes 7 [(62,2361216,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test8_0 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket7 8 h61Block8_0 = true := by decide +kernel
def h61Nodes8 : List NodeSpec := h61Block8_0
lemma h61Check8 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket7 8 h61Nodes8 = true := h61Test8_0
def h61Bucket8 : BT (List (List Nat)) := buildBucketsBT h61W h61Nodes8
set_option maxRecDepth 200000 in
lemma h61Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h61G 8 xs.toFinset) h61Bucket8 := buildBucketsBT_sound (by decide) h61Pairs h61WOk h61PoolsOk h61AutosOk h61Bucket7Ok h61Check8
set_option maxRecDepth 200000 in
lemma h61Bound : Lower h61R h61G 9 := lower_of_forestBT (essPairs := [(VAR 0,0,1),(VAR 2,1,5),(VAR 3,5,13),(VAR 4,12,28),(VAR 5,5,37)]) (by decide +kernel) h61Bucket8Ok (by decide +kernel)
def h79R : List Nat := varsOf 62
def h79G : Nat := 0xfcccfffcf0c0fcccfcccfffcf0c0fccc
lemma h79Bound : Lower h79R h79G 9 := carry_of (swaps := [(2,3),(0,1)]) (roots2 := h33R) (T2 := h33G) (by decide +kernel) h33Bound
def h80R : List Nat := varsOf 62
def h80G : Nat := 0xfcffccfcf0ccc0ccfcffccfcf0ccc0cc
lemma h80Bound : Lower h80R h80G 9 := carry_of (swaps := [(2,3),(0,1)]) (roots2 := h61R) (T2 := h61G) (by decide +kernel) h61Bound
def h81R : List Nat := varsOf 62
def h81G : Nat := 0xffcfcfccffcccc0cffcfcfccffcccc0c
lemma h81Bound : Lower h81R h81G 9 := carry_of (swaps := [(2,3),(0,1)]) (roots2 := h48R) (T2 := h48G) (by decide +kernel) h48Bound
def h83R : List Nat := varsOf 58
def h83G : Nat := 0xffffffff33cc0000ffffffff33cc0000
lemma h83Bound : Lower h83R h83G 5 := carry_of (swaps := [(0,1),(1,2),(2,3),(3,4),(4,5),(3,4)]) (roots2 := h62R) (T2 := h62G) (by decide +kernel) h62Bound
def h86R : List Nat := varsOf 30
def h86G : Nat := 0xf3c0f000f3c0f000f3c0f000f3c0f000
lemma h86Bound : Lower h86R h86G 5 := carry_of (swaps := [(4,5),(2,3),(3,4),(2,3),(0,1),(1,2)]) (roots2 := h27R) (T2 := h27G) (by decide +kernel) h27Bound
def h87R : List Nat := varsOf 54
def h87G : Nat := 0xfffff0f0c0c00000fffff0f0c0c00000
lemma h87Bound : Lower h87R h87G 5 := carry_of (swaps := [(1,2),(2,3),(3,4),(4,5),(1,2),(2,3),(3,4),(2,3),(0,1),(1,2)]) (roots2 := h24R) (T2 := h24G) (by decide +kernel) h24Bound
def h88R : List Nat := varsOf 58
def h88G : Nat := 0xffffff0033000000ffffff0033000000
lemma h88Bound : Lower h88R h88G 5 := lift_of (z := 2) (o := 0) (essPairs := [(VAR 1,24,26)]) (by decide +kernel) h37Bound
def h89R : List Nat := varsOf 60
def h89G : Nat := 0xfffffff0ff00f000fffffff0ff00f000
lemma h89Bound : Lower h89R h89G 5 := carry_of (swaps := [(2,3),(3,4),(2,3),(0,1),(1,2)]) (roots2 := h17R) (T2 := h17G) (by decide +kernel) h17Bound
def h90R : List Nat := varsOf 46
def h90G : Nat := 0xfffffffff3c0f3c0fffffffff3c0f3c0
lemma h90Bound : Lower h90R h90G 4 := carry_of (swaps := [(0,1),(1,2),(2,3),(3,4),(4,5),(3,4),(1,2),(2,3),(0,1),(1,2)]) (roots2 := h31R) (T2 := h31G) (by decide +kernel) h31Bound
def h91R : List Nat := varsOf 60
def h91G : Nat := 0xfffffff0f0f0f000fffffff0f0f0f000
lemma h91Bound : Lower h91R h91G 5 := carry_of (swaps := [(2,3),(3,4),(0,1),(1,2),(2,3),(1,2)]) (roots2 := h17R) (T2 := h17G) (by decide +kernel) h17Bound
def h82R : List Nat := varsOf 62
def h82G : Nat := 0xfffffff0f3c0f000fffffff0f3c0f000
def h82Pos : List Nat := [12,24,14,22,12,14,24,22,24,40,36,36,48,40,50,22,58,50,50,48,52,48,38,22,30,38,28,42,14,12,36]
def h82Neg : List Nat := [8,26,10,20,4,6,8,18,16,8,4,32,32,32,26,6,26,18,34,20,20,16,6,26,26,34,20,34,26,20,20]
def h82Mask : Nat := fullMask 31
def h82Base : List Decor := [(0xcccccccccccccccccccccccccccccccc,0x1bc7c0ac,0x1bc7c0a6),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x77d08cbd,0x64588438),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x3d012377,0x11814247),(0xffff0000ffff0000ffff0000ffff0000,0x5bfd1ca,0x75bb418a),(0xffffffff00000000ffffffff00000000,0x4a7f7e00,0xa043800)]
def h82Steps : List (Nat × Nat × Nat) := [(0,0,3),(1,1,2),(1,1,3),(1,1,4),(1,2,3),(1,2,4),(3,1,10),(1,3,4),(2,3,5),(1,4,5),(3,2,8),(1,4,13),(1,0,4),(3,4,17),(3,4,6),(3,2,7),(3,1,9),(3,1,12),(3,2,12)]
def h82W : BT Decor := buildWiresBT 5 h82Base h82Steps
def h82AutoList : List (List (Nat × Nat)) := [[]]
def h82Autos : BT (List (Nat × Nat)) := btOfList 1 h82AutoList
lemma h82Pairs : goodPairs h82G h82Pos h82Neg := goodPairs_of (by decide +kernel)
lemma h82BaseOk : ∀ x ∈ h82Base, faithful h82Pos h82Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma h82WOk : btAll (fun x => faithful h82Pos h82Neg x ∧ x.1 < 2^128) h82W := buildWiresBT_faithful h82BaseOk
lemma h82AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h82G = h82G) h82Autos := btAll_ofList (autos_of (by decide +kernel))
def h82SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 2,5),some (subcubeFast 0 16,4),some (subcubeFast 2 0,5),some (subcubeFast 4 0,5),some (subcubeFast 6 0,4),some (subcubeFast 8 0,5),some (subcubeFast 8 2,4),some (subcubeFast 16 0,4),some (subcubeFast 16 2,4),some (subcubeFast 18 0,4),some (subcubeFast 32 0,5),some (subcubeFast 32 16,3),some (0xff00ff00ff00ff00ff00ff00ff00ff0,5)]
def h82Slices : BT (Option (Nat × Nat)) := btOfList 4 h82SliceList
def h82Specs : List PoolSpec := [(2,[]),(0,[]),(4,[]),(5,[(0,0,3)]),(7,[]),(10,[(0,0,3)]),(1,[]),(6,[]),(11,[]),(8,[]),(9,[]),(10,[]),(3,[]),(5,[]),(12,[])]
def h82Pools : BT (Option BoundPool) := buildPoolsBT 4 h82W h82R h82Slices h82Specs
set_option maxRecDepth 200000 in
lemma h82Slice15 : Slice h82R h82G (0xff00ff00ff00ff00ff00ff00ff00ff0) 5 := opposite_slice (oppositeRow 2 3 58) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h83Bound
set_option maxRecDepth 200000 in
lemma h82Slice11 : Slice h82R h82G (subcubeFast 32 16) 3 := slice_fast_direct (zDead := 0) (by decide +kernel) h13Bound
set_option maxRecDepth 200000 in
lemma h82Slice10 : Slice h82R h82G (subcubeFast 32 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h86Bound
set_option maxRecDepth 200000 in
lemma h82Slice9 : Slice h82R h82G (subcubeFast 18 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h3Bound
set_option maxRecDepth 200000 in
lemma h82Slice8 : Slice h82R h82G (subcubeFast 16 2) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h3Bound
set_option maxRecDepth 200000 in
lemma h82Slice7 : Slice h82R h82G (subcubeFast 16 0) 4 := slice_fast_direct (zDead := 2) (by decide +kernel) h3Bound
set_option maxRecDepth 200000 in
lemma h82Slice6 : Slice h82R h82G (subcubeFast 8 2) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h54Bound
set_option maxRecDepth 200000 in
lemma h82Slice5 : Slice h82R h82G (subcubeFast 8 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h87Bound
set_option maxRecDepth 200000 in
lemma h82Slice4 : Slice h82R h82G (subcubeFast 6 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h37Bound
set_option maxRecDepth 200000 in
lemma h82Slice3 : Slice h82R h82G (subcubeFast 4 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h88Bound
set_option maxRecDepth 200000 in
lemma h82Slice2 : Slice h82R h82G (subcubeFast 2 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h89Bound
set_option maxRecDepth 200000 in
lemma h82Slice1 : Slice h82R h82G (subcubeFast 0 16) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h90Bound
set_option maxRecDepth 200000 in
lemma h82Slice0 : Slice h82R h82G (subcubeFast 0 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h91Bound
lemma h82SlicesOk : btAll (sliceSpec h82R h82G) h82Slices := btAll_ofList (P := sliceSpec h82R h82G) (sliceSpecCons h82Slice0 (sliceSpecCons h82Slice1 (sliceSpecCons h82Slice2 (sliceSpecCons h82Slice3 (sliceSpecCons h82Slice4 (sliceSpecCons h82Slice5 (sliceSpecCons h82Slice6 (sliceSpecCons h82Slice7 (sliceSpecCons h82Slice8 (sliceSpecCons h82Slice9 (sliceSpecCons h82Slice10 (sliceSpecCons h82Slice11 (sliceSpecCons h82Slice15 sliceSpecNil)))))))))))))
set_option maxRecDepth 200000 in
lemma h82PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h82R h82G c) h82Pools := buildPoolsBT_sound h82SlicesOk
def h82Empty : BT (List (List Nat)) := BT.empty
lemma h82EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h82G (4 - 1) xs.toFinset) h82Empty := trivial
def h82Block4_0 : List NodeSpec := priorityNodes 4 [(2706,1,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h82Test4_0 : checkNodesBT h82W h82G h82Mask h82Pools h82Autos h82Empty 4 h82Block4_0 = true := by decide +kernel
def h82Nodes4 : List NodeSpec := h82Block4_0
lemma h82Check4 : checkNodesBT h82W h82G h82Mask h82Pools h82Autos h82Empty 4 h82Nodes4 = true := h82Test4_0
def h82Bucket4 : BT (List (List Nat)) := buildBucketsBT h82W h82Nodes4
set_option maxRecDepth 200000 in
lemma h82Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h82G 4 xs.toFinset) h82Bucket4 := buildBucketsBT_sound (by decide) h82Pairs h82WOk h82PoolsOk h82AutosOk h82EmptyOk h82Check4
def h82Block5_0 : List NodeSpec := priorityNodes 4 [(2172,356,2),(32828,292,2),(16956,356,2),(25717,372,2),(698,29,2),(2230,28,2),(15935,272,2),(33855,1,2),(2590,28,2),(65598,1,2),(35903,1,2),(4158,1,2),(37951,1,2),(39999,1,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h82Test5_0 : checkNodesBT h82W h82G h82Mask h82Pools h82Autos h82Bucket4 5 h82Block5_0 = true := by decide +kernel
def h82Nodes5 : List NodeSpec := h82Block5_0
lemma h82Check5 : checkNodesBT h82W h82G h82Mask h82Pools h82Autos h82Bucket4 5 h82Nodes5 = true := h82Test5_0
def h82Bucket5 : BT (List (List Nat)) := buildBucketsBT h82W h82Nodes5
set_option maxRecDepth 200000 in
lemma h82Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h82G 5 xs.toFinset) h82Bucket5 := buildBucketsBT_sound (by decide) h82Pairs h82WOk h82PoolsOk h82AutosOk h82Bucket4Ok h82Check5
def h82Block6_0 : List NodeSpec := priorityNodes 4 [(124,86850,2),(16444,98932,2),(27765,6073,2),(29813,4794,2),(190,28724850,2),(318,121128,2),(574,32355458,2),(1086,117368,2),(2110,32289927,2),(8254,31240614,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h82Test6_0 : checkNodesBT h82W h82G h82Mask h82Pools h82Autos h82Bucket5 6 h82Block6_0 = true := by decide +kernel
def h82Nodes6 : List NodeSpec := h82Block6_0
lemma h82Check6 : checkNodesBT h82W h82G h82Mask h82Pools h82Autos h82Bucket5 6 h82Nodes6 = true := h82Test6_0
def h82Bucket6 : BT (List (List Nat)) := buildBucketsBT h82W h82Nodes6
set_option maxRecDepth 200000 in
lemma h82Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h82G 6 xs.toFinset) h82Bucket6 := buildBucketsBT_sound (by decide) h82Pairs h82WOk h82PoolsOk h82AutosOk h82Bucket5Ok h82Check6
def h82Block7_0 : List NodeSpec := priorityNodes 4 [(62,1952538,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h82Test7_0 : checkNodesBT h82W h82G h82Mask h82Pools h82Autos h82Bucket6 7 h82Block7_0 = true := by decide +kernel
def h82Nodes7 : List NodeSpec := h82Block7_0
lemma h82Check7 : checkNodesBT h82W h82G h82Mask h82Pools h82Autos h82Bucket6 7 h82Nodes7 = true := h82Test7_0
def h82Bucket7 : BT (List (List Nat)) := buildBucketsBT h82W h82Nodes7
set_option maxRecDepth 200000 in
lemma h82Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h82G 7 xs.toFinset) h82Bucket7 := buildBucketsBT_sound (by decide) h82Pairs h82WOk h82PoolsOk h82AutosOk h82Bucket6Ok h82Check7
set_option maxRecDepth 200000 in
lemma h82Bound : Lower h82R h82G 8 := lower_of_forestBT (essPairs := [(VAR 1,20,22),(VAR 2,8,12),(VAR 3,4,12),(VAR 4,6,22),(VAR 5,4,36)]) (by decide +kernel) h82Bucket7Ok (by decide +kernel)
namespace Cofactor12116

def R_23 : List Nat := varsOf 46
def G_23 : Nat := 0xfffcfffcfcc0fcc0fffcfffcfcc0fcc0
lemma low_23 : Lower R_23 G_23 7 := carry_of (swaps := [(4,5),(2,3),(1,2),(0,1)]) (roots2 := Cofactor12068.R_7) (T2 := Cofactor12068.G_7) (by decide +kernel) Cofactor12068.low_7

def G_46 : Nat := 0xfefefefee8e8e8e8fefefefee8e8e8e8
def R_46 : List Nat := varsOf 39
lemma low_46_ok : carryOK [(0,3),(0,2),(0,1)] R_46 G_46 R_23 G_23 = true := by decide +kernel
lemma low_46 : Lower R_46 G_46 7 := carry_of low_46_ok low_23

def G_59 : Nat := 0xfefee8e8e8e8e8e8fefee8e8e8e8e8e8
def R_59 : List Nat := varsOf 55
lemma low_59_ok : liftCheck 0 16 R_59 G_59 R_46 G_46 [(VAR 4,49,33)] = true := by decide +kernel
lemma low_59 : Lower R_59 G_59 8 := lift_of low_59_ok low_46

end Cofactor12116
def h94R : List Nat := varsOf 54
def h94G : Nat := 0xfcfcfcfcf0f0ccccfcfcfcfcf0f0cccc
lemma h94Bound : Lower h94R h94G 5 := carry_of (swaps := [(1,2),(2,3),(3,4),(1,2)]) (roots2 := h12R) (T2 := h12G) (by decide +kernel) h12Bound
def h96R : List Nat := varsOf 53
def h96G : Nat := 0xffffa0a0fafa0000ffffa0a0fafa0000
lemma h96Bound : Lower h96R h96G 6 := carry_of (swaps := [(3,4)]) (roots2 := h18R) (T2 := h18G) (by decide +kernel) h18Bound
def h98R : List Nat := varsOf 54
def h98G : Nat := 0xfcfcf0f0f0f0c0c0fcfcf0f0f0f0c0c0
lemma h98Bound : Lower h98R h98G 6 := carry_of (swaps := [(2,3),(3,4),(0,1)]) (roots2 := h18R) (T2 := h18G) (by decide +kernel) h18Bound
def h99R : List Nat := varsOf 23
def h99G : Nat := 0xfafa8888fafa8888fafa8888fafa8888
lemma h99Bound : Lower h99R h99G 4 := carry_of (swaps := [(4,5),(3,4),(1,2),(2,3),(1,2)]) (roots2 := h46R) (T2 := h46G) (by decide +kernel) h46Bound
def h100R : List Nat := varsOf 39
def h100G : Nat := 0xe8e8e8e888888888e8e8e8e888888888
lemma h100Bound : Lower h100R h100G 5 := lift_of (z := 0) (o := 4) (essPairs := [(VAR 2,33,37)]) (by decide +kernel) h15Bound
def h101R : List Nat := varsOf 19
def h101G : Nat := 0xeeee8888eeee8888eeee8888eeee8888
lemma h101Bound : Lower h101R h101G 4 := carry_of (swaps := [(4,5),(1,2),(2,3),(0,1),(1,2)]) (roots2 := h3R) (T2 := h3G) (by decide +kernel) h3Bound
def h102R : List Nat := varsOf 51
def h102G : Nat := 0xeeee8888aaaa8888eeee8888aaaa8888
lemma h102Bound : Lower h102R h102G 5 := carry_of (swaps := [(2,3),(3,4),(0,1)]) (roots2 := h24R) (T2 := h24G) (by decide +kernel) h24Bound
def h103R : List Nat := varsOf 53
def h103G : Nat := 0xfafaa0a0fafa0000fafaa0a0fafa0000
lemma h103Bound : Lower h103R h103G 5 := carry_of (swaps := [(1,2),(2,3),(3,4),(1,2)]) (roots2 := h24R) (T2 := h24G) (by decide +kernel) h24Bound
def h104R : List Nat := varsOf 22
def h104G : Nat := 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0
lemma h104Bound : Lower h104R h104G 4 := carry_of (swaps := [(4,5),(1,2),(2,3)]) (roots2 := h3R) (T2 := h3G) (by decide +kernel) h3Bound
def h105R : List Nat := varsOf 54
def h105G : Nat := 0xfcfcc0c0f0f00000fcfcc0c0f0f00000
lemma h105Bound : Lower h105R h105G 5 := carry_of (swaps := [(1,2),(2,3),(3,4),(0,1),(1,2),(0,1)]) (roots2 := h100R) (T2 := h100G) (by decide +kernel) h100Bound
def h106R : List Nat := varsOf 23
def h106G : Nat := 0xfefee8e8fefee8e8fefee8e8fefee8e8
lemma h106Bound : Lower h106R h106G 7 := Cofactor12068.low_7
def h107R : List Nat := varsOf 51
def h107G : Nat := 0xffffeeeeffff8888ffffeeeeffff8888
lemma h107Bound : Lower h107R h107G 5 := carry_of (swaps := [(0,1),(1,2),(2,3),(3,4),(0,1),(1,2)]) (roots2 := h39R) (T2 := h39G) (by decide +kernel) h39Bound
def h93R : List Nat := varsOf 55
def h93G : Nat := 0xfefee8e8fafa8888fefee8e8fafa8888
def h93Pos : List Nat := [17,38,17,20,37,37,20,17,38,37,3,50,22,22,3,21,50,17,35,7,3,20,7,49,19,38,35,50,21,52,37,17,49,3,3,7,21,19,49,3,17,7]
def h93Neg : List Nat := [16,36,18,16,33,36,4,1,6,5,2,48,18,6,1,5,18,5,34,6,18,0,5,33,18,34,33,34,1,36,1,33,1,0,6,2,16,1,48,5,0,1]
def h93Mask : Nat := fullMask 42
def h93Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x3ffd5dec6b5,0x2a1d4c2c290),(0xcccccccccccccccccccccccccccccccc,0x2ae0f5d7d02,0xc0b1d3504),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x2187268b37a,0x84204aa362),(0xffff0000ffff0000ffff0000ffff0000,0x171b9a3b8cd,0x500111180d),(0xffffffff00000000ffffffff00000000,0x416e850b32,0x40ae840832)]
def h93Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(3,0,1),(0,0,2),(1,0,2),(2,0,2),(3,0,2),(0,0,3),(1,0,3),(2,0,3),(0,1,2),(1,1,2),(2,1,2),(2,1,3),(0,2,3),(1,0,20),(1,2,3),(2,2,3),(3,2,3),(1,2,5),(2,2,5),(1,3,5),(0,1,27),(0,2,27),(1,2,27),(2,2,27),(3,2,27),(2,3,5),(2,4,5),(1,5,20),(3,0,22),(1,3,36),(0,4,22),(1,5,38),(3,5,22),(1,5,24),(2,4,29),(0,4,30),(3,3,6),(0,4,6),(1,2,45),(2,2,45),(1,3,45),(2,3,45),(2,22,45),(0,6,22),(2,6,24),(0,2,48),(3,2,48),(1,3,7),(1,7,24),(1,3,9),(0,4,10),(2,4,11),(0,4,14),(2,4,14),(1,12,19),(1,1,13),(2,1,13),(2,4,13),(1,0,16),(3,3,66),(2,14,16),(0,4,17),(1,0,18)]
def h93W : BT Decor := buildWiresBT 7 h93Base h93Steps
def h93AutoList : List (List (Nat × Nat)) := [[],[(1,2),(0,4)]]
def h93Autos : BT (List (Nat × Nat)) := btOfList 1 h93AutoList
lemma h93Pairs : goodPairs h93G h93Pos h93Neg := goodPairs_of (by decide +kernel)
lemma h93BaseOk : ∀ x ∈ h93Base, faithful h93Pos h93Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma h93WOk : btAll (fun x => faithful h93Pos h93Neg x ∧ x.1 < 2^128) h93W := buildWiresBT_faithful h93BaseOk
lemma h93AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h93G = h93G) h93Autos := btAll_ofList (autos_of (by decide +kernel))
def h93SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 2,5),some (subcubeFast 0 4,5),some (subcubeFast 0 32,7),some (subcubeFast 1 0,5),some (subcubeFast 1 2,4),some (subcubeFast 1 32,4),some (subcubeFast 2 0,5),some (subcubeFast 2 32,4),some (subcubeFast 4 0,5),some (subcubeFast 4 32,4),some (subcubeFast 16 0,5),some (subcubeFast 16 4,4),some (subcubeFast 32 0,4),some (0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5,6),some (0xcccc3333cccc3333cccc3333cccc3333,6),some (0x5555aaaa5555aaaa5555aaaa5555aaaa,5)]
def h93Slices : BT (Option (Nat × Nat)) := btOfList 4 h93SliceList
def h93Specs : List PoolSpec := poolSteps h93Steps [(3,[]),(6,[]),(2,[0]),(13,[]),(8,[]),(10,[]),(2,[15,16]),(0,[]),(1,[]),(2,[15]),(0,[29]),(5,[]),(12,[]),(14,[]),(2,[]),(0,[22]),(2,[0,22]),(2,[17]),(8,[33]),(10,[33]),(2,[18]),(11,[]),(2,[19]),(2,[0,20]),(2,[0,21]),(2,[0,28]),(4,[]),(2,[1]),(1,[14]),(3,[40]),(7,[]),(6,[40]),(2,[2,50]),(2,[3]),(2,[4,52]),(2,[5]),(1,[9]),(15,[]),(9,[]),(2,[8,58]),(2,[8,59]),(2,[9]),(2,[11,61]),(2,[12])]
def h93Pools : BT (Option BoundPool) := buildPoolsBT 6 h93W h93R h93Slices h93Specs
set_option maxRecDepth 200000 in
lemma h93Slice17 : Slice h93R h93G (0x5555aaaa5555aaaa5555aaaa5555aaaa) 5 := opposite_slice (oppositeRow 0 4 54) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h94Bound
set_option maxRecDepth 200000 in
lemma h93Slice15 : Slice h93R h93G (0xcccc3333cccc3333cccc3333cccc3333) 6 := mapped_slice (identifyRow 1 4 53) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h96Bound
set_option maxRecDepth 200000 in
lemma h93Slice13 : Slice h93R h93G (0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5) 6 := mapped_slice (identifyRow 0 2 54) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h98Bound
set_option maxRecDepth 200000 in
lemma h93Slice12 : Slice h93R h93G (subcubeFast 32 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h99Bound
set_option maxRecDepth 200000 in
lemma h93Slice11 : Slice h93R h93G (subcubeFast 16 4) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h15Bound
set_option maxRecDepth 200000 in
lemma h93Slice10 : Slice h93R h93G (subcubeFast 16 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h100Bound
set_option maxRecDepth 200000 in
lemma h93Slice9 : Slice h93R h93G (subcubeFast 4 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h101Bound
set_option maxRecDepth 200000 in
lemma h93Slice8 : Slice h93R h93G (subcubeFast 4 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h102Bound
set_option maxRecDepth 200000 in
lemma h93Slice7 : Slice h93R h93G (subcubeFast 2 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h51Bound
set_option maxRecDepth 200000 in
lemma h93Slice6 : Slice h93R h93G (subcubeFast 2 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h103Bound
set_option maxRecDepth 200000 in
lemma h93Slice5 : Slice h93R h93G (subcubeFast 1 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h104Bound
set_option maxRecDepth 200000 in
lemma h93Slice4 : Slice h93R h93G (subcubeFast 1 2) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h54Bound
set_option maxRecDepth 200000 in
lemma h93Slice3 : Slice h93R h93G (subcubeFast 1 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h105Bound
set_option maxRecDepth 200000 in
lemma h93Slice2 : Slice h93R h93G (subcubeFast 0 32) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h106Bound
set_option maxRecDepth 200000 in
lemma h93Slice1 : Slice h93R h93G (subcubeFast 0 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h107Bound
set_option maxRecDepth 200000 in
lemma h93Slice0 : Slice h93R h93G (subcubeFast 0 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h55Bound
lemma h93SlicesOk : btAll (sliceSpec h93R h93G) h93Slices := btAll_ofList (P := sliceSpec h93R h93G) (sliceSpecCons h93Slice0 (sliceSpecCons h93Slice1 (sliceSpecCons h93Slice2 (sliceSpecCons h93Slice3 (sliceSpecCons h93Slice4 (sliceSpecCons h93Slice5 (sliceSpecCons h93Slice6 (sliceSpecCons h93Slice7 (sliceSpecCons h93Slice8 (sliceSpecCons h93Slice9 (sliceSpecCons h93Slice10 (sliceSpecCons h93Slice11 (sliceSpecCons h93Slice12 (sliceSpecCons h93Slice13 (sliceSpecCons h93Slice15 (sliceSpecCons h93Slice17 sliceSpecNil))))))))))))))))
set_option maxRecDepth 200000 in
lemma h93PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h93R h93G c) h93Pools := buildPoolsBT_sound h93SlicesOk
def h93Empty : BT (List (List Nat)) := BT.empty
lemma h93EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h93G (4 - 1) xs.toFinset) h93Empty := trivial
def h93Block4_0 : List NodeSpec := priorityNodes 6 [(6828117,1,2),(7083061,1,2),(19984469,1,2),(1512207,1,2),(74783,1,2),(2036495,1,2),(4330255,1,2),(97311,1,2),(17868823,1,2),(19965975,1,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h93Test4_0 : checkNodesBT h93W h93G h93Mask h93Pools h93Autos h93Empty 4 h93Block4_0 = true := by decide +kernel
def h93Nodes4 : List NodeSpec := h93Block4_0
lemma h93Check4 : checkNodesBT h93W h93G h93Mask h93Pools h93Autos h93Empty 4 h93Nodes4 = true := h93Test4_0
def h93Bucket4 : BT (List (List Nat)) := buildBucketsBT h93W h93Nodes4
set_option maxRecDepth 200000 in
lemma h93Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h93G 4 xs.toFinset) h93Bucket4 := buildBucketsBT_sound (by decide) h93Pairs h93WOk h93PoolsOk h93AutosOk h93EmptyOk h93Check4
def h93Block5_0 : List NodeSpec := priorityNodes 6 [(135413,18370819,2),(3802655,19963979,2),(64575,20497219,2),(258293,72,2),(2893871,328653,2),(3280415,4875,2),(548959,21832456,2),(149567,320256,2),(2373679,67,2),(3019295,1,2),(935983,1,2),(2758175,1,2),(153663,64,2),(686127,21024832,2),(948271,328527,2),(2390063,1,2),(2914351,1,2),(27788331,5959,2),(12324383,76,2),(194623,5004,2),(45103151,71,2),(11801119,1,2),(11277855,6087,2),(198719,1,2),(218143,76,2),(676895,1,2),(939039,1,2),(2380831,5831,2),(182335,295364,2),(215103,1,2),(239679,1,2),(55055477,65,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h93Test5_0 : checkNodesBT h93W h93G h93Mask h93Pools h93Autos h93Bucket4 5 h93Block5_0 = true := by decide +kernel
def h93Block5_1 : List NodeSpec := priorityNodes 6 [(528447,1,2),(260159,1,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h93Test5_1 : checkNodesBT h93W h93G h93Mask h93Pools h93Autos h93Bucket4 5 h93Block5_1 = true := by decide +kernel
def h93Nodes5 : List NodeSpec := h93Block5_0 ++ h93Block5_1
lemma h93Check5 : checkNodesBT h93W h93G h93Mask h93Pools h93Autos h93Bucket4 5 h93Nodes5 = true := by
  unfold h93Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h93Test5_0,h93Test5_1⟩
def h93Bucket5 : BT (List (List Nat)) := buildBucketsBT h93W h93Nodes5
set_option maxRecDepth 200000 in
lemma h93Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h93G 5 xs.toFinset) h93Bucket5 := buildBucketsBT_sound (by decide) h93Pairs h93WOk h93PoolsOk h93AutosOk h93Bucket4Ok h93Check5
def h93Block6_0 : List NodeSpec := priorityNodes 6 [(31871,321614751731968,6),(71807,356728240083456,2),(75903,344341,2),(79999,1444954117,2),(88151,17039895,2),(92247,17039640,2),(96303,266256,2),(48191,1209062400,6),(120879,17039705,2),(32287,4171,2),(221547,1546913671,2),(270527,23925255,6),(286911,344341,2),(303295,1443893767,2),(165951,1311801626,6),(87071,4890,6),(170047,91,2),(270783,5444,2),(287167,4608,2),(211007,1209139648,2),(508223,5761,2),(219199,401690,2),(223295,99,2),(115743,369163,2),(41022,1703956995,2),(492095,18981121,2),(137279,108686262741,2),(487531,27029824,2),(495723,18088040,2),(128031,368971,2),(84543,6949375852545,6),(1903167,4954,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h93Test6_0 : checkNodesBT h93W h93G h93Mask h93Pools h93Autos h93Bucket5 6 h93Block6_0 = true := by decide +kernel
def h93Block6_1 : List NodeSpec := priorityNodes 6 [(231487,105,2),(235583,105,2),(32830,105,2),(256063,1695824538,2),(272415,5781,2),(536639,107,2),(544831,20496469,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h93Test6_1 : checkNodesBT h93W h93G h93Mask h93Pools h93Autos h93Bucket5 6 h93Block6_1 = true := by decide +kernel
def h93Nodes6 : List NodeSpec := h93Block6_0 ++ h93Block6_1
lemma h93Check6 : checkNodesBT h93W h93G h93Mask h93Pools h93Autos h93Bucket5 6 h93Nodes6 = true := by
  unfold h93Nodes6 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h93Test6_0,h93Test6_1⟩
def h93Bucket6 : BT (List (List Nat)) := buildBucketsBT h93W h93Nodes6
set_option maxRecDepth 200000 in
lemma h93Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h93G 6 xs.toFinset) h93Bucket6 := buildBucketsBT_sound (by decide) h93Pairs h93WOk h93PoolsOk h93AutosOk h93Bucket5Ok h93Check6
def h93Block7_0 : List NodeSpec := priorityNodes 6 [(126,77394354251,2),(190,1209288410,6),(318,1209287115,6),(574,268378,6),(1086,18194699,2),(2110,1124480661,2),(4158,20554453,2),(8254,17127078,6),(9791,83887235403,6),(32830,108515464853,6),(65598,17933643,2),(12863,23679262,6),(13887,439957,2),(14911,264085,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h93Test7_0 : checkNodesBT h93W h93G h93Mask h93Pools h93Autos h93Bucket6 7 h93Block7_0 = true := by decide +kernel
def h93Nodes7 : List NodeSpec := h93Block7_0
lemma h93Check7 : checkNodesBT h93W h93G h93Mask h93Pools h93Autos h93Bucket6 7 h93Nodes7 = true := h93Test7_0
def h93Bucket7 : BT (List (List Nat)) := buildBucketsBT h93W h93Nodes7
set_option maxRecDepth 200000 in
lemma h93Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h93G 7 xs.toFinset) h93Bucket7 := buildBucketsBT_sound (by decide) h93Pairs h93WOk h93PoolsOk h93AutosOk h93Bucket6Ok h93Check7
def h93Block8_0 : List NodeSpec := priorityNodes 6 [(62,78,6)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h93Test8_0 : checkNodesBT h93W h93G h93Mask h93Pools h93Autos h93Bucket7 8 h93Block8_0 = true := by decide +kernel
def h93Nodes8 : List NodeSpec := h93Block8_0
lemma h93Check8 : checkNodesBT h93W h93G h93Mask h93Pools h93Autos h93Bucket7 8 h93Nodes8 = true := h93Test8_0
def h93Bucket8 : BT (List (List Nat)) := buildBucketsBT h93W h93Nodes8
set_option maxRecDepth 200000 in
lemma h93Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h93G 8 xs.toFinset) h93Bucket8 := buildBucketsBT_sound (by decide) h93Pairs h93WOk h93PoolsOk h93AutosOk h93Bucket7Ok h93Check8
set_option maxRecDepth 200000 in
lemma h93Bound : Lower h93R h93G 9 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,16,20),(VAR 4,1,17),(VAR 5,5,37)]) (by decide +kernel) h93Bucket8Ok (by decide +kernel)
def h108R : List Nat := varsOf 59
def h108G : Nat := 0xffeeee88ffcc8888ffeeee88ffcc8888
lemma h108Bound : Lower h108R h108G 9 := carry_of (swaps := [(2,3),(0,1)]) (roots2 := h93R) (T2 := h93G) (by decide +kernel) h93Bound
def h110R : List Nat := varsOf 53
def h110G : Nat := 0xfffffafafafa0000fffffafafafa0000
lemma h110Bound : Lower h110R h110G 5 := carry_of (swaps := [(3,4)]) (roots2 := h17R) (T2 := h17G) (by decide +kernel) h17Bound
def h111R : List Nat := varsOf 29
def h111G : Nat := 0xfa00a000fa00a000fa00a000fa00a000
lemma h111Bound : Lower h111R h111G 5 := lift_of (z := 0) (o := 8) (essPairs := [(VAR 3,5,13)]) (by decide +kernel) h51Bound
def h112R : List Nat := varsOf 45
def h112G : Nat := 0xfffafffaa000a000fffafffaa000a000
lemma h112Bound : Lower h112R h112G 6 := carry_of (swaps := [(3,4),(4,5),(3,4)]) (roots2 := h18R) (T2 := h18G) (by decide +kernel) h18Bound
def h113R : List Nat := varsOf 57
def h113G : Nat := 0xffffffaaaa000000ffffffaaaa000000
lemma h113Bound : Lower h113R h113G 6 := carry_of (swaps := [(3,4),(4,5),(2,3)]) (roots2 := h18R) (T2 := h18G) (by decide +kernel) h18Bound
def h114R : List Nat := varsOf 60
def h114G : Nat := 0xfffffff0f0000000fffffff0f0000000
lemma h114Bound : Lower h114R h114G 6 := carry_of (swaps := [(3,4),(4,5),(2,3),(0,1),(1,2)]) (roots2 := h18R) (T2 := h18G) (by decide +kernel) h18Bound
def h115R : List Nat := varsOf 53
def h115G : Nat := 0xfffffffffafaa0a0fffffffffafaa0a0
lemma h115Bound : Lower h115R h115G 5 := carry_of (swaps := [(0,1),(1,2),(2,3),(3,4),(4,5),(0,1)]) (roots2 := h39R) (T2 := h39G) (by decide +kernel) h39Bound
def h109R : List Nat := varsOf 61
def h109G : Nat := 0xfffffffafa00a000fffffffafa00a000
def h109Pos : List Nat := [25,28,13,13,28,13,25,25,29,40,33,33,13,48,48,28,44,40,36,25,40,36,41,52,37,48,41,36,49,40,49,13,52,25,40,29,33,48,49,13,33,28,13,13,33,41,56,36,25]
def h109Neg : List Nat := [24,24,9,12,20,5,17,9,21,8,1,32,0,16,32,12,12,32,4,16,12,32,32,20,5,21,9,12,17,9,32,21,32,1,0,24,17,0,1,8,0,21,4,1,5,8,24,5,21]
def h109Mask : Nat := fullMask 49
def h109Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x13ddad5481ded,0x19a52b70005e4),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x8e8989a5913e,0x196008b958138),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x16e8ea45b93ff,0x60882c11828f),(0xffff0000ffff0000ffff0000ffff0000,0x1426b5288e1d3,0x1421892882153),(0xffffffff00000000ffffffff00000000,0xf1757ff76e00,0x140624800)]
def h109Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(1,0,2),(3,0,2),(0,1,2),(3,1,2),(1,2,3),(2,2,3),(1,2,4),(2,2,4),(3,2,4),(0,2,6),(1,2,6),(2,2,6),(3,2,6),(1,3,4),(3,3,4),(1,3,6),(3,3,6),(1,3,9),(3,3,9),(0,4,6),(1,4,6),(2,4,6),(3,4,6),(1,4,9),(3,4,9),(1,1,3),(0,2,33),(1,6,26),(3,3,33),(3,9,33),(3,1,3),(1,1,4),(3,9,39),(1,6,40),(1,1,9),(3,3,42),(3,4,42),(0,6,15),(1,3,17),(1,4,17),(1,3,20),(3,1,23),(0,2,23),(3,4,23),(2,2,24),(1,4,24),(3,6,25),(3,1,31),(1,1,32),(2,2,32),(1,0,3),(0,2,28),(2,2,30),(3,3,58),(0,39,58),(3,1,28),(1,1,59),(3,3,28),(1,3,30),(1,0,4),(3,3,67),(2,2,63),(1,3,63),(1,6,68),(1,2,27),(1,3,27),(3,0,4),(3,0,12),(2,12,24),(0,6,12),(2,6,13),(1,0,19),(1,4,19),(1,0,16),(3,1,81),(1,16,17),(3,3,41),(2,6,16),(3,0,18),(3,1,18),(3,17,18),(1,5,76),(0,6,21),(3,6,21),(1,0,22),(2,6,22),(3,0,23),(3,0,28),(3,27,28),(1,1,95),(1,0,29),(1,3,87),(3,3,97)]
def h109W : BT Decor := buildWiresBT 7 h109Base h109Steps
def h109AutoList : List (List (Nat × Nat)) := [[],[(2,4)],[(0,2)],[(0,4)],[(2,4),(0,2)],[(2,4),(0,4)]]
def h109Autos : BT (List (Nat × Nat)) := btOfList 3 h109AutoList
lemma h109Pairs : goodPairs h109G h109Pos h109Neg := goodPairs_of (by decide +kernel)
lemma h109BaseOk : ∀ x ∈ h109Base, faithful h109Pos h109Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma h109WOk : btAll (fun x => faithful h109Pos h109Neg x ∧ x.1 < 2^128) h109W := buildWiresBT_faithful h109BaseOk
lemma h109AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h109G = h109G) h109Autos := btAll_ofList (autos_of (by decide +kernel))
def h109SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 8,5),some (subcubeFast 1 0,6),some (subcubeFast 4 0,6),some (subcubeFast 16 0,6),some (subcubeFast 32 0,5),some (subcubeFast 32 8,4),some (0xaa55aa55aa55aa55aa55aa55aa55aa55,5),some (0xf00ff00ff00ff00ff00ff00ff00ff00f,5),some (0xff0000ffff0000ffff0000ffff0000ff,5),some (0x55555555aaaaaaaa55555555aaaaaaaa,5),some (0xf0f0f0ff0f0f0f00f0f0f0ff0f0f0f0,5),some (0xff00ffff00ff0000ff00ffff00ff00,7),some (0xffffffff00000000ffffffff0000,5)]
def h109Slices : BT (Option (Nat × Nat)) := btOfList 4 h109SliceList
def h109Specs : List PoolSpec := poolSteps h109Steps [(1,[]),(2,[]),(2,[4]),(11,[1,4]),(0,[]),(2,[4,20]),(4,[4]),(2,[53]),(3,[]),(1,[28]),(3,[1]),(2,[62]),(0,[62]),(0,[27]),(4,[]),(2,[62,63]),(1,[7]),(6,[]),(1,[8]),(8,[]),(1,[21,30]),(1,[8,73]),(11,[1]),(1,[10]),(5,[]),(1,[11]),(1,[12]),(2,[12]),(11,[1,12]),(12,[]),(1,[12,13]),(1,[13]),(1,[14]),(2,[14]),(11,[1,14]),(1,[15]),(1,[15,43]),(1,[16]),(1,[16,85]),(9,[]),(1,[16,86]),(1,[17]),(1,[18]),(2,[18]),(1,[19]),(2,[19]),(1,[22]),(1,[22,67]),(1,[22,68]),(1,[23]),(2,[23]),(1,[23,54]),(2,[23,54]),(1,[23,60]),(1,[24]),(1,[25]),(2,[25]),(2,[3]),(3,[3]),(2,[13]),(7,[]),(3,[4]),(10,[]),(1,[37]),(3,[4,37]),(11,[4,37]),(11,[4]),(0,[26]),(1,[26]),(1,[27]),(3,[62]),(2,[69]),(3,[69]),(11,[]),(2,[10]),(3,[10]),(2,[11]),(3,[11])]
def h109Pools : BT (Option BoundPool) := buildPoolsBT 7 h109W h109R h109Slices h109Specs
set_option maxRecDepth 200000 in
lemma h109Slice12 : Slice h109R h109G (0xffffffff00000000ffffffff0000) 5 := opposite_slice (oppositeRow 4 5 45) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h17Bound
set_option maxRecDepth 200000 in
lemma h109Slice11 : Slice h109R h109G (0xff00ffff00ff0000ff00ffff00ff00) 7 := opposite_slice (oppositeRow 3 5 53) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h49Bound
set_option maxRecDepth 200000 in
lemma h109Slice10 : Slice h109R h109G (0xf0f0f0ff0f0f0f00f0f0f0ff0f0f0f0) 5 := opposite_slice (oppositeRow 2 5 57) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h63Bound
set_option maxRecDepth 200000 in
lemma h109Slice9 : Slice h109R h109G (0x55555555aaaaaaaa55555555aaaaaaaa) 5 := opposite_slice (oppositeRow 0 5 60) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h89Bound
set_option maxRecDepth 200000 in
lemma h109Slice8 : Slice h109R h109G (0xff0000ffff0000ffff0000ffff0000ff) 5 := mapped_slice (identifyRow 3 4 53) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h110Bound
set_option maxRecDepth 200000 in
lemma h109Slice7 : Slice h109R h109G (0xf00ff00ff00ff00ff00ff00ff00ff00f) 5 := mapped_slice (identifyRow 2 3 57) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h63Bound
set_option maxRecDepth 200000 in
lemma h109Slice6 : Slice h109R h109G (0xaa55aa55aa55aa55aa55aa55aa55aa55) 5 := mapped_slice (identifyRow 0 3 60) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h89Bound
set_option maxRecDepth 200000 in
lemma h109Slice5 : Slice h109R h109G (subcubeFast 32 8) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h51Bound
set_option maxRecDepth 200000 in
lemma h109Slice4 : Slice h109R h109G (subcubeFast 32 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h111Bound
set_option maxRecDepth 200000 in
lemma h109Slice3 : Slice h109R h109G (subcubeFast 16 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h112Bound
set_option maxRecDepth 200000 in
lemma h109Slice2 : Slice h109R h109G (subcubeFast 4 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h113Bound
set_option maxRecDepth 200000 in
lemma h109Slice1 : Slice h109R h109G (subcubeFast 1 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h114Bound
set_option maxRecDepth 200000 in
lemma h109Slice0 : Slice h109R h109G (subcubeFast 0 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h115Bound
lemma h109SlicesOk : btAll (sliceSpec h109R h109G) h109Slices := btAll_ofList (P := sliceSpec h109R h109G) (sliceSpecCons h109Slice0 (sliceSpecCons h109Slice1 (sliceSpecCons h109Slice2 (sliceSpecCons h109Slice3 (sliceSpecCons h109Slice4 (sliceSpecCons h109Slice5 (sliceSpecCons h109Slice6 (sliceSpecCons h109Slice7 (sliceSpecCons h109Slice8 (sliceSpecCons h109Slice9 (sliceSpecCons h109Slice10 (sliceSpecCons h109Slice11 (sliceSpecCons h109Slice12 sliceSpecNil)))))))))))))
set_option maxRecDepth 200000 in
lemma h109PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h109R h109G c) h109Pools := buildPoolsBT_sound h109SlicesOk
def h109Empty : BT (List (List Nat)) := BT.empty
lemma h109EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h109G (3 - 1) xs.toFinset) h109Empty := trivial
def h109Block3_0 : List NodeSpec := priorityNodes 7 [(60320793,1,2),(10944813,1,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h109Test3_0 : checkNodesBT h109W h109G h109Mask h109Pools h109Autos h109Empty 3 h109Block3_0 = true := by decide +kernel
def h109Nodes3 : List NodeSpec := h109Block3_0
lemma h109Check3 : checkNodesBT h109W h109G h109Mask h109Pools h109Autos h109Empty 3 h109Nodes3 = true := h109Test3_0
def h109Bucket3 : BT (List (List Nat)) := buildBucketsBT h109W h109Nodes3
set_option maxRecDepth 200000 in
lemma h109Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h109G 3 xs.toFinset) h109Bucket3 := buildBucketsBT_sound (by decide) h109Pairs h109WOk h109PoolsOk h109AutosOk h109EmptyOk h109Check3
def h109Block4_0 : List NodeSpec := priorityNodes 7 [(6691145,1,2),(31605037,129,2),(516285,129,2),(1130685,1,2),(6845377581,1,2),(1712097325,136,2),(428255277,1,2),(1851581,128,2),(1941669,1,2),(99619145,1,2),(32247351,1,2),(1302615,1,2),(1318959,1,2),(1384535,1,2),(32770615,1,2),(118490167,1,2),(4620717,1,2),(383007,1,2),(5943349293,1,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h109Test4_0 : checkNodesBT h109W h109G h109Mask h109Pools h109Autos h109Bucket3 4 h109Block4_0 = true := by decide +kernel
def h109Nodes4 : List NodeSpec := h109Block4_0
lemma h109Check4 : checkNodesBT h109W h109G h109Mask h109Pools h109Autos h109Bucket3 4 h109Nodes4 = true := h109Test4_0
def h109Bucket4 : BT (List (List Nat)) := buildBucketsBT h109W h109Nodes4
set_option maxRecDepth 200000 in
lemma h109Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h109G 4 xs.toFinset) h109Bucket4 := buildBucketsBT_sound (by decide) h109Pairs h109WOk h109PoolsOk h109AutosOk h109Bucket3Ok h109Check4
def h109Block5_0 : List NodeSpec := priorityNodes 7 [(5304,16512,2),(3214525,1,2),(4000957,16512,2),(8785085,129,2),(66740,1,2),(263348,1,2),(2098356,1,2),(951925,132,2),(1017461,1,2),(639349,133,2),(672117,129,2),(835957,129,2),(868725,129,2),(428196141,2229383,30),(654360765,1,18),(159760573,16512,2),(43527285,136,66),(63998069,136,2),(59811957,136,2),(956350653,16512,2),(38584509,129,2),(3375477,18049,2),(186660981,142,2),(182470773,1,2),(4096373,143,2),(679567797,1,2),(629285301,1,2),(9109877,129,2),(270390,1,2),(3277871,145,2),(602175,1,2),(206911,18568,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h109Test5_0 : checkNodesBT h109W h109G h109Mask h109Pools h109Autos h109Bucket4 5 h109Block5_0 = true := by decide +kernel
def h109Block5_1 : List NodeSpec := priorityNodes 7 [(278582,136,82),(64575,18952,2),(610367,2162837,82),(597079,142,2),(170047,1,2),(9896309,129,2),(58455,1,2),(153663,17412,2),(667711,1,2),(174143,1,2),(178239,329384081,2),(60503,158,2),(10551669,128,2),(618559,1,2),(13887,1,2),(1187887,1,2),(593983,1,2),(626751,1,2),(9634165,18560,2),(64599,1,2),(9240879,145,2),(2785583,164,2),(708671,2326694,38),(716863,168,2),(11338101,129,2),(665647,167,2),(553023,2738308,2),(733247,1,2),(741439,1,2),(599799925,128,2),(190527,1,2),(194623,1,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h109Test5_1 : checkNodesBT h109W h109G h109Mask h109Pools h109Autos h109Bucket4 5 h109Block5_1 = true := by decide +kernel
def h109Block5_2 : List NodeSpec := priorityNodes 7 [(11600245,128,2),(198719,145,2),(39999,1,2),(202815,167,2),(8716631,175,2),(8847663,176,2),(57887,1,2),(54335,1,2),(749631,1,2),(454743,23091,10),(227391,1,2),(503855,1,2),(251967,1,2),(11731317,128,2),(3506519,179,2),(3899695,181,2),(12124533,128,2),(59935,1,2),(231487,308412544,2),(256063,1,2),(782399,1,2),(45352565,132,2),(3698795,142,2),(149567,1,2),(14425175,1,2),(161855,145,2),(165951,1,2),(34645271,195,2),(211007,1,2),(215103,1,2),(2830453,1,2),(213930091,167,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h109Test5_2 : checkNodesBT h109W h109G h109Mask h109Pools h109Autos h109Bucket4 5 h109Block5_2 = true := by decide +kernel
def h109Block5_3 : List NodeSpec := priorityNodes 7 [(536639,1,2),(544831,167,2),(3310453,141,2),(12454487,145,2),(247871,145,2),(1031802987,1,2),(790591,1,2),(643135,1,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h109Test5_3 : checkNodesBT h109W h109G h109Mask h109Pools h109Autos h109Bucket4 5 h109Block5_3 = true := by decide +kernel
def h109Nodes5 : List NodeSpec := h109Block5_0 ++ h109Block5_1 ++ h109Block5_2 ++ h109Block5_3
lemma h109Check5 : checkNodesBT h109W h109G h109Mask h109Pools h109Autos h109Bucket4 5 h109Nodes5 = true := by
  unfold h109Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨h109Test5_0,h109Test5_1⟩,h109Test5_2⟩,h109Test5_3⟩
def h109Bucket5 : BT (List (List Nat)) := buildBucketsBT h109W h109Nodes5
set_option maxRecDepth 200000 in
lemma h109Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h109G 5 xs.toFinset) h109Bucket5 := buildBucketsBT_sound (by decide) h109Pairs h109WOk h109PoolsOk h109AutosOk h109Bucket4Ok h109Check5
def h109Block6_0 : List NodeSpec := priorityNodes 7 [(1212,35177693186,2),(3441013,2098439,78),(4030837,293830667,14),(8382,285231108,10),(16574,36515629458,90),(65726,304106392,10),(86207,2116740,10),(13887,686752683658650,10),(94399,304152730,10),(524478,2607236,10),(15935,5570105443345,46),(110783,335824132,10),(118975,289472675,10),(127167,285233821,54),(270527,285234318,10),(39999,735061650101514,26),(286911,21770,26),(42047,691149904500234,26),(303295,2119178,54),(352447,40294842542,10),(50239,47884403239,10),(368831,47595226890,10),(385215,2986894,10),(54335,5404964756535,10),(401599,350453943,10),(684095,304225688,58),(5182,394283136,2),(1999679,398475281,2),(157759,850969416966018,22),(4391743,2376194,2),(66614,19352,6),(56383,836629849727512,6)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h109Test6_0 : checkNodesBT h109W h109G h109Mask h109Pools h109Autos h109Bucket5 6 h109Block6_0 = true := by decide +kernel
def h109Block6_1 : List NodeSpec := priorityNodes 7 [(1475391,2375704,2),(58431,36510452753,6),(119552063,398480256,2),(243775,6463405760306,30),(4831295,2737970,2),(219199,6464766869656,6),(22108223,18584,2),(766015,2234520,50),(634943,36515628825,6)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h109Test6_1 : checkNodesBT h109W h109G h109Mask h109Pools h109Autos h109Bucket5 6 h109Block6_1 = true := by decide +kernel
def h109Nodes6 : List NodeSpec := h109Block6_0 ++ h109Block6_1
lemma h109Check6 : checkNodesBT h109W h109G h109Mask h109Pools h109Autos h109Bucket5 6 h109Nodes6 = true := by
  unfold h109Nodes6 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h109Test6_0,h109Test6_1⟩
def h109Bucket6 : BT (List (List Nat)) := buildBucketsBT h109W h109Nodes6
set_option maxRecDepth 200000 in
lemma h109Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h109G 6 xs.toFinset) h109Bucket6 := buildBucketsBT_sound (by decide) h109Pairs h109WOk h109PoolsOk h109AutosOk h109Bucket5Ok h109Check6
def h109Block7_0 : List NodeSpec := priorityNodes 7 [(190,5157727404160,10),(574,391004184,22),(1086,6670480605208,22),(260159,44975702040,94),(577599,420593688,22),(65598,426937240,30),(12863,55189063428,30)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h109Test7_0 : checkNodesBT h109W h109G h109Mask h109Pools h109Autos h109Bucket6 7 h109Block7_0 = true := by decide +kernel
def h109Nodes7 : List NodeSpec := h109Block7_0
lemma h109Check7 : checkNodesBT h109W h109G h109Mask h109Pools h109Autos h109Bucket6 7 h109Nodes7 = true := h109Test7_0
def h109Bucket7 : BT (List (List Nat)) := buildBucketsBT h109W h109Nodes7
set_option maxRecDepth 200000 in
lemma h109Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h109G 7 xs.toFinset) h109Bucket7 := buildBucketsBT_sound (by decide) h109Pairs h109WOk h109PoolsOk h109AutosOk h109Bucket6Ok h109Check7
def h109Block8_0 : List NodeSpec := priorityNodes 7 [(62,421658752,30)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h109Test8_0 : checkNodesBT h109W h109G h109Mask h109Pools h109Autos h109Bucket7 8 h109Block8_0 = true := by decide +kernel
def h109Nodes8 : List NodeSpec := h109Block8_0
lemma h109Check8 : checkNodesBT h109W h109G h109Mask h109Pools h109Autos h109Bucket7 8 h109Nodes8 = true := h109Test8_0
def h109Bucket8 : BT (List (List Nat)) := buildBucketsBT h109W h109Nodes8
set_option maxRecDepth 200000 in
lemma h109Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h109G 8 xs.toFinset) h109Bucket8 := buildBucketsBT_sound (by decide) h109Pairs h109WOk h109PoolsOk h109AutosOk h109Bucket7Ok h109Check8
set_option maxRecDepth 200000 in
lemma h109Bound : Lower h109R h109G 9 := lower_of_forestBT (essPairs := [(VAR 0,12,13),(VAR 2,9,13),(VAR 3,5,13),(VAR 4,9,25),(VAR 5,1,33)]) (by decide +kernel) h109Bucket8Ok (by decide +kernel)
def h116R : List Nat := varsOf 61
def h116G : Nat := 0xfafafaf0faf0f0a0fafafaf0faf0f0a0
lemma h116Bound : Lower h116R h116G 9 := carry_of (swaps := [(4,5),(2,3),(3,4),(0,1),(1,2),(2,3),(0,1)]) (roots2 := h109R) (T2 := h109G) (by decide +kernel) h109Bound
def h117R : List Nat := varsOf 62
def h117G : Nat := 0xfffffffcf0c0c000fffffffcf0c0c000
lemma h117Bound : Lower h117R h117G 9 := carry_of (swaps := [(2,3),(0,1)]) (roots2 := h109R) (T2 := h109G) (by decide +kernel) h109Bound
def h118R : List Nat := varsOf 62
def h118G : Nat := 0xffccffc0ffc0fc00ffccffc0ffc0fc00
lemma h118Bound : Lower h118R h118G 9 := carry_of (swaps := [(4,5),(2,3),(3,4),(0,1),(1,2)]) (roots2 := h109R) (T2 := h109G) (by decide +kernel) h109Bound
def h119R : List Nat := varsOf 15
def h119G : Nat := 0xe888e888e888e888e888e888e888e888
lemma h119Bound : Lower h119R h119G 5 := carry_of (swaps := [(4,5),(3,4)]) (roots2 := h100R) (T2 := h100G) (by decide +kernel) h100Bound
def h120R : List Nat := varsOf 26
def h120G : Nat := 0xffcccc00ffcccc00ffcccc00ffcccc00
lemma h120Bound : Lower h120R h120G 4 := carry_of (swaps := [(4,5),(1,2)]) (roots2 := h3R) (T2 := h3G) (by decide +kernel) h3Bound
def h121R : List Nat := varsOf 30
def h121G : Nat := 0xf0c0c000f0c0c000f0c0c000f0c0c000
lemma h121Bound : Lower h121R h121G 5 := carry_of (swaps := [(2,3),(0,1)]) (roots2 := h111R) (T2 := h111G) (by decide +kernel) h111Bound
def h122R : List Nat := varsOf 23
def h122G : Nat := 0xfafae8e8fafae8e8fafae8e8fafae8e8
lemma h122Bound : Lower h122R h122G 5 := carry_of (swaps := [(4,5),(2,3),(3,4),(1,2),(2,3),(0,1)]) (roots2 := h17R) (T2 := h17G) (by decide +kernel) h17Bound
def h123R : List Nat := varsOf 27
def h123G : Nat := 0xffccee88ffccee88ffccee88ffccee88
lemma h123Bound : Lower h123R h123G 5 := carry_of (swaps := [(4,5),(2,3),(3,4),(1,2)]) (roots2 := h17R) (T2 := h17G) (by decide +kernel) h17Bound
def h125R : List Nat := varsOf 29
def h125G : Nat := 0xfaf0f0a0faf0f0a0faf0f0a0faf0f0a0
lemma h125Bound : Lower h125R h125G 6 := carry_of (swaps := [(4,5),(2,3)]) (roots2 := h18R) (T2 := h18G) (by decide +kernel) h18Bound
def h126R : List Nat := varsOf 30
def h126G : Nat := 0xffc0fc00ffc0fc00ffc0fc00ffc0fc00
lemma h126Bound : Lower h126R h126G 6 := carry_of (swaps := [(4,5),(0,1)]) (roots2 := h18R) (T2 := h18G) (by decide +kernel) h18Bound
def h124R : List Nat := varsOf 31
def h124G : Nat := 0xfac8e888fac8e888fac8e888fac8e888
def h124Pos : List Nat := [13,14,3,3,22,14,7,13,14,11,13,22,19,25,7,11,19,22,25,28,28,28,25,3,22]
def h124Neg : List Nat := [12,12,1,2,21,10,6,9,6,10,5,6,18,9,5,9,17,18,17,24,20,12,24,18,26]
def h124Mask : Nat := fullMask 25
def h124Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xc5f6cd,0x5e494),(0xcccccccccccccccccccccccccccccccc,0x183db7e,0x1821b68),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x13a4df3,0x304d53),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x7ca7a3,0x168a2a3),(0xffff0000ffff0000ffff0000ffff0000,0x17f3810,0x1df1010)]
def h124Steps : List (Nat × Nat × Nat) := [(1,0,1),(1,0,4),(1,1,4),(0,2,3),(3,4,5),(3,1,6)]
def h124W : BT Decor := buildWiresBT 4 h124Base h124Steps
def h124AutoList : List (List (Nat × Nat)) := [[],[(2,3),(0,1)]]
def h124Autos : BT (List (Nat × Nat)) := btOfList 1 h124AutoList
lemma h124Pairs : goodPairs h124G h124Pos h124Neg := goodPairs_of (by decide +kernel)
lemma h124BaseOk : ∀ x ∈ h124Base, faithful h124Pos h124Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma h124WOk : btAll (fun x => faithful h124Pos h124Neg x ∧ x.1 < 2^128) h124W := buildWiresBT_faithful h124BaseOk
lemma h124AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h124G = h124G) h124Autos := btAll_ofList (autos_of (by decide +kernel))
def h124SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 4,5),some (subcubeFast 0 8,5),some (subcubeFast 1 0,5),some (subcubeFast 1 4,4),some (subcubeFast 2 0,5),some (subcubeFast 2 8,4),some (subcubeFast 16 0,5),some (subcubeFast 16 4,4),some (subcubeFast 16 8,4),some (0xaa55aa55aa55aa55aa55aa55aa55aa55,6),some (0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3,6),some (0x66666666666666666666666666666666,5)]
def h124Slices : BT (Option (Nat × Nat)) := btOfList 4 h124SliceList
def h124Specs : List PoolSpec := [(2,[]),(4,[]),(10,[]),(0,[]),(9,[]),(1,[]),(6,[]),(11,[]),(3,[]),(8,[]),(5,[]),(7,[])]
def h124Pools : BT (Option BoundPool) := buildPoolsBT 4 h124W h124R h124Slices h124Specs
set_option maxRecDepth 200000 in
lemma h124Slice11 : Slice h124R h124G (0x66666666666666666666666666666666) 5 := opposite_slice (oppositeRow 0 1 30) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h86Bound
set_option maxRecDepth 200000 in
lemma h124Slice10 : Slice h124R h124G (0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3) 6 := mapped_slice (identifyRow 1 2 29) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h125Bound
set_option maxRecDepth 200000 in
lemma h124Slice9 : Slice h124R h124G (0xaa55aa55aa55aa55aa55aa55aa55aa55) 6 := mapped_slice (identifyRow 0 3 30) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h126Bound
set_option maxRecDepth 200000 in
lemma h124Slice8 : Slice h124R h124G (subcubeFast 16 8) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h23Bound
set_option maxRecDepth 200000 in
lemma h124Slice7 : Slice h124R h124G (subcubeFast 16 4) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h25Bound
set_option maxRecDepth 200000 in
lemma h124Slice6 : Slice h124R h124G (subcubeFast 16 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h119Bound
set_option maxRecDepth 200000 in
lemma h124Slice5 : Slice h124R h124G (subcubeFast 2 8) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h51Bound
set_option maxRecDepth 200000 in
lemma h124Slice4 : Slice h124R h124G (subcubeFast 2 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h111Bound
set_option maxRecDepth 200000 in
lemma h124Slice3 : Slice h124R h124G (subcubeFast 1 4) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h120Bound
set_option maxRecDepth 200000 in
lemma h124Slice2 : Slice h124R h124G (subcubeFast 1 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h121Bound
set_option maxRecDepth 200000 in
lemma h124Slice1 : Slice h124R h124G (subcubeFast 0 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h122Bound
set_option maxRecDepth 200000 in
lemma h124Slice0 : Slice h124R h124G (subcubeFast 0 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h123Bound
lemma h124SlicesOk : btAll (sliceSpec h124R h124G) h124Slices := btAll_ofList (P := sliceSpec h124R h124G) (sliceSpecCons h124Slice0 (sliceSpecCons h124Slice1 (sliceSpecCons h124Slice2 (sliceSpecCons h124Slice3 (sliceSpecCons h124Slice4 (sliceSpecCons h124Slice5 (sliceSpecCons h124Slice6 (sliceSpecCons h124Slice7 (sliceSpecCons h124Slice8 (sliceSpecCons h124Slice9 (sliceSpecCons h124Slice10 (sliceSpecCons h124Slice11 sliceSpecNil))))))))))))
set_option maxRecDepth 200000 in
lemma h124PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h124R h124G c) h124Pools := buildPoolsBT_sound h124SlicesOk
def h124Empty : BT (List (List Nat)) := BT.empty
lemma h124EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h124G (5 - 1) xs.toFinset) h124Empty := trivial
def h124Block5_0 : List NodeSpec := priorityNodes 4 [(1086,1,2),(414,272,2),(2110,1,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h124Test5_0 : checkNodesBT h124W h124G h124Mask h124Pools h124Autos h124Empty 5 h124Block5_0 = true := by decide +kernel
def h124Nodes5 : List NodeSpec := h124Block5_0
lemma h124Check5 : checkNodesBT h124W h124G h124Mask h124Pools h124Autos h124Empty 5 h124Nodes5 = true := h124Test5_0
def h124Bucket5 : BT (List (List Nat)) := buildBucketsBT h124W h124Nodes5
set_option maxRecDepth 200000 in
lemma h124Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h124G 5 xs.toFinset) h124Bucket5 := buildBucketsBT_sound (by decide) h124Pairs h124WOk h124PoolsOk h124AutosOk h124EmptyOk h124Check5
def h124Block6_0 : List NodeSpec := priorityNodes 4 [(126,374616583,2),(190,94616,2),(574,7080,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h124Test6_0 : checkNodesBT h124W h124G h124Mask h124Pools h124Autos h124Bucket5 6 h124Block6_0 = true := by decide +kernel
def h124Nodes6 : List NodeSpec := h124Block6_0
lemma h124Check6 : checkNodesBT h124W h124G h124Mask h124Pools h124Autos h124Bucket5 6 h124Nodes6 = true := h124Test6_0
def h124Bucket6 : BT (List (List Nat)) := buildBucketsBT h124W h124Nodes6
set_option maxRecDepth 200000 in
lemma h124Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h124G 6 xs.toFinset) h124Bucket6 := buildBucketsBT_sound (by decide) h124Pairs h124WOk h124PoolsOk h124AutosOk h124Bucket5Ok h124Check6
def h124Block7_0 : List NodeSpec := priorityNodes 4 [(62,28584600,6)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h124Test7_0 : checkNodesBT h124W h124G h124Mask h124Pools h124Autos h124Bucket6 7 h124Block7_0 = true := by decide +kernel
def h124Nodes7 : List NodeSpec := h124Block7_0
lemma h124Check7 : checkNodesBT h124W h124G h124Mask h124Pools h124Autos h124Bucket6 7 h124Nodes7 = true := h124Test7_0
def h124Bucket7 : BT (List (List Nat)) := buildBucketsBT h124W h124Nodes7
set_option maxRecDepth 200000 in
lemma h124Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h124G 7 xs.toFinset) h124Bucket7 := buildBucketsBT_sound (by decide) h124Pairs h124WOk h124PoolsOk h124AutosOk h124Bucket6Ok h124Check7
set_option maxRecDepth 200000 in
lemma h124Bound : Lower h124R h124G 8 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,9,13),(VAR 3,5,13),(VAR 4,6,22)]) (by decide +kernel) h124Bucket7Ok (by decide +kernel)
def h127R : List Nat := varsOf 43
def h127G : Nat := 0xee88ee8888888888ee88ee8888888888
lemma h127Bound : Lower h127R h127G 5 := carry_of (swaps := [(2,3)]) (roots2 := h100R) (T2 := h100G) (by decide +kernel) h100Bound
def h128R : List Nat := varsOf 45
def h128G : Nat := 0xaaa0aaa0a000a000aaa0aaa0a000a000
lemma h128Bound : Lower h128R h128G 5 := carry_of (swaps := [(4,5),(2,3),(0,1),(1,2),(0,1)]) (roots2 := h111R) (T2 := h111G) (by decide +kernel) h111Bound
def h129R : List Nat := varsOf 46
def h129G : Nat := 0xccc0ccc0c000c000ccc0ccc0c000c000
lemma h129Bound : Lower h129R h129G 5 := carry_of (swaps := [(4,5),(2,3),(0,1),(1,2)]) (roots2 := h111R) (T2 := h111G) (by decide +kernel) h111Bound
def h130R : List Nat := varsOf 39
def h130G : Nat := 0xeeeeeeeee8e8e8e8eeeeeeeee8e8e8e8
lemma h130Bound : Lower h130R h130G 5 := carry_of (swaps := [(2,3),(3,4),(4,5),(3,4),(1,2),(2,3),(0,1),(1,2)]) (roots2 := h17R) (T2 := h17G) (by decide +kernel) h17Bound
def h131R : List Nat := varsOf 43
def h131G : Nat := 0xeeeeeeeeee88ee88eeeeeeeeee88ee88
lemma h131Bound : Lower h131R h131G 5 := carry_of (swaps := [(2,3),(3,4),(4,5),(3,4),(0,1),(1,2),(2,3),(0,1),(1,2)]) (roots2 := h17R) (T2 := h17G) (by decide +kernel) h17Bound
def h132R : List Nat := varsOf 46
def h132G : Nat := 0xfffcfffcfcccfcccfffcfffcfcccfccc
lemma h132Bound : Lower h132R h132G 5 := carry_of (swaps := [(0,1)]) (roots2 := h39R) (T2 := h39G) (by decide +kernel) h39Bound
def h133R : List Nat := varsOf 47
def h133G : Nat := 0xeee8eee8e888e888eee8eee8e888e888
def h133Pos : List Nat := [13,14,3,3,14,13,14,13,38,35,37,35,37,41,41]
def h133Neg : List Nat := [12,12,1,2,10,9,6,5,6,34,5,33,33,33,9]
def h133Mask : Nat := fullMask 15
def h133Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x7ead,0x7ca4),(0xcccccccccccccccccccccccccccccccc,2910,856),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,5619,1475),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x60f3,0x4033),(0xffffffff00000000ffffffff00000000,0x7f00,0x3a00)]
def h133Steps : List (Nat × Nat × Nat) := []
def h133W : BT Decor := buildWiresBT 3 h133Base h133Steps
def h133AutoList : List (List (Nat × Nat)) := [[],[(3,5)],[(2,3)],[(2,5)],[(0,1)],[(3,5),(2,3)],[(3,5),(2,5)],[(3,5),(0,1)],[(2,3),(0,1)],[(2,5),(0,1)],[(3,5),(2,3),(0,1)],[(3,5),(2,5),(0,1)]]
def h133Autos : BT (List (Nat × Nat)) := btOfList 4 h133AutoList
lemma h133Pairs : goodPairs h133G h133Pos h133Neg := goodPairs_of (by decide +kernel)
lemma h133BaseOk : ∀ x ∈ h133Base, faithful h133Pos h133Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma h133WOk : btAll (fun x => faithful h133Pos h133Neg x ∧ x.1 < 2^128) h133W := buildWiresBT_faithful h133BaseOk
lemma h133AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h133G = h133G) h133Autos := btAll_ofList (autos_of (by decide +kernel))
def h133SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,5),some (subcubeFast 0 2,5),some (subcubeFast 0 4,5),some (subcubeFast 0 8,5),some (subcubeFast 1 0,5),some (subcubeFast 2 0,5),some (subcubeFast 4 0,5),some (subcubeFast 8 0,5)]
def h133Slices : BT (Option (Nat × Nat)) := btOfList 3 h133SliceList
def h133Specs : List PoolSpec := [(4,[]),(0,[]),(5,[]),(1,[]),(6,[]),(2,[]),(7,[]),(3,[])]
def h133Pools : BT (Option BoundPool) := buildPoolsBT 3 h133W h133R h133Slices h133Specs
set_option maxRecDepth 200000 in
lemma h133Slice7 : Slice h133R h133G (subcubeFast 8 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h100Bound
set_option maxRecDepth 200000 in
lemma h133Slice6 : Slice h133R h133G (subcubeFast 4 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h127Bound
set_option maxRecDepth 200000 in
lemma h133Slice5 : Slice h133R h133G (subcubeFast 2 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h128Bound
set_option maxRecDepth 200000 in
lemma h133Slice4 : Slice h133R h133G (subcubeFast 1 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h129Bound
set_option maxRecDepth 200000 in
lemma h133Slice3 : Slice h133R h133G (subcubeFast 0 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h130Bound
set_option maxRecDepth 200000 in
lemma h133Slice2 : Slice h133R h133G (subcubeFast 0 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h131Bound
set_option maxRecDepth 200000 in
lemma h133Slice1 : Slice h133R h133G (subcubeFast 0 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h39Bound
set_option maxRecDepth 200000 in
lemma h133Slice0 : Slice h133R h133G (subcubeFast 0 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h132Bound
lemma h133SlicesOk : btAll (sliceSpec h133R h133G) h133Slices := btAll_ofList (P := sliceSpec h133R h133G) (sliceSpecCons h133Slice0 (sliceSpecCons h133Slice1 (sliceSpecCons h133Slice2 (sliceSpecCons h133Slice3 (sliceSpecCons h133Slice4 (sliceSpecCons h133Slice5 (sliceSpecCons h133Slice6 (sliceSpecCons h133Slice7 sliceSpecNil))))))))
lemma h133PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h133R h133G c) h133Pools := buildPoolsBT_sound h133SlicesOk
def h133Empty : BT (List (List Nat)) := BT.empty
lemma h133EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h133G (7 - 1) xs.toFinset) h133Empty := trivial
def h133Block7_0 : List NodeSpec := priorityNodes 3 [(62,33212040,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h133Test7_0 : checkNodesBT h133W h133G h133Mask h133Pools h133Autos h133Empty 7 h133Block7_0 = true := by decide +kernel
def h133Nodes7 : List NodeSpec := h133Block7_0
lemma h133Check7 : checkNodesBT h133W h133G h133Mask h133Pools h133Autos h133Empty 7 h133Nodes7 = true := h133Test7_0
def h133Bucket7 : BT (List (List Nat)) := buildBucketsBT h133W h133Nodes7
lemma h133Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h133G 7 xs.toFinset) h133Bucket7 := buildBucketsBT_sound (by decide) h133Pairs h133WOk h133PoolsOk h133AutosOk h133EmptyOk h133Check7
lemma h133Bound : Lower h133R h133G 8 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,9,13),(VAR 3,5,13),(VAR 5,5,37)]) (by decide +kernel) h133Bucket7Ok (by decide +kernel)
def h137R : List Nat := varsOf 51
def h137G : Nat := 0xeeee888888888888eeee888888888888
lemma h137Bound : Lower h137R h137G 5 := carry_of (swaps := [(2,3),(3,4)]) (roots2 := h100R) (T2 := h100G) (by decide +kernel) h100Bound
def h138R : List Nat := varsOf 54
def h138G : Nat := 0xccccc0c0c0c00000ccccc0c0c0c00000
lemma h138Bound : Lower h138R h138G 5 := carry_of (swaps := [(4,5),(2,3),(3,4),(0,1),(1,2)]) (roots2 := h111R) (T2 := h111G) (by decide +kernel) h111Bound
def h139R : List Nat := varsOf 23
def h139G : Nat := 0xeeeee8e8eeeee8e8eeeee8e8eeeee8e8
lemma h139Bound : Lower h139R h139G 5 := carry_of (swaps := [(4,5),(2,3),(3,4),(1,2),(2,3),(0,1),(1,2)]) (roots2 := h17R) (T2 := h17G) (by decide +kernel) h17Bound
def h140R : List Nat := varsOf 51
def h140G : Nat := 0xeeeeeeeecccc8888eeeeeeeecccc8888
lemma h140Bound : Lower h140R h140G 5 := carry_of (swaps := [(2,3),(3,4)]) (roots2 := h14R) (T2 := h14G) (by decide +kernel) h14Bound
def h142R : List Nat := varsOf 53
def h142G : Nat := 0xaaaaa0a0fafaaaaaaaaaa0a0fafaaaaa
lemma h142Bound : Lower h142R h142G 6 := carry_of (swaps := [(4,5),(1,2),(2,3),(0,1)]) (roots2 := h35R) (T2 := h35G) (by decide +kernel) h35Bound
def h144R : List Nat := varsOf 54
def h144G : Nat := 0xfffffcfcc0c00000fffffcfcc0c00000
lemma h144Bound : Lower h144R h144G 6 := carry_of (swaps := [(3,4),(4,5),(0,1)]) (roots2 := h18R) (T2 := h18G) (by decide +kernel) h18Bound
def h141R : List Nat := varsOf 55
def h141G : Nat := 0xeeeee8e8c8c88888eeeee8e8c8c88888
def h141Pos : List Nat := [22,37,3,3,22,37,22,19,49,38,37,35,49]
def h141Neg : List Nat := [20,36,1,2,18,33,6,18,33,6,5,33,17]
def h141Mask : Nat := fullMask 13
def h141Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,7598,7460),(0xcccccccccccccccccccccccccccccccc,2781,728),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,1651,1603),(0xffff0000ffff0000ffff0000ffff0000,4561,4241),(0xffffffff00000000ffffffff00000000,7970,2338)]
def h141Steps : List (Nat × Nat × Nat) := []
def h141W : BT Decor := buildWiresBT 3 h141Base h141Steps
def h141AutoList : List (List (Nat × Nat)) := [[],[(2,4)]]
def h141Autos : BT (List (Nat × Nat)) := btOfList 1 h141AutoList
lemma h141Pairs : goodPairs h141G h141Pos h141Neg := goodPairs_of (by decide +kernel)
lemma h141BaseOk : ∀ x ∈ h141Base, faithful h141Pos h141Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma h141WOk : btAll (fun x => faithful h141Pos h141Neg x ∧ x.1 < 2^128) h141W := buildWiresBT_faithful h141BaseOk
lemma h141AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h141G = h141G) h141Autos := btAll_ofList (autos_of (by decide +kernel))
def h141SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 4,5),some (subcubeFast 0 16,5),some (subcubeFast 0 32,5),some (subcubeFast 1 2,4),some (subcubeFast 4 0,5),some (subcubeFast 16 0,5),some (0xaaaaaaaa55555555aaaaaaaa55555555,6),some (0x33333333cccccccc33333333cccccccc,6)]
def h141Slices : BT (Option (Nat × Nat)) := btOfList 3 h141SliceList
def h141Specs : List PoolSpec := [(3,[]),(0,[]),(4,[]),(1,[]),(5,[]),(2,[]),(6,[]),(7,[])]
def h141Pools : BT (Option BoundPool) := buildPoolsBT 3 h141W h141R h141Slices h141Specs
set_option maxRecDepth 200000 in
lemma h141Slice11 : Slice h141R h141G (0x33333333cccccccc33333333cccccccc) 6 := opposite_slice (oppositeRow 1 5 53) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h142Bound
set_option maxRecDepth 200000 in
lemma h141Slice8 : Slice h141R h141G (0xaaaaaaaa55555555aaaaaaaa55555555) 6 := mapped_slice (identifyRow 0 5 54) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h144Bound
set_option maxRecDepth 200000 in
lemma h141Slice7 : Slice h141R h141G (subcubeFast 16 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h100Bound
set_option maxRecDepth 200000 in
lemma h141Slice6 : Slice h141R h141G (subcubeFast 4 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h137Bound
set_option maxRecDepth 200000 in
lemma h141Slice5 : Slice h141R h141G (subcubeFast 1 2) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h54Bound
set_option maxRecDepth 200000 in
lemma h141Slice3 : Slice h141R h141G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h139Bound
set_option maxRecDepth 200000 in
lemma h141Slice2 : Slice h141R h141G (subcubeFast 0 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h14Bound
set_option maxRecDepth 200000 in
lemma h141Slice1 : Slice h141R h141G (subcubeFast 0 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h140Bound
lemma h141SlicesOk : btAll (sliceSpec h141R h141G) h141Slices := btAll_ofList (P := sliceSpec h141R h141G) (sliceSpecCons h141Slice1 (sliceSpecCons h141Slice2 (sliceSpecCons h141Slice3 (sliceSpecCons h141Slice5 (sliceSpecCons h141Slice6 (sliceSpecCons h141Slice7 (sliceSpecCons h141Slice8 (sliceSpecCons h141Slice11 sliceSpecNil))))))))
lemma h141PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h141R h141G c) h141Pools := buildPoolsBT_sound h141SlicesOk
def h141Empty : BT (List (List Nat)) := BT.empty
lemma h141EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h141G (7 - 1) xs.toFinset) h141Empty := trivial
def h141Block7_0 : List NodeSpec := priorityNodes 3 [(62,33212040,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h141Test7_0 : checkNodesBT h141W h141G h141Mask h141Pools h141Autos h141Empty 7 h141Block7_0 = true := by decide +kernel
def h141Nodes7 : List NodeSpec := h141Block7_0
lemma h141Check7 : checkNodesBT h141W h141G h141Mask h141Pools h141Autos h141Empty 7 h141Nodes7 = true := h141Test7_0
def h141Bucket7 : BT (List (List Nat)) := buildBucketsBT h141W h141Nodes7
lemma h141Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h141G 7 xs.toFinset) h141Bucket7 := buildBucketsBT_sound (by decide) h141Pairs h141WOk h141PoolsOk h141AutosOk h141EmptyOk h141Check7
lemma h141Bound : Lower h141R h141G 8 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,18,22),(VAR 4,6,22),(VAR 5,5,37)]) (by decide +kernel) h141Bucket7Ok (by decide +kernel)
def h145R : List Nat := varsOf 57
def h145G : Nat := 0xaaaaaa00aa000000aaaaaa00aa000000
lemma h145Bound : Lower h145R h145G 5 := carry_of (swaps := [(4,5),(2,3),(3,4),(0,1),(1,2),(2,3),(0,1)]) (roots2 := h111R) (T2 := h111G) (by decide +kernel) h111Bound
def h146R : List Nat := varsOf 27
def h146G : Nat := 0xeeeeee88eeeeee88eeeeee88eeeeee88
lemma h146Bound : Lower h146R h146G 5 := carry_of (swaps := [(4,5),(2,3),(3,4),(0,1),(1,2),(2,3),(0,1),(1,2)]) (roots2 := h17R) (T2 := h17G) (by decide +kernel) h17Bound
def h147R : List Nat := varsOf 51
def h147G : Nat := 0xeeeeeeeeaaaa8888eeeeeeeeaaaa8888
lemma h147Bound : Lower h147R h147G 5 := carry_of (swaps := [(2,3),(3,4),(0,1)]) (roots2 := h14R) (T2 := h14G) (by decide +kernel) h14Bound
def h148R : List Nat := varsOf 58
def h148G : Nat := 0xffffffccffccccccffffffccffcccccc
lemma h148Bound : Lower h148R h148G 5 := carry_of (swaps := [(3,4),(2,3),(0,1)]) (roots2 := h39R) (T2 := h39G) (by decide +kernel) h39Bound
def h149R : List Nat := varsOf 59
def h149G : Nat := 0xeeeeee88aa888888eeeeee88aa888888
lemma h149Bound : Lower h149R h149G 8 := carry_of (swaps := [(2,3),(0,1)]) (roots2 := h141R) (T2 := h141G) (by decide +kernel) h141Bound
def h150R : List Nat := varsOf 29
def h150G : Nat := 0xfaaaaaa0faaaaaa0faaaaaa0faaaaaa0
lemma h150Bound : Lower h150R h150G 6 := carry_of (swaps := [(4,5),(2,3),(0,1),(1,2),(0,1)]) (roots2 := h18R) (T2 := h18G) (by decide +kernel) h18Bound
def h152R : List Nat := varsOf 60
def h152G : Nat := 0xf0ff00f0f0000000f0ff00f0f0000000
lemma h152Bound : Lower h152R h152G 6 := carry_of (swaps := [(2,3)]) (roots2 := h74R) (T2 := h74G) (by decide +kernel) h74Bound
def h153R : List Nat := varsOf 57
def h153G : Nat := 0xffaaaa00ff000000ffaaaa00ff000000
lemma h153Bound : Lower h153R h153G 5 := carry_of (swaps := [(1,2),(2,3),(3,4),(0,1),(1,2),(2,3)]) (roots2 := h100R) (T2 := h100G) (by decide +kernel) h100Bound
def h154R : List Nat := varsOf 57
def h154G : Nat := 0xffaaaa00ff00aa00ffaaaa00ff00aa00
lemma h154Bound : Lower h154R h154G 5 := carry_of (swaps := [(2,3),(3,4),(1,2),(2,3)]) (roots2 := h24R) (T2 := h24G) (by decide +kernel) h24Bound
def h151R : List Nat := varsOf 61
def h151G : Nat := 0xfaaaaaa0fa00a000faaaaaa0fa00a000
def h151Pos : List Nat := [25,28,41,28,49,13,28,41,25,37,13,25,49,41,60,37,49,41,60,13,13,25,13,29,37,37,25,28,60,41,49,53,28,53,45,13,28,37,28,41,13,41,57,49,13,37,28,28,28,53,37,49]
def h151Neg : List Nat := [24,24,44,20,48,5,12,40,9,5,12,17,33,9,52,33,17,33,56,1,9,21,21,21,52,36,1,52,44,1,1,21,44,52,44,8,21,44,16,56,4,32,56,21,44,4,8,0,4,33,1,52]
def h151Mask : Nat := fullMask 52
def h151Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xe3faee7fbbfb5,0x60810e4fbbb20),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x7f17f9bdcc66a,0x939379be0466c),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x1d7dd3cfe6def,0x54ad101425c7),(0xffff0000ffff0000ffff0000ffff0000,0xbcc53dca5595b,0x80cd289e5481b),(0xffffffff00000000ffffffff00000000,0xe2ea6f307f294,0xa16a71b06d094)]
def h151Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(3,0,1),(0,0,2),(1,0,2),(2,0,2),(3,0,2),(0,0,4),(2,0,4),(3,0,4),(0,1,2),(1,1,2),(2,1,2),(3,1,2),(2,0,19),(0,2,3),(1,2,3),(2,2,3),(0,2,4),(1,2,4),(2,2,4),(3,2,4),(2,2,5),(3,3,4),(1,3,5),(0,0,30),(2,0,30),(0,2,30),(0,4,30),(2,4,33),(2,19,30),(2,30,33),(1,3,19),(2,3,19),(2,3,5),(1,5,19),(0,0,41),(0,2,41),(0,1,3),(1,1,3),(2,1,3),(0,1,4),(3,1,4),(0,0,22),(3,1,22),(3,5,22),(1,1,23),(3,3,52),(1,5,23),(2,0,24),(1,1,24),(1,5,24),(0,0,57),(2,0,27),(1,1,27),(0,0,60),(1,5,27),(1,1,29),(1,5,29),(1,1,33),(0,2,6),(1,1,66),(0,4,66),(2,4,66),(3,2,6),(0,3,6),(3,3,6),(0,4,6),(2,6,24),(2,6,27),(1,1,70),(1,1,73),(1,7,19),(2,4,8),(1,8,24),(1,8,27),(0,2,45),(1,3,82),(1,9,13),(1,13,82),(3,2,45),(3,9,45),(1,13,45),(3,13,45),(1,4,82),(2,4,82),(0,4,45),(0,1,10),(0,4,10),(3,11,45),(2,4,12),(0,0,38),(0,2,38),(3,3,77),(0,0,85),(0,2,85),(2,0,53),(3,14,17),(3,1,103),(1,14,19),(1,14,45),(3,14,45),(1,3,104),(1,14,82),(2,4,16),(3,16,45),(3,23,45),(2,3,18),(1,19,23),(1,19,46),(1,24,44),(3,24,45),(1,27,44),(3,27,45),(1,3,92),(1,24,46),(1,27,46),(2,0,48),(1,3,48),(0,0,124)]
def h151W : BT Decor := buildWiresBT 7 h151Base h151Steps
def h151AutoList : List (List (Nat × Nat)) := [[],[(2,4)]]
def h151Autos : BT (List (Nat × Nat)) := btOfList 1 h151AutoList
lemma h151Pairs : goodPairs h151G h151Pos h151Neg := goodPairs_of (by decide +kernel)
lemma h151BaseOk : ∀ x ∈ h151Base, faithful h151Pos h151Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma h151WOk : btAll (fun x => faithful h151Pos h151Neg x ∧ x.1 < 2^128) h151W := buildWiresBT_faithful h151BaseOk
lemma h151AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h151G = h151G) h151Autos := btAll_ofList (autos_of (by decide +kernel))
def h151SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,5),some (subcubeFast 0 4,4),some (subcubeFast 0 8,5),some (subcubeFast 0 16,4),some (subcubeFast 0 32,6),some (subcubeFast 4 0,5),some (subcubeFast 4 1,4),some (subcubeFast 16 0,5),some (subcubeFast 16 1,4),some (subcubeFast 32 0,5),some (subcubeFast 32 8,4),some (0xaaaaaaaa55555555aaaaaaaa55555555,6),some (0xf00ff00ff00ff00ff00ff00ff00ff00f,5),some (0xf0f00f0ff0f00f0ff0f00f0ff0f00f0f,5),some (0xff0000ffff0000ffff0000ffff0000ff,5),some (0x55aa55aa55aa55aa55aa55aa55aa55aa,6)]
def h151Slices : BT (Option (Nat × Nat)) := btOfList 4 h151SliceList
def h151Specs : List PoolSpec := poolSteps h151Steps [(0,[]),(5,[]),(6,[]),(4,[0]),(1,[]),(2,[]),(7,[0]),(13,[]),(9,[14]),(8,[]),(3,[]),(7,[]),(14,[]),(9,[]),(4,[]),(12,[]),(4,[0,23]),(4,[0,25]),(4,[0,35]),(4,[1]),(5,[61]),(5,[66]),(11,[]),(4,[1,61]),(5,[65]),(4,[1,66]),(4,[1,67]),(5,[67]),(5,[68]),(4,[2]),(7,[2]),(15,[]),(4,[3]),(2,[8]),(10,[]),(15,[8]),(4,[4]),(7,[8]),(2,[9]),(7,[9]),(4,[54]),(5,[4]),(4,[6]),(4,[50]),(4,[14]),(7,[8,0]),(4,[40]),(4,[12]),(4,[11]),(9,[11]),(4,[16]),(4,[18,47]),(4,[18]),(5,[15]),(4,[14,33]),(4,[39]),(4,[39,40]),(4,[41]),(4,[119]),(4,[51]),(4,[55])]
def h151Pools : BT (Option BoundPool) := buildPoolsBT 6 h151W h151R h151Slices h151Specs
set_option maxRecDepth 200000 in
lemma h151Slice15 : Slice h151R h151G (0x55aa55aa55aa55aa55aa55aa55aa55aa) 6 := opposite_slice (oppositeRow 0 3 60) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h152Bound
set_option maxRecDepth 200000 in
lemma h151Slice14 : Slice h151R h151G (0xff0000ffff0000ffff0000ffff0000ff) 5 := mapped_slice (identifyRow 3 4 53) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h103Bound
set_option maxRecDepth 200000 in
lemma h151Slice13 : Slice h151R h151G (0xf0f00f0ff0f00f0ff0f00f0ff0f00f0f) 5 := mapped_slice (identifyRow 2 4 57) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h153Bound
set_option maxRecDepth 200000 in
lemma h151Slice12 : Slice h151R h151G (0xf00ff00ff00ff00ff00ff00ff00ff00f) 5 := mapped_slice (identifyRow 2 3 57) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h154Bound
set_option maxRecDepth 200000 in
lemma h151Slice11 : Slice h151R h151G (0xaaaaaaaa55555555aaaaaaaa55555555) 6 := mapped_slice (identifyRow 0 5 60) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h114Bound
set_option maxRecDepth 200000 in
lemma h151Slice10 : Slice h151R h151G (subcubeFast 32 8) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h51Bound
set_option maxRecDepth 200000 in
lemma h151Slice9 : Slice h151R h151G (subcubeFast 32 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h111Bound
set_option maxRecDepth 200000 in
lemma h151Slice8 : Slice h151R h151G (subcubeFast 16 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h3Bound
set_option maxRecDepth 200000 in
lemma h151Slice7 : Slice h151R h151G (subcubeFast 16 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h128Bound
set_option maxRecDepth 200000 in
lemma h151Slice6 : Slice h151R h151G (subcubeFast 4 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h37Bound
set_option maxRecDepth 200000 in
lemma h151Slice5 : Slice h151R h151G (subcubeFast 4 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h145Bound
set_option maxRecDepth 200000 in
lemma h151Slice4 : Slice h151R h151G (subcubeFast 0 32) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h150Bound
set_option maxRecDepth 200000 in
lemma h151Slice3 : Slice h151R h151G (subcubeFast 0 16) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h46Bound
set_option maxRecDepth 200000 in
lemma h151Slice2 : Slice h151R h151G (subcubeFast 0 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h60Bound
set_option maxRecDepth 200000 in
lemma h151Slice1 : Slice h151R h151G (subcubeFast 0 4) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h78Bound
set_option maxRecDepth 200000 in
lemma h151Slice0 : Slice h151R h151G (subcubeFast 0 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h89Bound
lemma h151SlicesOk : btAll (sliceSpec h151R h151G) h151Slices := btAll_ofList (P := sliceSpec h151R h151G) (sliceSpecCons h151Slice0 (sliceSpecCons h151Slice1 (sliceSpecCons h151Slice2 (sliceSpecCons h151Slice3 (sliceSpecCons h151Slice4 (sliceSpecCons h151Slice5 (sliceSpecCons h151Slice6 (sliceSpecCons h151Slice7 (sliceSpecCons h151Slice8 (sliceSpecCons h151Slice9 (sliceSpecCons h151Slice10 (sliceSpecCons h151Slice11 (sliceSpecCons h151Slice12 (sliceSpecCons h151Slice13 (sliceSpecCons h151Slice14 (sliceSpecCons h151Slice15 sliceSpecNil))))))))))))))))
set_option maxRecDepth 200000 in
lemma h151PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h151R h151G c) h151Pools := buildPoolsBT_sound h151SlicesOk
def h151Empty : BT (List (List Nat)) := BT.empty
lemma h151EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h151G (4 - 1) xs.toFinset) h151Empty := trivial
def h151Block4_0 : List NodeSpec := priorityNodes 6 [(30293011,1,2),(126762003,1,2),(128012363,1,2),(366863,1,2),(1166035493,1,2),(78121525,1,2),(26297629,109,2),(6241453341,109,2),(337951,78,2),(92801559,1,2),(24773775,1,2),(436255,1,2),(4932640843,1,2),(4932657227,1,2),(1116783849491,1,2),(489785733139,1,2),(390157323,1,2),(310505525,1,2),(487080101,1,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h151Test4_0 : checkNodesBT h151W h151G h151Mask h151Pools h151Autos h151Empty 4 h151Block4_0 = true := by decide +kernel
def h151Nodes4 : List NodeSpec := h151Block4_0
lemma h151Check4 : checkNodesBT h151W h151G h151Mask h151Pools h151Autos h151Empty 4 h151Nodes4 = true := h151Test4_0
def h151Bucket4 : BT (List (List Nat)) := buildBucketsBT h151W h151Nodes4
set_option maxRecDepth 200000 in
lemma h151Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h151G 4 xs.toFinset) h151Bucket4 := buildBucketsBT_sound (by decide) h151Pairs h151WOk h151PoolsOk h151AutosOk h151EmptyOk h151Check4
def h151Block5_0 : List NodeSpec := priorityNodes 6 [(6060107,4546,2),(3030123,70,2),(11811947,1,2),(729333,69,2),(745707,74,2),(194623,65,2),(778475,74,2),(206911,65,2),(3426351,1,2),(34621487,1,2),(219199,1,2),(909547,1,2),(948271,65,2),(14186543,1,2),(239679,1,2),(958699,74,2),(247871,65,2),(960559,21275009,2),(3975215,4545,2),(2402351,1,2),(60479,320332,2),(178276439,5391,2),(199247919,5444,2),(203442223,1,2),(577599,64,2),(165705815,1,2),(186677295,1,2),(190871599,1,2),(585791,64,2),(2871383,5391,2),(3919959,1,2),(12714603,77,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h151Test5_0 : checkNodesBT h151W h151G h151Mask h151Pools h151Autos h151Bucket4 5 h151Block5_0 = true := by decide +kernel
def h151Block5_1 : List NodeSpec := priorityNodes 6 [(626751,78,2),(634943,78,2),(136324405,26088002,2),(11929375,104,2),(2950773,299330,2),(38536791,5068,2),(684095,1,2),(10880799,107,2),(37490263,1,2),(749631,5005,2),(222464555,101,2),(3343647,1,2),(3081503,6336,2),(4852277,26010178,6),(973736501,6978,2),(34896874027,6477,2),(36439327,4131,2),(39585055,398208,2),(40109343,4992,2),(45352223,1,2),(9702517,4238,2),(700479,86,2),(10356511,1,2),(46925599,111,2),(222400043,103,2),(3213087,1,2),(2950943,1,2),(47974175,1,2),(47449887,103,2),(35915551,78,2),(48498463,1,2),(49022751,110,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h151Test5_1 : checkNodesBT h151W h151G h151Mask h151Pools h151Autos h151Bucket4 5 h151Block5_1 = true := by decide +kernel
def h151Block5_2 : List NodeSpec := priorityNodes 6 [(822495307,4417,2),(755910731,65,2),(2231447659,65,2),(51913835,1,2),(643135,5005,2),(38282347,115,2),(806975,65,2),(3292267,4481,2),(755136587,4417,2),(202390635,65,2),(766015,65,2),(220237899,68,2),(207679563,65,2),(4664221771,4546,2),(2517246027,31486209,2),(2785681483,4545,2),(3188334667,120,2),(52498539,68,2),(921663,1,2),(938047,1,2),(245385303,78,2),(929855,1,2),(232814679,78,2),(946239,77,2),(35715103,77,2),(39909407,78,2),(195056671,1,2),(962623,1,2),(60903531,1,2),(970815,1,2),(616585303,4737,2),(608200791,65,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h151Test5_2 : checkNodesBT h151W h151G h151Mask h151Pools h151Autos h151Bucket4 5 h151Block5_2 = true := by decide +kernel
def h151Block5_3 : List NodeSpec := priorityNodes 6 [(995391,65,2),(223295,316106,2),(235583,1,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h151Test5_3 : checkNodesBT h151W h151G h151Mask h151Pools h151Autos h151Bucket4 5 h151Block5_3 = true := by decide +kernel
def h151Nodes5 : List NodeSpec := h151Block5_0 ++ h151Block5_1 ++ h151Block5_2 ++ h151Block5_3
lemma h151Check5 : checkNodesBT h151W h151G h151Mask h151Pools h151Autos h151Bucket4 5 h151Nodes5 = true := by
  unfold h151Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨h151Test5_0,h151Test5_1⟩,h151Test5_2⟩,h151Test5_3⟩
def h151Bucket5 : BT (List (List Nat)) := buildBucketsBT h151W h151Nodes5
set_option maxRecDepth 200000 in
lemma h151Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h151G 5 xs.toFinset) h151Bucket5 := buildBucketsBT_sound (by decide) h151Pairs h151WOk h151PoolsOk h151AutosOk h151Bucket4Ok h151Check5
def h151Block6_0 : List NodeSpec := priorityNodes 6 [(59627,18895234,2),(71807,19661441,2),(75903,303681,2),(79999,4929,2),(92287,320321,2),(50239,1294771202,2),(100479,307841,2),(108591,18682498,2),(54335,83971281545,2),(299055,336578,2),(303295,1309938500,2),(352447,20500485,2),(512087,356489,2),(256063,20279433,2),(1089623,23085385,2),(1105967,1498694336,2),(1122351,23703817,2),(288799,24134473,2),(205675,385282,2),(127423,4354,2),(270783,19435778,2),(287167,4354,2),(336319,20500738,2),(369087,4354,2),(58431,418790620025090,2),(1081663,320321,2),(1278271,319501,2),(161855,20500553,2),(313375,315465,2),(17436,19146978,2),(17438,301186,2),(33822,25729282,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h151Test6_0 : checkNodesBT h151W h151G h151Mask h151Pools h151Autos h151Bucket5 6 h151Block6_0 = true := by decide +kernel
def h151Block6_1 : List NodeSpec := priorityNodes 6 [(344895,113317255104,2),(4784959,102174593282,2),(260159,83972890882,2),(1466475,282697,2),(1220715,299330,2),(374815,315714,2),(36894,19308710,2),(4523839,1243894018,2),(593983,83972890882,2),(24604,6274,2),(383007,315970,2),(214303,413858,2),(8520991,1854198338,6),(33817887,413858,2),(17040959,80699646093,2),(602175,1260931202,2),(5407,4258,2),(59167,27193510,2),(182047,27159298,2),(4130591,26778498,6),(15475819,1259540802,2),(365119,1925230690,6),(496191,1955119809,2),(15935,1261093122,2),(651327,1312051842,6),(440351,6274,2),(157759,19703938,6),(202815,1090536098,6),(1777711,6274,2),(888895,6274,2),(1794095,307522,2),(33855,102243807874,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h151Test6_1 : checkNodesBT h151W h151G h151Mask h151Pools h151Autos h151Bucket5 6 h151Block6_1 = true := by decide +kernel
def h151Block6_2 : List NodeSpec := priorityNodes 6 [(32319,30674948,2),(13909099,1209315460,6),(14433387,1209287362,2),(302655,19968961,2),(141375,5296782590026,6),(5119551,307268,2),(5381695,303172,2),(133183,102243803140,2),(1712203,18841858,2),(21505087,316097,6),(18365503,319565,2),(905279,20501186,2),(56383,4706448724546,6),(7625791,286978,2),(22553663,20467981,2),(19414079,5374265004356,2),(643135,418506985754692,2),(314611775,118298792004,2),(348166207,19701828,2),(398497855,4974,2),(23602239,316106,2),(20462655,320321,2),(774207,1312051842,2),(170047,80699908354,2),(954431,6274,2),(979007,19703938,2),(987199,131013296802,6),(211007,80699464418,2),(215103,132257415458,2),(227391,5164765565800,2),(231487,5303378665220,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h151Test6_2 : checkNodesBT h151W h151G h151Mask h151Pools h151Autos h151Bucket5 6 h151Block6_2 = true := by decide +kernel
def h151Nodes6 : List NodeSpec := h151Block6_0 ++ h151Block6_1 ++ h151Block6_2
lemma h151Check6 : checkNodesBT h151W h151G h151Mask h151Pools h151Autos h151Bucket5 6 h151Nodes6 = true := by
  unfold h151Nodes6 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨h151Test6_0,h151Test6_1⟩,h151Test6_2⟩
def h151Bucket6 : BT (List (List Nat)) := buildBucketsBT h151W h151Nodes6
set_option maxRecDepth 200000 in
lemma h151Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h151G 6 xs.toFinset) h151Bucket6 := buildBucketsBT_sound (by decide) h151Pairs h151WOk h151PoolsOk h151AutosOk h151Bucket5Ok h151Check6
def h151Block7_0 : List NodeSpec := priorityNodes 6 [(126,1293169218,2),(190,83971354761,2),(318,102225007170,2),(574,83971407945,2),(1086,1680220319,6),(2110,1295552834,6),(4158,24940706,6),(8254,1597544578,2),(5407,20486274,6),(9791,19194018,6),(5919,299906,6),(65598,299170,2),(12863,1311705218,2),(13887,19677346,6),(14911,309378,2),(15935,102191251618,6),(165951,1293382338,2),(170047,5296948265538,6),(174143,82776990402,2),(178239,309378,2),(182335,1261977762,6),(42047,1311510562,6),(48191,80547471693,6)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h151Test7_0 : checkNodesBT h151W h151G h151Mask h151Pools h151Autos h151Bucket6 7 h151Block7_0 = true := by decide +kernel
def h151Nodes7 : List NodeSpec := h151Block7_0
lemma h151Check7 : checkNodesBT h151W h151G h151Mask h151Pools h151Autos h151Bucket6 7 h151Nodes7 = true := h151Test7_0
def h151Bucket7 : BT (List (List Nat)) := buildBucketsBT h151W h151Nodes7
set_option maxRecDepth 200000 in
lemma h151Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h151G 7 xs.toFinset) h151Bucket7 := buildBucketsBT_sound (by decide) h151Pairs h151WOk h151PoolsOk h151AutosOk h151Bucket6Ok h151Check7
def h151Block8_0 : List NodeSpec := priorityNodes 6 [(62,78,6)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h151Test8_0 : checkNodesBT h151W h151G h151Mask h151Pools h151Autos h151Bucket7 8 h151Block8_0 = true := by decide +kernel
def h151Nodes8 : List NodeSpec := h151Block8_0
lemma h151Check8 : checkNodesBT h151W h151G h151Mask h151Pools h151Autos h151Bucket7 8 h151Nodes8 = true := h151Test8_0
def h151Bucket8 : BT (List (List Nat)) := buildBucketsBT h151W h151Nodes8
set_option maxRecDepth 200000 in
lemma h151Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h151G 8 xs.toFinset) h151Bucket8 := buildBucketsBT_sound (by decide) h151Pairs h151WOk h151PoolsOk h151AutosOk h151Bucket7Ok h151Check8
set_option maxRecDepth 200000 in
lemma h151Bound : Lower h151R h151G 9 := lower_of_forestBT (essPairs := [(VAR 0,12,13),(VAR 2,9,13),(VAR 3,5,13),(VAR 4,9,25),(VAR 5,5,37)]) (by decide +kernel) h151Bucket8Ok (by decide +kernel)
def h155R : List Nat := varsOf 30
def h155G : Nat := 0xfcccccc0fcccccc0fcccccc0fcccccc0
lemma h155Bound : Lower h155R h155G 6 := carry_of (swaps := [(4,5),(2,3),(0,1),(1,2)]) (roots2 := h18R) (T2 := h18G) (by decide +kernel) h18Bound
def h156R : List Nat := varsOf 46
def h156G : Nat := 0xfcccfcccf0c0f0c0fcccfcccf0c0f0c0
lemma h156Bound : Lower h156R h156G 4 := carry_of (swaps := [(2,3),(0,1)]) (roots2 := h46R) (T2 := h46G) (by decide +kernel) h46Bound
def h157R : List Nat := varsOf 58
def h157G : Nat := 0xffccccccffcccc00ffccccccffcccc00
lemma h157Bound : Lower h157R h157G 5 := carry_of (swaps := [(2,3),(3,4),(4,5),(0,1),(1,2),(2,3),(0,1)]) (roots2 := h14R) (T2 := h14G) (by decide +kernel) h14Bound
def h158R : List Nat := varsOf 62
def h158G : Nat := 0xfcccccc0f0c0c000fcccccc0f0c0c000
lemma h158Bound : Lower h158R h158G 9 := carry_of (swaps := [(2,3),(0,1)]) (roots2 := h151R) (T2 := h151G) (by decide +kernel) h151Bound
def h160R : List Nat := varsOf 30
def h160G : Nat := 0xfcccfffcfcccfffcfcccfffcfcccfffc
lemma h160Bound : Lower h160R h160G 5 := carry_of (swaps := [(0,1)]) (roots2 := h45R) (T2 := h45G) (by decide +kernel) h45Bound
def h161R : List Nat := varsOf 30
def h161G : Nat := 0xfcffccfcfcffccfcfcffccfcfcffccfc
lemma h161Bound : Lower h161R h161G 5 := carry_of (swaps := [(3,4),(0,1)]) (roots2 := h45R) (T2 := h45G) (by decide +kernel) h45Bound
def h162R : List Nat := varsOf 30
def h162G : Nat := 0xffcfcfccffcfcfccffcfcfccffcfcfcc
lemma h162Bound : Lower h162R h162G 5 := carry_of (swaps := [(3,4),(2,3),(0,1)]) (roots2 := h45R) (T2 := h45G) (by decide +kernel) h45Bound
def h163R : List Nat := varsOf 27
def h163G : Nat := 0xffeeee88ffeeee88ffeeee88ffeeee88
lemma h163Bound : Lower h163R h163G 7 := carry_of (swaps := [(3,4),(4,5),(1,2)]) (roots2 := h49R) (T2 := h49G) (by decide +kernel) h49Bound
def h159R : List Nat := varsOf 31
def h159G : Nat := 0xfeeeeee8feeeeee8feeeeee8feeeeee8
def h159Pos : List Nat := [5,6,3,3,6,5,9,17,28,28,13,10,18,9,18,28,21,9,3,17,10,14,5,14,22,5,7,18,6,11,11,17]
def h159Neg : List Nat := [4,4,1,2,2,1,1,1,12,20,12,2,2,8,20,24,20,12,4,20,8,2,12,12,20,0,4,16,12,2,1,16]
def h159Mask : Nat := fullMask 32
def h159Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xe64f24ed,0x400000e4),(0xcccccccccccccccccccccccccccccccc,0x7db4581e,0x20201818),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x17e18733,0x15cf4703),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x60b2af40,0x10d2a500),(0xffff0000ffff0000ffff0000ffff0000,0x8909d380,0x8909c200)]
def h159Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(1,0,2),(1,1,2),(1,3,4),(1,3,8),(3,3,11),(3,4,11),(1,6,9),(3,6,9),(1,4,12),(3,4,12),(0,8,9),(0,2,3),(1,2,3),(2,2,3),(0,2,6),(3,2,6),(3,1,2),(1,1,3),(1,4,20),(2,6,20),(0,8,25),(1,6,28),(3,3,25),(3,1,8),(1,3,31),(1,3,22),(2,3,22),(1,3,23),(3,1,11),(1,12,30),(1,1,12),(3,0,2),(1,0,19),(3,1,40),(1,19,23),(2,6,19),(3,0,14),(2,14,22),(1,1,44),(1,4,21),(1,4,5),(3,5,37),(1,0,15),(3,4,35),(2,8,24),(3,0,26)]
def h159W : BT Decor := buildWiresBT 6 h159Base h159Steps
def h159AutoList : List (List (Nat × Nat)) := [[],[(3,4)],[(2,3)],[(2,4)],[(0,1)],[(3,4),(2,3)],[(3,4),(2,4)],[(3,4),(0,1)],[(2,3),(0,1)],[(2,4),(0,1)],[(3,4),(2,3),(0,1)],[(3,4),(2,4),(0,1)]]
def h159Autos : BT (List (Nat × Nat)) := btOfList 4 h159AutoList
lemma h159Pairs : goodPairs h159G h159Pos h159Neg := goodPairs_of (by decide +kernel)
lemma h159BaseOk : ∀ x ∈ h159Base, faithful h159Pos h159Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma h159WOk : btAll (fun x => faithful h159Pos h159Neg x ∧ x.1 < 2^128) h159W := buildWiresBT_faithful h159BaseOk
lemma h159AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h159G = h159G) h159Autos := btAll_ofList (autos_of (by decide +kernel))
def h159SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 1 0,6),some (subcubeFast 2 0,6),some (subcubeFast 4 0,5),some (subcubeFast 8 0,5),some (subcubeFast 12 0,4),some (subcubeFast 16 0,5),some (subcubeFast 20 0,4),some (subcubeFast 24 0,4),some (0xf00ff00ff00ff00ff00ff00ff00ff00f,7),some (0xf0f00f0ff0f00f0ff0f00f0ff0f00f0f,7),some (0xff0000ffff0000ffff0000ffff0000ff,7),some (0x5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a,5),some (0x55aa55aa55aa55aa55aa55aa55aa55aa,5),some (0x5555aaaa5555aaaa5555aaaa5555aaaa,5),some (0x3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c,5),some (0x33cc33cc33cc33cc33cc33cc33cc33cc,5),some (0x3333cccc3333cccc3333cccc3333cccc,5)]
def h159Slices : BT (Option (Nat × Nat)) := btOfList 5 h159SliceList
def h159Specs : List PoolSpec := poolSteps h159Steps [(0,[]),(1,[]),(1,[3]),(2,[]),(0,[4]),(8,[1,3]),(9,[1,3]),(0,[14]),(8,[1,35]),(8,[1]),(3,[]),(5,[15]),(8,[]),(5,[]),(13,[]),(0,[15]),(9,[15]),(4,[]),(11,[]),(8,[1,22]),(9,[1]),(0,[17]),(8,[1,17]),(9,[1,17,28]),(9,[1,17]),(0,[17,29]),(9,[16]),(9,[]),(1,[10]),(0,[18]),(1,[18]),(8,[1,18]),(9,[1,18]),(10,[]),(10,[1]),(14,[]),(8,[3]),(6,[]),(9,[3]),(8,[20]),(15,[]),(0,[26]),(8,[3,26]),(9,[3,26]),(16,[]),(10,[3,15]),(8,[21]),(8,[3,5]),(9,[3,5]),(10,[3]),(7,[]),(0,[6]),(12,[]),(1,[14]),(8,[35,36]),(8,[35]),(1,[15])]
def h159Pools : BT (Option BoundPool) := buildPoolsBT 6 h159W h159R h159Slices h159Specs
set_option maxRecDepth 200000 in
lemma h159Slice16 : Slice h159R h159G (0x3333cccc3333cccc3333cccc3333cccc) 5 := opposite_slice (oppositeRow 1 4 29) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h45Bound
set_option maxRecDepth 200000 in
lemma h159Slice15 : Slice h159R h159G (0x33cc33cc33cc33cc33cc33cc33cc33cc) 5 := opposite_slice (oppositeRow 1 3 29) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h59Bound
set_option maxRecDepth 200000 in
lemma h159Slice14 : Slice h159R h159G (0x3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c) 5 := opposite_slice (oppositeRow 1 2 29) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h75Bound
set_option maxRecDepth 200000 in
lemma h159Slice13 : Slice h159R h159G (0x5555aaaa5555aaaa5555aaaa5555aaaa) 5 := opposite_slice (oppositeRow 0 4 30) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h160Bound
set_option maxRecDepth 200000 in
lemma h159Slice12 : Slice h159R h159G (0x55aa55aa55aa55aa55aa55aa55aa55aa) 5 := opposite_slice (oppositeRow 0 3 30) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h161Bound
set_option maxRecDepth 200000 in
lemma h159Slice11 : Slice h159R h159G (0x5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a) 5 := opposite_slice (oppositeRow 0 2 30) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h162Bound
set_option maxRecDepth 200000 in
lemma h159Slice10 : Slice h159R h159G (0xff0000ffff0000ffff0000ffff0000ff) 7 := mapped_slice (identifyRow 3 4 23) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h106Bound
set_option maxRecDepth 200000 in
lemma h159Slice9 : Slice h159R h159G (0xf0f00f0ff0f00f0ff0f00f0ff0f00f0f) 7 := mapped_slice (identifyRow 2 4 27) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h163Bound
set_option maxRecDepth 200000 in
lemma h159Slice8 : Slice h159R h159G (0xf00ff00ff00ff00ff00ff00ff00ff00f) 7 := mapped_slice (identifyRow 2 3 27) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h163Bound
set_option maxRecDepth 200000 in
lemma h159Slice7 : Slice h159R h159G (subcubeFast 24 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h23Bound
set_option maxRecDepth 200000 in
lemma h159Slice6 : Slice h159R h159G (subcubeFast 20 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h25Bound
set_option maxRecDepth 200000 in
lemma h159Slice5 : Slice h159R h159G (subcubeFast 16 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h30Bound
set_option maxRecDepth 200000 in
lemma h159Slice4 : Slice h159R h159G (subcubeFast 12 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h101Bound
set_option maxRecDepth 200000 in
lemma h159Slice3 : Slice h159R h159G (subcubeFast 8 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h139Bound
set_option maxRecDepth 200000 in
lemma h159Slice2 : Slice h159R h159G (subcubeFast 4 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h146Bound
set_option maxRecDepth 200000 in
lemma h159Slice1 : Slice h159R h159G (subcubeFast 2 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h150Bound
set_option maxRecDepth 200000 in
lemma h159Slice0 : Slice h159R h159G (subcubeFast 1 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h155Bound
lemma h159SlicesOk : btAll (sliceSpec h159R h159G) h159Slices := btAll_ofList (P := sliceSpec h159R h159G) (sliceSpecCons h159Slice0 (sliceSpecCons h159Slice1 (sliceSpecCons h159Slice2 (sliceSpecCons h159Slice3 (sliceSpecCons h159Slice4 (sliceSpecCons h159Slice5 (sliceSpecCons h159Slice6 (sliceSpecCons h159Slice7 (sliceSpecCons h159Slice8 (sliceSpecCons h159Slice9 (sliceSpecCons h159Slice10 (sliceSpecCons h159Slice11 (sliceSpecCons h159Slice12 (sliceSpecCons h159Slice13 (sliceSpecCons h159Slice14 (sliceSpecCons h159Slice15 (sliceSpecCons h159Slice16 sliceSpecNil)))))))))))))))))
set_option maxRecDepth 200000 in
lemma h159PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h159R h159G c) h159Pools := buildPoolsBT_sound h159SlicesOk
def h159Empty : BT (List (List Nat)) := BT.empty
lemma h159EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h159G (3 - 1) xs.toFinset) h159Empty := trivial
def h159Block3_0 : List NodeSpec := priorityNodes 6 [(8966297,1,2),(40931481,1,2),(48488525,1,2),(2851117,1,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h159Test3_0 : checkNodesBT h159W h159G h159Mask h159Pools h159Autos h159Empty 3 h159Block3_0 = true := by decide +kernel
def h159Nodes3 : List NodeSpec := h159Block3_0
lemma h159Check3 : checkNodesBT h159W h159G h159Mask h159Pools h159Autos h159Empty 3 h159Nodes3 = true := h159Test3_0
def h159Bucket3 : BT (List (List Nat)) := buildBucketsBT h159W h159Nodes3
set_option maxRecDepth 200000 in
lemma h159Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h159G 3 xs.toFinset) h159Bucket3 := buildBucketsBT_sound (by decide) h159Pairs h159WOk h159PoolsOk h159AutosOk h159EmptyOk h159Check3
def h159Block4_0 : List NodeSpec := priorityNodes 6 [(5296,65,2),(9392,1,2),(69206688,1,2),(368829,4160,2),(19419437,1,2),(1121847,1,2),(315479,1,2),(4981815,4875,2),(5114423,5580,2),(340055,1,2),(17567255,5836,2),(516525,1,2),(99359,1,2),(4457527,1,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h159Test4_0 : checkNodesBT h159W h159G h159Mask h159Pools h159Autos h159Bucket3 4 h159Block4_0 = true := by decide +kernel
def h159Nodes4 : List NodeSpec := h159Block4_0
lemma h159Check4 : checkNodesBT h159W h159G h159Mask h159Pools h159Autos h159Bucket3 4 h159Nodes4 = true := h159Test4_0
def h159Bucket4 : BT (List (List Nat)) := buildBucketsBT h159W h159Nodes4
set_option maxRecDepth 200000 in
lemma h159Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h159G 4 xs.toFinset) h159Bucket4 := buildBucketsBT_sound (by decide) h159Pairs h159WOk h159PoolsOk h159AutosOk h159Bucket3Ok h159Check4
def h159Block5_0 : List NodeSpec := priorityNodes 6 [(1712,274690,294),(1720,4099,2),(2294973,1,42),(3081405,4160,2),(2097844,1,34),(8389300,287040,2),(4068005,64,2),(4284,65,10),(8380,65,2),(2261365,4609,2),(605271,1,2),(52287,320332,2),(161855,1,2),(857175,5132,2),(48191,83,2),(8421430,5654,6),(934191,89,2),(39999,1,2),(165951,1,2),(988247,5772,2),(274479,1,2),(137279,1,2),(2523509,64,2),(1032495,1,2),(2916725,64,2),(2235479,1,2),(64575,6226,2),(37233829,67,2),(5174,65,2),(9270,1,2),(11666007,1,2),(69206566,1,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h159Test5_0 : checkNodesBT h159W h159G h159Mask h159Pools h159Autos h159Bucket4 5 h159Block5_0 = true := by decide +kernel
def h159Block5_1 : List NodeSpec := priorityNodes 6 [(50239,4160,2),(12060759,74,2),(58431,1,2),(2105894,76,2),(2425431,29021184,2),(10286,97,2),(13887,1,2),(133183,1,2),(9791,1,2),(8508,1,2),(9700399,82,2),(141375,82,2),(12863,91,2),(153663,118,2),(202815,1,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h159Test5_1 : checkNodesBT h159W h159G h159Mask h159Pools h159Autos h159Bucket4 5 h159Block5_1 = true := by decide +kernel
def h159Nodes5 : List NodeSpec := h159Block5_0 ++ h159Block5_1
lemma h159Check5 : checkNodesBT h159W h159G h159Mask h159Pools h159Autos h159Bucket4 5 h159Nodes5 = true := by
  unfold h159Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h159Test5_0,h159Test5_1⟩
def h159Bucket5 : BT (List (List Nat)) := buildBucketsBT h159W h159Nodes5
set_option maxRecDepth 200000 in
lemma h159Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h159G 5 xs.toFinset) h159Bucket5 := buildBucketsBT_sound (by decide) h159Pairs h159WOk h159PoolsOk h159AutosOk h159Bucket4Ok h159Check5
def h159Block6_0 : List NodeSpec := priorityNodes 6 [(700,1175728130,6),(110783,1243877827,42),(118975,1378096081,554),(270527,1411657813,38),(32830,373522,38),(32958,1414041859,38),(65726,377987,34),(39999,6630813517725,6),(286911,21508189,34),(1590,274690,294),(1598,1665663170,2),(2163287,16928913,2),(1147199,27425042,42),(56383,0x6caeaa2934a8c2,6),(1540415,21508098,34),(819799,28640209,34),(2622,1908485106,6),(4158,1936462930,10),(8254,1758597201,2),(8766,264466,2),(174143,413969,2),(149567,1998328485,2),(46143,7871903566161,1594)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h159Test6_0 : checkNodesBT h159W h159G h159Mask h159Pools h159Autos h159Bucket5 6 h159Block6_0 = true := by decide +kernel
def h159Nodes6 : List NodeSpec := h159Block6_0
lemma h159Check6 : checkNodesBT h159W h159G h159Mask h159Pools h159Autos h159Bucket5 6 h159Nodes6 = true := h159Test6_0
def h159Bucket6 : BT (List (List Nat)) := buildBucketsBT h159W h159Nodes6
set_option maxRecDepth 200000 in
lemma h159Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h159G 6 xs.toFinset) h159Bucket6 := buildBucketsBT_sound (by decide) h159Pairs h159WOk h159PoolsOk h159AutosOk h159Bucket5Ok h159Check6
def h159Block7_0 : List NodeSpec := priorityNodes 6 [(190,432397076410432,1598),(574,7048343998481,6),(145471,17041745,34),(15935,1288991397,34),(33855,86115416401,1594)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h159Test7_0 : checkNodesBT h159W h159G h159Mask h159Pools h159Autos h159Bucket6 7 h159Block7_0 = true := by decide +kernel
def h159Nodes7 : List NodeSpec := h159Block7_0
lemma h159Check7 : checkNodesBT h159W h159G h159Mask h159Pools h159Autos h159Bucket6 7 h159Nodes7 = true := h159Test7_0
def h159Bucket7 : BT (List (List Nat)) := buildBucketsBT h159W h159Nodes7
set_option maxRecDepth 200000 in
lemma h159Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h159G 7 xs.toFinset) h159Bucket7 := buildBucketsBT_sound (by decide) h159Pairs h159WOk h159PoolsOk h159AutosOk h159Bucket6Ok h159Check7
def h159Block8_0 : List NodeSpec := priorityNodes 6 [(62,1634517056,1598)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h159Test8_0 : checkNodesBT h159W h159G h159Mask h159Pools h159Autos h159Bucket7 8 h159Block8_0 = true := by decide +kernel
def h159Nodes8 : List NodeSpec := h159Block8_0
lemma h159Check8 : checkNodesBT h159W h159G h159Mask h159Pools h159Autos h159Bucket7 8 h159Nodes8 = true := h159Test8_0
def h159Bucket8 : BT (List (List Nat)) := buildBucketsBT h159W h159Nodes8
set_option maxRecDepth 200000 in
lemma h159Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h159G 8 xs.toFinset) h159Bucket8 := buildBucketsBT_sound (by decide) h159Pairs h159WOk h159PoolsOk h159AutosOk h159Bucket7Ok h159Check8
set_option maxRecDepth 200000 in
lemma h159Bound : Lower h159R h159G 9 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 3,1,9),(VAR 4,1,17)]) (by decide +kernel) h159Bucket8Ok (by decide +kernel)
def h164R : List Nat := varsOf 47
def h164G : Nat := 0xfeeefeeefac8fac8feeefeeefac8fac8
lemma h164Bound : Lower h164R h164G 6 := lift_of (z := 12) (o := 0) (essPairs := [(VAR 2,2,6),(VAR 3,1,9)]) (by decide +kernel) h15Bound
def h166R : List Nat := varsOf 39
def h166G : Nat := 0xfefefefee8e8e8e8fefefefee8e8e8e8
lemma h166Bound : Lower h166R h166G 7 := carry_of (swaps := [(3,4),(1,2),(2,3)]) (roots2 := h49R) (T2 := h49G) (by decide +kernel) h49Bound
def h165R : List Nat := varsOf 55
def h165G : Nat := 0xfefeeeeefafae8e8fefeeeeefafae8e8
def h165Pos : List Nat := [5,6,3,3,6,5,20,17,17,34,33,33,50,20,52,50,52]
def h165Neg : List Nat := [4,4,1,2,2,1,4,1,16,2,1,32,48,16,48,18,36]
def h165Mask : Nat := fullMask 17
def h165Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,3501,1188),(0xcccccccccccccccccccccccccccccccc,0x921e,0x8218),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x16073,0x10043),(0xffff0000ffff0000ffff0000ffff0000,0x1f1c0,0xf100),(0xffffffff00000000ffffffff00000000,0x1de00,0x15800)]
def h165Steps : List (Nat × Nat × Nat) := []
def h165W : BT Decor := buildWiresBT 3 h165Base h165Steps
def h165AutoList : List (List (Nat × Nat)) := [[],[(4,5),(1,2)]]
def h165Autos : BT (List (Nat × Nat)) := btOfList 1 h165AutoList
lemma h165Pairs : goodPairs h165G h165Pos h165Neg := goodPairs_of (by decide +kernel)
lemma h165BaseOk : ∀ x ∈ h165Base, faithful h165Pos h165Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma h165WOk : btAll (fun x => faithful h165Pos h165Neg x ∧ x.1 < 2^128) h165W := buildWiresBT_faithful h165BaseOk
lemma h165AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h165G = h165G) h165Autos := btAll_ofList (autos_of (by decide +kernel))
def h165SliceList : List (Option (Nat × Nat)) := [some (0xffff00000000ffffffff00000000ffff,7)]
def h165Slices : BT (Option (Nat × Nat)) := btOfList 1 h165SliceList
def h165Specs : List PoolSpec := [(0,[])]
def h165Pools : BT (Option BoundPool) := buildPoolsBT 1 h165W h165R h165Slices h165Specs
set_option maxRecDepth 200000 in
lemma h165Slice0 : Slice h165R h165G (0xffff00000000ffffffff00000000ffff) 7 := mapped_slice (identifyRow 4 5 39) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h166Bound
lemma h165SlicesOk : btAll (sliceSpec h165R h165G) h165Slices := btAll_ofList (P := sliceSpec h165R h165G) (sliceSpecCons h165Slice0 sliceSpecNil)
lemma h165PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h165R h165G c) h165Pools := buildPoolsBT_sound h165SlicesOk
def h165Empty : BT (List (List Nat)) := BT.empty
lemma h165EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h165G (6 - 1) xs.toFinset) h165Empty := trivial
def h165Block6_0 : List NodeSpec := priorityNodes 1 [(62,2,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h165Test6_0 : checkNodesBT h165W h165G h165Mask h165Pools h165Autos h165Empty 6 h165Block6_0 = true := by decide +kernel
def h165Nodes6 : List NodeSpec := h165Block6_0
lemma h165Check6 : checkNodesBT h165W h165G h165Mask h165Pools h165Autos h165Empty 6 h165Nodes6 = true := h165Test6_0
def h165Bucket6 : BT (List (List Nat)) := buildBucketsBT h165W h165Nodes6
lemma h165Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h165G 6 xs.toFinset) h165Bucket6 := buildBucketsBT_sound (by decide) h165Pairs h165WOk h165PoolsOk h165AutosOk h165EmptyOk h165Check6
lemma h165Bound : Lower h165R h165G 7 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 4,1,17),(VAR 5,1,33)]) (by decide +kernel) h165Bucket6Ok (by decide +kernel)
def h167R : List Nat := varsOf 59
def h167G : Nat := 0xffeeeeeeffccee88ffeeeeeeffccee88
lemma h167Bound : Lower h167R h167G 7 := carry_of (swaps := [(2,3),(0,1)]) (roots2 := h165R) (T2 := h165G) (by decide +kernel) h165Bound
def h168R : List Nat := varsOf 61
def h168G : Nat := 0xfffffffafafafaaafffffffafafafaaa
lemma h168Bound : Lower h168R h168G 6 := lift_of (z := 9) (o := 0) (essPairs := [(VAR 0,0,1),(VAR 3,4,12)]) (by decide +kernel) h54Bound
def h169R : List Nat := varsOf 62
def h169G : Nat := 0xfffffffcffccfcccfffffffcffccfccc
lemma h169Bound : Lower h169R h169G 6 := carry_of (swaps := [(2,3),(0,1)]) (roots2 := h168R) (T2 := h168G) (by decide +kernel) h168Bound
def h0R : List Nat := varsOf 63
def h0G : Nat := 0xfeeeeee8fac8e888feeeeee8fac8e888
def h0Pos : List Nat := [13,14,3,3,22,14,7,13,14,11,13,22,19,25,38,35,37,7,11,19,35,22,25,37,42,41,41,28,49,49,28,45,22,28,60,53,28,60,49,50,49,60,37,28,30,29,27,23,50,38,13,37,25,14,49,53,37,28,41,42,22,13,28,58,41,41,22,28,25,60,13,38,46,54,14,28,37,25,42,50,49,42,57,25,13,3,58,11,3,19,35,50,42,14,3,11,38,3,25,22,29,11,30,35,53,57,53,3,54]
def h0Neg : List Nat := [12,12,1,2,21,10,6,9,6,10,5,6,18,9,6,34,5,5,9,17,33,18,17,33,34,9,44,21,17,33,12,44,26,24,56,21,44,52,48,48,1,44,21,20,26,21,26,21,34,36,1,36,26,26,52,52,52,52,1,40,20,21,4,26,33,40,2,8,1,40,44,34,44,52,44,56,1,24,26,26,21,44,56,56,8,9,56,1,17,1,1,18,10,8,10,2,52,18,8,4,9,26,6,2,33,33,5,0,34]
def h0Mask : Nat := fullMask 109
def h0Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xfb6c7bd305325dce548b6dfb6cd,0x71007a110112404a5083adf2494),(0xcccccccccccccccccccccccccccccccc,0x18ebffe2c7849823d081013edb7e,0x10e2d800c084803150010120db68),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x155920101fec73aebe3fc8a34df3,0x4490003074073caae38cc034d53),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x274b0de6d7bee347a36cf4427a3,0x34707eed6a88305217c60422a3),(0xffff0000ffff0000ffff0000ffff0000,0x175c0a4daa3cd2d1fbff78683810,0x23094dea00b3f0fcef18681010),(0xffffffff00000000ffffffff00000000,0x17811c47d3a38dcb07ecb791c000,0x1301004e0fe30bcb02f4a5908000)]
def h0Steps : List (Nat × Nat × Nat) := [(1,0,1),(2,0,1),(3,0,1),(1,0,2),(3,0,2),(1,0,3),(3,0,3),(1,0,4),(3,0,4),(3,0,5),(1,1,2),(3,1,2),(1,1,3),(3,1,3),(1,1,4),(3,1,4),(3,1,5),(0,2,3),(1,0,23),(3,1,24),(1,2,3),(2,2,3),(3,2,3),(0,2,4),(1,2,4),(2,2,4),(3,2,4),(0,2,5),(3,2,5),(0,2,6),(3,2,6),(0,3,4),(1,3,4),(2,3,4),(3,3,4),(0,3,5),(2,3,5),(3,3,5),(0,3,6),(3,3,6),(0,4,5),(1,4,5),(3,4,5),(0,4,6),(3,4,6),(0,5,6),(3,5,6),(3,3,36),(1,4,23),(1,4,36),(3,4,36),(2,5,23),(1,0,46),(1,2,46),(0,5,59),(2,6,23),(1,3,46),(3,46,61),(2,6,46),(1,23,46),(1,0,48),(1,1,48),(1,2,48),(1,3,48),(2,6,48),(1,23,48),(0,3,54),(1,2,51),(1,3,51),(1,4,51),(1,51,54),(1,23,51),(3,4,76),(2,6,57),(3,0,26),(1,2,49),(0,4,26),(1,4,26),(3,4,26),(1,2,84),(1,3,84),(0,6,84),(2,6,84),(0,5,26),(0,6,26),(1,3,90),(1,4,90),(1,49,90),(2,26,49),(1,26,52),(2,26,52),(1,4,53),(1,50,53),(1,0,82),(1,2,82),(1,3,82),(3,3,83),(0,52,93),(3,52,83),(1,0,27),(1,1,27),(1,4,27),(2,6,27),(1,0,29),(3,1,109),(1,1,41),(1,2,41),(1,4,41),(2,6,41),(1,1,43),(1,2,43),(1,4,43),(1,1,29),(2,6,29),(3,41,119),(1,29,41),(1,29,43),(3,0,30),(3,1,30),(3,1,38),(0,6,30),(1,1,39),(1,2,102),(2,6,102),(1,4,44),(2,30,44),(1,4,126),(1,30,52),(2,30,52),(1,45,56),(1,0,72),(1,1,72),(1,0,31),(1,1,31),(2,6,31),(1,31,41),(1,31,43),(0,6,68),(1,0,32),(1,1,32),(1,3,32),(2,6,32),(1,0,33),(3,1,148),(1,1,33),(3,0,150),(1,3,33),(3,4,152),(1,4,33),(2,6,33),(1,0,34),(1,1,34),(1,3,34),(3,4,158),(0,6,158),(1,4,34),(2,6,34),(1,34,44),(0,6,161),(2,6,161),(1,34,49),(1,4,162),(3,4,91),(1,35,48),(1,51,132),(0,6,47),(3,4,73),(3,35,74),(3,1,58),(3,1,9),(3,3,9),(3,4,9),(3,4,16),(1,4,17),(2,9,17),(0,9,38),(2,9,43),(2,9,48),(3,4,18),(0,9,184),(0,9,18),(1,4,186),(0,5,186),(2,5,186),(2,9,31),(2,9,19),(3,2,20),(0,9,20),(1,4,176),(1,2,21),(2,9,21),(1,2,22),(1,3,22),(1,0,124),(3,0,139),(1,0,37),(2,9,37),(0,9,127),(2,9,39),(2,9,40),(2,9,41),(2,9,46),(1,1,10),(1,3,10),(1,4,10),(3,10,16),(3,10,38),(1,10,19),(3,10,20),(1,10,21),(3,10,30),(1,10,37),(1,10,39),(3,4,218),(1,10,40),(1,10,41),(1,10,43),(1,10,46),(1,10,48),(3,1,11),(3,2,11),(3,4,11),(0,11,16),(2,11,17),(0,11,20),(2,11,21),(2,11,29),(0,11,30),(2,11,31),(1,4,234),(2,11,32),(2,11,33),(2,11,34),(2,11,46),(2,11,48),(1,1,12),(1,2,12),(1,4,12),(1,12,17),(3,12,20),(1,12,21),(1,12,29),(3,12,30),(1,12,31),(3,4,249),(1,12,32),(1,12,33),(1,12,34),(1,12,46),(1,12,48),(3,1,13),(3,2,13),(3,3,13),(2,13,34),(2,13,21),(0,13,26),(2,13,43),(2,13,23),(2,13,27),(1,1,28),(2,13,28),(3,0,145),(2,13,32),(2,13,33),(2,13,41),(1,1,14),(1,2,14),(1,3,14),(1,14,23),(3,14,26),(1,14,27),(1,14,28),(3,14,30),(1,14,33),(1,14,34),(1,14,41),(1,14,43),(1,1,15),(1,2,15),(1,3,15),(1,4,15),(3,4,284),(3,4,285),(1,1,80),(2,26,46),(2,26,48),(3,1,105),(0,5,105),(3,0,106),(1,27,46),(1,27,48),(3,0,118),(1,1,123),(2,30,41),(2,30,43),(1,1,60),(3,1,138),(3,1,144),(1,32,41),(1,32,43),(3,1,156),(3,0,157),(3,1,66)]
def h0W : BT Decor := buildWiresBT 9 h0Base h0Steps
def h0AutoList : List (List (Nat × Nat)) := [[],[(2,3),(0,1)]]
def h0Autos : BT (List (Nat × Nat)) := btOfList 1 h0AutoList
lemma h0Pairs : goodPairs h0G h0Pos h0Neg := goodPairs_of (by decide +kernel)
lemma h0BaseOk : ∀ x ∈ h0Base, faithful h0Pos h0Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma h0WOk : btAll (fun x => faithful h0Pos h0Neg x ∧ x.1 < 2^128) h0W := buildWiresBT_faithful h0BaseOk
lemma h0AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h0G = h0G) h0Autos := btAll_ofList (autos_of (by decide +kernel))
def h0SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,6),some (subcubeFast 0 2,6),some (subcubeFast 0 4,7),some (subcubeFast 0 8,7),some (subcubeFast 0 16,6),some (subcubeFast 0 32,9),some (subcubeFast 1 0,9),some (subcubeFast 1 2,5),some (subcubeFast 1 4,5),some (subcubeFast 1 16,4),some (subcubeFast 1 32,6),some (subcubeFast 2 0,9),some (subcubeFast 2 1,5),some (subcubeFast 2 8,5),some (subcubeFast 2 16,4),some (subcubeFast 2 32,6),some (subcubeFast 4 0,8),some (subcubeFast 4 1,5),some (subcubeFast 4 8,5),some (subcubeFast 4 16,5),some (subcubeFast 4 32,5),some (subcubeFast 6 0,5),some (subcubeFast 6 1,4),some (subcubeFast 8 0,8),some (subcubeFast 8 2,5),some (subcubeFast 8 4,5),some (subcubeFast 8 16,5),some (subcubeFast 8 32,5),some (subcubeFast 9 0,5),some (subcubeFast 9 2,4),some (subcubeFast 12 0,5),some (subcubeFast 12 16,4),some (subcubeFast 12 32,4),some (subcubeFast 16 0,8),some (subcubeFast 16 1,5),some (subcubeFast 16 2,5),some (subcubeFast 16 4,5),some (subcubeFast 16 8,5),some (subcubeFast 16 32,5),some (subcubeFast 17 0,5),some (subcubeFast 17 2,4),some (subcubeFast 18 0,5),some (subcubeFast 18 1,4),some (subcubeFast 20 0,5),some (subcubeFast 20 8,4),some (subcubeFast 20 32,4),some (subcubeFast 24 0,5),some (subcubeFast 24 4,4),some (subcubeFast 24 32,4),some (subcubeFast 32 0,8),some (subcubeFast 32 4,5),some (subcubeFast 32 8,5),some (subcubeFast 33 0,5),some (subcubeFast 33 4,4),some (subcubeFast 34 0,5),some (subcubeFast 34 8,4),some (subcubeFast 48 0,5),some (subcubeFast 48 4,4),some (subcubeFast 48 8,4),some (0xaa55aa55aa55aa55aa55aa55aa55aa55,9),some (0xaaaaaaaa55555555aaaaaaaa55555555,9),some (0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3,9),some (0xcccccccc33333333cccccccc33333333,9),some (0xf0f00f0ff0f00f0ff0f00f0ff0f00f0f,9),some (0xff0000ffff0000ffff0000ffff0000ff,9),some (0x66666666666666666666666666666666,8),some (0x5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a,9),some (0x55aa55aa55aa55aa55aa55aa55aa55aa,9),some (0x5555aaaa5555aaaa5555aaaa5555aaaa,9),some (0x3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c,9),some (0x33cc33cc33cc33cc33cc33cc33cc33cc,9),some (0x3333cccc3333cccc3333cccc3333cccc,9),some (0xffffffff00000000ffffffff0000,9)]
def h0Slices : BT (Option (Nat × Nat)) := btOfList 7 h0SliceList
def h0Specs : List PoolSpec := poolSteps h0Steps [(6,[]),(11,[]),(6,[17]),(11,[17]),(11,[17,18]),(0,[]),(16,[0]),(16,[]),(23,[0]),(59,[]),(34,[]),(1,[]),(5,[0,17]),(2,[]),(11,[17,30]),(23,[0,30]),(5,[17,0,30]),(3,[]),(36,[]),(50,[]),(33,[0,30]),(17,[]),(23,[]),(6,[40]),(35,[]),(11,[40]),(24,[]),(16,[40]),(23,[40,53]),(37,[]),(49,[17]),(5,[17,53]),(49,[0]),(43,[]),(23,[40]),(5,[17]),(5,[0]),(6,[17,55]),(11,[17,55]),(49,[]),(5,[]),(33,[]),(33,[17]),(6,[40,58]),(11,[40,58]),(5,[0,58]),(5,[17,59]),(33,[0]),(6,[42]),(11,[42]),(16,[42]),(23,[42]),(51,[]),(38,[]),(45,[]),(63,[0]),(5,[17,65]),(19,[]),(6,[17,48]),(11,[17,48]),(64,[0]),(3,[48]),(4,[]),(6,[45,17,48]),(6,[45]),(11,[45,17,48]),(11,[45]),(63,[0,45]),(64,[0,45]),(49,[17,48]),(57,[]),(5,[17,48]),(59,[0,45]),(11,[17,45]),(61,[0,45]),(16,[0,45]),(23,[0,45]),(33,[0,45]),(6,[17,45,71]),(11,[17,45,71]),(6,[17,51]),(11,[17,51]),(33,[17,51]),(6,[17,51,73]),(11,[17,51,73]),(23,[0,73]),(20,[]),(65,[]),(5,[0,17,55]),(6,[20]),(11,[20]),(2,[0]),(5,[0,20]),(3,[0]),(53,[]),(33,[20]),(61,[0,43]),(59,[0,43]),(8,[]),(63,[]),(32,[]),(31,[]),(2,[0,45]),(2,[0,46]),(33,[0,46]),(63,[0,44]),(39,[]),(5,[20,76]),(30,[]),(6,[20,78]),(6,[20,77]),(11,[20,77]),(23,[77]),(5,[20,77]),(60,[20,77]),(52,[]),(13,[]),(61,[]),(11,[20,78]),(16,[78]),(23,[78]),(5,[20,78]),(60,[20,78]),(6,[20,45]),(11,[20,45]),(3,[0,45]),(5,[20]),(60,[20]),(11,[20,46]),(6,[46]),(11,[46]),(23,[0,46]),(3,[0,46]),(63,[0,46]),(6,[20,84]),(11,[20,84]),(23,[0,84]),(5,[0,20,84]),(11,[30,47]),(5,[0,30,47]),(6,[21]),(11,[21]),(5,[0,21]),(55,[]),(33,[21]),(6,[21,101]),(11,[21,101]),(23,[101]),(5,[0,21,101]),(58,[]),(5,[21,101]),(6,[21,45]),(11,[21,45]),(49,[21]),(5,[21]),(11,[21,102]),(23,[0,102]),(5,[0,21,102]),(6,[23]),(11,[23]),(11,[23,103]),(5,[0,23,103]),(49,[23,103]),(11,[35]),(11,[37]),(18,[]),(11,[45,23,103]),(5,[0,23]),(11,[23,30]),(25,[]),(5,[23,0,30]),(6,[35]),(16,[35]),(33,[35,106]),(26,[]),(49,[23]),(5,[23,106]),(33,[35]),(16,[35,107]),(5,[23,107]),(46,[]),(5,[23]),(6,[23,113]),(11,[23,113]),(23,[23]),(6,[35,108]),(5,[23,115]),(6,[37]),(16,[37]),(33,[37]),(27,[]),(61,[37]),(5,[23,116]),(5,[20,76,95]),(16,[0,44]),(11,[23,44]),(6,[23,45]),(11,[23,45]),(56,[]),(5,[0,23,113]),(6,[24]),(11,[24]),(5,[0,24]),(61,[24]),(5,[24,32]),(3,[24]),(33,[20,96]),(5,[24,33]),(2,[33]),(59,[24]),(23,[24]),(63,[0,120]),(33,[0,120]),(64,[]),(44,[]),(64,[0,39]),(28,[]),(6,[24,45]),(11,[24,45]),(49,[24]),(5,[24]),(60,[24]),(11,[24,46]),(64,[0,46]),(6,[24,120]),(11,[24,120]),(5,[0,24,120]),(11,[30,50]),(5,[0,30,50]),(6,[25]),(11,[25]),(5,[0,25]),(5,[25,33]),(49,[25]),(5,[25,107]),(5,[25]),(47,[]),(23,[25]),(5,[25,135]),(26,[110]),(5,[25,110]),(5,[25,136]),(6,[20,78,80]),(5,[25,62]),(63,[42,62]),(61,[42]),(6,[25,44]),(11,[25,44]),(6,[25,45]),(11,[25,45]),(11,[25,134]),(6,[26]),(11,[26]),(5,[0,26]),(23,[26]),(6,[26,140]),(11,[26,140]),(16,[140]),(5,[0,26,140]),(5,[26,140]),(6,[26,45]),(11,[26,45]),(49,[26]),(5,[26]),(11,[26,141]),(16,[0,141]),(5,[0,26,141]),(6,[27]),(11,[27]),(11,[27,142]),(5,[0,142]),(60,[]),(6,[27,144]),(5,[0,144]),(62,[]),(23,[27]),(6,[27,146]),(11,[27,146]),(5,[0,146]),(33,[27,146]),(49,[147]),(5,[146,147]),(33,[27]),(6,[27,148]),(11,[27,148]),(23,[27,148]),(5,[0,148]),(5,[148]),(11,[27,149]),(5,[0,149]),(6,[28]),(11,[28]),(23,[28]),(49,[0,38]),(5,[0,38,152]),(3,[28]),(5,[0,38,157]),(6,[28,152]),(11,[28,152]),(16,[152]),(5,[0,152]),(33,[28,152]),(49,[153]),(5,[152,153]),(5,[152]),(49,[0,154]),(5,[0,152,154]),(33,[28]),(49,[0,43]),(5,[0,43,155]),(5,[0,43]),(5,[0,43,160]),(68,[28]),(6,[28,44]),(6,[44]),(11,[28,44]),(11,[44]),(5,[0,44]),(49,[0,44]),(5,[0,44,155]),(49,[0,159]),(5,[0,155,159]),(6,[28,155]),(11,[28,155]),(16,[155]),(23,[28,155]),(5,[0,155]),(5,[155]),(49,[0,158]),(5,[0,155,158]),(6,[28,156]),(11,[28,156]),(5,[0,156]),(49,[0,161]),(11,[29]),(5,[0,29]),(49,[0,29]),(5,[0,29,62]),(2,[42]),(5,[0,29,163]),(6,[24,120,126]),(11,[24,120,126]),(12,[24]),(72,[0,45]),(6,[29,45]),(11,[29,45]),(3,[0,45,67]),(23,[0,29,45]),(33,[0,29,45]),(5,[0,29,67]),(5,[0,68]),(23,[0,29]),(63,[0,29]),(10,[]),(6,[29,46]),(66,[]),(6,[30]),(11,[30]),(5,[0,30]),(6,[30,49]),(11,[30,49]),(5,[0,30,49]),(49,[0,39]),(5,[0,39]),(49,[0,30]),(6,[30,44]),(11,[30,46]),(67,[]),(11,[40,52]),(5,[0,52]),(6,[40,53]),(11,[40,53]),(5,[0,53]),(5,[53]),(6,[42,62]),(11,[42,62]),(5,[0,62]),(23,[42,62]),(33,[62]),(5,[62]),(49,[0,137]),(5,[0,62,137]),(6,[42,64]),(48,[]),(11,[43]),(11,[43,75]),(6,[43,45]),(6,[43,46]),(68,[]),(11,[44,45]),(16,[0,44,45]),(23,[0,44,45]),(11,[44,46]),(11,[45,67]),(5,[0,67]),(5,[0,67,166]),(5,[0,69]),(6,[45,67,166]),(11,[3]),(6,[10]),(5,[3,10]),(6,[10,172]),(11,[3,172]),(4,[3]),(5,[3,10,172]),(35,[3]),(29,[]),(16,[32]),(6,[32]),(11,[3,32]),(23,[3,11]),(40,[]),(49,[3,11]),(5,[3,11]),(42,[]),(6,[11,37]),(11,[3,37]),(66,[11]),(6,[11,42]),(11,[3,42]),(5,[3,11,174]),(16,[12]),(23,[3]),(2,[12]),(11,[3,24]),(33,[3]),(2,[12,178]),(49,[3,24]),(5,[3,24]),(6,[12,180]),(49,[3,25]),(5,[3,25]),(22,[]),(5,[3,12]),(3,[3]),(3,[42]),(49,[12]),(49,[3]),(62,[3]),(66,[12]),(6,[171]),(11,[3,171]),(23,[3,171]),(16,[171]),(3,[3,171]),(49,[3,171]),(5,[3,171]),(5,[12]),(70,[3]),(64,[3]),(5,[3]),(11,[3,180]),(16,[12,180]),(23,[3,180]),(5,[3,12,180]),(6,[13]),(2,[13]),(5,[3,13]),(49,[13]),(6,[13,185]),(16,[13,185]),(6,[14]),(16,[14]),(5,[3,14]),(7,[]),(1,[32]),(23,[14]),(3,[14]),(49,[14,32]),(5,[14,32]),(6,[32,14,187]),(41,[]),(6,[170]),(11,[3,170]),(16,[170]),(19,[170]),(64,[3,170]),(49,[3,170]),(5,[3,170]),(49,[14]),(5,[14]),(6,[14,187]),(16,[14,187]),(5,[3,14,187]),(71,[]),(16,[15]),(5,[3,15]),(49,[15]),(11,[3,190]),(6,[16]),(16,[16]),(6,[16,169]),(16,[16,169]),(2,[16]),(5,[3,169]),(6,[16,192]),(16,[16,192]),(11,[3,192]),(5,[192]),(15,[]),(6,[169]),(16,[169]),(6,[32,169]),(11,[32,3]),(23,[3,169]),(33,[3,169]),(49,[3,169]),(62,[32]),(5,[32]),(12,[]),(6,[37,169]),(2,[37]),(6,[42,169]),(6,[24,118]),(16,[118]),(5,[3,24,118]),(6,[25,133]),(5,[3,25,184]),(6,[31]),(16,[31]),(2,[31,195]),(16,[31,195]),(2,[31]),(5,[3,31]),(49,[31]),(11,[3,31,196]),(16,[31,196]),(5,[3,31,196]),(5,[3,32]),(6,[32,171]),(11,[32,3,171]),(16,[32,171]),(5,[32,3,171]),(49,[32]),(6,[32,175]),(5,[3,32,175]),(6,[33]),(16,[33]),(11,[3,33]),(5,[3,33]),(49,[33,121]),(5,[33,121]),(11,[3,33,197]),(64,[3,197]),(6,[33,170]),(11,[33,3,170]),(5,[33,3,170]),(49,[33]),(5,[33]),(6,[33,198]),(11,[3,33,198]),(16,[34]),(2,[34]),(5,[3,34]),(11,[34,3,171]),(16,[34,171]),(49,[34]),(11,[3,34,199]),(16,[34,199]),(23,[3,199]),(11,[3,35]),(16,[35,105]),(5,[3,105]),(54,[]),(6,[35,170]),(6,[35,200]),(11,[3,35,200]),(5,[3,200]),(23,[109]),(6,[37,176]),(70,[]),(6,[170,188]),(11,[3,170,188]),(2,[188]),(16,[170,188]),(5,[3,170,188]),(11,[3,40,201]),(5,[3,201]),(23,[42,61]),(11,[42,63]),(33,[63]),(6,[42,171]),(11,[42,3,171]),(16,[42,171]),(6,[42,177]),(11,[4]),(11,[4,32]),(33,[4,10]),(4,[4]),(49,[4,10]),(5,[4,10]),(21,[]),(69,[4]),(26,[4]),(5,[4,10,172]),(5,[10,4,205]),(23,[4]),(5,[4,13]),(33,[4]),(62,[4]),(5,[4]),(49,[4]),(11,[4,207]),(5,[4,15]),(6,[15,189]),(11,[4,189]),(5,[4,15,189]),(11,[4,209]),(15,[32]),(3,[4]),(15,[4]),(6,[202]),(5,[4,202]),(6,[32,202]),(49,[4,202]),(5,[4,24]),(5,[24,4,210]),(5,[4,31]),(11,[4,31,211]),(5,[4,32]),(23,[119]),(5,[32,119]),(49,[32,119]),(23,[4,206]),(11,[4,33]),(11,[4,33,212]),(5,[4,34]),(23,[4,77]),(11,[4,34,214]),(23,[4,214]),(11,[4,35]),(5,[4,105]),(11,[4,35,106]),(5,[4,106]),(11,[4,35,215]),(5,[4,215]),(5,[4,216]),(6,[203]),(11,[4,203]),(5,[4,203]),(6,[33,212,213]),(11,[4,40,53]),(5,[4,53]),(11,[4,40,217]),(5,[4,217]),(5,[4,218]),(6,[204]),(5,[4,204]),(11,[5]),(16,[5]),(2,[5]),(5,[5,10]),(33,[5]),(63,[5]),(49,[5]),(5,[5]),(11,[5,222]),(16,[5,222]),(5,[5,10,222]),(5,[5,11]),(49,[11]),(5,[5,11,223]),(23,[11,223]),(5,[5,14]),(67,[14]),(5,[5,14,224]),(3,[15]),(5,[5,15]),(67,[15]),(11,[5,225]),(5,[5,15,225]),(5,[191]),(64,[16]),(6,[219]),(23,[219]),(6,[24,219]),(11,[24,5]),(16,[5,219]),(49,[5,219]),(5,[5,219]),(62,[24]),(3,[23,103]),(23,[23,103]),(5,[5,23]),(11,[5,24]),(5,[5,24]),(3,[25]),(5,[5,25]),(23,[25,228]),(11,[5,26]),(3,[26]),(5,[5,26]),(16,[5,230]),(5,[5,231]),(16,[5,232]),(5,[5,232]),(6,[220]),(11,[5,220]),(5,[5,220]),(69,[]),(14,[]),(11,[5,40]),(3,[40]),(5,[5,233]),(33,[5,234]),(5,[5,234]),(6,[221]),(11,[5,221]),(5,[5,221]),(11,[6]),(16,[6]),(5,[6,11]),(33,[6]),(5,[6]),(49,[6]),(11,[6,238]),(5,[6,14]),(6,[14,237]),(11,[6,237]),(6,[14,239]),(5,[6,15]),(11,[6,240]),(6,[16,237]),(6,[237]),(5,[6,237]),(62,[6,237]),(3,[237]),(6,[235]),(6,[24,235]),(16,[6,235]),(33,[6,235]),(49,[6,235]),(5,[6,235]),(6,[28,235]),(6,[42,235]),(5,[6,23]),(11,[6,24]),(2,[6]),(5,[6,24]),(6,[24,242]),(5,[6,24,242]),(5,[6,25]),(11,[6,26]),(5,[6,26]),(11,[6,26,245]),(16,[6,245]),(5,[6,146]),(5,[6,246]),(11,[6,28]),(6,[28,247]),(5,[6,247]),(6,[236]),(11,[6,236]),(5,[6,236]),(11,[6,40]),(6,[40,56]),(59,[40,56]),(11,[6,40,56]),(5,[6,56]),(11,[6,40,248]),(5,[6,248]),(11,[6,42]),(6,[42,249]),(5,[6,249]),(11,[7]),(68,[14]),(5,[7,14]),(6,[14,28]),(11,[7,28]),(2,[7]),(69,[7]),(6,[14,186]),(11,[7,186]),(5,[7,14,186]),(25,[7]),(50,[7]),(16,[7]),(23,[7]),(49,[7]),(5,[7]),(0,[15]),(11,[7,20]),(16,[7,15]),(23,[7,15]),(49,[7,15]),(5,[7,15]),(51,[15]),(5,[7,15,189]),(6,[15,37]),(11,[7,37]),(11,[7,252]),(5,[15,7,252]),(68,[15]),(23,[16,191]),(3,[7]),(6,[250]),(6,[20,250]),(11,[20,7]),(16,[7,250]),(23,[7,250]),(33,[250]),(49,[7,250]),(5,[7,250]),(62,[20]),(6,[24,250]),(5,[24,7,250]),(6,[28,250]),(6,[32,250]),(5,[32,7,250]),(6,[37,250]),(11,[37,7]),(6,[42,250]),(15,[7]),(5,[7,20]),(16,[7,255]),(23,[7,255]),(5,[7,21]),(23,[7,101]),(23,[7,258]),(6,[22]),(33,[22]),(11,[7,22]),(5,[7,22]),(49,[22]),(11,[7,22,260]),(16,[7,260]),(68,[24]),(11,[7,24]),(5,[7,24]),(33,[118]),(49,[7,24]),(5,[7,25]),(6,[25,251]),(11,[25,7,251]),(5,[25,7,251]),(11,[7,251]),(11,[7,26]),(5,[7,26]),(16,[7,139]),(12,[26]),(5,[7,26,262]),(5,[7,263]),(16,[7,253]),(5,[7,253]),(6,[251]),(5,[7,251]),(11,[7,32]),(5,[7,32]),(11,[7,33]),(5,[7,33]),(6,[33,252]),(11,[33,7,252]),(5,[33,7,252]),(11,[7,35]),(6,[35,107]),(5,[7,107]),(11,[7,35,264]),(5,[7,264]),(68,[37]),(11,[37,110]),(23,[7,256]),(5,[7,256]),(6,[252]),(5,[7,252]),(11,[7,42]),(11,[8]),(5,[8]),(16,[8]),(23,[8]),(6,[265]),(6,[20,265]),(16,[8,265]),(23,[8,265]),(49,[8,265]),(5,[8,265]),(6,[28,265]),(49,[8]),(11,[8,20]),(2,[8]),(3,[8]),(5,[8,20]),(6,[20,269]),(5,[8,20,269]),(5,[8,21]),(23,[8,101]),(23,[8,270]),(11,[8,22]),(5,[8,22]),(6,[22,271]),(11,[8,22,271]),(5,[8,24]),(69,[8]),(16,[8,118]),(6,[24,272]),(11,[24,8,272]),(5,[24,8,272]),(50,[8]),(5,[8,148]),(5,[8,273]),(11,[8,28]),(6,[28,274]),(5,[8,274]),(6,[266]),(11,[8,266]),(5,[8,266]),(11,[8,35]),(11,[8,35,107]),(5,[8,107]),(6,[35,275]),(11,[8,35,275]),(5,[8,275]),(11,[8,37]),(6,[37,276]),(6,[267]),(11,[8,267]),(5,[8,267]),(11,[9]),(11,[24,9]),(16,[9,277]),(33,[9,277]),(23,[9,277]),(10,[24]),(16,[9]),(23,[9]),(64,[9]),(33,[9]),(11,[9,22]),(5,[22,259]),(60,[22,259]),(16,[259]),(62,[9]),(5,[23,103]),(11,[9,24]),(5,[24,118]),(60,[24,118]),(6,[278]),(11,[9,278]),(5,[278]),(6,[278,281]),(5,[278,281]),(11,[9,33]),(6,[279]),(11,[9,279]),(5,[279]),(6,[279,282]),(5,[279,282]),(5,[17,18]),(6,[17,19]),(16,[19]),(23,[19]),(6,[17,42]),(3,[18]),(6,[17,40]),(11,[17,40]),(6,[17,40,53]),(11,[17,40,53]),(6,[17,40,59]),(11,[17,40,59]),(11,[17,42]),(6,[17,42,65]),(11,[17,42,65]),(16,[74]),(23,[74]),(5,[20,74]),(6,[20,283]),(16,[74,283]),(23,[74,283]),(2,[283]),(5,[20,74,283]),(3,[283]),(23,[40,78]),(23,[42,78]),(33,[20,285]),(6,[20,76]),(11,[20,76]),(11,[21,99]),(23,[99]),(5,[21,99]),(6,[21,286]),(16,[286]),(5,[21,99,286]),(23,[99,286]),(3,[286]),(6,[21,287]),(16,[287]),(6,[21,100]),(23,[100]),(5,[21,100]),(11,[21,288]),(16,[288]),(5,[21,100,288]),(23,[100,288]),(3,[288]),(6,[21,40]),(6,[21,42]),(6,[23,104]),(16,[104]),(33,[104]),(6,[35,23]),(6,[23,35,106]),(5,[23,103,106]),(6,[23,35,107]),(5,[23,103,107]),(6,[37,23]),(6,[23,112]),(5,[23,112]),(16,[291]),(33,[291]),(6,[23,35]),(11,[23,35]),(11,[23,35,106]),(11,[23,35,107]),(6,[23,35,115]),(11,[23,35,115]),(6,[23,37]),(11,[23,37]),(6,[23,37,116]),(11,[23,37,116]),(16,[1]),(64,[1]),(49,[1]),(5,[1]),(11,[24,117]),(5,[24,117]),(6,[24,292]),(16,[117,292]),(2,[292]),(16,[118,193]),(2,[193]),(6,[24,32]),(11,[24,32]),(6,[24,33]),(11,[24,33]),(9,[]),(11,[24,35]),(5,[24,105]),(23,[24,111]),(23,[24,294]),(2,[2]),(64,[2]),(3,[2]),(2,[295]),(5,[25,132]),(6,[25,296]),(16,[296]),(5,[25,133]),(16,[194]),(6,[25,33]),(11,[25,33]),(6,[25,35]),(11,[25,35]),(5,[25,105]),(6,[25,35,107]),(11,[25,35,107]),(6,[25,35,135]),(11,[25,35,135]),(6,[25,37]),(11,[25,37]),(6,[25,37,110]),(11,[25,37,110]),(6,[25,37,136]),(11,[25,37,136]),(6,[25,42]),(11,[25,42]),(6,[25,42,62]),(11,[25,42,62]),(16,[138]),(5,[26,138]),(6,[26,297]),(16,[138,297]),(2,[297]),(33,[297]),(16,[139]),(5,[26,139]),(16,[139,261]),(2,[261]),(33,[261]),(11,[26,35]),(11,[26,37]),(23,[26,111]),(23,[26,299]),(5,[142]),(6,[27,143]),(16,[143]),(5,[142,143]),(5,[144]),(11,[27,145]),(16,[145]),(5,[144,145]),(6,[27,146,147]),(11,[27,146,147]),(5,[150]),(6,[28,300]),(16,[150,300]),(2,[300]),(5,[150,300]),(16,[151]),(5,[151]),(11,[28,301]),(16,[151,301]),(2,[301]),(5,[151,301]),(6,[28,152,153]),(11,[28,152,153]),(2,[153]),(16,[152,153]),(5,[52]),(6,[40,168]),(33,[168]),(5,[52,168]),(5,[60]),(6,[42,302]),(5,[60,302])]
def h0Pools : BT (Option BoundPool) := buildPoolsBT 11 h0W h0R h0Slices h0Specs
set_option maxRecDepth 200000 in
lemma h0Slice73 : Slice h0R h0G (0xffffffff00000000ffffffff0000) 9 := opposite_slice (oppositeRow 4 5 47) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h1Bound
set_option maxRecDepth 200000 in
lemma h0Slice72 : Slice h0R h0G (0x3333cccc3333cccc3333cccc3333cccc) 9 := opposite_slice (oppositeRow 1 4 61) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h33Bound
set_option maxRecDepth 200000 in
lemma h0Slice71 : Slice h0R h0G (0x33cc33cc33cc33cc33cc33cc33cc33cc) 9 := opposite_slice (oppositeRow 1 3 61) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h48Bound
set_option maxRecDepth 200000 in
lemma h0Slice70 : Slice h0R h0G (0x3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c) 9 := opposite_slice (oppositeRow 1 2 61) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h61Bound
set_option maxRecDepth 200000 in
lemma h0Slice69 : Slice h0R h0G (0x5555aaaa5555aaaa5555aaaa5555aaaa) 9 := opposite_slice (oppositeRow 0 4 62) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h79Bound
set_option maxRecDepth 200000 in
lemma h0Slice68 : Slice h0R h0G (0x55aa55aa55aa55aa55aa55aa55aa55aa) 9 := opposite_slice (oppositeRow 0 3 62) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h80Bound
set_option maxRecDepth 200000 in
lemma h0Slice67 : Slice h0R h0G (0x5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a) 9 := opposite_slice (oppositeRow 0 2 62) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h81Bound
set_option maxRecDepth 200000 in
lemma h0Slice66 : Slice h0R h0G (0x66666666666666666666666666666666) 8 := opposite_slice (oppositeRow 0 1 62) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h82Bound
set_option maxRecDepth 200000 in
lemma h0Slice64 : Slice h0R h0G (0xff0000ffff0000ffff0000ffff0000ff) 9 := mapped_slice (identifyRow 3 4 55) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h93Bound
set_option maxRecDepth 200000 in
lemma h0Slice63 : Slice h0R h0G (0xf0f00f0ff0f00f0ff0f00f0ff0f00f0f) 9 := mapped_slice (identifyRow 2 4 59) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h108Bound
set_option maxRecDepth 200000 in
lemma h0Slice62 : Slice h0R h0G (0xcccccccc33333333cccccccc33333333) 9 := mapped_slice (identifyRow 1 5 61) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h109Bound
set_option maxRecDepth 200000 in
lemma h0Slice61 : Slice h0R h0G (0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3) 9 := mapped_slice (identifyRow 1 2 61) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h116Bound
set_option maxRecDepth 200000 in
lemma h0Slice60 : Slice h0R h0G (0xaaaaaaaa55555555aaaaaaaa55555555) 9 := mapped_slice (identifyRow 0 5 62) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h117Bound
set_option maxRecDepth 200000 in
lemma h0Slice59 : Slice h0R h0G (0xaa55aa55aa55aa55aa55aa55aa55aa55) 9 := mapped_slice (identifyRow 0 3 62) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h118Bound
set_option maxRecDepth 200000 in
lemma h0Slice58 : Slice h0R h0G (subcubeFast 48 8) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h23Bound
set_option maxRecDepth 200000 in
lemma h0Slice57 : Slice h0R h0G (subcubeFast 48 4) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h25Bound
set_option maxRecDepth 200000 in
lemma h0Slice56 : Slice h0R h0G (subcubeFast 48 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h119Bound
set_option maxRecDepth 200000 in
lemma h0Slice55 : Slice h0R h0G (subcubeFast 34 8) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h51Bound
set_option maxRecDepth 200000 in
lemma h0Slice54 : Slice h0R h0G (subcubeFast 34 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h111Bound
set_option maxRecDepth 200000 in
lemma h0Slice53 : Slice h0R h0G (subcubeFast 33 4) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h120Bound
set_option maxRecDepth 200000 in
lemma h0Slice52 : Slice h0R h0G (subcubeFast 33 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h121Bound
set_option maxRecDepth 200000 in
lemma h0Slice51 : Slice h0R h0G (subcubeFast 32 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h122Bound
set_option maxRecDepth 200000 in
lemma h0Slice50 : Slice h0R h0G (subcubeFast 32 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h123Bound
set_option maxRecDepth 200000 in
lemma h0Slice49 : Slice h0R h0G (subcubeFast 32 0) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h124Bound
set_option maxRecDepth 200000 in
lemma h0Slice48 : Slice h0R h0G (subcubeFast 24 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h23Bound
set_option maxRecDepth 200000 in
lemma h0Slice47 : Slice h0R h0G (subcubeFast 24 4) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h15Bound
set_option maxRecDepth 200000 in
lemma h0Slice46 : Slice h0R h0G (subcubeFast 24 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h100Bound
set_option maxRecDepth 200000 in
lemma h0Slice45 : Slice h0R h0G (subcubeFast 20 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h25Bound
set_option maxRecDepth 200000 in
lemma h0Slice44 : Slice h0R h0G (subcubeFast 20 8) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h15Bound
set_option maxRecDepth 200000 in
lemma h0Slice43 : Slice h0R h0G (subcubeFast 20 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h127Bound
set_option maxRecDepth 200000 in
lemma h0Slice42 : Slice h0R h0G (subcubeFast 18 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h3Bound
set_option maxRecDepth 200000 in
lemma h0Slice41 : Slice h0R h0G (subcubeFast 18 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h128Bound
set_option maxRecDepth 200000 in
lemma h0Slice40 : Slice h0R h0G (subcubeFast 17 2) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h3Bound
set_option maxRecDepth 200000 in
lemma h0Slice39 : Slice h0R h0G (subcubeFast 17 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h129Bound
set_option maxRecDepth 200000 in
lemma h0Slice38 : Slice h0R h0G (subcubeFast 16 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h30Bound
set_option maxRecDepth 200000 in
lemma h0Slice37 : Slice h0R h0G (subcubeFast 16 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h130Bound
set_option maxRecDepth 200000 in
lemma h0Slice36 : Slice h0R h0G (subcubeFast 16 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h131Bound
set_option maxRecDepth 200000 in
lemma h0Slice35 : Slice h0R h0G (subcubeFast 16 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h39Bound
set_option maxRecDepth 200000 in
lemma h0Slice34 : Slice h0R h0G (subcubeFast 16 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h132Bound
set_option maxRecDepth 200000 in
lemma h0Slice33 : Slice h0R h0G (subcubeFast 16 0) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h133Bound
set_option maxRecDepth 200000 in
lemma h0Slice32 : Slice h0R h0G (subcubeFast 12 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h101Bound
set_option maxRecDepth 200000 in
lemma h0Slice31 : Slice h0R h0G (subcubeFast 12 16) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h15Bound
set_option maxRecDepth 200000 in
lemma h0Slice30 : Slice h0R h0G (subcubeFast 12 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h137Bound
set_option maxRecDepth 200000 in
lemma h0Slice29 : Slice h0R h0G (subcubeFast 9 2) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h54Bound
set_option maxRecDepth 200000 in
lemma h0Slice28 : Slice h0R h0G (subcubeFast 9 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h138Bound
set_option maxRecDepth 200000 in
lemma h0Slice27 : Slice h0R h0G (subcubeFast 8 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h139Bound
set_option maxRecDepth 200000 in
lemma h0Slice26 : Slice h0R h0G (subcubeFast 8 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h14Bound
set_option maxRecDepth 200000 in
lemma h0Slice25 : Slice h0R h0G (subcubeFast 8 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h140Bound
set_option maxRecDepth 200000 in
lemma h0Slice24 : Slice h0R h0G (subcubeFast 8 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h55Bound
set_option maxRecDepth 200000 in
lemma h0Slice23 : Slice h0R h0G (subcubeFast 8 0) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h141Bound
set_option maxRecDepth 200000 in
lemma h0Slice22 : Slice h0R h0G (subcubeFast 6 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h37Bound
set_option maxRecDepth 200000 in
lemma h0Slice21 : Slice h0R h0G (subcubeFast 6 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h145Bound
set_option maxRecDepth 200000 in
lemma h0Slice20 : Slice h0R h0G (subcubeFast 4 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h146Bound
set_option maxRecDepth 200000 in
lemma h0Slice19 : Slice h0R h0G (subcubeFast 4 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h16Bound
set_option maxRecDepth 200000 in
lemma h0Slice18 : Slice h0R h0G (subcubeFast 4 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h147Bound
set_option maxRecDepth 200000 in
lemma h0Slice17 : Slice h0R h0G (subcubeFast 4 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h148Bound
set_option maxRecDepth 200000 in
lemma h0Slice16 : Slice h0R h0G (subcubeFast 4 0) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h149Bound
set_option maxRecDepth 200000 in
lemma h0Slice15 : Slice h0R h0G (subcubeFast 2 32) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h150Bound
set_option maxRecDepth 200000 in
lemma h0Slice14 : Slice h0R h0G (subcubeFast 2 16) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h46Bound
set_option maxRecDepth 200000 in
lemma h0Slice13 : Slice h0R h0G (subcubeFast 2 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h60Bound
set_option maxRecDepth 200000 in
lemma h0Slice12 : Slice h0R h0G (subcubeFast 2 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h89Bound
set_option maxRecDepth 200000 in
lemma h0Slice11 : Slice h0R h0G (subcubeFast 2 0) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h151Bound
set_option maxRecDepth 200000 in
lemma h0Slice10 : Slice h0R h0G (subcubeFast 1 32) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h155Bound
set_option maxRecDepth 200000 in
lemma h0Slice9 : Slice h0R h0G (subcubeFast 1 16) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h156Bound
set_option maxRecDepth 200000 in
lemma h0Slice8 : Slice h0R h0G (subcubeFast 1 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h157Bound
set_option maxRecDepth 200000 in
lemma h0Slice7 : Slice h0R h0G (subcubeFast 1 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h91Bound
set_option maxRecDepth 200000 in
lemma h0Slice6 : Slice h0R h0G (subcubeFast 1 0) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h158Bound
set_option maxRecDepth 200000 in
lemma h0Slice5 : Slice h0R h0G (subcubeFast 0 32) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h159Bound
set_option maxRecDepth 200000 in
lemma h0Slice4 : Slice h0R h0G (subcubeFast 0 16) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h164Bound
set_option maxRecDepth 200000 in
lemma h0Slice3 : Slice h0R h0G (subcubeFast 0 8) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h165Bound
set_option maxRecDepth 200000 in
lemma h0Slice2 : Slice h0R h0G (subcubeFast 0 4) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h167Bound
set_option maxRecDepth 200000 in
lemma h0Slice1 : Slice h0R h0G (subcubeFast 0 2) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h168Bound
set_option maxRecDepth 200000 in
lemma h0Slice0 : Slice h0R h0G (subcubeFast 0 1) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h169Bound
lemma h0SlicesOk : btAll (sliceSpec h0R h0G) h0Slices := btAll_ofList (P := sliceSpec h0R h0G) (sliceSpecCons h0Slice0 (sliceSpecCons h0Slice1 (sliceSpecCons h0Slice2 (sliceSpecCons h0Slice3 (sliceSpecCons h0Slice4 (sliceSpecCons h0Slice5 (sliceSpecCons h0Slice6 (sliceSpecCons h0Slice7 (sliceSpecCons h0Slice8 (sliceSpecCons h0Slice9 (sliceSpecCons h0Slice10 (sliceSpecCons h0Slice11 (sliceSpecCons h0Slice12 (sliceSpecCons h0Slice13 (sliceSpecCons h0Slice14 (sliceSpecCons h0Slice15 (sliceSpecCons h0Slice16 (sliceSpecCons h0Slice17 (sliceSpecCons h0Slice18 (sliceSpecCons h0Slice19 (sliceSpecCons h0Slice20 (sliceSpecCons h0Slice21 (sliceSpecCons h0Slice22 (sliceSpecCons h0Slice23 (sliceSpecCons h0Slice24 (sliceSpecCons h0Slice25 (sliceSpecCons h0Slice26 (sliceSpecCons h0Slice27 (sliceSpecCons h0Slice28 (sliceSpecCons h0Slice29 (sliceSpecCons h0Slice30 (sliceSpecCons h0Slice31 (sliceSpecCons h0Slice32 (sliceSpecCons h0Slice33 (sliceSpecCons h0Slice34 (sliceSpecCons h0Slice35 (sliceSpecCons h0Slice36 (sliceSpecCons h0Slice37 (sliceSpecCons h0Slice38 (sliceSpecCons h0Slice39 (sliceSpecCons h0Slice40 (sliceSpecCons h0Slice41 (sliceSpecCons h0Slice42 (sliceSpecCons h0Slice43 (sliceSpecCons h0Slice44 (sliceSpecCons h0Slice45 (sliceSpecCons h0Slice46 (sliceSpecCons h0Slice47 (sliceSpecCons h0Slice48 (sliceSpecCons h0Slice49 (sliceSpecCons h0Slice50 (sliceSpecCons h0Slice51 (sliceSpecCons h0Slice52 (sliceSpecCons h0Slice53 (sliceSpecCons h0Slice54 (sliceSpecCons h0Slice55 (sliceSpecCons h0Slice56 (sliceSpecCons h0Slice57 (sliceSpecCons h0Slice58 (sliceSpecCons h0Slice59 (sliceSpecCons h0Slice60 (sliceSpecCons h0Slice61 (sliceSpecCons h0Slice62 (sliceSpecCons h0Slice63 (sliceSpecCons h0Slice64 (sliceSpecCons h0Slice66 (sliceSpecCons h0Slice67 (sliceSpecCons h0Slice68 (sliceSpecCons h0Slice69 (sliceSpecCons h0Slice70 (sliceSpecCons h0Slice71 (sliceSpecCons h0Slice72 (sliceSpecCons h0Slice73 sliceSpecNil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
set_option maxRecDepth 200000 in
lemma h0PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h0R h0G c) h0Pools := buildPoolsBT_sound h0SlicesOk
def h0Empty : BT (List (List Nat)) := BT.empty
lemma h0EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G (6 - 1) xs.toFinset) h0Empty := trivial
def h0Block6_0 : List NodeSpec := priorityNodes 11 [(479359,2088,2),(1642559,4300819,2),(1650751,1,2),(1459822687,4393056,2),(281115679,2150,2),(1090681887,2151,2),(306247743,1,2),(348194879,4276263,2),(6455487,2163,2),(88289343,2087,2),(306251839,1,2),(348190783,18228143302695,2),(381749311,1,2),(122618789,2210,2),(307167925,2210,2),(93602037,1,2),(1892479,1,2),(85365370399,4333635,2),(77381727,2259,2),(1350629439,1,2),(1300301887,1,2),(21877777439,2115,2),(5303681119,1,2),(511155761239,4331559,2),(123498169375,2115,2),(2004940863,9114374212,2),(7986102487,4397095,2),(429979735,4902933,2),(2055272511,1,2),(2038529055,2150,2),(2021722175,1,2),(27615453335,1,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test6_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Empty 6 h0Block6_0 = true := by decide +kernel
def h0Nodes6 : List NodeSpec := h0Block6_0
lemma h0Check6 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Empty 6 h0Nodes6 = true := h0Test6_0
def h0Bucket6 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes6
set_option maxRecDepth 200000 in
lemma h0Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 6 xs.toFinset) h0Bucket6 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0EmptyOk h0Check6
def h0Block7_0 : List NodeSpec := priorityNodes 11 [(612393431,0x82104007c0f01d0380600680a,2),(65089663,0x41402604a06813815,2),(174073983,0x20b41602b0460800c01602203405007,2),(975103,0x105c0901081e01600400005,2),(56717439,4302887,2),(2146559,0x41a03304804c1c835,2),(1898559,18176574355526,2),(602175,0x84b09e13826046,2),(111212607,2078,2),(618559,18314088851542,2),(2382741855,18193741623301,2),(696356991,9001103401,2),(2900223,4399174,2),(2315665759,4388869,2),(59257919,4403210,2),(176698431,9022152714,2),(3780735,4409406,2),(2670847,4399122,2),(608196735,8850008074,2),(2572543,2157,2),(1057439935,18571870674949,2),(1450111,0x82807c0a43a05e,2),(2867455,9076547678,2),(2248589503,9097455686,2),(2181513407,18640577605637,2),(2703615,4337726,2),(331413567,8912939102,2),(460863,0x22141402010820840867,2),(2919710911,8669691909,2),(2986819775,8984209440,2),(2834687,0x4320620480801f005,2),(2998527,8669753362,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Block7_0 = true := by decide +kernel
def h0Block7_1 : List NodeSpec := priorityNodes 11 [(9194029557,0x228c510a00d401802818,2),(8925659637,4530338,2),(981594229,0x8a200a1345304b,2),(2801918423,0x22c0578ae15a1b00681a,2),(2835472735,0x22d0598b215e2a41f01a,2),(2634059903,0x8b716c0600b015,2),(717260927,0x22e45a83e05206806807,2),(3784959,0x8ba15e1b000005,2),(2566967423,4583463,2),(3817727,0x8bd0ca04c5f0a5,2),(4261462447,18451397734429,2),(3926081967,9009375375,2),(3372360031,18451439673399,2),(255087679,18820974667852,2),(2768302207,9479317526,2),(4112639,9009602565,2),(255611967,4464666,2),(48304255,4634641,2),(885037183,8699021325,2),(3389472959,18451259205764,2),(4047103,2191,2),(1266743359,18666246656094,2),(4786239,0x11be210410810500800a867,2),(10939220159,8669691909,2),(11073437887,8984209440,2),(914514391,8669663332,2),(2768396639,0x8ea1d22d01f01a,2),(700491903,9575723026,2),(8880383,0x8ee1d21b009005,2),(2869060055,19654748108818,2),(8945919,0x8f11d22b852812,2),(629301719,19689149777938,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_1 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Block7_1 = true := by decide +kernel
def h0Block7_2 : List NodeSpec := priorityNodes 11 [(9666815,0x9192300dc1f01d,2),(15368143279,20118855780357,2),(10322175,9831483685,2),(10060031,20196203032605,2),(10125567,9874016273,2),(15099871583,20247767805957,2),(10518783,9894490420,2),(14965686623,20333709596677,2),(3774984319,9919655983,2),(10453247,9936961554,2),(10387711,9970532414,2),(10584319,20452894420997,2),(10649855,0x4320340420480283e,2),(562258391,20488403314693,2),(10715391,10011830608,2),(11475927391,4307030,2),(1367406655,0x12ae1f4220270165582580a,6),(2734805119,0x83e04802813821,2),(24160303191,0x4ae15b06802c2585e,2),(12617022527,0x95e0341f42f04b,2),(13153893439,19293387378763,2),(323080407,0x12c057cae9500160d02d815,2),(9011455,10188742669,2),(188934207,0x95709a10c0a866,2),(102857759,0x41a18730c02c0980a,2),(197243007,18494389266445,2),(12812479,0x98a2bc0541a05e,6),(16307896511,20986649006150,2),(10911999,21004046954514,2),(90245183,2442,2),(98633791,2444,2),(331789109399,5067163,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_2 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Block7_2 = true := by decide +kernel
def h0Block7_3 : List NodeSpec := priorityNodes 11 [(5251346647,4540827,2),(5217800407,4532635,2),(9294671999,8850061365,2),(14336127,4321691,2),(14303359,4321691,6),(43696255,0x4e29c43866b4139c6,2),(60473471,4274630,2),(20870881375,17783136045527,2),(14294196351,5236747,2),(6504575,0x107c0590f82804e01c0021e,2),(934170593375,5791850,2),(52882620543,5236747,2),(37715959935,5236747,2),(30687447,0x81a7d02b555062,2),(76824671,0xbe9554fa80d039,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_3 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Block7_3 = true := by decide +kernel
def h0Nodes7 : List NodeSpec := h0Block7_0 ++ h0Block7_1 ++ h0Block7_2 ++ h0Block7_3
lemma h0Check7 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Nodes7 = true := by
  unfold h0Nodes7 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨h0Test7_0,h0Test7_1⟩,h0Test7_2⟩,h0Test7_3⟩
def h0Bucket7 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes7
set_option maxRecDepth 200000 in
lemma h0Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 7 xs.toFinset) h0Bucket7 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0Bucket6Ok h0Check7
def h0Block8_0 : List NodeSpec := priorityNodes 11 [(303605,17660930695178,2),(28332247,0x40981002403807815,2),(98578687,0x104808c1102003c0740c81802e00c0101b03404805015,6),(106967295,0x20d0198310600900c00601408009836,2),(794879,0x21141e81608e0901003e0420f01d815,2),(29891647,0x84d0981240f015,2),(1687743,0x4290390a202010015,2),(462975,0x107c0a4140270b009804015,2),(98603263,0x42d83906c11817815,2),(102797567,0x8650be16c0a80a,2),(473993471,0x43585f02a04c2d865,2),(2539775,0x8710480802f83e00a1bc2e85e,2),(2572543,0x10f01dc1e0370481e40285d07c1d82305e,2),(490770687,0x21e41c83702616c36012,2),(26752063,0x84c0961f03d846,2),(213983423,0x85c09a1180d05e,2),(222372031,0x88406c20c340240c817840015,2),(1400959,0x20f81488611221c2f06c,2),(2769151,0x8880ca1741782410c1902f015,2),(1082167551,18760836771861,2),(778495,0x86c06e0800908b0262282e815,2),(168191,2137,2),(3326207,0x44b0930780802e83e12825449015,2),(25705535,18898489596053,2),(1695871,0x20f81489d13627047815,2),(6783477,0x2294510a11400bc03005,2),(7934167,0x4550131522a00a015,2),(26276095,0x116a2c4578ae15627c4f0ac1520600d015,2),(30470399,0x8bd1761941201a00c08009864,2),(3129599,0x2090100340c80183a00a,2),(90247263,9407844453,2),(23612479,0x42603418a310258c6,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_0 = true := by decide +kernel
def h0Block8_1 : List NodeSpec := priorityNodes 11 [(1876095,0x209c0b01118e2dc17815,2),(17895679,0x8cc1681742303c0b60841f015,2),(19992831,0x8cf08c0f01081d0b60f80a80a,2),(30478591,0x2334548640b60bc04015,2),(32575743,0x46b0d112a0542e81a,2),(356585727,0x23242e8130c80602d8d6,2),(3162367,0x10782a41f00600a0d82f08f,2),(1216418047,0x46683c02616c54836,2),(22565951,0x84c0683686c846,2),(180494527,0x23284a84c01623c0505e,2),(188883135,0x10c820c1b0240bc0546f00a,2),(1990783,0x2058088e20bc38470021,2),(3948799,0x8d602a174120081c00d82f00a,2),(1619071231,19404888928277,2),(827647,0x11521741f03c0420800a0e41c604c31015,2),(17903871,0x47401d0781181f015,6),(22098175,0x8eb1d2398728080303b057015,2),(26292479,0x22b8120e90403b032015,2),(2638079,0x42f83e0781900a88f,6),(73478399,0x23a41a8240400481f015,2),(81875039,0x80d1ee3d8610ae,2),(200959,2248,2),(21519423,18168756551750,2),(4440191,9638553836,2),(9208063,0x4819010400185483420416c3a00a,2),(20472895,0x42603420a41026813,2),(4669567,0x20580890a2124202f00a,2),(18678261,19911494101002,2),(18940395,19937263910938,2),(9601279,0x122e4583603c0720803a015,6),(9732351,0x48f11d14a1741e03e04247010015,6),(4931711,0x20f81481624048447815,6)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_1 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_1 = true := by decide +kernel
def h0Block8_2 : List NodeSpec := priorityNodes 11 [(22122751,0x49382402a02032125,2),(9994495,0x216c1e00600a4b4101290ca2a496074,6),(32608511,0x83902a0bc1b134,2),(34658431,0x80a2764e49f065,2),(69308671,0x93d2660549f00a,2),(10191103,0x106e514a205b0780800583e2845180908f,2),(5161087,0x41f02905052ca5064,2),(10256639,0x94c0c85281b02f01023c10015,2),(2801919,0x41e0390480841003402a1903a01a,2),(28422399,0x9520140181b150,2),(4145407,0x95414a1b02e83c0480800583e00c5541b00a,6),(17333311,0x1068090ac950014068ac04b,6),(34662527,0x4528420720d00501a2b053ca804b,2),(18381887,0x8820c85880d036,2),(413823,0x1152044b48132d059c0683e,2),(10025087,0x12d85acb516601a0280d015,6),(15267967,0x96c2cc4f89e80d2da0680a80a,6),(32507967,8699029574,2),(69208127,0x96e0145980d015,6),(1720821,20762069794837,2),(876799,0x4ba05d0420740e0082e60803100a,2),(487551,0x20b00b0070501784780a,2),(1024255,0x41b8082f45e41000b0725e047862,2),(1073279,0x82802c5f847836,2),(2113791,0x12fe0d80400604023c2f00a,2),(2474239,0x11521741202003a028041810260d831015,2),(1366079,0x8420686080d046,2),(1890367,0x97f10460c0d036,2),(452671,0x10680900998527c0540d00a,6),(897151,0x84207c0d0098150344f49f00a,6),(1370175,0x98802a4f40d00a,6),(755417279,0x98a18c1342602401623c0a85e,6)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_2 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_2 = true := by decide +kernel
def h0Block8_3 : List NodeSpec := priorityNodes 11 [(822526143,0x109812c058c63181784780a,6),(2212095,0x22a42e837068080090083146242d815,2),(2277631,0x45700b18c0f01c83711e178c600a,2),(456767,2084,6),(355468503,0x26500999332464406995,2),(721487063,21141557201310,2),(889259223,21167339509974,2),(1057031383,0x4cd0a534668809839,2),(357565655,21055633011102,2),(359662807,0x9a40266580a99e,2),(209913047,0x9ac3566a45499b,2),(226690263,21296252289435,2),(511804031,0x4d99522fe2b81c836,2),(669002879,0x9bf37c6f4dd9b401a0285719b,6),(5947519,0x4e29b207c09ce21a738c6b4e199b,6),(186122879,2487,2),(6111359,0x2730e41a607c66ce588f,2),(621216863,0x4ea9d43a60e4cb19e,2),(656424063,0x2780ef9de3ba768d303e01a75c3a196,2),(6176895,0x2788089e332c118f09d7,2),(6275199,0x82804e028f40ec,2),(5150617835,0x9ec3da7acf701a,2),(198705791,0x4039ef0347c4098d6,2),(9227481215,0x9fc3f60f8fd1f93ea7b8068113ec2d0fb81a,2),(8891977855,21966601900102,2),(4278284415,0x27f4fc1b30668000c013,2),(121111767,0xa0335004c06996,2),(273679575,4231574,2),(380634327,22033262137776,2),(403703029,0x503208412698d49fd,2),(6471807,0x141c82813a0f41a658d300a,2),(18723397727,0x142884c0d009424844230ae,6)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_3 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_3 = true := by decide +kernel
def h0Block8_4 : List NodeSpec := priorityNodes 11 [(5783679,0x202c00a170721190b0b4,2),(62128767,0x50ea1c3846d85499b,2),(18454978735,0x51101a3b8045102211a00d0051db,2),(6537343,0xa2644a6585481d,2),(18454995039,0x9bd07c8ad141bc3748a8cd80a,2),(6570111,0x82804e8a11722f3648b4cd80a,2),(53740159,22430676765083,2),(18186576047,21657591673068,2),(6602879,0x20f814a3646a8dccb0a9,2),(55837311,0xa380e86800999b,2),(5816447,10976698438,2),(6209663,0x80b47c8f51e23f0688ec0883e,2),(17649786975,21380390056172,2),(6635647,0x205808a40014904cd812,2),(15336063,0x2909199b234c0d00999b,2),(15860351,0x290ce098e00e015221d015c0e452813,2),(17381384287,0x523a462a4914df0ae,2),(5849215,11039447423,2),(188910807,0x52624e49a92ccb996,2),(353373399,0xa523229442f24f,2),(1639987415,22703278029206,2),(6832255,0x83e0529512d05e,2),(6865023,0x816022000eb85e,2),(389024983,0x14bc04c06a564ba2a52e1e5,2),(6897791,0x8160229592f85e,2),(277120639,0x5301fb4c47a8cb85e,2),(11442073727,0x5332643fa7f0fd83e0149945281a,2),(120065239,4262294,2),(6257979607,22883665471899,2),(94899415,11089940894,2),(6963327,0x20a013a6a4a8958cb062,2),(60556927,0x53726d4d89612b862022928e8039,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_4 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_4 = true := by decide +kernel
def h0Block8_5 : List NodeSpec := priorityNodes 11 [(6799487,22946269743198,2),(6996095,0xa714a8188cb039,2),(124259543,0xa734c204c3119e,2),(7061631,0x105009d3aa614e8958cd862,2),(53216895,0x4312774a89d91899b,2),(107482327,0x53c1960249e43106c,2),(7094399,0x20f814a7a32c9ed2a062,2),(7127167,11257712854,2),(7028863,0x54000a07c8644781d,2),(25955543,0x540a56152a08cd862,2),(7159935,0x205808a83336a112b062,2),(7192703,11295461477,2),(7323775,0x20f949291336179480d8,2),(7356543,0x41f29652a66c47815,2),(7389311,0x20340380153223ceb8d8,2),(7422079,0x203403a9e11ea314e8d8,2),(195562111,0xa8d15c1881a196,2),(3279984767,0x155037153aa654aa880882101aa9151818,2),(103290101,0x22884f2a9554a31449fd,2),(7454847,11325063600,2),(7487615,17935947073942,2),(7520383,23504938373552,2),(7585919,23539147139478,2),(7618687,11497030064,2),(7651455,0x41f029514ad95b996,2),(7553151,0xaae1b004c091b0,2),(7684223,11538590102,2),(15075967,0x54697a1b02b83108f,2),(7716991,0x40680715cb0160996,2),(7848063,0x82804eb2c0a865,2),(1874884703,23753125163065,2),(7880831,11606603877,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_5 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_5 = true := by decide +kernel
def h0Block8_6 : List NodeSpec := priorityNodes 11 [(7465865311,17681097943276,2),(7913599,0x82804eb44050ec,2),(3716159615,0x15ac7b45483e04e029691f3540b396a9b0,2),(3548420223,0x2b716daa83fa3706583e052b6054818,2),(3481327743,0xada15c4cc1c9fd016b6d6e8a9,2),(12985659519,0xad93fa5487a8a95b6b780c0ae,2),(7197495391,9361707440,2),(7946367,0x82804eb205c1b0,2),(7979135,0xae40bcb8c54821,2),(7130402911,8850467248,2),(8011903,9584021936,2),(8077439,0x105009d74ae15d066c7f00a,2),(294657199,17844423133616,2),(8110207,0x83e052bac899b0,2),(8142975,0x80b002bb9768ec,2),(8044671,0x8280260f8769b0,2),(26483887,0x15eabcd640115e8bd85299b,2),(8175743,0x203403af7336be01100a,2),(8208511,0x4058015f6be82f065,2),(244189279,24175298738277,2),(1505757279,0xb0760ac1181839,2),(138428510,0xb11620a68091b0,2),(906233951,0x2c4988b1061e074091b0,2),(1530923103,0xb1360ec19809b0,2),(3020163167,0x588b0e618c1c35012628c418a81d,2),(7969181791,0xb17624a698b06a,2),(2076182623,2840,2),(773850239,0x58d319612a7cf503e0d40d0311b0,2),(778044543,0x9f23e01780e996,2),(3867170943,0x16461f9913216401b01f01501ac758e01a,2),(3800078463,0x59080b5507f406b25196c81920ae,2),(3732985983,0x1640c7c91b2224e490069fd0160e593321,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_6 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_6 = true := by decide +kernel
def h0Block8_7 : List NodeSpec := priorityNodes 11 [(14663299199,0x590b203f67f40b01165074593839,2),(14327795839,0x2c899031e3fe2fc5f03e654ca59081a,2),(13992292479,0x405b2c6422b995839,2),(6031605,24268701712394,2),(87033951,8851573168,2),(23332415,24278414248368,2),(16941183,11849126320,2),(16810111,0x20a013b2f634cb98099b,2),(396363871,0x44b000662c681f1b0,2),(17006719,24622083035568,2),(17137791,0x59cb016706585706a,2),(467667039,5026224,2),(202938779743,0xb3e67880457021,2),(7600165079,0x5a1013682035a00ae,2),(18352223,2248,2),(1111492703,0x414b4768cc0435196,2),(2143291487,24808125583792,2),(1186990175,8753869232,2),(17334399,12117561776,2),(610272383,0x15f8740950056141a80e865,2),(8339583,0x40b011694c05a599b,2),(29460832431,0x2d501a01a6a6d4808839,2),(421529695,0x4e801a6aec25ab039,2),(17399935,0xb5832cd645706a,2),(217056383,0x16b6bf0e806a024c2831065,2),(16875647,0x58d0076b8d742f19b,2),(4118829183,0x16d4da59187e0d8d980d012,2),(3984644223,0x5b536803a49c921fd016da5b5812,2),(15334428799,0xb6a6ce7fcfe8bf024da40e996,2),(8405405871,8766130608,2),(84940895,12230658480,2),(22809151,25120609571248,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_7 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_7 = true := by decide +kernel
def h0Block8_8 : List NodeSpec := priorityNodes 11 [(17662079,0x82804ed90151b0,2),(17727615,0x202c00b726e217c2f06c,2),(392173663,0x8966e8dbc109b0,2),(17793151,0x4140276eadbc481b0,2),(17858687,0x20a013b796f0cd0cb0a5,2),(463476831,25258091997590,2),(8338354271,0x5c037f6dcdf9be8d6,2),(1178605663,19090597022128,2),(17989759,0x816022e088d1b0,2),(18055295,0x80b002e15c20ec,2),(417339487,0x2e29b7356072e2ccb0b4,2),(18120831,0x203403b8d718e38cb0b4,2),(18186367,0x80b002e41b60d6,2),(4253063295,0x2e61cbb961a43341f03472a08409b99,2),(41423999,0x20f40b03e042e70229b0,2),(1050678399,0x1742e7c06b9b2c2e79d019b,2),(396372213,0x8a573a289cd1fd,2),(229643391,0xba267a8081f00d2c2e91d3196,2),(18514047,25662069239826,2),(18579583,0x405801762ec008839,2),(84095,0x48902876aed1d9818,2),(51394687,0x5db8d8062060023b2034ed805039,2),(306204887,0x177609c0c00a7740a80f8a9,2),(495743,0x202c02bbd77807811021,2),(1089663,0x202c02bc077e0e019839,2),(18645119,0x178c449e4bc778af21e2018,2),(1292001375,25927367037022,2),(18710655,8988614750,2),(1224925279,0x80d7966cc1f05e,2),(18776191,18085889400926,2),(616585343,0x21fc3f05a0340543106c,2),(1302655,0x21e0068770ec1b43c85f,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_8 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_8 = true := by decide +kernel
def h0Block8_9 : List NodeSpec := priorityNodes 11 [(18841727,0x2f54893d67a8f4de9018,2),(964784255,0x5e783106009c0c19606a6cc05039,2),(50600681599,0x408bd87a2029eb9fd,2),(18972799,0x2f7c87be07bcf75ee00a,2),(19038335,9194260623,2),(348180695,4311183,2),(19103871,9298888847,2),(1728639,0x4890287caf91f181a,2),(2298515583,0x2f985001800e28c0d06a00ae8c5886c,2),(2231423103,0x5f58a00302900d06a00a2885e8a5,2),(19169407,17639361442198,2),(2533412991,0xa4f7da2f452996,2),(1400967383,0x5f901a7ce2c05686c,2),(1417744479,0x5f981a7d22cc36039,2),(1908863,0x202c02bf57e82e85886c,2),(1925247,0x202c02bf97f03005e8a5,2),(12386687,0x17faff0fe8c1068fe83a06a,2),(19234943,0x24481440180406a00018,2),(6373503,26426946376086,2),(2843777151,0x23746e0d119a05431021,2),(2130747567,0x30240d0d00221904783e,2),(683710591,22432660670875,2),(2063671471,4550750,2),(19300479,8728703070,2),(717265023,0x51c0c90423340999b,2),(1468084319,0x8118183341c85e,2),(19366015,19357472196702,2),(1426277247,0xc1033632607021,2),(893425791,0x23746e0c903005431021,2),(901814399,0x5540dc07c0845499b,2),(12517759,0x2fecfe8ce07d0243a05e,2),(4865606527,26521482119201,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_9 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_9 = true := by decide +kernel
def h0Block8_10 : List NodeSpec := priorityNodes 11 [(9110067327,0x4690cd5510441099b,2),(19497087,0x48902882806a09818,2),(6406271,12977197462,2),(457265367,0xabc01a1781f064,2),(675326079,22432727654811,2),(1384206431,0x60e80d8382c8750ec,2),(4472959,0xc1f83c3b80906c,2),(1434538199,0xc238443a452812,2),(4505727,0xc258483a4090a5,2),(10420607,0x1812fecfe85f07cfe87908f,2),(1493262511,9319964815,2),(314659031,0x6148158503cc57012,2),(19562623,0x24481442d85d0be1601a,2),(17203327,0xc338640161a196,2),(3439382655,21638838000022,2),(19628159,9298888798,2),(1434546271,26861417646174,2),(19693695,26872209590366,2),(4735103,0x41f00a8790ee1d01a,2),(4800639,0x4088098810fe1f00a,2),(4866175,0x1016016210118824641f06c,2),(19759231,0x20fa2344501511e2201a,2),(19824767,0x204404c4b8991362500a,2),(5062783,0x31462844f89c0f89701d,2),(5554303,0x40a80d8ab1522981a,2),(19890303,0x40a80d8b006a2b818,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_10 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_10 = true := by decide +kernel
def h0Nodes8 : List NodeSpec := h0Block8_0 ++ h0Block8_1 ++ h0Block8_2 ++ h0Block8_3 ++ h0Block8_4 ++ h0Block8_5 ++ h0Block8_6 ++ h0Block8_7 ++ h0Block8_8 ++ h0Block8_9 ++ h0Block8_10
lemma h0Check8 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Nodes8 = true := by
  unfold h0Nodes8 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0Test8_0,h0Test8_1⟩,h0Test8_2⟩,h0Test8_3⟩,h0Test8_4⟩,h0Test8_5⟩,h0Test8_6⟩,h0Test8_7⟩,h0Test8_8⟩,h0Test8_9⟩,h0Test8_10⟩
def h0Bucket8 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes8
set_option maxRecDepth 200000 in
lemma h0Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 8 xs.toFinset) h0Bucket8 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0Bucket7Ok h0Check8
def h0Block9_0 : List NodeSpec := priorityNodes 11 [(143615,0x42b83905e0a8120230400780300001800c04015,6),(168191,0x43f0570be0bc1000d0001743285c0101680a85e,2),(176383,0x89a12015c1c82f0400580888e01023447815,2),(192767,0x8b816a2bc528570520800400014e27c0300a,2),(200959,0x46e0571a40f81000d0103206b0ca00c3240505e,2),(209151,0x4768eb1d22942b83e052080040061ce0bc73015,6),(217343,0x9071fc15c1001d01001c068fd00c1787e00a,2),(225535,0x123444c2b83905e0900400021808047815,6),(233727,0x49c05705e0209992400c0902d92211e48c0a820,6),(241919,0x114a1b01c8210400342b94f034028a7015,6),(129151,0x43182702c044099661d8594b200d,2),(250111,0x22a41001200c15c2f166034028b2815,6),(663807,0x10ae0901101b0100180005e0320804780a,6),(696575,0x42b80800c0001f0330640a41208f0bc0c405020,6),(712959,0x98418c2d01082003a0482b936034054c000a,6),(372863,0x26106a86304e0440680a27a4f09d065,6),(729343,0x4570390520802b93d0340549e00a,6),(194623,8866838592,6),(1491135,0x10840901001501406820057,6),(745727,0x46305e02a028478240341002b820,6),(1523903,0x121e2040d01510402812057,6),(132214,0x4c80131d863cc700d,2),(263286,0x4ce98e34201ccf196,2),(525438,0x9b5368004001b236269cd31a53806dccf19b,6),(688767,0x13946d40b1c901a71cc70ec,2),(754303,0x2790ef9c034c01ce79ce01a6582319e,2),(819839,0x9e736a0a4039e601a638050ec,2),(885375,0x9f334c0d01380d3d2638cb046,2),(5587071,0x9fd3c8448148160227d40d00d3dc060fa18e,2),(5637335,0x10c601cd60131d8320cf00d,2),(5899479,0x101a6bc318e51d81180399e,2),(3736191,0xa0c36a058038004160345499e,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_0 = true := by decide +kernel
def h0Block9_1 : List NodeSpec := priorityNodes 11 [(3867263,0x2854e002902c03423210022664cc0ec,6),(3998335,0xa2336a0350d8164346590c0ec,6),(4129407,0x14586d403a290520347619e,2),(8520319,0x100e8c0cb01601a708558ec,2),(9044607,0x9c21ac058069a63400445d846,2),(5619839,0x28e86a82703a0d0ef1da01a764ec011,2),(9831039,0x40382901a7087619e,2),(10355327,0x9a60680a41386501a68c18046,2),(5652607,0x27906a8270226ecdf00d3722b8dc046,2),(133238,0x263d272500bc66c03996,2),(624255,0x14b27280b25500e924e3865,2),(689791,0x2940f21e03be01c3299e,2),(755327,0x14b279c14a5b00e924050d6,2),(820863,0x29592a1f33362941c82732c7a92485e,2),(6668415,0x81a4c67908902903005808a6400e7f52485e,2),(5377239,0x14a00a53386500e3206b05e,2),(3606143,0x52ca0c4d29510399e,2),(3737215,0xa5942a0446b0074d6928cc065,2),(3868287,0x144888c03a7032c9510c0d6,2),(3999359,0x2965160114e401c5299e,2),(4130431,0x14ac0e40b1964ec01c3605e,2),(8783487,0x4140070c809c2f0d6,2),(6701183,0x28e86a86504e0741a27f4fc01d3e811,2),(9569919,0x14a82941382203a9600d99e,2),(10094207,0x41400704e1942f036,2),(6733951,0x27906a8270220054380715ca186b05e,2),(135294,0x408a8b0bc034d8196,2),(266366,0x152823c08a9300ea200a8d6,2),(625279,0x4f229711ea60cf196,2),(690815,0x13ce23c14a9b538a20050d6,2),(756351,0x4f99b004e0444a996,2),(7225471,0x1360790890750520355101154e0615088f,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_1 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_1 = true := by decide +kernel
def h0Block9_2 : List NodeSpec := priorityNodes 11 [(2427519,0x151c2bc08800556295461b0,2),(2558591,0xa8e32c0442f00d55aab0640d6,6),(2689663,0x2a387481155e01c6b1b0,2),(2820735,0x54719620c0455980d56266c050d6,2),(2951807,0x40b007022a3c6b1b0,2),(3082879,0x2a3c08a8901a4884a88f,2),(7258239,0x2aec3182700e04d5d011572ae0cb00d,2),(9308799,0x99604e0595e99b022a3c050d6,2),(9833087,0x547a8906409c0981115ca301808f,2),(7291007,0x11aa7903183904e03562011586b084a996,6),(270462,0x1594a5004ac700eb140a865,2),(560767,0xaca3c877c14acc0127340d065,2),(626303,0x159479c04ad0052b14050ec,2),(691839,0xac83e67a8cd8ae15209cf48095926c02f01a,2),(7749759,0x4f21120ea0a406adc5ae0600b1b0,2),(2297471,0x5650af5be2e1641b0,2),(2428543,0x56501a01a17804ae25c02b8640a9,6),(2559615,0x15943a4148095ca01c571b0,2),(2690687,0x565106034035738095cc66c5480a,2),(2821759,0x15904685703900eb24899b0,2),(2952831,0x20a00d0095d8489650ec,6),(7782527,0x2aec3286304e04809af15e00597780d,2),(9047679,0x2b1854827036068092f2336b241100a,2),(9571967,0x40d0095f20c165065,6),(7815295,0x4f206304e0356a2ce02c0e5698ec,6),(2113630,0x160467814afe5fabf0e6865,6),(984191,0x5851e43be6117f02915cbf0e6839,2),(4210782,0x153800188afc0d40a4d8196,2),(8405118,0x5849ea32c0d0f98273601798599b,2),(8241279,0x24483a816022035901e4644c6c0d1b0,2),(2753663,0x58518405208c0f0006160e5849b0,2),(3540095,0xb0a3366102f00d65ac342c865,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_2 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_2 = true := by decide +kernel
def h0Block9_3 : List NodeSpec := priorityNodes 11 [(3802239,0x16146104c82966001c329b0,2),(4064383,0x59bb0a3366119b00d66a65999865,2),(18352223,0xb020c6cf0148ae1906c19d05e,6),(9176191,0xb0a30836c3180d67866d9db016100a4640ae,2),(9700479,0x16143a431b3f308394571b0,2),(20449375,0x1000d1431b44052054cd85e,2),(10749055,0x4c202900ec2c329b0,2),(11273343,0x249003b0b60066d8089527048832b0a,2),(8274047,0x157618c1381602204da6839686d30cd80d,2),(13370495,0x1614854c2029022355a719b69e2b8cc039,2),(13894783,0x2c29118296a266cc2350612860cb039,2),(14943359,0x99b3080a5aa99602cc2c55865,2),(15991935,0x13362f00b31a6162f58a85e6b42ec32b0a,6),(8306815,0x14743541380d00e0d1af8ae62cd78cd811,6),(37225599,0x99b3080a413b6015cc2c18039,2),(8421502,0xb643d46581a01d0247ccf48276c46c02f018,2),(17465471,0x48907502c04406b6a6ca068149b0,2),(2493567,0x2db01181e6c4d90151b0,2),(3279999,0x16d8d8c148180bc035b836f6dad902c812,6),(3542143,0x5b7b6c13205809373022d90481b0,2),(3804287,0x5b6337052061bbb76666d90cb012,2),(17307743,0x16f601dbd0ec1900a46b05e,2),(10226815,0x16c844c5281d00ed888d1b0,2),(10751103,0x20a414018706489b60ec,6),(17531007,0x15763585482702c04409b8870e0a5c300d,2),(14421119,0x16c62b00c016024e24558296c46582f0b4,2),(15469695,0x41481871e2edb60d6,6),(17596543,0x14743b05282701a01c1a393724e4414811,6),(18251903,0x13c86c03a82902c0440688f034061ca161,2),(2233471,0x2e741c82a2c2e6c0f1b0,2),(3019903,0x4b082701a1642308f,2),(3282047,0x96104e01c4a9b0,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_3 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_3 = true := by decide +kernel
def h0Block9_4 : List NodeSpec := priorityNodes 11 [(3544191,0x258413b9e666e6ccb046,2),(3806335,0x17362e0528342c2e74579b0,2),(4068479,0x2e6cb08dc1ac3481389501ae9064046,6),(8655999,0x25845286404e01c231b0,2),(9180287,0xb9b2c23f81a02703a0340999e,2),(18317439,0xabb0c605808ba81d8ea5d380d,6),(11801727,0x173481c548132c2e6d0619e,2),(12326015,0x2e6dcd1972c20f8138ec022118cc08f,2),(12850303,0x96115219013bac32ce6d0c095,2),(13374591,0xb9a44e584138130240441a19e,2),(18382975,0xa3a1aa03403bae1acebdd6811,6),(18448511,0x2790878d50c60440680112a11832961,2),(79999,0x215cc210f052009d900402c02803996,2),(49293439,0x20680c01501401c13bb977008c11021,6),(53487743,0x10460680abbe76c0cc0f039,6),(405631,0x4f218404e11c1d83a07c0840b007,6),(219199,0x8510a009c0b007,6),(1237119,0x85701af04c210f052005e1859784044cf05e,2),(228612223,0x4003c302603431065,2),(43014271,0x41402701a17c4785e,2),(47208575,0x41c82702c0440387e0520344785e,2),(237000831,0x2f39e686b0260342f86c,6),(1286271,0x157658c1405f07c09c098710de1b80880d,2),(1302655,0x13c86101380d0f21dc3b06d07c1e008846,2),(245389439,0x10ec17c3680d0f204c0906c,2),(266360959,0x82811e0342f065,2),(1646719,0x22302b98421e0a400bd17a00440399e,6),(1663103,0x136015cf2112052f6ded0117b20600388f,2),(88191,0x42f87e0b41640b00d,2),(40921215,0x104e0580a80a7c20441088f,2),(45115519,0x4138157c401c1c88f,2),(1679487,0x2790c20271260f80889612224803895,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_4 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_4 = true := by decide +kernel
def h0Block9_5 : List NodeSpec := priorityNodes 11 [(1712255,0x215c878110120044f3a30527f40399b,2),(1859711,0x227c2b91202c045f6bec00e068149b0,6),(13142143,0x40d01802c05403bf17e02d45886c,2),(15239295,0x10500600abf77ec2f4578a5,2),(1581183,0x28e8b782804e0040006411e0a403811,6),(1941631,0x133c15cc210f02202406bfe7fe178640d6,6),(784373887,0x2ffd9d013190034310d6,2),(1958015,0x99b0ae790890d60500580880001a324cb036,2),(792762495,0x4643a5026034648d6,2),(8951935,0x30186a81180a0e43180d198118760d6,2),(10000511,0x30205482980e18c068d219e1181c8d6,2),(12097663,0x105009c0d00d8140585705e,2),(14194815,0x11920a40b0070220346b05e,2),(178296959,0x8dc1922b80886401a17854821,2),(1597567,0xa3a2de1c014027002000038ae01a23c1b011,2),(608213119,0x4570700bc03454836,2),(38836351,0x218c068271b82b81b05e,2),(64002175,0x8c90500342f0d6,2),(4374655,0x10ae610878110120060919e1d801c72846,6),(4407423,0x10ae790890ec02c0460a8074086c073046,2),(8956031,0x30620b8d50c63b06b064,6),(11053183,0x10520580ac1a8322b0758ec,2),(13150335,0x30841442004e01c32046,2),(1335423,0x14745bc14027002000320ae0be23c03811,6),(36743295,0x184e0ca130271d611857036,2),(104575,0x2348088dc1920a46400d,2),(4571263,0x10ae66c8781101200406c2b8547f41485e,2),(4604031,0x215c8901602200218c3001a67814996,2),(10008703,0x10340600680786a3f85885e,2),(12105855,0x120e06008c365643f85e85e,2),(4636799,0x28e8b78272000d0819011fe03414811,6),(4702335,0x242c2b984052044048010e601e1c99e,6)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_5 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_5 = true := by decide +kernel
def h0Block9_6 : List NodeSpec := priorityNodes 11 [(4767871,0x9b021815cf20290340580891087a0600388f,2),(4833407,0x51d16f1aa1940e91522809c03811,6),(4898943,0x4f21841aa0448e11b00e2b88f8d6,6),(4964479,0x215cc202902202400c4301a488cf064,6),(4997247,0x10ae7901481a02c0440044801b124cd88f,2),(5030015,0x51d16f1aa0749512925603498011,6),(5128319,0x2790c20d5022510a194201a51c57095,6),(438399,0x10ae05ccd81101a024038018a46c01485e,2),(446591,0x2aecb1816022358549732e40a4ba80d,6),(503935,0x99e0ae6102f01101a024038018ac0c0d817f,6),(520319,0x2aecb18160222a41c97a2ee5d8bd80d,6)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_6 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_6 = true := by decide +kernel
def h0Nodes9 : List NodeSpec := h0Block9_0 ++ h0Block9_1 ++ h0Block9_2 ++ h0Block9_3 ++ h0Block9_4 ++ h0Block9_5 ++ h0Block9_6
lemma h0Check9 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Nodes9 = true := by
  unfold h0Nodes9 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨h0Test9_0,h0Test9_1⟩,h0Test9_2⟩,h0Test9_3⟩,h0Test9_4⟩,h0Test9_5⟩,h0Test9_6⟩
def h0Bucket9 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes9
set_option maxRecDepth 200000 in
lemma h0Bucket9Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 9 xs.toFinset) h0Bucket9 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0Bucket8Ok h0Check9
def h0Block10_0 : List NodeSpec := priorityNodes 11 [(254,0x13085bcb182805209c0b0070ae09000800,6),(1150,0x82904e0580680738463800163,2),(2174,0x20a4138164b092400007,6),(4222,0x82904e01c0b01151ea200016f,6),(8318,0x20a413807592b1400016,6),(16510,0x104e05803829616bf000184,6),(32894,0x209c0b0076c4d8400029,6),(65662,0x20a41401600ee5000027,6),(75903,0x10520a0138230060080b007,6),(88191,0x2aecb182904e0443f05a0b20580380d,6),(92287,0x105209c4d08d1180440b007,6),(100479,0x209c0b0b513e27814807,6),(104575,0x55d96304e0586e0c91900a40380d,6),(108671,0x209c0b0eb1cc39414807,6),(112767,0x104e058838fc1f603403829,6),(116863,0x41481621842c14007,6),(120959,0x10520581412324403403827,6),(340095,0x40b00703205c14029,6),(356479,0x20a00b0070620c014827,6)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test10_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket9 10 h0Block10_0 = true := by decide +kernel
def h0Nodes10 : List NodeSpec := h0Block10_0
lemma h0Check10 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket9 10 h0Nodes10 = true := h0Test10_0
def h0Bucket10 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes10
set_option maxRecDepth 200000 in
lemma h0Bucket10Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 10 xs.toFinset) h0Bucket10 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0Bucket9Ok h0Check10
def h0Block11_0 : List NodeSpec := priorityNodes 11 [(126,8757708800,6)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test11_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket10 11 h0Block11_0 = true := by decide +kernel
def h0Nodes11 : List NodeSpec := h0Block11_0
lemma h0Check11 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket10 11 h0Nodes11 = true := h0Test11_0
def h0Bucket11 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes11
set_option maxRecDepth 200000 in
lemma h0Bucket11Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 11 xs.toFinset) h0Bucket11 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0Bucket10Ok h0Check11
set_option maxRecDepth 200000 in
lemma h0Bound : Lower h0R h0G 12 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,9,13),(VAR 3,5,13),(VAR 4,6,22),(VAR 5,5,37)]) (by decide +kernel) h0Bucket11Ok (by decide +kernel)
def wit : List PEqualNP.CircuitLowerBounds.Gate := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 4]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 6]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 4]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 8]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 9]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 12]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 3]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 14]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 15]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 16]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 17]⟩]
def wo : Nat := 18
lemma wit_mono : PEqualNP.MetaComplexity.Monotone2 ⟨wit, wo⟩ := by simp [PEqualNP.MetaComplexity.Monotone2, wit]
set_option maxRecDepth 100000 in set_option maxHeartbeats 0 in
lemma wit_eval : ∀ r : Row, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput6 r)) = ((4277071592 * 2 ^ 32 + 4207470728) ||| ((4277071592 * 2 ^ 32 + 4207470728) <<< 64)).testBit r.val := by decide +kernel
lemma low_root : Lower (varsOf 63) ((4277071592 * 2 ^ 32 + 4207470728) ||| ((4277071592 * 2 ^ 32 + 4207470728) <<< 64)) 12 := h0Bound
end PEqualNP.Outside.L_meta_46856
theorem PEqualNP.Outside.L_meta_46856 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071592 * 2 ^ 32 + 4207470728) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071592 * 2 ^ 32 + 4207470728) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hcs
  exact PEqualNP.Outside.L_meta_46856.table2_of_lower (4277071592 * 2 ^ 32 + 4207470728) (by decide) (by decide) (by decide) (by decide)
    12 PEqualNP.Outside.L_meta_46856.low_root
    PEqualNP.Outside.L_meta_46856.wit PEqualNP.Outside.L_meta_46856.wo (by decide)
    PEqualNP.Outside.L_meta_46856.wit_mono PEqualNP.Outside.L_meta_46856.wit_eval s hcs
