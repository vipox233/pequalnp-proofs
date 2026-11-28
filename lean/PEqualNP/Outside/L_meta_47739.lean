import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_47739
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
def h1R : List Nat := varsOf 11
def h1G : Nat := 0xee88ee88ee88ee88ee88ee88ee88ee88
def h1Pos : List Nat := [9,10,3,3,10,9]
def h1Neg : List Nat := [8,8,1,2,2,1]
def h1Mask : Nat := fullMask 6
def h1Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,45,36),(0xcccccccccccccccccccccccccccccccc,30,24),(0xff00ff00ff00ff00ff00ff00ff00ff00,51,3)]
def h1Steps : List (Nat × Nat × Nat) := []
def h1W : BT Decor := buildWiresBT 2 h1Base h1Steps
def h1AutoList : List (List (Nat × Nat)) := [[],[(1,3)],[(0,1)],[(0,3)],[(1,3),(0,1)],[(1,3),(0,3)]]
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
lemma h1Bound : Lower h1R h1G 4 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 3,1,9)]) (by decide +kernel) h1Bucket3Ok (by decide +kernel)
def h2R : List Nat := varsOf 13
def h2G : Nat := 0xfaa0faa0faa0faa0faa0faa0faa0faa0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h2Bound : Lower h2R h2G 4 := carry_of (swaps := [(1,2)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h3R : List Nat := varsOf 14
def h3G : Nat := 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Bound : Lower h3R h3G 4 := carry_of (swaps := [(1,2),(0,1)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
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
def h4R : List Nat := varsOf 15
def h4G : Nat := 0xe880e880e880e880e880e880e880e880
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4Bound : Lower h4R h4G 7 := carry_of (swaps := [(3,4),(4,5),(0,1),(1,2),(2,3),(3,4)]) (roots2 := Cofactor12058.R_10) (T2 := Cofactor12058.G_10) (by decide +kernel) Cofactor12058.low_10
def h5R : List Nat := varsOf 19
def h5G : Nat := 0xeeee8888eeee8888eeee8888eeee8888
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Bound : Lower h5R h5G 4 := carry_of (swaps := [(3,4)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h6R : List Nat := varsOf 23
def h6G : Nat := 0xe0e08080e0e08080e0e08080e0e08080
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Bound : Lower h6R h6G 5 := lift_of (z := 0) (o := 4) (essPairs := [(VAR 2,3,7)]) (by decide +kernel) h5Bound
def h7R : List Nat := varsOf 28
def h7G : Nat := 0xfff0f000fff0f000fff0f000fff0f000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Bound : Lower h7R h7G 4 := carry_of (swaps := [(3,4),(1,2),(2,3),(0,1),(1,2)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h8R : List Nat := varsOf 29
def h8G : Nat := 0xaaa0a000aaa0a000aaa0a000aaa0a000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8Bound : Lower h8R h8G 5 := carry_of (swaps := [(1,2),(2,3),(0,1),(1,2)]) (roots2 := h6R) (T2 := h6G) (by decide +kernel) h6Bound
def h9R : List Nat := varsOf 15
def h9G : Nat := 0xeae0eae0eae0eae0eae0eae0eae0eae0
def h9Pos : List Nat := [5,11,5,6,6,11,9,14]
def h9Neg : List Nat := [4,10,1,2,4,3,1,10]
def h9Mask : Nat := fullMask 8
def h9Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,103,100),(0xcccccccccccccccccccccccccccccccc,186,170),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,157,17),(0xff00ff00ff00ff00ff00ff00ff00ff00,226,130)]
def h9Steps : List (Nat × Nat × Nat) := []
def h9W : BT Decor := buildWiresBT 2 h9Base h9Steps
def h9AutoList : List (List (Nat × Nat)) := [[],[(1,3),(0,2)]]
def h9Autos : BT (List (Nat × Nat)) := btOfList 1 h9AutoList
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
def h9Block3_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3],[])]
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
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Bound : Lower h9R h9G 4 := lower_of_forestBT (essPairs := [(VAR 0,4,5),(VAR 1,4,6),(VAR 2,1,5),(VAR 3,1,9)]) (by decide +kernel) h9Bucket3Ok (by decide +kernel)
def h11R : List Nat := varsOf 7
def h11G : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Bound : Lower h11R h11G 4 := carry_of (swaps := [(2,3)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h10R : List Nat := varsOf 23
def h10G : Nat := 0xeaeae8e8eaeae8e8eaeae8e8eaeae8e8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h10Bound : Lower h10R h10G 5 := lift_of (z := 16) (o := 0) (essPairs := [(VAR 4,1,17)]) (by decide +kernel) h11Bound
def h12R : List Nat := varsOf 27
def h12G : Nat := 0xeeeeee88eeeeee88eeeeee88eeeeee88
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h12Bound : Lower h12R h12G 5 := lift_of (z := 8) (o := 0) (essPairs := [(VAR 3,1,9)]) (by decide +kernel) h5Bound
def h13R : List Nat := varsOf 29
def h13G : Nat := 0xfaf0faa0faf0faa0faf0faa0faf0faa0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13Bound : Lower h13R h13G 5 := carry_of (swaps := [(2,3),(0,1),(1,2)]) (roots2 := h10R) (T2 := h10G) (by decide +kernel) h10Bound
def h14R : List Nat := varsOf 30
def h14G : Nat := 0xfff0fcc0fff0fcc0fff0fcc0fff0fcc0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14Bound : Lower h14R h14G 5 := carry_of (swaps := [(1,2),(2,3),(0,1),(1,2)]) (roots2 := h12R) (T2 := h12G) (by decide +kernel) h12Bound
def h15R : List Nat := varsOf 31
def h15G : Nat := 0xeae0e880eae0e880eae0e880eae0e880
def h15Pos : List Nat := [13,14,25,14,25,7,14,21,11,22,21,7,13,25,22,11,25,22,13,7,21,22,22,23,27,13,11,27,14,21,30,30,25,7,25,11,21,22,7,7,11]
def h15Neg : List Nat := [12,12,26,10,24,3,6,20,3,6,5,6,9,9,18,9,17,20,5,5,17,26,19,19,19,1,10,26,26,1,28,26,1,4,28,2,28,28,2,1,1]
def h15Mask : Nat := fullMask 41
def h15Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x1df2f9dbdb5,0x18123ddb520),(0xcccccccccccccccccccccccccccccccc,0x1eaddeacb6a,0x489de04b6c),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf2f2fe5eeb,0x36400e0ec3),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x10ddf05b15f,0x34dc20b01f),(0xffff0000ffff0000ffff0000ffff0000,0x35e9f36694,0x34d9f34094)]
def h15Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(3,0,1),(0,0,2),(1,0,2),(2,0,2),(0,0,3),(1,0,3),(2,0,3),(3,0,3),(3,1,2),(0,0,16),(0,2,3),(1,2,3),(2,2,3),(3,2,3),(2,2,5),(1,4,5),(0,2,23),(3,2,23),(0,3,23),(3,3,23),(0,1,3),(1,1,3),(2,1,3),(3,18,23),(1,5,18),(0,0,19),(3,4,19),(0,19,23),(1,3,35),(3,5,19),(1,5,21),(2,3,24),(0,2,6),(1,1,40),(0,3,40),(1,3,40),(2,3,40),(3,3,40),(3,2,6),(0,3,6),(3,3,6),(3,4,6),(0,6,19),(2,6,21),(1,4,42),(3,4,43),(2,2,8),(1,8,21),(2,2,14),(1,4,9),(3,4,9),(0,0,29),(0,2,59),(2,2,59),(3,9,29),(0,1,10),(3,1,10),(3,4,10),(1,4,12),(0,2,13),(1,14,16),(1,4,15),(1,4,28),(2,2,30)]
def h15W : BT Decor := buildWiresBT 7 h15Base h15Steps
def h15AutoList : List (List (Nat × Nat)) := [[],[(1,3),(0,2)]]
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
def h15SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,5),some (subcubeFast 0 2,5),some (subcubeFast 0 4,5),some (subcubeFast 0 8,5),some (subcubeFast 0 16,4),some (subcubeFast 2 0,5),some (subcubeFast 2 1,4),some (subcubeFast 8 0,5),some (subcubeFast 8 4,4),some (subcubeFast 16 0,7),some (subcubeFast 16 1,4),some (subcubeFast 16 2,4),some (subcubeFast 16 4,4),some (subcubeFast 16 8,4)]
def h15Slices : BT (Option (Nat × Nat)) := btOfList 4 h15SliceList
def h15Specs : List PoolSpec := [(0,[]),(5,[]),(6,[]),(9,[(0,0,1)]),(1,[]),(2,[]),(7,[(3,1,2)]),(0,[(1,4,5)]),(11,[]),(9,[(0,0,1),(3,1,2)]),(4,[]),(9,[(0,2,3)]),(9,[]),(7,[]),(3,[]),(7,[(0,0,19)]),(9,[(1,2,3),(0,0,19)]),(1,[(1,4,5)]),(9,[(1,2,3)]),(12,[]),(9,[(2,2,3)]),(8,[]),(9,[(3,2,3)]),(9,[(1,0,1)]),(5,[(3,4,6)]),(10,[]),(9,[(1,0,1),(0,2,6)]),(5,[(0,2,6)]),(9,[(1,0,1),(3,2,6)]),(5,[(3,2,6)]),(9,[(1,0,1),(0,3,6)]),(5,[(0,3,6)]),(9,[(1,0,1),(3,3,6)]),(5,[(3,3,6)]),(9,[(2,0,1)]),(9,[(3,0,1)]),(9,[(3,0,1),(2,2,8)]),(7,[(0,0,2)]),(9,[(0,0,2)]),(5,[(0,0,2)]),(9,[(1,0,2)]),(9,[(1,0,2),(0,1,10)]),(9,[(1,0,2),(3,1,10)]),(9,[(2,0,2)]),(9,[(0,0,3)]),(9,[(1,0,3)]),(7,[(0,2,13)]),(9,[(1,0,3),(0,2,13)]),(9,[(2,0,3)]),(7,[(2,2,14)]),(13,[]),(9,[(3,0,3)]),(9,[(0,1,3)]),(1,[(1,4,28)]),(9,[(1,1,3)]),(9,[(1,1,3),(0,0,29)]),(5,[(0,0,29)]),(9,[(2,1,3)]),(7,[(2,2,30)])]
def h15Pools : BT (Option BoundPool) := buildPoolsBT 6 h15W h15R h15Slices h15Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Slice13 : Slice h15R h15G (subcubeFast 16 8) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h11Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Slice12 : Slice h15R h15G (subcubeFast 16 4) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h1Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Slice11 : Slice h15R h15G (subcubeFast 16 2) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h2Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Slice10 : Slice h15R h15G (subcubeFast 16 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h3Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Slice9 : Slice h15R h15G (subcubeFast 16 0) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h4Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Slice8 : Slice h15R h15G (subcubeFast 8 4) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h5Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Slice7 : Slice h15R h15G (subcubeFast 8 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h6Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Slice6 : Slice h15R h15G (subcubeFast 2 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h7Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Slice5 : Slice h15R h15G (subcubeFast 2 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h8Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Slice4 : Slice h15R h15G (subcubeFast 0 16) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h9Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Slice3 : Slice h15R h15G (subcubeFast 0 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h10Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Slice2 : Slice h15R h15G (subcubeFast 0 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h12Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Slice1 : Slice h15R h15G (subcubeFast 0 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h13Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Slice0 : Slice h15R h15G (subcubeFast 0 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h14Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h15R h15G p.1 p.2) h15Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h15R h15G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h15Slice0) (forall_cons (fun _ h => by cases h; exact h15Slice1) (forall_cons (fun _ h => by cases h; exact h15Slice2) (forall_cons (fun _ h => by cases h; exact h15Slice3) (forall_cons (fun _ h => by cases h; exact h15Slice4) (forall_cons (fun _ h => by cases h; exact h15Slice5) (forall_cons (fun _ h => by cases h; exact h15Slice6) (forall_cons (fun _ h => by cases h; exact h15Slice7) (forall_cons (fun _ h => by cases h; exact h15Slice8) (forall_cons (fun _ h => by cases h; exact h15Slice9) (forall_cons (fun _ h => by cases h; exact h15Slice10) (forall_cons (fun _ h => by cases h; exact h15Slice11) (forall_cons (fun _ h => by cases h; exact h15Slice12) (forall_cons (fun _ h => by cases h; exact h15Slice13) (fun _ h => (List.not_mem_nil h).elim)))))))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h15R h15G c) h15Pools := buildPoolsBT_sound h15SlicesOk
def h15Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h15G (4 - 1) xs.toFinset) h15Empty := trivial
def h15Block4_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,31],[]),([1,3,4,22,33],[]),([1,2,3,23,33],[]),([0,1,2,3,35],[]),([0,1,2,23,36],[]),([0,1,2,23,39],[]),([1,3,4,33,40],[]),([1,2,3,33,49],[]),([0,1,3,40,52],[]),([0,1,3,40,53],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Test4_0 : checkNodesBT h15W h15G h15Mask h15Pools h15Autos h15Empty 4 h15Block4_0 = true := by decide +kernel
def h15Nodes4 : List NodeSpec := h15Block4_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Check4 : checkNodesBT h15W h15G h15Mask h15Pools h15Autos h15Empty 4 h15Nodes4 = true := h15Test4_0
def h15Bucket4 : BT (List (List Nat)) := buildBucketsBT h15W h15Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h15G 4 xs.toFinset) h15Bucket4 := buildBucketsBT_sound (by decide) h15Pairs h15WOk h15PoolsOk h15AutosOk h15EmptyOk h15Check4
def h15Block5_0 : List NodeSpec := nodesWithIdentity [([0,2,3,16,23],[1,7]),([0,1,2,3,18,23],[10]),([0,1,2,3,4,32],[10,12]),([1,2,3,4,5,33],[4,14,15,16]),([0,1,3,4,19,22],[1]),([0,1,2,3,19,23],[1,7,10,17]),([0,1,2,3,5,34],[10,19]),([0,1,2,3,4,37],[0,4,10,12]),([0,1,3,4,20,22],[1]),([0,1,2,3,20,23],[]),([0,1,2,3,21,23],[1,17]),([0,1,2,3,4,38],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Test5_0 : checkNodesBT h15W h15G h15Mask h15Pools h15Autos h15Bucket4 5 h15Block5_0 = true := by decide +kernel
def h15Block5_1 : List NodeSpec := nodesWithIdentity [([0,1,2,3,23,24],[]),([0,1,2,3,23,25],[1,3]),([0,1,2,3,23,26],[10]),([0,1,2,3,23,27],[]),([0,1,2,3,4,24],[1,13,14]),([1,2,3,4,6,33],[5,14,15,16]),([0,1,2,3,19,49],[0,4,10,24,25]),([0,1,2,3,4,50],[0,1,5,10,12]),([0,1,3,4,20,40],[0]),([0,1,2,3,20,49],[]),([0,1,3,4,21,40],[]),([0,1,2,3,21,49],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Test5_1 : checkNodesBT h15W h15G h15Mask h15Pools h15Autos h15Bucket4 5 h15Block5_1 = true := by decide +kernel
def h15Block5_2 : List NodeSpec := [([0,1,2,3,4,51],[0],[0]),([0,1,3,4,40,42],[0,4,26,27],[0,1]),([0,1,3,4,40,43],[0,4,26,27],[0]),([0,1,3,4,40,44],[],[0]),([0,1,3,4,40,45],[],[0]),([0,1,2,3,4,55],[],[0]),([0,1,3,4,9,56],[12,14],[0]),([1,2,3,4,9,59],[4],[0]),([0,1,2,3,4,60],[1,4,10,12],[0]),([0,1,2,3,4,62],[],[0]),([0,1,2,3,4,68],[],[0]),([0,1,2,3,4,61],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Test5_2 : checkNodesBT h15W h15G h15Mask h15Pools h15Autos h15Bucket4 5 h15Block5_2 = true := by decide +kernel
def h15Nodes5 : List NodeSpec := h15Block5_0 ++ h15Block5_1 ++ h15Block5_2
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Check5 : checkNodesBT h15W h15G h15Mask h15Pools h15Autos h15Bucket4 5 h15Nodes5 = true := by
  unfold h15Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨h15Test5_0,h15Test5_1⟩,h15Test5_2⟩
def h15Bucket5 : BT (List (List Nat)) := buildBucketsBT h15W h15Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h15G 5 xs.toFinset) h15Bucket5 := buildBucketsBT_sound (by decide) h15Pairs h15WOk h15PoolsOk h15AutosOk h15Bucket4Ok h15Check5
def h15Block6_0 : List NodeSpec := [([0,2,3,4,5,16],[0,1,4,5,6,8,9],[0]),([0,1,2,3,4,5,18],[1,3,11,13],[0,1]),([0,1,2,3,4,5,19],[0,1,3,4,5,13,14,18],[0]),([0,1,2,3,4,5,20],[1,5,14,20,21],[0]),([0,1,2,3,4,5,21],[1,4,5,13,14,22],[0]),([0,1,2,3,4,22],[0,1,2,4,10,12,13,14],[0]),([0,1,2,3,23],[1,2,3,7,10,17],[0]),([0,1,2,3,4,23],[0,1,3,4,5,10,12,13,14],[0]),([0,1,2,3,4,6,19],[0,1,4,5,13,14,18,23],[0,1]),([0,1,2,3,4,6,20],[0,5,13,14,20,21],[0]),([0,1,2,3,4,6,21],[0,5,13,14,22],[0]),([0,1,3,4,40],[0,4,26,27],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Test6_0 : checkNodesBT h15W h15G h15Mask h15Pools h15Autos h15Bucket5 6 h15Block6_0 = true := by decide +kernel
def h15Block6_1 : List NodeSpec := [([0,1,2,3,4,40],[0,1,4,10,12,13,14,26,27],[0,1]),([0,1,3,4,46],[0,4,5,28,29],[0]),([0,1,2,4,47],[0,4,13,30,31],[0]),([0,1,2,4,48],[0,4,14,32,33],[0]),([0,1,2,3,49],[0,4,10,23,24,25],[0,1]),([0,1,2,3,4,7,20],[2,4,14],[0]),([0,1,2,3,4,7,21],[1,2,4,5],[0]),([0,1,2,3,4,8,21],[0,5],[0]),([0,1,2,3,4,54],[0,1,10,12,13,14,36],[0]),([0,1,2,3,4,9,14],[5,13,14,37],[0]),([0,1,2,3,4,9,29],[0,1,4,5,13,14],[0,1]),([0,1,2,3,4,9,41],[0,1,2,4,39],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Test6_1 : checkNodesBT h15W h15G h15Mask h15Pools h15Autos h15Bucket5 6 h15Block6_1 = true := by decide +kernel
def h15Block6_2 : List NodeSpec := [([0,1,2,3,4,9,17],[1,2,4],[0,1]),([0,1,2,3,4,57],[0,1,4,5,10,12,13,14,38],[0]),([0,1,2,3,4,58],[1,4,10,13,14,25,38],[0]),([0,2,3,4,63],[0,1,5,41],[0]),([0,2,3,4,64],[0,4,5,42],[0]),([0,1,2,3,65],[0,2,5,10,25,40],[0]),([0,1,2,3,4,9],[0,1,4,10,12,13,14,38],[0]),([0,1,2,3,4,66],[0,1,4,5,10,12,13,14,21,44],[0]),([0,1,2,3,4,67],[0,1,2,4,5,10,12,14,46,47],[0]),([0,1,2,3,4,14,16],[1,2,4,13,14],[0]),([0,1,2,3,4,56],[0,1,4,5,10,12,13,14,21,49],[0]),([0,1,2,3,69],[0,2,10,13,25,51],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Test6_2 : checkNodesBT h15W h15G h15Mask h15Pools h15Autos h15Bucket5 6 h15Block6_2 = true := by decide +kernel
def h15Block6_3 : List NodeSpec := nodesWithIdentity [([0,1,2,3,70],[1,2,10,13,21,52,53]),([0,1,2,3,4,70],[0,1,2,4,5,10,12,21,52]),([0,1,2,3,4,59],[0,1,2,4,5,10,12,14,55,56]),([0,1,2,3,4,71],[0,1,2,4,5,10,12,14,58])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Test6_3 : checkNodesBT h15W h15G h15Mask h15Pools h15Autos h15Bucket5 6 h15Block6_3 = true := by decide +kernel
def h15Nodes6 : List NodeSpec := h15Block6_0 ++ h15Block6_1 ++ h15Block6_2 ++ h15Block6_3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Check6 : checkNodesBT h15W h15G h15Mask h15Pools h15Autos h15Bucket5 6 h15Nodes6 = true := by
  unfold h15Nodes6 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨h15Test6_0,h15Test6_1⟩,h15Test6_2⟩,h15Test6_3⟩
def h15Bucket6 : BT (List (List Nat)) := buildBucketsBT h15W h15Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h15G 6 xs.toFinset) h15Bucket6 := buildBucketsBT_sound (by decide) h15Pairs h15WOk h15PoolsOk h15AutosOk h15Bucket5Ok h15Check6
def h15Block7_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,4,5,12,13,14],[0]),([0,1,2,3,4,6],[0,1,4,5,12,13,14,23,25],[0,1]),([0,1,2,3,4,7],[0,1,2,4,5,12,13,14,34],[0,1]),([0,1,2,3,4,8],[0,1,5,12,13,14,25,35],[0,1]),([0,1,2,3,4,9],[0,1,2,4,5,12,13,14,21,38],[0,1]),([0,1,2,3,4,10],[0,1,2,4,5,12,13,14,25,40],[0,1]),([0,1,2,3,4,11],[0,1,2,4,5,12,13,14,19,21,43],[0]),([0,1,2,3,4,12],[0,1,2,4,5,12,13,14,21,44],[0]),([0,1,2,3,4,13],[0,1,2,4,5,12,13,14,25,45],[0]),([0,1,2,3,4,14],[0,1,2,4,5,12,13,14,21,48,50],[0,1]),([0,1,2,3,4,15],[0,1,2,4,5,12,13,21,25,51],[0]),([0,1,2,3,4,28],[0,1,2,4,5,12,13,21,52],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Test7_0 : checkNodesBT h15W h15G h15Mask h15Pools h15Autos h15Bucket6 7 h15Block7_0 = true := by decide +kernel
def h15Block7_1 : List NodeSpec := [([0,1,2,3,4,29],[0,1,2,4,5,8,12,13,14,21,54],[0,1]),([0,1,2,3,4,30],[0,1,2,4,5,12,13,14,50,57],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Test7_1 : checkNodesBT h15W h15G h15Mask h15Pools h15Autos h15Bucket6 7 h15Block7_1 = true := by decide +kernel
def h15Nodes7 : List NodeSpec := h15Block7_0 ++ h15Block7_1
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Check7 : checkNodesBT h15W h15G h15Mask h15Pools h15Autos h15Bucket6 7 h15Nodes7 = true := by
  unfold h15Nodes7 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h15Test7_0,h15Test7_1⟩
def h15Bucket7 : BT (List (List Nat)) := buildBucketsBT h15W h15Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h15G 7 xs.toFinset) h15Bucket7 := buildBucketsBT_sound (by decide) h15Pairs h15WOk h15PoolsOk h15AutosOk h15Bucket6Ok h15Check7
def h15Block8_0 : List NodeSpec := [([0,1,2,3,4],[12],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Test8_0 : checkNodesBT h15W h15G h15Mask h15Pools h15Autos h15Bucket7 8 h15Block8_0 = true := by decide +kernel
def h15Nodes8 : List NodeSpec := h15Block8_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Check8 : checkNodesBT h15W h15G h15Mask h15Pools h15Autos h15Bucket7 8 h15Nodes8 = true := h15Test8_0
def h15Bucket8 : BT (List (List Nat)) := buildBucketsBT h15W h15Nodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h15G 8 xs.toFinset) h15Bucket8 := buildBucketsBT_sound (by decide) h15Pairs h15WOk h15PoolsOk h15AutosOk h15Bucket7Ok h15Check8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Bound : Lower h15R h15G 9 := lower_of_forestBT (essPairs := [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11),(VAR 4,5,21)]) (by decide +kernel) h15Bucket8Ok (by decide +kernel)
def h16R : List Nat := varsOf 35
def h16G : Nat := 0xeeeeeeee88888888eeeeeeee88888888
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Bound : Lower h16R h16G 4 := carry_of (swaps := [(3,4),(4,5)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h17R : List Nat := varsOf 39
def h17G : Nat := 0xe0e0e0e080808080e0e0e0e080808080
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h17Bound : Lower h17R h17G 5 := carry_of (swaps := [(4,5)]) (roots2 := h6R) (T2 := h6G) (by decide +kernel) h6Bound
def h18R : List Nat := varsOf 44
def h18G : Nat := 0xfff0fff0f000f000fff0fff0f000f000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18Bound : Lower h18R h18G 4 := carry_of (swaps := [(3,4),(4,5),(1,2),(2,3),(0,1),(1,2)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h19R : List Nat := varsOf 45
def h19G : Nat := 0xaaa0aaa0a000a000aaa0aaa0a000a000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h19Bound : Lower h19R h19G 5 := carry_of (swaps := [(4,5),(1,2),(2,3),(0,1),(1,2)]) (roots2 := h6R) (T2 := h6G) (by decide +kernel) h6Bound
def h20R : List Nat := varsOf 43
def h20G : Nat := 0xeeeeeeeeee88ee88eeeeeeeeee88ee88
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h20Bound : Lower h20R h20G 5 := carry_of (swaps := [(4,5)]) (roots2 := h12R) (T2 := h12G) (by decide +kernel) h12Bound
def h21R : List Nat := varsOf 45
def h21G : Nat := 0xfaf0faf0faa0faa0faf0faf0faa0faa0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Bound : Lower h21R h21G 5 := carry_of (swaps := [(4,5),(2,3),(0,1),(1,2)]) (roots2 := h10R) (T2 := h10G) (by decide +kernel) h10Bound
def h22R : List Nat := varsOf 46
def h22G : Nat := 0xfff0fff0fcc0fcc0fff0fff0fcc0fcc0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Bound : Lower h22R h22G 5 := carry_of (swaps := [(4,5),(1,2),(2,3),(0,1),(1,2)]) (roots2 := h12R) (T2 := h12G) (by decide +kernel) h12Bound
def h23R : List Nat := varsOf 47
def h23G : Nat := 0xeae0eae0e880e880eae0eae0e880e880
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h23Bound : Lower h23R h23G 9 := carry_of (swaps := [(4,5)]) (roots2 := h15R) (T2 := h15G) (by decide +kernel) h15Bound
def h24R : List Nat := varsOf 23
def h24G : Nat := 0xe8e8e0e0e8e8e0e0e8e8e0e0e8e8e0e0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h24Bound : Lower h24R h24G 5 := lift_of (z := 0) (o := 16) (essPairs := [(VAR 4,3,19)]) (by decide +kernel) h11Bound
def h25R : List Nat := varsOf 39
def h25G : Nat := 0xe8e8e8e8e0e0e0e0e8e8e8e8e0e0e0e0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h25Bound : Lower h25R h25G 5 := carry_of (swaps := [(4,5)]) (roots2 := h24R) (T2 := h24G) (by decide +kernel) h24Bound
def h26R : List Nat := varsOf 51
def h26G : Nat := 0xeeeeeeeeeeee8888eeeeeeeeeeee8888
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Bound : Lower h26R h26G 5 := carry_of (swaps := [(4,5),(3,4)]) (roots2 := h12R) (T2 := h12G) (by decide +kernel) h12Bound
def h27R : List Nat := varsOf 53
def h27G : Nat := 0xfafaf0f0f0f0a0a0fafaf0f0f0f0a0a0
def h27Pos : List Nat := [20,49,20,20,49,36,49,5,5,5,36,21,21]
def h27Neg : List Nat := [16,48,17,4,33,4,17,4,1,0,32,4,17]
def h27Mask : Nat := fullMask 13
def h27Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,7122,4436),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,8109,2216),(0xffff0000ffff0000ffff0000ffff0000,6239,4167),(0xffffffff00000000ffffffff00000000,1138,1042)]
def h27Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(3,0,1),(0,0,2),(1,0,2),(2,0,2),(1,2,4),(2,2,4),(0,2,5),(3,2,5),(1,3,10),(2,3,10)]
def h27W : BT Decor := buildWiresBT 5 h27Base h27Steps
def h27AutoList : List (List (Nat × Nat)) := [[],[(4,5)],[(0,4)],[(0,5)],[(4,5),(0,4)],[(4,5),(0,5)]]
def h27Autos : BT (List (Nat × Nat)) := btOfList 3 h27AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27Pairs : goodPairs h27G h27Pos h27Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27BaseOk : ∀ x ∈ h27Base, faithful h27Pos h27Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27WOk : btAll (fun x => faithful h27Pos h27Neg x ∧ x.1 < 2^128) h27W := buildWiresBT_faithful h27BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h27G = h27G) h27Autos := btAll_ofList (autos_of (by decide +kernel))
def h27SliceList : List (Option (Nat × Nat)) := []
def h27Slices : BT (Option (Nat × Nat)) := btOfList 1 h27SliceList
def h27Specs : List PoolSpec := []
def h27Pools : BT (Option BoundPool) := buildPoolsBT 1 h27W h27R h27Slices h27Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h27R h27G p.1 p.2) h27Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h27R h27G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h27R h27G c) h27Pools := buildPoolsBT_sound h27SlicesOk
def h27Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h27G (3 - 1) xs.toFinset) h27Empty := trivial
def h27Block3_0 : List NodeSpec := nodesWithIdentity [([0,1,3,11],[]),([0,1,3,12],[]),([0,1,3,13],[]),([0,1,3,14],[]),([1,3,8,9],[]),([0,1,2,15],[]),([0,1,2,16],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27Test3_0 : checkNodesBT h27W h27G h27Mask h27Pools h27Autos h27Empty 3 h27Block3_0 = true := by decide +kernel
def h27Nodes3 : List NodeSpec := h27Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27Check3 : checkNodesBT h27W h27G h27Mask h27Pools h27Autos h27Empty 3 h27Nodes3 = true := h27Test3_0
def h27Bucket3 : BT (List (List Nat)) := buildBucketsBT h27W h27Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h27G 3 xs.toFinset) h27Bucket3 := buildBucketsBT_sound (by decide) h27Pairs h27WOk h27PoolsOk h27AutosOk h27EmptyOk h27Check3
def h27Block4_0 : List NodeSpec := [([0,1,2,3,4],[],[0,1]),([0,1,2,3,5],[],[0,1]),([0,1,2,3,6],[],[0]),([0,1,2,3,7],[],[0]),([0,1,2,3,8],[],[0]),([0,1,2,3,9],[],[0]),([0,1,2,3,10],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27Test4_0 : checkNodesBT h27W h27G h27Mask h27Pools h27Autos h27Bucket3 4 h27Block4_0 = true := by decide +kernel
def h27Nodes4 : List NodeSpec := h27Block4_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27Check4 : checkNodesBT h27W h27G h27Mask h27Pools h27Autos h27Bucket3 4 h27Nodes4 = true := h27Test4_0
def h27Bucket4 : BT (List (List Nat)) := buildBucketsBT h27W h27Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h27G 4 xs.toFinset) h27Bucket4 := buildBucketsBT_sound (by decide) h27Pairs h27WOk h27PoolsOk h27AutosOk h27Bucket3Ok h27Check4
def h27Block5_0 : List NodeSpec := [([0,1,2,3],[],[0,1,2,3,4,5])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27Test5_0 : checkNodesBT h27W h27G h27Mask h27Pools h27Autos h27Bucket4 5 h27Block5_0 = true := by decide +kernel
def h27Nodes5 : List NodeSpec := h27Block5_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27Check5 : checkNodesBT h27W h27G h27Mask h27Pools h27Autos h27Bucket4 5 h27Nodes5 = true := h27Test5_0
def h27Bucket5 : BT (List (List Nat)) := buildBucketsBT h27W h27Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h27G 5 xs.toFinset) h27Bucket5 := buildBucketsBT_sound (by decide) h27Pairs h27WOk h27PoolsOk h27AutosOk h27Bucket4Ok h27Check5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27Bound : Lower h27R h27G 6 := lower_of_forestBT (essPairs := [(VAR 0,4,5),(VAR 2,1,5),(VAR 4,4,20),(VAR 5,4,36)]) (by decide +kernel) h27Bucket5Ok (by decide +kernel)
def h28R : List Nat := varsOf 54
def h28G : Nat := 0xfcfcf0f0f0f0c0c0fcfcf0f0f0f0c0c0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h28Bound : Lower h28R h28G 6 := carry_of (swaps := [(0,1)]) (roots2 := h27R) (T2 := h27G) (by decide +kernel) h27Bound
def h29R : List Nat := varsOf 55
def h29G : Nat := 0xe8e8e0e0e0e08080e8e8e0e0e0e08080
def h29Pos : List Nat := [21,22,22,21,37,51,51,51,37,38,22,38,21,22,51,38,51,7,7,37,7,21,23,21,51,7,7,7,7,39,23,53,54,53,51,22,7,37,51,51,22]
def h29Neg : List Nat := [20,20,18,5,5,19,35,49,33,34,6,6,19,19,52,36,50,5,3,36,19,17,19,1,34,6,4,2,1,35,20,52,52,49,3,4,35,52,48,18,52]
def h29Mask : Nat := fullMask 41
def h29Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf6ffff51f9,0x1630f631f8),(0xcccccccccccccccccccccccccccccccc,0x1dd7f57eee6,0x942b553e64),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x13bfefebf1f,0x129c60acc1b),(0xffff0000ffff0000ffff0000ffff0000,0x1cfc1e174ef,0x1e3c07170a7),(0xffffffff00000000ffffffff00000000,0xe7a109cbf0,0x173a109c3c0)]
def h29Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(0,0,2),(0,1,2),(0,3,4),(1,3,4),(2,3,4),(0,3,5),(1,3,5),(2,3,5),(3,3,5),(1,3,7),(3,3,7),(0,5,7),(2,5,7),(1,7,8),(0,2,3),(1,2,3),(2,2,3),(3,2,3),(1,2,5),(2,2,5),(2,2,8),(2,1,2),(2,1,3),(0,1,4),(1,1,7),(2,1,7),(0,3,25),(3,3,25),(2,0,2),(0,0,3),(2,0,3),(2,0,21),(2,1,21),(1,4,21),(0,2,40),(2,4,21),(1,5,21),(2,5,21),(2,1,44),(0,0,22),(0,1,46),(2,1,46),(0,4,22),(3,4,22),(1,3,47),(3,5,22),(2,0,24),(0,1,53),(2,1,53),(1,5,24),(2,3,54),(2,0,18),(2,1,58),(2,4,18),(3,18,25),(2,0,19),(0,0,10),(0,1,10),(0,5,10),(3,5,10),(2,1,63),(0,2,63),(2,2,63),(1,4,66),(2,0,11),(1,5,11),(2,5,11),(2,1,73),(1,4,73),(2,0,12),(2,1,76),(2,1,12),(3,12,13),(2,0,15),(2,4,14),(2,4,15),(0,6,70),(0,2,80),(1,7,28),(1,7,29),(2,0,41),(2,1,68),(3,7,10),(2,2,17),(2,1,90),(2,0,30),(1,30,36),(2,2,77)]
def h29W : BT Decor := buildWiresBT 7 h29Base h29Steps
def h29AutoList : List (List (Nat × Nat)) := [[],[(4,5)],[(0,1)],[(4,5),(0,1)]]
def h29Autos : BT (List (Nat × Nat)) := btOfList 2 h29AutoList
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
def h29SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,6),some (subcubeFast 0 2,6),some (subcubeFast 0 4,5),some (subcubeFast 0 16,5),some (subcubeFast 0 32,5),some (subcubeFast 0 48,4),some (subcubeFast 16 0,5),some (subcubeFast 16 4,4),some (subcubeFast 32 0,5),some (subcubeFast 32 4,4)]
def h29Slices : BT (Option (Nat × Nat)) := btOfList 4 h29SliceList
def h29Specs : List PoolSpec := [(0,[]),(1,[]),(6,[(0,0,2),(0,1,2)]),(8,[(0,0,2),(0,1,2)]),(1,[(0,0,2)]),(2,[]),(0,[(0,1,2)]),(6,[(0,0,2)]),(8,[(0,0,2)]),(0,[(0,2,3)]),(6,[]),(3,[]),(0,[(0,2,3),(1,4,21)]),(3,[(1,4,21)]),(0,[(0,2,3),(2,4,21)]),(0,[(0,2,3),(1,5,21)]),(0,[(0,2,3),(2,5,21)]),(0,[(1,2,3)]),(6,[(0,0,22)]),(0,[(1,2,3),(0,4,22)]),(6,[(0,4,22)]),(0,[(1,2,3),(3,4,22)]),(0,[(1,2,3),(0,1,46)]),(0,[(1,2,3),(3,5,22)]),(0,[(2,2,3)]),(7,[]),(0,[(3,2,3)]),(4,[]),(8,[]),(5,[]),(0,[(0,5,7)]),(0,[(1,2,5)]),(0,[(1,2,5),(0,3,25)]),(0,[(1,2,5),(3,3,25)]),(0,[(2,2,5)]),(1,[(2,2,5)]),(0,[(2,5,7)]),(0,[(0,3,4)]),(0,[(0,3,4),(1,3,4)]),(0,[(1,3,4)]),(0,[(2,3,4)]),(0,[(2,3,4),(1,5,11)]),(0,[(2,3,4),(2,5,11)]),(0,[(0,3,5)]),(0,[(0,3,5),(1,3,5)]),(0,[(1,3,5)]),(0,[(2,3,5)]),(0,[(2,3,5),(2,4,14)]),(0,[(3,3,5)]),(0,[(3,3,5),(2,4,15)]),(9,[]),(0,[(2,1,2)]),(0,[(2,1,7)]),(1,[(2,0,2)]),(1,[(0,0,3)]),(0,[(2,1,3)]),(4,[(0,0,3)]),(4,[(2,1,3)]),(1,[(0,3,5)]),(2,[(1,3,4)]),(1,[(2,0,3)]),(4,[(2,0,3)]),(8,[(0,2,3)]),(1,[(0,2,3)]),(1,[(0,2,3),(2,0,21)]),(1,[(0,2,3),(1,4,21)]),(2,[(1,4,21)]),(1,[(0,2,3),(2,4,21)]),(2,[(2,4,21)]),(3,[(2,4,21)]),(1,[(1,2,3)]),(1,[(1,2,3),(0,0,22)]),(1,[(1,2,3),(0,4,22)]),(1,[(1,2,3),(3,4,22)]),(6,[(3,4,22)]),(1,[(2,2,3)]),(1,[(3,2,3)]),(1,[(0,3,4)]),(1,[(0,3,4),(1,3,4)]),(1,[(1,3,4)]),(6,[(0,2,40)]),(1,[(2,3,4)]),(1,[(2,3,4),(2,0,11)])]
def h29Pools : BT (Option BoundPool) := buildPoolsBT 7 h29W h29R h29Slices h29Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Slice9 : Slice h29R h29G (subcubeFast 32 4) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h5Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Slice8 : Slice h29R h29G (subcubeFast 32 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h6Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Slice7 : Slice h29R h29G (subcubeFast 16 4) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h16Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Slice6 : Slice h29R h29G (subcubeFast 16 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h17Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Slice5 : Slice h29R h29G (subcubeFast 0 48) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h11Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Slice4 : Slice h29R h29G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h24Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Slice3 : Slice h29R h29G (subcubeFast 0 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h25Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Slice2 : Slice h29R h29G (subcubeFast 0 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h26Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Slice1 : Slice h29R h29G (subcubeFast 0 2) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h27Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Slice0 : Slice h29R h29G (subcubeFast 0 1) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h28Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h29R h29G p.1 p.2) h29Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h29R h29G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h29Slice0) (forall_cons (fun _ h => by cases h; exact h29Slice1) (forall_cons (fun _ h => by cases h; exact h29Slice2) (forall_cons (fun _ h => by cases h; exact h29Slice3) (forall_cons (fun _ h => by cases h; exact h29Slice4) (forall_cons (fun _ h => by cases h; exact h29Slice5) (forall_cons (fun _ h => by cases h; exact h29Slice6) (forall_cons (fun _ h => by cases h; exact h29Slice7) (forall_cons (fun _ h => by cases h; exact h29Slice8) (forall_cons (fun _ h => by cases h; exact h29Slice9) (fun _ h => (List.not_mem_nil h).elim)))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h29R h29G c) h29Pools := buildPoolsBT_sound h29SlicesOk
def h29Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h29G (3 - 1) xs.toFinset) h29Empty := trivial
def h29Block3_0 : List NodeSpec := nodesWithIdentity [([4,5,20,51],[]),([4,5,20,57],[]),([3,5,20,70],[]),([2,3,5,83],[]),([3,5,20,75],[])]
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
def h29Block4_0 : List NodeSpec := nodesWithIdentity [([1,2,4,51,58],[]),([0,1,2,51,60],[]),([0,1,2,57,60],[]),([0,1,3,4,61],[]),([2,4,5,6,51],[]),([2,4,5,6,57],[]),([0,1,2,9,66],[29]),([0,1,2,4,79],[]),([0,1,2,14,82],[29]),([2,3,5,6,70],[]),([2,3,5,6,75],[]),([0,2,4,31,51],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Test4_0 : checkNodesBT h29W h29G h29Mask h29Pools h29Autos h29Bucket3 4 h29Block4_0 = true := by decide +kernel
def h29Block4_1 : List NodeSpec := nodesWithIdentity [([0,2,3,4,88],[]),([1,2,10,36,92],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Test4_1 : checkNodesBT h29W h29G h29Mask h29Pools h29Autos h29Bucket3 4 h29Block4_1 = true := by decide +kernel
def h29Nodes4 : List NodeSpec := h29Block4_0 ++ h29Block4_1
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Check4 : checkNodesBT h29W h29G h29Mask h29Pools h29Autos h29Bucket3 4 h29Nodes4 = true := by
  unfold h29Nodes4 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h29Test4_0,h29Test4_1⟩
def h29Bucket4 : BT (List (List Nat)) := buildBucketsBT h29W h29Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h29G 4 xs.toFinset) h29Bucket4 := buildBucketsBT_sound (by decide) h29Pairs h29WOk h29PoolsOk h29AutosOk h29Bucket3Ok h29Check4
def h29Block5_0 : List NodeSpec := nodesWithIdentity [([3,4,5,7,8],[0,1,2,3,4,5,6]),([2,3,4,5,7,8],[0,1,5]),([2,3,4,5,7,32],[0,1]),([1,3,4,5,7,25],[0]),([1,3,4,5,7,26],[0]),([0,1,2,3,5,40],[10,12,13]),([0,1,2,3,5,42],[14]),([0,1,2,3,4,43],[5,15]),([0,1,2,3,4,44],[16]),([1,2,3,4,5,46],[1,11,18]),([0,1,2,3,5,49],[11,19,20]),([0,1,2,3,5,50],[21])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Test5_0 : checkNodesBT h29W h29G h29Mask h29Pools h29Autos h29Bucket4 5 h29Block5_0 = true := by decide +kernel
def h29Block5_1 : List NodeSpec := [([0,1,2,3,4,47],[11,22],[0]),([0,1,2,3,4,52],[0,1,23],[0]),([1,2,3,4,5,53],[1],[0]),([0,1,2,3,4,56],[],[0]),([0,1,2,3,4,54],[10,27,28],[0]),([0,1,2,3,4,58],[],[0]),([1,2,3,4,18,58],[0],[0,1]),([0,1,2,3,4,26],[],[0]),([0,1,3,4,18,26],[0],[0]),([0,1,2,4,18,51],[10,29],[0,2]),([0,1,2,4,18,57],[11],[0,1]),([1,2,3,4,5,58],[0],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Test5_1 : checkNodesBT h29W h29G h29Mask h29Pools h29Autos h29Bucket4 5 h29Block5_1 = true := by decide +kernel
def h29Block5_2 : List NodeSpec := nodesWithIdentity [([0,1,3,4,18,25],[]),([0,1,2,4,5,51],[]),([0,1,2,4,5,57],[]),([0,1,2,4,5,33],[32]),([0,1,2,4,5,34],[33]),([0,1,2,3,4,18],[10,11,27,28]),([0,1,3,4,19,26],[]),([1,2,3,4,5,62],[0]),([0,1,2,5,9,10],[10,11,29,38]),([1,2,3,4,5,63],[1]),([0,1,2,3,4,65],[]),([0,1,2,3,4,66],[10,11])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Test5_2 : checkNodesBT h29W h29G h29Mask h29Pools h29Autos h29Bucket4 5 h29Block5_2 = true := by decide +kernel
def h29Block5_3 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,72],[10,41]),([0,1,2,3,4,73],[11,42]),([1,2,3,4,5,76],[0]),([0,1,2,4,12,13],[44]),([0,1,2,4,14,15],[29]),([0,1,2,3,5,70],[10,29]),([0,1,2,3,5,81],[47]),([1,2,3,4,5,80],[0,11]),([0,1,2,3,5,75],[]),([0,1,2,3,5,82],[11,49]),([1,3,4,7,8,58],[5]),([1,2,3,4,7,58],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Test5_3 : checkNodesBT h29W h29G h29Mask h29Pools h29Autos h29Bucket4 5 h29Block5_3 = true := by decide +kernel
def h29Block5_4 : List NodeSpec := [([0,1,3,4,7,85],[],[0]),([1,2,3,4,7,80],[5],[0]),([0,2,3,4,29,32],[10],[0]),([0,1,2,3,4,86],[1],[0]),([0,1,2,3,4,84],[10],[0]),([0,1,3,4,7,26],[0],[0]),([0,1,2,4,7,51],[],[0,2]),([1,2,3,4,7,63],[5,11,27],[0]),([0,1,3,4,7,41],[0,25,50],[0]),([0,1,2,3,4,68],[1,10,11],[0]),([0,1,2,3,4,89],[],[0]),([0,1,3,4,7,90],[0],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Test5_4 : checkNodesBT h29W h29G h29Mask h29Pools h29Autos h29Bucket4 5 h29Block5_4 = true := by decide +kernel
def h29Block5_5 : List NodeSpec := [([1,2,3,4,36,92],[11],[0]),([0,1,2,10,30,36],[10],[0,3]),([0,1,2,3,4,93],[],[0]),([0,1,2,4,10,78],[28],[0,3]),([0,1,2,4,36,64],[0],[0]),([0,2,3,4,27,77],[],[0]),([0,1,2,4,21,77],[29],[0]),([0,1,2,3,4,94],[],[0]),([0,1,2,4,37,39],[],[0]),([0,1,2,3,4,91],[],[0]),([0,1,2,3,4,45],[10],[0]),([1,2,3,4,46,47],[11,18,71],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Test5_5 : checkNodesBT h29W h29G h29Mask h29Pools h29Autos h29Bucket4 5 h29Block5_5 = true := by decide +kernel
def h29Block5_6 : List NodeSpec := nodesWithIdentity [([1,2,3,4,46,48],[]),([0,1,2,3,4,48],[5]),([0,1,2,3,4,55],[]),([0,1,2,3,4,67],[]),([0,1,2,3,4,69],[]),([0,1,2,3,4,87],[]),([0,1,2,3,4,74],[10])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Test5_6 : checkNodesBT h29W h29G h29Mask h29Pools h29Autos h29Bucket4 5 h29Block5_6 = true := by decide +kernel
def h29Nodes5 : List NodeSpec := h29Block5_0 ++ h29Block5_1 ++ h29Block5_2 ++ h29Block5_3 ++ h29Block5_4 ++ h29Block5_5 ++ h29Block5_6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Check5 : checkNodesBT h29W h29G h29Mask h29Pools h29Autos h29Bucket4 5 h29Nodes5 = true := by
  unfold h29Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨h29Test5_0,h29Test5_1⟩,h29Test5_2⟩,h29Test5_3⟩,h29Test5_4⟩,h29Test5_5⟩,h29Test5_6⟩
def h29Bucket5 : BT (List (List Nat)) := buildBucketsBT h29W h29Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h29G 5 xs.toFinset) h29Bucket5 := buildBucketsBT_sound (by decide) h29Pairs h29WOk h29PoolsOk h29AutosOk h29Bucket4Ok h29Check5
def h29Block6_0 : List NodeSpec := [([1,2,3,4,5,7],[0,1,4,5,7,8],[0]),([0,1,2,3,4,5,21],[9,10,11],[0]),([0,1,2,3,4,5,22],[0,1,5,10,11,17],[0,2]),([0,1,2,3,4,5,23],[10,11,24,25],[0]),([0,1,2,3,4,5,24],[0,1,5,10,11,26],[0,2]),([0,1,2,3,4,18],[10,11,27,28],[0,1,2]),([0,1,2,3,4,5,18],[5,30],[0,1,2]),([0,1,2,3,4,5,25],[0,1,5,31],[0,1,2]),([0,1,2,3,4,26],[0,1,10,11,27,28,34,35],[0]),([0,1,2,3,4,5,26],[0,1,5,34],[0,2]),([0,1,2,3,4,5,19],[5,36],[0,2]),([0,1,2,3,4,5,9],[10,11,27,28,29,37],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Test6_0 : checkNodesBT h29W h29G h29Mask h29Pools h29Autos h29Bucket5 6 h29Block6_0 = true := by decide +kernel
def h29Block6_1 : List NodeSpec := [([0,1,2,3,4,5,10],[0,1,10,11,27,28,39],[0,2]),([0,1,2,3,4,5,11],[10,11,27,28,40],[0]),([0,1,2,3,4,5,12],[10,11,43],[0,2]),([0,1,2,3,4,5,13],[10,11,45],[0]),([0,1,2,3,4,5,14],[10,11,46],[0]),([0,1,2,3,4,5,15],[10,11,48],[0,2]),([0,1,3,4,7,8],[0,1,4,5,6,25,50],[0,2]),([0,1,2,3,4,7,8],[0,1,4,5,6],[0,2]),([0,1,3,4,7,28],[0,1,4,5,25,50,51],[0]),([0,1,2,3,4,7,29],[0,1,10,11,25],[0]),([0,1,2,3,4,7,18],[1,4,25,50],[0,1,2]),([0,1,2,3,4,32],[0,1,4,5,10,11,27,28,52],[0,1,2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Test6_1 : checkNodesBT h29W h29G h29Mask h29Pools h29Autos h29Bucket5 6 h29Block6_1 = true := by decide +kernel
def h29Block6_2 : List NodeSpec := [([0,1,2,3,4,7,32],[0,1,4,5],[0,2]),([0,1,2,3,4,7,10],[0,5,10,11,25,27,28,50],[0]),([0,1,2,3,4,7,16],[0,5,10,11,25],[0]),([0,1,2,3,4,7,17],[10,11,25],[0]),([0,1,2,3,4,59],[0,1,5,10,11,25,27,28,30,50],[0]),([0,1,2,4,29,36],[0,1,10,11,25,54,55,56,57],[0]),([0,1,2,3,4,30,36],[0,1,10,11,27,28],[0,3]),([0,1,2,3,4,78],[0,1,5,10,11,25,27,28,58],[0,2,3]),([0,1,2,4,10,36],[0,10,11,25,28,39,56,59],[0]),([0,1,2,3,4,77],[0,1,5,10,11,27,28,29,43],[0,2]),([0,1,2,4,21,37],[0,5,9,10,11,29,61,62],[0]),([0,1,2,3,4,90],[0,1,5,10,11,25,27,28],[0,2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Test6_2 : checkNodesBT h29W h29G h29Mask h29Pools h29Autos h29Bucket5 6 h29Block6_2 = true := by decide +kernel
def h29Block6_3 : List NodeSpec := [([0,1,2,3,4,38],[0,1,5,9,10,11,25,27,28,64],[0,2]),([0,1,2,3,40],[10,12,13,25,27,29,65,66],[0]),([0,1,2,3,42],[10,14,25,28,67,68,69],[0]),([1,2,3,4,46],[5,11,17,18,25,50,71],[0]),([0,1,2,3,4,46],[0,1,5,11,17,18,25,27,28,50,71],[0]),([0,1,2,3,49],[5,11,19,20,28,72],[0]),([0,1,2,3,50],[5,11,21,27,73,74],[0]),([0,1,2,3,4,53],[0,1,5,10,26,27,28,50],[0]),([0,1,2,9,10],[10,11,25,29,38,59,78],[0]),([0,1,2,3,4,63],[0,1,5,10,11,27,39],[0,2,3]),([0,1,2,3,4,41],[0,1,5,10,11,25,27,50,62,66,80],[0,2]),([0,1,2,3,4,71],[0,1,5,10,11,25,27,29,40,82],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Test6_3 : checkNodesBT h29W h29G h29Mask h29Pools h29Autos h29Bucket5 6 h29Block6_3 = true := by decide +kernel
def h29Nodes6 : List NodeSpec := h29Block6_0 ++ h29Block6_1 ++ h29Block6_2 ++ h29Block6_3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Check6 : checkNodesBT h29W h29G h29Mask h29Pools h29Autos h29Bucket5 6 h29Nodes6 = true := by
  unfold h29Nodes6 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨h29Test6_0,h29Test6_1⟩,h29Test6_2⟩,h29Test6_3⟩
def h29Bucket6 : BT (List (List Nat)) := buildBucketsBT h29W h29Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h29G 6 xs.toFinset) h29Bucket6 := buildBucketsBT_sound (by decide) h29Pairs h29WOk h29PoolsOk h29AutosOk h29Bucket5Ok h29Check6
def h29Block7_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,5,10,11,27,28],[0,1,2]),([0,1,2,3,4,7],[0,1,4,5,10,11,25,27,28,50],[0,1]),([0,1,2,3,4,35],[0,1,5,10,11,25,27,28,50,53],[0,2]),([0,1,2,3,4,36],[0,1,5,10,25,27,28,29,54],[0]),([0,1,2,3,4,37],[0,1,5,10,11,25,27,28,29,60],[0,2]),([0,1,2,3,4,21],[0,1,5,9,10,11,25,27,28,29,50,63],[0,2]),([0,1,2,3,4,22],[0,1,5,10,11,17,25,27,28,50,70],[0,2]),([0,1,2,3,4,23],[0,1,5,10,11,24,25,27,28,29,50,75],[0]),([0,1,2,3,4,24],[0,1,5,10,26,27,28,50,76],[0,2]),([0,1,2,3,4,9],[0,1,5,10,11,25,28,29,37,77],[0]),([0,1,2,3,4,10],[0,1,5,10,11,25,27,28,39,50,79],[0,1,2,3]),([0,1,2,3,4,11],[0,1,5,10,11,25,27,28,29,40,81],[0,2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Test7_0 : checkNodesBT h29W h29G h29Mask h29Pools h29Autos h29Bucket6 7 h29Block7_0 = true := by decide +kernel
def h29Nodes7 : List NodeSpec := h29Block7_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Check7 : checkNodesBT h29W h29G h29Mask h29Pools h29Autos h29Bucket6 7 h29Nodes7 = true := h29Test7_0
def h29Bucket7 : BT (List (List Nat)) := buildBucketsBT h29W h29Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h29G 7 xs.toFinset) h29Bucket7 := buildBucketsBT_sound (by decide) h29Pairs h29WOk h29PoolsOk h29AutosOk h29Bucket6Ok h29Check7
def h29Block8_0 : List NodeSpec := [([0,1,2,3,4],[0,1],[0,1,2,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Test8_0 : checkNodesBT h29W h29G h29Mask h29Pools h29Autos h29Bucket7 8 h29Block8_0 = true := by decide +kernel
def h29Nodes8 : List NodeSpec := h29Block8_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Check8 : checkNodesBT h29W h29G h29Mask h29Pools h29Autos h29Bucket7 8 h29Nodes8 = true := h29Test8_0
def h29Bucket8 : BT (List (List Nat)) := buildBucketsBT h29W h29Nodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h29G 8 xs.toFinset) h29Bucket8 := buildBucketsBT_sound (by decide) h29Pairs h29WOk h29PoolsOk h29AutosOk h29Bucket7Ok h29Check8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Bound : Lower h29R h29G 9 := lower_of_forestBT (essPairs := [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 4,5,21),(VAR 5,5,37)]) (by decide +kernel) h29Bucket8Ok (by decide +kernel)
def h30R : List Nat := varsOf 25
def h30G : Nat := 0xffaaaa00ffaaaa00ffaaaa00ffaaaa00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h30Bound : Lower h30R h30G 4 := carry_of (swaps := [(3,4),(1,2),(2,3)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h31R : List Nat := varsOf 27
def h31G : Nat := 0xee88aa00ee88aa00ee88aa00ee88aa00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Bound : Lower h31R h31G 5 := lift_of (z := 0) (o := 2) (essPairs := [(VAR 1,17,19)]) (by decide +kernel) h30Bound
def h32R : List Nat := varsOf 41
def h32G : Nat := 0xffaaffaaaa00aa00ffaaffaaaa00aa00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h32Bound : Lower h32R h32G 4 := carry_of (swaps := [(3,4),(4,5),(1,2),(2,3)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
def h33R : List Nat := varsOf 43
def h33G : Nat := 0xee88ee88aa00aa00ee88ee88aa00aa00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Bound : Lower h33R h33G 5 := carry_of (swaps := [(4,5)]) (roots2 := h31R) (T2 := h31G) (by decide +kernel) h31Bound
def h34R : List Nat := varsOf 51
def h34G : Nat := 0xeeeeaaaaaaaa8888eeeeaaaaaaaa8888
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34Bound : Lower h34R h34G 6 := carry_of (swaps := [(1,2),(0,1)]) (roots2 := h27R) (T2 := h27G) (by decide +kernel) h27Bound
def h35R : List Nat := varsOf 57
def h35G : Nat := 0xffaaaa00aa00aa00ffaaaa00aa00aa00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Bound : Lower h35R h35G 5 := carry_of (swaps := [(4,5),(1,2),(2,3),(3,4),(2,3)]) (roots2 := h31R) (T2 := h31G) (by decide +kernel) h31Bound
def h36R : List Nat := varsOf 58
def h36G : Nat := 0xffccff00ff00cc00ffccff00ff00cc00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h36Bound : Lower h36R h36G 6 := carry_of (swaps := [(2,3),(0,1)]) (roots2 := h27R) (T2 := h27G) (by decide +kernel) h27Bound
def h37R : List Nat := varsOf 59
def h37G : Nat := 0xee88aa00aa008800ee88aa00aa008800
def h37Pos : List Nat := [25,58,25,58,25,41,51,51,11,11,25,27,51,58,41,58,25,51,41,11,51,25,11,11,27,27,11,43,11,43,57,51,25,41,41]
def h37Neg : List Nat := [24,56,26,50,9,9,19,35,10,9,19,26,49,26,33,42,18,50,40,3,33,17,2,8,19,24,19,42,1,35,56,34,1,42,56]
def h37Mask : Nat := fullMask 35
def h37Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x7ffff5ff5,0x1353856f0),(0xcccccccccccccccccccccccccccccccc,0xbfdabbca,0x2ad4badcc),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x77fedef3f,0x64a84ab37),(0xffff0000ffff0000ffff0000ffff0000,0x1c333bcdf,0x447233c4f),(0xffffffff00000000ffffffff00000000,0x6e816f0ea,0x6e816d08a)]
def h37Steps : List (Nat × Nat × Nat) := [(0,0,1),(2,0,1),(0,0,2),(0,1,2),(0,3,4),(0,3,5),(2,3,10),(0,4,10),(2,4,10),(0,7,8),(2,7,8),(0,7,10),(0,4,11),(2,4,11),(1,5,8),(0,1,3),(1,1,3),(2,1,3),(3,1,3),(1,1,7),(2,1,7),(3,1,2),(0,2,3),(0,4,20),(1,5,27),(3,7,20),(0,7,29),(2,5,27),(3,2,3),(2,2,5),(2,2,7),(2,2,23),(2,4,23),(1,5,23),(0,3,24),(3,3,24),(2,3,25),(2,3,34),(2,1,10),(2,2,10),(1,11,33),(2,2,11),(1,0,2),(2,0,8),(2,2,48),(1,3,14),(2,4,14),(2,0,26),(1,5,26),(2,0,28),(1,14,23),(0,0,38),(2,4,16),(2,2,12),(2,0,43),(2,2,56),(2,4,31),(3,7,21),(0,2,59),(2,2,59),(1,4,22),(2,4,22),(1,7,22),(3,14,24),(0,4,47),(0,45,47),(2,4,41)]
def h37W : BT Decor := buildWiresBT 7 h37Base h37Steps
def h37AutoList : List (List (Nat × Nat)) := [[],[(4,5)],[(1,4)],[(1,5)],[(0,3)],[(4,5),(1,4)],[(4,5),(1,5)],[(4,5),(0,3)],[(1,4),(0,3)],[(1,5),(0,3)],[(4,5),(1,4),(0,3)],[(4,5),(1,5),(0,3)]]
def h37Autos : BT (List (Nat × Nat)) := btOfList 4 h37AutoList
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
def h37SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,6),some (subcubeFast 0 2,5),some (subcubeFast 0 8,6),some (subcubeFast 0 16,5),some (subcubeFast 0 18,4),some (subcubeFast 0 32,5),some (subcubeFast 0 34,4),some (subcubeFast 0 48,4)]
def h37Slices : BT (Option (Nat × Nat)) := btOfList 3 h37SliceList
def h37Specs : List PoolSpec := [(0,[]),(1,[]),(2,[]),(2,[(0,0,1)]),(0,[(0,1,2)]),(3,[]),(5,[]),(0,[(3,1,2)]),(4,[]),(6,[]),(0,[(0,1,3)]),(5,[(0,1,3)]),(3,[(0,4,20)]),(0,[(3,1,3)]),(5,[(3,1,3)]),(3,[(2,4,23)]),(0,[(3,1,3),(2,4,23)]),(7,[]),(2,[(0,7,8)]),(0,[(2,2,5)]),(0,[(0,3,5)]),(2,[(2,0,1)]),(2,[(2,0,8)]),(0,[(0,1,3),(1,1,3)]),(0,[(1,1,3)]),(0,[(2,1,3)]),(0,[(2,1,3),(1,4,22)]),(1,[(1,4,22)]),(0,[(2,1,3),(2,4,22)]),(0,[(0,1,2),(1,3,14)]),(0,[(1,1,7)]),(0,[(1,1,7),(0,3,24)]),(0,[(1,1,7),(3,3,24)]),(0,[(2,1,7)]),(2,[(2,1,7)]),(2,[(2,7,8)]),(2,[(0,1,3)]),(2,[(0,1,3),(1,1,3)]),(1,[(0,4,20)]),(2,[(1,1,3)]),(2,[(2,1,3)]),(2,[(2,1,3),(1,4,22)]),(1,[(2,4,22)]),(2,[(2,1,3),(2,4,22)])]
def h37Pools : BT (Option BoundPool) := buildPoolsBT 6 h37W h37R h37Slices h37Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Slice7 : Slice h37R h37G (subcubeFast 0 48) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h1Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Slice6 : Slice h37R h37G (subcubeFast 0 34) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h30Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Slice5 : Slice h37R h37G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h31Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Slice4 : Slice h37R h37G (subcubeFast 0 18) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h32Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Slice3 : Slice h37R h37G (subcubeFast 0 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h33Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Slice2 : Slice h37R h37G (subcubeFast 0 8) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h34Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Slice1 : Slice h37R h37G (subcubeFast 0 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h35Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Slice0 : Slice h37R h37G (subcubeFast 0 1) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h36Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h37R h37G p.1 p.2) h37Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h37R h37G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h37Slice0) (forall_cons (fun _ h => by cases h; exact h37Slice1) (forall_cons (fun _ h => by cases h; exact h37Slice2) (forall_cons (fun _ h => by cases h; exact h37Slice3) (forall_cons (fun _ h => by cases h; exact h37Slice4) (forall_cons (fun _ h => by cases h; exact h37Slice5) (forall_cons (fun _ h => by cases h; exact h37Slice6) (forall_cons (fun _ h => by cases h; exact h37Slice7) (fun _ h => (List.not_mem_nil h).elim)))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h37R h37G c) h37Pools := buildPoolsBT_sound h37SlicesOk
def h37Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h37G (3 - 1) xs.toFinset) h37Empty := trivial
def h37Block3_0 : List NodeSpec := nodesWithIdentity [([4,7,20,29],[]),([4,7,19,45],[]),([1,7,45,69],[]),([1,4,7,70],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test3_0 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Empty 3 h37Block3_0 = true := by decide +kernel
def h37Nodes3 : List NodeSpec := h37Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Check3 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Empty 3 h37Nodes3 = true := h37Test3_0
def h37Bucket3 : BT (List (List Nat)) := buildBucketsBT h37W h37Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h37G 3 xs.toFinset) h37Bucket3 := buildBucketsBT_sound (by decide) h37Pairs h37WOk h37PoolsOk h37AutosOk h37EmptyOk h37Check3
def h37Block4_0 : List NodeSpec := nodesWithIdentity [([3,4,7,8,10],[2]),([3,4,7,8,11],[]),([4,5,7,20,27],[]),([3,4,5,7,36],[]),([2,3,5,7,37],[]),([2,4,5,7,39],[]),([1,3,4,7,29],[0,2]),([1,4,7,11,33],[]),([0,1,2,4,45],[]),([0,2,4,20,29],[]),([0,2,3,14,37],[9,15]),([0,2,3,4,55],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test4_0 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket3 4 h37Block4_0 = true := by decide +kernel
def h37Block4_1 : List NodeSpec := nodesWithIdentity [([0,2,3,34,37],[]),([0,1,2,3,57],[]),([0,2,4,25,50],[]),([0,1,2,50,51],[]),([0,1,2,45,51],[]),([0,1,3,4,58],[]),([2,4,7,20,56],[8]),([0,2,4,21,30],[]),([0,2,4,20,31],[8,11]),([0,1,2,3,61],[]),([0,2,3,25,65],[]),([0,2,4,14,39],[8,9])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test4_1 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket3 4 h37Block4_1 = true := by decide +kernel
def h37Block4_2 : List NodeSpec := nodesWithIdentity [([0,2,3,4,68],[]),([1,4,7,45,47],[]),([0,1,2,3,71],[]),([2,4,20,35,56],[]),([0,2,4,20,60],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test4_2 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket3 4 h37Block4_2 = true := by decide +kernel
def h37Nodes4 : List NodeSpec := h37Block4_0 ++ h37Block4_1 ++ h37Block4_2
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Check4 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket3 4 h37Nodes4 = true := by
  unfold h37Nodes4 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨h37Test4_0,h37Test4_1⟩,h37Test4_2⟩
def h37Bucket4 : BT (List (List Nat)) := buildBucketsBT h37W h37Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h37G 4 xs.toFinset) h37Bucket4 := buildBucketsBT_sound (by decide) h37Pairs h37WOk h37PoolsOk h37AutosOk h37Bucket3Ok h37Check4
def h37Block5_0 : List NodeSpec := [([3,4,5,7,8],[0,1,2,3,4],[0,1,4,7]),([1,3,4,5,7,8],[0,1,2],[0]),([2,3,4,5,7,20],[],[0,4]),([2,3,4,5,7,23],[],[0]),([2,3,4,5,7,24],[0],[0,1]),([2,3,4,5,7,25],[0],[0]),([1,3,4,5,7,27],[],[0,2,4]),([1,3,4,5,7,34],[0,2],[0]),([1,2,3,4,7,10],[2],[0,2]),([1,2,3,4,7,11],[2],[0]),([2,3,4,5,8,48],[1],[0]),([0,2,3,4,8,10],[2],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test5_0 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket4 5 h37Block5_0 = true := by decide +kernel
def h37Block5_1 : List NodeSpec := [([0,2,3,4,8,11],[],[0]),([1,2,3,4,5,48],[0],[0]),([0,1,2,3,4,14],[5,6],[0,1]),([0,2,3,4,5,53],[],[0]),([0,2,4,5,20,27],[],[0]),([0,2,3,4,14,20],[5,11],[0]),([0,2,3,4,20,34],[5],[0]),([0,2,4,5,11,20],[5],[0]),([0,2,3,4,5,28],[0,8,11,12],[0]),([0,2,3,4,14,23],[5,14],[0]),([0,2,3,4,23,34],[],[0]),([0,2,3,4,5,36],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test5_1 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket4 5 h37Block5_1 = true := by decide +kernel
def h37Block5_2 : List NodeSpec := [([0,2,3,5,37],[1,9,14,15,16],[0]),([0,2,3,4,5,38],[],[0]),([0,1,2,3,4,16],[6],[0,2]),([0,1,2,3,4,29],[0,2],[0]),([0,1,2,3,4,32],[],[0]),([0,1,2,3,4,48],[],[0]),([1,2,3,4,14,48],[0],[0]),([0,1,2,3,4,25],[],[0]),([0,2,3,4,14,25],[0],[0,1]),([0,1,2,4,14,50],[17],[0]),([0,1,2,4,45],[],[0]),([0,1,2,3,4,45],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test5_2 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket4 5 h37Block5_2 = true := by decide +kernel
def h37Block5_3 : List NodeSpec := [([0,1,2,4,14,45],[5],[0,1]),([0,2,3,4,5,25],[0],[0]),([0,1,2,4,5,45],[],[0]),([0,1,2,3,4,42],[],[0]),([0,1,2,4,9,11],[6],[0]),([0,1,2,3,4,12],[2],[0]),([0,1,2,3,4,17],[],[0]),([0,2,3,4,10,43],[0],[0]),([0,1,2,3,4,44],[],[0]),([0,1,2,3,4,13],[],[0]),([0,2,3,4,5,43],[0],[0]),([1,2,3,4,11,35],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test5_3 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket4 5 h37Block5_3 = true := by decide +kernel
def h37Block5_4 : List NodeSpec := [([0,1,2,4,11,33],[],[0]),([0,1,2,3,4,46],[],[0]),([0,1,2,3,4,18],[1],[0]),([0,2,4,7,20,21],[1,8,23],[0,4]),([0,1,2,3,4,30],[],[0]),([1,2,3,4,7,56],[2],[0]),([0,2,3,4,21,25],[],[0]),([0,1,2,3,4,31],[1,5,6],[0]),([0,1,2,3,4,62],[],[0]),([1,2,3,4,7,59],[2],[0,8]),([0,2,3,4,22,25],[],[0,2]),([0,1,2,3,7,65],[26,27],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test5_4 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket4 5 h37Block5_4 = true := by decide +kernel
def h37Block5_5 : List NodeSpec := [([0,1,2,3,7,66],[5,28],[0,2,8]),([0,1,2,3,4,67],[1],[0]),([0,1,2,3,4,63],[],[0,2]),([1,2,3,4,7,48],[0],[0]),([0,2,3,4,14,24],[8,9],[0,1]),([0,1,2,4,7,50],[8,29],[0]),([0,1,2,4,7,45],[],[0]),([0,1,2,4,7,39],[1,31],[0,4]),([0,1,2,4,7,40],[32],[0]),([0,1,2,3,4,41],[6],[0,2]),([0,2,3,4,15,25],[],[0]),([1,2,3,4,7,52],[0],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test5_5 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket4 5 h37Block5_5 = true := by decide +kernel
def h37Block5_6 : List NodeSpec := nodesWithIdentity [([0,2,4,20,56],[1,8,9,11]),([0,1,2,3,4,54],[]),([1,2,3,4,35,56],[]),([0,1,2,3,4,60],[]),([1,2,3,4,35,59],[]),([0,1,2,3,4,64],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test5_6 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket4 5 h37Block5_6 = true := by decide +kernel
def h37Nodes5 : List NodeSpec := h37Block5_0 ++ h37Block5_1 ++ h37Block5_2 ++ h37Block5_3 ++ h37Block5_4 ++ h37Block5_5 ++ h37Block5_6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Check5 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket4 5 h37Nodes5 = true := by
  unfold h37Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨h37Test5_0,h37Test5_1⟩,h37Test5_2⟩,h37Test5_3⟩,h37Test5_4⟩,h37Test5_5⟩,h37Test5_6⟩
def h37Bucket5 : BT (List (List Nat)) := buildBucketsBT h37W h37Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h37G 5 xs.toFinset) h37Bucket5 := buildBucketsBT_sound (by decide) h37Pairs h37WOk h37PoolsOk h37AutosOk h37Bucket4Ok h37Check5
def h37Block6_0 : List NodeSpec := [([1,2,3,4,5,7],[0,1,2,3],[0,1]),([0,2,3,4,5,8],[0,1,2,3,4],[0,1,4,7]),([0,1,2,3,4,5,8],[0,1,2,3,4],[0,4]),([0,2,3,4,5,26],[0,1,2,3,7,8,9],[0]),([0,2,3,4,5,20],[0,1,5,8,9,10,11],[0,4]),([0,2,3,4,5,23],[0,1,5,8,9,13,14],[0]),([0,1,2,3,4,5,27],[1,5],[0,2,4,8]),([0,1,2,3,4,14],[5,6],[0,1,4]),([0,1,2,3,4,5,14],[2,8,9,18],[0,1,4]),([0,1,2,3,4,34],[0,1,2,3,5,6,19],[0,1,4,8,11]),([0,1,2,3,4,5,34],[0,1,2,3],[0,4]),([0,1,2,3,4,5,9],[1,5,6,8,9,17],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test6_0 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket5 6 h37Block6_0 = true := by decide +kernel
def h37Block6_1 : List NodeSpec := [([0,1,2,3,4,10],[2,6,8,20],[0,2]),([0,1,2,3,4,5,10],[5,8],[0,2]),([0,1,2,3,4,11],[0,1,2,6,8],[0,2,8]),([0,1,2,3,4,5,11],[0,1,5,8],[0,2]),([0,1,2,3,4,49],[0,1,2,4,5,6,8,9,22],[0]),([0,1,2,3,4,7,20],[0,1,2,5,8,10],[0,2,4,8]),([0,1,2,3,4,7,21],[0,1,2,5,24],[0,2,4]),([0,1,2,3,4,7,22],[0,1,2,5,25],[0,2,4,8]),([0,1,2,3,4,7,14],[1,4],[0,1,4]),([0,1,2,3,4,7,24],[0,1,2,30],[0,1,4]),([0,1,2,3,4,25],[0,2,5,6,33,34],[0,1]),([0,1,2,3,4,7,25],[0,1,2,33],[0,4])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test6_1 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket5 6 h37Block6_1 = true := by decide +kernel
def h37Block6_2 : List NodeSpec := [([0,1,2,3,4,7,15],[1,35],[0,4]),([0,2,4,20,21],[1,8,9,11,23,37],[0,4]),([0,1,2,3,4,28],[0,2,8,9,11,12,17,38],[0,2,3,4,8,9]),([0,1,2,3,4,56],[0,1,2,5,6,9],[0]),([0,1,2,3,4,59],[0,1,2,5,6,8,17],[0,8]),([0,1,2,3,65],[5,6,8,26,27,41],[0]),([0,1,2,3,66],[5,8,9,17,28,42,43],[0,2,8])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test6_2 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket5 6 h37Block6_2 = true := by decide +kernel
def h37Nodes6 : List NodeSpec := h37Block6_0 ++ h37Block6_1 ++ h37Block6_2
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Check6 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket5 6 h37Nodes6 = true := by
  unfold h37Nodes6 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨h37Test6_0,h37Test6_1⟩,h37Test6_2⟩
def h37Bucket6 : BT (List (List Nat)) := buildBucketsBT h37W h37Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h37G 6 xs.toFinset) h37Bucket6 := buildBucketsBT_sound (by decide) h37Pairs h37WOk h37PoolsOk h37AutosOk h37Bucket5Ok h37Check6
def h37Block7_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,5,6,8,9],[0,1]),([0,1,2,3,4,6],[0,1,2,5,6,8,9,21],[0,4]),([0,1,2,3,4,7],[0,1,2,5,6],[0,1,2,3,4,5,6,8,9]),([0,1,2,3,4,20],[0,1,2,5,6,8,9,10,17,36],[0,2,3,4,8,9]),([0,1,2,3,4,21],[0,1,2,5,6,9,24,39],[0,4]),([0,1,2,3,4,22],[0,1,2,5,6,8,9,17,25,40],[0,2,4,8])]
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
def h37Block8_0 : List NodeSpec := [([0,1,2,3,4],[0,2],[0,1,2,3,4,5,6,8,9])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Test8_0 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket7 8 h37Block8_0 = true := by decide +kernel
def h37Nodes8 : List NodeSpec := h37Block8_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Check8 : checkNodesBT h37W h37G h37Mask h37Pools h37Autos h37Bucket7 8 h37Nodes8 = true := h37Test8_0
def h37Bucket8 : BT (List (List Nat)) := buildBucketsBT h37W h37Nodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h37G 8 xs.toFinset) h37Bucket8 := buildBucketsBT_sound (by decide) h37Pairs h37WOk h37PoolsOk h37AutosOk h37Bucket7Ok h37Check8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Bound : Lower h37R h37G 9 := lower_of_forestBT (essPairs := [(VAR 0,10,11),(VAR 1,9,11),(VAR 3,3,11),(VAR 4,9,25),(VAR 5,9,41)]) (by decide +kernel) h37Bucket8Ok (by decide +kernel)
def h38R : List Nat := varsOf 60
def h38G : Nat := 0xfff0fff0fff0f000fff0fff0fff0f000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38Bound : Lower h38R h38G 5 := carry_of (swaps := [(4,5),(3,4),(1,2),(2,3),(0,1),(1,2)]) (roots2 := h12R) (T2 := h12G) (by decide +kernel) h12Bound
def h39R : List Nat := varsOf 61
def h39G : Nat := 0xaaa0aaa0aaa0a000aaa0aaa0aaa0a000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h39Bound : Lower h39R h39G 6 := lift_of (z := 16) (o := 1) (essPairs := [(VAR 0,12,13),(VAR 4,5,21)]) (by decide +kernel) h18Bound
def h40R : List Nat := varsOf 60
def h40G : Nat := 0xfff0f0f0f0f0f000fff0f0f0f0f0f000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h40Bound : Lower h40R h40G 6 := carry_of (swaps := [(0,1),(1,2),(2,3),(1,2)]) (roots2 := h27R) (T2 := h27G) (by decide +kernel) h27Bound
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

def G_38 : Nat := 0xfe008000fe008000fe008000fe008000
def R_38 : List Nat := varsOf 31
lemma low_38_ok : liftCheck 0 8 R_38 G_38 R_16 G_16 [(VAR 3,15,7)] = true := by decide +kernel
lemma low_38 : Lower R_38 G_38 7 := lift_of low_38_ok low_16

end Cofactor12086
def h41R : List Nat := varsOf 62
def h41G : Nat := 0xccc0c0c0c0c0c000ccc0c0c0c0c0c000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h41Bound : Lower h41R h41G 7 := carry_of (swaps := [(2,3),(3,4),(4,5),(1,2),(2,3),(3,4),(0,1),(1,2),(2,3),(1,2),(0,1)]) (roots2 := Cofactor12086.R_38) (T2 := Cofactor12086.G_38) (by decide +kernel) Cofactor12086.low_38
def h42R : List Nat := varsOf 15
def h42G : Nat := 0xeee8eee8eee8eee8eee8eee8eee8eee8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h42Bound : Lower h42R h42G 5 := carry_of (swaps := [(2,3),(3,4)]) (roots2 := h12R) (T2 := h12G) (by decide +kernel) h12Bound
def h43R : List Nat := varsOf 29
def h43G : Nat := 0xfffafaf0fffafaf0fffafaf0fffafaf0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Bound : Lower h43R h43G 5 := lift_of (z := 4) (o := 0) (essPairs := [(VAR 2,0,4)]) (by decide +kernel) h30Bound
def h44R : List Nat := varsOf 31
def h44G : Nat := 0xeee8eae0eee8eae0eee8eae0eee8eae0
def h44Pos : List Nat := [5,6,11,19,6,5,26,9,26,19,19,14,14,21]
def h44Neg : List Nat := [4,4,10,17,2,1,18,1,10,3,18,12,10,17]
def h44Mask : Nat := fullMask 14
def h44Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,9901,8872),(0xcccccccccccccccccccccccccccccccc,8030,5972),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x3833,2051),(0xff00ff00ff00ff00ff00ff00ff00ff00,6596,6404),(0xffff0000ffff0000ffff0000ffff0000,0x2748,9288)]
def h44Steps : List (Nat × Nat × Nat) := []
def h44W : BT Decor := buildWiresBT 3 h44Base h44Steps
def h44AutoList : List (List (Nat × Nat)) := [[]]
def h44Autos : BT (List (Nat × Nat)) := btOfList 1 h44AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h44Pairs : goodPairs h44G h44Pos h44Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h44BaseOk : ∀ x ∈ h44Base, faithful h44Pos h44Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h44WOk : btAll (fun x => faithful h44Pos h44Neg x ∧ x.1 < 2^128) h44W := buildWiresBT_faithful h44BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h44AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h44G = h44G) h44Autos := btAll_ofList (autos_of (by decide +kernel))
def h44SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 2,5),some (subcubeFast 0 16,5),some (subcubeFast 4 0,5),some (subcubeFast 8 0,5)]
def h44Slices : BT (Option (Nat × Nat)) := btOfList 2 h44SliceList
def h44Specs : List PoolSpec := [(0,[]),(2,[]),(3,[]),(1,[])]
def h44Pools : BT (Option BoundPool) := buildPoolsBT 2 h44W h44R h44Slices h44Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h44Slice3 : Slice h44R h44G (subcubeFast 8 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h24Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h44Slice2 : Slice h44R h44G (subcubeFast 4 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h31Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h44Slice1 : Slice h44R h44G (subcubeFast 0 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h42Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h44Slice0 : Slice h44R h44G (subcubeFast 0 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h43Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h44SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h44R h44G p.1 p.2) h44Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h44R h44G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h44Slice0) (forall_cons (fun _ h => by cases h; exact h44Slice1) (forall_cons (fun _ h => by cases h; exact h44Slice2) (forall_cons (fun _ h => by cases h; exact h44Slice3) (fun _ h => (List.not_mem_nil h).elim)))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h44PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h44R h44G c) h44Pools := buildPoolsBT_sound h44SlicesOk
def h44Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h44EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h44G (6 - 1) xs.toFinset) h44Empty := trivial
def h44Block6_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4],[0,1,2,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h44Test6_0 : checkNodesBT h44W h44G h44Mask h44Pools h44Autos h44Empty 6 h44Block6_0 = true := by decide +kernel
def h44Nodes6 : List NodeSpec := h44Block6_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h44Check6 : checkNodesBT h44W h44G h44Mask h44Pools h44Autos h44Empty 6 h44Nodes6 = true := h44Test6_0
def h44Bucket6 : BT (List (List Nat)) := buildBucketsBT h44W h44Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h44Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h44G 6 xs.toFinset) h44Bucket6 := buildBucketsBT_sound (by decide) h44Pairs h44WOk h44PoolsOk h44AutosOk h44EmptyOk h44Check6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h44Bound : Lower h44R h44G 7 := lower_of_forestBT (essPairs := [(VAR 0,4,5),(VAR 1,4,6),(VAR 2,1,5),(VAR 3,1,9),(VAR 4,3,19)]) (by decide +kernel) h44Bucket6Ok (by decide +kernel)
def h45R : List Nat := varsOf 45
def h45G : Nat := 0xfffafffafaf0faf0fffafffafaf0faf0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45Bound : Lower h45R h45G 5 := carry_of (swaps := [(4,5)]) (roots2 := h43R) (T2 := h43G) (by decide +kernel) h43Bound
def h46R : List Nat := varsOf 47
def h46G : Nat := 0xeee8eee8eae0eae0eee8eee8eae0eae0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Bound : Lower h46R h46G 7 := carry_of (swaps := [(4,5)]) (roots2 := h44R) (T2 := h44G) (by decide +kernel) h44Bound
namespace Cofactor12168
def G_0 : Nat := 0xffffff00ff000000ffffff00ff000000
def R_0 : List Nat := varsOf 56
def pos_0 : List Nat := [24,24,40,40,48,48,24,40,48]
def neg_0 : List Nat := [16,8,32,8,32,16,32,16,8]
def fmask_0 : Nat := fullMask 9
def base_0 : List Decor := [(0xff00ff00ff00ff00ff00ff00ff00ff00,0xcf,0x10a),(0xffff0000ffff0000ffff0000ffff0000,0x173,0xa1),(0xffffffff00000000ffffffff00000000,0x1bc,0x54)]
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
lemma root_0_ok : forestRootCheck R_0 G_0 [(VAR 3,24,16),(VAR 4,24,8),(VAR 5,40,8)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_0_in : bucketContainsBT bk_0_3 R_0 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_0 : Lower R_0 G_0 4 := lower_of_forestBT root_0_ok bk_0_3_ok root_0_in

def G_11 : Nat := 0xffc0fc00ffc0fc00ffc0fc00ffc0fc00
def R_11 : List Nat := varsOf 30
def pos_11 : List Nat := [10,10,12,12,14,22,22,22,24,24,26,28,10,10,10,12,12,12,22,24,24,24]
def neg_11 : List Nat := [8,2,8,4,6,20,18,6,16,8,18,20,6,18,20,6,18,20,8,6,18,20]
def fmask_11 : Nat := fullMask 22
def base_11 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0x474f3,0x19b4d2),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x788fc,0x2ad8b8),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x3bff1f,0x40205),(0xffff0000ffff0000ffff0000ffff0000,0x3c0fe0,0x336d60)]
def steps_11 : List (Nat × Nat × Nat) := [(3,0,2),(2,0,1),(2,0,2),(1,0,2),(1,0,1),(0,0,2),(0,0,1),(0,1,7),(3,0,1),(1,5,3),(1,9,1),(3,5,3),(3,1,7),(3,9,1),(3,10,8)]
def W_11 : BT Decor := buildWiresBT 5 base_11 steps_11
def autosL_11 : List (List (Nat × Nat)) := [[],[(2,4)],[(1,2)],[(1,4),(1,2)],[(1,2),(1,4)],[(1,4)]]
def autos_11 : BT (List (Nat × Nat)) := btOfList 3 autosL_11
def slicesL_11 : List (Option (Nat × Nat)) := []
def slices_11 : BT (Option (Nat × Nat)) := btOfList 1 slicesL_11
def ps_11 : List PoolSpec := []
def P_11 : BT (Option BoundPool) := buildPoolsBT 1 W_11 R_11 slices_11 ps_11
lemma gp_11 : goodPairs G_11 pos_11 neg_11 := goodPairs_of (by decide +kernel)
lemma base_11_ok : ∀ x ∈ base_11, faithful pos_11 neg_11 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_11_ok : btAll (fun x => faithful pos_11 neg_11 x ∧ x.1 < 2^128) W_11 := buildWiresBT_faithful base_11_ok
set_option maxRecDepth 500000 in
lemma autos_11_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_11 = G_11) autos_11 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma slices_11_ok : btAll (fun o => ∀ p, o = some p → Slice R_11 G_11 p.1 p.2) slices_11 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_11 G_11 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 500000 in
lemma P_11_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_11 G_11 c) P_11 := buildPoolsBT_sound slices_11_ok
def bk_11_init : BT (List (List Nat)) := BT.empty
lemma bk_11_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_11 (0 - 1) xs.toFinset) bk_11_init := trivial
def nodes_11_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_11_0 : checkNodesBT W_11 G_11 fmask_11 P_11 autos_11 bk_11_init 0 nodes_11_0 = true := by decide +kernel
def bk_11_0 : BT (List (List Nat)) := buildBucketsBT W_11 nodes_11_0
set_option maxRecDepth 500000 in
lemma bk_11_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_11 0 xs.toFinset) bk_11_0 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok P_11_ok autos_11_ok bk_11_init_ok chk_11_0
def nodes_11_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_11_1 : checkNodesBT W_11 G_11 fmask_11 P_11 autos_11 bk_11_0 1 nodes_11_1 = true := by decide +kernel
def bk_11_1 : BT (List (List Nat)) := buildBucketsBT W_11 nodes_11_1
set_option maxRecDepth 500000 in
lemma bk_11_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_11 1 xs.toFinset) bk_11_1 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok P_11_ok autos_11_ok bk_11_0_ok chk_11_1
def nodes_11_2 : List NodeSpec := [([18,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_11_2 : checkNodesBT W_11 G_11 fmask_11 P_11 autos_11 bk_11_1 2 nodes_11_2 = true := by decide +kernel
def bk_11_2 : BT (List (List Nat)) := buildBucketsBT W_11 nodes_11_2
set_option maxRecDepth 500000 in
lemma bk_11_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_11 2 xs.toFinset) bk_11_2 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok P_11_ok autos_11_ok bk_11_1_ok chk_11_2
def nodes_11_3 : List NodeSpec := [([6,4,1,3],[],[]),([0,11,2,3],[],[]),([5,12,2,3],[],[0]),([0,1,2,13],[],[]),([0,14,2,3],[],[]),([0,1,15,2],[],[]),([16,0,2,3],[],[]),([17,0,2,3],[],[]),([10,8,2,3],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_11_3 : checkNodesBT W_11 G_11 fmask_11 P_11 autos_11 bk_11_2 3 nodes_11_3 = true := by decide +kernel
def bk_11_3 : BT (List (List Nat)) := buildBucketsBT W_11 nodes_11_3
set_option maxRecDepth 500000 in
lemma bk_11_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_11 3 xs.toFinset) bk_11_3 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok P_11_ok autos_11_ok bk_11_2_ok chk_11_3
def nodes_11_4 : List NodeSpec := [([4,0,1,2,3],[],[0]),([5,0,1,2,3],[],[0]),([6,0,1,2,3],[],[0]),([0,1,2,7,3],[],[0,1]),([0,1,8,2,3],[],[0]),([9,0,1,2,3],[],[0,1]),([10,0,1,2,3],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_11_4 : checkNodesBT W_11 G_11 fmask_11 P_11 autos_11 bk_11_3 4 nodes_11_4 = true := by decide +kernel
def bk_11_4 : BT (List (List Nat)) := buildBucketsBT W_11 nodes_11_4
set_option maxRecDepth 500000 in
lemma bk_11_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_11 4 xs.toFinset) bk_11_4 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok P_11_ok autos_11_ok bk_11_3_ok chk_11_4
def nodes_11_5 : List NodeSpec := [([0,1,2,3],[],[0,2,1,3,4,5])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_11_5 : checkNodesBT W_11 G_11 fmask_11 P_11 autos_11 bk_11_4 5 nodes_11_5 = true := by decide +kernel
def bk_11_5 : BT (List (List Nat)) := buildBucketsBT W_11 nodes_11_5
set_option maxRecDepth 500000 in
lemma bk_11_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_11 5 xs.toFinset) bk_11_5 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok P_11_ok autos_11_ok bk_11_4_ok chk_11_5
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_11_ok : forestRootCheck R_11 G_11 [(VAR 1,10,8),(VAR 2,12,8),(VAR 3,10,2),(VAR 4,22,6)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_11_in : bucketContainsBT bk_11_5 R_11 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_11 : Lower R_11 G_11 6 := lower_of_forestBT root_11_ok bk_11_5_ok root_11_in

def G_12 : Nat := 0xffffff00ff00f000ffffff00ff00f000
def R_12 : List Nat := varsOf 60
lemma low_12_ok : liftCheck 4 0 R_12 G_12 R_0 G_0 [(VAR 2,12,8)] = true := by decide +kernel
lemma low_12 : Lower R_12 G_12 5 := lift_of low_12_ok low_0

def G_30 : Nat := 0xffffff00ff00cc00ffffff00ff00cc00
def R_30 : List Nat := varsOf 58
lemma low_30_ok : carryOK [(1,2)] R_30 G_30 R_12 G_12 = true := by decide +kernel
lemma low_30 : Lower R_30 G_30 5 := carry_of low_30_ok low_12

def G_37 : Nat := 0xffffff00ffc0fc00ffffff00ffc0fc00
def R_37 : List Nat := varsOf 62
def pos_37 : List Nat := [10,10,12,12,14,22,22,22,24,24,26,28,40,40,42,44,46,48,48,50,50,52,52,54,10,10,10,12,12,12,22,22,24,24,24,40,40,40,48,48,48,48]
def neg_37 : List Nat := [8,2,8,4,6,20,18,6,16,8,18,20,32,8,34,36,38,32,16,34,18,36,20,38,18,20,38,18,20,38,8,38,18,20,38,18,20,38,8,18,20,38]
def fmask_37 : Nat := fullMask 42
def base_37 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xc79944f3,0x2adad9944d2),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf8e188fc,0x336b6e188b8),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x3f3f01ff1f,0x4040002205),(0xffff0000ffff0000ffff0000ffff0000,0x3c7c0fe0fe0,0x19b1b540d60),(0xffffffff00000000ffffffff00000000,0x3f800fff000,0x224a4abd000)]
def steps_37 : List (Nat × Nat × Nat) := [(3,2,3),(2,2,3),(1,2,3),(1,0,3),(0,2,3),(3,0,3),(3,0,2),(1,0,2),(1,5,0),(2,7,4),(0,11,3),(3,0,7),(0,0,7),(3,10,2),(1,9,4),(2,0,9),(1,0,9),(0,2,8),(1,10,1),(3,11,3),(1,6,0),(1,10,2),(3,1,12),(3,2,8),(3,12,3),(2,12,3),(1,11,3),(1,12,3),(2,11,3),(0,12,3),(1,6,5),(2,14,0),(2,25,1),(3,1,7),(1,0,19),(2,1,9),(1,1,9),(2,0,19),(3,1,32),(0,14,0),(1,15,1),(1,22,4),(1,1,22),(2,31,4),(3,1,31),(1,15,4),(1,29,1),(2,32,4),(2,14,1),(1,1,19)]
def W_37 : BT Decor := buildWiresBT 6 base_37 steps_37
def autosL_37 : List (List (Nat × Nat)) := [[],[(1,2)]]
def autos_37 : BT (List (Nat × Nat)) := btOfList 1 autosL_37
def slicesL_37 : List (Option (Nat × Nat)) := [some (subcubeFast 32 0,6),some (subcubeFast 4 0,5),some (subcubeFast 6 0,4),some (subcubeFast 2 0,5)]
def slices_37 : BT (Option (Nat × Nat)) := btOfList 2 slicesL_37
def ps_37 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(0,[(1,2,3),(3,0,7)]),(3,[]),(0,[(1,2,3),(0,0,7)]),(0,[(0,2,3),(2,0,9)]),(0,[(0,2,3),(1,0,9)]),(0,[(2,2,3),(3,2,3)]),(0,[(3,0,3),(1,10,1)]),(0,[(1,0,2),(3,1,12)]),(0,[(3,2,3)]),(0,[(2,2,3)]),(0,[(1,2,3)]),(0,[(1,0,3)]),(0,[(0,2,3)]),(0,[(3,0,3)]),(0,[(3,0,2)]),(0,[(1,0,2)])]
def P_37 : BT (Option BoundPool) := buildPoolsBT 5 W_37 R_37 slices_37 ps_37
lemma gp_37 : goodPairs G_37 pos_37 neg_37 := goodPairs_of (by decide +kernel)
lemma base_37_ok : ∀ x ∈ base_37, faithful pos_37 neg_37 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_37_ok : btAll (fun x => faithful pos_37 neg_37 x ∧ x.1 < 2^128) W_37 := buildWiresBT_faithful base_37_ok
set_option maxRecDepth 500000 in
lemma autos_37_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_37 = G_37) autos_37 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_37_0_ok : sliceDirectCheck 32 0 0 R_37 G_37 R_11 G_11 = true := by decide +kernel
lemma sl_37_0 : Slice R_37 G_37 (subcubeFast 32 0) 6 := slice_fast_direct sl_37_0_ok low_11
lemma sl_37_1_ok : sliceDirectCheck 4 0 0 R_37 G_37 R_30 G_30 = true := by decide +kernel
lemma sl_37_1 : Slice R_37 G_37 (subcubeFast 4 0) 5 := slice_fast_direct sl_37_1_ok low_30
lemma sl_37_2_ok : sliceDirectCheck 6 0 0 R_37 G_37 R_0 G_0 = true := by decide +kernel
lemma sl_37_2 : Slice R_37 G_37 (subcubeFast 6 0) 4 := slice_fast_direct sl_37_2_ok low_0
lemma sl_37_3_ok : sliceDirectCheck 2 0 0 R_37 G_37 R_12 G_12 = true := by decide +kernel
lemma sl_37_3 : Slice R_37 G_37 (subcubeFast 2 0) 5 := slice_fast_direct sl_37_3_ok low_12
set_option maxRecDepth 500000 in
lemma slices_37_ok : btAll (fun o => ∀ p, o = some p → Slice R_37 G_37 p.1 p.2) slices_37 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_37 G_37 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_37_0) (forall_cons (fun _ h => by cases h; exact sl_37_1) (forall_cons (fun _ h => by cases h; exact sl_37_2) (forall_cons (fun _ h => by cases h; exact sl_37_3) (fun _ h => (List.not_mem_nil h).elim)))))
set_option maxRecDepth 500000 in
lemma P_37_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_37 G_37 c) P_37 := buildPoolsBT_sound slices_37_ok
def bk_37_init : BT (List (List Nat)) := BT.empty
lemma bk_37_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_37 (0 - 1) xs.toFinset) bk_37_init := trivial
def nodes_37_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_37_0 : checkNodesBT W_37 G_37 fmask_37 P_37 autos_37 bk_37_init 0 nodes_37_0 = true := by decide +kernel
def bk_37_0 : BT (List (List Nat)) := buildBucketsBT W_37 nodes_37_0
set_option maxRecDepth 500000 in
lemma bk_37_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_37 0 xs.toFinset) bk_37_0 :=
  buildBucketsBT_sound (by decide) gp_37 W_37_ok P_37_ok autos_37_ok bk_37_init_ok chk_37_0
def nodes_37_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_37_1 : checkNodesBT W_37 G_37 fmask_37 P_37 autos_37 bk_37_0 1 nodes_37_1 = true := by decide +kernel
def bk_37_1 : BT (List (List Nat)) := buildBucketsBT W_37 nodes_37_1
set_option maxRecDepth 500000 in
lemma bk_37_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_37 1 xs.toFinset) bk_37_1 :=
  buildBucketsBT_sound (by decide) gp_37 W_37_ok P_37_ok autos_37_ok bk_37_0_ok chk_37_1
def nodes_37_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_37_2 : checkNodesBT W_37 G_37 fmask_37 P_37 autos_37 bk_37_1 2 nodes_37_2 = true := by decide +kernel
def bk_37_2 : BT (List (List Nat)) := buildBucketsBT W_37 nodes_37_2
set_option maxRecDepth 500000 in
lemma bk_37_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_37 2 xs.toFinset) bk_37_2 :=
  buildBucketsBT_sound (by decide) gp_37 W_37_ok P_37_ok autos_37_ok bk_37_1_ok chk_37_2
def nodes_37_3 : List NodeSpec := [([53,36,2,3],[],[]),([2,3,39,54],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_37_3 : checkNodesBT W_37 G_37 fmask_37 P_37 autos_37 bk_37_2 3 nodes_37_3 = true := by decide +kernel
def bk_37_3 : BT (List (List Nat)) := buildBucketsBT W_37 nodes_37_3
set_option maxRecDepth 500000 in
lemma bk_37_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_37 3 xs.toFinset) bk_37_3 :=
  buildBucketsBT_sound (by decide) gp_37 W_37_ok P_37_ok autos_37_ok bk_37_2_ok chk_37_3
def nodes_37_4 : List NodeSpec := [([6,35,0,1,4],[],[]),([0,1,2,3,19],[],[]),([36,14,1,2,3],[],[0]),([14,16,1,2,3],[],[]),([37,0,2,3,4],[],[]),([38,16,2,3,4],[],[]),([38,17,2,3,4],[],[]),([0,1,2,7,19],[],[]),([1,2,3,19,39],[],[0]),([35,0,1,2,4],[],[]),([0,1,3,7,19],[],[]),([5,0,1,2,19],[],[]),([6,0,1,3,19],[],[]),([20,1,2,3,19],[],[]),([40,2,21,3,4],[],[]),([14,17,1,2,3],[],[]),([35,0,1,3,4],[],[]),([2,21,41,3,4],[],[]),([5,1,2,21,4],[],[]),([1,2,21,7,4],[],[]),([14,0,1,2,3],[],[]),([42,1,2,3,19],[],[]),([43,0,2,3,4],[],[]),([5,18,0,1,4],[],[]),([44,14,1,2,3],[],[]),([16,1,2,3,4],[],[]),([0,45,2,3,4],[],[]),([0,1,2,3,46],[],[]),([5,0,23,2,4],[],[]),([10,1,2,31,4],[],[]),([0,2,47,3,4],[],[]),([5,35,0,1,4],[],[]),([11,1,26,3,4],[],[]),([48,0,1,2,3],[],[]),([6,5,0,1,4],[],[]),([49,0,2,3,4],[],[]),([0,1,2,3,50],[],[]),([0,51,2,3,4],[],[]),([1,2,34,8,4],[],[]),([52,0,1,2,3],[],[]),([1,2,21,3,19],[],[]),([1,2,21,3,4],[],[]),([0,23,2,7,4],[],[]),([1,22,12,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_37_4 : checkNodesBT W_37 G_37 fmask_37 P_37 autos_37 bk_37_3 4 nodes_37_4 = true := by decide +kernel
def bk_37_4 : BT (List (List Nat)) := buildBucketsBT W_37 nodes_37_4
set_option maxRecDepth 500000 in
lemma bk_37_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_37 4 xs.toFinset) bk_37_4 :=
  buildBucketsBT_sound (by decide) gp_37 W_37_ok P_37_ok autos_37_ok bk_37_3_ok chk_37_4
def nodes_37_5 : List NodeSpec := [([0,13,1,2,3,4],[],[]),([6,5,0,1,3,4],[],[0]),([6,5,0,1,2,4],[],[0]),([14,0,1,2,3,7],[0],[0,1]),([15,0,1,2,3,4],[1,0],[0]),([11,10,1,2,3,4],[2],[0]),([14,0,1,2,3],[],[0,1]),([6,0,1,2,3,4],[],[0]),([16,1,2,3,4],[3],[]),([0,1,2,3,7,4],[4,1,0],[0,1]),([17,1,2,3,7,4],[2,5],[0]),([0,1,9,3,7,4],[],[0]),([18,0,1,2,3,4],[4],[0]),([0,1,9,2,7,4],[],[0,1]),([0,1,9,2,3,19],[0],[0,1]),([11,1,2,12,3,4],[0,2],[]),([0,1,2,3,19],[],[0,1]),([5,0,1,2,3,4],[],[0]),([6,0,1,9,3,4],[0],[0]),([0,1,2,8,7,4],[4],[]),([20,1,9,2,3,4],[2,6],[0,1]),([16,0,1,2,3,4],[],[]),([0,1,2,21,3,4],[],[]),([1,2,21,3,4],[7],[0]),([6,5,0,1,4],[8],[0]),([0,1,22,2,3,4],[1,4,0],[0]),([0,1,9,2,3,4],[4,1,0],[0,1]),([10,1,2,3,8,4],[2],[]),([5,0,1,2,8,4],[4],[]),([5,10,0,1,2,4],[4],[0]),([16,1,2,3,7,4],[4,3],[1,0]),([0,23,2,3,4],[9],[0]),([5,0,1,9,2,4],[0],[0,1]),([0,24,1,2,3,4],[],[]),([0,25,1,2,3,4],[1],[0]),([10,0,23,2,3,4],[1,2],[]),([0,1,2,26,3,4],[],[0]),([27,0,2,12,3,4],[1],[]),([6,0,1,2,7,4],[0],[0]),([28,0,1,2,3,4],[],[]),([29,0,1,2,3,4],[1],[0]),([27,0,2,3,4],[10],[]),([30,0,1,2,3,4],[],[]),([10,0,1,2,7,4],[4],[0]),([0,1,2,3,31,4],[1,0],[0]),([5,0,1,3,7,4],[0],[0]),([0,1,2,3,32,4],[1,0],[0]),([1,9,2,21,3,4],[4,7],[0]),([1,2,12,3,8,4],[2],[0]),([33,0,1,2,3,4],[],[]),([0,1,2,34,3,4],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_37_5 : checkNodesBT W_37 G_37 fmask_37 P_37 autos_37 bk_37_4 5 nodes_37_5 = true := by decide +kernel
def bk_37_5 : BT (List (List Nat)) := buildBucketsBT W_37 nodes_37_5
set_option maxRecDepth 500000 in
lemma bk_37_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_37 5 xs.toFinset) bk_37_5 :=
  buildBucketsBT_sound (by decide) gp_37 W_37_ok P_37_ok autos_37_ok bk_37_4_ok chk_37_5
def nodes_37_6 : List NodeSpec := [([5,0,1,2,3,4],[4,1,0,11],[0,1]),([6,0,1,2,3,4],[4,1,0,12],[0,1]),([0,1,2,3,7,4],[4,13,1],[0,1]),([0,1,2,3,8,4],[4,2,14],[0]),([0,1,9,2,3,4],[4,15,1],[0,1]),([10,0,1,2,3,4],[4,1,2,0,16],[0]),([11,0,1,2,3,4],[4,1,2,0,17],[0]),([0,1,2,12,3,4],[2,18],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_37_6 : checkNodesBT W_37 G_37 fmask_37 P_37 autos_37 bk_37_5 6 nodes_37_6 = true := by decide +kernel
def bk_37_6 : BT (List (List Nat)) := buildBucketsBT W_37 nodes_37_6
set_option maxRecDepth 500000 in
lemma bk_37_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_37 6 xs.toFinset) bk_37_6 :=
  buildBucketsBT_sound (by decide) gp_37 W_37_ok P_37_ok autos_37_ok bk_37_5_ok chk_37_6
def nodes_37_7 : List NodeSpec := [([0,1,2,3,4],[4,2,0],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_37_7 : checkNodesBT W_37 G_37 fmask_37 P_37 autos_37 bk_37_6 7 nodes_37_7 = true := by decide +kernel
def bk_37_7 : BT (List (List Nat)) := buildBucketsBT W_37 nodes_37_7
set_option maxRecDepth 500000 in
lemma bk_37_7_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_37 7 xs.toFinset) bk_37_7 :=
  buildBucketsBT_sound (by decide) gp_37 W_37_ok P_37_ok autos_37_ok bk_37_6_ok chk_37_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_37_ok : forestRootCheck R_37 G_37 [(VAR 1,10,8),(VAR 2,12,8),(VAR 3,10,2),(VAR 4,22,6),(VAR 5,40,8)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_37_in : bucketContainsBT bk_37_7 R_37 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_37 : Lower R_37 G_37 8 := lower_of_forestBT root_37_ok bk_37_7_ok root_37_in

end Cofactor12168
def h47R : List Nat := varsOf 55
def h47G : Nat := 0xeeeeeaeaeaeae8e8eeeeeaeaeaeae8e8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h47Bound : Lower h47R h47G 8 := carry_of (swaps := [(2,3),(3,4),(4,5),(1,2),(2,3),(3,4),(0,1),(1,2),(2,3)]) (roots2 := Cofactor12168.R_37) (T2 := Cofactor12168.G_37) (by decide +kernel) Cofactor12168.low_37
def h48R : List Nat := varsOf 59
def h48G : Nat := 0xeeeeeeeeeeeeee88eeeeeeeeeeeeee88
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Bound : Lower h48R h48G 6 := lift_of (z := 24) (o := 0) (essPairs := [(VAR 3,1,9),(VAR 4,1,17)]) (by decide +kernel) h16Bound
def h49R : List Nat := varsOf 61
def h49G : Nat := 0xfffafaf0faf0faa0fffafaf0faf0faa0
def h49Pos : List Nat := [9,12,5,5,20,12,9,20,36,49,49,56,25,21,56,41,37,20,9,20,25,41,56,49,28,44,9,5,36,25,25,12,36,36,52,20,21,20,49,9,37,9,25]
def h49Neg : List Nat := [8,8,1,4,17,4,1,4,4,17,33,40,24,17,24,40,33,24,4,16,17,33,48,48,24,40,0,0,33,16,1,0,32,48,48,48,4,0,1,24,4,33,8]
def h49Mask : Nat := fullMask 43
def h49Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x7d06cb5b64d,0x24050312654),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x13f9b0b21be,0x110000401a8),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x680e774d863,0x4800302d803),(0xffff0000ffff0000ffff0000ffff0000,0x47c61da7e90,0x8e21da7210),(0xffffffff00000000ffffffff00000000,0x14712e1cf00,0x20f12e18c00)]
def h49Steps : List (Nat × Nat × Nat) := [(1,0,1),(3,0,1),(0,0,2),(1,0,2),(1,1,2),(0,3,4),(1,3,4),(2,3,4),(0,3,5),(2,3,5),(0,3,8),(1,3,8),(2,3,8),(3,3,8),(1,5,8),(2,5,8),(0,5,9),(0,1,3),(1,1,3),(2,1,3),(3,1,3),(0,1,8),(3,1,8),(3,1,9),(2,1,2),(3,2,3),(1,2,4),(3,2,5),(3,2,8),(1,3,26),(2,3,26),(3,0,2),(1,0,3),(3,0,3),(3,0,9),(1,2,39),(0,3,19),(3,3,19),(3,4,19),(1,0,29),(2,5,29),(1,0,30),(1,1,46),(3,2,46),(2,5,30),(1,0,10),(1,1,50),(3,1,50),(1,2,50),(3,2,50),(1,1,10),(3,0,55),(0,4,55),(1,2,10),(3,2,51),(2,5,10),(1,0,13),(1,1,14),(3,0,62),(3,2,62),(0,2,61),(1,2,61),(2,2,61),(3,2,61),(1,4,22),(2,4,22),(2,8,22),(3,2,23),(1,7,57),(3,4,23),(0,8,23),(3,8,23),(1,2,76),(1,0,24),(1,2,78),(3,2,78),(2,8,24),(2,19,26),(2,8,10),(2,4,83),(1,0,12),(1,8,12),(3,2,86),(2,8,12),(1,4,88),(3,0,16),(3,15,16),(1,2,90),(1,4,17),(2,4,17),(1,7,84),(3,0,31),(0,31,37),(3,1,92)]
def h49W : BT Decor := buildWiresBT 7 h49Base h49Steps
def h49AutoList : List (List (Nat × Nat)) := [[],[(4,5)],[(0,3)],[(4,5),(0,3)]]
def h49Autos : BT (List (Nat × Nat)) := btOfList 2 h49AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Pairs : goodPairs h49G h49Pos h49Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49BaseOk : ∀ x ∈ h49Base, faithful h49Pos h49Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49WOk : btAll (fun x => faithful h49Pos h49Neg x ∧ x.1 < 2^128) h49W := buildWiresBT_faithful h49BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h49G = h49G) h49Autos := btAll_ofList (autos_of (by decide +kernel))
def h49SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 16,5),some (subcubeFast 0 32,5),some (subcubeFast 1 0,6),some (subcubeFast 4 0,5),some (subcubeFast 4 16,4),some (subcubeFast 4 32,4),some (subcubeFast 8 0,6),some (subcubeFast 16 0,5),some (subcubeFast 32 0,5),some (subcubeFast 48 0,4)]
def h49Slices : BT (Option (Nat × Nat)) := btOfList 4 h49SliceList
def h49Specs : List PoolSpec := [(2,[]),(3,[]),(0,[(1,0,1),(1,1,2)]),(1,[(1,0,1),(1,1,2)]),(6,[(1,0,1)]),(6,[]),(2,[(1,1,2)]),(0,[(1,0,1)]),(1,[(1,0,1)]),(4,[]),(5,[]),(7,[]),(0,[]),(8,[]),(1,[]),(2,[(2,1,2)]),(9,[]),(6,[(1,0,1),(0,3,19)]),(2,[(3,2,5)]),(6,[(3,0,1)]),(6,[(3,0,9)]),(2,[(0,1,3)]),(2,[(0,1,3),(1,4,22)]),(0,[(1,4,22)]),(2,[(0,1,3),(2,4,22)]),(2,[(0,3,5),(1,2,61)]),(2,[(0,1,3),(2,8,22)]),(2,[(1,1,3)]),(7,[(0,4,55)]),(2,[(1,1,3),(3,4,23)]),(2,[(1,1,3),(0,8,23)]),(2,[(1,1,3),(3,8,23)]),(2,[(2,1,3)]),(2,[(3,1,3)]),(2,[(0,1,8)]),(2,[(0,1,8),(1,3,26)]),(2,[(0,1,8),(2,3,26)]),(2,[(1,5,8)]),(2,[(1,5,8),(0,3,19)]),(2,[(1,5,8),(3,3,19)]),(2,[(2,5,8)]),(2,[(3,1,8)]),(6,[(3,1,8)]),(2,[(0,3,4)]),(2,[(0,3,4),(1,3,4)]),(2,[(1,3,4)]),(2,[(2,3,4)]),(2,[(2,3,4),(1,8,12)]),(2,[(2,3,4),(2,8,12)]),(2,[(0,3,8)]),(2,[(0,3,8),(1,3,8)]),(2,[(1,3,8)]),(2,[(2,3,8)]),(6,[(1,0,30)]),(2,[(2,3,8),(1,4,17)]),(2,[(2,3,8),(2,4,17)]),(2,[(3,3,8)]),(6,[(1,0,3)]),(2,[(3,2,3)]),(8,[(1,0,3)]),(8,[(3,2,3)]),(3,[(0,3,4)]),(6,[(3,0,3)]),(8,[(3,0,3)]),(1,[(1,1,3)]),(6,[(0,1,3)]),(2,[(0,3,5)]),(6,[(0,1,3),(1,4,22)]),(6,[(0,1,3),(2,4,22)]),(6,[(1,1,3)]),(3,[(3,4,23)]),(6,[(1,1,3),(3,4,23)]),(7,[(3,4,23)]),(6,[(2,1,3)]),(6,[(3,1,3)]),(6,[(0,3,4)]),(6,[(0,3,4),(1,3,4)]),(6,[(1,3,4)]),(6,[(2,3,4)]),(6,[(2,3,4),(1,0,12)]),(8,[(1,0,12)])]
def h49Pools : BT (Option BoundPool) := buildPoolsBT 7 h49W h49R h49Slices h49Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Slice9 : Slice h49R h49G (subcubeFast 48 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h2Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Slice8 : Slice h49R h49G (subcubeFast 32 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h13Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Slice7 : Slice h49R h49G (subcubeFast 16 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h21Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Slice6 : Slice h49R h49G (subcubeFast 8 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h27Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Slice5 : Slice h49R h49G (subcubeFast 4 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h30Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Slice4 : Slice h49R h49G (subcubeFast 4 16) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h32Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Slice3 : Slice h49R h49G (subcubeFast 4 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h35Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Slice2 : Slice h49R h49G (subcubeFast 1 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h40Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Slice1 : Slice h49R h49G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h43Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Slice0 : Slice h49R h49G (subcubeFast 0 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h45Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h49R h49G p.1 p.2) h49Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h49R h49G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h49Slice0) (forall_cons (fun _ h => by cases h; exact h49Slice1) (forall_cons (fun _ h => by cases h; exact h49Slice2) (forall_cons (fun _ h => by cases h; exact h49Slice3) (forall_cons (fun _ h => by cases h; exact h49Slice4) (forall_cons (fun _ h => by cases h; exact h49Slice5) (forall_cons (fun _ h => by cases h; exact h49Slice6) (forall_cons (fun _ h => by cases h; exact h49Slice7) (forall_cons (fun _ h => by cases h; exact h49Slice8) (forall_cons (fun _ h => by cases h; exact h49Slice9) (fun _ h => (List.not_mem_nil h).elim)))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h49R h49G c) h49Pools := buildPoolsBT_sound h49SlicesOk
def h49Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h49G (3 - 1) xs.toFinset) h49Empty := trivial
def h49Block3_0 : List NodeSpec := nodesWithIdentity [([3,8,21,57],[]),([1,3,8,73],[]),([3,8,21,89],[]),([3,8,21,84],[]),([1,3,8,95],[]),([3,4,21,76],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test3_0 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Empty 3 h49Block3_0 = true := by decide +kernel
def h49Nodes3 : List NodeSpec := h49Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Check3 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Empty 3 h49Nodes3 = true := h49Test3_0
def h49Bucket3 : BT (List (List Nat)) := buildBucketsBT h49W h49Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h49G 3 xs.toFinset) h49Bucket3 := buildBucketsBT_sound (by decide) h49Pairs h49WOk h49PoolsOk h49AutosOk h49EmptyOk h49Check3
def h49Block4_0 : List NodeSpec := nodesWithIdentity [([1,2,4,39,41],[]),([0,1,2,41,43],[]),([0,1,2,42,43],[]),([0,1,3,4,59],[]),([1,3,7,8,57],[]),([0,2,3,4,82],[]),([0,1,2,11,83],[16]),([0,1,2,4,91],[]),([0,1,2,18,93],[16]),([1,3,7,8,89],[]),([1,3,7,8,84],[]),([1,2,10,37,96],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test4_0 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket3 4 h49Block4_0 = true := by decide +kernel
def h49Block4_1 : List NodeSpec := nodesWithIdentity [([1,3,4,65,66],[25]),([2,3,4,21,63],[]),([1,3,4,7,76],[31]),([0,2,3,21,57],[]),([0,1,2,3,73],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test4_1 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket3 4 h49Block4_1 = true := by decide +kernel
def h49Nodes4 : List NodeSpec := h49Block4_0 ++ h49Block4_1
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Check4 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket3 4 h49Nodes4 = true := by
  unfold h49Nodes4 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h49Test4_0,h49Test4_1⟩
def h49Bucket4 : BT (List (List Nat)) := buildBucketsBT h49W h49Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h49G 4 xs.toFinset) h49Bucket4 := buildBucketsBT_sound (by decide) h49Pairs h49WOk h49PoolsOk h49AutosOk h49Bucket3Ok h49Check4
def h49Block5_0 : List NodeSpec := nodesWithIdentity [([3,4,5,8,9],[0,1,2,3,4,5,6]),([1,3,4,5,8,9],[0,1,5]),([2,3,4,5,8,26],[0]),([2,3,4,5,8,27],[0]),([1,3,4,5,8,32],[0,5]),([2,3,4,5,9,39],[1]),([1,2,3,4,5,39],[0]),([0,1,2,3,4,19],[11,12,13,14]),([0,2,3,4,5,45],[]),([1,2,3,4,5,46],[1]),([0,1,3,4,30,32],[12]),([0,1,2,3,4,47],[12])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test5_0 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket4 5 h49Block5_0 = true := by decide +kernel
def h49Block5_1 : List NodeSpec := [([0,1,2,3,4,49],[5],[0]),([0,1,2,3,4,39],[],[0]),([1,2,3,4,19,39],[0],[0,1]),([0,1,2,3,4,27],[],[0]),([0,2,3,4,19,27],[0],[0]),([0,1,2,4,19,41],[12,16],[0,2]),([0,1,2,4,19,42],[11],[0,1]),([0,2,3,4,5,27],[0],[0]),([0,1,2,4,5,41],[17],[0,2]),([1,2,3,4,5,50],[1,11,13],[0]),([0,2,3,4,5,55],[0,9,10],[0]),([0,1,2,3,4,51],[5,11,12],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test5_1 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket4 5 h49Block5_1 = true := by decide +kernel
def h49Block5_2 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,60],[]),([0,2,3,4,5,62],[0]),([1,2,3,4,8,61],[5,7,11]),([0,1,2,3,8,69],[11,22,23]),([0,1,2,3,8,70],[24]),([0,1,2,3,4,66],[11,25]),([0,1,2,3,4,71],[0,5,26]),([0,1,2,3,8,57],[12,28]),([0,1,2,3,8,74],[29]),([0,1,2,3,4,75],[1,30]),([0,1,2,3,4,76],[31]),([1,2,3,4,8,78],[5])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test5_2 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket4 5 h49Block5_2 = true := by decide +kernel
def h49Block5_3 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,79],[12,13,14]),([0,1,2,3,4,81],[]),([0,2,3,4,19,26],[]),([0,1,2,4,8,34],[35]),([0,1,2,4,8,35],[36]),([1,2,3,4,8,39],[0]),([0,1,2,4,8,41],[38]),([0,1,2,4,8,42],[39]),([1,2,3,4,8,44],[0]),([0,2,3,4,20,27],[]),([1,2,3,4,8,50],[5]),([0,1,2,8,10,11],[11,12,16,44])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test5_3 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket4 5 h49Block5_3 = true := by decide +kernel
def h49Block5_4 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,53],[]),([0,1,2,3,4,83],[11,12]),([0,1,2,3,4,86],[11,47]),([0,1,2,3,4,88],[12,48]),([0,1,2,4,15,16],[50]),([1,2,3,4,8,90],[0]),([1,2,3,4,8,46],[0,53]),([0,1,2,4,17,18],[16]),([0,1,2,3,8,93],[11,54]),([0,1,2,3,8,94],[55]),([0,1,2,3,8,89],[]),([0,1,2,3,8,84],[12,16])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test5_4 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket4 5 h49Block5_4 = true := by decide +kernel
def h49Block5_5 : List NodeSpec := [([1,2,3,4,37,96],[11],[0]),([0,1,2,10,31,37],[12],[0,3]),([0,1,2,3,4,97],[],[0]),([0,1,2,4,10,48],[14],[0,3]),([0,1,2,4,37,58],[0],[0]),([0,1,2,4,38,72],[],[0]),([0,1,2,4,23,92],[16],[0]),([0,1,2,3,4,64],[],[0]),([0,1,3,4,28,92],[],[0]),([0,1,2,3,4,98],[],[0]),([1,2,3,4,61,65],[1,10,11,16,66],[0]),([1,2,3,4,61,66],[7,11],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test5_5 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket4 5 h49Block5_5 = true := by decide +kernel
def h49Block5_6 : List NodeSpec := nodesWithIdentity [([1,2,3,4,61,67],[]),([1,2,3,4,61,68],[]),([1,2,3,4,36,61],[1]),([0,1,2,3,4,68],[1]),([1,2,3,4,7,63],[12]),([1,2,3,4,36,63],[12]),([0,1,2,3,4,77],[12]),([0,1,2,3,7,57],[12,13,28,61]),([0,1,2,3,33,57],[12,28]),([0,1,2,3,4,80],[]),([0,1,2,3,4,52],[]),([0,1,2,3,4,54],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test5_6 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket4 5 h49Block5_6 = true := by decide +kernel
def h49Block5_7 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,56],[]),([0,1,2,3,4,87],[11])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test5_7 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket4 5 h49Block5_7 = true := by decide +kernel
def h49Nodes5 : List NodeSpec := h49Block5_0 ++ h49Block5_1 ++ h49Block5_2 ++ h49Block5_3 ++ h49Block5_4 ++ h49Block5_5 ++ h49Block5_6 ++ h49Block5_7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Check5 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket4 5 h49Nodes5 = true := by
  unfold h49Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨h49Test5_0,h49Test5_1⟩,h49Test5_2⟩,h49Test5_3⟩,h49Test5_4⟩,h49Test5_5⟩,h49Test5_6⟩,h49Test5_7⟩
def h49Bucket5 : BT (List (List Nat)) := buildBucketsBT h49W h49Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h49G 5 xs.toFinset) h49Bucket5 := buildBucketsBT_sound (by decide) h49Pairs h49WOk h49PoolsOk h49AutosOk h49Bucket4Ok h49Check5
def h49Block6_0 : List NodeSpec := [([1,2,3,4,5,8],[0,1,4,5,7,8],[0]),([0,2,3,4,5,9],[0,1,4,5,6,9,10],[0,2]),([0,1,2,3,4,5,9],[0,1,4,5,6],[0,2]),([0,2,3,4,5,29],[0,1,4,5,9,10,15],[0]),([0,1,2,3,4,5,30],[0,5,9,11,12],[0]),([0,1,2,3,4,19],[11,12,13,14],[0,1,2]),([0,1,2,3,4,5,19],[4,5,9,10],[0,1,2]),([0,1,2,3,4,32],[0,1,4,5,11,12,13,14,18],[0,1,2]),([0,1,2,3,4,5,32],[0,1,4,5],[0,2]),([0,1,2,3,4,5,10],[0,1,9,10,11,12,13,14],[0]),([0,1,2,3,4,5,13],[0,1,9,11,12],[0]),([0,1,2,3,4,5,14],[9,11,12],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test6_0 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket5 6 h49Block6_0 = true := by decide +kernel
def h49Block6_1 : List NodeSpec := [([0,1,2,3,4,40],[0,1,5,6,9,10,11,12,13,14,20],[0]),([0,1,2,3,4,8,22],[0,1,5,11,12,21],[0,2]),([0,1,2,3,4,8,23],[11,12,27],[0]),([0,1,2,3,4,8,24],[0,1,5,11,12,32],[0,2]),([0,1,2,3,4,8,25],[9,11,12,33],[0]),([0,1,2,3,4,8,26],[0,1,5,34],[0,1,2]),([0,1,2,3,4,8,19],[1,37],[0,1,2]),([0,1,2,3,4,8,20],[1,40],[0,2]),([0,1,2,3,4,27],[0,5,11,12,13,14,41,42],[0]),([0,1,2,3,4,8,27],[0,1,5,41],[0,2]),([0,1,2,3,4,8,10],[0,5,11,12,13,14,43],[0,2]),([0,1,2,3,4,8,11],[11,12,13,14,16,45],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test6_1 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket5 6 h49Block6_1 = true := by decide +kernel
def h49Block6_2 : List NodeSpec := [([0,1,2,3,4,8,12],[11,12,13,14,46],[0]),([0,1,2,3,4,8,15],[11,12,49],[0]),([0,1,2,3,4,8,16],[11,12,51],[0,2]),([0,1,2,3,4,8,17],[11,12,52],[0,2]),([0,1,2,3,4,8,18],[11,12,56],[0]),([0,1,2,4,30,37],[0,5,9,11,12,57,58,59,60],[0]),([0,1,2,3,4,31,37],[0,5,11,12,13,14],[0,3]),([0,1,2,3,4,48],[0,1,5,9,11,12,13,14,53,58],[0,3]),([0,1,2,4,10,37],[0,9,11,12,14,43,59,61],[0]),([0,1,2,4,23,38],[0,1,11,12,16,27,63,64],[0]),([0,1,2,3,4,62],[0,1,5,9,11,12,13,14],[0,2]),([0,1,2,3,4,92],[0,1,5,11,12,13,14,16,51],[0,2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test6_2 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket5 6 h49Block6_2 = true := by decide +kernel
def h49Block6_3 : List NodeSpec := [([1,2,3,4,61],[1,9,10,11,66],[0]),([0,1,2,3,4,61],[0,1,5,9,10,11,13,14,66],[0]),([0,1,2,3,69],[1,11,14,22,67],[0]),([0,1,2,3,70],[1,11,13,24,68],[0]),([0,1,2,3,4,63],[0,1,5,9,11,12,13,14],[0,2]),([0,1,2,3,57],[9,12,13,16,28,61],[0,2]),([0,1,2,3,74],[9,12,14,29,70,71,72],[0]),([0,1,2,3,4,78],[0,1,5,10,12,13,14,32],[0]),([0,1,2,3,4,50],[0,1,5,11,12,13,43],[0,2,3]),([0,1,2,3,4,55],[0,1,5,9,10,11,12,13,61],[0,2]),([0,1,2,10,11],[9,11,12,16,44,61,76],[0]),([0,1,2,3,4,85],[0,1,5,10,11,12,14,16,46,79,80],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test6_3 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket5 6 h49Block6_3 = true := by decide +kernel
def h49Nodes6 : List NodeSpec := h49Block6_0 ++ h49Block6_1 ++ h49Block6_2 ++ h49Block6_3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Check6 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket5 6 h49Nodes6 = true := by
  unfold h49Nodes6 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨h49Test6_0,h49Test6_1⟩,h49Test6_2⟩,h49Test6_3⟩
def h49Bucket6 : BT (List (List Nat)) := buildBucketsBT h49W h49Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h49G 6 xs.toFinset) h49Bucket6 := buildBucketsBT_sound (by decide) h49Pairs h49WOk h49PoolsOk h49AutosOk h49Bucket5Ok h49Check6
def h49Block7_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,4,5,9,10,11,12,13,14],[0,1]),([0,1,2,3,4,6],[0,1,5,9,10,11,12,13,14,19],[0,2]),([0,1,2,3,4,8],[0,1,5,11,12,13,14],[0,1,2]),([0,1,2,3,4,37],[0,1,5,9,11,12,13,14,16,57],[0]),([0,1,2,3,4,38],[0,1,5,9,11,13,14,16,62],[0,2]),([0,1,2,3,4,22],[0,1,5,9,10,11,13,14,21,65],[0,2]),([0,1,2,3,4,23],[0,1,5,9,10,11,12,13,14,16,27,69],[0,2]),([0,1,2,3,4,24],[0,1,5,10,11,12,13,14,32,73],[0,2]),([0,1,2,3,4,25],[0,1,5,9,10,11,12,13,14,16,33,74],[0]),([0,1,2,3,4,10],[0,1,5,9,10,11,12,13,43,75],[0,1,2,3]),([0,1,2,3,4,11],[0,1,5,9,11,12,13,14,16,45,77],[0]),([0,1,2,3,4,12],[0,1,5,9,10,11,12,13,14,16,46,78],[0,2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test7_0 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket6 7 h49Block7_0 = true := by decide +kernel
def h49Nodes7 : List NodeSpec := h49Block7_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Check7 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket6 7 h49Nodes7 = true := h49Test7_0
def h49Bucket7 : BT (List (List Nat)) := buildBucketsBT h49W h49Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h49G 7 xs.toFinset) h49Bucket7 := buildBucketsBT_sound (by decide) h49Pairs h49WOk h49PoolsOk h49AutosOk h49Bucket6Ok h49Check7
def h49Block8_0 : List NodeSpec := [([0,1,2,3,4],[0,5],[0,1,2,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Test8_0 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket7 8 h49Block8_0 = true := by decide +kernel
def h49Nodes8 : List NodeSpec := h49Block8_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Check8 : checkNodesBT h49W h49G h49Mask h49Pools h49Autos h49Bucket7 8 h49Nodes8 = true := h49Test8_0
def h49Bucket8 : BT (List (List Nat)) := buildBucketsBT h49W h49Nodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h49G 8 xs.toFinset) h49Bucket8 := buildBucketsBT_sound (by decide) h49Pairs h49WOk h49PoolsOk h49AutosOk h49Bucket7Ok h49Check8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Bound : Lower h49R h49G 9 := lower_of_forestBT (essPairs := [(VAR 0,4,5),(VAR 2,1,5),(VAR 3,1,9),(VAR 4,4,20),(VAR 5,4,36)]) (by decide +kernel) h49Bucket8Ok (by decide +kernel)
def h50R : List Nat := varsOf 62
def h50G : Nat := 0xfffcfff0fff0fcc0fffcfff0fff0fcc0
def h50Pos : List Nat := [10,12,6,6,20,12,10,20,36,50,50,24,40,40,50,20,22,38,26,42,12,12,24,40,6,36,26,10,36,10,28,26,6,22]
def h50Neg : List Nat := [8,8,2,4,18,4,2,4,4,18,34,8,8,34,48,16,18,34,18,34,2,0,16,32,0,34,8,18,32,0,8,2,18,2]
def h50Mask : Nat := fullMask 34
def h50Base : List Decor := [(0xcccccccccccccccccccccccccccccccc,0x3ad0f464d,0x38a1f2654),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x3533381be,424),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xecfc3863,0x44001803),(0xffff0000ffff0000ffff0000ffff0000,0x2c445ce90,0x10845c210),(0xffffffff00000000ffffffff00000000,0x128a7700,0x128a6400)]
def h50Steps : List (Nat × Nat × Nat) := [(1,0,1),(2,0,1),(1,0,2),(1,1,2),(1,3,4),(1,3,5),(3,3,8),(3,3,10),(1,4,10),(3,4,10),(1,7,8),(2,7,8),(1,7,10),(1,4,12),(3,4,12),(1,8,12),(2,1,2),(3,1,7),(1,2,3),(2,2,3),(3,2,5),(3,2,7),(1,2,22),(3,2,10),(1,1,12),(1,2,12),(3,2,12),(0,0,3),(1,0,3),(2,0,3),(0,0,8),(3,0,8),(0,3,15),(3,3,15),(3,0,38),(3,4,15),(1,1,26),(2,5,26),(1,4,33),(0,5,23),(1,8,44),(1,3,25),(3,1,43),(1,2,34),(1,4,34),(2,4,34),(2,5,34),(2,8,34),(2,15,34),(1,3,53),(1,1,51),(1,3,35),(2,3,35),(3,0,10),(3,4,17),(3,2,13),(3,2,55),(3,4,45),(2,8,32),(3,2,29),(2,15,35),(3,4,54)]
def h50W : BT Decor := buildWiresBT 7 h50Base h50Steps
def h50AutoList : List (List (Nat × Nat)) := [[],[(4,5)],[(2,3)],[(1,4)],[(1,5)],[(4,5),(2,3)],[(4,5),(1,4)],[(2,3),(1,4)],[(4,5),(1,5)],[(2,3),(1,5)],[(4,5),(2,3),(1,4)],[(4,5),(2,3),(1,5)]]
def h50Autos : BT (List (Nat × Nat)) := btOfList 4 h50AutoList
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
def h50SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 2 0,5),some (subcubeFast 4 0,6),some (subcubeFast 8 0,6),some (subcubeFast 16 0,5),some (subcubeFast 18 0,4),some (subcubeFast 32 0,5),some (subcubeFast 34 0,4),some (subcubeFast 48 0,4)]
def h50Slices : BT (Option (Nat × Nat)) := btOfList 3 h50SliceList
def h50Specs : List PoolSpec := [(1,[]),(0,[]),(2,[(1,0,1)]),(2,[]),(1,[(1,0,2)]),(3,[]),(5,[]),(4,[]),(6,[]),(1,[(1,0,3)]),(5,[(1,0,3)]),(3,[(1,4,33)]),(1,[(2,0,3)]),(5,[(2,0,3)]),(3,[(1,4,34)]),(1,[(2,0,3),(1,4,34)]),(7,[]),(2,[(1,7,8)]),(1,[(3,2,5)]),(1,[(1,3,5)]),(2,[(2,0,1)]),(2,[(3,1,7)]),(1,[(0,0,3)]),(2,[(0,0,3)]),(1,[(0,0,3),(1,0,3)]),(2,[(0,0,3),(1,0,3)]),(2,[(1,0,3)]),(0,[(1,4,33)]),(2,[(2,0,3)]),(1,[(2,0,3),(2,4,34)]),(3,[(2,4,34)]),(2,[(2,0,3),(1,4,34)]),(2,[(2,0,3),(2,4,34)]),(1,[(0,0,8)]),(1,[(0,0,8),(1,3,35)]),(1,[(0,0,8),(2,3,35)]),(1,[(1,0,2),(0,3,15)]),(1,[(1,0,2),(3,3,15)]),(2,[(2,7,8)]),(1,[(3,0,8)]),(2,[(3,0,8)])]
def h50Pools : BT (Option BoundPool) := buildPoolsBT 6 h50W h50R h50Slices h50Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50Slice7 : Slice h50R h50G (subcubeFast 48 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h3Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50Slice6 : Slice h50R h50G (subcubeFast 34 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h7Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50Slice5 : Slice h50R h50G (subcubeFast 32 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h14Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50Slice4 : Slice h50R h50G (subcubeFast 18 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h18Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50Slice3 : Slice h50R h50G (subcubeFast 16 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h22Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50Slice2 : Slice h50R h50G (subcubeFast 8 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h28Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50Slice1 : Slice h50R h50G (subcubeFast 4 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h36Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50Slice0 : Slice h50R h50G (subcubeFast 2 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h38Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h50R h50G p.1 p.2) h50Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h50R h50G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h50Slice0) (forall_cons (fun _ h => by cases h; exact h50Slice1) (forall_cons (fun _ h => by cases h; exact h50Slice2) (forall_cons (fun _ h => by cases h; exact h50Slice3) (forall_cons (fun _ h => by cases h; exact h50Slice4) (forall_cons (fun _ h => by cases h; exact h50Slice5) (forall_cons (fun _ h => by cases h; exact h50Slice6) (forall_cons (fun _ h => by cases h; exact h50Slice7) (fun _ h => (List.not_mem_nil h).elim)))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h50R h50G c) h50Pools := buildPoolsBT_sound h50SlicesOk
def h50Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h50G (3 - 1) xs.toFinset) h50Empty := trivial
def h50Block3_0 : List NodeSpec := nodesWithIdentity [([4,8,33,44],[])]
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
def h50Block4_0 : List NodeSpec := nodesWithIdentity [([3,4,7,8,10],[3]),([3,4,7,8,12],[]),([0,1,2,4,38],[]),([4,5,8,23,33],[]),([1,2,4,33,44],[]),([3,4,5,8,48],[]),([2,3,5,8,49],[]),([1,2,3,15,49],[8,14]),([1,2,3,4,53],[]),([1,2,3,25,49],[]),([2,4,5,8,56],[]),([0,3,4,8,44],[0,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50Test4_0 : checkNodesBT h50W h50G h50Mask h50Pools h50Autos h50Bucket3 4 h50Block4_0 = true := by decide +kernel
def h50Block4_1 : List NodeSpec := nodesWithIdentity [([0,4,8,12,24],[]),([0,1,2,3,59],[]),([1,2,4,36,37],[]),([0,1,2,37,40],[]),([0,1,2,38,40],[]),([0,1,3,4,60],[]),([2,4,8,33,55],[7]),([1,2,4,33,45],[7,10]),([1,2,4,32,39],[]),([2,4,21,33,55],[]),([1,2,4,33,61],[]),([0,1,2,3,62],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50Test4_1 : checkNodesBT h50W h50G h50Mask h50Pools h50Autos h50Bucket3 4 h50Block4_1 = true := by decide +kernel
def h50Block4_2 : List NodeSpec := nodesWithIdentity [([0,1,2,11,50],[]),([1,2,4,15,56],[7,8]),([1,2,3,4,65],[]),([0,1,2,3,66],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50Test4_2 : checkNodesBT h50W h50G h50Mask h50Pools h50Autos h50Bucket3 4 h50Block4_2 = true := by decide +kernel
def h50Nodes4 : List NodeSpec := h50Block4_0 ++ h50Block4_1 ++ h50Block4_2
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50Check4 : checkNodesBT h50W h50G h50Mask h50Pools h50Autos h50Bucket3 4 h50Nodes4 = true := by
  unfold h50Nodes4 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨h50Test4_0,h50Test4_1⟩,h50Test4_2⟩
def h50Bucket4 : BT (List (List Nat)) := buildBucketsBT h50W h50Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h50G 4 xs.toFinset) h50Bucket4 := buildBucketsBT_sound (by decide) h50Pairs h50WOk h50PoolsOk h50AutosOk h50Bucket3Ok h50Check4
def h50Block5_0 : List NodeSpec := [([3,4,5,7,8],[0,1,2,3,4],[0,1,2,5]),([2,3,4,5,7,22],[1],[0]),([1,2,3,4,7,10],[3],[0]),([1,2,3,4,7,12],[],[0]),([0,3,4,5,7,8],[0,1,3],[0]),([0,2,3,4,5,22],[0],[0]),([0,1,2,3,4,15],[5,6],[0,1]),([1,2,3,4,5,42],[],[0]),([2,3,4,5,8,33],[],[0,2]),([1,2,4,5,23,33],[],[0]),([1,2,3,4,15,33],[5,10],[0]),([1,2,3,4,25,33],[5],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50Test5_0 : checkNodesBT h50W h50G h50Mask h50Pools h50Autos h50Bucket4 5 h50Block5_0 = true := by decide +kernel
def h50Block5_1 : List NodeSpec := [([1,2,4,5,12,33],[5],[0]),([1,2,3,4,5,43],[0,7,10,11],[0]),([2,3,4,5,8,34],[],[0]),([1,2,3,4,15,34],[5,13],[0]),([1,2,3,4,25,34],[],[0]),([1,2,3,4,5,48],[],[0]),([1,2,3,5,49],[1,8,13,14,15],[0]),([1,2,3,4,5,51],[],[0]),([2,3,4,5,8,35],[0],[0,1]),([2,3,4,5,8,36],[0],[0]),([0,3,4,5,8,23],[],[0,2,3]),([0,3,4,5,8,25],[0,3],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50Test5_1 : checkNodesBT h50W h50G h50Mask h50Pools h50Autos h50Bucket4 5 h50Block5_1 = true := by decide +kernel
def h50Block5_2 : List NodeSpec := [([0,2,3,4,8,10],[3],[0,3]),([0,2,3,4,8,12],[3],[0]),([0,1,2,3,4,44],[0,3],[0]),([0,1,2,3,4,17],[6],[0,3]),([0,1,2,3,4,31],[],[0]),([0,1,2,3,4,36],[],[0]),([1,2,3,4,15,36],[0],[0,1]),([0,1,2,3,4,22],[],[0]),([0,2,3,4,15,22],[0],[0]),([0,1,2,4,15,37],[16],[0]),([0,1,2,4,38],[],[0]),([0,1,2,3,4,38],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50Test5_2 : checkNodesBT h50W h50G h50Mask h50Pools h50Autos h50Bucket4 5 h50Block5_2 = true := by decide +kernel
def h50Block5_3 : List NodeSpec := [([0,1,2,4,15,38],[5],[0,1]),([1,2,3,4,5,36],[0],[0]),([0,1,2,4,5,38],[],[0]),([0,1,2,3,4,46],[],[0]),([0,1,2,4,9,12],[6],[0]),([0,1,2,3,4,13],[3],[0]),([0,1,2,3,4,19],[],[0]),([1,2,3,4,10,58],[0],[0]),([0,1,2,3,4,28],[],[0]),([0,1,2,3,4,14],[],[0]),([1,2,3,4,5,58],[0],[0]),([0,2,3,4,12,21],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50Test5_3 : checkNodesBT h50W h50G h50Mask h50Pools h50Autos h50Bucket4 5 h50Block5_3 = true := by decide +kernel
def h50Block5_4 : List NodeSpec := [([0,1,2,4,12,24],[],[0]),([0,1,2,3,4,30],[],[0]),([0,1,2,3,4,18],[1],[0]),([1,2,4,8,32,33],[1,7,24],[0,2]),([1,2,4,33,55],[1,7,8,10],[0]),([1,2,3,4,32,36],[],[0]),([0,2,3,4,8,55],[3],[0]),([0,1,2,3,4,45],[1,5,6],[0]),([0,1,2,3,4,63],[],[0]),([0,2,3,4,21,55],[],[0]),([0,1,2,3,4,61],[],[0]),([0,1,2,3,4,39],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50Test5_4 : checkNodesBT h50W h50G h50Mask h50Pools h50Autos h50Bucket4 5 h50Block5_4 = true := by decide +kernel
def h50Block5_5 : List NodeSpec := [([0,1,2,3,4,47],[],[0]),([0,2,3,4,8,29],[3],[0,2]),([0,1,2,4,11,34],[],[0]),([0,1,2,3,8,49],[1,15],[0,2]),([0,1,2,3,8,50],[29,30],[0]),([0,1,2,3,4,20],[],[0]),([0,1,2,3,4,52],[1],[0]),([0,2,3,4,21,29],[],[0]),([0,1,2,3,4,64],[],[0]),([1,2,3,4,15,35],[7,8],[0,1]),([0,1,2,4,8,56],[1,34],[0,2]),([0,1,2,4,8,57],[35],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50Test5_5 : checkNodesBT h50W h50G h50Mask h50Pools h50Autos h50Bucket4 5 h50Block5_5 = true := by decide +kernel
def h50Block5_6 : List NodeSpec := [([0,2,3,4,8,22],[0],[0]),([0,1,2,4,8,37],[7,36],[0]),([0,1,2,4,8,38],[37],[0]),([1,2,3,4,16,36],[],[0]),([0,2,3,4,8,41],[0],[0]),([0,1,2,3,4,54],[6],[0,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50Test5_6 : checkNodesBT h50W h50G h50Mask h50Pools h50Autos h50Bucket4 5 h50Block5_6 = true := by decide +kernel
def h50Nodes5 : List NodeSpec := h50Block5_0 ++ h50Block5_1 ++ h50Block5_2 ++ h50Block5_3 ++ h50Block5_4 ++ h50Block5_5 ++ h50Block5_6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50Check5 : checkNodesBT h50W h50G h50Mask h50Pools h50Autos h50Bucket4 5 h50Nodes5 = true := by
  unfold h50Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨h50Test5_0,h50Test5_1⟩,h50Test5_2⟩,h50Test5_3⟩,h50Test5_4⟩,h50Test5_5⟩,h50Test5_6⟩
def h50Bucket5 : BT (List (List Nat)) := buildBucketsBT h50W h50Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h50G 5 xs.toFinset) h50Bucket5 := buildBucketsBT_sound (by decide) h50Pairs h50WOk h50PoolsOk h50AutosOk h50Bucket4Ok h50Check5
def h50Block6_0 : List NodeSpec := [([1,2,3,4,5,7],[0,1,2,3,4],[0,1,2,5]),([0,1,2,3,4,5,7],[0,1,2,3,4],[0,2]),([1,2,3,4,5,26],[0,1,2,3,7,8],[0]),([1,2,3,4,5,33],[0,1,5,7,8,9,10],[0,2]),([1,2,3,4,5,34],[0,1,5,7,8,12,13],[0]),([0,2,3,4,5,8],[0,1,2,3],[0,1]),([0,1,2,3,4,5,23],[1,5],[0,2,3,7]),([0,1,2,3,4,15],[5,6],[0,1,2]),([0,1,2,3,4,5,15],[3,7,8,17],[0,1,2]),([0,1,2,3,4,25],[0,1,2,3,5,6,18],[0,1,2]),([0,1,2,3,4,5,25],[0,1,2,3],[0,2]),([0,1,2,3,4,5,9],[1,5,6,7,8,16],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50Test6_0 : checkNodesBT h50W h50G h50Mask h50Pools h50Autos h50Bucket5 6 h50Block6_0 = true := by decide +kernel
def h50Block6_1 : List NodeSpec := [([0,1,2,3,4,10],[3,6,7,19],[0,3]),([0,1,2,3,4,5,10],[5,7],[0,3]),([0,1,2,3,4,12],[0,1,3,6,7],[0,3]),([0,1,2,3,4,5,12],[0,1,5,7],[0,3]),([0,1,2,3,4,27],[0,1,3,4,5,6,7,8,21],[0]),([1,2,4,32,33],[1,7,8,10,24,25],[0,2]),([0,1,2,3,4,8,32],[0,1,3,5,22],[0,2,3]),([0,1,2,3,4,55],[0,1,3,5,6,8],[0]),([0,1,2,3,4,8,33],[0,1,3,5,7,9],[0,2,3,7]),([0,1,2,3,4,43],[0,3,7,8,10,11,16,27],[0,2,3,4,7,9]),([0,1,2,3,4,8,34],[0,1,3,5,12],[0,2]),([0,1,2,3,4,29],[0,1,3,6,7,8],[0,2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50Test6_1 : checkNodesBT h50W h50G h50Mask h50Pools h50Autos h50Bucket5 6 h50Block6_1 = true := by decide +kernel
def h50Block6_2 : List NodeSpec := [([0,1,2,3,49],[1,7,8,14,15,31],[0,2]),([0,1,2,3,50],[1,6,7,29,30,32],[0]),([0,1,2,3,4,8,35],[0,1,3,33],[0,1,2]),([0,1,2,3,4,8,15],[1,4],[0,1,2]),([0,1,2,3,4,8,16],[1,38],[0,2]),([0,1,2,3,4,36],[0,3,5,6,39,40],[0,1,3,8]),([0,1,2,3,4,8,36],[0,1,3,39],[0,2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50Test6_2 : checkNodesBT h50W h50G h50Mask h50Pools h50Autos h50Bucket5 6 h50Block6_2 = true := by decide +kernel
def h50Nodes6 : List NodeSpec := h50Block6_0 ++ h50Block6_1 ++ h50Block6_2
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50Check6 : checkNodesBT h50W h50G h50Mask h50Pools h50Autos h50Bucket5 6 h50Nodes6 = true := by
  unfold h50Nodes6 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨h50Test6_0,h50Test6_1⟩,h50Test6_2⟩
def h50Bucket6 : BT (List (List Nat)) := buildBucketsBT h50W h50Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h50G 6 xs.toFinset) h50Bucket6 := buildBucketsBT_sound (by decide) h50Pairs h50WOk h50PoolsOk h50AutosOk h50Bucket5Ok h50Check6
def h50Block7_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,5,6,7,8],[0,1]),([0,1,2,3,4,6],[0,1,3,5,6,7,8,20],[0,2]),([0,1,2,3,4,32],[0,1,3,5,6,8,22,23],[0,2]),([0,1,2,3,4,33],[0,1,3,5,6,7,8,9,16,26],[0,2,3,4,7,9]),([0,1,2,3,4,34],[0,1,3,5,6,7,8,12,28],[0,2]),([0,1,2,3,4,8],[0,1,3,5,6],[0,1,2,3,4,6,7,8,9])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50Test7_0 : checkNodesBT h50W h50G h50Mask h50Pools h50Autos h50Bucket6 7 h50Block7_0 = true := by decide +kernel
def h50Nodes7 : List NodeSpec := h50Block7_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50Check7 : checkNodesBT h50W h50G h50Mask h50Pools h50Autos h50Bucket6 7 h50Nodes7 = true := h50Test7_0
def h50Bucket7 : BT (List (List Nat)) := buildBucketsBT h50W h50Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h50G 7 xs.toFinset) h50Bucket7 := buildBucketsBT_sound (by decide) h50Pairs h50WOk h50PoolsOk h50AutosOk h50Bucket6Ok h50Check7
def h50Block8_0 : List NodeSpec := [([0,1,2,3,4],[0,3],[0,1,2,3,4,6,7,8,9])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50Test8_0 : checkNodesBT h50W h50G h50Mask h50Pools h50Autos h50Bucket7 8 h50Block8_0 = true := by decide +kernel
def h50Nodes8 : List NodeSpec := h50Block8_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50Check8 : checkNodesBT h50W h50G h50Mask h50Pools h50Autos h50Bucket7 8 h50Nodes8 = true := h50Test8_0
def h50Bucket8 : BT (List (List Nat)) := buildBucketsBT h50W h50Nodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h50G 8 xs.toFinset) h50Bucket8 := buildBucketsBT_sound (by decide) h50Pairs h50WOk h50PoolsOk h50AutosOk h50Bucket7Ok h50Check8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h50Bound : Lower h50R h50G 9 := lower_of_forestBT (essPairs := [(VAR 1,4,6),(VAR 2,2,6),(VAR 3,2,10),(VAR 4,4,20),(VAR 5,4,36)]) (by decide +kernel) h50Bucket8Ok (by decide +kernel)
def h0R : List Nat := varsOf 63
def h0G : Nat := 0xeee8eae0eae0e880eee8eae0eae0e880
def h0Pos : List Nat := [13,14,25,14,25,7,14,21,11,22,21,38,37,37,7,13,58,13,22,7,21,25,25,41,37,51,21,41,25,51,51,22,30,46,22,23,39,58,58,51,27,43,57,41,11,7,53,58,38,11,11,11,14,38,13,38,41,27,7,7,11,22,22,25,11,21,23,23,43,38,7,41,14,22,37,45]
def h0Neg : List Nat := [12,12,26,10,24,3,6,20,3,6,5,6,5,36,6,9,56,5,20,5,17,17,9,9,33,49,19,33,19,19,35,26,26,42,19,19,35,42,26,50,19,35,49,40,9,19,49,50,36,19,10,35,26,42,1,34,49,26,2,1,1,4,18,1,2,4,6,5,42,4,35,1,44,2,1,9]
def h0Mask : Nat := fullMask 76
def h0Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcdf9f4e7f987ffaf5b5,0xcc8994a771c7ffa9520),(0xcccccccccccccccccccccccccccccccc,0x37d7ebfb3ffe20d4b6a,0x25546bea3fff4004b6c),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf6e6cf1601f851efeeb,0x12e20010000000e7ec3),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x991935e9f6318e3815f,0x9100234186380c1801f),(0xffff0000ffff0000ffff0000ffff0000,0x20ee200c5edf6750694,0x4312e5cdb6350094),(0xffffffff00000000ffffffff00000000,0xcb001a1cef26b813800,0x15001a9ceb24b012000)]
def h0Steps : List (Nat × Nat × Nat) := [(0,0,1),(2,0,2),(2,0,3),(2,0,4),(2,1,2),(2,1,3),(2,1,4),(2,1,5),(0,2,3),(1,2,3),(0,0,15),(0,1,15),(0,0,17),(2,2,3),(3,2,3),(1,2,4),(1,2,5),(2,2,5),(1,2,6),(3,2,6),(1,3,4),(2,3,4),(1,3,5),(2,3,5),(1,3,6),(1,4,5),(1,4,6),(3,4,6),(3,4,17),(1,5,6),(2,1,15),(1,3,24),(3,3,24),(0,4,15),(3,4,15),(1,4,24),(3,4,24),(1,5,32),(0,15,32),(2,15,32),(3,6,15),(2,0,31),(2,1,31),(1,2,31),(1,4,46),(3,2,32),(1,4,44),(2,0,33),(2,1,33),(1,2,33),(1,5,33),(0,1,56),(2,15,33),(0,1,58),(2,1,58),(0,0,40),(2,1,40),(1,6,40),(3,4,63),(0,1,50),(3,5,50),(0,0,21),(2,0,21),(0,1,21),(0,0,69),(0,3,21),(3,3,21),(3,6,72),(3,5,21),(1,6,74),(3,6,74),(3,6,21),(2,1,21),(0,0,26),(0,1,26),(3,2,26),(3,5,26),(1,3,77),(1,5,77),(3,6,26),(1,2,85),(3,2,85),(0,21,28),(3,2,30),(0,21,30),(3,4,30),(2,1,70),(0,1,49),(3,6,49),(2,1,74),(0,24,26),(2,0,25),(2,1,25),(0,1,81),(2,1,82),(1,2,82),(1,6,82),(0,1,55),(2,1,55),(1,3,10),(1,4,7),(1,4,10),(2,0,11),(1,2,11),(1,4,11),(0,1,106),(3,2,110),(1,2,12),(1,3,12),(1,5,12),(3,2,115),(1,2,48),(1,2,68),(2,1,8),(1,2,8),(1,4,8),(1,5,78),(3,8,21),(0,1,121),(3,2,121),(1,3,9),(1,5,9),(1,9,10),(3,9,15),(3,12,15),(3,2,127),(1,9,13),(0,1,22),(0,15,127),(1,2,47),(3,9,22),(3,9,28),(1,2,99),(3,10,26),(1,2,108),(1,3,67),(3,11,21),(1,2,53),(1,5,14),(2,15,53),(3,12,22),(3,12,28),(1,16,31),(1,2,79)]
def h0W : BT Decor := buildWiresBT 8 h0Base h0Steps
def h0AutoList : List (List (Nat × Nat)) := [[],[(4,5)]]
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
def h0SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,9),some (subcubeFast 0 2,9),some (subcubeFast 0 4,6),some (subcubeFast 0 8,8),some (subcubeFast 0 16,7),some (subcubeFast 0 18,5),some (subcubeFast 0 32,7),some (subcubeFast 0 34,5),some (subcubeFast 0 48,5),some (subcubeFast 1 0,7),some (subcubeFast 1 2,6),some (subcubeFast 2 0,6),some (subcubeFast 2 1,5),some (subcubeFast 4 0,9),some (subcubeFast 4 1,6),some (subcubeFast 4 2,5),some (subcubeFast 4 8,6),some (subcubeFast 4 16,5),some (subcubeFast 4 18,4),some (subcubeFast 4 32,5),some (subcubeFast 4 34,4),some (subcubeFast 4 48,4),some (subcubeFast 8 0,9),some (subcubeFast 8 1,6),some (subcubeFast 8 2,6),some (subcubeFast 8 4,5),some (subcubeFast 8 16,5),some (subcubeFast 8 32,5),some (subcubeFast 8 48,4),some (subcubeFast 16 0,9),some (subcubeFast 16 1,5),some (subcubeFast 16 2,5),some (subcubeFast 16 4,5),some (subcubeFast 18 0,5),some (subcubeFast 18 1,4),some (subcubeFast 24 0,5),some (subcubeFast 24 4,4),some (subcubeFast 32 0,9),some (subcubeFast 32 1,5),some (subcubeFast 32 2,5),some (subcubeFast 32 4,5),some (subcubeFast 32 8,5),some (subcubeFast 32 16,4),some (subcubeFast 34 0,5),some (subcubeFast 34 1,4),some (subcubeFast 40 0,5),some (subcubeFast 40 4,4),some (subcubeFast 48 0,7),some (subcubeFast 48 1,4),some (subcubeFast 48 2,4),some (subcubeFast 48 4,4)]
def h0Slices : BT (Option (Nat × Nat)) := btOfList 6 h0SliceList
def h0Specs : List PoolSpec := [(0,[]),(1,[]),(13,[(0,0,1)]),(0,[(1,2,3)]),(1,[(1,2,3)]),(9,[]),(3,[(0,0,1)]),(0,[(1,2,3),(0,1,15)]),(11,[]),(13,[(0,0,1),(0,1,15)]),(2,[]),(22,[(0,0,1),(0,1,15)]),(3,[]),(29,[(0,0,1),(1,2,3),(0,1,15)]),(33,[]),(37,[(0,0,1),(1,2,3),(0,1,15)]),(29,[(1,2,3),(0,1,15)]),(9,[(1,2,3),(0,1,15)]),(37,[(1,2,3),(0,1,15)]),(22,[(0,0,1)]),(13,[]),(0,[(1,2,3),(1,2,6)]),(3,[(0,0,1),(1,2,6)]),(1,[(1,2,3),(1,2,6)]),(22,[(0,0,1),(1,2,6)]),(22,[]),(29,[(1,2,3),(0,0,1),(1,2,6)]),(32,[]),(37,[(1,2,3),(0,0,1),(1,2,6)]),(3,[(0,0,1),(1,2,6),(1,4,6)]),(22,[(0,0,1),(1,4,6)]),(9,[(1,2,3)]),(29,[(0,0,1),(1,2,3)]),(9,[(1,4,5)]),(0,[(1,4,5)]),(1,[(1,4,5)]),(13,[(1,4,5)]),(3,[(1,4,5)]),(22,[(1,4,5)]),(29,[(0,0,1),(1,2,3),(3,6,15)]),(47,[]),(4,[]),(4,[(1,2,3)]),(47,[(1,2,3)]),(47,[(0,0,1)]),(4,[(0,0,1)]),(37,[(0,0,1),(1,2,3)]),(29,[(1,2,3)]),(0,[(1,2,3),(1,4,6)]),(0,[(1,4,6)]),(3,[(0,0,1),(1,4,6)]),(1,[(1,2,3),(1,4,6)]),(1,[(1,4,6)]),(13,[(0,0,1),(1,4,6)]),(29,[(1,2,3),(0,0,1)]),(37,[(1,2,3),(0,0,1),(1,4,6)]),(29,[(0,0,1)]),(37,[(0,0,1),(1,4,6)]),(8,[]),(37,[(1,2,3)]),(6,[(1,2,3)]),(29,[(1,2,3),(0,0,1),(0,15,32)]),(29,[]),(30,[]),(0,[(3,4,6)]),(3,[(0,0,1),(3,4,6)]),(1,[(3,4,6)]),(10,[(1,2,3)]),(13,[(0,0,1),(3,4,6)]),(22,[(0,0,1),(3,4,6)]),(37,[(0,0,1),(3,4,6)]),(0,[(3,4,6),(1,5,33)]),(3,[(0,0,1),(3,4,6),(1,5,33)]),(1,[(3,4,6),(1,5,33)]),(13,[(0,0,1),(3,4,6),(1,5,33)]),(22,[(0,0,1),(3,4,6),(1,5,33)]),(29,[(1,2,3),(0,0,1),(1,5,33)]),(29,[(0,0,1),(1,5,33)]),(43,[]),(6,[]),(29,[(1,2,3),(0,0,1),(2,15,33)]),(22,[(0,0,1),(3,4,6),(2,15,33)]),(37,[]),(17,[]),(0,[(1,2,3),(3,4,15)]),(1,[(1,2,3),(3,4,15)]),(13,[(0,0,1),(3,4,15)]),(13,[(3,4,15)]),(22,[(0,0,1),(3,4,15)]),(22,[(3,4,15)]),(37,[(0,0,1),(1,2,3),(3,4,15)]),(9,[(1,2,3),(3,4,15)]),(37,[(1,2,3),(3,4,15)]),(37,[(0,0,1)]),(6,[(0,0,1)]),(29,[(0,0,1),(1,2,3),(1,6,40)]),(5,[]),(3,[(0,0,17)]),(1,[(1,2,3),(0,0,17)]),(13,[(0,1,15),(0,0,17)]),(22,[(0,1,15),(0,0,17)]),(29,[(1,2,3),(0,1,15),(0,0,17)]),(37,[(1,2,3),(0,1,15),(0,0,17)]),(0,[(1,2,3),(3,6,15)]),(1,[(1,2,3),(3,6,15)]),(13,[(0,0,1),(3,6,15)]),(22,[(0,0,1),(3,6,15)]),(37,[(0,0,1),(1,2,3),(3,6,15)]),(29,[(1,2,3),(0,0,1),(2,15,32)]),(0,[(1,2,4)]),(1,[(1,2,4)]),(0,[(1,2,4),(0,1,21)]),(13,[(0,0,1),(0,1,21)]),(22,[(0,0,1),(1,2,4),(0,1,21)]),(29,[(0,0,1),(0,1,21)]),(37,[(0,0,1),(1,2,4),(0,1,21)]),(22,[(1,2,4),(0,1,21)]),(9,[(1,2,4),(0,1,21)]),(0,[(1,2,4),(3,3,21)]),(25,[]),(6,[(1,2,4),(0,1,21)]),(0,[(1,2,4),(3,5,21)]),(40,[]),(22,[(0,0,1),(1,2,4)]),(0,[(1,2,4),(1,3,4)]),(1,[(1,2,4),(1,3,4)]),(13,[(0,0,1),(1,3,4)]),(13,[(1,3,4)]),(2,[(1,3,4)]),(3,[(0,0,1),(1,2,4)]),(22,[(1,2,4)]),(3,[(1,2,4)]),(37,[(1,2,4),(1,3,4)]),(20,[]),(13,[(1,3,4),(0,0,1),(3,6,21)]),(22,[(0,0,1),(1,2,4),(3,6,21)]),(29,[(0,0,1),(3,6,21)]),(36,[]),(1,[(1,3,5)]),(4,[(1,3,5)]),(29,[(1,3,5)]),(6,[(1,2,4)]),(37,[(1,2,4)]),(9,[(1,3,5)]),(45,[]),(9,[(1,2,4)]),(46,[]),(29,[(1,3,5),(0,21,28)]),(37,[(1,2,4),(0,21,28)]),(37,[(0,0,1),(1,2,4)]),(1,[(1,3,6)]),(22,[(1,2,4),(0,0,1)]),(13,[(0,0,1),(1,3,6)]),(29,[(0,0,1),(1,3,6)]),(0,[(1,3,6)]),(23,[]),(29,[(0,0,1),(1,3,6),(0,21,30)]),(1,[(1,2,4),(3,3,21)]),(29,[(3,3,21)]),(13,[(3,3,21)]),(3,[(0,0,1),(1,2,4),(3,6,21)]),(0,[(1,2,4),(1,4,5)]),(1,[(1,2,4),(1,4,5)]),(11,[(1,4,5)]),(13,[(0,0,1),(1,4,5)]),(2,[(1,4,5)]),(22,[(1,2,4),(1,4,5)]),(3,[(1,2,4),(1,4,5)]),(0,[(1,2,4),(1,4,6)]),(1,[(1,2,4),(1,4,6)]),(22,[(1,2,4),(0,0,1),(1,4,6)]),(37,[(1,2,4),(0,0,1),(1,4,6)]),(1,[(1,5,6)]),(29,[(0,0,1),(1,5,6)]),(37,[(1,2,4),(0,0,1)]),(38,[]),(0,[(1,4,5),(1,2,31)]),(1,[(1,4,5),(1,2,31)]),(22,[(1,4,5),(1,2,31)]),(3,[(1,4,5),(1,2,31)]),(29,[(1,2,31)]),(37,[(1,2,31)]),(1,[(1,2,4),(3,5,21)]),(13,[(0,0,1),(3,5,21)]),(13,[(3,5,21)]),(22,[(0,0,1),(1,2,4),(3,5,21)]),(22,[(1,2,4),(3,5,21)]),(3,[(1,2,4),(3,5,21)]),(29,[(0,0,1),(3,5,21)]),(29,[(3,5,21)]),(7,[]),(1,[(1,2,4),(0,0,69)]),(10,[(1,2,4)]),(13,[(0,1,21),(0,0,69)]),(29,[(0,1,21),(0,0,69)]),(4,[(0,0,69)]),(22,[(1,2,4),(0,1,21),(0,0,69)]),(37,[(1,2,4),(0,1,21),(0,0,69)]),(0,[(1,2,4),(3,6,21)]),(0,[(1,2,6),(1,4,24)]),(1,[(1,2,6),(1,4,24)]),(13,[(0,0,1),(1,4,24)]),(29,[(0,0,1),(1,2,6)]),(22,[(0,0,1),(1,2,6),(1,4,24)]),(9,[(1,4,24)]),(37,[(0,0,1),(1,2,6),(1,4,24)]),(1,[(1,2,4),(3,6,21)]),(13,[(0,0,1),(3,6,21)]),(37,[(0,0,1),(1,2,4),(3,6,21)]),(23,[(1,2,4),(3,6,21)]),(22,[(0,0,1),(1,2,4),(3,6,72)]),(37,[(0,0,1),(1,2,4),(3,6,74)]),(0,[(1,2,6)]),(1,[(1,2,6)]),(37,[(0,0,1),(1,2,6)]),(50,[]),(9,[(1,3,4)]),(18,[]),(29,[(0,0,1),(1,2,6),(0,24,26)]),(14,[]),(16,[]),(0,[(1,2,6),(1,3,6)]),(1,[(1,2,6),(1,3,6)]),(37,[(0,0,1),(1,3,6)]),(13,[(0,0,1),(1,3,24)]),(9,[(1,3,24)]),(13,[(0,0,1),(3,3,24)]),(9,[(3,3,24)]),(47,[(0,0,1),(1,2,6)]),(0,[(1,2,6),(1,4,6)]),(1,[(1,2,6),(1,4,6)]),(37,[(0,0,1),(1,2,6),(1,4,6)]),(0,[(1,2,6),(3,4,24)]),(1,[(1,2,6),(3,4,24)]),(13,[(0,0,1),(3,4,24)]),(22,[(0,0,1),(1,2,6),(3,4,24)]),(9,[(3,4,24)]),(37,[(0,0,1),(1,2,6),(3,4,24)]),(0,[(3,2,6)]),(1,[(3,2,6)]),(10,[]),(22,[(0,0,1),(3,2,6)]),(29,[(0,0,1),(3,2,6)]),(37,[(0,0,1),(3,2,6)]),(0,[(1,3,4)]),(1,[(1,3,4)]),(37,[(0,0,1),(1,3,4)]),(0,[(1,3,4),(3,2,26)]),(1,[(1,3,4),(3,2,26)]),(22,[(0,0,1),(3,2,26)]),(29,[(0,0,1),(3,2,26)]),(22,[(3,2,26)]),(29,[(3,2,26)]),(37,[(1,3,4),(3,2,26)]),(16,[(0,0,1)]),(0,[(1,3,4),(1,4,6)]),(1,[(1,3,4),(1,4,6)]),(13,[(1,3,4),(0,0,1),(1,4,6)]),(37,[(1,3,4),(0,0,1),(1,4,6)]),(37,[(1,3,4)]),(37,[(1,3,4),(0,0,1)]),(3,[(0,0,1),(1,5,6)]),(0,[(1,3,4),(3,5,26)]),(1,[(1,3,4),(3,5,26)]),(22,[(0,0,1),(3,5,26)]),(29,[(0,0,1),(3,5,26)]),(13,[(0,0,1),(1,3,4),(3,5,26)]),(13,[(1,3,4),(3,5,26)]),(22,[(3,5,26)]),(29,[(3,5,26)]),(41,[]),(35,[]),(0,[(1,3,4),(3,6,26)]),(1,[(1,3,4),(3,6,26)]),(13,[(0,0,1),(1,3,4),(3,6,26)]),(22,[(0,0,1),(3,6,26)]),(29,[(0,0,1),(3,6,26)]),(37,[(0,0,1),(1,3,4),(3,6,26)]),(0,[(1,3,6),(3,2,30)]),(1,[(1,3,6),(3,2,30)]),(22,[(0,0,1),(3,2,30)]),(9,[(3,2,30)]),(29,[(0,0,1),(1,3,6),(3,2,30)]),(37,[(0,0,1),(1,3,6),(3,2,30)]),(22,[(0,0,1),(1,4,5)]),(29,[(0,0,1),(1,3,6),(1,5,32)]),(29,[(0,0,1),(1,5,32)]),(47,[(0,0,1),(1,3,6)]),(0,[(1,3,6),(1,4,6)]),(1,[(1,3,6),(1,4,6)]),(37,[(0,0,1),(1,3,6),(1,4,6)]),(0,[(1,3,6),(3,4,30)]),(1,[(1,3,6),(3,4,30)]),(22,[(0,0,1),(3,4,30)]),(13,[(0,0,1),(1,3,6),(3,4,30)]),(9,[(3,4,30)]),(37,[(0,0,1),(1,3,6),(3,4,30)]),(0,[(1,4,6),(1,5,32)]),(1,[(1,4,6),(1,5,32)]),(13,[(0,0,1),(1,4,6),(1,5,32)]),(9,[(1,5,32)]),(22,[(0,0,1),(1,4,6),(1,5,32)]),(0,[(1,4,6),(3,2,32)]),(1,[(1,4,6),(3,2,32)]),(29,[(0,0,1),(3,2,32)]),(22,[(0,0,1),(1,4,6),(3,2,32)]),(37,[(0,0,1),(1,4,6),(3,2,32)]),(0,[(3,4,6),(1,2,33)]),(1,[(3,4,6),(1,2,33)]),(29,[(0,0,1),(1,2,33)]),(22,[(0,0,1),(3,4,6),(1,2,33)]),(37,[(0,0,1),(3,4,6),(1,2,33)]),(1,[(2,0,2)]),(0,[(2,1,2)]),(22,[(2,0,2),(2,1,2)]),(29,[(2,0,2),(2,1,2)]),(37,[(2,0,2),(2,1,2)]),(9,[(2,1,2)]),(22,[(2,0,2)]),(0,[(2,1,3)]),(13,[(2,1,3)]),(3,[(2,0,2)]),(29,[(2,0,2),(2,1,3)]),(14,[(1,4,5)]),(9,[(2,1,3)]),(4,[(2,1,3)]),(47,[(2,1,3)]),(4,[(2,0,2)]),(47,[(2,0,2)]),(37,[(2,0,2),(2,1,3)]),(29,[(2,1,3)]),(0,[(2,1,3),(1,4,7)]),(3,[(2,0,2),(1,4,7)]),(0,[(1,4,7)]),(22,[(2,0,2),(1,4,7)]),(1,[(2,0,2),(1,4,7)]),(13,[(2,1,3),(1,4,7)]),(13,[(1,4,7)]),(29,[(2,0,2)]),(37,[(2,0,2),(1,4,7)]),(37,[(2,1,3)]),(6,[(2,1,3)]),(24,[]),(13,[(2,1,3),(1,4,11)]),(0,[(2,1,3),(1,4,11)]),(1,[(2,0,2),(1,4,11)]),(1,[(1,4,11)]),(22,[(2,0,2),(1,4,11)]),(22,[(1,4,11)]),(37,[(2,1,3),(1,4,11)]),(10,[(1,4,11)]),(37,[(2,0,2)]),(6,[(2,0,2)]),(0,[(2,1,4)]),(13,[(2,1,4)]),(22,[(2,0,2),(2,1,4)]),(21,[]),(37,[(2,0,2),(2,1,4)]),(22,[(2,1,4)]),(3,[(2,1,4)]),(9,[(2,1,4)]),(31,[]),(10,[(1,3,12)]),(14,[(2,1,4)]),(13,[(2,1,4),(1,4,5)]),(0,[(2,1,4),(1,4,5)]),(1,[(2,0,2),(1,4,5)]),(22,[(2,1,4),(1,4,5)]),(3,[(2,1,4),(1,4,5)]),(37,[(2,1,4)]),(6,[(2,1,4)]),(10,[(1,4,5)]),(13,[(2,1,4),(1,5,12)]),(0,[(2,1,4),(1,5,12)]),(1,[(2,0,2),(1,5,12)]),(1,[(1,5,12)]),(22,[(2,1,4),(1,5,12)]),(3,[(2,1,4),(1,5,12)]),(29,[(2,0,2),(1,5,12)]),(29,[(1,5,12)]),(10,[(1,5,12)]),(44,[]),(13,[(1,4,5),(2,1,31)]),(0,[(1,4,5),(2,1,31)]),(22,[(1,4,5),(2,1,31)]),(3,[(1,4,5),(2,1,31)]),(29,[(2,1,31)]),(37,[(2,1,31)]),(12,[]),(0,[(3,2,6),(2,1,25)]),(13,[(0,0,1),(2,1,25)]),(1,[(1,3,4),(3,2,6)]),(14,[(1,3,4)]),(22,[(0,0,1),(3,2,6),(2,1,25)]),(29,[(0,0,1),(3,2,6),(2,1,25)]),(37,[(0,0,1),(3,2,6),(2,1,25)]),(6,[(1,3,4)]),(10,[(1,3,4)]),(1,[(2,3,4),(3,2,6)]),(13,[(2,3,4)]),(0,[(2,3,4)]),(14,[(2,3,4)]),(9,[(2,3,4)]),(1,[(2,3,4)]),(37,[(2,3,4)]),(6,[(2,3,4)]),(10,[(2,3,4)]),(1,[(1,4,5),(3,2,6)]),(1,[(2,0,2),(1,3,4)]),(37,[(2,0,2),(1,3,4)]),(22,[(2,0,2),(1,4,5)]),(0,[(1,4,7),(0,1,106)]),(13,[(1,4,7),(0,1,106)]),(29,[(2,0,2),(0,1,106)]),(22,[(2,0,2),(1,4,7),(0,1,106)]),(37,[(2,0,2),(1,4,7),(0,1,106)]),(13,[(2,0,21)]),(1,[(1,2,4),(2,0,21)]),(22,[(1,2,4),(2,0,21)]),(29,[(2,0,21)]),(37,[(1,2,4),(2,0,21)]),(0,[(1,2,4),(1,2,68)]),(1,[(1,2,4),(2,0,21),(1,2,68)]),(13,[(2,0,3)]),(1,[(2,0,3)]),(22,[(2,1,2)]),(3,[(2,1,2)]),(29,[(2,0,3),(2,1,2)]),(29,[(2,0,3)]),(4,[(2,0,3)]),(37,[(2,0,3)]),(6,[(2,0,3)]),(23,[(1,4,5)]),(4,[(2,1,2)]),(47,[(2,1,2)]),(47,[(2,0,3)]),(37,[(2,0,3),(2,1,2)]),(29,[(2,1,2)]),(22,[(2,1,2),(1,4,10)]),(0,[(2,1,2),(1,4,10)]),(1,[(2,0,3),(1,4,10)]),(3,[(2,1,2),(1,4,10)]),(1,[(1,4,10)]),(13,[(2,0,3),(1,4,10)]),(13,[(1,4,10)]),(37,[(2,0,3),(2,1,2),(1,4,10)]),(37,[(2,1,2),(1,4,10)]),(34,[]),(22,[(1,2,4),(2,1,21)]),(0,[(1,2,4),(2,1,21)]),(1,[(2,0,3),(1,2,4)]),(3,[(1,2,4),(2,1,21)]),(13,[(2,1,21)]),(29,[(2,0,3),(2,1,21)]),(29,[(2,1,21)]),(37,[(1,2,4),(2,1,21)]),(22,[(1,2,4),(2,1,21),(1,5,78)]),(0,[(1,2,4),(2,1,21),(1,5,78)]),(1,[(2,0,3),(1,2,4),(1,5,78)]),(3,[(1,2,4),(2,1,21),(1,5,78)]),(1,[(1,2,4),(1,5,78)]),(13,[(2,1,21),(1,5,78)]),(29,[(2,1,21),(1,5,78)]),(37,[(2,1,2)]),(15,[]),(13,[(2,0,3),(2,1,4)]),(28,[]),(37,[(2,0,3),(2,1,4)]),(0,[(2,1,4),(1,2,8)]),(0,[(1,2,8)]),(29,[(2,0,3),(1,2,8)]),(1,[(2,0,3),(1,2,8)]),(22,[(2,1,4),(1,2,8)]),(13,[(2,1,4),(2,0,3)]),(22,[(1,2,8)]),(37,[(2,0,3),(1,2,8)]),(23,[(2,1,4)]),(16,[(2,1,4)]),(22,[(2,1,4),(1,2,12)]),(0,[(2,1,4),(1,2,12)]),(1,[(2,0,3),(1,2,12)]),(3,[(2,1,4),(1,2,12)]),(1,[(1,2,12)]),(29,[(2,0,3),(1,2,12)]),(29,[(1,2,12)]),(37,[(2,1,4),(1,2,12)]),(1,[(2,0,3),(1,4,5)]),(1,[(2,0,3),(1,5,12)]),(13,[(2,0,3),(2,1,4),(1,5,12)]),(29,[(2,0,3),(1,5,12)]),(0,[(2,1,8)]),(22,[(2,1,8)]),(13,[(2,0,3),(2,1,8)]),(0,[(1,2,4),(2,1,8)]),(1,[(1,2,4),(2,0,3)]),(22,[(1,2,4),(2,1,8)]),(29,[(2,0,3),(2,1,8)]),(37,[(2,0,3),(2,1,8)]),(23,[(1,2,4)]),(0,[(1,4,5),(2,1,8)]),(1,[(1,4,5),(2,0,3)]),(22,[(1,4,5),(2,1,8)]),(47,[(2,0,3),(2,1,8)]),(37,[(2,0,3),(1,2,4)]),(13,[(2,0,3),(0,1,21)]),(29,[(2,0,3),(0,1,21)]),(3,[(1,2,4),(0,1,21)]),(13,[(0,1,21)]),(29,[(0,1,21)]),(37,[(1,2,4),(0,1,21)]),(13,[(2,0,3),(1,4,5)]),(26,[]),(1,[(2,0,3),(1,2,4),(3,5,21)]),(13,[(2,0,3),(3,5,21)]),(29,[(2,0,3),(3,5,21)]),(22,[(1,2,4),(3,8,21)]),(0,[(1,2,4),(3,8,21)]),(1,[(2,0,3),(1,2,4),(3,8,21)]),(13,[(2,0,3),(3,8,21)]),(29,[(2,0,3),(3,8,21)]),(37,[(2,0,3),(1,2,4),(3,8,21)]),(0,[(1,4,8)]),(13,[(2,0,3),(1,4,8)]),(1,[(2,0,3),(1,4,8)]),(22,[(1,4,8)]),(37,[(2,0,3),(1,4,8)]),(0,[(1,4,8),(0,1,121)]),(29,[(2,0,3),(0,1,121)]),(13,[(2,0,3),(1,4,8),(0,1,121)]),(22,[(1,4,8),(0,1,121)]),(37,[(2,0,3),(1,4,8),(0,1,121)]),(0,[(1,4,8),(3,2,121)]),(1,[(2,0,3),(1,4,8),(3,2,121)]),(22,[(1,4,8),(3,2,121)]),(29,[(2,0,3),(3,2,121)]),(37,[(2,0,3),(1,4,8),(3,2,121)]),(13,[(2,0,4)]),(1,[(2,0,4)]),(22,[(2,0,4),(2,1,2)]),(37,[(2,0,4),(2,1,2)]),(22,[(2,0,4)]),(3,[(2,0,4)]),(37,[(2,0,4)]),(0,[(2,1,2),(1,9,10)]),(1,[(2,0,4),(1,9,10)]),(13,[(2,0,4),(1,9,10)]),(22,[(2,0,4),(2,1,2),(1,9,10)]),(29,[(2,1,2),(1,9,10)]),(48,[]),(37,[(2,0,4),(2,1,2),(1,9,10)]),(0,[(3,4,6),(1,2,33),(2,1,55)]),(9,[(2,1,55)]),(13,[(0,0,1),(3,4,6),(2,1,55)]),(29,[(0,0,1),(1,2,33),(2,1,55)]),(4,[(2,1,55)]),(13,[(2,0,4),(2,1,3)]),(37,[(2,0,4),(2,1,3)]),(29,[(2,1,3),(1,2,11)]),(0,[(2,1,3),(1,2,11)]),(1,[(2,0,4),(1,2,11)]),(1,[(1,2,11)]),(22,[(2,0,4),(1,2,11)]),(22,[(1,2,11)]),(37,[(2,1,3),(1,2,11)]),(10,[(1,2,11)]),(6,[(2,0,4)]),(24,[(2,0,4)]),(16,[(2,0,4)]),(13,[(2,0,4),(2,1,4)]),(0,[(2,1,4),(1,2,3)]),(3,[(2,0,4),(2,1,4)]),(1,[(2,0,4),(1,2,3)]),(11,[(2,0,4)]),(22,[(2,0,4),(2,1,4)]),(37,[(2,0,4),(2,1,4)]),(0,[(2,1,4),(1,2,3),(3,12,15)]),(29,[(1,2,3),(3,12,15)]),(1,[(2,0,4),(1,2,3),(3,12,15)]),(0,[(2,1,4),(1,5,9)]),(1,[(2,0,4),(1,5,9)]),(29,[(1,5,9)]),(13,[(2,1,4),(2,0,4),(1,5,9)]),(22,[(2,1,4),(2,0,4),(1,5,9)]),(37,[(2,1,4),(2,0,4)]),(0,[(2,1,5)]),(29,[(2,1,5)]),(9,[(2,1,5)]),(0,[(2,1,5),(3,4,6),(2,1,33)]),(29,[(2,1,5),(0,0,1),(2,1,33)]),(37,[(0,0,1),(3,4,6),(2,1,33)]),(4,[(2,1,5)]),(13,[(2,0,4),(2,1,5)]),(22,[(2,0,4),(2,1,5)]),(13,[(2,1,5)]),(22,[(2,1,5)]),(3,[(2,1,5)]),(0,[(2,1,5),(1,9,13)]),(1,[(2,0,4),(1,9,13)]),(13,[(2,0,4),(2,1,5),(1,9,13)]),(22,[(2,0,4),(2,1,5),(1,9,13)]),(29,[(2,1,5),(1,9,13)]),(37,[(2,0,4),(1,9,13)]),(39,[]),(0,[(3,4,6),(2,1,33)]),(29,[(0,0,1),(2,1,33)]),(1,[(1,2,3),(3,4,6)]),(13,[(0,0,1),(3,4,6),(2,1,33)]),(22,[(0,0,1),(3,4,6),(2,1,33)]),(1,[(1,2,3),(0,4,15),(3,4,6)]),(1,[(3,2,3),(3,4,6)]),(29,[(3,2,3)]),(0,[(3,2,3)]),(4,[(3,2,3)]),(9,[(3,2,3)]),(1,[(3,2,3)]),(37,[(3,2,3)]),(6,[(3,2,3)]),(10,[(3,2,3)]),(9,[(1,2,5)]),(1,[(1,2,5),(3,4,6)]),(29,[(1,2,5)]),(0,[(1,2,5)]),(4,[(1,2,5)]),(22,[(1,2,5)]),(3,[(1,2,5)]),(1,[(1,2,5)]),(10,[(1,2,5)]),(1,[(1,3,5),(3,4,6)]),(0,[(1,3,5)]),(13,[(1,3,5)]),(10,[(1,3,5)]),(1,[(2,3,5),(3,4,6)]),(29,[(2,3,5)]),(0,[(2,3,5)]),(4,[(2,3,5)]),(9,[(2,3,5)]),(13,[(2,3,5)]),(10,[(2,3,5)]),(1,[(2,3,5)]),(37,[(2,0,4),(1,2,3)]),(0,[(1,2,3),(1,5,9)]),(0,[(1,5,9)]),(3,[(2,0,4),(1,5,9)]),(29,[(1,2,3),(1,5,9)]),(1,[(1,2,3),(2,0,4),(1,5,9)]),(13,[(2,0,4),(1,5,9)]),(22,[(2,0,4),(1,5,9)]),(37,[(1,2,3),(2,0,4)]),(0,[(1,2,3),(1,5,9),(0,15,127)]),(29,[(1,2,3),(1,5,9),(0,15,127)]),(42,[]),(37,[(1,2,3),(2,0,4),(0,15,127)]),(22,[(2,0,4),(1,5,9),(0,15,127)]),(19,[]),(3,[(1,4,5),(2,0,31)]),(29,[(1,2,3),(2,0,31)]),(37,[(1,2,3),(2,0,31)]),(1,[(1,4,5),(2,0,31)]),(13,[(1,4,5),(2,0,31)]),(22,[(1,4,5),(2,0,31)]),(29,[(2,0,31)]),(37,[(2,0,31)]),(29,[(1,2,3),(0,0,40)]),(3,[(0,0,40)]),(1,[(1,2,3),(3,4,15),(0,0,40)]),(13,[(3,4,15),(0,0,40)]),(22,[(3,4,15),(0,0,40)]),(37,[(1,2,3),(3,4,15),(0,0,40)]),(0,[(1,2,3),(3,9,15)]),(29,[(1,2,3),(3,9,15)]),(13,[(2,0,4),(3,9,15)]),(1,[(2,0,4),(1,2,3),(3,9,15)]),(22,[(2,0,4),(3,9,15)]),(37,[(2,0,4),(1,2,3),(3,9,15)]),(1,[(1,2,3),(3,4,6),(2,15,33)]),(1,[(2,0,4),(1,2,5)]),(22,[(2,0,4),(1,2,5)]),(0,[(1,2,5),(3,9,22)]),(13,[(2,0,4),(3,9,22)]),(1,[(2,0,4),(1,2,5),(3,9,22)]),(22,[(2,0,4),(1,2,5),(3,9,22)]),(29,[(1,2,5),(3,9,22)]),(37,[(2,0,4),(3,9,22)]),(29,[(2,0,21),(1,2,68)]),(0,[(3,4,6),(1,2,33),(0,1,55)]),(9,[(0,1,55)]),(29,[(0,0,1),(1,2,33),(0,1,55)]),(4,[(0,1,55)]),(13,[(2,0,4),(1,3,5)]),(1,[(2,0,4),(1,3,5)]),(0,[(1,3,5),(3,9,28)]),(13,[(2,0,4),(1,3,5),(3,9,28)]),(1,[(2,0,4),(1,3,5),(3,9,28)]),(22,[(2,0,4),(3,9,28)]),(29,[(1,3,5),(3,9,28)]),(37,[(2,0,4),(3,9,28)]),(0,[(1,3,9)]),(29,[(1,3,9)]),(13,[(2,0,4),(1,3,9)]),(1,[(2,0,4),(1,3,9)]),(37,[(2,0,4),(1,3,9)]),(0,[(3,4,6),(1,5,33),(0,1,56)]),(9,[(0,1,56)]),(29,[(0,0,1),(1,5,33),(0,1,56)]),(27,[]),(4,[(0,1,56)]),(0,[(1,5,9),(3,2,127)]),(1,[(2,0,4),(1,5,9),(3,2,127)]),(22,[(2,0,4),(1,5,9),(3,2,127)]),(29,[(1,5,9),(3,2,127)]),(37,[(2,0,4),(3,2,127)]),(0,[(1,4,5),(1,2,47)]),(1,[(1,4,5),(2,0,31),(1,2,47)]),(22,[(1,4,5),(2,0,31),(1,2,47)]),(29,[(2,0,31),(1,2,47)]),(37,[(2,0,31),(1,2,47)]),(0,[(2,1,2),(1,2,6)]),(13,[(0,0,1),(2,0,25)]),(1,[(3,2,6),(2,0,25)]),(0,[(1,2,3),(3,2,6)]),(22,[(0,0,1),(3,2,6),(2,0,25)]),(29,[(0,0,1),(3,2,6),(2,0,25)]),(37,[(0,0,1),(3,2,6),(2,0,25)]),(23,[(3,2,6)]),(0,[(3,2,3),(3,2,6)]),(0,[(2,1,2),(1,3,4)]),(37,[(2,1,2),(1,3,4)]),(0,[(1,3,4),(3,2,26),(0,1,81)]),(13,[(1,3,4),(0,1,81)]),(22,[(3,2,26),(0,1,81)]),(29,[(3,2,26),(0,1,81)]),(37,[(1,3,4),(3,2,26),(0,1,81)]),(1,[(1,3,4),(3,10,26)]),(0,[(2,1,2),(1,3,4),(3,10,26)]),(13,[(1,3,4),(3,10,26)]),(22,[(2,1,2),(3,10,26)]),(29,[(2,1,2),(3,10,26)]),(37,[(2,1,2),(1,3,4),(3,10,26)]),(1,[(1,3,10)]),(0,[(2,1,2),(1,3,10)]),(13,[(1,3,10)]),(29,[(2,1,2),(1,3,10)]),(37,[(2,1,2),(1,3,10)]),(13,[(2,1,15)]),(0,[(1,2,3),(2,1,15)]),(13,[(0,1,15)]),(0,[(2,1,2),(1,2,3),(0,1,15)]),(22,[(2,1,15)]),(29,[(1,2,3),(2,1,15)]),(37,[(1,2,3),(2,1,15)]),(0,[(2,1,2),(1,4,5)]),(22,[(2,1,2),(1,4,5)]),(0,[(2,1,2),(1,2,4),(0,1,21)]),(0,[(2,1,2),(2,1,4),(1,2,12)]),(29,[(2,1,2),(1,5,78)]),(6,[(2,1,2)]),(1,[(2,0,11)]),(22,[(2,0,11)]),(13,[(2,1,3),(2,0,11)]),(1,[(1,2,4),(2,0,11)]),(0,[(1,2,4),(2,1,3)]),(22,[(1,2,4),(2,0,11)]),(29,[(2,1,3),(2,0,11)]),(37,[(2,1,3),(2,0,11)]),(12,[(1,4,5)]),(9,[(1,2,4),(3,5,21)]),(0,[(2,1,3),(1,2,108)]),(1,[(2,0,11),(1,2,108)]),(22,[(2,0,11),(1,2,108)]),(29,[(2,1,3),(2,0,11),(1,2,108)]),(37,[(2,1,3),(2,0,11),(1,2,108)]),(1,[(1,4,5),(2,0,11)]),(0,[(1,4,5),(2,1,3)]),(22,[(1,4,5),(2,0,11)]),(47,[(2,1,3),(2,0,11)]),(0,[(2,1,3),(1,2,4)]),(37,[(2,1,3),(1,2,4)]),(22,[(1,2,4),(0,0,21)]),(3,[(1,2,4),(0,0,21)]),(22,[(1,2,4),(0,0,21),(3,11,21)]),(1,[(1,2,4),(3,11,21)]),(24,[(1,2,4)]),(13,[(2,1,3),(1,4,5)]),(13,[(2,1,3),(3,5,21)]),(29,[(2,1,3),(3,5,21)]),(22,[(1,2,4),(3,11,21)]),(0,[(2,1,3),(1,2,4),(3,11,21)]),(13,[(2,1,3),(3,11,21)]),(29,[(2,1,3),(3,11,21)]),(37,[(2,1,3),(1,2,4),(3,11,21)]),(0,[(2,1,3),(1,4,5)]),(1,[(1,4,11),(3,2,110)]),(0,[(2,1,3),(1,4,11),(3,2,110)]),(22,[(1,4,11),(3,2,110)]),(29,[(2,1,3),(3,2,110)]),(37,[(2,1,3),(1,4,11),(3,2,110)]),(1,[(3,4,6),(2,0,33)]),(29,[(0,0,1),(2,0,33)]),(13,[(0,0,1),(3,4,6),(2,0,33)]),(0,[(0,2,3),(3,4,6)]),(9,[(0,2,3)]),(29,[(0,2,3)]),(0,[(0,2,3)]),(22,[(0,0,1),(3,4,6),(2,0,33)]),(1,[(0,2,3)]),(0,[(3,4,6),(0,2,3),(1,5,14)]),(9,[(0,2,3),(1,5,14)]),(29,[(0,2,3),(1,5,14)]),(0,[(0,2,3),(1,5,14)]),(2,[(1,5,14)]),(3,[(1,5,14)]),(1,[(0,2,3),(1,5,14)]),(37,[(0,0,1),(3,4,6),(2,0,33)]),(37,[(0,2,3)]),(6,[(0,2,3)]),(0,[(1,2,3),(3,4,6)]),(9,[(1,2,3),(0,4,15)]),(0,[(1,2,3),(0,4,15),(3,4,6)]),(0,[(1,2,3),(3,4,15),(3,4,6)]),(0,[(2,2,3),(3,4,6)]),(9,[(2,2,3)]),(29,[(2,2,3)]),(0,[(2,2,3)]),(1,[(2,2,3)]),(37,[(2,2,3)]),(6,[(2,2,3)]),(0,[(3,2,3),(3,4,6)]),(0,[(1,2,5),(3,4,6)]),(0,[(2,2,5),(3,4,6)]),(9,[(2,2,5)]),(29,[(2,2,5)]),(0,[(2,2,5)]),(22,[(2,2,5)]),(3,[(2,2,5)]),(1,[(2,2,5)]),(0,[(3,4,6),(1,2,53)]),(1,[(3,4,6),(2,0,33),(1,2,53)]),(29,[(0,0,1),(2,0,33),(1,2,53)]),(4,[(1,2,53)]),(0,[(1,3,5),(3,4,6)]),(0,[(2,3,5),(3,4,6)]),(37,[(2,1,4),(1,2,3)]),(1,[(1,2,3),(1,4,5)]),(0,[(1,2,3),(2,1,4),(1,5,12)]),(1,[(1,2,3),(1,5,12)]),(29,[(1,2,3),(1,5,12)]),(37,[(1,2,3),(2,1,4)]),(29,[(1,2,3),(2,1,31)]),(37,[(1,2,3),(2,1,31)]),(49,[]),(3,[(3,4,17)]),(0,[(1,2,3),(0,1,15),(3,4,17)]),(1,[(1,2,3),(3,4,17)]),(13,[(0,1,15),(3,4,17)]),(22,[(0,1,15),(3,4,17)]),(37,[(1,2,3),(0,1,15),(3,4,17)]),(1,[(1,2,3),(3,12,15)]),(13,[(2,1,4),(3,12,15)]),(22,[(2,1,4),(3,12,15)]),(37,[(2,1,4),(1,2,3),(3,12,15)]),(0,[(2,1,4),(1,2,5)]),(22,[(2,1,4),(1,2,5)]),(13,[(2,1,4),(0,1,22)]),(0,[(2,1,4),(1,2,5),(0,1,22)]),(22,[(2,1,4),(1,2,5),(0,1,22)]),(29,[(1,2,5),(0,1,22)]),(37,[(2,1,4),(0,1,22)]),(4,[(1,2,5),(0,1,22)]),(22,[(1,2,5),(0,1,22)]),(13,[(2,1,4),(1,4,5),(0,1,22)]),(1,[(1,4,5),(1,2,5)]),(1,[(1,2,5),(1,4,5)]),(0,[(2,1,4),(1,2,5),(1,4,5)]),(22,[(2,1,4),(1,2,5),(1,4,5)]),(1,[(1,4,5),(1,2,5),(3,12,22)]),(13,[(1,4,5),(2,1,4),(3,12,22)]),(26,[(1,2,5)]),(1,[(1,2,5),(3,12,22)]),(0,[(2,1,4),(1,2,5),(3,12,22)]),(13,[(2,1,4),(3,12,22)]),(22,[(2,1,4),(1,2,5),(3,12,22)]),(29,[(1,2,5),(3,12,22)]),(37,[(2,1,4),(3,12,22)]),(1,[(1,4,5),(1,2,12)]),(0,[(1,4,5),(2,1,4),(1,2,12)]),(13,[(1,4,5),(2,1,4)]),(22,[(1,4,5),(2,1,4),(1,2,12)]),(25,[(1,4,5)]),(0,[(2,1,4),(1,3,5)]),(13,[(2,1,4),(1,3,5)]),(1,[(1,3,5),(3,12,28)]),(0,[(2,1,4),(1,3,5),(3,12,28)]),(13,[(2,1,4),(1,3,5),(3,12,28)]),(22,[(2,1,4),(3,12,28)]),(29,[(1,3,5),(3,12,28)]),(37,[(2,1,4),(3,12,28)]),(1,[(1,3,12)]),(0,[(2,1,4),(1,3,12)]),(13,[(2,1,4),(1,3,12)]),(29,[(1,3,12)]),(37,[(2,1,4),(1,3,12)]),(1,[(1,5,12),(3,2,115)]),(0,[(2,1,4),(1,5,12),(3,2,115)]),(22,[(2,1,4),(1,5,12),(3,2,115)]),(29,[(1,5,12),(3,2,115)]),(37,[(2,1,4),(3,2,115)]),(1,[(1,4,5),(1,2,48)]),(0,[(1,4,5),(2,1,31),(1,2,48)]),(22,[(1,4,5),(2,1,31),(1,2,48)]),(29,[(2,1,31),(1,2,48)]),(37,[(2,1,31),(1,2,48)]),(13,[(0,0,15)]),(22,[(0,0,15)]),(29,[(1,2,3),(0,0,15)]),(37,[(1,2,3),(0,0,15)]),(1,[(1,2,3),(0,0,15)]),(0,[(1,2,3),(1,4,5)]),(13,[(0,0,15),(1,4,5)]),(22,[(0,0,15),(1,4,5)]),(47,[(1,2,3),(0,0,15)]),(22,[(0,1,15)]),(47,[(1,2,3),(0,1,15)]),(13,[(0,1,15),(1,4,5)]),(22,[(0,1,15),(1,4,5)]),(0,[(1,2,3),(3,4,15),(2,1,40)]),(13,[(3,4,15),(2,1,40)]),(22,[(3,4,15),(2,1,40)]),(29,[(1,2,3),(2,1,40)]),(37,[(1,2,3),(3,4,15),(2,1,40)]),(13,[(0,0,21)]),(29,[(0,0,21)]),(1,[(1,2,4),(0,0,21)]),(37,[(1,2,4),(0,0,21)]),(0,[(1,3,5),(1,2,4)]),(13,[(1,3,5),(0,0,21)]),(29,[(1,3,5),(0,0,21)]),(13,[(0,0,21),(0,1,21)]),(22,[(1,2,4),(0,0,21),(0,1,21)]),(29,[(0,0,21),(0,1,21)]),(0,[(1,2,4),(0,1,21),(2,1,70)]),(13,[(0,1,21),(0,0,69),(2,1,70)]),(29,[(0,1,21),(0,0,69),(2,1,70)]),(13,[(0,0,21),(3,3,21)]),(29,[(0,0,21),(3,3,21)]),(37,[(1,2,4),(3,3,21)]),(0,[(1,2,4),(1,3,67)]),(13,[(0,0,21),(3,5,21)]),(22,[(1,2,4),(0,0,21),(3,5,21)]),(29,[(0,0,21),(3,5,21)]),(1,[(1,2,4),(0,0,21),(3,5,21)]),(1,[(1,3,5),(1,2,4)]),(13,[(1,3,5),(0,1,21)]),(29,[(1,3,5),(0,1,21)]),(1,[(1,4,5),(1,2,4)]),(0,[(1,4,5),(1,2,4),(0,1,21)]),(13,[(1,4,5),(0,1,21)]),(22,[(1,4,5),(1,2,4),(0,1,21)]),(13,[(0,1,21),(3,3,21)]),(29,[(0,1,21),(3,3,21)]),(13,[(0,1,21),(3,5,21)]),(22,[(1,2,4),(0,1,21),(3,5,21)]),(29,[(0,1,21),(3,5,21)]),(0,[(1,2,4),(1,3,4),(3,5,26)]),(1,[(1,2,4),(1,3,4),(3,5,26)]),(22,[(1,2,4),(3,5,26)]),(0,[(1,2,4),(1,3,5)]),(1,[(1,2,4),(1,3,5)]),(0,[(1,2,4),(1,3,5),(0,21,28)]),(1,[(1,2,4),(1,3,5),(0,21,28)]),(13,[(1,3,5),(0,21,28)]),(22,[(1,2,4),(0,21,28)]),(0,[(1,4,5),(1,2,31),(0,1,49)]),(13,[(1,4,5),(0,1,49)]),(22,[(1,4,5),(1,2,31),(0,1,49)]),(29,[(1,2,31),(0,1,49)]),(37,[(1,2,31),(0,1,49)]),(0,[(1,2,4),(3,5,21),(2,1,74)]),(13,[(3,5,21),(2,1,74)]),(22,[(1,2,4),(3,5,21),(2,1,74)]),(29,[(3,5,21),(2,1,74)]),(37,[(1,2,4),(2,1,74)]),(13,[(1,3,4),(0,0,26)]),(22,[(0,0,26)]),(29,[(0,0,26)]),(1,[(1,3,4),(0,0,26)]),(37,[(1,3,4),(0,0,26)]),(0,[(1,3,4),(1,2,79)]),(1,[(1,3,4),(0,0,26),(1,2,79)]),(22,[(0,0,26),(1,2,79)]),(29,[(0,0,26),(1,2,79)]),(37,[(1,3,4),(0,0,26),(1,2,79)]),(0,[(1,3,4),(0,1,26)]),(13,[(1,3,4),(0,1,26)]),(22,[(0,1,26)]),(29,[(0,1,26)]),(37,[(1,3,4),(0,1,26)]),(1,[(1,3,4),(3,2,26),(1,2,99)]),(22,[(3,2,26),(0,1,81),(1,2,99)]),(3,[(0,1,81),(1,2,99)]),(29,[(3,2,26),(0,1,81),(1,2,99)]),(0,[(1,3,4),(3,5,26),(2,1,82)]),(13,[(1,3,4),(3,5,26),(2,1,82)]),(22,[(3,5,26),(2,1,82)]),(29,[(3,5,26),(2,1,82)]),(37,[(1,3,4),(2,1,82)]),(0,[(1,3,4),(3,5,26),(1,2,82)]),(1,[(1,3,4),(3,5,26),(1,2,82)]),(22,[(3,5,26),(1,2,82)]),(29,[(3,5,26),(1,2,82)]),(37,[(1,3,4),(1,2,82)])]
def h0Pools : BT (Option BoundPool) := buildPoolsBT 10 h0W h0R h0Slices h0Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice50 : Slice h0R h0G (subcubeFast 48 4) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h1Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice49 : Slice h0R h0G (subcubeFast 48 2) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h2Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice48 : Slice h0R h0G (subcubeFast 48 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h3Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice47 : Slice h0R h0G (subcubeFast 48 0) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h4Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice46 : Slice h0R h0G (subcubeFast 40 4) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h5Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice45 : Slice h0R h0G (subcubeFast 40 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h6Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice44 : Slice h0R h0G (subcubeFast 34 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h7Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice43 : Slice h0R h0G (subcubeFast 34 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h8Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice42 : Slice h0R h0G (subcubeFast 32 16) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h9Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice41 : Slice h0R h0G (subcubeFast 32 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h10Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice40 : Slice h0R h0G (subcubeFast 32 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h12Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice39 : Slice h0R h0G (subcubeFast 32 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h13Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice38 : Slice h0R h0G (subcubeFast 32 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h14Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice37 : Slice h0R h0G (subcubeFast 32 0) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h15Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice36 : Slice h0R h0G (subcubeFast 24 4) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h16Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice35 : Slice h0R h0G (subcubeFast 24 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h17Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice34 : Slice h0R h0G (subcubeFast 18 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h18Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice33 : Slice h0R h0G (subcubeFast 18 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h19Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice32 : Slice h0R h0G (subcubeFast 16 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h20Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice31 : Slice h0R h0G (subcubeFast 16 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h21Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice30 : Slice h0R h0G (subcubeFast 16 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h22Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice29 : Slice h0R h0G (subcubeFast 16 0) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h23Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice28 : Slice h0R h0G (subcubeFast 8 48) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h11Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice27 : Slice h0R h0G (subcubeFast 8 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h24Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice26 : Slice h0R h0G (subcubeFast 8 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h25Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice25 : Slice h0R h0G (subcubeFast 8 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h26Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice24 : Slice h0R h0G (subcubeFast 8 2) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h27Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice23 : Slice h0R h0G (subcubeFast 8 1) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h28Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice22 : Slice h0R h0G (subcubeFast 8 0) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h29Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice21 : Slice h0R h0G (subcubeFast 4 48) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h1Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice20 : Slice h0R h0G (subcubeFast 4 34) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h30Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice19 : Slice h0R h0G (subcubeFast 4 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h31Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice18 : Slice h0R h0G (subcubeFast 4 18) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h32Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice17 : Slice h0R h0G (subcubeFast 4 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h33Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice16 : Slice h0R h0G (subcubeFast 4 8) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h34Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice15 : Slice h0R h0G (subcubeFast 4 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h35Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice14 : Slice h0R h0G (subcubeFast 4 1) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h36Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice13 : Slice h0R h0G (subcubeFast 4 0) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h37Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice12 : Slice h0R h0G (subcubeFast 2 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h38Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice11 : Slice h0R h0G (subcubeFast 2 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h39Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice10 : Slice h0R h0G (subcubeFast 1 2) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h40Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice9 : Slice h0R h0G (subcubeFast 1 0) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h41Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice8 : Slice h0R h0G (subcubeFast 0 48) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h42Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice7 : Slice h0R h0G (subcubeFast 0 34) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h43Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice6 : Slice h0R h0G (subcubeFast 0 32) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h44Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice5 : Slice h0R h0G (subcubeFast 0 18) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h45Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice4 : Slice h0R h0G (subcubeFast 0 16) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h46Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice3 : Slice h0R h0G (subcubeFast 0 8) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h47Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice2 : Slice h0R h0G (subcubeFast 0 4) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h48Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice1 : Slice h0R h0G (subcubeFast 0 2) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h49Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice0 : Slice h0R h0G (subcubeFast 0 1) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h50Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h0R h0G p.1 p.2) h0Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h0R h0G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h0Slice0) (forall_cons (fun _ h => by cases h; exact h0Slice1) (forall_cons (fun _ h => by cases h; exact h0Slice2) (forall_cons (fun _ h => by cases h; exact h0Slice3) (forall_cons (fun _ h => by cases h; exact h0Slice4) (forall_cons (fun _ h => by cases h; exact h0Slice5) (forall_cons (fun _ h => by cases h; exact h0Slice6) (forall_cons (fun _ h => by cases h; exact h0Slice7) (forall_cons (fun _ h => by cases h; exact h0Slice8) (forall_cons (fun _ h => by cases h; exact h0Slice9) (forall_cons (fun _ h => by cases h; exact h0Slice10) (forall_cons (fun _ h => by cases h; exact h0Slice11) (forall_cons (fun _ h => by cases h; exact h0Slice12) (forall_cons (fun _ h => by cases h; exact h0Slice13) (forall_cons (fun _ h => by cases h; exact h0Slice14) (forall_cons (fun _ h => by cases h; exact h0Slice15) (forall_cons (fun _ h => by cases h; exact h0Slice16) (forall_cons (fun _ h => by cases h; exact h0Slice17) (forall_cons (fun _ h => by cases h; exact h0Slice18) (forall_cons (fun _ h => by cases h; exact h0Slice19) (forall_cons (fun _ h => by cases h; exact h0Slice20) (forall_cons (fun _ h => by cases h; exact h0Slice21) (forall_cons (fun _ h => by cases h; exact h0Slice22) (forall_cons (fun _ h => by cases h; exact h0Slice23) (forall_cons (fun _ h => by cases h; exact h0Slice24) (forall_cons (fun _ h => by cases h; exact h0Slice25) (forall_cons (fun _ h => by cases h; exact h0Slice26) (forall_cons (fun _ h => by cases h; exact h0Slice27) (forall_cons (fun _ h => by cases h; exact h0Slice28) (forall_cons (fun _ h => by cases h; exact h0Slice29) (forall_cons (fun _ h => by cases h; exact h0Slice30) (forall_cons (fun _ h => by cases h; exact h0Slice31) (forall_cons (fun _ h => by cases h; exact h0Slice32) (forall_cons (fun _ h => by cases h; exact h0Slice33) (forall_cons (fun _ h => by cases h; exact h0Slice34) (forall_cons (fun _ h => by cases h; exact h0Slice35) (forall_cons (fun _ h => by cases h; exact h0Slice36) (forall_cons (fun _ h => by cases h; exact h0Slice37) (forall_cons (fun _ h => by cases h; exact h0Slice38) (forall_cons (fun _ h => by cases h; exact h0Slice39) (forall_cons (fun _ h => by cases h; exact h0Slice40) (forall_cons (fun _ h => by cases h; exact h0Slice41) (forall_cons (fun _ h => by cases h; exact h0Slice42) (forall_cons (fun _ h => by cases h; exact h0Slice43) (forall_cons (fun _ h => by cases h; exact h0Slice44) (forall_cons (fun _ h => by cases h; exact h0Slice45) (forall_cons (fun _ h => by cases h; exact h0Slice46) (forall_cons (fun _ h => by cases h; exact h0Slice47) (forall_cons (fun _ h => by cases h; exact h0Slice48) (forall_cons (fun _ h => by cases h; exact h0Slice49) (forall_cons (fun _ h => by cases h; exact h0Slice50) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))))))))))))))))))))))))))))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h0R h0G c) h0Pools := buildPoolsBT_sound h0SlicesOk
def h0Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G (6 - 1) xs.toFinset) h0Empty := trivial
def h0Block6_0 : List NodeSpec := nodesWithIdentity [([0,2,3,4,5,46,65],[41]),([0,1,2,3,4,46,66],[]),([0,1,2,3,5,32,90],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test6_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Empty 6 h0Block6_0 = true := by decide +kernel
def h0Nodes6 : List NodeSpec := h0Block6_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Check6 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Empty 6 h0Nodes6 = true := h0Test6_0
def h0Bucket6 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 6 xs.toFinset) h0Bucket6 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0EmptyOk h0Check6
def h0Block7_0 : List NodeSpec := nodesWithIdentity [([0,1,3,4,5,15,24,32],[14,22,24,29,30]),([0,1,2,3,4,5,31,46],[39,40,41]),([0,1,2,3,4,5,15,44],[20,25,31,41,50,61]),([0,1,2,3,4,5,32,46],[12,41,56,62,63]),([0,1,2,3,4,15,56],[5,8,41,71,72,73,74,75,76,77,78,79]),([0,1,2,3,4,5,58],[0,1,5,8,20,25,41,62,79,80,81,82]),([0,1,2,3,4,5,15,58],[5,20,25]),([0,1,2,3,4,5,6,63],[6,41,91,95]),([0,1,2,3,5,15,52],[50,61]),([0,1,2,3,4,5,46],[0,1,20,25,41,62,79,82]),([0,1,2,3,4,5,15,46],[5,20,25]),([0,1,2,3,4,5,46,50],[31,39,41,62,103,104,107])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Block7_0 = true := by decide +kernel
def h0Block7_1 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,45,46],[41,62,108]),([0,2,3,4,5,6,69,72],[41,117,118,119]),([0,2,3,4,5,6,69,74],[41,45,114,117,120,121,122]),([0,1,2,3,5,26,77],[25,62,96,134,135,136]),([0,1,2,3,5,6,26,77],[41]),([0,1,2,3,5,6,21,85],[131]),([0,1,2,3,4,5,28,77],[12,144]),([0,1,2,3,4,5,6,88],[2,5,58,139,141,144,147,148]),([0,1,2,3,5,21,30,32],[8,41,62,131,152]),([0,1,2,3,4,5,30,41],[12,19,25,154,155]),([0,1,2,3,4,5,30,77],[12,19,25,155]),([0,1,2,3,4,5,6,90],[2,5,25,155,156])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_1 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Block7_1 = true := by decide +kernel
def h0Block7_2 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,70,72],[12,25,119,130,158,159]),([0,1,2,3,4,5,72,77],[12,14,25,130,135,158,160]),([0,1,2,3,4,5,35,77],[41,79,82,93,172,175]),([0,1,2,3,4,5,94],[0,1,12,20,25,40,41,62,79,82]),([0,1,2,3,4,5,6,94],[0,1,41]),([0,1,2,3,4,5,6,75],[79]),([0,1,2,3,4,5,70,74],[5,40,79,82,142,184]),([0,1,2,3,4,5,74,77],[5,40,79,82,142]),([0,1,2,3,4,5,77],[0,1,12,20,25,62,79,82,198]),([0,1,2,3,4,5,77,83],[12,25,135,145,198,206,209]),([0,1,2,3,4,5,73,77],[12,25,210]),([0,1,2,3,4,5,77,84],[45,79,82,136,208])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_2 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Block7_2 = true := by decide +kernel
def h0Block7_3 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,76,77],[79,82,211]),([0,1,2,3,4,5,6,96],[5,12,19,20,217,218,219]),([0,1,2,3,4,5,6,87],[220]),([0,1,2,3,4,5,30,42],[12,20,27,41,202]),([0,1,3,4,5,6,24,89],[0,2,152]),([0,1,2,3,5,6,24,64],[91,220]),([0,1,2,3,4,5,24,46],[0,2,12,20,24,25,105,212,213]),([0,1,2,3,4,5,24,77],[0,2,20,41,62,202,207,213]),([0,1,2,3,4,5,35,85],[12,79,82,93,175]),([0,1,2,3,4,5,6,102],[79]),([0,1,2,3,4,5,6,86],[0,1,5,8,10,12,20,96,274]),([0,1,2,3,4,5,32,89],[10,25,41,56,220])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_3 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Block7_3 = true := by decide +kernel
def h0Block7_4 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,30,43],[12,19,25,41,57,79,155,285,286]),([0,1,2,3,4,8,122],[8,10,41,78,79,456,457,458,459,460,461,462]),([0,1,2,3,5,21,31,119],[163,492,497]),([0,1,2,3,4,5,49,119],[8,12,41,240,424,491]),([0,1,2,3,4,5,74,119],[8,79,142,240]),([0,1,2,3,4,5,69,123],[1,8,12,110,220]),([0,1,2,3,5,12,15,129],[360]),([0,1,2,3,5,9,130],[0,42,62,63,575,576,577]),([0,1,2,3,5,9,15,130],[41]),([0,2,3,4,5,15,17,54],[12,14,66,217]),([0,1,2,3,5,15,39,54],[12,14,41,608]),([0,1,2,3,4,5,15,59],[240])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_4 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Block7_4 = true := by decide +kernel
def h0Block7_5 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,134],[0,1,5,8,20,25,41,62,82,648,649,650,651,652]),([0,1,2,3,4,5,15,60],[1,5,10,12,20,25,65,83,674]),([0,1,2,3,5,21,31,108],[41,141,142,758,763,764]),([0,1,2,3,4,5,49,108],[5,12,41,319,388,757]),([0,1,2,3,4,5,74,108],[5,79,142,388,765]),([0,1,2,3,4,5,67,142],[0,5,12,14,109,219,779,780]),([0,1,2,3,4,53,144],[20,25,79,144,798,805,806,807,808,809,810,811]),([0,1,2,3,5,15,39,53],[12,41,816,817]),([0,1,2,3,5,15,40,53],[12,91,797,818]),([0,1,2,3,4,5,15,145],[5]),([0,1,2,3,4,5,15,53],[5,12,41,64,388,797]),([0,2,3,12,31,133],[62,163,165,370,764,865,866,867,869,870])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_5 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Block7_5 = true := by decide +kernel
def h0Block7_6 : List NodeSpec := nodesWithIdentity [([0,1,2,3,31,146],[40,62,82,361,381,466,622,874,875,876]),([0,1,2,3,4,5,16,48],[3,5,8,35,41,849]),([0,1,2,3,4,5,16,148],[3,12,40]),([0,1,2,3,4,5,71,92],[0,8,25,191,240,940]),([0,1,2,3,4,5,72,92],[0,8,12,191,240]),([0,1,2,3,4,5,74,92],[0,8,79,142,240])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_6 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Block7_6 = true := by decide +kernel
def h0Nodes7 : List NodeSpec := h0Block7_0 ++ h0Block7_1 ++ h0Block7_2 ++ h0Block7_3 ++ h0Block7_4 ++ h0Block7_5 ++ h0Block7_6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Check7 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Nodes7 = true := by
  unfold h0Nodes7 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨h0Test7_0,h0Test7_1⟩,h0Test7_2⟩,h0Test7_3⟩,h0Test7_4⟩,h0Test7_5⟩,h0Test7_6⟩
def h0Bucket7 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 7 xs.toFinset) h0Bucket7 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0Bucket6Ok h0Check7
def h0Block8_0 : List NodeSpec := [([0,2,3,4,5,6,17],[0,4,6,7,8,9,10,11,12,13,14,15,16,17,18],[0]),([0,1,3,4,5,15,24],[2,5,8,10,21,22,23,24,25,26,27,28],[0]),([0,1,3,4,5,6,15,24],[2,5,8,19,20,21,22,23,24,26,28,31],[0,1]),([0,1,2,3,4,5,6,15,31],[6,14,19,27,31,32,33,34,35,36,37,38,42,43,44,45],[0]),([0,1,2,3,4,5,15,32],[3,4,5,8,10,12,14,20,25,30,31,41,42,48,49,50,51,52,53,54,55,56,57,58,59,60],[0]),([0,1,2,3,4,5,6,15,32],[5,6,8,14,19,30,31,45,47,49,50,52,53,54,56],[0]),([0,1,2,3,4,5,15,33],[5,8,10,12,20,25,31,41,42,54,56,58,59,60,64,65,66,67,68,69,70,83],[0]),([0,1,2,3,4,5,6,40],[0,1,2,5,6,8,10,12,19,27,32,41,45,47,58,84,85,86,87,88,89,90,91,92,93,94,96],[0]),([0,1,2,3,4,5,15,18],[7,20,25,31,42,47,59,60,67,97,98,99,100,101,102],[0,1]),([0,1,2,3,4,5,46],[0,1,20,25,39,41,62,79,82,103,104,105,106,107],[0,1]),([0,1,2,3,4,5,6,46],[0,1,2,6,12,19,31,39,45,56,93,94,103,104,105,106,107],[0,1]),([0,1,2,3,4,5,15,46],[3,4,5,6,20,25,31,39,42,47,59,60,103,104,105,106,107],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_0 = true := by decide +kernel
def h0Block8_1 : List NodeSpec := nodesWithIdentity [([0,2,3,4,5,6,69],[0,8,10,41,78,110,111,112,113,114,115,116,117]),([0,2,3,4,5,6,21,69],[1,10,14,41,45,58,109,110,111,112,113,114,115,116,117]),([0,1,2,3,5,6,21,26],[2,19,41,45,56,58,96,123,124,125,126,127,128,129,130,131,132,133,137]),([0,1,2,3,4,5,6,21,28],[6,45,56,78,129,131,138,139,140,141,142,143,145,146]),([0,1,2,3,4,5,6,21,30],[5,6,8,45,56,129,130,131,150,151,153]),([0,1,2,3,4,5,6,21,72],[2,6,19,41,119,123,129,131,145,157,158]),([0,1,2,3,5,6,21,31],[2,36,40,41,44,45,56,78,93,96,129,141,142,149,161,162,163,164,165,166,167]),([0,1,2,3,5,6,21,32],[2,5,8,14,45,50,53,56,57,58,62,96,129,145,168,169,170,171]),([0,1,2,3,4,5,6,21,35],[5,8,45,56,58,78,93,94,142,145,172,173,174]),([0,1,2,3,4,5,6,49],[0,1,5,6,8,10,19,36,41,44,45,79,94,96,176,177,178,179,180,181]),([0,1,2,3,4,5,6,74],[0,1,2,5,6,8,10,19,41,45,56,79,94,121,122,142,149,182,183,184,185,186,187,188,189,190]),([0,1,2,3,4,5,6,21,74],[2,41,45,56,93,122,141,142,145,149,182,189])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_1 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_1 = true := by decide +kernel
def h0Block8_2 : List NodeSpec := [([0,1,2,3,4,5,21,70],[14,20,62,96,111,130,131,141,142,145,191,192,193,194,195,196,197],[0]),([0,1,2,3,4,5,6,41],[0,1,6,14,19,45,58,93,94,96,199,200,201,202,203,204,205],[0]),([0,1,2,3,4,5,77],[0,1,12,20,25,62,79,82,135,136,198,206,207,208],[0]),([0,1,2,3,4,5,6,77],[0,1,2,6,19,41,45,56,93,94,135,136,145,198,206,207,208],[0]),([0,1,2,3,4,5,21,77],[5,20,45,62,109,110,130,131,135,136,141,142,145,198,206,207,208],[0]),([0,1,2,3,4,5,6,21,77],[2,5,14,41,45,56,109,110,145,198,207],[0]),([0,1,2,3,4,5,6,24,26],[5,6,22,45,56,126,127,137,202,216,217],[0]),([0,1,2,3,4,5,24,30],[2,5,10,12,19,20,22,24,25,133,150,152,153,154,202,212,213,214,217,219,221,222,223],[0,1]),([0,1,2,3,4,5,6,24,37],[6,19,24,202,212,213,214,224,225],[0,1]),([0,1,2,3,4,5,6,24,38],[2,6,19,22,24,226,227],[0]),([0,1,2,3,4,5,6,24,31],[5,33,36,44,45,164,202,217,228],[0]),([0,1,2,3,4,5,24,32],[2,5,10,14,20,22,24,30,41,49,50,52,53,56,57,58,62,202,212,213,214,217,219,229,230,231],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_2 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_2 = true := by decide +kernel
def h0Block8_3 : List NodeSpec := [([0,1,2,3,4,5,6,24,41],[14,45,56,201,202,204,212,213],[0]),([0,1,2,3,4,5,6,42],[0,1,2,5,6,8,19,20,41,45,56,58,62,93,94,202,219,232,233,234,235,236,237],[0]),([0,1,2,3,4,5,6,24,42],[2,45,56,202,217,234,236],[0]),([0,1,2,3,4,5,24],[0,1,5,12,25,41,62,79,82,212],[0]),([0,1,2,3,4,5,6,81],[0,1,2,5,6,8,10,12,19,41,56,58,93,94,126,127,217,220,247,248,249,250,251,252,253,254],[0]),([0,1,2,3,5,6,26,32],[5,8,14,19,30,45,50,56,57,58,62,216,217,255,256,257,258],[0]),([0,1,2,3,4,5,6,26,35],[5,6,58,78,93,94,173,216,259,260,261],[0]),([0,1,2,3,4,5,6,82],[0,1,2,5,6,8,12,19,41,56,79,94,133,190,246,259,262,263,264,265,266,267,268,269,270],[0]),([0,1,2,3,4,5,85],[0,1,6,10,20,25,62,79,82,137,271,272,273,274,275,276,277],[0]),([0,1,2,3,4,5,6,85],[0,1,2,6,12,19,56,93,94,137,216,272,273,274,275,276,277],[0]),([0,1,2,3,4,5,6,89],[0,1,2,5,6,8,10,19,20,25,45,56,93,94,152,155,278,279,280,281,282,283],[0,1]),([0,1,2,3,4,5,6,30,31],[5,6,37,38,44,45,56,93,94,153,284,287],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_3 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_3 = true := by decide +kernel
def h0Block8_4 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,30,32],[5,12,14,19,25,30,41,49,50,52,53,56,57,58,62,150,152,153,154,155,223,288,289,290]),([0,1,2,3,4,5,6,91],[0,1,2,5,6,8,19,25,41,45,56,58,62,93,94,153,155,217,291,292,293,294,295,296]),([0,1,2,3,4,5,6,43],[0,1,2,6,19,40,44,45,57,94,217,286,297,298,299,300,301]),([0,1,2,3,4,5,51],[0,1,5,8,10,12,20,25,41,53,79,82,119,302,303,304,305,306]),([0,1,2,3,4,5,55],[0,1,5,8,10,12,20,25,41,68,79,82,119,307,308,309,310,311]),([0,1,2,3,4,56],[71,73,74,75,77,79]),([0,1,2,3,4,5,7,11,31],[33,37,321,322,323,324,325,326,327,328]),([0,1,2,3,4,5,11,106],[1,5,8,10,12,25,41,58,96,319,320,324,325,331,332,333,334,335,336,337,338,339,340,341,342]),([0,1,2,3,4,5,7,110],[0,5,8,10,12,14,20,41,58,219,312,318,321,327,330,343,344,345,346,347,348,349,350,351,352]),([0,1,2,3,4,5,7,12,114],[41,318,321,355,359,360,361,362,363]),([0,1,2,3,5,7,12,31],[35,40,41,163,165,312,327,338,351,357,360,361,364,365,366,367,368,369,370,371]),([0,1,2,3,4,5,7,115],[0,5,8,10,20,41,78,79,219,312,318,321,327,338,352,357,369,372,373,374,375,376,377,378,379,380])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_4 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_4 = true := by decide +kernel
def h0Block8_5 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,7,48],[0,5,8,10,20,35,41,79,219,318,321,327,328,352,366,371,382,383,384,385,386,387,388]),([0,1,2,3,4,5,26,98],[5,8,10,12,14,25,41,62,127,133,216,217,239,240,244,245,259,389,390,391,392,393,394,395,396,397]),([0,1,2,3,4,5,27,98],[5,8,10,12,14,25,41,62,133,239,240,389,390,393,394,395,398,399,400,401,402,403,404,405,406]),([0,1,2,3,4,5,31,98],[5,8,10,14,33,34,35,36,37,38,40,41,62,79,82,215,217,239,240,323,389,390,393,394,395,407]),([0,1,2,3,4,5,111],[0,1,5,8,10,12,20,25,41,78,79,82,335,411,412,413,414,415]),([0,1,2,3,4,5,118],[0,1,5,8,12,20,25,62,79,82,416,421,422]),([0,1,2,3,4,5,8,10,31],[37,426,427,428,429,430,431,432,433,434,435]),([0,1,2,3,4,5,8,107],[0,5,8,10,12,14,25,41,58,155,423,424,427,429,430,431,437,438,439,440,441,442,443,444,445,446]),([0,1,2,3,4,5,8,78],[0,5,8,10,12,25,41,58,110,119,155,388,429,430,431,448,449,450,451,452,453,454,455]),([0,1,2,3,4,5,12,120],[1,5,8,10,12,41,62,215,220,353,354,358,359,369,370,423,468,469,470,471,472,473,474,475,476,477]),([0,1,2,3,4,5,8,113],[0,5,8,10,12,25,41,58,119,146,155,354,423,424,428,429,430,431,465,478,479,480,481,482,483,484,485]),([0,1,2,3,4,5,8,12,113],[41,359,361,423,429,465,476,481])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_5 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_5 = true := by decide +kernel
def h0Block8_6 : List NodeSpec := [([0,1,2,3,5,8,12,31],[35,40,41,146,163,215,360,361,364,365,367,368,369,370,424,428,429,430,466,467,486],[0]),([0,1,2,3,4,5,8,115],[0,5,8,12,25,41,78,79,119,155,215,369,372,373,375,376,377,379,423,424,428,429,431,467,487,488,489],[0]),([0,1,2,3,4,5,8,48],[0,5,8,12,25,35,41,79,119,155,215,382,383,384,385,386,387,388,423,429,431,435,486],[0]),([0,1,2,3,4,5,21,119],[5,8,10,12,14,20,41,62,109,110,130,131,141,142,192,240,424,490,491,492,493,494,495,496,497,498],[0]),([0,1,2,3,4,5,31,119],[5,8,12,34,35,36,37,38,40,41,62,79,82,240,371,424,432,490,491,492,496,497,499,500,501,502],[0,1]),([0,1,2,3,4,5,8,69],[0,5,8,10,12,25,41,58,110,111,116,155,381,388,423,424,428,429,430,431,450,504,505,506,507,508,509],[0]),([0,1,2,3,4,5,8,21,69],[14,41,110,116,130,131,424,429,450,498,506],[0]),([0,1,2,3,5,8,21,31],[36,40,41,131,141,142,161,162,165,166,167,381,423,428,429,430,466,503,510,511],[0]),([0,1,2,3,4,5,8,49],[0,5,10,12,25,36,41,79,119,155,176,177,178,179,180,181,388,424,429,431,435],[0]),([0,1,2,3,4,5,8,74],[0,5,10,12,25,41,79,121,122,142,155,182,184,186,187,189,388,423,424,428,429,431,503,512,513,514],[0]),([0,1,2,3,4,5,21,123],[12,14,20,62,109,110,130,131,141,142,146,429,498,515,516,517,518,519,520],[0]),([0,1,2,3,4,5,124],[0,1,5,8,10,12,20,25,41,78,79,82,523,526,527,528,529,530],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_6 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_6 = true := by decide +kernel
def h0Block8_7 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,125],[0,1,5,8,10,12,20,25,41,79,82,122,522,531,532,533,534,535]),([0,1,2,3,4,5,128],[0,1,12,20,25,62,63,79,82,543,544,545,546,547,548,549]),([0,1,2,3,4,5,104],[0,8,10,12,25,62,78,79,82,308,550,551,552,553,554]),([0,1,2,3,4,5,9,109],[0,5,8,10,12,41,62,220,320,447,536,537,540,541,542,555,557,558,559,560,561,562,563,564,565,566,567]),([0,1,2,3,5,9,12,15],[3,4,41,42,47,58,63,133,353,360,361,447,537,568,569,570,571,572,573,574]),([0,1,2,3,5,12,127],[1,41,62,133,360,370,578,579,580,581,582,583]),([0,2,3,4,5,13,54],[5,8,41,66,78,82,217,356,586,587,588,589,590]),([0,1,2,3,4,5,132],[0,1,10,12,20,25,62,63,82,356,596,597,598,599,600,601]),([0,1,2,3,4,5,15,54],[3,4,5,8,10,12,20,25,31,41,42,47,58,59,60,66,67,217,240,356,589,603,604,605,606,607]),([0,1,2,3,4,5,20,54],[5,8,10,12,20,25,41,58,66,217,220,240,356,589,603,604,606,607,609,610,611,612,613,614,615,616,617]),([0,1,2,3,4,5,22,54],[5,8,10,20,41,58,66,78,79,82,240,466,589,603,604,606,607,618,619,620,621,622,623,624,625,626]),([0,1,2,3,4,5,28,54],[5,8,12,25,41,58,66,78,79,82,138,139,140,143,240,356,589,603,604,606,607,627,628,629,630])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_7 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_7 = true := by decide +kernel
def h0Block8_8 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,29,54],[5,8,12,25,41,66,78,79,82,240,356,589,603,604,606,607,631,632,633,634,635,636,637,638]),([0,1,2,3,4,5,15,127],[3,4,5,10,12,20,25,31,41,47,60,79,133,215,447,542,579,580,640,641,642,643,644,645,646,647,653]),([0,1,2,3,4,5,15,47],[4,5,10,12,20,25,31,34,41,42,60,67,79,83,215,447,548,654,655,656,657,658,659,660,661]),([0,1,2,3,4,5,15,61],[4,20,25,27,31,42,59,60,63,67,84,662,663,664,665,666,667]),([0,1,2,3,4,5,129],[0,1,8,20,25,62,63,79,82,447,668,669,670,671,672,673]),([0,1,2,3,4,5,15,129],[3,4,5,20,25,31,47,59,60,541,668,669,670,671,672,673]),([0,1,2,3,4,5,136],[0,1,8,12,20,25,62,63,82,447,677,678,679,680,681,682]),([0,1,2,3,4,5,103],[0,1,5,8,12,20,25,41,68,78,79,82,308,684,685,686,687]),([0,1,2,3,4,5,137],[0,1,8,10,20,25,62,63,82,447,690,691,692,693,694,695]),([0,1,2,3,4,5,57],[0,1,5,8,10,12,20,25,41,62,70,73,79,133,653,701,702,703,704,705]),([0,1,2,3,4,5,131],[0,1,5,8,10,12,20,25,41,62,79,119,645,706,707,708,709,710]),([0,1,2,3,4,5,135],[0,1,5,8,10,12,20,25,41,79,240,658,711,712,713,714,715])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_8 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_8 = true := by decide +kernel
def h0Block8_9 : List NodeSpec := nodesWithIdentity [([0,1,3,4,5,10,24],[0,1,212,213,313,716]),([0,1,2,3,4,5,15,97],[1,3,4,5,8,10,12,20,25,27,31,42,47,59,60,119,122,155,238,388,717,718,719,720,721,722,723]),([0,1,2,3,4,5,20,97],[1,5,8,10,12,20,25,27,122,220,238,388,610,611,612,613,614,615,616,717,718,720,721,722,724]),([0,1,2,3,4,5,99],[0,5,8,10,25,62,79,82,248,388,727,728,729,730,731]),([0,1,2,3,4,5,139],[0,1,5,20,25,62,79,82,133,464,732,733,734,735,736,737]),([0,2,3,4,5,10,17],[0,1,4,7,313,745,746]),([0,1,2,3,4,5,69],[0,1,5,12,20,25,41,62,79,82,110,111]),([0,1,2,3,4,5,113],[0,1,5,12,20,25,41,62,79,82,479,482]),([0,1,2,3,4,122],[79,456,457,460,461,462]),([0,2,3,4,5,10,69],[0,1,110,111,313,507,752]),([0,1,3,4,5,10,113],[0,1,313,317,479,482,753]),([0,1,2,3,4,10,122],[8,10,78,119,388,434,455,456,457,460,461,462,754,755])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_9 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_9 = true := by decide +kernel
def h0Block8_10 : List NodeSpec := [([0,1,2,3,4,5,21,108],[5,8,10,12,20,41,62,109,110,130,131,141,142,145,319,388,447,756,757,758,759,760,761,762,763],[0]),([0,1,2,3,4,5,140],[0,5,8,10,12,27,41,62,79,82,758,766,767,768,769,770],[0]),([0,1,2,3,4,5,31,108],[5,8,12,27,33,34,35,36,37,38,40,41,62,79,82,319,388,756,757,758,762,763,771,772,773,774],[0,1]),([0,1,2,3,4,5,11,21,67],[14,41,109,110,131,145,319,324,775,777,778,781],[0]),([0,1,2,3,5,11,21,31],[36,40,41,96,131,141,142,161,162,163,165,166,167,320,325,330,340,776,782],[0]),([0,1,2,3,4,5,11,49],[1,8,10,12,25,36,41,79,96,176,177,178,179,180,181,319,324,325,326,341,342],[0]),([0,1,2,3,4,5,11,74],[1,8,10,12,25,41,79,121,142,182,184,186,187,189,190,319,320,324,325,330,341,342,776,783,784],[0]),([0,1,2,3,4,5,21,142],[12,20,62,109,110,130,131,141,142,145,146,325,780,785,786,787,788,789],[0]),([0,1,2,3,4,5,112],[0,1,5,8,10,12,20,25,41,79,82,122,343,791,792,793,794,795],[0]),([0,1,2,3,4,5,14,53],[5,8,10,12,20,25,41,58,64,83,381,388,796,797,798,799,800,801,802,803,804,812,813,814],[0]),([0,1,2,3,4,5,15,53],[3,4,5,8,10,12,20,25,31,41,42,47,58,59,60,64,356,388,796,797,798,803,812,815],[0]),([0,1,2,3,4,5,19,53],[5,8,10,12,20,25,41,58,64,119,388,796,797,798,803,812,819,820,821,822,823,824,825],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_10 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_10 = true := by decide +kernel
def h0Block8_11 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,20,53],[5,8,10,12,20,25,41,58,64,220,356,388,610,611,612,613,614,615,616,796,797,798,803,812,826]),([0,1,2,3,4,5,22,53],[5,8,10,20,41,58,64,79,82,381,388,466,618,620,621,622,623,624,625,626,796,797,798,803,812,827]),([0,1,2,3,4,5,23,53],[5,8,10,20,41,58,64,79,82,83,388,466,796,797,798,803,812,828,829,830,831,832,833,834]),([0,1,2,3,4,5,143],[0,5,8,10,12,25,41,79,82,119,240,798,835,836,837,838]),([0,1,2,3,4,5,28,53],[5,8,12,25,41,58,64,79,82,119,138,140,143,144,356,381,388,628,629,796,797,798,803,812,839]),([0,1,2,3,4,5,29,53],[5,8,12,25,41,58,64,79,82,119,356,388,511,632,633,635,636,638,796,797,798,803,812,840]),([0,1,2,3,4,5,12,15,53],[3,4,31,41,42,353,359,360,361,388,569,797,815]),([0,1,2,3,5,12,15,31],[4,35,40,41,42,43,47,59,163,165,361,364,365,367,368,369,370,371,841,842]),([0,1,2,3,4,5,15,115],[3,4,8,10,12,20,25,31,41,42,47,60,78,79,215,369,372,373,375,376,377,379,380,843,844,845,846]),([0,1,2,3,4,5,15,48],[3,8,10,12,20,25,31,35,41,42,43,60,79,83,215,371,382,383,384,385,386,387,847,848,849]),([0,1,2,3,4,5,15,34],[3,16,20,25,27,31,42,59,60,361,850,851,852,853,854,855]),([0,1,2,3,4,5,130],[0,1,5,20,25,62,79,82,361,575,576,849,856,857,858,859])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_11 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_11 = true := by decide +kernel
def h0Block8_12 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,15,130],[3,4,20,25,31,41,42,47,59,60,359,575,576,856,857,858,859]),([0,2,3,4,5,12,133],[8,10,62,79,388,625,862,863,864,865,866,867,868]),([0,1,2,3,12,22,31],[62,82,163,165,190,361,364,369,370,466,620,622,871,872,873]),([0,1,2,3,4,5,146],[0,1,5,12,20,25,58,62,82,361,466,877,878,879,880,881,882]),([0,1,2,3,5,31,113],[41,62,82,83,146,165,484,485,883,884,885,886,887]),([0,1,2,3,4,5,147],[0,1,5,10,20,25,62,82,146,361,890,891,892,893,894,895]),([0,1,2,3,4,5,116],[0,1,5,8,10,12,20,25,41,62,79,119,372,901,902,903,904,905]),([0,1,2,3,4,5,117],[0,1,5,10,12,20,25,40,41,79,119,382,906,907,908,909,910]),([0,1,2,3,4,5,16,31],[3,5,10,12,33,34,35,36,37,38,40,41,62,79,82,371,911,912,913,914,915,916,917,918,919]),([0,1,2,3,4,5,17,31],[4,7,8,10,12,14,16,18,33,34,35,36,37,38,40,41,62,67,79,82,745,842,920,921,922,923]),([0,1,2,3,4,5,62],[0,1,5,8,10,12,20,25,41,79,82,85,388,924,925,926,927,928]),([0,1,2,3,4,5,28,67],[5,10,12,25,41,79,82,109,138,140,143,144,146,447,628,629,630,777,778,929,930,931,932,933,934,935])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_12 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_12 = true := by decide +kernel
def h0Block8_13 : List NodeSpec := [([0,1,2,3,4,5,67,69],[0,1,5,8,41,58,96,109,110,111,116,192,219,506,507,508,509,777,778,929,930,931,932,936,937,938],[0]),([0,1,2,3,4,5,21,92],[0,1,5,8,10,14,41,78,96,109,110,130,131,141,142,145,191,240,939,940,941],[0]),([0,1,2,3,4,5,67,72],[0,5,12,25,41,58,109,118,119,130,157,158,159,219,777,778,929,930,931,932,942,943,944],[0]),([0,1,2,3,4,5,21,67,141],[5,109,130,131,777,778,945],[0]),([0,1,2,3,4,5,67,74],[0,5,40,41,58,79,82,109,121,122,142,182,184,186,187,189,777,778,929,930,931,932,946,947,948,949],[0]),([0,1,2,3,4,5,28,69],[8,10,12,25,41,78,79,82,96,110,111,116,138,139,140,143,144,192,506,507,508,509,628,629,950,951,952],[0]),([0,1,2,3,5,31,69],[41,62,78,82,96,163,381,508,509,764,953,954,955,956],[0,1]),([0,1,2,3,4,5,69,72],[1,8,12,25,41,58,96,110,111,116,118,119,130,157,158,159,192,506,507,508,509,944,957,958],[0]),([0,1,2,3,4,5,69,74],[1,8,40,41,58,79,82,96,110,111,116,121,122,142,182,184,186,187,189,192,506,507,508,509,959,960,961],[0]),([0,1,2,3,5,21,82],[20,41,62,131,132,133,141,267,269,962,963,964],[0]),([0,1,2,3,4,5,88],[0,1,5,8,20,25,62,82,144,147,148,967,968,969,970],[0]),([0,1,2,3,4,5,93],[0,1,5,8,12,25,40,41,79,177,388,971,972,973,974,975],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_13 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_13 = true := by decide +kernel
def h0Block8_14 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,95],[0,1,5,8,10,12,20,25,41,62,79,182,388,976,977,978,979,980]),([0,1,2,3,4,5,149],[0,1,5,8,10,12,41,79,82,240,981,986,987,988,989,990]),([0,1,2,3,4,5,138],[0,1,5,8,10,12,41,78,79,82,96,122,388,728,996,997,998,999]),([0,1,2,3,4,5,100],[0,1,5,8,10,12,20,25,41,62,79,263,388,1000,1001,1002,1003,1004]),([0,1,2,3,4,5,101],[0,1,5,8,10,12,20,25,41,62,79,133,267,1005,1006,1007,1008,1009])]
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
def h0Block9_0 : List NodeSpec := [([0,1,2,3,4,5,6,15],[0,1,2,3,4,5,6,8,10,12,19,20,25,31,32,46,47,56,59,93],[0,1]),([0,1,2,3,4,5,6,21],[0,1,2,5,6,8,10,19,20,41,45,56,58,62,93,109,110,123,130,131,142,145,149],[0]),([0,1,2,3,4,5,24],[0,1,2,5,10,12,24,25,27,41,62,79,82,119,122,137,146,202,212,213,214,215],[0]),([0,1,2,3,4,5,6,24],[0,1,2,5,6,19,20,24,56,93,202,212,213,214],[0,1]),([0,1,2,3,4,5,25],[2,5,12,25,41,62,79,82,137,146,215,238,239,240,241,242,243],[0]),([0,1,2,3,4,5,6,26],[0,1,2,5,6,8,12,19,25,41,56,58,62,93,126,127,137,216,244,245,246,259,271],[0,1]),([0,1,2,3,4,5,6,30],[0,1,2,5,6,12,19,25,56,93,150,152,153,154,223],[0,1]),([0,1,2,3,4,5,6,31],[0,1,2,5,6,8,19,33,34,35,36,37,38,40,41,44,45,56,62,79,82,93,164,215,284],[0,1]),([0,1,2,3,4,5,32],[0,1,5,12,20,25,30,41,49,52,53,56,57,58,79,82],[0]),([0,1,2,3,4,5,6,32],[0,1,2,5,6,14,19,30,45,49,52,53,56,57,58,62,93],[0,1]),([0,1,2,3,4,5,33],[5,12,20,25,41,56,58,64,66,68,69,70,79,82,240],[0]),([0,1,3,4,5,7,10],[0,1,10,20,27,119,122,137,146,215,240,312,313,314,315,316,317],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_0 = true := by decide +kernel
def h0Block9_1 : List NodeSpec := [([0,1,2,3,4,5,7,11],[0,1,5,8,10,12,20,25,219,240,312,318,319,320,321,322,324,329,330,338,340,342,351],[0,1]),([0,1,2,3,4,5,7,12],[0,1,5,8,10,20,41,58,62,219,240,312,318,321,327,338,351,353,354,355,356,357,358,359,360,361,369,381],[0]),([0,1,2,3,4,5,98],[0,1,5,8,12,14,20,25,41,62,78,79,82,219,239,240,389,390],[0,1]),([0,1,2,3,4,5,7,26],[0,5,10,12,20,25,41,58,62,127,137,216,219,220,244,245,259,312,318,321,338,351,356,392,397,408,409],[0]),([0,1,2,3,4,5,7,31],[0,5,10,20,33,34,35,36,37,38,40,41,62,79,82,215,219,312,318,321,323,327,328,338,351,366,371,410],[0,1]),([0,1,2,3,4,5,106],[0,1,5,12,20,25,41,58,79,82,333,334,335,337,338,339],[0]),([0,1,2,3,4,5,68],[1,5,12,25,41,58,79,82,109,240,416,417,418,419,420],[0]),([0,1,2,3,4,5,8,10],[0,1,5,8,10,12,20,25,133,155,217,240,313,381,388,423,424,425,426,427,428,430,436,437,447,463,464],[0,1]),([0,1,2,3,4,5,8,12],[0,1,5,8,12,25,41,58,62,155,240,353,354,358,359,361,369,381,423,424,428,429,430,465,466,467],[0]),([0,1,2,3,4,5,119],[0,1,8,12,20,25,41,62,79,82,155,240,424,490,491,492,496,497],[0,1]),([0,1,2,3,4,5,8,21],[0,5,10,12,20,25,41,58,62,109,110,130,131,142,146,155,423,424,428,429,430,450,466,503],[0]),([0,1,2,3,4,5,120],[0,1,10,12,20,25,41,62,79,82,155,215,220,423,469,470,471,474,475],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_1 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_1 = true := by decide +kernel
def h0Block9_2 : List NodeSpec := [([0,1,2,3,4,5,8,31],[0,5,12,25,34,35,36,37,38,40,41,62,79,82,155,215,423,424,428,429,430,435,486,510],[0,1]),([0,1,2,3,4,5,121],[0,1,12,20,25,41,58,79,82,217,428,521,522,523,524,525],[0]),([0,1,2,3,4,5,9,10],[0,1,5,8,10,20,41,58,62,240,313,317,356,388,425,426,437,447,463,464,536,537,538,539,540,541,542],[0]),([0,1,2,3,4,5,9,11],[0,1,5,8,12,25,41,58,62,240,319,320,324,330,340,342,447,466,536,537,540,541,542,555,556],[0]),([0,1,2,3,5,9,12],[0,1,41,58,62,353,360,537,568,573,574],[0]),([0,1,2,3,4,5,9,13],[0,1,5,8,41,58,62,79,82,240,356,447,536,537,540,541,542,565,584,585,586,591,592,593,594,595,602],[0]),([0,1,2,3,4,5,54],[0,1,5,8,12,20,25,41,62,66,78,79,82,217,240,603,604],[0]),([0,1,2,3,4,5,9,15],[0,3,4,5,10,12,20,25,31,41,47,58,59,62,63,67,356,447,536,537,540,541,542,571,639],[0]),([0,1,2,3,4,5,9,22],[0,5,10,20,41,58,62,63,79,82,447,466,536,537,540,541,542,565,618,620,621,623,624,625,626,675,676],[0]),([0,1,2,3,4,5,118],[0,1,5,10,12,20,25,41,62,79,82,83,119,122,146,240,416,421,447,683],[0]),([0,1,2,3,4,5,9,118],[0,5,20,41,58,62,63,83,240,416,421,511,536,537,540,541,542,548,683],[0]),([0,1,2,3,4,5,9,28],[0,5,12,25,41,58,62,63,79,82,138,140,143,144,146,356,447,536,537,540,541,542,628,629,630,688,689],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_2 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_2 = true := by decide +kernel
def h0Block9_3 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,9,126],[0,5,12,25,41,58,62,63,240,511,536,537,540,541,542,696,697,698,699,700]),([0,1,2,3,4,5,127],[0,1,5,12,20,25,62,79,447,542,579,580,641,645,646]),([0,1,2,3,4,5,9,127],[0,5,41,62,63,82,240,356,536,537,540,541,542,565,579,580,641,645,646]),([0,1,2,3,4,5,47],[1,5,12,20,25,34,41,79,240,657,658,659,660,661]),([0,1,2,3,4,5,10,25],[0,2,5,8,10,14,78,119,219,238,239,241,242,243,313,317,425,426,437,463]),([0,1,2,3,4,5,97],[0,1,5,12,20,25,41,62,79,82,133,217,238,240,381,447,717,718]),([0,1,2,3,4,5,10,97],[0,1,5,8,10,14,20,78,119,238,240,313,317,381,388,425,426,437,447,463,464,717,718]),([0,1,2,3,4,5,10,26],[1,8,10,12,14,20,25,41,58,62,127,133,137,217,220,240,244,245,259,313,356,425,426,437,447,463,464,725,726]),([0,1,2,3,4,5,10,105],[1,8,12,20,25,119,217,240,313,381,388,425,426,437,447,463,464,738,739,740,741,742]),([0,1,2,3,4,5,10,36],[4,8,10,12,14,25,78,240,313,342,388,425,426,437,463,743,744,747,748,749]),([0,1,2,3,4,5,10,31],[1,8,10,14,20,34,35,36,37,38,40,41,62,78,79,82,215,217,240,313,425,426,433,434,437,447,463,464,750,751]),([0,1,2,3,4,5,107],[0,1,5,12,20,25,41,58,79,82,437,438,439,442,444,446])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_3 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_3 = true := by decide +kernel
def h0Block9_4 : List NodeSpec := [([0,1,2,3,4,5,10,107],[1,8,14,20,27,41,62,133,240,313,388,425,426,433,437,438,439,442,444,446,447,463,464],[0]),([0,1,2,3,4,5,78],[0,5,12,25,41,58,79,82,110,448,449,452,454,455],[0]),([0,1,2,3,4,5,10,78],[8,10,41,62,78,110,119,240,313,388,425,426,433,434,437,448,449,452,454,455,463],[0]),([0,1,2,3,4,5,108],[0,1,5,12,20,25,41,62,79,82,319,756,757,758,762,763],[0,1]),([0,1,2,3,4,5,11,21],[1,8,10,12,20,25,41,58,62,109,110,130,131,142,146,240,319,320,325,330,340,342,466,775,776],[0]),([0,1,2,3,4,5,109],[0,1,5,10,12,20,25,41,62,79,82,215,320,342,557,558,560,562,563],[0,1]),([0,1,2,3,4,5,11,31],[1,8,12,25,34,35,36,37,38,40,41,62,79,82,215,240,319,320,325,326,330,340,342,782,790],[0,1]),([0,1,2,3,4,5,110],[0,1,5,12,20,25,41,58,79,82,330,343,344,346,348,349],[0]),([0,1,2,3,4,5,53],[0,1,5,12,20,25,41,62,64,79,82,240,381,796,797],[0]),([0,1,2,3,4,5,12,53],[0,1,5,8,41,58,62,64,78,83,240,353,354,358,359,360,361,369,388,511,796,797],[0]),([0,1,2,3,4,5,12,15],[1,3,4,8,10,12,20,25,41,42,47,58,59,62,240,353,354,356,358,359,361,369,569,841],[0]),([0,1,2,3,4,5,12,22],[1,8,10,20,41,58,62,79,82,240,353,354,358,359,361,369,370,466,620,621,622,623,624,625,860,861],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_4 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_4 = true := by decide +kernel
def h0Block9_5 : List NodeSpec := [([0,1,2,3,4,5,113],[0,1,5,10,12,20,25,41,62,79,82,83,119,146,354,356,478,479,482,484,485],[0]),([0,1,2,3,4,5,12,113],[1,20,41,58,62,83,240,353,354,358,359,361,369,478,479,482,484,485],[0]),([0,1,2,3,4,5,12,28],[1,8,12,25,41,58,62,79,82,138,139,140,144,146,240,353,354,356,358,359,361,369,628,629,888,889],[0]),([0,1,2,3,4,5,12,114],[1,12,25,41,58,62,240,353,354,358,359,361,369,511,896,897,898,899,900],[0]),([0,1,2,3,5,12,31],[1,35,40,41,62,82,364,365,367,369],[0]),([0,1,2,3,4,5,115],[0,1,5,12,20,25,41,62,79,369,372,373,375,376,379],[0]),([0,1,2,3,4,5,12,115],[1,41,58,62,78,82,240,353,354,356,358,359,361,369,370,372,373,375,376,379,381],[0]),([0,1,2,3,4,5,48],[0,5,12,20,25,35,40,41,79,382,383,384,386,387],[0]),([0,1,2,3,4,5,16],[0,1,3,5,12,20,25,41,62,79,82,240,911,912,913,914,915],[0]),([0,1,2,3,4,5,17],[0,1,4,5,7,8,12,14,16,18,20,25,41,62,78,79,82,381,388,447,745,920],[0]),([0,1,2,3,4,5,15,31],[3,4,10,12,20,25,34,35,36,37,38,40,41,42,43,47,59,62,79,82,215,842,916],[0,1]),([0,1,2,3,4,5,40],[0,1,5,12,20,25,41,47,58,79,82,84,85,87,89,92],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_5 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_5 = true := by decide +kernel
def h0Block9_6 : List NodeSpec := [([0,1,2,3,4,5,67],[0,1,5,12,20,25,62,79,82,109,240,777,929,930,931,932],[0]),([0,1,2,3,4,5,21,67],[0,5,20,41,58,62,109,110,130,131,142,145,192,777,929,930,931,932],[0]),([0,1,2,3,4,5,69],[0,1,5,8,12,20,25,41,62,79,82,96,110,111,116,381,388,507,508,509],[0,1]),([0,1,2,3,4,5,21,69],[1,14,20,41,58,62,96,109,110,111,116,130,131,142,507,508,509],[0]),([0,1,2,3,5,21,26],[20,25,41,58,62,124,125,127,130,131,132],[0]),([0,1,2,3,4,5,21,28],[10,12,20,25,41,58,62,79,82,109,110,130,131,138,139,140,142,146,220,628,629,965,966],[0]),([0,1,2,3,4,5,21,72],[12,20,25,41,58,62,109,110,118,119,130,131,142,146,157,158,159,944],[0]),([0,1,2,3,5,21,31],[20,36,41,62,82,131,142,161,162,166],[0,1]),([0,1,2,3,4,5,49],[0,1,5,12,25,36,40,41,79,176,177,178,180,181],[0]),([0,1,2,3,4,5,74],[0,1,5,12,20,25,41,62,79,121,142,182,184,186,189],[0]),([0,1,2,3,4,5,21,74],[20,41,58,62,82,109,110,121,122,130,131,141,142,146,182,184,186,189],[0]),([0,1,2,3,4,5,79],[0,1,5,12,20,25,62,79,82,137,240,244,981,982,983,984,985],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_6 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_6 = true := by decide +kernel
def h0Block9_7 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,80],[0,1,5,8,12,20,25,62,79,82,96,137,245,381,388,991,992,993,994,995]),([0,1,2,3,4,5,81],[0,1,5,10,12,20,25,62,79,82,127,220,247,248,251,252,253,356]),([0,1,2,3,4,5,82],[0,1,5,12,20,25,62,79,133,137,259,262,263,267,268,269])]
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
def h0Block10_0 : List NodeSpec := [([0,1,2,3,4,5,6],[0,1,2,5,12,19,20,25,56,62,82,93],[0,1]),([0,1,2,3,4,5,7],[0,1,5,12,20,25,62,82,219,240,312,318,338,351],[0,1]),([0,1,2,3,4,5,8],[0,1,12,20,25,62,82,423,424,428,430],[0,1]),([0,1,2,3,4,5,9],[0,1,5,12,20,25,62,82,240,536,537,540,542],[0]),([0,1,2,3,4,5,10],[0,1,12,20,25,62,82,313,425,437,463],[0,1]),([0,1,2,3,4,5,11],[0,1,12,20,25,62,82,319,320,330,340],[0,1]),([0,1,2,3,4,5,12],[0,1,12,20,25,41,62,82,353,354,358,369],[0,1]),([0,1,2,3,4,5,15],[0,1,3,4,12,20,25,47,59,62,82],[0,1]),([0,1,2,3,4,5,21],[0,1,12,20,25,41,62,82,109,110,130,142],[0,1]),([0,1,2,3,4,5,26],[0,1,12,20,25,62,82,127,244,245,259],[0,1]),([0,1,2,3,4,5,31],[0,1,12,20,25,34,35,36,38,40,41,62,82],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test10_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket9 10 h0Block10_0 = true := by decide +kernel
def h0Nodes10 : List NodeSpec := h0Block10_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Check10 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket9 10 h0Nodes10 = true := h0Test10_0
def h0Bucket10 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes10
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket10Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 10 xs.toFinset) h0Bucket10 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0Bucket9Ok h0Check10
def h0Block11_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,20,25,62,82],[0,1])]
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
lemma h0Bound : Lower h0R h0G 12 := lower_of_forestBT (essPairs := [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11),(VAR 4,5,21),(VAR 5,5,37)]) (by decide +kernel) h0Bucket11Ok (by decide +kernel)
def wit : List PEqualNP.CircuitLowerBounds.Gate := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 7]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 5]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 9]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 10]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 3]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 12]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 5]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 14]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 15]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 16]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 17]⟩]
def wo : Nat := 18
lemma wit_mono : PEqualNP.MetaComplexity.Monotone2 ⟨wit, wo⟩ := by simp [PEqualNP.MetaComplexity.Monotone2, wit]
set_option maxRecDepth 100000 in set_option maxHeartbeats 0 in
lemma wit_eval : ∀ r : Row, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput6 r)) = ((4008241888 * 2 ^ 32 + 3940608128) ||| ((4008241888 * 2 ^ 32 + 3940608128) <<< 64)).testBit r.val := by decide +kernel
lemma low_root : Lower (varsOf 63) ((4008241888 * 2 ^ 32 + 3940608128) ||| ((4008241888 * 2 ^ 32 + 3940608128) <<< 64)) 12 := h0Bound
end PEqualNP.Outside.L_meta_47739
theorem PEqualNP.Outside.L_meta_47739 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241888 * 2 ^ 32 + 3940608128) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241888 * 2 ^ 32 + 3940608128) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hcs
  exact PEqualNP.Outside.L_meta_47739.table2_of_lower (4008241888 * 2 ^ 32 + 3940608128) (by decide) (by decide) (by decide) (by decide)
    12 PEqualNP.Outside.L_meta_47739.low_root
    PEqualNP.Outside.L_meta_47739.wit PEqualNP.Outside.L_meta_47739.wo (by decide)
    PEqualNP.Outside.L_meta_47739.wit_mono PEqualNP.Outside.L_meta_47739.wit_eval s hcs
