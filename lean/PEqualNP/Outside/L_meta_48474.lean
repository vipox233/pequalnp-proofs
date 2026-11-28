import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_48474
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

structure CertifiedBucket (G k : Nat) where
  rows : List (List Nat)
  valid : ∀ xs ∈ rows, Impossible G k xs.toFinset

def bucketFragment {G k : Nat} (W : BT Decor) (ns : List NodeSpec)
    (h : ∀ s ∈ ns, Impossible G k (nodeValsBT W s).toFinset) (off len : Nat) : CertifiedBucket G k :=
  ⟨((ns.drop off).take len).map (nodeValsBT W), by
    intro xs hx
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hx
    exact h s (List.drop_subset _ _ (List.take_subset _ _ hs))⟩

def joinBucket {G k : Nat} (a b : CertifiedBucket G k) : CertifiedBucket G k :=
  ⟨a.rows ++ b.rows, forall_append a.valid b.valid⟩

def bucketValues {G k : Nat} : BT (CertifiedBucket G k) → BT (List (List Nat))
  | .empty => .empty
  | .leaf x => .leaf x.rows
  | .node a b => .node (bucketValues a) (bucketValues b)

lemma bucketValues_ok {G k : Nat} (t : BT (CertifiedBucket G k)) :
    btAll (fun bk => ∀ xs ∈ bk, Impossible G k xs.toFinset) (bucketValues t) := by
  induction t with
  | empty => trivial
  | leaf x => exact x.valid
  | node _ _ ha hb => exact ⟨ha,hb⟩


def emptyBucket {G k : Nat} : CertifiedBucket G k := ⟨[], fun _ h => (List.not_mem_nil h).elim⟩

def collectParts {G k : Nat} (tbl : BT (Nat → Nat → CertifiedBucket G k)) (ps : List (Nat × Nat × Nat)) :
    CertifiedBucket G k :=
  ps.foldr (fun p r => joinBucket ((btGet (fun _ _ => emptyBucket) tbl p.1) p.2.1 p.2.2) r) emptyBucket

def staticBuckets {G k : Nat} (parts : BT (Nat → Nat → CertifiedBucket G k)) (layout : List (List (Nat × Nat × Nat))) :=
  btOfList 6 (layout.map (collectParts parts))
structure CertifiedDecor (p n : List Nat) where
  val : Decor
  ok : faithful p n val ∧ val.1 < 2^128

namespace F0
def roots : List Nat := varsOf 15
def goal : Nat := 0xeaa8eaa8eaa8eaa8eaa8eaa8eaa8eaa8
def pos : List Nat := [3,3,5,5,9,9,14,14,14,7,3,5,14]
def neg : List Nat := [1,2,1,4,1,8,6,10,12,6,0,6,8]
def base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xe3f,0x15),(0xcccccccccccccccccccccccccccccccc,0x17c3,0xac2),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x1bcc,0xb48),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x11f0,0x11a0)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma pairsOK : goodPairs goal pos neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma baseOK : ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
def wires : BT Decor := buildWiresBT 5 base [(0,0,1),(1,0,1),(2,0,1),(3,0,1),(0,1,2),(1,1,2),(2,1,2),(1,4,2),(3,4,2),(0,5,2),(2,5,2),(1,10,3),(3,10,3)]
set_option maxRecDepth 200000 in
lemma wiresOK : btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) wires := buildWiresBT_faithful baseOK
def alist : List (List (Nat × Nat)) := [[],[(1,2)],[(1,3)],[(2,3)],[(1,3),(1,2)],[(2,3),(1,2)]]
def autos : BT (List (Nat × Nat)) := btOfList 3 alist
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma autosOK : btAll (fun sw => swapsValid sw = true ∧ permWord sw goal = goal) autos := btAll_ofList (autos_of (by decide +kernel))
def sliceList : List (Option (Nat × Nat)) := []
def slices : BT (Option (Nat × Nat)) := btOfList 1 sliceList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma slicesOK : btAll (fun o => ∀ p, o = some p → Slice roots goal p.1 p.2) slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice roots goal p.1 p.2) (fun _ h => by cases h)
def empty : BT (List (List Nat)) := BT.empty
lemma emptyOK : btAll (fun bk => ∀ xs ∈ bk, Impossible goal (3-1) xs.toFinset) empty := trivial
def b3x0Pools : BT (Option BoundPool) := buildPoolsBT 1 wires roots slices []
def b3x0 : List NodeSpec := [([14,0,1,3],[],[]),([0,1,2,16],[],[]),([12,0,1,3],[],[]),([0,1,13,3],[],[]),([0,1,11,3],[],[]),([0,8,9,3],[],[]),([0,1,2,15],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b3x0Ok : checkNodesBT wires goal (fullMask 13) b3x0Pools autos empty 3 b3x0 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b3x0Mem : ∀ ns ∈ b3x0, Impossible goal 3 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK emptyOK b3x0Ok
def table3 : BT (List (List Nat)) := buildBucketsBT wires b3x0
set_option maxRecDepth 200000 in
lemma table3OK : btAll (fun bk => ∀ xs ∈ bk, Impossible goal 3 xs.toFinset) table3 := buildBucketsBT_of_mem b3x0Mem
def b4x0Pools : BT (Option BoundPool) := buildPoolsBT 1 wires roots slices []
def b4x0 : List NodeSpec := [([10,0,1,2,3],[],[0]),([0,8,1,2,3],[],[0]),([0,1,2,9,3],[],[0]),([6,0,1,2,3],[],[]),([4,0,1,2,3],[],[0,3]),([0,1,5,2,3],[],[0,3]),([7,0,1,2,3],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b4x0Ok : checkNodesBT wires goal (fullMask 13) b4x0Pools autos table3 4 b4x0 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b4x0Mem : ∀ ns ∈ b4x0, Impossible goal 4 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table3OK b4x0Ok
def table4 : BT (List (List Nat)) := buildBucketsBT wires b4x0
set_option maxRecDepth 200000 in
lemma table4OK : btAll (fun bk => ∀ xs ∈ bk, Impossible goal 4 xs.toFinset) table4 := buildBucketsBT_of_mem b4x0Mem
def b5x0Pools : BT (Option BoundPool) := buildPoolsBT 1 wires roots slices []
def b5x0 : List NodeSpec := [([0,1,2,3],[],[0,1,2,3,4,5])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b5x0Ok : checkNodesBT wires goal (fullMask 13) b5x0Pools autos table4 5 b5x0 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b5x0Mem : ∀ ns ∈ b5x0, Impossible goal 5 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table4OK b5x0Ok
def table5 : BT (List (List Nat)) := buildBucketsBT wires b5x0
set_option maxRecDepth 200000 in
lemma table5OK : btAll (fun bk => ∀ xs ∈ bk, Impossible goal 5 xs.toFinset) table5 := buildBucketsBT_of_mem b5x0Mem
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lower : Lower roots goal 6 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 3,1,9)]) (by decide +kernel) table5OK (by decide +kernel)
end F0
namespace F1
def roots : List Nat := varsOf 7
def goal : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def pos : List Nat := [3,3,5,5,6,6]
def neg : List Nat := [1,2,1,4,2,4]
def base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf,0x5),(0xcccccccccccccccccccccccccccccccc,0x33,0x12),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x3c,0x28)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma pairsOK : goodPairs goal pos neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma baseOK : ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
def wires : BT Decor := buildWiresBT 2 base []
set_option maxRecDepth 200000 in
lemma wiresOK : btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) wires := buildWiresBT_faithful baseOK
def alist : List (List (Nat × Nat)) := [[],[(0,1)],[(0,2)],[(1,2)],[(0,2),(0,1)],[(1,2),(0,1)]]
def autos : BT (List (Nat × Nat)) := btOfList 3 alist
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma autosOK : btAll (fun sw => swapsValid sw = true ∧ permWord sw goal = goal) autos := btAll_ofList (autos_of (by decide +kernel))
def sliceList : List (Option (Nat × Nat)) := []
def slices : BT (Option (Nat × Nat)) := btOfList 1 sliceList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma slicesOK : btAll (fun o => ∀ p, o = some p → Slice roots goal p.1 p.2) slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice roots goal p.1 p.2) (fun _ h => by cases h)
def empty : BT (List (List Nat)) := BT.empty
lemma emptyOK : btAll (fun bk => ∀ xs ∈ bk, Impossible goal (3-1) xs.toFinset) empty := trivial
def b3x0Pools : BT (Option BoundPool) := buildPoolsBT 1 wires roots slices []
def b3x0 : List NodeSpec := [([0,1,2],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b3x0Ok : checkNodesBT wires goal (fullMask 6) b3x0Pools autos empty 3 b3x0 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b3x0Mem : ∀ ns ∈ b3x0, Impossible goal 3 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK emptyOK b3x0Ok
def table3 : BT (List (List Nat)) := buildBucketsBT wires b3x0
set_option maxRecDepth 200000 in
lemma table3OK : btAll (fun bk => ∀ xs ∈ bk, Impossible goal 3 xs.toFinset) table3 := buildBucketsBT_of_mem b3x0Mem
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lower : Lower roots goal 4 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5)]) (by decide +kernel) table3OK (by decide +kernel)
end F1
namespace F2
def roots : List Nat := varsOf 15
def goal : Nat := 0xe888e888e888e888e888e888e888e888
def pos : List Nat := [3,3,13,13,13,14,14,14]
def neg : List Nat := [1,2,5,9,12,6,10,12]
def base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x1f,0xd),(0xcccccccccccccccccccccccccccccccc,0xe3,0x62),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfc,0xb4),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xfc,0xd8)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma pairsOK : goodPairs goal pos neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma baseOK : ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
def wires : BT Decor := buildWiresBT 2 base []
set_option maxRecDepth 200000 in
lemma wiresOK : btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) wires := buildWiresBT_faithful baseOK
def alist : List (List (Nat × Nat)) := [[],[(0,1)],[(2,3)],[(2,3),(0,1)]]
def autos : BT (List (Nat × Nat)) := btOfList 2 alist
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma autosOK : btAll (fun sw => swapsValid sw = true ∧ permWord sw goal = goal) autos := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl0 : Slice roots goal (subcubeFast 0 4) 4 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 11)) (qGoal := 0xee88ee88ee88ee88ee88ee88ee88ee88) (by decide +kernel) (carry_of (swaps := [(2,3)]) (by decide +kernel) F1.lower)
def sliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 4,4)]
def slices : BT (Option (Nat × Nat)) := btOfList 0 sliceList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma slicesOK : btAll (fun o => ∀ p, o = some p → Slice roots goal p.1 p.2) slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice roots goal p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl0) (fun _ h => by cases h))
def empty : BT (List (List Nat)) := BT.empty
lemma emptyOK : btAll (fun bk => ∀ xs ∈ bk, Impossible goal (4-1) xs.toFinset) empty := trivial
def b4x0Pools : BT (Option BoundPool) := buildPoolsBT 0 wires roots slices [(0,[])]
def b4x0 : List NodeSpec := [([0,1,2,3],[0],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b4x0Ok : checkNodesBT wires goal (fullMask 8) b4x0Pools autos empty 4 b4x0 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b4x0Mem : ∀ ns ∈ b4x0, Impossible goal 4 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK emptyOK b4x0Ok
def table4 : BT (List (List Nat)) := buildBucketsBT wires b4x0
set_option maxRecDepth 200000 in
lemma table4OK : btAll (fun bk => ∀ xs ∈ bk, Impossible goal 4 xs.toFinset) table4 := buildBucketsBT_of_mem b4x0Mem
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lower : Lower roots goal 5 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,9,13),(VAR 3,5,13)]) (by decide +kernel) table4OK (by decide +kernel)
end F2
namespace F3
def roots : List Nat := varsOf 31
def goal : Nat := 0xe8888880e8888880e8888880e8888880
def pos : List Nat := [7,7,7,11,11,11,19,19,19,29,29,29,29,30,30,30,30,15,15,23,23,27,7,7,7,7,11,11,11,19,19,29,29,11]
def neg : List Nat := [3,5,6,3,9,10,3,17,18,13,21,25,28,14,22,26,28,13,14,21,22,26,1,2,4,13,1,13,14,22,26,17,24,12]
def base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x3fffe1fff,0x8e4a0edb),(0xcccccccccccccccccccccccccccccccc,0x27fffe1ff,0x70b4e16d),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x183dffe07,0x23b1f7606),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x39c27fe38,0x35a27ba30),(0xffff0000ffff0000ffff0000ffff0000,0x1e039ffc0,0x1e039dd80)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma pairsOK : goodPairs goal pos neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma baseOK : ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
def wires : BT Decor := buildWiresBT 7 base [(0,0,1),(1,0,1),(0,0,2),(2,0,2),(3,0,2),(0,1,2),(1,1,2),(2,1,2),(3,1,2),(0,1,3),(0,2,3),(1,2,3),(2,2,3),(3,2,3),(0,3,4),(0,5,2),(3,20,0),(3,20,1),(3,20,2),(1,20,3),(0,20,3),(3,25,2),(3,25,3),(3,25,4),(3,20,4),(1,18,20),(3,18,4),(3,20,5),(1,5,2),(0,27,6),(0,6,2),(0,6,4),(3,20,33),(0,33,3),(2,33,3),(3,32,1),(0,23,3),(3,23,3),(3,42,4),(1,17,4),(0,7,3),(3,7,3),(1,7,14),(3,18,1),(0,5,16),(0,0,16),(3,49,4),(3,5,16),(1,17,5),(3,17,5),(3,17,0),(3,17,4),(0,22,3),(3,22,3),(3,45,1),(3,45,2),(0,45,4),(3,61,1),(3,45,4),(3,46,1),(0,46,4),(3,46,4),(0,15,4),(2,0,67),(3,50,1),(3,55,1)]
set_option maxRecDepth 200000 in
lemma wiresOK : btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) wires := buildWiresBT_faithful baseOK
def alist : List (List (Nat × Nat)) := [[],[(0,1)],[(2,3)],[(2,4)],[(3,4)],[(2,3),(0,1)],[(2,4),(0,1)],[(3,4),(0,1)],[(2,4),(2,3)],[(3,4),(2,3)],[(2,4),(2,3),(0,1)],[(3,4),(2,3),(0,1)]]
def autos : BT (List (Nat × Nat)) := btOfList 4 alist
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma autosOK : btAll (fun sw => swapsValid sw = true ∧ permWord sw goal = goal) autos := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl0 : Slice roots goal (subcubeFast 0 1) 6 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 30)) (qGoal := 0xfcccccc0fcccccc0fcccccc0fcccccc0) (by decide +kernel) (carry_of (swaps := [(3,4),(2,3),(1,2),(0,1)]) (by decide +kernel) F0.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl1 : Slice roots goal (subcubeFast 0 2) 6 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 29)) (qGoal := 0xfaaaaaa0faaaaaa0faaaaaa0faaaaaa0) (by decide +kernel) (carry_of (swaps := [(3,4),(2,3),(1,2)]) (by decide +kernel) F0.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl2 : Slice roots goal (subcubeFast 0 4) 5 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 27)) (qGoal := 0xee888888ee888888ee888888ee888888) (by decide +kernel) (carry_of (swaps := [(3,4),(2,3)]) (by decide +kernel) F2.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl3 : Slice roots goal (subcubeFast 0 8) 5 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 23)) (qGoal := 0xe8e88888e8e88888e8e88888e8e88888) (by decide +kernel) (carry_of (swaps := [(3,4)]) (by decide +kernel) F2.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl4 : Slice roots goal (subcubeFast 0 16) 5 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 15)) (qGoal := 0xe888e888e888e888e888e888e888e888) (by decide +kernel) (carry_of (swaps := []) (by decide +kernel) F2.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl5 : Slice roots goal (subcubeFast 0 12) 4 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 19)) (qGoal := 0xeeee8888eeee8888eeee8888eeee8888) (by decide +kernel) (carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) F1.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl6 : Slice roots goal (subcubeFast 0 20) 4 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 11)) (qGoal := 0xee88ee88ee88ee88ee88ee88ee88ee88) (by decide +kernel) (carry_of (swaps := [(2,3)]) (by decide +kernel) F1.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl7 : Slice roots goal (subcubeFast 0 24) 4 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 7)) (qGoal := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8) (by decide +kernel) (carry_of (swaps := []) (by decide +kernel) F1.lower)
def sliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,6),some (subcubeFast 0 2,6),some (subcubeFast 0 4,5),some (subcubeFast 0 8,5),some (subcubeFast 0 16,5),some (subcubeFast 0 12,4),some (subcubeFast 0 20,4),some (subcubeFast 0 24,4)]
def slices : BT (Option (Nat × Nat)) := btOfList 3 sliceList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma slicesOK : btAll (fun o => ∀ p, o = some p → Slice roots goal p.1 p.2) slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice roots goal p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl0) (forall_cons (fun _ h => by cases h; exact sl1) (forall_cons (fun _ h => by cases h; exact sl2) (forall_cons (fun _ h => by cases h; exact sl3) (forall_cons (fun _ h => by cases h; exact sl4) (forall_cons (fun _ h => by cases h; exact sl5) (forall_cons (fun _ h => by cases h; exact sl6) (forall_cons (fun _ h => by cases h; exact sl7) (fun _ h => by cases h)))))))))
def empty : BT (List (List Nat)) := BT.empty
lemma emptyOK : btAll (fun bk => ∀ xs ∈ bk, Impossible goal (3-1) xs.toFinset) empty := trivial
def ps0 : PoolSpec := (0,[(0,2,3),(1,2,3)])
def b3x0Pools : BT (Option BoundPool) := buildPoolsBT 1 wires roots slices []
def b3x0 : List NodeSpec := [([34,5,2,4],[],[]),([5,47,15,4],[],[]),([27,5,35,4],[],[]),([27,5,36,2],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b3x0Ok : checkNodesBT wires goal (fullMask 34) b3x0Pools autos empty 3 b3x0 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b3x0Mem : ∀ ns ∈ b3x0, Impossible goal 3 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK emptyOK b3x0Ok
def table3 : BT (List (List Nat)) := buildBucketsBT wires b3x0
set_option maxRecDepth 200000 in
lemma table3OK : btAll (fun bk => ∀ xs ∈ bk, Impossible goal 3 xs.toFinset) table3 := buildBucketsBT_of_mem b3x0Mem
def b4x0Pools : BT (Option BoundPool) := buildPoolsBT 2 wires roots slices [(1,[]),(6,[]),(5,[]),(0,[])]
def b4x0 : List NodeSpec := [([37,0,1,3,4],[],[]),([43,0,1,2,3],[],[]),([5,45,10,3,4],[0],[]),([62,0,2,3,4],[],[]),([28,0,1,2,3],[],[]),([0,1,47,15,4],[],[0]),([23,0,1,24,4],[],[]),([26,0,1,3,4],[],[]),([20,0,1,31,3],[1,2],[]),([5,7,1,31,3],[],[]),([46,5,10,3,4],[],[]),([22,0,1,31,3],[],[]),([5,7,14,15,4],[],[0]),([30,0,1,3,4],[],[]),([23,0,1,3,44],[],[]),([5,50,1,15,4],[2],[]),([5,7,48,3,4],[],[]),([27,5,6,2,4],[],[0]),([27,29,0,1,2],[],[]),([5,47,2,3,4],[3,0],[0]),([69,0,1,15,4],[],[]),([41,0,1,16,4],[],[]),([51,0,1,2,3],[],[]),([20,0,1,38,4],[2,1],[]),([49,0,1,15,4],[2,1],[]),([29,0,1,2,24],[],[]),([5,7,1,38,4],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b4x0Ok : checkNodesBT wires goal (fullMask 34) b4x0Pools autos table3 4 b4x0 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b4x0Mem : ∀ ns ∈ b4x0, Impossible goal 4 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table3OK b4x0Ok
def table4 : BT (List (List Nat)) := buildBucketsBT wires b4x0
set_option maxRecDepth 200000 in
lemma table4OK : btAll (fun bk => ∀ xs ∈ bk, Impossible goal 4 xs.toFinset) table4 := buildBucketsBT_of_mem b4x0Mem
def b5x0Pools : BT (Option BoundPool) := buildPoolsBT 4 wires roots slices [(1,[]),(2,[]),(0,[]),(4,[]),(6,[]),(5,[]),ps0,(7,[]),(3,[])]
def b5x0 : List NodeSpec := [([5,55,1,2,3,4],[0],[5]),([46,0,10,1,3,4],[],[0]),([70,0,1,2,3,4],[],[]),([5,7,10,3,4],[0,1,2],[0,1,4,7]),([42,0,1,2,3,4],[3],[0]),([41,0,1,2,3,4],[],[0]),([61,0,1,2,3,4],[0],[0]),([69,0,1,2,3,4],[],[0]),([50,0,1,15,4],[4,5,6],[0]),([63,0,1,2,3,4],[],[]),([18,22,0,1,3,4],[],[0]),([52,0,1,2,3,4],[],[]),([20,0,1,2,24,4],[7],[0,2]),([5,7,10,2,3,4],[1,0],[]),([53,0,1,2,3,4],[1],[]),([27,0,1,2,4],[],[]),([7,0,14,1,15,4],[],[0]),([49,0,1,2,3,4],[1,8,3],[0]),([68,0,1,2,3,4],[],[]),([21,20,1,2,3,4],[2],[]),([60,45,0,1,3,4],[2],[]),([65,0,1,2,3,4],[],[]),([23,20,0,1,3,4],[2],[0,4]),([54,0,1,2,3,4],[],[0]),([7,0,48,1,3,4],[],[0]),([22,5,7,2,3,4],[0,2],[]),([23,5,7,1,3,4],[2],[]),([46,7,0,1,15,4],[8],[]),([27,5,0,1,2,4],[],[0]),([59,0,1,2,3,4],[],[]),([0,58,1,2,3,4],[],[]),([32,23,0,1,3,4],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b5x0Ok : checkNodesBT wires goal (fullMask 34) b5x0Pools autos table4 5 b5x0 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b5x0Mem : ∀ ns ∈ b5x0, Impossible goal 5 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table4OK b5x0Ok
def b5x1Pools : BT (Option BoundPool) := buildPoolsBT 4 wires roots slices [(0,[]),(5,[]),(6,[]),(1,[]),(2,[]),(0,[(1,1,2),(0,33,3)]),(0,[(0,1,2),(1,20,3)]),(0,[(1,1,2),(2,33,3)]),(4,[]),(3,[]),(1,[(0,0,2),(3,7,3)]),(0,[(3,2,3),(3,18,4)]),(0,[(2,2,3),(1,17,4)]),ps0]
def b5x1 : List NodeSpec := [([7,0,1,67,3,4],[0,1,2],[]),([0,1,47,2,3,4],[0,3],[0]),([27,7,0,1,2,4],[],[]),([22,7,0,10,3,4],[4],[]),([5,0,1,2,38,4],[4,5],[0,1]),([5,0,1,2,24,4],[1,6],[0]),([39,5,0,1,2,4],[7],[]),([46,0,1,2,19,4],[8],[]),([27,0,1,2,3,4],[],[]),([5,45,1,2,3,4],[3],[0,2]),([20,0,1,15,3,4],[9,2],[]),([57,0,1,2,3,4],[],[]),([5,7,1,15,3,4],[],[0,1]),([64,0,1,2,3,4],[],[2]),([5,7,14,2,3,4],[],[0,1,2]),([46,5,1,2,3,4],[10],[0]),([7,0,1,31,3],[2,1,11],[0]),([5,50,1,2,3,4],[3],[0]),([45,0,10,1,3,4],[3],[0]),([21,7,1,2,3,4],[0],[]),([66,0,1,2,3,4],[4],[]),([22,0,1,15,3,4],[9],[]),([5,0,1,2,3,44],[1,12],[0]),([23,0,1,3,16,4],[],[0]),([25,0,1,2,3,4],[8],[0,2]),([27,20,0,1,2,4],[9],[0,4]),([20,0,1,33,3,4],[1,2],[0,4]),([5,0,1,15,16,4],[1,13],[0,1]),([17,23,0,1,3,4],[],[0]),([18,20,0,1,3,4],[9,2],[0]),([5,7,1,33,3,4],[0],[0,4]),([18,5,7,1,3,4],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b5x1Ok : checkNodesBT wires goal (fullMask 34) b5x1Pools autos table4 5 b5x1 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b5x1Mem : ∀ ns ∈ b5x1, Impossible goal 5 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table4OK b5x1Ok
def b5x2Pools : BT (Option BoundPool) := buildPoolsBT 1 wires roots slices [(3,[]),(0,[(2,2,3),(3,17,4)])]
def b5x2 : List NodeSpec := [([5,0,1,2,3,56],[0,1],[2,5])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b5x2Ok : checkNodesBT wires goal (fullMask 34) b5x2Pools autos table4 5 b5x2 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b5x2Mem : ∀ ns ∈ b5x2, Impossible goal 5 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table4OK b5x2Ok
def table5 : BT (List (List Nat)) := buildBucketsBT wires (b5x0 ++ (b5x1 ++ b5x2))
set_option maxRecDepth 200000 in
lemma table5OK : btAll (fun bk => ∀ xs ∈ bk, Impossible goal 5 xs.toFinset) table5 := buildBucketsBT_of_mem (forall_append b5x0Mem (forall_append b5x1Mem b5x2Mem))
def b6x0Pools : BT (Option BoundPool) := buildPoolsBT 5 wires roots slices [(1,[(0,0,2)]),(2,[]),(0,[]),(5,[]),(1,[]),(4,[]),(0,[(0,2,3)]),(6,[]),(0,[(1,2,3)]),(3,[]),(0,[(2,2,3)]),(1,[(0,0,2),(3,7,3)]),(0,[(3,2,3)]),(7,[]),(0,[(3,1,2)]),(0,[(1,1,2)]),(0,[(0,1,2)]),(0,[(2,1,2)]),(1,[(2,0,2)]),(1,[(3,0,2)]),(0,[(2,2,3),(1,17,4)]),(1,[(2,2,3),(1,17,4)]),ps0,(1,[(0,2,3),(1,2,3)]),(0,[(2,2,3),(3,17,4)]),(1,[(2,2,3),(3,17,4)])]
def b6x0 : List NodeSpec := [([22,7,0,1,2,3,4],[0,1,2],[0,1]),([45,0,1,2,3,4],[3,4,5,6],[0,2]),([5,0,1,15,2,3,4],[3,6,4],[0,1,2,5]),([7,0,1,15,3,4],[3,6,7],[0,1]),([5,0,1,2,3,16,4],[1,8,9,4],[0,1,2]),([17,5,0,1,2,3,4],[9,10,4,1],[0,1,2,5]),([46,0,1,2,3,4],[3,11,5,12],[0,2]),([50,0,1,2,3,4],[7,9,4,8],[0]),([0,1,67,2,3,4],[3,7,2,4,13],[0,1,2,3,5,6]),([45,7,0,1,2,3,4],[3,10],[2]),([5,0,1,2,33,3,4],[14,1,4,15],[0,1,4]),([18,7,0,1,3,4],[7,3,8,12],[0]),([7,0,14,1,2,3,4],[9,1],[0,1,2,5]),([20,0,1,2,3,4],[9,5,16,17,14],[0,1,4]),([55,0,1,2,3,4],[3,13,4,10],[0,5]),([5,7,1,2,3,4],[0,1,2],[0,4]),([46,7,0,1,2,3,4],[3,2],[0,2]),([20,5,0,1,2,3,4],[18,17,16],[0,4]),([0,40,1,2,3,4],[3,16,7],[]),([12,7,0,1,3,4],[3,0,7,15],[]),([23,0,1,2,3,4],[14,19,9,5,16],[0,4]),([7,0,10,1,3,4],[0,16,1],[0,1,4,7]),([7,0,1,2,19,3,4],[13,7,3],[0,4]),([32,5,0,1,2,3,4],[16,1,0,17],[0]),([22,0,1,2,3,4],[17,0,9,5],[0,1,4]),([0,1,2,3,44],[3,5,20,21],[0]),([20,7,0,1,2,3,4],[14,3,7,0],[0,1,4]),([0,1,15,16,4],[7,3,22,23],[0,1]),([23,5,0,1,2,3,4],[14,1,4],[0,1]),([0,1,2,3,56],[3,13,24,25],[0,2,5]),([7,0,10,1,2,3,4],[16,1,4],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b6x0Ok : checkNodesBT wires goal (fullMask 34) b6x0Pools autos table5 6 b6x0 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b6x0Mem : ∀ ns ∈ b6x0, Impossible goal 6 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table5OK b6x0Ok
def table6 : BT (List (List Nat)) := buildBucketsBT wires b6x0
set_option maxRecDepth 200000 in
lemma table6OK : btAll (fun bk => ∀ xs ∈ bk, Impossible goal 6 xs.toFinset) table6 := buildBucketsBT_of_mem b6x0Mem
def b7x0Pools : BT (Option BoundPool) := buildPoolsBT 4 wires roots slices [(5,[]),(0,[]),(6,[]),(1,[(0,0,2)]),(0,[(0,2,3)]),(1,[(0,2,3)]),(7,[]),(3,[]),(0,[(1,2,3)]),(1,[(1,2,3)]),(0,[(2,2,3)]),(1,[(2,2,3)]),(1,[]),(2,[]),(4,[])]
def b7x0 : List NodeSpec := [([7,0,1,2,3,4],[0,1,2,3],[0,4]),([0,1,15,2,3,4],[0,2,4,5,6],[0,1,2,3,5,6]),([0,1,2,3,16,4],[2,7,8,9],[0,1]),([17,0,1,2,3,4],[6,0,10,11],[0,1,2,5]),([8,0,1,2,3,4],[0,2,1,12],[0,1]),([5,0,1,2,3,4],[1,12,13,7,14],[0,1,2,3,4,5,6,8,9])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b7x0Ok : checkNodesBT wires goal (fullMask 34) b7x0Pools autos table6 7 b7x0 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b7x0Mem : ∀ ns ∈ b7x0, Impossible goal 7 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table6OK b7x0Ok
def table7 : BT (List (List Nat)) := buildBucketsBT wires b7x0
set_option maxRecDepth 200000 in
lemma table7OK : btAll (fun bk => ∀ xs ∈ bk, Impossible goal 7 xs.toFinset) table7 := buildBucketsBT_of_mem b7x0Mem
def b8x0Pools : BT (Option BoundPool) := buildPoolsBT 1 wires roots slices [(0,[]),(1,[])]
def b8x0 : List NodeSpec := [([0,1,2,3,4],[0,1],[0,1,2,3,4,5,6,8,9])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b8x0Ok : checkNodesBT wires goal (fullMask 34) b8x0Pools autos table7 8 b8x0 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b8x0Mem : ∀ ns ∈ b8x0, Impossible goal 8 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table7OK b8x0Ok
def table8 : BT (List (List Nat)) := buildBucketsBT wires b8x0
set_option maxRecDepth 200000 in
lemma table8OK : btAll (fun bk => ∀ xs ∈ bk, Impossible goal 8 xs.toFinset) table8 := buildBucketsBT_of_mem b8x0Mem
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lower : Lower roots goal 9 := lower_of_forestBT (essPairs := [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11),(VAR 4,3,19)]) (by decide +kernel) table8OK (by decide +kernel)
end F3
namespace F4
def roots : List Nat := varsOf 15
def goal : Nat := 0xe8a8e8a8e8a8e8a8e8a8e8a8e8a8e8a8
def pos : List Nat := [3,3,5,5,14,14,14,11]
def neg : List Nat := [1,2,1,4,6,10,12,10]
def base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x8f,0x5),(0xcccccccccccccccccccccccccccccccc,0xf3,0xb2),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x7c,0x58),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xf0,0xe0)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma pairsOK : goodPairs goal pos neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma baseOK : ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
def wires : BT Decor := buildWiresBT 2 base []
set_option maxRecDepth 200000 in
lemma wiresOK : btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) wires := buildWiresBT_faithful baseOK
def alist : List (List (Nat × Nat)) := [[],[(1,2)]]
def autos : BT (List (Nat × Nat)) := btOfList 1 alist
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma autosOK : btAll (fun sw => swapsValid sw = true ∧ permWord sw goal = goal) autos := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl0 : Slice roots goal (subcubeFast 0 8) 4 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 7)) (qGoal := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8) (by decide +kernel) (carry_of (swaps := []) (by decide +kernel) F1.lower)
def sliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 8,4)]
def slices : BT (Option (Nat × Nat)) := btOfList 0 sliceList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma slicesOK : btAll (fun o => ∀ p, o = some p → Slice roots goal p.1 p.2) slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice roots goal p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl0) (fun _ h => by cases h))
def empty : BT (List (List Nat)) := BT.empty
lemma emptyOK : btAll (fun bk => ∀ xs ∈ bk, Impossible goal (4-1) xs.toFinset) empty := trivial
def b4x0Pools : BT (Option BoundPool) := buildPoolsBT 0 wires roots slices [(0,[])]
def b4x0 : List NodeSpec := [([0,1,2,3],[0],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b4x0Ok : checkNodesBT wires goal (fullMask 8) b4x0Pools autos empty 4 b4x0 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b4x0Mem : ∀ ns ∈ b4x0, Impossible goal 4 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK emptyOK b4x0Ok
def table4 : BT (List (List Nat)) := buildBucketsBT wires b4x0
set_option maxRecDepth 200000 in
lemma table4OK : btAll (fun bk => ∀ xs ∈ bk, Impossible goal 4 xs.toFinset) table4 := buildBucketsBT_of_mem b4x0Mem
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lower : Lower roots goal 5 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 3,6,14)]) (by decide +kernel) table4OK (by decide +kernel)
end F4
namespace F5
def roots : List Nat := varsOf 15
def goal : Nat := 0xa880a880a880a880a880a880a880a880
def pos : List Nat := [7,7,7,11,11,11,13,13,13]
def neg : List Nat := [3,5,6,3,9,10,5,9,12]
def base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x1ff,0xdb),(0xcccccccccccccccccccccccccccccccc,0x3f,0x2d),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x1c7,0x146),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x1f8,0x1b0)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma pairsOK : goodPairs goal pos neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma baseOK : ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
def wires : BT Decor := buildWiresBT 2 base []
set_option maxRecDepth 200000 in
lemma wiresOK : btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) wires := buildWiresBT_faithful baseOK
def alist : List (List (Nat × Nat)) := [[],[(1,2)],[(1,3)],[(2,3)],[(1,3),(1,2)],[(2,3),(1,2)]]
def autos : BT (List (Nat × Nat)) := btOfList 3 alist
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma autosOK : btAll (fun sw => swapsValid sw = true ∧ permWord sw goal = goal) autos := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl0 : Slice roots goal (subcubeFast 0 1) 4 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 14)) (qGoal := 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0) (by decide +kernel) (carry_of (swaps := [(2,3),(1,2),(0,1)]) (by decide +kernel) F1.lower)
def sliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,4)]
def slices : BT (Option (Nat × Nat)) := btOfList 0 sliceList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma slicesOK : btAll (fun o => ∀ p, o = some p → Slice roots goal p.1 p.2) slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice roots goal p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl0) (fun _ h => by cases h))
def empty : BT (List (List Nat)) := BT.empty
lemma emptyOK : btAll (fun bk => ∀ xs ∈ bk, Impossible goal (4-1) xs.toFinset) empty := trivial
def b4x0Pools : BT (Option BoundPool) := buildPoolsBT 0 wires roots slices [(0,[])]
def b4x0 : List NodeSpec := [([0,1,2,3],[0],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b4x0Ok : checkNodesBT wires goal (fullMask 9) b4x0Pools autos empty 4 b4x0 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b4x0Mem : ∀ ns ∈ b4x0, Impossible goal 4 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK emptyOK b4x0Ok
def table4 : BT (List (List Nat)) := buildBucketsBT wires b4x0
set_option maxRecDepth 200000 in
lemma table4OK : btAll (fun bk => ∀ xs ∈ bk, Impossible goal 4 xs.toFinset) table4 := buildBucketsBT_of_mem b4x0Mem
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lower : Lower roots goal 5 := lower_of_forestBT (essPairs := [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11)]) (by decide +kernel) table4OK (by decide +kernel)
end F5
namespace F6
def roots : List Nat := varsOf 31
def goal : Nat := 0xe8a8a880e8a8a880e8a8a880e8a8a880
def pos : List Nat := [7,7,7,11,11,11,13,13,13,19,19,19,21,21,21,30,30,30,30,15,23,27,27,29,7,7,7,7,7,11,11,11,13,13,13,19,30,30,30,30,30]
def neg : List Nat := [3,5,6,3,9,10,5,9,12,3,17,18,5,17,20,14,22,26,28,14,22,25,26,25,1,2,4,14,22,1,2,14,1,14,25,25,6,18,20,24,25]
def base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffff87fff,0x10d21a036db),(0xcccccccccccccccccccccccccccccccc,0x1f8ff7f8e3f,0x32da5b8a2d),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x1f71f9ff1c7,0x529c1dd146),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x1f7e0ef81f8,0x18e88ee81b0),(0xffff0000ffff0000ffff0000ffff0000,0x1f800f7fe00,0x1ec10f76c00)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma pairsOK : goodPairs goal pos neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma baseOK : ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
def wires : BT Decor := buildWiresBT 7 base [(0,0,1),(2,0,1),(3,0,1),(0,0,2),(1,0,2),(2,0,2),(3,0,2),(0,0,3),(1,0,3),(2,0,3),(3,0,3),(0,1,2),(1,1,2),(2,1,2),(0,1,3),(2,1,3),(0,2,3),(1,2,3),(2,2,3),(3,2,3),(0,2,4),(0,3,4),(1,3,4),(2,3,4),(0,5,2),(3,29,0),(3,29,1),(1,29,3),(3,29,2),(3,29,32),(3,29,4),(0,33,1),(1,5,3),(2,5,3),(0,1,37),(3,38,0),(1,5,8),(0,16,3),(3,16,3),(1,0,16),(1,23,5),(3,23,5),(3,23,1),(0,5,27),(3,48,2),(3,5,27),(0,0,27),(0,1,27),(3,7,2),(3,12,1),(0,54,2),(3,54,2),(1,12,4),(2,16,3),(3,12,4),(1,12,16),(0,60,3),(3,20,2),(1,16,3),(0,16,13),(3,16,13),(1,39,2),(0,13,4),(2,13,4),(2,39,2),(3,39,2),(3,15,1),(0,71,2),(3,71,2),(1,15,16),(3,29,44),(2,44,3),(3,42,2),(3,42,63),(1,58,4),(3,58,4),(1,43,4),(3,43,4),(3,16,27),(0,16,27),(0,2,27),(1,28,16),(3,28,16),(1,19,25),(3,40,2),(2,0,62),(3,51,1),(2,0,52),(3,52,2),(3,28,1),(3,94,2)]
set_option maxRecDepth 200000 in
lemma wiresOK : btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) wires := buildWiresBT_faithful baseOK
def alist : List (List (Nat × Nat)) := [[],[(1,2)],[(3,4)],[(3,4),(1,2)]]
def autos : BT (List (Nat × Nat)) := btOfList 2 alist
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma autosOK : btAll (fun sw => swapsValid sw = true ∧ permWord sw goal = goal) autos := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl0 : Slice roots goal (subcubeFast 0 2) 6 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 29)) (qGoal := 0xfaaaaaa0faaaaaa0faaaaaa0faaaaaa0) (by decide +kernel) (carry_of (swaps := [(3,4),(2,3),(1,2)]) (by decide +kernel) F0.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl1 : Slice roots goal (subcubeFast 0 4) 6 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 27)) (qGoal := 0xeeaaaa88eeaaaa88eeaaaa88eeaaaa88) (by decide +kernel) (carry_of (swaps := [(3,4),(2,3)]) (by decide +kernel) F0.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl2 : Slice roots goal (subcubeFast 0 1) 5 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 30)) (qGoal := 0xfcfcfcc0fcfcfcc0fcfcfcc0fcfcfcc0) (by decide +kernel) (dualLower (G := 0xfcc0c0c0fcc0c0c0fcc0c0c0fcc0c0c0) (by decide +kernel) (by decide +kernel) (carry_of (swaps := [(3,4),(2,3),(1,2),(0,1)]) (by decide +kernel) F2.lower))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl3 : Slice roots goal (subcubeFast 0 8) 5 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 23)) (qGoal := 0xe8e8a8a8e8e8a8a8e8e8a8a8e8e8a8a8) (by decide +kernel) (carry_of (swaps := [(3,4)]) (by decide +kernel) F4.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl4 : Slice roots goal (subcubeFast 0 16) 5 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 15)) (qGoal := 0xe8a8e8a8e8a8e8a8e8a8e8a8e8a8e8a8) (by decide +kernel) (carry_of (swaps := []) (by decide +kernel) F4.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl5 : Slice roots goal (subcubeFast 8 0) 5 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 23)) (qGoal := 0xa8a88080a8a88080a8a88080a8a88080) (by decide +kernel) (carry_of (swaps := [(3,4)]) (by decide +kernel) F5.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl6 : Slice roots goal (subcubeFast 16 0) 5 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 15)) (qGoal := 0xa880a880a880a880a880a880a880a880) (by decide +kernel) (carry_of (swaps := []) (by decide +kernel) F5.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl7 : Slice roots goal (subcubeFast 0 24) 4 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 7)) (qGoal := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8) (by decide +kernel) (carry_of (swaps := []) (by decide +kernel) F1.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl8 : Slice roots goal (subcubeFast 8 1) 4 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 22)) (qGoal := 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0) (by decide +kernel) (carry_of (swaps := [(2,3),(3,4),(1,2),(0,1)]) (by decide +kernel) F1.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl9 : Slice roots goal (subcubeFast 16 1) 4 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 14)) (qGoal := 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0) (by decide +kernel) (carry_of (swaps := [(2,3),(1,2),(0,1)]) (by decide +kernel) F1.lower)
def sliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 2,6),some (subcubeFast 0 4,6),some (subcubeFast 0 1,5),some (subcubeFast 0 8,5),some (subcubeFast 0 16,5),some (subcubeFast 8 0,5),some (subcubeFast 16 0,5),some (subcubeFast 0 24,4),some (subcubeFast 8 1,4),some (subcubeFast 16 1,4)]
def slices : BT (Option (Nat × Nat)) := btOfList 4 sliceList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma slicesOK : btAll (fun o => ∀ p, o = some p → Slice roots goal p.1 p.2) slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice roots goal p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl0) (forall_cons (fun _ h => by cases h; exact sl1) (forall_cons (fun _ h => by cases h; exact sl2) (forall_cons (fun _ h => by cases h; exact sl3) (forall_cons (fun _ h => by cases h; exact sl4) (forall_cons (fun _ h => by cases h; exact sl5) (forall_cons (fun _ h => by cases h; exact sl6) (forall_cons (fun _ h => by cases h; exact sl7) (forall_cons (fun _ h => by cases h; exact sl8) (forall_cons (fun _ h => by cases h; exact sl9) (fun _ h => by cases h)))))))))))
def empty : BT (List (List Nat)) := BT.empty
lemma emptyOK : btAll (fun bk => ∀ xs ∈ bk, Impossible goal (3-1) xs.toFinset) empty := trivial
def b3x0Pools : BT (Option BoundPool) := buildPoolsBT 1 wires roots slices []
def b3x0 : List NodeSpec := [([41,16,61,4],[],[]),([34,41,16,4],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b3x0Ok : checkNodesBT wires goal (fullMask 41) b3x0Pools autos empty 3 b3x0 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b3x0Mem : ∀ ns ∈ b3x0, Impossible goal 3 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK emptyOK b3x0Ok
def table3 : BT (List (List Nat)) := buildBucketsBT wires b3x0
set_option maxRecDepth 200000 in
lemma table3OK : btAll (fun bk => ∀ xs ∈ bk, Impossible goal 3 xs.toFinset) table3 := buildBucketsBT_of_mem b3x0Mem
def b4x0Pools : BT (Option BoundPool) := buildPoolsBT 0 wires roots slices [(7,[])]
def b4x0 : List NodeSpec := [([0,16,61,17,4],[],[0]),([31,0,2,32,4],[],[]),([78,0,1,2,4],[],[]),([49,0,1,3,4],[],[]),([43,0,1,2,80],[0],[]),([83,0,1,2,26],[0],[]),([77,0,1,25,27],[],[]),([34,0,16,17,4],[],[0]),([75,1,2,3,4],[],[]),([34,35,0,1,2],[],[]),([35,0,1,2,32],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b4x0Ok : checkNodesBT wires goal (fullMask 41) b4x0Pools autos table3 4 b4x0 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b4x0Mem : ∀ ns ∈ b4x0, Impossible goal 4 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table3OK b4x0Ok
def table4 : BT (List (List Nat)) := buildBucketsBT wires b4x0
set_option maxRecDepth 200000 in
lemma table4OK : btAll (fun bk => ∀ xs ∈ bk, Impossible goal 4 xs.toFinset) table4 := buildBucketsBT_of_mem b4x0Mem
def b5x0Pools : BT (Option BoundPool) := buildPoolsBT 5 wires roots slices [(1,[]),(8,[]),(0,[]),(9,[]),(4,[]),(0,[(0,0,3),(0,54,2)]),(0,[(2,2,3),(1,58,4)]),(5,[]),(6,[]),(7,[]),(3,[]),(1,[(1,0,3),(0,16,13)]),(2,[]),(0,[(0,0,3),(1,12,16)]),(0,[(0,2,3),(1,2,3)]),(0,[(0,0,3),(3,12,4)]),(0,[(2,3,4),(3,28,16)]),(0,[(0,0,2),(1,29,3)])]
def b5x0 : List NodeSpec := [([71,0,16,2,3,4],[0],[]),([5,8,16,3,4],[1,2,0,3],[]),([0,1,2,88,3,4],[],[]),([95,0,1,2,3,4],[4],[]),([55,0,1,2,3,4],[5],[]),([34,0,16,1,2,4],[],[0]),([50,0,1,2,3,4],[],[]),([0,16,1,2,3,79],[6],[]),([0,19,1,25,2,27],[7],[0,3]),([0,19,1,85,2,4],[2],[]),([72,0,1,2,3,4],[7,4,8],[]),([30,36,1,2,3,4],[],[0]),([29,0,1,2,32,4],[7,9],[0,1]),([0,64,39,2,3,4],[10,1,11],[]),([77,0,1,25,3,4],[4],[0]),([5,0,52,2,3,4],[10,4],[]),([45,0,1,2,3,4],[0],[]),([0,1,60,2,3,4],[12,13],[]),([18,0,39,2,3,4],[12],[]),([0,42,1,2,63,4],[14],[0]),([70,0,1,2,3,4],[12],[]),([59,0,16,1,2,3],[15],[]),([0,16,39,2,3,4],[0,10,1],[]),([0,56,1,2,3,4],[7],[]),([0,87,1,2,3,4],[10,16],[]),([5,51,1,2,3,4],[1,2,3],[]),([30,29,1,2,3,4],[2],[]),([31,29,0,2,3,4],[2],[0,2]),([46,0,1,2,3,4],[7],[]),([90,0,1,2,3,4],[],[]),([33,5,8,1,3,4],[12],[]),([0,16,1,2,32,4],[17],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b5x0Ok : checkNodesBT wires goal (fullMask 41) b5x0Pools autos table4 5 b5x0 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b5x0Mem : ∀ ns ∈ b5x0, Impossible goal 5 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table4OK b5x0Ok
def b5x1Pools : BT (Option BoundPool) := buildPoolsBT 5 wires roots slices [(0,[]),(1,[]),(0,[(1,0,2),(2,44,3)]),(7,[]),(3,[]),(0,[(2,2,3),(3,58,4)]),(0,[(1,0,3),(3,16,13)]),(5,[]),(0,[(3,2,3),(1,43,4)]),(0,[(2,3,4),(1,28,16)]),(1,[(1,0,3),(0,16,13)]),(1,[(0,0,1),(1,29,3)]),(0,[(1,0,3),(2,13,4)]),(0,[(1,0,3),(0,16,13)]),(4,[]),(2,[]),(0,[(0,3,4),(1,3,4)]),(6,[]),(8,[]),(0,[(1,0,3),(0,13,4)]),(0,[(3,2,3),(3,43,4)])]
def b5x1 : List NodeSpec := [([30,5,16,2,3,4],[0],[]),([33,5,0,16,3,4],[1,0],[]),([76,0,16,1,2,4],[2],[]),([69,0,39,2,3,4],[],[]),([58,43,0,1,2,4],[3],[0]),([0,16,1,61,2,4],[],[0]),([0,16,1,2,3,80],[4,5],[0]),([65,0,1,2,3,4],[6],[]),([91,0,1,2,3,4],[],[]),([12,0,1,62,2,4],[3],[]),([0,16,1,2,3,81],[7,3,8],[]),([0,86,1,2,3,4],[7,9],[]),([0,39,2,66,3,4],[10],[]),([5,0,1,2,32,4],[11],[1]),([68,0,16,1,2,3],[12],[]),([93,0,1,2,3,4],[],[]),([0,64,1,2,3,4],[4,13],[]),([83,0,1,2,3,4],[4,14],[0]),([29,1,44,2,3,4],[],[0]),([5,8,0,16,3,4],[15,0],[]),([0,16,1,2,26,27],[3,7,16],[0]),([23,54,0,1,2,4],[],[]),([77,0,1,2,4,27],[17],[0]),([31,5,0,2,3,4],[0],[]),([5,0,47,2,3,4],[15],[]),([5,16,44,2,3,4],[0],[]),([0,84,1,2,3,4],[],[]),([0,16,1,2,3,67],[4,18,19],[]),([73,0,1,2,3,4],[],[]),([0,16,82,1,2,3],[20],[]),([70,0,39,2,3,4],[],[]),([48,0,1,2,3,4],[1,4,14],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b5x1Ok : checkNodesBT wires goal (fullMask 41) b5x1Pools autos table4 5 b5x1 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b5x1Mem : ∀ ns ∈ b5x1, Impossible goal 5 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table4OK b5x1Ok
def b5x2Pools : BT (Option BoundPool) := buildPoolsBT 3 wires roots slices [(5,[]),(7,[]),(0,[(0,0,3),(1,12,4)]),(3,[]),(1,[])]
def b5x2 : List NodeSpec := [([0,16,1,2,3,57],[0,1,2],[]),([89,0,1,2,3,4],[],[]),([34,29,0,1,2,4],[3],[0,2]),([0,16,52,2,3,4],[4],[]),([0,1,74,2,3,4],[],[]),([23,33,0,1,3,4],[0],[]),([92,0,1,2,3,4],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b5x2Ok : checkNodesBT wires goal (fullMask 41) b5x2Pools autos table4 5 b5x2 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b5x2Mem : ∀ ns ∈ b5x2, Impossible goal 5 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table4OK b5x2Ok
def table5 : BT (List (List Nat)) := buildBucketsBT wires (b5x0 ++ (b5x1 ++ b5x2))
set_option maxRecDepth 200000 in
lemma table5OK : btAll (fun bk => ∀ xs ∈ bk, Impossible goal 5 xs.toFinset) table5 := buildBucketsBT_of_mem (forall_append b5x0Mem (forall_append b5x1Mem b5x2Mem))
def b6x0Pools : BT (Option BoundPool) := buildPoolsBT 6 wires roots slices [(8,[]),(7,[]),(0,[(0,0,3),(1,12,4)]),(1,[(0,0,3),(1,12,4)]),(0,[(2,0,2)]),(2,[]),(1,[]),(0,[(1,3,4)]),(3,[]),(0,[(1,0,3)]),(5,[]),(9,[]),(4,[]),(0,[]),(6,[]),(0,[(0,0,3)]),(0,[(2,0,3)]),(0,[(0,0,2)]),(1,[(2,0,1)]),(1,[(0,0,1)]),(0,[(3,0,2)]),(0,[(1,2,3)]),(0,[(0,3,4)]),(0,[(0,2,3)]),(1,[(2,1,3)]),(1,[(0,1,3)]),(0,[(2,2,3)]),(1,[(3,0,1)]),(0,[(3,0,3)]),(0,[(2,3,4)]),(0,[(0,0,3),(3,12,4)]),(1,[(0,0,3),(3,12,4)]),(1,[(2,3,4),(3,28,1)]),(0,[(1,0,2)])]
def b6x0 : List NodeSpec := [([0,1,2,3,57],[0,1,2,3],[0]),([30,0,16,1,2,3,4],[4,5,6],[0,1]),([0,19,1,2,4,27],[0,1,7],[0]),([0,16,1,2,3,13,4],[8,9,10,6],[0,1]),([5,0,1,2,3,4,27],[0,8,11,12,13],[0]),([40,0,1,2,3,4],[0,8,6,14,12,15],[0,1]),([14,0,16,1,2,3,4],[8,0,16],[]),([5,8,0,1,2,3,4],[17,5,6],[0,1]),([23,0,19,1,2,4],[0,1,13,6],[]),([30,0,1,2,3,4],[4,18,10,8,14,12,17],[0]),([36,0,16,1,2,3,4],[17,5,19,20],[0]),([38,5,0,1,2,3,4],[0,8,15],[]),([20,12,0,1,2,4],[1,10,5,13],[0,1]),([12,0,16,1,2,3,4],[10,8,15],[0]),([23,5,0,1,2,3,4],[8,0,13,6],[0]),([0,16,1,2,3,63,4],[8,10,21],[0]),([0,52,1,2,3,4],[7,8,12,5,6],[0,1,3]),([0,16,1,2,26,3,4],[1,10,14,22],[0]),([0,1,62,2,3,4],[1,23,5,24],[0,1]),([58,0,16,1,2,3,4],[25,8,23,26],[0]),([29,0,16,1,2,3,4],[27,20,17],[0,2]),([71,0,1,2,3,4],[11,10,6,28],[0]),([28,0,16,1,2,3,4],[12,10,8,14,29],[0]),([59,0,1,2,3],[0,14,30,31],[0]),([0,39,2,3,4],[1,5],[0]),([0,94,1,2,3,4],[0,1,32],[0]),([0,16,1,44,2,3,4],[4,5,6,33],[0,1,2]),([15,0,16,1,2,3,4],[10,28,6,8],[0,1]),([29,0,1,2,3,4],[10,8,14,12,4,17,20],[0,1,2]),([5,8,1,2,3,4],[19,17,0,11],[0,1]),([5,0,16,2,3,4],[19,0,13,11],[0]),([0,39,1,2,3,4],[1,5,6,9],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b6x0Ok : checkNodesBT wires goal (fullMask 41) b6x0Pools autos table5 6 b6x0 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b6x0Mem : ∀ ns ∈ b6x0, Impossible goal 6 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table5OK b6x0Ok
def b6x1Pools : BT (Option BoundPool) := buildPoolsBT 5 wires roots slices [(0,[(2,0,2)]),(8,[]),(9,[]),(1,[(0,0,1)]),(0,[(1,0,2)]),(3,[]),(1,[(0,0,3),(3,12,1)]),(6,[]),(4,[]),(2,[]),(0,[(1,0,3),(2,13,4)]),(1,[(1,0,3),(2,13,4)]),(0,[(3,0,2)]),(5,[]),(1,[]),(0,[]),(1,[(2,1,3)]),(0,[(2,2,3)]),(0,[(0,2,3)]),(7,[]),(0,[(0,3,4),(1,3,4)]),(1,[(0,3,4),(1,3,4)]),(1,[(0,1,3)]),(0,[(1,3,4)]),(0,[(1,0,3),(0,13,4)]),(1,[(1,0,3),(0,13,4)]),(0,[(0,0,2)]),(0,[(3,2,3)])]
def b6x1 : List NodeSpec := [([29,5,0,1,2,3,4],[0,1,2,3],[0,1,2]),([11,5,1,2,3,4],[1,3,2,4],[]),([5,0,1,2,3,37,4],[1,5],[]),([54,0,1,2,3,4],[1,6,7,8],[0]),([68,0,1,2,3],[9,8,5,10,11],[0]),([33,0,1,2,3,4],[3,12,13,5,7,8],[0,1,2]),([0,19,1,25,2,3,4],[13,7,14,8,15,5],[0,3]),([0,42,16,1,2,3,4],[16,13,17,18],[0]),([51,0,1,2,3,4],[1,5,8,15,14,2],[0,1]),([0,1,2,26,27],[1,19,20,21],[0]),([33,5,0,1,2,3,4],[3,15,9],[0,1]),([77,0,1,2,3,4],[1,17,7,8,22],[0]),([0,16,1,2,3,4,27],[5,23,13,7,8,14],[0,1]),([0,1,2,3,67],[9,7,5,24,25],[0]),([0,53,1,2,3,4],[1,2,26],[]),([43,0,16,1,2,3,4],[5,13,27],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b6x1Ok : checkNodesBT wires goal (fullMask 41) b6x1Pools autos table5 6 b6x1 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b6x1Mem : ∀ ns ∈ b6x1, Impossible goal 6 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table5OK b6x1Ok
def table6 : BT (List (List Nat)) := buildBucketsBT wires (b6x0 ++ b6x1)
set_option maxRecDepth 200000 in
lemma table6OK : btAll (fun bk => ∀ xs ∈ bk, Impossible goal 6 xs.toFinset) table6 := buildBucketsBT_of_mem (forall_append b6x0Mem b6x1Mem)
def b7x0Pools : BT (Option BoundPool) := buildPoolsBT 5 wires roots slices [(3,[]),(4,[]),(8,[]),(0,[(1,3,4)]),(1,[(1,3,4)]),(9,[]),(7,[]),(0,[]),(1,[(2,1,3)]),(1,[(0,1,3)]),(6,[]),(2,[]),(0,[(1,0,3)]),(1,[]),(1,[(1,0,3)]),(0,[(2,0,3)]),(1,[(2,0,3)]),(0,[(0,0,3)]),(1,[(0,0,3)]),(0,[(0,3,4)]),(1,[(0,3,4)]),(0,[(2,3,4)]),(1,[(2,3,4)]),(5,[]),(0,[(3,0,3)]),(1,[(3,0,3)]),(1,[(0,0,1)])]
def b7x0 : List NodeSpec := [([0,1,2,3,4,27],[0,1,2,3,4,5],[0,1,2,3]),([20,0,1,2,3,4],[6,7,2,8],[0,1]),([0,19,1,2,3,4],[2,7,6,9,10],[0]),([0,1,2,3,13,4],[6,11,12,13,7,14],[0,1]),([14,0,1,2,3,4],[6,2,15,16],[0]),([7,0,1,2,3,4],[2,7,5,13],[0,1]),([12,0,1,2,3,4],[2,5,6,17,18],[0,1]),([0,1,2,26,3,4],[2,6,19,20],[0]),([28,0,1,2,3,4],[2,6,21,22],[0,1]),([15,0,1,2,3,4],[5,23,24,25],[0,1]),([0,16,1,2,3,4],[7,13,11,23,0,10,1],[0,1,2]),([5,0,1,2,3,4],[2,7,5,26,0,1],[0,2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b7x0Ok : checkNodesBT wires goal (fullMask 41) b7x0Pools autos table6 7 b7x0 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b7x0Mem : ∀ ns ∈ b7x0, Impossible goal 7 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table6OK b7x0Ok
def table7 : BT (List (List Nat)) := buildBucketsBT wires b7x0
set_option maxRecDepth 200000 in
lemma table7OK : btAll (fun bk => ∀ xs ∈ bk, Impossible goal 7 xs.toFinset) table7 := buildBucketsBT_of_mem b7x0Mem
def b8x0Pools : BT (Option BoundPool) := buildPoolsBT 1 wires roots slices [(0,[]),(1,[])]
def b8x0 : List NodeSpec := [([0,1,2,3,4],[0,1],[0,1,2,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b8x0Ok : checkNodesBT wires goal (fullMask 41) b8x0Pools autos table7 8 b8x0 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b8x0Mem : ∀ ns ∈ b8x0, Impossible goal 8 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table7OK b8x0Ok
def table8 : BT (List (List Nat)) := buildBucketsBT wires b8x0
set_option maxRecDepth 200000 in
lemma table8OK : btAll (fun bk => ∀ xs ∈ bk, Impossible goal 8 xs.toFinset) table8 := buildBucketsBT_of_mem b8x0Mem
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lower : Lower roots goal 9 := lower_of_forestBT (essPairs := [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11),(VAR 4,3,19)]) (by decide +kernel) table8OK (by decide +kernel)
end F6
namespace F7
def roots : List Nat := varsOf 15
def goal : Nat := 0xe880e880e880e880e880e880e880e880
def pos : List Nat := [7,7,7,11,11,11,13,13,13,14,14,14]
def neg : List Nat := [3,5,6,3,9,10,5,9,12,6,10,12]
def base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x1ff,0xdb),(0xcccccccccccccccccccccccccccccccc,0xe3f,0x62d),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xfc7,0xb46),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xff8,0xdb0)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma pairsOK : goodPairs goal pos neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma baseOK : ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
def wires : BT Decor := buildWiresBT 4 base [(0,0,1),(0,0,2),(0,1,2),(0,4,2),(3,7,3),(3,4,2)]
set_option maxRecDepth 200000 in
lemma wiresOK : btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) wires := buildWiresBT_faithful baseOK
def alist : List (List (Nat × Nat)) := [[],[(0,1)],[(0,2)],[(0,3)],[(1,2)],[(1,3)],[(2,3)],[(0,2),(0,1)],[(0,3),(0,1)],[(1,2),(0,1)],[(1,3),(0,1)],[(2,3),(0,1)],[(0,3),(0,2)],[(1,3),(0,2)],[(2,3),(0,2)],[(1,2),(0,3)],[(1,3),(1,2)],[(2,3),(1,2)],[(0,3),(0,2),(0,1)],[(1,3),(0,2),(0,1)],[(2,3),(0,2),(0,1)],[(1,2),(0,3),(0,1)],[(1,3),(1,2),(0,1)],[(2,3),(1,2),(0,1)]]
def autos : BT (List (Nat × Nat)) := btOfList 5 alist
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma autosOK : btAll (fun sw => swapsValid sw = true ∧ permWord sw goal = goal) autos := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl0 : Slice roots goal (subcubeFast 0 1) 4 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 14)) (qGoal := 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0) (by decide +kernel) (carry_of (swaps := [(2,3),(1,2),(0,1)]) (by decide +kernel) F1.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl1 : Slice roots goal (subcubeFast 0 2) 4 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 13)) (qGoal := 0xfaa0faa0faa0faa0faa0faa0faa0faa0) (by decide +kernel) (carry_of (swaps := [(2,3),(1,2)]) (by decide +kernel) F1.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl2 : Slice roots goal (subcubeFast 0 4) 4 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 11)) (qGoal := 0xee88ee88ee88ee88ee88ee88ee88ee88) (by decide +kernel) (carry_of (swaps := [(2,3)]) (by decide +kernel) F1.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl3 : Slice roots goal (subcubeFast 0 8) 4 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 7)) (qGoal := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8) (by decide +kernel) (carry_of (swaps := []) (by decide +kernel) F1.lower)
def sliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,4),some (subcubeFast 0 2,4),some (subcubeFast 0 4,4),some (subcubeFast 0 8,4)]
def slices : BT (Option (Nat × Nat)) := btOfList 2 sliceList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma slicesOK : btAll (fun o => ∀ p, o = some p → Slice roots goal p.1 p.2) slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice roots goal p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl0) (forall_cons (fun _ h => by cases h; exact sl1) (forall_cons (fun _ h => by cases h; exact sl2) (forall_cons (fun _ h => by cases h; exact sl3) (fun _ h => by cases h)))))
def empty : BT (List (List Nat)) := BT.empty
lemma emptyOK : btAll (fun bk => ∀ xs ∈ bk, Impossible goal (3-1) xs.toFinset) empty := trivial
def b3x0Pools : BT (Option BoundPool) := buildPoolsBT 1 wires roots slices [(1,[]),(0,[])]
def b3x0 : List NodeSpec := [([4,5,6,3],[0,1],[]),([8,0,1,2],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b3x0Ok : checkNodesBT wires goal (fullMask 12) b3x0Pools autos empty 3 b3x0 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b3x0Mem : ∀ ns ∈ b3x0, Impossible goal 3 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK emptyOK b3x0Ok
def table3 : BT (List (List Nat)) := buildBucketsBT wires b3x0
set_option maxRecDepth 200000 in
lemma table3OK : btAll (fun bk => ∀ xs ∈ bk, Impossible goal 3 xs.toFinset) table3 := buildBucketsBT_of_mem b3x0Mem
def b4x0Pools : BT (Option BoundPool) := buildPoolsBT 2 wires roots slices [(3,[]),(1,[]),(2,[])]
def b4x0 : List NodeSpec := [([7,0,1,2,3],[0],[0]),([4,5,1,2,3],[1,2],[0]),([9,0,1,2,3],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b4x0Ok : checkNodesBT wires goal (fullMask 12) b4x0Pools autos table3 4 b4x0 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b4x0Mem : ∀ ns ∈ b4x0, Impossible goal 4 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table3OK b4x0Ok
def table4 : BT (List (List Nat)) := buildBucketsBT wires b4x0
set_option maxRecDepth 200000 in
lemma table4OK : btAll (fun bk => ∀ xs ∈ bk, Impossible goal 4 xs.toFinset) table4 := buildBucketsBT_of_mem b4x0Mem
def b5x0Pools : BT (Option BoundPool) := buildPoolsBT 2 wires roots slices [(0,[]),(1,[]),(2,[]),(3,[])]
def b5x0 : List NodeSpec := [([4,0,1,2,3],[0,1,2,3],[0,1,6,11])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b5x0Ok : checkNodesBT wires goal (fullMask 12) b5x0Pools autos table4 5 b5x0 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b5x0Mem : ∀ ns ∈ b5x0, Impossible goal 5 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table4OK b5x0Ok
def table5 : BT (List (List Nat)) := buildBucketsBT wires b5x0
set_option maxRecDepth 200000 in
lemma table5OK : btAll (fun bk => ∀ xs ∈ bk, Impossible goal 5 xs.toFinset) table5 := buildBucketsBT_of_mem b5x0Mem
def b6x0Pools : BT (Option BoundPool) := buildPoolsBT 2 wires roots slices [(0,[]),(1,[]),(2,[]),(3,[])]
def b6x0 : List NodeSpec := [([0,1,2,3],[0,1,2,3],[0,2,3,4,5,13])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b6x0Ok : checkNodesBT wires goal (fullMask 12) b6x0Pools autos table5 6 b6x0 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b6x0Mem : ∀ ns ∈ b6x0, Impossible goal 6 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table5OK b6x0Ok
def table6 : BT (List (List Nat)) := buildBucketsBT wires b6x0
set_option maxRecDepth 200000 in
lemma table6OK : btAll (fun bk => ∀ xs ∈ bk, Impossible goal 6 xs.toFinset) table6 := buildBucketsBT_of_mem b6x0Mem
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lower : Lower roots goal 7 := lower_of_forestBT (essPairs := [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11)]) (by decide +kernel) table6OK (by decide +kernel)
end F7
namespace F8
def roots : List Nat := varsOf 15
def goal : Nat := 0xeac8eac8eac8eac8eac8eac8eac8eac8
def pos : List Nat := [3,3,6,6,9,9,13,13,14]
def neg : List Nat := [1,2,2,4,1,8,5,12,12]
def base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf3,0x51),(0xcccccccccccccccccccccccccccccccc,0x10f,0x6),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x1cc,0x1c8),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x1f0,0x1a0)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma pairsOK : goodPairs goal pos neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma baseOK : ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
def wires : BT Decor := buildWiresBT 2 base []
set_option maxRecDepth 200000 in
lemma wiresOK : btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) wires := buildWiresBT_faithful baseOK
def alist : List (List (Nat × Nat)) := [[],[(2,3),(0,1)]]
def autos : BT (List (Nat × Nat)) := btOfList 1 alist
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma autosOK : btAll (fun sw => swapsValid sw = true ∧ permWord sw goal = goal) autos := btAll_ofList (autos_of (by decide +kernel))
def sliceList : List (Option (Nat × Nat)) := []
def slices : BT (Option (Nat × Nat)) := btOfList 1 sliceList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma slicesOK : btAll (fun o => ∀ p, o = some p → Slice roots goal p.1 p.2) slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice roots goal p.1 p.2) (fun _ h => by cases h)
def empty : BT (List (List Nat)) := BT.empty
lemma emptyOK : btAll (fun bk => ∀ xs ∈ bk, Impossible goal (3-1) xs.toFinset) empty := trivial
def b3x0Pools : BT (Option BoundPool) := buildPoolsBT 1 wires roots slices []
def b3x0 : List NodeSpec := [([0,1,2,3],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b3x0Ok : checkNodesBT wires goal (fullMask 9) b3x0Pools autos empty 3 b3x0 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b3x0Mem : ∀ ns ∈ b3x0, Impossible goal 3 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK emptyOK b3x0Ok
def table3 : BT (List (List Nat)) := buildBucketsBT wires b3x0
set_option maxRecDepth 200000 in
lemma table3OK : btAll (fun bk => ∀ xs ∈ bk, Impossible goal 3 xs.toFinset) table3 := buildBucketsBT_of_mem b3x0Mem
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lower : Lower roots goal 4 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,2,6),(VAR 3,1,9)]) (by decide +kernel) table3OK (by decide +kernel)
end F8
namespace F9
def roots : List Nat := varsOf 31
def goal : Nat := 0xeac8e880eac8e880eac8e880eac8e880
def pos : List Nat := [7,7,7,11,11,11,13,13,13,14,14,14,19,19,19,22,22,22,25,25,25,23,29,29,30,30,7,7,7,11,11,13,13,14,19,19,22,22,22,25,25,25]
def neg : List Nat := [3,5,6,3,9,10,5,9,12,6,10,12,3,17,18,6,18,20,9,17,24,21,21,28,26,28,1,2,4,1,2,1,4,28,1,26,21,26,28,1,26,28]
def base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x38dfcfc71ff,0x94a46c30db),(0xcccccccccccccccccccccccccccccccc,0x7e7f23fe3f,0x1284901d62d),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x739fe38fc7,0x25312e28b46),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x383e3dc0ff8,0x36a03940db0),(0xffff0000ffff0000ffff0000ffff0000,0x3fc03fff000,0x37a03fb6000)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma pairsOK : goodPairs goal pos neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma baseOK : ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
def wires : BT Decor := buildWiresBT 7 base [(0,0,1),(1,0,1),(2,0,1),(0,0,2),(1,0,2),(2,0,2),(3,0,2),(0,0,3),(1,0,3),(2,0,3),(3,0,3),(2,1,2),(0,1,3),(1,1,3),(2,1,3),(3,1,3),(0,2,3),(1,2,3),(2,2,3),(1,5,2),(2,5,2),(0,1,24),(3,25,0),(3,14,1),(0,5,22),(3,5,22),(0,0,22),(0,6,2),(2,6,2),(2,6,4),(3,8,1),(0,0,18),(1,8,4),(3,17,37),(0,18,37),(0,1,37),(1,40,3),(3,40,3),(3,1,37),(0,3,37),(3,3,37),(1,8,17),(3,8,18),(2,18,4),(1,20,8),(0,26,3),(1,50,4),(1,26,3),(2,52,4),(2,26,3),(3,26,3),(3,1,9),(0,9,3),(2,9,3),(0,9,18),(2,9,4),(3,20,9),(3,11,1),(1,20,11),(0,1,13),(1,14,16),(1,15,4),(1,21,4),(3,31,1),(3,23,1)]
set_option maxRecDepth 200000 in
lemma wiresOK : btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) wires := buildWiresBT_faithful baseOK
def alist : List (List (Nat × Nat)) := [[],[(2,3),(0,1)]]
def autos : BT (List (Nat × Nat)) := btOfList 1 alist
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma autosOK : btAll (fun sw => swapsValid sw = true ∧ permWord sw goal = goal) autos := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl0 : Slice roots goal (subcubeFast 16 0) 7 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 15)) (qGoal := 0xe880e880e880e880e880e880e880e880) (by decide +kernel) (carry_of (swaps := []) (by decide +kernel) F7.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl1 : Slice roots goal (subcubeFast 0 1) 5 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 30)) (qGoal := 0xffccfcc0ffccfcc0ffccfcc0ffccfcc0) (by decide +kernel) (dualLower (G := 0xfcc0cc00fcc0cc00fcc0cc00fcc0cc00) (by decide +kernel) (by decide +kernel) (carry_of (swaps := [(3,4),(1,2),(2,3),(1,2),(0,1)]) (by decide +kernel) F2.lower))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl2 : Slice roots goal (subcubeFast 0 2) 5 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 29)) (qGoal := 0xfafafaa0fafafaa0fafafaa0fafafaa0) (by decide +kernel) (dualLower (G := 0xfaa0a0a0faa0a0a0faa0a0a0faa0a0a0) (by decide +kernel) (by decide +kernel) (carry_of (swaps := [(3,4),(2,3),(1,2)]) (by decide +kernel) F2.lower))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl3 : Slice roots goal (subcubeFast 0 4) 5 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 27)) (qGoal := 0xeeccee88eeccee88eeccee88eeccee88) (by decide +kernel) (dualLower (G := 0xee88cc88ee88cc88ee88cc88ee88cc88) (by decide +kernel) (by decide +kernel) (carry_of (swaps := [(3,4),(2,3),(0,1)]) (by decide +kernel) F4.lower))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl4 : Slice roots goal (subcubeFast 0 8) 5 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 23)) (qGoal := 0xeaeae8e8eaeae8e8eaeae8e8eaeae8e8) (by decide +kernel) (dualLower (G := 0xe8e8a8a8e8e8a8a8e8e8a8a8e8e8a8a8) (by decide +kernel) (by decide +kernel) (carry_of (swaps := [(3,4)]) (by decide +kernel) F4.lower))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl5 : Slice roots goal (subcubeFast 4 0) 5 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 27)) (qGoal := 0xaa888800aa888800aa888800aa888800) (by decide +kernel) (carry_of (swaps := [(3,4),(2,3)]) (by decide +kernel) F5.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl6 : Slice roots goal (subcubeFast 8 0) 5 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 23)) (qGoal := 0xc8c88080c8c88080c8c88080c8c88080) (by decide +kernel) (carry_of (swaps := [(3,4),(0,1)]) (by decide +kernel) F5.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl7 : Slice roots goal (subcubeFast 0 16) 4 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 15)) (qGoal := 0xeac8eac8eac8eac8eac8eac8eac8eac8) (by decide +kernel) (carry_of (swaps := []) (by decide +kernel) F8.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl8 : Slice roots goal (subcubeFast 4 1) 4 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 26)) (qGoal := 0xffcccc00ffcccc00ffcccc00ffcccc00) (by decide +kernel) (carry_of (swaps := [(2,3),(3,4),(1,2),(2,3),(0,1)]) (by decide +kernel) F1.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl9 : Slice roots goal (subcubeFast 8 2) 4 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 21)) (qGoal := 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0) (by decide +kernel) (carry_of (swaps := [(2,3),(3,4),(1,2)]) (by decide +kernel) F1.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl10 : Slice roots goal (subcubeFast 16 1) 4 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 14)) (qGoal := 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0) (by decide +kernel) (carry_of (swaps := [(2,3),(1,2),(0,1)]) (by decide +kernel) F1.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl11 : Slice roots goal (subcubeFast 16 2) 4 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 13)) (qGoal := 0xfaa0faa0faa0faa0faa0faa0faa0faa0) (by decide +kernel) (carry_of (swaps := [(2,3),(1,2)]) (by decide +kernel) F1.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl12 : Slice roots goal (subcubeFast 16 4) 4 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 11)) (qGoal := 0xee88ee88ee88ee88ee88ee88ee88ee88) (by decide +kernel) (carry_of (swaps := [(2,3)]) (by decide +kernel) F1.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl13 : Slice roots goal (subcubeFast 16 8) 4 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 7)) (qGoal := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8) (by decide +kernel) (carry_of (swaps := []) (by decide +kernel) F1.lower)
def sliceList : List (Option (Nat × Nat)) := [some (subcubeFast 16 0,7),some (subcubeFast 0 1,5),some (subcubeFast 0 2,5),some (subcubeFast 0 4,5),some (subcubeFast 0 8,5),some (subcubeFast 4 0,5),some (subcubeFast 8 0,5),some (subcubeFast 0 16,4),some (subcubeFast 4 1,4),some (subcubeFast 8 2,4),some (subcubeFast 16 1,4),some (subcubeFast 16 2,4),some (subcubeFast 16 4,4),some (subcubeFast 16 8,4)]
def slices : BT (Option (Nat × Nat)) := btOfList 4 sliceList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma slicesOK : btAll (fun o => ∀ p, o = some p → Slice roots goal p.1 p.2) slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice roots goal p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl0) (forall_cons (fun _ h => by cases h; exact sl1) (forall_cons (fun _ h => by cases h; exact sl2) (forall_cons (fun _ h => by cases h; exact sl3) (forall_cons (fun _ h => by cases h; exact sl4) (forall_cons (fun _ h => by cases h; exact sl5) (forall_cons (fun _ h => by cases h; exact sl6) (forall_cons (fun _ h => by cases h; exact sl7) (forall_cons (fun _ h => by cases h; exact sl8) (forall_cons (fun _ h => by cases h; exact sl9) (forall_cons (fun _ h => by cases h; exact sl10) (forall_cons (fun _ h => by cases h; exact sl11) (forall_cons (fun _ h => by cases h; exact sl12) (forall_cons (fun _ h => by cases h; exact sl13) (fun _ h => by cases h)))))))))))))))
def empty : BT (List (List Nat)) := BT.empty
lemma emptyOK : btAll (fun bk => ∀ xs ∈ bk, Impossible goal (4-1) xs.toFinset) empty := trivial
def b4x0Pools : BT (Option BoundPool) := buildPoolsBT 1 wires roots slices []
def b4x0 : List NodeSpec := [([0,1,2,41,37],[],[]),([36,26,2,3,4],[],[]),([48,0,26,2,3],[],[]),([38,0,1,2,3],[],[]),([53,0,26,2,3],[],[]),([0,1,2,3,39],[],[]),([0,26,2,3,51],[],[]),([35,36,2,3,4],[],[]),([42,0,1,2,37],[],[]),([36,1,2,3,37],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b4x0Ok : checkNodesBT wires goal (fullMask 42) b4x0Pools autos empty 4 b4x0 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b4x0Mem : ∀ ns ∈ b4x0, Impossible goal 4 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK emptyOK b4x0Ok
def table4 : BT (List (List Nat)) := buildBucketsBT wires b4x0
set_option maxRecDepth 200000 in
lemma table4OK : btAll (fun bk => ∀ xs ∈ bk, Impossible goal 4 xs.toFinset) table4 := buildBucketsBT_of_mem b4x0Mem
def b5x0Pools : BT (Option BoundPool) := buildPoolsBT 4 wires roots slices [(8,[]),(3,[]),(10,[]),(7,[]),(1,[]),(4,[]),(0,[]),(9,[]),(11,[]),(2,[]),(12,[]),(5,[])]
def b5x0 : List NodeSpec := [([65,0,1,2,3,4],[],[]),([0,26,2,3,18,4],[0,1,2],[0]),([60,20,0,1,2,3],[],[]),([0,17,1,2,3,37],[3],[0]),([68,0,1,2,3,4],[],[]),([19,0,26,2,3,4],[4],[]),([0,61,1,2,3,4],[4],[]),([0,50,26,2,3,4],[0,1,2],[0,1]),([30,0,1,2,3,4],[],[]),([0,26,2,3,52,4],[0,1,2],[0]),([60,0,1,2,3,18],[2,3,0,1],[1]),([54,0,26,2,3,4],[],[]),([29,0,1,2,3,4],[1,5,3,6],[]),([16,0,1,3,37],[0],[]),([60,19,0,1,2,3],[],[]),([63,0,1,2,3,4],[],[]),([8,36,1,2,3,4],[5,7,8],[0]),([0,1,2,44,3,37],[3],[]),([55,0,26,2,3,4],[],[]),([0,1,46,2,3,4],[3,6],[]),([47,0,1,2,3,4],[9,6,3],[]),([45,0,1,2,3,37],[],[]),([5,27,1,2,3,4],[1],[]),([48,8,0,1,2,3],[8,3],[]),([20,0,1,2,3,37],[10,11],[]),([0,40,1,2,3,37],[],[0]),([35,0,2,3,18,4],[11],[0]),([0,1,2,59,3,4],[9,4,6,3],[]),([43,0,1,2,3,37],[2,11],[]),([0,1,2,3,18,37],[0,10,3],[0]),([19,35,0,2,3,4],[11],[]),([0,49,1,2,3,4],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b5x0Ok : checkNodesBT wires goal (fullMask 42) b5x0Pools autos table4 5 b5x0 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b5x0Mem : ∀ ns ∈ b5x0, Impossible goal 5 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table4OK b5x0Ok
def b5x1Pools : BT (Option BoundPool) := buildPoolsBT 0 wires roots slices [(3,[])]
def b5x1 : List NodeSpec := [([5,31,1,2,3,4],[0],[]),([19,0,1,2,3,37],[],[]),([20,0,26,2,3,4],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b5x1Ok : checkNodesBT wires goal (fullMask 42) b5x1Pools autos table4 5 b5x1 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b5x1Mem : ∀ ns ∈ b5x1, Impossible goal 5 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table4OK b5x1Ok
def table5 : BT (List (List Nat)) := buildBucketsBT wires (b5x0 ++ b5x1)
set_option maxRecDepth 200000 in
lemma table5OK : btAll (fun bk => ∀ xs ∈ bk, Impossible goal 5 xs.toFinset) table5 := buildBucketsBT_of_mem (forall_append b5x0Mem b5x1Mem)
def b6x0Pools : BT (Option BoundPool) := buildPoolsBT 4 wires roots slices [(9,[]),(1,[]),(3,[]),(10,[]),(6,[]),(4,[]),(5,[]),(11,[]),(8,[]),(0,[]),(7,[]),(2,[]),(12,[])]
def b6x0 : List NodeSpec := [([0,1,2,57,4],[0,1,2],[]),([0,26,1,2,3,4],[3,2,4,5],[0,1]),([0,1,32,3,4],[0,1,6],[]),([60,0,1,2,3],[3,2],[0,1]),([20,8,0,1,2,3,4],[6,4,2,5,7],[0]),([14,16,0,1,2,3,4],[2,5,8,4],[0]),([0,28,1,2,3,4],[0,6,2,9,10,5],[1]),([20,11,0,1,2,3,4],[1,11],[0]),([5,0,1,2,3,22,4],[2,6,5,4,1,11],[0,1]),([8,0,1,2,3,18,4],[7,6,3,5,4,2],[0]),([19,8,0,1,2,3,4],[0,5,7],[0]),([20,0,1,2,9,3,4],[7,1,4,5],[0]),([31,0,1,2,3,4],[8,12,11,5],[0]),([0,1,2,3,66],[8,0],[]),([14,5,0,1,2,3,4],[0,5],[1]),([56,0,2,3,4],[0,1,2],[]),([33,0,1,3,4],[0,1,2],[]),([5,0,1,2,24,3,4],[8,2],[]),([8,0,17,1,2,3,4],[6,4,7,3],[0,1]),([0,1,2,9,3,18,4],[7,3,6,2,4,5],[0,1]),([0,1,2,3,67],[8,0],[]),([0,64,1,2,3,4],[8,5,3],[]),([19,0,1,2,9,3,4],[0,5,7],[0]),([0,1,2,3,37],[8,10],[0]),([34,0,1,2,3],[8,0],[]),([10,20,0,1,2,3,4],[8,2],[]),([16,8,0,1,3,4],[6,12,0,1],[0]),([25,5,0,1,2,3,4],[8,2],[0]),([35,0,1,2,3,4],[8,4,5,9,10],[0]),([0,69,1,2,3,4],[8,5,9,10],[]),([0,26,2,3,4],[3,2],[0]),([19,10,0,1,2,3,4],[2,8],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b6x0Ok : checkNodesBT wires goal (fullMask 42) b6x0Pools autos table5 6 b6x0 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b6x0Mem : ∀ ns ∈ b6x0, Impossible goal 6 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table5OK b6x0Ok
def b6x1Pools : BT (Option BoundPool) := buildPoolsBT 3 wires roots slices [(10,[]),(5,[]),(6,[]),(4,[]),(3,[])]
def b6x1 : List NodeSpec := [([62,0,1,2,3,4],[0,1,2,3],[]),([58,0,1,2,4],[0,3,4],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b6x1Ok : checkNodesBT wires goal (fullMask 42) b6x1Pools autos table5 6 b6x1 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b6x1Mem : ∀ ns ∈ b6x1, Impossible goal 6 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table5OK b6x1Ok
def table6 : BT (List (List Nat)) := buildBucketsBT wires (b6x0 ++ b6x1)
set_option maxRecDepth 200000 in
lemma table6OK : btAll (fun bk => ∀ xs ∈ bk, Impossible goal 6 xs.toFinset) table6 := buildBucketsBT_of_mem (forall_append b6x0Mem b6x1Mem)
def b7x0Pools : BT (Option BoundPool) := buildPoolsBT 4 wires roots slices [(10,[]),(2,[]),(8,[]),(6,[]),(4,[]),(0,[]),(0,[(0,0,2)]),(9,[]),(0,[(0,2,3)]),(12,[]),(13,[]),(5,[]),(3,[]),(0,[(0,0,3)]),(11,[]),(0,[(0,0,1)])]
def b7x0 : List NodeSpec := [([0,1,6,2,3,4],[0,1,2,3,4,5],[0,1]),([8,0,1,2,3,4],[2,6,1,4,3],[0]),([0,1,21,2,3,4],[2,7,8],[0]),([0,1,2,3,22,4],[9,7,2,4],[0,1]),([23,0,1,2,3,4],[2,10,1],[0]),([11,0,1,2,3,4],[0,11,1,4,3],[0,1]),([0,1,2,3,13,4],[2,4,0,1],[0]),([14,0,1,2,3,4],[10,2,7,12],[0,1]),([0,1,2,9,3,4],[0,12,1,3,4,5],[0,1]),([12,0,1,2,3,4],[7,2,13,4,12],[]),([15,0,1,2,3,4],[7,0,12,11,5],[0]),([10,0,1,2,3,4],[2,9],[0,1]),([7,0,1,2,3,4],[14,2,7,12,15],[]),([5,0,1,2,3,4],[2,7,15,12,4],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b7x0Ok : checkNodesBT wires goal (fullMask 42) b7x0Pools autos table6 7 b7x0 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b7x0Mem : ∀ ns ∈ b7x0, Impossible goal 7 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table6OK b7x0Ok
def table7 : BT (List (List Nat)) := buildBucketsBT wires b7x0
set_option maxRecDepth 200000 in
lemma table7OK : btAll (fun bk => ∀ xs ∈ bk, Impossible goal 7 xs.toFinset) table7 := buildBucketsBT_of_mem b7x0Mem
def b8x0Pools : BT (Option BoundPool) := buildPoolsBT 0 wires roots slices [(0,[])]
def b8x0 : List NodeSpec := [([0,1,2,3,4],[0],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b8x0Ok : checkNodesBT wires goal (fullMask 42) b8x0Pools autos table7 8 b8x0 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b8x0Mem : ∀ ns ∈ b8x0, Impossible goal 8 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table7OK b8x0Ok
def table8 : BT (List (List Nat)) := buildBucketsBT wires b8x0
set_option maxRecDepth 200000 in
lemma table8OK : btAll (fun bk => ∀ xs ∈ bk, Impossible goal 8 xs.toFinset) table8 := buildBucketsBT_of_mem b8x0Mem
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lower : Lower roots goal 9 := lower_of_forestBT (essPairs := [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11),(VAR 4,3,19)]) (by decide +kernel) table8OK (by decide +kernel)
end F9
namespace RootCert
def roots : List Nat := varsOf 63
def goal : Nat := 0xfee8eac8eac8e880fee8eac8eac8e880
def pos : List Nat := [7,7,11,11,13,14,19,22,25,35,38,41,53,53,53,53,58,58,58,58,60,60,60,60,7,11,13,13,14,14,19,19,22,22,25,25,35,35,38,38,41,41,23,27,29,29,30,30,39,43,45,45,46,51,51,54,54,57,57,7,7,11,13,13,13,14,14,14,19,19,22,22,22,25,35,35,38,41,7,7,7,11,11,13,19,19,22,22,25,25,35,38,41,53,53,53,58,58,60,60]
def neg : List Nat := [3,6,3,9,9,6,3,6,9,3,6,9,21,37,49,52,26,42,50,56,28,44,52,56,5,10,5,12,10,12,17,18,18,20,17,24,33,34,34,36,33,40,21,26,21,28,26,28,37,42,37,44,44,49,50,50,52,49,56,21,37,26,21,28,37,26,28,42,21,26,21,26,28,28,49,50,50,49,1,2,4,1,2,1,1,2,2,4,1,8,1,2,1,5,33,36,34,40,36,40]
def base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf73fee31fe6f3f3ccf00fb5f,0x751a64515a25151445007b5d),(0xcccccccccccccccccccccccccccccccc,0x30cf7ddfe39f3ccf3f30f06ef,0x1086498aa20c24861920706e7),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xce8c9d1cfd99df4c33df0f4b3,0x4a0810355d91db4822d70b4a2),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xf130e220fe61efb0c3eff093c,0xa020003aea41aea083abb0918),(0xffff0000ffff0000ffff0000ffff0000,0xfe3f003f007e0fc0fc0fff1c0,0x3ff6efe0fc0fc0ddd000),(0xffffffff00000000ffffffff00000000,0xffc003c0007ff03f000fffe00,0xfc0003c0917ff03f000eee000)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma pairsOK : goodPairs goal pos neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma baseOK : ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
def wires : BT Decor := buildWiresBT 9 base [(0,0,1),(1,0,1),(2,0,1),(3,0,1),(0,0,2),(1,0,2),(2,0,2),(3,0,2),(0,0,3),(1,0,3),(2,0,3),(3,0,3),(0,0,4),(1,0,4),(2,0,4),(3,0,4),(0,1,2),(1,1,2),(2,1,2),(3,1,2),(0,1,3),(1,1,3),(2,1,3),(3,1,3),(0,1,4),(1,1,4),(2,1,4),(3,1,4),(1,1,5),(2,1,5),(3,1,5),(0,2,3),(1,2,3),(2,2,3),(3,2,3),(0,2,4),(1,2,4),(2,2,4),(3,2,4),(0,2,5),(1,2,5),(2,2,5),(3,2,5),(0,3,4),(1,3,4),(2,3,4),(3,3,4),(0,3,5),(1,3,5),(2,3,5),(3,3,5),(0,4,5),(1,4,5),(2,4,5),(3,4,5),(1,6,37),(0,61,4),(3,62,61),(3,62,4),(1,61,4),(3,62,65),(1,61,57),(2,61,57),(0,61,58),(3,61,58),(1,59,61),(3,59,61),(1,59,6),(1,59,37),(3,6,38),(1,39,6),(1,6,41),(0,77,3),(3,78,77),(2,77,5),(0,77,54),(3,55,77),(3,6,54),(3,41,54),(1,55,41),(3,6,42),(1,43,6),(1,44,6),(2,7,37),(0,7,38),(0,90,4),(3,91,90),(3,91,4),(1,90,4),(3,91,94),(1,90,57),(2,90,57),(0,90,58),(3,90,58),(1,59,90),(3,59,90),(3,59,7),(3,59,38),(3,39,7),(2,7,41),(0,7,54),(1,106,41),(0,7,42),(1,108,3),(3,108,3),(3,108,5),(1,56,108),(3,56,42),(3,43,7),(3,44,7),(1,8,37),(3,8,38),(1,39,8),(1,40,8),(1,8,41),(3,8,54),(3,8,42),(1,8,53),(1,43,8),(1,44,8),(1,8,49),(3,8,50),(1,51,8),(1,52,8),(1,59,8),(1,10,26),(0,131,4),(3,132,131),(3,132,4),(1,131,4),(3,132,135),(2,131,57),(1,133,5),(0,131,138),(3,133,5),(1,131,57),(0,131,58),(3,131,58),(1,59,131),(1,1,144),(1,59,10),(3,146,1),(3,10,27),(1,28,10),(1,29,10),(1,59,29),(1,10,30),(1,152,3),(3,152,3),(1,152,5),(3,152,54),(1,55,152),(3,10,54),(3,30,54),(1,55,30),(3,10,31),(1,10,53),(3,53,31),(1,32,10),(1,32,53),(1,33,10),(3,33,54),(1,55,33),(1,10,49),(3,10,50),(1,51,10),(1,52,10),(0,11,27),(0,173,4),(3,174,173),(3,174,4),(1,173,4),(3,174,177),(0,177,5),(2,177,5),(1,173,179),(1,180,173),(2,173,57),(0,173,58),(3,173,58),(3,59,173),(0,186,3),(3,59,11),(2,188,3),(3,28,11),(3,29,11),(3,30,11),(0,11,31),(0,193,3),(3,194,193),(0,193,5),(2,193,53),(3,56,193),(2,11,53),(3,56,31),(3,32,11),(1,32,56),(3,33,11),(2,11,49),(0,11,50),(3,51,11),(3,52,11),(1,28,12),(1,12,29),(1,59,12),(1,12,30),(3,12,31),(1,12,53),(1,32,12),(1,12,33),(1,12,49),(3,12,50),(1,51,12),(1,52,12),(1,29,13),(1,59,13),(1,13,30),(3,13,54),(3,13,31),(1,13,53),(1,32,13),(1,33,13),(1,13,49),(3,13,50),(1,51,13),(1,52,13),(1,14,22),(0,232,4),(3,233,232),(3,233,4),(1,233,5),(1,232,4),(0,232,236),(3,233,5),(3,233,237),(3,59,232),(1,232,57),(2,232,57),(3,232,58),(1,59,232),(1,245,2),(1,59,14),(3,247,2),(3,14,23),(1,24,14),(1,59,24),(1,25,14),(1,14,30),(1,253,2),(3,253,2),(1,253,5),(3,253,46),(1,47,253),(3,14,46),(3,30,46),(1,47,30),(3,14,31),(1,32,14),(1,32,45),(1,32,48),(1,33,14),(3,33,46),(1,47,33),(1,14,41),(3,14,42),(1,43,14),(1,44,14),(0,23,15),(0,273,4),(3,274,273),(3,274,4),(1,273,4),(3,274,277),(3,273,58),(1,276,5),(3,276,5),(1,59,273),(1,273,57),(2,273,57),(0,273,58),(3,59,273),(0,1,286),(3,59,23),(3,59,15),(3,24,15),(3,1,289),(3,25,15),(3,30,15),(0,15,46),(3,45,15),(0,295,31),(3,45,31),(0,15,31),(0,2,298),(3,2,298),(0,298,5),(3,48,31),(0,302,15),(3,32,15),(3,33,15),(3,41,15),(0,15,42),(3,43,15),(3,44,15),(1,16,24),(1,59,16),(1,16,25),(1,59,25),(1,16,30),(3,16,46),(3,16,31),(1,16,45),(1,32,16),(1,16,33),(1,16,41),(3,16,42),(1,43,16),(1,16,44),(1,25,17),(1,17,30),(3,17,46),(3,17,31),(1,32,17),(1,33,17),(1,17,41),(3,17,42),(1,43,17),(1,44,17),(1,59,17),(3,18,34),(1,35,18),(1,18,37),(1,337,5),(1,40,18),(3,18,38),(1,39,18),(3,18,46),(1,47,18),(3,18,54),(1,55,18),(3,36,19),(0,38,19),(0,347,5),(3,40,19),(3,37,19),(3,39,19),(3,45,19),(3,48,19),(3,53,19),(3,56,19),(1,20,36),(1,20,37),(3,20,38),(1,20,39),(1,20,40),(1,20,45),(1,20,48),(1,20,53),(1,20,56),(1,21,37),(3,21,38),(1,39,21),(1,40,21),(3,21,46),(1,47,21),(3,21,54),(1,55,21),(1,59,39),(1,43,56)]
set_option maxRecDepth 200000 in
lemma wiresOK : btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) wires := buildWiresBT_faithful baseOK
def alist : List (List (Nat × Nat)) := [[],[(4,5)],[(2,3),(0,1)],[(4,5),(2,3),(0,1)]]
def autos : BT (List (Nat × Nat)) := btOfList 2 alist
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma autosOK : btAll (fun sw => swapsValid sw = true ∧ permWord sw goal = goal) autos := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl0 : Slice roots goal (subcubeFast 0 1) 9 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 62)) (qGoal := 0xfffcffccffccfcc0fffcffccffccfcc0) (by decide +kernel) (dualLower (G := 0xfcc0cc00cc00c000fcc0cc00cc00c000) (by decide +kernel) (by decide +kernel) (carry_of (swaps := [(4,5),(3,4),(1,2),(2,3),(1,2),(0,1)]) (by decide +kernel) F3.lower))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl1 : Slice roots goal (subcubeFast 0 2) 9 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 61)) (qGoal := 0xfffafafafafafaa0fffafafafafafaa0) (by decide +kernel) (dualLower (G := 0xfaa0a0a0a0a0a000faa0a0a0a0a0a000) (by decide +kernel) (by decide +kernel) (carry_of (swaps := [(4,5),(3,4),(2,3),(1,2)]) (by decide +kernel) F3.lower))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl2 : Slice roots goal (subcubeFast 0 4) 9 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 59)) (qGoal := 0xffeeeecceeccee88ffeeeecceeccee88) (by decide +kernel) (dualLower (G := 0xee88cc88cc888800ee88cc88cc888800) (by decide +kernel) (by decide +kernel) (carry_of (swaps := [(4,5),(3,4),(2,3),(0,1)]) (by decide +kernel) F6.lower))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl3 : Slice roots goal (subcubeFast 0 8) 9 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 55)) (qGoal := 0xfefeeaeaeaeae8e8fefeeaeaeaeae8e8) (by decide +kernel) (dualLower (G := 0xe8e8a8a8a8a88080e8e8a8a8a8a88080) (by decide +kernel) (by decide +kernel) (carry_of (swaps := [(4,5),(3,4)]) (by decide +kernel) F6.lower))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl4 : Slice roots goal (subcubeFast 0 16) 9 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 47)) (qGoal := 0xfee8fee8eac8eac8fee8fee8eac8eac8) (by decide +kernel) (dualLower (G := 0xeca8eca8e880e880eca8eca8e880e880) (by decide +kernel) (by decide +kernel) (carry_of (swaps := [(4,5),(0,1)]) (by decide +kernel) F9.lower))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl5 : Slice roots goal (subcubeFast 0 32) 9 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 31)) (qGoal := 0xfee8eac8fee8eac8fee8eac8fee8eac8) (by decide +kernel) (dualLower (G := 0xeca8e880eca8e880eca8e880eca8e880) (by decide +kernel) (by decide +kernel) (carry_of (swaps := [(0,1)]) (by decide +kernel) F9.lower))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl6 : Slice roots goal (subcubeFast 1 0) 9 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 62)) (qGoal := 0xfcc0c0c0c0c0c000fcc0c0c0c0c0c000) (by decide +kernel) (carry_of (swaps := [(4,5),(3,4),(2,3),(1,2),(0,1)]) (by decide +kernel) F3.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl7 : Slice roots goal (subcubeFast 2 0) 9 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 61)) (qGoal := 0xfaa0aa00aa00a000faa0aa00aa00a000) (by decide +kernel) (carry_of (swaps := [(4,5),(3,4),(1,2),(2,3),(1,2)]) (by decide +kernel) F3.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl8 : Slice roots goal (subcubeFast 4 0) 9 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 59)) (qGoal := 0xee88aa88aa888800ee88aa88aa888800) (by decide +kernel) (carry_of (swaps := [(4,5),(3,4),(2,3)]) (by decide +kernel) F6.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl9 : Slice roots goal (subcubeFast 8 0) 9 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 55)) (qGoal := 0xe8e8c8c8c8c88080e8e8c8c8c8c88080) (by decide +kernel) (carry_of (swaps := [(4,5),(3,4),(0,1)]) (by decide +kernel) F6.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl10 : Slice roots goal (subcubeFast 16 0) 9 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 47)) (qGoal := 0xeac8eac8e880e880eac8eac8e880e880) (by decide +kernel) (carry_of (swaps := [(4,5)]) (by decide +kernel) F9.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl11 : Slice roots goal (subcubeFast 32 0) 9 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 31)) (qGoal := 0xeac8e880eac8e880eac8e880eac8e880) (by decide +kernel) (carry_of (swaps := []) (by decide +kernel) F9.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl12 : Slice roots goal (subcubeFast 0 48) 7 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 15)) (qGoal := 0xfee8fee8fee8fee8fee8fee8fee8fee8) (by decide +kernel) (dualLower (G := 0xe880e880e880e880e880e880e880e880) (by decide +kernel) (by decide +kernel) (carry_of (swaps := []) (by decide +kernel) F7.lower))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl13 : Slice roots goal (subcubeFast 48 0) 7 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 15)) (qGoal := 0xe880e880e880e880e880e880e880e880) (by decide +kernel) (carry_of (swaps := []) (by decide +kernel) F7.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl14 : Slice roots goal (subcubeFast 1 2) 6 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 60)) (qGoal := 0xfff0f0f0f0f0f000fff0f0f0f0f0f000) (by decide +kernel) (carry_of (swaps := [(3,4),(4,5),(2,3),(3,4),(1,2),(2,3),(0,1),(1,2)]) (by decide +kernel) F0.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl15 : Slice roots goal (subcubeFast 1 4) 6 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 58)) (qGoal := 0xffcccccccccccc00ffcccccccccccc00) (by decide +kernel) (carry_of (swaps := [(3,4),(4,5),(2,3),(3,4),(1,2),(2,3),(0,1)]) (by decide +kernel) F0.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl16 : Slice roots goal (subcubeFast 2 1) 6 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 60)) (qGoal := 0xfff0ff00ff00f000fff0ff00ff00f000) (by decide +kernel) (carry_of (swaps := [(3,4),(4,5),(2,3),(3,4),(0,1),(1,2),(2,3),(0,1),(1,2)]) (by decide +kernel) F0.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl17 : Slice roots goal (subcubeFast 2 8) 6 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 53)) (qGoal := 0xfafaaaaaaaaaa0a0fafaaaaaaaaaa0a0) (by decide +kernel) (carry_of (swaps := [(3,4),(4,5),(2,3),(3,4),(1,2)]) (by decide +kernel) F0.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl18 : Slice roots goal (subcubeFast 4 2) 6 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 57)) (qGoal := 0xffaaaaaaaaaaaa00ffaaaaaaaaaaaa00) (by decide +kernel) (carry_of (swaps := [(3,4),(4,5),(2,3),(3,4),(1,2),(2,3)]) (by decide +kernel) F0.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl19 : Slice roots goal (subcubeFast 4 8) 6 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 51)) (qGoal := 0xeeeeaaaaaaaa8888eeeeaaaaaaaa8888) (by decide +kernel) (carry_of (swaps := [(3,4),(4,5),(2,3),(3,4)]) (by decide +kernel) F0.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl20 : Slice roots goal (subcubeFast 8 1) 6 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 54)) (qGoal := 0xfcfcccccccccc0c0fcfcccccccccc0c0) (by decide +kernel) (carry_of (swaps := [(3,4),(4,5),(2,3),(3,4),(1,2),(0,1)]) (by decide +kernel) F0.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl21 : Slice roots goal (subcubeFast 8 4) 6 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 51)) (qGoal := 0xeeeecccccccc8888eeeecccccccc8888) (by decide +kernel) (carry_of (swaps := [(3,4),(4,5),(2,3),(3,4),(0,1)]) (by decide +kernel) F0.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl22 : Slice roots goal (subcubeFast 0 20) 5 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 43)) (qGoal := 0xffeeffeeeecceeccffeeffeeeecceecc) (by decide +kernel) (dualLower (G := 0xcc88cc8888008800cc88cc8888008800) (by decide +kernel) (by decide +kernel) (carry_of (swaps := [(3,4),(4,5),(2,3),(0,1)]) (by decide +kernel) F5.lower))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl23 : Slice roots goal (subcubeFast 0 24) 5 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 39)) (qGoal := 0xfefefefeeaeaeaeafefefefeeaeaeaea) (by decide +kernel) (dualLower (G := 0xa8a8a8a880808080a8a8a8a880808080) (by decide +kernel) (by decide +kernel) (carry_of (swaps := [(3,4),(4,5)]) (by decide +kernel) F5.lower))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl24 : Slice roots goal (subcubeFast 0 36) 5 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 27)) (qGoal := 0xffeeeeccffeeeeccffeeeeccffeeeecc) (by decide +kernel) (dualLower (G := 0xcc888800cc888800cc888800cc888800) (by decide +kernel) (by decide +kernel) (carry_of (swaps := [(3,4),(2,3),(0,1)]) (by decide +kernel) F5.lower))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl25 : Slice roots goal (subcubeFast 0 40) 5 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 23)) (qGoal := 0xfefeeaeafefeeaeafefeeaeafefeeaea) (by decide +kernel) (dualLower (G := 0xa8a88080a8a88080a8a88080a8a88080) (by decide +kernel) (by decide +kernel) (carry_of (swaps := [(3,4)]) (by decide +kernel) F5.lower))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl26 : Slice roots goal (subcubeFast 1 8) 5 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 54)) (qGoal := 0xfcfcc0c0c0c0c0c0fcfcc0c0c0c0c0c0) (by decide +kernel) (carry_of (swaps := [(3,4),(4,5),(2,3),(3,4),(1,2),(0,1)]) (by decide +kernel) F2.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl27 : Slice roots goal (subcubeFast 1 16) 5 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 46)) (qGoal := 0xfcc0fcc0c0c0c0c0fcc0fcc0c0c0c0c0) (by decide +kernel) (carry_of (swaps := [(3,4),(4,5),(2,3),(1,2),(0,1)]) (by decide +kernel) F2.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl28 : Slice roots goal (subcubeFast 1 32) 5 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 30)) (qGoal := 0xfcc0c0c0fcc0c0c0fcc0c0c0fcc0c0c0) (by decide +kernel) (carry_of (swaps := [(3,4),(2,3),(1,2),(0,1)]) (by decide +kernel) F2.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl29 : Slice roots goal (subcubeFast 2 4) 5 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 57)) (qGoal := 0xffaaaa00aa00aa00ffaaaa00aa00aa00) (by decide +kernel) (carry_of (swaps := [(3,4),(4,5),(2,3),(3,4),(1,2),(2,3)]) (by decide +kernel) F2.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl30 : Slice roots goal (subcubeFast 2 16) 5 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 45)) (qGoal := 0xfaa0faa0aa00aa00faa0faa0aa00aa00) (by decide +kernel) (carry_of (swaps := [(3,4),(4,5),(1,2),(2,3),(1,2)]) (by decide +kernel) F2.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl31 : Slice roots goal (subcubeFast 2 32) 5 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 29)) (qGoal := 0xfaa0aa00faa0aa00faa0aa00faa0aa00) (by decide +kernel) (carry_of (swaps := [(3,4),(1,2),(2,3),(1,2)]) (by decide +kernel) F2.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl32 : Slice roots goal (subcubeFast 4 1) 5 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 58)) (qGoal := 0xffccffccffcccc00ffccffccffcccc00) (by decide +kernel) (dualLower (G := 0xffcccc00cc00cc00ffcccc00cc00cc00) (by decide +kernel) (by decide +kernel) (carry_of (swaps := [(3,4),(4,5),(2,3),(3,4),(1,2),(2,3),(0,1)]) (by decide +kernel) F2.lower))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl33 : Slice roots goal (subcubeFast 4 16) 5 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 43)) (qGoal := 0xee88ee88aa88aa88ee88ee88aa88aa88) (by decide +kernel) (carry_of (swaps := [(3,4),(4,5),(2,3)]) (by decide +kernel) F4.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl34 : Slice roots goal (subcubeFast 4 32) 5 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 27)) (qGoal := 0xee88aa88ee88aa88ee88aa88ee88aa88) (by decide +kernel) (carry_of (swaps := [(3,4),(2,3)]) (by decide +kernel) F4.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl35 : Slice roots goal (subcubeFast 8 2) 5 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 53)) (qGoal := 0xfafafafafafaa0a0fafafafafafaa0a0) (by decide +kernel) (dualLower (G := 0xfafaa0a0a0a0a0a0fafaa0a0a0a0a0a0) (by decide +kernel) (by decide +kernel) (carry_of (swaps := [(3,4),(4,5),(2,3),(3,4),(1,2)]) (by decide +kernel) F2.lower))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl36 : Slice roots goal (subcubeFast 8 16) 5 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 39)) (qGoal := 0xe8e8e8e8c8c8c8c8e8e8e8e8c8c8c8c8) (by decide +kernel) (carry_of (swaps := [(3,4),(4,5),(0,1)]) (by decide +kernel) F4.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl37 : Slice roots goal (subcubeFast 8 32) 5 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 23)) (qGoal := 0xe8e8c8c8e8e8c8c8e8e8c8c8e8e8c8c8) (by decide +kernel) (carry_of (swaps := [(3,4),(0,1)]) (by decide +kernel) F4.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl38 : Slice roots goal (subcubeFast 16 1) 5 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 46)) (qGoal := 0xffccffccfcc0fcc0ffccffccfcc0fcc0) (by decide +kernel) (dualLower (G := 0xfcc0fcc0cc00cc00fcc0fcc0cc00cc00) (by decide +kernel) (by decide +kernel) (carry_of (swaps := [(3,4),(4,5),(1,2),(2,3),(1,2),(0,1)]) (by decide +kernel) F2.lower))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl39 : Slice roots goal (subcubeFast 16 2) 5 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 45)) (qGoal := 0xfafafafafaa0faa0fafafafafaa0faa0) (by decide +kernel) (dualLower (G := 0xfaa0faa0a0a0a0a0faa0faa0a0a0a0a0) (by decide +kernel) (by decide +kernel) (carry_of (swaps := [(3,4),(4,5),(2,3),(1,2)]) (by decide +kernel) F2.lower))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl40 : Slice roots goal (subcubeFast 16 4) 5 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 43)) (qGoal := 0xeecceeccee88ee88eecceeccee88ee88) (by decide +kernel) (dualLower (G := 0xee88ee88cc88cc88ee88ee88cc88cc88) (by decide +kernel) (by decide +kernel) (carry_of (swaps := [(3,4),(4,5),(2,3),(0,1)]) (by decide +kernel) F4.lower))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl41 : Slice roots goal (subcubeFast 16 8) 5 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 39)) (qGoal := 0xeaeaeaeae8e8e8e8eaeaeaeae8e8e8e8) (by decide +kernel) (dualLower (G := 0xe8e8e8e8a8a8a8a8e8e8e8e8a8a8a8a8) (by decide +kernel) (by decide +kernel) (carry_of (swaps := [(3,4),(4,5)]) (by decide +kernel) F4.lower))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl42 : Slice roots goal (subcubeFast 20 0) 5 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 43)) (qGoal := 0xaa88aa8888008800aa88aa8888008800) (by decide +kernel) (carry_of (swaps := [(3,4),(4,5),(2,3)]) (by decide +kernel) F5.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl43 : Slice roots goal (subcubeFast 24 0) 5 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 39)) (qGoal := 0xc8c8c8c880808080c8c8c8c880808080) (by decide +kernel) (carry_of (swaps := [(3,4),(4,5),(0,1)]) (by decide +kernel) F5.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl44 : Slice roots goal (subcubeFast 32 1) 5 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 30)) (qGoal := 0xffccfcc0ffccfcc0ffccfcc0ffccfcc0) (by decide +kernel) (dualLower (G := 0xfcc0cc00fcc0cc00fcc0cc00fcc0cc00) (by decide +kernel) (by decide +kernel) (carry_of (swaps := [(3,4),(1,2),(2,3),(1,2),(0,1)]) (by decide +kernel) F2.lower))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl45 : Slice roots goal (subcubeFast 32 2) 5 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 29)) (qGoal := 0xfafafaa0fafafaa0fafafaa0fafafaa0) (by decide +kernel) (dualLower (G := 0xfaa0a0a0faa0a0a0faa0a0a0faa0a0a0) (by decide +kernel) (by decide +kernel) (carry_of (swaps := [(3,4),(2,3),(1,2)]) (by decide +kernel) F2.lower))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl46 : Slice roots goal (subcubeFast 32 4) 5 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 27)) (qGoal := 0xeeccee88eeccee88eeccee88eeccee88) (by decide +kernel) (dualLower (G := 0xee88cc88ee88cc88ee88cc88ee88cc88) (by decide +kernel) (by decide +kernel) (carry_of (swaps := [(3,4),(2,3),(0,1)]) (by decide +kernel) F4.lower))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl47 : Slice roots goal (subcubeFast 32 8) 5 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 23)) (qGoal := 0xeaeae8e8eaeae8e8eaeae8e8eaeae8e8) (by decide +kernel) (dualLower (G := 0xe8e8a8a8e8e8a8a8e8e8a8a8e8e8a8a8) (by decide +kernel) (by decide +kernel) (carry_of (swaps := [(3,4)]) (by decide +kernel) F4.lower))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl48 : Slice roots goal (subcubeFast 36 0) 5 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 27)) (qGoal := 0xaa888800aa888800aa888800aa888800) (by decide +kernel) (carry_of (swaps := [(3,4),(2,3)]) (by decide +kernel) F5.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl49 : Slice roots goal (subcubeFast 40 0) 5 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 23)) (qGoal := 0xc8c88080c8c88080c8c88080c8c88080) (by decide +kernel) (carry_of (swaps := [(3,4),(0,1)]) (by decide +kernel) F5.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl50 : Slice roots goal (subcubeFast 16 32) 4 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 15)) (qGoal := 0xeac8eac8eac8eac8eac8eac8eac8eac8) (by decide +kernel) (carry_of (swaps := []) (by decide +kernel) F8.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl51 : Slice roots goal (subcubeFast 32 16) 4 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 15)) (qGoal := 0xeac8eac8eac8eac8eac8eac8eac8eac8) (by decide +kernel) (carry_of (swaps := []) (by decide +kernel) F8.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl52 : Slice roots goal (subcubeFast 1 24) 4 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 38)) (qGoal := 0xfcfcfcfcc0c0c0c0fcfcfcfcc0c0c0c0) (by decide +kernel) (carry_of (swaps := [(2,3),(3,4),(4,5),(1,2),(0,1)]) (by decide +kernel) F1.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl53 : Slice roots goal (subcubeFast 1 40) 4 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 22)) (qGoal := 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0) (by decide +kernel) (carry_of (swaps := [(2,3),(3,4),(1,2),(0,1)]) (by decide +kernel) F1.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl54 : Slice roots goal (subcubeFast 1 48) 4 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 14)) (qGoal := 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0) (by decide +kernel) (carry_of (swaps := [(2,3),(1,2),(0,1)]) (by decide +kernel) F1.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl55 : Slice roots goal (subcubeFast 2 20) 4 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 41)) (qGoal := 0xffaaffaaaa00aa00ffaaffaaaa00aa00) (by decide +kernel) (carry_of (swaps := [(2,3),(3,4),(4,5),(1,2),(2,3)]) (by decide +kernel) F1.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl56 : Slice roots goal (subcubeFast 2 36) 4 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 25)) (qGoal := 0xffaaaa00ffaaaa00ffaaaa00ffaaaa00) (by decide +kernel) (carry_of (swaps := [(2,3),(3,4),(1,2),(2,3)]) (by decide +kernel) F1.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl57 : Slice roots goal (subcubeFast 2 48) 4 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 13)) (qGoal := 0xfaa0faa0faa0faa0faa0faa0faa0faa0) (by decide +kernel) (carry_of (swaps := [(2,3),(1,2)]) (by decide +kernel) F1.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl58 : Slice roots goal (subcubeFast 4 48) 4 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 11)) (qGoal := 0xee88ee88ee88ee88ee88ee88ee88ee88) (by decide +kernel) (carry_of (swaps := [(2,3)]) (by decide +kernel) F1.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl59 : Slice roots goal (subcubeFast 8 48) 4 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 7)) (qGoal := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8) (by decide +kernel) (carry_of (swaps := []) (by decide +kernel) F1.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl60 : Slice roots goal (subcubeFast 20 1) 4 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 42)) (qGoal := 0xffccffcccc00cc00ffccffcccc00cc00) (by decide +kernel) (carry_of (swaps := [(2,3),(3,4),(4,5),(1,2),(2,3),(0,1)]) (by decide +kernel) F1.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl61 : Slice roots goal (subcubeFast 24 2) 4 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 37)) (qGoal := 0xfafafafaa0a0a0a0fafafafaa0a0a0a0) (by decide +kernel) (carry_of (swaps := [(2,3),(3,4),(4,5),(1,2)]) (by decide +kernel) F1.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl62 : Slice roots goal (subcubeFast 36 1) 4 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 26)) (qGoal := 0xffcccc00ffcccc00ffcccc00ffcccc00) (by decide +kernel) (carry_of (swaps := [(2,3),(3,4),(1,2),(2,3),(0,1)]) (by decide +kernel) F1.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl63 : Slice roots goal (subcubeFast 40 2) 4 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 21)) (qGoal := 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0) (by decide +kernel) (carry_of (swaps := [(2,3),(3,4),(1,2)]) (by decide +kernel) F1.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl64 : Slice roots goal (subcubeFast 48 1) 4 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 14)) (qGoal := 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0) (by decide +kernel) (carry_of (swaps := [(2,3),(1,2),(0,1)]) (by decide +kernel) F1.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl65 : Slice roots goal (subcubeFast 48 2) 4 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 13)) (qGoal := 0xfaa0faa0faa0faa0faa0faa0faa0faa0) (by decide +kernel) (carry_of (swaps := [(2,3),(1,2)]) (by decide +kernel) F1.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl66 : Slice roots goal (subcubeFast 48 4) 4 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 11)) (qGoal := 0xee88ee88ee88ee88ee88ee88ee88ee88) (by decide +kernel) (carry_of (swaps := [(2,3)]) (by decide +kernel) F1.lower)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sl67 : Slice roots goal (subcubeFast 48 8) 4 := slice_fast_direct (zDead := 0) (qRoots := (varsOf 7)) (qGoal := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8) (by decide +kernel) (carry_of (swaps := []) (by decide +kernel) F1.lower)
def sliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,9),some (subcubeFast 0 2,9),some (subcubeFast 0 4,9),some (subcubeFast 0 8,9),some (subcubeFast 0 16,9),some (subcubeFast 0 32,9),some (subcubeFast 1 0,9),some (subcubeFast 2 0,9),some (subcubeFast 4 0,9),some (subcubeFast 8 0,9),some (subcubeFast 16 0,9),some (subcubeFast 32 0,9),some (subcubeFast 0 48,7),some (subcubeFast 48 0,7),some (subcubeFast 1 2,6),some (subcubeFast 1 4,6),some (subcubeFast 2 1,6),some (subcubeFast 2 8,6),some (subcubeFast 4 2,6),some (subcubeFast 4 8,6),some (subcubeFast 8 1,6),some (subcubeFast 8 4,6),some (subcubeFast 0 20,5),some (subcubeFast 0 24,5),some (subcubeFast 0 36,5),some (subcubeFast 0 40,5),some (subcubeFast 1 8,5),some (subcubeFast 1 16,5),some (subcubeFast 1 32,5),some (subcubeFast 2 4,5),some (subcubeFast 2 16,5),some (subcubeFast 2 32,5),some (subcubeFast 4 1,5),some (subcubeFast 4 16,5),some (subcubeFast 4 32,5),some (subcubeFast 8 2,5),some (subcubeFast 8 16,5),some (subcubeFast 8 32,5),some (subcubeFast 16 1,5),some (subcubeFast 16 2,5),some (subcubeFast 16 4,5),some (subcubeFast 16 8,5),some (subcubeFast 20 0,5),some (subcubeFast 24 0,5),some (subcubeFast 32 1,5),some (subcubeFast 32 2,5),some (subcubeFast 32 4,5),some (subcubeFast 32 8,5),some (subcubeFast 36 0,5),some (subcubeFast 40 0,5),some (subcubeFast 16 32,4),some (subcubeFast 32 16,4),some (subcubeFast 1 24,4),some (subcubeFast 1 40,4),some (subcubeFast 1 48,4),some (subcubeFast 2 20,4),some (subcubeFast 2 36,4),some (subcubeFast 2 48,4),some (subcubeFast 4 48,4),some (subcubeFast 8 48,4),some (subcubeFast 20 1,4),some (subcubeFast 24 2,4),some (subcubeFast 36 1,4),some (subcubeFast 40 2,4),some (subcubeFast 48 1,4),some (subcubeFast 48 2,4),some (subcubeFast 48 4,4),some (subcubeFast 48 8,4)]
def slices : BT (Option (Nat × Nat)) := btOfList 7 sliceList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma slicesOK : btAll (fun o => ∀ p, o = some p → Slice roots goal p.1 p.2) slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice roots goal p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl0) (forall_cons (fun _ h => by cases h; exact sl1) (forall_cons (fun _ h => by cases h; exact sl2) (forall_cons (fun _ h => by cases h; exact sl3) (forall_cons (fun _ h => by cases h; exact sl4) (forall_cons (fun _ h => by cases h; exact sl5) (forall_cons (fun _ h => by cases h; exact sl6) (forall_cons (fun _ h => by cases h; exact sl7) (forall_cons (fun _ h => by cases h; exact sl8) (forall_cons (fun _ h => by cases h; exact sl9) (forall_cons (fun _ h => by cases h; exact sl10) (forall_cons (fun _ h => by cases h; exact sl11) (forall_cons (fun _ h => by cases h; exact sl12) (forall_cons (fun _ h => by cases h; exact sl13) (forall_cons (fun _ h => by cases h; exact sl14) (forall_cons (fun _ h => by cases h; exact sl15) (forall_cons (fun _ h => by cases h; exact sl16) (forall_cons (fun _ h => by cases h; exact sl17) (forall_cons (fun _ h => by cases h; exact sl18) (forall_cons (fun _ h => by cases h; exact sl19) (forall_cons (fun _ h => by cases h; exact sl20) (forall_cons (fun _ h => by cases h; exact sl21) (forall_cons (fun _ h => by cases h; exact sl22) (forall_cons (fun _ h => by cases h; exact sl23) (forall_cons (fun _ h => by cases h; exact sl24) (forall_cons (fun _ h => by cases h; exact sl25) (forall_cons (fun _ h => by cases h; exact sl26) (forall_cons (fun _ h => by cases h; exact sl27) (forall_cons (fun _ h => by cases h; exact sl28) (forall_cons (fun _ h => by cases h; exact sl29) (forall_cons (fun _ h => by cases h; exact sl30) (forall_cons (fun _ h => by cases h; exact sl31) (forall_cons (fun _ h => by cases h; exact sl32) (forall_cons (fun _ h => by cases h; exact sl33) (forall_cons (fun _ h => by cases h; exact sl34) (forall_cons (fun _ h => by cases h; exact sl35) (forall_cons (fun _ h => by cases h; exact sl36) (forall_cons (fun _ h => by cases h; exact sl37) (forall_cons (fun _ h => by cases h; exact sl38) (forall_cons (fun _ h => by cases h; exact sl39) (forall_cons (fun _ h => by cases h; exact sl40) (forall_cons (fun _ h => by cases h; exact sl41) (forall_cons (fun _ h => by cases h; exact sl42) (forall_cons (fun _ h => by cases h; exact sl43) (forall_cons (fun _ h => by cases h; exact sl44) (forall_cons (fun _ h => by cases h; exact sl45) (forall_cons (fun _ h => by cases h; exact sl46) (forall_cons (fun _ h => by cases h; exact sl47) (forall_cons (fun _ h => by cases h; exact sl48) (forall_cons (fun _ h => by cases h; exact sl49) (forall_cons (fun _ h => by cases h; exact sl50) (forall_cons (fun _ h => by cases h; exact sl51) (forall_cons (fun _ h => by cases h; exact sl52) (forall_cons (fun _ h => by cases h; exact sl53) (forall_cons (fun _ h => by cases h; exact sl54) (forall_cons (fun _ h => by cases h; exact sl55) (forall_cons (fun _ h => by cases h; exact sl56) (forall_cons (fun _ h => by cases h; exact sl57) (forall_cons (fun _ h => by cases h; exact sl58) (forall_cons (fun _ h => by cases h; exact sl59) (forall_cons (fun _ h => by cases h; exact sl60) (forall_cons (fun _ h => by cases h; exact sl61) (forall_cons (fun _ h => by cases h; exact sl62) (forall_cons (fun _ h => by cases h; exact sl63) (forall_cons (fun _ h => by cases h; exact sl64) (forall_cons (fun _ h => by cases h; exact sl65) (forall_cons (fun _ h => by cases h; exact sl66) (forall_cons (fun _ h => by cases h; exact sl67) (fun _ h => by cases h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def empty : BT (List (List Nat)) := BT.empty
lemma emptyOK : btAll (fun bk => ∀ xs ∈ bk, Impossible goal (6-1) xs.toFinset) empty := trivial
def ps0 : PoolSpec := (12,[])
def ps1 : PoolSpec := (13,[])
def ps2 : PoolSpec := (18,[])
def ps3 : PoolSpec := (60,[])
def ps4 : PoolSpec := (61,[])
def ps5 : PoolSpec := (52,[])
def ps6 : PoolSpec := (10,[])
def ps7 : PoolSpec := (11,[])
def ps8 : PoolSpec := (15,[])
def ps9 : PoolSpec := (53,[])
def ps10 : PoolSpec := (16,[])
def ps11 : PoolSpec := (14,[])
def ps12 : PoolSpec := (55,[])
def ps13 : PoolSpec := (8,[])
def ps14 : PoolSpec := (9,[])
def ps15 : PoolSpec := (2,[])
def ps16 : PoolSpec := (21,[])
def ps17 : PoolSpec := (20,[])
def ps18 : PoolSpec := (4,[])
def ps19 : PoolSpec := (7,[])
def ps20 : PoolSpec := (3,[])
def ps21 : PoolSpec := (5,[])
def ps22 : PoolSpec := (56,[])
def ps23 : PoolSpec := (1,[])
def ps24 : PoolSpec := (62,[])
def ps25 : PoolSpec := (17,[])
def ps26 : PoolSpec := (64,[])
def ps27 : PoolSpec := (19,[])
def ps28 : PoolSpec := (54,[])
def ps29 : PoolSpec := (63,[])
def ps30 : PoolSpec := (6,[])
def ps31 : PoolSpec := (22,[])
def ps32 : PoolSpec := (58,[])
def ps33 : PoolSpec := (42,[])
def ps34 : PoolSpec := (65,[])
def ps35 : PoolSpec := (36,[])
def ps36 : PoolSpec := (23,[])
def ps37 : PoolSpec := (59,[])
def ps38 : PoolSpec := (38,[])
def ps39 : PoolSpec := (57,[])
def ps40 : PoolSpec := (39,[])
def ps41 : PoolSpec := (67,[])
def ps42 : PoolSpec := (30,[])
def ps43 : PoolSpec := (33,[])
def ps44 : PoolSpec := (40,[])
def ps45 : PoolSpec := (66,[])
def ps46 : PoolSpec := (27,[])
def ps47 : PoolSpec := (25,[])
def ps48 : PoolSpec := (44,[])
def ps49 : PoolSpec := (41,[])
def ps50 : PoolSpec := (46,[])
def ps51 : PoolSpec := (29,[])
def ps52 : PoolSpec := (4,[(1,0,1)])
def ps53 : PoolSpec := (13,[(0,0,2)])
def ps54 : PoolSpec := (12,[(1,0,3)])
def ps55 : PoolSpec := (10,[(0,0,1)])
def ps56 : PoolSpec := (4,[(0,0,2)])
def ps57 : PoolSpec := (0,[(2,4,5)])
def ps58 : PoolSpec := (12,[(1,0,2)])
def ps59 : PoolSpec := (13,[(0,0,3)])
def ps60 : PoolSpec := (4,[(1,0,2)])
def ps61 : PoolSpec := (0,[(0,2,4)])
def ps62 : PoolSpec := (4,[(3,0,2)])
def ps63 : PoolSpec := (4,[(1,0,3)])
def ps64 : PoolSpec := (4,[(2,0,3)])
def ps65 : PoolSpec := (4,[(0,0,3)])
def ps66 : PoolSpec := (3,[(2,4,5)])
def ps67 : PoolSpec := (14,[(0,4,5)])
def ps68 : PoolSpec := (3,[(0,4,5),(1,4,5)])
def ps69 : PoolSpec := (1,[(0,4,5),(1,4,5)])
def ps70 : PoolSpec := (11,[(2,0,3)])
def ps71 : PoolSpec := (6,[(2,4,5)])
def ps72 : PoolSpec := (5,[(1,0,1)])
def ps73 : PoolSpec := (1,[(2,4,5)])
def ps74 : PoolSpec := (5,[(1,0,2)])
def ps75 : PoolSpec := (11,[(0,0,2)])
def ps76 : PoolSpec := (8,[(2,4,5)])
def ps77 : PoolSpec := (4,[(3,0,3)])
def ps78 : PoolSpec := (2,[(2,4,5)])
def ps79 : PoolSpec := (6,[(0,2,4)])
def ps80 : PoolSpec := (10,[(1,0,2),(1,1,3),(0,11,27)])
def ps81 : PoolSpec := (15,[(2,4,5)])
def ps82 : PoolSpec := (8,[(0,4,5),(1,4,5)])
def ps83 : PoolSpec := (15,[(1,4,5)])
def ps84 : PoolSpec := (13,[(0,0,1)])
def ps85 : PoolSpec := (18,[(0,4,5)])
def ps86 : PoolSpec := (3,[(2,0,2)])
def ps87 : PoolSpec := (3,[(0,0,4)])
def ps88 : PoolSpec := (11,[(0,0,1)])
def ps89 : PoolSpec := (5,[(3,0,2)])
def ps90 : PoolSpec := (8,[(0,4,5)])
def ps91 : PoolSpec := (0,[(0,4,5)])
def ps92 : PoolSpec := (1,[(0,4,5)])
def ps93 : PoolSpec := (11,[(0,0,3)])
def ps94 : PoolSpec := (2,[(0,4,5),(1,4,5)])
def ps95 : PoolSpec := (7,[(0,4,5)])
def ps96 : PoolSpec := (2,[(0,4,5)])
def ps97 : PoolSpec := (7,[(2,4,5)])
def ps98 : PoolSpec := (3,[(1,4,5)])
def ps99 : PoolSpec := (8,[(1,4,5)])
def ps100 : PoolSpec := (0,[(1,4,5)])
def ps101 : PoolSpec := (0,[(0,4,5),(1,4,5)])
def ps102 : PoolSpec := (4,[(0,2,3)])
def ps103 : PoolSpec := (5,[(3,0,3)])
def ps104 : PoolSpec := (10,[(0,0,3)])
def ps105 : PoolSpec := (5,[(0,0,3)])
def ps106 : PoolSpec := (5,[(1,0,3)])
def ps107 : PoolSpec := (5,[(2,0,3)])
def ps108 : PoolSpec := (4,[(2,0,2)])
def ps109 : PoolSpec := (5,[(0,0,2)])
def ps110 : PoolSpec := (3,[(0,4,5)])
def ps111 : PoolSpec := (4,[(2,0,1)])
def ps112 : PoolSpec := (10,[(0,0,2),(0,1,3),(1,10,26)])
def ps113 : PoolSpec := (14,[(1,4,5)])
def ps114 : PoolSpec := (15,[(0,4,5)])
def ps115 : PoolSpec := (12,[(1,0,1)])
def ps116 : PoolSpec := (7,[(0,4,5),(1,4,5)])
def ps117 : PoolSpec := (0,[(3,3,4)])
def ps118 : PoolSpec := (0,[(1,3,4)])
def ps119 : PoolSpec := (9,[(0,4,5)])
def ps120 : PoolSpec := (4,[(0,0,1)])
def ps121 : PoolSpec := (9,[(0,4,5),(1,4,5)])
def ps122 : PoolSpec := (3,[(1,1,4)])
def ps123 : PoolSpec := (10,[(1,0,2)])
def ps124 : PoolSpec := (4,[(1,2,3)])
def ps125 : PoolSpec := (1,[(1,4,5)])
def ps126 : PoolSpec := (0,[(2,2,4)])
def ps127 : PoolSpec := (1,[(1,2,4)])
def ps128 : PoolSpec := (4,[(2,2,3)])
def ps129 : PoolSpec := (7,[(1,4,5)])
def ps130 : PoolSpec := (2,[(1,4,5)])
def ps131 : PoolSpec := (10,[(1,0,3)])
def ps132 : PoolSpec := (11,[(3,0,2)])
def ps133 : PoolSpec := (9,[(1,4,5)])
def ps134 : PoolSpec := (3,[(2,0,4)])
def ps135 : PoolSpec := (5,[(0,2,3)])
def ps136 : PoolSpec := (9,[(2,4,5)])
def ps137 : PoolSpec := (2,[(2,1,4)])
def ps138 : PoolSpec := (8,[(0,0,3)])
def ps139 : PoolSpec := (3,[(1,0,2)])
def ps140 : PoolSpec := (1,[(0,3,4)])
def ps141 : PoolSpec := (1,[(3,0,3)])
def ps142 : PoolSpec := (11,[(2,0,2)])
def ps143 : PoolSpec := (5,[(2,0,2)])
def ps144 : PoolSpec := (11,[(3,0,3)])
def ps145 : PoolSpec := (5,[(0,0,1)])
def ps146 : PoolSpec := (7,[(0,0,3)])
def ps147 : PoolSpec := (11,[(1,0,3)])
def ps148 : PoolSpec := (9,[(2,0,1)])
def ps149 : PoolSpec := (3,[(2,0,1)])
def ps150 : PoolSpec := (11,[(2,0,1)])
def ps151 : PoolSpec := (5,[(2,0,1)])
def ps152 : PoolSpec := (11,[(1,0,1)])
def ps153 : PoolSpec := (6,[(0,1,4)])
def ps154 : PoolSpec := (11,[(0,0,2),(0,1,3),(1,10,26)])
def ps155 : PoolSpec := (5,[(1,0,3),(1,1,2),(0,23,15)])
def ps156 : PoolSpec := (11,[(1,0,2),(1,1,3),(0,11,27)])
def ps157 : PoolSpec := (5,[(0,0,3),(0,1,2),(1,14,22)])
def ps158 : PoolSpec := (4,[(0,0,3),(0,1,2),(1,14,22)])
def ps159 : PoolSpec := (4,[(3,0,2),(3,1,3)])
def ps160 : PoolSpec := (4,[(1,0,3),(1,1,2),(0,23,15)])
def ps161 : PoolSpec := (4,[(2,0,3),(2,1,2),(1,16,24)])
def ps162 : PoolSpec := (4,[(3,0,2),(3,1,3),(1,29,13)])
def ps163 : PoolSpec := (0,[(1,1,3),(0,4,5)])
def ps164 : PoolSpec := (4,[(2,0,3),(2,1,2)])
def ps165 : PoolSpec := (0,[(1,1,2),(1,4,5)])
def ps166 : PoolSpec := (4,[(0,0,3),(0,1,2)])
def ps167 : PoolSpec := (6,[(0,1,3),(0,4,5)])
def ps168 : PoolSpec := (6,[(0,4,5),(1,4,5)])
def ps169 : PoolSpec := (5,[(2,0,3),(2,1,2),(1,16,24)])
def ps170 : PoolSpec := (5,[(3,0,2),(3,1,3),(1,29,13)])
def b6x0Pools : BT (Option BoundPool) := buildPoolsBT 1 wires roots slices [ps18,ps6]
def b6x0 : List NodeSpec := [([66,0,1,2,3,5],[],[]),([178,0,1,2,173,3,5],[],[]),([95,0,1,90,2,3,5],[],[]),([178,0,1,2,3,5],[],[]),([134,0,1,131,2,3,140],[0],[]),([143,0,1,131,2,3,57],[0],[]),([240,0,1,2,3,5],[],[]),([66,0,1,2,61,3,5],[],[]),([284,0,1,2,273,3,58],[1],[]),([136,0,1,131,2,3,5],[],[]),([275,0,1,2,273,3,280],[1],[]),([0,1,232,2,3,237,236],[1],[]),([0,1,2,174,173,3,179],[0],[]),([0,1,2,184,173,3,57],[0],[]),([278,0,1,2,3,5],[],[]),([240,0,1,232,2,3,5],[],[]),([136,0,1,2,3,5],[],[]),([278,0,1,2,273,3,5],[],[]),([95,0,1,2,3,5],[],[]),([0,1,232,2,3,242,58],[1],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b6x0Ok : checkNodesBT wires goal (fullMask 100) b6x0Pools autos empty 6 b6x0 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b6x0Mem : ∀ ns ∈ b6x0, Impossible goal 6 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK emptyOK b6x0Ok
def buckets6 : BT (CertifiedBucket goal 6) := staticBuckets (btOfList 0 [bucketFragment wires b6x0 b6x0Mem]) [[(0,0,1)],[(0,1,1)],[],[],[],[],[(0,2,1)],[(0,3,1)],[],[],[],[],[],[],[],[],[(0,4,2)],[(0,6,1)],[],[(0,7,1)],[],[(0,8,1)],[],[],[(0,9,1)],[(0,10,1)],[],[],[],[],[],[(0,11,1)],[],[],[],[(0,12,2)],[],[],[(0,14,1)],[],[(0,15,1)],[],[],[],[],[],[],[],[(0,16,1)],[(0,17,1)],[],[],[],[],[],[(0,18,1)],[],[],[],[],[(0,19,1)],[],[],[]]
def table6 := bucketValues buckets6
set_option maxRecDepth 200000 in
lemma table6OK : btAll (fun bk => ∀ xs ∈ bk, Impossible goal 6 xs.toFinset) table6 := bucketValues_ok _
def b7x0Pools : BT (Option BoundPool) := buildPoolsBT 6 wires roots slices [ps6,ps30,ps19,ps13,ps14,ps18,ps7,ps8,ps2,ps20,ps38,ps21,ps112,ps0,ps154,ps3,ps160,ps15,ps9,(51,[]),ps22,ps1,ps155,ps4,(50,[]),ps10,ps156,ps11,ps16,ps80,ps46,ps31,(10,[(2,0,3),(2,1,2),(1,16,24)]),ps161,ps42,ps36,ps23,(0,[]),ps5,(4,[(0,0,3),(2,1,2),(1,24,14)])]
def b7x0 : List NodeSpec := [([284,0,1,2,273,3,4,5],[0],[0]),([0,1,101,2,3,4,5],[1,2,3,4,5,6],[]),([0,1,2,72,3,4,5],[1,3,5,6,2,4],[]),([0,1,2,81,77,3,4,5],[7,8,9,10],[]),([0,1,90,100,2,3,4,5],[11],[]),([137,0,1,131,2,3,4,5],[12,13,14],[]),([275,276,0,1,2,3,5],[15,13,16],[0]),([234,235,0,1,232,2,3,5],[0,5],[0]),([0,1,303,2,3,298,4,5],[17],[]),([0,1,2,173,182,3,4,5],[18,19],[]),([0,1,139,2,3,4,5],[18,19,20],[]),([0,1,2,61,71,3,4,5],[11],[]),([279,0,1,2,273,3,4,5],[16,21,22],[]),([0,1,2,198,193,3,4,5],[9],[]),([0,1,2,285,273,3,4,5],[5],[]),([239,0,1,232,2,3,4],[15,23,6,24],[]),([0,1,2,173,3,4,181,5],[18,25,26,13,27,28,29],[]),([310,0,1,2,3,57,58],[30,31,32,33,34,35],[]),([143,0,1,131,2,3,4,5],[5],[0]),([0,1,241,232,2,3,4,5],[15,19],[]),([0,1,108,112,2,3,4,5],[9],[]),([0,1,2,274,3,277,5],[15,24,23,16],[0]),([0,1,2,273,3,57,58],[23,15,16,13],[0]),([59,0,1,232,2,3,237,5],[13,19,0],[]),([0,1,2,182,3,4,5],[19,36,37,17,9,5],[]),([133,134,0,1,2,3,5],[38,21,12],[0]),([275,276,0,1,2,273,3,5],[0,5],[0]),([156,0,1,152,2,3,4,5],[9],[]),([0,1,90,2,3,57,58],[38,15],[]),([0,250,1,2,3,57,58],[23,39,35,31],[]),([0,1,132,131,2,3,135,5],[5,0],[0]),([60,0,1,2,174,173,3,5],[24,21,5],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b7x0Ok : checkNodesBT wires goal (fullMask 100) b7x0Pools autos table6 7 b7x0 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b7x0Mem : ∀ ns ∈ b7x0, Impossible goal 7 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table6OK b7x0Ok
def b7x1Pools : BT (Option BoundPool) := buildPoolsBT 6 wires roots slices [ps13,ps21,ps18,ps3,ps5,ps12,(10,[(1,0,2),(3,1,3),(3,29,11)]),ps46,ps43,(51,[]),ps0,ps6,ps24,ps11,ps157,ps1,ps10,ps16,ps158,ps4,ps7,(50,[]),ps30,ps19,ps14,(10,[(3,0,2),(3,1,3),(1,29,13)]),ps31,ps42,ps36,ps162,(4,[(1,0,3),(2,1,2),(3,24,15)]),ps2,ps17,ps15,ps80]
def b7x1 : List NodeSpec := [([296,0,1,2,3,298,4,5],[0],[]),([0,1,101,90,2,3,4,5],[1],[]),([244,0,1,232,2,3,4,5],[2],[]),([0,1,2,62,3,65,5],[3,4],[0]),([0,1,2,61,3,57,58],[5,3],[]),([0,191,1,2,3,57,58],[5,6,7,8],[]),([0,1,2,186,173,3,4,5],[1],[]),([59,275,0,1,2,273,3,5],[9,10,11],[]),([92,93,0,1,2,3,5],[3,4],[0]),([0,1,238,232,2,3,4,5],[12,13,14,15,16,17,18],[]),([0,1,2,72,61,3,4,5],[1],[]),([0,1,253,258,2,3,4,5],[1],[]),([0,1,2,274,273,3,277,5],[2,11],[0]),([0,1,2,273,281,3,4],[19,3,20,21],[]),([60,134,0,1,131,2,3,5],[15,21,2],[]),([0,1,233,2,3,237,5],[3,10,18],[0]),([0,1,232,2,3,57,58],[3,19,18,10],[0]),([0,1,2,274,273,3,5,58],[15,21,2,3],[]),([0,1,2,186,3,4,5],[9,22,23,0,24],[]),([0,1,142,131,2,3,4,5],[2],[]),([0,1,131,2,3,4,138],[5,4,9,1],[]),([63,64,0,1,2,3,5],[3,4],[0]),([220,0,1,2,3,57,58],[7,25,26,27,28,29],[]),([0,1,2,290,3,57,58],[3,30,26,28],[]),([0,1,2,184,173,3,4,5],[13,31,2,16,32],[0]),([175,176,0,1,2,173,3,5],[11,2],[0]),([0,1,2,273,3,4,280],[19,3,10,15],[0]),([0,1,2,282,3,4,5],[3,9,19],[]),([0,1,131,144,2,3,4,5],[1],[]),([92,93,0,1,90,2,3,5],[11,2],[0]),([257,0,1,253,2,3,4,5],[33],[]),([175,176,0,1,2,3,5],[9,4,34],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b7x1Ok : checkNodesBT wires goal (fullMask 100) b7x1Pools autos table6 7 b7x1 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b7x1Mem : ∀ ns ∈ b7x1, Impossible goal 7 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table6OK b7x1Ok
def b7x2Pools : BT (Option BoundPool) := buildPoolsBT 5 wires roots slices [(51,[]),ps20,(0,[]),ps15,ps23,ps18,ps6,ps5,ps12,ps112,ps1,ps0,ps11,ps8,ps10,ps25,ps3,ps14,ps4,ps7,ps2,ps17,(50,[]),ps158,ps9,ps30,ps19,ps13,ps21,(28,[])]
def b7x2 : List NodeSpec := [([0,1,245,2,3,4,5],[0,1,2,3,4],[]),([0,1,2,62,61,3,65,5],[5,6],[0]),([0,1,132,2,3,135,5],[7,0,8,9],[0]),([0,1,131,2,3,57,58],[8,7,9,10],[0]),([175,0,1,2,173,3,57,5],[11,0,6,7],[]),([99,0,1,90,2,3,4,5],[5],[]),([0,1,232,2,3,4,242,5],[6,12,13,14,15],[0]),([0,1,2,173,3,4,179],[7,8,10,11],[0]),([0,1,2,273,282,3,4,5],[16,0],[]),([0,1,91,2,3,94,5],[7,16],[0]),([197,0,1,2,193,3,4,5],[17],[]),([185,0,1,2,173,3,4,5],[5],[]),([0,1,2,286,3,4,5],[16,18,19,5],[]),([97,0,1,90,2,3,4,5],[6],[]),([68,0,1,2,61,3,4,5],[6],[]),([0,1,233,232,2,3,237,5],[5,6],[0]),([0,1,2,69,61,3,4,5],[13,20,5,21],[]),([0,1,2,273,3,4,283,5],[6],[]),([234,235,0,1,2,3,5],[22,16,23],[0]),([0,1,139,131,2,3,4,5],[24,0],[]),([0,1,98,90,2,3,4,5],[5],[]),([0,1,131,2,3,4,141,5],[6],[]),([63,64,0,1,2,61,3,5],[6,5],[0]),([70,0,1,2,61,3,4,5],[5],[]),([0,1,131,2,3,57,135,5],[0,11,6,7],[]),([0,1,241,2,3,4,5],[0,25,26,27,17,6],[]),([0,1,100,2,3,4,5],[3,2,5,19,4,1],[]),([0,1,2,71,3,4,5],[4,2,1,3,5,19],[]),([0,1,2,174,173,3,177,5],[5,6],[0]),([0,1,2,82,77,3,4,5],[28],[]),([133,134,0,1,131,2,3,5],[6,5],[0]),([0,1,106,2,107,3,4,5],[21,27,15,29],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b7x2Ok : checkNodesBT wires goal (fullMask 100) b7x2Pools autos table6 7 b7x2 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b7x2Mem : ∀ ns ∈ b7x2, Impossible goal 7 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table6OK b7x2Ok
def b7x3Pools : BT (Option BoundPool) := buildPoolsBT 5 wires roots slices [ps21,ps9,ps22,ps6,ps18,ps5,ps12,(51,[]),ps3,ps4,ps0,ps1,ps80,(50,[]),ps2,ps8,ps25,(10,[(0,0,2),(3,1,3),(1,29,10)]),ps31,ps43]
def b7x3 : List NodeSpec := [([0,1,2,286,273,3,4,5],[0],[]),([0,1,144,2,3,4,5],[1,2,3,4],[]),([180,0,1,2,173,3,4],[5,6,0,7],[]),([0,1,232,2,3,4,236],[8,9,10,11],[0]),([0,1,2,174,3,177,5],[5,11,12],[0]),([0,1,2,173,3,57,58],[5,6,12,11],[0]),([183,0,1,2,173,3,4,5],[3],[]),([0,1,152,157,2,3,4,5],[0],[]),([0,1,91,90,2,3,94,5],[4,3],[0]),([243,0,1,232,2,3,4,5],[3],[]),([235,0,1,232,2,3,5,58],[13,11,4,8],[]),([0,1,232,245,2,3,4,5],[0],[]),([0,1,90,2,3,4,96,5],[14,3,15,16],[]),([0,1,2,61,3,4,67,5],[3],[]),([0,150,1,2,3,57,58],[5,17,18,19],[]),([0,1,131,2,3,4,140],[6,5,11,10],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b7x3Ok : checkNodesBT wires goal (fullMask 100) b7x3Pools autos table6 7 b7x3 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b7x3Mem : ∀ ns ∈ b7x3, Impossible goal 7 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table6OK b7x3Ok
def buckets7 : BT (CertifiedBucket goal 7) := staticBuckets (btOfList 2 [bucketFragment wires b7x0 b7x0Mem,bucketFragment wires b7x1 b7x1Mem,bucketFragment wires b7x2 b7x2Mem,bucketFragment wires b7x3 b7x3Mem]) [[],[(0,0,4)],[(0,4,1)],[(0,5,2)],[],[(0,7,3)],[(0,10,2)],[(0,12,3)],[(0,15,1)],[(0,16,1)],[(0,17,6)],[(0,23,2)],[],[(0,25,1)],[(0,26,3)],[(0,29,2)],[(0,31,1),(1,0,2)],[],[(1,2,3)],[(1,5,2)],[(1,7,4)],[(1,11,3)],[(1,14,3)],[],[(1,17,1)],[(1,18,1)],[],[(1,19,2)],[],[(1,21,4)],[(1,25,3)],[],[(1,28,1)],[],[],[(1,29,2)],[(1,31,1)],[(2,0,2)],[],[(2,2,2)],[(2,4,4)],[(2,8,1)],[],[(2,9,1)],[(2,10,3)],[(2,13,5)],[(2,18,3)],[(2,21,1)],[(2,22,1)],[(2,23,2)],[],[(2,25,4)],[(2,29,1)],[(2,30,2)],[],[(3,0,1)],[(3,1,1)],[(3,2,4)],[(3,6,3)],[],[(3,9,5)],[(3,14,2)],[],[]]
def table7 := bucketValues buckets7
set_option maxRecDepth 200000 in
lemma table7OK : btAll (fun bk => ∀ xs ∈ bk, Impossible goal 7 xs.toFinset) table7 := bucketValues_ok _
def b8x0Pools : BT (Option BoundPool) := buildPoolsBT 7 wires roots slices [ps22,ps32,ps8,ps17,ps10,ps27,ps1,ps5,(49,[]),ps31,(0,[(0,2,4),(1,6,41)]),ps3,ps39,ps36,ps4,ps2,ps44,ps50,ps81,ps12,ps9,ps38,ps0,(51,[]),ps20,ps160,(16,[(1,2,4)]),(14,[(1,3,4)]),ps25,ps24,ps155,ps26,ps40,ps19,ps37,(24,[]),ps28,ps29,(48,[]),ps43,ps33,(4,[(0,0,2),(1,10,30)]),ps47,ps23,ps11,(10,[(3,0,2),(3,13,31)]),(50,[]),ps169,ps46,(15,[(3,4,5)]),ps161,ps42,(31,[]),ps113,(16,[(1,4,5)]),ps21,(47,[]),(20,[(1,1,4)]),ps58,ps158,ps16,ps157,ps6,ps7,ps163,ps34,(17,[(3,0,2)]),ps13,(37,[]),ps35,ps162,ps170]
def b8x0 : List NodeSpec := [([0,223,30,1,2,3,4,5],[0,1,2,3,4,5,6],[]),([0,1,2,77,3,4,5,54],[0,7,8,2,9,10],[0]),([251,0,1,2,3,15,4,5],[11,12,13,14,4,15,16,17,18],[]),([75,0,1,2,3,57,4,5],[7,19,20,21,22],[]),([0,1,2,187,188,3,4,5],[0,21,23,24],[]),([0,1,2,273,3,4,277,5],[14,25,26,27,11,23,22,9,13,2,28,29,30],[0]),([32,0,1,2,3,225,4,5],[1,31,32,3,5,33],[]),([297,0,1,2,3,15,4,5],[11,34,35,15,5,2,6,19,36],[]),([33,259,0,1,2,3,4,5],[37,36,38,2],[]),([76,0,1,2,3,57,4,5],[7,19,15,20,32,22,39],[]),([0,1,232,2,3,57,4,5],[11,14,29,22],[0]),([105,0,1,2,3,4,5,54],[29,14,28,8],[]),([0,1,152,2,3,4,5,54],[0,7,40,8,41],[0]),([0,1,2,3,225,4,31,5],[1,31,42,4,3,43],[]),([56,0,224,1,2,3,4,5],[7,1,44,4,2,28,6,45],[]),([64,0,1,2,61,3,4,5],[11,14,7,6,46,20,29],[0]),([310,0,1,2,3,4,5,58],[47,48,9,49,15,50,51,13,4,3,28],[0]),([36,0,1,2,349,3,4,5],[19,3,1,5,6,2,52,44,22],[]),([0,1,2,273,3,4,5,58],[25,29,14,53,54,6,30,9,13,2,28],[0,1]),([35,0,339,1,2,3,4,5],[20,19,2,5],[]),([16,297,0,1,2,3,4,5],[36,37,35,15],[]),([0,1,104,2,3,4,5,58],[7,11,6,28,15,55],[]),([0,1,2,196,193,3,4,5],[19,31,0,7,8,56,57,58],[]),([0,1,2,3,348,347,4,5],[7,19,20],[]),([16,268,0,1,2,3,4,5],[36,11,3,24,15,51],[]),([0,1,122,2,53,3,4,5],[7,4,15,36,2,3,28,5,6,42],[]),([0,1,233,232,2,3,4,5],[11,14,44,4,6,46,59,5,60,29,61],[0]),([59,0,1,2,173,3,4,5],[20,0,7,60,5,62,63,64],[0,1]),([0,1,90,2,3,4,5,58],[7,19,20,6],[0]),([151,10,0,1,2,3,4,5],[20,65,0,66,67,21,44,68,69],[]),([220,0,1,2,3,57,4,5],[21,22,18,32,15,4,70,71,39,69,63,3,28],[0]),([0,250,1,2,3,4,5,58],[14,51,2,37,15,4,48,55,6,28,9],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b8x0Ok : checkNodesBT wires goal (fullMask 100) b8x0Pools autos table7 8 b8x0 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b8x0Mem : ∀ ns ∈ b8x0, Impossible goal 8 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table7OK b8x0Ok
def b8x1Pools : BT (Option BoundPool) := buildPoolsBT 7 wires roots slices [ps3,ps24,ps25,ps2,ps35,ps36,ps16,ps4,(34,[]),ps17,ps81,ps39,ps44,ps50,ps29,ps28,ps15,ps5,ps33,(4,[(0,0,2),(1,10,30)]),ps11,ps14,ps47,(47,[]),ps26,ps37,ps51,ps9,ps43,ps31,ps6,ps67,ps12,ps1,ps7,ps42,ps22,ps46,ps20,ps8,(48,[]),ps34,(28,[]),(51,[]),(14,[(0,4,5),(1,4,5)]),(10,[(0,0,2),(3,1,3)]),ps159,ps68,ps52,(16,[(0,4,5),(1,4,5)]),(4,[(1,0,3),(2,1,2)]),ps82,ps164,ps38,ps40,ps13,(45,[]),ps10,(49,[]),ps53,ps158,ps83,(17,[(1,4,5)]),ps157,(0,[(1,1,4),(3,2,4)]),(4,[(2,0,3),(3,1,2)]),ps41,ps0,(31,[]),ps80,(2,[(1,1,3),(0,173,4)]),(3,[(1,0,2),(0,173,4)]),(18,[(0,0,4)]),(50,[]),ps156,(15,[(0,4,5),(1,4,5)]),(10,[(2,0,3),(2,1,2)]),(0,[(1,1,2),(1,273,4)]),ps155,ps112,(16,[(0,4,5)]),ps154,(10,[(3,0,2),(3,1,3)]),(17,[(0,4,5),(1,4,5)])]
def b8x1 : List NodeSpec := [([0,1,2,290,3,57,4,5],[0,1,2,3,4,5,6],[0]),([16,313,0,1,2,3,4,5],[7,0,1,5,8,9],[]),([251,14,0,1,2,3,4,5],[7,10,11,3,5,12,13],[]),([48,0,1,2,3,298,4,5],[14,0,15,16,5,8],[0]),([0,1,152,2,3,153,4,5],[17,18,19,20,21,22,23,24,15],[]),([0,1,302,2,3,15,4,5],[24,14,8,25,20,26],[]),([59,0,150,1,2,3,4,5],[27,3,28,2,29,30,6,17,31],[]),([0,1,2,61,3,4,5,58],[32,27,33],[0]),([0,1,2,337,3,4,5,338],[7,27,18,34],[]),([268,14,0,1,2,3,4,5],[15,0,35,25,3,13],[]),([0,191,1,2,3,4,5,58],[32,36,9,2,37,28,20],[0]),([16,260,0,1,2,3,4,5],[15,9,0,26,38,39,40,41,25],[]),([24,247,0,1,2,3,4,5],[7,0,42,29,3,43,20],[]),([29,10,0,1,2,3,57,58],[17,44,45,4,32,28,41,46,47],[0]),([0,1,108,2,3,109,4,5],[17,18,39,3,21,22,23,1,15,48],[]),([16,0,1,302,2,3,4,5],[15,14,8,26],[]),([24,0,1,2,3,15,57,58],[0,49,50,12,7,5,11,51,52],[0]),([151,13,0,1,2,3,4,5],[36,27,53,54,20,4,39,2,55,56,57],[]),([247,0,22,1,2,3,4,5],[0,7,15,20,43,29],[0]),([202,13,0,1,2,3,4,5],[24,17,39,2,55,54],[]),([158,0,30,1,2,3,4,5],[36,17,58],[]),([146,0,26,1,2,3,4,5],[36,27,59,20,43,54],[0]),([0,1,232,2,3,4,5,58],[60,1,61,7,62,33,63],[0,1]),([0,1,299,2,3,298,4,5],[17,0,14,57,16,15,40,8,64],[]),([16,25,0,1,2,3,57,58],[0,44,65,66,32,7],[]),([118,0,1,2,3,57,4,5],[17,3,57,27,53,39,35,28,29,67],[]),([36,0,1,2,3,347,4,5],[32,27,9,33,68,67],[]),([0,1,2,174,173,3,4,5],[69,70,71,17,32,72,33,73,57,27,74],[0]),([16,24,0,1,2,3,57,58],[75,7,11,52,5,0,76],[0]),([276,0,1,2,273,3,4,5],[0,7,33,73,77,1,78],[0]),([0,1,131,2,3,57,4,5],[79,27,32,80,31,67,81,53,54,3,9],[0,1]),([29,13,0,1,2,3,57,58],[17,32,24,41,82,28,4,75,83,46],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b8x1Ok : checkNodesBT wires goal (fullMask 100) b8x1Pools autos table7 8 b8x1 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b8x1Mem : ∀ ns ∈ b8x1, Impossible goal 8 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table7OK b8x1Ok
def b8x2Pools : BT (Option BoundPool) := buildPoolsBT 7 wires roots slices [ps3,(51,[]),ps47,ps19,ps28,ps37,(48,[]),ps51,ps10,ps8,ps34,ps0,(13,[(0,0,3),(3,253,46)]),ps29,ps5,ps67,ps38,ps9,ps2,(15,[(1,1,3)]),ps31,ps7,ps25,ps17,ps1,ps11,ps27,ps26,ps33,(37,[]),(9,[(0,0,2),(0,1,4),(1,10,30)]),ps4,(32,[]),(47,[]),ps22,(49,[]),(28,[]),ps36,ps48,ps12,ps32,ps84,ps170,ps46,(15,[(3,4,5)]),ps42,ps162,ps24,ps21,ps16,ps14,ps112,(16,[(3,2,4)]),(14,[(3,3,4)]),(50,[]),ps40,ps154,ps23,(24,[]),ps43,ps81,(18,[(2,4,5)]),ps169,(17,[(2,4,5)]),ps114,ps161,ps18,ps165,(15,[(2,1,4)]),ps158,(17,[(2,0,4)]),ps157,(15,[(0,4,5),(1,4,5)]),(4,[(0,0,3),(2,1,2)]),ps39,ps44,ps69,ps15,(34,[]),ps49,(0,[(1,1,3),(0,173,4)]),ps156,ps166,(8,[(0,0,3),(1,232,4)]),(9,[(0,1,2),(1,232,4)]),(17,[(1,0,4)]),ps115,(6,[(1,3,5),(0,7,54)]),ps58,(4,[(1,0,3),(1,1,2)]),ps54,(12,[(1,1,2)]),(20,[(3,1,4)]),ps80,(18,[(3,0,4)]),(17,[(3,0,2)]),ps35]
def b8x2 : List NodeSpec := [([291,0,1,2,3,289,4,5],[0,1,2,3],[]),([260,14,0,1,2,3,4,5],[4,5,6,7,8,9,10,11],[]),([259,0,30,1,2,3,4,5],[4,12,6,13,11,3,9,2],[]),([148,0,1,2,3,57,4,5],[14,15,11,16,17,18,19,20,21],[]),([0,1,314,2,3,4,5,46],[4,22,0,23,9,24,25,26,27],[]),([0,1,152,2,3,4,5,155],[4,28,8,25,2,29,21,14,30],[]),([55,0,1,2,77,3,4,5],[31,4,20,32,33],[0]),([295,0,1,2,3,4,31,5],[34,0,26,35],[]),([24,0,1,2,3,289,4,5],[0,31,8,18,36,37,38,20,25],[]),([6,0,1,37,2,3,57,58],[14,0,39,40,41],[0]),([220,0,1,2,3,4,5,58],[42,43,44,20,45,37,18,46,8,23,22],[0]),([0,1,2,290,3,4,5,58],[0,20,22,47,18,9,37,48,24,49,45],[0]),([55,0,1,152,2,3,4,5],[34,4,33,50,28,27,14],[0]),([134,0,1,131,2,3,4,5],[14,51,39,52,53,24,54,25,8,17,16,55,56],[0]),([147,146,0,1,2,3,4,5],[17,1,57,58,59],[]),([73,0,1,37,2,3,4,5],[0,17,55,45,41],[0]),([59,310,0,1,2,3,4,5],[60,61,62,63,23,64,65],[]),([59,0,1,2,273,3,4,5],[0,31,47,48,66,67],[0]),([234,0,1,232,2,3,4,5],[0,68,69,70,31,1,11,47,71],[0]),([24,14,0,1,2,3,57,58],[31,72,73,74,75,76],[0]),([255,0,1,253,2,3,4,5],[31,0,77,4,13,78,6],[]),([10,0,1,167,2,3,4,5],[14,39,79,11,24,23,25],[]),([175,0,1,2,173,3,4,5],[14,39,1,11,80,17,81],[0]),([44,0,1,121,2,3,4,5],[34,14,8],[]),([14,0,22,1,2,3,57,58],[0,31,82,74,4],[0]),([0,1,232,2,3,4,237,5],[69,83,84,0,31,85,1,11,25,47,71],[0]),([0,1,102,2,3,38,4,5],[17,34,16,1,75,18,86],[0]),([0,1,106,41,2,3,4,5],[31,47,20,23,35,87],[0]),([0,1,2,193,53,3,4,5],[27,88,20,14,18,50,8,2],[0]),([0,1,2,23,3,15,57,58],[31,0,89,90,91],[0]),([176,0,1,2,173,3,4,5],[14,92,93,94,39,24,54,17,81],[0]),([151,0,1,2,11,3,4,5],[34,10,95,25,16,29,17,96],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b8x2Ok : checkNodesBT wires goal (fullMask 100) b8x2Pools autos table7 8 b8x2 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b8x2Mem : ∀ ns ∈ b8x2, Impossible goal 8 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table7OK b8x2Ok
def b8x3Pools : BT (Option BoundPool) := buildPoolsBT 7 wires roots slices [ps41,ps28,ps42,ps8,ps27,ps23,ps29,ps3,ps36,(24,[]),(10,[(1,0,3),(0,15,31)]),ps4,ps5,ps1,(50,[]),ps17,ps9,ps24,ps12,(51,[]),ps0,ps22,(37,[]),ps38,ps2,ps25,ps14,ps40,ps10,ps7,ps21,ps83,ps47,ps16,ps32,(35,[]),ps11,ps39,ps45,ps115,ps33,(32,[]),ps48,(45,[]),(47,[]),(49,[]),ps44,ps13,(14,[(2,3,4)]),ps26,(6,[(0,1,2),(1,232,4)]),ps157,(10,[(1,0,2),(3,1,3)]),ps35,ps34,(17,[(0,4,5),(1,4,5)]),ps159,ps116,(17,[(0,4,5)]),ps46,(34,[]),ps6,(6,[(0,1,3),(0,131,4)]),ps154,ps59,(43,[]),(48,[]),ps160,(16,[(2,2,4)]),ps31,ps155,ps112]
def b8x3 : List NodeSpec := [([33,0,1,2,3,315,4,5],[0,1,2,3,4,5],[]),([0,1,45,2,3,298,4,5],[6,7,8,9,10],[0]),([0,1,2,62,61,3,4,5],[7,11,12,3,13,14,15,16,17],[0]),([63,0,1,2,61,3,4,5],[12,18,7,19,20,16,17],[0]),([202,0,1,2,11,3,4,5],[21,12,22,13],[]),([29,0,1,2,188,3,4,5],[21,16,23,18,24,25,26,27],[]),([0,1,2,116,3,4,5,58],[12,11,28,24,3,29,30],[]),([59,0,1,90,2,3,4,5],[16,7,25,24],[0]),([119,0,1,2,3,4,5,58],[12,11,13,30,3,24],[]),([59,0,250,1,2,3,4,5],[11,31,24,32,6,9,28,25,33],[]),([32,0,1,2,3,213,4,5],[12,21,32,33],[]),([163,13,0,1,2,3,4,5],[34,16,35,28,36,37],[]),([0,1,7,2,3,38,57,58],[12,7,18,38,39],[0]),([111,0,1,108,2,3,4,5],[40,1,11,41,12,3,42,43,44,45],[]),([13,0,1,167,2,3,4,5],[18,12,15,3,35,13,20,36],[]),([0,1,2,3,213,4,31,5],[12,7,21,33,5,42],[]),([92,0,1,90,2,3,4,5],[12,18,7,19,20,16,17],[0]),([43,0,1,2,3,123,4,5],[12,11,46,32,42,47],[]),([154,0,1,152,2,3,4,5],[7,12,48,49,1,28,22,45],[]),([235,0,1,232,2,3,4,5],[7,11,13,14,50,17,51],[0]),([29,0,1,2,11,3,57,58],[18,52,12,53,23,54,55,56,57],[0]),([59,0,1,2,61,3,4,5],[16,7,25,24],[0]),([79,0,1,2,77,3,4,5],[18,12,26,1,17,44,32],[]),([0,1,131,2,3,4,5,58],[18,16,13],[0]),([59,0,191,1,2,3,4,5],[21,15,58,59,60,61,36,24,33,18],[]),([133,0,1,131,2,3,4,5],[12,18,19,20,62,16,63],[0]),([0,1,253,2,3,4,5,46],[1,64,65,66,25,3,6],[0]),([275,0,1,2,273,3,4,5],[7,67,11,48,68,19,20,36,28,17,69,8,70],[0]),([159,10,0,1,2,3,4,5],[12,21,45],[]),([10,0,160,1,2,3,4,5],[1,21,44,35,28,15],[]),([0,1,131,2,3,4,135,5],[18,12,19,20,71,16,63],[0]),([195,0,1,2,193,3,4,5],[18,12,26,1,49,44,32],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b8x3Ok : checkNodesBT wires goal (fullMask 100) b8x3Pools autos table7 8 b8x3 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b8x3Mem : ∀ ns ∈ b8x3, Impossible goal 8 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table7OK b8x3Ok
def b8x4Pools : BT (Option BoundPool) := buildPoolsBT 7 wires roots slices [ps3,ps4,ps24,ps21,ps27,ps16,ps18,(6,[(0,1,2),(1,4,5)]),ps9,ps12,ps40,(32,[]),ps38,ps25,ps54,ps42,ps11,ps47,(48,[]),ps32,ps5,(35,[]),ps8,ps10,ps22,ps33,ps2,(51,[]),ps80,(20,[(0,4,5)]),ps85,ps0,ps156,ps23,ps48,ps1,ps28,ps26,ps17,ps20,(50,[]),ps49,(4,[(2,0,3),(1,16,30)]),(49,[]),ps7,ps35,ps13,ps15,ps39,(28,[]),(31,[]),ps46,ps31,(10,[(0,0,2),(0,1,3)]),(13,[(0,1,3)]),ps53,ps81,(18,[(2,4,5)]),ps170,(17,[(2,4,5)]),ps114,ps162,(24,[]),ps36,(16,[(1,4,5)]),ps29,(34,[]),(10,[(1,0,2),(1,1,3)]),ps34,(37,[]),ps41,ps19]
def b8x4 : List NodeSpec := [([59,0,1,232,2,3,4,5],[0,1,2,3,4,5,6,7],[0]),([210,29,0,1,2,3,4,5],[8,9,10,11,12,13],[]),([33,0,1,2,3,294,4,5],[0,14,15,16,17,5,18],[]),([13,0,1,2,200,3,4,5],[19,20,21,13,22,23,16],[]),([6,0,1,74,2,3,4,5],[8,24,19,25,12,26,27],[0]),([0,1,2,173,3,57,4,5],[28,8,29,9,30,31,32],[0,1]),([33,0,326,1,2,3,4,5],[0,20,15,33,17,34],[]),([161,0,1,2,53,3,4,5],[20,35,9,26,17,4,36,5],[]),([0,1,222,2,3,4,5,54],[24,37,38,22,39],[]),([0,1,91,90,2,3,4,5],[0,1,9,35,40,8,2],[0]),([0,1,2,188,3,27,4,5],[8,24,9,37,10],[0]),([47,0,1,314,2,3,4,5],[0,36,13,38,16,41,42],[]),([159,13,0,1,2,3,4,5],[37,24,43,13],[]),([13,0,160,1,2,3,4,5],[24,36,23,22,21,13,35,38,16],[]),([0,150,1,2,3,57,4,5],[20,10,26,8,13,38,12,15,31,44,5,45],[0]),([163,0,1,2,11,3,4,5],[37,8,21,46,47,48,35],[]),([247,0,1,2,246,3,4,5],[1,49,27,46],[]),([16,0,261,1,2,3,4,5],[36,0,38,50,26,39],[]),([89,0,1,2,3,4,5,58],[0,1,2,51,35],[]),([209,0,1,2,3,4,5,58],[20,0,35,3,16,13],[]),([13,0,1,2,3,165,4,5],[8,24,38,21,22,35,31,16,46],[]),([83,0,1,41,2,3,4,5],[20,24,46,52],[]),([10,0,26,1,2,3,57,58],[20,9,53,54,55],[0]),([59,220,0,1,2,3,4,5],[56,57,58,59,38,60,61],[]),([59,0,1,2,290,3,4,5],[0,13,62,26,2,63,5,64],[]),([32,0,1,2,3,162,4,5],[20,55,10,23,18,5,17],[]),([48,0,1,2,3,316,4,5],[65,36,66,47],[]),([248,247,0,1,2,3,4,5],[1,49,27,47],[]),([0,1,2,11,3,27,57,58],[20,9,67,68,37],[0]),([80,0,1,2,77,3,4,5],[9,36,44,20,1,69,17],[]),([12,151,0,1,2,3,4,5],[8,24,10,13,12,16,45],[]),([0,30,1,2,3,315,4,5],[70,36,18,22,16,71],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b8x4Ok : checkNodesBT wires goal (fullMask 100) b8x4Pools autos table7 8 b8x4 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b8x4Mem : ∀ ns ∈ b8x4, Impossible goal 8 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table7OK b8x4Ok
def b8x5Pools : BT (Option BoundPool) := buildPoolsBT 7 wires roots slices [ps5,ps53,(48,[]),ps10,ps47,ps23,ps16,ps3,ps4,ps37,ps43,ps8,ps1,ps26,ps31,ps2,(37,[]),(10,[(1,0,2),(0,11,31)]),(50,[]),ps9,ps24,ps17,ps0,ps27,ps28,ps51,ps20,ps44,ps42,ps12,(35,[]),ps11,ps49,(51,[]),(20,[(1,1,4)]),(49,[]),(0,[(1,1,4),(3,3,4)]),ps22,ps38,ps25,ps46,ps40,ps19,(24,[]),ps50,(31,[]),ps112,(14,[(0,3,4)]),(16,[(0,2,4)]),ps154,ps32,ps15,(12,[(1,0,2),(2,193,53)]),ps33,(10,[(2,0,2),(3,1,3)]),(14,[(0,4,5),(1,4,5)]),ps55,(32,[]),(45,[]),ps14,(47,[]),(15,[(0,1,4)]),ps29,(4,[(0,0,3),(1,14,30)]),ps45,ps6,ps7,ps167,ps81,ps161,ps169,ps35,ps83,ps21,ps36]
def b8x5 : List NodeSpec := [([0,1,2,3,162,4,31,5],[0,1,2,3,4,5,6],[]),([0,1,2,264,3,15,4,5],[7,8,9,10,11,12],[]),([56,0,1,2,193,3,4,5],[0,13,14,15,3,16,17],[0]),([93,0,1,90,2,3,4,5],[7,8,0,12,18,19,20],[0]),([0,224,1,2,53,3,4,5],[13,0,15,11,21,22,3,23,24],[]),([16,0,1,267,2,3,4,5],[24,7,21,25,11,26,15,27,28,9],[]),([168,10,0,1,2,3,4,5],[24,29,30,21,31,32,12],[]),([0,287,1,2,3,289,4,5],[7,33,4,5],[]),([0,1,2,194,193,3,4,5],[29,34,0,13,24,35,16,36],[]),([32,199,0,1,2,3,4,5],[37,13,4,21],[]),([312,0,1,2,3,57,4,5],[29,38,21,37,31,39,40,41,22],[]),([146,0,1,145,2,3,4,5],[19,33,42,10,43],[]),([14,0,261,1,2,3,4,5],[24,7,44,9,45,15],[]),([0,1,132,131,2,3,4,5],[29,46,47,48,0,12,18,38,41,15,21,19,49],[0]),([0,1,2,11,200,3,4,5],[13,0,16,50,39,30,51],[]),([16,0,1,2,264,3,4,5],[24,8,10,25],[]),([199,0,1,2,3,4,31,5],[13,52,4,37,12,5,21,2],[]),([56,0,1,108,2,3,4,5],[0,20,53,25,15,16],[0]),([12,29,0,1,2,3,57,58],[0,29,54,9,7,55],[]),([0,1,2,78,77,3,4,5],[29,8,0,20,24,35,16,56],[]),([35,0,1,2,337,3,4,5],[19,8,11,57,58],[]),([29,146,0,1,2,3,4,5],[19,37,10,41,39,38,0,3,59],[]),([0,1,2,173,3,4,5,58],[0,29,19,12],[0]),([311,25,0,1,2,3,4,5],[8,7,4,21,31,43,60],[]),([0,1,253,2,254,3,4,5],[8,61,7,43,44,62,24,63],[]),([0,1,7,2,3,103,4,5],[7,19,29,5,64],[0]),([59,0,1,131,2,3,4,5],[19,37,29,65,66,67],[0,1]),([311,24,0,1,2,3,4,5],[7,14,8,4,40,15,31,3,21,60],[]),([310,0,1,2,3,57,4,5],[38,22,68,15,40,3,69,28,41,70,66,21,39,10,71],[0]),([168,13,0,1,2,3,4,5],[29,24,30,21,31,32,12,11],[]),([249,0,1,2,3,4,5,58],[8,72,12,73,62,74],[]),([14,0,1,267,2,3,4,5],[24,9,27,7,28,15,11,22,12],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b8x5Ok : checkNodesBT wires goal (fullMask 100) b8x5Pools autos table7 8 b8x5 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b8x5Mem : ∀ ns ∈ b8x5, Impossible goal 8 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table7OK b8x5Ok
def b8x6Pools : BT (Option BoundPool) := buildPoolsBT 6 wires roots slices [ps5,ps12,ps2,ps9,ps38,ps0,ps43,ps4,ps24,ps28,ps3,(43,[]),ps25,ps11,ps50,(4,[(0,0,3),(1,14,30)]),ps22,(51,[]),ps14,ps31,ps16,ps54,ps47,(48,[]),ps10,ps35,ps1,ps17,ps33,(37,[]),(49,[]),ps27,ps80,ps156,(12,[(1,1,2)]),ps36,(45,[]),ps29,ps21,(2,[(1,0,3),(1,1,4),(0,15,31)]),ps37,ps26,ps40,ps20,ps8,(34,[]),ps51,ps7,(16,[(3,2,4)]),(24,[]),ps46,ps13,(50,[]),ps160,ps155,(47,[]),ps59,(15,[(0,1,4)]),ps15,ps48]
def b8x6 : List NodeSpec := [([0,1,117,2,3,57,4,5],[0,1,2,3,4,5,6],[]),([0,1,2,273,3,57,4,5],[7,8,5],[0]),([47,0,1,253,2,3,4,5],[9,10,11,12,13,14,15],[0]),([189,0,1,2,188,3,4,5],[16,4,17,18],[]),([0,150,1,2,3,4,5,58],[0,3,2,12,19,6,20],[0]),([0,30,1,2,3,294,4,5],[10,21,22,23,13,24,20],[]),([0,1,2,11,3,165,4,5],[16,3,25,26,27,13],[]),([110,0,1,108,2,3,4,5],[7,28,0,8,9,27,29,30],[]),([0,1,2,317,3,4,31,5],[9,16,31,26,27,24],[]),([0,1,2,173,3,4,177,5],[0,1,13,24,17,5,32,20,31,3,33],[0]),([0,1,2,288,3,15,4,5],[10,7,34,13,35,36],[0]),([0,1,2,3,301,298,4,5],[0,37,10,23,14,38,39],[]),([0,326,30,1,2,3,4,5],[10,40,0],[]),([265,0,1,2,3,15,4,5],[41,40,19,42,43,24,44,45,46,9],[]),([0,1,90,2,3,57,4,5],[10,7,5,47,1,3],[0]),([0,1,2,120,3,4,5,54],[9,0,2,24,12,27,44],[]),([0,1,2,61,3,4,65,5],[1,0,10,17,5,8,3],[0]),([300,0,1,2,3,298,4,5],[0,10,37,48,9,14,49],[]),([0,250,1,2,3,57,4,5],[7,37,44,2,50,4,24],[0]),([0,1,121,41,2,3,4,5],[7,0,16,24,51,36],[]),([0,1,45,2,3,316,4,5],[37,9,49,51],[]),([0,1,2,274,273,3,4,5],[7,10,26,52,53,8,54],[0]),([55,0,1,222,2,3,4,5],[16,41,55,18],[]),([16,265,0,1,2,3,4,5],[9,7,19,45],[]),([0,1,253,2,3,4,5,256],[9,11,37,24,49,45,10,56,57],[]),([0,1,90,2,3,4,94,5],[0,1,10,17,5,2,44,8,3],[0]),([0,1,2,61,3,57,4,5],[10,7,5,47,0,3],[0]),([0,1,2,3,123,4,42,5],[0,7,24,2,58,59,22],[]),([293,0,1,2,3,4,5,46],[10,5,7,12,23,41,26,2,44],[]),([0,191,1,2,3,57,4,5],[1,42,27,16,12,13,4,5,47,2,25],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b8x6Ok : checkNodesBT wires goal (fullMask 100) b8x6Pools autos table7 8 b8x6 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b8x6Mem : ∀ ns ∈ b8x6, Impossible goal 8 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table7OK b8x6Ok
def buckets8 : BT (CertifiedBucket goal 8) := staticBuckets (btOfList 3 [bucketFragment wires b8x0 b8x0Mem,bucketFragment wires b8x1 b8x1Mem,bucketFragment wires b8x2 b8x2Mem,bucketFragment wires b8x3 b8x3Mem,bucketFragment wires b8x4 b8x4Mem,bucketFragment wires b8x5 b8x5Mem,bucketFragment wires b8x6 b8x6Mem]) [[(0,0,2)],[(0,2,4)],[(0,6,5)],[(0,11,3)],[(0,14,5)],[(0,19,1)],[(0,20,4)],[(0,24,3)],[(0,27,2)],[(0,29,3),(1,0,1)],[(1,1,1)],[(1,2,4)],[(1,6,3)],[(1,9,2)],[(1,11,4)],[(1,15,4)],[(1,19,5)],[],[(1,24,4)],[(1,28,3)],[(1,31,1),(2,0,6)],[(2,6,2)],[(2,8,2)],[(2,10,2)],[(2,12,4)],[(2,16,6)],[(2,22,8)],[(2,30,2),(3,0,3)],[(3,3,4)],[(3,7,2)],[(3,9,4)],[(3,13,3)],[(3,16,5)],[(3,21,3)],[(3,24,3)],[(3,27,4)],[(3,31,1)],[(4,0,6)],[],[(4,6,1)],[(4,7,4)],[(4,11,4)],[(4,15,2)],[(4,17,6)],[(4,23,6)],[(4,29,3),(5,0,1)],[(5,1,1)],[(5,2,3)],[(5,5,4)],[(5,9,6)],[(5,15,5)],[(5,20,3)],[],[(5,23,3)],[(5,26,6),(6,0,2)],[(6,2,5)],[(6,7,5)],[(6,12,1)],[(6,13,4)],[(6,17,2)],[(6,19,3)],[(6,22,1)],[(6,23,5)],[(6,28,2)]]
def table8 := bucketValues buckets8
set_option maxRecDepth 200000 in
lemma table8OK : btAll (fun bk => ∀ xs ∈ bk, Impossible goal 8 xs.toFinset) table8 := bucketValues_ok _
def b9x0Pools : BT (Option BoundPool) := buildPoolsBT 7 wires roots slices [ps4,ps5,ps10,ps30,ps18,ps31,ps14,ps20,(32,[]),ps7,ps21,(0,[]),ps1,ps22,(0,[(0,2,5)]),ps19,ps23,ps85,(20,[(0,4,5)]),ps32,ps37,(5,[(3,0,2),(3,1,3)]),ps159,ps38,ps40,ps48,(45,[]),ps27,ps11,ps3,ps12,ps6,ps26,ps16,ps117,ps28,ps25,ps39,ps45,(35,[]),ps2,ps70,ps9,(14,[(2,4,5)]),ps86,ps67,ps29,ps17,ps8,ps41,ps87,ps33,ps42,ps15,ps56,ps34,ps13,ps50,(6,[(1,3,4)]),ps46,(6,[(0,2,3),(0,4,5)]),ps88,ps55,ps36,ps0,ps118,ps60,ps89,ps24,ps44,ps35,ps61,(8,[(1,0,4)]),(12,[(1,2,3)]),ps49,ps90,ps119,ps91,ps92]
def b9x0 : List NodeSpec := [([214,0,1,2,3,4,5],[0,1,2,3,4,5,6,7,8,9,10,11],[]),([352,0,1,2,3,4,5],[12,13,14,8,15,16,6,7,10],[2]),([29,13,0,1,2,3,57,4,5],[17,18,19,20,21,22,23,24,25,26],[0]),([0,1,292,2,3,4,5],[27,2,28,29,30,31,4,9,10],[]),([0,1,2,207,3,4,5],[32,33,27,20,34,15,16,9,10],[]),([47,16,33,0,1,2,3,4,5],[35,29,28,36,37,38,39,40,27,33,41],[0]),([59,12,29,0,1,2,3,4,5],[42,43,13,24,29,20,1,33,44,45],[0]),([33,0,1,2,11,3,4,5,54],[13,32,46,37,1,47,30],[]),([230,0,1,2,3,4,5],[48,47,49,19],[]),([231,0,1,2,3,4,5],[48,27,32,20],[]),([340,0,1,2,3,4,5],[48,50,38,1,42,15,16,11,9,10],[]),([270,0,1,2,3,4,5],[48,33,35,51,15,16,3,4,9,10],[1]),([87,0,1,2,3,4,5],[1,38,40,48,11,52,6,7,9,10,35,53,3],[]),([10,0,30,1,2,3,4,5,54],[1,13,51,12,54],[0]),([32,14,0,1,45,2,3,4,5],[35,46,13,55,29,48,0],[]),([311,0,1,2,3,4,5],[47,35,49,3,15,16,56,53,31,4],[0,2]),([39,8,0,1,2,3,57,4,5],[1,29,24,37,19,35,25,57,40,36],[0]),([170,0,1,2,3,4,5],[27,58,0,59,15,16,4,9,10,42],[1]),([6,0,1,37,2,3,57,4,5],[29,0,60,35,61,19,57,1,42,62],[0]),([322,0,1,2,3,4,5],[27,47,38,35],[]),([359,0,1,2,3,4,5],[33,32,42,11,63,3,15,16,7,9,10],[]),([262,0,1,2,3,4,5],[28,1,0,4,46,35,56,53,11,3,9,10],[]),([343,0,1,2,3,4,5],[64,29,42,57,12,15,16,6,7],[2]),([0,1,2,205,3,4,5],[30,65,0,27,66,15,16,9,10,47,53],[]),([55,33,10,0,1,2,3,4,5],[35,49,37,13,40,27,30,47,32,39,51,1,54],[0]),([32,56,13,0,1,2,3,4,5],[1,19,32,55,2,20,28,36,67],[0]),([218,0,1,2,3,4,5],[33,35,30,3,47,16,15,7,10,9,68],[]),([219,0,1,2,3,4,5],[68,42,33,7,3,15,16,9,10,69,70,6],[]),([306,0,1,2,3,4,5],[27,71,30,23,15,16,53,9,10,68],[1]),([350,0,1,2,3,4,5],[47,19,72,29,68,3,15,16,9,10],[]),([226,0,1,2,3,4,5],[48,2,0,19,55],[]),([6,0,1,2,3,38,57,4,5],[1,30,35,57,42,73,62,74,37,75,76,77,78],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b9x0Ok : checkNodesBT wires goal (fullMask 100) b9x0Pools autos table8 9 b9x0 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b9x0Mem : ∀ ns ∈ b9x0, Impossible goal 9 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table8OK b9x0Ok
def b9x1Pools : BT (Option BoundPool) := buildPoolsBT 7 wires roots slices [ps28,ps59,ps37,ps51,ps2,ps11,ps25,ps0,ps27,ps8,(43,[]),(8,[(0,1,4)]),ps93,ps4,ps24,ps115,ps17,ps1,ps29,(6,[(1,3,5)]),(2,[(1,3,5)]),ps32,ps5,ps26,ps10,(35,[]),(10,[(3,0,2)]),ps114,ps39,ps44,ps92,ps12,ps18,ps6,ps21,ps7,ps22,ps168,ps55,ps120,ps69,(4,[(3,0,1)]),ps94,ps82,ps68,ps121,ps49,ps46,ps20,ps19,ps23,ps13,ps15,ps85,ps3,ps9,(12,[(1,1,3)]),(45,[]),(48,[]),ps95,ps96,ps54,(12,[(1,1,2)]),ps45,ps16,(26,[]),ps62,ps71,ps14,ps97,ps72,ps57,ps73,ps40,ps42,ps48,ps50,ps34,ps36,ps35,(34,[]),(16,[(1,4,5)]),ps113,ps165,(18,[(1,4,5)]),ps53,ps98,ps41,ps30,(0,[]),(17,[(1,4,5)]),ps31,(24,[]),ps99,ps47,ps33,(47,[]),(16,[(0,4,5)]),ps67,ps167,ps43,(13,[(0,2,3)]),(28,[]),ps100,(2,[(1,0,1),(0,4,5)]),(12,[(1,2,3)]),ps52,(10,[(1,0,1)]),ps101]
def b9x1 : List NodeSpec := [([14,0,30,1,2,3,4,5,46],[0,1,2,3,4,5,6,7,8,9,10,11,12],[0]),([0,1,7,41,2,3,4,5,54],[13,14,15,16,17,8,18,19,20],[0]),([56,13,0,1,2,3,4,31,5],[21,22,23,24,2,5,25,6,26],[0]),([24,14,0,1,2,3,57,4,5],[13,27,18,28,29,0,30],[0]),([312,0,1,2,3,4,5],[5,8,31,32,33,34,35,36],[0]),([6,0,1,2,3,57,58],[37,31,38,39,40,22,7,41,42,43,44,45],[0]),([0,371,1,2,3,4,5],[7,18,16,46,47,48,49,50,51,52],[2]),([10,0,1,2,3,27,57,4,5],[22,53,0,13,54,55,56,46,57,58,59,60],[0]),([14,0,22,1,2,3,57,4,5],[54,13,14,28,0],[0]),([0,1,2,23,3,15,57,4,5],[13,14,61,62],[0]),([47,33,14,0,1,2,3,4,5],[54,0,25,28,63,6,8,64,4,12],[0]),([13,0,30,1,2,3,4,5,54],[36,23,21,6,10,16,65,20,66],[0]),([73,0,1,2,3,4,5],[36,38,55,67,51,52,68,48,69,32],[0]),([0,229,1,2,3,4,5],[9,8,21,13],[1]),([0,1,102,2,3,4,5],[54,70,13,71,51,52,68,48,72,33],[0]),([39,6,0,1,2,3,57,4,5],[22,54,0,21,73,74,75,76,4,6,38,60],[0]),([25,0,1,2,3,15,4,5,58],[54,77,31,13,14,6,78,23,79,80,81,82,83],[]),([29,10,0,1,2,3,4,5,58],[22,84,55,79,77,85,86],[0]),([373,0,1,2,3,4,5],[64,55,54,21,48,87,88,89,49,50,33,32],[]),([24,0,1,2,3,15,4,5,58],[81,63,54,90,14,78,91,9,23,92,93,94,83],[0]),([55,33,13,0,1,2,3,4,5],[21,23,25,87,28,5,16,31,8,66],[0]),([28,10,0,1,2,3,57,4,5],[22,28,13,31,55,4,95,0,29,96,97,98,99],[]),([310,0,1,2,3,4,5],[9,6,32,33,34,35],[0,1]),([8,0,1,37,2,3,4,5,58],[13,22,100,92,77,101,54,102,9,103],[0]),([263,0,1,2,3,4,5],[77,0,24,5,6,51,52,35,34,79,89,50,88],[]),([0,339,1,2,3,4,5],[8,9,13,63],[0]),([0,1,117,2,3,4,5],[24,9,22,55],[0]),([0,1,7,2,3,38,57,4,5],[54,13,104,105,76,15,31,29,75,55],[0]),([0,1,2,273,3,4,5],[5,24,64,8,33,32,35,34],[0,1]),([318,0,1,2,3,4,5],[6,0,77,24,88,5,51,52,34,35],[]),([0,369,1,2,3,4,5],[7,14,9,29,49,50,89,68,48,22],[2]),([0,1,7,2,3,57,58],[40,54,106,107,108,13,17,43,42,45,44],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b9x1Ok : checkNodesBT wires goal (fullMask 100) b9x1Pools autos table8 9 b9x1 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b9x1Mem : ∀ ns ∈ b9x1, Impossible goal 9 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table8OK b9x1Ok
def b9x2Pools : BT (Option BoundPool) := buildPoolsBT 7 wires roots slices [ps113,ps3,ps41,ps12,ps24,ps36,ps4,ps34,(17,[(1,4,5)]),ps83,(24,[]),ps35,ps47,(20,[(0,4,5)]),ps40,ps37,ps22,ps85,ps38,(45,[]),ps58,ps95,ps33,ps48,ps67,ps163,ps11,ps0,ps9,ps13,ps15,ps14,ps20,ps2,ps17,ps25,ps6,ps18,ps7,ps21,ps16,ps5,ps32,ps23,ps19,ps45,(5,[(2,0,3),(2,1,2)]),ps164,ps10,ps30,(0,[]),(10,[(2,0,3)]),ps26,(35,[]),(5,[(3,0,2),(3,1,3)]),(18,[(3,4,5)]),(17,[(3,0,2)]),(15,[(3,1,3)]),ps43,ps159,ps8,ps51,(10,[(3,0,2)]),ps44,ps122,ps54,ps63,ps74,ps39,ps1,ps50,ps27,(7,[(0,3,5)]),(8,[(0,0,1),(1,4,5)]),(13,[(0,2,3)]),(34,[]),ps84,ps168,ps56,(10,[(0,0,2)]),ps94,ps62,ps69,ps116,ps68,ps121,ps82,ps102,(10,[(0,2,3)]),(4,[(3,2,3)]),ps101,ps31,ps123,ps166,ps59,ps60]
def b9x2 : List NodeSpec := [([16,25,0,1,2,3,4,5,58],[0,1,2,3,4,5,6,7,8,9,10,11,12],[0]),([29,0,1,2,11,3,57,4,5],[13,3,14,15,16,17,18,19,20,21,22,23,24,25],[0]),([335,0,1,2,3,4,5],[26,27,6,28,29,30,31,32],[]),([0,1,104,2,3,4,5],[33,34,35,1,4,32,36,37,38,39],[0]),([0,1,2,3,351,4,5],[40,41,1,32,4,42,34,43,44,37,39,38],[]),([32,12,0,1,2,53,3,4,5],[41,45,16,6,27,28],[0]),([16,24,0,1,2,3,4,5,58],[9,46,8,47,45,2],[0]),([328,0,1,2,3,4,5],[48,11,7,28,37,30,29,49,50,39,38],[]),([0,1,314,2,3,4,5],[35,51,26,48,2,29,30,39,38],[0]),([204,0,1,2,3,4,5],[34,40,52,5,44,43,32,50,38,39],[1]),([12,0,1,2,53,3,4,31,5],[41,45,53,4,28,35,26,48],[0]),([29,13,0,1,2,3,4,5,58],[54,41,3,52,7,55,56,57,58,11,9,8,48,40,59],[0]),([0,1,115,2,3,4,5],[6,42,60,33,52,50,31,32,38,39,30,29],[]),([0,1,90,2,3,4,5],[35,33,60,34,36,37,38,39],[0,1]),([32,17,0,1,45,2,3,4,5],[1,15,7,6,27,48,61,41],[]),([0,250,1,2,3,4,5],[60,40,26,48,37,36,39,38],[0,1]),([0,1,222,2,3,4,5],[60,48,52,62],[0]),([0,1,2,3,216,4,5],[40,41,4,63,34,49,43,44,32,39,38],[1]),([0,1,2,3,298,4,5],[64,48,26,65,5,29,30,38,66],[0]),([32,56,0,1,2,11,3,4,5],[41,16,7,23,15,67],[0]),([40,36,0,1,2,3,4,19,5],[3,6,68,69,16,60,48,26,34,70],[0]),([8,0,1,2,53,3,4,42,5],[41,6,40,28,71,27,69,60,33,23,72],[0]),([342,0,1,2,3,4,5],[60,27,28,44,43,31,32],[2]),([6,0,1,37,2,3,4,5,58],[41,73,3,28,74,58,75,76],[0]),([10,0,1,2,3,57,58],[77,78,79,80,58,41,69,81,82,83,84,85],[0]),([0,1,37,2,3,57,58],[86,6,87,88,84,1,69,89,77,90,83,82],[0]),([0,1,353,2,3,4,5],[69,3,60,75,23,27,44,43,31,32],[2]),([56,0,1,2,11,3,4,31,5],[41,52,91,33,15,48,35,53,71,40,92],[0]),([17,0,30,1,2,3,4,5,46],[1,15,28,61,4,33,48,26],[0]),([25,14,0,1,2,3,4,5,58],[6,4,3,7,9,52,75,93,12,94,0],[]),([0,1,2,61,3,4,5],[60,33,34,35,36,37,38,39],[0,1]),([0,1,2,193,3,4,5],[95,26,48,91,20,33,31,32,38],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b9x2Ok : checkNodesBT wires goal (fullMask 100) b9x2Pools autos table8 9 b9x2 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b9x2Mem : ∀ ns ∈ b9x2, Impossible goal 9 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table8OK b9x2Ok
def b9x3Pools : BT (Option BoundPool) := buildPoolsBT 7 wires roots slices [ps10,ps36,ps29,ps40,ps23,ps17,ps13,ps15,ps20,ps7,ps21,ps94,ps5,(10,[(1,2,3)]),ps124,ps68,ps12,ps0,ps168,ps101,ps116,ps69,ps28,ps3,ps25,ps11,ps45,(43,[]),ps49,ps2,ps51,ps27,ps16,ps64,ps4,ps41,ps22,ps39,ps1,ps83,ps42,(17,[(1,4,5)]),ps46,ps47,(24,[]),ps59,ps125,(16,[(1,4,5)]),ps166,ps9,ps35,ps8,(0,[]),ps19,ps18,ps52,ps126,ps115,ps24,ps14,ps31,ps103,ps57,(26,[]),ps30,ps6,(7,[(0,0,3),(1,4,5)]),(6,[(0,1,2),(1,4,5)]),(13,[(0,1,2)]),(31,[]),(28,[]),ps104,ps32,ps165,(1,[(1,0,3),(1,4,5)]),ps26,ps34,ps43,ps113,(6,[(1,3,5)]),ps127,(35,[]),ps75,ps128,(10,[(2,2,3)]),ps102,ps62,(10,[(3,0,2)]),ps56,ps121,(13,[(0,2,3)]),(6,[(1,4,5)]),ps129,ps130,ps98,(7,[(0,0,2),(0,4,5)]),ps167,ps33,(49,[]),(48,[]),ps44,(16,[(0,4,5)]),ps67,(32,[]),(2,[(3,0,4)]),(0,[(1,2,3),(1,4,5)]),ps72]
def b9x3 : List NodeSpec := [([0,1,2,3,126,4,5],[0,1,2,3,4,5,6,7,8,9,10],[1]),([0,1,2,3,38,57,58],[11,12,13,14,15,16,17,18,19,20,21],[0]),([47,16,0,30,1,2,3,4,5],[22,23,24,25,26,27,28,29,30,31,32,33],[0]),([55,6,0,1,41,2,3,4,5],[22,34,35,29,16,32,31],[0]),([12,33,0,1,2,3,4,5,54],[12,36,37,25,38,16,23],[]),([24,14,0,1,2,3,4,5,58],[39,34,40,26,2,41,42,43,44,45,46,47,48],[0]),([0,331,1,2,3,4,5],[32,23,49,50,51,52,53,4,54,9,10],[1]),([0,191,1,2,3,4,5],[24,32,25,0],[0,1]),([0,1,114,2,3,4,5],[29,55,56,57,58,59,8,9],[]),([0,1,2,212,3,4,5],[25,60,58,12,7,54,22,59,8,9,10],[]),([334,0,1,2,3,4,5],[23,61,34,62,53,4,6,7,63,64,65],[2]),([14,0,22,1,2,3,4,5,58],[66,67,23,45,58,42,40,34,68,41,39,69,70,60,1],[0]),([0,272,1,2,3,4,5],[51,34,45,32,71,4,53,10,72],[]),([0,1,2,23,3,15,4,5,58],[73,74,34,58,60,1,75,76,51,43,24,44,77,50,78,47],[0]),([130,0,1,2,3,4,5],[0,34,49,22,64,76,6,7,59,8,65,54],[]),([344,0,1,2,3,4,5],[17,2,79,63,53,4,6,7,8],[2]),([75,0,1,2,3,4,5],[51,24,12,65,54,9,10,49],[0]),([164,0,1,2,3,4,5],[12,29,0,34,7,59,8,9,10,72,4,64],[]),([0,1,108,2,3,4,5],[23,80,57,51,55,59,8,9,29,52],[0,3]),([55,33,0,1,2,11,3,4,5],[36,75,35,37,16,81,5,31],[]),([55,10,0,30,1,2,3,4,5],[22,36,35,12,0,75,81,5,82],[0]),([39,0,1,2,3,57,58],[15,23,83,84,11,12,85,19,18,21,20],[]),([44,8,0,1,2,3,4,5,54],[12,36,51,72,2],[0]),([13,0,1,2,3,57,58],[19,72,75,11,86,87,88,21,20,15,89],[0,2]),([76,0,1,2,3,4,5],[24,51,12,49,29,52,54,65,10,9],[0]),([0,1,232,2,3,4,5],[25,0,31,32,65,54,9,10],[0,1]),([0,1,7,37,2,3,4,5,58],[23,76,16,58,24,50,12,29,5,90,75,77,91,92,93,94,55],[0]),([10,0,26,1,2,3,57,4,5],[95,96,16,49,97,27,37,22,98,99,29,5,28,100,101,102],[0]),([0,1,2,217,3,4,5],[16,49,32,8,103,64,53,4,34,9,10,54],[]),([149,0,1,2,3,4,5],[31,25,0,34,12,54,65,10,9],[]),([366,0,1,2,3,4,5],[26,22,104,5,51,53,4,8,9,10,28],[]),([0,1,7,2,3,38,4,5,58],[12,16,49,75,105,55,26,106],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b9x3Ok : checkNodesBT wires goal (fullMask 100) b9x3Pools autos table8 9 b9x3 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b9x3Mem : ∀ ns ∈ b9x3, Impossible goal 9 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table8OK b9x3Ok
def b9x4Pools : BT (Option BoundPool) := buildPoolsBT 7 wires roots slices [(1,[(1,0,2),(0,4,5)]),ps163,ps5,ps58,ps9,ps38,ps40,ps12,(12,[(1,1,3)]),ps85,(20,[(0,4,5)]),(45,[]),ps48,ps33,(43,[]),ps28,ps3,ps45,ps25,ps11,ps2,ps51,ps27,ps16,ps65,ps24,ps18,(0,[]),ps19,ps23,ps7,ps21,ps44,ps35,ps1,(26,[]),(37,[]),ps30,ps13,ps15,ps20,ps22,ps17,ps26,ps34,(17,[(1,0,2)]),(17,[(1,4,5)]),(18,[(1,4,5)]),ps129,ps4,ps105,ps71,ps104,(32,[]),ps10,ps59,ps68,ps63,ps131,ps101,ps0,ps116,ps69,ps82,ps94,ps32,ps41,(35,[]),ps132,ps39,(47,[]),(16,[(0,4,5)]),ps42,(28,[]),(24,[]),ps52,ps133,ps8,ps14,ps29,(18,[(2,4,5)]),ps67,ps66,ps6,(16,[(2,4,5)]),ps47,ps50,(16,[(1,4,5)]),ps76,ps81,ps37,ps49,ps83,ps99,ps100,ps123,ps57,ps74,ps134,ps64,(10,[(2,0,3)]),ps43,ps135,ps136]
def b9x4 : List NodeSpec := [([0,1,2,11,3,27,57,4,5],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14],[0]),([47,14,0,30,1,2,3,4,5],[15,16,14,17,18,19,20,21,22,23,24],[0]),([332,0,1,2,3,4,5],[25,4,23,22,26,27,28,29,30,31,32,33],[]),([364,0,1,2,3,4,5],[34,35,16,36,37,28,29,38,39,40],[2]),([29,0,1,2,11,3,4,5,58],[7,41,2,42,33,43,44,45,19,46,47,48],[0]),([247,0,1,2,3,4,5],[49,50,51,52,28,29,38,39,4,27],[0]),([0,1,2,330,3,4,5],[7,4,23,53,40,26,37,28,29,49,30,31,39],[]),([0,1,253,2,3,4,5],[52,54,19,14,55,18,38,39,31],[0]),([0,1,2,3,15,57,58],[56,16,57,58,59,60,61,62,63,64],[0]),([55,13,0,30,1,2,3,4,5],[65,43,41,66,23,67,22,68],[0]),([28,0,1,2,11,3,57,4,5],[7,4,49,69,10,15,12,70,3,71,1],[]),([39,0,1,7,2,3,4,5,58],[16,2,43,66,72,6,73,18,20,74,75,76],[0]),([362,0,1,2,3,4,5],[77,34,7,28,29,40,78],[2]),([0,1,2,113,3,4,5],[60,16,2,23,34,37,27,28,29],[]),([35,18,0,1,37,2,3,4,5],[4,49,79,77,18,44,53,74,20],[0]),([59,29,10,0,1,2,3,4,5],[4,80,36,44,2,23,22,5,33,81,82],[0]),([220,0,1,2,3,4,5],[77,18,83,26,30,31],[0,1]),([227,0,1,2,3,4,5],[77,69,43,19,27,78,40,28,30,31],[]),([0,203,1,2,3,4,5],[43,69,19,54,20,39,78,40,30,31,32,28],[]),([0,1,2,290,3,4,5],[20,54,18],[0,1]),([59,24,0,1,2,3,15,4,5],[16,84,74,85,22,23,49,25,32,69,86,87,88,89],[0]),([20,36,0,1,37,2,3,4,5],[49,65,43,69,16,77,19],[]),([12,29,0,1,2,3,57,4,5],[81,7,4,90,16,6,15,10,9,91,11,12],[0]),([40,8,0,1,2,3,4,5,58],[49,2,7,44,17,73,74],[0]),([14,0,1,2,23,3,4,5,58],[49,92,44,2,7,79,55,74,33,73,93,94],[0]),([0,1,2,188,3,4,5],[41,95,96,97,16,28,29,78,40,39],[0]),([0,1,2,3,358,4,5],[77,98,7,43,28,29,4,26,30,31],[]),([16,0,1,2,3,57,58],[56,15,66,59,99,100,24,62,61,64,63],[0,2]),([25,17,0,1,2,3,4,5,58],[49,25,101,33,43,44,2],[]),([0,1,74,2,3,4,5],[16,102,49,103,37,27,28,29,88,83],[0]),([20,36,0,1,2,3,38,4,5],[4,7,43,69,20,41],[]),([161,0,1,2,3,4,5],[19,20,2,15,78,40,37,26,30,31],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b9x4Ok : checkNodesBT wires goal (fullMask 100) b9x4Pools autos table8 9 b9x4 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b9x4Mem : ∀ ns ∈ b9x4, Impossible goal 9 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table8OK b9x4Ok
def b9x5Pools : BT (Option BoundPool) := buildPoolsBT 7 wires roots slices [ps1,ps22,ps11,ps24,ps10,ps13,ps15,ps14,ps20,ps3,(14,[(2,4,5)]),ps47,ps4,ps41,ps25,(9,[(3,1,2)]),ps113,ps2,ps34,ps81,(5,[(2,0,3),(2,1,2)]),(17,[(2,4,5)]),ps164,(24,[]),ps27,ps16,ps114,ps29,ps60,ps137,ps7,ps21,ps101,ps12,ps123,ps94,ps116,ps69,ps121,ps68,ps9,ps131,ps66,ps26,ps19,ps23,ps57,(18,[(2,4,5)]),(5,[(3,0,2),(3,1,3)]),(20,[(2,4,5)]),ps38,ps159,ps40,ps85,ps8,ps32,ps39,ps17,(8,[(3,0,4)]),ps28,ps30,ps42,ps88,ps5,(13,[(0,1,3)]),ps53,ps168,ps65,ps104,ps0,ps77,ps82,ps45,(6,[(2,2,4)]),(47,[]),(28,[]),ps54,(0,[]),ps44,ps18,ps71,(10,[(2,0,2)]),ps78,ps35,ps62,ps6,ps79,ps84,ps55,(35,[]),ps50,ps138,ps83,ps73,ps51,ps36]
def b9x5 : List NodeSpec := [([0,346,1,2,3,4,5],[0,1,2,3,4,5,6,7,8],[]),([59,16,25,0,1,2,3,4,5],[9,10,11,12,1,13,3,14,15,16],[0]),([0,1,2,120,3,4,5],[4,17,12,18],[0]),([59,16,24,0,1,2,3,4,5],[19,20,21,22,23,12,11,24,25,26],[0,2]),([0,1,2,116,3,4,5],[4,17,12,27],[0]),([0,1,2,201,3,4,5],[4,28,29,12,1,7,8,30,31,18],[]),([0,1,2,11,3,57,58],[32,33,34,28,35,0,36,37,38,39],[0]),([0,1,2,3,289,4,5],[40,41,9,42,43,44,45,5,6,46,31],[0,2]),([59,29,13,0,1,2,3,4,5],[47,48,49,50,51,52,25,24,53],[0,2]),([119,0,1,2,3,4,5],[54,4,24,12,27],[0]),([20,39,36,0,1,2,3,4,5],[40,55,17,56,43,1,33,9,2],[]),([0,1,2,365,3,4,5],[57,58,12,59,45,44,3,60,31,30],[]),([59,6,0,1,37,2,3,4,5],[40,9,17,14,55,52,61,62],[0]),([10,0,26,1,2,3,4,5,58],[63,33,40,64,65],[0]),([14,0,1,2,3,57,58],[66,12,67,68,39,69,70,37,36,35,71],[0]),([271,0,1,2,3,4,5],[59,25,24,72,73,44,45,30,31],[]),([345,0,1,2,3,4,5],[69,12,57,74,75,0,44,45,5,6],[2]),([0,1,2,3,308,4,5],[24,76,3,63,77,78,79,44,45,30],[]),([118,0,1,2,3,4,5],[4,25,17,63,40],[0]),([0,1,2,11,3,27,4,5,58],[63,33,40,18,43],[0]),([210,0,1,2,3,4,5],[1,80,81,40,44,45,7,8,82,31],[0]),([124,0,1,2,3,4,5],[4,17,72,59],[]),([129,0,1,2,3,4,5],[4,83,18,40,60,5,6,8,7,30,31],[]),([0,224,1,2,3,4,5],[54,84,2,4,55,8,7,31,30],[0]),([0,1,131,2,3,4,5],[2,4,25,24,85,79,30,31],[0,1]),([0,1,2,77,3,4,5],[33,86,87,17,88,7,8,31,54,77],[0]),([0,1,2,190,3,4,5],[4,25,24,12,33,85,79,30,31],[]),([55,12,33,0,1,2,3,4,5],[59,1,9,33,89,63,56,25,43,14],[]),([59,24,14,0,1,2,3,4,5],[12,19,56,27,11,14,25,78,90,91,92,93],[0]),([32,48,0,1,2,3,15,4,5],[43,18,55,27,24,14,12,54,59,94,95,9,41],[0]),([33,0,1,2,3,15,4,5,46],[9,76,27,24,33,14,59,25,0,3],[0]),([148,0,1,2,3,4,5],[2,24,63,85,79,30,31,40],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b9x5Ok : checkNodesBT wires goal (fullMask 100) b9x5Pools autos table8 9 b9x5 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b9x5Mem : ∀ ns ∈ b9x5, Impossible goal 9 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table8OK b9x5Ok
def b9x6Pools : BT (Option BoundPool) := buildPoolsBT 7 wires roots slices [ps8,ps17,ps28,ps33,ps4,ps3,ps27,ps16,ps39,ps24,(49,[]),ps166,ps165,ps11,ps47,(45,[]),(24,[]),ps63,(4,[(1,1,2)]),ps5,ps53,ps22,ps2,ps0,ps26,ps9,ps29,ps32,ps31,ps106,ps19,ps23,ps15,ps13,(10,[(1,2,3)]),ps78,ps30,(0,[]),ps66,ps21,ps61,ps14,ps20,ps7,(7,[(1,2,4)]),ps18,(35,[]),ps25,ps10,ps35,ps12,ps6,(8,[(0,1,4)]),(10,[(0,0,2)]),ps1,ps37,ps36,ps54,ps34,ps41,ps51,(10,[(2,0,3)]),(9,[(3,1,4)]),ps113,(37,[]),ps45,ps43,ps38,(31,[]),ps40,ps52,(47,[]),ps107,ps44,ps49,(43,[]),ps46,(20,[(0,4,5)]),(17,[(1,0,2)]),ps139,(17,[(2,4,5)]),(18,[(2,4,5)]),ps97,ps137]
def b9x6 : List NodeSpec := [([0,1,2,3,321,4,5],[0,1,2,3],[1]),([59,14,0,22,1,2,3,4,5],[4,5,6,7,8,2,9,10,11],[0,2]),([59,0,1,2,23,3,15,4,5],[5,4,9,12,13,14,15,16,17,18],[0,2]),([32,10,0,1,2,53,3,4,5],[19,20,21,6,4,22,23,24,7,25],[0]),([48,0,1,2,3,15,4,31,5],[26,24,27,5,13,2,28,0,29],[0]),([372,0,1,2,3,4,5],[1,23,4,30,31,32,33],[2]),([0,1,2,3,103,4,5],[25,34,21,35,36,37,30,31,38,39],[0]),([374,0,1,2,3,4,5],[6,23,19,9,36,37,31,30],[]),([105,0,1,2,3,4,5],[22,40,4,28,41,42,32,43,39,9],[0]),([86,0,1,2,3,4,5],[0,44,19,2,41,42,45,43,39],[3]),([10,0,1,2,53,3,4,31,5],[19,20,27,25,46,47,23,6,48,13,7],[0]),([0,327,1,2,3,4,5],[4,25,48,13,49,33,32,45,43,39,26,37,36],[]),([0,252,1,2,3,4,5],[13,7,6,4,50,45,51,39,43],[]),([0,1,152,2,3,4,5],[52,13,48,20,3,41,42,39,53],[0]),([0,1,85,2,3,4,5],[23,4,50,6,54,36,37,30,31],[]),([0,1,2,349,3,4,5],[6,1,50,55],[0]),([0,1,2,3,228,4,5],[0,1,24,56],[1]),([0,1,2,3,304,4,5],[48,47,57,58,33,32,37,43],[]),([32,16,48,0,1,2,3,4,5],[2,59,60,58,27,0,6,13,48,61],[0]),([16,33,0,1,2,3,4,5,46],[2,59,50,22,0,13,6,48,62],[0]),([12,29,0,1,2,3,4,5,58],[19,63,50,25,58,49,64,65],[0]),([0,1,2,361,3,4,5],[23,21,0,66,67,37,30,31,41,42],[2]),([59,0,1,7,2,3,38,4,5],[25,5,47,22,68,69,65,70],[0]),([16,48,0,1,2,3,4,31,5],[2,26,71,27,7,60,6,72],[0]),([0,1,2,320,3,4,5],[1,6,50,59],[1]),([0,1,2,3,169,4,5],[19,1,3,6,7,20,30,31,39,32,45],[1]),([28,12,0,1,2,3,57,4,5],[19,50,25,73,8,2,74,5],[]),([324,0,1,2,3,4,5],[5,19,7,13,48,6,51,45,43,39],[]),([0,1,127,2,3,4,5],[48,75,25,76,31,32,33,42,45,39,43],[1]),([0,1,2,3,363,4,5],[23,5,1,25,36,30,49,31,33,32],[2]),([59,29,0,1,2,11,3,4,5],[21,77,25,58,67,50,64,78,13,7,22,49,79,80,81,82],[0]),([32,13,0,1,2,53,3,4,5],[27,24,4,47,6,1,13,48,83],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b9x6Ok : checkNodesBT wires goal (fullMask 100) b9x6Pools autos table8 9 b9x6 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b9x6Mem : ∀ ns ∈ b9x6, Impossible goal 9 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table8OK b9x6Ok
def b9x7Pools : BT (Option BoundPool) := buildPoolsBT 7 wires roots slices [ps5,ps32,ps39,ps29,ps11,ps22,ps12,ps1,ps0,(32,[]),ps50,ps19,ps23,ps13,(0,[]),ps14,ps20,ps26,ps27,ps16,ps8,ps7,ps21,ps17,ps24,(37,[]),ps15,(35,[]),ps25,ps10,(2,[(1,1,4)]),ps89,ps28,ps64,ps9,ps34,ps37,ps51,ps2,ps3,ps6,ps18,ps30,ps104,(9,[(3,1,4)]),ps58,ps60,ps41,ps4,ps45,ps48,(3,[(3,1,4)]),ps101,ps77,(10,[(3,0,3)]),ps68,ps65,ps69,ps116,ps94,ps82,ps53,ps35,ps49,(10,[(2,0,2)]),ps108,ps56,ps121,ps55,(7,[(3,2,4)]),ps84,ps76,ps109,ps71,ps43,ps47]
def b9x7 : List NodeSpec := [([33,10,0,1,2,3,4,5,54],[0,1,2,3,4,5,6,7],[0]),([370,0,1,2,3,4,5],[8,9,0,10,11,12,13,14,15,16],[2]),([0,1,309,2,3,4,5],[17,18,19,1,20,14,11,12,21,22,13],[]),([0,1,2,355,3,4,5],[7,0,23,24,8,11,25,12,13,26],[2]),([13,0,1,2,53,3,4,31,5],[17,1,27,28,29,4,23,18,30,31],[0]),([0,1,2,3,316,4,5],[23,4,32,33],[0]),([35,40,18,0,1,2,3,4,5],[6,34,20,35,3],[0]),([56,0,1,7,2,3,4,42,5],[0,24,36,20,37,38,39,28,27],[0]),([89,0,1,2,3,4,5],[38,23,39,40,41,21,22,24],[0]),([192,0,1,2,3,4,5],[29,39,6,17,5,42,11,15,16,12,14,21,22],[]),([209,0,1,2,3,4,5],[4,19,28,39,24],[0]),([0,266,1,2,3,4,5],[4,43,44,6,26,13,22,21,3,2],[]),([0,1,2,206,3,4,5],[23,6,45,19,46,11,12,47,21],[]),([20,40,36,0,1,2,3,4,5],[6,48,17,2,5,10,4,23,20],[]),([32,48,14,0,1,2,3,4,5],[3,32,35,1,48,37,20,18],[]),([43,8,0,1,2,53,3,4,5],[0,48,49,8,34,50,18,20,38],[0]),([33,14,0,1,2,3,4,5,46],[32,3,6,7,38,20,18,8,51],[0]),([17,0,1,2,3,57,58],[52,48,53,54,55,7,39,56,57,58,59,60],[2]),([172,0,1,2,3,4,5],[18,61,34,39,62,26,14,12,11,41,22],[]),([128,0,1,2,3,4,5],[29,63,3,32,42,13,26,15,16,21,22],[]),([221,0,1,2,3,4,5],[20,1,17,14,22,11,12,15,16,40],[2]),([12,0,1,2,3,57,58],[59,0,64,65,52,6,8,66,57,58,55,67],[0]),([33,13,0,1,2,3,4,5,54],[1,17,3,2,0,23,4,6],[0]),([88,0,1,2,3,4,5],[20,68,69,70,5,16,15,22],[]),([146,0,1,2,3,4,5],[34,71,72,39,32,11,12,15,16,73,40],[0]),([0,166,1,2,3,4,5],[4,38,61,2,16,15,41,22],[]),([367,0,1,2,3,4,5],[19,32,24,16,63,14,11,12,42,21,22],[]),([84,0,1,2,3,4,5],[18,8,6,3,42,14,11,12],[]),([333,0,1,2,3,4,5],[19,17,34,14,74,26,12,11,13,22,21],[]),([368,0,1,2,3,4,5],[18,23,49,32],[]),([171,0,1,2,3,4,5],[47,32,23,18,19,11,12,42,21,22,16],[]),([32,0,1,45,2,3,15,4,5],[39,3,5,35,75,28,48,17,8,32],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b9x7Ok : checkNodesBT wires goal (fullMask 100) b9x7Pools autos table8 9 b9x7 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b9x7Mem : ∀ ns ∈ b9x7, Impossible goal 9 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table8OK b9x7Ok
def b9x8Pools : BT (Option BoundPool) := buildPoolsBT 7 wires roots slices [ps5,ps4,ps27,ps29,ps1,ps16,ps0,(28,[]),ps2,ps8,(0,[(1,3,5)]),ps10,ps25,ps3,ps26,ps13,ps15,ps23,(0,[]),ps7,ps21,ps11,ps44,ps24,ps39,ps30,ps20,ps14,ps19,(9,[(0,0,4)]),(13,[(0,2,3)]),ps17,ps33,ps79,ps12,ps104,ps36,ps54,(2,[(1,0,4)]),(12,[(1,2,3)]),ps6,ps18,ps37,ps41,ps32,ps9,(43,[]),ps131,ps22,ps167,ps42,ps40,ps38,(11,[(0,1,3)]),ps75,ps67,ps85,ps28,(45,[]),ps110,ps48,ps51,ps34,ps31,ps163,(8,[(2,1,4)]),(16,[(0,4,5)]),ps90,ps114,(9,[(2,0,4)]),ps58,(35,[]),ps122,ps74,(10,[(2,0,3)]),(9,[(0,2,5)]),ps49,(47,[])]
def b9x8 : List NodeSpec := [([8,0,1,41,2,3,4,5,54],[0,1,2,3,4,5,6,7,8,9,10],[0]),([293,0,1,2,3,4,5],[11,12,13,14,15,16,17,18,19,20],[0]),([215,0,1,2,3,4,5],[21,22,23,24,25,18,17,26,27,28,20,19],[]),([0,1,2,337,3,4,5],[1,9,29,30,31,32,28,17,26,20],[0]),([0,1,2,269,3,4,5],[1,33,34,2,35,28,17,19,20,9,18],[]),([0,1,2,3,307,4,5],[13,9,36,2,5,37,18,28,17,19],[1]),([0,1,2,3,347,4,5],[34,31,38,39,9,36,28,17,26,19],[0]),([208,0,1,2,3,4,5],[13,0,5,21,11,26,40,41,19,20],[]),([360,0,1,2,3,4,5],[9,2,34,42,14],[]),([323,0,1,2,3,4,5],[9,31,43,44],[]),([0,341,1,2,3,4,5],[5,13,0,41,18,43,45,28,17,19,20],[]),([0,1,325,2,3,4,5],[11,46,0,13,16,15,26,25,18,17,20,19,45,14],[]),([0,1,45,2,3,15,4,31,5],[13,3,36,6,47],[0]),([0,1,2,173,3,4,5],[21,11,5,2,40,41,19,20],[0,1]),([59,10,0,26,1,2,3,4,5],[45,48,0,49,11,50,51,52,53,54],[0,2]),([29,10,0,1,2,3,57,4,5],[55,42,0,56,45,51,32,57,58,5,59,60,49],[0]),([0,30,1,2,3,15,4,5,46],[13,37,2,42,4,23,12,57,21,5,61,8,46],[0]),([59,0,1,2,11,3,27,4,5],[45,48,5,2,62,14,0,63,64],[0,2]),([32,0,1,2,11,53,3,4,5],[48,14,1,6,12,45,31,4,65],[0]),([24,0,1,2,3,15,57,4,5],[13,66,23,22,1,0,12,5,24,37,67,68],[0]),([125,0,1,2,3,4,5],[9,11,1,44,62],[]),([356,0,1,2,3,4,5],[21,4,13,48,15,16,26,27],[]),([329,0,1,2,3,4,5],[13,45,21,11,34,15,16,19,20,17,18,25,28],[]),([0,305,1,2,3,4,5],[13,12,21,34,18,15,16,19,20,17,28,14,24],[]),([32,16,0,1,45,2,3,4,5],[57,43,48,62,13,9,21,11],[0]),([319,0,1,2,3,4,5],[21,31,43,24],[]),([249,0,1,2,3,4,5],[21,5,1,40,41,19,20,3],[0]),([0,1,357,2,3,4,5],[14,69,44,9,31,28,17,26,19,20],[]),([0,1,2,11,53,3,4,31,5],[14,70,71,48,8,0,63,2,44,31,12,4,72,73],[0]),([16,0,1,45,2,3,4,31,5],[57,3,2,8,34,9,74,75],[0]),([0,150,1,2,3,4,5],[12,21,8],[0,1]),([16,25,0,1,2,3,57,4,5],[13,55,23,76,1,57,44,77],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b9x8Ok : checkNodesBT wires goal (fullMask 100) b9x8Pools autos table8 9 b9x8 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b9x8Mem : ∀ ns ∈ b9x8, Impossible goal 9 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table8OK b9x8Ok
def b9x9Pools : BT (Option BoundPool) := buildPoolsBT 6 wires roots slices [ps28,ps41,ps51,ps2,ps8,ps27,ps10,ps11,ps70,(9,[(0,1,4)]),ps17,ps1,ps24,ps19,ps23,ps13,ps15,ps5,ps4,ps50,ps32,ps12,ps48,(12,[(1,2,3)]),ps95,ps9,ps39,ps22,ps84,ps0,(9,[(0,2,4)]),ps61,ps44,ps14,ps20,ps7,ps21,ps29,ps37,ps26,ps31,ps34,(32,[]),ps114,(5,[(2,0,3),(2,1,2)]),ps164,ps49,ps3,ps16,(45,[]),ps69,(10,[(2,0,1)]),ps111,ps101,ps120,ps94,ps82,ps68,ps121]
def b9x9 : List NodeSpec := [([16,0,30,1,2,3,4,5,46],[0,1,2,3,4,5,6,7,8,9],[0]),([354,0,1,2,3,4,5],[10,11,12,13,14,15,16],[2]),([8,0,1,2,3,38,57,4,5],[17,18,19,20,0,21,3,22,23,24],[0]),([36,0,1,2,3,38,4,19,5],[21,25,26,18,10,27,11,19,7,6,20],[0]),([6,0,1,41,2,3,4,5,54],[17,27,28,5,4,29,21,30,31],[0]),([0,1,211,2,3,4,5],[21,12,7,6,32,33,34,16,35,36,27,13,14],[]),([32,48,17,0,1,2,3,4,5],[37,38,39,40,18,4,41,42,17,3],[]),([16,24,0,1,2,3,57,4,5],[43,18,26,0,44,45,46,47,7,6,5,48,32,49,22],[0]),([8,0,1,2,3,57,58],[50,17,51,52,53,18,54,55,56,57,58],[]),([33,17,0,1,2,3,4,5,46],[38,47,21,3,12,6,7],[0]),([336,0,1,2,3,4,5],[29,37,6,25,11,15,16,33,34],[]),([0,1,122,2,3,4,5],[4,6,17,0],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b9x9Ok : checkNodesBT wires goal (fullMask 100) b9x9Pools autos table8 9 b9x9 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b9x9Mem : ∀ ns ∈ b9x9, Impossible goal 9 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table8OK b9x9Ok
def buckets9 : BT (CertifiedBucket goal 9) := staticBuckets (btOfList 4 [bucketFragment wires b9x0 b9x0Mem,bucketFragment wires b9x1 b9x1Mem,bucketFragment wires b9x2 b9x2Mem,bucketFragment wires b9x3 b9x3Mem,bucketFragment wires b9x4 b9x4Mem,bucketFragment wires b9x5 b9x5Mem,bucketFragment wires b9x6 b9x6Mem,bucketFragment wires b9x7 b9x7Mem,bucketFragment wires b9x8 b9x8Mem,bucketFragment wires b9x9 b9x9Mem]) [[(0,0,5)],[(0,5,9)],[(0,14,5)],[(0,19,5)],[(0,24,8),(1,0,2)],[(1,2,5)],[(1,7,3)],[(1,10,5)],[(1,15,3)],[(1,18,2)],[(1,20,9)],[(1,29,3)],[(2,0,5)],[(2,5,4)],[(2,9,5)],[(2,14,5)],[(2,19,8)],[(2,27,2)],[(2,29,3),(3,0,2)],[(3,2,8)],[(3,10,4)],[(3,14,5)],[(3,19,8)],[(3,27,2)],[(3,29,3),(4,0,1)],[(4,1,2)],[(4,3,4)],[(4,7,2)],[(4,9,5)],[(4,14,6)],[(4,20,7)],[(4,27,3)],[(4,30,2),(5,0,1)],[(5,1,2)],[(5,3,5)],[(5,8,2)],[(5,10,2)],[(5,12,6)],[(5,18,2)],[(5,20,7)],[(5,27,5),(6,0,1)],[(6,1,6)],[(6,7,9)],[(6,16,2)],[(6,18,4)],[(6,22,4)],[(6,26,4)],[(6,30,2),(7,0,4)],[(7,4,2)],[(7,6,7)],[(7,13,6)],[(7,19,2)],[(7,21,1)],[(7,22,4)],[(7,26,1)],[(7,27,4)],[(7,31,1),(8,0,7)],[(8,7,7)],[(8,14,3)],[(8,17,7)],[(8,24,5)],[(8,29,2)],[(8,31,1),(9,0,6)],[(9,6,6)]]
def table9 := bucketValues buckets9
set_option maxRecDepth 200000 in
lemma table9OK : btAll (fun bk => ∀ xs ∈ bk, Impossible goal 9 xs.toFinset) table9 := bucketValues_ok _
def b10x0Pools : BT (Option BoundPool) := buildPoolsBT 8 wires roots slices [ps17,ps26,ps27,ps16,ps1,ps62,ps15,ps13,ps0,ps2,ps10,ps140,(7,[(0,3,4)]),(6,[(0,3,4)]),ps89,ps132,ps57,ps103,ps4,ps3,ps66,ps77,ps6,ps7,ps141,(8,[(3,0,3)]),ps91,ps73,ps97,ps78,ps76,ps105,(2,[(1,3,4)]),ps86,ps28,ps108,ps118,ps11,ps25,ps12,(1,[(1,3,4)]),(7,[(2,0,2)]),ps142,ps143,ps5,ps14,ps30,(1,[(1,3,5)]),(2,[(1,3,5)]),(1,[(3,0,4)]),(8,[(3,0,4)]),(2,[(3,0,4)]),(2,[(2,1,3)]),(0,[]),ps9,ps23,(10,[(2,0,2)]),(4,[(2,1,3)]),(10,[(2,1,3)]),(5,[(2,1,3)]),(11,[(2,1,3)]),ps110,ps32,ps90,(5,[(2,2,3)]),ps128,(47,[]),(6,[(2,2,3)]),(0,[(2,2,3)]),(6,[(0,4,5)]),ps92,ps95,ps38,ps96,ps48,ps119,ps22,ps18,ps109,ps136,ps37,ps20,ps144,ps137,(8,[(2,1,4)]),ps65,ps8,ps55,(1,[(3,2,4)]),ps84,ps19,(9,[(0,0,1)]),ps145,ps88,(0,[(3,2,4)]),(3,[(3,2,4)]),(32,[]),ps45,(3,[(3,0,4)]),(7,[(2,2,5)]),(9,[(2,2,5)]),(6,[(0,2,3)]),(8,[(2,0,4)]),ps102,ps134,(7,[(0,2,3)]),ps135,(11,[(0,2,3)]),(7,[(2,0,4)]),ps53,ps117,(7,[(0,0,2)]),ps75,(2,[(3,3,4)]),(1,[(3,3,4)]),ps56,(0,[(1,1,4)]),ps122,ps29,(2,[(1,1,4)]),(2,[(0,1,4)]),(9,[(2,1,4)]),(1,[(2,3,4)]),(7,[(2,3,4)]),ps79,ps138,ps59,(7,[(0,2,4)]),ps61,ps146,ps93,ps125,ps52,ps100,ps72,ps99,ps130,ps133,ps98,(2,[(1,0,1)]),(3,[(1,0,1)]),ps124,(1,[(1,2,3)]),(5,[(1,2,3)]),(11,[(1,2,3)]),ps63,ps126,ps54,ps24,(1,[(1,0,3)]),ps106,ps147,(7,[(2,2,4)]),ps31,(9,[(1,1,4)]),ps21,(0,[(3,3,5)]),(6,[(3,3,5)]),(1,[(3,3,5)]),(6,[(2,2,4)]),ps131,(2,[(1,0,3)]),(0,[(3,4,5)]),ps127,ps111,(3,[(1,2,4)]),ps148,ps149,ps150,ps151,ps152,ps87,(11,[(2,2,3)]),ps64,ps107,ps70,(43,[]),(8,[(0,1,4)]),ps153,(0,[(3,1,4)]),(6,[(1,4,5)]),ps43,ps129,(9,[(0,0,2)]),ps35,ps49]
def b10x0 : List NodeSpec := [([13,0,1,2,49,3,4,5],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[0,1]),([59,17,0,1,2,3,4,5],[16,17,18,19,20,3,21,10,22,23,24,25,26,27,28,29,30,31],[0,2]),([12,0,1,2,3,4,50,5],[32,33,34,35,36,37,2,38,39,4,8,40,41,42,43],[0,1]),([21,0,1,2,3,4,5,54],[8,4,0,44,38,2,45,46,10,47,48,49,50,51],[0,2]),([28,12,0,1,2,3,4,5],[52,33,37,10,44,53,3,2,54,55,35,56,43,42,57,58,59,60],[0]),([39,0,1,2,3,57,4,5],[61,19,62,63,64,65,22,66,8,38,9,67,68,23,26,69,70,71],[0]),([13,0,1,2,3,57,4,5],[26,62,72,73,14,5,74,9,22,8,10,0,2,23,70,71,69,61,75],[0,2]),([59,12,0,1,2,3,4,5],[29,43,54,19,35,37,22,16,76,3,77,41,33,73,78,27,28,20,79],[0]),([32,17,0,1,2,3,4,5],[10,80,21,38,3,53,81,8,4,25,17,82,83,84,85],[0]),([44,6,0,1,2,3,4,5],[86,87,76,88,89,90,38,3,77,8,91,92,93,94,95],[0]),([47,21,0,1,2,3,4,5],[8,4,96,34,97,10,9,46,0,77,6,2,49,98,99,100],[0,2]),([20,0,1,37,2,3,4,5],[101,102,80,103,104,86,9,45,37,4,8,105,106,107,108],[0,3]),([52,10,0,1,2,3,4,5],[2,109,44,110,13,77,22,54,37,38,8,111,78,112,113,114,115],[0]),([17,0,1,2,3,4,31,5],[116,24,80,21,117,3,118,9,37,4,8,46,119,25,82,17],[0]),([32,12,0,1,2,3,4,5],[83,35,37,10,44,53,3,34,55,38,4,8,120,33,43,42,115,121],[0]),([51,13,0,1,2,3,4,5],[0,62,5,3,9,53,86,10,8,4,14,15,122,123,115],[0,1]),([14,0,1,41,2,3,4,5],[124,125,18,126,2,8,86,9,37,45,81,127,128,129,31,130,85],[0,1]),([0,1,7,2,3,4,5,58],[131,132,133,134,4,9,0,135,136,137,138,139,140],[0,2]),([20,0,1,2,3,38,4,5],[86,141,104,39,38,37,54,22,4,8,142,143,144,108],[0]),([43,0,1,2,3,15,4,5],[2,145,146,147,148,10,9,22,4,149,150,151,152],[0]),([12,0,1,2,3,4,31,5],[37,35,9,153,6,7,44,8,4,3,34,116,117,154,33,42,43],[0]),([43,56,0,1,2,3,4,5],[2,8,4,44,148,38,155,9,22,156,157,158,146,159,152],[0]),([0,1,2,3,15,57,4,5],[26,160,61,148,150,10,2,8,23,71,70,149,63,73,161,162],[0]),([8,0,1,2,3,4,42,5],[86,163,164,44,3,8,4,90,34,165,166,167,168,169],[0]),([44,0,1,7,2,3,4,5],[94,139,18,88,132,4,9,0,1,7,3,8,140,134,170,95],[0,3]),([20,39,0,1,2,3,4,5],[65,104,86,19,9,54,68,3,38,37,4,8,171,64,172,108,103],[0,3]),([43,16,0,1,2,3,4,5],[2,34,173,146,37,81,38,9,8,4,174,175,85,152],[0,1]),([52,13,0,1,2,3,4,5],[2,1,110,5,4,9,10,0,38,8,14,15,114],[0,1]),([17,0,30,1,2,3,4,5],[10,176,21,38,4,45,81,19,8,3,1,120,177,178,25,179,17,82],[0]),([10,0,1,2,3,4,5,58],[180,115,78,136,181,44,2,4,37,131,182,133,138,137,111,183],[0]),([0,1,37,2,3,4,5,58],[135,103,106,138,184,0,9,4,180,133,101,131,182,105,136],[0,2]),([16,0,1,2,3,57,4,5],[69,61,34,185,174,173,66,22,8,38,37,2,86,23,70,71,73,63],[0,2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b10x0Ok : checkNodesBT wires goal (fullMask 100) b10x0Pools autos table9 10 b10x0 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b10x0Mem : ∀ ns ∈ b10x0, Impossible goal 10 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table9OK b10x0Ok
def b10x1Pools : BT (Option BoundPool) := buildPoolsBT 8 wires roots slices [ps0,ps1,ps11,ps10,ps9,(0,[]),ps8,ps23,ps25,(8,[(0,0,4)]),ps87,(9,[(0,0,4)]),(2,[(2,1,5)]),(8,[(2,1,5)]),(9,[(2,1,5)]),ps153,(7,[(2,0,2)]),ps45,(2,[(0,1,4)]),ps108,ps22,ps16,(9,[(0,1,4)]),ps86,ps143,ps142,(1,[(1,3,4)]),ps149,ps111,ps118,ps27,ps2,(2,[(1,3,4)]),ps150,ps151,ps17,ps26,ps60,ps15,ps13,ps14,ps20,ps18,(7,[(0,3,4)]),ps140,(1,[(1,0,2)]),ps117,ps74,(11,[(1,0,2)]),ps130,(5,[(1,2,3)]),ps5,ps124,ps98,ps12,(6,[(1,4,5)]),ps100,(0,[(1,2,3)]),ps129,ps125,(1,[(1,2,3)]),ps4,ps61,ps79,(7,[(0,2,4)]),(6,[(2,3,5)]),(1,[(2,3,5)]),(7,[(2,3,5)]),(2,[(3,1,5)]),(3,[(3,1,5)]),(9,[(3,1,5)]),(8,[(2,0,4)]),ps134,(9,[(2,0,4)]),(2,[(3,0,4)]),(4,[(3,2,3)]),(1,[(3,0,4)]),(1,[(3,2,3)]),(7,[(3,2,3)]),(5,[(3,2,3)]),(11,[(3,2,3)]),ps48,ps32,ps30,ps6,(1,[(1,0,4)]),(3,[(1,0,4)]),(7,[(3,2,5)]),(1,[(3,2,5)]),(3,[(3,2,5)]),ps73,ps57,ps148,ps92,ps145,ps78,ps76,ps66,ps136,(0,[(3,1,2)]),ps19,ps3,ps24,(0,[(1,1,2)]),ps63,ps131,ps106,ps147,(10,[(3,1,2)]),(4,[(3,1,2)]),(11,[(3,1,2)]),(5,[(3,1,2)]),(6,[(0,1,3)]),ps56,(10,[(0,0,2)]),ps109,ps75,(4,[(3,1,3)]),(10,[(3,1,3)]),(5,[(3,1,3)]),(11,[(3,1,3)]),ps120,ps127,(0,[(1,2,4)]),(3,[(1,2,4)]),(9,[(0,0,1)]),ps88,ps91,ps123,ps96,ps7,ps95,ps119,ps110,ps139,(0,[(3,4,5)]),(10,[(2,1,2)]),(4,[(2,1,2)]),(11,[(2,1,2)]),(5,[(2,1,2)]),(26,[]),ps37,(1,[(3,3,5)]),(2,[(3,3,5)]),(7,[(2,0,4)]),(6,[(2,2,4)]),ps65,ps28,ps146,ps105,ps93,(7,[(2,2,4)]),ps126,(5,[(2,2,3)]),ps128,ps43,ps102,(6,[(2,2,3)]),(0,[(2,2,3)]),(6,[(0,2,3)]),ps29,(10,[(0,2,3)]),ps135,(11,[(0,2,3)]),(10,[(2,0,1)]),ps89,ps62,ps133,ps58,(7,[(2,3,4)]),(1,[(2,3,4)]),(6,[(0,4,5)]),(49,[]),ps138,ps90,ps64,(10,[(2,0,3)]),ps107,ps70,(10,[(1,2,3)]),(11,[(1,2,3)]),(8,[(3,0,3)]),ps141,ps103,ps144,ps77,ps71,ps55,(8,[(0,0,1)]),(10,[(3,0,2)]),ps132,(2,[(1,0,1)]),ps52,ps115,(3,[(1,0,1)]),ps152,ps72,(1,[(1,0,3)]),ps99,(2,[(1,0,3)]),(8,[(3,0,4)]),(8,[(2,3,5)]),(10,[(2,2,3)]),(11,[(2,2,3)])]
def b10x1 : List NodeSpec := [([35,18,0,1,2,3,4,5],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14],[0]),([12,0,30,1,2,3,4,5],[15,16,17,18,19,1,20,2,8,0,5,21,22,23,24,25],[0]),([8,0,1,2,3,4,50,5],[26,27,28,4,29,6,8,30,1,0,31,32,33,34],[0,1]),([0,1,2,11,49,3,4,5],[35,21,36,1,37,38,3,39,40,41,42,0,43,44,45,46,47,48],[0,1]),([0,1,2,3,38,4,5,58],[49,50,51,52,53,1,54,6,8,55,56,57,58,59,60],[0]),([55,0,1,41,2,3,4,5],[0,1,30,21,61,31,38,35,41,62,63,64,65,66,67],[0,3]),([20,36,0,1,2,3,4,5],[2,0,7,31,6,68,69,70,71,72,73],[0]),([40,21,0,1,2,3,4,5],[35,17,74,75,1,6,3,0,61,76,77,78,79,80],[0,3]),([48,0,1,2,3,4,19,5],[1,0,6,54,81,3,82,83,35,84,39,21,85,86,87,88,89],[0,2]),([59,8,0,1,2,3,4,5],[34,90,4,61,91,28,6,31,84,27,92,93,94,95,96,97,98],[0]),([25,0,1,2,3,15,4,5],[30,99,2,3,7,100,101,102,103,104,105,106,107,108,109,110,111],[0]),([29,10,0,1,2,3,4,5],[2,31,30,35,40,41,112,113,114,115,116,117,118,119,120],[0,1]),([6,0,1,2,3,4,42,5],[6,121,20,122,100,38,39,21,84,0,1,51,7,8,123,124,125,126,94],[0,3]),([0,1,2,11,3,57,4,5],[127,128,129,47,81,0,130,3,35,131,93,45,132,133,134,135],[0,2]),([24,0,1,2,3,15,4,5],[3,8,6,30,38,39,103,104,105,106,107,136,137,138,139],[0,1]),([20,56,0,1,2,3,4,5],[0,1,140,36,141,8,2,30,40,5,6,84,142,143,144,71],[0,2]),([43,14,0,1,2,3,4,5],[145,146,30,21,147,38,2,41,31,39,1,0,148,63,149,150,151,152],[0,1]),([39,0,1,2,3,4,5,58],[53,153,154,49,155,51,31,1,8,56,55,59,58,156,157,158],[0,2]),([8,0,1,37,2,3,4,5],[31,159,61,27,40,5,6,160,156,161,162,163,28,164,34,33],[0]),([13,0,1,2,3,4,5,58],[56,165,166,49,155,31,1,3,35,30,59,58,113,53,167],[0,2]),([51,0,1,2,11,3,4,5],[35,37,21,168,3,38,54,84,1,45,47,48,169,170],[0,1]),([14,0,1,2,3,57,4,5],[171,61,147,133,149,146,84,172,0,2,6,40,148,173,130,93,131,129,174,127],[0]),([16,25,0,1,2,3,4,5],[2,30,7,41,109,108,111,110,175,176,177,178],[0,1]),([8,0,1,2,3,38,4,5],[6,27,8,31,7,100,51,4,57,52,179,50,180,164,28,33,34],[0]),([17,0,1,41,2,3,4,5],[62,181,61,36,30,21,1,0,31,3,41,64,63,182,183,184,185],[0,1]),([16,24,0,1,2,3,4,5],[6,8,38,41,137,136,139,138,175,176,177,178],[0,1]),([59,6,0,1,2,3,4,5],[186,187,20,94,90,8,6,4,42,188,125,91,95,96,97,98],[0]),([29,13,0,1,2,3,4,5],[31,35,5,7,166,189,165,190,117,118,119,120],[0,1]),([0,1,7,2,3,4,42,5],[122,191,123,192,193,21,1,35,124,194,195,196],[0,3]),([0,1,2,3,15,4,5,58],[53,106,104,56,1,3,30,58,59,197,198,49,199],[0,2]),([55,21,0,1,2,3,4,5],[35,0,61,5,3,21,130,76,74,200,66,67,201],[0,2]),([39,8,0,1,2,3,4,5],[31,51,27,158,7,6,8,4,28,164,34,33,154,202,153,203],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b10x1Ok : checkNodesBT wires goal (fullMask 100) b10x1Pools autos table9 10 b10x1 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b10x1Mem : ∀ ns ∈ b10x1, Impossible goal 10 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table9OK b10x1Ok
def b10x2Pools : BT (Option BoundPool) := buildPoolsBT 8 wires roots slices [ps139,ps117,(2,[(3,3,4)]),ps26,ps60,ps1,ps17,ps10,ps25,ps14,ps0,(1,[(1,0,2)]),ps74,(11,[(1,0,2)]),(1,[(3,3,4)]),ps11,ps2,ps53,ps56,ps6,ps153,ps27,ps18,(9,[(0,0,2)]),ps109,ps75,(3,[(3,1,4)]),(9,[(3,1,4)]),(8,[(0,0,1)]),(6,[(0,2,3)]),ps8,ps20,ps23,ps102,(10,[(0,2,3)]),ps135,(11,[(0,2,3)]),ps120,ps55,ps145,ps88,ps37,(4,[(3,2,3)]),ps134,ps12,(1,[(3,2,3)]),(7,[(3,2,3)]),(5,[(3,2,3)]),(11,[(3,2,3)]),(7,[(2,0,4)]),ps16,ps13,ps15,ps4,(6,[(0,1,2)]),ps29,ps65,ps104,ps105,ps93,(0,[(3,1,2)]),(4,[(3,1,2)]),(10,[(3,1,2)]),(5,[(3,1,2)]),(11,[(3,1,2)]),ps30,ps5,(0,[]),ps19,ps9,ps124,(10,[(1,2,3)]),(5,[(1,2,3)]),(11,[(1,2,3)]),(1,[(1,2,5)]),(7,[(1,2,5)]),(3,[(1,2,5)]),(7,[(0,0,4)]),(9,[(0,0,4)]),ps87,ps98,ps107,ps64,ps100,ps46,ps125,ps129,ps130,ps99,(4,[(2,1,2)]),(10,[(2,1,2)]),(5,[(2,1,2)]),(11,[(2,1,2)]),(2,[(1,0,3)]),(0,[(3,2,4)]),ps63,(1,[(1,0,3)]),ps106,ps147,(7,[(3,2,4)]),(1,[(3,2,4)]),ps24,(1,[(1,0,4)]),(7,[(0,3,5)]),(1,[(0,3,5)]),(2,[(1,0,4)]),(8,[(1,0,4)]),(8,[(0,3,5)]),ps57,ps72,ps73,ps52,ps3,ps7,(2,[(1,0,1)]),(3,[(1,0,1)]),ps91,ps76,ps78,ps136,ps66,(4,[(1,1,3)]),(10,[(1,1,3)]),(5,[(1,1,3)]),(11,[(1,1,3)]),(10,[(0,0,2)]),ps146,(4,[(0,1,2)]),(10,[(0,1,2)]),(5,[(0,1,2)]),(11,[(0,1,2)]),(0,[(1,1,2)]),ps131,(10,[(1,1,2)]),(4,[(1,1,2)]),(11,[(1,1,2)]),(5,[(1,1,2)]),(0,[(2,2,3)]),ps128,(10,[(2,2,3)]),(5,[(2,2,3)]),(11,[(2,2,3)]),(0,[(3,1,4)]),ps62,ps89,ps132,(10,[(1,0,1)]),ps152,ps133,ps126,ps77,ps141,ps61,ps103,ps144,(7,[(2,2,4)]),ps41,ps70,ps118,(2,[(1,3,4)]),(1,[(1,3,4)]),(7,[(0,0,2)]),(0,[(0,2,5)]),(32,[]),ps21,(7,[(0,2,5)]),(3,[(1,0,4)]),(9,[(0,2,5)]),(6,[(0,1,3)]),(2,[(2,1,3)]),(4,[(2,1,3)]),(10,[(2,1,3)]),(5,[(2,1,3)]),(11,[(2,1,3)]),(6,[(0,3,4)]),ps45,ps108,ps140,(7,[(0,3,4)]),(7,[(2,0,2)]),ps143,ps142,ps110,ps48,(8,[(3,0,3)]),ps92,ps95,ps96,ps90,(6,[(0,4,5)]),(0,[(1,2,3)]),ps71,ps33,ps97,(7,[(0,2,3)]),ps79,ps111,ps34,(9,[(0,2,4)]),ps149,ps148,ps151,ps150,(6,[(1,4,5)]),ps35,ps138,ps28,ps50,ps86,ps119]
def b10x2 : List NodeSpec := [([52,0,1,2,11,3,4,5],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14],[0,1]),([33,10,0,1,2,3,4,5],[15,16,17,18,19,20,21,22,10,23,24,25,26,27],[0]),([6,0,1,37,2,3,4,5],[28,29,8,6,16,30,31,32,33,34,35,36,37,38,39,40],[0,1]),([20,40,0,1,2,3,4,5],[30,41,42,43,9,15,10,5,44,45,46,47,48,49,33],[0]),([25,14,0,1,2,3,4,5],[15,21,50,51,52,53,54,31,55,56,57,58,59,60,61,62,63,64],[0]),([6,0,1,2,3,38,4,5],[30,8,52,65,66,51,31,9,67,68,32,69,70,71,72,73,38,37,40,39],[0]),([18,0,1,2,3,4,5,46],[30,5,69,10,50,15,22,74,75,76,77,78,79],[0,2]),([16,0,1,2,3,4,5,58],[80,81,82,83,84,15,5,8,21,30,56,85,86,87,88],[0,2]),([24,14,0,1,2,3,4,5],[30,50,15,7,68,32,54,56,57,58,59,89,90,91,92],[0,1]),([44,0,1,2,3,15,4,5],[93,94,3,21,50,95,5,30,7,9,10,96,97,98,99,100],[0,1]),([0,1,2,53,3,4,19,5],[6,10,101,7,50,19,9,102,103,104,105,106,107],[0,2]),([59,0,1,7,2,3,4,5],[108,109,53,110,111,16,112,6,19,113,114,115,116,117,118,119,120],[0]),([10,0,1,2,3,27,4,5],[15,21,32,65,66,68,31,9,67,51,52,69,121,122,123,124,125,18,25,24],[0]),([14,0,22,1,2,3,4,5],[126,54,21,50,15,52,7,31,127,128,129,130,56,57,58,59],[0,1]),([0,1,2,23,3,15,4,5],[131,96,50,21,15,7,51,9,132,95,98,97,133,134,135,136],[0,1]),([39,6,0,1,2,3,4,5],[8,30,16,137,51,52,66,29,69,37,38,39,40,138,139,140,141],[0]),([33,13,0,1,2,3,4,5],[16,3,142,143,5,21,6,7,10,144,145,26,27],[0]),([0,1,7,37,2,3,4,5],[16,6,67,51,112,65,32,68,52,9,31,101,34,33,36,35,111,146,109,147],[0]),([0,1,2,11,3,4,5,58],[83,12,44,87,4,7,5,6,86,85,11,148,80,0],[0]),([43,17,0,1,2,3,4,5],[149,150,21,50,41,101,7,31,16,52,5,10,151,152,153,154,155,56],[0]),([16,44,0,1,2,3,4,5],[30,156,5,82,50,31,10,15,8,9,21,100,99,94,81,157],[0,1]),([10,0,1,2,3,4,50,5],[21,18,69,158,65,8,19,10,5,15,159,160,161,25,24],[0,1]),([0,1,45,2,3,4,19,5],[10,5,162,105,163,16,7,6,21,164,102,165,166,167],[0,2]),([28,10,0,1,2,3,4,5],[21,15,7,68,32,66,168,67,69,18,125,24,25,169,170,171,172,173],[0]),([12,0,1,2,49,3,4,5],[50,174,175,176,5,10,15,177,178,179,2,180,181],[0,1]),([17,0,1,2,3,57,4,5],[116,53,41,10,182,19,50,153,150,183,113,7,151,184,112,185,186,187,188,189],[0,2]),([0,1,7,2,3,38,4,5],[114,190,8,16,6,30,68,9,71,70,73,72,146,111,147,109],[0,1]),([59,10,0,1,2,3,4,5],[191,24,192,118,18,21,69,15,19,113,161,23,189,110,193,108,120,119],[0]),([59,0,1,37,2,3,4,5],[35,117,53,112,120,6,33,16,19,113,29,194,188,108,191,110,193,118],[0]),([8,0,1,41,2,3,4,5],[16,195,53,196,5,21,10,67,30,197,198,199,200,201,202],[0]),([14,0,1,2,3,4,5,58],[203,56,58,80,204,5,15,30,9,85,86,87,88,83,126,205],[0]),([12,0,1,2,3,57,4,5],[189,187,206,112,180,176,207,19,10,15,50,179,208,113,185,186,182,209],[0,2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b10x2Ok : checkNodesBT wires goal (fullMask 100) b10x2Pools autos table9 10 b10x2 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b10x2Mem : ∀ ns ∈ b10x2, Impossible goal 10 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table9OK b10x2Ok
def b10x3Pools : BT (Option BoundPool) := buildPoolsBT 8 wires roots slices [ps17,ps16,ps11,ps10,ps23,ps19,(0,[(1,1,3)]),ps60,ps123,ps74,(11,[(1,0,2)]),(10,[(3,1,3)]),(4,[(3,1,3)]),(11,[(3,1,3)]),(5,[(3,1,3)]),ps78,(5,[(1,2,3)]),ps66,ps124,ps44,ps9,ps6,ps8,ps25,ps22,ps18,(0,[(1,2,3)]),(1,[(1,2,3)]),ps96,ps71,ps57,ps97,ps73,(6,[(2,1,4)]),ps56,ps32,ps137,ps27,ps5,ps1,ps0,ps153,(9,[(0,0,2)]),ps109,ps75,(9,[(2,1,4)]),(1,[(1,0,3)]),(0,[(3,1,4)]),ps41,(3,[(3,1,4)]),ps63,ps3,ps2,(2,[(1,0,3)]),ps106,ps147,(2,[(3,1,4)]),(0,[(2,2,3)]),ps20,ps14,ps24,ps52,(10,[(1,0,1)]),ps72,ps152,(10,[(2,2,3)]),ps128,(11,[(2,2,3)]),(5,[(2,2,3)]),ps13,ps15,ps28,ps122,(9,[(1,1,4)]),(6,[(0,2,3)]),(8,[(0,0,4)]),ps4,(13,[(0,2,3)]),ps87,ps102,(7,[(0,2,3)]),ps135,(11,[(0,2,3)]),(7,[(0,0,4)]),(2,[(1,0,4)]),(1,[(1,0,4)]),ps108,ps30,(0,[]),ps12,(7,[(2,0,2)]),ps143,ps142,(1,[(2,3,4)]),(7,[(2,3,4)]),ps65,ps79,ps146,ps105,ps93,(1,[(3,2,4)]),(7,[(3,2,4)]),ps59,ps118,ps62,(1,[(1,3,4)]),ps132,ps89,(1,[(3,2,3)]),ps149,ps29,ps111,(10,[(2,0,1)]),ps151,ps150,(4,[(3,2,3)]),(10,[(3,2,3)]),(5,[(3,2,3)]),(11,[(3,2,3)]),(4,[(1,1,2)]),(10,[(1,1,2)]),(5,[(1,1,2)]),(11,[(1,1,2)]),ps104,ps45,(11,[(1,2,3)]),(0,[(1,2,4)]),ps54,(7,[(1,2,4)]),ps127,(0,[(3,2,4)]),ps36,(12,[(1,2,3)]),(6,[(2,2,3)]),ps110,ps91,ps136,ps64,ps107,ps70,(6,[(3,3,5)]),(0,[(3,3,5)]),(1,[(3,3,5)]),(0,[(3,1,2)]),ps141,ps77,(10,[(3,0,3)]),ps103,ps144,(4,[(3,1,2)]),(10,[(3,1,2)]),(5,[(3,1,2)]),(11,[(3,1,2)]),(8,[(0,0,1)]),ps55,ps84,ps61,(9,[(0,2,4)]),(9,[(0,0,1)]),ps145,ps88,ps33,(3,[(1,0,4)]),(2,[(3,3,4)]),ps86,ps117,(1,[(3,3,4)]),(1,[(1,0,2)]),ps26,ps139,(9,[(3,1,4)]),(0,[(1,1,4)]),(7,[(0,0,2)]),ps53,(2,[(0,1,4)]),(9,[(0,1,4)]),(6,[(0,3,4)]),ps148,ps140,ps40,(8,[(0,3,4)]),ps76]
def b10x3 : List NodeSpec := [([29,0,1,2,11,3,4,5],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14],[0,1]),([59,0,1,2,3,38,4,5],[15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32],[0]),([32,10,0,1,2,3,4,5],[33,34,35,3,2,36,37,38,4,23,39,40,41,42,43,44,45],[0]),([33,0,1,2,3,15,4,5],[46,47,48,49,50,39,37,51,23,52,40,53,54,55,56],[0]),([39,0,1,7,2,3,4,5],[52,57,23,0,58,51,59,60,26,61,62,63,64,65,66,67,68],[0]),([10,0,1,2,3,4,31,5],[2,34,52,69,38,21,40,39,70,37,71,72,73,42,44,43],[0]),([18,0,1,37,2,3,4,5],[74,75,76,77,78,0,40,22,52,2,79,80,81,82,83],[0]),([0,1,37,2,3,4,19,5],[0,79,60,84,52,35,59,3,21,40,39,58,85,80,57,82,81],[0]),([51,12,0,1,2,3,4,5],[1,71,86,0,87,88,2,40,39,89,90,91,92,34,93,94],[0,1]),([44,14,0,1,2,3,4,5],[22,76,1,39,95,96,2,25,40,97,98,99,100,101,102],[0,1]),([13,0,1,2,3,4,50,5],[37,103,104,35,23,40,39,3,52,105,106,107],[0,1]),([40,8,0,1,2,3,4,5],[22,76,108,109,70,52,0,110,111,112,113,114,115,116,117,118],[0]),([14,0,1,2,23,3,4,5],[2,1,4,87,76,5,70,69,88,59,58,110,119,120,121,122,123,95,99,98],[0]),([18,0,1,2,3,38,4,5],[22,78,124,39,18,20,23,70,69,2,25,40,27,26,16,125,83],[0]),([0,1,2,3,15,4,42,5],[126,50,1,37,127,22,3,69,59,39,128,129,46,130,55,54],[0,1]),([0,1,2,3,38,4,19,5],[18,84,26,0,131,132,23,89,3,59,39,85,27,57,125,16],[0]),([59,39,0,1,2,3,4,5],[68,17,51,15,66,20,52,23,21,57,133,134,30,29,32,31,81],[0]),([59,13,0,1,2,3,4,5],[107,30,51,15,104,52,3,70,69,0,37,21,135,32,31,43,17,136],[0,2]),([16,33,0,1,2,3,4,5],[2,48,49,137,39,52,40,22,37,23,56,138,139],[0]),([56,0,1,2,3,4,42,5],[39,40,1,37,38,22,69,23,59,126,129,128,140,141,142],[0,3]),([25,17,0,1,2,3,4,5],[143,144,1,37,51,2,3,58,60,70,145,146,147,148,149,150,151,152],[0]),([6,0,1,41,2,3,4,5],[153,96,154,52,89,155,23,37,40,4,156,157,158,159,160],[0]),([32,13,0,1,2,3,4,5],[3,35,104,36,69,37,0,23,40,39,107,106,34,45],[0]),([16,0,1,2,3,4,42,5],[22,137,1,37,58,71,59,40,39,23,2,129,128,126,139,138],[0,1]),([39,18,0,1,2,3,4,5],[133,78,161,66,22,39,20,52,70,48,2,40,23,69,83,74,57,68,67],[0]),([39,0,1,2,3,4,19,5],[162,57,35,66,84,52,60,0,3,39,40,23,59,85,67,68],[0]),([52,12,0,1,2,3,4,5],[163,164,20,51,86,2,39,124,165,37,1,23,40,90,91,92,166],[0]),([33,0,1,2,11,3,4,5],[167,47,89,168,52,39,40,2,69,70,3,0,5,169,9,10,7,170,49],[0]),([13,0,1,2,3,4,31,5],[52,171,104,35,40,39,0,37,72,73,106,107],[0]),([10,0,30,1,2,3,4,5],[172,41,173,174,34,161,37,2,3,23,40,175,42,43,44],[0]),([8,0,1,2,49,3,4,5],[176,177,178,111,179,39,110,1,40,52,22,180,166,113,114],[0,1]),([59,0,1,2,3,15,4,5],[30,54,17,51,50,21,3,37,25,46,53,135,31,32,181,15],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b10x3Ok : checkNodesBT wires goal (fullMask 100) b10x3Pools autos table9 10 b10x3 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b10x3Mem : ∀ ns ∈ b10x3, Impossible goal 10 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table9OK b10x3Ok
def b10x4Pools : BT (Option BoundPool) := buildPoolsBT 8 wires roots slices [ps2,ps5,ps111,ps126,ps23,ps8,ps27,ps0,ps1,ps28,ps149,ps148,ps151,ps150,ps120,(9,[(2,2,4)]),ps87,(0,[(1,3,5)]),(26,[]),ps11,ps25,ps7,(1,[(1,3,5)]),(2,[(1,3,5)]),(7,[(0,0,4)]),(8,[(0,0,4)]),(6,[(0,4,5)]),ps4,ps92,ps6,(45,[]),ps96,ps90,ps110,ps119,(43,[]),(3,[(3,1,4)]),ps65,ps14,ps29,ps18,ps138,ps153,ps105,ps93,(2,[(3,1,4)]),(0,[(3,1,4)]),ps10,ps24,ps30,ps17,ps19,(2,[(1,0,4)]),(8,[(1,0,4)]),(3,[(1,0,4)]),(2,[(3,1,5)]),(9,[(3,1,5)]),(3,[(3,1,5)]),(7,[(0,0,2)]),(6,[(0,1,3)]),ps16,ps20,ps15,(4,[(0,1,3)]),(10,[(0,1,3)]),(5,[(0,1,3)]),(11,[(0,1,3)]),ps56,(10,[(0,0,2)]),ps109,ps75,ps61,ps52,ps13,(9,[(0,2,4)]),(3,[(1,0,1)]),(0,[(3,2,4)]),ps72,ps152,ps63,ps54,(0,[]),(2,[(1,0,3)]),ps106,ps147,(8,[(2,1,4)]),ps137,ps100,ps103,ps77,ps98,ps35,ps125,ps129,ps130,ps99,ps141,(8,[(3,0,3)]),(1,[(1,0,2)]),(0,[(1,1,3)]),(10,[(1,1,3)]),(4,[(1,1,3)]),(11,[(1,1,3)]),(5,[(1,1,3)]),ps123,ps60,(11,[(1,0,2)]),ps74,ps3,ps9,(9,[(0,0,4)]),(7,[(2,2,5)]),(9,[(2,2,5)]),ps122,(0,[(1,1,4)]),(2,[(1,1,4)]),ps107,ps66,ps57,ps49,ps64,ps73,ps97,ps78,ps76,(1,[(2,3,4)]),ps140,(8,[(2,3,4)]),ps21,(1,[(1,0,4)]),(1,[(3,3,5)]),(2,[(3,3,5)]),ps143,ps108,ps12,ps133,(7,[(2,0,2)]),ps86,ps33,(2,[(0,1,4)]),ps62,ps26,(9,[(0,1,4)]),ps89,ps132,ps127,(7,[(1,2,4)]),ps146,(1,[(3,2,5)]),(7,[(3,2,5)]),(3,[(3,2,5)]),(7,[(2,0,4)]),ps134,(9,[(2,0,4)]),(1,[(1,2,5)]),(7,[(1,2,5)]),(3,[(1,2,5)]),(1,[(3,0,4)]),(3,[(3,0,4)]),ps118,ps139,ps58,(2,[(1,3,4)]),(1,[(1,3,4)]),ps70,(6,[(2,2,4)]),ps42,ps79,(9,[(0,0,1)]),ps145,ps88,(2,[(2,1,3)]),ps22,(10,[(2,1,3)]),(4,[(2,1,3)]),(11,[(2,1,3)]),(5,[(2,1,3)]),ps144,(1,[(3,2,4)]),(7,[(3,2,4)]),ps38,ps91,ps136,ps55,ps39,(8,[(0,0,1)]),(4,[(3,1,3)]),(10,[(3,1,3)]),(5,[(3,1,3)]),(11,[(3,1,3)]),(10,[(2,0,2)]),ps142,(9,[(2,1,4)]),(1,[(3,3,4)]),ps34,ps117,(2,[(3,3,4)]),(8,[(0,1,4)])]
def b10x4 : List NodeSpec := [([43,8,0,1,2,3,4,5],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[0]),([18,0,1,2,3,4,5,54],[7,8,16,17,18,19,20,6,21,5,22,23,24,25],[0,2]),([8,0,1,2,3,57,4,5],[26,27,9,28,12,2,29,30,7,0,5,11,10,21,31,32,33,34],[0]),([33,14,0,1,2,3,4,5],[19,35,36,37,8,38,39,5,0,40,7,41,42,43,44,45,46],[0]),([36,0,1,2,3,4,19,5],[8,7,19,47,48,49,50,51,0,52,53,54,55,56,57],[0]),([10,0,26,1,2,3,4,5],[58,59,60,6,19,47,61,62,63,64,65,66,67,68,69,70],[0,1]),([0,1,7,41,2,3,4,5],[0,71,27,8,72,49,48,73,62,6,40,7,50,74,75,76,77,78],[0]),([32,0,1,2,3,15,4,5],[47,79,20,80,6,81,29,8,82,83,84,85,86],[0]),([17,0,1,2,3,4,5,58],[87,88,89,90,91,60,8,47,92,93,94,95,37,96,97],[0,2]),([0,1,2,11,3,27,4,5],[98,99,6,60,19,47,73,38,100,101,102,103,104,105,106,107],[0,1]),([47,18,0,1,2,3,4,5],[7,8,5,108,0,109,81,19,62,6,21,24,16,110,111,112],[0,2]),([0,1,2,3,15,4,31,5],[113,79,114,19,47,80,51,0,6,8,46,115,82,84,83],[0]),([59,16,0,1,2,3,4,5],[116,117,9,118,119,19,120,20,6,5,38,29,33,43,121,122,123,124],[0,2]),([51,8,0,1,2,3,4,5],[2,125,50,1,5,9,39,10,47,0,60,8,7,126,12,13,14,127],[0]),([56,0,1,2,3,4,19,5],[8,7,50,1,48,20,49,47,6,38,128,129,52,53,130,131],[0,2]),([12,0,1,2,3,4,5,58],[94,132,1,133,87,8,19,134,60,67,92,93,90,135,136,137],[0]),([13,0,30,1,2,3,4,5],[47,138,139,140,8,73,141,20,7,62,6,50,0,42,142,143,144],[0]),([14,0,1,2,3,4,42,5],[5,37,60,9,38,62,73,29,7,8,19,61,145,146,147,44,43],[0,1]),([20,48,0,1,2,3,4,5],[5,8,134,40,60,128,19,148,149,150,151,152,153],[0,2]),([21,0,1,2,3,4,5,46],[7,8,5,48,47,73,60,49,50,154,155,156,157,158],[0,2]),([0,1,2,11,3,4,50,5],[159,160,134,161,162,105,20,47,8,163,98,106,107],[0,1]),([32,16,0,1,2,3,4,5],[20,9,120,47,5,61,81,6,7,8,116,164,37,86,85],[0]),([43,6,0,1,2,3,4,5],[165,14,0,5,166,20,1,62,4,9,73,6,8,7,167,168,169,170,3,15],[0,3]),([28,0,1,2,11,3,4,5],[47,171,6,50,61,38,134,172,99,105,104,107,106,173,174,175,176],[0]),([44,17,0,1,2,3,4,5],[60,141,76,89,8,47,7,27,96,71,88,177,178,179],[0,1]),([59,0,1,2,11,3,4,5],[123,107,118,105,180,172,47,73,50,29,21,98,160,181,122,121,182,117],[0]),([16,0,1,2,3,4,31,5],[19,113,120,9,0,7,8,6,5,38,115,164,116],[0]),([6,0,1,2,3,57,4,5],[26,183,170,28,184,20,7,5,181,31,32,33,34,185,168],[0,2]),([12,29,0,1,2,3,4,5],[19,60,4,62,186,187,188,189,133,190,132,191],[0,1]),([32,0,1,2,11,3,4,5],[47,105,86,172,50,20,29,8,7,160,107,106,192],[0]),([52,8,0,1,2,3,4,5],[10,193,109,194,195,2,5,8,20,0,6,7,126,12,13,196],[0]),([0,30,1,2,3,15,4,5],[47,20,108,8,79,61,6,38,141,40,7,82,46,83,84,197,139],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b10x4Ok : checkNodesBT wires goal (fullMask 100) b10x4Pools autos table9 10 b10x4 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b10x4Mem : ∀ ns ∈ b10x4, Impossible goal 10 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table9OK b10x4Ok
def b10x5Pools : BT (Option BoundPool) := buildPoolsBT 8 wires roots slices [ps71,ps105,ps4,ps66,ps65,ps14,ps6,ps11,ps8,ps20,ps18,ps146,ps138,(6,[(0,4,5)]),ps73,ps97,ps78,ps76,ps57,ps60,(0,[(1,1,4)]),ps2,ps10,ps31,ps58,ps19,ps13,ps15,ps1,ps17,(0,[(3,1,4)]),(9,[(1,1,4)]),ps122,ps139,(11,[(1,0,2)]),ps74,(6,[(2,1,4)]),ps25,ps23,ps28,ps0,ps153,ps93,ps137,(8,[(2,1,4)]),ps52,ps126,ps115,ps24,ps27,(3,[(1,0,1)]),ps72,ps152,(9,[(2,2,4)]),ps45,ps87,(7,[(0,0,4)]),(6,[(0,2,3)]),(1,[(3,2,3)]),(7,[(3,2,3)]),(5,[(3,2,3)]),(11,[(3,2,3)]),(4,[(3,2,3)]),ps12,(2,[(1,0,4)]),ps37,(1,[(1,0,4)]),ps41,ps64,(2,[(0,1,4)]),(8,[(0,1,4)]),ps107,ps70,ps29,ps30,(0,[]),(2,[(1,1,4)]),ps9,ps7,(2,[(1,1,5)]),(3,[(1,1,5)]),(9,[(1,1,5)]),(8,[(0,0,4)]),(9,[(0,0,4)]),ps92,ps3,ps91,(2,[(1,0,1)]),ps90,ps96,ps119,ps110,ps141,(3,[(3,1,4)]),ps77,ps16,(8,[(3,0,3)]),ps103,ps144,(2,[(3,1,4)]),(0,[(1,3,5)]),(6,[(1,3,5)]),ps79,ps61,(1,[(1,3,5)]),(7,[(0,2,4)]),ps125,ps151,ps5,ps111,ps100,ps120,ps130,ps99,ps98,ps133,ps148,ps149,ps102,(2,[(3,0,4)]),(7,[(0,2,3)]),ps135,(11,[(0,2,3)]),(1,[(3,0,4)]),(0,[(2,2,3)]),ps108,(9,[(3,1,4)]),ps86,ps143,ps142,(6,[(0,3,4)]),(9,[(0,0,2)]),ps53,ps56,ps140,(7,[(0,3,4)]),(7,[(0,0,2)]),ps109,ps75,ps26,ps22,(9,[(0,1,4)]),(1,[(0,3,5)]),(7,[(0,3,5)]),(8,[(0,3,5)]),(7,[(2,0,4)]),(8,[(2,0,4)]),(0,[(1,2,4)]),ps127,(7,[(1,2,4)]),(0,[(1,2,3)]),(1,[(1,2,3)]),(5,[(1,2,3)]),(11,[(1,2,3)]),ps124,ps63,(1,[(1,0,3)]),(0,[(3,2,4)]),ps106,ps147,ps33,(48,[]),ps95,ps32,(1,[(3,2,4)]),ps34,ps150,(3,[(3,2,4)]),ps59,(43,[]),(10,[(1,2,3)]),ps50,(2,[(3,4,5)]),(1,[(2,3,5)]),(7,[(2,3,5)]),(8,[(2,3,5)]),(7,[(0,2,5)]),(9,[(0,2,5)]),ps134,(9,[(2,0,4)]),(6,[(2,3,4)]),(1,[(2,3,4)]),(7,[(2,3,4)]),(3,[(3,0,4)]),ps128,ps49,(5,[(2,2,3)]),(11,[(2,2,3)]),(6,[(1,4,5)]),ps145,(8,[(0,0,1)]),(9,[(0,0,1)])]
def b10x5 : List NodeSpec := [([59,14,0,1,2,3,4,5],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18],[0]),([0,1,2,11,3,4,31,5],[19,20,21,22,23,24,7,25,26,27,28,29,30,31,32,33,34,35],[0]),([32,14,0,1,2,3,4,5],[36,4,37,2,38,39,7,22,8,5,9,25,28,40,41,12,1,42,43,44],[0]),([43,0,1,7,2,3,4,5],[21,45,46,47,48,29,49,6,28,50,51,52,53],[0]),([40,18,0,1,2,3,4,5],[8,2,28,54,55,40,5,7,29,56,57,58,59,60,61,62],[0]),([40,0,1,2,3,4,19,5],[29,63,62,64,22,40,28,65,66,59,58,61,60],[0]),([16,0,30,1,2,3,4,5],[37,41,67,68,28,40,7,8,49,69,70,71,72],[0]),([14,0,1,2,3,4,31,5],[7,4,73,32,5,39,38,25,21,6,74,40,28,75,8,9,76,20,12,42,1],[0]),([18,0,1,2,3,4,5,34],[7,40,28,2,77,21,78,8,10,79,80,81,82,83,55],[0]),([0,1,7,2,3,57,4,5],[84,85,73,86,51,45,6,40,78,21,29,87,50,88,89,90,91],[0]),([33,17,0,1,2,3,4,5],[30,92,85,73,93,94,95,28,7,22,21,40,96,97,98,99],[0]),([0,1,41,2,3,4,5,54],[49,28,37,21,9,100,101,102,103,104,105],[0,3]),([8,0,1,2,3,4,5,58],[106,107,108,109,110,8,28,21,111,112,113,114,115,116,117],[0]),([21,0,1,37,2,3,4,5],[29,2,48,28,118,119,21,26,22,10,40,120,57,121,122,123,124],[0,3]),([12,33,0,1,2,3,4,5],[7,54,28,125,21,69,40,26,95,30,93,126,127,128,129],[0]),([10,0,1,2,49,3,4,5],[130,131,132,49,95,133,29,40,7,27,134,135,136,137,138],[0,1]),([0,30,1,2,11,3,4,5],[22,69,139,28,19,140,30,74,26,25,29,38,37,10,40,33,35,34,141],[0]),([20,0,1,2,53,3,4,5],[28,40,29,77,7,95,9,75,8,142,143,144,145,146],[0,2]),([17,0,1,2,3,4,42,5],[95,147,94,65,40,28,22,148,149,92,98,97],[0,1]),([21,0,1,2,3,38,4,5],[150,119,108,54,29,37,28,40,5,8,22,151,152,153,154,123,124],[0,3]),([0,1,41,2,3,15,4,5],[49,139,103,28,155,22,21,10,40,156,105,157,158,159],[0,1]),([10,0,1,2,3,57,4,5],[13,160,39,89,40,6,161,49,137,133,78,7,136,131,84,162,86,91,90],[0]),([0,1,37,2,3,57,4,5],[88,2,163,40,91,29,6,121,118,161,21,78,57,120,85,13,86,162,84,89],[0]),([44,8,0,1,2,3,4,5],[8,2,164,109,28,21,95,40,165,117,116,107,166,167],[0]),([14,0,30,1,2,3,4,5],[11,41,168,4,37,169,7,22,40,8,5,9,69,70,12,1,42],[0]),([0,1,2,3,38,57,4,5],[89,170,91,152,171,8,37,40,78,13,86,150,162,84,151,172],[0,2]),([55,18,0,1,2,3,4,5],[40,28,29,77,7,2,75,8,10,95,9,56,82,173,174,175],[0,2]),([20,0,1,45,2,3,4,5],[28,40,8,85,21,27,49,75,7,176,177,145,178,179],[0,2]),([51,10,0,1,2,3,4,5],[180,133,49,95,39,7,27,29,9,28,40,136,130,137,138,181,182],[0,1]),([16,0,1,41,2,3,4,5],[49,102,67,68,28,21,40,8,7,37,105,71,72],[0,1]),([39,21,0,1,2,3,4,5],[124,183,48,184,119,185,28,21,29,22,40,37,123,55,186,187],[0,3]),([6,0,1,2,3,4,5,58],[188,189,63,111,106,28,37,108,8,110,112,113,114,115,190,191],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b10x5Ok : checkNodesBT wires goal (fullMask 100) b10x5Pools autos table9 10 b10x5 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b10x5Mem : ∀ ns ∈ b10x5, Impossible goal 10 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table9OK b10x5Ok
def b10x6Pools : BT (Option BoundPool) := buildPoolsBT 1 wires roots slices [ps6,ps18]
def b10x6 : List NodeSpec := [([0,1,2,3,57,58],[0,1],[0,2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b10x6Ok : checkNodesBT wires goal (fullMask 100) b10x6Pools autos table9 10 b10x6 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b10x6Mem : ∀ ns ∈ b10x6, Impossible goal 10 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table9OK b10x6Ok
def buckets10 : BT (CertifiedBucket goal 10) := staticBuckets (btOfList 3 [bucketFragment wires b10x0 b10x0Mem,bucketFragment wires b10x1 b10x1Mem,bucketFragment wires b10x2 b10x2Mem,bucketFragment wires b10x3 b10x3Mem,bucketFragment wires b10x4 b10x4Mem,bucketFragment wires b10x5 b10x5Mem,bucketFragment wires b10x6 b10x6Mem]) [[(0,0,1)],[(0,1,3)],[(0,4,3)],[(0,7,3)],[(0,10,4)],[(0,14,4)],[(0,18,3)],[(0,21,2)],[(0,23,1)],[(0,24,1)],[(0,25,6)],[(0,31,1)],[(1,0,5)],[(1,5,4)],[(1,9,5)],[(1,14,1)],[(1,15,5)],[(1,20,2)],[(1,22,3)],[(1,25,1)],[(1,26,3)],[(1,29,1)],[(1,30,2),(2,0,3)],[],[(2,3,4)],[(2,7,4)],[(2,11,4)],[],[(2,15,4)],[(2,19,4)],[(2,23,4)],[(2,27,4)],[(2,31,1),(3,0,1)],[(3,1,3)],[(3,4,4)],[(3,8,3)],[(3,11,5)],[(3,16,6)],[],[(3,22,1)],[(3,23,7)],[(3,30,1)],[(3,31,1),(4,0,2)],[(4,2,5)],[(4,7,3)],[(4,10,2)],[(4,12,6)],[(4,18,3)],[(4,21,4)],[(4,25,3)],[(4,28,1)],[(4,29,3)],[(5,0,2)],[],[(5,2,4)],[(5,6,4)],[(5,10,2)],[(5,12,2)],[(5,14,3)],[(5,17,4)],[(5,21,2)],[(5,23,2)],[(5,25,1)],[(5,26,6),(6,0,1)]]
def table10 := bucketValues buckets10
set_option maxRecDepth 200000 in
lemma table10OK : btAll (fun bk => ∀ xs ∈ bk, Impossible goal 10 xs.toFinset) table10 := bucketValues_ok _
def b11x0Pools : BT (Option BoundPool) := buildPoolsBT 4 wires roots slices [ps30,ps19,ps15,ps13,ps20,ps14,ps18,ps6,ps21,ps7,ps0,(0,[]),ps23,ps1]
def b11x0 : List NodeSpec := [([6,0,1,2,3,4,5],[0,1,2,3,4,5,6,7,8,9],[0,1,2,3]),([0,1,2,3,4,42,5],[2,6,10,0,11,1,12,5,4,9,8],[0,1,2,3]),([0,1,7,2,3,4,5],[12,11,3,2,5,4,7,6,9,8],[0,1,2,3]),([59,0,1,2,3,4,5],[8,7,11,0,12,1,2,3,4,5],[0,2]),([10,0,1,2,3,4,5],[0,3,12,1,4,5,6,7,8,9],[0,1]),([0,1,37,2,3,4,5],[3,5,0,11,12,1,6,7,8,9],[0,1,2,3]),([18,0,1,2,3,4,5],[0,7,13,12,1,2,3,4,5,8,9],[0,2]),([0,1,2,3,4,19,5],[11,6,10,1,12,3,2,5,4,9,8],[0,2,3]),([0,1,2,3,38,4,5],[2,4,0,11,1,12,7,6,9,8],[0,1,2,3]),([39,0,1,2,3,4,5],[4,3,11,0,12,1,6,7,8,9],[0,1,2,3]),([13,0,1,2,3,4,5],[11,3,12,1,4,5,6,7,8,9],[0,1,2]),([0,1,2,3,15,4,5],[11,4,1,12,3,2,7,6,9,8],[0,1,2]),([16,0,1,2,3,4,5],[0,4,12,1,2,3,6,7,8,9],[0,1,2]),([0,1,41,2,3,4,5],[3,7,13,0,11,12,1,4,5,8,9],[0,1,2,3]),([0,1,2,11,3,4,5],[11,2,1,12,5,4,7,6,9,8],[0,1,2]),([14,0,1,2,3,4,5],[0,5,12,1,2,3,6,7,8,9],[0,1]),([21,0,1,2,3,4,5],[11,7,13,12,1,2,3,4,5,8,9],[0,2,3]),([43,0,1,2,3,4,5],[6,3,10,11,0,12,1,4,5,8,9],[0,1,2,3]),([0,1,2,3,57,4,5],[7,9,0,11,12,1,2,3,4,5],[0,2]),([17,0,1,2,3,4,5],[11,5,12,1,2,3,6,7,8,9],[0,1,2]),([20,0,1,2,3,4,5],[0,6,10,12,1,2,3,4,5,8,9],[0,2,3]),([12,0,1,2,3,4,5],[0,2,12,1,4,5,6,7,8,9],[0,1,2]),([0,1,2,3,4,5,58],[6,8,0,11,1,12,3,2,5,4],[0,2]),([44,0,1,2,3,4,5],[2,7,13,11,0,12,1,4,5,8,9],[0,1,2,3]),([8,0,1,2,3,4,5],[0,12,2,3,4,5,6,7,8,9],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b11x0Ok : checkNodesBT wires goal (fullMask 100) b11x0Pools autos table10 11 b11x0 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b11x0Mem : ∀ ns ∈ b11x0, Impossible goal 11 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table10OK b11x0Ok
def buckets11 : BT (CertifiedBucket goal 11) := staticBuckets (btOfList 0 [bucketFragment wires b11x0 b11x0Mem]) [[],[],[],[],[],[(0,0,1)],[],[],[(0,1,1)],[],[],[(0,2,1)],[],[],[(0,3,1)],[],[(0,4,2)],[(0,6,2)],[(0,8,1)],[],[],[],[(0,9,2)],[],[],[],[],[(0,11,1)],[],[],[],[(0,12,2)],[],[],[(0,14,1)],[],[],[(0,15,1)],[],[],[(0,16,1)],[],[(0,17,1)],[(0,18,1)],[],[],[],[],[],[],[(0,19,1)],[(0,20,1)],[(0,21,1)],[],[],[],[],[(0,22,1)],[],[],[],[(0,23,1)],[],[(0,24,1)]]
def table11 := bucketValues buckets11
set_option maxRecDepth 200000 in
lemma table11OK : btAll (fun bk => ∀ xs ∈ bk, Impossible goal 11 xs.toFinset) table11 := bucketValues_ok _
def b12x0Pools : BT (Option BoundPool) := buildPoolsBT 1 wires roots slices []
def b12x0 : List NodeSpec := [([0,1,2,3,4,5],[],[0,1,2,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma b12x0Ok : checkNodesBT wires goal (fullMask 100) b12x0Pools autos table11 12 b12x0 = true := by decide +kernel
set_option maxRecDepth 200000 in
lemma b12x0Mem : ∀ ns ∈ b12x0, Impossible goal 12 (nodeValsBT wires ns).toFinset := checkNodesBT_mem (by decide) pairsOK wiresOK (buildPoolsBT_sound slicesOK) autosOK table11OK b12x0Ok
def buckets12 : BT (CertifiedBucket goal 12) := staticBuckets (btOfList 0 [bucketFragment wires b12x0 b12x0Mem]) [[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[(0,0,1)]]
def table12 := bucketValues buckets12
set_option maxRecDepth 200000 in
lemma table12OK : btAll (fun bk => ∀ xs ∈ bk, Impossible goal 12 xs.toFinset) table12 := bucketValues_ok _
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lower : Lower roots goal 13 := lower_of_forestBT (essPairs := [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11),(VAR 4,3,19),(VAR 5,3,35)]) (by decide +kernel) table12OK (by decide +kernel)
end RootCert
def wit : List PEqualNP.CircuitLowerBounds.Gate := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1,3]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4,5]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0,2]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4,5]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3,8]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1,2]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10,11]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1,2]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0,13]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6,14]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7,15]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [9,15]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12,17]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [16,18]⟩]
def wo : Nat := 19
lemma wit_mono : PEqualNP.MetaComplexity.Monotone2 ⟨wit, wo⟩ := by simp [PEqualNP.MetaComplexity.Monotone2, wit]
set_option maxRecDepth 100000 in set_option maxHeartbeats 0 in
lemma wit_eval : ∀ r : Row, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput6 r)) = ((4276677320 * 2 ^ 32 + 3939035264) ||| ((4276677320 * 2 ^ 32 + 3939035264) <<< 64)).testBit r.val := by decide +kernel
lemma low_root : Lower (varsOf 63) ((4276677320 * 2 ^ 32 + 3939035264) ||| ((4276677320 * 2 ^ 32 + 3939035264) <<< 64)) 13 := RootCert.lower
end PEqualNP.Outside.L_meta_48474
theorem PEqualNP.Outside.L_meta_48474 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276677320 * 2 ^ 32 + 3939035264) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276677320 * 2 ^ 32 + 3939035264) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  intro s hcs
  exact PEqualNP.Outside.L_meta_48474.table2_of_lower (4276677320 * 2 ^ 32 + 3939035264) (by decide) (by decide) (by decide) (by decide)
    13 PEqualNP.Outside.L_meta_48474.low_root
    PEqualNP.Outside.L_meta_48474.wit PEqualNP.Outside.L_meta_48474.wo (by decide)
    PEqualNP.Outside.L_meta_48474.wit_mono PEqualNP.Outside.L_meta_48474.wit_eval s hcs
