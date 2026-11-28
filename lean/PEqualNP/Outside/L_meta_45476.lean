import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_45476
open PEqualNP.CircuitLowerBounds
abbrev Row := Fin 64
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
lemma bin_lt (d a b : Nat) (ha : a < 2^64) (hb : b < 2^64) : bin d a b < 2^64 := by
  have h1 : ∀ x y : Nat, x < 2^64 → y < 2^64 → (x &&& y) < 2^64 := fun x y hx _ =>
    Nat.lt_of_le_of_lt Nat.and_le_left hx
  have h2 : ∀ x y : Nat, x < 2^64 → y < 2^64 → (x ||| y) < 2^64 := fun x y hx hy =>
    Nat.or_lt_two_pow hx hy
  have h3 : ∀ x y : Nat, x < 2^64 → y < 2^64 → (x ^^^ y) < 2^64 := fun x y hx hy =>
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
lemma swGate_lt (w : List SWire) (hw : ∀ u ∈ w, u.2 < 2^64 ∧ u.2.testBit 0 = false) (g : Gate) :
    (swGate w g).2 < 2^64 ∧ (swGate w g).2.testBit 0 = false := by
  have hz : (0 : Nat) < 2^64 ∧ (0 : Nat).testBit 0 = false := ⟨by decide, by decide⟩
  have hg (i : Nat) : (w.getD i swZero).2 < 2^64 ∧ (w.getD i swZero).2.testBit 0 = false := by
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
    (hw : ∀ u ∈ w, u.2 < 2^64 ∧ u.2.testBit 0 = false) :
    ∀ u ∈ swExec gs w, u.2 < 2^64 ∧ u.2.testBit 0 = false := by
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
lemma normPack_lt (f : Wire) : normPack f < 2^64 :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => f r != f 0))).cast List.length_ofFn).isLt
lemma testBit_normPack (f : Wire) (r : Nat) :
    (normPack f).testBit r = if h : r < 64 then (f ⟨r, h⟩ != f 0) else false := by
  change ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => f r != f 0))).cast List.length_ofFn).getLsbD r = _
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases h : r < 64 <;> simp [h]
lemma normPack_eq_of_obs {a : Nat} (ha : a < 2^64) (h0 : a.testBit 0 = false) :
    normPack (obs a) = a := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack]
  by_cases hr : r < 64
  · simp [hr, obs, h0]
  · simp only [hr, dite_false]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega)))).symm
lemma normPack_inv (f : Wire) : normPack (invW f) = normPack f := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack, testBit_normPack]
  by_cases hr : r < 64
  · simp only [hr, dite_true, invW]
    cases f ⟨r, hr⟩ <;> cases f 0 <;> rfl
  · simp [hr]
lemma normPack_const {f : Wire} (h : Constant f) : normPack f = 0 := by
  obtain ⟨b, rfl⟩ := h
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack]
  by_cases hr : r < 64 <;> simp [hr]
lemma normPack_comb2 (op : Bool) (a b : Wire) :
    ∃ d < 4, normPack (comb2 op a b) = bin d (normPack a) (normPack b) := by
  refine ⟨opIdx (if op then !(a 0) else a 0) (if op then !(b 0) else b 0), opIdx_lt _ _, ?_⟩
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack, testBit_bin, testBit_normPack, testBit_normPack]
  by_cases hr : r < 64
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
set_option maxRecDepth 4000 in
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
      have ha1 : simple w (normPack a) := (avail_normPack ha).imp id (fun hm => hreps.symm ▸ hm)
      have hb1 : simple w (normPack b) := (avail_normPack hb).imp id (fun hm => hreps.symm ▸ hm)
      exact made_priced w d (false, normPack a) (false, normPack b) hd ha1 hb1
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
    (hT0 : T ≠ 0) (hTlt : T < 2^64) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^64 ∧ a.testBit 0 = false)
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
lemma obs_not_const {T : Nat} (hT0 : T ≠ 0) (hTlt : T < 2^64) (hTb0 : T.testBit 0 = false) :
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
def makePoolAux (d : Nat) (pool pm : List Nat) : List Choice → Option (List Nat × List Nat)
  | [] => some (pool, pm)
  | c :: cs =>
    if choiceOK d pm c then
      let v := choiceVal c
      makePoolAux d (v :: pool) ((v &&& d) :: pm) cs
    else none
lemma makePoolAux_eq (d : Nat) (pool : List Nat) (cs : List Choice) :
    makePoolAux d pool (pool.map (· &&& d)) cs = (makePool d pool cs).map (fun p => (p, p.map (· &&& d))) := by
  induction cs generalizing pool with
  | nil => rfl
  | cons c cs ih =>
    unfold makePoolAux makePool
    split
    · exact ih (choiceVal c :: pool)
    · rfl
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
lemma availM_sub {d a : Nat} {pm1 pm2 : List Nat} (hsub : ∀ m ∈ pm1, m ∈ pm2)
    (ok : availM d pm1 a = true) : availM d pm2 a = true := by
  simp only [availM, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at ok ⊢
  rcases ok with ((h | h) | h) | h
  · exact Or.inl (Or.inl (Or.inl h))
  · exact Or.inl (Or.inl (Or.inr h))
  · exact Or.inl (Or.inr (hsub _ h))
  · exact Or.inr (hsub _ h)
def cleanPM (d : Nat) : List Nat → List Nat
  | [] => []
  | m :: ms =>
    let r := cleanPM d ms
    if m == 0 || m == d || r.contains m || r.contains (d ^^^ m) then r else m :: r
lemma cleanPM_sub (d : Nat) (l : List Nat) : ∀ m ∈ cleanPM d l, m ∈ l := by
  induction l with
  | nil => intro m hm; simp [cleanPM] at hm
  | cons x xs ih =>
    intro m hm; unfold cleanPM at hm; dsimp only at hm
    split at hm
    · exact List.mem_cons_of_mem x (ih m hm)
    · rcases List.mem_cons.mp hm with rfl | hm'
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem x (ih m hm')
structure BoundPool where
  dom : Nat
  lb : Nat
  paid : Nat
  wires : List Nat
  pm : List Nat
def ValidPool (_raw : List Nat) (T : Nat) (c : BoundPool) : Prop :=
  (∀ m ∈ c.pm, m ∈ c.wires.map (· &&& c.dom)) ∧
  ∃ (f : Row → Row) (roots : List Nat) (bank : List Wire),
    (∀ r : Row, c.dom.testBit (f r).val = true) ∧ ¬Constant (restrictW f (obs T)) ∧
    (∀ q ws, Reach (roots.map obs) q ws → Avail ws (restrictW f (obs T)) → c.lb ≤ q) ∧
    Reach (roots.map obs) c.paid bank ∧ poolSupply f bank c.wires
def materialize (raw : List Nat) (cs : List Choice) (d lb : Nat) : Option BoundPool :=
  (makePoolAux d raw (raw.map (· &&& d)) cs).map fun p => ⟨d, lb, cs.length, p.1, cleanPM d p.2⟩
lemma materialize_sound {raw T d L cs c} (sl : Slice raw T d L)
    (h : materialize raw cs d L = some c) : ValidPool raw T c := by
  unfold materialize at h
  rw [makePoolAux_eq] at h
  cases he : makePool d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he, Option.map_some, Option.some.injEq] at h
    subst c
    obtain ⟨f, roots, dom, base, nc, lo⟩ := sl
    obtain ⟨bank, hr, hs⟩ := makePool_sound dom (show Reach (roots.map obs) 0 (roots.map obs) from rfl) base cs he
    exact ⟨cleanPM_sub d _, f, roots, bank, dom, nc, lo, by simpa using hr, hs⟩
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
    · exact availM_sound dom hs (availM_sub hpm hav)
    · exact availM_sound dom hs (availM_sub hpm (cut.1.2 a ha))
  | false =>
    have hok : choiceOK c.dom (c.wires.map (· &&& c.dom)) op = true := by
      have h2 := cut.2
      simp only [hav, Bool.not_false, Bool.not_true, Bool.false_eq_true, false_or] at h2
      simp only [choiceOK, Bool.and_eq_true] at h2 ⊢
      exact ⟨⟨h2.1.1, availM_sub hpm h2.1.2⟩, availM_sub hpm h2.2⟩
    obtain ⟨out, hr, hc⟩ := pay_choice dom hp hs op hok
    apply finish (c.paid + 1) out hr _ (by simp [hav])
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hc (choiceVal op) (by simp)
    · have hpt : poolSupply f out c.wires := fun v hv => hc v (List.mem_cons_of_mem _ hv)
      exact availM_sound dom hpt (availM_sub hpm (cut.1.2 a ha))
def fixRow (z o : Nat) (r : Row) : Row :=
  ⟨((r.val &&& (63 ^^^ z)) ||| o) % 64, Nat.mod_lt _ (by decide)⟩
def renameW (f : Row → Row) (a : Nat) : Nat :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).toNat
lemma testBit_renameW (f : Row → Row) (a : Nat) (r : Row) :
    (renameW f a).testBit r.val = a.testBit (f r).val := by
  change ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).getLsbD r.val = _
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn, r.isLt, dite_true, Option.getD_some]
lemma renameW_lt (f : Row → Row) (a : Nat) : renameW f a < 2^64 :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).isLt
lemma obs_renameW (f : Row → Row) (a : Nat) : obs (renameW f a) = restrictW f (obs a) := by
  funext r; exact testBit_renameW f a r
lemma renameW_bin (f : Row → Row) (d a b : Nat) :
    renameW f (bin d a b) = bin d (renameW f a) (renameW f b) := by
  apply Nat.eq_of_testBit_eq
  intro r
  by_cases hr : r < 64
  · rw [testBit_renameW f _ ⟨r, hr⟩, testBit_bin, testBit_bin, testBit_renameW f _ ⟨r, hr⟩, testBit_renameW f _ ⟨r, hr⟩]
  · have hlt (x : Nat) : (renameW f x).testBit r = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt f x) (Nat.pow_le_pow_right (by decide) (by omega)))
    rw [hlt, testBit_bin, hlt, hlt]
    rcases d with _ | _ | _ | d <;> rfl
lemma renameW_zero (f : Row → Row) : renameW f 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 64
  · simpa using testBit_renameW f 0 ⟨r, hr⟩
  · rw [Nat.zero_testBit]
    exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt f 0) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 64 ≤ r)))
lemma renameW_inj (f : Row → Row) (onto : Function.Surjective f) {a b : Nat}
    (ha : a < 2^64) (hb : b < 2^64) (eq : renameW f a = renameW f b) : a = b := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 64
  · obtain ⟨q, hq⟩ := onto ⟨r, hr⟩
    have h := congrArg (fun x => x.testBit q.val) eq
    rw [testBit_renameW, testBit_renameW, hq] at h
    exact h
  · have hge : 64 ≤ r := by omega
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide : 0 < 2) hge)),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide : 0 < 2) hge))]
lemma live_renameW {T k S} (h : Live T k S) (hS : ∀ a ∈ S, a < 2^64) (f : Row → Row)
    (onto : Function.Surjective f) : Live (renameW f T) k (S.image (renameW f)) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl, hT⟩ := h
    have hTlt : T < 2^64 := hS T (by simp)
    refine ⟨by simp, fun hz => hT (renameW_inj f onto hTlt (by decide) (hz.trans (renameW_zero f).symm))⟩
  | succ k ih =>
    obtain ⟨U, a, b, d, hd, rfl, ha, hb, hab, fresh, tail⟩ := h
    have halt : a < 2^64 := hS a (by simp)
    have hblt : b < 2^64 := hS b (by simp)
    have hUlt : ∀ x ∈ U, x < 2^64 := fun x hx => hS x (by simp [hx])
    have hzlt : bin d a b < 2^64 := bin_lt d a b halt hblt
    have htail_lt : ∀ x ∈ insert (bin d a b) U, x < 2^64 := by
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
    (hT0 : T ≠ 0) (hTlt : T < 2^64) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^64 ∧ a.testBit 0 = false)
    (hG0 : G ≠ 0) (hGlt : G < 2^64) (hGb0 : G.testBit 0 = false)
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
    (hT0 : T ≠ 0) (hTlt : T < 2^64) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^64 ∧ a.testBit 0 = false)
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
  | 0 => 0xaaaaaaaaaaaaaaaa
  | 1 => 0xcccccccccccccccc
  | 2 => 0xf0f0f0f0f0f0f0f0
  | 3 => 0xff00ff00ff00ff00
  | 4 => 0xffff0000ffff0000
  | 5 => 0xffffffff00000000
  | _ => 0
def ALL64 : Nat := 0xffffffffffffffff
def swapRow (i j : Nat) (r : Row) : Row :=
  let bi := r.val.testBit i
  let bj := r.val.testBit j
  if bi == bj then r
  else ⟨(r.val ^^^ (1 <<< i) ^^^ (1 <<< j)) % 64, Nat.mod_lt _ (by decide)⟩
def swapWord (i j : Nat) (w : Nat) : Nat :=
  let a := VAR i
  let b := VAR j
  let m10 := a ^^^ (a &&& b)
  let m01 := b ^^^ (a &&& b)
  let msame := ALL64 ^^^ (m10 ||| m01)
  let d := (1 <<< j) - (1 <<< i)
  (w &&& msame) ||| ((w &&& m10) <<< d) ||| ((w &&& m01) >>> d)
def permRow (swaps : List (Nat × Nat)) (r : Row) : Row :=
  swaps.foldl (fun x p => swapRow p.1 p.2 x) r
def permWord (swaps : List (Nat × Nat)) (w : Nat) : Nat :=
  swaps.foldr (fun p x => swapWord p.1 p.2 x) w
lemma swapRow_invol (i j : Nat) (hi : i < 6) (hj : j < 6) (r : Row) :
    swapRow i j (swapRow i j r) = r := by
  revert r
  interval_cases i <;> interval_cases j <;> decide +kernel
lemma swapWord_testBit (i j : Nat) (hij : i < j) (hj : j < 6) (w : Nat) (hw : w < 2^64) (r : Row) :
    (swapWord i j w).testBit r.val = w.testBit (swapRow i j r).val := by
  have hi : i < 6 := by omega
  have hspec : ∀ r : Row,
      let a := VAR i; let b := VAR j
      let m10 := a ^^^ (a &&& b); let m01 := b ^^^ (a &&& b); let msame := ALL64 ^^^ (m10 ||| m01)
      let d := (1 <<< j) - (1 <<< i)
      (msame.testBit r.val = true → (swapRow i j r).val = r.val ∧ (d ≤ r.val → m10.testBit (r.val - d) = false) ∧ m01.testBit (r.val + d) = false) ∧
      (msame.testBit r.val = false →
        (d ≤ r.val ∧ m10.testBit (r.val - d) = true ∧ (swapRow i j r).val = r.val - d ∧ m01.testBit (r.val + d) = false) ∨
        ((d ≤ r.val → m10.testBit (r.val - d) = false) ∧ m01.testBit (r.val + d) = true ∧ (swapRow i j r).val = r.val + d)) := by
    revert r; interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have hr := hspec r
  simp only [swapWord, Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Nat.add_comm]
  cases hms : (ALL64 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j)))).testBit r.val with
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
lemma swapWord_lt (i j : Nat) (hij : i < j) (hj : j < 6) (w : Nat) : swapWord i j w < 2^64 := by
  have hi : i < 6 := by omega
  have h1 : (ALL64 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j)))) < 2^64 := by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have h2 : ((VAR i ^^^ (VAR i &&& VAR j)) <<< ((1 <<< j) - (1 <<< i))) < 2^64 := by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have h3 : ((VAR j ^^^ (VAR i &&& VAR j)) >>> ((1 <<< j) - (1 <<< i))) < 2^64 := by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  unfold swapWord
  have e1 : (w &&& (ALL64 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j))))) < 2^64 :=
    Nat.lt_of_le_of_lt Nat.and_le_right h1
  have e2 : ((w &&& (VAR i ^^^ (VAR i &&& VAR j))) <<< ((1 <<< j) - (1 <<< i))) < 2^64 := by
    have hle : (w &&& (VAR i ^^^ (VAR i &&& VAR j))) ≤ (VAR i ^^^ (VAR i &&& VAR j)) := Nat.and_le_right
    calc ((w &&& (VAR i ^^^ (VAR i &&& VAR j))) <<< ((1 <<< j) - (1 <<< i)))
        = (w &&& (VAR i ^^^ (VAR i &&& VAR j))) * 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.shiftLeft_eq _ _
      _ ≤ (VAR i ^^^ (VAR i &&& VAR j)) * 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.mul_le_mul_right _ hle
      _ = ((VAR i ^^^ (VAR i &&& VAR j)) <<< ((1 <<< j) - (1 <<< i))) := (Nat.shiftLeft_eq _ _).symm
      _ < 2^64 := h2
  have e3 : ((w &&& (VAR j ^^^ (VAR i &&& VAR j))) >>> ((1 <<< j) - (1 <<< i))) < 2^64 := by
    have hle : (w &&& (VAR j ^^^ (VAR i &&& VAR j))) ≤ (VAR j ^^^ (VAR i &&& VAR j)) := Nat.and_le_right
    calc ((w &&& (VAR j ^^^ (VAR i &&& VAR j))) >>> ((1 <<< j) - (1 <<< i)))
        = (w &&& (VAR j ^^^ (VAR i &&& VAR j))) / 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.shiftRight_eq_div_pow _ _
      _ ≤ (VAR j ^^^ (VAR i &&& VAR j)) / 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.div_le_div_right hle
      _ = ((VAR j ^^^ (VAR i &&& VAR j)) >>> ((1 <<< j) - (1 <<< i))) := (Nat.shiftRight_eq_div_pow _ _).symm
      _ < 2^64 := h3
  exact Nat.or_lt_two_pow (Nat.or_lt_two_pow e1 e2) e3
lemma swapWord_eq_renameW (i j : Nat) (hij : i < j) (hj : j < 6) (w : Nat) (hw : w < 2^64) :
    swapWord i j w = renameW (swapRow i j) w := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 64
  · rw [swapWord_testBit i j hij hj w hw ⟨r, hr⟩, ← testBit_renameW (swapRow i j) w ⟨r, hr⟩]
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (swapWord_lt i j hij hj w) (Nat.pow_le_pow_right (by decide) (by omega))),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))]
def swapsValid (swaps : List (Nat × Nat)) : Bool :=
  swaps.all fun p => decide (p.1 < p.2) && decide (p.2 < 6)
lemma permWord_eq_renameW (swaps : List (Nat × Nat)) (hv : swapsValid swaps = true)
    (w : Nat) (hw : w < 2^64) : permWord swaps w = renameW (permRow swaps) w := by
  induction swaps generalizing w with
  | nil =>
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hr : r < 64
    · exact (testBit_renameW (permRow []) w ⟨r, hr⟩).symm
    · rw [show permWord [] w = w from rfl,
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))]
  | cons p ps ih =>
    simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hv
    have ihw := ih hv.2 w hw
    have hlt : permWord ps w < 2^64 := ihw ▸ renameW_lt _ w
    change swapWord p.1 p.2 (permWord ps w) = renameW (permRow (p :: ps)) w
    rw [swapWord_eq_renameW p.1 p.2 hv.1.1 hv.1.2 _ hlt, ihw]
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hr : r < 64
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
    (hT : T < 2^64) (hfix : permWord swaps T = T)
    (hw : ∀ a ∈ ws, a < 2^64) :
    Impossible T n (ws.map (permWord swaps)).toFinset := by
  intro k hk run
  have hr : ∀ a ∈ (ws.map (permWord swaps)).toFinset, a < 2^64 := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    rw [permWord_eq_renameW swaps hv x (hw x hx)]
    exact renameW_lt _ x
  have hvr : swapsValid swaps.reverse = true := by
    simp only [swapsValid, List.all_reverse]; exact hv
  have hinv_row2 : ∀ r : Row, permRow swaps (permRow swaps.reverse r) = r := by
    intro r; simpa using permRow_rev_cancel swaps.reverse hvr r
  have hinv_word : ∀ x : Nat, x < 2^64 → renameW (permRow swaps.reverse) (permWord swaps x) = x := by
    intro x hx
    rw [permWord_eq_renameW swaps hv x hx]
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hrr : r < 64
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
  (List.range 6).filterMap fun i => if m.testBit i then some (VAR i) else none
def subcube (z o : Nat) : Nat :=
  (List.range 64).foldr (fun r acc =>
    if (r &&& z == 0) && (r &&& o == o) then acc ||| (1 <<< r) else acc) 0
def fixWord (z o w : Nat) : Nat :=
  (List.range 64).foldr (fun r acc =>
    let fr := ((r &&& (63 ^^^ z)) ||| o) % 64
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
  by_cases hr : r < 64
  · rw [testBit_renameW (fixRow z o) w ⟨r, hr⟩]
    simp [hr, fixRow]
  · simp only [List.mem_range, hr, decide_false, Bool.false_and]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))).symm
lemma subcube_fixRow (z o : Nat) (hz : z < 64) (ho : o < 64) (hzo : (z &&& o) = 0) (r : Row) :
    (subcube z o).testBit (fixRow z o r).val = true := by
  unfold subcube
  rw [testBit_foldr_bits]
  have hmem : (fixRow z o r).val ∈ List.range 64 := List.mem_range.mpr (fixRow z o r).isLt
  simp only [hmem, decide_true, Bool.true_and, Bool.and_eq_true, beq_iff_eq]
  have h63 : ((r.val &&& (63 ^^^ z)) ||| o) < 64 := by
    have hr := r.isLt
    have hlt1 : (r.val &&& (63 ^^^ z)) < 64 := Nat.lt_of_le_of_lt Nat.and_le_left hr
    exact Nat.or_lt_two_pow (n := 6) hlt1 ho
  have hval : (fixRow z o r).val = ((r.val &&& (63 ^^^ z)) ||| o) := Nat.mod_eq_of_lt h63
  rw [hval]
  constructor
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, Nat.zero_testBit]
    have hzi : (z.testBit i && o.testBit i) = false := by
      have := congrArg (fun x => x.testBit i) hzo; simpa [Nat.testBit_and] using this
    by_cases hi : i < 6
    · have h7 : (63 : Nat).testBit i = true := by interval_cases i <;> decide
      cases hzb : z.testBit i <;> cases hob : o.testBit i <;> simp_all [h7]
    · have hzf : z.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hz (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 6 ≤ i)))
      simp [hzf]
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_or]
    cases o.testBit i <;> simp
def checkEss1 (T : Nat) (roots : List Nat) (a r s : Nat) : Bool :=
  decide (r < 64) && decide (s < 64) && (T.testBit r != T.testBit s) &&
    roots.all fun v => v == a || (v.testBit r == v.testBit s)
lemma checkEss1_sound {T roots a r s} (h : checkEss1 T roots a r s = true) : Essential T roots a := by
  simp only [checkEss1, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  exact ⟨⟨r, h.1.1.1⟩, ⟨s, h.1.1.2⟩, h.1.2, fun v hv hne => (h.2 v hv).resolve_left hne⟩
def freeIn (other : List Nat) (w : Nat) : Bool := w == 0 || w == ALL64 || other.contains w
lemma freeIn_sound {other : List Nat} {f : Row → Row} {a : Nat} (ok : freeIn other (renameW f a) = true) :
    Avail (other.map obs) (restrictW f (obs a)) := by
  rw [← obs_renameW]
  simp only [freeIn, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at ok
  rcases ok with (h0 | h1) | hm
  · exact Or.inr (Or.inl ⟨false, by rw [h0]; funext r; simp [obs]⟩)
  · exact Or.inr (Or.inl ⟨true, by rw [h1]; funext r; simp only [obs, ALL64]; have := r.isLt; exact Nat.testBit_two_pow_sub_one 64 r.val |> fun e => by simpa [this] using e⟩)
  · exact Or.inl (List.mem_map_of_mem hm)
def checkProper (w : Nat) : Bool := w != 0 && decide (w < 2^64) && !w.testBit 0
lemma checkProper_sound {w : Nat} (h : checkProper w = true) : w ≠ 0 ∧ w < 2^64 ∧ w.testBit 0 = false := by
  simp only [checkProper, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq, Bool.not_eq_true'] at h
  exact ⟨h.1.1, h.1.2, h.2⟩
def checkRoots (rs : List Nat) : Bool := rs.all fun a => decide (a < 2^64) && !a.testBit 0
lemma checkRoots_sound {rs : List Nat} (h : checkRoots rs = true) :
    ∀ a ∈ rs, a < 2^64 ∧ a.testBit 0 = false := by
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
  base.all fun x => (x.2.1 == projBits pos x.1) && (x.2.2 == projBits neg x.1) && decide (x.1 < 2^64)
lemma base_of {pos neg base} (ok : baseCheck pos neg base = true) :
    ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^64 := by
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
lemma var_testBit (i : Fin 6) (r : Row) : (VAR i.val).testBit r.val = r.val.testBit i.val := by revert i r; decide +kernel
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
inductive btAll {α : Type} (P : α → Prop) : BT α → Prop where
  | empty : btAll P .empty
  | leaf {x : α} : P x → btAll P (.leaf x)
  | node {l r : BT α} : btAll P l → btAll P r → btAll P (.node l r)
lemma btAll_get {α : Type} {P : α → Prop} {d : α} {t : BT α} (ht : btAll P t) (hd : P d) (i : Nat) :
    P (btGet d t i) := by
  induction ht generalizing i with
  | empty => exact hd
  | leaf hx => exact hx
  | node _ _ ihl ihr =>
    unfold btGet
    split
    · exact ihl _
    · exact ihr _
lemma btAll_set {α : Type} {P : α → Prop} {depth : Nat} {t : BT α} {i : Nat} {v : α}
    (ht : btAll P t) (hv : P v) : btAll P (btSet depth t i v) := by
  induction depth generalizing t i with
  | zero => exact .leaf hv
  | succ d ih =>
    cases ht with
    | empty =>
      unfold btSet; split
      · exact .node (ih .empty) .empty
      · exact .node .empty (ih .empty)
    | leaf hx =>
      unfold btSet; split
      · exact .node (ih (.leaf hx)) .empty
      · exact .node .empty (ih (.leaf hx))
    | node hl hr =>
      unfold btSet; split
      · exact .node (ih hl) hr
      · exact .node hl (ih hr)
lemma btAll_update {α : Type} {P : α → Prop} {d0 : α} {depth : Nat} {t : BT α} {i : Nat} {f : α → α}
    (ht : btAll P t) (hd0 : P d0) (hf : ∀ x, P x → P (f x)) : btAll P (btUpdate d0 depth t i f) := by
  induction depth generalizing t i with
  | zero =>
    cases ht with
    | leaf hx => exact .leaf (hf _ hx)
    | empty => exact .leaf (hf d0 hd0)
    | node _ _ => exact .leaf (hf d0 hd0)
  | succ d ih =>
    cases ht with
    | empty =>
      unfold btUpdate; split
      · exact .node (ih .empty) .empty
      · exact .node .empty (ih .empty)
    | leaf hx =>
      unfold btUpdate; split
      · exact .node (ih (.leaf hx)) .empty
      · exact .node .empty (ih (.leaf hx))
    | node hl hr =>
      unfold btUpdate; split
      · exact .node (ih hl) hr
      · exact .node hl (ih hr)
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
  exact hgo l (0, BT.empty) h .empty
def fastBitMask (z o i : Nat) : Nat :=
  if z.testBit i then ALL64 ^^^ VAR i else if o.testBit i then VAR i else ALL64
def subcubeFast (z o : Nat) : Nat :=
  fastBitMask z o 0 &&& fastBitMask z o 1 &&& fastBitMask z o 2 &&&
  fastBitMask z o 3 &&& fastBitMask z o 4 &&& fastBitMask z o 5
lemma fastBitMask_testBit (z o i : Nat) (hi : i < 6) (r : Row) :
    (fastBitMask z o i).testBit r.val =
      (if z.testBit i then !(r.val.testBit i) else if o.testBit i then r.val.testBit i else true) := by
  have hall : ALL64.testBit r.val = true := by
    simp only [ALL64]; have hr := r.isLt; simpa [hr] using Nat.testBit_two_pow_sub_one 64 r.val
  have hvar : (VAR i).testBit r.val = r.val.testBit i := var_testBit ⟨i, hi⟩ r
  unfold fastBitMask
  split
  · simp [Nat.testBit_xor, hall, hvar]
  · split
    · exact hvar
    · exact hall
lemma subcubeFast_eq_subcube (z o : Nat) (hz : z < 64) (ho : o < 64) (hzo : (z &&& o) = 0) :
    subcubeFast z o = subcube z o := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 64
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
      fastBitMask_testBit z o 5 (by decide) ⟨r, hr⟩]
    have hbit (i : Nat) (hi : i < 6) :
        ((r &&& z).testBit i = false ∧ (r &&& o).testBit i = o.testBit i) ↔
          (if z.testBit i then !r.testBit i else if o.testBit i then r.testBit i else true) = true := by
      have hzi : (z.testBit i && o.testBit i) = false := by
        have := congrArg (fun x => x.testBit i) hzo; simpa [Nat.testBit_and] using this
      simp only [Nat.testBit_and]
      cases hz' : z.testBit i <;> cases ho' : o.testBit i <;> cases hr' : r.testBit i <;> simp_all
    have heq_iff : (((r &&& z == 0) && (r &&& o == o)) = true) ↔
        ∀ i < 6, (r &&& z).testBit i = false ∧ (r &&& o).testBit i = o.testBit i := by
      simp only [Bool.and_eq_true, beq_iff_eq]
      constructor
      · rintro ⟨h1, h2⟩ i _; rw [h1, h2, Nat.zero_testBit]; exact ⟨rfl, rfl⟩
      · intro h
        constructor
        · apply Nat.eq_of_testBit_eq; intro i
          rw [Nat.zero_testBit]
          by_cases hi : i < 6
          · exact (h i hi).1
          · have hzf : z.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hz (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 6 ≤ i)))
            simp [Nat.testBit_and, hzf]
        · apply Nat.eq_of_testBit_eq; intro i
          by_cases hi : i < 6
          · exact (h i hi).2
          · have hof : o.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ho (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 6 ≤ i)))
            simp [Nat.testBit_and, hof]
    apply Bool.eq_iff_iff.mpr
    rw [heq_iff]
    simp only [Bool.and_eq_true]
    constructor
    · intro h i hi
      have := hbit i hi
      interval_cases i <;> tauto
    · intro h
      refine ⟨⟨⟨⟨⟨(hbit 0 (by decide)).mp (h 0 (by decide)), (hbit 1 (by decide)).mp (h 1 (by decide))⟩,
        (hbit 2 (by decide)).mp (h 2 (by decide))⟩, (hbit 3 (by decide)).mp (h 3 (by decide))⟩,
        (hbit 4 (by decide)).mp (h 4 (by decide))⟩, (hbit 5 (by decide)).mp (h 5 (by decide))⟩
  · have hlt_f (i : Nat) : (fastBitMask z o i).testBit r = false := by
      have hle : 64 ≤ r := by omega
      have ha : ALL64 < 2^64 := by decide
      have hv : VAR i < 2^64 := by
        unfold VAR; rcases i with _ | _ | _ | _ | _ | _ | _
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · change (0 : Nat) < 2^64; decide
      have hlt_m : fastBitMask z o i < 2^64 := by
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
def hashWs64 (ws : List Nat) : Nat :=
  (ws.foldl (fun h w => h * 31 + (w &&& 255) + ((w >>> 8) &&& 255) * 3 + ((w >>> 16) &&& 255) * 7 + ((w >>> 32) &&& 255) * 13 + ((w >>> 48) &&& 255) * 29) 0) &&& 255
def bucketContainsBT (bks : BT (List (List Nat))) (ws : List Nat) : Bool :=
  let s := sortNats ws
  (btGet [] bks (hashWs64 s)).contains s
def mapPermWord (sw : List (Nat × Nat)) (ws : List Nat) : List Nat :=
  match sw with
  | [] => ws
  | _ => ws.map (permWord sw)
lemma mapPermWord_eq (sw : List (Nat × Nat)) (ws : List Nat) :
    mapPermWord sw ws = ws.map (permWord sw) := by
  cases sw with
  | nil =>
    change ws = ws.map (fun w => w)
    simp
  | cons p ps => rfl
def closeChildBT (pools : List BoundPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (k : Nat) (rest : List Nat) (op : Choice) : Bool :=
  let ws := choiceVal op :: rest
  pools.any (fun c => scalarPoolCut c k rest op) ||
    autos.any (fun sw => bucketContainsBT prevBks (mapPermWord sw ws))
lemma closeChildBT_sound {raw T pools autos prevBks k rest op}
    (hT : T < 2^64)
    (hPools : ∀ c ∈ pools, ValidPool raw T c)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : btAll (fun b => ∀ xs ∈ b, Impossible T k xs.toFinset) prevBks)
    (nd : (choiceVal op :: rest).Nodup)
    (hlt : ∀ x ∈ choiceVal op :: rest, x < 2^64)
    (h : closeChildBT pools autos prevBks k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  simp only [closeChildBT, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with ⟨c, hc, hcut⟩ | ⟨sw, hsw, hhit⟩
  · exact scalarPoolCut_sound (hPools c hc) nd hcut
  · rw [mapPermWord_eq] at hhit; unfold bucketContainsBT at hhit
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
    have hinv_w : ∀ x : Nat, x < 2^64 → permWord sw.reverse (permWord sw x) = x := by
      intro x hx
      have h1 := permWord_eq_renameW sw hsv x hx
      have h2 := permWord_eq_renameW sw.reverse hvr (permWord sw x) (h1 ▸ renameW_lt _ x)
      rw [h2, h1]
      apply Nat.eq_of_testBit_eq; intro r
      by_cases hrr : r < 64
      · rw [testBit_renameW _ _ ⟨r, hrr⟩, testBit_renameW, hinv_row2]
      · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))),
            Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)))]
    have hfixr : permWord sw.reverse T = T := by
      have := hinv_w T hT; rwa [hfix] at this
    have hmap_lt : ∀ a ∈ (choiceVal op :: rest).map (permWord sw), a < 2^64 := by
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
abbrev FastPool := BoundPool × List Nat × List Nat × Nat
def prepPool (vals : List Nat) (c : BoundPool) : Option FastPool :=
  let miss := vals.filter (fun w => !availM c.dom c.pm w)
  if miss.length > 2 then none
  else
    let consts := vals.filter (isConstM c.dom)
    some (c, miss, consts, consts.length)
def fastPoolCut (fp : FastPool) (k a b z : Nat) (ka kb : Bool) : Bool :=
  let c := fp.1
  let miss := fp.2.1
  let consts := fp.2.2.1
  let totC := fp.2.2.2
  if !miss.all (fun m => (!ka && m == a) || (!kb && m == b)) then false
  else
    let dropA := if !ka && consts.contains a then 1 else 0
    let dropB := if !kb && consts.contains b then 1 else 0
    let base := c.lb + (totC - dropA - dropB)
    if k + c.paid >= base + 1 then false
    else
      let m := z &&& c.dom
      if m == 0 || m == c.dom then true
      else if k + c.paid >= base then false
      else
        if k + c.paid + 1 < base && (!miss.contains a && !miss.contains b) then true
        else c.pm.contains m || c.pm.contains (c.dom ^^^ m)
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
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws) (hab : a.1 ≠ b.1) (hd : d < 4)
    (ndc : (bin d a.1 b.1 :: (delTwo ws a b ka kb).map Prod.fst).Nodup)
    (hcut : fastPoolCut fp k a.1 b.1 (bin d a.1 b.1) ka kb = true) :
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
        have hmem_del : ∀ u ∈ delTwo ws a b ka kb, u.1 = w → (ka = false → u ≠ a) ∧ (kb = false → u ≠ b) := by
          intro u hu _
          constructor
          · intro hka; subst hka
            have hsub1 : (delTwo ws a b false kb).Sublist (ws.erase a) := by
              cases kb <;> simp [delTwo, delOne, List.erase_sublist]
            have hu1 := hsub1.subset hu
            intro heq; subst heq
            exact List.Nodup.not_mem_erase (List.Nodup.of_map Prod.fst nd) hu1
          · intro hkb; subst hkb
            have hnd_ws : ws.Nodup := List.Nodup.of_map Prod.fst nd
            have hnd2 : (delOne ws a ka).Nodup := by cases ka; exact hnd_ws.erase a; exact hnd_ws
            have h2 := List.Nodup.not_mem_erase hnd2 (a := b)
            exact fun heq => h2 (heq ▸ hu)
        obtain ⟨u, hu, huw⟩ := List.mem_map.mp hw
        have ⟨hna', hnb'⟩ := hmem_del u hu huw
        rcases hm with ⟨hka, hwa⟩ | ⟨hkb, hwb⟩
        · exact hna' hka (unique_fst nd ((delTwo_sub ws a b ka kb).subset hu) ha (huw.trans hwa))
        · exact hnb' hkb (unique_fst nd ((delTwo_sub ws a b ka kb).subset hu) hb (huw.trans hwb))
      have hcnt := countP_delTwo_fst (isConstM c.dom) nd ha hb hab ka kb
      have hlen_f : ((ws.map Prod.fst).filter (isConstM c.dom)).length = (ws.map Prod.fst).countP (isConstM c.dom) := by
        rw [List.countP_eq_length_filter]
      have hca : ((ws.map Prod.fst).filter (isConstM c.dom)).contains a.1 = isConstM c.dom a.1 := by
        apply Bool.eq_iff_iff.mpr
        simp only [List.contains_iff_mem, List.mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨List.mem_map_of_mem ha, h⟩⟩
      have hcb : ((ws.map Prod.fst).filter (isConstM c.dom)).contains b.1 = isConstM c.dom b.1 := by
        apply Bool.eq_iff_iff.mpr
        simp only [List.contains_iff_mem, List.mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨List.mem_map_of_mem hb, h⟩⟩
      have hma : (!((ws.map Prod.fst).filter (fun w => !availM c.dom c.pm w)).contains a.1) = availM c.dom c.pm a.1 := by
        cases h : availM c.dom c.pm a.1 <;> simp [List.contains_iff_mem, List.mem_filter, List.mem_map_of_mem ha, h]
      have hmb : (!((ws.map Prod.fst).filter (fun w => !availM c.dom c.pm w)).contains b.1) = availM c.dom c.pm b.1 := by
        cases h : availM c.dom c.pm b.1 <;> simp [List.contains_iff_mem, List.mem_filter, List.mem_map_of_mem hb, h]
      rw [hlen_f, hca, hcb, hma, hmb] at hcut
      apply scalarPoolCut_sound (op := (d, a.1, b.1)) (rest := (delTwo ws a b ka kb).map Prod.fst) hP ndc
      unfold scalarPoolCut choiceOK
      simp only [choiceVal, h_all_avail, Bool.and_true, List.countP_cons, Bool.and_eq_true, decide_eq_true_eq, hd, true_and]
      rw [hcnt]
      set z := bin d a.1 b.1
      set m := z &&& c.dom
      set restC := (ws.map Prod.fst).countP (isConstM c.dom) - (if !ka && isConstM c.dom a.1 then 1 else 0) - (if !kb && isConstM c.dom b.1 then 1 else 0)
      change (k + c.paid + (!availM c.dom c.pm z).toNat < c.lb + (restC + if isConstM c.dom z then 1 else 0)) ∧
        ((!(!availM c.dom c.pm z)) || (availM c.dom c.pm a.1 && availM c.dom c.pm b.1)) = true
      have hbase_le : ¬(k + c.paid ≥ c.lb + restC + 1) := by
        intro hge; simp only [hge, ↓reduceIte, Bool.false_eq_true] at hcut
      simp only [hbase_le, ↓reduceIte] at hcut
      by_cases hzc : (m == 0 || m == c.dom) = true
      · have hisc : isConstM c.dom z = true := hzc
        have havz : availM c.dom c.pm z = true := by
          unfold availM; dsimp only; rw [show (z &&& c.dom == 0 || z &&& c.dom == c.dom) = true from hzc]; simp
        simp only [hisc, havz, Bool.not_true, Bool.not_false, Bool.toNat_false, Bool.true_or, ite_true, and_true]
        omega
      · have hzc_f : (m == 0 || m == c.dom) = false := Bool.eq_false_iff.mpr hzc
        have hisc : isConstM c.dom z = false := hzc_f
        have hav_eq : availM c.dom c.pm z = (c.pm.contains m || c.pm.contains (c.dom ^^^ m)) := by
          unfold availM; dsimp only
          have hm0 : (m == 0) = false := by cases h1 : (m == 0) <;> simp [h1] at hzc_f ⊢
          have hmd : (m == c.dom) = false := by cases h1 : (m == c.dom) <;> simp [h1] at hzc_f ⊢
          change (m == 0 || m == c.dom || c.pm.contains m || c.pm.contains (c.dom ^^^ m)) = _
          simp [hm0, hmd]
        simp only [hzc_f, Bool.false_eq_true, ↓reduceIte] at hcut
        have hlt_b : ¬(k + c.paid ≥ c.lb + restC) := by
          intro hge; simp only [hge, ↓reduceIte, Bool.false_eq_true] at hcut
        simp only [hlt_b, ↓reduceIte] at hcut
        rw [hav_eq, hisc]
        simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
        by_cases hfast : (k + c.paid + 1 < c.lb + restC ∧ (availM c.dom c.pm a.1 && availM c.dom c.pm b.1) = true)
        · cases hpm : (c.pm.contains m || c.pm.contains (c.dom ^^^ m)) <;>
            simp only [Bool.not_true, Bool.not_false, Bool.toNat_true, Bool.toNat_false, Bool.true_or, Bool.false_or, hfast.2] <;>
            exact ⟨by omega, trivial⟩
        · have hfast_b : (decide (k + c.paid + 1 < c.lb + restC) && (availM c.dom c.pm a.1 && availM c.dom c.pm b.1)) = false := by
            rw [Bool.eq_false_iff]; intro h; simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            exact hfast ⟨h.1, (Bool.and_eq_true _ _).mpr h.2⟩
          simp only [hfast_b, Bool.false_eq_true, ↓reduceIte] at hcut
          simp only [hcut, Bool.not_true, Bool.not_false, Bool.toNat_false, Bool.true_or]
          exact ⟨by omega, trivial⟩
def evalMoveBT (cap n fmask : Nat) (ws : List Decor)
    (fpools : List FastPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat)))
    (d : Nat) (a b : Decor) (z1 sz rs : Nat) (ka kb : Bool) : Bool :=
  let len := 1 + (n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len > cap then true else
    if ((rs ||| sz) &&& fmask) != fmask then true else
    if fpools.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 z1 ka kb) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChildBT [] autos prevBks (cap - 1) rest (d, a.1, b.1)
def testPairBT (cap n fmask : Nat) (ws : List Decor) (r00 r10 r01 r11 : Nat)
    (fpools : List FastPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (a b : Decor) (d : Nat) : Bool :=
  if n > cap + 1 then true else
  let z1 := bin d a.1 b.1
  if z1 == 0 || ws.any (fun v => v.1 == z1) then true else
    let sz := bin d a.2.1 b.2.1 ^^^ bin d a.2.2 b.2.2
    let go := evalMoveBT cap n fmask ws fpools autos prevBks d a b z1 sz
    if n > cap then go r00 false false
    else if n == cap then go r00 false false && go r10 true false && go r01 false true
    else go r00 false false && go r10 true false && go r01 false true && go r11 true true
def testAllBT (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (fpools : List FastPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) : List Decor → Bool
  | [] => true
  | a :: bs =>
    let sa := dsep a
    let r01 := takeOne cov sa
    bs.all (fun b =>
      let sb := dsep b
      let r00 := takeTwo cov sa sb
      let r10 := takeOne cov sb
      [0, 1, 2, 3].all (testPairBT cap n fmask ws r00 r10 r01 cov.1 fpools autos prevBks a b)) &&
      testAllBT cap n fmask ws cov fpools autos prevBks bs
lemma evalMoveBT_sound {raw T pos neg ws fpools autos prevBks cap a b d ka kb}
    (hT : T < 2^64) (gp : goodPairs T pos neg) (hf : ∀ w ∈ ws, faithful pos neg w)
    (nd : (ws.map Prod.fst).Nodup) (hlt : ∀ w ∈ ws, w.1 < 2^64)
    (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) (hcap : 0 < cap) (_hd : d < 4)
    (hPools : ∀ fp ∈ fpools, ValidPool raw T fp.1 ∧ prepPool (ws.map Prod.fst) fp.1 = some fp)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (cap - 1) xs.toFinset) prevBks)
    (_hnz : bin d a.1 b.1 ≠ 0) (hfr : bin d a.1 b.1 ∉ ws.map Prod.fst)
    (test : evalMoveBT cap ws.length (fullMask pos.length) ws fpools autos prevBks d a b (bin d a.1 b.1) (dsep (dbin d a b)) (restCov (coverage ws) (dsep a) (dsep b) ka kb) ka kb = true) :
    Impossible T (cap - 1) ((dbin d a b :: delTwo ws a b ka kb).map Prod.fst).toFinset := by
  let z := dbin d a b
  let rest := delTwo ws a b ka kb
  let child := (z :: rest).map Prod.fst
  have sub : rest.Sublist ws := delTwo_sub ws a b ka kb
  have ndc : child.Nodup := by
    simp only [child, List.map_cons, List.nodup_cons]
    exact ⟨fun hm => hfr ((sub.map Prod.fst).subset hm), (sub.map Prod.fst).nodup nd⟩
  have hltc : ∀ x ∈ child, x < 2^64 := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact bin_lt d a.1 b.1 (hlt a ha) (hlt b hb)
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx; exact hlt w (sub.subset hw)
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
  dsimp only [z] at hcov_b
  simp only [hleq, hnotgt, ↓reduceIte, hcov_b, Bool.false_eq_true] at test
  have hab1 : a.1 ≠ b.1 := fun eq => ne (unique_fst nd ha hb eq)
  by_cases hfp : fpools.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 (bin d a.1 b.1) ka kb) = true
  · obtain ⟨fp, hmem, hcut⟩ := List.any_eq_true.mp hfp
    have ⟨hv, hpr⟩ := hPools fp hmem
    exact fastPoolCut_sound hv hpr nd ha hb hab1 _hd ndc hcut k hk h
  · have hfp_f : fpools.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 (bin d a.1 b.1) ka kb) = false := Bool.eq_false_iff.mpr hfp
    simp only [hfp_f, Bool.false_eq_true, ↓reduceIte] at test
    exact closeChildBT_sound (raw := raw) (op := (d, a.1, b.1)) (rest := rest.map Prod.fst) hT (fun _ hm => (List.not_mem_nil hm).elim) hAutos hPrev ndc hltc test k hk h
lemma testAllBT_pair {cap n fmask ws cov fpools autos prevBks l}
    (h : testAllBT cap n fmask ws cov fpools autos prevBks l = true)
    {a b : Decor} (ha : a ∈ l) (hb : b ∈ l) (ne : a ≠ b) :
    (∀ d < 4, testPairBT cap n fmask ws (takeTwo cov (dsep a) (dsep b)) (takeOne cov (dsep b)) (takeOne cov (dsep a)) cov.1 fpools autos prevBks a b d = true) ∨
    (∀ d < 4, testPairBT cap n fmask ws (takeTwo cov (dsep b) (dsep a)) (takeOne cov (dsep a)) (takeOne cov (dsep b)) cov.1 fpools autos prevBks b a d = true) := by
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
    (hT : T < 2^64) (gp : goodPairs T pos neg)
    (hf : ∀ w ∈ ws, faithful pos neg w) (nd : (ws.map Prod.fst).Nodup)
    (hlt : ∀ w ∈ ws, w.1 < 2^64) (out : T ∉ ws.map Prod.fst)
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
      (ht : testPairBT cap ws.length (fullMask pos.length) ws (takeTwo (coverage ws) (dsep x) (dsep y)) (takeOne (coverage ws) (dsep y)) (takeOne (coverage ws) (dsep x)) (coverage ws).1 fpools autos prevBks x y d' = true) :
      Impossible T (cap - 1) (childTwo (ws.map Prod.fst) x.1 y.1 d' k1 k2).toFinset := by
    rw [← delTwo_map_toFinset nd hx hy nxy d' k1 k2]
    have hem : evalMoveBT cap ws.length (fullMask pos.length) ws fpools autos prevBks d' x y (bin d' x.1 y.1) (dsep (dbin d' x y)) (restCov (coverage ws) (dsep x) (dsep y) k1 k2) k1 k2 = true := by
      have hnz_b : (bin d' x.1 y.1 == 0) = false := beq_false_of_ne hnz'
      have hfr_b : (ws.any (fun v => v.1 == bin d' x.1 y.1)) = false := by
        rw [Bool.eq_false_iff]; intro h; obtain ⟨v, hv, heq⟩ := List.any_eq_true.mp h
        exact hfr' ((beq_iff_eq.mp heq) ▸ List.mem_map_of_mem hv)
      by_cases hlen : 1 + (ws.length - (if k1 then 0 else 1) - (if k2 then 0 else 1)) > cap
      · unfold evalMoveBT; simp [hlen]
      · unfold testPairBT at ht
        have hnot1 : ¬(ws.length > cap + 1) := by cases k1 <;> cases k2 <;> simp at hlen <;> omega
        simp only [hnot1, ↓reduceIte, hnz_b, hfr_b, Bool.false_or, Bool.false_eq_true] at ht
        by_cases hgt : ws.length > cap
        · simp only [hgt, ↓reduceIte] at ht
          cases k1 <;> cases k2
          · exact ht
          · simp at hlen; omega
          · simp at hlen; omega
          · simp at hlen; omega
        · simp only [hgt, ↓reduceIte] at ht
          by_cases heq : ws.length = cap
          · simp only [heq, beq_self_eq_true, ↓reduceIte, Bool.and_eq_true] at ht ⊢
            cases k1 <;> cases k2
            · exact ht.1.1
            · exact ht.2
            · exact ht.1.2
            · simp at hlen; omega
          · have hneq : (ws.length == cap) = false := beq_false_of_ne heq
            simp only [hneq, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at ht
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
    (hbase : ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^64) :
    btAll (fun x => faithful pos neg x ∧ x.1 < 2^64) (buildWiresBT depth base steps) := by
  have hdef : faithful pos neg (0, 0, 0) ∧ (0 : Nat) < 2^64 := ⟨faithful_zero pos neg, by decide⟩
  unfold buildWiresBT
  have h0 : btAll (fun x => faithful pos neg x ∧ x.1 < 2^64) (btOfList depth base) := btAll_ofList hbase
  have hgo : ∀ (ss : List (Nat × Nat × Nat)) (acc : Nat × BT Decor),
      btAll (fun x => faithful pos neg x ∧ x.1 < 2^64) acc.2 →
      btAll (fun x => faithful pos neg x ∧ x.1 < 2^64)
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
def nodupNats : List Nat → Bool
  | [] => true
  | x :: xs => !(xs.contains x) && nodupNats xs
lemma nodupNats_sound : ∀ {l : List Nat}, nodupNats l = true → l.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    simp only [nodupNats, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at h
    exact List.nodup_cons.mpr ⟨h.1, nodupNats_sound h.2⟩
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
  nodupNats vals && !(vals.contains T) &&
    (k == 0 || testAllBT k ws.length fmask ws (coverage ws) fpools nodeAutos prevBks ws)
def checkNodesBT (W : BT Decor) (T fmask : Nat)
    (poolTable : BT (Option BoundPool)) (autosTable : BT (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (k : Nat) (nodes : List NodeSpec) : Bool :=
  nodes.all (checkNodeBT W T fmask poolTable autosTable prevBks k)
lemma checkNodeBT_sound {W : BT Decor} {raw pos neg T poolTable autosTable prevBks k ns}
    (hT : T < 2^64) (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^64) W)
    (hPoolTable : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) poolTable)
    (hAutos : btAll (fun sw => swapsValid sw = true ∧ permWord sw T = T) autosTable)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (k - 1) xs.toFinset) prevBks)
    (ok : checkNodeBT W T (fullMask pos.length) poolTable autosTable prevBks k ns = true) :
    Impossible T k ((ns.1.map fun idx => (btGet (0, 0, 0) W idx).1).toFinset) := by
  have hdef : faithful pos neg (0, 0, 0) ∧ (0 : Nat) < 2^64 := ⟨faithful_zero pos neg, by decide⟩
  have hget (idx : Nat) : faithful pos neg (btGet (0, 0, 0) W idx) ∧ (btGet (0, 0, 0) W idx).1 < 2^64 :=
    btAll_get hW hdef idx
  unfold checkNodeBT at ok
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem, Bool.or_eq_true, beq_iff_eq] at ok
  let ws := ns.1.map fun idx => btGet (0, 0, 0) W idx
  have hmap : ws.map Prod.fst = ns.1.map fun idx => (btGet (0, 0, 0) W idx).1 := by simp [ws, List.map_map, Function.comp_def]
  rw [← hmap]
  apply nodeBT_sound hT gp
    (fun w hw => by obtain ⟨idx, _, rfl⟩ := List.mem_map.mp hw; exact (hget idx).1)
    (nodupNats_sound ok.1.1)
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
    btUpdate [] 8 acc (hashWs64 xs) (fun b => if b.contains xs then b else xs :: b)) BT.empty
lemma buildBucketsBT_sound {W : BT Decor} {raw pos neg T poolTable autosTable prevBks k}
    {nodes : List NodeSpec}
    (hT : T < 2^64) (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^64) W)
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
  have hinit : btAll (fun bk => ∀ xs ∈ bk, Impossible T k xs.toFinset) (BT.empty : BT (List (List Nat))) := .empty
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
  have hinit : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) (BT.empty : BT (Option BoundPool)) := .empty
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
lemma checkNodesBT_mem {W : BT Decor} {raw pos neg T poolTable autosTable prevBks k nodes}
    (hT : T < 2^64) (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^64) W)
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
  have hinit : btAll (fun bk => ∀ xs ∈ bk, Impossible T k xs.toFinset) (BT.empty : BT (List (List Nat))) := .empty
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
lemma obs_all64_xor (G : Nat) : obs (ALL64 ^^^ G) = invW (obs G) := by
  funext r
  have hall : ALL64.testBit r.val = true := by
    simp only [ALL64]; have hr := r.isLt; simpa [hr] using Nat.testBit_two_pow_sub_one 64 r.val
  simp only [obs, invW, Nat.testBit_xor, hall, Bool.true_xor]
lemma lower_slice_flip {roots other : List Nat} {T G : Nat}
    (hT0 : T ≠ 0) (hTlt : T < 2^64) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^64 ∧ a.testBit 0 = false)
    (hG0 : G ≠ 0) (hGlt : G < 2^64) (hGb0 : G.testBit 0 = false)
    (f : Row → Row) (eq : renameW f T = G ∨ renameW f T = ALL64 ^^^ G)
    (covered : ∀ a ∈ roots, Avail (other.map obs) (restrictW f (obs a)))
    (singles : Finset Nat) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (restrictW f (obs a)))
    (L : Nat) (prior : Lower other G L) : Lower roots T (L + singles.card) := by
  rcases eq with heq | heq
  · exact lower_slice hT0 hTlt hTb0 hR hG0 hGlt hGb0 f heq covered singles necessary constant L prior
  · classical
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
    have gc : restrictW f (obs T) = invW (obs G) :=
      (obs_renameW f T).symm.trans ((congrArg obs heq).trans (obs_all64_xor G))
    have hnc : ¬Constant (invW (obs G)) := fun hc => obs_not_const hG0 hGlt hGb0 (invW_inv (obs G) ▸ invW_const hc)
    have hsup : Supply (other.map obs) ((front.map obs).map (restrictW f)) := by
      intro v hv
      obtain ⟨_, hm', rfl⟩ := List.mem_map.mp hv
      obtain ⟨a, ha', rfl⟩ := List.mem_map.mp hm'
      exact covered a (sub a (fe ▸ List.mem_toFinset.mpr ha'))
    obtain ⟨q, next, hq, hav, hbound⟩ :=
      contraction (gc ▸ hnc) (restrict_run f (live_to_run run front nd fe))
        (other.map obs) (show Reach (other.map obs) 0 (other.map obs) from rfl) hsup
    have havG : Avail next (obs G) := by
      rw [gc] at hav; simpa [invW_inv] using avail_inv hav
    have hlo := prior q next hq havG
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
    omega
def liftCheckF (z o : Nat) (roots : List Nat) (T : Nat) (other : List Nat) (G : Nat)
    (essPairs : List (Nat × Nat × Nat)) : Bool :=
  checkProper T && checkRoots roots && checkProper G &&
    decide (essPairs.map Prod.fst).Nodup &&
    (fixWord z o T == G || fixWord z o T == ALL64 ^^^ G) &&
    roots.all (fun a => freeIn other (fixWord z o a)) &&
    essPairs.all (fun e => checkEss1 T roots e.1 e.2.1 e.2.2 &&
      (fixWord z o e.1 == 0 || fixWord z o e.1 == ALL64))
lemma lift_of_f {z o roots T other G essPairs L} (ok : liftCheckF z o roots T other G essPairs = true)
    (hL : Lower other G L) : Lower roots T (L + essPairs.length) := by
  simp only [liftCheckF, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨⟨hT, hR⟩, hG⟩, hnd⟩, heq⟩, hcov⟩, hess⟩ := ok
  have ⟨p1a, p1b, p1c⟩ := checkProper_sound hT
  have ⟨p2a, p2b, p2c⟩ := checkProper_sound hG
  have hR' := checkRoots_sound hR
  have heq' : renameW (fixRow z o) T = G ∨ renameW (fixRow z o) T = ALL64 ^^^ G := by
    rw [← fixWord_eq_renameW]; exact heq
  have hcov' : ∀ a ∈ roots, Avail (other.map obs) (restrictW (fixRow z o) (obs a)) := fun a ha =>
    freeIn_sound ((fixWord_eq_renameW z o a).symm ▸ hcov a ha)
  have hcard : (essPairs.map Prod.fst).toFinset.card = essPairs.length := by
    rw [List.toFinset_card_of_nodup hnd, List.length_map]
  rw [← hcard]
  apply lower_slice_flip p1a p1b p1c hR' p2a p2b p2c (fixRow z o) heq' hcov' (essPairs.map Prod.fst).toFinset _ _ L hL
  · intro a ha
    obtain ⟨⟨v, r, s⟩, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    exact checkEss1_sound (hess (v, r, s) hm).1
  · intro a ha
    obtain ⟨⟨v, r, s⟩, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    have hc := (hess (v, r, s) hm).2
    simp only [fixWord_eq_renameW] at hc
    rw [← obs_renameW]
    rcases hc with h0 | h1
    · exact ⟨false, by rw [h0]; funext r'; simp [obs]⟩
    · exact ⟨true, by rw [h1]; funext r'; simp only [obs, ALL64]; have := r'.isLt; exact Nat.testBit_two_pow_sub_one 64 r'.val |> fun e => by simpa [this] using e⟩
def sliceDirectCheckF (z o : Nat) (raw : List Nat) (T : Nat) (qRoots : List Nat) (qGoal : Nat) : Bool :=
  decide (z < 64) && decide (o < 64) && ((z &&& o) == 0) &&
    checkProper qGoal && checkRoots qRoots &&
    (fixWord z o T == qGoal || fixWord z o T == ALL64 ^^^ qGoal) &&
    raw.all (fun a => freeIn qRoots (fixWord z o a))
lemma slice_fast_direct_f {z o raw T qRoots qGoal qL}
    (ok : sliceDirectCheckF z o raw T qRoots qGoal = true)
    (hPrior : Lower qRoots qGoal qL) :
    Slice raw T (subcubeFast z o) qL := by
  simp only [sliceDirectCheckF, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨⟨hz, ho⟩, hzo⟩, hGp⟩, hQR⟩, heq⟩, hcov⟩ := ok
  rw [subcubeFast_eq_subcube z o hz ho hzo]
  have ⟨g0, glt, gb0⟩ := checkProper_sound hGp
  rcases heq with heq | heq
  · refine ⟨fixRow z o, qRoots, subcube_fixRow z o hz ho hzo,
      fun a ha => freeIn_sound ((fixWord_eq_renameW z o a).symm ▸ hcov a ha),
      by rw [← obs_renameW, ← fixWord_eq_renameW, heq]; exact obs_not_const g0 glt gb0, ?_⟩
    rw [← obs_renameW, ← fixWord_eq_renameW, heq]
    exact hPrior
  · refine ⟨fixRow z o, qRoots, subcube_fixRow z o hz ho hzo,
      fun a ha => freeIn_sound ((fixWord_eq_renameW z o a).symm ▸ hcov a ha),
      by rw [← obs_renameW, ← fixWord_eq_renameW, heq, obs_all64_xor]; exact fun hc => obs_not_const g0 glt gb0 (invW_inv (obs qGoal) ▸ invW_const hc), ?_⟩
    rw [← obs_renameW, ← fixWord_eq_renameW, heq, obs_all64_xor]
    intro p bank hr hav
    exact hPrior p bank hr (by simpa [invW_inv] using avail_inv hav)
def identRow (u v : Nat) (r : Row) : Row :=
  if r.val.testBit u == r.val.testBit v then r
  else ⟨(r.val ^^^ (1 <<< v)) % 64, Nat.mod_lt _ (by decide)⟩
def identDom (u v : Nat) : Nat := ALL64 ^^^ (VAR u ^^^ VAR v)
def identWord (u v w : Nat) : Nat :=
  (List.range 64).foldr (fun r acc =>
    let fr := if r.testBit u == r.testBit v then r else (r ^^^ (1 <<< v)) % 64
    if w.testBit fr then acc ||| (1 <<< r) else acc) 0
lemma identWord_eq_renameW (u v w : Nat) : identWord u v w = renameW (identRow u v) w := by
  apply Nat.eq_of_testBit_eq; intro r
  unfold identWord
  rw [testBit_foldr_bits]
  by_cases hr : r < 64
  · rw [testBit_renameW (identRow u v) w ⟨r, hr⟩]
    simp only [List.mem_range, hr, decide_true, Bool.true_and, identRow]
    split <;> rfl
  · simp only [List.mem_range, hr, decide_false, Bool.false_and]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))).symm
lemma identDom_identRow (u v : Nat) (hu : u < 6) (hv : v < 6) (r : Row) :
    (identDom u v).testBit (identRow u v r).val = true := by
  revert r
  interval_cases u <;> interval_cases v <;> decide +kernel
def sliceIdentCheck (u v : Nat) (raw : List Nat) (T : Nat) (qRoots : List Nat) (qGoal : Nat) : Bool :=
  decide (u < 6) && decide (v < 6) &&
    checkProper qGoal && checkRoots qRoots &&
    (identWord u v T == qGoal || identWord u v T == ALL64 ^^^ qGoal) &&
    raw.all (fun a => freeIn qRoots (identWord u v a))
lemma slice_ident {u v raw T qRoots qGoal qL}
    (ok : sliceIdentCheck u v raw T qRoots qGoal = true)
    (hPrior : Lower qRoots qGoal qL) :
    Slice raw T (identDom u v) qL := by
  simp only [sliceIdentCheck, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨hu, hv⟩, hGp⟩, hQR⟩, heq⟩, hcov⟩ := ok
  have ⟨g0, glt, gb0⟩ := checkProper_sound hGp
  rcases heq with heq | heq
  · refine ⟨identRow u v, qRoots, identDom_identRow u v hu hv,
      fun a ha => freeIn_sound ((identWord_eq_renameW u v a).symm ▸ hcov a ha),
      by rw [← obs_renameW, ← identWord_eq_renameW, heq]; exact obs_not_const g0 glt gb0, ?_⟩
    rw [← obs_renameW, ← identWord_eq_renameW, heq]
    exact hPrior
  · refine ⟨identRow u v, qRoots, identDom_identRow u v hu hv,
      fun a ha => freeIn_sound ((identWord_eq_renameW u v a).symm ▸ hcov a ha),
      by rw [← obs_renameW, ← identWord_eq_renameW, heq, obs_all64_xor]; exact fun hc => obs_not_const g0 glt gb0 (invW_inv (obs qGoal) ▸ invW_const hc), ?_⟩
    rw [← obs_renameW, ← identWord_eq_renameW, heq, obs_all64_xor]
    intro p bank hr hav
    exact hPrior p bank hr (by simpa [invW_inv] using avail_inv hav)

def freeInFlip (other : List Nat) (w : Nat) : Bool :=
  w == 0 || w == ALL64 || other.contains w || other.contains (ALL64 ^^^ w)
lemma freeInFlip_sound {other : List Nat} {f : Row → Row} {a : Nat}
    (ok : freeInFlip other (renameW f a) = true) :
    Avail (other.map obs) (restrictW f (obs a)) := by
  rw [← obs_renameW]
  simp only [freeInFlip, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at ok
  rcases ok with ((h0 | h1) | hm) | hm
  · exact Or.inr (Or.inl ⟨false, by rw [h0]; funext r; simp [obs]⟩)
  · exact Or.inr (Or.inl ⟨true, by rw [h1]; funext r; simp only [obs, ALL64]; have := r.isLt; exact Nat.testBit_two_pow_sub_one 64 r.val |> fun e => by simpa [this] using e⟩)
  · exact Or.inl (List.mem_map_of_mem hm)
  · have hmem : obs (ALL64 ^^^ renameW f a) ∈ other.map obs := List.mem_map_of_mem hm
    rw [obs_all64_xor] at hmem
    exact Or.inr (Or.inr hmem)
def fiRowVal (z o u v : Nat) (fl : Bool) (r : Nat) : Nat :=
  let r1 := ((r &&& (63 ^^^ z)) ||| o) % 64
  let want := if fl then !r1.testBit u else r1.testBit u
  if r1.testBit v == want then r1 else (r1 ^^^ (1 <<< v)) % 64
lemma fiRowVal_lt (z o u v : Nat) (fl : Bool) (r : Nat) : fiRowVal z o u v fl r < 64 := by
  unfold fiRowVal; dsimp only; split <;> split <;> exact Nat.mod_lt _ (by decide : 0 < 64)
def fiRow (z o u v : Nat) (fl : Bool) (r : Row) : Row := ⟨fiRowVal z o u v fl r.val, fiRowVal_lt z o u v fl r.val⟩
def fiDom (z o u v : Nat) (fl : Bool) : Nat :=
  subcubeFast z o &&& (if fl then VAR u ^^^ VAR v else ALL64 ^^^ (VAR u ^^^ VAR v))
def fiWord (z o u v : Nat) (fl : Bool) (w : Nat) : Nat :=
  (List.range 64).foldr (fun r acc => if w.testBit (fiRowVal z o u v fl r) then acc ||| (1 <<< r) else acc) 0
lemma fiWord_eq_renameW (z o u v : Nat) (fl : Bool) (w : Nat) : fiWord z o u v fl w = renameW (fiRow z o u v fl) w := by
  apply Nat.eq_of_testBit_eq; intro r
  unfold fiWord; rw [testBit_foldr_bits]
  by_cases hr : r < 64
  · rw [testBit_renameW (fiRow z o u v fl) w ⟨r, hr⟩]
    simp [hr, fiRow]
  · simp only [List.mem_range, hr, decide_false, Bool.false_and]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))).symm
def sliceFICheck (z o u v : Nat) (fl : Bool) (raw : List Nat) (T : Nat) (qRoots : List Nat) (qGoal : Nat) : Bool :=
  (List.range 64).all (fun r => (fiDom z o u v fl).testBit (fiRowVal z o u v fl r)) &&
    checkProper qGoal && checkRoots qRoots &&
    (fiWord z o u v fl T == qGoal || fiWord z o u v fl T == ALL64 ^^^ qGoal) &&
    raw.all (fun a => freeInFlip qRoots (fiWord z o u v fl a))
lemma slice_fi {z o u v fl raw T qRoots qGoal qL}
    (ok : sliceFICheck z o u v fl raw T qRoots qGoal = true)
    (hPrior : Lower qRoots qGoal qL) :
    Slice raw T (fiDom z o u v fl) qL := by
  simp only [sliceFICheck, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at ok
  obtain ⟨⟨⟨⟨hdom, hGp⟩, hQR⟩, heq⟩, hcov⟩ := ok
  have hdom' : ∀ r : Row, (fiDom z o u v fl).testBit (fiRow z o u v fl r).val = true := fun r => hdom r.val r.isLt
  have ⟨g0, glt, gb0⟩ := checkProper_sound hGp
  rcases heq with heq | heq
  · refine ⟨fiRow z o u v fl, qRoots, hdom',
      fun a ha => freeInFlip_sound ((fiWord_eq_renameW z o u v fl a).symm ▸ hcov a ha),
      by rw [← obs_renameW, ← fiWord_eq_renameW, heq]; exact obs_not_const g0 glt gb0, ?_⟩
    rw [← obs_renameW, ← fiWord_eq_renameW, heq]; exact hPrior
  · refine ⟨fiRow z o u v fl, qRoots, hdom',
      fun a ha => freeInFlip_sound ((fiWord_eq_renameW z o u v fl a).symm ▸ hcov a ha),
      by rw [← obs_renameW, ← fiWord_eq_renameW, heq, obs_all64_xor]; exact fun hc => obs_not_const g0 glt gb0 (invW_inv (obs qGoal) ▸ invW_const hc), ?_⟩
    rw [← obs_renameW, ← fiWord_eq_renameW, heq, obs_all64_xor]
    intro p bank hr hav
    exact hPrior p bank hr (by simpa [invW_inv] using avail_inv hav)

def mkBase (pos neg : List Nat) (rs : List Nat) : List Decor :=
  rs.map fun w => (w, projBits pos w, projBits neg w)
lemma mkBase_ok {pos neg rs} (hR : checkRoots rs = true) :
    ∀ x ∈ mkBase pos neg rs, faithful pos neg x ∧ x.1 < 2^64 := by
  have hr := checkRoots_sound hR
  intro x hx
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
  exact ⟨⟨rfl, rfl⟩, (hr w hw).1⟩
def evalInput6 (r : Row) : Fin 6 → Bool := fun i => r.val.testBit i.val
def packInput6 (x : Fin 6 → Bool) : Row :=
  ⟨(x 0).toNat + 2 * (x 1).toNat + 4 * (x 2).toNat + 8 * (x 3).toNat +
   16 * (x 4).toNat + 32 * (x 5).toNat, by
    cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> cases x 4 <;> cases x 5 <;> decide⟩
lemma evalInput6_packInput6 (x : Fin 6 → Bool) : evalInput6 (packInput6 x) = x := by
  funext i
  have h : ∀ (b0 b1 b2 b3 b4 b5 : Bool) (j : Fin 6),
      ((b0.toNat + 2 * b1.toNat + 4 * b2.toNat + 8 * b3.toNat +
        16 * b4.toNat + 32 * b5.toNat).testBit j.val) =
        ([b0, b1, b2, b3, b4, b5].getD j.val false) := by decide +kernel
  have hi := h (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) i
  fin_cases i <;> simpa [evalInput6, packInput6] using hi
lemma var_testBit6 (i : Fin 6) (r : Row) : (VAR i.val).testBit r.val = r.val.testBit i.val := by
  revert i r; decide +kernel
lemma sw_extract_full6 (T : Nat) (hT0 : T ≠ 0) (hTlt : T < 2^64) (hTb0 : T.testBit 0 = false)
    (gs : List Gate) (o : Nat)
    (legal : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (he : ∀ r : Row, Circuit.eval ⟨gs, o⟩ (List.ofFn (evalInput6 r)) = T.testBit r.val) :
    ∃ k S, k ≤ gs.countP isBin ∧ Live T k S ∧ ∀ a ∈ S, a ∈ varsOf 63 := by
  let seeds : List SWire := (varsOf 63).map (fun v => (false, v))
  have hseeds_lt : ∀ u ∈ seeds, u.2 < 2^64 ∧ u.2.testBit 0 = false := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
    have hall : (varsOf 63).all (fun a => decide (a < 2^64) && !a.testBit 0) = true := by decide +kernel
    have h1 := List.all_eq_true.mp hall v hv
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h1
    exact h1
  let final := swExec gs seeds
  let out := final.getD o swZero
  have hfinal_lt : out.2 < 2^64 ∧ out.2.testBit 0 = false := by
    simp only [out, List.getD_eq_getElem?_getD]
    cases eq : final[o]? with
    | none => exact ⟨by decide, by decide⟩
    | some a => exact swExec_lt gs seeds hseeds_lt a (List.mem_of_getElem? eq)
  have hread_seeds (r : Row) : seeds.map (swRead r.val) = List.ofFn (evalInput6 r) := by
    apply List.ext_getElem
    · simp only [seeds, List.length_map, List.length_ofFn]; decide
    · intro i hi1 hi2
      have hi6 : i < 6 := by simpa using hi2
      have hv : (varsOf 63)[i]? = some (VAR i) := by
        interval_cases i <;> decide
      simp only [List.getElem_map, List.getElem_ofFn, seeds, evalInput6, swRead, Bool.false_bne]
      have hget : (varsOf 63)[i]'(by simpa [seeds] using hi1) = VAR i := by
        have := List.getElem?_eq_some_iff.mp hv; exact this.2
      rw [hget]
      exact var_testBit6 ⟨i, hi6⟩ r
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
    by_cases hr : r < 64
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
lemma replace_of_lower6 (T : Nat) (hT0 : T ≠ 0) (hTlt : T < 2^64) (hTb0 : T.testBit 0 = false)
    (L : Nat) (hLow : Lower (varsOf 63) T L)
    (wit : List Gate) (wo : Nat) (hwLen : wit.length ≤ L + 1)
    (hwMono : PEqualNP.MetaComplexity.Monotone2 ⟨wit, wo⟩)
    (tgt : (Fin 6 → Bool) → Bool)
    (hTgtT : ∀ r : Row, tgt (evalInput6 r) = T.testBit r.val)
    (hwEvalR : ∀ r : Row, Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput6 r)) = T.testBit r.val)
    (s : Nat) (hs : PEqualNP.MetaComplexity.HasCircuitSize 6 tgt s) :
    ∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧
      ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = tgt x := by
  obtain ⟨⟨gates, o⟩, hfan, hsize, spec⟩ := hs
  have legal : ∀ g ∈ gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨hop, hlen⟩ := hfan g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    exact ⟨hop, hlen⟩
  have hwEval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wit, wo⟩ (List.ofFn x) = tgt x := by
    intro x
    have hx := evalInput6_packInput6 x
    rw [← hx]
    exact (hwEvalR (packInput6 x)).trans (hTgtT (packInput6 x)).symm
  by_cases hn : ∃ g ∈ gates, g.op = .not
  · have hlt : gates.countP isBin < gates.length := by
      apply Nat.lt_of_le_of_ne List.countP_le_length
      intro eq
      obtain ⟨g, hg, hop⟩ := hn
      have bad := List.countP_eq_length.mp eq g hg
      simp [isBin, hop] at bad
    obtain ⟨k, S, hk, hlive, hsub⟩ := sw_extract_full6 T hT0 hTlt hTb0 gates o legal (fun r => (spec (evalInput6 r)).trans (hTgtT r))
    have hnd : S.toList.Nodup := Finset.nodup_toList S
    have hrun := live_to_run hlive S.toList hnd (by simp)
    have hsup : Supply ((varsOf 63).map obs) (S.toList.map obs) := fun v hv => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
      exact Or.inl (List.mem_map_of_mem (hsub a (Finset.mem_toList.mp ha)))
    obtain ⟨q, next, hq, hav, hbound⟩ :=
      contraction (obs_not_const hT0 hTlt hTb0) hrun ((varsOf 63).map obs)
        (show Reach ((varsOf 63).map obs) 0 ((varsOf 63).map obs) from rfl) hsup
    have hlo := hLow q next hq hav
    have hcsz : (⟨wit, wo⟩ : Circuit).size = wit.length := rfl
    have hgsz : (⟨gates, o⟩ : Circuit).size = gates.length := rfl
    refine ⟨⟨wit, wo⟩, hwMono, ?_, hwEval⟩
    omega
  · refine ⟨⟨gates, o⟩, ?_, hsize, spec⟩
    intro g hg
    obtain ⟨hop, hlen⟩ := legal g hg
    refine ⟨?_, hlen⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hn ⟨g, hg, h⟩).elim
def q (sl : Nat) (cs : List Nat) : Option PoolSpec :=
  some (sl, cs.map fun x => (x % 4, (x / 4) % 1024, x / 4096))
def r (a n : Nat) : List Nat := List.range' a n
def b6 : List Nat := [0,1,2,3,4,5]
def b5 : List Nat := [0,1,2,3,4]
def u6 (w p : List Nat) : NodeSpec := (b6 ++ w, p, [0])
def e6 (w p : List Nat) : NodeSpec := (b6 ++ w, p, [])
def a6 (w p a : List Nat) : NodeSpec := (b6 ++ w, p, a)
def u5 (w p : List Nat) : NodeSpec := (b5 ++ w, p, [0])
def e5 (w p : List Nat) : NodeSpec := (b5 ++ w, p, [])
def a5 (w p a : List Nat) : NodeSpec := (b5 ++ w, p, a)

def g_0 := 0xe8e8e8e8e8e8e8e8
def r_0 : List Nat := varsOf 7
def p_0 : List Nat := [3,3,5,5,6,6]
def q_0 : List Nat := [2,1,4,1,4,2]
def F_0 : Nat := fullMask 6
set_option maxHeartbeats 0 in
lemma gp_0 : goodPairs g_0 p_0 q_0 := goodPairs_of (by decide +kernel)
def W_0 : BT Decor := buildWiresBT 2 (mkBase p_0 q_0 r_0) []
lemma W_0_ok : btAll (fun x => faithful p_0 q_0 x ∧ x.1 < 2^64) W_0 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_0 : List (List (Nat × Nat)) := [[]]
def A_0 : BT (List (Nat × Nat)) := btOfList 1 al_0
set_option maxHeartbeats 0 in
lemma A_0_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_0 = g_0) A_0 := btAll_ofList (autos_of (by decide +kernel))
def S_0 : BT (Option (Nat × Nat)) := btOfList 1 []
lemma S_0_ok : btAll (fun o => ∀ p, o = some p → Slice r_0 g_0 p.1 p.2) S_0 := btAll_ofList (fun _ h => (List.not_mem_nil h).elim)
def ps_0 : BT (Option PoolSpec) := btOfList 1 []
def B_0_2 : BT (List (List Nat)) := BT.empty
lemma B_0_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_0 2 xs.toFinset) B_0_2 := .empty
def U_0_3 : List Nat := []
def P_0_3 : BT (Option BoundPool) := buildPoolsSubBT 1 W_0 r_0 S_0 ps_0 U_0_3
def N_0_3 : List NodeSpec := [([0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_0_3 : checkNodesBT W_0 g_0 F_0 P_0_3 A_0 B_0_2 3 N_0_3 = true := by decide +kernel
def B_0_3 : BT (List (List Nat)) := buildBucketsBT W_0 N_0_3
set_option maxRecDepth 500000 in
lemma B_0_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_0 3 xs.toFinset) B_0_3 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok (buildPoolsSubBT_sound S_0_ok) A_0_ok B_0_2_ok C_0_3
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_0_ok : forestRootCheck r_0 g_0 [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_0_in : bucketContainsBT B_0_3 r_0 = true := by decide +kernel
lemma low_0 : Lower r_0 g_0 4 := lower_of_forestBT root_0_ok B_0_3_ok root_0_in
def g_1 := 0xe880e880e880e880
def r_1 : List Nat := varsOf 15
def p_1 : List Nat := [7,7,7,11,11,11,13,13,13,14,14,14]
def q_1 : List Nat := [6,5,3,10,9,3,12,9,5,12,10,6]
def F_1 : Nat := fullMask 12
set_option maxHeartbeats 0 in
lemma gp_1 : goodPairs g_1 p_1 q_1 := goodPairs_of (by decide +kernel)
def W_1 : BT Decor := buildWiresBT 4 (mkBase p_1 q_1 r_1) [(0,0,1),(0,0,2),(0,1,2),(0,6,3),(3,7,0),(0,2,3),(3,9,0),(0,4,2)]
lemma W_1_ok : btAll (fun x => faithful p_1 q_1 x ∧ x.1 < 2^64) W_1 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_1 : List (List (Nat × Nat)) := [[],[(2,3)],[(1,2)],[(1,2),(2,3)],[(0,1)],[(0,1),(2,3)],[(0,2),(1,2)],[(0,2),(1,2),(2,3)],[(0,2),(1,3)],[(0,1),(1,2),(2,3)],[(0,2),(1,3),(2,3)]]
def A_1 : BT (List (Nat × Nat)) := btOfList 4 al_1
set_option maxHeartbeats 0 in
lemma A_1_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_1 = g_1) A_1 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_1_0 : Slice r_1 g_1 (subcubeFast 0 1) 4 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_1_1 : Slice r_1 g_1 (subcubeFast 0 2) 4 := by
  have hc : Lower (varsOf 13) 0xfaa0faa0faa0faa0 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_1_2 : Slice r_1 g_1 (subcubeFast 0 4) 4 := by
  have hc : Lower (varsOf 11) 0xee88ee88ee88ee88 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_1_3 : Slice r_1 g_1 (subcubeFast 0 8) 4 := by
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) low_0
def S_1 : BT (Option (Nat × Nat)) := btOfList 2 [some (subcubeFast 0 1,4),some (subcubeFast 0 2,4),some (subcubeFast 0 4,4),some (subcubeFast 0 8,4)]
lemma S_1_ok : btAll (fun o => ∀ p, o = some p → Slice r_1 g_1 p.1 p.2) S_1 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_1_0) (forall_cons (fun _ h => by cases h; exact sl_1_1) (forall_cons (fun _ h => by cases h; exact sl_1_2) (forall_cons (fun _ h => by cases h; exact sl_1_3) (fun _ h => (List.not_mem_nil h).elim)))))
def ps_1 : BT (Option PoolSpec) := btOfList 2 [q 1 [],q 0 [],q 2 [],q 3 []]
def B_1_2 : BT (List (List Nat)) := BT.empty
lemma B_1_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_1 2 xs.toFinset) B_1_2 := .empty
def U_1_3 : List Nat := [0,1]
def P_1_3 : BT (Option BoundPool) := buildPoolsSubBT 2 W_1 r_1 S_1 ps_1 U_1_3
def N_1_3 : List NodeSpec := [([4,5,6,3],[0,1],[]),([8,1,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_1_3 : checkNodesBT W_1 g_1 F_1 P_1_3 A_1 B_1_2 3 N_1_3 = true := by decide +kernel
def B_1_3 : BT (List (List Nat)) := buildBucketsBT W_1 N_1_3
set_option maxRecDepth 500000 in
lemma B_1_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_1 3 xs.toFinset) B_1_3 :=
  buildBucketsBT_sound (by decide) gp_1 W_1_ok (buildPoolsSubBT_sound S_1_ok) A_1_ok B_1_2_ok C_1_3
def U_1_4 : List Nat := [0,2,3]
def P_1_4 : BT (Option BoundPool) := buildPoolsSubBT 2 W_1 r_1 S_1 ps_1 U_1_4
def N_1_4 : List NodeSpec := [([4,5,1,2,3],[0,2],[0]),([11,0,1,2,3],[3],[9]),([10,0,1,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_1_4 : checkNodesBT W_1 g_1 F_1 P_1_4 A_1 B_1_3 4 N_1_4 = true := by decide +kernel
def B_1_4 : BT (List (List Nat)) := buildBucketsBT W_1 N_1_4
set_option maxRecDepth 500000 in
lemma B_1_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_1 4 xs.toFinset) B_1_4 :=
  buildBucketsBT_sound (by decide) gp_1 W_1_ok (buildPoolsSubBT_sound S_1_ok) A_1_ok B_1_3_ok C_1_4
def U_1_5 : List Nat := (r 0 4)
def P_1_5 : BT (Option BoundPool) := buildPoolsSubBT 2 W_1 r_1 S_1 ps_1 U_1_5
def N_1_5 : List NodeSpec := [([4,0,1,2,3],(r 0 4),[0,1,4,5,8,10])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_1_5 : checkNodesBT W_1 g_1 F_1 P_1_5 A_1 B_1_4 5 N_1_5 = true := by decide +kernel
def B_1_5 : BT (List (List Nat)) := buildBucketsBT W_1 N_1_5
set_option maxRecDepth 500000 in
lemma B_1_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_1 5 xs.toFinset) B_1_5 :=
  buildBucketsBT_sound (by decide) gp_1 W_1_ok (buildPoolsSubBT_sound S_1_ok) A_1_ok B_1_4_ok C_1_5
def U_1_6 : List Nat := (r 0 4)
def P_1_6 : BT (Option BoundPool) := buildPoolsSubBT 2 W_1 r_1 S_1 ps_1 U_1_6
def N_1_6 : List NodeSpec := [([0,1,2,3],[1,0,2,3],[0,2,3,6,7,8])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_1_6 : checkNodesBT W_1 g_1 F_1 P_1_6 A_1 B_1_5 6 N_1_6 = true := by decide +kernel
def B_1_6 : BT (List (List Nat)) := buildBucketsBT W_1 N_1_6
set_option maxRecDepth 500000 in
lemma B_1_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_1 6 xs.toFinset) B_1_6 :=
  buildBucketsBT_sound (by decide) gp_1 W_1_ok (buildPoolsSubBT_sound S_1_ok) A_1_ok B_1_5_ok C_1_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_1_ok : forestRootCheck r_1 g_1 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_1_in : bucketContainsBT B_1_6 r_1 = true := by decide +kernel
lemma low_1 : Lower r_1 g_1 7 := lower_of_forestBT root_1_ok B_1_6_ok root_1_in
def g_2 := 0xfe80fe80fe80fe80
def r_2 : List Nat := varsOf 15
def p_2 : List Nat := [7,7,7,9,9,10,10,11,12,12,13,14]
def q_2 : List Nat := [6,5,3,8,1,8,2,3,8,4,5,6]
def F_2 : Nat := fullMask 12
set_option maxHeartbeats 0 in
lemma gp_2 : goodPairs g_2 p_2 q_2 := goodPairs_of (by decide +kernel)
def W_2 : BT Decor := buildWiresBT 5 (mkBase p_2 q_2 r_2) [(0,2,3),(1,2,3),(3,4,5),(0,1,2),(1,1,2),(3,7,8),(2,0,3),(3,0,3),(1,1,3),(0,0,12),(0,0,3),(1,0,3),(3,4,0),(1,14,2),(2,0,2),(3,0,2),(3,2,15),(2,2,1),(3,21,0),(2,0,1),(1,23,2),(0,0,1),(1,0,1),(3,2,3)]
lemma W_2_ok : btAll (fun x => faithful p_2 q_2 x ∧ x.1 < 2^64) W_2 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_2 : List (List (Nat × Nat)) := [[],[(1,2)],[(0,1)],[(0,2),(1,2)],[(0,1),(1,2)],[(0,2)]]
def A_2 : BT (List (Nat × Nat)) := btOfList 3 al_2
set_option maxHeartbeats 0 in
lemma A_2_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_2 = g_2) A_2 := btAll_ofList (autos_of (by decide +kernel))
def S_2 : BT (Option (Nat × Nat)) := btOfList 1 []
lemma S_2_ok : btAll (fun o => ∀ p, o = some p → Slice r_2 g_2 p.1 p.2) S_2 := btAll_ofList (fun _ h => (List.not_mem_nil h).elim)
def ps_2 : BT (Option PoolSpec) := btOfList 1 []
def B_2_1 : BT (List (List Nat)) := BT.empty
lemma B_2_1_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_2 1 xs.toFinset) B_2_1 := .empty
def U_2_2 : List Nat := []
def P_2_2 : BT (Option BoundPool) := buildPoolsSubBT 1 W_2 r_2 S_2 ps_2 U_2_2
def N_2_2 : List NodeSpec := [([6,0,1],[],[]),([9,0,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_2_2 : checkNodesBT W_2 g_2 F_2 P_2_2 A_2 B_2_1 2 N_2_2 = true := by decide +kernel
def B_2_2 : BT (List (List Nat)) := buildBucketsBT W_2 N_2_2
set_option maxRecDepth 500000 in
lemma B_2_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_2 2 xs.toFinset) B_2_2 :=
  buildBucketsBT_sound (by decide) gp_2 W_2_ok (buildPoolsSubBT_sound S_2_ok) A_2_ok B_2_1_ok C_2_2
def U_2_3 : List Nat := []
def P_2_3 : BT (Option BoundPool) := buildPoolsSubBT 1 W_2 r_2 S_2 ps_2 U_2_3
def N_2_3 : List NodeSpec := [([10,11,1,2],[],[3]),([13,1,2,3],[],[]),([14,1,2,15],[],[3]),([16,1,2,3],[],[]),([0,1,17,3],[],[]),([18,19,1,3],[],[2]),([20,0,1,3],[],[]),([22,1,2,3],[],[]),([0,1,24,3],[],[]),([25,26,2,3],[],[4])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_2_3 : checkNodesBT W_2 g_2 F_2 P_2_3 A_2 B_2_2 3 N_2_3 = true := by decide +kernel
def B_2_3 : BT (List (List Nat)) := buildBucketsBT W_2 N_2_3
set_option maxRecDepth 500000 in
lemma B_2_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_2 3 xs.toFinset) B_2_3 :=
  buildBucketsBT_sound (by decide) gp_2 W_2_ok (buildPoolsSubBT_sound S_2_ok) A_2_ok B_2_2_ok C_2_3
def U_2_4 : List Nat := []
def P_2_4 : BT (Option BoundPool) := buildPoolsSubBT 1 W_2 r_2 S_2 ps_2 U_2_4
def N_2_4 : List NodeSpec := [([10,0,1,2,3],[],[0]),([14,0,1,2,3],[],[0,1,3,5]),([18,0,1,2,3],[],[0,1,3]),([27,0,1,2,3],[],[4]),([0,1,2,3,15],[],[0,1,2,4]),([0,1,26,2,3],[],[0]),([25,0,1,2,3],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_2_4 : checkNodesBT W_2 g_2 F_2 P_2_4 A_2 B_2_3 4 N_2_4 = true := by decide +kernel
def B_2_4 : BT (List (List Nat)) := buildBucketsBT W_2 N_2_4
set_option maxRecDepth 500000 in
lemma B_2_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_2 4 xs.toFinset) B_2_4 :=
  buildBucketsBT_sound (by decide) gp_2 W_2_ok (buildPoolsSubBT_sound S_2_ok) A_2_ok B_2_3_ok C_2_4
def U_2_5 : List Nat := []
def P_2_5 : BT (Option BoundPool) := buildPoolsSubBT 1 W_2 r_2 S_2 ps_2 U_2_5
def N_2_5 : List NodeSpec := [([0,1,2,3],[],[0,1,2,3,4,5])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_2_5 : checkNodesBT W_2 g_2 F_2 P_2_5 A_2 B_2_4 5 N_2_5 = true := by decide +kernel
def B_2_5 : BT (List (List Nat)) := buildBucketsBT W_2 N_2_5
set_option maxRecDepth 500000 in
lemma B_2_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_2 5 xs.toFinset) B_2_5 :=
  buildBucketsBT_sound (by decide) gp_2 W_2_ok (buildPoolsSubBT_sound S_2_ok) A_2_ok B_2_4_ok C_2_5
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_2_ok : forestRootCheck r_2 g_2 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,1,9)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_2_in : bucketContainsBT B_2_5 r_2 = true := by decide +kernel
lemma low_2 : Lower r_2 g_2 6 := lower_of_forestBT root_2_ok B_2_5_ok root_2_in
def g_3 := 0xffe8ffe8ffe8ffe8
def r_3 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_3 : Lower r_3 g_3 5 := by
  exact lift_of_f (z := 8) (o := 0) (other := r_0) (G := g_0) (essPairs := [(VAR 3,0,8)]) (by decide +kernel) low_0
def g_4 := 0xfffee880fffee880
def r_4 : List Nat := varsOf 31
def p_4 : List Nat := [7,7,7,11,11,11,13,13,13,14,14,14,17,17,18,18,19,20,20,21,22,24,24,25,26,28]
def q_4 : List Nat := [6,5,3,10,9,3,12,9,5,12,10,6,16,1,16,2,3,16,4,5,6,16,8,9,10,12]
def F_4 : Nat := fullMask 26
set_option maxHeartbeats 0 in
lemma gp_4 : goodPairs g_4 p_4 q_4 := goodPairs_of (by decide +kernel)
def W_4 : BT Decor := buildWiresBT 3 (mkBase p_4 q_4 r_4) [(1,0,1),(1,2,3),(0,5,6)]
lemma W_4_ok : btAll (fun x => faithful p_4 q_4 x ∧ x.1 < 2^64) W_4 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_4 : List (List (Nat × Nat)) := [[],[(1,2)],[(1,2),(2,3)],[(0,2),(1,2)],[(0,2),(1,2),(2,3)],[(0,2),(1,3)]]
def A_4 : BT (List (Nat × Nat)) := btOfList 3 al_4
set_option maxHeartbeats 0 in
lemma A_4_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_4 = g_4) A_4 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_4_0 : Slice r_4 g_4 (subcubeFast 16 0) 7 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_1
set_option maxHeartbeats 0 in
lemma sl_4_1 : Slice r_4 g_4 (subcubeFast 2 0) 6 := by
  have hc : Lower (varsOf 29) 0xfffaa000fffaa000 6 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_4_2 : Slice r_4 g_4 (subcubeFast 4 0) 6 := by
  have hc : Lower (varsOf 27) 0xffee8800ffee8800 6 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_4_3 : Slice r_4 g_4 (subcubeFast 8 0) 6 := by
  have hc : Lower (varsOf 23) 0xfefe8080fefe8080 6 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_4_4 : Slice r_4 g_4 (subcubeFast 1 0) 6 := by
  have hc : Lower (varsOf 30) 0xfffcc000fffcc000 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_4_5 : Slice r_4 g_4 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) 0xfffffcc0fffffcc0 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_4_6 : Slice r_4 g_4 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) 0xfffffaa0fffffaa0 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_4_7 : Slice r_4 g_4 (subcubeFast 0 4) 5 := by
  have hc : Lower (varsOf 27) 0xffffee88ffffee88 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_4_8 : Slice r_4 g_4 (subcubeFast 0 8) 5 := by
  have hc : Lower (varsOf 23) 0xffffe8e8ffffe8e8 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_4_9 : Slice r_4 g_4 (subcubeFast 16 2) 4 := by
  have hc : Lower (varsOf 13) 0xfaa0faa0faa0faa0 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 2) (by decide +kernel) hc
def S_4 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 16 0,7),some (subcubeFast 2 0,6),some (subcubeFast 4 0,6),some (subcubeFast 8 0,6),some (subcubeFast 1 0,6),some (subcubeFast 0 1,5),some (subcubeFast 0 2,5),some (subcubeFast 0 4,5),some (subcubeFast 0 8,5),some (subcubeFast 16 2,4)]
lemma S_4_ok : btAll (fun o => ∀ p, o = some p → Slice r_4 g_4 p.1 p.2) S_4 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_4_0) (forall_cons (fun _ h => by cases h; exact sl_4_1) (forall_cons (fun _ h => by cases h; exact sl_4_2) (forall_cons (fun _ h => by cases h; exact sl_4_3) (forall_cons (fun _ h => by cases h; exact sl_4_4) (forall_cons (fun _ h => by cases h; exact sl_4_5) (forall_cons (fun _ h => by cases h; exact sl_4_6) (forall_cons (fun _ h => by cases h; exact sl_4_7) (forall_cons (fun _ h => by cases h; exact sl_4_8) (forall_cons (fun _ h => by cases h; exact sl_4_9) (fun _ h => (List.not_mem_nil h).elim)))))))))))
def ps_4 : BT (Option PoolSpec) := btOfList 4 [q 1 [12297],q 4 [],q 5 [],q 6 [],q 7 [],q 3 [],q 8 [],q 2 [4097],q 9 [],q 3 [4097],q 1 [],q 2 [],q 0 []]
def B_4_4 : BT (List (List Nat)) := BT.empty
lemma B_4_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_4 4 xs.toFinset) B_4_4 := .empty
def U_4_5 : List Nat := []
def P_4_5 : BT (Option BoundPool) := buildPoolsSubBT 4 W_4 r_4 S_4 ps_4 U_4_5
def N_4_5 : List NodeSpec := [e5 [7] []]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_4_5 : checkNodesBT W_4 g_4 F_4 P_4_5 A_4 B_4_4 5 N_4_5 = true := by decide +kernel
def B_4_5 : BT (List (List Nat)) := buildBucketsBT W_4 N_4_5
set_option maxRecDepth 500000 in
lemma B_4_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_4 5 xs.toFinset) B_4_5 :=
  buildBucketsBT_sound (by decide) gp_4 W_4_ok (buildPoolsSubBT_sound S_4_ok) A_4_ok B_4_4_ok C_4_5
def U_4_6 : List Nat := (r 0 8)
def P_4_6 : BT (Option BoundPool) := buildPoolsSubBT 4 W_4 r_4 S_4 ps_4 U_4_6
def N_4_6 : List NodeSpec := [u5 [5,6] (r 0 8)]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_4_6 : checkNodesBT W_4 g_4 F_4 P_4_6 A_4 B_4_5 6 N_4_6 = true := by decide +kernel
def B_4_6 : BT (List (List Nat)) := buildBucketsBT W_4 N_4_6
set_option maxRecDepth 500000 in
lemma B_4_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_4 6 xs.toFinset) B_4_6 :=
  buildBucketsBT_sound (by decide) gp_4 W_4_ok (buildPoolsSubBT_sound S_4_ok) A_4_ok B_4_5_ok C_4_6
def U_4_7 : List Nat := ([1,4]++r 6 4)
def P_4_7 : BT (Option BoundPool) := buildPoolsSubBT 4 W_4 r_4 S_4 ps_4 U_4_7
def N_4_7 : List NodeSpec := [u5 [5] [1,4,6,8,7,9]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_4_7 : checkNodesBT W_4 g_4 F_4 P_4_7 A_4 B_4_6 7 N_4_7 = true := by decide +kernel
def B_4_7 : BT (List (List Nat)) := buildBucketsBT W_4 N_4_7
set_option maxRecDepth 500000 in
lemma B_4_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_4 7 xs.toFinset) B_4_7 :=
  buildBucketsBT_sound (by decide) gp_4 W_4_ok (buildPoolsSubBT_sound S_4_ok) A_4_ok B_4_6_ok C_4_7
def U_4_8 : List Nat := [1,5,10,11,12]
def P_4_8 : BT (Option BoundPool) := buildPoolsSubBT 4 W_4 r_4 S_4 ps_4 U_4_8
def N_4_8 : List NodeSpec := [a5 [] [10,1,11,5,12] [0,1,2,3,4,5]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_4_8 : checkNodesBT W_4 g_4 F_4 P_4_8 A_4 B_4_7 8 N_4_8 = true := by decide +kernel
def B_4_8 : BT (List (List Nat)) := buildBucketsBT W_4 N_4_8
set_option maxRecDepth 500000 in
lemma B_4_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_4 8 xs.toFinset) B_4_8 :=
  buildBucketsBT_sound (by decide) gp_4 W_4_ok (buildPoolsSubBT_sound S_4_ok) A_4_ok B_4_7_ok C_4_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_4_ok : forestRootCheck r_4 g_4 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11),(VAR 4,1,17)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_4_in : bucketContainsBT B_4_8 r_4 = true := by decide +kernel
lemma low_4 : Lower r_4 g_4 9 := lower_of_forestBT root_4_ok B_4_8_ok root_4_in
def g_5 := 0xe800e800e800e800
def r_5 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_5 : Lower r_5 g_5 5 := by
  exact lift_of_f (z := 0) (o := 8) (other := r_0) (G := g_0) (essPairs := [(VAR 3,3,11)]) (by decide +kernel) low_0
def g_6 := 0xf880f880f880f880
def r_6 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_6 : Lower r_6 g_6 5 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,6,7)]) (by decide +kernel) hc
def g_7 := 0xffe88000ffe88000
def r_7 : List Nat := varsOf 31
def p_7 : List Nat := [15,15,15,15,19,19,19,21,21,21,22,22,22,23,24,24,25,25,26,26,27,28,28,29,30]
def q_7 : List Nat := [14,13,11,7,18,17,3,20,17,5,20,18,6,7,16,8,17,9,18,10,11,20,12,13,14]
def F_7 : Nat := fullMask 25
set_option maxHeartbeats 0 in
lemma gp_7 : goodPairs g_7 p_7 q_7 := goodPairs_of (by decide +kernel)
def W_7 : BT Decor := buildWiresBT 8 (mkBase p_7 q_7 r_7) [(0,0,1),(0,0,2),(0,1,2),(0,7,4),(1,8,3),(1,3,4),(0,0,10),(1,7,3),(0,12,4),(0,6,4),(3,14,0),(2,0,3),(3,16,2),(2,3,4),(3,18,7),(3,19,0),(0,3,4),(3,21,10),(1,5,3),(0,23,4),(2,0,13),(3,14,4),(1,14,3),(1,5,21),(2,5,3),(0,5,2),(3,30,0),(2,0,4),(3,32,1),(3,31,4),(0,2,3),(3,35,0),(3,5,2),(3,18,23),(0,30,4),(3,39,0),(0,5,4),(2,7,3),(3,42,0),(1,41,2),(1,41,3),(3,3,4),(1,7,4),(3,8,47),(3,30,1),(3,7,3),(0,0,4),(1,7,51),(3,8,4),(1,14,1),(3,14,2),(0,7,3),(3,56,12),(3,8,3),(1,8,0),(2,1,3),(1,60,51),(1,60,6),(0,2,10),(3,63,0),(1,5,4),(3,3,65),(3,18,2),(3,67,0),(0,3,65),(2,5,4),(3,41,4),(0,1,4),(3,50,0),(0,5,3),(2,0,21),(3,75,1),(0,2,65),(0,0,3),(1,53,3),(3,42,4),(1,16,21),(1,31,3),(0,31,4),(3,29,0),(3,70,0),(3,6,3),(3,30,4),(2,5,35),(3,60,2),(3,89,0),(1,18,5),(1,72,3),(0,0,92),(1,30,3),(2,2,3),(0,95,4),(3,96,0),(3,18,0),(3,60,4),(2,0,99),(3,95,0),(3,72,2),(3,102,0),(0,2,4),(3,16,1),(3,53,0),(3,37,4),(2,2,4),(1,108,5),(3,7,10),(0,16,4),(3,5,3),(3,17,4),(0,5,10),(1,7,78),(1,95,5),(2,2,21),(3,117,0),(2,5,21),(2,5,104),(3,95,5),(3,108,5),(3,108,0),(0,101,4),(1,15,3),(3,29,2),(3,18,5),(0,1,3),(3,128,2),(3,129,0),(2,1,4),(3,131,2),(3,132,0),(3,16,4),(3,12,4),(0,0,12),(1,51,3),(3,95,4)]
lemma W_7_ok : btAll (fun x => faithful p_7 q_7 x ∧ x.1 < 2^64) W_7 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_7 : List (List (Nat × Nat)) := [[],[(1,2)],[(0,1)],[(0,2),(1,2)],[(0,1),(1,2)],[(0,2)]]
def A_7 : BT (List (Nat × Nat)) := btOfList 3 al_7
set_option maxHeartbeats 0 in
lemma A_7_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_7 = g_7) A_7 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_7_0 : Slice r_7 g_7 (subcubeFast 0 1) 6 := by
  have hc : Lower (varsOf 30) 0xfffcc000fffcc000 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_1 : Slice r_7 g_7 (subcubeFast 0 2) 6 := by
  have hc : Lower (varsOf 29) 0xfffaa000fffaa000 6 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_2 : Slice r_7 g_7 (subcubeFast 0 4) 6 := by
  have hc : Lower (varsOf 27) 0xffee8800ffee8800 6 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_3 : Slice r_7 g_7 (subcubeFast 8 0) 5 := by
  have hc : Lower (varsOf 23) 0xe8e80000e8e80000 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_4 : Slice r_7 g_7 (subcubeFast 0 16) 5 := by
  exact slice_fast_direct_f (z := 0) (o := 16) (by decide +kernel) low_3
set_option maxHeartbeats 0 in
lemma sl_7_5 : Slice r_7 g_7 (subcubeFast 8 16) 4 := by
  exact slice_fast_direct_f (z := 8) (o := 16) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_7_6 : Slice r_7 g_7 (identDom 0 3) 5 := by
  have hc : Lower (varsOf 23) 0xeaea8080eaea8080 5 := carry_of (swaps := [(0,2),(1,2),(3,4)]) (by decide +kernel) low_6
  exact slice_ident (u := 0) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_7 : Slice r_7 g_7 (identDom 1 3) 5 := by
  have hc : Lower (varsOf 23) 0xecec8080ecec8080 5 := carry_of (swaps := [(1,2),(3,4)]) (by decide +kernel) low_6
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_8 : Slice r_7 g_7 (identDom 2 3) 5 := by
  have hc : Lower (varsOf 23) 0xf8f88080f8f88080 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_6
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
def S_7 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 0 1,6),some (subcubeFast 0 2,6),some (subcubeFast 0 4,6),some (subcubeFast 8 0,5),some (subcubeFast 0 16,5),some (subcubeFast 8 16,4),some (identDom 0 3,5),some (identDom 1 3,5),some (identDom 2 3,5)]
lemma S_7_ok : btAll (fun o => ∀ p, o = some p → Slice r_7 g_7 p.1 p.2) S_7 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_7_0) (forall_cons (fun _ h => by cases h; exact sl_7_1) (forall_cons (fun _ h => by cases h; exact sl_7_2) (forall_cons (fun _ h => by cases h; exact sl_7_3) (forall_cons (fun _ h => by cases h; exact sl_7_4) (forall_cons (fun _ h => by cases h; exact sl_7_5) (forall_cons (fun _ h => by cases h; exact sl_7_6) (forall_cons (fun _ h => by cases h; exact sl_7_7) (forall_cons (fun _ h => by cases h; exact sl_7_8) (fun _ h => (List.not_mem_nil h).elim))))))))))
def ps_7 : BT (Option PoolSpec) := btOfList 7 [q 0 [16396,16397,41047],q 2 [],q 1 [16412,16413,192547],q 1 [],q 1 [12316,12317,49379],q 0 [],q 0 [16397,40968],q 5 [],q 1 [16396,16397,41047],q 2 [16396,16397,41047],q 0 [16405,266255],q 0 [16405,266252],q 0 [16406,16407],q 7 [],q 0 [16404,12453],q 1 [16404,12453],q 0 [16404,16405],q 1 [8480,35],q 0 [16398,16399],q 1 [12319,203],q 4 [],q 0 [12308,12309],q 1 [16396,86018],q 3 [],q 6 [],q 0 [16405,266248],q 0 [16396,86037],q 0 [12294,8435],q 0 [16388,8483],q 1 [16397,40991],q 0 [12310,12311],q 1 [16412,12323],q 0 [16388,12577],q 1 [16392,419],q 1 [16397,40960],q 0 [12298,20861],q 0 [16396,86026],q 0 [16392,426006],q 0 [12298,20863],q 0 [16396,86038],q 1 [16412,35],q 0 [12310,8311],q 0 [16396,16397],q 1 [16384,208925],q 0 [16397,40980],q 1 [16384,12453],q 0 [4300,12453],q 1 [16398,16399],q 2 [16398,16399],q 2 [16396,86018],q 0 [16398],q 0 [16392],q 2 [419],q 2 [16384],q 1 [16384],q 0 [4300],q 0 [16399],q 2 [16767],q 8 [],q 2 [4096],q 0 [16404],q 0 [16396],q 1 [16404],q 0 [16397],q 1 [16396,16397],q 2 [16396,16397],q 0 [16448],q 0 [12309],q 0 [16405],q 1 [8192],q 0 [8196],q 1 [16386],q 1 [16415],q 0 [12308],q 1 [31],q 2 [31],q 1 [12319],q 0 [12298],q 1 [12298,383],q 2 [383],q 1 [12309],q 0 [12296],q 0 [8212],q 1 [8212],q 2 [435],q 0 [16394],q 0 [16406],q 2 [16415],q 0 [12310],q 1 [12290],q 0 [12493],q 1 [16384,12493],q 2 [16384,12493],q 2 [16397,40960],q 1 [12310],q 2 [143],q 1 [16399],q 2 [16399],q 1 [16398],q 2 [16398],q 1 [16397],q 2 [16397],q 1 [16396],q 2 [16396],q 2 [16386],q 2 [12290],q 1 [12288],q 2 [12288]]
def B_7_2 : BT (List (List Nat)) := BT.empty
lemma B_7_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_7 2 xs.toFinset) B_7_2 := .empty
def U_7_3 : List Nat := []
def P_7_3 : BT (Option BoundPool) := buildPoolsSubBT 7 W_7 r_7 S_7 ps_7 U_7_3
def N_7_3 : List NodeSpec := [([5,6,9,4],[],[]),([11,1,2,13],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_7_3 : checkNodesBT W_7 g_7 F_7 P_7_3 A_7 B_7_2 3 N_7_3 = true := by decide +kernel
def B_7_3 : BT (List (List Nat)) := buildBucketsBT W_7 N_7_3
set_option maxRecDepth 500000 in
lemma B_7_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_7 3 xs.toFinset) B_7_3 :=
  buildBucketsBT_sound (by decide) gp_7 W_7_ok (buildPoolsSubBT_sound S_7_ok) A_7_ok B_7_2_ok C_7_3
def U_7_4 : List Nat := (r 0 6)
def P_7_4 : BT (Option BoundPool) := buildPoolsSubBT 7 W_7 r_7 S_7 ps_7 U_7_4
def N_7_4 : List NodeSpec := [([22,5,0,1,2],[0],[]),([41,6,7,3,4],[1],[4]),([29,6,7,3,4],[1],[]),([48,0,1,2,3],[2],[]),([5,52,2,3,4],[3],[]),([57,0,1,2,4],[4],[]),([5,62,2,3,4],[5],[]),([40,58,1,2,4],[],[]),([40,1,2,9,4],[],[]),([5,61,2,3,4],[],[]),([58,1,59,2,4],[],[]),([5,0,2,9,4],[],[0]),([15,55,1,3,4],[],[]),([11,1,2,12,4],[],[0]),([15,54,2,3,4],[],[]),([53,5,6,3,4],[],[]),([50,43,1,2,4],[],[]),([31,49,2,3,4],[],[]),([0,1,44,45,4],[],[]),([5,6,3,12,4],[],[]),([46,43,1,2,4],[],[]),([15,1,17,3,4],[],[]),([43,1,2,21,4],[],[]),([40,1,2,3,4],[],[]),([0,1,2,38,4],[],[]),([36,37,1,3,4],[],[]),([32,1,34,2,3],[],[]),([31,33,2,3,4],[],[]),([16,5,2,12,4],[],[]),([16,1,2,28,4],[],[]),([15,1,2,27,4],[],[]),([15,26,1,2,3],[],[]),([25,1,2,3,4],[],[]),([0,1,2,24,10],[],[4]),([20,1,2,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_7_4 : checkNodesBT W_7 g_7 F_7 P_7_4 A_7 B_7_3 4 N_7_4 = true := by decide +kernel
def B_7_4 : BT (List (List Nat)) := buildBucketsBT W_7 N_7_4
set_option maxRecDepth 500000 in
lemma B_7_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_7 4 xs.toFinset) B_7_4 :=
  buildBucketsBT_sound (by decide) gp_7 W_7_ok (buildPoolsSubBT_sound S_7_ok) A_7_ok B_7_3_ok C_7_4
def U_7_5_0 : List Nat := ([0,1,3]++r 5 42)
def P_7_5_0 : BT (Option BoundPool) := buildPoolsSubBT 7 W_7 r_7 S_7 ps_7 U_7_5_0
def N_7_5_0 : List NodeSpec := [([41,6,1,2,3,4],[1],[0,4]),([29,6,1,2,3,4],[1],[0]),([53,0,72,1,2,3],[3],[4]),([75,5,1,2,3,4],[3],[]),([5,123,1,2,3,4],[3],[4]),([16,5,105,2,3,4],[3],[]),([111,5,1,2,3,4],[3],[]),([5,6,7,3,4],[3,1,5],[0,1,2,3,4]),([78,0,1,2,12,4],[5],[]),([16,0,1,2,12,4],[5],[0,1]),([31,30,1,2,3,4],[5],[0,1]),([15,6,1,104,3,4],[5],[]),([31,5,1,2,3,4],[5],[1]),([15,6,1,2,3,4],[5],[0]),([15,14,1,2,3,4],[5],[0]),([5,0,2,3,12,4],[5],[0]),([40,8,1,2,3,4],[5],[0]),([5,0,2,3,99,4],[5],[]),([53,5,0,2,3,4],[5],[0]),([53,0,8,1,2,3],[5],[2,4]),([15,51,1,2,3,4],[5],[0]),([31,5,7,2,3,4],[5,3],[]),e5 [64] [6],([64,0,1,63,3,4],[6],[]),([16,5,72,2,3,4],[7],[2]),([16,46,5,1,2,4],[7],[]),([16,46,0,1,2,134],[7],[]),([5,0,1,63,3,4],[7,6],[4]),([22,0,1,2],[7,0,8,9],[0,1,3]),([66,5,0,1,2,4],[10],[]),([5,0,1,2,69,4],[11],[]),([70,71,0,1,2,3],[12],[4]),([58,0,8,1,2,4],[13],[0]),([5,0,1,2,45,4],[14],[]),([0,1,2,45,4],[14,15],[4,5]),([41,0,1,2,3,65],[16],[4]),([40,72,1,2,3,4],[17],[]),([18,46,5,0,1,2],[18],[0]),([73,7,1,2,3,4],[19],[]),([5,51,72,2,3,4],[3,20],[]),([5,85,1,2,3,4],[5,20],[]),([101,51,1,2,3,4],[20],[5]),([53,0,7,72,2,3],[20],[]),([29,46,0,1,2,4],[20],[4]),([30,51,1,2,3,4],[20],[]),([74,0,1,2,23,4],[21],[4]),([75,76,1,2,3,4],[22],[]),([75,7,1,2,3,4],[22],[]),([119,75,1,2,3,4],[22],[]),a5 [127] [1,23] [4],([5,98,1,2,3,4],[3,23],[]),([36,5,1,2,3,4],[3,23],[0]),([16,60,5,2,3,4],[5,23],[]),([36,6,1,2,3,4],[5,23],[]),([16,30,1,2,3,4],[23],[]),([41,0,1,2,45,4],[23],[0,1,3,4]),e5 [124] [23],([16,5,1,2,23,4],[23],[]),([16,15,1,2,3,4],[23],[0]),([16,0,1,2,81,4],[23],[]),a5 [41] [1,24,23] [4],a5 [24] [3,1,24] [0,4],([5,11,1,2,3,4],[3,24,7],[]),([5,84,1,2,3,4],[5,24],[]),([51,0,1,2,3,134],[7,24],[]),e5 [93] [24],e5 [82] [24],([31,78,1,2,3,4],[24],[3,5]),e5 [88] [24,1],e5 [79] [24,5,3,1],([0,1,2,23,4,10],[24,13],[0,4]),a5 [39] [24,23] [0,2,4],a5 [122] [24,23] [4],([5,0,1,77,3,4],[25],[]),a5 [28] [26,23] [0,2],e5 [90] [27],([5,0,89,2,3,4],[27],[]),e5 [103] [28],e5 [110] [29],([29,112,0,1,2,4],[30],[4]),([58,0,7,1,2,4],[31],[]),([5,0,2,3,92,4],[7,32],[]),([15,0,7,1,3,4],[33],[]),([114,11,1,2,3,4],[24,7,34],[]),a5 [116] [3,23,35] [1,3],e5 [118] [36],e5 [120] [37],e5 [121] [1,38],e5 [119] [39],([40,7,1,2,3,4],[40],[]),([5,0,1,126,3,4],[24,41],[4]),([5,0,1,2,21,10],[42],[0]),a5 [52] [20,1,43] [0,1],e5 [114] [24,44],([51,0,1,2,45,4],[45,46],[3]),e5 [87] [],e5 [125] [],e5 [83] [],([16,86,6,1,2,4],[],[]),e5 [80] [],e5 [130] [],([46,101,0,1,2,4],[],[]),e5 [133] [],e5 [68] [],u5 [61] [],e5 [135] [],([32,31,1,2,3,4],[],[0,1]),([5,51,1,2,3,65],[],[]),e5 [136] [],([43,1,2,3,4],[],[0]),e5 [109] [],([18,0,1,2,23,4],[],[0]),e5 [45] [],([40,1,2,3,4],[],[]),e5 [40] [],e5 [43] [],([41,0,1,44,3,4],[],[0,1,3,4]),e5 [106] [],([16,5,7,2,3,4],[],[0,1,2]),([16,49,1,2,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_7_5_0 : checkNodesBT W_7 g_7 F_7 P_7_5_0 A_7 B_7_4 5 N_7_5_0 = true := by decide +kernel
def U_7_5_1 : List Nat := []
def P_7_5_1 : BT (Option BoundPool) := buildPoolsSubBT 7 W_7 r_7 S_7 ps_7 U_7_5_1
def N_7_5_1 : List NodeSpec := [([5,6,72,2,3,4],[],[2,3]),a5 [107] [] [4],e5 [53] [],([31,0,72,2,3,4],[],[]),e5 [100] [],e5 [97] [],([101,0,1,2,21,4],[],[]),([16,5,1,2,21,4],[],[0]),e5 [113] [],e5 [115] [],([29,0,1,2,21,4],[],[0,4]),e5 [23] [],e5 [94] [],e5 [91] []]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_7_5_1 : checkNodesBT W_7 g_7 F_7 P_7_5_1 A_7 B_7_4 5 N_7_5_1 = true := by decide +kernel
def N_7_5 := N_7_5_0 ++ N_7_5_1
def B_7_5 : BT (List (List Nat)) := buildBucketsBT W_7 N_7_5
set_option maxRecDepth 500000 in
lemma B_7_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_7 5 xs.toFinset) B_7_5 := by
  have hm0 := checkNodesBT_mem (by decide) gp_7 W_7_ok (buildPoolsSubBT_sound S_7_ok) A_7_ok B_7_4_ok C_7_5_0
  have hm1 := checkNodesBT_mem (by decide) gp_7 W_7_ok (buildPoolsSubBT_sound S_7_ok) A_7_ok B_7_4_ok C_7_5_1
  exact buildBucketsBT_of_mem (forall_append (hm0) hm1)
def U_7_6 : List Nat := ([1,3,5,7,13,18,20,22,23,24,33,34,42]++r 47 49)
def P_7_6 : BT (Option BoundPool) := buildPoolsSubBT 7 W_7 r_7 S_7 ps_7 U_7_6
def N_7_6 : List NodeSpec := [u5 [16,105] [3,24,23,5],u5 [111,51] [7,24],e5 [51,137] [7,24],u5 [16,134] [7,24,5],a5 [16,72] [24,3,5,7] [0,1,2,3],u5 [16,60] [24,5,3,13,23],([18,46,0,1,2],[7,18,47,48],[0,1,3]),([75,1,2,3,4],[22,49,7],[0,1]),a5 [98] [23,3,1,20,50] [0,1,3,5],a5 [18,5] [23,3,50] [0,2],u5 [15,104] [20,51,52],a5 [15] [51,23,24,33,52] [0,3],([5,51,1,2,3,4],[5,7,54],[0,1,2,3,4,5]),a5 [51,72] [54,5,20] [0,1,3],a5 [41,51] [53,7,54,55] [0,1,3,4],([16,46,0,1,2,4],[7,56],[0,1,3,5]),a5 [46,5] [24,7,3,56] [0,2,4],a5 [138] [57,5,3,7,58] [0,1,2,3],a5 [5,104] [51,3,59] [0,1,3,4],a5 [41,5] [20,59,60] [0,1,3,4],a5 [75] [7,61,22,49] [0,1,3,5],a5 [5,21] [23,61,3,59] [0,2,4],([16,0,1,2,21,4],[61,7],[0,1,3,5]),a5 [41] [60,62,1,23,24] [0,1,2,3,4],a5 [5,10] [7,63,3,59] [0,2,4],([0,1,2,21,10],[42,64,65,23,20],[0,1,3]),a5 [111] [7,24,3,1,66] [0,1,3,5],a5 [5,23] [24,23,67,3] [0,2],a5 [5,65] [20,68,3,59] [0,2,4],([5,6,1,2,3,4],[5,59,69],[0,1,2,4]),a5 [32,7] [20,1,70,71] [0,3,5],a5 [53,7] [20,1,72] [0,1,3],a5 [74,5] [24,23,73] [0,1,3],a5 [31,7] [1,70,74] [0,1],a5 [31] [70,23,24,20,74,75] [0,1,2,3,4],a5 [50,7] [70,1,23,76] [0,2,3,4],a5 [101] [24,20,77,78,79] [0,3,5],a5 [23] [67,80,1,58,24,20] [0,4,5],a5 [5,35] [23,81,3,59] [0,2,4],a5 [30,5] [59,82] [0,2,4],a5 [30] [82,83,59,23,24,20] [0,2,4],a5 [123] [3,84,7,85] [0,3],a5 [70,5] [20,86] [0,2],a5 [53] [5,23,72,87] [0,1,3],a5 [29,5] [23,59,24,88] [0,2],a5 [16,7] [24,1,70,23,89] [0,1,2,3,4],([16,5,1,2,3,4],[89,5,7],[0,1,2]),a5 [137] [90,7,91,13,92,58,24] [2,4],a5 [11] [7,63,34,93] [0,1,3,5],([11,1,2,3,4],[34,93,7],[0,1,3,5]),a5 [29] [24,88,94,1,20] [0,2,4],a5 [36] [3,81,7,95] [0,3]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_7_6 : checkNodesBT W_7 g_7 F_7 P_7_6 A_7 B_7_5 6 N_7_6 = true := by decide +kernel
def B_7_6 : BT (List (List Nat)) := buildBucketsBT W_7 N_7_6
set_option maxRecDepth 500000 in
lemma B_7_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_7 6 xs.toFinset) B_7_6 :=
  buildBucketsBT_sound (by decide) gp_7 W_7_ok (buildPoolsSubBT_sound S_7_ok) A_7_ok B_7_5_ok C_7_6
def U_7_7 : List Nat := ([1,3,5,7,20,23,24,50,53,54,56,59,61,63,71,89]++r 96 12)
def P_7_7 : BT (Option BoundPool) := buildPoolsSubBT 7 W_7 r_7 S_7 ps_7 U_7_7
def N_7_7 : List NodeSpec := [a5 [51] [54,53,7,5] [0,1,2,3,4,5],a5 [5] [3,5,59,23,20] [0,2,4],a5 [46] [7,56,96,97] [0,1,2,3,4],a5 [18] [23,20,50,98,99] [0,1,2,3,4],a5 [10] [63,100,101,7,5,3,1] [0,1,2,3,4],a5 [21] [61,102,103,5,7,3,1] [0,1,2,3,4],a5 [32] [5,7,71,104] [0,3,5],a5 [16] [24,89,105,5,7] [0,1,3,5],a5 [78] [5,7,106,107] [3,5]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_7_7 : checkNodesBT W_7 g_7 F_7 P_7_7 A_7 B_7_6 7 N_7_7 = true := by decide +kernel
def B_7_7 : BT (List (List Nat)) := buildBucketsBT W_7 N_7_7
set_option maxRecDepth 500000 in
lemma B_7_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_7 7 xs.toFinset) B_7_7 :=
  buildBucketsBT_sound (by decide) gp_7 W_7_ok (buildPoolsSubBT_sound S_7_ok) A_7_ok B_7_6_ok C_7_7
def U_7_8 : List Nat := [1,3,5]
def P_7_8 : BT (Option BoundPool) := buildPoolsSubBT 7 W_7 r_7 S_7 ps_7 U_7_8
def N_7_8 : List NodeSpec := [a5 [] [5,3,1] [0,1,2,3,4]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_7_8 : checkNodesBT W_7 g_7 F_7 P_7_8 A_7 B_7_7 8 N_7_8 = true := by decide +kernel
def B_7_8 : BT (List (List Nat)) := buildBucketsBT W_7 N_7_8
set_option maxRecDepth 500000 in
lemma B_7_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_7 8 xs.toFinset) B_7_8 :=
  buildBucketsBT_sound (by decide) gp_7 W_7_ok (buildPoolsSubBT_sound S_7_ok) A_7_ok B_7_7_ok C_7_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_7_ok : forestRootCheck r_7 g_7 [(VAR 0,14,15),(VAR 1,13,15),(VAR 2,11,15),(VAR 3,7,15),(VAR 4,3,19)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_7_in : bucketContainsBT B_7_8 r_7 = true := by decide +kernel
lemma low_7 : Lower r_7 g_7 9 := lower_of_forestBT root_7_ok B_7_8_ok root_7_in
def g_8 := 0xfc80fc80fc80fc80
def r_8 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_8 : Lower r_8 g_8 5 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,6,7)]) (by decide +kernel) hc
def g_9 := 0xfac0fac0fac0fac0
def r_9 : List Nat := varsOf 15
def p_9 : List Nat := [6,6,7,7,9,9,11,11,12,12,13,14]
def q_9 : List Nat := [4,2,5,3,8,1,10,3,8,4,5,10]
def F_9 : Nat := fullMask 12
set_option maxHeartbeats 0 in
lemma gp_9 : goodPairs g_9 p_9 q_9 := goodPairs_of (by decide +kernel)
def W_9 : BT Decor := buildWiresBT 2 (mkBase p_9 q_9 r_9) []
lemma W_9_ok : btAll (fun x => faithful p_9 q_9 x ∧ x.1 < 2^64) W_9 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_9 : List (List (Nat × Nat)) := [[]]
def A_9 : BT (List (Nat × Nat)) := btOfList 1 al_9
set_option maxHeartbeats 0 in
lemma A_9_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_9 = g_9) A_9 := btAll_ofList (autos_of (by decide +kernel))
def S_9 : BT (Option (Nat × Nat)) := btOfList 1 []
lemma S_9_ok : btAll (fun o => ∀ p, o = some p → Slice r_9 g_9 p.1 p.2) S_9 := btAll_ofList (fun _ h => (List.not_mem_nil h).elim)
def ps_9 : BT (Option PoolSpec) := btOfList 1 []
def B_9_2 : BT (List (List Nat)) := BT.empty
lemma B_9_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_9 2 xs.toFinset) B_9_2 := .empty
def U_9_3 : List Nat := []
def P_9_3 : BT (Option BoundPool) := buildPoolsSubBT 1 W_9 r_9 S_9 ps_9 U_9_3
def N_9_3 : List NodeSpec := [([0,1,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_9_3 : checkNodesBT W_9 g_9 F_9 P_9_3 A_9 B_9_2 3 N_9_3 = true := by decide +kernel
def B_9_3 : BT (List (List Nat)) := buildBucketsBT W_9 N_9_3
set_option maxRecDepth 500000 in
lemma B_9_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_9 3 xs.toFinset) B_9_3 :=
  buildBucketsBT_sound (by decide) gp_9 W_9_ok (buildPoolsSubBT_sound S_9_ok) A_9_ok B_9_2_ok C_9_3
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_9_ok : forestRootCheck r_9 g_9 [(VAR 0,8,9),(VAR 1,4,6),(VAR 2,2,6),(VAR 3,1,9)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_9_in : bucketContainsBT B_9_3 r_9 = true := by decide +kernel
lemma low_9 : Lower r_9 g_9 4 := lower_of_forestBT root_9_ok B_9_3_ok root_9_in
def g_10 := 0xfea8c000fea8c000
def r_10 : List Nat := varsOf 31
def p_10 : List Nat := [14,14,14,15,15,15,19,19,19,21,21,21,23,23,25,25,25,26,26,26,27,28,28,28,29,30]
def q_10 : List Nat := [12,10,6,13,11,7,18,17,3,20,17,5,22,7,24,17,9,24,18,10,11,24,20,12,13,22]
def F_10 : Nat := fullMask 26
set_option maxHeartbeats 0 in
lemma gp_10 : goodPairs g_10 p_10 q_10 := goodPairs_of (by decide +kernel)
def W_10 : BT Decor := buildWiresBT 8 (mkBase p_10 q_10 r_10) [(0,0,4),(1,1,2),(0,6,3),(1,5,7),(0,3,4),(0,2,4),(1,1,10),(2,11,3),(3,2,3),(1,0,7),(0,14,4),(2,6,3),(0,1,2),(3,17,3),(3,0,4),(1,19,7),(2,6,9),(1,2,4),(3,10,22),(0,0,3),(2,0,3),(1,25,1),(0,1,4),(1,27,2),(2,0,7),(1,5,2),(0,6,4),(1,25,17),(0,7,4),(1,5,1),(1,34,2),(0,35,3),(0,28,3),(2,0,37),(3,6,3),(3,39,4),(0,11,3),(3,24,6),(3,31,3),(1,3,4),(3,9,44),(1,1,4),(0,3,46),(0,0,47),(0,0,11),(1,13,10),(3,1,3),(3,51,4),(1,13,1),(0,53,4),(1,1,3),(3,10,55),(1,2,3),(3,1,57),(3,58,4),(0,1,3),(0,2,3),(1,61,1),(3,3,4),(3,7,4),(0,3,22),(2,0,65),(2,0,2),(1,67,1),(0,26,4),(0,0,6),(2,1,4),(3,1,4),(3,2,46),(0,68,4),(1,71,24),(3,24,46),(1,67,27),(1,24,2),(2,1,2),(2,2,1),(1,80,13),(1,24,27),(3,63,6),(3,10,1),(0,1,22),(1,24,1),(3,61,6),(0,86,4),(3,2,9),(1,24,17),(3,2,55),(1,71,25),(1,79,24),(0,57,4),(1,25,27),(3,25,46),(1,25,79),(3,6,4),(3,98,3),(1,13,27),(3,25,6),(2,34,2),(3,5,6),(1,1,9),(1,63,1),(2,3,4),(3,106,0),(0,1,44),(0,0,44),(2,2,4),(3,110,3),(3,110,0),(0,0,46),(3,13,4),(2,2,3),(3,115,1),(1,115,1),(2,1,3),(1,118,2),(3,2,4),(3,2,44),(3,13,1),(3,3,46),(2,0,1),(3,124,4),(3,24,4),(3,10,3),(3,25,4),(0,55,4),(3,80,3),(2,0,61),(0,0,2),(1,132,1),(0,0,1),(2,0,4)]
lemma W_10_ok : btAll (fun x => faithful p_10 q_10 x ∧ x.1 < 2^64) W_10 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_10 : List (List (Nat × Nat)) := [[],[(1,2)]]
def A_10 : BT (List (Nat × Nat)) := btOfList 1 al_10
set_option maxHeartbeats 0 in
lemma A_10_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_10 = g_10) A_10 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_10_0 : Slice r_10 g_10 (subcubeFast 0 1) 6 := by
  have hc : Lower (varsOf 30) 0xfffcc000fffcc000 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_1 : Slice r_10 g_10 (subcubeFast 4 16) 4 := by
  have hc : Lower (varsOf 11) 0xee88ee88ee88ee88 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_2 : Slice r_10 g_10 (subcubeFast 2 16) 4 := by
  have hc : Lower (varsOf 13) 0xfaa0faa0faa0faa0 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 2) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_3 : Slice r_10 g_10 (subcubeFast 1 8) 4 := by
  have hc : Lower (varsOf 22) 0xfcfcc0c0fcfcc0c0 4 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_4 : Slice r_10 g_10 (identDom 1 2) 5 := by
  have hc : Lower (varsOf 27) 0xee88cc00ee88cc00 5 := carry_of (swaps := [(1,2),(2,4)]) (by decide +kernel) low_6
  exact slice_ident (u := 1) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_5 : Slice r_10 g_10 (identDom 1 3) 5 := by
  have hc : Lower (varsOf 23) 0xececc0c0ececc0c0 5 := carry_of (swaps := [(1,3),(2,3),(3,4)]) (by decide +kernel) low_8
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_6 : Slice r_10 g_10 (identDom 2 3) 5 := by
  have hc : Lower (varsOf 23) 0xf8f8c0c0f8f8c0c0 5 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_8
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_7 : Slice r_10 g_10 (subcubeFast 0 4) 4 := by
  have hc : Lower (varsOf 27) 0xffaacc00ffaacc00 4 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_8 : Slice r_10 g_10 (subcubeFast 0 2) 4 := by
  have hc : Lower (varsOf 29) 0xffaaf000ffaaf000 4 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
def S_10 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 0 1,6),some (subcubeFast 4 16,4),some (subcubeFast 2 16,4),some (subcubeFast 1 8,4),some (identDom 1 2,5),some (identDom 1 3,5),some (identDom 2 3,5),some (subcubeFast 0 4,4),some (subcubeFast 0 2,4)]
lemma S_10_ok : btAll (fun o => ∀ p, o = some p → Slice r_10 g_10 p.1 p.2) S_10 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_10_0) (forall_cons (fun _ h => by cases h; exact sl_10_1) (forall_cons (fun _ h => by cases h; exact sl_10_2) (forall_cons (fun _ h => by cases h; exact sl_10_3) (forall_cons (fun _ h => by cases h; exact sl_10_4) (forall_cons (fun _ h => by cases h; exact sl_10_5) (forall_cons (fun _ h => by cases h; exact sl_10_6) (forall_cons (fun _ h => by cases h; exact sl_10_7) (forall_cons (fun _ h => by cases h; exact sl_10_8) (fun _ h => (List.not_mem_nil h).elim))))))))))
def ps_10 : BT (Option PoolSpec) := btOfList 6 [q 0 [16392,16393,90155],q 4 [12312,28674],q 2 [],q 0 [],q 1 [],q 3 [],q 5 [],q 0 [16389,188428],q 8 [],q 0 [16388,8301],q 7 [],q 0 [16393,90124],q 0 [8196,8197],q 4 [12312],q 4 [24576],q 0 [16390,16391],q 0 [16388,16389],q 0 [16389,188427],q 4 [],q 4 [12314],q 0 [16389,188515],q 0 [16388,110689],q 0 [16392,4139],q 0 [16393,90116],q 0 [8198,98621],q 4 [12288],q 0 [16389,188519],q 4 [12290],q 0 [12299,4149],q 6 [],q 0 [8197],q 0 [4365],q 0 [8196],q 0 [4193],q 0 [8198],q 0 [16399],q 0 [16390],q 0 [16395],q 0 [16483],q 0 [16389],q 0 [16392,12331],q 0 [12299],q 0 [16388],q 0 [4197],q 0 [12293],q 0 [16487],q 0 [16396],q 0 [12296],q 0 [12292],q 0 [4106,12611]]
def B_10_2 : BT (List (List Nat)) := BT.empty
lemma B_10_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_10 2 xs.toFinset) B_10_2 := .empty
def U_10_3 : List Nat := []
def P_10_3 : BT (Option BoundPool) := buildPoolsSubBT 6 W_10 r_10 S_10 ps_10 U_10_3
def N_10_3 : List NodeSpec := [([1,2,8,9],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_10_3 : checkNodesBT W_10 g_10 F_10 P_10_3 A_10 B_10_2 3 N_10_3 = true := by decide +kernel
def B_10_3 : BT (List (List Nat)) := buildBucketsBT W_10 N_10_3
set_option maxRecDepth 500000 in
lemma B_10_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_10 3 xs.toFinset) B_10_3 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok (buildPoolsSubBT_sound S_10_ok) A_10_ok B_10_2_ok C_10_3
def U_10_4 : List Nat := (r 0 4)
def P_10_4 : BT (Option BoundPool) := buildPoolsSubBT 6 W_10 r_10 S_10 ps_10 U_10_4
def N_10_4 : List NodeSpec := [([23,24,0,1,3],[0],[]),([25,23,0,1,3],[0],[]),([29,17,6,3,4],[1],[]),([5,1,30,31,3],[2],[]),([13,5,1,31,3],[2],[]),([1,2,8,3,4],[3],[0]),([5,1,2,33,3],[3],[]),([0,32,6,3,4],[],[]),([43,5,1,2,3],[],[]),([42,0,17,3,4],[],[]),([18,0,7,6,4],[],[]),([13,0,41,11,4],[],[]),([5,1,2,40,3],[],[]),([38,1,28,3,4],[],[]),([5,1,2,7,9],[],[0]),([5,1,2,36,4],[],[]),([12,13,0,11,4],[],[]),([0,26,28,3,4],[],[]),([21,5,1,2,3],[],[]),([1,2,20,3,4],[],[]),([16,18,0,6,4],[],[]),([1,2,7,15,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_10_4 : checkNodesBT W_10 g_10 F_10 P_10_4 A_10 B_10_3 4 N_10_4 = true := by decide +kernel
def B_10_4 : BT (List (List Nat)) := buildBucketsBT W_10 N_10_4
set_option maxRecDepth 500000 in
lemma B_10_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_10 4 xs.toFinset) B_10_4 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok (buildPoolsSubBT_sound S_10_ok) A_10_ok B_10_3_ok C_10_4
def U_10_5 : List Nat := ([0]++r 2 27)
def P_10_5 : BT (Option BoundPool) := buildPoolsSubBT 6 W_10 r_10 S_10 ps_10 U_10_5
def N_10_5 : List NodeSpec := [([5,1,2,9,3,104],[2],[]),([0,60,2,62,3,4],[2],[]),([24,0,1,2,7,4],[3],[]),e5 [92] [3],([25,0,1,2,47,4],[3],[]),([29,1,2,7,3,4],[3],[]),([25,0,1,2,7,4],[3],[]),e5 [75] [3],([19,1,2,7,3,4],[3],[0]),([13,0,1,31,3,4],[2,4],[0]),([13,0,11,3,4],[2,4],[0]),([5,1,2,31,3],[2,4,3],[0,1]),([103,5,1,2,3,4],[3,4],[]),([39,5,1,2,3,4],[4],[0]),([89,5,1,2,9,3],[4],[]),e5 [103] [4],([13,81,0,1,3,4],[4],[]),e5 [100] [4],e5 [74] [4],([13,0,1,3,50,4],[4],[]),([87,0,1,6,3,4],[4],[]),e5 [77] [4],e5 [54] [4],e5 [56] [4],e5 [59] [4],([5,1,2,31,6,3],[4,2],[]),([23,0,1,3],[4,2,0],[0]),([13,0,1,11,3,4],[2,5],[]),([13,0,60,6,3,4],[2,5],[]),([13,5,1,6,3,4],[2,5],[0]),([13,19,1,6,3,4],[2,5],[]),e5 [7] [3,5],e5 [83] [3,5],e5 [99] [3,5],u5 [33] [3,5,4,2],([5,1,2,6,9,3],[4,2,5],[0]),([13,51,0,6,3,4],[4,5],[]),([0,60,61,6,3,4],[4,5],[]),([45,0,1,2,9],[4,5,2],[]),e5 [101] [5],([1,2,7,14,3,4],[5],[0]),([71,0,86,2,3,4],[5],[]),([5,1,30,6,3,4],[5,2],[0]),([45,0,1,2],[5,2,4],[]),e5 [64] [5,3],([5,1,2,35,3,4],[5,3,4],[0]),([5,1,2,7,3,4],[5,4],[0]),e5 [41] [3,5,6],([0,1,52,2,9,3],[6,4],[]),([48,0,1,2,47,4],[6,2,7],[]),([12,0,2,11,3,4],[2,4,8],[0]),([91,0,1,10,3,4],[4,8],[]),([49,0,2,11,3,4],[8],[]),([24,0,1,2,47,4],[8,2,3],[]),([25,0,1,28,3,4],[2,9],[0]),([24,0,1,28,3,4],[9],[]),([0,1,2,31,9,3],[4,8,2,10,5],[]),([5,0,1,2,31,3],[8,10,3,4],[]),e5 [88] [8,10,4],([0,1,2,7,9,4],[8,10,4],[0]),([0,1,37,28,3,4],[9,2,4,10],[0,1]),([0,27,68,2,3,4],[10],[]),([0,17,1,78,3,4],[10],[]),([0,27,53,2,3,4],[10],[]),([0,27,1,2,3,94],[10,8,4],[]),([66,0,1,2,65,4],[11],[]),([0,17,7,6,3,4],[12,4,13,10],[0]),([70,0,17,6,3,4],[10,14],[]),([71,25,72,0,2,3],[15],[1]),([71,72,24,0,2,3],[15],[1]),([24,0,27,2,3,46],[16],[1]),([25,0,27,2,3,46],[16],[1]),([73,24,0,1,3,4],[17],[]),([25,73,0,1,3,4],[17],[]),([18,0,6,3,4],[18,4],[0]),([16,0,17,6,3,4],[18,4,19,10],[0]),e5 [76] [20],e5 [82] [21],([84,24,0,2,3,4],[22],[]),([25,84,0,2,3,4],[22],[]),([24,0,85,2,3,4],[10,4,23],[]),([25,0,85,2,3,4],[23],[]),e5 [93] [24],([24,0,17,6,3,4],[10,12,25],[0]),e5 [96] [26],([25,0,17,6,3,4],[4,12,27],[0]),([0,60,53,2,3,4],[28,2],[]),([79,0,26,2,3,4],[],[]),([39,19,1,2,3,4],[],[]),e5 [97] [],([19,1,53,2,3,4],[],[]),([5,1,53,2,3,4],[],[]),([91,19,1,2,3,4],[],[]),e5 [90] [],u5 [40] [],([63,0,1,2,7,4],[],[]),([0,27,26,2,3,4],[],[0]),u5 [43] [],([102,5,1,2,3,4],[],[]),u5 [42] [],e5 [95] [],([29,1,2,6,3,4],[],[0]),u5 [21] [],u5 [32] [],e5 [69] []]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_10_5 : checkNodesBT W_10 g_10 F_10 P_10_5 A_10 B_10_4 5 N_10_5 = true := by decide +kernel
def B_10_5 : BT (List (List Nat)) := buildBucketsBT W_10 N_10_5
set_option maxRecDepth 500000 in
lemma B_10_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_10 5 xs.toFinset) B_10_5 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok (buildPoolsSubBT_sound S_10_ok) A_10_ok B_10_4_ok C_10_5
def U_10_6 : List Nat := (r 2 9++[12]++r 15 4++[22,23,25]++r 27 23)
def P_10_6 : BT (Option BoundPool) := buildPoolsSubBT 6 W_10 r_10 S_10 ps_10 U_10_6
def N_10_6 : List NodeSpec := [([0,1,2,9,44],[2,4,5],[0]),([13,0,1,10,3,4],[2,4,5],[0]),([0,1,119,3,4],[2,5],[]),([0,116,2,3,4],[2,5],[]),([107,1,2,3,4],[2,5],[]),([0,108,2,3,4],[2,5],[]),([109,1,2,3,4],[2,5],[]),([113,1,2,3,4],[2,5],[]),([112,1,2,3,4],[2,5],[]),([5,1,2,3,4],[2,5],[]),([5,1,34,2,3,4],[2,5,4],[0,1]),([106,5,1,2,3],[4,5],[]),e5 [133] [4,5],([106,63,0,1,2],[4,5],[0]),([121,0,1,3,4],[5,2],[]),([13,5,1,2,3,4],[5,2,4],[0]),u5 [18] [5,3,2,4],e5 [111] [5,3,4,2],([123,0,1,2,4],[5,4],[]),([131,1,2,3,4],[5,4],[]),e5 [117] [5,4],([5,1,2,9,3,4],[5,4,2],[]),([5,1,2,9,3],[5,4,2],[0,1]),e5 [9] [5,4,2],([0,60,2,55,4],[2,5,6],[]),u5 [9,104] [2,6],([0,1,2,47,4],[2,4,7],[0,1]),u5 [47] [5,7,4,2],([0,60,2,6,3,4],[2,5,4,8],[0,1]),([79,51,0,2,3,4],[2,5,8,4],[1]),e5 [67,72] [2,8,4],u5 [11] [2,8,5,3,4],u5 [62] [5,3,4,8],u5 [67,27] [2,4,10],e5 [125] [2,5,4,10],e5 [34] [2,5,8,4,10],e5 [13,72] [2,8,4,10],u5 [13,27] [2,10,4],([13,0,1,6,3,4],[2,10,4,5],[0]),([0,1,28,3,4],[2,10,9,4],[0,1]),u5 [70,6] [3,10],u5 [16,6] [4,2,8,10],u5 [31,6] [4,2,10],([13,120,0,1,3,4],[4,2,10],[]),u5 [6,9] [4,8,2,10,5],e5 [13,114] [4,10],a5 [129] [5,2,4,10] [1],e5 [13] [5,2,8,4,10],e5 [105] [5,2,8,4,10],a5 [91] [5,2,8,10] [0,1],u5 [52] [5,3,2,4,10,6],u5 [6] [5,3,4,2,8,10],a5 [31] [5,3,4,2,10] [0,1],u5 [98] [5,3,4,2,10,8],u5 [7] [5,3,8,2,10],u5 [39] [5,3,10,8,4],e5 [104] [8,2,5,3,4,10],u5 [63,6] [8,2,10,4,5],a5 [27,57] [10,4,2] [0,1],e5 [120,55] [10,4,2],([71,72,0,2,3],[4,2,15],[0,1]),([0,27,2,3,46],[2,4,16],[0,1]),([73,0,1,3,4],[4,2,17],[0]),([0,17,6,3,4],[4,10,12,18],[0]),([84,0,2,3,4],[2,4,22],[0]),([0,85,2,3,4],[2,4,23],[0]),u5 [53] [8,28,5,10,4],a5 [13,9] [4,5,29] [1],a5 [89,9] [4,29] [0,1],e5 [89] [5,3,2,8,29,4],u5 [13,51] [6,4,2,29,5],e5 [13,122] [8,29,4,10],e5 [13,53] [10,2,4,29],([5,1,2,6,3,4],[2,4,5,30],[0,1]),u5 [24,6] [5,10,30],u5 [25,6] [8,2,10,4,5,30],u5 [5,6] [8,2,10,4,5,30],u5 [7,6] [30,2,4,8,10,5],([19,1,2,6,3,4],[30,4,2,5],[0,1]),u5 [68] [5,31,10,8,4],a5 [24,17] [4,5,2,32] [0,1],u5 [25,17] [4,5,32],a5 [86] [5,33,8,4,10] [0,1],u5 [25,79] [2,5,34,27],u5 [79,24] [5,10,4,34,25],([63,19,1,2,3,4],[35,2,4,5],[]),u5 [71,25] [4,5,36],u5 [71,24] [5,2,36],a5 [120,24] [5,4,10,37] [1],a5 [25,120] [5,4,10,37] [1],e5 [126] [5,38,2,8,4,10],a5 [25,46] [5,4,39] [0,1],a5 [24,46] [8,2,5,39] [0,1],e5 [127] [5,2,8,4,40],u5 [13,60] [2,4,41,5,10],([13,19,1,2,3,4],[41,2,5,4],[0]),a5 [25,27] [2,5,42] [0,1],a5 [24,27] [2,5,42] [0,1],u5 [26] [5,43,8,4,10],([19,1,2,3,55,4],[5,44,2,4],[0]),e5 [128] [45,5,2,8,4,10],([19,1,2,9,3,4],[46,5,2,4],[]),a5 [60,61] [47,5,48,4,2] [0,1],e5 [130] [5,49,4,8]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_10_6 : checkNodesBT W_10 g_10 F_10 P_10_6 A_10 B_10_5 6 N_10_6 = true := by decide +kernel
def B_10_6 : BT (List (List Nat)) := buildBucketsBT W_10 N_10_6
set_option maxRecDepth 500000 in
lemma B_10_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_10 6 xs.toFinset) B_10_6 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok (buildPoolsSubBT_sound S_10_ok) A_10_ok B_10_5_ok C_10_6
def U_10_7 : List Nat := (r 2 5++[8,10,18,29,30,32,34,36,37,39,41,42,46,48])
def P_10_7 : BT (Option BoundPool) := buildPoolsSubBT 6 W_10 r_10 S_10 ps_10 U_10_7
def N_10_7 : List NodeSpec := [([19,1,2,3,4],[3,4,2],[0,1]),a5 [44] [2,4,5,3] [0,1],([5,1,2,3,4],[2,5,4,3],[0,1]),a5 [134] [3,4,5,2] [1],a5 [5] [4,2,5,3] [0,1],u5 [135] [4,3,2,5],u5 [106] [4,3,5,2],a5 [63] [5,2,4] [0,1],a5 [25] [5,2,4,3] [0,1],a5 [24] [5,2,4,3] [0,1],a5 [118] [2,5,4,6] [0,1],a5 [55] [5,2,8,4] [0,1],a5 [67] [4,2,5,3,10] [0,1],a5 [6] [2,8,4,10,5,30] [0,1],u5 [17] [4,5,2,32],a5 [79] [2,5,4,10,34,18] [0,1],a5 [71] [4,3,5,2,36] [0,1],a5 [120] [5,4,2,37] [0,1],a5 [46] [2,4,39,5,3] [0,1],a5 [13] [5,41,2,10,4,29] [0,1],a5 [27] [2,5,4,42] [0,1],a5 [9] [2,46,5,4] [0,1],a5 [60] [2,3,5,48,4] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_10_7 : checkNodesBT W_10 g_10 F_10 P_10_7 A_10 B_10_6 7 N_10_7 = true := by decide +kernel
def B_10_7 : BT (List (List Nat)) := buildBucketsBT W_10 N_10_7
set_option maxRecDepth 500000 in
lemma B_10_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_10 7 xs.toFinset) B_10_7 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok (buildPoolsSubBT_sound S_10_ok) A_10_ok B_10_6_ok C_10_7
def U_10_8 : List Nat := [3]
def P_10_8 : BT (Option BoundPool) := buildPoolsSubBT 6 W_10 r_10 S_10 ps_10 U_10_8
def N_10_8 : List NodeSpec := [a5 [] [3] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_10_8 : checkNodesBT W_10 g_10 F_10 P_10_8 A_10 B_10_7 8 N_10_8 = true := by decide +kernel
def B_10_8 : BT (List (List Nat)) := buildBucketsBT W_10 N_10_8
set_option maxRecDepth 500000 in
lemma B_10_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_10 8 xs.toFinset) B_10_8 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok (buildPoolsSubBT_sound S_10_ok) A_10_ok B_10_7_ok C_10_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_10_ok : forestRootCheck r_10 g_10 [(VAR 0,18,19),(VAR 1,12,14),(VAR 2,10,14),(VAR 3,6,14),(VAR 4,3,19)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_10_in : bucketContainsBT B_10_8 r_10 = true := by decide +kernel
lemma low_10 : Lower r_10 g_10 9 := lower_of_forestBT root_10_ok B_10_8_ok root_10_in
def g_11 := 0xfee8fee8fee8fee8
def r_11 : List Nat := varsOf 15
def p_11 : List Nat := [3,3,5,5,6,6,9,9,10,10,12,12]
def q_11 : List Nat := [2,1,4,1,4,2,8,1,8,2,8,4]
def F_11 : Nat := fullMask 12
set_option maxHeartbeats 0 in
lemma gp_11 : goodPairs g_11 p_11 q_11 := goodPairs_of (by decide +kernel)
def W_11 : BT Decor := buildWiresBT 4 (mkBase p_11 q_11 r_11) [(1,0,1),(1,4,2),(2,5,3),(1,1,2),(1,3,1),(1,3,2),(2,4,3),(1,3,0)]
lemma W_11_ok : btAll (fun x => faithful p_11 q_11 x ∧ x.1 < 2^64) W_11 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_11 : List (List (Nat × Nat)) := [[],[(2,3)],[(1,2)],[(1,3),(2,3)],[(1,2),(2,3)],[(1,3)],[(0,2),(1,2)],[(0,3),(1,3),(2,3)],[(0,2),(1,2),(2,3)],[(0,3),(1,3)],[(0,1),(1,2)],[(0,2),(1,3)]]
def A_11 : BT (List (Nat × Nat)) := btOfList 4 al_11
set_option maxHeartbeats 0 in
lemma A_11_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_11 = g_11) A_11 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_11_0 : Slice r_11 g_11 (subcubeFast 1 0) 4 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_1 : Slice r_11 g_11 (subcubeFast 2 0) 4 := by
  have hc : Lower (varsOf 13) 0xfaa0faa0faa0faa0 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_2 : Slice r_11 g_11 (subcubeFast 4 0) 4 := by
  have hc : Lower (varsOf 11) 0xee88ee88ee88ee88 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_3 : Slice r_11 g_11 (subcubeFast 8 0) 4 := by
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) low_0
def S_11 : BT (Option (Nat × Nat)) := btOfList 2 [some (subcubeFast 1 0,4),some (subcubeFast 2 0,4),some (subcubeFast 4 0,4),some (subcubeFast 8 0,4)]
lemma S_11_ok : btAll (fun o => ∀ p, o = some p → Slice r_11 g_11 p.1 p.2) S_11 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_11_0) (forall_cons (fun _ h => by cases h; exact sl_11_1) (forall_cons (fun _ h => by cases h; exact sl_11_2) (forall_cons (fun _ h => by cases h; exact sl_11_3) (fun _ h => (List.not_mem_nil h).elim)))))
def ps_11 : BT (Option PoolSpec) := btOfList 2 [q 2 [],q 1 [],q 3 [],q 0 []]
def B_11_2 : BT (List (List Nat)) := BT.empty
lemma B_11_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_11 2 xs.toFinset) B_11_2 := .empty
def U_11_3 : List Nat := [0,1]
def P_11_3 : BT (Option BoundPool) := buildPoolsSubBT 2 W_11 r_11 S_11 ps_11 U_11_3
def N_11_3 : List NodeSpec := [([0,7,8,9],[0,1],[]),([6,0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_11_3 : checkNodesBT W_11 g_11 F_11 P_11_3 A_11 B_11_2 3 N_11_3 = true := by decide +kernel
def B_11_3 : BT (List (List Nat)) := buildBucketsBT W_11 N_11_3
set_option maxRecDepth 500000 in
lemma B_11_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_11 3 xs.toFinset) B_11_3 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok (buildPoolsSubBT_sound S_11_ok) A_11_ok B_11_2_ok C_11_3
def U_11_4 : List Nat := [1,2,3]
def P_11_4 : BT (Option BoundPool) := buildPoolsSubBT 2 W_11 r_11 S_11 ps_11 U_11_4
def N_11_4 : List NodeSpec := [([0,1,2,5,3],[2],[0]),([0,1,2,11,8],[3,1],[10]),([10,0,1,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_11_4 : checkNodesBT W_11 g_11 F_11 P_11_4 A_11 B_11_3 4 N_11_4 = true := by decide +kernel
def B_11_4 : BT (List (List Nat)) := buildBucketsBT W_11 N_11_4
set_option maxRecDepth 500000 in
lemma B_11_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_11 4 xs.toFinset) B_11_4 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok (buildPoolsSubBT_sound S_11_ok) A_11_ok B_11_3_ok C_11_4
def U_11_5 : List Nat := (r 0 4)
def P_11_5 : BT (Option BoundPool) := buildPoolsSubBT 2 W_11 r_11 S_11 ps_11 U_11_5
def N_11_5 : List NodeSpec := [([0,1,4,2,3],[3,1,0,2],[0,1,3,5,7,9])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_11_5 : checkNodesBT W_11 g_11 F_11 P_11_5 A_11 B_11_4 5 N_11_5 = true := by decide +kernel
def B_11_5 : BT (List (List Nat)) := buildBucketsBT W_11 N_11_5
set_option maxRecDepth 500000 in
lemma B_11_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_11 5 xs.toFinset) B_11_5 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok (buildPoolsSubBT_sound S_11_ok) A_11_ok B_11_4_ok C_11_5
def U_11_6 : List Nat := (r 0 4)
def P_11_6 : BT (Option BoundPool) := buildPoolsSubBT 2 W_11 r_11 S_11 ps_11 U_11_6
def N_11_6 : List NodeSpec := [([0,1,2,3],[3,1,0,2],[0,2,4,6,8,11])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_11_6 : checkNodesBT W_11 g_11 F_11 P_11_6 A_11 B_11_5 6 N_11_6 = true := by decide +kernel
def B_11_6 : BT (List (List Nat)) := buildBucketsBT W_11 N_11_6
set_option maxRecDepth 500000 in
lemma B_11_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_11 6 xs.toFinset) B_11_6 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok (buildPoolsSubBT_sound S_11_ok) A_11_ok B_11_5_ok C_11_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_11_ok : forestRootCheck r_11 g_11 [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 3,1,9)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_11_in : bucketContainsBT B_11_6 r_11 = true := by decide +kernel
lemma low_11 : Lower r_11 g_11 7 := lower_of_forestBT root_11_ok B_11_6_ok root_11_in
def g_12 := 0xfff8e880fff8e880
def r_12 : List Nat := varsOf 31
def p_12 : List Nat := [7,7,7,11,11,11,13,13,13,14,14,14,19,19,19,20,20,21,21,22,22,24,24,25,25,26,26,28]
def q_12 : List Nat := [6,5,3,10,9,3,12,9,5,12,10,6,18,17,3,16,4,17,5,18,6,16,8,17,9,18,10,12]
def F_12 : Nat := fullMask 28
set_option maxHeartbeats 0 in
lemma gp_12 : goodPairs g_12 p_12 q_12 := goodPairs_of (by decide +kernel)
def W_12 : BT Decor := buildWiresBT 8 (mkBase p_12 q_12 r_12) [(1,2,3),(0,0,1),(1,6,4),(0,5,7),(0,2,3),(1,9,4),(0,6,2),(1,11,4),(0,3,12),(1,3,12),(3,13,14),(0,1,3),(1,16,2),(1,17,4),(0,0,18),(1,16,4),(0,2,20),(0,6,3),(1,22,4),(1,2,23),(3,3,24),(1,2,4),(0,0,26),(0,0,3),(1,28,4),(3,6,10),(0,0,5),(1,6,9),(2,0,4),(0,1,2),(1,34,4),(0,3,35),(1,3,35),(3,36,37),(0,6,5),(1,39,4),(1,6,2),(1,41,4),(3,6,42),(0,0,2),(1,44,4),(2,6,4),(1,46,9),(2,32,4),(2,2,23),(3,2,23),(0,3,7),(1,51,2),(1,3,4),(1,9,7),(1,28,35),(1,25,22),(0,1,26),(1,28,34),(2,58,4),(0,2,23),(1,3,7),(0,3,26),(3,51,61),(0,2,7),(0,3,42),(2,2,7),(3,2,7),(1,41,3),(3,6,68),(3,6,3),(1,70,4),(0,2,61),(2,2,3),(3,3,45),(3,44,3),(1,73,7),(2,5,7),(1,5,4),(3,16,2),(3,9,7),(3,6,2),(1,81,4),(1,6,3),(2,0,36),(1,70,2),(3,3,42),(3,3,41),(3,57,3),(0,1,5),(0,16,26),(3,90,0),(3,46,5),(2,5,4),(3,70,26),(3,75,53),(2,1,4),(3,96,0),(3,22,26),(2,2,4),(3,6,78),(3,3,7),(3,70,53),(3,16,26),(3,70,5),(2,3,4),(1,105,2),(3,6,106),(1,73,6),(3,51,2),(2,41,4),(3,3,12),(1,69,4),(1,64,3),(0,2,29),(2,0,20),(1,73,4),(1,28,2),(2,117,4),(2,108,4),(3,73,26),(0,6,53),(3,121,2),(1,25,6),(3,16,0),(3,2,14),(1,125,44),(0,2,53),(2,3,2),(3,128,7),(2,68,4),(3,28,0),(1,131,4),(1,44,3),(3,34,3),(1,79,4),(3,16,45),(0,0,10),(1,2,29),(2,2,20),(3,2,20),(1,46,73),(1,33,2),(3,16,142),(2,9,4),(3,144,5),(0,0,53),(2,0,10),(3,89,0),(2,0,62),(0,1,53),(3,150,0),(3,128,53),(0,0,78),(1,31,4),(0,6,26),(0,44,3),(1,156,4),(0,44,53),(1,105,44),(2,1,3),(3,160,0),(2,1,2),(3,162,53),(3,33,3),(3,99,3),(3,22,2),(1,11,3),(3,160,2),(1,168,4),(1,96,2),(1,99,6),(0,34,3),(3,172,0),(1,133,4),(1,75,4),(0,0,35),(3,125,0),(1,160,4),(1,96,3),(1,73,28),(3,150,2),(3,162,0),(1,162,4),(3,105,2),(3,105,0),(2,73,4),(3,128,0),(2,0,9),(2,44,4),(2,131,4),(2,6,3),(3,96,2),(2,131,2),(1,131,2),(2,44,3)]
lemma W_12_ok : btAll (fun x => faithful p_12 q_12 x ∧ x.1 < 2^64) W_12 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_12 : List (List (Nat × Nat)) := [[],[(2,3)],[(0,1)],[(0,1),(2,3)]]
def A_12 : BT (List (Nat × Nat)) := btOfList 2 al_12
set_option maxHeartbeats 0 in
lemma A_12_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_12 = g_12) A_12 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_12_0 : Slice r_12 g_12 (subcubeFast 0 1) 7 := by
  have hc : Lower (varsOf 30) 0xfffcfcc0fffcfcc0 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_11
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_1 : Slice r_12 g_12 (subcubeFast 0 2) 7 := by
  have hc : Lower (varsOf 29) 0xfffafaa0fffafaa0 7 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_11
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_2 : Slice r_12 g_12 (subcubeFast 16 0) 7 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_1
set_option maxHeartbeats 0 in
lemma sl_12_3 : Slice r_12 g_12 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) 0xfff0a000fff0a000 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_4 : Slice r_12 g_12 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) 0xff888800ff888800 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_5 : Slice r_12 g_12 (subcubeFast 0 4) 5 := by
  have hc : Lower (varsOf 27) 0xffffee88ffffee88 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_6 : Slice r_12 g_12 (subcubeFast 8 0) 5 := by
  have hc : Lower (varsOf 23) 0xf8f88080f8f88080 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_7 : Slice r_12 g_12 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) 0xfff0c000fff0c000 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_8 : Slice r_12 g_12 (subcubeFast 16 8) 4 := by
  exact slice_fast_direct_f (z := 16) (o := 8) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_12_9 : Slice r_12 g_12 (subcubeFast 16 4) 4 := by
  have hc : Lower (varsOf 11) 0xee88ee88ee88ee88 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_10 : Slice r_12 g_12 (subcubeFast 16 2) 4 := by
  have hc : Lower (varsOf 13) 0xfaa0faa0faa0faa0 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_11 : Slice r_12 g_12 (subcubeFast 8 2) 4 := by
  have hc : Lower (varsOf 21) 0xfafaa0a0fafaa0a0 4 := carry_of (swaps := [(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 8) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_12 : Slice r_12 g_12 (subcubeFast 4 2) 4 := by
  have hc : Lower (varsOf 25) 0xffaaaa00ffaaaa00 4 := carry_of (swaps := [(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_13 : Slice r_12 g_12 (subcubeFast 16 1) 4 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_14 : Slice r_12 g_12 (subcubeFast 8 1) 4 := by
  have hc : Lower (varsOf 22) 0xfcfcc0c0fcfcc0c0 4 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 8) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_15 : Slice r_12 g_12 (subcubeFast 4 1) 4 := by
  have hc : Lower (varsOf 26) 0xffcccc00ffcccc00 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_16 : Slice r_12 g_12 (subcubeFast 2 1) 4 := by
  have hc : Lower (varsOf 28) 0xfff0f000fff0f000 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 2) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_17 : Slice r_12 g_12 (subcubeFast 1 2) 4 := by
  have hc : Lower (varsOf 28) 0xfff0f000fff0f000 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_18 : Slice r_12 g_12 (identDom 2 3) 6 := by
  have hc : Lower (varsOf 23) 0xf8f8e0e0f8f8e0e0 6 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_2
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
def S_12 : BT (Option (Nat × Nat)) := btOfList 5 [some (subcubeFast 0 1,7),some (subcubeFast 0 2,7),some (subcubeFast 16 0,7),some (subcubeFast 2 0,5),some (subcubeFast 4 0,5),some (subcubeFast 0 4,5),some (subcubeFast 8 0,5),some (subcubeFast 1 0,5),some (subcubeFast 16 8,4),some (subcubeFast 16 4,4),some (subcubeFast 16 2,4),some (subcubeFast 8 2,4),some (subcubeFast 4 2,4),some (subcubeFast 16 1,4),some (subcubeFast 8 1,4),some (subcubeFast 4 1,4),some (subcubeFast 2 1,4),some (subcubeFast 1 2,4),some (identDom 2 3,6)]
lemma S_12_ok : btAll (fun o => ∀ p, o = some p → Slice r_12 g_12 p.1 p.2) S_12 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_12_0) (forall_cons (fun _ h => by cases h; exact sl_12_1) (forall_cons (fun _ h => by cases h; exact sl_12_2) (forall_cons (fun _ h => by cases h; exact sl_12_3) (forall_cons (fun _ h => by cases h; exact sl_12_4) (forall_cons (fun _ h => by cases h; exact sl_12_5) (forall_cons (fun _ h => by cases h; exact sl_12_6) (forall_cons (fun _ h => by cases h; exact sl_12_7) (forall_cons (fun _ h => by cases h; exact sl_12_8) (forall_cons (fun _ h => by cases h; exact sl_12_9) (forall_cons (fun _ h => by cases h; exact sl_12_10) (forall_cons (fun _ h => by cases h; exact sl_12_11) (forall_cons (fun _ h => by cases h; exact sl_12_12) (forall_cons (fun _ h => by cases h; exact sl_12_13) (forall_cons (fun _ h => by cases h; exact sl_12_14) (forall_cons (fun _ h => by cases h; exact sl_12_15) (forall_cons (fun _ h => by cases h; exact sl_12_16) (forall_cons (fun _ h => by cases h; exact sl_12_17) (forall_cons (fun _ h => by cases h; exact sl_12_18) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))))
def ps_12 : BT (Option PoolSpec) := btOfList 7 [q 11 [],q 18 [4096,20504,16541],q 12 [],q 14 [],q 18 [],q 1 [],q 0 [],q 4 [],q 8 [],q 17 [],q 5 [],q 7 [],q 3 [],q 6 [],q 2 [],q 0 [8217,16549,172047],q 2 [12292,106560,363],q 18 [4096,20504],q 0 [12313,16409,16397],q 18 [4096,16410],q 15 [],q 9 [],q 18 [16390,387],q 2 [4096,12312,106587],q 0 [12297,16405,319515],q 0 [8217,12313,12297],q 2 [4096,12312],q 18 [4096,16409],q 18 [4096,20480],q 18 [4096,16386],q 18 [4096,20507],q 2 [4096,217112,8679],q 10 [],q 0 [8217,12453,16658],q 0 [12465,16561,16397],q 2 [8192,217088,217096],q 18 [20484,359],q 2 [106508,253954],q 13 [],q 16 [],q 2 [217092,603],q 2 [106496,106508],q 2 [4096,12288],q 0 [16409,28687],q 2 [4096,106496],q 1 [16393,106563],q 2 [8192,217096],q 0 [16409,16393],q 0 [16393,106511],q 1 [16409,16393],q 2 [4096,106520],q 0 [12297,20507],q 0 [8305,16854],q 18 [16386],q 2 [4096,8216],q 2 [4096,106523],q 0 [12465,16397],q 2 [8192,217264],q 18 [4096],q 2 [4096,8219],q 2 [4096,8192],q 2 [4,8196],q 0 [8217,12453],q 0 [12313,8205],q 0 [12313,16397],q 0 [8217,12454],q 0 [8217,16550],q 18 [20480],q 0 [16561,16397],q 2 [4096,12315],q 2 [8192,217088],q 0 [8205,16397],q 0 [12297,16406],q 0 [16393,106523],q 1 [16393,106523],q 2 [12292,67],q 2 [12292,8259],q 0 [8305,16497],q 0 [12297,16405],q 0 [12465,16917],q 18 [16421],q 2 [8192,12467],q 0 [16397,217099],q 0 [16561,184335],q 0 [8217,16549],q 0 [8217,16409],q 2 [217092,8795],q 2 [12292,106563],q 0 [8217,12313],q 1 [16393,106511],q 2 [217096],q 1 [12297,16406],q 0 [16393],q 2 [106496],q 1 [8205,16397],q 0 [16561],q 2 [8192],q 0 [12465],q 1 [12297,16405],q 2 [4096],q 0 [12297],q 1 [12297],q 2 [12296],q 0 [8217],q 0 [16409],q 2 [8196],q 2 [12288],q 1 [16393],q 0 [16397]]
def B_12_2 : BT (List (List Nat)) := BT.empty
lemma B_12_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 2 xs.toFinset) B_12_2 := .empty
def U_12_3 : List Nat := []
def P_12_3 : BT (Option BoundPool) := buildPoolsSubBT 7 W_12 r_12 S_12 ps_12 U_12_3
def N_12_3 : List NodeSpec := [([0,1,8,10],[],[]),([15,0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_3 : checkNodesBT W_12 g_12 F_12 P_12_3 A_12 B_12_2 3 N_12_3 = true := by decide +kernel
def B_12_3 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_3
set_option maxRecDepth 500000 in
lemma B_12_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 3 xs.toFinset) B_12_3 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_2_ok C_12_3
def U_12_4 : List Nat := (r 0 7)
def P_12_4 : BT (Option BoundPool) := buildPoolsSubBT 7 W_12 r_12 S_12 ps_12 U_12_4
def N_12_4 : List NodeSpec := [([31,1,32,5,4],[0],[]),([33,1,32,5,4],[0],[]),([0,1,9,5,40],[1],[]),([6,2,3,45,20],[2,3],[]),([0,1,64,65,4],[4],[]),([0,1,9,8,4],[4],[0]),([0,1,52,4,61],[4],[]),([0,1,5,4,54],[4],[]),([6,2,3,4,55],[5,6],[]),([0,1,52,7,53],[],[]),([63,0,1,2,4],[],[]),([27,1,2,62,29],[],[]),([0,1,60,3,24],[],[1]),([59,6,2,3,4],[],[]),([27,57,2,3,7],[],[]),([56,0,1,2,4],[],[]),([0,1,2,8,53],[],[]),([0,1,5,7,10],[],[0]),([19,1,21,3,4],[],[]),([25,0,1,2,23],[],[]),([49,50,0,1,3],[],[1]),([48,0,1,5,4],[],[]),([0,1,47,5,4],[],[]),([43,0,2,3,20],[],[]),([38,0,1,2,4],[],[]),([30,0,1,5,4],[],[]),([25,27,1,2,29],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_4 : checkNodesBT W_12 g_12 F_12 P_12_4 A_12 B_12_3 4 N_12_4 = true := by decide +kernel
def B_12_4 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_4
set_option maxRecDepth 500000 in
lemma B_12_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 4 xs.toFinset) B_12_4 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_3_ok C_12_4
def U_12_5_0 : List Nat := ([0]++r 2 35)
def P_12_5_0 : BT (Option BoundPool) := buildPoolsSubBT 7 W_12 r_12 S_12 ps_12 U_12_5_0
def N_12_5_0 : List NodeSpec := [([6,44,2,3,4,20],[2],[0,1]),([6,0,1,32,5,4],[0,3],[]),([147,0,1,5,4,10],[3],[]),([137,0,1,5,4,10],[3],[]),([115,6,2,3,4,20],[3],[]),([0,1,32,5,4],[0,3,4],[0,2]),([33,1,2,32,3,4],[0,6],[0]),([103,6,0,2,3,4],[6],[]),e5 [112] [6,5],([99,70,0,1,5,4],[7],[]),([0,1,2,5,4,71],[7],[]),([81,70,0,1,5,4],[7],[]),([81,0,1,5,4,53],[7],[]),([0,1,2,113,4,7],[7],[1]),e5 [129] [7],([0,1,145,4],[0,3,8],[]),([0,1,2,3,132,35],[8],[]),([0,1,2,3,116,7],[8],[]),([0,1,72,3,4,7],[8],[1]),([25,6,28,1,2,4],[8],[]),([0,1,114,3,29,26],[8],[]),([43,28,1,2,3,4],[8],[2]),([6,0,1,5,4,10],[8,0,3],[0]),([27,1,2,3,7,26],[9],[0]),([6,58,2,3,4],[9,6],[0]),u5 [54] [5,6,7,10],([25,28,27,1,2,4],[6,10],[0]),e5 [123] [10],e5 [76] [10],([25,22,0,1,2,4],[10],[0]),([99,0,1,2,3,23],[10],[]),([44,0,126,1,3,4],[10],[]),([19,1,2,3,4,20],[10],[0]),([118,0,1,2,3,29],[10],[]),([110,0,1,2,3,7],[10],[]),([46,93,0,1,2,3],[10,8],[]),([6,31,89,2,3,4],[10,8,0],[]),a5 [8] [6,5,10,7,12] [0,1],([81,0,1,83,5,4],[7,11,12],[]),([81,0,1,3,4,78],[11,12],[1]),([0,1,2,3,7,78],[11,12],[]),u5 [55] [11,12,5,6],([0,1,2,3,82,7],[11,12,7],[]),e5 [94] [12],([0,1,2,3,7,10],[11,12,7,13],[0]),([0,1,2,3,45,20],[11,12,7,13],[0]),([0,1,2,3,135,20],[12,7,13],[]),([104,0,1,2,5,4],[13],[]),([102,0,1,2,4,53],[13],[]),([43,0,1,3,5,4],[13],[]),([74,0,1,2,45,53],[13],[]),([95,0,1,2,4,53],[13],[]),([25,0,1,2,29,26],[13],[0]),([101,0,1,2,7,53],[13],[]),([69,0,1,2,4,53],[14],[]),([81,0,1,3,7,26],[14,11,12],[]),([79,0,1,3,20,26],[14,12,13],[]),([86,6,0,1,2,4],[15],[]),([91,1,2,3,4,26],[16],[]),([39,0,1,9,5,4],[4,7,8,17],[0]),([0,1,2,83,7,53],[18,11,12,3],[]),([46,0,1,9,5,4],[7,19],[0]),([0,1,2,3,12,14],[11,20,12,2],[1]),([0,1,2,3,12,53],[11,20,12,2,13],[1]),([0,1,127,3,45,53],[20],[1]),([33,93,6,1,2,3],[8,21],[]),([6,0,2,3,35,53],[21,20,3],[1]),([97,0,1,9,5,4],[22],[]),e5 [98] [23],e5 [100] [24],([0,1,41,83,5,4],[25,11,12,2],[]),([0,1,60,2,3,23],[3,11,12,26],[0]),([0,1,9,5,4,7],[27,7,10],[0]),([6,31,1,9,5,4],[10,0,28],[0]),([33,6,1,9,5,4],[8,0,29],[0]),([69,0,1,9,5,4],[7,30],[]),([122,0,1,3,4,53],[31],[]),([6,27,57,2,3,4],[10,32],[0]),([130,6,0,1,2,3],[33],[]),([0,1,2,133,45,53],[34,11,7,21],[]),([44,146,1,127,3,4],[8,21,35],[1]),([148,0,1,9,5,4],[36],[]),([25,124,0,1,2,4],[],[]),([25,134,0,1,2,4],[],[]),([93,81,0,1,3,4],[],[]),e5 [136] [],([0,1,114,3,4,138],[],[2,3]),([93,97,0,1,2,3],[],[]),([139,140,0,1,3,4],[],[1]),e5 [141] [],e5 [143] [],([49,0,1,2,3,23],[],[0]),([109,0,1,3,4,7],[],[]),e5 [103] [],e5 [43] [],e5 [92] [],([25,88,0,1,2,4],[],[]),u5 [30] [],([87,70,0,1,2,4],[],[]),([81,0,1,85,3,4],[],[]),([84,1,2,3,4,35],[],[]),([0,1,2,5,7,53],[],[0]),e5 [80] [],([25,0,1,2,3,7],[],[]),e5 [77] [],([74,75,0,1,2,4],[],[]),u5 [48] [],([0,1,64,3,4,42],[],[0,1]),([73,0,1,3,7,26],[],[]),e5 [69] [],([66,67,0,1,3,4],[],[1]),([86,0,1,2,4,7],[],[]),([27,0,1,3,120,4],[],[]),e5 [119] [],([99,69,0,1,3,4],[],[]),([0,1,2,3,5,40],[],[0]),([33,108,1,2,3,4],[],[]),([81,0,1,106,3,4],[],[]),u5 [59] [],([27,1,2,3,29,26],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_5_0 : checkNodesBT W_12 g_12 F_12 P_12_5_0 A_12 B_12_4 5 N_12_5_0 = true := by decide +kernel
def U_12_5_1 : List Nat := []
def P_12_5_1 : BT (Option BoundPool) := buildPoolsSubBT 7 W_12 r_12 S_12 ps_12 U_12_5_1
def N_12_5_1 : List NodeSpec := [([73,43,0,1,3,4],[],[]),([111,0,1,2,3,12],[],[1]),u5 [47] [],([108,0,1,3,4,26],[],[]),e5 [107] [],([25,81,0,1,3,4],[],[]),([101,70,0,1,2,4],[],[]),([0,1,64,3,7,26],[],[1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_5_1 : checkNodesBT W_12 g_12 F_12 P_12_5_1 A_12 B_12_4 5 N_12_5_1 = true := by decide +kernel
def N_12_5 := N_12_5_0 ++ N_12_5_1
def B_12_5 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_5
set_option maxRecDepth 500000 in
lemma B_12_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 5 xs.toFinset) B_12_5 := by
  have hm0 := checkNodesBT_mem (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_4_ok C_12_5_0
  have hm1 := checkNodesBT_mem (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_4_ok C_12_5_1
  exact buildBucketsBT_of_mem (forall_append (hm0) hm1)
def U_12_6_0 : List Nat := ([0]++r 2 13++r 19 4++[26,27,29,32]++r 37 23)
def P_12_6_0 : BT (Option BoundPool) := buildPoolsSubBT 7 W_12 r_12 S_12 ps_12 U_12_6_0
def N_12_6_0 : List NodeSpec := [u5 [6,32] [0,3],e5 [44,159] [3],e5 [6,108] [6,2],e5 [6,171] [6,2],([0,1,5,4,10],[0,3,8],[0,2]),([73,0,1,165,4],[0,8],[0]),e5 [180] [0,8],([131,1,2,164,4],[0,8],[]),([0,1,9,5,4],[0,8,4],[]),([0,1,127,5,4],[2,8],[]),e5 [10] [3,0,8,7],([144,0,1,5,4],[8,0],[0]),([6,44,16,2,3,4],[9,3,2],[0,1,3]),([73,6,0,1,3,4,26],[8,10,2],[0]),a5 [79,20] [8,10,7] [0,3],([73,27,0,1,3,4,26],[10],[0]),u5 [139,20] [10,7],u5 [66,7] [10,7],([131,0,1,2,62,4,26],[10,8],[]),([6,31,1,2,3,5,4],[10,8,0,6,9],[0]),([33,6,1,9,2,3,4],[0,11,8,3],[0]),u5 [137,10] [3,11],u5 [115,20] [3,11],u5 [147,10] [3,11],a5 [44,20] [8,7,3,11,10] [0,1,3],a5 [114,29] [8,11,0,10,7] [0,3],e5 [157] [11,0,7],([0,1,2,3,157],[11,0,7],[]),e5 [169] [11,6,0,7],([153,1,2,3,4],[11,10,8],[]),a5 [81,83] [8,3,11,12,7] [0,1],([81,0,1,3,4,26],[8,7,11,12],[0,1]),u5 [6,10] [8,12,0,3,11],([81,6,0,1,3,5,4],[10,2,12,11],[0]),u5 [6,5] [10,7,8,12,0,11,6],u5 [6,85] [10,12,3,11,5],u5 [6,106] [10,12,8,0,11,6],u5 [31,89] [12,0,3,11],([99,6,0,1,41,3,4],[12,2],[]),u5 [46,9] [12,7],([0,1,2,167,4],[12,7,8],[]),([0,1,2,3,12],[12,7,11],[0,1]),([73,6,0,1,41,3,4],[12,11,2],[]),([166,0,1,3,4],[7,12,13,11],[]),a5 [81,70] [7,13] [0,1],u5 [39,5] [7,13,8],([81,0,1,3,5,4],[7,13,11,12],[0,1]),u5 [69,5] [7,13,12],a5 [82] [11,6,12,5,7,13,8] [1],e5 [152] [11,6,13,8,12,5],([173,1,2,3,4],[12,7,13,11],[]),a5 [32] [0,3,2,14] [0,2],a5 [69] [5,6,7,10,13,14] [0,1],a5 [108] [10,12,14,2,20] [0,2],([79,0,1,3,4,26],[10,14,20,12,13],[3]),([99,28,0,1,117,3,4],[13,20],[]),u5 [58] [20,0,14],e5 [176,35] [20,11],e5 [135] [20,12,13,10],e5 [99,161] [7,21,8],([0,1,2,152,4,53],[8,21,13],[1,3]),e5 [154] [9,21,8],([73,0,1,41,3,4],[11,2,21,13],[]),e5 [163,53] [21],([44,1,41,3,4],[21,2],[]),a5 [74,45] [21,7,13,8] [0,3],([99,6,0,1,3,5,4],[21,8,2],[0]),u5 [131,35] [21,11,3,20,8],u5 [6,116] [21,12,8,2,6,11],u5 [99,22] [21,7,26],a5 [79,53] [8,13,7,32] [1],u5 [46,5] [10,7,8,13,12,32],a5 [5,7] [10,7,8,13,32] [0,1],u5 [9,7] [32,7,10,13,8],a5 [81,7] [32,10,7] [0,1],a5 [64,7] [32,11,12,10,7] [0,1],a5 [101,7] [32,12,13,8] [0,1],e5 [149,26] [11,3,37],a5 [25,44] [7,38,8,10] [2],a5 [25,27] [11,38,8] [0,2],u5 [46,73] [12,7,10,38,9,19],u5 [27,57] [12,32,38,11],a5 [45,174] [38,2,21,8,13] [1,3],a5 [73,7] [38,11,32,12,7,27,10,13,8] [0,1],a5 [7,42] [38,32,10,7] [0,1],a5 [44,178] [0,8,39] [2],([33,6,1,2,3,5,4],[8,0,38,21,39,9],[0]),e5 [131,183] [11,2,21,39],e5 [131,170] [11,3,39],e5 [182,53] [11,39,2,21],u5 [97,5] [11,39,32],a5 [44,179] [32,8,0,7,39] [3],([33,73,6,1,2,3,4],[38,2,9,39,21,29],[0]),u5 [97,9] [39,11],u5 [148,5] [39,11],e5 [73,97] [39,32,22],e5 [151,53] [11,39,40],a5 [27,62] [13,8,38,11,10,41] [1],([99,6,28,1,2,3,4],[2,20,8,42],[]),u5 [101,6] [12,32,11,8,43],([6,27,1,2,3,4,26],[10,32,6,9,44],[0]),e5 [103,16] [10,12,45],u5 [103] [11,6,12,10,7,45],([44,0,1,127,3,4,53],[8,38,20,10,46],[0]),([6,0,1,2,3,7,26],[14,12,47,11,2],[0,1]),([25,28,0,1,2,4],[8,10,48],[0,1,2]),([25,28,0,1,2,4,26],[8,13,10,48],[0]),a5 [25,6] [12,8,11,5,10,48] [0,2],([0,1,2,3,7,26],[11,47,12,49,7,32],[0,1,2]),a5 [155,26] [7,8,50] [0,1],e5 [69,6] [10,5,51],u5 [118,28] [13,21,7,52],([33,0,1,9,5,4],[8,0,3,53],[0,2]),a5 [11,53] [8,13,12,11,20,2,54] [0,1],a5 [12] [11,12,7,54,13,8] [0,1],e5 [43,26] [7,12,55],([44,0,1,2,133,4,53],[13,8,7,56,11,21],[0]),a5 [158,53] [32,13,57] [3],([6,0,1,9,5,4],[0,3,8,58],[0,2]),a5 [81,53] [8,13,11,20,12,2,59] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_6_0 : checkNodesBT W_12 g_12 F_12 P_12_6_0 A_12 B_12_5 6 N_12_6_0 = true := by decide +kernel
def U_12_6_1 : List Nat := ([0,2,3]++r 5 9++[20,21,32,38,39,55]++r 59 30)
def P_12_6_1 : BT (Option BoundPool) := buildPoolsSubBT 7 W_12 r_12 S_12 ps_12 U_12_6_1
def N_12_6_1 : List NodeSpec := [([81,6,0,1,3,4,26],[10,59,12,2,11],[0]),u5 [6,82] [59,10,2,11,6,12],([6,44,1,2,3,4,53],[21,0,39,2,60],[1,2,3]),([6,0,2,3,4,35],[12,21,20,61,3],[0,1]),([33,6,34,2,3,4],[38,20,9,0,21,3,61],[]),u5 [6,68] [62,32],([6,0,1,2,83,5,4],[13,12,63,11,2],[0]),([6,0,1,2,83,4,53],[13,8,12,64,11,32],[0]),u5 [87,6] [12,2,11,8,65],u5 [110,6] [12,21,7,11,5,66],([31,0,1,9,5,4],[0,3,8,67],[0,2]),([44,0,1,2,3,45,53],[21,7,68,11,3],[0,3]),([0,1,2,3,45,53],[68,21,11,2,13],[0,1,2]),a5 [99,70] [7,21,13,69] [0,1],([44,146,1,2,3,4,53],[8,21,6,70],[0,1]),([6,0,1,2,5,4,53],[21,8,71,2,32],[0,1]),([33,93,0,1,2,3],[8,72,21],[0,2]),a5 [93,6] [12,8,11,5,21,72] [0,1,2],e5 [43,6] [10,5,73],a5 [43] [7,13,8,73,55,74] [0,2],e5 [99,124] [3,11,75],u5 [124,26] [3,39,9,75],([79,0,16,1,3,4,26],[10,76,12,2,13],[0]),a5 [117,29] [77,20,10,8] [0,1],a5 [6,78] [10,8,12,78,11,5] [0,1],a5 [44,174] [79,39,2,10] [3],([0,1,9,5,4,10],[3,0,80,8],[]),a5 [44,175] [81,8,3,11,7,10] [3],e5 [177,53] [8,3,82,11,21],u5 [74,44] [7,21,8,83],u5 [6,42] [84,5,3],a5 [41,7] [85,11,12,2,10,32] [0,1],a5 [181,53] [8,32,7,86] [1],e5 [103,26] [7,12,87],u5 [41,83] [88,11,12,2,10,3,8]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_6_1 : checkNodesBT W_12 g_12 F_12 P_12_6_1 A_12 B_12_5 6 N_12_6_1 = true := by decide +kernel
def N_12_6 := N_12_6_0 ++ N_12_6_1
def B_12_6 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_6
set_option maxRecDepth 500000 in
lemma B_12_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 6 xs.toFinset) B_12_6 := by
  have hm0 := checkNodesBT_mem (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_5_ok C_12_6_0
  have hm1 := checkNodesBT_mem (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_5_ok C_12_6_1
  exact buildBucketsBT_of_mem (forall_append (hm0) hm1)
def U_12_7 : List Nat := ([0]++r 2 13++[20,21,32,38,39,48,53,54,58,59,60,71,72,75,76,78]++r 89 20)
def P_12_7 : BT (Option BoundPool) := buildPoolsSubBT 7 W_12 r_12 S_12 ps_12 U_12_7
def N_12_7 : List NodeSpec := [([0,1,9,5,4],[0,3,8,4],[0,2]),u5 [9] [0,7,8,3],e5 [9,5] [3,0,4,8],([131,28,1,2,3,4],[6,0,8],[]),([73,0,1,9,3,4],[6,0,8,4],[0]),([73,0,1,2,5,4],[6,8,2,4],[0]),a5 [132] [3,9,8] [2,3],e5 [185] [10,7,8,9],e5 [190] [10,7,8,9],e5 [186] [6,11,8,2],e5 [73] [6,11,8,2,4],u5 [73,28] [8,6,11,0,10,7],u5 [106] [0,3,10,11,8,12],u5 [5] [0,3,10,11,8,12],e5 [195] [7,11,5,12,8],e5 [193] [10,11,5,12,8],e5 [191] [12,11,10,7,8],a5 [184] [2,6,11,8,14] [1],a5 [156] [7,11,5,14,0] [0,2],([99,73,0,1,3,4],[14,8,2],[0]),u5 [168] [0,8,20],e5 [188] [3,9,20],([73,0,1,3,4,26],[8,2,20,10],[0,1,2]),([99,0,1,2,3,26],[14,2,20,10],[]),a5 [73,26] [20,2,10,8] [1],a5 [44,16] [2,3,8,21] [0,1,3],e5 [44,5] [2,8,3,21,11],u5 [116] [2,20,8,11,12,21],([0,1,9,2,5,4],[2,21,4],[]),a5 [131,34] [3,20,21,9,8] [0,2],e5 [187] [3,21,9],e5 [194] [3,21,12,5],u5 [9,10] [7,3,0,8,21],u5 [31] [8,9,3,21],e5 [117] [11,0,3,12,21,7],a5 [41] [12,2,11,5,20,21,6,13,8] [0,2],([33,131,1,2,3,4],[14,9,21,8],[0]),e5 [9,26] [20,2,8,21,13],([99,0,1,3,5,4],[21,2,20,8],[0]),a5 [6,9] [0,3,12,8,2,32] [0,2],a5 [192] [20,14,32,8,13] [3],a5 [97] [32,10,7,8,13,11] [0,1],a5 [44,26] [2,8,21,38,11,3] [0,3],a5 [142] [38,10,12,9,13,8] [2,3],a5 [33,160] [0,8,2,9,21,20,39] [2],a5 [131,162] [2,3,39,21,9,8] [0,3],a5 [182] [2,39,21] [0,1],a5 [99,131] [21,20,9,39,8,2] [2],a5 [33,73] [38,8,2,20,9,39,53] [0,2],a5 [11] [12,11,7,8,13,14,54] [0,1],a5 [73,6] [12,2,6,11,5,32,20,8,0,3,58] [0,2],a5 [81] [8,13,2,20,59] [0,1],a5 [81,6] [10,2,12,3,59,11,20] [0,1],([6,44,1,2,3,4],[11,5,0,2,60],[0,1,2]),u5 [124] [3,9,75],a5 [79,16] [2,3,10,76] [0,3],u5 [79] [10,20,2,13,76],a5 [25,26] [8,13,10,48,89] [0,1,2,3],a5 [25] [11,8,12,7,48,89,10] [0,2],u5 [127] [2,20,10,90,8],a5 [127,53] [38,20,8,32,2,21,90] [0,1,2,3],a5 [93] [11,8,12,72,91,21] [0,2],a5 [131,26] [8,92,32,10,3,39,9,20] [0,3],e5 [27] [10,8,13,92,20,9,93],a5 [27,26] [32,8,21,92,9,93] [0,1,3],([0,1,2,5,4,53],[71,94,21,8,14],[0]),a5 [45] [2,95,21,96,12,13,8] [0,1,2,3],e5 [189] [11,8,13,96,2],a5 [44,45] [21,2,95,96,3] [0,1,3],a5 [44,133] [2,3,8,97,21] [0,1],a5 [78] [78,98,10,8,11,6,12,5] [0,2],([33,6,1,2,3,4],[5,2,0,21,8,9,99],[0,1]),a5 [46] [12,11,10,7,8,13,99] [0,1],a5 [99,6] [12,21,2,0,99,20,8] [0,1,2],a5 [7] [12,32,11,38,99,7,10,13,8] [0,1],a5 [33,5] [8,0,38,100,21,39,9] [0,2],a5 [31,5] [10,0,8,100,9] [0,2],a5 [6,5] [0,3,10,8,12,100,2,11,20,101,32] [0,1,2],a5 [10] [0,3,7,21,102,11,12,8] [0,2],u5 [144] [7,6,11,102,0],a5 [33,9] [8,0,38,3,7,21,9,39,102] [0,2],a5 [6,41] [12,2,21,103,9,3,32] [0,1],a5 [6,7] [12,104,9,99,2,3] [0,1],a5 [33,34] [38,20,0,9,8,3,105] [0,2],a5 [99,28] [21,20,0,39,8,106,2] [0,1,2],a5 [6,26] [10,8,99,12,92,2,11,20,107,0] [0,1,2,3],a5 [44,53] [21,32,8,96,108,11,39,2,3] [0,1,3]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_7 : checkNodesBT W_12 g_12 F_12 P_12_7 A_12 B_12_6 7 N_12_7 = true := by decide +kernel
def B_12_7 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_7
set_option maxRecDepth 500000 in
lemma B_12_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 7 xs.toFinset) B_12_7 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_6_ok C_12_7
def U_12_8 : List Nat := ([0]++r 2 5++[8,9,10,12,14,20,21,38,92,96]++r 99 4++[107])
def P_12_8 : BT (Option BoundPool) := buildPoolsSubBT 7 W_12 r_12 S_12 ps_12 U_12_8
def N_12_8 : List NodeSpec := [a5 [131] [6,5,3,14,9,8] [0,2,3],a5 [73] [6,20,5,2,8,14,4] [0,1,2,3],a5 [99] [6,21,5,14,2,20] [0,1,2,3],a5 [33] [14,5,38,6,9] [0,1,2,3],a5 [44] [6,5,2,96] [0,1,2,3],a5 [6] [5,6,12,99] [0,1,2,3],a5 [5] [100,101,8,21,14] [0,1,2,3],a5 [9] [0,3,6,20,102,5,2] [0,1,2],a5 [26] [92,107,10,14] [0,1,2,3]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_8 : checkNodesBT W_12 g_12 F_12 P_12_8 A_12 B_12_7 8 N_12_8 = true := by decide +kernel
def B_12_8 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_8
set_option maxRecDepth 500000 in
lemma B_12_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 8 xs.toFinset) B_12_8 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_7_ok C_12_8
def U_12_9 : List Nat := [5,6,14]
def P_12_9 : BT (Option BoundPool) := buildPoolsSubBT 7 W_12 r_12 S_12 ps_12 U_12_9
def N_12_9 : List NodeSpec := [a5 [] [6,5,14] [0,1,2,3]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_9 : checkNodesBT W_12 g_12 F_12 P_12_9 A_12 B_12_8 9 N_12_9 = true := by decide +kernel
def B_12_9 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_9
set_option maxRecDepth 500000 in
lemma B_12_9_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 9 xs.toFinset) B_12_9 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_8_ok C_12_9
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_12_ok : forestRootCheck r_12 g_12 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11),(VAR 4,3,19)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_12_in : bucketContainsBT B_12_9 r_12 = true := by decide +kernel
lemma low_12 : Lower r_12 g_12 10 := lower_of_forestBT root_12_ok B_12_9_ok root_12_in
def g_13 := 0xfcc08000fcc08000
def r_13 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_13 : Lower r_13 g_13 8 := by
  have hc : Lower (varsOf 30) 0xfcc0c000fcc0c000 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,14,15)]) (by decide +kernel) hc
def g_14 := 0xfee0fee0fee0fee0
def r_14 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_14 : Lower r_14 g_14 5 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,4,5)]) (by decide +kernel) hc
def g_15 := 0xffc8e080ffc8e080
def r_15 : List Nat := varsOf 31
def p_15 : List Nat := [7,7,7,13,13,13,14,14,14,15,19,19,19,22,22,22,23,24,24,25,25,26,26,27,28,28,29]
def q_15 : List Nat := [6,5,3,12,9,5,12,10,6,11,18,17,3,20,18,6,21,16,8,17,9,18,10,11,20,12,21]
def F_15 : Nat := fullMask 27
set_option maxHeartbeats 0 in
lemma gp_15 : goodPairs g_15 p_15 q_15 := goodPairs_of (by decide +kernel)
def W_15 : BT Decor := buildWiresBT 4 (mkBase p_15 q_15 r_15) [(1,0,3),(2,5,4),(1,3,4),(3,0,7),(1,5,4),(1,0,4),(0,1,2)]
lemma W_15_ok : btAll (fun x => faithful p_15 q_15 x ∧ x.1 < 2^64) W_15 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_15 : List (List (Nat × Nat)) := [[],[(1,2),(3,4)]]
def A_15 : BT (List (Nat × Nat)) := btOfList 1 al_15
set_option maxHeartbeats 0 in
lemma A_15_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_15 = g_15) A_15 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_15_0 : Slice r_15 g_15 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) 0xfffaf0a0fffaf0a0 5 := carry_of (swaps := [(1,4),(3,4)]) (by decide +kernel) low_14
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_15_1 : Slice r_15 g_15 (subcubeFast 0 4) 5 := by
  have hc : Lower (varsOf 27) 0xffccee88ffccee88 5 := carry_of (swaps := [(1,2),(2,4)]) (by decide +kernel) low_14
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_15_2 : Slice r_15 g_15 (subcubeFast 8 0) 5 := by
  have hc : Lower (varsOf 23) 0xc8c88080c8c88080 5 := carry_of (swaps := [(1,3),(2,3),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_15_3 : Slice r_15 g_15 (subcubeFast 16 0) 5 := by
  have hc : Lower (varsOf 15) 0xe080e080e080e080 5 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_15_4 : Slice r_15 g_15 (subcubeFast 8 2) 4 := by
  have hc : Lower (varsOf 21) 0xfafaa0a0fafaa0a0 4 := carry_of (swaps := [(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 8) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_15_5 : Slice r_15 g_15 (subcubeFast 1 2) 4 := by
  have hc : Lower (varsOf 28) 0xfff0f000fff0f000 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_15_6 : Slice r_15 g_15 (subcubeFast 1 4) 4 := by
  have hc : Lower (varsOf 26) 0xffcccc00ffcccc00 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_15_7 : Slice r_15 g_15 (subcubeFast 16 4) 4 := by
  have hc : Lower (varsOf 11) 0xee88ee88ee88ee88 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_15_8 : Slice r_15 g_15 (identDom 1 4) 6 := by
  have hc : Lower (varsOf 15) 0xecc8ecc8ecc8ecc8 6 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_2
  exact slice_ident (u := 1) (v := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_15_9 : Slice r_15 g_15 (identDom 2 3) 6 := by
  have hc : Lower (varsOf 23) 0xf8f8e0e0f8f8e0e0 6 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_2
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
def S_15 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 0 2,5),some (subcubeFast 0 4,5),some (subcubeFast 8 0,5),some (subcubeFast 16 0,5),some (subcubeFast 8 2,4),some (subcubeFast 1 2,4),some (subcubeFast 1 4,4),some (subcubeFast 16 4,4),some (identDom 1 4,6),some (identDom 2 3,6)]
lemma S_15_ok : btAll (fun o => ∀ p, o = some p → Slice r_15 g_15 p.1 p.2) S_15 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_15_0) (forall_cons (fun _ h => by cases h; exact sl_15_1) (forall_cons (fun _ h => by cases h; exact sl_15_2) (forall_cons (fun _ h => by cases h; exact sl_15_3) (forall_cons (fun _ h => by cases h; exact sl_15_4) (forall_cons (fun _ h => by cases h; exact sl_15_5) (forall_cons (fun _ h => by cases h; exact sl_15_6) (forall_cons (fun _ h => by cases h; exact sl_15_7) (forall_cons (fun _ h => by cases h; exact sl_15_8) (forall_cons (fun _ h => by cases h; exact sl_15_9) (fun _ h => (List.not_mem_nil h).elim)))))))))))
def ps_15 : BT (Option PoolSpec) := btOfList 4 [q 8 [],q 0 [],q 9 [],q 1 [],q 2 [],q 3 [],q 6 [],q 4 [],q 7 [],q 5 []]
def B_15_4 : BT (List (List Nat)) := BT.empty
lemma B_15_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_15 4 xs.toFinset) B_15_4 := .empty
def U_15_5 : List Nat := (r 0 6)
def P_15_5 : BT (Option BoundPool) := buildPoolsSubBT 4 W_15 r_15 S_15 ps_15 U_15_5
def N_15_5 : List NodeSpec := [e5 [9] (r 0 4),([1,2,3,5,4,10],[4,5],[]),e5 [6] [],e5 [8] []]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_15_5 : checkNodesBT W_15 g_15 F_15 P_15_5 A_15 B_15_4 5 N_15_5 = true := by decide +kernel
def B_15_5 : BT (List (List Nat)) := buildBucketsBT W_15 N_15_5
set_option maxRecDepth 500000 in
lemma B_15_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_15 5 xs.toFinset) B_15_5 :=
  buildBucketsBT_sound (by decide) gp_15 W_15_ok (buildPoolsSubBT_sound S_15_ok) A_15_ok B_15_4_ok C_15_5
def U_15_6 : List Nat := (r 5 4)
def P_15_6 : BT (Option BoundPool) := buildPoolsSubBT 4 W_15 r_15 S_15 ps_15 U_15_6
def N_15_6 : List NodeSpec := [u5 [5] [7,6,5],u5 [7] [6,7,8],e5 [11] [6,7,8]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_15_6 : checkNodesBT W_15 g_15 F_15 P_15_6 A_15 B_15_5 6 N_15_6 = true := by decide +kernel
def B_15_6 : BT (List (List Nat)) := buildBucketsBT W_15 N_15_6
set_option maxRecDepth 500000 in
lemma B_15_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_15 6 xs.toFinset) B_15_6 :=
  buildBucketsBT_sound (by decide) gp_15 W_15_ok (buildPoolsSubBT_sound S_15_ok) A_15_ok B_15_5_ok C_15_6
def U_15_7 : List Nat := ([0,2]++r 6 4)
def P_15_7 : BT (Option BoundPool) := buildPoolsSubBT 4 W_15 r_15 S_15 ps_15 U_15_7
def N_15_7 : List NodeSpec := [a5 [] [9,6,7,0,2,8] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_15_7 : checkNodesBT W_15 g_15 F_15 P_15_7 A_15 B_15_6 7 N_15_7 = true := by decide +kernel
def B_15_7 : BT (List (List Nat)) := buildBucketsBT W_15 N_15_7
set_option maxRecDepth 500000 in
lemma B_15_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_15 7 xs.toFinset) B_15_7 :=
  buildBucketsBT_sound (by decide) gp_15 W_15_ok (buildPoolsSubBT_sound S_15_ok) A_15_ok B_15_6_ok C_15_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_15_ok : forestRootCheck r_15 g_15 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,5,13),(VAR 4,3,19)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_15_in : bucketContainsBT B_15_7 r_15 = true := by decide +kernel
lemma low_15 : Lower r_15 g_15 8 := lower_of_forestBT root_15_ok B_15_7_ok root_15_in
def g_16 := 0xfec0fec0fec0fec0
def r_16 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_16 : Lower r_16 g_16 5 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,8,9)]) (by decide +kernel) hc
def g_17 := 0xfffefc80fffefc80
def r_17 : List Nat := varsOf 31
def p_17 : List Nat := [7,7,7,10,10,11,11,12,12,13,13,14,17,17,18,18,19,20,20,21,22,24,24,25]
def q_17 : List Nat := [6,5,3,8,2,9,3,8,4,9,5,6,16,1,16,2,3,16,4,5,6,16,8,9]
def F_17 : Nat := fullMask 24
set_option maxHeartbeats 0 in
lemma gp_17 : goodPairs g_17 p_17 q_17 := goodPairs_of (by decide +kernel)
def W_17 : BT Decor := buildWiresBT 4 (mkBase p_17 q_17 r_17) [(1,1,2),(1,5,4),(3,3,6),(1,1,4),(3,2,8),(2,5,4),(1,2,4)]
lemma W_17_ok : btAll (fun x => faithful p_17 q_17 x ∧ x.1 < 2^64) W_17 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_17 : List (List (Nat × Nat)) := [[],[(1,2)]]
def A_17 : BT (List (Nat × Nat)) := btOfList 1 al_17
set_option maxHeartbeats 0 in
lemma A_17_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_17 = g_17) A_17 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_17_0 : Slice r_17 g_17 (subcubeFast 8 0) 6 := by
  have hc : Lower (varsOf 23) 0xfefe8080fefe8080 6 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_1 : Slice r_17 g_17 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) 0xfffffcc0fffffcc0 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_2 : Slice r_17 g_17 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) 0xfffaf000fffaf000 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_16
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_3 : Slice r_17 g_17 (subcubeFast 16 0) 5 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_8
set_option maxHeartbeats 0 in
lemma sl_17_4 : Slice r_17 g_17 (subcubeFast 5 0) 4 := by
  have hc : Lower (varsOf 26) 0xffcccc00ffcccc00 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 5) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_5 : Slice r_17 g_17 (subcubeFast 16 1) 4 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_6 : Slice r_17 g_17 (subcubeFast 3 0) 4 := by
  have hc : Lower (varsOf 28) 0xfff0f000fff0f000 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 3) (o := 0) (by decide +kernel) hc
def S_17 : BT (Option (Nat × Nat)) := btOfList 3 [some (subcubeFast 8 0,6),some (subcubeFast 0 1,5),some (subcubeFast 2 0,5),some (subcubeFast 16 0,5),some (subcubeFast 5 0,4),some (subcubeFast 16 1,4),some (subcubeFast 3 0,4)]
lemma S_17_ok : btAll (fun o => ∀ p, o = some p → Slice r_17 g_17 p.1 p.2) S_17 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_17_0) (forall_cons (fun _ h => by cases h; exact sl_17_1) (forall_cons (fun _ h => by cases h; exact sl_17_2) (forall_cons (fun _ h => by cases h; exact sl_17_3) (forall_cons (fun _ h => by cases h; exact sl_17_4) (forall_cons (fun _ h => by cases h; exact sl_17_5) (forall_cons (fun _ h => by cases h; exact sl_17_6) (fun _ h => (List.not_mem_nil h).elim))))))))
def ps_17 : BT (Option PoolSpec) := btOfList 4 [q 6 [],q 1 [],q 0 [],q 3 [],q 5 [],q 0 [16389],q 4 [],q 0 [8197],q 2 []]
def B_17_3 : BT (List (List Nat)) := BT.empty
lemma B_17_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 3 xs.toFinset) B_17_3 := .empty
def U_17_4 : List Nat := []
def P_17_4 : BT (Option BoundPool) := buildPoolsSubBT 4 W_17 r_17 S_17 ps_17 U_17_4
def N_17_4 : List NodeSpec := [([7,0,1,2,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_4 : checkNodesBT W_17 g_17 F_17 P_17_4 A_17 B_17_3 4 N_17_4 = true := by decide +kernel
def B_17_4 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_4
set_option maxRecDepth 500000 in
lemma B_17_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 4 xs.toFinset) B_17_4 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_3_ok C_17_4
def U_17_5 : List Nat := (r 0 4)
def P_17_5 : BT (Option BoundPool) := buildPoolsSubBT 4 W_17 r_17 S_17 ps_17 U_17_5
def N_17_5 : List NodeSpec := [u5 [6] [0,1,2],([0,1,5,3,4,11],[0,3],[]),e5 [9] [],e5 [10] []]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_5 : checkNodesBT W_17 g_17 F_17 P_17_5 A_17 B_17_4 5 N_17_5 = true := by decide +kernel
def B_17_5 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_5
set_option maxRecDepth 500000 in
lemma B_17_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 5 xs.toFinset) B_17_5 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_4_ok C_17_5
def U_17_6 : List Nat := ([0]++r 3 6)
def P_17_6 : BT (Option BoundPool) := buildPoolsSubBT 4 W_17 r_17 S_17 ps_17 U_17_6
def N_17_6 : List NodeSpec := [a5 [8] [0,4,5,6] [0,1],a5 [5] [6,7,8,3] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_6 : checkNodesBT W_17 g_17 F_17 P_17_6 A_17 B_17_5 6 N_17_6 = true := by decide +kernel
def B_17_6 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_6
set_option maxRecDepth 500000 in
lemma B_17_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 6 xs.toFinset) B_17_6 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_5_ok C_17_6
def U_17_7 : List Nat := [1,2,3,6,8]
def P_17_7 : BT (Option BoundPool) := buildPoolsSubBT 4 W_17 r_17 S_17 ps_17 U_17_7
def N_17_7 : List NodeSpec := [a5 [] [2,3,1,8,6] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_7 : checkNodesBT W_17 g_17 F_17 P_17_7 A_17 B_17_6 7 N_17_7 = true := by decide +kernel
def B_17_7 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_7
set_option maxRecDepth 500000 in
lemma B_17_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 7 xs.toFinset) B_17_7 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_6_ok C_17_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_17_ok : forestRootCheck r_17 g_17 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,2,10),(VAR 4,1,17)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_17_in : bucketContainsBT B_17_7 r_17 = true := by decide +kernel
lemma low_17 : Lower r_17 g_17 8 := lower_of_forestBT root_17_ok B_17_7_ok root_17_in
def g_18 := 0x2222222222222222
def r_18 : List Nat := varsOf 3
set_option maxHeartbeats 0 in
lemma low_18 : Lower r_18 g_18 1 := count_of (essPairs := [(VAR 0,0,1),(VAR 1,1,3)]) (by decide +kernel)
def g_19 := 0x8e8e8e8e8e8e8e8e
def r_19 : List Nat := varsOf 7
def p_19 : List Nat := [1,2,7,7]
def q_19 : List Nat := [0,0,6,5]
def F_19 : Nat := fullMask 4
set_option maxHeartbeats 0 in
lemma gp_19 : goodPairs g_19 p_19 q_19 := goodPairs_of (by decide +kernel)
def W_19 : BT Decor := buildWiresBT 2 (mkBase p_19 q_19 r_19) []
lemma W_19_ok : btAll (fun x => faithful p_19 q_19 x ∧ x.1 < 2^64) W_19 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_19 : List (List (Nat × Nat)) := [[]]
def A_19 : BT (List (Nat × Nat)) := btOfList 1 al_19
set_option maxHeartbeats 0 in
lemma A_19_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_19 = g_19) A_19 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_19_0 : Slice r_19 g_19 (subcubeFast 1 0) 1 := by
  have hc : Lower (varsOf 6) 0xc0c0c0c0c0c0c0c 1 := carry_of (swaps := [(0,2),(1,2)]) (by decide +kernel) low_18
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_19_1 : Slice r_19 g_19 (subcubeFast 0 1) 1 := by
  have hc : Lower (varsOf 6) 0x3030303030303030 1 := carry_of (swaps := [(0,2)]) (by decide +kernel) low_18
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_19_2 : Slice r_19 g_19 (subcubeFast 2 0) 1 := by
  have hc : Lower (varsOf 5) 0xa0a0a0a0a0a0a0a 1 := carry_of (swaps := [(1,2)]) (by decide +kernel) low_18
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_19_3 : Slice r_19 g_19 (subcubeFast 0 2) 1 := by
  have hc : Lower (varsOf 5) 0x5050505050505050 1 := carry_of (swaps := [(0,1),(1,2)]) (by decide +kernel) low_18
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
def S_19 : BT (Option (Nat × Nat)) := btOfList 2 [some (subcubeFast 1 0,1),some (subcubeFast 0 1,1),some (subcubeFast 2 0,1),some (subcubeFast 0 2,1)]
lemma S_19_ok : btAll (fun o => ∀ p, o = some p → Slice r_19 g_19 p.1 p.2) S_19 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_19_0) (forall_cons (fun _ h => by cases h; exact sl_19_1) (forall_cons (fun _ h => by cases h; exact sl_19_2) (forall_cons (fun _ h => by cases h; exact sl_19_3) (fun _ h => (List.not_mem_nil h).elim)))))
def ps_19 : BT (Option PoolSpec) := btOfList 2 [q 0 [],q 1 [],q 2 [],q 3 []]
def B_19_2 : BT (List (List Nat)) := BT.empty
lemma B_19_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_19 2 xs.toFinset) B_19_2 := .empty
def U_19_3 : List Nat := (r 0 4)
def P_19_3 : BT (Option BoundPool) := buildPoolsSubBT 2 W_19 r_19 S_19 ps_19 U_19_3
def N_19_3 : List NodeSpec := [([0,1,2],(r 0 4),[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_19_3 : checkNodesBT W_19 g_19 F_19 P_19_3 A_19 B_19_2 3 N_19_3 = true := by decide +kernel
def B_19_3 : BT (List (List Nat)) := buildBucketsBT W_19 N_19_3
set_option maxRecDepth 500000 in
lemma B_19_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_19 3 xs.toFinset) B_19_3 :=
  buildBucketsBT_sound (by decide) gp_19 W_19_ok (buildPoolsSubBT_sound S_19_ok) A_19_ok B_19_2_ok C_19_3
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_19_ok : forestRootCheck r_19 g_19 [(VAR 0,0,1),(VAR 1,0,2),(VAR 2,1,5)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_19_in : bucketContainsBT B_19_3 r_19 = true := by decide +kernel
lemma low_19 : Lower r_19 g_19 4 := lower_of_forestBT root_19_ok B_19_3_ok root_19_in
def g_20 := 0x202020202020202
def r_20 : List Nat := varsOf 7
set_option maxHeartbeats 0 in
lemma low_20 : Lower r_20 g_20 2 := count_of (essPairs := [(VAR 0,0,1),(VAR 1,1,3),(VAR 2,1,5)]) (by decide +kernel)
def g_21 := 0xe8fee8fee8fee8fe
def r_21 : List Nat := varsOf 15
def p_21 : List Nat := [1,2,4,11,11,13,13,14,14]
def q_21 : List Nat := [0,0,0,10,9,12,9,12,10]
def F_21 : Nat := fullMask 9
set_option maxHeartbeats 0 in
lemma gp_21 : goodPairs g_21 p_21 q_21 := goodPairs_of (by decide +kernel)
def W_21 : BT Decor := buildWiresBT 5 (mkBase p_21 q_21 r_21) [(3,0,3),(1,2,1),(3,4,5),(1,0,2),(1,0,1),(0,8,3),(2,5,0),(3,10,3),(3,2,3),(3,8,3),(1,13,2),(1,2,3),(0,8,15),(0,7,3),(2,8,3),(1,18,2),(1,12,0),(3,2,8),(3,1,3),(1,8,2),(0,23,3),(1,0,3),(3,2,25),(3,5,3)]
lemma W_21_ok : btAll (fun x => faithful p_21 q_21 x ∧ x.1 < 2^64) W_21 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_21 : List (List (Nat × Nat)) := [[],[(1,2)],[(0,1)],[(0,2),(1,2)],[(0,1),(1,2)]]
def A_21 : BT (List (Nat × Nat)) := btOfList 3 al_21
set_option maxHeartbeats 0 in
lemma A_21_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_21 = g_21) A_21 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_21_0 : Slice r_21 g_21 (subcubeFast 1 0) 4 := by
  have hc : Lower (varsOf 14) 0xc0fcc0fcc0fcc0fc 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_19
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_1 : Slice r_21 g_21 (subcubeFast 2 0) 4 := by
  have hc : Lower (varsOf 13) 0xa0faa0faa0faa0fa 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_19
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_2 : Slice r_21 g_21 (subcubeFast 4 0) 4 := by
  have hc : Lower (varsOf 11) 0x88ee88ee88ee88ee 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_19
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_3 : Slice r_21 g_21 (subcubeFast 0 8) 4 := by
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_21_4 : Slice r_21 g_21 (subcubeFast 0 1) 2 := by
  have hc : Lower (varsOf 14) 0x300030003000300 2 := carry_of (swaps := [(0,3)]) (by decide +kernel) low_20
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_5 : Slice r_21 g_21 (subcubeFast 0 2) 2 := by
  have hc : Lower (varsOf 13) 0x500050005000500 2 := carry_of (swaps := [(0,1),(1,3)]) (by decide +kernel) low_20
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_6 : Slice r_21 g_21 (subcubeFast 0 4) 2 := by
  have hc : Lower (varsOf 11) 0x1100110011001100 2 := carry_of (swaps := [(0,1),(1,2),(2,3)]) (by decide +kernel) low_20
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
def S_21 : BT (Option (Nat × Nat)) := btOfList 3 [some (subcubeFast 1 0,4),some (subcubeFast 2 0,4),some (subcubeFast 4 0,4),some (subcubeFast 0 8,4),some (subcubeFast 0 1,2),some (subcubeFast 0 2,2),some (subcubeFast 0 4,2)]
lemma S_21_ok : btAll (fun o => ∀ p, o = some p → Slice r_21 g_21 p.1 p.2) S_21 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_21_0) (forall_cons (fun _ h => by cases h; exact sl_21_1) (forall_cons (fun _ h => by cases h; exact sl_21_2) (forall_cons (fun _ h => by cases h; exact sl_21_3) (forall_cons (fun _ h => by cases h; exact sl_21_4) (forall_cons (fun _ h => by cases h; exact sl_21_5) (forall_cons (fun _ h => by cases h; exact sl_21_6) (fun _ h => (List.not_mem_nil h).elim))))))))
def ps_21 : BT (Option PoolSpec) := btOfList 5 [q 4 [4105],q 4 [],q 4 [8197],q 1 [],q 0 [12322,8265],q 0 [],q 5 [9],q 3 [],q 2 [],q 1 [12291,20499],q 5 [],q 6 [],q 0 [12299],q 2 [12289],q 0 [4105],q 1 [9],q 0 [8226],q 1 [8226],q 2 [4097],q 2 [49],q 0 [8225],q 1 [8225],q 1 [12311],q 2 [12311],q 0 [12320],q 1 [12320],q 0 [12322],q 0 [12297],q 1 [12299],q 1 [12289]]
def B_21_1 : BT (List (List Nat)) := BT.empty
lemma B_21_1_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_21 1 xs.toFinset) B_21_1 := .empty
def U_21_2 : List Nat := [0]
def P_21_2 : BT (Option BoundPool) := buildPoolsSubBT 5 W_21 r_21 S_21 ps_21 U_21_2
def N_21_2 : List NodeSpec := [([6,1,7],[0],[]),([9,7,5],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_21_2 : checkNodesBT W_21 g_21 F_21 P_21_2 A_21 B_21_1 2 N_21_2 = true := by decide +kernel
def B_21_2 : BT (List (List Nat)) := buildBucketsBT W_21 N_21_2
set_option maxRecDepth 500000 in
lemma B_21_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_21 2 xs.toFinset) B_21_2 :=
  buildBucketsBT_sound (by decide) gp_21 W_21_ok (buildPoolsSubBT_sound S_21_ok) A_21_ok B_21_1_ok C_21_2
def U_21_3 : List Nat := (r 0 10)
def P_21_3 : BT (Option BoundPool) := buildPoolsSubBT 5 W_21 r_21 S_21 ps_21 U_21_3
def N_21_3 : List NodeSpec := [([0,20,1,5],[0],[]),([0,11,1,2],[1],[]),([12,0,8,5],[2],[4]),([0,1,17,5],[3],[1]),([0,1,8,19],[4],[]),([8,7,5,3],[3,5,0,6],[0,1,3]),([12,22,0,5],[3,8],[]),([6,0,1,2],[7,8,9],[0,1]),([0,1,14,3],[],[]),([0,1,16,2],[],[]),([21,22,0,2],[],[]),([0,1,14],[],[]),([0,1,2,24],[],[]),([0,1,9,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_21_3 : checkNodesBT W_21 g_21 F_21 P_21_3 A_21 B_21_2 3 N_21_3 = true := by decide +kernel
def B_21_3 : BT (List (List Nat)) := buildBucketsBT W_21 N_21_3
set_option maxRecDepth 500000 in
lemma B_21_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_21 3 xs.toFinset) B_21_3 :=
  buildBucketsBT_sound (by decide) gp_21 W_21_ok (buildPoolsSubBT_sound S_21_ok) A_21_ok B_21_2_ok C_21_3
def U_21_4 : List Nat := ([1,3,5,7,8]++r 10 18)
def P_21_4 : BT (Option BoundPool) := buildPoolsSubBT 5 W_21 r_21 S_21 ps_21 U_21_4
def N_21_4 : List NodeSpec := [([0,1,9,2,3],[1],[]),([27,0,1,2,3],[5],[3]),([12,22,0,1,2],[10,3,11,8],[0]),([12,0,20,1,2],[11,5,8],[]),([12,0,1,8,2],[1,3,10,11,12,8],[0,2,4]),([12,0,1,7,3],[8,12,7],[2]),([12,0,1,7],[11,12],[1,2]),([0,20,1,2,3],[12,1],[]),([26,0,1,2],[3,10,11,13],[]),([0,1,7,5,3],[14,15,11],[0,1,2,3]),([21,0,1,2,3],[11,7,16,17,18],[0,2,4]),([0,20,1,2],[1,12,3,10,19],[0]),([0,1,2,23,3],[20,1,21,10,18,11,7],[0]),([27,0,1,2],[5,10,1,11,22,23],[3]),([0,1,9,8,2],[24,3,7],[]),([0,1,9,2],[24,25,8,11],[1,3]),([18,0,1,8,2],[3,18,26],[0]),([0,1,8,2,15],[27,1,3,10,8,11],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_21_4 : checkNodesBT W_21 g_21 F_21 P_21_4 A_21 B_21_3 4 N_21_4 = true := by decide +kernel
def B_21_4 : BT (List (List Nat)) := buildBucketsBT W_21 N_21_4
set_option maxRecDepth 500000 in
lemma B_21_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_21 4 xs.toFinset) B_21_4 :=
  buildBucketsBT_sound (by decide) gp_21 W_21_ok (buildPoolsSubBT_sound S_21_ok) A_21_ok B_21_3_ok C_21_4
def U_21_5 : List Nat := [1,3,5,7,8,11,12,13,18,28,29]
def P_21_5 : BT (Option BoundPool) := buildPoolsSubBT 5 W_21 r_21 S_21 ps_21 U_21_5
def N_21_5 : List NodeSpec := [([0,1,8,2,3],[5,3,7,1,18],[0,1,3,4]),([12,0,1,2,3],[7,8,12,28],[0,2]),([12,0,1,2],[11,12,28,7,8],[0,2]),([0,1,2,25],[5,7,29,13],[0,1,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_21_5 : checkNodesBT W_21 g_21 F_21 P_21_5 A_21 B_21_4 5 N_21_5 = true := by decide +kernel
def B_21_5 : BT (List (List Nat)) := buildBucketsBT W_21 N_21_5
set_option maxRecDepth 500000 in
lemma B_21_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_21 5 xs.toFinset) B_21_5 :=
  buildBucketsBT_sound (by decide) gp_21 W_21_ok (buildPoolsSubBT_sound S_21_ok) A_21_ok B_21_4_ok C_21_5
def U_21_6 : List Nat := [3,5,7,8]
def P_21_6 : BT (Option BoundPool) := buildPoolsSubBT 5 W_21 r_21 S_21 ps_21 U_21_6
def N_21_6 : List NodeSpec := [([0,1,2,3],[5,3,8,7],[0,1,2,3,4])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_21_6 : checkNodesBT W_21 g_21 F_21 P_21_6 A_21 B_21_5 6 N_21_6 = true := by decide +kernel
def B_21_6 : BT (List (List Nat)) := buildBucketsBT W_21 N_21_6
set_option maxRecDepth 500000 in
lemma B_21_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_21 6 xs.toFinset) B_21_6 :=
  buildBucketsBT_sound (by decide) gp_21 W_21_ok (buildPoolsSubBT_sound S_21_ok) A_21_ok B_21_5_ok C_21_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_21_ok : forestRootCheck r_21 g_21 [(VAR 0,0,1),(VAR 1,0,2),(VAR 2,0,4),(VAR 3,1,9)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_21_in : bucketContainsBT B_21_6 r_21 = true := by decide +kernel
lemma low_21 : Lower r_21 g_21 7 := lower_of_forestBT root_21_ok B_21_6_ok root_21_in
def g_22 := 0x808080808080808
def r_22 : List Nat := varsOf 7
set_option maxHeartbeats 0 in
lemma low_22 : Lower r_22 g_22 2 := count_of (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,3,7)]) (by decide +kernel)
def g_23 := 0x80e880e880e880e8
def r_23 : List Nat := varsOf 15
def p_23 : List Nat := [3,3,5,5,6,6,15,15,15]
def q_23 : List Nat := [2,1,4,1,4,2,14,13,11]
def F_23 : Nat := fullMask 9
set_option maxHeartbeats 0 in
lemma gp_23 : goodPairs g_23 p_23 q_23 := goodPairs_of (by decide +kernel)
def W_23 : BT Decor := buildWiresBT 5 (mkBase p_23 q_23 r_23) [(0,0,1),(2,1,3),(0,0,2),(1,5,6),(0,1,2),(1,8,3),(2,2,3),(1,10,4),(2,0,3),(3,6,1),(3,8,0),(1,14,3),(2,8,3),(3,16,0),(0,0,3),(1,8,18),(0,4,2),(1,20,3),(1,4,3),(3,8,3),(3,23,0),(3,5,2),(3,10,0),(0,2,3),(3,27,0),(3,12,1),(2,4,3)]
lemma W_23_ok : btAll (fun x => faithful p_23 q_23 x ∧ x.1 < 2^64) W_23 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_23 : List (List (Nat × Nat)) := [[],[(1,2)],[(0,1)],[(0,2),(1,2)],[(0,1),(1,2)],[(0,2)]]
def A_23 : BT (List (Nat × Nat)) := btOfList 3 al_23
set_option maxHeartbeats 0 in
lemma A_23_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_23 = g_23) A_23 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_23_0 : Slice r_23 g_23 (subcubeFast 0 1) 4 := by
  have hc : Lower (varsOf 14) 0xc0fcc0fcc0fcc0fc 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_19
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_1 : Slice r_23 g_23 (subcubeFast 0 2) 4 := by
  have hc : Lower (varsOf 13) 0xa0faa0faa0faa0fa 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_19
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_2 : Slice r_23 g_23 (subcubeFast 0 4) 4 := by
  have hc : Lower (varsOf 11) 0x88ee88ee88ee88ee 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_19
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_3 : Slice r_23 g_23 (subcubeFast 8 0) 4 := by
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_23_4 : Slice r_23 g_23 (subcubeFast 1 0) 2 := by
  have hc : Lower (varsOf 14) 0xc000c000c000c0 2 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_22
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_5 : Slice r_23 g_23 (subcubeFast 2 0) 2 := by
  have hc : Lower (varsOf 13) 0xa000a000a000a0 2 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_22
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_6 : Slice r_23 g_23 (subcubeFast 4 0) 2 := by
  have hc : Lower (varsOf 11) 0x88008800880088 2 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_22
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
def S_23 : BT (Option (Nat × Nat)) := btOfList 3 [some (subcubeFast 0 1,4),some (subcubeFast 0 2,4),some (subcubeFast 0 4,4),some (subcubeFast 8 0,4),some (subcubeFast 1 0,2),some (subcubeFast 2 0,2),some (subcubeFast 4 0,2)]
lemma S_23_ok : btAll (fun o => ∀ p, o = some p → Slice r_23 g_23 p.1 p.2) S_23 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_23_0) (forall_cons (fun _ h => by cases h; exact sl_23_1) (forall_cons (fun _ h => by cases h; exact sl_23_2) (forall_cons (fun _ h => by cases h; exact sl_23_3) (forall_cons (fun _ h => by cases h; exact sl_23_4) (forall_cons (fun _ h => by cases h; exact sl_23_5) (forall_cons (fun _ h => by cases h; exact sl_23_6) (fun _ h => (List.not_mem_nil h).elim))))))))
def ps_23 : BT (Option PoolSpec) := btOfList 5 [q 0 [],q 1 [],q 3 [],q 0 [12298,16425],q 4 [],q 2 [],q 4 [8196],q 5 [8192],q 1 [12323,95],q 6 [4],q 5 [],q 0 [12298],q 2 [43],q 0 [12296],q 0 [8208],q 1 [8208],q 2 [4096],q 6 [],q 0 [8196],q 1 [12323],q 0 [12305],q 1 [12305],q 1 [35],q 2 [35],q 1 [12290],q 0 [12306],q 1 [12306],q 1 [8192],q 2 [12290],q 1 [12288],q 2 [12288]]
def B_23_1 : BT (List (List Nat)) := BT.empty
lemma B_23_1_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 1 xs.toFinset) B_23_1 := .empty
def U_23_2 : List Nat := [0]
def P_23_2 : BT (Option BoundPool) := buildPoolsSubBT 5 W_23 r_23 S_23 ps_23 U_23_2
def N_23_2 : List NodeSpec := [([4,7,2],[0],[]),([4,6,9],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_2 : checkNodesBT W_23 g_23 F_23 P_23_2 A_23 B_23_1 2 N_23_2 = true := by decide +kernel
def B_23_2 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_2
set_option maxRecDepth 500000 in
lemma B_23_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 2 xs.toFinset) B_23_2 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok (buildPoolsSubBT_sound S_23_ok) A_23_ok B_23_1_ok C_23_2
def U_23_3 : List Nat := (r 0 10)
def P_23_3 : BT (Option BoundPool) := buildPoolsSubBT 5 W_23 r_23 S_23 ps_23 U_23_3
def N_23_3 : List NodeSpec := [([4,0,2,9],[0],[0]),([12,5,4,2],[0,2],[]),([11,0,1,2],[1,2,3],[1,3]),([0,1,2,15],[4],[]),([12,4,8,2],[6],[2]),([4,6,8,3],[5,6,0,7],[0,2,4]),([24,8,1,2],[8],[]),([4,0,25,2],[9],[]),([12,13,1,2],[],[]),([17,1,2],[],[]),([0,1,19,2],[],[]),([0,1,2,21],[],[]),([17,1,2,3],[],[]),([0,1,2,22],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_3 : checkNodesBT W_23 g_23 F_23 P_23_3 A_23 B_23_2 3 N_23_3 = true := by decide +kernel
def B_23_3 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_3
set_option maxRecDepth 500000 in
lemma B_23_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 3 xs.toFinset) B_23_3 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok (buildPoolsSubBT_sound S_23_ok) A_23_ok B_23_2_ok C_23_3
def U_23_4 : List Nat := ([0,1,2,4,5]++r 10 18)
def P_23_4 : BT (Option BoundPool) := buildPoolsSubBT 5 W_23 r_23 S_23 ps_23 U_23_4
def N_23_4 : List NodeSpec := [([12,0,29,1,2],[1,4,0],[]),([0,1,2,3,22],[4],[]),([30,0,1,2,3],[5],[0,4]),([12,5,0,1,2],[4,0,1,10],[0]),([26,0,1,2,3],[11,4],[]),([26,0,1,2],[4,1,10,11,12],[3]),([28,0,1,2],[4,1,10,13],[]),([20,0,1,2,3],[2,4,14,15,10,16,17],[0]),([4,0,1,27,2],[4,5,17,13,1,10],[4]),([23,0,8,1,2],[18,5,19],[0,3]),([4,0,1,2,22],[2,20,4],[]),([0,1,2,22],[20,21,17,5],[4,5]),([14,0,1,2,3],[2,4,18,22,23],[0,2,4]),([12,4,1,2,3],[2,0,24],[0]),([12,0,8,1,2],[4,10,17,5,0,24],[0,1,3]),([12,4,1,2],[4,24],[0,1,2]),([30,0,1,2],[4,10,5,17,25,26],[4]),([4,6,1,2,3],[4,27,16],[0,2,4])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_4 : checkNodesBT W_23 g_23 F_23 P_23_4 A_23 B_23_3 4 N_23_4 = true := by decide +kernel
def B_23_4 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_4
set_option maxRecDepth 500000 in
lemma B_23_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 4 xs.toFinset) B_23_4 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok (buildPoolsSubBT_sound S_23_ok) A_23_ok B_23_3_ok C_23_4
def U_23_5 : List Nat := [0,1,2,4,16,24,28,29,30]
def P_23_5 : BT (Option BoundPool) := buildPoolsSubBT 5 W_23 r_23 S_23 ps_23 U_23_5
def N_23_5 : List NodeSpec := [([4,0,1,2,3],[1,0,2,4,16],[0,2,4]),([12,0,1,2,3],[2,0,24,28],[0,1,3,5]),([12,0,1,2],[2,4,24,28,0],[0,1,3,5]),([18,0,1,2],[2,0,29,30],[3,5])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_5 : checkNodesBT W_23 g_23 F_23 P_23_5 A_23 B_23_4 5 N_23_5 = true := by decide +kernel
def B_23_5 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_5
set_option maxRecDepth 500000 in
lemma B_23_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 5 xs.toFinset) B_23_5 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok (buildPoolsSubBT_sound S_23_ok) A_23_ok B_23_4_ok C_23_5
def U_23_6 : List Nat := [0,1,2,5]
def P_23_6 : BT (Option BoundPool) := buildPoolsSubBT 5 W_23 r_23 S_23 ps_23 U_23_6
def N_23_6 : List NodeSpec := [([0,1,2,3],[0,1,5,2],[0,1,2,3,4])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_6 : checkNodesBT W_23 g_23 F_23 P_23_6 A_23 B_23_5 6 N_23_6 = true := by decide +kernel
def B_23_6 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_6
set_option maxRecDepth 500000 in
lemma B_23_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 6 xs.toFinset) B_23_6 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok (buildPoolsSubBT_sound S_23_ok) A_23_ok B_23_5_ok C_23_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_23_ok : forestRootCheck r_23 g_23 [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 3,3,11)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_23_in : bucketContainsBT B_23_6 r_23 = true := by decide +kernel
lemma low_23 : Lower r_23 g_23 7 := lower_of_forestBT root_23_ok B_23_6_ok root_23_in
def g_24 := 0xacacacacacacacac
def r_24 : List Nat := varsOf 7
def p_24 : List Nat := [2,3,5,5,7]
def q_24 : List Nat := [0,1,4,1,6]
def F_24 : Nat := fullMask 5
set_option maxHeartbeats 0 in
lemma gp_24 : goodPairs g_24 p_24 q_24 := goodPairs_of (by decide +kernel)
def W_24 : BT Decor := buildWiresBT 2 (mkBase p_24 q_24 r_24) []
lemma W_24_ok : btAll (fun x => faithful p_24 q_24 x ∧ x.1 < 2^64) W_24 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_24 : List (List (Nat × Nat)) := [[]]
def A_24 : BT (List (Nat × Nat)) := btOfList 1 al_24
set_option maxHeartbeats 0 in
lemma A_24_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_24 = g_24) A_24 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_24_0 : Slice r_24 g_24 (subcubeFast 1 0) 1 := by
  have hc : Lower (varsOf 6) 0xc0c0c0c0c0c0c0c 1 := carry_of (swaps := [(0,2),(1,2)]) (by decide +kernel) low_18
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_1 : Slice r_24 g_24 (subcubeFast 0 2) 1 := by
  have hc : Lower (varsOf 5) 0x5050505050505050 1 := carry_of (swaps := [(0,1),(1,2)]) (by decide +kernel) low_18
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
def S_24 : BT (Option (Nat × Nat)) := btOfList 1 [some (subcubeFast 1 0,1),some (subcubeFast 0 2,1)]
lemma S_24_ok : btAll (fun o => ∀ p, o = some p → Slice r_24 g_24 p.1 p.2) S_24 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_24_0) (forall_cons (fun _ h => by cases h; exact sl_24_1) (fun _ h => (List.not_mem_nil h).elim)))
def ps_24 : BT (Option PoolSpec) := btOfList 1 [q 0 [],q 1 []]
def B_24_1 : BT (List (List Nat)) := BT.empty
lemma B_24_1_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_24 1 xs.toFinset) B_24_1 := .empty
def U_24_2 : List Nat := [0,1]
def P_24_2 : BT (Option BoundPool) := buildPoolsSubBT 1 W_24 r_24 S_24 ps_24 U_24_2
def N_24_2 : List NodeSpec := [([0,1,2],[0,1],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_24_2 : checkNodesBT W_24 g_24 F_24 P_24_2 A_24 B_24_1 2 N_24_2 = true := by decide +kernel
def B_24_2 : BT (List (List Nat)) := buildBucketsBT W_24 N_24_2
set_option maxRecDepth 500000 in
lemma B_24_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_24 2 xs.toFinset) B_24_2 :=
  buildBucketsBT_sound (by decide) gp_24 W_24_ok (buildPoolsSubBT_sound S_24_ok) A_24_ok B_24_1_ok C_24_2
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_24_ok : forestRootCheck r_24 g_24 [(VAR 0,4,5),(VAR 1,0,2),(VAR 2,1,5)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_24_in : bucketContainsBT B_24_2 r_24 = true := by decide +kernel
lemma low_24 : Lower r_24 g_24 3 := lower_of_forestBT root_24_ok B_24_2_ok root_24_in
def g_25 := 0xeafceafceafceafc
def r_25 : List Nat := varsOf 15
def p_25 : List Nat := [2,3,4,5,9,9,11,13,14,14]
def q_25 : List Nat := [0,1,0,1,8,1,10,12,12,10]
def F_25 : Nat := fullMask 10
set_option maxHeartbeats 0 in
lemma gp_25 : goodPairs g_25 p_25 q_25 := goodPairs_of (by decide +kernel)
def W_25 : BT Decor := buildWiresBT 4 (mkBase p_25 q_25 r_25) [(3,0,3),(3,1,3),(1,5,2),(1,1,3),(3,4,7),(3,0,7),(3,2,3),(1,1,2)]
lemma W_25_ok : btAll (fun x => faithful p_25 q_25 x ∧ x.1 < 2^64) W_25 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_25 : List (List (Nat × Nat)) := [[],[(1,2)]]
def A_25 : BT (List (Nat × Nat)) := btOfList 1 al_25
set_option maxHeartbeats 0 in
lemma A_25_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_25 = g_25) A_25 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_25_0 : Slice r_25 g_25 (subcubeFast 1 0) 4 := by
  have hc : Lower (varsOf 14) 0xc0fcc0fcc0fcc0fc 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_19
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_25_1 : Slice r_25 g_25 (subcubeFast 2 0) 3 := by
  have hc : Lower (varsOf 13) 0xaaf0aaf0aaf0aaf0 3 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_24
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_25_2 : Slice r_25 g_25 (subcubeFast 4 0) 3 := by
  have hc : Lower (varsOf 11) 0xaaccaaccaaccaacc 3 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_24
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_25_3 : Slice r_25 g_25 (subcubeFast 0 2) 2 := by
  have hc : Lower (varsOf 13) 0x500050005000500 2 := carry_of (swaps := [(0,1),(1,3)]) (by decide +kernel) low_20
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_25_4 : Slice r_25 g_25 (subcubeFast 0 4) 2 := by
  have hc : Lower (varsOf 11) 0x1100110011001100 2 := carry_of (swaps := [(0,1),(1,2),(2,3)]) (by decide +kernel) low_20
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
def S_25 : BT (Option (Nat × Nat)) := btOfList 3 [some (subcubeFast 1 0,4),some (subcubeFast 2 0,3),some (subcubeFast 4 0,3),some (subcubeFast 0 2,2),some (subcubeFast 0 4,2)]
lemma S_25_ok : btAll (fun o => ∀ p, o = some p → Slice r_25 g_25 p.1 p.2) S_25 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_25_0) (forall_cons (fun _ h => by cases h; exact sl_25_1) (forall_cons (fun _ h => by cases h; exact sl_25_2) (forall_cons (fun _ h => by cases h; exact sl_25_3) (forall_cons (fun _ h => by cases h; exact sl_25_4) (fun _ h => (List.not_mem_nil h).elim))))))
def ps_25 : BT (Option PoolSpec) := btOfList 4 [q 0 [12295,8213],q 0 [],q 1 [],q 0 [12299],q 4 [],q 2 [],q 3 [],q 0 [12293],q 0 [8197]]
def B_25_1 : BT (List (List Nat)) := BT.empty
lemma B_25_1_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_25 1 xs.toFinset) B_25_1 := .empty
def U_25_2 : List Nat := []
def P_25_2 : BT (Option BoundPool) := buildPoolsSubBT 4 W_25 r_25 S_25 ps_25 U_25_2
def N_25_2 : List NodeSpec := [([4,1,6],[],[]),([8,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_25_2 : checkNodesBT W_25 g_25 F_25 P_25_2 A_25 B_25_1 2 N_25_2 = true := by decide +kernel
def B_25_2 : BT (List (List Nat)) := buildBucketsBT W_25 N_25_2
set_option maxRecDepth 500000 in
lemma B_25_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_25 2 xs.toFinset) B_25_2 :=
  buildBucketsBT_sound (by decide) gp_25 W_25_ok (buildPoolsSubBT_sound S_25_ok) A_25_ok B_25_1_ok C_25_2
def U_25_3 : List Nat := [0,1]
def P_25_3 : BT (Option BoundPool) := buildPoolsSubBT 4 W_25 r_25 S_25 ps_25 U_25_3
def N_25_3 : List NodeSpec := [([0,1,6,3],[0],[0]),([9,1,2,3],[1],[]),([0,1,6],[],[]),([10,4,1,2],[],[1]),([4,1,2,7],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_25_3 : checkNodesBT W_25 g_25 F_25 P_25_3 A_25 B_25_2 3 N_25_3 = true := by decide +kernel
def B_25_3 : BT (List (List Nat)) := buildBucketsBT W_25 N_25_3
set_option maxRecDepth 500000 in
lemma B_25_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_25 3 xs.toFinset) B_25_3 :=
  buildBucketsBT_sound (by decide) gp_25 W_25_ok (buildPoolsSubBT_sound S_25_ok) A_25_ok B_25_2_ok C_25_3
def U_25_4 : List Nat := (r 1 8)
def P_25_4 : BT (Option BoundPool) := buildPoolsSubBT 4 W_25 r_25 S_25 ps_25 U_25_4
def N_25_4 : List NodeSpec := [([4,1,2,3],[1],[0,1]),([10,0,1,2,3],(r 2 4),[0,1]),([10,0,1,2],[1,4,6,5],[1]),([0,1,2,7],[6,2,1,4],[]),([0,1,2,3,7],[7,2,6],[0]),([0,1,2,11,3],[8,2,6,4],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_25_4 : checkNodesBT W_25 g_25 F_25 P_25_4 A_25 B_25_3 4 N_25_4 = true := by decide +kernel
def B_25_4 : BT (List (List Nat)) := buildBucketsBT W_25 N_25_4
set_option maxRecDepth 500000 in
lemma B_25_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_25 4 xs.toFinset) B_25_4 :=
  buildBucketsBT_sound (by decide) gp_25 W_25_ok (buildPoolsSubBT_sound S_25_ok) A_25_ok B_25_3_ok C_25_4
def U_25_5 : List Nat := [1,2,5]
def P_25_5 : BT (Option BoundPool) := buildPoolsSubBT 4 W_25 r_25 S_25 ps_25 U_25_5
def N_25_5 : List NodeSpec := [([0,1,2,3],[1,2,5],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_25_5 : checkNodesBT W_25 g_25 F_25 P_25_5 A_25 B_25_4 5 N_25_5 = true := by decide +kernel
def B_25_5 : BT (List (List Nat)) := buildBucketsBT W_25 N_25_5
set_option maxRecDepth 500000 in
lemma B_25_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_25 5 xs.toFinset) B_25_5 :=
  buildBucketsBT_sound (by decide) gp_25 W_25_ok (buildPoolsSubBT_sound S_25_ok) A_25_ok B_25_4_ok C_25_5
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_25_ok : forestRootCheck r_25 g_25 [(VAR 0,8,9),(VAR 1,0,2),(VAR 2,0,4),(VAR 3,1,9)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_25_in : bucketContainsBT B_25_5 r_25 = true := by decide +kernel
lemma low_25 : Lower r_25 g_25 6 := lower_of_forestBT root_25_ok B_25_5_ok root_25_in
def g_26 := 0x88e088e088e088e0
def r_26 : List Nat := varsOf 15
def p_26 : List Nat := [5,5,6,6,7,11,11,11,15,15]
def q_26 : List Nat := [4,1,4,2,3,10,9,3,14,13]
def F_26 : Nat := fullMask 10
set_option maxHeartbeats 0 in
lemma gp_26 : goodPairs g_26 p_26 q_26 := goodPairs_of (by decide +kernel)
def W_26 : BT Decor := buildWiresBT 4 (mkBase p_26 q_26 r_26) [(2,2,3),(2,1,3),(3,5,0),(0,0,3),(1,4,7),(2,0,3),(0,1,3),(3,10,2),(0,0,1)]
lemma W_26_ok : btAll (fun x => faithful p_26 q_26 x ∧ x.1 < 2^64) W_26 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_26 : List (List (Nat × Nat)) := [[],[(0,1)]]
def A_26 : BT (List (Nat × Nat)) := btOfList 1 al_26
set_option maxHeartbeats 0 in
lemma A_26_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_26 = g_26) A_26 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_26_0 : Slice r_26 g_26 (subcubeFast 0 4) 4 := by
  have hc : Lower (varsOf 11) 0x88ee88ee88ee88ee 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_19
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_26_1 : Slice r_26 g_26 (subcubeFast 0 1) 3 := by
  have hc : Lower (varsOf 14) 0xccf0ccf0ccf0ccf0 3 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_24
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_26_2 : Slice r_26 g_26 (subcubeFast 0 2) 3 := by
  have hc : Lower (varsOf 13) 0xaaf0aaf0aaf0aaf0 3 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_24
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_26_3 : Slice r_26 g_26 (subcubeFast 1 0) 2 := by
  have hc : Lower (varsOf 14) 0xc000c000c000c0 2 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_22
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_26_4 : Slice r_26 g_26 (subcubeFast 2 0) 2 := by
  have hc : Lower (varsOf 13) 0xa000a000a000a0 2 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_22
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
def S_26 : BT (Option (Nat × Nat)) := btOfList 3 [some (subcubeFast 0 4,4),some (subcubeFast 0 1,3),some (subcubeFast 0 2,3),some (subcubeFast 1 0,2),some (subcubeFast 2 0,2)]
lemma S_26_ok : btAll (fun o => ∀ p, o = some p → Slice r_26 g_26 p.1 p.2) S_26 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_26_0) (forall_cons (fun _ h => by cases h; exact sl_26_1) (forall_cons (fun _ h => by cases h; exact sl_26_2) (forall_cons (fun _ h => by cases h; exact sl_26_3) (forall_cons (fun _ h => by cases h; exact sl_26_4) (fun _ h => (List.not_mem_nil h).elim))))))
def ps_26 : BT (Option PoolSpec) := btOfList 4 [q 0 [12294,23],q 0 [],q 2 [],q 3 [],q 1 [],q 0 [12290],q 4 [],q 0 [12288],q 0 [4096]]
def B_26_1 : BT (List (List Nat)) := BT.empty
lemma B_26_1_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_26 1 xs.toFinset) B_26_1 := .empty
def U_26_2 : List Nat := []
def P_26_2 : BT (Option BoundPool) := buildPoolsSubBT 4 W_26 r_26 S_26 ps_26 U_26_2
def N_26_2 : List NodeSpec := [([4,6,1],[],[]),([0,8,1],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_26_2 : checkNodesBT W_26 g_26 F_26 P_26_2 A_26 B_26_1 2 N_26_2 = true := by decide +kernel
def B_26_2 : BT (List (List Nat)) := buildBucketsBT W_26 N_26_2
set_option maxRecDepth 500000 in
lemma B_26_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_26 2 xs.toFinset) B_26_2 :=
  buildBucketsBT_sound (by decide) gp_26 W_26_ok (buildPoolsSubBT_sound S_26_ok) A_26_ok B_26_1_ok C_26_2
def U_26_3 : List Nat := [0,1]
def P_26_3 : BT (Option BoundPool) := buildPoolsSubBT 4 W_26 r_26 S_26 ps_26 U_26_3
def N_26_3 : List NodeSpec := [([6,1,2,3],[0],[0]),([11,0,1,3],[1],[]),([9,4,0,1],[],[1]),([6,1,2],[],[]),([4,7,0,1],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_26_3 : checkNodesBT W_26 g_26 F_26 P_26_3 A_26 B_26_2 3 N_26_3 = true := by decide +kernel
def B_26_3 : BT (List (List Nat)) := buildBucketsBT W_26 N_26_3
set_option maxRecDepth 500000 in
lemma B_26_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_26 3 xs.toFinset) B_26_3 :=
  buildBucketsBT_sound (by decide) gp_26 W_26_ok (buildPoolsSubBT_sound S_26_ok) A_26_ok B_26_2_ok C_26_3
def U_26_4 : List Nat := (r 1 8)
def P_26_4 : BT (Option BoundPool) := buildPoolsSubBT 4 W_26 r_26 S_26 ps_26 U_26_4
def N_26_4 : List NodeSpec := [([4,0,1,3],[1],[0,1]),([9,0,1,2,3],(r 2 4),[0,1]),([9,0,1,2],[3,6,1,4],[1]),([7,0,1,2],[3,6,1,4],[]),([7,0,1,2,3],[4,3,7],[0,1]),([12,0,1,2,3],[3,4,6,8],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_26_4 : checkNodesBT W_26 g_26 F_26 P_26_4 A_26 B_26_3 4 N_26_4 = true := by decide +kernel
def B_26_4 : BT (List (List Nat)) := buildBucketsBT W_26 N_26_4
set_option maxRecDepth 500000 in
lemma B_26_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_26 4 xs.toFinset) B_26_4 :=
  buildBucketsBT_sound (by decide) gp_26 W_26_ok (buildPoolsSubBT_sound S_26_ok) A_26_ok B_26_3_ok C_26_4
def U_26_5 : List Nat := [1,2,4]
def P_26_5 : BT (Option BoundPool) := buildPoolsSubBT 4 W_26 r_26 S_26 ps_26 U_26_5
def N_26_5 : List NodeSpec := [([0,1,2,3],[4,2,1],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_26_5 : checkNodesBT W_26 g_26 F_26 P_26_5 A_26 B_26_4 5 N_26_5 = true := by decide +kernel
def B_26_5 : BT (List (List Nat)) := buildBucketsBT W_26 N_26_5
set_option maxRecDepth 500000 in
lemma B_26_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_26 5 xs.toFinset) B_26_5 :=
  buildBucketsBT_sound (by decide) gp_26 W_26_ok (buildPoolsSubBT_sound S_26_ok) A_26_ok B_26_4_ok C_26_5
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_26_ok : forestRootCheck r_26 g_26 [(VAR 0,4,5),(VAR 1,4,6),(VAR 2,1,5),(VAR 3,3,11)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_26_in : bucketContainsBT B_26_5 r_26 = true := by decide +kernel
lemma low_26 : Lower r_26 g_26 6 := lower_of_forestBT root_26_ok B_26_5_ok root_26_in
def g_27 := 0xff8eff8eff8eff8e
def r_27 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_27 : Lower r_27 g_27 5 := by
  exact lift_of_f (z := 8) (o := 0) (other := r_19) (G := g_19) (essPairs := [(VAR 3,0,8)]) (by decide +kernel) low_19
def g_28 := 0xff8eac08ff8eac08
def r_28 : List Nat := varsOf 31
def p_28 : List Nat := [3,3,10,10,11,13,13,13,15,15,17,17,18,18,23,23,23,24,24,25,28,28,29,30,30]
def q_28 : List Nat := [2,1,8,2,9,12,9,5,14,7,16,1,16,2,22,21,7,16,8,9,20,12,21,22,14]
def F_28 : Nat := fullMask 25
set_option maxHeartbeats 0 in
lemma gp_28 : goodPairs g_28 p_28 q_28 := goodPairs_of (by decide +kernel)
def W_28 : BT Decor := buildWiresBT 4 (mkBase p_28 q_28 r_28) [(2,2,4),(3,5,1),(2,0,2),(1,7,3),(0,0,2),(1,2,4),(2,0,4)]
lemma W_28_ok : btAll (fun x => faithful p_28 q_28 x ∧ x.1 < 2^64) W_28 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_28 : List (List (Nat × Nat)) := [[]]
def A_28 : BT (List (Nat × Nat)) := btOfList 1 al_28
set_option maxHeartbeats 0 in
lemma A_28_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_28 = g_28) A_28 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_28_0 : Slice r_28 g_28 (subcubeFast 0 2) 7 := by
  have hc : Lower (varsOf 29) 0xffafaf0affafaf0a 7 := carry_of (swaps := [(1,4),(2,3),(3,4)]) (by decide +kernel) low_21
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_28_1 : Slice r_28 g_28 (subcubeFast 8 0) 7 := by
  have hc : Lower (varsOf 23) 0x8e8e08088e8e0808 7 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_23
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_28_2 : Slice r_28 g_28 (subcubeFast 0 1) 6 := by
  have hc : Lower (varsOf 30) 0xffcffc0cffcffc0c 6 := carry_of (swaps := [(0,4),(2,3),(3,4)]) (by decide +kernel) low_25
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_28_3 : Slice r_28 g_28 (subcubeFast 16 0) 6 := by
  have hc : Lower (varsOf 15) 0xac08ac08ac08ac08 6 := carry_of (swaps := [(1,2),(2,3)]) (by decide +kernel) low_26
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_28_4 : Slice r_28 g_28 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) 0xffeecc88ffeecc88 5 := carry_of (swaps := [(1,2),(2,4),(3,4)]) (by decide +kernel) low_14
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_28_5 : Slice r_28 g_28 (subcubeFast 0 16) 5 := by
  exact slice_fast_direct_f (z := 0) (o := 16) (by decide +kernel) low_27
set_option maxHeartbeats 0 in
lemma sl_28_6 : Slice r_28 g_28 (subcubeFast 0 6) 4 := by
  have hc : Lower (varsOf 25) 0xffaaaa00ffaaaa00 4 := carry_of (swaps := [(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 0) (o := 6) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_28_7 : Slice r_28 g_28 (subcubeFast 5 0) 4 := by
  have hc : Lower (varsOf 26) 0xffcccc00ffcccc00 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 5) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_28_8 : Slice r_28 g_28 (subcubeFast 12 0) 4 := by
  have hc : Lower (varsOf 19) 0xeeee8888eeee8888 4 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 12) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_28_9 : Slice r_28 g_28 (subcubeFast 1 2) 4 := by
  have hc : Lower (varsOf 28) 0xff0f0f00ff0f0f00 4 := carry_of (swaps := [(0,3),(1,4)]) (by decide +kernel) low_19
  exact slice_fast_direct_f (z := 1) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_28_10 : Slice r_28 g_28 (subcubeFast 8 16) 4 := by
  exact slice_fast_direct_f (z := 8) (o := 16) (by decide +kernel) low_19
set_option maxHeartbeats 0 in
lemma sl_28_11 : Slice r_28 g_28 (subcubeFast 16 8) 3 := by
  exact slice_fast_direct_f (z := 16) (o := 8) (by decide +kernel) low_24
def S_28 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 0 2,7),some (subcubeFast 8 0,7),some (subcubeFast 0 1,6),some (subcubeFast 16 0,6),some (subcubeFast 4 0,5),some (subcubeFast 0 16,5),some (subcubeFast 0 6,4),some (subcubeFast 5 0,4),some (subcubeFast 12 0,4),some (subcubeFast 1 2,4),some (subcubeFast 8 16,4),some (subcubeFast 16 8,3)]
lemma S_28_ok : btAll (fun o => ∀ p, o = some p → Slice r_28 g_28 p.1 p.2) S_28 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_28_0) (forall_cons (fun _ h => by cases h; exact sl_28_1) (forall_cons (fun _ h => by cases h; exact sl_28_2) (forall_cons (fun _ h => by cases h; exact sl_28_3) (forall_cons (fun _ h => by cases h; exact sl_28_4) (forall_cons (fun _ h => by cases h; exact sl_28_5) (forall_cons (fun _ h => by cases h; exact sl_28_6) (forall_cons (fun _ h => by cases h; exact sl_28_7) (forall_cons (fun _ h => by cases h; exact sl_28_8) (forall_cons (fun _ h => by cases h; exact sl_28_9) (forall_cons (fun _ h => by cases h; exact sl_28_10) (forall_cons (fun _ h => by cases h; exact sl_28_11) (fun _ h => (List.not_mem_nil h).elim)))))))))))))
def ps_28 : BT (Option PoolSpec) := btOfList 5 [q 7 [],q 0 [16394],q 8 [],q 5 [],q 9 [],q 6 [],q 11 [],q 3 [],q 2 [],q 10 [],q 2 [16393],q 0 [16393],q 4 [],q 1 [8194],q 1 [8192],q 3 [8192],q 0 [],q 1 []]
def B_28_5 : BT (List (List Nat)) := BT.empty
lemma B_28_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_28 5 xs.toFinset) B_28_5 := .empty
def U_28_6 : List Nat := (r 0 9)
def P_28_6 : BT (Option BoundPool) := buildPoolsSubBT 5 W_28 r_28 S_28 ps_28 U_28_6
def N_28_6 : List NodeSpec := [([0,6,2,3,4],(r 0 4),[]),([0,1,2,8,4],[4,5,0,6],[]),([9,0,1,3,4,10],[5,2,3,7,4,8],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_28_6 : checkNodesBT W_28 g_28 F_28 P_28_6 A_28 B_28_5 6 N_28_6 = true := by decide +kernel
def B_28_6 : BT (List (List Nat)) := buildBucketsBT W_28 N_28_6
set_option maxRecDepth 500000 in
lemma B_28_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_28 6 xs.toFinset) B_28_6 :=
  buildBucketsBT_sound (by decide) gp_28 W_28_ok (buildPoolsSubBT_sound S_28_ok) A_28_ok B_28_5_ok C_28_6
def U_28_7 : List Nat := (r 0 6++r 7 9)
def P_28_7 : BT (Option BoundPool) := buildPoolsSubBT 5 W_28 r_28 S_28 ps_28 U_28_7
def N_28_7 : List NodeSpec := [u5 [5] [0,1,2,7,3],([5,0,1,3,4],[4,9,1],[]),u5 [10] [5,10,9,0,7],([0,1,3,4,10],[11,9,4],[]),e5 [11] [7,5,4,12,9],([7,0,1,3,4],[4,3,13],[]),u5 [7] [5,13,3,7,4,8,0],([9,0,1,3,4],[3,4,14],[]),u5 [9] [4,8,14,3,12,15]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_28_7 : checkNodesBT W_28 g_28 F_28 P_28_7 A_28 B_28_6 7 N_28_7 = true := by decide +kernel
def B_28_7 : BT (List (List Nat)) := buildBucketsBT W_28 N_28_7
set_option maxRecDepth 500000 in
lemma B_28_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_28 7 xs.toFinset) B_28_7 :=
  buildBucketsBT_sound (by decide) gp_28 W_28_ok (buildPoolsSubBT_sound S_28_ok) A_28_ok B_28_6_ok C_28_7
def U_28_8 : List Nat := [7,8,16,17]
def P_28_8 : BT (Option BoundPool) := buildPoolsSubBT 5 W_28 r_28 S_28 ps_28 U_28_8
def N_28_8 : List NodeSpec := [u5 [] [16,8,17,7]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_28_8 : checkNodesBT W_28 g_28 F_28 P_28_8 A_28 B_28_7 8 N_28_8 = true := by decide +kernel
def B_28_8 : BT (List (List Nat)) := buildBucketsBT W_28 N_28_8
set_option maxRecDepth 500000 in
lemma B_28_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_28 8 xs.toFinset) B_28_8 :=
  buildBucketsBT_sound (by decide) gp_28 W_28_ok (buildPoolsSubBT_sound S_28_ok) A_28_ok B_28_7_ok C_28_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_28_ok : forestRootCheck r_28 g_28 [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,3,7),(VAR 3,2,10),(VAR 4,1,17)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_28_in : bucketContainsBT B_28_8 r_28 = true := by decide +kernel
lemma low_28 : Lower r_28 g_28 9 := lower_of_forestBT root_28_ok B_28_8_ok root_28_in
def g_29 := 0xffe8c000ffe8c000
def r_29 : List Nat := varsOf 31
def p_29 : List Nat := [14,14,14,15,15,15,19,19,19,21,21,21,22,22,22,23,24,24,25,25,26,26,27,28,28,29]
def q_29 : List Nat := [12,10,6,13,11,7,18,17,3,20,17,5,20,18,6,7,16,8,17,9,18,10,11,20,12,13]
def F_29 : Nat := fullMask 26
set_option maxHeartbeats 0 in
lemma gp_29 : goodPairs g_29 p_29 q_29 := goodPairs_of (by decide +kernel)
def W_29 : BT Decor := buildWiresBT 5 (mkBase p_29 q_29 r_29) [(2,2,3),(3,5,1),(0,1,2),(0,1,4),(2,1,3),(0,2,4),(3,10,1),(3,7,4),(0,7,4),(1,7,3),(0,0,4),(2,0,3)]
lemma W_29_ok : btAll (fun x => faithful p_29 q_29 x ∧ x.1 < 2^64) W_29 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_29 : List (List (Nat × Nat)) := [[],[(1,2)]]
def A_29 : BT (List (Nat × Nat)) := btOfList 1 al_29
set_option maxHeartbeats 0 in
lemma A_29_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_29 = g_29) A_29 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_29_0 : Slice r_29 g_29 (subcubeFast 0 1) 6 := by
  have hc : Lower (varsOf 30) 0xfffcc000fffcc000 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_29_1 : Slice r_29 g_29 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) 0xfffaf000fffaf000 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_16
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_29_2 : Slice r_29 g_29 (subcubeFast 8 16) 4 := by
  exact slice_fast_direct_f (z := 8) (o := 16) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_29_3 : Slice r_29 g_29 (subcubeFast 1 4) 4 := by
  have hc : Lower (varsOf 26) 0xffcccc00ffcccc00 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_29_4 : Slice r_29 g_29 (identDom 2 3) 5 := by
  have hc : Lower (varsOf 23) 0xf8f8c0c0f8f8c0c0 5 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_8
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
def S_29 : BT (Option (Nat × Nat)) := btOfList 3 [some (subcubeFast 0 1,6),some (subcubeFast 0 2,5),some (subcubeFast 8 16,4),some (subcubeFast 1 4,4),some (identDom 2 3,5)]
lemma S_29_ok : btAll (fun o => ∀ p, o = some p → Slice r_29 g_29 p.1 p.2) S_29 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_29_0) (forall_cons (fun _ h => by cases h; exact sl_29_1) (forall_cons (fun _ h => by cases h; exact sl_29_2) (forall_cons (fun _ h => by cases h; exact sl_29_3) (forall_cons (fun _ h => by cases h; exact sl_29_4) (fun _ h => (List.not_mem_nil h).elim))))))
def ps_29 : BT (Option PoolSpec) := btOfList 3 [q 2 [],q 3 [],q 0 [],q 4 [],q 1 [],q 0 [8196]]
def B_29_4 : BT (List (List Nat)) := BT.empty
lemma B_29_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_29 4 xs.toFinset) B_29_4 := .empty
def U_29_5 : List Nat := (r 0 4)
def P_29_5 : BT (Option BoundPool) := buildPoolsSubBT 3 W_29 r_29 S_29 ps_29 U_29_5
def N_29_5 : List NodeSpec := [([0,7,8,2,3,4],[0,1],[]),([9,0,7,2,3,4],[0,1],[]),e5 [12] [1,2],e5 [14] [2,1],e5 [13] [2,1,3,0],e5 [6] [],e5 [11] []]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_29_5 : checkNodesBT W_29 g_29 F_29 P_29_5 A_29 B_29_4 5 N_29_5 = true := by decide +kernel
def B_29_5 : BT (List (List Nat)) := buildBucketsBT W_29 N_29_5
set_option maxRecDepth 500000 in
lemma B_29_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_29 5 xs.toFinset) B_29_5 :=
  buildBucketsBT_sound (by decide) gp_29 W_29_ok (buildPoolsSubBT_sound S_29_ok) A_29_ok B_29_4_ok C_29_5
def U_29_6 : List Nat := (r 0 6)
def P_29_6 : BT (Option BoundPool) := buildPoolsSubBT 3 W_29 r_29 S_29 ps_29 U_29_6
def N_29_6 : List NodeSpec := [([16,1,2,3,4],[0,1],[]),([15,1,2,3,4],[1,0],[]),a5 [9] [1,2,0,3,4] [0,1],a5 [8] [1,2,0,4] [0,1],a5 [7] [1,5,4,0,3] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_29_6 : checkNodesBT W_29 g_29 F_29 P_29_6 A_29 B_29_5 6 N_29_6 = true := by decide +kernel
def B_29_6 : BT (List (List Nat)) := buildBucketsBT W_29 N_29_6
set_option maxRecDepth 500000 in
lemma B_29_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_29 6 xs.toFinset) B_29_6 :=
  buildBucketsBT_sound (by decide) gp_29 W_29_ok (buildPoolsSubBT_sound S_29_ok) A_29_ok B_29_5_ok C_29_6
def U_29_7 : List Nat := [0,1,2,4]
def P_29_7 : BT (Option BoundPool) := buildPoolsSubBT 3 W_29 r_29 S_29 ps_29 U_29_7
def N_29_7 : List NodeSpec := [a5 [] [2,4,1,0] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_29_7 : checkNodesBT W_29 g_29 F_29 P_29_7 A_29 B_29_6 7 N_29_7 = true := by decide +kernel
def B_29_7 : BT (List (List Nat)) := buildBucketsBT W_29 N_29_7
set_option maxRecDepth 500000 in
lemma B_29_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_29 7 xs.toFinset) B_29_7 :=
  buildBucketsBT_sound (by decide) gp_29 W_29_ok (buildPoolsSubBT_sound S_29_ok) A_29_ok B_29_6_ok C_29_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_29_ok : forestRootCheck r_29 g_29 [(VAR 0,18,19),(VAR 1,12,14),(VAR 2,10,14),(VAR 3,6,14),(VAR 4,3,19)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_29_in : bucketContainsBT B_29_7 r_29 = true := by decide +kernel
lemma low_29 : Lower r_29 g_29 8 := lower_of_forestBT root_29_ok B_29_7_ok root_29_in
def g_30 := 0xfff3f220fff3f220
def r_30 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_30 : Lower r_30 g_30 8 := by
  have hc : Lower (varsOf 30) 0xfff3f330fff3f330 7 := carry_of (swaps := [(0,4),(1,3),(2,4)]) (by decide +kernel) low_21
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,4,5)]) (by decide +kernel) hc
def g_31 := 0xff8fce08ff8fce08
def r_31 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_31 : Lower r_31 g_31 8 := by
  have hc : Lower (varsOf 30) 0xffcfcf0cffcfcf0c 7 := carry_of (swaps := [(0,4),(1,4),(2,3),(3,4)]) (by decide +kernel) low_21
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,2,3)]) (by decide +kernel) hc
def g_32 := 0xf8ffa0c8f8ffa0c8
def r_32 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_32 : Lower r_32 g_32 8 := by
  have hc : Lower (varsOf 29) 0xfaffa0fafaffa0fa 7 := carry_of (swaps := [(1,4),(2,4)]) (by decide +kernel) low_21
  exact lift_of_f (z := 0) (o := 2) (essPairs := [(VAR 1,1,3)]) (by decide +kernel) hc
def g_33 := 0xffa8c000ffa8c000
def r_33 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_33 : Lower r_33 g_33 7 := by
  have hc : Lower (varsOf 30) 0xfffcc000fffcc000 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_2
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,18,19)]) (by decide +kernel) hc
def g_34 := 0xfefefc80fefefc80
def r_34 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_34 : Lower r_34 g_34 7 := by
  have hc : Lower (varsOf 23) 0xfefe8080fefe8080 6 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_2
  exact lift_of_f (z := 8) (o := 0) (essPairs := [(VAR 3,2,10)]) (by decide +kernel) hc
def g_35 := 0xfffafcc0fffafcc0
def r_35 : List Nat := varsOf 31
def p_35 : List Nat := [6,6,7,7,10,10,11,11,12,12,13,13,17,17,19,19,20,20,21,22,24,24,25,26]
def q_35 : List Nat := [4,2,5,3,8,2,9,3,8,4,9,5,16,1,18,3,16,4,5,18,16,8,9,18]
def F_35 : Nat := fullMask 24
set_option maxHeartbeats 0 in
lemma gp_35 : goodPairs g_35 p_35 q_35 := goodPairs_of (by decide +kernel)
def W_35 : BT Decor := buildWiresBT 3 (mkBase p_35 q_35 r_35) [(1,2,3),(3,1,5)]
lemma W_35_ok : btAll (fun x => faithful p_35 q_35 x ∧ x.1 < 2^64) W_35 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_35 : List (List (Nat × Nat)) := [[]]
def A_35 : BT (List (Nat × Nat)) := btOfList 1 al_35
set_option maxHeartbeats 0 in
lemma A_35_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_35 = g_35) A_35 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_35_0 : Slice r_35 g_35 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) 0xfffffcc0fffffcc0 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_35_1 : Slice r_35 g_35 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) 0xfffaf000fffaf000 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_16
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_35_2 : Slice r_35 g_35 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) 0xfff0fcc0fff0fcc0 5 := carry_of (swaps := [(0,4),(1,4)]) (by decide +kernel) low_14
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_35_3 : Slice r_35 g_35 (subcubeFast 17 0) 4 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 17) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_35_4 : Slice r_35 g_35 (subcubeFast 8 0) 4 := by
  have hc : Lower (varsOf 23) 0xfafac0c0fafac0c0 4 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_35_5 : Slice r_35 g_35 (subcubeFast 4 0) 4 := by
  have hc : Lower (varsOf 27) 0xffaacc00ffaacc00 4 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
def S_35 : BT (Option (Nat × Nat)) := btOfList 3 [some (subcubeFast 0 1,5),some (subcubeFast 2 0,5),some (subcubeFast 1 0,5),some (subcubeFast 17 0,4),some (subcubeFast 8 0,4),some (subcubeFast 4 0,4)]
lemma S_35_ok : btAll (fun o => ∀ p, o = some p → Slice r_35 g_35 p.1 p.2) S_35 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_35_0) (forall_cons (fun _ h => by cases h; exact sl_35_1) (forall_cons (fun _ h => by cases h; exact sl_35_2) (forall_cons (fun _ h => by cases h; exact sl_35_3) (forall_cons (fun _ h => by cases h; exact sl_35_4) (forall_cons (fun _ h => by cases h; exact sl_35_5) (fun _ h => (List.not_mem_nil h).elim)))))))
def ps_35 : BT (Option PoolSpec) := btOfList 3 [q 0 [],q 2 [],q 1 [],q 4 [],q 3 [],q 5 []]
def B_35_3 : BT (List (List Nat)) := BT.empty
lemma B_35_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_35 3 xs.toFinset) B_35_3 := .empty
def U_35_4 : List Nat := []
def P_35_4 : BT (Option BoundPool) := buildPoolsSubBT 3 W_35 r_35 S_35 ps_35 U_35_4
def N_35_4 : List NodeSpec := [([6,0,2,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_35_4 : checkNodesBT W_35 g_35 F_35 P_35_4 A_35 B_35_3 4 N_35_4 = true := by decide +kernel
def B_35_4 : BT (List (List Nat)) := buildBucketsBT W_35 N_35_4
set_option maxRecDepth 500000 in
lemma B_35_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_35 4 xs.toFinset) B_35_4 :=
  buildBucketsBT_sound (by decide) gp_35 W_35_ok (buildPoolsSubBT_sound S_35_ok) A_35_ok B_35_3_ok C_35_4
def U_35_5 : List Nat := (r 0 4)
def P_35_5 : BT (Option BoundPool) := buildPoolsSubBT 3 W_35 r_35 S_35 ps_35 U_35_5
def N_35_5 : List NodeSpec := [u5 [5] (r 0 4)]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_35_5 : checkNodesBT W_35 g_35 F_35 P_35_5 A_35 B_35_4 5 N_35_5 = true := by decide +kernel
def B_35_5 : BT (List (List Nat)) := buildBucketsBT W_35 N_35_5
set_option maxRecDepth 500000 in
lemma B_35_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_35 5 xs.toFinset) B_35_5 :=
  buildBucketsBT_sound (by decide) gp_35 W_35_ok (buildPoolsSubBT_sound S_35_ok) A_35_ok B_35_4_ok C_35_5
def U_35_6 : List Nat := ([0]++r 2 4)
def P_35_6 : BT (Option BoundPool) := buildPoolsSubBT 3 W_35 r_35 S_35 ps_35 U_35_6
def N_35_6 : List NodeSpec := [u5 [] [2,0,4,3,5]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_35_6 : checkNodesBT W_35 g_35 F_35 P_35_6 A_35 B_35_5 6 N_35_6 = true := by decide +kernel
def B_35_6 : BT (List (List Nat)) := buildBucketsBT W_35 N_35_6
set_option maxRecDepth 500000 in
lemma B_35_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_35 6 xs.toFinset) B_35_6 :=
  buildBucketsBT_sound (by decide) gp_35 W_35_ok (buildPoolsSubBT_sound S_35_ok) A_35_ok B_35_5_ok C_35_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_35_ok : forestRootCheck r_35 g_35 [(VAR 0,16,17),(VAR 1,4,6),(VAR 2,2,6),(VAR 3,2,10),(VAR 4,1,17)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_35_in : bucketContainsBT B_35_6 r_35 = true := by decide +kernel
lemma low_35 : Lower r_35 g_35 7 := lower_of_forestBT root_35_ok B_35_6_ok root_35_in
def g_36 := 0xffecf800ffecf800
def r_36 : List Nat := varsOf 31
def p_36 : List Nat := [11,11,11,12,12,13,13,14,14,15,18,18,19,19,21,21,21,22,22,23,24,24,25,25,26,28]
def q_36 : List Nat := [10,9,3,8,4,9,5,10,6,7,16,2,17,3,20,17,5,20,6,7,16,8,17,9,10,20]
def F_36 : Nat := fullMask 26
set_option maxHeartbeats 0 in
lemma gp_36 : goodPairs g_36 p_36 q_36 := goodPairs_of (by decide +kernel)
def W_36 : BT Decor := buildWiresBT 6 (mkBase p_36 q_36 r_36) [(1,2,3),(0,0,5),(1,2,4),(0,3,7),(0,3,4),(1,0,9),(1,2,9),(1,3,4),(3,9,12),(2,0,9),(1,1,9),(2,13,2),(2,1,9),(0,0,12),(2,13,0),(0,1,12),(1,7,3),(3,2,21),(0,13,1),(0,13,0),(3,0,12),(0,2,12),(2,3,4),(3,2,3),(1,1,2),(2,29,4),(3,1,4),(1,31,3),(3,2,32),(0,0,29),(1,1,3),(1,35,4),(3,1,36),(3,2,36),(0,0,4),(1,39,3),(3,2,40),(2,2,9),(3,9,4),(1,29,3),(2,44,4),(2,0,4),(1,46,3),(3,2,35),(3,46,3),(2,35,4),(3,39,3),(3,7,3),(2,5,4),(1,1,4),(3,2,54),(1,43,1),(0,0,3)]
lemma W_36_ok : btAll (fun x => faithful p_36 q_36 x ∧ x.1 < 2^64) W_36 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_36 : List (List (Nat × Nat)) := [[],[(1,2),(3,4)]]
def A_36 : BT (List (Nat × Nat)) := btOfList 1 al_36
set_option maxHeartbeats 0 in
lemma A_36_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_36 = g_36) A_36 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_36_0 : Slice r_36 g_36 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) 0xffcc8800ffcc8800 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_36_1 : Slice r_36 g_36 (subcubeFast 4 1) 4 := by
  have hc : Lower (varsOf 26) 0xffcccc00ffcccc00 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_36_2 : Slice r_36 g_36 (subcubeFast 2 1) 4 := by
  have hc : Lower (varsOf 28) 0xfff0f000fff0f000 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 2) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_36_3 : Slice r_36 g_36 (identDom 1 3) 6 := by
  have hc : Lower (varsOf 23) 0xececc8c8ececc8c8 6 := carry_of (swaps := [(1,3),(2,3),(3,4)]) (by decide +kernel) low_2
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_36_4 : Slice r_36 g_36 (identDom 2 4) 6 := by
  have hc : Lower (varsOf 15) 0xf8e0f8e0f8e0f8e0 6 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_2
  exact slice_ident (u := 2) (v := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_36_5 : Slice r_36 g_36 (identDom 0 3) 5 := by
  have hc : Lower (varsOf 23) 0xeeeea8a8eeeea8a8 5 := carry_of (swaps := [(0,3),(2,3),(3,4)]) (by decide +kernel) low_16
  exact slice_ident (u := 0) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_36_6 : Slice r_36 g_36 (subcubeFast 1 0) 4 := by
  have hc : Lower (varsOf 30) 0xffccf000ffccf000 4 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
def S_36 : BT (Option (Nat × Nat)) := btOfList 3 [some (subcubeFast 4 0,5),some (subcubeFast 4 1,4),some (subcubeFast 2 1,4),some (identDom 1 3,6),some (identDom 2 4,6),some (identDom 0 3,5),some (subcubeFast 1 0,4)]
lemma S_36_ok : btAll (fun o => ∀ p, o = some p → Slice r_36 g_36 p.1 p.2) S_36 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_36_0) (forall_cons (fun _ h => by cases h; exact sl_36_1) (forall_cons (fun _ h => by cases h; exact sl_36_2) (forall_cons (fun _ h => by cases h; exact sl_36_3) (forall_cons (fun _ h => by cases h; exact sl_36_4) (forall_cons (fun _ h => by cases h; exact sl_36_5) (forall_cons (fun _ h => by cases h; exact sl_36_6) (fun _ h => (List.not_mem_nil h).elim))))))))
def ps_36 : BT (Option PoolSpec) := btOfList 4 [q 1 [],q 6 [],q 3 [],q 2 [],q 4 [],q 0 [],q 5 [],q 4 [16397],q 3 [16391,12413],q 3 [16398],q 4 [12299],q 3 [16397]]
def B_36_2 : BT (List (List Nat)) := BT.empty
lemma B_36_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_36 2 xs.toFinset) B_36_2 := .empty
def U_36_3 : List Nat := []
def P_36_3 : BT (Option BoundPool) := buildPoolsSubBT 4 W_36 r_36 S_36 ps_36 U_36_3
def N_36_3 : List NodeSpec := [([13,18,1,2],[],[]),([0,20,26,9],[],[]),([13,0,1,2],[],[]),([13,25,1,2],[],[]),([24,13,1,2],[],[]),([23,13,0,2],[],[]),([13,22,0,1],[],[]),([13,0,20,2],[],[]),([19,13,1,2],[],[]),([6,1,8,4],[],[]),([17,13,0,2],[],[]),([13,0,1,11],[],[]),([16,13,0,1],[],[]),([0,15,11,12],[],[]),([14,13,1,2],[],[]),([13,1,2,10],[],[]),([1,10,11,12],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_36_3 : checkNodesBT W_36 g_36 F_36 P_36_3 A_36 B_36_2 3 N_36_3 = true := by decide +kernel
def B_36_3 : BT (List (List Nat)) := buildBucketsBT W_36 N_36_3
set_option maxRecDepth 500000 in
lemma B_36_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_36 3 xs.toFinset) B_36_3 :=
  buildBucketsBT_sound (by decide) gp_36 W_36_ok (buildPoolsSubBT_sound S_36_ok) A_36_ok B_36_2_ok C_36_3
def U_36_4 : List Nat := []
def P_36_4 : BT (Option BoundPool) := buildPoolsSubBT 4 W_36 r_36 S_36 ps_36 U_36_4
def N_36_4 : List NodeSpec := [([0,3,15,11,4],[],[0]),([13,0,1,2,3],[],[]),([14,1,2,9,12],[],[0]),([22,0,1,9,12],[],[0]),([22,0,20,3,4],[],[]),([41,0,1,3,4],[],[]),([1,2,9,10,12],[],[0,1]),([0,20,2,9,12],[],[0]),([14,17,2,3,4],[],[]),([17,42,0,3,4],[],[]),([22,18,1,3,4],[],[]),([17,0,3,11,4],[],[]),([17,0,2,9,12],[],[0]),([0,1,9,11,12],[],[0]),([25,1,2,9,12],[],[0]),([0,1,2,9,12],[],[0]),([27,0,2,15,4],[],[]),([27,43,0,1,2],[],[0]),([45,0,1,2,3],[],[]),([18,1,2,9,12],[],[0]),([1,3,10,11,4],[],[0]),([0,20,26,3,4],[],[0]),([13,0,1,2,12],[],[0,1]),([22,25,1,3,4],[],[]),([13,0,1,2,9],[],[0,1]),([13,0,1,2],[],[0,1]),([18,20,2,3,4],[],[]),([28,6,1,3,4],[],[]),([0,1,2,8,12],[],[]),([6,1,3,4,7],[],[0]),([27,13,0,1,2],[],[]),([22,0,1,3,4],[],[]),([30,31,0,2,3],[],[]),([0,1,8,5,4],[],[0]),([33,0,1,3,4],[],[]),([14,1,3,11,4],[],[]),([28,34,1,3,4],[],[]),([22,37,0,3,4],[],[]),([34,1,3,4,7],[],[]),([38,0,1,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_36_4 : checkNodesBT W_36 g_36 F_36 P_36_4 A_36 B_36_3 4 N_36_4 = true := by decide +kernel
def B_36_4 : BT (List (List Nat)) := buildBucketsBT W_36 N_36_4
set_option maxRecDepth 500000 in
lemma B_36_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_36 4 xs.toFinset) B_36_4 :=
  buildBucketsBT_sound (by decide) gp_36 W_36_ok (buildPoolsSubBT_sound S_36_ok) A_36_ok B_36_3_ok C_36_4
def U_36_5 : List Nat := (r 0 9)
def P_36_5 : BT (Option BoundPool) := buildPoolsSubBT 4 W_36 r_36 S_36 ps_36 U_36_5
def N_36_5 : List NodeSpec := [([14,1,2,9,3,4],[0],[0,1]),([6,1,2,3,4],[0],[0]),([6,1,2,3,5,4],[0],[0]),([18,1,2,3,4,12],[0],[0,1]),([34,1,2,29,3,4],[0],[]),e5 [56] [1,0],([34,1,2,3,4],[0,3],[0,1]),e5 [49] [1,2,3],([17,0,2,9,3,4],[2,3],[0]),([27,0,1,2,35,4],[3],[]),([0,20,2,3,4,12],[3],[0,1]),([28,0,1,29,3,4],[3],[0,1]),([1,2,9,3,10,4],[3,0,1],[0,1]),u5 [9] (r 0 5),u5 [8] (r 0 5),([0,1,29,3,4,7],[3,4],[0]),([0,1,3,5,4,7],[4],[0]),([28,0,1,3,5,4],[5],[0]),([27,0,1,2,9,4],[5],[0]),([0,1,2,3,7,12],[5],[0]),([0,1,9,3,11,4],[5],[0,1]),u5 [30] [5],([22,0,1,3,4,12],[5],[0]),([27,0,1,2,3,12],[5],[0]),a5 [36] [6,0] [0,1],a5 [12] [6,0,3] [0,1],u5 [44] [6,0,4],([25,1,2,3,4,12],[6,3,0],[0,1]),u5 [40] [6,5],([0,1,2,9,3,12],[7],[0]),a5 [32] [6,0,8] [0,1],([14,1,2,3,4],[],[]),e5 [22] [],([0,1,2,9,12],[],[0,1]),([27,43,0,1,2],[],[0,1]),e5 [52] [],e5 [55] [],e5 [53] [],([22,0,1,3,4],[],[]),e5 [47] [],e5 [51] [],([27,43,0,1,2,3],[],[0]),e5 [50] [],([18,1,2,3,4],[],[]),u5 [27] [],e5 [48] []]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_36_5 : checkNodesBT W_36 g_36 F_36 P_36_5 A_36 B_36_4 5 N_36_5 = true := by decide +kernel
def B_36_5 : BT (List (List Nat)) := buildBucketsBT W_36 N_36_5
set_option maxRecDepth 500000 in
lemma B_36_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_36 5 xs.toFinset) B_36_5 :=
  buildBucketsBT_sound (by decide) gp_36 W_36_ok (buildPoolsSubBT_sound S_36_ok) A_36_ok B_36_4_ok C_36_5
def U_36_6 : List Nat := (r 0 6++[7,9,10,11])
def P_36_6 : BT (Option BoundPool) := buildPoolsSubBT 4 W_36 r_36 S_36 ps_36 U_36_6
def N_36_6 : List NodeSpec := [u5 [46] [1,3,0],a5 [57] [3,0,1] [1],a5 [29] [0,3,2,4] [0,1],a5 [5] [0,3,4] [0,1],a5 [9] [1,0,3,2,4] [0,1],a5 [35] [3,2,5] [0,1],a5 [27] [1,0,3,2,9] [0,1],a5 [28] [0,3,2,4,10] [0,1],a5 [12] [1,0,11,3,7] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_36_6 : checkNodesBT W_36 g_36 F_36 P_36_6 A_36 B_36_5 6 N_36_6 = true := by decide +kernel
def B_36_6 : BT (List (List Nat)) := buildBucketsBT W_36 N_36_6
set_option maxRecDepth 500000 in
lemma B_36_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_36 6 xs.toFinset) B_36_6 :=
  buildBucketsBT_sound (by decide) gp_36 W_36_ok (buildPoolsSubBT_sound S_36_ok) A_36_ok B_36_5_ok C_36_6
def U_36_7 : List Nat := [0,2,3,4]
def P_36_7 : BT (Option BoundPool) := buildPoolsSubBT 4 W_36 r_36 S_36 ps_36 U_36_7
def N_36_7 : List NodeSpec := [a5 [] [3,0,2,4] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_36_7 : checkNodesBT W_36 g_36 F_36 P_36_7 A_36 B_36_6 7 N_36_7 = true := by decide +kernel
def B_36_7 : BT (List (List Nat)) := buildBucketsBT W_36 N_36_7
set_option maxRecDepth 500000 in
lemma B_36_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_36 7 xs.toFinset) B_36_7 :=
  buildBucketsBT_sound (by decide) gp_36 W_36_ok (buildPoolsSubBT_sound S_36_ok) A_36_ok B_36_6_ok C_36_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_36_ok : forestRootCheck r_36 g_36 [(VAR 0,10,11),(VAR 1,9,11),(VAR 2,8,12),(VAR 3,3,11),(VAR 4,2,18)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_36_in : bucketContainsBT B_36_7 r_36 = true := by decide +kernel
lemma low_36 : Lower r_36 g_36 8 := lower_of_forestBT root_36_ok B_36_7_ok root_36_in
def g_37 := 0xfc40fc40fc40fc40
def r_37 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_37 : Lower r_37 g_37 5 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,6,7)]) (by decide +kernel) hc
def g_38 := 0xfbb0fbb0fbb0fbb0
def r_38 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_38 : Lower r_38 g_38 5 := by
  have hc : Lower (varsOf 14) 0xf330f330f330f330 4 := carry_of (swaps := [(0,3),(1,2),(2,3)]) (by decide +kernel) low_19
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,6,7)]) (by decide +kernel) hc
def g_39 := 0xfdc0fdc0fdc0fdc0
def r_39 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_39 : Lower r_39 g_39 5 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,8,9)]) (by decide +kernel) hc
def g_40 := 0xcf08cf08cf08cf08
def r_40 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_40 : Lower r_40 g_40 5 := by
  have hc : Lower (varsOf 14) 0xcf0ccf0ccf0ccf0c 4 := carry_of (swaps := [(0,3),(1,3)]) (by decide +kernel) low_19
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,2,3)]) (by decide +kernel) hc
def g_41 := 0x80f880f880f880f8
def r_41 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_41 : Lower r_41 g_41 5 := by
  have hc : Lower (varsOf 14) 0xc0fcc0fcc0fcc0fc 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_19
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,2,3)]) (by decide +kernel) hc
def g_42 := 0xb0b0b0b0b0b0b0b0
def r_42 : List Nat := varsOf 7
set_option maxHeartbeats 0 in
lemma low_42 : Lower r_42 g_42 2 := count_of (essPairs := [(VAR 0,6,7),(VAR 1,4,6),(VAR 2,0,4)]) (by decide +kernel)
def g_43 := 0xfbe0fbe0fbe0fbe0
def r_43 : List Nat := varsOf 15
def p_43 : List Nat := [5,5,6,6,7,8,9,11,11,12,14]
def q_43 : List Nat := [4,1,4,2,3,0,1,10,3,4,10]
def F_43 : Nat := fullMask 11
set_option maxHeartbeats 0 in
lemma gp_43 : goodPairs g_43 p_43 q_43 := goodPairs_of (by decide +kernel)
def W_43 : BT Decor := buildWiresBT 2 (mkBase p_43 q_43 r_43) []
lemma W_43_ok : btAll (fun x => faithful p_43 q_43 x ∧ x.1 < 2^64) W_43 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_43 : List (List (Nat × Nat)) := [[]]
def A_43 : BT (List (Nat × Nat)) := btOfList 1 al_43
set_option maxHeartbeats 0 in
lemma A_43_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_43 = g_43) A_43 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_43_0 : Slice r_43 g_43 (subcubeFast 1 0) 3 := by
  have hc : Lower (varsOf 14) 0xf3c0f3c0f3c0f3c0 3 := carry_of (swaps := [(0,3),(1,2),(2,3)]) (by decide +kernel) low_24
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_43_1 : Slice r_43 g_43 (subcubeFast 4 0) 2 := by
  have hc : Lower (varsOf 11) 0xbb00bb00bb00bb00 2 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_42
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_43_2 : Slice r_43 g_43 (subcubeFast 0 8) 2 := by
  have hc : Lower (varsOf 7) 0x404040404040404 2 := carry_of (swaps := [(0,1)]) (by decide +kernel) low_20
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
def S_43 : BT (Option (Nat × Nat)) := btOfList 2 [some (subcubeFast 1 0,3),some (subcubeFast 4 0,2),some (subcubeFast 0 8,2)]
lemma S_43_ok : btAll (fun o => ∀ p, o = some p → Slice r_43 g_43 p.1 p.2) S_43 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_43_0) (forall_cons (fun _ h => by cases h; exact sl_43_1) (forall_cons (fun _ h => by cases h; exact sl_43_2) (fun _ h => (List.not_mem_nil h).elim))))
def ps_43 : BT (Option PoolSpec) := btOfList 2 [q 0 [],q 1 [],q 2 []]
def B_43_3 : BT (List (List Nat)) := BT.empty
lemma B_43_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_43 3 xs.toFinset) B_43_3 := .empty
def U_43_4 : List Nat := [0,1,2]
def P_43_4 : BT (Option BoundPool) := buildPoolsSubBT 2 W_43 r_43 S_43 ps_43 U_43_4
def N_43_4 : List NodeSpec := [([0,1,2,3],[0,1,2],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_43_4 : checkNodesBT W_43 g_43 F_43 P_43_4 A_43 B_43_3 4 N_43_4 = true := by decide +kernel
def B_43_4 : BT (List (List Nat)) := buildBucketsBT W_43 N_43_4
set_option maxRecDepth 500000 in
lemma B_43_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_43 4 xs.toFinset) B_43_4 :=
  buildBucketsBT_sound (by decide) gp_43 W_43_ok (buildPoolsSubBT_sound S_43_ok) A_43_ok B_43_3_ok C_43_4
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_43_ok : forestRootCheck r_43 g_43 [(VAR 0,4,5),(VAR 1,4,6),(VAR 2,1,5),(VAR 3,0,8)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_43_in : bucketContainsBT B_43_4 r_43 = true := by decide +kernel
lemma low_43 : Lower r_43 g_43 5 := lower_of_forestBT root_43_ok B_43_4_ok root_43_in
def g_44 := 0xf2f2f2f2f2f2f2f2
def r_44 : List Nat := varsOf 7
set_option maxHeartbeats 0 in
lemma low_44 : Lower r_44 g_44 2 := count_of (essPairs := [(VAR 0,0,1),(VAR 1,1,3),(VAR 2,0,4)]) (by decide +kernel)
def g_45 := 0xf280f280f280f280
def r_45 : List Nat := varsOf 15
def p_45 : List Nat := [7,7,7,9,9,12,12,13,14,14,15]
def q_45 : List Nat := [6,5,3,8,1,8,4,5,10,6,11]
def F_45 : Nat := fullMask 11
set_option maxHeartbeats 0 in
lemma gp_45 : goodPairs g_45 p_45 q_45 := goodPairs_of (by decide +kernel)
def W_45 : BT Decor := buildWiresBT 2 (mkBase p_45 q_45 r_45) []
lemma W_45_ok : btAll (fun x => faithful p_45 q_45 x ∧ x.1 < 2^64) W_45 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_45 : List (List (Nat × Nat)) := [[]]
def A_45 : BT (List (Nat × Nat)) := btOfList 1 al_45
set_option maxHeartbeats 0 in
lemma A_45_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_45 = g_45) A_45 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_45_0 : Slice r_45 g_45 (subcubeFast 0 1) 3 := by
  have hc : Lower (varsOf 14) 0xf3c0f3c0f3c0f3c0 3 := carry_of (swaps := [(0,3),(1,2),(2,3)]) (by decide +kernel) low_24
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_45_1 : Slice r_45 g_45 (subcubeFast 4 0) 2 := by
  have hc : Lower (varsOf 11) 0x2200220022002200 2 := carry_of (swaps := [(1,2),(2,3)]) (by decide +kernel) low_22
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_45_2 : Slice r_45 g_45 (subcubeFast 0 8) 2 := by
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) low_44
def S_45 : BT (Option (Nat × Nat)) := btOfList 2 [some (subcubeFast 0 1,3),some (subcubeFast 4 0,2),some (subcubeFast 0 8,2)]
lemma S_45_ok : btAll (fun o => ∀ p, o = some p → Slice r_45 g_45 p.1 p.2) S_45 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_45_0) (forall_cons (fun _ h => by cases h; exact sl_45_1) (forall_cons (fun _ h => by cases h; exact sl_45_2) (fun _ h => (List.not_mem_nil h).elim))))
def ps_45 : BT (Option PoolSpec) := btOfList 2 [q 0 [],q 1 [],q 2 []]
def B_45_3 : BT (List (List Nat)) := BT.empty
lemma B_45_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_45 3 xs.toFinset) B_45_3 := .empty
def U_45_4 : List Nat := [0,1,2]
def P_45_4 : BT (Option BoundPool) := buildPoolsSubBT 2 W_45 r_45 S_45 ps_45 U_45_4
def N_45_4 : List NodeSpec := [([0,1,2,3],[0,1,2],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_45_4 : checkNodesBT W_45 g_45 F_45 P_45_4 A_45 B_45_3 4 N_45_4 = true := by decide +kernel
def B_45_4 : BT (List (List Nat)) := buildBucketsBT W_45 N_45_4
set_option maxRecDepth 500000 in
lemma B_45_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_45 4 xs.toFinset) B_45_4 :=
  buildBucketsBT_sound (by decide) gp_45 W_45_ok (buildPoolsSubBT_sound S_45_ok) A_45_ok B_45_3_ok C_45_4
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_45_ok : forestRootCheck r_45 g_45 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,1,9)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_45_in : bucketContainsBT B_45_4 r_45 = true := by decide +kernel
lemma low_45 : Lower r_45 g_45 5 := lower_of_forestBT root_45_ok B_45_4_ok root_45_in
def g_46 := 0xfffffae8fc80c000
def r_46 : List Nat := varsOf 63
def p_46 : List Nat := [14,14,14,15,15,15,23,23,23,23,26,26,26,27,27,27,28,28,28,29,29,29,30,35,35,35,37,37,37,38,38,38,39,41,41,41,43,43,44,44,44,45,46,48,48,49,49,50,50,51,52,52,53,54,56,56,57,58]
def q_46 : List Nat := [12,10,6,13,11,7,22,21,19,7,24,18,10,25,19,11,24,20,12,25,21,13,22,34,33,3,36,33,5,36,34,6,7,40,33,9,42,11,40,36,12,13,42,32,16,33,17,34,18,19,36,20,21,22,40,24,25,42]
def F_46 : Nat := fullMask 58
set_option maxHeartbeats 0 in
lemma gp_46 : goodPairs g_46 p_46 q_46 := goodPairs_of (by decide +kernel)
def W_46 : BT Decor := buildWiresBT 9 (mkBase p_46 q_46 r_46) [(0,1,5),(1,6,3),(0,2,7),(2,0,8),(1,8,4),(3,1,10),(1,1,3),(1,2,4),(0,12,13),(0,14,5),(1,14,5),(3,15,16),(0,2,12),(2,1,5),(3,19,12),(2,2,4),(3,21,12),(1,15,4),(3,2,12),(2,12,4),(3,25,2),(1,3,5),(0,13,27),(3,1,28),(3,1,5),(1,30,4),(3,2,31),(3,3,31),(3,33,2),(1,1,5),(0,13,35),(3,3,36),(2,2,15),(1,2,5),(3,21,39),(2,12,40),(3,4,16),(2,14,5),(3,14,5),(0,1,27),(0,2,27),(1,1,46),(0,0,39),(2,1,4),(1,2,3),(0,50,35),(2,12,5),(1,25,2),(1,18,4),(0,7,13),(2,18,4),(1,12,4),(3,19,57),(1,4,5),(0,2,59),(3,60,12),(0,1,54),(2,1,2),(3,3,5),(1,64,4),(3,63,65),(1,25,5),(2,25,2),(0,0,12),(2,0,4),(1,70,3),(0,71,35),(0,1,2),(1,73,3),(0,74,59),(0,2,35),(3,49,35),(3,4,35),(0,0,2),(1,79,3),(0,12,5),(0,0,1),(1,82,3),(0,83,39),(1,1,4),(2,85,5),(0,2,31),(2,0,3),(3,73,59),(0,12,39),(1,3,4),(3,1,2),(0,91,5),(1,92,93),(2,2,3),(1,95,4),(0,96,35),(0,50,31),(3,25,39),(0,0,5),(1,100,3),(2,101,4),(2,0,2),(1,103,3),(0,0,59),(1,73,4),(0,80,35),(1,1,2),(0,108,27),(1,24,4),(3,73,65),(0,0,35),(0,108,65),(3,0,35),(0,83,13),(3,95,31),(1,109,4),(2,1,3),(0,83,59),(2,108,93),(3,4,5),(1,121,3),(0,108,122),(2,109,4),(2,2,5),(3,125,12),(2,51,4),(2,95,4),(3,128,35),(0,85,5),(1,3,130),(0,2,131),(1,12,5),(0,13,133),(3,21,5),(2,12,135),(1,21,3),(0,137,35),(1,125,25),(0,108,59),(3,1,13),(0,0,53),(0,80,59),(3,2,131),(1,49,46),(3,21,7),(1,21,100),(0,2,91),(1,6,148),(0,50,59),(3,1,150),(1,76,4),(3,21,35),(2,7,4),(3,154,2),(3,100,12),(1,92,4),(0,157,27),(0,1,150),(0,0,28),(2,0,28),(1,49,3),(0,162,39),(1,1,28),(3,2,27),(1,165,4),(3,4,27),(1,46,4),(3,1,27),(3,45,2),(1,21,5),(1,118,4),(3,21,1),(1,173,5),(3,21,27),(2,18,5),(1,18,5),(0,2,85),(1,63,5),(0,21,35),(3,92,27),(3,92,59),(2,91,5),(3,92,91),(3,3,157),(1,121,63),(2,50,4),(3,121,108),(3,2,5),(3,64,108),(1,21,1),(2,191,5),(3,6,2),(1,100,4),(0,108,91),(2,108,4),(1,19,3),(2,74,4),(1,30,3),(1,63,3),(3,1,59),(3,30,2),(1,202,4),(1,73,5),(3,79,91),(3,0,204),(0,0,204),(3,79,12),(2,74,5),(1,92,5),(1,64,92),(1,21,6),(3,100,91),(1,49,100),(1,100,73),(3,118,2),(2,157,5),(1,79,4),(3,19,2),(3,79,59),(2,83,4),(1,88,4),(1,19,4),(1,19,79),(3,1,39),(3,73,91),(3,63,91),(1,125,4),(3,64,2),(1,229,4),(3,1,50),(1,169,4),(3,64,13),(2,92,3),(1,234,5),(1,49,5),(3,79,85),(1,118,5),(2,108,3),(1,82,5),(1,88,5),(1,189,1),(2,242,4),(1,1,93),(2,83,5),(2,0,5),(2,13,5),(3,63,27),(0,2,5),(1,249,4),(3,82,39),(1,70,5),(1,216,5),(3,88,2),(2,80,4),(1,64,63),(3,100,2),(3,73,27),(3,1,137),(3,79,27),(3,82,2),(3,82,50),(1,193,4),(3,3,59),(3,49,2),(3,19,50),(3,19,91),(3,82,13),(3,3,39),(3,63,59),(3,19,13),(1,125,82),(3,70,2),(3,82,91),(1,92,100),(1,125,3),(2,80,5),(1,103,4),(1,21,82),(1,24,5),(3,6,91),(3,125,13),(1,121,73),(1,178,5),(3,82,27),(1,64,1),(1,64,73),(1,254,5),(1,3,135),(3,79,35),(2,108,5),(1,92,3),(3,82,59),(1,231,4),(1,49,189),(1,121,92),(3,100,85),(0,21,27),(3,30,13),(1,125,1),(3,3,13),(2,286,4),(2,137,5),(3,249,12),(3,4,39),(2,300,4),(1,189,4),(1,148,5),(0,2,133),(0,85,39),(0,12,59),(1,82,4),(3,121,2),(3,121,12),(1,216,4),(3,249,91),(0,50,85),(1,1,249),(2,318,4),(3,19,85),(3,3,85),(2,191,3),(1,249,3),(1,261,5),(3,249,85),(1,189,3),(0,85,27),(1,234,4),(1,49,79),(2,2,130),(1,225,4),(3,64,85),(1,265,5),(3,3,35),(3,2,7),(3,49,50),(1,49,249),(1,19,21),(3,125,85),(3,49,39),(1,125,49),(3,49,27),(1,173,3),(1,49,64),(1,6,4),(3,6,50),(3,6,13),(3,1,91),(1,95,1),(2,349,4),(3,2,35),(1,351,4),(0,91,35),(1,219,4),(3,189,12),(3,189,85),(1,141,5),(3,30,50),(1,21,30),(3,30,91),(1,231,5),(3,121,50),(2,349,5),(1,1,135),(1,21,64),(2,323,4),(0,91,39),(3,125,1),(1,368,3),(3,125,91),(3,189,91),(0,1,91),(3,372,2),(1,348,5),(2,1,93),(2,2,93),(3,2,91),(2,92,4),(0,0,85),(1,63,4),(1,103,5),(1,79,5),(2,92,5),(3,92,5),(0,0,91),(2,95,5),(3,2,85),(1,121,1),(2,50,5),(1,95,5)]
lemma W_46_ok : btAll (fun x => faithful p_46 q_46 x ∧ x.1 < 2^64) W_46 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_46 : List (List (Nat × Nat)) := [[]]
def A_46 : BT (List (Nat × Nat)) := btOfList 1 al_46
set_option maxHeartbeats 0 in
lemma A_46_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_46 = g_46) A_46 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_46_0 : Slice r_46 g_46 (subcubeFast 0 1) 9 := by
  have hc : Lower (varsOf 62) 0xfffffffcfcc0c000 9 := carry_of (swaps := [(0,5),(1,5),(2,5),(3,5),(4,5)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_1 : Slice r_46 g_46 (subcubeFast 8 0) 9 := by
  have hc : Lower (varsOf 55) 0xffffe8e880800000 9 := carry_of (swaps := [(3,5),(4,5)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_2 : Slice r_46 g_46 (subcubeFast 16 0) 9 := by
  have hc : Lower (varsOf 47) 0xfae8fae8c000c000 9 := carry_of (swaps := [(2,3),(4,5)]) (by decide +kernel) low_10
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_3 : Slice r_46 g_46 (identDom 0 1) 10 := by
  have hc : Lower (varsOf 61) 0xfffffaaafaa0a000 10 := carry_of (swaps := [(0,2),(1,5),(3,5),(4,5)]) (by decide +kernel) low_12
  exact slice_ident (u := 0) (v := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_4 : Slice r_46 g_46 (subcubeFast 32 0) 8 := by
  have hc : Lower (varsOf 31) 0xfc80c000fc80c000 8 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_13
  exact slice_fast_direct_f (z := 32) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_5 : Slice r_46 g_46 (subcubeFast 32 1) 7 := by
  have hc : Lower (varsOf 30) 0xfcc0c000fcc0c000 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 32) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_6 : Slice r_46 g_46 (subcubeFast 1 0) 8 := by
  have hc : Lower (varsOf 62) 0xfffff0c0fc00c000 8 := carry_of (swaps := [(0,5),(1,5),(2,5),(3,5),(4,5)]) (by decide +kernel) low_15
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_7 : Slice r_46 g_46 (subcubeFast 0 4) 8 := by
  have hc : Lower (varsOf 59) 0xffffffeeff88cc00 8 := carry_of (swaps := [(2,5),(4,5)]) (by decide +kernel) low_17
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_8 : Slice r_46 g_46 (fiDom 0 0 4 5 true) 9 := by
  have hc : Lower (varsOf 31) 0xfc80fae8fc80fae8 9 := carry_of (swaps := [(0,1),(2,4)]) (by decide +kernel) low_28
  exact slice_fi (z := 0) (o := 0) (u := 4) (v := 5) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_9 : Slice r_46 g_46 (subcubeFast 2 0) 8 := by
  have hc : Lower (varsOf 61) 0xfffffaa0f0000000 8 := carry_of (swaps := [(1,5),(2,5),(3,5),(4,5)]) (by decide +kernel) low_29
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_10 : Slice r_46 g_46 (fiDom 0 0 3 5 true) 8 := by
  have hc : Lower (varsOf 31) 0xfcffc0e8fcffc0e8 8 := carry_of (swaps := [(1,2),(2,3)]) (by decide +kernel) low_30
  exact slice_fi (z := 0) (o := 0) (u := 3) (v := 5) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_11 : Slice r_46 g_46 (fiDom 0 0 1 5 true) 8 := by
  have hc : Lower (varsOf 31) 0xffb3f220ffb3f220 8 := carry_of (swaps := [(1,2)]) (by decide +kernel) low_31
  exact slice_fi (z := 0) (o := 0) (u := 1) (v := 5) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_12 : Slice r_46 g_46 (fiDom 0 0 2 5 true) 8 := by
  have hc : Lower (varsOf 31) 0xff8fca08ff8fca08 8 := carry_of (swaps := [(0,1),(2,3)]) (by decide +kernel) low_32
  exact slice_fi (z := 0) (o := 0) (u := 2) (v := 5) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_13 : Slice r_46 g_46 (subcubeFast 4 0) 7 := by
  have hc : Lower (varsOf 59) 0xffffaa88cc000000 7 := carry_of (swaps := [(2,5),(3,5),(4,5)]) (by decide +kernel) low_33
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_14 : Slice r_46 g_46 (subcubeFast 0 2) 7 := by
  have hc : Lower (varsOf 61) 0xfffffafaffa0f000 7 := carry_of (swaps := [(1,5),(2,5),(4,5)]) (by decide +kernel) low_34
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_15 : Slice r_46 g_46 (subcubeFast 0 8) 7 := by
  have hc : Lower (varsOf 55) 0xfffffafafcfcc0c0 7 := carry_of (swaps := [(3,5),(4,5)]) (by decide +kernel) low_35
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_16 : Slice r_46 g_46 (fiDom 0 4 0 4 false) 7 := by
  have hc : Lower (varsOf 43) 0xffeeffeeee88ee88 7 := carry_of (swaps := [(2,4),(3,4),(4,5)]) (by decide +kernel) low_11
  exact slice_fi (z := 0) (o := 4) (u := 0) (v := 4) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_17 : Slice r_46 g_46 (fiDom 0 8 0 1 false) 7 := by
  have hc : Lower (varsOf 53) 0xfffffafafafaa0a0 7 := carry_of (swaps := [(1,4),(2,4),(3,5)]) (by decide +kernel) low_11
  exact slice_fi (z := 0) (o := 8) (u := 0) (v := 1) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_18 : Slice r_46 g_46 (fiDom 32 0 0 2 false) 7 := by
  have hc : Lower (varsOf 27) 0xee888800ee888800 7 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_fi (z := 32) (o := 0) (u := 0) (v := 2) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_19 : Slice r_46 g_46 (fiDom 32 0 0 4 false) 7 := by
  exact slice_fi (z := 32) (o := 0) (u := 0) (v := 4) (fl := false) (by decide +kernel) low_1
set_option maxHeartbeats 0 in
lemma sl_46_20 : Slice r_46 g_46 (fiDom 0 4 0 1 false) 7 := by
  have hc : Lower (varsOf 57) 0xffffffaaffaaaa00 7 := carry_of (swaps := [(1,4),(2,5),(3,4),(4,5)]) (by decide +kernel) low_11
  exact slice_fi (z := 0) (o := 4) (u := 0) (v := 1) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_21 : Slice r_46 g_46 (subcubeFast 8 1) 6 := by
  have hc : Lower (varsOf 54) 0xfffffcfcc0c00000 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,5)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 8) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_22 : Slice r_46 g_46 (subcubeFast 16 1) 6 := by
  have hc : Lower (varsOf 46) 0xfffcfffcc000c000 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4),(4,5)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 16) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_23 : Slice r_46 g_46 (subcubeFast 4 1) 6 := by
  have hc : Lower (varsOf 58) 0xffffffcccc000000 6 := carry_of (swaps := [(0,4),(1,4),(2,5),(3,4),(4,5)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 4) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_24 : Slice r_46 g_46 (subcubeFast 8 2) 6 := by
  have hc : Lower (varsOf 53) 0xfffffafaa0a00000 6 := carry_of (swaps := [(1,4),(2,4),(3,5)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 8) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_25 : Slice r_46 g_46 (subcubeFast 8 4) 6 := by
  have hc : Lower (varsOf 51) 0xffffeeee88880000 6 := carry_of (swaps := [(2,4),(3,5)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 8) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_26 : Slice r_46 g_46 (subcubeFast 2 1) 6 := by
  have hc : Lower (varsOf 60) 0xfffffff0f0000000 6 := carry_of (swaps := [(0,4),(1,5),(2,4),(3,5)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 2) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_27 : Slice r_46 g_46 (fiDom 32 0 0 3 true) 7 := by
  have hc : Lower (varsOf 23) 0xd4d44040d4d44040 7 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,4)]) (by decide +kernel) low_23
  exact slice_fi (z := 32) (o := 0) (u := 0) (v := 3) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_28 : Slice r_46 g_46 (fiDom 0 1 4 5 true) 7 := by
  have hc : Lower (varsOf 30) 0xfcc0fffcfcc0fffc 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_21
  exact slice_fi (z := 0) (o := 1) (u := 4) (v := 5) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_29 : Slice r_46 g_46 (fiDom 0 1 3 5 true) 7 := by
  have hc : Lower (varsOf 30) 0xfcffc0fcfcffc0fc 7 := carry_of (swaps := [(0,4),(1,4),(2,4)]) (by decide +kernel) low_21
  exact slice_fi (z := 0) (o := 1) (u := 3) (v := 5) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_30 : Slice r_46 g_46 (fiDom 0 4 0 5 true) 7 := by
  have hc : Lower (varsOf 27) 0xffdddd44ffdddd44 7 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_21
  exact slice_fi (z := 0) (o := 4) (u := 0) (v := 5) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_31 : Slice r_46 g_46 (fiDom 8 0 4 5 true) 7 := by
  have hc : Lower (varsOf 23) 0x8080e8e88080e8e8 7 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_23
  exact slice_fi (z := 8) (o := 0) (u := 4) (v := 5) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_32 : Slice r_46 g_46 (fiDom 0 1 1 5 true) 7 := by
  have hc : Lower (varsOf 30) 0xfff3f330fff3f330 7 := carry_of (swaps := [(0,4),(1,3),(2,4)]) (by decide +kernel) low_21
  exact slice_fi (z := 0) (o := 1) (u := 1) (v := 5) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_33 : Slice r_46 g_46 (identDom 1 2) 8 := by
  have hc : Lower (varsOf 59) 0xffffeecccc88cc00 8 := carry_of (swaps := [(1,4),(2,5),(3,4),(4,5)]) (by decide +kernel) low_36
  exact slice_ident (u := 1) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_34 : Slice r_46 g_46 (subcubeFast 24 32) 4 := by
  exact slice_fast_direct_f (z := 24) (o := 32) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_46_35 : Slice r_46 g_46 (subcubeFast 3 4) 4 := by
  have hc : Lower (varsOf 56) 0xffffff00ff000000 4 := carry_of (swaps := [(0,3),(1,4),(2,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 3) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_36 : Slice r_46 g_46 (subcubeFast 3 8) 4 := by
  have hc : Lower (varsOf 52) 0xfffff0f0f0f00000 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 3) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_37 : Slice r_46 g_46 (subcubeFast 32 3) 4 := by
  have hc : Lower (varsOf 28) 0xfff0f000fff0f000 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 32) (o := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_38 : Slice r_46 g_46 (subcubeFast 17 4) 4 := by
  have hc : Lower (varsOf 42) 0xffccffcccc00cc00 4 := carry_of (swaps := [(0,3),(1,3),(2,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 17) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_39 : Slice r_46 g_46 (subcubeFast 32 5) 4 := by
  have hc : Lower (varsOf 26) 0xffcccc00ffcccc00 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 32) (o := 5) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_40 : Slice r_46 g_46 (subcubeFast 33 8) 4 := by
  have hc : Lower (varsOf 22) 0xfcfcc0c0fcfcc0c0 4 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 33) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_41 : Slice r_46 g_46 (subcubeFast 32 9) 4 := by
  have hc : Lower (varsOf 22) 0xfcfcc0c0fcfcc0c0 4 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 32) (o := 9) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_42 : Slice r_46 g_46 (subcubeFast 32 17) 4 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 32) (o := 17) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_43 : Slice r_46 g_46 (subcubeFast 18 32) 4 := by
  have hc : Lower (varsOf 13) 0xfaa0faa0faa0faa0 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 18) (o := 32) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_44 : Slice r_46 g_46 (fiDom 0 8 0 1 true) 6 := by
  have hc : Lower (varsOf 53) 0xfffffafaf5f55050 6 := carry_of (swaps := [(0,3),(1,4),(2,4),(3,5)]) (by decide +kernel) low_25
  exact slice_fi (z := 0) (o := 8) (u := 0) (v := 1) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_45 : Slice r_46 g_46 (fiDom 16 0 2 5 true) 6 := by
  have hc : Lower (varsOf 15) 0xca08ca08ca08ca08 6 := carry_of (swaps := [(0,2),(1,2),(2,3)]) (by decide +kernel) low_26
  exact slice_fi (z := 16) (o := 0) (u := 2) (v := 5) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_46 : Slice r_46 g_46 (fiDom 4 0 4 5 true) 6 := by
  have hc : Lower (varsOf 27) 0xcc00aa88cc00aa88 6 := carry_of (swaps := [(0,2),(1,2),(2,4),(3,4)]) (by decide +kernel) low_26
  exact slice_fi (z := 4) (o := 0) (u := 4) (v := 5) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_47 : Slice r_46 g_46 (fiDom 0 2 4 5 true) 6 := by
  have hc : Lower (varsOf 29) 0xffa0fafaffa0fafa 6 := carry_of (swaps := [(0,1),(1,4),(3,4)]) (by decide +kernel) low_25
  exact slice_fi (z := 0) (o := 2) (u := 4) (v := 5) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_48 : Slice r_46 g_46 (fiDom 0 2 2 5 true) 6 := by
  have hc : Lower (varsOf 29) 0xffaffa0affaffa0a 6 := carry_of (swaps := [(0,1),(1,4),(2,3),(3,4)]) (by decide +kernel) low_25
  exact slice_fi (z := 0) (o := 2) (u := 2) (v := 5) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_49 : Slice r_46 g_46 (fiDom 16 0 0 5 false) 6 := by
  have hc : Lower (varsOf 15) 0xeaa8eaa8eaa8eaa8 6 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_2
  exact slice_fi (z := 16) (o := 0) (u := 0) (v := 5) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_50 : Slice r_46 g_46 (fiDom 4 0 0 5 false) 6 := by
  have hc : Lower (varsOf 27) 0xeeaaaa88eeaaaa88 6 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_2
  exact slice_fi (z := 4) (o := 0) (u := 0) (v := 5) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_51 : Slice r_46 g_46 (fiDom 0 2 3 5 false) 6 := by
  have hc : Lower (varsOf 29) 0xffa0fa00ffa0fa00 6 := carry_of (swaps := [(1,4),(2,4)]) (by decide +kernel) low_2
  exact slice_fi (z := 0) (o := 2) (u := 3) (v := 5) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_52 : Slice r_46 g_46 (fiDom 1 0 2 5 false) 6 := by
  have hc : Lower (varsOf 30) 0xfcf0f0c0fcf0f0c0 6 := carry_of (swaps := [(0,4),(1,4),(2,3),(3,4)]) (by decide +kernel) low_2
  exact slice_fi (z := 1) (o := 0) (u := 2) (v := 5) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_53 : Slice r_46 g_46 (fiDom 16 0 2 3 false) 5 := by
  have hc : Lower (varsOf 39) 0xf8f8f8f8c0c0c0c0 5 := carry_of (swaps := [(2,3),(3,4),(4,5)]) (by decide +kernel) low_8
  exact slice_fi (z := 16) (o := 0) (u := 2) (v := 3) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_54 : Slice r_46 g_46 (fiDom 1 0 1 3 true) 5 := by
  have hc : Lower (varsOf 54) 0xfffff0f030300000 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,5)]) (by decide +kernel) low_37
  exact slice_fi (z := 1) (o := 0) (u := 1) (v := 3) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_55 : Slice r_46 g_46 (fiDom 0 8 1 5 false) 5 := by
  have hc : Lower (varsOf 23) 0xfcfcc8c8fcfcc8c8 5 := carry_of (swaps := [(1,3),(2,3),(3,4)]) (by decide +kernel) low_16
  exact slice_fi (z := 0) (o := 8) (u := 1) (v := 5) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_56 : Slice r_46 g_46 (fiDom 0 8 0 5 true) 5 := by
  have hc : Lower (varsOf 23) 0xfdfdd0d0fdfdd0d0 5 := carry_of (swaps := [(0,1),(3,4)]) (by decide +kernel) low_38
  exact slice_fi (z := 0) (o := 8) (u := 0) (v := 5) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_57 : Slice r_46 g_46 (fiDom 0 8 0 2 true) 5 := by
  have hc : Lower (varsOf 51) 0xffffffffdddd4444 5 := carry_of (swaps := [(0,2),(1,2),(2,4),(3,5)]) (by decide +kernel) low_27
  exact slice_fi (z := 0) (o := 8) (u := 0) (v := 2) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_58 : Slice r_46 g_46 (fiDom 0 8 0 2 false) 5 := by
  have hc : Lower (varsOf 51) 0xffffaaaaeeee8888 5 := carry_of (swaps := [(0,2),(1,2),(2,4),(3,5),(4,5)]) (by decide +kernel) low_14
  exact slice_fi (z := 0) (o := 8) (u := 0) (v := 2) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_59 : Slice r_46 g_46 (fiDom 1 0 1 2 true) 5 := by
  have hc : Lower (varsOf 58) 0xffff3300ff000000 5 := carry_of (swaps := [(0,4),(1,4),(2,5),(3,4)]) (by decide +kernel) low_37
  exact slice_fi (z := 1) (o := 0) (u := 1) (v := 2) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_60 : Slice r_46 g_46 (fiDom 0 32 1 3 false) 5 := by
  have hc : Lower (varsOf 23) 0xffffe8e8ffffe8e8 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_3
  exact slice_fi (z := 0) (o := 32) (u := 1) (v := 3) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_61 : Slice r_46 g_46 (fiDom 1 0 2 4 true) 5 := by
  have hc : Lower (varsOf 46) 0xffcfffcfcc00cc00 5 := carry_of (swaps := [(0,4),(2,4),(3,4),(4,5)]) (by decide +kernel) low_39
  exact slice_fi (z := 1) (o := 0) (u := 2) (v := 4) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_62 : Slice r_46 g_46 (fiDom 1 0 2 3 false) 5 := by
  have hc : Lower (varsOf 54) 0xfffff0f0f0f0c0c0 5 := carry_of (swaps := [(0,4),(1,4),(2,3),(3,5)]) (by decide +kernel) low_16
  exact slice_fi (z := 1) (o := 0) (u := 2) (v := 3) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_63 : Slice r_46 g_46 (fiDom 8 0 2 4 false) 5 := by
  have hc : Lower (varsOf 39) 0xf8f8f8f880808080 5 := carry_of (swaps := [(3,4),(4,5)]) (by decide +kernel) low_6
  exact slice_fi (z := 8) (o := 0) (u := 2) (v := 4) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_64 : Slice r_46 g_46 (fiDom 4 0 3 5 true) 5 := by
  have hc : Lower (varsOf 27) 0xccff0088ccff0088 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_40
  exact slice_fi (z := 4) (o := 0) (u := 3) (v := 5) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_65 : Slice r_46 g_46 (fiDom 4 0 3 4 false) 5 := by
  have hc : Lower (varsOf 43) 0xff88ff88cc00cc00 5 := carry_of (swaps := [(2,4),(4,5)]) (by decide +kernel) low_8
  exact slice_fi (z := 4) (o := 0) (u := 3) (v := 4) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_66 : Slice r_46 g_46 (fiDom 4 0 1 4 false) 5 := by
  have hc : Lower (varsOf 43) 0xeecceecccc00cc00 5 := carry_of (swaps := [(1,3),(2,4),(4,5)]) (by decide +kernel) low_8
  exact slice_fi (z := 4) (o := 0) (u := 1) (v := 4) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_67 : Slice r_46 g_46 (fiDom 4 0 1 3 false) 5 := by
  have hc : Lower (varsOf 51) 0xffff8888cccc0000 5 := carry_of (swaps := [(2,4),(3,5),(4,5)]) (by decide +kernel) low_8
  exact slice_fi (z := 4) (o := 0) (u := 1) (v := 3) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_68 : Slice r_46 g_46 (fiDom 0 2 2 4 false) 5 := by
  have hc : Lower (varsOf 45) 0xfafafafaf0a0f0a0 5 := carry_of (swaps := [(0,1),(1,4),(2,3),(3,4),(4,5)]) (by decide +kernel) low_16
  exact slice_fi (z := 0) (o := 2) (u := 2) (v := 4) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_69 : Slice r_46 g_46 (fiDom 4 0 1 5 true) 5 := by
  have hc : Lower (varsOf 27) 0xff332200ff332200 5 := carry_of (swaps := [(1,2),(2,4),(3,4)]) (by decide +kernel) low_40
  exact slice_fi (z := 4) (o := 0) (u := 1) (v := 5) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_70 : Slice r_46 g_46 (fiDom 0 2 0 2 false) 5 := by
  have hc : Lower (varsOf 57) 0xffffaaaaffaaaa00 5 := carry_of (swaps := [(0,2),(1,4),(2,5),(3,5),(4,5)]) (by decide +kernel) low_14
  exact slice_fi (z := 0) (o := 2) (u := 0) (v := 2) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_71 : Slice r_46 g_46 (fiDom 2 0 3 4 false) 5 := by
  have hc : Lower (varsOf 45) 0xffa0ffa0f000f000 5 := carry_of (swaps := [(1,4),(2,4),(4,5)]) (by decide +kernel) low_8
  exact slice_fi (z := 2) (o := 0) (u := 3) (v := 4) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_72 : Slice r_46 g_46 (fiDom 2 0 2 4 false) 5 := by
  have hc : Lower (varsOf 45) 0xfaf0faf0f000f000 5 := carry_of (swaps := [(1,4),(2,3),(3,4),(4,5)]) (by decide +kernel) low_8
  exact slice_fi (z := 2) (o := 0) (u := 2) (v := 4) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_73 : Slice r_46 g_46 (fiDom 0 4 4 5 true) 5 := by
  have hc : Lower (varsOf 27) 0xff88ffeeff88ffee 5 := carry_of (swaps := [(2,4)]) (by decide +kernel) low_27
  exact slice_fi (z := 0) (o := 4) (u := 4) (v := 5) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_74 : Slice r_46 g_46 (fiDom 8 0 1 5 true) 5 := by
  have hc : Lower (varsOf 23) 0xb3b32020b3b32020 5 := carry_of (swaps := [(1,3),(2,3),(3,4)]) (by decide +kernel) low_41
  exact slice_fi (z := 8) (o := 0) (u := 1) (v := 5) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_75 : Slice r_46 g_46 (fiDom 0 4 1 5 true) 5 := by
  have hc : Lower (varsOf 27) 0xffbbff22ffbbff22 5 := carry_of (swaps := [(1,2),(2,4)]) (by decide +kernel) low_27
  exact slice_fi (z := 0) (o := 4) (u := 1) (v := 5) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_76 : Slice r_46 g_46 (fiDom 0 2 3 4 true) 5 := by
  have hc : Lower (varsOf 45) 0xfafffafff0a0f0a0 5 := carry_of (swaps := [(1,4),(3,4),(4,5)]) (by decide +kernel) low_43
  exact slice_fi (z := 0) (o := 2) (u := 3) (v := 4) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_77 : Slice r_46 g_46 (fiDom 1 0 2 3 true) 5 := by
  have hc : Lower (varsOf 54) 0xffffc0c00c0c0000 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,5),(4,5)]) (by decide +kernel) low_45
  exact slice_fi (z := 1) (o := 0) (u := 2) (v := 3) (fl := true) (by decide +kernel) hc
def S_46 : BT (Option (Nat × Nat)) := btOfList 7 [some (subcubeFast 0 1,9),some (subcubeFast 8 0,9),some (subcubeFast 16 0,9),some (identDom 0 1,10),some (subcubeFast 32 0,8),some (subcubeFast 32 1,7),some (subcubeFast 1 0,8),some (subcubeFast 0 4,8),some (fiDom 0 0 4 5 true,9),some (subcubeFast 2 0,8),some (fiDom 0 0 3 5 true,8),some (fiDom 0 0 1 5 true,8),some (fiDom 0 0 2 5 true,8),some (subcubeFast 4 0,7),some (subcubeFast 0 2,7),some (subcubeFast 0 8,7),some (fiDom 0 4 0 4 false,7),some (fiDom 0 8 0 1 false,7),some (fiDom 32 0 0 2 false,7),some (fiDom 32 0 0 4 false,7),some (fiDom 0 4 0 1 false,7),some (subcubeFast 8 1,6),some (subcubeFast 16 1,6),some (subcubeFast 4 1,6),some (subcubeFast 8 2,6),some (subcubeFast 8 4,6),some (subcubeFast 2 1,6),some (fiDom 32 0 0 3 true,7),some (fiDom 0 1 4 5 true,7),some (fiDom 0 1 3 5 true,7),some (fiDom 0 4 0 5 true,7),some (fiDom 8 0 4 5 true,7),some (fiDom 0 1 1 5 true,7),some (identDom 1 2,8),some (subcubeFast 24 32,4),some (subcubeFast 3 4,4),some (subcubeFast 3 8,4),some (subcubeFast 32 3,4),some (subcubeFast 17 4,4),some (subcubeFast 32 5,4),some (subcubeFast 33 8,4),some (subcubeFast 32 9,4),some (subcubeFast 32 17,4),some (subcubeFast 18 32,4),some (fiDom 0 8 0 1 true,6),some (fiDom 16 0 2 5 true,6),some (fiDom 4 0 4 5 true,6),some (fiDom 0 2 4 5 true,6),some (fiDom 0 2 2 5 true,6),some (fiDom 16 0 0 5 false,6),some (fiDom 4 0 0 5 false,6),some (fiDom 0 2 3 5 false,6),some (fiDom 1 0 2 5 false,6),some (fiDom 16 0 2 3 false,5),some (fiDom 1 0 1 3 true,5),some (fiDom 0 8 1 5 false,5),some (fiDom 0 8 0 5 true,5),some (fiDom 0 8 0 2 true,5),some (fiDom 0 8 0 2 false,5),some (fiDom 1 0 1 2 true,5),some (fiDom 0 32 1 3 false,5),some (fiDom 1 0 2 4 true,5),some (fiDom 1 0 2 3 false,5),some (fiDom 8 0 2 4 false,5),some (fiDom 4 0 3 5 true,5),some (fiDom 4 0 3 4 false,5),some (fiDom 4 0 1 4 false,5),some (fiDom 4 0 1 3 false,5),some (fiDom 0 2 2 4 false,5),some (fiDom 4 0 1 5 true,5),some (fiDom 0 2 0 2 false,5),some (fiDom 2 0 3 4 false,5),some (fiDom 2 0 2 4 false,5),some (fiDom 0 4 4 5 true,5),some (fiDom 8 0 1 5 true,5),some (fiDom 0 4 1 5 true,5),some (fiDom 0 2 3 4 true,5),some (fiDom 1 0 2 3 true,5)]
lemma S_46_ok : btAll (fun o => ∀ p, o = some p → Slice r_46 g_46 p.1 p.2) S_46 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_46_0) (forall_cons (fun _ h => by cases h; exact sl_46_1) (forall_cons (fun _ h => by cases h; exact sl_46_2) (forall_cons (fun _ h => by cases h; exact sl_46_3) (forall_cons (fun _ h => by cases h; exact sl_46_4) (forall_cons (fun _ h => by cases h; exact sl_46_5) (forall_cons (fun _ h => by cases h; exact sl_46_6) (forall_cons (fun _ h => by cases h; exact sl_46_7) (forall_cons (fun _ h => by cases h; exact sl_46_8) (forall_cons (fun _ h => by cases h; exact sl_46_9) (forall_cons (fun _ h => by cases h; exact sl_46_10) (forall_cons (fun _ h => by cases h; exact sl_46_11) (forall_cons (fun _ h => by cases h; exact sl_46_12) (forall_cons (fun _ h => by cases h; exact sl_46_13) (forall_cons (fun _ h => by cases h; exact sl_46_14) (forall_cons (fun _ h => by cases h; exact sl_46_15) (forall_cons (fun _ h => by cases h; exact sl_46_16) (forall_cons (fun _ h => by cases h; exact sl_46_17) (forall_cons (fun _ h => by cases h; exact sl_46_18) (forall_cons (fun _ h => by cases h; exact sl_46_19) (forall_cons (fun _ h => by cases h; exact sl_46_20) (forall_cons (fun _ h => by cases h; exact sl_46_21) (forall_cons (fun _ h => by cases h; exact sl_46_22) (forall_cons (fun _ h => by cases h; exact sl_46_23) (forall_cons (fun _ h => by cases h; exact sl_46_24) (forall_cons (fun _ h => by cases h; exact sl_46_25) (forall_cons (fun _ h => by cases h; exact sl_46_26) (forall_cons (fun _ h => by cases h; exact sl_46_27) (forall_cons (fun _ h => by cases h; exact sl_46_28) (forall_cons (fun _ h => by cases h; exact sl_46_29) (forall_cons (fun _ h => by cases h; exact sl_46_30) (forall_cons (fun _ h => by cases h; exact sl_46_31) (forall_cons (fun _ h => by cases h; exact sl_46_32) (forall_cons (fun _ h => by cases h; exact sl_46_33) (forall_cons (fun _ h => by cases h; exact sl_46_34) (forall_cons (fun _ h => by cases h; exact sl_46_35) (forall_cons (fun _ h => by cases h; exact sl_46_36) (forall_cons (fun _ h => by cases h; exact sl_46_37) (forall_cons (fun _ h => by cases h; exact sl_46_38) (forall_cons (fun _ h => by cases h; exact sl_46_39) (forall_cons (fun _ h => by cases h; exact sl_46_40) (forall_cons (fun _ h => by cases h; exact sl_46_41) (forall_cons (fun _ h => by cases h; exact sl_46_42) (forall_cons (fun _ h => by cases h; exact sl_46_43) (forall_cons (fun _ h => by cases h; exact sl_46_44) (forall_cons (fun _ h => by cases h; exact sl_46_45) (forall_cons (fun _ h => by cases h; exact sl_46_46) (forall_cons (fun _ h => by cases h; exact sl_46_47) (forall_cons (fun _ h => by cases h; exact sl_46_48) (forall_cons (fun _ h => by cases h; exact sl_46_49) (forall_cons (fun _ h => by cases h; exact sl_46_50) (forall_cons (fun _ h => by cases h; exact sl_46_51) (forall_cons (fun _ h => by cases h; exact sl_46_52) (forall_cons (fun _ h => by cases h; exact sl_46_53) (forall_cons (fun _ h => by cases h; exact sl_46_54) (forall_cons (fun _ h => by cases h; exact sl_46_55) (forall_cons (fun _ h => by cases h; exact sl_46_56) (forall_cons (fun _ h => by cases h; exact sl_46_57) (forall_cons (fun _ h => by cases h; exact sl_46_58) (forall_cons (fun _ h => by cases h; exact sl_46_59) (forall_cons (fun _ h => by cases h; exact sl_46_60) (forall_cons (fun _ h => by cases h; exact sl_46_61) (forall_cons (fun _ h => by cases h; exact sl_46_62) (forall_cons (fun _ h => by cases h; exact sl_46_63) (forall_cons (fun _ h => by cases h; exact sl_46_64) (forall_cons (fun _ h => by cases h; exact sl_46_65) (forall_cons (fun _ h => by cases h; exact sl_46_66) (forall_cons (fun _ h => by cases h; exact sl_46_67) (forall_cons (fun _ h => by cases h; exact sl_46_68) (forall_cons (fun _ h => by cases h; exact sl_46_69) (forall_cons (fun _ h => by cases h; exact sl_46_70) (forall_cons (fun _ h => by cases h; exact sl_46_71) (forall_cons (fun _ h => by cases h; exact sl_46_72) (forall_cons (fun _ h => by cases h; exact sl_46_73) (forall_cons (fun _ h => by cases h; exact sl_46_74) (forall_cons (fun _ h => by cases h; exact sl_46_75) (forall_cons (fun _ h => by cases h; exact sl_46_76) (forall_cons (fun _ h => by cases h; exact sl_46_77) (fun _ h => (List.not_mem_nil h).elim)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
set_option maxRecDepth 500000 in
def ps_46 : BT (Option PoolSpec) := btOfList 9 [q 35 [],q 36 [],q 34 [],q 37 [],q 15 [16417,40967],q 9 [],q 43 [],q 23 [],q 15 [],q 68 [],q 42 [],q 16 [],q 24 [8295],q 15 [8295],q 40 [],q 24 [],q 2 [],q 4 [],q 25 [],q 14 [],q 1 [49160,16434,8295],q 25 [16434],q 1 [49160,16457,16434],q 2 [12293,49160],q 6 [],q 73 [],q 24 [16457],q 72 [],q 26 [],q 39 [],q 7 [],q 13 [12293],q 53 [],q 71 [],q 21 [],q 1 [],q 28 [],q 0 [],q 46 [],q 25 [20528],q 14 [16393],q 15 [16393],q 47 [16393],q 38 [],q 23 [20497],q 76 [],q 24 [8192],q 32 [],q 33 [20495,16641],q 20 [12617],q 0 [12617,16393,53580],q 0 [12293,16393,53296],q 2 [12293,53296],q 2 [12293,8292],q 24 [16394],q 30 [12293],q 64 [],q 1 [16394,49239,20528],q 15 [16394],q 47 [],q 31 [],q 1 [49160,16394,20528],q 67 [],q 5 [],q 2 [20484,12313,28680,32770],q 15 [16417],q 31 [614407],q 50 [],q 22 [],q 41 [],q 74 [],q 31 [614404],q 61 [20493],q 2 [20493,110600],q 15 [16569],q 24 [110600],q 17 [],q 2 [12293,20528],q 45 [],q 23 [12293],q 1 [49160,16394],q 23 [12617],q 9 [16414],q 19 [],q 69 [],q 25 [20485],q 2 [8199,242035],q 2 [8199],q 21 [20497],q 21 [8199],q 2 [20485,143368],q 31 [8199],q 2 [8197,242096],q 2 [20484,12313],q 1 [49160,16458],q 15 [16458],q 9 [16682],q 7 [20497],q 8 [],q 2 [20480,12293,49555],q 33 [20493],q 33 [16397],q 9 [16394],q 75 [],q 2 [20486,20487],q 1 [20480,16394,409685],q 30 [],q 24 [8194],q 25 [20497],q 1 [20486,8271],q 6 [20497],q 31 [8192],q 23 [16737],q 21 [16389],q 21 [16701],q 32 [16701],q 24 [16386],q 70 [],q 48 [],q 1 [49160,16457],q 25 [16457],q 15 [16457],q 47 [16457],q 1 [49160,16434],q 20 [],q 32 [16390],q 1 [20480,16785],q 25 [20530],q 33 [20499],q 2 [8196,8197],q 1 [16394,49239],q 2 [12293,49239],q 2 [12293],q 1 [20480,16394],q 13 [16389],q 7 [16389,17381],q 6 [20485],q 5 [8547],q 24 [8547],q 1 [20528,331786],q 0 [12617,16393],q 61 [],q 65 [],q 31 [8196],q 2 [12293,241672],q 63 [],q 24 [16737],q 2 [241664],q 17 [16393],q 2 [20493,110644],q 21 [20485],q 21 [16394],q 2 [8391],q 22 [8199],q 7 [20485],q 2 [20485,143412],q 31 [8197],q 2 [12297,241864],q 24 [20480],q 29 [],q 2 [8192,241671],q 33 [20495],q 6 [16389],q 32 [16797],q 2 [20490,20491],q 23 [12569],q 24 [20480,16785],q 18 [16389],q 6 [16389,20822],q 15 [16481],q 6 [20485,143379],q 33 [20497],q 21 [8595],q 2 [12293,49163],q 29 [16393],q 1 [16394,20567],q 31 [4096],q 54 [],q 23 [16785],q 7 [16389,20822],q 7 [20485,143379],q 31 [8198],q 21 [8475],q 48 [16394],q 25 [50151],q 1 [20488,17381],q 7 [17381],q 1 [20490,49655],q 1 [16434,8295],q 2 [12293,8295],q 31 [8192,16701],q 2 [12293,241664],q 2 [20489,160084],q 7 [16389],q 2 [12293,241712],q 31 [4096,16713],q 13 [16397],q 25 [373735],q 0 [12605,16389],q 7 [16389,349159],q 2 [20489,159744],q 2 [20493,110932],q 9 [16394,49239],q 2 [20820,532490],q 2 [20820,532493],q 9 [143368],q 51 [8391],q 1 [49160,20528],q 2 [12297,204999],q 66 [],q 1 [20484,8219],q 5 [28680],q 27 [],q 9 [28680],q 2 [20484,12313,28680],q 1 [20484,16409],q 23 [12689],q 2 [12298],q 14 [16689],q 33 [],q 13 [20486],q 55 [],q 4 [241672],q 24 [126984],q 1 [16394,20528],q 25 [17678],q 25 [17381],q 21 [8196],q 5 [8196],q 50 [12293],q 3 [],q 2 [241671],q 2 [20493],q 10 [],q 1 [110600],q 2 [20493,110599],q 2 [372744],q 2 [20491,13045],q 12 [],q 52 [],q 3 [20490,16885],q 1 [20490],q 9 [20488],q 1 [20488],q 2 [20488],q 2 [20488,13285],q 4 [110600],q 7 [1019909],q 1 [16394],q 17 [16394],q 29 [16394],q 2 [20565],q 2 [4181],q 2 [20495],q 23 [16397],q 2 [241672],q 2 [12297],q 2 [8199,12658],q 2 [12294],q 2 [20487],q 2 [348160],q 1 [16390,8391],q 13 [20495],q 1 [8196],q 59 [],q 1 [49160],q 62 [],q 2 [20482],q 0 [16389],q 3 [16394],q 44 [],q 1 [4096],q 2 [20489,159751],q 1 [8192],q 0 [12293],q 2 [20480,12293],q 2 [20486,8271],q 0 [16389,12297],q 7 [20773],q 1 [20480,8595],q 2 [20480],q 11 [16397],q 1 [20484],q 2 [53263],q 13 [20487],q 3 [20490],q 2 [8197],q 2 [8196],q 2 [8194],q 0 [8197,16397],q 57 [],q 2 [8192],q 2 [12290],q 9 [16434],q 1 [16434],q 2 [12293,49152],q 2 [20567],q 33 [20482],q 24 [20482],q 3 [20486],q 2 [20484],q 1 [8196,16677],q 7 [16677],q 2 [8679],q 1 [4096,8523],q 77 [],q 0 [12605],q 2 [8192,12605],q 2 [20485,143360],q 9 [143360],q 2 [20486],q 2 [8196,12581],q 2 [20489],q 0 [16397],q 2 [8196,8487],q 2 [241679],q 0 [16393],q 2 [53255],q 1 [372736],q 1 [16390],q 2 [8198,12541],q 58 [],q 9 [16818],q 2 [8194,12701],q 2 [4096],q 1 [20480],q 2 [12294,8667],q 1 [4096,16713],q 2 [8198],q 56 [],q 2 [20820],q 0 [8197],q 4 [143368],q 33 [12290],q 1 [8192,16701],q 2 [20491],q 1 [20846],q 1 [16386,8475],q 2 [8199,12657],q 32 [16394],q 2 [20485],q 1 [20486],q 9 [49160],q 0 [12293,16393],q 2 [348168],q 2 [20480,12689],q 2 [12485],q 1 [20528],q 1 [20499],q 60 [],q 2 [372743],q 23 [12294],q 3 [20497],q 3 [16390],q 25 [16389],q 23 [16389],q 2 [348171],q 2 [20490],q 2 [12298,4477],q 2 [348175],q 2 [20822],q 0 [12617],q 2 [4096,12617],q 1 [20530],q 2 [20484,8219],q 49 [],q 2 [12373],q 1 [16386],q 2 [12773],q 2 [8197,12722],q 2 [12297,204807],q 2 [4581],q 1 [20482],q 0 [12297]]
def B_46_4 : BT (List (List Nat)) := BT.empty
lemma B_46_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_46 4 xs.toFinset) B_46_4 := .empty
def U_46_5 : List Nat := []
def P_46_5 : BT (Option BoundPool) := buildPoolsSubBT 9 W_46 r_46 S_46 ps_46 U_46_5
def N_46_5 : List NodeSpec := [([9,11,2,7,4,5],[],[]),([17,0,1,2,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_46_5 : checkNodesBT W_46 g_46 F_46 P_46_5 A_46 B_46_4 5 N_46_5 = true := by decide +kernel
def B_46_5 : BT (List (List Nat)) := buildBucketsBT W_46 N_46_5
set_option maxRecDepth 500000 in
lemma B_46_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_46 5 xs.toFinset) B_46_5 :=
  buildBucketsBT_sound (by decide) gp_46 W_46_ok (buildPoolsSubBT_sound S_46_ok) A_46_ok B_46_4_ok C_46_5
def U_46_6 : List Nat := (r 0 7)
def P_46_6 : BT (Option BoundPool) := buildPoolsSubBT 9 W_46 r_46 S_46 ps_46 U_46_6
def N_46_6 : List NodeSpec := [([9,1,2,7,4,10,5],[0],[0]),([0,18,3,20,4,13,5],[1],[]),([21,0,18,3,20,4,5],[2],[]),([37,0,2,12,4,36,5],[2],[]),([11,0,8,2,7,4,5],[3,4],[0]),([0,2,3,14,20,4,5],[5],[]),([29,0,2,12,4,28,5],[6],[]),([0,2,3,22,20,4,5],[],[]),([0,1,2,3,14,23,5],[],[]),([19,24,0,26,3,4,5],[],[]),([32,0,1,34,3,4,5],[],[]),([0,1,2,3,15,4,16],[],[0]),([38,0,1,3,14,4,5],[],[]),([41,21,0,1,3,4,5],[],[]),([42,0,1,2,3,14,5],[],[]),([43,44,0,1,2,3,4],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_46_6 : checkNodesBT W_46 g_46 F_46 P_46_6 A_46 B_46_5 6 N_46_6 = true := by decide +kernel
def B_46_6 : BT (List (List Nat)) := buildBucketsBT W_46 N_46_6
set_option maxRecDepth 500000 in
lemma B_46_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_46 6 xs.toFinset) B_46_6 :=
  buildBucketsBT_sound (by decide) gp_46 W_46_ok (buildPoolsSubBT_sound S_46_ok) A_46_ok B_46_5_ok C_46_6
def U_46_7_0 : List Nat := (r 0 4++r 5 58)
def P_46_7_0 : BT (Option BoundPool) := buildPoolsSubBT 9 W_46 r_46 S_46 ps_46 U_46_7_0
def N_46_7_0 : List NodeSpec := [e6 [163] [0,2],([118,0,2,3,4,36,5],[0,2],[]),([48,1,46,3,4,5],[1,2],[]),([0,2,3,4,58,5],[1,2],[]),([21,0,1,3,126,12,4,5],[2],[]),([0,1,3,126,12,4,13,5],[2],[]),e6 [139,12] [2],e6 [36] [2,0],([112,1,2,3,4,36,5],[2,0],[]),([0,18,2,3,20,4,5],[1,2,3],[0]),([0,2,3,20,12,4,13,5],[2,0,1,3],[0]),e6 [52,14] [2,3],e6 [52,110] [2,3],e6 [52,22] [2,3],([52,21,0,1,18,3,4,5],[3,2],[]),([52,21,24,0,1,3,4,5],[3,2],[]),([52,0,1,18,3,4,13,5],[3,2],[]),e6 [52,26] [3,2],([105,1,2,3,106,5],[0,6],[]),([0,73,109,3,4,5],[1,6],[]),([0,76,2,3,4,77,5],[2,6],[]),e6 [123] [3,6],u6 [37,36] [2,8],([0,45,46,2,47,3,4,5],[7,5,8],[]),e6 [116,31] [8],e6 [136,21] [7,2,9],([141,0,2,7,4,5],[0,10],[]),e6 [55] [0,10],e6 [78,104] [2,10],e6 [25,126] [2,10],e6 [127,51] [2,10],([19,25,24,0,2,3,4,5],[2,10],[0]),([0,1,132,2,4,85,131,5],[3,1,10,6],[]),e6 [124,109] [6,10],e6 [158] [6,10],e6 [97] [10,2],([19,0,26,2,3,12,4,5],[3,12,2],[0]),([24,0,1,26,3,4,5],(r 9 4++[3,13]),[0]),e6 [52,56] [3,2,14],e6 [119] [3,14,7,11],e6 [138] [14,2],e6 [109,117] [6,15,10],([19,25,0,18,2,3,4,5],[15,2,0,10],[]),([0,1,2,109,4,91,5],[1,15,16,3],[]),([49,0,2,3,51,4,5],[14,0,15,16],[]),u6 [44,14] [2,17],u6 [43,14] [17,2],([19,0,18,3,12,4,13,5],[18,3,1],[0]),([19,0,2,3,14,12,4,5],[18,5,3,15],[0]),e6 [86,104] [18,8],([19,0,2,3,12,4,110,5],[18,10],[]),e6 [28,164] [6,19,10],([19,21,24,0,3,12,4,5],[18,19],[]),([19,21,0,18,3,12,4,5],[18,19,2],[0]),([21,0,2,3,20,12,4,5],[19,2,0],[0]),u6 [29,28] [19,6],([25,0,1,18,26,3,4,5],[10,18,19,20],[]),([25,0,1,18,53,3,4,5],[10,7,1,21],[]),([25,142,1,2,3,4,5],[10,21,1],[]),([25,0,1,18,2,3,54,5],[7,22,19,2,8],[]),e6 [52,54] [23,10,2,3],e6 [149] [24,5,2,7],e6 [61] [24,5,3,2,25,9],([0,62,2,3,12,4,54,5],[26,1,10],[]),([19,0,2,3,12,4,54,5],[26,3,1,10],[]),([19,56,0,2,3,12,4,5],[27,28,1],[]),e6 [66] [1,29],e6 [33,87] [8,15,29,7],u6 [34,31] [14,29,15,7],([0,1,2,55,7,4,5],[29,0,10],[]),([114,1,2,3,4,36,5],[29,2],[]),([25,48,1,2,3,4,5],[29,7,1,2],[]),e6 [143] [29,14,5,3],([144,0,1,2,4,85,131,5],[29,15,6,1],[]),([25,24,0,1,26,3,4,5],[10,30],[]),e6 [129] [14,10,7,30],e6 [99] [24,2,7,30],e6 [98,31] [30],u6 [33,32] [30,15,8],e6 [111] [30,19,1,6],e6 [24,67] [30,2,10,31,3],([68,0,1,26,3,12,4,5],[9,32,33],[]),e6 [25,14] [18,32,33],e6 [69,54] [24,3,28,34],e6 [78,80] [24,34,10,2],e6 [86,80] [34,24,8,2,3],e6 [98] [16,19,29,35,8],e6 [113] [29,5,19,35,8],e6 [72] [14,7,30,35,36],e6 [102,92] [19,0,36,1],e6 [75] [24,37,6,38],([38,0,1,3,12,4,13,5],[2,39],[0]),([0,2,3,12,4,36,5],[40,2,9,29],[0]),([0,1,2,12,4,28,5],[18,6,41,29],[0]),([0,1,18,3,81,4,13,5],[39,40,2,41,42,38,3],[]),e6 [84] [3,43],e6 [21,156] [7,43,0],([21,0,1,3,12,4,40,5],[7,43,18],[0]),e6 [147,12] [10,43,0],e6 [25,22] [43,9,33],([21,0,1,3,90,4,5],[43,18,6],[]),([21,0,1,3,126,4,5],[43,29],[]),e6 [88,89] [24,34,44],e6 [120,91] [8,2,45],e6 [91,94] [45,2],e6 [107] [29,1,46,16,10],([21,78,112,1,2,3,5],[19,43,47,2],[]),([0,73,108,3,4,65,5],[48,1,3],[]),e6 [115] [49,43,50,17,2],u6 [14,81] [39,40,41,2,17,42,52],u6 [15,14] [51,0,18,2,52,17],([25,0,1,2,3,12,54,5],[9,53,33],[]),([19,0,2,3,22,12,4,5],[54],[0]),u6 [14,16] [0,55,40,41,2,17],e6 [134] [24,37,5,19,2,56],e6 [22,81] [57,9,43,31,58],([0,73,140,3,4,5],[6,43,59,3],[]),e6 [145] [1,19,17,60],([21,0,1,18,3,81,4,5],[59,61,9,2,58],[]),([0,1,2,146,7,4,5],[5,15,10,8,62],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_46_7_0 : checkNodesBT W_46 g_46 F_46 P_46_7_0 A_46 B_46_6 7 N_46_7_0 = true := by decide +kernel
def U_46_7_1 : List Nat := ([0,2,5,6,10,14,15,19,24,25,28,29,34,47]++r 62 11)
def P_46_7_1 : BT (Option BoundPool) := buildPoolsSubBT 9 W_46 r_46 S_46 ps_46 U_46_7_1
def N_46_7_1 : List NodeSpec := [([9,1,8,2,7,4,5],[63,0,14,62,64],[0]),([0,1,8,2,7,4,10,5],[10,0,62,6,65],[0]),e6 [151,150] [5,25,66],([112,1,2,3,4,152,5],[24,47,28,19,2,67],[]),([114,1,2,3,4,153,5],[10,68,19,34,69],[]),([0,1,155,2,7,4,5],[0,15,10,62,70],[]),e6 [159,150] [19,25,71],e6 [161,28] [24,29,72],e6 [160,28] [29,24,72]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_46_7_1 : checkNodesBT W_46 g_46 F_46 P_46_7_1 A_46 B_46_6 7 N_46_7_1 = true := by decide +kernel
def N_46_7 := N_46_7_0 ++ N_46_7_1
def B_46_7 : BT (List (List Nat)) := buildBucketsBT W_46 N_46_7
set_option maxRecDepth 500000 in
lemma B_46_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_46 7 xs.toFinset) B_46_7 := by
  have hm0 := checkNodesBT_mem (by decide) gp_46 W_46_ok (buildPoolsSubBT_sound S_46_ok) A_46_ok B_46_6_ok C_46_7_0
  have hm1 := checkNodesBT_mem (by decide) gp_46 W_46_ok (buildPoolsSubBT_sound S_46_ok) A_46_ok B_46_6_ok C_46_7_1
  exact buildBucketsBT_of_mem (forall_append (hm0) hm1)
def U_46_8_0 : List Nat := (r 0 4++r 5 7++[14,15])
def P_46_8_0 : BT (Option BoundPool) := buildPoolsSubBT 9 W_46 r_46 S_46 ps_46 U_46_8_0
def N_46_8_0 : List NodeSpec := [e6 [210] [0,2],e6 [253] [0,2],e6 [211] [0,2],([118,0,2,3,4,13,5,35],[0,2],[0]),([49,351,0,2,3,4,5,35],[0,2],[]),([49,0,2,3,50,4,5,35],[0,2],[0]),e6 [184] [0,2],e6 [296] [0,2],e6 [256] [1,2],([348,0,1,2,4,5,27],[1,2],[]),e6 [287] [1,2],([64,0,1,2,3,4,204],[1,2],[]),e6 [227] [1,2],([49,0,286,2,3,4,5],[1,2],[]),e6 [344] [1,2],e6 [302] [1,2],e6 [205] [2,1],e6 [226] [2,1],e6 [274] [2,1],([19,0,2,3,4,57,5],[2,1],[0]),([19,321,0,2,3,4,5],[2,1],[]),e6 [213] [2,1],e6 [266] [0,1,3],e6 [224] [0,3,1],e6 [271] [0,3,2],([19,0,2,3,12,4,13,5],[0,3,2,1],[0]),e6 [52] [2,3],e6 [192] [2,3],e6 [190] [3,2],e6 [125,126,12] [3,2],e6 [188] [3,2],e6 [314] [3,2],e6 [332] [3,2],([0,2,3,20,12,4,5],[1,2,3,5],[0]),e6 [281] [2,5,1],e6 [92,241] [0,3,6],e6 [285] [1,3,6],e6 [324] [0,7,2],e6 [92,122] [1,3,0,7,6],e6 [261,27] [1,7,0,3,6],e6 [219,27] [3,2,7,0],e6 [272] [3,7,6],([207,1,2,3,4,5,204],[6,7,0,2],[]),([0,1,76,3,4,5,39],[6,7,2],[]),([63,0,1,46,3,4,5],[7,1,6],[]),e6 [197,13] [0,2,8],([348,0,6,2,3,4,5],[1,8,2],[0]),e6 [95,236] [0,1,10,2,7],e6 [103,223] [0,1,10,7],e6 [103,236] [0,1,10,7],e6 [50,236] [0,2,10],e6 [50,223] [0,2,10],e6 [340] [0,2,10,8],e6 [103,172] [0,10,6,1],e6 [82,96] [1,7,10,3],e6 [25,12,67] [2,3,10],([19,25,0,2,3,4,5],[2,10],[]),([19,103,0,2,3,4,85,5],[3,1,10],[]),u6 [52,21,12] [3,2,10,6,9],([189,0,1,178,3,4,5],[3,7,10],[]),([193,0,1,3,4,13,5],[7,0,10],[]),e6 [19,278] [10,1,3,0],e6 [19,222] [10,2,0,3],([25,0,1,2,4,5,27],[10,6],[]),e6 [221] [1,3,7,10,11,8],([95,105,1,2,3,4,5],[1,10,2,11],[]),([49,95,0,2,3,4,5,35],[1,14,2],[]),e6 [13,241] [2,0,14],e6 [13,240] [2,0,14],e6 [183,108,91] [2,14,3,1,6],e6 [209] [2,14,6],e6 [360] [2,14,6],([0,2,3,162,4,5,35],[14,2],[]),e6 [183,92,91] [14,2,1,3,6],e6 [362] [14,6],e6 [181] [0,10,15,6],e6 [217,92] [0,15,1,3,6],e6 [331] [0,15,10],([49,0,242,2,3,4,5],[0,15,10],[]),e6 [157] [0,15,10],e6 [315] [0,15,10],e6 [294] [0,15,10],e6 [243] [0,15,10],e6 [185,157] [0,15,10],([141,0,6,2,3,4,5],[0,15,10],[0]),([19,0,2,3,50,4,85,5],[2,3,0,15],[]),([19,95,0,2,3,4,85,5],[3,2,15,0],[]),([19,0,18,2,3,12,4,5],[3,15,0,2],[0]),([19,25,0,2,3,12,4,5],[3,15,0,2],[0]),([19,24,0,2,3,12,4,5],[3,15,0,2],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_46_8_0 : checkNodesBT W_46 g_46 F_46 P_46_8_0 A_46 B_46_7 8 N_46_8_0 = true := by decide +kernel
def U_46_8_1 : List Nat := (r 0 4++r 5 6++r 12 8++[21,24,26]++r 28 5++[34])
def P_46_8_1 : BT (Option BoundPool) := buildPoolsSubBT 9 W_46 r_46 S_46 ps_46 U_46_8_1
def N_46_8_1 : List NodeSpec := [([19,88,0,2,3,4,85,5],[3,15,0,10],[]),([0,2,3,4,320,85,5],[3,15,6,5],[]),([0,1,309,3,4,5],[7,15,2],[]),e6 [328] [7,15,10],([49,0,2,318,3,4,5],[10,7,15],[]),([25,0,2,3,4,5,35],[10,15],[]),([78,114,1,2,3,4,5],[10,15,2],[]),([0,2,3,4,91,244,5],[14,2,15],[]),([49,88,0,2,3,4,5,35],[15,0,10],[]),e6 [354] [0,7,2,8,17],e6 [267] [1,2,17],e6 [95,223] [0,3,2,18,7,15],([118,48,1,2,3,4,5],[0,18,6],[]),([48,1,2,3,4,91,5],[1,2,18],[]),u6 [6,148] [1,2,18,7,8],e6 [109,27] [1,18,3,6],e6 [248] [1,18,6],e6 [350] [1,18,10],u6 [128,35] [2,1,7,18],e6 [276,85] [2,1,7,18],u6 [137,35] [2,7,1,18],e6 [19,96] [2,7,1,18,3,10],e6 [355] [3,16,10,18],([19,21,0,2,3,12,4,5],[3,18,2,0],[0]),([0,1,46,3,4,5,39],[6,7,18],[0]),([0,1,229,3,4,13,5],[7,18,2],[]),e6 [25,103] [10,7,18,1],([21,0,2,3,12,4,5,35],[14,3,2,9,18,10],[]),u6 [95,31] [14,6,15,10,18,7],e6 [371] [14,18,2],u6 [109] [15,18,1,3,6,10],([189,0,1,148,3,4,5],[18,7,2],[]),e6 [361] [0,19,2],e6 [357] [0,19,2],([49,305,0,1,2,3,5],[0,19,2],[]),e6 [230] [7,2,19,5],([169,0,73,2,3,4,5],[19,1,6],[]),u6 [25,53] [0,10,21,7,1,19,9],e6 [284] [6,7,24,2],e6 [54] [7,26,10,5,8],u6 [162,39] [0,28,2,14,15],e6 [207,204] [2,28,7],([49,112,2,3,4,5,35],[6,15,0,28],[]),([49,0,76,2,3,4,5,35],[6,15,0,28],[0]),([206,1,2,3,4,5,204],[7,24,2,28],[]),([49,114,2,3,4,5,35],[28,2],[]),([21,118,0,2,3,4,5,35],[28,2,0,6],[]),([0,1,2,3,345,13,5],[0,5,29,7,10],[]),([335,0,1,2,7,4,5],[0,8,10,6,29],[]),e6 [79,172] [0,10,29,1],e6 [199,13] [1,6,15,29],e6 [260] [1,29],e6 [208] [1,29],e6 [286,13] [1,29,2,19],e6 [49,229] [2,29,1,7],([125,0,1,3,12,4,13,5],[2,29,18,0],[0]),([19,79,0,2,3,4,85,5],[3,1,10,29],[]),e6 [125,57] [3,2,29,7],e6 [313,12] [3,2,29,7],e6 [125,12] [3,7,29,2],u6 [126] [3,29,2,14,6,10],e6 [125,162] [14,6,29,2,7],u6 [33,31] [14,6,29,15],e6 [202,91] [15,10,7,29],e6 [283] [24,2,6,29,7],e6 [329] [29,1],e6 [19,218] [29,1,10,3],e6 [233] [29,2],e6 [186] [29,2],e6 [370] [29,2,19,5],e6 [341] [29,6],e6 [299] [29,6],([0,202,1,3,4,13,5],[29,6],[]),e6 [125,369] [29,6,14],u6 [32,31] [29,6,14,15,7,18],u6 [50,31] [29,6,15,10],e6 [358] [29,16,10,15],e6 [12,280] [29,18,2,3],e6 [342] [1,2,10,7,30],u6 [108,122] [1,3,7,30,6],e6 [374] [1,19,2,7,30],e6 [232] [1,19,6,7,30],e6 [258] [1,19,30,6],e6 [363] [2,30,7,1],e6 [306] [10,30,7,6,15],e6 [319] [10,30,7,15],([125,0,1,3,4,282,5],[29,30,2],[]),e6 [176,12] [3,29,2,31],e6 [25,26] [10,12,32,21,13,1],e6 [88,106] [0,10,34,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_46_8_1 : checkNodesBT W_46 g_46 F_46 P_46_8_1 A_46 B_46_7 8 N_46_8_1 = true := by decide +kernel
def U_46_8_2 : List Nat := (r 0 4++r 5 6++r 14 6++[23,24]++r 27 5++r 33 6++[40,41,43])
def P_46_8_2 : BT (Option BoundPool) := buildPoolsSubBT 9 W_46 r_46 S_46 ps_46 U_46_8_2
def N_46_8_2 : List NodeSpec := [e6 [288] [0,34,2],e6 [88,236] [2,0,34],e6 [88,204] [2,28,7,24,34],e6 [247,88] [2,34,0],e6 [245] [2,34,3],e6 [108,241] [3,0,6,34,14],e6 [88,179] [18,28,2,24,34],e6 [125,83] [34,14,7,29,6],e6 [295] [0,8,35,10],e6 [263] [0,10,35,8],e6 [347] [0,35,8,10],e6 [346] [0,35,16,10,1,29],([0,1,2,3,4,204,27],[1,2,5,7,35],[]),([0,1,2,3,106,91,5],[1,10,7,35],[]),([19,0,2,12,4,5,27],[2,1,35,17],[]),e6 [203] [6,7,8,35],e6 [177] [6,7,24,35,8],e6 [308] [6,7,24,35,8],e6 [339] [6,29,8,35],([0,2,12,4,5,35,27],[14,2,17,35],[]),e6 [237] [29,8,35,6],e6 [214] [0,1,36],e6 [79,236] [0,1,10,2,37],e6 [79,223] [0,1,10,2,37],([70,0,1,2,3,106,5],[0,1,37,10],[]),e6 [333] [0,24,37,2],e6 [88,223] [2,3,0,37],([246,247,0,1,2,3,4],[2,37,0],[]),e6 [277] [2,37,14,6],e6 [317] [6,0,15,37],e6 [195] [15,18,24,2,37],e6 [167,46] [1,7,2,6,10,38],([70,167,0,1,2,3,5],[1,37,38,10],[]),([49,167,0,1,2,3,5],[1,38,8,19,10],[]),e6 [183,92] [2,0,1,3,36,38,6],u6 [86,79] [2,3,34,1,38,10],e6 [121,18] [2,38,3,14,23],e6 [356] [3,38,0,6],u6 [12,67] [3,38,31,18,2,10],([0,1,2,3,106,5,59],[6,38,10,5,7,1],[0]),([201,0,73,2,3,4,5],[6,38,15],[]),([189,0,1,18,3,4,5],[7,18,38,3],[]),e6 [167,92] [10,2,7,15,1,38,6],e6 [167,103] [10,7,1,30,2,38],e6 [167,79] [10,29,1,38],([21,78,0,1,2,3,5],[10,30,19,2,38,9,6],[]),u6 [74,59] [14,7,6,38],e6 [121,216] [38,14,6],([0,1,18,3,4,13,5],[7,18,0,40,2,38,23],[]),([0,1,18,3,12,4,13,5],[0,7,1,18,40,2,9,41,23,3],[0]),([0,1,2,12,4,13,5,27],[1,3,18,0,6,41,29],[0]),e6 [95,194] [1,10,43,14],([0,1,2,108,4,91,5,27],[1,15,2,10,43,3],[0]),e6 [21,199] [1,15,6,7,43,29],e6 [21,286] [1,19,7,43,2,29],e6 [218,27] [1,29,10,43],e6 [257,91] [2,1,10,43],e6 [352,35] [2,5,19,10,38,43],e6 [192,21] [2,43,10],e6 [21,240] [2,43,10],e6 [21,174] [2,43,10],e6 [95,312] [3,1,43,14],u6 [83,39] [3,24,43,34,8],e6 [279] [3,34,8,43],e6 [338] [3,35,8,43],e6 [268] [3,43],e6 [262] [3,43],([141,82,0,2,3,4,5],[3,43],[]),e6 [21,35] [5,19,2,7,43,10],e6 [73,194] [6,1,10,43],e6 [21,241] [6,7,43,2],e6 [270] [6,43,29,38,35,8],e6 [273,12] [7,0,14,31,43,10],e6 [257,12] [7,0,31,3,43,10],e6 [303,21] [7,43,2,6],e6 [21,12,171] [7,43,9,3,2,10],u6 [68,25,12] [9,1,15,43,33],e6 [19,187] [10,2,0,43],u6 [102] [10,19,7,1,43,8],e6 [73,222] [10,43,2,1,6,3],e6 [21,191,27] [10,43,27,9,6],e6 [118,278] [18,0,10,43,14],e6 [278,27] [18,1,43,10],e6 [12,278] [18,7,1,14,43,10],e6 [196,27] [18,10,43,6],([261,0,1,3,4,5,39],[24,43,3],[]),e6 [21,238] [28,2,0,7,43,6],e6 [21,197] [28,15,2,43,7,0,18],e6 [92,222] [34,0,43,10,2,1,15,38,3],([125,88,0,1,3,4,13,5],[43,0,2],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_46_8_2 : checkNodesBT W_46 g_46 F_46 P_46_8_2 A_46 B_46_7 8 N_46_8_2 = true := by decide +kernel
def U_46_8_3 : List Nat := (r 0 4++r 5 7++r 14 6++[23,24,25]++r 27 5++r 33 4++r 38 6++[45,46,47]++r 51 4++[56,58,59,60,62,63,67,68,69]++r 73 8)
def P_46_8_3 : BT (Option BoundPool) := buildPoolsSubBT 9 W_46 r_46 S_46 ps_46 U_46_8_3
def N_46_8_3 : List NodeSpec := [e6 [153] [43,2,9,6,17,8],e6 [166,27] [43,6,18,10],e6 [261,91] [43,7,14,1],e6 [21,343] [43,9,7,6,10],e6 [118,307] [43,18,0,10,14],([21,0,1,3,4,40,5],[43,18,6,10],[0]),e6 [12,307] [43,18,38,3,10],e6 [359] [43,35,8,6],u6 [108,93,91] [1,15,2,14,45,6],e6 [373,91] [2,1,45],u6 [92,93,91] [15,2,1,45,6],u6 [78,79] [10,29,1,38,6,46],u6 [80,35] [29,1,46,2,10,43],u6 [80,59] [29,14,6,3,1,38,46,10],e6 [21,169] [1,47,9,6,15],e6 [169,13] [2,40,1,6,47,9],([19,0,300,2,3,4,5],[2,47,29],[]),e6 [291,88] [24,2,34,15,18,47],([19,225,0,2,3,4,5],[47,2,0],[]),([19,201,0,2,3,4,5],[47,2,3],[]),([19,169,0,2,3,4,5],[47,2,3],[]),e6 [78,76] [47,19,10,2,38],u6 [14] [0,18,51,40,52,17,2],u6 [56,25,12] [18,3,1,9,53,33],e6 [21,364] [10,43,9,54],e6 [326,85] [0,3,1,15,56,10,18],([92,0,45,2,3,4,5,27],[1,15,56,6],[]),e6 [181,27] [1,19,56,6],e6 [21,133] [1,47,2,56,7,43,6,10],e6 [273,27] [2,1,10,56,43,38,14],e6 [298,27] [2,10,43,6,56],([21,167,0,1,2,3,5,27],[8,10,16,6,56],[]),e6 [170,27] [15,1,7,0,6,56],([21,167,0,1,2,3,5],[10,30,1,2,38,58],[]),e6 [175] [43,2,58,19,5,10],([49,231,0,2,3,4,5],[0,3,15,59,43],[]),e6 [183,108] [0,7,2,6,14,59,1,15,36],([231,0,6,2,3,4,5],[0,8,59,15,3],[]),u6 [14,12] [0,40,51,18,41,3,59,52],e6 [247,12] [1,34,2,18,29,59,0],e6 [305,12] [1,34,18,10,59,2,43],e6 [88,228] [2,6,59,7,34,24,15,28],e6 [154] [10,30,7,1,59,8],e6 [167,108] [11,7,10,59,2,15,1,6,38],e6 [212] [43,0,59,10],e6 [12,171] [43,1,34,6,31,18,10,59],e6 [12,228] [43,7,1,34,6,9,18,10,59],e6 [292,59] [43,14,7,59,38,15,10],([118,105,1,2,3,4,5],[0,60,10,2],[]),([105,1,2,3,4,5,27],[1,2,38,11,60],[]),([375,0,2,3,4,91,5],[1,2,60],[]),([63,0,1,60,3,4,5],[6,7,60],[]),e6 [92,252] [6,60,14,0,15,1],e6 [365] [43,60,10],e6 [118,218] [0,10,43,14,62],e6 [21,118,135] [7,43,6,54,62],e6 [21,322] [43,10,2,62,27],([105,1,2,3,4,5,35],[0,2,24,36,63,38],[]),e6 [64,178] [0,7,2,6,15,63,1],([48,1,2,3,4,5,27],[1,2,7,30,63],[0]),([48,1,2,3,12,4,5],[1,18,2,63],[0]),([169,82,0,2,3,4,5],[1,63,3,6],[]),([19,105,1,2,3,4,5],[2,63,0],[]),([19,48,1,2,3,4,5],[2,63,0],[]),e6 [30,148] [7,2,6,18,1,63,19],([125,105,1,2,3,4,5],[24,2,36,6,63,38],[]),e6 [92,194] [63,0,1,43,3,15],e6 [251] [63,3,43],([231,82,0,2,3,4,5],[63,3,43],[]),([78,112,1,2,3,4,5],[47,19,67,2,0],[0]),([112,1,76,2,3,4,5],[67,47,15,2,63],[0]),e6 [70,204] [2,28,7,24,68],e6 [229,85] [2,68,19,1,29,6,7],e6 [376,91] [1,15,60,2,69],([0,1,2,3,194,91,5],[1,69,24,43,35],[]),e6 [353] [15,1,69,2,30,7],e6 [367] [43,69,18,2,19,5],e6 [168,27] [1,10,6,25,35,73],e6 [46,168,27] [2,25,56,73,38],e6 [168] [7,2,74,10,73,5,19],e6 [169,46] [1,6,75],u6 [45,46] [76,1,15,18,7,6,56],u6 [81,12,13] [39,2,1,40,77,15,41,42,3,59],e6 [60,27] [1,63,43,7,6,56,18,60,78],e6 [118,250] [43,2,7,3,10,14,78,62,5,18],([125,189,0,1,3,4,91],[78,2,18,14],[]),u6 [69,18] [3,0,1,43,79],e6 [25,69] [3,1,79,0],e6 [21,69,12] [3,79,43,0],([21,0,1,18,3,12,4,5],[9,18,3,79,80,2,58,23],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_46_8_3 : checkNodesBT W_46 g_46 F_46 P_46_8_3 A_46 B_46_7 8 N_46_8_3 = true := by decide +kernel
def U_46_8_4 : List Nat := (r 0 4++r 5 7++[14,15,16,18,19]++r 23 9++r 35 4++[40,41,43,46,47,48,55,58,59,60,62,63]++r 67 4++[75,76,78,79]++r 81 52)
def P_46_8_4 : BT (Option BoundPool) := buildPoolsSubBT 9 W_46 r_46 S_46 ps_46 U_46_8_4
def N_46_8_4 : List NodeSpec := [u6 [83,59] [3,14,38,43,81,6],e6 [21,83] [43,6,81,2,27,29],([154,0,1,2,7,4,5],[10,0,8,82],[0]),u6 [153,35] [0,43,2,10,84],([21,112,1,2,3,4,5,35],[0,47,19,2,67,43,10,84],[0]),e6 [46,35] [1,76,2,7,19,84,29,0,18],([19,21,30,0,2,3,4],[10,3,84,0,2,1,9],[]),([21,78,0,1,2,3,5,35],[19,2,10,16,84],[0]),e6 [78,351] [30,10,2,84,47,19],e6 [180,35] [83,5,2,10,43,67,84],e6 [334,13] [2,41,1,47,15,85],([0,2,3,12,4,13,5,35],[14,3,2,40,85,29],[0]),e6 [21,334] [15,1,47,2,58,85],e6 [182] [0,8,35,6,86,3],u6 [157,27] [0,7,15,6,10,87],([92,0,1,2,4,91,5,27],[1,15,10,2,87,3],[]),e6 [88,92,59] [88,43,89,0,3],u6 [152,35] [10,2,5,19,25,90],([92,105,1,2,3,4,5],[0,1,10,2,11,43,91,3],[]),e6 [92,65] [1,3,10,2,0,91,48,7],e6 [264,92] [38,6,1,10,91],u6 [140] [3,43,6,38,35,59,8,92],u6 [7,13] [0,5,15,93,8,29,70],([0,1,2,7,4,13,5],[0,5,29,93,8],[0]),u6 [56,12] [1,9,43,23,60,3,79,94,95,10],e6 [198] [10,35,7,1,96,8],e6 [200,59] [14,28,6,97,18],e6 [118,60] [43,7,60,15,62,97,28,0,6],e6 [60,35] [0,63,67,2,7,6,84,78,98],e6 [235] [3,7,15,98,16],([196,121,0,1,2,3,5],[3,10,98,29],[]),([25,121,0,1,2,3,5],[3,98,19,10,8,14],[]),([187,121,0,1,2,3,5],[29,10,98,14],[]),u6 [156] [1,7,36,99,0,3],([0,73,108,3,4,5,27],[1,100,6,15],[0]),([0,73,108,3,4,91,5],[1,101,15,6,3],[]),([21,0,1,2,12,4,5,27],[1,3,6,58,18,102,10],[]),u6 [21,100,12] [9,3,7,43,102,18,31,58,55,0],([21,0,1,2,7,4,5],[10,6,8,0,102,62,27],[0]),e6 [21,7] [15,2,10,8,43,70,0,102,62,27],u6 [36,35] [0,2,29,103],u6 [13,133] [1,47,0,2,6,7,16,10,103],([19,30,0,2,3,4,13],[103,0,29,104,15,1],[]),u6 [147] [43,0,105,10],([112,1,2,3,4,13,5,35],[0,106,2],[0]),u6 [13,35] [2,106,0],([48,1,2,3,4,5,59],[6,63,2,24,106,7],[]),([48,1,2,3,4,5,35],[6,63,2,24,106,7],[]),e6 [13,238] [14,0,106,2],e6 [215] [24,0,106,36,1,6],u6 [104,85] [0,7,1,107,10,6,14],u6 [104,35] [1,7,107,18,2,10,43],e6 [264,108] [1,2,10,108],e6 [104,59] [43,14,69,1,107,108],e6 [239,59] [59,106,14,108],e6 [219,91] [1,2,109],e6 [220] [29,37,19,5,110,111,14,43,10],e6 [222,35] [2,0,19,10,84,112,43],e6 [125,88,85] [6,113,0,7,29,3],e6 [218,35] [0,29,14,10,19,2,114,43,115],e6 [125,71] [1,116,7,2,29,14,6,3],e6 [70,300] [6,7,116],e6 [103,201] [6,38,3,117,107,10,30,28],([103,0,2,3,4,85,5,35],[117,3,107,10,43,63],[]),([79,0,2,3,4,85,5,35],[117,46,10,29,43],[]),u6 [90] [0,18,118,3,2,6,10],e6 [269,85] [0,68,15,6,2,118],([125,118,189,0,1,3,4],[0,118,18,6],[]),u6 [46,47,27] [1,75,118,18],e6 [165,169] [1,118,6],u6 [52,18] [2,3,23,38,8,118],([125,189,0,1,3,12,4],[118,14,29,2,18,10],[]),u6 [18,12,54] [119,18,19,120,31,121,23],u6 [12,54] [26,1,119,120,31,121,23,10,122,3,60],u6 [25,18] [19,10,18,8,3,38,1,123,23,2],([21,114,1,2,3,4,5,35],[10,19,28,2,124,7,106,68],[0]),([114,1,2,3,4,13,5,35],[29,124,2,28,19],[0]),([49,79,0,2,3,4,5,35],[29,125,1,10],[]),([49,103,0,2,3,4,5,35],[125,1,10],[]),([0,2,3,4,77,5,35],[125,2,6,5],[0]),e6 [118,194] [6,0,10,43,126],e6 [52,13] [0,68,2,3,127,14,6],u6 [52,25] [2,3,15,127,8],e6 [52,21] [2,3,43,7,14,6,127],u6 [52,24] [2,3,43,59,127],u6 [52,12,13] [2,29,3,1,127,6,40],([121,0,73,108,3,4,5],[3,6,128,129],[]),u6 [22,12] [1,43,9,79,130,58,3,2,131],u6 [125,25,12] [2,59,132,3],([125,21,0,1,3,12,4,5],[2,132,7,43,3,31,6],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_46_8_4 : checkNodesBT W_46 g_46 F_46 P_46_8_4 A_46 B_46_7 8 N_46_8_4 = true := by decide +kernel
def U_46_8_5 : List Nat := (r 0 4++r 5 15++[21,24,25]++r 28 11++[40,41,43,44,46,48,54,56,58,59,60,62,63,73,78,79,84,97,102,103,106,107,113,118]++r 132 78)
def P_46_8_5 : BT (Option BoundPool) := buildPoolsSubBT 9 W_46 r_46 S_46 ps_46 U_46_8_5
def N_46_8_5 : List NodeSpec := [e6 [125,25] [7,10,29,2,19,1,132],u6 [25,53,12] [9,31,43,1,3,21,132],e6 [25,79] [10,29,7,1,132],u6 [25,39] [11,7,118,2,10,132],e6 [21,101] [24,63,43,10,58,133,0,9,106],e6 [46,85] [1,7,19,134,73,2,10,6],e6 [323,85] [3,1,134,15,18,10,6],([0,1,2,3,85,250,5],[3,5,10,134,135,7,14],[]),e6 [290] [29,37,10,16,136,1,46],e6 [254,35] [0,136,137,138,2,10,43,38],u6 [38,12] [3,29,2,59,139,31,78,10],u6 [83,13] [0,43,140,5,3,7,41,141,6,34,29],e6 [301,35] [0,19,2,18,106,14,142],e6 [187,35] [5,19,2,10,43,142],e6 [255] [10,3,7,1,43,142],u6 [73,65] [1,3,10,2,143,29,19,7,6],u6 [89] [24,6,8,38,143,44],u6 [60,12] [1,43,59,31,60,2,3,97,144,6,29],e6 [21,137,35] [2,43,10,58,145],e6 [19,21,137] [43,2,145,10],e6 [21,259] [43,10,2,145,62],e6 [125,222] [2,146,0,10,43],([105,73,1,2,3,4,5],[0,1,147,11,6],[0]),u6 [28] [6,148,18,10,24,19,149],e6 [21,88,35] [0,150,43,151,10],e6 [265,27] [1,0,56,152,38,6],e6 [92,71] [0,1,10,2,153,3,6],u6 [51] [15,0,29,154,2,10,103],u6 [36] [0,40,10,2,154,155,8,103],u6 [108,65] [29,3,8,2,10,156],u6 [150] [43,29,38,60,5,19,25,157,2],e6 [275] [0,43,1,158,3],e6 [297] [3,158,1,6],u6 [92,101] [63,0,1,3,158,43],e6 [167,165] [30,10,2,56,159,6],e6 [201,79] [29,38,46,160,3],([64,0,73,108,3,4,5],[1,15,43,161,3],[0]),e6 [254,85] [28,0,162,113,138,29,38],e6 [278,35] [136,10,14,19,0,2,7,18,43,163],([125,189,0,1,3,4,85],[118,6,3,164],[]),u6 [71,35] [2,0,84,165,34,1],([0,1,2,3,194,85,5],[3,162,5,43,166,1],[]),u6 [86,103] [2,7,3,18,1,167,10,168],e6 [86,95] [2,18,7,1,15,38,36,168],u6 [12,110] [43,10,1,18,9,169,3,60],e6 [78,95] [10,2,11,7,15,38,170],u6 [78,103] [10,30,1,38,6,170,107],([0,73,108,3,4,5,59],[6,3,43,11,7,171,59,15,1],[0]),e6 [257,85] [6,3,15,0,1,10,172],([21,24,0,1,3,12,4,5],[9,18,1,3,7,2,43,29,58,173],[0]),u6 [25,24] [10,173,21,19,59,1,2,3,8],e6 [28,27] [174,6,18,29],e6 [21,289] [1,3,2,43,58,175,0,9,145,18],u6 [21,12,135] [43,60,9,175,102,18,31,58],e6 [293] [3,63,6,176,43,14],e6 [12,218] [1,7,177,14,31,18,43,10],e6 [12,194] [1,3,177,178,0,31,10,43],e6 [86,50] [0,34,15,2,3,179,168],e6 [86,88] [2,34,15,18,7,38,179,36,168],e6 [78,88] [10,34,15,38,180,2,170],e6 [78,50] [11,34,15,10,180,2,170],u6 [63,65] [1,3,10,2,181,48,7,43],e6 [273,35] [0,7,84,14,10,182,43],([21,0,1,3,12,4,5,39],[7,43,18,6,183],[0]),e6 [304] [3,16,10,14,31,184],e6 [12,250] [3,185,7,186,31,18,10,78],u6 [126,12] [3,187,31,29,2,59],u6 [25,26,12] [9,32,19,188,132,10,33],u6 [26,12] [79,188,12,189,2,3,13,10],([0,1,2,3,218,5,59],[29,24,10,190,14,17],[]),([105,1,2,3,12,4,5],[1,60,38,11,191,14],[]),e6 [310] [6,0,3,192,2,193,8],e6 [311] [3,14,6,60,2,7,59,30,194],([0,1,2,3,312,5,59],[3,24,10,195,43,14,17],[]),e6 [76,91] [1,2,7,0,15,10,196],e6 [316] [2,14,196,197],u6 [80,85] [1,198,46,7,34,10,6,29],e6 [325] [3,134,199,6],([49,48,1,2,3,4,5],[0,1,6,200],[]),([48,1,2,3,4,85,5],[6,0,1,29,200,2,7],[]),e6 [327] [6,1,3,201,15,30,7,17],e6 [22] [43,54,202,58,2,17],e6 [330,85] [3,15,1,203,6],([0,1,2,4,85,131,5],[3,204,6,1],[0]),e6 [76,27] [1,63,0,7,15,205,2,56,18,154],e6 [64,265] [0,7,1,10,206],u6 [18,81] [14,19,207,2,10,118,8,59,38],e6 [336] [0,1,17,2,208],e6 [337] [0,10,3,7,209,8,35],([125,49,189,0,1,3,4],[0,78,6,14,18,209],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_46_8_5 : checkNodesBT W_46 g_46 F_46 P_46_8_5 A_46 B_46_7 8 N_46_8_5 = true := by decide +kernel
def U_46_8_6 : List Nat := (r 0 4++r 5 6++[14,15,18,19,25,28,29,31,35,43,56,58,59,62,67,76,88,90,134,142,196]++r 209 21)
def P_46_8_6 : BT (Option BoundPool) := buildPoolsSubBT 9 W_46 r_46 S_46 ps_46 U_46_8_6
def N_46_8_6 : List NodeSpec := [u6 [49,46] [1,209,7,18,8,6,19],e6 [193,91] [1,10,7,0,210],e6 [175,27] [212,43,2,10,6,56],([0,1,8,2,7,4,5],[0,211,212,213,8,62,10,214],[0]),e6 [95,345] [0,10,1,6,215,7,14],e6 [50,345] [0,59,215,10,6,29],e6 [101,85] [0,3,1,134,216,10,6],u6 [96,35] [76,2,7,5,19,10,18,217],e6 [152] [7,2,218,6,10,90,8],e6 [19,46] [2,1,219,220,221],e6 [19,60] [67,2,29,219,25,0,6,222],u6 [87,31] [14,10,6,29,223],u6 [21,81,12] [3,59,10,224,2,9,18,31,29,58],e6 [366] [10,19,7,1,225,142],([0,1,2,3,250,91,5],[14,196,226,10,3,7,35],[]),u6 [88,73,59] [6,88,43,227,228,10,7,28,15],e6 [246,21,12] [3,43,10,229,2]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_46_8_6 : checkNodesBT W_46 g_46 F_46 P_46_8_6 A_46 B_46_7 8 N_46_8_6 = true := by decide +kernel
def N_46_8 := N_46_8_0 ++ N_46_8_1 ++ N_46_8_2 ++ N_46_8_3 ++ N_46_8_4 ++ N_46_8_5 ++ N_46_8_6
def B_46_8 : BT (List (List Nat)) := buildBucketsBT W_46 N_46_8
set_option maxRecDepth 500000 in
lemma B_46_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_46 8 xs.toFinset) B_46_8 := by
  have hm0 := checkNodesBT_mem (by decide) gp_46 W_46_ok (buildPoolsSubBT_sound S_46_ok) A_46_ok B_46_7_ok C_46_8_0
  have hm1 := checkNodesBT_mem (by decide) gp_46 W_46_ok (buildPoolsSubBT_sound S_46_ok) A_46_ok B_46_7_ok C_46_8_1
  have hm2 := checkNodesBT_mem (by decide) gp_46 W_46_ok (buildPoolsSubBT_sound S_46_ok) A_46_ok B_46_7_ok C_46_8_2
  have hm3 := checkNodesBT_mem (by decide) gp_46 W_46_ok (buildPoolsSubBT_sound S_46_ok) A_46_ok B_46_7_ok C_46_8_3
  have hm4 := checkNodesBT_mem (by decide) gp_46 W_46_ok (buildPoolsSubBT_sound S_46_ok) A_46_ok B_46_7_ok C_46_8_4
  have hm5 := checkNodesBT_mem (by decide) gp_46 W_46_ok (buildPoolsSubBT_sound S_46_ok) A_46_ok B_46_7_ok C_46_8_5
  have hm6 := checkNodesBT_mem (by decide) gp_46 W_46_ok (buildPoolsSubBT_sound S_46_ok) A_46_ok B_46_7_ok C_46_8_6
  exact buildBucketsBT_of_mem (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (hm0) hm1) hm2) hm3) hm4) hm5) hm6)
def U_46_9_0 : List Nat := (r 0 4++r 5 7++r 14 6++[24,27,28,30,34,35,43,45,47,54,56,59,60,62,63,68,69,76,83,87,93,98])
def P_46_9_0 : BT (Option BoundPool) := buildPoolsSubBT 9 W_46 r_46 S_46 ps_46 U_46_9_0
def N_46_9_0 : List NodeSpec := [([0,2,3,4,85,5,35],[15,2,10,5,16,17],[0]),([19,0,2,3,4,85,5],[5,16,19,2,10,6,17],[0]),([118,0,2,3,4,5,35],[5,15,14,28,2],[0]),([125,21,0,1,3,4,5],[7,16,30,17,2,6],[0]),u6 [202] [7,30,8,16,17,15,6],e6 [377,91] [18,34,1,15,7,8,2],([0,1,2,12,4,5,27],[1,3,35,5,8,6,17],[0]),([0,2,3,12,4,5,35],[14,3,15,2,35,17,5],[0]),u6 [189,91] [18,1,15,8,35,10,0,3],u6 [64,108] [3,43,18,35,8,2,10],u6 [118,189] [5,18,15,0,10,43,14,6],u6 [21,173] [7,19,43,18,10,9,6],([21,0,1,3,4,5,39],[7,43,17,30,6,2,16],[0]),u6 [118,103] [18,7,28,43,14,6],u6 [334] [8,15,47,2,14],u6 [21,191] [7,43,5,27,18,10,54],u6 [73,27] [1,15,8,35,6,17,5,18,7,30,56],u6 [118,79] [0,15,43,14,6,28,62],u6 [82,39] [0,18,24,63,43,34,1],u6 [82,27] [1,18,8,35,6,24,63,5,7,0],u6 [19,125] [5,7,2,30,63,6],u6 [108,27] [15,18,1,63,3,8,6,43,59],e6 [88,39] [18,0,24,34,63,43],u6 [103,27] [18,63,1,2,7,43],u6 [19,103] [24,7,1,43,63,2,0],u6 [125,82] [24,7,63,1,34,6,30,18],u6 [19,88] [24,34,43,63,0,2,1],e6 [125,27] [63,2,8,35,6,7,30],u6 [19,27] [63,2,18,8,35,1,5,0],u6 [229] [63,5,7,19,18,8,2,16],u6 [31] [63,6,16,15,10,7,30,8],u6 [286] [63,7,30,16,15,2],u6 [199] [63,15,8,6],u6 [39,27] [63,18,6,35,8],u6 [242] [63,30,15,16],u6 [307] [63,30,18,43,10,5,19,8],u6 [65] [63,60,2,10,5,19,7,30],e6 [70,95] [24,11,68,7,1,14,10],u6 [70,27] [63,1,18,68,24,2,10,7,11],u6 [269] [18,76,2,69,1],([0,1,2,4,91,5,27],[76,1,10,2,35,16,17],[0]),u6 [372,91] [76,1,18,19,2,45],e6 [348,91] [76,15,1,5,2],u6 [169,27] [76,15,1,35,5,6],u6 [71] [1,11,5,19,68,83,8,7,60],u6 [252] [6,11,14,60,68,83],e6 [19,70] [24,83,68,28,1,10,0],([0,1,2,7,4,5],[5,63,8,93],[0]),u6 [157] [0,7,24,15,10,87,8,17,98],e6 [210] [0,7,24,17,15,2,8,16,98],u6 [172] [5,15,10,24,6,7,30,17,98],e6 [380] [5,30,18,28,43,24,10,8,6,17,98],u6 [236] [5,60,2,10,24,7,30,8,98],u6 [223] [5,60,2,10,24,7,30,8,98],e6 [381] [7,18,14,2,6,5,19,8,16,98],u6 [125] [7,19,5,8,98,16,30,18,6,2],e6 [378] [7,87,98,17,15],e6 [386] [8,19,5,7,98,16,18,2,6],u6 [222] [11,34,43,10,5,19,7,17,98],u6 [93,91] [14,1,15,2,18,60,35,8,98]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_46_9_0 : checkNodesBT W_46 g_46 F_46 P_46_9_0 A_46 B_46_8 9 N_46_9_0 = true := by decide +kernel
def U_46_9_1 : List Nat := (r 0 4++r 5 4++[10,11]++r 14 6++[24]++r 27 4++r 34 5++[43,46,47,56,59,60,62,63,68,69,76,78,83,84,87,90,91,97,98]++r 100 4++[106,107,108,110,116,117,118,124,125,128,132,136,137,141,147,154,158,159,161,171,173,176,200,205,209,217])
def P_46_9_1 : BT (Option BoundPool) := buildPoolsSubBT 9 W_46 r_46 S_46 ps_46 U_46_9_1
def N_46_9_1 : List NodeSpec := [e6 [390] [14,7,24,18,37,6,5,19,16,98],u6 [238] [14,28,24,15,37,2,7,30,16,98],u6 [86] [24,2,3,5,7,30,35,8,10,6,19,98],u6 [183] [24,2,36,14,5,19,7,30,35,6,10,8,98],e6 [389] [24,2,37,29,5,19,17,8,16,98,14,30,6],u6 [52] [24,2,47,3,5,35,7,30,16,98,14,6,19,8],u6 [291] [24,2,47,5,30,8,16,98,3,11,15,6],u6 [278] [24,7,18,43,10,5,19,8,17,98],u6 [240] [24,63,5,2,14,7,11,34,8,16,98],u6 [241] [24,63,6,34,5,19,7,30,16,98],e6 [382] [24,63,7,29,2,14,6,5,19,35,8,16,98],u6 [171] [43,7,24,60,6,5,19,30,2,8,98],u6 [125,59] [63,2,6,98,16,7,30],u6 [39,59] [63,2,11,6,78,16,98],u6 [19,59] [63,2,97,38,98,16,6,5,0],u6 [92,27] [15,63,1,8,18,3,0,100,5,6,56,87,38],u6 [63,27] [18,1,8,35,6,100],u6 [63,91] [18,1,10,8,2,101,6,29],u6 [21,82] [7,43,18,10,102,27,6],u6 [179] [5,30,18,28,2,11,106,24,8,16,98],u6 [88,59] [2,6,43,59,110,97,38,10,34,36,14,28,15,7],u6 [118,59] [6,63,110,97,38,60,15,14,69,28,18,8],u6 [103,59] [38,6,43,59,110,63,2,10,7,36,108,14,28],u6 [70,92] [24,11,68,7,3,0,1,87,116],u6 [118,39] [0,18,6,15,28,118,8],u6 [118,249] [14,18,15,5,7,10,78,62,6,118],u6 [19,39] [63,2,30,118,0,5],([125,0,1,3,4,13,5],[7,29,16,30,6,124,11,2,17],[0]),u6 [247] [24,2,37,106,5,19,29,35,8,98,6,124,11,30],u6 [35,39] [63,124,2,6,5,19,7],([49,0,2,3,4,5,35],[5,19,17,2,10,125,16],[0]),u6 [121,92] [17,3,30,7,15,38,6,14,60,128,29,87],u6 [103,12] [18,1,7,132,14,117,43],u6 [189,12] [18,19,5,8,35,3,132,43,10],u6 [79,35] [5,19,0,136,2,47,14,46,84,7,34,63,43],u6 [254] [24,34,19,5,7,0,43,137,11,16,38],u6 [246,13] [106,0,29,24,63,141,43,34,1],([105,1,2,3,4,5],[24,11,60,147,63],[0]),u6 [50,35] [15,0,136,63,29,124,106,103,154,2,43],u6 [88,35] [15,136,154,2,34,63,0,7,43],u6 [78,35] [47,5,2,154,16,19],u6 [351,35] [47,15,2,154,17,7,124,106,43,0],u6 [35,27] [63,76,15,2,5,18,154,35],u6 [70,35] [83,19,154,68,47,6,136,0,14,2,10,7,34],u6 [103,35] [136,63,2,7,47,28,14,107,154,18,43],u6 [92,100] [7,106,37,24,0,30,87,1,158,3],u6 [165,27] [18,63,159,15,7,8,6,0,43],u6 [167,27] [159,18,35,16,6,8],u6 [64,63] [17,18,2,1,43,10,161,29],u6 [63,59] [6,63,110,59,60,43,29,11,28,171,38,7,18,1],u6 [92,59] [38,63,110,59,60,91,3,6,87,0,7,171,5,15],u6 [24,12] [18,1,7,19,3,0,29,8,59,173],u6 [82,59] [6,63,97,38,16,24,98,176,43,14,7,34],([48,1,2,3,4,5],[24,30,18,200,63],[0]),u6 [76,35] [47,7,15,2,103,84,17,154,90,205],u6 [49,249] [10,78,5,7,14,18,0,3,209,6,1,15],u6 [95,100] [7,18,106,24,37,1,10,68,14,217],u6 [96] [7,76,18,10,24,217,5,19,17,98],u6 [128] [8,19,5,7,98,17,1,10,217],u6 [95,59] [38,63,110,59,6,60,8,18,14,69,7,2,217,1,15]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_46_9_1 : checkNodesBT W_46 g_46 F_46 P_46_9_1 A_46 B_46_8 9 N_46_9_1 = true := by decide +kernel
def U_46_9_2 : List Nat := (r 0 4++r 5 7++r 14 6++[24]++r 27 5++[35,37,38,43,47,56,59,60,63,68,69,73,76,78,79,84,85,87,97,98,101,102,104,106,110,118,132,134,136,143,145,148,154,159,162,164,174,185,186,193,196,209,217]++r 219 4++[228]++r 230 29)
def P_46_9_2 : BT (Option BoundPool) := buildPoolsSubBT 9 W_46 r_46 S_46 ps_46 U_46_9_2
def N_46_9_2 : List NodeSpec := [u6 [95,35] [136,1,63,15,154,2,85,18,69,76,7,84,217],u6 [92,384] [0,219,15,38,87,3],e6 [92,210] [15,0,17,219,3],u6 [92,157] [15,0,219,3,87],u6 [19,21] [7,2,3,43,27,0,10,18,102,1,220],([19,30,0,2,3,4],[47,5,63,15,221,104],[0]),u6 [30,91] [76,15,18,35,10,5,221,29],u6 [30,50] [76,15,29,43,5,221,6,10],u6 [73,59] [6,110,38,143,228,7,16,98,5,30,15,1],u6 [70,73] [11,7,68,1,6,228,24,10],u6 [100,73] [106,7,1,6,24,10,68,228],u6 [57] [1,3,230,15,132,7,30,118,8,17,98],u6 [35] [5,63,230,15,2,7,30,16,98],u6 [133] [47,230,37,15,2,3,7,30,16,98],([114,1,2,3,4,5,35],[63,230,15,2,7,106,68],[0]),u6 [300] [230,7,15,6,30,16,17,29],u6 [383] [230,37,7,98,16,15,2],u6 [201] [230,30,7,17,15,6,231,3],u6 [85,27] [6,1,3,162,232,15,193,8,35],u6 [13,27] [6,148,18,10,1,63,0,174,15,232,8],u6 [167] [24,10,5,19,2,7,30,98,6,76,232],u6 [27,59] [63,60,6,38,97,18,35,233],u6 [45,27] [76,1,18,35,6,19,0,233],u6 [46,27] [76,159,15,56,18,234,6,73],u6 [169] [230,30,7,17,35,1,235,15,3,6],u6 [148] [7,19,5,18,8,2,236,17],e6 [148,91] [76,2,1,18,69,15,196,236],u6 [326] [63,18,8,1,237],u6 [125,49] [7,5,6,0,10,1,15,239,18,209],u6 [125,368] [7,19,29,18,6,239],e6 [125,300] [7,29,5,6,239],e6 [125,228] [7,29,16,2,30,239],e6 [125,276] [7,29,35,2,239],([125,189,0,1,3,4],[238,239,18,164],[0]),u6 [228] [6,7,240,60,10,24,29,5,19,16,8,98],u6 [125,12] [1,2,3,14,6,7,19,29,132,60,18,239,241,31],u6 [125,91] [2,1,15,14,7,8,69,11,6,18,196,241],u6 [125,118] [7,6,15,28,0,14,239,30,241],u6 [276] [76,7,24,2,1,5,19,29,241,16,60],u6 [249,12] [3,19,5,243,8,132,7,30,31,18,118,78,10],u6 [249,91] [14,15,1,196,18,2,10,242,3,8,16,7,30,78,243],u6 [249,85] [3,5,244,6,15,134,193,7,30,118,18,14],u6 [250] [63,7,186,185,78,10,244,5,19,8],u6 [323] [63,7,18,8,243,5,19,1,245],u6 [46] [7,19,5,18,8,73,246,35,38],u6 [318] [63,7,15,247,16],u6 [21,12] [1,9,79,19,132,248,7,43,18,3,60,102,30,10],u6 [21,137] [7,43,248,102,10,145],u6 [21,6] [10,7,6,1,15,102,30,248,84,0,27],u6 [21,27] [10,63,1,15,6,248,18,7,8,43,56,249,250,102,232],u6 [21,171] [7,43,17,2,6,10,251],u6 [191] [230,7,15,43,252,30,17],u6 [64,85] [3,5,193,15,253,18,35,8],u6 [64,13] [29,0,18,1,15,253,35,8],u6 [92,91] [15,1,10,8,2,18,87,0,254,101,3,38],u6 [60] [7,19,5,60,78,255,222,8],u6 [187] [24,37,43,5,10,19,8,17,98,30,18,256],u6 [50,59] [43,29,110,63,11,60,106,6,97,59,256,2,0,15],u6 [234] [19,7,8,17,3,38,257],u6 [118,13] [0,18,10,5,15,258,6,14]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_46_9_2 : checkNodesBT W_46 g_46 F_46 P_46_9_2 A_46 B_46_8 9 N_46_9_2 = true := by decide +kernel
def U_46_9_3 : List Nat := (r 0 4++r 5 7++r 14 6++[23,24]++r 28 4++r 34 5++[40,43,46,47,56,59,60,63,68,69,76,84,87,93,97,98,102,103,106,107,109,110,111,118,126,129,132,133,134,152,158,161,162,175,177,193,196,217,219,221,228,230,239,248,253,256]++r 259 38)
def P_46_9_3 : BT (Option BoundPool) := buildPoolsSubBT 9 W_46 r_46 S_46 ps_46 U_46_9_3
def N_46_9_3 : List NodeSpec := [u6 [30,13] [29,18,0,40,5,259,15,14],e6 [379,85] [6,3,37,260,15],u6 [265] [5,7,8,152,17,261],u6 [21,64] [17,7,10,15,1,102,30,248,262,18,253],u6 [64,92] [17,15,2,3,87,1,10,161,262,18],u6 [64,73] [1,17,5,6,15,10,2,18,262,263],([0,73,108,3,4,5],[5,30,15,7,264,219,129],[0]),u6 [88,73] [24,7,34,0,6,43,264,1,228],e6 [246,73] [24,7,63,1,6,264],e6 [246,108] [106,24,63,3,264,34,1,43],u6 [18,12] [19,1,3,7,265,18,31,23,118,8,59],e6 [246,95] [24,7,63,1,69,10,68,266],u6 [246,21] [24,7,63,43,10,2,0,267],e6 [246,49] [24,28,63,0,1,10,267],e6 [246,85] [3,6,24,63,268,267,2,1],u6 [21,100] [7,106,37,24,43,269,102,30,0,133,10],u6 [82,50] [0,8,24,43,14,270,63,5,271],u6 [95,82] [7,18,1,43,14,217,271],u6 [225] [230,30,15,0,47,272,6],u6 [79,27] [18,1,63,8,2,24,56,7,30,273,43],u6 [12,39] [0,18,63,118,3,1,274,2,6,19,132],u6 [246,12] [1,3,24,63,274,177,7,2,0,10],u6 [70,12] [1,18,24,68,14,274,177,7,11,132],u6 [12,59] [3,14,110,63,60,274,6,2,38,59,97,132,18,19],u6 [79,12] [18,1,24,19,132,14,274,177,7,30,31,43],u6 [100,12] [1,19,5,18,8,35,3,24,274,177,7,275,0,10],u6 [219] [5,7,8,17,118,109,276,3,38],u6 [50,85] [15,0,162,277,5,193,256,3,6,29],u6 [204] [5,7,2,228,24,37,278,35,8,16,98],u6 [257] [7,106,0,279,43,17],u6 [100,85] [3,5,193,15,162,268,280,158,0,1,7,34],u6 [194] [24,63,11,126,280,5,36,19,7,8],u6 [95,6] [0,1,18,8,10,6,7,217,84,282,14],u6 [6,50] [0,8,43,5,103,282,6,10,29],u6 [6,91] [1,18,8,10,5,281,0,282],u6 [7] [5,63,282,8,7,30,93],u6 [301] [18,76,1,69,283],u6 [21,30] [7,10,6,14,15,30,18,29,9,102,284],u6 [95,30] [8,15,18,14,10,6,217,221,284,29],u6 [125,88] [24,7,34,15,43,18,6,285,0,63,239,14],u6 [125,70] [24,7,68,1,34,10,11,285,6,17,239,14,2],e6 [125,35] [63,5,2,19,285,6,7,30],u6 [121,108] [3,17,15,29,60,14,286],u6 [108,59] [3,43,110,11,59,106,38,6,7,60,10,286,15],u6 [73,91] [1,15,10,8,2,18,6,287,7,196,228],u6 [121,73] [3,7,2,6,14,29,228,38,287],u6 [49,103] [24,28,7,1,288,63,6,10,0],u6 [103,85] [162,10,7,6,268,288,107,0,1,193,18,63,47],u6 [108,91] [15,18,1,43,289,35,8,10,2,286,3,59],u6 [79,91] [18,1,34,8,290,291,14,7],u6 [49,79] [24,28,0,1,291,63,6,10],u6 [79,59] [38,63,59,6,24,98,291,111,14,28,34],u6 [79,85] [162,19,10,6,268,0,1,291,46,134,34,63,38],u6 [88,85] [15,162,193,10,34,6,268,292,7,0,63],u6 [21,88] [24,7,34,43,269,102,10,248,0,292],u6 [49,88] [24,28,34,63,0,10,6,292,1],u6 [25,12] [1,3,18,15,132,59,10,294,118,8],u6 [25] [24,10,19,132,7,30,17,98,293,294],u6 [69,12] [19,1,3,37,177,0,295],u6 [21,135] [7,43,98,175,102,10,296,30]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_46_9_3 : checkNodesBT W_46 g_46 F_46 P_46_9_3 A_46 B_46_8 9 N_46_9_3 = true := by decide +kernel
def U_46_9_4 : List Nat := (r 0 4++r 5 7++r 14 6++[23,24,28,29,30]++r 34 5++[40,43,47,60,63,68,69,76,78,83,84,87,90,98,102,103,106,118,124,128,132,134,136,141,154,162,193,205,209,215,217,220,221,230,232,253,256,263,264,268,269,270,273,281,286,287,291]++r 297 48)
def P_46_9_4 : BT (Option BoundPool) := buildPoolsSubBT 9 W_46 r_46 S_46 ps_46 U_46_9_4
def N_46_9_4 : List NodeSpec := [e6 [246,63] [24,28,63,1,43,2,297],e6 [246,92] [24,7,63,0,3,297,43,1,298],u6 [19,79] [24,5,0,1,43,63,299,2],u6 [6,13] [0,18,10,5,103,300,15,1],u6 [345] [5,63,215,6,10,300,7,30,8],u6 [106] [5,7,301,287,24,10,302,8,6,17,98],u6 [313] [63,5,7,19,2,6,8,35,303],u6 [261] [24,5,8,11,16,17,7,43,304,3,38],e6 [246,50] [106,0,24,63,43,305,7,29],u6 [80] [24,306,7,8,5,19,1,307,29,273,17],([112,1,2,3,4,5,35],[47,15,2,63,124,308,309],[0]),u6 [19,13] [0,18,10,5,310,2,1,17],u6 [74] [5,7,8,24,18,263,17,14,311],u6 [49,39] [0,18,6,28,312,78,15,1],u6 [85,39] [6,0,3,162,268,312,193,118,15],u6 [305] [24,37,2,5,10,19,8,98,43,30,6,312,18],u6 [91,35] [15,1,69,2,63,83,76,313,5,281,154,18],u6 [91,39] [43,69,63,1,18,313,2,118,0,15,78,8],u6 [92] [5,17,7,15,3,38,314],u6 [264] [76,1,36,60,315,2,14],u6 [82,13] [0,18,29,43,316,5,141,6,34,1,63],u6 [88,13] [18,0,34,29,43,316,141,8,63],u6 [141] [230,37,317,17,30,15,3],e6 [385,91] [8,2,69,37,1,318],u6 [49,95] [8,1,18,7,14,10,6,217,319,209,0],u6 [49,50] [11,0,5,29,256,319,10,6],u6 [49,64] [17,5,1,18,0,10,253,319],u6 [49,27] [83,1,18,8,2,5,232,10,0,319],u6 [200] [5,18,28,8,14,320],e6 [103,91] [18,1,10,16,7,321,14],u6 [196] [24,37,43,10,8,17,98,30,15,322,286],u6 [104] [7,18,1,323,14],u6 [82,91] [1,18,24,8,270,324,14,7,0],u6 [118,100] [28,15,0,24,37,10,68,14,6,325],u6 [216] [7,17,15,38,326],u6 [312] [5,327,11,43,7,3,6,8,324,17,98],u6 [121,63] [17,30,29,6,14,60,128,328],u6 [100,91] [1,18,8,10,16,24,37,329,7,106,325],u6 [130,85] [3,330,5,15,118,6,98],u6 [88,108] [15,34,43,3,331,264,8,63],u6 [76] [7,15,205,8,5,90,332,38],u6 [88,92] [24,7,34,15,0,87,3,333,43],u6 [88,63] [24,18,34,28,43,6,29,63,333],u6 [218] [24,7,334,43,10,5,19,8,291,17,98],u6 [189,85] [3,5,15,335,193,18,14],u6 [49,189] [5,0,14,18,10,1,15,335],u6 [183,91] [2,1,14,17,336,8],u6 [273] [0,337,68,83,11],u6 [292] [15,7,0,8,14,338],u6 [13,35] [0,136,63,124,106,40,10,5,103,2,154,340,18,19],u6 [21,35] [10,63,136,19,9,2,154,7,43,84,269,339,102,18,340],u6 [78] [24,10,7,30,8,98,6,340,15],u6 [19,50] [0,8,5,43,15,1,221,341,2,17],u6 [19,95] [1,18,7,217,15,2,17,221,341,0,220],u6 [197] [1,24,8,7,30,2,3,341,16,60],u6 [19,91] [2,76,1,18,5,221,341],([19,0,2,3,12,4,5],[5,19,1,2,3,341,17],[0]),u6 [18] [7,15,342,17,8,38,23],u6 [12,13] [0,18,40,343,1,5,19,132,35,8,29,3],e6 [178,85] [6,162,134,3,193,15,344]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_46_9_4 : checkNodesBT W_46 g_46 F_46 P_46_9_4 A_46 B_46_8 9 N_46_9_4 = true := by decide +kernel
def U_46_9_5 : List Nat := (r 0 4++r 5 4++[10,11]++r 14 6++[24]++r 27 4++[37,38,43,59,60,63,68,69,76,77,97,98,102,106,132,134,154,162,193,210,217,230,248,256,258,267,271,280,319,325]++r 344 28)
def P_46_9_5 : BT (Option BoundPool) := buildPoolsSubBT 9 W_46 r_46 S_46 ps_46 U_46_9_5
def N_46_9_5 : List NodeSpec := [u6 [178] [7,30,15,6,8,17,344],u6 [101] [24,1,106,8,325,5,19,345,17,7],u6 [162] [5,28,24,319,8,7,30,346,14,17,60],u6 [81,12] [3,347,5,19,18,29,77,8,59,10],u6 [121,12] [3,19,5,18,8,17,348,29,132],u6 [121,118] [5,14,15,6,29,348,258],u6 [121,50] [11,29,15,0,17,6,3,256,348],e6 [121,95] [14,18,15,1,7,3,6,38,29,217,348],e6 [246,118] [24,28,63,0,69,10,68,349],u6 [348] [230,30,7,17,1,3,350,15,2],u6 [21,118] [0,15,43,28,351,27,6,248,14,102,10],u6 [35,59] [63,352,2,6,5,19,38,97,154,16,98],u6 [49,100] [28,0,37,24,1,10,353,280],u6 [95,85] [162,1,15,193,10,217,8,18,6,354,355,14],e6 [387,85] [6,68,162,15,7,0,356],u6 [125,85] [6,162,3,15,7,134,193,2,11,357],u6 [349] [230,7,1,17,18,3,59,358],u6 [321] [8,15,1,69,6,359],e6 [86,85] [3,6,17,360,15],u6 [83] [24,361,5,8,7,11,362,3,271,17],u6 [52,12] [3,18,17,132,60,363,19,2,8],u6 [193] [7,5,8,17,210,364],e6 [246,91] [2,1,69,24,63,365,267],u6 [137] [76,7,24,1,18,5,19,366,14,17,60],e6 [70,118] [24,28,68,0,14,10,367],u6 [122] [63,1,8,348,5,19,7,30,368],u6 [239] [8,30,15,1,69,369],u6 [231] [230,37,17,30,15,0,3,59,370],e6 [388] [63,230,15,371,7,30]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_46_9_5 : checkNodesBT W_46 g_46 F_46 P_46_9_5 A_46 B_46_8 9 N_46_9_5 = true := by decide +kernel
def N_46_9 := N_46_9_0 ++ N_46_9_1 ++ N_46_9_2 ++ N_46_9_3 ++ N_46_9_4 ++ N_46_9_5
def B_46_9 : BT (List (List Nat)) := buildBucketsBT W_46 N_46_9
set_option maxRecDepth 500000 in
lemma B_46_9_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_46 9 xs.toFinset) B_46_9 := by
  have hm0 := checkNodesBT_mem (by decide) gp_46 W_46_ok (buildPoolsSubBT_sound S_46_ok) A_46_ok B_46_8_ok C_46_9_0
  have hm1 := checkNodesBT_mem (by decide) gp_46 W_46_ok (buildPoolsSubBT_sound S_46_ok) A_46_ok B_46_8_ok C_46_9_1
  have hm2 := checkNodesBT_mem (by decide) gp_46 W_46_ok (buildPoolsSubBT_sound S_46_ok) A_46_ok B_46_8_ok C_46_9_2
  have hm3 := checkNodesBT_mem (by decide) gp_46 W_46_ok (buildPoolsSubBT_sound S_46_ok) A_46_ok B_46_8_ok C_46_9_3
  have hm4 := checkNodesBT_mem (by decide) gp_46 W_46_ok (buildPoolsSubBT_sound S_46_ok) A_46_ok B_46_8_ok C_46_9_4
  have hm5 := checkNodesBT_mem (by decide) gp_46 W_46_ok (buildPoolsSubBT_sound S_46_ok) A_46_ok B_46_8_ok C_46_9_5
  exact buildBucketsBT_of_mem (forall_append (forall_append (forall_append (forall_append (forall_append (hm0) hm1) hm2) hm3) hm4) hm5)
def U_46_10 : List Nat := ([5,7,11]++r 15 5++[24,28,30,35,37,47,60,63,76,87,98,106,124,132,159,217,219,230,232,238,241,243,244,248,253,256,258,259,263,267,268,269,271,273,274,280,282]++r 285 4++[291,292,300,310,312,313,316,319,324,325,328,331,335,340,341,348,352,357,367,372,373])
def P_46_10 : BT (Option BoundPool) := buildPoolsSubBT 9 W_46 r_46 S_46 ps_46 U_46_10
def N_46_10 : List NodeSpec := [u6 [95] [24,37,7,5,18,35,30,17,76,217],u6 [92] [230,37,7,30,5,35,15,87,17,219],u6 [27] [63,76,35,232,24,159,5,30,98],u6 [249] [63,5,7,30,243,244,238],u6 [64] [63,5,30,35,253],u6 [118] [24,5,37,30,35,17,28,258],u6 [30] [30,35,63,5,15,259],u6 [85] [5,268,15,16,230,30,35,17,98],u6 [21] [24,7,37,5,16,248,30,17,98,269],u6 [12] [5,19,274,35,230,132,30,17],u6 [73] [24,5,37,7,263,287,17,30],u6 [103] [24,230,5,37,35,30,18,288,63],u6 [79] [24,230,5,37,7,30,273,291,63],u6 [88] [35,24,230,5,30,37,292,63],u6 [6] [63,5,30,35,47,282,300],u6 [39] [63,124,30,18,312,11,24,37,5,238,35],u6 [91] [313,76,35,16,24,5,30,17,98],u6 [13] [316,124,30,18,16,24,106,5,35,17],u6 [49] [24,5,37,30,16,17,28,319],u6 [82] [24,30,37,5,271,324,63],u6 [100] [17,37,230,5,30,24,106,325,280],u6 [63] [24,30,37,5,35,17,18,28,328,11,106,219],u6 [108] [5,30,230,15,331,286,11,106,35,17],u6 [189] [63,5,30,35,18,335],u6 [35] [5,63,15,340,230,47,37,30,35,98],u6 [19] [24,5,30,63,341,310],u6 [121] [63,5,30,16,348],u6 [59] [63,352,60,16,24,98,37,5,30,35],u6 [125] [24,7,5,241,98,357,30,285,63],u6 [70] [16,24,230,5,30,37,11,367,63],u6 [246] [24,63,37,372,267],u6 [50] [373,76,30,35,24,256,11,106,5,17]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_46_10 : checkNodesBT W_46 g_46 F_46 P_46_10 A_46 B_46_9 10 N_46_10 = true := by decide +kernel
def B_46_10 : BT (List (List Nat)) := buildBucketsBT W_46 N_46_10
set_option maxRecDepth 500000 in
lemma B_46_10_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_46 10 xs.toFinset) B_46_10 :=
  buildBucketsBT_sound (by decide) gp_46 W_46_ok (buildPoolsSubBT_sound S_46_ok) A_46_ok B_46_9_ok C_46_10
def U_46_11 : List Nat := [16,35,37,230]
def P_46_11 : BT (Option BoundPool) := buildPoolsSubBT 9 W_46 r_46 S_46 ps_46 U_46_11
def N_46_11 : List NodeSpec := [u6 [] [37,230,35,16]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_46_11 : checkNodesBT W_46 g_46 F_46 P_46_11 A_46 B_46_10 11 N_46_11 = true := by decide +kernel
def B_46_11 : BT (List (List Nat)) := buildBucketsBT W_46 N_46_11
set_option maxRecDepth 500000 in
lemma B_46_11_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_46 11 xs.toFinset) B_46_11 :=
  buildBucketsBT_sound (by decide) gp_46 W_46_ok (buildPoolsSubBT_sound S_46_ok) A_46_ok B_46_10_ok C_46_11
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_46_ok : forestRootCheck r_46 g_46 [(VAR 0,22,23),(VAR 1,12,14),(VAR 2,10,14),(VAR 3,6,14),(VAR 4,7,23),(VAR 5,3,35)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_46_in : bucketContainsBT B_46_11 r_46 = true := by decide +kernel
lemma low_46 : Lower r_46 g_46 12 := lower_of_forestBT root_46_ok B_46_11_ok root_46_in

def g_orig := 0xfeeaeaa8eee0e8a0
set_option maxHeartbeats 0 in
lemma low_orig : Lower (varsOf 63) g_orig 12 := carry_of (swaps := [(0,5),(1,3),(2,4),(3,4)]) (by decide +kernel) low_46
def targetFn (x : Fin 6 → Bool) : Bool := Nat.testBit (4276808360 * 2 ^ 32 + 4007717024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def temoin : List Gate := [⟨.and,[0,1]⟩,⟨.or,[6,4]⟩,⟨.or,[3,7]⟩,⟨.and,[7,3]⟩,⟨.and,[8,5]⟩,⟨.and,[9,2]⟩,⟨.or,[9,2]⟩,⟨.and,[1,8]⟩,⟨.or,[0,13]⟩,⟨.or,[11,0]⟩,⟨.and,[12,14]⟩,⟨.and,[15,10]⟩,⟨.or,[17,16]⟩]
lemma temoin_ok : PEqualNP.MetaComplexity.Monotone2 ⟨temoin, 18⟩ := by
  intro g hg; simp [temoin] at hg; rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxHeartbeats 0 in
lemma tgt_eq_G : ∀ r : Row, targetFn (evalInput6 r) = g_orig.testBit r.val := by decide +kernel
set_option maxHeartbeats 0 in
lemma temoin_eval : ∀ r : Row, Circuit.eval ⟨temoin, 18⟩ (List.ofFn (evalInput6 r)) = g_orig.testBit r.val := by decide +kernel

end PEqualNP.Outside.L_meta_45476

open PEqualNP.Outside.L_meta_45476 in
theorem PEqualNP.Outside.L_meta_45476 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808360 * 2 ^ 32 + 4007717024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808360 * 2 ^ 32 + 4007717024) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  exact replace_of_lower6 g_orig (by decide) (by decide) (by decide) 12 low_orig temoin 18 (by decide) temoin_ok targetFn tgt_eq_G temoin_eval
