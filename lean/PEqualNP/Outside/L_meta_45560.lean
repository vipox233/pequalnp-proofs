import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_45560
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
def g_1 := 0xfee8fee8fee8fee8
def r_1 : List Nat := varsOf 15
def p_1 : List Nat := [3,3,5,5,6,6,9,9,10,10,12,12]
def q_1 : List Nat := [2,1,4,1,4,2,8,1,8,2,8,4]
def F_1 : Nat := fullMask 12
set_option maxHeartbeats 0 in
lemma gp_1 : goodPairs g_1 p_1 q_1 := goodPairs_of (by decide +kernel)
def W_1 : BT Decor := buildWiresBT 4 (mkBase p_1 q_1 r_1) [(1,0,1),(1,4,2),(2,5,3),(1,1,2),(1,3,1),(1,3,2),(2,4,3),(1,3,0)]
lemma W_1_ok : btAll (fun x => faithful p_1 q_1 x ∧ x.1 < 2^64) W_1 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_1 : List (List (Nat × Nat)) := [[],[(2,3)],[(1,2)],[(1,3),(2,3)],[(1,2),(2,3)],[(1,3)],[(0,2),(1,2)],[(0,3),(1,3),(2,3)],[(0,2),(1,2),(2,3)],[(0,3),(1,3)],[(0,1),(1,2)],[(0,2),(1,3)]]
def A_1 : BT (List (Nat × Nat)) := btOfList 4 al_1
set_option maxHeartbeats 0 in
lemma A_1_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_1 = g_1) A_1 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_1_0 : Slice r_1 g_1 (subcubeFast 1 0) 4 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_1_1 : Slice r_1 g_1 (subcubeFast 2 0) 4 := by
  have hc : Lower (varsOf 13) 0xfaa0faa0faa0faa0 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_1_2 : Slice r_1 g_1 (subcubeFast 4 0) 4 := by
  have hc : Lower (varsOf 11) 0xee88ee88ee88ee88 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_1_3 : Slice r_1 g_1 (subcubeFast 8 0) 4 := by
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) low_0
def S_1 : BT (Option (Nat × Nat)) := btOfList 2 [some (subcubeFast 1 0,4),some (subcubeFast 2 0,4),some (subcubeFast 4 0,4),some (subcubeFast 8 0,4)]
lemma S_1_ok : btAll (fun o => ∀ p, o = some p → Slice r_1 g_1 p.1 p.2) S_1 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_1_0) (forall_cons (fun _ h => by cases h; exact sl_1_1) (forall_cons (fun _ h => by cases h; exact sl_1_2) (forall_cons (fun _ h => by cases h; exact sl_1_3) (fun _ h => (List.not_mem_nil h).elim)))))
def ps_1 : BT (Option PoolSpec) := btOfList 2 [q 2 [],q 1 [],q 3 [],q 0 []]
def B_1_2 : BT (List (List Nat)) := BT.empty
lemma B_1_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_1 2 xs.toFinset) B_1_2 := .empty
def U_1_3 : List Nat := [0,1]
def P_1_3 : BT (Option BoundPool) := buildPoolsSubBT 2 W_1 r_1 S_1 ps_1 U_1_3
def N_1_3 : List NodeSpec := [([0,7,8,9],[0,1],[]),([6,0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_1_3 : checkNodesBT W_1 g_1 F_1 P_1_3 A_1 B_1_2 3 N_1_3 = true := by decide +kernel
def B_1_3 : BT (List (List Nat)) := buildBucketsBT W_1 N_1_3
set_option maxRecDepth 500000 in
lemma B_1_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_1 3 xs.toFinset) B_1_3 :=
  buildBucketsBT_sound (by decide) gp_1 W_1_ok (buildPoolsSubBT_sound S_1_ok) A_1_ok B_1_2_ok C_1_3
def U_1_4 : List Nat := [1,2,3]
def P_1_4 : BT (Option BoundPool) := buildPoolsSubBT 2 W_1 r_1 S_1 ps_1 U_1_4
def N_1_4 : List NodeSpec := [([0,1,2,5,3],[2],[0]),([0,1,2,11,8],[3,1],[10]),([10,0,1,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_1_4 : checkNodesBT W_1 g_1 F_1 P_1_4 A_1 B_1_3 4 N_1_4 = true := by decide +kernel
def B_1_4 : BT (List (List Nat)) := buildBucketsBT W_1 N_1_4
set_option maxRecDepth 500000 in
lemma B_1_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_1 4 xs.toFinset) B_1_4 :=
  buildBucketsBT_sound (by decide) gp_1 W_1_ok (buildPoolsSubBT_sound S_1_ok) A_1_ok B_1_3_ok C_1_4
def U_1_5 : List Nat := (r 0 4)
def P_1_5 : BT (Option BoundPool) := buildPoolsSubBT 2 W_1 r_1 S_1 ps_1 U_1_5
def N_1_5 : List NodeSpec := [([0,1,4,2,3],[3,1,0,2],[0,1,3,5,7,9])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_1_5 : checkNodesBT W_1 g_1 F_1 P_1_5 A_1 B_1_4 5 N_1_5 = true := by decide +kernel
def B_1_5 : BT (List (List Nat)) := buildBucketsBT W_1 N_1_5
set_option maxRecDepth 500000 in
lemma B_1_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_1 5 xs.toFinset) B_1_5 :=
  buildBucketsBT_sound (by decide) gp_1 W_1_ok (buildPoolsSubBT_sound S_1_ok) A_1_ok B_1_4_ok C_1_5
def U_1_6 : List Nat := (r 0 4)
def P_1_6 : BT (Option BoundPool) := buildPoolsSubBT 2 W_1 r_1 S_1 ps_1 U_1_6
def N_1_6 : List NodeSpec := [([0,1,2,3],[3,1,0,2],[0,2,4,6,8,11])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_1_6 : checkNodesBT W_1 g_1 F_1 P_1_6 A_1 B_1_5 6 N_1_6 = true := by decide +kernel
def B_1_6 : BT (List (List Nat)) := buildBucketsBT W_1 N_1_6
set_option maxRecDepth 500000 in
lemma B_1_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_1 6 xs.toFinset) B_1_6 :=
  buildBucketsBT_sound (by decide) gp_1 W_1_ok (buildPoolsSubBT_sound S_1_ok) A_1_ok B_1_5_ok C_1_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_1_ok : forestRootCheck r_1 g_1 [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 3,1,9)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_1_in : bucketContainsBT B_1_6 r_1 = true := by decide +kernel
lemma low_1 : Lower r_1 g_1 7 := lower_of_forestBT root_1_ok B_1_6_ok root_1_in
def g_2 := 0xe880e880e880e880
def r_2 : List Nat := varsOf 15
def p_2 : List Nat := [7,7,7,11,11,11,13,13,13,14,14,14]
def q_2 : List Nat := [6,5,3,10,9,3,12,9,5,12,10,6]
def F_2 : Nat := fullMask 12
set_option maxHeartbeats 0 in
lemma gp_2 : goodPairs g_2 p_2 q_2 := goodPairs_of (by decide +kernel)
def W_2 : BT Decor := buildWiresBT 4 (mkBase p_2 q_2 r_2) [(0,0,1),(0,0,2),(0,1,2),(0,6,3),(3,7,0),(0,2,3),(3,9,0),(0,4,2)]
lemma W_2_ok : btAll (fun x => faithful p_2 q_2 x ∧ x.1 < 2^64) W_2 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_2 : List (List (Nat × Nat)) := [[],[(2,3)],[(1,2)],[(1,2),(2,3)],[(0,1)],[(0,1),(2,3)],[(0,2),(1,2)],[(0,2),(1,2),(2,3)],[(0,2),(1,3)],[(0,1),(1,2),(2,3)],[(0,2),(1,3),(2,3)]]
def A_2 : BT (List (Nat × Nat)) := btOfList 4 al_2
set_option maxHeartbeats 0 in
lemma A_2_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_2 = g_2) A_2 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_2_0 : Slice r_2 g_2 (subcubeFast 0 1) 4 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_2_1 : Slice r_2 g_2 (subcubeFast 0 2) 4 := by
  have hc : Lower (varsOf 13) 0xfaa0faa0faa0faa0 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_2_2 : Slice r_2 g_2 (subcubeFast 0 4) 4 := by
  have hc : Lower (varsOf 11) 0xee88ee88ee88ee88 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_2_3 : Slice r_2 g_2 (subcubeFast 0 8) 4 := by
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) low_0
def S_2 : BT (Option (Nat × Nat)) := btOfList 2 [some (subcubeFast 0 1,4),some (subcubeFast 0 2,4),some (subcubeFast 0 4,4),some (subcubeFast 0 8,4)]
lemma S_2_ok : btAll (fun o => ∀ p, o = some p → Slice r_2 g_2 p.1 p.2) S_2 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_2_0) (forall_cons (fun _ h => by cases h; exact sl_2_1) (forall_cons (fun _ h => by cases h; exact sl_2_2) (forall_cons (fun _ h => by cases h; exact sl_2_3) (fun _ h => (List.not_mem_nil h).elim)))))
def ps_2 : BT (Option PoolSpec) := btOfList 2 [q 1 [],q 0 [],q 2 [],q 3 []]
def B_2_2 : BT (List (List Nat)) := BT.empty
lemma B_2_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_2 2 xs.toFinset) B_2_2 := .empty
def U_2_3 : List Nat := [0,1]
def P_2_3 : BT (Option BoundPool) := buildPoolsSubBT 2 W_2 r_2 S_2 ps_2 U_2_3
def N_2_3 : List NodeSpec := [([4,5,6,3],[0,1],[]),([8,1,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_2_3 : checkNodesBT W_2 g_2 F_2 P_2_3 A_2 B_2_2 3 N_2_3 = true := by decide +kernel
def B_2_3 : BT (List (List Nat)) := buildBucketsBT W_2 N_2_3
set_option maxRecDepth 500000 in
lemma B_2_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_2 3 xs.toFinset) B_2_3 :=
  buildBucketsBT_sound (by decide) gp_2 W_2_ok (buildPoolsSubBT_sound S_2_ok) A_2_ok B_2_2_ok C_2_3
def U_2_4 : List Nat := [0,2,3]
def P_2_4 : BT (Option BoundPool) := buildPoolsSubBT 2 W_2 r_2 S_2 ps_2 U_2_4
def N_2_4 : List NodeSpec := [([4,5,1,2,3],[0,2],[0]),([11,0,1,2,3],[3],[9]),([10,0,1,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_2_4 : checkNodesBT W_2 g_2 F_2 P_2_4 A_2 B_2_3 4 N_2_4 = true := by decide +kernel
def B_2_4 : BT (List (List Nat)) := buildBucketsBT W_2 N_2_4
set_option maxRecDepth 500000 in
lemma B_2_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_2 4 xs.toFinset) B_2_4 :=
  buildBucketsBT_sound (by decide) gp_2 W_2_ok (buildPoolsSubBT_sound S_2_ok) A_2_ok B_2_3_ok C_2_4
def U_2_5 : List Nat := (r 0 4)
def P_2_5 : BT (Option BoundPool) := buildPoolsSubBT 2 W_2 r_2 S_2 ps_2 U_2_5
def N_2_5 : List NodeSpec := [([4,0,1,2,3],(r 0 4),[0,1,4,5,8,10])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_2_5 : checkNodesBT W_2 g_2 F_2 P_2_5 A_2 B_2_4 5 N_2_5 = true := by decide +kernel
def B_2_5 : BT (List (List Nat)) := buildBucketsBT W_2 N_2_5
set_option maxRecDepth 500000 in
lemma B_2_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_2 5 xs.toFinset) B_2_5 :=
  buildBucketsBT_sound (by decide) gp_2 W_2_ok (buildPoolsSubBT_sound S_2_ok) A_2_ok B_2_4_ok C_2_5
def U_2_6 : List Nat := (r 0 4)
def P_2_6 : BT (Option BoundPool) := buildPoolsSubBT 2 W_2 r_2 S_2 ps_2 U_2_6
def N_2_6 : List NodeSpec := [([0,1,2,3],[1,0,2,3],[0,2,3,6,7,8])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_2_6 : checkNodesBT W_2 g_2 F_2 P_2_6 A_2 B_2_5 6 N_2_6 = true := by decide +kernel
def B_2_6 : BT (List (List Nat)) := buildBucketsBT W_2 N_2_6
set_option maxRecDepth 500000 in
lemma B_2_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_2 6 xs.toFinset) B_2_6 :=
  buildBucketsBT_sound (by decide) gp_2 W_2_ok (buildPoolsSubBT_sound S_2_ok) A_2_ok B_2_5_ok C_2_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_2_ok : forestRootCheck r_2 g_2 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_2_in : bucketContainsBT B_2_6 r_2 = true := by decide +kernel
lemma low_2 : Lower r_2 g_2 7 := lower_of_forestBT root_2_ok B_2_6_ok root_2_in
def g_3 := 0xf880f880f880f880
def r_3 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_3 : Lower r_3 g_3 5 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,6,7)]) (by decide +kernel) hc
def g_4 := 0xffe8ffe8ffe8ffe8
def r_4 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_4 : Lower r_4 g_4 5 := by
  exact lift_of_f (z := 8) (o := 0) (other := r_0) (G := g_0) (essPairs := [(VAR 3,0,8)]) (by decide +kernel) low_0
def g_5 := 0xffe8e880ffe8e880
def r_5 : List Nat := varsOf 31
def p_5 : List Nat := [7,7,7,11,11,11,13,13,13,14,14,14,19,19,19,21,21,21,22,22,22,24,24,25,25,26,26,28,28]
def q_5 : List Nat := [6,5,3,10,9,3,12,9,5,12,10,6,18,17,3,20,17,5,20,18,6,16,8,17,9,18,10,20,12]
def F_5 : Nat := fullMask 29
set_option maxHeartbeats 0 in
lemma gp_5 : goodPairs g_5 p_5 q_5 := goodPairs_of (by decide +kernel)
def W_5 : BT Decor := buildWiresBT 6 (mkBase p_5 q_5 r_5) [(0,1,2),(1,5,3),(1,6,4),(3,5,7),(0,0,1),(0,0,2),(1,3,4),(0,0,11),(0,1,11),(0,5,11),(3,14,0),(1,9,3),(1,9,4),(0,9,2),(3,18,11),(1,18,4),(3,5,0),(0,2,11),(3,22,0),(2,2,4),(1,24,3),(1,16,4),(2,16,4),(0,9,11),(2,0,4),(2,29,3),(2,9,4),(1,29,3),(2,2,3),(3,33,0),(2,0,3),(2,1,3)]
lemma W_5_ok : btAll (fun x => faithful p_5 q_5 x ∧ x.1 < 2^64) W_5 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_5 : List (List (Nat × Nat)) := [[],[(3,4)],[(1,2)],[(0,1)],[(0,1),(3,4)],[(0,2),(1,2)],[(0,2),(1,2),(3,4)],[(0,1),(1,2)],[(0,1),(1,2),(3,4)],[(0,2)],[(0,2),(3,4)]]
def A_5 : BT (List (Nat × Nat)) := btOfList 4 al_5
set_option maxHeartbeats 0 in
lemma A_5_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_5 = g_5) A_5 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_5_0 : Slice r_5 g_5 (subcubeFast 0 1) 7 := by
  have hc : Lower (varsOf 30) 0xfffcfcc0fffcfcc0 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_1 : Slice r_5 g_5 (subcubeFast 0 2) 7 := by
  have hc : Lower (varsOf 29) 0xfffafaa0fffafaa0 7 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_2 : Slice r_5 g_5 (subcubeFast 16 0) 7 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_2
set_option maxHeartbeats 0 in
lemma sl_5_3 : Slice r_5 g_5 (subcubeFast 0 4) 7 := by
  have hc : Lower (varsOf 27) 0xffeeee88ffeeee88 7 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_4 : Slice r_5 g_5 (subcubeFast 8 0) 7 := by
  have hc : Lower (varsOf 23) 0xe8e88080e8e88080 7 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_5 : Slice r_5 g_5 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) 0xffc0c000ffc0c000 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_6 : Slice r_5 g_5 (subcubeFast 0 8) 5 := by
  have hc : Lower (varsOf 23) 0xffffe8e8ffffe8e8 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_7 : Slice r_5 g_5 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) 0xff888800ff888800 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_8 : Slice r_5 g_5 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) 0xffa0a000ffa0a000 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_9 : Slice r_5 g_5 (subcubeFast 16 8) 4 := by
  exact slice_fast_direct_f (z := 16) (o := 8) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_5_10 : Slice r_5 g_5 (subcubeFast 8 16) 4 := by
  exact slice_fast_direct_f (z := 8) (o := 16) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_5_11 : Slice r_5 g_5 (subcubeFast 16 4) 4 := by
  have hc : Lower (varsOf 11) 0xee88ee88ee88ee88 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_12 : Slice r_5 g_5 (subcubeFast 8 4) 4 := by
  have hc : Lower (varsOf 19) 0xeeee8888eeee8888 4 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 8) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_13 : Slice r_5 g_5 (subcubeFast 16 2) 4 := by
  have hc : Lower (varsOf 13) 0xfaa0faa0faa0faa0 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_14 : Slice r_5 g_5 (subcubeFast 4 2) 4 := by
  have hc : Lower (varsOf 25) 0xffaaaa00ffaaaa00 4 := carry_of (swaps := [(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_15 : Slice r_5 g_5 (subcubeFast 2 4) 4 := by
  have hc : Lower (varsOf 25) 0xffaaaa00ffaaaa00 4 := carry_of (swaps := [(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 2) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_16 : Slice r_5 g_5 (subcubeFast 16 1) 4 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_17 : Slice r_5 g_5 (subcubeFast 8 1) 4 := by
  have hc : Lower (varsOf 22) 0xfcfcc0c0fcfcc0c0 4 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 8) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_18 : Slice r_5 g_5 (subcubeFast 4 1) 4 := by
  have hc : Lower (varsOf 26) 0xffcccc00ffcccc00 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_19 : Slice r_5 g_5 (subcubeFast 1 4) 4 := by
  have hc : Lower (varsOf 26) 0xffcccc00ffcccc00 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_5_20 : Slice r_5 g_5 (subcubeFast 1 2) 4 := by
  have hc : Lower (varsOf 28) 0xfff0f000fff0f000 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 2) (by decide +kernel) hc
def S_5 : BT (Option (Nat × Nat)) := btOfList 5 [some (subcubeFast 0 1,7),some (subcubeFast 0 2,7),some (subcubeFast 16 0,7),some (subcubeFast 0 4,7),some (subcubeFast 8 0,7),some (subcubeFast 1 0,5),some (subcubeFast 0 8,5),some (subcubeFast 4 0,5),some (subcubeFast 2 0,5),some (subcubeFast 16 8,4),some (subcubeFast 8 16,4),some (subcubeFast 16 4,4),some (subcubeFast 8 4,4),some (subcubeFast 16 2,4),some (subcubeFast 4 2,4),some (subcubeFast 2 4,4),some (subcubeFast 16 1,4),some (subcubeFast 8 1,4),some (subcubeFast 4 1,4),some (subcubeFast 1 4,4),some (subcubeFast 1 2,4)]
lemma S_5_ok : btAll (fun o => ∀ p, o = some p → Slice r_5 g_5 p.1 p.2) S_5 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_5_0) (forall_cons (fun _ h => by cases h; exact sl_5_1) (forall_cons (fun _ h => by cases h; exact sl_5_2) (forall_cons (fun _ h => by cases h; exact sl_5_3) (forall_cons (fun _ h => by cases h; exact sl_5_4) (forall_cons (fun _ h => by cases h; exact sl_5_5) (forall_cons (fun _ h => by cases h; exact sl_5_6) (forall_cons (fun _ h => by cases h; exact sl_5_7) (forall_cons (fun _ h => by cases h; exact sl_5_8) (forall_cons (fun _ h => by cases h; exact sl_5_9) (forall_cons (fun _ h => by cases h; exact sl_5_10) (forall_cons (fun _ h => by cases h; exact sl_5_11) (forall_cons (fun _ h => by cases h; exact sl_5_12) (forall_cons (fun _ h => by cases h; exact sl_5_13) (forall_cons (fun _ h => by cases h; exact sl_5_14) (forall_cons (fun _ h => by cases h; exact sl_5_15) (forall_cons (fun _ h => by cases h; exact sl_5_16) (forall_cons (fun _ h => by cases h; exact sl_5_17) (forall_cons (fun _ h => by cases h; exact sl_5_18) (forall_cons (fun _ h => by cases h; exact sl_5_19) (forall_cons (fun _ h => by cases h; exact sl_5_20) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))))))
def ps_5 : BT (Option PoolSpec) := btOfList 6 [q 6 [],q 10 [],q 13 [],q 2 [4096,45056,45060],q 2 [8196,45076,59],q 0 [],q 17 [],q 15 [],q 14 [],q 2 [4096,8192,8196],q 0 [12325,16421,16397],q 5 [],q 8 [],q 2 [4096,8228,45131],q 16 [],q 2 [45056,45060],q 4 [],q 7 [],q 2 [8196,45079],q 0 [12325,16421],q 18 [],q 2 [4096,8228],q 2 [8196,23],q 2 [45064,91],q 11 [],q 2 [],q 0 [16421,12305],q 0 [12325,16449],q 9 [],q 0 [12325,16450],q 1 [],q 4 [4096,8192,8196],q 2 [4096,8192],q 1 [16397,45079],q 3 [16397,45079],q 2 [4096,45092],q 20 [],q 2 [4096,45056],q 3 [],q 0 [16397],q 19 [],q 2 [45056],q 4 [8196,23],q 0 [12325],q 4 [4096],q 4 [4096,8228],q 12 [],q 4 [4096,8192],q 2 [4096],q 1 [16397],q 3 [16397]]
def B_5_3 : BT (List (List Nat)) := BT.empty
lemma B_5_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_5 3 xs.toFinset) B_5_3 := .empty
def U_5_4 : List Nat := []
def P_5_4 : BT (Option BoundPool) := buildPoolsSubBT 6 W_5 r_5 S_5 ps_5 U_5_4
def N_5_4 : List NodeSpec := [([8,9,10,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_5_4 : checkNodesBT W_5 g_5 F_5 P_5_4 A_5 B_5_3 4 N_5_4 = true := by decide +kernel
def B_5_4 : BT (List (List Nat)) := buildBucketsBT W_5 N_5_4
set_option maxRecDepth 500000 in
lemma B_5_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_5 4 xs.toFinset) B_5_4 :=
  buildBucketsBT_sound (by decide) gp_5 W_5_ok (buildPoolsSubBT_sound S_5_ok) A_5_ok B_5_3_ok C_5_4
def U_5_5 : List Nat := (r 0 14)
def P_5_5 : BT (Option BoundPool) := buildPoolsSubBT 6 W_5 r_5 S_5 ps_5 U_5_5
def N_5_5 : List NodeSpec := [([9,12,13,2,3,4],(r 0 4),[]),([15,1,2,3,4,11],[4],[]),([8,9,0,2,3,4],[5],[0]),([9,10,5,3,4,11],([2]++r 6 4),[0,3,7]),([0,1,2,16,17,11],[10,11,12,6],[]),e5 [19] [13],e5 [8] []]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_5_5 : checkNodesBT W_5 g_5 F_5 P_5_5 A_5 B_5_4 5 N_5_5 = true := by decide +kernel
def B_5_5 : BT (List (List Nat)) := buildBucketsBT W_5 N_5_5
set_option maxRecDepth 500000 in
lemma B_5_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_5 5 xs.toFinset) B_5_5 :=
  buildBucketsBT_sound (by decide) gp_5 W_5_ok (buildPoolsSubBT_sound S_5_ok) A_5_ok B_5_4_ok C_5_5
def U_5_6 : List Nat := ([0,1,2]++r 5 5++[11,12]++r 14 25)
def P_5_6 : BT (Option BoundPool) := buildPoolsSubBT 6 W_5 r_5 S_5 ps_5 U_5_6
def N_5_6 : List NodeSpec := [u5 [12,13] [11,2,12,14,15],([0,1,2,3,20],[11,17,1],[]),e5 [8,11] [16,17,18],u5 [16,17] [19,6,0,2,1],u5 [18,11] [0,1,11,20,8,7,21],e5 [21,11] [11,20,8,7,22],e5 [23,11] [11,20,23],e5 [9,25] [24,0,1,8],([9,0,1,2,3,17,11],[1,25,11,26,12,6],[0]),a5 [9,26] [27,8,7] [7],e5 [27,9] [28,1,29],([9,10,5,3,4],[8,30,5,7,9,31],[0]),([9,10,1,2,3,4,11],[2,24,7,8,32],[0,3,7]),a5 [8] [11,5,16,25,33,34] [0,2],a5 [28,11] [24,16,35] [7],([9,12,1,2,3,4,11],[0,1,2,5,36,37],[0]),e5 [8,5] [0,38,33]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_5_6 : checkNodesBT W_5 g_5 F_5 P_5_6 A_5 B_5_5 6 N_5_6 = true := by decide +kernel
def B_5_6 : BT (List (List Nat)) := buildBucketsBT W_5 N_5_6
set_option maxRecDepth 500000 in
lemma B_5_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_5 6 xs.toFinset) B_5_6 :=
  buildBucketsBT_sound (by decide) gp_5 W_5_ok (buildPoolsSubBT_sound S_5_ok) A_5_ok B_5_5_ok C_5_6
def U_5_7 : List Nat := ([0,1,2,6,7,8,11,12,14,16,17,20,21,22,24,25,28,30,32,36]++r 38 12)
def P_5_7 : BT (Option BoundPool) := buildPoolsSubBT 6 W_5 r_5 S_5 ps_5 U_5_7
def N_5_7 : List NodeSpec := [e5 [31] [11,7,1],e5 [16] [11,7,6,17,28],e5 [29,36] [14,28,1,7,8,40,20],a5 [32] [14,40,36,1] [5],([29,35,1,2,3,4],[25,16,40,1],[]),e5 [12] [25,36,40,0,1],e5 [30] [30,12,28,40],a5 [12,11] [2,24,39,1,36,40,41] [0,2,5,9],u5 [21] [11,8,12,20,22,42],a5 [9,16] [7,28,43,44,2] [0,1],a5 [18] [11,12,17,0,16,1,25,21,45] [0,1],e5 [34] [1,25,46,36],a5 [29,5] [14,20,12,30,46,40,28,1] [5],([9,10,1,2,3,4],[11,30,8,38,32,47],[0]),a5 [9,11] [2,24,0,44,1,48,11,39,49,8,7] [0,1,3,7]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_5_7 : checkNodesBT W_5 g_5 F_5 P_5_7 A_5 B_5_6 7 N_5_7 = true := by decide +kernel
def B_5_7 : BT (List (List Nat)) := buildBucketsBT W_5 N_5_7
set_option maxRecDepth 500000 in
lemma B_5_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_5 7 xs.toFinset) B_5_7 :=
  buildBucketsBT_sound (by decide) gp_5 W_5_ok (buildPoolsSubBT_sound S_5_ok) A_5_ok B_5_6_ok C_5_7
def U_5_8 : List Nat := [0,1,5,7,14,16,25,30,36,38,39,40,44,48,49,50]
def P_5_8 : BT (Option BoundPool) := buildPoolsSubBT 6 W_5 r_5 S_5 ps_5 U_5_8
def N_5_8 : List NodeSpec := [a5 [29] [25,30,14,38,16,5,40,36,1] [0,2,6,10],a5 [9] [30,5,38,7,44,48] [0,1,3,7,8],a5 [11] [39,49,50,16,25,0] [0,2,3,5,7]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_5_8 : checkNodesBT W_5 g_5 F_5 P_5_8 A_5 B_5_7 8 N_5_8 = true := by decide +kernel
def B_5_8 : BT (List (List Nat)) := buildBucketsBT W_5 N_5_8
set_option maxRecDepth 500000 in
lemma B_5_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_5 8 xs.toFinset) B_5_8 :=
  buildBucketsBT_sound (by decide) gp_5 W_5_ok (buildPoolsSubBT_sound S_5_ok) A_5_ok B_5_7_ok C_5_8
def U_5_9 : List Nat := [5,16,25,30,38]
def P_5_9 : BT (Option BoundPool) := buildPoolsSubBT 6 W_5 r_5 S_5 ps_5 U_5_9
def N_5_9 : List NodeSpec := [a5 [] [5,30,38,16,25] [0,1,2,3,4,5,7,8]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_5_9 : checkNodesBT W_5 g_5 F_5 P_5_9 A_5 B_5_8 9 N_5_9 = true := by decide +kernel
def B_5_9 : BT (List (List Nat)) := buildBucketsBT W_5 N_5_9
set_option maxRecDepth 500000 in
lemma B_5_9_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_5 9 xs.toFinset) B_5_9 :=
  buildBucketsBT_sound (by decide) gp_5 W_5_ok (buildPoolsSubBT_sound S_5_ok) A_5_ok B_5_8_ok C_5_9
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_5_ok : forestRootCheck r_5 g_5 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11),(VAR 4,3,19)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_5_in : bucketContainsBT B_5_9 r_5 = true := by decide +kernel
lemma low_5 : Lower r_5 g_5 10 := lower_of_forestBT root_5_ok B_5_9_ok root_5_in
def g_6 := 0xfec0fec0fec0fec0
def r_6 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_6 : Lower r_6 g_6 5 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,8,9)]) (by decide +kernel) hc
def g_7 := 0xfe80fe80fe80fe80
def r_7 : List Nat := varsOf 15
def p_7 : List Nat := [7,7,7,9,9,10,10,11,12,12,13,14]
def q_7 : List Nat := [6,5,3,8,1,8,2,3,8,4,5,6]
def F_7 : Nat := fullMask 12
set_option maxHeartbeats 0 in
lemma gp_7 : goodPairs g_7 p_7 q_7 := goodPairs_of (by decide +kernel)
def W_7 : BT Decor := buildWiresBT 5 (mkBase p_7 q_7 r_7) [(0,2,3),(1,2,3),(3,4,5),(0,1,2),(1,1,2),(3,7,8),(2,0,3),(3,0,3),(1,1,3),(0,0,12),(0,0,3),(1,0,3),(3,4,0),(1,14,2),(2,0,2),(3,0,2),(3,2,15),(2,2,1),(3,21,0),(2,0,1),(1,23,2),(0,0,1),(1,0,1),(3,2,3)]
lemma W_7_ok : btAll (fun x => faithful p_7 q_7 x ∧ x.1 < 2^64) W_7 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_7 : List (List (Nat × Nat)) := [[],[(1,2)],[(0,1)],[(0,2),(1,2)],[(0,1),(1,2)],[(0,2)]]
def A_7 : BT (List (Nat × Nat)) := btOfList 3 al_7
set_option maxHeartbeats 0 in
lemma A_7_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_7 = g_7) A_7 := btAll_ofList (autos_of (by decide +kernel))
def S_7 : BT (Option (Nat × Nat)) := btOfList 1 []
lemma S_7_ok : btAll (fun o => ∀ p, o = some p → Slice r_7 g_7 p.1 p.2) S_7 := btAll_ofList (fun _ h => (List.not_mem_nil h).elim)
def ps_7 : BT (Option PoolSpec) := btOfList 1 []
def B_7_1 : BT (List (List Nat)) := BT.empty
lemma B_7_1_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_7 1 xs.toFinset) B_7_1 := .empty
def U_7_2 : List Nat := []
def P_7_2 : BT (Option BoundPool) := buildPoolsSubBT 1 W_7 r_7 S_7 ps_7 U_7_2
def N_7_2 : List NodeSpec := [([6,0,1],[],[]),([9,0,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_7_2 : checkNodesBT W_7 g_7 F_7 P_7_2 A_7 B_7_1 2 N_7_2 = true := by decide +kernel
def B_7_2 : BT (List (List Nat)) := buildBucketsBT W_7 N_7_2
set_option maxRecDepth 500000 in
lemma B_7_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_7 2 xs.toFinset) B_7_2 :=
  buildBucketsBT_sound (by decide) gp_7 W_7_ok (buildPoolsSubBT_sound S_7_ok) A_7_ok B_7_1_ok C_7_2
def U_7_3 : List Nat := []
def P_7_3 : BT (Option BoundPool) := buildPoolsSubBT 1 W_7 r_7 S_7 ps_7 U_7_3
def N_7_3 : List NodeSpec := [([10,11,1,2],[],[3]),([13,1,2,3],[],[]),([14,1,2,15],[],[3]),([16,1,2,3],[],[]),([0,1,17,3],[],[]),([18,19,1,3],[],[2]),([20,0,1,3],[],[]),([22,1,2,3],[],[]),([0,1,24,3],[],[]),([25,26,2,3],[],[4])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_7_3 : checkNodesBT W_7 g_7 F_7 P_7_3 A_7 B_7_2 3 N_7_3 = true := by decide +kernel
def B_7_3 : BT (List (List Nat)) := buildBucketsBT W_7 N_7_3
set_option maxRecDepth 500000 in
lemma B_7_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_7 3 xs.toFinset) B_7_3 :=
  buildBucketsBT_sound (by decide) gp_7 W_7_ok (buildPoolsSubBT_sound S_7_ok) A_7_ok B_7_2_ok C_7_3
def U_7_4 : List Nat := []
def P_7_4 : BT (Option BoundPool) := buildPoolsSubBT 1 W_7 r_7 S_7 ps_7 U_7_4
def N_7_4 : List NodeSpec := [([10,0,1,2,3],[],[0]),([14,0,1,2,3],[],[0,1,3,5]),([18,0,1,2,3],[],[0,1,3]),([27,0,1,2,3],[],[4]),([0,1,2,3,15],[],[0,1,2,4]),([0,1,26,2,3],[],[0]),([25,0,1,2,3],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_7_4 : checkNodesBT W_7 g_7 F_7 P_7_4 A_7 B_7_3 4 N_7_4 = true := by decide +kernel
def B_7_4 : BT (List (List Nat)) := buildBucketsBT W_7 N_7_4
set_option maxRecDepth 500000 in
lemma B_7_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_7 4 xs.toFinset) B_7_4 :=
  buildBucketsBT_sound (by decide) gp_7 W_7_ok (buildPoolsSubBT_sound S_7_ok) A_7_ok B_7_3_ok C_7_4
def U_7_5 : List Nat := []
def P_7_5 : BT (Option BoundPool) := buildPoolsSubBT 1 W_7 r_7 S_7 ps_7 U_7_5
def N_7_5 : List NodeSpec := [([0,1,2,3],[],[0,1,2,3,4,5])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_7_5 : checkNodesBT W_7 g_7 F_7 P_7_5 A_7 B_7_4 5 N_7_5 = true := by decide +kernel
def B_7_5 : BT (List (List Nat)) := buildBucketsBT W_7 N_7_5
set_option maxRecDepth 500000 in
lemma B_7_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_7 5 xs.toFinset) B_7_5 :=
  buildBucketsBT_sound (by decide) gp_7 W_7_ok (buildPoolsSubBT_sound S_7_ok) A_7_ok B_7_4_ok C_7_5
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_7_ok : forestRootCheck r_7 g_7 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,1,9)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_7_in : bucketContainsBT B_7_5 r_7 = true := by decide +kernel
lemma low_7 : Lower r_7 g_7 6 := lower_of_forestBT root_7_ok B_7_5_ok root_7_in
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
def g_10 := 0xfec8e000fec8e000
def r_10 : List Nat := varsOf 31
def p_10 : List Nat := [13,13,13,14,14,14,15,15,19,19,19,22,22,22,23,23,25,25,25,26,26,26,27,28,28,28,29]
def q_10 : List Nat := [12,9,5,12,10,6,11,7,18,17,3,20,18,6,21,7,24,17,9,24,18,10,11,24,20,12,21]
def F_10 : Nat := fullMask 27
set_option maxHeartbeats 0 in
lemma gp_10 : goodPairs g_10 p_10 q_10 := goodPairs_of (by decide +kernel)
def W_10 : BT Decor := buildWiresBT 7 (mkBase p_10 q_10 r_10) [(0,1,3),(0,2,4),(1,5,6),(1,1,3),(1,2,4),(0,8,9),(3,6,9),(3,5,8),(0,8,4),(0,2,13),(1,2,13),(3,14,15),(2,2,4),(3,2,4),(3,0,8),(1,0,6),(0,20,8),(0,11,8),(1,0,5),(0,3,9),(0,1,24),(1,0,25),(2,1,3),(3,1,3),(1,1,24),(3,0,29),(3,17,8),(3,6,8),(2,2,13),(3,2,13),(0,23,4),(1,35,2),(3,6,23),(0,23,9),(3,6,3),(0,20,3),(3,40,1),(3,2,3),(3,1,4),(1,42,43),(1,17,27),(1,1,2),(0,46,3),(0,3,4),(2,23,2),(2,23,4),(0,20,1),(3,43,3),(3,27,9),(2,46,48),(0,46,4),(3,55,3),(0,47,4),(1,3,4),(3,48,58),(1,17,5),(2,3,4),(3,3,4),(0,1,58),(2,1,4),(1,64,0),(2,2,1),(3,66,3),(0,1,2),(1,0,68),(1,1,48),(3,2,58),(3,2,48),(2,8,4),(0,1,9),(3,2,8),(1,1,4),(0,76,3),(3,0,58),(0,1,4),(3,17,3),(1,2,3),(2,1,2)]
lemma W_10_ok : btAll (fun x => faithful p_10 q_10 x ∧ x.1 < 2^64) W_10 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_10 : List (List (Nat × Nat)) := [[],[(1,2),(3,4)]]
def A_10 : BT (List (Nat × Nat)) := btOfList 1 al_10
set_option maxHeartbeats 0 in
lemma A_10_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_10 = g_10) A_10 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_10_0 : Slice r_10 g_10 (subcubeFast 1 0) 7 := by
  have hc : Lower (varsOf 30) 0xfcc0c000fcc0c000 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_1 : Slice r_10 g_10 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) 0xfffaf000fffaf000 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_2 : Slice r_10 g_10 (subcubeFast 1 4) 4 := by
  have hc : Lower (varsOf 26) 0xffcccc00ffcccc00 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_3 : Slice r_10 g_10 (subcubeFast 4 16) 4 := by
  have hc : Lower (varsOf 11) 0xee88ee88ee88ee88 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_4 : Slice r_10 g_10 (subcubeFast 2 8) 4 := by
  have hc : Lower (varsOf 21) 0xfafaa0a0fafaa0a0 4 := carry_of (swaps := [(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 2) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_5 : Slice r_10 g_10 (subcubeFast 1 16) 4 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_6 : Slice r_10 g_10 (subcubeFast 1 2) 4 := by
  have hc : Lower (varsOf 28) 0xfff0f000fff0f000 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_7 : Slice r_10 g_10 (identDom 1 4) 6 := by
  have hc : Lower (varsOf 15) 0xecc8ecc8ecc8ecc8 6 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_7
  exact slice_ident (u := 1) (v := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_8 : Slice r_10 g_10 (identDom 2 3) 6 := by
  have hc : Lower (varsOf 23) 0xf8f8e0e0f8f8e0e0 6 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_7
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_9 : Slice r_10 g_10 (identDom 0 3) 5 := by
  have hc : Lower (varsOf 23) 0xeaeaa0a0eaeaa0a0 5 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,4)]) (by decide +kernel) low_8
  exact slice_ident (u := 0) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_10 : Slice r_10 g_10 (identDom 1 2) 5 := by
  have hc : Lower (varsOf 27) 0xeecccc00eecccc00 5 := carry_of (swaps := [(1,3),(2,4)]) (by decide +kernel) low_8
  exact slice_ident (u := 1) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_11 : Slice r_10 g_10 (subcubeFast 0 1) 4 := by
  have hc : Lower (varsOf 30) 0xffccf000ffccf000 4 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
def S_10 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 1 0,7),some (subcubeFast 0 2,5),some (subcubeFast 1 4,4),some (subcubeFast 4 16,4),some (subcubeFast 2 8,4),some (subcubeFast 1 16,4),some (subcubeFast 1 2,4),some (identDom 1 4,6),some (identDom 2 3,6),some (identDom 0 3,5),some (identDom 1 2,5),some (subcubeFast 0 1,4)]
lemma S_10_ok : btAll (fun o => ∀ p, o = some p → Slice r_10 g_10 p.1 p.2) S_10 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_10_0) (forall_cons (fun _ h => by cases h; exact sl_10_1) (forall_cons (fun _ h => by cases h; exact sl_10_2) (forall_cons (fun _ h => by cases h; exact sl_10_3) (forall_cons (fun _ h => by cases h; exact sl_10_4) (forall_cons (fun _ h => by cases h; exact sl_10_5) (forall_cons (fun _ h => by cases h; exact sl_10_6) (forall_cons (fun _ h => by cases h; exact sl_10_7) (forall_cons (fun _ h => by cases h; exact sl_10_8) (forall_cons (fun _ h => by cases h; exact sl_10_9) (forall_cons (fun _ h => by cases h; exact sl_10_10) (forall_cons (fun _ h => by cases h; exact sl_10_11) (fun _ h => (List.not_mem_nil h).elim)))))))))))))
def ps_10 : BT (Option PoolSpec) := btOfList 4 [q 3 [],q 2 [],q 6 [],q 4 [],q 11 [],q 1 [],q 9 [],q 5 [],q 10 [],q 7 [],q 0 [],q 0 [12292],q 0 [16388],q 8 [],q 0 [8196],q 0 [16396]]
def B_10_1 : BT (List (List Nat)) := BT.empty
lemma B_10_1_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_10 1 xs.toFinset) B_10_1 := .empty
def U_10_2 : List Nat := []
def P_10_2 : BT (Option BoundPool) := buildPoolsSubBT 4 W_10 r_10 S_10 ps_10 U_10_2
def N_10_2 : List NodeSpec := [([0,7,10],[],[]),([11,12,0],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_10_2 : checkNodesBT W_10 g_10 F_10 P_10_2 A_10 B_10_1 2 N_10_2 = true := by decide +kernel
def B_10_2 : BT (List (List Nat)) := buildBucketsBT W_10 N_10_2
set_option maxRecDepth 500000 in
lemma B_10_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_10 2 xs.toFinset) B_10_2 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok (buildPoolsSubBT_sound S_10_ok) A_10_ok B_10_1_ok C_10_2
def U_10_3 : List Nat := []
def P_10_3 : BT (Option BoundPool) := buildPoolsSubBT 4 W_10 r_10 S_10 ps_10 U_10_3
def N_10_3 : List NodeSpec := [([16,0,1,3],[],[]),([0,5,6,10],[],[0]),([0,7,8,9],[],[0]),([17,18,12,0],[],[0]),([11,19,1,3],[],[]),([11,0,5,8],[],[0]),([5,2,21,4],[],[]),([22,0,1,3],[],[]),([11,1,23,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_10_3 : checkNodesBT W_10 g_10 F_10 P_10_3 A_10 B_10_2 3 N_10_3 = true := by decide +kernel
def B_10_3 : BT (List (List Nat)) := buildBucketsBT W_10 N_10_3
set_option maxRecDepth 500000 in
lemma B_10_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_10 3 xs.toFinset) B_10_3 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok (buildPoolsSubBT_sound S_10_ok) A_10_ok B_10_2_ok C_10_3
def U_10_4 : List Nat := [0,1]
def P_10_4 : BT (Option BoundPool) := buildPoolsSubBT 4 W_10 r_10 S_10 ps_10 U_10_4
def N_10_4 : List NodeSpec := [([18,0,1,3,31],[0],[]),([11,0,1,3,8],[0,1],[0]),([11,0,5,1,3],[1],[0]),([37,1,2,3,4],[],[]),([17,12,0,2,4],[],[0]),([17,18,1,23,3],[],[0]),([41,2,20,3,4],[],[]),([39,0,1,2,13],[],[]),([18,12,0,2,4],[],[0]),([0,1,2,24,13],[],[]),([0,25,2,29,4],[],[1]),([1,23,2,24,4],[],[]),([1,38,2,3,4],[],[1]),([5,2,20,8,4],[],[0,1]),([0,1,7,3,9],[],[0]),([1,26,2,24,4],[],[]),([19,1,6,3,9],[],[0]),([1,23,36,3,4],[],[]),([0,5,6,8,9],[],[0,1]),([33,34,0,1,3],[],[0]),([32,0,1,3,9],[],[0]),([0,5,2,10,4],[],[0,1]),([17,18,0,5,8],[],[0]),([19,1,2,24,4],[],[]),([17,18,19,1,3],[],[0]),([30,1,2,24,4],[],[]),([17,27,18,28,0],[],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_10_4 : checkNodesBT W_10 g_10 F_10 P_10_4 A_10 B_10_3 4 N_10_4 = true := by decide +kernel
def B_10_4 : BT (List (List Nat)) := buildBucketsBT W_10 N_10_4
set_option maxRecDepth 500000 in
lemma B_10_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_10 4 xs.toFinset) B_10_4 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok (buildPoolsSubBT_sound S_10_ok) A_10_ok B_10_3_ok C_10_4
def U_10_5 : List Nat := (r 0 8)
def P_10_5 : BT (Option BoundPool) := buildPoolsSubBT 4 W_10 r_10 S_10 ps_10 U_10_5
def N_10_5 : List NodeSpec := [([42,1,20,3,4],[0],[]),([18,0,1,2,3,13],[0],[]),([17,18,0,1,3,8],[0,1],[0]),([17,0,1,2,3,13],[1],[]),([17,18,0,5,1,3],[1],[0]),a5 [53] [1] [1],([0,1,2,24,29,4],[1,0],[0]),([0,25,1,2,24,4],[1,0],[0,1]),([0,5,1,6,3,9],[1,0],[0,1]),([11,0,1,3],[1,0],[0,1]),([0,1,2,24,8,4],[1,3,0],[0]),([0,5,2,8,4,9],[2,3],[0,1]),([17,1,23,2,3,4],[2,3],[0]),([39,28,0,1,2,4],[3],[]),([39,0,1,2,8,4],[3,0],[0]),([50,1,23,2,3,4],[2,3,4],[]),([19,1,6,2,3,4],[2,4],[0]),([1,23,2,3,4,9],[3,2,4],[0,1]),([49,1,23,2,3,4],[4],[]),([5,1,2,20,3,4],[4],[0,1]),([51,1,2,20,3,4],[4],[]),([1,35,23,2,3,4],[4],[0,1]),a5 [7] [4,1] [0,1],([19,1,2,3,4,9],[4,2,3],[0]),([0,52,1,2,48,4],[0,5],[]),([0,5,1,2,24,4],[1,0,5],[0,1]),u5 [32] [1,4,5],a5 [10] [1,4,5] [0,1],([0,1,2,47,48,4],[5,1,0],[]),e5 [57] [6,1,0],([59,0,1,2,48],[0,7,3],[]),([59,0,1,2],[7,3,0],[]),([33,0,1,2,3,13],[],[0]),([17,19,1,2,3,4],[],[0]),e5 [60] [],([18,19,1,2,3,4],[],[0]),e5 [44] [],([17,0,5,2,8,4],[],[0]),e5 [56] [],e5 [54] [],([18,1,23,2,3,4],[],[0]),([18,0,5,2,8,4],[],[0]),([34,0,1,2,3,13],[],[0]),e5 [45] [],([17,18,28,0,1,3],[],[0,1]),([17,27,18,0,1,3],[],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_10_5 : checkNodesBT W_10 g_10 F_10 P_10_5 A_10 B_10_4 5 N_10_5 = true := by decide +kernel
def B_10_5 : BT (List (List Nat)) := buildBucketsBT W_10 N_10_5
set_option maxRecDepth 500000 in
lemma B_10_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_10 5 xs.toFinset) B_10_5 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok (buildPoolsSubBT_sound S_10_ok) A_10_ok B_10_4_ok C_10_5
def U_10_6 : List Nat := (r 0 6++[7,8,9])
def P_10_6 : BT (Option BoundPool) := buildPoolsSubBT 4 W_10 r_10 S_10 ps_10 U_10_6
def N_10_6 : List NodeSpec := [a5 [72,48] [0,1] [1],([17,18,0,1,3],[0,1],[0]),a5 [42,48] [1,0] [1],([0,1,2,24,4],[1,0],[0,1]),a5 [18,5] [1,0] [0,1],u5 [18,8] [1,0],e5 [67] [2,0],a5 [17,27] [0,3] [0,1],([1,69,2,3,4],[0,3],[]),([73,0,1,2,3],[0,3],[]),([61,62,0,1,2],[0,3],[0]),([42,0,1,6,3,4],[1,0,3],[0]),a5 [5,9] [1,2,0,3] [0,1],a5 [5,6] [1,2,0,3] [0,1],a5 [8,9] [1,2,3,0] [0,1],([0,74,2,3,4],[1,3],[]),([75,0,1,3,4],[1,3],[]),([71,0,1,3,4],[1,3],[]),a5 [47] [1,3,0] [0,1],u5 [52] [2,0,1,3],([65,1,2,3,4],[3,0],[]),([78,1,2,3,4],[3,0],[]),([0,63,2,3,4],[3,0],[]),([19,1,2,3,4],[3,2],[0]),([0,5,2,8,4],[3,2],[0,1]),([1,23,2,3,4],[3,4],[0,1]),u5 [17,5] [0,3,5,1],a5 [17,8] [0,5,1] [0,1],a5 [46,48] [0,5,3,1] [0,1],a5 [24] [1,3,5,0] [0,1],u5 [39] [1,4,3,5,0],e5 [48,70] [3,5],a5 [18,28] [5,0,1] [0,1],u5 [42,43] [5,1,3,0],a5 [17,28] [5,3] [0,1],([0,1,2,48,58],[3,0,7],[0]),e5 [48] [7,3,0],e5 [77] [7,3,0],e5 [80] [7,3,5,0],([0,68,46,3,4],[0,1,8],[]),([0,79,2,3,76],[3,0,9],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_10_6 : checkNodesBT W_10 g_10 F_10 P_10_6 A_10 B_10_5 6 N_10_6 = true := by decide +kernel
def B_10_6 : BT (List (List Nat)) := buildBucketsBT W_10 N_10_6
set_option maxRecDepth 500000 in
lemma B_10_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_10 6 xs.toFinset) B_10_6 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok (buildPoolsSubBT_sound S_10_ok) A_10_ok B_10_5_ok C_10_6
def U_10_7 : List Nat := (r 0 4++[5]++r 7 9)
def P_10_7 : BT (Option BoundPool) := buildPoolsSubBT 4 W_10 r_10 S_10 ps_10 U_10_7
def N_10_7 : List NodeSpec := [a5 [18] [1,0] [0,1],a5 [81] [1,3,0] [1],a5 [46] [1,3,0,5] [0,1],u5 [61] [0,7,5,3],u5 [17] [0,7,5,3],a5 [82] [1,0,3,8] [1],a5 [58] [3,0,10,7] [0,1],a5 [8] [3,2,10,0,1] [0,1],u5 [64] [10,0,7,3,9],a5 [5] [1,3,11,0] [0,1],u5 [79] [3,12,1,0,5],a5 [42] [1,5,3,0,13] [0,1],u5 [68] [14,0,3],a5 [48] [3,15,0,5,1] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_10_7 : checkNodesBT W_10 g_10 F_10 P_10_7 A_10 B_10_6 7 N_10_7 = true := by decide +kernel
def B_10_7 : BT (List (List Nat)) := buildBucketsBT W_10 N_10_7
set_option maxRecDepth 500000 in
lemma B_10_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_10 7 xs.toFinset) B_10_7 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok (buildPoolsSubBT_sound S_10_ok) A_10_ok B_10_6_ok C_10_7
def U_10_8 : List Nat := [10]
def P_10_8 : BT (Option BoundPool) := buildPoolsSubBT 4 W_10 r_10 S_10 ps_10 U_10_8
def N_10_8 : List NodeSpec := [a5 [] [10] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_10_8 : checkNodesBT W_10 g_10 F_10 P_10_8 A_10 B_10_7 8 N_10_8 = true := by decide +kernel
def B_10_8 : BT (List (List Nat)) := buildBucketsBT W_10 N_10_8
set_option maxRecDepth 500000 in
lemma B_10_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_10 8 xs.toFinset) B_10_8 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok (buildPoolsSubBT_sound S_10_ok) A_10_ok B_10_7_ok C_10_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_10_ok : forestRootCheck r_10 g_10 [(VAR 0,12,13),(VAR 1,12,14),(VAR 2,9,13),(VAR 3,5,13),(VAR 4,3,19)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_10_in : bucketContainsBT B_10_8 r_10 = true := by decide +kernel
lemma low_10 : Lower r_10 g_10 9 := lower_of_forestBT root_10_ok B_10_8_ok root_10_in
def g_11 := 0xfee0fee0fee0fee0
def r_11 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_11 : Lower r_11 g_11 5 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,4,5)]) (by decide +kernel) hc
def g_12 := 0xffeef880ffeef880
def r_12 : List Nat := varsOf 31
def p_12 : List Nat := [7,7,7,11,11,11,12,12,13,13,14,14,17,17,18,18,19,21,21,22,22,24,24,25,26,28]
def q_12 : List Nat := [6,5,3,10,9,3,8,4,9,5,10,6,16,1,16,2,3,20,5,20,6,16,8,9,10,20]
def F_12 : Nat := fullMask 26
set_option maxHeartbeats 0 in
lemma gp_12 : goodPairs g_12 p_12 q_12 := goodPairs_of (by decide +kernel)
def W_12 : BT Decor := buildWiresBT 8 (mkBase p_12 q_12 r_12) [(0,0,1),(1,5,3),(1,2,4),(0,6,7),(1,3,4),(1,1,4),(0,0,10),(1,11,3),(3,2,12),(0,1,4),(3,14,10),(1,2,3),(0,5,7),(1,17,3),(3,2,3),(3,19,0),(1,0,4),(0,1,21),(1,0,1),(3,19,23),(0,2,6),(1,25,4),(2,0,3),(3,22,3),(3,2,6),(2,23,3),(1,6,4),(2,2,4),(3,32,6),(2,5,3),(1,34,4),(1,22,3),(3,5,3),(1,5,4),(0,0,7),(3,3,38),(3,5,9),(3,5,16),(0,3,4),(3,43,9),(2,27,4),(0,0,9),(0,1,7),(3,47,0),(0,0,16),(1,49,4),(3,0,4),(3,51,16),(3,1,4),(1,19,53),(3,19,21),(0,16,21),(3,1,21),(3,14,16),(0,0,4),(1,59,3),(3,2,60),(1,2,60),(3,14,0),(1,59,1),(2,1,3),(3,65,21),(1,11,2),(3,27,21),(3,65,0),(1,69,4),(1,0,3),(2,5,4),(1,72,3),(0,1,3),(3,74,0),(1,19,5),(1,5,2),(1,1,3),(1,19,59),(2,1,2),(3,80,21),(1,20,4),(2,0,4),(1,27,4),(3,74,21),(3,5,71),(2,3,4),(1,87,5),(0,23,16),(2,6,4),(2,1,0),(1,27,91),(0,1,16),(3,5,7),(3,91,16),(2,0,1),(1,19,96),(0,0,78),(3,19,1),(3,80,0),(1,100,4),(1,75,4),(0,0,3),(1,103,4),(3,3,4),(1,105,2),(3,87,0),(1,2,43),(1,1,43),(1,53,3),(3,3,21),(3,14,3),(1,59,2),(1,96,3),(2,0,2),(2,0,43),(1,1,2),(0,0,117),(3,27,1),(1,53,2),(3,2,71),(2,16,4),(3,1,3),(3,123,0),(1,115,4),(1,19,4),(1,27,1),(3,0,3),(1,128,1),(3,2,4),(1,0,2)]
lemma W_12_ok : btAll (fun x => faithful p_12 q_12 x ∧ x.1 < 2^64) W_12 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_12 : List (List (Nat × Nat)) := [[],[(0,1)]]
def A_12 : BT (List (Nat × Nat)) := btOfList 1 al_12
set_option maxHeartbeats 0 in
lemma A_12_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_12 = g_12) A_12 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_12_0 : Slice r_12 g_12 (subcubeFast 4 0) 6 := by
  have hc : Lower (varsOf 27) 0xffee8800ffee8800 6 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_1 : Slice r_12 g_12 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) 0xfffffcc0fffffcc0 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_2 : Slice r_12 g_12 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) 0xfffffaa0fffffaa0 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_3 : Slice r_12 g_12 (subcubeFast 0 4) 5 := by
  have hc : Lower (varsOf 27) 0xffeeff88ffeeff88 5 := carry_of (swaps := [(2,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_4 : Slice r_12 g_12 (subcubeFast 8 0) 5 := by
  have hc : Lower (varsOf 23) 0xeeee8080eeee8080 5 := carry_of (swaps := [(0,1),(1,2),(3,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_5 : Slice r_12 g_12 (subcubeFast 16 0) 5 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_3
set_option maxHeartbeats 0 in
lemma sl_12_6 : Slice r_12 g_12 (subcubeFast 8 4) 4 := by
  have hc : Lower (varsOf 19) 0xeeee8888eeee8888 4 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 8) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_7 : Slice r_12 g_12 (subcubeFast 16 2) 4 := by
  have hc : Lower (varsOf 13) 0xfaa0faa0faa0faa0 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_8 : Slice r_12 g_12 (subcubeFast 16 1) 4 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_9 : Slice r_12 g_12 (identDom 0 3) 5 := by
  have hc : Lower (varsOf 23) 0xeeeea8a8eeeea8a8 5 := carry_of (swaps := [(0,3),(2,3),(3,4)]) (by decide +kernel) low_6
  exact slice_ident (u := 0) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_10 : Slice r_12 g_12 (identDom 1 3) 5 := by
  have hc : Lower (varsOf 23) 0xeeeec8c8eeeec8c8 5 := carry_of (swaps := [(0,1),(1,3),(2,3),(3,4)]) (by decide +kernel) low_6
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_11 : Slice r_12 g_12 (identDom 0 1) 5 := by
  have hc : Lower (varsOf 29) 0xffaafaa0ffaafaa0 5 := carry_of (swaps := [(0,2),(1,4)]) (by decide +kernel) low_11
  exact slice_ident (u := 0) (v := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_12 : Slice r_12 g_12 (subcubeFast 2 0) 4 := by
  have hc : Lower (varsOf 29) 0xffaaf000ffaaf000 4 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_13 : Slice r_12 g_12 (subcubeFast 1 0) 4 := by
  have hc : Lower (varsOf 30) 0xffccf000ffccf000 4 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
def S_12 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 4 0,6),some (subcubeFast 0 1,5),some (subcubeFast 0 2,5),some (subcubeFast 0 4,5),some (subcubeFast 8 0,5),some (subcubeFast 16 0,5),some (subcubeFast 8 4,4),some (subcubeFast 16 2,4),some (subcubeFast 16 1,4),some (identDom 0 3,5),some (identDom 1 3,5),some (identDom 0 1,5),some (subcubeFast 2 0,4),some (subcubeFast 1 0,4)]
lemma S_12_ok : btAll (fun o => ∀ p, o = some p → Slice r_12 g_12 p.1 p.2) S_12 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_12_0) (forall_cons (fun _ h => by cases h; exact sl_12_1) (forall_cons (fun _ h => by cases h; exact sl_12_2) (forall_cons (fun _ h => by cases h; exact sl_12_3) (forall_cons (fun _ h => by cases h; exact sl_12_4) (forall_cons (fun _ h => by cases h; exact sl_12_5) (forall_cons (fun _ h => by cases h; exact sl_12_6) (forall_cons (fun _ h => by cases h; exact sl_12_7) (forall_cons (fun _ h => by cases h; exact sl_12_8) (forall_cons (fun _ h => by cases h; exact sl_12_9) (forall_cons (fun _ h => by cases h; exact sl_12_10) (forall_cons (fun _ h => by cases h; exact sl_12_11) (forall_cons (fun _ h => by cases h; exact sl_12_12) (forall_cons (fun _ h => by cases h; exact sl_12_13) (fun _ h => (List.not_mem_nil h).elim)))))))))))))))
def ps_12 : BT (Option PoolSpec) := btOfList 6 [q 0 [16388,16389,41019],q 11 [12309,24587],q 0 [],q 7 [],q 8 [],q 6 [],q 13 [],q 12 [],q 2 [],q 0 [16385,86080],q 0 [16385,86023],q 9 [],q 3 [],q 1 [],q 0 [16389,40960],q 0 [16388,65595],q 0 [16384,16385],q 0 [16384,12525],q 0 [16388,59],q 0 [16384,4333],q 4 [],q 0 [12294,263],q 5 [],q 11 [12297],q 0 [4096,4097],q 11 [],q 11 [12311],q 11 [8213],q 11 [12299],q 0 [16384,241741],q 11 [12309],q 0 [16386,16387],q 0 [6,65903],q 0 [16398],q 0 [16397],q 0 [79],q 0 [16391],q 0 [16386],q 0 [16385,86031],q 0 [16384],q 0 [16385],q 0 [65536],q 0 [12290],q 0 [4096],q 0 [4098],q 0 [4098,12673],q 0 [323],q 0 [4097],q 0 [12293],q 0 [12289],q 0 [16450],q 0 [16461],q 0 [12288],q 10 []]
def B_12_2 : BT (List (List Nat)) := BT.empty
lemma B_12_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 2 xs.toFinset) B_12_2 := .empty
def U_12_3 : List Nat := []
def P_12_3 : BT (Option BoundPool) := buildPoolsSubBT 6 W_12 r_12 S_12 ps_12 U_12_3
def N_12_3 : List NodeSpec := [([0,1,8,9],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_3 : checkNodesBT W_12 g_12 F_12 P_12_3 A_12 B_12_2 3 N_12_3 = true := by decide +kernel
def B_12_3 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_3
set_option maxRecDepth 500000 in
lemma B_12_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 3 xs.toFinset) B_12_3 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_2_ok C_12_3
def U_12_4 : List Nat := (r 0 4)
def P_12_4 : BT (Option BoundPool) := buildPoolsSubBT 6 W_12 r_12 S_12 ps_12 U_12_4
def N_12_4 : List NodeSpec := [([15,0,2,3,16],[0],[]),([19,15,0,2,3],[0],[]),([29,5,23,3,4],[1],[]),([0,1,3,8,4],[2],[0]),([0,1,3,7,31],[2],[]),([39,1,3,38,7],[3],[]),([27,1,3,38,7],[3],[]),([0,1,18,4,7],[],[]),([42,23,2,3,4],[],[]),([41,0,1,3,7],[],[]),([40,0,1,3,7],[],[]),([30,37,5,2,4],[],[]),([27,22,2,36,4],[],[]),([0,1,3,35,7],[],[]),([0,1,3,6,26],[],[]),([0,1,3,33,4],[],[]),([13,11,1,3,4],[],[]),([20,22,2,3,4],[],[]),([30,5,2,6,4],[],[]),([5,24,2,3,4],[],[]),([0,1,6,7,9],[],[0]),([27,28,22,2,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_4 : checkNodesBT W_12 g_12 F_12 P_12_4 A_12 B_12_3 4 N_12_4 = true := by decide +kernel
def B_12_4 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_4
set_option maxRecDepth 500000 in
lemma B_12_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 4 xs.toFinset) B_12_4 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_3_ok C_12_4
def U_12_5 : List Nat := ([0]++r 2 31)
def P_12_5 : BT (Option BoundPool) := buildPoolsSubBT 6 W_12 r_12 S_12 ps_12 U_12_5
def N_12_5 : List NodeSpec := [([19,0,1,2,60,4],[2],[]),e5 [52] [2],e5 [54] [2],([32,0,1,3,6,4],[2],[0]),([29,0,1,3,6,4],[2],[]),([0,1,2,6,16,4],[2],[]),([19,0,1,2,6,4],[2],[]),([5,0,1,3,38,7],[3,4],[]),([27,1,2,3,4,38],[3,4],[0]),([27,22,2,3,4],[3,4],[0]),([15,0,2,3],[3,4,0],[0]),([0,1,3,38,7],[3,4,2],[0,1]),([45,0,1,3,7,9],[4],[]),([46,0,1,3,7,9],[4],[]),([32,27,5,1,3,4],[3,5],[]),([44,0,1,2],[4,3,5],[]),([44,0,1,2,9],[4,3,5],[]),([27,5,1,3,4,7],[5,3],[0]),([5,0,1,3,7,9],[5,3,4],[0]),([11,1,2,67,3,4],[6],[]),([0,1,2,3,38,7],[3,6,7,2],[]),([0,1,2,3,104,10],[4,6,7],[]),([100,1,2,3,4,21],[7],[]),([69,1,2,3,4,21],[7],[]),([49,1,23,2,3,4],[7],[]),e5 [50] [6,7,8],e5 [56] [9],([57,0,2,3,16,4],[10],[]),([19,57,0,2,3,4],[10],[]),([0,1,2,60,16,4],[11,4,2],[]),e5 [88] [2,12],e5 [73] [2,12],e5 [90] [2,12],e5 [6] [2,12],e5 [12] [11,2,12],u5 [31] [11,7,2,12],e5 [94] [12],([0,1,25,3,6,4],[12],[0]),e5 [76] [12],([53,0,93,2,3,4],[12],[]),([5,39,1,3,4,7],[12,3],[0]),e5 [66] [13],([27,1,2,3,68,4],[13],[]),e5 [81] [13],e5 [85] [13],([86,5,1,2,3,4],[13],[]),e5 [102] [13],e5 [70] [13],e5 [101] [13],([98,1,2,3,71,4],[13],[]),([27,92,1,2,3,4],[13],[]),([28,0,22,2,3,4],[13,3,7],[0]),([11,1,2,3,12,4],[6,8,4,14],[0,1]),([19,11,1,2,3,4],[8,14],[1]),([11,1,2,3,16,4],[14],[]),e5 [58] [15],([59,1,2,3,16,21],[16],[1]),([19,59,1,2,3,21],[16],[1]),([0,1,2,60,62,4],[11,4,17],[]),([61,0,1,2,60,4],[17],[]),([19,63,1,2,3,4],[18],[]),([63,1,2,3,16,4],[18],[]),([0,64,2,3,16,4],[6,4,19],[]),([19,0,64,2,3,4],[19],[]),([0,1,2,3,38,9],[3,4,6,7,20],[]),([27,22,1,2,3,4],[3,20],[]),([27,5,2,3,78,4],[8,20],[]),([0,1,2,3,84,9],[11,20],[]),([27,65,5,2,3,4],[13,20],[]),([5,2,3,71,78,4],[20,13],[]),([69,1,2,3,71,4],[13,21],[]),([17,0,1,3,4,7],[5,2,22],[0]),([0,1,2,6,4,9],[11,7,22],[0]),([34,0,1,3,4,7],[22],[0]),([94,0,1,3,4,7],[22,2],[]),([75,1,2,3,4,21],[22,7],[]),([0,1,3,6,4,7],[22,12],[0]),([5,23,2,3,16,4],[23,7,24],[0]),([30,5,2,3,4],[25,3],[0]),([37,5,23,2,3,4],[13,25,26,7],[0]),([5,23,2,77,3,4],[27,7],[]),([19,5,23,2,3,4],[13,28,24],[0]),e5 [79] [29],([5,23,2,3,6,4],[30,7,13,24],[0]),([83,19,51,1,2,3],[31],[1]),([83,51,1,2,3,16],[31],[1]),e5 [95] [32],u5 [24] [],e5 [82] [],([69,0,1,3,4,7],[],[]),([20,1,2,3,4,21],[],[0]),([96,0,99,2,3,4],[],[]),([87,0,1,2,6,4],[],[]),([32,34,0,1,3,4],[],[]),u5 [42] [],e5 [97] [],e5 [55] [],u5 [35] [],e5 [89] [],([48,0,1,3,4,7],[],[]),([32,75,0,1,3,4],[],[]),([32,69,0,1,3,4],[],[]),([29,5,0,1,3,4],[],[0]),u5 [41] [],u5 [40] []]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_5 : checkNodesBT W_12 g_12 F_12 P_12_5 A_12 B_12_4 5 N_12_5 = true := by decide +kernel
def B_12_5 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_5
set_option maxRecDepth 500000 in
lemma B_12_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 5 xs.toFinset) B_12_5 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_4_ok C_12_5
def U_12_6 : List Nat := (r 2 7++r 10 5++r 16 10++[28,31]++r 33 20)
def P_12_6 : BT (Option BoundPool) := buildPoolsSubBT 6 W_12 r_12 S_12 ps_12 U_12_6
def N_12_6 : List NodeSpec := [([27,1,2,3,4,21],[3,4,5],[0]),([0,1,3,7,9],[3,4,5],[0,1]),([87,105,0,1,2],[3,5],[0]),e5 [124] [3,5],([116,1,2,3,4],[3,5],[]),([0,1,113,3,4],[3,5],[]),([112,0,1,2,4],[3,5],[]),([0,1,3,4,7],[3,5],[]),([0,1,106,3,4],[3,5],[]),([0,1,2,43,9],[3,5,4],[0]),([39,0,1,3,4,7],[3,5,4],[0,1]),e5 [9] [4,3,5],([0,1,3,4,7,9],[4,3,5],[]),([121,0,1,3,4],[4,5],[]),([105,0,1,3,7],[5,3],[]),([124,1,2,3,4],[5,3],[]),e5 [118] [5,3],([27,0,1,3,4,7],[5,3,4],[0,1]),a5 [103,10] [3,4,6] [0,1],e5 [27,84] [4,6],([83,27,1,2,3,4],[4,6,3],[]),e5 [83,80] [4,6,3],e5 [83,74] [4,6,3],u5 [5,38] [3,4,7],e5 [83,65] [4,6,7,3],u5 [5,77] [7,2],e5 [125] [4,5,7,8],u5 [104] [4,7,8,5],e5 [39] [7,8,4,5,6],a5 [27,10] [8,4,6] [1],a5 [115,10] [8,4,6] [1],([27,5,1,2,3,4],[8,6,5,4],[0]),([27,91,1,2,3,4],[8,6,5,4],[0]),u5 [45,9] [4,11],u5 [46,9] [4,11],u5 [27,9] [4,11,5],([103,1,2,71,4],[11,4,5],[]),u5 [84] [4,7,8,2,12,11],e5 [110] [4,8,2,12],e5 [46] [7,8,2,12,4,6],e5 [107] [7,8,2,12,4,6],e5 [27] [8,7,12,2,4,6],e5 [45] [11,4,8,7,12,2],([5,0,2,3,78,4],[5,3,13,7],[0,1]),e5 [27,119] [8,11,13,6],e5 [27,127] [11,7,6,13],u5 [30] [13,2,12,3],u5 [37,5] [13,8,7,6],([57,0,2,3,4],[13,10,3],[0]),([11,1,2,3,4],[4,6,14,3],[0,1]),([59,1,2,3,21],[13,3,16],[0,1]),([0,1,2,60,4],[3,4,17],[0]),u5 [60] [3,4,17,12],([63,1,2,3,4],[3,4,18],[0]),([0,64,2,3,4],[8,4,19],[0]),u5 [98] [2,12,20,11,3],a5 [38] [3,4,2,12,20,7] [0,1],u5 [72] [3,4,2,12,20,7,6],([0,1,3,108,4],[3,20,12],[]),a5 [11] [8,4,2,12,20,6] [0,1],u5 [27,65] [11,13,8,7,20],u5 [5] [13,2,12,20,3,6,7],([0,129,2,3,4],[13,20,3],[]),u5 [5,9] [20,7,3,4,6],u5 [87,5] [20,7,6,3,4],([0,2,3,109,4],[5,8,22],[]),u5 [34] [6,7,12,2,22],u5 [6] [6,13,7,8,2,12,22],([0,1,120,3,4],[8,5,22],[]),u5 [75] [13,7,22,6,5],u5 [69] [20,12,8,22,6,7,21],([5,23,2,3,4],[25,7,24,3],[0]),([83,51,1,2,3],[4,3,31],[0,1]),([32,87,0,1,3,4],[33,5,4,3],[]),([32,0,1,3,4,9],[34,5,4,3],[]),a5 [20] [12,7,8,22,6,20,35] [0,1],a5 [19,53] [8,12,36] [0,1],a5 [53,16] [12,8,36] [0,1],u5 [83,16] [6,4,37],u5 [83,19] [12,4,6,37],e5 [111] [8,7,12,4,38],a5 [59,16] [5,6,4,39] [0,1],a5 [19,59] [12,22,20,39] [0,1],a5 [19,21] [13,12,40] [0,1],a5 [16,21] [40,13,12] [0,1],a5 [49] [7,8,22,6,5,41] [0,1],a5 [27,78] [8,11,13,42,5] [0,1],([32,27,0,1,3,4],[42,5,3,4],[0,1]),([5,0,1,3,4,7],[3,4,5,43],[0,1]),u5 [5,16] [5,7,43],u5 [5,6] [7,20,6,13,8,43],u5 [5,7] [12,7,3,6,13,43],u5 [19,5] [12,7,13,6,8,20,43],([32,5,0,1,3,4],[43,3,4,5],[0,1]),u5 [19,96] [8,12,28,44],a5 [96,16] [12,23,6,13,44] [1],e5 [114] [6,13,3,45,12],u5 [100] [13,5,22,6,7,46],u5 [19,23] [12,13,47],a5 [23,16] [13,8,12,47] [0,1],a5 [71,78] [13,8,48,5,49] [0,1],e5 [122] [6,13,7,8,50,5],e5 [126] [51,12,6,13,7,8,20],([32,103,0,1,3,4],[52,5,4,3],[1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_6 : checkNodesBT W_12 g_12 F_12 P_12_6 A_12 B_12_5 6 N_12_6 = true := by decide +kernel
def B_12_6 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_6
set_option maxRecDepth 500000 in
lemma B_12_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 6 xs.toFinset) B_12_6 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_5_ok C_12_6
def U_12_7 : List Nat := (r 2 7++[11,12,13,20,22,25,34,36,37,39,40,42,43,44,47,49,53])
def P_12_7 : BT (Option BoundPool) := buildPoolsSubBT 6 W_12 r_12 S_12 ps_12 U_12_7
def N_12_7 : List NodeSpec := [([32,0,1,3,4],[2,3,4],[0,1]),a5 [7] [3,4,2,5] [0,1],a5 [87] [3,4,5] [0,1],([0,1,3,4,7],[3,4,5,2],[0,1]),a5 [43] [3,5,4,2] [0,1],u5 [105] [4,3,2,5],u5 [130] [4,3,5,2],a5 [131] [2,5,8,4] [1],a5 [115] [2,8,5,6,4] [0,1],a5 [103] [8,6,5,4] [0,1],a5 [16] [2,5,13,8,22] [0,1],a5 [19] [12,13,8,2,22,20] [0,1],a5 [9] [3,4,34,5] [0,1],a5 [53] [8,4,12,2,20,36] [0,1],u5 [83] [4,12,20,3,37],a5 [59] [4,3,12,2,20,39] [0,1],a5 [21] [3,40,4,12,20] [0,1],a5 [27] [11,8,5,42,4,6] [0,1],a5 [5] [7,12,43,20,3,6,4] [0,1],a5 [96] [12,20,3,25,6,13,44] [0,1],u5 [23] [13,3,12,20,47],a5 [71] [5,4,49,8,2] [0,1],a5 [123] [13,3,5,53] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_7 : checkNodesBT W_12 g_12 F_12 P_12_7 A_12 B_12_6 7 N_12_7 = true := by decide +kernel
def B_12_7 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_7
set_option maxRecDepth 500000 in
lemma B_12_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 7 xs.toFinset) B_12_7 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_6_ok C_12_7
def U_12_8 : List Nat := [2]
def P_12_8 : BT (Option BoundPool) := buildPoolsSubBT 6 W_12 r_12 S_12 ps_12 U_12_8
def N_12_8 : List NodeSpec := [a5 [] [2] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_8 : checkNodesBT W_12 g_12 F_12 P_12_8 A_12 B_12_7 8 N_12_8 = true := by decide +kernel
def B_12_8 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_8
set_option maxRecDepth 500000 in
lemma B_12_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 8 xs.toFinset) B_12_8 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_7_ok C_12_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_12_ok : forestRootCheck r_12 g_12 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11),(VAR 4,1,17)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_12_in : bucketContainsBT B_12_8 r_12 = true := by decide +kernel
lemma low_12 : Lower r_12 g_12 9 := lower_of_forestBT root_12_ok B_12_8_ok root_12_in
def g_13 := 0xfffefec0fffefec0
def r_13 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_13 : Lower r_13 g_13 8 := by
  have hc : Lower (varsOf 30) 0xfffcfcc0fffcfcc0 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,8,9)]) (by decide +kernel) hc
def g_14 := 0xfec0c000fec0c000
def r_14 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_14 : Lower r_14 g_14 8 := by
  have hc : Lower (varsOf 30) 0xfcc0c000fcc0c000 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_2
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,24,25)]) (by decide +kernel) hc
def g_15 := 0xfffefcc0fffefcc0
def r_15 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_15 : Lower r_15 g_15 8 := by
  have hc : Lower (varsOf 30) 0xfffcfcc0fffcfcc0 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,16,17)]) (by decide +kernel) hc
def g_16 := 0xffe8c000ffe8c000
def r_16 : List Nat := varsOf 31
def p_16 : List Nat := [14,14,14,15,15,15,19,19,19,21,21,21,22,22,22,23,24,24,25,25,26,26,27,28,28,29]
def q_16 : List Nat := [12,10,6,13,11,7,18,17,3,20,17,5,20,18,6,7,16,8,17,9,18,10,11,20,12,13]
def F_16 : Nat := fullMask 26
set_option maxHeartbeats 0 in
lemma gp_16 : goodPairs g_16 p_16 q_16 := goodPairs_of (by decide +kernel)
def W_16 : BT Decor := buildWiresBT 5 (mkBase p_16 q_16 r_16) [(2,2,3),(3,5,1),(0,1,2),(0,1,4),(2,1,3),(0,2,4),(3,10,1),(3,7,4),(0,7,4),(1,7,3),(0,0,4),(2,0,3)]
lemma W_16_ok : btAll (fun x => faithful p_16 q_16 x ∧ x.1 < 2^64) W_16 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_16 : List (List (Nat × Nat)) := [[],[(1,2)]]
def A_16 : BT (List (Nat × Nat)) := btOfList 1 al_16
set_option maxHeartbeats 0 in
lemma A_16_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_16 = g_16) A_16 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_16_0 : Slice r_16 g_16 (subcubeFast 0 1) 6 := by
  have hc : Lower (varsOf 30) 0xfffcc000fffcc000 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_1 : Slice r_16 g_16 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) 0xfffaf000fffaf000 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_2 : Slice r_16 g_16 (subcubeFast 8 16) 4 := by
  exact slice_fast_direct_f (z := 8) (o := 16) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_16_3 : Slice r_16 g_16 (subcubeFast 1 4) 4 := by
  have hc : Lower (varsOf 26) 0xffcccc00ffcccc00 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_4 : Slice r_16 g_16 (identDom 2 3) 5 := by
  have hc : Lower (varsOf 23) 0xf8f8c0c0f8f8c0c0 5 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_8
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
def S_16 : BT (Option (Nat × Nat)) := btOfList 3 [some (subcubeFast 0 1,6),some (subcubeFast 0 2,5),some (subcubeFast 8 16,4),some (subcubeFast 1 4,4),some (identDom 2 3,5)]
lemma S_16_ok : btAll (fun o => ∀ p, o = some p → Slice r_16 g_16 p.1 p.2) S_16 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_16_0) (forall_cons (fun _ h => by cases h; exact sl_16_1) (forall_cons (fun _ h => by cases h; exact sl_16_2) (forall_cons (fun _ h => by cases h; exact sl_16_3) (forall_cons (fun _ h => by cases h; exact sl_16_4) (fun _ h => (List.not_mem_nil h).elim))))))
def ps_16 : BT (Option PoolSpec) := btOfList 3 [q 2 [],q 3 [],q 0 [],q 4 [],q 1 [],q 0 [8196]]
def B_16_4 : BT (List (List Nat)) := BT.empty
lemma B_16_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_16 4 xs.toFinset) B_16_4 := .empty
def U_16_5 : List Nat := (r 0 4)
def P_16_5 : BT (Option BoundPool) := buildPoolsSubBT 3 W_16 r_16 S_16 ps_16 U_16_5
def N_16_5 : List NodeSpec := [([0,7,8,2,3,4],[0,1],[]),([9,0,7,2,3,4],[0,1],[]),e5 [12] [1,2],e5 [14] [2,1],e5 [13] [2,1,3,0],e5 [6] [],e5 [11] []]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_16_5 : checkNodesBT W_16 g_16 F_16 P_16_5 A_16 B_16_4 5 N_16_5 = true := by decide +kernel
def B_16_5 : BT (List (List Nat)) := buildBucketsBT W_16 N_16_5
set_option maxRecDepth 500000 in
lemma B_16_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_16 5 xs.toFinset) B_16_5 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok (buildPoolsSubBT_sound S_16_ok) A_16_ok B_16_4_ok C_16_5
def U_16_6 : List Nat := (r 0 6)
def P_16_6 : BT (Option BoundPool) := buildPoolsSubBT 3 W_16 r_16 S_16 ps_16 U_16_6
def N_16_6 : List NodeSpec := [([16,1,2,3,4],[0,1],[]),([15,1,2,3,4],[1,0],[]),a5 [9] [1,2,0,3,4] [0,1],a5 [8] [1,2,0,4] [0,1],a5 [7] [1,5,4,0,3] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_16_6 : checkNodesBT W_16 g_16 F_16 P_16_6 A_16 B_16_5 6 N_16_6 = true := by decide +kernel
def B_16_6 : BT (List (List Nat)) := buildBucketsBT W_16 N_16_6
set_option maxRecDepth 500000 in
lemma B_16_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_16 6 xs.toFinset) B_16_6 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok (buildPoolsSubBT_sound S_16_ok) A_16_ok B_16_5_ok C_16_6
def U_16_7 : List Nat := [0,1,2,4]
def P_16_7 : BT (Option BoundPool) := buildPoolsSubBT 3 W_16 r_16 S_16 ps_16 U_16_7
def N_16_7 : List NodeSpec := [a5 [] [2,4,1,0] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_16_7 : checkNodesBT W_16 g_16 F_16 P_16_7 A_16 B_16_6 7 N_16_7 = true := by decide +kernel
def B_16_7 : BT (List (List Nat)) := buildBucketsBT W_16 N_16_7
set_option maxRecDepth 500000 in
lemma B_16_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_16 7 xs.toFinset) B_16_7 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok (buildPoolsSubBT_sound S_16_ok) A_16_ok B_16_6_ok C_16_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_16_ok : forestRootCheck r_16 g_16 [(VAR 0,18,19),(VAR 1,12,14),(VAR 2,10,14),(VAR 3,6,14),(VAR 4,3,19)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_16_in : bucketContainsBT B_16_7 r_16 = true := by decide +kernel
lemma low_16 : Lower r_16 g_16 8 := lower_of_forestBT root_16_ok B_16_7_ok root_16_in
def g_17 := 0xe800e800e800e800
def r_17 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_17 : Lower r_17 g_17 5 := by
  exact lift_of_f (z := 0) (o := 8) (other := r_0) (G := g_0) (essPairs := [(VAR 3,3,11)]) (by decide +kernel) low_0
def g_18 := 0xfef0c800fef0c800
def r_18 : List Nat := varsOf 31
def p_18 : List Nat := [11,11,11,14,14,14,15,15,20,20,21,21,22,22,23,23,25,25,25,26,26,26,27,28,28,29]
def q_18 : List Nat := [10,9,3,12,10,6,13,7,16,4,17,5,18,6,19,7,24,17,9,24,18,10,19,24,12,13]
def F_18 : Nat := fullMask 26
set_option maxHeartbeats 0 in
lemma gp_18 : goodPairs g_18 p_18 q_18 := goodPairs_of (by decide +kernel)
def W_18 : BT Decor := buildWiresBT 3 (mkBase p_18 q_18 r_18) []
lemma W_18_ok : btAll (fun x => faithful p_18 q_18 x ∧ x.1 < 2^64) W_18 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_18 : List (List (Nat × Nat)) := [[]]
def A_18 : BT (List (Nat × Nat)) := btOfList 1 al_18
set_option maxHeartbeats 0 in
lemma A_18_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_18 = g_18) A_18 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_18_0 : Slice r_18 g_18 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) 0xfcf0c000fcf0c000 5 := carry_of (swaps := [(0,4),(1,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_1 : Slice r_18 g_18 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) 0xfff0fa00fff0fa00 5 := carry_of (swaps := [(1,4),(2,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_2 : Slice r_18 g_18 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) 0xee008800ee008800 5 := carry_of (swaps := [(2,4)]) (by decide +kernel) low_17
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_3 : Slice r_18 g_18 (subcubeFast 0 8) 5 := by
  have hc : Lower (varsOf 23) 0xfefec8c8fefec8c8 5 := carry_of (swaps := [(1,2),(3,4)]) (by decide +kernel) low_11
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
def S_18 : BT (Option (Nat × Nat)) := btOfList 2 [some (subcubeFast 1 0,5),some (subcubeFast 0 2,5),some (subcubeFast 4 0,5),some (subcubeFast 0 8,5)]
lemma S_18_ok : btAll (fun o => ∀ p, o = some p → Slice r_18 g_18 p.1 p.2) S_18 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_18_0) (forall_cons (fun _ h => by cases h; exact sl_18_1) (forall_cons (fun _ h => by cases h; exact sl_18_2) (forall_cons (fun _ h => by cases h; exact sl_18_3) (fun _ h => (List.not_mem_nil h).elim)))))
def ps_18 : BT (Option PoolSpec) := btOfList 2 [q 0 [],q 2 [],q 3 [],q 1 []]
def B_18_5 : BT (List (List Nat)) := BT.empty
lemma B_18_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_18 5 xs.toFinset) B_18_5 := .empty
def U_18_6 : List Nat := (r 0 4)
def P_18_6 : BT (Option BoundPool) := buildPoolsSubBT 2 W_18 r_18 S_18 ps_18 U_18_6
def N_18_6 : List NodeSpec := [e5 [] (r 0 4)]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_18_6 : checkNodesBT W_18 g_18 F_18 P_18_6 A_18 B_18_5 6 N_18_6 = true := by decide +kernel
def B_18_6 : BT (List (List Nat)) := buildBucketsBT W_18 N_18_6
set_option maxRecDepth 500000 in
lemma B_18_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_18 6 xs.toFinset) B_18_6 :=
  buildBucketsBT_sound (by decide) gp_18 W_18_ok (buildPoolsSubBT_sound S_18_ok) A_18_ok B_18_5_ok C_18_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_18_ok : forestRootCheck r_18 g_18 [(VAR 0,10,11),(VAR 1,9,11),(VAR 2,10,14),(VAR 3,3,11),(VAR 4,4,20)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_18_in : bucketContainsBT B_18_6 r_18 = true := by decide +kernel
lemma low_18 : Lower r_18 g_18 7 := lower_of_forestBT root_18_ok B_18_6_ok root_18_in
def g_19 := 0xffe0c000ffe0c000
def r_19 : List Nat := varsOf 31
def p_19 : List Nat := [14,14,14,15,15,15,21,21,21,22,22,22,23,23,24,24,25,25,26,26,27,27,28,28,29]
def q_19 : List Nat := [12,10,6,13,11,7,20,17,5,20,18,6,19,7,16,8,17,9,18,10,19,11,20,12,13]
def F_19 : Nat := fullMask 25
set_option maxHeartbeats 0 in
lemma gp_19 : goodPairs g_19 p_19 q_19 := goodPairs_of (by decide +kernel)
def W_19 : BT Decor := buildWiresBT 4 (mkBase p_19 q_19 r_19) [(0,3,4),(1,3,4),(3,5,6),(0,2,6),(2,3,4),(3,3,4),(2,2,5),(2,1,5)]
lemma W_19_ok : btAll (fun x => faithful p_19 q_19 x ∧ x.1 < 2^64) W_19 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_19 : List (List (Nat × Nat)) := [[]]
def A_19 : BT (List (Nat × Nat)) := btOfList 1 al_19
set_option maxHeartbeats 0 in
lemma A_19_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_19 = g_19) A_19 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_19_0 : Slice r_19 g_19 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) 0xffc0c000ffc0c000 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_19_1 : Slice r_19 g_19 (subcubeFast 0 4) 5 := by
  have hc : Lower (varsOf 27) 0xffeecc00ffeecc00 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_19_2 : Slice r_19 g_19 (subcubeFast 0 3) 4 := by
  have hc : Lower (varsOf 28) 0xfff0f000fff0f000 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 0) (o := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_19_3 : Slice r_19 g_19 (identDom 1 3) 5 := by
  have hc : Lower (varsOf 23) 0xececc0c0ececc0c0 5 := carry_of (swaps := [(1,3),(2,3),(3,4)]) (by decide +kernel) low_8
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
def S_19 : BT (Option (Nat × Nat)) := btOfList 2 [some (subcubeFast 1 0,5),some (subcubeFast 0 4,5),some (subcubeFast 0 3,4),some (identDom 1 3,5)]
lemma S_19_ok : btAll (fun o => ∀ p, o = some p → Slice r_19 g_19 p.1 p.2) S_19 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_19_0) (forall_cons (fun _ h => by cases h; exact sl_19_1) (forall_cons (fun _ h => by cases h; exact sl_19_2) (forall_cons (fun _ h => by cases h; exact sl_19_3) (fun _ h => (List.not_mem_nil h).elim)))))
def ps_19 : BT (Option PoolSpec) := btOfList 2 [q 0 [],q 2 [],q 3 [],q 1 []]
def B_19_2 : BT (List (List Nat)) := BT.empty
lemma B_19_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_19 2 xs.toFinset) B_19_2 := .empty
def U_19_3 : List Nat := []
def P_19_3 : BT (Option BoundPool) := buildPoolsSubBT 2 W_19 r_19 S_19 ps_19 U_19_3
def N_19_3 : List NodeSpec := [([7,0,1,2],[],[]),([0,1,8,5],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_19_3 : checkNodesBT W_19 g_19 F_19 P_19_3 A_19 B_19_2 3 N_19_3 = true := by decide +kernel
def B_19_3 : BT (List (List Nat)) := buildBucketsBT W_19 N_19_3
set_option maxRecDepth 500000 in
lemma B_19_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_19 3 xs.toFinset) B_19_3 :=
  buildBucketsBT_sound (by decide) gp_19 W_19_ok (buildPoolsSubBT_sound S_19_ok) A_19_ok B_19_2_ok C_19_3
def U_19_4 : List Nat := []
def P_19_4 : BT (Option BoundPool) := buildPoolsSubBT 2 W_19 r_19 S_19 ps_19 U_19_4
def N_19_4 : List NodeSpec := [([9,10,0,1,2],[],[0]),([0,1,8,3,4],[],[0]),([0,1,2,5,6],[],[0]),([11,0,1,3,4],[],[]),([12,0,2,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_19_4 : checkNodesBT W_19 g_19 F_19 P_19_4 A_19 B_19_3 4 N_19_4 = true := by decide +kernel
def B_19_4 : BT (List (List Nat)) := buildBucketsBT W_19 N_19_4
set_option maxRecDepth 500000 in
lemma B_19_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_19 4 xs.toFinset) B_19_4 :=
  buildBucketsBT_sound (by decide) gp_19 W_19_ok (buildPoolsSubBT_sound S_19_ok) A_19_ok B_19_3_ok C_19_4
def U_19_5 : List Nat := (r 0 4)
def P_19_5 : BT (Option BoundPool) := buildPoolsSubBT 2 W_19 r_19 S_19 ps_19 U_19_5
def N_19_5 : List NodeSpec := [u5 [10] [0,1],u5 [9] [1,0],u5 [6] (r 0 4),u5 [5] [0,1,3]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_19_5 : checkNodesBT W_19 g_19 F_19 P_19_5 A_19 B_19_4 5 N_19_5 = true := by decide +kernel
def B_19_5 : BT (List (List Nat)) := buildBucketsBT W_19 N_19_5
set_option maxRecDepth 500000 in
lemma B_19_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_19 5 xs.toFinset) B_19_5 :=
  buildBucketsBT_sound (by decide) gp_19 W_19_ok (buildPoolsSubBT_sound S_19_ok) A_19_ok B_19_4_ok C_19_5
def U_19_6 : List Nat := [0,1,3]
def P_19_6 : BT (Option BoundPool) := buildPoolsSubBT 2 W_19 r_19 S_19 ps_19 U_19_6
def N_19_6 : List NodeSpec := [u5 [] [0,3,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_19_6 : checkNodesBT W_19 g_19 F_19 P_19_6 A_19 B_19_5 6 N_19_6 = true := by decide +kernel
def B_19_6 : BT (List (List Nat)) := buildBucketsBT W_19 N_19_6
set_option maxRecDepth 500000 in
lemma B_19_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_19 6 xs.toFinset) B_19_6 :=
  buildBucketsBT_sound (by decide) gp_19 W_19_ok (buildPoolsSubBT_sound S_19_ok) A_19_ok B_19_5_ok C_19_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_19_ok : forestRootCheck r_19 g_19 [(VAR 0,20,21),(VAR 1,12,14),(VAR 2,10,14),(VAR 3,6,14),(VAR 4,5,21)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_19_in : bucketContainsBT B_19_6 r_19 = true := by decide +kernel
lemma low_19 : Lower r_19 g_19 7 := lower_of_forestBT root_19_ok B_19_6_ok root_19_in
def g_20 := 0xfffce800fffce800
def r_20 : List Nat := varsOf 31
def p_20 : List Nat := [11,11,11,13,13,13,14,14,14,15,18,18,19,19,20,20,21,21,22,23,24,24,25,25,26,28]
def q_20 : List Nat := [10,9,3,12,9,5,12,10,6,7,16,2,17,3,16,4,17,5,6,7,16,8,17,9,10,12]
def F_20 : Nat := fullMask 26
set_option maxHeartbeats 0 in
lemma gp_20 : goodPairs g_20 p_20 q_20 := goodPairs_of (by decide +kernel)
def W_20 : BT Decor := buildWiresBT 4 (mkBase p_20 q_20 r_20) [(1,1,4),(3,2,5),(1,1,2),(2,7,4),(1,7,4),(0,7,3),(3,2,3),(1,11,1),(1,2,4),(1,0,4),(3,0,3)]
lemma W_20_ok : btAll (fun x => faithful p_20 q_20 x ∧ x.1 < 2^64) W_20 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_20 : List (List (Nat × Nat)) := [[],[(1,2)]]
def A_20 : BT (List (Nat × Nat)) := btOfList 1 al_20
set_option maxHeartbeats 0 in
lemma A_20_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_20 = g_20) A_20 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_20_0 : Slice r_20 g_20 (subcubeFast 1 0) 6 := by
  have hc : Lower (varsOf 30) 0xfffcc000fffcc000 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_20_1 : Slice r_20 g_20 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) 0xfff0a000fff0a000 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_20_2 : Slice r_20 g_20 (subcubeFast 16 8) 4 := by
  exact slice_fast_direct_f (z := 16) (o := 8) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_20_3 : Slice r_20 g_20 (subcubeFast 4 1) 4 := by
  have hc : Lower (varsOf 26) 0xffcccc00ffcccc00 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_20_4 : Slice r_20 g_20 (identDom 2 3) 5 := by
  have hc : Lower (varsOf 23) 0xfcfce0e0fcfce0e0 5 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_6
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
def S_20 : BT (Option (Nat × Nat)) := btOfList 3 [some (subcubeFast 1 0,6),some (subcubeFast 2 0,5),some (subcubeFast 16 8,4),some (subcubeFast 4 1,4),some (identDom 2 3,5)]
lemma S_20_ok : btAll (fun o => ∀ p, o = some p → Slice r_20 g_20 p.1 p.2) S_20 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_20_0) (forall_cons (fun _ h => by cases h; exact sl_20_1) (forall_cons (fun _ h => by cases h; exact sl_20_2) (forall_cons (fun _ h => by cases h; exact sl_20_3) (forall_cons (fun _ h => by cases h; exact sl_20_4) (fun _ h => (List.not_mem_nil h).elim))))))
def ps_20 : BT (Option PoolSpec) := btOfList 3 [q 0 [],q 3 [],q 4 [],q 2 [],q 1 [],q 0 [8197]]
def B_20_4 : BT (List (List Nat)) := BT.empty
lemma B_20_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_20 4 xs.toFinset) B_20_4 := .empty
def U_20_5 : List Nat := (r 0 5)
def P_20_5 : BT (Option BoundPool) := buildPoolsSubBT 3 W_20 r_20 S_20 ps_20 U_20_5
def N_20_5 : List NodeSpec := [e5 [8] [0,1],e5 [10] [0,1],e5 [9] (r 0 4),([0,1,7,3,4,13],[4,3],[]),([11,0,1,7,3,4],[4,3],[]),e5 [6] [],e5 [12] []]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_20_5 : checkNodesBT W_20 g_20 F_20 P_20_5 A_20 B_20_4 5 N_20_5 = true := by decide +kernel
def B_20_5 : BT (List (List Nat)) := buildBucketsBT W_20 N_20_5
set_option maxRecDepth 500000 in
lemma B_20_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_20 5 xs.toFinset) B_20_5 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok (buildPoolsSubBT_sound S_20_ok) A_20_ok B_20_4_ok C_20_5
def U_20_6 : List Nat := (r 0 6)
def P_20_6 : BT (Option BoundPool) := buildPoolsSubBT 3 W_20 r_20 S_20 ps_20 U_20_6
def N_20_6 : List NodeSpec := [([1,2,3,4,14],[1,3],[]),([15,1,2,3,4],[3,1],[]),u5 [11] [1,4,2,3],a5 [5] [3,0,1,4] [0,1],a5 [7] [1,5,4,3,2] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_20_6 : checkNodesBT W_20 g_20 F_20 P_20_6 A_20 B_20_5 6 N_20_6 = true := by decide +kernel
def B_20_6 : BT (List (List Nat)) := buildBucketsBT W_20 N_20_6
set_option maxRecDepth 500000 in
lemma B_20_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_20 6 xs.toFinset) B_20_6 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok (buildPoolsSubBT_sound S_20_ok) A_20_ok B_20_5_ok C_20_6
def U_20_7 : List Nat := [0,1,3,4]
def P_20_7 : BT (Option BoundPool) := buildPoolsSubBT 3 W_20 r_20 S_20 ps_20 U_20_7
def N_20_7 : List NodeSpec := [a5 [] [0,1,4,3] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_20_7 : checkNodesBT W_20 g_20 F_20 P_20_7 A_20 B_20_6 7 N_20_7 = true := by decide +kernel
def B_20_7 : BT (List (List Nat)) := buildBucketsBT W_20 N_20_7
set_option maxRecDepth 500000 in
lemma B_20_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_20 7 xs.toFinset) B_20_7 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok (buildPoolsSubBT_sound S_20_ok) A_20_ok B_20_6_ok C_20_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_20_ok : forestRootCheck r_20 g_20 [(VAR 0,10,11),(VAR 1,9,11),(VAR 2,9,13),(VAR 3,3,11),(VAR 4,2,18)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_20_in : bucketContainsBT B_20_7 r_20 = true := by decide +kernel
lemma low_20 : Lower r_20 g_20 8 := lower_of_forestBT root_20_ok B_20_7_ok root_20_in
def g_21 := 0x2222222222222222
def r_21 : List Nat := varsOf 3
set_option maxHeartbeats 0 in
lemma low_21 : Lower r_21 g_21 1 := count_of (essPairs := [(VAR 0,0,1),(VAR 1,1,3)]) (by decide +kernel)
def g_22 := 0x8e8e8e8e8e8e8e8e
def r_22 : List Nat := varsOf 7
def p_22 : List Nat := [1,2,7,7]
def q_22 : List Nat := [0,0,6,5]
def F_22 : Nat := fullMask 4
set_option maxHeartbeats 0 in
lemma gp_22 : goodPairs g_22 p_22 q_22 := goodPairs_of (by decide +kernel)
def W_22 : BT Decor := buildWiresBT 2 (mkBase p_22 q_22 r_22) []
lemma W_22_ok : btAll (fun x => faithful p_22 q_22 x ∧ x.1 < 2^64) W_22 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_22 : List (List (Nat × Nat)) := [[]]
def A_22 : BT (List (Nat × Nat)) := btOfList 1 al_22
set_option maxHeartbeats 0 in
lemma A_22_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_22 = g_22) A_22 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_22_0 : Slice r_22 g_22 (subcubeFast 1 0) 1 := by
  have hc : Lower (varsOf 6) 0xc0c0c0c0c0c0c0c 1 := carry_of (swaps := [(0,2),(1,2)]) (by decide +kernel) low_21
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_1 : Slice r_22 g_22 (subcubeFast 0 1) 1 := by
  have hc : Lower (varsOf 6) 0x3030303030303030 1 := carry_of (swaps := [(0,2)]) (by decide +kernel) low_21
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_2 : Slice r_22 g_22 (subcubeFast 2 0) 1 := by
  have hc : Lower (varsOf 5) 0xa0a0a0a0a0a0a0a 1 := carry_of (swaps := [(1,2)]) (by decide +kernel) low_21
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_3 : Slice r_22 g_22 (subcubeFast 0 2) 1 := by
  have hc : Lower (varsOf 5) 0x5050505050505050 1 := carry_of (swaps := [(0,1),(1,2)]) (by decide +kernel) low_21
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
def S_22 : BT (Option (Nat × Nat)) := btOfList 2 [some (subcubeFast 1 0,1),some (subcubeFast 0 1,1),some (subcubeFast 2 0,1),some (subcubeFast 0 2,1)]
lemma S_22_ok : btAll (fun o => ∀ p, o = some p → Slice r_22 g_22 p.1 p.2) S_22 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_22_0) (forall_cons (fun _ h => by cases h; exact sl_22_1) (forall_cons (fun _ h => by cases h; exact sl_22_2) (forall_cons (fun _ h => by cases h; exact sl_22_3) (fun _ h => (List.not_mem_nil h).elim)))))
def ps_22 : BT (Option PoolSpec) := btOfList 2 [q 0 [],q 1 [],q 2 [],q 3 []]
def B_22_2 : BT (List (List Nat)) := BT.empty
lemma B_22_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 2 xs.toFinset) B_22_2 := .empty
def U_22_3 : List Nat := (r 0 4)
def P_22_3 : BT (Option BoundPool) := buildPoolsSubBT 2 W_22 r_22 S_22 ps_22 U_22_3
def N_22_3 : List NodeSpec := [([0,1,2],(r 0 4),[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_3 : checkNodesBT W_22 g_22 F_22 P_22_3 A_22 B_22_2 3 N_22_3 = true := by decide +kernel
def B_22_3 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_3
set_option maxRecDepth 500000 in
lemma B_22_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 3 xs.toFinset) B_22_3 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound S_22_ok) A_22_ok B_22_2_ok C_22_3
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_22_ok : forestRootCheck r_22 g_22 [(VAR 0,0,1),(VAR 1,0,2),(VAR 2,1,5)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_22_in : bucketContainsBT B_22_3 r_22 = true := by decide +kernel
lemma low_22 : Lower r_22 g_22 4 := lower_of_forestBT root_22_ok B_22_3_ok root_22_in
def g_23 := 0x202020202020202
def r_23 : List Nat := varsOf 7
set_option maxHeartbeats 0 in
lemma low_23 : Lower r_23 g_23 2 := count_of (essPairs := [(VAR 0,0,1),(VAR 1,1,3),(VAR 2,1,5)]) (by decide +kernel)
def g_24 := 0xe8fee8fee8fee8fe
def r_24 : List Nat := varsOf 15
def p_24 : List Nat := [1,2,4,11,11,13,13,14,14]
def q_24 : List Nat := [0,0,0,10,9,12,9,12,10]
def F_24 : Nat := fullMask 9
set_option maxHeartbeats 0 in
lemma gp_24 : goodPairs g_24 p_24 q_24 := goodPairs_of (by decide +kernel)
def W_24 : BT Decor := buildWiresBT 5 (mkBase p_24 q_24 r_24) [(3,0,3),(1,2,1),(3,4,5),(1,0,2),(1,0,1),(0,8,3),(2,5,0),(3,10,3),(3,2,3),(3,8,3),(1,13,2),(1,2,3),(0,8,15),(0,7,3),(2,8,3),(1,18,2),(1,12,0),(3,2,8),(3,1,3),(1,8,2),(0,23,3),(1,0,3),(3,2,25),(3,5,3)]
lemma W_24_ok : btAll (fun x => faithful p_24 q_24 x ∧ x.1 < 2^64) W_24 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_24 : List (List (Nat × Nat)) := [[],[(1,2)],[(0,1)],[(0,2),(1,2)],[(0,1),(1,2)]]
def A_24 : BT (List (Nat × Nat)) := btOfList 3 al_24
set_option maxHeartbeats 0 in
lemma A_24_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_24 = g_24) A_24 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_24_0 : Slice r_24 g_24 (subcubeFast 1 0) 4 := by
  have hc : Lower (varsOf 14) 0xc0fcc0fcc0fcc0fc 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_22
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_1 : Slice r_24 g_24 (subcubeFast 2 0) 4 := by
  have hc : Lower (varsOf 13) 0xa0faa0faa0faa0fa 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_22
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_2 : Slice r_24 g_24 (subcubeFast 4 0) 4 := by
  have hc : Lower (varsOf 11) 0x88ee88ee88ee88ee 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_22
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_3 : Slice r_24 g_24 (subcubeFast 0 8) 4 := by
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_24_4 : Slice r_24 g_24 (subcubeFast 0 1) 2 := by
  have hc : Lower (varsOf 14) 0x300030003000300 2 := carry_of (swaps := [(0,3)]) (by decide +kernel) low_23
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_5 : Slice r_24 g_24 (subcubeFast 0 2) 2 := by
  have hc : Lower (varsOf 13) 0x500050005000500 2 := carry_of (swaps := [(0,1),(1,3)]) (by decide +kernel) low_23
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_6 : Slice r_24 g_24 (subcubeFast 0 4) 2 := by
  have hc : Lower (varsOf 11) 0x1100110011001100 2 := carry_of (swaps := [(0,1),(1,2),(2,3)]) (by decide +kernel) low_23
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
def S_24 : BT (Option (Nat × Nat)) := btOfList 3 [some (subcubeFast 1 0,4),some (subcubeFast 2 0,4),some (subcubeFast 4 0,4),some (subcubeFast 0 8,4),some (subcubeFast 0 1,2),some (subcubeFast 0 2,2),some (subcubeFast 0 4,2)]
lemma S_24_ok : btAll (fun o => ∀ p, o = some p → Slice r_24 g_24 p.1 p.2) S_24 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_24_0) (forall_cons (fun _ h => by cases h; exact sl_24_1) (forall_cons (fun _ h => by cases h; exact sl_24_2) (forall_cons (fun _ h => by cases h; exact sl_24_3) (forall_cons (fun _ h => by cases h; exact sl_24_4) (forall_cons (fun _ h => by cases h; exact sl_24_5) (forall_cons (fun _ h => by cases h; exact sl_24_6) (fun _ h => (List.not_mem_nil h).elim))))))))
def ps_24 : BT (Option PoolSpec) := btOfList 5 [q 4 [4105],q 4 [],q 4 [8197],q 1 [],q 0 [12322,8265],q 0 [],q 5 [9],q 3 [],q 2 [],q 1 [12291,20499],q 5 [],q 6 [],q 0 [12299],q 2 [12289],q 0 [4105],q 1 [9],q 0 [8226],q 1 [8226],q 2 [4097],q 2 [49],q 0 [8225],q 1 [8225],q 1 [12311],q 2 [12311],q 0 [12320],q 1 [12320],q 0 [12322],q 0 [12297],q 1 [12299],q 1 [12289]]
def B_24_1 : BT (List (List Nat)) := BT.empty
lemma B_24_1_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_24 1 xs.toFinset) B_24_1 := .empty
def U_24_2 : List Nat := [0]
def P_24_2 : BT (Option BoundPool) := buildPoolsSubBT 5 W_24 r_24 S_24 ps_24 U_24_2
def N_24_2 : List NodeSpec := [([6,1,7],[0],[]),([9,7,5],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_24_2 : checkNodesBT W_24 g_24 F_24 P_24_2 A_24 B_24_1 2 N_24_2 = true := by decide +kernel
def B_24_2 : BT (List (List Nat)) := buildBucketsBT W_24 N_24_2
set_option maxRecDepth 500000 in
lemma B_24_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_24 2 xs.toFinset) B_24_2 :=
  buildBucketsBT_sound (by decide) gp_24 W_24_ok (buildPoolsSubBT_sound S_24_ok) A_24_ok B_24_1_ok C_24_2
def U_24_3 : List Nat := (r 0 10)
def P_24_3 : BT (Option BoundPool) := buildPoolsSubBT 5 W_24 r_24 S_24 ps_24 U_24_3
def N_24_3 : List NodeSpec := [([0,20,1,5],[0],[]),([0,11,1,2],[1],[]),([12,0,8,5],[2],[4]),([0,1,17,5],[3],[1]),([0,1,8,19],[4],[]),([8,7,5,3],[3,5,0,6],[0,1,3]),([12,22,0,5],[3,8],[]),([6,0,1,2],[7,8,9],[0,1]),([0,1,14,3],[],[]),([0,1,16,2],[],[]),([21,22,0,2],[],[]),([0,1,14],[],[]),([0,1,2,24],[],[]),([0,1,9,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_24_3 : checkNodesBT W_24 g_24 F_24 P_24_3 A_24 B_24_2 3 N_24_3 = true := by decide +kernel
def B_24_3 : BT (List (List Nat)) := buildBucketsBT W_24 N_24_3
set_option maxRecDepth 500000 in
lemma B_24_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_24 3 xs.toFinset) B_24_3 :=
  buildBucketsBT_sound (by decide) gp_24 W_24_ok (buildPoolsSubBT_sound S_24_ok) A_24_ok B_24_2_ok C_24_3
def U_24_4 : List Nat := ([1,3,5,7,8]++r 10 18)
def P_24_4 : BT (Option BoundPool) := buildPoolsSubBT 5 W_24 r_24 S_24 ps_24 U_24_4
def N_24_4 : List NodeSpec := [([0,1,9,2,3],[1],[]),([27,0,1,2,3],[5],[3]),([12,22,0,1,2],[10,3,11,8],[0]),([12,0,20,1,2],[11,5,8],[]),([12,0,1,8,2],[1,3,10,11,12,8],[0,2,4]),([12,0,1,7,3],[8,12,7],[2]),([12,0,1,7],[11,12],[1,2]),([0,20,1,2,3],[12,1],[]),([26,0,1,2],[3,10,11,13],[]),([0,1,7,5,3],[14,15,11],[0,1,2,3]),([21,0,1,2,3],[11,7,16,17,18],[0,2,4]),([0,20,1,2],[1,12,3,10,19],[0]),([0,1,2,23,3],[20,1,21,10,18,11,7],[0]),([27,0,1,2],[5,10,1,11,22,23],[3]),([0,1,9,8,2],[24,3,7],[]),([0,1,9,2],[24,25,8,11],[1,3]),([18,0,1,8,2],[3,18,26],[0]),([0,1,8,2,15],[27,1,3,10,8,11],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_24_4 : checkNodesBT W_24 g_24 F_24 P_24_4 A_24 B_24_3 4 N_24_4 = true := by decide +kernel
def B_24_4 : BT (List (List Nat)) := buildBucketsBT W_24 N_24_4
set_option maxRecDepth 500000 in
lemma B_24_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_24 4 xs.toFinset) B_24_4 :=
  buildBucketsBT_sound (by decide) gp_24 W_24_ok (buildPoolsSubBT_sound S_24_ok) A_24_ok B_24_3_ok C_24_4
def U_24_5 : List Nat := [1,3,5,7,8,11,12,13,18,28,29]
def P_24_5 : BT (Option BoundPool) := buildPoolsSubBT 5 W_24 r_24 S_24 ps_24 U_24_5
def N_24_5 : List NodeSpec := [([0,1,8,2,3],[5,3,7,1,18],[0,1,3,4]),([12,0,1,2,3],[7,8,12,28],[0,2]),([12,0,1,2],[11,12,28,7,8],[0,2]),([0,1,2,25],[5,7,29,13],[0,1,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_24_5 : checkNodesBT W_24 g_24 F_24 P_24_5 A_24 B_24_4 5 N_24_5 = true := by decide +kernel
def B_24_5 : BT (List (List Nat)) := buildBucketsBT W_24 N_24_5
set_option maxRecDepth 500000 in
lemma B_24_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_24 5 xs.toFinset) B_24_5 :=
  buildBucketsBT_sound (by decide) gp_24 W_24_ok (buildPoolsSubBT_sound S_24_ok) A_24_ok B_24_4_ok C_24_5
def U_24_6 : List Nat := [3,5,7,8]
def P_24_6 : BT (Option BoundPool) := buildPoolsSubBT 5 W_24 r_24 S_24 ps_24 U_24_6
def N_24_6 : List NodeSpec := [([0,1,2,3],[5,3,8,7],[0,1,2,3,4])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_24_6 : checkNodesBT W_24 g_24 F_24 P_24_6 A_24 B_24_5 6 N_24_6 = true := by decide +kernel
def B_24_6 : BT (List (List Nat)) := buildBucketsBT W_24 N_24_6
set_option maxRecDepth 500000 in
lemma B_24_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_24 6 xs.toFinset) B_24_6 :=
  buildBucketsBT_sound (by decide) gp_24 W_24_ok (buildPoolsSubBT_sound S_24_ok) A_24_ok B_24_5_ok C_24_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_24_ok : forestRootCheck r_24 g_24 [(VAR 0,0,1),(VAR 1,0,2),(VAR 2,0,4),(VAR 3,1,9)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_24_in : bucketContainsBT B_24_6 r_24 = true := by decide +kernel
lemma low_24 : Lower r_24 g_24 7 := lower_of_forestBT root_24_ok B_24_6_ok root_24_in
def g_25 := 0x808080808080808
def r_25 : List Nat := varsOf 7
set_option maxHeartbeats 0 in
lemma low_25 : Lower r_25 g_25 2 := count_of (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,3,7)]) (by decide +kernel)
def g_26 := 0x80e880e880e880e8
def r_26 : List Nat := varsOf 15
def p_26 : List Nat := [3,3,5,5,6,6,15,15,15]
def q_26 : List Nat := [2,1,4,1,4,2,14,13,11]
def F_26 : Nat := fullMask 9
set_option maxHeartbeats 0 in
lemma gp_26 : goodPairs g_26 p_26 q_26 := goodPairs_of (by decide +kernel)
def W_26 : BT Decor := buildWiresBT 5 (mkBase p_26 q_26 r_26) [(0,0,1),(2,1,3),(0,0,2),(1,5,6),(0,1,2),(1,8,3),(2,2,3),(1,10,4),(2,0,3),(3,6,1),(3,8,0),(1,14,3),(2,8,3),(3,16,0),(0,0,3),(1,8,18),(0,4,2),(1,20,3),(1,4,3),(3,8,3),(3,23,0),(3,5,2),(3,10,0),(0,2,3),(3,27,0),(3,12,1),(2,4,3)]
lemma W_26_ok : btAll (fun x => faithful p_26 q_26 x ∧ x.1 < 2^64) W_26 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_26 : List (List (Nat × Nat)) := [[],[(1,2)],[(0,1)],[(0,2),(1,2)],[(0,1),(1,2)],[(0,2)]]
def A_26 : BT (List (Nat × Nat)) := btOfList 3 al_26
set_option maxHeartbeats 0 in
lemma A_26_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_26 = g_26) A_26 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_26_0 : Slice r_26 g_26 (subcubeFast 0 1) 4 := by
  have hc : Lower (varsOf 14) 0xc0fcc0fcc0fcc0fc 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_22
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_26_1 : Slice r_26 g_26 (subcubeFast 0 2) 4 := by
  have hc : Lower (varsOf 13) 0xa0faa0faa0faa0fa 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_22
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_26_2 : Slice r_26 g_26 (subcubeFast 0 4) 4 := by
  have hc : Lower (varsOf 11) 0x88ee88ee88ee88ee 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_22
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_26_3 : Slice r_26 g_26 (subcubeFast 8 0) 4 := by
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_26_4 : Slice r_26 g_26 (subcubeFast 1 0) 2 := by
  have hc : Lower (varsOf 14) 0xc000c000c000c0 2 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_25
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_26_5 : Slice r_26 g_26 (subcubeFast 2 0) 2 := by
  have hc : Lower (varsOf 13) 0xa000a000a000a0 2 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_25
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_26_6 : Slice r_26 g_26 (subcubeFast 4 0) 2 := by
  have hc : Lower (varsOf 11) 0x88008800880088 2 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_25
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
def S_26 : BT (Option (Nat × Nat)) := btOfList 3 [some (subcubeFast 0 1,4),some (subcubeFast 0 2,4),some (subcubeFast 0 4,4),some (subcubeFast 8 0,4),some (subcubeFast 1 0,2),some (subcubeFast 2 0,2),some (subcubeFast 4 0,2)]
lemma S_26_ok : btAll (fun o => ∀ p, o = some p → Slice r_26 g_26 p.1 p.2) S_26 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_26_0) (forall_cons (fun _ h => by cases h; exact sl_26_1) (forall_cons (fun _ h => by cases h; exact sl_26_2) (forall_cons (fun _ h => by cases h; exact sl_26_3) (forall_cons (fun _ h => by cases h; exact sl_26_4) (forall_cons (fun _ h => by cases h; exact sl_26_5) (forall_cons (fun _ h => by cases h; exact sl_26_6) (fun _ h => (List.not_mem_nil h).elim))))))))
def ps_26 : BT (Option PoolSpec) := btOfList 5 [q 0 [],q 1 [],q 3 [],q 0 [12298,16425],q 4 [],q 2 [],q 4 [8196],q 5 [8192],q 1 [12323,95],q 6 [4],q 5 [],q 0 [12298],q 2 [43],q 0 [12296],q 0 [8208],q 1 [8208],q 2 [4096],q 6 [],q 0 [8196],q 1 [12323],q 0 [12305],q 1 [12305],q 1 [35],q 2 [35],q 1 [12290],q 0 [12306],q 1 [12306],q 1 [8192],q 2 [12290],q 1 [12288],q 2 [12288]]
def B_26_1 : BT (List (List Nat)) := BT.empty
lemma B_26_1_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_26 1 xs.toFinset) B_26_1 := .empty
def U_26_2 : List Nat := [0]
def P_26_2 : BT (Option BoundPool) := buildPoolsSubBT 5 W_26 r_26 S_26 ps_26 U_26_2
def N_26_2 : List NodeSpec := [([4,7,2],[0],[]),([4,6,9],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_26_2 : checkNodesBT W_26 g_26 F_26 P_26_2 A_26 B_26_1 2 N_26_2 = true := by decide +kernel
def B_26_2 : BT (List (List Nat)) := buildBucketsBT W_26 N_26_2
set_option maxRecDepth 500000 in
lemma B_26_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_26 2 xs.toFinset) B_26_2 :=
  buildBucketsBT_sound (by decide) gp_26 W_26_ok (buildPoolsSubBT_sound S_26_ok) A_26_ok B_26_1_ok C_26_2
def U_26_3 : List Nat := (r 0 10)
def P_26_3 : BT (Option BoundPool) := buildPoolsSubBT 5 W_26 r_26 S_26 ps_26 U_26_3
def N_26_3 : List NodeSpec := [([4,0,2,9],[0],[0]),([12,5,4,2],[0,2],[]),([11,0,1,2],[1,2,3],[1,3]),([0,1,2,15],[4],[]),([12,4,8,2],[6],[2]),([4,6,8,3],[5,6,0,7],[0,2,4]),([24,8,1,2],[8],[]),([4,0,25,2],[9],[]),([12,13,1,2],[],[]),([17,1,2],[],[]),([0,1,19,2],[],[]),([0,1,2,21],[],[]),([17,1,2,3],[],[]),([0,1,2,22],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_26_3 : checkNodesBT W_26 g_26 F_26 P_26_3 A_26 B_26_2 3 N_26_3 = true := by decide +kernel
def B_26_3 : BT (List (List Nat)) := buildBucketsBT W_26 N_26_3
set_option maxRecDepth 500000 in
lemma B_26_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_26 3 xs.toFinset) B_26_3 :=
  buildBucketsBT_sound (by decide) gp_26 W_26_ok (buildPoolsSubBT_sound S_26_ok) A_26_ok B_26_2_ok C_26_3
def U_26_4 : List Nat := ([0,1,2,4,5]++r 10 18)
def P_26_4 : BT (Option BoundPool) := buildPoolsSubBT 5 W_26 r_26 S_26 ps_26 U_26_4
def N_26_4 : List NodeSpec := [([12,0,29,1,2],[1,4,0],[]),([0,1,2,3,22],[4],[]),([30,0,1,2,3],[5],[0,4]),([12,5,0,1,2],[4,0,1,10],[0]),([26,0,1,2,3],[11,4],[]),([26,0,1,2],[4,1,10,11,12],[3]),([28,0,1,2],[4,1,10,13],[]),([20,0,1,2,3],[2,4,14,15,10,16,17],[0]),([4,0,1,27,2],[4,5,17,13,1,10],[4]),([23,0,8,1,2],[18,5,19],[0,3]),([4,0,1,2,22],[2,20,4],[]),([0,1,2,22],[20,21,17,5],[4,5]),([14,0,1,2,3],[2,4,18,22,23],[0,2,4]),([12,4,1,2,3],[2,0,24],[0]),([12,0,8,1,2],[4,10,17,5,0,24],[0,1,3]),([12,4,1,2],[4,24],[0,1,2]),([30,0,1,2],[4,10,5,17,25,26],[4]),([4,6,1,2,3],[4,27,16],[0,2,4])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_26_4 : checkNodesBT W_26 g_26 F_26 P_26_4 A_26 B_26_3 4 N_26_4 = true := by decide +kernel
def B_26_4 : BT (List (List Nat)) := buildBucketsBT W_26 N_26_4
set_option maxRecDepth 500000 in
lemma B_26_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_26 4 xs.toFinset) B_26_4 :=
  buildBucketsBT_sound (by decide) gp_26 W_26_ok (buildPoolsSubBT_sound S_26_ok) A_26_ok B_26_3_ok C_26_4
def U_26_5 : List Nat := [0,1,2,4,16,24,28,29,30]
def P_26_5 : BT (Option BoundPool) := buildPoolsSubBT 5 W_26 r_26 S_26 ps_26 U_26_5
def N_26_5 : List NodeSpec := [([4,0,1,2,3],[1,0,2,4,16],[0,2,4]),([12,0,1,2,3],[2,0,24,28],[0,1,3,5]),([12,0,1,2],[2,4,24,28,0],[0,1,3,5]),([18,0,1,2],[2,0,29,30],[3,5])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_26_5 : checkNodesBT W_26 g_26 F_26 P_26_5 A_26 B_26_4 5 N_26_5 = true := by decide +kernel
def B_26_5 : BT (List (List Nat)) := buildBucketsBT W_26 N_26_5
set_option maxRecDepth 500000 in
lemma B_26_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_26 5 xs.toFinset) B_26_5 :=
  buildBucketsBT_sound (by decide) gp_26 W_26_ok (buildPoolsSubBT_sound S_26_ok) A_26_ok B_26_4_ok C_26_5
def U_26_6 : List Nat := [0,1,2,5]
def P_26_6 : BT (Option BoundPool) := buildPoolsSubBT 5 W_26 r_26 S_26 ps_26 U_26_6
def N_26_6 : List NodeSpec := [([0,1,2,3],[0,1,5,2],[0,1,2,3,4])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_26_6 : checkNodesBT W_26 g_26 F_26 P_26_6 A_26 B_26_5 6 N_26_6 = true := by decide +kernel
def B_26_6 : BT (List (List Nat)) := buildBucketsBT W_26 N_26_6
set_option maxRecDepth 500000 in
lemma B_26_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_26 6 xs.toFinset) B_26_6 :=
  buildBucketsBT_sound (by decide) gp_26 W_26_ok (buildPoolsSubBT_sound S_26_ok) A_26_ok B_26_5_ok C_26_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_26_ok : forestRootCheck r_26 g_26 [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 3,3,11)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_26_in : bucketContainsBT B_26_6 r_26 = true := by decide +kernel
lemma low_26 : Lower r_26 g_26 7 := lower_of_forestBT root_26_ok B_26_6_ok root_26_in
def g_27 := 0xfdc0fdc0fdc0fdc0
def r_27 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_27 : Lower r_27 g_27 5 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,8,9)]) (by decide +kernel) hc
def g_28 := 0xcf08cf08cf08cf08
def r_28 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_28 : Lower r_28 g_28 5 := by
  have hc : Lower (varsOf 14) 0xcf0ccf0ccf0ccf0c 4 := carry_of (swaps := [(0,3),(1,3)]) (by decide +kernel) low_22
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,2,3)]) (by decide +kernel) hc
def g_29 := 0xfc40fc40fc40fc40
def r_29 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_29 : Lower r_29 g_29 5 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,6,7)]) (by decide +kernel) hc
def g_30 := 0xf3a0f3a0f3a0f3a0
def r_30 : List Nat := varsOf 15
def p_30 : List Nat := [5,5,7,7,8,9,12,14,14,15]
def q_30 : List Nat := [4,1,6,3,0,1,4,10,6,11]
def F_30 : Nat := fullMask 10
set_option maxHeartbeats 0 in
lemma gp_30 : goodPairs g_30 p_30 q_30 := goodPairs_of (by decide +kernel)
def W_30 : BT Decor := buildWiresBT 2 (mkBase p_30 q_30 r_30) []
lemma W_30_ok : btAll (fun x => faithful p_30 q_30 x ∧ x.1 < 2^64) W_30 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_30 : List (List (Nat × Nat)) := [[]]
def A_30 : BT (List (Nat × Nat)) := btOfList 1 al_30
set_option maxHeartbeats 0 in
lemma A_30_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_30 = g_30) A_30 := btAll_ofList (autos_of (by decide +kernel))
def S_30 : BT (Option (Nat × Nat)) := btOfList 1 []
lemma S_30_ok : btAll (fun o => ∀ p, o = some p → Slice r_30 g_30 p.1 p.2) S_30 := btAll_ofList (fun _ h => (List.not_mem_nil h).elim)
def ps_30 : BT (Option PoolSpec) := btOfList 1 []
def B_30_2 : BT (List (List Nat)) := BT.empty
lemma B_30_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_30 2 xs.toFinset) B_30_2 := .empty
def U_30_3 : List Nat := []
def P_30_3 : BT (Option BoundPool) := buildPoolsSubBT 1 W_30 r_30 S_30 ps_30 U_30_3
def N_30_3 : List NodeSpec := [([0,1,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_30_3 : checkNodesBT W_30 g_30 F_30 P_30_3 A_30 B_30_2 3 N_30_3 = true := by decide +kernel
def B_30_3 : BT (List (List Nat)) := buildBucketsBT W_30 N_30_3
set_option maxRecDepth 500000 in
lemma B_30_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_30 3 xs.toFinset) B_30_3 :=
  buildBucketsBT_sound (by decide) gp_30 W_30_ok (buildPoolsSubBT_sound S_30_ok) A_30_ok B_30_2_ok C_30_3
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_30_ok : forestRootCheck r_30 g_30 [(VAR 0,4,5),(VAR 1,8,10),(VAR 2,1,5),(VAR 3,0,8)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_30_in : bucketContainsBT B_30_3 r_30 = true := by decide +kernel
lemma low_30 : Lower r_30 g_30 4 := lower_of_forestBT root_30_ok B_30_3_ok root_30_in
def g_31 := 0xfff2fff2fff2fff2
def r_31 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_31 : Lower r_31 g_31 3 := count_of (essPairs := [(VAR 0,0,1),(VAR 1,1,3),(VAR 2,0,4),(VAR 3,0,8)]) (by decide +kernel)
def g_32 := 0xf2f2f2f2f2f2f2f2
def r_32 : List Nat := varsOf 7
set_option maxHeartbeats 0 in
lemma low_32 : Lower r_32 g_32 2 := count_of (essPairs := [(VAR 0,0,1),(VAR 1,1,3),(VAR 2,0,4)]) (by decide +kernel)
def g_33 := 0xfff3fa20fff3fa20
def r_33 : List Nat := varsOf 31
def p_33 : List Nat := [5,5,9,9,11,11,12,12,14,14,15,16,17,20,22,22,23,23,24,26,26,27]
def q_33 : List Nat := [4,1,8,1,10,3,8,4,10,6,7,0,1,4,18,6,19,7,8,18,10,19]
def F_33 : Nat := fullMask 22
set_option maxHeartbeats 0 in
lemma gp_33 : goodPairs g_33 p_33 q_33 := goodPairs_of (by decide +kernel)
def W_33 : BT Decor := buildWiresBT 6 (mkBase p_33 q_33 r_33) [(1,2,3),(0,0,5),(0,1,5),(2,1,4),(3,8,5),(1,3,4),(3,2,10),(3,1,2),(1,12,4),(3,3,13),(1,2,4),(1,12,3),(1,1,2),(2,17,3),(1,1,3),(0,19,15),(2,0,4),(3,21,5),(1,0,4),(3,3,15),(2,5,4),(1,5,4),(0,1,2),(1,27,3),(2,17,4),(2,2,3),(3,2,19),(2,19,4),(1,8,2),(1,8,3),(2,1,2),(1,35,3),(2,1,3),(1,37,2),(1,30,4),(2,2,4),(1,1,4),(3,1,15),(1,40,3),(3,1,5)]
lemma W_33_ok : btAll (fun x => faithful p_33 q_33 x ∧ x.1 < 2^64) W_33 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_33 : List (List (Nat × Nat)) := [[]]
def A_33 : BT (List (Nat × Nat)) := btOfList 1 al_33
set_option maxHeartbeats 0 in
lemma A_33_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_33 = g_33) A_33 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_33_0 : Slice r_33 g_33 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) 0xfff3f000fff3f000 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_27
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_33_1 : Slice r_33 g_33 (subcubeFast 8 0) 5 := by
  have hc : Lower (varsOf 23) 0xf3f32020f3f32020 5 := carry_of (swaps := [(1,2),(3,4)]) (by decide +kernel) low_28
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_33_2 : Slice r_33 g_33 (subcubeFast 16 0) 5 := by
  have hc : Lower (varsOf 15) 0xfa20fa20fa20fa20 5 := carry_of (swaps := [(0,1)]) (by decide +kernel) low_29
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_33_3 : Slice r_33 g_33 (subcubeFast 8 1) 4 := by
  have hc : Lower (varsOf 22) 0xf3f33030f3f33030 4 := carry_of (swaps := [(0,3),(1,2),(2,3),(3,4)]) (by decide +kernel) low_22
  exact slice_fast_direct_f (z := 8) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_33_4 : Slice r_33 g_33 (subcubeFast 18 0) 4 := by
  have hc : Lower (varsOf 13) 0xfaa0faa0faa0faa0 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 18) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_33_5 : Slice r_33 g_33 (subcubeFast 1 2) 4 := by
  have hc : Lower (varsOf 28) 0xfff0f000fff0f000 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_33_6 : Slice r_33 g_33 (subcubeFast 4 0) 4 := by
  have hc : Lower (varsOf 27) 0xff33aa00ff33aa00 4 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_30
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_33_7 : Slice r_33 g_33 (subcubeFast 0 4) 3 := by
  have hc : Lower (varsOf 27) 0xffffff22ffffff22 3 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_31
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_33_8 : Slice r_33 g_33 (subcubeFast 24 0) 2 := by
  have hc : Lower (varsOf 7) 0x2020202020202020 2 := carry_of (swaps := [(1,2)]) (by decide +kernel) low_25
  exact slice_fast_direct_f (z := 24) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_33_9 : Slice r_33 g_33 (subcubeFast 16 4) 2 := by
  have hc : Lower (varsOf 11) 0xff22ff22ff22ff22 2 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_32
  exact slice_fast_direct_f (z := 16) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_33_10 : Slice r_33 g_33 (subcubeFast 8 4) 2 := by
  have hc : Lower (varsOf 19) 0xffff2222ffff2222 2 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_32
  exact slice_fast_direct_f (z := 8) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_33_11 : Slice r_33 g_33 (subcubeFast 0 17) 2 := by
  have hc : Lower (varsOf 14) 0xc000c000c000c 2 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_23
  exact slice_fast_direct_f (z := 0) (o := 17) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_33_12 : Slice r_33 g_33 (subcubeFast 1 16) 2 := by
  have hc : Lower (varsOf 14) 0xc000c000c000c 2 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_23
  exact slice_fast_direct_f (z := 1) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_33_13 : Slice r_33 g_33 (subcubeFast 0 5) 2 := by
  have hc : Lower (varsOf 26) 0xcc000000cc 2 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_23
  exact slice_fast_direct_f (z := 0) (o := 5) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_33_14 : Slice r_33 g_33 (subcubeFast 4 1) 2 := by
  have hc : Lower (varsOf 26) 0xff33ff00ff33ff00 2 := carry_of (swaps := [(0,3),(2,4),(3,4)]) (by decide +kernel) low_32
  exact slice_fast_direct_f (z := 4) (o := 1) (by decide +kernel) hc
def S_33 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 1 0,5),some (subcubeFast 8 0,5),some (subcubeFast 16 0,5),some (subcubeFast 8 1,4),some (subcubeFast 18 0,4),some (subcubeFast 1 2,4),some (subcubeFast 4 0,4),some (subcubeFast 0 4,3),some (subcubeFast 24 0,2),some (subcubeFast 16 4,2),some (subcubeFast 8 4,2),some (subcubeFast 0 17,2),some (subcubeFast 1 16,2),some (subcubeFast 0 5,2),some (subcubeFast 4 1,2)]
lemma S_33_ok : btAll (fun o => ∀ p, o = some p → Slice r_33 g_33 p.1 p.2) S_33 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_33_0) (forall_cons (fun _ h => by cases h; exact sl_33_1) (forall_cons (fun _ h => by cases h; exact sl_33_2) (forall_cons (fun _ h => by cases h; exact sl_33_3) (forall_cons (fun _ h => by cases h; exact sl_33_4) (forall_cons (fun _ h => by cases h; exact sl_33_5) (forall_cons (fun _ h => by cases h; exact sl_33_6) (forall_cons (fun _ h => by cases h; exact sl_33_7) (forall_cons (fun _ h => by cases h; exact sl_33_8) (forall_cons (fun _ h => by cases h; exact sl_33_9) (forall_cons (fun _ h => by cases h; exact sl_33_10) (forall_cons (fun _ h => by cases h; exact sl_33_11) (forall_cons (fun _ h => by cases h; exact sl_33_12) (forall_cons (fun _ h => by cases h; exact sl_33_13) (forall_cons (fun _ h => by cases h; exact sl_33_14) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))
def ps_33 : BT (Option PoolSpec) := btOfList 5 [q 3 [20484],q 3 [8199,16433],q 4 [],q 3 [],q 3 [8199],q 6 [],q 3 [8197],q 7 [],q 0 [],q 5 [],q 11 [],q 9 [],q 8 [],q 10 [],q 1 [16389],q 1 [16390],q 3 [20487],q 2 [12298],q 14 [],q 12 [],q 1 [16394],q 13 [],q 2 []]
def B_33_3 : BT (List (List Nat)) := BT.empty
lemma B_33_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_33 3 xs.toFinset) B_33_3 := .empty
def U_33_4 : List Nat := (r 0 9)
def P_33_4 : BT (Option BoundPool) := buildPoolsSubBT 5 W_33 r_33 S_33 ps_33 U_33_4
def N_33_4 : List NodeSpec := [([6,7,2,3,4],[0],[]),([14,0,2,3,4],[1],[]),([2,3,13,23],[1],[]),([0,1,5,15,10],[2,3],[]),([0,2,16,4,10],[4,5,2],[]),([18,0,2,4,10],[2,6,7],[]),([0,2,3,20,4],[3,8],[]),([0,2,3,9,4],[],[]),([11,12,0,3,4],[],[]),([1,2,3,22,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_33_4 : checkNodesBT W_33 g_33 F_33 P_33_4 A_33 B_33_3 4 N_33_4 = true := by decide +kernel
def B_33_4 : BT (List (List Nat)) := buildBucketsBT W_33 N_33_4
set_option maxRecDepth 500000 in
lemma B_33_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_33 4 xs.toFinset) B_33_4 :=
  buildBucketsBT_sound (by decide) gp_33 W_33_ok (buildPoolsSubBT_sound S_33_ok) A_33_ok B_33_3_ok C_33_4
def U_33_5 : List Nat := ([0]++r 2 15)
def P_33_5 : BT (Option BoundPool) := buildPoolsSubBT 5 W_33 r_33 S_33 ps_33 U_33_5
def N_33_5 : List NodeSpec := [([42,0,2,3,4,15],[2],[]),([30,0,1,3,4,15],[2],[]),([0,1,3,5,4,15],[2,3],[0]),([40,0,1,3,5,4],[3,2],[]),([0,1,2,3,15,10],[2,5,3],[0]),([0,1,2,5,4,10],[3,2,5],[0]),([2,17,3,4,23],[2,6],[]),([0,2,3,34,4],[8,3,2,5,7],[]),([0,2,3,36,4],[8,3,2,7],[]),([0,7,2,3,5,4],[0,9],[0]),([12,2,3,4,23],[2,4,9],[0]),e5 [24] [2,9],e5 [39] [2,9],([21,30,1,2,3,4],[2,9,3],[]),u5 [11] [2,9,7],e5 [43] [3,2,9],e5 [26] [3,2,9],([6,1,2,3,5,4],[3,9,7],[0]),([0,2,3,19,4,15],[5,7,2,9],[0]),([21,1,2,3,5,4],[9,2,3],[0]),([0,2,3,28,4],[9,3,2,5],[]),([0,2,3,4,13],[2,10,3],[0]),([32,0,2,3,4],[5,7,2,10],[]),([0,2,3,16,4],[9,4,5,2,10],[0]),e5 [25] [3,2,9,10,11],([40,0,2,3,19,4],[5,11,2],[]),([29,0,2,3,4],[11,10],[]),([0,2,17,3,4,10],[6,5,7,12,10],[0]),([12,0,2,3,4,10],[10,12,4,5],[0]),([18,0,2,3,4],[2,9,13,10,6],[0]),([0,2,38,3,4],[8,3,2,13],[]),([31,0,2,3,4],[9,11,13],[]),([0,2,33,3,4],[10,8,2,13],[]),([30,0,2,3,4,41],[2,9,14],[]),([0,2,3,5,4,41],[9,10,14,2],[]),([8,30,0,2,3,4],[2,13,5,15],[]),([8,0,2,3,5,4],[7,9,10,15],[0]),([44,0,2,3,5,4],[2,9,16],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_33_5 : checkNodesBT W_33 g_33 F_33 P_33_5 A_33 B_33_4 5 N_33_5 = true := by decide +kernel
def B_33_5 : BT (List (List Nat)) := buildBucketsBT W_33 N_33_5
set_option maxRecDepth 500000 in
lemma B_33_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_33 5 xs.toFinset) B_33_5 :=
  buildBucketsBT_sound (by decide) gp_33 W_33_ok (buildPoolsSubBT_sound S_33_ok) A_33_ok B_33_4_ok C_33_5
def U_33_6 : List Nat := (r 2 4++r 8 8++r 17 5)
def P_33_6 : BT (Option BoundPool) := buildPoolsSubBT 5 W_33 r_33 S_33 ps_33 U_33_6
def N_33_6 : List NodeSpec := [([1,2,3,4,23],[2,3],[0]),([37,0,2,3,4],[8,2,3,5],[0]),([21,1,2,3,4],[2,9,3],[0]),([12,0,2,3,4],[9,2,5,4],[0]),([0,2,3,19,4],[9,3,5,2],[0]),u5 [5] [3,5,2,9,11],u5 [10] [3,2,9,10,12,5],([0,2,17,3,4],[9,2,5,3,13],[0]),([0,2,3,4,41],[9,2,14],[0]),([8,0,2,3,4],[2,3,5,9,10,15],[0]),u5 [30] [3,2,5,9,17],([0,27,2,3,4],[2,3,8,9,5,18],[0]),u5 [15] [2,10,19,3,5,13,9],u5 [40] [3,2,9,5,10,19,20],([35,0,2,3,4],[2,3,9,5,21],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_33_6 : checkNodesBT W_33 g_33 F_33 P_33_6 A_33 B_33_5 6 N_33_6 = true := by decide +kernel
def B_33_6 : BT (List (List Nat)) := buildBucketsBT W_33 N_33_6
set_option maxRecDepth 500000 in
lemma B_33_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_33 6 xs.toFinset) B_33_6 :=
  buildBucketsBT_sound (by decide) gp_33 W_33_ok (buildPoolsSubBT_sound S_33_ok) A_33_ok B_33_5_ok C_33_6
def U_33_7 : List Nat := [2,3,8,9,22]
def P_33_7 : BT (Option BoundPool) := buildPoolsSubBT 5 W_33 r_33 S_33 ps_33 U_33_7
def N_33_7 : List NodeSpec := [u5 [] [8,2,9,3,22]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_33_7 : checkNodesBT W_33 g_33 F_33 P_33_7 A_33 B_33_6 7 N_33_7 = true := by decide +kernel
def B_33_7 : BT (List (List Nat)) := buildBucketsBT W_33 N_33_7
set_option maxRecDepth 500000 in
lemma B_33_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_33 7 xs.toFinset) B_33_7 :=
  buildBucketsBT_sound (by decide) gp_33 W_33_ok (buildPoolsSubBT_sound S_33_ok) A_33_ok B_33_6_ok C_33_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_33_ok : forestRootCheck r_33 g_33 [(VAR 0,4,5),(VAR 1,5,7),(VAR 2,1,5),(VAR 3,1,9),(VAR 4,0,16)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_33_in : bucketContainsBT B_33_7 r_33 = true := by decide +kernel
lemma low_33 : Lower r_33 g_33 8 := lower_of_forestBT root_33_ok B_33_7_ok root_33_in
def g_34 := 0xacacacacacacacac
def r_34 : List Nat := varsOf 7
def p_34 : List Nat := [2,3,5,5,7]
def q_34 : List Nat := [0,1,4,1,6]
def F_34 : Nat := fullMask 5
set_option maxHeartbeats 0 in
lemma gp_34 : goodPairs g_34 p_34 q_34 := goodPairs_of (by decide +kernel)
def W_34 : BT Decor := buildWiresBT 2 (mkBase p_34 q_34 r_34) []
lemma W_34_ok : btAll (fun x => faithful p_34 q_34 x ∧ x.1 < 2^64) W_34 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_34 : List (List (Nat × Nat)) := [[]]
def A_34 : BT (List (Nat × Nat)) := btOfList 1 al_34
set_option maxHeartbeats 0 in
lemma A_34_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_34 = g_34) A_34 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_34_0 : Slice r_34 g_34 (subcubeFast 1 0) 1 := by
  have hc : Lower (varsOf 6) 0xc0c0c0c0c0c0c0c 1 := carry_of (swaps := [(0,2),(1,2)]) (by decide +kernel) low_21
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_34_1 : Slice r_34 g_34 (subcubeFast 0 2) 1 := by
  have hc : Lower (varsOf 5) 0x5050505050505050 1 := carry_of (swaps := [(0,1),(1,2)]) (by decide +kernel) low_21
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
def S_34 : BT (Option (Nat × Nat)) := btOfList 1 [some (subcubeFast 1 0,1),some (subcubeFast 0 2,1)]
lemma S_34_ok : btAll (fun o => ∀ p, o = some p → Slice r_34 g_34 p.1 p.2) S_34 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_34_0) (forall_cons (fun _ h => by cases h; exact sl_34_1) (fun _ h => (List.not_mem_nil h).elim)))
def ps_34 : BT (Option PoolSpec) := btOfList 1 [q 0 [],q 1 []]
def B_34_1 : BT (List (List Nat)) := BT.empty
lemma B_34_1_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_34 1 xs.toFinset) B_34_1 := .empty
def U_34_2 : List Nat := [0,1]
def P_34_2 : BT (Option BoundPool) := buildPoolsSubBT 1 W_34 r_34 S_34 ps_34 U_34_2
def N_34_2 : List NodeSpec := [([0,1,2],[0,1],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_34_2 : checkNodesBT W_34 g_34 F_34 P_34_2 A_34 B_34_1 2 N_34_2 = true := by decide +kernel
def B_34_2 : BT (List (List Nat)) := buildBucketsBT W_34 N_34_2
set_option maxRecDepth 500000 in
lemma B_34_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_34 2 xs.toFinset) B_34_2 :=
  buildBucketsBT_sound (by decide) gp_34 W_34_ok (buildPoolsSubBT_sound S_34_ok) A_34_ok B_34_1_ok C_34_2
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_34_ok : forestRootCheck r_34 g_34 [(VAR 0,4,5),(VAR 1,0,2),(VAR 2,1,5)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_34_in : bucketContainsBT B_34_2 r_34 = true := by decide +kernel
lemma low_34 : Lower r_34 g_34 3 := lower_of_forestBT root_34_ok B_34_2_ok root_34_in
def g_35 := 0xeafceafceafceafc
def r_35 : List Nat := varsOf 15
def p_35 : List Nat := [2,3,4,5,9,9,11,13,14,14]
def q_35 : List Nat := [0,1,0,1,8,1,10,12,12,10]
def F_35 : Nat := fullMask 10
set_option maxHeartbeats 0 in
lemma gp_35 : goodPairs g_35 p_35 q_35 := goodPairs_of (by decide +kernel)
def W_35 : BT Decor := buildWiresBT 4 (mkBase p_35 q_35 r_35) [(3,0,3),(3,1,3),(1,5,2),(1,1,3),(3,4,7),(3,0,7),(3,2,3),(1,1,2)]
lemma W_35_ok : btAll (fun x => faithful p_35 q_35 x ∧ x.1 < 2^64) W_35 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_35 : List (List (Nat × Nat)) := [[],[(1,2)]]
def A_35 : BT (List (Nat × Nat)) := btOfList 1 al_35
set_option maxHeartbeats 0 in
lemma A_35_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_35 = g_35) A_35 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_35_0 : Slice r_35 g_35 (subcubeFast 1 0) 4 := by
  have hc : Lower (varsOf 14) 0xc0fcc0fcc0fcc0fc 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_22
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_35_1 : Slice r_35 g_35 (subcubeFast 2 0) 3 := by
  have hc : Lower (varsOf 13) 0xaaf0aaf0aaf0aaf0 3 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_34
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_35_2 : Slice r_35 g_35 (subcubeFast 4 0) 3 := by
  have hc : Lower (varsOf 11) 0xaaccaaccaaccaacc 3 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_34
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_35_3 : Slice r_35 g_35 (subcubeFast 0 2) 2 := by
  have hc : Lower (varsOf 13) 0x500050005000500 2 := carry_of (swaps := [(0,1),(1,3)]) (by decide +kernel) low_23
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_35_4 : Slice r_35 g_35 (subcubeFast 0 4) 2 := by
  have hc : Lower (varsOf 11) 0x1100110011001100 2 := carry_of (swaps := [(0,1),(1,2),(2,3)]) (by decide +kernel) low_23
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
def S_35 : BT (Option (Nat × Nat)) := btOfList 3 [some (subcubeFast 1 0,4),some (subcubeFast 2 0,3),some (subcubeFast 4 0,3),some (subcubeFast 0 2,2),some (subcubeFast 0 4,2)]
lemma S_35_ok : btAll (fun o => ∀ p, o = some p → Slice r_35 g_35 p.1 p.2) S_35 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_35_0) (forall_cons (fun _ h => by cases h; exact sl_35_1) (forall_cons (fun _ h => by cases h; exact sl_35_2) (forall_cons (fun _ h => by cases h; exact sl_35_3) (forall_cons (fun _ h => by cases h; exact sl_35_4) (fun _ h => (List.not_mem_nil h).elim))))))
def ps_35 : BT (Option PoolSpec) := btOfList 4 [q 0 [12295,8213],q 0 [],q 1 [],q 0 [12299],q 4 [],q 2 [],q 3 [],q 0 [12293],q 0 [8197]]
def B_35_1 : BT (List (List Nat)) := BT.empty
lemma B_35_1_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_35 1 xs.toFinset) B_35_1 := .empty
def U_35_2 : List Nat := []
def P_35_2 : BT (Option BoundPool) := buildPoolsSubBT 4 W_35 r_35 S_35 ps_35 U_35_2
def N_35_2 : List NodeSpec := [([4,1,6],[],[]),([8,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_35_2 : checkNodesBT W_35 g_35 F_35 P_35_2 A_35 B_35_1 2 N_35_2 = true := by decide +kernel
def B_35_2 : BT (List (List Nat)) := buildBucketsBT W_35 N_35_2
set_option maxRecDepth 500000 in
lemma B_35_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_35 2 xs.toFinset) B_35_2 :=
  buildBucketsBT_sound (by decide) gp_35 W_35_ok (buildPoolsSubBT_sound S_35_ok) A_35_ok B_35_1_ok C_35_2
def U_35_3 : List Nat := [0,1]
def P_35_3 : BT (Option BoundPool) := buildPoolsSubBT 4 W_35 r_35 S_35 ps_35 U_35_3
def N_35_3 : List NodeSpec := [([0,1,6,3],[0],[0]),([9,1,2,3],[1],[]),([0,1,6],[],[]),([10,4,1,2],[],[1]),([4,1,2,7],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_35_3 : checkNodesBT W_35 g_35 F_35 P_35_3 A_35 B_35_2 3 N_35_3 = true := by decide +kernel
def B_35_3 : BT (List (List Nat)) := buildBucketsBT W_35 N_35_3
set_option maxRecDepth 500000 in
lemma B_35_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_35 3 xs.toFinset) B_35_3 :=
  buildBucketsBT_sound (by decide) gp_35 W_35_ok (buildPoolsSubBT_sound S_35_ok) A_35_ok B_35_2_ok C_35_3
def U_35_4 : List Nat := (r 1 8)
def P_35_4 : BT (Option BoundPool) := buildPoolsSubBT 4 W_35 r_35 S_35 ps_35 U_35_4
def N_35_4 : List NodeSpec := [([4,1,2,3],[1],[0,1]),([10,0,1,2,3],(r 2 4),[0,1]),([10,0,1,2],[1,4,6,5],[1]),([0,1,2,7],[6,2,1,4],[]),([0,1,2,3,7],[7,2,6],[0]),([0,1,2,11,3],[8,2,6,4],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_35_4 : checkNodesBT W_35 g_35 F_35 P_35_4 A_35 B_35_3 4 N_35_4 = true := by decide +kernel
def B_35_4 : BT (List (List Nat)) := buildBucketsBT W_35 N_35_4
set_option maxRecDepth 500000 in
lemma B_35_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_35 4 xs.toFinset) B_35_4 :=
  buildBucketsBT_sound (by decide) gp_35 W_35_ok (buildPoolsSubBT_sound S_35_ok) A_35_ok B_35_3_ok C_35_4
def U_35_5 : List Nat := [1,2,5]
def P_35_5 : BT (Option BoundPool) := buildPoolsSubBT 4 W_35 r_35 S_35 ps_35 U_35_5
def N_35_5 : List NodeSpec := [([0,1,2,3],[1,2,5],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_35_5 : checkNodesBT W_35 g_35 F_35 P_35_5 A_35 B_35_4 5 N_35_5 = true := by decide +kernel
def B_35_5 : BT (List (List Nat)) := buildBucketsBT W_35 N_35_5
set_option maxRecDepth 500000 in
lemma B_35_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_35 5 xs.toFinset) B_35_5 :=
  buildBucketsBT_sound (by decide) gp_35 W_35_ok (buildPoolsSubBT_sound S_35_ok) A_35_ok B_35_4_ok C_35_5
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_35_ok : forestRootCheck r_35 g_35 [(VAR 0,8,9),(VAR 1,0,2),(VAR 2,0,4),(VAR 3,1,9)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_35_in : bucketContainsBT B_35_5 r_35 = true := by decide +kernel
lemma low_35 : Lower r_35 g_35 6 := lower_of_forestBT root_35_ok B_35_5_ok root_35_in
def g_36 := 0xf280f280f280f280
def r_36 : List Nat := varsOf 15
def p_36 : List Nat := [7,7,7,9,9,12,12,13,14,14,15]
def q_36 : List Nat := [6,5,3,8,1,8,4,5,10,6,11]
def F_36 : Nat := fullMask 11
set_option maxHeartbeats 0 in
lemma gp_36 : goodPairs g_36 p_36 q_36 := goodPairs_of (by decide +kernel)
def W_36 : BT Decor := buildWiresBT 2 (mkBase p_36 q_36 r_36) []
lemma W_36_ok : btAll (fun x => faithful p_36 q_36 x ∧ x.1 < 2^64) W_36 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_36 : List (List (Nat × Nat)) := [[]]
def A_36 : BT (List (Nat × Nat)) := btOfList 1 al_36
set_option maxHeartbeats 0 in
lemma A_36_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_36 = g_36) A_36 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_36_0 : Slice r_36 g_36 (subcubeFast 0 1) 3 := by
  have hc : Lower (varsOf 14) 0xf3c0f3c0f3c0f3c0 3 := carry_of (swaps := [(0,3),(1,2),(2,3)]) (by decide +kernel) low_34
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_36_1 : Slice r_36 g_36 (subcubeFast 4 0) 2 := by
  have hc : Lower (varsOf 11) 0x2200220022002200 2 := carry_of (swaps := [(1,2),(2,3)]) (by decide +kernel) low_25
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_36_2 : Slice r_36 g_36 (subcubeFast 0 8) 2 := by
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) low_32
def S_36 : BT (Option (Nat × Nat)) := btOfList 2 [some (subcubeFast 0 1,3),some (subcubeFast 4 0,2),some (subcubeFast 0 8,2)]
lemma S_36_ok : btAll (fun o => ∀ p, o = some p → Slice r_36 g_36 p.1 p.2) S_36 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_36_0) (forall_cons (fun _ h => by cases h; exact sl_36_1) (forall_cons (fun _ h => by cases h; exact sl_36_2) (fun _ h => (List.not_mem_nil h).elim))))
def ps_36 : BT (Option PoolSpec) := btOfList 2 [q 0 [],q 1 [],q 2 []]
def B_36_3 : BT (List (List Nat)) := BT.empty
lemma B_36_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_36 3 xs.toFinset) B_36_3 := .empty
def U_36_4 : List Nat := [0,1,2]
def P_36_4 : BT (Option BoundPool) := buildPoolsSubBT 2 W_36 r_36 S_36 ps_36 U_36_4
def N_36_4 : List NodeSpec := [([0,1,2,3],[0,1,2],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_36_4 : checkNodesBT W_36 g_36 F_36 P_36_4 A_36 B_36_3 4 N_36_4 = true := by decide +kernel
def B_36_4 : BT (List (List Nat)) := buildBucketsBT W_36 N_36_4
set_option maxRecDepth 500000 in
lemma B_36_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_36 4 xs.toFinset) B_36_4 :=
  buildBucketsBT_sound (by decide) gp_36 W_36_ok (buildPoolsSubBT_sound S_36_ok) A_36_ok B_36_3_ok C_36_4
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_36_ok : forestRootCheck r_36 g_36 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,1,9)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_36_in : bucketContainsBT B_36_4 r_36 = true := by decide +kernel
lemma low_36 : Lower r_36 g_36 5 := lower_of_forestBT root_36_ok B_36_4_ok root_36_in
def g_37 := 0xcf80cf80cf80cf80
def r_37 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_37 : Lower r_37 g_37 4 := by
  have hc : Lower (varsOf 14) 0xcfc0cfc0cfc0cfc0 3 := carry_of (swaps := [(0,3),(1,3)]) (by decide +kernel) low_34
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,6,7)]) (by decide +kernel) hc
def g_38 := 0xfff3f280fff3f280
def r_38 : List Nat := varsOf 31
def p_38 : List Nat := [7,7,7,9,9,12,12,13,14,14,15,16,17,20,21,22,22,23,24,26,26,27,27]
def q_38 : List Nat := [6,5,3,8,1,8,4,5,10,6,11,0,1,4,5,18,6,19,8,18,10,19,11]
def F_38 : Nat := fullMask 23
set_option maxHeartbeats 0 in
lemma gp_38 : goodPairs g_38 p_38 q_38 := goodPairs_of (by decide +kernel)
def W_38 : BT Decor := buildWiresBT 6 (mkBase p_38 q_38 r_38) [(1,2,3),(0,1,5),(1,2,4),(1,3,4),(2,3,4),(0,0,5),(2,1,4),(3,11,5),(1,1,4),(0,5,13),(0,1,3),(1,11,3),(2,0,4),(3,2,3),(3,18,1),(2,1,2),(1,20,3),(1,9,2),(3,9,1),(3,3,7),(2,5,4),(3,1,5),(0,1,7),(1,11,2),(1,15,4),(1,15,2),(2,1,3),(1,31,4),(1,18,4),(1,20,4),(1,1,3),(2,35,4),(3,3,13),(1,5,4),(3,2,8),(1,31,2),(0,1,8)]
lemma W_38_ok : btAll (fun x => faithful p_38 q_38 x ∧ x.1 < 2^64) W_38 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_38 : List (List (Nat × Nat)) := [[]]
def A_38 : BT (List (Nat × Nat)) := btOfList 1 al_38
set_option maxHeartbeats 0 in
lemma A_38_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_38 = g_38) A_38 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_38_0 : Slice r_38 g_38 (subcubeFast 0 1) 6 := by
  have hc : Lower (varsOf 30) 0xfff3f3c0fff3f3c0 6 := carry_of (swaps := [(0,4),(1,3),(2,4)]) (by decide +kernel) low_35
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_38_1 : Slice r_38 g_38 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) 0xff332200ff332200 5 := carry_of (swaps := [(1,2),(2,4),(3,4)]) (by decide +kernel) low_28
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_38_2 : Slice r_38 g_38 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) 0xfff3f000fff3f000 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_27
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_38_3 : Slice r_38 g_38 (subcubeFast 16 0) 5 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_36
set_option maxHeartbeats 0 in
lemma sl_38_4 : Slice r_38 g_38 (subcubeFast 4 1) 4 := by
  have hc : Lower (varsOf 26) 0xff333300ff333300 4 := carry_of (swaps := [(0,3),(1,2),(2,4)]) (by decide +kernel) low_22
  exact slice_fast_direct_f (z := 4) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_38_5 : Slice r_38 g_38 (subcubeFast 1 2) 4 := by
  have hc : Lower (varsOf 28) 0xfff0f000fff0f000 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_38_6 : Slice r_38 g_38 (identDom 1 2) 5 := by
  have hc : Lower (varsOf 27) 0xffffee88ffffee88 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_4
  exact slice_ident (u := 1) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_38_7 : Slice r_38 g_38 (identDom 1 4) 5 := by
  exact slice_ident (u := 1) (v := 4) (by decide +kernel) low_6
set_option maxHeartbeats 0 in
lemma sl_38_8 : Slice r_38 g_38 (subcubeFast 8 0) 4 := by
  have hc : Lower (varsOf 23) 0xf3f38080f3f38080 4 := carry_of (swaps := [(1,2),(3,4)]) (by decide +kernel) low_37
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_38_9 : Slice r_38 g_38 (subcubeFast 8 1) 3 := by
  have hc : Lower (varsOf 22) 0xf3f3c0c0f3f3c0c0 3 := carry_of (swaps := [(0,3),(1,2),(2,3),(3,4)]) (by decide +kernel) low_34
  exact slice_fast_direct_f (z := 8) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_38_10 : Slice r_38 g_38 (subcubeFast 16 1) 3 := by
  have hc : Lower (varsOf 14) 0xf3c0f3c0f3c0f3c0 3 := carry_of (swaps := [(0,3),(1,2),(2,3)]) (by decide +kernel) low_34
  exact slice_fast_direct_f (z := 16) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_38_11 : Slice r_38 g_38 (subcubeFast 16 8) 2 := by
  exact slice_fast_direct_f (z := 16) (o := 8) (by decide +kernel) low_32
set_option maxHeartbeats 0 in
lemma sl_38_12 : Slice r_38 g_38 (subcubeFast 20 0) 2 := by
  have hc : Lower (varsOf 11) 0x2200220022002200 2 := carry_of (swaps := [(1,2),(2,3)]) (by decide +kernel) low_25
  exact slice_fast_direct_f (z := 20) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_38_13 : Slice r_38 g_38 (subcubeFast 4 8) 2 := by
  have hc : Lower (varsOf 19) 0xffff2222ffff2222 2 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_32
  exact slice_fast_direct_f (z := 4) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_38_14 : Slice r_38 g_38 (subcubeFast 0 17) 2 := by
  have hc : Lower (varsOf 14) 0xc000c000c000c 2 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_23
  exact slice_fast_direct_f (z := 0) (o := 17) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_38_15 : Slice r_38 g_38 (subcubeFast 1 16) 2 := by
  have hc : Lower (varsOf 14) 0xc000c000c000c 2 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_23
  exact slice_fast_direct_f (z := 1) (o := 16) (by decide +kernel) hc
def S_38 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 0 1,6),some (subcubeFast 4 0,5),some (subcubeFast 1 0,5),some (subcubeFast 16 0,5),some (subcubeFast 4 1,4),some (subcubeFast 1 2,4),some (identDom 1 2,5),some (identDom 1 4,5),some (subcubeFast 8 0,4),some (subcubeFast 8 1,3),some (subcubeFast 16 1,3),some (subcubeFast 16 8,2),some (subcubeFast 20 0,2),some (subcubeFast 4 8,2),some (subcubeFast 0 17,2),some (subcubeFast 1 16,2)]
lemma S_38_ok : btAll (fun o => ∀ p, o = some p → Slice r_38 g_38 p.1 p.2) S_38 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_38_0) (forall_cons (fun _ h => by cases h; exact sl_38_1) (forall_cons (fun _ h => by cases h; exact sl_38_2) (forall_cons (fun _ h => by cases h; exact sl_38_3) (forall_cons (fun _ h => by cases h; exact sl_38_4) (forall_cons (fun _ h => by cases h; exact sl_38_5) (forall_cons (fun _ h => by cases h; exact sl_38_6) (forall_cons (fun _ h => by cases h; exact sl_38_7) (forall_cons (fun _ h => by cases h; exact sl_38_8) (forall_cons (fun _ h => by cases h; exact sl_38_9) (forall_cons (fun _ h => by cases h; exact sl_38_10) (forall_cons (fun _ h => by cases h; exact sl_38_11) (forall_cons (fun _ h => by cases h; exact sl_38_12) (forall_cons (fun _ h => by cases h; exact sl_38_13) (forall_cons (fun _ h => by cases h; exact sl_38_14) (forall_cons (fun _ h => by cases h; exact sl_38_15) (fun _ h => (List.not_mem_nil h).elim)))))))))))))))))
def ps_38 : BT (Option PoolSpec) := btOfList 5 [q 4 [20484],q 14 [],q 3 [],q 4 [],q 6 [],q 5 [],q 2 [],q 11 [],q 13 [],q 8 [],q 4 [20487],q 7 [],q 8 [20484],q 12 [],q 10 [],q 1 [16390],q 9 [],q 0 [12294,16509],q 1 [16389],q 15 [],q 1 [16398],q 0 [12293],q 1 [12292],q 0 [12294],q 0 []]
def B_38_2 : BT (List (List Nat)) := BT.empty
lemma B_38_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_38 2 xs.toFinset) B_38_2 := .empty
def U_38_3 : List Nat := []
def P_38_3 : BT (Option BoundPool) := buildPoolsSubBT 5 W_38 r_38 S_38 ps_38 U_38_3
def N_38_3 : List NodeSpec := [([0,6,7,8],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_38_3 : checkNodesBT W_38 g_38 F_38 P_38_3 A_38 B_38_2 3 N_38_3 = true := by decide +kernel
def B_38_3 : BT (List (List Nat)) := buildBucketsBT W_38 N_38_3
set_option maxRecDepth 500000 in
lemma B_38_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_38 3 xs.toFinset) B_38_3 :=
  buildBucketsBT_sound (by decide) gp_38 W_38_ok (buildPoolsSubBT_sound S_38_ok) A_38_ok B_38_2_ok C_38_3
def U_38_4 : List Nat := (r 0 4)
def P_38_4 : BT (Option BoundPool) := buildPoolsSubBT 5 W_38 r_38 S_38 ps_38 U_38_4
def N_38_4 : List NodeSpec := [([10,6,2,3,4],[0],[]),([0,15,2,16,4],[1],[]),([0,1,5,7,8],[2,3],[0]),([0,6,3,4,7],[],[0]),([9,0,6,2,4],[],[]),([0,2,3,12,4],[],[]),([0,6,2,4,8],[],[0]),([0,2,3,14,4],[],[]),([17,19,2,3,4],[],[]),([18,0,1,21,4],[],[]),([17,6,2,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_38_4 : checkNodesBT W_38 g_38 F_38 P_38_4 A_38 B_38_3 4 N_38_4 = true := by decide +kernel
def B_38_4 : BT (List (List Nat)) := buildBucketsBT W_38 N_38_4
set_option maxRecDepth 500000 in
lemma B_38_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_38 4 xs.toFinset) B_38_4 :=
  buildBucketsBT_sound (by decide) gp_38 W_38_ok (buildPoolsSubBT_sound S_38_ok) A_38_ok B_38_3_ok C_38_4
def U_38_5 : List Nat := (r 0 20)
def P_38_5 : BT (Option BoundPool) := buildPoolsSubBT 5 W_38 r_38 S_38 ps_38 U_38_5
def N_38_5 : List NodeSpec := [([9,0,1,2,5,4],[3],[0]),([0,1,2,5,4,8],[3,2],[0]),e5 [30] [4],e5 [40] [4],e5 [28] [4],([31,0,1,2,4,8],[2,5],[]),([20,0,1,3,4,7],[3,2,5],[]),e5 [22] [3,4,5],e5 [38] [3,4,5],([10,1,2,3,5,4],[3,5],[0]),([9,31,0,1,2,4],[5],[]),([20,18,0,1,3,4],[5,3],[0]),([17,18,1,2,3,4],[5,3],[0]),e5 [25] [6,3,1],([17,31,2,3,4],[5,3,7],[]),([31,0,2,3,4],[5,3,7],[]),([36,0,2,3,4],[5,7,3],[]),([37,0,2,3,4],[6,3,7],[]),u5 [16] [6,3,7,2],([0,23,2,3,4],[6,7,3],[]),([9,31,0,2,4],[7],[]),e5 [24] [7],([0,15,1,2,4,8],[7,5],[]),u5 [21] [7,5],([0,2,3,16,4],[7,1,6,8],[]),([31,0,2,4,8],[7,8],[]),e5 [33] [8],e5 [39] [8],([18,0,1,2,4,8],[8,2],[]),([0,1,2,3,7,8],[8,3,9],[0]),([0,1,3,5,4,7],[9,2],[0]),([26,0,2,3,5,4],[4,5,10],[]),e5 [34] [3,5,11],e5 [29] [3,5,11],e5 [41] [3,6,11],([11,31,0,2,3,4],[11,2,7,9],[]),([0,6,2,3,5,4],[0,5,12],[0]),([0,6,2,3,4],[0,11,12],[0]),([0,27,2,3,4],[6,13,7],[]),([31,0,2,3,4,7],[7,13,8],[]),([11,20,0,2,3,4],[3,14,5,11],[]),([17,1,2,3,5,4],[5,14,3],[0]),([11,0,15,2,3,4],[11,14,5],[0]),([11,18,0,2,3,4],[8,15],[]),([11,0,2,3,5,4],[11,5,14,15],[0]),([31,20,0,2,3,4],[3,16,5,7],[]),([0,19,2,3,4],[16,11,8],[0]),([0,2,3,4,32],[17,7,8],[]),e5 [32] [17,11],([0,2,3,5,4,13],[5,14,18,1],[0]),([18,0,2,3,4,13],[8,18],[]),([0,2,3,35,4,7],[19,7,9,13],[]),e5 [6] [],e5 [19] [],e5 [27] [],e5 [23] []]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_38_5 : checkNodesBT W_38 g_38 F_38 P_38_5 A_38 B_38_4 5 N_38_5 = true := by decide +kernel
def B_38_5 : BT (List (List Nat)) := buildBucketsBT W_38 N_38_5
set_option maxRecDepth 500000 in
lemma B_38_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_38 5 xs.toFinset) B_38_5 :=
  buildBucketsBT_sound (by decide) gp_38 W_38_ok (buildPoolsSubBT_sound S_38_ok) A_38_ok B_38_4_ok C_38_5
def U_38_6 : List Nat := (r 2 8++[11]++r 13 4++r 18 6)
def P_38_6 : BT (Option BoundPool) := buildPoolsSubBT 5 W_38 r_38 S_38 ps_38 U_38_6
def N_38_6 : List NodeSpec := [([17,1,2,3,4],[3,5,2],[0]),u5 [18] [3,5,9,2],u5 [5] [3,7,5,4,9,2],u5 [20] [5,3,4,9,2],u5 [7] [3,2,13,5,4,9],u5 [11] [2,11,9,5,15],([11,0,2,3,4],[11,2,5,14,15],[0]),([0,2,3,4,13],[5,2,18],[0]),u5 [8] [19,2,3,8,5,11,9],u5 [9] [5,2,16,20],([0,2,3,35,4],[5,6,21,7,3,8],[0]),u5 [15] [5,3,16,2,22],u5 [31] [3,9,4,5,2,11,23,8,7],([31,0,2,3,4],[5,3,7,8,11,23],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_38_6 : checkNodesBT W_38 g_38 F_38 P_38_6 A_38 B_38_5 6 N_38_6 = true := by decide +kernel
def B_38_6 : BT (List (List Nat)) := buildBucketsBT W_38 N_38_6
set_option maxRecDepth 500000 in
lemma B_38_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_38 6 xs.toFinset) B_38_6 :=
  buildBucketsBT_sound (by decide) gp_38 W_38_ok (buildPoolsSubBT_sound S_38_ok) A_38_ok B_38_5_ok C_38_6
def U_38_7 : List Nat := [2,3,5,24]
def P_38_7 : BT (Option BoundPool) := buildPoolsSubBT 5 W_38 r_38 S_38 ps_38 U_38_7
def N_38_7 : List NodeSpec := [u5 [] [24,3,5,2]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_38_7 : checkNodesBT W_38 g_38 F_38 P_38_7 A_38 B_38_6 7 N_38_7 = true := by decide +kernel
def B_38_7 : BT (List (List Nat)) := buildBucketsBT W_38 N_38_7
set_option maxRecDepth 500000 in
lemma B_38_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_38 7 xs.toFinset) B_38_7 :=
  buildBucketsBT_sound (by decide) gp_38 W_38_ok (buildPoolsSubBT_sound S_38_ok) A_38_ok B_38_6_ok C_38_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_38_ok : forestRootCheck r_38 g_38 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,1,9),(VAR 4,0,16)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_38_in : bucketContainsBT B_38_7 r_38 = true := by decide +kernel
lemma low_38 : Lower r_38 g_38 8 := lower_of_forestBT root_38_ok B_38_7_ok root_38_in
def g_39 := 0xfffef800fffef800
def r_39 : List Nat := varsOf 31
def p_39 : List Nat := [11,11,11,12,12,13,13,14,14,15,17,17,18,18,19,20,20,21,22,23,24,24,25,26]
def q_39 : List Nat := [10,9,3,8,4,9,5,10,6,7,16,1,16,2,3,16,4,5,6,7,16,8,9,10]
def F_39 : Nat := fullMask 24
set_option maxHeartbeats 0 in
lemma gp_39 : goodPairs g_39 p_39 q_39 := goodPairs_of (by decide +kernel)
def W_39 : BT Decor := buildWiresBT 6 (mkBase p_39 q_39 r_39) [(0,3,4),(1,2,5),(1,0,6),(1,1,6),(1,3,4),(3,2,9),(2,10,1),(2,10,0),(3,5,9),(2,13,1),(0,13,0),(0,0,9),(1,0,3),(0,17,4),(1,2,18),(2,0,6),(3,6,9),(1,0,5),(1,1,5),(1,1,3),(1,24,4),(3,1,25),(2,0,5),(0,10,0),(1,17,4),(3,0,29),(3,3,4),(2,3,4),(3,0,3),(1,33,1),(3,0,4),(1,35,3),(3,1,36),(3,1,29),(1,31,0),(2,39,1),(1,1,18),(3,1,3),(3,1,4),(1,43,3),(0,24,4),(1,1,4),(3,2,44),(3,2,29),(3,33,4),(1,42,4),(1,32,0),(2,17,4),(1,0,4),(3,1,53),(0,3,53),(3,24,4),(3,35,3),(3,3,53)]
lemma W_39_ok : btAll (fun x => faithful p_39 q_39 x ∧ x.1 < 2^64) W_39 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_39 : List (List (Nat × Nat)) := [[],[(0,1)]]
def A_39 : BT (List (Nat × Nat)) := btOfList 1 al_39
set_option maxHeartbeats 0 in
lemma A_39_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_39 = g_39) A_39 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_39_0 : Slice r_39 g_39 (subcubeFast 4 0) 6 := by
  have hc : Lower (varsOf 27) 0xffee8800ffee8800 6 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_39_1 : Slice r_39 g_39 (subcubeFast 3 0) 4 := by
  have hc : Lower (varsOf 28) 0xfff0f000fff0f000 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 3) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_39_2 : Slice r_39 g_39 (identDom 1 3) 5 := by
  have hc : Lower (varsOf 23) 0xfefec8c8fefec8c8 5 := carry_of (swaps := [(1,2),(3,4)]) (by decide +kernel) low_11
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_39_3 : Slice r_39 g_39 (identDom 0 3) 5 := by
  have hc : Lower (varsOf 23) 0xfefea8a8fefea8a8 5 := carry_of (swaps := [(0,2),(1,2),(3,4)]) (by decide +kernel) low_11
  exact slice_ident (u := 0) (v := 3) (by decide +kernel) hc
def S_39 : BT (Option (Nat × Nat)) := btOfList 2 [some (subcubeFast 4 0,6),some (subcubeFast 3 0,4),some (identDom 1 3,5),some (identDom 0 3,5)]
lemma S_39_ok : btAll (fun o => ∀ p, o = some p → Slice r_39 g_39 p.1 p.2) S_39 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_39_0) (forall_cons (fun _ h => by cases h; exact sl_39_1) (forall_cons (fun _ h => by cases h; exact sl_39_2) (forall_cons (fun _ h => by cases h; exact sl_39_3) (fun _ h => (List.not_mem_nil h).elim)))))
def ps_39 : BT (Option PoolSpec) := btOfList 5 [q 0 [16396,16397,36887],q 0 [16396,16397],q 0 [16398,16399],q 1 [],q 0 [],q 0 [16397,36871],q 0 [16385,217095],q 3 [],q 0 [16396,20485],q 0 [16397,36864],q 2 [],q 0 [12291,4229],q 0 [16396,20482],q 0 [16398],q 0 [16397],q 0 [16396],q 0 [16399],q 0 [16391],q 0 [16385],q 0 [12295],q 0 [12289]]
def B_39_1 : BT (List (List Nat)) := BT.empty
lemma B_39_1_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_39 1 xs.toFinset) B_39_1 := .empty
def U_39_2 : List Nat := []
def P_39_2 : BT (Option BoundPool) := buildPoolsSubBT 5 W_39 r_39 S_39 ps_39 U_39_2
def N_39_2 : List NodeSpec := [([7,8,9],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_39_2 : checkNodesBT W_39 g_39 F_39 P_39_2 A_39 B_39_1 2 N_39_2 = true := by decide +kernel
def B_39_2 : BT (List (List Nat)) := buildBucketsBT W_39 N_39_2
set_option maxRecDepth 500000 in
lemma B_39_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_39 2 xs.toFinset) B_39_2 :=
  buildBucketsBT_sound (by decide) gp_39 W_39_ok (buildPoolsSubBT_sound S_39_ok) A_39_ok B_39_1_ok C_39_2
def U_39_3 : List Nat := []
def P_39_3 : BT (Option BoundPool) := buildPoolsSubBT 5 W_39 r_39 S_39 ps_39 U_39_3
def N_39_3 : List NodeSpec := [([2,22,23,9],[],[]),([0,1,6,9],[],[]),([3,7,8,4],[],[0]),([27,1,6,9],[],[]),([16,1,6,9],[],[]),([26,0,6,9],[],[]),([27,13,1,2],[],[]),([21,0,1,9],[],[]),([13,0,2,23],[],[]),([0,23,6,9],[],[]),([13,26,0,2],[],[]),([11,12,3,4],[],[]),([13,0,1,6],[],[]),([21,13,0,1],[],[]),([20,1,6,9],[],[]),([0,1,19,9],[],[]),([0,6,8,9],[],[0]),([13,16,1,2],[],[]),([13,0,1,2],[],[]),([15,13,1,2],[],[]),([13,10,0,1],[],[]),([14,13,0,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_39_3 : checkNodesBT W_39 g_39 F_39 P_39_3 A_39 B_39_2 3 N_39_3 = true := by decide +kernel
def B_39_3 : BT (List (List Nat)) := buildBucketsBT W_39 N_39_3
set_option maxRecDepth 500000 in
lemma B_39_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_39 3 xs.toFinset) B_39_3 :=
  buildBucketsBT_sound (by decide) gp_39 W_39_ok (buildPoolsSubBT_sound S_39_ok) A_39_ok B_39_2_ok C_39_3
def U_39_4 : List Nat := [0,1]
def P_39_4 : BT (Option BoundPool) := buildPoolsSubBT 5 W_39 r_39 S_39 ps_39 U_39_4
def N_39_4 : List NodeSpec := [([13,0,1,2,9],[0],[0,1]),([13,0,1,2,5],[0],[0,1]),([13,0,1,2],[0],[0,1]),([0,1,6,9],[1],[0,1]),([27,2,3,23,4],[],[]),([10,16,1,3,4],[],[]),([13,0,1,2,3],[],[]),([10,0,1,5,9],[],[0]),([27,1,2,5,9],[],[0]),([26,0,2,3,4],[],[]),([0,1,2,18,9],[],[0]),([0,2,3,45,46],[],[]),([47,0,1,3,4],[],[]),([27,1,3,6,4],[],[0]),([0,2,23,4,9],[],[]),([32,31,0,1,2],[],[0]),([32,0,2,23,4],[],[]),([48,0,1,3,4],[],[]),([26,0,2,5,9],[],[0]),([32,0,49,1,2],[],[]),([0,2,5,23,9],[],[0]),([0,3,23,6,4],[],[0]),([20,1,3,6,4],[],[0]),([0,1,3,6,9],[],[]),([43,0,2,3,50],[],[]),([31,0,1,3,6],[],[0]),([32,0,1,6,4],[],[0]),([32,0,34,2,4],[],[]),([0,1,3,6,4],[],[0]),([28,10,1,3,4],[],[]),([10,26,0,3,4],[],[]),([26,30,2,3,4],[],[]),([31,13,0,1,2],[],[]),([26,16,2,3,4],[],[]),([16,1,2,5,9],[],[0]),([0,1,2,5,9],[],[0]),([0,1,5,6,9],[],[0,1]),([0,1,6,4,9],[],[]),([11,10,0,3,4],[],[0]),([42,0,2,44,4],[],[]),([0,34,2,4,9],[],[]),([37,0,2,3,4],[],[]),([2,3,22,23,4],[],[0]),([38,0,2,3,4],[],[]),([40,0,2,3,4],[],[]),([0,1,3,19,4],[],[0]),([13,0,1,2,4],[],[]),([0,3,6,8,4],[],[0]),([32,13,0,1,2],[],[]),([10,0,1,3,4],[],[]),([0,2,3,41,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_39_4 : checkNodesBT W_39 g_39 F_39 P_39_4 A_39 B_39_3 4 N_39_4 = true := by decide +kernel
def B_39_4 : BT (List (List Nat)) := buildBucketsBT W_39 N_39_4
set_option maxRecDepth 500000 in
lemma B_39_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_39 4 xs.toFinset) B_39_4 :=
  buildBucketsBT_sound (by decide) gp_39 W_39_ok (buildPoolsSubBT_sound S_39_ok) A_39_ok B_39_3_ok C_39_4
def U_39_5 : List Nat := (r 1 12)
def P_39_5 : BT (Option BoundPool) := buildPoolsSubBT 5 W_39 r_39 S_39 ps_39 U_39_5
def N_39_5 : List NodeSpec := [([0,1,2,5,9],[1],[0,1]),([32,31,0,1,2],[2],[0]),([0,1,2,17,4,9],[3],[0]),([42,43,0,2,3,4],[3],[0]),([54,0,2,3,4,53],[3],[]),([32,0,1,2,17,4],[3],[]),([43,0,2,3,4,46],[3],[]),u5 [49] [3],([32,42,0,1,2,4],[3],[1]),([42,0,1,2,4,9],[3],[1]),u5 [39] [3],a5 [29] [3,4] [0,1],a5 [44] [3,4] [0,1],a5 [9] [3,4] [0,1],([31,0,1,2,5,3],[4],[0]),([32,0,1,2,3,9],[4],[0]),([10,0,1,3,4,9],[4],[0,1]),([31,0,1,2,4,9],[4],[0]),([32,0,1,2,5,4],[4],[0,1]),([0,1,5,3,6,4],[4],[0,1]),([26,0,2,3,4,9],[3,5],[0]),([26,0,2,3,4],[5],[]),([54,0,2,3,4],[6],[]),e5 [55] [7],a5 [18] [7,3,4] [0,1],([0,2,3,23,4],[8],[0]),([0,2,5,3,23,4],[8,3],[0]),([16,1,2,3,4,9],[3,9],[0,1]),([0,2,3,24,4,46],[3,10],[0]),u5 [5] [7,3,10,4],([0,34,2,3,4],[11],[0]),([27,1,2,5,3,4],[7,3,12],[0]),u5 [50] [],e5 [58] [],e5 [52] [],([0,1,2,5,3,9],[],[0]),u5 [32] [],([32,31,0,1,2,4],[],[0]),([0,1,3,6,4],[],[0,1]),([0,1,2,5,4,9],[],[0,1]),e5 [56] [],e5 [57] [],e5 [22] [],e5 [51] [],u5 [31] [],e5 [26] [],([32,31,0,1,2,3],[],[0]),([10,0,1,3,4],[],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_39_5 : checkNodesBT W_39 g_39 F_39 P_39_5 A_39 B_39_4 5 N_39_5 = true := by decide +kernel
def B_39_5 : BT (List (List Nat)) := buildBucketsBT W_39 N_39_5
set_option maxRecDepth 500000 in
lemma B_39_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_39 5 xs.toFinset) B_39_5 :=
  buildBucketsBT_sound (by decide) gp_39 W_39_ok (buildPoolsSubBT_sound S_39_ok) A_39_ok B_39_4_ok C_39_5
def U_39_6 : List Nat := ([3,7,10]++r 13 8)
def P_39_6 : BT (Option BoundPool) := buildPoolsSubBT 5 W_39 r_39 S_39 ps_39 U_39_6
def N_39_6 : List NodeSpec := [a5 [32] [3,7,10,13] [0,1],a5 [9] [14,3] [0,1],a5 [5] [15,3,7,10] [0,1],a5 [31] [3,16] [0,1],a5 [43] [3,17,10] [0,1],a5 [53] [3,18,7] [0,1],a5 [42] [3,10,19] [0,1],a5 [17] [3,20,7] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_39_6 : checkNodesBT W_39 g_39 F_39 P_39_6 A_39 B_39_5 6 N_39_6 = true := by decide +kernel
def B_39_6 : BT (List (List Nat)) := buildBucketsBT W_39 N_39_6
set_option maxRecDepth 500000 in
lemma B_39_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_39 6 xs.toFinset) B_39_6 :=
  buildBucketsBT_sound (by decide) gp_39 W_39_ok (buildPoolsSubBT_sound S_39_ok) A_39_ok B_39_5_ok C_39_6
def U_39_7 : List Nat := [3,4]
def P_39_7 : BT (Option BoundPool) := buildPoolsSubBT 5 W_39 r_39 S_39 ps_39 U_39_7
def N_39_7 : List NodeSpec := [a5 [] [3,4] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_39_7 : checkNodesBT W_39 g_39 F_39 P_39_7 A_39 B_39_6 7 N_39_7 = true := by decide +kernel
def B_39_7 : BT (List (List Nat)) := buildBucketsBT W_39 N_39_7
set_option maxRecDepth 500000 in
lemma B_39_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_39 7 xs.toFinset) B_39_7 :=
  buildBucketsBT_sound (by decide) gp_39 W_39_ok (buildPoolsSubBT_sound S_39_ok) A_39_ok B_39_6_ok C_39_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_39_ok : forestRootCheck r_39 g_39 [(VAR 0,10,11),(VAR 1,9,11),(VAR 2,8,12),(VAR 3,3,11),(VAR 4,1,17)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_39_in : bucketContainsBT B_39_7 r_39 = true := by decide +kernel
lemma low_39 : Lower r_39 g_39 8 := lower_of_forestBT root_39_ok B_39_7_ok root_39_in
def g_40 := 0xfe08fe08fe08fe08
def r_40 : List Nat := varsOf 15
def p_40 : List Nat := [3,3,9,9,10,10,12,12,13,14,15]
def q_40 : List Nat := [2,1,8,1,8,2,8,4,5,6,7]
def F_40 : Nat := fullMask 11
set_option maxHeartbeats 0 in
lemma gp_40 : goodPairs g_40 p_40 q_40 := goodPairs_of (by decide +kernel)
def W_40 : BT Decor := buildWiresBT 6 (mkBase p_40 q_40 r_40) [(0,0,3),(1,1,2),(1,0,3),(0,5,6),(0,1,3),(1,1,3),(3,8,9),(1,0,2),(0,0,1),(1,0,1),(3,12,13),(1,14,2),(0,1,6),(1,16,2),(1,12,2),(0,11,3),(1,1,19),(0,5,3),(2,0,21),(3,8,0),(2,0,1),(3,0,1),(1,25,2),(3,4,1),(1,27,2),(1,8,0),(2,0,3),(3,0,3),(3,8,11),(1,30,2),(0,0,9),(3,2,6),(1,4,1),(2,11,3),(1,4,2),(3,1,3),(3,1,11),(0,0,5),(3,1,6),(1,24,2),(3,2,3)]
lemma W_40_ok : btAll (fun x => faithful p_40 q_40 x ∧ x.1 < 2^64) W_40 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_40 : List (List (Nat × Nat)) := [[],[(0,1)]]
def A_40 : BT (List (Nat × Nat)) := btOfList 1 al_40
set_option maxHeartbeats 0 in
lemma A_40_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_40 = g_40) A_40 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_40_0 : Slice r_40 g_40 (subcubeFast 4 0) 4 := by
  have hc : Lower (varsOf 11) 0xee88ee88ee88ee88 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_40_1 : Slice r_40 g_40 (subcubeFast 0 1) 2 := by
  have hc : Lower (varsOf 14) 0xff0cff0cff0cff0c 2 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_32
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_40_2 : Slice r_40 g_40 (subcubeFast 0 2) 2 := by
  have hc : Lower (varsOf 13) 0xff0aff0aff0aff0a 2 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_32
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_40_3 : Slice r_40 g_40 (subcubeFast 8 0) 2 := by
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) low_25
def S_40 : BT (Option (Nat × Nat)) := btOfList 2 [some (subcubeFast 4 0,4),some (subcubeFast 0 1,2),some (subcubeFast 0 2,2),some (subcubeFast 8 0,2)]
lemma S_40_ok : btAll (fun o => ∀ p, o = some p → Slice r_40 g_40 p.1 p.2) S_40 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_40_0) (forall_cons (fun _ h => by cases h; exact sl_40_1) (forall_cons (fun _ h => by cases h; exact sl_40_2) (forall_cons (fun _ h => by cases h; exact sl_40_3) (fun _ h => (List.not_mem_nil h).elim)))))
def ps_40 : BT (Option PoolSpec) := btOfList 2 [q 0 [],q 2 [],q 1 [],q 3 []]
def B_40_0 : BT (List (List Nat)) := BT.empty
lemma B_40_0_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_40 0 xs.toFinset) B_40_0 := .empty
def U_40_1 : List Nat := []
def P_40_1 : BT (Option BoundPool) := buildPoolsSubBT 2 W_40 r_40 S_40 ps_40 U_40_1
def N_40_1 : List NodeSpec := [([4,7],[],[]),([10,11],[],[]),([15,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_40_1 : checkNodesBT W_40 g_40 F_40 P_40_1 A_40 B_40_0 1 N_40_1 = true := by decide +kernel
def B_40_1 : BT (List (List Nat)) := buildBucketsBT W_40 N_40_1
set_option maxRecDepth 500000 in
lemma B_40_1_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_40 1 xs.toFinset) B_40_1 :=
  buildBucketsBT_sound (by decide) gp_40 W_40_ok (buildPoolsSubBT_sound S_40_ok) A_40_ok B_40_0_ok C_40_1
def U_40_2 : List Nat := []
def P_40_2 : BT (Option BoundPool) := buildPoolsSubBT 2 W_40 r_40 S_40 ps_40 U_40_2
def N_40_2 : List NodeSpec := [([0,17,3],[],[]),([13,18,3],[],[]),([11,20,3],[],[]),([22,5,3],[],[]),([23,5,3],[],[]),([24,26,3],[],[0]),([4,5,6],[],[0,1]),([0,7,3],[],[0]),([0,28,3],[],[]),([29,5,3],[],[]),([14,2,3],[],[0]),([30,31,5],[],[1]),([32,1,3],[],[]),([10,0,2],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_40_2 : checkNodesBT W_40 g_40 F_40 P_40_2 A_40 B_40_1 2 N_40_2 = true := by decide +kernel
def B_40_2 : BT (List (List Nat)) := buildBucketsBT W_40 N_40_2
set_option maxRecDepth 500000 in
lemma B_40_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_40 2 xs.toFinset) B_40_2 :=
  buildBucketsBT_sound (by decide) gp_40 W_40_ok (buildPoolsSubBT_sound S_40_ok) A_40_ok B_40_1_ok C_40_2
def U_40_3 : List Nat := [0,1,2]
def P_40_3 : BT (Option BoundPool) := buildPoolsSubBT 2 W_40 r_40 S_40 ps_40 U_40_3
def N_40_3 : List NodeSpec := [([0,1,33,3],[0],[]),([0,1,43,3],[0],[1]),([0,1,18,3],[0],[0]),([0,1,38,3],[0,1],[]),([4,0,5,3],[1],[0,1]),([0,5,3,6],[1],[0]),([41,0,5,3],[1],[]),([0,21,5,3],[1],[0,1]),([0,36,2,3],[1],[1]),([35,0,1,3],[1],[]),([34,1,2,3],[1],[1]),([42,0,2,3],[1,2],[]),([37,1,11,3],[2],[]),([12,0,5,3],[2],[]),([12,13,2,3],[2],[0]),([40,1,11,3],[2],[]),([30,31,1,2],[],[0,1]),([4,1,2,6],[],[0,1]),([23,1,2,3],[],[0,1]),([24,1,11,3],[],[]),([24,25,2,3],[],[0,1]),([39,1,11,3],[],[1]),([30,1,11,3],[],[]),([30,0,5,3],[],[0]),([4,1,11,3],[],[1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_40_3 : checkNodesBT W_40 g_40 F_40 P_40_3 A_40 B_40_2 3 N_40_3 = true := by decide +kernel
def B_40_3 : BT (List (List Nat)) := buildBucketsBT W_40 N_40_3
set_option maxRecDepth 500000 in
lemma B_40_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_40 3 xs.toFinset) B_40_3 :=
  buildBucketsBT_sound (by decide) gp_40 W_40_ok (buildPoolsSubBT_sound S_40_ok) A_40_ok B_40_2_ok C_40_3
def U_40_4 : List Nat := (r 0 4)
def P_40_4 : BT (Option BoundPool) := buildPoolsSubBT 2 W_40 r_40 S_40 ps_40 U_40_4
def N_40_4 : List NodeSpec := [([30,0,1,2,3],[0],[0]),([4,0,1,2,3],[0],[0,1]),([12,0,1,2,3],[0],[0,1]),([24,0,1,2,3],[0,1],[0]),([39,0,1,2,3],[1],[0,1]),([0,5,3],[1],[0,1]),([0,1,2,3,6],[2,0],[0,1]),([0,1,13,2,3],[2,1],[0]),([44,0,1,3],[2,1,0],[]),([0,1,11,3],[2,1,3],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_40_4 : checkNodesBT W_40 g_40 F_40 P_40_4 A_40 B_40_3 4 N_40_4 = true := by decide +kernel
def B_40_4 : BT (List (List Nat)) := buildBucketsBT W_40 N_40_4
set_option maxRecDepth 500000 in
lemma B_40_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_40 4 xs.toFinset) B_40_4 :=
  buildBucketsBT_sound (by decide) gp_40 W_40_ok (buildPoolsSubBT_sound S_40_ok) A_40_ok B_40_3_ok C_40_4
def U_40_5 : List Nat := [0]
def P_40_5 : BT (Option BoundPool) := buildPoolsSubBT 2 W_40 r_40 S_40 ps_40 U_40_5
def N_40_5 : List NodeSpec := [([0,1,2,3],[0],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_40_5 : checkNodesBT W_40 g_40 F_40 P_40_5 A_40 B_40_4 5 N_40_5 = true := by decide +kernel
def B_40_5 : BT (List (List Nat)) := buildBucketsBT W_40 N_40_5
set_option maxRecDepth 500000 in
lemma B_40_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_40 5 xs.toFinset) B_40_5 :=
  buildBucketsBT_sound (by decide) gp_40 W_40_ok (buildPoolsSubBT_sound S_40_ok) A_40_ok B_40_4_ok C_40_5
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_40_ok : forestRootCheck r_40 g_40 [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,3,7),(VAR 3,1,9)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_40_in : bucketContainsBT B_40_5 r_40 = true := by decide +kernel
lemma low_40 : Lower r_40 g_40 6 := lower_of_forestBT root_40_ok B_40_5_ok root_40_in
def g_41 := 0xf220f220f220f220
def r_41 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_41 : Lower r_41 g_41 5 := by
  have hc : Lower (varsOf 14) 0xf330f330f330f330 4 := carry_of (swaps := [(0,3),(1,2),(2,3)]) (by decide +kernel) low_22
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,4,5)]) (by decide +kernel) hc
def g_42 := 0xfffeffc8fce0c000
def r_42 : List Nat := varsOf 63
def p_42 : List Nat := [14,14,14,15,15,15,21,21,21,22,22,22,23,23,26,26,26,27,27,27,28,28,28,29,29,35,35,35,38,38,38,39,39,40,40,41,41,42,42,43,44,44,45,45,49,49,49,50,50,50,51,52,52,52,53,56,56,57]
def q_42 : List Nat := [12,10,6,13,11,7,20,17,5,20,18,6,19,7,24,18,10,25,19,11,24,20,12,25,13,34,33,3,36,34,6,37,7,32,8,33,9,34,10,11,36,12,37,13,48,33,17,48,34,18,19,48,36,20,37,48,24,25]
def F_42 : Nat := fullMask 58
set_option maxHeartbeats 0 in
lemma gp_42 : goodPairs g_42 p_42 q_42 := goodPairs_of (by decide +kernel)
def W_42 : BT Decor := buildWiresBT 10 (mkBase p_42 q_42 r_42) [(0,1,4),(1,3,5),(0,2,7),(1,6,8),(1,1,4),(1,2,7),(0,10,11),(3,8,11),(3,6,10),(2,1,4),(3,1,4),(3,15,11),(0,10,7),(0,2,18),(1,2,18),(3,19,20),(3,8,10),(0,4,11),(0,22,11),(3,6,7),(0,25,2),(1,25,2),(3,26,27),(1,1,2),(0,29,7),(0,30,4),(1,30,4),(3,31,32),(1,2,3),(2,34,5),(2,2,7),(3,2,7),(2,2,3),(1,2,5),(0,10,39),(3,38,40),(1,6,5),(3,3,42),(1,6,2),(1,38,5),(3,0,45),(3,3,39),(2,2,5),(1,48,3),(1,1,23),(3,8,50),(1,3,4),(0,29,52),(0,53,5),(1,53,5),(3,54,55),(1,3,40),(3,6,57),(0,52,39),(0,1,59),(1,1,59),(3,60,61),(2,57,5),(2,1,59),(3,1,59),(2,1,23),(3,2,5),(2,14,0),(1,38,6),(1,67,3),(3,16,7),(2,44,5),(3,0,40),(1,73,3),(2,44,3),(3,3,5),(2,53,5),(3,53,5),(1,0,3),(0,79,40),(1,0,6),(0,2,42),(1,1,5),(0,52,83),(3,2,84),(0,1,5),(3,1,7),(3,6,11),(0,4,5),(3,89,4),(3,4,5),(0,1,2),(3,92,29),(1,76,6),(2,30,4),(3,30,4),(1,38,42),(1,3,89),(1,92,89),(1,3,99),(0,2,4),(1,86,101),(1,102,3),(0,2,5),(1,6,104),(3,105,79),(3,3,55),(2,2,42),(1,104,3),(1,6,3),(1,104,110),(1,75,5),(3,6,49),(0,44,7),(3,38,42),(1,48,6),(0,1,7),(2,1,31),(3,3,40),(1,0,109),(3,6,120),(2,25,2),(3,25,2),(3,15,7),(1,123,3),(1,123,5),(1,87,6),(1,36,117),(3,8,4),(3,36,10),(1,36,18),(2,2,18),(3,2,18),(3,6,109),(1,0,105),(2,135,3),(1,2,84),(1,2,4),(0,138,7),(3,1,139),(1,36,15),(1,1,139),(1,4,7),(0,2,143),(0,4,7),(3,4,7),(3,1,11),(1,2,145),(3,146,1),(3,2,143),(3,87,4),(1,1,7),(3,146,152),(3,36,4),(0,4,152),(1,117,2),(0,1,52),(1,157,104),(3,2,4),(1,159,117),(3,159,1),(3,161,7),(3,117,4),(0,1,138),(3,164,7),(3,145,143),(1,117,101),(0,1,34),(1,168,89),(3,1,5),(1,101,5),(3,0,171),(3,170,171),(1,170,3),(3,86,1),(1,175,0),(2,176,3),(1,175,3),(0,4,83),(0,138,83),(3,3,180),(1,3,180),(3,86,83),(2,47,0),(3,15,39),(0,34,4),(1,86,186),(1,1,145),(1,15,104),(3,87,138),(3,3,4),(0,29,4),(2,191,5),(1,193,117),(3,6,5),(3,4,11),(3,48,10),(0,4,39),(3,6,39),(2,81,3),(0,29,98),(3,146,29),(2,29,145),(3,159,7),(0,2,98),(1,1,3),(0,206,4),(1,104,207),(1,4,5),(3,3,83),(1,3,42),(0,1,98),(2,1,3),(1,213,4),(3,48,214),(3,48,4),(1,16,3),(0,1,171),(1,48,15),(3,159,83),(3,6,2),(1,195,3),(3,192,7),(1,72,3),(1,159,86),(0,29,209),(1,226,3),(3,213,5),(1,170,101),(2,29,3),(1,230,5),(1,15,8),(2,1,2),(3,233,4),(1,234,3),(1,92,5),(3,91,236),(1,191,1),(3,48,238),(3,6,79),(3,1,2),(3,175,206),(1,159,170),(1,92,3),(1,0,244),(3,3,245),(1,3,198),(2,226,3),(1,233,145),(1,86,3),(3,175,4),(1,3,251),(3,92,98),(0,52,236),(1,91,3),(1,101,228),(1,48,110),(3,92,7),(3,3,138),(1,259,5),(3,76,44),(1,38,195),(3,233,7),(1,36,6),(3,170,138),(3,6,45),(0,6,7),(1,92,145),(1,159,87),(3,3,10),(1,270,5),(3,91,1),(1,272,3),(0,1,209),(1,274,3),(1,90,3),(3,2,98),(3,1,143),(0,1,143),(3,3,209),(3,90,1),(1,281,3),(0,1,11),(2,1,8),(2,213,5),(3,191,209),(1,191,5),(3,0,287),(2,238,5),(3,90,52),(3,67,4),(3,67,1),(1,292,3),(3,285,4),(3,48,52),(3,48,1),(3,191,39),(0,1,39),(1,191,104),(3,104,4),(1,300,3),(2,1,104),(1,302,3),(1,159,3),(1,304,5),(1,161,5),(1,161,3),(2,2,4),(3,308,7),(1,308,5),(3,3,310),(1,308,3),(2,312,5),(3,308,1),(1,314,5),(1,314,3),(2,138,5),(1,317,3),(3,76,138),(1,191,2),(2,320,5),(1,164,3),(3,101,7),(3,1,171),(1,101,3),(2,325,5),(1,325,5),(2,1,101),(1,328,5),(1,328,3),(1,91,38),(1,90,38),(3,38,209),(3,38,4),(1,334,5),(3,38,1),(1,159,5),(3,3,337),(1,336,5),(3,91,34),(0,34,209),(1,186,5),(3,191,1),(1,343,5),(1,191,170),(3,170,52),(1,308,170),(1,38,170),(3,170,34),(3,170,4),(1,298,3),(2,52,5),(1,175,159),(1,175,101),(1,175,38),(3,175,34),(3,193,1),(3,101,83),(3,38,83),(2,206,5),(1,15,3),(1,38,86),(1,360,0),(3,67,206),(3,104,206),(3,159,206),(1,233,3),(2,367,5),(1,90,241),(1,207,5),(1,191,86),(1,308,86),(1,191,241),(3,233,52),(3,241,4),(1,213,5),(1,233,89),(3,16,34),(1,191,233),(1,350,3),(1,90,233),(1,375,3),(1,15,5),(2,280,0),(3,241,7),(3,91,29),(3,76,29),(3,241,52),(1,241,3),(2,389,5),(1,213,2),(0,391,4),(2,29,89),(1,90,1),(2,394,3),(2,1,89),(0,206,209),(2,29,5),(3,1,98),(1,241,5),(3,90,34),(1,192,5),(0,213,4),(1,15,38),(1,91,233),(3,92,52),(2,206,89),(2,34,89),(3,86,4),(3,48,206),(3,308,206),(3,3,171),(1,312,5),(1,398,3),(3,233,209),(1,291,3),(1,244,5),(3,3,383),(3,2,10),(3,101,206),(1,241,89),(1,168,5),(3,92,209),(1,192,3),(3,3,400),(1,90,92),(1,233,5),(1,234,5),(0,34,83),(3,213,209),(1,396,3),(1,164,5),(3,213,4),(3,191,29),(3,0,400),(3,241,209),(2,304,5),(2,6,5),(1,175,308),(1,375,5),(0,206,39),(3,92,4),(2,391,5),(2,10,5),(1,90,213),(3,191,83),(0,4,236),(1,91,241),(0,206,138),(3,90,206),(0,2,10),(1,191,67),(1,442,5),(1,16,5),(3,3,236),(1,367,5),(3,90,29),(3,175,79),(3,36,1),(1,191,92),(1,442,3),(3,175,138),(3,6,34),(1,76,92),(1,91,92),(1,403,5),(2,214,5),(1,433,5),(2,217,5),(3,91,206),(3,4,236),(3,228,4),(1,213,101),(3,175,52),(3,213,83),(1,308,213),(1,213,159),(3,213,39),(1,48,213),(1,213,67),(1,308,76),(1,3,179),(1,296,3),(1,389,5),(3,3,454),(1,76,159),(2,244,5),(1,3,216),(1,48,191),(1,0,110),(2,270,5),(2,110,5),(1,76,233),(1,157,5),(1,48,16),(2,230,5),(1,76,241),(1,438,3),(1,76,101),(1,38,89),(3,67,10),(3,104,52),(0,34,10),(3,213,138),(1,67,6),(1,213,104),(2,259,5),(1,15,76),(1,0,178),(3,38,10),(3,104,10),(2,270,0),(3,308,83),(3,76,10),(1,444,3),(1,0,312),(1,361,5),(1,213,89),(2,361,5),(3,15,34),(1,175,191),(3,67,52),(1,15,67),(1,217,5),(3,16,39),(3,0,454),(1,38,16),(1,16,104),(3,3,427),(1,67,16),(1,91,213),(1,76,16),(1,409,3),(3,86,34),(3,86,138),(3,86,52),(3,90,2),(3,76,4),(3,76,1),(3,191,5),(3,213,2),(3,191,2),(1,175,4),(1,175,2),(3,175,2),(1,90,2)]
lemma W_42_ok : btAll (fun x => faithful p_42 q_42 x ∧ x.1 < 2^64) W_42 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_42 : List (List (Nat × Nat)) := [[]]
def A_42 : BT (List (Nat × Nat)) := btOfList 1 al_42
set_option maxHeartbeats 0 in
lemma A_42_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_42 = g_42) A_42 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_42_0 : Slice r_42 g_42 (subcubeFast 1 0) 10 := by
  have hc : Lower (varsOf 62) 0xfffcffc0fcc0c000 10 := carry_of (swaps := [(0,5),(1,5),(2,5),(4,5)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_1 : Slice r_42 g_42 (subcubeFast 8 0) 9 := by
  have hc : Lower (varsOf 55) 0xfefec8c8e0e00000 9 := carry_of (swaps := [(3,5),(4,5)]) (by decide +kernel) low_10
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_2 : Slice r_42 g_42 (subcubeFast 0 1) 9 := by
  have hc : Lower (varsOf 62) 0xffffffccfcf0c000 9 := carry_of (swaps := [(0,5),(1,5),(3,5),(4,5)]) (by decide +kernel) low_12
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_3 : Slice r_42 g_42 (subcubeFast 0 16) 8 := by
  have hc : Lower (varsOf 47) 0xfffefffefce0fce0 8 := carry_of (swaps := [(2,3),(4,5)]) (by decide +kernel) low_13
  exact slice_fast_direct_f (z := 0) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_4 : Slice r_42 g_42 (subcubeFast 32 0) 8 := by
  have hc : Lower (varsOf 31) 0xfce0c000fce0c000 8 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_14
  exact slice_fast_direct_f (z := 32) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_5 : Slice r_42 g_42 (subcubeFast 0 4) 8 := by
  have hc : Lower (varsOf 59) 0xffffffccffeecc00 8 := carry_of (swaps := [(2,5),(3,5)]) (by decide +kernel) low_15
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_6 : Slice r_42 g_42 (subcubeFast 0 2) 8 := by
  have hc : Lower (varsOf 61) 0xfffffffafff0f000 8 := carry_of (swaps := [(1,5),(2,5),(3,5),(4,5)]) (by decide +kernel) low_15
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_7 : Slice r_42 g_42 (subcubeFast 1 2) 7 := by
  have hc : Lower (varsOf 60) 0xfffffff0fff0f000 7 := carry_of (swaps := [(0,4),(1,5),(2,4),(3,5)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 1) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_8 : Slice r_42 g_42 (subcubeFast 33 0) 7 := by
  have hc : Lower (varsOf 30) 0xfcc0c000fcc0c000 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 33) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_9 : Slice r_42 g_42 (subcubeFast 1 4) 7 := by
  have hc : Lower (varsOf 58) 0xffffffccffcccc00 7 := carry_of (swaps := [(0,4),(1,4),(2,5),(3,4),(4,5)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 1) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_10 : Slice r_42 g_42 (subcubeFast 1 16) 7 := by
  have hc : Lower (varsOf 46) 0xfffcfffcfcc0fcc0 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4),(4,5)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 1) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_11 : Slice r_42 g_42 (subcubeFast 9 0) 7 := by
  have hc : Lower (varsOf 54) 0xfcfcc0c0c0c00000 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,5)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 9) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_12 : Slice r_42 g_42 (subcubeFast 4 0) 8 := by
  have hc : Lower (varsOf 59) 0xffeeff88cc000000 8 := carry_of (swaps := [(2,5),(4,5)]) (by decide +kernel) low_16
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_13 : Slice r_42 g_42 (subcubeFast 2 0) 7 := by
  have hc : Lower (varsOf 61) 0xfffaff00f0a00000 7 := carry_of (swaps := [(1,5),(2,5),(3,5),(4,5)]) (by decide +kernel) low_18
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_14 : Slice r_42 g_42 (fiDom 0 2 0 2 false) 7 := by
  have hc : Lower (varsOf 57) 0xffffffaaffaaaa00 7 := carry_of (swaps := [(1,4),(2,5),(3,4),(4,5)]) (by decide +kernel) low_1
  exact slice_fi (z := 0) (o := 2) (u := 0) (v := 2) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_15 : Slice r_42 g_42 (fiDom 0 4 0 1 false) 7 := by
  have hc : Lower (varsOf 57) 0xffffffaaffaaaa00 7 := carry_of (swaps := [(1,4),(2,5),(3,4),(4,5)]) (by decide +kernel) low_1
  exact slice_fi (z := 0) (o := 4) (u := 0) (v := 1) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_16 : Slice r_42 g_42 (fiDom 0 16 0 1 false) 7 := by
  have hc : Lower (varsOf 45) 0xfffafffafaa0faa0 7 := carry_of (swaps := [(1,4),(2,4),(3,4),(4,5)]) (by decide +kernel) low_1
  exact slice_fi (z := 0) (o := 16) (u := 0) (v := 1) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_17 : Slice r_42 g_42 (fiDom 32 0 0 1 false) 7 := by
  have hc : Lower (varsOf 29) 0xfaa0a000faa0a000 7 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_fi (z := 32) (o := 0) (u := 0) (v := 1) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_18 : Slice r_42 g_42 (subcubeFast 16 0) 7 := by
  have hc : Lower (varsOf 47) 0xffc8ffc8c000c000 7 := carry_of (swaps := [(1,2),(4,5)]) (by decide +kernel) low_19
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_19 : Slice r_42 g_42 (identDom 1 3) 8 := by
  have hc : Lower (varsOf 55) 0xfefeccccececc0c0 8 := carry_of (swaps := [(1,4),(2,4),(3,5),(4,5)]) (by decide +kernel) low_20
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_20 : Slice r_42 g_42 (subcubeFast 4 1) 6 := by
  have hc : Lower (varsOf 58) 0xffffffcccc000000 6 := carry_of (swaps := [(0,4),(1,4),(2,5),(3,4),(4,5)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 4) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_21 : Slice r_42 g_42 (fiDom 0 2 0 5 true) 7 := by
  have hc : Lower (varsOf 29) 0xfff5f550fff5f550 7 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_24
  exact slice_fi (z := 0) (o := 2) (u := 0) (v := 5) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_22 : Slice r_42 g_42 (fiDom 0 4 0 4 true) 7 := by
  have hc : Lower (varsOf 43) 0xffddffdddd44dd44 7 := carry_of (swaps := [(0,3),(1,3),(2,4),(4,5)]) (by decide +kernel) low_24
  exact slice_fi (z := 0) (o := 4) (u := 0) (v := 4) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_23 : Slice r_42 g_42 (fiDom 32 0 0 4 true) 7 := by
  have hc : Lower (varsOf 15) 0xd440d440d440d440 7 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_26
  exact slice_fi (z := 32) (o := 0) (u := 0) (v := 4) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_24 : Slice r_42 g_42 (fiDom 0 0 2 5 true) 8 := by
  have hc : Lower (varsOf 31) 0xffeecf08ffeecf08 8 := carry_of (swaps := [(1,2),(3,4)]) (by decide +kernel) low_33
  exact slice_fi (z := 0) (o := 0) (u := 2) (v := 5) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_25 : Slice r_42 g_42 (fiDom 0 0 4 5 true) 8 := by
  have hc : Lower (varsOf 31) 0xfce0ffc8fce0ffc8 8 := carry_of (swaps := [(1,3),(3,4)]) (by decide +kernel) low_38
  exact slice_fi (z := 0) (o := 0) (u := 4) (v := 5) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_26 : Slice r_42 g_42 (identDom 2 4) 8 := by
  have hc : Lower (varsOf 47) 0xfff8fff8f0e0f0e0 8 := carry_of (swaps := [(2,4),(3,4),(4,5)]) (by decide +kernel) low_39
  exact slice_ident (u := 2) (v := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_27 : Slice r_42 g_42 (subcubeFast 3 4) 4 := by
  have hc : Lower (varsOf 56) 0xffffff00ff000000 4 := carry_of (swaps := [(0,3),(1,4),(2,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 3) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_28 : Slice r_42 g_42 (subcubeFast 12 32) 4 := by
  have hc : Lower (varsOf 19) 0xeeee8888eeee8888 4 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 12) (o := 32) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_29 : Slice r_42 g_42 (subcubeFast 10 16) 4 := by
  have hc : Lower (varsOf 37) 0xfafafafaa0a0a0a0 4 := carry_of (swaps := [(1,3),(2,3),(3,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 10) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_30 : Slice r_42 g_42 (subcubeFast 5 2) 4 := by
  have hc : Lower (varsOf 56) 0xffffff00ff000000 4 := carry_of (swaps := [(0,3),(1,4),(2,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 5) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_31 : Slice r_42 g_42 (subcubeFast 33 16) 4 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 33) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_32 : Slice r_42 g_42 (subcubeFast 9 2) 4 := by
  have hc : Lower (varsOf 52) 0xfffff0f0f0f00000 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 9) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_33 : Slice r_42 g_42 (subcubeFast 17 2) 4 := by
  have hc : Lower (varsOf 44) 0xfff0fff0f000f000 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 17) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_34 : Slice r_42 g_42 (subcubeFast 32 3) 4 := by
  have hc : Lower (varsOf 28) 0xfff0f000fff0f000 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 32) (o := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_35 : Slice r_42 g_42 (subcubeFast 9 4) 4 := by
  have hc : Lower (varsOf 50) 0xffffcccccccc0000 4 := carry_of (swaps := [(0,3),(1,3),(2,4),(3,5),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 9) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_36 : Slice r_42 g_42 (subcubeFast 17 4) 4 := by
  have hc : Lower (varsOf 42) 0xffccffcccc00cc00 4 := carry_of (swaps := [(0,3),(1,3),(2,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 17) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_37 : Slice r_42 g_42 (subcubeFast 16 5) 4 := by
  have hc : Lower (varsOf 42) 0xffccffcccc00cc00 4 := carry_of (swaps := [(0,3),(1,3),(2,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 5) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_38 : Slice r_42 g_42 (subcubeFast 5 16) 4 := by
  have hc : Lower (varsOf 42) 0xffccffcccc00cc00 4 := carry_of (swaps := [(0,3),(1,3),(2,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 5) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_39 : Slice r_42 g_42 (subcubeFast 33 4) 4 := by
  have hc : Lower (varsOf 26) 0xffcccc00ffcccc00 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 33) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_40 : Slice r_42 g_42 (subcubeFast 9 16) 4 := by
  have hc : Lower (varsOf 38) 0xfcfcfcfcc0c0c0c0 4 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 9) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_41 : Slice r_42 g_42 (subcubeFast 33 8) 4 := by
  have hc : Lower (varsOf 22) 0xfcfcc0c0fcfcc0c0 4 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 33) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_42 : Slice r_42 g_42 (subcubeFast 32 9) 4 := by
  have hc : Lower (varsOf 22) 0xfcfcc0c0fcfcc0c0 4 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 32) (o := 9) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_43 : Slice r_42 g_42 (subcubeFast 9 32) 4 := by
  have hc : Lower (varsOf 22) 0xfcfcc0c0fcfcc0c0 4 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 9) (o := 32) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_44 : Slice r_42 g_42 (fiDom 0 1 4 5 true) 6 := by
  have hc : Lower (varsOf 30) 0xfcf0ffccfcf0ffcc 6 := carry_of (swaps := [(0,4),(2,4),(3,4)]) (by decide +kernel) low_35
  exact slice_fi (z := 0) (o := 1) (u := 4) (v := 5) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_45 : Slice r_42 g_42 (fiDom 0 1 2 5 false) 6 := by
  have hc : Lower (varsOf 30) 0xfcf0f0c0fcf0f0c0 6 := carry_of (swaps := [(0,4),(1,4),(2,3),(3,4)]) (by decide +kernel) low_7
  exact slice_fi (z := 0) (o := 1) (u := 2) (v := 5) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_46 : Slice r_42 g_42 (fiDom 8 0 1 5 false) 6 := by
  have hc : Lower (varsOf 23) 0xececc8c8ececc8c8 6 := carry_of (swaps := [(1,3),(2,3),(3,4)]) (by decide +kernel) low_7
  exact slice_fi (z := 8) (o := 0) (u := 1) (v := 5) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_47 : Slice r_42 g_42 (fiDom 8 0 2 4 false) 6 := by
  have hc : Lower (varsOf 39) 0xf8f8f8f8e0e0e0e0 6 := carry_of (swaps := [(2,3),(3,4),(4,5)]) (by decide +kernel) low_7
  exact slice_fi (z := 8) (o := 0) (u := 2) (v := 4) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_48 : Slice r_42 g_42 (fiDom 1 0 4 5 false) 6 := by
  have hc : Lower (varsOf 30) 0xfffcc000fffcc000 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_7
  exact slice_fi (z := 1) (o := 0) (u := 4) (v := 5) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_49 : Slice r_42 g_42 (fiDom 1 0 3 4 false) 6 := by
  have hc : Lower (varsOf 46) 0xffc0ffc0fc00fc00 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(4,5)]) (by decide +kernel) low_7
  exact slice_fi (z := 1) (o := 0) (u := 3) (v := 4) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_50 : Slice r_42 g_42 (fiDom 2 0 3 4 true) 6 := by
  have hc : Lower (varsOf 45) 0xfffafffa00a000a0 6 := carry_of (swaps := [(1,4),(2,4),(3,4),(4,5)]) (by decide +kernel) low_40
  exact slice_fi (z := 2) (o := 0) (u := 3) (v := 4) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_51 : Slice r_42 g_42 (fiDom 16 0 2 5 true) 5 := by
  exact slice_fi (z := 16) (o := 0) (u := 2) (v := 5) (fl := true) (by decide +kernel) low_28
set_option maxHeartbeats 0 in
lemma sl_42_52 : Slice r_42 g_42 (fiDom 16 0 2 3 false) 5 := by
  have hc : Lower (varsOf 39) 0xf8f8f8f8c0c0c0c0 5 := carry_of (swaps := [(2,3),(3,4),(4,5)]) (by decide +kernel) low_8
  exact slice_fi (z := 16) (o := 0) (u := 2) (v := 3) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_53 : Slice r_42 g_42 (fiDom 2 0 2 4 false) 5 := by
  have hc : Lower (varsOf 45) 0xfff0fff0f0a0f0a0 5 := carry_of (swaps := [(1,4),(2,3),(3,4),(4,5)]) (by decide +kernel) low_6
  exact slice_fi (z := 2) (o := 0) (u := 2) (v := 4) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_54 : Slice r_42 g_42 (fiDom 1 0 1 4 false) 5 := by
  have hc : Lower (varsOf 46) 0xffccffccccc0ccc0 5 := carry_of (swaps := [(0,4),(1,3),(2,4),(4,5)]) (by decide +kernel) low_6
  exact slice_fi (z := 1) (o := 0) (u := 1) (v := 4) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_55 : Slice r_42 g_42 (fiDom 4 0 4 5 true) 5 := by
  have hc : Lower (varsOf 27) 0xcc00ff88cc00ff88 5 := carry_of (swaps := [(2,4)]) (by decide +kernel) low_28
  exact slice_fi (z := 4) (o := 0) (u := 4) (v := 5) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_56 : Slice r_42 g_42 (fiDom 4 0 3 5 true) 5 := by
  have hc : Lower (varsOf 27) 0xccee0088ccee0088 5 := carry_of (swaps := [(1,2),(2,4),(3,4)]) (by decide +kernel) low_41
  exact slice_fi (z := 4) (o := 0) (u := 3) (v := 5) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_57 : Slice r_42 g_42 (fiDom 4 0 3 4 false) 5 := by
  have hc : Lower (varsOf 43) 0xff88ff88cc00cc00 5 := carry_of (swaps := [(2,4),(4,5)]) (by decide +kernel) low_8
  exact slice_fi (z := 4) (o := 0) (u := 3) (v := 4) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_58 : Slice r_42 g_42 (fiDom 4 0 1 5 true) 5 := by
  have hc : Lower (varsOf 27) 0xff223300ff223300 5 := carry_of (swaps := [(1,2),(2,4)]) (by decide +kernel) low_28
  exact slice_fi (z := 4) (o := 0) (u := 1) (v := 5) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_59 : Slice r_42 g_42 (fiDom 4 0 1 3 false) 5 := by
  have hc : Lower (varsOf 51) 0xeeeecccccccc0000 5 := carry_of (swaps := [(1,3),(2,4),(3,5),(4,5)]) (by decide +kernel) low_8
  exact slice_fi (z := 4) (o := 0) (u := 1) (v := 3) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_60 : Slice r_42 g_42 (fiDom 2 0 2 3 false) 5 := by
  have hc : Lower (varsOf 53) 0xfafaf0f0f0f00000 5 := carry_of (swaps := [(1,4),(2,3),(3,5)]) (by decide +kernel) low_8
  exact slice_fi (z := 2) (o := 0) (u := 2) (v := 3) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_61 : Slice r_42 g_42 (fiDom 8 0 1 4 true) 5 := by
  have hc : Lower (varsOf 39) 0xfafafafa20202020 5 := carry_of (swaps := [(0,1),(3,4),(4,5)]) (by decide +kernel) low_29
  exact slice_fi (z := 8) (o := 0) (u := 1) (v := 4) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_62 : Slice r_42 g_42 (fiDom 8 0 1 2 false) 5 := by
  have hc : Lower (varsOf 51) 0xeeeecccccccc0000 5 := carry_of (swaps := [(1,3),(2,4),(3,5),(4,5)]) (by decide +kernel) low_8
  exact slice_fi (z := 8) (o := 0) (u := 1) (v := 2) (fl := false) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_63 : Slice r_42 g_42 (fiDom 8 0 1 2 true) 5 := by
  have hc : Lower (varsOf 51) 0xffff888822220000 5 := carry_of (swaps := [(2,4),(3,5),(4,5)]) (by decide +kernel) low_36
  exact slice_fi (z := 8) (o := 0) (u := 1) (v := 2) (fl := true) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_42_64 : Slice r_42 g_42 (fiDom 8 0 4 5 true) 5 := by
  have hc : Lower (varsOf 23) 0xe0e0c8c8e0e0c8c8 5 := carry_of (swaps := [(1,3),(3,4)]) (by decide +kernel) low_36
  exact slice_fi (z := 8) (o := 0) (u := 4) (v := 5) (fl := true) (by decide +kernel) hc
def S_42 : BT (Option (Nat × Nat)) := btOfList 7 [some (subcubeFast 1 0,10),some (subcubeFast 8 0,9),some (subcubeFast 0 1,9),some (subcubeFast 0 16,8),some (subcubeFast 32 0,8),some (subcubeFast 0 4,8),some (subcubeFast 0 2,8),some (subcubeFast 1 2,7),some (subcubeFast 33 0,7),some (subcubeFast 1 4,7),some (subcubeFast 1 16,7),some (subcubeFast 9 0,7),some (subcubeFast 4 0,8),some (subcubeFast 2 0,7),some (fiDom 0 2 0 2 false,7),some (fiDom 0 4 0 1 false,7),some (fiDom 0 16 0 1 false,7),some (fiDom 32 0 0 1 false,7),some (subcubeFast 16 0,7),some (identDom 1 3,8),some (subcubeFast 4 1,6),some (fiDom 0 2 0 5 true,7),some (fiDom 0 4 0 4 true,7),some (fiDom 32 0 0 4 true,7),some (fiDom 0 0 2 5 true,8),some (fiDom 0 0 4 5 true,8),some (identDom 2 4,8),some (subcubeFast 3 4,4),some (subcubeFast 12 32,4),some (subcubeFast 10 16,4),some (subcubeFast 5 2,4),some (subcubeFast 33 16,4),some (subcubeFast 9 2,4),some (subcubeFast 17 2,4),some (subcubeFast 32 3,4),some (subcubeFast 9 4,4),some (subcubeFast 17 4,4),some (subcubeFast 16 5,4),some (subcubeFast 5 16,4),some (subcubeFast 33 4,4),some (subcubeFast 9 16,4),some (subcubeFast 33 8,4),some (subcubeFast 32 9,4),some (subcubeFast 9 32,4),some (fiDom 0 1 4 5 true,6),some (fiDom 0 1 2 5 false,6),some (fiDom 8 0 1 5 false,6),some (fiDom 8 0 2 4 false,6),some (fiDom 1 0 4 5 false,6),some (fiDom 1 0 3 4 false,6),some (fiDom 2 0 3 4 true,6),some (fiDom 16 0 2 5 true,5),some (fiDom 16 0 2 3 false,5),some (fiDom 2 0 2 4 false,5),some (fiDom 1 0 1 4 false,5),some (fiDom 4 0 4 5 true,5),some (fiDom 4 0 3 5 true,5),some (fiDom 4 0 3 4 false,5),some (fiDom 4 0 1 5 true,5),some (fiDom 4 0 1 3 false,5),some (fiDom 2 0 2 3 false,5),some (fiDom 8 0 1 4 true,5),some (fiDom 8 0 1 2 false,5),some (fiDom 8 0 1 2 true,5),some (fiDom 8 0 4 5 true,5)]
lemma S_42_ok : btAll (fun o => ∀ p, o = some p → Slice r_42 g_42 p.1 p.2) S_42 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_42_0) (forall_cons (fun _ h => by cases h; exact sl_42_1) (forall_cons (fun _ h => by cases h; exact sl_42_2) (forall_cons (fun _ h => by cases h; exact sl_42_3) (forall_cons (fun _ h => by cases h; exact sl_42_4) (forall_cons (fun _ h => by cases h; exact sl_42_5) (forall_cons (fun _ h => by cases h; exact sl_42_6) (forall_cons (fun _ h => by cases h; exact sl_42_7) (forall_cons (fun _ h => by cases h; exact sl_42_8) (forall_cons (fun _ h => by cases h; exact sl_42_9) (forall_cons (fun _ h => by cases h; exact sl_42_10) (forall_cons (fun _ h => by cases h; exact sl_42_11) (forall_cons (fun _ h => by cases h; exact sl_42_12) (forall_cons (fun _ h => by cases h; exact sl_42_13) (forall_cons (fun _ h => by cases h; exact sl_42_14) (forall_cons (fun _ h => by cases h; exact sl_42_15) (forall_cons (fun _ h => by cases h; exact sl_42_16) (forall_cons (fun _ h => by cases h; exact sl_42_17) (forall_cons (fun _ h => by cases h; exact sl_42_18) (forall_cons (fun _ h => by cases h; exact sl_42_19) (forall_cons (fun _ h => by cases h; exact sl_42_20) (forall_cons (fun _ h => by cases h; exact sl_42_21) (forall_cons (fun _ h => by cases h; exact sl_42_22) (forall_cons (fun _ h => by cases h; exact sl_42_23) (forall_cons (fun _ h => by cases h; exact sl_42_24) (forall_cons (fun _ h => by cases h; exact sl_42_25) (forall_cons (fun _ h => by cases h; exact sl_42_26) (forall_cons (fun _ h => by cases h; exact sl_42_27) (forall_cons (fun _ h => by cases h; exact sl_42_28) (forall_cons (fun _ h => by cases h; exact sl_42_29) (forall_cons (fun _ h => by cases h; exact sl_42_30) (forall_cons (fun _ h => by cases h; exact sl_42_31) (forall_cons (fun _ h => by cases h; exact sl_42_32) (forall_cons (fun _ h => by cases h; exact sl_42_33) (forall_cons (fun _ h => by cases h; exact sl_42_34) (forall_cons (fun _ h => by cases h; exact sl_42_35) (forall_cons (fun _ h => by cases h; exact sl_42_36) (forall_cons (fun _ h => by cases h; exact sl_42_37) (forall_cons (fun _ h => by cases h; exact sl_42_38) (forall_cons (fun _ h => by cases h; exact sl_42_39) (forall_cons (fun _ h => by cases h; exact sl_42_40) (forall_cons (fun _ h => by cases h; exact sl_42_41) (forall_cons (fun _ h => by cases h; exact sl_42_42) (forall_cons (fun _ h => by cases h; exact sl_42_43) (forall_cons (fun _ h => by cases h; exact sl_42_44) (forall_cons (fun _ h => by cases h; exact sl_42_45) (forall_cons (fun _ h => by cases h; exact sl_42_46) (forall_cons (fun _ h => by cases h; exact sl_42_47) (forall_cons (fun _ h => by cases h; exact sl_42_48) (forall_cons (fun _ h => by cases h; exact sl_42_49) (forall_cons (fun _ h => by cases h; exact sl_42_50) (forall_cons (fun _ h => by cases h; exact sl_42_51) (forall_cons (fun _ h => by cases h; exact sl_42_52) (forall_cons (fun _ h => by cases h; exact sl_42_53) (forall_cons (fun _ h => by cases h; exact sl_42_54) (forall_cons (fun _ h => by cases h; exact sl_42_55) (forall_cons (fun _ h => by cases h; exact sl_42_56) (forall_cons (fun _ h => by cases h; exact sl_42_57) (forall_cons (fun _ h => by cases h; exact sl_42_58) (forall_cons (fun _ h => by cases h; exact sl_42_59) (forall_cons (fun _ h => by cases h; exact sl_42_60) (forall_cons (fun _ h => by cases h; exact sl_42_61) (forall_cons (fun _ h => by cases h; exact sl_42_62) (forall_cons (fun _ h => by cases h; exact sl_42_63) (forall_cons (fun _ h => by cases h; exact sl_42_64) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
set_option maxRecDepth 500000 in
def ps_42 : BT (Option PoolSpec) := btOfList 9 [q 56 [16388,16389],q 56 [16388,16389,40987],q 56 [16390,16391],q 56 [16389],q 29 [],q 27 [],q 30 [],q 61 [20633],q 7 [],q 61 [20489],q 50 [20489],q 31 [],q 52 [],q 51 [],q 34 [],q 61 [20490,20491],q 61 [20490],q 37 [],q 61 [],q 54 [],q 12 [],q 41 [],q 42 [],q 28 [],q 61 [20658],q 20 [],q 1 [16389,20489,159784,163843],q 56 [16390],q 32 [],q 55 [],q 33 [],q 2 [],q 62 [20496],q 61 [20488],q 54 [20493],q 54 [20489],q 54 [12298],q 35 [],q 61 [20781],q 56 [16388],q 13 [],q 21 [],q 61 [28848],q 61 [20618],q 9 [],q 38 [],q 8 [],q 10 [],q 1 [16388,20488,426009,430081],q 56 [16391],q 64 [],q 26 [],q 22 [],q 18 [],q 6 [20493,28691],q 60 [],q 18 [20493,28676],q 0 [],q 58 [],q 46 [16395],q 36 [],q 18 [20493],q 2 [16390,20493,28735],q 1 [16390,16391,20490],q 39 [],q 17 [],q 1 [],q 56 [],q 1 [16389,28712,73739],q 1 [16390,16391,20633],q 1 [16388,24577,28679],q 1 [16389,20489,159784],q 11 [],q 62 [],q 1 [16388,24577,20488],q 2 [16388,20493,28699],q 7 [20493,28699],q 12 [16388,20507],q 15 [],q 20 [16388],q 56 [94213],q 5 [20493,28691],q 56 [594038],q 9 [20493],q 53 [],q 59 [],q 43 [],q 14 [],q 1 [8197,16500,29443],q 12 [16388,12313],q 1 [16390,16391,20489],q 4 [16388,28699],q 56 [94214],q 57 [],q 1 [16389,28712,73737],q 47 [20487],q 54 [20490],q 1 [16390,16391,20618],q 15 [20633],q 61 [172187],q 15 [12481],q 18 [12653],q 15 [20495],q 61 [180531],q 61 [798873],q 51 [20493],q 11 [20496],q 3 [20489],q 15 [20493],q 8 [16388,446491],q 6 [20489,159771],q 4 [16388,159771],q 3 [20489,163853],q 61 [20491],q 5 [20493,28679],q 56 [356989],q 2 [16388,20493,28676],q 1 [16388,24577,20490],q 61 [172185],q 3 [20489,163855],q 3 [20493],q 46 [],q 4 [28688,593926],q 1 [28688,593925],q 6 [20493,28683],q 7 [20493],q 4 [28676,28688],q 2 [20493,28676],q 5 [20493],q 6 [20493,8661],q 40 [],q 1 [20490,213187],q 12 [16399],q 1 [20490,20491],q 24 [16397],q 12 [159760],q 8 [159760],q 3 [20493,28683],q 1 [20489,159952],q 1 [16395,29311],q 1 [16393,29224],q 6 [20493,28681],q 3 [20493,28681],q 2 [20493,28691],q 7 [16393],q 8 [16392,29079],q 20 [20493],q 3 [20493,29079],q 4 [28676,16855],q 47 [],q 1 [16392,16393],q 18 [20495],q 3 [20885,20493],q 10 [20885],q 18 [21782],q 3 [12693,21782],q 18 [21781],q 3 [12693,21781],q 3 [12693,20493],q 20 [20495],q 6 [20493,28689],q 7 [20497],q 18 [1380367],q 25 [12297],q 1 [20498,20499],q 1 [20497,856200],q 1 [20487,16395],q 1 [20486,701],q 4 [339984],q 1 [20485,340176],q 26 [20485],q 3 [20485],q 25 [12293],q 1 [16390,16391],q 7 [20493,29043],q 10 [20493],q 1 [8199,17351],q 4 [16388,8219],q 12 [16388],q 1 [16388,20489],q 1 [20496],q 1 [8198,29607],q 25 [8197],q 1 [8199,213959],q 1 [8197,28788],q 5 [16397,20690],q 44 [],q 3 [8197],q 1 [20497,856888],q 1 [16390,20488],q 2 [16390],q 3 [8197,20598],q 1 [8197,16500],q 10 [364557],q 5 [16389,40975],q 1 [20484,20485],q 18 [700431],q 3 [20885,700431],q 1 [16390,20490],q 45 [16390],q 11 [20484],q 10 [12693],q 1 [16389,20490],q 45 [],q 1 [16389,40971],q 4 [16388],q 16 [],q 1 [16391,20490],q 1 [16391,20633],q 6 [16397],q 1 [20490,212996],q 2 [16388,20493],q 1 [16388,20490],q 1 [16388,24577],q 5 [16389],q 1 [16388,28679],q 8 [8196],q 1 [16390,20491],q 3 [12297,20618],q 1 [16391,20618],q 24 [12289,16390],q 24 [12293],q 63 [],q 18 [21698],q 1 [20490,16579],q 1 [20489,160568],q 24 [12294],q 12 [12294],q 50 [],q 5 [20497,856079],q 8 [16392],q 4 [16388,172042],q 1 [16390,20489],q 1 [16388,20489,159771],q 9 [16389],q 3 [20489,159759],q 1 [16389,20489],q 1 [16388,20507],q 12 [20496],q 1 [20489,159760],q 4 [16388,172040],q 11 [20488],q 1 [16388,20488],q 11 [16388],q 6 [12313,20493],q 2 [16390,20493],q 5 [20497],q 1 [8197,213108],q 0 [16388,8219,20493],q 4 [16392],q 1 [28679,16735],q 1 [16388,20490,24769],q 1 [16390,20618],q 3 [20493,593929],q 1 [16390,28735],q 25 [12294],q 2 [16388,20505],q 24 [16389],q 1 [16389,40968],q 8 [16388,8219],q 6 [20489],q 12 [20484],q 2 [16399,4863],q 25 [8198],q 5 [12705],q 0 [16388,12298,20633],q 1 [16388,20633],q 0 [16388,20505,20493],q 1 [16388,20618],q 0 [16388,20490,12481],q 1 [16390,20489,159760],q 26 [20487],q 2 [16397,212996],q 8 [16388],q 1 [16388,20488,426009],q 4 [16388,28696],q 1 [16388,28699],q 0 [16388,20493,28699],q 0 [16388,20493,28676],q 4 [16388,28676],q 1 [16389,20618],q 1 [16389,28712],q 1 [16389,20633],q 1 [20490,4863],q 1 [16390,20633],q 24 [16390],q 1 [16389,20522],q 1 [16390,20489,159807],q 1 [16391,20489],q 25 [],q 48 [],q 1 [20498],q 2 [20498],q 1 [16691],q 1 [4403],q 1 [28691],q 2 [20493],q 1 [28688],q 4 [28688],q 49 [],q 2 [16399],q 1 [4863],q 1 [20690],q 1 [212996],q 5 [16397],q 1 [20491],q 1 [20490],q 24 [],q 0 [20490,16579],q 0 [20490,4291],q 2 [20497],q 1 [20489],q 1 [20499],q 1 [20489,159748],q 4 [159748],q 1 [20488,16803],q 1 [20488],q 1 [16395],q 1 [28676],q 0 [20493,28676],q 4 [28676],q 5 [12293],q 0 [16388,12298],q 1 [16388],q 0 [16388,20505],q 6 [20505],q 3 [20505],q 1 [20497],q 2 [16397],q 0 [16388,8219],q 2 [12294],q 2 [16388],q 1 [8198],q 1 [16393],q 1 [8199],q 1 [20485],q 19 [],q 1 [21334],q 3 [12297],q 1 [16391],q 1 [28679],q 1 [20497,856068],q 4 [856068],q 0 [16388,20490],q 1 [16390],q 6 [12297],q 20 [12294],q 1 [20487,17067],q 1 [16392],q 1 [20486],q 24 [12289],q 0 [20486,12989],q 2 [20486],q 1 [16394],q 1 [8196],q 0 [8196,12657],q 1 [20487],q 1 [16539],q 0 [20498,4459],q 0 [20486,17087],q 1 [16389],q 1 [17236],q 1 [21246],q 1 [139268],q 1 [8197],q 1 [17208],q 1 [17239],q 4 [8196],q 1 [21245],q 0 [16399,21245],q 1 [20484],q 0 [16388,12313],q 6 [12313],q 0 [8196,16755],q 2 [20489],q 0 [16388,20506],q 0 [16388,20493],q 0 [8196,20849],q 6 [20849],q 7 [20489],q 1 [20618],q 1 [21333],q 6 [12633],q 23 [],q 5 [20485],q 1 [20485,339984],q 0 [20486,8895],q 1 [16520],q 1 [4251],q 1 [20633],q 0 [12298,20633],q 0 [16392,413702],q 0 [16392,20885],q 1 [21306],q 0 [16388],q 0 [12294],q 0 [8196],q 0 [20498],q 0 [20486],q 0 [20490],q 0 [16392]]
def B_42_3 : BT (List (List Nat)) := BT.empty
lemma B_42_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_42 3 xs.toFinset) B_42_3 := .empty
def U_42_4 : List Nat := [0,1]
def P_42_4 : BT (Option BoundPool) := buildPoolsSubBT 9 W_42 r_42 S_42 ps_42 U_42_4
def N_42_4 : List NodeSpec := [([0,9,3,12,5],[0],[]),([13,14,0,3,5],[1],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_42_4 : checkNodesBT W_42 g_42 F_42 P_42_4 A_42 B_42_3 4 N_42_4 = true := by decide +kernel
def B_42_4 : BT (List (List Nat)) := buildBucketsBT W_42 N_42_4
set_option maxRecDepth 500000 in
lemma B_42_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_42 4 xs.toFinset) B_42_4 :=
  buildBucketsBT_sound (by decide) gp_42 W_42_ok (buildPoolsSubBT_sound S_42_ok) A_42_ok B_42_3_ok C_42_4
def U_42_5 : List Nat := (r 0 11)
def P_42_5 : BT (Option BoundPool) := buildPoolsSubBT 9 W_42 r_42 S_42 ps_42 U_42_5
def N_42_5 : List NodeSpec := [([0,9,3,10,5,11],[0],[0]),([13,0,6,3,10,5],[0],[0]),([0,6,8,3,12,5],[0],[0]),([14,0,8,3,5,11],[1],[0]),([36,37,14,0,3,5],[1],[0]),([15,13,16,0,3,5],[2],[0]),([24,0,1,3,4,5],[3],[]),([21,0,1,3,4,5],[3],[]),([35,14,0,2,3,7],[4,5],[]),([47,14,0,2,5,7],[4,5],[]),([0,6,3,41,40,5],[6],[]),([14,0,2,49,5,7],[6,4],[]),([14,0,2,3,45,7],[6,4],[]),([43,0,1,44,4,45],[7],[]),([14,46,2,3,5,45],[8],[]),([58,0,2,3,40,5],[9],[]),([62,0,2,3,4,5],[10],[]),([56,0,1,2,3,4],[],[]),([63,0,6,2,3,40],[],[]),([51,0,1,3,23,5],[],[]),([33,0,1,2,3,5],[],[]),([0,28,1,3,4,5],[],[]),([22,0,1,3,23,5],[],[]),([16,0,8,3,17,5],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_42_5 : checkNodesBT W_42 g_42 F_42 P_42_5 A_42 B_42_4 5 N_42_5 = true := by decide +kernel
def B_42_5 : BT (List (List Nat)) := buildBucketsBT W_42 N_42_5
set_option maxRecDepth 500000 in
lemma B_42_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_42 5 xs.toFinset) B_42_5 :=
  buildBucketsBT_sound (by decide) gp_42 W_42_ok (buildPoolsSubBT_sound S_42_ok) A_42_ok B_42_4_ok C_42_5
def U_42_6_0 : List Nat := (r 0 50)
def P_42_6_0 : BT (Option BoundPool) := buildPoolsSubBT 9 W_42 r_42 S_42 ps_42 U_42_6_0
def N_42_6_0 : List NodeSpec := [([0,6,8,3,10,5,11],[0],[0]),([36,37,0,6,3,10,5],[0],[0]),([36,15,37,16,0,3,5],[2],[0]),([15,16,0,8,3,5,11],[2],[0]),([129,0,1,2,3,18,5],[3],[]),([22,0,1,3,4,5,11],[3],[0]),([132,133,0,1,3,4,5],[3],[0]),([0,1,101,3,139,142,5],[4],[]),([87,81,2,3,4,42,7],[4],[]),([87,0,2,110,4,42,7],[4],[]),([140,0,1,101,3,139,5],[4],[]),([35,15,16,0,2,3,7],[4,5],[0]),([47,0,6,2,10,5,7],[4,5],[0]),([35,0,6,2,3,10,7],[4,5],[0]),([15,47,16,0,2,5,7],[4,5],[0]),([16,0,2,3,17,5,7],[4,5,2],[0]),([108,81,2,3,10,5,42],[5],[]),([48,14,0,2,3,5,42],[5,6],[]),([108,14,0,2,3,5,42],[5,6],[]),([36,14,0,2,3,5,7],[5,6,1],[0]),([0,1,3,41,4,40,5],[6],[0]),([0,2,9,3,10,5,7],[6,0],[0]),([15,16,0,2,49,5,7],[6,4],[0]),([0,6,2,49,10,5,7],[6,4],[0]),([15,16,0,2,3,45,7],[6,4],[0]),([0,6,2,3,10,45,7],[6,4],[0]),([37,14,0,2,3,5,7],[6,5,1],[0]),([46,6,2,3,10,5,45],[8],[0]),([15,16,46,2,3,5,45],[8],[0]),([0,60,2,3,4,61,5],[10],[0]),([64,65,0,2,3,4,5],[10],[0]),([48,14,0,2,3,5,7],[4,5,6,11],[0]),([48,0,44,3,10,5,42],[5,11],[]),([0,6,2,3,40,5,7],[6,5,11],[]),([66,0,1,8,3,23,5],[12],[]),([14,0,2,3,5,39,7],[11,14,6,5,4],[0]),([87,88,0,2,3,4,5],[14],[]),([81,82,2,3,10,5,42],[14,5],[]),([14,0,82,2,3,5,42],[14,5,6],[]),([0,2,105,3,111,10,5],[14,6,13],[]),([14,0,8,2,3,5,7],[14,11,5,6,1],[0]),([48,67,14,0,3],[13,6,14,15],[]),([14,0,116,2,3,5],[5,16],[]),([48,14,0,44,3,5],[6,5,16,11],[]),([14,0,2,3,49,5],[6,16,5],[0]),([48,14,0,3,34,5],[6,16,5,11],[]),([48,14,81,2,3,5],[6,16,14],[]),([48,68,14,2,3,5],[14,6,16],[]),([113,1,81,2,3,4,5],[16],[]),([47,14,0,2,3,5],[5,17,6,9],[0]),([0,6,2,3,40,57,5],[5,17,9],[0]),([119,0,6,2,3,40,5],[5,17,9],[]),([38,0,6,3,40,5],[14,5,6,17],[0]),([48,14,2,3,79,5],[14,16,17],[]),([106,1,2,105,3,4,5],[14,17],[]),([38,73,1,3,4,40,5],[17],[]),([75,76,0,1,2,4,42],[5,18],[]),([38,43,0,1,44,4,5],[18],[0]),([43,25,0,1,2,4,5],[18],[]),([43,1,81,2,4,42,7],[18],[]),([75,0,1,94,2,4,5],[18],[]),([43,0,1,69,2,4,5],[18],[]),([14,0,2,3,70,5],[5,14,19,4],[]),([25,0,1,2,125,4,5],[20],[]),([25,0,1,2,3,4,126],[20],[]),([25,0,1,2,3,4,45],[20],[]),([25,0,1,2,49,4,5],[20],[]),([0,1,2,49,4,18,5],[20,4],[]),([0,1,2,3,4,18,45],[20,4],[]),([1,81,2,3,4,45,42],[7,5,22],[]),([0,1,8,3,4,12,5],[3,23],[0]),([0,1,19,3,4,20,5],[3,23],[0]),([0,1,8,3,23,50,5],[21,22,12,23],[0]),([0,1,8,3,23,10,5],[21,22,23],[0]),([43,0,6,1,2,4,45],[22,21,23,7],[0]),([85,0,86,2,3,4,84],[23],[]),([0,29,3,4,99,100,5],[23],[]),([0,1,8,3,4,17,5],[23],[0]),([37,0,1,3,4,130,5],[23,3],[]),([1,2,102,79,103,4,5],[23,4],[]),([0,86,2,3,4,84,137],[23,21],[]),([13,0,1,3,4,10,5],[23,21,22,3],[0]),([72,14,0,2,3,5],[24,5],[]),([1,81,2,3,115,4,5],[25],[]),([1,2,3,74,4,40,5],[17,25,26,21],[]),([15,13,0,1,3,4,5],[27],[0]),([1,2,3,80,4,40,5],[17,28],[]),([90,91,93,0,3],[29,23,4,30],[]),([1,81,2,3,4,5,97],[31,5],[]),([134,1,81,2,3,4,5],[31,8],[]),([93,0,3,4,98,5],[32,14,30],[]),([14,0,2,105,3,5],[5,14,33],[]),([14,0,2,3,109,5],[6,14,33],[]),([88,0,2,3,10,5,7],[34,0],[]),([14,0,2,3,5,7,11],[34,4,14,5,1,6],[0]),([0,6,2,3,12,5,7],[34,5,0],[0]),([38,14,0,3,5,39],[6,35,5,11,17,36,4],[]),([76,0,6,1,2,4,112],[22,37,38],[]),([13,0,6,1,3,4,5],[22,21,23,39],[0]),([0,1,9,3,4,5,11],[39,12],[0]),([0,1,44,3,4,45,42],[7,40],[0]),([0,1,44,49,110,4,5],[16,40],[]),([0,82,44,3,10,5,42],[40],[]),([0,116,2,3,10,5,42],[40,6],[]),([14,0,2,3,5,45],[6,7,41],[0]),([0,1,2,114,110,4,5],[42,40],[]),([0,1,2,114,3,4,42],[42,40],[]),([35,14,0,2,3,5],[5,43],[]),([47,0,1,2,4,18,5],[4,44],[]),([35,0,1,2,3,4,18],[4,44],[]),e6 [131] [8,31,44],([0,1,2,3,23,18,5],[23,44,3],[]),([0,117,2,9,3,4,5],[22,45],[]),([121,1,2,3,109,4,5],[46],[]),([16,0,128,2,3,4,5],[23,47],[]),([136,1,2,105,3,4,5],[5,14,17,21,48],[]),([13,16,0,1,3,4,5],[49],[0]),([47,0,1,2,4,124,5],[],[]),([141,37,0,1,3,4,5],[],[]),([122,0,123,1,3,4,5],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_42_6_0 : checkNodesBT W_42 g_42 F_42 P_42_6_0 A_42 B_42_5 6 N_42_6_0 = true := by decide +kernel
def U_42_6_1 : List Nat := []
def P_42_6_1 : BT (Option BoundPool) := buildPoolsSubBT 9 W_42 r_42 S_42 ps_42 U_42_6_1
def N_42_6_1 : List NodeSpec := [([26,0,1,27,3,4,5],[],[0]),([25,0,2,3,4,127,5],[],[]),([87,25,81,2,3,4,5],[],[]),([95,96,0,1,2,3,5],[],[0]),([77,78,0,1,2,3,4],[],[0]),([47,0,1,71,2,4,5],[],[]),([0,1,2,54,3,4,55],[],[0]),([0,1,2,31,3,32,5],[],[0]),([63,0,1,2,3,4,40],[],[0]),([118,0,2,30,3,4,5],[],[]),([107,0,1,2,53,4,5],[],[]),([15,0,1,8,3,23,5],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_42_6_1 : checkNodesBT W_42 g_42 F_42 P_42_6_1 A_42 B_42_5 6 N_42_6_1 = true := by decide +kernel
def N_42_6 := N_42_6_0 ++ N_42_6_1
def B_42_6 : BT (List (List Nat)) := buildBucketsBT W_42 N_42_6
set_option maxRecDepth 500000 in
lemma B_42_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_42 6 xs.toFinset) B_42_6 := by
  have hm0 := checkNodesBT_mem (by decide) gp_42 W_42_ok (buildPoolsSubBT_sound S_42_ok) A_42_ok B_42_5_ok C_42_6_0
  have hm1 := checkNodesBT_mem (by decide) gp_42 W_42_ok (buildPoolsSubBT_sound S_42_ok) A_42_ok B_42_5_ok C_42_6_1
  exact buildBucketsBT_of_mem (forall_append (hm0) hm1)
def U_42_7_0 : List Nat := ([0]++r 2 13++[16,17,18]++r 20 4)
def P_42_7_0 : BT (Option BoundPool) := buildPoolsSubBT 9 W_42 r_42 S_42 ps_42 U_42_7_0
def N_42_7_0 : List NodeSpec := [e6 [249,7] [4],e6 [162,7] [4],([35,15,0,1,2,3,4,7],[4,5],[0]),e6 [36,124] [5],([200,1,2,110,4,5],[5,4],[]),([221,0,1,2,110,4,5,7],[5,4],[]),([118,0,2,29,3,4,5,7],[5,4],[0]),([108,0,6,2,3,10,5,42],[5,6],[0]),([36,0,6,2,3,10,5,7],[5,6,0],[0]),([36,15,16,0,2,3,5,7],[5,6,2],[0]),([16,0,1,2,3,4,45,7],[6,4],[0]),([16,0,1,2,49,4,5,7],[6,4],[0]),([37,0,6,2,3,10,5,7],[6,5,0],[0]),([15,37,16,0,2,3,5,7],[6,5,2],[0]),u6 [139,142] [4,8],([118,87,0,2,3,4,5,7],[8,4],[]),u6 [140,139] [8,4],u6 [64,59] [8,10],u6 [65,59] [8,10],([48,0,6,2,3,10,5,7],[4,5,6,11],[0]),([48,15,16,0,2,3,5,7],[4,5,6,11],[0]),([48,0,1,44,3,4,5,42],[5,11],[0]),e6 [190,7] [11,4],([48,15,67,16,0,3],[5,13,6,14],[0]),([0,6,2,3,70,10,5],[5,14],[0]),([15,16,0,2,3,70,5],[5,14],[0]),([76,1,81,2,3,4,42],[5,14,4],[]),([48,0,6,2,3,10,5,42],[5,14,6],[0]),([15,16,0,2,3,109,5],[11,6,14],[0]),([0,6,2,3,10,5,7,11],[11,14,4,5,0,6],[0]),([15,16,0,2,3,5,39,7],[11,14,6,5,4],[0]),([0,6,2,3,10,5,39,7],[11,14,6,5,4],[0]),([48,67,0,6,3,10],[13,5,6,14],[0]),([0,6,82,2,3,10,5,42],[14,5,6],[0]),([0,6,8,2,3,10,5,7],[14,11,4,5,6,0],[0]),([15,16,0,8,2,3,5,7],[14,11,5,6,2],[0]),([0,6,116,2,3,10,5],[5,6,16],[0]),([48,6,81,2,3,10,5],[5,14,16],[0]),([48,0,6,44,3,10,5],[6,5,16,11],[0]),([48,14,0,6,2,3,5],[6,5,16,11],[0]),([0,6,2,3,49,10,5],[16,6,5],[0]),([48,15,16,0,3,34,5],[4,6,5,17,11],[0]),([1,2,79,4,252,5],[4,17],[]),([1,2,79,235,4,5],[4,17],[]),([48,0,6,3,34,10,5],[5,4,6,17,11],[0]),([15,38,16,0,3,5,39],[5,6,11,17,4],[0]),([47,0,6,2,3,10,5],[5,17,9,6],[0]),([38,0,6,3,10,5,39],[14,5,6,17,4],[0]),([240,195,1,2,3,4,5],[17,4],[]),([48,6,2,3,79,10,5],[17,14,16],[0]),([0,1,2,110,4,42,7],[4,18,5,11],[0]),([200,1,2,3,4,5,42],[5,4,18],[]),([81,2,3,10,5,42],[5,14,18],[0]),([14,0,2,44,3,5],[5,18,11],[0]),([14,0,2,3,34,5],[5,18,11],[0]),([221,14,0,2,3,5],[6,5,18],[]),([38,14,0,2,3,5],[6,18,11],[0]),([68,14,2,3,5],[8,14,18,17],[0]),([76,14,0,2,3,5],[11,5,6,18],[]),([14,195,0,2,3,5],[11,18,5,6],[]),([0,2,44,3,10,5,42],[14,17,18,6],[0]),([1,81,2,3,4,42,7],[18,4,5,14],[0]),([0,1,2,110,4,5,42,7],[18,4,11],[]),([14,81,2,3,5],[18,5,14],[0]),([14,0,2,3,5,42],[18,5,14,6],[0]),([14,0,2,3,5,7],[18,11,14,6,5],[0]),([14,2,3,79,5],[18,14,17,8],[0]),e6 [48,124] [5,20,11],([1,2,79,4,247,5],[17,21],[]),([25,0,1,2,110,4,5,7],[21,4,18],[]),([43,1,81,2,3,4,5,42],[4,18,22],[0]),([1,81,2,3,4,5,42,7],[14,4,22],[]),([1,81,2,105,3,4,5],[14,5,4,22],[]),([25,1,81,2,3,4,5,7],[22,4],[0]),e6 [158] [22,5,11],([87,0,6,2,110,4,5,7],[22,21,4],[0]),([43,0,6,1,2,4,5,211],[22,21,18],[0]),([0,86,2,3,4,84],[4,11,23],[0]),([43,0,1,2,110,4,5,42],[4,18,23],[]),([191,0,1,2,226,3,5],[4,23],[]),e6 [145,153] [4,23],([129,0,1,2,3,10,5,7],[4,23,3,6],[0]),([47,16,0,1,2,4,5,7],[4,23,5],[0]),([233,241,0,3,4,98,5],[4,23,14],[0]),([196,87,0,1,2,3,5],[4,23,22],[]),([76,0,1,2,44,3,4,42],[5,11,23,18],[0]),e6 [221,222] [5,23],([246,1,2,244,4,5],[5,23],[]),([177,1,2,178,4,5],[5,23],[]),([221,195,0,1,2,3,4,7],[5,23],[]),([213,0,2,3,4,180,5],[5,23],[]),e6 [167] [5,23,4],e6 [221,25] [5,23,18],([38,43,0,6,1,2,4,5],[5,23,22,21,18],[0]),([0,1,101,3,180,5],[6,23],[]),e6 [87,139] [8,4,23],e6 [266,6] [8,17,23,22,21,7],u6 [59,61] [11,17,8,10,21,23],([76,0,1,2,4,260],[11,23],[]),u6 [60,59] [17,11,23,8,10],([1,2,3,79,4,99,5],[17,23],[]),([15,1,2,3,79,198,5],[17,23,5],[]),([0,1,8,3,4,10,5,11],[21,22,23,3],[0]),([15,184,47,1,2,3,4,5],[21,23,5,17],[]),([0,1,8,3,23,5],[21,23,12],[0]),([6,1,2,3,109,120,4,5],[21,23,14,6],[0]),([15,1,2,3,109,120,4,5],[21,23,14,11],[]),([87,0,149,2,3,4,5,7],[22,23,4],[]),([87,0,164,2,3,4,5,7],[22,23,4],[]),e6 [194] [22,23,4],u6 [40,7] [22,23,6,5,11,4],([36,16,0,117,2,3,4,5],[23],[0]),([176,2,3,242,4,5],[23,4],[]),([0,1,2,3,237,4,236],[23,4],[]),([87,0,161,2,3,4,5,7],[23,4],[]),([15,47,0,1,2,4,5,7],[23,4,5],[0]),u6 [102,103] [23,4,21],e6 [226,227] [23,4,21],([87,195,0,6,2,3,4,7],[23,4,22],[]),([48,16,0,117,2,3,4,5],[23,5],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_42_7_0 : checkNodesBT W_42 g_42 F_42 P_42_7_0 A_42 B_42_6 7 N_42_7_0 = true := by decide +kernel
def U_42_7_1 : List Nat := (r 2 8++r 11 4++[16,17,18]++r 20 14++[35]++r 37 5++[43,44,45])
def P_42_7_1 : BT (Option BoundPool) := buildPoolsSubBT 9 W_42 r_42 S_42 ps_42 U_42_7_1
def N_42_7_1 : List NodeSpec := [e6 [213,256] [23,6],([25,0,1,2,3,4,42,7],[23,11,18,4],[]),([1,2,226,3,79,4,5],[23,14],[]),([170,1,2,3,79,4,171],[23,17,6],[]),([170,172,1,2,3,4,171],[23,17,6],[]),u6 [25,42] [23,18,4],u6 [25,211] [23,18,4],u6 [99,100] [23,21],([213,0,1,2,3,228,4,171],[23,21],[]),e6 [180,182] [23,21],e6 [181,180] [23,21],e6 [248,226] [23,21],([0,1,8,3,23,4,5],[23,21,12],[0]),([37,87,0,6,2,3,4,5],[23,22],[]),([0,117,2,3,179,4,5],[23,22,4],[]),([0,117,2,3,155,4,5],[23,22,4],[]),([150,87,0,1,3,4,5],[23,22,4],[]),([43,0,6,1,2,4,5,7],[23,22,21,18],[0]),([72,0,6,2,3,10,5],[5,24],[0]),([48,1,81,2,3,4,5,42],[5,14,25],[]),([108,1,81,2,3,4,5,42],[5,25],[0]),([1,81,82,2,3,4,5,42],[14,5,25],[0]),([38,1,81,2,3,4,5,42],[14,25,18,5,4,22],[0]),([73,1,2,3,4,40,5],[14,5,17,26,22],[0]),([36,15,37,0,1,3,4,5],[23,27],[0]),([15,0,1,8,3,4,5,11],[23,27],[0]),([159,1,2,79,250,4,5],[4,5,14,28,23],[]),([48,1,2,217,79,4,5],[4,14,28,17],[]),([15,16,0,2,3,5,7,11],[4,28,14,5,2,6],[0]),([0,6,2,3,4,127,5,7],[28,4],[0]),([76,0,1,2,4,231],[28,23],[]),([90,91,233,241,0,3],[29,23,4],[0]),([15,0,1,2,3,23,5,7],[5,30,28,27],[0]),e6 [201] [14,30,17],e6 [163,8] [17,30,4,12],([1,81,2,3,4,5,42,211],[18,30,4,22],[]),([212,1,2,79,4,98,5],[21,23,17,30,4],[]),u6 [17,7] [23,5,27,30],([0,92,29,3,4,98,5],[23,14,30],[0]),e6 [187] [23,30],e6 [268] [23,30],([90,91,0,92,29,3],[29,23,30],[0]),([0,29,3,4,99,5],[30,14,23,29],[0]),e6 [254] [23,8,31,4],([93,0,3,89,4,5],[30,32,5,14,29],[0]),([0,6,2,105,3,10,5],[6,14,5,33],[0]),([0,2,105,3,10,5],[6,14,13,33],[0]),([0,6,2,3,109,10,5],[14,6,33],[0]),e6 [105,110] [22,14,5,33,4],e6 [6,111] [22,21,17,8,23,33],([35,0,1,2,3,4,10,7],[4,21,22,23,37,5],[0]),([47,0,1,2,4,10,5,7],[4,21,22,23,37,5],[0]),u6 [36,25] [5,20,37],([184,47,1,2,3,4,10,5],[5,21,37,17,23],[]),([38,0,1,44,3,4,5,42],[6,37,18,23],[0]),u6 [75,42] [11,23,21,37,18,5],u6 [8,18] [14,11,4,20,37,3],([0,1,2,44,3,4,42,7],[18,5,23,37],[0]),u6 [69,42] [18,11,23,5,37],u6 [36,18] [20,37,3],([0,1,2,3,23,10,5,7],[21,22,4,23,37,5,3,30],[0]),([35,0,6,1,2,3,4,7],[21,23,4,22,37,5],[0]),([48,75,0,6,1,3,4,5],[22,37,16],[]),([0,6,1,2,3,4,45,7],[22,37,23,6,4],[0]),([47,0,6,1,2,4,5,7],[23,21,4,22,37,5],[0]),([36,37,0,1,3,4,10,5],[23,37,22,3],[0]),([38,199,0,1,3,4,5],[37,5,20,17],[]),([46,1,2,3,4,10,5,45],[37,8,21,23],[0]),([46,6,1,2,3,4,5,45],[37,8,23,21],[0]),([0,1,2,3,4,10,45,7],[37,22,23,6,4],[0]),u6 [9,7] [22,6,37,39],([0,6,1,8,3,4,5,11],[22,21,23,39,12],[0]),e6 [37,25] [23,5,39],([36,37,0,6,1,3,4,5],[23,37,22,39],[0]),([0,6,1,2,110,109,4,5],[22,21,23,40,33],[]),e6 [118,8] [30,40,17],([0,117,1,8,156,3,4,5],[40,20],[]),([87,0,6,2,3,222,4,5],[40,22],[]),([14,0,2,3,5,39],[5,17,35,9,8,41,13,11,6],[0]),([0,6,2,3,10,5,45],[7,6,41],[0]),u6 [6,112] [22,37,41,38,5],e6 [6,45] [25,37,41,23,21,6],([16,46,1,2,3,4,5,45],[41,23,21,8],[0]),([35,0,6,2,3,10,5],[5,43],[0]),u6 [130,7] [4,6,3,44],([48,0,1,44,3,110,4,5],[4,17,44,16,21],[0]),e6 [18] [4,20,44,11],e6 [72,110] [4,21,17,44,24],([1,101,2,79,250,4,5],[4,23,28,21,44],[]),([0,164,2,3,174,4,5],[4,44,11],[]),u6 [43,44] [6,44,21,23,18],e6 [253] [8,31,44,23],u6 [18,11] [11,14,4,23,44,3,6],u6 [18,39] [11,14,44,4,23,6],u6 [19,18] [14,11,4,44,20,3],u6 [94,44] [18,6,44,23],e6 [44,211] [18,40,6,44],u6 [122,25] [20,44],([210,159,1,2,79,4,5],[21,23,44,4,28],[]),u6 [84,137] [23,44,21],u6 [71,39] [28,14,4,44,6],e6 [25] [31,20,44,4],e6 [165] [31,44,8,4],([0,1,82,44,3,4,5,42],[40,44,23],[0]),e6 [25,44] [44,6],u6 [132,18] [44,20,3],u6 [25,123] [44,20,4],([210,1,2,79,4,138,5],[44,21,23,4,28],[]),e6 [37,71] [44,23],u6 [85,84] [44,23],e6 [37,124] [44,23],e6 [37,18] [44,23,3],e6 [160,7] [4,5,45],([1,2,189,3,79,4,5],[4,14,21,45],[]),([15,0,1,2,3,198,5,7],[5,30,45,11],[]),([0,92,226,3,4,5],[23,45],[]),u6 [141,7] [30,45,27],e6 [87,204] [37,45,8,4],([15,0,1,2,49,4,5,7],[45,4],[0]),([15,0,1,2,3,4,45,7],[45,4],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_42_7_1 : checkNodesBT W_42 g_42 F_42 P_42_7_1 A_42 B_42_6 7 N_42_7_1 = true := by decide +kernel
def U_42_7_2 : List Nat := (r 3 6++r 11 4++[16,17,18]++r 20 6++r 27 5++[37,39,40,41]++r 44 36)
def P_42_7_2 : BT (Option BoundPool) := buildPoolsSubBT 9 W_42 r_42 S_42 ps_42 U_42_7_2
def N_42_7_2 : List NodeSpec := [e6 [185,7] [45,5,11],([159,258,0,1,3,4,5],[45,23,44],[]),e6 [232,7] [45,23,44,27],([159,0,117,1,8,3,4,5],[45,37,12,5],[]),u6 [54,53] [17,28,4,45,23,46],u6 [78,53] [23,46],u6 [53,55] [28,17,4,23,46],e6 [165,7] [46,4],e6 [25,7] [46,4],u6 [22,7] [46,22,4,44,6,3],u6 [12,7] [46,22,5,3,4],u6 [88,7] [46,22,23,4,5,39],u6 [77,53] [46,23],([15,46,1,2,3,4,5,45],[21,23,47],[0]),e6 [153] [23,31,47,8],([87,0,6,2,3,4,5,211],[47,22,21],[]),([87,25,0,6,2,3,4,5],[47,23],[0]),([1,2,105,135,3,4,5],[5,14,25,13,22,48],[0]),([36,37,16,0,1,3,4,5],[49],[0]),([16,0,1,8,3,4,5,11],[49,12],[0]),([146,0,151,1,2,3,5],[4,50,23],[]),([0,1,144,3,145,5],[21,23,50],[]),([166,0,1,2,3,5],[21,50,23],[]),([146,0,1,2,3,23,5],[5,30,51,21,47],[]),([146,147,0,2,3,4,5],[8,5,52,23],[]),e6 [263,145] [6,4,23,53],u6 [31,30] [14,37,23,47,53],([0,1,2,3,174,4,171],[23,6,53],[]),([0,1,173,2,3,4,171],[23,6,53],[]),u6 [30,32] [28,14,23,37,47,53],e6 [30] [31,23,53,47],e6 [117,216] [40,45,53,28],e6 [117,154] [40,45,53,28],u6 [96,30] [47,53],([0,117,2,3,145,4,188,5],[53,4],[]),([146,0,151,1,2,3,5,7],[53,11,4],[]),([146,0,1,2,192,3,5,7],[53,21,23,4],[]),([0,1,8,3,145,4,148,5],[53,23],[]),u6 [95,30] [53,47],([87,0,149,2,3,4,5],[54,4,14,23],[]),e6 [195,69] [6,37,55,5],u6 [128] [22,23,55,47,53],([87,0,6,2,3,4,5,11],[55,22,41,23,30,4],[0]),([16,0,117,8,2,3,4,5],[4,28,14,56],[]),e6 [129,117] [45,56],e6 [169] [23,57,31,4],e6 [139] [23,57,31,4],([0,1,102,3,138,5],[4,58,11],[]),([183,0,2,3,4,138],[5,4,58],[]),([159,86,2,3,79,4,83],[5,21,23,28,59],[]),([159,183,0,2,3,4],[5,58,59],[]),([35,16,0,1,2,3,4,7],[4,60],[0]),e6 [208] [14,60,21],e6 [36,71] [60],e6 [48,71] [60,20,14],e6 [71,8] [14,28,20,37,4,61],u6 [71,11] [28,14,4,6,61],e6 [117,204] [40,28,45,61],e6 [146,30] [47,61],u6 [124,11] [30,62,4,45],u6 [124,39] [30,62,11,4,44,45],e6 [8,124] [62,30,4,37,20],([15,16,0,2,3,49,5],[45,6,63,5],[0]),([48,15,16,2,3,79,5],[45,63,14],[0]),u6 [48,18] [4,64,20,11],([75,76,0,6,1,2,4,5],[5,64,22,18],[0]),([1,2,3,79,4,197,5],[8,64,45],[]),e6 [116,110] [17,64,4,21,16],([0,1,2,44,110,4,5,7],[18,5,21,64],[0]),([0,6,1,2,49,4,5,7],[22,64,23,6,4],[0]),e6 [6,257] [22,64,23,16],e6 [6,224] [22,64,23,24],([1,205,2,79,4,98,5],[23,14,4,64,17],[]),e6 [267,8] [25,17,5,37,64],e6 [6,49] [25,64,21,23,6],u6 [116,42] [40,23,6,64],([170,164,2,3,79,4,5],[64,4,37],[]),([0,1,2,49,4,10,5,7],[64,22,23,6,4],[0]),e6 [264,7] [64,23,4,39],e6 [6,109] [65,17,21,23,6],e6 [105] [14,5,66,21],u6 [105,111] [22,21,14,5,13,66],([76,0,1,2,4,271],[11,67,23],[]),([13,0,1,3,4,5],[23,21,67],[0]),u6 [30,145] [28,37,23,53,4,67],u6 [133,18] [20,44,68],([15,16,0,2,3,5,45],[45,6,69,41],[0]),([87,6,81,2,3,4,5,7],[40,22,70,30],[0]),([38,0,1,3,4,40,5],[14,6,71,60],[0]),([1,2,102,3,79,4,5],[4,23,21,72,5],[0]),([219,1,2,3,79,4,5],[4,25,21,72,44,45],[]),([1,225,2,3,79,4,5],[4,72,31,46,44,5],[]),([1,2,105,3,79,4,5],[14,17,72,21,5],[0]),([1,2,3,79,4,185,5],[17,5,72,21,25],[]),([1,2,3,79,4,40,5],[17,71,14,72],[0]),([1,2,3,79,4,180,5],[23,4,5,72,31],[]),([1,2,229,3,79,4,5],[25,8,23,72,44,64],[]),([1,2,220,3,79,4,5],[44,8,23,72,31,45],[]),([243,1,2,3,79,4,5],[44,8,72,21,45],[]),([265,1,2,3,79,4,5],[72,21,4,64],[]),([91,93,0,3,4,5],[4,5,73,14],[0]),([76,93,0,3,4,5],[14,23,73],[]),([90,93,0,3,4,5],[23,5,73,30],[0]),([93,3,79,4,5],[23,73,25,17,4],[]),([93,0,3,4,5,7],[28,14,23,73,30,4],[]),([191,93,0,3,4,5],[30,4,73],[]),([93,0,3,4,52,5],[45,4,73,23,14],[]),([93,0,3,4,5,209],[45,23,73,5,8,25,29],[]),([6,1,81,2,3,109,4,5],[46,22,74,14,5],[0]),e6 [25,8] [20,37,75,76],e6 [25,11] [23,5,55,76,75,4,39,61],u6 [25,27] [44,20,76,75,4,61],u6 [26,25] [44,75,76,20],([195,0,6,1,2,3,4,45],[23,22,64,77,40,7],[]),([25,1,81,2,3,4,5],[4,8,25,78],[0]),([1,94,81,2,3,4,5],[14,4,25,78],[]),([72,38,0,6,1,3,4,5],[78,23,64,24],[]),([116,1,81,2,3,4,5],[4,22,60,79],[]),([1,69,81,2,3,4,5],[4,65,55,5,79],[0]),([116,1,2,3,79,4,5],[72,21,17,79,5],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_42_7_2 : checkNodesBT W_42 g_42 F_42 P_42_7_2 A_42 B_42_6 7 N_42_7_2 = true := by decide +kernel
def U_42_7_3 : List Nat := (r 4 6++[11,13,14]++r 16 8++[25]++r 28 4++[33,37,40,41,42]++r 44 4++[50,53,58,60,61,64,71,75,76,77]++r 80 40)
def P_42_7_3 : BT (Option BoundPool) := buildPoolsSubBT 9 W_42 r_42 S_42 ps_42 U_42_7_3
def N_42_7_3 : List NodeSpec := [([0,1,2,3,23,50,5,7],[21,22,61,23,37,5,80,30],[0]),e6 [202,7] [14,23,53,81,4],e6 [203,7] [47,23,30,82],([0,1,101,3,139,5],[4,83,23],[0]),([175,170,0,101,3,138],[58,5,23,84],[]),e6 [213,215] [28,85],([43,0,6,1,2,4,42,7],[11,86,21,18],[0]),u6 [113,6] [64,86,16],([87,0,6,2,3,4,42,7],[86,4],[0]),([172,218,1,2,3,4,5],[86,17,11,6],[]),([0,6,1,2,3,4,45,42],[86,23,40,21,7],[0]),([14,0,6,104,2,3,5],[5,14,6,87,33],[0]),([14,0,104,2,3,5],[6,14,19,33,87,13],[0]),e6 [223] [8,31,47,44,46,88],e6 [223,7] [46,53,88],([0,6,1,2,49,110,4,5],[22,21,89,40,23,16],[0]),([15,47,16,0,2,3,5],[5,17,6,90],[0]),u6 [48,25] [5,20,4,91],([66,0,1,2,3,23,5,7],[5,30,61,92],[0]),e6 [191,239] [4,93],u6 [18,20] [11,14,4,44,94,20],([0,1,101,3,174,138,5],[23,6,4,95],[]),([170,1,101,3,79,138,5],[37,25,4,95,6],[]),([48,14,0,2,3,5],[6,5,96,16,11],[0]),([35,15,16,0,2,3,5],[5,60,97],[0]),([6,1,81,2,3,4,5,45],[37,98,25,22,7,5,17],[0]),([0,6,1,44,3,4,5,45],[98,37,20,64,40,7],[0]),u6 [6,115] [37,23,99,4],([0,6,1,44,3,49,4,5],[100,64,20,37,40,16],[0]),([0,1,2,192,3,255,5],[4,44,101,14],[]),e6 [6,261] [102,64,23,103],e6 [262,6] [8,17,22,37,77,104],e6 [25,39] [20,44,46,4,29,76,75,105,61],([92,1,2,79,4,98,5],[17,23,106,21,50],[]),([0,6,2,3,40,5],[5,17,107,11,9,6],[0]),u6 [6,114] [108,37,17,6,64,42],u6 [134,6] [17,21,109,33],e6 [199,7] [46,22,4,5,110,111],u6 [40,57] [21,22,5,14,112,71],([67,14,0,2,3,5],[5,19,14,113],[0]),e6 [269,7] [45,114,115],([0,6,117,8,2,3,4,5],[22,116,5,23,45],[0]),([6,1,81,2,3,49,4,5],[64,100,25,22,117,40,16],[0]),u6 [6,97] [37,41,21,118,5],u6 [119,40] [5,14,6,21,22,119,71]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_42_7_3 : checkNodesBT W_42 g_42 F_42 P_42_7_3 A_42 B_42_6 7 N_42_7_3 = true := by decide +kernel
def N_42_7 := N_42_7_0 ++ N_42_7_1 ++ N_42_7_2 ++ N_42_7_3
def B_42_7 : BT (List (List Nat)) := buildBucketsBT W_42 N_42_7
set_option maxRecDepth 500000 in
lemma B_42_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_42 7 xs.toFinset) B_42_7 := by
  have hm0 := checkNodesBT_mem (by decide) gp_42 W_42_ok (buildPoolsSubBT_sound S_42_ok) A_42_ok B_42_6_ok C_42_7_0
  have hm1 := checkNodesBT_mem (by decide) gp_42 W_42_ok (buildPoolsSubBT_sound S_42_ok) A_42_ok B_42_6_ok C_42_7_1
  have hm2 := checkNodesBT_mem (by decide) gp_42 W_42_ok (buildPoolsSubBT_sound S_42_ok) A_42_ok B_42_6_ok C_42_7_2
  have hm3 := checkNodesBT_mem (by decide) gp_42 W_42_ok (buildPoolsSubBT_sound S_42_ok) A_42_ok B_42_6_ok C_42_7_3
  exact buildBucketsBT_of_mem (forall_append (forall_append (forall_append (hm0) hm1) hm2) hm3)
def U_42_8_0 : List Nat := ([4,5,6,8,11,14]++r 16 8)
def P_42_8_0 : BT (Option BoundPool) := buildPoolsSubBT 9 W_42 r_42 S_42 ps_42 U_42_8_0
def N_42_8_0 : List NodeSpec := [e6 [405] [4,6],e6 [410] [4,6],e6 [365] [4,6],e6 [411] [4,6],e6 [415] [4,6],e6 [420] [4,6],e6 [528] [4,6],e6 [374] [4,6],e6 [527] [6,4],e6 [495] [6,4],e6 [303] [6,4],e6 [483] [6,4],e6 [316] [6,4],e6 [330] [6,4],e6 [462] [5,4,11,8],([175,170,0,2,3,4,138],[5,11,4],[0]),([352,0,86,1,2,3,4],[11,8,4],[]),([396,1,2,3,79,4,5],[4,14],[]),e6 [474] [4,14],([91,0,92,29,3,4,5],[4,14],[0]),e6 [407] [4,14],([91,233,241,0,3,4,5],[4,14],[0]),([67,0,6,2,3,10,5],[5,4,14],[0]),([15,67,16,0,2,3,5],[5,14,4],[0]),([48,0,6,2,3,10,5],[6,5,16,11],[0]),([409,1,2,3,79,4,5],[4,17],[]),e6 [434] [4,17],e6 [381] [6,17,11],([176,1,2,3,251,4,5],[17,4],[]),([221,0,6,2,3,10,5],[5,6,18],[0]),([0,6,2,3,34,10,5],[5,18,11],[0]),([0,6,2,44,3,10,5],[5,18,11],[0]),([38,0,6,2,3,10,5],[6,18,11],[0]),([6,81,2,3,10,5],[8,5,18,14],[0]),([14,0,6,2,3,5],[8,18,5],[0]),([195,0,6,2,3,10,5],[11,5,6,18],[0]),([76,0,6,2,3,10,5],[11,18,5,6],[0]),([0,6,2,3,10,5,42],[14,5,18,6],[0]),([6,2,3,79,10,5],[17,18,14,8],[0]),([0,6,2,3,10,5,7],[18,11,14,6,5],[0]),([14,0,2,3,5],[8,19,18],[0]),e6 [372] [4,11,20,5],e6 [38,409] [4,17,21],e6 [345] [4,21],e6 [299] [4,21],([1,2,3,110,490,4,5],[4,21,8],[0]),([0,1,2,110,34,4,5],[5,17,20,21],[]),([512,270,1,2,3,4,5],[8,21,4],[]),([270,76,0,1,2,4,5],[11,8,14,21],[0]),e6 [38,350] [17,11,21,6],([0,272,2,3,206,4,5],[21,4],[]),([48,16,0,1,3,34,4,5],[4,6,21,23,17,14],[0]),([213,280,0,1,2,4,5],[4,8,23,22],[]),([526,1,2,3,4,5,454],[4,23,8],[]),e6 [191,427] [4,23,17],u6 [146,152] [4,23,21],([16,0,117,2,3,4,5],[5,4,22,23,14],[0]),([435,1,2,3,4,5,400],[5,8,23,14],[]),e6 [90,117] [5,11,4,23,22],([67,0,1,2,3,4,42],[5,23],[]),e6 [534] [5,23],e6 [480] [5,23],e6 [523] [5,23],([213,0,2,3,4,138,5,83],[5,23],[0]),e6 [463] [5,23],([241,0,117,2,3,4,5],[5,23],[]),([241,0,274,2,3,4,5],[5,23],[]),([213,159,0,2,3,4,5,83],[5,23],[]),e6 [436] [5,23],e6 [356] [5,23],e6 [369] [5,23],e6 [385] [5,23],e6 [505] [5,23],e6 [520] [5,23],u6 [117,101] [5,23,4],([1,375,2,3,79,4,5],[8,17,21,23],[]),([360,363,1,2,3,4,5],[8,23,4],[]),([175,0,2,3,242,4,5],[8,23,4],[0]),([90,281,1,2,3,79,4,5],[8,23,4,17],[]),([1,2,3,79,179,4,5],[8,23,17,21],[]),e6 [481] [11,23],e6 [416] [11,23],e6 [508] [11,23],e6 [418] [11,23],([0,1,291,2,3,52,5],[11,23],[]),e6 [514] [11,23],e6 [276] [11,23],e6 [318] [11,23],e6 [522] [11,23],e6 [319] [11,23]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_42_8_0 : checkNodesBT W_42 g_42 F_42 P_42_8_0 A_42 B_42_7 8 N_42_8_0 = true := by decide +kernel
def U_42_8_1 : List Nat := [4,5,6,8,11,13,14,17,18,21,22,23,25,28,29,30]
def P_42_8_1 : BT (Option BoundPool) := buildPoolsSubBT 9 W_42 r_42 S_42 ps_42 U_42_8_1
def N_42_8_1 : List NodeSpec := [e6 [311] [11,23],([90,233,0,1,2,3,52,5],[11,23,4,22],[]),e6 [501] [11,23,8],([48,67,16,0,1,3,4],[13,6,23,14,21,5,11],[0]),e6 [414] [14,23],e6 [387] [14,23],e6 [354] [14,23],u6 [43,6] [17,21,23,4,6,22,18],e6 [90,395] [21,11,23],e6 [455] [21,23,4],e6 [43] [21,23,4],([16,0,117,2,3,4,5,7],[22,4,23,5,14],[0]),e6 [357,7] [22,23,4,8],e6 [117,7] [22,23,4,8],e6 [459,7] [22,23,4,8],([0,292,2,3,206,4,5],[23,4],[]),e6 [90,213,445] [23,4],([90,1,394,2,3,79,4,5],[23,4,14,17],[]),e6 [321,191] [23,4,17],u6 [193,117] [23,4,22],u6 [86,186] [23,5,4],([175,352,0,1,2,3,4],[23,8,4],[]),([1,291,2,3,79,4,5],[23,8,4,17],[]),e6 [426] [23,11],e6 [332] [23,11],([398,1,2,3,79,4,5],[23,14],[]),e6 [355] [23,14],e6 [251,7] [23,14,4],([195,6,1,2,3,79,4,5],[23,14,4,17],[0]),([90,233,241,0,3,4,5],[23,17],[0]),([1,2,3,79,4,5,310],[23,17,4,8],[]),e6 [259,83] [23,21,4],([233,1,101,3,79,4,5],[25,4],[]),([296,1,2,3,79,4,5],[25,4,8,23],[]),e6 [90,336] [25,6,11,4,23,17],([92,29,3,79,4,5],[25,8,23,4,17],[0]),([1,2,3,244,245,4,5],[25,23,4,8],[0]),e6 [213,310] [25,23,4,11,8,22],e6 [531] [4,28,21],e6 [430] [4,28,23],e6 [478] [5,28,21,23],([210,1,2,79,4,5],[8,23,21,28],[0]),([213,0,2,3,475,4,5],[8,23,28,5,21],[]),([1,2,217,79,4,5],[8,28,4,14,17],[0]),e6 [217,39] [22,17,6,5,4,28],([1,2,29,3,79,4,5,209],[23,4,14,28],[0]),e6 [467,213] [23,28,21],u6 [87,138,7] [28,4,23],e6 [104,433] [28,17,6,5,21,4],u6 [213,101,228] [28,23,5,21],e6 [506] [28,23,5,21],([233,241,0,3,4,5,209],[4,23,8,25,29],[0]),([90,91,241,0,1,2,3],[29,23,14],[0]),e6 [336,89] [4,5,30,23,6,21],([191,0,1,2,29,3,5,209],[4,23,30],[0]),u6 [146,87,7] [4,28,30,23],([360,0,1,2,3,89,4],[4,30],[]),([175,159,0,2,3,206,4,5],[4,30,23],[]),e6 [446] [4,30,23],e6 [421] [5,14,30],e6 [213,392] [5,28,30,23,21],e6 [38,281] [5,30,4,23],e6 [48,281] [5,30,11,23],u6 [229] [6,23,21,30],([170,0,1,2,3,4,171],[6,30,23],[0]),e6 [457] [11,17,30],([233,241,0,3,89,4,5],[17,30,23,4,29],[0]),u6 [210,159] [21,23,30],e6 [361,39] [22,5,11,4,23,30],u6 [101,174] [22,23,28,30],e6 [29,276] [22,23,30],([233,0,1,101,3,4,5,7],[23,4,6,25,30],[]),e6 [398,191] [23,4,30],e6 [281,7] [23,5,11,30],e6 [360,159] [23,14,25,30],e6 [294,7] [23,22,4,30],e6 [443,213] [23,28,4,30,5],e6 [306] [23,30],e6 [344] [23,30],([90,0,92,29,3,4,5],[23,30],[0]),e6 [206,337] [23,30,4],e6 [472,213] [28,23,5,4,30],e6 [518] [28,30,4,21],e6 [431] [30,4,14],e6 [282] [30,4,21],e6 [307] [30,4,21],e6 [48,251] [30,14,4,23],u6 [92,145] [30,17,23],u6 [285,145] [30,17,23,4,22],e6 [175,145] [30,17,23,14]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_42_8_1 : checkNodesBT W_42 g_42 F_42 P_42_8_1 A_42 B_42_7 8 N_42_8_1 = true := by decide +kernel
def U_42_8_2 : List Nat := ([4,5,6,8,11,12,14,17,18]++r 20 4++[25]++r 27 5++[33,37,39,40,41,44,45])
def P_42_8_2 : BT (Option BoundPool) := buildPoolsSubBT 9 W_42 r_42 S_42 ps_42 U_42_8_2
def N_42_8_2 : List NodeSpec := [e6 [396,38] [30,21,4,5],e6 [517] [30,23],e6 [191,400] [30,23,4,17],e6 [175,216] [30,25,23,14],e6 [175,334] [30,25,23,14],e6 [470] [4,21,31,8],e6 [468] [4,23,8,31],e6 [428] [4,23,8,31],u6 [271] [4,23,8,31],e6 [453] [4,23,8,31],e6 [524] [4,23,31,8],([1,81,2,3,110,4,5],[4,31,8,22],[0]),e6 [364] [4,31,8,23],e6 [487] [8,23,31,4],e6 [368] [8,23,31,4],e6 [492] [8,23,31,4],e6 [423] [8,23,31,4],e6 [425] [8,23,31,14],u6 [6,104,110] [22,21,17,5,23,33,4,6],u6 [71,7] [4,28,14,37,23],e6 [348] [6,37,21],e6 [38,179] [17,23,37,6],u6 [38,6] [17,37,6,11,25,23,21],([1,2,3,79,4,138,5,83],[23,4,5,28,14,37,25],[0]),([86,1,101,2,3,79,4,5],[23,4,25,37,21,28,5],[0]),e6 [331] [37,4,21],e6 [362] [37,4,21],e6 [38,272] [37,4,21,25],e6 [333] [37,4,23],u6 [37,6,7] [23,37,6,22,5,39],([0,1,2,206,109,4,5],[6,40,11,21],[]),e6 [401] [11,23,31,8,40],([170,0,157,2,3,4,5],[11,40,21],[]),e6 [213,291] [23,11,28,40,30],([396,0,2,3,206,4,5],[40,4,14],[]),([396,0,2,29,3,4,5],[40,5,14,21,30],[]),([302,0,2,3,206,4,5],[40,6,4],[]),([328,0,2,3,206,4,5],[40,6,4],[]),e6 [351] [40,21,4],([0,296,2,3,4,5,83],[40,23,6],[]),([0,281,2,3,4,5,83],[40,23,11],[]),e6 [230,209] [4,23,21,28,41],u6 [6,211] [21,22,4,41,23,18,6,5],e6 [29,287] [22,23,41,4,30],e6 [206,171] [23,41,4,30],e6 [533] [4,11,20,44],e6 [450] [4,11,44,20],u6 [252] [4,21,20,44],u6 [235] [4,21,20,44],u6 [260] [4,23,31,44],u6 [174,138] [4,44,22,23,30,11,28],e6 [535] [5,4,8,44],e6 [513] [6,23,30,44],e6 [317,206] [8,41,23,4,17,44],e6 [536] [11,20,44,4],e6 [445] [11,20,44,28],e6 [380] [11,21,4,28,20,44],e6 [346] [11,21,20,44,4,28],e6 [233,276] [11,22,23,4,25,44],e6 [521] [14,20,44,4],e6 [417] [21,23,4,44,30],u6 [29,255] [22,4,25,44,14],([38,210,0,1,2,4,5],[23,30,44,6],[]),([38,280,0,1,2,4,5],[23,44,4,22],[]),([298,1,2,3,79,4,5],[44,4,37,23,14],[]),e6 [90,298] [44,14,11,4,23],([184,47,1,2,3,4,5],[44,21,23,17],[0]),e6 [90,367] [44,22,6,4],([233,241,3,79,4,5],[44,23,4,25,14],[0]),([159,92,1,3,79,4,5],[44,25,4],[]),([76,233,0,1,101,3,4,5],[44,25,4,23],[]),e6 [366] [4,30,45],([91,0,1,2,3,4,236],[4,45],[0]),e6 [448] [5,14,45],e6 [353] [5,14,45],e6 [213,337] [5,23,45,28,30,4],e6 [477] [5,28,45],e6 [510] [6,37,8,45],e6 [301] [11,21,45,40,8],u6 [189] [11,45,30],e6 [48,270] [21,4,6,25,45],e6 [159,178] [21,14,4,45,44,23,25],e6 [48,361] [22,30,4,5,23,45],u6 [36,15,7] [23,4,5,45,27],e6 [52,400] [23,22,5,28,14,45],u6 [15,37,7] [23,37,5,45,27],([90,91,38,0,1,2,3],[29,23,45,30,4,12],[]),u6 [220] [30,45,23],e6 [502] [40,8,21,45],e6 [488] [45,21,40,8]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_42_8_2 : checkNodesBT W_42 g_42 F_42 P_42_8_2 A_42 B_42_7 8 N_42_8_2 = true := by decide +kernel
def U_42_8_3 : List Nat := ([4,5,6,8,11,14,17]++r 20 4++[25,28,30,31,37,40,41]++r 44 4++r 50 4)
def P_42_8_3 : BT (Option BoundPool) := buildPoolsSubBT 9 W_42 r_42 S_42 ps_42 U_42_8_3
def N_42_8_3 : List NodeSpec := [e6 [335] [45,23,40,8],e6 [305] [45,23,40,8,44],e6 [486] [45,40,8,23],([300,1,2,3,79,4,5],[4,17,21,23,14,46],[]),([0,1,2,3,251,5,209],[4,23,46],[]),e6 [379] [4,31,46,23,6],e6 [465] [4,45,46,23],e6 [461] [4,45,46,23],([442,1,2,3,79,4,5],[4,46,23,25],[]),e6 [504] [5,4,46,23],e6 [373] [5,46,23,4],([0,1,2,244,4,5,7],[21,23,4,40,46],[]),([90,1,2,3,79,4,5],[23,8,4,46,17],[]),([1,2,3,109,120,4,5],[23,14,21,46],[0]),u6 [16,39,7] [23,46,28,4,14,5,6],([328,1,2,3,79,4,5],[25,4,23,46],[]),([314,1,2,3,79,4,5],[25,4,23,46],[]),([1,2,3,79,4,5,236],[25,23,4,46,17],[]),e6 [473] [28,23,5,46,30,4],e6 [86,334] [30,4,37,45,23,46],e6 [404] [30,46,23,37],([302,0,2,3,4,10,5],[40,4,6,20,46],[]),([161,1,2,3,79,4,5],[44,4,23,46,37,17],[]),([0,1,2,3,216,5,209],[45,23,46],[]),e6 [406] [45,46,23,4],e6 [442,7] [46,4,14,23,30,25],u6 [10,39,7] [46,22,11,14,23,37,6,5,4],e6 [284,7] [46,22,23,4,6,25],e6 [241,255] [46,22,23,4,25,8],e6 [296,7] [46,22,23,25,4,6],e6 [314,7] [46,22,23,25,4,6],e6 [76,442] [46,23,4,30,25,14],([302,1,2,3,79,4,5],[46,25,4],[]),e6 [358] [6,23,44,47],([444,1,2,3,79,4,5],[8,25,23,47,28],[]),e6 [211] [21,23,4,47,8],e6 [289,191] [23,4,17,47,8,14],([1,2,3,312,516,4,5],[23,4,47],[]),e6 [315] [23,6,8,47],e6 [352,233] [23,6,25,4,22,47],([360,90,0,1,2,3,4],[23,47,4],[]),e6 [206,310] [23,47,25,8,41,4],([1,451,3,79,4,5],[25,8,47,23],[]),([191,210,0,1,2,4,5],[30,23,47],[]),e6 [275] [40,21,5,23,8,47],([0,274,2,3,4,5,83],[40,23,30,47],[]),e6 [382] [45,21,47,8],e6 [440] [45,23,47,8],([384,280,1,2,3,4,5],[47,4,23],[]),([191,0,1,2,3,286,5],[47,23,4],[]),([90,0,1,2,3,290,5],[47,23,11],[]),([0,1,2,3,145,5,143],[21,23,50],[0]),e6 [277,98] [22,4,30,20,17,50],e6 [48,145] [30,17,23,4,51,6,5],u6 [70,10] [14,11,52,5,4,23,21,37],([0,1,2,3,4,236,209],[4,23,40,20,53],[]),e6 [484] [5,23,8,31,53,47],e6 [429] [5,23,31,22,6,47,53],([0,1,2,3,4,42,39],[5,23,40,20,53],[]),e6 [497] [5,31,23,53,47],u6 [16,109] [6,21,23,14,11,53],([0,1,2,3,4,83,171],[6,23,40,20,53],[]),e6 [456] [6,23,53,47],e6 [493] [6,23,53,47],e6 [359] [6,23,53,47],([0,1,2,206,325,4,5],[6,40,20,53,21],[]),e6 [424] [21,4,28,20,53],u6 [247] [21,23,30,37,40,53],([0,1,2,109,4,52,5],[21,45,6,20,53],[]),e6 [159,376] [22,5,23,53,47],e6 [339] [23,6,53,47],e6 [329] [23,6,53,47],e6 [304,83] [23,8,22,40,37,53,45],e6 [507] [23,8,53,21,4],e6 [138,376] [23,22,5,53,47],e6 [376] [23,28,53,47],e6 [390] [23,47,53,28],([308,0,1,2,3,179,5],[23,53,6],[]),([0,1,2,3,145,5,209],[23,53,30],[]),u6 [231] [28,8,31,23,53,47],([328,0,2,3,4,5,83],[40,23,6,53],[]),e6 [498] [40,23,31,8,53],e6 [42] [40,23,53,8,31],e6 [466] [40,23,53,8,31],e6 [90,213] [40,53,11,28,22,23],([409,0,1,2,3,52,5],[53,4,11,5],[]),([409,0,1,2,3,138,5],[53,5,4,46],[]),([300,0,1,2,3,10,5],[53,6,14,20,21],[]),([0,350,1,2,3,52,5],[53,21,4,28],[]),e6 [90,230] [53,21,11,5,23,28]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_42_8_3 : checkNodesBT W_42 g_42 F_42 P_42_8_3 A_42 B_42_7 8 N_42_8_3 = true := by decide +kernel
def U_42_8_4 : List Nat := ([4,5,6,8,11,12,14,17,18]++r 20 4++[25,28,30,31,37,40]++r 44 4++[49,50,51,53,55,57,58,60,61,63,64])
def P_42_8_4 : BT (Option BoundPool) := buildPoolsSubBT 9 W_42 r_42 S_42 ps_42 U_42_8_4
def N_42_8_4 : List NodeSpec := [([442,0,1,2,3,5,209],[53,23,4],[]),([442,0,1,2,3,52,5],[53,23,4,45],[]),e6 [496] [23,40,47,53,21,55,28],u6 [36,117] [23,55,4,22,45,12],e6 [36,145] [30,17,23,4,51,12,25,6,55],e6 [287] [4,23,57,31],e6 [371] [4,57,31,21],e6 [273] [21,31,57,4],e6 [322] [21,31,57,4],([176,1,2,3,178,4,5],[23,5,31,57,4],[0]),([1,2,3,178,509,4,5],[23,14,57],[0]),([46,1,2,3,4,5,45],[23,57,21],[0]),e6 [110] [40,21,31,57,5,20,53],e6 [293] [40,23,31,57,21],e6 [178] [40,23,31,57,21],e6 [485] [57,23,31,4],e6 [519] [57,23,31,4],e6 [378] [57,23,31,4],e6 [439] [57,23,31,4],e6 [532] [57,23,31,4],e6 [313] [57,23,31,4],e6 [452] [57,23,31,4],e6 [530] [57,23,31,4],([0,86,2,3,4,138,83],[5,4,58],[0]),([159,0,86,2,3,4,83],[5,21,23,30,58],[0]),([175,170,0,101,2,3,4],[58,23,6,5,4],[0]),e6 [476] [4,60],e6 [525] [4,60],e6 [297] [4,60],e6 [38,251] [4,60,23],([213,47,0,1,2,4,5],[5,8,60,21],[]),e6 [503] [5,23,31,4,60,8],e6 [347] [6,60,17,11],e6 [213,300] [11,23,60,30,21,5],([38,16,0,1,3,4,5,39],[14,60,6,21,23,17,4],[0]),e6 [482] [21,23,28,4,60],u6 [48,217] [22,4,28,6,60,23],e6 [399,98] [22,23,60,30,40,14,50],e6 [110,39] [22,25,21,5,60,4],u6 [16,70] [22,37,14,60],u6 [36,16,7] [23,4,28,60,6,49],u6 [48,16,7] [23,4,60,6,14],([308,0,1,2,3,145,5],[23,60],[]),e6 [408] [23,60],([0,1,2,206,4,98,5],[30,40,21,60,46],[]),e6 [500] [37,60,45,21],u6 [205,98] [46,22,30,4,50,60],([300,0,1,2,3,52,5],[53,23,21,30,60],[]),([16,0,298,2,3,4,5],[60,4],[]),([191,47,0,1,2,4,5],[60,5,21,47],[]),e6 [309] [60,23],e6 [413] [60,23,40,8,44],([0,1,2,34,4,98,5],[60,30,21,20,53],[]),u6 [16,8,7] [23,4,28,6,14,61,60,49],e6 [118,145,7] [28,4,30,61],([48,15,16,0,2,3,5],[6,5,45,11,63],[0]),e6 [234,7] [4,17,6,61,64],([159,1,2,3,79,4,5,83],[4,23,28,14,45,64,25,37,17],[0]),([170,1,2,3,79,4,138,5],[4,37,25,64,28,14],[0]),([159,86,1,2,3,79,4,5],[5,21,4,28,37,47,17,64],[0]),u6 [225] [5,45,64],u6 [48,117] [5,64,23,4,45,60],e6 [48,274] [5,64,23,45],e6 [377] [6,17,64],u6 [197] [6,64,8,45],([170,0,164,2,3,4,5],[11,40,64],[0]),([259,76,0,1,2,4,5],[11,44,21,64],[0]),([230,76,0,1,2,4,5],[14,8,21,64],[0]),([91,0,1,2,192,3,5],[14,53,64],[0]),e6 [386] [14,64,21,8,4],e6 [48,207] [17,4,6,21,64,25,23],e6 [76,234] [17,4,64],e6 [48,179] [17,23,64,6],u6 [48,6] [17,64,6,4,25,21,23],u6 [44,110] [21,4,17,18,64],u6 [161,7] [22,4,17,23,30,45,64],u6 [159,250] [22,4,64],e6 [52,427] [23,4,14,47,22,64],([170,1,101,2,3,79,4,5],[23,6,37,17,21,28,64,4],[0]),u6 [216,7] [23,30,4,28,64,45],e6 [76,161] [23,64,4],u6 [48,15,7] [23,64,4,5,45,11],e6 [349] [23,64,5,6],e6 [48,433] [28,17,21,4,64,60,6,5,23],e6 [479] [28,53,47,64],u6 [219] [30,45,64],u6 [243] [30,45,64],([0,1,2,250,34,4,5],[40,20,4,64],[]),e6 [90,296] [53,11,4,64],e6 [489] [64,4]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_42_8_4 : checkNodesBT W_42 g_42 F_42 P_42_8_4 A_42 B_42_7 8 N_42_8_4 = true := by decide +kernel
def U_42_8_5 : List Nat := ([4,5,6,8,11,14,17,18]++r 20 4++[25,28,30,31,37,40]++r 44 4++[50,53,55,59,60,61]++r 64 4++[72,73,74,77,78,79,81]++r 83 4)
def P_42_8_5 : BT (Option BoundPool) := buildPoolsSubBT 9 W_42 r_42 S_42 ps_42 U_42_8_5
def N_42_8_5 : List NodeSpec := [([76,159,0,92,1,3,4,5],[64,4],[]),e6 [48,403] [64,5,21,25,60],([91,0,1,2,3,186,5],[64,23],[]),([170,0,168,2,3,4,5],[64,23],[]),e6 [340] [64,23,4],e6 [529] [64,23,4],e6 [76,164] [11,23,4,65,64],e6 [76,6] [17,23,4,6,11,65,64],e6 [76,314] [47,25,46,23,65,4],u6 [212,98] [65,4,14,60,23,21,50],u6 [168,89] [65,23,60,4],([0,1,2,3,4,287,7],[4,23,66,53],[]),u6 [71] [4,28,14,44,20,66],e6 [511] [8,6,31,66,21,14,11],([0,1,2,276,4,5,7],[11,23,66,53],[]),u6 [265] [11,66,21,5,6],([0,1,2,178,4,5,7],[14,40,23,66],[]),([0,6,1,2,110,4,5,7],[21,22,4,66,18,5,11],[0]),([360,0,1,2,3,4,7],[23,66,4,8],[]),([280,0,1,2,4,5,7],[23,66,21,4,47],[]),([352,0,1,2,3,4,7],[23,66,21,4,47],[]),([47,0,1,2,4,5,7],[23,66,21,5,44,60],[0]),([35,0,1,2,3,4,7],[23,66,21,44],[0]),e6 [469] [23,66,53,28],([0,1,2,3,4,376,7],[28,40,23,66],[]),e6 [393] [30,66,21,14,17],([0,1,2,3,4,45,7],[37,23,20,66],[0]),([0,1,2,49,4,5,7],[64,23,20,66],[0]),([0,1,451,3,4,5,7],[4,28,23,11,25,67,30],[]),([196,0,1,2,3,5,7],[21,4,23,60,67],[0]),([278,0,2,3,4,5,7],[21,23,4,67,30],[]),([150,0,1,3,4,5,7],[21,23,4,67,60],[0]),([0,1,2,3,23,5,7],[21,23,61,5,30,44,67],[0]),([0,1,8,3,4,5,11],[21,23,67],[0]),u6 [129,7] [22,4,28,23,45,25,61,30,67],e6 [375,7] [22,23,8,25,4,28,5,45,67,53],u6 [155,7] [23,22,4,28,8,67,53],u6 [154,7] [23,22,4,28,30,60,67,45],e6 [145,7] [23,22,4,28,30,67],u6 [23,7] [23,22,4,28,61,5,30,44,67],e6 [491] [23,53,21,4,67],([36,37,0,1,3,4,5],[23,60,21,67],[0]),([1,2,3,79,251,4,5],[4,17,72],[0]),([1,2,234,3,79,4,5],[4,17,72],[0]),([350,1,2,3,79,4,5],[8,17,21,72,47],[]),([1,2,3,79,4,5,454],[23,4,8,72,31],[]),([1,2,3,79,4,5,427],[23,4,14,44,17,72],[]),([438,1,2,3,79,4,5],[23,4,31,72,17],[]),([281,1,2,3,79,4,5],[23,44,5,4,72,14],[]),([272,1,2,3,79,4,5],[25,4,72,14],[]),([1,2,3,79,4,5,400],[25,23,72,14],[]),([164,1,2,3,79,4,5],[44,72,4,31,23,46,37,17],[0]),([175,1,2,3,79,4,5],[46,25,23,72,4],[]),([292,1,2,3,79,4,5],[46,25,23,72,4],[]),([6,1,2,3,79,4,5],[47,25,4,72,23,46,17],[]),([191,233,241,0,3,4,5],[4,30,73],[0]),([76,233,241,0,3,4,5],[23,64,73],[0]),([233,241,0,3,4,5,7],[73,28,4,14,23,30],[0]),([6,1,81,104,2,3,4,5],[5,46,14,22,74,17],[0]),u6 [38,195,6] [11,23,5,22,64,77,18],([38,0,6,1,44,3,4,5],[5,37,6,4,55,78,64,18],[0]),u6 [75,6] [17,37,21,11,55,78,18,4],u6 [72,6] [17,64,23,4,55,78,5],e6 [175,304] [78,5,21,14,45,53,23],e6 [175,198] [78,23,14,30],([38,6,1,81,2,3,4,5],[17,14,44,78,22,4,18,79],[0]),u6 [146,29,7] [4,30,23,81],u6 [263,7] [23,6,83,4,61,67],u6 [204,7] [23,45,83,4,28,67,61],([175,159,170,0,2,3,4],[5,30,59,84],[0]),([175,0,1,101,3,138,5],[44,5,78,23,84],[0]),e6 [48,213,433] [28,4,45,5,85],u6 [48,213,214] [28,5,60,22,85],e6 [90,213,391] [28,23,85,4],([175,176,2,3,206,4,5],[8,23,86],[0]),e6 [464] [8,86,53,23,4],u6 [43,6,42] [11,4,86,21,18],u6 [48,6,42] [23,5,86,46,6],([317,1,2,3,79,4,5],[23,8,4,46,86],[]),([175,159,1,2,3,79,4,5],[23,14,5,37,47,17,86,59],[]),u6 [52,236] [23,86,4],([1,2,3,79,4,5,42],[23,86,4,8,17],[]),e6 [447,236] [23,86,6,4,30],([1,2,3,79,4,5,337],[23,86,17,45,4,8],[]),([1,2,3,79,4,5,383],[23,86,47,4,8],[]),([240,6,1,2,3,4,5],[31,17,4,86,18],[0]),([0,117,2,3,4,5,83],[40,23,86,4],[0]),e6 [422] [40,23,86,4,53],([0,298,2,3,4,5,83],[40,23,86,4,60],[]),e6 [494] [40,23,86,8,47]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_42_8_5 : checkNodesBT W_42 g_42 F_42 P_42_8_5 A_42 B_42_7 8 N_42_8_5 = true := by decide +kernel
def U_42_8_6 : List Nat := (r 3 4++[8,9]++r 11 4++[16,17,18,21,22,23,25,28,30,31,33,37,39,40,41]++r 44 4++r 49 7++[57,58,60,61]++r 64 4++[78,79,81,83,84,86,87,89,90,93,95,106,107,108,114,117]++r 120 25)
def P_42_8_6 : BT (Option BoundPool) := buildPoolsSubBT 9 W_42 r_42 S_42 ps_42 U_42_8_6
def N_42_8_6 : List NodeSpec := [e6 [432] [40,23,86,8,47],u6 [6,42,211] [86,4,21,18,30],([76,0,1,2,3,4,236],[86,4,23],[]),e6 [191,236] [86,4,23,21],e6 [471,236] [86,4,53,45],u6 [218,171] [86,5,23,11,6,30,4],e6 [324,171] [86,6,40,41,30],e6 [94] [86,8,23,4],e6 [402] [86,8,31,23,53,47],([0,1,2,3,4,236,7],[86,23,4,40,66],[]),([0,1,2,3,4,42,7],[86,23,4,40,66,53],[]),([0,1,2,3,179,5,209],[86,23,53,4,8],[]),([0,1,2,3,198,5,209],[86,23,53,30,5],[]),e6 [370] [86,23,53,47,8],([76,0,1,2,3,4,42],[86,53,23,4],[]),e6 [342] [86,57,31,23,53,30,40],u6 [6,104] [5,87,14,21,23,4,53],([0,6,104,2,3,10,5],[6,14,87,8,40,33,13],[0]),([15,16,0,104,2,3,5],[11,6,87,8,14,4,13],[0]),([175,308,170,0,2,3,4],[23,58,6,87,8,5,84],[]),u6 [104,207] [87,14,21,60],u6 [48,6,110] [89,4,22,21,17,5,23,16],([15,16,0,2,3,5,39],[5,17,8,41,13,11,90,6],[0]),e6 [48,191,343] [4,30,6,60,93],u6 [48,191,238] [4,60,5,17,93],e6 [308,174] [87,23,4,21,28,95,6],([92,1,2,3,79,89,4,5],[17,23,106,4],[0]),([0,6,2,3,10,5,39],[5,17,8,41,107,13,11,9,6],[0]),u6 [6,44,7] [108,37,4,23,64,18,30,5,55],u6 [146,87] [8,47,4,54,114,23,22,81],u6 [159,87,7] [28,23,5,6,114,67],([48,6,1,81,2,3,4,5],[79,5,46,78,22,117,60],[0]),([0,1,144,3,4,5,7],[21,23,4,6,67,120],[0]),u6 [139,7] [23,11,83,4,28,67,120],u6 [29,145,7] [23,28,37,61,120,30,67,4],([193,146,0,1,2,3,5],[23,120,21,67],[0]),u6 [87,145,7] [28,120,4,61,23,67],([0,86,2,3,34,4,83],[5,23,121,58],[]),([183,0,2,3,4],[8,121,58],[0]),([0,117,2,3,4,5,152],[21,23,4,121,67],[0]),([0,283,2,3,4,5,7],[21,23,4,121,67,60],[]),([0,279,2,3,4,5,7],[21,23,4,121,67,120],[]),e6 [283,7] [22,23,4,121],e6 [279,7] [22,23,4,121],([175,1,2,3,458,4,5],[23,31,14,121],[]),e6 [298,7] [23,44,14,4,28,121],e6 [274,7] [23,47,14,4,28,121],([86,2,3,79,4,83],[46,121,23,14,28,4,8],[0]),u6 [118,7] [22,4,37,23,30,120,17,55,122],u6 [145,188,7] [61,30,123,4,50,120],u6 [37,16,7] [23,4,6,5,124,49],e6 [146,37] [23,52,5,124,81],u6 [233,145,7] [4,61,120,23,125],u6 [159,117,7] [4,125,5,23,120,61,30],([147,0,2,3,4,5,7],[21,23,125,67,30],[0]),([210,0,1,2,4,5,7],[21,66,23,125,30],[]),u6 [6,7,211] [22,21,23,4,18,125],u6 [6,7] [65,4,37,23,21,125,6,5,11],e6 [117,145,7] [4,120,61,30,125,23,126],u6 [117,145] [30,17,22,4,5,23,120,125,126],u6 [8,10,7] [14,11,21,22,4,23,5,128,6,3],u6 [117,8] [22,5,127,23,125,128,45,4],u6 [36,10,7] [23,4,5,21,22,128,6,3],u6 [36,6,7] [23,4,125,5,22,21,128,55,6,39],u6 [8,145] [30,17,23,6,25,4,120,128,12],([159,0,92,1,3,4,5,7],[128,23,4,25,30],[0]),([159,0,1,8,3,4,5,7],[128,23,45,25,4,6,67,12],[0]),u6 [117,156,7] [23,4,129,5,125],([288,1,2,3,4,5,287],[4,23,57,130],[]),([308,170,1,2,3,79,4,5],[17,6,21,28,4,23,130,95],[]),([274,1,2,3,79,4,5],[47,4,44,23,130,14],[]),e6 [460] [130,44,46,23,4],e6 [295] [45,131,64],([48,191,67,0,1,3,4],[60,13,132,6,5,21,133],[]),([48,67,0,1,3,4,52],[134,45,21,5,6,133],[]),u6 [198,7] [23,44,4,28,61,5,30,135,136,107],u6 [37,10,7] [37,23,6,22,5,3,137],u6 [37,87] [44,23,17,114,137,22,124],u6 [59] [11,17,22,138,23,40,8],e6 [204] [45,139,8,40,64,23],u6 [139] [4,83,140,8,23,11,120],u6 [16,7,11] [23,28,4,14,5,141,49,61,6],u6 [87,11] [17,23,142,141,22,41,121,30,4],u6 [10,7,11] [21,22,11,14,4,23,37,5,3,142,6],u6 [146,11] [52,5,141,23,51,142,47,143,4,54],e6 [449] [4,5,31,144,6,23,46],([0,164,2,3,206,4,5],[5,4,144,23,6],[]),u6 [210,138] [23,21,4,144],u6 [164,7] [65,4,11,17,37,23,21,144,6],u6 [180] [144,11,23,30,21]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_42_8_6 : checkNodesBT W_42 g_42 F_42 P_42_8_6 A_42 B_42_7 8 N_42_8_6 = true := by decide +kernel
def U_42_8_7 : List Nat := ([4,5,6,8]++r 11 4++[17,18]++r 20 4++[25,28,30,31,37,40,41]++r 44 4++[50,53,55]++r 57 5++r 64 4++[72,77,78,79,83,86,89,95,102,120,121,125,128,130]++r 145 62)
def P_42_8_7 : BT (Option BoundPool) := buildPoolsSubBT 9 W_42 r_42 S_42 ps_42 U_42_8_7
def N_42_8_7 : List NodeSpec := [e6 [328,7] [46,23,4,6,146],e6 [323] [23,40,8,145,146,61,147],u6 [163,7] [4,30,17,61,12,148],([0,1,101,3,138,5,7],[4,83,23,6,149,67],[0]),([1,101,3,79,138,5],[25,23,4,149,44],[0]),([0,1,101,3,206,138,5],[4,6,150,149],[]),([76,0,1,101,3,138,5],[11,23,149,150],[]),([76,0,1,2,3,4,171],[86,6,23,151,11],[]),e6 [499] [86,31,23,40,8,151,11],([0,1,2,3,4,171,7],[86,23,61,152,6,20,66,53],[]),([1,2,3,79,4,5,171],[25,23,17,153,4,8,72],[0]),([172,1,2,3,4,5,171],[25,23,17,153,41],[0]),e6 [326] [23,21,154,155],e6 [327] [21,31,23,156,157,40,8,47,44],([0,1,2,325,4,5,7],[21,23,61,158,6,20,46,53],[]),([76,6,1,81,2,3,4,5],[14,4,5,79,46,102,159],[0]),e6 [76,328] [46,23,6,4,159],u6 [87,143] [22,23,4,160,41,121,6],e6 [38,274] [5,37,161,23,4],e6 [338] [64,23,162,45],([90,91,0,1,2,3,34],[163,23,64,164],[]),e6 [341] [4,17,60,23,8,165],e6 [159,174] [22,28,166,30,95,64],([159,170,1,2,3,79,4,5],[64,4,21,28,23,25,166,37,17,59,95],[0]),([175,177,1,2,3,4,5],[5,8,23,167,4,121],[0]),u6 [179,7] [23,22,8,17,4,28,168],u6 [84] [4,22,169,23,30,44],([0,1,101,3,138,5,83],[6,23,58,170,171],[0]),([90,91,0,1,2,3,206],[172,30,4,164],[]),([15,16,0,2,3,34,5],[5,17,173,11],[0]),([15,38,16,0,2,3,5],[6,45,11,173],[0]),([15,76,16,0,2,3,5],[11,14,5,6,173],[0]),([15,16,2,3,79,5],[47,8,17,173,14],[0]),([15,16,0,2,3,5,7],[120,125,173,11,6,5],[0]),u6 [258] [23,53,4,146,174],u6 [149,7] [65,4,175,37,23,14,45,5,11],e6 [76,375] [23,14,176],u6 [221,110] [4,5,89,25,23,177],u6 [221,195] [5,177,4,17,77],([48,0,6,1,44,3,4,5],[5,64,178,78,17,37,11],[0]),([38,0,6,1,3,4,5,39],[17,37,13,178,78,5,21,23,4],[0]),e6 [69] [37,4,6,46,23,178,60],u6 [6,69] [37,5,4,18,11,55,178],([48,0,6,1,3,34,4,5],[64,5,4,178,78,17,21,23,11],[0]),u6 [76,6,44] [64,5,178,11,102,4,23,18],u6 [116] [64,66,21,5,6,178,60,45],u6 [47,6] [5,17,23,21,178,78,179],u6 [233,98] [22,4,180,6,50,17,64],u6 [241,98] [22,23,30,180,5,50,14],u6 [92,98] [65,23,14,8,4,21,180,50],e6 [263] [6,181,128,47,53,64,23],([90,91,0,1,2,29,3],[182,30,14,23,4,21],[0]),e6 [388] [5,183,45],u6 [30] [14,184,23,37,125,53,47],u6 [30,7] [23,14,125,61,4,184],([90,91,1,2,3,79],[186,23,14,4,17,46],[]),u6 [226] [4,14,161,23,21,187],([90,0,1,2,29,3,52,5],[23,11,30,187],[]),e6 [352,29] [25,23,11,185,4,30,186,187],e6 [397] [4,23,14,30,188,44],u6 [15,109] [11,37,21,23,189,190,6,40],e6 [398,52] [17,4,28,23,14,191,5],([0,1,2,192,3,52,5],[4,28,53,192,17,45,23,14,187],[]),([1,2,192,3,79,4,5],[8,17,23,192,14],[]),u6 [192,7] [14,192,4,23,37,6,21,61,187],e6 [76,192] [23,151,14,192,64],([1,2,79,4,98,5],[14,17,193,21,46],[0]),u6 [29,98] [22,14,30,17,53,193,50],e6 [270,39] [21,25,6,5,23,4,194,41,11,30],([191,0,86,2,3,4,83],[30,4,121,195],[]),e6 [412] [57,23,31,21,196,197],([48,15,0,1,3,34,4,5],[64,45,5,23,198,11],[0]),u6 [15,49] [64,45,23,198,6,5],([48,15,1,2,3,79,4,5],[45,4,198,14,130,17,86,199],[0]),([1,2,79,250,4,5],[4,14,46,200,21],[0]),([1,2,79,325,4,5],[25,23,21,17,201],[]),([48,1,2,3,79,4,10,5],[14,202,25,45,44,86],[0]),u6 [49,10] [202,64,6,25,45,21,23,5],([48,67,0,6,1,3,4],[13,5,178,203,46,17,21,23],[0]),([76,419,0,1,3,4,5],[11,6,5,204,64],[]),([419,0,1,3,4,5,7],[11,14,4,120,128,204],[]),([419,1,3,79,4,5],[44,47,4,204,14],[]),([76,0,6,1,2,3,4,42],[4,23,5,205,14,86,18],[0]),u6 [48,6,7] [23,64,4,5,6,65,21,205],u6 [38,6,42] [23,205,6,86,5,21,18,4],u6 [6,70] [78,5,17,21,23,37,205],u6 [6,42,7] [86,4,205,18,30],u6 [44,42] [86,5,17,178,205,37],u6 [6,94] [86,14,4,23,18,6,5,205],e6 [317,213] [23,11,28,22,4,206]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_42_8_7 : checkNodesBT W_42 g_42 F_42 P_42_8_7 A_42 B_42_7 8 N_42_8_7 = true := by decide +kernel
def U_42_8_8 : List Nat := ([4,5,6,8,11,13,14,17,18]++r 20 4++[25]++r 27 5++[37,39,40,41]++r 44 4++[52,53,55,58,60,61,62,64,65,67,71,73,78,79,84,85,86,89,107,108,111,120,121,125,128,130,133,136,146,149,159,164,178,189,190,199,202,203]++r 205 70)
def P_42_8_8 : BT (Option BoundPool) := buildPoolsSubBT 9 W_42 r_42 S_42 ps_42 U_42_8_8
def N_42_8_8 : List NodeSpec := [([90,91,0,92,1,2,3],[29,23,4,206,46],[0]),([48,16,1,2,3,79,4,5],[25,4,64,14,207,17],[0]),u6 [16,49] [64,6,23,207,45,60],u6 [16,45] [6,21,23,208,41,45,53],e6 [48,157] [5,64,209,45,21,25,210,23],u6 [6,8,7] [22,21,211,125,23,4,6,5,39],u6 [6,7,11] [22,125,211,37,23,5,4,39,61,6],([48,6,1,2,3,79,4,5],[4,79,17,212,45,44,86,14],[0]),e6 [48,110] [21,28,4,212,64,53,5,25],([6,1,81,2,3,4,5,7],[4,125,108,146,22,213,18,8,5,79,14],[0]),([200,6,1,2,3,4,5],[5,8,4,213,21,18],[0]),u6 [48,10,7] [4,23,64,6,22,11,214],([48,0,1,3,34,4,10,5],[6,214,64,202,25,60,23,11,5],[0]),([87,0,6,2,3,4,5,7],[125,4,22,215,23,6,14,30],[0]),u6 [99] [4,30,216,17,21,29],u6 [15,70] [22,5,37,11,217],([15,67,1,2,3,79,4,5],[47,23,5,14,217,17,199],[]),u6 [35,16] [8,23,4,64,60,218,5,219],([15,1,104,2,3,79,4,5],[45,14,8,4,189,190,130,220],[0]),([48,67,0,1,3,206,4],[221,6,14,133,60,11],[]),([0,92,29,3,4,52,5],[4,45,222,23,14],[0]),([93,0,3,4,5],[8,73,222],[0]),([76,0,92,29,3,4,5],[14,23,222],[0]),([0,92,29,3,4,5,7],[23,28,4,14,222,30],[0]),([191,0,92,29,3,4,5],[30,4,222],[0]),e6 [437] [23,31,8,40,37,223,45],([1,2,3,79,216,4,5],[25,23,30,224,4,8,64,46],[]),e6 [213,216] [30,23,28,64,224,4],e6 [441] [4,5,23,14,225],([48,213,67,0,1,3,4],[5,226,227,11,60,21,85],[]),([213,0,1,101,3,138,5],[5,227,4,23,11,85,149],[]),([0,1,2,250,4,52,5],[4,11,40,5,228,46],[]),([0,86,2,3,4,52,83],[4,11,121,23,5,228,209],[0]),([0,1,2,244,4,52,5],[4,45,25,228,23],[]),([233,241,0,3,4,52,5],[4,45,228,23,14],[0]),e6 [280,29] [8,23,25,21,229,22,4],u6 [102] [5,230,4,6,58,21],u6 [101,250] [22,230,23,4],u6 [108,6,42] [5,86,231,6],([15,38,0,1,3,4,5,39],[5,21,23,11,45,232],[0]),([15,1,2,3,79,4,5,39],[17,23,21,5,232,220,130,190,45],[0]),u6 [199] [8,5,31,21,20,17,111,233],u6 [40] [5,14,234,31,107,71,21,6],u6 [15,47] [21,23,5,235,190,45,232],([38,0,1,3,4,10,5,39],[14,5,6,37,214,236,25,60,21,23],[0]),([1,2,3,79,4,10,5,39],[17,236,25,14,37,28],[0]),u6 [47,10] [234,14,21,235,23,6,236,52,5,60],([195,0,6,1,2,3,4,7],[23,205,4,65,64,21,237,18,5],[0]),u6 [6,222] [65,4,8,17,64,21,237,205,18,6],([0,92,29,3,89,4,5],[30,14,238,23,29],[0]),e6 [213,198] [5,30,28,107,23,11,239,4],([1,2,3,79,198,4,5],[23,239,17,8,4,136],[0]),u6 [6,82,42] [86,17,5,205,23,240,6],([6,1,104,2,3,79,4,5],[17,14,241,242,243],[0]),([0,1,2,110,4,5,7],[21,4,244,40,61,5,46],[]),u6 [15,7,11] [5,23,4,245,125,27,45],u6 [15,8,7] [23,4,128,45,245,125,5,27],u6 [15,39,7] [23,46,4,5,11,245,45],([0,92,29,3,4,5,209],[23,45,8,25,246,29],[0]),u6 [53] [4,28,17,247,45,46,23],u6 [221,6,7] [37,6,5,146,248,4,23,18],u6 [213,171] [86,23,6,11,249,40,28,41,21,30],u6 [151,7] [46,22,250,4,23,37,61,6,60,14],u6 [6,116] [64,5,17,251,55,178],u6 [35,15] [23,64,5,218,252],u6 [145,148,7] [23,37,60,67,253,120],u6 [124] [30,254,44,20,11],u6 [124,7] [254,22,30,62,120,4,23,37,11],([90,91,213,0,1,2,3],[255,4,11,21,23,60,164],[]),([6,1,2,3,79,4,5,42],[4,17,256,86,14,18],[]),u6 [110,42] [4,256,86,22,18,5,23,89,11],([1,81,2,3,4,5,42],[53,5,256,4,14,25,22],[0]),([48,67,0,1,3,4,10],[257,6,11,14,46,203,23,21],[0]),([76,0,1,451,3,4,5],[11,23,258],[]),e6 [76,221,6] [6,5,23,64,159,259,4,18],u6 [6,39,7] [65,125,211,37,23,21,4,5,260,205,178,61],([0,86,1,101,3,138,5],[5,4,261,6,58,84],[0]),e6 [343,104] [22,262,5,30,6,60,4],([90,91,233,0,1,2,3],[263,4,17],[0]),u6 [109,10] [14,6,25,11,264,23,21],u6 [6,45] [37,25,265,266,41,45,178,6,21,23,40,53],([0,6,1,2,3,4,42,7],[86,267,4,23,205,18,5],[0]),u6 [35,6] [17,64,23,78,5,21,268],u6 [6,49] [64,25,269,212,45,178,21,23,6,53,5],([15,0,1,2,3,198,5],[5,23,53,11,270],[0]),([170,0,1,101,3,138,5],[6,23,11,271],[0]),u6 [157,104] [65,5,272,11,21],u6 [6,109] [65,273,242,17,11,37,21,23,6,40],u6 [105] [5,31,273,11,6,13,21,274],u6 [6,105] [5,273,17,11,274,6,13]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_42_8_8 : checkNodesBT W_42 g_42 F_42 P_42_8_8 A_42 B_42_7 8 N_42_8_8 = true := by decide +kernel
def U_42_8_9 : List Nat := ([4,5,6,8,11,14,17,18]++r 20 4++[25,28,30,37,40,41,44,45,46,52,55,60,61,64,65,75,76,91,120,125,128,199,218,235]++r 275 14)
def P_42_8_9 : BT (Option BoundPool) := buildPoolsSubBT 9 W_42 r_42 S_42 ps_42 U_42_8_9
def N_42_8_9 : List NodeSpec := [u6 [267,7] [46,65,4,5,17,128,23,55,275],u6 [25] [76,75,4,20,44,276,61,91],u6 [25,7] [4,23,37,276,91,76,277,61],u6 [25,6] [8,17,23,4,6,277,276,18],u6 [25,6,7] [23,4,125,11,277,276,18],([0,6,117,2,3,4,5,7],[22,4,5,278,23,120,125,55,279],[0]),u6 [35,10] [41,6,5,23,218,64,280,52,60],u6 [18] [4,28,14,281,120,20,44],u6 [18,7] [281,11,14,120,4,23,37],u6 [10,45] [282,37,6,25,41,45,21,23],e6 [48,343] [5,30,64,21,4,283,6,23,60],u6 [15,45] [45,21,23,284,41,6,40],([48,15,67,0,1,3,4],[5,45,285,21,23,199],[0]),e6 [515] [11,23,286],u6 [185] [5,30,11,287],u6 [47,16] [21,23,60,14,17,6,235,5,288]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_42_8_9 : checkNodesBT W_42 g_42 F_42 P_42_8_9 A_42 B_42_7 8 N_42_8_9 = true := by decide +kernel
def N_42_8 := N_42_8_0 ++ N_42_8_1 ++ N_42_8_2 ++ N_42_8_3 ++ N_42_8_4 ++ N_42_8_5 ++ N_42_8_6 ++ N_42_8_7 ++ N_42_8_8 ++ N_42_8_9
def B_42_8 : BT (List (List Nat)) := buildBucketsBT W_42 N_42_8
set_option maxRecDepth 500000 in
lemma B_42_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_42 8 xs.toFinset) B_42_8 := by
  have hm0 := checkNodesBT_mem (by decide) gp_42 W_42_ok (buildPoolsSubBT_sound S_42_ok) A_42_ok B_42_7_ok C_42_8_0
  have hm1 := checkNodesBT_mem (by decide) gp_42 W_42_ok (buildPoolsSubBT_sound S_42_ok) A_42_ok B_42_7_ok C_42_8_1
  have hm2 := checkNodesBT_mem (by decide) gp_42 W_42_ok (buildPoolsSubBT_sound S_42_ok) A_42_ok B_42_7_ok C_42_8_2
  have hm3 := checkNodesBT_mem (by decide) gp_42 W_42_ok (buildPoolsSubBT_sound S_42_ok) A_42_ok B_42_7_ok C_42_8_3
  have hm4 := checkNodesBT_mem (by decide) gp_42 W_42_ok (buildPoolsSubBT_sound S_42_ok) A_42_ok B_42_7_ok C_42_8_4
  have hm5 := checkNodesBT_mem (by decide) gp_42 W_42_ok (buildPoolsSubBT_sound S_42_ok) A_42_ok B_42_7_ok C_42_8_5
  have hm6 := checkNodesBT_mem (by decide) gp_42 W_42_ok (buildPoolsSubBT_sound S_42_ok) A_42_ok B_42_7_ok C_42_8_6
  have hm7 := checkNodesBT_mem (by decide) gp_42 W_42_ok (buildPoolsSubBT_sound S_42_ok) A_42_ok B_42_7_ok C_42_8_7
  have hm8 := checkNodesBT_mem (by decide) gp_42 W_42_ok (buildPoolsSubBT_sound S_42_ok) A_42_ok B_42_7_ok C_42_8_8
  have hm9 := checkNodesBT_mem (by decide) gp_42 W_42_ok (buildPoolsSubBT_sound S_42_ok) A_42_ok B_42_7_ok C_42_8_9
  exact buildBucketsBT_of_mem (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (hm0) hm1) hm2) hm3) hm4) hm5) hm6) hm7) hm8) hm9)
def U_42_9_0 : List Nat := ([4,5,6,8]++r 11 4++[17,18]++r 20 4++[25,28,30,31,37,40,41]++r 44 4++[51,53,55,58,60,61,64,66,67,73,78,84,87,107,120,121,125,128,144,150,161,170,171])
def P_42_9_0 : BT (Option BoundPool) := buildPoolsSubBT 9 W_42 r_42 S_42 ps_42 U_42_9_0
def N_42_9_0 : List NodeSpec := [([0,6,2,3,10,5],[8,18],[0]),u6 [91,241] [8,46,14,23,4,21,45],u6 [175,48] [40,23,8,25,46,44,45,4,5,6],u6 [86,138] [44,5,4,20,47,11,40,8],([159,0,92,1,3,4,5],[44,20,8,47,4,30],[0]),([233,0,1,101,3,4,5],[44,20,47,8,4,30],[0]),u6 [15,67] [46,47,5,21,23,11,4],u6 [90,83] [8,46,23,47,30,53],u6 [90,241] [8,53,23,30],u6 [83,209] [46,23,41,4,40,53,47],u6 [90,38] [53,23,25,6,21,17,30,47,45,12],u6 [101,83] [23,8,58,30,46,20,44,53,47],u6 [38,86] [46,21,20,8,4,23,44,45,5,58,55],u6 [67,16] [8,46,14,60,4,21,23],u6 [48,90] [20,53,23,44,46,30,47,6,60,11],u6 [90,233] [44,53,17,8,4,23,46,60,30,64],u6 [91,233] [46,44,4,20,64],u6 [400] [8,31,20,23,66,14,53,47],u6 [454] [8,31,23,4,53,20,44,66,47],u6 [175] [8,31,40,44,20,66,47,53,23,5,4,46],u6 [6] [8,31,44,20,66,46,4,5,53],u6 [398] [8,44,66,23,53,47,14],u6 [337] [44,23,53,45,64,40,8,66,47],u6 [164] [44,31,40,66,47,46,4],u6 [427] [44,40,6,8,23,66,64,53,47],u6 [317] [44,40,23,8,11,66,47],u6 [234] [44,53,8,40,4,6,66,46],u6 [161] [44,66,40,8,46,53,4],u6 [396] [46,20,40,44,66,8,53,4,5],u6 [302] [46,20,66,40,47,53,4],u6 [272] [46,31,40,44,20,66,47,4,5],u6 [292] [46,31,40,44,66,47,53,4],u6 [409] [46,40,8,53,44,20,66,30,4,60],u6 [90] [46,40,53,8,44,20,66,23,30,60,47],u6 [291] [46,40,53,8,44,23,30,66],u6 [310] [47,20,23,11,40,8,66],u6 [314] [47,20,66,40,46,4],u6 [383] [47,40,30,8,23,20,44,66],([233,241,0,3,4,5],[44,8,73],[0]),u6 [175,159] [44,40,5,78,37,47,30,23,46,64,84,4],u6 [16,104] [46,6,21,23,87,14,11,4,47,53,13],u6 [175,38] [40,23,25,44,21,45,14,4,5,22,121,55],e6 [175,544] [44,40,78,20,23,14,121],([175,170,0,2,3,4],[121,8],[0]),u6 [7,152] [21,23,125,67,30,120,40],u6 [193,7] [23,21,125,61,120,30,67,53],u6 [36,7] [23,21,125,120,44,6,20,67,45],u6 [241,7] [23,120,125,67,30,45],u6 [90,7] [46,23,125,66,47,53,61,11,30],u6 [48,7] [46,23,125,66,120,44,20,6,45],u6 [37,7] [23,22,128,20,37,17,5,67],u6 [175,138] [44,5,78,4,40,144,11,46,23],u6 [170,138] [44,11,144,4,64,28,21],([0,1,101,3,138,5],[44,20,150,51],[0]),u6 [48,209] [47,46,23,161,4,44,25,45,6],u6 [138,83] [5,144,11,23,30,20,171,4,46],u6 [308,83] [8,23,87,171,6,58,170],u6 [159,83] [8,30,171,23,46,44,64,170,20,37,5],u6 [48,83] [8,46,23,171,30,44,6,20,45],u6 [83,39] [46,23,41,5,6,40,20,44,60,107,30,171]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_42_9_0 : checkNodesBT W_42 g_42 F_42 P_42_9_0 A_42 B_42_8 9 N_42_9_0 = true := by decide +kernel
def U_42_9_1 : List Nat := ([4,5,6,8,11,13,14,17]++r 20 4++[25]++r 28 4++[37,40,41]++r 44 4++[52,53,58,60,61]++r 64 4++[72,78,84,86,87,106,107,120,121,125,128,136,146,161,164,171,173,175,176,178,180,182,186,187,190,192,193,195,198,202]++r 204 4++[214,216,222,227,230,232,237,238,239,246,249,255,257,258,260,261,263,271,273,285,286]++r 288 9)
def P_42_9_1 : BT (Option BoundPool) := buildPoolsSubBT 9 W_42 r_42 S_42 ps_42 U_42_9_1
def N_42_9_1 : List NodeSpec := [u6 [83,7] [46,23,125,66,120,30,171,40],([15,16,0,2,3,5],[47,8,173],[0]),u6 [375] [8,20,53,46,176],u6 [38,89] [46,21,30,180,20,47,23,60,6,45,44,29],u6 [29,89] [30,14,17,8,44,20,180,21,53,47,28,182],([1,2,3,79,89,4,5],[14,17,106,46,8,47,44,25,180,186],[0]),u6 [29,209] [4,30,161,41,187,23,20,44,46,28,182],u6 [91,29] [8,14,28,187,64,4,21],u6 [90,29] [8,30,53,28,187,17,23,46,14],u6 [192] [8,53,44,46,192],u6 [98] [46,180,53,193,40,8,21,20,44],([0,86,2,3,4,83],[8,46,58,195],[0]),u6 [48,15] [47,20,45,8,5,23,46,6,11,198],([419,0,1,3,4,5],[8,44,47,204],[0]),u6 [67,6] [5,46,40,4,205,78,17,21,23],u6 [6,44] [44,40,78,5,17,20,37,64,4,205],u6 [92,209] [47,23,206,4,8,25,46,40,44,29],e6 [175,543] [47,40,206,14,53,4,121,23,5],u6 [48,16] [8,20,6,4,60,23,46,45,14,207],u6 [48,10] [8,6,214,46,25,45,44,11,23,202],u6 [67,10] [8,11,214,4,14,46,52,20,23,21],([0,92,29,3,4,5],[8,20,222],[0]),u6 [101,7] [230,146,22,23,125,61,120,6,66,128,46,20,44,67,53,47],u6 [92,89] [23,65,238,4,30,216,17,21,180,47,8,29],u6 [241,89] [46,30,238,21,180,14,44,23,29],u6 [198] [44,239,30,40,8,53,136,20],u6 [241,209] [47,23,45,246,8,25,4,40,29],u6 [175,101] [23,25,249,40,47,5,14,4,30,8],u6 [170,101] [44,6,20,23,249,21,28,30],u6 [213,89] [46,21,180,60,238,40,47,4,30,8,5,227,255],u6 [104,10] [6,87,14,25,11,4,47,44,257,23,21],([0,1,451,3,4,5],[8,20,47,258],[0]),u6 [86,101] [5,14,230,23,261,47,53,4,58,21],u6 [159,86] [46,5,21,4,261,64,37,47,53,84],u6 [233,209] [4,206,246,23,46,45,17,44,52,20,263],u6 [233,89] [46,17,238,21,180,64,30,4,8,40,263],u6 [159,170] [8,44,30,21,28,64,20,37,271],u6 [308,170] [8,47,6,87,21,28,11,23,271],u6 [195,6] [5,40,178,65,273,64,21,237,53],u6 [15,39] [44,5,23,107,46,47,190,285,11,232,45],u6 [15,104] [46,11,21,23,190,8,40,45,5,6,4,285],u6 [444] [8,20,23,44,47,286],u6 [16,39] [44,60,107,23,46,8,17,41,5,6,40,13,14,288],u6 [90,281] [53,11,8,30,23,290],e6 [90,546] [53,11,20,23,290],u6 [90,394] [53,11,40,23,30,60,290],e6 [90,276] [53,11,66,23,47,290],([90,91,0,1,2,3],[289,290,164],[0]),u6 [276] [11,22,291,31,23,40,8,53,20,44,47],([90,1,2,3,79,4,5],[23,8,25,44,72,291,17,46,47,86],[0]),u6 [90,213] [40,53,23,11,28,4,22,30,227,5,17,291],([90,0,1,2,3,52,5],[47,11,291,23,46],[0]),([90,191,0,1,2,3,5],[53,47,46,291,23,17,21],[]),e6 [175,90] [40,53,23,8,292,46,47,4],u6 [90,39] [44,46,5,23,260,20,292,60,30,53,47],e6 [90,537] [53,11,44,292,46,23,60,290],e6 [538] [46,293,23,30,60,40,8,20,44],e6 [539] [46,31,40,294,44,20,47,53,23,5],u6 [146,7] [46,4,11,125,128,23,53,295,175,45],u6 [8,7] [21,22,296,23,46,6,25,125,120,44,67,45]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_42_9_1 : checkNodesBT W_42 g_42 F_42 P_42_9_1 A_42 B_42_8 9 N_42_9_1 = true := by decide +kernel
def U_42_9_2 : List Nat := ([4,5,6,8,11,13,14,17]++r 20 4++[25,28,30,31,37,40]++r 44 4++[52,53,60,61,64,66,67,72,83,87,107,120,121,125,128,130,132,133,146,149,151,161,203,206,209,221,224,227,228,260,261,262]++r 296 26)
def P_42_9_2 : BT (Option BoundPool) := buildPoolsSubBT 9 W_42 r_42 S_42 ps_42 U_42_9_2
def N_42_9_2 : List NodeSpec := [u6 [7,143] [21,46,296,23,4,125,67,120,53],u6 [7,11] [21,46,296,23,5,125,44,67,60,120,20],u6 [7,209] [46,23,296,4,161,125,66,53,47],u6 [285,7] [46,23,296,120,8,21,4,40,121,67],u6 [39,7] [46,23,296,125,5,260,20,44,66,120,60,107],u6 [308,7] [46,23,296,125,120,4,146,11,6,149,67],u6 [175,7] [46,296,23,66,120,8,40,4],u6 [145,7] [21,22,297,30,17,23,61,125,120,128,298,53],u6 [145] [30,297,31,17,40,8,298,20,44,53],u6 [191,343] [53,4,8,30,21,60,299],u6 [191,320] [53,4,20,60,21,299],u6 [191,540] [53,4,60,132,21,299,47],u6 [191,238] [53,4,40,30,47,300,132,60,21,299],e6 [191,542] [53,4,44,300,47,60,299],e6 [191,287] [53,4,46,47,300,21,299],u6 [343] [40,262,5,301,44,20,8,46,53,4],u6 [352] [47,40,23,8,11,20,44,302],u6 [157] [47,31,40,303,44,20,46,5],u6 [86,52] [47,4,11,304,45,66,46,40,8,261,5,228],u6 [233,52] [47,4,206,304,11,37,17,20,228,64],u6 [175,52] [47,4,206,304,45,40,209,23,22,11,14,121,5,228,46],u6 [170,52] [47,11,209,304,45,21,121,6,64,228],([67,1,2,3,79,4,5],[46,8,44,305,31,72,47,14,17,203],[0]),u6 [213,67] [46,40,5,11,60,8,21,4,305],u6 [191,67] [46,53,60,14,5,30,4,21,47,305],u6 [70] [46,305,44,40,37,8,23,53,47],u6 [67,52] [47,11,209,4,304,21,5,14,20,305],([48,1,2,3,79,4,5],[25,8,306,47,44,46,23,203],[0]),u6 [48,213] [40,5,64,28,22,6,23,227,4,25,45,306],([48,0,1,3,34,4,5],[44,20,306,64,23,46],[0]),u6 [48,52] [47,45,209,4,21,20,304,306,6,23,46],u6 [48,191] [53,23,64,4,132,17,30,25,6,45,22,306],u6 [49] [64,25,306,40,23,8,53,47,44],([48,67,0,1,3,4],[307,46,203,133],[0]),u6 [216] [30,25,308,224,40,8,64,53,44,46],u6 [296] [40,25,309,66,47,53,44,8,4,64],u6 [39,209] [46,23,310,52,60,11,4,161,5,260,20,53,47],([38,0,1,3,4,5,39],[44,20,46,311,21,23],[0]),u6 [47] [44,31,40,21,8,23,53,47,20,311],u6 [191,39] [44,60,260,5,311,23,46,53,47,300,21,4,30,13,132],([91,1,2,3,79,4,5],[46,8,44,25,312,72,47,4,14,130],[0]),u6 [91,38] [46,20,45,6,44,21,14,4,312],u6 [91,213] [46,40,4,21,8,5,227,64,45,312],u6 [255] [46,312,4,40,8,20,44,21,47],u6 [298] [44,40,47,53,20,313,4,314],u6 [300] [46,40,53,8,20,315,30],u6 [104,206] [6,87,8,14,316,46,4,30,221,11],u6 [191,104] [21,6,53,300,47,30,4,11,132,13,316],u6 [109] [46,316,31,20,40,23,8,21,53,47],u6 [159,206] [8,30,4,21,44,317,20,149,6,5,64],([159,1,2,3,79,4,5],[44,8,317,72,25,46,37,17,47,149],[0]),u6 [213,159] [44,40,5,30,47,64,21,227,317,149,4],u6 [304] [44,317,40,37,8,45,53,21,46],u6 [76,159] [46,44,64,30,5,317,47,14,23,151,11,149],u6 [159,7] [46,125,23,83,317,61,120,64,5,30,149,20],u6 [117,7] [4,22,318,5,319,23,128,120,125,40,320],u6 [117] [40,319,318,44,20,47,53,5,4,320],u6 [91,206] [8,4,14,321,6,46,312],u6 [48,206] [8,6,21,20,4,30,321,306,23,45,46],u6 [67,206] [8,14,321,21,4,30,305,60,11]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_42_9_2 : checkNodesBT W_42 g_42 F_42 P_42_9_2 A_42 B_42_8 9 N_42_9_2 = true := by decide +kernel
def U_42_9_3 : List Nat := ([4,5,6,8,11,13,14,17]++r 20 4++[25]++r 28 4++[37,40,41]++r 44 4++[53,58,60,61,64,65,66,72,78,83,85,86,107,120,121,125,128,130,134,144,151,161,171,172,178,179,180,186,205,206,209,212,213,221,226,227,238,242,246,255,260,273,291,304,311,316]++r 321 23)
def P_42_9_3 : BT (Option BoundPool) := buildPoolsSubBT 9 W_42 r_42 S_42 ps_42 U_42_9_3
def N_42_9_3 : List NodeSpec := [u6 [90,206] [8,30,321,6,21,53,4,291,23,60,46],u6 [206,39] [14,311,25,8,321,41,23,221,60,260,107,46,30,4,6],u6 [206,89] [30,14,180,8,238,60,321,6,46,172],u6 [38,6] [8,5,17,178,40,47,205,25,44,322,323,45,6,21,23],u6 [76,6] [8,11,17,23,40,178,323,65,14,273,4,64,151],u6 [6,34] [44,5,78,17,20,21,40,23,323,205],u6 [6,42] [40,324,23,53,205,4,5,178],u6 [42] [40,86,324,325,23,326,53,20,44,66],u6 [206,209] [4,23,14,30,186,47,8,41,327,246,6,321,46,172],([1,2,3,79,4,5,209],[23,4,186,130,46,8,47,25,44,327,72,31],[0]),u6 [38,209] [47,23,45,161,4,44,25,6,327,29],u6 [280] [47,31,40,4,8,20,23,44,327,53,21],([191,0,1,2,3,5,209],[47,53,4,46,327,23,21],[0]),u6 [52,39] [17,22,311,47,304,328,5,107,260,23,4,209,134,46,45],u6 [104,52] [328,47,21,209,4,45,6,20,44,134,316],u6 [221,6] [5,44,4,178,25,329,17,40,23],u6 [213,104] [21,23,40,11,330,8,5,85,6,227,4,226],u6 [213,39] [44,5,311,107,60,23,46,40,8,330,226,21,4,227],u6 [213,209] [47,4,206,246,23,46,40,22,130,8,330,327,227,5,255],u6 [6,104] [5,65,273,331,8,11,21,242,6,178,47,53,13],u6 [6,39] [44,5,78,17,8,331,20,23,46,40,13,205,179,53,47,178],([6,1,2,3,79,4,5],[47,25,4,44,17,72,323,331,8,46],[0]),([6,1,81,2,3,4,5],[47,40,78,25,213,65,5,331,53],[0]),([233,1,2,3,79,4,5],[44,25,332,72,47,46,8,4,17,37],[0]),u6 [191,233] [44,53,4,17,21,332],u6 [367] [44,332,40,4,6,53,47,46,21],u6 [233,7] [46,4,23,120,125,332,83,64,17],u6 [76,233] [46,44,64,8,332,4,17,23,11,14],u6 [206,138] [4,5,14,144,333,6,30,44],u6 [138,7] [4,83,333,125,23,11,144,120,46],([1,2,3,79,4,138,5],[44,4,25,37,8,47,72,333,46],[0]),u6 [213,138] [44,5,4,40,11,333,8,21],u6 [76,138] [44,11,144,5,333,46,64,14],u6 [259] [44,40,4,8,47,46,21,333],([241,1,2,3,79,4,5],[8,25,334,47,46,14,23],[0]),u6 [76,241] [8,46,23,14,11,334],u6 [191,241] [8,53,30,44,23,14,4,21,334,60],u6 [389] [8,334,20,53,23,47,46,21],u6 [241,52] [47,45,304,21,8,334,4,40,23,28,14],u6 [210] [8,20,23,44,53,21,47,335,40],u6 [38,83] [8,23,171,30,20,6,58,335,45],([213,0,2,3,4,5,83],[8,40,28,46,335,23,21],[0]),([1,2,3,79,4,5,83],[8,335,46,23,14,28,25,44,72,47],[0]),u6 [213,391] [5,20,28,336,4,21],e6 [213,541] [5,44,28,336,21,23],u6 [213,433] [28,47,336,5,4,21],u6 [213,214] [28,53,8,330,336,4,227,5,21],e6 [213,376] [40,28,46,336,8,23,5,21],u6 [213,228] [40,28,336,8,5,227,4,21],u6 [285] [40,31,44,20,337,47,53,5,22,23],u6 [34,83] [5,23,14,8,22,40,6,335,171,30,44,60,338],u6 [38,16] [8,20,6,60,47,14,21,23,339,45],([16,1,2,3,79,4,5],[8,44,25,339,72,46,47,14,17],[0]),u6 [76,16] [8,46,14,60,6,339,47,64,23,11,151],u6 [217] [8,339,20,28,44,4,53,21,46],u6 [16,34] [44,60,338,21,8,23,5,4,6,339,14],u6 [16,7] [46,120,23,128,125,339,61,14,6,60],u6 [87,7] [46,23,128,125,120,40,340,121,6,14,30],u6 [274] [47,20,40,44,341,5,342],u6 [48,6] [8,5,17,178,40,4,25,343,45,44,23,212,6,205]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_42_9_3 : checkNodesBT W_42 g_42 F_42 P_42_9_3 A_42 B_42_8 9 N_42_9_3 = true := by decide +kernel
def U_42_9_4 : List Nat := ([4,5,6,8,11,14,17]++r 20 4++[25,28,30,31,40]++r 44 4++[52,53,60,64,66,72,78,84,85,87,107,120,121,125,128,132,146,149,151,163,167,180,187,190,201,206,214,227,230,245,246,249,291,296,300,304,312,316,327,330,338]++r 344 23)
def P_42_9_4 : BT (Option BoundPool) := buildPoolsSubBT 9 W_42 r_42 S_42 ps_42 U_42_9_4
def N_42_9_4 : List NodeSpec := [u6 [15,38] [20,45,21,23,8,40,5,11,344,6],u6 [15,34] [44,5,21,338,23,344,11],u6 [15,7] [46,4,11,120,128,23,125,245,344,45,5],u6 [15,76] [46,11,64,23,8,40,5,45,344,4,14],([15,1,2,3,79,4,5],[47,44,25,344,46,4,8,190],[0]),u6 [361] [47,344,40,30,20,4,44,21,46],u6 [34,209] [4,17,23,47,44,52,246,5,345,327,163,64],u6 [90,34] [44,23,345,5,53,60,291],u6 [91,34] [44,64,345,5,20,21,23,4,14,312,53,47,60],u6 [34,89] [60,21,30,345,5,180,44,20,53,47,163],u6 [308,213] [40,4,330,8,227,21,23,11,5,346,85,149],u6 [350] [8,20,53,44,46,347,60],u6 [213,101] [5,23,28,227,40,47,4,249,22,348,30,346,8],u6 [101,206] [6,348,8,23,20,30,14,44,249],u6 [325] [21,25,348,20,40,23,8,53,201,46],u6 [76,101] [23,25,11,230,14,151,64,348],([1,101,2,3,79,4,5],[25,8,23,348,17,47,44,46],[0]),([175,0,2,3,206,4,5],[8,23,4,349,46,14],[0]),([175,213,0,2,3,4,5],[40,8,46,5,349,22,23],[]),u6 [175,191] [40,53,4,300,47,60,132,30,14,23,5,22,121,349],u6 [175,34] [44,5,78,23,40,338,60,121,349],([1,104,2,3,79,4,5],[46,8,25,14,316,31,72,47,350],[0]),u6 [178] [40,14,23,349,31,351,20,44,4,53,47,8],([175,176,1,2,3,4,5],[8,46,40,78,25,167,206,5,352,121,23,4],[0]),u6 [175,178] [40,14,351,66,352,8,121,23],u6 [175,39] [44,46,78,5,20,23,107,60,352,40,8,4],([175,1,2,3,79,4,5],[46,25,23,44,72,349,352,47,4,8,121],[0]),u6 [175,209] [46,206,23,8,352,4,40],u6 [175,308] [47,40,23,206,4,352,8,84],u6 [308,206] [8,4,87,6,47,14,353,149],([308,1,2,3,79,4,5],[47,8,25,353,31,72,46,4,23,149],[0]),u6 [312] [47,353,31,20,40,23,8,21,46],([92,1,2,3,79,4,5],[44,8,25,354,31,72,47,46,4,23],[0]),u6 [92,7] [46,23,296,4,125,146,128,120,40,8,354],u6 [244] [4,25,21,354,31,355,20,40,23,53,47,46],u6 [38,170] [8,20,6,11,30,21,44,45,121,356],([170,1,2,3,79,4,5],[8,44,25,356,72,47,46,121,28,14],[0]),u6 [191,170] [8,53,30,64,6,21,60,132,47,121,356],u6 [174] [8,356,46,20,28,44,21,53,47],u6 [170,34] [44,64,23,20,21,8,338,60,40,5,6,121,356,30,11],u6 [334] [30,20,357,25,40,8,46,53],u6 [281] [40,5,358,44,20,66,8,47,53,4,11],u6 [251] [40,14,359,8,4,60,20,44,66,53,46],u6 [175,251] [40,14,359,47,121,4],u6 [34,10] [5,360,14,4,44,338,52,17,6,20,214,64,23],u6 [38,10] [8,6,360,11,44,25,45,21,23],u6 [270] [8,31,20,21,44,4,47,46,360],([1,2,3,79,4,10,5],[8,47,360,28,14,25,44,72,31,46],[0]),u6 [10,7] [14,360,46,120,296,125,23,128,6,214],u6 [403] [40,31,44,20,361,53,46,17,21],u6 [193] [53,31,8,40,44,20,362,23,17,21],u6 [168] [44,31,40,363,47,53,46,23,4],u6 [29,52] [4,28,22,364,17,45,40,304,187,14],u6 [76,29] [8,14,46,364,187,30,64,11],u6 [191,29] [8,30,53,364,14,17,47,21],u6 [230] [8,44,53,21,47,28,46,364],([1,2,29,3,79,4,5],[8,44,72,364,31,47,46,17,14],[0]),u6 [29,7] [14,46,364,125,23,128,120,30,187],u6 [207] [8,365,31,53,44,20,60,46],u6 [433] [40,28,366,8,31,17,20,44,46,53]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_42_9_4 : checkNodesBT W_42 g_42 F_42 P_42_9_4 A_42 B_42_8 9 N_42_9_4 = true := by decide +kernel
def U_42_9_5 : List Nat := ([4,5,6,8,11,14,17,18]++r 20 4++[25,28,30,31,37,40,41]++r 44 4++[52,53,58,60,61,64,65,66,72,84,86,120,121,125,128,132,149,153,168,171,178,200,205,206,209,214,228,236,249,257,261,292,296,300,304,311,323,331,335,338,350,353,354,360]++r 367 27)
def P_42_9_5 : BT (Option BoundPool) := buildPoolsSubBT 9 W_42 r_42 S_42 ps_42 U_42_9_5
def N_42_9_5 : List NodeSpec := [u6 [91,92] [4,25,46,44,367,206,45],u6 [191,92] [4,25,53,44,367,23,300,47,17,30,21,354],u6 [90,92] [8,23,25,53,367,292,4,30,17,47],u6 [76,92] [23,25,46,367,65,4,14,64,11,354],u6 [92,52] [47,4,206,45,66,20,21,44,228,23,367],u6 [287] [4,22,368,369,31,23,40,8,53,20,44,46],u6 [86,34] [44,5,21,20,338,60,40,8,370,4],u6 [191,86] [46,21,53,4,60,132,47,370],([86,1,2,3,79,4,5],[46,44,25,370,47,4,8,200,14],[0]),u6 [6,110] [40,22,371,4,331,66,18,5,178,205],u6 [110] [40,22,323,31,371,372,20,4,44,53,46],u6 [442] [8,53,66,46,40,30,373,20,4],([1,2,3,79,4,5,39],[44,23,311,25,17,46,8,374,350,72,47],[0]),u6 [438] [40,31,44,20,66,53,17,375,23],u6 [6,7] [46,4,296,376,323,120,23,128,125,205,40,8,61,178,5],u6 [236] [40,86,377,20,378,66,367,53,47],u6 [10,39] [5,379,52,41,214,60,20,257,11,23,236,53,46,6],u6 [35] [44,40,23,8,64,53,47,380],u6 [376] [40,28,22,381,8,31,23,20,44,53,47],u6 [250] [46,370,40,382,20,4,44,21,53,47],u6 [76,10] [8,11,214,6,360,46,383,14,23,64],u6 [308,86] [46,4,383,261,11,44,58,84],u6 [308,76] [46,47,23,383,14,11,149,353],u6 [52,83] [4,28,22,335,14,23,171,384,45,304,209],u6 [191,83] [8,30,384,23,335,46,53,21,132,60,4],u6 [179] [8,385,60,20,44,53,168],e6 [175,545] [40,25,386,44,5,23,14,121],u6 [186] [44,387,40,53,8,23,30,46],u6 [336] [40,20,5,388,25,47,53,46,4],u6 [45] [37,25,389,390,31,21,23,40,8,46,53,47],u6 [328] [40,8,20,66,46,391,53,4],u6 [171] [86,392,31,20,53,153,249,40,8,66],u6 [360] [8,31,20,23,44,393,53,47,4,14]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_42_9_5 : checkNodesBT W_42 g_42 F_42 P_42_9_5 A_42 B_42_8 9 N_42_9_5 = true := by decide +kernel
def N_42_9 := N_42_9_0 ++ N_42_9_1 ++ N_42_9_2 ++ N_42_9_3 ++ N_42_9_4 ++ N_42_9_5
def B_42_9 : BT (List (List Nat)) := buildBucketsBT W_42 N_42_9
set_option maxRecDepth 500000 in
lemma B_42_9_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_42 9 xs.toFinset) B_42_9 := by
  have hm0 := checkNodesBT_mem (by decide) gp_42 W_42_ok (buildPoolsSubBT_sound S_42_ok) A_42_ok B_42_8_ok C_42_9_0
  have hm1 := checkNodesBT_mem (by decide) gp_42 W_42_ok (buildPoolsSubBT_sound S_42_ok) A_42_ok B_42_8_ok C_42_9_1
  have hm2 := checkNodesBT_mem (by decide) gp_42 W_42_ok (buildPoolsSubBT_sound S_42_ok) A_42_ok B_42_8_ok C_42_9_2
  have hm3 := checkNodesBT_mem (by decide) gp_42 W_42_ok (buildPoolsSubBT_sound S_42_ok) A_42_ok B_42_8_ok C_42_9_3
  have hm4 := checkNodesBT_mem (by decide) gp_42 W_42_ok (buildPoolsSubBT_sound S_42_ok) A_42_ok B_42_8_ok C_42_9_4
  have hm5 := checkNodesBT_mem (by decide) gp_42 W_42_ok (buildPoolsSubBT_sound S_42_ok) A_42_ok B_42_8_ok C_42_9_5
  exact buildBucketsBT_of_mem (forall_append (forall_append (forall_append (forall_append (forall_append (hm0) hm1) hm2) hm3) hm4) hm5)
def U_42_10 : List Nat := ([8,20,25,31,40,44,46,47,51,53,57,66,180,289,291,296,300,305,306,307,311,312,316,317,323,327]++r 332 4++[339,344,348,349,353,354,356,360,364,370]++r 394 7)
def P_42_10 : BT (Option BoundPool) := buildPoolsSubBT 9 W_42 r_42 S_42 ps_42 U_42_10
def N_42_10 : List NodeSpec := [u6 [206] [8,66,20,44,47,46],u6 [38] [20,31,8,66,47,46,44,25],u6 [34] [44,66,8,47,46],u6 [76] [46,8,44,20,66,47],u6 [52] [47,66,8,20,44,46],([1,2,3,79,4,5],[66,31],[0]),u6 [89] [46,180,8,53,47,44,20,289],u6 [7] [46,296,66,8,20,44,47],u6 [191] [47,300,53,8,20,44,66,46],u6 [67] [46,8,44,47,305],u6 [39] [44,57,31,311,46,8,307,47,20],u6 [91] [46,8,44,20,47,312],u6 [104] [46,31,57,8,20,316,47,307],u6 [159] [44,8,20,46,317,53,47,51],u6 [209] [47,57,31,327,46,8,20,44,289],u6 [233] [8,44,20,47,46,40,332],u6 [138] [44,333,47,8,46],u6 [241] [8,20,47,46,334],u6 [83] [8,46,335,20,44,47],u6 [16] [8,44,20,46,47,339,53],u6 [15] [47,44,20,46,40,8,344],u6 [308] [57,47,31,8,20,46,353,51],u6 [170] [8,44,20,47,46,356],u6 [10] [8,57,31,47,360,20,44,46],u6 [29] [8,44,47,46,364],u6 [86] [46,44,20,47,40,8,370],u6 [6] [8,31,394,47,20,40,44,323,46,53],u6 [213] [8,395,66,20,40,44,47,46],u6 [92] [8,31,20,396,44,47,46,40,354],u6 [90] [46,53,8,20,44,291,47,397],u6 [175] [8,31,398,46,20,40,44,349,47],u6 [48] [20,8,47,44,399,306,46],u6 [101] [44,400,20,8,348,53,47,46]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_42_10 : checkNodesBT W_42 g_42 F_42 P_42_10 A_42 B_42_9 10 N_42_10 = true := by decide +kernel
def B_42_10 : BT (List (List Nat)) := buildBucketsBT W_42 N_42_10
set_option maxRecDepth 500000 in
lemma B_42_10_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_42 10 xs.toFinset) B_42_10 :=
  buildBucketsBT_sound (by decide) gp_42 W_42_ok (buildPoolsSubBT_sound S_42_ok) A_42_ok B_42_9_ok C_42_10
def U_42_11 : List Nat := [57,66]
def P_42_11 : BT (Option BoundPool) := buildPoolsSubBT 9 W_42 r_42 S_42 ps_42 U_42_11
def N_42_11 : List NodeSpec := [u6 [] [57,66]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_42_11 : checkNodesBT W_42 g_42 F_42 P_42_11 A_42 B_42_10 11 N_42_11 = true := by decide +kernel
def B_42_11 : BT (List (List Nat)) := buildBucketsBT W_42 N_42_11
set_option maxRecDepth 500000 in
lemma B_42_11_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_42 11 xs.toFinset) B_42_11 :=
  buildBucketsBT_sound (by decide) gp_42 W_42_ok (buildPoolsSubBT_sound S_42_ok) A_42_ok B_42_10_ok C_42_11
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_42_ok : forestRootCheck r_42 g_42 [(VAR 0,20,21),(VAR 1,12,14),(VAR 2,10,14),(VAR 3,6,14),(VAR 4,5,21),(VAR 5,3,35)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_42_in : bucketContainsBT B_42_11 r_42 = true := by decide +kernel
lemma low_42 : Lower r_42 g_42 12 := lower_of_forestBT root_42_ok B_42_11_ok root_42_in

def g_orig := 0xfeeaeac8fee8ea80
set_option maxHeartbeats 0 in
lemma low_orig : Lower (varsOf 63) g_orig 12 := carry_of (swaps := [(0,5),(1,4)]) (by decide +kernel) low_42
def targetFn (x : Fin 6 → Bool) : Bool := Nat.testBit (4276808392 * 2 ^ 32 + 4276677248) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def temoin : List Gate := [⟨.or,[2,1]⟩,⟨.and,[1,2]⟩,⟨.or,[1,4]⟩,⟨.and,[7,0]⟩,⟨.and,[4,6]⟩,⟨.or,[0,7]⟩,⟨.or,[9,3]⟩,⟨.and,[5,8]⟩,⟨.or,[11,12]⟩,⟨.or,[12,13]⟩,⟨.and,[10,14]⟩,⟨.and,[15,11]⟩,⟨.or,[16,17]⟩]
lemma temoin_ok : PEqualNP.MetaComplexity.Monotone2 ⟨temoin, 18⟩ := by
  intro g hg; simp [temoin] at hg; rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxHeartbeats 0 in
lemma tgt_eq_G : ∀ r : Row, targetFn (evalInput6 r) = g_orig.testBit r.val := by decide +kernel
set_option maxHeartbeats 0 in
lemma temoin_eval : ∀ r : Row, Circuit.eval ⟨temoin, 18⟩ (List.ofFn (evalInput6 r)) = g_orig.testBit r.val := by decide +kernel

end PEqualNP.Outside.L_meta_45560

open PEqualNP.Outside.L_meta_45560 in
theorem PEqualNP.Outside.L_meta_45560 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808392 * 2 ^ 32 + 4276677248) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808392 * 2 ^ 32 + 4276677248) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  exact replace_of_lower6 g_orig (by decide) (by decide) (by decide) 12 low_orig temoin 18 (by decide) temoin_ok targetFn tgt_eq_G temoin_eval
