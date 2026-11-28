import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_42210
open PEqualNP.CircuitLowerBounds
abbrev Row := Fin 256
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
lemma bin_lt (d a b : Nat) (ha : a < 2^256) (hb : b < 2^256) : bin d a b < 2^256 := by
  have h1 : ∀ x y : Nat, x < 2^256 → y < 2^256 → (x &&& y) < 2^256 := fun x y hx _ =>
    Nat.lt_of_le_of_lt Nat.and_le_left hx
  have h2 : ∀ x y : Nat, x < 2^256 → y < 2^256 → (x ||| y) < 2^256 := fun x y hx hy =>
    Nat.or_lt_two_pow hx hy
  have h3 : ∀ x y : Nat, x < 2^256 → y < 2^256 → (x ^^^ y) < 2^256 := fun x y hx hy =>
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
lemma swGate_lt (w : List SWire) (hw : ∀ u ∈ w, u.2 < 2^256 ∧ u.2.testBit 0 = false) (g : Gate) :
    (swGate w g).2 < 2^256 ∧ (swGate w g).2.testBit 0 = false := by
  have hz : (0 : Nat) < 2^256 ∧ (0 : Nat).testBit 0 = false := ⟨by decide, by decide⟩
  have hg (i : Nat) : (w.getD i swZero).2 < 2^256 ∧ (w.getD i swZero).2.testBit 0 = false := by
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
    (hw : ∀ u ∈ w, u.2 < 2^256 ∧ u.2.testBit 0 = false) :
    ∀ u ∈ swExec gs w, u.2 < 2^256 ∧ u.2.testBit 0 = false := by
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
lemma normPack_lt (f : Wire) : normPack f < 2^256 :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => f r != f 0))).cast List.length_ofFn).isLt
lemma testBit_normPack (f : Wire) (r : Nat) :
    (normPack f).testBit r = if h : r < 256 then (f ⟨r, h⟩ != f 0) else false := by
  change ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => f r != f 0))).cast List.length_ofFn).getLsbD r = _
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases h : r < 256 <;> simp [h]
lemma normPack_eq_of_obs {a : Nat} (ha : a < 2^256) (h0 : a.testBit 0 = false) :
    normPack (obs a) = a := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack]
  by_cases hr : r < 256
  · simp [hr, obs, h0]
  · simp only [hr, dite_false]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega)))).symm
lemma normPack_inv (f : Wire) : normPack (invW f) = normPack f := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack, testBit_normPack]
  by_cases hr : r < 256
  · simp only [hr, dite_true, invW]
    cases f ⟨r, hr⟩ <;> cases f 0 <;> rfl
  · simp [hr]
lemma normPack_const {f : Wire} (h : Constant f) : normPack f = 0 := by
  obtain ⟨b, rfl⟩ := h
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack]
  by_cases hr : r < 256 <;> simp [hr]
lemma normPack_comb2 (op : Bool) (a b : Wire) :
    ∃ d < 4, normPack (comb2 op a b) = bin d (normPack a) (normPack b) := by
  refine ⟨opIdx (if op then !(a 0) else a 0) (if op then !(b 0) else b 0), opIdx_lt _ _, ?_⟩
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack, testBit_bin, testBit_normPack, testBit_normPack]
  by_cases hr : r < 256
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
    (hT0 : T ≠ 0) (hTlt : T < 2^256) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^256 ∧ a.testBit 0 = false)
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
lemma obs_not_const {T : Nat} (hT0 : T ≠ 0) (hTlt : T < 2^256) (hTb0 : T.testBit 0 = false) :
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
  ⟨((r.val &&& (255 ^^^ z)) ||| o) % 256, Nat.mod_lt _ (by decide)⟩
def renameW (f : Row → Row) (a : Nat) : Nat :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).toNat
lemma testBit_renameW (f : Row → Row) (a : Nat) (r : Row) :
    (renameW f a).testBit r.val = a.testBit (f r).val := by
  change ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).getLsbD r.val = _
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn, r.isLt, dite_true, Option.getD_some]
lemma renameW_lt (f : Row → Row) (a : Nat) : renameW f a < 2^256 :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).isLt
lemma obs_renameW (f : Row → Row) (a : Nat) : obs (renameW f a) = restrictW f (obs a) := by
  funext r; exact testBit_renameW f a r
lemma renameW_bin (f : Row → Row) (d a b : Nat) :
    renameW f (bin d a b) = bin d (renameW f a) (renameW f b) := by
  apply Nat.eq_of_testBit_eq
  intro r
  by_cases hr : r < 256
  · rw [testBit_renameW f _ ⟨r, hr⟩, testBit_bin, testBit_bin, testBit_renameW f _ ⟨r, hr⟩, testBit_renameW f _ ⟨r, hr⟩]
  · have hlt (x : Nat) : (renameW f x).testBit r = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt f x) (Nat.pow_le_pow_right (by decide) (by omega)))
    rw [hlt, testBit_bin, hlt, hlt]
    rcases d with _ | _ | _ | d <;> rfl
lemma renameW_zero (f : Row → Row) : renameW f 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 256
  · simpa using testBit_renameW f 0 ⟨r, hr⟩
  · rw [Nat.zero_testBit]
    exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt f 0) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 256 ≤ r)))
lemma renameW_inj (f : Row → Row) (onto : Function.Surjective f) {a b : Nat}
    (ha : a < 2^256) (hb : b < 2^256) (eq : renameW f a = renameW f b) : a = b := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 256
  · obtain ⟨q, hq⟩ := onto ⟨r, hr⟩
    have h := congrArg (fun x => x.testBit q.val) eq
    rw [testBit_renameW, testBit_renameW, hq] at h
    exact h
  · have hge : 256 ≤ r := by omega
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide : 0 < 2) hge)),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide : 0 < 2) hge))]
lemma live_renameW {T k S} (h : Live T k S) (hS : ∀ a ∈ S, a < 2^256) (f : Row → Row)
    (onto : Function.Surjective f) : Live (renameW f T) k (S.image (renameW f)) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl, hT⟩ := h
    have hTlt : T < 2^256 := hS T (by simp)
    refine ⟨by simp, fun hz => hT (renameW_inj f onto hTlt (by decide) (hz.trans (renameW_zero f).symm))⟩
  | succ k ih =>
    obtain ⟨U, a, b, d, hd, rfl, ha, hb, hab, fresh, tail⟩ := h
    have halt : a < 2^256 := hS a (by simp)
    have hblt : b < 2^256 := hS b (by simp)
    have hUlt : ∀ x ∈ U, x < 2^256 := fun x hx => hS x (by simp [hx])
    have hzlt : bin d a b < 2^256 := bin_lt d a b halt hblt
    have htail_lt : ∀ x ∈ insert (bin d a b) U, x < 2^256 := by
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
    (hT0 : T ≠ 0) (hTlt : T < 2^256) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^256 ∧ a.testBit 0 = false)
    (hG0 : G ≠ 0) (hGlt : G < 2^256) (hGb0 : G.testBit 0 = false)
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
    (hT0 : T ≠ 0) (hTlt : T < 2^256) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^256 ∧ a.testBit 0 = false)
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
  | 0 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
  | 1 => 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
  | 2 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
  | 3 => 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00
  | 4 => 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000
  | 5 => 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000
  | 6 => 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000
  | 7 => 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000
  | _ => 0
def ALL256 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def swapRow (i j : Nat) (r : Row) : Row :=
  let bi := r.val.testBit i
  let bj := r.val.testBit j
  if bi == bj then r
  else ⟨(r.val ^^^ (1 <<< i) ^^^ (1 <<< j)) % 256, Nat.mod_lt _ (by decide)⟩
def swapWord (i j : Nat) (w : Nat) : Nat :=
  let a := VAR i
  let b := VAR j
  let m10 := a ^^^ (a &&& b)
  let m01 := b ^^^ (a &&& b)
  let msame := ALL256 ^^^ (m10 ||| m01)
  let d := (1 <<< j) - (1 <<< i)
  (w &&& msame) ||| ((w &&& m10) <<< d) ||| ((w &&& m01) >>> d)
def permRow (swaps : List (Nat × Nat)) (r : Row) : Row :=
  swaps.foldl (fun x p => swapRow p.1 p.2 x) r
def permWord (swaps : List (Nat × Nat)) (w : Nat) : Nat :=
  swaps.foldr (fun p x => swapWord p.1 p.2 x) w
lemma swapRow_invol (i j : Nat) (hi : i < 8) (hj : j < 8) (r : Row) :
    swapRow i j (swapRow i j r) = r := by
  revert r
  interval_cases i <;> interval_cases j <;> decide +kernel
lemma swapWord_testBit (i j : Nat) (hij : i < j) (hj : j < 8) (w : Nat) (hw : w < 2^256) (r : Row) :
    (swapWord i j w).testBit r.val = w.testBit (swapRow i j r).val := by
  have hi : i < 8 := by omega
  have hspec : ∀ r : Row,
      let a := VAR i; let b := VAR j
      let m10 := a ^^^ (a &&& b); let m01 := b ^^^ (a &&& b); let msame := ALL256 ^^^ (m10 ||| m01)
      let d := (1 <<< j) - (1 <<< i)
      (msame.testBit r.val = true → (swapRow i j r).val = r.val ∧ (d ≤ r.val → m10.testBit (r.val - d) = false) ∧ m01.testBit (r.val + d) = false) ∧
      (msame.testBit r.val = false →
        (d ≤ r.val ∧ m10.testBit (r.val - d) = true ∧ (swapRow i j r).val = r.val - d ∧ m01.testBit (r.val + d) = false) ∨
        ((d ≤ r.val → m10.testBit (r.val - d) = false) ∧ m01.testBit (r.val + d) = true ∧ (swapRow i j r).val = r.val + d)) := by
    revert r; interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have hr := hspec r
  simp only [swapWord, Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Nat.add_comm]
  cases hms : (ALL256 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j)))).testBit r.val with
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
lemma swapWord_lt (i j : Nat) (hij : i < j) (hj : j < 8) (w : Nat) : swapWord i j w < 2^256 := by
  have hi : i < 8 := by omega
  have h1 : (ALL256 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j)))) < 2^256 := by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have h2 : ((VAR i ^^^ (VAR i &&& VAR j)) <<< ((1 <<< j) - (1 <<< i))) < 2^256 := by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have h3 : ((VAR j ^^^ (VAR i &&& VAR j)) >>> ((1 <<< j) - (1 <<< i))) < 2^256 := by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  unfold swapWord
  have e1 : (w &&& (ALL256 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j))))) < 2^256 :=
    Nat.lt_of_le_of_lt Nat.and_le_right h1
  have e2 : ((w &&& (VAR i ^^^ (VAR i &&& VAR j))) <<< ((1 <<< j) - (1 <<< i))) < 2^256 := by
    have hle : (w &&& (VAR i ^^^ (VAR i &&& VAR j))) ≤ (VAR i ^^^ (VAR i &&& VAR j)) := Nat.and_le_right
    calc ((w &&& (VAR i ^^^ (VAR i &&& VAR j))) <<< ((1 <<< j) - (1 <<< i)))
        = (w &&& (VAR i ^^^ (VAR i &&& VAR j))) * 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.shiftLeft_eq _ _
      _ ≤ (VAR i ^^^ (VAR i &&& VAR j)) * 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.mul_le_mul_right _ hle
      _ = ((VAR i ^^^ (VAR i &&& VAR j)) <<< ((1 <<< j) - (1 <<< i))) := (Nat.shiftLeft_eq _ _).symm
      _ < 2^256 := h2
  have e3 : ((w &&& (VAR j ^^^ (VAR i &&& VAR j))) >>> ((1 <<< j) - (1 <<< i))) < 2^256 := by
    have hle : (w &&& (VAR j ^^^ (VAR i &&& VAR j))) ≤ (VAR j ^^^ (VAR i &&& VAR j)) := Nat.and_le_right
    calc ((w &&& (VAR j ^^^ (VAR i &&& VAR j))) >>> ((1 <<< j) - (1 <<< i)))
        = (w &&& (VAR j ^^^ (VAR i &&& VAR j))) / 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.shiftRight_eq_div_pow _ _
      _ ≤ (VAR j ^^^ (VAR i &&& VAR j)) / 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.div_le_div_right hle
      _ = ((VAR j ^^^ (VAR i &&& VAR j)) >>> ((1 <<< j) - (1 <<< i))) := (Nat.shiftRight_eq_div_pow _ _).symm
      _ < 2^256 := h3
  exact Nat.or_lt_two_pow (Nat.or_lt_two_pow e1 e2) e3
lemma swapWord_eq_renameW (i j : Nat) (hij : i < j) (hj : j < 8) (w : Nat) (hw : w < 2^256) :
    swapWord i j w = renameW (swapRow i j) w := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 256
  · rw [swapWord_testBit i j hij hj w hw ⟨r, hr⟩, ← testBit_renameW (swapRow i j) w ⟨r, hr⟩]
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (swapWord_lt i j hij hj w) (Nat.pow_le_pow_right (by decide) (by omega))),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))]
def swapsValid (swaps : List (Nat × Nat)) : Bool :=
  swaps.all fun p => decide (p.1 < p.2) && decide (p.2 < 8)
lemma permWord_eq_renameW (swaps : List (Nat × Nat)) (hv : swapsValid swaps = true)
    (w : Nat) (hw : w < 2^256) : permWord swaps w = renameW (permRow swaps) w := by
  induction swaps generalizing w with
  | nil =>
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hr : r < 256
    · exact (testBit_renameW (permRow []) w ⟨r, hr⟩).symm
    · rw [show permWord [] w = w from rfl,
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))]
  | cons p ps ih =>
    simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hv
    have ihw := ih hv.2 w hw
    have hlt : permWord ps w < 2^256 := ihw ▸ renameW_lt _ w
    change swapWord p.1 p.2 (permWord ps w) = renameW (permRow (p :: ps)) w
    rw [swapWord_eq_renameW p.1 p.2 hv.1.1 hv.1.2 _ hlt, ihw]
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hr : r < 256
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
    (hT : T < 2^256) (hfix : permWord swaps T = T)
    (hw : ∀ a ∈ ws, a < 2^256) :
    Impossible T n (ws.map (permWord swaps)).toFinset := by
  intro k hk run
  have hr : ∀ a ∈ (ws.map (permWord swaps)).toFinset, a < 2^256 := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    rw [permWord_eq_renameW swaps hv x (hw x hx)]
    exact renameW_lt _ x
  have hvr : swapsValid swaps.reverse = true := by
    simp only [swapsValid, List.all_reverse]; exact hv
  have hinv_row2 : ∀ r : Row, permRow swaps (permRow swaps.reverse r) = r := by
    intro r; simpa using permRow_rev_cancel swaps.reverse hvr r
  have hinv_word : ∀ x : Nat, x < 2^256 → renameW (permRow swaps.reverse) (permWord swaps x) = x := by
    intro x hx
    rw [permWord_eq_renameW swaps hv x hx]
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hrr : r < 256
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
  (List.range 8).filterMap fun i => if m.testBit i then some (VAR i) else none
def subcube (z o : Nat) : Nat :=
  (List.range 256).foldr (fun r acc =>
    if (r &&& z == 0) && (r &&& o == o) then acc ||| (1 <<< r) else acc) 0
def fixWord (z o w : Nat) : Nat :=
  (List.range 256).foldr (fun r acc =>
    let fr := ((r &&& (255 ^^^ z)) ||| o) % 256
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
  by_cases hr : r < 256
  · rw [testBit_renameW (fixRow z o) w ⟨r, hr⟩]
    simp [hr, fixRow]
  · simp only [List.mem_range, hr, decide_false, Bool.false_and]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))).symm
lemma subcube_fixRow (z o : Nat) (hz : z < 256) (ho : o < 256) (hzo : (z &&& o) = 0) (r : Row) :
    (subcube z o).testBit (fixRow z o r).val = true := by
  unfold subcube
  rw [testBit_foldr_bits]
  have hmem : (fixRow z o r).val ∈ List.range 256 := List.mem_range.mpr (fixRow z o r).isLt
  simp only [hmem, decide_true, Bool.true_and, Bool.and_eq_true, beq_iff_eq]
  have h255 : ((r.val &&& (255 ^^^ z)) ||| o) < 256 := by
    have hr := r.isLt
    have hlt1 : (r.val &&& (255 ^^^ z)) < 256 := Nat.lt_of_le_of_lt Nat.and_le_left hr
    exact Nat.or_lt_two_pow (n := 8) hlt1 ho
  have hval : (fixRow z o r).val = ((r.val &&& (255 ^^^ z)) ||| o) := Nat.mod_eq_of_lt h255
  rw [hval]
  constructor
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, Nat.zero_testBit]
    have hzi : (z.testBit i && o.testBit i) = false := by
      have := congrArg (fun x => x.testBit i) hzo; simpa [Nat.testBit_and] using this
    by_cases hi : i < 8
    · have h7 : (255 : Nat).testBit i = true := by interval_cases i <;> decide
      cases hzb : z.testBit i <;> cases hob : o.testBit i <;> simp_all [h7]
    · have hzf : z.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hz (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 8 ≤ i)))
      simp [hzf]
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_or]
    cases o.testBit i <;> simp
def checkEss1 (T : Nat) (roots : List Nat) (a r s : Nat) : Bool :=
  decide (r < 256) && decide (s < 256) && (T.testBit r != T.testBit s) &&
    roots.all fun v => v == a || (v.testBit r == v.testBit s)
lemma checkEss1_sound {T roots a r s} (h : checkEss1 T roots a r s = true) : Essential T roots a := by
  simp only [checkEss1, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  exact ⟨⟨r, h.1.1.1⟩, ⟨s, h.1.1.2⟩, h.1.2, fun v hv hne => (h.2 v hv).resolve_left hne⟩
def freeIn (other : List Nat) (w : Nat) : Bool := w == 0 || w == ALL256 || other.contains w
lemma freeIn_sound {other : List Nat} {f : Row → Row} {a : Nat} (ok : freeIn other (renameW f a) = true) :
    Avail (other.map obs) (restrictW f (obs a)) := by
  rw [← obs_renameW]
  simp only [freeIn, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at ok
  rcases ok with (h0 | h1) | hm
  · exact Or.inr (Or.inl ⟨false, by rw [h0]; funext r; simp [obs]⟩)
  · exact Or.inr (Or.inl ⟨true, by rw [h1]; funext r; simp only [obs, ALL256]; have := r.isLt; exact Nat.testBit_two_pow_sub_one 256 r.val |> fun e => by simpa [this] using e⟩)
  · exact Or.inl (List.mem_map_of_mem hm)
def checkProper (w : Nat) : Bool := w != 0 && decide (w < 2^256) && !w.testBit 0
lemma checkProper_sound {w : Nat} (h : checkProper w = true) : w ≠ 0 ∧ w < 2^256 ∧ w.testBit 0 = false := by
  simp only [checkProper, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq, Bool.not_eq_true'] at h
  exact ⟨h.1.1, h.1.2, h.2⟩
def checkRoots (rs : List Nat) : Bool := rs.all fun a => decide (a < 2^256) && !a.testBit 0
lemma checkRoots_sound {rs : List Nat} (h : checkRoots rs = true) :
    ∀ a ∈ rs, a < 2^256 ∧ a.testBit 0 = false := by
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
  base.all fun x => (x.2.1 == projBits pos x.1) && (x.2.2 == projBits neg x.1) && decide (x.1 < 2^256)
lemma base_of {pos neg base} (ok : baseCheck pos neg base = true) :
    ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^256 := by
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
lemma var_testBit (i : Fin 8) (r : Row) : (VAR i.val).testBit r.val = r.val.testBit i.val := by revert i r; decide +kernel
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
  if z.testBit i then ALL256 ^^^ VAR i else if o.testBit i then VAR i else ALL256
def subcubeFast (z o : Nat) : Nat :=
  fastBitMask z o 0 &&& fastBitMask z o 1 &&& fastBitMask z o 2 &&&
  fastBitMask z o 3 &&& fastBitMask z o 4 &&& fastBitMask z o 5 &&&
  fastBitMask z o 6 &&& fastBitMask z o 7
lemma fastBitMask_testBit (z o i : Nat) (hi : i < 8) (r : Row) :
    (fastBitMask z o i).testBit r.val =
      (if z.testBit i then !(r.val.testBit i) else if o.testBit i then r.val.testBit i else true) := by
  have hall : ALL256.testBit r.val = true := by
    simp only [ALL256]; have hr := r.isLt; simpa [hr] using Nat.testBit_two_pow_sub_one 256 r.val
  have hvar : (VAR i).testBit r.val = r.val.testBit i := var_testBit ⟨i, hi⟩ r
  unfold fastBitMask
  split
  · simp [Nat.testBit_xor, hall, hvar]
  · split
    · exact hvar
    · exact hall
lemma subcubeFast_eq_subcube (z o : Nat) (hz : z < 256) (ho : o < 256) (hzo : (z &&& o) = 0) :
    subcubeFast z o = subcube z o := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 256
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
      fastBitMask_testBit z o 6 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 7 (by decide) ⟨r, hr⟩]
    have hbit (i : Nat) (hi : i < 8) :
        ((r &&& z).testBit i = false ∧ (r &&& o).testBit i = o.testBit i) ↔
          (if z.testBit i then !r.testBit i else if o.testBit i then r.testBit i else true) = true := by
      have hzi : (z.testBit i && o.testBit i) = false := by
        have := congrArg (fun x => x.testBit i) hzo; simpa [Nat.testBit_and] using this
      simp only [Nat.testBit_and]
      cases hz' : z.testBit i <;> cases ho' : o.testBit i <;> cases hr' : r.testBit i <;> simp_all
    have heq_iff : (((r &&& z == 0) && (r &&& o == o)) = true) ↔
        ∀ i < 8, (r &&& z).testBit i = false ∧ (r &&& o).testBit i = o.testBit i := by
      simp only [Bool.and_eq_true, beq_iff_eq]
      constructor
      · rintro ⟨h1, h2⟩ i _; rw [h1, h2, Nat.zero_testBit]; exact ⟨rfl, rfl⟩
      · intro h
        constructor
        · apply Nat.eq_of_testBit_eq; intro i
          rw [Nat.zero_testBit]
          by_cases hi : i < 8
          · exact (h i hi).1
          · have hzf : z.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hz (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 8 ≤ i)))
            simp [Nat.testBit_and, hzf]
        · apply Nat.eq_of_testBit_eq; intro i
          by_cases hi : i < 8
          · exact (h i hi).2
          · have hof : o.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ho (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 8 ≤ i)))
            simp [Nat.testBit_and, hof]
    apply Bool.eq_iff_iff.mpr
    rw [heq_iff]
    simp only [Bool.and_eq_true]
    constructor
    · intro h i hi
      have := hbit i hi
      interval_cases i <;> tauto
    · intro h
      refine ⟨⟨⟨⟨⟨⟨⟨(hbit 0 (by decide)).mp (h 0 (by decide)), (hbit 1 (by decide)).mp (h 1 (by decide))⟩,
        (hbit 2 (by decide)).mp (h 2 (by decide))⟩, (hbit 3 (by decide)).mp (h 3 (by decide))⟩,
        (hbit 4 (by decide)).mp (h 4 (by decide))⟩, (hbit 5 (by decide)).mp (h 5 (by decide))⟩,
        (hbit 6 (by decide)).mp (h 6 (by decide))⟩, (hbit 7 (by decide)).mp (h 7 (by decide))⟩
  · have hlt_f (i : Nat) : (fastBitMask z o i).testBit r = false := by
      have hle : 256 ≤ r := by omega
      have ha : ALL256 < 2^256 := by decide
      have hv : VAR i < 2^256 := by
        unfold VAR; rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · change (0 : Nat) < 2^256; decide
      have hlt_m : fastBitMask z o i < 2^256 := by
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
    (hT : T < 2^256)
    (hPools : ∀ c ∈ pools, ValidPool raw T c)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : btAll (fun b => ∀ xs ∈ b, Impossible T k xs.toFinset) prevBks)
    (nd : (choiceVal op :: rest).Nodup)
    (hlt : ∀ x ∈ choiceVal op :: rest, x < 2^256)
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
    have hinv_w : ∀ x : Nat, x < 2^256 → permWord sw.reverse (permWord sw x) = x := by
      intro x hx
      have h1 := permWord_eq_renameW sw hsv x hx
      have h2 := permWord_eq_renameW sw.reverse hvr (permWord sw x) (h1 ▸ renameW_lt _ x)
      rw [h2, h1]
      apply Nat.eq_of_testBit_eq; intro r
      by_cases hrr : r < 256
      · rw [testBit_renameW _ _ ⟨r, hrr⟩, testBit_renameW, hinv_row2]
      · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))),
            Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)))]
    have hfixr : permWord sw.reverse T = T := by
      have := hinv_w T hT; rwa [hfix] at this
    have hmap_lt : ∀ a ∈ (choiceVal op :: rest).map (permWord sw), a < 2^256 := by
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
        let okAB := !miss.contains a && !miss.contains b
        if k + c.paid + 1 < base && okAB then true
        else
          let zIn := c.pm.contains m || c.pm.contains (c.dom ^^^ m)
          if zIn then true
          else decide (k + c.paid + 1 < base) && okAB
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
          cases hpm : (c.pm.contains m || c.pm.contains (c.dom ^^^ m))
          · simp only [hpm, Bool.false_eq_true, ↓reduceIte] at hcut
          · simp only [Bool.not_true, Bool.not_false, Bool.toNat_false, Bool.true_or]
            exact ⟨by omega, trivial⟩
def evalMoveBT (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (fpools : List FastPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat)))
    (d : Nat) (a b z : Decor) (ka kb : Bool) : Bool :=
  let len := 1 + (n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len > cap then true else
    let rs := restCov cov (dsep a) (dsep b) ka kb
    if ((rs ||| dsep z) &&& fmask) != fmask then true else
    if fpools.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 z.1 ka kb) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChildBT [] autos prevBks (cap - 1) rest (d, a.1, b.1)
def testPairBT (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (fpools : List FastPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (a b : Decor) (d : Nat) : Bool :=
  if n > cap + 1 then true else
  let z := dbin d a b
  if z.1 == 0 || ws.any (fun v => v.1 == z.1) then true else
    let go := evalMoveBT cap n fmask ws cov fpools autos prevBks d a b z
    if n > cap then go false false
    else if n == cap then go false false && go true false && go false true
    else go false false && go true false && go false true && go true true
def testAllBT (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (fpools : List FastPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) : List Decor → Bool
  | [] => true
  | a :: bs =>
    bs.all (fun b => [0, 1, 2, 3].all (testPairBT cap n fmask ws cov fpools autos prevBks a b)) &&
      testAllBT cap n fmask ws cov fpools autos prevBks bs
lemma evalMoveBT_sound {raw T pos neg ws fpools autos prevBks cap a b d ka kb}
    (hT : T < 2^256) (gp : goodPairs T pos neg) (hf : ∀ w ∈ ws, faithful pos neg w)
    (nd : (ws.map Prod.fst).Nodup) (hlt : ∀ w ∈ ws, w.1 < 2^256)
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
  have hltc : ∀ x ∈ child, x < 2^256 := by
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
  dsimp only [dbin] at test
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
    (hT : T < 2^256) (gp : goodPairs T pos neg)
    (hf : ∀ w ∈ ws, faithful pos neg w) (nd : (ws.map Prod.fst).Nodup)
    (hlt : ∀ w ∈ ws, w.1 < 2^256) (out : T ∉ ws.map Prod.fst)
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
      have hnz_b : (bin d' x.1 y.1 == 0) = false := beq_false_of_ne hnz'
      have hfr_b : (ws.any (fun v => v.1 == bin d' x.1 y.1)) = false := by
        rw [Bool.eq_false_iff]; intro h; obtain ⟨v, hv, heq⟩ := List.any_eq_true.mp h
        exact hfr' ((beq_iff_eq.mp heq) ▸ List.mem_map_of_mem hv)
      by_cases hlen : 1 + (ws.length - (if k1 then 0 else 1) - (if k2 then 0 else 1)) > cap
      · unfold evalMoveBT; simp [hlen]
      · unfold testPairBT at ht
        dsimp only [dbin] at ht
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
    (hbase : ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^256) :
    btAll (fun x => faithful pos neg x ∧ x.1 < 2^256) (buildWiresBT depth base steps) := by
  have hdef : faithful pos neg (0, 0, 0) ∧ (0 : Nat) < 2^256 := ⟨faithful_zero pos neg, by decide⟩
  unfold buildWiresBT
  have h0 : btAll (fun x => faithful pos neg x ∧ x.1 < 2^256) (btOfList depth base) := btAll_ofList hbase
  have hgo : ∀ (ss : List (Nat × Nat × Nat)) (acc : Nat × BT Decor),
      btAll (fun x => faithful pos neg x ∧ x.1 < 2^256) acc.2 →
      btAll (fun x => faithful pos neg x ∧ x.1 < 2^256)
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
    (hT : T < 2^256) (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^256) W)
    (hPoolTable : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) poolTable)
    (hAutos : btAll (fun sw => swapsValid sw = true ∧ permWord sw T = T) autosTable)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (k - 1) xs.toFinset) prevBks)
    (ok : checkNodeBT W T (fullMask pos.length) poolTable autosTable prevBks k ns = true) :
    Impossible T k ((ns.1.map fun idx => (btGet (0, 0, 0) W idx).1).toFinset) := by
  have hdef : faithful pos neg (0, 0, 0) ∧ (0 : Nat) < 2^256 := ⟨faithful_zero pos neg, by decide⟩
  have hget (idx : Nat) : faithful pos neg (btGet (0, 0, 0) W idx) ∧ (btGet (0, 0, 0) W idx).1 < 2^256 :=
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
    btUpdate [] 6 acc (hashWs64 xs) (fun b => if b.contains xs then b else xs :: b)) BT.empty
lemma buildBucketsBT_sound {W : BT Decor} {raw pos neg T poolTable autosTable prevBks k}
    {nodes : List NodeSpec}
    (hT : T < 2^256) (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^256) W)
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
    (hT : T < 2^256) (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^256) W)
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
lemma obs_all256_xor (G : Nat) : obs (ALL256 ^^^ G) = invW (obs G) := by
  funext r
  have hall : ALL256.testBit r.val = true := by
    simp only [ALL256]; have hr := r.isLt; simpa [hr] using Nat.testBit_two_pow_sub_one 256 r.val
  simp only [obs, invW, Nat.testBit_xor, hall, Bool.true_xor]
lemma lower_slice_flip {roots other : List Nat} {T G : Nat}
    (hT0 : T ≠ 0) (hTlt : T < 2^256) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^256 ∧ a.testBit 0 = false)
    (hG0 : G ≠ 0) (hGlt : G < 2^256) (hGb0 : G.testBit 0 = false)
    (f : Row → Row) (eq : renameW f T = G ∨ renameW f T = ALL256 ^^^ G)
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
      (obs_renameW f T).symm.trans ((congrArg obs heq).trans (obs_all256_xor G))
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
    (fixWord z o T == G || fixWord z o T == ALL256 ^^^ G) &&
    roots.all (fun a => freeIn other (fixWord z o a)) &&
    essPairs.all (fun e => checkEss1 T roots e.1 e.2.1 e.2.2 &&
      (fixWord z o e.1 == 0 || fixWord z o e.1 == ALL256))
lemma lift_of_f {z o roots T other G essPairs L} (ok : liftCheckF z o roots T other G essPairs = true)
    (hL : Lower other G L) : Lower roots T (L + essPairs.length) := by
  simp only [liftCheckF, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨⟨hT, hR⟩, hG⟩, hnd⟩, heq⟩, hcov⟩, hess⟩ := ok
  have ⟨p1a, p1b, p1c⟩ := checkProper_sound hT
  have ⟨p2a, p2b, p2c⟩ := checkProper_sound hG
  have hR' := checkRoots_sound hR
  have heq' : renameW (fixRow z o) T = G ∨ renameW (fixRow z o) T = ALL256 ^^^ G := by
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
    · exact ⟨true, by rw [h1]; funext r'; simp only [obs, ALL256]; have := r'.isLt; exact Nat.testBit_two_pow_sub_one 256 r'.val |> fun e => by simpa [this] using e⟩
def sliceDirectCheckF (z o : Nat) (raw : List Nat) (T : Nat) (qRoots : List Nat) (qGoal : Nat) : Bool :=
  decide (z < 256) && decide (o < 256) && ((z &&& o) == 0) &&
    checkProper qGoal && checkRoots qRoots &&
    (fixWord z o T == qGoal || fixWord z o T == ALL256 ^^^ qGoal) &&
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
      by rw [← obs_renameW, ← fixWord_eq_renameW, heq, obs_all256_xor]; exact fun hc => obs_not_const g0 glt gb0 (invW_inv (obs qGoal) ▸ invW_const hc), ?_⟩
    rw [← obs_renameW, ← fixWord_eq_renameW, heq, obs_all256_xor]
    intro p bank hr hav
    exact hPrior p bank hr (by simpa [invW_inv] using avail_inv hav)
def identRow (u v : Nat) (r : Row) : Row :=
  if r.val.testBit u == r.val.testBit v then r
  else ⟨(r.val ^^^ (1 <<< v)) % 256, Nat.mod_lt _ (by decide)⟩
def identDom (u v : Nat) : Nat := ALL256 ^^^ (VAR u ^^^ VAR v)
def identWord (u v w : Nat) : Nat :=
  (List.range 256).foldr (fun r acc =>
    let fr := if r.testBit u == r.testBit v then r else (r ^^^ (1 <<< v)) % 256
    if w.testBit fr then acc ||| (1 <<< r) else acc) 0
lemma identWord_eq_renameW (u v w : Nat) : identWord u v w = renameW (identRow u v) w := by
  apply Nat.eq_of_testBit_eq; intro r
  unfold identWord
  rw [testBit_foldr_bits]
  by_cases hr : r < 256
  · rw [testBit_renameW (identRow u v) w ⟨r, hr⟩]
    simp only [List.mem_range, hr, decide_true, Bool.true_and, identRow]
    split <;> rfl
  · simp only [List.mem_range, hr, decide_false, Bool.false_and]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))).symm
lemma identDom_identRow (u v : Nat) (hu : u < 8) (hv : v < 8) (r : Row) :
    (identDom u v).testBit (identRow u v r).val = true := by
  revert r
  interval_cases u <;> interval_cases v <;> decide +kernel
def sliceIdentCheck (u v : Nat) (raw : List Nat) (T : Nat) (qRoots : List Nat) (qGoal : Nat) : Bool :=
  decide (u < 8) && decide (v < 8) &&
    checkProper qGoal && checkRoots qRoots &&
    (identWord u v T == qGoal || identWord u v T == ALL256 ^^^ qGoal) &&
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
      by rw [← obs_renameW, ← identWord_eq_renameW, heq, obs_all256_xor]; exact fun hc => obs_not_const g0 glt gb0 (invW_inv (obs qGoal) ▸ invW_const hc), ?_⟩
    rw [← obs_renameW, ← identWord_eq_renameW, heq, obs_all256_xor]
    intro p bank hr hav
    exact hPrior p bank hr (by simpa [invW_inv] using avail_inv hav)
def mkBase (pos neg : List Nat) (rs : List Nat) : List Decor :=
  rs.map fun w => (w, projBits pos w, projBits neg w)
lemma mkBase_ok {pos neg rs} (hR : checkRoots rs = true) :
    ∀ x ∈ mkBase pos neg rs, faithful pos neg x ∧ x.1 < 2^256 := by
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
lemma sw_extract_full6 (T : Nat) (hT0 : T ≠ 0) (hTlt : T < 2^256) (hTb0 : T.testBit 0 = false)
    (gs : List Gate) (o : Nat)
    (legal : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (he : ∀ r : Row, Circuit.eval ⟨gs, o⟩ (List.ofFn (evalInput6 r)) = T.testBit r.val) :
    ∃ k S, k ≤ gs.countP isBin ∧ Live T k S ∧ ∀ a ∈ S, a ∈ varsOf 63 := by
  let seeds : List SWire := (varsOf 63).map (fun v => (false, v))
  have hseeds_lt : ∀ u ∈ seeds, u.2 < 2^256 ∧ u.2.testBit 0 = false := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
    have hall : (varsOf 63).all (fun a => decide (a < 2^256) && !a.testBit 0) = true := by decide +kernel
    have h1 := List.all_eq_true.mp hall v hv
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h1
    exact h1
  let final := swExec gs seeds
  let out := final.getD o swZero
  have hfinal_lt : out.2 < 2^256 ∧ out.2.testBit 0 = false := by
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
    by_cases hr : r < 256
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
lemma replace_of_lower6 (T : Nat) (hT0 : T ≠ 0) (hTlt : T < 2^256) (hTb0 : T.testBit 0 = false)
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
def d (x : Nat) : Nat := x * 0x1000000000000000100000000000000010000000000000001
def r (a n : Nat) : List Nat := List.range' a n
def b6 : List Nat := [0,1,2,3,4,5]
def b5 : List Nat := [0,1,2,3,4]
def u6 (w p : List Nat) : NodeSpec := (b6 ++ w, p, [0])
def e6 (w p : List Nat) : NodeSpec := (b6 ++ w, p, [])
def a6 (w p a : List Nat) : NodeSpec := (b6 ++ w, p, a)
def u5 (w p : List Nat) : NodeSpec := (b5 ++ w, p, [0])
def e5 (w p : List Nat) : NodeSpec := (b5 ++ w, p, [])
def a5 (w p a : List Nat) : NodeSpec := (b5 ++ w, p, a)

def g_0 := (d 0xe8e8e8e8e8e8e8e8)
def r_0 : List Nat := varsOf 7
def p_0 : List Nat := [3,3,5,5,6,6]
def q_0 : List Nat := [2,1,4,1,4,2]
def F_0 : Nat := fullMask 6
set_option maxHeartbeats 0 in
lemma gp_0 : goodPairs g_0 p_0 q_0 := goodPairs_of (by decide +kernel)
def W_0 : BT Decor := buildWiresBT 2 (mkBase p_0 q_0 r_0) []
lemma W_0_ok : btAll (fun x => faithful p_0 q_0 x ∧ x.1 < 2^256) W_0 := buildWiresBT_faithful (mkBase_ok (by decide))
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
def g_1 := (d 0xfee8fee8fee8fee8)
def r_1 : List Nat := varsOf 15
def p_1 : List Nat := [3,3,5,5,6,6,9,9,10,10,12,12]
def q_1 : List Nat := [2,1,4,1,4,2,8,1,8,2,8,4]
def F_1 : Nat := fullMask 12
set_option maxHeartbeats 0 in
lemma gp_1 : goodPairs g_1 p_1 q_1 := goodPairs_of (by decide +kernel)
def W_1 : BT Decor := buildWiresBT 4 (mkBase p_1 q_1 r_1) [(1,0,1),(1,4,2),(2,5,3),(1,1,2),(1,3,1),(1,3,2),(2,4,3),(1,3,0)]
lemma W_1_ok : btAll (fun x => faithful p_1 q_1 x ∧ x.1 < 2^256) W_1 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_1 : List (List (Nat × Nat)) := [[],[(2,3)],[(1,2)],[(1,3),(2,3)],[(1,2),(2,3)],[(1,3)],[(0,2),(1,2)],[(0,3),(1,3),(2,3)],[(0,2),(1,2),(2,3)],[(0,3),(1,3)],[(0,1),(1,2)],[(0,2),(1,3)]]
def A_1 : BT (List (Nat × Nat)) := btOfList 4 al_1
set_option maxHeartbeats 0 in
lemma A_1_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_1 = g_1) A_1 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_1_0 : Slice r_1 g_1 (subcubeFast 1 0) 4 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_1_1 : Slice r_1 g_1 (subcubeFast 2 0) 4 := by
  have hc : Lower (varsOf 13) (d 0xfaa0faa0faa0faa0) 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_1_2 : Slice r_1 g_1 (subcubeFast 4 0) 4 := by
  have hc : Lower (varsOf 11) (d 0xee88ee88ee88ee88) 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_0
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
def N_1_3 : List NodeSpec := [([6,0,1,2],[],[]),([0,7,8,9],[0,1],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_1_3 : checkNodesBT W_1 g_1 F_1 P_1_3 A_1 B_1_2 3 N_1_3 = true := by decide +kernel
def B_1_3 : BT (List (List Nat)) := buildBucketsBT W_1 N_1_3
set_option maxRecDepth 500000 in
lemma B_1_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_1 3 xs.toFinset) B_1_3 :=
  buildBucketsBT_sound (by decide) gp_1 W_1_ok (buildPoolsSubBT_sound S_1_ok) A_1_ok B_1_2_ok C_1_3
def U_1_4 : List Nat := [1,2,3]
def P_1_4 : BT (Option BoundPool) := buildPoolsSubBT 2 W_1 r_1 S_1 ps_1 U_1_4
def N_1_4 : List NodeSpec := [([0,1,2,5,3],[2],[0]),([10,0,1,2,3],[],[]),([0,1,2,11,8],[1,3],[10])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_1_4 : checkNodesBT W_1 g_1 F_1 P_1_4 A_1 B_1_3 4 N_1_4 = true := by decide +kernel
def B_1_4 : BT (List (List Nat)) := buildBucketsBT W_1 N_1_4
set_option maxRecDepth 500000 in
lemma B_1_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_1 4 xs.toFinset) B_1_4 :=
  buildBucketsBT_sound (by decide) gp_1 W_1_ok (buildPoolsSubBT_sound S_1_ok) A_1_ok B_1_3_ok C_1_4
def U_1_5 : List Nat := (r 0 4)
def P_1_5 : BT (Option BoundPool) := buildPoolsSubBT 2 W_1 r_1 S_1 ps_1 U_1_5
def N_1_5 : List NodeSpec := [([0,1,4,2,3],(r 0 4),[0,1,3,5,7,9])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_1_5 : checkNodesBT W_1 g_1 F_1 P_1_5 A_1 B_1_4 5 N_1_5 = true := by decide +kernel
def B_1_5 : BT (List (List Nat)) := buildBucketsBT W_1 N_1_5
set_option maxRecDepth 500000 in
lemma B_1_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_1 5 xs.toFinset) B_1_5 :=
  buildBucketsBT_sound (by decide) gp_1 W_1_ok (buildPoolsSubBT_sound S_1_ok) A_1_ok B_1_4_ok C_1_5
def U_1_6 : List Nat := (r 0 4)
def P_1_6 : BT (Option BoundPool) := buildPoolsSubBT 2 W_1 r_1 S_1 ps_1 U_1_6
def N_1_6 : List NodeSpec := [([0,1,2,3],(r 0 4),[0,2,4,6,8,11])]
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
def g_2 := (d 0xe880e880e880e880)
def r_2 : List Nat := varsOf 15
def p_2 : List Nat := [7,7,7,11,11,11,13,13,13,14,14,14]
def q_2 : List Nat := [6,5,3,10,9,3,12,9,5,12,10,6]
def F_2 : Nat := fullMask 12
set_option maxHeartbeats 0 in
lemma gp_2 : goodPairs g_2 p_2 q_2 := goodPairs_of (by decide +kernel)
def W_2 : BT Decor := buildWiresBT 4 (mkBase p_2 q_2 r_2) [(0,0,1),(0,0,2),(0,1,2),(0,6,3),(3,7,0),(0,2,3),(3,9,0),(0,4,2)]
lemma W_2_ok : btAll (fun x => faithful p_2 q_2 x ∧ x.1 < 2^256) W_2 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_2 : List (List (Nat × Nat)) := [[],[(2,3)],[(1,2)],[(1,2),(2,3)],[(0,1)],[(0,1),(2,3)],[(0,2),(1,2)],[(0,2),(1,2),(2,3)],[(0,2),(1,3)],[(0,1),(1,2),(2,3)],[(0,2),(1,3),(2,3)]]
def A_2 : BT (List (Nat × Nat)) := btOfList 4 al_2
set_option maxHeartbeats 0 in
lemma A_2_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_2 = g_2) A_2 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_2_0 : Slice r_2 g_2 (subcubeFast 0 1) 4 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_2_1 : Slice r_2 g_2 (subcubeFast 0 2) 4 := by
  have hc : Lower (varsOf 13) (d 0xfaa0faa0faa0faa0) 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_2_2 : Slice r_2 g_2 (subcubeFast 0 4) 4 := by
  have hc : Lower (varsOf 11) (d 0xee88ee88ee88ee88) 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_0
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
def N_2_4 : List NodeSpec := [([4,5,1,2,3],[0,2],[0]),([10,0,1,2,3],[],[]),([11,0,1,2,3],[3],[9])]
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
def N_2_6 : List NodeSpec := [([0,1,2,3],(r 0 4),[0,2,3,6,7,8])]
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
def g_3 := (d 0xfc80fc80fc80fc80)
def r_3 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_3 : Lower r_3 g_3 5 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,6,7)]) (by decide +kernel) hc
def g_4 := (d 0xf880f880f880f880)
def r_4 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_4 : Lower r_4 g_4 5 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,6,7)]) (by decide +kernel) hc
def g_5 := (d 0xffe8ffe8ffe8ffe8)
def r_5 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_5 : Lower r_5 g_5 5 := by
  exact lift_of_f (z := 8) (o := 0) (other := r_0) (G := g_0) (essPairs := [(VAR 3,0,8)]) (by decide +kernel) low_0
def g_6 := (d 0xfe80fe80fe80fe80)
def r_6 : List Nat := varsOf 15
def p_6 : List Nat := [7,7,7,9,9,10,10,11,12,12,13,14]
def q_6 : List Nat := [6,5,3,8,1,8,2,3,8,4,5,6]
def F_6 : Nat := fullMask 12
set_option maxHeartbeats 0 in
lemma gp_6 : goodPairs g_6 p_6 q_6 := goodPairs_of (by decide +kernel)
def W_6 : BT Decor := buildWiresBT 5 (mkBase p_6 q_6 r_6) [(0,2,3),(1,2,3),(3,4,5),(0,1,2),(1,1,2),(3,7,8),(2,0,3),(3,0,3),(1,0,3),(3,2,12),(1,1,3),(0,0,14),(0,0,3),(1,16,2),(3,4,0),(2,0,2),(3,0,2),(2,2,1),(3,21,0),(2,0,1),(1,23,2),(0,0,1),(1,0,1),(3,2,3)]
lemma W_6_ok : btAll (fun x => faithful p_6 q_6 x ∧ x.1 < 2^256) W_6 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_6 : List (List (Nat × Nat)) := [[],[(1,2)],[(0,1)],[(0,2),(1,2)],[(0,1),(1,2)],[(0,2)]]
def A_6 : BT (List (Nat × Nat)) := btOfList 3 al_6
set_option maxHeartbeats 0 in
lemma A_6_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_6 = g_6) A_6 := btAll_ofList (autos_of (by decide +kernel))
def S_6 : BT (Option (Nat × Nat)) := btOfList 1 []
lemma S_6_ok : btAll (fun o => ∀ p, o = some p → Slice r_6 g_6 p.1 p.2) S_6 := btAll_ofList (fun _ h => (List.not_mem_nil h).elim)
def ps_6 : BT (Option PoolSpec) := btOfList 1 []
def B_6_1 : BT (List (List Nat)) := BT.empty
lemma B_6_1_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_6 1 xs.toFinset) B_6_1 := .empty
def U_6_2 : List Nat := []
def P_6_2 : BT (Option BoundPool) := buildPoolsSubBT 1 W_6 r_6 S_6 ps_6 U_6_2
def N_6_2 : List NodeSpec := [([6,0,1],[],[]),([9,0,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_6_2 : checkNodesBT W_6 g_6 F_6 P_6_2 A_6 B_6_1 2 N_6_2 = true := by decide +kernel
def B_6_2 : BT (List (List Nat)) := buildBucketsBT W_6 N_6_2
set_option maxRecDepth 500000 in
lemma B_6_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_6 2 xs.toFinset) B_6_2 :=
  buildBucketsBT_sound (by decide) gp_6 W_6_ok (buildPoolsSubBT_sound S_6_ok) A_6_ok B_6_1_ok C_6_2
def U_6_3 : List Nat := []
def P_6_3 : BT (Option BoundPool) := buildPoolsSubBT 1 W_6 r_6 S_6 ps_6 U_6_3
def N_6_3 : List NodeSpec := [([10,11,1,2],[],[3]),([13,0,1,3],[],[]),([15,1,2,3],[],[]),([16,1,2,12],[],[3]),([0,1,17,3],[],[]),([18,1,2,3],[],[]),([19,20,1,3],[],[2]),([22,1,2,3],[],[]),([0,1,24,3],[],[]),([25,26,2,3],[],[4])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_6_3 : checkNodesBT W_6 g_6 F_6 P_6_3 A_6 B_6_2 3 N_6_3 = true := by decide +kernel
def B_6_3 : BT (List (List Nat)) := buildBucketsBT W_6 N_6_3
set_option maxRecDepth 500000 in
lemma B_6_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_6 3 xs.toFinset) B_6_3 :=
  buildBucketsBT_sound (by decide) gp_6 W_6_ok (buildPoolsSubBT_sound S_6_ok) A_6_ok B_6_2_ok C_6_3
def U_6_4 : List Nat := []
def P_6_4 : BT (Option BoundPool) := buildPoolsSubBT 1 W_6 r_6 S_6 ps_6 U_6_4
def N_6_4 : List NodeSpec := [([27,0,1,2,3],[],[4]),([10,0,1,2,3],[],[0]),([0,1,2,3,12],[],[0,1,2,4]),([16,0,1,2,3],[],[0,1,3,5]),([19,0,1,2,3],[],[0,1,3]),([0,1,26,2,3],[],[0]),([25,0,1,2,3],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_6_4 : checkNodesBT W_6 g_6 F_6 P_6_4 A_6 B_6_3 4 N_6_4 = true := by decide +kernel
def B_6_4 : BT (List (List Nat)) := buildBucketsBT W_6 N_6_4
set_option maxRecDepth 500000 in
lemma B_6_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_6 4 xs.toFinset) B_6_4 :=
  buildBucketsBT_sound (by decide) gp_6 W_6_ok (buildPoolsSubBT_sound S_6_ok) A_6_ok B_6_3_ok C_6_4
def U_6_5 : List Nat := []
def P_6_5 : BT (Option BoundPool) := buildPoolsSubBT 1 W_6 r_6 S_6 ps_6 U_6_5
def N_6_5 : List NodeSpec := [([0,1,2,3],[],[0,1,2,3,4,5])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_6_5 : checkNodesBT W_6 g_6 F_6 P_6_5 A_6 B_6_4 5 N_6_5 = true := by decide +kernel
def B_6_5 : BT (List (List Nat)) := buildBucketsBT W_6 N_6_5
set_option maxRecDepth 500000 in
lemma B_6_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_6 5 xs.toFinset) B_6_5 :=
  buildBucketsBT_sound (by decide) gp_6 W_6_ok (buildPoolsSubBT_sound S_6_ok) A_6_ok B_6_4_ok C_6_5
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_6_ok : forestRootCheck r_6 g_6 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,1,9)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_6_in : bucketContainsBT B_6_5 r_6 = true := by decide +kernel
lemma low_6 : Lower r_6 g_6 6 := lower_of_forestBT root_6_ok B_6_5_ok root_6_in
def g_7 := (d 0xfff8e880fff8e880)
def r_7 : List Nat := varsOf 31
def p_7 : List Nat := [7,7,7,11,11,11,13,13,13,14,14,14,19,19,19,20,20,21,21,22,22,24,24,25,25,26,26,28]
def q_7 : List Nat := [6,5,3,10,9,3,12,9,5,12,10,6,18,17,3,16,4,17,5,18,6,16,8,17,9,18,10,12]
def F_7 : Nat := fullMask 28
set_option maxHeartbeats 0 in
lemma gp_7 : goodPairs g_7 p_7 q_7 := goodPairs_of (by decide +kernel)
def W_7 : BT Decor := buildWiresBT 8 (mkBase p_7 q_7 r_7) [(1,2,3),(0,0,1),(1,6,4),(0,5,7),(0,2,3),(1,9,4),(0,6,2),(1,11,4),(0,3,12),(1,3,12),(3,13,14),(1,6,9),(2,16,4),(0,0,5),(2,0,4),(0,0,3),(0,1,2),(1,20,21),(2,22,4),(1,21,4),(1,20,24),(0,0,2),(1,26,4),(0,1,3),(1,28,4),(1,6,2),(1,30,4),(3,6,31),(0,6,3),(1,33,4),(0,2,34),(1,2,34),(3,3,36),(3,6,10),(1,9,7),(1,3,4),(1,2,4),(0,0,41),(1,20,4),(1,37,33),(0,1,41),(0,3,24),(1,3,24),(3,46,47),(1,28,2),(1,49,4),(0,0,50),(0,2,29),(0,3,41),(0,3,7),(1,54,2),(1,3,7),(0,6,5),(1,57,4),(2,6,4),(1,59,9),(3,54,56),(2,2,34),(3,2,34),(0,2,7),(0,3,31),(3,45,3),(2,5,4),(2,2,7),(3,2,7),(0,2,56),(3,54,2),(1,5,4),(1,30,3),(3,6,73),(2,2,3),(1,75,4),(2,5,7),(3,3,7),(3,6,3),(2,30,4),(3,6,2),(1,6,3),(3,28,41),(2,2,4),(3,79,41),(3,33,41),(3,79,40),(3,28,2),(1,88,4),(3,3,31),(0,0,10),(2,1,4),(3,92,0),(3,3,27),(0,1,5),(2,73,4),(1,75,7),(3,21,3),(3,59,5),(2,0,46),(1,79,2),(1,59,75),(1,74,4),(1,37,6),(1,79,4),(3,3,30),(3,79,5),(0,2,43),(2,3,2),(3,109,7),(1,81,4),(1,75,6),(2,112,4),(0,6,40),(3,114,2),(2,3,4),(1,116,2),(3,3,12),(2,0,29),(3,6,72),(1,64,3),(3,26,3),(3,6,117),(3,28,0),(1,26,3),(3,9,7),(1,20,2),(2,127,4),(3,122,40),(3,28,27),(3,20,0),(1,131,4),(1,2,43),(2,2,29),(3,2,29),(1,19,2),(3,28,136),(0,28,41),(3,138,0),(0,0,40),(0,2,40),(3,2,14),(1,142,26),(2,0,10),(2,9,4),(3,145,5),(3,95,0),(3,75,41),(2,0,53),(0,1,40),(3,150,0),(3,84,3),(3,109,40),(3,150,2),(1,84,6),(1,92,3),(1,122,4),(2,1,2),(3,158,0),(1,18,4),(3,33,2),(3,19,3),(0,0,24),(0,26,40),(1,116,26),(1,158,4),(2,1,3),(3,167,2),(1,168,4),(1,125,4),(3,167,0),(1,11,3),(0,26,3),(1,173,4),(0,6,41),(0,21,3),(3,176,0),(0,0,72),(1,167,4),(1,75,20),(3,142,0),(1,92,2),(3,158,40),(3,116,2),(3,116,0),(2,75,4),(3,109,0),(2,26,3),(2,26,4),(2,6,3),(3,92,2),(2,0,9),(2,131,2),(1,131,2),(2,131,4)]
lemma W_7_ok : btAll (fun x => faithful p_7 q_7 x ∧ x.1 < 2^256) W_7 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_7 : List (List (Nat × Nat)) := [[],[(2,3)],[(0,1)],[(0,1),(2,3)]]
def A_7 : BT (List (Nat × Nat)) := btOfList 2 al_7
set_option maxHeartbeats 0 in
lemma A_7_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_7 = g_7) A_7 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_7_0 : Slice r_7 g_7 (subcubeFast 0 1) 7 := by
  have hc : Lower (varsOf 30) (d 0xfffcfcc0fffcfcc0) 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_1 : Slice r_7 g_7 (subcubeFast 0 2) 7 := by
  have hc : Lower (varsOf 29) (d 0xfffafaa0fffafaa0) 7 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_2 : Slice r_7 g_7 (subcubeFast 16 0) 7 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_2
set_option maxHeartbeats 0 in
lemma sl_7_3 : Slice r_7 g_7 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) (d 0xfff0a000fff0a000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_4 : Slice r_7 g_7 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) (d 0xff888800ff888800) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_5 : Slice r_7 g_7 (subcubeFast 0 4) 5 := by
  have hc : Lower (varsOf 27) (d 0xffffee88ffffee88) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_6 : Slice r_7 g_7 (subcubeFast 8 0) 5 := by
  have hc : Lower (varsOf 23) (d 0xf8f88080f8f88080) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_7 : Slice r_7 g_7 (subcubeFast 0 8) 5 := by
  have hc : Lower (varsOf 23) (d 0xffffe8e8ffffe8e8) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_8 : Slice r_7 g_7 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) (d 0xfff0c000fff0c000) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_9 : Slice r_7 g_7 (subcubeFast 16 8) 4 := by
  exact slice_fast_direct_f (z := 16) (o := 8) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_7_10 : Slice r_7 g_7 (subcubeFast 16 4) 4 := by
  have hc : Lower (varsOf 11) (d 0xee88ee88ee88ee88) 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_11 : Slice r_7 g_7 (subcubeFast 16 2) 4 := by
  have hc : Lower (varsOf 13) (d 0xfaa0faa0faa0faa0) 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_12 : Slice r_7 g_7 (subcubeFast 8 2) 4 := by
  have hc : Lower (varsOf 21) (d 0xfafaa0a0fafaa0a0) 4 := carry_of (swaps := [(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 8) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_13 : Slice r_7 g_7 (subcubeFast 4 2) 4 := by
  have hc : Lower (varsOf 25) (d 0xffaaaa00ffaaaa00) 4 := carry_of (swaps := [(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_14 : Slice r_7 g_7 (subcubeFast 16 1) 4 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_15 : Slice r_7 g_7 (subcubeFast 8 1) 4 := by
  have hc : Lower (varsOf 22) (d 0xfcfcc0c0fcfcc0c0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 8) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_16 : Slice r_7 g_7 (subcubeFast 4 1) 4 := by
  have hc : Lower (varsOf 26) (d 0xffcccc00ffcccc00) 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_17 : Slice r_7 g_7 (subcubeFast 2 1) 4 := by
  have hc : Lower (varsOf 28) (d 0xfff0f000fff0f000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 2) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_18 : Slice r_7 g_7 (subcubeFast 1 2) 4 := by
  have hc : Lower (varsOf 28) (d 0xfff0f000fff0f000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_19 : Slice r_7 g_7 (identDom 2 3) 6 := by
  have hc : Lower (varsOf 23) (d 0xf8f8e0e0f8f8e0e0) 6 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_6
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
def S_7 : BT (Option (Nat × Nat)) := btOfList 5 [some (subcubeFast 0 1,7),some (subcubeFast 0 2,7),some (subcubeFast 16 0,7),some (subcubeFast 2 0,5),some (subcubeFast 4 0,5),some (subcubeFast 0 4,5),some (subcubeFast 8 0,5),some (subcubeFast 0 8,5),some (subcubeFast 1 0,5),some (subcubeFast 16 8,4),some (subcubeFast 16 4,4),some (subcubeFast 16 2,4),some (subcubeFast 8 2,4),some (subcubeFast 4 2,4),some (subcubeFast 16 1,4),some (subcubeFast 8 1,4),some (subcubeFast 4 1,4),some (subcubeFast 2 1,4),some (subcubeFast 1 2,4),some (identDom 2 3,6)]
lemma S_7_ok : btAll (fun o => ∀ p, o = some p → Slice r_7 g_7 p.1 p.2) S_7 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_7_0) (forall_cons (fun _ h => by cases h; exact sl_7_1) (forall_cons (fun _ h => by cases h; exact sl_7_2) (forall_cons (fun _ h => by cases h; exact sl_7_3) (forall_cons (fun _ h => by cases h; exact sl_7_4) (forall_cons (fun _ h => by cases h; exact sl_7_5) (forall_cons (fun _ h => by cases h; exact sl_7_6) (forall_cons (fun _ h => by cases h; exact sl_7_7) (forall_cons (fun _ h => by cases h; exact sl_7_8) (forall_cons (fun _ h => by cases h; exact sl_7_9) (forall_cons (fun _ h => by cases h; exact sl_7_10) (forall_cons (fun _ h => by cases h; exact sl_7_11) (forall_cons (fun _ h => by cases h; exact sl_7_12) (forall_cons (fun _ h => by cases h; exact sl_7_13) (forall_cons (fun _ h => by cases h; exact sl_7_14) (forall_cons (fun _ h => by cases h; exact sl_7_15) (forall_cons (fun _ h => by cases h; exact sl_7_16) (forall_cons (fun _ h => by cases h; exact sl_7_17) (forall_cons (fun _ h => by cases h; exact sl_7_18) (forall_cons (fun _ h => by cases h; exact sl_7_19) (fun _ h => (List.not_mem_nil h).elim)))))))))))))))))))))
set_option maxRecDepth 500000 in
def ps_7 : BT (Option PoolSpec) := btOfList 9 [q 1 [12296,36889,12297],q 1 [],q 0 [],q 4 [4],q 6 [4],q 19 [],q 19 [4096,20504,16613],q 5 [],q 7 [],q 4 [],q 19 [4096,16410],q 1 [12296,36889],q 8 [],q 3 [],q 1 [16409,16393,167936],q 19 [4096,20507],q 2 [12296,12297],q 0 [12296,16421,12297],q 1 [12296,16421,12297],q 1 [12296,12297],q 19 [4096,20480],q 6 [],q 0 [12313,16409,16397],q 2 [4096,12313],q 0 [8217,12313,12297],q 12 [],q 9 [],q 5 [16386],q 2 [4096,12312,168071],q 19 [4096,16386],q 2 [],q 19 [4096,16409],q 19 [16390,371],q 1 [12297],q 0 [12297],q 0 [8216,16429],q 1 [8216,16429],q 0 [8217,12409,16678],q 2 [12288],q 2 [4096,163864,8651],q 0 [8217,16505,126991],q 15 [],q 3 [12288],q 0 [12296,36889,12297],q 0 [12297,16405,294939],q 19 [4096,20504],q 0 [12312,16517],q 1 [12312,16517],q 2 [4096,12312],q 10 [],q 0 [8196,16469],q 1 [16393],q 0 [16393],q 0 [12393,16489,16397],q 2 [8192,12393],q 2 [12292,168048,555],q 0 [16397,163848],q 2 [8192,163840,163848],q 0 [16489,16397,163848],q 2 [12296,12297,21063],q 19 [20484,383],q 0 [16393,167948],q 2 [167948,217090],q 0 [16393,167951],q 2 [167936],q 2 [167936,167948],q 0 [16393,167940],q 0 [16397,163844],q 2 [163844,603],q 2 [12298,12627],q 0 [12298,16393],q 2 [8206,164279],q 13 [],q 2 [8205,163848],q 0 [12296,12297],q 19 [20480],q 19 [16421],q 1 [16397],q 2 [163844,8795],q 0 [12296,16421],q 0 [12297,20484],q 2 [12296,8231,12589],q 0 [12296,8231,12589],q 0 [12297,16406],q 2 [12297],q 19 [16386],q 17 [],q 1 [371],q 2 [371],q 0 [12296,36889],q 0 [16394,24913],q 1 [12297,20480],q 1 [12296],q 4 [4096],q 3 [16386],q 2 [12296],q 1 [16386],q 1 [12288],q 1 [16394],q 2 [4096,12288],q 2 [167951],q 2 [4096,28687],q 0 [16409,28687],q 0 [12298,24877],q 0 [16398,8657],q 3 [8192],q 1 [8192],q 2 [4096,8192],q 1 [12657],q 0 [16390,12657],q 2 [4096],q 1 [16409],q 0 [16409],q 0 [16409,16393],q 1 [16409,16393],q 14 [],q 1 [12298],q 19 [4096],q 0 [16465],q 1 [12288,16465],q 0 [12298,8495,16421],q 1 [12298,8495,16421],q 2 [4096,12315],q 1 [16393,168051],q 2 [12292,168051],q 0 [8217,12409],q 2 [8192,12395],q 0 [12395,16873],q 2 [8198,635],q 7 [16386],q 0 [8196,86097],q 1 [12288,86097],q 16 [],q 0 [12297,16457],q 1 [12297,20480,16457],q 0 [12315,8509],q 0 [12312,8327],q 1 [12312,8327],q 2 [4096,12312,8327],q 1 [12290,16386,12367],q 2 [12290,12367],q 0 [8217,12298],q 1 [12296,16421],q 2 [4096,8216],q 2 [12292,8307],q 1 [8307,16393],q 8 [12292],q 0 [12292],q 6 [4096],q 2 [8192,163944],q 0 [8219,12297],q 1 [8219,12297],q 2 [4096,8219],q 2 [12288,167951],q 0 [8219,16393],q 0 [12297,20507],q 0 [16398,106961],q 0 [8198,17017],q 0 [8219],q 1 [8219],q 0 [8217,12313],q 0 [8216],q 1 [8216],q 0 [8217,16409],q 2 [12290,167948],q 0 [8219,16709],q 1 [8863,17057],q 7 [17057],q 2 [12294,8863],q 1 [8217,8192],q 0 [12313,16397],q 0 [12313,8205],q 8 [8196],q 0 [8196],q 2 [4,8196],q 1 [16469],q 2 [4096,8217],q 0 [8217,16506],q 0 [8217,16394],q 0 [16489],q 1 [8192,16489],q 7 [16393],q 1 [8219,16393],q 0 [8217,12410],q 1 [8219,16709],q 2 [12294,671],q 0 [8216,12333],q 1 [8216,12333],q 2 [4096,8216,12333],q 0 [16410],q 1 [16410],q 5 [16397],q 2 [8205],q 0 [8205,16397],q 0 [8217,16505],q 7 [16394],q 0 [12297,16394],q 1 [12298,24877],q 0 [12297,16405],q 2 [12292],q 0 [12298,12589],q 0 [12392,17077],q 2 [8196],q 2 [12298],q 2 [4096,167960],q 0 [12292,16497],q 0 [16393,167963],q 2 [4096,167963],q 1 [16393,167963],q 1 [16393,167936],q 2 [4096,167936],q 1 [8307,16737],q 1 [115],q 2 [12292,115],q 1 [8217,12298],q 0 [12298,16685],q 1 [12372,707],q 2 [8196,12372,707],q 2 [8192,12392],q 1 [8192,12392,17077],q 0 [12393,16885],q 0 [8273,16465],q 0 [12393,16397],q 0 [8273,16394],q 2 [12297,294912],q 2 [12288,8273],q 0 [8273,16894],q 2 [8192],q 11 [],q 0 [16489,16397],q 2 [8192,110607],q 0 [16489,110607],q 1 [17053],q 2 [12294],q 0 [12294,17053],q 0 [8207,82221],q 0 [16397,163851],q 2 [163851,571],q 2 [8192,163840],q 0 [16397],q 2 [8192,163848],q 0 [16390,8561],q 2 [8198,164475],q 0 [16398,8659],q 1 [16398,8657],q 0 [16398],q 18 [],q 1 [16393,167951],q 1 [12298,16393],q 1 [12298,16685],q 0 [8206],q 2 [8206,439],q 1 [8206,439],q 1 [12297,16406],q 1 [12297,16405],q 2 [12297,20480],q 1 [8205,16397],q 2 [12290],q 2 [12298,8495],q 0 [12298,8495],q 1 [8307],q 0 [8269],q 1 [16386,8269],q 2 [8269],q 0 [8273],q 1 [12288,8273],q 0 [12294],q 0 [12393],q 1 [8192,12393],q 0 [16394],q 0 [12394],q 0 [12298],q 0 [8217],q 1 [8217],q 0 [16490],q 0 [12314],q 0 [8198],q 1 [635],q 1 [16397,163848],q 2 [163848],q 0 [12296],q 1 [8563],q 2 [8563],q 0 [12392],q 1 [8192,12392],q 0 [8207],q 2 [8198],q 1 [12296,36866],q 2 [12296,36866],q 1 [8863],q 0 [12294,8863],q 0 [8718],q 0 [16909],q 1 [12290,16909],q 1 [12290],q 1 [12298,12589],q 2 [12298,12589],q 0 [16390],q 0 [8717],q 0 [16910],q 2 [12296,8231],q 0 [12296,8231],q 1 [12297,16394]]
def B_7_2 : BT (List (List Nat)) := BT.empty
lemma B_7_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_7 2 xs.toFinset) B_7_2 := .empty
def U_7_3 : List Nat := []
def P_7_3 : BT (Option BoundPool) := buildPoolsSubBT 9 W_7 r_7 S_7 ps_7 U_7_3
def N_7_3 : List NodeSpec := [([0,1,8,10],[],[]),([15,0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_7_3 : checkNodesBT W_7 g_7 F_7 P_7_3 A_7 B_7_2 3 N_7_3 = true := by decide +kernel
def B_7_3 : BT (List (List Nat)) := buildBucketsBT W_7 N_7_3
set_option maxRecDepth 500000 in
lemma B_7_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_7 3 xs.toFinset) B_7_3 :=
  buildBucketsBT_sound (by decide) gp_7 W_7_ok (buildPoolsSubBT_sound S_7_ok) A_7_ok B_7_2_ok C_7_3
def U_7_4 : List Nat := (r 0 7)
def P_7_4 : BT (Option BoundPool) := buildPoolsSubBT 9 W_7 r_7 S_7 ps_7 U_7_4
def N_7_4 : List NodeSpec := [([17,0,1,5,4],[],[]),([18,1,16,5,4],[0],[]),([19,1,16,5,4],[0],[]),([23,6,2,3,4],[],[]),([6,2,3,4,25],[1,2],[]),([6,2,3,27,29],[3,4],[]),([32,0,2,3,29],[],[]),([0,1,35,3,36],[],[1]),([37,0,1,2,34],[],[]),([38,0,1,5,4],[],[]),([0,1,5,4,39],[5],[]),([0,1,2,8,40],[],[]),([37,42,1,2,43],[],[]),([44,0,1,2,4],[],[]),([42,45,2,3,7],[],[]),([48,0,1,2,4],[],[]),([51,1,52,3,4],[],[]),([42,1,2,53,43],[],[]),([0,1,9,8,4],[5],[0]),([0,1,55,4,56],[5],[]),([0,1,9,5,58],[6],[]),([0,1,55,7,40],[],[]),([0,1,60,5,4],[],[]),([61,0,1,2,4],[],[]),([62,63,0,1,3],[],[1]),([0,1,5,7,10],[],[0]),([0,1,64,65,4],[5],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_7_4 : checkNodesBT W_7 g_7 F_7 P_7_4 A_7 B_7_3 4 N_7_4 = true := by decide +kernel
def B_7_4 : BT (List (List Nat)) := buildBucketsBT W_7 N_7_4
set_option maxRecDepth 500000 in
lemma B_7_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_7 4 xs.toFinset) B_7_4 :=
  buildBucketsBT_sound (by decide) gp_7 W_7_ok (buildPoolsSubBT_sound S_7_ok) A_7_ok B_7_3_ok C_7_4
def U_7_5 : List Nat := (r 0 6++r 7 54)
def P_7_5 : BT (Option BoundPool) := buildPoolsSubBT 9 W_7 r_7 S_7 ps_7 U_7_5
def N_7_5 : List NodeSpec := [([37,66,0,1,2,4],[],[]),([59,67,0,1,2,3],[7,8],[]),([59,0,1,9,5,4],[9,10],[0]),([19,1,2,16,3,4],[2,11],[0]),([68,69,0,1,3,4],[],[1]),([0,1,70,3,4,7],[8],[1]),([71,0,1,3,4,7],[],[]),([0,1,2,3,7,72],[12,13],[]),([37,0,1,2,3,7],[],[]),([42,1,2,3,7,41],[14],[0]),([0,1,64,3,4,31],[],[0,1]),([74,0,1,9,5,4],[5,9,15],[]),([0,1,2,3,76,7],[8],[]),e5 [77] [],([78,79,0,1,2,4],[],[]),([80,0,1,2,3,7],[2,7],[]),u5 [60] [],([6,0,1,5,4,10],[16,17,18],[0]),([6,18,1,9,5,4],[7,19,20],[0]),([0,1,2,3,27,29],[9,12,13,21],[0]),([62,0,1,2,3,34],[],[0]),([81,0,1,5,4,40],[9],[]),([0,1,2,5,7,40],[],[0]),([42,1,2,3,43,41],[],[0]),([0,1,2,82,7,40],[12,13,22,23],[]),([83,6,0,2,3,4],[2],[]),([32,0,1,3,5,4],[21],[]),([0,1,30,82,5,4],[12,13,24,25],[]),([19,67,6,1,2,3],[26,27],[]),([84,79,0,1,5,4],[9],[]),([37,33,0,1,2,4],[7],[0]),e5 [85] [13],e5 [86] [28],([19,6,1,9,5,4],[16,19,29],[0]),([87,0,1,2,4,40],[21,30],[]),([0,1,2,3,89,29],[9,13,21],[]),u5 [23] [],([90,0,1,2,4,7],[],[]),([91,0,1,5,4,10],[17],[]),e5 [74] [],([0,1,9,5,4,7],[7,9,31],[0]),([93,0,1,9,5,4],[32],[]),([94,0,1,2,27,40],[21],[]),([81,79,0,1,5,4],[9],[]),([6,18,95,2,3,4],[7,8,33,34],[]),([0,1,2,3,12,14],[9,12,13,35,36],[1]),([96,6,0,1,2,3],[37],[]),([75,0,1,3,7,41],[],[]),e5 [97] [7],([37,98,0,1,2,4],[],[]),e5 [32] [],e5 [99] [],([100,1,2,3,4,24],[],[]),([81,0,1,3,4,72],[12,13],[1]),([0,1,64,3,7,41],[],[1]),e5 [83] [],a5 [8] [1,2,7,9,13] [0,1],([81,0,1,101,3,4],[],[]),u5 [25] [1,2,8,13],e5 [102] [],e5 [103] [1,2],([81,0,1,3,7,41],[12,13,30],[]),e5 [104] [7],([0,1,2,5,4,105],[9],[]),([106,79,0,1,2,4],[],[]),([107,0,1,2,5,4],[9,21],[]),([0,1,108,3,43,41],[38],[]),([67,81,0,1,3,4],[],[]),([37,81,0,1,3,4],[],[]),e5 [110] [9],([0,1,2,3,5,58],[],[0]),u5 [39] [1,2,7,9],([0,1,2,3,111,7],[9,12,13],[]),([81,0,1,82,5,4],[9,12,13],[]),e5 [113] [],([115,0,1,3,4,40],[39],[]),([81,0,1,117,3,4],[],[]),([6,26,2,3,4,29],[3],[0,1]),([118,0,1,2,3,12],[],[1]),([90,6,0,1,2,4],[40],[]),([119,6,2,3,4,29],[41],[]),([6,22,2,3,4],[1,2,42],[0]),([32,20,1,2,3,4],[8],[2]),([37,6,20,1,2,4],[8],[]),([19,112,1,2,3,4],[],[]),([0,1,16,5,4],[0,5,43],[0,2]),u5 [17] [],([6,0,1,16,5,4],[0,9,43],[]),e5 [120] [2,44],([37,20,42,1,2,4],[2,7],[0]),([57,0,1,9,5,4],[5,9,16,45],[0]),([0,1,2,121,4,7],[9],[1]),([74,0,1,2,4,40],[30],[]),([0,1,2,3,7,10],[9,12,13,21],[0]),([94,122,0,1,2,4],[],[]),([84,74,0,1,3,4],[],[]),([112,0,1,3,4,41],[],[]),([0,1,35,2,3,34],[12,13,21,46,47,48],[0]),([75,32,0,1,3,4],[],[]),([6,0,2,3,24,40],[3,4,49,50],[1]),([6,42,45,2,3,4],[7,51,52],[0]),e5 [123] [],([37,124,0,1,2,4],[],[]),([0,1,2,125,27,40],[9,12,53,54],[]),e5 [126] [],([51,1,2,3,4,29],[7],[0]),u5 [38] [],([128,0,1,2,3,43],[2,7],[]),([129,0,1,2,4,40],[21,30],[]),([78,0,1,2,7,40],[21],[]),([88,0,1,3,29,41],[13,21,30],[]),e5 [130] [],([0,1,2,3,132,24],[8],[]),([37,0,1,2,43,41],[21],[0]),([0,1,108,3,4,133],[],[2,3]),([134,135,0,1,3,4],[],[1]),e5 [137] [],([139,1,2,3,4,41],[55],[]),([26,140,1,141,3,4],[8,56,57],[1]),([26,0,143,1,3,4],[7],[]),([67,93,0,1,2,3],[],[]),([144,0,1,5,4,10],[41],[]),([0,1,141,3,27,40],[58],[1]),([0,1,146,4],[25,41,59],[]),([84,0,1,2,3,34],[7,13],[]),([147,0,1,9,5,4],[60],[]),([0,1,2,3,12,40],[9,12,13,21,35,36],[1]),([42,0,1,3,148,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_7_5 : checkNodesBT W_7 g_7 F_7 P_7_5 A_7 B_7_4 5 N_7_5 = true := by decide +kernel
def B_7_5 : BT (List (List Nat)) := buildBucketsBT W_7 N_7_5
set_option maxRecDepth 500000 in
lemma B_7_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_7 5 xs.toFinset) B_7_5 :=
  buildBucketsBT_sound (by decide) gp_7 W_7_ok (buildPoolsSubBT_sound S_7_ok) A_7_ok B_7_4_ok C_7_5
def U_7_6 : List Nat := (r 1 5++r 7 7++r 16 4++[21,23,25,26,27]++r 29 5++[35,36,38,41,42]++r 48 5++[54,56]++r 61 182)
def P_7_6 : BT (Option BoundPool) := buildPoolsSubBT 9 W_7 r_7 S_7 ps_7 U_7_6
def N_7_6 : List NodeSpec := [e5 [149,41] [2,8,12,61,62],a5 [37,42] [8,12,21,63] [0,2],a5 [42,53] [7,8,12,21,26,61,64,65] [1],u5 [42,45] [1,12,13,51,66],e5 [151,40] [1,2,12,67,68],([75,0,1,152,4],[9,21,25,69],[0]),([75,42,0,1,3,4,41],[70],[0]),([0,1,2,153,4,40],[8,21,71],[1,3]),([0,1,141,5,4],[8,72,73],[]),([18,0,1,9,5,4],[7,16,19,26,41,74,75],[0,2]),([0,1,9,5,4,10],[9,16,17,18,25,26,41,76],[]),a5 [154,40] [8,9,77,78] [1],u5 [144,10] [12,41],u5 [91,10] [12,79],u5 [147,5] [1,2,12,80],([0,1,9,5,4],[5,7,25,26,81,82],[]),([19,67,0,1,2,3],[2,7,8,26,27,83,84],[0,2]),([19,0,1,9,5,4],[9,16,19,26,41,85],[0,2]),e5 [75,93] [9,12,32,86,87],u5 [93,5] [7,12,86,88],u5 [6,16] [9,11,89],e5 [6,155] [1,2,9,90],([6,18,1,2,3,5,4],[2,7,8,33,91],[0]),([19,6,1,9,2,3,4],(r 92 5),[0]),([84,6,20,1,2,3,4],[26,42,93,97,98,99],[]),u5 [59,9] [9,13],a5 [37,6] [1,2,7,8,12,13,63,100] [0,2],u5 [78,6] [8,12,13,101,102],e5 [6,112] [1,2,9,103],u5 [6,117] [1,7,12,13,21,26,104],([6,26,1,2,3,4,40],[25,49,77,93,105,106,107],[1,2,3]),a5 [26,156] [8,9,13,25,108,109] [3],a5 [78,7] [8,13,21,110] [0,1],a5 [81,82] [8,9,12,13,25] [0,1],u5 [68,7] [7,9],a5 [7,31] [7,9,111,112] [0,1],([0,1,2,3,7,41],[9,12,13,110,113,114],[0,1,2]),u5 [9,7] [7,8,9,21,110],([19,75,6,1,2,3,4],[12,29,49,94,96,115,116],[0]),([6,0,1,9,5,4],[7,9,16,19,25,74,117],[0,2]),a5 [108,43] [7,9,12,21,38,118,119] [0,3],e5 [10] [9,12,13,26,120,121],a5 [84,79] [9,21,49,122] [0,1],u5 [83] [2,7,12,13,123,124],u5 [6,73] [1,110,125],a5 [26,157] [7,8,9,12,126,127] [3],e5 [159,40] [7,8,12,72,86,128],([19,6,1,2,3,5,4],[12,27,33,84,94,96,115,129],[0]),u5 [22] [25,30,130,131,132],e5 [160] [7,8,12,13,133,134],u5 [6,101] [1,7,12,13,135],([161,0,1,3,4],[9,21,136,137,138],[]),([145,0,1,5,4],[9,25,26],[0]),([131,1,2,162,4],[12,21,25,129,139,140],[]),([75,6,0,1,30,3,4],[9,12,13,141],[]),e5 [163,24] [12,50],u5 [6,10] [12,13,79,95,142],a5 [12] [8,9,21,35,36,143] [0,1],([88,0,1,3,4,41],[7,9,21,30,132,144,145],[3]),([6,26,28,2,3,4],[1,2,93,105,106,146,147,148],[0,1,3]),a5 [164,40] [21,30,77,149] [3],([81,0,1,3,5,4],[9,21,150,151],[0,1]),a5 [81,7] [7,9,110,152] [0,1],e5 [153] [1,2,8,12,13,21],([37,20,0,1,2,4],[2,7,8,63,153],[0,1,2]),([81,6,0,1,3,4,41],[7,12,13,110,152,154],[0]),a5 [74] [1,7,9,13,30,155] [0,1],e5 [26,165] [21,156],e5 [131,166] [8,49,72,157],a5 [81,40] [8,9,12,13,21,152,158,159] [0,1],([37,20,0,1,2,4,41],[7,21,52,63,153],[0]),u5 [30,82] [7,8,12,13,25,72,160],u5 [18,95] [1,12,13,33,80],a5 [11,40] [8,9,12,13,21,30,143,161,162] [0,1],a5 [30,7] [7,12,13,72,110,163] [0,1],([131,0,1,2,53,4,41],[7,8,164],[]),u5 [6,111] [1,7,12,13,152,165],u5 [74,5] [7,9,13,21],e5 [74,6] [1,2,7,155],e5 [169] [2,7,9,12,166,167,168],([0,1,5,4,10],[9,17,18,26],[0,2]),([26,1,30,3,4],[7,12,49,169],[]),([6,0,1,2,82,4,40],[12,13,21,23,170],[0]),([6,0,1,2,82,5,4],[12,13,21,72,171],[0]),([19,6,21,2,3,4],[1,3,25,41,49,94,96,115,172,173,174],[]),a5 [64,7] [7,9,12,13,110,111,112] [0,1],([6,0,2,3,4,24],[3,4,13,49,50,174,175],[0,1]),u5 [80,6] [1,2,9,12,13,176,177],([84,6,0,1,30,3,4],[9,12,13,178],[]),a5 [27,170] [8,12,21,49,179,180] [1,3],([81,0,1,3,4,41],[9,30,152,154,181,182],[0,1]),u5 [106,6] [8,12,13,72,183],u5 [84,33] [9,13,48,49],u5 [57,5] [7,9,21,84],a5 [5,7] [7,8,9,21,110] [0,1],a5 [111] [8,9,21,165,184] [1],e5 [84,171] [9,49,185],a5 [75,7] [7,8,9,12,13,21,31,110,111,112] [0,1],([0,1,2,172,4],[8,9,186,187,188],[]),u5 [59,75] [7,9,10,12,13,189,190],u5 [119,29] [12,41],([6,0,1,2,5,4,40],[8,72,110,191,192,193],[0,1]),a5 [16] [11,13,25,30,72,89,93,148] [0,2],u5 [6,31] [1,25,194],([84,6,0,1,3,5,4],[9,25,49,195,196],[0]),a5 [112] [1,7,9,13,30,72,93,103,197] [0,2],a5 [6,72] [1,7,8,12,13,84,198] [0,1],a5 [88,29] [7,9,144,199] [0,3],u5 [6,5] [1,7,8,9,12,13,21,25,200],([0,1,2,3,174],[9,12,21,25,201],[]),u5 [131,24] [8,12,41,50,202],([81,6,0,1,3,5,4],[7,12,13,25,150],[0]),([75,6,0,1,3,4,41],[7,9,70,203],[0]),u5 [59,5] [7,8,9,13,21,110],a5 [175,41] [9,26,30,204] [0,1],([0,1,2,3,12],[9,35,36],[0,1]),a5 [26,29] [7,9,12,199,205] [0,1,3],a5 [32] [1,8,13,21,206,207,208] [0,2],e5 [83,28] [1,7,13,123],e5 [32,6] [1,2,7,206],([6,42,1,2,3,4,41],[2,7,51,209,210],[0]),e5 [32,41] [9,13,207],e5 [89] [7,21,132,211],u5 [124,41] [7,12,13,41,212,213],([75,0,1,30,3,4],[7,21,49,72,141,214],[]),u5 [6,76] [1,9,12,13,26,49,215],e5 [84,124] [9,12,49,147,213],([177,1,2,3,4],[9,12,21,216,217],[]),e5 [174] [9,12,25,201,218,219],a5 [26,170] [7,86,106,220] [3],a5 [127,43] [7,38,132,221] [0,1],([26,0,1,2,125,4,40],[9,12,21,54,222],[0]),([84,20,0,1,127,3,4],[9,21,223],[]),([178,1,2,3,4],[7,8,12,224],[]),u5 [128,20] [9,225,226],a5 [67,6] [1,2,7,12,13,26,83] [0,1,2],a5 [94,27] [8,9,21,227] [0,3],a5 [88,40] [9,21,77,191,228] [1],([88,0,28,1,3,4,41],[7,13,21,144,145,199],[0]),([0,1,2,3,27,40],[9,12,21,49,180,229],[0,1,2]),u5 [134,29] [7,9],([26,0,1,2,3,27,40],[9,12,41,49,229],[0,3]),u5 [94,26] [8,9,230,231],a5 [26,179] [9,13,25,26,232,233,234] [2],e5 [180] [25,26,30,235],e5 [181,40] [8,9,12,21,30,41,236,237],a5 [37,26] [8,9,63,115] [2],([6,0,1,2,3,7,41],[12,13,30,72,113],[0,1]),([26,140,1,2,3,4,40],[2,8,49,238],[0,1]),e5 [83,41] [9,13,124],a5 [81,79] [7,9,21] [0,1],([26,0,1,141,3,4,40],[7,8,56,239,240],[0]),e5 [131,182] [7,8,12,41,241],e5 [183,40] [13,242],u5 [93,9] [9,12,86]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_7_6 : checkNodesBT W_7 g_7 F_7 P_7_6 A_7 B_7_5 6 N_7_6 = true := by decide +kernel
def B_7_6 : BT (List (List Nat)) := buildBucketsBT W_7 N_7_6
set_option maxRecDepth 500000 in
lemma B_7_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_7 6 xs.toFinset) B_7_6 :=
  buildBucketsBT_sound (by decide) gp_7 W_7_ok (buildPoolsSubBT_sound S_7_ok) A_7_ok B_7_5_ok C_7_6
def U_7_7 : List Nat := ([1,2,5,7,8,9,12,13,16,19,21,25,26,27,30,33,34,38,41,49,51,52,54,56,63,64,70,72,74,77,79]++r 83 6++[91,92,93]++r 95 4++[100]++r 104 4++[110,111,112,115,116,117,128,132,142,143,144,147,152,158,159,161,168,176,179,180,189,193,196,198,199,200,202,203,209,212,213,215,218,225,227,233,239]++r 243 60)
def P_7_7 : BT (Option BoundPool) := buildPoolsSubBT 9 W_7 r_7 S_7 ps_7 U_7_7
def N_7_7 : List NodeSpec := [a5 [184] [2,12,21,26,30,72,243] [1],u5 [117] [7,12,13,21,26,104,244],e5 [185] [1,2,7,9,12,13,21,26,245,246],a5 [37,41] [7,9,21,26,30,51,52,63,247] [0,1,2,3],a5 [37] [1,2,7,8,9,12,13,30,63,100,247] [0,2],([84,0,1,2,3,41],[7,9,30,72,132],[]),e5 [42] [1,2,7,8,12,13,21,52,64,132,246],([84,75,0,1,3,4],[9,21,26,72,203],[0]),([75,0,1,3,4,41],[7,9,26,70,248],[0,1,2]),e5 [186] [1,2,8,9,12,13,72,203],u5 [76] [9,12,13,26,49,215,249],e5 [187] [1,2,7,12,13,41,132,246,250,251,252],a5 [67] [1,2,7,12,13,26,30,49,83,253] [0,2],a5 [72] [1,2,7,8,12,13,84,198,254] [0,2],([75,0,1,2,5,4],[2,5,9,26,34,72],[0]),u5 [18] [1,2,7,8,12,13,30,34,41,91,132,246,255],([0,1,2,5,4,40],[8,30,49,193,256],[0]),e5 [9,41] [7,9,26,51,52,72,95,132],e5 [9,5] [5,9,25,26,33,34,41],a5 [131,21] [8,13,25,41,132,202,246,257] [0,2],a5 [26,41] [7,9,26,41,51,52,72,115] [0,3],([0,1,9,2,5,4],[5,7,16,49,72,74],[]),a5 [26,28] [41,72,147,199,227] [0,1,3],([19,131,1,2,3,4],[2,12,21,26,49,246,257],[0]),([6,26,1,2,3,4],[2,7,12,25,72,93,105,106,107],[0,1,2]),u5 [9] [2,9,12,25,41,258,259],a5 [27] [8,9,13,21,49,179,180,227] [0,1,2,3],u5 [88] [1,2,7,9,12,21,30,132,144,260],a5 [84,20] [8,9,21,26,38,49,86,97,98,132] [0,1,2],a5 [136] [1,7,8,13,21,261,262,263] [2,3],a5 [88,28] [7,41,72,144,147,199] [0,3],e5 [127] [7,9,13,21,25,49,225,264,265],([131,20,1,2,3,4],[2,8,25,26],[]),a5 [19,167] [8,12,13,25,26,49,72,115,132,233,246,266] [2],a5 [19,5] [7,8,9,12,21,26,27,33,34,49,84,86,96,115] [0,2],a5 [26,125] [9,41,54,72,267,268] [0,1],a5 [84,6] [1,2,9,13,25,26,49,72,110,269] [0,1,2],e5 [75] [1,2,5,7,9,12,13,26,72],e5 [188] [1,8,9,13,26,270],a5 [81] [1,8,9,13,21,30,152,158,159] [0,1],a5 [75,41] [7,9,21,51,52,72,132,203] [1],a5 [75,6] [1,2,8,9,12,13,21,25,41,72,110,117,203,271] [0,2],a5 [11] [8,9,13,21,30,143,161] [0,1],a5 [30] [1,7,8,21,49,272,273] [0,2],a5 [19,21] [1,12,13,25,26,41,115,132,202,246] [0,2],e5 [189] [1,8,9,12,13,21,72,227,274],a5 [26,27] [9,41,49,72,179,180,227] [0,1,3],e5 [190] [7,8,9,13,26,275],a5 [159] [1,2,8,12,13,21,72,86,128,276,277] [0,1],a5 [141,40] [8,49,56,77,239,278,279] [0,1,2,3],a5 [7] [7,8,9,13,21,110,111,112] [0,1],a5 [81,6] [2,7,12,13,25,72,110,152,158] [0,1],a5 [6,7] [12,13,25,72,110,111,112] [0,1],([19,6,1,2,3,4],[12,25,26,30,49,72,96,110],[0,1]),a5 [6,9] [7,9,13,25,72,92,93,95,110,280] [0,2],e5 [26,5] [9,21,33,34,41,49,72],a5 [6,30] [12,13,25,72,176,272,273] [0,1],a5 [59] [7,8,9,13,21,110,189] [0,1],a5 [191] [1,8,21,30,132,281,282] [3],a5 [6,5] [7,8,9,12,13,21,25,33,34,41,72,84,110,132] [0,1,2],a5 [42,41] [7,26,51,52,64,209] [0,1,3],a5 [173] [1,9,12,13,21,25,30,218,283,284] [0,2],u5 [75,20] [2,7,8,21,25,26,97,285],u5 [124] [2,7,9,12,13,41,147,212,213],([0,1,9,5,4],[5,7,9,16,19,25,26,41,74],[0,2]),a5 [26,40] [8,9,12,21,41,49,77,86,106,227,239] [0,1,3],a5 [18,5] [7,9,26,33,34,84,91] [0,2],u5 [9,10] [9,25,26,41,49,79,142],a5 [6,41] [7,9,12,13,25,26,51,52,72,110,132] [0,1,2,3],a5 [131,158] [7,8,13,25,41,72,86,132,246,257,276,286] [0,3],e5 [192] [1,2,9,12,13,41,72,132,246,280,287,288],u5 [168] [2,9,12,25,132,168,289,290],e5 [193] [1,7,8,13,26,291],a5 [19,75] [7,9,12,26,41,49,85,86,96,115,116,271] [0,2],u5 [141] [2,7,8,12,30,72,132,279],a5 [132] [7,9,13,26,292,293] [2,3],a5 [131,41] [7,9,26,41,51,52,86,132,294] [0,3],u5 [5] [7,8,9,12,13,21,26,200,295,296],a5 [84,131] [8,9,26,49,86,98,132,269,294] [2],a5 [93] [2,7,8,9,12,13,21,87,88,297] [0,1],e5 [194] [1,13,41,49,298],a5 [19,9] [7,9,12,26,41,49,86,92,95,96,115] [0,2],e5 [195] [1,7,8,9,13,246,257,299],([75,0,1,9,3,4],[2,5,9,21,25,26,300,301],[0]),a5 [10] [9,12,13,21,26,49,79,95,142] [0,2],([84,0,1,3,5,4],[9,21,26,49,196,302],[0]),u5 [145] [1,2,9,12,13,21,25,95]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_7_7 : checkNodesBT W_7 g_7 F_7 P_7_7 A_7 B_7_6 7 N_7_7 = true := by decide +kernel
def B_7_7 : BT (List (List Nat)) := buildBucketsBT W_7 N_7_7
set_option maxRecDepth 500000 in
lemma B_7_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_7 7 xs.toFinset) B_7_7 :=
  buildBucketsBT_sound (by decide) gp_7 W_7_ok (buildPoolsSubBT_sound S_7_ok) A_7_ok B_7_6_ok C_7_7
def U_7_8 : List Nat := [1,2,5,7,8,9,12,13,25,26,30,33,34,41,49,51,52,72,84,92,95,96,98,106,110,115,116,132,227,257,269,271,280,294]
def P_7_8 : BT (Option BoundPool) := buildPoolsSubBT 9 W_7 r_7 S_7 ps_7 U_7_8
def N_7_8 : List NodeSpec := [a5 [84] [1,2,9,30,49,98,269] [0,1,2,3],a5 [41] [7,30,51,52] [0,1,2,3],a5 [5] [7,8,26,33,34,49,84] [0,1,2,3],a5 [75] [1,2,5,8,9,26,30,72,116,132,271] [0,1,2,3],a5 [19] [1,2,12,30,96,115] [0,1,2,3],a5 [131] [1,2,8,30,41,257,294] [0,2,3],a5 [26] [1,2,9,30,72,106,227] [0,1,2,3],a5 [9] [9,25,41,72,92,95,132,280] [0,1,2],a5 [6] [1,2,13,30,110] [0,1,2,3]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_7_8 : checkNodesBT W_7 g_7 F_7 P_7_8 A_7 B_7_7 8 N_7_8 = true := by decide +kernel
def B_7_8 : BT (List (List Nat)) := buildBucketsBT W_7 N_7_8
set_option maxRecDepth 500000 in
lemma B_7_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_7 8 xs.toFinset) B_7_8 :=
  buildBucketsBT_sound (by decide) gp_7 W_7_ok (buildPoolsSubBT_sound S_7_ok) A_7_ok B_7_7_ok C_7_8
def U_7_9 : List Nat := [1,2,30]
def P_7_9 : BT (Option BoundPool) := buildPoolsSubBT 9 W_7 r_7 S_7 ps_7 U_7_9
def N_7_9 : List NodeSpec := [a5 [] [1,2,30] [0,1,2,3]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_7_9 : checkNodesBT W_7 g_7 F_7 P_7_9 A_7 B_7_8 9 N_7_9 = true := by decide +kernel
def B_7_9 : BT (List (List Nat)) := buildBucketsBT W_7 N_7_9
set_option maxRecDepth 500000 in
lemma B_7_9_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_7 9 xs.toFinset) B_7_9 :=
  buildBucketsBT_sound (by decide) gp_7 W_7_ok (buildPoolsSubBT_sound S_7_ok) A_7_ok B_7_8_ok C_7_9
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_7_ok : forestRootCheck r_7 g_7 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11),(VAR 4,3,19)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_7_in : bucketContainsBT B_7_9 r_7 = true := by decide +kernel
lemma low_7 : Lower r_7 g_7 10 := lower_of_forestBT root_7_ok B_7_9_ok root_7_in
def g_8 := (d 0xfec0fec0fec0fec0)
def r_8 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_8 : Lower r_8 g_8 5 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,8,9)]) (by decide +kernel) hc
def g_9 := (d 0xfffef880fffef880)
def r_9 : List Nat := varsOf 31
def p_9 : List Nat := [7,7,7,11,11,11,12,12,13,13,14,14,17,17,18,18,19,20,20,21,22,24,24,25,26]
def q_9 : List Nat := [6,5,3,10,9,3,8,4,9,5,10,6,16,1,16,2,3,16,4,5,6,16,8,9,10]
def F_9 : Nat := fullMask 25
set_option maxHeartbeats 0 in
lemma gp_9 : goodPairs g_9 p_9 q_9 := goodPairs_of (by decide +kernel)
def W_9 : BT Decor := buildWiresBT 7 (mkBase p_9 q_9 r_9) [(1,0,2),(3,3,5),(1,1,3),(3,2,7),(0,0,1),(1,2,3),(2,10,4),(1,2,4),(3,3,12),(1,10,4),(3,1,14),(3,0,14),(0,10,4),(3,17,14),(0,1,10),(1,1,10),(3,19,20),(0,0,14),(0,1,4),(1,1,4),(3,23,24),(2,0,3),(1,26,2),(1,3,4),(3,2,28),(1,9,2),(1,30,4),(3,3,31),(3,2,4),(3,33,28),(3,10,4),(1,35,3),(1,26,4),(0,0,4),(1,38,3),(1,2,39),(2,0,2),(1,41,3),(1,41,4),(3,3,43),(2,27,4),(1,27,4),(1,0,4),(3,3,47),(1,48,2),(0,5,7),(1,38,2),(3,3,51),(2,1,2),(3,53,28),(3,23,0),(3,9,12),(2,0,10),(3,0,10),(2,30,4),(1,9,3),(1,30,3),(1,9,4),(3,3,62),(3,2,47),(3,0,4),(3,65,10),(2,1,3),(1,67,2),(0,0,10),(1,0,10),(3,23,10),(3,1,47),(3,9,10),(3,10,47),(2,30,3),(2,0,4),(3,1,4),(1,77,3),(0,10,47),(1,77,2),(1,80,3),(2,80,3),(2,0,17),(1,58,1),(1,1,17),(2,1,10),(3,86,0),(1,35,2),(3,3,4),(0,0,12),(2,0,28),(1,1,2),(1,0,1),(3,1,10)]
lemma W_9_ok : btAll (fun x => faithful p_9 q_9 x ∧ x.1 < 2^256) W_9 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_9 : List (List (Nat × Nat)) := [[],[(2,3)],[(0,1)],[(0,1),(2,3)]]
def A_9 : BT (List (Nat × Nat)) := btOfList 2 al_9
set_option maxHeartbeats 0 in
lemma A_9_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_9 = g_9) A_9 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_9_0 : Slice r_9 g_9 (identDom 0 1) 7 := by
  have hc : Lower (varsOf 29) (d 0xfffafaa0fffafaa0) 7 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_ident (u := 0) (v := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_9_1 : Slice r_9 g_9 (subcubeFast 4 0) 6 := by
  have hc : Lower (varsOf 27) (d 0xffee8800ffee8800) 6 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_9_2 : Slice r_9 g_9 (subcubeFast 8 0) 6 := by
  have hc : Lower (varsOf 23) (d 0xfefe8080fefe8080) 6 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_9_3 : Slice r_9 g_9 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) (d 0xfffcf000fffcf000) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_9_4 : Slice r_9 g_9 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) (d 0xfffffcc0fffffcc0) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_9_5 : Slice r_9 g_9 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) (d 0xfffaf000fffaf000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_9_6 : Slice r_9 g_9 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) (d 0xfffffaa0fffffaa0) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_9_7 : Slice r_9 g_9 (subcubeFast 16 0) 5 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_4
set_option maxHeartbeats 0 in
lemma sl_9_8 : Slice r_9 g_9 (subcubeFast 3 0) 4 := by
  have hc : Lower (varsOf 28) (d 0xfff0f000fff0f000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 3) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_9_9 : Slice r_9 g_9 (subcubeFast 16 1) 4 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_9_10 : Slice r_9 g_9 (subcubeFast 16 2) 4 := by
  have hc : Lower (varsOf 13) (d 0xfaa0faa0faa0faa0) 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 2) (by decide +kernel) hc
def S_9 : BT (Option (Nat × Nat)) := btOfList 4 [some (identDom 0 1,7),some (subcubeFast 4 0,6),some (subcubeFast 8 0,6),some (subcubeFast 1 0,5),some (subcubeFast 0 1,5),some (subcubeFast 2 0,5),some (subcubeFast 0 2,5),some (subcubeFast 16 0,5),some (subcubeFast 3 0,4),some (subcubeFast 16 1,4),some (subcubeFast 16 2,4)]
lemma S_9_ok : btAll (fun o => ∀ p, o = some p → Slice r_9 g_9 p.1 p.2) S_9 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_9_0) (forall_cons (fun _ h => by cases h; exact sl_9_1) (forall_cons (fun _ h => by cases h; exact sl_9_2) (forall_cons (fun _ h => by cases h; exact sl_9_3) (forall_cons (fun _ h => by cases h; exact sl_9_4) (forall_cons (fun _ h => by cases h; exact sl_9_5) (forall_cons (fun _ h => by cases h; exact sl_9_6) (forall_cons (fun _ h => by cases h; exact sl_9_7) (forall_cons (fun _ h => by cases h; exact sl_9_8) (forall_cons (fun _ h => by cases h; exact sl_9_9) (forall_cons (fun _ h => by cases h; exact sl_9_10) (fun _ h => (List.not_mem_nil h).elim))))))))))))
def ps_9 : BT (Option PoolSpec) := btOfList 7 [q 1 [16424,16425,57415],q 1 [40964,40965,81999],q 1 [16388,16389,98399],q 1 [],q 1 [49165,57344],q 2 [16393,57344],q 2 [],q 7 [],q 3 [],q 4 [],q 5 [],q 6 [],q 1 [16425,57351],q 1 [16425,57344],q 0 [],q 4 [12441],q 1 [16384,12441],q 1 [16426,16427],q 1 [16385,192527],q 2 [16384,8345],q 1 [16388,95],q 0 [12297,40963],q 0 [12297,40962],q 1 [40962,40963],q 8 [],q 9 [],q 10 [],q 2 [16388,16389,98399],q 0 [12294,8461],q 1 [40960,40961],q 1 [16388,41055],q 1 [16385,192519],q 0 [12297,40999],q 1 [16385,192555],q 1 [16386,16387],q 1 [16385,192552],q 1 [16384,12493],q 1 [16424,69634],q 0 [16421,16393],q 1 [40963,4329],q 4 [16397,16393],q 6 [16397,16393],q 2 [16393],q 1 [16424,69637],q 1 [40966,347],q 1 [16384,16385],q 1 [16424,16425],q 2 [8549],q 1 [49167],q 1 [16397],q 1 [16426],q 2 [16426],q 1 [16427],q 1 [16425],q 2 [16425],q 1 [16424],q 4 [16397],q 6 [16397],q 2 [16489],q 1 [12310],q 2 [8193],q 1 [12293],q 0 [8193],q 0 [12293],q 0 [12297],q 1 [16384],q 1 [4096],q 1 [16391],q 0 [16385,192519],q 2 [16385,192519],q 5 [8193],q 0 [12290],q 0 [16393],q 0 [8197],q 3 [8197],q 1 [4],q 0 [16421],q 1 [40961],q 1 [49165],q 1 [4097],q 0 [16385],q 2 [16385],q 0 [16384,12441],q 1 [16399],q 0 [12290,8297],q 1 [12290],q 2 [8297],q 2 [16388,95],q 0 [16384,8345],q 1 [16385],q 1 [16386],q 2 [16384,16385],q 1 [40962],q 2 [16386,16387],q 1 [40960],q 1 [40967],q 0 [16391],q 2 [16391],q 2 [16386],q 0 [16384],q 2 [16384],q 2 [4097],q 2 [4096]]
def B_9_2 : BT (List (List Nat)) := BT.empty
lemma B_9_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_9 2 xs.toFinset) B_9_2 := .empty
def U_9_3 : List Nat := []
def P_9_3 : BT (Option BoundPool) := buildPoolsSubBT 7 W_9 r_9 S_9 ps_9 U_9_3
def N_9_3 : List NodeSpec := [([6,8,9,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_9_3 : checkNodesBT W_9 g_9 F_9 P_9_3 A_9 B_9_2 3 N_9_3 = true := by decide +kernel
def B_9_3 : BT (List (List Nat)) := buildBucketsBT W_9 N_9_3
set_option maxRecDepth 500000 in
lemma B_9_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_9 3 xs.toFinset) B_9_3 :=
  buildBucketsBT_sound (by decide) gp_9 W_9_ok (buildPoolsSubBT_sound S_9_ok) A_9_ok B_9_2_ok C_9_3
def U_9_4 : List Nat := [0,1,2]
def P_9_4 : BT (Option BoundPool) := buildPoolsSubBT 7 W_9 r_9 S_9 ps_9 U_9_4
def N_9_4 : List NodeSpec := [([11,13,0,1,2],[],[]),([15,16,2,3,4],[],[]),([18,0,1,2,3],[0],[]),([21,0,2,3,4],[1],[]),([15,22,2,3,4],[],[]),([25,0,2,3,10],[2],[]),([13,0,1,27,4],[],[]),([6,8,0,1,4],[],[0]),([13,29,0,1,4],[],[]),([6,9,2,7,4],[],[0]),([13,22,1,2,4],[],[]),([32,0,1,2,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_9_4 : checkNodesBT W_9 g_9 F_9 P_9_4 A_9 B_9_3 4 N_9_4 = true := by decide +kernel
def B_9_4 : BT (List (List Nat)) := buildBucketsBT W_9 N_9_4
set_option maxRecDepth 500000 in
lemma B_9_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_9 4 xs.toFinset) B_9_4 :=
  buildBucketsBT_sound (by decide) gp_9 W_9_ok (buildPoolsSubBT_sound S_9_ok) A_9_ok B_9_3_ok C_9_4
def U_9_5 : List Nat := (r 2 45)
def P_9_5 : BT (Option BoundPool) := buildPoolsSubBT 7 W_9 r_9 S_9 ps_9 U_9_5
def N_9_5 : List NodeSpec := [([11,0,1,2,3,12],[3],[0]),([22,1,2,3,4,12],[4,5],[0]),([0,1,2,34,3,28],[6,7],[]),([13,0,1,2,4,28],[6],[0]),([13,0,1,2,12,28],[6,7],[]),([0,1,2,36,10,4],[3,7],[]),([0,1,2,3,37,28],[6,8],[]),e5 [14] (r 8 4),([13,0,1,2,10,4],[3],[0]),([15,0,2,3,10,4],[12],[]),([22,1,2,3,10,4],[13],[]),([11,0,1,2,3,14],[14],[0,1]),([6,9,1,2,3,4],[11],[0]),([0,1,2,39,40,4],[8,15,16],[]),([0,2,30,3,7,4],[6],[]),([0,1,2,42,10,4],[3,8],[]),e5 [44] [],([11,35,0,1,2,3],[17],[0]),e5 [45] [],e5 [46] [9],([26,13,0,1,2,4],[9],[0]),([0,1,2,42,4,28],[7],[1]),e5 [49] [18],e5 [50] [],([13,0,1,10,4,12],[3,6],[]),([6,0,1,2,7,4],[9,10],[0]),([0,1,2,39,10,4],[3,8,15],[]),([52,0,1,51,3,4],[19],[]),e5 [54] [3],([13,0,1,2,4,14],[14],[0,2]),([55,1,2,3,10,4],[20],[]),e5 [56] [],u5 [31] [6,14],([9,2,5,3,7,4],[9],[0,3]),([57,58,1,2,3,4],[21,22,23],[2]),e5 [59] [],([0,1,2,60,10,4],[3],[]),e5 [61] [],e5 [63] [],([26,64,1,2,3,4],[],[]),([25,0,2,3],([2]++r 24 4),[0]),e5 [66] [],([0,2,68,3,4,24],[28],[]),([69,1,2,3,70,4],[29],[2]),e5 [71] [3,30],([72,0,2,3,10,4],[31],[]),e5 [73] [14,32],([15,0,2,3,4,14],[10],[0]),e5 [74] [33],([22,1,2,3,4,14],[9,24],[0,1]),e5 [75] [],([76,65,1,2,3,10],[34],[2]),([0,1,2,60,4,28],[7,8,10],[]),([0,1,2,78,10,4],[3,11],[]),e5 [79] [9,35],e5 [81] [8,9,11],([0,1,2,17,10,28],[6],[]),e5 [82] [],e5 [40] [8,36],([83,1,2,3,10,4],[37],[]),([6,0,1,2,10,4],[3,9],[]),([0,1,2,3,62,12],[3,8,10,25,26,38],[]),([0,1,10,4,12,28],[3,7],[]),([0,84,2,3,10,4],[39],[]),([0,1,10,12,28],[3,6,7,40,41,42],[]),e5 [52] [19],([11,0,1,2,10,28],[6,7],[]),([0,2,3,10,85,4],[43],[]),([87,1,2,3,10,4],[44],[]),e5 [11] [],([38,1,2,3,10,47],[45],[2]),([0,1,2,3,17,14],[46],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_9_5 : checkNodesBT W_9 g_9 F_9 P_9_5 A_9 B_9_4 5 N_9_5 = true := by decide +kernel
def B_9_5 : BT (List (List Nat)) := buildBucketsBT W_9 N_9_5
set_option maxRecDepth 500000 in
lemma B_9_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_9 5 xs.toFinset) B_9_5 :=
  buildBucketsBT_sound (by decide) gp_9 W_9_ok (buildPoolsSubBT_sound S_9_ok) A_9_ok B_9_4_ok C_9_5
def U_9_6 : List Nat := ([3]++r 6 6++[16,18,19,20,24,25,26,31,34,42,45]++r 47 49)
def P_9_6 : BT (Option BoundPool) := buildPoolsSubBT 7 W_9 r_9 S_9 ps_9 U_9_6
def N_9_6 : List NodeSpec := [e5 [88] [25,26,47],a5 [13] ([3]++r 8 4++[42,48]) [0,2],a5 [12,28] [6,7,49] [0,1],([0,1,2,3,12,28],[25,26,42,49],[0,1]),e5 [90,12] [3,7,8,9,25],a5 [11,10] [3,6,7,50] [0,1],u5 [11] ([3,6]++r 8 4++[50,51]),a5 [35,10] [7,52] [0,1],a5 [14] (r 8 4++[53,54]) [0,1,2],a5 [17,10] [6,7,55] [0,1,2],u5 [91,28] [8,25],([0,1,2,10,4,28],[6,7,49,56,57],[0,1]),a5 [37] [3,8,10,11,25,58] [0,1],u5 [6] [6,7,9,10,11,25,59,60],a5 [5,7] ([9,11]++r 60 4) [0,3],a5 [38,10] [3,6,8,9,64,65] [0,1,2],a5 [9,10] ([3,6]++r 8 4++[64,66]) [0,1],a5 [80] [6,11,25,67] [0,1],([72,0,2,3,4],[9,11,25,31,68,69],[0]),([26,1,2,5,3,4],[3,6,8,9,25,70,71],[]),a5 [9,12] [3,7,8,10,25,26,72] [0,1],([9,0,2,92,3,4],[3,11,26,73,74,75],[1,2]),a5 [26,12] [3,6,8,25] [0,1,3],a5 [62] [3,6,8,10,25,26,76] [0,1],a5 [10,70] [8,9,77] [0,1],a5 [12,14] [25,26,42,78] [0,1,2],e5 [93,10] (r 8 4++[24,64,79]),([26,1,2,3,4,47],[7,8,9,71,80,81],[0,2]),([0,1,2,39,4],[7,8,16,24,82],[0,1]),([89,0,1,2,3,12],[3,7,25,26,42,83],[1]),a5 [27] [7,8,24,84,85,86] [0,1,2],a5 [30] [6,7,8,10,66] [0,1,2],([55,1,2,3,4],[7,8,10,20,87],[0]),a5 [51] [7,8,19,24,65,88] [0,1],u5 [13,12] [3,6,7,42,48],u5 [10,47] [8,9,64,89],u5 [76,10] [8,25,90],([38,1,2,3,47],[8,9,24,45,91],[0,2]),a5 [57,10] [8,9,64,92] [0,1,2],a5 [48] ([3,6]++r 8 4++[18,25,81]) [0,1],([76,65,1,2,3],[8,9,24,34,93],[0,2]),a5 [77,10] [3,6,10,11,67] [0,1,2],u5 [69,10] [8,9,94],a5 [10,14] [7,53] [0,1,2],a5 [94,10] [10,11,64,95] [2]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_9_6 : checkNodesBT W_9 g_9 F_9 P_9_6 A_9 B_9_5 6 N_9_6 = true := by decide +kernel
def B_9_6 : BT (List (List Nat)) := buildBucketsBT W_9 N_9_6
set_option maxRecDepth 500000 in
lemma B_9_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_9 6 xs.toFinset) B_9_6 :=
  buildBucketsBT_sound (by decide) gp_9 W_9_ok (buildPoolsSubBT_sound S_9_ok) A_9_ok B_9_5_ok C_9_6
def U_9_7 : List Nat := ([3]++r 6 6++[14,24,25,26,42,60]++r 64 4++[71,72,79,80,81,83,85,89,90]++r 96 7)
def P_9_7 : BT (Option BoundPool) := buildPoolsSubBT 7 W_9 r_9 S_9 ps_9 U_9_7
def N_9_7 : List NodeSpec := [u5 [89] ([3]++r 6 6++[25,26,83]),a5 [12] [3,8,10,25,26,42,72] [0,1,2,3],a5 [10] ([3]++r 6 6++[64]) [0,1,2],a5 [77] [3,6,9,10,11,14,25,67,96,97] [0,1,2],u5 [76] [8,10,14,24,25,90,98],a5 [38] ([3]++r 6 5++[14,24,65,99,100]) [0,1,2],u5 [26] [3,6,7,8,10,14,24,25,71,85],a5 [5] [3,8,9,11,14,24,25,60] [0,2],a5 [47] [7,8,9,14,24,25,26,80,81,89] [0,1],u5 [93] [9,11,14,24,25,79,101],a5 [9] [3,6,7,8,10,14,25,26,66,102] [0,1,2,3]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_9_7 : checkNodesBT W_9 g_9 F_9 P_9_7 A_9 B_9_6 7 N_9_7 = true := by decide +kernel
def B_9_7 : BT (List (List Nat)) := buildBucketsBT W_9 N_9_7
set_option maxRecDepth 500000 in
lemma B_9_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_9 7 xs.toFinset) B_9_7 :=
  buildBucketsBT_sound (by decide) gp_9 W_9_ok (buildPoolsSubBT_sound S_9_ok) A_9_ok B_9_6_ok C_9_7
def U_9_8 : List Nat := [3,6,14]
def P_9_8 : BT (Option BoundPool) := buildPoolsSubBT 7 W_9 r_9 S_9 ps_9 U_9_8
def N_9_8 : List NodeSpec := [a5 [] [3,6,14] [0,1,2,3]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_9_8 : checkNodesBT W_9 g_9 F_9 P_9_8 A_9 B_9_7 8 N_9_8 = true := by decide +kernel
def B_9_8 : BT (List (List Nat)) := buildBucketsBT W_9 N_9_8
set_option maxRecDepth 500000 in
lemma B_9_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_9 8 xs.toFinset) B_9_8 :=
  buildBucketsBT_sound (by decide) gp_9 W_9_ok (buildPoolsSubBT_sound S_9_ok) A_9_ok B_9_7_ok C_9_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_9_ok : forestRootCheck r_9 g_9 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11),(VAR 4,1,17)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_9_in : bucketContainsBT B_9_8 r_9 = true := by decide +kernel
lemma low_9 : Lower r_9 g_9 9 := lower_of_forestBT root_9_ok B_9_8_ok root_9_in
def g_10 := (d 0xfffefcc0fffefcc0)
def r_10 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_10 : Lower r_10 g_10 8 := by
  have hc : Lower (varsOf 30) (d 0xfffcfcc0fffcfcc0) 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,16,17)]) (by decide +kernel) hc
def g_11 := (d 0xfec0c000fec0c000)
def r_11 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_11 : Lower r_11 g_11 8 := by
  have hc : Lower (varsOf 30) (d 0xfcc0c000fcc0c000) 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_2
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,24,25)]) (by decide +kernel) hc
def g_12 := (d 0xfffee880fffee880)
def r_12 : List Nat := varsOf 31
def p_12 : List Nat := [7,7,7,11,11,11,13,13,13,14,14,14,17,17,18,18,19,20,20,21,22,24,24,25,26,28]
def q_12 : List Nat := [6,5,3,10,9,3,12,9,5,12,10,6,16,1,16,2,3,16,4,5,6,16,8,9,10,12]
def F_12 : Nat := fullMask 26
set_option maxHeartbeats 0 in
lemma gp_12 : goodPairs g_12 p_12 q_12 := goodPairs_of (by decide +kernel)
def W_12 : BT Decor := buildWiresBT 3 (mkBase p_12 q_12 r_12) [(1,0,1),(1,2,3),(0,5,6)]
lemma W_12_ok : btAll (fun x => faithful p_12 q_12 x ∧ x.1 < 2^256) W_12 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_12 : List (List (Nat × Nat)) := [[],[(1,2)],[(1,2),(2,3)],[(0,2),(1,2)],[(0,2),(1,2),(2,3)],[(0,2),(1,3)]]
def A_12 : BT (List (Nat × Nat)) := btOfList 3 al_12
set_option maxHeartbeats 0 in
lemma A_12_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_12 = g_12) A_12 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_12_0 : Slice r_12 g_12 (subcubeFast 16 0) 7 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_2
set_option maxHeartbeats 0 in
lemma sl_12_1 : Slice r_12 g_12 (subcubeFast 2 0) 6 := by
  have hc : Lower (varsOf 29) (d 0xfffaa000fffaa000) 6 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_2 : Slice r_12 g_12 (subcubeFast 4 0) 6 := by
  have hc : Lower (varsOf 27) (d 0xffee8800ffee8800) 6 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_3 : Slice r_12 g_12 (subcubeFast 8 0) 6 := by
  have hc : Lower (varsOf 23) (d 0xfefe8080fefe8080) 6 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_4 : Slice r_12 g_12 (subcubeFast 1 0) 6 := by
  have hc : Lower (varsOf 30) (d 0xfffcc000fffcc000) 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_5 : Slice r_12 g_12 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) (d 0xfffffcc0fffffcc0) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_6 : Slice r_12 g_12 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) (d 0xfffffaa0fffffaa0) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_7 : Slice r_12 g_12 (subcubeFast 0 4) 5 := by
  have hc : Lower (varsOf 27) (d 0xffffee88ffffee88) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_8 : Slice r_12 g_12 (subcubeFast 0 8) 5 := by
  have hc : Lower (varsOf 23) (d 0xffffe8e8ffffe8e8) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
def S_12 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 16 0,7),some (subcubeFast 2 0,6),some (subcubeFast 4 0,6),some (subcubeFast 8 0,6),some (subcubeFast 1 0,6),some (subcubeFast 0 1,5),some (subcubeFast 0 2,5),some (subcubeFast 0 4,5),some (subcubeFast 0 8,5)]
lemma S_12_ok : btAll (fun o => ∀ p, o = some p → Slice r_12 g_12 p.1 p.2) S_12 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_12_0) (forall_cons (fun _ h => by cases h; exact sl_12_1) (forall_cons (fun _ h => by cases h; exact sl_12_2) (forall_cons (fun _ h => by cases h; exact sl_12_3) (forall_cons (fun _ h => by cases h; exact sl_12_4) (forall_cons (fun _ h => by cases h; exact sl_12_5) (forall_cons (fun _ h => by cases h; exact sl_12_6) (forall_cons (fun _ h => by cases h; exact sl_12_7) (forall_cons (fun _ h => by cases h; exact sl_12_8) (fun _ h => (List.not_mem_nil h).elim))))))))))
def ps_12 : BT (Option PoolSpec) := btOfList 4 [q 1 [12297],q 4 [],q 5 [],q 6 [],q 2 [],q 7 [],q 3 [],q 8 [],q 2 [4097],q 1 [],q 0 [4097],q 3 [4097],q 0 []]
def B_12_4 : BT (List (List Nat)) := BT.empty
lemma B_12_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 4 xs.toFinset) B_12_4 := .empty
def U_12_5 : List Nat := []
def P_12_5 : BT (Option BoundPool) := buildPoolsSubBT 4 W_12 r_12 S_12 ps_12 U_12_5
def N_12_5 : List NodeSpec := [e5 [7] []]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_5 : checkNodesBT W_12 g_12 F_12 P_12_5 A_12 B_12_4 5 N_12_5 = true := by decide +kernel
def B_12_5 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_5
set_option maxRecDepth 500000 in
lemma B_12_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 5 xs.toFinset) B_12_5 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_4_ok C_12_5
def U_12_6 : List Nat := (r 0 9)
def P_12_6 : BT (Option BoundPool) := buildPoolsSubBT 4 W_12 r_12 S_12 ps_12 U_12_6
def N_12_6 : List NodeSpec := [u5 [5,6] (r 0 9)]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_6 : checkNodesBT W_12 g_12 F_12 P_12_6 A_12 B_12_5 6 N_12_6 = true := by decide +kernel
def B_12_6 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_6
set_option maxRecDepth 500000 in
lemma B_12_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 6 xs.toFinset) B_12_6 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_5_ok C_12_6
def U_12_7 : List Nat := ([1,2]++r 4 8)
def P_12_7 : BT (Option BoundPool) := buildPoolsSubBT 4 W_12 r_12 S_12 ps_12 U_12_7
def N_12_7 : List NodeSpec := [u5 [5] ([1,2]++r 4 8)]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_7 : checkNodesBT W_12 g_12 F_12 P_12_7 A_12 B_12_6 7 N_12_7 = true := by decide +kernel
def B_12_7 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_7
set_option maxRecDepth 500000 in
lemma B_12_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 7 xs.toFinset) B_12_7 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_6_ok C_12_7
def U_12_8 : List Nat := [1,4,6,9,12]
def P_12_8 : BT (Option BoundPool) := buildPoolsSubBT 4 W_12 r_12 S_12 ps_12 U_12_8
def N_12_8 : List NodeSpec := [a5 [] [1,4,6,9,12] [0,1,2,3,4,5]]
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
def g_13 := (d 0xfffce880fffce880)
def r_13 : List Nat := varsOf 31
def p_13 : List Nat := [7,7,7,11,11,11,13,13,13,14,14,14,18,18,19,19,20,20,21,21,22,24,24,25,25,26,28]
def q_13 : List Nat := [6,5,3,10,9,3,12,9,5,12,10,6,16,2,17,3,16,4,17,5,6,16,8,17,9,10,12]
def F_13 : Nat := fullMask 27
set_option maxHeartbeats 0 in
lemma gp_13 : goodPairs g_13 p_13 q_13 := goodPairs_of (by decide +kernel)
def W_13 : BT Decor := buildWiresBT 3 (mkBase p_13 q_13 r_13) [(0,1,2),(1,1,2),(2,1,3)]
lemma W_13_ok : btAll (fun x => faithful p_13 q_13 x ∧ x.1 < 2^256) W_13 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_13 : List (List (Nat × Nat)) := [[],[(2,3)],[(1,2)],[(1,3),(2,3)],[(1,2),(2,3)],[(1,3)]]
def A_13 : BT (List (Nat × Nat)) := btOfList 3 al_13
set_option maxHeartbeats 0 in
lemma A_13_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_13 = g_13) A_13 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_13_0 : Slice r_13 g_13 (subcubeFast 0 1) 7 := by
  have hc : Lower (varsOf 30) (d 0xfffcfcc0fffcfcc0) 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_1 : Slice r_13 g_13 (subcubeFast 16 0) 7 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_2
set_option maxHeartbeats 0 in
lemma sl_13_2 : Slice r_13 g_13 (subcubeFast 1 0) 6 := by
  have hc : Lower (varsOf 30) (d 0xfffcc000fffcc000) 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_3 : Slice r_13 g_13 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) (d 0xfff0a000fff0a000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_4 : Slice r_13 g_13 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) (d 0xfffffaa0fffffaa0) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_5 : Slice r_13 g_13 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) (d 0xffcc8800ffcc8800) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_6 : Slice r_13 g_13 (subcubeFast 0 4) 5 := by
  have hc : Lower (varsOf 27) (d 0xffffee88ffffee88) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_7 : Slice r_13 g_13 (subcubeFast 8 0) 5 := by
  have hc : Lower (varsOf 23) (d 0xfcfc8080fcfc8080) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_8 : Slice r_13 g_13 (subcubeFast 0 8) 5 := by
  have hc : Lower (varsOf 23) (d 0xffffe8e8ffffe8e8) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_9 : Slice r_13 g_13 (identDom 1 2) 5 := by
  have hc : Lower (varsOf 27) (d 0xffcccc88ffcccc88) 5 := carry_of (swaps := [(1,3),(2,4)]) (by decide +kernel) low_8
  exact slice_ident (u := 1) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_10 : Slice r_13 g_13 (identDom 1 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xfcfcc8c8fcfcc8c8) 5 := carry_of (swaps := [(1,3),(2,3),(3,4)]) (by decide +kernel) low_8
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
def S_13 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 0 1,7),some (subcubeFast 16 0,7),some (subcubeFast 1 0,6),some (subcubeFast 2 0,5),some (subcubeFast 0 2,5),some (subcubeFast 4 0,5),some (subcubeFast 0 4,5),some (subcubeFast 8 0,5),some (subcubeFast 0 8,5),some (identDom 1 2,5),some (identDom 1 3,5)]
lemma S_13_ok : btAll (fun o => ∀ p, o = some p → Slice r_13 g_13 p.1 p.2) S_13 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_13_0) (forall_cons (fun _ h => by cases h; exact sl_13_1) (forall_cons (fun _ h => by cases h; exact sl_13_2) (forall_cons (fun _ h => by cases h; exact sl_13_3) (forall_cons (fun _ h => by cases h; exact sl_13_4) (forall_cons (fun _ h => by cases h; exact sl_13_5) (forall_cons (fun _ h => by cases h; exact sl_13_6) (forall_cons (fun _ h => by cases h; exact sl_13_7) (forall_cons (fun _ h => by cases h; exact sl_13_8) (forall_cons (fun _ h => by cases h; exact sl_13_9) (forall_cons (fun _ h => by cases h; exact sl_13_10) (fun _ h => (List.not_mem_nil h).elim))))))))))))
def ps_13 : BT (Option PoolSpec) := btOfList 5 [q 0 [8196,8197],q 4 [],q 1 [8196,8197],q 9 [],q 3 [],q 0 [12294],q 6 [],q 5 [],q 1 [12294],q 10 [],q 7 [],q 8 [],q 0 [8197],q 2 [],q 1 [8197],q 0 [8196],q 1 [8196],q 0 [],q 1 []]
def B_13_5 : BT (List (List Nat)) := BT.empty
lemma B_13_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_13 5 xs.toFinset) B_13_5 := .empty
def U_13_6 : List Nat := (r 0 5)
def P_13_6 : BT (Option BoundPool) := buildPoolsSubBT 5 W_13 r_13 S_13 ps_13 U_13_6
def N_13_6 : List NodeSpec := [([0,5,6,3,4],(r 0 5),[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_13_6 : checkNodesBT W_13 g_13 F_13 P_13_6 A_13 B_13_5 6 N_13_6 = true := by decide +kernel
def B_13_6 : BT (List (List Nat)) := buildBucketsBT W_13 N_13_6
set_option maxRecDepth 500000 in
lemma B_13_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_13 6 xs.toFinset) B_13_6 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok (buildPoolsSubBT_sound S_13_ok) A_13_ok B_13_5_ok C_13_6
def U_13_7 : List Nat := ([1]++r 4 13)
def P_13_7 : BT (Option BoundPool) := buildPoolsSubBT 5 W_13 r_13 S_13 ps_13 U_13_7
def N_13_7 : List NodeSpec := [e5 [7] ([1]++r 4 8),u5 [6] ([1,4,6,7]++r 10 5),u5 [5] [1,4,7,10,11,15,16]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_13_7 : checkNodesBT W_13 g_13 F_13 P_13_7 A_13 B_13_6 7 N_13_7 = true := by decide +kernel
def B_13_7 : BT (List (List Nat)) := buildBucketsBT W_13 N_13_7
set_option maxRecDepth 500000 in
lemma B_13_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_13 7 xs.toFinset) B_13_7 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok (buildPoolsSubBT_sound S_13_ok) A_13_ok B_13_6_ok C_13_7
def U_13_8 : List Nat := [17,18]
def P_13_8 : BT (Option BoundPool) := buildPoolsSubBT 5 W_13 r_13 S_13 ps_13 U_13_8
def N_13_8 : List NodeSpec := [a5 [] [17,18] [0,1,2,3,4,5]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_13_8 : checkNodesBT W_13 g_13 F_13 P_13_8 A_13 B_13_7 8 N_13_8 = true := by decide +kernel
def B_13_8 : BT (List (List Nat)) := buildBucketsBT W_13 N_13_8
set_option maxRecDepth 500000 in
lemma B_13_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_13 8 xs.toFinset) B_13_8 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok (buildPoolsSubBT_sound S_13_ok) A_13_ok B_13_7_ok C_13_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_13_ok : forestRootCheck r_13 g_13 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11),(VAR 4,2,18)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_13_in : bucketContainsBT B_13_8 r_13 = true := by decide +kernel
lemma low_13 : Lower r_13 g_13 9 := lower_of_forestBT root_13_ok B_13_8_ok root_13_in
def g_14 := (d 0xe800e800e800e800)
def r_14 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_14 : Lower r_14 g_14 5 := by
  exact lift_of_f (z := 0) (o := 8) (other := r_0) (G := g_0) (essPairs := [(VAR 3,3,11)]) (by decide +kernel) low_0
def g_15 := (d 0xffe8c000ffe8c000)
def r_15 : List Nat := varsOf 31
def p_15 : List Nat := [14,14,14,15,15,15,19,19,19,21,21,21,22,22,22,23,24,24,25,25,26,26,27,28,28,29]
def q_15 : List Nat := [12,10,6,13,11,7,18,17,3,20,17,5,20,18,6,7,16,8,17,9,18,10,11,20,12,13]
def F_15 : Nat := fullMask 26
set_option maxHeartbeats 0 in
lemma gp_15 : goodPairs g_15 p_15 q_15 := goodPairs_of (by decide +kernel)
def W_15 : BT Decor := buildWiresBT 5 (mkBase p_15 q_15 r_15) [(0,2,4),(3,5,1),(2,2,3),(3,7,1),(0,1,2),(0,1,4),(2,1,3),(0,9,4),(3,9,4),(1,9,3),(0,0,4),(2,0,3)]
lemma W_15_ok : btAll (fun x => faithful p_15 q_15 x ∧ x.1 < 2^256) W_15 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_15 : List (List (Nat × Nat)) := [[],[(1,2)]]
def A_15 : BT (List (Nat × Nat)) := btOfList 1 al_15
set_option maxHeartbeats 0 in
lemma A_15_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_15 = g_15) A_15 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_15_0 : Slice r_15 g_15 (subcubeFast 0 1) 6 := by
  have hc : Lower (varsOf 30) (d 0xfffcc000fffcc000) 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_15_1 : Slice r_15 g_15 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) (d 0xffc0c000ffc0c000) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_15_2 : Slice r_15 g_15 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) (d 0xfffaf000fffaf000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_15_3 : Slice r_15 g_15 (subcubeFast 0 4) 5 := by
  have hc : Lower (varsOf 27) (d 0xffeecc00ffeecc00) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_15_4 : Slice r_15 g_15 (subcubeFast 8 0) 5 := by
  have hc : Lower (varsOf 23) (d 0xe8e80000e8e80000) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_14
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_15_5 : Slice r_15 g_15 (subcubeFast 0 16) 5 := by
  exact slice_fast_direct_f (z := 0) (o := 16) (by decide +kernel) low_5
set_option maxHeartbeats 0 in
lemma sl_15_6 : Slice r_15 g_15 (subcubeFast 8 16) 4 := by
  exact slice_fast_direct_f (z := 8) (o := 16) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_15_7 : Slice r_15 g_15 (subcubeFast 1 4) 4 := by
  have hc : Lower (varsOf 26) (d 0xffcccc00ffcccc00) 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_15_8 : Slice r_15 g_15 (identDom 2 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xf8f8c0c0f8f8c0c0) 5 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_3
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
def S_15 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 0 1,6),some (subcubeFast 1 0,5),some (subcubeFast 0 2,5),some (subcubeFast 0 4,5),some (subcubeFast 8 0,5),some (subcubeFast 0 16,5),some (subcubeFast 8 16,4),some (subcubeFast 1 4,4),some (identDom 2 3,5)]
lemma S_15_ok : btAll (fun o => ∀ p, o = some p → Slice r_15 g_15 p.1 p.2) S_15 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_15_0) (forall_cons (fun _ h => by cases h; exact sl_15_1) (forall_cons (fun _ h => by cases h; exact sl_15_2) (forall_cons (fun _ h => by cases h; exact sl_15_3) (forall_cons (fun _ h => by cases h; exact sl_15_4) (forall_cons (fun _ h => by cases h; exact sl_15_5) (forall_cons (fun _ h => by cases h; exact sl_15_6) (forall_cons (fun _ h => by cases h; exact sl_15_7) (forall_cons (fun _ h => by cases h; exact sl_15_8) (fun _ h => (List.not_mem_nil h).elim))))))))))
def ps_15 : BT (Option PoolSpec) := btOfList 4 [q 3 [],q 5 [],q 4 [],q 0 [],q 1 [],q 8 [],q 0 [16388],q 6 [],q 2 [],q 0 [12294],q 0 [8196],q 7 []]
def B_15_4 : BT (List (List Nat)) := BT.empty
lemma B_15_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_15 4 xs.toFinset) B_15_4 := .empty
def U_15_5 : List Nat := (r 0 6)
def P_15_5 : BT (Option BoundPool) := buildPoolsSubBT 4 W_15 r_15 S_15 ps_15 U_15_5
def N_15_5 : List NodeSpec := [e5 [6] [],e5 [8] [],([0,9,10,2,3,4],[0,1],[]),([11,0,9,2,3,4],[0,2],[]),e5 [12] (r 2 4),e5 [13] [3,4],e5 [14] [3,4]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_15_5 : checkNodesBT W_15 g_15 F_15 P_15_5 A_15 B_15_4 5 N_15_5 = true := by decide +kernel
def B_15_5 : BT (List (List Nat)) := buildBucketsBT W_15 N_15_5
set_option maxRecDepth 500000 in
lemma B_15_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_15 5 xs.toFinset) B_15_5 :=
  buildBucketsBT_sound (by decide) gp_15 W_15_ok (buildPoolsSubBT_sound S_15_ok) A_15_ok B_15_4_ok C_15_5
def U_15_6 : List Nat := (r 0 12)
def P_15_6 : BT (Option BoundPool) := buildPoolsSubBT 4 W_15 r_15 S_15 ps_15 U_15_6
def N_15_6 : List NodeSpec := [a5 [10] [0,6,7,8] [0,1],a5 [11] [0,2,5,7,8,9] [0,1],a5 [9] [1,2,4,5,8,10,11] [0,1],([15,1,2,3,4],[4,7,11],[]),([16,1,2,3,4],[3,4,7,11],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_15_6 : checkNodesBT W_15 g_15 F_15 P_15_6 A_15 B_15_5 6 N_15_6 = true := by decide +kernel
def B_15_6 : BT (List (List Nat)) := buildBucketsBT W_15 N_15_6
set_option maxRecDepth 500000 in
lemma B_15_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_15 6 xs.toFinset) B_15_6 :=
  buildBucketsBT_sound (by decide) gp_15 W_15_ok (buildPoolsSubBT_sound S_15_ok) A_15_ok B_15_5_ok C_15_6
def U_15_7 : List Nat := (r 0 4++[7,8])
def P_15_7 : BT (Option BoundPool) := buildPoolsSubBT 4 W_15 r_15 S_15 ps_15 U_15_7
def N_15_7 : List NodeSpec := [a5 [] (r 0 4++[7,8]) [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_15_7 : checkNodesBT W_15 g_15 F_15 P_15_7 A_15 B_15_6 7 N_15_7 = true := by decide +kernel
def B_15_7 : BT (List (List Nat)) := buildBucketsBT W_15 N_15_7
set_option maxRecDepth 500000 in
lemma B_15_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_15 7 xs.toFinset) B_15_7 :=
  buildBucketsBT_sound (by decide) gp_15 W_15_ok (buildPoolsSubBT_sound S_15_ok) A_15_ok B_15_6_ok C_15_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_15_ok : forestRootCheck r_15 g_15 [(VAR 0,18,19),(VAR 1,12,14),(VAR 2,10,14),(VAR 3,6,14),(VAR 4,3,19)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_15_in : bucketContainsBT B_15_7 r_15 = true := by decide +kernel
lemma low_15 : Lower r_15 g_15 8 := lower_of_forestBT root_15_ok B_15_7_ok root_15_in
def g_16 := (d 0xfff8e000fff8e000)
def r_16 : List Nat := varsOf 31
def p_16 : List Nat := [13,13,13,14,14,14,15,15,19,19,19,20,20,21,21,22,22,23,24,24,25,25,26,26,27,28]
def q_16 : List Nat := [12,9,5,12,10,6,11,7,18,17,3,16,4,17,5,18,6,7,16,8,17,9,18,10,11,12]
def F_16 : Nat := fullMask 26
set_option maxHeartbeats 0 in
lemma gp_16 : goodPairs g_16 p_16 q_16 := goodPairs_of (by decide +kernel)
def W_16 : BT Decor := buildWiresBT 6 (mkBase p_16 q_16 r_16) [(1,2,3),(1,5,4),(3,3,6),(0,2,4),(1,2,4),(3,8,9),(0,3,4),(1,3,4),(3,11,12),(0,2,12),(1,1,11),(1,1,8),(1,8,3),(0,0,12),(0,13,0),(2,0,11),(0,2,3),(0,21,4),(3,22,2),(1,2,11),(2,13,1),(0,0,9),(0,3,9),(3,1,12),(0,13,2),(2,10,3),(3,3,4),(2,2,4),(3,1,9),(3,0,9),(2,1,11),(1,21,4),(2,3,4),(3,37,5),(0,5,4),(1,31,21),(3,2,4),(1,0,8),(0,1,9),(1,31,2),(3,37,2),(2,5,4),(3,5,4),(3,21,4),(2,21,4)]
lemma W_16_ok : btAll (fun x => faithful p_16 q_16 x ∧ x.1 < 2^256) W_16 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_16 : List (List (Nat × Nat)) := [[],[(2,3)],[(0,1)],[(0,1),(2,3)]]
def A_16 : BT (List (Nat × Nat)) := btOfList 2 al_16
set_option maxHeartbeats 0 in
lemma A_16_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_16 = g_16) A_16 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_16_0 : Slice r_16 g_16 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) (d 0xfffcf000fffcf000) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_1 : Slice r_16 g_16 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) (d 0xfff0c000fff0c000) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_2 : Slice r_16 g_16 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) (d 0xfffaf000fffaf000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_3 : Slice r_16 g_16 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) (d 0xfff0a000fff0a000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_4 : Slice r_16 g_16 (subcubeFast 1 2) 4 := by
  have hc : Lower (varsOf 28) (d 0xfff0f000fff0f000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_5 : Slice r_16 g_16 (identDom 2 3) 6 := by
  have hc : Lower (varsOf 23) (d 0xf8f8e0e0f8f8e0e0) 6 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_6
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
def S_16 : BT (Option (Nat × Nat)) := btOfList 3 [some (subcubeFast 0 1,5),some (subcubeFast 1 0,5),some (subcubeFast 0 2,5),some (subcubeFast 2 0,5),some (subcubeFast 1 2,4),some (identDom 2 3,6)]
lemma S_16_ok : btAll (fun o => ∀ p, o = some p → Slice r_16 g_16 p.1 p.2) S_16 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_16_0) (forall_cons (fun _ h => by cases h; exact sl_16_1) (forall_cons (fun _ h => by cases h; exact sl_16_2) (forall_cons (fun _ h => by cases h; exact sl_16_3) (forall_cons (fun _ h => by cases h; exact sl_16_4) (forall_cons (fun _ h => by cases h; exact sl_16_5) (fun _ h => (List.not_mem_nil h).elim)))))))
def ps_16 : BT (Option PoolSpec) := btOfList 4 [q 1 [],q 0 [],q 3 [],q 2 [],q 5 [16399,8317],q 5 [],q 5 [16398,8343],q 4 [],q 5 [16404],q 5 [16407],q 5 [16393],q 5 [16392],q 5 [16394],q 5 [16399],q 5 [16470],q 5 [16469]]
def B_16_2 : BT (List (List Nat)) := BT.empty
lemma B_16_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_16 2 xs.toFinset) B_16_2 := .empty
def U_16_3 : List Nat := []
def P_16_3 : BT (Option BoundPool) := buildPoolsSubBT 4 W_16 r_16 S_16 ps_16 U_16_3
def N_16_3 : List NodeSpec := [([7,10,0,1],[],[]),([13,0,1,14],[],[]),([13,0,2,15],[],[]),([0,16,17,9],[],[]),([13,18,1,2],[],[]),([19,13,1,2],[],[]),([13,0,1,2],[],[]),([20,13,1,2],[],[]),([23,13,0,1],[],[]),([13,0,1,24],[],[]),([25,13,0,2],[],[]),([26,1,8,27],[],[]),([13,28,0,2],[],[]),([29,13,0,1],[],[]),([30,10,0,1],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_16_3 : checkNodesBT W_16 g_16 F_16 P_16_3 A_16 B_16_2 3 N_16_3 = true := by decide +kernel
def B_16_3 : BT (List (List Nat)) := buildBucketsBT W_16 N_16_3
set_option maxRecDepth 500000 in
lemma B_16_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_16 3 xs.toFinset) B_16_3 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok (buildPoolsSubBT_sound S_16_ok) A_16_ok B_16_2_ok C_16_3
def U_16_4 : List Nat := []
def P_16_4 : BT (Option BoundPool) := buildPoolsSubBT 4 W_16 r_16 S_16 ps_16 U_16_4
def N_16_4 : List NodeSpec := [([31,13,0,1,2],[],[]),([32,10,0,1,3],[],[]),([31,0,1,14,4],[],[]),([7,33,0,2,4],[],[]),([33,34,2,3,4],[],[]),([7,26,1,2,4],[],[]),([26,1,2,27,4],[],[0]),([20,35,2,3,4],[],[]),([0,1,8,3,36],[],[]),([20,23,1,3,4],[],[]),([13,0,1,2],[],[0,1,2]),([13,0,1,2,3],[],[]),([7,0,1,2,4],[],[]),([0,1,2,38,4],[],[]),([0,1,2,39,12],[],[]),([0,1,8,17,9],[],[0,1,2]),([0,1,8,3,9],[],[1]),([13,0,1,2,4],[],[]),([0,1,2,40,4],[],[]),([7,0,1,8,9],[],[0]),([20,1,3,24,4],[],[]),([23,0,3,15,4],[],[]),([32,41,0,1,3],[],[1]),([20,1,2,11,12],[],[0]),([33,0,8,3,9],[],[1]),([32,0,1,17,4],[],[]),([33,0,2,27,4],[],[]),([23,0,1,11,12],[],[0]),([0,2,16,17,4],[],[0]),([2,42,16,3,4],[],[]),([23,0,1,3,4],[],[]),([26,1,8,3,9],[],[0,1]),([13,0,1,2,11],[],[0,2]),([0,8,16,3,9],[],[0,1]),([13,0,1,2,12],[],[0,1,2]),([0,1,8,27,9],[],[0,1,2]),([26,43,2,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_16_4 : checkNodesBT W_16 g_16 F_16 P_16_4 A_16 B_16_3 4 N_16_4 = true := by decide +kernel
def B_16_4 : BT (List (List Nat)) := buildBucketsBT W_16 N_16_4
set_option maxRecDepth 500000 in
lemma B_16_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_16 4 xs.toFinset) B_16_4 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok (buildPoolsSubBT_sound S_16_ok) A_16_ok B_16_3_ok C_16_4
def U_16_5 : List Nat := (r 0 16)
def P_16_5 : BT (Option BoundPool) := buildPoolsSubBT 4 W_16 r_16 S_16 ps_16 U_16_5
def N_16_5 : List NodeSpec := [([32,41,0,1,2,3],[],[1]),u5 [44] (r 0 5),([32,41,0,1,3],[],[0,1]),u5 [9] (r 0 4++[5]),([32,41,0,1,3,4],[],[1]),a5 [45] (r 0 4++[6]) [1],([7,0,1,2,4],[],[]),([0,1,14,3,4,12],[],[0,1,3]),e5 [46] [],([23,0,1,11,3,4],[5],[0,2]),([33,0,2,3,4,9],[2,7],[0]),a5 [6] (r 0 4) [0,1],a5 [39] (r 0 4++[8]) [0,1],e5 [47] [9],e5 [48] [],([0,1,8,3,4,9],[10,11],[1]),([32,0,1,3,5,4],[12],[1]),e5 [7] [],([0,8,2,16,3,4],[2,7],[0,1]),([0,1,21,8,3,4],[5],[0]),([31,0,1,21,2,4],[13],[0]),a5 [8] (r 0 4++[5]) [0,1],([20,1,2,11,3,4],[1,7],[0]),e5 [49] [14],a5 [36] (r 0 4++[15]) [0,1],([0,1,8,2,3,9],[],[1]),([7,0,1,2,4,9],[5],[0,2]),([31,0,1,2,4,12],[1,13],[1]),a5 [22] (r 0 4) [0,1],([31,0,1,2,11,3],[1],[1]),([32,0,1,8,3,4],[1],[0]),u5 [32] [],([0,1,8,2,17,4],[],[0,1,2,3]),([23,0,1,3,4],[],[]),([0,1,2,5,4,12],[5],[0]),([32,0,1,2,3,9],[1],[0]),([0,1,8,3,9],[],[0,1,2,3]),e5 [23] [],a5 [31] [] [1],([26,1,2,3,4,9],[1,7],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_16_5 : checkNodesBT W_16 g_16 F_16 P_16_5 A_16 B_16_4 5 N_16_5 = true := by decide +kernel
def B_16_5 : BT (List (List Nat)) := buildBucketsBT W_16 N_16_5
set_option maxRecDepth 500000 in
lemma B_16_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_16 5 xs.toFinset) B_16_5 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok (buildPoolsSubBT_sound S_16_ok) A_16_ok B_16_4_ok C_16_5
def U_16_6 : List Nat := (r 0 4++[5]++r 10 4)
def P_16_6 : BT (Option BoundPool) := buildPoolsSubBT 4 W_16 r_16 S_16 ps_16 U_16_6
def N_16_6 : List NodeSpec := [a5 [31] (r 0 4++[5,13]) [0,1],a5 [9] (r 0 4++[5,10]) [0,1,2],a5 [32] (r 0 4++[5,12]) [0,1],a5 [8] (r 0 4++[5,11]) [0,1,2,3],a5 [5] (r 0 4++[5]) [0,1],a5 [21] (r 0 4++[5]) [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_16_6 : checkNodesBT W_16 g_16 F_16 P_16_6 A_16 B_16_5 6 N_16_6 = true := by decide +kernel
def B_16_6 : BT (List (List Nat)) := buildBucketsBT W_16 N_16_6
set_option maxRecDepth 500000 in
lemma B_16_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_16 6 xs.toFinset) B_16_6 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok (buildPoolsSubBT_sound S_16_ok) A_16_ok B_16_5_ok C_16_6
def U_16_7 : List Nat := (r 0 4++[5])
def P_16_7 : BT (Option BoundPool) := buildPoolsSubBT 4 W_16 r_16 S_16 ps_16 U_16_7
def N_16_7 : List NodeSpec := [a5 [] (r 0 4++[5]) [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_16_7 : checkNodesBT W_16 g_16 F_16 P_16_7 A_16 B_16_6 7 N_16_7 = true := by decide +kernel
def B_16_7 : BT (List (List Nat)) := buildBucketsBT W_16 N_16_7
set_option maxRecDepth 500000 in
lemma B_16_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_16 7 xs.toFinset) B_16_7 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok (buildPoolsSubBT_sound S_16_ok) A_16_ok B_16_6_ok C_16_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_16_ok : forestRootCheck r_16 g_16 [(VAR 0,12,13),(VAR 1,12,14),(VAR 2,9,13),(VAR 3,5,13),(VAR 4,3,19)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_16_in : bucketContainsBT B_16_7 r_16 = true := by decide +kernel
lemma low_16 : Lower r_16 g_16 8 := lower_of_forestBT root_16_ok B_16_7_ok root_16_in
def g_17 := (d 0xfee0fee0fee0fee0)
def r_17 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_17 : Lower r_17 g_17 5 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,4,5)]) (by decide +kernel) hc
def g_18 := (d 0xfffee800fffee800)
def r_18 : List Nat := varsOf 31
def p_18 : List Nat := [11,11,11,13,13,13,14,14,14,15,17,17,18,18,19,20,20,21,22,23,24,24,25,26,28]
def q_18 : List Nat := [10,9,3,12,9,5,12,10,6,7,16,1,16,2,3,16,4,5,6,7,16,8,9,10,12]
def F_18 : Nat := fullMask 25
set_option maxHeartbeats 0 in
lemma gp_18 : goodPairs g_18 p_18 q_18 := goodPairs_of (by decide +kernel)
def W_18 : BT Decor := buildWiresBT 8 (mkBase p_18 q_18 r_18) [(0,3,4),(1,2,5),(1,0,1),(0,7,3),(1,8,4),(1,0,2),(1,2,1),(1,11,4),(0,3,12),(1,7,4),(3,3,14),(1,1,10),(1,16,4),(3,2,17),(0,3,14),(0,2,14),(3,3,4),(1,21,8),(3,2,4),(3,2,7),(1,24,4),(3,2,3),(1,3,4),(0,10,27),(3,1,3),(1,2,4),(3,29,30),(1,0,4),(3,2,32),(1,26,0),(0,11,4),(3,35,12),(0,0,12),(0,7,30),(3,7,3),(1,39,2),(3,0,3),(3,41,11),(2,3,4),(2,7,4),(3,1,10),(1,10,4),(0,3,46),(3,11,3),(0,1,46),(3,1,14),(3,2,9),(1,2,3),(3,1,52),(3,5,27),(1,23,1),(1,21,7),(2,56,2),(0,11,3),(1,11,3),(3,58,59),(2,7,3),(3,0,30),(3,2,27),(1,63,0),(3,11,27),(1,0,5),(3,2,66),(1,7,3),(1,48,2),(1,48,4),(3,11,4),(1,71,2),(0,16,3),(1,1,4),(2,8,4),(1,26,4),(0,10,3),(3,35,3),(2,26,4),(1,26,1),(1,48,0),(1,34,4),(2,34,4),(0,7,4),(1,84,2),(1,79,0),(0,10,4),(1,21,0),(2,88,2),(1,84,3),(1,0,3),(3,11,91),(1,1,3),(3,2,93),(1,94,0),(0,7,52),(2,11,4),(1,97,0),(1,0,6),(2,16,4),(3,1,4),(1,101,0),(2,102,2),(1,26,7),(3,0,4),(3,105,11),(1,21,2),(1,61,2),(0,7,27),(1,10,3),(3,2,110),(2,24,4),(1,7,5),(3,21,7),(1,29,4),(3,2,115),(3,97,3),(0,3,30),(3,7,4),(3,11,32),(2,7,5),(1,58,0),(3,0,11),(3,123,3),(1,29,0),(2,125,2),(1,23,7),(3,41,74),(3,26,27),(3,2,74),(1,130,0),(3,62,3),(0,3,74),(1,0,133),(0,3,32),(1,23,0)]
lemma W_18_ok : btAll (fun x => faithful p_18 q_18 x ∧ x.1 < 2^256) W_18 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_18 : List (List (Nat × Nat)) := [[],[(1,2)],[(0,1)],[(0,2),(1,2)],[(0,1),(1,2)],[(0,2)]]
def A_18 : BT (List (Nat × Nat)) := btOfList 3 al_18
set_option maxHeartbeats 0 in
lemma A_18_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_18 = g_18) A_18 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_18_0 : Slice r_18 g_18 (subcubeFast 1 0) 6 := by
  have hc : Lower (varsOf 30) (d 0xfffcc000fffcc000) 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_1 : Slice r_18 g_18 (subcubeFast 2 0) 6 := by
  have hc : Lower (varsOf 29) (d 0xfffaa000fffaa000) 6 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_2 : Slice r_18 g_18 (subcubeFast 4 0) 6 := by
  have hc : Lower (varsOf 27) (d 0xffee8800ffee8800) 6 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_3 : Slice r_18 g_18 (subcubeFast 0 8) 5 := by
  have hc : Lower (varsOf 23) (d 0xffffe8e8ffffe8e8) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_4 : Slice r_18 g_18 (subcubeFast 16 0) 5 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_14
set_option maxHeartbeats 0 in
lemma sl_18_5 : Slice r_18 g_18 (subcubeFast 16 8) 4 := by
  exact slice_fast_direct_f (z := 16) (o := 8) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_18_6 : Slice r_18 g_18 (identDom 0 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xfefea8a8fefea8a8) 5 := carry_of (swaps := [(0,2),(1,2),(3,4)]) (by decide +kernel) low_17
  exact slice_ident (u := 0) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_7 : Slice r_18 g_18 (identDom 1 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xfefec8c8fefec8c8) 5 := carry_of (swaps := [(1,2),(3,4)]) (by decide +kernel) low_17
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_8 : Slice r_18 g_18 (identDom 2 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xfefee0e0fefee0e0) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_17
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
def S_18 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 1 0,6),some (subcubeFast 2 0,6),some (subcubeFast 4 0,6),some (subcubeFast 0 8,5),some (subcubeFast 16 0,5),some (subcubeFast 16 8,4),some (identDom 0 3,5),some (identDom 1 3,5),some (identDom 2 3,5)]
lemma S_18_ok : btAll (fun o => ∀ p, o = some p → Slice r_18 g_18 p.1 p.2) S_18 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_18_0) (forall_cons (fun _ h => by cases h; exact sl_18_1) (forall_cons (fun _ h => by cases h; exact sl_18_2) (forall_cons (fun _ h => by cases h; exact sl_18_3) (forall_cons (fun _ h => by cases h; exact sl_18_4) (forall_cons (fun _ h => by cases h; exact sl_18_5) (forall_cons (fun _ h => by cases h; exact sl_18_6) (forall_cons (fun _ h => by cases h; exact sl_18_7) (forall_cons (fun _ h => by cases h; exact sl_18_8) (fun _ h => (List.not_mem_nil h).elim))))))))))
def ps_18 : BT (Option PoolSpec) := btOfList 7 [q 1 [16428,16429,49295],q 1 [],q 2 [],q 0 [],q 0 [16396,16397,110615],q 1 [12332,12333,241899],q 0 [16397,110603],q 1 [16397,110603],q 2 [16396,20481],q 0 [12316,12317],q 7 [],q 4 [],q 8 [],q 0 [16413,57355],q 3 [16489],q 3 [],q 1 [16428,12431],q 6 [],q 0 [16412,8529],q 4 [122894],q 0 [16412,12625],q 1 [12299,105],q 0 [16396,20489],q 3 [20489],q 1 [16385,131083],q 0 [12319,8349],q 0 [12299,28777],q 0 [12318,12319],q 5 [],q 0 [12318,8437],q 0 [16397,110620],q 0 [16412,16413],q 0 [16396,20509],q 0 [131077,57356],q 1 [16385,57356],q 0 [16413,57356],q 1 [16413,57356],q 0 [16396,16397],q 1 [9],q 0 [16413,57359],q 0 [16393,122892],q 3 [16393],q 0 [16414,16415],q 1 [12291,45223],q 0 [16393,122908],q 1 [16385,131119],q 0 [16396,20510],q 1 [16397,110639],q 0 [16398,16399],q 2 [12295,117],q 1 [16396,16397,110615],q 2 [16396,16397,110615],q 0 [16389,303115],q 0 [131077,57355],q 3 [16389],q 4 [12299],q 0 [16389,303116],q 0 [16399],q 1 [16398,16399],q 2 [16398,16399],q 2 [16397],q 4 [110603],q 0 [16396],q 1 [16396,20481],q 3 [20481],q 1 [16396,20489],q 1 [16396,16397],q 2 [16396,16397],q 0 [131084],q 1 [16385,131084],q 2 [16385,131084],q 0 [131083],q 2 [16385],q 0 [16389],q 1 [16385],q 2 [16398],q 1 [12299],q 2 [12295],q 0 [12299],q 2 [16489],q 2 [105],q 0 [16395],q 2 [93],q 2 [4097],q 0 [12318],q 0 [12317],q 0 [8221],q 0 [16413],q 0 [16397],q 0 [8222],q 0 [12316],q 1 [12316],q 0 [16393],q 0 [8197],q 1 [12335],q 1 [8222],q 0 [131077],q 1 [8221],q 0 [4105],q 1 [16431],q 2 [12335],q 0 [16412],q 2 [16490],q 1 [16413],q 0 [16414],q 1 [16414],q 0 [12297],q 0 [16398],q 0 [372747],q 2 [12289],q 1 [16399],q 2 [16399],q 1 [16398],q 1 [16397],q 1 [16396],q 2 [16396],q 1 [16395],q 1 [12289]]
def B_18_2 : BT (List (List Nat)) := BT.empty
lemma B_18_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_18 2 xs.toFinset) B_18_2 := .empty
def U_18_3 : List Nat := []
def P_18_3 : BT (Option BoundPool) := buildPoolsSubBT 7 W_18 r_18 S_18 ps_18 U_18_3
def N_18_3 : List NodeSpec := [([0,1,6,9],[],[]),([7,10,13,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_18_3 : checkNodesBT W_18 g_18 F_18 P_18_3 A_18 B_18_2 3 N_18_3 = true := by decide +kernel
def B_18_3 : BT (List (List Nat)) := buildBucketsBT W_18 N_18_3
set_option maxRecDepth 500000 in
lemma B_18_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_18 3 xs.toFinset) B_18_3 :=
  buildBucketsBT_sound (by decide) gp_18 W_18_ok (buildPoolsSubBT_sound S_18_ok) A_18_ok B_18_2_ok C_18_3
def U_18_4 : List Nat := (r 0 6)
def P_18_4 : BT (Option BoundPool) := buildPoolsSubBT 7 W_18 r_18 S_18 ps_18 U_18_4
def N_18_4 : List NodeSpec := [([15,18,0,1,4],[],[]),([18,0,1,19,4],[],[]),([15,0,1,20,4],[],[]),([0,1,22,2,4],[],[]),([23,0,1,3,25],[],[]),([26,0,1,28,4],[],[]),([0,31,11,3,4],[],[]),([33,34,1,3,4],[],[]),([0,1,10,13,4],[],[0]),([36,0,1,2,3],[0],[]),([37,1,2,13,4],[],[]),([0,38,11,3,4],[1],[]),([0,1,40,4,27],[],[]),([42,1,10,3,4],[2],[]),([26,0,8,11,4],[],[]),([43,0,1,40,4],[],[]),([44,10,11,3,4],[],[]),([24,45,0,3,4],[],[]),([33,0,1,47,4],[],[]),([48,7,10,3,4],[3],[]),([33,0,49,3,4],[],[]),([44,50,0,2,3],[],[]),([7,10,3,4,12],[3],[0]),([8,10,11,3,4],[],[]),([51,0,1,3,4],[],[]),([24,53,0,3,4],[],[]),([54,0,1,7,2],[4],[]),([24,0,55,3,4],[],[]),([57,0,1,3,4],[],[]),([18,0,1,3,4],[],[]),([0,1,2,5,9],[],[0]),([0,1,8,6,4],[],[0]),([60,0,1,2,4],[5],[]),([61,0,1,40,4],[],[]),([33,62,1,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_18_4 : checkNodesBT W_18 g_18 F_18 P_18_4 A_18 B_18_3 4 N_18_4 = true := by decide +kernel
def B_18_4 : BT (List (List Nat)) := buildBucketsBT W_18 N_18_4
set_option maxRecDepth 500000 in
lemma B_18_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_18 4 xs.toFinset) B_18_4 :=
  buildBucketsBT_sound (by decide) gp_18 W_18_ok (buildPoolsSubBT_sound S_18_ok) A_18_ok B_18_3_ok C_18_4
def U_18_5 : List Nat := (r 1 4++r 6 51)
def P_18_5 : BT (Option BoundPool) := buildPoolsSubBT 7 W_18 r_18 S_18 ps_18 U_18_5
def N_18_5 : List NodeSpec := [e5 [64] [6],([65,63,0,1,3,4],[7],[]),([63,0,64,1,3,4],[6],[]),e5 [67] [8],e5 [44] [],([0,1,8,2,68,4],[9],[4]),([0,1,69,11,3,4],[1,10],[]),([0,1,16,3,4,30],[11],[]),e5 [70] [],([0,1,72,11,3,4],[1,11],[]),e5 [73] [],([24,23,0,1,3,4],[],[0,2]),([0,11,3,4,74,30],[1,11],[]),([67,1,2,3,66,4],[8],[]),([0,1,40,3,4],[],[0]),([61,29,0,7,2,4],[],[]),([21,0,1,8,2,4],[],[0]),([24,0,1,3,52,4],[12],[0,2]),([18,0,1,7,3,4],[13],[]),([33,0,1,3,4,30],[2],[0]),e5 [75] [],([43,26,0,1,2,76],[11,14],[]),([26,0,1,77,10,4],[15],[]),([43,48,0,1,2,4],[11],[3]),([26,0,1,8,2,4],[2],[0,2]),([78,0,1,2,11,4],[16],[]),([79,0,1,10,3,4],[3],[]),([37,1,2,3,4,12],[],[0,2,3,4]),([26,0,80,11,3,4],[1],[]),u5 [9] [1,2,3,17],([0,1,10,3,4,12],[3],[0]),e5 [81] [],e5 [82] [15],a5 [17] [15,17] [0,1,3],([48,0,1,10,3,4],[3],[0]),e5 [83] [],([0,1,7,85,3,4],[18],[]),([24,29,0,2,3,4],[],[]),e5 [86] [],([0,1,87,10,3,30],[],[]),([0,7,11,3,4,30],[],[0,2]),e5 [89] [],([26,0,7,11,3,4],[],[0,2,4]),([0,1,10,3,4,76],[3],[]),([0,1,2,3,76,30],[2,12,19],[]),([44,0,2,11,3,4],[2],[0]),([0,1,7,2,90,4],[20],[]),e5 [92] [17],([24,0,7,11,3,4],[1,2],[]),([63,0,1,10,3,4],[3],[]),([26,0,1,10,4,27],[],[0]),e5 [95] [],([48,0,1,2,4,27],[],[3]),e5 [96] [],([26,33,0,1,3,4],[15],[0]),([0,34,1,11,3,4],[21],[]),e5 [98] [],([0,1,3,6,99,4],[12,22,23],[]),e5 [100] [],([33,1,7,2,3,4],[1,24],[]),([0,1,7,40,3,4],[17,25],[0]),([0,1,8,2,5,4],[10,17],[0]),([26,29,0,11,3,4],[1,2,15],[]),e5 [103] [],e5 [104] [2,26],e5 [106] [],([61,39,0,1,2,4],[27],[0,4]),([0,1,10,3,6,4],[3,12,23],[]),([0,1,107,10,3,4],[3,15],[]),([26,0,1,16,3,4],[15],[]),([43,26,0,1,10,4],[28],[]),([44,0,7,2,3,74],[11],[]),([24,0,1,16,3,4],[3],[0,2]),([0,1,7,108,3,4],[29],[]),a5 [109] [15,30] [1,3],([0,1,84,2,3,14],[31],[4]),([111,0,1,11,3,4],[1,15],[3]),([33,0,1,3,4,46],[3],[0,1]),e5 [112] [],e5 [113] [17,32],e5 [114] [],([0,1,8,2,52,4],[2],[]),([18,0,1,3,4],[],[]),([0,1,2,19,4,32],[33,34],[1]),([24,0,2,3,4,74],[],[]),e5 [18] [],([18,0,1,3,4,14],[2],[0]),([0,1,2,19,4],[35,36],[4,5]),e5 [19] [],([0,1,7,2,5,27],[37],[0]),([7,10,11,3,4],[1,2,3,38],[0,1,2,3,4]),([0,1,2,19,4,14],[15],[0,1,3,4]),([15,0,1,2,4,14],[17],[0]),([15,0,1,7,2,4],[39],[]),([44,0,1,2,3,14],[3],[0,2]),([33,0,1,10,3,4],[3],[1]),([0,1,7,2,19,4],[35],[]),([43,0,34,1,2,4],[],[]),e5 [116] [],([33,1,10,3,4,32],[2],[]),([111,0,1,10,3,4],[3,15],[]),e5 [117] [1,2,3,17],([0,1,10,118,3,4],[3,40,41],[]),([0,1,72,10,3,4],[3],[1]),u5 [14] [2,15,17],([44,119,0,1,2,3],[42],[4]),([24,0,1,10,3,4],[3],[0]),a5 [42] [1,2,15,43] [0,1],a5 [38] [1,11,44] [0,2],e5 [120] [45],([0,1,77,11,3,4],[1],[1]),e5 [121] [3,46],e5 [122] [],([0,1,7,3,6,4],[22,23],[0]),e5 [124] [17],e5 [65] [47],([63,0,1,7,3,4],[6],[]),([43,21,0,1,7,2],[48],[0]),u5 [56] [2,15],([0,1,69,3,4,30],[11],[4]),e5 [126] [49],([0,34,1,2,4,27],[],[]),u5 [127] [15,17],a5 [128] [] [4],([54,0,1,2],[4,28,50,51],[0,1,3]),e5 [8] [],([26,0,1,2,129,4],[15],[]),e5 [131] [52],([18,0,1,3,4,32],[53],[]),([44,0,1,2,3,32],[3],[0]),u5 [25] [],([26,0,11,3,4,74],[1,54,55],[1]),e5 [132] [],e5 [134] [56]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_18_5 : checkNodesBT W_18 g_18 F_18 P_18_5 A_18 B_18_4 5 N_18_5 = true := by decide +kernel
def B_18_5 : BT (List (List Nat)) := buildBucketsBT W_18 N_18_5
set_option maxRecDepth 500000 in
lemma B_18_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_18 5 xs.toFinset) B_18_5 :=
  buildBucketsBT_sound (by decide) gp_18 W_18_ok (buildPoolsSubBT_sound S_18_ok) A_18_ok B_18_4_ok C_18_5
def U_18_6 : List Nat := ([1,2,3,6,7,8,10,11,12,14,15,17]++r 21 4++[28,37,38,41,48,55]++r 57 53)
def P_18_6 : BT (Option BoundPool) := buildPoolsSubBT 7 W_18 r_18 S_18 ps_18 U_18_6
def N_18_6 : List NodeSpec := [a5 [88] [1,2,11,15,57] [0,1,3,5],([43,21,0,1,2],[28,48,58,59],[0,1,3]),a5 [63] [1,2,3,6,7,15,28,60] [0,2],([63,0,1,3,4],[6,7,15,28,61],[0,2]),a5 [66] [8,28,62,63,64] [0,1,3,5],([0,1,3,6,4],[22,23,28,65],[0,2,4,5]),e5 [135,32] [3,11,17,28],([0,1,2,5,27],[11,15,37,66,67],[0,1,3]),a5 [135] [1,2,10,11,12,17,28,68,69,70] [2,3,4,5],u5 [33,32] [2,3,11,71,72],a5 [33] [1,3,12,15,24,71,72] [0,2,5],a5 [32,74] [73,74] [1,3,4],([43,26,0,1,2,4],[2,11,28,75],[0,2]),([26,0,1,2,4,27],[11,15,28,55,60],[0,2]),u5 [26,29] [2,10,12,76,77],a5 [26,32] [3,12,72,78] [0,2,3,4],u5 [26,76] [2,12,14,28],a5 [76] [1,3,12,14,28,79] [0,1,2,3],a5 [26,34] [15,17,78,80] [2],a5 [136] [1,11,28,81,82] [0,1,3],u5 [79,30] [12,28],a5 [61,7] [1,3,15,83,84] [0,2],a5 [7,68] [15,17,85] [0,1,3],a5 [7,16] [83,86] [0,1,3],a5 [7,14] [11,83,87] [0,1,3],a5 [26,7] [1,2,3,12,15,78,83] [0,1,2,3,4],a5 [7,27] [1,15,83,88] [0,1,3,4],a5 [24,7] [1,2,3,83,89] [0,2],a5 [8] [1,2,3,11,12,17,90,91] [0,1,3,4],([0,1,10,3,4,30],[2,11,41,92],[0,1,2,3,4,5]),a5 [48,11] [10,15,93,94] [0,1,3],a5 [24] [1,3,11,12,15,83,89,95] [0,2,4],a5 [32,14] [28,72,74,96] [0,1,3],a5 [16] [11,15,17,83,86,97] [0,1,3],a5 [8,7] [1,15,17,90] [0,1,3],([26,0,1,10,3,4],[2,3,15,55,78],[0,1,2]),a5 [7,5] [1,11,15,62,83] [0,1,3],([0,1,10,11,3,4],[2,38,98],[0,1,2,3]),a5 [71,11] [11,99] [0,1,3],a5 [48] [3,10,11,94,100] [0,1,3],a5 [84,7] [1,11,83,101] [0,1,3,4],a5 [79] [1,3,10,12,17,28,102] [0,2],a5 [14] [2,15,17,87,103] [0,1,3,4,5],a5 [44] [1,2,3,15,104,105] [0,2,4],a5 [44,7] [1,3,11,104] [0,2],a5 [7,52] [1,2,15,83,106] [0,4,5],a5 [43,7] [1,3,17,28,107] [0,1,3,4],a5 [21,7] [1,3,15,57] [0,1,3],a5 [23,7] [1,2,3,11,81,83] [0,1,3,4],a5 [111] [1,3,11,15,28,108,109] [0,2],a5 [7,30] [1,2,83,92] [0,1,2,3,4],a5 [34] [11,17,21,78,80] [0,1,3]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_18_6 : checkNodesBT W_18 g_18 F_18 P_18_6 A_18 B_18_5 6 N_18_6 = true := by decide +kernel
def B_18_6 : BT (List (List Nat)) := buildBucketsBT W_18 N_18_6
set_option maxRecDepth 500000 in
lemma B_18_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_18 6 xs.toFinset) B_18_6 :=
  buildBucketsBT_sound (by decide) gp_18 W_18_ok (buildPoolsSubBT_sound S_18_ok) A_18_ok B_18_5_ok C_18_6
def U_18_7 : List Nat := ([1,2,3,11,12,15,28,57,60,62,72,74,75,76,78,81,83,88,107]++r 109 9)
def P_18_7 : BT (Option BoundPool) := buildPoolsSubBT 7 W_18 r_18 S_18 ps_18 U_18_7
def N_18_7 : List NodeSpec := [a5 [21] [1,2,3,11,15,57,110,111] [0,1,2,3,4],a5 [43] [1,2,3,28,75,107,112] [0,1,3],a5 [27] [1,2,3,15,28,60,88,113] [0,1,3],a5 [5] [1,2,3,11,15,28,62,114,115] [0,1,2,3,4],a5 [23] [1,2,3,11,15,28,81,116] [0,2],a5 [26] [1,2,3,11,12,15,28,76,78] [0,2],a5 [91] [3,15,28,109,117] [0,1,3],a5 [32] [3,28,72,74] [0,1,3,5],a5 [7] [1,2,3,11,15,83] [0,1,3,4]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_18_7 : checkNodesBT W_18 g_18 F_18 P_18_7 A_18 B_18_6 7 N_18_7 = true := by decide +kernel
def B_18_7 : BT (List (List Nat)) := buildBucketsBT W_18 N_18_7
set_option maxRecDepth 500000 in
lemma B_18_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_18 7 xs.toFinset) B_18_7 :=
  buildBucketsBT_sound (by decide) gp_18 W_18_ok (buildPoolsSubBT_sound S_18_ok) A_18_ok B_18_6_ok C_18_7
def U_18_8 : List Nat := [1,2,3]
def P_18_8 : BT (Option BoundPool) := buildPoolsSubBT 7 W_18 r_18 S_18 ps_18 U_18_8
def N_18_8 : List NodeSpec := [a5 [] [1,2,3] [0,1,2,3,4]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_18_8 : checkNodesBT W_18 g_18 F_18 P_18_8 A_18 B_18_7 8 N_18_8 = true := by decide +kernel
def B_18_8 : BT (List (List Nat)) := buildBucketsBT W_18 N_18_8
set_option maxRecDepth 500000 in
lemma B_18_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_18 8 xs.toFinset) B_18_8 :=
  buildBucketsBT_sound (by decide) gp_18 W_18_ok (buildPoolsSubBT_sound S_18_ok) A_18_ok B_18_7_ok C_18_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_18_ok : forestRootCheck r_18 g_18 [(VAR 0,10,11),(VAR 1,9,11),(VAR 2,9,13),(VAR 3,3,11),(VAR 4,1,17)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_18_in : bucketContainsBT B_18_8 r_18 = true := by decide +kernel
lemma low_18 : Lower r_18 g_18 9 := lower_of_forestBT root_18_ok B_18_8_ok root_18_in
def g_19 := (d 0xfffcfc80fffcfc80)
def r_19 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_19 : Lower r_19 g_19 8 := by
  have hc : Lower (varsOf 30) (d 0xfffcfcc0fffcfcc0) 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,6,7)]) (by decide +kernel) hc
def g_20 := (d 0xfff8f880fff8f880)
def r_20 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_20 : Lower r_20 g_20 8 := by
  have hc : Lower (varsOf 30) (d 0xfffcfcc0fffcfcc0) 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,6,7)]) (by decide +kernel) hc
def g_21 := (d 0xffffffe8fec0c000)
def r_21 : List Nat := varsOf 63
def p_21 : List Nat := [14,14,14,15,15,15,22,22,22,23,23,23,25,25,25,26,26,26,27,27,28,28,28,29,29,35,35,35,37,37,37,38,38,38,39,40,40,41,41,42,42,43,44,44,45,48,48,49,49,50,50,51,52,52,53,56]
def q_21 : List Nat := [12,10,6,13,11,7,20,18,6,21,19,7,24,17,9,24,18,10,19,11,24,20,12,21,13,34,33,3,36,33,5,36,34,6,7,32,8,33,9,34,10,11,36,12,13,32,16,33,17,34,18,19,36,20,21,24]
def F_21 : Nat := fullMask 56
set_option maxHeartbeats 0 in
lemma gp_21 : goodPairs g_21 p_21 q_21 := goodPairs_of (by decide +kernel)
def W_21 : BT Decor := buildWiresBT 10 (mkBase p_21 q_21 r_21) [(0,2,4),(1,2,4),(3,6,7),(0,1,3),(1,1,3),(3,9,10),(0,8,11),(1,8,11),(3,12,13),(0,8,5),(1,8,5),(3,15,16),(0,17,1),(1,1,17),(3,18,19),(1,3,5),(0,2,21),(1,2,21),(3,22,23),(0,24,1),(1,24,1),(3,25,26),(0,3,5),(0,4,5),(1,29,3),(0,2,30),(1,2,30),(3,31,32),(0,33,1),(1,33,1),(3,34,35),(1,3,4),(3,2,37),(2,2,37),(0,3,4),(1,39,40),(0,1,41),(1,1,41),(3,42,43),(0,2,37),(1,2,37),(3,45,46),(0,47,1),(1,47,1),(3,48,49),(1,8,1),(0,8,1),(1,52,28),(0,2,3),(1,2,3),(3,54,55),(1,56,1),(0,56,1),(1,58,29),(2,57,59),(0,1,2),(1,61,40),(0,62,5),(1,62,5),(3,63,64),(1,1,2),(0,56,5),(1,56,5),(3,67,68),(0,69,1),(1,1,69),(1,37,5),(0,66,72),(0,4,21),(1,61,74),(1,4,5),(3,29,76),(0,77,3),(1,78,61),(1,77,3),(3,74,72),(1,61,28),(0,3,76),(1,61,29),(0,1,37),(1,1,37),(3,85,86),(2,87,2),(3,87,2),(1,89,40),(0,2,5),(1,2,5),(3,91,92),(0,1,4),(1,1,4),(3,94,95),(0,93,96),(1,93,96),(3,40,72),(0,37,5),(1,61,100),(0,4,82),(1,4,82),(3,102,103),(2,8,28),(0,105,1),(1,105,1),(3,106,107),(2,11,2),(3,11,2),(2,96,3),(2,111,2),(3,96,3),(1,112,113),(3,111,2),(0,111,2),(1,116,113),(1,111,2),(0,11,5),(1,11,5),(3,119,120),(2,121,2),(3,121,2),(3,8,1),(2,8,1),(1,125,28),(1,124,126),(0,1,76),(1,1,76),(3,128,129),(2,130,2),(3,130,2),(1,132,29),(3,116,118),(1,123,4),(0,1,5),(1,136,40),(0,2,137),(1,2,137),(3,138,139),(1,1,5),(3,29,72),(1,61,83),(3,100,72),(2,8,11),(3,8,11),(2,93,11),(3,93,11),(1,93,1),(0,93,1),(1,150,40),(0,2,76),(1,2,76),(3,152,153),(3,154,1),(1,155,3),(2,3,76),(0,66,76),(1,157,158),(3,61,159),(2,66,102),(3,61,72),(2,3,84),(3,3,84),(3,164,66),(1,28,4),(0,2,166),(1,2,166),(3,167,168),(1,124,3),(3,4,21),(2,4,21),(1,172,28),(0,169,1),(1,169,1),(3,84,76),(2,176,0),(3,177,77),(3,56,1),(2,56,1),(3,180,76),(3,28,21),(2,182,4),(3,182,4),(2,3,5),(3,3,5),(2,96,2),(3,96,2),(2,8,3),(0,189,1),(1,189,1),(3,190,191),(2,56,4),(2,193,1),(3,56,4),(1,194,195),(3,84,72),(1,91,40),(0,1,198),(1,1,198),(3,17,1),(2,62,100),(0,95,21),(0,2,203),(1,2,203),(3,204,205),(1,188,28),(0,66,21),(3,136,141),(2,209,2),(3,209,2),(1,40,5),(1,155,29),(2,62,5),(3,62,5),(2,37,5),(3,37,5),(3,63,37),(0,193,1),(1,193,1),(3,61,80),(2,3,4),(1,222,158),(3,61,223),(2,66,100),(2,66,63),(3,172,66),(0,1,166),(1,1,166),(3,228,229),(2,230,2),(3,230,2),(3,157,66),(0,8,21),(1,52,3),(1,40,101),(3,77,3),(2,66,237),(3,62,72),(2,11,29),(2,240,2),(3,240,2),(0,10,76),(0,2,243),(1,9,244),(1,2,243),(2,11,4),(2,247,2),(3,11,4),(1,247,249),(0,3,84),(1,3,84),(2,1,198),(3,1,198),(1,0,84),(0,255,76),(1,219,195),(1,136,3),(0,8,258),(1,8,3),(2,56,29),(0,261,1),(1,261,1),(3,61,76),(2,264,0),(3,265,76),(1,247,2),(3,138,141),(3,209,8),(0,154,1),(1,154,1),(1,217,40),(1,121,2),(2,57,29),(0,66,80),(1,180,29),(1,193,195),(3,3,76),(3,247,2),(0,8,10),(1,15,3),(3,37,64),(3,47,1),(1,283,40),(2,1,41),(3,1,41),(2,1,37),(1,287,40),(0,2,288),(1,2,288),(3,289,290),(3,102,21),(3,61,212),(3,2,137),(3,93,1),(1,222,295),(2,149,40),(2,93,40),(2,2,3),(1,299,128),(2,93,3),(2,1,4),(1,301,302),(0,77,2),(3,304,10),(3,152,10),(2,93,4),(3,307,10),(1,93,3),(0,309,95),(0,7,21),(2,1,311),(3,1,311),(1,1,311),(3,6,314),(3,1,5),(1,316,3),(0,8,317),(3,316,8),(1,319,3),(2,8,136),(1,321,3),(2,1,3),(3,8,5),(1,323,324),(2,93,1),(1,326,40),(3,324,10),(3,15,10),(3,2,288),(3,1,37),(2,77,2),(2,77,1),(1,222,61),(0,334,5),(1,335,4),(1,334,5),(1,157,84),(2,1,2),(3,61,272),(3,78,66),(3,2,76),(3,1,76),(2,293,0),(3,2,21),(3,1,21),(2,56,136),(3,343,55),(3,316,260),(1,185,187),(1,222,150),(1,323,304),(3,0,212),(1,61,5),(3,4,354),(0,77,66),(1,157,339),(3,261,1),(1,180,4),(1,61,3),(2,360,4),(3,4,82),(1,0,82),(2,4,3),(1,364,61),(0,365,5),(1,365,5),(3,366,367),(1,353,61),(3,185,51),(1,339,100),(3,52,21),(1,323,342),(3,323,8),(3,0,76),(1,375,84),(3,125,21),(1,360,5),(3,4,378),(1,0,334),(3,2,212),(3,1,212),(3,193,1),(3,4,5),(1,179,4),(1,222,210),(0,55,76),(0,1,387),(1,54,388),(2,247,91),(2,2,1),(3,391,80),(3,391,72),(3,0,21),(1,332,323),(0,66,212),(3,0,72),(2,162,0),(0,95,55),(0,399,5),(1,399,5),(3,400,401),(1,124,28),(3,222,21),(3,169,1),(1,61,4),(0,406,21),(1,364,5),(1,185,124),(3,2,5),(1,247,410),(3,61,21),(2,412,0),(3,413,21),(3,332,10),(2,77,0),(3,82,21),(1,96,3),(3,91,418),(0,193,5),(1,420,4),(1,157,61),(3,364,66),(0,264,3),(1,264,3),(3,424,425),(2,66,74),(1,78,339),(2,96,91),(1,348,29),(1,295,40),(1,339,237),(1,339,83),(1,323,15),(0,8,3),(1,58,4),(2,56,316),(1,185,52),(2,193,316),(0,51,21),(1,125,3),(3,364,149),(1,61,237),(3,124,21),(3,302,56),(3,302,309),(3,194,56),(1,189,136),(2,162,2),(0,1,72),(3,2,80),(0,1,80),(3,77,2),(1,182,1),(2,454,4),(1,77,1),(0,456,3),(1,77,2),(0,458,1),(0,77,1),(1,1,21),(3,4,461),(0,3,129),(3,2,129),(0,1,153),(2,57,4),(1,384,3),(0,66,467),(3,342,72),(3,1,3),(3,470,8),(3,412,4),(1,472,5),(3,29,129),(1,472,3),(0,77,10),(0,2,72),(1,477,1),(3,1,4),(1,324,3),(3,479,93),(0,96,5),(3,222,66),(2,4,5),(3,484,37),(1,61,485),(2,66,4),(3,487,21),(1,412,4),(3,264,72),(3,61,467),(0,1,21),(3,334,5),(1,493,3),(1,1,28),(3,2,467),(3,1,467),(0,10,7),(0,498,5),(1,498,5),(3,4,401),(1,185,4),(2,2,21),(1,503,28),(2,412,4),(0,360,76),(1,157,264),(0,93,3),(3,365,76),(2,1,5),(2,8,5),(1,484,3),(2,334,5),(3,333,76),(0,37,141),(2,162,1),(1,222,5),(3,299,77),(3,299,76),(1,360,4),(3,0,467),(1,94,54),(3,364,76),(2,93,94),(3,391,76),(1,157,525),(2,456,2),(1,8,28),(3,172,406),(1,186,4),(0,182,4),(3,40,86),(2,491,0),(1,302,345),(0,96,3),(3,391,212),(0,2,212),(3,391,21),(1,364,339),(1,222,525),(1,450,2),(2,77,391),(1,339,4),(0,543,21),(1,339,74),(1,222,264),(0,334,76),(1,172,339),(0,56,4),(3,8,3),(1,1,550),(1,56,4),(3,193,5),(2,1,195),(0,209,3),(3,56,5),(0,8,141),(3,510,8),(2,11,6),(2,1,29),(3,185,8),(1,54,136),(1,6,28),(3,264,21),(3,2,243),(2,498,5),(3,498,5),(0,93,10),(1,1,387),(3,323,93),(2,2,4),(3,571,10),(1,571,492),(0,182,2),(3,93,4),(3,364,93),(3,37,141),(1,577,40),(3,316,212),(0,1,212),(1,2,100),(3,346,7),(3,477,1),(3,449,1),(1,346,4),(1,157,128),(0,4,461),(1,345,4),(3,2,461),(1,492,4),(3,77,1),(2,1,76),(1,339,3),(0,593,76),(3,399,5),(3,2,258),(1,479,28),(2,10,4),(1,598,5),(2,66,3),(3,600,76),(1,302,3),(0,602,76),(3,571,21),(2,258,4),(3,2,3),(2,66,29),(1,128,3),(0,1,23),(2,1,21),(1,610,28),(3,364,406),(3,365,5),(2,1,166),(3,1,166),(1,410,3),(3,29,3),(0,10,92),(2,618,4),(1,299,29),(1,6,5),(0,10,621),(0,258,7),(1,222,339),(0,467,95),(0,2,461),(1,9,91),(3,299,95),(3,391,467),(1,94,5),(0,2,467),(1,618,4),(1,91,4),(1,2,28),(1,410,4),(1,2,29),(2,10,29),(3,6,258),(1,91,3),(1,9,29),(1,571,3),(0,641,95),(1,361,0),(0,55,141),(2,2,28),(0,602,92),(1,136,4),(3,299,647),(3,93,3),(3,302,21),(3,479,639),(0,2,258),(3,364,647),(3,4,141),(1,654,3),(1,410,40),(2,1,100),(0,1,639),(0,639,4),(1,449,1),(3,2,4),(0,1,30),(1,1,30),(0,1,467),(1,222,410),(1,616,4),(1,510,222),(2,2,5),(3,668,37),(1,510,40),(1,510,3),(1,671,4),(1,510,4),(3,3,141),(3,364,141),(0,647,3),(1,384,606),(1,484,606),(1,661,28),(1,470,410),(3,479,92),(3,2,30),(1,606,5),(3,0,683),(1,661,3),(2,685,5),(1,685,5),(1,185,302),(3,299,141),(1,571,136),(1,302,606),(1,323,571),(1,302,5),(1,299,5),(2,602,5),(1,1,29),(1,602,5),(1,323,4),(0,1,641),(3,186,95),(3,484,10),(2,598,5),(3,479,21),(2,10,5),(1,593,4),(3,186,66),(2,671,4),(3,484,66),(3,3,92),(1,606,136),(1,302,410),(2,593,4),(1,9,5),(3,2,713),(3,391,37),(0,406,3),(2,66,5),(1,717,3),(3,2,602),(2,487,3),(1,487,3),(2,593,5),(2,616,4),(2,95,5),(1,724,3),(0,66,37),(1,661,470),(3,316,37),(1,384,61),(1,717,0),(3,61,37),(2,66,40),(1,342,3),(3,91,37),(3,40,141),(2,360,5),(1,487,5),(1,258,4),(1,302,28),(2,487,5),(1,94,3),(2,741,5),(3,4,683),(1,185,339),(1,606,4),(1,339,40),(1,185,61),(1,9,4),(1,323,5),(3,4,749),(1,668,9),(1,593,5),(3,479,55),(1,339,5),(3,4,754),(3,316,55),(3,91,10),(1,339,28),(1,384,339),(1,222,136),(1,741,5),(1,54,5),(1,510,606),(0,1,762),(3,4,713),(1,384,9),(3,6,10),(1,571,9),(1,661,9),(3,6,141),(1,410,9),(1,94,28),(3,6,21),(1,484,9),(1,316,4),(3,3,7),(1,668,302),(1,571,5),(1,668,3),(1,323,384),(1,661,5),(3,668,10),(2,55,4),(3,3,95)]
lemma W_21_ok : btAll (fun x => faithful p_21 q_21 x ∧ x.1 < 2^256) W_21 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_21 : List (List (Nat × Nat)) := [[],[(3,4)],[(1,2)],[(1,2),(3,4)]]
def A_21 : BT (List (Nat × Nat)) := btOfList 2 al_21
set_option maxHeartbeats 0 in
lemma A_21_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_21 = g_21) A_21 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_21_0 : Slice r_21 g_21 (subcubeFast 1 0) 10 := by
  have hc : Lower (varsOf 62) (d 0xffffffc0fcc0c000) 10 := carry_of (swaps := [(0,5),(1,5),(2,5),(3,5),(4,5)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_1 : Slice r_21 g_21 (subcubeFast 0 1) 9 := by
  have hc : Lower (varsOf 62) (d 0xfffffffcffc0c000) 9 := carry_of (swaps := [(0,5),(1,5),(2,5),(3,5),(4,5)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_2 : Slice r_21 g_21 (subcubeFast 0 2) 8 := by
  have hc : Lower (varsOf 61) (d 0xfffffffafff0f000) 8 := carry_of (swaps := [(1,5),(2,5),(3,5),(4,5)]) (by decide +kernel) low_10
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_3 : Slice r_21 g_21 (subcubeFast 0 4) 8 := by
  have hc : Lower (varsOf 59) (d 0xffffffeeffcccc00) 8 := carry_of (swaps := [(2,5),(3,5),(4,5)]) (by decide +kernel) low_10
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_4 : Slice r_21 g_21 (subcubeFast 32 0) 8 := by
  exact slice_fast_direct_f (z := 32) (o := 0) (by decide +kernel) low_11
set_option maxHeartbeats 0 in
lemma sl_21_5 : Slice r_21 g_21 (identDom 0 5) 9 := by
  have hc : Lower (varsOf 31) (d 0xfeeaeaa8feeaeaa8) 9 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_12
  exact slice_ident (u := 0) (v := 5) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_6 : Slice r_21 g_21 (identDom 0 1) 9 := by
  have hc : Lower (varsOf 61) (d 0xffffffaafaa0a000) 9 := carry_of (swaps := [(0,1),(1,5),(2,5),(3,5),(4,5)]) (by decide +kernel) low_13
  exact slice_ident (u := 0) (v := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_7 : Slice r_21 g_21 (subcubeFast 33 0) 7 := by
  have hc : Lower (varsOf 30) (d 0xfcc0c000fcc0c000) 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 33) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_8 : Slice r_21 g_21 (subcubeFast 1 4) 7 := by
  have hc : Lower (varsOf 58) (d 0xffffffccffcccc00) 7 := carry_of (swaps := [(0,4),(1,4),(2,5),(3,4),(4,5)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 1) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_9 : Slice r_21 g_21 (subcubeFast 1 2) 7 := by
  have hc : Lower (varsOf 60) (d 0xfffffff0fff0f000) 7 := carry_of (swaps := [(0,4),(1,5),(2,4),(3,5)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 1) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_10 : Slice r_21 g_21 (subcubeFast 16 0) 8 := by
  have hc : Lower (varsOf 47) (d 0xffe8ffe8c000c000) 8 := carry_of (swaps := [(4,5)]) (by decide +kernel) low_15
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_11 : Slice r_21 g_21 (subcubeFast 8 0) 8 := by
  have hc : Lower (varsOf 55) (d 0xffffe8e8c0c00000) 8 := carry_of (swaps := [(3,5),(4,5)]) (by decide +kernel) low_15
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_12 : Slice r_21 g_21 (subcubeFast 2 0) 8 := by
  have hc : Lower (varsOf 61) (d 0xffffffa0fa000000) 8 := carry_of (swaps := [(1,5),(2,5),(3,5),(4,5)]) (by decide +kernel) low_16
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_13 : Slice r_21 g_21 (subcubeFast 4 0) 8 := by
  have hc : Lower (varsOf 59) (d 0xffffff88ee000000) 8 := carry_of (swaps := [(2,5),(3,5),(4,5)]) (by decide +kernel) low_16
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_14 : Slice r_21 g_21 (identDom 3 4) 9 := by
  have hc : Lower (varsOf 47) (d 0xffe8ffe8fe00fe00) 9 := carry_of (swaps := [(3,4),(4,5)]) (by decide +kernel) low_18
  exact slice_ident (u := 3) (v := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_15 : Slice r_21 g_21 (identDom 1 2) 8 := by
  have hc : Lower (varsOf 59) (d 0xffffffcceecccc00) 8 := carry_of (swaps := [(1,3),(2,5),(4,5)]) (by decide +kernel) low_19
  exact slice_ident (u := 1) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_16 : Slice r_21 g_21 (identDom 0 4) 8 := by
  have hc : Lower (varsOf 47) (d 0xffeaffeaea80ea80) 8 := carry_of (swaps := [(0,2),(1,2),(4,5)]) (by decide +kernel) low_20
  exact slice_ident (u := 0) (v := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_17 : Slice r_21 g_21 (subcubeFast 16 1) 6 := by
  have hc : Lower (varsOf 46) (d 0xfffcfffcc000c000) 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4),(4,5)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 16) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_18 : Slice r_21 g_21 (subcubeFast 8 1) 6 := by
  have hc : Lower (varsOf 54) (d 0xfffffcfcc0c00000) 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,5)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 8) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_19 : Slice r_21 g_21 (subcubeFast 24 32) 4 := by
  exact slice_fast_direct_f (z := 24) (o := 32) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_21_20 : Slice r_21 g_21 (subcubeFast 33 16) 4 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 33) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_21 : Slice r_21 g_21 (subcubeFast 33 8) 4 := by
  have hc : Lower (varsOf 22) (d 0xfcfcc0c0fcfcc0c0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 33) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_22 : Slice r_21 g_21 (subcubeFast 32 5) 4 := by
  have hc : Lower (varsOf 26) (d 0xffcccc00ffcccc00) 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 32) (o := 5) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_23 : Slice r_21 g_21 (subcubeFast 17 4) 4 := by
  have hc : Lower (varsOf 42) (d 0xffccffcccc00cc00) 4 := carry_of (swaps := [(0,3),(1,3),(2,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 17) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_24 : Slice r_21 g_21 (subcubeFast 9 4) 4 := by
  have hc : Lower (varsOf 50) (d 0xffffcccccccc0000) 4 := carry_of (swaps := [(0,3),(1,3),(2,4),(3,5),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 9) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_25 : Slice r_21 g_21 (subcubeFast 32 3) 4 := by
  have hc : Lower (varsOf 28) (d 0xfff0f000fff0f000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 32) (o := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_26 : Slice r_21 g_21 (subcubeFast 17 2) 4 := by
  have hc : Lower (varsOf 44) (d 0xfff0fff0f000f000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 17) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_27 : Slice r_21 g_21 (subcubeFast 9 2) 4 := by
  have hc : Lower (varsOf 52) (d 0xfffff0f0f0f00000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 9) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_28 : Slice r_21 g_21 (subcubeFast 3 4) 4 := by
  have hc : Lower (varsOf 56) (d 0xffffff00ff000000) 4 := carry_of (swaps := [(0,3),(1,4),(2,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 3) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_29 : Slice r_21 g_21 (subcubeFast 5 2) 4 := by
  have hc : Lower (varsOf 56) (d 0xffffff00ff000000) 4 := carry_of (swaps := [(0,3),(1,4),(2,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 5) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_30 : Slice r_21 g_21 (subcubeFast 6 1) 4 := by
  have hc : Lower (varsOf 56) (d 0xffffff00ff000000) 4 := carry_of (swaps := [(0,3),(1,4),(2,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 6) (o := 1) (by decide +kernel) hc
def S_21 : BT (Option (Nat × Nat)) := btOfList 5 [some (subcubeFast 1 0,10),some (subcubeFast 0 1,9),some (subcubeFast 0 2,8),some (subcubeFast 0 4,8),some (subcubeFast 32 0,8),some (identDom 0 5,9),some (identDom 0 1,9),some (subcubeFast 33 0,7),some (subcubeFast 1 4,7),some (subcubeFast 1 2,7),some (subcubeFast 16 0,8),some (subcubeFast 8 0,8),some (subcubeFast 2 0,8),some (subcubeFast 4 0,8),some (identDom 3 4,9),some (identDom 1 2,8),some (identDom 0 4,8),some (subcubeFast 16 1,6),some (subcubeFast 8 1,6),some (subcubeFast 24 32,4),some (subcubeFast 33 16,4),some (subcubeFast 33 8,4),some (subcubeFast 32 5,4),some (subcubeFast 17 4,4),some (subcubeFast 9 4,4),some (subcubeFast 32 3,4),some (subcubeFast 17 2,4),some (subcubeFast 9 2,4),some (subcubeFast 3 4,4),some (subcubeFast 5 2,4),some (subcubeFast 6 1,4)]
lemma S_21_ok : btAll (fun o => ∀ p, o = some p → Slice r_21 g_21 p.1 p.2) S_21 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_21_0) (forall_cons (fun _ h => by cases h; exact sl_21_1) (forall_cons (fun _ h => by cases h; exact sl_21_2) (forall_cons (fun _ h => by cases h; exact sl_21_3) (forall_cons (fun _ h => by cases h; exact sl_21_4) (forall_cons (fun _ h => by cases h; exact sl_21_5) (forall_cons (fun _ h => by cases h; exact sl_21_6) (forall_cons (fun _ h => by cases h; exact sl_21_7) (forall_cons (fun _ h => by cases h; exact sl_21_8) (forall_cons (fun _ h => by cases h; exact sl_21_9) (forall_cons (fun _ h => by cases h; exact sl_21_10) (forall_cons (fun _ h => by cases h; exact sl_21_11) (forall_cons (fun _ h => by cases h; exact sl_21_12) (forall_cons (fun _ h => by cases h; exact sl_21_13) (forall_cons (fun _ h => by cases h; exact sl_21_14) (forall_cons (fun _ h => by cases h; exact sl_21_15) (forall_cons (fun _ h => by cases h; exact sl_21_16) (forall_cons (fun _ h => by cases h; exact sl_21_17) (forall_cons (fun _ h => by cases h; exact sl_21_18) (forall_cons (fun _ h => by cases h; exact sl_21_19) (forall_cons (fun _ h => by cases h; exact sl_21_20) (forall_cons (fun _ h => by cases h; exact sl_21_21) (forall_cons (fun _ h => by cases h; exact sl_21_22) (forall_cons (fun _ h => by cases h; exact sl_21_23) (forall_cons (fun _ h => by cases h; exact sl_21_24) (forall_cons (fun _ h => by cases h; exact sl_21_25) (forall_cons (fun _ h => by cases h; exact sl_21_26) (forall_cons (fun _ h => by cases h; exact sl_21_27) (forall_cons (fun _ h => by cases h; exact sl_21_28) (forall_cons (fun _ h => by cases h; exact sl_21_29) (forall_cons (fun _ h => by cases h; exact sl_21_30) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))))))))))))))))
set_option maxRecDepth 500000 in
def ps_21 : BT (Option PoolSpec) := btOfList 12 [q 15 [20496,20497,311415],q 15 [20492,20493,86034,115377,86035],q 14 [8196,8197],q 15 [20492,20493,86131,17114,17115],q 15 [20494,20495],q 10 [12296,12297,225499,4870],q 1 [16392,16393,28699,20512,20513,65599],q 0 [16392,16393,28699,20512,20513,65599],q 19 [],q 1 [12296,12297,225499,20496,20497,311415],q 0 [12296,12297,225499,20496,20497,311415],q 15 [16396,16397],q 14 [20484,20485,578083,9030,9031],q 15 [16396,16397,20628,20629,295075],q 15 [20492,20493,86032,86033,295211],q 15 [20496,20497,311308,311309,295031],q 15 [16396,16397,20628,20629,295315],q 10 [12296,12297,225499,4868],q 15 [20496,20497,311415,12596,12597],q 0 [16392,16393,28699,12292,12293,40999],q 1 [16392,16393,28699,12292,12293,40999],q 15 [20492,20493],q 15 [16396,16397,20630,20631,164709],q 1 [12296,12297,225499,16610,16611,799493],q 0 [12296,12297,225499,16610,16611,799493],q 1 [12292,12293,40999,20488,20489,377199],q 0 [12292,12293,40999,20488,20489,377199],q 14 [20488,20489,377199,4468,4469],q 1 [20496,20497,311304,311305,627299],q 0 [20496,20497,311304,311305,627299],q 1 [20492,16497,679944,679945,688799],q 0 [20492,16497,679944,679945,688799],q 0 [16396,16397,151562,163997,151563],q 1 [16396,16397,151562,163997,151563],q 1 [16396,16397,151560,151561,188599],q 0 [16396,16397,151560,151561,188599],q 1 [20488,20489,377199],q 0 [20488,20489,377199],q 1 [20488,20489,377199,16396,16397],q 0 [20488,20489,377199,16396,16397],q 20 [],q 14 [20488,20489,377199,4471],q 1 [20484,20485,578083,16396,16397],q 0 [20484,20485,578083,16396,16397],q 14 [20484,20485,578083,9030],q 15 [16396],q 12 [20488,20489,377199],q 1 [20488,20489,377199,4468,4469],q 0 [20488,20489,377199,4468,4469],q 15 [16398],q 15 [16397],q 0 [20488,20489,16396,164205,16397],q 1 [20488,20489,16396,164205,16397],q 0 [12296,12297,225499,20496,119010],q 1 [12296,12297,225499,20496,119010],q 4 [16392,16393,28699],q 0 [12292,12293,40999,20524,20525,491999],q 2 [20496,20497,311415],q 12 [20496,20497,311415,8502],q 10 [151560,151561,188599],q 14 [8198],q 10 [],q 12 [16392,16393,28699],q 1 [16396,16397,20630,20631,164709],q 0 [16396,16397,20630,20631,164709],q 1 [12296,12297,225499,16610,4869],q 1 [16396,16397,20628,20629,295315],q 0 [16396,16397,20628,20629,295315],q 10 [20628,20629,295315],q 15 [20496,20497,311310,311311],q 1 [16396,20641,16397],q 2 [16396,20641,16397],q 3 [16396,20641,16397],q 12 [16396,20641,16397,20628],q 2 [20492,114933,20493],q 4 [12296,12297,225499,16610],q 12 [12296,12297,225499],q 10 [12296,12297,225499],q 1 [20496,20497,311415],q 0 [20496,20497,311415],q 22 [],q 11 [16392,16393,28699],q 14 [20488,20489,377199,4469],q 10 [8196,8197],q 15 [16396,16397,20629,295075],q 1 [8196,8197,16396,164085,16397],q 0 [8196,8197,16396,164085,16397],q 2 [16396,164085,16397],q 12 [16396,16397,20728],q 15 [20492,20493,86034,115377],q 4 [8196,8197],q 12 [20496,20497,311635],q 13 [20496,20497,311635],q 3 [20496,20497,311415],q 1 [8196,8197,20496,119029,20497],q 0 [8196,8197,20496,119029,20497],q 2 [20496,119029,20497],q 15 [],q 15 [20492,20493,86131,17114],q 0 [8196,8197,20496,20497,311415],q 1 [8196,8197,20496,20497,311415],q 15 [20496,20497,311415,12597],q 12 [20496,20497,311415],q 12 [20496,20497,311415,270644],q 0 [8196,8197,20496,20497,311415,270644],q 15 [20493,86032,86033,295211],q 2 [12296,12297,225499],q 0 [8196,8197,20496,20497,311560,311415],q 13 [20496,20497,311415],q 15 [20496,20497,311415,311308],q 15 [20494],q 14 [8196,8197,20628,409845],q 15 [16396,16397,20628,20629],q 15 [20496,20497,311415,311309],q 15 [16397,20628,20629,295315],q 15 [16396,20641,868355,16397],q 1 [20484,20485,578083,9030,9031],q 0 [20484,20485,578083,9030,9031],q 15 [16396,20641,16397,20628],q 0 [16392,16393,28699],q 1 [16392,16393,28699],q 1 [8196,8197,20492,114933,20493],q 0 [8196,8197,20492,114933,20493],q 15 [12305,20629,294931,294927],q 0 [16388,16389,389499,20488,20489,377199],q 15 [16397,20493,86035,20630],q 15 [16396,164085,16397],q 14 [8196,8197,164085],q 2 [16392,16393,28699],q 14 [8196,8197,20629,295176],q 15 [20492,20493,86032,86033],q 14 [8196,8197,164085,20628],q 1 [20484,20485,578083],q 0 [20484,20485,578083],q 15 [20492,20493,86131,86035],q 14 [8196,8197,20628,409866],q 2 [16397,20629,295159],q 1 [16392,16393,28699,20494,20495],q 0 [16392,16393,28699,20494,20495],q 4 [12296,12297,225499,4320],q 2 [20492,114933,16712],q 13 [16396,16397,167940],q 3 [16396,16397,163997],q 13 [12292,12293,40999],q 12 [16396,16397,20629],q 10 [20488,20489,377199,4470],q 1 [20488,20489,377199,16396,164214],q 2 [20496,119029,12626],q 12 [20493,86032,86033],q 1 [20492,20493,86034,115377,86035],q 0 [20492,20493,86034,115377,86035],q 15 [20493,86019],q 15 [20496,20497,311415,12599],q 15 [20496,20497,311415,12596],q 0 [8196,8197,16396,20641,868616,16397],q 12 [20496,20497,311560,311415],q 15 [16397,20629,294915],q 15 [16397,20629,295159,650],q 4 [16392,16393,28699,4131],q 1 [8196,8197,16396,20641,16397],q 15 [20496,20497,311309,295031],q 10 [20488,20489,377199],q 14 [20488,20489,377199,4468],q 11 [679944,679945,688799],q 0 [8196,8197,12305,20497,311308,340213],q 18 [8196,8197],q 2 [12305,20497,311308,340213],q 12 [20496,20497,344076],q 11 [20496,20497,311415],q 15 [20496,119029,20497],q 15 [20496,119029,20497,311635],q 1 [16396,16397,20628,20629,295075],q 0 [16396,16397,20628,20629,295075],q 4 [16396,16397,295075],q 12 [20496,20497,311309],q 0 [8196,20496,20497,311415,250166],q 14 [8196],q 1 [20492,20493,86131,17114,17115],q 0 [20492,20493,86131,17114,17115],q 11 [20496,20497,295031],q 14 [8197],q 1 [12296,12297,225499,16610,16611],q 0 [12296,12297,225499,16610,16611],q 12 [16396,16397,20628,413857],q 15 [16396,20641,16397,20630],q 23 [],q 1 [16392,16393,28699,4131,12785],q 12 [20492,20493,86131,17114],q 10 [20492,20493,86131],q 0 [12296,12297,225499],q 4 [12296,12297,225499],q 1 [20496,20497,311415,12596,12597],q 0 [20496,20497,311415,12596,12597],q 0 [8196,20496,20497,311543,311415],q 1 [20496,20497,311308,311309,295031],q 0 [20496,20497,311308,311309,295031],q 1 [20492,20493,86032,86033,295211],q 0 [20492,20493,86032,86033,295211],q 4 [86032,86033,295211],q 4 [16396,811012,16397],q 11 [16388,16389,389499],q 15 [20496,20497,311415,311310],q 15 [16396,16397,20631,164709],q 4 [12296,12297,225499,4321],q 1 [12296,12297,225499],q 7 [],q 15 [20499],q 11 [16392,16393,28699,4128],q 15 [20492],q 1 [16392,16393,28699,4128,4129],q 0 [16392,16393,28699,4128,4129],q 15 [20493],q 2 [12296,12297,225499,16610],q 4 [16392,16393,28699,4128],q 1 [16392,16393,28699,20492,20493],q 0 [16392,16393,28699,20492,20493],q 2 [16392,16393,28699,20512],q 15 [16396,16397,20630,20631],q 0 [8196,8197,20492,114933,20493,86280],q 15 [20492,114933,20493],q 12 [20492,20493,86280],q 11 [16392,16393,28699,4130],q 3 [16388,16389,389499],q 1 [16388,16389,389499,8578,8579],q 0 [16388,16389,389499,8578,8579],q 13 [16388,16389,389499],q 4 [16392,16393,28699,4130],q 4 [12296,12297,225499,4322],q 14 [8196,8197,20629,295159],q 0 [12296,12297,225499,16610,4868,230255],q 12 [20496,344077],q 0 [12296,12297,225499,16610,4870,230155],q 0 [],q 1 [],q 1 [20497,311304,311305,627299],q 0 [20497,311304,311305,627299],q 0 [20496,20497,311415,311309,294923],q 0 [20496,20497,311415,311309,294916],q 0 [20496,20497,311415,12597,327691],q 0 [20496,20497,311415,12597,327684],q 0 [20496,20497,311415,8502,8503],q 0 [20492,20493,86131,4825,18202],q 2 [20492,20493,86131],q 0 [20496,20497,311415,4405,14112],q 0 [20496,20497,311415,8501,5928],q 0 [20496,20497,311415,4404,4405],q 12 [20496,20497,311307,311415],q 0 [20492,20493,86021,86131,1888275],q 0 [20496,20497,311301,311415,528396],q 0 [20496,20497,311301,528395,311415],q 0 [20496,20497,311305,626692,311415],q 4 [8502],q 12 [],q 13 [],q 0 [12296,12297,225499,4321,16614],q 24 [],q 1 [16392,16393,28699,4131],q 0 [8197,16396,20641,868616,16397],q 0 [8196,8197,20499,13825,1913096],q 1 [20493,86032,86033,295211],q 0 [20493,86032,86033,295211],q 21 [],q 11 [86032,86033,295211],q 12 [20493,86032],q 13 [20493,86032],q 0 [16396,16397,151558,164989],q 1 [16396,16397,151558,164989],q 12 [16396,16397],q 2 [16396,16397,164989],q 10 [151558,1179657],q 11 [20497,311307,296283],q 2 [],q 0 [4104,20496,20497,311415,8502],q 0 [8196,8197,20492,20493],q 1 [8196,8197,20492,20493],q 15 [20492,20493,86033],q 12 [20492,20493],q 2 [20492,20493],q 0 [16392,16393,28699,12295,34651],q 0 [8196,8197,12306,271795],q 1 [8196,8197,12306,271795],q 11 [8196,8197,271795],q 14 [8196,20493,86263],q 0 [8196,20496,119029,20497,311635],q 0 [20496,20497,311300,311301,528503],q 12 [20496,20497,528503],q 3 [20492,20493,86131],q 12 [20492,20493,86131],q 13 [20492,20493,86131],q 1 [20492,20493,86131,86035],q 4 [8196],q 1 [20496,20497,311309,295031],q 0 [20496,20497,311309,295031],q 0 [4104,20496,20497,311307,311415],q 0 [8196,8197,12305,20497,311308],q 15 [12305,20497,311308],q 2 [12305,20497,311308],q 0 [12293,20496,20497,311415,41268],q 0 [8196,20496,20497,311415],q 12 [20496,20497,311415,310],q 25 [],q 13 [20496,20497,311415,310],q 12 [16397,20629,294920],q 1 [16397,20493,86035,20630],q 0 [16397,20493,86035,20630],q 11 [86035,20630],q 12 [20496,20497,311415,8500],q 0 [16390,16391,20492,20493,86131],q 1 [20492,20493,86131,17114],q 0 [16392,16393,28699,12292,12293],q 12 [16396,16397,1179659],q 10 [151558],q 10 [151558,1179659],q 12 [20492,20493,86035],q 10 [20492,20493],q 13 [20492,20493],q 1 [8197,20496,20497,311415],q 0 [8197,20496,20497,311415],q 0 [20484,16396,164385,16397],q 1 [20484,16396,164385,16397],q 2 [16396,164385,16397],q 4 [8196,311543],q 2 [20488,20489,377199],q 0 [16391,20488,20489,377199,382847],q 11 [20488,20489,377199],q 4 [16388,16389,389499],q 26 [],q 0 [16392,16393,28699,12293,40992],q 0 [20488,20489,377199,16396,164214],q 0 [8196,20496,119029,20497],q 1 [8196,20496,119029,20497],q 3 [20496,119029,20497],q 4 [8196,311635],q 2 [16396,20641,868355,16397],q 2 [20493,86033,295159],q 1 [16396,16397,20631,164709],q 0 [16396,16397,20631,164709],q 12 [16396,16397,20631,164709],q 4 [16396,16397],q 10 [8196],q 10 [151562,167942],q 12 [20496,20497],q 13 [20496,20497],q 10 [8196,8197,271227],q 0 [20492,20493],q 4 [8196,86263,1650],q 0 [8196,20493,86263,87671],q 12 [20493,1650,87671],q 16 [],q 2 [20493,86263,1650],q 3 [20493,86263,1650],q 1 [20488,16396,164205,811013],q 3 [20492,114933,20493],q 0 [4104,20492,114933,20493,86027],q 12 [20492,20493,86027],q 0 [8197,20496,20497,311415,270644],q 1 [8196,20492,114933,20493],q 0 [8196,20492,114933,20493],q 2 [20492,114933,20493,86019],q 12 [20492,20493,86019],q 13 [20492,20493,86019],q 2 [20492,114933,335873],q 3 [20492,114933,335873],q 0 [8196,8197],q 15 [16396,20641,868355],q 30 [],q 2 [16396,20641,868355],q 15 [20496,119029,12627],q 1 [20496,20497],q 0 [20496,20497],q 4 [],q 3 [20492,20493],q 0 [8196,8197,16396,20641,868616],q 15 [16397,20630,20631],q 0 [8196,16398,250745,21816,17725],q 1 [16397,20628,20629,295315],q 0 [16397,20628,20629,295315],q 11 [20628,20629,295315],q 0 [16392,16393,28699,20492,114693],q 1 [20496,20497,311415,12599],q 0 [20496,20497,311415,12599],q 1 [8196,20496,20497,311415],q 0 [4104,16397,20629,295159,8842],q 12 [12305,20629,294931],q 0 [16397,20493,86032],q 1 [16397,20493,86032],q 1 [16396,16397,20628,20629],q 0 [16396,16397,20628,20629],q 10 [20628,20629],q 15 [20497,20494,17125],q 11 [8196,8197],q 0 [8196,8197,16398,20493,86280],q 0 [20492,20493,86026,116701,86027],q 3 [20492,20493,116701],q 15 [12305,20497,20493],q 0 [16392,16393,28699,4128,12497],q 1 [20496,20497,311415,311309],q 0 [20496,20497,311415,311309],q 16 [8196,8197],q 15 [20493,86019,86033],q 12 [20493,86019],q 2 [20493,86019],q 15 [20492,20493,86035],q 1 [8196,8197],q 15 [16397,20493,86165],q 12 [20496,20497,311299,311415],q 13 [20496,20497,311299,311415],q 15 [16397,20629,294935],q 0 [8197,20496,20497,311560,311415],q 15 [20492,20493,86032],q 0 [16392,16393,28699,20492],q 1 [16392,16393,28699,20492],q 1 [16392,16393,28699,4129],q 13 [16396,16397],q 14 [8197,20629,295176],q 3 [12292,12293,40999],q 14 [8197,20628,409866],q 15 [12305,20629,294931],q 0 [8196,8197,16396,164085],q 1 [8196,8197,16396,164085],q 15 [16396,164085],q 2 [16396,164085],q 0 [8196,20494,21221,86263],q 0 [8196,8197,16397,20493,86280],q 4 [8196,8197,86280],q 1 [12305,20629,294931,294927],q 0 [12305,20629,294931,294927],q 4 [12305,294931,294927],q 1 [20496,20497,311415,12597],q 0 [20496,20497,311415,12597],q 1 [8196,16396,164085,16397],q 0 [8196,16396,164085,16397],q 3 [16396,164085,16397],q 13 [12305,20629,294931],q 11 [20496,20497,311415,310],q 15 [16397,20628,20629],q 15 [16397,20628,151955],q 14 [8196,164085,20630],q 0 [16388,16389,389499,8578],q 1 [16388,16389,389499,8578],q 2 [20496,119029,344065,20497],q 12 [20496,344065,20497],q 13 [20496,344065,20497],q 0 [8196,8197,20493,86280],q 1 [8196,8197,20493,86280],q 12 [20493,86280],q 11 [8196,335873],q 15 [12305,20499,20630],q 15 [16397,20493,86035],q 12 [16396,20641,16397],q 0 [8196,8197,16396,20641,16397],q 15 [16396,20641,16397],q 3 [],q 11 [],q 1 [20488,20489,377199,16758],q 0 [20488,20489,377199,16758],q 15 [16398,20497,311311],q 1 [20488,20489,377199,4468],q 0 [20488,20489,377199,4468],q 15 [16396,16397,20630],q 14 [8196,8197,20630],q 15 [12305,20497,20494],q 15 [16398,20493,86019],q 15 [16397,20494,20498],q 0 [16392,16393,28699,20487,13553],q 3 [16396,16397],q 15 [12305,20497,20628],q 0 [16392,16393,28699,20486,20487],q 15 [16397,20493,86019],q 17 [8196,8197],q 4 [8196,8197,86019],q 0 [16392,16393,28699,20514,20515],q 0 [8196,16398,250745,21817,1380371],q 15 [16396,16397,20631],q 14 [8196,8197,20631],q 1 [8196,8197,20497,311560],q 0 [8196,8197,20497,311560],q 0 [16392,16393,28699,20484,12833],q 1 [20496,20497,311415,12596],q 0 [20496,20497,311415,12596],q 12 [20496,20497,311415,12596],q 1 [20496,20497,311415,311310],q 0 [20496,20497,311415,311310],q 14 [],q 10 [8196,8197,311560],q 15 [16397,20493,20630],q 15 [20498,14225,20494],q 10 [8197],q 15 [16398,20499,13825],q 4 [8196,335891],q 0 [8196,8197,20492,20493,86280],q 1 [8196,8197,20496,20497],q 0 [8196,8197,20496,20497],q 2 [20496,20497],q 15 [20496,20497,311310],q 15 [20492,114933,16713],q 0 [20496,20497,311415,4406,312631],q 0 [20485,16396,20641,16397,577684],q 0 [20491,16396,20641,16397],q 3 [16396,20641,868355,16397],q 15 [12305,20497,20630],q 15 [20493,86019,86035],q 1 [16396,20641,16397,20630],q 1 [16392,16393,28699,20514],q 0 [16392,16393,28699,20514],q 12 [16396],q 0 [4106,20496,20497,311415,4404],q 11 [8196,8197,86280],q 0 [16396,16397],q 1 [16396,16397],q 2 [16396,16397],q 14 [8196,20629,295159],q 0 [12294,20496,20497,311415],q 1 [12294,20496,20497,311415],q 3 [20496,20497,311415,310],q 1 [8197,16396,20641,16397],q 4 [8196,8197,311560],q 1 [20492,20493],q 2 [16397,20629,294923],q 0 [16397,20629,294923,294919],q 1 [16397,20629,294923,294919],q 1 [20496,20497,311415,311308],q 0 [20496,20497,311415,311308],q 12 [20496,20497,311415,311308],q 0 [8196,16396,20641,868599,16397],q 15 [16398,21369,20497],q 0 [16388,16389,389499],q 0 [16388,16389,389499,20488,373122],q 10 [20493,86019],q 14 [8196,20628,409845],q 12 [16396,16397,20628],q 0 [12298,20496,20497,311415,316591],q 1 [20492,20493,86034,115377],q 0 [20492,20493,86034,115377],q 0 [12298,20496,20497,312495,311415],q 12 [12306,13749,2129939],q 0 [16392,16393,28699,20484,20485],q 12 [20496,20497,119842],q 0 [8196,20496,20497,311543,119842],q 0 [8196,8197,16396,16397],q 1 [8196,8197,16396,16397],q 15 [16396,16397,20629],q 14 [8196,8197,20629],q 12 [20492,20493,86019,86131],q 1 [16390,20492,20493,86131],q 3 [20492,20493,86019,86131],q 13 [20492,20493,86019,86131],q 0 [8196,20499,13825,1913079],q 1 [20488,20489,377199,16396],q 0 [20488,20489,377199,16396],q 0 [8196,8197,20493,86033,295176],q 15 [12305,20498,153491],q 0 [16392,16393,28699,20512,12349],q 0 [12296,12297,16388,221561,16389],q 2 [12296,12297,221561],q 14 [8196,164085],q 5 [],q 4 [8198],q 1 [8198,20496,20497,311415],q 0 [8198,20496,20497,311415],q 0 [8196,8197,20493,86034,271027],q 2 [20493,86034],q 15 [12306,20497,312755],q 14 [20496,20497,311415],q 15 [20497,20494,311311],q 0 [8196,8197,16397,20629,295159],q 15 [16397,20629,295159],q 0 [16388,20488,20489,377199,385398],q 15 [20497,311310,311311],q 1 [20488,20489,377199,16397],q 0 [20488,20489,377199,16397],q 14 [8196,164085,20628],q 0 [8196,8197,20493,86033,295159],q 15 [20497,311308,311309],q 12 [20497,311308],q 13 [20497,311308],q 1 [16396,20641,16397,20628],q 0 [16396,20641,16397,20628],q 1 [8196,16396,20641,16397],q 1 [8196,8197,20492,114933],q 0 [8196,8197,20492,114933],q 2 [20492,114933],q 15 [20492,114933,16714],q 1 [20488,20489,377199,4469],q 0 [20488,20489,377199,4469],q 0 [8196,16396,20641,868599],q 4 [16396,868355,16397],q 0 [4106,20496,20497,312863,311415],q 12 [16396,20641,868355],q 13 [16396,20641,868355],q 0 [8196,16397,20629,295159],q 2 [16397,20629,294915],q 3 [16397,20629,294915],q 0 [16396,20641,16397],q 0 [20496,20497,311415,4405,10018],q 0 [8196,8197,20497,311308,340213],q 2 [20497,311308,340213],q 0 [8196,12305,20497,311543,13344],q 18 [],q 12 [16397,20629,294915],q 1 [16396,16397,20629,295075],q 0 [16396,16397,20629,295075],q 2 [20496,20497,311299,311415],q 0 [20496,20497,311415,4404],q 3 [20496,20497,311299,311415],q 1 [20496,20497,311415,4404],q 1 [16396,16397,20630,20631],q 0 [16396,16397,20630,20631],q 10 [20630,20631],q 1 [8196,8197,20496,119029],q 0 [8196,8197,20496,119029],q 2 [20496,119029],q 15 [20496,119029,12624],q 12 [20496],q 0 [16392,16393,28699,20492,114721],q 0 [8196,16629,20493,86034,1663667],q 17 [8196],q 0 [12293,20496,20497,311415,311336],q 15 [16398,21369,20499],q 15 [16397,20495,17129],q 1 [16392,16393,28699,20512],q 0 [16392,16393,28699,20512],q 12 [20492,20493,86131,17112],q 13 [20492,20493,86131,17112],q 15 [16397,20629],q 10 [20493,86027,86023],q 0 [16396,16397,151556,151557,352419],q 10 [151556,151557],q 12 [16396,16397,352419],q 0 [20496,20497,311300,311415],q 4 [311299,311300],q 1 [20496,20497,311300,311415],q 0 [16392,16393,28699,20487,34035],q 4 [8197],q 1 [8198,16396,20641,16397],q 1 [16396,16397,151562,163997],q 0 [16396,16397,151562,163997],q 10 [151562],q 10 [151562,167940],q 14 [4106,20629,296479],q 10 [8198],q 4 [8196,344077],q 1 [20492,20493,86032,86033],q 0 [20492,20493,86032,86033],q 4 [86032,86033],q 0 [16392,16393,28699,4130,12789],q 0 [8198,20496,20497,311304,311415],q 12 [20496,20497,311304,311415],q 1 [20496,20497,311310,311311],q 0 [20496,20497,311310,311311],q 4 [311310,311311],q 0 [4106,20496,20497,311415,1601846],q 0 [16392,16393,28699,20494],q 1 [16392,16393,28699,20494],q 15 [16396,16397,20628],q 14 [8198,20628,410957],q 0 [16390,16391,20488,20489,377199],q 3 [20493,86019],q 11 [8198,20497,311304],q 2 [20496,20497,311415,310],q 1 [16392,16393,28699,12320],q 0 [16392,16393,28699,12320],q 1 [12296,12297,225499,16610],q 0 [12296,12297,225499,16610],q 1 [16392,16393,28699,4128],q 1 [16392,16393,28699,20493],q 0 [16392,16393,28699,20493],q 1 [12296,12297,225499,20499],q 0 [12296,12297,225499,20499],q 0 [16392,16393,28699,4129],q 15 [20497,20493,86035],q 4 [311300,310],q 0 [8196,20492,20493,86263],q 4 [86019],q 4 [12292,12293,40999],q 14 [20629],q 12 [16398,20499,13825],q 0 [12296,12297,225499,16608,231575],q 0 [16392,16393,28699,12323,2252805],q 0 [16392,16393,28699,12320,12321],q 14 [16392,16393,28699],q 0 [12296,12297,225499,16611,798726],q 3 [20484,20485,578083],q 13 [20484,20485,578083],q 1 [20484,20485,578083,13124],q 0 [20484,20485,578083,13124],q 11 [20484,20485,578083],q 1 [20484,20485,578083,9030],q 0 [20484,20485,578083,9030],q 0 [16392,16393,28699,20512,20513],q 14 [20488,20489,377199],q 1 [20488,16396,164205,16397],q 0 [20488,16396,164205,16397],q 3 [16396,164205,16397],q 0 [16392,16393,28699,12294,34063],q 0 [8196,8197,16397,20629,295176],q 0 [12296,12297,225499,16390,16391],q 14 [8196,8197,20628],q 0 [16392,16393,28699,20485,577568],q 0 [16392,16393,28699,20486,34811],q 10 [12292,12293,40999],q 0 [12292,12293,40999],q 0 [12292,12293,40999,16392,24622],q 0 [12296,12297,225499,20496,118790],q 0 [16392,16393,28699,20493,86048],q 0 [16392,16393,28699,20494,33511],q 0 [12296,12297,20484,557273,20485],q 3 [20484,557273,20485],q 0 [8196,12305,20497,311308,340213],q 18 [8196],q 12 [12305,20497,311308],q 27 [],q 13 [12305,20497,311308],q 0 [12292,12293,20497,311336],q 1 [12292,12293,20497,311336],q 11 [20497,311336],q 13 [16396,20641,16397],q 0 [12292,12293,20488,20489,377199],q 0 [16392,16393,20492,114713,20493],q 3 [20492,114713,20493],q 0 [12292,12293,20496,20497,311415],q 4 [12292,12293,311336],q 10 [12292,12293,311336],q 0 [12293,20488,20489,377199,41332],q 12 [20492,20493,86131,86032],q 13 [20492,20493,86131,86032],q 4 [679944,679945,688799],q 17 [],q 0 [12294,20488,20489,377199,382223],q 1 [20484,20485,578083,16398],q 0 [20484,20485,578083,16398],q 0 [8196,8197,20494,21221,86280],q 15 [12305,20498,22417],q 1 [20484,20485,578083,16396],q 0 [20484,20485,578083,16396],q 10 [20484,20485,578083],q 1 [20484,20485,578083,16397],q 0 [20484,20485,578083,16397],q 1 [20488,20489,377199,4471],q 0 [20488,20489,377199,4471],q 1 [20488,20489,377199,16398],q 0 [20488,20489,377199,16398],q 0 [20488,20489,377199,12660,12661],q 0 [20488,20489,377199,16758,16759],q 0 [20488,20489,377199,12306,382387],q 1 [20488,20489,16396,164205],q 0 [20488,20489,16396,164205],q 4 [16396],q 11 [20488,20489],q 10 [20488,20489],q 12 [12305,20497,20628],q 0 [20485,16396,16397,577687,166149],q 2 [16396,16397,166149],q 0 [20487,16396,20641,869619,16397],q 0 [16396,20641,16397,20628,409609],q 1 [16397,151560,151561,188599],q 0 [16397,151560,151561,188599],q 8 [],q 11 [151560,151561,188599],q 0 [20497,311308,311309,294916],q 11 [20497,294916],q 10 [311308,311309,294916],q 2 [20493,86027],q 13 [20493],q 0 [20497,311300,311310,524917],q 11 [20497,311300],q 12 [20497,311310],q 10 [311309],q 12 [20497,311309,294931],q 13 [20497,311309,294931],q 0 [20493,86020,86021,1888272],q 12 [20493,1888272],q 11 [86020,86021,1888272],q 1 [20493,86033,294916],q 11 [86019,86033,294916],q 13 [20493,86019],q 1 [20493,86027,17765],q 10 [20493,86019,86027],q 1 [20493,86021,1888275],q 1 [20493,86021,1888267],q 11 [86019,86021,1888267],q 12 [20493,86019,86027],q 1 [20493,86020,18353],q 10 [20493,86019,86020],q 0 [20496,20497,311415,8502],q 0 [20492,20493,86131],q 0 [20492,20493,86131,17114],q 0 [20496,20497,311415,4407],q 0 [20496,20497,311307,311415],q 0 [20496,20497,311302,311415],q 4 [311302,311303],q 0 [20496,20497,311302,311303],q 0 [20492,20493,86021,1888275],q 0 [20496,20497,311301,311415],q 0 [20492,20493,86021,1888267],q 4 [86021,1888267],q 4 [8198,86024],q 1 [8198,16396,16397],q 0 [8198,16396,16397],q 14 [8198,20628],q 0 [8198,13645,20497,313668],q 1 [16396,16397,20631],q 0 [16396,16397,20631],q 12 [16396,16397,20631],q 14 [8196,20631],q 3 [20493,86021,1888275],q 0 [20493,86021,86027,1888275],q 4 [16396,868355],q 3 [16396,20641,868355],q 0 [8198],q 11 [20497],q 0 [8198,13645,20497,311308],q 18 [8198],q 1 [16397,20495,17129],q 0 [16397,20495,17129],q 11 [17129],q 0 [16390,20492,20493,86131],q 0 [8197,20494,21221,86280],q 3 [20497],q 11 [20497,311304],q 1 [8198,20497,311304],q 0 [8198,20497,311304],q 4 [14225],q 0 [12292,20496,20497,311415],q 0 [8197,20493,86033,295176],q 12 [20493],q 2 [20493,86033],q 3 [20484,12833],q 1 [20484,12833,1056779],q 2 [20493,86032],q 0 [8197,20493,86032,303370],q 17 [8197],q 0 [16390,16391,20492,116605],q 12 [20492,116605],q 0 [8196,20493,86263],q 12 [20493,1650],q 13 [20493,1650],q 11 [8196,86263,1650],q 12 [20492,20493,86032],q 13 [20492,20493,86032],q 4 [16390,86032],q 1 [8197,20497,311560],q 0 [8197,20497,311560],q 0 [8197,20493,86280],q 1 [8197,20493,86280],q 2 [20493],q 13 [20493,86280],q 3 [20493],q 0 [8196,8197,20493],q 11 [8196,8197,86019],q 0 [20487,16396,20641,869619],q 2 [16396,20641],q 3 [16396,20641],q 0 [8197,20492,20493],q 1 [8197,20492,20493],q 12 [20493,86035],q 13 [20493,86035],q 10 [8197,271227],q 0 [8197],q 1 [8197],q 0 [12293,16426,22873,20499],q 2 [22873,20499],q 4 [12293,16426],q 0 [8197,12306,271795],q 1 [8197,12306,271795],q 11 [8197,271795],q 0 [8197,16397,20629,295176],q 12 [16397,20629],q 2 [16397,20629],q 13 [16397,20629],q 3 [16397,20629],q 15 [20494,20498],q 0 [16396,20641,868356,16397],q 0 [8197,16397,20493,86280],q 4 [8197,86280],q 14 [8197,20631],q 11 [8197],q 1 [8197,16396,16397],q 0 [8197,16396,16397],q 14 [8197,20628],q 0 [8197,16396,20641,868616],q 0 [8197,12554,20497,313699],q 1 [20499,13825],q 0 [8196],q 11 [20499,1912835],q 12 [20499,13825,1912835],q 13 [20499,13825,1912835],q 1 [20494,21221],q 11 [86019],q 12 [20494,21221,86019],q 13 [20494,21221,86019],q 0 [8196,16398,250745,20493],q 12 [16398,20493],q 13 [16398,20493],q 11 [8196],q 2 [20494,21221],q 0 [4104,20494,21221,86027],q 12 [20494,21221,86027],q 0 [20494,21221],q 4 [8196,86263],q 0 [8197,20492,20493,86280],q 12 [20497,311311],q 13 [20497,311311],q 1 [20497,311310,311311],q 0 [20493],q 1 [20493],q 12 [20493,86033],q 0 [8196,20493,86033,295159],q 13 [20493,86033],q 2 [16397,20493],q 11 [8197,86280],q 10 [21369],q 1 [20492,20493,86033],q 0 [20492,20493,86033],q 0 [8196,20492,20493],q 1 [8196,20492,20493],q 4 [86033],q 2 [20493,86035],q 10 [20493],q 1 [20497,311308,311309],q 0 [20497,311308,311309],q 10 [311308,311309],q 0 [4106,20493,87583],q 1 [4106,20493,87583],q 12 [20493,87583],q 3 [20493,87583],q 1 [16397,20630,20631],q 0 [12293,16426,20496,118797],q 2 [20496,118797],q 3 [20493,86023],q 12 [20493,86027],q 11 [4106,87583],q 4 [4106,87583],q 11 [20498],q 1 [20498,14225,20494],q 1 [20499],q 0 [20499],q 12 [16398,20499],q 10 [8196,250745],q 4 [8196,1913079],q 0 [20497],q 1 [20497],q 1 [8196,20493,86263],q 2 [20493,86263],q 3 [20493,86263],q 0 [8196,20493,86263,18035],q 11 [8196,86263],q 0 [8196,20493,86263,18034],q 1 [20493,86033,294923],q 11 [86019,86033,294923],q 1 [16396,16397,20629],q 0 [16396,16397,20629],q 0 [8196,16396,16397],q 1 [8196,16396,16397],q 10 [20629],q 14 [8196,20629],q 10 [8197,311560],q 0 [8197,12305,20497,311308],q 18 [8197],q 17 [8198],q 4 [8198,86019],q 1 [20492,20493,86035],q 0 [16392,16393,28699,20515],q 0 [8197,16650,20493,86032],q 11 [8196,868599],q 10 [8196,868599],q 1 [8196,8197,16397],q 0 [8196,8197,16397],q 15 [16397,20628],q 12 [16397],q 2 [16397],q 10 [8196,311543],q 1 [20494],q 0 [16390,13497,20497,313704],q 12 [20497,313704],q 0 [20492,20493,86020,86021],q 4 [86020,86021],q 0 [8196,16629],q 0 [16392,16393,20492,114713],q 3 [20492,114713],q 15 [12305,20499],q 0 [8196,8197,20493,86035],q 15 [20493,86035],q 0 [8197,16396,20641,16397],q 0 [4104,20493,86027],q 1 [16397],q 0 [16397],q 3 [16397],q 12 [16397,20628],q 1 [16396,16397,20630],q 14 [8196,20630],q 3 [20493,88303],q 0 [16397,20629,294916,294920],q 10 [20629,294916,294920],q 11 [20629,294916,294920],q 12 [20499,13825],q 0 [8196,8197,20499,13825],q 15 [20499,13825],q 1 [8196,16396,164085],q 0 [8196,16396,164085],q 3 [16396,164085],q 13 [16396],q 1 [8196,16398,250745],q 0 [8196,16398,250745],q 0 [8196,16398,250745,21818],q 1 [8196,8197,20497],q 0 [8196,8197,20497],q 2 [20497],q 0 [8196,8197,20497,311310],q 15 [20497,311310],q 2 [20497,311310],q 10 [20494],q 1 [16397,20494,20498],q 0 [8196,8197,20496,119050],q 15 [20496,119050],q 12 [20496,119050],q 2 [12305,20497,20628],q 1 [12306,20497,312755],q 0 [12306,20497,312755],q 4 [12306,312755],q 12 [12306,20497,312755],q 13 [12306,20497,312755],q 3 [20497,311310],q 0 [8198,20497,311310,1389173],q 11 [16388,16389],q 4 [16388,16389],q 0 [16388,16389,20494,20495],q 10 [20494,20495],q 2 [20494,20495],q 0 [8196,12533,20497,312736],q 12 [20497,312736],q 13 [20497,312736],q 1 [8196,20497,311543],q 0 [8196,20497,311543],q 0 [20497,311310],q 1 [20497,311310],q 0 [16398],q 1 [16398],q 10 [12293,28712],q 1 [16397,20493,86035],q 0 [8196,8197,20494,20495],q 12 [20494,20495],q 0 [8196,8197,20492,16497],q 12 [20492,16497],q 15 [20492,16497],q 2 [20492,16497],q 10 [12298,312495],q 13 [20497],q 3 [20497,312495],q 3 [20497,311300,12801],q 12 [12305,20497],q 0 [8196,8197,12305,20497],q 15 [12305,20497],q 2 [12305,20497],q 0 [20492,20493,86025,94212],q 4 [86025,94212],q 13 [20484,12833],q 12 [20497],q 11 [8196,1368065],q 3 [16398,250745,1368065],q 2 [16398,250745,1368065],q 10 [8196,250745,1368065],q 12 [16398,1368065],q 12 [20496,12405],q 0 [8196,8197,20496,12405],q 15 [20496,12405],q 2 [20496,12405],q 10 [13825],q 14 [8198,20631],q 10 [151558,151559],q 0 [16396,16397,151558,151559],q 1 [8196,8197,20499],q 0 [8196,8197,20499],q 2 [20499],q 15 [16398,20499],q 1 [16398,20493],q 0 [20493,86033],q 1 [20493,86033],q 11 [86033],q 4 [16397],q 0 [20496,20497,311415,4405],q 12 [16397,20494],q 15 [16397,20494],q 14 [8198,20629],q 0 [8197,20493,86034,271027],q 11 [20499],q 1 [16398,20499,13825],q 0 [16398,20499,13825],q 4 [16398],q 29 [],q 0 [20492,20493,86021,1888272],q 4 [86021,1888272],q 0 [8196,12533,21921,1548307],q 12 [21921,1548307],q 13 [21921,1548307],q 11 [8196,21921,1548307],q 0 [16396,20641,16397,20630],q 0 [8196,20497,311543,13344],q 0 [16398,20493],q 0 [8196,16398,20493,86263],q 0 [20496,20497,311301,528503],q 1 [8196,12533,16398],q 0 [8196,8197,20497,311308],q 15 [20497,311308],q 2 [20497,311308],q 2 [20492,20493,86019],q 4 [8196,86019],q 10 [20492,20493,86019],q 0 [20492,20493,86022,117129],q 1 [12305,20499,20630],q 1 [12305,20629,294931],q 12 [20498,14225],q 0 [8196,8197,20498,14225],q 15 [20498,14225],q 2 [20498,14225],q 0 [20491,16396,20641],q 1 [16396,20641],q 11 [868355],q 10 [868355],q 0 [8196,20497,311310,250485],q 0 [8196,8197,16398],q 1 [8196,8197,16398],q 15 [16398,20497],q 2 [16398],q 0 [20492,20493,86020],q 1 [20492,20493,86020],q 3 [20492,20493,86019],q 4 [86019,86020],q 1 [8196,8197,20493],q 15 [20493,20497],q 1 [16397,20628,151955],q 13 [16397],q 1 [12305,20497,20494],q 12 [16398,21369],q 0 [8196,8197,16398,21369],q 15 [16398,21369],q 2 [16398,21369],q 11 [8198],q 0 [8197,20499,13825,1913096],q 15 [16397,20493],q 13 [20499,13825],q 4 [12305],q 4 [16394,88303],q 0 [16394,20492,20493,88303],q 15 [16397,20630],q 1 [8196,20492,114933],q 0 [8196,20492,114933],q 12 [20492],q 3 [20492,114933],q 13 [20492],q 0 [8196,20492,114933,16714],q 4 [8196,16714],q 0 [8196,8197,20494],q 1 [8196,8197,20494],q 15 [20497,20494],q 2 [20494],q 12 [12306,1664435],q 0 [16392,16393,28699,12292],q 0 [16394,20493,88303],q 10 [20493,88303,86019],q 0 [8196,12306,251313,21943],q 4 [4106,312863],q 0 [8196,8197,20493,86033],q 15 [20493,86033],q 4 [8197,86019],q 0 [8196,8197,16397,20629],q 0 [8196,20496,119029,12627],q 4 [8196,12627],q 0 [8196,8197,16397,20630],q 12 [16397,20630],q 2 [16397,20630],q 0 [8196,8197,16398,20493],q 15 [16398,20493],q 2 [16398,20493],q 1 [12305,20497,20630],q 0 [20484,20485,16396,16397],q 10 [20484,20485],q 14 [20484,20485],q 0 [20493,86033,294919],q 0 [20493,86027,86033,294919],q 3 [20493,86033,294919],q 4 [86033,294919],q 11 [86033,294919],q 0 [8197,16398,20493,86280],q 12 [12306,271795],q 2 [12306],q 0 [8196,16398,250745,17721],q 12 [16398,17721],q 13 [20493,86023],q 0 [4104,20493,86027,86023],q 0 [16396,20641],q 0 [8196,16396,20641,16397],q 1 [20492,20493,86032],q 0 [20492,20493,86032],q 4 [86032],q 0 [12292,12293,20496,20497],q 11 [20496,20497],q 4 [12292,12293],q 1 [12305,20498,22417],q 0 [12305,20498,22417],q 11 [20498,22417],q 0 [8198,16396,20641,16397],q 15 [20492,114933],q 0 [20492,16497,679942,679943],q 11 [679942,679943],q 4 [679942,679943],q 14 [8197,20630],q 4 [4104,86027],q 0 [4104,20492,20493,86027],q 10 [20492,20493,86027],q 4 [8197,311560],q 12 [20491,13929],q 2 [20491,13929],q 0 [16390,16391],q 0 [16390,16391,20491,13929],q 3 [16390,16391],q 4 [16390,16391],q 2 [12297],q 11 [16390,86035],q 10 [20493,86027],q 0 [20493,86035],q 1 [20493,86035],q 1 [12305,20497,311308],q 0 [12305,20497,311308],q 0 [8196,12305,20497,311308],q 4 [12305,311308],q 0 [8196,16397,20493,86263],q 1 [16397,20493],q 0 [16392,16393,12292,12293],q 11 [16392,16393],q 10 [12292,12293],q 2 [16392,16393],q 3 [12292,12293],q 0 [8197,16397,20629,294916],q 3 [16397,20629,294916],q 0 [20484,16396,164385],q 1 [20484,16396,164385],q 2 [16396,164385],q 0 [16392,16393,28699,20513],q 1 [12305,20497,20628],q 0 [12305,20497,20628],q 11 [20497,20628],q 1 [16398,21369,20497],q 0 [16398,21369,20497],q 0 [8196,8197,20496,12407],q 12 [20496,12407],q 15 [20496,12407],q 2 [20496,12407],q 1 [20497,20494,311311],q 0 [8198,20497,311308,341325],q 3 [20497,311308],q 1 [16397,20493,86165],q 0 [16397,20493,86165],q 1 [8196],q 11 [86165],q 16 [8196],q 11 [86019,86033],q 1 [12305,20498,153491],q 0 [12305,20498,153491],q 11 [20498,153491],q 1 [16397,20629],q 11 [20629,294915],q 10 [20629,294915],q 13 [16397,20629,294915],q 1 [8197,20496,20497],q 0 [8197,20496,20497],q 0 [20486,20487,16396,16397],q 10 [20486,20487],q 14 [20486,20487],q 1 [8196,20496,119029],q 0 [8196,20496,119029],q 0 [8196,20496,119029,12624],q 4 [8196,12624],q 13 [20496],q 1 [16397,20493,20630],q 0 [12296,12297,20496,118790],q 11 [20496,118790],q 3 [20496,118790],q 10 [12296,12297],q 4 [12296,12297],q 0 [16397,20629],q 11 [20629],q 0 [8198,20492,20493],q 1 [8198,20492,20493],q 12 [16396,20641],q 0 [8196,8197,16396,20641],q 15 [16396,20641],q 2 [20499,13825],q 0 [4104,20499,13825,1912843],q 12 [20499,13825,1912843],q 1 [16397,20629,294923],q 0 [16397,20629,294923],q 0 [4104,16397,20629,294923],q 11 [20629,294923],q 10 [20629,294923],q 12 [16397,20629,294923],q 3 [12305,20497,311308],q 0 [8198,12305,20497,311308],q 0 [4106,20494,21221,87583],q 14 [8198,20630],q 3 [12305,20497,20628],q 2 [20493,20497],q 0 [16394,20493,86020,2017517],q 13 [20493,86020],q 0 [16397,20629,294916],q 1 [16397,20629,294916],q 10 [20629,294915,294916],q 11 [20629,294915,294916],q 12 [20494,21221],q 0 [8196,8197,20494,21221],q 15 [20494,21221],q 0 [16390,20493,86027,1414329],q 0 [8196,16398,250745,21816],q 2 [16398,250745],q 12 [16398],q 3 [16398,250745],q 13 [16398],q 0 [16392,16393,28699,4131],q 1 [16397,20628,20629],q 0 [16397,20628,20629],q 11 [20628,20629],q 0 [8196,16398,250745,21817],q 12 [20497,311336],q 2 [16393,20497],q 1 [16398,21369,20499],q 0 [16398,21369,20499],q 12 [16398,21369,20499],q 1 [16397,20629,294935],q 1 [12305,20497,20493],q 0 [12305,20497,20493],q 1 [16398,20497,311311],q 0 [8198,20494,21221,86024],q 0 [8196,20493,86263,18033],q 0 [8196,20492,114933,16713],q 4 [8196,16713],q 12 [12296,12297],q 2 [12296,12297],q 0 [12296,12297,20486,20487],q 11 [20486,20487],q 3 [20486,20487],q 0 [16392,16393,28699,12321],q 0 [12298,12299,20496,119981],q 3 [20496,119981],q 10 [12298,12299],q 1 [8198],q 1 [4104,20493,86027],q 0 [4106,16397,20629,296479],q 28 [],q 3 [16397,20629,294919],q 1 [20497,20494,17125],q 0 [20497,20494,17125],q 1 [12293,16393,28712],q 0 [12293,16393,28712],q 2 [16393],q 12 [16393,28712],q 3 [12293],q 13 [12293,28712],q 11 [16393,28712],q 0 [16392,20505,12293,2543656],q 11 [16392,20505,2543656],q 2 [16392,20505],q 0 [16393,20484,12833,29704],q 0 [8198,16398,1389433],q 1 [8198,16398,1389433],q 10 [8198,1389433],q 0 [16392,16393,28699,20484],q 0 [16396,16397,20629,294923],q 14 [20629,294923],q 1 [8196,20496,20497],q 0 [8196,20496,20497],q 3 [20496,20497],q 1 [20496,20497,311310],q 0 [20496,20497,311310],q 0 [8198,17741],q 1 [4106,20497,312863],q 0 [4106,20497,312863],q 10 [4106,312863],q 2 [12305,20497,20493],q 0 [16396,16397,151556,151557],q 0 [4106,20492,20493,87583],q 0 [4106,16396,20641,869919],q 1 [8198,20496,20497],q 0 [8198,20496,20497],q 0 [12293,20496,20497,311415],q 15 [16397,20631],q 0 [16392,16393,28699,20485],q 0 [16397,20493],q 0 [20493,86032],q 1 [20493,86032],q 0 [8198,20493,86024],q 12 [16398,17273],q 0 [8196,8197,16398,17273],q 15 [16398,17273],q 2 [16398,17273],q 0 [16389,20499,13825,390988],q 10 [13825,390988],q 4 [16389,390988],q 16 [8198],q 0 [20493,86020,86021,1888264],q 12 [20493,1888264],q 11 [86020,86021,1888264],q 3 [16397,20629,295159],q 0 [12292,20488,372773,20489],q 4 [12292],q 12 [20488,20489],q 3 [12292,372773],q 12 [20492,20493,86024],q 10 [20492,20493,86024],q 0 [8198,20492,20493,86024],q 10 [20493,86024],q 12 [20493,86024],q 0 [4106,20493,86033,296479],q 10 [12298,390319],q 0 [4106,20499,13825,1914399],q 10 [20491,13929],q 3 [16388,20857],q 0 [8198,20499,13825,1912840],q 1 [16390,20493,86035],q 12 [20493,86019,86035],q 13 [20493,86019,86035],q 0 [16392,16393,28699,12323],q 0 [16392,16393,28699,12293],q 0 [12296,12297,225499,16390],q 2 [20489],q 1 [20493,86025,94212],q 11 [86019,86025,94212],q 0 [16392,16393,28699,20486],q 0 [16388,16389,389499,20491],q 3 [16396,164205],q 0 [12296,12297,16388,221561],q 3 [16388,221561],q 0 [12293,20497,311336],q 1 [12293,20497,311336],q 0 [12296,12297,16390,16391],q 11 [16390,16391],q 0 [12296,12297,20484,557273],q 11 [20484],q 3 [20484,557273],q 11 [20488,16749],q 0 [12292,12293,20488,16749],q 2 [20488,16749],q 13 [12292,12293],q 0 [12293,20498,22417,311336],q 2 [20498,22417],q 12 [20492,114697],q 2 [20492,114697],q 0 [16390,16391,20492,114697],q 0 [20492,20493,86033,294923],q 4 [86033,294923],q 0 [12292,12293,20488,20489],q 2 [20488,20489],q 11 [20491,18025],q 0 [12292,12293],q 0 [12292,12293,20491,18025],q 2 [20491,18025],q 0 [12292,12293,20496,118793],q 11 [20496,118793],q 2 [20496,118793],q 1 [20488,16396,164205],q 0 [20488,16396,164205],q 11 [20488],q 10 [20488],q 16 [8197],q 0 [12292,12293,20496,118826],q 11 [20496,118826],q 0 [16392,20484,12833,1056795],q 10 [20484,12833],q 4 [16392,1056795],q 12 [20488,12653],q 2 [20488,12653],q 0 [16390,16391,20488,12653],q 13 [16390,16391],q 1 [8198,20493,86024],q 0 [12292,20488,20489,377199],q 0 [12292,20496,118821,20497],q 2 [16397,20629,294920],q 0 [16389,16394,14573,391684],q 2 [16394,14573],q 10 [14573,391684],q 0 [16390,20488,20489,377199],q 3 [12293,20493],q 0 [8196,12533],q 12 [17826,1445],q 10 [8196,12533,1445],q 3 [16397,20628],q 0 [16389,12298,390319],q 1 [16389,12298,390319],q 12 [12298,390319],q 2 [12298],q 11 [16389,390319],q 3 [16390,20485],q 12 [12297,577756],q 10 [12297,311516],q 12 [16397,20493],q 13 [16397,20493],q 0 [20488,20489,377199,12661],q 0 [12293,20488,20489,377199],q 4 [16389,86396],q 0 [16389,20492,20493,86396],q 0 [16390,16391,20492,20493],q 0 [16389,20493,86396],q 13 [20494,21221],q 2 [20497,311304],q 0 [12293,20497,311304,41571],q 13 [20493,86044],q 10 [20493,86044],q 3 [20493,86020],q 0 [20492,20493,86033,294916],q 4 [86033,294916],q 12 [20492,114698],q 2 [20492,114698],q 0 [16390,16391,20492,114698],q 0 [20499,13825],q 0 [12297,20497,311303,226655],q 3 [20497,311303],q 1 [12297,20497,311516],q 0 [12297,20497,311516],q 13 [20497,311516],q 11 [20497,311516],q 4 [12297,311516],q 0 [16390,13497,20489,379240],q 3 [16390,13497],q 12 [12298,12299],q 2 [12298,12299],q 0 [12298,12299,16390,16391],q 0 [16390,16391,20488,20489],q 0 [16390,16391,20494,20495],q 4 [12298,2651311],q 1 [16390,20492,20493],q 4 [16390,86019],q 0 [16388,16389,389499,12299],q 0 [20488,20489,377199,12663],q 2 [20493,86024],q 2 [16397,20628],q 0 [16391,20488,12653,2619263],q 10 [20488,12653],q 4 [16391,2619263],q 0 [12299,20484,20485,578083],q 14 [20629,294931],q 0 [12299,20496,20497,311415],q 14 [8197,20629],q 13 [16396,20641],q 0 [4104,16396,20641,868363],q 12 [16396,20641,868363],q 1 [16396,16397,20628],q 0 [16396,16397,20628],q 10 [20628],q 14 [8196,20628],q 1 [20484,12833,17418],q 0 [20484,12833,17418],q 4 [17418],q 0 [16397,20629,294923,5895],q 0 [20484,16929,12306,2651571],q 10 [20484],q 4 [12306,2651571],q 3 [20484,16929],q 14 [20484,16929],q 0 [20488,20489,377199,12660],q 0 [20485,16396,20641,16397],q 0 [20485,16396,16397,577684],q 0 [20485,16396,16397,577687],q 0 [8196,20497,311308,340213],q 0 [20485,16398,577555,14905],q 11 [20485,577555],q 2 [16398,14905],q 0 [20491,16396,165481,16397],q 0 [16396,20641,868363,16397],q 0 [16398,20493,86907,86020],q 12 [16398,20493,86907],q 13 [16398,20493,86907],q 0 [16396,16397,151557,352419],q 0 [16396,16397,20628,409609],q 10 [20628,409609],q 14 [20628,409609],q 0 [16396,16397,20628,409606],q 10 [20628,409606],q 14 [20628,409606],q 1 [20488,12653,2617348],q 1 [20488,12653,16398],q 0 [20488,12653,16398],q 0 [16396,16397,20629,294916],q 10 [20629,294916],q 14 [20629,294916],q 0 [16392,16393,28699,4128],q 1 [20497,20493,86035],q 1 [20488,12653,18940],q 0 [20488,12653,18940],q 4 [18940],q 0 [16397,20493,86020,86032],q 12 [16397,20493,86032],q 3 [16397,20493,86032],q 13 [16397,20493,86032],q 10 [20493,86020],q 4 [16397,86032],q 11 [20629,294915,294923],q 0 [16397,20629,294916,9993],q 4 [86035],q 0 [20492,20493,86131,86035],q 0 [16397,20629,294923,5893],q 0 [8198,16396,20641,868360],q 0 [16397,20629,294920],q 0 [16397,20629,294920,296823],q 0 [16397,20629,294916,294923],q 10 [20629,294916,294923],q 11 [20629,294916,294923],q 0 [12305,20629,294916,294931],q 12 [16394,16395],q 2 [16394,16395],q 13 [20486,20487],q 0 [16394,16395,20486,20487],q 0 [20496,12405,122884,122885],q 10 [122884,122885],q 4 [122884,122885],q 4 [311300],q 0 [20499,13825,1912843],q 3 [20499,13825],q 0 [20494,21221,86020],q 3 [20494,21221],q 4 [86020],q 0 [20493,86033,294916],q 0 [20497,20494,311311],q 3 [20493,86035],q 0 [20493,86027],q 0 [20493,86027,86035],q 0 [20493,86027,86033],q 3 [20493,86033],q 1 [20493,86027],q 0 [20493,86027,86023],q 4 [86023],q 11 [86023],q 10 [20493,86023],q 4 [86027],q 11 [86027],q 0 [20493,86025,94212],q 0 [20493,86021],q 0 [20493,86021,86027],q 3 [20493,86021],q 4 [86021],q 11 [86021],q 0 [20499,13825,1912836],q 0 [20493,86020],q 0 [20493,86020,86035],q 0 [20493,86020,86032],q 3 [20493,86032],q 11 [86032],q 0 [20497,311300,12801],q 0 [20492,20493,86035],q 0 [20496,20497,311302],q 0 [20492,16497],q 0 [20492,16497,679942],q 3 [20492,16497],q 13 [20492,16497],q 11 [679942],q 4 [679942],q 0 [20492,16497,679941],q 11 [679941],q 0 [20496,12405],q 0 [20496,12405,122884],q 1 [20496,12405],q 3 [20496,12405],q 13 [20496,12405],q 10 [122884],q 4 [122884],q 11 [86020],q 0 [16398,20493,86020],q 3 [16398,20493],q 11 [20629,294916],q 0 [12305,20629,294931],q 0 [16397,20628,151955],q 0 [16397,20628,409609],q 11 [20628,409609],q 0 [16397,20493,86035],q 0 [20493,86033,294923],q 0 [16397,20493,86020],q 3 [16397,20493],q 0 [16397,20629,294935],q 0 [16397,151557],q 0 [16397,151557,151563],q 2 [16397,151563],q 3 [16397,151557],q 10 [151557],q 11 [151557],q 0 [16397,151556,151557],q 10 [20631],q 14 [20631],q 0 [16396,16397,20630],q 14 [20630],q 0 [16396,16397,151563],q 10 [151563],q 14 [151563],q 9 [],q 9 [20497],q 12 [20497,311299],q 3 [20497,311299],q 13 [20497,311299],q 1 [20497,311302],q 0 [16396,16397,151557],q 14 [151557],q 0 [16396,20641,868363],q 0 [20491,16398,1680249],q 3 [16398],q 11 [20491],q 0 [20491,16396,16397],q 10 [20491],q 14 [20491],q 0 [20491,13929,18849],q 3 [18849],q 11 [20491,18849],q 0 [20486,16398,911353],q 0 [20490,16397,154227],q 11 [20490,154227],q 0 [20486,16396,165881],q 0 [20486,20487,16397],q 0 [20486,14329,19069],q 12 [19069],q 11 [20486,19069],q 0 [20486,14329,20494],q 11 [20486],q 12 [20494],q 0 [20493,86021,1888267],q 0 [20486,18425,20497],q 0 [20485,577555,14905],q 2 [14905],q 11 [20485],q 0 [20485,20494,577551],q 0 [20485,16398,577555],q 0 [20485,12306,578995],q 0 [20485,16397,577687],q 0 [20485,16397,577684],q 0 [20485,16396,16397],q 10 [20485],q 14 [20485],q 0 [20484,16396,16397],q 14 [20484],q 0 [20484,20485],q 0 [20484,20485,16398],q 1 [20484,20485],q 11 [20484,20485],q 3 [20484,20485],q 13 [20484,20485],q 0 [20484,20485,16397],q 0 [20484,12833],q 2 [12833],q 12 [17418],q 0 [20484,16929],q 0 [20484,16929,14876],q 11 [20484,16929],q 2 [16929],q 12 [14876],q 4 [14876],q 13 [20484,16929],q 0 [20484,16929,12305],q 12 [12305],q 0 [20484,12833,1056779],q 12 [1056779],q 4 [1056779],q 0 [20488,12653],q 1 [20488,12653],q 0 [20488,12653,2617348],q 3 [12653],q 4 [2617348],q 13 [2617348],q 0 [12299,20499,2483713],q 3 [20499],q 0 [12299,20498,2484113],q 3 [20498],q 0 [12299,20496,20497],q 4 [12299],q 0 [20484,20485,16396],q 2 [16396],q 0 [20496,118797],q 0 [12299,20496,118797],q 3 [20496,118797],q 12 [20496,118797],q 10 [12299],q 12 [12299],q 0 [12299,20496,118790],q 0 [16395,20492,117333],q 3 [20492],q 11 [16395],q 0 [12295,20491,1681241],q 2 [20491],q 3 [12295],q 2 [12299],q 0 [12299,20486,20487],q 0 [16391,20489,378751],q 3 [16391],q 0 [20496,12405,122891],q 10 [122891],q 4 [122891],q 0 [12299,20484,16929],q 0 [12299,20484,12833],q 2 [12299,12833],q 1 [12299,22905],q 0 [12299,22905],q 3 [2797571],q 11 [2797571],q 0 [16395,14933,23222],q 3 [23222],q 0 [16395,14933,23221],q 3 [23221],q 0 [16390,20499,13825],q 1 [16390],q 13 [16390],q 3 [16390],q 0 [16390,20494,21221],q 10 [20494,21221],q 11 [16390],q 4 [16390],q 0 [16390,20494,1237733],q 10 [20494,1237733],q 0 [20497,311300],q 1 [20497,311300],q 3 [20497,311300],q 13 [20497,311300],q 0 [20497,311300,311310],q 13 [20497,311310],q 0 [16390,20493,86032],q 0 [16390,20493,86024],q 0 [12298,20497,312495],q 0 [16390,20492,16497],q 10 [20492],q 0 [16390,20492,114698],q 10 [20492,114698],q 0 [20492,114697],q 0 [16390,20492,114697],q 10 [20492,114697],q 0 [20491,13929],q 0 [16390,20491,13929],q 12 [16394],q 2 [16394],q 0 [20486,20487],q 0 [16394,20486,20487],q 0 [12298,20485,578735],q 11 [20485,578735],q 13 [20485],q 0 [16396,16397,151556],q 10 [151556],q 14 [151556],q 0 [16394,20484,559341],q 10 [20484,559341],q 13 [20484],q 0 [16390,12299,22905],q 10 [12299,22905],q 2 [12299,22905],q 12 [12299,22905],q 0 [16390,12299,2483385],q 10 [12299,2483385],q 2 [12299,2483385],q 4 [12298],q 12 [12298],q 12 [20499],q 10 [12298],q 0 [20491,16396,165481],q 3 [16396],q 0 [16390,12298],q 1 [16390,12298],q 0 [12299,20484,20485],q 0 [12294,16394,2340109],q 10 [12294,2340109],q 11 [16394,2340109],q 2 [16394,2340109],q 13 [12294],q 3 [12294,2340109],q 12 [12298,20489],q 0 [12298,20489,16390],q 2 [20492],q 0 [16390,16391,20492],q 1 [16390,16391],q 12 [20489],q 0 [16390,16391,20489],q 12 [20488],q 2 [20488],q 0 [16390,16391,20488],q 0 [16390,16391,12299],q 0 [16398,20497,311311],q 0 [12298,12299,16390],q 4 [12298,12299],q 14 [20628],q 0 [16390,21689,20497],q 0 [12298,21677],q 0 [12298,21677,16390],q 10 [12298,21677],q 12 [12298,21677],q 3 [21677],q 0 [16390,13497,22890],q 12 [22890],q 0 [20496,118789],q 0 [12299,20496,118789],q 3 [20496,118789],q 11 [20496,118789],q 0 [16390,13497,22889],q 12 [22889],q 0 [12294,17677,12305],q 11 [17677],q 0 [20489],q 0 [16390,13497,20489],q 0 [16394,14573],q 1 [16394,14573],q 12 [16394,14573],q 0 [16394,14573,2625540],q 3 [14573],q 10 [14573],q 13 [2625540],q 0 [16394,14573,20489],q 11 [16394,20489],q 0 [16389,20495,389867],q 2 [20495],q 1 [20493,86021],q 6 [],q 11 [86019,86021],q 11 [16389],q 4 [16389],q 0 [16389,20494,20495],q 13 [20494,20495],q 3 [20494,20495],q 0 [16390,13497,20497],q 1 [16390,13497],q 13 [16390,13497],q 4 [12293,311336],q 13 [16389],q 0 [16389,20493,86027],q 0 [20497,20493,86035],q 12 [20495],q 0 [16390,16391,20495],q 0 [16394,14573,16390],q 11 [16394],q 0 [16393,20493,86020],q 0 [16389,20492,20493],q 0 [20493,86020,86024],q 0 [12305,20499,20630],q 0 [16389,20492,16497],q 0 [12297,20496,118790],q 12 [12297],q 4 [12297],q 13 [20496,118790],q 10 [12297],q 0 [12293,20496,118793],q 4 [12293],q 12 [20496,118793],q 10 [12293],q 0 [12293,16426,20499],q 0 [12293,20498,42899],q 2 [20498],q 0 [12293,16426,20496],q 2 [20496],q 11 [16426,20496],q 0 [20486,20487,16396],q 0 [12293,16426,22874],q 2 [22874],q 0 [16391,20493,87935],q 0 [12293,16426,22873],q 2 [22873],q 11 [16426,22873],q 0 [20493,86021,1888275],q 0 [12293,20495,20522],q 0 [16389],q 0 [16389,20499,13825],q 1 [16389],q 3 [16389],q 0 [8198,13645,18757],q 3 [18757],q 11 [8198,18757],q 2 [13645,18757],q 12 [18757],q 10 [8198,13645],q 0 [20485,20497,577555],q 0 [20488,20489],q 0 [12292,20488,20489],q 1 [20488,20489],q 0 [8197,20495,271083],q 3 [20495],q 0 [8196,16397],q 1 [8196,16397],q 0 [8197,20496,119050],q 3 [20496],q 0 [20486,14329,19070],q 12 [19070],q 0 [8197,20498,272275],q 1 [20493,86020],q 0 [12305,20497],q 1 [12305,20497],q 0 [8196,12305,20497],q 3 [12305,20497],q 13 [12305,20497],q 12 [20489,376847],q 0 [16390,20489,376847],q 2 [16397,20631],q 0 [12299,20484,559481],q 3 [20484],q 0 [8197,20493,86035],q 0 [16397,20630,20631],q 0 [8196,16396,20641],q 0 [20492,20493,86021],q 11 [20484,17418],q 0 [8197,20494],q 1 [8197,20494],q 0 [16390,20491,1680569],q 10 [20491,1680569],q 12 [20491],q 1 [8196,20499],q 0 [8196,20499],q 13 [20499],q 1 [16398,20499],q 0 [16398,20499],q 0 [8198,13645,18758],q 12 [18758],q 3 [18758],q 0 [8196,20496,12407],q 1 [20496,12407],q 3 [20496,12407],q 0 [12292,20517],q 0 [12292,20517,2920459],q 3 [12292,20517],q 2 [20517],q 12 [2920459],q 0 [8197,20497],q 1 [8197,20497],q 0 [8197,20493],q 1 [8197,20493],q 0 [20498,14225],q 0 [8197,20498,14225],q 3 [20498,14225],q 3 [16397,20494],q 0 [8198,16397,20494],q 0 [20485,12304,577555],q 2 [12304],q 0 [4106,16397,153119],q 12 [16397,153119],q 3 [16397,153119],q 10 [4106,153119],q 11 [4106,153119],q 0 [12296,20496,118790],q 12 [12296],q 1 [20496,118790],q 10 [12296],q 4 [12296],q 11 [16393],q 12 [16393],q 13 [12293],q 0 [8197,20493,86033],q 0 [8196,16629,13912],q 11 [8196,16629],q 2 [16629],q 12 [13912],q 3 [16629],q 13 [13912],q 0 [16393],q 0 [12293,16393,20522],q 3 [12293,20522],q 0 [16398,17273],q 0 [8197,16398,17273],q 3 [16398,17273],q 0 [8196,20725,1450003],q 12 [1450003],q 13 [1450003],q 1 [16397,20628],q 0 [16397,20628],q 11 [20628],q 0 [20494,21221,86027],q 2 [12305],q 3 [12293,20486],q 0 [12293,20486],q 0 [8197,12305,20497],q 0 [20497,311310,311311],q 0 [8197,20496,12407],q 0 [8197,20746,15157],q 2 [15157],q 3 [15157],q 0 [20491,13929,16398],q 0 [8197,20492,16497],q 0 [16390,13497],q 0 [16390,13497,2465803],q 2 [13497],q 12 [2465803],q 0 [12293,20493,16426],q 11 [16426],q 12 [20493,16426],q 1 [12293,16426],q 13 [12293,16426],q 3 [12293,16426],q 0 [20493,86020,86027],q 0 [16390,20493,86027],q 0 [8196,12533,21921],q 2 [12533,21921],q 3 [12533,21921],q 0 [16390,20492,20493],q 0 [8197,16650,14238],q 2 [14238],q 3 [14238],q 0 [8197,16650,14237],q 2 [14237],q 3 [14237],q 2 [12296],q 0 [12296,20486,20487],q 1 [20486,20487],q 12 [16426],q 0 [12293,20486,16426],q 11 [20486,16426],q 11 [8197,16650],q 3 [20494],q 0 [8197,16397,20630],q 3 [16397,20630],q 0 [16390,16391,20494],q 0 [12296,12297],q 0 [12296,12297,20486],q 1 [12296,12297],q 3 [20486],q 4 [16395],q 0 [20494,20495],q 0 [16395,20494,20495],q 1 [16389,20493],q 0 [16389,20493],q 1 [20498,14225],q 0 [8196,20498,14225],q 0 [8198,13645,22854],q 12 [22854],q 3 [22854],q 4 [8198,13645],q 0 [8197,16398],q 1 [8197,16398],q 0 [12292,12293,20497],q 1 [12292,12293],q 0 [20491,13929,18850],q 3 [18850],q 11 [20491,18850],q 0 [8198,17741,20494],q 11 [8198,17741],q 2 [17741],q 0 [16389,20862,15185],q 2 [15185],q 11 [16389,20862],q 0 [8196,8197,20492],q 0 [8197,16397,151816],q 0 [16395,12295,1927765],q 2 [16395],q 10 [12295],q 1 [8196,12533],q 0 [8196,12533,17826],q 2 [12533],q 3 [12533],q 12 [17826],q 10 [8196,12533],q 13 [17826],q 1 [8196,20497],q 0 [8196,20497],q 0 [8196,20497,311310],q 10 [311310],q 0 [20486,20487,16398],q 1 [16397,20494],q 2 [16397,20494],q 0 [8196,12533,20494],q 2 [12533,20494],q 3 [12533,20494],q 13 [20494],q 0 [8196,20499,13825],q 0 [8196,20493,86033],q 1 [8196,20493],q 0 [16390,20488,12653],q 0 [12297,20486,20487],q 0 [20487,16397,152819],q 0 [8197,16397],q 1 [8197,16397],q 0 [8196,20499,251393],q 3 [20499,251393],q 2 [20499,251393],q 0 [12292,20517,20497],q 0 [16393,20484,12833],q 4 [16393],q 0 [8198,16396,20641],q 0 [16397,20628,409606],q 11 [20628,409606],q 0 [8197,16397,20629],q 0 [8196,16397,20630],q 1 [16397,20630],q 0 [12296,16390,16391],q 0 [8197,20746],q 2 [2869],q 3 [2869],q 0 [8197,20494,20495],q 0 [8196,16629,20497],q 2 [16629,20497],q 3 [16629,20497],q 0 [8196,20494,20495],q 1 [20494,20495],q 0 [20492,20493,86027],q 0 [8196,20494,21221],q 0 [8198,20492,16497],q 1 [20494,20498],q 0 [8196,16397,151799],q 3 [16397,151799],q 2 [16397,151799],q 10 [8196,151799],q 11 [8196,151799],q 0 [8197,16396,164106],q 0 [8196,20725,20499],q 2 [20725,20499],q 3 [20725,20499],q 0 [16398,20493,86027],q 0 [16397,20494,20498],q 0 [20485,16396,20641],q 0 [8196,12533,16398],q 2 [12533,16398],q 3 [12533,16398],q 0 [20497,311307,13657],q 0 [8197,20497,311310],q 0 [20498,14225,20494],q 0 [8197,20496,12405],q 11 [20496],q 0 [8196,20493,86035],q 0 [8197,16398,20493],q 0 [8196,12533,17825],q 2 [12533,17825],q 3 [12533,17825],q 11 [8196,17825],q 12 [17825],q 13 [17825],q 4 [311310],q 0 [20488,16397,151919],q 0 [8198,20493,86035],q 0 [20485,16396,577699],q 0 [16397,20494],q 0 [8197,16397,20494],q 11 [4104,86027],q 2 [12533,17826],q 3 [12533,17826],q 11 [8196,17826],q 0 [8196,12533,21922],q 12 [21922],q 13 [21922],q 4 [8196,12533],q 0 [8197,16650,22429],q 2 [22429],q 3 [22429],q 10 [8197,22429],q 0 [8198,16397],q 1 [8198,16397],q 0 [8196,12533,20497],q 0 [8196,16629,20494],q 0 [20484,12833,17417],q 12 [17417],q 0 [16390,20492,115897],q 10 [20492,115897],q 0 [8196,20725,20493],q 2 [20725,20493],q 3 [20725,20493],q 0 [8196,20492,16497],q 1 [20492,16497],q 0 [16389,20491,13929],q 13 [13929],q 1 [12305,20499],q 0 [12305,20499],q 11 [8197,86019],q 0 [8197,16650,22430],q 2 [22430],q 3 [22430],q 0 [8196,16397,20629],q 0 [20488,16749],q 1 [20488,16749],q 0 [12292,20488,16749],q 12 [20488,16749],q 3 [16749],q 13 [12292],q 0 [8196,20493],q 11 [8196,86019],q 0 [16398,21369],q 1 [16398,21369],q 0 [8196,16398,21369],q 3 [16398,21369],q 0 [8196,16398,20493],q 0 [8197,16396,20641],q 1 [16398,20497],q 0 [16398,20497],q 0 [8196,16398],q 1 [8196,16398],q 0 [8196,16629,12305],q 2 [16629,12305],q 3 [16629,12305],q 13 [12305],q 0 [8196,20496,12405],q 0 [16388,12665,23446],q 12 [23446],q 0 [16397,151558,151559],q 0 [12299,22905,2797587],q 3 [2797587],q 1 [8197,20499],q 0 [8197,20499],q 1 [20493,20497],q 0 [20493,20497],q 0 [16390,20493,86035],q 0 [8198,20494,1389285],q 2 [20494,1389285],q 0 [12299,18809,20497],q 0 [8197,20499,13825],q 1 [20497,311308],q 0 [20497,311308],q 0 [8196,20497,311308],q 10 [311308],q 0 [8198,13645,20497],q 1 [8198,13645],q 0 [8197,20494,21221],q 0 [8196,8197,16396],q 0 [8198,16396,165197],q 2 [16396,165197],q 0 [12292,20496,118797],q 1 [20496,118797],q 13 [20496,118797],q 10 [12292],q 0 [8196,20494,250597],q 3 [20494,250597],q 2 [20494,250597],q 0 [12305,20497,20630],q 3 [12305],q 4 [311311],q 0 [16390,20497,311311],q 3 [20497,311311],q 0 [12292,16421,20497],q 3 [12292,16421],q 0 [8198,16397,20630],q 0 [12294,21773,3067923],q 12 [3067923],q 0 [12292,20490,39537],q 12 [20490],q 3 [12292,39537],q 0 [8198,13645,22853],q 3 [22853],q 1 [20497,20494],q 0 [8196,20494],q 1 [8196,20494],q 0 [12297,16391,227199],q 13 [16391,227199],q 13 [20486],q 1 [16394,16395],q 0 [16394,16395],q 0 [12292,12293,20488],q 0 [16396,16397,151558],q 14 [151558],q 0 [8198,16398,17273],q 0 [8198,16398,20493],q 0 [20491,18025],q 1 [20491,18025],q 0 [12292],q 0 [12292,20491,18025],q 12 [20491,18025],q 3 [12292],q 0 [8197,20497,311308],q 1 [8198,20497],q 0 [8198,20497],q 0 [8198,16398],q 1 [8198,16398],q 0 [8198,16397,20629],q 1 [8198,20499],q 0 [8198,20499],q 0 [8198,21837,3088403],q 12 [3088403],q 3 [3088403],q 0 [8198,20496,12405],q 0 [8198,20496,12407],q 1 [8198,20493],q 0 [8198,20493],q 11 [8198,86019],q 3 [12306],q 3 [16389,390319],q 0 [12293,20486,16394],q 10 [12293,20486],q 0 [16390,20494,20495],q 0 [12297,20484,20485],q 2 [16398,1389433],q 0 [12297,20487,226547],q 3 [20487],q 13 [20487,226547],q 0 [16390,13497,16398],q 0 [8198,20494],q 1 [8198,20494],q 0 [8198,20497,311308],q 0 [12292,20517,20499],q 0 [8198,20493,86033],q 1 [16398,17273],q 0 [8196,16398,17273],q 0 [12293,20493,20522],q 1 [16390,20493],q 0 [16390],q 1 [16397,20631],q 0 [16397,20631],q 0 [8198,20498,14225],q 0 [8198,20494,21221],q 0 [12293,20488,41327],q 12 [20488,41327],q 0 [8198,20494,20495],q 0 [16390,16391,20491],q 0 [12292,12293,20496],q 0 [8198,20492,116045],q 0 [12292,20517,20489],q 11 [20489],q 0 [8198,20499,1390081],q 2 [20499,1390081],q 0 [20484,16398,557945],q 0 [8198,20499,13825],q 0 [12292,16421,16393],q 2 [16421,16393],q 0 [16388,12665,12299],q 3 [16388,12665],q 0 [20497,311301,528396],q 0 [16395,14933,20494],q 0 [16388,12665,20494],q 11 [16388],q 0 [20493,86020,86021],q 11 [86020,86021],q 0 [16388,12665,23445],q 12 [23445],q 0 [16392,20505],q 0 [16392,20505,12293],q 3 [20505],q 0 [12296,20697],q 0 [12296,20697,16390],q 10 [12296,20697],q 12 [12296,20697],q 3 [20697],q 2 [12296,20697],q 0 [12299,20486,2484217],q 4 [12299,2484217],q 0 [12296,20697,3121156],q 13 [3121156],q 0 [16396,20641,868356],q 0 [16390,20488,20489],q 0 [16397,20493,20630],q 0 [16388,16389],q 0 [16388,16389,20494],q 3 [16388,16389],q 13 [16388,16389],q 0 [8198,20497,311310],q 0 [16392,16393],q 0 [16392,16393,12292],q 1 [16392,16393],q 12 [16392,16393],q 0 [12292,12293,16393],q 0 [12293],q 0 [12293,20493,86035],q 0 [12296,12297,16390],q 0 [16390,21689,20499],q 10 [21689],q 0 [12292,20517,2920467],q 12 [2920467],q 0 [16388,16389,12299],q 0 [16397,20493,86027],q 0 [12292,12293,20489],q 0 [12292,12293,20499],q 0 [20491,18025,12305],q 11 [20497,312495],q 0 [12292,20499,38401],q 0 [16388,12296,221561],q 11 [8198,86024],q 0 [16392,12293,40987],q 2 [16392],q 12 [16392,40987],q 3 [12293,40987],q 0 [12292,16394,39149],q 10 [12292,39149],q 3 [12292,39149],q 0 [8197,16398,21369],q 0 [12292,16395,39509],q 12 [16395],q 2 [16395,39509],q 0 [12296,20484,557273],q 0 [16392,20485,577563],q 0 [12305,20497,20494],q 0 [12292,20517,20491],q 2 [20517,20491],q 0 [12292,20491,38505],q 0 [16388,20492,115065],q 0 [8198,12305,20497],q 0 [20496,118793],q 0 [12292,20496,118793],q 1 [20496,118793],q 0 [12292,20496,20497],q 0 [16388,20493,86035],q 0 [20484,12833,16398],q 1 [20484,12833],q 0 [16392,20493,86043],q 0 [12292,20498,38801],q 12 [20498],q 4 [16388],q 0 [16388,20494,20495],q 0 [12297],q 0 [12293,12297,16426],q 0 [16393,16390,13497],q 10 [13497],q 0 [20493,86020,86033],q 0 [20487,17649],q 0 [12299,20487,17649],q 3 [20487,17649],q 11 [20487,17649],q 10 [20487],q 12 [16393,28687],q 0 [16393,16390,28687],q 2 [16393,28687],q 10 [28687],q 13 [20497,311303],q 11 [20497,311303],q 0 [20497,311302,311303],q 0 [12293,16393],q 1 [12293,16393],q 0 [8198,16398,21369],q 0 [12297,16390,16391],q 0 [16390,20490,1239665],q 4 [16390,1239665],q 0 [20498,22417],q 0 [12293,20498,22417],q 1 [12293],q 13 [20498,22417],q 3 [20498,22417],q 0 [12293,20496,41079],q 0 [16394,22765],q 0 [12293,16394,22765],q 2 [16394,22765],q 3 [22765],q 0 [16390,20485],q 0 [12297,16390,20485],q 0 [16393,20484,16929],q 0 [8197,16650,20493],q 1 [8197,16650],q 0 [12297,16390],q 1 [12297,16390],q 13 [12293,20522],q 0 [12293,16394,20522],q 0 [20490,14961],q 0 [16390,20490,14961],q 10 [20490,14961],q 12 [20490,14961],q 3 [14961],q 0 [12294,20499,1574157],q 4 [12294],q 11 [20499,1574157],q 0 [16395,23125],q 0 [12293,16395,23125],q 2 [16395,23125],q 0 [12292,12293,20491],q 0 [12293,20489,16426],q 10 [20489],q 11 [86019,86027],q 0 [12293,20489,376872],q 11 [20489,376872],q 0 [16390,16391,20493],q 0 [12297,20485,577555],q 3 [20485,577555],q 0 [20486,16396,16397],q 10 [20486],q 14 [20486],q 0 [12293,20490,43635],q 2 [20490],q 12 [12297,16606],q 1 [12297,16606],q 0 [16393,20486,14329],q 3 [20486,14329],q 0 [12293,16397,16426],q 10 [389135],q 4 [16389,389135],q 0 [16389,12307,389135],q 0 [20496,12407],q 0 [20496,118790],q 0 [16397,20630],q 0 [20489,20486],q 1 [20489],q 0 [12293,20493],q 0 [20496],q 0 [12299,20496],q 1 [12299],q 0 [12293,20489],q 0 [12293,20522],q 0 [16396],q 0 [20486,16396],q 1 [16396],q 0 [12305],q 0 [16390,20495],q 13 [20495],q 0 [20497,311302],q 0 [20488],q 0 [12292,20488],q 1 [20488],q 0 [16389,12299],q 0 [12292,20499],q 0 [12292,20497],q 1 [12292],q 0 [16389,20492],q 0 [8197,16650],q 0 [20485],q 0 [12299,20485],q 3 [20485],q 0 [12293,16426],q 0 [12296],q 0 [12296,20486],q 1 [12296],q 1 [20486],q 0 [20484,16397],q 0 [20494],q 0 [20486,20494],q 0 [12292,16393],q 1 [16393],q 0 [8196,20725],q 2 [20725],q 3 [20725],q 0 [16397,151563],q 0 [20485,16397],q 0 [20485,20494],q 0 [12297,20486],q 1 [12297],q 0 [16397,151556],q 0 [8197,16396],q 0 [16392],q 0 [12292,16392],q 1 [16392],q 11 [16392],q 12 [16392],q 0 [12296,16390],q 0 [12297,20484],q 0 [12293,20499],q 0 [16388,12665],q 0 [20486,14329],q 0 [12299],q 0 [12299,20486],q 0 [20485,16398],q 1 [20485],q 0 [12292,20496],q 1 [20496],q 0 [20484],q 0 [20484,16398],q 1 [20484],q 0 [20491,16396],q 0 [8196,16396],q 0 [12293,12297],q 0 [16393,16390],q 0 [20492],q 0 [8196,20492],q 1 [20492],q 0 [16389,20499],q 0 [16389,20494],q 0 [8197,20492],q 0 [16390,16397],q 0 [16388],q 0 [16388,12299],q 3 [16388],q 0 [8198,21837],q 0 [8198,16396],q 0 [12299,20484],q 0 [12292,20489],q 0 [16390,20488],q 0 [8198,20492],q 0 [12293,20497],q 0 [12292,20491],q 1 [20491],q 1 [20490],q 0 [20490],q 0 [20486],q 0 [20486,20490],q 0 [16390,16394],q 0 [20497,20494],q 0 [12293,16397],q 0 [16390,20489],q 1 [16394],q 0 [16394],q 0 [16394,20486],q 0 [16390,16398],q 0 [16390,20492],q 0 [20486,20493],q 0 [16390,20491],q 0 [16388,20494],q 13 [16388],q 0 [16390,20494],q 0 [16390,20497],q 0 [16390,20499],q 0 [16395,14933],q 0 [12293,20491],q 0 [20491,16397],q 0 [16390,21689],q 0 [12299,16391],q 11 [16391],q 0 [12299,20487],q 11 [20487],q 0 [20494,20498],q 13 [20498],q 0 [12299,20497],q 0 [12299,20499],q 0 [16395,20494],q 0 [20484,16396],q 0 [20485,20489],q 0 [20485,16396],q 0 [20485,20493],q 0 [20486,16398],q 0 [16390,20493],q 0 [20485,577555],q 0 [16390,12299],q 0 [8198,13645],q 0 [20486,16397],q 0 [20491],q 0 [16389,12307],q 2 [12307],q 13 [12307],q 3 [12307],q 0 [16397,151558]]
def B_21_1 : BT (List (List Nat)) := BT.empty
lemma B_21_1_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_21 1 xs.toFinset) B_21_1 := .empty
def U_21_2 : List Nat := []
def P_21_2 : BT (Option BoundPool) := buildPoolsSubBT 12 W_21 r_21 S_21 ps_21 U_21_2
def N_21_2 : List NodeSpec := [([14,0,5],[],[]),([20,0,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_21_2 : checkNodesBT W_21 g_21 F_21 P_21_2 A_21 B_21_1 2 N_21_2 = true := by decide +kernel
def B_21_2 : BT (List (List Nat)) := buildBucketsBT W_21 N_21_2
set_option maxRecDepth 500000 in
lemma B_21_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_21 2 xs.toFinset) B_21_2 :=
  buildBucketsBT_sound (by decide) gp_21 W_21_ok (buildPoolsSubBT_sound S_21_ok) A_21_ok B_21_1_ok C_21_2
def U_21_3 : List Nat := [0]
def P_21_3 : BT (Option BoundPool) := buildPoolsSubBT 12 W_21 r_21 S_21 ps_21 U_21_3
def N_21_3 : List NodeSpec := [([0,27,28,4],[],[]),([0,36,4,5],[],[]),([38,44,0,5],[],[]),([0,50,40,5],[],[]),([0,51,53,21],[],[]),([60,0,4,5],[],[]),([65,0,66,37],[],[]),([0,70,71,4],[],[1]),([0,73,28,75],[],[]),([0,79,66,80],[],[]),([81,0,66,82],[],[]),([77,58,0,57],[0],[]),([0,73,83,84],[],[]),([88,0,90,5],[],[]),([97,98,0,3],[],[0]),([99,0,66,101],[],[]),([104,0,66,21],[],[]),([0,108,3,5],[],[]),([77,109,0,110],[0],[]),([0,114,115,5],[],[]),([0,117,118,5],[],[]),([0,73,40,101],[],[]),([122,123,0,4],[],[1]),([0,3,127,5],[],[]),([0,73,62,100],[],[]),([131,0,3,133],[],[]),([0,113,134,5],[],[]),([0,121,2,135],[],[]),([140,0,37,141],[],[]),([142,0,66,143],[],[]),([144,0,66,62],[],[]),([12,13,0,5],[],[0]),([145,146,0,5],[],[0]),([147,148,0,4],[],[1]),([0,149,151,37],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_21_3 : checkNodesBT W_21 g_21 F_21 P_21_3 A_21 B_21_2 3 N_21_3 = true := by decide +kernel
def B_21_3 : BT (List (List Nat)) := buildBucketsBT W_21 N_21_3
set_option maxRecDepth 500000 in
lemma B_21_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_21 3 xs.toFinset) B_21_3 :=
  buildBucketsBT_sound (by decide) gp_21 W_21_ok (buildPoolsSubBT_sound S_21_ok) A_21_ok B_21_2_ok C_21_3
def U_21_4 : List Nat := (r 0 28)
def P_21_4 : BT (Option BoundPool) := buildPoolsSubBT 12 W_21 r_21 S_21 ps_21 U_21_4
def N_21_4 : List NodeSpec := [([154,0,1,156,29],[],[]),([77,0,79,66,3],[],[0]),([160,0,3,4,5],[],[]),([12,8,11,0,5],[],[0]),([0,61,73,28,74],[],[0,1]),([161,0,3,103,5],[],[]),([0,66,28,75,72],[],[0,1]),([77,0,61,73,3],[0],[]),([77,162,0,66,3],[0],[]),([104,0,66,3,5],[],[0]),([163,0,165,4,5],[],[]),([169,0,1,170,5],[],[]),([171,0,61,66,173],[1],[]),([174,0,175,3,5],[],[1]),([0,66,83,84,72],[],[0,1]),([176,178,1,2,3],[],[]),([0,165,3,84,76],[],[]),([0,179,181,4,5],[],[]),([122,0,121,2,4],[],[0]),([183,0,61,66,184],[2,3],[]),([0,66,62,100,72],[],[0]),([185,186,187,0,188],[4],[1]),([8,0,192,3,5],[],[2]),([193,0,1,196,5],[5],[3]),([97,93,96,0,3],[],[0]),([0,73,3,75,5],[],[0]),([197,0,66,3,76],[],[]),([0,199,200,37,92],[],[2]),([131,0,132,3,29],[],[0,1]),([201,0,1,17,3],[6,7,8],[3]),([202,0,66,37,5],[],[]),([8,0,1,53,21],[],[0]),([77,58,56,0,1],[9,10],[0]),([144,0,1,2,62],[],[0]),([206,0,94,3,5],[],[]),([187,0,3,207,5],[],[0]),([0,208,82,74,4],[],[]),([210,0,211,40,37],[11,12],[]),([0,61,208,173,4],[],[]),([0,66,37,101,212],[],[]),([163,164,0,66,76],[],[1]),([154,0,1,3,213],[],[2]),([0,66,40,101,72],[],[0]),([214,215,0,66,37],[],[0]),([99,0,61,66,100],[13],[0]),([0,73,62,37,5],[],[0]),([216,217,0,66,62],[],[0]),([218,0,66,62,5],[],[]),([219,0,220,195,5],[],[3]),([0,73,3,84,76],[],[0]),([81,0,61,66,28],[14],[0]),([142,0,61,66,83],[15],[0]),([0,208,75,37,5],[],[]),([77,221,0,66,3],[0],[]),([224,0,3,4,5],[],[]),([225,0,62,37,5],[],[]),([226,0,62,37,5],[],[]),([0,227,82,4,21],[],[]),([231,0,232,3,5],[],[1]),([144,0,61,66,40],[16],[0]),([77,0,61,233,3],[],[]),([234,0,1,235,5],[],[]),([0,66,37,236,5],[],[]),([176,0,158,3,84],[],[]),([77,238,0,61,3],[],[]),([239,0,66,37,5],[],[]),([0,61,73,40,100],[],[0]),([241,0,242,4,5],[],[3]),([0,73,3,4,101],[],[0]),([0,245,246,4,5],[],[]),([161,0,82,4,21],[],[]),([48,0,49,40,5],[],[0]),([0,208,28,4,75],[],[]),([0,27,3,4,5],[],[0]),([248,0,250,2,5],[],[]),([0,66,63,37,64],[],[0]),([0,66,251,252,76],[],[1]),([0,250,115,2,5],[],[]),([253,254,0,37,92],[],[2]),([65,0,66,3,4],[],[0]),([99,0,1,2,101],[],[0]),([176,1,2,3,256],[],[]),([77,0,66,3,143],[],[]),([193,0,1,257,5],[17],[3]),([65,0,1,2,37],[],[0]),([104,0,1,2,21],[],[0]),([259,0,1,260,5],[],[]),([262,0,263,4,5],[],[1]),([157,0,158,3,84],[],[]),([81,0,1,2,82],[],[0]),([176,1,266,2,3],[],[]),([78,0,61,66,80],[2,18],[0]),([0,79,1,2,80],[],[0]),([140,0,1,37,5],[],[0]),([0,250,2,267,5],[],[]),([8,11,13,0,5],[19,20],[0]),([268,0,2,137,37],[],[]),([269,8,209,0,3],[],[3]),([142,0,1,2,143],[],[0]),([187,0,188,28,21],[21],[1]),([0,51,3,53,5],[],[0,1]),([270,0,271,3,29],[],[1]),([216,0,61,66,272],[22],[]),([0,121,2,273,4],[],[2]),([274,58,0,4,5],[],[0]),([77,0,61,275,3],[0],[]),([52,0,51,28,21],[21],[0,1]),([185,186,52,0,51],[4],[1]),([77,56,0,1,57],[9,10],[0]),([0,179,4,276,5],[],[1]),([77,109,11,0,2],[],[0]),([77,56,0,179,1],[],[2]),([219,0,1,277,5],[23,24],[]),([157,278,0,66,84],[],[1]),([140,0,3,4,141],[],[0]),([248,0,249,279,5],[],[1]),([280,0,1,281,5],[],[]),([0,70,1,69,4],[],[0]),([145,8,11,0,5],[],[0]),([93,96,98,0,3],[],[0]),([147,93,11,0,4],[25,26],[0]),([0,149,3,151,4],[],[0]),([282,0,66,62,5],[],[]),([150,0,149,40,37],[11,27],[0]),([93,0,1,151,37],[],[0]),([47,0,1,284,5],[],[2]),([38,0,42,43,5],[],[0]),([88,0,89,40,5],[],[0]),([285,38,286,0,5],[],[0]),([291,0,1,37,5],[],[2]),([292,0,66,82,4],[],[]),([0,50,3,4,5],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_21_4 : checkNodesBT W_21 g_21 F_21 P_21_4 A_21 B_21_3 4 N_21_4 = true := by decide +kernel
def B_21_4 : BT (List (List Nat)) := buildBucketsBT W_21 N_21_4
set_option maxRecDepth 500000 in
lemma B_21_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_21 4 xs.toFinset) B_21_4 :=
  buildBucketsBT_sound (by decide) gp_21 W_21_ok (buildPoolsSubBT_sound S_21_ok) A_21_ok B_21_3_ok C_21_4
def U_21_5 : List Nat := ([1,3,8]++r 10 7++[18,19,21,22,24]++r 27 205)
def P_21_5 : BT (Option BoundPool) := buildPoolsSubBT 12 W_21 r_21 S_21 ps_21 U_21_5
def N_21_5_0 : List NodeSpec := [([154,0,1,156,4,5],[],[0]),([154,0,155,1,3,29],[8,28,29],[0,2]),([131,130,0,2,3,29],[],[0]),([154,0,1,271,3,29],[],[0]),([231,230,0,2,3,5],[],[0]),([174,169,0,1,3,5],[30,31],[0]),([48,0,49,3,4,5],[],[0]),([285,286,0,2,37,5],[],[0,2]),([0,42,2,43,37,5],[],[0,2]),([285,38,0,1,41,5],[],[0]),([38,0,1,41,43,5],[32,33],[0]),([48,47,0,1,40,5],[34,35],[0]),([293,0,1,2,37,5],[],[]),([253,254,0,2,37,5],[],[0,2]),([0,199,2,200,37,5],[],[0,2]),([294,0,2,137,37,141],[],[2]),([253,254,0,3,4,92],[],[0,2]),([0,199,3,200,4,92],[],[0,2]),([268,0,2,3,137,4],[],[0]),([93,0,296,1,3,4],[36,37],[]),([93,0,295,1,40,37],([8]++r 38 4),[2]),([210,209,0,2,40,37],[42,43,44],[0]),([210,0,211,40,3,4],[45],[0]),([297,93,0,1,3,4],[],[]),([298,0,1,149,3,4],[46],[]),([93,0,1,3,151,4],[],[0]),([222,150,0,149,3,4],[27,47,48,49],[]),([150,0,149,3,4,37],[50],[0]),([150,0,149,40,3,4],[45,46],[0]),([77,0,1,300,2,3],[],[]),([303,93,0,1,3,4],[],[]),([47,0,1,49,40,5],[34,35],[0]),([77,0,1,2,3,305],[],[]),([77,306,0,1,2,3],[],[]),([93,0,1,3,308,4],[],[]),([93,0,1,3,310,4],[],[]),([312,313,0,6,3,5],[],[2]),([315,0,1,3,311,5],[],[]),([0,9,244,246,4,5],[],[0,1]),([77,56,0,1],[8,10],[0,2]),([0,1,198,200,37,92],[51,52],[0]),([241,240,0,2,4,5],[],[0]),([261,0,1,263,4,5],[53,54],[0]),([270,0,271,3,4,5],[],[0,1]),([262,261,0,1,4,5],[53,54],[0]),([318,8,0,1,3,5],[],[]),([8,0,1,3,320,5],[],[]),([259,8,0,1,3,5],[55],[0]),([8,0,1,3,322,5],[],[]),([8,11,0,5],[8,19],[0,3]),([169,0,1,175,3,5],[30,31],[0]),([88,87,0,2,40,5],[],[0]),([8,0,1,325,3,5],[],[]),([93,0,1,3,327,4],[],[]),([328,8,0,1,3,5],[],[]),([8,0,1,329,3,5],[],[]),([0,121,2,4],[8,56],[0,2,3]),([330,331,0,2,288,5],[],[2]),([0,1,2,83,84,72],[],[0,1]),([332,333,77,0,61,3],[57,58],[]),([292,0,1,2,82,4],[],[0]),([1,2,3,255,252,76],[],[]),([0,61,227,28,4,21],[],[0,1]),([47,0,283,1,40,5],[59],[0,2]),([0,1,2,3,336,337],[],[]),([0,1,2,3,338,76],[],[]),([78,339,0,1,2,80],[18,60],[]),([340,0,1,2,37,5],[61],[]),([8,0,1,281,10,5],[62],[0]),([216,0,61,1,2,272],[63,64],[0]),([219,56,0,220,4,5],[65],[0,1]),([77,0,1,2,341,3],[],[]),([270,154,0,1,3,29],[],[0]),([144,0,61,1,2,40],[66,67,68],[0]),([157,278,0,61,66,29],[69],[0,1]),([77,342,343,0,61,3],[57],[]),([0,1,2,37,101,212],(r 70 4),[0]),([344,293,1,2,37,5],[],[]),([345,346,0,82,4,21],[74],[]),([239,0,1,2,37,5],[],[0]),([193,347,0,1,4,5],[75,76,77],[]),([216,217,0,1,2,62],[],[0]),([77,0,348,1,2,3],[78,79],[]),([8,0,349,1,3,5],[],[]),([202,0,1,2,37,5],[],[0]),([1,2,3,84,256,76],[80],[0]),([280,0,1,3,260,5],[81],[]),([214,215,0,1,2,37],[],[0]),([0,1,2,63,37,64],[],[0]),([216,0,66,62,37,5],[],[0]),([218,0,1,2,62,5],[],[0]),([93,0,1,149,40,37],[82],[0]),([0,61,73,3,4,100],[],[0]),([350,96,0,2,3,5],[],[]),([99,0,61,66,37,5],[83,84],[0]),([351,93,0,1,3,4],[],[]),([0,66,63,62,37,5],(r 85 4),[0]),([77,352,0,1,2,3],[],[]),([0,208,3,4,75,5],[],[0]),([0,61,208,74,37,5],[],[0]),([282,0,1,2,62,5],[],[0]),([293,353,1,2,37,5],[],[]),([171,0,61,227,3,5],[],[]),([0,61,66,173,4,21],[89,90],[0]),([176,0,1,2,3,72],[91,92],[]),([0,1,2,251,252,76],[],[0,1]),([77,162,0,1,2,3],[57,78,79,93],[0]),([0,61,73,28,4,21],[21],[0,1]),([176,278,0,1,2,3],[],[]),([216,0,1,2,66,272],[],[0]),([157,0,66,3,84,76],[94,95,96],[0,1]),([355,0,66,3,62,5],[],[0]),([162,0,66,3,4,5],[97],[]),([183,182,0,61,66,4],[98],[0]),([77,0,61,66,3,80],([57]++r 99 4),[0]),([356,77,0,61,3],[57,80,103,104],[]),([131,0,132,3,4,5],[],[0,1]),([77,357,0,1,2,3],[],[]),([261,0,358,1,4,5],[],[2]),([81,0,61,66,3,5],[105],[0]),([193,56,0,1,359,5],[77,106],[]),([77,0,61,158,3,76],[80,107],[]),([361,0,66,3,84,5],[],[]),([362,1,2,363,4,21],[],[]),([77,0,1,2,275,3],[102,108],[0]),([280,0,1,324,3,5],[],[]),([77,0,61,66,83,3],[102,109],[0]),([185,52,0,51,3,5],[110],[0]),([162,0,66,28,4,21],[21],[1]),([368,0,1,2,3,4],[],[]),([1,369,2,37,5,212],[],[]),([197,0,1,2,3,76],[],[0]),([0,66,40,37,101,5],[11,111],[0]),([0,61,66,40,100,72],[112],[0]),([0,1,2,73,40,100],[],[0]),([77,0,61,66,3,72],[57,99,100,102,113],[0]),([356,77,0,61,3,76],[57,80,104],[]),([157,278,0,1,2,84],[],[0,1]),([215,0,66,62,37,5],[],[0]),([144,0,61,66,3,4],[114],[0]),([353,61,66,37,5,212],[115],[]),([206,0,1,3,4,5],[],[0]),([77,265,264,1,2,3],[79],[]),([8,0,1,370,3,5],[],[]),([222,210,0,211,3,4],[12,49,116,117],[]),([0,1,2,37,371,212],[71,118],[]),([183,339,0,1,2,184],[3,60],[]),([8,0,1,372,3,5],[119,120],[]),([0,1,2,62,100,72],[],[0]),([362,0,66,82,4,21],[74,121,122],[1]),([171,278,0,61,66,5],[123],[]),([214,215,0,66,3,4],[],[0]),([77,373,0,1,2,3],[],[]),([93,96,0,3],[8,124],[0,1,2]),([374,0,1,3,260,5],[81],[]),([216,171,0,61,66,3],[125],[]),([0,66,62,37,5,64],[85,86,87,126,127],[0]),([177,176,77,1,2,3],[79],[0]),([234,0,124,1,3,5],[128],[]),([0,61,73,40,37,5],[11,129],[0]),([1,2,3,84,376,76],[80],[]),([8,0,1,377,3,5],[],[1]),([0,61,66,28,74,72],[130],[0,1]),([379,1,380,2,3,5],[],[]),([171,0,61,158,3,5],[],[]),([381,382,0,61,37,5],[],[]),([0,66,62,100,37,5],[85,86,87,131],[0]),([193,0,383,1,195,5],[],[2,3]),([384,56,0,1,385,5],[8,76],[]),([386,209,0,2,3,4],[132,133],[]),([0,1,389,387,4,5],[],[2]),([217,0,66,62,37,5],[],[0]),([171,182,0,61,66,4],[134],[]),([225,0,61,40,37,5],[11,135],[0]),([162,0,73,3,4,5],[136],[]),([0,66,3,84,252,76],[],[0]),([144,0,1,2,66,40],[],[0]),([185,186,52,8,0,1],[137,138],[0,1]),([261,58,0,1,4,5],[53,54,106,139],[]),([0,66,28,4,75,21],[],[0,1]),([163,164,0,1,2,76],[],[0,1]),([216,0,61,208,3,4],[],[]),([161,0,3,82,4,5],[140],[0]),([38,0,42,1,41,5],[32,33,141,142],[0]),([390,11,0,2,4,5],[143],[]),([0,66,62,37,5,72],[85,86,87,144],[0]),([176,375,1,2,3,76],[],[]),([226,0,3,62,4,5],[],[0]),([77,0,1,392,2,3],[93,101,102],[]),([77,0,1,393,2,3],[93,102,113],[]),([298,326,0,1,3,4],[46,145,146],[]),([0,165,3,4,84,5],[147],[0]),([0,66,3,75,5,72],[148],[0]),([171,0,61,1,2,173],[149,150],[0]),([185,187,0,188,3,5],[110],[0]),([0,66,3,63,4,64],[],[0]),([162,394,66,3,4,5],[151],[]),([77,0,61,66,237,3],[57,99,100,152],[0,1]),([171,0,66,82,4,21],[],[1]),([81,339,0,1,2,28],[14],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_21_5_0 : checkNodesBT W_21 g_21 F_21 P_21_5 A_21 B_21_4 5 N_21_5_0 = true := by decide +kernel
def N_21_5_1 : List NodeSpec := [([78,77,0,61,66,3],[102,153],[0]),([157,0,61,158,3,29],[],[0,1]),([77,395,0,1,2,3],[],[]),([77,0,1,2,73,3],[102,108],[0]),([0,61,396,37,5,212],[154],[]),([77,0,61,158,3],[80,107,155],[]),([0,66,3,4,101,72],[],[0]),([162,397,66,3,4,5],[156],[]),([99,0,1,2,66,100],[],[0]),([398,162,66,3,4,5],[157],[]),([193,0,1,277,5],[8,24],[0,2,3]),([65,0,1,2,3,4],[],[0]),([402,0,1,2,3,4],[],[]),([8,0,1,3,403,5],[158],[2]),([0,61,66,100,37,212],[71,118,159],[0]),([0,61,208,4,404,5],[],[]),([162,0,208,3,4,5],[],[]),([142,0,61,66,3,76],[90,160],[0]),([210,0,211,3,4,37],[50],[0]),([0,66,83,3,84,76],[],[0,1]),([150,93,0,1,40,37],[161,162],[0]),([185,8,0,1,235,5],[],[]),([0,61,223,3,4,5],[],[0]),([169,0,405,1,3,5],[163],[0,2]),([88,0,89,3,4,5],[],[0]),([0,66,143,37,5,76],[164,165,166],[1]),([163,164,0,66,4,5],[],[0,1]),([0,66,251,3,84,76],[94,95,96,167],[0,1]),([77,0,1,2,3,143],[168],[0]),([176,0,66,3,84,76],[91,94,95,96,169,170],[0]),([99,0,61,1,2,100],[171,172,173],[0]),([0,1,2,3,407,408],[],[]),([0,66,3,84,76,72],[94,95,96,174],[0]),([177,176,1,2,3,76],[],[0]),([8,0,409,1,3,5],[],[]),([176,77,375,1,2,3],[175],[]),([411,11,0,2,4,5],[],[]),([412,1,414,2,28,4],[],[1]),([77,0,1,2,3,415],[78,79],[]),([183,0,61,1,2,184],[176,177,178],[0]),([176,1,2,3,255,76],[],[0]),([81,0,1,2,66,28],[],[0]),([176,265,1,2,3,76],[],[0]),([171,0,61,73,3,5],[],[]),([104,0,1,2,3,5],[],[0]),([142,264,0,1,2,3],[179],[]),([78,0,1,2,66,80],[180],[0]),([219,193,0,1,195,5],[181,182],[0]),([0,1,2,37,236,5],[183],[0]),([332,77,343,0,61,3],[57],[]),([176,416,77,1,2,3],[175],[]),([176,0,1,2,3,76],[],[]),([216,0,61,73,3,4],[],[]),([216,0,61,66,37,212],[184],[]),([8,0,1,28,170,5],[62,185,186],[]),([176,0,1,2,3,80],[102,108,168],[]),([183,417,0,1,2,4],[187,188],[]),([419,96,0,2,3,5],[],[]),([193,56,0,1,421,5],[77,189,190],[]),([0,66,3,37,101,76],[],[]),([78,0,61,1,2,80],[168,176,191,192],[0]),([77,0,1,2,233,3],[],[0]),([216,339,0,1,2,272],[22],[]),([261,0,1,57,4,5],[53,54,76],[]),([77,221,0,1,2,3],[57,78,79,93],[0]),([8,0,1,260,258,5],[55],[0]),([0,61,208,28,74,4],[],[0]),([77,264,375,1,2,3],[193],[]),([77,0,422,1,2,3],[78,79],[]),([140,0,1,3,4,5],[],[0]),([0,1,2,28,75,72],[],[0,1]),([171,0,61,423,3,5],[],[]),([248,247,0,249,2,5],[],[0,2]),([142,0,61,1,2,83],[179,194,195],[0]),([332,333,0,61,3,76],[58],[]),([81,0,61,1,2,28],[196,197,198],[0]),([0,426,1,2,4,5],[],[]),([0,1,2,208,173,4],[],[0]),([183,0,1,2,66,184],[180],[0]),([77,238,0,1,2,3],[],[0]),([427,182,0,1,2,4],[],[]),([0,1,2,73,28,74],[],[0]),([77,0,79,1,2,3],[168],[0]),([77,428,0,1,2,3],[],[]),([0,199,1,198,37,92],[8,51,52,199],[0,2]),([429,0,2,3,418,5],[200],[]),([142,0,1,2,66,83],[],[0]),([157,77,0,61,66,3],[57,99,100,201],[0]),([0,61,66,272,37,5],[83,202],[0]),([171,0,1,2,66,173],[],[0]),([274,56,0,1,4,5],[189,203,204],[0]),([0,1,2,3,430,76],[],[]),([99,339,0,1,2,100],[13],[]),([144,339,0,1,2,40],[16],[]),([93,0,1,3,431,4],[],[]),([77,0,1,2,3,432],[],[]),([248,11,0,279,4,5],[],[0,3]),([77,0,1,2,3,433],[],[]),([142,339,0,1,2,83],[15],[]),([8,434,0,1,3,5],[],[]),([416,77,264,1,2,3],[78,205],[]),([384,109,0,110,4,5],[206],[1]),([171,339,0,1,2,173],[1],[]),([435,8,0,1,235,5],[207],[]),([193,56,0,1,436,5],[76,77],[]),([52,234,0,1,3,5],[8,128],[0]),([8,0,1,235,5,21],[55],[0]),([52,0,51,28,3,5],[62,128,208,209,210],[0,1]),([52,0,51,3,5,21],[209,210,211],[0]),([193,437,0,1,4,5],[77,212],[]),([384,58,0,57,4,5],[206],[1]),([8,0,1,3,53,5],[119,120,213],[0]),([176,416,1,2,3,76],[],[]),([52,8,0,1,28,21],[55,214,215],[0,1]),([438,8,0,1,3,5],[],[]),([253,0,1,198,37,92],[],[0]),([0,61,73,83,4,5],[],[1]),([439,56,0,1,4,5],[106,189,204],[]),([280,15,0,1,3,5],[8,216],[0]),([216,217,0,61,66,40],[217],[0]),([8,0,1,51,28,21],[214,215],[0,1]),([0,208,82,4,21],[80,218,219,220],[0,1]),([8,0,1,440,3,5],[119,120],[]),([185,186,8,0,1,51],[137,138],[0,1]),([163,0,66,3,84,76],[],[0]),([435,8,0,1,441,5],[221],[]),([187,0,188,28,3,5],([208]++r 222 4),[0,3]),([187,0,188,3,5,21],[211,222,223,224],[0,3]),([0,1,2,40,101,72],[],[0]),([319,0,1,3,260,5],[],[]),([8,0,1,3,126,5],[226],[1]),([93,0,1,442,3,4],[],[]),([261,180,0,1,4,5],[76,227],[]),([162,0,66,40,37,5],[11,228],[0]),([77,0,1,2,3,443],[78,79],[]),([187,96,0,2,28,21],[],[0,1]),([0,61,159,3,4,5],[],[0]),([185,186,187,96,0,2],[],[0,1]),([261,0,179,1,4,5],[106],[]),([8,0,124,1,28,21],[],[1,2]),([8,444,0,1,3,5],[],[]),([214,0,66,62,37,5],[],[0]),([185,186,8,0,124,1],[],[1,2]),([193,445,0,1,4,5],[76,77,229],[]),([93,0,1,3,446,4],[],[]),([0,66,251,4,252,5],[230],[0,1]),([193,447,0,1,4,5],[77,106,231],[]),([193,0,1,220,195,5],[],[0,2]),([8,0,1,448,3,5],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_21_5_1 : checkNodesBT W_21 g_21 F_21 P_21_5 A_21 B_21_4 5 N_21_5_1 = true := by decide +kernel
def N_21_5 := N_21_5_0 ++ N_21_5_1
def B_21_5 : BT (List (List Nat)) := buildBucketsBT W_21 N_21_5
set_option maxRecDepth 500000 in
lemma B_21_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_21 5 xs.toFinset) B_21_5 := by
  have hP := buildPoolsSubBT_sound (pdepth := 12) (W := W_21) (raw := r_21) (pspecs := ps_21) (used := U_21_5) S_21_ok
  have hm0 := checkNodesBT_mem (by decide) gp_21 W_21_ok hP A_21_ok B_21_4_ok C_21_5_0
  have hm1 := checkNodesBT_mem (by decide) gp_21 W_21_ok hP A_21_ok B_21_4_ok C_21_5_1
  exact buildBucketsBT_of_mem (forall_append (hm0) hm1)
def U_21_6 : List Nat := ([0,2,8,29,31,32,35,36,37,39,40,41,44,46,48,50,51,53,55,57,58,59,61,62,64]++r 67 8++r 76 9++[86,87]++r 89 5++r 95 5++[101,102,105,106,108,109]++r 112 4++[117,118,119,123,125,127,128,130,134,136,138,142,143,150,152,153,156]++r 160 4++[165,168,169,172,175,178,182,184,185,188,189,190,192,193,195,197,200,201,202,210,211,215,217,220,222,224,225,230]++r 232 527)
def P_21_6 : BT (Option BoundPool) := buildPoolsSubBT 12 W_21 r_21 S_21 ps_21 U_21_6
def N_21_6_0 : List NodeSpec := [e6 [412] [232,233],([154,0,155,1,3,4,5],[8,40,234,235],[0,2]),([154,0,1,271,3,4,5],[],[0]),([270,154,0,1,3,4,5],[],[0]),([81,0,1,2,28],[8,197],[0,2]),([142,0,1,2,83],[8,195],[0,2]),([77,449,0,1,3],[8,93,236],[]),([77,0,450,2,3],[8,102,237],[]),([332,333,0,1,2,3,76],[8,102,108],[0]),([77,451,0,1,3],[8,93,238],[]),([77,0,452,2,3],[8,102,239],[]),([332,0,1,453,3],[8,93,108,240],[3]),([332,333,77,0,1,2,3],[8,57,93,102,108],[0]),([455,182,0,1,2],[8,241,242],[]),([77,0,457,1,2],[8,57,243],[]),([77,0,459,2,3],[8,93,244],[]),([332,460,77,0,1,2,3],[8,57,58,93,102,108],[]),([460,0,456,2,3],[8,57,102,245],[1]),([460,77,342,0,1,2,3],[8,57,93,102,108,246],[]),([77,342,343,0,1,2,3],[57,93,102,108],[0]),([462,182,0,1,2],[8,242,247],[]),([77,0,1,2,463],[8,57,248],[]),([77,464,0,1,3],[8,93,249],[]),([77,0,465,2,3],[8,93,250],[]),([332,77,0,128,1,2,3],[8,57,58,93,102,108,251],[]),u6 [159] [252,253],([466,56,0,1,4,5],[8,76,77,106,189,190,254,255],[]),([0,1,2,73,3,4,100],[],[0]),([216,0,1,2,208,3,4],[],[0]),([0,1,2,208,74,37,5],[],[0]),([216,0,1,2,66,37,212],[71],[0]),([8,0,124,1,28,3,5],[55,62,81,128,185,256],[0,1,2]),([0,1,2,396,37,5,212],[71,257],[0]),([0,61,468,3,467,4,5],[80,258],[]),([81,0,61,1,2,3,5],([8]++r 259 4),[0]),([0,1,2,3,75,5,72],[263,264],[0]),([0,1,2,288,290,37,5],(r 265 5),[2]),([0,61,1,469,3,4,5],[8,40,270,271],[]),([332,77,0,61,1,3,76],[8,57,58,80,108,272],[0]),([0,61,66,28,4,21,72],(r 273 5),[0,1]),([471,8,0,1,3,5],[8,55,81,119,128,278],[]),([144,0,1,2,66,3,4],[],[0]),([0,61,423,3,4,5,21],[80,83,279,280,281],[0]),e6 [293] [232,233,282],([412,0,1,2,3,4,473],[61],[]),([176,0,1,2,3,76],[91,92,283],[0]),([474,0,128,2,3],[8,284,285],[]),([302,182,345,0,1,2,4],[8,286,287,288],[1]),([176,77,0,1,2,3],[57,78,79,93,102,108,168,175,261],[0,1]),([78,77,0,1,2,66,3],[57,93,102,108,168,261],[0]),([412,0,1,2,475,4,5],[61],[]),([171,182,0,61,1,2,4],[8,40,287,289],[0,1]),([424,0,1,2,425,4,5],[],[0]),([0,1,2,3,406,408,21],[],[0]),([261,0,1,4,5],[53,77,190],[0,2]),([142,0,61,1,2,3,76],[8,261,290,291,292],[0]),([77,342,0,61,1,3,76],[8,57,80,108,246,293],[0]),([0,61,66,83,37,5,76],[165,294,295,296],[0,1]),([476,77,0,1,2,3],[8,57,79,93,102,108,168,297],[]),([176,77,0,1,2,3,76],[78,79,102,175],[0]),([416,77,61,1,2,3,76],([40,78,80]++r 298 4),[0]),([449,0,1,478,3,4,5],[302],[]),([216,171,0,61,1,2,3],[261,303,304,305],[0]),([171,278,339,0,1,2,5],[123],[]),([171,0,1,2,173],[8,150],[0,2]),([460,304,77,0,1,2,3],[8,57,93,102,108,306],[]),([302,182,479,0,2],[8,242,287,307],[3]),([183,182,0,61,1,2,4],[8,40,287,308],[0]),([8,0,1,3,480,5],[55,62,128,185],[]),([8,0,9,10,5],[8,81,128,309],[0]),([330,0,1,2,288,37,5],[310,311,312],[0,2]),([171,412,0,1,2,28,4],[313,314],[1]),([412,0,1,2,28,4,72],[276,314,315],[1]),([77,0,1,2,66,237,3],[57,168,316,317],[0,1]),([0,1,2,137,139,37,5],[267,318,319,320],[2]),([77,264,0,1,2,3],[57,78,93,102,168,193,261,321],[0]),([481,93,0,1,3,4],[8,37,322,323,324],[]),([187,482,96,0,2,3,5],[8,222,225,325,326],[]),([280,8,0,1,3,5],[8,55,62,81,119,128,327],[0,1]),([0,1,2,251,4,252,5],[230],[0,1]),([298,93,0,1,3,4],[37,46,161,322,324,328],[0]),([176,0,1,2,3,84,76],([91,92,96,283]++r 329 4),[0]),([339,0,1,2,28,74,72],[130],[0,1]),([150,93,0,1,40,3,4],[46,161],[0]),([353,1,2,66,37,5,212],[333],[0]),([157,278,0,1,2,66,29],[],[0,1]),([345,162,0,1,3,4,5],[334],[]),([0,61,1,2,272,37,5],([8]++r 335 5),[0]),([285,0,1,2,41,37,5],[340],[0]),([150,0,149,3,4],[46,48,97,322],[0,1]),([0,1,2,3,84,76,72],[96,329,330,331,341,342],[0]),([384,0,61,483,3,4,5],[343],[]),([193,180,56,0,1,4,5],[76,77,106,255],[0]),([0,1,2,83,3,84,76],[],[0]),([77,342,0,61,1,3],[8,80,93,108,246,293],[2]),([413,412,1,2,28,4,21],[344,345],[0,1]),([0,1,2,3,37,486,5],[61],[]),([394,334,1,2,4,5,21],[],[]),([157,0,1,2,3,84,76],[96,329,330,331,341,342],[0]),([412,1,414,2,3,4,5],[232,346,347],[0]),([394,1,2,3,4,488,5],[],[]),([413,1,2,3,4,489,5],[348,349,350],[]),([171,0,1,2,82,4,21],[],[0,1]),([0,199,2,3,200,4,5],[351],[0,2]),([345,0,1,82,4,21],[74,80,315,352,353,354],[0]),e6 [490] [232,233,252],([356,77,0,1,2,3,76],[57,80,355],[0]),([222,345,346,0,61,4,5],[],[]),([394,1,2,82,4,21],([80,300]++r 356 5),[1]),([362,1,2,3,363,4,5],[348,361,362],[0]),([353,61,66,3,4,5,212],(r 363 4),[0]),([163,0,66,3,4,84,5],[367],[0]),([222,491,0,1,2,4,5],[61],[]),([0,422,1,2,3,29,76],[368,369,370],[0]),([332,77,0,1,2,3,10],[8,57,93,108],[0]),([0,492,1,2,28,4,311],[8,40,277,371],[]),([144,0,1,2,40],[8,67],[0,2]),([412,0,1,2,3,4,408],[61],[]),([0,61,396,3,4,5,212],[271,365,372],[0]),([0,334,1,2,494,4,5],[],[]),([216,217,0,61,66,3,4],[373],[0]),([0,1,2,28,4,75,21],[314],[0,1]),([0,1,393,2,28,4,21],[275,276,371],[1]),([15,8,0,1,3,10,5],[8,55,62,81,128,185],[0]),([0,334,1,2,3,336,5],[80,374],[0]),([222,412,0,1,2,4,5],[],[]),e6 [491] [232,233],([144,0,61,1,2,3,4],[40,68,261,375,376,377],[0]),([8,0,3,495,5],[55,81,128,378],[]),([77,0,61,1,2,237,3],[57,93,102,108,168,261,298,379,380,381],[0,1]),([496,497,0,61,3,4,5],[271],[]),([449,162,0,1,3,4,5],[80,136,382],[]),([0,1,2,3,4,101,72],[],[0]),([0,1,2,3,499,4,500],[],[1]),([501,0,1,2,3,399,5],[],[]),([171,0,450,2,66,3,5],[383],[]),([412,0,1,2,74,37,5],[61,384,385],[]),([0,61,1,2,40,100,72],[338,386,387,388],[0]),([412,0,1,2,4,37,5],[61],[]),([0,61,66,3,502,5,76],[90,389,390],[]),u6 [223] [252,253],([345,346,0,61,28,4,21],[277,354],[0,1]),([222,0,61,208,4,5,21],[391],[0]),([345,0,1,504,4],[8,315,392,393],[]),([0,61,66,37,5,21,76],[83,90,394],[]),([8,0,1,3,235,5],[8,55,62,81,119,128,395],[0,1]),([77,0,61,1,2,3,72],[8,57,93,102,108,261,298,381,396,397],[0]),([394,61,66,3,4,5,72],([365]++r 398 4),[0]),([171,0,61,66,28,4,21],[402],[0,1]),([0,61,66,3,4,5,72],[252,271,363,365,403,404],[0]),([216,0,1,2,272],[8,64],[0,2]),([77,375,61,1,2,3],[8,40,80,261,298,300,405,406],[0]),([216,0,61,66,3,4,72],[363,407],[0,1]),([77,0,1,2,158,3],[57,80,168,261,408],[0]),([505,412,0,1,2,37,5],[61],[]),([0,61,66,28,74,4,21],[276,409],[0,1]),([8,0,1,51,28,3,5],[55,62,128,185,410,411,412],[0,1]),([357,0,1,2,3,29,76],[],[0]),([0,66,3,4,37,101,5],[50,90],[0,1]),([0,1,2,73,40,37,5],[267,413,414],[0]),([248,247,11,0,2,4,5],[143,415],[0,2]),([225,0,1,2,40,37,5],[338,416],[0]),([171,0,61,66,3,4,5],[417],[]),([0,66,3,62,4,5,64],([83,390]++r 418 4),[0,1]),([162,394,1,2,3,4,5],[233,261],[0]),([412,394,1,2,3,4,5],[422],[]),([193,67,56,0,1,4,5],[8,77,190],[0]),([0,61,208,4,37,5,21],[423,424],[0]),([171,278,0,61,1,2,5],[8,425,426,427],[0]),([77,0,61,1,2,3,80],[8,57,93,102,108,261,298,381,428,429],[0]),([0,1,2,63,62,37,5],[8,87,267,413,430,431,432],[0]),([171,0,1,2,73,3,5],[383,433],[0]),([416,77,61,1,2,3],([40,78,80,261]++r 298 4++[434]),[0]),([0,1,2,73,28,4,21],[276,315],[0,1]),([99,0,1,2,100],[8,172],[0,2]),([0,61,66,3,4,100,72],[435],[0]),([216,0,61,66,3,4,5],[436],[]),([216,0,1,2,62,37,5],[437],[0]),([345,346,394,61,3,4,5],[261,401],[]),([157,0,1,2,506,4,5],[252,261],[1]),([187,96,0,2,3,5,21],[8,222,438,439],[0,2]),([1,2,3,84,255,76],[80,300,329,440,441,442],[0,1]),([225,0,61,3,4,37,5],[50],[0]),([0,61,208,3,4,5,72],[185,443,444,445],[0,1]),([1,2,3,363,4,103,5],[446],[1]),([460,77,0,1,2,3,55],[8,57,93,102,108,168,261],[2]),([216,384,0,61,66,3,4],[90,447],[]),([171,0,61,66,37,5,21],[83,448],[]),([157,278,339,0,1,2,29],[69],[1]),([171,0,61,66,3,5,72],[363,383,417],[0]),([77,0,1,2,66,3,80],[8,57,93,102,108,316,317],[0]),([52,0,51,3,5],[62,97,128,210],[0,1]),([193,56,316,0,1,4,5],[8,76,106,255],[0,2]),([0,61,66,37,5,212],[2,71,83,449,450,451],[0]),e6 [507] [232,233,271,452,453],([171,339,0,1,152,3,5],[],[]),([307,326,93,0,1,3,4],[40,46,80,161,322,454,455],[]),([222,278,0,61,66,4,5],[83,456],[1]),([150,508,93,0,1,3,4],[46,80,261,322,324,457,458],[]),([216,0,61,66,40,37,5],[2,83,459,460],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_21_6_0 : checkNodesBT W_21 g_21 F_21 P_21_6 A_21 B_21_5 6 N_21_6_0 = true := by decide +kernel
def N_21_6_1 : List NodeSpec := [([215,0,66,3,62,4,5],[],[0]),([185,0,61,66,37,5,76],[83,90,461],[]),([216,217,0,1,2,66,40],[],[0]),([509,0,1,2,3,5,76],[],[]),([157,77,0,1,2,66,3],[57,168,316,317],[0]),([215,0,1,2,62,37,5],[8],[0]),([334,1,380,2,4,5,21],[],[]),([394,1,2,3,4,407,5],[40],[]),([222,394,61,66,4,5,21],[462],[]),([0,66,62,37,5],[86,87,127,267],[0]),([185,484,0,61,66,37,5],[83,90,463],[]),([8,0,1,3,317,5],[55,128,185,464],[0,1]),([47,0,1,40,5],[8,35,59,465],[0,2]),([0,61,66,3,100,37,76],[466],[0]),([510,8,316,0,3],[8,62,128,467],[2]),([394,61,66,4,37,5,21],[468,469,470],[]),([511,0,1,324,3],[8,55,471],[3]),([379,0,334,1,2,3,5],[472],[0]),([171,0,61,66,3,37,5],[83,448],[0]),([217,0,61,66,40,37,5],[473,474],[0]),([157,0,61,158,3,4,5],[475,476],[0]),([8,0,1,3,258,5],[8,62,185,477],[0,3]),([78,77,0,61,1,2,3],[102,168,478,479,480],[0]),([157,77,0,61,1,2,3],[57,93,102,108,168,261,298,381,481,482],[0]),([185,264,0,1,2,37,5],[61],[]),([183,0,1,2,184],[8,178,483],[0,2]),([222,0,61,158,3,4,5],[80,475,476,484],[0]),([398,162,1,2,3,4,5],[80,232,300],[0]),([216,0,61,66,3,4,21],[90,485],[0]),([185,0,61,66,512,4,5],[90,486],[]),([0,1,2,66,272,37,5],[8,40,487],[0]),([77,264,0,1,2,3,76],[78,79,102,193,321],[0]),([0,1,2,66,40,100,72],[8],[0]),([222,0,61,66,467,4,5],[83,488],[]),([362,0,1,2,82,4,21],[74,276,315,352,356,357,489],[0,1]),([0,61,208,28,4,21],[80,220,424,490],[0,1]),([513,493,0,1,2,3,4],[],[1]),([77,0,61,66,3,76],[0,80,99,102],[0,1]),([157,0,61,66,3,29,76],(r 491 4),[0,1]),u6 [162] [232,233,271,452],([0,66,3,82,4,103,5],[390,495],[1]),([163,164,0,1,2,4,5],[],[0,1]),([77,0,1,2,3,514],[8,57,93,102,108,496],[]),([0,1,2,515,212],[8,71,497],[]),([410,353,1,2,37,212],[8,70,333,498,499],[]),([216,0,61,66,3,37,76],[90,500],[]),([171,394,61,66,3,4,5],[501],[]),([216,0,61,1,2,37,212],[8,40,502],[0]),([1,380,2,3,4,5,337],[],[0]),([511,52,8,0,1,3,5],[8,55,62,128,185,503,504],[]),([394,61,208,3,4,5,21],[80,401,443],[]),([0,66,3,63,62,4,5],[83,390,418,419,421,505],[0]),([460,77,391,0,2,3,76],[8,57,300,506],[]),([0,61,208,3,4,5,76],[185,424,443,444,507],[1]),([162,0,1,2,40,37,5],([61,465]++r 508 4),[0]),([416,77,323,1,2,3],[8,78,299,301,512,513,514],[]),([410,382,0,1,2,37,212],[8,71],[]),([381,382,0,61,3,4,5],[271],[0]),([0,1,2,66,100,37,212],[8,40,71,72,515],[0]),([185,0,61,158,3,4,5],[516],[]),([412,0,1,2,512,4,5],[61],[]),([162,0,1,2,28,4,21],[277,344,370,371,517],[0,1]),([171,0,61,208,3,4,5],[],[]),([449,516,162,0,3,4,5],[518,519,520],[]),([77,0,61,1,2,83,3],[102,168,521,522,523],[0]),([361,0,1,2,3,84,5],[],[0]),([293,0,1,2,37,5],[8,524],[0]),([0,61,66,3,4,517,76],[90,390,525],[]),([429,96,0,2,3,5],[200,225,325,526,527],[0,1,2,3]),([412,394,1,2,4,37,5],[528],[]),([162,0,66,3,4,37,5],[50],[0]),([81,0,1,2,66,3,5],[],[0]),([0,1,2,40,37,101,5],[61,465,508,509,510,529,530],[0]),([518,77,0,1,2,3],[8,57,79,93,102,108,168,531],[]),([0,61,1,2,173,4,21],[8,40,290,532,533],[0,1]),([77,0,1,2,3,519],[8,57,102,534],[]),([361,0,365,1,2,3,5],[535],[]),([8,0,136,3,141],[8,55,536],[2]),([176,264,0,1,2,3,76],[370,537,538],[0]),([0,335,1,2,3,4,337],[],[0,1]),([0,61,66,40,37,5,72],([267,510]++r 539 4),[0]),([302,182,394,1,2,4],([8]++r 543 4),[]),([491,521,1,2,3,4,5],[547],[]),([0,61,73,3,4,37,5],[50],[0]),([93,0,295,1,40,3,4],[40,46,161,261,322,324,548,549],[0,2]),([0,61,73,3,4,5,21],[211,271,365,550],[0,1]),([0,61,66,3,485,37,5],[83,551],[]),([8,0,1,3,281,5],[8,55,62,128,552],[0,1]),([0,522,55,95,5],[8,553,554],[]),([0,1,2,62,37,5,64],[8,87,430,431,432,555],[0]),([0,1,2,3,63,4,64],[],[0]),([77,342,0,1,2,3,10],[8,57,93,108],[2]),([513,1,380,2,3,4,5],[556],[]),([294,0,1,2,137,37,5],[],[0,2]),([339,0,1,2,40,100,72],[112],[0]),([449,516,0,61,3,4,5],[271,519,520],[]),([339,0,1,2,173,4,21],[89,557],[0]),([216,0,1,2,73,3,4],[],[0]),([214,0,1,2,62,37,5],[8],[0]),([157,77,339,0,1,2,3],[93,108,168,201,558,559],[0]),([0,61,227,3,4,5,21],[469,560,561],[0]),([0,61,66,3,523,5,76],[83,562],[1]),([78,0,1,2,80],[8,168,192,483,563],[0,2]),([77,0,1,2,158,3,76],[80,408],[0]),([460,77,391,0,2,3],[8,57,93,102,300,506],[]),([294,0,2,3,137,4,141],[],[0,2]),([345,346,0,61,3,4,5],[271],[]),([185,278,0,61,66,4,5],[90,564],[]),([162,0,66,3,4,5],[97,136,565,566],[0]),([524,93,0,1,3,4],[8,37,46,161,324,567],[]),([157,278,0,61,66,4,5],[568],[0,1]),([355,0,1,2,3,62,5],[],[0]),([93,0,295,1,3,4,37],[8,40,46,569,570],[0,2]),([0,1,2,62,100,37,5],[87,267,413,430,431,432,571],[0]),([162,0,66,3,4,5,21],[211,334,572],[0]),([0,61,66,83,4,5,72],[573,574],[0,1]),([0,1,2,73,83,4,5],[574,575],[0,1]),e6 [526] [252,452],([0,61,1,2,100,37,212],[71,72,73,338,576,577,578],[0]),([491,0,1,2,4,37,5],[61],[]),([362,0,66,3,82,4,5],(r 579 4),[0,1]),([214,215,0,1,2,3,4],[],[0]),([222,93,0,1,149,3,4],[82,322,324,583,584],[0,1]),([293,353,1,2,3,4,5],[585],[0]),([353,61,1,2,37,5,212],[8,70,586],[0]),([77,0,1,525,2,3,76],[300,587],[]),([222,413,412,1,2,4,5],[],[]),([1,369,2,3,4,5,212],[80,232,300,588,589],[0]),([8,0,136,1,3,260,5],[8,55,185],[0,2]),([162,397,1,2,3,4,5],[590,591,592],[0]),([154,0,1,3,29],[8,29],[0,2]),([293,0,1,2,37,5,212],[61,70,338,524,593],[0]),([381,0,61,1,37,5,212],[8,71],[0]),([77,527,0,1,3],[8,93,594],[]),([0,66,3,143,4,5,76],[165,595,596],[0,1]),([424,264,0,1,2,37,5],[597,598],[]),([214,0,66,3,62,4,5],[],[0]),([397,61,66,3,4,5,72],[156,363,365,591,599],[0]),([99,0,61,1,2,37,5],[8,40,339,600,601],[0]),([171,339,0,1,477,3,5],[],[]),([345,0,334,1,4,5,21],[],[]),([460,77,375,1,2,3],([8,78,300,405,406]++r 602 4),[]),([216,217,0,61,1,2,40],[606,607,608],[0]),([0,66,251,3,4,84,5],([83,90]++r 609 5),[0,1]),([505,413,1,2,3,4,5],[],[]),([77,342,0,128,1,2,3],[57,93,102,108,246],[]),([0,1,3,528,5],[55,81,185,614],[]),([0,1,2,3,529,5,21],[40,615,616],[]),([412,0,1,2,37,5,76],[282],[]),([171,0,1,2,423,3,5],[],[0]),([222,0,1,2,506,4,5],[252,261],[1]),([171,412,0,1,2,37,5],[61],[]),([77,0,1,2,3,243],[8,57,93,108,617],[]),([0,1,2,208,4,404,5],[],[0]),([163,0,1,2,3,84,76],[],[0]),([302,182,0,1,22,2,4],[8,242,286,287,288],[3]),([384,0,61,66,3,4,517],[90,618],[]),([0,1,2,208,28,74,4],[40,277,371],[0]),([77,0,1,2,66,3,72],[8,57,93,102,108,316,317],[0]),([0,61,66,3,530,37,5],[83,90,619],[]),([52,15,8,0,1,3,5],[8,55,62,128,185,620,621],[]),([157,0,1,2,158,3,29],[],[0,1]),([0,1,2,251,3,84,76],[96,329,330,331,341,342],[0,1]),([302,531,182,0,1,2],[8,188,622,623],[]),([356,77,0,1,2,3],[57,79,80,93,168,261,355],[0]),([162,0,66,3,4,5,72],[136,252,565,624],[0]),([183,182,0,1,2,66,4],[8,40,242],[0]),([217,0,1,2,62,37,5],[8],[0]),([345,346,0,61,4,37,5],[625],[]),([532,0,85,2,5],[8,326,510,626,627,628],[]),([77,375,128,1,2,3],[8,300,405,406,602,604,629,630,631],[]),([77,0,1,2,66,83,3],[57,93,102,108,168,261],[0,1]),([427,0,1,2,28,4,21],[],[0]),([0,1,2,66,28,74,72],[8],[0,1]),([319,8,0,1,3,5],[55,81,119,128,632],[0,1]),([150,93,0,1,3,4,37],[8,40,46,161,261,324],[0]),([142,0,1,2,66,3,76],[633],[0]),([0,1,2,227,28,4,21],[],[0,1]),([222,412,394,1,2,4,5],[],[]),([1,380,2,3,4,520,5],[],[]),([0,1,2,66,173,4,21],[8,633],[0]),([533,491,1,2,3,4,5],[232],[]),([216,171,0,1,2,66,3],[],[0]),([171,0,1,2,158,3,5],[],[0]),([0,61,208,3,74,4,5],[424,445],[0]),([8,0,1,28,21],[8,55,215],[0,1,2]),([93,0,1,3,309,4,95],[8,40,46,261,322],[0]),([171,0,1,2,227,3,5],[],[0]),([534,394,1,2,3,4,5],[],[]),([187,535,96,0,2,3,5],[200,222,225,326],[2]),([353,1,536,2,3,4,5],[],[]),([0,1,536,2,37,5,212],[61,71],[]),([77,339,0,1,2,3,72],[8,57,93,102,108,113,558,559],[2]),([339,353,1,2,37,5,212],[8,115,586],[]),([339,0,1,537,37,5,212],[8],[]),([339,0,1,2,100,37,212],[8,40,71,72,118,338,634],[0]),([216,339,0,1,2,37,212],[8,40,184],[]),([0,42,1,2,41,37,5],([142,413]++r 635 4),[0]),([0,1,393,2,40,37,5],[267,465,541,639],[]),([99,339,0,1,2,37,5],[84,640],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_21_6_1 : checkNodesBT W_21 g_21 F_21 P_21_6 A_21 B_21_5 6 N_21_6_1 = true := by decide +kernel
def N_21_6_2 : List NodeSpec := [([216,217,339,0,1,2,40],[217],[0]),([0,1,2,3,84,252,76],[641],[0]),([339,0,1,2,272,37,5],[8,40,202,640],[0]),([185,186,8,0,1],[55,81,138],[0,1,2]),([0,1,538,2,74,37,5],[],[]),([52,8,0,3,10,5],[8,62,81,128,185],[]),([339,0,1,22,74,37,5],[],[]),([216,171,339,0,1,2,3],[125],[]),([144,339,0,1,2,3,4],[114],[0]),([397,1,393,2,3,4,5],[156,592,599],[]),([0,348,1,2,3,29,76],[368,369,370],[0]),([171,0,1,393,2,3,5],[383,417],[]),([171,539,0,1,2,3,5],[],[]),([0,61,1,2,28,74,72],[314,642,643,644],[0,1]),([0,1,538,2,4,404,5],[],[]),([8,0,1,3,441,5],[8,55,62,81,119,128,645],[0,1]),([339,0,1,22,4,404,5],[],[]),([193,56,0,136,1,4,5],[8,76,106,190,255],[0,1,2]),e6 [540] [252,452],([77,0,1,525,2,3],[93,102,168,261,300,587],[]),([0,66,3,84,76],[80,95,169,341],[0,1]),([171,0,450,2,541,3,5],[383],[]),([77,339,0,1,152,3],[8,80,108,646,647],[]),([157,278,0,61,1,2,29],[648,649,650],[0,1]),([77,339,0,1,152,3,76],[8,80,646],[]),([542,77,0,1,2,3],[57,79,93,102,108,168,261,300,651],[]),([78,77,339,0,1,2,3],[57,93,102,153,168,261],[0]),([394,1,2,3,4,544,5],[],[]),([77,339,0,1,2,3,80],[8,57,93,101,102,108,558,559],[0,2]),([185,8,0,1,51,3,5],[81,128,652,653],[0]),([193,56,0,1,220,4,5],[76,106],[0]),([183,182,339,0,1,2,4],[8,40,98,286],[0]),([171,182,0,1,2,66,4],[8,40,242],[0]),([77,339,0,1,2,237,3],[93,108,152,168,558,559],[0,1]),([0,1,2,40,37,371,5],[338,510,654,655],[0]),([542,77,0,1,2,3,76],[57,300,651],[]),([77,339,0,1,2,83,3],[57,93,102,109,168,261],[0]),([131,130,0,2,3,4,5],[],[0]),([171,182,339,0,1,2,4],[8,40,134,286],[]),([0,1,2,28,4,545,21],[],[1]),([142,339,0,1,2,3,76],[160,557],[0]),([171,0,1,525,2,3,5],[],[]),([302,93,479,0,3],[8,46,322,656],[0]),e6 [546] [61,232,233,271,452],([394,1,393,2,3,4,5],[399,400,657],[]),e6 [547] [232,233,252,271,370,452],([339,0,1,469,3,4,5],[271,658],[]),([0,1,393,2,83,4,5],[573,574],[]),([81,339,0,1,2,3,5],[105],[0]),([171,548,0,1,2,3,5],[],[]),([416,460,77,1,2,3],[8,78,299,300,301,514,603,605,659],[]),([8,0,1,3,170,5],[8,55,62,185],[0,1]),([52,435,8,0,1,3,5],[62,81,128,185,660,661],[0]),([193,58,56,0,1,4,5],[76,77,106,255,662,663],[0]),([52,8,0,1,28,3,5],[55,62,128,185,410,411,664],[0,1]),([344,293,1,2,3,4,5],[232],[0]),([52,8,0,1,3,5,21],[8,55,62,81,185,664,665,666],[0]),([185,52,8,0,1,3,5],[62,81,128,652,653],[0]),([384,58,56,0,1,4,5],[8,190,667,668],[0,1]),([8,0,1,51,3,5,21],[8,62,128,412,665,666,669],[0]),([171,0,61,66,3,5,76],[90,670],[0]),([384,56,0,1,57,4,5],[8,106,190,667,668],[0,1]),([511,125,8,0,1,3,5],[8,55,62,128,185],[]),([534,0,1,2,28,4,21],[],[1]),([416,77,128,1,2,3],[8,78,299,300,301,514,629,631,659,671],[]),([302,180,56,0,4,5],[8,76,77,106,255],[]),([332,77,0,61,1,3],[8,57,58,80,93,108,272],[0]),([187,96,0,2,28,3,5],[222,225,325,326,439],[0,2,3]),([412,394,1,2,28,4,21],[672,673],[1]),([185,187,96,0,2,3,5],[200,222,225],[0]),([384,109,11,0,2,4,5],[8,415,674],[0,1]),([0,1,2,62,37,5,72],[87,267,413,430,431,432,675],[0]),([8,0,124,1,3,5,21],[8,62,128,185,256],[0,2]),([185,8,0,124,1,3,5],[62,81],[0,2]),([384,56,0,179,1,4,5],[8,190],[0,1,2]),([413,412,1,2,3,4,5],[232],[]),([0,334,1,2,467,4,5],[676],[]),([193,56,0,1,4,5],[8,76,106,190,255,677],[]),([0,1,198,37,92],[8,51],[0,2]),([8,0,551,3,5],[8,81,128,678],[]),([171,278,0,1,2,66,5],[],[0]),([435,0,1,260,5],[8,81,185,483,679,680],[]),([505,0,472,1,2,3,5],[],[1]),([8,0,1,3,260,10,5],[62,81,128,185],[0]),([302,56,0,1,4,552,5],[76,77,106,255],[1]),([410,96,0,2,3,418,5],[8,222,326],[2]),([99,0,1,2,66,37,5],[487],[0]),([253,254,0,2,3,4,5],[],[0,2]),([193,56,0,1,4,553,5],[8,190],[]),([193,0,1,195,5],[8,77,182,483],[0,2]),([193,56,0,1,4,95,5],[76,77,106,255],[0]),([193,302,56,0,1,4,5],[76,77,106,255],[0]),([420,193,56,0,1,4,5],[8,190],[0]),([554,56,0,4,5],[8,76,77,681],[]),([210,555,209,0,2,3,4],([261,300]++r 682 7),[]),([15,0,1,3,16],[8,55,689],[3]),([302,67,56,0,1,4,5],[8,76,106,190],[1]),([8,0,1,324,3,10,5],[8,62,128,185],[0]),([93,0,1,40,37],[8,39,161,690],[0,2]),([302,56,0,1,556,4,5],[8,76,106,190],[1]),([0,199,1,2,198,37,5],[8,338,413,691,692,693],[0]),([374,8,0,1,3,5],[8,55,62,81,119,128,694],[0,1]),([460,77,0,1,152,2,3],[8,57,93,102,108,647],[]),([0,61,73,3,4,5,72],[271,365,624,695],[0,1]),([302,56,479,0,5],[8,76,106,696],[1]),([0,61,66,40,100,37,5],[2,83,267,510,539,540,654,697],[0]),([557,8,0,1,3,5],[8,81,119,128,698],[]),([558,8,0,1,3,5],[8,62,81,119,699],[]),([261,56,0,1,4,5],[53,76,77,106,189,190],[0]),([0,61,208,3,4,37,5],[424,507],[0]),([559,11,0,2,4,5],[8,143,674,700,701,702],[]),([306,0,1,2,3,29,76],[],[0]),([560,56,0,4,5],[76,77,190,703],[]),([187,0,188,3,5],[97,222,224,225],[0,1]),([234,8,0,1,3,5],[8,62,119,128,704],[0]),([312,0,1,6,3,311,5],[],[0]),([561,8,0,1,3,5],[8,55,62,81,119,128,705],[]),([0,562,55,4,141],[8,706,707],[]),([0,1,2,143,37,5,76],([255]++r 708 5),[0]),([0,9,2,243,246,4,5],[713,714,715],[0,3]),([381,382,0,1,2,37,5],[449,716],[0]),([93,0,9,10,4],[8,322,324,717],[1]),([0,1,563,7,21],[8,718,719],[]),([312,313,0,2,3,4,5],[],[0,2]),([77,0,9,2,10],[8,57,720],[2]),e6 [564] [61,232,233,370],([0,9,244,2,243,4,5],[713,714,715,721,722],[0,2]),([565,0,9,2,243,4,5],[],[3]),([77,0,128,1,152,2,3],[57,93,102,108,647],[]),([566,567,0,1,2,3,4],[],[1]),([568,93,0,1,3,4],[37,40,46,161,261,322,324,723],[]),([77,0,61,66,3],[0,80,99,102],[0,1]),([307,93,0,1,3,10,4],[8,40,322],[0]),([302,182,0,1,2,74],[8,724,725],[]),([77,0,128,1,2,3,55],[8,57,93,102,108,168,261],[2]),([77,375,61,1,2,3,76],[8,40,78,80,298,300,405,406],[0]),([0,388,2,3,569,4,5],[],[2,3]),([332,77,343,0,1,2,3],[8,57,93,102,108],[0]),([169,0,1,3,5],[31,163,726],[0,2]),([413,412,1,2,4,37,5],[727],[]),([570,93,0,1,3,4],[36,37,40,46,161,261,322,324,365,728],[]),([222,210,209,0,2,3,4],[44,682,683,686,687,688,729,730],[0]),([302,93,0,1,3,309,4],[8,46,261,322],[0]),([307,323,93,0,1,3,4],[8,40,46,161],[1]),([307,301,93,0,1,3,4],[8,40,261],[]),([171,0,1,2,3,572,5],[],[]),([0,1,573,2,28,4,21],[],[1]),([0,61,208,3,4,5,21],[80,731],[]),([302,574,182,0,1,2,4],[8,242,286,287,288],[1]),([332,77,323,0,1,2,3],[8,93,102,108],[0]),([171,0,1,573,2,3,5],[],[]),([0,61,66,3,37,5,76],[90,390,732],[]),([171,534,0,1,2,3,5],[],[]),([307,150,93,0,1,3,4],[40,46,80,161,322],[]),([222,150,93,0,1,3,4],[46,162,261,322,324,457,458],[0]),([93,0,1,149,40,3,4],[46,80,161,322],[0]),([93,0,1,149,3,4,37],[8,40,322],[0]),([210,0,211,3,4],[97,117,682,683],[0,1]),([210,209,0,2,40,3,4],[300,682,733,734,735],[0,2]),([210,209,0,2,3,4,37],[8,40,682,736,737],[0]),([193,56,0,383,1,4,5],[76,106],[0,2]),([222,93,0,295,1,3,4],([40,41,46,161,324]++r 738 4),[0,2]),([508,0,1,309,4],[8,261,324,742],[2]),([307,0,1,575,3],[8,40,161,743],[3]),([576,93,0,1,3,4],[8,37,46,161,322,324,744],[]),([0,199,1,3,198,4,92],(r 745 5),[0,2]),([0,1,3,198,200,4,92],[745,746],[0]),([253,0,1,3,198,4,92],[],[0]),([253,0,1,2,198,37,5],[],[0]),([0,1,2,3,37,101,76],[750],[0]),([0,1,2,578,5],[8,751,752],[]),([0,1,579,2,37,212],[8,71,72,753],[]),([410,0,580,1,2,37,212],[8,71,72,716],[]),([0,1,37,581,212],[8,72,754],[]),([38,0,1,41,5],[8,32,142],[0,2]),([48,47,0,1,3,4,5],[755,756],[0]),([47,0,1,49,3,4,5],[755,756],[0]),([394,582,1,2,3,4,5],[233,757],[]),([88,87,0,2,3,4,5],[],[0]),([47,0,283,1,3,4,5],[40,59,261,758],[0,2]),([219,193,56,0,1,4,5],[76,106,662,663],[0]),([171,583,0,1,477,3,5],[433],[]),([449,516,0,584,3,4,5],[518,519,520],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_21_6_2 : checkNodesBT W_21 g_21 F_21 P_21_6 A_21 B_21_5 6 N_21_6_2 = true := by decide +kernel
def N_21_6 := N_21_6_0 ++ N_21_6_1 ++ N_21_6_2
def B_21_6 : BT (List (List Nat)) := buildBucketsBT W_21 N_21_6
set_option maxRecDepth 500000 in
lemma B_21_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_21 6 xs.toFinset) B_21_6 := by
  have hP := buildPoolsSubBT_sound (pdepth := 12) (W := W_21) (raw := r_21) (pspecs := ps_21) (used := U_21_6) S_21_ok
  have hm0 := checkNodesBT_mem (by decide) gp_21 W_21_ok hP A_21_ok B_21_5_ok C_21_6_0
  have hm1 := checkNodesBT_mem (by decide) gp_21 W_21_ok hP A_21_ok B_21_5_ok C_21_6_1
  have hm2 := checkNodesBT_mem (by decide) gp_21 W_21_ok hP A_21_ok B_21_5_ok C_21_6_2
  exact buildBucketsBT_of_mem (forall_append (forall_append (hm0) hm1) hm2)
def U_21_7 : List Nat := ([0,2,4,8,11,21,36,37,40,46,55,57,60,61,62,70,71,72]++r 76 6++[83,87,90,93,96,97,102,106,108,119,120,128,132,133,136,151,156,161,165,168,176,180,185,188,189,190,200,222,225,232,233,235,242,252,253,255,260,261,263,264,265,267,271,273,275,276,277,279,281,286,287,288,290,292,295,296,298,300,302,304,305,311,314,315,317,318,321,322,324,325,326,329,331,336,338,339,341,342,344,345,349,350,354,359,360,361]++r 363 4++[370,371,373,376,380,383,384]++r 387 4++[394,397]++r 399 6++[407,409,410,413,417,418,421,422,424,426,427,429,431,432,433,435,436,438,443]++r 445 5++[451,452,453,455,456,458,459,461,462,463,465,466,468,469,473,479,482,483]++r 485 4++[493,494,498,500,501,504,505,507,510,517,518,519,522,525,528,530,533,539,541,547,549,551,554,555,557,559,561,562,564,568,570,573,574,575,577,580,581,584,585]++r 588 6++[598,599,601,603,607,611,613,616,618,619,621,624,625,627,629,633,640,643,644,649,652,654,657,661,663,666,668,669,670,672,673,676,682,683,686,688,690]++r 709 5++[715,716,722,727,732,735,739,741]++r 746 5++[756]++r 759 855)
def P_21_7 : BT (Option BoundPool) := buildPoolsSubBT 12 W_21 r_21 S_21 ps_21 U_21_7
def N_21_7_0 : List NodeSpec := [([0,450,2,83,4,5],[8,574,759,760,761],[]),e6 [345,585] [40,326,452,762,763],a6 [586] [8,232,252,253,452,764,765,766] [2],([171,0,128,1,2,3,5],[8,767,768,769],[2]),([0,492,2,3,587,5],[8,770,771,772],[]),([394,450,2,3,4,5],[8,400,773,774],[]),([345,346,394,1,2,3,4,5],[400,401,657,775],[0]),([394,1,2,3,4,588,5],[8,233,400,401,657,776,777],[]),([462,394,1,2,3,5],[8,401,778],[]),([589,394,1,3,4,5],[8,401,657,779,780],[]),([345,394,492,1,2,3,4,5],[400,401,657,775,781],[]),([394,1,2,3,4,590,5],[8,40,233,400,657,775,782,783],[]),([0,1,2,173,4,21],[8,370,533],[0,2]),([142,0,1,2,3,76],[8,292,370],[0,2]),([0,1,2,28,74,72],[8,643,644],[0,1,2]),([157,77,0,1,2,3],[8,57,78,79,93,102,108,168,482],[0,2]),([77,0,1,2,3,72],[8,57,78,93,102,108,397],[0,2]),([77,0,1,2,83,3],[8,57,93,102,108,522],[0,1,2,3]),([332,77,0,1,2,3,76],[8,57,80,93,102,108,784],[0,2]),([460,77,0,1,2,3,76],[8,57,79,93,102,108,300,603],[0]),([183,182,0,1,2,4],[8,40,188,242,286,287,288,785,786],[0,2]),([77,0,1,2,3,80],[8,57,78,93,102,108,429],[0,2]),([77,0,591,1,2,3],[8,57,78,93,102,108,787],[2]),([332,77,0,1,2,3],[8,57,80,93,102,108,168,261,784],[0]),([416,77,1,2,3],[8,78,79,80,300],[0,2]),([77,342,0,1,2,3,76],[8,57,80,93,102,108,370,788],[0]),([592,77,0,1,2,3],[8,78,79,93,102,108,789],[]),([592,343,0,2,3,29],[8,341,493,790,791],[2,3]),([462,0,1,2,28,21],[8,277,792],[0]),([77,0,1,2,3,129],[8,57,78,93,108,793],[0,1,2]),([589,0,1,28,4,21],[8,277,371,794,795],[1]),([339,0,1,22,4,37,5,21],[796],[0]),([339,0,1,2,40,100,37,5],[8,40,60,267,338,413,465,510,640,654,797,798,799],[0]),a6 [594,76] [261,800] [1],([217,0,61,1,2,40,37,5],([8,338]++r 801 4),[0]),([462,345,0,1,2,3,5],[8,271,762,805,806],[]),([339,353,1,2,3,4,5,212],[8,364,365,807,808,809],[0,2]),([222,278,0,1,2,66,4,5],[487,810],[0,1]),a6 [595,399] [8,370] [1],([0,1,2,83,593,4,5,76],[8,261,811,812],[]),([0,61,1,2,3,530,37,5],[8,261,290,339,813,814,815],[0,1]),([302,182,0,1,2,4,21],[8,40,286,287,288,816],[0,3]),([302,0,1,22,2,3,74,5],[263,264,326],[]),u6 [208,21] [80,817],([157,339,0,1,152,3,4,5],(r 818 4),[0]),([185,0,1,2,66,512,4,5],[8,633,822],[0]),([77,0,9,1,2,3],[8,78,93,102,108,823],[0]),a6 [73,21] [365,763,824,825,826] [0,1],([222,596,0,1,2,258,4,5],[261,827,828],[]),([416,77,1,2,3,76],[8,78,79,80,300],[0,2]),u6 [427,21] [40,271,829,830,831],([185,278,0,1,2,66,4,5],[261,633,810],[0]),([302,0,2,3,597,5],[8,832,833],[2]),([413,412,1,2,3,4,5],([232,345,349,350,727]++r 834 4),[0]),([193,56,0,1,4,5],[8,76,77,106,189,190,255,663],[0,2]),([302,0,1,2,28,74,21],[8,314,838,839,840],[0]),([171,0,1,2,66,3,5,76],[8,633],[0]),u6 [157,158] [841,842],a6 [208,72] ([185,445]++r 843 5) [0,1],([394,61,66,3,4,5,21],[80,151,363,365,400,401,469,848,849],[0]),([394,1,2,208,3,4,5,21],[80,401,843],[0]),([222,93,0,1,3,4],[8,36,37,46,80,322,324,690,741],[0,1,2]),([0,1,579,2,3,4,212],[8,850,851,852],[0]),([0,1,2,66,28,4,21,72],[8,276,277,315,371,853,854],[0,1]),e6 [345,203] [8,253,452,762,763],([77,0,1,2,66,3],[8,57,80,261,317],[0,1]),([302,171,345,0,1,2,3,5],[762,855,856],[0]),([93,0,1,3,4,37],[8,40,324,570],[0,2]),u6 [384,483] [8,370,857],u6 [66,72] [252,253,271,365,452,858,859],([384,0,1,2,3,599],[8,860,861,862],[]),u6 [423,21] [8,80,487,863,864,865],a6 [73,72] ([365]++r 866 5) [0,1],([77,0,1,2,66,3,76],[8,57,80,261,317],[0,1]),([185,278,339,0,1,2,4,5],[261,557,564,810],[]),([0,1,2,66,3,485,37,5],[8,40,487],[0]),([185,484,0,61,66,3,4,5],[83,90,390,871],[0,1]),([222,394,1,2,66,4,5,21],[],[0]),([216,0,1,2,66,3,37,76],[633],[0]),([0,580,1,2,37,5,212],[8,71,72,449,593,716,872],[0,2]),([185,0,1,2,66,37,5,76],[487,633],[0]),([0,1,2,208,4,37,5,21],[873,874],[0]),([217,0,1,2,66,40,37,5],[8,40,338,510,875],[0]),([339,0,1,2,28,74,4,21],[40,276,277,314,371,409],[0,1]),([0,1,2,66,3,502,5,76],[633,876],[0]),([0,1,2,66,40,100,37,5],[8,40,180,267,338,413,465,487,510,877,878,879],[0]),u6 [216,66] [8,40,271],u6 [396,212] [365,851,880],a6 [601,76] [261,881] [1],([171,394,1,2,66,3,4,5],[8,40,401],[0]),([521,61,1,2,3,467,4,5],([8,80,261,300]++r 882 5),[0]),([394,61,1,2,3,4,5,21],([8,80,261,300,883]++r 887 4),[0]),([0,334,1,2,4,5,21],([40]++r 891 4),[0,1,2]),([345,0,61,1,3,4,5,21],[8,80,253,261,895,896,897],[0]),u6 [412,21] [252,422,453,887,898,899],([0,1,2,208,28,4,21],[40,80,277,314,344,874,900],[0,1]),([397,1,2,66,3,4,5,72],[365,591,592,858],[0]),([171,339,0,1,2,3,37,5],[8,40,448,640],[0]),([157,278,0,61,1,2,4,5],[8,40,261,810,901,902,903],[0,1]),a6 [162,21] ([8,261,453,845,847]++r 904 5) [0,2],u6 [208,37] [8,40,874,909,910],([384,0,1,2,66,3,4,517],[40,633,911],[0]),([0,61,1,2,28,4,21,72],([8,40,276,277,314,315,371]++r 912 5),[0,1]),e6 [171,538] [40,61,917,918],([0,61,1,2,83,4,5,72],[8,40,574,575,810,919,920,921],[0,1]),a6 [538,72] ([326,763,845]++r 922 4) [1],([216,217,0,61,1,2,3,4],[8,40,261,926],[0]),([598,0,1,2,30,5],[8,40,261,927,928],[]),([171,345,0,61,1,3,4,5],[8,261,917],[]),([345,346,0,61,3,4,5],[8,261,271,452,625,762,929,930],[0]),a6 [538,76] [8,326,845,922,923,924,931,932] [1],([185,0,61,1,2,512,4,5],[8,40,261,290,933,934],[0]),u6 [384,334] ([8,370,894]++r 935 4),u6 [491] [40,232,233,271,452,453,547,939],e6 [216,339] [8,40,436,452],([413,412,1,2,3,4,5,21],[345,835,837,904],[0]),([171,0,1,2,66,28,4,21],[8,40,277],[0,1]),a6 [412,76] ([40,61,763,825,834,899]++r 940 5) [0,1],u6 [412,472] [40,727,899,942,945,946],u6 [505,412] [40,61,947],([449,394,1,3,4,5],[8,657,948,949],[]),([0,61,1,2,40,37,5,72],([8,40,267,413,465,510]++r 950 6),[0]),u6 [222,158] [80,370,453,841,842,956],([0,1,2,66,83,37,5,76],[8,296,957,958],[0,1]),([339,394,1,2,4,37,5,21],[468,959,960],[]),([171,0,61,1,2,28,4,21],[8,40,276,961],[0,1]),([8,0,1,324,3,5],[8,55,62,128,185,962],[0,1]),([0,1,2,66,3,4,100,72],[8],[0]),([487,0,1,2,3,74,5,21],[8,40,831,963],[]),u6 [293] [61,232,233,271,370,452,453,585,964,965],([0,61,66,3,4,100,37,5],([83,90,390]++r 966 5),[0,1]),a6 [185,264] [61,261,321,453,971,972] [0,1],e6 [603] [8,40,232,253,452,973,974],([0,492,2,28,4,461],[8,276,277,975,976],[1,3]),([394,1,2,3,4,406,5,21],[8,40,616,977],[0]),([0,1,3,563,7,5],[8,978,979],[0,1]),([384,0,61,66,3,4,37,5],[83,90,390,980],[0,1]),([171,0,61,66,3,4,5,21],[83,90,390,917,981,982],[0,1]),([0,1,2,66,37,5,212],[8,40,71,72,180,487,593,983],[0]),([345,394,61,1,3,4,5,21],[8,80,261,401,775,781,984],[0]),a6 [37,101] ([8,40,61,261,290,453,970]++r 985 4) [0,1],u6 [393,37] [370,624,868,969,987],u6 [214,62] [8,370],([216,0,61,1,2,40,37,5],[8,40,176,267,339,989,990],[0]),e6 [492,604] [252,271,763,845,991],([171,0,61,66,3,4,5],[83,90,252,363,390,855,917,981,982],[0,1]),([460,77,0,1,2,3],[8,57,79,93,102,108,168,261,603],[0,3]),([0,450,477,3,4,5],[8,302,365,992,993,994],[]),([339,0,1,2,3,4,100,72],[435],[0]),([0,61,66,3,467,4,5],[80,83,363,365,403,995,996,997],[0,1]),([345,0,492,1,2,28,4,21],[8,276,277,315,354,371],[1]),([171,339,0,1,2,28,4,21],[8,40,371,402],[0,1]),([0,1,2,66,3,530,37,5],[487,633],[0]),u6 [63,62] ([8,339,370,421,505,894]++r 998 4),([302,182,0,1,2,4],[8,40,242,286,287,288,816],[0,1,3]),([216,0,1,2,66,3,4,21],[8,633],[0]),u6 [513,334] [8,370,1002,1003,1004],([157,0,61,66,3,4,5,76],([165]++r 1005 6),[0,1]),([185,484,0,61,1,2,37,5],[8,40,261,290,339,933,1011,1012],[0]),([605,606,0,1,2,258,4,5],[8,40,827],[]),([607,0,61,3,4,5],[80,83,90,97,1013,1014,1015],[]),([0,1,2,66,3,100,37,76],[8,40,1016],[0]),([0,61,1,2,3,523,5,76],([8,339]++r 1017 5),[0]),a6 [357,76] [8,452,812,1022,1023] [0,1],([185,186,0,94,2,95],(r 1024 5),[1,2]),u6 [506] [232,261,453,1029,1030,1031],a6 [157,264] ([261,453]++r 1032 4) [0,1],a6 [222,264] [261,321,370,453,971,1032,1033,1036,1037] [0,1],e6 [384,498] [8,370,1038],([171,0,61,1,2,37,5,21],[8,40,339,1039],[0]),([185,186,0,61,66,4],[4,90,390,1028,1040,1041],[1]),([412,394,1,2,3,4,5],[40,233,401,528,657,673,834,888],[0]),([0,61,66,3,166,5],([90,390]++r 1042 4),[]),e6 [519,95] [261,271,365,1046,1047,1048],([0,1,2,288,37,5],[8,40,61,265,267,311],[0,2]),([0,1,2,83,608,4,5],[8,252,261,574,575,765,1049],[]),([0,61,66,3,37,5,76],([83,90,390]++r 1050 4),[0,1]),([0,609,2,28,4,21],[8,371,1054,1055],[1]),e6 [605,596] [8,40,253,452,1056],a6 [506,76] [261,1029,1057] [0,1],a6 [334,76] [8,40,61,938,940,941,1002,1003] [0,1],([334,1,380,2,3,4,5],([80,232,1003]++r 1058 5),[0]),([0,61,66,3,4,30,5],([83,90]++r 1063 4),[]),([222,339,0,1,2,467,4,5],[40,488,640,1067],[]),([217,339,0,1,2,40,37,5],[8,40,338,465,473,1068],[0]),([287,331,0,2,40,5],[8,267,510,1069,1070],[2]),u6 [412] [40,61,232,233,271,422,452,453,899,946],([222,384,0,61,66,3,4,5],([83,90,390]++r 1071 4),[0]),([222,394,61,1,2,4,5,21],[8,261,888,1075],[0]),a6 [412,72] [40,763,825,834,918,942,943,944,1076,1077,1078] [0,1],([216,217,0,1,2,66,3,4],[8,1079],[0]),([77,0,1,456,2,3],[8,57,78,93,108,1080],[0,1,2]),([77,342,0,1,2,3],[8,57,80,93,102,108,261,370,788],[0,1,2]),([77,339,0,1,2,3,76],[0,8,80,93,102,261,559],[0,1,2]),([171,0,1,2,360,4,5],[252,253,261,855,856],[]),([185,0,61,66,4,37,5],[83,90,390,1081,1082],[0,1]),([339,0,1,2,40,37,5,72],[8,267,413,465,510,541,797,798,1083],[0,2]),u6 [227,21] [8,561,831,1084],([222,0,61,1,2,467,4,5],([8,339,676]++r 1085 4),[0]),([339,0,1,477,3,4,5,72],[8,365,868,870,1089],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_21_7_0 : checkNodesBT W_21 g_21 F_21 P_21_7 A_21 B_21_6 7 N_21_7_0 = true := by decide +kernel
def N_21_7_1 : List NodeSpec := [([0,1,2,28,587,21],[8,277,1090,1091],[1]),([379,0,1,2,3,5],([8]++r 1092 4),[]),([216,0,1,2,37,212],[8,71,72,1096],[0,2]),u6 [566,498] [8,370],u6 [424,264] [261,321,598,971,1097],([222,412,0,1,2,4,5,21],[453,1075,1088,1098,1099],[0,1]),([474,0,1,2,3,76],[8,370,493,1100],[0]),([0,61,208,3,4,5,21],[271,365,424,443,445,507,845],[0,1]),([394,1,538,2,3,4,5,21],[300,401,922],[]),([222,0,1,2,360,4,5,76],[261,1101],[0,1]),u6 [162,37] [40,61,261,453,867,970,985,986,987],([0,61,66,83,3,4,5,76],[83,90,165,1057,1102,1103,1104],[0,1]),([394,61,1,2,28,4,21],[40,80,261,300,359,360,517,914,915,1105,1106,1107],[0,1]),([0,1,2,611,4,21],[8,276,370,1108],[2]),([216,384,0,61,1,2,3,4],[8,40,261,290,1109],[0]),([8,0,1,28,3,5],[55,62,81,120,128,185,410],[0,1,2]),u6 [171,61] [8,40,252,261,1110],u6 [171,208] [40,61,917,918],([0,61,66,3,512,4,5],([83,90,363]++r 1111 4),[0,1]),([410,353,1,2,3,4,212],([8,366,808]++r 1115 4),[0]),u6 [422,76] [8,40,61,252,709,766,940,941,1119],([222,0,61,66,3,4,5,76],([83,90,390,1005,1006,1007]++r 1120 4),[0,1]),([394,492,1,2,28,4,21],([8,300,359,360,517]++r 1124 4),[1]),([0,61,66,3,4,5,21,76],[83,90,390,845,848,1005,1006,1007,1128,1129],[0,1]),u6 [216,61] [8,40,252,261,1130],u6 [73,37] [370,868,969,1131],([185,0,61,1,2,37,5,76],[8,261,290,339,810,1132],[0]),u6 [215,62] [8,370],([0,61,66,3,4,5,517],([90,363,390]++r 1133 4),[0]),([0,1,2,3,406,5,408],[40,252,253,339],[0]),([339,0,1,2,3,502,5,76],[389,557,1137],[]),([77,375,1,2,3,76],[8,78,79,80,300],[0,2]),([353,1,2,66,3,4,5,212],[365,366,858],[0]),u6 [468,467] [80,1138],([0,61,66,3,4,37,5,21],[83,90,390,966,967,970,1139],[0]),([8,0,1,3,5,21],[8,62,81,120,128,185,666],[0,2]),u6 [496,497] [271,452,995,1140],([353,61,1,2,3,4,5,212],[8,80,300,588,589,807,883,1116],[0]),([0,1,2,66,3,37,5,76],[633,876],[0]),([339,0,1,2,37,5,21,76],[8,394,557,640,1141],[]),([157,0,1,2,360,4,5,76],[261,709],[0,1]),([0,1,2,28,4,604,21],[8,276,277,315,344,1142,1143],[1]),([216,0,61,66,3,4,37,5],[83,90,390,1144],[0,1]),a6 [362,82] ([40,61,581]++r 1145 7) [0,1],([185,0,61,66,3,4,5,76],([83,90,390]++r 1152 4),[0]),([0,1,2,612,3,406,5],[40,252,253,339,1156],[]),([412,394,1,2,3,4,5,21],[400,673,834,888],[0]),([8,0,9,1,3,5],[8,62,81,120,185,1157],[0,3]),([216,0,1,2,66,3,4,72],[8,858],[0,1]),([394,1,2,3,4,604,5],[8,233,400,401,528,657,1158,1159],[]),([77,375,1,2,3],[8,78,79,80,300],[0,1,2,3]),a6 [613,365] [8,80,339,1160] [1],e6 [185,525] [61,261,453,1161],([0,61,66,3,4,5,21,72],[83,825,826,1128,1162,1163],[0,1]),([394,1,2,66,4,37,5,21],[831,1164],[0]),([0,61,66,3,4,5,72],[271,363,365,403,624,867,868,1165],[0,1]),u6 [163,84] [261,598,1166,1167],([216,0,61,66,3,4,5],[83,90,252,363,390,1144,1168,1169,1170],[0,1]),([0,1,2,62,37,5],[8,87,267,339,413,431,432,483,555],[0]),([0,66,3,62,4,5],[83,390,418,421],[0]),([222,0,61,66,4,5,21],[83,90,390,892,1171,1172,1173],[0,1]),([216,0,61,1,2,3,37,76],[8,40,261,290,1174],[0]),([0,61,66,3,4,37,5,72],[90,624,966,967,969,970],[0,1]),([0,136,2,40,37,141],[8,338,510,1175,1176,1177],[2]),([345,516,0,2,3,4,5],([8,271,762]++r 1178 5),[]),([171,0,1,2,66,37,5,21],[487],[0]),([222,0,1,2,208,4,5,21],[1183],[0]),([222,345,346,0,1,2,4,5],[892,893],[0]),([0,61,423,3,4,5],[185,279,281,1184,1185],[0,1]),a6 [334,520] [1186,1187] [0,1],([345,346,0,61,3,4,5,21],[8,261,845,930,1188,1189],[0]),u6 [293,212] [61,252,585,747,1116,1190],u6 [253,198] [252,271],([0,61,1,2,37,5,212],[8,40,70,71,72,176,339,449,593,716,1191],[0,2]),([0,61,1,2,28,74,4,21],[276,314,838,1192,1193,1194],[0,1]),([0,9,2,10,29,76],[8,493,1195,1196,1197],[0,3]),([0,61,1,2,3,37,5,76],[8,261,290,894,1198,1199,1200],[0,1]),([339,0,1,2,37,5,212],[8,40,60,72,449,451,593,640,1201],[0,2]),([0,9,2,243,4,5],[8,713,715,722],[0,3]),([0,66,3,82,4,5],[80,97,390,580,1202],[0,1]),([614,615,0,2,3,5],[1043,1045,1203,1204,1205],[2]),([93,0,1,149,3,4],[40,80,161,261,322,324,584],[0,1]),([81,0,1,2,3,5],[8,260],[0,2]),([216,0,1,2,66,40,37,5],[8,40,180,487,510,1206],[0]),([345,0,61,1,28,4,21],[8,80,315,354,371,1207,1208,1209],[0,1]),u6 [185,158] [61,261,453,1210],([302,479,0,2,3,616,5],(r 1211 6),[2]),a6 [62,64] [8,339,370,421,894,998,999,1000] [0,1],([302,171,0,1,2,3,55,5],[261,855,917,1217,1218],[2]),([185,484,0,1,2,66,37,5],[8,487,633,1079],[0]),([345,0,61,1,4,37,5,21],[8,185,909,1207,1219],[0]),([77,0,1,2,237,3],[8,57,78,93,102,108,380],[0,1,2]),u6 [171,412] [40,61,855,918,946,1220,1221],([77,0,61,1,2,3,76],[8,78,102,108,261,298],[0,1,2]),([185,339,0,1,2,37,5,76],[461,557,640],[]),([410,382,0,1,2,3,4,212],[8,851],[0]),([345,394,61,1,3,4,5],[8,261,657,777,781],[]),([0,61,1,2,83,37,5,76],([8,255]++r 709 4++[810]++r 1222 4),[0,1]),([412,0,1,2,4,37,5],[8,61,946,1226],[0,1]),([394,61,1,2,4,37,5,21],[8,40,261,528,616,1106,1227],[0]),([222,345,0,61,1,4,5,21],[8,1173],[0]),([0,9,6,10,7,5],(r 1228 5),[0,1,3]),([216,384,339,0,1,2,3,4],[447,557],[]),([0,450,2,66,3,4,5,72],[271,365,867,1233,1234],[0,1]),([222,412,0,1,2,4,5],[61,946,1099],[0]),([171,0,1,2,66,3,5,72],[8,858],[0,2]),a6 [137,139] [253,452,505,1235,1236,1237] [0,2],([8,0,1,3,5,16],[8,62,120,128,185,1238],[0]),([0,61,1,2,3,100,37,76],[8,261,750,1239,1240,1241],[0]),([0,61,1,2,3,4,517,76],[8,40,290,810,894,911,1242,1243],[0,1]),([93,0,295,1,3,4],[36,40,46,80,161,261,322,324,739],[0,1,2]),([0,1,2,100,37,212],[8,40,70,71,72,338,577],[0,2]),([617,0,61,66,4,5],([90,390]++r 1244 4),[]),([185,278,0,61,1,2,4,5],[8,40,261,290,810,901,1248],[0]),a6 [433,76] [812,1089,1249,1250] [1],e6 [412,37] [8,40,61,453,946,985,986,1079],([0,61,66,40,37,5],[2,11,83,267,510,539],[0]),([99,0,1,2,37,5],[8,61,601],[0,2]),u6 [61,72] ([8,40,252,253,261,271,452,883,918]++r 1251 4),([394,61,1,2,3,4,5,72],[8,40,261,400,401,528,657,775,1077,1255,1256],[0]),([0,61,1,2,3,485,37,5],[8,261,339,1257,1258,1259],[0]),([397,61,1,2,3,4,5,72],([8,40,80,261,300,599,883]++r 1260 4),[0]),([157,0,1,2,66,3,29,76],[8,493,1196,1264,1265],[0,1]),([185,8,0,1,3,5],[8,62,81,128,185,652],[0,2]),([510,316,0,2,40,37],[8,267,510,1266,1267,1268],[2]),u6 [251,84] ([261,339,598,611,613]++r 1269 5),([216,0,61,1,2,3,4,21],[8,40,261,290,1274],[0]),([560,0,54,55,4,5],(r 1275 5),[0]),a6 [162,72] ([8,40,252,261,590]++r 867 4++[954,1260,1280,1281]) [0,2],([339,0,1,2,28,4,21,72],[8,275,276,277,315,371,1282,1283],[0,1,2]),e6 [619,618] [8,40,61],([0,61,66,3,4,5,212],[83,365,390,403,851,1284,1285,1286],[0]),([345,394,1,2,3,4,95,5],[8,401,657,775],[2]),([496,0,61,1,3,467,4,5],[8,80,253,261,1287,1288,1289],[0]),([449,0,61,1,3,4,5,72],([8,40,80,253,261,868]++r 1290 6),[0]),([339,0,1,2,83,37,5,76],[8,295,812,1296,1297],[1,3]),e6 [538,21] [300,1298],([171,0,61,1,2,3,5,72],[8,40,261,383,433,883,1110],[0]),([216,339,0,1,2,40,37,5],[8,40,60,459,465,640,1299],[0]),([339,0,1,2,3,100,37,76],[8,40,466,1300],[]),a6 [208,76] [8,185,843,844,874,910,1301] [0,1],u6 [573,21] [185,271,365,1302,1303],([397,450,2,3,4,5],([8,365,599]++r 1304 4),[]),([0,61,66,3,4,5,21],[80,83,363,365,390,403,1308,1309,1310],[0,1]),u6 [534,21] [185,253,930,1311],([0,61,66,28,4,21],[21,80,90,273,276],[0,1]),u6 [335,334] ([8,80,894,1002,1003]++r 1312 5),([171,0,1,2,66,3,37,5],[8,40,487],[0]),u6 [208,74] [40,61,445,829,845,846,847,874],([8,0,124,1,3,5],[8,55,62,81,128,185,1317],[0,1,2]),([0,61,1,2,3,4,100,72],[40,261,388,1318,1319,1320],[0]),u6 [334,337] [8,370,938,1321],e6 [243,7] [8,253,261,452,1007,1089,1322,1323],([0,1,2,66,28,74,4,21],[8,40,276,277,314,315,371],[0,1]),([171,339,0,1,2,37,5,21],[448,640],[]),([1,2,3,82,363,4,5],[80,232,361,446,727,1146],[0,1]),([384,0,61,1,2,3,4,517],[8,40,261,290,1088,1324,1325,1326],[0]),([210,209,0,2,3,4],[40,132,133,261,300,682,683,686,688,735],[0,1,2,3]),([185,339,0,1,2,512,4,5],[486,557],[]),([216,0,61,1,2,3,4,72],[8,40,261,883,1327],[0,1]),([0,61,1,2,37,5,21,76],[8,40,290,339,1328,1329],[0,1]),([222,278,0,61,1,2,4,5],[8,40,261,339,810,901,902,1330],[0]),([339,0,1,22,3,4,5,21],[8,80,1331],[]),a6 [412,489] [40,61,763,825,942,943,944,1332] [0,1],a6 [82,103] [40,61,894,1333,1334] [0,1],([0,1,2,272,37,5],[8,40,61,336],[0,2]),([510,316,0,54,55,4],(r 1335 5),[1,2]),([77,0,61,1,2,3],[8,78,102,108,261,298],[0,1,2]),([154,0,1,3,4,5],[8,235],[0,2]),([216,339,0,1,2,3,37,76],[500,557],[]),([8,0,1,3,260,5],[8,55,62,81,128,185,1340],[0,1,2]),([606,0,1,4,620,5],[261,1341,1342,1343],[1]),([511,8,0,1,3,5],[8,55,62,119,128,185,504],[0]),e6 [538,37] [8,40,909,931],([216,339,0,1,2,3,4,21],[485,557],[0]),e6 [339,72] [8,252,404,452,1089,1344],([0,1,2,66,83,4,5,72],[8,574,575],[0,1]),([144,0,1,2,3,4],[8,376],[0,2]),([339,0,1,2,3,37,5,76],[557,732,1137],[]),([345,0,61,1,3,4,5,72],[8,261,762,826,930,984,1219,1345],[0,1]),([185,484,339,0,1,2,37,5],[463,557,640],[]),([171,0,61,1,2,3,37,5],[8,40,261,339,1039],[0]),([339,0,1,2,3,530,37,5],[557,619,640],[]),a6 [393,72] ([624]++r 867 4++[1346,1347]) [0,1],([339,397,1,2,3,4,5,72],[8,156,300,365,592,599,809],[2]),([339,516,0,2,3,4,5,72],[8,252,300,868,1089,1348],[]),e6 [171,339] [8,40,417,452],([0,61,1,2,3,502,5,76],[8,261,290,810,894,1349,1350],[0,1]),([216,384,0,1,2,66,3,4],[8,633,1141],[0]),([171,339,0,1,2,3,5,72],[8,383,417,809],[0,2]),u6 [499,498] ([8,370,1038]++r 1351 7),e6 [622] [8,232,253,452,1358,1359,1360],([216,217,339,0,1,2,3,4],[373],[0]),e6 [623] [40,232,252,271,827,1361],a6 [624,76] [8,80,1137,1362,1363,1364] [1],([8,0,136,1,3,5],[8,55,62,185,1365],[0,1,2]),([449,0,1,40,37,5],[8,465,1294,1366,1367],[]),e6 [384,624] [8,370,1364],([157,0,61,1,2,3,29,76],([261,341,342,493,1196]++r 1368 5),[0,1]),([339,0,1,2,3,4,517,76],[525,557,1137],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_21_7_1 : checkNodesBT W_21 g_21 F_21 P_21_7 A_21 B_21_6 7 N_21_7_1 = true := by decide +kernel
def N_21_7_2 : List NodeSpec := [([0,1,2,66,3,4,517,76],[633,876],[0]),([384,339,0,1,2,3,4,517],[40,557,618,911],[]),([339,0,1,2,3,523,5,76],[8,562,640],[1,3]),([222,0,1,538,2,4,5,21],[],[0]),([222,339,394,1,2,4,5,21],[462],[]),([394,1,2,3,4,543,5,21],[8,40,959,1373],[0]),u6 [222,525] [300,370,453,1374,1375,1376],([0,1,2,66,37,5,21,76],[487,633,1377],[0]),([222,339,0,1,22,4,5,21],[],[0]),([0,85,2,40,86,5],[8,267,510,627,1378],[0,2]),([171,394,61,1,2,3,4,5],[8,40,261,400,1221],[0]),([222,278,339,0,1,2,4,5],[456,640,810,902],[1]),([0,1,538,2,28,4,21],[40,276,300,314,315,344,371,932,1379],[1]),([77,339,0,1,2,3],[0,8,80,93,102,261,559],[0,1,2]),u6 [536,212] [61,851,1380],([157,339,0,1,2,3,29,76],[342,494,1196,1370,1381,1382],[0,1]),([394,1,538,2,3,4,5],[40,233,400,401,528,657,673,888,922],[]),([77,0,1,2,3,10,76],[8,93,108,300,1383],[0,2]),u6 [538,74] [40,61,763,829,925,932],([217,0,61,66,3,4,37,5],[90,1384],[0,1]),([8,0,1,3,5,141],[8,128,185,1385],[0]),([157,278,0,1,2,29],[8,649,1196],[0,1,2]),([412,0,1,2,4,37,5,21],[8,40,899,918,1226,1227,1386],[0]),u6 [157,525] [1374,1375],u6 [412,74] [40,61,263,899,946,1387,1388],([339,394,1,22,3,4,5,21],[8,80,657,1389],[]),([0,61,66,3,4,37,5],([83,90,363,390]++r 1390 4),[0,1]),e6 [625] [232,253,452,1287,1394,1395,1396],([339,394,1,2,3,4,5,72],[8,399,400,401,657,775,1397],[2]),([0,492,626,3,4,5],[8,1303,1398,1399,1400],[]),([171,339,394,1,2,3,4,5],[8,40,501,657],[]),([302,345,0,1,2,28,4,21],[8,276,315,371],[0]),a6 [162] [8,40,136,232,233,261,271,452,453,590,867,1401] [0,2],([171,339,0,1,2,3,5,76],[8,557,670,856],[0,2]),([487,394,1,2,3,4,5,21],[8,40,831],[0]),([0,1,627,3,4,92],([8,748]++r 1402 4),[2]),([339,0,1,22,28,4,21],[8,80,315,371,796,1406,1407,1408],[1]),([339,0,1,2,83,4,5,72],[8,573,574,575],[1,2]),([449,516,0,3,4,5],[8,518,519,1348],[0]),([339,0,1,22,3,74,4,5],[796,847,1089,1409,1410],[0]),a6 [393,21] [825,826,847,1163,1347,1411] [0,1],e6 [384,628] [8,370,1412],([157,278,339,0,1,2,4,5],[568,810,902],[0,1]),e6 [629,467] [300,1413],([0,1,2,3,616,4,630],[8,252,1414,1415],[]),([8,0,1,51,3,5],[8,55,81,120,128,185,669],[0,1]),([339,0,1,631,3,467,4,5],[8,80,1416],[]),([187,96,0,2,3,5],[8,200,222,225,325,326,438],[0,1,2,3]),([435,8,0,1,3,5],[8,62,81,128,185,661],[0,1,2]),u6 [312,311] [252,271],([0,1,538,2,4,37,5,21],[932],[0]),([302,171,394,1,2,3,5],[8,401,1417,1418,1419],[]),([8,0,1,550,3,5],[8,62,81,120,128,185,1420],[0,1]),([15,8,0,1,3,5],[8,55,62,128,185,621],[0,1,2]),([8,0,1,3,10,5],[8,55,62,81,128,185,1421],[0,1]),([302,56,0,1,4,5],[8,76,106,190,255,1422],[0,1]),e6 [618,632] [8,40,261,1355,1423],([394,609,2,3,4,5],[8,400,657,1424,1425],[]),([510,8,0,1,3,5],[8,62,119,120,185,1426],[0]),([410,96,0,2,3,5],[8,200,222,325,326,1427],[0,2,3]),([384,56,0,1,4,5],[8,190,668],[0,1,2]),([0,1,3,198,4,92],[746,748,749,1428],[0,2]),([0,1,522,55,4,5],[8,554,1429,1430],[0]),a6 [243,246] [253,261,452,715,1007,1322,1431,1432] [0,2],([302,479,0,54,55,5],[1215,1335,1336,1433,1434],[0,2]),([0,1,562,55,4,5],[8,365,1279,1335,1435,1436,1437],[0]),([0,9,2,10,4,633,5],([1197]++r 1438 4),[3]),([339,0,1,2,3,485,37,5],[8,40,551,640],[]),e6 [243] [8,232,253,452,1442,1443],([302,479,0,3,634,5],[1215,1216,1444,1445,1446],[2]),([449,0,1,28,4,21],[8,371,1447,1448],[1]),([0,9,91,10,4,92],[748,1197,1232,1449,1450],[0,2,3]),([0,9,2,10,4,635,5],([1197,1232]++r 1451 4),[3]),([0,9,10,4,636,5],[1197,1232,1455,1456,1457],[3]),u6 [199,198] ([252,271,747,1001,1428]++r 1458 4),([394,1,2,66,3,4,5,72],[365,400,401,657,775,1462],[0]),([637,0,9,2,4,5],[261,1197,1230,1463,1464],[2]),e6 [638] [232,252,253,271,370,452,1465,1466,1467],([302,479,0,2,3,639,5],([1216]++r 1468 4),[2]),([339,0,1,22,3,4,5,72],[185,847,1089,1410,1472],[1]),e6 [638,258] [61,1467],([93,0,9,1,3,4],[8,36,46,80,324,1473],[0,1]),([0,1,2,3,640,76],[8,341,1474],[3]),([222,0,1,2,66,467,4,5],[40,487,1067],[0]),([583,0,1,477,3,4,5,72],[302,365,869,870,1089,1347,1475],[0,1]),([171,339,0,1,22,3,4,5],[8],[]),e6 [642] [8,61,232,253,370,452,1476,1477,1478],([345,346,0,1,2,28,4,21],[8,276,277,315,371],[0,1]),([216,171,0,1,2,3],[8,304,305],[0,2]),e6 [498,37] [40,483,987,1038],([0,1,2,66,3,523,5,76],[8,487],[0,1]),([302,93,0,1,3,4],[8,37,40,46,80,261,322,324,1479],[0,1]),e6 [498,21] ([8,40]++r 1351 4++[1357,1480]),([361,643,1,2,3,360,4,5],[261,1481,1482,1483],[]),a6 [498,500] [8,370,1351,1352,1353,1355] [0,1,2],u6 [37,371] [8,968,970,1079,1484],a6 [628,76] ([8,261,1412]++r 1485 5) [1],([302,0,2,3,644,4,5],[8,1490,1491],[]),e6 [302,387] [8,252,326,370,1492],e6 [623,258] [827],([412,0,1,2,28,4,21],[40,276,277,314,315,344,370,371,517,672,899],[0,1]),([345,346,0,1,2,4,37,5],[1493,1494],[0]),([93,0,1,3,309,4],[8,40,46,80,261,322,324,1495],[0]),([93,0,1,3,10,4],[8,40,80,261,322,324,1496],[0,1]),([0,492,1,2,28,4,7,21],[8,40,276,277,314,315,371],[0,1,3]),([345,0,1,2,28,4,95,21],[8,277,315,371],[1,3]),([0,1,2,28,4,203,21],[8,277,315,344,371,1497,1498],[1,2]),([302,479,0,2,28,21],[8,276,277,1216,1499],[0,2]),([394,1,2,3,4,203,5],[8,233,401,657,775,1500],[]),u6 [345,346] [271,452,1308,1501],u6 [171,66] [8,40,271],u6 [306,76] [271,365,452,1502,1503],u6 [492,311] [8,40,252,271,845,847,1504,1505,1506],([0,450,2,28,4,21],[8,276,1507,1508],[1]),([302,645,479,0,3,5],[1216,1434,1509,1510,1511],[3]),u6 [491,467] [252,547,882,939,1512],a6 [348,76] [8,40,61,252,940,941,1513,1514] [0,1],a6 [388,387] ([252,271,818,1492]++r 1515 5) [0,2],e6 [646] [8,232,252,271,1520,1521],([0,61,208,3,4,5],[365,424,443,445,507,845],[0,1]),([302,299,606,479,0,5],[1215,1471,1522,1523,1524],[0,3]),([77,0,128,1,2,3,76],[8,57,93,102,108,629],[0,2]),([302,479,0,91,3,92],[1215,1216,1404,1450,1525],[0,2]),([185,302,186,479,0,2],[1028,1041,1216,1434,1526],[0,2]),e6 [302,519] [252,326,370,1046],a6 [294,137] [253,452] [0,2],([302,171,299,0,1,2,3,5],[855,856,1218,1488],[]),([410,0,1,2,37,212],[8,40,71,72,498],[0,2]),e6 [648,647] [253,1527],([150,93,0,1,3,4],[37,40,46,80,161,261,322,324,458],[0,1]),([302,394,1,2,28,4,21],[8,359,360,517,1105,1107,1126,1528,1529],[0]),([606,96,0,2,3,5],[8,200,222,326,1530],[2,3]),([302,0,1,22,2,28,4,21],[8,276,277,315,371],[0,2]),([78,77,0,1,2,3],[8,57,93,102,108,168,479],[0,1,2,3]),([77,0,1,2,3,10],[8,93,108,261,300,1383],[0,2]),([93,0,1,649,3,4],[8,46,80,322,324,1531],[1]),([353,1,2,37,5,212],[8,70,593],[0,2]),e6 [345,650] [253,452,763,930],([302,345,394,1,2,3,4,5],[8,400,657,775],[0]),a6 [565,243] [253,452] [0,3],([302,171,0,1,22,2,3,5],[855,856,917,1532],[2]),u6 [225,37] [8,271,1079,1533],e6 [651] [61,232,253,370,452,1469,1534,1535,1536],([307,93,0,1,3,4],[8,37,40,46,80,161,261,322,324,455],[0]),e6 [651,639] [370,1469],([0,492,1,22,2,28,4,21],[8,276,277,315,371,1406],[1]),([606,209,0,2,3,4],[8,133,300,682,686,1537],[3]),([171,278,0,1,2,5],[8,426,427,1538],[0,2]),([77,606,0,1,2,3],[8,57,93,102,1539],[3]),([0,1,2,66,40,37,5,72],[8,267,413,465,510,877,878,1540],[0]),([410,0,580,1,2,3,4,212],[8,851,852,1541],[0]),([157,278,0,1,2,66,4,5],[810],[0,1]),([381,0,61,1,3,4,5,212],[8,80,253,851,1542,1543],[0]),([0,61,1,2,40,100,37,5],([176,267,338,339,413,465,510,530,952,953]++r 1544 4),[0]),e6 [605,652] [8,40,253,261,452,827,1548,1549,1550],([449,0,584,1,3,4,5,72],[8,40,80,261,365,870,1290,1291,1293,1294,1295,1551],[0]),([0,1,2,653,3,647,5],([252]++r 1552 5),[]),([508,93,0,1,3,4],[8,36,37,46,80,261,322,324,1557],[0,2]),([93,0,1,40,3,4],[46,80,161,322,324,549],[0,2]),([0,1,2,137,37,5],[8,40,267,318],[0,2]),([0,1,2,37,141,212],[8,71,72,1558],[0]),([0,1,2,40,515,5],[8,510,1559],[0]),([577,0,1,2,40,5],[8,510,1560],[0]),a6 [143,76] [40,61,255,261,574,575,709,711,1561] [0,1],([222,0,1,2,655,5],[8,1562,1563,1564],[0]),([0,1,2,656,37,5],[8,40,185,465,1565],[]),u6 [381,382] [271,452,1284,1541],([381,0,1,2,37,5,212],[8,71,72,338,449,593,1566],[0,2]),([0,492,1,2,4,404,5],[8,1567,1568,1569],[2]),([532,0,1,2,37,5],[8,40,61,326,510,1570],[0]),([0,1,40,37,581,5],[8,465,1571,1572,1573],[0]),([657,0,2,40,37,5],[8,267,1574,1575,1576],[]),([0,1,2,40,100,72],[8,338,387],[0,2]),([222,0,658,1,2,639,4,5],[40,261,1469,1535,1577,1578,1579],[]),([0,450,2,40,37,5],[8,267,1580,1581,1582],[]),([216,217,0,1,2,40],[8,607],[0,2]),([52,8,0,1,3,5],[8,55,62,81,119,120,128,185,1583],[0,1]),([171,0,61,1,2,3,5,76],[8,40,261,290,855,856,1584],[0]),e6 [658,659] [40,61,252,261,1469,1585,1586,1587],([47,0,1,3,4,5],[8,756,987,1131],[0,2]),([0,492,1,2,74,37,5],([8,384]++r 1588 6),[2]),([449,397,1,3,4,5],[8,80,592,1290,1291,1594],[]),([0,450,2,541,3,4,5,72],[365,867,1234,1595],[0,1,2]),([171,182,0,1,2,4],[8,40,188,242,286,287,288,785,1596,1597],[0,2]),([449,0,1,660,3,4,5,72],[80,518,870,1089,1347,1598],[]),([339,0,1,537,3,4,5,212],[8,365,452,1599],[0]),([449,0,1,477,3,4,5],[302,869,870,1347,1475,1600,1601],[0]),([449,0,450,3,4,5],[8,1234,1347,1602,1603,1604],[]),([0,1,2,3,84,76],[96,290,329,331,341,342],[0,1,3]),([171,0,450,2,3,5],[8,383,1605],[0,2]),([171,0,450,1,2,3,5],[8,383,433,954,1605],[0,2]),([510,571,661,316,0,3],([1339]++r 1606 4),[0,2]),([449,516,0,1,3,4,5],[8,452,518,519,1348],[0]),([216,339,0,1,2,3,4,72],[407,809],[0,1]),u6 [449,516] [271,452,518,867,869,1348],([0,662,2,4,663,5],[1063,1066,1610,1611,1612],[3]),([77,0,128,1,2,3],[8,57,93,102,108,261,629,1613],[0,2,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_21_7_2 : checkNodesBT W_21 g_21 F_21 P_21_7 A_21 B_21_6 7 N_21_7_2 = true := by decide +kernel
def N_21_7 := N_21_7_0 ++ N_21_7_1 ++ N_21_7_2
def B_21_7 : BT (List (List Nat)) := buildBucketsBT W_21 N_21_7
set_option maxRecDepth 500000 in
lemma B_21_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_21 7 xs.toFinset) B_21_7 := by
  have hP := buildPoolsSubBT_sound (pdepth := 12) (W := W_21) (raw := r_21) (pspecs := ps_21) (used := U_21_7) S_21_ok
  have hm0 := checkNodesBT_mem (by decide) gp_21 W_21_ok hP A_21_ok B_21_6_ok C_21_7_0
  have hm1 := checkNodesBT_mem (by decide) gp_21 W_21_ok hP A_21_ok B_21_6_ok C_21_7_1
  have hm2 := checkNodesBT_mem (by decide) gp_21 W_21_ok hP A_21_ok B_21_6_ok C_21_7_2
  exact buildBucketsBT_of_mem (forall_append (forall_append (hm0) hm1) hm2)
def U_21_8 : List Nat := ([2,4,8,11,21,37,40,45,49,50,60,61,79,80,83,90,97,110,119,151,176,180,185,206,208,211,232,233,252,253,255,261,263,264,267,271,276,277,290,300,311,314,315,326,338,339,341,342,344,348,363,365]++r 368 4++[390,400,401,403,413,421,452,453,465,483,487,493,505,508,509,510,517,528,557,574,575,581,593,598,616,624,633,640,657,673,675,709,711,715,727,747,748,749,762,763,765,766,775,796,798,802,807,809,810,812,814,818,825,826,827,829,831,834,843,845,847,848,851,852,853,855,856,858,859,862,863,865]++r 867 5++[874,876,878,882,883,884,887,888]++r 892 4++[898,899,901,902,904,905,906]++r 908 4++[913,914,916,917,918,920,922,924,925]++r 928 6++[937,938,940,943,944,946,951,952,954,958,959]++r 967 4++[977,980,982,984,987,988,995,997,999,1000,1001,1003,1007,1009,1010,1011,1018,1022,1024,1027,1028,1034,1035,1038,1041]++r 1043 5++[1050,1052,1053,1056,1057,1063,1065,1066,1067]++r 1072 8++[1081,1082,1085,1087,1088,1089,1098,1103,1104,1106,1111]++r 1113 6++[1120,1122,1123,1124,1129,1131,1133,1135,1136,1137,1139,1140,1141,1144]++r 1146 4++[1152,1154,1155,1163,1169,1170,1172,1173,1176,1177,1185,1188,1190,1193,1194,1196,1197,1199,1207,1211,1212,1213,1215,1216,1217,1219,1220,1221,1223,1227,1229,1230,1232,1235,1240,1243,1245,1246,1247,1250,1252,1253,1258,1260,1261,1267,1268]++r 1276 7++[1284,1286,1287,1291,1293,1301,1303,1304,1308,1310]++r 1313 4++[1319,1325,1329,1335,1336,1338,1339,1344,1347,1350]++r 1352 6++[1360,1362,1364,1370,1372,1373,1384,1386,1387,1389,1390,1392,1393,1403,1404,1409,1410,1412,1414,1423,1430,1431,1434,1436,1438,1441,1443,1445,1450,1451,1452,1456,1457,1460,1461,1466,1468,1469,1471,1477,1480,1481,1484,1485,1488,1489,1490,1493,1494,1501,1506,1509,1510,1512,1521,1522,1523,1532,1533,1535,1541,1545,1546,1549,1550,1553,1555,1563,1592,1606,1608]++r 1614 944)
def P_21_8 : BT (Option BoundPool) := buildPoolsSubBT 12 W_21 r_21 S_21 ps_21 U_21_8
def N_21_8_0 : List NodeSpec := [u6 [496,467] [8,80,253,370,995,1085,1140,1287,1347,1512,1614,1615],a6 [492,21] [8,271,365,898,1308,1347,1501,1616,1617,1618] [2],([0,450,2,3,4,5,21],[8,365,825,1347,1619],[0,1]),([185,278,0,1,2,4,5],[8,810,901,902,1620],[0,2]),([0,1,2,3,502,5,76],[8,370,453,1350],[0,2]),u6 [171,345] [8,40,253,452,762,855,917,930,1621,1622,1623],a6 [345,72] [8,762,763,826,906,916,1076,1078,1347,1624,1625,1626] [0,3],u6 [345,346,21] [8,762,763,825,845,847,930,1188,1627],a6 [345,346] ([8,261,271,762,763,825,929,1219]++r 1627 6) [0,2],([0,609,2,3,4,5,21],[8,252,825,847,1633],[0,2]),u6 [345,461] ([8,97,185,762,763,1626]++r 1634 5),a6 [664,467] [8,271,365,995,1140,1347,1512,1615,1639] [2],a6 [171,492] [8,40,252,271,855,856,1303,1506,1621,1640,1641] [2],a6 [492,74] [8,263,264,829,845,1194,1303,1387,1506,1592,1618,1642,1643,1644] [0,1,2],a6 [608,76] [8,261,365,818,940,1047,1057,1347,1645] [0,1],([171,0,1,2,28,4,21],[8,40,276,277,315,344,371,1646],[0,1,2]),([77,0,1,2,3,76],[8,79],[0,1,2,3]),([77,0,1,2,3],[79],[0,1,2,3]),([592,0,1,2,3,29,76],[8,341,342,368,369,1370,1647],[0,1]),([0,492,1,2,28,4,21],[8,40,276,277,314,315,344,371,1124,1618],[0,1,2]),([394,1,2,28,4,21],[8,80,300,344,517,673],[0,1,2]),([614,0,1,2,3,166,5],([8,40,1043,1045]++r 1648 6),[0]),([0,1,2,3,166,229,5],[8,40,1045,1650,1651,1654,1655],[1]),([0,662,1,2,4,30,5],([8,1063,1066]++r 1656 7),[0]),([222,0,1,2,467,4,5],[8,40,1085,1087],[0,2]),([222,0,492,1,2,4,5,21],[8,892,893,1098,1663,1664,1665],[0,2]),([0,1,2,3,523,5,76],[8,61,1018],[0,1,2,3]),([0,1,2,3,4,517,76],[8,370,453,1243],[0,2]),([0,450,2,3,4,37,5],[8,40,969,1304,1666],[0]),([171,0,1,2,3,5,72],[8,1667],[0,2]),a6 [216] [8,232,252,253,271,452,1668] [0,2],([0,1,3,4,37,581,5],[8,40,987,1669,1670],[0]),([0,1,2,3,37,5,76],[8,370,453,1199],[0,2]),([0,1,2,3,485,37,5],[8,40,61,1258],[0,2]),([171,0,1,2,3,37,5],[8,61,855,856,1671],[0,2]),([0,1,2,3,100,37,76],[8,40,1141,1240],[0,2]),([449,0,1,3,4,5,21],[8,847,1347,1672],[0,2]),([0,1,2,37,5,21,76],[8,61,1141,1329],[0,2]),([0,492,1,2,4,37,5,21],[8,1386,1493,1494,1618,1673,1674],[0,2]),([216,0,1,2,3,4,72],[8,1675],[0,1,2]),e6 [38,86] ([8,97]++r 1676 6),([0,85,2,3,4,86,5],[8,969,970,1682],[0,2]),([217,0,1,2,40,37,5],[8,40,267,338,413,465,508,510,802,1683,1684],[0,2]),([171,394,1,2,3,4,5],[8,233,400,401,657,775,1220,1221],[0,2]),([216,0,1,2,40,37,5],[8,61,267,413,465,483,508,510,1685,1686],[0,2]),a6 [449,72] [8,80,253,867,868,870,1280,1291,1347] [0,2],([0,1,2,40,37,5,72],[8,267,413,465,509,510,675,951],[0,2]),([0,1,2,28,74,4,21],[8,276,277,315,371,1193,1194],[0,1,2]),([38,0,1,2,40,37,5],[8,267,413,465,508,510,1687,1688,1689],[2]),([0,1,2,37,5,212],[8,40,61,483,593],[0,2]),([592,375,1,2,3,4,5],([8]++r 1690 6),[]),([222,394,1,2,4,5,21],[8,888,1075,1098],[0,2]),([0,1,2,40,37,86,5],[8,40,413,465,510,1680,1696,1697],[0]),a6 [381,212] [8,61,80,253,453,747,851,852,1190,1284,1347,1541,1698] [0,2],([353,1,2,3,4,5,212],[8,80,232,300,365,807,1116,1117,1118,1190],[0,2]),e6 [665] [40,61,232,252,271,452,1699,1700,1701],([410,0,1,2,40,37,5],[40,267,465,508,510,1702,1703,1704],[0,2]),([410,0,1,2,3,4,212],[8,61,453,851,852,1115,1701,1703],[0,2]),e6 [666] [40,252,261,271,1414,1705,1706,1707],e6 [667] [8,232,233,253,271,370,452,1314,1708],a6 [450,72] [8,271,365,867,869,870,1280,1304,1347] [0,1,2],e6 [669] [8,252,271,1131,1709,1710],e6 [670] [8,253,452,505,1711],([510,316,0,2,3,4,37],[8,969,970,1338,1339,1608,1712],[0,2]),e6 [672] [8,253,452,1713,1714,1715],([185,0,1,2,671,4,5],[8,252,1716,1717,1718],[]),([589,0,1,3,4,5,21],[8,845,847,1719],[0]),([0,1,2,3,673,5,76],[8,370,1057,1720],[]),u6 [655] [8,233,253,452,1721,1722],([185,674,0,1,2,4,5],[8,271,1155,1723,1724],[]),([222,654,0,1,2,3,5],[8,1123,1563,1725],[0]),e6 [675] [8,253,452,1185,1726],u6 [577] [8,232,253,452,970,1727],a6 [72] [8,233,252,253,271,452,1252] [0,2],u6 [515] [8,233,253,452,970,1728],([0,1,2,40,37,5,141],[8,413,465,510,1729,1730,1731],[0]),([0,136,1,2,40,37,5],[40,267,338,413,465,508,1553,1732,1733],[0]),a6 [137] [253,452,505,747,1235,1436,1553] [0,2],([0,1,2,28,4,21,72],[8,276,277,315,371,517,913,916],[0,1,2]),([222,0,136,2,3,4,141],([8,1088,1177]++r 1734 6),[2]),([0,136,2,3,4,37,141],([8,970,1079]++r 1737 4),[0,2]),([93,0,1,3,4],[37],[0,1,2,3]),u6 [605,258] [40,252,261,827,1056,1466,1549,1550,1741,1742,1743],a6 [676,647] ([8,40,252,255,261,1553,1555]++r 1744 7) [3],([0,1,2,3,647,37,5],[8,40,261,453,1555,1751,1752],[]),u6 [596,258] [40,185,252,253,261,827,1056,1436,1466,1741,1742,1753,1754,1755],a6 [658,639] ([40,253,261,1468,1469,1535]++r 1756 6) [0,2],e6 [677] [8,232,233,252,271,1762,1763],e6 [678] [8,232,252,271,452,1764,1765],([606,0,1,2,3,29,76],[8,341,369,493,1196,1370,1766,1767],[0,3]),([0,136,2,40,3,4,141],[747,1176,1737,1738,1739,1768,1769],[0,2]),([606,0,1,2,4,30,5],([8,253,928]++r 1770 5),[]),([560,606,0,2,3,4,5],[1276,1277,1767,1774,1775,1776],[3]),a6 [679] [8,252,271,1777,1778,1779] [2],e6 [680] [8,40,61,232,255,452,453,1701,1780,1781,1782],([510,606,316,0,2,3,4],[8,1338,1339,1775,1783,1784],[0,1]),e6 [681] [8,452,453,1423,1785,1786],([682,0,1,2,4,30,5],[8,1063,1066,1656,1659,1660,1787,1788,1789],[3]),a6 [606,647] [40,252,1553,1555,1744,1746,1747,1767,1775,1790] [3],([606,0,1,2,258,4,5],[8,40,252,261,365,827,1767,1791,1792],[0]),([684,1,2,3,4,5,683],([8,80,232]++r 1793 4),[]),e6 [686] [8,232,252,271,452,1797,1798],e6 [687] [8,233,252,271,1799,1800],e6 [302,467] ([8,40,326,995,1067,1140,1512,1615]++r 1801 4),e6 [302,21] ([8,40,326,895,898,1308,1501,1617]++r 1802 7),e6 [688] [40,61,232,253,261,452,1718,1807,1809,1810],a6 [157,128] ([8,765,766,1022]++r 1811 6) [0,2],([302,0,1,2,3,74,5,21],[8,40,185,263,264,727,918,1817],[0]),a6 [302,22,21] [8,365,763,825,845,847,1410,1804,1818] [0,2],a6 [519,76] [8,940,1007,1047,1057,1819] [1,3],([302,0,1,2,3,166,5],[8,40,271,1043,1045,1648,1650,1651,1807,1808,1820,1821],[]),([302,645,0,1,3,4,5],[1509,1510,1803,1807,1808,1822,1823],[0]),([302,0,1,3,634,4,5],[370,453,1445,1804,1807,1808,1824,1825,1826],[0]),u6 [302,616] [40,252,255,261,1211,1212,1414,1701,1804,1808,1827,1828],([510,571,316,0,2,3,4],([8,252,261,1267,1338,1339,1608]++r 1829 4),[0,2]),([449,0,1,3,4,37,5],[8,40,987,1291,1293],[0]),e6 [689] [8,40,255,261,1488,1833,1834,1835],([0,85,1,2,40,37,5],[8,267,413,465,508,509,510,1836,1837,1838],[0]),e6 [690] [40,61,252,261,453,1829,1839,1840,1841],e6 [302,683] ([8,80,252,453,1767,1794,1802,1804,1807]++r 1842 4),e6 [691] [8,61,232,271,326,370,453,1804,1807,1846,1847,1848],e6 [302,384,299] ([8,40,326,1488,1808]++r 1849 4),u6 [656] [185,252,271,747,1701,1853,1854],a6 [302,299,21] [8,255,763,825,1803,1804,1807,1808,1850,1852,1855,1856] [0,3],([606,0,136,2,3,4,141],[8,1734,1737,1738,1767,1857],[0,3]),e6 [302,299,37] [40,61,255,261,969,1131,1488,1803,1804,1807,1850,1852],e6 [692] ([8,61,185,232,271,370,452,453,711,1829]++r 1858 6),([302,299,0,1,3,4,5,92],[8,1803,1864,1865],[]),([0,1,2,3,4,100,72],[8,1079,1319],[0,2]),([302,479,0,2,28,3,5],[1147,1215,1216,1434,1471,1866,1867,1868],[0,2,3]),([302,479,0,2,3,5,92],[8,1215,1423,1869,1870],[0,2]),([302,479,0,91,2,3,5],[1213,1216,1434,1471,1871,1872,1873],[0,2]),([302,606,479,0,2,3,5],[8,1215,1434,1775,1783,1874],[0]),([222,278,0,1,2,4,5],[8,810,901,902,1875],[0,2]),([302,299,606,0,1,4,5],[8,1522,1523,1803,1804,1876,1877],[0]),([0,1,2,40,100,37,5],[8,40,267,338,413,465,483,509,510,1545,1546,1878],[0,2]),([0,1,2,3,4,693,76],[8,370,1057,1879],[]),e6 [302,694] ([8,253,261,1803]++r 1880 5),e6 [695] [8,232,252,253,452,1885,1886],([606,0,2,3,4,696,5],([271,1767,1774,1783]++r 1887 4),[3]),e6 [697] [8,233,253,271,452,1891,1892],([0,1,2,3,698,37,5],[8,40,1752,1893,1894],[]),u6 [602,92] [8,261,1521,1807,1869,1895,1896],e6 [699,641] ([8,40,185,253,261,1477]++r 1897 7),([0,1,3,641,4,5,92],[8,261,1904,1905],[]),e6 [700] [8,253,452,1906,1907],([394,1,2,3,4,5,461],[8,401,657,727,775,1908,1909,1910],[0,2]),([185,186,0,1,2,4,95],([40,1027,1028]++r 1911 5),[0,1]),u6 [602,76] [8,40,261,818,940,1047,1057,1521,1916,1917,1918],a6 [243,76] [8,818,940,1007,1047,1431,1919] [1,3],a6 [345,95,21] [8,762,763,845,847,1920,1921] [0,3],([171,0,1,2,3,5,76],[8,370,855,856,1922],[0,2]),([302,186,479,0,2,3,5],[8,1215,1216,1471,1907,1923,1924],[0,3]),e6 [302,641] [8,185,253,261,326,1803,1808,1897,1899,1901,1902,1925,1926],a6 [492,7,21] [8,40,365,763,825,845,847,918,1353,1506,1927] [0,3],([0,1,2,28,4,95,21],[8,40,300,314,315,371,1912,1928],[0,1,2]),u6 [492,22,21] [8,365,763,825,845,847,1410,1506,1532,1929],([216,384,0,1,2,3,4],[8,370,1930],[0,2]),([0,1,2,3,95,166,5],[8,40,252,1045,1650,1651,1911,1931],[1]),([560,0,2,3,55,4,5],([1276,1277]++r 1932 5),[0]),([0,1,3,10,4,636,5],([1355,1456,1457]++r 1937 4),[0]),([598,384,0,1,2,3,5],[40,261,862,1073,1941],[0]),e6 [701] [8,40,253,261,452,1942,1943],([598,0,1,2,3,29,5],[40,261,1944,1945,1946],[0]),([510,316,0,2,40,3,4],[505,1267,1338,1339,1608,1769,1947],[0,2]),e6 [702] [8,232,233,253,271,452,1948,1949],e6 [703] [8,253,452,845,1950],u6 [599] [8,253,452,1951,1952,1953],([462,0,1,2,3,5,21],[8,845,1089,1954],[0]),([704,186,0,1,2,3,4],[8,271,370,1907,1955],[]),([394,1,2,3,4,5,21],[8,80,232,300,365,887,888,898],[0]),u6 [467,95] ([8,1140,1287,1615,1920]++r 1956 4),([339,0,1,2,40,37,5],[8,11,40,60,267,465,508,640,798],[0]),e6 [705] ([40,261]++r 1960 6),([654,0,1,2,3,5,76],[8,370,1007,1966],[]),([0,9,1,91,3,4,92],[8,748,1403,1404,1967,1968,1969],[0]),([171,0,1,2,37,5,21],[8,61,1671],[0,2]),e6 [706] [8,233,452,1907,1970,1971],a6 [61,37,72] [8,40,261,290,867,954,970,987,1131,1260,1280,1281,1972,1973] [0,1],u6 [607] [61,80,232,261,370,453,487,633,1945,1974,1975],e6 [707] [8,232,233,252,253,271,452,1976,1977],e6 [708] [40,261,453,1765,1943,1978],([345,394,1,2,3,4,5,21],[8,80,400,401,657,673,775,888,905,1622,1626],[0]),([394,492,1,2,3,4,5,21],[8,365,400,401,657,673,775,905,1640,1979],[0,2]),([0,61,1,2,3,37,5,76],([8,261,290,339,810,894,1050,1053]++r 1980 5),[0,1,3]),e6 [302,709] [8,252,261,452,1804,1985,1986],a6 [217,66,37] [8,40,633,970,1079,1987] [0,1],e6 [710] [8,40,61,80,252,453,1436,1767,1775,1988,1989],a6 [171,66] [8,40,261,487,633,858,876,917,1621,1990] [0,1],([216,217,0,1,2,3,4],[8,1991],[0,2]),a6 [61,212] [8,253,271,339,452,747,851,852,894,1116,1190,1253,1284,1541,1992] [0,2],([0,1,2,28,4,21,461],[8,277,315,371,517,1637,1993],[0,1,2]),e6 [605] [40,61,232,252,253,261,452,1549,1743,1994],u6 [185,66,76] [8,261,487,633,810,876,1007,1155,1995,1996],e6 [711] [40,61,232,261,453,1804,1997,1998,1999],u6 [222,384,61] ([8,261,290,339,894,937,1073,1085,1088,1763,1851]++r 2000 5),e6 [712] [40,61,232,252,261,1965,2005,2006,2007],([617,0,61,1,2,4,5],[290,339,453,894,1245,1247,2008,2009,2010],[0]),e6 [714,713] ([8,252,253,453,1403]++r 2011 5),a6 [66,21,76] ([8,487,633,876,1301]++r 2016 4) [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_21_8_0 : checkNodesBT W_21 g_21 F_21 P_21_8 A_21 B_21_7 8 N_21_8_0 = true := by decide +kernel
def N_21_8_1 : List NodeSpec := [a6 [66,512] [8,261,487,633,933,1114,2020,2021,2022] [0,1],([185,339,0,1,2,4,37,5],[8,40,557,640,1011,1081,1082,1137,2023,2024],[0,1]),([384,0,1,2,3,4,517],[8,40,453,911,1088,1325],[0,2]),([449,0,1,3,4,5,72],[8,253,870,1291,1347],[0]),([654,0,1,2,40,3,5],[8,2025,2026],[0]),e6 [715] ([8,61,252,370,452,453,970,1131]++r 2027 5),([560,0,54,2,3,4,5],([1276,1935]++r 2032 5),[0]),u6 [10,7,37] [40,261,969,970,987,1131,1353,1355,1940,2037,2038,2039],a6 [66,21,72] [8,487,763,825,826,845,847,2019,2040] [0,1],([0,1,2,83,37,5,76],[8,255,598,711,1223],[0,1,2,3]),e6 [716,406] ([40,252,253,261,339,977]++r 2041 6),e6 [704,7] [8,253,261,452,1353,2047,2048,2049],a6 [66,37] [8,40,61,453,487,633,876,1393,2050,2051,2052] [0,1],e6 [355] [8,232,252,253,453,2053,2054,2055],a6 [61,100,37] [8,40,261,290,339,894,969,970,987,988,1131,1546,1972,1973,2056,2057,2058] [0,1],u6 [345,21] [8,80,253,370,453,895,898,1308,1347,1617,2059],a6 [384,66,37] [8,40,487,633,876,1073,1141,2060] [0,1],a6 [538,21] [40,370,453,763,825,845,847,904,918,922,931,932] [0,1],([510,0,2,3,10,4,7,5],[8,300,1353,2037,2038,2061,2062],[]),([0,1,2,66,3,37,5,76],[8,261,487,633,810,876,1053,1980,1983,2063],[0,1]),([0,1,2,66,40,37,5],[8,40,180,465,487,510,878],[0]),([157,278,0,1,2,4,5],[8,810,901,902,2064],[0,1,2]),([617,0,1,2,66,4,5],[61,370,453,487,633,876,1247,2010,2065],[0]),e6 [718] [8,2066,2067,2068],([222,0,1,2,616,4,5],[40,185,255,452,1700,1701,2069],[]),([0,1,2,66,3,166,5],[8,40,453,633,876,1045,1650,2070],[0]),([0,61,1,2,28,4,21],[8,40,276,277,290,314,315,344,371,517,914],[0,1,2]),e6 [719,602] ([8,40,252,253,261,326,1521,1807,1918]++r 2071 4),e6 [598,21] ([8,40,261,326,370,763,845,847,904,918]++r 2075 6),u6 [345,492,21] [8,762,763,825,845,847,930,1303,2081],u6 [302,345,21] [8,185,763,825,847,930,1803,2082],u6 [378] [8,61,233,271,452,2083,2084,2085],([302,0,1,2,28,4,21],[8,40,276,277,314,315,344,371,1808,2086],[0,2]),e6 [720] [40,232,261,2087,2088,2089],e6 [721] [40,61,233,261,2090,2091,2092],([510,316,0,54,2,3,4],[8,1338,1608,1831,2033,2093,2094,2095],[0,2]),([510,598,0,2,3,4,5],[8,40,271,2096,2097,2098],[]),e6 [185,487] [40,261,271,452,453,1155,2099,2100],a6 [216,66] [8,40,261,487,633,858,876,1170,2101,2102] [0,1],([185,302,479,0,2,3,5],[8,1155,1215,1434,1471,1718,2103],[0,2]),([510,0,1,54,55,4,5],([8,452,1335,1717]++r 2104 4),[0,1]),a6 [208,21] [40,365,370,453,843,845,847,874,904,910,918] [0,1],([185,186,661,0,1,2,4],[1027,1028,1041,1779,1915,2108,2109,2110],[1,2]),u6 [62] [8,339,370,421,505,894,999,1000,1001],([394,1,2,3,4,95,5,21],[8,300,365,401,657,775,905,1956,2111,2112],[0]),a6 [61,512] [8,40,253,261,290,339,883,933,1111,1114,2020,2022,2113,2114] [0,1],e6 [722] ([8,61,232,252,370]++r 2115 4),a6 [222,66,76] [8,487,633,810,876,1007,1123,2016,2017,2119,2120] [0,1],([384,0,61,66,3,4,5],[83,90,206,271,363,390,1072,1073,1851],[0,1]),([0,9,2,10,4,5,76],[8,810,1007,1232,1441,2121,2122],[0,3]),e6 [723] [40,61,232,252,261,271,452,2123,2124,2125],([0,61,66,3,4,5,21],[83,90,211,390,403,825,845,848],[0,1]),e6 [185,543] [40,252,261,452,1373,1718,2100,2126,2127,2128],e6 [725] [8,253,452,2129,2130,2131],([0,61,66,28,3,4,5],[83,90,208,271,390,403,1147,1866,2132],[0,1]),e6 [726] [8,233,452,970,987,2133],e6 [727] [8,61,232,370,452,453,1779,1782,2134,2135,2136],u6 [361,360] ([61,252,253,261,894,1481]++r 2137 7),u6 [157,61,76] ([8,40,255,709,711,766,810,818,1007,1034,1035,1047,1057,1816]++r 2144 4),([510,222,316,0,2,3,4],[8,1123,1268,1314,1338,1339,1608,1831,2095,2148],[2]),([185,0,61,1,2,4,37,5],[8,40,261,290,339,453,894,1011,1081,2023,2149,2150],[0,1]),([397,1,2,3,4,5,72],[8,80,232,300,365,1260,1261,1280],[0,2]),([0,61,1,2,40,37,5],[8,40,176,267,339,413,465,508,509,510,952],[0]),([185,0,1,2,360,4,5],([40,252,253,261,894,1718]++r 2151 4),[]),a6 [61,467] [8,40,253,261,271,290,339,452,882,883,995,1067,1085,1140,1253,1287,1512,1615,2155] [0,1,2],a6 [61,21,72] [8,40,261,339,845,847,906,908,918,1076,1077,1078,2156,2157] [0,1,2],a6 [171] [8,40,232,252,253,271,452,1667] [0,2],([0,1,2,3,530,37,5],[8,61,370,814],[0,2]),a6 [302,639] [40,253,261,326,1460,1468,1469,1535,1756,1759,1803,1808,2158] [0,3],([510,316,0,2,3,55,4],[8,40,1217,1338,1339,1608,1933,2159],[0,2]),e6 [728] [8,232,253,452,970,2160],a6 [66,37,72] [8,40,633,868,969,970,987,1131,2161,2162] [0,1],a6 [208] [40,61,365,370,843,845,847,874,910] [0,1],e6 [729] [8,232,271,290,452,453,2163,2164,2165],([0,1,2,3,4,713,76],[8,61,453,1057,2013,2166],[]),a6 [258,7] [40,261,827,1436,1466,1742,2038,2167,2168] [0,3],a6 [339,212] [8,640,747,852,1089,1137,1190,1284,1286,1344,2169] [0,2],([657,0,2,3,4,37,5],[8,40,969,2170,2171],[0]),a6 [66,72] [8,40,252,253,261,365,859,868,870,954,1280,1281,2172] [0,1,2],a6 [216,61] [8,40,252,253,261,290,339,452,883,894,1169,1170,2102,2173,2174] [0,1],([302,479,0,54,2,3,5],[8,1213,1434,1471,1868,2033,2093,2175],[0,2]),([0,1,2,83,4,5,72],[8,574,575,920],[0,1,2]),([717,730,1,2,3,4,5],[8,232,598,2176,2177,2178],[]),a6 [412] [40,61,232,233,271,370,452,453,763,825,834,899,943,944,946] [0,1],([185,186,0,1,2,66,4],[40,633,876,1027,1028,1915,2179],[0,1]),([0,1,2,3,406,5,76],[40,261,370,1047,1057,2180,2181,2182],[1]),([185,186,0,61,1,2,4],[40,290,894,1027,1028,1041,1914,1915,2109,2183,2184],[0,1]),([345,0,1,2,28,4,21],[8,40,80,276,277,314,315,344,371,1631,2185],[0,1,3]),a6 [61,21] [8,40,253,261,271,290,339,452,453,883,887,894,895,898,1253,1308,1501,1617,1806,2186] [0,1,2],([339,0,1,2,3,166,5],[8,40,557,1043,1044,1137,1648,1650,2187],[]),a6 [185,484,61] [40,261,290,339,894,933,1011,2188] [0,1],e6 [731] ([8,61,232,271,370,452,453,969,1131]++r 2189 5),e6 [732] [8,61,185,232,370,453,487,876,1769,1854,2194],([384,0,1,2,3,4,354],[8,252,253,290,2195,2196,2197],[]),u6 [66,37,21] [8,261,453,487,633,876,909,2161,2162],([222,345,0,1,2,4,5,21],[8,892,1173,1632,1665,2198],[0]),([185,484,0,1,2,37,5],[8,61,370,453,933,1011,2199],[0,2]),([0,1,2,3,4,141,212],[8,61,252,453,851,852,2200],[0]),([222,0,1,2,360,4,5],[8,252,253,261,894,1314,1316,2142,2201,2202,2203],[0,1]),a6 [733,76] [8,255,261,818,940,1007,1057,1347,2204] [1,3],a6 [157,66,76] [8,810,958,1007,1010,2016,2017,2205] [0,1],([185,0,1,2,512,4,5],[8,933,2206],[0,2]),u6 [66,30] [8,61,261,487,633,1066,1656,1659,2207,2208],a6 [171,61,21] [8,40,261,290,339,825,855,856,894,1221,2209] [0,1,2],([222,0,1,2,66,4,5,21],[8,40,487,633,876,918,1098,1173,1665,2210],[0,1]),e6 [520] ([40,261,2142]++r 2211 6),([157,0,1,2,3,29,76],[8,341,342,368,369,493,1196,1370,1372,2217],[0,1,2]),e6 [734] [8,232,252,253,271,452,1131,2218],a6 [171,339,21] [8,40,557,640,847,982,1137,1621,2219] [0,1,2],([185,0,61,66,3,4,5],[83,90,110,271,363,390,1152,1155,1718],[0,1]),e6 [735] [8,232,253,452,1769,2220],a6 [243] [8,253,261,452,715,1007,1431] [0,2,3],([185,0,1,2,66,4,37,5],[8,40,453,487,633,876,1011,2023,2150,2221,2222],[0,1]),([345,0,61,1,3,4,5,21],[8,185,253,261,763,847,930,984,1207,1219,2223],[0]),a6 [66,100,37] [8,40,487,633,876,969,970,987,1079,1131,1533,2161,2162] [0,1],e6 [361] [40,61,232,233,252,253,261,271,452,2138,2141,2143,2224,2225,2226],e6 [736] ([8,61,232,252,253,370]++r 2227 4),e6 [737] ([8]++r 2231 4),a6 [339,37,72] [8,40,557,624,870,969,970,1131,2235,2236] [0,1,2],([0,61,66,3,4,37,5],[50,83,90,390,967,969,970],[0,1]),a6 [360,76] [40,61,261,894,940,1047,1057,2137,2142,2237] [0,1],e6 [185,406] [40,252,253,261,339,977,1718,2042,2043,2045,2154,2238],e6 [738] [8,40,253,261,452,2239,2240],a6 [739] [40,253,271,452,1147,1807,1808,2241,2242] [3],([0,1,2,3,4,354,21],[8,252,253,453,2243,2244,2245],[]),([0,61,1,2,3,166,5],[8,40,290,894,1043,1045,1648,1650,1651,2246,2247],[0]),a6 [616,95] [40,255,261,1212,1414,1701,1912,1956,1959,2248,2249] [1],a6 [384,61,37] [8,40,261,290,339,894,1141,2250,2251] [0,1],([394,1,2,66,3,4,5,21],[8,80,261,365,401,528,657,831,858,888,905,2018,2019,2252],[0]),a6 [412,21] [40,370,453,763,825,834,845,847,899,904,905,918,946] [0,1],e6 [740] [8,232,233,271,452,2253,2254,2255],a6 [61,72] ([8,40,253,261,271,452]++r 867 4++[883,954,1253,1260,1280,1281,2256]) [0,1,2],a6 [9,633] ([40,253,1403,1438,1461]++r 2257 6) [0,3],([394,61,1,2,3,4,5,21],[8,261,400,401,528,616,657,775,883,888,905,1106,2263,2264],[0,2]),a6 [61,517] ([8,40,253,290,883,894,911,1133,1136]++r 2265 4) [0,1],([222,0,61,1,2,4,5,21],[8,40,290,339,892,893,894,918,1075,1098,1173,1665,2269],[0,1,2]),u6 [66,212] [8,61,365,453,487,747,851,852,859,876,1190,2270],u6 [222,61,76] ([8,40,61,290,339,810,818,894,1007,1047,1057,1123,1314,1316,1700,2144,2145]++r 2271 4),u6 [61,37,21] [8,40,261,290,339,453,825,894,918,969,970,987,1131,1227,1386,1972,1973],([0,1,2,3,406,37,5],([40,339,453,1752,2042]++r 2275 4),[]),a6 [185,484,66] [8,40,261,487,633,876,933,1011,1155,1943] [0,1],u6 [61,30] [8,261,290,339,1063,1066,1656,1658,1659,1660,2208,2279],a6 [334] ([8,40,61,232,233,271,452,894,938,1003]++r 1313 4) [0,1],a6 [538] [40,61,252,370,452,763,845,922,924,925,931,932,1347] [0,1],e6 [742] [8,232,252,253,452,2280,2281],([287,331,0,2,3,4,5],[8,969,970,2282],[0,2]),e6 [743] [8,232,252,271,2283,2284],u6 [222,384,66] [8,40,487,633,876,1073,1085,1088,1123,2285,2286],([521,1,2,3,467,4,5],[8,80,232,300,365,882,884,1512],[0]),a6 [61,21,76] [8,40,261,290,339,763,810,818,825,845,847,894,918,1007,1047,1057,2144,2145,2157,2263,2287,2288] [0,1],([302,171,0,1,2,3,5],[8,40,261,271,855,856,2289],[0]),e6 [744] [40,61,232,252,261,271,1137,1718,2100,2290,2291],([0,1,2,3,745,5,76],[8,370,818,2292],[]),a6 [66,467] [40,80,261,365,487,859,1067,1085,1287,1512,2293] [0,1],a6 [61,83,76] ([8,40,255,290,339,574,575,709,711,810,1057]++r 2294 4) [0,1],a6 [593,76] [40,61,255,261,818,940,1057,1137,1965,2298,2299] [0,1],a6 [66,21] [8,40,80,365,453,487,859,876,895,898,1806,2300] [0,1],([394,1,2,4,37,5,21],[8,528,673,727,1227,1386],[0,2]),a6 [171,61] [8,40,252,253,261,290,339,452,855,856,883,894,917,1221,1621,2209] [0,1],([0,61,66,40,3,4,5],[45,83,90,271,390,505,1769,2301],[0]),e6 [746] [8,61,185,252,370,505,640,1137,1854,2302,2303],([0,9,1,2,4,30,5],([8,271,1770,1772,1773,2208]++r 2304 4),[]),e6 [747] [40,61,232,261,271,452,894,1718,2154,2308,2309,2310],([216,0,1,2,3,37,76],[8,370,2311],[0,2]),a6 [339,37,21] [8,261,453,557,640,1131,1137,1139,1674,2235,2236] [0,2],a6 [216,61,37] [8,40,261,290,339,894,969,2174] [0,1],a6 [384,339,37] [8,40,557,640,980,1137,1141,2312] [0,1],a6 [302,278] [8,370,901,902,1803,1804,1808,2313,2314,2315] [3],a6 [339,100,37] [8,40,557,640,968,969,970,987,1079,1131,1137,1484,2235,2236] [0,1],([0,1,2,3,748,5,76],[8,370,453,1057,2316,2317],[]),([0,450,2,3,4,5,72],[8,271,365,867,1304,1347],[0,1,2]),a6 [216,339] [8,40,252,261,271,452,557,640,809,1137,1144,1169,2102,2318] [0,1],e6 [750] [8,232,252,253,452,2319,2320],e6 [751] [8,232,233,252,271,370,2321,2322,2323],e6 [752] [8,233,252,271,2324,2325],a6 [216,339,37] [8,40,557,640,987,1137,1144] [0,1],u6 [185,61,76] [8,40,261,290,339,810,894,1011,1155,1718,2100,2154,2326,2327,2328],e6 [753] [8,61,185,232,253,370,452,1217,1786,1936,2329,2330],([510,571,661,0,1,3,5],[8,1606,2107,2331,2332,2333],[0]),a6 [217,339,37] [8,40,557,987,1079,1384] [0,1],([222,0,61,66,3,4,5],[2,49,83,90,271,363,390,403,1120,1123,1314],[0,1]),([0,9,91,2,10,4,5],[1197,1230,1441,1460,1872,2334],[0,2,3]),([287,0,1,2,40,37,5],[8,40,267,311,338,413,465,508,510,2335,2336],[0]),a6 [216,66,37] [8,40,487,633,876,970] [0,1],a6 [339,37] [8,40,557,640,1137,1390,1392,2050,2052,2337] [0,1],([222,339,0,1,2,4,5,21],[8,40,557,640,892,918,1137,1172,1665,2338],[0,1,2]),a6 [9,635] ([40,185,452,1403,1451,1703]++r 2339 6) [0,1],a6 [302,186,55] [8,1807,1808,1907,1923,1934,1971] [3],a6 [66,83,76] [8,487,633,810,818,958,1007,1047,1057,1104,2345] [0,1],a6 [222,339,76] ([8,557,640,810,818,1047,1122,1137,1316,1700]++r 2346 4) [0,2],([0,1,2,66,28,4,21],[8,40,80,277,314,633,853],[0,1]),a6 [339,72] [8,40,261,624,867,870,954,1089,1280,1281,1344,2350] [0,1,2],u6 [222,384,339] [8,40,557,640,1074,1085,1088,1137,1700,1763,2002,2351,2352],([394,1,2,3,4,5,72],[8,348,400,401,657,775,1077],[0,2]),e6 [755] [8,232,252,453,2353,2354,2355],e6 [339,30] [8,261,557,640,1063,1065,1656,1659,2208,2356],([617,339,0,1,2,4,5],[557,640,1137,1245,1246,2010,2357],[]),([339,394,1,2,3,4,5,21],[8,80,151,261,365,400,528,657,809,888,905,959,2358,2359,2360],[0,2]),a6 [423] [8,40,185,863,865,1185,2361] [0,1],u6 [628] [8,255,370,1412,1485,1488,1489,1920,2362]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_21_8_1 : checkNodesBT W_21 g_21 F_21 P_21_8 A_21 B_21_7 8 N_21_8_1 = true := by decide +kernel
def N_21_8_2 : List NodeSpec := [([510,571,0,2,3,10,4,5],[8,252,1717,1829,1830,1926,2061,2062,2363,2364],[]),([185,302,186,0,1,2,4],[40,453,1027,1028,1041,1807,1808,1914,1915,2109,2365],[0]),([0,136,2,3,55,4,141],[8,40,1217,1737,1738,1739,1934,2366],[2]),u6 [624] [8,40,232,252,255,271,1137,1314,1362,1364,2367],e6 [756] [40,61,232,253,261,452,1217,2368,2369,2370],([222,0,1,2,602,4,5],[40,252,326,1314,1807,2371],[]),a6 [185,339,76] [8,261,557,640,810,818,1137,1154,2100,2154,2372,2373] [0,2],a6 [339,83,76] [8,557,640,810,812,818,1007,1057,1103,1250,2374] [0,1,3],([384,0,1,2,3,4,713],[8,252,453,1403,1851,2013,2375],[]),a6 [339,21,72] [8,640,763,825,845,1163,1625,2358,2376] [0,1,2],a6 [61,37] [8,40,61,253,261,290,339,453,883,894,1390,1393,2050,2052,2377,2378] [0,1],([704,0,1,2,3,4,21],[8,370,845,2379],[]),([302,394,1,2,3,4,5,21],[8,365,400,528,657,727,775,905,2380,2381],[0,2]),a6 [217,61,37] [8,40,261,290,1079,2382,2383] [0,1],a6 [171,339] [8,40,252,261,271,452,557,640,809,855,982,1137,1621,2219] [0,1],a6 [339,512] [8,261,557,640,933,1111,1113,2020,2022,2384] [0,1],a6 [339,21] [8,40,80,557,640,898,1089,1137,1308,1310,1344,1617,1806,2385] [0,1,2],e6 [757] [40,61,232,252,253,261,1872,2039,2386,2387],([185,186,339,0,1,2,4],[4,40,557,1027,1041,1137,1915,2109,2388],[1]),a6 [185,484,339] [40,261,557,640,871,933,1011,1137,1765,2100] [0,1],([302,410,479,0,2,3,5],[1215,1216,1434,1781,1999,2389],[0,2]),([0,9,2,10,29,4,5],[1197,1230,1232,1441,1945,2122,2208,2390],[0,2,3]),e6 [758] [40,61,80,208,252,1137,1147,1778,2391],([0,1,2,3,4,713,92],[8,253,1869,2013,2392,2393],[]),e6 [759] [8,232,252,271,453,557,1851,2394,2395],e6 [760] [40,252,253,452,1088,1314,1436,2396],a6 [339,467] [40,80,261,557,640,995,997,1067,1085,1089,1344,1512,1615,2397] [0,1,2],([0,1,2,3,748,7,5],[8,253,2037,2038,2317,2398,2399],[]),([606,0,1,2,741,4,5],[8,252,2400,2401],[]),([0,1,2,463,4,5,76],[8,255,598,1007,1089,2402],[1]),([185,0,1,2,685,4,5],[8,452,1779,2100,2403],[]),([185,0,1,2,741,4,5],[8,252,1718,2401,2404,2405],[]),([0,492,2,3,4,5,461],[8,825,845,1303,2406,2407],[0,3]),e6 [761] [8,233,253,271,452,2408,2409],([302,171,0,1,2,3,5,21],[8,40,61,845,855,856,2289],[0]),u6 [10,621] [8,253,1360,2039,2410,2411,2412],e6 [302,762] ([8,253,326,1803,1807,2036]++r 2413 6),e6 [763] [8,61,232,370,453,1717,2107,2419,2420],e6 [764,762] [8,253,271,453,2036,2413,2416,2417,2421,2422],a6 [580,212] [8,365,851,852,1190,1284,1347,1541,2423] [0,2],([302,0,1,91,3,4,92],[8,261,370,452,748,749,1404,1450,1804,1808,1967,2424],[0]),([8,0,1,3,5],[119],[0,1,2]),([216,0,1,2,3,4,21],[8,370,2425],[0,2]),([185,0,94,2,3,95,5],([8,61,271,1011,1024,1155]++r 2426 4),[0,2]),a6 [157,339,76] [8,810,812,818,1009,1022,1047,2346,2347,2430] [0,2],([0,9,1,6,3,7,5],([8,452,1229,2307,2344]++r 2431 4),[0,1]),([0,9,2,10,4,7,5],[8,1197,1230,1232,1353,1441,2037,2435],[0,3]),a6 [171,10] [8,40,261,856,917,1355,1621,1938,1940,2039,2436,2437] [2],([302,0,1,54,55,4,5],[8,453,1278,1279,1335,1336,1804,1807,2104,2438],[0]),([384,0,1,2,3,4,693],[8,252,1808,1851,2439,2440],[]),e6 [765] [8,232,252,253,452,2441,2442],([606,0,94,2,3,95,5],[8,271,1024,1774,1783,2426,2428,2443],[0,3]),([345,0,1,2,4,37,5,21],[8,185,909,1386,1493,1631,1674,2444],[0]),([0,9,2,10,4,5,92],[8,1232,1423,2393,2445],[0,3]),([384,0,9,2,10,4,5],[8,271,1073,1085,1197,1232,1441,1452,2446],[1,2]),([0,1,2,3,635,37,5],[40,261,453,1451,2312,2447],[]),u6 [519] [8,252,255,261,271,1046,1047,1819,2448],e6 [766] [8,232,252,253,452,1403,1851,2449],a6 [522] [8,233,253,1430,2033,2450] [0,3],([339,0,1,22,3,4,5,21],[8,261,365,763,796,847,1389,1409,1410,2451],[0,1]),e6 [767] ([8,232,252,253,326,370,452,2039]++r 2452 4),e6 [768] [8,61,185,232,252,271,370,452,1829,1926,2456,2457,2458],u6 [66,517] [8,40,453,633,876,911,1136,2265,2268,2459],e6 [769] [8,61,252,271,370,2307,2344,2460,2461,2462],([339,0,1,2,28,4,21],[8,21,40,80,276,314,344,371,557,1282],[0,1,2]),a6 [562] [8,40,61,253,365,1436,1841,2033,2036,2463] [0,2],([394,492,1,2,3,4,5],[8,233,261,365,400,401,528,657,673,775,888,1640,1979],[0]),e6 [770] [8,232,253,453,1835,2453,2464],([185,0,1,2,37,5,76],[8,370,810,2465],[0,2]),([410,0,1,2,3,4,713],[8,252,365,453,1701,2013,2466,2467],[1]),e6 [771] [8,40,61,252,255,1701,1999,2344,2468],a6 [772] [8,233,253,271,370,452,1147,2469] [1,2],([339,0,1,2,3,37,5,76],[8,261,557,640,810,1050,1052,1137,1980,1983,2470],[0,1,3]),([0,9,1,3,4,636,5],[452,1403,1456,1939,2307,2344,2471,2472,2473],[0]),([0,9,1,2,3,29,76],[8,341,342,368,369,1196,1370,1403,2474],[0]),([171,0,94,1,2,3,5],[8,271,855,856,2475],[]),([222,0,1,2,258,4,5],[40,252,261,827,1314,1436,2476,2477],[0,1,2]),e6 [773] [8,232,233,252,253,271,452,763,2478],e6 [774] [8,232,252,253,452,2307,2479,2480],([185,186,0,94,1,2,4],[1027,1041,1914,1915,2109,2184,2405,2481,2482],[0,1]),e6 [598,55] [8,40,261,326,1217,1934,1936,2076,2080,2096,2483,2484],e6 [302,55,37] [40,261,326,453,969,1217,1803,1804,1807,1933,1936],a6 [602,7] [8,261,326,1521,2038,2047,2073,2168,2485,2486] [2],a6 [492,72] [8,326,365,845,906,908,1076,1347,1625,1979,2487] [1,2],a6 [606,775] ([40,326,1767,1783]++r 2488 5) [3],e6 [302,776] ([8,40,252,255,261,1804,1808]++r 2493 4),([592,343,0,2,3,4,5],[8,1007,1057,2497,2498,2499],[0,2]),a6 [10,7,21] [8,763,825,845,847,1353,1480,2037,2038,2168,2500,2501] [0,3],u6 [384,10,7] [8,40,1073,1353,1355,1763,1851,1938,1940,2002,2038,2039,2168],u6 [339,517] [8,40,557,911,1133,1135,1137,2265,2268,2502],a6 [498] ([8,252,253,370,1038]++r 1352 6) [0,1,3],([302,479,0,2,3,55,5],[8,1215,1216,1217,1434,1471,1933,2503],[0,2]),e6 [777] [8,61,80,232,261,271,370,453,1803,2322,2504,2505],u6 [10,76] ([8,1355,1443,1938,2039]++r 2506 5),u6 [637] [61,232,253,261,370,452,1938,1940,1945,2511],e6 [10,778] ([8,40,253,2039]++r 2512 4),([302,0,2,3,55,4,5,141],[8,252,1490,1933,2516,2517],[0]),([0,1,2,3,647,7,5],[40,253,261,1555,2038,2168,2518],[]),a6 [487,21] [8,40,185,261,453,845,847,904,2099,2519,2520] [0,1],a6 [302,55,21] [8,261,453,825,845,1803,1804,1807,1808,1933,1936,2521,2522] [0,3],a6 [82] ([40,61,233,290,581,894]++r 1146 4) [0,1],a6 [339,21,76] [8,370,557,640,763,818,847,1047,1129,1137,2346,2347,2358,2359] [0,1,2,3],e6 [704,571] [8,253,261,1830,2523,2524],u6 [302,55,76] [8,326,818,1057,1217,1804,1933,1934,1936,2521,2522],e6 [302,779] ([8,253,261,1803]++r 2525 5),e6 [302,384,55] [8,40,326,1217,1763,1808,1851,1933,1934,1936],e6 [780] [8,232,253,452,453,1851,2530,2531,2532],e6 [10,781] [8,80,1355,2508,2533,2534,2535],([410,0,9,2,10,4,5],[271,1197,1230,1232,1452,1701,1781,2536],[0,1,2]),e6 [598,92] [8,40,326,370,1423,1869,1895,2080,2537,2538],([345,394,1,2,3,4,5],[8,233,261,400,401,528,657,673,888,1622,1626,2539],[0]),a6 [171,66,21] [8,40,487,633,845,876,917,1990] [0,1],a6 [618] [8,40,261,1355,1423,2540,2541] [0,2],([302,479,0,2,3,5,21],[8,825,845,1215,1471,1868,2542],[0,2]),e6 [654,55] [8,40,453,1217,2483,2543,2544],([510,0,1,2,40,37,5],[8,267,413,465,508,509,2545,2546,2547],[0]),e6 [510,641] [8,253,261,300,1897,1898,1899,1901],e6 [782] [8,40,80,261,2039,2548,2549],e6 [510,783] [8,40,185,252,2107,2550,2551],e6 [671,7] [8,253,261,452,2038,2047,2552,2553],([598,0,1,2,3,37,5],[40,61,970,2076,2554],[]),([222,784,0,1,2,4,5],[8,261,326,711,1911,2555,2556,2557],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_21_8_2 : checkNodesBT W_21 g_21 F_21 P_21_8 A_21 B_21_7 8 N_21_8_2 = true := by decide +kernel
def N_21_8 := N_21_8_0 ++ N_21_8_1 ++ N_21_8_2
def B_21_8 : BT (List (List Nat)) := buildBucketsBT W_21 N_21_8
set_option maxRecDepth 500000 in
lemma B_21_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_21 8 xs.toFinset) B_21_8 := by
  have hP := buildPoolsSubBT_sound (pdepth := 12) (W := W_21) (raw := r_21) (pspecs := ps_21) (used := U_21_8) S_21_ok
  have hm0 := checkNodesBT_mem (by decide) gp_21 W_21_ok hP A_21_ok B_21_7_ok C_21_8_0
  have hm1 := checkNodesBT_mem (by decide) gp_21 W_21_ok hP A_21_ok B_21_7_ok C_21_8_1
  have hm2 := checkNodesBT_mem (by decide) gp_21 W_21_ok hP A_21_ok B_21_7_ok C_21_8_2
  exact buildBucketsBT_of_mem (forall_append (forall_append (hm0) hm1) hm2)
def U_21_9 : List Nat := ([8,40,45,49,50,60,61,80,97,110,176,180,185,206,208,211,232,233,252,253,255,261,271,290,326,339,344,363,365,370,452,453,483,487,505,508,557,598,613,633,640,673,711,727,747,763,809,810,818,825,845,847,858,859,876,883,888,894,898,904,905,911,918,933,935,936,940,941,954,969,970,972,985,986,987,1001,1007,1011,1034,1036,1037,1047,1057,1067,1073,1076,1079,1085,1088,1089,1098,1123,1131,1137,1141,1147,1149,1155,1190,1213,1217,1220,1253,1273,1280,1281,1314,1316,1344,1347,1353,1355,1386,1403,1423,1436,1452,1460,1461,1481,1488,1512,1553,1618,1622,1631,1632,1634,1640,1648,1656,1663,1676,1700,1701,1703,1704,1717,1718,1723,1730,1731,1733,1734,1741,1752,1763,1765,1767,1769,1774,1775,1778,1779,1781,1783,1786,1794,1802,1803,1804,1807,1808,1821,1824,1827,1829,1830,1831,1835,1841,1850,1851,1852,1854,1855,1866,1869,1871,1872,1895,1907,1911,1912,1920,1923,1926,1933,1934,1936,1938,1940,1943,1945,1956,1958,1959,1971,1972,1975,1980,1989,1995,1999,2001,2002,2004,2011,2018,2020,2033]++r 2035 5++[2047,2050,2057,2058,2060,2062,2071,2076,2093,2100,2107,2109,2119,2135,2139,2140,2154,2161,2176,2208,2221,2235,2251,2262,2263,2265,2272,2273,2278,2286,2288,2295,2307,2312,2322,2327,2331,2341,2344,2348,2352,2359,2369,2372,2383,2393,2405,2436,2461,2480,2483,2486,2492,2500,2508,2516,2521,2538,2546,2547,2549]++r 2558 141)
def P_21_9 : BT (Option BoundPool) := buildPoolsSubBT 12 W_21 r_21 S_21 ps_21 U_21_9
def N_21_9 : List NodeSpec := [a6 [21] [8,61,233,252,253,271,370,452,453,898] [0,1,2,3],a6 [171,21] [8,61,370,453,763,825,845,847,904,1220] [0,1,2],a6 [171] [8,40,61,232,252,253,271,370,452,453,1220] [0,1,2,3],a6 [21,76] [8,61,370,453,763,818,825,845,847,905,941,1007,1047,1057,2288] [0,1,2],a6 [345,21] [8,185,253,261,370,453,763,825,845,847,904,918,1347,1622,1631,1632] [0,1,3],a6 [492,21] [8,261,365,370,453,763,825,845,847,904,918,1347,1618,1640,1663] [0,1,2],([394,1,2,3,4,5,21],[8,232,261,673,727,888,904,905],[0,1,2,3]),([0,1,2,28,4,21],[344,370],[0,1,2,3]),([617,0,1,2,4,5],[61,370,453,2558],[0,2]),a6 [467] [8,233,252,253,261,271,370,452,1067,1085,1512] [0,1,2],([560,0,2,3,4,5],[61,252,370,2559],[0,3]),([0,1,3,634,4,5],[370,452,453,1824],[0,1,3]),([222,0,1,2,4,5,21],[8,40,370,453,918,1098],[0,1,2]),a6 [517] [8,40,252,253,271,452,453,911,2265] [0,2],a6 [37] [8,40,61,252,253,271,370,452,453,2050] [0,1,2],a6 [217,37] [8,40,969,970,986,987,1079,1131,2383] [0,1,2],a6 [216,37] [8,40,61,370,453,969,970,986,987,1131,2560] [0,1,2],a6 [216] [8,40,61,232,252,253,261,271,370,452,453,2560] [0,1,2],a6 [72] [8,40,233,252,253,261,271,452,954,1280,1281] [0,1,2],e6 [510,92] [8,253,271,370,452,1869,1895,2561,2562],a6 [10,21] [8,252,261,370,453,763,845,847,1355,1940,2039,2508,2563] [0,2],a6 [606,29] [253,613,1767,1774,1775,1783,1945,1975,2208,2564,2565,2566] [0,1,3],a6 [302,55] [40,261,271,453,1217,1803,1804,1807,1933,1936,2483,2521] [0,2,3],a6 [10,92] [8,261,370,1355,1423,1869,1940,2039,2393,2567] [0,2],a6 [384,339] [40,61,206,252,261,271,452,557,640,1085,1137,1763,1851,2352] [0,1],a6 [704] [8,61,232,252,253,261,271,370,452,2568] [0,1],u6 [510,40] [8,271,505,747,1001,1717,1769,1854,2107,2331,2546,2569,2570,2571],a6 [339,21] [8,211,253,261,453,557,640,825,847,904,918,1137,1344,2359] [0,1,2],a6 [384,37] [8,61,453,1073,1141,1752,1763,1851,2002,2060,2251,2278,2312,2572] [0,1,2],a6 [302,186] [40,261,271,370,453,1803,1804,1807,1808,1907,1923,1971,2573,2574] [0,1,3],([510,0,2,3,10,4,5],[8,252,261,271,370,453,1717,2062],[0]),u6 [592,76] [8,271,365,818,940,941,1047,1057,1347,2575],a6 [9,91] [40,253,452,1403,1460,1461,1871,2262,2307,2576,2577,2578] [0,2],a6 [606,95] [8,40,61,1767,1774,1775,1783,1911,1956,1959,2579] [0,1,3],a6 [222,384] [40,61,370,935,936,1073,1085,1088,1123,1314,1316,1700,1763,1851,2002,2004] [0,2],a6 [384,9] [8,252,271,370,935,1085,1403,1763,1851,2002,2262,2341,2344,2580] [0,1],a6 [9,76] [8,61,271,370,810,818,940,941,1047,1057,2262,2344,2581,2582] [0,1,3],a6 [28,95] [40,61,252,1149,1778,1821,1866,1911,1912,1920,1958,1959,2583] [0,1,3],a6 [21,72] [8,61,763,825,845,847,905,1076] [0,1,2],a6 [10,7] [40,252,253,261,1353,1355,1940,2037,2038,2039,2500] [0,3],u6 [487] [40,185,232,271,370,452,453,2584],a6 [606,141] [8,252,253,1723,1783,2585,2586,2587] [0,3],a6 [598] [40,61,232,252,253,271,326,370,452,2076,2588] [0,1,2,3],a6 [510,54] ([8,253,271,452,1717,2033,2331]++r 2589 4) [0,2],a6 [136,37] [40,61,261,271,453,969,986,987,1079,1131,1841,1989,2593] [0,1,2],u6 [510,185] [8,252,271,370,453,972,1717,1718,2100,2107,2154,2331,2594,2595],a6 [21,461] [8,252,763,845,847,905,1089,1634] [0,1,2],a6 [9,7] [8,40,61,253,452,1403,2037,2038,2047,2262,2307,2344,2596,2597] [0,3],a6 [354] [8,61,252,253,453,2598,2599,2600] [0,1],a6 [602] [252,253,261,271,326,370,452,1807,2071,2486] [0,1,2],a6 [38,37] [8,61,253,453,969,970,986,987,1131,1347,2601] [0,2],a6 [512] [8,61,252,253,261,271,370,452,933,2020] [0,1,2],u6 [37,141] [8,252,970,987,1131,1835,2587,2602],([0,9,2,10,4,5],[271,453,1452],[0,1,2,3]),a6 [713] [8,61,252,253,452,453,1403,2011] [0,1,2,3],u6 [185,141] [8,252,370,1155,1723,1835,2100,2154,2585,2587,2603],a6 [510,55] [8,261,370,452,453,1217,1717,1933,1936,2107,2331,2483,2604,2605] [0,1,2],u6 [85,37] [8,61,365,453,969,970,985,986,987,1131,1347,2606],u6 [66,40] [8,252,253,453,487,633,747,876,1769,1854,2607],a6 [9,6] ([8,253,452,2262,2307,2582]++r 2608 5) [0,1,3],a6 [384,61] [40,61,253,261,290,339,370,452,883,894,935,1073,1085,1763,1851,2001,2002] [0,1],a6 [302,54] [8,40,253,271,452,453,1802,1803,1807,2033,2035,2036,2093,2589,2613] [0,2],a6 [136,55] [40,253,261,271,452,453,1553,1933,1934,1936,1989,2483,2614] [0,1,2],a6 [384,10] [40,61,252,261,1073,1355,1763,1938,1940,2002,2039,2436,2615] [0,1,2],([510,316,0,2,3,4],[252,271,1831],[0,1,2]),a6 [741] [8,61,252,253,261,370,452,2405,2616] [0,1],a6 [671] [8,61,252,253,261,271,370,452,1717,2617] [0,1,2],a6 [510,606] [8,271,452,1717,1775,2107,2566,2618,2619] [0,1],([185,0,1,2,4,37,5],[8,40,61,370,453,1011,2221],[0,1,2]),a6 [222,141] [8,61,252,271,1123,1316,1700,1723,1731,1835,2585,2587,2620,2621] [0,1],a6 [61,21] [8,261,271,290,339,370,452,453,763,825,845,847,894,904,905,918,1253,2263] [0,1,2],a6 [9,29] [271,613,1273,1403,1975,2208,2262,2307,2344,2564,2582,2622,2623] [0,1,2],u6 [222,136] [40,252,271,1088,1314,1316,1436,1700,1733,1841,1989,2624,2625,2626],a6 [83,76] [8,61,255,370,598,711,818,1007,1047,1057,2295] [0,1,2,3],a6 [410,40] [505,747,1701,1703,1769,1781,1854,1999,2569,2627] [0,2],a6 [360] [61,252,253,261,370,894,1481,2139,2140] [0,1],u6 [61,40] [8,253,290,339,505,747,894,1001,1769,1854,2569,2571,2628],a6 [10,55] [252,253,261,453,1217,1355,1936,1940,2629] [0,2],a6 [717] [8,61,232,233,271,452,453,2176] [0,1],u6 [302,7] [40,61,253,271,1804,1807,2037,2038,2047,2630],([0,61,66,3,4,5],[97,252,271,363],[0,1]),a6 [61,28] [40,253,271,290,339,452,894,1147,1149,1253,1778,1821,1866,2631,2632,2633] [0,1],([0,1,2,3,166,5],[370,453,1648],[0,1,2,3]),a6 [37,86] [8,40,252,261,970,987,1089,1131,1676] [0,1],a6 [384,95] [8,61,252,261,1073,1763,1911,1912,1920,1956,1959,2002,2634] [0,1,2,3],a6 [100,37] [8,40,61,453,969,970,985,987,1079,1131,2057,2058] [0,1,2],a6 [185,95] [8,40,61,370,1011,1155,1718,1911,1920,1956,1959,2100,2154,2635] [0,1],a6 [66,28] [40,252,253,453,487,633,859,876,1778,1821,1866,2636] [0,1],a6 [302,37] [8,40,61,261,271,453,969,986,987,1131,1803,1804,2637] [0,1],a6 [606,94] [8,252,271,452,1774,1775,2405,2566,2638,2639,2640] [0,1,3],a6 [185,66] [8,370,453,487,633,858,876,1011,1155,1995,2100] [0,1],a6 [754] [8,61,252,452,453,2641] [0,1],a6 [384,66] [40,61,261,370,487,633,858,876,1073,1085,1763,2286] [0,1],u6 [339,40] [8,45,271,505,557,640,747,1137,1854,2569,2642],a6 [185,61] [8,253,290,339,370,452,453,883,894,972,1011,1155,1718,2100,2154,2327] [0,1],a6 [37,72] [8,40,370,969,970,985,987,1131,1280] [0,1,2],a6 [185,339] [8,110,252,271,370,452,557,640,1011,1137,1718,2100,2372] [0,1],([0,136,2,3,4,141],[271,370,1734],[0,1,2,3]),a6 [66,37] [8,40,61,261,453,487,633,876,970,987,2161] [0,1],a6 [606,136] [40,252,271,452,1436,1553,1767,1774,1775,1989,2624,2643] [0,3],a6 [339,37] [8,40,50,61,261,453,557,640,969,986,987,1137,2235] [0,1,2],a6 [9,92] [8,253,271,370,452,1869,1895,2344,2393,2562,2644] [0,3],a6 [302,91] [40,253,261,271,370,452,1460,1461,1803,1807,1808,1871,1872,2576,2645] [0,2],a6 [339,28] [40,208,253,271,557,640,1137,1147,1344,1778,1821,2631,2646] [0,1],a6 [10,76] [8,40,261,810,818,1007,1047,1057,1355,1940,2039,2508,2647] [0,1,2,3],a6 [410,9] [40,252,271,452,1403,1701,1703,1999,2307,2341,2344,2648,2649] [0,2],([302,0,2,3,4,5,141],[8,40,61,252,271,370,2516],[0,2,3]),e6 [510,668] ([8,252,253,271,370,452,2322,2549,2592]++r 2650 4),a6 [222,76] [8,61,370,810,818,940,941,1007,1037,1047,1057,1123,1314,1316,1700,2272] [0,2],a6 [302,571] [40,61,252,253,271,452,1803,1807,1829,1830,1926,2654] [0,2],a6 [185,76] [8,61,370,810,818,940,972,1007,1047,1057,1155,1718,2100,2154,2655] [0,2],a6 [10,37] [8,40,61,252,261,453,970,987,1131,1355,2039,2656] [0,2],a6 [302,92] [8,40,370,1423,1803,1804,1807,1869,1895,2393,2538,2657] [0,3],a6 [157,76] [8,255,598,711,810,818,940,941,1007,1034,1047,1057] [0,2],a6 [510,571] [8,40,61,252,370,1717,1829,1830,1926,2107,2331,2658,2659,2660] [0,2],u6 [302,222] [8,40,61,252,271,453,1036,1088,1314,1316,1700,1802,1803,1804,1807,2661],u6 [302,28] [40,61,271,1147,1149,1778,1802,1803,1804,1807,1808,1821,1866,2631,2662],a6 [510,21] [8,271,370,453,763,825,847,904,905,2107,2331,2592,2663] [1],a6 [302,410] [40,261,271,452,1701,1781,1804,1807,1808,1999,2664] [0,2],([0,1,2,40,37,5],[61,483,508],[0,2]),a6 [185,94] [8,61,252,271,972,1011,1718,2100,2154,2405,2638,2640,2665,2666] [0,1],u6 [185,302] [8,40,61,370,453,1155,1718,1803,1804,1807,2100,2154,2667],u6 [222,61] [8,40,61,176,253,271,290,339,452,883,894,1037,1123,1253,1314,1316,1700,2273],a6 [302,76] [8,40,61,271,370,810,818,940,1047,1057,1802,1803,1804,1807,2668] [0,3],([302,479,0,2,3,5],[252,271,1213],[0,2,3]),a6 [37,21] [8,61,261,370,453,969,970,985,987,1131,1386] [0,2],u6 [302,384] [8,40,61,252,261,271,370,936,1085,1763,1803,1804,1807,1808,1851,2002,2669],a6 [30] [8,61,252,253,261,271,370,452,1656,2208] [0,1,2,3],a6 [685] [8,61,252,261,271,370,452,1779,2670] [0,1],a6 [410,10] [40,252,253,261,1355,1703,1781,1940,2436,2671] [0,1,2],a6 [410,37] [40,61,253,261,453,969,970,986,987,1781,1999,2672] [0,1,2],a6 [693] [8,40,252,253,271,370,452,453,2673] [0,1,2,3],a6 [683] [8,61,80,233,252,271,452,453,1767,1794] [0,1],a6 [606,479] [8,252,253,271,1774,1783,1786,2674,2675] [0,1,3],a6 [606,316] [40,271,1767,1774,1783,2369,2492,2676,2677] [0,2,3],a6 [185,484] [61,370,933,1011,1155,1718,1765,1943,2100,2154,2480,2678,2679] [0,1,2],a6 [606,76] [8,61,253,810,818,940,1007,1057,1775,1783,2566,2680] [0,1,3],([0,1,2,3,37,5,76],[8,61,261,370,453,810,1980],[0,1,2,3]),a6 [384,606] [8,452,1073,1085,1763,1767,1775,1783,1851,2681] [0,1,3],a6 [185,661] [8,452,1011,1155,1718,1779,2100,2135,2461,2682] [0,1,2],a6 [258] [61,252,253,261,370,452,1436,1741] [0,1,2,3],u6 [136,40] [505,747,1001,1436,1553,1841,1854,1989,2569,2683],u6 [222,339] [8,40,49,60,61,252,253,271,452,557,640,809,1137,1314,1344,1700,2348],e6 [141,92] [8,252,253,370,452,1423,2684],a6 [40,141] [8,252,370,747,1001,1723,1730,1769,1835,1854,2587,2685] [0,1],a6 [66,21] [8,261,453,487,633,845,847,859,876,918,2018] [0,1],a6 [141,21] [8,252,370,453,763,845,847,1835,2587,2621,2686] [1],u6 [510,222] [8,271,453,1036,1037,1314,1316,1700,1717,2107,2331,2547,2592,2652,2687],a6 [61,37] [8,40,61,261,290,339,453,894,969,970,985,986,987,1131,1972] [0,1],a6 [302,21] [8,40,61,261,453,763,825,845,847,904,918,1802,1803,1804,1807,2688] [0,3],a6 [654] [8,40,232,252,253,271,370,452,453,2689] [0,1,3],a6 [302,299] [40,61,252,261,453,1488,1803,1804,1807,1850,1852,1855] [0,1,3],u6 [302,606] [8,40,61,452,1767,1775,1783,1804,1807,2690],a6 [593] [61,252,255,261,370,452,1137,2691] [0,1],a6 [510,37] [8,271,969,985,986,987,1131,2107,2331,2692] [0,2],a6 [616] [61,252,255,261,271,370,452,1701,1827] [0,1,3],a6 [222,410] [40,452,1123,1314,1700,1701,1704,1781,1999,2649,2693] [0,2],([185,186,0,1,2,4],[370,453,2109],[0,1,2]),a6 [212] [8,61,233,252,253,271,452,453,747,1190] [0,2],u6 [222,95] ([40,61,252,271,1911,1920,1956,1958,1959]++r 2694 4),a6 [222,66] [8,40,61,180,271,452,487,633,858,859,876,1123,1700,2119] [0,1],a6 [287,37] [40,261,271,365,969,986,987,1131,1347,2698] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_21_9 : checkNodesBT W_21 g_21 F_21 P_21_9 A_21 B_21_8 9 N_21_9 = true := by decide +kernel
def B_21_9 : BT (List (List Nat)) := buildBucketsBT W_21 N_21_9
set_option maxRecDepth 500000 in
lemma B_21_9_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_21 9 xs.toFinset) B_21_9 :=
  buildBucketsBT_sound (by decide) gp_21 W_21_ok (buildPoolsSubBT_sound S_21_ok) A_21_ok B_21_8_ok C_21_9
def U_21_10 : List Nat := [61,97,232,233,252,253,271,370,452,453,483,809,858,883,904,936,986,1036,2341,2381,2436,2569,2585,2594,2618,2624,2631,2652,2693]
def P_21_10 : BT (Option BoundPool) := buildPoolsSubBT 12 W_21 r_21 S_21 ps_21 U_21_10
def N_21_10 : List NodeSpec := [a6 [384] [61,232,252,253,271,370,452,453,936] [0,1,2,3],a6 [185] [61,232,252,253,271,370,452,453,2594] [0,1,2],a6 [21] [61,233,252,253,271,370,452,453,904] [0,1,2,3],a6 [28] [61,233,252,253,271,370,452,453,2631] [0,1,2,3],a6 [222] [61,232,233,252,253,271,370,452,453,483,1036] [0,2],a6 [61] [61,232,233,252,253,271,370,452,453,883] [0,1],a6 [339] [61,97,232,252,370,452,453,809] [0,1],a6 [10] [61,252,253,271,370,452,453,2436] [0,1,2,3],a6 [9] [61,232,233,252,253,370,452,453,2341] [0,1,2],a6 [510] [61,232,233,252,253,271,370,452,453,2652] [0,1],a6 [302] [61,232,252,253,271,370,452,453,2381] [0,2],a6 [410] [61,232,252,271,370,452,453,2693] [0,1,2,3],a6 [66] [61,271,370,452,453,858] [0,1],a6 [40] [61,252,253,271,370,452,453,2569] [0,2],a6 [606] [61,232,252,271,370,452,453,2618] [0,1,3],a6 [136] [61,232,252,253,370,452,453,2624] [0,1,2,3],a6 [37] [61,252,253,271,370,452,453,986] [0,1,2,3],a6 [141] [61,252,253,271,370,452,453,2585] [0,1,2,3]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_21_10 : checkNodesBT W_21 g_21 F_21 P_21_10 A_21 B_21_9 10 N_21_10 = true := by decide +kernel
def B_21_10 : BT (List (List Nat)) := buildBucketsBT W_21 N_21_10
set_option maxRecDepth 500000 in
lemma B_21_10_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_21 10 xs.toFinset) B_21_10 :=
  buildBucketsBT_sound (by decide) gp_21 W_21_ok (buildPoolsSubBT_sound S_21_ok) A_21_ok B_21_9_ok C_21_10
def U_21_11 : List Nat := [232]
def P_21_11 : BT (Option BoundPool) := buildPoolsSubBT 12 W_21 r_21 S_21 ps_21 U_21_11
def N_21_11 : List NodeSpec := [a6 [] [232] [0,1,2,3]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_21_11 : checkNodesBT W_21 g_21 F_21 P_21_11 A_21 B_21_10 11 N_21_11 = true := by decide +kernel
def B_21_11 : BT (List (List Nat)) := buildBucketsBT W_21 N_21_11
set_option maxRecDepth 500000 in
lemma B_21_11_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_21 11 xs.toFinset) B_21_11 :=
  buildBucketsBT_sound (by decide) gp_21 W_21_ok (buildPoolsSubBT_sound S_21_ok) A_21_ok B_21_10_ok C_21_11
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_21_ok : forestRootCheck r_21 g_21 [(VAR 0,24,25),(VAR 1,12,14),(VAR 2,10,14),(VAR 3,6,14),(VAR 4,6,22),(VAR 5,3,35)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_21_in : bucketContainsBT B_21_11 r_21 = true := by decide +kernel
lemma low_21 : Lower r_21 g_21 12 := lower_of_forestBT root_21_ok B_21_11_ok root_21_in

def g_orig := (d 0xfeeaeae8fee8e8a8)
set_option maxHeartbeats 0 in
lemma low_orig : Lower (varsOf 63) g_orig 12 := carry_of (swaps := [(0,5),(1,3),(2,4)]) (by decide +kernel) low_21
def targetFn (x : Fin 6 → Bool) : Bool := Nat.testBit (4276808424 * 2 ^ 32 + 4276676776) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def temoin : List Gate := [⟨.or,[3,4]⟩,⟨.and,[6,5]⟩,⟨.or,[5,6]⟩,⟨.and,[2,1]⟩,⟨.and,[3,4]⟩,⟨.or,[10,7]⟩,⟨.or,[2,1]⟩,⟨.or,[11,12]⟩,⟨.and,[13,0]⟩,⟨.and,[12,10]⟩,⟨.and,[8,9]⟩,⟨.or,[14,15]⟩,⟨.or,[16,17]⟩]
lemma temoin_ok : PEqualNP.MetaComplexity.Monotone2 ⟨temoin, 18⟩ := by
  intro g hg; simp [temoin] at hg; rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxHeartbeats 0 in
lemma tgt_eq_G : ∀ r : Row, targetFn (evalInput6 r) = g_orig.testBit r.val := by decide +kernel
set_option maxHeartbeats 0 in
lemma temoin_eval : ∀ r : Row, Circuit.eval ⟨temoin, 18⟩ (List.ofFn (evalInput6 r)) = g_orig.testBit r.val := by decide +kernel

end PEqualNP.Outside.L_meta_42210

open PEqualNP.Outside.L_meta_42210 in
theorem PEqualNP.Outside.L_meta_42210 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808424 * 2 ^ 32 + 4276676776) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808424 * 2 ^ 32 + 4276676776) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  exact replace_of_lower6 g_orig (by decide) (by decide) (by decide) 12 low_orig temoin 18 (by decide) temoin_ok targetFn tgt_eq_G temoin_eval
