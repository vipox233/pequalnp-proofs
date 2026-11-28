import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_44938
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
def g_9 := (d 0xfac0fac0fac0fac0)
def r_9 : List Nat := varsOf 15
def p_9 : List Nat := [6,6,7,7,9,9,11,11,12,12,13,14]
def q_9 : List Nat := [4,2,5,3,8,1,10,3,8,4,5,10]
def F_9 : Nat := fullMask 12
set_option maxHeartbeats 0 in
lemma gp_9 : goodPairs g_9 p_9 q_9 := goodPairs_of (by decide +kernel)
def W_9 : BT Decor := buildWiresBT 2 (mkBase p_9 q_9 r_9) []
lemma W_9_ok : btAll (fun x => faithful p_9 q_9 x ∧ x.1 < 2^256) W_9 := buildWiresBT_faithful (mkBase_ok (by decide))
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
def g_10 := (d 0xffecf880ffecf880)
def r_10 : List Nat := varsOf 31
def p_10 : List Nat := [7,7,7,11,11,11,12,12,13,13,14,14,18,18,19,19,21,21,21,22,22,24,24,25,25,26,28]
def q_10 : List Nat := [6,5,3,10,9,3,8,4,9,5,10,6,16,2,17,3,20,17,5,20,6,16,8,17,9,10,20]
def F_10 : Nat := fullMask 27
set_option maxHeartbeats 0 in
lemma gp_10 : goodPairs g_10 p_10 q_10 := goodPairs_of (by decide +kernel)
def W_10 : BT Decor := buildWiresBT 7 (mkBase p_10 q_10 r_10) [(0,1,4),(0,2,3),(1,5,6),(1,2,3),(1,1,4),(0,8,9),(3,6,8),(3,5,9),(0,0,9),(1,13,6),(2,1,4),(3,1,4),(2,11,5),(1,5,3),(0,2,18),(1,2,18),(3,19,20),(2,0,6),(2,2,3),(3,2,3),(0,0,8),(3,13,8),(1,25,4),(0,1,27),(1,16,6),(1,25,5),(3,6,9),(2,0,19),(1,6,4),(0,0,20),(1,13,3),(3,2,35),(3,4,20),(0,1,33),(1,1,33),(2,1,33),(3,1,33),(0,3,4),(1,3,4),(3,42,43),(3,16,8),(3,13,3),(1,25,1),(1,24,16),(3,25,1),(1,24,5),(2,2,4),(2,1,3),(1,52,4),(0,1,2),(3,54,43),(1,54,3),(2,56,4),(1,51,52),(1,56,4),(1,54,4),(3,2,18),(2,3,4),(3,3,4),(2,1,43),(2,0,42),(1,16,3),(3,6,1),(1,2,42),(2,1,42),(1,51,3),(0,1,3),(1,1,3),(0,2,4),(1,73,3),(1,1,2),(0,0,75),(1,5,2),(3,1,3),(3,78,0),(3,6,4),(0,1,43),(2,2,1),(1,82,3),(3,2,4),(2,1,2)]
lemma W_10_ok : btAll (fun x => faithful p_10 q_10 x ∧ x.1 < 2^256) W_10 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_10 : List (List (Nat × Nat)) := [[],[(1,2),(3,4)]]
def A_10 : BT (List (Nat × Nat)) := btOfList 1 al_10
set_option maxHeartbeats 0 in
lemma A_10_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_10 = g_10) A_10 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_10_0 : Slice r_10 g_10 (subcubeFast 0 1) 7 := by
  have hc : Lower (varsOf 30) (d 0xfffcfcc0fffcfcc0) 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_1 : Slice r_10 g_10 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) (d 0xffa0f000ffa0f000) 5 := carry_of (swaps := [(1,4),(2,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_2 : Slice r_10 g_10 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) (d 0xfffffaa0fffffaa0) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_3 : Slice r_10 g_10 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) (d 0xffcc8800ffcc8800) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_4 : Slice r_10 g_10 (subcubeFast 0 4) 5 := by
  have hc : Lower (varsOf 27) (d 0xffeeff88ffeeff88) 5 := carry_of (swaps := [(2,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_5 : Slice r_10 g_10 (subcubeFast 8 0) 5 := by
  have hc : Lower (varsOf 23) (d 0xecec8080ecec8080) 5 := carry_of (swaps := [(1,2),(3,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_6 : Slice r_10 g_10 (subcubeFast 16 0) 5 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_4
set_option maxHeartbeats 0 in
lemma sl_10_7 : Slice r_10 g_10 (subcubeFast 4 1) 4 := by
  have hc : Lower (varsOf 26) (d 0xffcccc00ffcccc00) 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_8 : Slice r_10 g_10 (subcubeFast 8 4) 4 := by
  have hc : Lower (varsOf 19) (d 0xeeee8888eeee8888) 4 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 8) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_9 : Slice r_10 g_10 (subcubeFast 16 2) 4 := by
  have hc : Lower (varsOf 13) (d 0xfaa0faa0faa0faa0) 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_10 : Slice r_10 g_10 (identDom 1 3) 6 := by
  have hc : Lower (varsOf 23) (d 0xececc8c8ececc8c8) 6 := carry_of (swaps := [(1,3),(2,3),(3,4)]) (by decide +kernel) low_6
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_11 : Slice r_10 g_10 (identDom 2 4) 6 := by
  have hc : Lower (varsOf 15) (d 0xf8e0f8e0f8e0f8e0) 6 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_6
  exact slice_ident (u := 2) (v := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_12 : Slice r_10 g_10 (identDom 0 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xeeeea8a8eeeea8a8) 5 := carry_of (swaps := [(0,3),(2,3),(3,4)]) (by decide +kernel) low_8
  exact slice_ident (u := 0) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_13 : Slice r_10 g_10 (identDom 1 2) 5 := by
  have hc : Lower (varsOf 27) (d 0xffcccc88ffcccc88) 5 := carry_of (swaps := [(1,3),(2,4)]) (by decide +kernel) low_8
  exact slice_ident (u := 1) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_14 : Slice r_10 g_10 (subcubeFast 1 0) 4 := by
  have hc : Lower (varsOf 30) (d 0xffccf000ffccf000) 4 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
def S_10 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 0 1,7),some (subcubeFast 2 0,5),some (subcubeFast 0 2,5),some (subcubeFast 4 0,5),some (subcubeFast 0 4,5),some (subcubeFast 8 0,5),some (subcubeFast 16 0,5),some (subcubeFast 4 1,4),some (subcubeFast 8 4,4),some (subcubeFast 16 2,4),some (identDom 1 3,6),some (identDom 2 4,6),some (identDom 0 3,5),some (identDom 1 2,5),some (subcubeFast 1 0,4)]
lemma S_10_ok : btAll (fun o => ∀ p, o = some p → Slice r_10 g_10 p.1 p.2) S_10 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_10_0) (forall_cons (fun _ h => by cases h; exact sl_10_1) (forall_cons (fun _ h => by cases h; exact sl_10_2) (forall_cons (fun _ h => by cases h; exact sl_10_3) (forall_cons (fun _ h => by cases h; exact sl_10_4) (forall_cons (fun _ h => by cases h; exact sl_10_5) (forall_cons (fun _ h => by cases h; exact sl_10_6) (forall_cons (fun _ h => by cases h; exact sl_10_7) (forall_cons (fun _ h => by cases h; exact sl_10_8) (forall_cons (fun _ h => by cases h; exact sl_10_9) (forall_cons (fun _ h => by cases h; exact sl_10_10) (forall_cons (fun _ h => by cases h; exact sl_10_11) (forall_cons (fun _ h => by cases h; exact sl_10_12) (forall_cons (fun _ h => by cases h; exact sl_10_13) (forall_cons (fun _ h => by cases h; exact sl_10_14) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))
def ps_10 : BT (Option PoolSpec) := btOfList 7 [q 9 [],q 8 [],q 0 [12296,12297,32795],q 0 [16396,16397,176299],q 2 [],q 0 [16390,16391],q 0 [16389],q 14 [],q 0 [12296,16409],q 4 [16409],q 3 [],q 5 [],q 1 [],q 0 [12296,12297],q 4 [],q 3 [32768],q 5 [32768],q 1 [36864],q 12 [],q 0 [],q 7 [],q 4 [24578],q 0 [16388,16389],q 6 [],q 0 [16398,16399],q 0 [16398,16633],q 0 [16396,16397],q 0 [16391,12353],q 0 [16394,12297],q 2 [16394],q 0 [12297],q 0 [12296,4123],q 0 [12297,16418],q 0 [12304,172041],q 4 [16397],q 0 [16396,172038],q 0 [16394,12493],q 0 [12292,12293],q 10 [],q 0 [16392,12581],q 0 [8196,8197],q 13 [],q 0 [8197],q 1 [307200],q 0 [8196,12505],q 0 [16388,8213],q 0 [16388,12309],q 0 [12295],q 0 [12296,16411],q 2 [16397],q 0 [12296],q 0 [16388],q 0 [4106,12617],q 0 [12299],q 0 [16390],q 0 [16398],q 0 [12292],q 0 [8196],q 0 [12293],q 0 [16395],q 11 [],q 0 [8198],q 0 [16396],q 0 [16394],q 0 [16397]]
def B_10_1 : BT (List (List Nat)) := BT.empty
lemma B_10_1_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_10 1 xs.toFinset) B_10_1 := .empty
def U_10_2 : List Nat := []
def P_10_2 : BT (Option BoundPool) := buildPoolsSubBT 7 W_10 r_10 S_10 ps_10 U_10_2
def N_10_2 : List NodeSpec := [([0,7,10],[],[]),([11,12,0],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_10_2 : checkNodesBT W_10 g_10 F_10 P_10_2 A_10 B_10_1 2 N_10_2 = true := by decide +kernel
def B_10_2 : BT (List (List Nat)) := buildBucketsBT W_10 N_10_2
set_option maxRecDepth 500000 in
lemma B_10_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_10 2 xs.toFinset) B_10_2 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok (buildPoolsSubBT_sound S_10_ok) A_10_ok B_10_1_ok C_10_2
def U_10_3 : List Nat := []
def P_10_3 : BT (Option BoundPool) := buildPoolsSubBT 7 W_10 r_10 S_10 ps_10 U_10_3
def N_10_3 : List NodeSpec := [([1,14,8,4],[],[]),([0,5,6,10],[],[0]),([15,11,16,0],[],[0]),([11,0,5,9],[],[0]),([17,0,1,4],[],[]),([0,7,8,9],[],[0]),([11,13,1,4],[],[]),([21,0,1,4],[],[]),([22,12,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_10_3 : checkNodesBT W_10 g_10 F_10 P_10_3 A_10 B_10_2 3 N_10_3 = true := by decide +kernel
def B_10_3 : BT (List (List Nat)) := buildBucketsBT W_10 N_10_3
set_option maxRecDepth 500000 in
lemma B_10_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_10 3 xs.toFinset) B_10_3 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok (buildPoolsSubBT_sound S_10_ok) A_10_ok B_10_2_ok C_10_3
def U_10_4 : List Nat := [0,1,2]
def P_10_4 : BT (Option BoundPool) := buildPoolsSubBT 7 W_10 r_10 S_10 ps_10 U_10_4
def N_10_4 : List NodeSpec := [([15,23,24,16,0],[],[0,1]),([15,16,25,2,3],[],[1]),([26,1,2,3,4],[],[]),([25,28,2,3,4],[],[]),([15,0,2,29,3],[0],[]),([15,16,0,6,8],[],[0,1]),([0,5,2,3,10],[],[0]),([1,30,2,3,4],[],[1]),([0,1,7,8,4],[],[0]),([22,1,2,18,4],[],[]),([22,5,2,3,9],[],[0]),([31,0,5,2,3],[],[1]),([15,22,16,2,3],[],[0]),([25,5,2,3,9],[],[1]),([0,5,6,8,9],[],[0,1]),([32,1,2,18,4],[],[]),([0,1,2,18,33],[],[]),([34,1,2,18,4],[],[]),([36,13,1,3,4],[],[]),([25,1,2,18,4],[],[]),([37,0,1,2,18],[],[]),([24,12,0,2,3],[],[1]),([11,0,5,1,4],[1,2],[0,1]),([0,38,2,3,39],[],[1]),([40,41,0,2,3],[],[1]),([11,0,1,4,9],[2],[0]),([15,11,0,1,4],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_10_4 : checkNodesBT W_10 g_10 F_10 P_10_4 A_10 B_10_3 4 N_10_4 = true := by decide +kernel
def B_10_4 : BT (List (List Nat)) := buildBucketsBT W_10 N_10_4
set_option maxRecDepth 500000 in
lemma B_10_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_10 4 xs.toFinset) B_10_4 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok (buildPoolsSubBT_sound S_10_ok) A_10_ok B_10_3_ok C_10_4
def U_10_5 : List Nat := (r 0 23)
def P_10_5 : BT (Option BoundPool) := buildPoolsSubBT 7 W_10 r_10 S_10 ps_10 U_10_5
def N_10_5 : List NodeSpec := [([44,0,1,2],[0,1,3],[]),e5 [45] [],([15,37,0,1,2,3],[4],[]),([15,16,0,2,3,8],[5],[0,1]),([15,25,1,2,3,4],[],[0]),([46,13,1,2,3,4],[4,6,7],[]),([25,1,47,2,3,4],[7],[]),([22,16,1,2,3,4],[],[0]),e5 [48] [],([49,25,1,2,3,4],[7],[]),([0,38,1,2,3,33],(r 8 4),[0,1]),a5 [50] [12] [1],([40,0,1,2,3,33],[],[0]),([0,5,1,6,8,4],[10,13,14],[0,1]),([15,24,16,0,2,3],[],[0]),([51,25,1,3,4],[14,15,16],[]),([24,13,1,2,3,4],[4,17],[1]),([0,1,2,3,33,39],[8,9,10],[0,1]),([15,0,1,6,8,4],[],[0]),([25,1,2,3,4,27],[7],[0,1]),([15,22,1,2,3,4],[],[0]),([15,23,24,0,1,4],[],[0]),([0,1,2,3,53,43],[11,12],[]),e5 [55] [],e5 [57] [],e5 [58] [],([44,0,1,2,43],[0,1,3],[]),e5 [59] [4,12,18,19],([25,1,2,3,4,9],[7],[0,1]),([22,1,2,3,4,9],[7,20],[0]),([0,1,2,3,60,43],[10,11,12],[]),a5 [10] [7,19] [0,1],([22,5,1,2,3,4],[7,11,20,21],[0]),([25,5,1,2,3,4],[7,14,15,16],[0]),([61,0,1,2,18,4],[],[1]),([24,0,1,2,18,4],[10],[]),([0,5,1,2,3,33],([4]++r 8 4),[0,1]),([0,1,2,3,9,33],(r 8 5),[1]),([11,0,1,4],[1,2],[0,1]),([15,0,1,2,3,33],[4],[]),([0,5,2,3,8,9],[4,22],[0,1]),([24,0,5,2,3,9],[],[0,1]),a5 [7] [4,7,10,12,19] [0,1],([37,0,5,1,2,3],[4,14],[0]),u5 [31] [7,10,12,19],([15,16,0,6,2,3],[0,5,12],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_10_5 : checkNodesBT W_10 g_10 F_10 P_10_5 A_10 B_10_4 5 N_10_5 = true := by decide +kernel
def B_10_5 : BT (List (List Nat)) := buildBucketsBT W_10 N_10_5
set_option maxRecDepth 500000 in
lemma B_10_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_10 5 xs.toFinset) B_10_5 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok (buildPoolsSubBT_sound S_10_ok) A_10_ok B_10_4_ok C_10_5
def U_10_6 : List Nat := ([0,1]++r 4 5++[10,11,12,14,15,16,20]++r 22 33)
def P_10_6 : BT (Option BoundPool) := buildPoolsSubBT 7 W_10 r_10 S_10 ps_10 U_10_6
def N_10_6 : List NodeSpec := [([62,63,0,1,2],[1,11,23,24],[0]),e5 [43] [0,1,25],u5 [64,43] [0,12],([0,1,2,42,43],[0,1,11,26],[0]),([65,1,2,3,4],[0,1],[]),e5 [66] [4,10,14,23,27],u5 [15,24] [0,12],([51,0,1,3,8,4],[10,11,14,23,28,29],[0]),([25,1,2,3,4],[1,7,14,15,16,30],[0,1]),u5 [51,52] [1,4,10,12,14],([67,0,2,3,4],[10,11,12,31],[]),([0,1,2,3,33],[8,10,11],[0,1]),u5 [37] [1,4,10,11,12,14,32],([0,1,3,68,4],[11,14,23,33],[]),a5 [15,23] [1,10,12] [0,1],a5 [51,43] [10,11,14,23,34] [1],([69,0,2,3,4],[11,12,23,35],[]),a5 [70] [1,4,10,12,36] [1],([0,71,2,72,4],[0,12,37,38],[]),a5 [54,43] [1,4,10,11,12,23] [0,1],e5 [74] [0,1,10,39],([22,1,2,3,4],[11,20],[0]),([0,54,75,3,4],[1,4,12,40,41],[]),a5 [24,16] [4,14] [0,1],([76,1,2,3,4],[0,1,4,42,43],[]),a5 [56] [1,10,12,23,44] [0,1],([0,1,77,3,4],[12,14,23,45],[]),a5 [18] [10,12,14,23,46] [0,1],([79,1,2,3,4],[0,1,4,47],[]),a5 [8,9] [4,6,14,30] [0,1],([80,0,1,2,3],[10,11,23,48],[]),e5 [81,43] [0,12,23,49],a5 [5,6] [4,10,11,12,14,23,50,51] [0,1],e5 [83] [0,1,4,10,23,52],([0,5,2,3,9],[4,12,22],[0,1]),a5 [5,8] [4,10,11,12,14,23,30,51] [0,1],a5 [24,9] [4,10,12,14,53] [0,1],a5 [24,5] [10,11,12,14,53] [0,1],u5 [15,6] [0,12,54],u5 [15,8] [0,12,14,54],([15,16,0,2,3],[4,5,12],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_10_6 : checkNodesBT W_10 g_10 F_10 P_10_6 A_10 B_10_5 6 N_10_6 = true := by decide +kernel
def B_10_6 : BT (List (List Nat)) := buildBucketsBT W_10 N_10_6
set_option maxRecDepth 500000 in
lemma B_10_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_10 6 xs.toFinset) B_10_6 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok (buildPoolsSubBT_sound S_10_ok) A_10_ok B_10_5_ok C_10_6
def U_10_7 : List Nat := ([0,1,4,10,11,12,14,23,30,41,42,51]++r 53 12)
def P_10_7 : BT (Option BoundPool) := buildPoolsSubBT 7 W_10 r_10 S_10 ps_10 U_10_7
def N_10_7 : List NodeSpec := [u5 [62] [0,1,4,10,11,12,14,55],a5 [71] [1,4,10,11,12,14,23,56] [0,1],a5 [54] [0,1,4,10,11,12,23,57] [0,1],u5 [75] [0,1,4,10,42],u5 [72] [0,1,4,10,12,58],a5 [84] [1,4,10,12,14,23,59,60] [1],a5 [85] [1,4,12,23,41,61] [1],a5 [24] [4,10,11,12,14,23,53] [0,1],a5 [5] [4,10,11,12,14,23,51] [0,1],a5 [8] [1,4,11,12,14,23,30] [0,1],u5 [15] [0,10,12,14,54],a5 [42] [1,4,11,12,23,62] [0,1],u5 [51] [0,1,4,10,11,12,14,60,63],a5 [43] [0,1,10,12,64] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_10_7 : checkNodesBT W_10 g_10 F_10 P_10_7 A_10 B_10_6 7 N_10_7 = true := by decide +kernel
def B_10_7 : BT (List (List Nat)) := buildBucketsBT W_10 N_10_7
set_option maxRecDepth 500000 in
lemma B_10_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_10 7 xs.toFinset) B_10_7 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok (buildPoolsSubBT_sound S_10_ok) A_10_ok B_10_6_ok C_10_7
def U_10_8 : List Nat := [19]
def P_10_8 : BT (Option BoundPool) := buildPoolsSubBT 7 W_10 r_10 S_10 ps_10 U_10_8
def N_10_8 : List NodeSpec := [a5 [] [19] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_10_8 : checkNodesBT W_10 g_10 F_10 P_10_8 A_10 B_10_7 8 N_10_8 = true := by decide +kernel
def B_10_8 : BT (List (List Nat)) := buildBucketsBT W_10 N_10_8
set_option maxRecDepth 500000 in
lemma B_10_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_10 8 xs.toFinset) B_10_8 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok (buildPoolsSubBT_sound S_10_ok) A_10_ok B_10_7_ok C_10_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_10_ok : forestRootCheck r_10 g_10 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11),(VAR 4,2,18)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_10_in : bucketContainsBT B_10_8 r_10 = true := by decide +kernel
lemma low_10 : Lower r_10 g_10 9 := lower_of_forestBT root_10_ok B_10_8_ok root_10_in
def g_11 := (d 0xfffefec0fffefec0)
def r_11 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_11 : Lower r_11 g_11 8 := by
  have hc : Lower (varsOf 30) (d 0xfffcfcc0fffcfcc0) 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,8,9)]) (by decide +kernel) hc
def g_12 := (d 0xfffefee0fffefee0)
def r_12 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_12 : Lower r_12 g_12 8 := by
  have hc : Lower (varsOf 30) (d 0xfffcfcc0fffcfcc0) 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,4,5)]) (by decide +kernel) hc
def g_13 := (d 0xfeece000feece000)
def r_13 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_13 : Lower r_13 g_13 8 := by
  have hc : Lower (varsOf 29) (d 0xfaa0a000faa0a000) 7 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_2
  exact lift_of_f (z := 2) (o := 0) (essPairs := [(VAR 1,12,14)]) (by decide +kernel) hc
def g_14 := (d 0xfee0fee0fee0fee0)
def r_14 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_14 : Lower r_14 g_14 5 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,4,5)]) (by decide +kernel) hc
def g_15 := (d 0xe800e800e800e800)
def r_15 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_15 : Lower r_15 g_15 5 := by
  exact lift_of_f (z := 0) (o := 8) (other := r_0) (G := g_0) (essPairs := [(VAR 3,3,11)]) (by decide +kernel) low_0
def g_16 := (d 0xfff8e800fff8e800)
def r_16 : List Nat := varsOf 31
def p_16 : List Nat := [11,11,11,13,13,13,14,14,14,15,19,19,19,20,20,21,21,22,22,23,24,24,25,25,26,26,28]
def q_16 : List Nat := [10,9,3,12,9,5,12,10,6,7,18,17,3,16,4,17,5,18,6,7,16,8,17,9,18,10,12]
def F_16 : Nat := fullMask 27
set_option maxHeartbeats 0 in
lemma gp_16 : goodPairs g_16 p_16 q_16 := goodPairs_of (by decide +kernel)
def W_16 : BT Decor := buildWiresBT 3 (mkBase p_16 q_16 r_16) [(1,2,4)]
lemma W_16_ok : btAll (fun x => faithful p_16 q_16 x ∧ x.1 < 2^256) W_16 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_16 : List (List (Nat × Nat)) := [[]]
def A_16 : BT (List (Nat × Nat)) := btOfList 1 al_16
set_option maxHeartbeats 0 in
lemma A_16_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_16 = g_16) A_16 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_16_0 : Slice r_16 g_16 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) (d 0xfffcfc00fffcfc00) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_14
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_1 : Slice r_16 g_16 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) (d 0xfff0a000fff0a000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_2 : Slice r_16 g_16 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) (d 0xfffafa00fffafa00) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_14
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_3 : Slice r_16 g_16 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) (d 0xff888800ff888800) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_4 : Slice r_16 g_16 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) (d 0xfff0c000fff0c000) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_5 : Slice r_16 g_16 (subcubeFast 0 8) 5 := by
  have hc : Lower (varsOf 23) (d 0xffffe8e8ffffe8e8) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_6 : Slice r_16 g_16 (subcubeFast 16 0) 5 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_15
set_option maxHeartbeats 0 in
lemma sl_16_7 : Slice r_16 g_16 (subcubeFast 16 8) 4 := by
  exact slice_fast_direct_f (z := 16) (o := 8) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_16_8 : Slice r_16 g_16 (identDom 2 3) 6 := by
  have hc : Lower (varsOf 23) (d 0xf8f8e0e0f8f8e0e0) 6 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_6
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
def S_16 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 0 1,5),some (subcubeFast 2 0,5),some (subcubeFast 0 2,5),some (subcubeFast 4 0,5),some (subcubeFast 1 0,5),some (subcubeFast 0 8,5),some (subcubeFast 16 0,5),some (subcubeFast 16 8,4),some (identDom 2 3,6)]
lemma S_16_ok : btAll (fun o => ∀ p, o = some p → Slice r_16 g_16 p.1 p.2) S_16 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_16_0) (forall_cons (fun _ h => by cases h; exact sl_16_1) (forall_cons (fun _ h => by cases h; exact sl_16_2) (forall_cons (fun _ h => by cases h; exact sl_16_3) (forall_cons (fun _ h => by cases h; exact sl_16_4) (forall_cons (fun _ h => by cases h; exact sl_16_5) (forall_cons (fun _ h => by cases h; exact sl_16_6) (forall_cons (fun _ h => by cases h; exact sl_16_7) (forall_cons (fun _ h => by cases h; exact sl_16_8) (fun _ h => (List.not_mem_nil h).elim))))))))))
def ps_16 : BT (Option PoolSpec) := btOfList 4 [q 4 [],q 0 [],q 1 [],q 2 [],q 5 [16393],q 3 [],q 6 [],q 7 [],q 5 [],q 8 []]
def B_16_5 : BT (List (List Nat)) := BT.empty
lemma B_16_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_16 5 xs.toFinset) B_16_5 := .empty
def U_16_6 : List Nat := (r 0 8)
def P_16_6 : BT (Option BoundPool) := buildPoolsSubBT 4 W_16 r_16 S_16 ps_16 U_16_6
def N_16_6 : List NodeSpec := [e5 [5] (r 0 8)]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_16_6 : checkNodesBT W_16 g_16 F_16 P_16_6 A_16 B_16_5 6 N_16_6 = true := by decide +kernel
def B_16_6 : BT (List (List Nat)) := buildBucketsBT W_16 N_16_6
set_option maxRecDepth 500000 in
lemma B_16_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_16 6 xs.toFinset) B_16_6 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok (buildPoolsSubBT_sound S_16_ok) A_16_ok B_16_5_ok C_16_6
def U_16_7 : List Nat := (r 0 4++r 5 5)
def P_16_7 : BT (Option BoundPool) := buildPoolsSubBT 4 W_16 r_16 S_16 ps_16 U_16_7
def N_16_7 : List NodeSpec := [u5 [] (r 0 4++r 5 5)]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_16_7 : checkNodesBT W_16 g_16 F_16 P_16_7 A_16 B_16_6 7 N_16_7 = true := by decide +kernel
def B_16_7 : BT (List (List Nat)) := buildBucketsBT W_16 N_16_7
set_option maxRecDepth 500000 in
lemma B_16_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_16 7 xs.toFinset) B_16_7 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok (buildPoolsSubBT_sound S_16_ok) A_16_ok B_16_6_ok C_16_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_16_ok : forestRootCheck r_16 g_16 [(VAR 0,10,11),(VAR 1,9,11),(VAR 2,9,13),(VAR 3,3,11),(VAR 4,3,19)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_16_in : bucketContainsBT B_16_7 r_16 = true := by decide +kernel
lemma low_16 : Lower r_16 g_16 8 := lower_of_forestBT root_16_ok B_16_7_ok root_16_in
def g_17 := (d 0xffe8e000ffe8e000)
def r_17 : List Nat := varsOf 31
def p_17 : List Nat := [13,13,13,14,14,14,15,15,19,19,19,21,21,21,22,22,22,23,24,24,25,25,26,26,27,28,28]
def q_17 : List Nat := [12,9,5,12,10,6,11,7,18,17,3,20,17,5,20,18,6,7,16,8,17,9,18,10,11,20,12]
def F_17 : Nat := fullMask 27
set_option maxHeartbeats 0 in
lemma gp_17 : goodPairs g_17 p_17 q_17 := goodPairs_of (by decide +kernel)
def W_17 : BT Decor := buildWiresBT 3 (mkBase p_17 q_17 r_17) [(0,2,4)]
lemma W_17_ok : btAll (fun x => faithful p_17 q_17 x ∧ x.1 < 2^256) W_17 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_17 : List (List (Nat × Nat)) := [[]]
def A_17 : BT (List (Nat × Nat)) := btOfList 1 al_17
set_option maxHeartbeats 0 in
lemma A_17_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_17 = g_17) A_17 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_17_0 : Slice r_17 g_17 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) (d 0xfffcf000fffcf000) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_1 : Slice r_17 g_17 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) (d 0xffa0a000ffa0a000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_2 : Slice r_17 g_17 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) (d 0xfffaf000fffaf000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_3 : Slice r_17 g_17 (subcubeFast 0 4) 5 := by
  have hc : Lower (varsOf 27) (d 0xffeeee00ffeeee00) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_14
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_4 : Slice r_17 g_17 (subcubeFast 8 0) 5 := by
  have hc : Lower (varsOf 23) (d 0xe8e80000e8e80000) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_15
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_5 : Slice r_17 g_17 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) (d 0xffc0c000ffc0c000) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_6 : Slice r_17 g_17 (subcubeFast 0 16) 5 := by
  exact slice_fast_direct_f (z := 0) (o := 16) (by decide +kernel) low_5
set_option maxHeartbeats 0 in
lemma sl_17_7 : Slice r_17 g_17 (subcubeFast 8 16) 4 := by
  exact slice_fast_direct_f (z := 8) (o := 16) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_17_8 : Slice r_17 g_17 (identDom 2 3) 6 := by
  have hc : Lower (varsOf 23) (d 0xf8f8e0e0f8f8e0e0) 6 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_6
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
def S_17 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 0 1,5),some (subcubeFast 2 0,5),some (subcubeFast 0 2,5),some (subcubeFast 0 4,5),some (subcubeFast 8 0,5),some (subcubeFast 1 0,5),some (subcubeFast 0 16,5),some (subcubeFast 8 16,4),some (identDom 2 3,6)]
lemma S_17_ok : btAll (fun o => ∀ p, o = some p → Slice r_17 g_17 p.1 p.2) S_17 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_17_0) (forall_cons (fun _ h => by cases h; exact sl_17_1) (forall_cons (fun _ h => by cases h; exact sl_17_2) (forall_cons (fun _ h => by cases h; exact sl_17_3) (forall_cons (fun _ h => by cases h; exact sl_17_4) (forall_cons (fun _ h => by cases h; exact sl_17_5) (forall_cons (fun _ h => by cases h; exact sl_17_6) (forall_cons (fun _ h => by cases h; exact sl_17_7) (forall_cons (fun _ h => by cases h; exact sl_17_8) (fun _ h => (List.not_mem_nil h).elim))))))))))
def ps_17 : BT (Option PoolSpec) := btOfList 4 [q 5 [],q 0 [],q 1 [],q 2 [],q 6 [],q 4 [],q 7 [],q 3 [],q 8 []]
def B_17_5 : BT (List (List Nat)) := BT.empty
lemma B_17_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 5 xs.toFinset) B_17_5 := .empty
def U_17_6 : List Nat := (r 0 8)
def P_17_6 : BT (Option BoundPool) := buildPoolsSubBT 4 W_17 r_17 S_17 ps_17 U_17_6
def N_17_6 : List NodeSpec := [e5 [5] (r 0 8)]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_6 : checkNodesBT W_17 g_17 F_17 P_17_6 A_17 B_17_5 6 N_17_6 = true := by decide +kernel
def B_17_6 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_6
set_option maxRecDepth 500000 in
lemma B_17_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 6 xs.toFinset) B_17_6 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_5_ok C_17_6
def U_17_7 : List Nat := (r 0 9)
def P_17_7 : BT (Option BoundPool) := buildPoolsSubBT 4 W_17 r_17 S_17 ps_17 U_17_7
def N_17_7 : List NodeSpec := [u5 [] (r 0 9)]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_7 : checkNodesBT W_17 g_17 F_17 P_17_7 A_17 B_17_6 7 N_17_7 = true := by decide +kernel
def B_17_7 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_7
set_option maxRecDepth 500000 in
lemma B_17_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 7 xs.toFinset) B_17_7 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_6_ok C_17_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_17_ok : forestRootCheck r_17 g_17 [(VAR 0,12,13),(VAR 1,12,14),(VAR 2,9,13),(VAR 3,5,13),(VAR 4,3,19)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_17_in : bucketContainsBT B_17_7 r_17 = true := by decide +kernel
lemma low_17 : Lower r_17 g_17 8 := lower_of_forestBT root_17_ok B_17_7_ok root_17_in
def g_18 := (d 0xffecf800ffecf800)
def r_18 : List Nat := varsOf 31
def p_18 : List Nat := [11,11,11,12,12,13,13,14,14,15,18,18,19,19,21,21,21,22,22,23,24,24,25,25,26,28]
def q_18 : List Nat := [10,9,3,8,4,9,5,10,6,7,16,2,17,3,20,17,5,20,6,7,16,8,17,9,10,20]
def F_18 : Nat := fullMask 26
set_option maxHeartbeats 0 in
lemma gp_18 : goodPairs g_18 p_18 q_18 := goodPairs_of (by decide +kernel)
def W_18 : BT Decor := buildWiresBT 6 (mkBase p_18 q_18 r_18) [(0,3,4),(1,3,4),(3,5,6),(2,7,2),(0,7,1),(2,7,0),(1,2,3),(0,0,11),(1,2,4),(0,3,13),(1,0,5),(1,2,5),(1,13,3),(3,2,17),(1,1,5),(3,0,6),(0,7,0),(2,1,5),(0,0,6),(2,0,5),(0,1,6),(0,2,6),(2,3,4),(3,1,4),(1,28,3),(3,2,29),(1,1,2),(1,31,3),(2,32,4),(0,0,31),(2,31,4),(1,1,3),(1,36,4),(3,2,37),(3,2,3),(0,0,4),(1,40,3),(3,2,41),(3,5,4),(2,2,5),(3,1,37),(3,2,36),(3,13,3),(1,1,4),(3,2,48),(2,11,4),(2,0,4),(3,51,3),(1,43,1),(3,40,3),(1,51,3),(2,36,4),(0,0,3)]
lemma W_18_ok : btAll (fun x => faithful p_18 q_18 x ∧ x.1 < 2^256) W_18 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_18 : List (List (Nat × Nat)) := [[],[(1,2),(3,4)]]
def A_18 : BT (List (Nat × Nat)) := btOfList 1 al_18
set_option maxHeartbeats 0 in
lemma A_18_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_18 = g_18) A_18 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_18_0 : Slice r_18 g_18 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) (d 0xfffcfc00fffcfc00) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_14
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_1 : Slice r_18 g_18 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) (d 0xffa0f000ffa0f000) 5 := carry_of (swaps := [(1,4),(2,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_2 : Slice r_18 g_18 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) (d 0xffcc8800ffcc8800) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_3 : Slice r_18 g_18 (subcubeFast 4 1) 4 := by
  have hc : Lower (varsOf 26) (d 0xffcccc00ffcccc00) 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_4 : Slice r_18 g_18 (subcubeFast 2 1) 4 := by
  have hc : Lower (varsOf 28) (d 0xfff0f000fff0f000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 2) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_5 : Slice r_18 g_18 (identDom 1 3) 6 := by
  have hc : Lower (varsOf 23) (d 0xececc8c8ececc8c8) 6 := carry_of (swaps := [(1,3),(2,3),(3,4)]) (by decide +kernel) low_6
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_6 : Slice r_18 g_18 (identDom 2 4) 6 := by
  have hc : Lower (varsOf 15) (d 0xf8e0f8e0f8e0f8e0) 6 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_6
  exact slice_ident (u := 2) (v := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_7 : Slice r_18 g_18 (identDom 0 1) 5 := by
  have hc : Lower (varsOf 29) (d 0xffaafa00ffaafa00) 5 := carry_of (swaps := [(0,1),(1,4),(2,4)]) (by decide +kernel) low_8
  exact slice_ident (u := 0) (v := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_8 : Slice r_18 g_18 (identDom 0 4) 5 := by
  have hc : Lower (varsOf 15) (d 0xfaa8faa8faa8faa8) 5 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_8
  exact slice_ident (u := 0) (v := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_9 : Slice r_18 g_18 (identDom 0 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xeeeea8a8eeeea8a8) 5 := carry_of (swaps := [(0,3),(2,3),(3,4)]) (by decide +kernel) low_8
  exact slice_ident (u := 0) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_10 : Slice r_18 g_18 (subcubeFast 1 0) 4 := by
  have hc : Lower (varsOf 30) (d 0xffccf000ffccf000) 4 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
def S_18 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 0 1,5),some (subcubeFast 2 0,5),some (subcubeFast 4 0,5),some (subcubeFast 4 1,4),some (subcubeFast 2 1,4),some (identDom 1 3,6),some (identDom 2 4,6),some (identDom 0 1,5),some (identDom 0 4,5),some (identDom 0 3,5),some (subcubeFast 1 0,4)]
lemma S_18_ok : btAll (fun o => ∀ p, o = some p → Slice r_18 g_18 p.1 p.2) S_18 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_18_0) (forall_cons (fun _ h => by cases h; exact sl_18_1) (forall_cons (fun _ h => by cases h; exact sl_18_2) (forall_cons (fun _ h => by cases h; exact sl_18_3) (forall_cons (fun _ h => by cases h; exact sl_18_4) (forall_cons (fun _ h => by cases h; exact sl_18_5) (forall_cons (fun _ h => by cases h; exact sl_18_6) (forall_cons (fun _ h => by cases h; exact sl_18_7) (forall_cons (fun _ h => by cases h; exact sl_18_8) (forall_cons (fun _ h => by cases h; exact sl_18_9) (forall_cons (fun _ h => by cases h; exact sl_18_10) (fun _ h => (List.not_mem_nil h).elim))))))))))))
def ps_18 : BT (Option PoolSpec) := btOfList 5 [q 2 [],q 8 [],q 4 [],q 3 [],q 0 [],q 10 [],q 5 [],q 1 [],q 6 [],q 6 [16397],q 1 [126976],q 7 [],q 2 [126976],q 0 [8197],q 9 [],q 2 [45056],q 5 [16391,12401],q 5 [16398],q 5 [16397],q 6 [12299]]
def B_18_2 : BT (List (List Nat)) := BT.empty
lemma B_18_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_18 2 xs.toFinset) B_18_2 := .empty
def U_18_3 : List Nat := []
def P_18_3 : BT (Option BoundPool) := buildPoolsSubBT 5 W_18 r_18 S_18 ps_18 U_18_3
def N_18_3 : List NodeSpec := [([8,7,0,1],[],[]),([9,7,0,2],[],[]),([10,7,1,2],[],[]),([12,1,14,4],[],[]),([1,15,16,6],[],[]),([7,0,1,16],[],[]),([7,18,0,1],[],[]),([0,19,16,6],[],[]),([7,20,1,2],[],[]),([21,7,1,2],[],[]),([22,7,0,2],[],[]),([7,23,1,2],[],[]),([7,1,2,15],[],[]),([7,0,1,2],[],[]),([24,7,1,2],[],[]),([0,25,26,5],[],[]),([7,0,25,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_18_3 : checkNodesBT W_18 g_18 F_18 P_18_3 A_18 B_18_2 3 N_18_3 = true := by decide +kernel
def B_18_3 : BT (List (List Nat)) := buildBucketsBT W_18 N_18_3
set_option maxRecDepth 500000 in
lemma B_18_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_18 3 xs.toFinset) B_18_3 :=
  buildBucketsBT_sound (by decide) gp_18 W_18_ok (buildPoolsSubBT_sound S_18_ok) A_18_ok B_18_2_ok C_18_3
def U_18_4 : List Nat := []
def P_18_4 : BT (Option BoundPool) := buildPoolsSubBT 5 W_18 r_18 S_18 ps_18 U_18_4
def N_18_4 : List NodeSpec := [([27,7,0,1,2],[],[]),([18,0,25,3,4],[],[]),([0,25,26,3,4],[],[0]),([7,0,1,2,3],[],[]),([1,3,15,16,4],[],[0]),([18,0,1,5,6],[],[0]),([18,0,1,3,4],[],[]),([0,1,14,11,4],[],[0]),([0,25,2,5,6],[],[0]),([30,0,1,3,4],[],[]),([7,0,1,2,6],[],[0,1]),([27,0,2,19,4],[],[]),([33,0,1,2,3],[],[]),([34,1,3,4,13],[],[]),([7,0,1,2],[],[0,1]),([35,28,0,2,3],[],[]),([23,25,2,3,4],[],[]),([0,1,2,14,6],[],[]),([38,0,1,3,4],[],[]),([39,34,1,3,4],[],[]),([7,0,1,2,5],[],[0,1]),([39,12,1,3,4],[],[]),([42,0,1,3,4],[],[]),([24,1,2,5,6],[],[0]),([18,20,1,3,4],[],[]),([27,43,0,1,2],[],[0]),([12,1,3,4,13],[],[0]),([1,2,5,15,6],[],[0,1]),([24,1,3,16,4],[],[]),([18,23,1,3,4],[],[]),([24,22,2,3,4],[],[]),([0,3,19,16,4],[],[0]),([22,0,3,16,4],[],[]),([0,1,5,16,6],[],[0]),([22,44,0,3,4],[],[]),([22,0,2,5,6],[],[0]),([0,1,2,5,6],[],[0]),([23,1,2,5,6],[],[0]),([18,45,0,3,4],[],[]),([20,1,2,5,6],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_18_4 : checkNodesBT W_18 g_18 F_18 P_18_4 A_18 B_18_3 4 N_18_4 = true := by decide +kernel
def B_18_4 : BT (List (List Nat)) := buildBucketsBT W_18 N_18_4
set_option maxRecDepth 500000 in
lemma B_18_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_18 4 xs.toFinset) B_18_4 :=
  buildBucketsBT_sound (by decide) gp_18 W_18_ok (buildPoolsSubBT_sound S_18_ok) A_18_ok B_18_3_ok C_18_4
def U_18_5 : List Nat := (r 0 17)
def P_18_5 : BT (Option BoundPool) := buildPoolsSubBT 5 W_18 r_18 S_18 ps_18 U_18_5
def N_18_5 : List NodeSpec := [([27,43,0,1,2],[],[0,1]),([18,0,1,3,4,6],[0],[0]),e5 [18] [],([20,1,2,3,4,6],[1,2,3],[0,1]),([23,1,2,3,4],[],[]),u5 [27] [],([27,0,1,2,5,4],[4],[0]),([18,0,1,3,4],[],[]),([23,1,2,3,4,6],[4],[0,1]),e5 [46] [],u5 [14] (r 4 5),u5 [35] [0],a5 [6] [0,1,4,7] [0,1],e5 [47] [],e5 [49] [],e5 [50] [],([39,0,1,31,3,4],[7],[0,1]),([27,43,0,1,2,3],[],[0]),([0,1,2,5,3,6],[9],[0]),([34,1,2,31,3,4],[4,10],[]),e5 [52] [5,6,7],e5 [53] [4,11],e5 [54] [],([0,25,2,3,4,6],[2],[0,1]),e5 [55] [],u5 [32] [4,8,11],([0,1,31,3,4,13],[7,8],[0]),([34,1,2,3,4],[10,12,13],[0,1]),([1,2,5,3,15,4],[2,3,5],[0,1]),u5 [41] [0,14],([12,1,2,3,11,4],[4,15],[0]),([12,1,2,3,4],[15],[0]),([39,0,1,3,11,4],[0],[0]),([22,0,2,5,3,4],[2,6],[0]),([27,0,1,2,36,4],[7],[]),([0,1,3,11,4,13],[8],[0]),a5 [37] [0,4,11] [0,1],e5 [56] [],a5 [29] [0,4,14,16] [0,1],([27,0,1,2,3,6],[4],[0]),([0,1,2,3,13,6],[0],[0]),([24,1,2,5,3,4],[4],[0,1]),([24,1,2,3,4],[],[]),u5 [5] ([0]++r 4 5),([0,1,2,5,6],[],[0,1]),([0,1,5,3,16,4],[0],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_18_5 : checkNodesBT W_18 g_18 F_18 P_18_5 A_18 B_18_4 5 N_18_5 = true := by decide +kernel
def B_18_5 : BT (List (List Nat)) := buildBucketsBT W_18 N_18_5
set_option maxRecDepth 500000 in
lemma B_18_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_18 5 xs.toFinset) B_18_5 :=
  buildBucketsBT_sound (by decide) gp_18 W_18_ok (buildPoolsSubBT_sound S_18_ok) A_18_ok B_18_4_ok C_18_5
def U_18_6 : List Nat := (r 0 10++[13,14,17,18,19])
def P_18_6 : BT (Option BoundPool) := buildPoolsSubBT 5 W_18 r_18 S_18 ps_18 U_18_6
def N_18_6 : List NodeSpec := [a5 [27] ([0,1]++r 4 4++[17]) [0,1],a5 [6] [0,4,5,7,9,18] [0,1],a5 [5] ([0]++r 4 5) [0,1],a5 [39] [3,6,7,8,19] [0,1],a5 [11] [3,7,8] [0,1],a5 [36] [0,2,6,7] [0,1],a5 [31] [3,6,7,8,13] [0,1],u5 [51] (r 1 5),a5 [57] [0,2,3,5,7,14] [1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_18_6 : checkNodesBT W_18 g_18 F_18 P_18_6 A_18 B_18_5 6 N_18_6 = true := by decide +kernel
def B_18_6 : BT (List (List Nat)) := buildBucketsBT W_18 N_18_6
set_option maxRecDepth 500000 in
lemma B_18_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_18 6 xs.toFinset) B_18_6 :=
  buildBucketsBT_sound (by decide) gp_18 W_18_ok (buildPoolsSubBT_sound S_18_ok) A_18_ok B_18_5_ok C_18_6
def U_18_7 : List Nat := [0,2,3,4,6,7,8]
def P_18_7 : BT (Option BoundPool) := buildPoolsSubBT 5 W_18 r_18 S_18 ps_18 U_18_7
def N_18_7 : List NodeSpec := [a5 [] [0,2,3,4,6,7,8] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_18_7 : checkNodesBT W_18 g_18 F_18 P_18_7 A_18 B_18_6 7 N_18_7 = true := by decide +kernel
def B_18_7 : BT (List (List Nat)) := buildBucketsBT W_18 N_18_7
set_option maxRecDepth 500000 in
lemma B_18_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_18 7 xs.toFinset) B_18_7 :=
  buildBucketsBT_sound (by decide) gp_18 W_18_ok (buildPoolsSubBT_sound S_18_ok) A_18_ok B_18_6_ok C_18_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_18_ok : forestRootCheck r_18 g_18 [(VAR 0,10,11),(VAR 1,9,11),(VAR 2,8,12),(VAR 3,3,11),(VAR 4,2,18)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_18_in : bucketContainsBT B_18_7 r_18 = true := by decide +kernel
lemma low_18 : Lower r_18 g_18 8 := lower_of_forestBT root_18_ok B_18_7_ok root_18_in
def g_19 := (d 0xfffef880fffef880)
def r_19 : List Nat := varsOf 31
def p_19 : List Nat := [7,7,7,11,11,11,12,12,13,13,14,14,17,17,18,18,19,20,20,21,22,24,24,25,26]
def q_19 : List Nat := [6,5,3,10,9,3,8,4,9,5,10,6,16,1,16,2,3,16,4,5,6,16,8,9,10]
def F_19 : Nat := fullMask 25
set_option maxHeartbeats 0 in
lemma gp_19 : goodPairs g_19 p_19 q_19 := goodPairs_of (by decide +kernel)
def W_19 : BT Decor := buildWiresBT 7 (mkBase p_19 q_19 r_19) [(1,0,2),(3,3,5),(1,1,3),(3,2,7),(0,0,1),(1,2,3),(2,10,4),(1,2,4),(3,3,12),(1,10,4),(3,1,14),(3,0,14),(0,10,4),(3,17,14),(0,1,10),(1,1,10),(3,19,20),(0,0,14),(0,1,4),(1,1,4),(3,23,24),(2,0,3),(1,26,2),(1,3,4),(3,2,28),(1,9,2),(1,30,4),(3,3,31),(3,2,4),(3,33,28),(3,10,4),(1,35,3),(1,26,4),(0,0,4),(1,38,3),(1,2,39),(2,0,2),(1,41,3),(1,41,4),(3,3,43),(2,27,4),(1,27,4),(1,0,4),(3,3,47),(1,48,2),(0,5,7),(1,38,2),(3,3,51),(2,1,2),(3,53,28),(3,23,0),(3,9,12),(2,0,10),(3,0,10),(2,30,4),(1,9,3),(1,30,3),(1,9,4),(3,3,62),(3,2,47),(3,0,4),(3,65,10),(2,1,3),(1,67,2),(0,0,10),(1,0,10),(3,23,10),(3,1,47),(3,9,10),(3,10,47),(2,30,3),(2,0,4),(3,1,4),(1,77,3),(0,10,47),(1,77,2),(1,80,3),(2,80,3),(2,0,17),(1,58,1),(1,1,17),(2,1,10),(3,86,0),(1,35,2),(3,3,4),(0,0,12),(2,0,28),(1,1,2),(1,0,1),(3,1,10)]
lemma W_19_ok : btAll (fun x => faithful p_19 q_19 x ∧ x.1 < 2^256) W_19 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_19 : List (List (Nat × Nat)) := [[],[(2,3)],[(0,1)],[(0,1),(2,3)]]
def A_19 : BT (List (Nat × Nat)) := btOfList 2 al_19
set_option maxHeartbeats 0 in
lemma A_19_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_19 = g_19) A_19 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_19_0 : Slice r_19 g_19 (identDom 0 1) 7 := by
  have hc : Lower (varsOf 29) (d 0xfffafaa0fffafaa0) 7 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_ident (u := 0) (v := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_19_1 : Slice r_19 g_19 (subcubeFast 4 0) 6 := by
  have hc : Lower (varsOf 27) (d 0xffee8800ffee8800) 6 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_19_2 : Slice r_19 g_19 (subcubeFast 8 0) 6 := by
  have hc : Lower (varsOf 23) (d 0xfefe8080fefe8080) 6 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_19_3 : Slice r_19 g_19 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) (d 0xfffcf000fffcf000) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_19_4 : Slice r_19 g_19 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) (d 0xfffffcc0fffffcc0) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_19_5 : Slice r_19 g_19 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) (d 0xfffaf000fffaf000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_19_6 : Slice r_19 g_19 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) (d 0xfffffaa0fffffaa0) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_19_7 : Slice r_19 g_19 (subcubeFast 16 0) 5 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_4
set_option maxHeartbeats 0 in
lemma sl_19_8 : Slice r_19 g_19 (subcubeFast 3 0) 4 := by
  have hc : Lower (varsOf 28) (d 0xfff0f000fff0f000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 3) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_19_9 : Slice r_19 g_19 (subcubeFast 16 1) 4 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_19_10 : Slice r_19 g_19 (subcubeFast 16 2) 4 := by
  have hc : Lower (varsOf 13) (d 0xfaa0faa0faa0faa0) 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 2) (by decide +kernel) hc
def S_19 : BT (Option (Nat × Nat)) := btOfList 4 [some (identDom 0 1,7),some (subcubeFast 4 0,6),some (subcubeFast 8 0,6),some (subcubeFast 1 0,5),some (subcubeFast 0 1,5),some (subcubeFast 2 0,5),some (subcubeFast 0 2,5),some (subcubeFast 16 0,5),some (subcubeFast 3 0,4),some (subcubeFast 16 1,4),some (subcubeFast 16 2,4)]
lemma S_19_ok : btAll (fun o => ∀ p, o = some p → Slice r_19 g_19 p.1 p.2) S_19 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_19_0) (forall_cons (fun _ h => by cases h; exact sl_19_1) (forall_cons (fun _ h => by cases h; exact sl_19_2) (forall_cons (fun _ h => by cases h; exact sl_19_3) (forall_cons (fun _ h => by cases h; exact sl_19_4) (forall_cons (fun _ h => by cases h; exact sl_19_5) (forall_cons (fun _ h => by cases h; exact sl_19_6) (forall_cons (fun _ h => by cases h; exact sl_19_7) (forall_cons (fun _ h => by cases h; exact sl_19_8) (forall_cons (fun _ h => by cases h; exact sl_19_9) (forall_cons (fun _ h => by cases h; exact sl_19_10) (fun _ h => (List.not_mem_nil h).elim))))))))))))
def ps_19 : BT (Option PoolSpec) := btOfList 7 [q 1 [16424,16425,57415],q 1 [40964,40965,81999],q 1 [16388,16389,98399],q 1 [],q 1 [49165,57344],q 2 [16393,57344],q 2 [],q 7 [],q 3 [],q 4 [],q 5 [],q 6 [],q 1 [16425,57351],q 1 [16425,57344],q 0 [],q 4 [12441],q 1 [16384,12441],q 1 [16426,16427],q 1 [16385,192527],q 2 [16384,8345],q 1 [16388,95],q 0 [12297,40963],q 0 [12297,40962],q 1 [40962,40963],q 8 [],q 9 [],q 10 [],q 2 [16388,16389,98399],q 0 [12294,8461],q 1 [40960,40961],q 1 [16388,41055],q 1 [16385,192519],q 0 [12297,40999],q 1 [16385,192555],q 1 [16386,16387],q 1 [16385,192552],q 1 [16384,12493],q 1 [16424,69634],q 0 [16421,16393],q 1 [40963,4329],q 4 [16397,16393],q 6 [16397,16393],q 2 [16393],q 1 [16424,69637],q 1 [40966,347],q 1 [16384,16385],q 1 [16424,16425],q 2 [8549],q 1 [49167],q 1 [16397],q 1 [16426],q 2 [16426],q 1 [16427],q 1 [16425],q 2 [16425],q 1 [16424],q 4 [16397],q 6 [16397],q 2 [16489],q 1 [12310],q 2 [8193],q 1 [12293],q 0 [8193],q 0 [12293],q 0 [12297],q 1 [16384],q 1 [4096],q 1 [16391],q 0 [16385,192519],q 2 [16385,192519],q 5 [8193],q 0 [12290],q 0 [16393],q 0 [8197],q 3 [8197],q 1 [4],q 0 [16421],q 1 [40961],q 1 [49165],q 1 [4097],q 0 [16385],q 2 [16385],q 0 [16384,12441],q 1 [16399],q 0 [12290,8297],q 1 [12290],q 2 [8297],q 2 [16388,95],q 0 [16384,8345],q 1 [16385],q 1 [16386],q 2 [16384,16385],q 1 [40962],q 2 [16386,16387],q 1 [40960],q 1 [40967],q 0 [16391],q 2 [16391],q 2 [16386],q 0 [16384],q 2 [16384],q 2 [4097],q 2 [4096]]
def B_19_2 : BT (List (List Nat)) := BT.empty
lemma B_19_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_19 2 xs.toFinset) B_19_2 := .empty
def U_19_3 : List Nat := []
def P_19_3 : BT (Option BoundPool) := buildPoolsSubBT 7 W_19 r_19 S_19 ps_19 U_19_3
def N_19_3 : List NodeSpec := [([6,8,9,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_19_3 : checkNodesBT W_19 g_19 F_19 P_19_3 A_19 B_19_2 3 N_19_3 = true := by decide +kernel
def B_19_3 : BT (List (List Nat)) := buildBucketsBT W_19 N_19_3
set_option maxRecDepth 500000 in
lemma B_19_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_19 3 xs.toFinset) B_19_3 :=
  buildBucketsBT_sound (by decide) gp_19 W_19_ok (buildPoolsSubBT_sound S_19_ok) A_19_ok B_19_2_ok C_19_3
def U_19_4 : List Nat := [0,1,2]
def P_19_4 : BT (Option BoundPool) := buildPoolsSubBT 7 W_19 r_19 S_19 ps_19 U_19_4
def N_19_4 : List NodeSpec := [([11,13,0,1,2],[],[]),([15,16,2,3,4],[],[]),([18,0,1,2,3],[0],[]),([21,0,2,3,4],[1],[]),([15,22,2,3,4],[],[]),([25,0,2,3,10],[2],[]),([13,0,1,27,4],[],[]),([6,8,0,1,4],[],[0]),([13,29,0,1,4],[],[]),([6,9,2,7,4],[],[0]),([13,22,1,2,4],[],[]),([32,0,1,2,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_19_4 : checkNodesBT W_19 g_19 F_19 P_19_4 A_19 B_19_3 4 N_19_4 = true := by decide +kernel
def B_19_4 : BT (List (List Nat)) := buildBucketsBT W_19 N_19_4
set_option maxRecDepth 500000 in
lemma B_19_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_19 4 xs.toFinset) B_19_4 :=
  buildBucketsBT_sound (by decide) gp_19 W_19_ok (buildPoolsSubBT_sound S_19_ok) A_19_ok B_19_3_ok C_19_4
def U_19_5 : List Nat := (r 2 45)
def P_19_5 : BT (Option BoundPool) := buildPoolsSubBT 7 W_19 r_19 S_19 ps_19 U_19_5
def N_19_5 : List NodeSpec := [([11,0,1,2,3,12],[3],[0]),([22,1,2,3,4,12],[4,5],[0]),([0,1,2,34,3,28],[6,7],[]),([13,0,1,2,4,28],[6],[0]),([13,0,1,2,12,28],[6,7],[]),([0,1,2,36,10,4],[3,7],[]),([0,1,2,3,37,28],[6,8],[]),e5 [14] (r 8 4),([13,0,1,2,10,4],[3],[0]),([15,0,2,3,10,4],[12],[]),([22,1,2,3,10,4],[13],[]),([11,0,1,2,3,14],[14],[0,1]),([6,9,1,2,3,4],[11],[0]),([0,1,2,39,40,4],[8,15,16],[]),([0,2,30,3,7,4],[6],[]),([0,1,2,42,10,4],[3,8],[]),e5 [44] [],([11,35,0,1,2,3],[17],[0]),e5 [45] [],e5 [46] [9],([26,13,0,1,2,4],[9],[0]),([0,1,2,42,4,28],[7],[1]),e5 [49] [18],e5 [50] [],([13,0,1,10,4,12],[3,6],[]),([6,0,1,2,7,4],[9,10],[0]),([0,1,2,39,10,4],[3,8,15],[]),([52,0,1,51,3,4],[19],[]),e5 [54] [3],([13,0,1,2,4,14],[14],[0,2]),([55,1,2,3,10,4],[20],[]),e5 [56] [],u5 [31] [6,14],([9,2,5,3,7,4],[9],[0,3]),([57,58,1,2,3,4],[21,22,23],[2]),e5 [59] [],([0,1,2,60,10,4],[3],[]),e5 [61] [],e5 [63] [],([26,64,1,2,3,4],[],[]),([25,0,2,3],([2]++r 24 4),[0]),e5 [66] [],([0,2,68,3,4,24],[28],[]),([69,1,2,3,70,4],[29],[2]),e5 [71] [3,30],([72,0,2,3,10,4],[31],[]),e5 [73] [14,32],([15,0,2,3,4,14],[10],[0]),e5 [74] [33],([22,1,2,3,4,14],[9,24],[0,1]),e5 [75] [],([76,65,1,2,3,10],[34],[2]),([0,1,2,60,4,28],[7,8,10],[]),([0,1,2,78,10,4],[3,11],[]),e5 [79] [9,35],e5 [81] [8,9,11],([0,1,2,17,10,28],[6],[]),e5 [82] [],e5 [40] [8,36],([83,1,2,3,10,4],[37],[]),([6,0,1,2,10,4],[3,9],[]),([0,1,2,3,62,12],[3,8,10,25,26,38],[]),([0,1,10,4,12,28],[3,7],[]),([0,84,2,3,10,4],[39],[]),([0,1,10,12,28],[3,6,7,40,41,42],[]),e5 [52] [19],([11,0,1,2,10,28],[6,7],[]),([0,2,3,10,85,4],[43],[]),([87,1,2,3,10,4],[44],[]),e5 [11] [],([38,1,2,3,10,47],[45],[2]),([0,1,2,3,17,14],[46],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_19_5 : checkNodesBT W_19 g_19 F_19 P_19_5 A_19 B_19_4 5 N_19_5 = true := by decide +kernel
def B_19_5 : BT (List (List Nat)) := buildBucketsBT W_19 N_19_5
set_option maxRecDepth 500000 in
lemma B_19_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_19 5 xs.toFinset) B_19_5 :=
  buildBucketsBT_sound (by decide) gp_19 W_19_ok (buildPoolsSubBT_sound S_19_ok) A_19_ok B_19_4_ok C_19_5
def U_19_6 : List Nat := ([3]++r 6 6++[16,18,19,20,24,25,26,31,34,42,45]++r 47 49)
def P_19_6 : BT (Option BoundPool) := buildPoolsSubBT 7 W_19 r_19 S_19 ps_19 U_19_6
def N_19_6 : List NodeSpec := [e5 [88] [25,26,47],a5 [13] ([3]++r 8 4++[42,48]) [0,2],a5 [12,28] [6,7,49] [0,1],([0,1,2,3,12,28],[25,26,42,49],[0,1]),e5 [90,12] [3,7,8,9,25],a5 [11,10] [3,6,7,50] [0,1],u5 [11] ([3,6]++r 8 4++[50,51]),a5 [35,10] [7,52] [0,1],a5 [14] (r 8 4++[53,54]) [0,1,2],a5 [17,10] [6,7,55] [0,1,2],u5 [91,28] [8,25],([0,1,2,10,4,28],[6,7,49,56,57],[0,1]),a5 [37] [3,8,10,11,25,58] [0,1],u5 [6] [6,7,9,10,11,25,59,60],a5 [5,7] ([9,11]++r 60 4) [0,3],a5 [38,10] [3,6,8,9,64,65] [0,1,2],a5 [9,10] ([3,6]++r 8 4++[64,66]) [0,1],a5 [80] [6,11,25,67] [0,1],([72,0,2,3,4],[9,11,25,31,68,69],[0]),([26,1,2,5,3,4],[3,6,8,9,25,70,71],[]),a5 [9,12] [3,7,8,10,25,26,72] [0,1],([9,0,2,92,3,4],[3,11,26,73,74,75],[1,2]),a5 [26,12] [3,6,8,25] [0,1,3],a5 [62] [3,6,8,10,25,26,76] [0,1],a5 [10,70] [8,9,77] [0,1],a5 [12,14] [25,26,42,78] [0,1,2],e5 [93,10] (r 8 4++[24,64,79]),([26,1,2,3,4,47],[7,8,9,71,80,81],[0,2]),([0,1,2,39,4],[7,8,16,24,82],[0,1]),([89,0,1,2,3,12],[3,7,25,26,42,83],[1]),a5 [27] [7,8,24,84,85,86] [0,1,2],a5 [30] [6,7,8,10,66] [0,1,2],([55,1,2,3,4],[7,8,10,20,87],[0]),a5 [51] [7,8,19,24,65,88] [0,1],u5 [13,12] [3,6,7,42,48],u5 [10,47] [8,9,64,89],u5 [76,10] [8,25,90],([38,1,2,3,47],[8,9,24,45,91],[0,2]),a5 [57,10] [8,9,64,92] [0,1,2],a5 [48] ([3,6]++r 8 4++[18,25,81]) [0,1],([76,65,1,2,3],[8,9,24,34,93],[0,2]),a5 [77,10] [3,6,10,11,67] [0,1,2],u5 [69,10] [8,9,94],a5 [10,14] [7,53] [0,1,2],a5 [94,10] [10,11,64,95] [2]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_19_6 : checkNodesBT W_19 g_19 F_19 P_19_6 A_19 B_19_5 6 N_19_6 = true := by decide +kernel
def B_19_6 : BT (List (List Nat)) := buildBucketsBT W_19 N_19_6
set_option maxRecDepth 500000 in
lemma B_19_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_19 6 xs.toFinset) B_19_6 :=
  buildBucketsBT_sound (by decide) gp_19 W_19_ok (buildPoolsSubBT_sound S_19_ok) A_19_ok B_19_5_ok C_19_6
def U_19_7 : List Nat := ([3]++r 6 6++[14,24,25,26,42,60]++r 64 4++[71,72,79,80,81,83,85,89,90]++r 96 7)
def P_19_7 : BT (Option BoundPool) := buildPoolsSubBT 7 W_19 r_19 S_19 ps_19 U_19_7
def N_19_7 : List NodeSpec := [u5 [89] ([3]++r 6 6++[25,26,83]),a5 [12] [3,8,10,25,26,42,72] [0,1,2,3],a5 [10] ([3]++r 6 6++[64]) [0,1,2],a5 [77] [3,6,9,10,11,14,25,67,96,97] [0,1,2],u5 [76] [8,10,14,24,25,90,98],a5 [38] ([3]++r 6 5++[14,24,65,99,100]) [0,1,2],u5 [26] [3,6,7,8,10,14,24,25,71,85],a5 [5] [3,8,9,11,14,24,25,60] [0,2],a5 [47] [7,8,9,14,24,25,26,80,81,89] [0,1],u5 [93] [9,11,14,24,25,79,101],a5 [9] [3,6,7,8,10,14,25,26,66,102] [0,1,2,3]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_19_7 : checkNodesBT W_19 g_19 F_19 P_19_7 A_19 B_19_6 7 N_19_7 = true := by decide +kernel
def B_19_7 : BT (List (List Nat)) := buildBucketsBT W_19 N_19_7
set_option maxRecDepth 500000 in
lemma B_19_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_19 7 xs.toFinset) B_19_7 :=
  buildBucketsBT_sound (by decide) gp_19 W_19_ok (buildPoolsSubBT_sound S_19_ok) A_19_ok B_19_6_ok C_19_7
def U_19_8 : List Nat := [3,6,14]
def P_19_8 : BT (Option BoundPool) := buildPoolsSubBT 7 W_19 r_19 S_19 ps_19 U_19_8
def N_19_8 : List NodeSpec := [a5 [] [3,6,14] [0,1,2,3]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_19_8 : checkNodesBT W_19 g_19 F_19 P_19_8 A_19 B_19_7 8 N_19_8 = true := by decide +kernel
def B_19_8 : BT (List (List Nat)) := buildBucketsBT W_19 N_19_8
set_option maxRecDepth 500000 in
lemma B_19_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_19 8 xs.toFinset) B_19_8 :=
  buildBucketsBT_sound (by decide) gp_19 W_19_ok (buildPoolsSubBT_sound S_19_ok) A_19_ok B_19_7_ok C_19_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_19_ok : forestRootCheck r_19 g_19 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11),(VAR 4,1,17)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_19_in : bucketContainsBT B_19_8 r_19 = true := by decide +kernel
lemma low_19 : Lower r_19 g_19 9 := lower_of_forestBT root_19_ok B_19_8_ok root_19_in
def g_20 := (d 0xfffee800fffee800)
def r_20 : List Nat := varsOf 31
def p_20 : List Nat := [11,11,11,13,13,13,14,14,14,15,17,17,18,18,19,20,20,21,22,23,24,24,25,26,28]
def q_20 : List Nat := [10,9,3,12,9,5,12,10,6,7,16,1,16,2,3,16,4,5,6,7,16,8,9,10,12]
def F_20 : Nat := fullMask 25
set_option maxHeartbeats 0 in
lemma gp_20 : goodPairs g_20 p_20 q_20 := goodPairs_of (by decide +kernel)
def W_20 : BT Decor := buildWiresBT 8 (mkBase p_20 q_20 r_20) [(0,3,4),(1,2,5),(1,0,1),(0,7,3),(1,8,4),(1,0,2),(1,2,1),(1,11,4),(0,3,12),(1,7,4),(3,3,14),(1,1,10),(1,16,4),(3,2,17),(0,3,14),(0,2,14),(3,3,4),(1,21,8),(3,2,4),(3,2,7),(1,24,4),(3,2,3),(1,3,4),(0,10,27),(3,1,3),(1,2,4),(3,29,30),(1,0,4),(3,2,32),(1,26,0),(0,11,4),(3,35,12),(0,0,12),(0,7,30),(3,7,3),(1,39,2),(3,0,3),(3,41,11),(2,3,4),(2,7,4),(3,1,10),(1,10,4),(0,3,46),(3,11,3),(0,1,46),(3,1,14),(3,2,9),(1,2,3),(3,1,52),(3,5,27),(1,23,1),(1,21,7),(2,56,2),(0,11,3),(1,11,3),(3,58,59),(2,7,3),(3,0,30),(3,2,27),(1,63,0),(3,11,27),(1,0,5),(3,2,66),(1,7,3),(1,48,2),(1,48,4),(3,11,4),(1,71,2),(0,16,3),(1,1,4),(2,8,4),(1,26,4),(0,10,3),(3,35,3),(2,26,4),(1,26,1),(1,48,0),(1,34,4),(2,34,4),(0,7,4),(1,84,2),(1,79,0),(0,10,4),(1,21,0),(2,88,2),(1,84,3),(1,0,3),(3,11,91),(1,1,3),(3,2,93),(1,94,0),(0,7,52),(2,11,4),(1,97,0),(1,0,6),(2,16,4),(3,1,4),(1,101,0),(2,102,2),(1,26,7),(3,0,4),(3,105,11),(1,21,2),(1,61,2),(0,7,27),(1,10,3),(3,2,110),(2,24,4),(1,7,5),(3,21,7),(1,29,4),(3,2,115),(3,97,3),(0,3,30),(3,7,4),(3,11,32),(2,7,5),(1,58,0),(3,0,11),(3,123,3),(1,29,0),(2,125,2),(1,23,7),(3,41,74),(3,26,27),(3,2,74),(1,130,0),(3,62,3),(0,3,74),(1,0,133),(0,3,32),(1,23,0)]
lemma W_20_ok : btAll (fun x => faithful p_20 q_20 x ∧ x.1 < 2^256) W_20 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_20 : List (List (Nat × Nat)) := [[],[(1,2)],[(0,1)],[(0,2),(1,2)],[(0,1),(1,2)],[(0,2)]]
def A_20 : BT (List (Nat × Nat)) := btOfList 3 al_20
set_option maxHeartbeats 0 in
lemma A_20_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_20 = g_20) A_20 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_20_0 : Slice r_20 g_20 (subcubeFast 1 0) 6 := by
  have hc : Lower (varsOf 30) (d 0xfffcc000fffcc000) 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_20_1 : Slice r_20 g_20 (subcubeFast 2 0) 6 := by
  have hc : Lower (varsOf 29) (d 0xfffaa000fffaa000) 6 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_20_2 : Slice r_20 g_20 (subcubeFast 4 0) 6 := by
  have hc : Lower (varsOf 27) (d 0xffee8800ffee8800) 6 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_20_3 : Slice r_20 g_20 (subcubeFast 0 8) 5 := by
  have hc : Lower (varsOf 23) (d 0xffffe8e8ffffe8e8) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_20_4 : Slice r_20 g_20 (subcubeFast 16 0) 5 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_15
set_option maxHeartbeats 0 in
lemma sl_20_5 : Slice r_20 g_20 (subcubeFast 16 8) 4 := by
  exact slice_fast_direct_f (z := 16) (o := 8) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_20_6 : Slice r_20 g_20 (identDom 0 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xfefea8a8fefea8a8) 5 := carry_of (swaps := [(0,2),(1,2),(3,4)]) (by decide +kernel) low_14
  exact slice_ident (u := 0) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_20_7 : Slice r_20 g_20 (identDom 1 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xfefec8c8fefec8c8) 5 := carry_of (swaps := [(1,2),(3,4)]) (by decide +kernel) low_14
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_20_8 : Slice r_20 g_20 (identDom 2 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xfefee0e0fefee0e0) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_14
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
def S_20 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 1 0,6),some (subcubeFast 2 0,6),some (subcubeFast 4 0,6),some (subcubeFast 0 8,5),some (subcubeFast 16 0,5),some (subcubeFast 16 8,4),some (identDom 0 3,5),some (identDom 1 3,5),some (identDom 2 3,5)]
lemma S_20_ok : btAll (fun o => ∀ p, o = some p → Slice r_20 g_20 p.1 p.2) S_20 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_20_0) (forall_cons (fun _ h => by cases h; exact sl_20_1) (forall_cons (fun _ h => by cases h; exact sl_20_2) (forall_cons (fun _ h => by cases h; exact sl_20_3) (forall_cons (fun _ h => by cases h; exact sl_20_4) (forall_cons (fun _ h => by cases h; exact sl_20_5) (forall_cons (fun _ h => by cases h; exact sl_20_6) (forall_cons (fun _ h => by cases h; exact sl_20_7) (forall_cons (fun _ h => by cases h; exact sl_20_8) (fun _ h => (List.not_mem_nil h).elim))))))))))
def ps_20 : BT (Option PoolSpec) := btOfList 7 [q 1 [16428,16429,49295],q 1 [],q 2 [],q 0 [],q 0 [16396,16397,110615],q 1 [12332,12333,241899],q 0 [16397,110603],q 1 [16397,110603],q 2 [16396,20481],q 0 [12316,12317],q 7 [],q 4 [],q 8 [],q 0 [16413,57355],q 3 [16489],q 3 [],q 1 [16428,12431],q 6 [],q 0 [16412,8529],q 4 [122894],q 0 [16412,12625],q 1 [12299,105],q 0 [16396,20489],q 3 [20489],q 1 [16385,131083],q 0 [12319,8349],q 0 [12299,28777],q 0 [12318,12319],q 5 [],q 0 [12318,8437],q 0 [16397,110620],q 0 [16412,16413],q 0 [16396,20509],q 0 [131077,57356],q 1 [16385,57356],q 0 [16413,57356],q 1 [16413,57356],q 0 [16396,16397],q 1 [9],q 0 [16413,57359],q 0 [16393,122892],q 3 [16393],q 0 [16414,16415],q 1 [12291,45223],q 0 [16393,122908],q 1 [16385,131119],q 0 [16396,20510],q 1 [16397,110639],q 0 [16398,16399],q 2 [12295,117],q 1 [16396,16397,110615],q 2 [16396,16397,110615],q 0 [16389,303115],q 0 [131077,57355],q 3 [16389],q 4 [12299],q 0 [16389,303116],q 0 [16399],q 1 [16398,16399],q 2 [16398,16399],q 2 [16397],q 4 [110603],q 0 [16396],q 1 [16396,20481],q 3 [20481],q 1 [16396,20489],q 1 [16396,16397],q 2 [16396,16397],q 0 [131084],q 1 [16385,131084],q 2 [16385,131084],q 0 [131083],q 2 [16385],q 0 [16389],q 1 [16385],q 2 [16398],q 1 [12299],q 2 [12295],q 0 [12299],q 2 [16489],q 2 [105],q 0 [16395],q 2 [93],q 2 [4097],q 0 [12318],q 0 [12317],q 0 [8221],q 0 [16413],q 0 [16397],q 0 [8222],q 0 [12316],q 1 [12316],q 0 [16393],q 0 [8197],q 1 [12335],q 1 [8222],q 0 [131077],q 1 [8221],q 0 [4105],q 1 [16431],q 2 [12335],q 0 [16412],q 2 [16490],q 1 [16413],q 0 [16414],q 1 [16414],q 0 [12297],q 0 [16398],q 0 [372747],q 2 [12289],q 1 [16399],q 2 [16399],q 1 [16398],q 1 [16397],q 1 [16396],q 2 [16396],q 1 [16395],q 1 [12289]]
def B_20_2 : BT (List (List Nat)) := BT.empty
lemma B_20_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_20 2 xs.toFinset) B_20_2 := .empty
def U_20_3 : List Nat := []
def P_20_3 : BT (Option BoundPool) := buildPoolsSubBT 7 W_20 r_20 S_20 ps_20 U_20_3
def N_20_3 : List NodeSpec := [([0,1,6,9],[],[]),([7,10,13,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_20_3 : checkNodesBT W_20 g_20 F_20 P_20_3 A_20 B_20_2 3 N_20_3 = true := by decide +kernel
def B_20_3 : BT (List (List Nat)) := buildBucketsBT W_20 N_20_3
set_option maxRecDepth 500000 in
lemma B_20_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_20 3 xs.toFinset) B_20_3 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok (buildPoolsSubBT_sound S_20_ok) A_20_ok B_20_2_ok C_20_3
def U_20_4 : List Nat := (r 0 6)
def P_20_4 : BT (Option BoundPool) := buildPoolsSubBT 7 W_20 r_20 S_20 ps_20 U_20_4
def N_20_4 : List NodeSpec := [([15,18,0,1,4],[],[]),([18,0,1,19,4],[],[]),([15,0,1,20,4],[],[]),([0,1,22,2,4],[],[]),([23,0,1,3,25],[],[]),([26,0,1,28,4],[],[]),([0,31,11,3,4],[],[]),([33,34,1,3,4],[],[]),([0,1,10,13,4],[],[0]),([36,0,1,2,3],[0],[]),([37,1,2,13,4],[],[]),([0,38,11,3,4],[1],[]),([0,1,40,4,27],[],[]),([42,1,10,3,4],[2],[]),([26,0,8,11,4],[],[]),([43,0,1,40,4],[],[]),([44,10,11,3,4],[],[]),([24,45,0,3,4],[],[]),([33,0,1,47,4],[],[]),([48,7,10,3,4],[3],[]),([33,0,49,3,4],[],[]),([44,50,0,2,3],[],[]),([7,10,3,4,12],[3],[0]),([8,10,11,3,4],[],[]),([51,0,1,3,4],[],[]),([24,53,0,3,4],[],[]),([54,0,1,7,2],[4],[]),([24,0,55,3,4],[],[]),([57,0,1,3,4],[],[]),([18,0,1,3,4],[],[]),([0,1,2,5,9],[],[0]),([0,1,8,6,4],[],[0]),([60,0,1,2,4],[5],[]),([61,0,1,40,4],[],[]),([33,62,1,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_20_4 : checkNodesBT W_20 g_20 F_20 P_20_4 A_20 B_20_3 4 N_20_4 = true := by decide +kernel
def B_20_4 : BT (List (List Nat)) := buildBucketsBT W_20 N_20_4
set_option maxRecDepth 500000 in
lemma B_20_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_20 4 xs.toFinset) B_20_4 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok (buildPoolsSubBT_sound S_20_ok) A_20_ok B_20_3_ok C_20_4
def U_20_5 : List Nat := (r 1 4++r 6 51)
def P_20_5 : BT (Option BoundPool) := buildPoolsSubBT 7 W_20 r_20 S_20 ps_20 U_20_5
def N_20_5 : List NodeSpec := [e5 [64] [6],([65,63,0,1,3,4],[7],[]),([63,0,64,1,3,4],[6],[]),e5 [67] [8],e5 [44] [],([0,1,8,2,68,4],[9],[4]),([0,1,69,11,3,4],[1,10],[]),([0,1,16,3,4,30],[11],[]),e5 [70] [],([0,1,72,11,3,4],[1,11],[]),e5 [73] [],([24,23,0,1,3,4],[],[0,2]),([0,11,3,4,74,30],[1,11],[]),([67,1,2,3,66,4],[8],[]),([0,1,40,3,4],[],[0]),([61,29,0,7,2,4],[],[]),([21,0,1,8,2,4],[],[0]),([24,0,1,3,52,4],[12],[0,2]),([18,0,1,7,3,4],[13],[]),([33,0,1,3,4,30],[2],[0]),e5 [75] [],([43,26,0,1,2,76],[11,14],[]),([26,0,1,77,10,4],[15],[]),([43,48,0,1,2,4],[11],[3]),([26,0,1,8,2,4],[2],[0,2]),([78,0,1,2,11,4],[16],[]),([79,0,1,10,3,4],[3],[]),([37,1,2,3,4,12],[],[0,2,3,4]),([26,0,80,11,3,4],[1],[]),u5 [9] [1,2,3,17],([0,1,10,3,4,12],[3],[0]),e5 [81] [],e5 [82] [15],a5 [17] [15,17] [0,1,3],([48,0,1,10,3,4],[3],[0]),e5 [83] [],([0,1,7,85,3,4],[18],[]),([24,29,0,2,3,4],[],[]),e5 [86] [],([0,1,87,10,3,30],[],[]),([0,7,11,3,4,30],[],[0,2]),e5 [89] [],([26,0,7,11,3,4],[],[0,2,4]),([0,1,10,3,4,76],[3],[]),([0,1,2,3,76,30],[2,12,19],[]),([44,0,2,11,3,4],[2],[0]),([0,1,7,2,90,4],[20],[]),e5 [92] [17],([24,0,7,11,3,4],[1,2],[]),([63,0,1,10,3,4],[3],[]),([26,0,1,10,4,27],[],[0]),e5 [95] [],([48,0,1,2,4,27],[],[3]),e5 [96] [],([26,33,0,1,3,4],[15],[0]),([0,34,1,11,3,4],[21],[]),e5 [98] [],([0,1,3,6,99,4],[12,22,23],[]),e5 [100] [],([33,1,7,2,3,4],[1,24],[]),([0,1,7,40,3,4],[17,25],[0]),([0,1,8,2,5,4],[10,17],[0]),([26,29,0,11,3,4],[1,2,15],[]),e5 [103] [],e5 [104] [2,26],e5 [106] [],([61,39,0,1,2,4],[27],[0,4]),([0,1,10,3,6,4],[3,12,23],[]),([0,1,107,10,3,4],[3,15],[]),([26,0,1,16,3,4],[15],[]),([43,26,0,1,10,4],[28],[]),([44,0,7,2,3,74],[11],[]),([24,0,1,16,3,4],[3],[0,2]),([0,1,7,108,3,4],[29],[]),a5 [109] [15,30] [1,3],([0,1,84,2,3,14],[31],[4]),([111,0,1,11,3,4],[1,15],[3]),([33,0,1,3,4,46],[3],[0,1]),e5 [112] [],e5 [113] [17,32],e5 [114] [],([0,1,8,2,52,4],[2],[]),([18,0,1,3,4],[],[]),([0,1,2,19,4,32],[33,34],[1]),([24,0,2,3,4,74],[],[]),e5 [18] [],([18,0,1,3,4,14],[2],[0]),([0,1,2,19,4],[35,36],[4,5]),e5 [19] [],([0,1,7,2,5,27],[37],[0]),([7,10,11,3,4],[1,2,3,38],[0,1,2,3,4]),([0,1,2,19,4,14],[15],[0,1,3,4]),([15,0,1,2,4,14],[17],[0]),([15,0,1,7,2,4],[39],[]),([44,0,1,2,3,14],[3],[0,2]),([33,0,1,10,3,4],[3],[1]),([0,1,7,2,19,4],[35],[]),([43,0,34,1,2,4],[],[]),e5 [116] [],([33,1,10,3,4,32],[2],[]),([111,0,1,10,3,4],[3,15],[]),e5 [117] [1,2,3,17],([0,1,10,118,3,4],[3,40,41],[]),([0,1,72,10,3,4],[3],[1]),u5 [14] [2,15,17],([44,119,0,1,2,3],[42],[4]),([24,0,1,10,3,4],[3],[0]),a5 [42] [1,2,15,43] [0,1],a5 [38] [1,11,44] [0,2],e5 [120] [45],([0,1,77,11,3,4],[1],[1]),e5 [121] [3,46],e5 [122] [],([0,1,7,3,6,4],[22,23],[0]),e5 [124] [17],e5 [65] [47],([63,0,1,7,3,4],[6],[]),([43,21,0,1,7,2],[48],[0]),u5 [56] [2,15],([0,1,69,3,4,30],[11],[4]),e5 [126] [49],([0,34,1,2,4,27],[],[]),u5 [127] [15,17],a5 [128] [] [4],([54,0,1,2],[4,28,50,51],[0,1,3]),e5 [8] [],([26,0,1,2,129,4],[15],[]),e5 [131] [52],([18,0,1,3,4,32],[53],[]),([44,0,1,2,3,32],[3],[0]),u5 [25] [],([26,0,11,3,4,74],[1,54,55],[1]),e5 [132] [],e5 [134] [56]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_20_5 : checkNodesBT W_20 g_20 F_20 P_20_5 A_20 B_20_4 5 N_20_5 = true := by decide +kernel
def B_20_5 : BT (List (List Nat)) := buildBucketsBT W_20 N_20_5
set_option maxRecDepth 500000 in
lemma B_20_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_20 5 xs.toFinset) B_20_5 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok (buildPoolsSubBT_sound S_20_ok) A_20_ok B_20_4_ok C_20_5
def U_20_6 : List Nat := ([1,2,3,6,7,8,10,11,12,14,15,17]++r 21 4++[28,37,38,41,48,55]++r 57 53)
def P_20_6 : BT (Option BoundPool) := buildPoolsSubBT 7 W_20 r_20 S_20 ps_20 U_20_6
def N_20_6 : List NodeSpec := [a5 [88] [1,2,11,15,57] [0,1,3,5],([43,21,0,1,2],[28,48,58,59],[0,1,3]),a5 [63] [1,2,3,6,7,15,28,60] [0,2],([63,0,1,3,4],[6,7,15,28,61],[0,2]),a5 [66] [8,28,62,63,64] [0,1,3,5],([0,1,3,6,4],[22,23,28,65],[0,2,4,5]),e5 [135,32] [3,11,17,28],([0,1,2,5,27],[11,15,37,66,67],[0,1,3]),a5 [135] [1,2,10,11,12,17,28,68,69,70] [2,3,4,5],u5 [33,32] [2,3,11,71,72],a5 [33] [1,3,12,15,24,71,72] [0,2,5],a5 [32,74] [73,74] [1,3,4],([43,26,0,1,2,4],[2,11,28,75],[0,2]),([26,0,1,2,4,27],[11,15,28,55,60],[0,2]),u5 [26,29] [2,10,12,76,77],a5 [26,32] [3,12,72,78] [0,2,3,4],u5 [26,76] [2,12,14,28],a5 [76] [1,3,12,14,28,79] [0,1,2,3],a5 [26,34] [15,17,78,80] [2],a5 [136] [1,11,28,81,82] [0,1,3],u5 [79,30] [12,28],a5 [61,7] [1,3,15,83,84] [0,2],a5 [7,68] [15,17,85] [0,1,3],a5 [7,16] [83,86] [0,1,3],a5 [7,14] [11,83,87] [0,1,3],a5 [26,7] [1,2,3,12,15,78,83] [0,1,2,3,4],a5 [7,27] [1,15,83,88] [0,1,3,4],a5 [24,7] [1,2,3,83,89] [0,2],a5 [8] [1,2,3,11,12,17,90,91] [0,1,3,4],([0,1,10,3,4,30],[2,11,41,92],[0,1,2,3,4,5]),a5 [48,11] [10,15,93,94] [0,1,3],a5 [24] [1,3,11,12,15,83,89,95] [0,2,4],a5 [32,14] [28,72,74,96] [0,1,3],a5 [16] [11,15,17,83,86,97] [0,1,3],a5 [8,7] [1,15,17,90] [0,1,3],([26,0,1,10,3,4],[2,3,15,55,78],[0,1,2]),a5 [7,5] [1,11,15,62,83] [0,1,3],([0,1,10,11,3,4],[2,38,98],[0,1,2,3]),a5 [71,11] [11,99] [0,1,3],a5 [48] [3,10,11,94,100] [0,1,3],a5 [84,7] [1,11,83,101] [0,1,3,4],a5 [79] [1,3,10,12,17,28,102] [0,2],a5 [14] [2,15,17,87,103] [0,1,3,4,5],a5 [44] [1,2,3,15,104,105] [0,2,4],a5 [44,7] [1,3,11,104] [0,2],a5 [7,52] [1,2,15,83,106] [0,4,5],a5 [43,7] [1,3,17,28,107] [0,1,3,4],a5 [21,7] [1,3,15,57] [0,1,3],a5 [23,7] [1,2,3,11,81,83] [0,1,3,4],a5 [111] [1,3,11,15,28,108,109] [0,2],a5 [7,30] [1,2,83,92] [0,1,2,3,4],a5 [34] [11,17,21,78,80] [0,1,3]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_20_6 : checkNodesBT W_20 g_20 F_20 P_20_6 A_20 B_20_5 6 N_20_6 = true := by decide +kernel
def B_20_6 : BT (List (List Nat)) := buildBucketsBT W_20 N_20_6
set_option maxRecDepth 500000 in
lemma B_20_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_20 6 xs.toFinset) B_20_6 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok (buildPoolsSubBT_sound S_20_ok) A_20_ok B_20_5_ok C_20_6
def U_20_7 : List Nat := ([1,2,3,11,12,15,28,57,60,62,72,74,75,76,78,81,83,88,107]++r 109 9)
def P_20_7 : BT (Option BoundPool) := buildPoolsSubBT 7 W_20 r_20 S_20 ps_20 U_20_7
def N_20_7 : List NodeSpec := [a5 [21] [1,2,3,11,15,57,110,111] [0,1,2,3,4],a5 [43] [1,2,3,28,75,107,112] [0,1,3],a5 [27] [1,2,3,15,28,60,88,113] [0,1,3],a5 [5] [1,2,3,11,15,28,62,114,115] [0,1,2,3,4],a5 [23] [1,2,3,11,15,28,81,116] [0,2],a5 [26] [1,2,3,11,12,15,28,76,78] [0,2],a5 [91] [3,15,28,109,117] [0,1,3],a5 [32] [3,28,72,74] [0,1,3,5],a5 [7] [1,2,3,11,15,83] [0,1,3,4]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_20_7 : checkNodesBT W_20 g_20 F_20 P_20_7 A_20 B_20_6 7 N_20_7 = true := by decide +kernel
def B_20_7 : BT (List (List Nat)) := buildBucketsBT W_20 N_20_7
set_option maxRecDepth 500000 in
lemma B_20_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_20 7 xs.toFinset) B_20_7 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok (buildPoolsSubBT_sound S_20_ok) A_20_ok B_20_6_ok C_20_7
def U_20_8 : List Nat := [1,2,3]
def P_20_8 : BT (Option BoundPool) := buildPoolsSubBT 7 W_20 r_20 S_20 ps_20 U_20_8
def N_20_8 : List NodeSpec := [a5 [] [1,2,3] [0,1,2,3,4]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_20_8 : checkNodesBT W_20 g_20 F_20 P_20_8 A_20 B_20_7 8 N_20_8 = true := by decide +kernel
def B_20_8 : BT (List (List Nat)) := buildBucketsBT W_20 N_20_8
set_option maxRecDepth 500000 in
lemma B_20_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_20 8 xs.toFinset) B_20_8 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok (buildPoolsSubBT_sound S_20_ok) A_20_ok B_20_7_ok C_20_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_20_ok : forestRootCheck r_20 g_20 [(VAR 0,10,11),(VAR 1,9,11),(VAR 2,9,13),(VAR 3,3,11),(VAR 4,1,17)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_20_in : bucketContainsBT B_20_8 r_20 = true := by decide +kernel
lemma low_20 : Lower r_20 g_20 9 := lower_of_forestBT root_20_ok B_20_8_ok root_20_in
def g_21 := (d 0xfffefc80fffefc80)
def r_21 : List Nat := varsOf 31
def p_21 : List Nat := [7,7,7,10,10,11,11,12,12,13,13,14,17,17,18,18,19,20,20,21,22,24,24,25]
def q_21 : List Nat := [6,5,3,8,2,9,3,8,4,9,5,6,16,1,16,2,3,16,4,5,6,16,8,9]
def F_21 : Nat := fullMask 24
set_option maxHeartbeats 0 in
lemma gp_21 : goodPairs g_21 p_21 q_21 := goodPairs_of (by decide +kernel)
def W_21 : BT Decor := buildWiresBT 4 (mkBase p_21 q_21 r_21) [(1,1,2),(1,5,4),(3,3,6),(1,1,4),(3,2,8),(2,5,4),(1,2,4)]
lemma W_21_ok : btAll (fun x => faithful p_21 q_21 x ∧ x.1 < 2^256) W_21 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_21 : List (List (Nat × Nat)) := [[],[(1,2)]]
def A_21 : BT (List (Nat × Nat)) := btOfList 1 al_21
set_option maxHeartbeats 0 in
lemma A_21_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_21 = g_21) A_21 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_21_0 : Slice r_21 g_21 (identDom 0 2) 7 := by
  have hc : Lower (varsOf 27) (d 0xffeeee88ffeeee88) 7 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_ident (u := 0) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_1 : Slice r_21 g_21 (identDom 0 1) 7 := by
  have hc : Lower (varsOf 29) (d 0xfffafaa0fffafaa0) 7 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_ident (u := 0) (v := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_2 : Slice r_21 g_21 (subcubeFast 8 0) 6 := by
  have hc : Lower (varsOf 23) (d 0xfefe8080fefe8080) 6 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_3 : Slice r_21 g_21 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) (d 0xfffffcc0fffffcc0) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_4 : Slice r_21 g_21 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) (d 0xfffaf000fffaf000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_5 : Slice r_21 g_21 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) (d 0xffeecc00ffeecc00) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_6 : Slice r_21 g_21 (subcubeFast 16 0) 5 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_3
set_option maxHeartbeats 0 in
lemma sl_21_7 : Slice r_21 g_21 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) (d 0xfffcfc00fffcfc00) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_14
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_8 : Slice r_21 g_21 (subcubeFast 16 1) 4 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 1) (by decide +kernel) hc
def S_21 : BT (Option (Nat × Nat)) := btOfList 4 [some (identDom 0 2,7),some (identDom 0 1,7),some (subcubeFast 8 0,6),some (subcubeFast 0 1,5),some (subcubeFast 2 0,5),some (subcubeFast 4 0,5),some (subcubeFast 16 0,5),some (subcubeFast 1 0,5),some (subcubeFast 16 1,4)]
lemma S_21_ok : btAll (fun o => ∀ p, o = some p → Slice r_21 g_21 p.1 p.2) S_21 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_21_0) (forall_cons (fun _ h => by cases h; exact sl_21_1) (forall_cons (fun _ h => by cases h; exact sl_21_2) (forall_cons (fun _ h => by cases h; exact sl_21_3) (forall_cons (fun _ h => by cases h; exact sl_21_4) (forall_cons (fun _ h => by cases h; exact sl_21_5) (forall_cons (fun _ h => by cases h; exact sl_21_6) (forall_cons (fun _ h => by cases h; exact sl_21_7) (forall_cons (fun _ h => by cases h; exact sl_21_8) (fun _ h => (List.not_mem_nil h).elim))))))))))
def ps_21 : BT (Option PoolSpec) := btOfList 4 [q 0 [],q 3 [],q 2 [],q 0 [4105],q 4 [],q 6 [],q 1 [16389],q 2 [16389],q 8 [],q 5 [],q 1 [8197],q 0 [8197],q 2 [8197],q 1 [],q 7 []]
def B_21_3 : BT (List (List Nat)) := BT.empty
lemma B_21_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_21 3 xs.toFinset) B_21_3 := .empty
def U_21_4 : List Nat := []
def P_21_4 : BT (Option BoundPool) := buildPoolsSubBT 4 W_21 r_21 S_21 ps_21 U_21_4
def N_21_4 : List NodeSpec := [([7,0,1,2,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_21_4 : checkNodesBT W_21 g_21 F_21 P_21_4 A_21 B_21_3 4 N_21_4 = true := by decide +kernel
def B_21_4 : BT (List (List Nat)) := buildBucketsBT W_21 N_21_4
set_option maxRecDepth 500000 in
lemma B_21_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_21 4 xs.toFinset) B_21_4 :=
  buildBucketsBT_sound (by decide) gp_21 W_21_ok (buildPoolsSubBT_sound S_21_ok) A_21_ok B_21_3_ok C_21_4
def U_21_5 : List Nat := (r 0 6)
def P_21_5 : BT (Option BoundPool) := buildPoolsSubBT 4 W_21 r_21 S_21 ps_21 U_21_5
def N_21_5 : List NodeSpec := [e5 [9] [],e5 [10] [],u5 [6] [0,1,2],([0,1,5,3,4,11],[3,4,5],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_21_5 : checkNodesBT W_21 g_21 F_21 P_21_5 A_21 B_21_4 5 N_21_5 = true := by decide +kernel
def B_21_5 : BT (List (List Nat)) := buildBucketsBT W_21 N_21_5
set_option maxRecDepth 500000 in
lemma B_21_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_21 5 xs.toFinset) B_21_5 :=
  buildBucketsBT_sound (by decide) gp_21 W_21_ok (buildPoolsSubBT_sound S_21_ok) A_21_ok B_21_4_ok C_21_5
def U_21_6 : List Nat := ([1]++r 4 9)
def P_21_6 : BT (Option BoundPool) := buildPoolsSubBT 4 W_21 r_21 S_21 ps_21 U_21_6
def N_21_6 : List NodeSpec := [a5 [8] ([1,4]++r 6 4) [0,1],a5 [5] ([1,4,5]++r 9 4) [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_21_6 : checkNodesBT W_21 g_21 F_21 P_21_6 A_21 B_21_5 6 N_21_6 = true := by decide +kernel
def B_21_6 : BT (List (List Nat)) := buildBucketsBT W_21 N_21_6
set_option maxRecDepth 500000 in
lemma B_21_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_21 6 xs.toFinset) B_21_6 :=
  buildBucketsBT_sound (by decide) gp_21 W_21_ok (buildPoolsSubBT_sound S_21_ok) A_21_ok B_21_5_ok C_21_6
def U_21_7 : List Nat := [0,1,2,4,5,9,13,14]
def P_21_7 : BT (Option BoundPool) := buildPoolsSubBT 4 W_21 r_21 S_21 ps_21 U_21_7
def N_21_7 : List NodeSpec := [a5 [] [0,1,2,4,5,9,13,14] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_21_7 : checkNodesBT W_21 g_21 F_21 P_21_7 A_21 B_21_6 7 N_21_7 = true := by decide +kernel
def B_21_7 : BT (List (List Nat)) := buildBucketsBT W_21 N_21_7
set_option maxRecDepth 500000 in
lemma B_21_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_21 7 xs.toFinset) B_21_7 :=
  buildBucketsBT_sound (by decide) gp_21 W_21_ok (buildPoolsSubBT_sound S_21_ok) A_21_ok B_21_6_ok C_21_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_21_ok : forestRootCheck r_21 g_21 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,2,10),(VAR 4,1,17)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_21_in : bucketContainsBT B_21_7 r_21 = true := by decide +kernel
lemma low_21 : Lower r_21 g_21 8 := lower_of_forestBT root_21_ok B_21_7_ok root_21_in
def g_22 := (d 0xfffafc80fffafc80)
def r_22 : List Nat := varsOf 31
def p_22 : List Nat := [7,7,7,10,10,11,11,12,12,13,13,14,17,17,19,19,20,20,21,22,22,24,24,25,26]
def q_22 : List Nat := [6,5,3,8,2,9,3,8,4,9,5,6,16,1,18,3,16,4,5,18,6,16,8,9,18]
def F_22 : Nat := fullMask 25
set_option maxHeartbeats 0 in
lemma gp_22 : goodPairs g_22 p_22 q_22 := goodPairs_of (by decide +kernel)
def W_22 : BT Decor := buildWiresBT 5 (mkBase p_22 q_22 r_22) [(1,2,3),(1,2,4),(1,3,4),(2,1,4),(3,8,5),(2,2,4),(1,10,3),(2,5,4),(1,5,4),(0,0,6),(2,2,3),(3,2,7),(1,1,4)]
lemma W_22_ok : btAll (fun x => faithful p_22 q_22 x ∧ x.1 < 2^256) W_22 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_22 : List (List (Nat × Nat)) := [[],[(0,1),(3,4)]]
def A_22 : BT (List (Nat × Nat)) := btOfList 1 al_22
set_option maxHeartbeats 0 in
lemma A_22_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_22 = g_22) A_22 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_22_0 : Slice r_22 g_22 (identDom 0 1) 7 := by
  have hc : Lower (varsOf 29) (d 0xfffafaa0fffafaa0) 7 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_ident (u := 0) (v := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_1 : Slice r_22 g_22 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) (d 0xfffffcc0fffffcc0) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_2 : Slice r_22 g_22 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) (d 0xfff0fc00fff0fc00) 5 := carry_of (swaps := [(0,4),(1,4),(2,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_3 : Slice r_22 g_22 (subcubeFast 16 0) 5 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_3
set_option maxHeartbeats 0 in
lemma sl_22_4 : Slice r_22 g_22 (subcubeFast 8 0) 5 := by
  have hc : Lower (varsOf 23) (d 0xfafa8080fafa8080) 5 := carry_of (swaps := [(0,1),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_5 : Slice r_22 g_22 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) (d 0xfffaffa0fffaffa0) 5 := carry_of (swaps := [(1,4),(2,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_6 : Slice r_22 g_22 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) (d 0xfffaf000fffaf000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_7 : Slice r_22 g_22 (subcubeFast 3 0) 4 := by
  have hc : Lower (varsOf 28) (d 0xfff0f000fff0f000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 3) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_8 : Slice r_22 g_22 (subcubeFast 16 1) 4 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_9 : Slice r_22 g_22 (subcubeFast 8 2) 4 := by
  have hc : Lower (varsOf 21) (d 0xfafaa0a0fafaa0a0) 4 := carry_of (swaps := [(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 8) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_10 : Slice r_22 g_22 (subcubeFast 4 0) 4 := by
  have hc : Lower (varsOf 27) (d 0xffaacc00ffaacc00) 4 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
def S_22 : BT (Option (Nat × Nat)) := btOfList 4 [some (identDom 0 1,7),some (subcubeFast 0 1,5),some (subcubeFast 1 0,5),some (subcubeFast 16 0,5),some (subcubeFast 8 0,5),some (subcubeFast 0 2,5),some (subcubeFast 2 0,5),some (subcubeFast 3 0,4),some (subcubeFast 16 1,4),some (subcubeFast 8 2,4),some (subcubeFast 4 0,4)]
lemma S_22_ok : btAll (fun o => ∀ p, o = some p → Slice r_22 g_22 p.1 p.2) S_22 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_22_0) (forall_cons (fun _ h => by cases h; exact sl_22_1) (forall_cons (fun _ h => by cases h; exact sl_22_2) (forall_cons (fun _ h => by cases h; exact sl_22_3) (forall_cons (fun _ h => by cases h; exact sl_22_4) (forall_cons (fun _ h => by cases h; exact sl_22_5) (forall_cons (fun _ h => by cases h; exact sl_22_6) (forall_cons (fun _ h => by cases h; exact sl_22_7) (forall_cons (fun _ h => by cases h; exact sl_22_8) (forall_cons (fun _ h => by cases h; exact sl_22_9) (forall_cons (fun _ h => by cases h; exact sl_22_10) (fun _ h => (List.not_mem_nil h).elim))))))))))))
def ps_22 : BT (Option PoolSpec) := btOfList 5 [q 3 [],q 4 [],q 6 [],q 5 [],q 2 [],q 1 [],q 3 [24576],q 4 [16390],q 8 [],q 10 [],q 9 [],q 5 [12297],q 0 [16390],q 2 [16390],q 1 [16390],q 7 [],q 1 [16394],q 2 [16389],q 1 [16389],q 0 []]
def B_22_3 : BT (List (List Nat)) := BT.empty
lemma B_22_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 3 xs.toFinset) B_22_3 := .empty
def U_22_4 : List Nat := [0,1]
def P_22_4 : BT (Option BoundPool) := buildPoolsSubBT 5 W_22 r_22 S_22 ps_22 U_22_4
def N_22_4 : List NodeSpec := [([0,1,5,6,7],[0,1],[]),([0,2,3,9,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_4 : checkNodesBT W_22 g_22 F_22 P_22_4 A_22 B_22_3 4 N_22_4 = true := by decide +kernel
def B_22_4 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_4
set_option maxRecDepth 500000 in
lemma B_22_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 4 xs.toFinset) B_22_4 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound S_22_ok) A_22_ok B_22_3_ok C_22_4
def U_22_5 : List Nat := (r 0 10)
def P_22_5 : BT (Option BoundPool) := buildPoolsSubBT 5 W_22 r_22 S_22 ps_22 U_22_5
def N_22_5 : List NodeSpec := [e5 [11] [2,3],e5 [12] [2,3],e5 [13] (r 2 4),([10,0,1,3,5,4],[1],[]),([14,1,2,3,4,6],[5,6],[]),([8,15,0,2,3,4],[7],[]),e5 [16] [],([0,1,2,3,6,7],[1,8,9],[0]),([0,1,3,5,4,6],[0,1],[0]),([8,0,2,3,5,4],[2,7],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_5 : checkNodesBT W_22 g_22 F_22 P_22_5 A_22 B_22_4 5 N_22_5 = true := by decide +kernel
def B_22_5 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_5
set_option maxRecDepth 500000 in
lemma B_22_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 5 xs.toFinset) B_22_5 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound S_22_ok) A_22_ok B_22_4_ok C_22_5
def U_22_6 : List Nat := (r 0 6++r 7 12)
def P_22_6 : BT (Option BoundPool) := buildPoolsSubBT 5 W_22 r_22 S_22 ps_22 U_22_6
def N_22_6 : List NodeSpec := [a5 [7] [1,8,9,10] [0,1],a5 [5] (r 0 6++[9,10,11]) [0,1],([8,0,2,3,4],([0,2,7,8]++r 12 4),[0]),a5 [10] (r 0 6++[8,9,16]) [0,1],([0,2,3,4,17],[8,10,17,18],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_6 : checkNodesBT W_22 g_22 F_22 P_22_6 A_22 B_22_5 6 N_22_6 = true := by decide +kernel
def B_22_6 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_6
set_option maxRecDepth 500000 in
lemma B_22_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 6 xs.toFinset) B_22_6 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound S_22_ok) A_22_ok B_22_5_ok C_22_6
def U_22_7 : List Nat := (r 0 6++[19])
def P_22_7 : BT (Option BoundPool) := buildPoolsSubBT 5 W_22 r_22 S_22 ps_22 U_22_7
def N_22_7 : List NodeSpec := [a5 [] (r 0 6++[19]) [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_7 : checkNodesBT W_22 g_22 F_22 P_22_7 A_22 B_22_6 7 N_22_7 = true := by decide +kernel
def B_22_7 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_7
set_option maxRecDepth 500000 in
lemma B_22_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 7 xs.toFinset) B_22_7 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound S_22_ok) A_22_ok B_22_6_ok C_22_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_22_ok : forestRootCheck r_22 g_22 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,2,10),(VAR 4,1,17)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_22_in : bucketContainsBT B_22_7 r_22 = true := by decide +kernel
lemma low_22 : Lower r_22 g_22 8 := lower_of_forestBT root_22_ok B_22_7_ok root_22_in
def g_23 := (d 0xfffef800fffef800)
def r_23 : List Nat := varsOf 31
def p_23 : List Nat := [11,11,11,12,12,13,13,14,14,15,17,17,18,18,19,20,20,21,22,23,24,24,25,26]
def q_23 : List Nat := [10,9,3,8,4,9,5,10,6,7,16,1,16,2,3,16,4,5,6,7,16,8,9,10]
def F_23 : Nat := fullMask 24
set_option maxHeartbeats 0 in
lemma gp_23 : goodPairs g_23 p_23 q_23 := goodPairs_of (by decide +kernel)
def W_23 : BT Decor := buildWiresBT 6 (mkBase p_23 q_23 r_23) [(0,3,4),(1,2,5),(1,0,6),(1,1,6),(1,3,4),(3,6,9),(3,5,9),(2,11,1),(3,2,9),(1,1,3),(1,14,4),(3,1,15),(1,0,3),(0,17,4),(1,2,18),(2,0,5),(1,1,5),(2,13,1),(2,13,0),(1,0,5),(0,0,9),(0,11,0),(2,0,6),(3,3,4),(1,28,0),(2,29,1),(2,3,4),(0,13,0),(3,0,3),(3,33,4),(3,1,4),(3,1,3),(1,36,4),(1,35,3),(1,33,1),(3,0,4),(1,40,3),(3,1,41),(1,1,18),(1,17,4),(3,2,44),(3,1,44),(3,2,38),(3,0,44),(0,14,4),(1,1,4),(1,31,0),(3,14,4),(2,17,4),(3,40,3),(1,0,4),(3,1,55),(0,3,55),(3,3,55)]
lemma W_23_ok : btAll (fun x => faithful p_23 q_23 x ∧ x.1 < 2^256) W_23 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_23 : List (List (Nat × Nat)) := [[],[(0,1)]]
def A_23 : BT (List (Nat × Nat)) := btOfList 1 al_23
set_option maxHeartbeats 0 in
lemma A_23_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_23 = g_23) A_23 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_23_0 : Slice r_23 g_23 (subcubeFast 4 0) 6 := by
  have hc : Lower (varsOf 27) (d 0xffee8800ffee8800) 6 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_1 : Slice r_23 g_23 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) (d 0xfffaf000fffaf000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_2 : Slice r_23 g_23 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) (d 0xfffcf000fffcf000) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_3 : Slice r_23 g_23 (subcubeFast 3 0) 4 := by
  have hc : Lower (varsOf 28) (d 0xfff0f000fff0f000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 3) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_4 : Slice r_23 g_23 (identDom 1 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xfefec8c8fefec8c8) 5 := carry_of (swaps := [(1,2),(3,4)]) (by decide +kernel) low_14
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_5 : Slice r_23 g_23 (identDom 0 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xfefea8a8fefea8a8) 5 := carry_of (swaps := [(0,2),(1,2),(3,4)]) (by decide +kernel) low_14
  exact slice_ident (u := 0) (v := 3) (by decide +kernel) hc
def S_23 : BT (Option (Nat × Nat)) := btOfList 3 [some (subcubeFast 4 0,6),some (subcubeFast 2 0,5),some (subcubeFast 1 0,5),some (subcubeFast 3 0,4),some (identDom 1 3,5),some (identDom 0 3,5)]
lemma S_23_ok : btAll (fun o => ∀ p, o = some p → Slice r_23 g_23 p.1 p.2) S_23 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_23_0) (forall_cons (fun _ h => by cases h; exact sl_23_1) (forall_cons (fun _ h => by cases h; exact sl_23_2) (forall_cons (fun _ h => by cases h; exact sl_23_3) (forall_cons (fun _ h => by cases h; exact sl_23_4) (forall_cons (fun _ h => by cases h; exact sl_23_5) (fun _ h => (List.not_mem_nil h).elim)))))))
def ps_23 : BT (Option PoolSpec) := btOfList 5 [q 0 [16396,16397,36887],q 0 [16396,16397],q 1 [],q 0 [16398,16399],q 2 [],q 0 [],q 3 [],q 0 [16397,36864],q 5 [],q 0 [16396,20485],q 0 [16397,36871],q 2 [16391],q 0 [12291,4229],q 0 [16396,20482],q 2 [12293],q 4 [],q 0 [16385,225287],q 2 [225287],q 0 [16399],q 0 [16398],q 0 [16397],q 0 [16396],q 0 [16391],q 0 [16385],q 0 [12295],q 1 [12289],q 0 [12289]]
def B_23_1 : BT (List (List Nat)) := BT.empty
lemma B_23_1_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 1 xs.toFinset) B_23_1 := .empty
def U_23_2 : List Nat := []
def P_23_2 : BT (Option BoundPool) := buildPoolsSubBT 5 W_23 r_23 S_23 ps_23 U_23_2
def N_23_2 : List NodeSpec := [([7,8,9],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_2 : checkNodesBT W_23 g_23 F_23 P_23_2 A_23 B_23_1 2 N_23_2 = true := by decide +kernel
def B_23_2 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_2
set_option maxRecDepth 500000 in
lemma B_23_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 2 xs.toFinset) B_23_2 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok (buildPoolsSubBT_sound S_23_ok) A_23_ok B_23_1_ok C_23_2
def U_23_3 : List Nat := []
def P_23_3 : BT (Option BoundPool) := buildPoolsSubBT 5 W_23 r_23 S_23 ps_23 U_23_3
def N_23_3 : List NodeSpec := [([10,11,0,1],[],[]),([12,11,0,2],[],[]),([11,13,0,1],[],[]),([11,16,0,2],[],[]),([11,0,1,2],[],[]),([0,1,19,9],[],[]),([20,11,1,2],[],[]),([0,21,6,9],[],[]),([22,23,3,4],[],[]),([2,24,21,9],[],[]),([11,0,2,21],[],[]),([11,0,1,6],[],[]),([20,1,6,9],[],[]),([11,25,1,2],[],[]),([3,7,8,4],[],[0]),([10,0,1,9],[],[]),([25,1,6,9],[],[]),([16,0,6,9],[],[]),([26,11,1,2],[],[]),([0,6,8,9],[],[0]),([27,1,6,9],[],[]),([0,1,6,9],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_3 : checkNodesBT W_23 g_23 F_23 P_23_3 A_23 B_23_2 3 N_23_3 = true := by decide +kernel
def B_23_3 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_3
set_option maxRecDepth 500000 in
lemma B_23_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 3 xs.toFinset) B_23_3 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok (buildPoolsSubBT_sound S_23_ok) A_23_ok B_23_2_ok C_23_3
def U_23_4 : List Nat := [0,1]
def P_23_4 : BT (Option BoundPool) := buildPoolsSubBT 5 W_23 r_23 S_23 ps_23 U_23_4
def N_23_4 : List NodeSpec := [([13,0,1,3,4],[],[]),([0,1,3,6,4],[],[0]),([22,13,0,3,4],[],[0]),([13,16,0,3,4],[],[]),([13,25,1,3,4],[],[]),([30,0,2,3,4],[],[]),([16,25,2,3,4],[],[]),([11,0,1,2,4],[],[]),([11,0,1,2,3],[],[]),([11,0,1,2],[0],[0,1]),([13,0,1,5,9],[],[0]),([16,0,2,5,9],[],[0]),([31,28,0,1,2],[],[0]),([32,13,1,3,4],[],[]),([25,1,2,5,9],[],[0]),([0,1,2,5,9],[],[0]),([0,1,5,6,9],[],[0,1]),([0,1,6,9],[1],[0,1]),([31,0,34,1,2],[],[]),([20,1,3,6,4],[],[0]),([35,0,2,3,37],[],[]),([28,11,0,1,2],[],[]),([0,1,3,6,9],[],[]),([36,0,2,38,4],[],[]),([0,39,2,4,9],[],[]),([28,0,1,3,6],[],[0]),([31,11,0,1,2],[],[]),([42,0,2,3,4],[],[]),([16,0,2,3,4],[],[]),([0,1,3,19,4],[],[0]),([11,0,1,2,5],[0],[0,1]),([0,2,3,43,4],[],[]),([45,0,1,3,4],[],[]),([0,1,2,18,9],[],[0]),([46,0,2,3,4],[],[]),([47,0,1,3,4],[],[]),([11,0,1,2,9],[0],[0,1]),([31,0,2,21,4],[],[]),([0,2,21,4,9],[],[]),([0,3,21,6,4],[],[0]),([16,48,2,3,4],[],[]),([20,2,3,21,4],[],[]),([31,0,39,2,4],[],[]),([0,2,5,21,9],[],[0]),([20,1,2,5,9],[],[0]),([2,3,24,21,4],[],[0]),([0,3,6,8,4],[],[0]),([0,2,3,49,50],[],[]),([31,0,1,6,4],[],[0]),([27,1,3,6,4],[],[0]),([0,1,6,4,9],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_4 : checkNodesBT W_23 g_23 F_23 P_23_4 A_23 B_23_3 4 N_23_4 = true := by decide +kernel
def B_23_4 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_4
set_option maxRecDepth 500000 in
lemma B_23_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 4 xs.toFinset) B_23_4 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok (buildPoolsSubBT_sound S_23_ok) A_23_ok B_23_3_ok C_23_4
def U_23_5 : List Nat := (r 1 17)
def P_23_5 : BT (Option BoundPool) := buildPoolsSubBT 5 W_23 r_23 S_23 ps_23 U_23_5
def N_23_5 : List NodeSpec := [u5 [29] [2],([31,28,0,1,2,4],[],[0]),([31,28,0,1,2],[3],[0]),a5 [9] [2,4,5] [0,1],e5 [51] [],e5 [16] [],([13,0,1,3,4],[],[0,1]),([25,1,2,3,4,9],[6,7],[0,1]),([31,28,0,1,2,3],[],[0]),([0,1,2,5,3,9],[],[0]),u5 [28] [],([31,36,0,1,2,4],[2],[1]),a5 [18] [2,5,8] [0,1],([0,2,5,3,21,4],[2,9],[0]),([0,1,3,6,4],[],[0,1]),u5 [37] [],([36,0,1,2,4,9],[2],[1]),e5 [52] [],([28,0,1,2,4,9],[5],[0]),e5 [53] [],([16,0,2,3,4],[10],[]),e5 [54] [],([36,35,0,2,3,4],[11],[0]),a5 [44] [2,5] [0,1],a5 [38] [4,5] [0,1],([31,0,1,2,3,9],[5],[0]),([0,39,2,3,4],[12],[0]),([20,1,2,5,3,4],[6,8,13],[0]),([31,0,1,2,17,4],[4],[]),([16,0,2,3,4,9],[2,10],[0]),([35,0,2,3,4,50],[2,11],[]),([0,2,3,14,4,50],[14,15],[0]),e5 [24] [],u5 [34] [4],([31,0,1,2,5,4],[5],[0,1]),([0,1,2,17,4,9],[4],[0]),([56,0,2,3,4],[16],[]),([0,1,2,5,4,9],[],[0,1]),([0,2,3,21,4],[9],[0]),([56,0,2,3,4,55],[2,17],[]),u5 [5] [2,4,5,8,15],([0,1,2,5,9],[1],[0,1]),([0,1,5,3,6,4],[5],[0,1]),e5 [57] [8],e5 [58] [],u5 [31] [],([13,0,1,3,4,9],[5],[0,1]),([28,0,1,2,5,3],[5],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_5 : checkNodesBT W_23 g_23 F_23 P_23_5 A_23 B_23_4 5 N_23_5 = true := by decide +kernel
def B_23_5 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_5
set_option maxRecDepth 500000 in
lemma B_23_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 5 xs.toFinset) B_23_5 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok (buildPoolsSubBT_sound S_23_ok) A_23_ok B_23_4_ok C_23_5
def U_23_6 : List Nat := ([2,4,5,6,8,15]++r 18 9)
def P_23_6 : BT (Option BoundPool) := buildPoolsSubBT 5 W_23 r_23 S_23 ps_23 U_23_6
def N_23_6 : List NodeSpec := [a5 [28] [2,4,5,18] [0,1],a5 [31] [2,4,5,8,15,19] [0,1],a5 [9] [2,4,20] [0,1],a5 [5] [2,4,8,15,21] [0,1],a5 [35] [4,5,6,15,22] [0,1],a5 [55] [6,8,23] [0,1],a5 [36] [4,6,15,24] [0,1],a5 [17] [4,6,8,25,26] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_6 : checkNodesBT W_23 g_23 F_23 P_23_6 A_23 B_23_5 6 N_23_6 = true := by decide +kernel
def B_23_6 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_6
set_option maxRecDepth 500000 in
lemma B_23_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 6 xs.toFinset) B_23_6 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok (buildPoolsSubBT_sound S_23_ok) A_23_ok B_23_5_ok C_23_6
def U_23_7 : List Nat := [2,5,6]
def P_23_7 : BT (Option BoundPool) := buildPoolsSubBT 5 W_23 r_23 S_23 ps_23 U_23_7
def N_23_7 : List NodeSpec := [a5 [] [2,5,6] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_7 : checkNodesBT W_23 g_23 F_23 P_23_7 A_23 B_23_6 7 N_23_7 = true := by decide +kernel
def B_23_7 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_7
set_option maxRecDepth 500000 in
lemma B_23_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 7 xs.toFinset) B_23_7 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok (buildPoolsSubBT_sound S_23_ok) A_23_ok B_23_6_ok C_23_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_23_ok : forestRootCheck r_23 g_23 [(VAR 0,10,11),(VAR 1,9,11),(VAR 2,8,12),(VAR 3,3,11),(VAR 4,1,17)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_23_in : bucketContainsBT B_23_7 r_23 = true := by decide +kernel
lemma low_23 : Lower r_23 g_23 8 := lower_of_forestBT root_23_ok B_23_7_ok root_23_in
def g_24 := (d 0xfffffeecffe8e000)
def r_24 : List Nat := varsOf 63
def p_24 : List Nat := [13,13,13,14,14,14,15,15,19,19,19,21,21,21,22,22,22,23,24,24,25,25,26,26,27,28,28,34,34,35,35,37,37,37,38,38,39,41,41,41,42,42,43,44,44,44,48,48,49,49,50,52,52,56]
def q_24 : List Nat := [12,9,5,12,10,6,11,7,18,17,3,20,17,5,20,18,6,7,16,8,17,9,18,10,11,20,12,32,2,33,3,36,33,5,36,6,7,40,33,9,40,10,11,40,36,12,32,16,33,17,18,36,20,40]
def F_24 : Nat := fullMask 54
set_option maxHeartbeats 0 in
lemma gp_24 : goodPairs g_24 p_24 q_24 := goodPairs_of (by decide +kernel)
def W_24 : BT Decor := buildWiresBT 9 (mkBase p_24 q_24 r_24) [(0,4,5),(1,4,5),(3,6,7),(1,0,2),(3,8,3),(2,9,10),(0,8,2),(1,0,3),(3,12,13),(0,8,3),(3,15,9),(0,2,7),(3,17,13),(0,9,7),(0,19,3),(1,19,3),(3,20,21),(2,3,7),(3,23,9),(1,1,20),(0,3,7),(2,9,26),(1,3,4),(0,9,28),(0,29,5),(1,29,5),(3,30,31),(0,28,5),(2,9,33),(0,3,4),(3,35,28),(0,36,5),(3,37,9),(2,8,2),(3,39,7),(1,8,3),(3,2,41),(3,1,41),(3,0,41),(3,8,2),(1,8,2),(2,46,3),(1,2,3),(0,48,7),(2,28,5),(3,28,5),(1,51,35),(1,0,5),(0,36,53),(1,36,5),(3,0,55),(1,28,5),(3,26,57),(1,3,5),(0,4,59),(1,0,60),(0,3,5),(1,62,4),(0,9,57),(3,2,55),(0,2,5),(1,66,35),(1,2,5),(3,1,57),(2,19,3),(3,19,3),(1,2,59),(3,62,72),(0,2,59),(1,2,7),(3,6,75),(3,0,2),(0,9,63),(1,1,60),(2,36,5),(3,36,5),(0,13,7),(0,28,53),(3,2,28),(2,2,28),(1,85,35),(2,3,5),(3,87,28),(2,2,5),(3,89,28),(3,1,31),(0,8,9),(3,1,46),(3,17,75),(2,29,5),(3,29,5),(0,8,13),(2,8,3),(3,4,59),(2,4,59),(1,100,62),(1,1,30),(2,4,5),(1,103,3),(0,9,104),(3,62,57),(0,3,75),(3,6,57),(3,2,59),(2,2,59),(1,110,62),(0,2,4),(1,112,62),(1,2,4),(0,2,3),(1,115,6),(1,23,19),(3,3,7),(3,87,9),(1,23,6),(0,46,3),(0,28,68),(3,1,75),(3,3,75),(3,60,57),(0,8,48),(2,2,3),(3,127,7),(1,35,5),(0,2,129),(1,2,129),(3,130,131),(2,8,127),(0,2,28),(1,2,28),(3,134,135),(0,36,68),(3,89,36),(1,0,28),(0,2,139),(3,2,139),(1,87,19),(3,0,135),(1,36,0),(0,144,2),(2,144,2),(1,36,2),(3,0,147),(2,36,2),(3,36,2),(3,35,135),(1,3,6),(0,2,152),(1,2,152),(3,153,154),(3,1,55),(0,2,55),(3,0,57),(3,0,46),(0,2,57),(0,36,2),(3,2,57),(1,2,60),(3,35,57),(3,33,57),(3,74,72),(3,0,7),(0,36,9),(2,8,0),(3,0,75),(3,2,7),(2,2,7),(1,172,6),(0,2,41),(1,8,0),(1,0,7),(3,6,176),(3,4,5),(1,115,4),(1,179,5),(3,1,180),(1,0,4),(3,0,3),(1,87,4),(2,3,4),(3,3,4),(2,48,6),(2,9,5),(3,188,28),(3,0,5),(1,112,5),(0,13,191),(3,3,5),(3,193,7),(3,35,139),(2,9,3),(1,196,4),(3,0,4),(1,0,6),(3,35,68),(1,198,5),(1,186,5),(1,198,62),(0,9,202),(1,183,4),(1,205,5),(3,1,206),(3,2,4),(3,3,68),(1,127,167),(1,1,35),(3,2,3),(1,209,4),(3,0,28),(1,0,35),(1,208,62),(1,0,59),(3,62,217),(2,2,129),(3,2,129),(2,36,0),(0,2,63),(3,196,7),(1,134,5),(0,0,57),(3,2,63),(3,2,5),(1,1,6),(3,3,114),(1,229,5),(3,0,63),(2,2,60),(1,127,5),(0,28,233),(2,2,152),(3,2,152),(0,2,104),(1,0,152),(3,178,59),(3,0,202),(3,185,59),(1,185,5),(1,178,3),(1,190,4),(1,103,212),(3,4,53),(1,246,3),(3,3,53),(1,212,4),(2,249,5),(1,212,5),(3,4,251),(3,28,53),(2,2,35),(3,2,202),(3,127,53),(1,193,198),(3,198,59),(3,3,182),(1,259,5),(1,127,198),(1,127,6),(2,182,5),(1,263,3),(1,89,3),(1,265,4),(0,182,59),(1,183,5),(2,259,5),(1,66,4),(1,87,198),(3,115,182),(3,183,7),(2,2,6),(2,196,5),(1,112,3),(1,178,183),(2,265,4),(3,103,13),(1,178,127),(1,249,5),(2,13,4),(2,282,5),(3,185,53),(2,13,5),(1,198,3),(2,2,4),(1,287,3),(1,193,4),(3,4,268),(2,9,35),(3,62,182),(1,188,3),(1,66,3),(3,193,9),(3,186,53),(1,115,5),(3,4,233),(1,167,3),(3,3,201),(1,227,3),(1,287,5),(3,0,59),(1,198,66),(1,0,129),(3,112,13),(2,114,5),(3,2,104),(3,35,53),(3,35,5),(1,89,4),(3,115,53),(3,112,53),(1,188,4),(1,193,208),(1,183,66),(1,190,3),(2,205,5),(1,89,198),(1,87,112),(1,103,183),(2,196,4),(1,287,193),(1,196,5),(2,229,5),(1,89,183),(2,9,4),(1,327,5),(3,287,53),(3,0,179),(1,87,208),(1,282,5),(1,287,190),(2,327,5),(3,212,7),(1,307,3),(3,287,59),(1,198,115),(3,185,9),(3,3,270),(3,89,182),(3,3,311),(1,248,4),(3,66,13),(3,0,129),(3,87,182),(1,285,4),(1,89,186),(3,62,114),(3,3,191),(2,3,6),(1,287,183),(3,178,9),(3,127,182),(3,66,182),(1,190,112),(1,185,190),(2,9,6),(1,103,127),(3,193,182),(0,2,202),(0,9,59),(1,294,4),(3,103,9),(3,4,68),(1,365,3),(3,178,13),(3,287,13),(1,17,3),(1,286,5),(2,48,5),(2,286,5),(1,327,3),(3,3,244),(1,190,115),(3,28,68),(1,190,35),(3,0,152),(1,84,5),(1,371,4),(2,48,4),(1,193,112),(1,127,4),(1,186,190),(1,183,112),(2,179,5),(2,276,5),(3,4,297),(3,193,114),(1,317,4),(3,115,7),(1,103,115),(1,178,115),(1,127,190),(2,9,62),(2,381,5),(1,381,5),(3,103,48),(3,178,48),(2,317,4),(2,383,5),(1,171,3),(3,190,28),(3,227,28),(1,178,212),(1,276,5),(3,0,191),(0,3,191),(3,112,59),(3,89,13),(2,294,4),(0,114,59),(3,87,114),(1,288,5),(2,288,5),(3,3,302),(3,186,9),(1,185,66),(1,287,62),(1,87,287),(1,208,3),(1,421,5),(1,212,6),(2,421,5),(1,208,5),(3,3,425),(3,208,59),(2,13,6),(1,186,66),(3,185,68),(3,186,68),(1,301,4),(1,89,35),(1,89,185),(2,301,4),(3,0,270),(1,227,4),(3,3,437),(1,227,35),(1,183,6),(1,185,227),(1,186,227),(1,383,5),(3,66,28),(1,2,6),(1,2,35)]
lemma W_24_ok : btAll (fun x => faithful p_24 q_24 x ∧ x.1 < 2^256) W_24 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_24 : List (List (Nat × Nat)) := [[]]
def A_24 : BT (List (Nat × Nat)) := btOfList 1 al_24
set_option maxHeartbeats 0 in
lemma A_24_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_24 = g_24) A_24 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_24_0 : Slice r_24 g_24 (subcubeFast 2 0) 10 := by
  have hc : Lower (varsOf 61) (d 0xfffffaa0ffa0a000) 10 := carry_of (swaps := [(1,5),(2,5),(3,5)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_1 : Slice r_24 g_24 (subcubeFast 1 0) 9 := by
  have hc : Lower (varsOf 62) (d 0xfffffcccffc0c000) 9 := carry_of (swaps := [(0,5),(2,5),(3,5),(4,5)]) (by decide +kernel) low_10
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_2 : Slice r_24 g_24 (subcubeFast 0 1) 8 := by
  have hc : Lower (varsOf 62) (d 0xfffffffcfffcf000) 8 := carry_of (swaps := [(0,5),(1,5),(2,5),(3,5),(4,5)]) (by decide +kernel) low_11
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_3 : Slice r_24 g_24 (subcubeFast 0 4) 8 := by
  have hc : Lower (varsOf 59) (d 0xffffffeeffeeee00) 8 := carry_of (swaps := [(2,5),(3,5),(4,5)]) (by decide +kernel) low_12
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_4 : Slice r_24 g_24 (subcubeFast 16 0) 8 := by
  have hc : Lower (varsOf 47) (d 0xfeecfeece000e000) 8 := carry_of (swaps := [(4,5)]) (by decide +kernel) low_13
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_5 : Slice r_24 g_24 (subcubeFast 8 0) 8 := by
  have hc : Lower (varsOf 55) (d 0xffffecece8e80000) 8 := carry_of (swaps := [(1,2),(3,5),(4,5)]) (by decide +kernel) low_16
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_6 : Slice r_24 g_24 (subcubeFast 32 0) 8 := by
  exact slice_fast_direct_f (z := 32) (o := 0) (by decide +kernel) low_17
set_option maxHeartbeats 0 in
lemma sl_24_7 : Slice r_24 g_24 (subcubeFast 1 4) 7 := by
  have hc : Lower (varsOf 58) (d 0xffffffccffcccc00) 7 := carry_of (swaps := [(0,4),(1,4),(2,5),(3,4),(4,5)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 1) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_8 : Slice r_24 g_24 (subcubeFast 2 4) 7 := by
  have hc : Lower (varsOf 57) (d 0xffffffaaffaaaa00) 7 := carry_of (swaps := [(1,4),(2,5),(3,4),(4,5)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 2) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_9 : Slice r_24 g_24 (subcubeFast 18 0) 7 := by
  have hc : Lower (varsOf 45) (d 0xfaa0faa0a000a000) 7 := carry_of (swaps := [(1,4),(2,4),(3,4),(4,5)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 18) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_10 : Slice r_24 g_24 (subcubeFast 4 0) 8 := by
  have hc : Lower (varsOf 59) (d 0xffffeeccff880000) 8 := carry_of (swaps := [(2,5),(3,5),(4,5)]) (by decide +kernel) low_18
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_11 : Slice r_24 g_24 (identDom 0 5) 9 := by
  have hc : Lower (varsOf 31) (d 0xffeaeaa8ffeaeaa8) 9 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_19
  exact slice_ident (u := 0) (v := 5) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_12 : Slice r_24 g_24 (identDom 3 5) 9 := by
  have hc : Lower (varsOf 31) (d 0xffe8fe00ffe8fe00) 9 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_20
  exact slice_ident (u := 3) (v := 5) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_13 : Slice r_24 g_24 (identDom 2 3) 8 := by
  have hc : Lower (varsOf 55) (d 0xfffffcfcf8f8e0e0) 8 := carry_of (swaps := [(2,4),(3,5)]) (by decide +kernel) low_21
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_14 : Slice r_24 g_24 (identDom 0 3) 8 := by
  have hc : Lower (varsOf 55) (d 0xffffeeeeeaeaa0a0) 8 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,5),(4,5)]) (by decide +kernel) low_22
  exact slice_ident (u := 0) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_15 : Slice r_24 g_24 (identDom 2 4) 8 := by
  have hc : Lower (varsOf 47) (d 0xfefcfefcf0e0f0e0) 8 := carry_of (swaps := [(1,2),(2,4),(3,4),(4,5)]) (by decide +kernel) low_23
  exact slice_ident (u := 2) (v := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_16 : Slice r_24 g_24 (identDom 2 5) 8 := by
  have hc : Lower (varsOf 31) (d 0xfff8f0e0fff8f0e0) 8 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_23
  exact slice_ident (u := 2) (v := 5) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_17 : Slice r_24 g_24 (subcubeFast 17 4) 4 := by
  have hc : Lower (varsOf 42) (d 0xffccffcccc00cc00) 4 := carry_of (swaps := [(0,3),(1,3),(2,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 17) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_18 : Slice r_24 g_24 (subcubeFast 40 16) 4 := by
  exact slice_fast_direct_f (z := 40) (o := 16) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_24_19 : Slice r_24 g_24 (subcubeFast 18 32) 4 := by
  have hc : Lower (varsOf 13) (d 0xfaa0faa0faa0faa0) 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 18) (o := 32) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_20 : Slice r_24 g_24 (subcubeFast 18 8) 4 := by
  have hc : Lower (varsOf 37) (d 0xfafafafaa0a0a0a0) 4 := carry_of (swaps := [(1,3),(2,3),(3,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 18) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_21 : Slice r_24 g_24 (subcubeFast 34 4) 4 := by
  have hc : Lower (varsOf 25) (d 0xffaaaa00ffaaaa00) 4 := carry_of (swaps := [(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 34) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_22 : Slice r_24 g_24 (subcubeFast 10 4) 4 := by
  have hc : Lower (varsOf 49) (d 0xffffaaaaaaaa0000) 4 := carry_of (swaps := [(1,3),(2,4),(3,5),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 10) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_23 : Slice r_24 g_24 (subcubeFast 17 8) 4 := by
  have hc : Lower (varsOf 38) (d 0xfcfcfcfcc0c0c0c0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 17) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_24 : Slice r_24 g_24 (subcubeFast 33 4) 4 := by
  have hc : Lower (varsOf 26) (d 0xffcccc00ffcccc00) 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 33) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_25 : Slice r_24 g_24 (subcubeFast 9 4) 4 := by
  have hc : Lower (varsOf 50) (d 0xffffcccccccc0000) 4 := carry_of (swaps := [(0,3),(1,3),(2,4),(3,5),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 9) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_26 : Slice r_24 g_24 (subcubeFast 12 1) 4 := by
  have hc : Lower (varsOf 50) (d 0xffffcccccccc0000) 4 := carry_of (swaps := [(0,3),(1,3),(2,4),(3,5),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 12) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_27 : Slice r_24 g_24 (subcubeFast 33 2) 4 := by
  have hc : Lower (varsOf 28) (d 0xfff0f000fff0f000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 33) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_28 : Slice r_24 g_24 (subcubeFast 34 1) 4 := by
  have hc : Lower (varsOf 28) (d 0xfff0f000fff0f000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 34) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_24_29 : Slice r_24 g_24 (subcubeFast 18 1) 4 := by
  have hc : Lower (varsOf 44) (d 0xfff0fff0f000f000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 18) (o := 1) (by decide +kernel) hc
def S_24 : BT (Option (Nat × Nat)) := btOfList 5 [some (subcubeFast 2 0,10),some (subcubeFast 1 0,9),some (subcubeFast 0 1,8),some (subcubeFast 0 4,8),some (subcubeFast 16 0,8),some (subcubeFast 8 0,8),some (subcubeFast 32 0,8),some (subcubeFast 1 4,7),some (subcubeFast 2 4,7),some (subcubeFast 18 0,7),some (subcubeFast 4 0,8),some (identDom 0 5,9),some (identDom 3 5,9),some (identDom 2 3,8),some (identDom 0 3,8),some (identDom 2 4,8),some (identDom 2 5,8),some (subcubeFast 17 4,4),some (subcubeFast 40 16,4),some (subcubeFast 18 32,4),some (subcubeFast 18 8,4),some (subcubeFast 34 4,4),some (subcubeFast 10 4,4),some (subcubeFast 17 8,4),some (subcubeFast 33 4,4),some (subcubeFast 9 4,4),some (subcubeFast 12 1,4),some (subcubeFast 33 2,4),some (subcubeFast 34 1,4),some (subcubeFast 18 1,4)]
lemma S_24_ok : btAll (fun o => ∀ p, o = some p → Slice r_24 g_24 p.1 p.2) S_24 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_24_0) (forall_cons (fun _ h => by cases h; exact sl_24_1) (forall_cons (fun _ h => by cases h; exact sl_24_2) (forall_cons (fun _ h => by cases h; exact sl_24_3) (forall_cons (fun _ h => by cases h; exact sl_24_4) (forall_cons (fun _ h => by cases h; exact sl_24_5) (forall_cons (fun _ h => by cases h; exact sl_24_6) (forall_cons (fun _ h => by cases h; exact sl_24_7) (forall_cons (fun _ h => by cases h; exact sl_24_8) (forall_cons (fun _ h => by cases h; exact sl_24_9) (forall_cons (fun _ h => by cases h; exact sl_24_10) (forall_cons (fun _ h => by cases h; exact sl_24_11) (forall_cons (fun _ h => by cases h; exact sl_24_12) (forall_cons (fun _ h => by cases h; exact sl_24_13) (forall_cons (fun _ h => by cases h; exact sl_24_14) (forall_cons (fun _ h => by cases h; exact sl_24_15) (forall_cons (fun _ h => by cases h; exact sl_24_16) (forall_cons (fun _ h => by cases h; exact sl_24_17) (forall_cons (fun _ h => by cases h; exact sl_24_18) (forall_cons (fun _ h => by cases h; exact sl_24_19) (forall_cons (fun _ h => by cases h; exact sl_24_20) (forall_cons (fun _ h => by cases h; exact sl_24_21) (forall_cons (fun _ h => by cases h; exact sl_24_22) (forall_cons (fun _ h => by cases h; exact sl_24_23) (forall_cons (fun _ h => by cases h; exact sl_24_24) (forall_cons (fun _ h => by cases h; exact sl_24_25) (forall_cons (fun _ h => by cases h; exact sl_24_26) (forall_cons (fun _ h => by cases h; exact sl_24_27) (forall_cons (fun _ h => by cases h; exact sl_24_28) (forall_cons (fun _ h => by cases h; exact sl_24_29) (fun _ h => (List.not_mem_nil h).elim)))))))))))))))))))))))))))))))
set_option maxRecDepth 500000 in
def ps_24 : BT (Option PoolSpec) := btOfList 12 [q 1 [16397,114724,20596,20597,127099],q 3 [20496,20497,28699],q 10 [20496,20497,28699],q 1 [20496,20497,28699],q 2 [20496,20497,28699],q 0 [20496,20497,28699],q 0 [20496,20497,28699,8226,28831],q 5 [20496,20497,28699],q 18 [],q 1 [20496,20497,28699,12321,167947],q 7 [20496,20497,28699],q 0 [20496,20497,28699,12321,167947],q 5 [20496,20497,28699,167947],q 0 [20496,20497,28699,12321],q 5 [20496,20497,28699,167943],q 1 [20496,20497,28699,12321,167943],q 19 [],q 23 [],q 0 [20496,20497,28699,12321,167939],q 1 [20496,20497,28699,8226,8227],q 15 [],q 0 [20496,20497,28699,8226,8227],q 1 [20496,20497,28699,12320,12321],q 12 [],q 12 [20496,20497,28699],q 0 [20496,20497,28699,12320,12321],q 0 [20496,20497,28699,8225,12474],q 1 [20496,20497,28699,8225,12474],q 0 [12297,20496,20497,28864,28699],q 1 [16396,16397,20594,20595,143565],q 0 [16396,16397,20594,20595,143565],q 2 [16396,16397,114831],q 0 [16396,16397,114831],q 0 [20481,16396,16397,114831,217232],q 10 [16396,16397,114831],q 3 [16396,16397,114831],q 1 [16396,16397,114831,217232],q 6 [16396,16397,114831],q 0 [16396,16397,114831,20625,225283],q 1 [20497,28684,28685,233579],q 0 [20492,16633,20493,241680,245761],q 2 [20492,16633,20493],q 1 [20497,28684,28685,233508],q 1 [16396,16397,114831,20625,225291],q 7 [16396,16397,114831],q 0 [16396,16397,114831,20625,225291],q 6 [16396,16397,114831,225291],q 0 [20488,20489,16396,143625,16397],q 1 [20488,20489,16396,143625,16397],q 7 [16396,143625,16397],q 6 [16396,16397],q 1 [20492,20493,241672,241673,295163],q 7 [20492,20493],q 0 [20492,20493,241672,241673,295163],q 5 [241672,241673],q 7 [20496,20497],q 17 [],q 0 [20496,20497,28680,28681,307227],q 10 [20496,20497,307227],q 1 [16396,16397,114831,20592],q 1 [20492,16633,20493,241680,245765],q 9 [20492,20493],q 5 [],q 1 [16396,16397,114831,20626,20627],q 0 [16396,16397,114831,20626,20627],q 0 [12289,20496,20497,28724,28699],q 1 [20496,20497,28724,28699],q 1 [20496,20497,28686,28699],q 0 [20481,16396,16397,114831,217200],q 1 [16396,16397,114831,217200],q 1 [16396,16397,114698,143701,114699],q 3 [16396,16397,143701],q 10 [16396,16397],q 0 [16396,16397,114698,143701,114699],q 7 [16396,16397,143701],q 1 [16397,114724,20494,115039],q 4 [20490,115047],q 1 [16396,16397,114831],q 0 [20490,16396,16397,115047,114831],q 6 [16396,16397,115047,114831],q 1 [16397,114724,20597,126983],q 0 [8193,20496,20497,28699,36896],q 1 [20496,20497,28699,36896],q 20 [],q 0 [20496,20497,28699,8225],q 8 [20496,20497,28699],q 1 [20496,20497,28699,8225,188423],q 1 [20496,20497,28680,28681,307271],q 0 [20496,20497,28680,28681,307271],q 2 [20493,20497,28684],q 1 [16397,114724,20598,20599],q 0 [12289,20496,20497,28699,53280],q 1 [20496,20497,28699,53280],q 1 [20496,20497,28699,12322,12323],q 0 [20496,20497,28699,12322,12323],q 1 [20492,20493,241682,254353,241683],q 0 [20492,20493,241682,254353,241683],q 1 [16397,114724,20596,122885],q 1 [20494,20498,12701,426020],q 1 [20492,20493,241680,241681,233723],q 0 [20492,20493,241680,241681,233723],q 1 [20496,20497,28680,28699],q 1 [20488,20489,16396,16397,114831],q 0 [20488,20489,16396,16397,114831],q 16 [16396,16397,114831],q 1 [20496,20497,28681,307212,28699],q 0 [20496,20497,28681,307212,28699],q 0 [20496,20497,28684,28685,233499],q 1 [20496,20497,28684,28685,233499],q 1 [20492,20493,241674,254393,241675],q 3 [20492,20493,254393],q 0 [20492,20493,241674,254393,241675],q 7 [20492,20493,254393],q 0 [16392,16393,20492,254401,20493],q 1 [16392,16393,20492,254401,20493],q 7 [20492,254401,20493],q 4 [20492,20493],q 12 [16392,16393,254401],q 0 [12296,12297,20496,25037,20497],q 1 [12296,12297,20496,25037,20497],q 3 [20496,25037,20497],q 7 [20496,25037,20497],q 13 [20496,25037,20497],q 1 [],q 10 [],q 1 [20496,20497,28686,24669,28687],q 0 [20496,20497,28686,24669,28687],q 1 [20496,20497,28699,8225,12472],q 0 [20496,20497,28699,8225,12472],q 1 [16397,114724,20596,20597],q 0 [20489,16396,16397,114831,278640],q 6 [16396,16397,114831,278640],q 1 [16396,16397,114831,20594],q 0 [20496,20497,28681,28699],q 1 [20496,20497,28681,307207,28699],q 1 [16396,16397,114831,20624,20625],q 12 [16396,16397,114831],q 0 [16396,16397,114831,20624,20625],q 1 [20496,20497,28684,28699],q 0 [8193,16396,16397,114724,114831],q 1 [16396,16397,114724,114831],q 0 [8193,20496,20497,28708,28699],q 1 [20496,20497,28708,28699],q 0 [20496,20497,28681,307215,28699],q 1 [20496,20497,28681,307215,28699],q 1 [20496,20497,28686,24669],q 0 [20492,20493,241680,241681,233715],q 1 [20492,20493,241680,241681,233715],q 0 [12297,20496,20497,28699,196640],q 4 [12298,29183],q 0 [12298,20496,20497,29183,28699],q 5 [20496,20497,29183,28699],q 1 [16396,20621,528392,528393,537099],q 7 [16396,20621],q 0 [16396,20621,528392,528393,537099],q 5 [528392,528393,537099],q 4 [528392,528393,537099],q 10 [20496,20497,28684,28699],q 0 [12298,20496,20497,28699,520226],q 0 [20496,20497,28685,28699],q 1 [20496,20497,28685,233479,28699],q 1 [16396,16397,114696,114697,553499],q 7 [16396,16397],q 0 [16396,16397,114696,114697,553499],q 4 [114696,114697,553499],q 0 [20489,16396,16397,114831,278672],q 0 [20490,16396,16397,114831,147815],q 1 [12296,12297,20496,20497,28699],q 0 [12296,12297,20496,20497,28699],q 13 [20496,20497,28699],q 1 [16396,16397,569352,114831],q 0 [16396,16397,114689,569352,114831],q 1 [16396,16397,569355,114831],q 0 [16396,16397,114689,569355,114831],q 2 [],q 0 [16396,16397,114697,552963,114831],q 1 [16396,16397,114831,8768],q 0 [16396,16397,114831,145,8768],q 1 [16396,16397,114831,8770],q 0 [16396,16397,114831,145,8770],q 0 [16396,16397,114831,8337,602115],q 1 [16396,16397,114831,8338,8339],q 13 [],q 0 [16396,16397,114831,8338,8339],q 0 [16396,16397,114696,114697,553103],q 10 [16396,16397,553103],q 1 [20496,24589,622600,622601,631399],q 7 [20496,24589],q 0 [20496,24589,622600,622601,631399],q 4 [622600,622601,631399],q 6 [622600,622601,631399],q 1 [20496,20497,28699,8224,8225],q 0 [20496,20497,28699,8224,8225],q 0 [16396,16397,114831,20625],q 6 [16396,16397,114831,225287],q 1 [16396,16397,114831,20625,225287],q 1 [16396,16397,114831,20625,225288],q 0 [16396,16397,114831,20625,225288],q 0 [16396,16397,114831,20593,233475],q 0 [16396,16397,114831,20593],q 1 [16396,16397,114831,20593,233479],q 0 [20496,20497,28699,8225,188419],q 10 [20496,20497,28699,12320],q 1 [16396,16397,114831,20593,233480],q 0 [16396,16397,114831,20593,233480],q 1 [16396,16397,114831,8336,8337],q 0 [16396,16397,114831,8336,8337],q 1 [16396,16397,114831,20593,233483],q 0 [16396,16397,114831,20593,233483],q 6 [16396,16397,114831,233483],q 4 [20593,233483],q 0 [20492,16633,20493,241680,245769],q 1 [20492,16633,20493,241680,245769],q 3 [20492,16633,20493],q 7 [20492,16633,20493],q 12 [16633,241680,245769],q 0 [16396,16397,20592,20593,233615],q 1 [16396,16397,20592,20593,233615],q 1 [16396,16397,20592,20593,233607],q 0 [16396,16397,20592,20593,233607],q 1 [20492,20493,241672,241673,295211],q 0 [20492,20493,241672,241673,295211],q 5 [241672,241673,295211],q 1 [20496,20497,28684,28685,233579],q 0 [20496,20497,28684,28685,233579],q 0 [8193,16396,16397,114831,37008],q 1 [16396,16397,114831,37008],q 1 [20496,20497,28699,8224],q 0 [20496,20497,28681,307203,28699],q 1 [20496,20497,28682,25265,28683],q 3 [20496,20497,25265],q 10 [20496,20497],q 0 [20496,20497,28682,25265,28683],q 7 [20496,20497,25265],q 1 [20496,20497,28699,12321,167944],q 0 [20496,20497,28699,12321,167944],q 1 [20496,20497,28685,233480,28699],q 0 [20496,20497,28685,233480,28699],q 1 [20496,20497,28685,233483,28699],q 0 [20496,20497,28685,233483,28699],q 5 [20496,20497,233483,28699],q 4 [28685,233483],q 1 [16396,16397,114724,20592],q 2 [16396,16397],q 3 [16396,16397],q 0 [20496,20497,28685,233475,28699],q 0 [20497,28684,28685,233480],q 1 [20497,28684,28685,233480],q 10 [20497,28684],q 5 [20497,233480],q 0 [20497,28680,28685],q 1 [20497,28685,233479],q 2 [20497,28685,233479],q 5 [20497,233479],q 0 [20497,28680,28681,307212],q 1 [20497,28680,28681,307212],q 7 [20497],q 5 [20497,28680],q 6 [28680,28681,307212],q 4 [28680,28681,307212],q 1 [20497,28680,28681,307271],q 0 [20497,28680,28681,307271],q 0 [20496,20497,28699,8226],q 1 [20496,20497,28699,12323],q 0 [20496,20497,28699,12323],q 0 [20497,28683,28685],q 3 [20497,28685,233479],q 1 [20496,20497,28699,8226],q 1 [20496,20497,28699,8225],q 0 [20496,20497,28699,33],q 4 [28687],q 1 [20496,20497,28687,28699],q 0 [20496,20497,28687,28699],q 0 [20496,20497,28686,28699],q 5 [20496,20497],q 0 [20496,20497,28686,28687],q 1 [20496,20497,28686,28687],q 4 [],q 0 [20496,20497,28685,233499],q 1 [20496,20497,28685,233499],q 1 [20496,20497,28685,28699],q 0 [20496,20497,28699,34],q 1 [20496,20497,28685,233483],q 3 [20496,20497],q 0 [20496,20497,28685,233483],q 5 [20496,20497,233483],q 0 [20496,20497,28685,233480],q 1 [20496,20497,28685,233480],q 1 [20496,20497,28685,233479],q 0 [20496,20497,28685,233475],q 2 [20496,20497],q 4 [28685,233475],q 5 [20496,20497,233475],q 0 [20496,20497,28683,28699],q 1 [20496,20497,28683,28699],q 0 [20496,20497,28682,28699],q 4 [28682,28683],q 0 [20496,20497,28682,28683],q 1 [20496,20497,28682,28683],q 1 [20496,20497,28681,307215],q 0 [20496,20497,28681,307215],q 4 [28681,307215],q 0 [20496,20497,28681,307212],q 1 [20496,20497,28681,307212],q 4 [28681,307212],q 0 [20496,20497,28681,307203],q 4 [28681,307203],q 0 [20496,20497,28680,28699],q 4 [28680],q 0 [20496,20497,28675,28699],q 1 [20496,20497,28680],q 1 [20496,20497,720923],q 0 [20496,20497,28673,720923],q 4 [12296,12297],q 6 [12296,12297],q 0 [12296,12297,20498,20499],q 1 [12296,12297,20498,20499],q 5 [20498,20499],q 3 [20498,20499],q 13 [20498,20499],q 0 [12296,12297,20496,20497],q 1 [12296,12297,20496,20497],q 13 [20496,20497],q 0 [16396,16397,114689,569352],q 1 [16396,16397,569352],q 4 [114689,569352],q 1 [12296,16845,21197,737287],q 3 [16845,21197,737287],q 7 [16845,21197,737287],q 5 [21197,737287],q 1 [20492,20493,241681,233723],q 0 [20492,20493,241681,233723],q 0 [20481,16396,16397,114831],q 26 [],q 2 [16397,20594],q 6 [],q 5 [8193,114724],q 4 [8193,114724],q 1 [16397,114724,20594],q 6 [16397],q 4 [8195],q 1 [16397,20499,20594],q 0 [16385,20492,16633,20493],q 1 [20492,16633,20493],q 0 [16396,16397,114698,114831],q 1 [16397,20494,115039],q 5 [8193],q 3 [],q 2 [20497,28680],q 0 [12289,20496,20497,28699],q 0 [16397,20593,233475],q 1 [16397,20593,233479],q 2 [16397,20593,233479],q 1 [20497,28686,28687],q 4 [20489,278640],q 1 [16396,16397],q 1 [20489,16396,16397,278640],q 0 [20489,16396,16397,278640],q 6 [16396,16397,278640],q 0 [12291,20496,20497,28699],q 5 [20497],q 4 [8193,28708],q 0 [16396,16397,114831,8338],q 1 [16396,16397,114831,8338],q 0 [12296,20496,25037,20497],q 1 [12296,20496,25037,20497],q 1 [20496,20497,28686],q 0 [20492,20493,241674,254393],q 1 [20492,20493,241674,254393],q 5 [241674],q 10 [20492,20493],q 0 [8195,20496,20497,28699],q 1 [20494,16733,20498],q 7 [20493,20497,28684],q 1 [20493,20497,28684],q 2 [16397,20497],q 21 [],q 22 [],q 0 [20497,28675,28685],q 10 [20497,28685,233479],q 1 [16396,16397,114696,114831],q 0 [16396,16397,114696,114831],q 4 [114696],q 1 [16397,20497,20594],q 0 [16396,16397,114699,114831],q 1 [16396,16397,114699,114831],q 0 [20496,24589,622600,622601],q 1 [20496,24589,622600,622601],q 4 [622600,622601],q 10 [20496,24589],q 1 [16396,16397,20594],q 0 [20496,20497,28699,8224],q 0 [20488,20489,16396,143625],q 1 [20488,20489,16396,143625],q 5 [20488,20489],q 7 [16396,143625],q 4 [20488,20489],q 16 [],q 16 [16396,143625],q 0 [8193,20498,20893,28708],q 1 [20498,20893,28708],q 2 [20498,20893],q 3 [20498,20893],q 0 [16396,16397,114831,145],q 1 [12296,20496,20497,28699],q 0 [12296,20496,20497,28699],q 0 [20496,20497,28682,25265],q 1 [20496,20497,28682,25265],q 4 [114698,114699],q 0 [16396,16397,114698,114699],q 1 [16396,16397,114698,114699],q 1 [20496,20497,28699,12322],q 0 [20496,20497,28699,12322],q 0 [20496,20497,28686,24669],q 4 [28687,20594],q 12 [16397,28687],q 1 [16397,20497,28687,20594],q 0 [16397,20497,28687,20594],q 7 [],q 1 [16397,20592,114823],q 0 [12296,12297,20497,28864],q 1 [12296,12297,20497,28864],q 5 [20497,28864],q 6 [12296,12297,28864],q 4 [12296,12297,28864],q 1 [20497,28685,233508],q 2 [20497,28685],q 1 [20494,16733,20497],q 5 [8195],q 0 [20488,20489,16398,16399],q 1 [20488,20489,16398,16399],q 6 [16398,16399],q 3 [16398,16399],q 16 [16398,16399],q 0 [20490,16396,16397,115047],q 6 [16396,16397,115047],q 2 [20497,28684],q 1 [16396,16397,114697,114831],q 0 [16396,16397,114697,114831],q 1 [16397,114696,114697,553499],q 7 [16397],q 0 [16397,114696,114697,553499],q 10 [16397],q 1 [20497,28708],q 2 [20497],q 0 [8193,20497,28708],q 10 [20497,28708],q 3 [20497],q 1 [12296,12297,20496,24770],q 7 [20496],q 0 [12296,12297,20496,24770],q 13 [20496,24770],q 0 [8195,20492,16633,20493],q 6 [8193,28708],q 0 [20496,20497,28673,28699],q 0 [20481,16396,16397,217200],q 1 [16396,16397,217200],q 4 [20481,217200],q 1 [20492,16633,20493,241683],q 0 [20492,16633,20493,241683],q 7 [16397,20593,233479],q 0 [8193,20496,20497,28699],q 0 [20489,16396,16397,114831],q 1 [20489,16396,16397,114831],q 0 [12289,20496,20497,28724],q 1 [20496,20497,28724],q 4 [12289,28724],q 2 [20492,16633],q 1 [16396,16397,114831,8339],q 0 [16396,16397,114831,8339],q 1 [16396,16397,114831,20626],q 0 [16396,16397,114831,20626],q 1 [20488,16396,16397,114831],q 0 [20488,16396,16397,114831],q 1 [16397,114724,20497],q 0 [20483,16396,16397,114831],q 2 [16392,20929],q 0 [20492,20493,241680,245761],q 5 [241680,245761],q 2 [20492,20493],q 12 [241680,245761],q 2 [16397,20494],q 0 [8193,16397,114724,20494],q 1 [16397,114724,20494],q 1 [20497,28684,28685],q 2 [16397],q 1 [16397,114724,20599],q 4 [20594],q 0 [16396,16397,114831,20594],q 4 [8193],q 1 [20493,20497,241683],q 1 [16397,114724,20596],q 0 [8193,16397,114724],q 10 [16397,114724],q 0 [8193,16396,16397,114831],q 0 [16393,20492,16633,20493],q 1 [16393,20492,16633,20493],q 6 [8193,37215],q 0 [8193,20492,16633,20493],q 1 [20496,20497],q 4 [12297,28864],q 0 [20496,20497],q 0 [12297,20496,20497,28864],q 2 [20497,28686],q 1 [20495,20497,29447],q 6 [8193],q 1 [16396,16397,569487],q 0 [16396,16397,114689,569487],q 1 [12326,17169,16399],q 0 [8193,12326,17169,16399],q 3 [17169,16399],q 4 [8193,12326],q 1 [20496,20497,28699,12321],q 0 [20492,16633,20493,241680],q 1 [20492,16633,20493,241680],q 1 [20494,20498,12701],q 1 [20496,20497,28681,28699],q 1 [16397,20593,233480],q 2 [16397,20593,233480],q 0 [16397,20593,233480],q 0 [16397,20593,233480,234115],q 3 [16397,20593],q 10 [16397,20593],q 7 [16397,20593],q 1 [16396,16397,114831,8337],q 0 [16396,16397,114831,8337],q 0 [16387,20492,16633,20493],q 24 [],q 0 [8195,16396,16397,114831],q 12 [8193,12326],q 1 [12326,16396,20621],q 3 [16396,20621],q 1 [20497,28724],q 5 [20497,28724],q 0 [12296,12297,20496,24577],q 13 [20496,24577],q 2 [12296,12297],q 5 [20496,24577],q 3 [20496,24577],q 1 [16397,114724,20597],q 3 [16397],q 0 [20492,20493,241681,233475],q 5 [241681,233475],q 4 [20492,20493,233475],q 12 [241681,233475],q 6 [8195],q 1 [20488,20489,16396,278671],q 7 [16396],q 0 [20488,20489,16396,278671],q 16 [16396,278671],q 0 [16387,21273,12296,16845],q 1 [21273,12296,16845],q 5 [16387,21273],q 7 [21273,16845],q 2 [12296,16845],q 1 [16397,20593],q 0 [16397,114699,20593,233475],q 3 [16397,20593,233475],q 4 [20593,233475],q 5 [20593,233475],q 2 [16397,114699],q 1 [20492,20493,241681,233483],q 3 [20492,20493],q 0 [20492,20493,241681,233483],q 5 [241681,233483],q 12 [241681,233483],q 4 [20492,20493,233483],q 1 [20496,20497,28681,307207],q 8 [20496,20497],q 4 [28681,307207],q 0 [16396,16397,114831,20595],q 1 [16396,16397,114831,20595],q 1 [16396,16397,20592],q 0 [20492,20493,241682,241683],q 1 [20492,20493,241682,241683],q 2 [20497,28687],q 0 [16396,16397,20593,233615],q 1 [16396,16397,20593,233615],q 0 [8193,12326,16396,20621],q 1 [12326,16399,21225],q 0 [20490,16396,16397,114831],q 1 [20490,16396,16397,114831],q 0 [8193,16397,20593,233508],q 1 [16397,20593,233508],q 2 [16397,20593],q 0 [20496,20497,28681,307227],q 1 [16396,16397,569355],q 0 [16396,16397,114689,569355],q 4 [114689,569355],q 1 [20492,20493,241680,245765],q 5 [241680,245765],q 12 [241680,245765],q 1 [20496,20497,28684],q 10 [20496,20497,28684],q 4 [12298,28684],q 1 [12298,20497,29183],q 0 [16387,20492,254745,20493],q 1 [20492,254745,20493],q 0 [20496,20497,28680,28681],q 1 [20496,20497,28680,28681],q 4 [28680,28681],q 1 [16397,114724,20592],q 2 [16397,20592],q 0 [8193,16396,16397,114724],q 1 [16396,16397,114724],q 27 [],q 5 [20593,233479],q 0 [20497,28684,28685,233579],q 0 [16396,16397,114831,20624],q 1 [16396,16397,114831,20624],q 0 [20496,20497,28684,28685],q 1 [20496,20497,28684,28685],q 1 [16396,16397,114831,20625],q 1 [12297,20496,20497,28699],q 0 [12297,20496,20497,28699],q 0 [12296,12297,20496,25037],q 1 [12296,12297,20496,25037],q 3 [20496,25037],q 7 [20496,25037],q 13 [20496,25037],q 0 [8193,16398,17125,114724],q 1 [16398,17125,114724],q 2 [16398,17125],q 3 [16398,17125],q 1 [16397,114724,20598],q 0 [12298,20496,20497,29183],q 5 [20496,20497,29183],q 1 [17117,21301,843783],q 5 [21301,843783],q 1 [16395,20492,16633,20493],q 0 [16395,20492,16633,20493],q 1 [12298,20496,20497,28699],q 0 [12298,20496,20497,28699],q 1 [20489,16396,20621,278543],q 0 [20489,16396,20621,278543],q 4 [20489,278543],q 5 [20489],q 10 [16396,20621,278543],q 0 [16396,16397,114697,553103],q 1 [12298,20497,684541],q 1 [20488,20489,16396,143365],q 6 [16396,143365],q 7 [16396,143365],q 16 [16396,143365],q 0 [20488,20489,16396],q 0 [12299,20496,20497,28699],q 0 [16392,16393,20492,254401],q 1 [16392,16393,20492,254401],q 5 [16392,16393],q 7 [20492,254401],q 6 [16392,16393],q 0 [16396,16397,20595,143565],q 1 [16396,16397,20595,143565],q 0 [20496,20497,28699,12320],q 1 [20496,20497,28699,12320],q 0 [16392,16393,20492,20493],q 1 [16392,16393,20492,20493],q 15 [20492,20493],q 12 [16392,16393],q 0 [16392,20492,254401,20493],q 1 [16392,20492,254401,20493],q 3 [20492,254401,20493],q 5 [16392],q 1 [20489,16399,278543,17221],q 0 [20489,16399,278543,17221],q 3 [16399,17221],q 0 [16396,16397,114691,114831],q 0 [16396,16397,20593,233475],q 1 [16396,16397,20593,233479],q 0 [8193,20498,12701,426020],q 1 [20498,12701,426020],q 2 [20498,12701],q 3 [20498,12701],q 4 [8193,426020],q 0 [20488,20489,16396,143361],q 2 [20488,20489],q 16 [16396,143361],q 5 [241683,20594],q 0 [16397,20493,241683,20594],q 1 [16397,20493,241683,20594],q 0 [16395,20492,254785,20493],q 1 [16395,20492,254785,20493],q 0 [20492,20493,241681,233480],q 1 [20492,20493,241681,233480],q 5 [241681,233480],q 12 [241681,233480],q 0 [20488,20489,16396,16397],q 1 [20488,20489,16396,16397],q 16 [16396,16397],q 7 [20497,28685,233479],q 0 [20488,16396,143625,16397],q 1 [20488,16396,143625,16397],q 3 [16396,143625,16397],q 0 [20492,20493,241672,241673],q 1 [20492,20493,241672,241673],q 0 [20489,16398,17125,278640],q 6 [16398,17125,278640],q 1 [16396,16397,114831,20627],q 0 [16396,16397,114831,20627],q 1 [20492,20493,889083],q 0 [20492,20493,241665,889083],q 0 [16396,20621,528392,528393],q 1 [16396,20621,528392,528393],q 5 [528392,528393],q 4 [528392,528393],q 10 [16396,20621],q 0 [8193,20496,20497,28708],q 1 [20496,20497,28708],q 0 [16396,16397,114689,114831],q 0 [16396,16397,114696,114697],q 1 [16396,16397,114696,114697],q 4 [114696,114697],q 0 [16396,16397,114697,552963],q 4 [114697,552963],q 0 [16396,16397,114698,143701],q 1 [16396,16397,114698,143701],q 1 [20494,20497,28687],q 0 [16396,16397,114831,8336],q 1 [16396,16397,114831,8336],q 0 [16396,20621,528394,528395],q 1 [16396,20621,528394,528395],q 5 [528394,528395],q 4 [528394,528395],q 0 [16396,16397,114831,146],q 0 [16396,16397,114831,20592],q 0 [20496,20497,28684,28699],q 1 [16396,16397,114831,20593],q 0 [8193,20492,16633,258084],q 1 [20492,16633,258084],q 3 [20492,16633],q 6 [8193,258084],q 0 [16397,114699,20593],q 3 [16397,20593,233479],q 1 [16397,114699,20593,233479],q 1 [16397,20593,233480,233487],q 0 [16397,20593,233480,233487],q 0 [16396,16397,20592,20593],q 1 [16396,16397,20592,20593],q 0 [20492,16633,258056,20493],q 0 [16396,16397,20593,233480],q 1 [16396,16397,20593,233480],q 4 [20593,233480],q 1 [20492,20493,241673,295163],q 0 [20492,20493,241673,295163],q 5 [241673],q 1 [16396,16397,20593,233483],q 0 [16396,16397,20593,233483],q 0 [16396,16397,20594,20595],q 1 [16396,16397,20594,20595],q 2 [16397,114696,21017],q 0 [16397,114696,21017,20592],q 1 [16397,20493,20592],q 2 [16397,20493,20592],q 1 [16397,114696,20493,20592],q 0 [16397,20493,20592],q 0 [16397,114696,20493,20592],q 10 [16397,20493,20592],q 5 [20592],q 3 [16397,20493,20592],q 6 [16397,114696],q 4 [20493,20592],q 1 [16397,114696,20494,115039],q 0 [16397,114696,20494,115039],q 10 [16397,20494,115039],q 0 [16397,114696,20593],q 1 [16397,114696,20593,233479],q 6 [16397,233479],q 5 [20593],q 10 [16397,20593,233487],q 1 [16397,114696,20593,233487],q 0 [16397,114696,20593,233487],q 1 [16397,20493,241777,233479],q 1 [16397,20592,20593,233607],q 0 [16397,20592,20593,233607],q 0 [8193,16397,114724,20493],q 1 [16397,114724,20493],q 2 [16397,20493],q 0 [16397,20593,233472,233480],q 5 [20593,233472,233480],q 0 [16397,20593,233472],q 10 [16397,20593,233472],q 1 [20497,28685],q 0 [20497,28685,233475],q 0 [20497,28683,28685,233475],q 3 [20497,28685,233475],q 0 [16397,20593,233475,233480],q 6 [16397,233475,233480],q 0 [20492,20493,241682,254353],q 1 [20492,20493,241682,254353],q 2 [16397,20593,233483],q 0 [16397,20593,233475,233483],q 0 [20492,16633,20493],q 0 [20492,16633,258059,20493],q 10 [20492,16633,20493],q 1 [16397,20593,233479,233480],q 0 [16397,20593,233483],q 1 [16397,20593,233479,233483],q 5 [20593,233472,233479],q 0 [20491,16396,16397,114831],q 1 [12296,12297,20496,24581],q 5 [20496,24581],q 3 [20496,24581],q 7 [20496,24581],q 13 [20496,24581],q 10 [16397,20593,233479],q 1 [20496,20497,28699,8227],q 0 [20496,20497,28699,8227],q 6 [16397,233487,233491],q 0 [16397,20593,233487,233491],q 1 [16397,20593,233487,233491],q 1 [16393,466959,21397,20495],q 6 [16393,466959],q 0 [16393,466959,21397,20495],q 3 [21397,20495],q 0 [20492,16633,258051,20493],q 5 [241674,241675],q 0 [20492,20493,241674,241675],q 1 [20492,20493,241674,241675],q 0 [8193,16399,21225,827428],q 1 [16399,21225,827428],q 2 [16399,21225],q 3 [16399,21225],q 4 [8193,827428],q 0 [20492,20493,241680,245769],q 1 [20492,20493,241680,245769],q 5 [241680,245769],q 12 [241680,245769],q 1 [20492,20493,241680,245770],q 0 [20492,20493,241680,245770],q 5 [241680,245770],q 12 [241680,245770],q 0 [20492,20493,241680,241681],q 1 [20492,20493,241680,241681],q 5 [241680,241681],q 1 [20492,20493,241681,233479],q 5 [241681,233479],q 12 [241681,233479],q 1 [20493,241672,241673,295211],q 7 [20493],q 0 [20493,241672,241673,295211],q 10 [20493],q 0 [],q 0 [12298,20989,16397,954480],q 1 [20493,20497,241680,245765],q 9 [20493],q 0 [20493,241680,241681,233715],q 1 [20493,241680,241681,233715],q 3 [20496,24589],q 0 [20496,24589,622602,622603],q 1 [20496,24589,622602,622603],q 4 [622602,622603],q 6 [622602,622603],q 1 [20498,20893],q 0 [20498,20893],q 0 [20498,20893,28683],q 1 [20498,20893,28683],q 7 [20498,20893],q 4 [28683],q 1 [20498,20893,28680],q 0 [20498,20893,28680],q 1 [20498,12701],q 1 [20498,12701,425992],q 0 [20498,12701],q 0 [20498,12701,425992],q 1 [20497,28685,233483],q 0 [20497,28685,233483],q 0 [20497,28685,233480],q 1 [20497,28685,233480],q 10 [20497],q 1 [20497,28681,307215],q 0 [20497,28681,307215],q 0 [20497,28681,307212],q 1 [20497,28681,307212],q 1 [20497,28681,307207],q 8 [20497],q 1 [20497,28680],q 0 [20497,28685],q 10 [20497,28685],q 0 [20497,28680,28681],q 1 [20497,28680,28681],q 3 [20497,28675],q 10 [20497,28675],q 1 [20496,20497,28687],q 0 [20496,20497,28687],q 0 [20496,20497,28685],q 1 [20496,20497,28685],q 0 [20496,20497,28684],q 4 [28684],q 1 [20496,20497,28683],q 0 [20496,20497,28683],q 1 [20496,20497,28682],q 0 [20496,20497,28682],q 0 [20496,20497,28675],q 4 [28675],q 0 [20496,20497,28673],q 4 [28673],q 1 [20496,24589],q 1 [20496,24589,622603],q 2 [20496,24589],q 0 [20496,24589,622603],q 4 [622603],q 6 [622603],q 1 [20496,24589,622602],q 0 [20496,24589,622602],q 4 [622602],q 6 [622602],q 0 [20496,24589,622601],q 1 [20496,24589,622601],q 4 [622601],q 6 [622601],q 0 [20496,24589,622593],q 4 [622593],q 6 [622593],q 5 [20498],q 0 [20494,20498,12701],q 10 [20497,28687],q 0 [20494,20497,28687],q 0 [20494,16733,20497],q 4 [20493],q 0 [20493,241682,241683],q 1 [20493,241682,241683],q 1 [20493,241681,233483],q 3 [20493],q 0 [20493,241681,233483],q 4 [20493,233483],q 0 [20493,241681,233480],q 1 [20493,241681,233480],q 0 [20493,241681,233475],q 2 [20493],q 1 [20493,241680,245770],q 0 [20493,241680,245770],q 0 [20493,241680,245769],q 1 [20493,241680,245769],q 6 [241680,245769],q 1 [20493,241680,245765],q 6 [241680,245765],q 0 [20493,241680,245761],q 0 [20493,20499,242379],q 1 [20493,20499,242379],q 0 [20493,20498,241683],q 1 [20493,20498,241683],q 0 [20493,20498,20893],q 1 [20493,20498,20893],q 0 [20493,20497,241683],q 0 [20493,20497,241680],q 1 [20493,20497,241680],q 1 [20493,20497,28687],q 0 [20493,20497,28687],q 1 [20493,20497],q 2 [20493,20497],q 0 [20493,20497],q 0 [20493,20497,28683],q 3 [20493,20497],q 7 [20493,20497],q 0 [20493,20497,28675],q 10 [20493,20497],q 0 [20493,241672,241673],q 1 [20493,241672,241673],q 6 [241672,241673],q 1 [20492,20493],q 1 [20492,20493,241682],q 0 [20492,20493,241682],q 5 [241682],q 12 [241682],q 0 [20492,20493,241681],q 1 [20492,20493,241681],q 5 [241681],q 12 [241681],q 1 [20492,20493,241675],q 0 [20492,20493,241675],q 5 [241675],q 12 [241675],q 0 [20492,20493,241672],q 1 [20492,20493,241672],q 5 [241672],q 12 [241672],q 1 [20492,16633],q 0 [20492,16633],q 0 [20492,16633,258059],q 4 [20492],q 10 [20492,16633],q 7 [20492,16633],q 0 [20492,16633,258051],q 6 [258051],q 0 [16399,20493,241683],q 1 [16399,20493,241683],q 1 [16399,21225,20495],q 6 [16399],q 5 [21225],q 0 [16399,21225,20495],q 0 [16399,21225,20493],q 1 [16399,21225,20493],q 0 [16399,21225,827395],q 10 [16399,21225],q 1 [16399,21225],q 7 [16399,21225],q 0 [16398,20497,28687],q 1 [16398,20497,28687],q 5 [20499],q 0 [16398,20493,20499],q 1 [16398,20493,20499],q 1 [16398,20493,20497],q 0 [16398,20493,20497],q 0 [16398,20493,242407],q 1 [16398,20493,242407],q 6 [16398,242407],q 0 [16398,21221,20497],q 1 [16398,21221,20497],q 1 [16397,20593,233491],q 0 [16397,20593,233491],q 1 [16397,20593,233487],q 0 [16397,20593,233487],q 6 [16397,233475],q 0 [16397,20499,13001],q 1 [16397,20499,13001],q 0 [16397,20497,20594],q 1 [16397,20497,28687],q 0 [16397,20497,28687],q 0 [16397,20493,241777],q 1 [16397,20493,241777],q 1 [16397,20493,20594],q 0 [16397,20493,20594],q 1 [16397,20493,241683],q 0 [16397,20493,241683],q 0 [16397,20493,241680],q 1 [16397,20493,241680],q 6 [16397,241680],q 1 [17145],q 1 [17145,12298],q 0 [20483,17145],q 0 [20483,17145,12298],q 5 [20483,17145],q 3 [20483,17145],q 4 [20483],q 1 [12299,20498,868765],q 7 [20498],q 0 [12299,20498,868765],q 4 [12299],q 0 [20481,217107,13273],q 1 [217107,13273],q 5 [20481,217107],q 7 [217107,13273],q 1 [20497,217107],q 0 [20481,20497,217107],q 1 [16397,114696],q 2 [16397,114696],q 0 [16397,114696],q 0 [16397,114696,20595],q 10 [16397,20595],q 2 [16397,20595],q 1 [16397,20595],q 1 [16397,114696,20595],q 1 [20497],q 1 [217103,20497],q 0 [20497],q 0 [20481,217103,20497],q 7 [217103,20497],q 6 [217103],q 1 [12299,17233,21478],q 7 [21478],q 0 [12299,17233,21478],q 5 [21478],q 4 [12299,21478],q 5 [20481],q 4 [20481],q 0 [20481,16398,16399],q 1 [16398,16399],q 2 [16398,16399],q 7 [16398,16399],q 10 [16398,16399],q 2 [20493,20499],q 0 [20493,20499],q 0 [8193,20493,20499],q 1 [12299,21329,1028115],q 7 [1028115],q 0 [12299,21329,1028115],q 5 [1028115],q 1 [16397,217203],q 0 [20481,16397,217203],q 1 [16396,143370],q 0 [20481,16396,143370],q 6 [16396,143370],q 10 [20481],q 0 [16399,21225],q 0 [16399,21225,827403],q 1 [16399,21225,827403],q 0 [20481,16397,217200],q 1 [16397,217200],q 5 [20481,217200],q 7 [16397,217200],q 0 [12289,20497,28724],q 7 [20497,28724],q 25 [],q 6 [12289,28724],q 0 [20489,278543,17221],q 1 [20489,278543,17221],q 3 [17221],q 7 [17221],q 0 [16397,20494,20829],q 1 [16397,20494,20829],q 10 [20481,217107],q 1 [12298,217107],q 0 [20481,12298,217107],q 1 [12298,20497,28687],q 0 [12298,20497,28687],q 0 [20481,12298,217599],q 1 [12298,217599],q 5 [20481,217599],q 3 [20481,217599],q 2 [12298],q 7 [217599],q 6 [12298,217599],q 0 [8193,16398,17125],q 1 [16398,17125],q 6 [16398,17125],q 2 [20498],q 2 [20494],q 7 [20494],q 1 [20494,20498],q 0 [8193,16396,20621],q 1 [16396,20621],q 2 [16396,20621],q 1 [20495,811781],q 0 [16387,20495,811781],q 6 [16387],q 1 [20493,242459],q 0 [16387,20493,242459],q 0 [20496,20497,28680],q 0 [16387,20492,16633],q 5 [16387],q 0 [12297,20496,20497],q 1 [12297,20496,20497],q 4 [12297],q 0 [16385,745487,21517],q 1 [745487,21517],q 5 [16385,21517],q 7 [745487,21517],q 1 [12298,811517],q 0 [16387,12298,811517],q 5 [16387,811517],q 3 [16387,811517],q 4 [12298],q 7 [811517],q 0 [12298,20496,25085],q 1 [12298,20496,25085],q 3 [20496,25085],q 7 [20496,25085],q 6 [12298],q 13 [20496],q 1 [21273,20495],q 0 [16387,21273,20495],q 2 [20495],q 4 [20495],q 7 [21273,20495],q 0 [16387,21273,20493],q 1 [21273,20493],q 7 [21273,20493],q 0 [16385,21210,13341],q 1 [21210,13341],q 5 [16385,21210],q 7 [21210,13341],q 1 [20497,21210],q 0 [16385,20497,21210],q 0 [20490,12645,17445],q 1 [20490,12645,17445],q 3 [12645,17445],q 7 [12645,17445],q 0 [16385,20493,242392],q 1 [20493,242392],q 5 [16385,242392],q 7 [20493,242392],q 6 [16385,242392],q 0 [12291,21213,20497],q 1 [21213,20497],q 4 [12291,21213],q 7 [21213,20497],q 1 [745487,21518],q 0 [16385,745487,21518],q 0 [16385,20488,16649],q 1 [20488,16649],q 2 [20488,16649],q 7 [16649],q 6 [16385],q 0 [16385,20492,20493],q 5 [16385],q 12 [16385],q 1 [20488,20489],q 1 [20488,20489,16399],q 0 [20488,20489,16399],q 3 [16399],q 16 [16399],q 1 [20494,811357],q 0 [16387,20494,811357],q 1 [12296,745935],q 0 [16385,12296,745935],q 7 [745935],q 2 [12296],q 4 [12296,745935],q 1 [20497,29407],q 0 [12291,20497,29407],q 4 [20494],q 0 [20494,16733,20498],q 0 [12291,20496,20497],q 4 [12291],q 0 [8195,20496,24589],q 0 [20496,20497,28681],q 1 [20496,20497,28681],q 4 [28681],q 0 [12291,20496,24589],q 6 [12291],q 1 [16395,20492,16633],q 0 [16395,20492,16633],q 5 [16395],q 6 [16395],q 2 [20496,24586],q 10 [12291],q 0 [12291,20496,24586],q 1 [20496,24586],q 1 [16396,16397,114699],q 0 [16396,16397,114699],q 4 [114699],q 1 [12326,21266],q 0 [8193,12326,21266],q 3 [21266],q 0 [12291,16392,20929],q 3 [20929],q 7 [20929],q 6 [16392],q 0 [16396,16397],q 0 [16396,16397,20594],q 2 [16392,12737],q 0 [12291,16392,12737],q 7 [12737],q 0 [20492,20493,241665],q 5 [241665],q 12 [241665],q 1 [20499,750281],q 0 [12291,20499,750281],q 1 [20490,12645,17446],q 0 [20490,12645,17446],q 3 [12645,17446],q 7 [12645,17446],q 0 [20493,241680,241681],q 1 [20493,241680,241681],q 6 [241680,241681],q 2 [20495,20497],q 0 [8195,20495,20497],q 7 [20495,20497],q 0 [20483,16392,20929],q 1 [16397,20594],q 1 [12326,16396],q 0 [8193,12326,16396],q 3 [16396],q 0 [12291,17117,21301],q 1 [17117,21301],q 2 [21301],q 1 [12298,20497],q 0 [12289,20498,53663],q 1 [20498,53663],q 5 [20498,53663],q 7 [20498,53663],q 0 [16387,20492,20493],q 12 [16387],q 1 [12298,20499,520905],q 3 [20499,520905],q 7 [20499,520905],q 5 [20499,520905],q 0 [12299,17233,21477],q 1 [12299,17233,21477],q 3 [21477],q 5 [21477],q 7 [21477],q 3 [12289],q 10 [12289],q 0 [8195,16396,20621],q 0 [8193,16398,20493],q 2 [16398,20493],q 6 [16398],q 7 [16397,20594],q 0 [12289,20496,24589],q 4 [12289],q 6 [12289],q 1 [16397,20493,20499],q 0 [16397,20493,20499],q 1 [16438,21610],q 0 [12289,16438,21610],q 0 [20497,28681,307203],q 0 [20481,16398,217831],q 1 [16398,217831],q 2 [16398],q 4 [20481,217831],q 7 [16398,217831],q 1 [20493,20534],q 0 [12289,20493,20534],q 5 [20534],q 1 [12297],q 2 [12297],q 0 [12297],q 0 [12297,16397,20594],q 3 [16397,20594],q 1 [16396,143365],q 1 [20491,16396,143365],q 2 [16396,143365],q 3 [16396,143365],q 5 [20491],q 9 [20491],q 1 [16399,16438],q 0 [12289,16399,16438],q 1 [13081,20494],q 0 [16387,13081,20494],q 1 [16397,16438],q 0 [12289,16397,16438],q 2 [20493,241683],q 7 [20493,241683],q 0 [8195],q 0 [8195,20493,241683],q 0 [16397,20594,20595],q 1 [16397,20594,20595],q 0 [16394,13437,16397],q 1 [16394,13437,16397],q 3 [13437,16397],q 7 [13437,16397],q 0 [12289,16392,12737],q 1 [16392,12737],q 10 [20498],q 4 [20490],q 1 [16399,20495,17157],q 0 [16399,20495,17157],q 5 [17157],q 2 [20490],q 1 [21213,1097747],q 0 [12291,21213,1097747],q 0 [16397,20495,17157],q 1 [16397,20495,17157],q 1 [16396,143398],q 2 [16396],q 0 [8193,16396,143398],q 0 [12298,16399,21225],q 1 [12298,16399,21225],q 1 [20492,745723],q 0 [16385,20492,745723],q 2 [20492],q 0 [20492,20493,241680],q 1 [20492,20493,241680],q 5 [241680],q 12 [241680],q 1 [16397,20593,233495],q 0 [16397,20593,233495],q 0 [8193,20518,13041],q 1 [20518,13041],q 3 [13041],q 0 [12289,20496,24586],q 5 [20496,24586],q 1 [16397,20493],q 1 [16397,114696,20493],q 0 [16397,20493],q 0 [16397,114696,20493],q 10 [16397,20493],q 3 [16397,20493],q 0 [12289,20488,12553],q 1 [20488,12553],q 2 [20488,12553],q 7 [12553],q 0 [8193,20495,37639],q 1 [20495,37639],q 3 [20495],q 5 [8193,37639],q 1 [12296,12297],q 1 [12296,12297,20498],q 0 [12296,12297,20498],q 3 [20498],q 13 [20498],q 10 [12289,20534],q 1 [16394,20534],q 5 [16394],q 0 [12289,20495,20534],q 0 [20481,16399,217835],q 1 [16399,217835],q 5 [20481,217835],q 7 [16399,217835],q 5 [20490],q 1 [20490,16398,16399],q 0 [20490,16398,16399],q 0 [16397,20593],q 1 [16397,20593,233483],q 1 [21213,20499],q 0 [12291,21213,20499],q 0 [20481,12296,20941],q 1 [12296,20941],q 2 [12296,20941],q 3 [20481,20941],q 7 [20941],q 1 [12298,20989,954387],q 0 [12298,20989,954387],q 3 [20989,954387],q 7 [20989,954387],q 0 [20497,28675,12957],q 1 [20497,12957],q 7 [20497,12957],q 1 [16397],q 1 [20489,16397,278640],q 0 [20489,16397,278640],q 0 [16387,12296,16845],q 7 [16845],q 1 [21273,823311],q 0 [16387,21273,823311],q 6 [16387,823311],q 7 [21273,823311],q 0 [20491,13197,16397],q 1 [20491,13197,16397],q 0 [12289,16394,21629],q 1 [16394,21629],q 2 [16394,21629],q 7 [21629],q 0 [12289],q 0 [12289,16397,20594],q 11 [],q 10 [16397,20594],q 0 [8193,20494,20829],q 1 [20494,20829],q 2 [20494,20829],q 3 [20494,20829],q 0 [8195,20498,12701],q 7 [20498,12701],q 1 [17117],q 1 [17117,20490],q 0 [12291,17117],q 0 [12291,17117,20490],q 6 [12291,17117],q 3 [12291,17117],q 0 [16398,17125],q 0 [20490,16398,17125],q 10 [16398,17125],q 1 [20490],q 2 [20494,16733],q 0 [8195,20494,16733],q 1 [20494,16733],q 7 [20494,16733],q 0 [20492,20493,241667],q 12 [241667],q 0 [16387,20488,271129],q 1 [20488,271129],q 2 [20488],q 7 [271129],q 0 [16396,20621,528385],q 5 [528385],q 4 [528385],q 1 [12296,745487],q 0 [16385,12296,745487],q 1 [16392,53699],q 0 [12289,16392,53699],q 7 [53699],q 1 [16393,20497,20938],q 0 [16393,20497,20938],q 0 [16397,20592,20593],q 1 [16397,20592,20593],q 1 [20497,28687],q 0 [8193],q 0 [8193,20497,28687],q 3 [20497,28687],q 0 [20498,12701,425995],q 10 [20498,12701],q 1 [20498,12701,425995],q 1 [16396,217231],q 0 [20481,16396,217231],q 0 [16385,12296,16845],q 1 [12296,16845],q 0 [20489,16396,20621],q 1 [20489,16396,20621],q 4 [20489],q 1 [16396,20623],q 0 [8193,16396,20623],q 3 [16396,20623],q 2 [20499],q 7 [16398],q 0 [20490,16741,20497],q 1 [20490,16741,20497],q 3 [16741,20497],q 7 [16741,20497],q 1 [12296,217551],q 0 [20481,12296,217551],q 7 [217551],q 1 [16392,217539],q 0 [20481,16392,217539],q 7 [217539],q 0 [20481,20498,12701],q 3 [20481],q 6 [12701],q 14 [],q 1 [20494,20497],q 0 [8193,20518,17137],q 1 [20518,17137],q 3 [17137],q 4 [8193,20518],q 0 [16397,114697,552963],q 5 [114697,552963],q 1 [12296,12297,20499],q 0 [12296,12297,20499],q 3 [20499],q 13 [20499],q 0 [16393,20492,20493],q 1 [16393,20492,20493],q 5 [16393],q 12 [16393],q 1 [16395,20495,852741],q 7 [20495],q 0 [16395,20495,852741],q 5 [16395,852741],q 1 [20496,24581],q 2 [20496,24581],q 9 [8193],q 1 [20489,20493,278543],q 0 [20489,20493,278543],q 0 [16396,16397,114689],q 4 [114689],q 0 [12291,20488,271069],q 1 [20488,271069],q 7 [271069],q 5 [20488],q 0 [20483,13049,16397],q 1 [13049,16397],q 10 [20483,13049],q 1 [16392,20929,20495],q 0 [16392,20929,20495],q 0 [20497,28680],q 0 [20497,28680,28687],q 0 [8193,20496,24589],q 1 [17117,21302],q 0 [12291,17117,21302],q 1 [16397,20592],q 0 [8193,20496,20497],q 1 [20490,811365],q 0 [16387,20490,811365],q 6 [16387,811365],q 7 [811365],q 0 [20481,16398,17125],q 0 [20481,12296,16845],q 0 [16392,20494,459101],q 1 [16392,20494,459101],q 3 [20494,459101],q 7 [20494,459101],q 0 [8193,16397,20594],q 1 [20498,749981],q 0 [12291,20498,749981],q 0 [12291,20488,12553],q 1 [12326,17170],q 0 [8193,12326,17170],q 3 [17170],q 0 [20481,16396,16397],q 1 [16394,20495,791677],q 0 [16394,20495,791677],q 10 [20495],q 5 [16394,791677],q 6 [16394],q 1 [20492,20493,241674],q 0 [20492,20493,241674],q 12 [241674],q 0 [8193,12326,21265],q 1 [12326,21265],q 3 [21265],q 5 [8193,21265],q 0 [16392,16393,20493],q 1 [16392,16393,20493],q 15 [20493],q 1 [16392,16393],q 1 [16392,16393,20495],q 2 [16392,16393],q 0 [16392,16393,20495],q 15 [20495],q 1 [16393,466959,21398],q 7 [21398],q 0 [16393,466959,21398],q 0 [16387,20492,254745],q 1 [20492,254745],q 0 [8193,16398,16399],q 4 [20491],q 1 [20491,16398,16399],q 0 [20491,16398,16399],q 6 [28680],q 1 [20495,20497],q 0 [20495,20497],q 0 [20495,20497,28680],q 3 [20495,20497],q 6 [28675],q 0 [20495,20497,28675],q 10 [20495,20497],q 1 [20490,749925],q 0 [12291,20490,749925],q 6 [12291,749925],q 0 [8193,16422,21789],q 1 [16422,21789],q 3 [21789],q 4 [8193,21789],q 6 [8193,16422],q 0 [8193,20493,20497],q 0 [20481,16394,218239],q 1 [16394,218239],q 2 [16394],q 7 [218239],q 4 [20481,218239],q 6 [16394,218239],q 0 [12296,16845,733187],q 3 [16845],q 0 [8193,20492,20493],q 12 [8193],q 1 [16395,20494,852317],q 0 [16395,20494,852317],q 6 [8193,12326],q 1 [12326,20499],q 3 [16385,745487],q 0 [16385,12298,745487],q 4 [12298,745487],q 10 [16385,745487],q 6 [28683],q 0 [20495,20497,28683],q 1 [20498,20499],q 1 [12298,20498,20499],q 2 [20498,20499],q 10 [20498,20499],q 0 [12298,20498,20499],q 0 [8193,12326,17169],q 1 [12326,17169],q 3 [17169],q 0 [16397,20592,114823],q 0 [8193,20495,20497],q 1 [20490,12645],q 2 [20490,12645],q 0 [20490,12645,20497],q 0 [16397,114696,20594],q 1 [16397,114696,20594],q 0 [12289,16438,21609],q 1 [16438,21609],q 5 [16438,21609],q 7 [16438,21609],q 1 [16394,779389],q 0 [20483,16394,779389],q 4 [20483,779389],q 1 [16397,114724],q 0 [16387,20488,16649],q 4 [20488],q 1 [16422,21790],q 0 [8193,16422,21790],q 3 [21790],q 3 [20497,28685],q 2 [12298,20989],q 1 [12298,20989],q 0 [12298,20989],q 0 [16385,12298,20989],q 7 [20989],q 10 [16385],q 5 [20989],q 1 [20497,28683],q 2 [20497,28683],q 0 [20497,28683],q 0 [20497,28683,28687],q 0 [20496,20497,28686],q 4 [28686],q 5 [20496],q 0 [16387,21273,12296],q 1 [21273],q 1 [21273,12296],q 7 [21273],q 4 [12296],q 28 [],q 1 [16396,16397,114698],q 0 [16396,16397,114698],q 4 [114698],q 0 [16385,20492,16633],q 0 [12299,20497,29523],q 1 [12299,20497,29523],q 6 [12299,29523],q 4 [12299,29523],q 0 [16393,20938,13517],q 1 [16393,20938,13517],q 3 [13517],q 7 [13517],q 0 [16394,20493,242815],q 1 [16394,20493,242815],q 3 [20493,242815],q 7 [20493,242815],q 5 [16394,242815],q 6 [16394,242815],q 1 [16396,16397,20595],q 0 [16396,16397,20595],q 4 [20595],q 1 [12326,20494],q 0 [8193,12326,20494],q 3 [20494],q 0 [20483,13049,12296],q 1 [13049,12296],q 5 [20483],q 7 [13049],q 0 [12296,20496,20497],q 1 [12296,20496,20497],q 0 [20488,12553,16397],q 1 [20488,12553,16397],q 3 [12553,16397],q 7 [12553,16397],q 1 [20488,12553,16398],q 0 [20488,12553,16398],q 3 [12553,16398],q 7 [12553,16398],q 0 [16397,114689,569352],q 1 [16397,569352],q 5 [114689,569352],q 0 [12291,20498,20499],q 0 [8193,16397,20593],q 0 [20493,241674,241675],q 0 [12297,20498,20893],q 0 [16387,12296,471833],q 1 [12296,471833],q 7 [471833],q 2 [16399],q 0 [8193,12326,16399],q 1 [12326,16399],q 2 [20495,17157],q 0 [8195,20495,17157],q 1 [20495,17157],q 7 [20495,17157],q 1 [16398,20499,13001],q 0 [16398,20499,13001],q 0 [12289,20496,20497],q 0 [8195,16396,16397],q 0 [12289,20488,16649],q 1 [12298,20497,28684],q 0 [12298,20497,28684],q 0 [20493,20498,12701],q 1 [20493,20498,12701],q 4 [20593],q 1 [16397,114699,20593],q 1 [16397,114699],q 0 [8193,16398,37607],q 1 [16398,37607],q 3 [16398],q 4 [8193,37607],q 1 [20488,16649,1105935],q 0 [20488,16649,1105935],q 3 [16649,1105935],q 7 [16649,1105935],q 0 [8193,20494,16733],q 3 [20494,16733],q 0 [16385,20490,745831],q 1 [20490,745831],q 7 [745831],q 4 [20490,745831],q 6 [16385,745831],q 1 [20497,28686],q 1 [20490,16741,1273871],q 0 [20490,16741,1273871],q 3 [16741,1273871],q 7 [16741,1273871],q 0 [8193,16399,21225],q 0 [20489,16398,16399],q 1 [20489,16398,16399],q 0 [8193,20492,16633],q 5 [8193,20518],q 1 [20518,16398],q 0 [20481,217103,17377],q 1 [217103,17377],q 5 [20481,17377],q 7 [217103,17377],q 9 [],q 1 [20488,53515],q 0 [12289,20488,53515],q 7 [53515],q 5 [20488,53515],q 0 [8193,20499,13001],q 1 [20499,13001],q 2 [20499,13001],q 3 [20499,13001],q 0 [16396,143361],q 0 [20488,16396,143361],q 6 [16396,143361],q 10 [16396,143361],q 0 [16396,20621,528387],q 5 [528387],q 4 [528387],q 0 [20497,28684,28685],q 0 [16385,20494,745823],q 1 [20494,745823],q 4 [20494,745823],q 7 [20494,745823],q 0 [8195,16398,20493],q 7 [16398,20493],q 0 [12289,20534,17525],q 1 [20534,17525],q 5 [20534,17525],q 7 [20534,17525],q 7 [20499],q 0 [20492,20493,241673],q 1 [20492,20493,241673],q 12 [241673],q 1 [20490,16399,762213],q 0 [20490,16399,762213],q 3 [16399,762213],q 7 [16399,762213],q 6 [16396],q 5 [20497,233475],q 1 [16393,20492,467195],q 7 [20492],q 0 [16393,20492,467195],q 10 [20492,467195],q 6 [16393],q 1 [16396,20621,528394],q 0 [16396,20621,528394],q 5 [528394],q 4 [528394],q 1 [12326,20497],q 0 [8193,12326,20497],q 1 [12296,20497,28687],q 0 [12296,20497,28687],q 7 [20497,28687],q 1 [13049,12298],q 0 [20483,13049,12298],q 3 [20483,13049],q 1 [16392,20929,782351],q 3 [20929,782351],q 7 [20929,782351],q 6 [16392,782351],q 0 [20491,16396,143361],q 3 [16396,143361],q 2 [20491],q 1 [20496,24590],q 0 [8193,20496,24590],q 3 [20496,24590],q 10 [12289,16438],q 1 [20490,16438],q 0 [12289,20490,16438],q 1 [20489,16396,278671],q 0 [20489,16396,278671],q 10 [16396,278671],q 6 [16396,278671],q 1 [16394,750717],q 0 [12291,16394,750717],q 4 [12291,750717],q 3 [12291,750717],q 1 [12298,20496,24581],q 10 [20496,24581],q 9 [12298],q 0 [8193,20499,37579],q 1 [20499,37579],q 0 [12298,20989,16393],q 1 [12298,20989,16393],q 4 [12298,20989],q 0 [16385,12298,745983],q 1 [12298,745983],q 5 [16385,745983],q 3 [16385,745983],q 4 [12298,745983],q 7 [745983],q 0 [8193,16397,20493],q 1 [20488,745739],q 0 [16385,20488,745739],q 7 [745739],q 0 [8195,20493,20499],q 0 [20483,16392,459513],q 1 [16392,459513],q 2 [16392],q 7 [459513],q 1 [16397,20497],q 1 [20490,16397,115047],q 0 [20490,16397,115047],q 3 [16397,115047],q 0 [8193,20497],q 1 [16398,778981],q 0 [20483,16398,778981],q 1 [20496,24614],q 2 [20496],q 0 [8193,20496,24614],q 3 [20496],q 1 [12298,20498,520605],q 0 [12298,20498,520605],q 3 [20498,520605],q 7 [20498,520605],q 0 [16385,20495,746247],q 1 [20495,746247],q 5 [16385,746247],q 1 [16397,114696,20592],q 0 [16397,20592],q 0 [16397,114696,20592],q 10 [16397,20592],q 4 [20592],q 3 [16397,20592],q 6 [16397,233480],q 0 [8193,16396,16397],q 0 [20490,20497,28687],q 0 [8193,20498,12701],q 1 [16399,21225,827400],q 0 [16399,21225,827400],q 0 [16397,114691],q 0 [16397,114691,20594],q 10 [16397,114691],q 3 [16397,114691],q 5 [114691],q 4 [114691],q 0 [16392,12737,20493],q 1 [16392,12737,20493],q 3 [12737,20493],q 7 [12737,20493],q 0 [8193,20493,241700],q 1 [20493,241700],q 6 [8193,241700],q 0 [20490,20498,12701],q 0 [20488,12553,17561],q 1 [20488,12553,17561],q 3 [12553,17561],q 7 [12553,17561],q 0 [8193,20498,20499],q 0 [20481,20494,217103],q 0 [8193,20498,37279],q 1 [20498,37279],q 0 [8195,20492,16633],q 0 [12296,20496,25037],q 1 [12296,20496,25037],q 0 [20481,16392,20929],q 1 [16392,20929],q 1 [20497,28684],q 0 [16392,16393,20492],q 1 [16392,16393,20492],q 3 [20492],q 15 [20492],q 1 [20490,16741,20498],q 0 [20490,16741,20498],q 3 [16741,20498],q 7 [16741,20498],q 0 [16396,16397,114697],q 1 [16396,16397,114697],q 4 [114697],q 0 [20489,278547,13749],q 1 [20489,278547,13749],q 3 [13749],q 7 [13749],q 0 [16387,13081,20493],q 1 [13081,20493],q 6 [16387,13081],q 7 [13081,20493],q 0 [12289,20499,53963],q 1 [20499,53963],q 5 [20499,53963],q 7 [20499,53963],q 2 [16396,20623],q 0 [8195,16396,20623],q 0 [8195,16397,20593],q 0 [8195,16397,20494],q 7 [16397,20494],q 1 [16397,20494],q 1 [16393,16397,466959],q 0 [16393,16397,466959],q 4 [466959],q 7 [16397,20497],q 0 [8195,20496,20497],q 0 [12289,16394,54399],q 1 [16394,54399],q 5 [16394,54399],q 7 [54399],q 0 [8195,20498,20499],q 7 [20498,20499],q 0 [20483,16398,16399],q 0 [12289,16392,20929],q 0 [8193,20494,37215],q 1 [20494,37215],q 7 [16397,20592],q 1 [20493,217103],q 0 [20481,20493,217103],q 0 [16397,114696,114697],q 1 [16397,114696,114697],q 5 [114696,114697],q 0 [8195,16398,17125],q 7 [16398,17125],q 0 [8195,16398,16399],q 0 [20481,20498,217107],q 1 [20498,217107],q 1 [20497,28680,12357],q 0 [20497,28680,12357],q 3 [20497,12357],q 0 [8195,16399,21225],q 0 [16387,13081,21625],q 1 [13081,21625],q 2 [21625],q 5 [16387,21625],q 7 [13081,21625],q 1 [20518,16397],q 0 [16397],q 0 [8193,20518,16397],q 9 [12291],q 0 [8195,20494,20829],q 7 [20494,20829],q 9 [8195],q 0 [16392,20929,20493],q 1 [16392,20929,20493],q 3 [20929,20493],q 7 [20929,20493],q 0 [20481,16396,20621],q 0 [16396,16397,114691],q 2 [16398,21221],q 0 [8195,16398,21221],q 1 [16398,21221],q 7 [16398,21221],q 7 [20497,28685],q 0 [8195,20497],q 10 [20674],q 1 [12297,16394,20674],q 0 [12297,16394,20674],q 5 [16394,20674],q 4 [12297,20674],q 1 [20488,20489,16396],q 16 [16396],q 2 [20496,24590],q 0 [8195,20496,24590],q 7 [20497,28686],q 1 [13081,21626],q 0 [16387,13081,21626],q 5 [16387,21626],q 7 [13081,21626],q 1 [20489,16396,143365],q 9 [20489],q 10 [16396,143365],q 0 [8193,16422,13597],q 1 [16422,13597],q 3 [13597],q 1 [12326,20493],q 0 [8193,12326,20493],q 0 [16397,20494,115039],q 0 [8193,16398,21221],q 3 [16398,21221],q 4 [21221],q 1 [20488,16396,143365],q 9 [20488],q 1 [16397,745487],q 0 [16385,16397,745487],q 0 [8195,20498,20893],q 0 [8195,20499,13001],q 7 [20499,13001],q 0 [8193,20495,17157],q 3 [20495,17157],q 1 [13049,16398],q 0 [20483,13049,16398],q 1 [17145,999439],q 0 [20483,17145,999439],q 0 [20483,12296,471801],q 1 [12296,471801],q 7 [471801],q 0 [20483,12296,20941],q 0 [20489,16396,143361],q 2 [20489],q 1 [20489,16397,278643],q 0 [20489,16397,278643],q 0 [20483,16396,144121],q 1 [16396,144121],q 0 [20496,24589,622595],q 4 [622595],q 6 [622595],q 0 [20481],q 0 [20481,20497,28687],q 1 [16397,114699,20817],q 0 [16397,114699,20817],q 0 [8193,16397,20494],q 9 [20483],q 2 [16396,143370],q 10 [20483],q 0 [20483,16396,143370],q 0 [12297,20674,17869],q 1 [12297,20674,17869],q 3 [17869],q 7 [17869],q 0 [20483,16396,20621],q 0 [12297,20496,24589],q 1 [12297,20496,24589],q 6 [12297],q 0 [12298,20497,29183],q 0 [20496,24577],q 0 [12298,20496,24577],q 1 [12297,16397,16578],q 0 [12297,16397,16578],q 5 [16578],q 0 [16392,20495,459525],q 1 [16392,20495,459525],q 3 [20495,459525],q 7 [20495,459525],q 0 [20481,12298,16893],q 2 [12298,16893],q 1 [12298,16893],q 7 [16893],q 1 [16399,778985],q 0 [20483,16399,778985],q 1 [16393,466959,20495],q 0 [16393,466959,20495],q 4 [466959,20495],q 0 [20496,24589,622600],q 1 [20496,24589,622600],q 4 [622600],q 0 [12296,16845,20497],q 1 [12296,16845,20497],q 3 [16845,20497],q 7 [16845,20497],q 0 [12291,16392,459485],q 1 [16392,459485],q 7 [459485],q 1 [12296,16845,20498],q 0 [12296,16845,20498],q 3 [16845,20498],q 7 [16845,20498],q 0 [20483,16396,16397],q 0 [16397,114699],q 0 [16397,114699,20594],q 1 [16397,114699,20594],q 0 [20498,20893,28675],q 10 [20498,20893],q 0 [12296,16845,21197],q 1 [12296,16845,21197],q 3 [16845,21197],q 7 [16845,21197],q 5 [21197],q 1 [12296,16845,21198],q 0 [12296,16845,21198],q 3 [16845,21198],q 7 [16845,21198],q 0 [20497,28686,28687],q 1 [16392,12737,21586],q 3 [12737,21586],q 7 [12737,21586],q 5 [16392,21586],q 5 [20593,233483],q 1 [12296,20941,20499],q 6 [12296],q 0 [12296,20941,20499],q 3 [20941,20499],q 7 [20941,20499],q 6 [12299],q 1 [12299,20498,20499],q 0 [12299,20498,20499],q 1 [12296,20941,1216531],q 0 [12296,20941,1216531],q 3 [20941,1216531],q 7 [20941,1216531],q 0 [20495,20497,29447],q 0 [16393,20495,467719],q 1 [16393,20495,467719],q 0 [20483,13049,17653],q 1 [13049,17653],q 2 [17653],q 5 [20483,17653],q 7 [13049,17653],q 0 [12296,12297,20496],q 1 [12296,12297,20496],q 0 [12296,12297,20497],q 1 [12296,12297,20497],q 13 [20497],q 0 [12297,16399,16578],q 0 [12296,20496,24589],q 1 [12296,20496,24589],q 1 [16393,466959,20492],q 0 [16393,466959,20492],q 1 [12297,20493,20674],q 0 [12297,20493,20674],q 5 [20674],q 1 [12296,20497,29135],q 0 [12296,20497,29135],q 3 [20497,29135],q 7 [20497,29135],q 0 [12296,20498,471453],q 1 [12296,20498,471453],q 3 [20498,471453],q 7 [20498,471453],q 0 [12296,20498,20499],q 1 [12296,20498,20499],q 0 [12296,20499,471753],q 1 [12296,20499,471753],q 3 [20499,471753],q 7 [20499,471753],q 0 [12297,16397,20674],q 10 [16397,20674],q 0 [12297,16399,21225],q 1 [12298,778749],q 0 [20483,12298,778749],q 5 [20483,778749],q 3 [20483,778749],q 1 [12297,20495,20674],q 1 [20492,253990],q 0 [8193,20492,253990],q 1 [12297,16578,22006],q 7 [22006],q 0 [12297,16578,22006],q 5 [16578,22006],q 0 [12297,16578,22005],q 1 [12297,16578,22005],q 3 [22005],q 7 [22005],q 4 [12297,22005],q 5 [16578,22005],q 0 [16396,16397,20593],q 1 [16396,16397,20593],q 0 [16397,20499,20594],q 0 [12289,20490,16741],q 1 [20490,16741],q 2 [20490,16741],q 7 [16741],q 0 [12297,20496,24577],q 10 [20496,24577],q 0 [8195,20497,28687],q 1 [12297,20496,24581],q 9 [12297],q 1 [20492,20493,241683],q 0 [20492,20493,241683],q 12 [241683],q 1 [12297,20496,24770],q 0 [12297,20496,24770],q 10 [20496,24770],q 5 [20496,24770],q 0 [8195,16397,20493],q 7 [16397,20493],q 0 [12297,20497,28864],q 1 [12297,20497,28864],q 0 [20493,20497,28684],q 0 [12297,20498,197023],q 1 [12297,20498,197023],q 10 [20498,197023],q 5 [20498,197023],q 0 [20488,16396,143625],q 1 [20488,16396,143625],q 3 [16396,143625],q 0 [12297,20498,20499],q 1 [12297,20498,20499],q 0 [12297,20499,197323],q 1 [12297,20499,197323],q 10 [20499,197323],q 0 [16396,16397,114696],q 1 [16396,16397,114696],q 1 [12298,16893,16399],q 5 [16893],q 0 [12298,16893,16399],q 3 [16893,16399],q 7 [16893,16399],q 1 [13049,17654],q 0 [20483,13049,17654],q 1 [12298],q 0 [12298],q 0 [12298,16397,20594],q 1 [16397,20534],q 0 [12289,16397,20534],q 7 [16397,20534],q 1 [12298,16893,22014],q 0 [12298,16893,22014],q 3 [16893,22014],q 7 [16893,22014],q 0 [12298,20989,16397],q 3 [20989,16397],q 0 [20492,16633,258056],q 0 [12298,20989,20493],q 1 [12298,20989,20493],q 3 [20989,20493],q 7 [20989,20493],q 1 [12298,20496,24589],q 0 [12298,20496,24589],q 1 [20497,28683,12973],q 0 [20497,28683,12973],q 5 [20497,28683],q 1 [12298,20496,20497],q 0 [12298,20496,20497],q 3 [20497,29183],q 7 [20497,29183],q 5 [20497,29183],q 1 [12298,20989,20495],q 0 [12298,20498,20893],q 5 [20498,20893],q 0 [8195,16397,20594],q 0 [12299,21329,20497],q 1 [12299,21329,20497],q 1 [16397,115451],q 0 [20483,16397,115451],q 0 [12299,20496,24577],q 2 [12299],q 1 [12299,20496,24581],q 9 [12299],q 1 [12299,20496,24589],q 0 [12299,20496,24589],q 1 [20490,16396,20621],q 0 [20490,16396,20621],q 0 [20491,16397,115599],q 1 [20491,16397,115599],q 4 [20491,115599],q 5 [20491,115599],q 0 [12298,16893,16397],q 1 [12298,16893,16397],q 3 [16893,16397],q 7 [16893,16397],q 1 [12299,20496,20497],q 0 [12299,20496,20497],q 1 [12299,20499,869065],q 0 [12299,20499,869065],q 1 [16392,12737,20494],q 0 [16392,12737,20494],q 0 [16392,12737,21585],q 1 [16392,12737,21585],q 3 [12737,21585],q 7 [12737,21585],q 1 [12299,21329,20499],q 0 [12299,21329,20499],q 0 [16392,20492,254401],q 1 [16392,20492,254401],q 3 [20492,254401],q 9 [20481],q 0 [16392,20929,782339],q 5 [16392,20929],q 4 [782339],q 1 [16395,20492,20493],q 0 [16395,20492,20493],q 12 [16395],q 1 [16392,20929,782348],q 0 [16392,20929],q 0 [16392,20929,782351],q 4 [782351],q 10 [782351],q 0 [16392,20492,20493],q 1 [16392,20492,20493],q 12 [16392],q 1 [16392,16393,20494],q 0 [16392,16393,20494],q 15 [20494],q 0 [16398,17125,114699],q 1 [16398,17125,114699],q 1 [16392,20493,242115],q 0 [16392,20493,242115],q 3 [20493,242115],q 7 [20493,242115],q 0 [16393,20490,12645],q 1 [16393,20490,12645],q 7 [12645],q 4 [20490,12645],q 0 [12289,20490,53607],q 1 [20490,53607],q 5 [20490,53607],q 3 [12289,53607],q 7 [53607],q 6 [12289,53607],q 0 [12289,16399,21225],q 0 [16393,16398,466959],q 10 [16398,466959],q 0 [16393,466959,21397],q 1 [16393,466959,21397],q 3 [21397],q 7 [21397],q 4 [466959,21397],q 1 [20491,16396,16397],q 0 [20491,16396,16397],q 0 [16393,20492,16633],q 1 [16393,20492,16633],q 0 [8195,16396],q 1 [20488,12553,17562],q 0 [20488,12553,17562],q 3 [12553,17562],q 7 [12553,17562],q 0 [20489,16396,16397],q 1 [20489,16396,16397],q 0 [16393,20493,242120],q 1 [16393,20493,242120],q 0 [8193,20498,20893],q 0 [16393,20494,467295],q 1 [16393,20494,467295],q 0 [8195,20493,20497],q 0 [16393,20499,20938],q 1 [12296,20496,24581],q 9 [12296],q 7 [20497,28684],q 0 [16394,13437,21633],q 1 [16394,13437,21633],q 3 [13437,21633],q 7 [13437,21633],q 5 [16394,21633],q 10 [21633],q 6 [16394,13437],q 1 [16394,13437,21634],q 0 [16394,13437,21634],q 3 [13437,21634],q 7 [13437,21634],q 1 [16394,21629,1237007],q 0 [16394,21629,1237007],q 3 [21629,1237007],q 7 [21629,1237007],q 0 [16396,20621,528392],q 1 [16396,20621,528392],q 5 [528392],q 4 [528392],q 0 [8193,16399,37611],q 1 [16399,37611],q 0 [16394,21629,20497],q 1 [16394,21629,20497],q 3 [21629,20497],q 7 [21629,20497],q 0 [20488,16398,271077],q 1 [20488,16398,271077],q 3 [16398,271077],q 7 [16398,271077],q 1 [16394,21629,20499],q 4 [21629],q 0 [16394,21629,20499],q 0 [20488,16396,16397],q 1 [20488,16396,16397],q 10 [278543],q 1 [16394,20489,278543],q 0 [16394,20489,278543],q 0 [16397,20495,20594],q 1 [16397,20495,20594],q 0 [16394,20492,255101],q 1 [16394,20492,255101],q 3 [20492,255101],q 7 [20492,255101],q 1 [20488,20489,16398],q 0 [20488,20489,16398],q 16 [16398],q 1 [16394,20492,20493],q 0 [16394,20492,20493],q 12 [16394],q 1 [20490,12645,20494],q 1 [16394,20494,1175901],q 0 [16394,20494,1175901],q 10 [20494],q 0 [16395,13121,20493],q 1 [16395,13121,20493],q 1 [16395,13121,20494],q 0 [16395,13121,22165],q 1 [16395,13121,22165],q 3 [22165],q 7 [22165],q 4 [22165],q 1 [20489,16396,278543],q 0 [20489,16396,278543],q 1 [20489,16399,278543],q 7 [16399],q 0 [16397,114691,20494],q 3 [16397,20494],q 10 [16397,20494],q 0 [12299,20496,25425],q 1 [12299,20496,25425],q 1 [16395,13121,22166],q 7 [22166],q 0 [16395,13121,22166],q 5 [16395,22166],q 4 [22166],q 1 [16398,21221,20499],q 0 [16398,21221,20499],q 1 [21273,12298],q 0 [16387,21273],q 0 [16387,21273,12298],q 3 [16387,21273],q 10 [16387,21273],q 0 [12296,20496,24577],q 1 [20493,241681,233479],q 0 [16395,21313,20493],q 1 [16395,21313,20493],q 1 [16395,21313,20495],q 1 [16395,21313,1740815],q 7 [1740815],q 0 [16395,21313,1740815],q 4 [1740815],q 5 [16395,21313],q 0 [20493,20497,28680],q 0 [16395,20493,242499],q 1 [16395,20493,242499],q 6 [16395,242499],q 5 [16395,242499],q 0 [12289,20498,20499],q 0 [20490,16396,143361],q 0 [20488,16649,16397],q 1 [20488,16649,16397],q 3 [16649,16397],q 7 [16649,16397],q 1 [20488,16649,16399],q 0 [20488,16649,16399],q 3 [16649,16399],q 7 [16649,16399],q 0 [20488,20489,16397],q 1 [20488,20489,16397],q 16 [16397],q 0 [20488,16396,20621],q 1 [20488,16396,20621],q 1 [20496,24630],q 0 [12289,20496,24630],q 0 [20488,16398,16399],q 1 [20488,16398,16399],q 0 [20488,16399,271081],q 1 [20488,16399,271081],q 3 [16399,271081],q 7 [16399,271081],q 1 [20493,241683],q 0 [8193,20493,241683],q 3 [20493,241683],q 0 [8195,20492,20493],q 12 [8195],q 1 [20489],q 0 [20489,16398,17125],q 0 [20489,16398,279271],q 1 [20489,16398,279271],q 4 [20489,279271],q 0 [20489,16399,279275],q 1 [20489,16399,279275],q 6 [278543],q 1 [20489,20494,278543],q 0 [20489,20494,278543],q 1 [20490,16396,16397],q 0 [20490,16396,16397],q 0 [20489],q 0 [20489,20497,28687],q 1 [20489,20497,278547],q 0 [20489,20497,278547],q 0 [20489,20498,12701],q 0 [20491,13197,17589],q 1 [20491,13197,17589],q 3 [17589],q 7 [17589],q 0 [20497,28675],q 0 [20497,28675,28687],q 6 [278547],q 0 [20489,20498,278547],q 0 [20490,12645,20493],q 1 [20490,12645,20493],q 3 [12645,20493],q 7 [12645,20493],q 6 [12645],q 0 [20490,16396,143717],q 1 [20490,16396,143717],q 3 [16396,143717],q 7 [16396,143717],q 1 [20490,16396,143365],q 9 [20490],q 7 [16397,115047],q 5 [20490,115047],q 0 [20489,278543,20497],q 10 [278543,20497],q 1 [20490,16398,758117],q 3 [16398,758117],q 7 [16398,758117],q 6 [16398,758117],q 0 [16395,20492,254785],q 1 [16395,20492,254785],q 1 [20491,13197],q 1 [20491,13197,16398],q 0 [20491,13197,16398],q 0 [12289,20498,20893],q 1 [20491,13197,17590],q 7 [17590],q 0 [20491,13197,17590],q 4 [20491,13197],q 0 [16397,20493,20497],q 1 [16397,20493,20497],q 0 [20488,16649,1105923],q 3 [16649],q 1 [20491,17293,1789967],q 7 [1789967],q 0 [20491,17293,1789967],q 0 [20491,16396,144269],q 1 [20491,16396,144269],q 0 [12291,20496,25309],q 1 [20496,25309],q 1 [20491,16396,20621],q 0 [20491,16396,20621],q 1 [20491,16398,930533],q 0 [20491,16398,930533],q 4 [20491,930533],q 1 [16394,13437,16398],q 0 [16394,13437,16398],q 1 [20491,16399,930537],q 0 [20491,16399,930537],q 1 [16398,17125,114696],q 0 [16398,17125,114696],q 0 [16396,20621,528393],q 1 [16396,20621,528393],q 5 [528393],q 4 [528393],q 1 [16396,20621,528395],q 0 [16396,20621,528395],q 5 [528395],q 4 [528395],q 0 [16396,16397,20592],q 0 [20497,28682,28683],q 0 [12298,16893,22013],q 1 [12298,16893,22013],q 3 [16893,22013],q 7 [16893,22013],q 1 [16397,569355],q 0 [16397,114689,569355],q 5 [114689,569355],q 0 [12296,20941,20497],q 1 [12296,20941,20497],q 3 [20941,20497],q 7 [20941,20497],q 1 [16397,114696,21017],q 0 [16397,114696,21017],q 3 [16397,21017],q 5 [114696],q 1 [16397,114696,20494],q 0 [16397,20494],q 0 [16397,114696,20494],q 1 [16397,114696,20593],q 0 [16397,114698,114699],q 0 [16397,114699,20493],q 1 [16397,114699,20493],q 1 [20488,16397,114955],q 0 [20488,16397,114955],q 3 [16397,114955],q 7 [16397,114955],q 5 [114699],q 0 [16397,114699,20494],q 1 [16397,114699,20494],q 0 [20499,13001],q 0 [20497,28687],q 0 [20497,28684],q 1 [20497,28682],q 0 [20497,28682],q 0 [20496,24590],q 0 [20496,24589],q 0 [20496,24586],q 0 [20496,24585],q 1 [20496,24585],q 1 [20498],q 0 [20494,20498],q 1 [20494],q 0 [20494,20829],q 0 [20489,16396],q 1 [20489,16396],q 1 [12298,16393],q 0 [12298,16393],q 3 [20989],q 0 [16397,20595],q 1 [16399],q 1 [12298,16399],q 10 [16399],q 0 [12298,16399],q 1 [12297,20674],q 0 [12297,20674],q 0 [12298,16893],q 3 [16893],q 1 [16393],q 1 [16393,20494],q 2 [16393],q 0 [16393,20494],q 1 [12297,16399],q 0 [12297,16399],q 0 [12297,16397],q 1 [12297,16397],q 0 [12297,20497],q 1 [12297,20497],q 1 [12297,16394],q 0 [12297,16394],q 0 [12296,12297],q 0 [12296,16845],q 7 [17145],q 29 [],q 1 [217107],q 0 [20481,217107],q 7 [217107],q 1 [20499],q 0 [12289,20499],q 10 [20499],q 1 [12299,20497],q 0 [12299,20497],q 0 [16387,12296],q 1 [16398,20497],q 0 [16398,20497],q 10 [16398],q 1 [16398],q 0 [20481,16398],q 0 [20481,16397],q 1 [16394],q 0 [20481,16394],q 0 [20481,16399],q 0 [20481,16392],q 1 [16392],q 1 [20493],q 1 [12298,20493],q 0 [12298,20493],q 0 [20481,20494],q 0 [20493,241667],q 0 [20481,20490],q 0 [16387,20494],q 3 [16387],q 10 [16387],q 0 [16385],q 0 [16385,16398],q 3 [16385],q 0 [8195,20498],q 1 [20495],q 0 [12289,20495],q 1 [16392,20495],q 0 [16392,20495],q 0 [20497,28686],q 1 [20491,16397],q 0 [20491,16397],q 0 [16387,20490],q 1 [16422],q 0 [8193,16422],q 0 [16387,12298],q 0 [20483,16396],q 10 [16396],q 1 [16396],q 0 [16385,12296],q 1 [12296],q 1 [12296,20499],q 0 [12296,20499],q 0 [16387,13081],q 1 [13081],q 7 [13081],q 0 [20488,16649],q 1 [20534],q 0 [12289,20534],q 7 [20534],q 1 [12297,20495],q 0 [12297,20495],q 0 [16387,20493],q 0 [16385,20493],q 1 [16393,16398],q 0 [16393,16398],q 1 [16393,20938],q 0 [16393,20938],q 1 [745487],q 0 [16385,745487],q 0 [16393,20493],q 1 [16393,20493],q 0 [20481,20493],q 0 [16385,20492],q 1 [20492],q 10 [20492],q 0 [16396,143370],q 0 [12289,16392],q 1 [20493,20498],q 0 [20493,20498],q 0 [12297,20496],q 1 [12297,20496],q 10 [20496],q 0 [8193,20495],q 0 [8195,20499],q 0 [20491,13197],q 0 [20481,12298],q 0 [8193,20493],q 0 [8193,16397],q 0 [20483,16398],q 3 [20483],q 0 [20490,16398],q 1 [12298,16397],q 0 [12298,16397],q 0 [12291,20496],q 1 [20496],q 1 [12299],q 0 [12299,20498],q 1 [12326],q 0 [8193,12326],q 1 [20493,241675],q 0 [20493,241675],q 0 [16387,20488],q 0 [8195,20496],q 0 [20483,12298],q 0 [16385,20497],q 0 [8193,16398],q 0 [20481,16396],q 0 [20494,16733],q 1 [12296,20498],q 0 [12296,20498],q 0 [12299,17233],q 1 [12299,17233],q 0 [8195,20494],q 0 [20488,12553],q 3 [12553],q 1 [20490,16396],q 0 [20490,16396],q 0 [12297,20493],q 1 [12297,20493],q 0 [8195,20495],q 0 [8195,16399],q 0 [12289,20497],q 0 [20493,241673],q 1 [20493,241673],q 6 [241673],q 0 [20483,16397],q 0 [12291,20497],q 3 [12291],q 0 [8195,16397],q 0 [20489,20497],q 1 [20489,20497],q 1 [16398,20493],q 0 [16398,20493],q 0 [12289,20498],q 0 [8193,16399],q 0 [12289,20493],q 0 [8193,20499],q 7 [17117],q 0 [20493,241665],q 6 [241665],q 1 [12297,16578],q 0 [12297,16578],q 10 [16578],q 0 [16385,16394],q 0 [20483,16394],q 0 [16394,21629],q 3 [21629],q 1 [20490,20493],q 0 [20490,20493],q 0 [16385,20499],q 0 [20497,28673],q 0 [8193,20496],q 0 [16395,21313],q 1 [16395,21313],q 0 [20481,12296],q 0 [20493,241672],q 1 [20493,241672],q 0 [20493,241683],q 0 [20495,17157],q 0 [20483,16392],q 0 [16385,20495],q 0 [20483,12296],q 0 [16397,114697],q 1 [16397,114697],q 1 [16393,466959],q 0 [16393,466959],q 0 [12289,16397],q 0 [12296,20497],q 1 [12296,20497],q 0 [20490,16399],q 1 [20490,16399],q 0 [8193,16396],q 0 [16392,20492],q 1 [16392,20492],q 0 [20490,12645],q 3 [12645],q 1 [16438],q 0 [12289,16438],q 7 [16438],q 0 [12291,16392],q 0 [12289,20496],q 0 [8195,16398],q 0 [16385,16397],q 0 [12291,16394],q 1 [12298,20496],q 0 [12298,20496],q 0 [12289,20490],q 0 [8193,20494],q 0 [12291,20488],q 1 [12297,20498],q 0 [12297,20498],q 0 [12291,20499],q 0 [8193,20492],q 0 [12291,20498],q 1 [20518],q 0 [8193,20518],q 0 [16398,16399],q 0 [16385,12298],q 0 [8195,20493],q 0 [16385,20488],q 1 [20488],q 0 [16394,20494],q 0 [12289,20488],q 1 [20490,20497],q 0 [20490,20497],q 0 [12291,20490],q 0 [12298,20497],q 0 [12298,20498],q 1 [12298,20498],q 0 [12298,20499],q 0 [12299,21329],q 1 [12299,21329],q 1 [12299,20496],q 0 [12299,20496],q 0 [20488,20489],q 0 [12299,20499],q 0 [16392,12737],q 3 [12737],q 0 [20490,16741],q 3 [16741],q 0 [16385,20494],q 0 [20491,17293],q 1 [20491,17293],q 0 [16392,16393],q 1 [16392,20494],q 0 [16392,20494],q 0 [16392,20493],q 1 [16392,20493],q 1 [16394,20499],q 0 [16394,20499],q 1 [16395,20492],q 0 [16395,20492],q 2 [16395],q 1 [16393,20490],q 0 [16393,20490],q 1 [16394,20497],q 0 [16394,20497],q 0 [20481,20498],q 0 [16393,16397],q 1 [16393,16397],q 0 [16396,20621],q 1 [217103],q 0 [20481,217103],q 7 [217103],q 0 [16393,20492],q 1 [16393,20492],q 1 [16393,20495],q 0 [16393,20495],q 0 [16387,20492],q 0 [16393,20497],q 1 [16393,20497],q 1 [16393,20499],q 0 [16393,20499],q 1 [16397,20495],q 0 [16397,20495],q 0 [16394,13437],q 1 [16394,13437],q 3 [13437],q 7 [13437],q 0 [20494,20497],q 1 [16397,114698],q 0 [16397,114698],q 1 [16394,20489],q 0 [16394,20489],q 1 [12297,20499],q 0 [12297,20499],q 0 [20481,20497],q 1 [16394,16397],q 0 [16394,16397],q 1 [16397,20499],q 0 [16397,20499],q 1 [16394,16398],q 0 [16394,16398],q 1 [16394,20493],q 0 [16394,20493],q 0 [12289,16394],q 0 [12296,20496],q 1 [12296,20496],q 0 [16394,20495],q 0 [16395,13121],q 1 [16395,13121],q 0 [20483,16399],q 1 [16395,20493],q 0 [16395,20493],q 1 [16395],q 0 [16395,20494],q 0 [16395,20495],q 1 [12298,20495],q 0 [12298,20495],q 0 [16397,20497],q 0 [20488,16396],q 1 [20488,16396],q 0 [16387,20495],q 0 [20488,16397],q 1 [20488,16397],q 1 [20488,16398],q 0 [20488,16398],q 0 [12296,20941],q 3 [20941],q 1 [20489,16398],q 0 [20489,16398],q 1 [16399,20493],q 0 [16399,20493],q 1 [20489,16399],q 0 [20489,16399],q 1 [16394,20492],q 0 [16394,20492],q 0 [20489,20493],q 1 [20489,20493],q 1 [20489,20494],q 0 [20489,20494],q 1 [20489,20498],q 0 [20489,20498],q 0 [20497,28681],q 1 [20497,28681],q 1 [20488,16399],q 0 [20488,16399],q 1 [20489,278547],q 0 [20489,278547],q 1 [20490,16397],q 0 [20490,16397],q 1 [20490,20494],q 0 [20490,20494],q 0 [20483,13049],q 1 [13049],q 1 [21210],q 0 [16385,21210],q 1 [20490,20498],q 0 [20490,20498],q 1 [20491,16396],q 0 [20491,16396],q 1 [20491],q 0 [20491,16398],q 0 [8193,20498],q 0 [20491,16399],q 0 [16396,143369],q 1 [16396,143369],q 0 [12291,21213],q 1 [21213],q 7 [21213],q 0 [16396,20623],q 0 [20498,20499],q 0 [16397,114689],q 5 [114689],q 0 [16397,20594],q 0 [16398,21221],q 0 [12289,12298],q 0 [20489,16397],q 1 [20489,16397],q 0 [16398,20499],q 1 [16398,20499],q 0 [16399,20495],q 1 [16399,20495],q 0 [20492,20493],q 0 [8195,20492],q 1 [20489,278543],q 0 [20489,278543],q 1 [20493,241674],q 0 [20493,241674],q 0 [16385,20490],q 1 [20493,20499],q 0 [20493,241680],q 1 [20493,241680],q 6 [241680],q 0 [20493,241681],q 1 [20493,241681],q 6 [241681],q 0 [12289,16399],q 1 [20493,241682],q 0 [20493,241682],q 0 [20498],q 0 [12296],q 0 [20483],q 0 [16387],q 0 [12291],q 0 [20488],q 0 [20492],q 0 [16394],q 0 [16392],q 0 [20493],q 0 [20494],q 0 [20496],q 0 [12299],q 0 [16396],q 0 [16398],q 0 [20499],q 0 [16399],q 0 [16393],q 0 [16395],q 0 [20490],q 0 [20491],q 0 [20495]]
def B_24_4 : BT (List (List Nat)) := BT.empty
lemma B_24_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_24 4 xs.toFinset) B_24_4 := .empty
def U_24_5 : List Nat := [0]
def P_24_5 : BT (Option BoundPool) := buildPoolsSubBT 12 W_24 r_24 S_24 ps_24 U_24_5
def N_24_5 : List NodeSpec := [([8,11,0,1,2,3],[],[]),([8,0,1,2,3,14],[],[]),([8,0,1,2,16,3],[],[]),([8,18,0,1,2,3],[],[]),([22,0,1,2,4,5],[],[]),([8,0,1,2,24,3],[],[]),([0,2,25,21,4,5],[],[]),([8,27,0,1,2,3],[],[]),([32,0,1,2,3,4],[0],[]),([34,36,0,1,2,5],[],[]),([36,0,1,2,38,5],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_24_5 : checkNodesBT W_24 g_24 F_24 P_24_5 A_24 B_24_4 5 N_24_5 = true := by decide +kernel
def B_24_5 : BT (List (List Nat)) := buildBucketsBT W_24 N_24_5
set_option maxRecDepth 500000 in
lemma B_24_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_24 5 xs.toFinset) B_24_5 :=
  buildBucketsBT_sound (by decide) gp_24 W_24_ok (buildPoolsSubBT_sound S_24_ok) A_24_ok B_24_4_ok C_24_5
def U_24_6 : List Nat := (r 1 245)
def P_24_6 : BT (Option BoundPool) := buildPoolsSubBT 12 W_24 r_24 S_24 ps_24 U_24_6
def N_24_6 : List NodeSpec := [([8,0,1,2,3,40],(r 1 8),[]),([8,42,0,1,3],([1]++r 8 5),[]),([8,43,0,2,3],([8]++r 13 5),[]),([8,44,1,2,3],[4,8,18],[]),([39,0,1,45,3],[1,2,10,19,20,21],[]),([15,0,1,2,41],([7,17]++r 22 4),[]),([8,47,0,1,2],[1,8,26,27],[]),([8,0,1,2,3,49],[1,3,4,5,8,28],[]),([50,0,1,2,52],[8,17,29,30],[]),([54,36,0,1,2,5],([8]++r 31 7),[]),([36,56,1,2,5],[8,31,38],[]),([58,0,1,2,9,4,5],[17,39],[]),([1,2,61,63,59],[8,40,41],[]),([0,1,2,64,26,4,5],[42],[]),([36,65,0,1,5],([8,35]++r 43 4),[]),([0,1,67,28,68],([8]++r 47 4),[]),([69,0,2,19,3,4,5],[],[]),([70,71,0,1,2,4,5],[],[0]),([73,0,1,74,4],([8]++r 51 4),[]),([76,0,1,17,3],(r 55 4),[]),([36,77,0,1,2,33,5],[31,34,44,59],[]),([0,1,2,20,21,4,5],[],[0]),([0,1,2,78,4,63,59],[41],[]),([0,2,79,63,59],[8,17,60,61],[]),([0,2,19,25,3,4,5],[62],[0]),([80,0,1,2,81],[8,17,23,63,64],[]),([8,0,1,2,3,82],[1,2,4,7,65,66],[]),([8,0,1,2,9,10,3],[4,7,17],[0]),([27,0,1,2,3,6,7],[],[0]),([0,1,2,24,3,6,7],[],[0]),([23,8,0,1,2,9,3],[4,7,67],[0]),([36,0,1,2,83,5],[31,34,35,37,68,69],[]),([80,36,77,0,1,2,5],[17,31,44],[]),([84,0,1,86,5],([8]++r 70 5),[]),([0,1,2,29,4,88,5],[75],[]),([34,0,1,2,35,28,5],[],[0]),([36,0,1,2,90,5],([31,34,35]++r 76 4),[]),([91,0,2,29,3,4,5],[80],[]),([92,8,0,1,2,3],[1,4,5,7,81,82,83],[]),([8,93,0,2,3],[8,10,84,85,86],[]),([8,77,0,1,2,10,3],[4,10,17],[]),([12,8,0,1,2,3,13],[2,3,4,7,10,83],[0]),([94,0,1,3,6],[8,55,87,88],[]),([27,0,1,2,4,59,7],[89],[]),([95,96,0,1,2,3,4],[90],[0]),([97,8,0,1,2,3],[1,2,4,5,7,8,91,92],[]),([98,0,1,2,10],[8,17,23,93,94],[]),([37,36,0,1,2,9,5],[17,31,34,35,37,77],[0]),([99,0,1,2,101],[8,17,95,96],[]),([0,2,29,102,3,4,5],[97],[]),([87,0,1,2,105,4,5],[62,98],[]),([106,0,1,2,60],[8,17,99,100],[]),([80,36,0,1,2,9,5],[8,16,17,31],[]),([8,0,1,17,2,3,13],(r 1 4++[7,83,101]),[0]),([36,0,1,66,68],[37,44,102,103,104],[]),([8,0,1,2,107],[8,10,105,106],[]),([108,0,1,2,26],[8,17,107,108],[]),([109,0,1,111,4],([8]++r 109 4),[]),([0,1,113,114,59],(r 113 5),[]),([0,1,48,116,7],([8]++r 118 5),[]),e6 [117] [123,124],([23,8,77,0,1,2,3],[4,10,67],[]),([15,8,0,1,2,9,3],(r 1 4++[7,17]),[0]),([118,0,1,2,119,4,5],[],[]),([118,0,1,2,120],[8,17,125,126],[]),([18,0,1,2,3,6,7],[],[0]),([8,0,1,121,2],[7,8,10,127,128],[]),([0,1,2,30,3,4,31],[129],[0]),([8,0,1,2,19,3,7],[4],[]),([36,0,1,2,122,5],[31,34,35,77,130,131],[]),([15,8,77,0,1,2,3],[2,4,10,17],[]),([50,36,0,1,2,9,5],[8,16,31,132],[]),([8,123,0,2,3],[8,10,85,133,134],[]),([37,0,1,2,55],[17,23,37,135,136,137],[]),([8,0,1,2,9,26,3],[1,2,4,7,83,138],[0]),([36,0,1,2,29,5],[16,31,35,37,139,140],[]),([8,0,1,2,19,3],[1,4,7,83,141,142],[]),([8,124,0,1,2],[1,8,143,144],[]),([50,36,77,0,1,2,5],[31,44,132],[]),([0,1,2,9,3,120,7],[17,145],[]),([92,8,0,1,2,3,7],[4],[]),([125,0,1,2,62],[8,17,146,147],[]),([126,8,0,1,2,3],(r 1 5++[7,8,148]),[]),([8,0,1,2,3,128],(r 1 5++[149,150,151]),[]),([132,0,1,3,4],(r 152 5),[]),([8,127,0,1,2,26],[8,157],[]),([133,8,0,1,2,3],(r 1 5++[7,8,158]),[]),([8,69,0,2,3],[8,16,17,159,160],[]),([136,0,1,35,5],([8]++r 161 4),[]),([137,36,0,1,2,5],[8,31,32,34,35,37,77,165],[]),([138,36,0,1,2,5],[8,31,32,34,35,37,77,166],[]),([8,0,1,115,48],[7,8,10,167,168,169],[]),([36,0,1,140,5],[8,31,34,170,171],[]),([77,0,1,2,3,120,7],[17,145],[]),([36,141,0,1,5],[8,35,172,173],[]),([37,36,77,0,1,2,5],[17,31,34,44],[]),e6 [142] [123,124,174],([36,143,1,2,5],[8,31,35,175],[]),([36,145,0,1,5],[8,31,44,176,177],[]),([36,146,0,1,5],[8,35,178,179],[]),([36,148,1,2,5],[8,31,35,180],[]),([149,0,1,150,5],[34,35,44,181,182,183],[]),([151,0,1,134,5],[56,162,184,185],[]),([155,0,1,4,5],(r 186 5),[]),([12,0,1,46,3],[2,10,20,191,192],[]),([99,0,1,2,19,3,5],[],[]),([36,156,0,2,5],[8,16,17,193,194,195],[]),([36,0,1,157,5],[8,34,196,197],[]),([36,158,1,2,5],[8,31,198],[]),([36,69,0,2,5],[8,16,17,199,200],[]),([8,159,1,2,3],[1,4,8,201],[]),([15,8,127,0,1,2],[7,8,202],[]),([36,0,1,160,5],[8,34,203,204],[]),([161,0,1,147,5],[34,44,182,205,206],[]),([36,162,0,1,5],([8,35,44]++r 207 4),[]),([8,77,0,1,2,26,3],[2,4,10,138],[]),([0,1,163,63,59],([116]++r 211 5),[]),([164,0,1,2,33],[8,17,216,217],[]),([165,0,1,2,35],[8,17,218,219],[]),([166,0,1,62,4],[8,52,220,221,222],[]),([58,0,1,2,6],[8,17,223,224],[]),([36,0,1,2,9,33,5],[31,34,35,37,59],[0]),([118,0,1,2,24,4,5],[],[]),([8,167,0,1,17,2,3],[1,2,4,101],[]),([168,36,0,1,2,5],[16,31,32,35,37,225,226],[]),([12,8,167,0,1,2,3],[2,4,10,227],[]),([169,8,0,1,17,2,3],[1,2,4,10],[]),([8,170,1,2,3],[1,4,8,228],[]),([58,77,0,1,2,4,5],[17,39],[]),([0,1,2,19,26,4,59],[],[]),([171,0,1,3,173],([8]++r 229 5),[]),([8,0,1,174,3],[2,8,234,235],[]),([8,0,1,160,3],[2,8,236,237],[]),([8,162,0,1,3],([1,8,10]++r 238 4),[]),([0,1,2,29,35,33,5],[16,242,243,244],[]),([8,158,1,2,3],[4,8,245],[]),([169,12,8,0,1,2,3],[1,2,4,10,227],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_24_6 : checkNodesBT W_24 g_24 F_24 P_24_6 A_24 B_24_5 6 N_24_6 = true := by decide +kernel
def B_24_6 : BT (List (List Nat)) := buildBucketsBT W_24 N_24_6
set_option maxRecDepth 500000 in
lemma B_24_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_24 6 xs.toFinset) B_24_6 :=
  buildBucketsBT_sound (by decide) gp_24 W_24_ok (buildPoolsSubBT_sound S_24_ok) A_24_ok B_24_5_ok C_24_6
def U_24_7 : List Nat := (r 1 5++[7,8,10,13,16,17,23,31,32,34,35,37,39,41,44,49,50,52,54,55,56,59,61,62,67,71,72,74,76,77,83,84,89,101,104,110,112,115,116,120,121,123,124,132,133,138,145,149,153,159,162,169,174,182,187,193,199,210,213,214,227,230,231,233,241,243,244]++r 246 606)
def P_24_7 : BT (Option BoundPool) := buildPoolsSubBT 12 W_24 r_24 S_24 ps_24 U_24_7
def N_24_7_0 : List NodeSpec := [([0,1,160,26,4,5],([8]++r 246 4),[]),([69,0,17,2,3,4,5],([8,16]++r 250 4),[]),([0,1,17,107,4,5],(r 254 6),[]),([94,0,1,3,4,5],[8,256,260,261],[0]),([39,8,0,1,2,3,7],(r 1 4++[8,10,262]),[0]),([8,0,1,2,10,3],[1,2,4,8,263,264],[0]),([171,69,0,2,3,4,5],[8,16,251,252,265,266],[]),([39,8,0,1,2,3],(r 1 4++[7,8,10,83,262,267]),[0]),([8,0,1,2,46,3],[3,8,10,84,268],[0]),([8,0,175,1,2,3],(r 1 4++[8,269]),[]),([8,118,0,1,2,3],[1,2,4,5,7,8,17,270,271,272],[]),([23,8,0,1,2,3],(r 1 4++[7,8,67,273]),[0]),([23,118,0,1,2,6],[8,17,274,275,276],[0]),([108,0,1,2,3,7],[8,17,277,278,279],[0]),([8,0,1,2,3,57],[1,2,3,8,17,159,280],[0]),([169,8,0,1,2,3],(r 1 4++[7,8,10,17,83,281]),[0]),([162,0,1,3,6,7],([8,55,241]++r 282 4),[0]),([0,1,160,3,6,7],[8,231,286,287],[0]),([69,0,2,3,6,7],[16,17,288],[0]),([158,1,2,3,6,7],([8]++r 289 4),[0]),([8,171,0,1,2,3,7],(r 1 4++[8,10,277,293,294]),[]),([172,8,0,1,2,3],[2,4,8,56,295],[]),([172,171,0,1,3,6],[55,231,283,296,297,298],[0]),([124,0,1,2,6,7],[8,55,299,300,301],[0]),([0,1,2,107,6,7],[8,55,274,283,302,303,304],[0]),([170,1,2,3,6,7],[8,283,290,305,306],[0]),([8,0,1,17,2,3],[1,2,4,8,83,101,307,308],[0]),([8,167,0,1,2,3,7],(r 1 4++[8,10,309]),[0]),([8,167,0,1,2,3],[2,3,4,8,10,17,83,309],[0]),([167,0,1,17,2,3,6,7],[55,231,283,290,310],[0]),([177,0,1,2,3,7],[8,290,311,312],[]),([103,178,0,1,115,48],(r 313 7),[0]),([0,1,115,48,6,7],[8,55,274,283,313,320,321,322],[0]),([0,1,140,35,28,5],[8,72,162,243,323,324,325],[0]),([181,0,2,3,4,5],([16]++r 326 4),[]),([106,0,1,2,4,59],[8,17,62,330,331],[0]),([36,0,1,2,28,5,53],[8,77,332,333],[0]),e6 [50,29] ([16,17]++r 334 6),([50,178,77,0,1,2,3,4],[340,341],[]),([0,1,2,182,63,59],[8,41,213,342,343],[]),u6 [70,19] [62,83],([85,36,0,1,2,5],[8,31,34,56,344],[]),([0,1,2,9,4,88,28,5],[8,345,346],[0]),u6 [18,7] [174,347,348],([8,0,1,2,3,13,7],(r 1 4++[8,10,349]),[0]),([8,0,1,2,3,13],[2,3,4,8,10,83,349],[0]),([69,158,2,3,4,5],[16,17,350,351,352],[]),([23,118,77,0,1,2,4,5],[17,353],[0]),([0,1,2,35,122,28,5],([8,243,244]++r 354 5),[0]),([8,183,0,1,2,3],(r 1 4++[8,359]),[]),([0,1,2,19,3,4,59,7],[83,360,361],[0]),([149,36,0,1,2,28,5],[8,31,34,35,77,333,362,363],[]),([0,1,2,3,116,7],[8,120,121,274,364,365],[0]),([23,77,0,1,2,3,6,7],[17,55,290,366],[0]),([0,1,2,111,4,59],([17,110,112]++r 367 4),[0]),([8,77,0,1,2,3],[3,4,10,17,371],[0]),([103,77,0,1,2,3,184,5],[340,372],[]),([77,0,1,2,26,4,59,7],[89,373,374],[]),e6 [19,28] [8,361,375,376,377],([69,167,0,2,3,4,5],[16,251,252,253,266,378,379],[]),([36,0,1,134,2,5],[8,16,17,31,34,35,333,380,381,382],[]),([50,77,0,1,2,3,4,7],[17,340,383],[]),([36,84,0,1,2,28,5],[8,31,34,35,44,77,277,384,385],[]),([0,1,153,4,154,5],([187]++r 386 4),[0]),([50,77,0,1,2,35,28,5],[17,162,243,390],[0]),([12,8,0,1,2,3],(r 1 4++[7,8,83,227,391]),[0]),([0,1,3,67,4,68],(r 392 7),[0]),e6 [19,7] [174,361],e6 [19] ([62,83,361]++r 399 4),([36,0,144,1,2,5],[8,31,34,35,77,403],[0]),([8,0,1,115,2,3],[1,2,4,8,10,404,405],[0]),([0,1,2,3,173,7],[8,230,233,277,406,407],[0]),([85,84,0,1,35,5],[72,162,244,408,409,410],[0]),([98,8,0,1,2,3],(r 1 5++[7,8,17,411,412]),[0]),([0,1,2,3,120,7],[8,145,274,277,413],[0]),([50,118,0,1,2,4],([8,17]++r 414 4),[]),e6 [50,77] [174,418,419],([0,1,115,49,4,5],([256]++r 420 5),[]),u6 [64,7] [17,62,425,426],([77,0,1,2,3,184,5,7],[340,427,428],[]),([77,0,1,2,4,88,28,5],[345,428],[]),([185,186,0,1,66,68],([394,396]++r 429 5),[0]),([69,0,2,9,3,4,5,7],[8,17,251,252],[0]),([0,1,2,35,90,28,5],[8,50,72,76,243,244,355,434,435],[0]),u6 [27,7] [83,174,436],([36,0,1,2,135,5],[8,44,77,437,438],[0]),([136,0,1,3,4,5],([8]++r 439 4),[0]),u6 [19,57] ([377]++r 443 5),u6 [71,19] [62,83],([187,0,1,115,4,5],([182,313,314]++r 448 4),[]),([77,0,1,2,4,63,59],[17,41,214,343,428,452],[]),u6 [19,59] [8,56,62,83,453],([8,0,1,2,3,176],(r 1 4++[8,454]),[]),([0,1,2,35,83,28,5],[8,72,243,244,333,455,456,457],[0]),([99,0,1,2,63,59],[8,17,41,213,458,459],[]),([69,77,0,2,3,4,5],[351,352,460],[]),([36,0,1,2,5,53],[8,37,77,332,333],[0]),([8,0,1,2,9,3,7],[1,3,4,8,17,83,461],[0]),e6 [178,29] [16,17,62,335,336,337],([36,0,1,2,28,5,68],[8,44,462,463],[0]),([0,1,2,3,82,6,7],[8,231,274,283,290,464,465,466],[0]),u6 [78,63] [467],e6 [189,28] [16],([36,0,1,150,2,5],[8,31,34,35,44,468,469],[0]),([80,36,0,1,2,5],[8,31,32,34,35,37,77,470,471],[0]),([23,0,1,2,9,3,6,7],[17,274,290,366],[0]),([36,0,1,66,2,5],[8,31,34,35,44,472,473],[0]),e6 [29,7] [8,17,336,375,376,474],([36,190,0,1,2,5],[8,31,34,35,77,475],[]),e6 [192,191] [476],([1,2,62,4,61,59],([8,116]++r 477 4),[0]),([87,0,1,2,29,4,5],[17,335,336,337,481,482,483],[]),([77,0,1,2,26,4,5,57],[17,248,484],[0]),u6 [96,29] [16,17,335,485,486],([8,171,0,1,2,3],[1,2,8,10,83,277,293,294],[]),([50,36,0,1,2,5],[8,31,32,34,35,37,77,132,487,488],[0]),([99,0,1,2,9,3,5,7],[8,17,489,490],[0]),u6 [30,29] [16,335,336,337,485,491,492,493],([36,0,1,2,9,5],[8,16,17,35,77,494],[0]),([0,1,2,114,63,59],[8,41,213,214,495,496],[]),e6 [103,119] [8,277,497],([23,118,0,1,2,9,4,5],[17,353,360],[0]),([0,1,2,9,4,63,59],[8,16,17,41,116,213,343,346,498],[0]),([0,1,2,3,49,6,7],([8,283,290]++r 499 4),[0]),u6 [24,7] [8,346,503],([0,1,2,9,3,194,4,7],[504,505],[]),([195,0,1,2,28,5],[8,243,506,507],[]),([186,0,1,2,197,5],([8]++r 508 4),[]),([0,1,2,9,3,184,5,7],[346,427,489],[]),([8,0,1,2,3,41],[1,2,3,8,13,17,512],[0]),([0,1,2,60,63,59],[8,17,213,513,514],[0]),([87,0,1,2,9,104,4,5],[8,346,515],[0]),([8,0,1,2,3,75],[3,8,10,133,516],[0]),([162,0,1,160,3,4,5],(r 517 7),[]),([50,178,0,1,2,9,3,4],[341,489],[]),([36,0,1,2,147,5],[8,44,77,524,525],[0]),([50,0,1,2,9,35,28,5],[8,16,17,243,390],[0]),([198,0,1,2,63,59],[8,41,213,333,526,527],[]),([0,1,2,9,26,4,59,7],[8,89,360,374],[0]),([36,77,0,1,2,5],[17,31,44,77,528],[0]),([196,0,1,2,4,5,129],[83,511,529,530,531],[]),e6 [17,82] [83,124,347,348,444,447,532,533],([1,115,48,4,199,5],([313]++r 534 5),[]),u6 [29,31] [16,335,485,492,493,539,540],([158,1,2,62,4,59],([8,479]++r 541 4),[]),([77,0,1,2,3,194,4,7],[504,545],[]),([200,0,1,66,3,4],([394,396,397]++r 546 4),[]),([0,1,2,3,179,5,201],([8]++r 550 5),[]),u6 [19,26] [62,83,361,436,443,444,446,447],([196,0,1,2,26,4,5,7],[8,83,511],[]),([84,158,1,2,3,4,5],([8,174,350]++r 555 6),[]),([162,0,1,62,4,59],([8,52]++r 561 6),[]),([123,0,2,3,6,7],[8,55,567,568,569],[0]),([51,36,0,1,2,5],[8,17,31,34,35,37,77,570,571],[]),([0,1,2,9,35,33,28,5],[8,17,50,72,243,244,572],[0]),([100,99,0,1,2,62],[8,17,116,573,574],[0]),e6 [118,19] [62,83,360,575],([164,0,1,2,28,5],[8,17,277,576,577],[0]),([196,0,1,2,4,129],[83,511,529,530,531,578],[]),([196,0,1,2,4,5,202],[83,347,511,579],[]),([89,36,0,1,2,5],[8,31,34,35,77,104,333,580,581],[0]),e6 [64] [8,16,83,521,582,583,584],u6 [19,21] [62,83,443,444,446,447],([76,0,1,2,3,7],[8,55,56,277,585],[0]),([99,77,0,1,2,3,5,7],[17,340,490],[]),([141,0,1,35,28,5],[8,244,586,587,588],[0]),([0,2,62,4,79,59],[17,61,589,590,591],[0]),([0,1,2,9,26,3,6,7],[17,83,231,274,283,290,592],[0]),([127,0,1,2,26,6,7],[8,274,593,594],[0]),e6 [167,128] [174,595],([0,1,2,203,4,59],[23,116,333,479,596,597],[]),e6 [50,9] [8,16,174,419],([0,1,17,3,6,75],[55,231,598,599,600],[0]),u6 [29,33] [16,17,335,336,337,485,493,540,601,602],([0,1,2,29,35,28,5],[16,17,50,243,244,337,603,604],[0]),([36,0,1,134,2,28,5],[8,17,31,32,35,77,380,381,382],[]),([69,0,2,9,3,4,5],[8,83,351,352,605,606],[]),([87,0,1,2,29,4,28,5],[483],[0]),([8,0,1,2,9,3],[1,3,8,17,461],[0]),([103,0,1,2,9,3,184,5],[372,489],[]),e6 [204,202] [174],([77,0,1,2,35,33,28,5],[17,72,162,243,572],[0]),u6 [119,7] [8,56,346,497],([58,0,1,2,4,5],[8,39,607],[0]),([37,36,0,1,2,5],[8,31,34,35,37,77,608,609],[0]),([0,1,2,26,6,57],[17,274,610,611],[0]),([0,1,2,9,26,4,5,57],[8,17,248,484],[0]),([36,0,1,2,5,55],[8,17,34,35,77,193,612],[0]),([8,0,1,2,3,48],[2,7,8,10,613,614],[0]),([0,1,48,4,116,5],([182,313,314]++r 615 5),[0]),e6 [29] ([16,17,277,335,336,337]++r 620 4),u6 [95,29] [16,335,624],e6 [185,19] [62,83,361],u6 [34,28] [16,174,602],u6 [20,19] ([62,83,361]++r 443 4++[453]),([8,0,1,2,3,48,7],[3,4,5,8,10,613,614],[0]),([0,1,2,3,128,6,7],[8,149,231,274,283,290,499,501,625,626],[0]),([207,0,2,3,4,5],[16,627,628],[]),([208,0,1,2,63,59],[8,41,213,333,629,630],[]),([8,127,0,1,2,3],[2,8,17,169,631,632],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_24_7_0 : checkNodesBT W_24 g_24 F_24 P_24_7 A_24 B_24_6 7 N_24_7_0 = true := by decide +kernel
def N_24_7_1 : List NodeSpec := [([209,0,1,2,4,129],([153]++r 633 5),[]),([151,0,1,2,28,5],[8,56,162,277,638],[0]),e6 [210,7] [17,124,377,639],([0,66,3,211,4,68],([394,396]++r 640 5),[]),([8,212,0,1,2,3],[1,3,4,8,169,645],[]),([0,1,3,113,114,5],(r 646 5),[0]),([0,1,2,52,28,5],[17,50,277,651,652],[0]),([15,8,0,1,2,3],(r 1 4++[7,8,653,654]),[0]),([0,1,112,62,114,59],([52,116,562,648]++r 655 4),[0]),([0,1,2,113,4,59],([17,115,370]++r 659 4),[0]),([186,0,1,2,213,5],[8,635,663,664,665],[]),([36,214,0,1,2,5],[8,17,31,44,77,333,666],[]),([36,0,1,2,9,28,5],[16,17,31,35,37,494],[0]),([158,1,2,35,28,5],[8,243,558,667],[0]),([69,0,2,35,28,5],[16,17,668],[0]),u6 [87,19] [56,62,83,277,453],u6 [105] ([16,17,62,277]++r 669 5),([1,66,3,215,4,68],[394,396,674,675,676],[]),([50,99,0,1,2,3],[8,17,677,678,679],[]),([0,1,2,216,4,59],[8,52,116,562,680,681],[]),([0,1,160,62,4,59],([8,370]++r 682 4),[]),([0,1,66,35,28,68],[8,50,162,396,686,687,688],[0]),([69,77,0,2,3,4,5,7],[17,251,252,689],[]),([0,1,2,67,28,5],[8,49,690,691,692],[0]),([0,1,74,62,4,72],[8,52,54,370,693,694],[0]),([36,0,1,2,5,68],[8,34,37,44,462,463],[0]),e6 [122] [8,123,174,354,623,695,696],([36,0,1,2,81,5],[8,17,34,35,697,698],[0]),u6 [23,19] [],([89,36,0,1,2,28,5],[8,31,34,77,333,580,581],[0]),([218,0,1,2,4,59],[8,333,699,700],[]),([0,1,130,3,4,131],([153]++r 701 5),[0]),([0,1,2,19,3,6,7],[83,274,283,290,361,706,707],[0]),([36,0,1,2,139,5],[8,31,34,35,77,708],[0]),([8,0,1,17,2,3,7],[1,3,4,5,8,101,307,308],[0]),([0,1,134,35,135,5],[72,162,709,710,711],[0]),([143,1,2,35,28,5],[8,243,244,712,713],[0]),([87,196,0,1,2,4,5,7],[83,377,511],[]),([0,1,2,86,28,5],[8,71,74,277,714,715],[0]),([87,118,0,1,2,9,4,5],[8,83,346,360,716],[0]),([161,36,0,1,2,28,5],[8,17,31,32,34,35,56,77,717,718],[]),([77,0,1,2,26,3,6,7],[17,55,231,290,592],[0]),([36,84,0,1,2,5],[8,16,34,35,44,277,384,385],[]),([219,220,0,1,3,4],([531,705]++r 719 4),[0]),([221,36,0,1,2,5],[8,16,17,31,34,35,37,44,77,333,723],[]),([161,36,0,1,2,5],[8,16,17,31,34,35,37,77,333,717,718],[0]),([8,77,0,1,2,3,7],[3,4,10,17,371],[0]),([36,0,1,2,33,5],[8,31,34,35,59,724],[0]),([8,0,1,2,26,3],[1,2,4,8,138,725],[0]),([36,0,1,2,5,57],[8,17,34,35,77,199,726],[0]),e6 [78] ([62,277,335,467]++r 727 4),([84,69,0,2,3,4,5],[8,83,351,352,731,732,733],[]),([118,0,1,160,4,5],[8,17,734,735],[]),([0,1,2,35,33,57],[17,50,736,737],[0]),([169,8,0,1,2,3,7],(r 1 4++[8,10,281]),[0]),([149,36,0,1,2,5],[8,16,31,34,35,37,44,77,362,363],[0]),([0,1,222,2,4,63,59],[8,41,213,333,343,738],[]),([0,1,160,35,28,5],[8,72,739,740,741],[0]),([73,0,1,2,4,59],[16,52,62,742,743,744],[0]),([0,1,17,2,3,13,6,7],[55,83,231,274,283,290,310,499],[0]),e6 [223,7] [83],([162,0,1,35,28,5],[8,162,210,244,745,746],[0]),([50,51,0,1,2,35],[8,17,747,748],[0]),([50,0,1,2,9,3,4,7],[17,383,489],[]),([0,1,2,3,4,33,224],[8,16,124,749,750],[]),([193,0,1,2,19,3,4,7],[],[]),([0,1,134,2,4,33,59],([8]++r 751 10),[]),([0,1,134,2,4,88,5],[8,62,761,762,763],[]),([69,0,134,2,3,4,5],[8,83,351,352,764,765,766],[]),([118,0,1,134,2,4,5],([8]++r 767 4),[]),([69,0,2,3,4,5],[16,17,771],[]),([165,0,1,2,3,4],[8,17,772,773],[0]),([0,1,2,29,4,5,59],[8,17,62,335,336,337,774,775,776],[]),([225,1,160,3,4,5],[8,517,777,778],[]),([8,127,0,1,2,3,7],[2,3,4,8,17,631,632],[0]),([225,1,160,2,3,4,5],[123,517,523,777,779,780],[]),([171,158,1,2,3,4,5],([8,174]++r 781 4),[]),([158,1,160,3,4,5],[8,17,518,785,786],[]),([12,8,0,1,2,3,7],(r 1 5++[8,56,391]),[0]),([0,1,2,101,4,59],[8,17,62,787,788],[0]),([162,158,1,3,4,5],[8,17,557,789,790],[]),([226,0,1,2,4,63,59],[8,41,62,116,213,214,343,791,792,793],[]),([162,158,1,2,3,4,5],[8,17,174,350,555,557,789,790],[]),([87,118,77,0,1,2,4,5],[428,716],[]),([69,0,160,3,4,5],[16,17,794],[]),([69,0,160,2,3,4,5],[16,17,351,352,519,732,794],[]),([162,69,0,3,4,5],[8,16,460,795,796],[]),([69,225,2,3,4,5],[8,16,351,460,779,797],[]),([36,227,0,1,2,5],[8,31,35,77,104,798],[]),([118,0,1,160,2,4,5],[8,17,735,767,768],[]),([0,115,48,4,228,5],([313,314]++r 799 5),[]),([162,69,0,2,3,4,5],[8,16,351,352,460,732,795,796,804],[]),([8,0,1,45,2,3],[1,2,4,8,10,805,806],[0]),([99,118,0,1,2,5],[8,17,807,808,809],[]),([193,0,1,2,4,230],([8]++r 810 4),[]),([231,0,1,2,4,63,59],[8,41,116,213,214,343,793,814],[]),([110,109,0,1,62,4],[8,52,370,562,815,816,817],[0]),e6 [204] ([62,83]++r 818 5),([0,1,62,4,163,59],([52,116,562]++r 823 4),[0]),([232,0,1,62,4,59],([8,116,370]++r 827 4),[]),([0,1,2,62,60,57],[17,831,832,833],[0]),([36,77,0,1,2,28,5],[17,31,44,77,528],[0]),([69,0,2,62,4,59],[16,17,834,835,836],[]),([166,0,1,3,4,5],([8]++r 837 4),[0]),([87,77,0,1,2,104,4,5],[428,515],[]),e6 [234] [8,16,123,174,841,842],([0,2,3,79,59,7],[8,17,56,843,844],[]),([125,0,1,2,3,5],[8,17,845,846],[0]),([235,236,0,1,4,5],([389]++r 847 5),[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_24_7_1 : checkNodesBT W_24 g_24 F_24 P_24_7 A_24 B_24_6 7 N_24_7_1 = true := by decide +kernel
def N_24_7 := N_24_7_0 ++ N_24_7_1
def B_24_7 : BT (List (List Nat)) := buildBucketsBT W_24 N_24_7
set_option maxRecDepth 500000 in
lemma B_24_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_24 7 xs.toFinset) B_24_7 := by
  have hP := buildPoolsSubBT_sound (pdepth := 12) (W := W_24) (raw := r_24) (pspecs := ps_24) (used := U_24_7) S_24_ok
  have hm0 := checkNodesBT_mem (by decide) gp_24 W_24_ok hP A_24_ok B_24_6_ok C_24_7_0
  have hm1 := checkNodesBT_mem (by decide) gp_24 W_24_ok hP A_24_ok B_24_6_ok C_24_7_1
  exact buildBucketsBT_of_mem (forall_append (hm0) hm1)
def U_24_8 : List Nat := ([3,5,8,16,17,23,32,50,52,55,56,62,72,76,77,83,116,123,124,153,162,174,182,187,210,231,241,243,244,248,250,251,256,265,270,274,277,283,290,301,306,308,310,313,314,317,318,319,322,325]++r 333 5++[339,340,341,343]++r 345 4++[350,351,353,354,355,360,361,366,369,370,372]++r 374 5++[382,383,389,390]++r 394 4++[401,402,418,419,422,426,427,428,431,432,433,436,440]++r 442 4++[447,449,453,457,467,476,478,479,481,484,485,487,489,490,492,497,499,501,503,504,505,511,515,517,519,521,522,523,527,531,532,533]++r 535 4++[540,542,545,547,552,554,555,559,560,562,569,572,575,584,588,592,595,600,602,605,606,617,618,622,623,635,636]++r 641 4++[648,649,650,657,658,662,671,672,675,676,688,705,711,713,716,729,731,744,751,754,757,759,764,766,767,776,779,781,782,791,795]++r 800 4++[811,820,821,825,838,840,841,844,847]++r 852 1752)
def P_24_8 : BT (Option BoundPool) := buildPoolsSubBT 12 W_24 r_24 S_24 ps_24 U_24_8
def N_24_8_0 : List NodeSpec := [e6 [171,7] ([8,124,401,402]++r 852 6),e6 [17,7] [8,308,333,347,401,402,852,853,858,859],e6 [237,104] ([8,17,347,671,672]++r 860 4),([162,0,1,3,4,5,7],[8,241,256,447,864,865],[0]),([0,1,160,3,4,5,7],[8,333,866,867,868],[0]),([69,0,2,3,4,5,7],[8,16,251],[0]),([124,0,1,2,4,5,7],[8,256,301,869,870],[0]),([0,1,2,107,4,5,7],[8,256,360,447,871,872],[0]),([123,0,2,3,4,5,7],[8,256,569,873,874],[0]),u6 [17,57] [8,250,333,377,426,447,781,875,876,877],([0,1,17,3,4,5,75],[8,256,600,868,878,879],[0]),u6 [167,17,7] [256,348,444,447,868,875,880,881],([8,0,1,2,3,7],[3,5,8],[0]),([8,0,1,2,3],[3,5],[0]),([118,0,1,2,3,6,7],[8,17,231,283,290,499,501,882,883],[0]),([0,1,2,3,6,7,57],[8,17,231,283,499,884,885],[0]),([0,1,2,26,3,6,7],[8,231,274,283,290,592,886,887],[0]),([171,0,1,2,3,6,7],[8,55,83,231,274,283,290,499,857,888,889],[0]),([172,0,1,2,3,6,7],[8,231,290,499,890,891],[0]),([167,0,1,2,3,6,7],[8,17,55,83,231,274,283,290,499,892,893],[0]),([0,1,2,3,6,7,176],[8,231,283,290,499,894,895],[0]),([236,0,1,2,4,152,5],([8,187,389,847]++r 896 6),[0]),([235,0,1,2,4,152,5],([83,389,847,896,898]++r 902 4),[0]),([0,1,2,4,152,154,5],([8,187,389,847]++r 906 4),[0]),([0,1,2,4,152,238,5],[8,83,187,389,896,898,910,911,912],[]),([87,0,1,2,104,4,5],[8,515,913,914],[0]),([87,118,0,1,2,4,5],[8,360,716,915,916],[0]),([0,1,2,3,184,5,7],[8,277,360,427,917],[0]),([100,99,0,1,2,3,5],[8,17,918,919,920],[0]),([162,0,1,3,4,5,59],([8,838]++r 921 4),[0]),([0,1,160,3,4,5,59],[8,16,840,925,926],[0]),([158,1,2,3,4,5,59],[8,16,542,927,928],[0]),([232,0,1,3,4,5,59],[8,16,840,929,930],[0]),([0,1,3,4,163,5,59],[825,838,918,931,932,933],[0]),([0,2,3,4,79,5,59],[8,17,844,934,935],[0]),([1,2,3,4,61,5,59],[8,16,56,478,928,936],[0]),([0,1,2,3,239,4,59],[8,17,62,335,937,938],[]),([103,99,0,1,2,3,5],[8,17,918,939,940],[]),([0,1,2,3,4,59,7],[8,17,62,277,941,942],[]),([99,0,1,2,3,59,7],[8,17,277,490,943],[]),([0,1,2,3,60,59,7],[8,17,944,945],[0]),([118,0,1,2,4,59,7],[8,17,62,946,947],[]),([171,0,1,2,3,4,59,7],([8,377,857]++r 948 6),[]),([167,0,1,2,3,4,59,7],([8,333,893,948,949]++r 952 4),[]),([0,1,74,3,4,5,72],[8,838,840,956,957,958],[0]),([100,0,1,2,62,4,59],([8,17,116,370,479,562]++r 959 5),[0]),([0,1,2,62,4,59,57],([17,370,562,959]++r 964 4),[0]),([109,0,1,2,62,4,59],([8,479,562,959]++r 968 4),[0]),([0,1,74,2,62,4,59],([8,370,479,959]++r 972 4),[0]),u6 [226,63] ([8,62,124,335,467,729]++r 976 6),u6 [231,63] ([62,123,333,335,467,729,976]++r 979 5),([99,186,0,1,2,3,5],[8,17,277,984,985],[]),([193,0,1,2,3,4,202],([8,17,277]++r 986 4),[]),([0,1,2,3,4,202,59],[8,17,62,277,990,991],[]),e6 [240,202] ([8,123,333,820,821]++r 992 4),([185,118,0,1,2,4,5],[8,17,360,915,996,997],[]),([185,178,0,1,2,4,59],[8,17,62,335,918,998,999,1000],[]),([185,0,1,2,4,59,7],[8,17,360,918,1001,1002],[]),([0,1,2,4,241,5,59],[8,17,62,1003,1004,1005],[]),([0,1,2,3,4,242,7],[8,17,62,277,1006,1007],[]),([0,1,160,3,4,28,5],[8,17,442,517,519],[0]),([69,0,2,3,4,28,5],[16,17,83,351,766],[0]),([99,0,1,2,3,5,57],[8,17,841,1008,1009],[0]),e6 [99] [8,17,123,124,174,347,1008,1009],([118,0,1,2,4,5,57],[8,17,841,1010,1011],[0]),e6 [118] [8,17,123,124,174,347,841,1010,1011],([158,1,2,3,4,5,57],[8,17,123,333,350,584,1012],[0]),([225,1,2,3,4,5,57],[8,174,418,555,779],[0]),([0,1,2,243,4,28,5],[17,277,339,1013,1014],[]),([50,0,1,2,3,4,7],[8,277,383,1015],[0]),([118,0,1,2,4,28,5],[8,17,277,915,1016,1017],[0]),u6 [57] [17,123,124,174,339,347,1018,1019],([50,0,1,2,3,4,59],[8,17,62,1020,1021],[0]),([99,0,1,2,3,28,5],[8,17,277,1022,1023],[0]),([0,1,2,4,33,28,59],[17,339,376,751,754],[0]),([99,0,1,2,28,5,59],[8,17,277,1022,1023],[]),([0,1,2,60,28,5,59],[8,17,1024,1025,1026],[]),e6 [127,244] ([8,124,377]++r 1027 7),e6 [245] ([8,62,123,174,841,913]++r 1034 4),e6 [247] ([8,124]++r 1038 4),([246,0,1,2,3,5,7],[8,174,277,1042,1043],[]),e6 [51,134] ([8,397,759]++r 1044 8),e6 [248,7] ([8,16,277,333,444,447,868]++r 1052 6),e6 [250] ([8,56,62,123,174,277,841]++r 1058 5),([185,186,0,1,2,5,53],([16,431]++r 1063 7),[0]),([178,0,1,2,9,3,4,59],[17,335,346,505,998,1070,1071,1072],[]),e6 [252] ([8,62,123,174,841]++r 1073 4),e6 [253] [8,123,124,347,841,1077,1078],([254,0,1,3,4,5,53],([1063,1064]++r 1079 4),[]),e6 [255,202] [8,124,820,821,994,995,1083,1084,1085],e6 [83] ([8,17,124,485,527]++r 1086 4),e6 [82] ([83,124,444,532,533]++r 1090 4),u6 [213] ([8,635]++r 1094 4),([0,1,2,4,28,5,59],[17,277,339,1098,1099],[]),e6 [246,127] [8,16,124,1100,1101,1102],([127,118,0,1,2,4,5,7],[8,17,62,447,915,1103,1104],[]),e6 [256] ([8,277,377,527]++r 1105 7),u6 [9,28] [16,17,62,277,346,489,505,622,623,1112,1113,1114],u6 [87,103,77] ([340,428,545,1035]++r 1115 4),([0,1,2,9,3,4,129],[8,16,62,277,346,489,531,1119,1120,1121],[0]),e6 [257] [62,83,123,124,174,347,841,1122,1123,1124],e6 [258] [8,123,124,347,841,1125,1126],([0,1,17,2,3,6,7],[8,83,231,283,290,308,310,499,1127],[0]),([198,0,1,2,3,63,5],[62,333,467,527,729,1124,1128,1129],[0]),([0,1,2,3,48,6,7],[8,55,231,274,283,1130,1131,1132],[0]),e6 [260] ([8,124]++r 1133 4),e6 [261] ([16,62,83,123,335,347,841,1109]++r 1137 6),e6 [262] ([62,83,174]++r 1143 6),([193,0,1,2,3,4,201],([16,333,1124]++r 1149 5),[]),([0,1,2,3,4,201,59],[16,62,83,552,928,1154,1155,1156],[]),e6 [264] ([8,124]++r 1157 4),([263,0,1,2,3,4,7],[8,56,174,277,1161,1162],[]),e6 [266] ([8,174,335]++r 1163 4),e6 [267] ([56,928]++r 1167 5),([0,1,2,3,4,268,7],([8,174,277,360,444]++r 1172 4),[]),e6 [269] [8,56,123,124,841,1176,1177],([0,1,2,3,182,270,5],([8]++r 1178 5),[]),([0,1,2,62,4,182,59],[8,52,116,370,479,959,1183,1184,1185],[0]),([186,0,1,66,3,4,68],([8,396,675,987]++r 1186 5),[0]),e6 [271] [16,62,123,124,174,347,841,1129,1191,1192],e6 [272] ([8,56,123,174,277,335,841]++r 1193 5),e6 [273] [8,123,124,347,841,1198,1199],([103,0,1,2,3,184,5],[8,62,372,1200,1201],[0]),([183,0,1,2,3,6,7],[8,231,283,290,499,1202,1203],[0]),e6 [77,152] [187,340,545,896,898,1204],([0,1,2,3,6,7,75],[8,55,283,499,1205,1206,1207],[0]),([183,0,1,2,4,152,5],[8,56,123,389,847,896,898,1203,1208,1209],[]),([208,0,1,2,3,63,5],([62,333,335,467,729,979]++r 1210 4),[0]),([274,183,0,1,3,4,5],([1203,1209]++r 1214 4),[]),([84,0,1,2,35,28,5],[8,16,50,72,162,243,244,355,1218,1219,1220],[0]),e6 [275] [16,83,123,841,1221,1222,1223],e6 [183,191] ([16,17,476,1203]++r 1224 4),([50,0,1,2,35,28,5],[8,72,243,244,355,390,1228,1229],[0]),([183,0,1,2,276,4,5],[8,16,17,56,83,1203,1230,1231,1232],[]),([0,1,2,62,4,59,217],[16,370,479,562,959,1233,1234,1235],[0]),e6 [277] [8,123,124,347,841,1236,1237],e6 [278] ([8,123,124,174,347]++r 1238 4),([0,1,2,3,60,5,57],[8,17,1242,1243,1244],[0]),([193,77,0,1,2,3,4,7],[17,545,1245,1246,1247],[0]),([190,0,1,2,3,4,191],[8,16,17,56,83,476,1033,1226,1248],[]),u6 [50,9,28] [8,16,17,334,346,485,489,505,1249],([196,0,1,2,35,4,5],[83,174,1250,1251,1252],[0]),u6 [206] [8,124,174,347,1253,1254,1255],e6 [127,53,7] [16,17,335,527,868,1082,1092,1109,1256],e6 [279] ([8,124]++r 1257 4),([198,0,1,2,62,4,59],[16,370,479,562,959,1129,1261,1262],[0]),u6 [82,7] [8,444,447,532,868,1090,1091],e6 [280] ([16,62,83,123,174,347]++r 1263 4),e6 [281] ([8]++r 1267 5),u6 [17,13,7] [8,83,256,348,360,444,447,868,875,1052,1272,1273],([77,0,1,2,3,4,129],[153,340,428,1120,1121,1274],[]),([185,0,1,2,9,4,5,59],[16,17,62,83,346,1275,1276,1277],[]),u6 [50,77,28] [17,334,340,428,440,485,545,1249,1278],([0,1,2,13,4,152,5],[8,83,187,389,847,896,898,1279,1280,1281],[]),([185,259,0,1,2,4,5],[8,56,1184],[]),([263,178,0,1,2,3,4],[8,56,1182],[]),([178,0,1,2,4,28,59],[8,17,62,339,918,1282,1283],[]),e6 [283] [8,123,124,347,841,1284,1285],([170,1,2,3,4,5,7],[8,306,444,447,1286],[0]),([0,1,2,4,63,59],[8,16,23,62,116,343,791],[0]),e6 [284] ([8,16,83,124,1063]++r 1287 5),([285,0,1,2,3,4,59],[16,62,174,1292,1293,1294],[]),e6 [50,48] ([8,16,62,397,1132,1278]++r 1295 5),([227,0,2,3,211,4,5],([641,643]++r 1300 6),[]),([282,186,0,1,2,3,5],[8,1306,1307],[]),([87,0,1,2,286,4,5],[16,277,333,1129,1308,1309],[]),([282,0,1,2,3,28,5],[8,174,277,1310,1311],[]),u6 [99,77] ([17,174,340,418,428,545]++r 1312 4),([50,51,0,1,2,3,4],[8,17,1316,1317],[0]),([0,1,2,288,4,28,5],([8,56,124,277,442]++r 1318 4),[]),([0,1,2,13,276,4,5],[16,83,124,1230,1232,1280,1322,1323],[]),e6 [89,103,13] [8,376,1115,1272,1273,1280,1281,1324,1325],([186,0,1,2,3,289,5],[8,17,1152,1326,1327,1328],[]),e6 [89,13,7] [8,376,444,868,1092,1272,1273,1280,1281,1329],e6 [290] [8,123,124,347,841,1330,1331],u6 [19,7] [83,335,360,361,443,444,445,447,453],([0,1,2,3,289,28,5],[17,277,339,1332,1333],[]),e6 [291] [16,56,62,123,277,335,346,489,841,1252,1334,1335,1336],e6 [127,202] [8,83,124,277,376,820,821,987,988,994,1083,1109,1141,1337,1338],e6 [292] [56,123,124,174,841,1184,1339,1340,1341],([0,1,2,62,60,4,59],([17,23,370,562,959]++r 1342 4),[0]),([50,0,1,2,3,4,57],[8,17,841,1346,1347],[0]),e6 [293] [16,62,83,1348,1349,1350],([274,0,1,3,13,4,5],[1214,1217,1273,1280,1281,1351,1352],[]),([0,1,134,2,4,28,5,59],([8,62,382,776]++r 1353 6),[0]),([0,1,2,13,294,4,5],([8]++r 1359 4),[]),e6 [295] ([8,16,17,376,1151]++r 1363 4),([103,0,1,115,48,4,5],([8,313,347,536,913]++r 1367 5),[0]),e6 [285,287] [8,16,56,124,1372,1373,1374],([285,193,0,1,2,3,4],[8,1092,1281,1375],[]),e6 [296] ([8,124]++r 1376 4),([89,185,186,0,1,2,5],[16,62,277,432,433,1066,1067,1069,1325,1380,1381,1382],[0]),u6 [162,57] [8,124,521,523,555,584,795,1383,1384],([178,0,1,2,3,4,268],[8,62,1209,1385,1386],[]),([0,1,2,3,4,53,297],([8,1063]++r 1387 5),[]),e6 [298] ([8,123,124,174,347]++r 1392 4),e6 [299,7] [8,83,333,444,447,868,1396,1397,1398],u6 [122,28] [8,354,440,485,1399,1400,1401],([198,0,1,2,3,179,5],[8,62,554,1092,1129,1402,1403],[0]),e6 [300] ([16,62,83,123,124,174,347,841]++r 1404 4)]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_24_8_0 : checkNodesBT W_24 g_24 F_24 P_24_8 A_24 B_24_7 8 N_24_8_0 = true := by decide +kernel
def N_24_8_1 : List NodeSpec := [([0,1,2,301,4,28,5],[8,277,440,540,1408,1409],[]),e6 [13,302] ([8,56,62]++r 1410 4),e6 [50,13] ([8,16,62,123,334,1249,1272,1273,1278,1280]++r 1414 4),e6 [9,59] ([8,17,62,83,505]++r 1418 4),u6 [77,104] [17,340,428,671,860,1422,1423],e6 [89,205] ([8,62,124,376,1203,1380]++r 1424 6),e6 [89,28] ([8,62,124,277,376,622,1113,1114,1325,1329,1380]++r 1430 4),u6 [77,184] ([17,340,428]++r 1434 4),u6 [9,59,7] [8,16,17,83,335,346,360,489,505,948,949],([303,0,1,2,62,4,59],[8,370,479,562,959,1438,1439],[]),e6 [304] ([8,62,83,333,1124]++r 1440 4),([0,1,2,3,4,129,305],[8,16,153,705,1120,1121,1444,1445,1446],[]),([259,0,1,115,2,4,5],[56,347,1184,1447,1448],[]),e6 [306] [16,83,123,277,335,841,1280,1449,1450,1451],([307,0,1,2,3,4,7],[8,256,277,1452,1453],[]),e6 [185,178,9] [8,16,17,346,489,998,1277,1289],([0,1,2,3,4,33,57],[17,339,1454,1455],[0]),u6 [118,9] ([8,16,17,83,123,346,489]++r 1456 4),e6 [308,104] [8,124,277,671,672,860,862,913,1423,1460,1461,1462],e6 [309] [16,62,123,124,347,841,1063,1335,1463,1464],([0,1,2,3,182,179,5],[8,124,554,1184,1403,1465,1466],[]),([0,1,2,3,4,68,129],[8,124,153,531,636,705,1121,1467,1468,1469],[0]),([310,0,1,2,9,3,4],[62,277,335,346,489,505,1470,1471,1472],[]),e6 [185,178,77] [17,340,428,998,1289,1473,1474],([0,1,2,3,311,5,7],([8,124,277]++r 1475 4),[]),e6 [312] [8,123,174,277,527,841,1196,1479,1480,1481],e6 [313] [16,62,83,123,841,1482,1483,1484],e6 [104,53] ([8,123,671,672,860,913,1064,1082,1461]++r 1485 4),u6 [87,9,7] [8,17,346,360,444,489,505,1116,1489],e6 [314] ([8]++r 1490 4),([50,0,1,2,4,28,59],[8,17,335,1020,1021],[]),([143,1,2,3,4,28,5],[8,485,540,713,1494,1495],[0]),([178,0,1,115,48,4,5],([8,314,347,536,998,1367]++r 1496 4),[0]),([0,1,2,62,4,114,59],([8,52,116,562]++r 1500 4),[0]),e6 [315] ([16,62,123,174,841,1152]++r 1504 4),([0,2,9,3,4,228,5],[83,335,489,505,800,801,1508,1509,1510],[]),([209,0,1,2,4,5,59],[16,62,636,838,1511,1512],[]),([0,1,2,35,28,139,5],[8,72,243,244,355,1513,1514],[0]),e6 [316] ([8,277,1442]++r 1515 4),([0,1,2,317,4,28,5],[8,174,277,485,1519,1520,1521],[]),([193,0,1,2,3,4,191],[16,124,333,476,1152,1227,1522,1523],[]),e6 [118,17] [8,83,124,347,348,575,875,915,1456,1524,1525],([0,1,2,9,4,152,5],[8,83,277,489,505,847,896,898,1526],[]),e6 [318] [8,123,124,347,841,1527,1528],u6 [9,33,28] [8,17,339,346,442,485,489,540,602,1529],([0,1,2,9,3,6,7],[8,17,83,274,283,290,489,499,1530],[0]),e6 [319] ([16,62,83,123,335,841,1329]++r 1531 4),e6 [28,53] [8,527,622,623,1064,1082,1113,1432,1486,1535],e6 [179,53] [8,527,554,1063,1403,1466,1536],e6 [320] ([16,123,124,174,662]++r 1537 4),u6 [50,9] [8,16,17,123,346,489,1249,1299,1457,1541],e6 [321] [8,123,124,347,841,1542,1543],([183,0,1,2,294,4,5],[8,1361,1362,1544],[]),e6 [322] [8,56,123,841,1545,1546,1547],([0,1,2,35,28,5,53],[8,50,243,333,355,1064,1548],[0]),e6 [323] ([56,62,123,174,841]++r 1549 5),([110,0,1,2,62,4,59],[8,16,116,369,370,479,562,959,1554,1555,1556],[0]),e6 [324] ([16,83]++r 1557 4),([0,1,112,3,114,5,59],[648,650,838,918,1561,1562,1563],[0]),([193,0,1,112,3,114,5],([8,650,658,1152]++r 1564 5),[]),e6 [325] [8,123,174,841,1569,1570,1571],u6 [203] [124,333,1124,1129,1341,1572,1573],([185,186,0,1,2,9,5],[16,346,431,432,489,1066,1067,1574],[0]),([185,186,227,0,1,2,5],[431,432,433,1066,1067,1304,1575,1576,1577],[0]),([193,0,1,17,2,3,4,7],([8,335,1245]++r 1578 5),[]),([193,167,0,1,2,3,4,7],([8,1245,1247,1579]++r 1582 4),[]),e6 [326] [8,123,277,335,376,841,1329,1380,1586,1587,1588],e6 [328] ([8,56]++r 1589 5),([0,1,2,9,3,4,59,7],[8,17,83,346,360,489,505,948,949,1594],[0]),e6 [329] ([8,56,62,83,1082]++r 1595 6),e6 [330,179] [8,554,1403,1601,1602],([0,1,2,9,62,4,59],[8,16,17,116,346,479,562,959,1603,1604],[0]),e6 [331] [16,62,123,174,277,841,1117,1200,1212,1605,1606],e6 [178,196] [16,83,335,346,347,1498,1607,1608],([127,259,0,1,2,4,5],([56,347,1109,1184]++r 1609 4),[]),u6 [87,77,7] [17,256,340,428,444,545,1116,1117,1489],([193,171,0,1,2,3,4,7],[8,1245,1247,1579,1582,1613,1614],[]),([103,178,127,0,1,2,3],([83,318,319,1141,1147]++r 1615 5),[0]),u6 [197] [8,511,1620,1621,1622],u6 [50] [8,123,124,174,347,419,841,1623],([193,0,1,2,9,3,4,7],[8,17,335,505,1245,1580,1624],[0]),e6 [265,7] [8,16,83,333,444,868,1052,1054,1625,1626,1627],e6 [50,134] [8,16,124,334,347,1044,1045,1046,1249,1417,1628,1629],e6 [332] ([8,124]++r 1630 4),e6 [333] [8,56,62,123,277,841,1597,1634,1635,1636],u6 [29] [16,17,62,277,335,336,337,485,492,540,1637],([198,0,1,2,3,270,5],[333,527,1180,1181,1638,1639],[]),e6 [334] [8,62,123,841,1640,1641,1642],u6 [167,57] [8,256,333,360,378,426,781,877,1488,1643],e6 [182,233] ([8,16,56]++r 1644 7),e6 [118,171] ([8,83,124,347,575,1456,1459]++r 1651 4),([23,0,1,2,3,6,7],[8,231,274,283,290,366,499,1655,1656],[0]),e6 [9,152] [8,83,489,505,847,896,898,1526,1657],u6 [115,201] ([16,552,1124,1196]++r 1658 6),([85,0,1,2,35,28,5],[8,72,243,244,355,1664,1665,1666],[0]),([0,1,2,3,182,63,5],[8,467,729,976,1184,1667],[0]),e6 [335] ([62,174,256,277,335,360,447]++r 1668 4),e6 [336] ([8]++r 1672 4),e6 [337] ([56,840]++r 1676 6),([36,0,1,2,28,5],[8,17,32,77],[0]),u6 [171,57] [8,182,265,426,781,868,876,1643,1651,1652],([51,0,1,2,35,28,5],[8,17,50,72,243,244,355,1682,1683,1684],[0]),([87,196,0,1,2,4,5],[8,83,346,376,511,1116,1685,1686,1687],[0]),([0,1,115,2,317,4,5],([8]++r 1688 4),[]),([0,1,115,2,3,6,7],[8,55,231,274,283,290,499,1662,1692,1693],[0]),([0,1,2,294,4,28,5],([8,124,277,1361]++r 1694 4),[]),([185,0,1,2,294,4,5],([8,124,1361,1518]++r 1698 4),[]),([0,1,140,3,4,28,5],[8,174,325,442,485,1702,1703,1704],[0]),([103,178,183,0,1,2,3],[317,318,1203,1209,1615,1617,1618,1705],[0]),u6 [9,57] [16,17,124,339,347,555,584,1706],([110,109,0,1,3,4,5],[8,840,922,1707],[0]),e6 [48,7] [8,333,401,402,852,853,1132,1295,1296,1708],e6 [338] [8,16,333,335,1129,1196,1709,1710,1711],([196,186,0,1,2,4,5],[83,511,1189,1712,1713,1714],[0]),e6 [77,289] ([17,545]++r 1715 4),([185,0,1,2,243,4,5],[8,17,998,1719,1720],[]),([0,1,2,3,13,6,7],[8,55,83,231,274,290,499,1280,1721],[0]),([99,0,1,2,3,5,7],[8,277,490,943],[0]),([77,0,1,2,35,28,5],[17,162,243,340,355,1722],[0]),e6 [13,270] [8,1092,1179,1180,1181,1281,1723],([127,0,1,2,26,4,5,7],[8,83,248,333,360,1724,1725],[0]),([0,1,2,104,4,5,59],[17,277,1487,1726,1727],[]),u6 [84,57] [8,397,442,521,555,560,584,731,767,1383,1728,1729,1730],e6 [339] ([8,16,83,277,346]++r 1731 4),e6 [340] ([8,123,124,174,347,841]++r 1735 4),u6 [9,184] [8,16,17,62,346,489,1200,1434,1436,1739,1740],u6 [19] [62,83,335,361,443,444,445,447,453],e6 [341] ([8,56,62,83,1329,1649]++r 1741 5),u6 [23,9,7] [8,17,346,360,444,503,1746],e6 [342] ([8,123,124,174,347,841]++r 1747 4),u6 [9,202] [16,17,83,346,489,820,821,987,988,994,1751],([69,0,2,3,4,5,57],[16,17,351,841],[0]),([185,186,0,1,2,5,68],[431,432,636,1068,1069,1469,1752,1753],[0]),u6 [9,63] [8,62,346,467,505,729,976,979,1754],e6 [188,185] [16,62,83,1733,1755,1756],e6 [343] ([8,124]++r 1757 4),([0,2,9,3,211,4,5],[16,62,346,641,1300,1302,1303,1510,1761],[]),e6 [344] ([8,62,123,174,277,841,1092,1281]++r 1762 4),e6 [9,243] ([8,17,83,505,998]++r 1766 4),([1,66,2,3,215,4,5],([174,1442,1518,1639]++r 1770 4),[0]),([345,0,1,2,3,4,129],[8,531,705,1120,1121,1774,1775,1776],[]),([0,1,2,26,4,5,57],[8,248,360,484,1777],[0]),e6 [346] ([56,1116,1184]++r 1778 4),([185,77,0,1,2,4,5,59],[17,428,1276,1782,1783],[]),e6 [347] ([8,124]++r 1784 4),u6 [178,77,28] [17,340,428,440,485,545,1473,1788],([0,1,2,62,4,59,72],[8,16,52,562,744,1789,1790,1791],[0]),e6 [348] ([8,123,174,841,1325]++r 1792 4),u6 [9,129] [8,16,62,277,346,489,531,1119,1120,1121,1796],([158,1,2,3,4,5,7],[8,333,444,782,1797],[0]),e6 [349] ([62,123,124,174,335,841,1502]++r 1798 5),([219,0,1,2,3,4,129],([16,531,705,1120,1121]++r 1803 4),[0]),u6 [196,7] [8,16,83,277,377,447,1052,1054,1607,1807,1808],([118,0,1,115,2,4,5],[8,347,915,1459,1809,1810,1811],[]),([127,0,1,2,317,4,5],[8,174,347,1109,1521,1690,1812,1813,1814],[]),u6 [29,28] [16,17,62,277,336,337,339,485,492,540,1637],e6 [350] ([16,62,83,123,124,174,347]++r 1815 4),([227,1,2,3,215,4,5],[174,676,1304,1575,1770,1772,1819,1820,1821],[]),([351,0,1,2,9,4,5],[62,277,335,346,489,505,1822,1823,1824],[]),e6 [185,77,7] [17,256,340,428,444,1289,1474],e6 [89,282] [8,83,124,1825,1826,1827],u6 [200] ([62,123,174,277,547,636,841,1469]++r 1828 4),e6 [352] ([8,56,123,277,335,347,841,1374,1597]++r 1832 4),u6 [185,9,7] [8,17,83,346,360,444,489,1289],([127,0,2,3,4,228,5],[83,801,803,1141,1147,1508,1509,1836,1837,1838],[]),e6 [353] [16,62,83,1498,1839,1840],([0,1,3,4,114,5,233],[8,124,1648,1841,1842,1843],[]),e6 [354] ([8,16,56,1109,1649]++r 1844 6),([0,1,2,9,4,28,5,59],[8,16,17,346,489,505,776,918,1353,1850],[0]),e6 [355] [8,56,62,123,841,1851,1852,1853],([178,77,0,1,2,3,4,59],[17,428,545,1070,1854],[]),e6 [356] ([8,17,62,83,1033]++r 1855 4),u6 [9,28,7] [8,17,346,375,489,505,1859],u6 [90,28] [8,333,485,1399,1860,1861,1862],u6 [9,7,57] [8,17,346,426,444,447,781,868,1863],e6 [357] [8,123,124,347,841,1864,1865],e6 [358] ([56,62,83,123,335,505,841]++r 1866 4),u6 [118,9,7] [8,17,83,346,444,489,505,575,1456],e6 [359] ([8,123,174,841,1141]++r 1870 4),e6 [360] [56,124,1151,1182,1874,1875,1876],u6 [134,33] ([8,382,540,602,757,759,1045,1529]++r 1877 6),([0,1,160,3,4,5,57],[8,17,347,517,519,1883],[0]),([0,1,2,9,35,28,5],[8,16,17,243,244,355,489,1884],[0]),e6 [122] [8,16,354,440,540,1400,1401],e6 [89,118] [8,270,277,575,915,1325,1329,1433,1456,1885],u6 [9,104] [16,17,83,346,671,672,860,913,1487,1886],e6 [361,202] [8,333,347,820,821,994,1083,1887,1888],e6 [50,214] ([8,16,174,334,1249,1299,1417]++r 1889 6),([0,1,2,276,4,5,59],([16,83,124,335,1230]++r 1895 4),[]),e6 [362] [8,277,335,922,1899,1900,1901],e6 [89,104] [8,124,376,671,672,860,862,913,1329,1433,1487,1902],e6 [363] ([8,123,124,174]++r 1903 4),([103,178,0,1,2,9,3],[83,317,318,489,505,1615,1617,1907],[0]),e6 [77,129] [153,340,428,1120,1121,1274],([87,248,0,1,2,4,5],[8,527,1063,1908],[]),e6 [364] [8,56,62,1370,1909,1910],u6 [77,63] [428,467,545,976,981,1911],u6 [116] [8,124,174,617,618,1657,1662,1912,1913],([0,1,2,3,4,53,191],[16,83,476,1064,1226,1914,1915],[]),u6 [9,26,7] [8,17,346,360,436,444,447,489,505,868,1916]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_24_8_1 : checkNodesBT W_24 g_24 F_24 P_24_8 A_24 B_24_7 8 N_24_8_1 = true := by decide +kernel
def N_24_8_2 : List NodeSpec := [([0,1,112,62,3,114,5],([648,650,979,1566]++r 1917 4),[0]),([103,0,1,2,3,311,5],([8,124,1325]++r 1921 4),[]),([0,1,2,35,28,135,5],[8,162,244,355,1925,1926,1927],[0]),e6 [366] ([8]++r 1928 4),([0,1,2,286,4,5,59],([16,83,335,928]++r 1932 4),[]),e6 [367] ([16,83,124,1473]++r 1936 4),([310,77,0,1,2,3,4],[340,428,545,1470,1940,1941],[]),u6 [77,57] [17,124,523,555,584,1942],([77,0,1,2,4,152,5],[187,340,545,896,898,1204],[]),([87,77,0,1,2,4,28,5],[17,340,428,481,545,1943,1944,1945],[0]),([229,0,1,2,4,28,5],[8,277,440,1946,1947,1948],[]),([158,1,2,3,4,28,5],[8,333,350,485,559],[0]),u6 [77,28,7] [17,340,428,444,485,545,1859,1949],([77,0,1,2,3,6,7],[17,55,290,340,499,1950],[0]),e6 [368] ([8,16,56,1273,1597]++r 1951 4),([103,178,77,0,1,2,3],[340,545,1615,1617,1955,1956],[0]),([185,186,190,0,1,2,5],[431,432,1033,1066,1067,1069,1690,1957],[0]),u6 [13,191] [16,83,124,476,1092,1225,1226,1227,1280,1915,1958],u6 [119] [8,16,62,277,346,377,497,1116,1687,1959,1960],u6 [77,33,28] [17,340,428,440,442,485,602,1529,1961],([248,0,1,2,4,5,59],[62,83,174,1057,1962,1963],[]),([0,1,134,3,4,135,5],[8,440,442,711,1044,1964,1965,1966],[0]),u6 [77,28] [17,340,418,428,545,622,1113,1967,1968],([185,186,77,0,1,2,5],[340,428,1066,1067,1068,1969],[0]),([103,246,0,1,2,3,5],[8,1064,1970,1971],[]),e6 [369,7] [8,17,83,333,444,1052,1972,1973,1974],e6 [77,202] [17,340,428,820,994,995,1975],u6 [77,59,7] [17,340,428,545,948,949,953],e6 [370] ([16,83,124,1934]++r 1976 5),u6 [188,28] [8,16,62,83,376,540,1399,1755,1981,1982,1983],([183,0,2,3,4,228,5],[800,801,1203,1209,1508,1509,1837,1984],[]),e6 [77,59] [17,428,1419,1420,1985,1986],([77,0,2,3,4,228,5],[340,545,802,1508,1509,1987],[]),([0,1,2,3,4,191,59],([16,62,83,124,476]++r 1988 4),[]),([0,1,2,3,4,53,129],[8,16,153,531,705,1063,1064,1120,1121,1992],[]),([214,0,1,2,35,28,5],[8,16,17,50,72,162,243,244,333,355,1894,1993],[0]),e6 [77,242] ([17,428]++r 1994 4),u6 [77,7,57] [17,426,428,781,868,1998,1999],([371,287,0,1,3,4,5],([8,277,418]++r 2000 5),[]),([0,1,66,35,3,4,68],[394,396,644,675,1186,1252,1796,2005,2006],[0]),([351,77,0,1,2,4,5],[340,428,545,1822,2007,2008],[]),u6 [23,77,7] [17,256,428,444,503,1746,2009],e6 [372] ([16,62,83,123,124,174,347,841]++r 2010 4),([0,2,3,211,4,5,68],[636,641,642,1303,2014,2015,2016],[0]),e6 [373] [8,2017,2018,2019],([196,0,1,2,4,5,59],[83,335,346,922,2020,2021],[]),([0,1,2,4,88,28,5],[8,62,345,2022],[0]),e6 [9,242] [8,16,17,62,346,1994,1996,2023,2024,2025],([0,66,2,3,211,4,5],[641,642,1300,1302,1303,1518,2016,2026,2027],[0]),([259,0,1,2,4,28,5],[8,56,174,277,2028,2029],[]),e6 [77,7] [17,340,401,428,545,852,856,2030],e6 [77,243] [17,545,1767,1768,2031,2032],u6 [87,103,9] [8,83,346,489,505,913,1115,1116,1118,1200],e6 [9,289] [8,17,83,505,1328,1715,1717,2033,2034],([185,0,1,2,317,4,5],[8,1521,1690,2035,2036],[]),e6 [374] [8,123,124,347,841,2037,2038],e6 [375] [8,277,1196,2039,2040,2041],([190,0,1,2,3,4,297],[8,62,1389,1391,2042],[]),([1,2,3,215,4,5,68],[636,1469,1772,1773,1820,2043,2044],[0]),e6 [376] [8,56,123,174,440,841,2045,2046],e6 [377] [8,124,347,1335,1690,2047,2048],([378,0,1,2,4,152,5],[8,389,847,896,898,2049,2050,2051],[]),e6 [118,53] [8,17,83,123,575,915,1082,1456,1486,1811,2052,2053],e6 [28,379] [8,16,376,440,2054,2055],([87,0,1,2,9,4,28,5],[8,16,17,62,346,481,489,505,1945,2056],[0]),([190,0,2,3,211,4,5],[641,1300,1302,1303,1690,2016,2057],[]),([254,190,0,1,3,4,5],[1033,1079,1690,2058,2059,2060],[]),e6 [380] ([8,2004]++r 2061 4),([190,0,1,2,3,4,129],[8,56,123,531,705,1033,1120,1121,1690,2065],[]),([0,1,2,48,4,152,5],[8,124,187,389,847,898,1132,2066,2067,2068],[]),u6 [128,7] [8,444,595,868,1052,1054,2069],([127,1,2,3,4,199,5],[277,335,535,537,538,1109,1141,1147,2070,2071],[]),([381,0,1,2,3,28,5],[8,56,277,440,2072,2073,2074],[]),e6 [382] ([83,124,174,1227]++r 2075 4),e6 [383,53] ([8,83]++r 2079 4),e6 [384] [8,123,124,347,841,2083,2084],([229,193,0,1,2,4,5],[8,811,1365,1505,2085,2086,2087],[0]),([0,1,153,2,4,152,5],[8,389,896,898,2088,2089,2090],[0]),([0,1,2,3,179,5,7],([8,124,335,360,554]++r 2091 4),[]),e6 [385] [8,16,17,335,1203,1857,2095,2096,2097],([103,0,1,2,3,179,5],([8,62,124,554,1662]++r 2098 4),[]),([190,0,1,2,35,28,5],[8,72,243,244,355,1033,2102],[0]),e6 [50,84] [8,16,124,334,347,560,1249,1299,1730,2103,2104,2105],e6 [167,7] [8,123,333,401,402,852,856,893,2106,2107],u6 [180] ([8,123,124,174]++r 2108 5),e6 [386] ([8,123,124,174,347,841]++r 2113 4),([23,118,0,1,2,4,5],[8,353,360,915,2117],[0]),e6 [387] ([16,62,83,123,124,174,347]++r 2118 4),([162,0,1,3,4,28,5],[8,210,440,540,795,1384,2122],[0]),([178,0,1,2,3,4,297],([8,62,124,1389]++r 2123 5),[]),([103,178,212,0,1,2,3],[317,318,319,1037,1615,1617,2128,2129,2130],[0]),e6 [388] ([8,123,124,174,347]++r 2131 4),([0,1,2,3,194,4,7],[8,335,504,2135],[0]),e6 [389] [8,174,1365,1505,2136,2137],e6 [390] ([8,124,174]++r 2138 5),([0,1,115,48,6,4,5],[313,314,536,1148,1367,1657,1869,2143,2144],[0]),([0,1,115,48,4,5,7],[8,256,360,447,2145,2146,2147],[0]),([381,186,0,1,2,3,5],[56,277,2074,2148],[]),([0,1,115,2,4,152,5],[8,187,347,389,847,896,898,1657,1662,2149,2150],[]),([229,0,1,2,62,4,5],[8,1799,2151,2152],[]),([371,0,1,2,3,4,59],[16,62,838,2153,2154,2155],[]),e6 [391] ([8,123,124,174,347,841]++r 2156 4),e6 [392] ([8,123,174,1662]++r 2160 4),([103,178,0,1,115,2,3],[317,318,1615,1617,1618,1662,1956,2124,2164,2165],[0]),e6 [393] ([8,123,124,174]++r 2166 4),e6 [371,28] [8,16,62,277,376,440,485,540,1399,1982,2155,2170,2171],e6 [48,202] [8,397,820,821,987,988,994,1083,1132,1295,1296,2172],e6 [394] ([8,62,123,277,347,377,841,1109,1147]++r 2173 4),([371,193,0,1,2,3,4],[8,62,376,1505,2155,2177],[]),e6 [395] [8,62,123,277,346,376,841,1919,2178,2179],e6 [396] ([8,62,123,124,174,841]++r 2180 4),e6 [397] ([8,56]++r 2184 6),([0,1,2,35,28,5,57],[8,17,50,72,244,355,2190,2191],[0]),([50,178,0,1,2,3,4],[8,277,341,2192],[0]),e6 [13,311] ([8,16,62]++r 2193 4),([1,2,3,48,4,199,5],[537,538,1132,1296,2068,2197,2198],[0]),u6 [118,77] [17,174,340,418,428,575,1314,1811,2199],([0,2,3,48,4,228,5],[800,801,802,1132,1837,2068,2200,2201],[0]),([99,0,1,2,62,4,59],[8,17,23,62,370,479,562,959,2202,2203,2204],[0]),u6 [187] ([123,174,277,335,449,841,1132,2068]++r 2205 4),([77,0,1,2,4,28,5,59],[17,340,428,545,776,1353,2209,2210],[]),u6 [49] [8,83,124,256,422,447,2211,2212],([0,1,2,26,4,59,7],[8,333,360,374,377,2213],[0]),e6 [398] ([8,124,277,1035,1132,1370]++r 2214 4),u6 [67] [8,124,174,395,1518,2218,2219,2220],([103,178,0,1,2,3,48],[317,318,1132,1618,1956,2068,2221,2222],[0]),e6 [399] [8,16,124,1498,1788,2068,2223,2224,2225],([0,1,134,2,35,28,5],[8,16,17,72,243,244,333,355,382,2226,2227],[0]),([186,0,1,2,3,383,5],([8,124,1141]++r 2228 5),[]),e6 [400] [8,123,124,347,841,2233,2234],e6 [50,127] [8,277,334,487,1109,1141,1249,1417,2235,2236,2237],e6 [285,28] [8,16,62,277,442,485,540,1294,1372,1399,1663,1982,2238,2239,2240],e6 [401] ([8,123,124,174,347,841]++r 2241 4),u6 [28,233] [8,16,124,442,485,1399,1644,1645,1646,1650,2245,2246],u6 [222,63] [8,333,467,729,976,2247],([0,1,2,3,4,233,59],([8,16,124,1650]++r 2248 4),[]),([127,0,1,2,4,152,5],[83,347,389,847,896,898,1141,1147,2252,2253],[]),e6 [402,7] [8,83,256,377,444,1052,1054,2254,2255,2256],([127,0,1,2,3,6,7],[8,17,83,231,283,290,322,499,1141,2257,2258],[0]),e6 [128] [8,83,174,277,377,595,1092,2069,2259,2260,2261],u6 [127,167,7] [8,17,333,444,868,881,1052,2235],([193,0,1,2,3,4,233],[8,16,124,377,1147,1650,2262],[]),e6 [127,7] [8,83,124,277,335,377,401,402,852,853,1109,1141,1147,2107,2235,2263,2264],u6 [50,77] [17,174,334,340,418,428,1249,1278,1314,2265],([0,1,2,3,4,251,7],[8,256,277,360,447,2266,2267],[]),e6 [403] [8,123,124,347,841,2268,2269],([212,1,2,3,4,199,5],[174,535,537,538,1037,2070,2128,2270,2271],[]),([212,0,2,3,4,228,5],[800,801,803,1037,1508,1509,2128,2272,2273],[]),([212,0,1,2,4,152,5],[8,124,847,896,898,1037,2274,2275],[]),([89,0,1,2,3,4,129],[16,347,531,705,1120,1121,1325,1380,2276,2277],[]),e6 [404] ([62,123,174,277,335,339,440]++r 2278 4),([0,1,2,3,383,28,5],([8,124,2229]++r 2282 4),[]),([212,0,1,2,3,6,7],[8,274,283,290,322,499,1037,2286,2287],[0]),e6 [405] [8,62,123,174,841,998,1788,2288,2289],([87,0,1,2,276,4,5],[16,124,277,333,662,1230,2290,2291],[]),e6 [406] ([16,83,124,174]++r 2292 4),([178,0,1,2,3,4,251],[8,62,347,1498,2128,2296,2297],[]),u6 [113] [174,333,649,662,979,1227,2298,2299,2300],([0,2,3,211,4,5,53],[16,641,642,1063,1300,1302,2016,2301],[]),e6 [407,191] [16,17,83,333,476,1225,1226,2302,2303,2304],([127,118,0,1,2,4,5],[8,16,17,83,347,915,1103],[]),([208,0,1,2,62,4,59],[16,116,479,562,657,959,1212,2305,2306,2307],[0]),e6 [408,191] [8,16,83,333,476,1227,1915,2308],e6 [350,191] ([16,17,62,124,476,1225,1915,2303]++r 2309 4),([0,1,112,2,62,4,59],[16,52,116,370,479,562,662,959,2313,2314,2315],[0]),([87,0,1,112,3,114,5],[8,347,648,658,1200,1564,1566,1687,2316,2317,2318],[]),e6 [84,28] [8,62,124,277,622,623,1113,1220,1430,1432,1968,2319,2320],e6 [409] ([8,123,124,174,347]++r 2321 4),([0,1,3,265,4,114,5],([8,124]++r 2325 4),[]),e6 [410] ([8,277,376,1092]++r 2329 6),e6 [13,202] [8,820,821,987,988,993,994,1272,1273,1280,1416,2335],([185,229,0,1,2,4,5],[8,56,811,1474,1502,1948,2336,2337],[]),u6 [160,57] [8,17,333,339,347,517,519,521,555,584,1383],u6 [230] ([8]++r 2338 5),([227,0,1,2,35,28,5],[8,243,244,355,688,1575,2343,2344],[0]),([0,1,2,3,114,63,5],[8,124,467,729,981,1502,2345,2346],[0]),([77,0,2,3,211,4,5],[340,428,642,1300,1302,1987,2347],[]),e6 [411] ([8,123,124,174,347]++r 2348 4),([0,1,2,35,28,5,68],[8,50,72,162,244,1469,2352,2353],[0]),e6 [412] [8,838,922,2354,2355],u6 [9,7] [8,17,83,335,346,401,402,489,505,852,2264,2356],e6 [413] [8,1117,1502,1687,2357,2358],([77,0,1,2,3,4,59,7],[17,340,428,545,948,949,953,2359],[0]),([307,178,0,1,2,3,4],[8,56,277,1788,2360],[]),([0,115,2,3,4,228,5],[800,801,802,1508,1509,1662,1837,2124,2361,2362],[0]),u6 [77,26,7] [17,256,340,428,436,444,545,868,1916,2363],e6 [414] ([8,56]++r 2364 7),e6 [415] ([8,123,124,174,347]++r 2371 4),([118,0,1,2,4,5,59],[8,17,62,946,947],[0]),e6 [416] ([8,123,124,174,347]++r 2375 4),([0,1,130,2,3,4,129],([8,705,1120,1121]++r 2379 4),[0]),e6 [417] [8,1189,2383,2384],([0,1,2,3,4,302,7],([8,56,124,277,868]++r 2385 4),[]),e6 [418] ([8,124,174]++r 2389 4),([178,0,1,2,3,4,302],[8,56,124,1553,2393,2394,2395],[]),([0,1,66,2,35,28,5],[8,50,72,162,243,244,355,1639,2396,2397],[0]),([287,209,0,1,3,4,5],[8,277,347,418,635,2398,2399,2400],[]),([50,193,0,1,2,3,4],[8,17,62,2401,2402],[]),e6 [419] ([56,174,335,1374,1553]++r 2403 4),([185,0,1,66,3,4,68],[8,347,394,675,1186,1277,1733,2407,2408,2409],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_24_8_2 : checkNodesBT W_24 g_24 F_24 P_24_8 A_24 B_24_7 8 N_24_8_2 = true := by decide +kernel
def N_24_8_3 : List NodeSpec := [([287,0,1,2,62,4,59],[8,370,479,562,657,959,1374,2410,2411,2412],[]),([87,0,1,2,265,4,5],[8,16,124,376,1380,2413],[]),e6 [420] [56,62,123,174,335,841,1374,2414,2415,2416],([0,1,2,421,4,5,59],[8,83,335,838,918,922,1212,2417,2418],[]),([87,0,1,2,421,4,5],[16,277,347,376,1117,1212,1687,2419],[]),e6 [422] ([8,16,83]++r 2420 5),([209,0,1,2,35,4,5],[16,83,547,2425,2426],[0]),([186,209,0,1,2,4,5],[16,83,635,1189,2427,2428],[0]),u6 [83,28] [8,333,442,457,485,540,1086,1087,1089],([87,214,0,1,2,4,28,5],[8,481,1893,1894,1944,1945,2429,2430,2431],[]),e6 [423] [174,335,449,1037,1148,1657,1869,2128,2432,2433],e6 [424] ([16,62,83,123,174,277,841]++r 2434 5),([178,0,1,2,3,4,242],[8,17,62,1277,2025,2439,2440],[]),e6 [127,201] ([16,83,124,277,377,552,1124,1141,1659,1661,1663]++r 2441 5),([1,115,2,3,4,199,5],[174,537,1196,1662,2070,2124,2198,2446],[0]),([36,0,1,2,5],[32,77],[0]),([69,0,2,3,4,5,59],[8,16,17,2447],[0]),([0,1,2,3,4,425,59],[8,16,62,838,918,922,1213,2448,2449],[]),([193,0,1,2,3,4,425],[16,62,347,376,1152,1213,1505,2450],[]),e6 [426] ([16,62,123,174,841]++r 2451 5),([0,1,17,2,3,4,59,7],[8,308,333,948,949,950,955,2456],[]),e6 [427] ([62,174,277,335,838,918,922]++r 2457 4),([103,178,0,1,2,3,13],[83,317,1280,1281,1615,1617,1618,1956,2461],[0]),([89,1,2,3,215,4,5],[62,277,676,1325,1329,1380,1770,1772,1820,2462],[]),([0,1,2,3,270,28,5],([8,62,124,1180]++r 2463 4),[]),([186,0,1,2,3,270,5],([8,124,1180,1639]++r 2467 4),[]),([0,1,66,3,4,28,68],[339,394,396,440,2471,2472,2473],[0]),([0,1,66,2,3,4,129],[8,153,347,531,705,1120,1121,1518,1639,1796,2474,2475],[]),e6 [428] [83,123,124,335,347,841,1281,1867,2476,2477],([185,186,0,1,66,2,5],([431,432]++r 1066 4++[1518,1639,2478,2479]),[0]),e6 [429] ([8,174,1639]++r 2480 4),u6 [99,9] [8,16,17,123,346,489,505,1457,2484,2485,2486],([77,0,1,2,62,4,59],[17,52,428,479,959,2487,2488],[0]),u6 [28,68] [8,622,623,1113,1469,2044,2489,2490],e6 [430] [8,16,636,1474,1733,2491,2492,2493],e6 [431] [8,1189,2428,2494,2495],([162,0,1,3,4,5,57],[8,17,124,418,523,795,1384],[0]),([87,209,0,1,2,4,5],[16,376,635,636,1117,2496,2497,2498],[]),([89,0,1,2,35,28,5],[8,72,243,244,333,355,688,1325,2499,2500],[0]),e6 [118,68] [8,83,1459,1811,2044,2489,2501,2502],([365,0,1,2,3,5,7],[8,256,277,2503,2504],[]),e6 [104,68] [8,182,671,672,860,913,1469,1487,2044,2489,2505],e6 [432] ([8]++r 2506 4),e6 [118,167] [8,17,83,174,575,880,881,915,1456,1459,2510,2511],([103,365,0,1,2,3,5],[56,1469,2512,2513],[]),([0,1,2,265,4,5,59],([83,124]++r 2514 5),[]),([0,2,3,13,4,228,5],[83,800,802,1281,1508,1509,1837],[]),e6 [433] ([16,174,335,1380,2006]++r 2519 4),([89,0,2,3,211,4,5],[16,643,1300,1302,1303,1380,2016,2523,2524],[]),e6 [90] [76,442,527,1860,1861,1862,2525,2526],e6 [209,7] [8,83,256,277,377,444,447,1052,1054,2527,2528],e6 [434] ([16,83,123,174,1380]++r 2529 4),u6 [49,7] [8,256,444,1052,1054,2211,2212],u6 [216] [174,979,1212,1213,1799,1919,2533,2534],([185,0,1,2,301,4,5],[8,56,347,1304,2535,2536,2537],[]),e6 [13,7] [8,401,402,852,1092,1272,1273,1280,2107,2538],e6 [435] ([8,123,174,277,841]++r 2539 4),([0,1,2,4,28,59,7],[8,17,62,277,2543,2544],[]),e6 [436,270] [8,1180,1181,2545,2546],e6 [438] [8,56,123,174,841,2547,2548,2549],e6 [439] [174,547,1252,1304,1575,1796,2006,2550,2551],e6 [440] [8,124,347,1203,1657,1867,2552,2553],([227,0,1,2,3,4,129],[8,124,531,1120,1121,1304,1575,2554,2555],[]),e6 [441] [8,123,174,277,841,1474,2556,2557,2558],([185,0,1,2,288,4,5],[8,56,124,1374,2559,2560],[]),e6 [442] [8,123,174,841,2428,2561,2562],e6 [134,28] [8,17,347,382,622,623,1113,1430,2563,2564],([69,0,2,3,4,5],[8,16,83,351,605,606],[0]),([0,1,2,3,4,129,131],([8,153,531,705]++r 2565 4),[0]),u6 [178,9,28] [16,17,339,346,485,489,505,1473],u6 [118,77,7] [17,256,340,428,444,545,575,1456,1811],([220,0,1,2,3,4,129],([8,153,531,705,1120,1121]++r 2569 4),[0]),([0,1,2,35,33,28,5],[8,50,72,243,244,572,1881,2573],[0]),([172,171,0,1,3,4,5],[8,447,868,2256,2574],[0]),e6 [443] ([8,62,174,347]++r 2575 4),([141,0,1,3,4,28,5],[8,540,588,2579,2580,2581],[0]),([0,1,2,3,4,297,7],([8,124,277,360,1389]++r 2582 4),[]),u6 [28,224] [8,16,333,2586,2587,2588],([87,0,1,134,2,4,28,5],([8,62,382,481,1945,2430]++r 2589 4),[0]),u6 [134,57] [8,333,376,522,540,555,584,764,1044,1383,2593],([85,84,0,1,3,4,5],[8,56,442,540,1730,2594],[0]),([84,0,1,2,4,28,5,59],[8,62,376,776,918,1220,1353,1355,1357,1358,2210,2595,2596],[]),e6 [444] ([8,123,124,174,347,841]++r 2597 4),([87,84,0,1,2,4,28,5],[8,481,1220,1944,1945,2430,2601,2602,2603],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_24_8_3 : checkNodesBT W_24 g_24 F_24 P_24_8 A_24 B_24_7 8 N_24_8_3 = true := by decide +kernel
def N_24_8 := N_24_8_0 ++ N_24_8_1 ++ N_24_8_2 ++ N_24_8_3
def B_24_8 : BT (List (List Nat)) := buildBucketsBT W_24 N_24_8
set_option maxRecDepth 500000 in
lemma B_24_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_24 8 xs.toFinset) B_24_8 := by
  have hP := buildPoolsSubBT_sound (pdepth := 12) (W := W_24) (raw := r_24) (pspecs := ps_24) (used := U_24_8) S_24_ok
  have hm0 := checkNodesBT_mem (by decide) gp_24 W_24_ok hP A_24_ok B_24_7_ok C_24_8_0
  have hm1 := checkNodesBT_mem (by decide) gp_24 W_24_ok hP A_24_ok B_24_7_ok C_24_8_1
  have hm2 := checkNodesBT_mem (by decide) gp_24 W_24_ok hP A_24_ok B_24_7_ok C_24_8_2
  have hm3 := checkNodesBT_mem (by decide) gp_24 W_24_ok hP A_24_ok B_24_7_ok C_24_8_3
  exact buildBucketsBT_of_mem (forall_append (forall_append (forall_append (hm0) hm1) hm2) hm3)
def U_24_9 : List Nat := ([8,16,17,20,23,56,62,83,123,124,174,182,256,277,308,333,335,339,340,346,347,355,360,376,377,382,397,418,428,440,442,444,447,449,485,489,499,501,505,527,540,545,547,555,636,662,744,767,781,838,840,841,852,853,857,860,862,868,875,876,893,896,913,918,922,928,948,950,959,976,977,979,987,988,994,998,1027,1029,1033,1035,1037,1044,1046,1050,1052,1054,1063,1064,1066,1071,1079,1082,1083,1092,1109,1113]++r 1115 4++[1120,1124,1129,1132,1141,1147,1148,1151,1152,1179,1181,1182,1184,1185,1186,1189,1190,1196,1200,1203,1209,1212,1213,1215,1217,1220]++r 1225 4++[1232,1234,1249,1252,1256,1262,1272,1273,1277,1280,1281,1289,1295,1296,1300,1304,1323,1324,1325,1328,1329,1335,1341,1353,1355,1360,1362,1365,1367,1370,1371,1374,1380,1383,1388,1391,1399,1403,1411,1413,1414,1419,1424,1426,1430,1433,1436,1442,1456,1457,1466,1469,1470,1473,1474,1486,1487,1489,1498,1499,1502,1503,1505,1508,1518,1524,1529,1551,1553,1563,1564,1568,1575,1578,1579,1580,1583,1597,1602,1604,1613,1615,1625,1639,1645,1646,1648,1649,1651,1653,1657,1659,1661,1662,1663,1687,1690,1691,1712,1717,1730,1733,1746,1761,1767,1770,1788,1796,1799,1802,1821,1822,1857,1859,1863,1867,1869,1878,1889,1915,1916,1919,1920,1945,1948,1982,1996,1999,2000,2006,2025,2044,2052,2059,2068,2070,2074,2081,2082,2103,2124,2128,2147,2155,2194,2196,2229,2235,2271,2307,2309,2315,2318,2327,2347,2394,2409,2412,2416,2428,2442,2473,2484,2488,2489,2496,2510,2535,2546,2589,2591,2601]++r 2604 413)
def P_24_9 : BT (Option BoundPool) := buildPoolsSubBT 12 W_24 r_24 S_24 ps_24 U_24_9
def N_24_9_0 : List NodeSpec := [u6 [243] [8,83,124,174,277,335,347,998,1767,2604],u6 [104] [8,17,83,124,174,277,347,860,862,913,1487],u6 [118,7] [8,62,277,335,444,447,868,1052,1054,1456,2605],u6 [118] [8,83,123,124,174,277,335,347,841,1456,2605],u6 [7,57] [8,62,444,447,781,868,876,1052],u6 [26,7] [8,277,333,335,360,377,444,447,868,1916,2606],u6 [172,7] [8,333,347,444,868,1052,2607,2608],([0,1,2,3,6,7],[277,499,501],[0]),([351,0,1,2,4,5],[62,277,335,1822,2609],[0]),([0,1,2,4,152,5],[277,335,896,2610],[0]),([274,0,1,3,4,5],[124,277,335,1217,2611],[0]),([0,1,3,4,445,5],[277,335,418,2612,2613],[]),([0,2,3,4,228,5],[277,335,1508,1761],[0]),([1,2,3,4,199,5],[174,277,335,2070],[0]),([193,0,1,2,3,4,7],[8,83,277,335,360,1579,1580],[0]),u6 [87,103] [277,335,913,1115,1116,1118,1200,1324,1370,1687,2416,2614,2615,2616],u6 [59] [8,16,62,124,174,277,335,347,1419,2617],u6 [35,68] [16,124,335,547,636,1252,1469,1796,2044,2489,2618,2619],([127,0,1,3,4,114,5],[8,62,124,277,418,1141,2620,2621],[0]),u6 [233] [16,62,124,174,277,347,1092,1147,1645,1646,1648,2622],u6 [51,28] [8,17,339,376,442,485,540,1050,1399,2623],u6 [127,186] ([16,17,62,124,277,347,987,1109,1141,1147,1189,1712]++r 2624 4),u6 [371] [16,62,123,124,174,277,376,418,841,2000,2155,2628,2629],u6 [383] [8,83,124,174,335,347,2081,2082,2229,2630,2631],u6 [87,114] ([8,124,347,1116,1502,1503,1687]++r 2632 4),u6 [186,48] [16,62,124,347,987,1132,1189,1295,1296,1712,2068,2428,2636,2637],u6 [48,28] [8,62,83,124,277,440,540,2068,2638,2639],u6 [48,7] [8,16,83,256,277,360,447,868,2068,2640,2641],([287,0,1,3,48,4,5],[8,62,124,277,418,1374,2642,2643],[0]),([0,1,115,48,4,5],[62,182,347,418,1367,2644],[0]),u6 [179] [8,62,124,174,335,1403,1466,1602,1662,2645],u6 [244] [8,62,124,174,335,1027,1029,1033,2646,2647],u6 [167,7] [8,16,256,333,360,444,447,868,893,1052,1583,2510],u6 [246] [8,16,62,123,124,174,277,347,841,2648,2649,2650],u6 [178,13] [8,62,83,123,174,277,998,1272,1273,1281,1414,1473,1498,1788,2651,2652,2653],u6 [212,7] [8,124,335,360,444,447,1052,2147,2271,2654,2655],u6 [198,115] [16,347,418,1124,1129,1196,1662,2124,2656],u6 [185,7] [8,277,335,360,444,447,868,1052,1289,1733,2657,2658,2659],u6 [185,53] [8,16,123,174,277,335,1063,1082,1289,1474,1486,2052,2659,2660,2661],u6 [28,53] [8,16,17,333,335,440,442,485,1063,1064,1082,1399,2662],u6 [287,53] [8,16,123,174,333,335,418,1063,1064,1082,1486,2052,2663,2664],u6 [186,53] [16,17,123,174,1063,1064,1082,1486,1712,2052,2428,2624,2626,2665],u6 [112,53] [16,123,174,333,335,418,1064,1857,2666,2667],u6 [127,59] [8,16,17,62,83,335,347,840,918,922,928,2668,2669,2670],u6 [87,53] [16,123,174,335,1063,1082,1116,1486,1687,2052,2416,2616,2671],u6 [303,59] [8,17,838,840,922,928,2668,2672],e6 [89,53] [16,123,174,335,347,527,1063,1082,1329,1433,2052,2673],u6 [87,198] [16,174,1116,1129,1200,1262,1687,2416,2616,2674,2675,2676],u6 [185,182] [8,123,174,277,1184,1289,1649,1733,2659,2660,2677,2678,2679],u6 [103,77] [17,174,340,418,428,545,1035,1115,2614,2680],u6 [193,13] [62,83,123,174,1151,1272,1273,1281,1365,1414,1551,2681,2682],u6 [193,112] [16,83,124,347,1151,1152,1227,1365,1505,1551,1857,2315,2667,2683,2684],u6 [23,7] [8,333,360,377,444,447,868,1052,1746,2685],u6 [227,28] [8,62,124,485,540,1399,1821,2473,2686,2687],u6 [89,198] [16,83,174,333,347,418,1129,1325,1329,1433,2675,2676,2688],u6 [327] [8,62,123,335,347,841,2689,2690],u6 [127,198] [16,83,174,347,418,1109,1124,1141,1147,2235,2675,2676,2691],u6 [190,35] [418,1033,1252,1335,1690,1796,2059,2692,2693,2694],u6 [115,182] [8,123,124,174,277,418,1184,1196,2695,2696],u6 [201] [16,62,124,174,277,1124,1659,1661,1663,2442],u6 [178,115] [8,124,347,998,1196,1473,1498,1788,2124,2653,2696,2697,2698],u6 [286] [83,124,174,277,333,335,1129,2699,2700,2701],u6 [270] [8,62,124,174,335,1179,1181,1639,2546,2702],u6 [285] [16,62,123,124,174,277,347,841,1092,1281,2703,2704,2705],u6 [193,48] [62,83,124,347,1151,1295,1296,1365,2068,2706,2707],u6 [198,59] [16,62,83,335,840,922,928,2668,2675,2676,2708],u6 [152] [8,83,124,174,277,335,347,896,1657,2610],u6 [182,59] [8,838,840,928,1184,1649,2668,2709],u6 [185,114] [8,124,277,347,1289,1502,1733,2632,2634,2710,2711],u6 [307] [8,62,123,124,174,277,418,841,2712,2713],u6 [259] [8,56,83,123,124,174,277,333,335,347,841,2714,2715],u6 [114,59] [8,124,838,922,2716,2717],u6 [53,59] [8,16,17,62,335,838,840,928,1063,1082,2668,2718],u6 [62,182] [8,174,277,979,1184,1341,1649,1799,2679,2719,2720,2721],([254,0,1,3,4,5],[62,124,277,1079,2722],[0]),u6 [112,13] [16,62,83,123,124,174,418,1227,1280,1281,1857,2667,2723],u6 [103,59] [8,17,62,335,840,918,922,928,2668,2724,2725],u6 [48,6] [62,83,124,335,449,1132,1657,1869,2068,2726,2727,2728],u6 [63] [8,62,124,174,335,347,976,977,979],u6 [193,9] [8,17,62,83,123,335,346,489,505,1365,1457,1604,2681,2729],u6 [178,77] [174,340,418,428,545,1473,1788,2651,2730],u6 [301] [8,277,335,347,418,1304,2535,2731],u6 [127,53] [16,17,123,174,335,418,1063,1064,1082,1109,1147,1486,2052,2235,2732],u6 [9,59] [8,16,17,62,83,346,489,505,922,928,2668,2733],u6 [77,7] [256,340,428,444,545,1052,1999],u6 [9,28] [8,17,62,83,346,485,489,505,540,1399,2734],u6 [185,190] [8,174,1289,1690,1733,2059,2659,2660,2735,2736],u6 [89,185] [8,16,62,277,335,1289,1329,1380,1433,1733,2409,2659,2660,2737],u6 [127,28] [8,17,62,83,277,347,442,485,540,1109,1141,1147,1399,2738,2739],u6 [183,6] [418,1203,1209,1215,1657,1867,1869,2728,2740,2741],u6 [103,212] [8,347,913,1037,1115,1370,1371,2271,2614,2742,2743],u6 [196] [83,123,277,335,347,377,841,2744,2745],u6 [109,59] [8,62,124,335,838,922,928,2668,2746,2747],u6 [198,66] [333,347,418,1124,1442,1639,2748],u6 [77,6] [124,340,428,449,545,1867,2741,2749],u6 [127,190] [8,62,83,174,418,1033,1109,1147,2059,2235,2736,2750],u6 [182,7] [8,277,335,444,447,868,1052,1649,2679,2751],u6 [33,28] [8,62,277,335,376,442,485,540,1529,1663,1878],u6 [185,9] [8,62,123,277,346,489,505,1457,1733,2660,2752],u6 [35,53] [16,174,335,418,547,1063,1064,1082,1335,1796,2693,2694,2753],u6 [184] [8,16,62,124,174,277,347,1200,1436,2754],u6 [103,115] [8,124,347,913,1035,1115,1196,1324,1370,1662,2696,2755,2756],u6 [28,59] [8,17,62,277,335,339,840,922,1353,1355],u6 [249] [8,62,335,347,418,1037,2757,2758],u6 [87,77] [174,340,418,428,545,1116,1117,2488,2616,2759],u6 [294] [8,83,124,174,277,335,1360,1362,1518,2760,2761],u6 [89,35] [16,335,347,1252,1325,1329,1335,1380,1433,2006,2693,2694,2762,2763],u6 [48,59] [8,16,62,83,124,335,838,922,2764,2765],u6 [193,77] [17,174,340,418,428,545,1151,1505,2488,2681,2766],u6 [186,77] [17,174,340,418,428,545,1712,2428,2624,2767],([0,1,2,35,28,5],[277,355,1228],[0]),u6 [13,7] [8,16,83,256,277,360,444,868,1052,1273,1281,2768],u6 [59,72] [8,16,83,124,744,838,922,2769,2770,2771],u6 [190,28] [8,62,123,442,485,540,1399,2059,2736,2772],u6 [183,7] [8,335,444,447,868,1052,1215,2773,2774],u6 [77,28] [17,340,428,440,485,545,1399,2775],u6 [68,7] [8,16,124,256,277,335,447,636,2776,2777],([185,0,1,2,4,5,59],[8,16,62,335,918,2778,2779],[0]),u6 [103,13] [16,83,123,174,1035,1115,1272,1273,1280,1281,1324,1370,1414,2614,2780],u6 [186,9] [16,17,62,83,123,277,346,489,505,987,1189,1457,2624,2781],u6 [57] [8,16,17,83,123,124,174,347,555,767,1383],u6 [202] [8,16,124,174,277,347,987,988,994,1083],u6 [13,59] [16,62,83,333,335,838,840,928,1281,2668,2782],u6 [178,9] [8,123,277,335,346,489,505,998,1457,1498,2651,2783],u6 [205] [8,62,124,174,335,1203,1424,1426,2647,2784],u6 [59,217] [16,83,333,838,840,928,1234,2668,2785,2786],u6 [381] [8,56,123,124,174,277,335,418,841,2074,2787,2788,2789],e6 [287,182] [8,56,123,174,277,347,1184,1597,1649,2663,2677,2790],u6 [287,190] [8,174,347,418,1597,2059,2663,2791],u6 [302] [8,16,62,124,174,347,1411,1413,2394,2792,2793],u6 [89,59] [8,16,62,83,333,335,347,840,922,928,2668,2794,2795],u6 [178,182] [8,123,174,277,1182,1473,1498,1649,2651,2653,2677,2679,2796],([0,1,2,3,4,59,7],[8,62,83,277,335,360,948,950],[0]),u6 [7,176] [8,174,256,333,444,868,1052,2797],u6 [9,6] [83,124,335,346,489,505,1657,1867,1869,2741,2798],u6 [425] [16,62,277,347,376,418,1213,2799,2800],u6 [115,53] [8,16,123,174,335,418,1063,1064,1196,1662,2124,2696,2801],u6 [74,59] [8,333,347,840,928,2668,2802,2803],u6 [99,59] [8,17,62,277,335,840,922,928,2484,2668,2804],u6 [289] [8,83,124,174,335,347,1328,1717,2805],u6 [9,7] [8,16,277,346,360,444,447,489,505,1052,1863],u6 [17,7] [8,16,308,333,347,444,447,868,875,1052,1524,1578],u6 [190,112] [83,333,347,418,662,1033,1227,1857,2806],u6 [193,182] [8,123,174,1151,1182,1185,1365,1551,1649,2677,2679,2681,2807],u6 [190,115] [8,124,335,347,418,1196,1690,2696,2808],u6 [28,135] [8,124,440,540,1399,2809,2810],u6 [229] [8,123,124,174,277,335,418,841,1948,2811,2812],u6 [13,28] [8,62,83,277,333,440,442,485,1273,1280,1281,1399,2813],u6 [115,7] [8,256,277,335,347,360,444,447,868,1052,1196,2814,2815],u6 [89,186] [16,62,83,277,333,347,1189,1190,1325,1329,1433,1712,2624,2626,2816,2817],u6 [9,35] [16,62,124,346,347,489,505,1252,1335,1796,2694,2818],u6 [112,62] [662,979,1227,1341,1799,1857,1919,2720,2721,2819,2820],u6 [265] [17,62,83,124,174,277,347,527,1380,1625,2327,2821,2822],u6 [282] [8,83,123,124,174,277,335,347,841,2823,2824,2825],u6 [183,112] [16,347,418,662,1203,1209,1227,1857,2826],u6 [13,6] [62,83,418,449,1273,1280,1281,1657,1867,2728,2741,2827],u6 [77,35] [124,340,418,428,545,547,1335,2347,2694],u6 [185,77] [174,340,418,428,545,1289,1474,2660,2828],u6 [182,28] [8,62,277,440,442,485,1184,1399,1649,2829],u6 [287,183] [8,174,347,418,1215,1374,1597,2663,2774,2830],u6 [127,6] [62,83,347,1109,1141,1147,1148,1867,1869,2235,2728,2741,2831,2832],u6 [89,13] [16,62,83,123,174,333,347,418,1272,1273,1281,1325,1329,1380,1414,1433,2833],u6 [87,9] [8,16,62,123,346,489,505,1200,1457,1604,1687,2616,2834],u6 [183,66] [8,62,347,418,1209,1442,2835],u6 [103,48] [16,83,124,335,347,1035,1115,1132,1295,1296,1370,2068,2836,2837],u6 [178,183] [8,174,998,1209,1215,1473,1498,2651,2653,2774,2838],u6 [9,62] [8,124,346,489,505,979,1341,1919,2720,2839],u6 [103,183] [8,174,913,1115,1203,1215,1324,1370,2614,2774,2840],u6 [59,7] [8,16,62,277,335,840,922,928,948,950],u6 [188] [16,62,123,277,347,376,841,2841,2842],([185,186,0,1,2,5],[62,277,1066,2843],[0]),u6 [127,182] [8,17,62,83,123,124,277,418,1109,1141,1147,1184,1649,2235,2677,2679,2844],u6 [77,59] [17,340,428,545,838,928,2668,2845],u6 [66,182] [8,123,174,277,418,1182,1442,2846,2847],u6 [87,287] [8,62,347,1116,1374,1597,2318,2412,2416,2616,2663,2848],u6 [66,13] [8,62,83,123,174,418,1281,1442,1518,1639,2847,2849],u6 [171,7] [8,16,124,256,277,335,360,377,444,447,857,868,1052,1613,1651,1653],u6 [89,7] [8,16,277,335,347,360,444,447,868,1052,1325,1329,1380,2850,2851],u6 [89,183] [8,16,174,335,418,1203,1215,1325,1329,1380,1433,2774,2852],u6 [127,7] [8,16,62,83,277,444,447,868,1052,1109,1147,1256,2147,2853],u6 [103,127] [16,17,83,277,335,347,1109,1115,1141,1147,1324,1371,2235,2614,2854,2855],u6 [178,127] [8,62,83,277,335,1109,1147,1473,1498,1499,2235,2651,2653,2856],u6 [251] [8,62,277,347,418,2128,2857,2858],u6 [212,6] [124,1037,1148,1657,1867,1869,2128,2271,2741,2742,2859,2860],([0,1,66,3,4,68],[335,397,418,1186,2861],[0]),u6 [178,212] [8,347,998,1473,1498,1499,2128,2271,2651,2742,2862],u6 [276] [17,83,124,174,277,333,335,662,1232,1323,2863,2864],u6 [311] [8,16,62,124,174,277,347,1325,2194,2196,2865,2866],u6 [87,182] [8,123,174,1116,1184,1185,1649,1687,2416,2616,2677,2679,2867],u6 [437] [8,62,335,347,418,1575,2868,2869],u6 [191] [16,62,124,174,277,1225,1226,1227,1915,2309],([0,1,112,3,114,5],[20,277,418,1564,2870],[0]),u6 [87,112] [16,124,347,662,1116,1117,1200,1687,1857,2315,2416,2667,2871,2872],u6 [112,59] [16,62,83,335,347,838,840,918,922,928,1857,2668,2873,2874],u6 [287,178] [8,124,277,335,347,1473,1553,1597,2651,2653,2875,2876],u6 [208,62] [979,1212,1213,1341,1919,1920,2720,2877,2878,2879],([89,0,1,3,4,114,5],[8,124,277,335,418,1325,2880,2881],[0]),u6 [287,7] [8,277,335,347,444,868,1052,1597,2882,2883],u6 [103,53] [8,17,123,174,335,1035,1063,1064,1082,1115,1324,1486,2052,2614,2884],u6 [114,28] [8,62,124,277,440,540,2885,2886]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_24_9_0 : checkNodesBT W_24 g_24 F_24 P_24_9 A_24 B_24_8 9 N_24_9_0 = true := by decide +kernel
def N_24_9_1 : List NodeSpec := [u6 [129] [8,16,62,124,174,277,347,1120,1796,2887],u6 [248] [62,83,123,124,174,277,333,347,527,841,1063,2888,2889,2890],u6 [62,114] [8,124,277,979,1502,1799,1802,1919,2634,2891,2892],u6 [193,114] [8,62,124,347,1151,1365,1503,1802,2632,2634,2893,2894],u6 [198,62] [979,1124,1129,1341,1919,2675,2676,2720,2721,2895],([0,2,3,211,4,5],[62,1300,1761],[0]),u6 [114,7] [8,124,256,277,335,447,2896,2897],([0,1,2,3,4,129],[62,277,1120,2887],[0]),u6 [178,114] [8,124,277,347,1473,1498,1802,2632,2634,2898,2899],u6 [193,28] [8,17,62,277,339,442,485,540,1365,1399,1551,2900,2901],u6 [288] ([8,56,83,124,174,277,333,335,347,1374]++r 2902 4),u6 [87,7] [8,277,335,360,444,447,868,1052,1116,1489,1687,2416,2906],u6 [85,28] [8,17,347,442,485,1399,2907,2908],([287,0,1,3,4,5,68],[8,124,335,418,1469,2909,2910],[0]),u6 [178,48] [8,62,83,277,347,998,1295,1296,1473,1498,1788,2068,2653,2911,2912],u6 [53,7] [8,16,256,277,335,444,868,1052,1063,1064,1082,2913],u6 [287,28] [8,62,277,347,442,485,1399,1597,2914,2915],u6 [214,28] [17,333,440,442,485,540,1399,1663,1889],u6 [178,28] [8,62,277,339,442,485,540,1399,1473,1498,2653,2916,2917],u6 [287,185] [8,62,124,277,347,1289,1374,1597,1733,2659,2660,2918,2919],u6 [287,59] [8,347,840,928,1563,1597,2668,2920,2921],u6 [287,13] [8,62,83,123,124,418,1272,1273,1280,1281,1374,1414,1597,2663,2922],u6 [115,6] [347,449,1196,1657,1662,1867,1869,2124,2696,2728,2741,2923,2924],u6 [287,193] [8,335,347,1151,1551,1553,1568,1597,2412,2663,2681,2925],u6 [421] [83,277,335,347,377,418,1212,2926,2927],u6 [186,190] [8,174,1033,1189,1712,2059,2624,2626,2736,2928],u6 [208,59] [16,62,83,124,335,922,928,1563,2668,2879,2929,2930],u6 [87,208] [16,347,1116,1200,1212,1687,2307,2318,2616,2879,2931,2932],u6 [193,208] [16,83,347,1151,1152,1213,1365,1568,2307,2681,2879,2931,2933],u6 [127,193] [8,62,83,124,335,347,1109,1147,1151,1152,1365,1551,2681,2934,2935],u6 [28,7] [8,62,277,335,442,444,447,485,540,868,1859,2936],u6 [66,35] [347,547,1252,1335,1442,1518,1639,1796,2693,2694,2847,2937,2938],u6 [193,198] [16,83,174,1124,1151,1152,1262,1365,1551,2675,2676,2681,2939],u6 [66,28] [8,62,277,339,347,440,442,485,540,1399,1442,2940,2941],u6 [185,66] [8,124,347,1277,1289,1442,1474,1518,1733,2659,2847,2942,2943],u6 [297] [8,16,62,124,174,277,1388,1391,2944,2945],u6 [185,68] [8,16,277,335,347,636,1474,1733,2044,2489,2659,2946,2947],u6 [186,59] [8,17,62,335,840,918,922,928,2668,2948,2949],u6 [186,68] [16,62,83,124,347,636,1189,1469,2044,2428,2489,2950,2951],u6 [287,62] [8,347,1341,1374,1553,1597,1919,1920,2720,2721,2952,2953],u6 [68,59] [8,16,62,83,124,335,838,922,2954,2955],u6 [87,68] [16,124,335,347,636,1116,1687,2044,2489,2956,2957],u6 [7] [8,62,124,174,277,335,347,852,853],u6 [103,68] [83,124,335,347,636,913,1035,1370,1469,2044,2489,2958,2959],u6 [7,75] [8,124,256,447,1052,2960,2961],u6 [186,66] [8,124,347,987,1189,1442,1639,1712,2428,2626,2847,2962,2963],u6 [365] [8,62,123,124,174,277,418,841,2964,2965],u6 [89,28] [8,16,62,83,333,335,442,485,540,1325,1399,2473,2966,2967],u6 [89,87] [8,16,62,124,335,347,1116,1200,1329,1380,1687,2416,2616,2968,2969],u6 [317] [8,83,124,277,335,1690,1691,2970,2971],u6 [263] [8,16,17,56,62,123,124,174,277,347,841,2972,2973],u6 [89,103] [8,83,124,277,335,347,913,1115,1324,1325,1329,1370,1380,2614,2974,2975],u6 [227,35] [124,1252,1304,1335,1575,1796,1821,2006,2694,2976,2977,2978],u6 [185,227] [8,347,1289,1304,1733,1821,2409,2660,2978,2979],u6 [103,9] [16,17,83,123,277,335,346,489,505,913,1370,1457,2614,2980],u6 [186,227] [8,347,1189,1190,1575,1712,1821,2624,2978,2981],([1,2,3,215,4,5],[62,174,277,1770],[0]),([0,1,3,446,4,5],[62,277,347,418,2982,2983],[]),u6 [268] [8,16,62,124,277,2984,2985,2986],([310,0,1,2,3,4],[62,277,335,1470,2987],[0]),([103,178,0,1,2,3],[277,335,1615,2988],[0]),u6 [28,139] [8,174,333,440,442,485,1399,2989,2990],u6 [134,28] [8,83,333,347,382,442,485,540,1044,1046,1399,2589],u6 [84,28] [8,62,83,124,277,339,376,440,442,485,540,1220,1399,1730,2103,2601],([87,0,1,2,4,28,5],[8,16,62,277,335,1200,1945,2591],[0]),u6 [28,57] [8,17,339,442,540,555,1383,1399],u6 [50] [8,16,62,123,124,174,277,347,841,1249,2991],u6 [50,28] [8,62,277,335,442,485,540,1249,1399,1982,2991],u6 [28] [8,17,62,124,174,277,335,347,1113,1430],u6 [242] [8,16,62,124,174,347,1996,2025,2992],e6 [127,13] [62,83,123,174,347,1092,1109,1272,1273,1280,1414,2235,2993],u6 [28,68] [8,16,83,335,440,442,540,636,1469,2994,2995],u6 [185,178] [62,277,998,1277,1289,1473,1498,1733,2651,2653,2659,2660,2996,2997],([0,1,2,4,28,5,59],[8,16,17,62,277,335,918,1353,1355],[0]),u6 [186,193] [17,62,277,987,1151,1152,1189,1365,1551,1712,2624,2626,2681,2998,2999],([0,1,2,62,4,59],[23,62,959,3000],[0]),u6 [77,62] [124,340,418,428,545,1341,1799,2720,3001],u6 [209] [62,83,123,124,174,277,377,418,841,2496,3002,3003],u6 [110,59] [16,17,83,347,840,928,2668,3004,3005],u6 [89,182] [8,16,17,123,174,333,418,1182,1184,1329,1380,1433,1649,2677,2679,3006],([178,0,1,2,3,4,59],[8,62,83,277,335,998,1071,3007],[0]),u6 [60,59] [8,17,62,277,335,840,922,2668,3008,3009,3010],u6 [59,57] [8,17,277,840,922,2668,3011,3012,3013],u6 [186,13] [8,16,62,123,174,333,1189,1272,1273,1280,1281,1414,1712,2428,2624,2626,3014],u6 [100,59] [8,17,840,918,922,928,2668,3015,3016],u6 [99] [8,16,62,83,123,124,174,277,335,347,841,2484,2804]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_24_9_1 : checkNodesBT W_24 g_24 F_24 P_24_9 A_24 B_24_8 9 N_24_9_1 = true := by decide +kernel
def N_24_9 := N_24_9_0 ++ N_24_9_1
def B_24_9 : BT (List (List Nat)) := buildBucketsBT W_24 N_24_9
set_option maxRecDepth 500000 in
lemma B_24_9_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_24 9 xs.toFinset) B_24_9 := by
  have hP := buildPoolsSubBT_sound (pdepth := 12) (W := W_24) (raw := r_24) (pspecs := ps_24) (used := U_24_9) S_24_ok
  have hm0 := checkNodesBT_mem (by decide) gp_24 W_24_ok hP A_24_ok B_24_8_ok C_24_9_0
  have hm1 := checkNodesBT_mem (by decide) gp_24 W_24_ok hP A_24_ok B_24_8_ok C_24_9_1
  exact buildBucketsBT_of_mem (forall_append (hm0) hm1)
def U_24_10 : List Nat := ([20,23,62,123,124,174,182,277,335,347,397,418,1052,1054,1295,1297,1314,1399,1414,1433,1457,1982,2052,2235,2236,2489,2501,2614,2616,2624,2632,2651,2660,2663,2667,2668,2677,2681,2694,2696,2720,2741,2742,2847,2931,2978]++r 3017 22)
def P_24_10 : BT (Option BoundPool) := buildPoolsSubBT 12 W_24 r_24 S_24 ps_24 U_24_10
def N_24_10 : List NodeSpec := [u6 [103] [62,123,124,174,277,335,347,2614,3017],u6 [7] [62,124,174,277,335,347,1052,1054],u6 [48] [62,124,277,335,347,418,1295,1297],u6 [115] [62,123,124,174,277,335,347,418,2696,3018],u6 [190] [62,123,124,174,277,335,347,418,3019],u6 [198] [62,123,124,174,277,335,347,418,3020],u6 [182] [62,123,124,174,277,335,418,2677],u6 [183] [62,123,124,174,277,335,347,418,3021],u6 [66] [62,123,124,174,277,335,347,418,2847,3022],u6 [53] [62,123,124,174,277,335,418,2052],u6 [62] [62,124,174,277,335,347,2720,3023],u6 [287] [20,62,123,124,174,277,335,347,2663,3024],u6 [77] [123,174,418,1314],u6 [127] [62,123,124,174,182,277,335,347,2235,2236],u6 [112] [62,123,124,174,277,335,347,418,2667,3025],u6 [59] [62,124,174,277,335,347,2668,3026],u6 [87] [23,62,123,124,174,277,335,347,2616,3027],u6 [6] [62,123,124,174,277,335,347,2741,3028],u6 [212] [62,123,174,182,277,335,347,418,2742,3029],u6 [35] [62,123,124,174,277,335,347,2694,3030],u6 [185] [62,123,124,174,277,335,347,2660,3031],u6 [178] [62,123,124,174,277,335,347,2651,3032],u6 [13] [62,123,124,174,277,335,418,1414],u6 [186] [62,123,124,174,277,335,347,2624,3033],u6 [9] [62,123,174,277,335,347,1457],u6 [114] [62,124,277,335,347,418,2632,3034],u6 [208] [20,62,123,174,277,335,347,418,2931,3035],u6 [68] [62,124,277,335,347,418,2489,2501],u6 [89] [62,123,124,174,277,335,347,397,1433,3036],u6 [227] [62,123,174,277,335,347,397,418,2978,3037],u6 [28] [62,124,174,277,335,347,1399,1982],u6 [193] [23,62,123,124,174,277,335,347,2681,3038]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_24_10 : checkNodesBT W_24 g_24 F_24 P_24_10 A_24 B_24_9 10 N_24_10 = true := by decide +kernel
def B_24_10 : BT (List (List Nat)) := buildBucketsBT W_24 N_24_10
set_option maxRecDepth 500000 in
lemma B_24_10_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_24 10 xs.toFinset) B_24_10 :=
  buildBucketsBT_sound (by decide) gp_24 W_24_ok (buildPoolsSubBT_sound S_24_ok) A_24_ok B_24_9_ok C_24_10
def U_24_11 : List Nat := [123,841]
def P_24_11 : BT (Option BoundPool) := buildPoolsSubBT 12 W_24 r_24 S_24 ps_24 U_24_11
def N_24_11 : List NodeSpec := [u6 [] [123,841]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_24_11 : checkNodesBT W_24 g_24 F_24 P_24_11 A_24 B_24_10 11 N_24_11 = true := by decide +kernel
def B_24_11 : BT (List (List Nat)) := buildBucketsBT W_24 N_24_11
set_option maxRecDepth 500000 in
lemma B_24_11_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_24 11 xs.toFinset) B_24_11 :=
  buildBucketsBT_sound (by decide) gp_24 W_24_ok (buildPoolsSubBT_sound S_24_ok) A_24_ok B_24_10_ok C_24_11
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_24_ok : forestRootCheck r_24 g_24 [(VAR 0,12,13),(VAR 1,12,14),(VAR 2,9,13),(VAR 3,5,13),(VAR 4,3,19),(VAR 5,2,34)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_24_in : bucketContainsBT B_24_11 r_24 = true := by decide +kernel
lemma low_24 : Lower r_24 g_24 12 := lower_of_forestBT root_24_ok B_24_11_ok root_24_in

def g_orig := (d 0xfeeefee8feeae8c8)
set_option maxHeartbeats 0 in
lemma low_orig : Lower (varsOf 63) g_orig 12 := carry_of (swaps := [(0,5),(1,4),(2,3)]) (by decide +kernel) low_24
def targetFn (x : Fin 6 → Bool) : Bool := Nat.testBit (4277075688 * 2 ^ 32 + 4276807880) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def temoin : List Gate := [⟨.and,[2,3]⟩,⟨.or,[2,3]⟩,⟨.or,[3,5]⟩,⟨.and,[2,1]⟩,⟨.and,[7,5]⟩,⟨.or,[10,4]⟩,⟨.and,[11,8]⟩,⟨.or,[6,1]⟩,⟨.or,[0,12]⟩,⟨.and,[0,11]⟩,⟨.or,[15,13]⟩,⟨.and,[14,16]⟩,⟨.or,[9,17]⟩]
lemma temoin_ok : PEqualNP.MetaComplexity.Monotone2 ⟨temoin, 18⟩ := by
  intro g hg; simp [temoin] at hg; rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxHeartbeats 0 in
lemma tgt_eq_G : ∀ r : Row, targetFn (evalInput6 r) = g_orig.testBit r.val := by decide +kernel
set_option maxHeartbeats 0 in
lemma temoin_eval : ∀ r : Row, Circuit.eval ⟨temoin, 18⟩ (List.ofFn (evalInput6 r)) = g_orig.testBit r.val := by decide +kernel

end PEqualNP.Outside.L_meta_44938

open PEqualNP.Outside.L_meta_44938 in
theorem PEqualNP.Outside.L_meta_44938 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075688 * 2 ^ 32 + 4276807880) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075688 * 2 ^ 32 + 4276807880) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  exact replace_of_lower6 g_orig (by decide) (by decide) (by decide) 12 low_orig temoin 18 (by decide) temoin_ok targetFn tgt_eq_G temoin_eval
