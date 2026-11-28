import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_45150
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
def g_1 := (d 0xe880e880e880e880)
def r_1 : List Nat := varsOf 15
def p_1 : List Nat := [7,7,7,11,11,11,13,13,13,14,14,14]
def q_1 : List Nat := [6,5,3,10,9,3,12,9,5,12,10,6]
def F_1 : Nat := fullMask 12
set_option maxHeartbeats 0 in
lemma gp_1 : goodPairs g_1 p_1 q_1 := goodPairs_of (by decide +kernel)
def W_1 : BT Decor := buildWiresBT 4 (mkBase p_1 q_1 r_1) [(0,0,1),(0,0,2),(0,1,2),(0,6,3),(3,7,0),(0,2,3),(3,9,0),(0,4,2)]
lemma W_1_ok : btAll (fun x => faithful p_1 q_1 x ∧ x.1 < 2^256) W_1 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_1 : List (List (Nat × Nat)) := [[],[(2,3)],[(1,2)],[(1,2),(2,3)],[(0,1)],[(0,1),(2,3)],[(0,2),(1,2)],[(0,2),(1,2),(2,3)],[(0,2),(1,3)],[(0,1),(1,2),(2,3)],[(0,2),(1,3),(2,3)]]
def A_1 : BT (List (Nat × Nat)) := btOfList 4 al_1
set_option maxHeartbeats 0 in
lemma A_1_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_1 = g_1) A_1 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_1_0 : Slice r_1 g_1 (subcubeFast 0 1) 4 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_1_1 : Slice r_1 g_1 (subcubeFast 0 2) 4 := by
  have hc : Lower (varsOf 13) (d 0xfaa0faa0faa0faa0) 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_1_2 : Slice r_1 g_1 (subcubeFast 0 4) 4 := by
  have hc : Lower (varsOf 11) (d 0xee88ee88ee88ee88) 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_0
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
def N_1_4 : List NodeSpec := [([4,5,1,2,3],[0,2],[0]),([10,0,1,2,3],[],[]),([11,0,1,2,3],[3],[9])]
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
def N_1_6 : List NodeSpec := [([0,1,2,3],(r 0 4),[0,2,3,6,7,8])]
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
def g_2 := (d 0xfee8fee8fee8fee8)
def r_2 : List Nat := varsOf 15
def p_2 : List Nat := [3,3,5,5,6,6,9,9,10,10,12,12]
def q_2 : List Nat := [2,1,4,1,4,2,8,1,8,2,8,4]
def F_2 : Nat := fullMask 12
set_option maxHeartbeats 0 in
lemma gp_2 : goodPairs g_2 p_2 q_2 := goodPairs_of (by decide +kernel)
def W_2 : BT Decor := buildWiresBT 4 (mkBase p_2 q_2 r_2) [(1,0,1),(1,4,2),(2,5,3),(1,1,2),(1,3,1),(1,3,2),(2,4,3),(1,3,0)]
lemma W_2_ok : btAll (fun x => faithful p_2 q_2 x ∧ x.1 < 2^256) W_2 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_2 : List (List (Nat × Nat)) := [[],[(2,3)],[(1,2)],[(1,3),(2,3)],[(1,2),(2,3)],[(1,3)],[(0,2),(1,2)],[(0,3),(1,3),(2,3)],[(0,2),(1,2),(2,3)],[(0,3),(1,3)],[(0,1),(1,2)],[(0,2),(1,3)]]
def A_2 : BT (List (Nat × Nat)) := btOfList 4 al_2
set_option maxHeartbeats 0 in
lemma A_2_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_2 = g_2) A_2 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_2_0 : Slice r_2 g_2 (subcubeFast 1 0) 4 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_2_1 : Slice r_2 g_2 (subcubeFast 2 0) 4 := by
  have hc : Lower (varsOf 13) (d 0xfaa0faa0faa0faa0) 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_2_2 : Slice r_2 g_2 (subcubeFast 4 0) 4 := by
  have hc : Lower (varsOf 11) (d 0xee88ee88ee88ee88) 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_2_3 : Slice r_2 g_2 (subcubeFast 8 0) 4 := by
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) low_0
def S_2 : BT (Option (Nat × Nat)) := btOfList 2 [some (subcubeFast 1 0,4),some (subcubeFast 2 0,4),some (subcubeFast 4 0,4),some (subcubeFast 8 0,4)]
lemma S_2_ok : btAll (fun o => ∀ p, o = some p → Slice r_2 g_2 p.1 p.2) S_2 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_2_0) (forall_cons (fun _ h => by cases h; exact sl_2_1) (forall_cons (fun _ h => by cases h; exact sl_2_2) (forall_cons (fun _ h => by cases h; exact sl_2_3) (fun _ h => (List.not_mem_nil h).elim)))))
def ps_2 : BT (Option PoolSpec) := btOfList 2 [q 2 [],q 1 [],q 3 [],q 0 []]
def B_2_2 : BT (List (List Nat)) := BT.empty
lemma B_2_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_2 2 xs.toFinset) B_2_2 := .empty
def U_2_3 : List Nat := [0,1]
def P_2_3 : BT (Option BoundPool) := buildPoolsSubBT 2 W_2 r_2 S_2 ps_2 U_2_3
def N_2_3 : List NodeSpec := [([6,0,1,2],[],[]),([0,7,8,9],[0,1],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_2_3 : checkNodesBT W_2 g_2 F_2 P_2_3 A_2 B_2_2 3 N_2_3 = true := by decide +kernel
def B_2_3 : BT (List (List Nat)) := buildBucketsBT W_2 N_2_3
set_option maxRecDepth 500000 in
lemma B_2_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_2 3 xs.toFinset) B_2_3 :=
  buildBucketsBT_sound (by decide) gp_2 W_2_ok (buildPoolsSubBT_sound S_2_ok) A_2_ok B_2_2_ok C_2_3
def U_2_4 : List Nat := [1,2,3]
def P_2_4 : BT (Option BoundPool) := buildPoolsSubBT 2 W_2 r_2 S_2 ps_2 U_2_4
def N_2_4 : List NodeSpec := [([0,1,2,5,3],[2],[0]),([10,0,1,2,3],[],[]),([0,1,2,11,8],[1,3],[10])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_2_4 : checkNodesBT W_2 g_2 F_2 P_2_4 A_2 B_2_3 4 N_2_4 = true := by decide +kernel
def B_2_4 : BT (List (List Nat)) := buildBucketsBT W_2 N_2_4
set_option maxRecDepth 500000 in
lemma B_2_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_2 4 xs.toFinset) B_2_4 :=
  buildBucketsBT_sound (by decide) gp_2 W_2_ok (buildPoolsSubBT_sound S_2_ok) A_2_ok B_2_3_ok C_2_4
def U_2_5 : List Nat := (r 0 4)
def P_2_5 : BT (Option BoundPool) := buildPoolsSubBT 2 W_2 r_2 S_2 ps_2 U_2_5
def N_2_5 : List NodeSpec := [([0,1,4,2,3],(r 0 4),[0,1,3,5,7,9])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_2_5 : checkNodesBT W_2 g_2 F_2 P_2_5 A_2 B_2_4 5 N_2_5 = true := by decide +kernel
def B_2_5 : BT (List (List Nat)) := buildBucketsBT W_2 N_2_5
set_option maxRecDepth 500000 in
lemma B_2_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_2 5 xs.toFinset) B_2_5 :=
  buildBucketsBT_sound (by decide) gp_2 W_2_ok (buildPoolsSubBT_sound S_2_ok) A_2_ok B_2_4_ok C_2_5
def U_2_6 : List Nat := (r 0 4)
def P_2_6 : BT (Option BoundPool) := buildPoolsSubBT 2 W_2 r_2 S_2 ps_2 U_2_6
def N_2_6 : List NodeSpec := [([0,1,2,3],(r 0 4),[0,2,4,6,8,11])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_2_6 : checkNodesBT W_2 g_2 F_2 P_2_6 A_2 B_2_5 6 N_2_6 = true := by decide +kernel
def B_2_6 : BT (List (List Nat)) := buildBucketsBT W_2 N_2_6
set_option maxRecDepth 500000 in
lemma B_2_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_2 6 xs.toFinset) B_2_6 :=
  buildBucketsBT_sound (by decide) gp_2 W_2_ok (buildPoolsSubBT_sound S_2_ok) A_2_ok B_2_5_ok C_2_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_2_ok : forestRootCheck r_2 g_2 [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 3,1,9)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_2_in : bucketContainsBT B_2_6 r_2 = true := by decide +kernel
lemma low_2 : Lower r_2 g_2 7 := lower_of_forestBT root_2_ok B_2_6_ok root_2_in
def g_3 := (d 0xfec0fec0fec0fec0)
def r_3 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_3 : Lower r_3 g_3 5 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,8,9)]) (by decide +kernel) hc
def g_4 := (d 0xe800e800e800e800)
def r_4 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_4 : Lower r_4 g_4 5 := by
  exact lift_of_f (z := 0) (o := 8) (other := r_0) (G := g_0) (essPairs := [(VAR 3,3,11)]) (by decide +kernel) low_0
def g_5 := (d 0xfee0fee0fee0fee0)
def r_5 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_5 : Lower r_5 g_5 5 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,4,5)]) (by decide +kernel) hc
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
def g_7 := (d 0xfee8e000fee8e000)
def r_7 : List Nat := varsOf 31
def p_7 : List Nat := [13,13,13,14,14,14,15,15,19,19,19,21,21,21,22,22,22,23,25,25,25,26,26,26,27,28,28,28]
def q_7 : List Nat := [12,9,5,12,10,6,11,7,18,17,3,20,17,5,20,18,6,7,24,17,9,24,18,10,11,24,20,12]
def F_7 : Nat := fullMask 28
set_option maxHeartbeats 0 in
lemma gp_7 : goodPairs g_7 p_7 q_7 := goodPairs_of (by decide +kernel)
def W_7 : BT Decor := buildWiresBT 8 (mkBase p_7 q_7 r_7) [(1,0,1),(0,5,4),(0,2,3),(1,6,7),(1,2,3),(0,9,4),(1,5,2),(0,11,4),(0,12,3),(1,3,12),(3,13,14),(0,3,4),(3,16,2),(1,1,2),(0,18,4),(1,1,16),(0,2,4),(1,1,21),(1,1,3),(0,23,4),(1,21,3),(1,0,2),(0,26,3),(0,27,4),(1,1,28),(0,26,4),(1,30,3),(2,5,10),(0,5,9),(3,33,4),(1,1,7),(1,0,21),(0,6,9),(0,26,23),(0,38,4),(3,5,4),(3,40,9),(1,6,3),(0,42,2),(3,1,4),(0,19,3),(1,3,19),(3,45,46),(1,5,7),(0,48,4),(0,5,3),(0,50,4),(3,51,42),(1,5,3),(0,53,4),(3,54,2),(2,54,2),(0,54,2),(1,2,54),(2,5,16),(3,21,3),(3,60,53),(1,0,3),(0,62,18),(3,63,4),(1,51,2),(0,5,2),(0,66,4),(1,6,2),(0,68,3),(3,6,9),(2,5,3),(3,6,3),(3,2,4),(3,73,3),(2,68,3),(3,24,2),(2,24,2),(2,5,2),(0,7,4),(1,78,21),(1,71,21),(2,6,3),(2,5,74),(3,44,3),(3,84,26),(1,71,7),(2,6,7),(0,66,3),(3,88,5),(3,50,4),(1,0,7),(2,26,3),(3,71,4),(3,78,4),(1,0,10),(3,88,4),(3,7,4),(3,2,62),(3,1,30),(1,16,26),(3,1,100),(3,51,2),(3,6,2),(1,67,3),(0,62,4),(1,2,105),(3,66,3),(2,12,3),(3,16,11),(3,16,26),(2,2,3),(1,111,6),(2,3,2),(3,113,6),(3,78,3),(3,113,4),(3,89,4),(1,40,7),(3,60,62),(1,111,40),(3,1,106),(1,0,16),(3,2,122),(3,0,3),(3,124,4),(0,62,2),(3,1,26),(3,3,4),(2,5,79),(3,111,5),(3,130,4),(3,113,5),(3,24,26),(1,5,21),(2,134,3),(3,60,5),(0,18,3),(3,137,4),(1,98,21),(2,23,2),(3,140,4),(3,1,91),(0,126,4),(3,9,4),(1,144,7),(1,44,0),(3,1,10),(1,111,16),(1,2,16),(3,1,149),(2,36,3),(0,91,4),(3,1,3),(1,153,21),(3,1,2),(2,11,3),(1,44,2),(1,155,0),(3,73,62),(1,1,79),(1,21,62),(1,26,3),(0,162,4),(3,113,62),(1,113,21),(1,1,30),(3,0,4),(3,167,3),(3,71,2),(0,53,2),(3,50,2),(3,73,5),(3,128,2),(3,167,2),(3,1,36),(1,17,0),(3,1,162),(1,128,2),(2,30,3),(1,153,2),(0,180,4),(3,1,9),(1,128,0),(3,23,4),(3,5,2),(3,23,2),(0,111,4),(1,111,0),(0,155,3),(3,124,2),(0,155,4)]
lemma W_7_ok : btAll (fun x => faithful p_7 q_7 x ∧ x.1 < 2^256) W_7 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_7 : List (List (Nat × Nat)) := [[],[(2,3)],[(0,1)],[(0,1),(2,3)]]
def A_7 : BT (List (Nat × Nat)) := btOfList 2 al_7
set_option maxHeartbeats 0 in
lemma A_7_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_7 = g_7) A_7 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_7_0 : Slice r_7 g_7 (subcubeFast 2 0) 7 := by
  have hc : Lower (varsOf 29) (d 0xfaa0a000faa0a000) 7 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_1 : Slice r_7 g_7 (subcubeFast 0 16) 7 := by
  exact slice_fast_direct_f (z := 0) (o := 16) (by decide +kernel) low_2
set_option maxHeartbeats 0 in
lemma sl_7_2 : Slice r_7 g_7 (subcubeFast 1 0) 7 := by
  have hc : Lower (varsOf 30) (d 0xfcc0c000fcc0c000) 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_3 : Slice r_7 g_7 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) (d 0xfffcf000fffcf000) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_4 : Slice r_7 g_7 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) (d 0xfffaf000fffaf000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_5 : Slice r_7 g_7 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) (d 0xee880000ee880000) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_6 : Slice r_7 g_7 (subcubeFast 0 4) 5 := by
  have hc : Lower (varsOf 27) (d 0xffeeee00ffeeee00) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_7 : Slice r_7 g_7 (subcubeFast 8 0) 5 := by
  have hc : Lower (varsOf 23) (d 0xe8e80000e8e80000) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_8 : Slice r_7 g_7 (subcubeFast 0 8) 5 := by
  have hc : Lower (varsOf 23) (d 0xfefee0e0fefee0e0) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_9 : Slice r_7 g_7 (subcubeFast 8 16) 4 := by
  exact slice_fast_direct_f (z := 8) (o := 16) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_7_10 : Slice r_7 g_7 (subcubeFast 4 16) 4 := by
  have hc : Lower (varsOf 11) (d 0xee88ee88ee88ee88) 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_11 : Slice r_7 g_7 (subcubeFast 2 16) 4 := by
  have hc : Lower (varsOf 13) (d 0xfaa0faa0faa0faa0) 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 2) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_12 : Slice r_7 g_7 (subcubeFast 2 8) 4 := by
  have hc : Lower (varsOf 21) (d 0xfafaa0a0fafaa0a0) 4 := carry_of (swaps := [(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 2) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_13 : Slice r_7 g_7 (subcubeFast 2 4) 4 := by
  have hc : Lower (varsOf 25) (d 0xffaaaa00ffaaaa00) 4 := carry_of (swaps := [(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 2) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_14 : Slice r_7 g_7 (subcubeFast 1 16) 4 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_15 : Slice r_7 g_7 (subcubeFast 1 8) 4 := by
  have hc : Lower (varsOf 22) (d 0xfcfcc0c0fcfcc0c0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_16 : Slice r_7 g_7 (subcubeFast 1 4) 4 := by
  have hc : Lower (varsOf 26) (d 0xffcccc00ffcccc00) 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 4) (by decide +kernel) hc
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
def S_7 : BT (Option (Nat × Nat)) := btOfList 5 [some (subcubeFast 2 0,7),some (subcubeFast 0 16,7),some (subcubeFast 1 0,7),some (subcubeFast 0 1,5),some (subcubeFast 0 2,5),some (subcubeFast 4 0,5),some (subcubeFast 0 4,5),some (subcubeFast 8 0,5),some (subcubeFast 0 8,5),some (subcubeFast 8 16,4),some (subcubeFast 4 16,4),some (subcubeFast 2 16,4),some (subcubeFast 2 8,4),some (subcubeFast 2 4,4),some (subcubeFast 1 16,4),some (subcubeFast 1 8,4),some (subcubeFast 1 4,4),some (subcubeFast 2 1,4),some (subcubeFast 1 2,4),some (identDom 2 3,6)]
lemma S_7_ok : btAll (fun o => ∀ p, o = some p → Slice r_7 g_7 p.1 p.2) S_7 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_7_0) (forall_cons (fun _ h => by cases h; exact sl_7_1) (forall_cons (fun _ h => by cases h; exact sl_7_2) (forall_cons (fun _ h => by cases h; exact sl_7_3) (forall_cons (fun _ h => by cases h; exact sl_7_4) (forall_cons (fun _ h => by cases h; exact sl_7_5) (forall_cons (fun _ h => by cases h; exact sl_7_6) (forall_cons (fun _ h => by cases h; exact sl_7_7) (forall_cons (fun _ h => by cases h; exact sl_7_8) (forall_cons (fun _ h => by cases h; exact sl_7_9) (forall_cons (fun _ h => by cases h; exact sl_7_10) (forall_cons (fun _ h => by cases h; exact sl_7_11) (forall_cons (fun _ h => by cases h; exact sl_7_12) (forall_cons (fun _ h => by cases h; exact sl_7_13) (forall_cons (fun _ h => by cases h; exact sl_7_14) (forall_cons (fun _ h => by cases h; exact sl_7_15) (forall_cons (fun _ h => by cases h; exact sl_7_16) (forall_cons (fun _ h => by cases h; exact sl_7_17) (forall_cons (fun _ h => by cases h; exact sl_7_18) (forall_cons (fun _ h => by cases h; exact sl_7_19) (fun _ h => (List.not_mem_nil h).elim)))))))))))))))))))))
set_option maxRecDepth 500000 in
def ps_7 : BT (Option PoolSpec) := btOfList 9 [q 2 [12296,12297,36884],q 19 [],q 2 [],q 0 [],q 6 [5],q 8 [5],q 19 [4097,28693,16576],q 1 [4097,8213],q 3 [],q 4 [],q 6 [],q 2 [12309,16596],q 0 [12309,16596],q 8 [],q 1 [],q 5 [],q 0 [12296,12297,36884],q 7 [],q 0 [12296,28673],q 19 [4097,28693],q 1 [12296,12297],q 0 [8212,16404,16392],q 1 [4097,8212],q 2 [12296,12297,16420],q 0 [8212,12552,16739],q 3 [12293],q 9 [],q 5 [16391],q 13 [],q 1 [8193,106561,409607],q 0 [12308,16584,8399],q 2 [12293,16476],q 1 [12289],q 19 [4097,16404],q 1 [4097,8213,45123],q 2 [12296,12297],q 19 [5,16391],q 2 [16632,16392,12373],q 2 [16404,16392,86021],q 2 [12297,36884],q 19 [4097,16407],q 19 [5,28677],q 2 [8440,16392,16632],q 1 [12289,8440],q 0 [12296,12297,16420],q 19 [4097,28694],q 0 [8212,12308,12296],q 12 [],q 0 [12296,16412,323606],q 0 [16392,86017],q 1 [4097,86037,12826],q 19 [28673,372743],q 0 [12296,12297,16423,29249],q 2 [12296,12297,16423,29249],q 15 [],q 1 [12296,12297,29249],q 1 [12293,86021,12373],q 0 [16392,12373],q 19 [16391,177],q 0 [16396,8257],q 1 [8257,610311],q 2 [16392,12434],q 1 [86017,12434],q 2 [16396],q 2 [12298,12733,16420],q 0 [12298,12733,16420],q 1 [12298,12733],q 2 [12297,16420],q 0 [8204,16396,8257],q 2 [8204,16396,8257],q 1 [8204,8257],q 0 [12296,8223,12733],q 2 [12296,8223,12733],q 1 [12296,8223,12733],q 2 [12296],q 0 [12296],q 2 [12296,16748],q 0 [12296,28673,16748],q 19 [16391],q 0 [12296,16415],q 18 [],q 0 [177],q 2 [16391],q 1 [12295,86629],q 1 [8197,12360],q 0 [12360,16935],q 1 [8199,65545],q 1 [12296],q 2 [8213,12334],q 0 [8213,12334],q 1 [4097],q 0 [16404,8219],q 0 [8193],q 1 [8193,106503],q 2 [16404,16392],q 0 [16404,16392],q 0 [16404],q 2 [16404],q 2 [16392],q 0 [16392],q 2 [16632,16392],q 16 [],q 0 [12298,8639],q 0 [8214,16699],q 1 [4097,8214],q 2 [16396,8259],q 1 [8193,8259],q 2 [16407],q 0 [16407],q 1 [8193,106563],q 0 [12297,16420],q 1 [12297],q 2 [12310],q 0 [12310],q 1 [4097,12310],q 0 [12296,16412],q 2 [8199,16391,8369],q 1 [8199,8369],q 0 [8212,16648],q 1 [8193],q 2 [12394,16396],q 1 [8193,12394],q 2 [12309],q 0 [12309],q 1 [4097,12309],q 0 [12289,16632],q 2 [12296,12297,16423],q 2 [12308,8207],q 0 [12308,8207],q 1 [12293,86021],q 1 [177],q 0 [8212,12296],q 2 [16883],q 0 [12291,16883],q 1 [8199,621],q 0 [16456],q 2 [8197,16456],q 1 [5,8197],q 10 [],q 2 [8197],q 3 [8197],q 2 [16399],q 0 [8212,16404],q 2 [16392,86021],q 1 [5,86021],q 2 [12293],q 1 [5,12293],q 2 [16395,254247],q 0 [8212,12552],q 2 [12310,12296],q 0 [12310,12296],q 4 [8193],q 2 [12296,16412,323589],q 1 [12296,323589],q 2 [12297],q 3 [16391],q 1 [12289,254037],q 2 [12393,17032],q 0 [8193,12393,17032],q 1 [8193,12393],q 0 [12296,28694],q 2 [8206,254407],q 2 [8213,16428],q 0 [8213,16428],q 11 [],q 2 [12298],q 1 [86017,12373],q 0 [8193,16488],q 0 [8212],q 2 [8197,8212],q 0 [8286,16947],q 1 [8206,86469],q 1 [12293,8286],q 2 [8214,16699],q 6 [4097],q 1 [4097,8193],q 5 [16396],q 2 [12310,16396],q 0 [12310,16396],q 1 [4097,12308],q 0 [12308,16587],q 2 [12298,16396],q 2 [16632],q 0 [16387,12959],q 0 [16396,8259],q 1 [8259],q 0 [12310,8479],q 0 [8212,12308],q 2 [12308],q 2 [8212],q 5 [16399],q 0 [12308,16399],q 0 [12309,8404],q 2 [12309,8404],q 1 [12296,28673,12297],q 0 [12296,12297],q 19 [28673],q 2 [12296,28677],q 0 [12297,36884],q 8 [4097],q 14 [],q 0 [8206,20935],q 2 [8206,20935],q 2 [8199],q 2 [8440,16392],q 0 [8206,16839],q 0 [16396,65558],q 0 [12298,16396],q 1 [12298],q 0 [8212,16392],q 1 [4097,65558],q 2 [16396,65558],q 0 [12308,8395],q 1 [4097,86037],q 0 [16395,20775],q 0 [16399,8707],q 2 [12293,94312],q 0 [8193,94312],q 2 [106503],q 2 [8863],q 0 [16387,8863],q 2 [16396,106563],q 1 [86017,147463],q 19 [16420],q 7 [16391],q 2 [8440,16888],q 0 [12289],q 2 [8440,16632],q 1 [8259,69],q 2 [12392,16399],q 2 [12393,663559],q 19 [4097],q 2 [12298,16399,8705],q 1 [12298,8705],q 1 [12293],q 1 [12293,8291],q 0 [16476,8291],q 0 [12296,16392],q 7 [16392],q 2 [16392,12373],q 1 [12289,12373],q 0 [8805,17104],q 1 [12295,8805],q 7 [17104],q 0 [16399,8705],q 2 [16399,8705],q 1 [12373],q 1 [86017],q 0 [12298,16399],q 2 [12298,16399],q 2 [8206,16839],q 0 [12298,12733],q 2 [12298,12733],q 0 [12297],q 2 [12297,36871],q 1 [12297,36871],q 2 [8204,16399],q 0 [8204,16399],q 2 [16396,16451],q 0 [16396],q 2 [12296,16392],q 2 [12298,8639],q 1 [12298,8639],q 2 [8440],q 0 [16399,513],q 17 [],q 0 [16399],q 2 [12293,16479],q 0 [16479],q 2 [12394],q 2 [8197,8199],q 0 [12289,8440],q 1 [5],q 2 [16399,8707],q 1 [12291],q 2 [12297,12298],q 1 [12297,12298],q 0 [8193,12394],q 0 [8215],q 2 [12293,8287],q 1 [8199],q 2 [12296,16412],q 2 [12298,16828],q 1 [8257],q 0 [12298,445],q 1 [12298,445],q 0 [8213],q 2 [8213],q 2 [12296,16415],q 2 [16488],q 1 [8863],q 0 [621],q 4 [16387],q 0 [16387],q 2 [8199,12908],q 2 [12297,16423],q 0 [8805],q 2 [12295,8805],q 2 [8691],q 0 [12291,8691],q 1 [12296,28673],q 2 [8199,17004],q 0 [12291],q 0 [8193,12393],q 2 [12393],q 0 [8369],q 1 [8369],q 2 [12296,8223]]
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
def N_7_4 : List NodeSpec := [([17,0,19,3,20],[],[]),([0,2,22,24,25],[],[]),([0,2,29,31,4],[],[]),([32,0,1,7,4],[],[]),([34,0,1,7,4],[],[]),([0,33,7,35,4],[0],[]),([6,2,36,22,3],[],[]),([0,1,37,7,4],[1],[]),([0,1,21,8,3],[],[]),([5,2,39,3,4],[2,3],[]),([0,1,41,7,4],[],[]),([0,1,6,43,16],[],[]),([5,2,30,3,24],[4,5],[]),([0,1,8,9,4],[1],[0]),([44,0,33,7,4],[0],[]),([47,0,1,2,4],[],[]),([17,0,1,12,3],[],[]),([0,1,7,49,9],[6],[]),([52,0,1,2,4],[],[]),([55,56,0,1,3],[],[1]),([0,1,6,7,10],[],[0]),([0,1,57,3,58],[],[1]),([59,0,2,19,3],[],[]),([0,1,61,2,4],[],[]),([64,5,2,3,4],[],[]),([0,1,65,42,4],[1],[]),([0,1,67,69,4],[1],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_7_4 : checkNodesBT W_7 g_7 F_7 P_7_4 A_7 B_7_3 4 N_7_4 = true := by decide +kernel
def B_7_4 : BT (List (List Nat)) := buildBucketsBT W_7 N_7_4
set_option maxRecDepth 500000 in
lemma B_7_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_7 4 xs.toFinset) B_7_4 :=
  buildBucketsBT_sound (by decide) gp_7 W_7_ok (buildPoolsSubBT_sound S_7_ok) A_7_ok B_7_3_ok C_7_4
def U_7_5 : List Nat := (r 0 6++r 7 52)
def P_7_5 : BT (Option BoundPool) := buildPoolsSubBT 9 W_7 r_7 S_7 ps_7 U_7_5
def N_7_5 : List NodeSpec := [e5 [70] [],([71,72,0,1,2,4],[],[]),([0,1,2,12,3,14],(r 7 4),[1]),([0,1,57,2,3,54],[8,9,11,12,13],[0,1]),a5 [8] [8,10,14,15] [0,1],([71,0,1,74,2,4],[],[]),([75,0,1,6,2,4],[],[]),([0,1,67,68,3,4],[],[0,1]),([0,1,33,7,4],[0,1,16],[0,2]),([76,77,0,1,3,4],[],[1]),([0,1,6,2,3,10],[8,9,10,13],[0]),([71,78,0,1,7,4],[10],[]),([0,1,6,79,2,3],[8,9],[]),([0,1,6,21,68,3],[],[1]),([0,1,21,80,3,4],[10],[]),([17,0,1,6,2,3],[],[]),e5 [81] [8],([82,72,0,1,2,4],[],[0]),e5 [83] [],e5 [85] [],([0,1,7,86,2,4],[13],[]),e5 [87] [],([71,0,1,6,2,16],[8,9,14],[]),u5 [34] [],e5 [89] [],([90,0,1,6,2,3],[3,17],[]),([5,2,91,35,3,4],[15,17,18],[]),([71,0,1,7,21,4],[13],[]),([0,1,7,48,9,4],[1,10,19,20],[0]),([0,21,2,22,3,24],[],[0,1]),([5,2,30,3,23,4],[5],[0]),([0,1,66,6,21,3],[8,9,21,22],[]),([55,0,1,2,3,54],[],[0]),([92,0,1,2,30,16],[8,10,14],[]),([0,1,7,2,93,4],[10],[]),([17,0,5,18,3,4],[15],[]),([0,1,6,2,94,3],[8,9,10],[]),([0,1,7,10,95,4],[23],[]),([0,1,6,43,3,4],[13],[0,1]),([96,0,1,5,2,3],[24],[]),([5,2,38,3,4],[2,3,25],[0,1]),([0,1,6,7,21,3],[],[0]),([97,44,0,5,2,3],[26,27],[]),([17,98,0,1,3,4],[],[]),([59,0,2,18,3,4],[15],[0]),([99,5,2,30,3,4],[3,28],[]),([101,0,2,16,3,4],[29],[]),e5 [59] [],([102,0,1,5,3,4],[30],[]),([0,5,21,2,3,24],[4,5,26,31],[1]),([103,0,1,6,21,3],[10],[]),([0,2,30,29,3,4],[17],[0]),([0,1,6,2,104,4],[15],[1]),([71,0,1,66,7,4],[8,9,10],[]),([0,1,33,5,7,4],[0,10,16],[]),([0,1,21,3,105,106],[32],[]),([0,1,6,7,9,4],[10,15,33],[0]),([0,1,21,2,3,54],(r 8 6),[1]),([71,107,0,1,2,4],[],[]),([108,0,1,2,12,3],[],[1]),e5 [109] [34],([71,73,0,1,7,4],[10],[]),([44,0,5,7,9,4],[20,35,36],[0]),([110,1,5,2,3,4],[3],[]),([17,0,1,11,3,4],[17],[0,1]),e5 [112] [10],([0,1,21,2,105,25],[37],[2]),e5 [114] [15],([71,0,1,2,115,4],[],[]),([111,0,1,6,2,16],[],[]),([0,1,6,2,116,3],[8,17],[]),([0,6,21,2,22,3],[38],[0]),([102,0,1,6,3,4],[],[]),e5 [117] [2,3],([44,0,33,2,3,4],[3,39],[0]),e5 [118] [],([71,97,0,1,2,4],[],[]),([71,0,1,79,2,4],[8,9],[0]),([17,0,1,30,16,3],[10],[2]),([0,1,119,2,62,4],[2,17],[]),([97,40,0,1,2,3],[15,17],[]),e5 [120] [],([121,0,2,3,105,4],[],[]),([17,123,0,1,3,4],[],[]),([40,0,1,7,9,4],[10,40],[0]),u5 [41] [],([71,17,0,1,2,4],[],[]),([0,5,7,35,9,4],[15,35,41],[0]),([0,125,1,2,19,3],[8,17],[]),([0,1,7,2,49,3],[],[0]),([89,0,1,21,3,4],[14],[]),([0,1,126,21,3,105],[8,13,42,43],[]),([17,127,0,1,3,4],[],[]),([128,89,0,1,2,4],[],[]),u5 [37] [2,3,10,15],([0,1,5,7,10,4],[20,23,44],[0]),([89,0,1,7,9,4],[1,10,45],[]),([0,1,66,50,7,4],[8,9,46,47],[]),e5 [129] [48],u5 [32] [],e5 [131] [],([0,1,132,21,3,4],[],[]),([59,111,0,1,2,4],[],[]),([128,0,1,2,12,3],[8,17],[]),([5,2,36,22,3,4],[15,49],[0]),([59,0,1,7,2,4],[10],[]),e5 [133] [],([135,0,1,21,2,4],[50],[]),e5 [136] [15],u5 [39] [2,3,8,9],u5 [64] [],([0,1,2,30,3,24],[8,9,10,13],[0]),e5 [110] [],([138,0,1,2,19,3],[3,17],[]),([0,1,21,3,139,4],[10],[]),([0,1,2,141,3,24],[9,10,13],[]),([76,140,0,1,3,4],[],[]),([142,0,1,7,9,4],[51],[]),([0,1,143,3,106,4],[],[1,3]),([76,0,1,21,3,24],[10],[]),([0,1,145,4],([47]++r 52 4),[]),([44,0,132,2,3,4],[],[]),([0,2,22,23,25,4],[15,56,57],[0]),([17,0,18,3,20,4],[3,17],[0]),([97,0,146,1,2,3],[],[]),([0,146,1,7,9,4],[58],[]),([147,0,1,7,10,4],[47],[]),([0,1,2,122,148,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_7_5 : checkNodesBT W_7 g_7 F_7 P_7_5 A_7 B_7_4 5 N_7_5 = true := by decide +kernel
def B_7_5 : BT (List (List Nat)) := buildBucketsBT W_7 N_7_5
set_option maxRecDepth 500000 in
lemma B_7_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_7 5 xs.toFinset) B_7_5 :=
  buildBucketsBT_sound (by decide) gp_7 W_7_ok (buildPoolsSubBT_sound S_7_ok) A_7_ok B_7_4_ok C_7_5
def U_7_6 : List Nat := (r 1 5++r 7 4++[13,14,15,17,18,20,22,23]++r 25 4++[32,33,35,36,39,40,43,44,47,49,54]++r 58 186)
def P_7_6 : BT (Option BoundPool) := buildPoolsSubBT 9 W_7 r_7 S_7 ps_7 U_7_6
def N_7_6 : List NodeSpec := [e5 [150,16] [9,59,60],a5 [151,21] [13,15,61,62] [1],a5 [17,122] [8,15,63] [0,2],e5 [10] [2,3,8,9,10,26,64,65,66],u5 [10,95] [8,67],([0,1,7,149,4],[17,28,68,69,70],[]),([0,1,7,10,4],[10,23,26,44],[0,2]),([0,1,7,9,4],[1,15,26,47,71,72,73],[]),u5 [142,7] [2,9,18],u5 [91,35] [8,9,74,75],e5 [152] [3,8,9,15,17,76,77],([44,0,1,7,9,4],[15,20,26,35,47,78],[0]),([97,44,0,1,2,3],[3,15,26,27,79],[0]),e5 [111,146] [8,15,58,80,81],u5 [146,9] [8,80,82],e5 [21,154] [9,83],a5 [97,5] [2,3,8,9,15,26,79] [0,1,2],u5 [138,18] [13,14,84,85],([155,0,1,16,3,149,4],[15,17,86],[]),u5 [7,48] [10,13,15,87],([156,0,1,2,4],[10,13,88,89],[]),e5 [148] [2,3,8,9,13,17],a5 [103,5] [8,9,15,90,91] [1],e5 [128,127] [9,13,26,92,93],([0,1,6,21,2,3],[8,9,10,90,94,95],[0,1,2]),u5 [6,9] [10,13,15,17,90],a5 [103,6] [8,10,15,90] [0,1],a5 [67,6] [10,15,96,97] [0,1],u5 [36,22] [8,9,98,99],([0,1,21,2,3,105,62],[8,13,26,100,101],[0,1]),u5 [5,7] [2,8,9,10,13,15,17,47,102],u5 [5,94] [2,8,9,15,103,104],([17,0,1,26,16,3,4],[10,17,63,105,106],[0,2]),u5 [111,40] [8,9,13,15,17,40,107,108],e5 [110,16] [8,13,14,109],a5 [82,6] [13,17] [0,1],u5 [5,10] [2,8,9,67,110,111],u5 [71,21] [8,9,10,13,15,112,113,114],u5 [71,66] [8,9,13,15,28,112,113],a5 [5,79] [2,8,9,15,17,87,115] [0,1],([155,0,157,3,4],[9,10,101,116,117],[]),a5 [67,5] [2,47,118] [1],([92,0,1,2,26,16,4],[8,10,17,119,120,121],[0]),a5 [21,53] [8,9,10,13,15,122,123,124] [0,1],a5 [71,6] [13,17,114] [0,1],([0,1,21,2,3,105],[8,10,13,26,100,125],[0,1,2]),([144,0,1,7,4],[10,26,47,126],[0]),a5 [6,7] [10,13,15,17,90] [0,1],([111,0,1,50,2,4],[10,17,26,47,127,128],[]),u5 [89,7] [8,10,13,15],([0,21,2,22,3,23,4],[3,15,26,129],[0,1]),a5 [111,6] [8,9,10,13,15,17,33,90,96,97] [0,1],u5 [147,10] [3,9,47],u5 [146,7] [8,15,80,82,130],([0,1,66,5,7,3,4],[8,9,10,47,131],[0]),u5 [125,18] [8,9,26,54,132,133],e5 [128,158] [8,13,26,134],([111,0,1,50,5,2,4],[8,9,13,128],[]),u5 [40,7] [8,10,13,15,17,90],([0,5,2,19,3,4],([2,4,5,9]++r 135 4),[1,2]),([71,0,1,5,7,2,4],[8,9,17,47],[0]),([128,0,5,2,18,3,4],([5]++r 137 5),[]),a5 [66,6] [8,9,10,15,22,28,97,142] [0,1],([0,5,21,2,22,3,4],[3,15,143,144],[0]),a5 [71,78] [10,13,15] [0,1],([0,5,21,2,3,23,4],[5,25,26,98,101,145,146],[0,1,3]),e5 [159,62] [10,147],u5 [88,5] [2,90,148],u5 [71,73] [10,13,114,138],([71,0,1,7,2,4],[10,13,149,150],[0]),([5,2,26,3,23,4],[4,5,25,92,145,151],[0,3]),([0,2,160,3,4],[9,15,17,152,153],[]),([44,0,5,2,3,9,4],[4,82,111,154,155],[0]),a5 [21,161] [10,14,99,156] [1],e5 [163] [3,8,9,10,47,157,158,159],e5 [89,5] [2,15,160],([17,0,1,26,3,4],[2,15,17,105,106],[0,1,2]),e5 [164] [2,26,47,161],a5 [12] [7,10,13,14,17,162,163] [0,1],([111,44,0,5,2,3,4],[9,26,36,82,155,164,165],[1]),a5 [36,25] [8,13,15,26,98,166] [2],a5 [30,23] [3,9,13,17,119,167] [0,3],a5 [89] [2,8,10,14,15,160] [0,1],([0,66,18,3,4],[9,138,168,169],[]),e5 [141] [3,13,15,101,170],([0,1,21,3,165,4],[10,15,171],[1,3]),u5 [141,23] [3,9,13,15,17,170,172],a5 [94] [2,3,8,10,13,14,17,103,104,173] [1],([44,5,2,26,3,4],[2,47,54,82,92,138,155,164,174,175],[]),([71,0,1,2,16,4],[13,14,176,177,178],[0,1]),e5 [30,166] [9,167],u5 [90,5] [2,3,8,9,13,179,180],([111,0,1,2,16,122,4],[181],[0]),u5 [128,11] [7,8,13,26],a5 [143,105] [8,10,15,26,125,182] [0,1,3],e5 [155,168] [9,28,183],a5 [17,5] [2,3,8,9,15,17,184,185] [0,1,2],a5 [6,68] [8,9,10,15,90] [0,1],([71,0,1,5,2,16,4],[8,9,17,90,114,178],[0]),a5 [5,169] [2,8,9,15,186] [0,1],u5 [66,50] [8,9,10,15,17,28,47,187,188,189],([128,0,1,5,7,2,4],[13,26,47,190],[0,1]),([128,0,1,50,5,2,4],[8,9,13,191],[]),a5 [30,31] [8,10,13,17,119,167] [1],([0,1,170,3,4],[13,15,192,193],[]),([0,1,7,91,9,4],[15,26,35,54,194,195,196],[0,2]),([0,5,7,2,35,3,4],[3,15,17,197],[0]),([0,1,2,12,3],[10,162,163],[0,1]),a5 [33] [8,14,28,39,47,174,198,199] [0,2],u5 [33,5] [2,10,39,198],u5 [17,62] [8,15,105,200],a5 [132] [2,8,14,15,28,174,201,202] [0,1,2],e5 [158,16] [8,15,17,28,80,134,203],e5 [132,5] [2,10,201],([0,1,126,21,3,62,4],[8,10,13,32,43,204],[0]),u5 [5,116] [2,8,9,10,26,138,205],u5 [40,9] [8,10],e5 [59,5] [2,17,206],([111,0,1,5,2,16,4],[17,176,207,208],[0,1]),([0,1,66,5,21,3,4],[8,9,10,22,90,209],[0]),a5 [59] [2,8,10,14,15,206,210,211] [0,2],([0,1,6,5,21,2,3],[8,9,14,28,95],[0,1]),a5 [171,5] [2,3,8,9,15,47,212] [1],a5 [21,134] [10,14,26,213] [0,1],e5 [59,16] [8,13,14,210],e5 [172,5] [2,10,214],a5 [5,173] [2,8,9,13,15,26,215] [1],a5 [38] [14,28,54,216,217] [0,1],a5 [155,105] [9,15,28,32,125] [3],u5 [127,16] [8,9,28,93,218],a5 [174,23] [8,9,15,101,219,220] [3],e5 [110,26] [2,8,17,221],e5 [175,21] [2,9,49,222],a5 [92,21] [10,13,15,200] [1],([0,1,7,10,9,4],[20,26,35,47,54,195,223],[]),([44,0,5,7,2,3,4],[9,27,74,82,87,155,164,224],[0]),e5 [155,125] [9,26,28,133],a5 [143,62] [2,8,17,80,225,226] [1],a5 [126,105] [10,15,43,101,227] [0,3],e5 [176,16] [8,13,14,17,54,105,228],([128,0,1,2,27,26,4],[8,13,229],[]),([177,0,2,3,4],[9,10,13,230],[]),([0,1,5,7,9,4],[15,20,35,47,174,195,231],[0,2]),([92,0,1,2,16,4],[10,13,14,47,120,176],[1]),([0,1,2,3,163],[8,10,13,47,157,158],[]),a5 [92,30] [13,17,121] [0,3],([111,0,1,178,4],[10,13,47,232,233],[0]),u5 [99,30] [3,9,28],a5 [179,30] [13,17] [3],u5 [76,24] [9,10,15,234],u5 [76,23] [9,14,15,235,236],([0,1,5,7,21,3,4],[15,47,87,90,237,238],[0,1]),([0,1,21,2,62,25,4],[15,17,239,240],[0,2]),u5 [110] [2,3,8,9,14,15,109,221],e5 [181] [2,3,8,9,10,14,15,241,242,243]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_7_6 : checkNodesBT W_7 g_7 F_7 P_7_6 A_7 B_7_5 6 N_7_6 = true := by decide +kernel
def B_7_6 : BT (List (List Nat)) := buildBucketsBT W_7 N_7_6
set_option maxRecDepth 500000 in
lemma B_7_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_7 6 xs.toFinset) B_7_6 :=
  buildBucketsBT_sound (by decide) gp_7 W_7_ok (buildPoolsSubBT_sound S_7_ok) A_7_ok B_7_5_ok C_7_6
def U_7_7 : List Nat := (r 1 4++r 7 4++[13,14,15,17,18,20,22,26,27,28,32,35,43,47,49,54,57,59,63,66,67,74,75]++r 78 5++[87,90,92,93]++r 96 4++[101,102,105,108]++r 110 6++[119,121,130,132,133,134,137,138,139,141,145,154,159,164,165,167,168,174,181,184,185,189,195,199,200,203,205,207,208,215,218,219,220,226,231,234,237,239,242]++r 244 64)
def P_7_7 : BT (Option BoundPool) := buildPoolsSubBT 9 W_7 r_7 S_7 ps_7 U_7_7
def N_7_7 : List NodeSpec := [u5 [178] [2,8,13,14,26,28,244,245],a5 [21,25] [15,26,57,239,246] [0,1,2,3],a5 [21,36] [8,15,26,49,98,247] [0,1,2],([111,128,0,1,2,4],[10,13,26,47,138,208,248,249],[0]),u5 [111,16] [10,14,17,47,54,63,208],u5 [116] [8,9,10,26,138,205,250],u5 [9] [8,10,47,54,66,251,252],u5 [10,9] [10,26,47,54,138,154,253],a5 [10] [8,9,10,13,26,67,110,111,138] [0,2],e5 [21,9] [15,17,26,28,101,111,154,253],e5 [182] [2,8,9,10,14,28,47,80,253,254,255],([128,0,1,7,2,4],[10,26,138,256,257],[0]),([128,0,1,2,16,3],[3,13,14,17,47,54,258,259],[]),([0,1,7,21,3,4],[14,15,26,237,260],[0,1]),e5 [7,9] [1,15,26,47,54,111,154,253],u5 [7] [8,9,15,17,26,102,261,262],a5 [126,62] [8,10,32,43,47,101,226,263] [0,1,3],a5 [111,26] [2,15,17,28,92,119,138,165] [1],e5 [183] [3,8,9,10,15,26,141,264,265],a5 [17] [2,3,8,9,10,14,15,17,105,184,185] [0,2],a5 [128,26] [2,10,13,15,26,54,80,92,119,138,141,266] [0,1,2],a5 [26,23] [28,54,92,119,145,234] [0,3],a5 [40] [8,10,13,15,17,90,108] [0,1],e5 [184] [2,8,9,10,13,15,54,234,267,268],a5 [92,26] [2,17,28,54,92,119,121,269] [0,3],([155,0,2,18,3,4],[3,9,28,101,138,270],[]),e5 [126] [9,10,13,15,43,47,138,263,271],a5 [44,26] [2,9,10,15,26,28,47,54,80,82,119,164] [0,3],a5 [128,5] [2,3,8,9,13,26,28,47,90,138,141,199,266] [0,1,2],a5 [21,26] [2,15,26,28,54,98,119,200] [0,1],([44,0,5,2,3,4],[2,3,9,26,54,82,101,138,272],[0,1]),u5 [173] [8,9,13,15,26,215,273],([0,5,2,18,3,4],[3,4,9,15,54,101,137,139],[0,1,2]),u5 [125] [3,9,10,14,15,26,132,133,274],a5 [66] [2,13,15,17,138,168,189] [0,1,2],a5 [5,9] [8,9,15,17,28,47,90,111,154,174,199,253] [0,2],a5 [66,5] [8,9,10,22,28,47,90,168,189] [0,1],u5 [127] [3,8,9,13,14,17,28,92,93,218],([111,0,1,2,9,4],[1,3,15,47,138,253,275,276],[0]),a5 [111,5] [2,3,8,9,15,28,47,90,101,165,208,231] [0,1,2],a5 [92] [2,3,9,10,13,14,15,47,121,269,277] [0,3],a5 [146] [8,10,13,15,17,81,82,130] [0,1],a5 [71] [2,10,13,14,15,112,113,114] [0,1],e5 [185] [8,13,14,15,17,138,278],e5 [186] [2,8,9,13,14,15,138,279],a5 [155,62] [2,9,13,15,17,28,32,47,80,101,203,226,280] [0,3],a5 [79] [2,3,8,9,15,17,87,115,281] [0,2],a5 [71,5] [2,8,9,17,28,47,90,112,113,114] [0,1],e5 [36] [8,9,13,15,17,49,98,101,247,265],u5 [128,155] [9,13,26,47,138,141,203,265],a5 [21,62] [8,13,15,26,32,80,98,99,101,226] [0,1,2],a5 [6] [8,10,13,14,15,17,90,96,97] [0,1],e5 [187] [2,3,8,9,13,15,47,208,282],a5 [6,5] [8,9,14,28,47,90,96,97] [0,1],u5 [149] [15,17,28,59,101,283],e5 [188] [3,8,9,15,54,101,165,265,284,285],a5 [11] [7,8,10,13,14,17,286,287] [0,1],a5 [97] [2,3,8,9,14,15,26,79,138,288] [0,2],a5 [5,7] [8,9,15,17,28,47,54,74,75,87,90,101] [0,1,2],u5 [111,44] [9,15,47,78,82,138,164,165,265],([0,1,7,2,9,4],[1,15,20,28,35,138,195],[]),e5 [7,26] [2,15,28,54,74,119,138],a5 [30] [9,10,13,17,119,138,167,289] [0,1,2,3],a5 [17,16] [10,17,63,105,138,184,259] [0,2],a5 [30,26] [8,28,54,92,119,138,289] [0,1,3],a5 [174] [2,3,9,13,15,17,219,220,290] [0,1],u5 [158] [8,13,15,17,28,80,134,203,291],u5 [155,167] [8,9,26,28,47,54,138,200,203,265,292,293],e5 [189] [2,8,9,14,15,17,26,294],u5 [144] [2,3,8,9,10,13,47,111,295],u5 [180] [8,10,47,101,242,296,297],e5 [190] [2,3,9,10,14,15,54,138,298,299],a5 [7,91] [8,15,17,18,26,74,300] [0,2],e5 [191] [2,8,9,13,15,17,80,280,301],a5 [5,21] [8,9,15,26,28,47,90,98,99,101] [0,1,2],a5 [155,124] [8,9,15,17,28,47,54,80,101,265,274,280,302] [0,3],a5 [155,16] [13,17,28,47,63,138,203,259,265] [0,1],([155,44,0,2,3,4],[3,9,10,26,27,80,138,280],[0]),([0,1,7,9,4],[1,10,15,20,26,35,47,54,195],[0,2]),u5 [162] [3,8,9,10,13,14,47,159,303,304],u5 [157] [13,14,17,101,305,306],([111,0,1,2,16,4],[13,17,138,181,207],[0,1,2]),u5 [44,7] [9,10,15,26,27,74,75,82,87,138,164,265],u5 [44,9] [9,10,13,15,17,26,47,82,111,138,154,164,265],e5 [111] [1,2,3,8,9,10,14,15,47,138,307],u5 [91] [8,9,15,17,18,54,74,101,265,300],([111,0,1,7,3,4],[1,3,15,17,26,47,307],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_7_7 : checkNodesBT W_7 g_7 F_7 P_7_7 A_7 B_7_6 7 N_7_7 = true := by decide +kernel
def B_7_7 : BT (List (List Nat)) := buildBucketsBT W_7 N_7_7
set_option maxRecDepth 500000 in
lemma B_7_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_7 7 xs.toFinset) B_7_7 :=
  buildBucketsBT_sound (by decide) gp_7 W_7_ok (buildPoolsSubBT_sound S_7_ok) A_7_ok B_7_6_ok C_7_7
def U_7_8 : List Nat := [1,2,3,8,9,10,13,14,15,17,26,28,47,54,74,75,82,87,90,92,98,99,101,111,119,138,141,154,164,165,203,208,253,266,280]
def P_7_8 : BT (Option BoundPool) := buildPoolsSubBT 9 W_7 r_7 S_7 ps_7 U_7_8
def N_7_8 : List NodeSpec := [a5 [128] [2,3,13,14,26,141,266] [0,2],a5 [21] [14,15,98,99] [0,1,2,3],a5 [111] [1,2,3,14,15,47,54,138,165,208] [0,1,2],a5 [9] [10,13,28,47,54,101,111,154,253] [0,1,2],a5 [44] [2,3,9,14,82,164] [0,1,2,3],a5 [7] [15,17,26,74,75,87,138] [0,1,2,3],a5 [155] [2,3,9,14,15,28,203,280] [0,1,3],a5 [26] [2,10,28,92,119] [0,1,2,3],a5 [5] [2,3,8,14,90] [0,1,2,3]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_7_8 : checkNodesBT W_7 g_7 F_7 P_7_8 A_7 B_7_7 8 N_7_8 = true := by decide +kernel
def B_7_8 : BT (List (List Nat)) := buildBucketsBT W_7 N_7_8
set_option maxRecDepth 500000 in
lemma B_7_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_7 8 xs.toFinset) B_7_8 :=
  buildBucketsBT_sound (by decide) gp_7 W_7_ok (buildPoolsSubBT_sound S_7_ok) A_7_ok B_7_7_ok C_7_8
def U_7_9 : List Nat := [2,3,14]
def P_7_9 : BT (Option BoundPool) := buildPoolsSubBT 9 W_7 r_7 S_7 ps_7 U_7_9
def N_7_9 : List NodeSpec := [a5 [] [2,3,14] [0,1,2,3]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_7_9 : checkNodesBT W_7 g_7 F_7 P_7_9 A_7 B_7_8 9 N_7_9 = true := by decide +kernel
def B_7_9 : BT (List (List Nat)) := buildBucketsBT W_7 N_7_9
set_option maxRecDepth 500000 in
lemma B_7_9_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_7 9 xs.toFinset) B_7_9 :=
  buildBucketsBT_sound (by decide) gp_7 W_7_ok (buildPoolsSubBT_sound S_7_ok) A_7_ok B_7_8_ok C_7_9
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_7_ok : forestRootCheck r_7 g_7 [(VAR 0,12,13),(VAR 1,12,14),(VAR 2,9,13),(VAR 3,5,13),(VAR 4,3,19)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_7_in : bucketContainsBT B_7_9 r_7 = true := by decide +kernel
lemma low_7 : Lower r_7 g_7 10 := lower_of_forestBT root_7_ok B_7_9_ok root_7_in
def g_8 := (d 0xfc80fc80fc80fc80)
def r_8 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_8 : Lower r_8 g_8 5 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,6,7)]) (by decide +kernel) hc
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
def g_10 := (d 0xfec8e000fec8e000)
def r_10 : List Nat := varsOf 31
def p_10 : List Nat := [13,13,13,14,14,14,15,15,19,19,19,22,22,22,23,23,25,25,25,26,26,26,27,28,28,28,29]
def q_10 : List Nat := [12,9,5,12,10,6,11,7,18,17,3,20,18,6,21,7,24,17,9,24,18,10,11,24,20,12,21]
def F_10 : Nat := fullMask 27
set_option maxHeartbeats 0 in
lemma gp_10 : goodPairs g_10 p_10 q_10 := goodPairs_of (by decide +kernel)
def W_10 : BT Decor := buildWiresBT 7 (mkBase p_10 q_10 r_10) [(0,1,3),(0,2,4),(1,5,6),(1,1,3),(1,2,4),(0,8,9),(3,6,9),(3,5,8),(0,8,4),(0,2,13),(1,2,13),(3,14,15),(2,2,4),(3,2,4),(3,0,8),(0,11,8),(1,0,6),(0,21,8),(1,0,5),(2,2,13),(3,2,13),(0,3,9),(0,1,26),(1,0,27),(1,1,26),(3,6,8),(3,17,8),(0,23,4),(1,32,2),(0,21,3),(3,34,1),(3,6,23),(3,0,29),(0,23,9),(3,6,3),(2,1,3),(3,1,3),(0,3,4),(1,3,4),(3,42,43),(3,2,3),(3,1,4),(1,45,46),(1,17,40),(3,46,3),(3,40,9),(1,1,2),(0,51,3),(2,23,2),(2,51,42),(0,21,1),(2,23,4),(0,51,4),(3,57,3),(0,52,4),(1,17,5),(2,3,4),(3,3,4),(0,1,43),(3,2,42),(1,1,42),(0,1,2),(1,0,66),(3,2,8),(2,1,4),(1,69,0),(2,2,1),(3,71,3),(2,8,4),(0,1,9),(3,2,43),(1,1,4),(0,76,3),(3,17,3),(3,0,43),(0,1,4),(2,1,2),(1,2,3)]
lemma W_10_ok : btAll (fun x => faithful p_10 q_10 x ∧ x.1 < 2^256) W_10 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_10 : List (List (Nat × Nat)) := [[],[(1,2),(3,4)]]
def A_10 : BT (List (Nat × Nat)) := btOfList 1 al_10
set_option maxHeartbeats 0 in
lemma A_10_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_10 = g_10) A_10 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_10_0 : Slice r_10 g_10 (subcubeFast 1 0) 7 := by
  have hc : Lower (varsOf 30) (d 0xfcc0c000fcc0c000) 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_1 : Slice r_10 g_10 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) (d 0xfa00a000fa00a000) 5 := carry_of (swaps := [(1,4),(2,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_2 : Slice r_10 g_10 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) (d 0xfffaf000fffaf000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_3 : Slice r_10 g_10 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) (d 0xee880000ee880000) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_4 : Slice r_10 g_10 (subcubeFast 0 4) 5 := by
  have hc : Lower (varsOf 27) (d 0xffccee00ffccee00) 5 := carry_of (swaps := [(2,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_5 : Slice r_10 g_10 (subcubeFast 0 8) 5 := by
  have hc : Lower (varsOf 23) (d 0xfefee0e0fefee0e0) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_6 : Slice r_10 g_10 (subcubeFast 0 16) 5 := by
  have hc : Lower (varsOf 15) (d 0xfec8fec8fec8fec8) 5 := carry_of (swaps := [(1,2)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_7 : Slice r_10 g_10 (subcubeFast 4 16) 4 := by
  have hc : Lower (varsOf 11) (d 0xee88ee88ee88ee88) 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_8 : Slice r_10 g_10 (subcubeFast 2 8) 4 := by
  have hc : Lower (varsOf 21) (d 0xfafaa0a0fafaa0a0) 4 := carry_of (swaps := [(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 2) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_9 : Slice r_10 g_10 (subcubeFast 1 8) 4 := by
  have hc : Lower (varsOf 22) (d 0xfcfcc0c0fcfcc0c0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_10 : Slice r_10 g_10 (identDom 1 4) 6 := by
  have hc : Lower (varsOf 15) (d 0xecc8ecc8ecc8ecc8) 6 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_6
  exact slice_ident (u := 1) (v := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_11 : Slice r_10 g_10 (identDom 2 3) 6 := by
  have hc : Lower (varsOf 23) (d 0xf8f8e0e0f8f8e0e0) 6 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_6
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_12 : Slice r_10 g_10 (identDom 0 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xeaeaa0a0eaeaa0a0) 5 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,4)]) (by decide +kernel) low_8
  exact slice_ident (u := 0) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_13 : Slice r_10 g_10 (identDom 1 2) 5 := by
  have hc : Lower (varsOf 27) (d 0xeecccc00eecccc00) 5 := carry_of (swaps := [(1,3),(2,4)]) (by decide +kernel) low_8
  exact slice_ident (u := 1) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_14 : Slice r_10 g_10 (subcubeFast 0 1) 4 := by
  have hc : Lower (varsOf 30) (d 0xffccf000ffccf000) 4 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
def S_10 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 1 0,7),some (subcubeFast 2 0,5),some (subcubeFast 0 2,5),some (subcubeFast 4 0,5),some (subcubeFast 0 4,5),some (subcubeFast 0 8,5),some (subcubeFast 0 16,5),some (subcubeFast 4 16,4),some (subcubeFast 2 8,4),some (subcubeFast 1 8,4),some (identDom 1 4,6),some (identDom 2 3,6),some (identDom 0 3,5),some (identDom 1 2,5),some (subcubeFast 0 1,4)]
lemma S_10_ok : btAll (fun o => ∀ p, o = some p → Slice r_10 g_10 p.1 p.2) S_10 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_10_0) (forall_cons (fun _ h => by cases h; exact sl_10_1) (forall_cons (fun _ h => by cases h; exact sl_10_2) (forall_cons (fun _ h => by cases h; exact sl_10_3) (forall_cons (fun _ h => by cases h; exact sl_10_4) (forall_cons (fun _ h => by cases h; exact sl_10_5) (forall_cons (fun _ h => by cases h; exact sl_10_6) (forall_cons (fun _ h => by cases h; exact sl_10_7) (forall_cons (fun _ h => by cases h; exact sl_10_8) (forall_cons (fun _ h => by cases h; exact sl_10_9) (forall_cons (fun _ h => by cases h; exact sl_10_10) (forall_cons (fun _ h => by cases h; exact sl_10_11) (forall_cons (fun _ h => by cases h; exact sl_10_12) (forall_cons (fun _ h => by cases h; exact sl_10_13) (forall_cons (fun _ h => by cases h; exact sl_10_14) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))
def ps_10 : BT (Option PoolSpec) := btOfList 7 [q 7 [],q 0 [16392,16393,36891],q 0 [16396,16397,176299],q 8 [],q 0 [],q 5 [],q 2 [],q 4 [],q 3 [],q 0 [16394,16395],q 14 [],q 1 [],q 2 [20481],q 5 [20481],q 6 [],q 0 [12292,12293],q 0 [16393,36876],q 3 [36876],q 6 [24577],q 0 [12292],q 0 [16392,16393],q 0 [16393,12324],q 3 [12324],q 9 [],q 12 [],q 1 [32771],q 0 [16398,16399],q 0 [16397,176132],q 0 [16398,12535],q 0 [16396,16397],q 3 [16396],q 0 [16394],q 0 [16391,12475],q 0 [16395],q 0 [16392,12299],q 1 [12299],q 0 [16392,12315],q 0 [16392],q 0 [8196],q 0 [16393],q 0 [8197,12492],q 1 [12492],q 0 [12293,32779],q 1 [32779],q 0 [16390],q 0 [4106,12575],q 0 [12293],q 0 [12293,16418],q 1 [16418],q 0 [16393,36868],q 3 [36868],q 0 [12305,176139],q 0 [16389,12592],q 0 [8196,8197],q 13 [],q 0 [16394,12359],q 0 [16388,16389],q 10 [],q 0 [16398],q 0 [8197],q 0 [8198],q 0 [12299],q 11 [],q 0 [16388],q 0 [12297],q 0 [16396],q 0 [16397]]
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
def N_10_3 : List NodeSpec := [([16,0,1,3],[],[]),([17,18,12,0],[],[0]),([0,7,8,9],[],[0]),([11,19,1,3],[],[]),([20,0,1,3],[],[]),([0,5,6,10],[],[0]),([11,0,5,8],[],[0]),([5,2,22,4],[],[]),([11,1,23,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_10_3 : checkNodesBT W_10 g_10 F_10 P_10_3 A_10 B_10_2 3 N_10_3 = true := by decide +kernel
def B_10_3 : BT (List (List Nat)) := buildBucketsBT W_10 N_10_3
set_option maxRecDepth 500000 in
lemma B_10_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_10 3 xs.toFinset) B_10_3 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok (buildPoolsSubBT_sound S_10_ok) A_10_ok B_10_2_ok C_10_3
def U_10_4 : List Nat := [0,1]
def P_10_4 : BT (Option BoundPool) := buildPoolsSubBT 7 W_10 r_10 S_10 ps_10 U_10_4
def N_10_4 : List NodeSpec := [([24,25,0,1,3],[],[0]),([1,28,2,26,4],[],[]),([0,1,2,26,13],[],[]),([0,27,2,29,4],[],[1]),([19,1,2,26,4],[],[]),([17,18,19,1,3],[],[0]),([17,18,0,5,8],[],[0]),([0,5,2,10,4],[],[0,1]),([30,0,1,3,9],[],[0]),([19,1,6,3,9],[],[0]),([18,0,1,3,31],[0],[]),([17,18,1,23,3],[],[0]),([0,1,7,3,9],[],[0]),([1,23,33,3,4],[],[]),([35,2,21,3,4],[],[]),([36,1,2,3,4],[],[]),([37,1,2,26,4],[],[]),([1,23,2,26,4],[],[]),([18,12,0,2,4],[],[0]),([1,38,2,3,4],[],[1]),([0,5,6,8,9],[],[0,1]),([39,0,1,2,13],[],[]),([17,40,18,41,0],[],[0,1]),([11,0,1,3,8],[0,1],[0]),([11,0,5,1,3],[1],[0]),([5,2,21,8,4],[],[0,1]),([17,12,0,2,4],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_10_4 : checkNodesBT W_10 g_10 F_10 P_10_4 A_10 B_10_3 4 N_10_4 = true := by decide +kernel
def B_10_4 : BT (List (List Nat)) := buildBucketsBT W_10 N_10_4
set_option maxRecDepth 500000 in
lemma B_10_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_10 4 xs.toFinset) B_10_4 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok (buildPoolsSubBT_sound S_10_ok) A_10_ok B_10_3_ok C_10_4
def U_10_5 : List Nat := (r 0 26)
def P_10_5 : BT (Option BoundPool) := buildPoolsSubBT 7 W_10 r_10 S_10 ps_10 U_10_5
def N_10_5 : List NodeSpec := [([44,0,1,2],[0,2,3],[]),e5 [47] [],([17,40,18,0,1,3],[],[0,1]),e5 [48] [],([25,0,1,2,3,13],[],[0]),([0,49,1,2,42,4],[4,5,6],[]),([24,0,1,2,3,13],[],[0]),([17,0,1,2,3,13],[7],[]),([17,18,41,0,1,3],[],[0,1]),([17,18,0,1,3,8],[0,7,8,9],[0]),a5 [50] [6,7] [1],a5 [10] [4,6,7,10,11] [0,1],([1,23,2,3,4,9],(r 10 4),[0,1]),([0,1,2,52,42,4],[6,7,14],[]),([5,1,2,21,3,4],[10],[0,1]),([17,1,23,2,3,4],[11,12],[0]),([0,5,2,8,4,9],[6,11,15],[0,1]),([0,1,2,26,8,4],[7,11,14,16,17],[0]),([1,32,23,2,3,4],[10],[0,1]),([53,1,23,2,3,4],[10],[]),([44,0,1,2,42],[0,2,3],[]),e5 [54] [],([39,41,0,1,2,4],[11],[]),([45,1,21,3,4],[8,18],[]),([55,1,2,21,3,4],[10],[]),([17,18,0,5,1,3],[9],[0]),([56,1,23,2,3,4],[10,11,19],[]),([39,0,1,2,8,4],[8,11],[0]),([11,0,1,3],[0,1],[0,1]),e5 [58] [],([0,5,1,6,3,9],[8,20],[0,1]),([18,0,5,2,8,4],[],[0]),([0,27,1,2,26,4],[7,21,22],[0,1]),([17,19,1,2,3,4],[],[0]),a5 [7] [4,10] [0,1],([19,1,6,2,3,4],[10,23],[0]),([0,1,2,26,29,4],[7,14,21,22],[0]),e5 [59] [4,6,11,24],([0,5,1,2,26,4],[6,7,14,16,17],[0,1]),([18,19,1,2,3,4],[],[0]),([18,0,1,2,3,13],[6,8],[]),u5 [30] [4,6,10],([18,1,23,2,3,4],[],[0]),([17,0,5,2,8,4],[],[0]),e5 [60] [],([19,1,2,3,4,9],[6,10,23,25],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_10_5 : checkNodesBT W_10 g_10 F_10 P_10_5 A_10 B_10_4 5 N_10_5 = true := by decide +kernel
def B_10_5 : BT (List (List Nat)) := buildBucketsBT W_10 N_10_5
set_option maxRecDepth 500000 in
lemma B_10_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_10 5 xs.toFinset) B_10_5 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok (buildPoolsSubBT_sound S_10_ok) A_10_ok B_10_4_ok C_10_5
def U_10_6 : List Nat := ([0]++r 3 9++[13,14,15,19,21,22,23]++r 26 32)
def P_10_6 : BT (Option BoundPool) := buildPoolsSubBT 7 W_10 r_10 S_10 ps_10 U_10_6
def N_10_6 : List NodeSpec := [([61,62,0,1,2],[0,5,14,26],[0]),([0,63,2,3,4],[5,11,14,27],[]),e5 [42] [0,3,4,6,7,8,11,28],([0,1,2,42,43],[0,3,5,29],[0]),a5 [64,42] [0,7,8] [1],a5 [45,42] [5,7,8,14,30] [1],u5 [45,46] [0,6,7,8,11],u5 [17,5] [6,7,8,11,31],e5 [42,65] [3,6],([1,23,2,3,4],[3,10,11,13,19],[0,1]),([0,5,2,8,4],[6,11,15],[0,1]),u5 [49] (r 3 6++[11,32]),a5 [18,41] [0,6,7] [0,1],a5 [18,5] [0,7,11,33] [0,1],([45,0,1,6,3,4],[5,7,8,14,34,35],[0]),u5 [39] ([0]++r 4 5++[11,36]),a5 [5,6] [8,11,19,37] [0,1],([1,67,2,3,4],[0,3,11,38],[]),a5 [5,9] (r 5 4++[11,14,19,39]) [0,1],a5 [52] [3,4,6,7,8,11,14,40,41] [0,1],([68,0,1,3,4],[5,6,7,42,43],[]),([70,1,2,3,4],[0,3,11,44],[]),e5 [72] [0,4,6,11,45],a5 [8,9] (r 5 4++[11,14,39,46]) [0,1],([73,0,1,2,3],[5,6,14,47,48],[]),a5 [51,42] [0,5,6,7,11] [0,1],([19,1,2,3,4],[6,23,46],[0]),([0,74,2,3,4],[7,11,14,49,50],[]),a5 [17,8] [6,7,8,14,31] [0,1],([75,0,1,3,4],[5,7,14,51],[]),e5 [77] [0,3,4,6,7,8,11,52],([0,1,2,26,4],[7,14,21,22],[0,1]),a5 [26] [6,7,8,11,14,21] [0,1],([0,66,51,3,4],[0,6,11,53,54],[]),u5 [18,8] [0,6,7,33],e5 [78] [6,8,11,14,55],a5 [17,40] [8,11] [0,1],a5 [17,41] [3,6] [0,1],([17,18,0,1,3],[7,8,9],[0]),([79,1,2,3,4],[0,3],[]),([0,80,2,3,76],[0,3,11,56,57],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_10_6 : checkNodesBT W_10 g_10 F_10 P_10_6 A_10 B_10_5 6 N_10_6 = true := by decide +kernel
def B_10_6 : BT (List (List Nat)) := buildBucketsBT W_10 N_10_6
set_option maxRecDepth 500000 in
lemma B_10_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_10 6 xs.toFinset) B_10_6 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok (buildPoolsSubBT_sound S_10_ok) A_10_ok B_10_5_ok C_10_6
def U_10_7 : List Nat := ([0]++r 3 6++[11,14,19,31,33,38,44,46,54]++r 57 10)
def P_10_7 : BT (Option BoundPool) := buildPoolsSubBT 7 W_10 r_10 S_10 ps_10 U_10_7
def N_10_7 : List NodeSpec := [u5 [61] [0,3,4,6,7,8,11,14,58],a5 [5] (r 3 6++[11,14,19]) [0,1],u5 [66] ([0]++r 3 4++[11,14,38]),a5 [51] ([0,3]++r 5 4++[11,14,59]) [0,1],a5 [8] (r 5 4++[14,46]) [0,1],a5 [18] ([0]++r 4 4++[11,33]) [0,1],a5 [81] (r 3 6++[11,14,54,60]) [1],a5 [45] [0,3,4,6,7,8,11,14,61,62] [0,1],u5 [80] ([0]++r 3 6++[11,63]),a5 [82] ([3]++r 5 4++[11,14,64]) [1],u5 [69] (r 3 6++[11,14,44,57]),a5 [42] [0,3,6,7,65] [0,1],u5 [17] (r 4 5++[11,14,31]),a5 [43] [0,5,6,11,66] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_10_7 : checkNodesBT W_10 g_10 F_10 P_10_7 A_10 B_10_6 7 N_10_7 = true := by decide +kernel
def B_10_7 : BT (List (List Nat)) := buildBucketsBT W_10 N_10_7
set_option maxRecDepth 500000 in
lemma B_10_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_10 7 xs.toFinset) B_10_7 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok (buildPoolsSubBT_sound S_10_ok) A_10_ok B_10_6_ok C_10_7
def U_10_8 : List Nat := [4]
def P_10_8 : BT (Option BoundPool) := buildPoolsSubBT 7 W_10 r_10 S_10 ps_10 U_10_8
def N_10_8 : List NodeSpec := [a5 [] [4] [0,1]]
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
def g_11 := (d 0xf880f880f880f880)
def r_11 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_11 : Lower r_11 g_11 5 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,6,7)]) (by decide +kernel) hc
def g_12 := (d 0xfea8c000fea8c000)
def r_12 : List Nat := varsOf 31
def p_12 : List Nat := [14,14,14,15,15,15,19,19,19,21,21,21,23,23,25,25,25,26,26,26,27,28,28,28,29,30]
def q_12 : List Nat := [12,10,6,13,11,7,18,17,3,20,17,5,22,7,24,17,9,24,18,10,11,24,20,12,13,22]
def F_12 : Nat := fullMask 26
set_option maxHeartbeats 0 in
lemma gp_12 : goodPairs g_12 p_12 q_12 := goodPairs_of (by decide +kernel)
def W_12 : BT Decor := buildWiresBT 8 (mkBase p_12 q_12 r_12) [(0,0,4),(1,1,2),(0,6,3),(1,5,7),(0,3,4),(0,2,4),(1,1,10),(2,11,3),(3,2,3),(0,11,3),(2,6,3),(0,1,2),(3,16,3),(0,0,3),(3,18,6),(1,2,4),(3,10,20),(1,0,7),(0,22,4),(2,0,3),(1,24,1),(0,1,4),(1,26,2),(2,6,9),(0,7,4),(0,27,3),(2,0,30),(1,5,2),(0,6,4),(1,5,1),(1,34,2),(0,35,3),(3,0,4),(1,37,7),(1,24,16),(3,6,3),(3,40,4),(2,0,7),(3,33,3),(1,3,4),(3,9,44),(0,3,20),(2,0,46),(1,1,4),(0,3,48),(0,0,49),(1,1,3),(3,2,51),(1,2,3),(3,1,53),(3,54,4),(0,1,3),(1,13,1),(0,2,3),(1,58,1),(3,6,4),(3,60,3),(1,13,10),(0,57,4),(3,7,4),(3,3,4),(3,65,6),(3,1,3),(3,58,6),(3,10,51),(0,0,6),(2,2,1),(1,71,13),(3,67,4),(2,34,2),(3,24,6),(0,25,4),(2,0,2),(1,77,26),(3,2,48),(0,1,20),(3,18,48),(2,1,2),(1,82,18),(1,18,26),(3,10,1),(1,77,1),(0,86,4),(1,18,1),(0,88,4),(2,1,4),(1,24,82),(1,18,2),(1,90,18),(1,18,16),(1,24,26),(3,24,48),(0,53,4),(1,90,24),(3,1,4),(0,0,11),(3,5,6),(1,13,26),(1,1,9),(3,2,9),(2,3,4),(3,105,0),(3,2,44),(0,0,44),(1,65,1),(3,2,4),(2,2,4),(3,111,0),(3,13,4),(3,111,3),(2,2,3),(1,115,1),(0,51,4),(2,0,1),(3,118,4),(0,1,44),(3,18,4),(2,0,58),(3,24,4),(3,13,1),(0,0,2),(1,125,1),(2,1,3),(1,127,2),(3,3,48),(3,115,1),(3,10,3),(0,0,48),(3,71,3),(0,0,1),(2,0,4)]
lemma W_12_ok : btAll (fun x => faithful p_12 q_12 x ∧ x.1 < 2^256) W_12 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_12 : List (List (Nat × Nat)) := [[],[(1,2)]]
def A_12 : BT (List (Nat × Nat)) := btOfList 1 al_12
set_option maxHeartbeats 0 in
lemma A_12_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_12 = g_12) A_12 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_12_0 : Slice r_12 g_12 (subcubeFast 0 1) 6 := by
  have hc : Lower (varsOf 30) (d 0xfffcc000fffcc000) 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_1 : Slice r_12 g_12 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) (d 0xfaa00000faa00000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_2 : Slice r_12 g_12 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) (d 0xfc00c000fc00c000) 5 := carry_of (swaps := [(0,4),(1,4),(2,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_3 : Slice r_12 g_12 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) (d 0xee880000ee880000) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_4 : Slice r_12 g_12 (subcubeFast 0 8) 5 := by
  have hc : Lower (varsOf 23) (d 0xfefec0c0fefec0c0) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_5 : Slice r_12 g_12 (subcubeFast 0 16) 5 := by
  have hc : Lower (varsOf 15) (d 0xfea8fea8fea8fea8) 5 := carry_of (swaps := [(0,2),(1,2)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_6 : Slice r_12 g_12 (subcubeFast 4 16) 4 := by
  have hc : Lower (varsOf 11) (d 0xee88ee88ee88ee88) 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_7 : Slice r_12 g_12 (subcubeFast 2 16) 4 := by
  have hc : Lower (varsOf 13) (d 0xfaa0faa0faa0faa0) 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 2) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_8 : Slice r_12 g_12 (subcubeFast 1 8) 4 := by
  have hc : Lower (varsOf 22) (d 0xfcfcc0c0fcfcc0c0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_9 : Slice r_12 g_12 (identDom 1 2) 5 := by
  have hc : Lower (varsOf 27) (d 0xee88cc00ee88cc00) 5 := carry_of (swaps := [(1,2),(2,4)]) (by decide +kernel) low_11
  exact slice_ident (u := 1) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_10 : Slice r_12 g_12 (identDom 1 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xececc0c0ececc0c0) 5 := carry_of (swaps := [(1,3),(2,3),(3,4)]) (by decide +kernel) low_8
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_11 : Slice r_12 g_12 (identDom 2 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xf8f8c0c0f8f8c0c0) 5 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_8
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_12 : Slice r_12 g_12 (subcubeFast 0 4) 4 := by
  have hc : Lower (varsOf 27) (d 0xffaacc00ffaacc00) 4 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_13 : Slice r_12 g_12 (subcubeFast 0 2) 4 := by
  have hc : Lower (varsOf 29) (d 0xffaaf000ffaaf000) 4 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
def S_12 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 0 1,6),some (subcubeFast 2 0,5),some (subcubeFast 1 0,5),some (subcubeFast 4 0,5),some (subcubeFast 0 8,5),some (subcubeFast 0 16,5),some (subcubeFast 4 16,4),some (subcubeFast 2 16,4),some (subcubeFast 1 8,4),some (identDom 1 2,5),some (identDom 1 3,5),some (identDom 2 3,5),some (subcubeFast 0 4,4),some (subcubeFast 0 2,4)]
lemma S_12_ok : btAll (fun o => ∀ p, o = some p → Slice r_12 g_12 p.1 p.2) S_12 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_12_0) (forall_cons (fun _ h => by cases h; exact sl_12_1) (forall_cons (fun _ h => by cases h; exact sl_12_2) (forall_cons (fun _ h => by cases h; exact sl_12_3) (forall_cons (fun _ h => by cases h; exact sl_12_4) (forall_cons (fun _ h => by cases h; exact sl_12_5) (forall_cons (fun _ h => by cases h; exact sl_12_6) (forall_cons (fun _ h => by cases h; exact sl_12_7) (forall_cons (fun _ h => by cases h; exact sl_12_8) (forall_cons (fun _ h => by cases h; exact sl_12_9) (forall_cons (fun _ h => by cases h; exact sl_12_10) (forall_cons (fun _ h => by cases h; exact sl_12_11) (forall_cons (fun _ h => by cases h; exact sl_12_12) (forall_cons (fun _ h => by cases h; exact sl_12_13) (fun _ h => (List.not_mem_nil h).elim)))))))))))))))
def ps_12 : BT (Option PoolSpec) := btOfList 7 [q 0 [16392,16393,81963],q 0 [],q 1 [16384,16408],q 9 [12312,28674],q 8 [],q 7 [],q 6 [],q 0 [16393,81932],q 10 [],q 1 [196620],q 0 [16389,196620],q 2 [],q 3 [],q 1 [16392],q 5 [],q 13 [],q 1 [],q 0 [12299,4149],q 0 [16388,8297],q 3 [16388],q 12 [],q 4 [],q 11 [],q 9 [],q 9 [12314],q 0 [8196,8197],q 9 [12312],q 9 [24576],q 1 [16408],q 5 [4105],q 5 [8197],q 9 [12290],q 0 [16388,16389],q 0 [16388,106805],q 0 [16389,196619],q 3 [81924],q 0 [16393,81924],q 0 [16389,196683],q 0 [8198,74057],q 0 [16388,106569],q 0 [16392,4139],q 9 [12288],q 0 [16389,196707],q 0 [16390,16391],q 0 [16392,4137],q 1 [16384],q 4 [16384],q 1 [16387],q 4 [16387],q 0 [16396,36869],q 1 [16395],q 3 [16439],q 2 [12299],q 0 [16389],q 0 [12299],q 0 [16396],q 3 [16384],q 1 [16859],q 0 [16859],q 0 [8196],q 2 [16396],q 0 [16390],q 0 [16388],q 0 [8197],q 0 [16459],q 0 [16483],q 0 [12296],q 0 [12292],q 0 [16391],q 0 [8198],q 0 [4169],q 0 [4117],q 0 [16395],q 0 [16399],q 3 [16387],q 0 [12293],q 0 [4597],q 2 [12295],q 1 [196619],q 1 [196623],q 0 [16389,196623],q 2 [12292],q 0 [16392,12331],q 0 [4193],q 1 [196608],q 0 [4106,12575],q 0 [4405]]
def B_12_2 : BT (List (List Nat)) := BT.empty
lemma B_12_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 2 xs.toFinset) B_12_2 := .empty
def U_12_3 : List Nat := []
def P_12_3 : BT (Option BoundPool) := buildPoolsSubBT 7 W_12 r_12 S_12 ps_12 U_12_3
def N_12_3 : List NodeSpec := [([1,2,8,9],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_3 : checkNodesBT W_12 g_12 F_12 P_12_3 A_12 B_12_2 3 N_12_3 = true := by decide +kernel
def B_12_3 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_3
set_option maxRecDepth 500000 in
lemma B_12_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 3 xs.toFinset) B_12_3 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_2_ok C_12_3
def U_12_4 : List Nat := (r 0 4)
def P_12_4 : BT (Option BoundPool) := buildPoolsSubBT 7 W_12 r_12 S_12 ps_12 U_12_4
def N_12_4 : List NodeSpec := [([12,13,0,11,4],[],[]),([13,0,14,11,4],[],[]),([15,17,0,6,4],[],[]),([19,0,16,3,4],[],[]),([21,18,0,1,3],[0],[]),([1,2,7,23,3],[],[]),([0,25,27,3,4],[],[]),([28,5,1,2,3],[],[]),([5,1,2,29,3],[1],[]),([31,1,27,3,4],[],[]),([17,0,7,6,4],[],[]),([5,1,32,33,3],[2],[]),([24,21,0,1,3],[0],[]),([5,1,2,36,4],[],[]),([1,2,38,3,4],[],[]),([0,39,6,3,4],[],[]),([13,5,1,33,3],[2],[]),([1,2,8,3,4],[1],[0]),([5,1,2,7,9],[],[0]),([5,1,2,41,3],[],[]),([42,16,6,3,4],[3],[]),([43,5,1,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_4 : checkNodesBT W_12 g_12 F_12 P_12_4 A_12 B_12_3 4 N_12_4 = true := by decide +kernel
def B_12_4 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_4
set_option maxRecDepth 500000 in
lemma B_12_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 4 xs.toFinset) B_12_4 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_3_ok C_12_4
def U_12_5 : List Nat := ([0,1,2]++r 4 45)
def P_12_5 : BT (Option BoundPool) := buildPoolsSubBT 7 W_12 r_12 S_12 ps_12 U_12_5
def N_12_5 : List NodeSpec := [([45,0,1,2],[4,5,6],[]),([47,0,1,2,46,4],[7],[]),([50,0,1,2,49,4],[8,9,10],[]),e5 [14] [1,8,11,12],([13,0,11,3,4],[5,6,12,13],[0]),([52,0,1,10,3,4],[14,15],[]),e5 [55] [16],([0,56,57,2,3,4],[16,17],[]),([0,56,2,59,3,4],[16],[]),([0,1,30,27,3,4],[16,18,19,20],[0,1]),e5 [61] [1,11],([0,1,2,33,9,3],[5,6,15,20,21],[]),u5 [43] [],u5 [41] [],e5 [7] [1,11],([13,0,1,3,62,4],[12],[]),e5 [63] [16],([42,1,2,6,3,4],[],[0]),([0,1,2,7,9,4],[8,14,22],[0]),e5 [64] [1,11],([42,1,2,7,3,4],[1],[]),([1,2,7,22,3,4],[11],[0]),e5 [66] [1,11],([13,67,0,6,3,4],[12,16,21],[]),([0,56,58,6,3,4],[16,21],[]),([68,0,1,6,3,4],[12,16],[]),e5 [69] [16],([15,0,16,6,3,4],[16,20,23,24],[0]),([0,16,7,6,3,4],[16,20,23,25,26],[0]),([70,0,16,6,3,4],[25,27],[]),([13,0,1,33,3,4],[6,12,28,29],[0]),([17,0,6,3,4],[6,16,23,30],[0]),([12,0,2,11,3,4],[5,12,15],[0]),([13,72,0,1,3,4],[12],[]),([24,0,16,6,3,4],[16,25,31],[0]),([0,1,73,2,9,3],[8,21],[]),([74,5,1,2,3,4],[],[]),e5 [75] [11],e5 [76] [],u5 [39] [],([40,5,1,2,3,4],[14],[0]),([24,0,1,2,7,4],[1],[]),([18,0,26,2,3,48],[32],[1]),([65,0,1,2,7,4],[],[]),e5 [78] [33],([18,0,1,2,49,4],[1,8,9],[]),([0,26,25,2,3,4],[],[0]),([24,0,1,2,49,4],[1],[]),([79,18,0,1,3,4],[34],[]),([18,0,80,2,3,4],[20,35,36],[]),e5 [81] [1,37],e5 [83] [38],([82,0,25,2,3,4],[],[]),e5 [84] [39],([85,18,0,2,3,4],[40],[]),([5,0,1,2,33,3],[1,6,15,20],[]),([0,26,86,2,3,4],[20],[]),e5 [87] [16],e5 [89] [11,12,15,20],([18,0,1,2,7,4],[1],[]),([90,0,88,2,3,4],[11],[]),e5 [91] [],([18,0,16,6,3,4],[20,25,41],[0]),([45,0,1,2,9],[4,5,6,21],[]),([24,79,0,1,3,4],[34],[]),([21,0,1,3],[0,5,6],[0]),([0,16,1,92,3,4],[20],[]),([5,1,2,33,6,3],[2,6],[]),([52,37,1,2,3,4],[],[]),([13,0,1,11,3,4],[13,21],[]),([18,0,1,27,3,4],[18],[]),e5 [93] [1],e5 [94] [],u5 [19] [],([24,0,80,2,3,4],[36],[]),e5 [95] [],e5 [96] [42],([24,0,1,27,3,4],[16,18],[0]),([0,26,1,2,3,97],[6,15,20],[]),([37,1,2,7,3,4],[1],[0]),([24,0,26,2,3,48],[32],[1]),u5 [29] [1,11,12,16],([13,0,56,6,3,4],[16,21],[]),e5 [98] [1],([90,24,99,0,2,3],[43],[1]),([100,0,2,11,3,4],[44],[]),([5,1,32,6,3,4],[11,45],[0]),([5,1,2,7,3,4],[11,14],[0]),([5,1,2,35,3,4],[1,14,46],[0]),([5,1,2,33,3],[1,5,6],[0,1]),([101,5,1,2,3,4],[1,14],[]),([13,5,1,6,3,4],[45,46],[0]),([0,26,57,2,3,4],[20],[]),u5 [28] [],([90,99,18,0,2,3],[43],[1]),([5,1,2,6,9,3],[5,6,46],[0]),e5 [102] [16],([5,1,57,2,3,4],[],[]),([5,1,2,9,3,103],[5],[]),([37,1,57,2,3,4],[],[]),([104,5,1,2,9,3],[6],[]),([24,85,0,2,3,4],[40],[]),e5 [101] [11],([13,37,1,6,3,4],[47,48],[]),([40,37,1,2,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_5 : checkNodesBT W_12 g_12 F_12 P_12_5 A_12 B_12_4 5 N_12_5 = true := by decide +kernel
def B_12_5 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_5
set_option maxRecDepth 500000 in
lemma B_12_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 5 xs.toFinset) B_12_5 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_4_ok C_12_5
def U_12_6 : List Nat := ([1,4,5,6]++r 8 11++r 20 4++[25,28,29,31,32,34,35,36,40,41]++r 43 44)
def P_12_6 : BT (Option BoundPool) := buildPoolsSubBT 7 W_12 r_12 S_12 ps_12 U_12_6
def N_12_6 : List NodeSpec := [([106,1,2,3,4],[1,5,6,11],[]),([107,0,1,3,4],[5,6,21],[]),([108,1,2,3,4],[1,6,11,21],[]),a5 [104,9] [6,12,22] [0,1],e5 [109] [4,5,12,15,20],e5 [103] [5,11,12,15,20,49],([90,99,0,2,3],[5,6,16,43],[0,1]),u5 [49] [1,5,6,10,11,14,16],([0,1,2,49,4],[5,6,9,10],[0,1]),([85,0,2,3,4],[6,12,16,40],[0]),u5 [11] [5,11,12,15,21,44],a5 [13,9] [4,6,22] [1],([13,110,0,1,3,4],[6,12,14,20,21,50],[]),([112,1,2,3,4],[1,5,11,12],[]),u5 [13,67] [8,12,16,21,22],e5 [13,113] [12,14,20,21,22,51],e5 [104] [1,6,11,15,16,22],e5 [13,57] [12,16,20,22],u5 [57] ([8,11,12]++r 14 4++[20]),([0,1,2,9,44],[4,5,6],[0]),u5 [9,103] [5,8],e5 [114] [1,5,11,12,14],e5 [116] [4,6],a5 [117] [1,4,5,11,12,20] [1],([13,0,1,10,3,4],[6,12,13,14,21,52],[0]),e5 [110,51] [5,6,20,21],a5 [24,48] [11,14,21,53] [0,1],u5 [13,56] [4,8,12,16,22,54],([5,1,2,9,3,4],[1,4,5,6,11,45,55,56],[]),e5 [119] [1,4,5,11,12,20,57,58],u5 [24,16] [1,11,16,59],e5 [13,99] [5,6,8,12,15,20],([5,1,2,9,3],[4,5,6,60],[0,1]),u5 [90,18] [1,11,16,61],([0,120,2,3,4],[6,16,21],[]),([105,5,1,2,3],[4,6,14],[]),([13,5,1,2,3,4],[4,6,11,45,56],[0]),a5 [52] [1,4,11,12,14,15,16,20] [0,1],u5 [77,26] [6,11,12,16,20,62],([37,1,2,6,3,4],[5,6,47,48,63],[0,1]),([5,1,2,3,4],[1,4,5,6,11],[]),e5 [121] [1,4,11,12,15,16,20,21,64],([0,56,2,51,4],[4,5,8,16],[]),([122,1,2,3,4],[4,6,11],[]),e5 [123] [11,12,15,16,20,21,65],u5 [24,6] [1,11,12,15,16,20,21,63],a5 [56,58] [4,12,16,66,67] [0,1],([0,1,27,3,4],[5,6,16,18,20],[0,1]),e5 [77,99] [5,6,11,15,68],u5 [13,26] [6,12,16,20,22],u5 [82,18] [11,12,16,20,41,69],a5 [88] [4,11,12,14,15,20,70] [0,1],([5,1,34,2,3,4],[4,5,11,45,56,71],[0,1]),a5 [24,26] [1,11,16,62] [0,1],u5 [90,24] [1,11,16,61],a5 [110,18] [6,11,20,72] [1],e5 [13,124] [12,15,16,20,21,22],a5 [24,110] [1,6,11,20,72] [1],([105,65,0,1,2],[5,6,14,21],[0]),([65,37,1,2,3,4],[1,5,6,47,48,73,74],[]),u5 [18,6] [1,11,20,21,63],a5 [18,26] [11,16,62] [0,1],([37,1,2,3,51,4],[1,5,48,74,75],[0]),a5 [18,16] [11,12,16,59] [0,1],u5 [17] [1,6,11,12,16],u5 [59] [1,6,8,11,16],a5 [18,48] [11,15,16,21,53] [0,1],([5,1,2,6,3,4],[5,6,11,46,63],[0,1]),e5 [9] [1,4,5,6,11,12,14,16],a5 [26,53] [6,12,16,20] [0,1],u5 [24,82] [1,11,16,31,69],e5 [126] [4,6,11,12,76],([0,1,128,3,4],[4,5,16],[]),([82,67,0,2,3,4],[5,12,15,16,21,77],[1]),e5 [34] [4,5,11,12,15,20,71],u5 [5,6] [1,6,11,12,15,16,20,63],([79,0,1,3,4],[5,6,34,78],[0]),([13,37,1,2,3,4],[1,6,47,48,54,74],[0]),([129,0,1,2,4],[5,6,21,79,80],[]),([0,80,2,3,4],[6,16,35,36],[0]),([37,1,2,9,3,4],[1,4,5,6,47,55,74],[]),u5 [33,6] [5,6,16,20,28],([0,130,2,3,4],[6,12,16,21],[]),([0,16,6,3,4],[6,16,20,23,25],[0]),u5 [70,6] [1,11,63],u5 [7] [1,11,12,14,15,16,20],u5 [73] [1,5,8,11,12,20],([0,56,2,6,3,4],[5,12,15,16,21,81],[0,1]),e5 [131] [1,6,11,12,15,16,82],u5 [60] [1,5,6,8,11,15,20,21],u5 [25] [11,12,14,15,20,21,83],([13,0,1,6,3,4],[6,12,16,20,21,29,52],[0]),u5 [7,6] [12,15,16,20,21,63],u5 [15,6] [12,15,16,20],([132,1,2,3,4],[1,5,6,11,84],[]),a5 [33] [1,5,6,11,20,21,28] [0,1],u5 [40] [1,8,11,14,15,20],u5 [6,9] [5,6,15,16,20,21],u5 [65,6] [5,6,12,15,16,20,21],u5 [6] [1,6,11,15,16,20,21],([0,26,2,3,48],[6,16,32],[0,1]),e5 [133] [1,6,11,15,16,85],u5 [86] [4,11,14,15,16,20,86],e5 [13] [1,4,6,11,12,15,16,20,21]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_6 : checkNodesBT W_12 g_12 F_12 P_12_6 A_12 B_12_5 6 N_12_6 = true := by decide +kernel
def B_12_6 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_6
set_option maxRecDepth 500000 in
lemma B_12_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 6 xs.toFinset) B_12_6 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_5_ok C_12_6
def U_12_7 : List Nat := ([1,4,5,6,8,11,12,14,15,16]++r 20 4++[53,54,55,59,61,62,63,67,69,72,73,75])
def P_12_7 : BT (Option BoundPool) := buildPoolsSubBT 7 W_12 r_12 S_12 ps_12 U_12_7
def N_12_7 : List NodeSpec := [a5 [65] [1,4,5,6,11,12,16,21,73] [0,1],a5 [44] [1,5,6,11,21] [0,1],a5 [110] [1,5,6,11,16,21,72] [0,1],a5 [9] [4,5,6,55] [0,1],a5 [90] [1,6,11,16,21,61] [0,1],a5 [26] [1,5,6,11,16,21,62] [0,1],a5 [127] [1,4,5,8,11,12,14,16,21] [0,1],a5 [134] [1,4,5,12,14,16,21] [1],([5,1,2,3,4],[1,4,5,6,11],[0,1]),u5 [105] [1,4,5,6,11,14],a5 [77] [1,4,6,11,12,14,16,20,21] [0,1],a5 [18] [1,4,11,12,14,16] [0,1],a5 [24] [1,11,12,14,16,21] [0,1],u5 [135] [1,4,5,6,11,21],a5 [48] [1,5,6,11,16,21,53] [0,1],a5 [13] [1,4,6,11,12,14,16,20,22,54] [0,1],a5 [82] [1,5,11,12,14,16,20,21,23,69] [0,1],([37,1,2,3,4],[1,5,6],[0,1]),a5 [51] [4,5,12,15,16,75] [0,1],a5 [5] [1,4,5,6,11,12,16,21] [0,1],u5 [16] [1,6,11,12,16,21,59],a5 [6] [5,6,11,12,15,16,20,21,63] [0,1],a5 [56] [1,4,5,11,12,16,67] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_7 : checkNodesBT W_12 g_12 F_12 P_12_7 A_12 B_12_6 7 N_12_7 = true := by decide +kernel
def B_12_7 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_7
set_option maxRecDepth 500000 in
lemma B_12_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 7 xs.toFinset) B_12_7 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_6_ok C_12_7
def U_12_8 : List Nat := [1]
def P_12_8 : BT (Option BoundPool) := buildPoolsSubBT 7 W_12 r_12 S_12 ps_12 U_12_8
def N_12_8 : List NodeSpec := [a5 [] [1] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_8 : checkNodesBT W_12 g_12 F_12 P_12_8 A_12 B_12_7 8 N_12_8 = true := by decide +kernel
def B_12_8 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_8
set_option maxRecDepth 500000 in
lemma B_12_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 8 xs.toFinset) B_12_8 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_7_ok C_12_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_12_ok : forestRootCheck r_12 g_12 [(VAR 0,18,19),(VAR 1,12,14),(VAR 2,10,14),(VAR 3,6,14),(VAR 4,3,19)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_12_in : bucketContainsBT B_12_8 r_12 = true := by decide +kernel
lemma low_12 : Lower r_12 g_12 9 := lower_of_forestBT root_12_ok B_12_8_ok root_12_in
def g_13 := (d 0xfee0c000fee0c000)
def r_13 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_13 : Lower r_13 g_13 8 := by
  have hc : Lower (varsOf 30) (d 0xfcc0c000fcc0c000) 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,20,21)]) (by decide +kernel) hc
def g_14 := (d 0xfee80000fee80000)
def r_14 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_14 : Lower r_14 g_14 8 := by
  exact lift_of_f (z := 0) (o := 16) (other := r_2) (G := g_2) (essPairs := [(VAR 4,3,19)]) (by decide +kernel) low_2
def g_15 := (d 0xfffefee0fffefee0)
def r_15 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_15 : Lower r_15 g_15 8 := by
  have hc : Lower (varsOf 30) (d 0xfffcfcc0fffcfcc0) 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_2
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,4,5)]) (by decide +kernel) hc
def g_16 := (d 0xfffef800fffef800)
def r_16 : List Nat := varsOf 31
def p_16 : List Nat := [11,11,11,12,12,13,13,14,14,15,17,17,18,18,19,20,20,21,22,23,24,24,25,26]
def q_16 : List Nat := [10,9,3,8,4,9,5,10,6,7,16,1,16,2,3,16,4,5,6,7,16,8,9,10]
def F_16 : Nat := fullMask 24
set_option maxHeartbeats 0 in
lemma gp_16 : goodPairs g_16 p_16 q_16 := goodPairs_of (by decide +kernel)
def W_16 : BT Decor := buildWiresBT 6 (mkBase p_16 q_16 r_16) [(0,3,4),(1,2,5),(1,0,6),(1,1,6),(1,3,4),(3,6,9),(3,5,9),(2,11,1),(3,2,9),(1,1,3),(1,14,4),(3,1,15),(1,0,3),(0,17,4),(1,2,18),(2,0,5),(1,1,5),(2,13,1),(2,13,0),(1,0,5),(0,0,9),(0,11,0),(2,0,6),(3,3,4),(1,28,0),(2,29,1),(2,3,4),(0,13,0),(3,0,3),(3,33,4),(3,1,4),(3,1,3),(1,36,4),(1,35,3),(1,33,1),(3,0,4),(1,40,3),(3,1,41),(1,1,18),(1,17,4),(3,2,44),(3,1,44),(3,2,38),(3,0,44),(0,14,4),(1,1,4),(1,31,0),(3,14,4),(2,17,4),(3,40,3),(1,0,4),(3,1,55),(0,3,55),(3,3,55)]
lemma W_16_ok : btAll (fun x => faithful p_16 q_16 x ∧ x.1 < 2^256) W_16 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_16 : List (List (Nat × Nat)) := [[],[(0,1)]]
def A_16 : BT (List (Nat × Nat)) := btOfList 1 al_16
set_option maxHeartbeats 0 in
lemma A_16_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_16 = g_16) A_16 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_16_0 : Slice r_16 g_16 (subcubeFast 4 0) 6 := by
  have hc : Lower (varsOf 27) (d 0xffee8800ffee8800) 6 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_1 : Slice r_16 g_16 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) (d 0xfffaf000fffaf000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_2 : Slice r_16 g_16 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) (d 0xfffcf000fffcf000) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_3 : Slice r_16 g_16 (subcubeFast 3 0) 4 := by
  have hc : Lower (varsOf 28) (d 0xfff0f000fff0f000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 3) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_4 : Slice r_16 g_16 (identDom 1 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xfefec8c8fefec8c8) 5 := carry_of (swaps := [(1,2),(3,4)]) (by decide +kernel) low_5
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_5 : Slice r_16 g_16 (identDom 0 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xfefea8a8fefea8a8) 5 := carry_of (swaps := [(0,2),(1,2),(3,4)]) (by decide +kernel) low_5
  exact slice_ident (u := 0) (v := 3) (by decide +kernel) hc
def S_16 : BT (Option (Nat × Nat)) := btOfList 3 [some (subcubeFast 4 0,6),some (subcubeFast 2 0,5),some (subcubeFast 1 0,5),some (subcubeFast 3 0,4),some (identDom 1 3,5),some (identDom 0 3,5)]
lemma S_16_ok : btAll (fun o => ∀ p, o = some p → Slice r_16 g_16 p.1 p.2) S_16 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_16_0) (forall_cons (fun _ h => by cases h; exact sl_16_1) (forall_cons (fun _ h => by cases h; exact sl_16_2) (forall_cons (fun _ h => by cases h; exact sl_16_3) (forall_cons (fun _ h => by cases h; exact sl_16_4) (forall_cons (fun _ h => by cases h; exact sl_16_5) (fun _ h => (List.not_mem_nil h).elim)))))))
def ps_16 : BT (Option PoolSpec) := btOfList 5 [q 0 [16396,16397,36887],q 0 [16396,16397],q 1 [],q 0 [16398,16399],q 2 [],q 0 [],q 3 [],q 0 [16397,36864],q 5 [],q 0 [16396,20485],q 0 [16397,36871],q 2 [16391],q 0 [12291,4229],q 0 [16396,20482],q 2 [12293],q 4 [],q 0 [16385,225287],q 2 [225287],q 0 [16399],q 0 [16398],q 0 [16397],q 0 [16396],q 0 [16391],q 0 [16385],q 0 [12295],q 1 [12289],q 0 [12289]]
def B_16_1 : BT (List (List Nat)) := BT.empty
lemma B_16_1_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_16 1 xs.toFinset) B_16_1 := .empty
def U_16_2 : List Nat := []
def P_16_2 : BT (Option BoundPool) := buildPoolsSubBT 5 W_16 r_16 S_16 ps_16 U_16_2
def N_16_2 : List NodeSpec := [([7,8,9],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_16_2 : checkNodesBT W_16 g_16 F_16 P_16_2 A_16 B_16_1 2 N_16_2 = true := by decide +kernel
def B_16_2 : BT (List (List Nat)) := buildBucketsBT W_16 N_16_2
set_option maxRecDepth 500000 in
lemma B_16_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_16 2 xs.toFinset) B_16_2 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok (buildPoolsSubBT_sound S_16_ok) A_16_ok B_16_1_ok C_16_2
def U_16_3 : List Nat := []
def P_16_3 : BT (Option BoundPool) := buildPoolsSubBT 5 W_16 r_16 S_16 ps_16 U_16_3
def N_16_3 : List NodeSpec := [([10,11,0,1],[],[]),([12,11,0,2],[],[]),([11,13,0,1],[],[]),([11,16,0,2],[],[]),([11,0,1,2],[],[]),([0,1,19,9],[],[]),([20,11,1,2],[],[]),([0,21,6,9],[],[]),([22,23,3,4],[],[]),([2,24,21,9],[],[]),([11,0,2,21],[],[]),([11,0,1,6],[],[]),([20,1,6,9],[],[]),([11,25,1,2],[],[]),([3,7,8,4],[],[0]),([10,0,1,9],[],[]),([25,1,6,9],[],[]),([16,0,6,9],[],[]),([26,11,1,2],[],[]),([0,6,8,9],[],[0]),([27,1,6,9],[],[]),([0,1,6,9],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_16_3 : checkNodesBT W_16 g_16 F_16 P_16_3 A_16 B_16_2 3 N_16_3 = true := by decide +kernel
def B_16_3 : BT (List (List Nat)) := buildBucketsBT W_16 N_16_3
set_option maxRecDepth 500000 in
lemma B_16_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_16 3 xs.toFinset) B_16_3 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok (buildPoolsSubBT_sound S_16_ok) A_16_ok B_16_2_ok C_16_3
def U_16_4 : List Nat := [0,1]
def P_16_4 : BT (Option BoundPool) := buildPoolsSubBT 5 W_16 r_16 S_16 ps_16 U_16_4
def N_16_4 : List NodeSpec := [([13,0,1,3,4],[],[]),([0,1,3,6,4],[],[0]),([22,13,0,3,4],[],[0]),([13,16,0,3,4],[],[]),([13,25,1,3,4],[],[]),([30,0,2,3,4],[],[]),([16,25,2,3,4],[],[]),([11,0,1,2,4],[],[]),([11,0,1,2,3],[],[]),([11,0,1,2],[0],[0,1]),([13,0,1,5,9],[],[0]),([16,0,2,5,9],[],[0]),([31,28,0,1,2],[],[0]),([32,13,1,3,4],[],[]),([25,1,2,5,9],[],[0]),([0,1,2,5,9],[],[0]),([0,1,5,6,9],[],[0,1]),([0,1,6,9],[1],[0,1]),([31,0,34,1,2],[],[]),([20,1,3,6,4],[],[0]),([35,0,2,3,37],[],[]),([28,11,0,1,2],[],[]),([0,1,3,6,9],[],[]),([36,0,2,38,4],[],[]),([0,39,2,4,9],[],[]),([28,0,1,3,6],[],[0]),([31,11,0,1,2],[],[]),([42,0,2,3,4],[],[]),([16,0,2,3,4],[],[]),([0,1,3,19,4],[],[0]),([11,0,1,2,5],[0],[0,1]),([0,2,3,43,4],[],[]),([45,0,1,3,4],[],[]),([0,1,2,18,9],[],[0]),([46,0,2,3,4],[],[]),([47,0,1,3,4],[],[]),([11,0,1,2,9],[0],[0,1]),([31,0,2,21,4],[],[]),([0,2,21,4,9],[],[]),([0,3,21,6,4],[],[0]),([16,48,2,3,4],[],[]),([20,2,3,21,4],[],[]),([31,0,39,2,4],[],[]),([0,2,5,21,9],[],[0]),([20,1,2,5,9],[],[0]),([2,3,24,21,4],[],[0]),([0,3,6,8,4],[],[0]),([0,2,3,49,50],[],[]),([31,0,1,6,4],[],[0]),([27,1,3,6,4],[],[0]),([0,1,6,4,9],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_16_4 : checkNodesBT W_16 g_16 F_16 P_16_4 A_16 B_16_3 4 N_16_4 = true := by decide +kernel
def B_16_4 : BT (List (List Nat)) := buildBucketsBT W_16 N_16_4
set_option maxRecDepth 500000 in
lemma B_16_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_16 4 xs.toFinset) B_16_4 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok (buildPoolsSubBT_sound S_16_ok) A_16_ok B_16_3_ok C_16_4
def U_16_5 : List Nat := (r 1 17)
def P_16_5 : BT (Option BoundPool) := buildPoolsSubBT 5 W_16 r_16 S_16 ps_16 U_16_5
def N_16_5 : List NodeSpec := [u5 [29] [2],([31,28,0,1,2,4],[],[0]),([31,28,0,1,2],[3],[0]),a5 [9] [2,4,5] [0,1],e5 [51] [],e5 [16] [],([13,0,1,3,4],[],[0,1]),([25,1,2,3,4,9],[6,7],[0,1]),([31,28,0,1,2,3],[],[0]),([0,1,2,5,3,9],[],[0]),u5 [28] [],([31,36,0,1,2,4],[2],[1]),a5 [18] [2,5,8] [0,1],([0,2,5,3,21,4],[2,9],[0]),([0,1,3,6,4],[],[0,1]),u5 [37] [],([36,0,1,2,4,9],[2],[1]),e5 [52] [],([28,0,1,2,4,9],[5],[0]),e5 [53] [],([16,0,2,3,4],[10],[]),e5 [54] [],([36,35,0,2,3,4],[11],[0]),a5 [44] [2,5] [0,1],a5 [38] [4,5] [0,1],([31,0,1,2,3,9],[5],[0]),([0,39,2,3,4],[12],[0]),([20,1,2,5,3,4],[6,8,13],[0]),([31,0,1,2,17,4],[4],[]),([16,0,2,3,4,9],[2,10],[0]),([35,0,2,3,4,50],[2,11],[]),([0,2,3,14,4,50],[14,15],[0]),e5 [24] [],u5 [34] [4],([31,0,1,2,5,4],[5],[0,1]),([0,1,2,17,4,9],[4],[0]),([56,0,2,3,4],[16],[]),([0,1,2,5,4,9],[],[0,1]),([0,2,3,21,4],[9],[0]),([56,0,2,3,4,55],[2,17],[]),u5 [5] [2,4,5,8,15],([0,1,2,5,9],[1],[0,1]),([0,1,5,3,6,4],[5],[0,1]),e5 [57] [8],e5 [58] [],u5 [31] [],([13,0,1,3,4,9],[5],[0,1]),([28,0,1,2,5,3],[5],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_16_5 : checkNodesBT W_16 g_16 F_16 P_16_5 A_16 B_16_4 5 N_16_5 = true := by decide +kernel
def B_16_5 : BT (List (List Nat)) := buildBucketsBT W_16 N_16_5
set_option maxRecDepth 500000 in
lemma B_16_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_16 5 xs.toFinset) B_16_5 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok (buildPoolsSubBT_sound S_16_ok) A_16_ok B_16_4_ok C_16_5
def U_16_6 : List Nat := ([2,4,5,6,8,15]++r 18 9)
def P_16_6 : BT (Option BoundPool) := buildPoolsSubBT 5 W_16 r_16 S_16 ps_16 U_16_6
def N_16_6 : List NodeSpec := [a5 [28] [2,4,5,18] [0,1],a5 [31] [2,4,5,8,15,19] [0,1],a5 [9] [2,4,20] [0,1],a5 [5] [2,4,8,15,21] [0,1],a5 [35] [4,5,6,15,22] [0,1],a5 [55] [6,8,23] [0,1],a5 [36] [4,6,15,24] [0,1],a5 [17] [4,6,8,25,26] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_16_6 : checkNodesBT W_16 g_16 F_16 P_16_6 A_16 B_16_5 6 N_16_6 = true := by decide +kernel
def B_16_6 : BT (List (List Nat)) := buildBucketsBT W_16 N_16_6
set_option maxRecDepth 500000 in
lemma B_16_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_16 6 xs.toFinset) B_16_6 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok (buildPoolsSubBT_sound S_16_ok) A_16_ok B_16_5_ok C_16_6
def U_16_7 : List Nat := [2,5,6]
def P_16_7 : BT (Option BoundPool) := buildPoolsSubBT 5 W_16 r_16 S_16 ps_16 U_16_7
def N_16_7 : List NodeSpec := [a5 [] [2,5,6] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_16_7 : checkNodesBT W_16 g_16 F_16 P_16_7 A_16 B_16_6 7 N_16_7 = true := by decide +kernel
def B_16_7 : BT (List (List Nat)) := buildBucketsBT W_16 N_16_7
set_option maxRecDepth 500000 in
lemma B_16_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_16 7 xs.toFinset) B_16_7 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok (buildPoolsSubBT_sound S_16_ok) A_16_ok B_16_6_ok C_16_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_16_ok : forestRootCheck r_16 g_16 [(VAR 0,10,11),(VAR 1,9,11),(VAR 2,8,12),(VAR 3,3,11),(VAR 4,1,17)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_16_in : bucketContainsBT B_16_7 r_16 = true := by decide +kernel
lemma low_16 : Lower r_16 g_16 8 := lower_of_forestBT root_16_ok B_16_7_ok root_16_in
def g_17 := (d 0xffe8ffe8ffe8ffe8)
def r_17 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_17 : Lower r_17 g_17 5 := by
  exact lift_of_f (z := 8) (o := 0) (other := r_0) (G := g_0) (essPairs := [(VAR 3,0,8)]) (by decide +kernel) low_0
def g_18 := (d 0xfff8e800fff8e800)
def r_18 : List Nat := varsOf 31
def p_18 : List Nat := [11,11,11,13,13,13,14,14,14,15,19,19,19,20,20,21,21,22,22,23,24,24,25,25,26,26,28]
def q_18 : List Nat := [10,9,3,12,9,5,12,10,6,7,18,17,3,16,4,17,5,18,6,7,16,8,17,9,18,10,12]
def F_18 : Nat := fullMask 27
set_option maxHeartbeats 0 in
lemma gp_18 : goodPairs g_18 p_18 q_18 := goodPairs_of (by decide +kernel)
def W_18 : BT Decor := buildWiresBT 3 (mkBase p_18 q_18 r_18) [(1,2,4)]
lemma W_18_ok : btAll (fun x => faithful p_18 q_18 x ∧ x.1 < 2^256) W_18 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_18 : List (List (Nat × Nat)) := [[]]
def A_18 : BT (List (Nat × Nat)) := btOfList 1 al_18
set_option maxHeartbeats 0 in
lemma A_18_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_18 = g_18) A_18 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_18_0 : Slice r_18 g_18 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) (d 0xfffcfc00fffcfc00) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_1 : Slice r_18 g_18 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) (d 0xfff0a000fff0a000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_2 : Slice r_18 g_18 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) (d 0xfffafa00fffafa00) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_3 : Slice r_18 g_18 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) (d 0xff888800ff888800) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_11
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_4 : Slice r_18 g_18 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) (d 0xfff0c000fff0c000) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_5 : Slice r_18 g_18 (subcubeFast 0 8) 5 := by
  have hc : Lower (varsOf 23) (d 0xffffe8e8ffffe8e8) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_17
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_6 : Slice r_18 g_18 (subcubeFast 16 0) 5 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_4
set_option maxHeartbeats 0 in
lemma sl_18_7 : Slice r_18 g_18 (subcubeFast 16 8) 4 := by
  exact slice_fast_direct_f (z := 16) (o := 8) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_18_8 : Slice r_18 g_18 (identDom 2 3) 6 := by
  have hc : Lower (varsOf 23) (d 0xf8f8e0e0f8f8e0e0) 6 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_6
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
def S_18 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 0 1,5),some (subcubeFast 2 0,5),some (subcubeFast 0 2,5),some (subcubeFast 4 0,5),some (subcubeFast 1 0,5),some (subcubeFast 0 8,5),some (subcubeFast 16 0,5),some (subcubeFast 16 8,4),some (identDom 2 3,6)]
lemma S_18_ok : btAll (fun o => ∀ p, o = some p → Slice r_18 g_18 p.1 p.2) S_18 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_18_0) (forall_cons (fun _ h => by cases h; exact sl_18_1) (forall_cons (fun _ h => by cases h; exact sl_18_2) (forall_cons (fun _ h => by cases h; exact sl_18_3) (forall_cons (fun _ h => by cases h; exact sl_18_4) (forall_cons (fun _ h => by cases h; exact sl_18_5) (forall_cons (fun _ h => by cases h; exact sl_18_6) (forall_cons (fun _ h => by cases h; exact sl_18_7) (forall_cons (fun _ h => by cases h; exact sl_18_8) (fun _ h => (List.not_mem_nil h).elim))))))))))
def ps_18 : BT (Option PoolSpec) := btOfList 4 [q 4 [],q 0 [],q 1 [],q 2 [],q 5 [16393],q 3 [],q 6 [],q 7 [],q 5 [],q 8 []]
def B_18_5 : BT (List (List Nat)) := BT.empty
lemma B_18_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_18 5 xs.toFinset) B_18_5 := .empty
def U_18_6 : List Nat := (r 0 8)
def P_18_6 : BT (Option BoundPool) := buildPoolsSubBT 4 W_18 r_18 S_18 ps_18 U_18_6
def N_18_6 : List NodeSpec := [e5 [5] (r 0 8)]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_18_6 : checkNodesBT W_18 g_18 F_18 P_18_6 A_18 B_18_5 6 N_18_6 = true := by decide +kernel
def B_18_6 : BT (List (List Nat)) := buildBucketsBT W_18 N_18_6
set_option maxRecDepth 500000 in
lemma B_18_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_18 6 xs.toFinset) B_18_6 :=
  buildBucketsBT_sound (by decide) gp_18 W_18_ok (buildPoolsSubBT_sound S_18_ok) A_18_ok B_18_5_ok C_18_6
def U_18_7 : List Nat := (r 0 4++r 5 5)
def P_18_7 : BT (Option BoundPool) := buildPoolsSubBT 4 W_18 r_18 S_18 ps_18 U_18_7
def N_18_7 : List NodeSpec := [u5 [] (r 0 4++r 5 5)]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_18_7 : checkNodesBT W_18 g_18 F_18 P_18_7 A_18 B_18_6 7 N_18_7 = true := by decide +kernel
def B_18_7 : BT (List (List Nat)) := buildBucketsBT W_18 N_18_7
set_option maxRecDepth 500000 in
lemma B_18_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_18 7 xs.toFinset) B_18_7 :=
  buildBucketsBT_sound (by decide) gp_18 W_18_ok (buildPoolsSubBT_sound S_18_ok) A_18_ok B_18_6_ok C_18_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_18_ok : forestRootCheck r_18 g_18 [(VAR 0,10,11),(VAR 1,9,11),(VAR 2,9,13),(VAR 3,3,11),(VAR 4,3,19)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_18_in : bucketContainsBT B_18_7 r_18 = true := by decide +kernel
lemma low_18 : Lower r_18 g_18 8 := lower_of_forestBT root_18_ok B_18_7_ok root_18_in
def g_19 := (d 0xfffafcc0fffafcc0)
def r_19 : List Nat := varsOf 31
def p_19 : List Nat := [6,6,7,7,10,10,11,11,12,12,13,13,17,17,19,19,20,20,21,22,24,24,25,26]
def q_19 : List Nat := [4,2,5,3,8,2,9,3,8,4,9,5,16,1,18,3,16,4,5,18,16,8,9,18]
def F_19 : Nat := fullMask 24
set_option maxHeartbeats 0 in
lemma gp_19 : goodPairs g_19 p_19 q_19 := goodPairs_of (by decide +kernel)
def W_19 : BT Decor := buildWiresBT 3 (mkBase p_19 q_19 r_19) [(1,2,3),(3,1,5)]
lemma W_19_ok : btAll (fun x => faithful p_19 q_19 x ∧ x.1 < 2^256) W_19 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_19 : List (List (Nat × Nat)) := [[]]
def A_19 : BT (List (Nat × Nat)) := btOfList 1 al_19
set_option maxHeartbeats 0 in
lemma A_19_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_19 = g_19) A_19 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_19_0 : Slice r_19 g_19 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) (d 0xfffffcc0fffffcc0) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_17
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_19_1 : Slice r_19 g_19 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) (d 0xfffaf000fffaf000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_19_2 : Slice r_19 g_19 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) (d 0xfff0fcc0fff0fcc0) 5 := carry_of (swaps := [(0,4),(1,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_19_3 : Slice r_19 g_19 (subcubeFast 17 0) 4 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 17) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_19_4 : Slice r_19 g_19 (subcubeFast 8 0) 4 := by
  have hc : Lower (varsOf 23) (d 0xfafac0c0fafac0c0) 4 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_19_5 : Slice r_19 g_19 (subcubeFast 4 0) 4 := by
  have hc : Lower (varsOf 27) (d 0xffaacc00ffaacc00) 4 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
def S_19 : BT (Option (Nat × Nat)) := btOfList 3 [some (subcubeFast 0 1,5),some (subcubeFast 2 0,5),some (subcubeFast 1 0,5),some (subcubeFast 17 0,4),some (subcubeFast 8 0,4),some (subcubeFast 4 0,4)]
lemma S_19_ok : btAll (fun o => ∀ p, o = some p → Slice r_19 g_19 p.1 p.2) S_19 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_19_0) (forall_cons (fun _ h => by cases h; exact sl_19_1) (forall_cons (fun _ h => by cases h; exact sl_19_2) (forall_cons (fun _ h => by cases h; exact sl_19_3) (forall_cons (fun _ h => by cases h; exact sl_19_4) (forall_cons (fun _ h => by cases h; exact sl_19_5) (fun _ h => (List.not_mem_nil h).elim)))))))
def ps_19 : BT (Option PoolSpec) := btOfList 3 [q 0 [],q 2 [],q 1 [],q 4 [],q 3 [],q 5 []]
def B_19_3 : BT (List (List Nat)) := BT.empty
lemma B_19_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_19 3 xs.toFinset) B_19_3 := .empty
def U_19_4 : List Nat := []
def P_19_4 : BT (Option BoundPool) := buildPoolsSubBT 3 W_19 r_19 S_19 ps_19 U_19_4
def N_19_4 : List NodeSpec := [([6,0,2,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_19_4 : checkNodesBT W_19 g_19 F_19 P_19_4 A_19 B_19_3 4 N_19_4 = true := by decide +kernel
def B_19_4 : BT (List (List Nat)) := buildBucketsBT W_19 N_19_4
set_option maxRecDepth 500000 in
lemma B_19_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_19 4 xs.toFinset) B_19_4 :=
  buildBucketsBT_sound (by decide) gp_19 W_19_ok (buildPoolsSubBT_sound S_19_ok) A_19_ok B_19_3_ok C_19_4
def U_19_5 : List Nat := (r 0 4)
def P_19_5 : BT (Option BoundPool) := buildPoolsSubBT 3 W_19 r_19 S_19 ps_19 U_19_5
def N_19_5 : List NodeSpec := [u5 [5] (r 0 4)]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_19_5 : checkNodesBT W_19 g_19 F_19 P_19_5 A_19 B_19_4 5 N_19_5 = true := by decide +kernel
def B_19_5 : BT (List (List Nat)) := buildBucketsBT W_19 N_19_5
set_option maxRecDepth 500000 in
lemma B_19_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_19 5 xs.toFinset) B_19_5 :=
  buildBucketsBT_sound (by decide) gp_19 W_19_ok (buildPoolsSubBT_sound S_19_ok) A_19_ok B_19_4_ok C_19_5
def U_19_6 : List Nat := (r 0 6)
def P_19_6 : BT (Option BoundPool) := buildPoolsSubBT 3 W_19 r_19 S_19 ps_19 U_19_6
def N_19_6 : List NodeSpec := [u5 [] (r 0 6)]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_19_6 : checkNodesBT W_19 g_19 F_19 P_19_6 A_19 B_19_5 6 N_19_6 = true := by decide +kernel
def B_19_6 : BT (List (List Nat)) := buildBucketsBT W_19 N_19_6
set_option maxRecDepth 500000 in
lemma B_19_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_19 6 xs.toFinset) B_19_6 :=
  buildBucketsBT_sound (by decide) gp_19 W_19_ok (buildPoolsSubBT_sound S_19_ok) A_19_ok B_19_5_ok C_19_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_19_ok : forestRootCheck r_19 g_19 [(VAR 0,16,17),(VAR 1,4,6),(VAR 2,2,6),(VAR 3,2,10),(VAR 4,1,17)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_19_in : bucketContainsBT B_19_6 r_19 = true := by decide +kernel
lemma low_19 : Lower r_19 g_19 7 := lower_of_forestBT root_19_ok B_19_6_ok root_19_in
def g_20 := (d 0xfefef800fefef800)
def r_20 : List Nat := varsOf 31
def p_20 : List Nat := [11,11,11,12,12,13,13,14,14,15,17,17,18,18,19,20,20,21,22,23,25,25,26,26,28]
def q_20 : List Nat := [10,9,3,8,4,9,5,10,6,7,16,1,16,2,3,16,4,5,6,7,24,9,24,10,24]
def F_20 : Nat := fullMask 25
set_option maxHeartbeats 0 in
lemma gp_20 : goodPairs g_20 p_20 q_20 := goodPairs_of (by decide +kernel)
def W_20 : BT Decor := buildWiresBT 4 (mkBase p_20 q_20 r_20) [(1,0,4),(3,1,5),(2,3,4),(3,1,4),(1,0,1)]
lemma W_20_ok : btAll (fun x => faithful p_20 q_20 x ∧ x.1 < 2^256) W_20 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_20 : List (List (Nat × Nat)) := [[],[(0,1)]]
def A_20 : BT (List (Nat × Nat)) := btOfList 1 al_20
set_option maxHeartbeats 0 in
lemma A_20_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_20 = g_20) A_20 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_20_0 : Slice r_20 g_20 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) (d 0xeeee8800eeee8800) 5 := carry_of (swaps := [(0,1),(1,2),(2,4),(3,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_20_1 : Slice r_20 g_20 (subcubeFast 0 8) 5 := by
  have hc : Lower (varsOf 23) (d 0xfefef8f8fefef8f8) 5 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_17
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_20_2 : Slice r_20 g_20 (identDom 1 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xfefec8c8fefec8c8) 5 := carry_of (swaps := [(1,2),(3,4)]) (by decide +kernel) low_5
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_20_3 : Slice r_20 g_20 (subcubeFast 2 0) 4 := by
  have hc : Lower (varsOf 29) (d 0xfafaf000fafaf000) 4 := carry_of (swaps := [(1,4),(3,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_20_4 : Slice r_20 g_20 (subcubeFast 1 0) 4 := by
  have hc : Lower (varsOf 30) (d 0xfcfcf000fcfcf000) 4 := carry_of (swaps := [(0,4),(1,4),(3,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
def S_20 : BT (Option (Nat × Nat)) := btOfList 3 [some (subcubeFast 4 0,5),some (subcubeFast 0 8,5),some (identDom 1 3,5),some (subcubeFast 2 0,4),some (subcubeFast 1 0,4)]
lemma S_20_ok : btAll (fun o => ∀ p, o = some p → Slice r_20 g_20 p.1 p.2) S_20 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_20_0) (forall_cons (fun _ h => by cases h; exact sl_20_1) (forall_cons (fun _ h => by cases h; exact sl_20_2) (forall_cons (fun _ h => by cases h; exact sl_20_3) (forall_cons (fun _ h => by cases h; exact sl_20_4) (fun _ h => (List.not_mem_nil h).elim))))))
def ps_20 : BT (Option PoolSpec) := btOfList 3 [q 1 [],q 0 [16398],q 2 [],q 3 [],q 4 [],q 0 []]
def B_20_3 : BT (List (List Nat)) := BT.empty
lemma B_20_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_20 3 xs.toFinset) B_20_3 := .empty
def U_20_4 : List Nat := []
def P_20_4 : BT (Option BoundPool) := buildPoolsSubBT 3 W_20 r_20 S_20 ps_20 U_20_4
def N_20_4 : List NodeSpec := [([6,0,2,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_20_4 : checkNodesBT W_20 g_20 F_20 P_20_4 A_20 B_20_3 4 N_20_4 = true := by decide +kernel
def B_20_4 : BT (List (List Nat)) := buildBucketsBT W_20 N_20_4
set_option maxRecDepth 500000 in
lemma B_20_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_20 4 xs.toFinset) B_20_4 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok (buildPoolsSubBT_sound S_20_ok) A_20_ok B_20_3_ok C_20_4
def U_20_5 : List Nat := (r 0 5)
def P_20_5 : BT (Option BoundPool) := buildPoolsSubBT 3 W_20 r_20 S_20 ps_20 U_20_5
def N_20_5 : List NodeSpec := [([7,0,1,2,4],[0,1],[]),e5 [8] [0,2,3],u5 [5] [3,4],e5 [9] [3]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_20_5 : checkNodesBT W_20 g_20 F_20 P_20_5 A_20 B_20_4 5 N_20_5 = true := by decide +kernel
def B_20_5 : BT (List (List Nat)) := buildBucketsBT W_20 N_20_5
set_option maxRecDepth 500000 in
lemma B_20_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_20 5 xs.toFinset) B_20_5 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok (buildPoolsSubBT_sound S_20_ok) A_20_ok B_20_4_ok C_20_5
def U_20_6 : List Nat := [0,3,4,5]
def P_20_6 : BT (Option BoundPool) := buildPoolsSubBT 3 W_20 r_20 S_20 ps_20 U_20_6
def N_20_6 : List NodeSpec := [a5 [] [0,3,4,5] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_20_6 : checkNodesBT W_20 g_20 F_20 P_20_6 A_20 B_20_5 6 N_20_6 = true := by decide +kernel
def B_20_6 : BT (List (List Nat)) := buildBucketsBT W_20 N_20_6
set_option maxRecDepth 500000 in
lemma B_20_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_20 6 xs.toFinset) B_20_6 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok (buildPoolsSubBT_sound S_20_ok) A_20_ok B_20_5_ok C_20_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_20_ok : forestRootCheck r_20 g_20 [(VAR 0,10,11),(VAR 1,9,11),(VAR 2,8,12),(VAR 3,3,11),(VAR 4,1,17)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_20_in : bucketContainsBT B_20_6 r_20 = true := by decide +kernel
lemma low_20 : Lower r_20 g_20 7 := lower_of_forestBT root_20_ok B_20_6_ok root_20_in
def g_21 := (d 0xfffce800fffce800)
def r_21 : List Nat := varsOf 31
def p_21 : List Nat := [11,11,11,13,13,13,14,14,14,15,18,18,19,19,20,20,21,21,22,23,24,24,25,25,26,28]
def q_21 : List Nat := [10,9,3,12,9,5,12,10,6,7,16,2,17,3,16,4,17,5,6,7,16,8,17,9,10,12]
def F_21 : Nat := fullMask 26
set_option maxHeartbeats 0 in
lemma gp_21 : goodPairs g_21 p_21 q_21 := goodPairs_of (by decide +kernel)
def W_21 : BT Decor := buildWiresBT 4 (mkBase p_21 q_21 r_21) [(1,1,4),(3,2,5),(1,1,2),(2,7,4),(3,2,3),(1,9,1),(1,7,4),(0,7,3),(1,2,4),(1,0,4),(3,0,3)]
lemma W_21_ok : btAll (fun x => faithful p_21 q_21 x ∧ x.1 < 2^256) W_21 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_21 : List (List (Nat × Nat)) := [[],[(1,2)]]
def A_21 : BT (List (Nat × Nat)) := btOfList 1 al_21
set_option maxHeartbeats 0 in
lemma A_21_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_21 = g_21) A_21 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_21_0 : Slice r_21 g_21 (subcubeFast 1 0) 6 := by
  have hc : Lower (varsOf 30) (d 0xfffcc000fffcc000) 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_1 : Slice r_21 g_21 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) (d 0xfffcfc00fffcfc00) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_2 : Slice r_21 g_21 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) (d 0xfff0a000fff0a000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_3 : Slice r_21 g_21 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) (d 0xffcc8800ffcc8800) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_4 : Slice r_21 g_21 (subcubeFast 0 8) 5 := by
  have hc : Lower (varsOf 23) (d 0xffffe8e8ffffe8e8) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_17
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_5 : Slice r_21 g_21 (subcubeFast 16 0) 5 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_4
set_option maxHeartbeats 0 in
lemma sl_21_6 : Slice r_21 g_21 (subcubeFast 16 8) 4 := by
  exact slice_fast_direct_f (z := 16) (o := 8) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_21_7 : Slice r_21 g_21 (subcubeFast 4 1) 4 := by
  have hc : Lower (varsOf 26) (d 0xffcccc00ffcccc00) 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_8 : Slice r_21 g_21 (identDom 2 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xfcfce0e0fcfce0e0) 5 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_3
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
def S_21 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 1 0,6),some (subcubeFast 0 1,5),some (subcubeFast 2 0,5),some (subcubeFast 4 0,5),some (subcubeFast 0 8,5),some (subcubeFast 16 0,5),some (subcubeFast 16 8,4),some (subcubeFast 4 1,4),some (identDom 2 3,5)]
lemma S_21_ok : btAll (fun o => ∀ p, o = some p → Slice r_21 g_21 p.1 p.2) S_21 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_21_0) (forall_cons (fun _ h => by cases h; exact sl_21_1) (forall_cons (fun _ h => by cases h; exact sl_21_2) (forall_cons (fun _ h => by cases h; exact sl_21_3) (forall_cons (fun _ h => by cases h; exact sl_21_4) (forall_cons (fun _ h => by cases h; exact sl_21_5) (forall_cons (fun _ h => by cases h; exact sl_21_6) (forall_cons (fun _ h => by cases h; exact sl_21_7) (forall_cons (fun _ h => by cases h; exact sl_21_8) (fun _ h => (List.not_mem_nil h).elim))))))))))
def ps_21 : BT (Option PoolSpec) := btOfList 4 [q 0 [],q 1 [],q 8 [],q 4 [],q 2 [],q 5 [],q 0 [12299],q 3 [],q 6 [],q 0 [16389],q 0 [8197],q 7 [],q 2 [16385],q 4 [16385],q 2 [12291]]
def B_21_4 : BT (List (List Nat)) := BT.empty
lemma B_21_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_21 4 xs.toFinset) B_21_4 := .empty
def U_21_5 : List Nat := (r 0 6)
def P_21_5 : BT (Option BoundPool) := buildPoolsSubBT 4 W_21 r_21 S_21 ps_21 U_21_5
def N_21_5 : List NodeSpec := [e5 [6] [],e5 [8] [0,1],e5 [10] [],e5 [11] (r 0 4),e5 [12] [0,1],([0,1,7,3,4,13],[4,5],[]),([9,0,1,7,3,4],[3,4],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_21_5 : checkNodesBT W_21 g_21 F_21 P_21_5 A_21 B_21_4 5 N_21_5 = true := by decide +kernel
def B_21_5 : BT (List (List Nat)) := buildBucketsBT W_21 N_21_5
set_option maxRecDepth 500000 in
lemma B_21_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_21 5 xs.toFinset) B_21_5 :=
  buildBucketsBT_sound (by decide) gp_21 W_21_ok (buildPoolsSubBT_sound S_21_ok) A_21_ok B_21_4_ok C_21_5
def U_21_6 : List Nat := (r 0 15)
def P_21_6 : BT (Option BoundPool) := buildPoolsSubBT 4 W_21 r_21 S_21 ps_21 U_21_6
def N_21_6 : List NodeSpec := [u5 [9] [0,2,4,6,7,8],a5 [5] [4,7,8,9] [0,1],a5 [7] (r 1 5++[10,11]) [0,1],([1,2,3,4,14],[8,11,12,13],[]),([15,1,2,3,4],[0,1,8,11,14],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_21_6 : checkNodesBT W_21 g_21 F_21 P_21_6 A_21 B_21_5 6 N_21_6 = true := by decide +kernel
def B_21_6 : BT (List (List Nat)) := buildBucketsBT W_21 N_21_6
set_option maxRecDepth 500000 in
lemma B_21_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_21 6 xs.toFinset) B_21_6 :=
  buildBucketsBT_sound (by decide) gp_21 W_21_ok (buildPoolsSubBT_sound S_21_ok) A_21_ok B_21_5_ok C_21_6
def U_21_7 : List Nat := [0,3,4,5,7,8]
def P_21_7 : BT (Option BoundPool) := buildPoolsSubBT 4 W_21 r_21 S_21 ps_21 U_21_7
def N_21_7 : List NodeSpec := [a5 [] [0,3,4,5,7,8] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_21_7 : checkNodesBT W_21 g_21 F_21 P_21_7 A_21 B_21_6 7 N_21_7 = true := by decide +kernel
def B_21_7 : BT (List (List Nat)) := buildBucketsBT W_21 N_21_7
set_option maxRecDepth 500000 in
lemma B_21_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_21 7 xs.toFinset) B_21_7 :=
  buildBucketsBT_sound (by decide) gp_21 W_21_ok (buildPoolsSubBT_sound S_21_ok) A_21_ok B_21_6_ok C_21_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_21_ok : forestRootCheck r_21 g_21 [(VAR 0,10,11),(VAR 1,9,11),(VAR 2,9,13),(VAR 3,3,11),(VAR 4,2,18)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_21_in : bucketContainsBT B_21_7 r_21 = true := by decide +kernel
lemma low_21 : Lower r_21 g_21 8 := lower_of_forestBT root_21_ok B_21_7_ok root_21_in
def g_22 := (d 0xffc8e000ffc8e000)
def r_22 : List Nat := varsOf 31
def p_22 : List Nat := [13,13,13,14,14,14,15,15,19,19,19,22,22,22,23,23,24,24,25,25,26,26,27,28,28,29]
def q_22 : List Nat := [12,9,5,12,10,6,11,7,18,17,3,20,18,6,21,7,16,8,17,9,18,10,11,20,12,21]
def F_22 : Nat := fullMask 26
set_option maxHeartbeats 0 in
lemma gp_22 : goodPairs g_22 p_22 q_22 := goodPairs_of (by decide +kernel)
def W_22 : BT Decor := buildWiresBT 7 (mkBase p_22 q_22 r_22) [(0,3,4),(1,3,4),(3,5,6),(2,7,2),(0,7,1),(2,7,0),(0,2,4),(1,0,11),(0,2,3),(1,13,4),(0,0,6),(0,1,6),(1,1,5),(1,2,5),(3,0,6),(3,2,6),(0,7,0),(0,1,3),(0,22,4),(3,23,1),(1,0,5),(2,0,5),(0,2,6),(2,3,4),(0,1,4),(1,29,3),(0,11,3),(3,31,1),(2,2,4),(0,1,2),(0,34,4),(3,35,3),(3,34,4),(1,0,34),(2,1,3),(3,39,4),(2,2,40),(2,2,5),(1,0,22),(1,0,3),(0,44,4),(2,2,45),(3,5,4),(3,1,6),(3,47,1),(3,33,3),(3,13,4),(3,34,3),(0,34,3),(3,0,4),(3,54,3),(2,44,4),(1,54,3),(3,11,1),(3,11,3),(0,33,3),(3,13,1),(1,0,4),(0,62,3),(3,0,3)]
lemma W_22_ok : btAll (fun x => faithful p_22 q_22 x ∧ x.1 < 2^256) W_22 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_22 : List (List (Nat × Nat)) := [[],[(1,2),(3,4)]]
def A_22 : BT (List (Nat × Nat)) := btOfList 1 al_22
set_option maxHeartbeats 0 in
lemma A_22_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_22 = g_22) A_22 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_22_0 : Slice r_22 g_22 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) (d 0xfffaf000fffaf000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_1 : Slice r_22 g_22 (subcubeFast 0 4) 5 := by
  have hc : Lower (varsOf 27) (d 0xffccee00ffccee00) 5 := carry_of (swaps := [(2,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_2 : Slice r_22 g_22 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) (d 0xffc0c000ffc0c000) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_11
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_3 : Slice r_22 g_22 (subcubeFast 1 4) 4 := by
  have hc : Lower (varsOf 26) (d 0xffcccc00ffcccc00) 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_4 : Slice r_22 g_22 (subcubeFast 1 2) 4 := by
  have hc : Lower (varsOf 28) (d 0xfff0f000fff0f000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_5 : Slice r_22 g_22 (identDom 1 4) 6 := by
  have hc : Lower (varsOf 15) (d 0xecc8ecc8ecc8ecc8) 6 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_6
  exact slice_ident (u := 1) (v := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_6 : Slice r_22 g_22 (identDom 2 3) 6 := by
  have hc : Lower (varsOf 23) (d 0xf8f8e0e0f8f8e0e0) 6 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_6
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_7 : Slice r_22 g_22 (identDom 0 4) 5 := by
  have hc : Lower (varsOf 15) (d 0xea88ea88ea88ea88) 5 := carry_of (swaps := [(0,3),(2,3)]) (by decide +kernel) low_8
  exact slice_ident (u := 0) (v := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_8 : Slice r_22 g_22 (identDom 0 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xeaeaa0a0eaeaa0a0) 5 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,4)]) (by decide +kernel) low_8
  exact slice_ident (u := 0) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_9 : Slice r_22 g_22 (identDom 0 1) 5 := by
  have hc : Lower (varsOf 29) (d 0xffaaa000ffaaa000) 5 := carry_of (swaps := [(0,1),(1,4),(2,4),(3,4)]) (by decide +kernel) low_8
  exact slice_ident (u := 0) (v := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_10 : Slice r_22 g_22 (subcubeFast 0 1) 4 := by
  have hc : Lower (varsOf 30) (d 0xffccf000ffccf000) 4 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
def S_22 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 0 2,5),some (subcubeFast 0 4,5),some (subcubeFast 1 0,5),some (subcubeFast 1 4,4),some (subcubeFast 1 2,4),some (identDom 1 4,6),some (identDom 2 3,6),some (identDom 0 4,5),some (identDom 0 3,5),some (identDom 0 1,5),some (subcubeFast 0 1,4)]
lemma S_22_ok : btAll (fun o => ∀ p, o = some p → Slice r_22 g_22 p.1 p.2) S_22 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_22_0) (forall_cons (fun _ h => by cases h; exact sl_22_1) (forall_cons (fun _ h => by cases h; exact sl_22_2) (forall_cons (fun _ h => by cases h; exact sl_22_3) (forall_cons (fun _ h => by cases h; exact sl_22_4) (forall_cons (fun _ h => by cases h; exact sl_22_5) (forall_cons (fun _ h => by cases h; exact sl_22_6) (forall_cons (fun _ h => by cases h; exact sl_22_7) (forall_cons (fun _ h => by cases h; exact sl_22_8) (forall_cons (fun _ h => by cases h; exact sl_22_9) (forall_cons (fun _ h => by cases h; exact sl_22_10) (fun _ h => (List.not_mem_nil h).elim))))))))))))
def ps_22 : BT (Option PoolSpec) := btOfList 5 [q 2 [],q 10 [],q 5 [],q 0 [],q 6 [],q 1 [],q 9 [],q 3 [],q 8 [],q 6 [16394,12423],q 0 [90113],q 5 [16396],q 0 [139265],q 1 [139265],q 7 [],q 4 [],q 5 [16398],q 6 [16396],q 6 [16394],q 0 [12289]]
def B_22_2 : BT (List (List Nat)) := BT.empty
lemma B_22_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 2 xs.toFinset) B_22_2 := .empty
def U_22_3 : List Nat := []
def P_22_3 : BT (Option BoundPool) := buildPoolsSubBT 5 W_22 r_22 S_22 ps_22 U_22_3
def N_22_3 : List NodeSpec := [([8,7,0,1],[],[]),([9,7,0,2],[],[]),([10,7,1,2],[],[]),([1,12,3,14],[],[]),([15,16,2,5],[],[]),([0,17,18,6],[],[]),([7,19,1,2],[],[]),([7,0,1,18],[],[]),([7,20,0,1],[],[]),([21,7,1,2],[],[]),([24,7,0,2],[],[]),([7,15,1,2],[],[]),([7,1,2,25],[],[]),([7,0,1,2],[],[]),([26,7,1,2],[],[]),([0,16,27,5],[],[]),([7,0,16,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_3 : checkNodesBT W_22 g_22 F_22 P_22_3 A_22 B_22_2 3 N_22_3 = true := by decide +kernel
def B_22_3 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_3
set_option maxRecDepth 500000 in
lemma B_22_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 3 xs.toFinset) B_22_3 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound S_22_ok) A_22_ok B_22_2_ok C_22_3
def U_22_4 : List Nat := []
def P_22_4 : BT (Option BoundPool) := buildPoolsSubBT 5 W_22 r_22 S_22 ps_22 U_22_4
def N_22_4 : List NodeSpec := [([28,0,16,2,3],[],[]),([28,7,0,1,2],[],[]),([20,0,16,3,4],[],[]),([0,16,27,3,4],[],[0]),([19,16,2,3,4],[],[]),([7,0,1,2,6],[],[0,1]),([7,0,1,2,5],[],[0,1]),([0,1,2,5,30],[],[]),([32,0,2,3,4],[],[]),([7,0,1,2,3],[],[]),([33,1,12,3,4],[],[]),([1,3,25,18,4],[],[]),([20,0,1,5,6],[],[0]),([15,16,2,3,4],[],[0]),([36,0,1,2,4],[],[]),([24,0,2,3,4],[],[]),([0,3,17,18,4],[],[0]),([33,37,0,1,3],[],[]),([29,38,2,3,4],[],[]),([0,22,2,30,4],[],[1]),([41,0,1,3,4],[],[]),([33,1,38,3,4],[],[]),([24,42,0,3,4],[],[]),([24,0,2,5,6],[],[0]),([29,43,2,3,4],[],[1]),([46,0,1,3,4],[],[]),([0,1,5,18,6],[],[0]),([24,2,3,25,4],[],[]),([20,19,1,3,4],[],[]),([28,47,0,1,2],[],[0]),([1,2,5,25,6],[],[0]),([26,24,2,3,4],[],[]),([26,1,2,5,6],[],[0]),([24,0,3,18,4],[],[]),([0,1,2,5,6],[],[0]),([15,1,2,5,6],[],[0,1]),([20,48,0,3,4],[],[]),([19,1,2,5,6],[],[0]),([0,16,2,5,6],[],[0]),([7,0,1,2],[],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_4 : checkNodesBT W_22 g_22 F_22 P_22_4 A_22 B_22_3 4 N_22_4 = true := by decide +kernel
def B_22_4 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_4
set_option maxRecDepth 500000 in
lemma B_22_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 4 xs.toFinset) B_22_4 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound S_22_ok) A_22_ok B_22_3_ok C_22_4
def U_22_5 : List Nat := (r 0 17)
def P_22_5 : BT (Option BoundPool) := buildPoolsSubBT 5 W_22 r_22 S_22 ps_22 U_22_5
def N_22_5 : List NodeSpec := [([28,47,0,1,2],[],[0,1]),u5 [6] (r 0 6),e5 [49] [0,6],([20,0,1,3,4,6],[4,7],[0]),([19,1,2,3,4,6],[0],[0,1]),([19,1,2,3,4],[],[]),u5 [28] [],([28,0,1,2,5,4],[3],[0]),([24,0,2,5,3,4],[3],[0]),([33,0,1,11,3,4],[3,5],[0]),a5 [50] [0,3,8,9] [1],([0,34,29,2,3,4],[2,5],[0]),e5 [51] [],([28,0,29,1,2,3],[3],[]),([1,43,2,3,4],[10],[0,1]),([28,47,0,1,2,3],[],[0]),([0,1,2,5,3,6],[11],[0]),([33,0,34,1,3,4],[3],[0]),([0,16,2,3,4,6],[3],[0]),a5 [52] [5] [1],([22,1,43,2,3,4],[0,10],[1]),u5 [30] [0,1,2,4,5],a5 [53] [0,2,8] [1],e5 [55] [],e5 [56] [],e5 [57] [1,4,5],([34,1,38,2,3,4],[0,12],[]),([1,38,2,3,4],[12,13],[0,1]),a5 [23] [0,5,14] [0,1],e5 [58] [],([15,1,2,3,4,6],[1,7,15],[0,1]),([24,0,2,3,4],[],[]),e5 [59] [],([0,22,29,2,3,4],[2],[0]),e5 [60] [],e5 [24] [],e5 [61] [],([28,0,1,2,3,6],[3,16],[0]),([26,1,2,5,3,4],[7,14,15],[0,1]),([0,29,1,2,5,3],[3],[0]),([1,2,3,25,4],[],[]),([1,2,5,3,25,4],[0],[0,1]),a5 [5] [0,3,5,14] [0,1],([0,1,2,5,6],[],[0,1]),a5 [63] [3,8,14] [1],([0,1,5,3,18,4],[7],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_5 : checkNodesBT W_22 g_22 F_22 P_22_5 A_22 B_22_4 5 N_22_5 = true := by decide +kernel
def B_22_5 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_5
set_option maxRecDepth 500000 in
lemma B_22_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 5 xs.toFinset) B_22_5 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound S_22_ok) A_22_ok B_22_4_ok C_22_5
def U_22_6 : List Nat := (r 0 6++[7,8,11]++r 15 5)
def P_22_6 : BT (Option BoundPool) := buildPoolsSubBT 5 W_22 r_22 S_22 ps_22 U_22_6
def N_22_6 : List NodeSpec := [a5 [28] (r 0 4++[5,16]) [0,1],a5 [6] (r 0 6) [0,1],a5 [5] [0,1,3,5,11,17] [0,1],u5 [33] [0,2,3,4,7,18],a5 [22] [0,2,5,15] [0,1],a5 [34] [0,2,3,4,7] [0,1],a5 [29] [0,2,5,15] [0,1],a5 [64] [0,1,3,5,7,8,15] [1],a5 [44] [0,1,7,8,15,19] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_6 : checkNodesBT W_22 g_22 F_22 P_22_6 A_22 B_22_5 6 N_22_6 = true := by decide +kernel
def B_22_6 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_6
set_option maxRecDepth 500000 in
lemma B_22_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 6 xs.toFinset) B_22_6 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound S_22_ok) A_22_ok B_22_5_ok C_22_6
def U_22_7 : List Nat := ([0]++r 2 4++[7,15])
def P_22_7 : BT (Option BoundPool) := buildPoolsSubBT 5 W_22 r_22 S_22 ps_22 U_22_7
def N_22_7 : List NodeSpec := [a5 [] ([0]++r 2 4++[7,15]) [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_7 : checkNodesBT W_22 g_22 F_22 P_22_7 A_22 B_22_6 7 N_22_7 = true := by decide +kernel
def B_22_7 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_7
set_option maxRecDepth 500000 in
lemma B_22_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 7 xs.toFinset) B_22_7 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound S_22_ok) A_22_ok B_22_6_ok C_22_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_22_ok : forestRootCheck r_22 g_22 [(VAR 0,12,13),(VAR 1,12,14),(VAR 2,9,13),(VAR 3,5,13),(VAR 4,3,19)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_22_in : bucketContainsBT B_22_7 r_22 = true := by decide +kernel
lemma low_22 : Lower r_22 g_22 8 := lower_of_forestBT root_22_ok B_22_7_ok root_22_in
def g_23 := (d 0xfffcfee8fac00000)
def r_23 : List Nat := varsOf 63
def p_23 : List Nat := [22,22,22,23,23,23,25,25,25,27,27,27,28,28,28,29,29,30,30,31,35,35,35,37,37,37,38,38,38,39,41,41,41,42,42,42,43,44,44,44,45,46,47,50,50,50,51,51,52,52,52,53,53,56,56,56,57,58]
def q_23 : List Nat := [20,18,6,21,19,7,24,17,9,26,19,11,24,20,12,21,13,26,14,15,34,33,3,36,33,5,36,34,6,7,40,33,9,40,34,10,11,40,36,12,13,14,15,48,34,18,49,19,48,36,20,49,21,48,40,24,49,26]
def F_23 : Nat := fullMask 58
set_option maxHeartbeats 0 in
lemma gp_23 : goodPairs g_23 p_23 q_23 := goodPairs_of (by decide +kernel)
def W_23 : BT Decor := buildWiresBT 9 (mkBase p_23 q_23 r_23) [(0,4,5),(1,0,6),(0,3,7),(1,2,8),(1,1,9),(0,10,5),(1,2,3),(1,1,12),(0,13,5),(0,14,4),(1,14,4),(3,15,16),(2,12,4),(0,13,7),(1,1,2),(2,20,3),(1,1,3),(0,22,5),(1,2,4),(0,23,24),(1,0,25),(1,2,23),(1,1,4),(0,12,28),(0,29,5),(0,12,5),(1,31,4),(3,30,32),(1,23,4),(3,25,34),(2,14,4),(1,18,14),(1,4,5),(3,6,38),(3,2,22),(0,24,5),(3,25,27),(3,1,3),(3,43,12),(0,12,4),(1,45,14),(3,0,46),(0,28,5),(1,2,48),(1,3,48),(2,13,6),(0,51,38),(1,0,15),(3,1,9),(3,2,3),(3,2,38),(1,56,3),(3,55,57),(0,12,38),(1,1,59),(3,2,60),(2,12,6),(1,62,1),(0,63,5),(3,0,63),(3,1,7),(1,66,12),(1,66,2),(3,18,5),(3,12,7),(1,70,3),(3,1,12),(3,4,5),(2,4,5),(3,74,13),(0,3,5),(1,3,5),(3,76,77),(2,78,2),(2,78,1),(3,0,16),(2,13,4),(3,74,12),(2,12,5),(1,84,82),(1,82,31),(3,18,14),(3,3,60),(3,45,14),(3,0,13),(0,13,38),(3,3,7),(2,22,6),(2,22,4),(1,94,2),(0,95,5),(3,66,12),(0,22,38),(1,2,98),(3,3,99),(1,66,3),(3,2,101),(3,2,98),(3,0,38),(2,3,48),(3,94,5),(0,20,5),(1,107,3),(2,3,4),(3,109,5),(1,94,31),(1,23,24),(3,0,112),(3,55,98),(2,20,8),(0,56,3),(3,116,57),(3,29,5),(3,2,7),(1,18,23),(3,25,5),(2,23,24),(3,122,5),(0,18,5),(3,30,12),(3,14,4),(1,3,41),(2,3,41),(3,119,22),(2,93,2),(1,93,2),(3,0,131),(1,43,2),(3,43,59),(1,0,30),(3,56,3),(1,1,136),(3,12,38),(1,1,8),(2,3,5),(3,3,5),(2,141,1),(1,140,142),(1,141,2),(1,0,136),(1,141,1),(1,78,1),(3,3,4),(1,148,0),(2,149,1),(1,150,2),(1,109,2),(0,152,5),(3,2,5),(3,109,154),(3,1,110),(3,1,153),(1,1,153),(1,3,4),(0,159,5),(1,1,160),(3,2,161),(1,2,160),(3,12,5),(1,1,41),(3,3,165),(3,1,83),(3,1,59),(3,1,5),(1,169,4),(0,12,170),(2,23,4),(3,2,34),(2,22,31),(1,154,4),(0,22,175),(1,172,2),(2,22,41),(1,2,106),(1,1,31),(0,40,5),(2,27,4),(1,140,164),(3,31,28),(2,180,4),(0,154,3),(1,154,3),(3,186,187),(3,84,13),(3,169,12),(1,2,76),(2,62,1),(3,1,31),(3,3,49),(1,12,4),(0,195,5),(3,1,196),(1,12,5),(3,31,198),(3,1,69),(0,20,110),(1,1,69),(1,1,196),(3,74,22),(3,2,204),(3,23,12),(1,18,169),(3,23,24),(1,43,41),(3,18,13),(1,12,48),(1,55,48),(1,105,2),(1,109,107),(1,181,4),(3,45,195),(3,12,4),(3,31,13),(3,2,106),(3,82,5),(1,1,83),(1,193,4),(1,78,2),(3,2,50),(0,12,7),(1,217,0),(1,18,6),(1,82,5),(1,2,204),(3,3,38),(1,230,2),(2,230,1),(1,230,1),(1,56,1),(1,2,6),(3,3,235),(1,141,4),(3,2,237),(2,149,2),(3,159,5),(1,240,2),(3,2,159),(3,242,5),(3,1,159),(0,3,4),(1,109,154),(0,154,159),(1,164,4),(3,3,175),(3,154,3),(1,1,250),(1,186,4),(2,154,1),(1,253,4),(3,24,5),(1,255,3),(3,3,24),(1,74,55),(3,1,38),(3,154,159),(1,3,6),(1,55,4),(0,262,5),(1,55,6),(3,4,198),(3,0,198),(1,18,1),(3,43,5),(1,268,2),(3,133,5),(1,142,4),(1,148,2),(1,74,2),(1,2,110),(1,109,169),(2,191,4),(3,55,5),(1,12,6),(3,76,28),(3,1,4),(3,280,12),(3,0,77),(2,56,1),(2,20,4),(1,2,5),(0,22,285),(3,2,4),(3,287,22),(0,22,24),(0,3,24),(1,1,290),(3,55,28),(3,141,24),(1,43,4),(3,2,294),(3,141,28),(0,3,38),(3,148,20),(3,3,170),(1,55,169),(3,109,20),(3,3,28),(3,154,22),(3,257,5),(1,107,4),(2,20,6),(0,13,4),(0,294,5),(1,287,43),(3,55,38),(1,169,3),(3,2,77),(0,21,5),(3,21,5),(0,302,5),(3,141,20),(1,76,4),(3,140,20),(1,74,12),(2,20,245),(1,284,3),(3,284,5),(0,20,77),(3,43,24),(3,2,28),(2,20,76),(1,280,3),(3,2,327),(3,2,261),(0,20,38),(3,76,24),(3,2,317),(3,74,20),(1,74,3),(3,2,334),(3,43,285),(1,154,43),(1,43,6),(0,20,159),(3,169,24),(1,74,43),(1,217,3),(3,12,28),(0,325,5),(1,55,280),(2,13,5),(3,302,5),(1,1,5),(0,12,348),(3,154,28),(1,302,2),(1,280,2),(1,352,3),(2,273,3),(3,12,348),(3,55,348),(3,3,348),(1,357,2),(1,169,2),(1,359,3),(3,43,38),(3,2,311),(3,2,348),(3,2,170),(0,257,5),(3,169,159),(0,4,198),(3,3,198),(3,1,198),(1,140,1),(1,2,245),(3,1,24),(1,1,245),(1,140,2),(3,1,285),(1,154,1)]
lemma W_23_ok : btAll (fun x => faithful p_23 q_23 x ∧ x.1 < 2^256) W_23 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_23 : List (List (Nat × Nat)) := [[]]
def A_23 : BT (List (Nat × Nat)) := btOfList 1 al_23
set_option maxHeartbeats 0 in
lemma A_23_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_23 = g_23) A_23 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_23_0 : Slice r_23 g_23 (subcubeFast 1 0) 10 := by
  have hc : Lower (varsOf 62) (d 0xfffcfcc0f0c00000) 10 := carry_of (swaps := [(0,5),(1,5),(3,5),(4,5)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_1 : Slice r_23 g_23 (subcubeFast 2 0) 9 := by
  have hc : Lower (varsOf 61) (d 0xfff0faa0fa000000) 9 := carry_of (swaps := [(1,5),(2,5),(4,5)]) (by decide +kernel) low_10
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_2 : Slice r_23 g_23 (subcubeFast 4 0) 9 := by
  have hc : Lower (varsOf 59) (d 0xffccee88aa000000) 9 := carry_of (swaps := [(0,1),(2,5),(4,5)]) (by decide +kernel) low_12
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_3 : Slice r_23 g_23 (subcubeFast 8 0) 8 := by
  have hc : Lower (varsOf 55) (d 0xfcfce8e8c0c00000) 8 := carry_of (swaps := [(1,2),(2,3),(3,5),(4,5)]) (by decide +kernel) low_13
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_4 : Slice r_23 g_23 (subcubeFast 16 0) 8 := by
  have hc : Lower (varsOf 47) (d 0xfee8fee800000000) 8 := carry_of (swaps := [(4,5)]) (by decide +kernel) low_14
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_5 : Slice r_23 g_23 (subcubeFast 0 32) 8 := by
  have hc : Lower (varsOf 31) (d 0xfffcfee8fffcfee8) 8 := carry_of (swaps := [(1,2),(2,3),(3,4)]) (by decide +kernel) low_15
  exact slice_fast_direct_f (z := 0) (o := 32) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_6 : Slice r_23 g_23 (subcubeFast 3 0) 7 := by
  have hc : Lower (varsOf 60) (d 0xfff0f000f0000000) 7 := carry_of (swaps := [(0,4),(1,5),(2,4),(3,5)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 3) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_7 : Slice r_23 g_23 (subcubeFast 16 32) 7 := by
  exact slice_fast_direct_f (z := 16) (o := 32) (by decide +kernel) low_2
set_option maxHeartbeats 0 in
lemma sl_23_8 : Slice r_23 g_23 (subcubeFast 1 32) 7 := by
  have hc : Lower (varsOf 30) (d 0xfffcfcc0fffcfcc0) 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 1) (o := 32) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_9 : Slice r_23 g_23 (subcubeFast 9 0) 7 := by
  have hc : Lower (varsOf 54) (d 0xfcfcc0c0c0c00000) 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,5)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 9) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_10 : Slice r_23 g_23 (subcubeFast 0 2) 8 := by
  have hc : Lower (varsOf 61) (d 0xfffffffafaf00000) 8 := carry_of (swaps := [(1,5),(3,5),(4,5)]) (by decide +kernel) low_16
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_11 : Slice r_23 g_23 (identDom 1 4) 8 := by
  have hc : Lower (varsOf 47) (d 0xfeecfeecc8c0c8c0) 8 := carry_of (swaps := [(1,4),(3,4),(4,5)]) (by decide +kernel) low_18
  exact slice_ident (u := 1) (v := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_12 : Slice r_23 g_23 (subcubeFast 0 16) 7 := by
  have hc : Lower (varsOf 47) (d 0xfffcfffcfac0fac0) 7 := carry_of (swaps := [(3,4),(4,5)]) (by decide +kernel) low_19
  exact slice_fast_direct_f (z := 0) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_13 : Slice r_23 g_23 (subcubeFast 0 1) 7 := by
  have hc : Lower (varsOf 62) (d 0xfffcfffcffc00000) 7 := carry_of (swaps := [(0,5),(1,5),(2,5),(3,5),(4,5)]) (by decide +kernel) low_20
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_14 : Slice r_23 g_23 (identDom 2 4) 8 := by
  have hc : Lower (varsOf 47) (d 0xfef8fef8f0c0f0c0) 8 := carry_of (swaps := [(2,4),(3,4),(4,5)]) (by decide +kernel) low_21
  exact slice_ident (u := 2) (v := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_15 : Slice r_23 g_23 (identDom 3 4) 8 := by
  have hc : Lower (varsOf 47) (d 0xffe8ffe8fa00fa00) 8 := carry_of (swaps := [(0,1),(3,4),(4,5)]) (by decide +kernel) low_21
  exact slice_ident (u := 3) (v := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_16 : Slice r_23 g_23 (subcubeFast 4 2) 6 := by
  have hc : Lower (varsOf 57) (d 0xffffffaaaa000000) 6 := carry_of (swaps := [(1,4),(2,5),(3,4),(4,5)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 4) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_17 : Slice r_23 g_23 (identDom 1 3) 8 := by
  have hc : Lower (varsOf 55) (d 0xfcfcececc8c80000) 8 := carry_of (swaps := [(1,3),(2,3),(3,5),(4,5)]) (by decide +kernel) low_22
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_18 : Slice r_23 g_23 (subcubeFast 24 32) 4 := by
  exact slice_fast_direct_f (z := 24) (o := 32) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_23_19 : Slice r_23 g_23 (subcubeFast 20 32) 4 := by
  have hc : Lower (varsOf 11) (d 0xee88ee88ee88ee88) 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 20) (o := 32) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_20 : Slice r_23 g_23 (subcubeFast 18 32) 4 := by
  have hc : Lower (varsOf 13) (d 0xfaa0faa0faa0faa0) 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 18) (o := 32) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_21 : Slice r_23 g_23 (subcubeFast 6 8) 4 := by
  have hc : Lower (varsOf 49) (d 0xffffaaaaaaaa0000) 4 := carry_of (swaps := [(1,3),(2,4),(3,5),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 6) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_22 : Slice r_23 g_23 (subcubeFast 17 32) 4 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 17) (o := 32) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_23 : Slice r_23 g_23 (subcubeFast 8 17) 4 := by
  have hc : Lower (varsOf 38) (d 0xfcfcfcfcc0c0c0c0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 8) (o := 17) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_24 : Slice r_23 g_23 (subcubeFast 9 4) 4 := by
  have hc : Lower (varsOf 50) (d 0xffffcccccccc0000) 4 := carry_of (swaps := [(0,3),(1,3),(2,4),(3,5),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 9) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_25 : Slice r_23 g_23 (subcubeFast 3 16) 4 := by
  have hc : Lower (varsOf 44) (d 0xfff0fff0f000f000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 3) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_26 : Slice r_23 g_23 (subcubeFast 9 2) 4 := by
  have hc : Lower (varsOf 52) (d 0xfffff0f0f0f00000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 9) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_27 : Slice r_23 g_23 (subcubeFast 3 4) 4 := by
  have hc : Lower (varsOf 56) (d 0xffffff00ff000000) 4 := carry_of (swaps := [(0,3),(1,4),(2,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 3) (o := 4) (by decide +kernel) hc
def S_23 : BT (Option (Nat × Nat)) := btOfList 5 [some (subcubeFast 1 0,10),some (subcubeFast 2 0,9),some (subcubeFast 4 0,9),some (subcubeFast 8 0,8),some (subcubeFast 16 0,8),some (subcubeFast 0 32,8),some (subcubeFast 3 0,7),some (subcubeFast 16 32,7),some (subcubeFast 1 32,7),some (subcubeFast 9 0,7),some (subcubeFast 0 2,8),some (identDom 1 4,8),some (subcubeFast 0 16,7),some (subcubeFast 0 1,7),some (identDom 2 4,8),some (identDom 3 4,8),some (subcubeFast 4 2,6),some (identDom 1 3,8),some (subcubeFast 24 32,4),some (subcubeFast 20 32,4),some (subcubeFast 18 32,4),some (subcubeFast 6 8,4),some (subcubeFast 17 32,4),some (subcubeFast 8 17,4),some (subcubeFast 9 4,4),some (subcubeFast 3 16,4),some (subcubeFast 9 2,4),some (subcubeFast 3 4,4)]
lemma S_23_ok : btAll (fun o => ∀ p, o = some p → Slice r_23 g_23 p.1 p.2) S_23 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_23_0) (forall_cons (fun _ h => by cases h; exact sl_23_1) (forall_cons (fun _ h => by cases h; exact sl_23_2) (forall_cons (fun _ h => by cases h; exact sl_23_3) (forall_cons (fun _ h => by cases h; exact sl_23_4) (forall_cons (fun _ h => by cases h; exact sl_23_5) (forall_cons (fun _ h => by cases h; exact sl_23_6) (forall_cons (fun _ h => by cases h; exact sl_23_7) (forall_cons (fun _ h => by cases h; exact sl_23_8) (forall_cons (fun _ h => by cases h; exact sl_23_9) (forall_cons (fun _ h => by cases h; exact sl_23_10) (forall_cons (fun _ h => by cases h; exact sl_23_11) (forall_cons (fun _ h => by cases h; exact sl_23_12) (forall_cons (fun _ h => by cases h; exact sl_23_13) (forall_cons (fun _ h => by cases h; exact sl_23_14) (forall_cons (fun _ h => by cases h; exact sl_23_15) (forall_cons (fun _ h => by cases h; exact sl_23_16) (forall_cons (fun _ h => by cases h; exact sl_23_17) (forall_cons (fun _ h => by cases h; exact sl_23_18) (forall_cons (fun _ h => by cases h; exact sl_23_19) (forall_cons (fun _ h => by cases h; exact sl_23_20) (forall_cons (fun _ h => by cases h; exact sl_23_21) (forall_cons (fun _ h => by cases h; exact sl_23_22) (forall_cons (fun _ h => by cases h; exact sl_23_23) (forall_cons (fun _ h => by cases h; exact sl_23_24) (forall_cons (fun _ h => by cases h; exact sl_23_25) (forall_cons (fun _ h => by cases h; exact sl_23_26) (forall_cons (fun _ h => by cases h; exact sl_23_27) (fun _ h => (List.not_mem_nil h).elim)))))))))))))))))))))))))))))
set_option maxRecDepth 500000 in
def ps_23 : BT (Option PoolSpec) := btOfList 11 [q 1 [12297,20532,16440,16441,65599],q 10 [16440,16441,65599],q 2 [49157,20532,16440,16441,65599],q 2 [20496,20497,155675],q 10 [20496,20497,155675],q 3 [20496,20497,155675],q 2 [49157,20496,24630,20497,155852],q 1 [20496,24577,28684,32777],q 0 [12299,20497,155659,12513,233695],q 1 [12299,20497,155659,12513,233695],q 21 [],q 4 [12299,155659,12513,233695],q 5 [12299,12513,233695],q 3 [20497,155696],q 10 [],q 10 [20496,24577],q 4 [],q 12 [24577],q 3 [20496,24577],q 4 [28684,32777],q 23 [],q 22 [],q 2 [20496,24577],q 1 [12297,20496,20497,155675],q 10 [12297,20496,20497,155675],q 2 [49159,20496,20497,155675],q 7 [12297],q 1 [12297,20498,53547,20499],q 10 [20498,20499],q 2 [49157,20498,53547,20499],q 0 [12297,20496,20497,155675],q 2 [49157,20496,20497,155675],q 2 [49157,20496,24630,20497],q 1 [20492,20493,315699,8506],q 2 [20492,20493,315699],q 10 [20492,20493,315699],q 24 [],q 2 [20492,20493,315699,4410],q 1 [12297,20532],q 2 [49157,20532,16441,65584],q 1 [12297,20532,16441,65539],q 10 [16441,65539],q 2 [49157,20532,16441,65539],q 1 [12297,20532,20496,24577],q 2 [49157,20532,20496,24577],q 4 [12297,49157,20532],q 0 [12297,49157,16438],q 13 [12297,16434],q 11 [20496,24577],q 5 [12297,16434,24577],q 5 [12297,49157],q 1 [12297,20496,24577,28724],q 2 [49157,20496,24577,28724],q 4 [12297,49157,28724],q 1 [12297,16434,20532],q 1 [12297,16434,20532,16442],q 1 [12297,20532,16440,61441],q 10 [16440,61441],q 2 [49157,20532,16440,61441],q 2 [49157,20532],q 3 [49157,20532],q 2 [20497,155696],q 2 [20498,20499],q 2 [49157,20532,16440,61490],q 7 [12293,94217],q 1 [12297,20496,20497,155700],q 10 [20496,20497],q 2 [49157,20496,20497,155700],q 13 [],q 1 [20497,155736],q 4 [12293,20568],q 2 [12293,20568],q 0 [12293,12297,20496,20497,155675],q 7 [12293,12297],q 2 [12293,20496,20497,155675],q 2 [],q 2 [12293,20568,16477,20576],q 1 [12297,16434,20532,57417],q 2 [20497,155651],q 10 [20497,155651],q 1 [12297,20532,16440,16441],q 10 [16440,16441],q 2 [49157,20532,16440,16441],q 7 [12293,90123],q 0 [20496,20497,155675],q 0 [12293,90123,20496,20497,155675],q 1 [20496,20497,155675],q 1 [90123,20496,20497,155675],q 7 [8197,12370],q 0 [8197,12370,20496,20497,155675],q 1 [12370,20496,20497,155675],q 2 [12370,20496,20497,155675],q 2 [20496,20497],q 2 [12293,16474,20528,127353],q 7 [12293,12299],q 10 [12299,20496,20497,155675],q 0 [12293,12299,20496,20497,155675],q 1 [12297,16434,20496,24577],q 2 [16434,20496,24577],q 3 [20496,20497],q 1 [20496,24577],q 13 [32777],q 3 [20497,155736],q 1 [20496,24577,28684,32850],q 0 [20497,155659,12512,12513,233939],q 1 [20497,155659,12512,12513,233939],q 7 [12512,12513,233939],q 7 [12295,12297],q 0 [12295,12297,20496,20497,155675],q 4 [12297,20528],q 0 [],q 1 [12297,20532,20497,155651],q 2 [49157,20532,20497,155651],q 1 [12297,20568,16434,94281],q 20 [],q 12 [],q 1 [12297,20532,16442,16443],q 10 [16442,16443],q 2 [49157,20532,16442,16443],q 3 [16389,20592],q 2 [16389,20592],q 10 [16393,20576,167949],q 1 [16393,20568,20576,167949],q 10 [16393,20576,167950],q 2 [12293,20496,24577,90591],q 3 [20497,155651],q 0 [12295,8365,20496,20497,155675],q 7 [12295,8365],q 1 [8365,20496,20497,155675],q 3 [],q 3 [20498,20499],q 0 [12297,49157,20532],q 10 [12297,20528,16509],q 1 [12297,20528,16509,20592],q 2 [12293,20568,98396,102401],q 7 [12293,98396,102401],q 2 [16389,20528,20592,196621],q 10 [12297,20528,122881],q 1 [12297,20528,114812,122881],q 7 [12297,114812,122881],q 0 [20497,155659,12515,557061],q 1 [20497,155659,12515],q 10 [20497,155659],q 3 [20497,155659],q 19 [],q 0 [20497,155659,12514,12515],q 1 [20497,155659,12514,12515],q 7 [12514,12515],q 5 [24577,28684,32777],q 7 [28684,32777],q 2 [20496,24577,28684,32773],q 4 [28684,32773],q 13 [32773],q 5 [24577,28684,32773],q 7 [28684,32773],q 2 [20496,24577,12765],q 13 [12765],q 1 [20496,24577,12553],q 13 [12553],q 0 [20494,20495,4662,582193],q 1 [20494,20495,582193],q 10 [20494,20495],q 2 [20494,20495,4662,582193],q 7 [4662],q 2 [20494,20495,578097],q 0 [20494,20495,578097],q 0 [20494,20495,578097,8506],q 1 [20494,20495,578097],q 10 [20494,20495,578097],q 18 [],q 1 [20494,20495,578097,8506],q 0 [20494,20495,578097,4410],q 7 [4410],q 0 [20494,20495,578097,8757],q 1 [20494,20495,578097,8757],q 1 [20497,155659,12515,557057],q 9 [20497,155659],q 0 [20494,20495,578097,4661],q 2 [20494,20495,578097,4661],q 0 [20492,20493,315699],q 0 [20492,20493,315699,8506],q 1 [20492,20493,315699],q 7 [8506],q 0 [20492,20493,315699,4409],q 2 [20492,20493,315699,4409],q 2 [16399,593,4694],q 13 [8793],q 1 [16399,593,8793],q 10 [16399,593],q 7 [4694,8793],q 0 [16398,20919,450571,21103],q 2 [16398,20919,21103],q 1 [16398,20919,450571],q 2 [16398,20919],q 1 [],q 27 [],q 1 [16398,8629,21088],q 1 [16397,21116,659467],q 2 [16397,21116,655365],q 10 [16397,21116,655369],q 1 [16397,21116],q 2 [16397,21116],q 2 [12906,21139],q 3 [20491,21139],q 1 [16393,20576,675855],q 26 [],q 0 [12299,20497,155659,12513],q 1 [12299,20497,155659,12513],q 1 [12297,20498,49451],q 2 [20497,155696,241671],q 10 [12297,20497,155696],q 1 [12297,20497,155696],q 0 [12297,20497,155696],q 2 [20497,155696,241669],q 4 [12297,155696],q 5 [12297],q 1 [12297,20496,24626],q 0 [12297,20496,24626],q 4 [12297],q 5 [12297,24626],q 0 [20494,20495,578097,4662],q 0 [20487,17061,12297,696368],q 10 [12297,696368],q 1 [17061,12297,696368],q 2 [20487,17061,696368],q 7 [12297,696368],q 2 [12295,20497,155651],q 8 [12295,8365],q 1 [8365,20497,155651],q 4 [155651],q 0 [12295,8365,20496,20497],q 4 [12295,8365],q 5 [12295,8365],q 1 [8365,20496,20497],q 4 [8197,12370],q 0 [20498,20499],q 0 [8197,12370,20498,20499],q 1 [20498,20499],q 1 [12370,20498,20499],q 2 [12370,20498,20499],q 2 [12293,16434,20496],q 11 [20496],q 1 [12297,16434],q 2 [12293,20496,24666],q 0 [12293,20496,24666],q 4 [12293],q 10 [20496],q 2 [20496],q 16 [],q 1 [12297,90123],q 1 [8365,20496,24577],q 13 [12295,8365],q 16 [20496,24577],q 2 [12293,20568,16477],q 1 [12299,20496,24577],q 2 [12293,20496,24577],q 10 [12299,20496,24577],q 5 [12293,12299,24577],q 14 [],q 1 [20568,16478],q 2 [12293,20568,16478],q 3 [20528],q 2 [12293,20528,127066],q 1 [12297,20528],q 1 [12297,20528,127066],q 10 [12297,20528],q 1 [16474,20496,24577],q 2 [12293,16474,20496,24577],q 5 [24577],q 5 [12293,16474,24577],q 7 [12293],q 8 [12293,90123],q 1 [20497,155651],q 1 [90123,20497,155651],q 2 [12293,20497,155651],q 0 [20496,20497],q 0 [8197,12370,20496,20497],q 1 [20496,20497],q 1 [12370,20496,20497],q 5 [8197,12370],q 2 [12370,20496,20497],q 7 [12297,49159],q 11 [],q 1 [20496,24577,8457],q 2 [20496,24577,28679],q 13 [8457],q 7 [28679,8457],q 3 [20499],q 1 [12297],q 10 [12297],q 1 [12297,16434,20552],q 2 [16434,20552],q 0 [20494,20495,578097,8758],q 1 [20494,20495,578097,8758],q 7 [8758],q 4 [12297,49157,53251],q 2 [49157,53251,20498],q 7 [12293,716888],q 0 [12293,20491,17001,716888],q 1 [20491,17001,716888],q 2 [12293,17001,716888],q 1 [20568],q 7 [12293,8881],q 5 [16393],q 1 [12297,20528,16509],q 0 [12293,16393,20576,168026],q 1 [16393,20576,168026],q 2 [12293,20576,168026],q 7 [12293,168026],q 1 [16393,20576],q 1 [16393,20576,167950],q 10 [16393],q 2 [12293,20568,20576],q 4 [12293,20568,20576],q 5 [12293],q 3 [20498],q 2 [20497],q 10 [20497],q 0 [12293,20497,155736],q 1 [20497,155736,401417],q 2 [12293,20497,155736],q 10 [16393,20576],q 1 [16393,20568,20576],q 2 [20496,24577,28684],q 2 [12293,20568,98398],q 7 [12293,98398],q 0 [12293,20568],q 3 [20568],q 0 [12295,12297,49327],q 3 [20496],q 2 [12293,16474,20859],q 0 [12297,49157,16432,16438],q 1 [12297,16432],q 2 [49157,16432,16438],q 4 [12297,49157],q 12 [12297],q 7 [12297,49157],q 1 [12297,16432,16438],q 1 [12297,20528,16510],q 10 [20497,401419],q 1 [20497,155736,401419],q 1 [20592,196621],q 0 [12297,20496,20497],q 1 [12297,20496,20497],q 2 [49157,20496,20497],q 2 [12293,20568,98396],q 7 [12293,98396],q 1 [20568,94219],q 3 [20568,94219],q 2 [12293,20568,16494],q 0 [20494,20495,8758,672305],q 2 [20494,20495,672305],q 1 [20494,20495,8758,672305],q 1 [12297,20532,20499],q 10 [20499],q 2 [49157,20532,20499],q 2 [12293],q 5 [12293,12297],q 1 [12297,16434,20499],q 2 [16434,20499],q 5 [],q 7 [12297,114815],q 2 [16389,20528,114815],q 0 [12293,90123,20496,20497],q 1 [90123,20496,20497],q 4 [12293,90123],q 5 [12293,90123],q 2 [12293,20496,20497],q 0 [12297,20528],q 1 [12297,20528,114812],q 2 [20528],q 7 [12297,114812],q 3 [20496,24666],q 1 [12299,20496,24666],q 5 [16389],q 1 [12297,20497,155651],q 8 [12293,12297],q 10 [12297,20497,155651],q 2 [20498],q 10 [20498],q 0 [12293,12297,20496,20497],q 4 [12293,12297],q 10 [12297,20496,20497],q 1 [12297,20528,17106],q 7 [12297,126981],q 1 [12297,16438,20496],q 2 [49157,16438],q 10 [16478],q 4 [12295,12297],q 5 [12295,12297],q 0 [12295,12297,20496,20497],q 1 [16393,20576,167949],q 0 [20491,12904,12905,766699],q 1 [20491,12904,12905,766699],q 2 [12904,12905,766699],q 3 [16393,20576],q 0 [12293,20496,20497,155675],q 1 [16397,21116,655369],q 1 [12297,16474,20496],q 14 [20496],q 2 [12293,16474],q 1 [12297,20496,24666],q 0 [12293,12297,20496,24666],q 0 [12297,49157,16432,20532],q 1 [12297,16432,20532],q 2 [49157,16432,20532],q 0 [8197,20496,20497,155675],q 7 [8197],q 0 [12297,20528,20607,12945],q 1 [12297,20528,20607,12945],q 2 [20528,20607,12945],q 1 [12297,20496,24577],q 2 [49157,20496,24577],q 5 [12297,24577],q 3 [20496,24626],q 0 [12297,49157,20530,53587],q 1 [12297,20530,53587],q 2 [49157,20530,53587],q 1 [12297,20498,53547],q 2 [49157,20498,53547],q 2 [20498,49451],q 0 [20487,12297,49831,20528],q 1 [12297,49831,20528],q 2 [20487,49831,20528],q 10 [12297,20496,24577],q 2 [49159,20496,24577],q 4 [12297,49159],q 1 [20496,24577,28687],q 13 [8197],q 0 [8197,20560,20492,311305],q 1 [20560,20492,311305],q 3 [8197,20560],q 10 [20492,311305],q 16 [20492],q 7 [8197,311305],q 10 [12297,20496,24626],q 2 [20499],q 1 [20496,24577,28684],q 1 [12297,20568,20528],q 2 [12293,20568,20528],q 3 [20568,20528],q 0 [12295,12297,20497,155696],q 0 [8197,20560,16398,8629],q 1 [20560,16398,8629],q 10 [16398,8629],q 7 [8197,8629],q 0 [12297,20498,49451],q 4 [12293,12299],q 1 [12299,20498,20499],q 2 [12293,20498,20499],q 10 [12299,20498,20499],q 2 [20528,126983],q 3 [20528,126983],q 1 [20592],q 2 [16389,20592,200719],q 10 [16478,21171],q 1 [20568,16478,21171],q 8 [8197,12370],q 1 [12370,20497,155651],q 2 [12370,20497,155651],q 2 [20528,20529,811135],q 0 [12297,20528,20529,811135],q 0 [12297,16434,20555],q 4 [12297,20555],q 25 [],q 0 [8197,20560,12717,20492],q 0 [12293,12297,20498,20499],q 1 [12297,20498,20499],q 10 [12297,20498,20499],q 1 [12297,49327],q 3 [20497],q 1 [12299,20497,155736],q 0 [12293,12299,20497,155736],q 1 [90123,20496,24577],q 1 [12297,20532,16440],q 10 [16440],q 2 [49157,20532,16440],q 2 [49157],q 3 [49157],q 2 [20560,20492],q 1 [12297,16434,20555],q 2 [20528,16509],q 10 [20496,8566],q 0 [12293,12297,20497,155736],q 1 [12297,20497,155736],q 10 [12297,20497],q 0 [12293,12297,20497,155696],q 2 [12293,20497,155696],q 1 [12297,16433,21260],q 2 [12293,20498,90411],q 1 [20498,90411],q 1 [12299,20496,20497],q 10 [12299,20496,20497],q 5 [12293,12299],q 2 [16434,20555],q 2 [12293,20496,24626],q 7 [],q 7 [12299],q 0 [12299,20496,20497,155675],q 13 [12297],q 8 [12297],q 2 [49157,20497,155651],q 4 [12297,155651],q 16 [20528],q 3 [90123,20528],q 0 [20492,20493,315699,4410],q 0 [12293,90123,20498,20499],q 1 [90123,20498,20499],q 0 [12297,49157,20530,20532],q 1 [12297,20530,20532],q 2 [49157,20530,20532],q 0 [8197,20560,12717,16398],q 7 [8197,12717],q 1 [12297,20568,49247],q 2 [12293,20568,49247],q 7 [12297,692297],q 1 [12297,16434,692297],q 10 [12297,16434],q 2 [20487,16434,692297],q 8 [12295,12297],q 1 [20568,16477],q 1 [20568,94217],q 0 [12297,49157,20530],q 1 [12297,53251],q 1 [12297,53251,20530],q 2 [49157,53251],q 2 [49157,53251,20530],q 3 [49157,53251],q 7 [12297,49157,53251],q 1 [12297,16434,20496],q 2 [16434,20496],q 13 [12293,12297],q 5 [12293,12297,24577],q 1 [20496,24577,28683],q 10 [20496,24577,28683],q 1 [12297,20528,20592],q 2 [16389,20528,20592],q 1 [12299,20497,155651],q 10 [12299,20497,155651],q 1 [12297,20532,20496],q 2 [49157,20532,20496],q 4 [12297,28723],q 0 [12295,12297,20498,20499],q 0 [12297,49157,16434,53323],q 4 [12293,20859],q 7 [12295],q 0 [12295,20496,20497,155675],q 1 [12297,20532,16441],q 10 [16441],q 2 [49157,20532,16441],q 0 [12297,49157,16432],q 13 [12297,16432],q 1 [12297,53251,16432],q 2 [49157,53251,16432],q 5 [12297,49157,53251],q 0 [12297],q 10 [12297,20596],q 2 [16389,114736,20596],q 7 [12297,114736],q 10 [12297,20599],q 2 [16389,114736,20599],q 1 [12297,114736],q 2 [16389,114736,20528],q 4 [12297,114736],q 0 [16389,20592],q 4 [20592],q 0 [12297,16434,20496],q 5 [12297,16434],q 2 [16389,20592,196621],q 2 [16389,20592,196622],q 0 [12297,16399,16434],q 12 [593],q 1 [12297,16399,593,16434],q 0 [16389,12297,20592,196658],q 1 [12297,20592,196658],q 2 [16389,20592,196658],q 7 [12297,196658],q 10 [12297,196658],q 7 [12297,49831],q 1 [12297,49831],q 0 [12297,49157,20528],q 1 [12297,53251,20528],q 2 [49157,53251,20528],q 2 [49157,53251,20496],q 0 [12297,16434,20552],q 4 [12297,20552],q 0 [8197,20560,16398,438709],q 1 [20560,16398,438709],q 2 [20560,16398,438709],q 7 [8197,438709],q 0 [12297,49157,16434,20532],q 2 [49157,16434,20532],q 13 [12295,12297],q 1 [12297,20496,24630],q 2 [49157,20496,24630],q 10 [16477],q 1 [20495,20568],q 10 [20495],q 3 [20568,16477],q 2 [12293,20568,17109],q 7 [12293,94219],q 0 [12297,16434,16435,888905],q 1 [12297,16434,16435,888905],q 2 [16434,16435,888905],q 11 [20499],q 0 [12297,16434,20499],q 2 [49157,16438,20498],q 0 [12297,49157,20528,53375],q 1 [12297,20528,53375],q 0 [12297,20528,16509],q 5 [12297,16509],q 0 [12293,16399,16474],q 1 [16399,593,16474],q 2 [12293,16399,593,16474],q 13 [12293,16474],q 1 [20495,20568,16478],q 3 [20568,16478],q 0 [12297,49157,20528,16438],q 1 [12297,16438],q 1 [12297,20528,16438],q 2 [49157,20528,16438],q 3 [49157,16438],q 1 [12370,20496,24577],q 2 [12370,20496,24577],q 0 [12293,16474,20859],q 5 [12297,49157,16438],q 0 [12297,49157,20530,16438],q 1 [12297,20530,16438],q 2 [49157,20530,16438],q 1 [12297,16438,20811],q 2 [49157,16438,20811],q 1 [12297,20532,16442],q 10 [16442],q 2 [49157,20532,16442],q 1 [12297,20532,16443],q 10 [16443],q 2 [49157,20532,16443],q 2 [49159],q 2 [49159,20496,24626],q 10 [12297,196617],q 1 [12297,20532,20497],q 2 [49157,20532,20497],q 1 [12297,20532,20498],q 2 [49157,20532,20498],q 2 [49157,20496,24626],q 2 [49157,20497,155696],q 1 [12297,20528,17157],q 7 [12297,126983],q 0 [12295,8365,20498,20499],q 1 [8365,20498,20499],q 1 [12297,20497,155700],q 2 [49157,20497,155700],q 0 [12297,20498,20499],q 2 [49157,20498,20499],q 0 [12297,20495,8757,20528],q 1 [12297,20495,8757,20528],q 2 [49159,20497,155651],q 0 [20492,20493,315699,8505],q 1 [20492,20493,315699,8505],q 2 [49159,20497,155696],q 2 [49159,20498,20499],q 2 [20495,20528,16510],q 0 [12297,16432,16433,798903],q 1 [12297,16432,16433,798903],q 2 [16432,16433,798903],q 5 [12297,49159],q 2 [49159,20496,20497],q 2 [20528,20607],q 3 [20528,20607],q 2 [16434,20555,20528],q 2 [20496,24577,28720],q 4 [12297,28720],q 0 [12293,16474,8569,20860],q 1 [16474,8569,20860],q 2 [12293,16474,20860],q 7 [12293,8569],q 0 [12297,16434,16435],q 1 [12297,16434,16435,869],q 2 [16434,20496,24649],q 2 [49157,16438,20809],q 2 [20528,126981],q 3 [20528,126981],q 0 [8197,20492,20493,315699],q 1 [12297,20528,20529,811135],q 1 [12297,20530,49491],q 0 [20497,155659,12512,12513],q 1 [20497,155659,12512,12513],q 0 [12297,20531,8849,12945],q 1 [12297,20531,8849,12945],q 4 [28679],q 2 [20497,155663],q 0 [20497,155663],q 0 [20497,155663,9114],q 1 [20497,155663],q 1 [20497,155663,9114],q 10 [20497,155663],q 7 [9114],q 0 [20497,155663,9113],q 1 [20497,155663,9113],q 0 [20497,155663,5018],q 7 [5018],q 0 [20497,155663,5017],q 2 [20497,155663,5017],q 0 [20497,155659,12513],q 1 [20497,155659,12513],q 2 [20497,12513],q 7 [12513],q 0 [20497,155659],q 0 [20497,155659,12514],q 1 [20497,155659],q 1 [20497,155659,12514],q 7 [12514],q 7 [12512],q 0 [20497,155659,4321],q 0 [20496,24585,962575],q 1 [20496,24585,962575],q 4 [28684],q 5 [24577,28684],q 7 [28684],q 2 [20495,16949],q 4 [20495],q 4 [20495,970763],q 0 [20495,16949,970763],q 1 [20495,16949,970763],q 7 [970763],q 0 [20495,16949],q 0 [20495,8758,16949],q 1 [20495,16949],q 10 [20495,16949],q 3 [8757],q 2 [20494,20495],q 0 [20494,20495,8757],q 1 [20494,20495],q 3 [4661],q 0 [20494,20495],q 0 [20494,20495,4661],q 0 [20492,20787,8757],q 1 [20492,20787,8757],q 2 [20492,20787],q 2 [16399,593],q 1 [16399,593],q 1 [16399,593,8790],q 0 [16399],q 5 [16399,593],q 7 [4694],q 0 [16398,20919],q 0 [16398,20919,450571],q 1 [16398,20919],q 10 [16398,20919],q 0 [16398,8629,21088],q 2 [16398,21088],q 1 [16398,8629],q 5 [16398,8629],q 7 [8629],q 0 [16397,21119,9153],q 1 [16397,21119,9153],q 2 [16397,21119],q 0 [16397,21116,655365],q 10 [16397,21116],q 0 [16397,20495,21116],q 1 [16397,20495,21116],q 0 [16397,651275,21451],q 1 [16397,651275,21451],q 2 [16397,21451],q 2 [20496,24577,28687],q 0 [16396,16397],q 0 [16396,16397,651271],q 10 [16396,16397],q 1 [16396,16397],q 15 [651271],q 3 [651271],q 0 [20491,16398,8629],q 1 [20491,16398,8629],q 0 [20491,16398,631221],q 1 [20491,16398,631221],q 3 [20491],q 0 [20491,16397,651880],q 1 [20491,16397,651880],q 2 [16397,651880],q 0 [20495,8758,17041],q 1 [20495,8758,17041],q 0 [20491,17001,716815],q 1 [20491,17001,716815],q 7 [716815],q 3 [4662],q 0 [20494,20495,4662],q 7 [651275],q 12 [20491],q 0 [20491,16397,651275],q 1 [20491,16397,651275],q 0 [20491,12907,1024005],q 5 [12907,1024005],q 1 [20491,12907],q 10 [20491],q 7 [12907,1024005],q 2 [12907,1024005],q 0 [20491,12906,21139],q 1 [20491,12906,21139],q 0 [20491,12906,8849],q 1 [20491,12906,8849],q 2 [12906],q 0 [20491,12905,20492],q 1 [20491,12905,20492],q 2 [12905,20492],q 0 [20491,12904,17129],q 1 [20491,12904,17129],q 2 [12904,17129],q 0 [20491,17001],q 0 [20491,4714,17001],q 10 [20491,17001],q 2 [4714,17001],q 1 [20491,17001],q 4 [20491],q 0 [20491,4714,21495],q 1 [20491,21495],q 5 [4714],q 7 [4714],q 0 [20491,4714,17397],q 1 [20491,17397],q 5 [4714,17397],q 2 [4714,17397],q 0 [16393,20579,13309],q 1 [16393,20579,13309],q 2 [20579,13309],q 7 [13309],q 0 [20491,16398,631223],q 1 [20491,16398,631223],q 7 [631223],q 0 [16393,20576,167949],q 4 [20576,167949],q 0 [16393,20576],q 0 [16393,20576,167950],q 2 [20576],q 2 [20576,167950],q 7 [167950],q 2 [20576,167949],q 7 [167949],q 0 [16393,20576,167941],q 2 [20576,167941],q 4 [20576,167941],q 7 [98319],q 12 [20495],q 0 [16393,98319,20495],q 1 [16393,98319,20495],q 0 [16393,98319,20492],q 1 [16393,98319,20492],q 3 [16393],q 4 [12299],q 0 [12299,20498,20499],q 0 [12299,20498,225577],q 1 [12299,20498,225577],q 2 [20498,225577],q 10 [12299],q 0 [12299,20497,155663],q 3 [20497,155655],q 0 [12299,20497,155655],q 2 [20497,155655],q 8 [],q 8 [12299],q 0 [20491,16397,651883],q 1 [20491,16397,651883],q 2 [16397,651883],q 0 [12299,20496,24589],q 1 [12299,20496,24589],q 10 [20496,24589],q 2 [20496,24589],q 0 [12299,16605,21528],q 1 [12299,16605,21528],q 2 [16605,21528],q 3 [21528],q 3 [21088],q 3 [20498,49451],q 0 [12299,20496,24797],q 1 [12299,20496,24797],q 2 [20496,24797],q 0 [12297,20497,155699],q 1 [12297,20497,155699],q 2 [20497,155699],q 0 [12297,20497,155663],q 1 [12297,20497,155663],q 13 [12299],q 0 [12297,20497,155659],q 1 [12297,20497,155659],q 0 [12297,20497,155655],q 0 [16397,21116,655369],q 7 [655369],q 0 [16393,20492,311305],q 1 [16393,20492,311305],q 7 [311305],q 0 [12297,20531,12945],q 1 [12297,20531,12945],q 2 [20531,12945],q 0 [12297,20531,8849],q 1 [12297,20531,8849],q 0 [12297,20530,20531],q 2 [20530,20531],q 0 [12297,20529,811027],q 1 [12297,20529,811027],q 2 [20529,811027],q 1 [12297,20529,811011],q 2 [20529,811011],q 2 [20528,16510],q 5 [12297,126981],q 0 [12297,20528,20607],q 1 [12297,20528,20607],q 0 [12297,20528,126981],q 1 [12297,16435,869],q 0 [12297,16435],q 2 [16435,869],q 0 [16398,20919,450567],q 3 [450567],q 7 [450567],q 2 [16398,20919,450567],q 0 [12297,20531],q 0 [12297,16434,20531],q 1 [12297,20531],q 10 [12297,20531],q 2 [16434,20531],q 0 [12297,16434,20528],q 2 [16434,20528],q 1 [12297,16434,16435],q 2 [16434,16435],q 3 [16434],q 3 [16434,20555],q 4 [12297,4169],q 2 [16434,4169],q 0 [12297,16433,798735],q 1 [12297,16433,798735],q 3 [16433],q 0 [12297,16432,16433],q 1 [12297,16432,16433],q 2 [16432,16433],q 0 [12297,16432,49335],q 2 [16432,49335],q 0 [20491,17002,21503],q 1 [20491,17002,21503],q 0 [12297,20495,20528],q 2 [20495,20528],q 1 [20495],q 1 [12297,20495,20528],q 0 [12297,20495,16949],q 3 [16949],q 0 [12297,20495,8757],q 1 [12297,20495,8757],q 2 [12295,49327],q 13 [12293],q 5 [12293,24577],q 2 [12293,16399,593],q 6 [16399],q 0 [12293,16399],q 0 [16389,20592,196617],q 1 [20592,196617],q 10 [196617],q 7 [196617],q 0 [12295,20655,9265],q 1 [20655,9265],q 10 [9265],q 2 [12295,20655],q 0 [16389,12297,114736],q 2 [16389,114736],q 3 [16389,114736],q 0 [12295,8365,21015],q 1 [8365,21015],q 3 [21015],q 0 [12293,12297,20528],q 2 [12293,20528],q 12 [12293],q 0 [16389],q 0 [16389,12297,20528],q 2 [16389],q 2 [16389,20528],q 3 [16389],q 0 [20495,4662,16953],q 1 [20495,16953],q 2 [20495,4662,16953],q 0 [12297,16399,8785],q 1 [12297,16399,8785],q 0 [12293,20498,20499],q 0 [12293,20498,8489],q 2 [12293,20498],q 10 [20498,8489],q 1 [20498,8489],q 0 [12297,20496],q 0 [12297,49157],q 1 [12297,20496],q 2 [49157,20496],q 0 [12293],q 0 [12293,20497,155659],q 2 [12293,20497],q 1 [12297,20498],q 0 [20491,12905],q 0 [20487,20491,12905],q 5 [12905],q 2 [12905],q 2 [20487,12905],q 17 [],q 10 [20491,12905],q 7 [12905],q 0 [12297,16433,21260],q 2 [16433,21260],q 0 [12295,8365],q 0 [12295,8365,20499],q 1 [8365],q 1 [8365,20499],q 2 [12295],q 2 [12295,20499],q 16 [20499],q 0 [12293,20496,20497],q 1 [20496,24666],q 0 [12297,20496,24589],q 1 [12297,20496,24589],q 3 [16434,20496],q 0 [12293,12297,90123],q 3 [90123],q 0 [16398,20919,450569],q 1 [16398,20919,450569],q 3 [450569],q 7 [450569],q 0 [20487,16398,692661],q 1 [16398,692661],q 2 [20487,16398,692661],q 3 [20487],q 0 [12293,20496,24585],q 10 [20496,24585],q 1 [20496,24585],q 2 [12293,20496],q 0 [20492,311305],q 0 [20492,311305,17150],q 1 [20492,311305],q 2 [20492],q 2 [20492,17150],q 3 [17150],q 4 [20492,311305],q 1 [20492,311305,17150],q 2 [12293,20576],q 4 [12293,20576],q 0 [12297,20531,17041],q 2 [20531,17041],q 4 [12297,20531],q 0 [12293,20568,16477],q 3 [8197],q 0 [8197,20494,20495],q 0 [12293,20568,94217],q 10 [94217],q 0 [20491,12904,21227],q 1 [20491,12904,21227],q 5 [12904],q 7 [12904],q 4 [8197],q 0 [12293,16474,8569],q 1 [16474,8569],q 0 [20487,12297,49831],q 2 [20487,49831],q 3 [20487,49831],q 0 [12293,20495,20568],q 2 [16399,16434],q 1 [12297,16399,16434],q 0 [12297,20496,24625],q 1 [12297,20496,24625],q 2 [20496,24625],q 0 [16389,20492,114995],q 1 [20492,114995],q 2 [16389,20492,114995],q 0 [12293,20493,20568],q 1 [20493,20568],q 2 [12293,20493,20568],q 0 [16391,12297,50275],q 1 [12297,50275],q 2 [16391,50275],q 3 [16391,50275],q 10 [12297,16432],q 2 [49157,16432],q 1 [20493,315395],q 8 [12293],q 10 [20493,315395],q 2 [12293,20493,315395],q 4 [20493,315395],q 0 [20497,155659,4322],q 7 [4322],q 0 [8197,16466,16396],q 1 [16466,16396],q 2 [16466,16396],q 3 [8197,16466],q 0 [12293,16397,21116],q 3 [21116],q 4 [21116],q 0 [12295,8365,20498],q 1 [8365,20498],q 2 [12295,20498],q 0 [8197,16398,8629],q 2 [16398],q 12 [8197],q 4 [8197,8629],q 0 [16397],q 0 [12293,16397,20568],q 1 [16397],q 1 [16397,20568],q 10 [16397],q 2 [16397],q 0 [12293,20491,20568],q 1 [20491,20568],q 0 [12293,20489,1167448],q 1 [20489,1167448],q 2 [12293,1167448],q 3 [20489,1167448],q 0 [12293,16395,91263],q 1 [16395,91263],q 2 [12293,91263],q 0 [12293,16393,20579],q 1 [16393,20579],q 10 [16393,20579],q 2 [12293,20579],q 0 [12293,16393,20576],q 0 [8197,20492,20493],q 5 [8197],q 1 [20492,20493],q 2 [20492,20493],q 4 [20492,20493],q 0 [12293,16393,98392],q 1 [16393,98392],q 2 [12293,98392],q 3 [16393,98392],q 4 [12293,98392],q 7 [12293,98392],q 0 [16389,12299,20703],q 1 [12299,20703],q 4 [12299,20703],q 2 [16389,20703],q 0 [20497],q 0 [12293,90123,20497],q 1 [20497],q 1 [90123,20497],q 0 [8197,20497,155659],q 4 [155659],q 0 [16393,98316,1187845],q 2 [98316,1187845],q 4 [98316,1187845],q 7 [98316,1187845],q 0 [16389,12299,114911],q 1 [12299,114911],q 2 [16389,114911],q 0 [16398,16821,651275],q 1 [16398,16821,651275],q 2 [16398,16821],q 0 [20496],q 0 [12293,90123,20496],q 1 [20496],q 1 [90123,20496],q 0 [12293,90123,20491],q 1 [90123,20491],q 3 [90123,20491],q 0 [8197,12370,20496],q 1 [12370,20496],q 2 [12370,20496],q 0 [16393,20495,98871],q 1 [16393,20495,98871],q 2 [20495,98871],q 1 [12299,20497],q 10 [12299,20497],q 0 [12293,12299,20497],q 0 [20491,12904,12905],q 1 [20491,12904,12905],q 2 [12904,12905],q 0 [12293,20491,17001],q 2 [12293,17001],q 3 [20491,17001],q 0 [12293,20495,16949],q 1 [12299,20496],q 10 [12299,20496],q 0 [12293,12299,20496],q 0 [12295,16557],q 0 [12295,16557,20491],q 1 [16557],q 1 [16557,20491],q 5 [12295,16557],q 4 [12295],q 2 [12295,16557],q 2 [20493,315395],q 8 [8197],q 3 [315395],q 0 [12295,16557,1204235],q 1 [16557,1204235],q 3 [1204235],q 0 [16389,20495,115255],q 1 [20495,115255],q 2 [16389,20495,115255],q 0 [8197,20497,155660],q 1 [20497,155660],q 2 [20497,155660],q 4 [155660],q 4 [8197,155660],q 0 [8197,16399,82515],q 1 [16399,82515],q 10 [16399],q 2 [16399,82515],q 0 [20487,17061,696335],q 1 [17061,696335],q 2 [20487,17061,696335],q 7 [696335],q 1 [12297,20530],q 2 [49157,20530],q 10 [12297,20530],q 0 [12293,12297],q 0 [12293,12297,20498],q 10 [12297,20498],q 1 [20498],q 0 [12295,8365,20497],q 1 [8365,20497],q 0 [20487,12299,692445],q 1 [12299,692445],q 2 [20487,692445],q 7 [12299,692445],q 1 [12297,20499],q 10 [12297,20499],q 2 [49159,20499],q 0 [8197,16398,20919],q 4 [20919],q 0 [8197,16398,82359],q 1 [16398,82359],q 2 [16398,82359],q 4 [8197,82359],q 10 [16398],q 0 [12295,16393,20576],q 2 [12295,20576],q 12 [12295],q 0 [12293,20491,16474],q 1 [20491],q 1 [16474],q 1 [20491,16474],q 3 [16474],q 0 [20491,12906,17041],q 1 [20491,12906,17041],q 2 [12906,17041],q 5 [12297,126983],q 0 [16389,20491,114703],q 0 [12293,12297,20530],q 2 [12293,20530],q 0 [8197,16396,16397],q 2 [16396,16397],q 15 [8197],q 1 [12297,20493,315395],q 0 [12293,20491,90731],q 1 [20491,90731],q 2 [12293,90731],q 3 [20491,90731],q 7 [12293,90731],q 0 [12293,90123,20640],q 1 [90123,20640],q 0 [12293,12297,16474],q 1 [12297,16474],q 5 [12293,16474],q 0 [16393,98319,21511],q 1 [16393,98319,21511],q 2 [98319,21511],q 0 [8197,20560,20494],q 1 [20560,20494],q 2 [20560,20494],q 0 [8197,20560,16813],q 1 [20560,16813],q 2 [20560,16813],q 10 [16813],q 0 [8197,20496,24658],q 1 [20496,24658],q 2 [20496,24658],q 0 [12297,49157,16436],q 1 [12297,16436],q 2 [49157,16436],q 3 [49157,16436],q 0 [12295,16557,21656],q 1 [16557,21656],q 3 [21656],q 2 [12295,16557,21656],q 0 [12295,16395,177277],q 1 [16395,177277],q 2 [12295,177277],q 3 [16395],q 0 [12297,20498],q 2 [49157,20498],q 1 [16399,16474],q 2 [12293,16399,16474],q 0 [12297,16397,651275],q 1 [12297,16397,651275],q 0 [12297,20493,315443],q 1 [12297,20493,315443],q 0 [8197,20560,12717],q 0 [20492],q 0 [8197,20560,20492],q 1 [20560,20492],q 0 [12299,20497,155871],q 1 [12299,20497,155871],q 2 [20497,155871],q 0 [16397,21116],q 0 [8197,16397,21116],q 4 [8197,21116],q 0 [20487,12965,20492],q 1 [12965,20492],q 2 [20487,12965,20492],q 0 [12293,12299],q 0 [12293,12299,20498],q 1 [12299],q 10 [12299,20498],q 0 [16389,114703,20492],q 1 [114703,20492],q 2 [16389,114703,20492],q 0 [12297,20493,315403],q 1 [12297,20493,315403],q 0 [8197,12370,20564],q 1 [12370,20564],q 2 [12370,20564],q 0 [8197,12370,20497],q 1 [12370,20497],q 2 [12370,20497],q 0 [8197,12370,20567],q 1 [12370,20567],q 2 [12370,20567],q 3 [8197,20567],q 10 [20567],q 0 [16389,114703,21688],q 1 [114703,21688],q 2 [16389,114703,21688],q 7 [114703],q 2 [49159,20498],q 0 [20491],q 2 [17001,716815],q 0 [20491,12905,20495],q 1 [20491,12905,20495],q 0 [16393],q 0 [12295,20655,16393],q 1 [16393],q 1 [20655,16393],q 0 [12297,20530,49491],q 2 [20530,49491],q 0 [8197,20495,82487],q 1 [20495,82487],q 2 [20495,82487],q 5 [8197,82487],q 7 [8197,82487],q 7 [28679],q 3 [8758],q 0 [20494,20495,8758],q 0 [12293,20568,16478],q 0 [20492,16689],q 0 [8197,20492,16689],q 1 [20492,16689],q 2 [20492,16689],q 4 [20492],q 10 [20492,16689],q 0 [20495],q 0 [12293,20495,16474],q 1 [20495,16474],q 2 [20495],q 0 [8197,20494,82483],q 1 [20494,82483],q 2 [20494,82483],q 0 [8197,12370,20498],q 1 [12370,20498],q 2 [12370,20498],q 0 [12297,20498,49449],q 1 [12297,20498,49449],q 2 [20498,49449],q 0 [8197,16396,1003602],q 1 [16396,1003602],q 2 [16396,1003602],q 0 [12297,20528,16510],q 0 [8197,12370,20499],q 1 [12370,20499],q 2 [12370,20499],q 0 [12295,20655],q 0 [12295,20655,20491],q 1 [20655],q 1 [20655,20491],q 5 [12295],q 4 [12295,20655],q 0 [12293,12297,20497],q 1 [12297,20497],q 0 [12293,16474,20496],q 1 [16474,20496],q 2 [12293,16474,20496],q 3 [16474,20496],q 0 [12293,16393,20568],q 1 [16393,20568],q 0 [12293,20498,90411],q 3 [20498,90411],q 0 [8197,16466,13425],q 0 [12293,20497,155663],q 2 [12293,20497,155663],q 4 [155663],q 0 [12297,20528,126983],q 0 [8197,16466,21619],q 1 [16466,21619],q 10 [21619],q 2 [16466,21619],q 4 [8197,21619],q 0 [12297,16433],q 0 [20487,12297,16433],q 5 [12297,16433],q 2 [16433],q 2 [20487,16433],q 0 [8197,20493,315472],q 1 [20493,315472],q 2 [20493,315472],q 10 [20493],q 12 [20487],q 0 [20487,12297,16434],q 2 [20487,16434],q 0 [12295,16393,98479],q 1 [16393,98479],q 2 [12295,98479],q 0 [8197,16399],q 3 [8197,593],q 0 [12293,12297,16432],q 2 [12293,16432],q 3 [16432],q 0 [8197,20497,155663],q 4 [8197,155663],q 0 [20491,12906,17001],q 1 [20491,12906],q 10 [20491,12906],q 7 [114699],q 0 [16389,114699,20491],q 1 [12297,20531,17041],q 0 [8197,20492,311378],q 1 [20492,311378],q 2 [20492,311378],q 7 [8197,311378],q 10 [20492],q 0 [8197,20495,16949],q 0 [12293,20496,24589],q 1 [20496,24589],q 0 [12293,12297,16434],q 2 [12293,16434],q 0 [16391,13409,1339403],q 1 [13409,1339403],q 2 [16391,13409],q 0 [12293,20568,94219],q 0 [12293,90123,20498],q 1 [90123],q 1 [90123,20498],q 0 [8197,20496,24585],q 0 [8197,20496,20497],q 0 [20496,24589,1069067],q 1 [20496,24589,1069067],q 2 [12293,20495,20568],q 1 [16474,20859],q 3 [16474,20859],q 0 [8197,20497,155728],q 1 [20497,155728],q 2 [20497,155728],q 4 [8197,155728],q 0 [12297,49157,53263],q 1 [12297,53263],q 2 [49157,53263],q 0 [16393,20492,98611],q 1 [16393,20492,98611],q 0 [12293,90123],q 0 [12293,90123,20499],q 1 [90123,20499],q 0 [12293,12297,20568],q 1 [12297,20568],q 2 [16432],q 0 [12295,12297,16432],q 0 [20492,16689,1298443],q 1 [20492,16689,1298443],q 0 [12297,16397,20528],q 1 [12297,16397,20528],q 2 [16397,20528],q 0 [12295,12297],q 0 [12295,12297,16434],q 0 [8197,20498,82219],q 1 [20498,82219],q 2 [20498,82219],q 0 [12295,12297,20528],q 3 [20530],q 0 [12295,12297,20530],q 0 [12295,12297,20499],q 0 [20498,12585,1368075],q 1 [20498,12585,1368075],q 2 [20498,12585],q 0 [12295,8365,20496],q 1 [8365,20496],q 10 [16397,651275],q 0 [20487,16397,651275],q 2 [20487,16397],q 0 [12295,12297,20497],q 0 [12293,12297,20499],q 2 [12293,20499],q 0 [8197,20492,311305],q 0 [12295,12297,20498],q 0 [12295,20489,1167535],q 1 [20489,1167535],q 10 [20489],q 2 [12295,1167535],q 3 [20489],q 0 [12295,20491,176745],q 1 [20491,176745],q 2 [12295,176745],q 7 [12295,176745],q 0 [12295,20496,24749],q 1 [20496,24749],q 0 [20487,12965,16393],q 1 [12965,16393],q 2 [20487,12965],q 4 [20487,12965],q 7 [12965],q 2 [12295,20496,24577],q 13 [12295],q 0 [8197,16397,651344],q 1 [16397,651344],q 2 [16397,651344],q 4 [8197,651344],q 3 [8197,651344],q 0 [12295,20496,24589],q 0 [20487,16393,98983],q 1 [16393,98983],q 2 [20487,98983],q 2 [20496,24626],q 0 [12295,20496,20497],q 8 [12295],q 2 [16434],q 0 [12297,20495,16434],q 2 [20495,16434],q 0 [12299,20496,20497],q 5 [12299],q 0 [12295,20498,176425],q 1 [20498,176425],q 2 [12295,20498,176425],q 0 [12295,20498,20499],q 0 [12297,16435,13157],q 1 [12297,16435,13157],q 2 [16435,13157],q 0 [16389,12297,114739],q 1 [12297,114739],q 2 [16389,114739],q 0 [16389,12297,20531],q 0 [16389,114699,21780],q 1 [114699,21780],q 2 [16389,21780],q 10 [21780],q 0 [16391,12299,1147101],q 1 [12299,1147101],q 2 [16391,1147101],q 3 [16391],q 0 [12297,49157,20534],q 1 [12297,20534],q 2 [49157,20534],q 3 [49157,20534],q 0 [12297,49159,20530],q 2 [49159,20530],q 3 [49159],q 0 [16389,12297,20592],q 1 [12297,20592],q 0 [16389,114703,21691],q 1 [114703,21691],q 2 [16389,114703,21691],q 0 [12297,20496,24585],q 1 [12297,20496,24585],q 3 [20496,24585],q 5 [12297,24585],q 0 [20485,12297,1425456],q 1 [12297,1425456],q 2 [20485,1425456],q 3 [20485,1425456],q 0 [16389,12299,20592],q 16 [20495],q 0 [16389,114699],q 0 [16389,114699,20495],q 3 [16389,114699],q 0 [16389,20491,12905],q 1 [20491,12905],q 2 [16389,12905],q 0 [16389,20491,115307],q 1 [20491,115307],q 2 [16389,115307],q 0 [16389,114703,9401],q 1 [114703,9401],q 2 [16389,114703],q 0 [20487,17061,12297],q 1 [17061,12297],q 2 [20487,17061],q 3 [20487,17061],q 4 [20487],q 0 [20495,8757],q 0 [20487,20495,8757],q 5 [8757],q 2 [20487,20495],q 10 [20495,8757],q 0 [16389,114703,20495],q 2 [16389,114703,20495],q 0 [12293,12297,20496],q 10 [12297,20496],q 0 [16389,20492,311305],q 2 [16389,20492],q 0 [20495,4662,16949],q 0 [16389,20495,8757],q 1 [20495,8757],q 2 [16389,20495],q 0 [8197,20560],q 0 [8197,20560,16398],q 1 [20560],q 2 [20560,16398],q 0 [16389,20592,196621],q 7 [196621],q 0 [16389,20592,196622],q 7 [196622],q 2 [49157,20528],q 0 [16391,9313,13697],q 1 [9313,13697],q 2 [16391,13697],q 4 [13697],q 7 [13697],q 0 [8197,20498,20499],q 0 [20498,8489,13382],q 1 [20498,8489,13382],q 0 [20485,12297,1425459],q 1 [12297,1425459],q 0 [20487,12965,20495],q 1 [12965,20495],q 2 [20487,12965,20495],q 0 [12293,12299,20499],q 1 [12299,20499],q 10 [12299,20499],q 0 [20485,12299,1425631],q 1 [12299,1425631],q 2 [20485,1425631],q 0 [12299,16605],q 0 [20487,12299,16605],q 5 [12299,16605],q 2 [16605],q 2 [20487,16605],q 10 [12299,16605],q 0 [20485,1425423,9621],q 1 [1425423,9621],q 2 [20485,1425423],q 3 [20531],q 0 [20487,8869,20491],q 1 [8869,20491],q 2 [20487],q 5 [8869],q 0 [16396,16397,651275],q 1 [16396,16397,651275],q 15 [651275],q 0 [20487,8869,13725],q 1 [8869,13725],q 10 [13725],q 2 [20487,13725],q 0 [12297,49159,20528],q 0 [20491,12906,12907],q 1 [20491,12906,12907],q 2 [12906,12907],q 0 [20487,8869,16397],q 1 [8869,16397],q 7 [8869],q 16 [16397],q 3 [20487,8869],q 0 [12297,16433,20528],q 1 [12297,16433],q 10 [12297,16433],q 1 [12297,16433,20528],q 2 [16433,20528],q 0 [12295,20497,155823],q 1 [20497,155823],q 2 [12295,20497,155823],q 0 [20487,8869],q 0 [20487,8869,20495],q 1 [8869],q 1 [8869,20495],q 4 [20487,8869],q 0 [12295,12297,20496],q 0 [20487,12297,20528],q 2 [20487,20528],q 0 [20487,12965,1273867],q 1 [12965,1273867],q 10 [1273867],q 3 [20485,1425419],q 0 [20485,12299,1425419],q 1 [12299,1425419],q 4 [20485,1425419],q 0 [20487,12965],q 0 [20487,12965,20491],q 1 [12965],q 1 [12965,20491],q 5 [12965],q 0 [20487,17061,696331],q 1 [17061,696331],q 0 [20487],q 0 [20487,12297,20531],q 0 [16393,98319,21508],q 1 [16393,98319,21508],q 0 [12297,20528,20529],q 1 [12297,20528,20529],q 2 [20528,20529],q 0 [12299,20703],q 0 [20487,12299,20703],q 2 [20703],q 2 [20487,20703],q 10 [12299,20703],q 0 [20491,12904,8937],q 1 [20491,12904,8937],q 2 [12904],q 10 [16393,98319],q 0 [20487,16393,98319],q 0 [12297,49157,16434],q 2 [49157,16434],q 0 [20497,155659,12515],q 0 [12297,49159],q 2 [49159,20496],q 0 [16398,8629],q 0 [20487,16398,8629],q 2 [20487,16398],q 0 [20487,20492,311305],q 5 [311305],q 2 [20487,20492],q 0 [12297,20497],q 2 [49157,20497],q 0 [20487,16397,651943],q 1 [16397,651943],q 2 [20487,16397,651943],q 0 [12297,20499],q 2 [49157,20499],q 0 [12297,16432],q 0 [12297,49159,16432],q 0 [12297,20529,811024],q 1 [12297,20529,811024],q 2 [20529,811024],q 0 [12297,20529,811023],q 1 [12297,20529,811023],q 0 [12297,49159,16434],q 2 [49159,16434],q 2 [49159,20497],q 0 [12297,20529,811015],q 2 [20529,811015],q 3 [20529,811015],q 0 [12297,16397,21116],q 1 [12297,16399,593],q 0 [12297,16399],q 0 [12297,20493,20528],q 1 [12297,20493,20528],q 2 [20493,20528],q 0 [20498,12585],q 1 [20498,12585],q 0 [20498,8489],q 0 [20497,155660],q 0 [20495,16950],q 1 [20495,16950],q 0 [20495,4662],q 0 [20495,4661],q 2 [20495,4661],q 0 [20494,4657],q 2 [20494,4657],q 0 [20492,20493],q 0 [16399,8785],q 1 [16399,8785],q 2 [16399],q 3 [593],q 0 [16397,21119],q 1 [16397,21119],q 0 [16397,20495],q 1 [16397,20495],q 0 [16397,651275],q 1 [16397,651275],q 0 [16397,651271],q 4 [651271],q 7 [651271],q 0 [8197],q 0 [8197,16398],q 1 [16398],q 5 [16398],q 4 [8629],q 0 [16393,98316],q 1 [16393,98316],q 2 [98316],q 0 [16389,12299],q 0 [16396,1003529],q 1 [16396,1003529],q 2 [16396],q 0 [12295,20498],q 0 [12295,20497],q 0 [16389,20492],q 1 [20492],q 0 [20489],q 0 [12295,20489],q 1 [20489],q 0 [16398,16821],q 1 [16398,16821],q 0 [16389,12297],q 0 [12295,16395],q 1 [16395],q 0 [16393,98311],q 2 [98311],q 15 [],q 0 [12295,16393],q 0 [16391,13409],q 1 [13409],q 0 [8197,20499],q 1 [20499],q 0 [16391,9313],q 1 [9313],q 2 [16391],q 0 [20485,12297],q 2 [20485],q 3 [20485],q 0 [20487,12297],q 0 [12299,20496],q 0 [16396,1003525],q 2 [16396,1003525],q 0 [12293,20499],q 0 [16393,20495],q 1 [16393,20495],q 0 [12293,20497],q 0 [8197,20497],q 0 [20496,24589],q 5 [24589],q 0 [16395,13437],q 1 [16395,13437],q 2 [13437],q 0 [12293,20491],q 0 [20491,16397],q 1 [20491,16397],q 5 [16397],q 0 [12293,16474],q 0 [8197,20496],q 0 [20487,17061],q 1 [17061],q 5 [17061],q 0 [12293,20496],q 0 [8197,20495],q 0 [20485,1425419],q 1 [1425419],q 0 [12293,16395],q 10 [16395],q 0 [20485],q 0 [20485,12299],q 0 [12297,16434],q 0 [12299,20498],q 0 [12293,16397],q 2 [12293,16397],q 0 [12293,20495],q 2 [12293,20495],q 0 [8197,20494],q 1 [20494],q 2 [20494],q 10 [20494],q 0 [8197,20492],q 0 [20491,12907],q 2 [12907],q 0 [16389,20495],q 0 [12299],q 0 [12299,20499],q 1 [16399],q 1 [20491,12904],q 0 [8197,16397],q 0 [12293,16393],q 0 [8197,16396],q 1 [16396],q 10 [16396],q 2 [20560],q 0 [20487,16397],q 0 [12293,20498],q 0 [12295],q 0 [12295,20499],q 0 [20489,1167375],q 1 [20489,1167375],q 2 [1167375],q 0 [12295,20496],q 0 [8197,16466],q 1 [16466],q 2 [16466],q 0 [8197,20498],q 0 [20496,24585],q 0 [20487,16398],q 0 [20492,20787],q 1 [20492,20787],q 0 [20495,8758],q 1 [20495,8758],q 2 [16435],q 0 [12297,20530],q 2 [20530],q 0 [20494,8753],q 1 [20494,8753],q 0 [16391,12297],q 0 [20485,1425423],q 1 [1425423],q 0 [12293,20493],q 1 [20493],q 2 [12293,20493],q 4 [20493],q 1 [114699],q 4 [114699],q 0 [8197,20493],q 2 [20493],q 0 [20487,12299],q 0 [20487,16393],q 0 [16393,20579],q 2 [20579],q 0 [20487,20491],q 0 [16391,12299],q 5 [16391],q 2 [17001],q 5 [17001],q 0 [20487,20492],q 0 [20487,20495],q 0 [12297,20493],q 1 [12297,20493],q 2 [20531],q 0 [16389,20491],q 0 [16393,98319],q 1 [16393,98319],q 2 [98319],q 0 [12297,20495],q 1 [12297,20495],q 0 [20497,155655],q 0 [12297,20529],q 1 [12297,20529],q 2 [20529],q 0 [12297,16397],q 1 [12297,16397],q 0 [8197,12370],q 1 [12370],q 2 [12370],q 1 [12299,16605],q 0 [12299,20497],q 0 [20493,315403],q 1 [20493,315403],q 0 [16393,20492],q 1 [16393,20492],q 12 [20492],q 0 [20491,20495],q 1 [20491,20495],q 0 [12293,20489],q 4 [20576],q 0 [16389,114703],q 1 [114703],q 0 [20489,1167367],q 2 [1167367],q 0 [20491,20492],q 1 [20491,20492],q 0 [20491,4713],q 5 [4713],q 2 [4713],q 0 [20491,4714],q 2 [4714],q 0 [20491,12906],q 7 [12906],q 0 [20491,17002],q 1 [20491,17002],q 0 [20498],q 0 [20499],q 0 [20494],q 0 [20493],q 0 [16398],q 0 [16391],q 0 [16396],q 0 [16395]]
def B_23_4 : BT (List (List Nat)) := BT.empty
lemma B_23_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 4 xs.toFinset) B_23_4 := .empty
def U_23_5 : List Nat := (r 0 7)
def P_23_5 : BT (Option BoundPool) := buildPoolsSubBT 11 W_23 r_23 S_23 ps_23 U_23_5
def N_23_5 : List NodeSpec := [([1,3,9,11,4,7],[],[]),([17,0,1,2,3,12],[0,1,2],[]),([18,1,2,3,19,5],[],[]),([21,1,9,4,7,5],[],[]),([1,3,26,27,4,5],[],[]),([33,0,1,2,3,5],[],[]),([35,0,1,2,3,5],[],[]),([36,0,1,2,3,37],[],[]),([39,40,0,1,3,12],[3,4],[]),([0,1,3,27,41,34],[],[]),([42,0,1,3,4,5],[],[]),([39,0,1,44,2,12],[5],[]),([47,1,2,3,14,4],[],[]),([0,1,31,4,49,50],[],[]),([39,21,0,1,2,12],[3,4],[]),([52,0,1,2,3,12],[6],[]),([18,1,2,3,14,7],[],[]),([18,1,2,3,14,53],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_5 : checkNodesBT W_23 g_23 F_23 P_23_5 A_23 B_23_4 5 N_23_5 = true := by decide +kernel
def B_23_5 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_5
set_option maxRecDepth 500000 in
lemma B_23_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 5 xs.toFinset) B_23_5 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok (buildPoolsSubBT_sound S_23_ok) A_23_ok B_23_4_ok C_23_5
def U_23_6 : List Nat := ([3,4,5]++r 7 133)
def P_23_6 : BT (Option BoundPool) := buildPoolsSubBT 11 W_23 r_23 S_23 ps_23 U_23_6
def N_23_6 : List NodeSpec := [([54,1,3,9,4,7,5],[7],[]),([0,1,58,4,5],(r 8 5),[]),([61,0,1,3,59,4,5],[13,14],[]),([62,0,1,64,2,3,4],[14],[]),([62,65,1,2,3,4,5],[],[]),([1,2,3,67,4,7,5],[15,16,17],[]),([1,68,3,12,4,7,5],[15,18],[]),([1,3,9,10,4,7,5],([7]++r 18 4),[0]),([0,1,2,3,31,69,32],[],[]),([1,2,71,12,4,7,5],[21,22],[]),([39,72,0,1,2,3,12],[3,23,24,25],[]),([73,0,1,2,3,12,75],(r 26 4),[]),([39,0,1,2,3,12,13],[4,20,23,26,30,31],[0]),([51,0,1,2,3,12,38],[32],[0]),([79,80,78,0,1,2,4],(r 33 5),[]),([0,1,2,3,59,14,4],[14,38,39],[]),([81,1,2,3,12,14,4],[40,41,42],[]),([1,2,3,12,14,4,7],[15,43,44,45],[0]),([62,82,0,1,2,3,5],[],[]),([82,0,1,2,3,83,5],[],[]),([82,85,0,1,2,3,5],[20,46],[]),([82,0,1,2,3,86,5],[],[]),([18,51,0,1,2,3,5],[47],[]),([18,1,2,3,13,7,5],[47,48,49],[0]),([18,73,0,1,2,3,14],[50],[]),([1,2,3,12,19,4,5],[15,51,52,53],[0]),([18,0,1,2,3,14,6],[10,36,54],[0]),([18,36,0,1,2,3,14],[55],[0]),([0,1,2,3,87,14,4],[38,45],[]),([1,2,3,12,14,53,4],[45,56,57,58],[0]),([0,1,2,3,14,4,69],[14,38,59,60],[]),([36,0,1,2,3,45,14],[],[]),([88,0,1,2,59,4,5],[14,61],[]),([89,0,1,2,3,14,4],[],[]),([74,73,21,0,1,2,12],[28,62],[0]),([21,0,1,2,59,4,5],[14,61],[]),([21,1,2,12,4,7,5],[15,22],[]),([18,0,1,2,3,15,14],[10,36,54],[0]),([90,1,2,3,83,4,5],[],[]),([62,0,1,2,3,14,4],[14,38,59,63],[]),([62,90,1,2,3,4,5],[],[]),([0,1,3,23,27,4,41],[64],[0]),([40,0,1,3,59,4,5],[14,61],[]),([0,1,2,3,12,91,6],[65,66,67],[0]),([21,92,1,2,4,7,5],[15,68],[]),([93,0,1,2,96,3,4],[36],[]),([97,1,2,3,4,7,5],[],[]),([100,0,1,2,98,4,5],[36,69],[]),([0,1,3,27,24,34,5],[70,71],[0]),([102,1,2,3,4,7,5],[],[]),([39,0,1,2,22,12],[5,23,24,72,73,74],[]),([93,18,0,1,2,3,5],[],[]),([93,18,0,1,2,12,5],[],[]),([40,0,1,3,83,4,5],[],[]),([103,0,1,98,12,4,5],[75],[]),([0,1,2,3,23,41,34],[76],[0]),([0,1,2,3,14,37,4],[77],[0]),([40,104,1,3,12,4,5],[78,79],[]),([0,1,2,3,12,15,16],[80,81,82],[0]),([105,0,1,2,31,4,48],[10,36],[]),([39,40,0,1,2,3],([3,4,74]++r 83 5),[0]),([0,1,2,3,23,106,34],[],[]),([39,21,0,1,2,3],([3,4,84,86]++r 88 4),[]),([74,73,40,0,1,3,12],[28,62],[0]),([0,1,2,108,4,110,5],[],[]),([40,0,1,3,12,6,38],[66,92],[0]),e6 [111] [93],([39,55,0,1,2,22],[5,74,86,94,95,96],[]),([113,1,2,3,23,4,5],[],[]),([18,1,2,22,12,7,5],[97,98],[]),([18,72,1,2,3,7,5],[],[]),([0,1,44,2,12,6,38],[99],[0]),([1,20,3,9,4,7,5],[18,21,100,101],[0]),([0,1,2,3,83,14,4],[],[]),([0,1,114,2,98,4,5],[69,102],[]),([115,1,2,3,4,7,5],[100,103],[]),([0,1,117,4,5],[36,104,105,106],[]),([39,43,0,1,2,12],[3,5,23,107,108],[0]),([0,1,2,3,30,32,5],[20,109],[0]),([21,104,1,2,12,4,5],[78,79],[]),([118,0,1,2,3,31,4],[110],[]),([94,62,0,1,2,3,5],[],[]),([1,44,2,12,4,7,5],[18],[]),([40,119,1,3,4,7,5],[15,68],[]),([104,1,2,3,12,14,4],[79,111,112],[]),([40,1,3,12,4,7,5],[15,22],[]),e6 [120] [113],([0,1,2,3,25,34,5],[20,70],[0]),([121,0,1,2,3,23,4],[110],[]),([39,0,1,2,3,22,12],[3,4,5,23],[0]),([0,1,2,3,23,4,123],[14,36,114,115],[]),([124,0,1,2,3,14,4],[],[]),e6 [125] [],([36,126,0,1,2,3,12],[116,117,118],[0]),([0,1,12,4,49,50,5],[119,120],[0]),([0,1,2,23,4,41,127],[121,122],[]),([128,0,1,2,23,4,41],[10,123],[]),([0,1,2,96,3,4,106],[36],[]),([0,1,3,31,4,48,49],[36],[0]),([21,1,2,8,4,7,5],[15,68],[0]),([1,129,2,3,4,7,5],[124],[]),([21,0,1,2,12,6,38],[66,92],[0]),([130,93,0,1,12,4,5],[75],[]),([104,1,44,2,12,4,5],[125],[]),([93,132,1,2,3,4,5],[],[]),([39,0,1,2,133,3],[5,126,127,128],[]),([0,1,44,2,59,4,5],[129],[]),([74,73,0,1,44,2,12],[130],[0]),([0,1,3,25,27,4,5],[71],[0]),([0,1,134,2,59,4,5],[13],[]),([0,1,2,3,14,46,4],[14,38,45,59,60,131],[0]),([0,1,2,3,31,48,32],[132,133],[]),([1,2,3,23,26,4,5],[20,134,135],[0]),([0,1,2,31,4,48,50],[136],[0]),([1,2,3,31,135,4,5],[20,137,138,139],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_6 : checkNodesBT W_23 g_23 F_23 P_23_6 A_23 B_23_5 6 N_23_6 = true := by decide +kernel
def B_23_6 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_6
set_option maxRecDepth 500000 in
lemma B_23_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 6 xs.toFinset) B_23_6 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok (buildPoolsSubBT_sound S_23_ok) A_23_ok B_23_5_ok C_23_6
def U_23_7 : List Nat := ([3,4,5,7,10]++r 13 11++[26,28,30]++r 33 6++[45,46,47,49,50,54]++r 59 4++[64,66]++r 68 4++[73,74,75,78,79,83,86,88,92,94]++r 97 6++[107,109,110,114,115,119,120,121,123,125,127]++r 129 4++r 140 550)
def P_23_7 : BT (Option BoundPool) := buildPoolsSubBT 11 W_23 r_23 S_23 ps_23 U_23_7
def N_23_7_0 : List NodeSpec := [([56,0,137,3,4,5],(r 140 5),[]),([138,0,1,136,4,5],[36,145,146,147],[0]),([1,3,9,4,7,5],[7,18,19,20,101,148,149],[0]),([2,3,139,4,7,5],([15,18]++r 150 5),[]),([1,2,3,71,4,7,5],[15,21,100,155,156],[]),([1,2,3,101,4,7,5],[15,21,22,157,158],[0]),([143,141,0,1,2,4],([10]++r 159 5),[]),([79,141,78,0,1,2,4],([10]++r 164 7),[]),([80,141,78,0,1,2,4],[10,165,167,168,171,172],[]),([78,0,1,2,144,4],[164,168,169,173,174],[]),([56,1,145,3,4,5],[143,144,175,176],[]),([78,0,1,146,2,4],[10,167,168,169,177,178],[]),([79,78,0,1,2,4],(r 33 4++[169]++r 179 4),[0]),([78,0,1,147,2,4],[35,36,169,181,183,184],[]),([149,1,2,151,3,4,5],([10]++r 185 5),[]),([0,1,2,153,3,4,110],[169,190,191],[]),e6 [155,156] [14,36,75,192,193],e6 [157,153] [14,194,195],e6 [153,158] [14,196],e6 [162,160] [36,75,197,198],e6 [161,163] [36,199,200,201],([124,154,0,1,2,3,31,4],[144,202,203],[]),e6 [166,41] [10,129,204,205],([55,0,1,57,4,5],[143,144,206,207],[0]),e6 [167,83] [14,194,208],e6 [168,59] [194,209,210,211],u6 [59,60] ([14,20]++r 211 5),u6 [62,63] ([14]++r 216 4),([142,78,0,1,2,4],[10,163,165,167,168,220],[]),e6 [171] ([16,75,129]++r 221 5),([104,1,2,133,3,4,5],([125,127]++r 226 4),[]),([0,1,2,133,3,6,38],([99]++r 230 4),[0]),([74,73,21,0,1,2,3],([28,62,88]++r 234 6),[0]),([18,0,1,2,3,22,6,5],[10,20,218,240,241,242],[0]),u6 [93,131] ([36]++r 243 4),([40,0,1,3,12,6,4,5],([10,36]++r 246 4),[0]),([1,2,133,3,4,7,5],[16,18,21,127,231,250,251,252],[]),([172,0,1,2,3,23,34,5],[70],[0]),e6 [173,23] [16,36,70,248,253],([55,1,2,22,4,7,5],([18,100]++r 254 4),[]),e6 [172,27] [36,71,258,259,260],e6 [174,31] (r 261 5),([94,1,2,3,7,5],([17,20]++r 266 5),[]),([40,104,1,2,3,4,5],([78,79,83,229]++r 271 4),[0]),([21,0,1,2,3,6,38],([16,66,92,234]++r 275 6),[0]),e6 [72,32] [109,132,281,282],([1,2,68,3,4,7,5],([15,18,252]++r 283 4),[0]),([73,0,1,44,2,12,4,5],[287],[0]),([124,0,1,2,22,12,4,5],(r 288 4),[]),([164,78,0,1,2,4],[10,164,165,167,168,292,293,294],[]),([74,90,1,2,3,12,4,5],[10,20,295,296],[0]),e6 [154,176] [14,248,297],e6 [176] ([129,194]++r 297 4),e6 [177,23] [14,36,115,260,301,302],e6 [178,41] [14,115,303],([0,1,2,3,31,28,32,5],[16,132,304],[0]),e6 [178] ([16,75,110,129,194]++r 305 4),([128,0,1,2,22,4,41,5],[10,123,144,309,310],[0]),([0,1,2,3,23,4,41,24],([10,36,115]++r 311 4),[]),([74,0,1,44,2,12,4,5],[315],[0]),([40,0,1,3,12,4,5,38],[10,36,248,249,316,317],[0]),u6 [98,99] ([20,36,314]++r 317 4),([0,1,2,3,23,4,41],[10,14,36,115,270,312,313,321,322],[0]),([1,2,3,9,4,7,5],([7,15]++r 17 4++[101,148,149,323]),[0]),u6 [122,23] [36,115,144,324,325],u6 [23,112] [10,14,144,301,314,326,327],([0,1,44,2,12,6,4,5],[10,36,328,329],[0]),e6 [106,179] [36,330],([82,0,1,2,3,45,5],(r 331 7),[]),e6 [124,180] [14,263,282,338],u6 [103,98] [36,69,75,102,320,339,340],u6 [49,50] [10,36,119,120,341],([0,1,2,3,12,13,6,38],[20,66,218,342,343,344],[0]),u6 [25,23] [70,115,301,326,327,345,346],e6 [181,34] [70,115,258,347,348],e6 [182,23] [16,64,115,349],([183,141,0,1,2,4],[10,294,350,351,352],[]),([43,0,1,2,12,4,69,5],[10,129,169],[]),([73,0,1,2,3,12,14,4],[10,336,353,354,355],[0]),([0,1,2,22,59,12,4,5],[13,61,129,210,211,288,289,356],[]),([154,0,1,2,3,31,4,32],[144,169],[]),e6 [184,31] [10,14,215],([0,1,3,23,27,4,24,5],[36,64,75],[0]),([55,0,1,2,4,48,50,5],[114,119],[]),([18,73,0,1,2,22,12,5],[73,242,357,358,359],[]),e6 [184,12] [14,360,361,362],([40,0,1,2,3,6,38],([16,66,92,275,277]++r 363 5),[0]),u6 [30,31] ([109,261,265]++r 368 4),([93,55,0,1,2,4,5],[75,94,243,372,373],[]),e6 [125,48] [10,14,374],([21,0,1,2,12,4,5,38],[10,36,289,316,317],[0]),([104,1,2,22,12,4,5],[125,274,375,376,377],[]),([74,21,0,1,2,12,4,5],[378,379],[0]),([0,1,2,22,12,6,38],[99,343,357,367,380,381,382],[0]),e6 [185,31] [16,115,383,384],u6 [22,59] [13,14,61,114,211,356],([82,0,1,2,3,12,6,5],[10,16,20,36,46,215,334,385,386],[0]),([172,0,1,2,3,23,4,106],[114,115,270,326,387],[0]),([43,0,1,2,12,6,38],[92,99,343,388,389,390],[0]),([0,1,2,22,4,41,127,5],[121,129,144,391],[0]),([0,1,188,2,4,5],[36,144,392,393,394],[]),e6 [165,127] [10,121,309,395],([39,0,1,2,3,22],[4,5,74,86,270,396],[0]),([0,1,20,3,4,160,163,5],[10,169,199,397],[]),([94,0,1,2,3,12,6,5],[10,20,245,398,399,400],[0]),([93,0,1,2,12,4,5],[73,75,144,243,372,401,402],[0]),([0,1,2,3,45,14,4],[10,38,45,59,60,403,404,405],[0]),([39,0,1,2,20,3],[3,4,5,86,406,407],[0]),([0,1,2,187,31,4],[10,144,408,409,410],[]),([1,2,3,12,13,4,7,5],[15,20,334,411,412,413],[0]),([62,43,0,1,2,4,5],[194,216,414],[]),e6 [189] [10,16,50,75,129,194,248,336,415,416,417],u6 [12,75] [16,289,379,418,419],u6 [22,83] [14,114,208,356,420],([62,43,0,1,2,12,4,5],[10,129],[]),e6 [190,31] [194,215,265,421,422,423],([0,1,2,22,83,12,4,5],[208,288,289,420],[]),([72,1,2,3,12,4,7,5],[22,411,424,425,426],[0]),([92,1,2,20,3,4,7,5],[15,20,21,427,428],[0]),([0,1,107,3,191,4],([10,36]++r 429 6),[]),e6 [192,62] [14,194,216,435],([73,40,0,1,3,12,4,5],[354,436],[0]),([1,2,20,8,3,4,7,5],[15,18,21,22,68,428,437],[0]),([0,1,2,3,23,31,4],[73,263,438,439,440],[]),e6 [178,24] [14,308,360],([43,0,1,2,59,4,5],[13,61,211,389,441],[0]),([0,1,152,107,3,4,5],([169,431]++r 442 4),[]),u6 [83,13] [114,215,218,446],([74,73,55,0,1,2,22],([94,130,237]++r 447 4),[0]),u6 [94,31] [73,115,144,263,400],e6 [193,32] [109,132,282,451,452],e6 [194,48] [10,14,36,129,453,454],([0,1,2,3,23,4,106],[14,71,114,115,270,455,456],[0]),([21,104,1,2,3,4,5],[78,79,88,229,272,457,458,459],[]),e6 [197,196] [10,14,194],([18,43,0,1,2,12,6,5],[10,20,36],[]),([199,0,1,2,3,31,4],[10,26,215,263,460,461],[]),e6 [200,69] [14,20,194,462,463,464],([0,1,2,76,108,4],[10,431,465],[]),([74,73,0,1,2,22,12],[73,130,381,449,466,467,468],[0]),([0,1,44,2,12,4,5,38],[10,36,289,328,469,470],[0]),([55,0,1,2,98,4,5],[69,94,102,320,471,472],[0]),([40,1,2,3,4,7,5],[15,16,21,22,68,83,100,255,365,473],[0]),([0,1,2,3,12,15,14,4],[10,36,45,131,289,474,475,476],[0]),u6 [13,69] [14,20,114,288,336,462,463,477,478],u6 [201,110] [14,36,129],([154,0,1,3,23,27,4,5],[71],[]),([0,1,107,3,191,4,5],([10]++r 429 6++[479]),[]),([74,40,0,1,3,12,4,5],[10,378,379],[0]),e6 [69,202] [14,480],([0,1,2,22,12,4,32,5],[73,132,144,169,304,356,481],[]),u6 [130,93] [36,75,243,482],([0,1,2,98,12,4,5],[102,144,320,357,483,484,485],[0]),([0,1,2,22,59,4,5],[13,210,211,357,486,487],[]),([39,0,1,2,3,12],[3,4,5,23,26,30],[0]),e6 [196,203] [14,488],e6 [205,204] [36,75,489],e6 [98,12] [36,75,102,144,317,484],e6 [204,12] [144,288,379,489,490],([55,0,1,2,22,6,38],[99,277,367,447,491,492,493],[0]),e6 [172,181] [16,36,70,115,260],([0,1,2,22,12,4,69,5],[73,144,169,289,356,480,494],[]),([62,0,1,2,22,4,5],[194,216,435,495],[]),([39,55,0,1,2,3],[3,4,5,86,496,497,498],[0]),([104,1,2,3,12,13,4,5],([79,335,375]++r 499 4),[0]),([40,0,1,3,31,4,5],[10,356,503,504],[]),u6 [62,22] [14,114,194,216,218,414,495],([80,78,0,1,2,4],(r 34 4++[169,172,179,181,505]),[0]),([104,1,2,3,22,12,4,5],[78,79,125,375],[0]),([74,73,40,0,1,2,3],[28,62,83,235,237,365,449,506,507],[0]),([84,0,1,2,3,14,4],[10,38,45,59,60,131,336,508,509,510],[]),([109,0,1,2,108,4,5],[10,431,511,512],[]),e6 [206,23] [71,513,514],e6 [207,12] ([14]++r 515 4),u6 [18,23] [71,73,114,115,242],e6 [124,193] [14,16,109,115,338],([43,104,1,2,12,4,5],[78,125,226,375,519],[0]),u6 [27,34] [36,70,71,115,253,520,521],e6 [23,31] [71,263,357,438],([84,90,1,2,3,4,5],([10,68,295]++r 522 7),[]),([18,0,1,2,22,12,6,5],[36,529,530],[0]),([181,0,1,3,23,27,4,5],[71,248],[]),([1,2,22,12,4,7,5],[18,255,381,411,424,531,532],[0]),([119,1,2,3,22,4,7,5],[15,20,21,22,100,255,533,534],[0]),([0,1,2,3,31,4,48],[10,26,36,115,265,535,536],[0]),([55,104,1,2,22,4,5],[125,272,274,537,538],[]),([74,73,0,1,2,3,22,12],[28,62,130,467],[0]),u6 [93,12] [36,75,144,243,245,288,372,401],([43,0,1,2,59,12,4,5],[10,13,129],[0]),([0,1,2,3,12,14,6,4],[10,36,45,131,246,289,335,539,540],[0]),e6 [208,23] [14,115,314],([43,0,1,2,83,12,4,5],[],[]),([70,1,2,3,12,4,7,5],[20,21,218,541],[0]),([74,73,43,0,1,2,12],[62,107,130,388,467,542],[0]),e6 [41,209] [129],e6 [18,210] [10,543],e6 [12,106] [36,115,144,330,544],([43,0,1,2,4,41,127,5],[144,395],[]),([39,43,0,1,2,3],[3,5,86,496,545,546],[0]),([0,1,2,3,12,14,4,16],[10,36,50,131,289,547,548,549],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_7_0 : checkNodesBT W_23 g_23 F_23 P_23_7 A_23 B_23_6 7 N_23_7_0 = true := by decide +kernel
def N_23_7_1 : List NodeSpec := [([90,1,2,3,45,4,5],([10,68,295,527,528]++r 550 5),[]),e6 [82,31] [115,336],u6 [30,12] [129,288,499,555,556,557],u6 [118,12] [14,360,558,559,560],u6 [29,31] [215,265,335,360,561,562,563],u6 [48,211] [14,20,374,453,564,565],([18,0,1,2,3,13,6,5],[10,20,36,218,241,242,566,567],[0]),([0,1,2,3,31,12,4,48],[10,36,265,335,374,536],[]),([0,1,2,12,4,48,50,5],[114,129,568],[0]),([105,0,1,2,12,4,48,5],[10,36,114,120,289,569],[0]),([18,149,1,2,3,5],[10,26,47,570,571,572],[]),e6 [125] ([16,75,110,129,194]++r 573 5),e6 [125,12] [75,114,129,575,577],e6 [48,212] [129],e6 [213,48] [36,248,374,569],e6 [171,12] [115,129,222,224],([0,1,2,76,108,4,5],[10,431,465,512],[]),e6 [18,190] [14,115,289,517,578,579],([90,1,2,3,31,4,5],[10,20,68,295,523,525,527,580,581,582],[]),e6 [72,69] [14,16,114,281,288],([90,1,2,3,12,6,4,5],[10,20,36,295,499,583],[0]),([21,0,1,2,12,6,4,5],[10,36,246,247,289],[0]),u6 [124,13] [20,114,567,584,585],e6 [214] ([16,75,110,129,194,431]++r 586 4),([18,0,1,2,3,14,4],[10,38,50,54,59,60,131,590,591],[0]),([43,1,2,12,4,7,5],[18,20,22,388,411,592],[0]),u6 [51,12] [10,16,36,75,334,499,555,593,594],([141,0,1,2,3,23,4,34],([114,270]++r 595 4),[]),([62,0,1,2,22,12,4,5],[129,216,288,289,356,435,495],[]),u6 [18,14] [114,115,336],e6 [23,215] [14,36,114,115,301,327,599,600],([18,216,0,1,2,3,5],[10,26,601,602,603],[]),([18,73,0,1,2,3,13,5],[20,26,50,115,604,605],[0]),([74,82,0,1,2,3,12,5],[10,334,335,606],[0]),([1,2,3,22,12,4,7,5],[15,18,20,22,218,245,411],[0]),([73,21,0,1,2,12,4,5],[354,436],[0]),e6 [218,31] [10,263,607,608],e6 [13,32] [14,20,109,288,304,477,478,609,610],([94,149,1,2,3,5],([10,270,571]++r 611 4),[]),([172,141,0,1,2,3,23,4],[270,327,387,615,616],[]),([82,0,1,2,3,31,5],([10,46,115,334,386]++r 617 5),[0]),([21,1,2,3,4,7,5],[15,16,21,22,68,88,100,234,622,623],[0]),u6 [219,106] [20,36,75,330,544,624],([84,82,0,1,2,3,5],([10,115,621]++r 625 4),[0]),([82,0,1,2,3,12,220,5],[10,20,36,46,335,336,386,629],[0]),e6 [12,220] [10,36,335,336,499,555,629,630],([36,0,1,2,3,12,14,4],[336,631,632,633],[0]),([126,0,1,2,3,12,14,4],[10,45,634,635,636],[0]),e6 [62,72] [14,16,216,435,637,638],([0,1,3,12,4,48,49,5],[36,75,114,119,639],[0]),([0,1,2,3,12,14,4,38],[10,36,50,131,218,289,317,640,641],[0]),([74,0,1,2,3,12,14,4],[10,45,335,379,642,643],[0]),u6 [62,13] [14,114,217,218,219,288,477,644],u6 [59,13] [14,20,114,212,214,215,288,645],u6 [83,221] [14,208,215,218],e6 [72,83] [14,16,208],e6 [31,222] [14,115,144,169,370,646,647],([74,73,0,1,2,133,3],[127,130,231,648,649],[0]),u6 [12,91] [10,36,317,360,499,555,650,651],([74,73,0,1,2,3,12,13],[20,26,28,218,335,467,652,653],[0]),e6 [124,72] [14,290,496],([0,1,144,3,31,4],[10,169,654,655],[]),([18,72,0,1,2,3,6,5],[10,36],[0]),([72,104,1,2,3,12,4,5],[78,375,377,656],[]),([78,0,1,2,223,4],[34,35,169,657,658],[]),e6 [72,59] [61,210,211,360,659],([74,73,72,0,1,2,3,12],[62,467,468,660],[0]),([141,0,1,2,3,31,4,32],[144,169],[]),([124,141,0,1,2,3,31,4],[169,261,661],[]),e6 [224,48] [36,129,568],([216,0,1,2,3,5],[10,26,662,663,664],[]),([18,1,2,3,7,5],[17,20,26,49,97,98,268],[]),([18,73,72,0,1,2,3,5],[26,115,665],[]),([72,0,1,2,3,12,6,38],[92,343,382,666],[0]),([164,0,1,2,3,31,4,32],[26,144,169,667,668],[]),([0,1,2,3,31,4,69],[26,115,144,169,263,669],[0]),([0,1,2,3,31,12,4,69],[144,169,215,335,669],[]),([1,2,3,225,12,4,7,5],[18,20,21,499,670,671],[]),([18,0,1,2,3,31,4,69],[26,115,144,169],[]),e6 [96] ([10,36,75,110,129,194]++r 672 4),([18,226,1,2,3,5],[10,26,47,676,677],[]),([18,0,1,2,3,31,32,5],[26,144,169],[0]),([18,0,1,2,3,12,227,5],[218,678],[]),([18,1,2,3,12,7,5],[16,20,26,97,98,218,413],[0]),([82,0,1,2,3,12,5,228],[10,335,625,679],[0]),e6 [180,32] [109,115,132,263,304,680,681],([124,0,1,2,3,31,32,5],[109],[0]),([0,1,2,3,23,24,34,5],[16,115,253],[0]),([124,0,1,2,3,31,4,69],[26,115,144,169,368],[0]),e6 [204,229] [36,245,314,379,489,490],([124,164,0,1,2,3,31,4],[26,109,144,169],[]),([78,0,1,2,20,4],[10,34,35,181,407,682],[]),([199,0,1,2,3,4],[10,26,460,461,683],[]),([0,1,2,3,22,12,6,38],[66,92,99,343],[0]),e6 [31,180] [14,684],e6 [22,69] [14,114,115,129,463,480],e6 [193,31] [10,14,194],([116,0,1,57,4,5],[143,144,685,686],[0]),([0,1,144,187,4,5],[144,169,687,688],[]),([66,1,2,3,12,4,7,5],[15,20,22,100,284,411,499,689],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_7_1 : checkNodesBT W_23 g_23 F_23 P_23_7 A_23 B_23_6 7 N_23_7_1 = true := by decide +kernel
def N_23_7 := N_23_7_0 ++ N_23_7_1
def B_23_7 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_7
set_option maxRecDepth 500000 in
lemma B_23_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 7 xs.toFinset) B_23_7 := by
  have hP := buildPoolsSubBT_sound (pdepth := 11) (W := W_23) (raw := r_23) (pspecs := ps_23) (used := U_23_7) S_23_ok
  have hm0 := checkNodesBT_mem (by decide) gp_23 W_23_ok hP A_23_ok B_23_6_ok C_23_7_0
  have hm1 := checkNodesBT_mem (by decide) gp_23 W_23_ok hP A_23_ok B_23_6_ok C_23_7_1
  exact buildBucketsBT_of_mem (forall_append (hm0) hm1)
def U_23_8 : List Nat := ([3,10]++r 13 4++[18,20,21,22,26,28,34,36,38,46,50]++r 59 4++[64,66]++r 68 4++[73,75,78,79,83,84,86,88,92,94,99,100,102,107,109,110,114,115,119,120,125,127,129,130,131]++r 141 4++[161,163,164,165,167,169,179,181,188]++r 192 5++[198,200,201,202,205,208,211,212]++r 215 4++[229,231,232,234,235,237]++r 242 8++[253,254,255]++r 258 4++[263,265,270,272,274,275,277,279,281,282,284]++r 287 5++[294,301,304,309,310,311]++r 314 5++[320,321,323]++r 326 5++[332,334,335,336,338,341,342,343,347,354]++r 356 5++r 365 4++[370,372,374,375,378,379,381,384]++r 386 4++[391,395,397,400,407,411,413,414,420,426,427,428,431,432,434,436,437,444]++r 446 4++[451,452,453,462,463,464,467,469,470]++r 477 5++[485]++r 488 4++[493,494,496,497,499,500,512,517]++r 520 4++[525,529,530,533,545,550,555,558,561]++r 563 8++[578,579,580,584,595,596,597,600,605,609,611,618,621,624,637,647,652,665,676,680,681,684]++r 690 1048)
def P_23_8 : BT (Option BoundPool) := buildPoolsSubBT 11 W_23 r_23 S_23 ps_23 U_23_8
def N_23_8_0 : List NodeSpec := [([138,230,0,1,2,4,5],([10]++r 690 7),[]),([230,0,1,2,231,4,5],[10,169,690,697,698],[]),([232,230,0,1,2,4,5],[10,691,693,695,699,700],[]),([230,0,1,233,2,4,5],[10,169,693,695,701,702],[]),u6 [57] ([10,360]++r 703 4),([138,56,0,1,3,4,5],([36,142,143,195]++r 707 5),[0]),([116,56,0,1,3,4,5],[36,142,143,195,709,712],[0]),([56,0,1,234,3,4,5],[142,143,144,195,709,713],[]),e6 [236] [10,14,110,144,194,714,715],([1,2,8,3,4,7,5],[15,18,22,68,100,323,437,716,717,718],[0]),([39,0,1,2,3],[3,84,86,496],[0]),e6 [141,238] ([10,16,169]++r 719 6),e6 [164,237] ([10,144,169]++r 725 4),([140,141,0,1,2,144,4],([161,169]++r 729 4),[0]),([140,141,0,1,146,2,4],([10,169,730]++r 732 4),[0]),e6 [144] [14,169,736,737,738],([239,149,1,2,3,4,5],([10,21,68,188]++r 739 4),[]),([150,149,1,2,3,4,5],[10,16,21,68,188,739,740,742,743,744],[0]),u6 [155,110] ([36,75,169,192,193]++r 745 4),e6 [153,152] ([36,195,196,360,444]++r 749 5),e6 [241] [14,169,754,755,756],u6 [160,161] [169,198,200,757,758],([141,0,1,2,3,4,160],[10,115,129,169,759,760],[]),e6 [243] [14,169,761,762,763],([92,1,2,3,4,7,5],[15,20,21,68,100,427,764],[0]),([244,0,1,2,245,159,5],([10]++r 765 6),[]),([154,0,1,152,3,4,5],[36,129,144,444,753,771,772],[]),e6 [246] [14,110,129,144,194,773,774,775],e6 [247] [14,110,169,194,776,777,778],e6 [141,248] [10,169,294,779,780],e6 [249] [10,14,110,194,781,782,783],([140,142,141,0,1,2,4],[10,161,163,732,784,785],[0]),([242,154,0,1,3,4,5],([36,115,144,169]++r 786 4),[]),([154,0,2,251,3,4,5],([14,129,144,775]++r 790 6),[]),([154,0,1,2,3,31,4],[36,75,144,195,202,796,797],[0]),([154,0,1,144,3,4,5],[36,144,169,798,799,800],[0]),([0,1,2,76,187,4,5],[144,775,801,802,803],[]),e6 [154,252] [36,144,787,793,804,805,806],e6 [253,175] ([36,144,282]++r 807 6),e6 [154,107] ([10,14,793]++r 813 4),e6 [154,254] ([20,36,144]++r 817 4),e6 [256] ([10]++r 821 4),e6 [155] [14,36,110,194,825,826,827],e6 [24,127] [10,129,144,828,829],u6 [128,41] ([10,144,205,309,310,321,395]++r 830 5),u6 [41,127] [144,321,391,395,828],e6 [127] [10,391,828,835,836],u6 [41,165] [144,205,309,321,395,837,838,839],([257,141,0,1,2,4,5],([10,115,144,169]++r 840 4),[]),([257,0,1,2,76,4,5],[144,844,845,846],[]),([74,73,55,0,1,2,3],[28,62,130,235,237,448,497,847,848],[0]),e6 [258] [14,110,169,194,849,850,851],([230,55,0,1,2,4,5],[75,169,690,693,695,852,853],[]),([55,56,0,1,3,4,5],[36,142,143,195,360,497,709],[0]),([55,259,0,2,3,4,5],[497,852,854,855,856],[]),([55,104,1,2,3,4,5],[78,79,125,272,497,857,858],[0]),e6 [260] [14,169,194,859,860,861],([55,0,1,2,4,261,5],([16,169,329,852]++r 862 4),[]),e6 [263] ([14,169,497]++r 866 4),u6 [153] [14,36,196,749,750,753,870],([74,73,0,1,2,3,12],[26,28,62,130,218,467,652],[0]),u6 [83,12] [16,208,215,218,288,289,420,446,871],e6 [264] [10,329,847,872,873,874],u6 [83] [14,208,215,218,420,446,871],e6 [138] [10,14,26,110,194,875,876,877],u6 [59] [13,14,26,61,211,212],([230,0,1,2,12,4,5],[10,26,75,169,289,878,879],[]),([55,1,2,3,4,7,5],[15,18,20,21,22,68,100,254,497,847,880],[0]),([56,0,1,3,12,4,5],[26,36,129,144,195,881,882],[]),([259,0,2,3,12,4,5],[26,289,854,856,883],[]),([104,1,2,3,12,4,5],[26,78,79,125,375,500],[0]),([0,1,2,3,12,6,38],[66,92,99,215,218,342,343],[0]),e6 [159,163] [10,169,201,884,885],([0,1,3,191,4,24,5],[36,432,846,886,887,888],[]),([1,2,3,12,4,7,5],[15,18,20,21,22,26,218,411,413,499],[0]),([0,1,2,187,12,4,5],[10,144,289,889,890,891],[0]),([164,0,1,144,3,4,5],[10,169,892,893],[0]),([84,164,0,1,2,3,4],[10,215,894,895],[0]),([265,0,1,2,3,12,5],[10,26,896,897,898],[]),([266,1,2,3,12,4,5],[10,26,496,500,899,900],[]),u6 [124,31,12] [26,218,335,901],u6 [31,12,32] [26,144,169,261,335,481],u6 [12,32] [20,26,144,169,289,304,481,609],e6 [31,12,180] [10,263,265,289,680,902],([164,0,1,2,3,31,4],[10,26,263,903,904],[0]),u6 [31,180] [10,14,263,265,384,680,681,905],([226,1,2,3,12,4,5],[10,26,499,906,907,908],[0]),u6 [156,110] ([36,169,193,194,464,745,747,748]++r 909 4),e6 [18,164] ([10,26,496]++r 913 5),u6 [18,31] [10,26,115,261,263,265,368,370,517,918,919],([18,217,0,1,2,3,5],[10,26,218,676,920,921],[0]),u6 [18,12,69] [26,144,169,215,335,463,494,922],([18,73,0,1,2,3,12,5],[20,26,215,335,358,359,605],[0]),u6 [12,69] [26,129,144,169,289,335,462,480,494,923],u6 [124,12] ([20,26,75,129]++r 288 4++[335,496,555,584]),e6 [18,267,12] [10,115,242,289,517,924,925],u6 [69] [14,26,115,144,462,480,494,923],([141,78,0,1,2,4],[10,164,165,167,169,496],[0]),e6 [257] [14,110,144,194,926,927,928],([0,1,2,3,45,195,5],[10,26,218,929,930,931],[0]),e6 [18,12] [10,26,75,215,288,289,335,555,932,933],([154,0,1,2,3,4,41],[36,75,115,144,934,935],[]),e6 [141,31] ([10,169,261,263,265,368,370,597]++r 936 4),([141,0,1,2,3,31,4],[10,129,169,261,263,936,939],[0]),e6 [12,237] [10,26,258,335,719,720,940,941],([0,1,144,3,12,4,5],[10,75,169,942,943],[0]),([0,1,44,2,12,4,5],[10,75,129,328,469,944],[0]),([1,2,3,22,4,7,5],[15,18,20,21,100,245,255,270,945,946],[0]),([149,1,2,3,22,4,5],[10,188,270,740,945,947,948,949],[0]),e6 [49] ([16,36,120]++r 950 4),u6 [48,49] [36,114,119,120,950,951,952],e6 [269] ([169]++r 954 4),u6 [29,12] [10,215,218,289,335,558,561,563,958,959,960],e6 [270] [10,110,115,169,194,248,961,962,963],u6 [22,31] [10,14,73,114,215,261,263,265,964,965,966],u6 [31,28] ([10,16,26,114,115,261,263,265]++r 967 5),e6 [141,271] [10,163,169,972,973,974],([0,1,272,3,12,4,5],[10,16,75,218,975,976],[]),([74,73,0,1,2,3,22],[28,130,237,245,270,449,977],[0]),e6 [273,22] ([14,36,144,194,245,314]++r 978 4),u6 [98] [36,69,102,270,317,318,320],e6 [164,31] [10,26,144,169,263,265,368,903,904],u6 [12,13,6] ([10,36,215,246,289,334]++r 982 4),e6 [56,22] [10,14,36,129,142,144,194,195,270,314,709,986,987,988],u6 [74,22,12] [10,129,218,245,288,289,315,378,379,989],e6 [169,187] ([10,194,775]++r 990 8),u6 [196] [10,14,26,488,998,999],u6 [73,133] ([115,127,129,248,287,496]++r 1000 7),([0,1,2,3,22,6,38],[66,99,245,277,314,367,1007],[0]),u6 [93] ([16,36,75,110,194]++r 243 4++[270,372,1008]),([0,1,2,12,4,261,5],[10,16,26,864,865,1009,1010],[]),([18,0,1,2,3,12,6,5],[10,16,26,36,215,218,529,530,566,1011],[0]),([40,0,1,3,12,4,5],[10,75,248,249,356,1012,1013],[0]),e6 [274] ([14,169,193]++r 1014 4),u6 [160,163] [169,201,397,758,884],e6 [275] ([36,75,110,114,194]++r 1018 4),e6 [22,235] ([10,16,129,144,195,245,270]++r 1022 4),e6 [276,191] ([16,20,36,129,195,432,888]++r 1026 8),u6 [22,41,24] [10,115,144,270,309,311,314,321,846,966,1034,1035],e6 [12,248] [10,26,1036,1037,1038],u6 [23,34] [14,114,115,253,270,520,595,1039],([140,141,0,1,2,20,4],[10,407,732,1040,1041],[0]),u6 [23,27] [10,14,36,64,71,327,521,1042,1043],([154,0,1,2,277,3,4],([10,129,144]++r 1044 4),[]),([1,2,20,3,4,7,5],[15,16,18,21,22,68,100,407,428,1048],[0]),u6 [95] [36,115,360,400,1049,1050],e6 [163] [14,36,201,397,884,885],u6 [190,12] [10,14,75,129,215,218,288,289,335,555,578,579,1051,1052,1053],e6 [141,23] [10,14,71,169,301,326,327,596,597,1054],([18,148,0,1,2,3,5],[10,26,115,218,242,570,1055,1056],[0]),e6 [278] [10,16,26,218,1057,1058,1059],u6 [31,32] [26,115,144,169,265,304,481,609],e6 [279] [20,75,110,114,194,1060,1061,1062],([0,1,2,3,23,4,77],[10,205,270,314,327,1063,1064,1065],[]),e6 [281,12] ([16,26,75,129,218,288,555]++r 1066 4),u6 [45,13] [10,50,334,336,464,477,478,550,1070,1071],e6 [231] [10,14,169,690,697,698],([282,1,2,3,22,4,5],([10,270]++r 1072 5),[]),([283,56,0,1,3,4,5],[36,142,707,709,1077,1078],[]),([284,0,1,2,245,3,5],([14,115,407]++r 1079 4),[]),([82,0,1,2,3,12,5],[10,46,335,386,618,621],[0]),e6 [22,160] [10,114,115,200,270,758,1083,1084,1085],u6 [74,133] [10,16,129,231,232,248,315,1000,1002,1004,1086,1087,1088],([0,1,152,20,3,4,5],([36,115,194,444,751,1040]++r 1089 4),[0]),e6 [23,159] ([10,14,16,270,327]++r 1093 6),u6 [154,23] [10,36,70,71,270,301,314,326,327,1099,1100],([56,0,1,3,22,4,5],[36,142,144,195,270,709,987],[]),e6 [286] ([270]++r 1101 4),e6 [288] [194,270,1105,1106,1107],e6 [255,22] ([10,14,115,129,144,194,270,966,986]++r 1108 4),u6 [22,41] [10,14,129,144,270,309,321,395,966,1034,1112],([0,1,2,20,76,4,77],([407,1040]++r 1113 5),[0]),e6 [289] ([129,144,311,966]++r 1118 6),e6 [277,28] ([14,114,169,194,497,967,969,971]++r 1124 4),u6 [40,38] ([10,16,36,83,248,316,317,988]++r 1128 4),([56,0,1,20,3,4,5],[36,142,194,407,709,1132,1133],[]),([0,2,3,291,4,24,5],([144,311,846]++r 1134 4),[]),e6 [292] [75,114,971,1138,1139,1140],([119,1,2,3,4,7,5],[15,18,20,21,22,68,100,533],[0]),e6 [242] [14,110,169,194,1141,1142,1143],u6 [40,6] ([10,16,36,83,246,247,248,365,1025]++r 1144 4),([40,154,0,1,3,4,5],[10,36,83,248,356,360,366,793,812,1148,1149,1150],[]),u6 [21,6] [10,16,36,88,234,246,247,1144,1146,1151,1152,1153],e6 [293] [14,169,1154,1155,1156],([55,0,1,2,22,4,5,38],[10,94,195,447,470,493,988,1130,1157,1158,1159],[0]),([186,0,1,2,187,4,5],[144,775,1160,1161,1162],[0]),u6 [22,175] [10,14,129,270,809,811,966,1163,1164,1165],e6 [22,237] [10,270,282,720,727,728,941,966,1166],([55,0,1,2,22,6,4,5],[10,94,329,447,1025,1146,1167,1168,1169],[0]),e6 [154,294] ([115,129,169,545,775,787]++r 1170 7),([282,1,2,20,3,4,5],[10,1072,1074,1177,1178,1179],[]),e6 [295] [110,115,129,169,194,1180,1181,1182],e6 [296] [36,75,169,597,1183,1184,1185],([0,1,2,20,297,4,5],([407,1040]++r 1186 5),[]),e6 [298] ([10,75,115,360,407]++r 1191 4),e6 [299] ([10,75,110,194]++r 1195 4),u6 [84,13] [10,50,288,336,477,478,522,983,1199,1200,1201],([74,0,1,2,22,12,4,5],([10,288,289,315,357,381,979,989]++r 1202 4),[0]),([104,1,2,20,3,4,5],[78,79,125,229,272,407,1178],[0]),u6 [18,31,12] [10,26,335,919]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_8_0 : checkNodesBT W_23 g_23 F_23 P_23_8 A_23 B_23_7 8 N_23_8_0 = true := by decide +kernel
def N_23_8_1 : List NodeSpec := [u6 [133,38] [10,14,16,36,127,232,248,470,1004,1206,1207],u6 [154,22,175] [10,36,144,245,356,787,809,811,1164],e6 [300] ([16,75,110,114,115,194,1021]++r 1208 4),u6 [73,72,12] [10,26,281,289,335,436,1212,1213,1214],u6 [20,110] [10,14,169,193,407,745,747,748,1040,1215,1216],e6 [301] ([10,16,36,75,115,129,360,1040,1091]++r 1217 5),u6 [43,41] [10,144,309,395,545,830,1222,1223,1224],e6 [94,154] ([10,36,115,144,270,787]++r 1225 5),e6 [154,248] [36,144,793,1230,1231,1232],u6 [193,31,12] [10,265,288,451,1233],e6 [302,154] [10,20,36,114,144,793,1234],([84,0,1,2,22,12,4,5],[10,73,288,289,357,1199,1201,1202,1235,1236],[]),([0,1,2,20,245,159,5],[115,169,407,767,768,1040,1237,1238,1239],[]),([282,1,2,3,12,4,5],[10,26,500,1076,1177,1240],[]),e6 [303] ([16,115,129,144,194,793]++r 1241 5),e6 [181] [16,36,83,110,115,194,248,1246,1247],u6 [94,12] [10,75,144,245,258,288,335,400,555,1229,1248,1249,1250],e6 [304] [10,14,129,144,1251,1252,1253],([140,0,1,2,107,3,4],[10,14,431,1254,1255,1256],[]),e6 [107,305] ([10,114,407]++r 1257 4),e6 [306] [10,75,110,129,194,360,407,1048,1261,1262,1263],([0,1,2,3,12,307,5],([26,218]++r 1264 4),[]),e6 [308] ([36,169,545]++r 1268 4),e6 [309] ([75,110,194,545]++r 1272 4),([78,0,1,2,4],[34,179,181,496],[0]),u6 [74,12,13] [10,215,334,379,989,1276,1277],e6 [238] [14,16,36,110,194,719,722,723,724],([94,148,0,1,2,3,5],[10,115,245,270,400,611,1278,1279],[0]),([242,0,1,3,12,4,5],[10,75,115,169,1280,1281],[]),e6 [164] [10,14,26,110,194,1282,1283],u6 [108] [10,14,16,68,115,129,512,1284],u6 [107,76] [10,14,407,431,479,1285,1286,1287],e6 [310] [10,14,169,1288,1289,1290],u6 [20,160] [10,36,200,201,407,758,1084,1291,1292,1293],([0,1,2,76,311,4,5],[114,1021,1294,1295,1296],[]),([74,55,0,1,2,22,4,5],([129,315,447,493,852,979]++r 1297 4),[0]),([302,0,1,2,76,4,5],[114,971,1301,1302,1303],[]),e6 [154,277] [10,144,1044,1045,1046],([312,0,1,3,12,4,5],[10,75,144,360,1304,1305],[]),e6 [313] [10,16,36,75,88,110,115,194,1306,1307,1308],u6 [21,38] [10,16,36,88,316,317,1128,1130,1309,1310,1311],e6 [314] ([10,14,16,36,88,115,129]++r 1312 5),e6 [315] ([10,16,75,110,194]++r 1317 4),u6 [74,72,12] [10,218,289,378,426,989,1204,1321],e6 [249,154] [10,129,144,781,782,783,787,793,1165,1226,1322,1323],([141,0,1,2,187,4,5],[10,169,775,1324,1325],[0]),e6 [268,24] ([16,75,115,144,169,545,846,957]++r 1326 4),e6 [31,12] [10,26,218,1330,1331],e6 [316] ([16,75,115,169,360,597]++r 1332 5),([66,1,2,3,4,7,5],[15,16,18,20,21,22,68,100,284,1144,1337],[0]),([140,164,141,0,1,2,4],[10,294,730,1338,1339],[0]),u6 [73,22,12] [10,73,129,287,288,289,335,354,436,966,1212],u6 [172,23] [16,70,71,115,259,260,270,301,326,327,387,1340],e6 [20,317] ([115,169,407,1040]++r 1341 6),e6 [94,141] ([10,194,270,496,938,1227]++r 1347 4),e6 [318] [16,407,1040,1351,1352,1353],u6 [74,21] [10,16,36,234,279,378,379,1354,1355,1356],e6 [319] [10,16,215,218,1357,1358,1359],([164,0,1,2,187,4,5],[10,144,889,890],[0]),e6 [320] [16,110,129,194,407,1040,1048,1360,1361,1362],u6 [124,31] [16,26,109,115,261,263,265,338,368,370,901,1363],u6 [73,21] [10,36,88,115,354,436,496,1364,1365,1366],e6 [154,268] ([129,169,545,775,957]++r 1367 6),([0,1,2,22,12,4,5,38],[73,195,357,381,470,485,988,1373,1374],[0]),([94,0,1,2,3,6,5],([10,115,245,270,360,1250]++r 1375 4),[0]),u6 [23,24] [10,16,36,70,71,75,115,144,270,327,1326,1328,1379,1380],u6 [204] [36,245,314,489,490,1381,1382],e6 [321] [10,20,68,115,1383],([230,0,1,2,22,4,5],[10,194,270,693,695,1384,1385,1386],[]),u6 [31] [10,14,26,684,1330,1331],u6 [193,31] [10,109,194,261,263,265,368,451,452,647,1387],e6 [322] ([10,20,129,407]++r 1388 5),e6 [169,195] ([10,14,26,114,218,928]++r 1393 5),([56,0,1,3,57,4,5],[36,143,144,703,704],[0]),e6 [323] ([10,407]++r 1398 4),e6 [18,169] [10,14,26,114,242,517,922,1402,1403,1404],([0,1,2,107,76,3,4],[10,14,431,479,1286,1287],[0]),e6 [324] [75,144,194,846,1405,1406,1407],u6 [12,14] [10,14,38,50,59,60,131,289,335,336,360],([149,1,2,20,3,4,5],[10,188,407,739,740,1408,1409],[]),([0,1,2,22,45,12,4,5],[10,73,289,332,357,381,1070,1410,1411,1412],[]),([230,0,1,2,20,4,5],[10,690,693,695,1114,1413,1414],[]),e6 [164,175] [36,144,169,807,809,811,1415,1416,1417],([325,154,0,1,3,4,5],[14,36,248,793,1418,1419],[]),e6 [164,248] [10,26,1036,1038,1420],e6 [326] ([10,16,75,110,115,129,194,1040]++r 1421 5),e6 [20,237] [10,36,407,719,725,727,728,941,1091,1426],([0,1,2,22,4,261,5],[10,16,270,864,1427,1428],[]),([18,0,1,2,22,12,4,5],[10,73,242,288,289,356,357,381,517,1202,1429,1430],[0]),e6 [29] [114,289,335,558,561,563,958,959,960],e6 [328] [110,169,194,1431,1432,1433],u6 [181,23] [10,36,70,71,248,301,326,327,347,600,1434],u6 [74,40] [10,16,36,248,365,366,378,379,979,1205,1435,1436,1437],([230,43,0,1,2,4,5],[10,169,194],[]),([0,1,20,3,4,235,5],[16,36,247,407,1023,1024,1438],[]),([0,1,2,20,3,6,38],[66,92,99,277,1048,1114,1439],[0]),e6 [329] [10,14,110,169,194,865,1440,1441],([141,0,1,2,3,23,4],[10,14,71,129,169,327,596,597,1054,1442],[0]),u6 [106] [36,114,115,270,330,624,1443,1444],e6 [330] ([10,129,317,1114]++r 1445 4),u6 [22,12,6] [10,36,218,245,246,247,289,329,356,984,1202],([21,0,1,2,12,4,5],[10,14,75,1449,1450,1451],[0]),e6 [331] [14,110,144,194,846,1452,1453],u6 [73,40] [10,83,115,496,1006,1013,1454,1455,1456],u6 [23,12] [10,14,71,73,144,289,314,327,335,1457,1458],([0,1,2,22,31,12,4,5],[10,73,261,263,265,289,357,381,964,965],[0]),u6 [18,22] [10,14,194,218,242,282,314,356,517,567,922,966,986,1429,1430],([104,1,2,3,22,4,5],[79,125,270,272,274,1073],[0]),([43,0,1,2,45,12,4,5],[10,107,332,388,389,1412,1459,1460],[]),e6 [332] [14,110,169,194,1344,1461,1462],e6 [31,159] [10,26,169,261,263,265,1093,1095,1097,1098,1463,1464,1465],([18,43,0,1,2,12,4,5],[10,20,107,129,242,288,388,389,922,1004,1466,1467],[0]),e6 [333] [10,129,379,1048,1468,1469,1470],([43,0,1,2,31,12,4,5],[10,20,107,261,263,370,388,389,1471],[]),([84,43,0,1,2,12,4,5],[10,107,129,288,389,1004,1199,1466,1472,1473],[]),([73,43,0,1,2,12,4,5],[20,107,129,287,288,1004,1005,1212,1466,1474],[0]),e6 [335] [14,110,169,194,1475,1476,1477],u6 [133,6] [10,36,127,231,248,329,1004,1478,1479],e6 [242,169] [14,114,169,1480,1481,1482],([43,0,1,2,12,4,5,38],[10,36,107,289,316,388,389,470,1374,1483],[0]),([73,0,1,2,22,12,4,5],[10,73,287,288,289,356,1202,1212,1213,1484,1485],[0]),([90,1,2,3,12,4,5],[20,36,499,523,525,983],[0]),([18,0,1,2,3,6,5],[10,26,115,218,360,529,530,566,567,1011],[0]),([0,1,20,3,191,4,5],[20,36,432,434,1028,1029,1040,1486],[0]),([74,43,0,1,2,12,4,5],[10,129,288,315,388,389,989,1004,1088,1466,1487],[0]),e6 [336] ([16,194,545]++r 1488 5),e6 [337] ([16,75,110,115,144,194,775]++r 1493 4),e6 [338] [10,329,1175,1497,1498],e6 [311,24] ([10,75,115,144,311,1021,1326]++r 1499 5),([43,1,2,3,4,7,5],[18,20,21,22,68,100,545,1175,1504,1505],[0]),e6 [339] ([16,75,129,169,1097]++r 1506 5),([43,0,1,2,4,261,5],[10,329,1175,1428,1511],[]),e6 [340] [10,75,110,129,144,194,1512,1513,1514],u6 [62] [14,16,26,75,110,129,194,216,217,218,414,1515],([43,0,1,2,3,6,38],[92,99,275,277,360,1175,1371,1516],[0]),([43,104,1,2,3,4,5],[78,125,272,545,857,1517],[0]),e6 [18,141] [26,75,242,496,517,597,841,922,938,1347,1350,1518,1519,1520],([56,43,0,1,3,4,5],[36,143,144,545,709],[]),([55,0,1,2,3,6,38],[66,92,99,275,277,360,491,847,1521,1522],[0]),e6 [341] [10,75,110,194,315,1175,1523,1524,1525],([74,73,43,0,1,2,3],[62,130,235,237,545,1175,1526],[0]),([0,1,2,342,12,4,5],[10,16,218,289,1527,1528,1529],[]),e6 [343] [110,114,194,248,1530,1531,1532],u6 [31,12,28] [10,215,218,263,265,288,335,374,970],e6 [164,28] [10,14,26,114,144,169,194,915,967,1533],e6 [344] ([10,110,114,129,194]++r 1534 4),e6 [345] ([75,110,194,497]++r 1538 4),([346,0,1,2,3,12,4],([26,215]++r 1542 4),[]),e6 [84,72] [10,14,281,665,1199,1201,1546,1547,1548],u6 [12,48] [10,26,36,114,119,120,289,565,1549,1550],e6 [347] [10,20,114,1551,1552,1553],([0,1,3,12,4,235,5],([26,129,195,218,247]++r 1554 4),[]),e6 [349,12] ([26,215,218]++r 1558 4),u6 [55,48] [10,14,114,119,120,453,497,564,852,1562],e6 [141,325] ([114,248]++r 1563 4),e6 [187,28] [10,114,967,996,997,1567,1568,1569],e6 [350] [10,75,129,144,194,1570,1571,1572],e6 [351] [10,20,114,115,1573,1574,1575],u6 [12,170] ([10,26,36,289,335]++r 1576 5),e6 [169,144] ([14,114,169,1350]++r 1581 5),([302,141,0,1,2,4,5],[10,14,114,169,597,1320,1586,1587],[]),u6 [82,12] [10,16,46,75,129,215,288,334,335,336,386,555,618],u6 [59,12] [13,26,61,211,212,215,218,288,289,360],([0,1,2,22,12,6,4,5],[73,195,329,381,984,1025,1588,1589],[0]),e6 [191,28] [114,195,432,888,971,1028,1029,1032,1590,1591],e6 [142,237] [10,169,282,720,725,727,728,1592],e6 [144,28] [14,114,169,194,967,1585,1593,1594,1595],u6 [109,107] ([10,14,407,431,1114]++r 1596 4),e6 [50] [10,341,568,1600,1601],u6 [48,50] [114,119,341,568,1600,1601],u6 [105,48] [10,14,36,114,119,120,453,564,569,1602,1603],u6 [31,13] [10,26,114,263,265,334,477,478,580,983,1604],e6 [353] ([169,248]++r 1605 5),([74,73,0,1,2,20,3],[28,62,130,237,407,1048,1610],[0]),e6 [281] ([26,75,110,129,194,218]++r 1066 4),e6 [349] ([26,215]++r 1558 4),e6 [354] [10,14,110,144,194,1611,1612],e6 [355] [26,110,169,194,248,1613,1614],([141,0,1,2,311,4,5],[10,14,169,597,1021,1615,1616,1617],[]),([257,0,1,2,12,4,5],[10,75,115,144,289,926,927],[]),([73,55,0,1,2,22,4,5],[94,129,287,356,852,1297,1299,1485,1618,1619,1620],[0]),e6 [356] [16,497,1522,1621,1622,1623],e6 [169,262] ([14,115,129,169,497,847,1021]++r 1624 6),e6 [358] [169,1630,1631,1632],e6 [187] [14,144,889,890,891,1633],e6 [12,196] [10,26,115,998,999],([154,0,1,359,3,4,5],([14,36,793,812]++r 1634 4),[]),([242,0,1,2,245,159,5],[169,765,767,768,1238,1638,1639,1640],[]),e6 [360] ([114,248,360]++r 1641 4),u6 [72,31] [10,263,265,368,426,1645],([164,0,1,250,2,4,5],[10,36,144,1646,1647,1648],[0]),e6 [359,159] ([114,129,1093,1097,1482]++r 1649 5),e6 [31,195] ([10,26,144,169,263,265,1393,1396]++r 1654 5),e6 [361] [10,75,169,194,317,1659,1660,1661],e6 [141,359] ([114,248,1563,1584,1636,1637,1651,1653]++r 1662 5),([43,0,1,2,12,6,4,5],[10,36,107,247,329,388,984,1667],[0]),e6 [169,31] [10,26,109,215,261,263,265,368,370,1668,1669],e6 [154,31] [36,144,195,202,793,796,797],e6 [362] [10,14,36,75,110,114,115,194,1501,1670,1671,1672],([55,363,0,1,3,4,5],([248,360,1522]++r 1673 4),[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_8_1 : checkNodesBT W_23 g_23 F_23 P_23_8 A_23 B_23_7 8 N_23_8_1 = true := by decide +kernel
def N_23_8_2 : List NodeSpec := [e6 [154,311] ([10,144,1021,1502,1503]++r 1677 5),e6 [364] [10,16,20,36,110,115,129,194,1578,1682,1683],e6 [190] [16,75,110,114,115,129,194,289,578,579,1051,1052,1053],u6 [169,31,12] [10,263,265,289,360,1669],u6 [22,12,38] [10,36,289,316,317,356,357,470,1202,1374],e6 [164,169] [10,14,26,144,169,915,916,1684,1685],e6 [365] [10,14,110,144,194,1686,1687],([0,1,2,3,31,4,198],[10,26,215,263,1688,1689,1690],[0]),e6 [169,277] ([14,129,497,1021,1125,1126,1522]++r 1691 5),([154,0,1,3,191,4,5],[20,36,129,144,195,205,1696,1697,1698],[]),e6 [257,169] [10,14,114,144,1402,1699,1700],u6 [18,13] [10,20,26,50,218,242,282,288,477,478,517,983,1701,1702],([56,0,1,136,3,4,5],(r 141 4++[709,1703]),[0]),u6 [18,169,12] [10,218,242,288,289,335,517,1404,1580],u6 [72,12,6] [10,36,218,247,289,426,984,1589,1704,1705],e6 [27] [16,36,64,71,115,521,1042,1043],e6 [169,152] [36,114,195,444,752,753,1021,1090,1706,1707,1708],e6 [169,191] [10,36,114,432,888,1021,1026,1028,1029,1709,1710,1711],([154,0,1,2,107,3,4],([10,14,144,793]++r 813 4),[]),u6 [62,12] [16,26,75,129,216,217,218,288,289,414,555,1515],([0,1,2,3,12,14,4],[10,14,38,59,60,131,289],[0]),u6 [12,13,38] [10,20,36,50,218,289,317,983,1374,1712,1713],e6 [366] [36,75,110,169,194,1714,1715,1716],u6 [73,12,13] [10,20,335,336,354,1212,1717,1718],e6 [72,45] [10,281,332,426,665,1070,1719,1720],([0,1,2,3,12,367,5],[10,16,215,218,1721,1722,1723],[]),([368,0,1,2,12,4,5],[10,75,169,289,360,1724,1725],[]),u6 [18,72] [10,14,16,218,242,426,517,637,665,1704,1726,1727],u6 [72,12,38] [10,36,215,289,316,485,665,1374,1704,1728],([369,0,2,3,12,4,5],[26,289,1729,1730,1731],[]),e6 [12,160] [10,26,115,144,201,1084,1085,1732],([149,1,2,3,12,4,5],[10,21,26,499,739,1733,1734],[0]),([0,1,2,3,31,4,77],[10,26,36,215,261,1735,1736,1737],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_8_2 : checkNodesBT W_23 g_23 F_23 P_23_8 A_23 B_23_7 8 N_23_8_2 = true := by decide +kernel
def N_23_8 := N_23_8_0 ++ N_23_8_1 ++ N_23_8_2
def B_23_8 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_8
set_option maxRecDepth 500000 in
lemma B_23_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 8 xs.toFinset) B_23_8 := by
  have hP := buildPoolsSubBT_sound (pdepth := 11) (W := W_23) (raw := r_23) (pspecs := ps_23) (used := U_23_8) S_23_ok
  have hm0 := checkNodesBT_mem (by decide) gp_23 W_23_ok hP A_23_ok B_23_7_ok C_23_8_0
  have hm1 := checkNodesBT_mem (by decide) gp_23 W_23_ok hP A_23_ok B_23_7_ok C_23_8_1
  have hm2 := checkNodesBT_mem (by decide) gp_23 W_23_ok hP A_23_ok B_23_7_ok C_23_8_2
  exact buildBucketsBT_of_mem (forall_append (forall_append (hm0) hm1) hm2)
def U_23_9 : List Nat := ([10,14,16,20,22,26,36,62,68,71,75,78,92,100,110,114,115,120,129,144,163,169,193,194,195,200,201,205,215,218,235,237,242]++r 245 4++[261,263,268,270,272,275,277,287,288,289,294,301,303,309,311]++r 314 4++[326,327,329,332,335,354,356,360,368,370,374,378,379,400,407,436,453,464,470,477,478,496,497,545,555,564,597,637,690,691,693,707,709,719,720,725,727,730,732,734,739,740,742,745,747,751,753,765,768,770,775,784,792,793,800,807,811,812,816,830,832,840,841,846,847,852,856,857,888,907,913,915,922,928,938,941,949,957,966,967,969,971,979]++r 981 4++[986,988,989,990,993,997,1000,1002,1004,1005,1013,1021,1024,1025,1026,1028,1029,1040,1047,1048,1072,1084,1090,1093,1095,1097,1098,1109,1114,1115,1116,1125,1128,1130,1133,1144,1146,1157,1167,1170,1172,1175,1176,1177,1179,1187,1188,1193,1199,1202,1205,1212,1221,1226,1227,1229,1238,1239,1275,1276,1285,1291,1297,1299,1320,1322,1326,1328,1338,1341,1343,1344,1345,1347,1350,1367,1369,1371,1374,1386,1393,1396,1401,1402,1408,1412,1416,1418,1425,1428,1433,1436,1454,1459,1466,1472,1482,1485,1490,1492,1501,1503,1518,1522,1541,1564,1568,1575,1578,1580,1581,1584,1591,1594,1595,1596,1598,1619,1624,1627,1632,1633,1636,1651,1655,1662,1664,1677,1679,1684,1691,1693,1698,1704,1706,1711,1712,1717,1719,1734]++r 1738 207)
def P_23_9 : BT (Option BoundPool) := buildPoolsSubBT 11 W_23 r_23 S_23 ps_23 U_23_9
def N_23_9 : List NodeSpec := [u6 [334] [10,14,16,75,360,1738,1739],u6 [273] [14,16,36,129,144,360,378,981,1740],u6 [230] [10,14,75,110,129,169,194,360,496,690,691,693],([230,0,1,2,4,5],[496,690,691,693,1386],[0]),([0,1,2,297,4,5],[129,496,1187,1188,1741],[0]),u6 [56] [14,36,75,110,129,144,194,316,360,496,707,709],([104,1,2,3,4,5],[78,272,496,857],[0]),([0,1,2,3,6,38],[16,92,275,277,360],[0]),([1,2,3,4,7,5],[16,22,68,100,268,496],[0]),u6 [240,141] [10,16,115,169,496,597,720,938,1347,1350,1742,1743],u6 [141,237] [10,115,169,496,597,719,725,727],u6 [237] [14,115,496,719,725,727,941],u6 [142,141] [10,163,194,597,720,784,938,1347,1744],u6 [141,146] [10,14,169,597,938,1745,1746],([140,141,0,1,2,4],[129,496,730,732,734],[0]),([0,370,2,3,4,5],[14,129,496,1747,1748],[]),([282,1,2,3,4,5],[496,857,1072,1177,1179],[0]),([0,1,2,76,4,77],[129,360,496,1115,1116,1749],[0]),u6 [191] [14,36,115,129,195,888,1026,1028,1029],u6 [272] [10,14,16,115,496,1750,1751,1752],([149,1,2,3,4,5],[68,496,739,740,742,1753],[0]),u6 [110] [14,129,169,193,496,745,747],u6 [240] [10,14,75,110,115,194,496,1754,1755],u6 [160,159] [10,115,169,200,496,1097,1291],u6 [141,159] [10,16,115,129,169,360,720,1093,1095,1097,1098,1756,1757],u6 [242] [10,14,16,75,110,115,169,194,360,1098,1758,1759],u6 [244,159] [10,169,194,770,1093,1095,1097,1760,1761,1762],u6 [48] [14,114,120,129,453,496,564],([74,73,0,1,2,3],[16,62,235,237,496],[0]),u6 [109,20] ([10,14,16,115,194,407,1040,1048,1090,1114,1221,1239]++r 1763 4),u6 [152] [14,36,115,129,195,751,753,1090,1706,1767],u6 [290,24] [115,144,311,846,1328,1768,1769,1770],u6 [55,28] [14,16,115,194,374,497,847,852,967,969,971,1299,1771],e6 [371] [14,16,36,129,144,496,1772,1773,1774],u6 [74,43] [36,129,315,378,1004,1175,1205,1371,1775],u6 [43,38] [14,36,316,470,545,1004,1128,1130,1776],u6 [76,28] [14,36,115,496,969,971,1029,1345,1425,1591,1777,1778],u6 [43,285] [14,545,1004,1492,1779,1780,1781],u6 [159] [10,14,16,75,115,496,1782,1783],u6 [12,28] [10,26,218,288,289,335,374,969,971,1784],u6 [287,43] [129,545,1004,1175,1275,1371,1785,1786],([0,1,2,22,12,4,5],[10,129,288,289,356,1202],[0]),e6 [372,24] [144,311,464,1326,1328,1787,1788],u6 [31] [14,26,115,261,263,368,370],([0,1,2,245,159,5],[115,129,496,765,768,1238,1789],[0]),u6 [43,24] [16,20,115,144,545,846,1004,1175,1326,1328,1790],u6 [268] [10,16,75,115,129,169,194,957,1367,1369],u6 [23] [14,71,115,270,301,326,327],u6 [327] [10,16,496,1433,1791,1792],u6 [73,20] [10,75,115,194,287,354,407,436,496,1040,1763,1793,1794],u6 [352] [16,129,248,360,496,1795,1796,1797],u6 [133] [16,115,129,248,360,1000,1002,1004],u6 [12,348] [10,26,215,288,1798,1799,1800],u6 [169,12] [10,14,26,75,129,215,218,288,289,555,1021,1580,1636,1801],u6 [55,6] [246,247,329,360,497,847,852,1144,1146,1167,1802],([0,2,3,373,4,5],[14,16,129,496,1803,1804],[]),u6 [73,22] [10,14,115,129,194,270,287,354,356,986,1485,1794,1805],u6 [141,24] [10,16,75,115,129,144,169,303,311,496,597,841,846,1326,1328,1350,1806,1807],u6 [22,38] [10,129,270,314,317,356,470,988,1130,1808],u6 [20,38] [10,16,316,317,407,470,1040,1114,1130,1809],u6 [261] [10,14,16,75,496,1428,1810,1811],e6 [342] [10,14,16,496,1812,1813,1814],u6 [154,22] [10,14,36,129,144,194,245,270,314,356,775,793,986,1226,1815],u6 [154,159] [10,16,36,75,115,129,144,169,496,793,1093,1095,1097,1816,1817,1818],u6 [94] [75,110,115,129,194,270,360,400,1227,1229,1819],u6 [20,6] [10,246,247,329,407,1040,1048,1146,1820],u6 [170] [14,20,115,129,496,1578,1580,1821,1822,1823],u6 [45,12] [10,26,115,218,289,332,1412,1459,1719],u6 [22,6] [10,129,245,246,270,314,329,1025,1146,1824],u6 [141,20] [10,14,75,194,407,597,938,1040,1048,1350,1763,1825],u6 [363] [16,110,129,194,248,360,496,1826,1827],u6 [287,22] [10,14,129,194,245,270,314,356,986,1786,1828,1829],u6 [55,348] [194,497,1299,1799,1800,1830,1831],u6 [18,12] [10,16,26,75,115,129,215,218,242,288,289,335,555,922,1518,1832],u6 [294] [115,129,545,1170,1172,1176],u6 [74,55] [129,315,378,379,847,852,1205,1299,1522,1833],u6 [22,159] [10,16,115,129,245,270,1095,1097,1818,1834,1835],u6 [141,22] [10,14,129,194,245,270,356,360,597,720,938,986,1836,1837],u6 [140,20] ([14,194,407,1040,1763]++r 1838 4),u6 [20,76] [10,14,20,360,407,1029,1040,1048,1345,1425,1778,1842],u6 [154,250] [36,129,144,792,793,1226,1843,1844],u6 [141,28] [10,16,129,169,194,374,496,597,938,967,969,971,1595,1845],u6 [73,55] [75,115,129,287,354,436,496,497,852,1299,1619,1846,1847],u6 [40] [10,14,16,75,110,115,194,248,356,360,1013,1436,1454],u6 [148,20] [10,14,407,1048,1114,1193,1239,1408,1752,1763,1848],u6 [186,154] [20,36,195,205,775,793,812,1047,1226,1698,1849],u6 [20,159] [10,115,129,407,1040,1048,1095,1097,1098,1850],u6 [22,24] [10,115,144,245,270,311,314,356,846,966,1328,1851],u6 [160] [14,115,169,200,201,496,1084,1291],u6 [12,6] [10,26,129,215,218,246,247,289,329,982,984],u6 [20,245] [14,16,407,1040,1048,1774,1852,1853,1854],([43,0,1,2,12,4,5],[10,75,129,288,1004,1466],[0]),u6 [311] [10,14,114,115,1021,1501,1503,1677,1679],u6 [107] [10,14,16,115,129,407,1596,1598,1855],u6 [169,159] [10,115,129,169,496,1021,1093,1095,1097,1098,1482,1818,1856],u6 [74,22] [10,14,129,194,245,314,315,356,379,979,986,1205,1857],u6 [18] [14,26,110,115,129,194,242,360,922,1518,1832],u6 [73,43] [20,115,129,194,287,496,545,1004,1005,1794,1858,1859],u6 [154,187] [36,129,144,990,993,1568],e6 [368] [10,14,16,75,110,169,194,360,496,1860,1861,1862],u6 [43,6] [36,247,329,360,545,1004,1144,1146,1175,1863],u6 [284] [10,14,20,75,110,115,129,194,360,407,1864,1865,1866],u6 [74,20] [10,14,16,75,194,315,378,379,1040,1048,1114,1205,1763,1867],u6 [235] [14,16,36,129,144,247,496,1024,1868],u6 [109,169] [36,129,194,496,1021,1090,1221,1636,1765,1869],u6 [359] [14,16,36,115,129,248,1636,1651,1662,1664],u6 [22,12] [10,14,129,215,218,245,288,289,314,356,1202],([55,0,1,2,22,4,5],[129,194,356,852,1297,1299],[0]),u6 [141] [10,14,16,75,110,169,194,360,496,1870,1871],u6 [148,22] [10,14,129,194,245,270,314,949,986,1848],u6 [164,141] [10,75,294,597,720,938,1338,1347,1350,1872,1873],u6 [217,12] [10,26,115,215,218,288,289,555,907,1874],u6 [84,12] [10,26,129,215,288,289,555,1199,1472,1875,1876],e6 [374] [14,36,129,144,496,1840,1877,1878],u6 [280,12] [10,26,129,215,218,288,555,1541,1797,1879],u6 [357] [10,16,75,110,169,194,360,496,1632,1880,1881],u6 [22,77] ([10,129,270,314,1401]++r 1882 4),u6 [325] [14,36,110,115,129,194,248,360,1418,1564,1886,1887],u6 [154,43] [20,36,129,144,545,775,1004,1175,1226],([56,0,1,3,4,5],[496,707,709,1133],[0]),u6 [20,77] [10,129,407,1048,1114,1401,1883,1888,1889],u6 [55,169] [20,129,194,360,497,847,852,1021,1299,1580,1636,1890],u6 [169,24] [75,115,144,303,311,496,846,1021,1326,1328,1402,1636,1891],u6 [255] [14,20,110,115,129,194,496,1109,1892,1893],u6 [154,169] [14,75,144,195,360,496,775,793,1021,1226,1580,1636,1684,1894],u6 [55,280] [129,497,847,1299,1541,1797,1895,1896],u6 [175] [14,20,115,129,496,807,811,812,1897,1898],u6 [144] [10,14,16,115,129,169,360,1350,1581,1594],u6 [169,76] [36,194,360,496,1021,1029,1285,1425,1711,1778,1899],u6 [141,169] [10,14,129,169,360,496,597,938,1021,1580,1584,1636,1684,1900],u6 [12,13] [10,215,218,288,289,477,478,983],u6 [72,12] [10,288,289,555,637,1704],u6 [317] [14,115,129,496,1341,1343,1344],u6 [148,12] [10,26,115,129,215,218,288,289,555,1734,1752],u6 [12,77] [10,26,129,215,1885,1889,1901,1902],u6 [277] [10,14,16,115,129,169,1125,1691,1693],u6 [164] [10,14,16,26,110,115,194,913,915,1633,1903],u6 [154,28] [16,144,194,195,374,496,775,793,967,969,971,1226,1904],u6 [257] [10,14,75,110,115,129,144,194,360,840,846,1905,1906,1907],u6 [141,12] [10,75,129,169,218,288,289,360,555,1350,1908,1909],([259,0,2,3,4,5],[14,496,856,1910],[0]),u6 [31,12] [10,26,261,263,289,368,370],u6 [242,159] [115,169,1093,1095,1097,1098,1758,1759],u6 [195] [10,14,26,115,928,1393,1396,1655],u6 [12,195] [10,26,115,218,1393,1396,1655],u6 [12,198] [10,26,215,288,496,1911,1912,1913],u6 [164,12] [10,26,218,288,289,360,555,913,915,1903],u6 [12,159] [10,16,26,115,129,218,1098,1818,1914,1915],u6 [12,38] [10,26,129,215,288,289,316,317,470,1374,1712],u6 [74,12] [10,129,215,218,288,289,315,378,379,555,989,1276],u6 [21] [10,14,16,36,75,110,115,194,360,1916,1917,1918],u6 [73,12] [10,26,75,115,129,287,288,289,354,436,555,1212,1717],u6 [262] [14,115,129,497,1624,1627,1919],u6 [55,38] [316,317,470,497,852,1128,1130,1157,1299,1920],e6 [257,24] [10,115,129,144,311,1326,1328,1905,1906,1907],u6 [312] [10,14,16,75,110,144,194,360,496,1889,1921,1922],u6 [76,24] [115,144,311,496,846,1029,1425,1923,1924,1925],u6 [41] [14,115,129,144,309,496,830,832],u6 [141,154] [10,36,129,144,169,360,496,597,775,793,812,1226,1322,1350,1926,1927],u6 [22,285] [10,14,270,356,1490,1492,1781,1928],u6 [41,24] [20,115,144,309,311,360,830,832,1929],u6 [302] [10,14,75,110,114,115,129,194,360,971,1320,1575,1930,1931],([375,0,2,3,4,5],[14,496,1932,1933],[]),u6 [141,144] [10,169,1350,1581,1594],u6 [154,76] [36,129,144,496,793,1029,1285,1425,1778,1934,1935],e6 [154,376] [14,144,195,205,793,1226,1936,1937,1938],u6 [253,154] [36,194,793,812,816,1226,1322,1939,1940],u6 [187] [10,14,115,144,775,990,993,997,1568],u6 [164,154] [10,36,129,195,775,793,800,812,1226,1322,1416,1941,1942],u6 [154,175] [20,36,115,144,496,793,807,811],u6 [255,154] [16,36,115,144,496,775,793,812,1226,1322,1943,1944],u6 [109,154] [36,75,129,144,496,775,793,1221,1226,1765]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_9 : checkNodesBT W_23 g_23 F_23 P_23_9 A_23 B_23_8 9 N_23_9 = true := by decide +kernel
def B_23_9 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_9
set_option maxRecDepth 500000 in
lemma B_23_9_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 9 xs.toFinset) B_23_9 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok (buildPoolsSubBT_sound S_23_ok) A_23_ok B_23_8_ok C_23_9
def U_23_10 : List Nat := ([14,16,75,110,115,129,194,247,288,316,356,360,378,436,496,555,742,938,967,969,986,1004,1029,1090,1093,1095,1098,1128,1130,1144,1146,1205,1226,1285,1299,1322,1326,1328,1347,1350,1636,1684,1752,1763,1765,1774,1778,1779,1781,1786,1789,1794,1797,1799,1830,1839,1840,1846,1848,1853,1858,1883,1889]++r 1945 8)
def P_23_10 : BT (Option BoundPool) := buildPoolsSubBT 11 W_23 r_23 S_23 ps_23 U_23_10
def N_23_10 : List NodeSpec := [u6 [74] [14,16,75,110,129,194,360,378,1205,1945],u6 [73] [14,75,110,129,194,436,496,1794,1946],u6 [141] [14,16,75,110,129,194,360,496,938,1347,1350],u6 [6] [14,16,129,247,360,496,1144,1146],u6 [140] [14,75,110,129,194,496,1839,1840,1947],u6 [77] [14,129,360,496,1883,1889,1948],u6 [148] [14,16,75,110,129,194,360,496,742,1752,1789,1848],u6 [109] [14,16,75,110,115,129,194,360,496,1090,1765,1789,1949],u6 [38] [14,75,129,194,316,360,496,1128,1130],u6 [22] [14,16,129,194,356,360,986],u6 [280] [16,75,110,129,194,360,496,1797,1950],u6 [76] [14,129,496,1029,1285,1778],u6 [43] [16,75,110,129,194,360,1004,1858],u6 [28] [14,16,115,129,194,496,967,969],u6 [245] [14,16,129,194,496,1774,1853,1951],u6 [20] [14,16,75,129,194,360,1763],u6 [55] [14,16,75,110,129,194,360,1299,1846],u6 [159] [14,16,115,129,496,1093,1095,1098],u6 [348] [129,194,360,496,1799,1830],u6 [169] [14,16,75,110,129,194,360,496,1636,1684],u6 [12] [14,16,75,129,288,360,555],u6 [24] [14,16,75,115,129,496,1326,1328],u6 [287] [14,16,75,110,129,194,360,496,1786,1952],u6 [285] [14,75,129,194,496,1779,1781],u6 [154] [14,16,75,110,129,194,360,496,1226,1322]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_10 : checkNodesBT W_23 g_23 F_23 P_23_10 A_23 B_23_9 10 N_23_10 = true := by decide +kernel
def B_23_10 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_10
set_option maxRecDepth 500000 in
lemma B_23_10_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 10 xs.toFinset) B_23_10 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok (buildPoolsSubBT_sound S_23_ok) A_23_ok B_23_9_ok C_23_10
def U_23_11 : List Nat := [75,110,194]
def P_23_11 : BT (Option BoundPool) := buildPoolsSubBT 11 W_23 r_23 S_23 ps_23 U_23_11
def N_23_11 : List NodeSpec := [u6 [] [75,110,194]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_11 : checkNodesBT W_23 g_23 F_23 P_23_11 A_23 B_23_10 11 N_23_11 = true := by decide +kernel
def B_23_11 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_11
set_option maxRecDepth 500000 in
lemma B_23_11_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 11 xs.toFinset) B_23_11 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok (buildPoolsSubBT_sound S_23_ok) A_23_ok B_23_10_ok C_23_11
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_23_ok : forestRootCheck r_23 g_23 [(VAR 0,24,25),(VAR 1,20,22),(VAR 2,18,22),(VAR 3,17,25),(VAR 4,6,22),(VAR 5,3,35)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_23_in : bucketContainsBT B_23_11 r_23 = true := by decide +kernel
lemma low_23 : Lower r_23 g_23 12 := lower_of_forestBT root_23_ok B_23_11_ok root_23_in

def g_orig := (d 0xeeeaeae0eea8e880)
set_option maxHeartbeats 0 in
lemma low_orig : Lower (varsOf 63) g_orig 12 := carry_of (swaps := [(0,5),(1,4),(2,3)]) (by decide +kernel) low_23
def targetFn (x : Fin 6 → Bool) : Bool := Nat.testBit (4008372960 * 2 ^ 32 + 4004046976) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def temoin : List Gate := [⟨.or,[4,2]⟩,⟨.and,[6,3]⟩,⟨.and,[4,2]⟩,⟨.or,[7,5]⟩,⟨.or,[3,6]⟩,⟨.or,[9,8]⟩,⟨.and,[5,2]⟩,⟨.or,[0,12]⟩,⟨.and,[11,0]⟩,⟨.or,[13,7]⟩,⟨.or,[1,14]⟩,⟨.and,[16,15]⟩,⟨.and,[10,17]⟩]
lemma temoin_ok : PEqualNP.MetaComplexity.Monotone2 ⟨temoin, 18⟩ := by
  intro g hg; simp [temoin] at hg; rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxHeartbeats 0 in
lemma tgt_eq_G : ∀ r : Row, targetFn (evalInput6 r) = g_orig.testBit r.val := by decide +kernel
set_option maxHeartbeats 0 in
lemma temoin_eval : ∀ r : Row, Circuit.eval ⟨temoin, 18⟩ (List.ofFn (evalInput6 r)) = g_orig.testBit r.val := by decide +kernel

end PEqualNP.Outside.L_meta_45150

open PEqualNP.Outside.L_meta_45150 in
theorem PEqualNP.Outside.L_meta_45150 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372960 * 2 ^ 32 + 4004046976) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372960 * 2 ^ 32 + 4004046976) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  exact replace_of_lower6 g_orig (by decide) (by decide) (by decide) 12 low_orig temoin 18 (by decide) temoin_ok targetFn tgt_eq_G temoin_eval
