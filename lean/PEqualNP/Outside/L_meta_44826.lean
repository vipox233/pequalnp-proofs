import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_44826
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
def evalInput (r : Row) : Fin 8 → Bool := fun i => r.val.testBit i.val
def packInput (x : Fin 8 → Bool) : Row :=
  ⟨(x 0).toNat + 2 * (x 1).toNat + 4 * (x 2).toNat + 8 * (x 3).toNat +
    16 * (x 4).toNat + 32 * (x 5).toNat + 64 * (x 6).toNat + 128 * (x 7).toNat, by
    have h0 := Bool.toNat_le (x 0); have h1 := Bool.toNat_le (x 1); have h2 := Bool.toNat_le (x 2)
    have h3 := Bool.toNat_le (x 3); have h4 := Bool.toNat_le (x 4); have h5 := Bool.toNat_le (x 5)
    have h6 := Bool.toNat_le (x 6); have h7 := Bool.toNat_le (x 7); omega⟩
lemma evalInput_packInput (x : Fin 8 → Bool) : evalInput (packInput x) = x := by
  funext i
  have h : ∀ (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) (j : Fin 8),
      ((b0.toNat + 2 * b1.toNat + 4 * b2.toNat + 8 * b3.toNat +
        16 * b4.toNat + 32 * b5.toNat + 64 * b6.toNat + 128 * b7.toNat).testBit j.val) =
        ([b0, b1, b2, b3, b4, b5, b6, b7].getD j.val false) := by decide +kernel
  have hi := h (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) i
  fin_cases i <;> simpa [evalInput, packInput] using hi
lemma var_testBit (i : Fin 8) (r : Row) : (VAR i.val).testBit r.val = r.val.testBit i.val := by
  revert i r; decide +kernel
lemma sw_extract_full (T : Nat) (hT0 : T ≠ 0) (hTlt : T < 2^256) (hTb0 : T.testBit 0 = false)
    (gs : List Gate) (o : Nat)
    (legal : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (he : ∀ r : Row, Circuit.eval ⟨gs, o⟩ (List.ofFn (evalInput r)) = T.testBit r.val) :
    ∃ k S, k ≤ gs.countP isBin ∧ Live T k S ∧ ∀ a ∈ S, a ∈ varsOf 255 := by
  let seeds : List SWire := (varsOf 255).map (fun v => (false, v))
  have hseeds_lt : ∀ u ∈ seeds, u.2 < 2^256 ∧ u.2.testBit 0 = false := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
    have hall : (varsOf 255).all (fun a => decide (a < 2^256) && !a.testBit 0) = true := by decide +kernel
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
  have hread_seeds (r : Row) : seeds.map (swRead r.val) = List.ofFn (evalInput r) := by
    apply List.ext_getElem
    · simp only [seeds, List.length_map, List.length_ofFn]; decide
    · intro i hi1 hi2
      have hi8 : i < 8 := by simpa using hi2
      have hv : (varsOf 255)[i]? = some (VAR i) := by
        interval_cases i <;> decide
      simp only [List.getElem_map, List.getElem_ofFn, seeds, evalInput, swRead, Bool.false_bne]
      have hget : (varsOf 255)[i]'(by simpa [seeds] using hi1) = VAR i := by
        have := List.getElem?_eq_some_iff.mp hv; exact this.2
      rw [hget]
      exact var_testBit ⟨i, hi8⟩ r
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
lemma replace_of_lower (T : Nat) (hT0 : T ≠ 0) (hTlt : T < 2^256) (hTb0 : T.testBit 0 = false)
    (L : Nat) (hLow : Lower (varsOf 255) T L)
    (wit : List Gate) (wo : Nat) (hwLen : wit.length ≤ L + 1)
    (hwMono : ∀ g ∈ wit, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (edgeFn : (Fin 8 → Bool) → Bool)
    (hEdgeT : ∀ r : Row, edgeFn (evalInput r) = T.testBit r.val)
    (hwEvalR : ∀ r : Row, Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput r)) = T.testBit r.val)
    (gates : List Gate) (o : Nat)
    (legal : ∀ g ∈ gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (spec : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = edgeFn x) :
    ∃ (gates' : List Gate) (o' : Nat),
      (∀ g ∈ gates', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧
      ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = edgeFn x := by
  have hwEval : ∀ x : Fin 8 → Bool, Circuit.eval ⟨wit, wo⟩ (List.ofFn x) = edgeFn x := by
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
    have hsup : Supply ((varsOf 255).map obs) (S.toList.map obs) := fun v hv => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
      exact Or.inl (List.mem_map_of_mem (hsub a (Finset.mem_toList.mp ha)))
    obtain ⟨q, next, hq, hav, hbound⟩ :=
      contraction (obs_not_const hT0 hTlt hTb0) hrun ((varsOf 255).map obs)
        (show Reach ((varsOf 255).map obs) 0 ((varsOf 255).map obs) from rfl) hsup
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


def g_0 := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
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
def ps_0 : BT (Option PoolSpec) := btOfList 1 ((([] : List PoolSpec)).map some)
def B_0_2 : BT (List (List Nat)) := BT.empty
lemma B_0_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_0 2 xs.toFinset) B_0_2 := .empty
def P_0_3 : BT (Option BoundPool) := buildPoolsSubBT 1 W_0 r_0 S_0 ps_0 []
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
def g_1 := 0xfee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8
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
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_1_1 : Slice r_1 g_1 (subcubeFast 2 0) 4 := by
  have hc : Lower (varsOf 13) 0xfaa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_1_2 : Slice r_1 g_1 (subcubeFast 4 0) 4 := by
  have hc : Lower (varsOf 11) 0xee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_1_3 : Slice r_1 g_1 (subcubeFast 8 0) 4 := by
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) low_0
def S_1 : BT (Option (Nat × Nat)) := btOfList 2 [some (subcubeFast 1 0,4),some (subcubeFast 2 0,4),some (subcubeFast 4 0,4),some (subcubeFast 8 0,4)]
lemma S_1_ok : btAll (fun o => ∀ p, o = some p → Slice r_1 g_1 p.1 p.2) S_1 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_1_0) (forall_cons (fun _ h => by cases h; exact sl_1_1) (forall_cons (fun _ h => by cases h; exact sl_1_2) (forall_cons (fun _ h => by cases h; exact sl_1_3) (fun _ h => (List.not_mem_nil h).elim)))))
def ps_1 : BT (Option PoolSpec) := btOfList 2 ((([(2,[]),(1,[]),(3,[]),(0,[])] : List PoolSpec)).map some)
def B_1_2 : BT (List (List Nat)) := BT.empty
lemma B_1_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_1 2 xs.toFinset) B_1_2 := .empty
def P_1_3 : BT (Option BoundPool) := buildPoolsSubBT 2 W_1 r_1 S_1 ps_1 [0,1]
def N_1_3 : List NodeSpec := [([6,0,1,2],[],[]),([0,7,8,9],[0,1],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_1_3 : checkNodesBT W_1 g_1 F_1 P_1_3 A_1 B_1_2 3 N_1_3 = true := by decide +kernel
def B_1_3 : BT (List (List Nat)) := buildBucketsBT W_1 N_1_3
set_option maxRecDepth 500000 in
lemma B_1_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_1 3 xs.toFinset) B_1_3 :=
  buildBucketsBT_sound (by decide) gp_1 W_1_ok (buildPoolsSubBT_sound S_1_ok) A_1_ok B_1_2_ok C_1_3
def P_1_4 : BT (Option BoundPool) := buildPoolsSubBT 2 W_1 r_1 S_1 ps_1 [1,2,3]
def N_1_4 : List NodeSpec := [([0,1,2,5,3],[2],[0]),([10,0,1,2,3],[],[]),([0,1,2,11,8],[1,3],[10])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_1_4 : checkNodesBT W_1 g_1 F_1 P_1_4 A_1 B_1_3 4 N_1_4 = true := by decide +kernel
def B_1_4 : BT (List (List Nat)) := buildBucketsBT W_1 N_1_4
set_option maxRecDepth 500000 in
lemma B_1_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_1 4 xs.toFinset) B_1_4 :=
  buildBucketsBT_sound (by decide) gp_1 W_1_ok (buildPoolsSubBT_sound S_1_ok) A_1_ok B_1_3_ok C_1_4
def P_1_5 : BT (Option BoundPool) := buildPoolsSubBT 2 W_1 r_1 S_1 ps_1 [0,1,2,3]
def N_1_5 : List NodeSpec := [([0,1,4,2,3],[0,1,2,3],[0,1,3,5,7,9])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_1_5 : checkNodesBT W_1 g_1 F_1 P_1_5 A_1 B_1_4 5 N_1_5 = true := by decide +kernel
def B_1_5 : BT (List (List Nat)) := buildBucketsBT W_1 N_1_5
set_option maxRecDepth 500000 in
lemma B_1_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_1 5 xs.toFinset) B_1_5 :=
  buildBucketsBT_sound (by decide) gp_1 W_1_ok (buildPoolsSubBT_sound S_1_ok) A_1_ok B_1_4_ok C_1_5
def P_1_6 : BT (Option BoundPool) := buildPoolsSubBT 2 W_1 r_1 S_1 ps_1 [0,1,2,3]
def N_1_6 : List NodeSpec := [([0,1,2,3],[0,1,2,3],[0,2,4,6,8,11])]
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
def g_2 := 0xe880e880e880e880e880e880e880e880e880e880e880e880e880e880e880e880
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
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_2_1 : Slice r_2 g_2 (subcubeFast 0 2) 4 := by
  have hc : Lower (varsOf 13) 0xfaa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_2_2 : Slice r_2 g_2 (subcubeFast 0 4) 4 := by
  have hc : Lower (varsOf 11) 0xee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_2_3 : Slice r_2 g_2 (subcubeFast 0 8) 4 := by
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) low_0
def S_2 : BT (Option (Nat × Nat)) := btOfList 2 [some (subcubeFast 0 1,4),some (subcubeFast 0 2,4),some (subcubeFast 0 4,4),some (subcubeFast 0 8,4)]
lemma S_2_ok : btAll (fun o => ∀ p, o = some p → Slice r_2 g_2 p.1 p.2) S_2 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_2_0) (forall_cons (fun _ h => by cases h; exact sl_2_1) (forall_cons (fun _ h => by cases h; exact sl_2_2) (forall_cons (fun _ h => by cases h; exact sl_2_3) (fun _ h => (List.not_mem_nil h).elim)))))
def ps_2 : BT (Option PoolSpec) := btOfList 2 ((([(1,[]),(0,[]),(2,[]),(3,[])] : List PoolSpec)).map some)
def B_2_2 : BT (List (List Nat)) := BT.empty
lemma B_2_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_2 2 xs.toFinset) B_2_2 := .empty
def P_2_3 : BT (Option BoundPool) := buildPoolsSubBT 2 W_2 r_2 S_2 ps_2 [0,1]
def N_2_3 : List NodeSpec := [([4,5,6,3],[0,1],[]),([8,1,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_2_3 : checkNodesBT W_2 g_2 F_2 P_2_3 A_2 B_2_2 3 N_2_3 = true := by decide +kernel
def B_2_3 : BT (List (List Nat)) := buildBucketsBT W_2 N_2_3
set_option maxRecDepth 500000 in
lemma B_2_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_2 3 xs.toFinset) B_2_3 :=
  buildBucketsBT_sound (by decide) gp_2 W_2_ok (buildPoolsSubBT_sound S_2_ok) A_2_ok B_2_2_ok C_2_3
def P_2_4 : BT (Option BoundPool) := buildPoolsSubBT 2 W_2 r_2 S_2 ps_2 [0,2,3]
def N_2_4 : List NodeSpec := [([4,5,1,2,3],[0,2],[0]),([10,0,1,2,3],[],[]),([11,0,1,2,3],[3],[9])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_2_4 : checkNodesBT W_2 g_2 F_2 P_2_4 A_2 B_2_3 4 N_2_4 = true := by decide +kernel
def B_2_4 : BT (List (List Nat)) := buildBucketsBT W_2 N_2_4
set_option maxRecDepth 500000 in
lemma B_2_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_2 4 xs.toFinset) B_2_4 :=
  buildBucketsBT_sound (by decide) gp_2 W_2_ok (buildPoolsSubBT_sound S_2_ok) A_2_ok B_2_3_ok C_2_4
def P_2_5 : BT (Option BoundPool) := buildPoolsSubBT 2 W_2 r_2 S_2 ps_2 [0,1,2,3]
def N_2_5 : List NodeSpec := [([4,0,1,2,3],[0,1,2,3],[0,1,4,5,8,10])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_2_5 : checkNodesBT W_2 g_2 F_2 P_2_5 A_2 B_2_4 5 N_2_5 = true := by decide +kernel
def B_2_5 : BT (List (List Nat)) := buildBucketsBT W_2 N_2_5
set_option maxRecDepth 500000 in
lemma B_2_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_2 5 xs.toFinset) B_2_5 :=
  buildBucketsBT_sound (by decide) gp_2 W_2_ok (buildPoolsSubBT_sound S_2_ok) A_2_ok B_2_4_ok C_2_5
def P_2_6 : BT (Option BoundPool) := buildPoolsSubBT 2 W_2 r_2 S_2 ps_2 [0,1,2,3]
def N_2_6 : List NodeSpec := [([0,1,2,3],[0,1,2,3],[0,2,3,6,7,8])]
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
def g_3 := 0xfc80fc80fc80fc80fc80fc80fc80fc80fc80fc80fc80fc80fc80fc80fc80fc80
def r_3 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_3 : Lower r_3 g_3 5 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,6,7)]) (by decide +kernel) hc
def g_4 := 0xf880f880f880f880f880f880f880f880f880f880f880f880f880f880f880f880
def r_4 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_4 : Lower r_4 g_4 5 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,6,7)]) (by decide +kernel) hc
def g_5 := 0xffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8
def r_5 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_5 : Lower r_5 g_5 5 := by
  exact lift_of_f (z := 8) (o := 0) (other := r_0) (G := g_0) (essPairs := [(VAR 3,0,8)]) (by decide +kernel) low_0
def g_6 := 0xfe80fe80fe80fe80fe80fe80fe80fe80fe80fe80fe80fe80fe80fe80fe80fe80
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
def ps_6 : BT (Option PoolSpec) := btOfList 1 ((([] : List PoolSpec)).map some)
def B_6_1 : BT (List (List Nat)) := BT.empty
lemma B_6_1_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_6 1 xs.toFinset) B_6_1 := .empty
def P_6_2 : BT (Option BoundPool) := buildPoolsSubBT 1 W_6 r_6 S_6 ps_6 []
def N_6_2 : List NodeSpec := [([6,0,1],[],[]),([9,0,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_6_2 : checkNodesBT W_6 g_6 F_6 P_6_2 A_6 B_6_1 2 N_6_2 = true := by decide +kernel
def B_6_2 : BT (List (List Nat)) := buildBucketsBT W_6 N_6_2
set_option maxRecDepth 500000 in
lemma B_6_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_6 2 xs.toFinset) B_6_2 :=
  buildBucketsBT_sound (by decide) gp_6 W_6_ok (buildPoolsSubBT_sound S_6_ok) A_6_ok B_6_1_ok C_6_2
def P_6_3 : BT (Option BoundPool) := buildPoolsSubBT 1 W_6 r_6 S_6 ps_6 []
def N_6_3 : List NodeSpec := [([10,11,1,2],[],[3]),([13,0,1,3],[],[]),([15,1,2,3],[],[]),([16,1,2,12],[],[3]),([0,1,17,3],[],[]),([18,1,2,3],[],[]),([19,20,1,3],[],[2]),([22,1,2,3],[],[]),([0,1,24,3],[],[]),([25,26,2,3],[],[4])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_6_3 : checkNodesBT W_6 g_6 F_6 P_6_3 A_6 B_6_2 3 N_6_3 = true := by decide +kernel
def B_6_3 : BT (List (List Nat)) := buildBucketsBT W_6 N_6_3
set_option maxRecDepth 500000 in
lemma B_6_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_6 3 xs.toFinset) B_6_3 :=
  buildBucketsBT_sound (by decide) gp_6 W_6_ok (buildPoolsSubBT_sound S_6_ok) A_6_ok B_6_2_ok C_6_3
def P_6_4 : BT (Option BoundPool) := buildPoolsSubBT 1 W_6 r_6 S_6 ps_6 []
def N_6_4 : List NodeSpec := [([27,0,1,2,3],[],[4]),([10,0,1,2,3],[],[0]),([0,1,2,3,12],[],[0,1,2,4]),([16,0,1,2,3],[],[0,1,3,5]),([19,0,1,2,3],[],[0,1,3]),([0,1,26,2,3],[],[0]),([25,0,1,2,3],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_6_4 : checkNodesBT W_6 g_6 F_6 P_6_4 A_6 B_6_3 4 N_6_4 = true := by decide +kernel
def B_6_4 : BT (List (List Nat)) := buildBucketsBT W_6 N_6_4
set_option maxRecDepth 500000 in
lemma B_6_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_6 4 xs.toFinset) B_6_4 :=
  buildBucketsBT_sound (by decide) gp_6 W_6_ok (buildPoolsSubBT_sound S_6_ok) A_6_ok B_6_3_ok C_6_4
def P_6_5 : BT (Option BoundPool) := buildPoolsSubBT 1 W_6 r_6 S_6 ps_6 []
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
def g_7 := 0xfff8e880fff8e880fff8e880fff8e880fff8e880fff8e880fff8e880fff8e880
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
  have hc : Lower (varsOf 30) 0xfffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_1 : Slice r_7 g_7 (subcubeFast 0 2) 7 := by
  have hc : Lower (varsOf 29) 0xfffafaa0fffafaa0fffafaa0fffafaa0fffafaa0fffafaa0fffafaa0fffafaa0 7 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_2 : Slice r_7 g_7 (subcubeFast 16 0) 7 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_2
set_option maxHeartbeats 0 in
lemma sl_7_3 : Slice r_7 g_7 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) 0xfff0a000fff0a000fff0a000fff0a000fff0a000fff0a000fff0a000fff0a000 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_4 : Slice r_7 g_7 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) 0xff888800ff888800ff888800ff888800ff888800ff888800ff888800ff888800 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_5 : Slice r_7 g_7 (subcubeFast 0 4) 5 := by
  have hc : Lower (varsOf 27) 0xffffee88ffffee88ffffee88ffffee88ffffee88ffffee88ffffee88ffffee88 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_6 : Slice r_7 g_7 (subcubeFast 8 0) 5 := by
  have hc : Lower (varsOf 23) 0xf8f88080f8f88080f8f88080f8f88080f8f88080f8f88080f8f88080f8f88080 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_7 : Slice r_7 g_7 (subcubeFast 0 8) 5 := by
  have hc : Lower (varsOf 23) 0xffffe8e8ffffe8e8ffffe8e8ffffe8e8ffffe8e8ffffe8e8ffffe8e8ffffe8e8 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_8 : Slice r_7 g_7 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) 0xfff0c000fff0c000fff0c000fff0c000fff0c000fff0c000fff0c000fff0c000 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_9 : Slice r_7 g_7 (subcubeFast 16 8) 4 := by
  exact slice_fast_direct_f (z := 16) (o := 8) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_7_10 : Slice r_7 g_7 (subcubeFast 16 4) 4 := by
  have hc : Lower (varsOf 11) 0xee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_11 : Slice r_7 g_7 (subcubeFast 16 2) 4 := by
  have hc : Lower (varsOf 13) 0xfaa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_12 : Slice r_7 g_7 (subcubeFast 8 2) 4 := by
  have hc : Lower (varsOf 21) 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0fafaa0a0 4 := carry_of (swaps := [(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 8) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_13 : Slice r_7 g_7 (subcubeFast 4 2) 4 := by
  have hc : Lower (varsOf 25) 0xffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00 4 := carry_of (swaps := [(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_14 : Slice r_7 g_7 (subcubeFast 16 1) 4 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_15 : Slice r_7 g_7 (subcubeFast 8 1) 4 := by
  have hc : Lower (varsOf 22) 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0 4 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 8) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_16 : Slice r_7 g_7 (subcubeFast 4 1) 4 := by
  have hc : Lower (varsOf 26) 0xffcccc00ffcccc00ffcccc00ffcccc00ffcccc00ffcccc00ffcccc00ffcccc00 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_17 : Slice r_7 g_7 (subcubeFast 2 1) 4 := by
  have hc : Lower (varsOf 28) 0xfff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 2) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_18 : Slice r_7 g_7 (subcubeFast 1 2) 4 := by
  have hc : Lower (varsOf 28) 0xfff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_7_19 : Slice r_7 g_7 (identDom 2 3) 6 := by
  have hc : Lower (varsOf 23) 0xf8f8e0e0f8f8e0e0f8f8e0e0f8f8e0e0f8f8e0e0f8f8e0e0f8f8e0e0f8f8e0e0 6 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_6
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
def S_7 : BT (Option (Nat × Nat)) := btOfList 5 [some (subcubeFast 0 1,7),some (subcubeFast 0 2,7),some (subcubeFast 16 0,7),some (subcubeFast 2 0,5),some (subcubeFast 4 0,5),some (subcubeFast 0 4,5),some (subcubeFast 8 0,5),some (subcubeFast 0 8,5),some (subcubeFast 1 0,5),some (subcubeFast 16 8,4),some (subcubeFast 16 4,4),some (subcubeFast 16 2,4),some (subcubeFast 8 2,4),some (subcubeFast 4 2,4),some (subcubeFast 16 1,4),some (subcubeFast 8 1,4),some (subcubeFast 4 1,4),some (subcubeFast 2 1,4),some (subcubeFast 1 2,4),some (identDom 2 3,6)]
lemma S_7_ok : btAll (fun o => ∀ p, o = some p → Slice r_7 g_7 p.1 p.2) S_7 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_7_0) (forall_cons (fun _ h => by cases h; exact sl_7_1) (forall_cons (fun _ h => by cases h; exact sl_7_2) (forall_cons (fun _ h => by cases h; exact sl_7_3) (forall_cons (fun _ h => by cases h; exact sl_7_4) (forall_cons (fun _ h => by cases h; exact sl_7_5) (forall_cons (fun _ h => by cases h; exact sl_7_6) (forall_cons (fun _ h => by cases h; exact sl_7_7) (forall_cons (fun _ h => by cases h; exact sl_7_8) (forall_cons (fun _ h => by cases h; exact sl_7_9) (forall_cons (fun _ h => by cases h; exact sl_7_10) (forall_cons (fun _ h => by cases h; exact sl_7_11) (forall_cons (fun _ h => by cases h; exact sl_7_12) (forall_cons (fun _ h => by cases h; exact sl_7_13) (forall_cons (fun _ h => by cases h; exact sl_7_14) (forall_cons (fun _ h => by cases h; exact sl_7_15) (forall_cons (fun _ h => by cases h; exact sl_7_16) (forall_cons (fun _ h => by cases h; exact sl_7_17) (forall_cons (fun _ h => by cases h; exact sl_7_18) (forall_cons (fun _ h => by cases h; exact sl_7_19) (fun _ h => (List.not_mem_nil h).elim)))))))))))))))))))))
def ps_7 : BT (Option PoolSpec) := btOfList 9 ((([(1,[(0,2,3),(1,6,9),(1,2,3)]),(1,[]),(0,[]),(4,[(0,1,0)]),(6,[(0,1,0)]),(19,[]),(19,[(0,0,1),(0,6,5),(1,57,4)]),(5,[]),(7,[]),(4,[]),(19,[(0,0,1),(2,6,4)]),(1,[(0,2,3),(1,6,9)]),(8,[]),(3,[]),(1,[(1,6,4),(1,2,4),(0,0,41)]),(19,[(0,0,1),(3,6,5)]),(2,[(0,2,3),(1,2,3)]),(0,[(0,2,3),(1,9,4),(1,2,3)]),(1,[(0,2,3),(1,9,4),(1,2,3)]),(1,[(0,2,3),(1,2,3)]),(19,[(0,0,1),(0,0,5)]),(6,[]),(0,[(1,6,3),(1,6,4),(1,3,4)]),(2,[(0,0,1),(1,6,3)]),(0,[(1,6,2),(1,6,3),(1,2,3)]),(12,[]),(9,[]),(5,[(2,0,4)]),(2,[(0,0,1),(0,6,3),(3,33,41)]),(19,[(0,0,1),(2,0,4)]),(2,[]),(19,[(0,0,1),(1,6,4)]),(19,[(2,1,4),(3,92,0)]),(1,[(1,2,3)]),(0,[(1,2,3)]),(0,[(0,6,2),(1,11,4)]),(1,[(0,6,2),(1,11,4)]),(0,[(1,6,2),(1,30,3),(2,73,4)]),(2,[(0,0,3)]),(2,[(0,0,1),(0,6,40),(3,114,2)]),(0,[(1,6,2),(1,30,4),(3,3,31)]),(15,[]),(3,[(0,0,3)]),(0,[(0,2,3),(1,6,9),(1,2,3)]),(0,[(1,2,3),(1,5,4),(3,6,72)]),(19,[(0,0,1),(0,6,5)]),(0,[(0,6,3),(1,33,4)]),(1,[(0,6,3),(1,33,4)]),(2,[(0,0,1),(0,6,3)]),(10,[]),(0,[(0,1,2),(1,21,4)]),(1,[(1,2,4)]),(0,[(1,2,4)]),(0,[(1,26,3),(1,26,4),(1,3,4)]),(2,[(0,0,2),(1,26,3)]),(2,[(0,1,3),(0,28,41),(3,138,0)]),(0,[(1,3,4),(0,2,40)]),(2,[(0,0,2),(0,0,40),(0,2,40)]),(0,[(1,26,4),(1,3,4),(0,2,40)]),(2,[(0,2,3),(1,2,3),(3,145,5)]),(19,[(0,1,5),(3,95,0)]),(0,[(1,2,4),(0,3,41)]),(2,[(0,3,41),(2,0,53)]),(0,[(1,2,4),(3,3,41)]),(2,[(0,0,41)]),(2,[(0,0,41),(0,3,41)]),(0,[(1,2,4),(0,1,41)]),(0,[(1,3,4),(0,1,40)]),(2,[(0,1,40),(3,150,0)]),(2,[(2,2,3),(3,84,3)]),(0,[(2,2,3),(1,2,4)]),(2,[(2,3,2),(3,109,40)]),(13,[]),(2,[(1,3,2),(0,2,40)]),(0,[(0,2,3),(1,2,3)]),(19,[(0,0,5)]),(19,[(1,9,4)]),(1,[(1,3,4)]),(2,[(0,1,40),(3,150,2)]),(0,[(0,2,3),(1,9,4)]),(0,[(1,2,3),(0,1,5)]),(2,[(0,2,3),(3,9,2),(1,75,3)]),(0,[(0,2,3),(3,9,2),(1,75,3)]),(0,[(1,2,3),(2,5,4)]),(2,[(1,2,3)]),(19,[(2,0,4)]),(17,[]),(1,[(3,92,0)]),(2,[(3,92,0)]),(0,[(0,2,3),(1,6,9)]),(0,[(2,2,4),(1,84,6)]),(1,[(1,2,3),(0,0,5)]),(1,[(0,2,3)]),(4,[(0,0,1)]),(3,[(2,0,4)]),(2,[(0,2,3)]),(1,[(2,0,4)]),(1,[(0,0,3)]),(1,[(2,2,4)]),(2,[(0,0,1),(0,0,3)]),(2,[(3,3,41)]),(2,[(0,0,1),(3,3,7)]),(0,[(1,6,4),(3,3,7)]),(0,[(2,2,3),(1,75,6)]),(0,[(2,3,4),(1,116,2)]),(3,[(0,0,2)]),(1,[(0,0,2)]),(2,[(0,0,1),(0,0,2)]),(1,[(1,92,3)]),(0,[(2,1,4),(1,92,3)]),(2,[(0,0,1)]),(1,[(1,6,4)]),(0,[(1,6,4)]),(0,[(1,6,4),(1,2,4)]),(1,[(1,6,4),(1,2,4)]),(14,[]),(1,[(2,2,3)]),(19,[(0,0,1)]),(0,[(1,20,4)]),(1,[(0,0,3),(1,20,4)]),(0,[(2,2,3),(3,75,2),(1,9,4)]),(1,[(2,2,3),(3,75,2),(1,9,4)]),(2,[(0,0,1),(3,6,3)]),(1,[(1,2,4),(3,28,41)]),(2,[(0,1,3),(3,28,41)]),(0,[(1,6,2),(1,30,3)]),(2,[(0,0,2),(3,26,3)]),(0,[(3,26,3),(1,122,4)]),(2,[(2,1,2),(3,158,0)]),(7,[(2,0,4)]),(0,[(0,1,2),(1,20,21)]),(1,[(0,0,3),(1,20,21)]),(16,[]),(0,[(1,2,3),(1,18,4)]),(1,[(1,2,3),(0,0,5),(1,18,4)]),(0,[(3,6,3),(1,79,2)]),(0,[(0,6,3),(3,33,2)]),(1,[(0,6,3),(3,33,2)]),(2,[(0,0,1),(0,6,3),(3,33,2)]),(1,[(2,0,3),(2,0,4),(3,19,3)]),(2,[(2,0,3),(3,19,3)]),(0,[(1,6,2),(2,2,3)]),(1,[(0,2,3),(1,9,4)]),(2,[(0,0,1),(0,6,2)]),(2,[(0,1,3),(3,28,2)]),(1,[(3,28,2),(1,2,4)]),(8,[(0,1,3)]),(0,[(0,1,3)]),(6,[(0,0,1)]),(2,[(0,0,2),(0,26,40)]),(0,[(3,6,2),(1,2,3)]),(1,[(3,6,2),(1,2,3)]),(2,[(0,0,1),(3,6,2)]),(2,[(0,0,3),(3,3,41)]),(0,[(3,6,2),(1,2,4)]),(0,[(1,2,3),(3,6,5)]),(0,[(2,3,4),(1,116,26)]),(0,[(2,1,2),(1,158,4)]),(0,[(3,6,2)]),(1,[(3,6,2)]),(0,[(1,6,2),(1,6,3)]),(0,[(0,6,2)]),(1,[(0,6,2)]),(0,[(1,6,2),(1,6,4)]),(2,[(2,0,3),(0,3,41)]),(0,[(3,6,2),(1,81,4)]),(1,[(3,167,2),(1,168,4)]),(7,[(1,168,4)]),(2,[(2,1,3),(3,167,2)]),(1,[(1,6,2),(0,0,2)]),(0,[(1,6,3),(1,3,4)]),(0,[(1,6,3),(1,3,2)]),(8,[(0,1,2)]),(0,[(0,1,2)]),(2,[(0,1,0),(0,1,2)]),(1,[(1,21,4)]),(2,[(0,0,1),(1,6,2)]),(0,[(1,6,2),(2,30,4)]),(0,[(1,6,2),(2,2,4)]),(0,[(1,26,4)]),(1,[(0,0,2),(1,26,4)]),(7,[(1,2,4)]),(1,[(3,6,2),(1,2,4)]),(0,[(1,6,2),(2,30,3)]),(1,[(3,6,2),(1,81,4)]),(2,[(2,1,3),(3,167,0)]),(0,[(0,6,2),(1,11,3)]),(1,[(0,6,2),(1,11,3)]),(2,[(0,0,1),(0,6,2),(1,11,3)]),(0,[(2,6,4)]),(1,[(2,6,4)]),(5,[(1,3,4)]),(2,[(1,3,2)]),(0,[(1,3,2),(1,3,4)]),(0,[(1,6,2),(1,30,4)]),(7,[(2,2,4)]),(0,[(1,2,3),(2,2,4)]),(1,[(2,2,3),(1,75,6)]),(0,[(1,2,3),(1,5,4)]),(2,[(0,1,3)]),(0,[(2,2,3),(1,75,3)]),(0,[(0,26,3),(1,173,4)]),(2,[(0,1,2)]),(2,[(2,2,3)]),(2,[(0,0,1),(0,6,41)]),(0,[(0,1,3),(1,28,4)]),(0,[(1,2,4),(3,6,41)]),(2,[(0,0,1),(3,6,41)]),(1,[(1,2,4),(3,6,41)]),(1,[(1,2,4),(0,0,41)]),(2,[(0,0,1),(0,0,41)]),(1,[(3,28,2),(1,88,4)]),(1,[(3,28,0)]),(2,[(0,1,3),(3,28,0)]),(1,[(1,6,2),(2,2,3)]),(0,[(2,2,3),(1,75,4)]),(1,[(0,21,3),(3,176,0)]),(2,[(0,1,2),(0,21,3),(3,176,0)]),(2,[(0,0,2),(0,26,3)]),(1,[(0,0,2),(0,26,3),(1,173,4)]),(0,[(1,26,3),(1,125,4)]),(0,[(1,20,2),(1,20,4)]),(0,[(1,26,3),(1,3,4)]),(0,[(1,20,2),(2,2,4)]),(2,[(1,2,3),(0,0,72)]),(2,[(0,0,3),(1,20,2)]),(0,[(1,20,2),(2,127,4)]),(2,[(0,0,2)]),(11,[]),(0,[(1,26,4),(1,3,4)]),(2,[(0,0,2),(3,3,27)]),(0,[(1,26,4),(3,3,27)]),(1,[(1,167,4)]),(2,[(2,1,3)]),(0,[(2,1,3),(1,167,4)]),(0,[(3,3,2),(1,75,20)]),(0,[(1,3,4),(3,2,40)]),(2,[(3,2,40),(3,142,0)]),(2,[(0,0,2),(0,0,40)]),(0,[(1,3,4)]),(2,[(0,0,2),(0,2,40)]),(0,[(2,1,4),(1,92,2)]),(2,[(2,1,2),(3,158,40)]),(0,[(2,3,4),(3,116,2)]),(1,[(2,3,4),(1,116,2)]),(0,[(2,3,4)]),(18,[]),(1,[(1,2,4),(3,3,41)]),(1,[(2,2,3),(1,2,4)]),(1,[(2,2,3),(1,75,4)]),(0,[(2,3,2)]),(2,[(2,3,2),(3,109,0)]),(1,[(2,3,2),(3,109,0)]),(1,[(1,2,3),(2,5,4)]),(1,[(1,2,3),(1,5,4)]),(2,[(1,2,3),(0,0,5)]),(1,[(1,3,2),(1,3,4)]),(2,[(2,0,3)]),(2,[(2,2,3),(3,75,2)]),(0,[(2,2,3),(3,75,2)]),(1,[(3,28,2)]),(0,[(1,19,2)]),(1,[(2,0,4),(1,19,2)]),(2,[(1,19,2)]),(0,[(1,20,2)]),(1,[(0,0,3),(1,20,2)]),(0,[(2,1,3)]),(0,[(1,26,3)]),(1,[(0,0,2),(1,26,3)]),(0,[(2,2,4)]),(0,[(2,26,3)]),(0,[(2,2,3)]),(0,[(1,6,2)]),(1,[(1,6,2)]),(0,[(2,26,4)]),(0,[(2,6,3)]),(0,[(2,1,2)]),(1,[(3,158,0)]),(1,[(1,3,4),(0,2,40)]),(2,[(0,2,40)]),(0,[(0,2,3)]),(1,[(3,92,2)]),(2,[(3,92,2)]),(0,[(0,26,3)]),(1,[(0,0,2),(0,26,3)]),(0,[(3,3,2)]),(2,[(2,1,2)]),(1,[(0,2,3),(2,0,9)]),(2,[(0,2,3),(2,0,9)]),(1,[(3,167,2)]),(0,[(2,1,3),(3,167,2)]),(0,[(2,131,2)]),(0,[(1,131,4)]),(1,[(2,0,3),(1,131,4)]),(1,[(2,0,3)]),(1,[(2,2,3),(1,75,3)]),(2,[(2,2,3),(1,75,3)]),(0,[(2,1,4)]),(0,[(1,131,2)]),(0,[(2,131,4)]),(2,[(0,2,3),(3,9,2)]),(0,[(0,2,3),(3,9,2)]),(1,[(1,2,3),(2,2,4)])] : List PoolSpec)).map some)
def B_7_2 : BT (List (List Nat)) := BT.empty
lemma B_7_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_7 2 xs.toFinset) B_7_2 := .empty
def P_7_3 : BT (Option BoundPool) := buildPoolsSubBT 9 W_7 r_7 S_7 ps_7 []
def N_7_3 : List NodeSpec := [([0,1,8,10],[],[]),([15,0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_7_3 : checkNodesBT W_7 g_7 F_7 P_7_3 A_7 B_7_2 3 N_7_3 = true := by decide +kernel
def B_7_3 : BT (List (List Nat)) := buildBucketsBT W_7 N_7_3
set_option maxRecDepth 500000 in
lemma B_7_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_7 3 xs.toFinset) B_7_3 :=
  buildBucketsBT_sound (by decide) gp_7 W_7_ok (buildPoolsSubBT_sound S_7_ok) A_7_ok B_7_2_ok C_7_3
def P_7_4 : BT (Option BoundPool) := buildPoolsSubBT 9 W_7 r_7 S_7 ps_7 [0,1,2,3,4,5,6]
def N_7_4 : List NodeSpec := [([17,0,1,5,4],[],[]),([18,1,16,5,4],[0],[]),([19,1,16,5,4],[0],[]),([23,6,2,3,4],[],[]),([6,2,3,4,25],[1,2],[]),([6,2,3,27,29],[3,4],[]),([32,0,2,3,29],[],[]),([0,1,35,3,36],[],[1]),([37,0,1,2,34],[],[]),([38,0,1,5,4],[],[]),([0,1,5,4,39],[5],[]),([0,1,2,8,40],[],[]),([37,42,1,2,43],[],[]),([44,0,1,2,4],[],[]),([42,45,2,3,7],[],[]),([48,0,1,2,4],[],[]),([51,1,52,3,4],[],[]),([42,1,2,53,43],[],[]),([0,1,9,8,4],[5],[0]),([0,1,55,4,56],[5],[]),([0,1,9,5,58],[6],[]),([0,1,55,7,40],[],[]),([0,1,60,5,4],[],[]),([61,0,1,2,4],[],[]),([62,63,0,1,3],[],[1]),([0,1,5,7,10],[],[0]),([0,1,64,65,4],[5],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_7_4 : checkNodesBT W_7 g_7 F_7 P_7_4 A_7 B_7_3 4 N_7_4 = true := by decide +kernel
def B_7_4 : BT (List (List Nat)) := buildBucketsBT W_7 N_7_4
set_option maxRecDepth 500000 in
lemma B_7_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_7 4 xs.toFinset) B_7_4 :=
  buildBucketsBT_sound (by decide) gp_7 W_7_ok (buildPoolsSubBT_sound S_7_ok) A_7_ok B_7_3_ok C_7_4
def P_7_5 : BT (Option BoundPool) := buildPoolsSubBT 9 W_7 r_7 S_7 ps_7 [0,1,2,3,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60]
def N_7_5 : List NodeSpec := [([37,66,0,1,2,4],[],[]),([59,67,0,1,2,3],[7,8],[]),([59,0,1,9,5,4],[9,10],[0]),([19,1,2,16,3,4],[2,11],[0]),([68,69,0,1,3,4],[],[1]),([0,1,70,3,4,7],[8],[1]),([71,0,1,3,4,7],[],[]),([0,1,2,3,7,72],[12,13],[]),([37,0,1,2,3,7],[],[]),([42,1,2,3,7,41],[14],[0]),([0,1,64,3,4,31],[],[0,1]),([74,0,1,9,5,4],[5,9,15],[]),([0,1,2,3,76,7],[8],[]),([77,0,1,2,3,4],[],[]),([78,79,0,1,2,4],[],[]),([80,0,1,2,3,7],[2,7],[]),([0,1,60,2,3,4],[],[0]),([6,0,1,5,4,10],[16,17,18],[0]),([6,18,1,9,5,4],[7,19,20],[0]),([0,1,2,3,27,29],[9,12,13,21],[0]),([62,0,1,2,3,34],[],[0]),([81,0,1,5,4,40],[9],[]),([0,1,2,5,7,40],[],[0]),([42,1,2,3,43,41],[],[0]),([0,1,2,82,7,40],[12,13,22,23],[]),([83,6,0,2,3,4],[2],[]),([32,0,1,3,5,4],[21],[]),([0,1,30,82,5,4],[12,13,24,25],[]),([19,67,6,1,2,3],[26,27],[]),([84,79,0,1,5,4],[9],[]),([37,33,0,1,2,4],[7],[0]),([85,0,1,2,3,4],[13],[]),([86,0,1,2,3,4],[28],[]),([19,6,1,9,5,4],[16,19,29],[0]),([87,0,1,2,4,40],[21,30],[]),([0,1,2,3,89,29],[9,13,21],[]),([23,0,1,2,3,4],[],[0]),([90,0,1,2,4,7],[],[]),([91,0,1,5,4,10],[17],[]),([74,0,1,2,3,4],[],[]),([0,1,9,5,4,7],[7,9,31],[0]),([93,0,1,9,5,4],[32],[]),([94,0,1,2,27,40],[21],[]),([81,79,0,1,5,4],[9],[]),([6,18,95,2,3,4],[7,8,33,34],[]),([0,1,2,3,12,14],[9,12,13,35,36],[1]),([96,6,0,1,2,3],[37],[]),([75,0,1,3,7,41],[],[]),([0,1,2,3,4,97],[7],[]),([37,98,0,1,2,4],[],[]),([32,0,1,2,3,4],[],[]),([0,1,2,3,99,4],[],[]),([100,1,2,3,4,24],[],[]),([81,0,1,3,4,72],[12,13],[1]),([0,1,64,3,7,41],[],[1]),([83,0,1,2,3,4],[],[]),([0,1,2,3,8,4],[1,2,7,9,13],[0,1]),([81,0,1,101,3,4],[],[]),([0,1,2,3,4,25],[1,2,8,13],[0]),([102,0,1,2,3,4],[],[]),([0,1,2,3,4,103],[1,2],[]),([81,0,1,3,7,41],[12,13,30],[]),([104,0,1,2,3,4],[7],[]),([0,1,2,5,4,105],[9],[]),([106,79,0,1,2,4],[],[]),([107,0,1,2,5,4],[9,21],[]),([0,1,108,3,43,41],[38],[]),([67,81,0,1,3,4],[],[]),([37,81,0,1,3,4],[],[]),([0,1,2,110,3,4],[9],[]),([0,1,2,3,5,58],[],[0]),([0,1,2,3,4,39],[1,2,7,9],[0]),([0,1,2,3,111,7],[9,12,13],[]),([81,0,1,82,5,4],[9,12,13],[]),([113,0,1,2,3,4],[],[]),([115,0,1,3,4,40],[39],[]),([81,0,1,117,3,4],[],[]),([6,26,2,3,4,29],[3],[0,1]),([118,0,1,2,3,12],[],[1]),([90,6,0,1,2,4],[40],[]),([119,6,2,3,4,29],[41],[]),([6,22,2,3,4],[1,2,42],[0]),([32,20,1,2,3,4],[8],[2]),([37,6,20,1,2,4],[8],[]),([19,112,1,2,3,4],[],[]),([0,1,16,5,4],[0,5,43],[0,2]),([17,0,1,2,3,4],[],[0]),([6,0,1,16,5,4],[0,9,43],[]),([120,0,1,2,3,4],[2,44],[]),([37,20,42,1,2,4],[2,7],[0]),([57,0,1,9,5,4],[5,9,16,45],[0]),([0,1,2,121,4,7],[9],[1]),([74,0,1,2,4,40],[30],[]),([0,1,2,3,7,10],[9,12,13,21],[0]),([94,122,0,1,2,4],[],[]),([84,74,0,1,3,4],[],[]),([112,0,1,3,4,41],[],[]),([0,1,35,2,3,34],[12,13,21,46,47,48],[0]),([75,32,0,1,3,4],[],[]),([6,0,2,3,24,40],[3,4,49,50],[1]),([6,42,45,2,3,4],[7,51,52],[0]),([123,0,1,2,3,4],[],[]),([37,124,0,1,2,4],[],[]),([0,1,2,125,27,40],[9,12,53,54],[]),([126,0,1,2,3,4],[],[]),([51,1,2,3,4,29],[7],[0]),([38,0,1,2,3,4],[],[0]),([128,0,1,2,3,43],[2,7],[]),([129,0,1,2,4,40],[21,30],[]),([78,0,1,2,7,40],[21],[]),([88,0,1,3,29,41],[13,21,30],[]),([130,0,1,2,3,4],[],[]),([0,1,2,3,132,24],[8],[]),([37,0,1,2,43,41],[21],[0]),([0,1,108,3,4,133],[],[2,3]),([134,135,0,1,3,4],[],[1]),([137,0,1,2,3,4],[],[]),([139,1,2,3,4,41],[55],[]),([26,140,1,141,3,4],[8,56,57],[1]),([26,0,143,1,3,4],[7],[]),([67,93,0,1,2,3],[],[]),([144,0,1,5,4,10],[41],[]),([0,1,141,3,27,40],[58],[1]),([0,1,146,4],[25,41,59],[]),([84,0,1,2,3,34],[7,13],[]),([147,0,1,9,5,4],[60],[]),([0,1,2,3,12,40],[9,12,13,21,35,36],[1]),([42,0,1,3,148,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_7_5 : checkNodesBT W_7 g_7 F_7 P_7_5 A_7 B_7_4 5 N_7_5 = true := by decide +kernel
def B_7_5 : BT (List (List Nat)) := buildBucketsBT W_7 N_7_5
set_option maxRecDepth 500000 in
lemma B_7_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_7 5 xs.toFinset) B_7_5 :=
  buildBucketsBT_sound (by decide) gp_7 W_7_ok (buildPoolsSubBT_sound S_7_ok) A_7_ok B_7_4_ok C_7_5
def P_7_6 : BT (Option BoundPool) := buildPoolsSubBT 9 W_7 r_7 S_7 ps_7 [1,2,3,4,5,7,8,9,10,11,12,13,16,17,18,19,21,23,25,26,27,29,30,31,32,33,35,36,38,41,42,48,49,50,51,52,54,56,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242]
def N_7_6 : List NodeSpec := [([149,0,1,2,3,4,41],[2,8,12,61,62],[]),([37,42,0,1,2,3,4],[8,12,21,63],[0,2]),([42,0,1,2,53,3,4],[7,8,12,21,26,61,64,65],[1]),([42,0,45,1,2,3,4],[1,12,13,51,66],[0]),([151,0,1,2,3,4,40],[1,2,12,67,68],[]),([75,0,1,152,4],[9,21,25,69],[0]),([75,42,0,1,3,4,41],[70],[0]),([0,1,2,153,4,40],[8,21,71],[1,3]),([0,1,141,5,4],[8,72,73],[]),([18,0,1,9,5,4],[7,16,19,26,41,74,75],[0,2]),([0,1,9,5,4,10],[9,16,17,18,25,26,41,76],[]),([154,0,1,2,3,4,40],[8,9,77,78],[1]),([144,0,1,2,3,4,10],[12,41],[0]),([91,0,1,2,3,4,10],[12,79],[0]),([147,0,1,2,3,5,4],[1,2,12,80],[0]),([0,1,9,5,4],[5,7,25,26,81,82],[]),([19,67,0,1,2,3],[2,7,8,26,27,83,84],[0,2]),([19,0,1,9,5,4],[9,16,19,26,41,85],[0,2]),([75,93,0,1,2,3,4],[9,12,32,86,87],[]),([93,0,1,2,3,5,4],[7,12,86,88],[0]),([6,0,1,2,16,3,4],[9,11,89],[0]),([6,155,0,1,2,3,4],[1,2,9,90],[]),([6,18,1,2,3,5,4],[2,7,8,33,91],[0]),([19,6,1,9,2,3,4],[92,93,94,95,96],[0]),([84,6,20,1,2,3,4],[26,42,93,97,98,99],[]),([59,0,1,9,2,3,4],[9,13],[0]),([37,6,0,1,2,3,4],[1,2,7,8,12,13,63,100],[0,2]),([78,6,0,1,2,3,4],[8,12,13,101,102],[0]),([6,112,0,1,2,3,4],[1,2,9,103],[]),([6,0,1,2,117,3,4],[1,7,12,13,21,26,104],[0]),([6,26,1,2,3,4,40],[25,49,77,93,105,106,107],[1,2,3]),([26,0,1,2,3,156,4],[8,9,13,25,108,109],[3]),([78,0,1,2,3,4,7],[8,13,21,110],[0,1]),([81,0,1,2,3,82,4],[8,9,12,13,25],[0,1]),([68,0,1,2,3,4,7],[7,9],[0]),([0,1,2,3,4,7,31],[7,9,111,112],[0,1]),([0,1,2,3,7,41],[9,12,13,110,113,114],[0,1,2]),([0,1,9,2,3,4,7],[7,8,9,21,110],[0]),([19,75,6,1,2,3,4],[12,29,49,94,96,115,116],[0]),([6,0,1,9,5,4],[7,9,16,19,25,74,117],[0,2]),([0,1,108,2,3,4,43],[7,9,12,21,38,118,119],[0,3]),([0,1,2,3,4,10],[9,12,13,26,120,121],[]),([84,79,0,1,2,3,4],[9,21,49,122],[0,1]),([83,0,1,2,3,4],[2,7,12,13,123,124],[0]),([6,0,1,2,3,73,4],[1,110,125],[0]),([26,0,1,2,3,4,157],[7,8,9,12,126,127],[3]),([159,0,1,2,3,4,40],[7,8,12,72,86,128],[]),([19,6,1,2,3,5,4],[12,27,33,84,94,96,115,129],[0]),([0,1,22,2,3,4],[25,30,130,131,132],[0]),([0,1,2,3,4,160],[7,8,12,13,133,134],[]),([6,0,1,2,101,3,4],[1,7,12,13,135],[0]),([161,0,1,3,4],[9,21,136,137,138],[]),([145,0,1,5,4],[9,25,26],[0]),([131,1,2,162,4],[12,21,25,129,139,140],[]),([75,6,0,1,30,3,4],[9,12,13,141],[]),([163,0,1,2,3,4,24],[12,50],[]),([6,0,1,2,3,4,10],[12,13,79,95,142],[0]),([0,1,2,3,4,12],[8,9,21,35,36,143],[0,1]),([88,0,1,3,4,41],[7,9,21,30,132,144,145],[3]),([6,26,28,2,3,4],[1,2,93,105,106,146,147,148],[0,1,3]),([164,0,1,2,3,4,40],[21,30,77,149],[3]),([81,0,1,3,5,4],[9,21,150,151],[0,1]),([81,0,1,2,3,4,7],[7,9,110,152],[0,1]),([0,1,2,153,3,4],[1,2,8,12,13,21],[]),([37,20,0,1,2,4],[2,7,8,63,153],[0,1,2]),([81,6,0,1,3,4,41],[7,12,13,110,152,154],[0]),([74,0,1,2,3,4],[1,7,9,13,30,155],[0,1]),([26,165,0,1,2,3,4],[21,156],[]),([131,0,1,2,3,4,166],[8,49,72,157],[]),([81,0,1,2,3,4,40],[8,9,12,13,21,152,158,159],[0,1]),([37,20,0,1,2,4,41],[7,21,52,63,153],[0]),([0,1,2,30,3,82,4],[7,8,12,13,25,72,160],[0]),([18,0,95,1,2,3,4],[1,12,13,33,80],[0]),([11,0,1,2,3,4,40],[8,9,12,13,21,30,143,161,162],[0,1]),([0,1,2,30,3,4,7],[7,12,13,72,110,163],[0,1]),([131,0,1,2,53,4,41],[7,8,164],[]),([6,0,1,2,3,4,111],[1,7,12,13,152,165],[0]),([74,0,1,2,3,5,4],[7,9,13,21],[0]),([74,6,0,1,2,3,4],[1,2,7,155],[]),([0,1,2,3,4,169],[2,7,9,12,166,167,168],[]),([0,1,5,4,10],[9,17,18,26],[0,2]),([26,1,30,3,4],[7,12,49,169],[]),([6,0,1,2,82,4,40],[12,13,21,23,170],[0]),([6,0,1,2,82,5,4],[12,13,21,72,171],[0]),([19,6,21,2,3,4],[1,3,25,41,49,94,96,115,172,173,174],[]),([0,1,64,2,3,4,7],[7,9,12,13,110,111,112],[0,1]),([6,0,2,3,4,24],[3,4,13,49,50,174,175],[0,1]),([80,6,0,1,2,3,4],[1,2,9,12,13,176,177],[0]),([84,6,0,1,30,3,4],[9,12,13,178],[]),([0,1,2,3,4,27,170],[8,12,21,49,179,180],[1,3]),([81,0,1,3,4,41],[9,30,152,154,181,182],[0,1]),([106,6,0,1,2,3,4],[8,12,13,72,183],[0]),([84,33,0,1,2,3,4],[9,13,48,49],[0]),([57,0,1,2,3,5,4],[7,9,21,84],[0]),([0,1,2,3,5,4,7],[7,8,9,21,110],[0,1]),([0,1,2,3,4,111],[8,9,21,165,184],[1]),([84,171,0,1,2,3,4],[9,49,185],[]),([75,0,1,2,3,4,7],[7,8,9,12,13,21,31,110,111,112],[0,1]),([0,1,2,172,4],[8,9,186,187,188],[]),([59,75,0,1,2,3,4],[7,9,10,12,13,189,190],[0]),([119,0,1,2,3,4,29],[12,41],[0]),([6,0,1,2,5,4,40],[8,72,110,191,192,193],[0,1]),([0,1,2,16,3,4],[11,13,25,30,72,89,93,148],[0,2]),([6,0,1,2,3,4,31],[1,25,194],[0]),([84,6,0,1,3,5,4],[9,25,49,195,196],[0]),([112,0,1,2,3,4],[1,7,9,13,30,72,93,103,197],[0,2]),([6,0,1,2,3,4,72],[1,7,8,12,13,84,198],[0,1]),([88,0,1,2,3,4,29],[7,9,144,199],[0,3]),([6,0,1,2,3,5,4],[1,7,8,9,12,13,21,25,200],[0]),([0,1,2,3,174],[9,12,21,25,201],[]),([131,0,1,2,3,4,24],[8,12,41,50,202],[0]),([81,6,0,1,3,5,4],[7,12,13,25,150],[0]),([75,6,0,1,3,4,41],[7,9,70,203],[0]),([59,0,1,2,3,5,4],[7,8,9,13,21,110],[0]),([175,0,1,2,3,4,41],[9,26,30,204],[0,1]),([0,1,2,3,12],[9,35,36],[0,1]),([26,0,1,2,3,4,29],[7,9,12,199,205],[0,1,3]),([32,0,1,2,3,4],[1,8,13,21,206,207,208],[0,2]),([83,0,28,1,2,3,4],[1,7,13,123],[]),([32,6,0,1,2,3,4],[1,2,7,206],[]),([6,42,1,2,3,4,41],[2,7,51,209,210],[0]),([32,0,1,2,3,4,41],[9,13,207],[]),([0,1,2,3,4,89],[7,21,132,211],[]),([124,0,1,2,3,4,41],[7,12,13,41,212,213],[0]),([75,0,1,30,3,4],[7,21,49,72,141,214],[]),([6,0,1,2,3,4,76],[1,9,12,13,26,49,215],[0]),([84,124,0,1,2,3,4],[9,12,49,147,213],[]),([177,1,2,3,4],[9,12,21,216,217],[]),([0,1,2,3,4,174],[9,12,25,201,218,219],[]),([26,0,1,2,3,4,170],[7,86,106,220],[3]),([0,1,2,127,3,4,43],[7,38,132,221],[0,1]),([26,0,1,2,125,4,40],[9,12,21,54,222],[0]),([84,20,0,1,127,3,4],[9,21,223],[]),([178,1,2,3,4],[7,8,12,224],[]),([128,20,0,1,2,3,4],[9,225,226],[0]),([67,6,0,1,2,3,4],[1,2,7,12,13,26,83],[0,1,2]),([94,0,1,2,3,4,27],[8,9,21,227],[0,3]),([88,0,1,2,3,4,40],[9,21,77,191,228],[1]),([88,0,28,1,3,4,41],[7,13,21,144,145,199],[0]),([0,1,2,3,27,40],[9,12,21,49,180,229],[0,1,2]),([134,0,1,2,3,4,29],[7,9],[0]),([26,0,1,2,3,27,40],[9,12,41,49,229],[0,3]),([94,26,0,1,2,3,4],[8,9,230,231],[0]),([26,0,1,2,3,4,179],[9,13,25,26,232,233,234],[2]),([0,180,1,2,3,4],[25,26,30,235],[]),([181,0,1,2,3,4,40],[8,9,12,21,30,41,236,237],[]),([37,26,0,1,2,3,4],[8,9,63,115],[2]),([6,0,1,2,3,7,41],[12,13,30,72,113],[0,1]),([26,140,1,2,3,4,40],[2,8,49,238],[0,1]),([83,0,1,2,3,4,41],[9,13,124],[]),([81,79,0,1,2,3,4],[7,9,21],[0,1]),([26,0,1,141,3,4,40],[7,8,56,239,240],[0]),([131,0,1,2,182,3,4],[7,8,12,41,241],[]),([0,1,2,183,3,4,40],[13,242],[]),([93,0,1,9,2,3,4],[9,12,86],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_7_6 : checkNodesBT W_7 g_7 F_7 P_7_6 A_7 B_7_5 6 N_7_6 = true := by decide +kernel
def B_7_6 : BT (List (List Nat)) := buildBucketsBT W_7 N_7_6
set_option maxRecDepth 500000 in
lemma B_7_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_7 6 xs.toFinset) B_7_6 :=
  buildBucketsBT_sound (by decide) gp_7 W_7_ok (buildPoolsSubBT_sound S_7_ok) A_7_ok B_7_5_ok C_7_6
def P_7_7 : BT (Option BoundPool) := buildPoolsSubBT 9 W_7 r_7 S_7 ps_7 [1,2,5,7,8,9,12,13,16,19,21,25,26,27,30,33,34,38,41,49,51,52,54,56,63,64,70,72,74,77,79,83,84,85,86,87,88,91,92,93,95,96,97,98,100,104,105,106,107,110,111,112,115,116,117,128,132,142,143,144,147,152,158,159,161,168,176,179,180,189,193,196,198,199,200,202,203,209,212,213,215,218,225,227,233,239,243,244,245,246,247,248,249,250,251,252,253,254,255,256,257,258,259,260,261,262,263,264,265,266,267,268,269,270,271,272,273,274,275,276,277,278,279,280,281,282,283,284,285,286,287,288,289,290,291,292,293,294,295,296,297,298,299,300,301,302]
def N_7_7 : List NodeSpec := [([0,1,184,2,3,4],[2,12,21,26,30,72,243],[1]),([0,1,2,117,3,4],[7,12,13,21,26,104,244],[0]),([185,0,1,2,3,4],[1,2,7,9,12,13,21,26,245,246],[]),([37,0,1,2,3,4,41],[7,9,21,26,30,51,52,63,247],[0,1,2,3]),([37,0,1,2,3,4],[1,2,7,8,9,12,13,30,63,100,247],[0,2]),([84,0,1,2,3,41],[7,9,30,72,132],[]),([42,0,1,2,3,4],[1,2,7,8,12,13,21,52,64,132,246],[]),([84,75,0,1,3,4],[9,21,26,72,203],[0]),([75,0,1,3,4,41],[7,9,26,70,248],[0,1,2]),([186,0,1,2,3,4],[1,2,8,9,12,13,72,203],[]),([0,1,2,3,4,76],[9,12,13,26,49,215,249],[0]),([187,0,1,2,3,4],[1,2,7,12,13,41,132,246,250,251,252],[]),([67,0,1,2,3,4],[1,2,7,12,13,26,30,49,83,253],[0,2]),([0,1,2,3,4,72],[1,2,7,8,12,13,84,198,254],[0,2]),([75,0,1,2,5,4],[2,5,9,26,34,72],[0]),([18,0,1,2,3,4],[1,2,7,8,12,13,30,34,41,91,132,246,255],[0]),([0,1,2,5,4,40],[8,30,49,193,256],[0]),([0,1,9,2,3,4,41],[7,9,26,51,52,72,95,132],[]),([0,1,9,2,3,5,4],[5,9,25,26,33,34,41],[]),([131,0,21,1,2,3,4],[8,13,25,41,132,202,246,257],[0,2]),([26,0,1,2,3,4,41],[7,9,26,41,51,52,72,115],[0,3]),([0,1,9,2,5,4],[5,7,16,49,72,74],[]),([26,0,28,1,2,3,4],[41,72,147,199,227],[0,1,3]),([19,131,1,2,3,4],[2,12,21,26,49,246,257],[0]),([6,26,1,2,3,4],[2,7,12,25,72,93,105,106,107],[0,1,2]),([0,1,9,2,3,4],[2,9,12,25,41,258,259],[0]),([0,1,2,3,4,27],[8,9,13,21,49,179,180,227],[0,1,2,3]),([88,0,1,2,3,4],[1,2,7,9,12,21,30,132,144,260],[0]),([84,20,0,1,2,3,4],[8,9,21,26,38,49,86,97,98,132],[0,1,2]),([0,1,2,136,3,4],[1,7,8,13,21,261,262,263],[2,3]),([88,0,28,1,2,3,4],[7,41,72,144,147,199],[0,3]),([0,1,2,127,3,4],[7,9,13,21,25,49,225,264,265],[]),([131,20,1,2,3,4],[2,8,25,26],[]),([19,167,0,1,2,3,4],[8,12,13,25,26,49,72,115,132,233,246,266],[2]),([19,0,1,2,3,5,4],[7,8,9,12,21,26,27,33,34,49,84,86,96,115],[0,2]),([26,0,1,2,3,125,4],[9,41,54,72,267,268],[0,1]),([84,6,0,1,2,3,4],[1,2,9,13,25,26,49,72,110,269],[0,1,2]),([75,0,1,2,3,4],[1,2,5,7,9,12,13,26,72],[]),([188,0,1,2,3,4],[1,8,9,13,26,270],[]),([81,0,1,2,3,4],[1,8,9,13,21,30,152,158,159],[0,1]),([75,0,1,2,3,4,41],[7,9,21,51,52,72,132,203],[1]),([75,6,0,1,2,3,4],[1,2,8,9,12,13,21,25,41,72,110,117,203,271],[0,2]),([11,0,1,2,3,4],[8,9,13,21,30,143,161],[0,1]),([0,1,2,30,3,4],[1,7,8,21,49,272,273],[0,2]),([19,0,21,1,2,3,4],[1,12,13,25,26,41,115,132,202,246],[0,2]),([189,0,1,2,3,4],[1,8,9,12,13,21,72,227,274],[]),([26,0,1,2,3,4,27],[9,41,49,72,179,180,227],[0,1,3]),([190,0,1,2,3,4],[7,8,9,13,26,275],[]),([159,0,1,2,3,4],[1,2,8,12,13,21,72,86,128,276,277],[0,1]),([0,1,141,2,3,4,40],[8,49,56,77,239,278,279],[0,1,2,3]),([0,1,2,3,4,7],[7,8,9,13,21,110,111,112],[0,1]),([81,6,0,1,2,3,4],[2,7,12,13,25,72,110,152,158],[0,1]),([6,0,1,2,3,4,7],[12,13,25,72,110,111,112],[0,1]),([19,6,1,2,3,4],[12,25,26,30,49,72,96,110],[0,1]),([6,0,1,9,2,3,4],[7,9,13,25,72,92,93,95,110,280],[0,2]),([26,0,1,2,3,5,4],[9,21,33,34,41,49,72],[]),([6,0,1,2,30,3,4],[12,13,25,72,176,272,273],[0,1]),([59,0,1,2,3,4],[7,8,9,13,21,110,189],[0,1]),([0,1,191,2,3,4],[1,8,21,30,132,281,282],[3]),([6,0,1,2,3,5,4],[7,8,9,12,13,21,25,33,34,41,72,84,110,132],[0,1,2]),([42,0,1,2,3,4,41],[7,26,51,52,64,209],[0,1,3]),([173,0,1,2,3,4],[1,9,12,13,21,25,30,218,283,284],[0,2]),([75,20,0,1,2,3,4],[2,7,8,21,25,26,97,285],[0]),([124,0,1,2,3,4],[2,7,9,12,13,41,147,212,213],[0]),([0,1,9,5,4],[5,7,9,16,19,25,26,41,74],[0,2]),([26,0,1,2,3,4,40],[8,9,12,21,41,49,77,86,106,227,239],[0,1,3]),([18,0,1,2,3,5,4],[7,9,26,33,34,84,91],[0,2]),([0,1,9,2,3,4,10],[9,25,26,41,49,79,142],[0]),([6,0,1,2,3,4,41],[7,9,12,13,25,26,51,52,72,110,132],[0,1,2,3]),([131,158,0,1,2,3,4],[7,8,13,25,41,72,86,132,246,257,276,286],[0,3]),([192,0,1,2,3,4],[1,2,9,12,13,41,72,132,246,280,287,288],[]),([0,1,168,2,3,4],[2,9,12,25,132,168,289,290],[0]),([193,0,1,2,3,4],[1,7,8,13,26,291],[]),([19,75,0,1,2,3,4],[7,9,12,26,41,49,85,86,96,115,116,271],[0,2]),([0,1,141,2,3,4],[2,7,8,12,30,72,132,279],[0]),([0,1,2,3,4,132],[7,9,13,26,292,293],[2,3]),([131,0,1,2,3,4,41],[7,9,26,41,51,52,86,132,294],[0,3]),([0,1,2,3,5,4],[7,8,9,12,13,21,26,200,295,296],[0]),([84,131,0,1,2,3,4],[8,9,26,49,86,98,132,269,294],[2]),([93,0,1,2,3,4],[2,7,8,9,12,13,21,87,88,297],[0,1]),([0,1,2,194,3,4],[1,13,41,49,298],[]),([19,0,1,9,2,3,4],[7,9,12,26,41,49,86,92,95,96,115],[0,2]),([195,0,1,2,3,4],[1,7,8,9,13,246,257,299],[]),([75,0,1,9,3,4],[2,5,9,21,25,26,300,301],[0]),([0,1,2,3,4,10],[9,12,13,21,26,49,79,95,142],[0,2]),([84,0,1,3,5,4],[9,21,26,49,196,302],[0]),([145,0,1,2,3,4],[1,2,9,12,13,21,25,95],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_7_7 : checkNodesBT W_7 g_7 F_7 P_7_7 A_7 B_7_6 7 N_7_7 = true := by decide +kernel
def B_7_7 : BT (List (List Nat)) := buildBucketsBT W_7 N_7_7
set_option maxRecDepth 500000 in
lemma B_7_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_7 7 xs.toFinset) B_7_7 :=
  buildBucketsBT_sound (by decide) gp_7 W_7_ok (buildPoolsSubBT_sound S_7_ok) A_7_ok B_7_6_ok C_7_7
def P_7_8 : BT (Option BoundPool) := buildPoolsSubBT 9 W_7 r_7 S_7 ps_7 [1,2,5,7,8,9,12,13,25,26,30,33,34,41,49,51,52,72,84,92,95,96,98,106,110,115,116,132,227,257,269,271,280,294]
def N_7_8 : List NodeSpec := [([84,0,1,2,3,4],[1,2,9,30,49,98,269],[0,1,2,3]),([0,1,2,3,4,41],[7,30,51,52],[0,1,2,3]),([0,1,2,3,5,4],[7,8,26,33,34,49,84],[0,1,2,3]),([75,0,1,2,3,4],[1,2,5,8,9,26,30,72,116,132,271],[0,1,2,3]),([19,0,1,2,3,4],[1,2,12,30,96,115],[0,1,2,3]),([131,0,1,2,3,4],[1,2,8,30,41,257,294],[0,2,3]),([26,0,1,2,3,4],[1,2,9,30,72,106,227],[0,1,2,3]),([0,1,9,2,3,4],[9,25,41,72,92,95,132,280],[0,1,2]),([6,0,1,2,3,4],[1,2,13,30,110],[0,1,2,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_7_8 : checkNodesBT W_7 g_7 F_7 P_7_8 A_7 B_7_7 8 N_7_8 = true := by decide +kernel
def B_7_8 : BT (List (List Nat)) := buildBucketsBT W_7 N_7_8
set_option maxRecDepth 500000 in
lemma B_7_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_7 8 xs.toFinset) B_7_8 :=
  buildBucketsBT_sound (by decide) gp_7 W_7_ok (buildPoolsSubBT_sound S_7_ok) A_7_ok B_7_7_ok C_7_8
def P_7_9 : BT (Option BoundPool) := buildPoolsSubBT 9 W_7 r_7 S_7 ps_7 [1,2,30]
def N_7_9 : List NodeSpec := [([0,1,2,3,4],[1,2,30],[0,1,2,3])]
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
def g_8 := 0xfffefec0fffefec0fffefec0fffefec0fffefec0fffefec0fffefec0fffefec0
def r_8 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_8 : Lower r_8 g_8 8 := by
  have hc : Lower (varsOf 30) 0xfffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,8,9)]) (by decide +kernel) hc
def g_9 := 0xfeece000feece000feece000feece000feece000feece000feece000feece000
def r_9 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_9 : Lower r_9 g_9 8 := by
  have hc : Lower (varsOf 29) 0xfaa0a000faa0a000faa0a000faa0a000faa0a000faa0a000faa0a000faa0a000 7 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_2
  exact lift_of_f (z := 2) (o := 0) (essPairs := [(VAR 1,12,14)]) (by decide +kernel) hc
def g_10 := 0xfcc8e000fcc8e000fcc8e000fcc8e000fcc8e000fcc8e000fcc8e000fcc8e000
def r_10 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_10 : Lower r_10 g_10 8 := by
  have hc : Lower (varsOf 30) 0xfcc0c000fcc0c000fcc0c000fcc0c000fcc0c000fcc0c000fcc0c000fcc0c000 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_2
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,12,13)]) (by decide +kernel) hc
def g_11 := 0xfffee880fffee880fffee880fffee880fffee880fffee880fffee880fffee880
def r_11 : List Nat := varsOf 31
def p_11 : List Nat := [7,7,7,11,11,11,13,13,13,14,14,14,17,17,18,18,19,20,20,21,22,24,24,25,26,28]
def q_11 : List Nat := [6,5,3,10,9,3,12,9,5,12,10,6,16,1,16,2,3,16,4,5,6,16,8,9,10,12]
def F_11 : Nat := fullMask 26
set_option maxHeartbeats 0 in
lemma gp_11 : goodPairs g_11 p_11 q_11 := goodPairs_of (by decide +kernel)
def W_11 : BT Decor := buildWiresBT 3 (mkBase p_11 q_11 r_11) [(1,0,1),(1,2,3),(0,5,6)]
lemma W_11_ok : btAll (fun x => faithful p_11 q_11 x ∧ x.1 < 2^256) W_11 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_11 : List (List (Nat × Nat)) := [[],[(1,2)],[(1,2),(2,3)],[(0,2),(1,2)],[(0,2),(1,2),(2,3)],[(0,2),(1,3)]]
def A_11 : BT (List (Nat × Nat)) := btOfList 3 al_11
set_option maxHeartbeats 0 in
lemma A_11_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_11 = g_11) A_11 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_11_0 : Slice r_11 g_11 (subcubeFast 16 0) 7 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_2
set_option maxHeartbeats 0 in
lemma sl_11_1 : Slice r_11 g_11 (subcubeFast 2 0) 6 := by
  have hc : Lower (varsOf 29) 0xfffaa000fffaa000fffaa000fffaa000fffaa000fffaa000fffaa000fffaa000 6 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_2 : Slice r_11 g_11 (subcubeFast 4 0) 6 := by
  have hc : Lower (varsOf 27) 0xffee8800ffee8800ffee8800ffee8800ffee8800ffee8800ffee8800ffee8800 6 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_3 : Slice r_11 g_11 (subcubeFast 8 0) 6 := by
  have hc : Lower (varsOf 23) 0xfefe8080fefe8080fefe8080fefe8080fefe8080fefe8080fefe8080fefe8080 6 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_4 : Slice r_11 g_11 (subcubeFast 1 0) 6 := by
  have hc : Lower (varsOf 30) 0xfffcc000fffcc000fffcc000fffcc000fffcc000fffcc000fffcc000fffcc000 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_5 : Slice r_11 g_11 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) 0xfffffcc0fffffcc0fffffcc0fffffcc0fffffcc0fffffcc0fffffcc0fffffcc0 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_6 : Slice r_11 g_11 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) 0xfffffaa0fffffaa0fffffaa0fffffaa0fffffaa0fffffaa0fffffaa0fffffaa0 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_7 : Slice r_11 g_11 (subcubeFast 0 4) 5 := by
  have hc : Lower (varsOf 27) 0xffffee88ffffee88ffffee88ffffee88ffffee88ffffee88ffffee88ffffee88 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_8 : Slice r_11 g_11 (subcubeFast 0 8) 5 := by
  have hc : Lower (varsOf 23) 0xffffe8e8ffffe8e8ffffe8e8ffffe8e8ffffe8e8ffffe8e8ffffe8e8ffffe8e8 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
def S_11 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 16 0,7),some (subcubeFast 2 0,6),some (subcubeFast 4 0,6),some (subcubeFast 8 0,6),some (subcubeFast 1 0,6),some (subcubeFast 0 1,5),some (subcubeFast 0 2,5),some (subcubeFast 0 4,5),some (subcubeFast 0 8,5)]
lemma S_11_ok : btAll (fun o => ∀ p, o = some p → Slice r_11 g_11 p.1 p.2) S_11 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_11_0) (forall_cons (fun _ h => by cases h; exact sl_11_1) (forall_cons (fun _ h => by cases h; exact sl_11_2) (forall_cons (fun _ h => by cases h; exact sl_11_3) (forall_cons (fun _ h => by cases h; exact sl_11_4) (forall_cons (fun _ h => by cases h; exact sl_11_5) (forall_cons (fun _ h => by cases h; exact sl_11_6) (forall_cons (fun _ h => by cases h; exact sl_11_7) (forall_cons (fun _ h => by cases h; exact sl_11_8) (fun _ h => (List.not_mem_nil h).elim))))))))))
def ps_11 : BT (Option PoolSpec) := btOfList 4 ((([(1,[(1,2,3)]),(4,[]),(5,[]),(6,[]),(2,[]),(7,[]),(3,[]),(8,[]),(2,[(1,0,1)]),(1,[]),(0,[(1,0,1)]),(3,[(1,0,1)]),(0,[])] : List PoolSpec)).map some)
def B_11_4 : BT (List (List Nat)) := BT.empty
lemma B_11_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_11 4 xs.toFinset) B_11_4 := .empty
def P_11_5 : BT (Option BoundPool) := buildPoolsSubBT 4 W_11 r_11 S_11 ps_11 []
def N_11_5 : List NodeSpec := [([0,1,7,2,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_11_5 : checkNodesBT W_11 g_11 F_11 P_11_5 A_11 B_11_4 5 N_11_5 = true := by decide +kernel
def B_11_5 : BT (List (List Nat)) := buildBucketsBT W_11 N_11_5
set_option maxRecDepth 500000 in
lemma B_11_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_11 5 xs.toFinset) B_11_5 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok (buildPoolsSubBT_sound S_11_ok) A_11_ok B_11_4_ok C_11_5
def P_11_6 : BT (Option BoundPool) := buildPoolsSubBT 4 W_11 r_11 S_11 ps_11 [0,1,2,3,4,5,6,7,8]
def N_11_6 : List NodeSpec := [([0,1,5,2,3,6,4],[0,1,2,3,4,5,6,7,8],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_11_6 : checkNodesBT W_11 g_11 F_11 P_11_6 A_11 B_11_5 6 N_11_6 = true := by decide +kernel
def B_11_6 : BT (List (List Nat)) := buildBucketsBT W_11 N_11_6
set_option maxRecDepth 500000 in
lemma B_11_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_11 6 xs.toFinset) B_11_6 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok (buildPoolsSubBT_sound S_11_ok) A_11_ok B_11_5_ok C_11_6
def P_11_7 : BT (Option BoundPool) := buildPoolsSubBT 4 W_11 r_11 S_11 ps_11 [1,2,4,5,6,7,8,9,10,11]
def N_11_7 : List NodeSpec := [([0,1,5,2,3,4],[1,2,4,5,6,7,8,9,10,11],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_11_7 : checkNodesBT W_11 g_11 F_11 P_11_7 A_11 B_11_6 7 N_11_7 = true := by decide +kernel
def B_11_7 : BT (List (List Nat)) := buildBucketsBT W_11 N_11_7
set_option maxRecDepth 500000 in
lemma B_11_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_11 7 xs.toFinset) B_11_7 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok (buildPoolsSubBT_sound S_11_ok) A_11_ok B_11_6_ok C_11_7
def P_11_8 : BT (Option BoundPool) := buildPoolsSubBT 4 W_11 r_11 S_11 ps_11 [1,4,6,9,12]
def N_11_8 : List NodeSpec := [([0,1,2,3,4],[1,4,6,9,12],[0,1,2,3,4,5])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_11_8 : checkNodesBT W_11 g_11 F_11 P_11_8 A_11 B_11_7 8 N_11_8 = true := by decide +kernel
def B_11_8 : BT (List (List Nat)) := buildBucketsBT W_11 N_11_8
set_option maxRecDepth 500000 in
lemma B_11_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_11 8 xs.toFinset) B_11_8 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok (buildPoolsSubBT_sound S_11_ok) A_11_ok B_11_7_ok C_11_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_11_ok : forestRootCheck r_11 g_11 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11),(VAR 4,1,17)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_11_in : bucketContainsBT B_11_8 r_11 = true := by decide +kernel
lemma low_11 : Lower r_11 g_11 9 := lower_of_forestBT root_11_ok B_11_8_ok root_11_in
def g_12 := 0xfec0fec0fec0fec0fec0fec0fec0fec0fec0fec0fec0fec0fec0fec0fec0fec0
def r_12 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_12 : Lower r_12 g_12 5 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,8,9)]) (by decide +kernel) hc
def g_13 := 0xfffeeac0fffeeac0fffeeac0fffeeac0fffeeac0fffeeac0fffeeac0fffeeac0
def r_13 : List Nat := varsOf 31
def p_13 : List Nat := [6,6,7,7,9,9,11,11,13,13,14,14,17,17,18,18,19,20,20,21,24,24,26,28]
def q_13 : List Nat := [4,2,5,3,8,1,10,3,12,5,12,10,16,1,16,2,3,16,4,5,16,8,10,12]
def F_13 : Nat := fullMask 24
set_option maxHeartbeats 0 in
lemma gp_13 : goodPairs g_13 p_13 q_13 := goodPairs_of (by decide +kernel)
def W_13 : BT Decor := buildWiresBT 5 (mkBase p_13 q_13 r_13) [(1,2,0),(0,5,4),(1,1,6),(1,2,4),(3,2,4),(1,9,0),(2,10,3),(1,0,1),(1,12,4),(3,3,13),(0,12,4),(1,15,3),(1,3,1),(0,17,4),(1,3,4),(1,0,4),(3,3,20),(1,1,4),(3,3,22),(3,3,4),(1,2,3),(3,25,4),(2,12,4)]
lemma W_13_ok : btAll (fun x => faithful p_13 q_13 x ∧ x.1 < 2^256) W_13 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_13 : List (List (Nat × Nat)) := [[],[(1,2)],[(0,1),(2,3)],[(0,2),(1,2),(2,3)],[(0,1),(1,3),(2,3)],[(0,2),(1,3)],[(0,3)],[(0,3),(1,2)]]
def A_13 : BT (List (Nat × Nat)) := btOfList 3 al_13
set_option maxHeartbeats 0 in
lemma A_13_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_13 = g_13) A_13 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_13_0 : Slice r_13 g_13 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) 0xfffcc0c0fffcc0c0fffcc0c0fffcc0c0fffcc0c0fffcc0c0fffcc0c0fffcc0c0 5 := carry_of (swaps := [(0,4),(3,4)]) (by decide +kernel) low_12
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_1 : Slice r_13 g_13 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) 0xfffaaa00fffaaa00fffaaa00fffaaa00fffaaa00fffaaa00fffaaa00fffaaa00 5 := carry_of (swaps := [(0,1),(1,4),(2,4),(3,4)]) (by decide +kernel) low_12
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_2 : Slice r_13 g_13 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) 0xffeeaa00ffeeaa00ffeeaa00ffeeaa00ffeeaa00ffeeaa00ffeeaa00ffeeaa00 5 := carry_of (swaps := [(0,1),(2,4),(3,4)]) (by decide +kernel) low_12
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_3 : Slice r_13 g_13 (subcubeFast 8 0) 5 := by
  have hc : Lower (varsOf 23) 0xfefec0c0fefec0c0fefec0c0fefec0c0fefec0c0fefec0c0fefec0c0fefec0c0 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_12
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_4 : Slice r_13 g_13 (subcubeFast 6 0) 4 := by
  have hc : Lower (varsOf 25) 0xffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00 4 := carry_of (swaps := [(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 6) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_5 : Slice r_13 g_13 (subcubeFast 9 0) 4 := by
  have hc : Lower (varsOf 22) 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0 4 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 9) (o := 0) (by decide +kernel) hc
def S_13 : BT (Option (Nat × Nat)) := btOfList 3 [some (subcubeFast 1 0,5),some (subcubeFast 2 0,5),some (subcubeFast 4 0,5),some (subcubeFast 8 0,5),some (subcubeFast 6 0,4),some (subcubeFast 9 0,4)]
lemma S_13_ok : btAll (fun o => ∀ p, o = some p → Slice r_13 g_13 p.1 p.2) S_13 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_13_0) (forall_cons (fun _ h => by cases h; exact sl_13_1) (forall_cons (fun _ h => by cases h; exact sl_13_2) (forall_cons (fun _ h => by cases h; exact sl_13_3) (forall_cons (fun _ h => by cases h; exact sl_13_4) (forall_cons (fun _ h => by cases h; exact sl_13_5) (fun _ h => (List.not_mem_nil h).elim)))))))
def ps_13 : BT (Option PoolSpec) := btOfList 4 ((([(3,[]),(0,[(3,3,20)]),(0,[(3,3,4)]),(2,[]),(1,[]),(0,[]),(0,[(1,3,1)]),(5,[]),(4,[]),(3,[(1,0,1)])] : List PoolSpec)).map some)
def B_13_2 : BT (List (List Nat)) := BT.empty
lemma B_13_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_13 2 xs.toFinset) B_13_2 := .empty
def P_13_3 : BT (Option BoundPool) := buildPoolsSubBT 4 W_13 r_13 S_13 ps_13 []
def N_13_3 : List NodeSpec := [([0,7,3,8],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_13_3 : checkNodesBT W_13 g_13 F_13 P_13_3 A_13 B_13_2 3 N_13_3 = true := by decide +kernel
def B_13_3 : BT (List (List Nat)) := buildBucketsBT W_13 N_13_3
set_option maxRecDepth 500000 in
lemma B_13_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_13 3 xs.toFinset) B_13_3 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok (buildPoolsSubBT_sound S_13_ok) A_13_ok B_13_2_ok C_13_3
def P_13_4 : BT (Option BoundPool) := buildPoolsSubBT 4 W_13 r_13 S_13 ps_13 []
def N_13_4 : List NodeSpec := [([11,0,1,2,4],[],[]),([14,0,1,2,4],[],[]),([0,1,2,16,4],[],[3]),([0,1,2,18,19],[],[2])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_13_4 : checkNodesBT W_13 g_13 F_13 P_13_4 A_13 B_13_3 4 N_13_4 = true := by decide +kernel
def B_13_4 : BT (List (List Nat)) := buildBucketsBT W_13 N_13_4
set_option maxRecDepth 500000 in
lemma B_13_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_13 4 xs.toFinset) B_13_4 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok (buildPoolsSubBT_sound S_13_ok) A_13_ok B_13_3_ok C_13_4
def P_13_5 : BT (Option BoundPool) := buildPoolsSubBT 4 W_13 r_13 S_13 ps_13 [0,1,2,3,4,5,6]
def N_13_5 : List NodeSpec := [([21,0,1,2,4,20],[0,1],[]),([23,0,1,2,3,4],[],[]),([21,0,1,2,4],[],[]),([24,0,1,2,4,19],[0,2],[]),([26,0,1,2,3,4],[],[]),([0,10,1,2,3,4],[0],[0]),([27,0,1,2,3,4],[],[]),([0,1,2,3,4,13],[0,3],[0,2]),([0,1,15,2,3,4],[0,3,4,5],[0,2,4,6]),([0,1,2,17,4,19],[4,6],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_13_5 : checkNodesBT W_13 g_13 F_13 P_13_5 A_13 B_13_4 5 N_13_5 = true := by decide +kernel
def B_13_5 : BT (List (List Nat)) := buildBucketsBT W_13 N_13_5
set_option maxRecDepth 500000 in
lemma B_13_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_13 5 xs.toFinset) B_13_5 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok (buildPoolsSubBT_sound S_13_ok) A_13_ok B_13_4_ok C_13_5
def P_13_6 : BT (Option BoundPool) := buildPoolsSubBT 4 W_13 r_13 S_13 ps_13 [3,4,5,7,8,9]
def N_13_6 : List NodeSpec := [([24,0,1,2,3,4],[3,4,5,7],[0,1,2,4]),([0,1,2,3,4,20],[3,4,5,7],[0,1,2,4,6,7]),([0,1,12,2,3,4],[4,5,7,8,9],[0,4,5,6])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_13_6 : checkNodesBT W_13 g_13 F_13 P_13_6 A_13 B_13_5 6 N_13_6 = true := by decide +kernel
def B_13_6 : BT (List (List Nat)) := buildBucketsBT W_13 N_13_6
set_option maxRecDepth 500000 in
lemma B_13_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_13 6 xs.toFinset) B_13_6 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok (buildPoolsSubBT_sound S_13_ok) A_13_ok B_13_5_ok C_13_6
def P_13_7 : BT (Option BoundPool) := buildPoolsSubBT 4 W_13 r_13 S_13 ps_13 [3,4,5,7,8]
def N_13_7 : List NodeSpec := [([0,1,2,3,4],[3,4,5,7,8],[0,1,2,3,4,5,6])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_13_7 : checkNodesBT W_13 g_13 F_13 P_13_7 A_13 B_13_6 7 N_13_7 = true := by decide +kernel
def B_13_7 : BT (List (List Nat)) := buildBucketsBT W_13 N_13_7
set_option maxRecDepth 500000 in
lemma B_13_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_13 7 xs.toFinset) B_13_7 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok (buildPoolsSubBT_sound S_13_ok) A_13_ok B_13_6_ok C_13_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_13_ok : forestRootCheck r_13 g_13 [(VAR 0,8,9),(VAR 1,4,6),(VAR 2,2,6),(VAR 3,1,9),(VAR 4,1,17)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_13_in : bucketContainsBT B_13_7 r_13 = true := by decide +kernel
lemma low_13 : Lower r_13 g_13 8 := lower_of_forestBT root_13_ok B_13_7_ok root_13_in
def g_14 := 0xfff8e000fff8e000fff8e000fff8e000fff8e000fff8e000fff8e000fff8e000
def r_14 : List Nat := varsOf 31
def p_14 : List Nat := [13,13,13,14,14,14,15,15,19,19,19,20,20,21,21,22,22,23,24,24,25,25,26,26,27,28]
def q_14 : List Nat := [12,9,5,12,10,6,11,7,18,17,3,16,4,17,5,18,6,7,16,8,17,9,18,10,11,12]
def F_14 : Nat := fullMask 26
set_option maxHeartbeats 0 in
lemma gp_14 : goodPairs g_14 p_14 q_14 := goodPairs_of (by decide +kernel)
def W_14 : BT Decor := buildWiresBT 6 (mkBase p_14 q_14 r_14) [(1,2,3),(1,5,4),(3,3,6),(0,2,4),(1,2,4),(3,8,9),(0,3,4),(1,3,4),(3,11,12),(0,2,12),(1,1,11),(1,1,8),(1,8,3),(0,0,12),(0,13,0),(2,0,11),(0,2,3),(0,21,4),(3,22,2),(1,2,11),(2,13,1),(0,0,9),(0,3,9),(3,1,12),(0,13,2),(2,10,3),(3,3,4),(2,2,4),(3,1,9),(3,0,9),(2,1,11),(1,21,4),(2,3,4),(3,37,5),(0,5,4),(1,31,21),(3,2,4),(1,0,8),(0,1,9),(1,31,2),(3,37,2),(2,5,4),(3,5,4),(3,21,4),(2,21,4)]
lemma W_14_ok : btAll (fun x => faithful p_14 q_14 x ∧ x.1 < 2^256) W_14 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_14 : List (List (Nat × Nat)) := [[],[(2,3)],[(0,1)],[(0,1),(2,3)]]
def A_14 : BT (List (Nat × Nat)) := btOfList 2 al_14
set_option maxHeartbeats 0 in
lemma A_14_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_14 = g_14) A_14 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_14_0 : Slice r_14 g_14 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) 0xfffcf000fffcf000fffcf000fffcf000fffcf000fffcf000fffcf000fffcf000 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_12
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_14_1 : Slice r_14 g_14 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) 0xfff0c000fff0c000fff0c000fff0c000fff0c000fff0c000fff0c000fff0c000 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_14_2 : Slice r_14 g_14 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) 0xfffaf000fffaf000fffaf000fffaf000fffaf000fffaf000fffaf000fffaf000 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_12
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_14_3 : Slice r_14 g_14 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) 0xfff0a000fff0a000fff0a000fff0a000fff0a000fff0a000fff0a000fff0a000 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_14_4 : Slice r_14 g_14 (subcubeFast 1 2) 4 := by
  have hc : Lower (varsOf 28) 0xfff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_14_5 : Slice r_14 g_14 (identDom 2 3) 6 := by
  have hc : Lower (varsOf 23) 0xf8f8e0e0f8f8e0e0f8f8e0e0f8f8e0e0f8f8e0e0f8f8e0e0f8f8e0e0f8f8e0e0 6 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_6
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
def S_14 : BT (Option (Nat × Nat)) := btOfList 3 [some (subcubeFast 0 1,5),some (subcubeFast 1 0,5),some (subcubeFast 0 2,5),some (subcubeFast 2 0,5),some (subcubeFast 1 2,4),some (identDom 2 3,6)]
lemma S_14_ok : btAll (fun o => ∀ p, o = some p → Slice r_14 g_14 p.1 p.2) S_14 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_14_0) (forall_cons (fun _ h => by cases h; exact sl_14_1) (forall_cons (fun _ h => by cases h; exact sl_14_2) (forall_cons (fun _ h => by cases h; exact sl_14_3) (forall_cons (fun _ h => by cases h; exact sl_14_4) (forall_cons (fun _ h => by cases h; exact sl_14_5) (fun _ h => (List.not_mem_nil h).elim)))))))
def ps_14 : BT (Option PoolSpec) := btOfList 4 ((([(1,[]),(0,[]),(3,[]),(2,[]),(5,[(3,3,4),(1,31,2)]),(5,[]),(5,[(2,3,4),(3,37,2)]),(4,[]),(5,[(0,5,4)]),(5,[(3,5,4)]),(5,[(1,2,4)]),(5,[(0,2,4)]),(5,[(2,2,4)]),(5,[(3,3,4)]),(5,[(2,21,4)]),(5,[(1,21,4)])] : List PoolSpec)).map some)
def B_14_2 : BT (List (List Nat)) := BT.empty
lemma B_14_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_14 2 xs.toFinset) B_14_2 := .empty
def P_14_3 : BT (Option BoundPool) := buildPoolsSubBT 4 W_14 r_14 S_14 ps_14 []
def N_14_3 : List NodeSpec := [([7,10,0,1],[],[]),([13,0,1,14],[],[]),([13,0,2,15],[],[]),([0,16,17,9],[],[]),([13,18,1,2],[],[]),([19,13,1,2],[],[]),([13,0,1,2],[],[]),([20,13,1,2],[],[]),([23,13,0,1],[],[]),([13,0,1,24],[],[]),([25,13,0,2],[],[]),([26,1,8,27],[],[]),([13,28,0,2],[],[]),([29,13,0,1],[],[]),([30,10,0,1],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_14_3 : checkNodesBT W_14 g_14 F_14 P_14_3 A_14 B_14_2 3 N_14_3 = true := by decide +kernel
def B_14_3 : BT (List (List Nat)) := buildBucketsBT W_14 N_14_3
set_option maxRecDepth 500000 in
lemma B_14_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_14 3 xs.toFinset) B_14_3 :=
  buildBucketsBT_sound (by decide) gp_14 W_14_ok (buildPoolsSubBT_sound S_14_ok) A_14_ok B_14_2_ok C_14_3
def P_14_4 : BT (Option BoundPool) := buildPoolsSubBT 4 W_14 r_14 S_14 ps_14 []
def N_14_4 : List NodeSpec := [([31,13,0,1,2],[],[]),([32,10,0,1,3],[],[]),([31,0,1,14,4],[],[]),([7,33,0,2,4],[],[]),([33,34,2,3,4],[],[]),([7,26,1,2,4],[],[]),([26,1,2,27,4],[],[0]),([20,35,2,3,4],[],[]),([0,1,8,3,36],[],[]),([20,23,1,3,4],[],[]),([13,0,1,2],[],[0,1,2]),([13,0,1,2,3],[],[]),([7,0,1,2,4],[],[]),([0,1,2,38,4],[],[]),([0,1,2,39,12],[],[]),([0,1,8,17,9],[],[0,1,2]),([0,1,8,3,9],[],[1]),([13,0,1,2,4],[],[]),([0,1,2,40,4],[],[]),([7,0,1,8,9],[],[0]),([20,1,3,24,4],[],[]),([23,0,3,15,4],[],[]),([32,41,0,1,3],[],[1]),([20,1,2,11,12],[],[0]),([33,0,8,3,9],[],[1]),([32,0,1,17,4],[],[]),([33,0,2,27,4],[],[]),([23,0,1,11,12],[],[0]),([0,2,16,17,4],[],[0]),([2,42,16,3,4],[],[]),([23,0,1,3,4],[],[]),([26,1,8,3,9],[],[0,1]),([13,0,1,2,11],[],[0,2]),([0,8,16,3,9],[],[0,1]),([13,0,1,2,12],[],[0,1,2]),([0,1,8,27,9],[],[0,1,2]),([26,43,2,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_14_4 : checkNodesBT W_14 g_14 F_14 P_14_4 A_14 B_14_3 4 N_14_4 = true := by decide +kernel
def B_14_4 : BT (List (List Nat)) := buildBucketsBT W_14 N_14_4
set_option maxRecDepth 500000 in
lemma B_14_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_14 4 xs.toFinset) B_14_4 :=
  buildBucketsBT_sound (by decide) gp_14 W_14_ok (buildPoolsSubBT_sound S_14_ok) A_14_ok B_14_3_ok C_14_4
def P_14_5 : BT (Option BoundPool) := buildPoolsSubBT 4 W_14 r_14 S_14 ps_14 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]
def N_14_5 : List NodeSpec := [([32,41,0,1,2,3],[],[1]),([0,1,2,44,3,4],[0,1,2,3,4],[0]),([32,41,0,1,3],[],[0,1]),([0,1,2,3,4,9],[0,1,2,3,5],[0]),([32,41,0,1,3,4],[],[1]),([0,1,45,2,3,4],[0,1,2,3,6],[1]),([7,0,1,2,4],[],[]),([0,1,14,3,4,12],[],[0,1,3]),([46,0,1,2,3,4],[],[]),([23,0,1,11,3,4],[5],[0,2]),([33,0,2,3,4,9],[2,7],[0]),([0,1,2,3,4,6],[0,1,2,3],[0,1]),([0,1,2,3,39,4],[0,1,2,3,8],[0,1]),([47,0,1,2,3,4],[9],[]),([48,0,1,2,3,4],[],[]),([0,1,8,3,4,9],[10,11],[1]),([32,0,1,3,5,4],[12],[1]),([7,0,1,2,3,4],[],[]),([0,8,2,16,3,4],[2,7],[0,1]),([0,1,21,8,3,4],[5],[0]),([31,0,1,21,2,4],[13],[0]),([0,1,8,2,3,4],[0,1,2,3,5],[0,1]),([20,1,2,11,3,4],[1,7],[0]),([49,0,1,2,3,4],[14],[]),([0,1,2,3,4,36],[0,1,2,3,15],[0,1]),([0,1,8,2,3,9],[],[1]),([7,0,1,2,4,9],[5],[0,2]),([31,0,1,2,4,12],[1,13],[1]),([0,1,22,2,3,4],[0,1,2,3],[0,1]),([31,0,1,2,11,3],[1],[1]),([32,0,1,8,3,4],[1],[0]),([32,0,1,2,3,4],[],[0]),([0,1,8,2,17,4],[],[0,1,2,3]),([23,0,1,3,4],[],[]),([0,1,2,5,4,12],[5],[0]),([32,0,1,2,3,9],[1],[0]),([0,1,8,3,9],[],[0,1,2,3]),([23,0,1,2,3,4],[],[]),([31,0,1,2,3,4],[],[1]),([26,1,2,3,4,9],[1,7],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_14_5 : checkNodesBT W_14 g_14 F_14 P_14_5 A_14 B_14_4 5 N_14_5 = true := by decide +kernel
def B_14_5 : BT (List (List Nat)) := buildBucketsBT W_14 N_14_5
set_option maxRecDepth 500000 in
lemma B_14_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_14 5 xs.toFinset) B_14_5 :=
  buildBucketsBT_sound (by decide) gp_14 W_14_ok (buildPoolsSubBT_sound S_14_ok) A_14_ok B_14_4_ok C_14_5
def P_14_6 : BT (Option BoundPool) := buildPoolsSubBT 4 W_14 r_14 S_14 ps_14 [0,1,2,3,5,10,11,12,13]
def N_14_6 : List NodeSpec := [([31,0,1,2,3,4],[0,1,2,3,5,13],[0,1]),([0,1,2,3,4,9],[0,1,2,3,5,10],[0,1,2]),([32,0,1,2,3,4],[0,1,2,3,5,12],[0,1]),([0,1,8,2,3,4],[0,1,2,3,5,11],[0,1,2,3]),([0,1,2,3,5,4],[0,1,2,3,5],[0,1]),([0,1,21,2,3,4],[0,1,2,3,5],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_14_6 : checkNodesBT W_14 g_14 F_14 P_14_6 A_14 B_14_5 6 N_14_6 = true := by decide +kernel
def B_14_6 : BT (List (List Nat)) := buildBucketsBT W_14 N_14_6
set_option maxRecDepth 500000 in
lemma B_14_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_14 6 xs.toFinset) B_14_6 :=
  buildBucketsBT_sound (by decide) gp_14 W_14_ok (buildPoolsSubBT_sound S_14_ok) A_14_ok B_14_5_ok C_14_6
def P_14_7 : BT (Option BoundPool) := buildPoolsSubBT 4 W_14 r_14 S_14 ps_14 [0,1,2,3,5]
def N_14_7 : List NodeSpec := [([0,1,2,3,4],[0,1,2,3,5],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_14_7 : checkNodesBT W_14 g_14 F_14 P_14_7 A_14 B_14_6 7 N_14_7 = true := by decide +kernel
def B_14_7 : BT (List (List Nat)) := buildBucketsBT W_14 N_14_7
set_option maxRecDepth 500000 in
lemma B_14_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_14 7 xs.toFinset) B_14_7 :=
  buildBucketsBT_sound (by decide) gp_14 W_14_ok (buildPoolsSubBT_sound S_14_ok) A_14_ok B_14_6_ok C_14_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_14_ok : forestRootCheck r_14 g_14 [(VAR 0,12,13),(VAR 1,12,14),(VAR 2,9,13),(VAR 3,5,13),(VAR 4,3,19)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_14_in : bucketContainsBT B_14_7 r_14 = true := by decide +kernel
lemma low_14 : Lower r_14 g_14 8 := lower_of_forestBT root_14_ok B_14_7_ok root_14_in
def g_15 := 0xfee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0
def r_15 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_15 : Lower r_15 g_15 5 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,4,5)]) (by decide +kernel) hc
def g_16 := 0xfffefc80fffefc80fffefc80fffefc80fffefc80fffefc80fffefc80fffefc80
def r_16 : List Nat := varsOf 31
def p_16 : List Nat := [7,7,7,10,10,11,11,12,12,13,13,14,17,17,18,18,19,20,20,21,22,24,24,25]
def q_16 : List Nat := [6,5,3,8,2,9,3,8,4,9,5,6,16,1,16,2,3,16,4,5,6,16,8,9]
def F_16 : Nat := fullMask 24
set_option maxHeartbeats 0 in
lemma gp_16 : goodPairs g_16 p_16 q_16 := goodPairs_of (by decide +kernel)
def W_16 : BT Decor := buildWiresBT 4 (mkBase p_16 q_16 r_16) [(1,1,2),(1,5,4),(3,3,6),(1,1,4),(3,2,8),(2,5,4),(1,2,4)]
lemma W_16_ok : btAll (fun x => faithful p_16 q_16 x ∧ x.1 < 2^256) W_16 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_16 : List (List (Nat × Nat)) := [[],[(1,2)]]
def A_16 : BT (List (Nat × Nat)) := btOfList 1 al_16
set_option maxHeartbeats 0 in
lemma A_16_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_16 = g_16) A_16 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_16_0 : Slice r_16 g_16 (identDom 0 2) 7 := by
  have hc : Lower (varsOf 27) 0xffeeee88ffeeee88ffeeee88ffeeee88ffeeee88ffeeee88ffeeee88ffeeee88 7 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_ident (u := 0) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_1 : Slice r_16 g_16 (identDom 0 1) 7 := by
  have hc : Lower (varsOf 29) 0xfffafaa0fffafaa0fffafaa0fffafaa0fffafaa0fffafaa0fffafaa0fffafaa0 7 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_ident (u := 0) (v := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_2 : Slice r_16 g_16 (subcubeFast 8 0) 6 := by
  have hc : Lower (varsOf 23) 0xfefe8080fefe8080fefe8080fefe8080fefe8080fefe8080fefe8080fefe8080 6 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_3 : Slice r_16 g_16 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) 0xfffffcc0fffffcc0fffffcc0fffffcc0fffffcc0fffffcc0fffffcc0fffffcc0 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_4 : Slice r_16 g_16 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) 0xfffaf000fffaf000fffaf000fffaf000fffaf000fffaf000fffaf000fffaf000 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_12
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_5 : Slice r_16 g_16 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) 0xffeecc00ffeecc00ffeecc00ffeecc00ffeecc00ffeecc00ffeecc00ffeecc00 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_12
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_6 : Slice r_16 g_16 (subcubeFast 16 0) 5 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_3
set_option maxHeartbeats 0 in
lemma sl_16_7 : Slice r_16 g_16 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) 0xfffcfc00fffcfc00fffcfc00fffcfc00fffcfc00fffcfc00fffcfc00fffcfc00 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_15
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_16_8 : Slice r_16 g_16 (subcubeFast 16 1) 4 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 1) (by decide +kernel) hc
def S_16 : BT (Option (Nat × Nat)) := btOfList 4 [some (identDom 0 2,7),some (identDom 0 1,7),some (subcubeFast 8 0,6),some (subcubeFast 0 1,5),some (subcubeFast 2 0,5),some (subcubeFast 4 0,5),some (subcubeFast 16 0,5),some (subcubeFast 1 0,5),some (subcubeFast 16 1,4)]
lemma S_16_ok : btAll (fun o => ∀ p, o = some p → Slice r_16 g_16 p.1 p.2) S_16 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_16_0) (forall_cons (fun _ h => by cases h; exact sl_16_1) (forall_cons (fun _ h => by cases h; exact sl_16_2) (forall_cons (fun _ h => by cases h; exact sl_16_3) (forall_cons (fun _ h => by cases h; exact sl_16_4) (forall_cons (fun _ h => by cases h; exact sl_16_5) (forall_cons (fun _ h => by cases h; exact sl_16_6) (forall_cons (fun _ h => by cases h; exact sl_16_7) (forall_cons (fun _ h => by cases h; exact sl_16_8) (fun _ h => (List.not_mem_nil h).elim))))))))))
def ps_16 : BT (Option PoolSpec) := btOfList 4 ((([(0,[]),(3,[]),(2,[]),(0,[(1,2,1)]),(4,[]),(6,[]),(1,[(1,1,4)]),(2,[(1,1,4)]),(8,[]),(5,[]),(1,[(1,1,2)]),(0,[(1,1,2)]),(2,[(1,1,2)]),(1,[]),(7,[])] : List PoolSpec)).map some)
def B_16_3 : BT (List (List Nat)) := BT.empty
lemma B_16_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_16 3 xs.toFinset) B_16_3 := .empty
def P_16_4 : BT (Option BoundPool) := buildPoolsSubBT 4 W_16 r_16 S_16 ps_16 []
def N_16_4 : List NodeSpec := [([7,0,1,2,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_16_4 : checkNodesBT W_16 g_16 F_16 P_16_4 A_16 B_16_3 4 N_16_4 = true := by decide +kernel
def B_16_4 : BT (List (List Nat)) := buildBucketsBT W_16 N_16_4
set_option maxRecDepth 500000 in
lemma B_16_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_16 4 xs.toFinset) B_16_4 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok (buildPoolsSubBT_sound S_16_ok) A_16_ok B_16_3_ok C_16_4
def P_16_5 : BT (Option BoundPool) := buildPoolsSubBT 4 W_16 r_16 S_16 ps_16 [0,1,2,3,4,5]
def N_16_5 : List NodeSpec := [([9,0,1,2,3,4],[],[]),([10,0,1,2,3,4],[],[]),([0,1,2,3,4,6],[0,1,2],[0]),([0,1,5,3,4,11],[3,4,5],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_16_5 : checkNodesBT W_16 g_16 F_16 P_16_5 A_16 B_16_4 5 N_16_5 = true := by decide +kernel
def B_16_5 : BT (List (List Nat)) := buildBucketsBT W_16 N_16_5
set_option maxRecDepth 500000 in
lemma B_16_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_16 5 xs.toFinset) B_16_5 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok (buildPoolsSubBT_sound S_16_ok) A_16_ok B_16_4_ok C_16_5
def P_16_6 : BT (Option BoundPool) := buildPoolsSubBT 4 W_16 r_16 S_16 ps_16 [1,4,5,6,7,8,9,10,11,12]
def N_16_6 : List NodeSpec := [([0,1,2,3,4,8],[1,4,6,7,8,9],[0,1]),([0,1,2,5,3,4],[1,4,5,9,10,11,12],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_16_6 : checkNodesBT W_16 g_16 F_16 P_16_6 A_16 B_16_5 6 N_16_6 = true := by decide +kernel
def B_16_6 : BT (List (List Nat)) := buildBucketsBT W_16 N_16_6
set_option maxRecDepth 500000 in
lemma B_16_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_16 6 xs.toFinset) B_16_6 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok (buildPoolsSubBT_sound S_16_ok) A_16_ok B_16_5_ok C_16_6
def P_16_7 : BT (Option BoundPool) := buildPoolsSubBT 4 W_16 r_16 S_16 ps_16 [0,1,2,4,5,9,13,14]
def N_16_7 : List NodeSpec := [([0,1,2,3,4],[0,1,2,4,5,9,13,14],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_16_7 : checkNodesBT W_16 g_16 F_16 P_16_7 A_16 B_16_6 7 N_16_7 = true := by decide +kernel
def B_16_7 : BT (List (List Nat)) := buildBucketsBT W_16 N_16_7
set_option maxRecDepth 500000 in
lemma B_16_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_16 7 xs.toFinset) B_16_7 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok (buildPoolsSubBT_sound S_16_ok) A_16_ok B_16_6_ok C_16_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_16_ok : forestRootCheck r_16 g_16 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,2,10),(VAR 4,1,17)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_16_in : bucketContainsBT B_16_7 r_16 = true := by decide +kernel
lemma low_16 : Lower r_16 g_16 8 := lower_of_forestBT root_16_ok B_16_7_ok root_16_in
def g_17 := 0xffffffe8fec0c080ffffffe8fec0c080ffffffe8fec0c080ffffffe8fec0c080
def r_17 : List Nat := varsOf 63
def p_17 : List Nat := [7,7,7,14,14,14,15,15,22,22,22,23,23,25,25,25,26,26,26,27,27,28,28,28,29,29,35,35,35,37,37,37,38,38,38,40,40,41,41,42,42,43,44,44,45,48,48,49,49,50,50,51,52,52,53,56]
def q_17 : List Nat := [6,5,3,12,10,6,13,11,20,18,6,21,19,24,17,9,24,18,10,19,11,24,20,12,21,13,34,33,3,36,33,5,36,34,6,32,8,33,9,34,10,11,36,12,13,32,16,33,17,34,18,19,36,20,21,24]
def F_17 : Nat := fullMask 56
set_option maxHeartbeats 0 in
lemma gp_17 : goodPairs g_17 p_17 q_17 := goodPairs_of (by decide +kernel)
def W_17 : BT Decor := buildWiresBT 9 (mkBase p_17 q_17 r_17) [(0,2,4),(1,2,4),(3,6,7),(0,8,5),(1,8,5),(3,9,10),(0,11,1),(1,1,11),(3,12,13),(1,3,5),(0,2,15),(1,2,15),(3,16,17),(0,18,1),(1,18,1),(3,19,20),(0,3,5),(0,2,5),(1,2,5),(3,23,24),(1,25,1),(0,25,1),(0,3,4),(1,27,28),(1,3,4),(0,1,5),(1,31,28),(0,2,32),(1,2,32),(3,33,34),(1,1,5),(0,1,3),(1,1,3),(3,37,38),(2,25,39),(3,25,39),(0,1,4),(1,1,4),(3,42,43),(0,25,44),(1,25,44),(1,4,5),(0,1,47),(1,1,47),(3,48,49),(2,50,2),(3,50,2),(0,4,5),(1,52,53),(0,39,5),(1,39,5),(3,55,56),(3,57,2),(1,58,4),(3,11,1),(1,60,0),(2,57,2),(0,2,3),(1,2,3),(3,63,64),(0,65,5),(1,65,5),(3,66,67),(0,68,1),(1,1,68),(0,1,2),(1,71,28),(0,72,5),(1,72,5),(3,73,74),(1,1,2),(1,0,73),(0,2,47),(1,2,47),(3,78,79),(3,80,1),(1,81,3),(1,0,81),(0,80,1),(1,80,1),(1,23,28),(2,1,86),(3,1,86),(1,57,2),(1,71,53),(3,90,47),(0,76,47),(3,30,74),(3,31,36),(2,94,2),(3,94,2),(3,0,74),(2,76,73),(0,1,86),(1,0,99),(2,25,1),(1,101,0),(1,81,53),(1,1,86),(3,94,8),(2,25,28),(3,0,104),(3,25,1),(1,0,108),(3,33,36),(2,72,5),(3,72,5),(3,2,32),(2,3,4),(1,114,108),(1,108,28),(1,0,33),(1,114,95),(1,28,5),(3,2,119),(3,1,119),(0,43,15),(0,2,122),(1,2,122),(3,123,124),(1,25,3),(0,126,43),(3,53,47),(3,4,15),(0,76,15),(1,71,22),(1,30,5),(0,76,132),(3,71,119),(2,4,3),(3,135,26),(3,114,15),(1,135,71),(0,138,5),(1,138,5),(3,139,140),(1,101,28),(3,3,47),(1,114,71),(0,144,5),(1,145,4),(1,144,5),(2,26,28),(1,71,5),(3,4,149),(0,128,76),(3,2,15),(3,1,15),(0,76,119),(3,2,47),(3,1,47),(2,128,2),(2,25,4),(3,158,38),(2,128,1),(2,25,3),(2,1,4),(1,161,162),(3,162,126),(1,114,27),(0,43,64),(0,166,5),(1,166,5),(3,167,168),(0,25,3),(3,4,5),(1,171,3),(3,71,172),(3,71,15),(3,128,2),(3,22,15),(1,176,1),(2,177,4),(0,128,1),(0,128,2),(2,2,15),(1,181,22),(1,1,15),(3,4,183),(3,53,49),(3,71,132),(3,2,5),(3,1,5),(3,188,119),(3,30,36),(1,190,28),(1,114,0),(3,135,25),(3,25,4),(0,94,3),(1,128,1),(3,0,196),(1,31,3),(2,198,4),(0,2,198),(1,0,200),(1,23,3),(0,1,202),(1,0,203),(2,1,3),(3,205,25),(3,1,4),(0,64,47),(1,1,208),(3,0,209),(3,144,5),(1,211,3),(1,71,3),(1,213,5),(3,4,214),(3,2,49),(1,0,145),(3,0,10),(2,2,1),(2,128,219),(1,8,1),(3,0,221),(3,71,47),(3,223,15),(3,207,25),(0,1,119),(3,135,47),(3,2,132),(3,1,132),(3,2,172),(3,1,172),(2,1,2),(2,196,2),(2,1,5),(3,234,8),(0,38,7),(0,236,5),(1,236,5),(0,76,172),(2,144,5),(2,174,4),(3,223,132),(3,219,47),(0,1,79),(3,155,132),(3,188,8),(3,219,119),(0,8,1),(0,2,119),(3,160,47),(3,219,132),(3,219,15),(3,0,49),(0,25,38),(3,138,47),(0,1,208),(1,0,256),(2,8,5),(0,8,36),(1,0,37),(2,44,2),(3,44,2),(0,44,5),(1,0,237),(2,8,1),(1,128,2),(0,266,1),(3,8,5),(2,44,23),(1,63,31),(2,25,42),(1,170,0),(3,0,238),(3,4,168),(2,236,5),(3,236,5),(0,7,15),(2,1,277),(3,1,277),(0,2,132),(2,3,5),(3,0,183),(2,1,47),(0,1,15),(0,1,132),(3,128,1),(1,187,28),(3,4,36),(1,288,3),(3,2,183),(1,31,4),(3,135,291),(3,2,198),(3,2,3),(2,2,4),(3,2,4),(3,78,38),(2,1,15),(1,298,22),(2,38,4),(1,300,5),(0,38,24),(1,302,4),(2,302,4),(1,37,23),(3,8,1),(1,153,4),(1,0,63),(1,114,5),(2,2,3),(3,310,291),(3,156,64),(3,138,5),(3,25,3),(0,64,36),(0,2,183),(3,3,5),(2,76,53),(3,219,172),(0,213,47),(1,71,4),(1,135,5),(0,38,47),(1,2,323),(0,198,7),(3,2,323),(3,53,3),(1,0,22),(1,22,4),(3,135,321),(1,174,4),(3,135,76),(3,295,15),(1,162,3),(0,334,24),(0,2,172),(0,1,17),(3,162,15),(3,156,132),(3,166,5),(1,155,3),(0,1,172),(1,48,3),(3,6,36),(1,114,187),(1,232,3),(1,346,4),(1,37,5),(3,2,348),(2,346,4),(2,76,4),(2,351,3),(2,346,5),(3,188,64),(1,114,232),(1,232,5),(3,4,356),(1,213,4),(2,76,5),(1,359,3),(1,171,232),(1,346,5),(2,38,5),(2,351,5),(2,2,5),(1,365,37),(1,205,5),(3,4,367),(2,213,4),(3,135,36),(3,310,36),(3,23,38),(1,334,5),(2,213,5),(1,351,5),(1,281,232),(1,187,3),(1,232,22),(1,162,187),(1,232,28),(1,281,71),(1,234,3),(1,171,71),(3,207,24),(1,351,3),(2,76,28),(1,187,37),(1,205,295),(3,310,43),(1,365,162),(1,295,5),(2,64,4),(2,300,5),(2,43,5),(1,394,3),(3,317,43),(1,295,3),(0,1,397),(3,2,334),(2,334,5),(1,310,5),(1,162,5),(1,295,31),(3,3,24),(1,365,3),(3,310,47),(3,365,38),(1,205,171),(1,294,31),(1,63,5),(0,1,410),(1,234,294),(3,317,76),(3,1,3),(1,414,187),(1,198,4),(1,114,31),(3,28,36),(1,187,4),(1,382,4),(3,3,36),(1,234,4),(2,4,5),(3,423,76),(2,382,4),(1,234,28),(1,234,114),(1,377,4),(2,377,4),(1,294,5),(2,1,53),(1,2,22)]
lemma W_17_ok : btAll (fun x => faithful p_17 q_17 x ∧ x.1 < 2^256) W_17 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_17 : List (List (Nat × Nat)) := [[],[(3,4)],[(1,2)],[(1,2),(3,4)]]
def A_17 : BT (List (Nat × Nat)) := btOfList 2 al_17
set_option maxHeartbeats 0 in
lemma A_17_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_17 = g_17) A_17 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_17_0 : Slice r_17 g_17 (subcubeFast 1 0) 10 := by
  have hc : Lower (varsOf 62) 0xffffffc0fcc0c000ffffffc0fcc0c000ffffffc0fcc0c000ffffffc0fcc0c000 10 := carry_of (swaps := [(0,5),(1,5),(2,5),(3,5),(4,5)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_1 : Slice r_17 g_17 (subcubeFast 0 2) 8 := by
  have hc : Lower (varsOf 61) 0xfffffffafff0f0a0fffffffafff0f0a0fffffffafff0f0a0fffffffafff0f0a0 8 := carry_of (swaps := [(1,5),(2,3),(3,5),(4,5)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_2 : Slice r_17 g_17 (subcubeFast 0 4) 8 := by
  have hc : Lower (varsOf 59) 0xffffffeeffcccc88ffffffeeffcccc88ffffffeeffcccc88ffffffeeffcccc88 8 := carry_of (swaps := [(1,3),(2,5),(4,5)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_3 : Slice r_17 g_17 (subcubeFast 8 0) 8 := by
  have hc : Lower (varsOf 55) 0xffffe8e8c0c08080ffffe8e8c0c08080ffffe8e8c0c08080ffffe8e8c0c08080 8 := carry_of (swaps := [(1,2),(2,3),(3,5),(4,5)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_4 : Slice r_17 g_17 (subcubeFast 16 0) 8 := by
  have hc : Lower (varsOf 47) 0xffe8ffe8c080c080ffe8ffe8c080c080ffe8ffe8c080c080ffe8ffe8c080c080 8 := carry_of (swaps := [(1,2),(2,3),(4,5)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_5 : Slice r_17 g_17 (subcubeFast 32 0) 8 := by
  have hc : Lower (varsOf 31) 0xfec0c080fec0c080fec0c080fec0c080fec0c080fec0c080fec0c080fec0c080 8 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_10
  exact slice_fast_direct_f (z := 32) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_6 : Slice r_17 g_17 (identDom 3 4) 9 := by
  have hc : Lower (varsOf 47) 0xffe8ffe8fe80fe80ffe8ffe8fe80fe80ffe8ffe8fe80fe80ffe8ffe8fe80fe80 9 := carry_of (swaps := [(3,4),(4,5)]) (by decide +kernel) low_11
  exact slice_ident (u := 3) (v := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_7 : Slice r_17 g_17 (subcubeFast 24 0) 7 := by
  have hc : Lower (varsOf 39) 0xe8e8e8e880808080e8e8e8e880808080e8e8e8e880808080e8e8e8e880808080 7 := carry_of (swaps := [(3,4),(4,5)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 24) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_8 : Slice r_17 g_17 (subcubeFast 1 2) 7 := by
  have hc : Lower (varsOf 60) 0xfffffff0fff0f000fffffff0fff0f000fffffff0fff0f000fffffff0fff0f000 7 := carry_of (swaps := [(0,4),(1,5),(2,4),(3,5)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 1) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_9 : Slice r_17 g_17 (subcubeFast 33 0) 7 := by
  have hc : Lower (varsOf 30) 0xfcc0c000fcc0c000fcc0c000fcc0c000fcc0c000fcc0c000fcc0c000fcc0c000 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 33) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_10 : Slice r_17 g_17 (subcubeFast 0 1) 8 := by
  have hc : Lower (varsOf 62) 0xfffffffcffc0c0c0fffffffcffc0c0c0fffffffcffc0c0c0fffffffcffc0c0c0 8 := carry_of (swaps := [(0,5),(1,5),(2,3),(3,5),(4,5)]) (by decide +kernel) low_13
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_11 : Slice r_17 g_17 (subcubeFast 4 0) 8 := by
  have hc : Lower (varsOf 59) 0xffffff88ee000000ffffff88ee000000ffffff88ee000000ffffff88ee000000 8 := carry_of (swaps := [(2,5),(3,5),(4,5)]) (by decide +kernel) low_14
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_12 : Slice r_17 g_17 (subcubeFast 2 0) 8 := by
  have hc : Lower (varsOf 61) 0xffffffa0fa000000ffffffa0fa000000ffffffa0fa000000ffffffa0fa000000 8 := carry_of (swaps := [(1,5),(2,5),(3,5),(4,5)]) (by decide +kernel) low_14
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_13 : Slice r_17 g_17 (identDom 1 2) 8 := by
  have hc : Lower (varsOf 59) 0xffffffcceecccc88ffffffcceecccc88ffffffcceecccc88ffffffcceecccc88 8 := carry_of (swaps := [(1,4),(2,5),(3,4),(4,5)]) (by decide +kernel) low_16
  exact slice_ident (u := 1) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_14 : Slice r_17 g_17 (subcubeFast 6 1) 4 := by
  have hc : Lower (varsOf 56) 0xffffff00ff000000ffffff00ff000000ffffff00ff000000ffffff00ff000000 4 := carry_of (swaps := [(0,3),(1,4),(2,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 6) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_15 : Slice r_17 g_17 (subcubeFast 5 2) 4 := by
  have hc : Lower (varsOf 56) 0xffffff00ff000000ffffff00ff000000ffffff00ff000000ffffff00ff000000 4 := carry_of (swaps := [(0,3),(1,4),(2,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 5) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_16 : Slice r_17 g_17 (subcubeFast 3 4) 4 := by
  have hc : Lower (varsOf 56) 0xffffff00ff000000ffffff00ff000000ffffff00ff000000ffffff00ff000000 4 := carry_of (swaps := [(0,3),(1,4),(2,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 3) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_17 : Slice r_17 g_17 (subcubeFast 9 2) 4 := by
  have hc : Lower (varsOf 52) 0xfffff0f0f0f00000fffff0f0f0f00000fffff0f0f0f00000fffff0f0f0f00000 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 9) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_18 : Slice r_17 g_17 (subcubeFast 17 2) 4 := by
  have hc : Lower (varsOf 44) 0xfff0fff0f000f000fff0fff0f000f000fff0fff0f000f000fff0fff0f000f000 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 17) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_19 : Slice r_17 g_17 (subcubeFast 33 2) 4 := by
  have hc : Lower (varsOf 28) 0xfff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 33) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_20 : Slice r_17 g_17 (subcubeFast 9 4) 4 := by
  have hc : Lower (varsOf 50) 0xffffcccccccc0000ffffcccccccc0000ffffcccccccc0000ffffcccccccc0000 4 := carry_of (swaps := [(0,3),(1,3),(2,4),(3,5),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 9) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_21 : Slice r_17 g_17 (subcubeFast 17 4) 4 := by
  have hc : Lower (varsOf 42) 0xffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00 4 := carry_of (swaps := [(0,3),(1,3),(2,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 17) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_22 : Slice r_17 g_17 (subcubeFast 33 4) 4 := by
  have hc : Lower (varsOf 26) 0xffcccc00ffcccc00ffcccc00ffcccc00ffcccc00ffcccc00ffcccc00ffcccc00 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 33) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_23 : Slice r_17 g_17 (subcubeFast 33 8) 4 := by
  have hc : Lower (varsOf 22) 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0 4 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 33) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_24 : Slice r_17 g_17 (subcubeFast 33 16) 4 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 33) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_25 : Slice r_17 g_17 (subcubeFast 24 2) 4 := by
  have hc : Lower (varsOf 37) 0xfafafafaa0a0a0a0fafafafaa0a0a0a0fafafafaa0a0a0a0fafafafaa0a0a0a0 4 := carry_of (swaps := [(1,3),(2,3),(3,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 24) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_26 : Slice r_17 g_17 (subcubeFast 24 4) 4 := by
  have hc : Lower (varsOf 35) 0xeeeeeeee88888888eeeeeeee88888888eeeeeeee88888888eeeeeeee88888888 4 := carry_of (swaps := [(2,3),(3,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 24) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_27 : Slice r_17 g_17 (subcubeFast 24 32) 4 := by
  exact slice_fast_direct_f (z := 24) (o := 32) (by decide +kernel) low_0
def S_17 : BT (Option (Nat × Nat)) := btOfList 5 [some (subcubeFast 1 0,10),some (subcubeFast 0 2,8),some (subcubeFast 0 4,8),some (subcubeFast 8 0,8),some (subcubeFast 16 0,8),some (subcubeFast 32 0,8),some (identDom 3 4,9),some (subcubeFast 24 0,7),some (subcubeFast 1 2,7),some (subcubeFast 33 0,7),some (subcubeFast 0 1,8),some (subcubeFast 4 0,8),some (subcubeFast 2 0,8),some (identDom 1 2,8),some (subcubeFast 6 1,4),some (subcubeFast 5 2,4),some (subcubeFast 3 4,4),some (subcubeFast 9 2,4),some (subcubeFast 17 2,4),some (subcubeFast 33 2,4),some (subcubeFast 9 4,4),some (subcubeFast 17 4,4),some (subcubeFast 33 4,4),some (subcubeFast 33 8,4),some (subcubeFast 33 16,4),some (subcubeFast 24 2,4),some (subcubeFast 24 4,4),some (subcubeFast 24 32,4)]
lemma S_17_ok : btAll (fun o => ∀ p, o = some p → Slice r_17 g_17 p.1 p.2) S_17 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_17_0) (forall_cons (fun _ h => by cases h; exact sl_17_1) (forall_cons (fun _ h => by cases h; exact sl_17_2) (forall_cons (fun _ h => by cases h; exact sl_17_3) (forall_cons (fun _ h => by cases h; exact sl_17_4) (forall_cons (fun _ h => by cases h; exact sl_17_5) (forall_cons (fun _ h => by cases h; exact sl_17_6) (forall_cons (fun _ h => by cases h; exact sl_17_7) (forall_cons (fun _ h => by cases h; exact sl_17_8) (forall_cons (fun _ h => by cases h; exact sl_17_9) (forall_cons (fun _ h => by cases h; exact sl_17_10) (forall_cons (fun _ h => by cases h; exact sl_17_11) (forall_cons (fun _ h => by cases h; exact sl_17_12) (forall_cons (fun _ h => by cases h; exact sl_17_13) (forall_cons (fun _ h => by cases h; exact sl_17_14) (forall_cons (fun _ h => by cases h; exact sl_17_15) (forall_cons (fun _ h => by cases h; exact sl_17_16) (forall_cons (fun _ h => by cases h; exact sl_17_17) (forall_cons (fun _ h => by cases h; exact sl_17_18) (forall_cons (fun _ h => by cases h; exact sl_17_19) (forall_cons (fun _ h => by cases h; exact sl_17_20) (forall_cons (fun _ h => by cases h; exact sl_17_21) (forall_cons (fun _ h => by cases h; exact sl_17_22) (forall_cons (fun _ h => by cases h; exact sl_17_23) (forall_cons (fun _ h => by cases h; exact sl_17_24) (forall_cons (fun _ h => by cases h; exact sl_17_25) (forall_cons (fun _ h => by cases h; exact sl_17_26) (forall_cons (fun _ h => by cases h; exact sl_17_27) (fun _ h => (List.not_mem_nil h).elim)))))))))))))))))))))))))))))
def ps_17 : BT (Option PoolSpec) := btOfList 11 ((([(13,[(0,3,4),(1,3,4)]),(6,[(0,1,5),(1,1,5),(3,31,36),(2,94,2),(3,94,2)]),(6,[(0,2,5),(1,2,5),(3,23,24),(2,25,1),(1,101,0)]),(0,[(0,2,4),(1,2,4),(3,6,7),(0,8,5),(1,8,5),(3,9,10)]),(7,[(0,8,5),(1,8,5),(3,9,10)]),(14,[]),(0,[(0,1,3),(1,1,3),(3,37,38),(0,2,5),(1,2,5),(3,23,24)]),(6,[(0,2,5),(1,2,5),(3,23,24),(0,25,1),(1,25,1)]),(6,[(0,2,5),(1,2,5),(3,23,24),(3,25,1),(1,0,108)]),(0,[(0,4,5),(1,4,5),(0,2,47),(1,2,47),(3,78,79)]),(7,[(0,2,47),(1,2,47),(3,78,79)]),(0,[(0,2,5),(1,2,5),(0,3,4),(1,23,28),(1,3,4)]),(5,[(0,3,4),(0,1,86),(1,3,4)]),(7,[(0,2,5),(1,2,5)]),(10,[(0,2,5),(1,2,5),(3,23,24)]),(0,[(0,2,5),(1,2,5),(3,23,24)]),(0,[(0,2,5),(1,2,5),(3,23,24),(0,3,4),(1,3,4)]),(23,[]),(7,[(0,2,5),(1,2,5),(3,23,24)]),(6,[(0,2,5),(1,2,5),(3,23,24),(3,25,1)]),(1,[(0,2,5),(1,2,5),(3,23,24),(1,0,108)]),(12,[(0,2,5),(1,2,5),(3,23,24)]),(10,[(0,1,5),(1,1,5),(3,31,36)]),(0,[(0,1,5),(1,1,5),(3,31,36)]),(0,[(0,1,5),(1,1,5),(3,31,36),(2,94,2),(3,94,2)]),(13,[(2,3,4)]),(13,[(0,3,4)]),(0,[(0,1,5),(1,1,5),(3,31,36),(0,3,4),(1,3,4)]),(6,[(0,1,5),(1,1,5),(3,31,36),(2,94,2)]),(6,[(0,2,5),(1,2,5),(3,23,24),(1,25,1)]),(11,[(0,4,5),(1,4,5),(0,76,47),(3,53,47)]),(1,[(0,4,5),(1,4,5),(3,53,47)]),(13,[(0,4,5),(1,71,53),(1,4,5)]),(1,[(0,4,5),(1,71,53),(1,4,5)]),(13,[(0,4,5),(1,71,53),(1,4,5),(3,90,47)]),(11,[(0,4,5),(1,4,5),(3,90,47)]),(13,[(0,3,5),(1,71,22),(1,3,5)]),(1,[(0,3,5),(1,71,22),(1,3,5)]),(11,[(0,3,5),(1,3,5),(0,76,15)]),(7,[(0,1,2),(1,1,2),(0,76,15)]),(3,[(0,2,5),(1,2,5),(3,23,24),(2,25,1)]),(0,[(0,1,3),(1,1,3),(3,37,38),(0,39,5),(1,39,5),(3,55,56)]),(7,[(0,39,5),(1,39,5),(3,55,56)]),(13,[(1,3,4)]),(0,[(0,1,2),(1,1,2),(0,3,4),(1,71,28),(1,3,4)]),(1,[(0,3,4),(1,71,28),(1,3,4)]),(11,[(0,3,4),(1,3,4),(0,72,5)]),(7,[(0,1,2),(1,1,2)]),(13,[(1,4,3),(1,30,5),(3,4,132),(3,3,132)]),(13,[(0,3,4),(1,71,28),(1,3,4)]),(6,[(0,1,2),(1,1,2),(1,71,28)]),(16,[]),(11,[(0,4,5),(1,4,5),(3,53,47),(0,128,76)]),(11,[(0,4,5),(1,4,5),(3,53,47),(2,128,1)]),(0,[(0,1,4),(1,1,4),(3,42,43),(0,2,5),(1,2,5),(3,23,24)]),(22,[]),(0,[(0,2,5),(1,2,5),(3,23,24),(0,25,1),(1,25,1)]),(3,[(0,2,5),(1,2,5),(3,23,24)]),(6,[(0,2,5),(1,2,5),(3,23,24),(0,25,1)]),(8,[(0,2,5),(1,2,5),(3,23,24)]),(12,[(0,4,5),(1,4,5),(3,53,47)]),(11,[(0,4,5),(1,4,5),(3,53,47)]),(24,[]),(0,[(0,4,5),(1,4,5),(3,53,47),(2,128,2),(3,128,2)]),(2,[(0,4,5),(1,4,5),(3,53,47)]),(7,[(2,128,2),(3,128,2)]),(0,[(1,4,5),(0,2,47),(1,2,47),(3,78,79)]),(21,[]),(7,[(1,176,1)]),(12,[(0,3,5),(1,3,5),(3,22,15),(2,177,4)]),(0,[(0,3,5),(1,3,5),(3,22,15),(1,176,1),(2,177,4)]),(1,[(0,3,5),(1,3,5),(3,22,15)]),(11,[(0,4,5),(1,4,5),(3,53,47),(0,128,1)]),(0,[(0,3,5),(1,3,5),(2,2,15),(1,181,22),(3,2,15)]),(2,[(0,3,5),(1,3,5),(1,181,22)]),(11,[(0,3,5),(1,3,5)]),(7,[(2,2,15),(3,2,15)]),(7,[(1,1,15)]),(0,[(0,4,5),(1,4,5),(0,1,47),(1,1,47),(3,53,49)]),(18,[]),(12,[(0,4,5),(1,4,5),(3,53,49)]),(7,[(0,1,47),(1,1,47)]),(4,[]),(1,[(0,3,4),(1,28,5),(1,3,4)]),(27,[]),(0,[(3,1,5),(0,3,4),(1,28,5),(3,188,119),(1,3,4)]),(2,[(0,3,4),(1,28,5),(1,3,4)]),(5,[(0,3,4),(1,3,4)]),(7,[]),(0,[(1,1,5),(0,3,4),(1,3,4),(3,30,36),(1,190,28)]),(25,[]),(5,[(0,3,4),(1,3,4),(3,30,36),(1,190,28)]),(0,[(0,1,5),(0,3,4),(1,31,28),(1,3,4)]),(12,[(0,3,4),(1,3,4)]),(1,[(0,3,4),(1,31,28),(1,3,4)]),(2,[(0,3,4),(1,23,28),(1,3,4)]),(0,[(0,2,5),(1,2,5),(0,3,4),(1,23,28)]),(5,[(0,3,4)]),(3,[(0,2,5),(1,2,5)]),(4,[(0,2,5),(1,2,5)]),(4,[(0,2,5),(1,2,5),(3,23,24),(1,114,0)]),(4,[(0,2,5),(1,2,5),(3,23,24)]),(0,[(0,2,5),(1,2,5),(3,23,24),(2,4,3),(3,135,25)]),(1,[(0,2,5),(1,2,5),(3,23,24)]),(0,[(0,2,5),(1,2,5),(3,23,24),(0,3,4),(2,25,28)]),(0,[(0,2,5),(1,2,5),(3,23,24),(2,25,4),(3,25,4)]),(0,[(0,2,5),(1,2,5),(3,23,24),(0,25,3),(1,25,3)]),(2,[(0,1,5),(1,1,5),(3,31,36)]),(3,[(0,1,5),(1,1,5),(3,31,36)]),(0,[(0,1,5),(1,1,5),(3,31,36),(2,94,2)]),(0,[(0,1,5),(1,1,5),(3,31,36),(2,3,4)]),(0,[(0,1,5),(1,1,5),(3,31,36),(1,3,4)]),(7,[(0,1,5),(1,1,5),(3,31,36)]),(0,[(0,1,5),(1,1,5),(3,31,36),(0,3,4)]),(19,[]),(0,[(0,2,5),(1,2,5),(3,23,24),(2,25,4)]),(11,[(0,1,5),(1,1,5),(3,31,36)]),(0,[(0,1,5),(1,1,5),(3,31,36),(0,94,3)]),(13,[]),(0,[(0,2,5),(1,2,5),(3,23,24),(2,25,1)]),(0,[(0,2,5),(1,2,5),(3,23,24),(1,25,1)]),(6,[(0,2,5),(1,2,5),(3,23,24)]),(0,[(0,4,5),(1,4,5),(3,53,47),(1,128,1)]),(8,[(0,4,5),(1,4,5),(3,53,47)]),(7,[(1,128,1),(3,0,196)]),(0,[(0,2,5),(1,2,5),(3,23,24),(0,25,1)]),(12,[(0,4,5),(1,4,5),(3,53,47),(2,128,2)]),(8,[(0,2,5),(1,23,3)]),(0,[(0,2,5),(0,3,4),(1,23,28),(1,3,4)]),(11,[(0,3,4),(1,3,4)]),(7,[(0,2,5)]),(0,[(2,1,3),(0,2,5),(1,2,5),(3,23,24),(3,205,25)]),(0,[(0,2,5),(1,2,5),(3,23,24),(3,25,1)]),(0,[(0,2,5),(1,2,5),(3,23,24),(2,3,4)]),(0,[(2,1,4),(3,1,4),(0,2,5),(1,2,5),(3,23,24)]),(5,[]),(6,[(0,1,2),(1,3,5),(3,71,15)]),(0,[(0,4,5),(1,4,5),(3,53,47),(0,128,1),(1,128,1)]),(7,[(0,128,1),(1,128,1)]),(0,[(0,4,5),(1,4,5),(1,1,47),(3,2,49),(3,53,47)]),(7,[(1,1,47),(3,2,49)]),(3,[(0,1,2),(1,1,2),(0,76,15)]),(1,[(0,3,5),(1,3,5)]),(0,[(0,1,2),(1,1,2),(0,4,5),(1,71,53),(1,4,5)]),(11,[(0,4,5),(1,4,5)]),(0,[(0,2,4),(1,2,4),(3,6,7),(1,8,5)]),(5,[(0,2,4),(1,2,4),(3,6,7),(3,0,10)]),(7,[(1,8,5),(3,0,10)]),(0,[(0,4,5),(1,4,5),(3,53,47)]),(0,[(2,2,1),(0,4,5),(1,4,5),(3,53,47),(2,128,219)]),(3,[(0,4,5),(1,4,5),(3,53,47)]),(7,[(2,2,1),(2,128,219)]),(0,[(0,2,4),(1,2,4),(3,6,7),(1,8,1)]),(8,[(0,2,4),(1,2,4),(3,6,7)]),(7,[(1,8,1),(3,0,221)]),(11,[(0,4,5),(1,4,5),(0,1,47),(3,53,47)]),(10,[]),(0,[]),(0,[(3,1,4),(0,2,5),(1,2,5),(3,23,24),(3,207,25)]),(1,[]),(11,[(0,3,4),(1,28,5),(1,3,4)]),(13,[(2,4,3),(1,4,5),(3,135,47)]),(4,[(0,1,2),(1,1,2)]),(2,[(0,3,5),(1,71,22),(1,3,5)]),(12,[(0,3,5),(1,3,5),(3,2,15)]),(0,[(0,2,4),(1,2,4),(3,6,7),(0,1,5),(1,1,5)]),(5,[(0,2,4),(1,2,4),(3,6,7)]),(7,[(0,1,5),(1,1,5)]),(1,[(0,2,4),(1,2,4),(3,6,7)]),(11,[(0,4,5),(1,4,5),(2,223,53)]),(12,[(0,3,4),(1,28,5),(1,3,4)]),(4,[(0,1,2),(3,71,47)]),(0,[(0,1,2),(0,4,5),(1,4,5),(3,71,47),(3,53,47)]),(7,[(0,1,2),(3,71,47)]),(0,[(0,1,2),(0,3,4),(1,71,28),(1,3,4)]),(2,[(0,3,4),(1,71,28),(1,3,4)]),(6,[(0,1,2),(1,71,28)]),(13,[(1,4,3),(1,4,5),(1,3,5)]),(5,[(0,1,2),(1,1,2)]),(3,[(0,1,2),(1,1,2)]),(0,[(0,1,2),(1,1,2),(0,3,4),(1,28,5),(1,3,4)]),(13,[(0,3,4),(1,28,5),(1,3,4)]),(0,[(0,4,5),(1,4,5),(3,53,47),(1,128,1),(2,196,2)]),(7,[(1,128,1),(2,196,2)]),(7,[(0,1,2)]),(12,[(0,2,4),(1,2,4),(3,6,7)]),(0,[(0,2,4),(1,2,4),(3,6,7)]),(0,[(0,2,4),(1,2,4),(3,6,7),(2,1,5),(3,234,8)]),(3,[(0,2,4),(1,2,4),(3,6,7)]),(7,[(2,1,5),(3,234,8)]),(2,[(0,4,5),(1,71,53),(1,4,5)]),(4,[(0,1,2),(3,90,47)]),(12,[(0,4,5),(1,4,5),(3,90,47)]),(0,[(0,2,5),(1,2,5),(3,23,24),(0,3,4)]),(0,[(0,1,2),(1,1,2),(0,3,4),(1,71,28)]),(1,[(0,3,4),(1,71,28)]),(11,[(0,3,4)]),(7,[(0,1,2),(1,1,2),(0,76,132)]),(5,[(1,4,3),(3,4,132),(3,3,132)]),(0,[(1,1,2),(0,4,5),(1,4,5),(0,76,47),(3,53,47)]),(7,[(1,1,2),(0,76,47)]),(13,[(0,3,4),(1,71,28)]),(0,[(0,1,2),(0,4,5),(1,71,53),(1,4,5),(3,90,47)]),(7,[(0,1,2),(3,90,47)]),(0,[(0,1,2),(1,1,2),(0,4,5),(1,4,5),(3,53,47)]),(13,[(0,4,5),(1,4,5),(3,53,47)]),(0,[(0,1,2),(0,3,4),(1,28,5),(3,71,119),(1,3,4)]),(12,[(0,4,5),(1,4,5),(3,2,47),(3,53,47)]),(1,[(1,3,5),(1,4,15)]),(11,[]),(11,[(0,3,5),(1,3,5),(3,1,15)]),(0,[(2,2,1),(0,4,5),(1,4,5),(3,219,47),(3,53,47)]),(7,[(2,2,1),(3,219,47)]),(0,[(1,1,2),(0,4,5),(1,4,5),(3,53,47),(0,128,76)]),(7,[(1,1,2),(0,128,76)]),(0,[(0,1,2),(1,1,2)]),(13,[(1,4,3),(1,30,5),(3,4,132)]),(0,[(0,1,3),(1,1,3),(0,2,5),(1,2,5),(3,23,24)]),(0,[(0,1,2),(0,4,5),(1,4,5),(3,53,47),(2,128,71)]),(7,[(0,1,2),(2,128,71)]),(0,[(0,4,5),(1,4,5),(1,2,47),(0,1,79),(3,53,47)]),(0,[(0,2,4),(1,2,4),(3,6,7),(3,1,5),(3,188,8)]),(7,[(3,1,5),(3,188,8)]),(13,[(1,4,5),(1,3,5),(3,4,15)]),(3,[]),(0,[(0,2,4),(1,2,4),(3,6,7),(0,8,1),(1,8,1)]),(7,[(0,8,1),(1,8,1)]),(0,[(0,2,5),(1,2,5),(3,23,24),(1,3,4)]),(0,[(0,4,5),(1,4,5),(3,53,47),(2,128,1),(3,160,47)]),(7,[(2,128,1),(3,160,47)]),(13,[(1,3,4),(1,3,5),(3,4,15)]),(3,[(0,1,2),(3,71,119)]),(4,[(2,128,2)]),(0,[(0,4,5),(1,4,5),(1,1,47),(3,53,47)]),(7,[(1,1,47),(3,0,49)]),(0,[(1,1,3),(0,2,5),(1,2,5),(3,23,24),(0,25,38)]),(0,[(0,2,4),(1,2,4),(3,6,7),(1,1,5),(0,8,36)]),(7,[(1,1,5),(0,8,36)]),(0,[(0,1,4),(1,1,4),(3,42,43),(2,44,2),(3,44,2)]),(2,[(0,1,4),(1,1,4),(3,42,43)]),(11,[(0,1,4),(1,1,4),(3,42,43)]),(7,[(2,44,2),(3,44,2)]),(5,[(0,1,4),(1,1,4),(3,42,43)]),(0,[(0,2,4),(1,2,4),(3,6,7),(0,8,5),(1,8,5)]),(7,[(0,8,5),(1,8,5)]),(0,[(0,4,5),(1,4,5),(3,53,47),(1,128,2),(0,266,1)]),(0,[(0,2,4),(1,2,4),(3,6,7),(2,8,5),(3,8,5)]),(12,[]),(0,[(0,1,4),(1,1,4),(3,42,43)]),(0,[(0,1,4),(1,1,4),(3,42,43),(0,2,5),(2,44,23)]),(3,[(0,1,4),(1,1,4),(3,42,43)]),(7,[(0,2,5),(2,44,23)]),(0,[(0,2,4),(1,2,4),(3,6,7),(2,1,5),(3,1,5)]),(7,[(2,1,5),(3,1,5)]),(0,[(0,2,3),(1,2,3),(0,1,5),(1,63,31),(1,1,5)]),(2,[(0,1,5),(1,63,31),(1,1,5)]),(1,[(0,2,3),(1,2,3),(1,63,31)]),(0,[(0,1,4),(0,2,5),(1,2,5),(3,23,24),(2,25,42)]),(0,[(0,2,5),(1,2,5),(3,23,24),(0,25,3)]),(2,[]),(12,[(3,4,5),(1,171,3)]),(11,[(3,4,5),(1,171,3)]),(12,[(2,3,5),(1,281,5)]),(11,[(2,3,5),(1,281,5)]),(0,[(1,3,5),(1,1,15),(3,2,15)]),(8,[(1,3,5),(3,2,15)]),(2,[(1,3,5),(1,1,15),(3,0,183)]),(5,[(1,1,15),(3,0,183)]),(3,[(1,1,15),(3,0,183)]),(0,[(0,4,5),(1,4,5),(3,53,47),(2,128,2)]),(7,[(2,128,2)]),(7,[(1,128,1)]),(0,[(0,4,5),(1,4,5),(3,53,47),(0,128,1)]),(7,[(0,128,1)]),(0,[(0,4,5),(1,4,5),(3,2,47),(3,53,47)]),(7,[(3,2,47)]),(2,[(0,3,5),(1,3,5)]),(12,[(0,3,5),(1,3,5)]),(0,[(0,4,5),(1,4,5),(2,1,47),(3,53,47)]),(7,[(2,1,47)]),(12,[(0,4,5),(1,4,5)]),(1,[(0,4,5),(1,4,5)]),(4,[(2,1,47),(3,1,47)]),(0,[(0,4,5),(1,4,5),(2,1,47),(3,1,47)]),(7,[(2,1,47),(3,1,47)]),(0,[(0,3,5),(1,3,5),(1,1,15)]),(8,[(0,3,5),(1,3,5)]),(7,[(1,1,15),(3,0,183)]),(4,[(0,1,47)]),(7,[(0,1,47)]),(12,[(1,3,4),(1,30,5)]),(11,[(1,3,4),(1,30,5)]),(4,[(1,30,5)]),(11,[(1,4,3),(1,30,5),(3,4,132)]),(7,[(0,1,132)]),(12,[(1,4,3),(1,30,5),(3,4,132)]),(12,[(1,3,4),(1,3,5)]),(11,[(1,3,4),(1,3,5)]),(0,[(0,4,5),(1,4,5),(3,53,47),(3,128,1)]),(7,[(3,128,1)]),(0,[(0,3,4),(1,28,5),(1,3,4)]),(0,[(0,3,4),(1,28,5),(3,2,119),(1,3,4)]),(12,[(0,3,4),(1,28,5)]),(11,[(0,3,4),(1,28,5)]),(0,[(0,3,4),(1,28,5),(0,1,119),(1,3,4)]),(1,[(0,3,4),(1,28,5)]),(0,[(3,2,5),(0,3,4),(1,187,28),(1,3,4)]),(2,[(0,3,4),(1,3,4)]),(20,[]),(7,[(3,2,5)]),(0,[(1,1,5),(2,3,4),(3,4,36),(1,288,3)]),(3,[(1,1,5),(3,4,36)]),(5,[(2,3,4),(3,4,36),(1,288,3)]),(0,[(1,1,5),(0,3,4),(1,3,4),(3,30,36)]),(1,[(0,3,4),(1,3,4)]),(3,[(1,1,5),(3,30,36)]),(0,[(1,1,5),(0,3,4),(1,28,5),(1,3,4)]),(7,[(1,1,5)]),(0,[(2,3,4),(1,3,5),(3,114,15),(0,1,15)]),(12,[(2,3,4),(1,3,5),(3,114,15)]),(11,[(2,3,4),(1,3,5),(3,114,15)]),(7,[(0,1,15)]),(2,[(0,3,4),(1,28,5)]),(0,[(0,1,5),(0,3,4),(1,31,28)]),(12,[(0,3,4)]),(1,[(0,3,4),(1,31,28)]),(5,[(2,3,4),(1,114,0)]),(10,[(0,1,5),(1,1,5)]),(1,[(2,3,4),(1,114,0)]),(3,[(0,1,5),(1,1,5)]),(4,[(0,1,5),(1,1,5),(1,114,0)]),(0,[(0,1,5),(1,1,5),(0,3,4),(1,3,4)]),(6,[(0,1,5),(1,1,5)]),(2,[(0,3,4),(1,23,28)]),(0,[(3,2,5),(0,3,4),(1,28,5),(1,3,4)]),(4,[(0,1,5),(1,1,5),(3,31,36)]),(7,[(0,1,5)]),(0,[(0,3,5),(1,3,5),(1,1,15),(3,2,183)]),(3,[(1,1,15),(3,2,183)]),(0,[(0,1,5),(1,31,4),(2,4,3),(3,135,291)]),(4,[(0,1,5)]),(5,[(2,4,3),(3,135,291)]),(2,[(0,1,5),(1,31,4)]),(6,[(0,1,5),(1,31,4)]),(2,[(0,1,5),(1,31,3)]),(7,[(0,1,5),(0,2,198)]),(0,[(0,1,5),(1,31,3),(2,198,4)]),(5,[(2,198,4)]),(1,[(0,2,5),(1,23,3),(1,0,203)]),(0,[(0,2,5),(1,23,3),(0,1,202)]),(9,[(0,1,202)]),(11,[(0,1,202),(1,0,203)]),(7,[(0,2,5),(0,1,202),(1,0,203)]),(0,[(3,2,3),(0,1,5),(1,1,5),(3,31,36)]),(6,[(1,30,5),(3,4,132)]),(0,[(1,4,3),(1,30,5),(3,4,132),(3,3,132)]),(1,[(1,3,5),(0,2,15)]),(12,[(1,3,5),(3,4,15)]),(11,[(2,1,5),(3,1,5)]),(2,[(2,1,5),(3,1,5)]),(12,[(2,2,4),(3,2,4)]),(1,[(2,2,4),(3,2,4)]),(0,[(2,2,4),(3,2,4),(2,1,5),(3,1,5)]),(12,[(0,2,5),(1,2,5)]),(1,[(0,2,5),(1,2,5)]),(0,[(2,1,4),(3,1,4),(0,2,5),(1,2,5)]),(5,[(2,1,4),(3,1,4)]),(2,[(2,1,4),(3,1,4)]),(0,[(1,2,3),(1,4,5),(0,64,47)]),(2,[(1,4,5)]),(11,[(1,4,5),(0,64,47)]),(3,[(1,4,5),(0,64,47)]),(5,[(1,2,3),(0,64,47)]),(4,[(1,2,3),(0,64,47)]),(1,[(1,3,5),(3,2,15)]),(11,[(1,3,5)]),(1,[(1,4,5),(0,2,47)]),(7,[(0,2,47),(3,78,38)]),(0,[(0,3,5),(1,3,5),(2,1,15),(1,298,22)]),(3,[(2,1,15)]),(7,[(2,1,15)]),(0,[(1,1,3),(2,38,4),(1,300,5),(3,4,5)]),(1,[(1,300,5),(3,4,5)]),(5,[(1,1,3),(2,38,4)]),(3,[(2,38,4),(1,300,5),(3,4,5)]),(7,[(1,300,5)]),(2,[(1,1,3)]),(1,[(1,2,5)]),(7,[(1,2,5),(0,38,24)]),(7,[(1,1,47)]),(0,[(1,1,3),(1,2,4),(0,38,7)]),(1,[(1,2,4)]),(0,[(0,1,3),(0,2,5),(1,37,23),(1,2,5)]),(5,[(0,1,3)]),(2,[(0,1,3),(1,37,23)]),(12,[(0,2,3),(1,2,3)]),(1,[(0,2,3),(1,2,3)]),(0,[(0,2,3),(1,2,3),(2,1,5),(3,1,5)]),(3,[(2,1,5),(3,1,5)]),(0,[(0,2,3),(1,2,3),(0,1,5),(1,63,31)]),(3,[(0,1,5)]),(2,[(0,1,5),(1,63,31)]),(5,[(0,2,3),(1,2,3)]),(0,[(0,2,5),(1,2,5),(3,23,24),(1,25,3)]),(0,[(0,1,4),(1,1,4),(3,42,43),(3,2,5)]),(0,[(0,2,4),(1,2,4),(3,6,7),(2,1,5)]),(7,[(2,1,5)]),(0,[(0,2,4),(1,2,4),(3,6,7),(1,1,5)]),(0,[(0,2,5),(0,3,4),(1,23,28)]),(3,[(0,2,5)]),(4,[(0,2,5)]),(0,[(0,2,4),(1,2,4),(3,6,7),(0,1,5)]),(0,[(0,2,4),(1,2,4),(3,6,7),(3,8,1)]),(7,[(3,8,1)]),(0,[(0,1,4),(1,1,4),(3,42,43),(2,44,2)]),(7,[(2,44,2)]),(12,[(0,2,3),(1,0,63)]),(1,[(0,2,3),(1,0,63)]),(0,[(0,2,3),(2,1,5),(3,1,5)]),(10,[(2,1,5),(3,1,5)]),(2,[(1,0,63),(2,1,5),(3,1,5)]),(1,[(2,3,4),(1,3,5)]),(0,[(0,1,2),(1,1,2),(2,3,4),(1,114,5)]),(13,[(2,3,4),(1,114,5)]),(11,[(2,3,4),(1,114,5)]),(1,[(2,3,4),(1,114,5)]),(0,[(0,4,5),(1,4,5),(1,1,47),(3,53,49)]),(2,[(1,3,5)]),(11,[(1,3,5),(0,7,15)]),(4,[(1,3,5),(0,7,15)]),(2,[(1,3,5),(0,1,15)]),(1,[(1,3,5)]),(7,[(0,1,15),(0,7,15)]),(0,[(0,1,2),(1,1,2),(2,3,5),(1,281,5)]),(13,[(2,3,5),(1,281,5)]),(1,[(2,3,5),(1,281,5)]),(4,[(1,3,47)]),(0,[(1,4,5),(0,1,47),(1,3,47),(3,4,132)]),(12,[(1,4,5),(1,3,47),(3,4,132)]),(11,[(1,4,5),(1,3,47),(3,4,132)]),(0,[(2,1,2)]),(7,[(2,1,2)]),(0,[(0,1,2)]),(0,[(2,1,4),(0,2,5),(1,2,5),(3,23,24)]),(0,[(2,1,2),(0,3,4),(1,28,5),(1,3,4)]),(0,[(0,1,3),(1,1,3),(0,2,5),(1,2,5)]),(5,[(0,1,3),(1,1,3)]),(2,[(0,1,3),(1,1,3)]),(3,[(1,30,5)]),(7,[(0,1,2),(3,71,15)]),(2,[(1,4,5),(3,1,47)]),(7,[(3,1,47),(3,156,64)]),(0,[(0,1,2),(0,3,4),(1,71,28)]),(2,[(0,3,4),(1,71,28)]),(3,[(0,1,2)]),(4,[(0,1,2)]),(7,[(1,8,5)]),(0,[(0,1,2),(0,3,4),(1,28,5),(1,3,4)]),(0,[(0,1,2),(0,3,4),(1,28,5),(3,71,119)]),(4,[(0,1,2),(3,71,119)]),(0,[(0,1,2),(0,4,5),(1,71,53),(1,4,5)]),(3,[(0,1,2),(1,135,71)]),(0,[(0,2,5),(1,2,5),(3,23,24),(3,25,3)]),(7,[(1,1,5),(0,64,36)]),(2,[(2,1,4),(1,1,5)]),(12,[(1,2,3),(0,64,36)]),(5,[(1,2,3),(0,64,36)]),(12,[(0,3,4),(1,28,5),(3,2,119)]),(0,[(1,3,5),(0,1,15),(1,1,15),(0,2,183)]),(11,[(1,3,5),(0,1,15)]),(5,[(0,1,15),(1,1,15),(0,2,183)]),(7,[(0,1,15),(1,1,15),(0,2,183)]),(12,[(1,3,5),(0,2,183)]),(0,[(0,1,2),(1,1,2),(1,3,5),(0,76,15)]),(11,[(1,3,5),(0,76,15)]),(5,[(0,1,2),(1,1,2),(0,76,15)]),(0,[(0,1,2),(1,1,2),(1,3,5),(3,4,15)]),(11,[(1,3,5),(3,4,15)]),(1,[(1,3,5),(3,4,15)]),(13,[(1,3,5),(3,4,15)]),(11,[(0,3,5),(1,3,5),(0,1,15)]),(2,[(1,3,5),(3,1,15)]),(11,[(1,3,5),(3,1,15)]),(7,[(1,8,1)]),(0,[(0,1,2),(1,1,2),(3,4,5),(1,171,3)]),(13,[(3,4,5),(1,171,3)]),(1,[(3,4,5),(1,171,3)]),(1,[(1,3,4),(1,3,5)]),(7,[(0,2,1),(3,2,15)]),(0,[(0,1,2),(1,1,2),(2,3,5),(3,3,5)]),(13,[(2,3,5),(3,3,5)]),(7,[(2,2,1),(3,219,132)]),(10,[(0,1,2),(1,1,2)]),(13,[(2,3,4),(1,114,0)]),(11,[(2,3,4),(1,114,0)]),(4,[(0,1,2),(1,1,2),(1,114,0)]),(0,[(0,2,4),(1,2,4),(3,6,7),(3,8,5)]),(7,[(3,8,5)]),(0,[(0,1,2),(1,1,2),(0,3,4),(1,28,5)]),(13,[(0,3,4),(1,28,5)]),(0,[(0,1,2),(1,1,2),(0,4,5),(2,76,53)]),(13,[(0,4,5),(2,76,53)]),(0,[(0,1,2),(3,4,5),(1,171,3),(3,71,172)]),(7,[(0,1,2),(3,71,172)]),(5,[(0,1,2),(3,71,172)]),(0,[(1,1,2)]),(7,[(1,1,2)]),(15,[]),(2,[(1,3,4),(1,30,5)]),(0,[(1,1,3),(0,2,5),(1,2,5),(3,23,24)]),(0,[(0,1,2),(1,71,3),(1,213,5),(3,4,214)]),(12,[(1,213,5),(3,4,214)]),(11,[(1,213,5),(3,4,214)]),(3,[(0,1,2),(1,213,5),(3,4,214)]),(12,[(2,3,4),(1,3,5)]),(11,[(2,3,4),(1,3,5)]),(11,[(1,4,5)]),(7,[(0,1,2),(0,213,47)]),(3,[(0,1,2),(3,71,15)]),(0,[(0,1,3),(0,2,5),(1,2,5),(3,23,24)]),(13,[(1,3,5),(1,4,5)]),(1,[(1,4,5)]),(3,[(3,4,5)]),(0,[(0,1,2),(1,71,4),(2,4,3),(1,135,5)]),(0,[(1,1,3),(1,4,5),(0,38,47)]),(12,[(1,4,5),(0,38,47)]),(3,[(1,4,5),(0,38,47)]),(0,[(1,2,4),(0,1,5),(1,31,3),(0,198,7)]),(7,[(0,1,5),(0,198,7)]),(5,[(1,2,4),(0,198,7)]),(12,[(1,3,5),(3,2,15)]),(13,[(1,4,3),(1,4,5)]),(11,[(1,4,3),(1,4,5)]),(1,[(1,4,3),(1,4,5)]),(7,[(0,1,5),(3,2,198)]),(11,[(0,1,5),(1,31,3)]),(10,[(0,1,2),(1,71,3)]),(1,[(1,71,3),(2,3,4),(1,114,0)]),(2,[(1,71,3),(2,3,4),(1,114,0)]),(4,[(0,1,2),(1,71,3),(1,114,0)]),(12,[(2,3,4),(1,114,0)]),(0,[(0,4,5),(1,4,5),(0,1,47),(3,53,47)]),(12,[(2,3,5),(1,281,5),(3,2,15)]),(3,[(0,2,1),(3,2,15)]),(4,[(1,3,5)]),(0,[(2,1,5),(3,1,5),(0,3,4),(1,3,4)]),(6,[(2,1,5),(3,1,5)]),(0,[(0,1,2),(1,1,2),(0,4,5),(3,53,3)]),(13,[(0,4,5),(3,53,3)]),(13,[(2,3,4),(1,3,5)]),(13,[(0,3,5),(1,0,22)]),(9,[(0,1,2),(1,1,2)]),(0,[(0,1,2),(2,3,4),(1,114,71)]),(1,[(2,3,4),(1,114,71)]),(12,[(2,3,4)]),(2,[(2,3,4),(1,114,71)]),(11,[(2,3,4)]),(0,[(0,1,2),(1,1,2),(0,3,5),(1,3,5)]),(13,[(0,3,5),(1,3,5)]),(1,[(1,3,5),(1,4,5)]),(7,[(1,1,2),(0,76,15)]),(0,[(0,1,2),(1,1,2),(0,3,5),(1,71,22)]),(1,[(0,3,5),(1,71,22)]),(13,[(0,3,5),(1,71,22)]),(0,[(0,1,2),(1,1,2),(0,3,5),(1,22,4)]),(13,[(0,3,5),(1,22,4)]),(4,[(2,1,2)]),(0,[(0,1,2),(1,71,4),(2,4,3),(3,135,321)]),(0,[(0,1,2),(1,1,2),(1,3,4),(1,30,5)]),(13,[(1,3,4),(1,30,5)]),(1,[(1,3,4),(1,30,5)]),(13,[(1,3,5),(1,4,15)]),(0,[(2,1,2),(0,4,5),(1,4,5),(3,53,47)]),(5,[(2,4,3),(3,135,47)]),(11,[(2,4,3),(1,4,5),(3,135,47)]),(12,[(2,4,3),(1,4,5),(3,135,47)]),(0,[(0,3,5),(1,3,5)]),(0,[(0,1,2),(0,3,5),(1,3,5),(3,71,15)]),(4,[(0,3,5),(1,3,5)]),(4,[(2,1,5),(3,1,5),(1,114,0)]),(7,[(1,1,2),(0,76,132)]),(0,[(3,1,5),(0,3,4),(1,28,5),(3,188,119)]),(3,[(3,1,5),(3,188,119)]),(4,[(3,1,5),(3,188,119)]),(0,[(0,3,5),(1,3,5),(1,1,15),(3,4,183)]),(0,[(1,1,2),(0,4,5),(1,4,5),(3,53,47)]),(0,[(0,1,2),(0,4,5),(1,4,5),(3,53,47)]),(5,[(0,1,2)]),(0,[(0,2,4),(1,2,4),(3,6,7),(0,8,1)]),(7,[(0,8,1)]),(0,[(0,1,2),(2,3,5),(1,281,5),(3,71,15)]),(0,[(0,1,2),(1,71,3),(1,3,5),(3,4,15)]),(3,[(1,4,15)]),(7,[(0,1,2),(3,71,132)]),(12,[(1,3,4),(1,30,5),(3,2,132)]),(12,[(3,4,5),(1,171,3),(3,2,172)]),(0,[(1,1,2),(0,3,4),(1,28,5),(1,3,4)]),(0,[(0,1,2),(1,1,2),(2,4,3),(3,135,76)]),(11,[(2,4,3),(3,135,76)]),(1,[(2,4,3)]),(4,[(1,1,2)]),(2,[(1,3,5),(3,295,15)]),(0,[(2,1,4),(1,162,3),(1,2,5),(0,334,24)]),(7,[(1,2,5),(0,334,24)]),(0,[(1,1,2),(0,3,5),(1,3,5),(0,76,15)]),(3,[(1,1,2),(0,76,15)]),(0,[(0,3,5),(1,3,5),(0,1,15),(1,1,15)]),(3,[(0,1,15),(1,1,15)]),(7,[(0,1,15),(1,1,15)]),(10,[(0,1,5),(1,31,3)]),(4,[(0,1,5),(1,31,3),(1,114,0)]),(6,[(0,1,5),(1,31,3)]),(0,[(0,1,2),(1,3,4),(1,30,5),(3,71,132)]),(0,[(0,1,2),(1,71,3),(1,4,5),(0,213,47)]),(12,[(1,4,5),(0,213,47)]),(11,[(1,4,5),(0,213,47)]),(2,[(3,4,5),(1,171,3)]),(0,[(0,3,5),(1,3,5),(1,2,15),(0,1,17)]),(3,[(1,2,15),(0,1,17)]),(7,[(1,2,15),(0,1,17)]),(7,[(2,2,1),(3,219,15)]),(0,[(1,4,5),(3,1,47),(1,3,47),(3,156,132)]),(1,[(1,4,5),(1,3,47)]),(7,[(3,1,47),(3,156,132)]),(1,[(0,2,5),(1,23,3)]),(0,[(0,2,5),(1,23,3),(2,3,4)]),(4,[(0,2,5),(1,23,3)]),(0,[(0,2,4),(1,2,4),(3,6,7),(0,8,5)]),(7,[(0,8,5)]),(7,[(2,1,2),(0,2,15)]),(5,[(1,4,3)]),(5,[(2,1,2)]),(3,[(2,1,2)]),(12,[(1,2,4),(0,38,7)]),(11,[(1,1,3),(0,38,7)]),(3,[(1,2,4),(0,38,7)]),(4,[(1,1,3),(0,38,7)]),(0,[(2,2,1),(0,3,5),(1,3,5),(3,219,15)]),(3,[(2,2,1),(3,219,15)]),(3,[(2,1,2),(0,2,15)]),(0,[(0,1,2),(1,1,2),(0,3,4),(1,3,4)]),(6,[(0,1,2),(1,1,2)]),(2,[(1,3,5),(1,1,15),(3,4,183)]),(0,[(1,3,5),(1,1,15),(3,2,15),(3,4,183)]),(0,[(0,2,4),(1,2,4),(3,6,7),(2,8,5)]),(4,[(0,1,2),(1,114,71)]),(5,[(0,2,3),(1,0,63)]),(0,[(0,2,3),(0,1,5),(1,1,5)]),(2,[(1,0,63),(0,1,5),(1,1,5)]),(1,[(1,4,3),(1,4,5),(1,3,5)]),(5,[(1,1,2)]),(3,[(1,1,2)]),(2,[(2,3,5),(1,281,5)]),(0,[(3,4,5),(1,171,3)]),(0,[(3,4,5),(1,171,3),(3,2,172)]),(7,[(3,2,172)]),(0,[(2,3,5),(1,281,5)]),(0,[(2,3,5),(1,281,5),(3,2,15)]),(3,[(3,2,15)]),(7,[(3,2,15)]),(0,[(2,3,5),(1,281,5),(0,1,15)]),(3,[(0,1,15)]),(5,[(0,1,15)]),(2,[(1,3,5),(3,4,15)]),(0,[(1,3,5),(3,2,15)]),(0,[(1,3,5),(3,2,15),(3,4,15)]),(0,[(1,3,5),(1,4,15)]),(0,[(1,3,5),(3,2,15),(1,4,15)]),(2,[(1,3,5),(1,4,15)]),(12,[(1,3,5),(1,4,15)]),(5,[(1,4,15)]),(12,[(1,3,5)]),(0,[(1,3,5),(3,2,15),(3,1,15)]),(5,[(3,1,15)]),(3,[(3,1,15)]),(4,[(1,3,5),(3,1,15)]),(5,[(3,2,15)]),(4,[(1,3,5),(3,2,15)]),(0,[(1,4,5)]),(0,[(1,4,5),(3,2,47),(1,155,3)]),(12,[(1,4,5)]),(11,[(1,4,5),(3,1,47)]),(0,[(1,4,5),(2,1,47),(3,1,47)]),(0,[(1,3,5),(1,2,15),(0,1,17)]),(0,[(1,3,5),(1,1,15)]),(2,[(1,3,5),(1,1,15)]),(5,[(1,1,15)]),(3,[(1,1,15)]),(0,[(3,4,5),(1,171,3),(0,1,172)]),(7,[(0,1,172)]),(0,[(1,3,5),(0,1,15)]),(0,[(1,3,5),(0,1,15),(3,4,15)]),(0,[(1,3,5),(0,1,15),(1,4,15)]),(11,[(1,3,5),(1,4,15)]),(0,[(1,3,5),(0,1,15),(1,1,15)]),(0,[(1,4,5),(0,1,47),(1,48,3)]),(0,[(0,4,5),(1,4,5)]),(0,[(0,4,5),(1,4,5),(2,1,47)]),(2,[(0,4,5),(1,4,5)]),(0,[(0,3,5),(1,3,5),(0,1,15)]),(0,[(2,3,4),(1,3,5)]),(0,[(2,3,4),(1,3,5),(0,1,15)]),(2,[(2,3,4),(1,3,5)]),(0,[(2,4,3),(1,4,5),(3,135,47)]),(3,[(1,4,5),(3,135,47)]),(0,[(1,4,3),(1,30,5),(3,4,132)]),(3,[(1,30,5),(3,4,132)]),(0,[(0,2,4),(1,1,5),(3,6,36)]),(1,[(0,2,4)]),(11,[(1,1,5)]),(12,[(0,2,4),(3,6,36)]),(0,[(3,2,5),(2,3,4),(1,114,187)]),(5,[(2,3,4)]),(0,[(2,1,2),(1,232,3),(1,346,4)]),(2,[(1,346,4)]),(3,[(2,1,2),(1,346,4)]),(1,[(1,232,3),(1,346,4)]),(11,[(1,232,3),(1,346,4)]),(12,[(1,346,4)]),(0,[(0,1,3),(1,37,5)]),(0,[(0,1,3),(1,37,5),(3,2,348)]),(2,[(0,1,3),(1,37,5)]),(1,[(1,37,5)]),(3,[(3,2,348)]),(7,[(3,2,348)]),(11,[(0,1,3),(1,37,5)]),(12,[(3,2,348)]),(0,[(2,1,2),(1,232,3),(2,346,4)]),(12,[(2,346,4)]),(2,[(2,346,4)]),(0,[(0,1,2),(0,4,5),(3,53,3)]),(2,[(0,4,5),(3,53,3)]),(1,[(0,4,5),(3,53,3)]),(11,[(2,1,5)]),(10,[(2,1,5)]),(3,[(2,1,5)]),(4,[(0,2,3),(1,0,63)]),(0,[(0,1,3),(1,2,5)]),(10,[(1,2,5)]),(2,[(0,1,3),(1,0,37)]),(1,[(1,0,37),(1,2,5)]),(3,[(1,2,5)]),(7,[(1,2,5)]),(5,[(0,1,3),(1,0,37)]),(12,[(1,2,5)]),(1,[(1,0,37)]),(11,[(0,1,3),(1,0,37)]),(2,[(1,0,63)]),(10,[(0,1,5)]),(3,[(1,4,5)]),(0,[(2,1,2),(1,3,5),(3,4,15)]),(0,[(0,2,3),(1,2,3)]),(0,[(0,2,3),(1,2,3),(2,1,5)]),(2,[(2,1,5)]),(4,[(0,2,3),(1,2,3)]),(0,[(0,1,5),(1,1,5)]),(0,[(3,2,3),(0,1,5),(1,1,5)]),(2,[(0,1,5),(1,1,5)]),(5,[(3,2,3)]),(1,[(3,2,3)]),(11,[(1,1,3),(2,1,5)]),(12,[(2,2,4)]),(3,[(2,2,4)]),(1,[(2,2,4)]),(0,[(1,1,3),(2,1,5),(2,2,4)]),(0,[(1,2,3),(0,1,5),(1,1,5)]),(5,[(1,2,3)]),(1,[(1,2,3)]),(11,[(0,1,5),(1,1,5)]),(0,[(1,4,5),(1,3,5),(3,4,15)]),(3,[(1,4,5),(3,4,15)]),(0,[(1,3,5)]),(0,[(2,2,1),(1,3,5),(3,219,15)]),(5,[(2,2,1),(3,219,15)]),(3,[(1,2,4)]),(12,[(1,2,4)]),(2,[(1,1,3),(2,1,5)]),(0,[(1,1,3),(2,1,5),(1,2,4)]),(12,[(0,2,3)]),(1,[(0,2,3)]),(0,[(2,1,5),(3,1,5)]),(12,[(2,38,4)]),(0,[(1,1,3),(2,1,5),(2,38,4)]),(0,[(0,2,3),(0,1,5),(1,63,31)]),(11,[(0,1,5)]),(5,[(0,2,3)]),(0,[(2,1,2),(0,3,5),(1,3,5)]),(0,[(0,3,5),(1,22,4)]),(0,[(2,1,2),(0,3,5),(1,22,4)]),(2,[(0,3,5),(1,22,4)]),(11,[(0,3,5),(1,22,4)]),(0,[(1,1,2),(2,76,4),(2,351,3)]),(1,[(2,351,3)]),(2,[(2,351,3)]),(0,[(0,1,2),(1,1,2),(1,3,4)]),(11,[(1,3,4)]),(1,[(1,3,4)]),(0,[(2,1,2),(1,232,3),(2,346,5)]),(12,[(2,346,5)]),(2,[(2,346,5)]),(3,[(2,1,2),(2,346,5)]),(7,[(2,1,2),(2,346,5)]),(0,[(1,2,3),(3,1,5),(3,188,64)]),(2,[(3,1,5)]),(11,[(3,1,5),(3,188,64)]),(7,[(3,1,5),(3,188,64)]),(0,[(2,1,2),(2,3,4),(1,114,232)]),(11,[(2,3,4),(1,114,232)]),(1,[(2,3,4),(1,114,232)]),(2,[(2,3,4)]),(0,[(0,3,4),(1,3,4)]),(0,[(2,1,2),(0,3,4),(1,3,4)]),(6,[(2,1,2)]),(0,[(0,3,4),(1,28,5)]),(0,[(2,1,2),(0,3,4),(1,28,5)]),(0,[(1,3,4),(1,30,5)]),(0,[(1,1,2),(1,3,4),(1,30,5)]),(5,[(1,3,4)]),(0,[(2,1,2),(1,232,5),(3,4,356)]),(12,[(3,4,356)]),(2,[(3,4,356)]),(7,[(2,1,2),(1,232,5)]),(12,[(1,3,5),(0,2,15)]),(7,[(0,2,15)]),(2,[(2,1,4)]),(10,[(3,2,5)]),(3,[(3,2,5)]),(0,[(0,1,2),(1,71,3),(1,213,4)]),(1,[(1,71,3),(1,213,4)]),(2,[(1,71,3),(1,213,4)]),(3,[(0,1,2),(1,213,4)]),(12,[(1,213,4)]),(11,[(1,213,4)]),(0,[(1,1,2),(3,4,5),(1,171,3)]),(0,[(1,4,3),(1,4,5)]),(0,[(0,1,2),(1,4,3),(1,4,5)]),(2,[(1,4,3),(1,4,5)]),(12,[(1,4,3),(1,4,5)]),(0,[(2,1,2),(1,3,5),(0,2,15)]),(5,[(2,1,2),(0,2,15)]),(8,[(1,3,5)]),(0,[(1,1,2),(2,76,5),(1,359,3)]),(1,[(1,359,3)]),(2,[(1,359,3)]),(3,[(1,1,2),(2,76,5)]),(7,[(1,1,2),(2,76,5)]),(7,[(0,38,47)]),(5,[(1,1,3),(0,38,47)]),(0,[(2,3,4),(1,114,5)]),(0,[(1,1,2),(2,3,4),(1,114,5)]),(2,[(2,3,4),(1,114,5)]),(4,[(1,114,5)]),(0,[(0,1,2),(0,3,4),(1,28,5)]),(0,[(2,1,4),(1,162,3),(1,2,5)]),(2,[(2,1,4),(1,162,3)]),(0,[(2,1,2),(3,4,5),(1,171,232)]),(11,[(3,4,5),(1,171,232)]),(1,[(3,4,5),(1,171,232)]),(7,[(2,1,2),(1,171,232)]),(0,[(0,1,2),(0,3,5),(1,3,5)]),(0,[(1,1,2),(0,4,5),(2,76,53)]),(1,[(0,4,5)]),(2,[(0,4,5)]),(0,[(2,1,2),(2,3,4),(1,3,5)]),(0,[(2,1,2),(1,232,3),(1,346,5)]),(2,[(1,346,5)]),(3,[(2,1,2),(1,346,5)]),(1,[(1,232,3),(1,346,5)]),(12,[(1,346,5)]),(7,[(2,1,2),(1,346,5)]),(5,[(2,1,2),(1,232,3)]),(0,[(1,2,4)]),(0,[(1,1,3),(1,2,4),(2,38,5)]),(2,[(1,1,3),(2,38,5)]),(0,[(0,1,5),(1,31,3)]),(0,[(0,1,2),(2,3,4),(1,3,5)]),(0,[(1,1,2),(2,76,4),(2,351,5)]),(1,[(2,351,5)]),(2,[(2,351,5)]),(7,[(1,1,2),(2,351,5)]),(0,[(0,1,2),(1,3,4),(1,30,5)]),(0,[(0,1,3),(2,2,5),(1,365,37)]),(11,[(0,1,3)]),(12,[(2,2,5)]),(1,[(2,2,5),(1,365,37)]),(7,[(2,2,5)]),(2,[(0,1,3),(1,365,37)]),(0,[(2,1,3),(1,205,5),(3,4,367)]),(7,[(1,205,5)]),(1,[(1,205,5),(3,4,367)]),(12,[(3,4,367)]),(0,[(1,1,2),(1,4,3),(1,4,5)]),(0,[(2,1,2),(0,4,5),(3,53,3)]),(11,[(0,4,5),(3,53,3)]),(0,[(1,1,2),(1,3,5),(0,76,15)]),(5,[(1,1,2),(0,76,15)]),(0,[(0,1,2),(1,1,2),(3,4,5)]),(11,[(3,4,5)]),(1,[(3,4,5)]),(13,[(3,4,5)]),(2,[(2,3,4),(1,114,0)]),(0,[(0,1,3),(1,1,3),(0,2,5)]),(1,[(0,2,5)]),(11,[(0,1,3),(1,1,3)]),(0,[(0,1,2),(1,1,2),(2,3,4)]),(1,[(2,3,4)]),(0,[(0,1,2),(1,71,3)]),(0,[(0,1,2),(1,71,3),(2,213,4)]),(11,[(2,213,4)]),(0,[(1,1,5),(2,4,3),(3,135,36)]),(5,[(2,4,3),(3,135,36)]),(0,[(1,1,2),(0,3,5),(1,3,5)]),(0,[(2,1,2),(1,3,4),(1,30,5)]),(0,[(2,1,2),(1,4,3),(1,4,5)]),(0,[(2,2,3),(1,1,5),(3,310,36)]),(1,[(2,2,3)]),(5,[(2,2,3),(3,310,36)]),(26,[]),(0,[(2,1,2),(2,3,5),(1,281,5)]),(0,[(1,1,3),(0,2,5),(3,23,38)]),(11,[(1,1,3)]),(12,[(0,2,5),(3,23,38)]),(7,[(0,2,5),(3,23,38)]),(5,[(1,1,3)]),(0,[(0,1,2),(2,3,4),(1,114,5)]),(0,[(2,1,4),(1,162,3),(1,334,5)]),(3,[(2,1,4),(1,334,5)]),(7,[(1,334,5)]),(5,[(2,1,4),(1,162,3)]),(0,[(0,1,2),(1,71,4),(1,4,5)]),(1,[(1,71,4),(1,4,5)]),(2,[(1,71,4),(1,4,5)]),(0,[(1,1,5),(0,4,3),(3,4,36)]),(1,[(0,4,3)]),(5,[(0,4,3),(3,4,36)]),(0,[(1,1,5),(1,3,4),(3,30,36)]),(0,[(0,1,2),(1,1,2),(2,3,5)]),(11,[(2,3,5)]),(1,[(2,3,5)]),(13,[(2,3,5)]),(0,[(0,2,1),(1,3,5),(3,2,15)]),(5,[(0,2,1),(3,2,15)]),(0,[(0,1,2),(1,71,3),(2,213,5)]),(12,[(2,213,5)]),(11,[(2,213,5)]),(3,[(0,1,2),(2,213,5)]),(7,[(0,1,2),(2,213,5)]),(0,[(1,1,2),(2,76,4),(1,351,5)]),(1,[(1,351,5)]),(2,[(1,351,5)]),(4,[(1,1,2),(1,351,5)]),(7,[(1,1,2),(1,351,5)]),(11,[(2,1,4)]),(0,[(0,1,2),(1,71,3),(1,213,5)]),(1,[(1,71,3),(1,213,5)]),(2,[(1,71,3),(1,213,5)]),(7,[(0,1,2),(1,213,5)]),(12,[(1,213,5)]),(11,[(1,213,5)]),(0,[(0,1,2),(0,3,4),(1,3,4)]),(6,[(0,1,2)]),(0,[(0,1,2),(1,71,3),(2,3,5)]),(1,[(1,71,3),(2,3,5)]),(2,[(1,71,3),(2,3,5)]),(0,[(2,1,4),(3,1,4),(1,2,5)]),(11,[(2,1,4),(3,1,4)]),(0,[(2,3,5),(3,3,5)]),(0,[(0,1,2),(2,3,5),(3,3,5)]),(2,[(2,3,5),(3,3,5)]),(1,[(2,3,5),(3,3,5)]),(4,[(2,3,5),(3,3,5)]),(0,[(0,3,5),(1,3,5),(3,2,15)]),(0,[(0,1,2),(2,3,5),(1,281,5)]),(0,[(2,1,2),(2,3,5),(1,281,232)]),(11,[(2,3,5),(1,281,232)]),(1,[(2,3,5),(1,281,232)]),(2,[(2,3,5)]),(0,[(0,1,2),(1,71,3),(1,4,5)]),(0,[(0,1,2),(0,3,5),(1,22,4)]),(1,[(0,3,5),(1,22,4)]),(0,[(1,1,4)]),(0,[(1,1,4),(3,2,5),(1,187,3)]),(1,[(3,2,5),(1,187,3)]),(5,[(1,1,4)]),(2,[(1,1,4)]),(11,[(1,187,3)]),(0,[(3,2,5),(0,3,4),(1,28,5)]),(4,[(3,2,5)]),(0,[(0,1,2),(1,71,5),(3,4,149)]),(12,[(3,4,149)]),(11,[(3,4,149)]),(7,[(0,1,2),(1,71,5)]),(0,[(1,1,2),(0,3,4),(1,3,4)]),(6,[(1,1,2)]),(0,[(0,1,2),(1,3,5),(3,71,15)]),(2,[(1,3,5),(3,71,15)]),(1,[(1,3,5),(3,71,15)]),(5,[(0,1,2),(3,71,15)]),(0,[(1,1,2),(2,3,5),(3,3,5)]),(0,[(2,1,2),(0,3,5),(1,232,22)]),(2,[(0,3,5)]),(13,[(0,3,5)]),(11,[(0,3,5),(1,232,22)]),(12,[(3,2,5)]),(1,[(3,2,5)]),(0,[(2,1,4),(3,1,4),(3,2,5)]),(0,[(0,1,3),(1,37,5),(1,2,5)]),(0,[(2,1,4),(3,2,5),(1,162,187)]),(4,[(3,2,5),(1,162,187)]),(7,[(3,2,5),(1,162,187)]),(5,[(2,1,4)]),(0,[(2,1,2),(1,232,3),(1,4,5)]),(0,[(1,1,2),(2,3,5),(1,281,5)]),(4,[(2,3,5),(1,281,5)]),(0,[(0,1,2),(1,3,5),(3,4,15)]),(0,[(0,1,2),(1,1,2),(0,3,4)]),(1,[(0,3,4)]),(0,[(2,1,2),(0,3,4),(1,232,28)]),(2,[(0,3,4)]),(1,[(0,3,4),(1,232,28)]),(11,[(0,3,4),(1,232,28)]),(0,[(1,3,5),(1,1,15),(3,4,183)]),(17,[]),(0,[(1,1,3),(3,3,5),(2,38,5)]),(1,[(3,3,5)]),(3,[(2,38,5)]),(7,[(2,38,5)]),(0,[(0,1,2),(2,3,5),(1,281,71)]),(2,[(2,3,5),(1,281,71)]),(1,[(2,3,5),(1,281,71)]),(5,[(0,1,2),(1,281,71)]),(0,[(1,1,2),(2,3,4),(1,3,5)]),(0,[(2,1,5),(1,234,3),(2,3,5)]),(0,[(1,2,4),(0,1,5),(1,31,4)]),(1,[(1,2,4),(1,31,4)]),(5,[(1,2,4)]),(0,[(1,1,2),(2,76,4),(1,3,5)]),(12,[(2,213,4)]),(12,[(1,2,3)]),(0,[(1,2,3),(2,1,5),(3,1,5)]),(0,[(0,2,5),(1,23,3)]),(0,[(2,1,4),(0,2,5),(1,23,3)]),(2,[(1,23,3)]),(12,[(0,2,5),(1,23,3)]),(0,[(0,1,2),(3,4,5),(1,171,71)]),(2,[(3,4,5),(1,171,71)]),(1,[(3,4,5),(1,171,71)]),(7,[(0,1,2),(1,171,71)]),(0,[(0,1,2),(3,4,5),(1,171,3)]),(0,[(1,1,2),(0,4,5),(3,53,3)]),(0,[(2,2,4),(3,2,4)]),(0,[(2,2,4),(3,2,4),(2,1,5)]),(5,[(2,2,4),(3,2,4)]),(3,[(2,2,4),(3,2,4)]),(0,[(3,1,4),(1,2,5),(3,207,24)]),(2,[(3,1,4)]),(11,[(3,1,4),(3,207,24)]),(0,[(2,1,2),(2,3,5),(3,3,5)]),(11,[(2,3,5),(3,3,5)]),(0,[(1,1,2),(2,76,4),(1,351,3)]),(2,[(1,351,3)]),(0,[(0,1,5),(1,1,5),(0,3,4)]),(4,[(0,1,5),(1,1,5)]),(0,[(0,1,5),(1,1,5),(1,3,4)]),(0,[(0,1,2),(1,71,4),(1,4,3)]),(1,[(1,71,4),(1,4,3)]),(2,[(1,71,4),(1,4,3)]),(3,[(0,1,2),(1,71,4)]),(12,[(1,4,3)]),(11,[(1,4,3)]),(12,[(3,2,3)]),(0,[(3,2,3),(2,1,5),(3,1,5)]),(0,[(1,1,2),(0,3,4),(2,76,28)]),(0,[(1,1,2),(0,3,4),(1,28,5)]),(1,[(0,3,5),(1,0,22)]),(2,[(0,3,5),(1,0,22)]),(9,[]),(9,[(1,1,2)]),(4,[(0,3,5),(1,0,22)]),(11,[(1,1,4)]),(0,[(2,3,4),(1,3,5),(3,2,15)]),(0,[(0,1,2),(1,71,3),(2,3,4)]),(1,[(1,71,3),(2,3,4)]),(2,[(1,71,3),(2,3,4)]),(0,[(1,1,5),(0,3,4),(1,28,5)]),(3,[(1,1,5)]),(4,[(1,1,5)]),(0,[(0,1,3),(1,37,5),(3,2,5)]),(1,[(1,37,5),(3,2,5)]),(0,[(0,1,3),(3,2,5),(1,187,37)]),(2,[(0,1,3)]),(0,[(2,1,2),(2,3,4),(1,114,5)]),(7,[(0,38,7)]),(0,[(2,1,3),(2,2,4),(1,205,295)]),(7,[(1,205,295)]),(1,[(2,2,4),(1,205,295)]),(2,[(2,1,3),(1,205,295)]),(0,[(1,1,2),(2,4,3),(3,135,76)]),(2,[(2,4,3)]),(0,[(1,1,4),(2,2,3),(3,310,43)]),(3,[(1,1,4),(3,310,43)]),(2,[(1,1,4),(3,310,43)]),(4,[(2,2,3),(3,310,43)]),(7,[(3,310,43)]),(0,[(2,1,4),(2,2,5),(1,365,162)]),(4,[(2,2,5),(1,365,162)]),(7,[(2,2,5),(1,365,162)]),(0,[(2,2,4),(1,295,5)]),(0,[(1,1,3),(2,2,4),(1,295,5)]),(7,[(1,295,5)]),(1,[(2,2,4),(1,295,5)]),(2,[(1,295,5)]),(0,[(2,1,4),(1,1,5)]),(0,[(1,2,3),(2,1,4),(1,1,5)]),(0,[(0,1,3),(1,1,3),(1,2,5)]),(0,[(1,3,4),(1,3,5)]),(0,[(1,3,4),(1,3,5),(3,2,15)]),(2,[(1,3,4),(1,3,5)]),(0,[(0,1,2),(0,3,5),(1,71,22)]),(2,[(0,3,5),(1,71,22)]),(11,[(1,1,3),(2,38,5)]),(0,[(1,1,3),(2,2,4),(2,38,5)]),(0,[(1,2,4),(0,1,5),(1,31,3)]),(1,[(1,31,3)]),(0,[(2,2,4),(2,1,5),(3,1,5)]),(4,[(2,1,5),(3,1,5)]),(0,[(0,1,3),(1,1,3)]),(0,[(0,1,3),(1,1,3),(3,2,5)]),(0,[(1,2,5)]),(0,[(1,1,3),(1,2,5),(2,38,4)]),(2,[(1,1,3),(2,38,4)]),(0,[(1,1,3),(1,2,5),(0,38,24)]),(3,[(1,2,5),(0,38,24)]),(0,[(1,2,3)]),(0,[(1,2,3),(1,1,5),(3,4,36)]),(2,[(1,1,5),(3,4,36)]),(0,[(3,2,5),(0,3,4),(1,3,4)]),(6,[(3,2,5)]),(12,[(1,2,3),(2,64,4)]),(0,[(1,2,4),(2,1,5),(1,234,3)]),(2,[(2,1,5),(1,234,3)]),(0,[(1,1,3),(1,3,5),(2,38,5)]),(0,[(1,1,3),(2,38,4),(1,300,5)]),(1,[(1,300,5)]),(3,[(2,38,4),(1,300,5)]),(0,[(2,1,5),(3,1,5),(0,3,4)]),(0,[(1,1,3),(2,38,4),(2,300,5)]),(1,[(2,300,5)]),(7,[(2,300,5)]),(0,[(1,1,3),(2,38,4),(3,4,5)]),(0,[(0,1,2),(1,1,2),(0,3,5)]),(11,[(0,3,5)]),(1,[(0,3,5)]),(0,[(1,1,4),(2,43,5),(1,394,3)]),(1,[(1,394,3)]),(3,[(1,1,4),(2,43,5)]),(7,[(2,43,5)]),(0,[(1,1,4),(3,3,5),(3,317,43)]),(3,[(1,1,4),(3,317,43)]),(7,[(3,317,43)]),(11,[(0,3,5),(1,0,22)]),(9,[(2,1,2)]),(0,[(2,2,4),(1,295,3),(1,2,5)]),(3,[(2,2,4),(1,2,5)]),(5,[(2,2,4),(1,295,3)]),(0,[(2,2,4),(1,295,3)]),(0,[(2,2,4),(1,295,3),(0,1,397)]),(12,[(2,2,4),(1,295,3)]),(2,[(1,295,3)]),(1,[(2,2,4),(1,295,3)]),(7,[(0,1,397)]),(0,[(2,1,4),(1,162,3)]),(0,[(2,1,4),(1,162,3),(3,2,334)]),(1,[(1,162,3)]),(3,[(2,1,4)]),(11,[(2,1,4),(1,162,3)]),(7,[(3,2,334)]),(10,[(1,1,2)]),(4,[(1,114,0)]),(0,[(1,3,4),(1,3,5),(0,1,15)]),(0,[(2,1,4),(1,162,3),(2,334,5)]),(7,[(2,334,5)]),(12,[(2,334,5)]),(0,[(2,2,3),(1,310,5)]),(0,[(2,2,3),(1,310,5),(2,1,4)]),(4,[(2,2,3),(1,310,5)]),(2,[(1,310,5)]),(3,[(1,310,5)]),(7,[(1,310,5)]),(1,[(2,2,3),(1,310,5)]),(5,[(2,2,3)]),(0,[(2,1,4),(1,162,5),(1,4,5)]),(7,[(1,162,5)]),(0,[(2,1,4),(1,162,5),(3,4,5)]),(4,[(1,162,5)]),(12,[(0,2,5)]),(0,[(2,1,4),(3,1,4)]),(0,[(2,1,4),(3,1,4),(0,2,5)]),(0,[(2,2,3),(1,2,5)]),(0,[(2,2,3),(1,2,5),(2,1,4)]),(4,[(2,2,3),(1,2,5)]),(1,[(2,2,3),(1,2,5)]),(0,[(2,2,4),(0,1,5),(1,295,31)]),(7,[(0,1,5),(1,295,31)]),(5,[(2,2,4)]),(12,[(1,2,5),(3,3,24)]),(0,[(2,1,4),(1,2,5),(3,3,24)]),(1,[(1,2,5),(3,3,24)]),(0,[(2,2,5),(1,365,3)]),(0,[(2,1,4),(2,2,5),(1,365,3)]),(4,[(2,2,5),(1,365,3)]),(2,[(1,365,3)]),(3,[(2,2,5)]),(12,[(2,2,5),(1,365,3)]),(0,[(0,2,5),(1,2,5)]),(0,[(0,1,3),(0,2,5),(1,2,5)]),(0,[(1,1,5),(1,4,5),(3,4,36)]),(0,[(3,2,5),(1,187,3)]),(0,[(2,1,4),(3,2,5),(1,187,3)]),(4,[(3,2,5),(1,187,3)]),(12,[(3,2,5),(1,187,3)]),(0,[(0,1,5),(1,31,3),(2,3,4)]),(0,[(0,1,2),(1,71,5),(3,4,5)]),(1,[(1,71,5),(3,4,5)]),(2,[(1,71,5),(3,4,5)]),(0,[(2,2,3),(1,4,5),(3,310,47)]),(7,[(3,310,47)]),(0,[(2,1,4),(1,3,5),(3,4,15)]),(0,[(2,2,4),(1,295,3),(2,1,5)]),(0,[(1,1,3),(2,2,5),(3,365,38)]),(1,[(2,2,5)]),(3,[(2,2,5),(3,365,38)]),(7,[(2,2,5),(3,365,38)]),(0,[(2,1,5),(0,3,4),(1,3,4)]),(6,[(2,1,5)]),(0,[(2,1,3),(3,4,5),(1,205,171)]),(5,[(2,1,3)]),(3,[(3,4,5),(1,205,171)]),(7,[(1,205,171)]),(0,[(2,1,4),(0,2,5),(1,2,5)]),(0,[(0,3,4),(1,28,5),(0,1,119)]),(3,[(0,1,119)]),(4,[(0,1,119)]),(0,[(1,1,2),(1,3,5),(3,4,15)]),(0,[(3,2,3),(0,1,5),(1,294,31)]),(2,[(0,1,5)]),(12,[(1,3,4)]),(0,[(2,1,5),(3,1,5),(1,3,4)]),(0,[(3,2,3),(0,1,5),(1,31,3)]),(0,[(0,2,3),(1,63,5)]),(0,[(0,2,3),(1,63,5),(0,1,410)]),(12,[(0,2,3),(1,63,5)]),(2,[(1,63,5)]),(3,[(0,1,410)]),(7,[(0,1,410)]),(1,[(0,2,3),(1,63,5)]),(11,[(0,1,410)]),(0,[(3,2,3),(2,1,5),(1,234,294)]),(5,[(3,2,3),(1,234,294)]),(1,[(3,2,3),(1,234,294)]),(0,[(1,1,2),(3,3,5),(3,317,76)]),(2,[(3,3,5)]),(3,[(1,1,2),(3,317,76)]),(7,[(1,1,2),(3,317,76)]),(0,[(1,3,4),(1,3,5),(3,4,15)]),(10,[(0,1,2)]),(0,[(3,1,3),(3,2,5),(1,414,187)]),(2,[(3,1,3)]),(5,[(3,1,3)]),(11,[(0,1,202)]),(7,[(0,2,5),(0,1,202)]),(0,[(0,1,5),(1,31,3),(3,2,198)]),(4,[(0,1,5),(1,31,3)]),(12,[(3,2,198)]),(5,[(3,2,198)]),(10,[(2,1,2)]),(0,[(0,1,5),(1,31,4),(1,4,3)]),(3,[(0,1,5),(1,31,4)]),(0,[(0,1,2),(1,71,5),(1,3,5)]),(1,[(1,71,5),(1,3,5)]),(2,[(1,71,5),(1,3,5)]),(3,[(0,1,2),(1,71,5)]),(0,[(0,1,5),(1,31,3),(1,198,4)]),(12,[(1,198,4)]),(5,[(1,198,4)]),(3,[(0,1,5),(1,198,4)]),(12,[(2,198,4)]),(0,[(0,1,5),(1,1,5),(2,3,4)]),(0,[(2,1,2),(3,4,5),(1,171,3)]),(0,[(0,1,5),(2,3,4),(1,114,31)]),(0,[(0,1,5),(0,3,4),(1,3,4)]),(6,[(0,1,5)]),(0,[(1,1,5),(0,3,4),(3,28,36)]),(5,[(0,3,4),(3,28,36)]),(0,[(1,1,5),(0,3,4),(1,3,4)]),(6,[(1,1,5)]),(3,[(1,4,5),(3,310,47)]),(5,[(2,2,3),(3,310,47)]),(0,[(3,2,5),(1,187,4),(1,4,3)]),(2,[(1,4,3)]),(3,[(3,2,5),(1,187,4)]),(10,[(1,1,5)]),(0,[(2,1,5),(1,234,3),(1,382,4)]),(12,[(1,382,4)]),(3,[(2,1,5),(1,382,4)]),(4,[(1,1,5),(3,3,36)]),(5,[(3,3,36)]),(0,[(1,1,5),(3,4,36),(1,288,3)]),(5,[(3,4,36),(1,288,3)]),(0,[(1,3,5),(1,1,15),(3,2,183)]),(0,[(2,1,5),(1,234,4),(1,4,5)]),(0,[(1,1,2),(2,4,5),(3,423,76)]),(1,[(2,4,5)]),(2,[(2,4,5)]),(0,[(2,1,5),(1,234,3),(2,382,4)]),(12,[(2,382,4)]),(0,[(2,1,5),(3,1,5),(2,3,4)]),(0,[(2,1,5),(0,3,4),(1,234,28)]),(4,[(2,1,5)]),(0,[(1,1,2),(0,3,5),(1,22,4)]),(0,[(3,2,5),(1,187,3),(2,3,4)]),(0,[(2,1,5),(2,3,4),(1,234,114)]),(5,[(2,3,4),(1,234,114)]),(0,[(3,2,5),(1,187,3),(1,377,4)]),(2,[(1,377,4)]),(3,[(3,2,5),(1,377,4)]),(0,[(0,1,2),(1,1,2),(1,3,5)]),(13,[(1,3,5)]),(0,[(3,2,5),(1,187,3),(2,377,4)]),(5,[(2,377,4)]),(0,[(3,2,5),(0,3,4),(1,187,28)]),(0,[(0,3,4),(1,28,5),(3,2,119)]),(3,[(3,2,119)]),(4,[(3,2,119)]),(0,[(1,4,3),(1,4,5),(1,3,5)]),(9,[(0,1,2)]),(0,[(1,3,4),(1,30,5),(0,1,132)]),(0,[(1,3,4),(1,30,5),(3,2,132)]),(7,[(3,2,132)]),(0,[(1,3,5),(1,4,5)]),(0,[(0,4,5),(3,53,3)]),(0,[(3,2,5),(2,3,4)]),(0,[(1,3,4)]),(0,[(3,2,5),(1,3,4)]),(2,[(1,3,4)]),(6,[]),(0,[(2,1,5),(1,3,5)]),(0,[(2,1,5),(1,3,4)]),(0,[(1,1,5),(3,4,36)]),(0,[(2,1,5),(2,3,4)]),(0,[(1,1,5),(1,3,5)]),(2,[(1,1,5)]),(0,[(1,4,5),(2,1,47)]),(0,[(1,1,5),(1,3,4)]),(0,[(1,1,5),(0,3,4)]),(0,[(1,1,5),(1,2,5)]),(0,[(0,1,5)]),(0,[(0,1,5),(2,3,4)]),(0,[(0,3,4)]),(0,[(0,1,5),(0,3,4)]),(0,[(3,2,3),(3,1,5)]),(3,[(3,1,5)]),(7,[(3,1,5)]),(0,[(3,2,3),(2,1,5)]),(0,[(3,2,3),(1,294,5)]),(0,[(3,4,5)]),(0,[(2,1,4),(3,4,5)]),(12,[(3,4,5)]),(2,[(3,4,5)]),(0,[(2,1,4),(1,4,5)]),(0,[(2,1,4),(3,2,5)]),(0,[(0,3,5)]),(0,[(2,1,2),(0,3,5)]),(0,[(0,1,2),(2,3,4)]),(0,[(2,1,2),(1,3,4)]),(0,[(0,4,5),(2,1,53)]),(0,[(3,2,3),(0,1,5)]),(0,[(1,1,2),(1,3,4)]),(0,[(2,1,2),(2,3,5)]),(12,[(2,3,5)]),(0,[(1,1,5)]),(0,[(3,2,3),(1,1,5)]),(0,[(1,1,2),(2,76,4)]),(0,[(0,1,2),(2,3,5)]),(0,[(2,1,2),(0,3,4)]),(0,[(2,1,4),(1,162,5)]),(0,[(1,1,2),(3,4,5)]),(0,[(2,1,2),(1,232,5)]),(0,[(1,1,2),(1,3,5)]),(0,[(0,1,2),(1,71,5)]),(1,[(1,71,5)]),(2,[(1,71,5)]),(0,[(1,1,2),(2,3,5)]),(0,[(1,1,2),(0,3,5)]),(4,[(0,3,5)]),(0,[(1,1,2),(2,3,4)]),(0,[(1,1,4),(3,4,5)]),(0,[(2,2,4)]),(0,[(2,1,4),(2,2,4)]),(0,[(0,1,2),(0,3,5)]),(0,[(0,3,5),(1,2,22)]),(0,[(2,1,2),(1,232,3)]),(0,[(1,2,4),(2,1,4)]),(0,[(2,1,4),(1,3,5)]),(0,[(1,1,2),(2,76,5)]),(0,[(0,1,2),(0,3,4)]),(0,[(3,2,5),(0,3,4)]),(0,[(0,1,2),(1,3,4)]),(0,[(0,1,2),(1,3,5)]),(0,[(0,1,3)]),(0,[(2,1,2),(2,3,4)]),(0,[(0,1,2),(3,4,5)]),(0,[(1,1,5),(2,3,4)]),(0,[(1,1,2),(0,3,4)]),(0,[(1,2,3),(2,1,5)]),(4,[(1,2,3)]),(0,[(1,1,5),(2,3,5)]),(0,[(1,3,5),(3,4,15)]),(0,[(0,2,3)]),(0,[(0,2,3),(2,1,5)]),(0,[(0,1,3),(3,2,5)]),(0,[(0,2,5)]),(0,[(0,1,3),(0,2,5)]),(0,[(1,1,3),(2,1,5)]),(12,[(3,3,5)]),(0,[(2,1,4),(3,3,5)]),(11,[(3,3,5)]),(0,[(2,1,2),(1,3,5)]),(0,[(1,1,3),(1,2,3)]),(0,[(2,1,5),(0,3,4)]),(0,[(2,1,5),(1,234,3)]),(0,[(2,1,2),(3,4,5)]),(1,[(1,71,3)]),(2,[(1,71,3)]),(0,[(1,1,3),(1,2,5)]),(4,[(1,1,3)]),(0,[(1,1,3)]),(0,[(1,1,3),(3,4,5)]),(0,[(1,2,3),(0,1,5)]),(0,[(1,1,3),(1,2,4)]),(0,[(1,2,3),(2,1,4)]),(0,[(1,1,3),(3,2,5)]),(12,[(2,2,3)]),(0,[(2,1,4),(2,2,3)]),(0,[(1,1,3),(1,3,5)]),(0,[(2,3,5)]),(0,[(2,1,5),(2,3,5)]),(0,[(0,1,5),(1,3,4)]),(0,[(1,1,3),(2,38,4)]),(0,[(1,2,5),(2,1,5)]),(0,[(1,1,3),(2,38,5)]),(0,[(1,1,3),(1,4,5)]),(0,[(2,2,5)]),(0,[(2,1,5),(2,2,5)]),(0,[(2,1,4),(0,2,5)]),(0,[(2,1,4),(1,2,5)]),(4,[(1,2,5)]),(0,[(2,2,4),(2,1,5)]),(0,[(2,3,4)]),(0,[(2,1,5)]),(0,[(2,1,4)]),(0,[(3,2,5)]),(0,[(3,2,3)])] : List PoolSpec)).map some)
def B_17_1 : BT (List (List Nat)) := BT.empty
lemma B_17_1_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 1 xs.toFinset) B_17_1 := .empty
def P_17_2 : BT (Option BoundPool) := buildPoolsSubBT 11 W_17 r_17 S_17 ps_17 []
def N_17_2 : List NodeSpec := [([14,0,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_2 : checkNodesBT W_17 g_17 F_17 P_17_2 A_17 B_17_1 2 N_17_2 = true := by decide +kernel
def B_17_2 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_2
set_option maxRecDepth 500000 in
lemma B_17_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 2 xs.toFinset) B_17_2 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_1_ok C_17_2
def P_17_3 : BT (Option BoundPool) := buildPoolsSubBT 11 W_17 r_17 S_17 ps_17 []
def N_17_3 : List NodeSpec := [([0,21,22,4],[],[]),([0,26,29,30],[],[]),([35,0,30,36],[],[]),([40,41,0,4],[],[1]),([45,46,0,3],[],[0]),([51,0,3,54],[],[]),([0,57,2,59],[],[]),([61,1,11,3],[],[]),([62,58,0,4],[],[1]),([0,69,70,4],[],[1]),([75,0,76,30],[],[]),([76,77,30,74],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_3 : checkNodesBT W_17 g_17 F_17 P_17_3 A_17 B_17_2 3 N_17_3 = true := by decide +kernel
def B_17_3 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_3
set_option maxRecDepth 500000 in
lemma B_17_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 3 xs.toFinset) B_17_3 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_2_ok C_17_3
def P_17_4 : BT (Option BoundPool) := buildPoolsSubBT 11 W_17 r_17 S_17 ps_17 [0,1,2,3,4,5,6,7,8]
def N_17_4 : List NodeSpec := [([0,21,3,4,5],[],[0]),([80,0,1,82,53],[],[]),([80,1,83,3,53],[],[]),([51,0,52,3,53],[],[0,1]),([84,0,85,3,53],[],[1]),([35,0,1,30,5],[],[0]),([87,88,0,30,24],[],[2]),([35,0,3,4,36],[],[0]),([0,57,2,89,4],[],[2]),([0,69,1,68,4],[],[0]),([91,0,92,3,90],[],[]),([93,0,76,72,5],[],[]),([76,3,77,4,74],[],[0]),([75,0,76,3,4],[],[0]),([1,2,77,30,74],[],[0]),([95,0,96,28,30],[0,1],[]),([0,26,3,29,4],[],[0]),([97,76,72,30,5],[],[]),([0,76,73,30,74],[],[0]),([25,0,1,29,30],[],[0]),([98,0,72,30,5],[],[]),([1,100,86,30,24],[],[]),([76,72,77,30,5],[],[0]),([25,102,1,28,30],[2],[]),([80,0,1,3,103],[],[2]),([62,0,57,2,4],[],[0]),([0,99,104,30,24],[],[2]),([60,0,1,11,3],[3,4],[0,3]),([25,44,46,0,3],[],[0]),([45,25,44,0,3],[],[0]),([40,25,39,0,4],[5,6],[0]),([105,8,94,0,3],[],[3]),([27,0,26,28,30],[0,7],[0]),([106,102,1,3,4],[],[]),([107,1,86,30,24],[],[]),([25,1,109,28,30],[8],[]),([75,0,1,2,30],[],[0]),([110,0,2,32,30],[],[]),([111,112,0,76,30],[],[0]),([100,3,104,4,24],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_4 : checkNodesBT W_17 g_17 F_17 P_17_4 A_17 B_17_3 4 N_17_4 = true := by decide +kernel
def B_17_4 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_4
set_option maxRecDepth 500000 in
lemma B_17_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 4 xs.toFinset) B_17_4 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_3_ok C_17_4
def P_17_5 : BT (Option BoundPool) := buildPoolsSubBT 11 W_17 r_17 S_17 ps_17 [1,2,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59]
def N_17_5 : List NodeSpec := [([80,0,1,82,4,5],[],[0]),([80,1,83,3,4,5],[],[0]),([51,0,52,3,4,5],[],[0,1]),([84,0,85,3,4,5],[],[0,1]),([80,0,81,1,3,53],[9,10],[0,2]),([51,50,0,2,3,53],[],[0]),([80,0,1,85,3,53],[],[0]),([87,88,0,2,30,5],[],[0,2]),([107,1,2,86,30,5],[],[0]),([0,99,2,104,30,5],[],[0,2]),([35,0,1,3,4,5],[],[0]),([113,0,2,32,30,36],[],[2]),([87,88,0,3,4,24],[],[0,2]),([0,1,86,104,30,24],[11],[0]),([107,1,3,86,4,24],[],[0]),([0,99,1,86,30,24],[11,12,13],[0,2]),([1,100,3,86,4,24],[],[0]),([25,0,115,1,3,4],[14,15],[]),([25,0,108,1,28,30],[16,17,18,19],[0,2]),([25,0,1,3,116,4],[],[]),([25,1,109,3,4,30],[],[0]),([1,117,3,34,4,5],[],[2]),([25,1,109,28,3,4],[20,21],[0]),([118,94,0,2,3,4],[22,23],[]),([114,95,0,96,3,4],[1,5,24,25],[]),([95,0,96,28,3,4],[26],[0]),([95,94,0,2,28,30],[27,28],[0,2]),([120,121,0,71,30,5],[],[]),([25,0,1,26,28,30],[29],[0]),([125,0,1,3,4,5],[],[]),([1,100,2,86,30,5],[],[0]),([25,0,1,3,127,4],[],[]),([87,0,1,86,30,24],[],[0]),([27,0,26,28,3,4],[21,26],[0]),([111,112,0,76,3,4],[],[0]),([128,0,71,92,3],[30,31],[]),([129,0,71,92,3,5],[],[]),([91,0,76,3,90,47],[32,33,34,35],[0]),([0,130,131,4,15],[36,37,38,39],[1]),([106,101,0,1,3,4],[21,40],[0]),([111,112,0,1,2,30],[],[0]),([0,57,2,4],[41,42],[0,2,3]),([1,2,72,77,30,5],[],[0]),([75,0,1,2,3,4],[],[0]),([129,0,71,133,3,5],[],[]),([134,0,1,2,30,5],[],[]),([25,102,1,3,4,30],[],[0]),([25,0,1,136,3,4],[],[]),([0,71,130,4,137,5],[],[]),([141,0,1,2,3,4],[],[]),([95,0,96,3,4,30],[43],[0]),([111,0,76,72,30,5],[],[0]),([0,1,2,73,30,74],[],[0]),([0,76,73,72,30,5],[44,45,46,47],[0]),([25,0,1,3,142,4],[],[]),([129,143,0,71,76,5],[48],[]),([110,0,2,3,32,4],[],[0]),([0,1,2,3,146,147],[],[]),([0,99,3,104,4,24],[],[0,2]),([148,25,0,1,3,4],[],[]),([0,76,72,30,5,74],[44,45,49,50],[0]),([114,25,1,109,3,4],[8,14,51],[]),([98,0,3,72,4,5],[],[0]),([128,0,71,92,3,47],[31],[]),([0,76,3,73,4,74],[],[0]),([150,0,76,3,72,5],[],[0]),([97,1,2,72,30,5],[],[0]),([151,128,0,71,3],[31,52],[]),([97,76,3,72,4,5],[],[0]),([152,153,0,131,4,15],[37],[]),([0,71,154,30,5,119],[],[]),([128,155,156,0,71,3],[31],[]),([151,128,0,71,3,47],[31],[]),([27,0,26,3,4,30],[43],[0]),([157,128,156,0,71,3],[31],[]),([25,0,1,3,159,4],[],[]),([112,0,76,72,30,5],[],[0]),([157,160,128,0,71,3],[31,53],[]),([157,160,0,71,3,47],[53],[]),([76,3,72,77,4,5],[],[0]),([25,44,0,3],[18,54],[0,1,2]),([25,102,1,28,3,4],[55],[0]),([163,25,0,1,3,4],[],[]),([25,0,1,3,164,4],[],[]),([1,2,3,77,4,74],[],[0]),([165,25,0,1,3,4],[],[]),([114,27,0,26,3,4],[5,7,25,56],[]),([91,0,1,2,3,47],[],[]),([169,0,1,2,3,4],[],[]),([158,25,102,1,3,4],[55],[]),([25,0,1,3,29,4],[],[0]),([84,80,0,1,3,53],[],[0]),([27,25,0,1,28,30],[57,58],[0]),([106,0,1,26,3,4],[21],[]),([93,0,1,2,72,5],[],[0]),([170,25,102,1,3,4],[14,55,59],[]),([114,25,102,1,3,4],[2,14,59],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_5 : checkNodesBT W_17 g_17 F_17 P_17_5 A_17 B_17_4 5 N_17_5 = true := by decide +kernel
def B_17_5 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_5
set_option maxRecDepth 500000 in
lemma B_17_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 5 xs.toFinset) B_17_5 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_4_ok C_17_5
def P_17_6 : BT (Option BoundPool) := buildPoolsSubBT 11 W_17 r_17 S_17 ps_17 [5,9,10,11,13,14,15,16,17,18,19,21,24,28,29,31,32,33,35,37,38,39,44,45,47,48,50,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250,251,252,253,254,255,256,257,258]
def N_17_6_0 : List NodeSpec := [([173,0,1,2,3,4,5],[],[]),([174,0,1,2,3,4,5],[],[]),([80,0,1,85,3,4,5],[],[0]),([157,160,0,1,2,3,47],[60,61,62],[0]),([157,0,1,175,3],[61,63,64,65],[3]),([80,0,81,1,3,4,5],[10,55,66,67],[0,2]),([157,160,128,0,1,2,3],[31,60,61,62,64],[0]),([84,80,0,1,3,4,5],[],[0]),([178,176,0,1,2],[17,62,68,69,70,71],[]),([179,180,128,0,1,2,3],[31,60,61,62,64,72],[]),([128,155,156,0,1,2,3],[31,60,61,64],[0]),([152,0,1,182,4],[17,73,74,75,76],[]),([184,176,0,1,2],[17,62,71,77],[]),([185,0,48,2,3],[78,79,80,81],[]),([80,0,1,3,53],[9,10],[0,2]),([186,0,1,2,3,4,5],[],[]),([174,0,1,2,4,30,5],[82],[]),([134,0,1,2,3,4,5],[],[0]),([187,121,0,1,2,30,119],[83,84],[]),([0,1,189,2,30,119],[83,85,86,87,88],[]),([0,1,2,191,5],[17,89,90,91],[]),([113,0,1,2,32,30,5],[],[0,2]),([87,88,0,2,3,4,5],[],[0,2]),([0,1,2,32,34,30,5],[92,93,94],[2]),([107,1,2,3,86,4,5],[],[0]),([0,1,86,30,24],[11,13,95],[0,2]),([0,99,1,3,86,4,24],[96,97,98,99],[0,2]),([25,192,1,3,4],[5,14,18,57,100],[]),([193,25,0,1,3,4],[15,18,21,57,101,102,103],[]),([106,25,0,1,3,4],[15,21,57,101,103,104],[0]),([158,0,1,194,3],[18,62,101,105],[3]),([158,161,25,0,1,3,4],[17,18,62],[]),([170,0,1,126,4],[18,55,57,106],[2]),([25,1,109,3,4],[21,55],[0,1]),([114,95,94,0,2,3,4],[5,28,107,108,109,110],[0,2]),([95,94,0,2,3,4,30],[17,107,111,112],[0,2]),([114,174,0,1,2,4,5],[],[]),([95,94,0,2,28,3,4],[107,108,113,114],[0,2]),([158,101,25,0,1,3,4],[21,55,62,101,103,115],[0]),([95,195,94,0,2,3,4],[5,17,107,108,109,114,116,117],[2]),([95,0,96,3,4],[24,107,116,118],[0,1]),([25,102,1,3,4],[55,59,119],[0,1]),([114,25,0,1,26,3,4],[5,29,57,103,120],[0,1]),([25,0,1,28,30],[16,18,57,121],[0,2]),([25,0,1,26,3,4,30],[17,18,103],[0]),([25,0,1,26,28,3,4],[21,55,57,103],[0]),([27,25,0,1,3,4,30],[17,18,57,62,101],[0]),([158,27,25,0,1,3,4],[21,55,62,101,103],[]),([128,197,1,2,3],[62,122,123,124],[]),([27,170,25,0,1,3,4],[5,17,21,55,57,103,125],[]),([157,179,128,0,1,2,3],[31,60,61,62,64,126],[]),([27,0,26,3,4],[21,56,103,118],[0,1]),([199,1,2,201,3,4,5],[],[]),([114,1,204,2,202,4,5],[127],[]),([0,99,1,2,86,30,5],[87,95,128,129,130],[0]),([158,205,25,0,1,3,4],[18,21,62,101],[1]),([206,25,0,1,3,4],[5,14,15,17,21,57,62,101,103,131],[]),([114,25,0,108,1,3,4],[5,19,57,62,101,132,133],[0,2]),([162,25,207,0,3],[18,21,103,134],[0]),([210,1,2,3,208,4,5],[],[]),([0,99,2,3,104,4,5],[],[0,2]),([0,144,1,2,212,4,5],[],[]),([0,144,1,2,3,146,5],[135],[0]),([215,0,144,1,2,3,5],[],[]),([174,0,1,2,30,5,47],[136],[]),([179,0,196,2,3],[31,60,137,138],[1]),([128,216,0,1,3],[31,64,139,140],[]),([129,0,1,2,92,3,5],[],[0]),([0,145,1,2,3,4,147],[],[0,1]),([0,71,130,22,4,15],[38,39,141,142],[0,1]),([144,1,217,2,3,4,5],[],[]),([87,0,1,2,86,30,5],[],[0]),([0,76,3,90,47],[32,33,47,143,144],[0,1]),([112,0,1,2,72,30,5],[84],[0]),([91,128,0,1,2,3,47],[61],[]),([8,218,1,3,5],[5,67,145,146,147],[]),([152,153,0,71,4,30,5],[],[]),([220,128,0,1,2,3],[31,61,148,149,150,151],[]),([158,25,0,1,3,38,4],[18,62,103],[0]),([111,112,0,1,2,3,4],[],[0]),([8,222,1,3,5],[67,152,153,154],[]),([128,0,48,1,78,2,3],[31,60,61,64,155],[]),([97,1,2,3,72,4,5],[],[0]),([120,0,71,1,30,5,119],[83,84],[0]),([1,2,3,72,77,4,5],[135],[0]),([51,50,0,2,3,4,5],[],[0]),([0,224,1,2,3,4,5],[82,135,156,157],[]),([225,25,0,1,3,4],[15,18,57,103,158],[]),([120,121,0,71,3,4,5],[159],[0]),([187,0,226,1,2,30,119],[83,84,86,160],[]),([157,128,0,71,1,3],[31,61,62,64,126],[0]),([0,71,76,3,227,5,47],[161,162],[1]),([152,0,1,131,4,15],[37,75,163,164],[0]),([8,0,31,3,36],[165,166,167,168],[2]),([228,229,0,71,3,4,5],[159],[]),([111,0,1,2,72,30,5],[84],[0]),([230,231,0,71,3,4,5],[159],[]),([91,223,0,1,2,3,47],[82,169],[]),([120,121,0,1,2,30,5],[160,170],[0]),([128,223,0,1,2,3],[31,61,64,148,150,171,172,173],[]),([0,1,2,72,30,5,74],[45,84,174,175,176],[0]),([129,143,232,0,1,2,5],[48],[]),([0,71,76,30,5,15,47],[177,178,179],[]),([114,0,71,130,4,5,15],[],[0]),([129,174,0,1,2,30,5],[82],[]),([87,0,1,3,86,4,24],[],[0]),([111,0,76,3,72,4,5],[],[0]),([0,71,76,30,5,119],[47,83,160,180,181],[0]),([128,233,0,1,3],[31,64,182,183],[]),([114,152,153,0,71,4,5],[],[]),([0,71,130,3,4,5,47],[39,79],[1]),([0,1,2,73,72,30,5],[45,84,93,129,174,175,184],[0]),([162,25,0,1,3,126,4],[18,21,55,103],[0]),([235,8,0,1,3,5],[84,166,168,185,186,187,188,189],[]),([91,0,1,2,3,90,47],[33,35,190,191,192],[0]),([25,0,108,1,28,3,4],[17,21,57,62,101,103,193],[0,2]),([0,1,2,3,237,4,238],[],[1]),([112,0,76,3,72,4,5],[],[0]),([0,76,72,30,5],[44,45,47,50],[0]),([0,71,154,3,4,5,119],[159],[0]),([0,76,3,73,72,4,5],[162,179,194,195,196],[0]),([0,71,133,3,4,5,132],[159,197],[0,1]),([114,27,25,0,1,3,4],[5,17,21,57,58,103,125],[0]),([129,143,0,71,1,2,5],[84,198],[0]),([0,71,239,3,172,4,5],[159],[]),([129,0,71,130,3,4,5],[],[]),([0,1,3,86,104,4,24],[96],[0]),([128,223,0,1,2,3,47],[61,171],[]),([128,0,1,2,92,3],[31,64,148,150,199,200],[0]),([152,0,144,1,4,5,15],[],[]),([27,25,0,1,28,3,4],[21,57],[0]),([0,76,3,72,4,5,74],[162,179,194,195,201],[0,1]),([91,0,1,2,3,47],[35,192,202,203],[]),([128,0,71,76,3],[31,47,61,204,205],[0]),([240,211,0,1,2,3,4],[],[1]),([128,0,71,76,3,47],[31,47,61,204,205],[0]),([0,71,130,4,30,5,15],[39],[]),([134,0,1,2,30,5],[88,206],[]),([0,71,130,3,4,5,15],[141,159],[]),([179,128,155,0,1,2,3],[31,60,61,62,64,207],[]),([241,174,0,1,2,30,5],[82],[]),([151,128,0,1,2,3,47],[31],[0]),([0,71,133,3,4,5,15],[197,208],[0]),([0,242,1,2,3,4,5],[156,157,209],[]),([152,153,0,71,22,4,15],[142,210],[0,1]),([128,0,1,243,2,3],[31,61,148,150,211,212],[]),([151,128,0,1,2,3],[31,64,148,150,213,214],[0]),([157,128,156,0,1,2,3],[31,60,61,62,64],[0]),([129,0,71,76,3,5,132],[47,215,216],[0]),([128,155,0,71,1,3,47],[31,61,62,207],[0]),([25,0,37,38,4],[18,57,103,217],[1]),([91,128,0,1,2,3],[31,60,61,64,148,150,218,219],[]),([157,128,0,71,1,3,47],[31,61,62,126],[0]),([152,153,0,71,3,4,5],[159],[]),([0,1,2,154,30,5,119],[83],[0]),([128,155,0,48,1,2,3],[31,60,61,64,207],[]),([129,0,1,2,133,3,5],[],[0]),([128,232,0,1,78,3],[31,61,62,64],[]),([128,0,244,2,3],[60,62,64,220],[]),([129,143,0,1,2,76,5],[],[0]),([0,71,1,245,3,4,5],[62,84,159],[]),([0,1,2,130,4,137,5],[],[0]),([128,0,1,2,92,3,47],[31],[0]),([246,8,0,1,3,5],[166,168,186,188,221,222],[]),([129,0,71,76,3,5,47],[162,223],[0]),([0,1,247,2,30,5,119],[83,224],[]),([248,0,221,3,5],[118,168,185,225,226],[]),([25,0,108,1,3,4,30],[17,18,227],[0,2]),([232,0,1,249,30,5,119],[84],[]),([128,0,1,2,3,250],[31,60,61,64,148,150,228,229],[]),([129,0,71,76,30,5,15],[162,230],[]),([129,0,1,251,2,3,5],[],[]),([150,0,1,2,3,72,5],[],[0]),([0,1,252,2,4,137,5],[],[]),([134,0,1,2,30,5,119],[231],[]),([232,0,1,16,4,137,5],[],[]),([128,155,0,71,1,3],[61,62,64,207],[2]),([128,0,1,243,2,3,47],[31],[]),([128,232,0,1,78,3,47],[62,64],[]),([157,128,0,48,1,2,3],[31,60,61,62,64,126,232],[]),([179,128,219,0,2,3],[31,60,62,64],[]),([128,253,1,2,3],[62,123,233,234],[]),([179,128,0,1,78,2,3],[31,60,61,62,64,72],[]),([254,25,0,1,3,4],[15,17,21,57,62,101,103,235],[]),([220,128,0,1,2,3,47],[31],[]),([0,1,2,3,73,4,74],[],[0]),([179,128,219,0,2,3,47],[31,62],[]),([129,0,1,243,2,3,5],[],[]),([255,0,1,2,3,5,47],[],[]),([129,232,0,1,78,3,5],[],[]),([1,257,2,3,208,4,5],[],[]),([258,248,8,0,1,3,5],[67,84,166,168,185],[]),([259,8,0,1,3,5],[84,166,168,185,186,188,236,237],[]),([25,1,260,3,4],[14,18,21,57],[]),([248,9,8,0,1,3,5],[67,84,166,168,185],[]),([261,0,262,3,5],[118,238,239,240,241],[]),([261,263,44,0,2,3,5],[79,84,239,240,242],[]),([0,71,130,3,4,5,132],[39,79],[1]),([1,2,3,236,264,4,5],[],[]),([258,265,8,0,1,3,5],[67,84,166,168,185],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_6_0 : checkNodesBT W_17 g_17 F_17 P_17_6 A_17 B_17_5 6 N_17_6_0 = true := by decide +kernel
def N_17_6_1 : List NodeSpec := [([9,0,1,3,10],[67,166,243,244],[3]),([128,0,267,2,3],[60,62,64,245],[]),([258,0,1,268,3],[84,166,246],[3]),([1,100,2,3,86,4,5],[247],[0,2]),([269,44,0,2,3,5],[240,242,248,249,250,251],[]),([234,8,188,0,3],[168,185,252,253],[2]),([0,270,64,4,36],[167,254,255,256],[]),([113,0,2,3,32,4,36],[],[0,2]),([271,25,0,1,3,4],[15,18,21,57,101,257],[]),([25,272,1,3,4],[5,14,18,57,258],[]),([273,1,2,3,236,4,5],[],[]),([274,0,1,2,3,166,5],[],[]),([275,276,0,1,2,3,4],[],[1]),([278,279,0,2,3,4,5],[],[2]),([25,0,1,3,126,4,43],[18,21,55,62,103],[0]),([129,232,0,1,280,3,5],[],[]),([0,256,2,3,209,4,5],[],[3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_6_1 : checkNodesBT W_17 g_17 F_17 P_17_6 A_17 B_17_5 6 N_17_6_1 = true := by decide +kernel
def N_17_6 := N_17_6_0 ++ N_17_6_1
def B_17_6 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_6
set_option maxRecDepth 500000 in
lemma B_17_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 6 xs.toFinset) B_17_6 := by
  have hP := buildPoolsSubBT_sound (pdepth := 11) (W := W_17) (raw := r_17) (pspecs := ps_17) (used := [5,9,10,11,13,14,15,16,17,18,19,21,24,28,29,31,32,33,35,37,38,39,44,45,47,48,50,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250,251,252,253,254,255,256,257,258]) S_17_ok
  have hm0 := checkNodesBT_mem (by decide) gp_17 W_17_ok hP A_17_ok B_17_5_ok C_17_6_0
  have hm1 := checkNodesBT_mem (by decide) gp_17 W_17_ok hP A_17_ok B_17_5_ok C_17_6_1
  exact buildBucketsBT_of_mem (forall_append (hm0) hm1)
def P_17_7 : BT (Option BoundPool) := buildPoolsSubBT 11 W_17 r_17 S_17 ps_17 [0,5,10,13,15,17,18,21,31,33,39,45,47,55,57,60,61,62,64,66,67,75,77,79,82,83,84,86,87,88,90,92,93,96,97,98,99,101,103,107,108,109,112,114,115,116,118,120,121,122,125,129,132,133,135,141,142,144,145,148,150,152,157,159,160,161,162,164,166,167,168,170,174,175,177,178,179,181,184,185,186,188,190,193,194,195,196,198,205,208,209,215,216,223,224,227,230,231,233,239,240,242,247,253,258,259,260,261,262,263,264,265,266,267,268,269,270,271,272,273,274,275,276,277,278,279,280,281,282,283,284,285,286,287,288,289,290,291,292,293,294,295,296,297,298,299,300,301,302,303,304,305,306,307,308,309,310,311,312,313,314,315,316,317,318,319,320,321,322,323,324,325,326,327,328,329,330,331,332,333,334,335,336,337,338,339,340,341,342,343,344,345,346,347,348,349,350,351,352,353,354,355,356,357,358,359,360,361,362,363,364,365,366,367,368,369,370,371,372,373,374,375,376,377,378,379,380,381,382,383,384,385,386,387,388,389,390,391,392,393,394,395,396,397,398,399,400,401,402,403,404,405,406,407,408,409,410,411,412,413,414,415,416,417,418,419,420,421,422,423,424,425,426,427,428,429,430,431,432,433,434,435,436,437,438,439,440,441,442,443,444,445,446,447,448,449,450,451,452,453,454,455,456,457,458,459,460,461,462,463,464,465,466,467,468,469,470,471,472,473,474,475,476,477,478,479,480,481,482,483,484,485,486,487,488,489,490,491,492,493,494,495,496,497,498,499,500,501,502,503,504,505,506,507,508,509,510,511,512,513,514,515,516,517,518,519,520,521,522,523,524,525,526,527,528,529,530,531,532,533,534,535,536,537,538,539,540,541,542,543,544,545,546,547,548,549,550,551,552,553,554,555,556,557,558,559,560,561,562,563,564,565,566,567,568,569,570,571,572,573,574,575,576,577,578,579,580,581,582,583,584,585,586,587,588,589,590,591,592,593,594,595,596,597,598,599,600,601,602,603,604,605,606,607,608,609,610,611,612,613,614,615,616,617,618,619,620,621,622,623,624,625,626,627,628,629,630,631,632,633,634,635,636,637,638,639,640,641,642,643,644,645,646,647,648,649,650,651,652]
def N_17_7_0 : List NodeSpec := [([230,231,0,1,2,3,4,5],[159,259,260,261],[0]),([152,153,0,1,2,3,4,5],[159,259,262,263],[0]),([152,282,1,2,3,4,5],[84,264,265,266,267,268],[]),([157,128,0,1,2,3],[31,60,61,62,64,269,270],[0]),([128,0,1,196,2,3],[31,61,62,64,88,122,271],[0,1,2]),([179,128,0,1,2,3],[31,60,61,62,64,148,272,273],[0]),([128,155,0,1,2,3],[31,60,61,62,64,82,274,275],[0,2]),([152,153,0,1,2,22,4,15],[17,75,142,276,277],[0,1]),([283,128,0,1,2,3],[60,61,62,64,79,278,279],[]),([283,156,0,2,3,53],[280,281,282,283,284],[2,3]),([282,1,2,22,4,15],[17,142,268,285,286,287],[1]),([128,0,48,1,2,3,47],[31,60,61,62,64,150,288,289],[0,2]),([152,0,284,1,2,22,4,15],[17,75,142,164,276,277],[1]),([228,229,0,1,2,3,4,5],[159,259,290,291],[0]),([129,0,285,1,2,3,5],[62,292,293,294,295],[2]),([152,153,0,1,2,4,30,5],[296,297],[0]),([128,0,286,1,2,3],[31,60,61,62,64,298,299],[2]),([120,0,1,2,30,5,119],[83,84,86,87,88,160,170,300,301],[0,2]),([120,121,0,1,2,3,4,5],[159,259,302,303],[0]),([0,226,1,2,30,5,119],[83,84,86,87,88,160,170,300,304],[0,2]),([187,121,0,1,2,3,4,119],[84,305],[0]),([0,1,2,287,30,5],[87,306,307,308,309],[]),([114,0,1,2,289,5],[17,79,310,311,312],[0]),([190,0,1,2,28,5],[17,313,314,315],[0]),([0,1,2,30,36,119],[83,84,86,316,317],[]),([0,284,1,2,4,137,5],[84,318,319,320,321],[2]),([187,0,226,1,2,3,4,119],[84,303,305,322],[0]),([0,1,2,3,32,34,4,5],[209,259,323,324,325],[0,2]),([192,31,2,3,4,36],[167,326,327,328,329,330],[2]),([0,31,2,28,30,36],[87,167,314,329,331,332],[2]),([0,1,3,86,4,24],[96,98,99,333],[0,2]),([114,25,0,1,3,4],[18,21,55,57,103,121,133],[0,1,2]),([187,0,1,2,30,119],[83,84,86,88,309,334],[0,2]),([25,0,1,28,3,4],[21,55,57,101,103,193],[0,2]),([25,0,108,1,3,4],[17,21,55,57,62,101,103,132],[0,1,2]),([95,94,0,2,3,4],[17,62,107,108,109,114,116,335],[0,1,2,3]),([0,1,2,32,30,5],[87,92,93,336],[0,2]),([27,25,0,1,3,4],[15,17,21,55,57,62,101,103,125],[0,1]),([290,0,1,22,4,15],[17,142,276,337,338],[1]),([0,1,2,292,3,291,5],[247,339,340,341,342,343],[]),([114,293,0,1,2,198,4,5],[5,17,344],[]),([199,0,1,200,2,3,4,5],[17,62,209,259,344,345,346,347],[0]),([1,204,2,3,202,4,5],[17,247,348,349,350,351,352],[0,2]),([294,94,0,2,3,4],[107,108,112,114,353],[3]),([129,143,0,1,2,5],[17,62,198,354,355],[0,2]),([162,129,0,1,16,2,3,5],[90,356,357],[]),([234,295,296,188,0,3],[358,359,360,361,362],[0,2]),([162,207,0,23,3,24],[363,364,365,366,367],[0,2]),([278,0,1,2,3,4,277,5],[159,247],[0]),([0,256,1,2,3,208,4,5],[159,247,368,369,370,371,372,373],[0]),([152,0,1,2,3,4,122,5],[209,259,374,375],[]),([297,0,1,2,3,4,5,47],[159,259,376,377],[]),([0,1,2,299,4,15],[17,277,378,379,380],[2]),([171,0,1,2,3,301],[79,381,382,383,384,385],[]),([0,1,2,3,302,4,303,5],[17,62,386,387,388],[]),([275,0,1,2,3,236,4,5],[84,135],[0]),([128,0,1,2,3,49],[31,61,62,64,233,389],[0,1,2]),([304,0,1,2,3,302,4,5],[62,82,388],[]),([0,1,2,3,236,4,5,238],[84,135,386,390,391],[0,1,2]),([0,1,305,3,4,24],[13,98,363,392,393,394],[2]),([234,188,0,63,64,4],[359,395,396,397,398],[1,2]),([0,1,270,64,4,5],[336,395,399,400,401,402],[0]),([25,0,1,3,126,4],[17,18,21,55,57,62,103,403],[0]),([187,44,0,2,3,5],[79,239,242,309,404],[2]),([234,8,0,1,3,5],[67,84,166,168,185,405,406],[0]),([8,0,1,3,5,36],[67,84,166,168,317,407],[0]),([0,99,1,2,3,86,4,5],[97,159,196,247,333,408,409,410],[0]),([8,0,31,1,3,5],[67,166,185,336,411],[0,2]),([8,0,306,1,3,5],[67,84,166,168,185,412,413],[2]),([152,0,1,2,3,4,307,5],[62,79,259],[]),([261,44,0,2,3,5],[79,84,239,240,242,414,415],[0,2]),([234,188,2,308,3,4],[253,398,416,417,418,419,420],[2]),([114,152,0,71,1,4,5,15],[84,421],[0]),([240,0,144,1,2,3,4,5],[84,135],[0]),([0,71,76,3,4,5,309],[47,179,215,422,423,424,425],[]),([185,0,1,2,3,47],[62,79,82,389,426],[0]),([0,284,1,2,3,4,277,5],[62,159,247,427,428,429,430,431,432],[]),([0,71,76,3,4,5,15],[5,47,159,178,215,263,433,434,435],[0]),([129,0,48,1,2,3,5],[62,289,436,437,438,439],[2]),([129,232,0,1,2,3,5,132],[17,216,440,441],[0,2]),([129,0,71,1,2,3,5,132],[17,62,84,184,293,295,442],[0]),([162,25,0,1,3,4],[17,18,21,55,57,62,103,443],[0,1]),([232,0,1,2,30,5,119],[83,84,86,87,160,181,300,441,444],[0,2]),([0,37,23,38,4,24],[98,364,445,446,447],[0,2,3]),([186,0,1,2,3,4,5,132],[17,62,88,209,292,448],[]),([0,1,2,3,311,4,291,5],[135,209,340],[]),([174,0,1,2,4,30,5],[82,449],[0]),([0,312,1,2,3,4,5,47],[55,67,82,247,450,451],[]),([0,1,2,3,72,4,5,74],[84,135,195,452,453,454,455],[0,1]),([8,0,1,3,5,10],[67,84,145,166,168,185,456],[0]),([0,1,247,2,3,4,5,119],[224,305],[0]),([0,71,1,2,30,5,119],[83,84,86,87,88,160,170,184,300,457],[0,2]),([134,0,1,2,3,4,5],[82,135,157,159,224,231,259,458,459],[0]),([0,1,2,3,90,47],[33,144,184,190,280,460],[0,1,3]),([313,0,138,1,2,3,4,5],[84,135,461],[1]),([25,0,1,314,3,4],[18,21,55,57,103,462],[1]),([25,0,1,26,3,4],[17,55,57,62,101,103,120],[0,1]),([162,0,2,3,315,4,5],[84,463,464,465,466],[]),([120,0,71,1,3,4,5,119],[84,209,305,467],[0]),([111,0,1,2,3,72,4,5],[84,135],[0]),([0,284,316,3,4,5],[17,431,468,469,470,471,472],[]),([0,71,130,3,4,5,15],[39,141,159,431,473,474,475],[0]),([129,0,71,76,3,4,5],[47,178,179,209,215,476,477,478,479],[0]),([0,284,1,16,2,22,4,15],[17,75,142,276,277,480],[1]),([152,153,0,71,3,4,5],[17,84,159,259,374,481,482],[0]),([8,0,1,221,3,5],[67,84,152,166,168,188,483],[0]),([0,1,2,3,73,72,4,5],[84,135,195,196,324,452,453,454,455],[0]),([0,71,76,3,172,4,5],[5,47,159,178,215,261,484,485,486],[0]),([152,0,71,1,4,30,5,15],[84,487,488],[0]),([232,0,1,249,3,4,5,119],[84,259],[0]),([281,317,0,71,76,4],[47,178,179,489,490],[1]),([129,0,71,76,3,4,5,15],[47,162,178,179,478,479],[0]),([0,1,251,2,3,4,5,15],[82,208,491],[0]),([192,71,76,3,4,5],[47,179,328,492,493,494,495],[]),([174,0,1,2,3,4,5,47],[62,82,449],[0,1]),([8,0,1,268,3,5],[67,166,168,185,496,497],[0]),([0,71,76,3,4,5,119],[5,162,179,303,305,498,499],[0]),([318,0,71,3,4,5],[47,118,162,178,500,501],[]),([173,0,1,2,3,4,5],[135,157,159,224,259,502,503,504],[]),([129,0,1,2,76,3,5,132],[17,505,506],[0]),([232,0,1,280,3,4,5,132],[507,508],[0,1]),([25,0,1,3,38,4],[17,18,55,57,62,103,509],[0,1]),([0,1,319,2,3,172,4,5],[159],[]),([215,0,1,2,3,5],[17,510,511,512,513],[]),([114,152,153,0,1,2,4,5],[514,515],[0]),([25,0,1,3,4,30],[17,18,55,57,227],[0,2]),([0,144,1,2,4,5,15],[135,184,514,515],[0,1,2]),([0,1,2,3,320,4,5,47],[17,516,517],[]),([179,128,0,1,2,3,47],[31,60,61,62,64,79,148,272,273],[0]),([174,0,1,2,3,4,5,15],[135,209,224,518],[]),([25,0,37,1,3,4],[18,21,55,57,519],[0,1]),([0,71,76,3,4,5,15,47],[47,162,178,179,431,520,521],[0,1]),([173,0,1,2,3,172,4,5],[135,209,522],[]),([112,0,1,2,3,72,4,5],[84,135],[0]),([0,1,2,3,321,5,322],[62,184,209,247,523],[]),([0,1,2,3,323,324,4,5],[17,209,259,521,524,525,526],[2]),([0,1,2,3,325,4,5],[157,247,344,527,528,529],[]),([129,0,71,1,2,30,5,15],[62,84,455],[0]),([152,0,71,1,3,4,5,132],[17,84,208,374,530],[1]),([326,0,1,2,3,323,4,5],[209,259],[3]),([0,71,76,3,30,5,47],[47,162,178,531,532,533],[0,1]),([199,293,0,1,2,3,4,5],[62,209,259,534,535],[]),([192,1,2,213,4,5],[17,184,454,494,536,537,538,539,540],[]),([128,0,48,1,2,3],[31,60,61,62,64,288,289,541],[0,2]),([152,0,71,1,3,4,5,15],[17,84,209,435,542,543],[0]),([174,0,1,2,4,30,5,15],[62,88,449,544],[0]),([234,188,0,2,28,30],[93,253,314,398,545,546],[2]),([327,0,71,76,4,5],[162,178,179,547,548],[]),([0,71,130,3,4,5],[5,39,431,473,474,475],[0]),([0,1,2,72,30,5],[45,84,93,129,174,175,184,454],[0]),([114,0,71,76,4,5,15],[47,178,179,421,515,549],[0,1]),([71,76,3,328,4,5],[47,179,550,551],[]),([80,0,1,3,4,5],[10,66,84],[0,2]),([0,145,144,1,2,3,4,5],[84,135,454,552,553,554,555,556],[0]),([0,71,76,22,4,15],[47,75,142,179,557,558],[0,1]),([134,0,1,2,3,4,5,119],[209,231],[0]),([0,1,2,130,3,4,5,47],[79,559,560],[0,1]),([162,129,152,0,1,2,3,5],[90,357,374],[]),([0,76,3,131,4,5],[47,118,178,179,561,562,563],[1]),([0,71,76,3,329,5],[47,178,179,564,565],[]),([232,0,1,2,3,227,5,47],[62,161,566],[1,3]),([0,1,2,330,3,321,5],[62,184,209,247,455,567],[]),([0,71,76,3,4,5,132],[5,47,159,215,291,568,569,570],[0,1]),([0,71,76,3,4,5,15,132],[47,208,571],[0,1]),([128,232,0,1,2,3,47],[60,61,62,64,205,441,572],[0,2]),([0,71,1,2,3,227,5,47],[84,455,573,574,575],[0]),([174,0,1,2,22,4,15],[75,142,224,276,277,449,518,576,577,578],[1]),([234,188,192,2,3,4],[253,328,398,419,540,579],[2]),([0,1,2,133,3,4,5,132],[159,580],[0,1]),([0,1,189,2,3,4,119],[82,224,305,322,581,582,583],[0]),([114,0,1,252,2,4,5,15],[],[0]),([184,0,1,2,22,15],[17,62,142,584],[0]),([129,232,0,1,2,3,5,47],[62,223,477,566],[0,2]),([152,0,71,1,22,4,15],[17,75,142,164,276,543],[0,1]),([170,25,0,1,3,4],[17,18,21,55,57,103,258],[0,2]),([128,0,1,2,76,3,47],[31,62,64,150,506,585],[0]),([128,0,71,1,2,3],[60,61,62,184,586],[0,2]),([0,71,1,2,30,5,15,47],[17,84,88,454,587],[0,1]),([128,0,71,1,2,3,47],[60,61,62,184,586],[0,2]),([248,8,0,1,3,5],[67,84,166,168,185,186,588,589],[0]),([174,0,1,2,3,4,331,5],[62,449],[]),([0,1,251,2,3,4,5,132],[159],[0,1]),([241,174,0,1,2,3,4,5],[62,82,449],[0]),([174,0,1,2,3,4,5],[82,135,157,159,224,259,449,518,590],[]),([129,0,1,2,213,4,5],[17,184,209,247,357,477,591],[]),([174,0,1,2,3,4,5,132],[62,449,544,592],[1]),([113,0,1,2,3,32,4,5],[209,259],[0,2]),([129,174,0,1,2,3,4,5],[62,209,449],[0]),([152,153,0,71,3,4,5,15],[17,84,431,482,530],[0]),([129,152,0,71,1,3,4,5],[17,84,478],[]),([0,1,2,3,325,198,4,5],[344],[]),([186,0,1,2,3,4,5,15],[17,88,209,224,593],[]),([158,25,0,1,3,4],[15,17,18,21,55,57,62,101,103,115],[0]),([114,174,0,1,2,4,5,15],[224,518],[1]),([228,0,71,1,3,4,5,132],[17,62,84,209,570,594],[0]),([230,0,71,1,3,172,4,5],[17,84,209,486,595],[0]),([0,1,2,154,3,4,5,119],[305],[0]),([0,1,2,76,30,5,119],[83,84,86,87,88,300,506,596],[0]),([128,232,0,1,2,3],[60,62,64,205,441,572],[2]),([0,1,2,130,4,30,5,15],[560],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_7_0 : checkNodesBT W_17 g_17 F_17 P_17_7 A_17 B_17_6 7 N_17_7_0 = true := by decide +kernel
def N_17_7_1 : List NodeSpec := [([0,71,332,3,4,5],[5,47,162,597,598,599],[]),([129,0,1,2,76,30,5,15],[600],[0]),([0,1,2,76,3,227,5,47],[62,600],[0,1]),([0,284,1,2,3,4,333,5],[159,247,375,431,469,601],[]),([114,0,1,2,130,4,5,15],[],[0]),([157,128,0,1,2,3,47],[31,60,61,62,64,269,270],[0,2]),([0,1,2,3,335,4,5],[17,157,247,602,603],[]),([0,1,2,130,22,4,15],[142,276,560,576,578,604,605],[0,1]),([128,0,1,2,76,3],[31,62,64,506,585],[0]),([0,1,2,130,3,4,5,132],[79,560],[0,1]),([0,1,2,239,3,172,4,5],[159],[0]),([0,284,2,22,4,183],[142,277,606,607,608],[1,3]),([192,1,2,198,4,5],[5,326,540,609,610,611],[]),([186,0,1,2,3,4,5],[135,157,159,224,259,593,612],[]),([129,232,0,1,16,3,4,5],[427,507],[]),([129,0,1,2,130,3,4,5],[62,82,478,544],[0]),([0,1,2,3,320,4,5],[17,517,613,614,615],[]),([232,0,1,336,3,172,4,5],[507,616],[]),([129,0,1,2,76,3,5,47],[62,600],[0]),([0,1,2,133,3,4,5,15],[82,208,580],[0]),([114,232,0,1,16,4,5,15],[],[0]),([0,337,2,22,4,15],[17,276,277,617,618,619],[1]),([0,1,2,130,3,4,5,15],[159,605],[0]),([87,0,1,2,3,86,4,5],[159,247],[0]),([152,0,1,2,3,4,338,5],[209,259,375,530],[]),([0,1,252,2,4,30,5,15],[620],[]),([0,1,339,2,3,4,5],[62,157,209,259,621,622,623],[2]),([114,0,203,1,2,202,4,5],[5,17,62,624,625,626],[0]),([9,8,0,1,3,5],[67,84,166,168,185,627,628],[0,2]),([232,0,1,16,4,30,5,15],[629],[]),([232,0,1,2,30,5,15,47],[84,177,630,631,632],[]),([0,1,2,3,237,236,4,5],[84,135,386,390,391,633,634,635,636],[0]),([129,0,71,1,2,3,5,47],[17,62,84,357,455,477],[0]),([129,232,0,1,2,30,5,15],[230,566],[]),([114,174,0,1,2,4,5],[449,518],[]),([0,1,252,2,22,4,15],[75,142,576,578,620,637,638],[1]),([0,76,3,72,4,5],[162,179,194,195],[0]),([232,0,1,16,22,4,15],[17,75,142,276,639],[1]),([340,0,1,2,3,166,4,5],[84,135],[1]),([0,71,76,28,30,5],[0,47,129,179,314,640,641],[0]),([0,1,252,2,3,4,5,47],[79,620],[1]),([0,1,252,2,3,4,5,132],[79],[1]),([129,0,1,252,2,3,4,5],[62,82,478,544],[]),([184,152,0,1,2,3,5],[17,62,77,159,374,642,643],[]),([258,8,0,1,3,5],[67,84,166,168,185,186,644],[0]),([0,144,1,2,3,4,5,147],[84,135,645],[0]),([232,0,1,16,3,4,5,132],[67],[1]),([31,2,308,3,4,36],[167,327,329,417,646,647,648],[2]),([0,1,2,76,30,5,15,47],[649,650,651],[0]),([0,1,252,2,3,4,5,15],[159,638],[]),([128,155,0,1,2,3,47],[31,60,61,62,64,82,275],[0]),([232,0,1,16,3,4,5,15],[507,639,652],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_7_1 : checkNodesBT W_17 g_17 F_17 P_17_7 A_17 B_17_6 7 N_17_7_1 = true := by decide +kernel
def N_17_7 := N_17_7_0 ++ N_17_7_1
def B_17_7 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_7
set_option maxRecDepth 500000 in
lemma B_17_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 7 xs.toFinset) B_17_7 := by
  have hP := buildPoolsSubBT_sound (pdepth := 11) (W := W_17) (raw := r_17) (pspecs := ps_17) (used := [0,5,10,13,15,17,18,21,31,33,39,45,47,55,57,60,61,62,64,66,67,75,77,79,82,83,84,86,87,88,90,92,93,96,97,98,99,101,103,107,108,109,112,114,115,116,118,120,121,122,125,129,132,133,135,141,142,144,145,148,150,152,157,159,160,161,162,164,166,167,168,170,174,175,177,178,179,181,184,185,186,188,190,193,194,195,196,198,205,208,209,215,216,223,224,227,230,231,233,239,240,242,247,253,258,259,260,261,262,263,264,265,266,267,268,269,270,271,272,273,274,275,276,277,278,279,280,281,282,283,284,285,286,287,288,289,290,291,292,293,294,295,296,297,298,299,300,301,302,303,304,305,306,307,308,309,310,311,312,313,314,315,316,317,318,319,320,321,322,323,324,325,326,327,328,329,330,331,332,333,334,335,336,337,338,339,340,341,342,343,344,345,346,347,348,349,350,351,352,353,354,355,356,357,358,359,360,361,362,363,364,365,366,367,368,369,370,371,372,373,374,375,376,377,378,379,380,381,382,383,384,385,386,387,388,389,390,391,392,393,394,395,396,397,398,399,400,401,402,403,404,405,406,407,408,409,410,411,412,413,414,415,416,417,418,419,420,421,422,423,424,425,426,427,428,429,430,431,432,433,434,435,436,437,438,439,440,441,442,443,444,445,446,447,448,449,450,451,452,453,454,455,456,457,458,459,460,461,462,463,464,465,466,467,468,469,470,471,472,473,474,475,476,477,478,479,480,481,482,483,484,485,486,487,488,489,490,491,492,493,494,495,496,497,498,499,500,501,502,503,504,505,506,507,508,509,510,511,512,513,514,515,516,517,518,519,520,521,522,523,524,525,526,527,528,529,530,531,532,533,534,535,536,537,538,539,540,541,542,543,544,545,546,547,548,549,550,551,552,553,554,555,556,557,558,559,560,561,562,563,564,565,566,567,568,569,570,571,572,573,574,575,576,577,578,579,580,581,582,583,584,585,586,587,588,589,590,591,592,593,594,595,596,597,598,599,600,601,602,603,604,605,606,607,608,609,610,611,612,613,614,615,616,617,618,619,620,621,622,623,624,625,626,627,628,629,630,631,632,633,634,635,636,637,638,639,640,641,642,643,644,645,646,647,648,649,650,651,652]) S_17_ok
  have hm0 := checkNodesBT_mem (by decide) gp_17 W_17_ok hP A_17_ok B_17_6_ok C_17_7_0
  have hm1 := checkNodesBT_mem (by decide) gp_17 W_17_ok hP A_17_ok B_17_6_ok C_17_7_1
  exact buildBucketsBT_of_mem (forall_append (hm0) hm1)
def P_17_8 : BT (Option BoundPool) := buildPoolsSubBT 11 W_17 r_17 S_17 ps_17 [0,5,13,15,17,25,26,43,47,51,55,62,67,75,77,79,82,84,87,88,90,93,97,98,99,114,118,129,130,135,142,144,148,156,157,159,162,167,178,179,184,186,195,196,208,209,215,224,247,253,259,260,261,262,263,264,268,275,276,277,279,280,281,284,285,287,289,290,291,292,294,296,297,300,302,303,305,307,308,309,311,314,317,321,322,323,324,326,328,329,332,336,338,340,342,344,346,347,349,356,357,358,359,361,363,364,366,367,369,374,375,383,385,386,387,390,391,393,396,398,400,402,406,409,416,417,418,421,423,424,425,427,430,431,434,435,441,442,446,447,448,449,452,453,454,455,464,469,477,478,479,481,482,485,486,487,488,490,493,494,499,505,506,507,508,514,515,516,518,520,521,522,524,530,531,532,533,534,535,540,543,544,546,548,549,550,552,553,554,555,556,558,559,560,562,565,566,569,570,571,576,578,587,592,599,600,605,607,608,616,618,620,624,626,629,630,631,632,638,639,641,645,646,650,651,652,653,654,655,656,657,658,659,660,661,662,663,664,665,666,667,668,669,670,671,672,673,674,675,676,677,678,679,680,681,682,683,684,685,686,687,688,689,690,691,692,693,694,695,696,697,698,699,700,701,702,703,704,705,706,707,708,709,710,711,712,713,714,715,716,717,718,719,720,721,722,723,724,725,726,727,728,729,730,731,732,733,734,735,736,737,738,739,740,741,742,743,744,745,746,747,748,749,750,751,752,753,754,755,756,757,758,759,760,761,762,763,764,765,766,767,768,769,770,771,772,773,774,775,776,777,778,779,780,781,782,783,784,785,786,787,788,789,790,791,792,793,794,795,796,797,798,799,800,801,802,803,804,805,806,807,808,809,810,811,812,813,814,815,816,817,818,819,820,821,822,823,824,825,826,827,828,829,830,831,832,833,834,835,836,837,838,839,840,841,842,843,844,845,846,847,848,849,850,851,852,853,854,855,856,857,858,859,860,861,862,863,864,865,866,867,868,869,870,871,872,873,874,875,876,877,878,879,880,881,882,883,884,885,886,887,888,889,890,891,892,893,894,895,896,897,898,899,900,901,902,903,904,905,906,907,908,909,910,911,912,913,914,915,916,917,918,919,920,921,922,923,924,925,926,927,928,929,930,931,932,933,934,935,936,937,938,939,940,941,942,943,944,945,946,947,948,949,950,951,952,953,954,955,956,957,958,959,960,961,962,963,964,965,966,967,968,969,970,971,972,973,974,975,976,977,978,979,980,981,982,983,984,985,986,987,988,989,990,991,992,993,994,995,996,997,998,999,1000,1001,1002,1003,1004,1005,1006,1007,1008,1009,1010,1011,1012,1013,1014,1015,1016,1017,1018,1019,1020,1021,1022,1023,1024,1025,1026,1027,1028,1029,1030,1031,1032,1033,1034,1035,1036,1037,1038,1039,1040,1041,1042,1043,1044,1045,1046,1047,1048,1049,1050,1051,1052,1053,1054,1055,1056,1057,1058,1059,1060,1061,1062,1063,1064,1065,1066,1067,1068,1069,1070,1071,1072,1073,1074,1075,1076,1077,1078,1079,1080,1081,1082,1083,1084,1085,1086,1087,1088,1089,1090,1091,1092,1093,1094,1095,1096,1097,1098,1099,1100,1101,1102,1103,1104,1105,1106,1107,1108,1109,1110,1111,1112,1113,1114,1115,1116,1117,1118,1119,1120,1121,1122,1123,1124,1125,1126,1127,1128,1129,1130,1131,1132,1133,1134,1135,1136,1137,1138,1139,1140,1141,1142,1143,1144,1145,1146,1147,1148,1149,1150,1151,1152,1153,1154,1155,1156,1157,1158,1159,1160,1161,1162,1163,1164,1165,1166,1167,1168,1169,1170,1171,1172,1173,1174,1175,1176,1177,1178,1179,1180,1181,1182,1183,1184,1185,1186,1187,1188,1189,1190,1191,1192,1193,1194,1195,1196,1197,1198,1199,1200,1201,1202,1203,1204,1205,1206,1207,1208,1209,1210,1211,1212,1213,1214,1215,1216,1217,1218,1219,1220,1221,1222,1223,1224,1225,1226,1227,1228,1229,1230,1231,1232,1233,1234,1235,1236,1237,1238,1239,1240,1241,1242,1243,1244,1245,1246,1247,1248,1249,1250,1251,1252,1253,1254,1255,1256,1257,1258,1259,1260,1261,1262,1263,1264,1265,1266,1267,1268,1269,1270,1271,1272,1273,1274,1275,1276,1277,1278,1279,1280,1281,1282,1283,1284,1285,1286,1287,1288,1289,1290,1291,1292,1293,1294,1295,1296,1297,1298,1299,1300,1301,1302,1303,1304,1305,1306,1307,1308,1309,1310,1311,1312,1313,1314,1315,1316,1317,1318,1319,1320,1321,1322,1323,1324,1325,1326,1327,1328,1329,1330,1331,1332,1333,1334,1335,1336,1337,1338]
def N_17_8_0 : List NodeSpec := [([230,0,1,2,3,172,4,5],[17,51,135,209,260,261,486,522,616,653,654,655],[0]),([152,0,1,2,3,4,5,15],[17,51,135,209,262,263,435,652,656,657,658,659],[0]),([0,284,1,2,3,4,5,15],[5,17,51,262,263,321,435,652,656,660,661,662],[2]),([129,152,0,1,2,3,4,5],[62,84,88,209,259,357,374,375,477,478,530,663,664,665],[0]),([152,0,1,2,3,4,5,132],[17,208,374,530,592,659,666,667,668,669,670],[0,3]),([152,153,0,1,2,3,4,5,15],[17,374,375,427,431,482,530,671],[0]),([152,153,0,1,2,3,4,5],[17,84,159,374,375,481,658,671,672,673,674,675,676,677],[0,2]),([0,1,2,3,341,4,5,47],[17,51,84,275,369,521,678,679,680],[3]),([283,156,0,2,3,4,5],[79,84,114,284,521,680,681,682],[0,2]),([0,337,2,3,4,5,15],[17,84,427,618,671,683],[0,2]),([152,0,1,2,3,4,5,183],[84,118,264,374,375,659,684,685,686,687],[0]),([0,342,1,2,3,172,4,5],[5,17,51,135,260,261,486,616,653,688,689],[2]),([129,0,284,1,2,3,4,5],[62,84,159,321,357,430,431,469,477,478,663,690,691],[2]),([0,284,1,2,3,4,5,132],[17,79,208,321,430,469,666,668,669,670,692,693],[1,2]),([0,284,1,16,2,3,4,5,15],[17,356,375,427,430,431,469,671],[0]),([0,284,2,3,4,5,183],[17,84,431,469,607,608,671,694],[0,3]),([0,1,2,3,343,4,5,47],[5,17,51,289,369,516,678,680,695],[]),([128,0,1,2,3,47],[62,88,148],[0,2]),([128,0,1,2,3],[88,148],[0,2]),([283,0,1,2,3,53,47],[62,144,279,280,281,696,697,698],[0,1]),([0,284,1,2,22,4,15],[17,75,142,276,277,321,576,661,699],[0,1,2]),([114,0,284,1,2,4,5,15],[84,321,421,514,515,661,662,700,701,702],[0,2]),([0,1,2,3,227,5,47],[84,88,703,704],[0,1,2,3]),([129,0,1,2,3,5,132],[62,88,705,706],[0,2]),([344,0,1,2,3,4,5],[157,209,224,247,317,707,708,709,710],[]),([345,0,1,2,3,4,5],[135,157,159,247,308,309,711,712],[]),([0,1,2,3,4,347,5],[17,135,209,441,507,713,714,715,716,717,718],[]),([349,0,1,2,3,4,5,348],[84,209,247,393,719,720,721,722,723,724,725,726],[]),([350,0,1,2,3,4,5],[62,135,157,247,259,308,441,507,727,728,729],[]),([327,0,71,1,2,4,5],[82,135,224,454,455,587,730,731,732],[0]),([234,1,2,308,3,4,5],[209,224,406,417,646,733,734,735,736],[0]),([1,260,2,3,4,5,24],[737,738,739,740,741,742,743,744,745,746],[2]),([31,1,2,308,3,4,5],[156,209,336,400,416,646,747,748],[0]),([0,71,1,2,3,4,5,15,47],[17,62,84,184,369,375,427,431,454,455,516,521,544,587,671,680,749],[0,1]),([129,232,0,1,2,3,4,5],[62,84,247,259,357,441,477,479,507,631,632,663,750],[0]),([232,0,1,2,3,4,5,15,132],[17,375,441,571,668],[0,1,2]),([234,0,1,63,64,4,5],[224,396,402,406,735,751,752,753,754],[0,1]),([294,0,31,2,3,4,36],[159,167,329,755,756,757,758,759],[0,3]),([234,295,0,2,3,38,4,5],[84,406,760,761,762,763,764],[]),([0,31,2,3,64,4,36],[62,167,329,757,765,766,767,768],[2]),([129,0,1,2,3,5,47],[62,88,135,357,477,769,770],[0,2]),([0,284,1,2,3,4,7,5,15],[62,84,321,375,391,427,430,431,544,671],[0,3]),([0,1,252,2,3,4,5,15],[62,135,224,375,431,544,620,638,771,772,773],[0]),([234,0,2,3,38,4,7,5],[84,114,391,406,774,775,776,777],[]),([234,188,0,63,2,3,4],[253,358,398,418,778,779,780],[0,2]),([234,300,0,2,3,4,5],[62,159,406,781,782],[]),([0,1,252,2,3,4,5],[51,62,82,135,209,375,431,620,772,773],[0]),([0,144,1,2,3,4,5],[82,84,135,157,159,184,259,454,552,553,554,555,556,645],[0,1]),([0,1,2,270,3,4,5],[82,247,336,400,778,783,784,785],[0,2]),([232,0,1,2,22,4,15],[17,75,276,277,441,558,576,632,786],[0,1,2]),([232,0,1,2,3,329,5],[441,565,631,632,787,788,789,790],[]),([352,0,1,2,3,4,5],[5,17,157,506,791,792,793],[]),([0,71,76,3,4,30,5],[43,47,162,178,179,794,795,796],[0,1]),([353,0,1,2,3,4,5],[17,82,157,224,247,308,797,798,799,800,801],[]),([0,71,1,2,3,4,5,15,132],[17,62,84,184,427,431,544,592,669,693],[0,1,2]),([0,354,1,2,3,4,5],[55,62,82,157,209,259,767,802,803,804,805],[]),([355,0,1,2,3,4,5],[135,157,159,209,259,308,441,507,632,806,807,808,809],[]),([232,0,1,2,28,30,5],[0,84,87,93,129,307,441,632,810,811,812],[0]),([232,0,1,2,3,4,5,119],[84,97,247,303,305,322,499,507,566,632,813,814],[0,2]),([0,1,2,76,3,4,5,132],[5,84,448,506,508,570,815,816,817],[0,1]),([357,0,1,2,3,4,5],[17,55,157,224,247,507,818,819,820,821],[]),([162,0,1,16,2,3,4,5,15],[17,84,90,375,671,822,823,824],[0,2]),([187,1,260,2,3,4,5],[156,247,309,739,743,745,825,826],[2]),([0,1,2,3,4,358,5],[17,184,827,828,829,830,831,832],[]),([0,1,2,76,3,172,4,5],[5,17,486,506,522,616,650,653,833],[0]),([0,71,1,2,3,30,5,47],[17,84,88,184,455,532,533,587,749,834,835,836,837],[0,1,3]),([232,0,1,16,3,4,5,15],[17,84,375,427,431,629,639,822,838,839],[0]),([282,1,2,3,4,5,15],[5,17,84,268,287,431,684,840],[0]),([0,1,2,3,360,4,5],[5,62,114,841,842,843,844,845],[]),([0,1,2,3,323,4,5,47],[84,369,516,521,524,678,846,847],[1,3]),([0,1,2,76,3,4,5,309],[5,62,84,224,425,506,651,712,848,849,850,851],[0]),([0,71,1,2,3,4,5,119],[82,84,97,159,224,247,259,302,303,305,322,454,455,813,852],[0,2]),([0,1,2,76,3,4,5,15,47],[17,62,506,559,600,650,651],[0,1]),([0,1,2,3,334,4,5,24],[17,742,744,853,854],[0]),([361,0,1,2,3,4,5],[55,157,159,209,224,507,631,855,856,857,858],[]),([0,71,1,2,22,4,15],[17,75,142,184,276,277,454,576,859],[0,1,2]),([0,1,2,76,3,4,5,15,132],[17,208,506],[0,1]),([318,0,1,2,3,4,5],[82,135,157,224,506,600,650,860,861,862],[0]),([114,232,0,1,2,4,5,15],[84,441,515,549,631,632,702,712,863],[0,1,2]),([0,1,2,3,4,5,362],[17,55,62,507,864,865,866,867,868,869,870],[]),([363,0,1,2,3,4,7,5],[84,114,209,259,391,871,872,873],[]),([199,0,1,2,3,198,4,5],[17,247,336,344,346,347,535,874],[0]),([114,0,71,1,2,4,5,15],[84,184,421,454,514,515,587,702,712,875],[0,1,2]),([364,0,1,2,3,4,5],[5,17,62,79,114,157,224,876,877,878,879],[]),([0,71,1,2,3,4,5,132],[17,62,84,159,184,247,259,290,291,292,448,508,570,815,880],[0,1,2]),([0,366,1,2,3,4,5],[82,157,159,247,259,881,882,883,884,885,886],[]),([368,0,1,2,3,4,5],[17,88,157,159,209,259,887,888,889,890],[]),([0,1,2,76,3,30,5,47],[84,506,533,630,650,749,834,836,891],[0,1]),([327,232,0,1,2,4,5],[548,566,631,632,731,892,893],[]),([0,1,2,130,3,4,5,15],[62,135,224,427,431,544,560,605,771,894,895],[0]),([0,1,2,3,72,4,5],[84,135,195,196,324,452,453,454,455],[0]),([171,0,71,76,3,4,5],[47,159,162,178,179,215,896,897,898,899],[0,1]),([187,192,1,2,3,4,5],[156,309,326,328,540,825,826,900],[2]),([0,37,23,2,38,4,5],[130,409,446,901,902,903],[0,2,3]),([114,0,71,76,3,4,5],[25,47,159,178,179,215,556,641,904,905],[0,1]),([369,0,1,2,3,213,4,5],[17,184,209,247,906,907,908],[]),([0,1,2,3,370,4,5],[79,84,209,259,317,599,909,910],[]),([0,1,2,76,22,4,15],[17,142,276,506,578,651,911],[0,1]),([232,0,1,2,3,4,5,132],[84,247,291,441,507,508,569,815,817,912],[0,1,2]),([232,0,1,2,3,30,5,47],[84,441,531,532,630,631,834,836,913],[0,1,3]),([0,1,2,3,371,4,5],[308,507,709,914,915,916,917],[]),([232,0,1,2,3,4,5,15],[17,247,263,434,441,507,631,632,652,656,918],[0,2]),([372,0,1,2,3,4,5],[62,82,157,209,247,507,902,919,920,921,922,923],[]),([0,71,1,2,3,4,5,309],[62,84,184,224,247,424,425,454,712,848,850,924],[0,1]),([0,1,2,3,4,5,373],[17,79,156,159,209,259,925,926,927,928],[]),([0,1,2,3,321,5,47],[17,62,135,184,516,680,929,930,931],[1]),([288,0,1,2,28,3,5],[79,84,311,932,933,934],[0]),([190,0,1,2,3,4,5],[17,157,209,259,317,796,935],[0]),([129,0,71,1,2,3,4,5,15],[17,62,84,184,357,375,454,455,477,587],[0,2]),([129,232,0,1,2,3,4,5,15],[62,84,427,441,479,566,631,632,663],[0,2]),([281,0,71,76,3,4,5],[47,159,178,179,215,936,937,938,939],[0]),([152,0,71,1,3,4,5,15],[17,84,375,427,431,488,530,543,940,941],[0]),([374,0,1,2,3,4,5],[17,62,82,84,157,209,224,247,942,943,944,945,946],[]),([0,1,2,3,4,5,375],[62,79,947,948,949,950,951],[]),([152,0,284,1,2,3,4,5,15],[17,374,375,427,431,469,530,671],[0]),([162,152,0,1,2,3,4,5,15],[17,84,90,427,530,659,671,824,952],[0]),([0,1,2,3,4,5,214],[17,82,84,156,953,954,955,956,957,958],[0]),([0,71,1,2,28,30,5],[84,87,93,129,184,224,307,314,454,810,959,960],[0]),([281,0,1,2,213,4,5],[17,184,209,247,454,961,962,963],[]),([162,207,0,2,3,5,24],[366,367,387,742,744,964,965],[0,2]),([281,317,0,71,1,2,4],[184,454,587,966,967,968,969,970],[0,1]),([152,0,1,2,22,4,15],[17,75,142,276,277,576,658,659,971],[0,1,3]),([0,71,1,2,3,4,5,15],[17,84,159,184,224,247,259,262,263,435,587,652,656,972],[0,2]),([376,0,1,2,3,4,5],[82,157,159,209,259,441,507,632,973,974,975,976],[]),([162,129,0,1,2,3,5],[62,88,159,357,477],[]),([0,1,2,3,213,4,5,47],[17,62,184,516,680,977],[0]),([0,71,1,2,3,329,5],[88,135,184,224,454,587,787,789,978,979],[0]),([0,1,2,3,377,4,43,5],[17,308,309,980,981,982,983,984,985],[]),([187,0,1,2,3,4,119],[82,84,224,305,322,826,986,987],[0,2]),([150,0,1,2,3,4,5],[17,62,84,157,209,224,247,988,989,990,991],[]),([0,1,2,76,28,30,5],[84,87,88,307,314,506,651,992,993],[0]),([174,0,1,2,3,4,5],[62,82,135,157,159,259,375,449,671,994,995,996,997],[0]),([281,317,0,1,2,76,4],[506,650,651,968,969,970,998],[0,1]),([0,1,2,3,378,4,5],[209,441,631,632,999,1000,1001,1002],[]),([162,187,207,0,2,3,5],[309,366,367,1003,1004,1005],[0,2]),([0,1,2,3,4,348,24],[84,209,721,741,742,744,1006],[]),([379,0,1,2,3,4,5],[51,79,82,157,224,824,1007,1008,1009,1010],[]),([174,0,1,2,3,4,5,15],[62,135,224,375,427,431,449,518,544,671,771,994,997],[0]),([0,1,2,3,346,4,5,47],[17,308,369,441,678,680,917,1011],[]),([0,1,2,76,3,4,5,15],[5,17,135,224,435,506,650,651,652,656,1012,1013],[0]),([129,0,71,1,2,3,4,5],[62,84,159,184,209,247,357,442,454,477,478,587,663,1014],[0]),([0,71,76,28,3,4,5],[26,159,162,178,179,196,1015,1016],[0]),([0,1,2,3,380,4,5],[135,209,308,324,507,566,632,1017,1018,1019,1020],[]),([184,0,1,2,3,5,15],[17,62,90,431,507,1021],[0]),([363,317,0,1,2,3,4],[114,224,1022,1023,1024,1025,1026],[]),([0,381,1,2,3,4,5],[17,82,135,157,159,184,259,454,1027,1028,1029,1030],[]),([114,0,1,2,76,4,5,15],[84,421,506,650,651,700,702,712,1031],[0,1]),([281,0,1,2,382,4,5],[114,247,406,735,1032],[]),([0,1,2,3,291,7,5],[17,62,209,336,342,775,1033,1034,1035],[]),([351,0,1,2,3,4,5,15],[17,62,79,90,135,224,427,431,506,771,1036],[]),([369,0,1,2,3,4,5],[17,62,157,184,209,247,907,908,1037],[]),([234,188,0,2,3,64,4],[62,253,358,359,398,767,1038,1039],[0,2]),([162,0,1,2,3,202,4,5],[17,79,130,209,409,624,626,952,1010,1040,1041,1042,1043],[3]),([0,1,2,130,3,4,5],[5,62,82,135,427,431,560,894,895],[0]),([0,383,1,2,3,4,5],[17,84,157,159,224,259,587,1044,1045,1046,1047],[]),([0,71,1,2,3,172,4,5],[17,84,159,184,247,259,260,261,486,522,587,616,653,1048],[0,2]),([327,0,1,2,76,4,5],[82,135,224,600,650,651,731,732,1049],[0]),([234,295,296,0,1,3,5],[209,259,361,406,733,753,1050,1051,1052,1053],[0]),([0,1,384,2,3,4,5],[209,224,259,387,742,1054,1055,1056],[]),([281,317,232,0,1,2,4],[441,490,631,632,966,968,1057,1058],[1]),([0,1,2,3,385,4,5],[17,79,135,156,506,1059,1060],[]),([0,31,2,28,3,4,36],[97,329,757,768,1016,1061,1062],[0,2]),([0,31,2,3,4,30,36],[167,329,757,768,796,817,1063],[0,2]),([0,1,2,3,321,30,5],[62,184,209,247,1064,1065,1066,1067,1068,1069],[]),([234,294,188,0,2,3,4],[253,359,398,759,1070,1071],[0,1]),([386,0,1,2,3,4,5],[5,82,135,157,224,600,651,1016,1018,1022,1072],[]),([0,1,2,76,3,4,5,119],[5,82,84,97,224,305,322,600,651,813,1073],[0]),([1,2,76,3,328,4,5],[224,506,651,1074,1075,1076,1077,1078],[0]),([152,0,1,2,3,4,43,5,15],[84,374,375,427,431,659,984,1079],[0,3]),([114,152,0,1,2,4,5,15],[84,421,514,658,659,676,702,1080],[0]),([114,0,1,2,213,4,5],[17,84,184,209,247,454,554,556,1081,1082,1083],[0,1]),([0,1,2,3,4,36,119],[84,247,305,322,1084,1085,1086],[0]),([187,0,1,2,3,4,348],[5,224,247,309,721,1087,1088],[]),([0,1,387,2,3,4,5],[82,135,247,309,393,826,1003,1089,1090],[]),([232,0,1,2,3,4,5,309],[62,84,247,423,424,441,507,632,712,848,850,1091],[]),([0,1,2,3,236,4,5],[84,135,386,390,391,1092],[0,1]),([388,0,1,2,3,4,5],[5,135,157,159,224,259,1022,1093,1094,1095,1096],[]),([0,1,2,332,3,4,5],[5,79,135,506,599,1097,1098],[0]),([0,1,2,3,389,4,5],[135,308,507,915,1079,1099,1100,1101,1102,1103],[]),([390,0,1,2,3,4,5],[5,55,79,82,157,224,952,1104,1105,1106],[]),([0,1,2,3,38,4,5,391],[62,84,209,920,1107,1108,1109,1110,1111],[]),([162,0,2,3,64,4,5,36],[84,247,317,464,766,767,1038,1112,1113],[0]),([0,37,2,38,4,5,24],[387,446,447,741,742,903,1114],[0,3]),([152,0,1,2,4,30,5,15],[17,296,297,487,659,817,1115,1116,1117],[0]),([232,0,1,2,3,4,5,15,47],[84,135,369,375,427,441,516,520,566,631,632],[0,1,2,3]),([0,1,2,3,131,4,5],[184,454,562,587,1118,1119],[0,1]),([363,295,0,1,2,3,4,5],[67,84,114,209,763,1120,1121],[]),([0,1,2,3,198,4,7,5],[17,336,344,775,1035,1122,1123],[0]),([234,295,188,0,2,3,4],[17,253,358,359,398,761,763,1124,1125],[0,2]),([187,0,37,2,38,4,5],[159,309,446,447,826,1004,1126,1127],[1,2]),([300,0,1,2,3,4,5,24],[62,79,135,387,741,742,1128,1129,1130],[]),([129,0,1,2,76,3,4,5,15],[62,84,431,478,506,600,650,651],[0]),([0,1,2,3,302,4,5],[17,62,84,386,387,1131,1132],[0,2]),([288,0,1,2,3,64,4,5],[62,79,84,224,317,767,1038,1133,1134,1135],[]),([0,1,2,30,5,119],[84,87,88,300],[0,2]),([187,0,1,2,28,30,5],[87,93,307,309,314,810,826,1136,1137],[0,2]),([234,392,0,1,2,3,4,5],[62,67,114,247,406,753,1138],[]),([0,1,2,3,382,4,7,5],[17,84,209,259,406,775,871,1139,1140],[]),([363,0,1,2,3,4,15],[17,224,431,1026,1141],[]),([0,1,2,3,4,5,301],[62,209,259,383,385,1142,1143,1144],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_8_0 : checkNodesBT W_17 g_17 F_17 P_17_8 A_17 B_17_7 8 N_17_8_0 = true := by decide +kernel
def N_17_8_1 : List NodeSpec := [([234,188,0,2,28,3,4],[324,358,359,398,1016,1125,1145],[0,2]),([393,0,1,2,3,4,5],[62,157,209,259,1146,1147,1148],[]),([300,171,0,1,2,3,5],[62,88,383,898,1149],[0]),([0,71,76,22,3,4,5],[47,159,178,179,1001,1150,1151,1152],[0,1]),([0,1,2,3,395,4,5],[114,209,259,1153,1154,1155,1156],[]),([0,1,2,396,3,4,5],[114,209,259,1024,1157,1158,1159],[]),([232,1,2,3,328,4,5],[441,550,632,1075,1160,1161],[]),([0,1,3,397,4,5,24],[17,67,742,1162,1163,1164],[]),([0,398,1,2,3,397,4,5],[17,209,1165,1166,1167,1168,1169,1170],[]),([399,0,1,2,3,334,4,5],[17,209,247,854,1171,1172,1173,1174,1175,1176],[]),([192,1,2,76,3,4,5],[5,224,326,328,506,651,900,1177,1178],[0]),([0,284,1,2,4,30,5,15],[17,296,297,321,487,1115,1117,1179],[2]),([400,0,1,2,3,4,5],[17,157,209,247,259,1180,1181,1182],[]),([25,0,1,3,4],[15],[0,1,2,3]),([162,0,1,2,3,4,5,401],[79,84,209,247,952,1183,1184,1185,1186,1187,1188,1189,1190],[]),([0,1,2,3,4,402,47],[62,79,680,1191,1192],[]),([171,0,1,2,3,4,402],[79,247,1010,1192,1193,1194],[]),([162,207,0,23,2,3,5],[130,366,902,965,1195,1196,1197],[0,2]),([162,310,0,1,3,4,5,24],[84,209,741,742,952,1190,1198,1199,1200,1201],[]),([0,1,403,2,3,4,5],[5,67,224,247,761,784,1202,1203,1204],[]),([162,404,0,1,2,3,4,5],[17,79,84,247,308,824,1205,1206,1207],[]),([162,0,1,2,3,405,4,5],[55,79,84,209,247,885,952,1208,1209,1210,1211,1212,1213],[]),([0,37,1,23,3,4,24],[13,98,259,363,393,1090,1214,1215],[0,2]),([288,0,1,2,3,5,47],[17,62,82,84,317,521,1216],[]),([162,0,1,2,3,377,4,5],[17,79,247,308,309,824,826,1010,1217,1218,1219,1220],[]),([114,0,1,2,198,4,5],[17,135,247,336,344,400,554,712,1221],[0,1,2]),([171,0,1,2,3,4,149],[84,209,247,587,1222,1223,1224],[]),([234,192,1,2,3,4,5],[5,326,328,406,494,540,734,735,900],[0]),([0,1,2,3,406,4,5,47],[84,516,521,678,680,1225,1226],[1,3]),([162,129,0,1,2,3,5,15],[17,62,84,357,431,477,544,1227],[0]),([234,0,1,2,3,397,4,5],[17,67,114,209,247,406,762,1164,1165,1167,1168,1228],[]),([0,1,2,3,407,4,5],[55,507,920,1229,1230,1231,1232],[]),([234,0,1,2,28,30,5],[84,87,93,129,307,314,406,735,810,1233,1234],[0]),([408,0,1,2,3,4,5],[82,157,209,224,259,1022,1235,1236,1237,1238],[]),([8,0,1,3,5],[88,186],[0,2]),([162,0,1,23,3,4,24],[13,17,98,99,135,259,363,364,824,1010,1214,1239],[0]),([0,226,1,2,3,4,5,119],[5,51,84,302,303,305,322,813,1240,1241,1242],[0,2]),([129,0,1,2,76,3,4,5],[5,62,84,478,505,506,650,651,663,1243],[0]),([0,1,409,2,3,4,5],[82,224,247,336,400,758,1070,1244,1245],[]),([234,188,0,2,3,4,30],[253,358,359,398,796,1246,1247],[0,2]),([294,0,1,2,198,4,5],[5,135,247,336,344,758,1248],[]),([0,411,1,2,3,4,5,410],[84,209,1249,1250,1251,1252,1253,1254,1255,1256],[]),([412,0,1,2,3,4,5],[82,135,157,159,224,406,735,753,1257,1258,1259],[]),([0,1,2,413,3,4,5],[5,114,1024,1260,1261,1262,1263],[]),([129,0,1,2,30,5,15],[17,62,82,544,1264],[0,2]),([192,71,1,2,3,4,5],[84,184,224,326,328,454,494,540,900,1265],[0]),([415,0,1,2,3,4,5],[82,135,157,224,259,309,826,1004,1266,1267,1268],[]),([0,203,1,2,3,202,4,5],[17,62,209,349,409,624,626,1040,1042,1043,1269,1270],[0,2]),([293,0,1,2,3,198,4,5],[17,62,209,247,344,400,534,535,874,1123,1271,1272,1273,1274],[0]),([232,192,1,2,3,4,5],[84,156,326,441,493,494,540,632,900,1275],[]),([0,1,2,3,291,30,5],[62,336,630,1068,1276,1277],[]),([0,1,2,3,4,149,15],[84,209,224,671,1278,1279,1280,1281],[]),([0,1,2,3,4,416,5],[17,209,259,336,1282,1283,1284,1285],[]),([0,1,2,22,4,15,183],[17,75,77,142,276,285,687],[0,1,2]),([199,0,1,2,3,4,5],[62,157,209,247,259,336,346,1286],[]),([114,0,31,2,3,4,36],[159,167,329,332,712,755,757,768,905,1287],[0,2]),([232,0,1,2,3,172,4,5],[17,247,261,441,485,507,616,631,653,1288],[0,2]),([0,1,417,2,3,4,5],[62,209,247,259,400,554,712,1289],[]),([0,1,2,3,32,4,5],[97,209,259,323,324,340,400],[0,2]),([0,31,1,2,28,30,5],[87,93,129,307,336,400,810,1290,1291],[0]),([192,31,1,2,3,4,5],[156,326,336,400,494,540,748,900],[0]),([0,1,2,3,323,4,5],[84,209,259,521,524,846,847],[0,2,3]),([418,0,1,2,3,4,5],[82,84,157,209,247,259,1016,1022,1086,1292,1293],[]),([0,1,2,28,30,5,36],[84,87,129,307,314,317,1085,1294,1295],[0]),([0,1,2,3,406,4,5],[84,159,247,308,516,1225,1226,1296,1297],[]),([0,1,2,3,419,30,5],[62,67,309,1298,1299,1300],[]),([192,1,2,3,4,5,36],[84,317,326,328,494,900,1085,1301],[0]),([114,288,0,1,2,3,5],[62,311,905],[0]),([0,1,2,3,4,420,5],[114,209,259,406,1302,1303,1304],[]),([281,421,0,1,2,4,5],[317,1022,1085,1305,1306],[]),([0,1,2,3,289,4,5],[17,79,156,159,209,259,311,317,1307,1308],[0]),([290,0,1,3,4,5,15],[17,84,338,427,431,1309],[0]),([0,1,2,3,422,5,47],[84,114,406,680,1310],[]),([0,1,2,424,3,4,5],[5,224,506,1311,1312,1313],[]),([425,0,1,2,3,4,5],[62,157,209,247,259,406,1314,1315],[]),([234,114,188,0,2,3,4],[253,358,359,398,546,554,905,1316],[0,2]),([0,1,2,426,3,4,5],[114,209,259,324,735,1317,1318],[]),([0,1,2,76,3,329,5],[88,135,224,506,650,651,789,979,1319],[0]),([114,0,1,2,377,4,5],[135,259,308,309,712,826,1320],[]),([427,0,1,2,3,4,5],[82,114,135,157,209,259,406,735,1321,1322],[]),([0,1,2,3,4,428,5],[17,159,247,309,1323,1324,1325],[]),([0,71,76,3,4,5,15],[47,178,179,375,431,1326,1327],[0,1]),([429,0,1,2,3,4,5],[135,157,159,247,308,309,1328,1329],[]),([0,1,2,3,287,4,5],[97,159,247,308,826,987,1018,1330],[0]),([120,0,1,2,3,4,5,119],[51,84,97,209,302,303,305,322,813,1331,1332,1333],[0,2]),([0,1,2,30,5,15,47],[84,88,630,1334],[0,2]),([71,1,2,3,328,4,5],[184,224,454,1074,1075,1076,1078,1335],[0]),([0,285,1,2,3,4,5,132],[5,17,51,290,291,294,508,570,815,1336],[0,1,2]),([228,0,1,2,3,4,5,132],[17,51,209,290,291,508,570,815,817,1337,1338],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_8_1 : checkNodesBT W_17 g_17 F_17 P_17_8 A_17 B_17_7 8 N_17_8_1 = true := by decide +kernel
def N_17_8 := N_17_8_0 ++ N_17_8_1
def B_17_8 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_8
set_option maxRecDepth 500000 in
lemma B_17_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 8 xs.toFinset) B_17_8 := by
  have hP := buildPoolsSubBT_sound (pdepth := 11) (W := W_17) (raw := r_17) (pspecs := ps_17) (used := [0,5,13,15,17,25,26,43,47,51,55,62,67,75,77,79,82,84,87,88,90,93,97,98,99,114,118,129,130,135,142,144,148,156,157,159,162,167,178,179,184,186,195,196,208,209,215,224,247,253,259,260,261,262,263,264,268,275,276,277,279,280,281,284,285,287,289,290,291,292,294,296,297,300,302,303,305,307,308,309,311,314,317,321,322,323,324,326,328,329,332,336,338,340,342,344,346,347,349,356,357,358,359,361,363,364,366,367,369,374,375,383,385,386,387,390,391,393,396,398,400,402,406,409,416,417,418,421,423,424,425,427,430,431,434,435,441,442,446,447,448,449,452,453,454,455,464,469,477,478,479,481,482,485,486,487,488,490,493,494,499,505,506,507,508,514,515,516,518,520,521,522,524,530,531,532,533,534,535,540,543,544,546,548,549,550,552,553,554,555,556,558,559,560,562,565,566,569,570,571,576,578,587,592,599,600,605,607,608,616,618,620,624,626,629,630,631,632,638,639,641,645,646,650,651,652,653,654,655,656,657,658,659,660,661,662,663,664,665,666,667,668,669,670,671,672,673,674,675,676,677,678,679,680,681,682,683,684,685,686,687,688,689,690,691,692,693,694,695,696,697,698,699,700,701,702,703,704,705,706,707,708,709,710,711,712,713,714,715,716,717,718,719,720,721,722,723,724,725,726,727,728,729,730,731,732,733,734,735,736,737,738,739,740,741,742,743,744,745,746,747,748,749,750,751,752,753,754,755,756,757,758,759,760,761,762,763,764,765,766,767,768,769,770,771,772,773,774,775,776,777,778,779,780,781,782,783,784,785,786,787,788,789,790,791,792,793,794,795,796,797,798,799,800,801,802,803,804,805,806,807,808,809,810,811,812,813,814,815,816,817,818,819,820,821,822,823,824,825,826,827,828,829,830,831,832,833,834,835,836,837,838,839,840,841,842,843,844,845,846,847,848,849,850,851,852,853,854,855,856,857,858,859,860,861,862,863,864,865,866,867,868,869,870,871,872,873,874,875,876,877,878,879,880,881,882,883,884,885,886,887,888,889,890,891,892,893,894,895,896,897,898,899,900,901,902,903,904,905,906,907,908,909,910,911,912,913,914,915,916,917,918,919,920,921,922,923,924,925,926,927,928,929,930,931,932,933,934,935,936,937,938,939,940,941,942,943,944,945,946,947,948,949,950,951,952,953,954,955,956,957,958,959,960,961,962,963,964,965,966,967,968,969,970,971,972,973,974,975,976,977,978,979,980,981,982,983,984,985,986,987,988,989,990,991,992,993,994,995,996,997,998,999,1000,1001,1002,1003,1004,1005,1006,1007,1008,1009,1010,1011,1012,1013,1014,1015,1016,1017,1018,1019,1020,1021,1022,1023,1024,1025,1026,1027,1028,1029,1030,1031,1032,1033,1034,1035,1036,1037,1038,1039,1040,1041,1042,1043,1044,1045,1046,1047,1048,1049,1050,1051,1052,1053,1054,1055,1056,1057,1058,1059,1060,1061,1062,1063,1064,1065,1066,1067,1068,1069,1070,1071,1072,1073,1074,1075,1076,1077,1078,1079,1080,1081,1082,1083,1084,1085,1086,1087,1088,1089,1090,1091,1092,1093,1094,1095,1096,1097,1098,1099,1100,1101,1102,1103,1104,1105,1106,1107,1108,1109,1110,1111,1112,1113,1114,1115,1116,1117,1118,1119,1120,1121,1122,1123,1124,1125,1126,1127,1128,1129,1130,1131,1132,1133,1134,1135,1136,1137,1138,1139,1140,1141,1142,1143,1144,1145,1146,1147,1148,1149,1150,1151,1152,1153,1154,1155,1156,1157,1158,1159,1160,1161,1162,1163,1164,1165,1166,1167,1168,1169,1170,1171,1172,1173,1174,1175,1176,1177,1178,1179,1180,1181,1182,1183,1184,1185,1186,1187,1188,1189,1190,1191,1192,1193,1194,1195,1196,1197,1198,1199,1200,1201,1202,1203,1204,1205,1206,1207,1208,1209,1210,1211,1212,1213,1214,1215,1216,1217,1218,1219,1220,1221,1222,1223,1224,1225,1226,1227,1228,1229,1230,1231,1232,1233,1234,1235,1236,1237,1238,1239,1240,1241,1242,1243,1244,1245,1246,1247,1248,1249,1250,1251,1252,1253,1254,1255,1256,1257,1258,1259,1260,1261,1262,1263,1264,1265,1266,1267,1268,1269,1270,1271,1272,1273,1274,1275,1276,1277,1278,1279,1280,1281,1282,1283,1284,1285,1286,1287,1288,1289,1290,1291,1292,1293,1294,1295,1296,1297,1298,1299,1300,1301,1302,1303,1304,1305,1306,1307,1308,1309,1310,1311,1312,1313,1314,1315,1316,1317,1318,1319,1320,1321,1322,1323,1324,1325,1326,1327,1328,1329,1330,1331,1332,1333,1334,1335,1336,1337,1338]) S_17_ok
  have hm0 := checkNodesBT_mem (by decide) gp_17 W_17_ok hP A_17_ok B_17_7_ok C_17_8_0
  have hm1 := checkNodesBT_mem (by decide) gp_17 W_17_ok hP A_17_ok B_17_7_ok C_17_8_1
  exact buildBucketsBT_of_mem (forall_append (hm0) hm1)
def P_17_9 : BT (Option BoundPool) := buildPoolsSubBT 11 W_17 r_17 S_17 ps_17 [5,17,25,26,43,51,55,62,77,79,82,84,88,97,114,118,130,135,156,157,159,184,196,209,215,224,247,259,308,309,317,321,324,336,340,369,375,386,387,391,393,400,406,409,410,427,431,441,442,448,454,455,505,506,507,516,521,522,544,554,556,566,576,587,592,600,630,631,632,650,651,653,656,658,659,661,662,664,666,670,671,676,678,680,684,690,700,709,712,719,733,735,737,741,742,744,749,753,755,758,759,761,762,763,766,767,771,775,778,779,780,784,785,787,795,796,803,809,810,812,813,815,817,824,826,834,848,851,871,874,882,883,897,898,899,902,905,906,920,923,937,938,939,952,960,966,976,980,983,984,987,993,1000,1001,1003,1004,1010,1016,1018,1035,1038,1070,1076,1079,1085,1086,1090,1112,1126,1128,1133,1137,1151,1152,1171,1174,1178,1190,1192,1195,1196,1217,1234,1245,1246,1261,1291,1295,1318,1327,1339,1340,1341,1342,1343,1344,1345,1346,1347,1348,1349,1350,1351,1352,1353,1354,1355,1356,1357,1358,1359,1360,1361,1362,1363,1364,1365,1366,1367,1368,1369,1370,1371,1372,1373,1374,1375,1376,1377,1378,1379,1380,1381,1382,1383,1384,1385,1386,1387,1388,1389,1390,1391,1392,1393,1394,1395,1396,1397,1398,1399,1400,1401,1402,1403,1404,1405,1406,1407,1408,1409,1410,1411,1412,1413,1414,1415,1416,1417,1418,1419,1420,1421,1422,1423,1424,1425,1426,1427,1428,1429,1430,1431,1432,1433,1434,1435,1436,1437,1438,1439,1440,1441,1442,1443,1444,1445,1446,1447,1448,1449,1450,1451,1452,1453,1454,1455,1456,1457]
def N_17_9 : List NodeSpec := [([0,1,2,3,172,4,5],[17,88,135,159,209,247,259,522,653],[0,2]),([0,1,2,3,4,5,15],[17,88,135,159,209,224,247,259,656],[0,2]),([0,1,2,3,4,5,15,47],[84,88,135,369,375,427,431,516,521,671,680,749,1339],[0,1,2]),([0,1,2,22,4,15],[88,224,576],[0,1,2,3]),([0,1,2,3,4,5,15,132],[17,88,375,427,431,592,666,670,671],[0,1,2]),([327,0,1,2,4,5],[82,135,224,1340],[0,2]),([0,1,2,3,329,5],[88,135,224,787],[0,2]),([1,2,3,328,4,5],[88,224,1076],[0,2]),([114,0,1,2,4,5,15],[84,88,135,224,700,712],[0,1,2]),([192,1,2,3,4,5],[88,156,224,1178],[0,2]),([0,1,2,3,30,5,47],[84,88,630,749,834],[0,1,2,3]),([0,1,2,3,4,5,119],[82,84,97,159,209,224,247,259,813],[0,2]),([114,187,0,1,2,3,4,5],[259,309,554,712,809,826,905,1003,1004,1137,1341],[0,2]),([152,0,1,2,3,4,5,15],[17,51,84,135,209,224,375,427,431,544,658,659,664,671,676,771],[0,1,3]),([187,0,1,2,3,4,30,5],[309,796,817,1003,1004,1246,1342,1343,1344],[0,1,2]),([0,1,2,3,377,4,5],[17,135,159,247,259,308,309,826,1217],[0,1]),([0,1,2,28,30,5],[88,224,810,1345],[0,2]),([234,0,1,2,3,4,5,15],[17,84,135,159,224,375,427,671,733,753,771,1346],[1]),([234,0,1,2,3,4,30,5],[84,159,406,733,753,795,796,817,1246,1342,1344,1347],[0]),([288,0,1,2,3,4,5],[62,79,82,84,157,159,209,224,247,259,317,1348],[0,1,3]),([234,114,0,1,2,3,4,5],[84,159,224,406,554,556,733,735,753,809,905,1234,1349],[0]),([0,1,2,3,4,5,36,15],[17,84,135,224,247,375,427,431,709,1350,1351],[1]),([283,0,1,2,3,4,5,47],[5,51,84,159,369,516,678,680,1352],[0]),([0,1,2,3,4,30,5,36],[84,247,317,709,795,796,817,1344,1351,1353],[0]),([0,1,2,28,3,4,5,36],[84,97,135,196,247,709,1016,1018,1085,1086,1351,1354],[0,1]),([281,317,0,1,2,4],[88,135,224,966],[0,1,2]),([0,1,2,3,4,5,36,24],[84,135,209,247,259,387,1355],[]),([114,0,31,1,2,3,4,5],[159,247,336,400,554,556,712,784,809,1245,1291,1356,1357],[0]),([0,31,1,2,28,3,4,5],[97,196,324,340,400,784,1018,1245,1358,1359],[0]),([0,1,2,3,198,4,5],[17,135,209,247,259,336,400,874],[0,1,2]),([294,188,0,1,2,3,4,5],[159,758,759,803,1360,1361,1362],[0,2,3]),([234,294,0,1,2,3,4,5],[84,159,259,406,735,753,759,1070,1363],[0,1]),([0,1,2,3,4,5,430],[55,84,88,159,224,247,259,758,1364],[]),([162,171,0,1,2,3,4,5],[82,88,135,159,247,824,897,952,1010,1365,1366,1367,1368],[0]),([162,0,1,2,3,4,5,47],[62,82,88,135,159,369,516,678,680,824,952,1369],[0]),([162,187,0,1,2,3,4,5],[17,62,159,259,824,826,1003,1004,1010,1174,1370],[0,2]),([232,0,1,2,22,3,4,5],[159,209,247,441,631,632,1000,1001,1151,1371,1372],[0,1]),([114,0,71,1,2,3,4,5],[84,159,184,247,259,442,454,554,556,587,712,809,905,960,1373],[0]),([232,0,1,2,3,4,30,5],[43,84,159,247,441,631,795,817,1246,1342,1344,1374],[0,1]),([431,0,2,3,4,5],[88,135,247,1375],[]),([294,0,31,1,2,3,4,5],[159,247,259,336,400,758,1070,1245,1356,1376],[0,3]),([0,1,2,76,3,4,30,5],[84,224,506,650,796,817,1344,1377],[0,1]),([0,284,1,2,3,4,5,15],[5,17,51,84,135,224,321,375,427,431,544,661,662,671,690,771],[0,1,2]),([0,31,2,3,4,36],[135,159,755],[0,1,2,3]),([281,232,0,1,2,3,4,5],[84,135,159,247,259,441,631,632,937,938,939,976,1378,1379],[0]),([294,0,1,2,3,4,5,36],[84,209,247,317,759,1085,1351,1380,1381],[0,3]),([351,0,1,2,3,4,5],[5,62,79,135,157,159,224,259,506,1382],[0]),([281,0,71,1,2,3,4,5],[84,135,159,184,224,247,442,454,587,937,938,976,1379,1383],[0]),([232,0,1,2,28,3,4,5],[26,84,97,159,196,247,324,566,631,632,1018,1358,1384],[0]),([0,1,2,3,4,5,402],[62,84,159,209,247,259,1192,1385],[0,1,2,3]),([171,0,1,2,76,3,4,5],[17,62,82,135,505,506,522,600,650,651,898,1368,1386],[0,1]),([0,1,2,3,4,5,356],[82,84,224,247,259,1387],[0,1]),([0,1,2,76,3,4,5,15],[17,84,224,427,431,506,544,650,651,1388],[0,1]),([0,1,2,3,334,4,5],[17,79,88,135,209,247,259,1171,1174],[0,2]),([0,1,2,3,4,5,149],[82,84,209,224,247,1389,1390,1391],[0,1]),([281,0,1,2,76,3,4,5],[84,135,224,505,506,650,651,938,976,1392],[0,1]),([0,1,2,76,22,3,4,5],[135,209,247,506,650,651,1000,1152,1393,1394],[0,1]),([114,0,1,2,76,3,4,5],[84,159,259,505,506,650,651,712,809,905,993,1395],[0,1]),([171,0,1,2,3,4,43,5],[88,247,897,898,980,983,984,1079,1368,1396],[1]),([162,295,0,1,2,3,4,5],[62,82,88,159,209,259,761,824,952,1397,1398],[]),([0,71,1,2,22,3,4,5],[159,184,247,259,454,587,1000,1151,1152,1371,1399],[0,1]),([0,1,3,432,4,5],[88,135,224,259,1400],[]),([0,1,2,3,346,4,5],[17,135,247,259,308,441,632,1401],[0]),([0,71,76,3,4,5],[118,159,209,215],[0,1]),([162,0,1,2,3,4,7,5],[62,82,88,159,209,775,824,871,1402],[]),([162,0,1,2,3,4,5,15],[84,88,135,375,427,544,671,771,824,952,1010,1403],[0,3]),([359,0,1,2,3,4,5],[5,82,84,114,157,159,224,259,1404],[0,1]),([0,71,1,2,28,3,4,5],[84,97,196,224,247,324,454,455,587,1016,1018,1358,1405],[0]),([187,0,1,2,28,3,4,5],[97,324,826,987,1003,1004,1016,1018,1358,1406],[0,2]),([0,71,1,2,3,4,30,5],[84,184,224,247,454,587,795,796,817,1246,1342,1344,1407],[0,1]),([0,71,1,2,3,4,5,15],[17,84,135,159,184,224,259,375,427,431,454,544,587,671,771,1408],[0,1,2]),([1,260,2,3,4,5],[88,156,224,247,1409],[0,2]),([114,232,0,1,2,3,4,5],[25,84,159,209,247,259,441,554,556,631,632,712,809,812,1410],[0]),([171,0,71,1,2,3,4,5],[17,62,82,135,159,184,247,442,454,522,587,897,898,1367,1368,1411],[0,1]),([114,0,1,2,3,4,5,36],[84,159,247,317,556,709,809,905,1085,1295,1351,1380,1412],[0,1]),([0,1,2,76,28,3,4,5],[82,84,97,209,247,600,650,651,1016,1018,1413],[0]),([234,0,1,2,3,64,4,5],[17,84,224,247,733,735,753,766,767,1038,1133,1414,1415],[0,1,2]),([281,0,1,2,3,4,5,36],[135,247,317,709,937,938,976,1085,1351,1380,1416],[0]),([0,1,2,3,4,5,348],[84,88,209,224,247,259,393,719],[0,2]),([129,0,1,2,3,4,5,15],[62,82,84,88,135,224,375,427,431,671,771,1417],[0,2]),([0,37,2,38,4,5],[88,159,224,1126],[0,2,3]),([234,0,1,63,2,3,4,5],[84,159,209,224,259,406,733,735,778,779,785,1418,1419],[0,2]),([187,0,37,1,2,3,4,5],[159,247,259,309,393,826,1003,1090,1409,1420],[0,2]),([0,37,1,23,2,3,4,5],[130,209,259,393,409,882,1195,1421,1422],[0,2]),([234,0,2,3,38,4,5],[17,84,135,159,224,247,406,735,1423],[0]),([162,317,0,1,2,3,4,5],[88,135,159,824,952,1010,1261,1424,1425,1426],[1]),([232,0,1,2,3,4,5,15],[17,84,209,224,375,427,431,441,544,631,632,671,771,1327,1427],[0,1,2]),([0,1,2,3,38,64,4,5],[17,88,209,224,247,386,767,1415,1428],[]),([0,1,2,3,4,5,15,183],[17,77,84,88,247,375,427,431,507,684],[0,1,2]),([234,0,1,2,28,3,4,5],[84,97,159,196,324,733,735,753,1016,1018,1318,1358,1429],[0]),([0,1,2,3,382,4,5],[17,82,84,159,209,224,247,259,735,1430],[0,1,2]),([171,232,0,1,2,3,4,5],[17,62,82,159,247,259,441,522,631,632,897,898,899,1367,1368,1431],[0,1]),([0,1,2,3,213,4,5],[17,135,184,209,247,454,906,1432,1433],[0,1]),([0,1,2,3,38,4,5,24],[17,84,135,386,387,741,744,920,1434,1435],[0,2]),([0,1,2,3,4,5,132],[84,88,159,209,247,259,448,815,817],[0,1,2]),([234,188,0,2,3,4],[159,247,780],[0,1,2]),([171,0,1,2,3,38,4,5],[88,247,386,897,898,920,923,1368,1436,1437],[0,1]),([0,31,1,2,3,64,4,5],[17,62,159,209,224,259,340,766,1038,1133,1245,1415,1438],[0,1,2]),([162,207,0,2,3,5],[88,159,247,1196],[0,2]),([0,1,2,3,38,4,7,5],[88,209,247,386,391,923,1035,1439],[0,3]),([162,0,1,2,3,64,4,5],[88,159,224,247,766,824,1010,1038,1133,1174,1415,1440],[0,2,3]),([187,0,1,2,3,38,4,5],[17,62,209,247,386,987,1004,1435,1436,1441],[0,1,2]),([162,310,0,1,2,3,4,5],[88,209,952,1010,1190,1442,1443],[0,1,3]),([0,1,2,3,38,4,5,15],[17,88,135,224,247,375,386,427,431,920,1444],[0]),([234,281,0,1,2,3,4,5],[135,159,224,247,406,733,735,753,937,976,1379,1445,1446],[0]),([0,31,1,2,3,4,30,5],[336,784,795,817,1245,1246,1342,1344,1447],[0,1]),([300,0,1,2,3,4,5],[62,79,88,135,157,159,209,224,259,1448],[0,2]),([129,0,1,2,3,4,5],[62,84,88,135,157,159,209,224,247,259,1417],[0,2]),([234,0,1,2,3,4,5,24],[84,135,159,209,744,753,1128,1449],[]),([363,0,1,2,3,4,5],[17,82,84,114,157,159,209,224,247,259,1450],[0,1]),([0,1,2,3,38,4,5,47],[84,88,369,386,516,521,920,923,1451],[0,1,3]),([234,365,0,1,2,3,4,5],[84,135,159,209,259,733,753,883,1452,1453],[]),([162,0,2,3,4,5,36],[62,84,135,159,247,317,1112],[0,2,3]),([0,37,1,2,3,4,5,24],[84,135,159,209,259,737,741,742,744,1090,1128],[0,3]),([162,0,1,23,2,3,4,5],[17,62,135,159,209,259,409,410,902,952,1010,1174,1195,1421,1454],[0,2]),([0,1,2,3,4,5,309],[62,84,88,159,209,224,247,259,712,848,851],[0,2]),([162,0,1,2,3,4,5,24],[62,84,135,387,741,742,744,824,952,1128,1455,1456],[0,3]),([234,295,0,1,2,3,4,5],[62,82,84,135,209,733,735,753,761,762,763,1457],[0,2])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_9 : checkNodesBT W_17 g_17 F_17 P_17_9 A_17 B_17_8 9 N_17_9 = true := by decide +kernel
def B_17_9 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_9
set_option maxRecDepth 500000 in
lemma B_17_9_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 9 xs.toFinset) B_17_9 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_8_ok C_17_9
def P_17_10 : BT (Option BoundPool) := buildPoolsSubBT 11 W_17 r_17 S_17 ps_17 [82,88,118,135,157,159,209,224,247,259,440,442,505,771,1342,1345,1356,1358,1365,1371,1380,1409,1436,1445,1458,1459,1460,1461,1462]
def N_17_10 : List NodeSpec := [([171,0,1,2,3,4,5],[88,135,157,159,209,224,247,259,1365],[0,1,2,3]),([281,0,1,2,3,4,5],[88,135,157,159,209,224,247,259,1445],[0,2]),([0,1,2,3,4,5,15],[88,135,159,209,224,247,259,771],[0,1,2,3]),([0,1,2,22,3,4,5],[88,135,159,209,224,247,259,1371],[0,1,2,3]),([114,0,1,2,3,4,5],[88,135,157,159,209,224,247,259,1345,1458],[0,2]),([0,71,1,2,3,4,5],[82,135,157,159,209,224,247,259,442],[0,1]),([232,0,1,2,3,4,5],[82,118,135,157,209,224,247,259,440],[0,1]),([0,1,2,3,38,4,5],[88,135,159,209,224,247,259,1436],[0,1,2,3]),([0,37,1,2,3,4,5],[88,135,157,209,224,247,259,1409],[0,2]),([234,0,1,2,3,4,5],[82,135,157,159,209,224,247,259,1459],[0,1]),([162,0,1,2,3,4,5],[82,88,135,157,159,209,224,247,259,1460],[0,2]),([187,0,1,2,3,4,5],[82,135,157,159,224,247,259,1461],[0,1,2,3]),([0,1,2,76,3,4,5],[82,135,159,224,259,505],[0,1]),([0,1,2,28,3,4,5],[82,135,159,209,224,247,259,1358],[0,2]),([294,0,1,2,3,4,5],[88,135,157,159,224,247,259,1462],[0,3]),([0,31,1,2,3,4,5],[82,135,157,209,224,247,259,1356],[0,1,2,3]),([0,1,2,3,4,30,5],[88,135,159,209,224,247,259,1342],[0,1,2]),([0,1,2,3,4,5,36],[82,135,159,209,224,247,259,1380],[0,1,2,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_10 : checkNodesBT W_17 g_17 F_17 P_17_10 A_17 B_17_9 10 N_17_10 = true := by decide +kernel
def B_17_10 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_10
set_option maxRecDepth 500000 in
lemma B_17_10_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 10 xs.toFinset) B_17_10 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_9_ok C_17_10
def P_17_11 : BT (Option BoundPool) := buildPoolsSubBT 11 W_17 r_17 S_17 ps_17 [157]
def N_17_11 : List NodeSpec := [([0,1,2,3,4,5],[157],[0,1,2,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_11 : checkNodesBT W_17 g_17 F_17 P_17_11 A_17 B_17_10 11 N_17_11 = true := by decide +kernel
def B_17_11 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_11
set_option maxRecDepth 500000 in
lemma B_17_11_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 11 xs.toFinset) B_17_11 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_10_ok C_17_11
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_17_ok : forestRootCheck r_17 g_17 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,6,14),(VAR 4,6,22),(VAR 5,3,35)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_17_in : bucketContainsBT B_17_11 r_17 = true := by decide +kernel
lemma low_17 : Lower r_17 g_17 12 := lower_of_forestBT root_17_ok B_17_11_ok root_17_in

def g_orig := 0xfeeefaa8fee8eaa0feeefaa8fee8eaa0feeefaa8fee8eaa0feeefaa8fee8eaa0
set_option maxHeartbeats 0 in
lemma low_orig : Lower (varsOf 63) g_orig 12 := carry_of (swaps := [(0,5),(2,3),(3,4)]) (by decide +kernel) low_17
def targetFn (x : Fin 6 → Bool) : Bool := Nat.testBit (4277074600 * 2 ^ 32 + 4276677280) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def temoin : List Gate := [⟨.or,[2,3]⟩,⟨.and,[2,3]⟩,⟨.and,[4,1]⟩,⟨.and,[8,0]⟩,⟨.or,[4,1]⟩,⟨.or,[8,7]⟩,⟨.or,[5,10]⟩,⟨.and,[12,11]⟩,⟨.or,[9,5]⟩,⟨.or,[0,13]⟩,⟨.and,[14,10]⟩,⟨.or,[6,16]⟩,⟨.and,[17,15]⟩]
lemma temoin_ok : PEqualNP.MetaComplexity.Monotone2 ⟨temoin, 18⟩ := by
  intro g hg; simp [temoin] at hg; rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxHeartbeats 0 in
lemma tgt_eq_G : ∀ r : Row, targetFn (evalInput6 r) = g_orig.testBit r.val := by decide +kernel
set_option maxHeartbeats 0 in
lemma temoin_eval : ∀ r : Row, Circuit.eval ⟨temoin, 18⟩ (List.ofFn (evalInput6 r)) = g_orig.testBit r.val := by decide +kernel

end PEqualNP.Outside.L_meta_44826

open PEqualNP.Outside.L_meta_44826 in
theorem PEqualNP.Outside.L_meta_44826 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074600 * 2 ^ 32 + 4276677280) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074600 * 2 ^ 32 + 4276677280) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  exact replace_of_lower6 g_orig (by decide) (by decide) (by decide) 12 low_orig temoin 18 (by decide) temoin_ok targetFn tgt_eq_G temoin_eval
