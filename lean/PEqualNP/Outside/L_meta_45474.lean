import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_45474
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
def g_2 := (d 0xfe80fe80fe80fe80)
def r_2 : List Nat := varsOf 15
def p_2 : List Nat := [7,7,7,9,9,10,10,11,12,12,13,14]
def q_2 : List Nat := [6,5,3,8,1,8,2,3,8,4,5,6]
def F_2 : Nat := fullMask 12
set_option maxHeartbeats 0 in
lemma gp_2 : goodPairs g_2 p_2 q_2 := goodPairs_of (by decide +kernel)
def W_2 : BT Decor := buildWiresBT 5 (mkBase p_2 q_2 r_2) [(0,2,3),(1,2,3),(3,4,5),(0,1,2),(1,1,2),(3,7,8),(2,0,3),(3,0,3),(1,0,3),(3,2,12),(1,1,3),(0,0,14),(0,0,3),(1,16,2),(3,4,0),(2,0,2),(3,0,2),(2,2,1),(3,21,0),(2,0,1),(1,23,2),(0,0,1),(1,0,1),(3,2,3)]
lemma W_2_ok : btAll (fun x => faithful p_2 q_2 x ∧ x.1 < 2^256) W_2 := buildWiresBT_faithful (mkBase_ok (by decide))
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
def N_2_3 : List NodeSpec := [([10,11,1,2],[],[3]),([13,0,1,3],[],[]),([15,1,2,3],[],[]),([16,1,2,12],[],[3]),([0,1,17,3],[],[]),([18,1,2,3],[],[]),([19,20,1,3],[],[2]),([22,1,2,3],[],[]),([0,1,24,3],[],[]),([25,26,2,3],[],[4])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_2_3 : checkNodesBT W_2 g_2 F_2 P_2_3 A_2 B_2_2 3 N_2_3 = true := by decide +kernel
def B_2_3 : BT (List (List Nat)) := buildBucketsBT W_2 N_2_3
set_option maxRecDepth 500000 in
lemma B_2_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_2 3 xs.toFinset) B_2_3 :=
  buildBucketsBT_sound (by decide) gp_2 W_2_ok (buildPoolsSubBT_sound S_2_ok) A_2_ok B_2_2_ok C_2_3
def U_2_4 : List Nat := []
def P_2_4 : BT (Option BoundPool) := buildPoolsSubBT 1 W_2 r_2 S_2 ps_2 U_2_4
def N_2_4 : List NodeSpec := [([27,0,1,2,3],[],[4]),([10,0,1,2,3],[],[0]),([0,1,2,3,12],[],[0,1,2,4]),([16,0,1,2,3],[],[0,1,3,5]),([19,0,1,2,3],[],[0,1,3]),([0,1,26,2,3],[],[0]),([25,0,1,2,3],[],[0])]
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
def g_3 := (d 0xffe8ffe8ffe8ffe8)
def r_3 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_3 : Lower r_3 g_3 5 := by
  exact lift_of_f (z := 8) (o := 0) (other := r_0) (G := g_0) (essPairs := [(VAR 3,0,8)]) (by decide +kernel) low_0
def g_4 := (d 0xfffee880fffee880)
def r_4 : List Nat := varsOf 31
def p_4 : List Nat := [7,7,7,11,11,11,13,13,13,14,14,14,17,17,18,18,19,20,20,21,22,24,24,25,26,28]
def q_4 : List Nat := [6,5,3,10,9,3,12,9,5,12,10,6,16,1,16,2,3,16,4,5,6,16,8,9,10,12]
def F_4 : Nat := fullMask 26
set_option maxHeartbeats 0 in
lemma gp_4 : goodPairs g_4 p_4 q_4 := goodPairs_of (by decide +kernel)
def W_4 : BT Decor := buildWiresBT 3 (mkBase p_4 q_4 r_4) [(1,0,1),(1,2,3),(0,5,6)]
lemma W_4_ok : btAll (fun x => faithful p_4 q_4 x ∧ x.1 < 2^256) W_4 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_4 : List (List (Nat × Nat)) := [[],[(1,2)],[(1,2),(2,3)],[(0,2),(1,2)],[(0,2),(1,2),(2,3)],[(0,2),(1,3)]]
def A_4 : BT (List (Nat × Nat)) := btOfList 3 al_4
set_option maxHeartbeats 0 in
lemma A_4_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_4 = g_4) A_4 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_4_0 : Slice r_4 g_4 (subcubeFast 16 0) 7 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_1
set_option maxHeartbeats 0 in
lemma sl_4_1 : Slice r_4 g_4 (subcubeFast 2 0) 6 := by
  have hc : Lower (varsOf 29) (d 0xfffaa000fffaa000) 6 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_4_2 : Slice r_4 g_4 (subcubeFast 4 0) 6 := by
  have hc : Lower (varsOf 27) (d 0xffee8800ffee8800) 6 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_4_3 : Slice r_4 g_4 (subcubeFast 8 0) 6 := by
  have hc : Lower (varsOf 23) (d 0xfefe8080fefe8080) 6 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_4_4 : Slice r_4 g_4 (subcubeFast 1 0) 6 := by
  have hc : Lower (varsOf 30) (d 0xfffcc000fffcc000) 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_4_5 : Slice r_4 g_4 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) (d 0xfffffcc0fffffcc0) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_4_6 : Slice r_4 g_4 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) (d 0xfffffaa0fffffaa0) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_4_7 : Slice r_4 g_4 (subcubeFast 0 4) 5 := by
  have hc : Lower (varsOf 27) (d 0xffffee88ffffee88) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_4_8 : Slice r_4 g_4 (subcubeFast 0 8) 5 := by
  have hc : Lower (varsOf 23) (d 0xffffe8e8ffffe8e8) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
def S_4 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 16 0,7),some (subcubeFast 2 0,6),some (subcubeFast 4 0,6),some (subcubeFast 8 0,6),some (subcubeFast 1 0,6),some (subcubeFast 0 1,5),some (subcubeFast 0 2,5),some (subcubeFast 0 4,5),some (subcubeFast 0 8,5)]
lemma S_4_ok : btAll (fun o => ∀ p, o = some p → Slice r_4 g_4 p.1 p.2) S_4 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_4_0) (forall_cons (fun _ h => by cases h; exact sl_4_1) (forall_cons (fun _ h => by cases h; exact sl_4_2) (forall_cons (fun _ h => by cases h; exact sl_4_3) (forall_cons (fun _ h => by cases h; exact sl_4_4) (forall_cons (fun _ h => by cases h; exact sl_4_5) (forall_cons (fun _ h => by cases h; exact sl_4_6) (forall_cons (fun _ h => by cases h; exact sl_4_7) (forall_cons (fun _ h => by cases h; exact sl_4_8) (fun _ h => (List.not_mem_nil h).elim))))))))))
def ps_4 : BT (Option PoolSpec) := btOfList 4 [q 1 [12297],q 4 [],q 5 [],q 6 [],q 2 [],q 7 [],q 3 [],q 8 [],q 2 [4097],q 1 [],q 0 [4097],q 3 [4097],q 0 []]
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
def U_4_6 : List Nat := (r 0 9)
def P_4_6 : BT (Option BoundPool) := buildPoolsSubBT 4 W_4 r_4 S_4 ps_4 U_4_6
def N_4_6 : List NodeSpec := [u5 [5,6] (r 0 9)]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_4_6 : checkNodesBT W_4 g_4 F_4 P_4_6 A_4 B_4_5 6 N_4_6 = true := by decide +kernel
def B_4_6 : BT (List (List Nat)) := buildBucketsBT W_4 N_4_6
set_option maxRecDepth 500000 in
lemma B_4_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_4 6 xs.toFinset) B_4_6 :=
  buildBucketsBT_sound (by decide) gp_4 W_4_ok (buildPoolsSubBT_sound S_4_ok) A_4_ok B_4_5_ok C_4_6
def U_4_7 : List Nat := ([1,2]++r 4 8)
def P_4_7 : BT (Option BoundPool) := buildPoolsSubBT 4 W_4 r_4 S_4 ps_4 U_4_7
def N_4_7 : List NodeSpec := [u5 [5] ([1,2]++r 4 8)]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_4_7 : checkNodesBT W_4 g_4 F_4 P_4_7 A_4 B_4_6 7 N_4_7 = true := by decide +kernel
def B_4_7 : BT (List (List Nat)) := buildBucketsBT W_4 N_4_7
set_option maxRecDepth 500000 in
lemma B_4_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_4 7 xs.toFinset) B_4_7 :=
  buildBucketsBT_sound (by decide) gp_4 W_4_ok (buildPoolsSubBT_sound S_4_ok) A_4_ok B_4_6_ok C_4_7
def U_4_8 : List Nat := [1,4,6,9,12]
def P_4_8 : BT (Option BoundPool) := buildPoolsSubBT 4 W_4 r_4 S_4 ps_4 U_4_8
def N_4_8 : List NodeSpec := [a5 [] [1,4,6,9,12] [0,1,2,3,4,5]]
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
def g_5 := (d 0xe800e800e800e800)
def r_5 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_5 : Lower r_5 g_5 5 := by
  exact lift_of_f (z := 0) (o := 8) (other := r_0) (G := g_0) (essPairs := [(VAR 3,3,11)]) (by decide +kernel) low_0
def g_6 := (d 0xfec0fec0fec0fec0)
def r_6 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_6 : Lower r_6 g_6 5 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,8,9)]) (by decide +kernel) hc
def g_7 := (d 0xfee0fee0fee0fee0)
def r_7 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_7 : Lower r_7 g_7 5 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,4,5)]) (by decide +kernel) hc
def g_8 := (d 0xf880f880f880f880)
def r_8 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_8 : Lower r_8 g_8 5 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,6,7)]) (by decide +kernel) hc
def g_9 := (d 0xfc80fc80fc80fc80)
def r_9 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_9 : Lower r_9 g_9 5 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,6,7)]) (by decide +kernel) hc
def g_10 := (d 0xfac0fac0fac0fac0)
def r_10 : List Nat := varsOf 15
def p_10 : List Nat := [6,6,7,7,9,9,11,11,12,12,13,14]
def q_10 : List Nat := [4,2,5,3,8,1,10,3,8,4,5,10]
def F_10 : Nat := fullMask 12
set_option maxHeartbeats 0 in
lemma gp_10 : goodPairs g_10 p_10 q_10 := goodPairs_of (by decide +kernel)
def W_10 : BT Decor := buildWiresBT 2 (mkBase p_10 q_10 r_10) []
lemma W_10_ok : btAll (fun x => faithful p_10 q_10 x ∧ x.1 < 2^256) W_10 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_10 : List (List (Nat × Nat)) := [[]]
def A_10 : BT (List (Nat × Nat)) := btOfList 1 al_10
set_option maxHeartbeats 0 in
lemma A_10_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_10 = g_10) A_10 := btAll_ofList (autos_of (by decide +kernel))
def S_10 : BT (Option (Nat × Nat)) := btOfList 1 []
lemma S_10_ok : btAll (fun o => ∀ p, o = some p → Slice r_10 g_10 p.1 p.2) S_10 := btAll_ofList (fun _ h => (List.not_mem_nil h).elim)
def ps_10 : BT (Option PoolSpec) := btOfList 1 []
def B_10_2 : BT (List (List Nat)) := BT.empty
lemma B_10_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_10 2 xs.toFinset) B_10_2 := .empty
def U_10_3 : List Nat := []
def P_10_3 : BT (Option BoundPool) := buildPoolsSubBT 1 W_10 r_10 S_10 ps_10 U_10_3
def N_10_3 : List NodeSpec := [([0,1,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_10_3 : checkNodesBT W_10 g_10 F_10 P_10_3 A_10 B_10_2 3 N_10_3 = true := by decide +kernel
def B_10_3 : BT (List (List Nat)) := buildBucketsBT W_10 N_10_3
set_option maxRecDepth 500000 in
lemma B_10_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_10 3 xs.toFinset) B_10_3 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok (buildPoolsSubBT_sound S_10_ok) A_10_ok B_10_2_ok C_10_3
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_10_ok : forestRootCheck r_10 g_10 [(VAR 0,8,9),(VAR 1,4,6),(VAR 2,2,6),(VAR 3,1,9)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_10_in : bucketContainsBT B_10_3 r_10 = true := by decide +kernel
lemma low_10 : Lower r_10 g_10 4 := lower_of_forestBT root_10_ok B_10_3_ok root_10_in
def g_11 := (d 0xfea8c000fea8c000)
def r_11 : List Nat := varsOf 31
def p_11 : List Nat := [14,14,14,15,15,15,19,19,19,21,21,21,23,23,25,25,25,26,26,26,27,28,28,28,29,30]
def q_11 : List Nat := [12,10,6,13,11,7,18,17,3,20,17,5,22,7,24,17,9,24,18,10,11,24,20,12,13,22]
def F_11 : Nat := fullMask 26
set_option maxHeartbeats 0 in
lemma gp_11 : goodPairs g_11 p_11 q_11 := goodPairs_of (by decide +kernel)
def W_11 : BT Decor := buildWiresBT 8 (mkBase p_11 q_11 r_11) [(0,0,4),(1,1,2),(0,6,3),(1,5,7),(0,3,4),(0,2,4),(1,1,10),(2,11,3),(3,2,3),(0,11,3),(2,6,3),(0,1,2),(3,16,3),(0,0,3),(3,18,6),(1,2,4),(3,10,20),(1,0,7),(0,22,4),(2,0,3),(1,24,1),(0,1,4),(1,26,2),(2,6,9),(0,7,4),(0,27,3),(2,0,30),(1,5,2),(0,6,4),(1,5,1),(1,34,2),(0,35,3),(3,0,4),(1,37,7),(1,24,16),(3,6,3),(3,40,4),(2,0,7),(3,33,3),(1,3,4),(3,9,44),(0,3,20),(2,0,46),(1,1,4),(0,3,48),(0,0,49),(1,1,3),(3,2,51),(1,2,3),(3,1,53),(3,54,4),(0,1,3),(1,13,1),(0,2,3),(1,58,1),(3,6,4),(3,60,3),(1,13,10),(0,57,4),(3,7,4),(3,3,4),(3,65,6),(3,1,3),(3,58,6),(3,10,51),(0,0,6),(2,2,1),(1,71,13),(3,67,4),(2,34,2),(3,24,6),(0,25,4),(2,0,2),(1,77,26),(3,2,48),(0,1,20),(3,18,48),(2,1,2),(1,82,18),(1,18,26),(3,10,1),(1,77,1),(0,86,4),(1,18,1),(0,88,4),(2,1,4),(1,24,82),(1,18,2),(1,90,18),(1,18,16),(1,24,26),(3,24,48),(0,53,4),(1,90,24),(3,1,4),(0,0,11),(3,5,6),(1,13,26),(1,1,9),(3,2,9),(2,3,4),(3,105,0),(3,2,44),(0,0,44),(1,65,1),(3,2,4),(2,2,4),(3,111,0),(3,13,4),(3,111,3),(2,2,3),(1,115,1),(0,51,4),(2,0,1),(3,118,4),(0,1,44),(3,18,4),(2,0,58),(3,24,4),(3,13,1),(0,0,2),(1,125,1),(2,1,3),(1,127,2),(3,3,48),(3,115,1),(3,10,3),(0,0,48),(3,71,3),(0,0,1),(2,0,4)]
lemma W_11_ok : btAll (fun x => faithful p_11 q_11 x ∧ x.1 < 2^256) W_11 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_11 : List (List (Nat × Nat)) := [[],[(1,2)]]
def A_11 : BT (List (Nat × Nat)) := btOfList 1 al_11
set_option maxHeartbeats 0 in
lemma A_11_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_11 = g_11) A_11 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_11_0 : Slice r_11 g_11 (subcubeFast 0 1) 6 := by
  have hc : Lower (varsOf 30) (d 0xfffcc000fffcc000) 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_1 : Slice r_11 g_11 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) (d 0xfaa00000faa00000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_2 : Slice r_11 g_11 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) (d 0xfc00c000fc00c000) 5 := carry_of (swaps := [(0,4),(1,4),(2,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_3 : Slice r_11 g_11 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) (d 0xee880000ee880000) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_4 : Slice r_11 g_11 (subcubeFast 0 8) 5 := by
  have hc : Lower (varsOf 23) (d 0xfefec0c0fefec0c0) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_5 : Slice r_11 g_11 (subcubeFast 0 16) 5 := by
  have hc : Lower (varsOf 15) (d 0xfea8fea8fea8fea8) 5 := carry_of (swaps := [(0,2),(1,2)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 0) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_6 : Slice r_11 g_11 (subcubeFast 4 16) 4 := by
  have hc : Lower (varsOf 11) (d 0xee88ee88ee88ee88) 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_7 : Slice r_11 g_11 (subcubeFast 2 16) 4 := by
  have hc : Lower (varsOf 13) (d 0xfaa0faa0faa0faa0) 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 2) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_8 : Slice r_11 g_11 (subcubeFast 1 8) 4 := by
  have hc : Lower (varsOf 22) (d 0xfcfcc0c0fcfcc0c0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_9 : Slice r_11 g_11 (identDom 1 2) 5 := by
  have hc : Lower (varsOf 27) (d 0xee88cc00ee88cc00) 5 := carry_of (swaps := [(1,2),(2,4)]) (by decide +kernel) low_8
  exact slice_ident (u := 1) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_10 : Slice r_11 g_11 (identDom 1 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xececc0c0ececc0c0) 5 := carry_of (swaps := [(1,3),(2,3),(3,4)]) (by decide +kernel) low_9
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_11 : Slice r_11 g_11 (identDom 2 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xf8f8c0c0f8f8c0c0) 5 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_9
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_12 : Slice r_11 g_11 (subcubeFast 0 4) 4 := by
  have hc : Lower (varsOf 27) (d 0xffaacc00ffaacc00) 4 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_10
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_11_13 : Slice r_11 g_11 (subcubeFast 0 2) 4 := by
  have hc : Lower (varsOf 29) (d 0xffaaf000ffaaf000) 4 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_10
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
def S_11 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 0 1,6),some (subcubeFast 2 0,5),some (subcubeFast 1 0,5),some (subcubeFast 4 0,5),some (subcubeFast 0 8,5),some (subcubeFast 0 16,5),some (subcubeFast 4 16,4),some (subcubeFast 2 16,4),some (subcubeFast 1 8,4),some (identDom 1 2,5),some (identDom 1 3,5),some (identDom 2 3,5),some (subcubeFast 0 4,4),some (subcubeFast 0 2,4)]
lemma S_11_ok : btAll (fun o => ∀ p, o = some p → Slice r_11 g_11 p.1 p.2) S_11 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_11_0) (forall_cons (fun _ h => by cases h; exact sl_11_1) (forall_cons (fun _ h => by cases h; exact sl_11_2) (forall_cons (fun _ h => by cases h; exact sl_11_3) (forall_cons (fun _ h => by cases h; exact sl_11_4) (forall_cons (fun _ h => by cases h; exact sl_11_5) (forall_cons (fun _ h => by cases h; exact sl_11_6) (forall_cons (fun _ h => by cases h; exact sl_11_7) (forall_cons (fun _ h => by cases h; exact sl_11_8) (forall_cons (fun _ h => by cases h; exact sl_11_9) (forall_cons (fun _ h => by cases h; exact sl_11_10) (forall_cons (fun _ h => by cases h; exact sl_11_11) (forall_cons (fun _ h => by cases h; exact sl_11_12) (forall_cons (fun _ h => by cases h; exact sl_11_13) (fun _ h => (List.not_mem_nil h).elim)))))))))))))))
def ps_11 : BT (Option PoolSpec) := btOfList 7 [q 0 [16392,16393,81963],q 0 [],q 1 [16384,16408],q 9 [12312,28674],q 8 [],q 7 [],q 6 [],q 0 [16393,81932],q 10 [],q 1 [196620],q 0 [16389,196620],q 2 [],q 3 [],q 1 [16392],q 5 [],q 13 [],q 1 [],q 0 [12299,4149],q 0 [16388,8297],q 3 [16388],q 12 [],q 4 [],q 11 [],q 9 [],q 9 [12314],q 0 [8196,8197],q 9 [12312],q 9 [24576],q 1 [16408],q 5 [4105],q 5 [8197],q 9 [12290],q 0 [16388,16389],q 0 [16388,106805],q 0 [16389,196619],q 3 [81924],q 0 [16393,81924],q 0 [16389,196683],q 0 [8198,74057],q 0 [16388,106569],q 0 [16392,4139],q 9 [12288],q 0 [16389,196707],q 0 [16390,16391],q 0 [16392,4137],q 1 [16384],q 4 [16384],q 1 [16387],q 4 [16387],q 0 [16396,36869],q 1 [16395],q 3 [16439],q 2 [12299],q 0 [16389],q 0 [12299],q 0 [16396],q 3 [16384],q 1 [16859],q 0 [16859],q 0 [8196],q 2 [16396],q 0 [16390],q 0 [16388],q 0 [8197],q 0 [16459],q 0 [16483],q 0 [12296],q 0 [12292],q 0 [16391],q 0 [8198],q 0 [4169],q 0 [4117],q 0 [16395],q 0 [16399],q 3 [16387],q 0 [12293],q 0 [4597],q 2 [12295],q 1 [196619],q 1 [196623],q 0 [16389,196623],q 2 [12292],q 0 [16392,12331],q 0 [4193],q 1 [196608],q 0 [4106,12575],q 0 [4405]]
def B_11_2 : BT (List (List Nat)) := BT.empty
lemma B_11_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_11 2 xs.toFinset) B_11_2 := .empty
def U_11_3 : List Nat := []
def P_11_3 : BT (Option BoundPool) := buildPoolsSubBT 7 W_11 r_11 S_11 ps_11 U_11_3
def N_11_3 : List NodeSpec := [([1,2,8,9],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_11_3 : checkNodesBT W_11 g_11 F_11 P_11_3 A_11 B_11_2 3 N_11_3 = true := by decide +kernel
def B_11_3 : BT (List (List Nat)) := buildBucketsBT W_11 N_11_3
set_option maxRecDepth 500000 in
lemma B_11_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_11 3 xs.toFinset) B_11_3 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok (buildPoolsSubBT_sound S_11_ok) A_11_ok B_11_2_ok C_11_3
def U_11_4 : List Nat := (r 0 4)
def P_11_4 : BT (Option BoundPool) := buildPoolsSubBT 7 W_11 r_11 S_11 ps_11 U_11_4
def N_11_4 : List NodeSpec := [([12,13,0,11,4],[],[]),([13,0,14,11,4],[],[]),([15,17,0,6,4],[],[]),([19,0,16,3,4],[],[]),([21,18,0,1,3],[0],[]),([1,2,7,23,3],[],[]),([0,25,27,3,4],[],[]),([28,5,1,2,3],[],[]),([5,1,2,29,3],[1],[]),([31,1,27,3,4],[],[]),([17,0,7,6,4],[],[]),([5,1,32,33,3],[2],[]),([24,21,0,1,3],[0],[]),([5,1,2,36,4],[],[]),([1,2,38,3,4],[],[]),([0,39,6,3,4],[],[]),([13,5,1,33,3],[2],[]),([1,2,8,3,4],[1],[0]),([5,1,2,7,9],[],[0]),([5,1,2,41,3],[],[]),([42,16,6,3,4],[3],[]),([43,5,1,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_11_4 : checkNodesBT W_11 g_11 F_11 P_11_4 A_11 B_11_3 4 N_11_4 = true := by decide +kernel
def B_11_4 : BT (List (List Nat)) := buildBucketsBT W_11 N_11_4
set_option maxRecDepth 500000 in
lemma B_11_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_11 4 xs.toFinset) B_11_4 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok (buildPoolsSubBT_sound S_11_ok) A_11_ok B_11_3_ok C_11_4
def U_11_5 : List Nat := ([0,1,2]++r 4 45)
def P_11_5 : BT (Option BoundPool) := buildPoolsSubBT 7 W_11 r_11 S_11 ps_11 U_11_5
def N_11_5 : List NodeSpec := [([45,0,1,2],[4,5,6],[]),([47,0,1,2,46,4],[7],[]),([50,0,1,2,49,4],[8,9,10],[]),e5 [14] [1,8,11,12],([13,0,11,3,4],[5,6,12,13],[0]),([52,0,1,10,3,4],[14,15],[]),e5 [55] [16],([0,56,57,2,3,4],[16,17],[]),([0,56,2,59,3,4],[16],[]),([0,1,30,27,3,4],[16,18,19,20],[0,1]),e5 [61] [1,11],([0,1,2,33,9,3],[5,6,15,20,21],[]),u5 [43] [],u5 [41] [],e5 [7] [1,11],([13,0,1,3,62,4],[12],[]),e5 [63] [16],([42,1,2,6,3,4],[],[0]),([0,1,2,7,9,4],[8,14,22],[0]),e5 [64] [1,11],([42,1,2,7,3,4],[1],[]),([1,2,7,22,3,4],[11],[0]),e5 [66] [1,11],([13,67,0,6,3,4],[12,16,21],[]),([0,56,58,6,3,4],[16,21],[]),([68,0,1,6,3,4],[12,16],[]),e5 [69] [16],([15,0,16,6,3,4],[16,20,23,24],[0]),([0,16,7,6,3,4],[16,20,23,25,26],[0]),([70,0,16,6,3,4],[25,27],[]),([13,0,1,33,3,4],[6,12,28,29],[0]),([17,0,6,3,4],[6,16,23,30],[0]),([12,0,2,11,3,4],[5,12,15],[0]),([13,72,0,1,3,4],[12],[]),([24,0,16,6,3,4],[16,25,31],[0]),([0,1,73,2,9,3],[8,21],[]),([74,5,1,2,3,4],[],[]),e5 [75] [11],e5 [76] [],u5 [39] [],([40,5,1,2,3,4],[14],[0]),([24,0,1,2,7,4],[1],[]),([18,0,26,2,3,48],[32],[1]),([65,0,1,2,7,4],[],[]),e5 [78] [33],([18,0,1,2,49,4],[1,8,9],[]),([0,26,25,2,3,4],[],[0]),([24,0,1,2,49,4],[1],[]),([79,18,0,1,3,4],[34],[]),([18,0,80,2,3,4],[20,35,36],[]),e5 [81] [1,37],e5 [83] [38],([82,0,25,2,3,4],[],[]),e5 [84] [39],([85,18,0,2,3,4],[40],[]),([5,0,1,2,33,3],[1,6,15,20],[]),([0,26,86,2,3,4],[20],[]),e5 [87] [16],e5 [89] [11,12,15,20],([18,0,1,2,7,4],[1],[]),([90,0,88,2,3,4],[11],[]),e5 [91] [],([18,0,16,6,3,4],[20,25,41],[0]),([45,0,1,2,9],[4,5,6,21],[]),([24,79,0,1,3,4],[34],[]),([21,0,1,3],[0,5,6],[0]),([0,16,1,92,3,4],[20],[]),([5,1,2,33,6,3],[2,6],[]),([52,37,1,2,3,4],[],[]),([13,0,1,11,3,4],[13,21],[]),([18,0,1,27,3,4],[18],[]),e5 [93] [1],e5 [94] [],u5 [19] [],([24,0,80,2,3,4],[36],[]),e5 [95] [],e5 [96] [42],([24,0,1,27,3,4],[16,18],[0]),([0,26,1,2,3,97],[6,15,20],[]),([37,1,2,7,3,4],[1],[0]),([24,0,26,2,3,48],[32],[1]),u5 [29] [1,11,12,16],([13,0,56,6,3,4],[16,21],[]),e5 [98] [1],([90,24,99,0,2,3],[43],[1]),([100,0,2,11,3,4],[44],[]),([5,1,32,6,3,4],[11,45],[0]),([5,1,2,7,3,4],[11,14],[0]),([5,1,2,35,3,4],[1,14,46],[0]),([5,1,2,33,3],[1,5,6],[0,1]),([101,5,1,2,3,4],[1,14],[]),([13,5,1,6,3,4],[45,46],[0]),([0,26,57,2,3,4],[20],[]),u5 [28] [],([90,99,18,0,2,3],[43],[1]),([5,1,2,6,9,3],[5,6,46],[0]),e5 [102] [16],([5,1,57,2,3,4],[],[]),([5,1,2,9,3,103],[5],[]),([37,1,57,2,3,4],[],[]),([104,5,1,2,9,3],[6],[]),([24,85,0,2,3,4],[40],[]),e5 [101] [11],([13,37,1,6,3,4],[47,48],[]),([40,37,1,2,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_11_5 : checkNodesBT W_11 g_11 F_11 P_11_5 A_11 B_11_4 5 N_11_5 = true := by decide +kernel
def B_11_5 : BT (List (List Nat)) := buildBucketsBT W_11 N_11_5
set_option maxRecDepth 500000 in
lemma B_11_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_11 5 xs.toFinset) B_11_5 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok (buildPoolsSubBT_sound S_11_ok) A_11_ok B_11_4_ok C_11_5
def U_11_6 : List Nat := ([1,4,5,6]++r 8 11++r 20 4++[25,28,29,31,32,34,35,36,40,41]++r 43 44)
def P_11_6 : BT (Option BoundPool) := buildPoolsSubBT 7 W_11 r_11 S_11 ps_11 U_11_6
def N_11_6 : List NodeSpec := [([106,1,2,3,4],[1,5,6,11],[]),([107,0,1,3,4],[5,6,21],[]),([108,1,2,3,4],[1,6,11,21],[]),a5 [104,9] [6,12,22] [0,1],e5 [109] [4,5,12,15,20],e5 [103] [5,11,12,15,20,49],([90,99,0,2,3],[5,6,16,43],[0,1]),u5 [49] [1,5,6,10,11,14,16],([0,1,2,49,4],[5,6,9,10],[0,1]),([85,0,2,3,4],[6,12,16,40],[0]),u5 [11] [5,11,12,15,21,44],a5 [13,9] [4,6,22] [1],([13,110,0,1,3,4],[6,12,14,20,21,50],[]),([112,1,2,3,4],[1,5,11,12],[]),u5 [13,67] [8,12,16,21,22],e5 [13,113] [12,14,20,21,22,51],e5 [104] [1,6,11,15,16,22],e5 [13,57] [12,16,20,22],u5 [57] ([8,11,12]++r 14 4++[20]),([0,1,2,9,44],[4,5,6],[0]),u5 [9,103] [5,8],e5 [114] [1,5,11,12,14],e5 [116] [4,6],a5 [117] [1,4,5,11,12,20] [1],([13,0,1,10,3,4],[6,12,13,14,21,52],[0]),e5 [110,51] [5,6,20,21],a5 [24,48] [11,14,21,53] [0,1],u5 [13,56] [4,8,12,16,22,54],([5,1,2,9,3,4],[1,4,5,6,11,45,55,56],[]),e5 [119] [1,4,5,11,12,20,57,58],u5 [24,16] [1,11,16,59],e5 [13,99] [5,6,8,12,15,20],([5,1,2,9,3],[4,5,6,60],[0,1]),u5 [90,18] [1,11,16,61],([0,120,2,3,4],[6,16,21],[]),([105,5,1,2,3],[4,6,14],[]),([13,5,1,2,3,4],[4,6,11,45,56],[0]),a5 [52] [1,4,11,12,14,15,16,20] [0,1],u5 [77,26] [6,11,12,16,20,62],([37,1,2,6,3,4],[5,6,47,48,63],[0,1]),([5,1,2,3,4],[1,4,5,6,11],[]),e5 [121] [1,4,11,12,15,16,20,21,64],([0,56,2,51,4],[4,5,8,16],[]),([122,1,2,3,4],[4,6,11],[]),e5 [123] [11,12,15,16,20,21,65],u5 [24,6] [1,11,12,15,16,20,21,63],a5 [56,58] [4,12,16,66,67] [0,1],([0,1,27,3,4],[5,6,16,18,20],[0,1]),e5 [77,99] [5,6,11,15,68],u5 [13,26] [6,12,16,20,22],u5 [82,18] [11,12,16,20,41,69],a5 [88] [4,11,12,14,15,20,70] [0,1],([5,1,34,2,3,4],[4,5,11,45,56,71],[0,1]),a5 [24,26] [1,11,16,62] [0,1],u5 [90,24] [1,11,16,61],a5 [110,18] [6,11,20,72] [1],e5 [13,124] [12,15,16,20,21,22],a5 [24,110] [1,6,11,20,72] [1],([105,65,0,1,2],[5,6,14,21],[0]),([65,37,1,2,3,4],[1,5,6,47,48,73,74],[]),u5 [18,6] [1,11,20,21,63],a5 [18,26] [11,16,62] [0,1],([37,1,2,3,51,4],[1,5,48,74,75],[0]),a5 [18,16] [11,12,16,59] [0,1],u5 [17] [1,6,11,12,16],u5 [59] [1,6,8,11,16],a5 [18,48] [11,15,16,21,53] [0,1],([5,1,2,6,3,4],[5,6,11,46,63],[0,1]),e5 [9] [1,4,5,6,11,12,14,16],a5 [26,53] [6,12,16,20] [0,1],u5 [24,82] [1,11,16,31,69],e5 [126] [4,6,11,12,76],([0,1,128,3,4],[4,5,16],[]),([82,67,0,2,3,4],[5,12,15,16,21,77],[1]),e5 [34] [4,5,11,12,15,20,71],u5 [5,6] [1,6,11,12,15,16,20,63],([79,0,1,3,4],[5,6,34,78],[0]),([13,37,1,2,3,4],[1,6,47,48,54,74],[0]),([129,0,1,2,4],[5,6,21,79,80],[]),([0,80,2,3,4],[6,16,35,36],[0]),([37,1,2,9,3,4],[1,4,5,6,47,55,74],[]),u5 [33,6] [5,6,16,20,28],([0,130,2,3,4],[6,12,16,21],[]),([0,16,6,3,4],[6,16,20,23,25],[0]),u5 [70,6] [1,11,63],u5 [7] [1,11,12,14,15,16,20],u5 [73] [1,5,8,11,12,20],([0,56,2,6,3,4],[5,12,15,16,21,81],[0,1]),e5 [131] [1,6,11,12,15,16,82],u5 [60] [1,5,6,8,11,15,20,21],u5 [25] [11,12,14,15,20,21,83],([13,0,1,6,3,4],[6,12,16,20,21,29,52],[0]),u5 [7,6] [12,15,16,20,21,63],u5 [15,6] [12,15,16,20],([132,1,2,3,4],[1,5,6,11,84],[]),a5 [33] [1,5,6,11,20,21,28] [0,1],u5 [40] [1,8,11,14,15,20],u5 [6,9] [5,6,15,16,20,21],u5 [65,6] [5,6,12,15,16,20,21],u5 [6] [1,6,11,15,16,20,21],([0,26,2,3,48],[6,16,32],[0,1]),e5 [133] [1,6,11,15,16,85],u5 [86] [4,11,14,15,16,20,86],e5 [13] [1,4,6,11,12,15,16,20,21]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_11_6 : checkNodesBT W_11 g_11 F_11 P_11_6 A_11 B_11_5 6 N_11_6 = true := by decide +kernel
def B_11_6 : BT (List (List Nat)) := buildBucketsBT W_11 N_11_6
set_option maxRecDepth 500000 in
lemma B_11_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_11 6 xs.toFinset) B_11_6 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok (buildPoolsSubBT_sound S_11_ok) A_11_ok B_11_5_ok C_11_6
def U_11_7 : List Nat := ([1,4,5,6,8,11,12,14,15,16]++r 20 4++[53,54,55,59,61,62,63,67,69,72,73,75])
def P_11_7 : BT (Option BoundPool) := buildPoolsSubBT 7 W_11 r_11 S_11 ps_11 U_11_7
def N_11_7 : List NodeSpec := [a5 [65] [1,4,5,6,11,12,16,21,73] [0,1],a5 [44] [1,5,6,11,21] [0,1],a5 [110] [1,5,6,11,16,21,72] [0,1],a5 [9] [4,5,6,55] [0,1],a5 [90] [1,6,11,16,21,61] [0,1],a5 [26] [1,5,6,11,16,21,62] [0,1],a5 [127] [1,4,5,8,11,12,14,16,21] [0,1],a5 [134] [1,4,5,12,14,16,21] [1],([5,1,2,3,4],[1,4,5,6,11],[0,1]),u5 [105] [1,4,5,6,11,14],a5 [77] [1,4,6,11,12,14,16,20,21] [0,1],a5 [18] [1,4,11,12,14,16] [0,1],a5 [24] [1,11,12,14,16,21] [0,1],u5 [135] [1,4,5,6,11,21],a5 [48] [1,5,6,11,16,21,53] [0,1],a5 [13] [1,4,6,11,12,14,16,20,22,54] [0,1],a5 [82] [1,5,11,12,14,16,20,21,23,69] [0,1],([37,1,2,3,4],[1,5,6],[0,1]),a5 [51] [4,5,12,15,16,75] [0,1],a5 [5] [1,4,5,6,11,12,16,21] [0,1],u5 [16] [1,6,11,12,16,21,59],a5 [6] [5,6,11,12,15,16,20,21,63] [0,1],a5 [56] [1,4,5,11,12,16,67] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_11_7 : checkNodesBT W_11 g_11 F_11 P_11_7 A_11 B_11_6 7 N_11_7 = true := by decide +kernel
def B_11_7 : BT (List (List Nat)) := buildBucketsBT W_11 N_11_7
set_option maxRecDepth 500000 in
lemma B_11_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_11 7 xs.toFinset) B_11_7 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok (buildPoolsSubBT_sound S_11_ok) A_11_ok B_11_6_ok C_11_7
def U_11_8 : List Nat := [1]
def P_11_8 : BT (Option BoundPool) := buildPoolsSubBT 7 W_11 r_11 S_11 ps_11 U_11_8
def N_11_8 : List NodeSpec := [a5 [] [1] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_11_8 : checkNodesBT W_11 g_11 F_11 P_11_8 A_11 B_11_7 8 N_11_8 = true := by decide +kernel
def B_11_8 : BT (List (List Nat)) := buildBucketsBT W_11 N_11_8
set_option maxRecDepth 500000 in
lemma B_11_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_11 8 xs.toFinset) B_11_8 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok (buildPoolsSubBT_sound S_11_ok) A_11_ok B_11_7_ok C_11_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_11_ok : forestRootCheck r_11 g_11 [(VAR 0,18,19),(VAR 1,12,14),(VAR 2,10,14),(VAR 3,6,14),(VAR 4,3,19)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_11_in : bucketContainsBT B_11_8 r_11 = true := by decide +kernel
lemma low_11 : Lower r_11 g_11 9 := lower_of_forestBT root_11_ok B_11_8_ok root_11_in
def g_12 := (d 0xfee8fee8fee8fee8)
def r_12 : List Nat := varsOf 15
def p_12 : List Nat := [3,3,5,5,6,6,9,9,10,10,12,12]
def q_12 : List Nat := [2,1,4,1,4,2,8,1,8,2,8,4]
def F_12 : Nat := fullMask 12
set_option maxHeartbeats 0 in
lemma gp_12 : goodPairs g_12 p_12 q_12 := goodPairs_of (by decide +kernel)
def W_12 : BT Decor := buildWiresBT 4 (mkBase p_12 q_12 r_12) [(1,0,1),(1,4,2),(2,5,3),(1,1,2),(1,3,1),(1,3,2),(2,4,3),(1,3,0)]
lemma W_12_ok : btAll (fun x => faithful p_12 q_12 x ∧ x.1 < 2^256) W_12 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_12 : List (List (Nat × Nat)) := [[],[(2,3)],[(1,2)],[(1,3),(2,3)],[(1,2),(2,3)],[(1,3)],[(0,2),(1,2)],[(0,3),(1,3),(2,3)],[(0,2),(1,2),(2,3)],[(0,3),(1,3)],[(0,1),(1,2)],[(0,2),(1,3)]]
def A_12 : BT (List (Nat × Nat)) := btOfList 4 al_12
set_option maxHeartbeats 0 in
lemma A_12_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_12 = g_12) A_12 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_12_0 : Slice r_12 g_12 (subcubeFast 1 0) 4 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_1 : Slice r_12 g_12 (subcubeFast 2 0) 4 := by
  have hc : Lower (varsOf 13) (d 0xfaa0faa0faa0faa0) 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_2 : Slice r_12 g_12 (subcubeFast 4 0) 4 := by
  have hc : Lower (varsOf 11) (d 0xee88ee88ee88ee88) 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_12_3 : Slice r_12 g_12 (subcubeFast 8 0) 4 := by
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) low_0
def S_12 : BT (Option (Nat × Nat)) := btOfList 2 [some (subcubeFast 1 0,4),some (subcubeFast 2 0,4),some (subcubeFast 4 0,4),some (subcubeFast 8 0,4)]
lemma S_12_ok : btAll (fun o => ∀ p, o = some p → Slice r_12 g_12 p.1 p.2) S_12 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_12_0) (forall_cons (fun _ h => by cases h; exact sl_12_1) (forall_cons (fun _ h => by cases h; exact sl_12_2) (forall_cons (fun _ h => by cases h; exact sl_12_3) (fun _ h => (List.not_mem_nil h).elim)))))
def ps_12 : BT (Option PoolSpec) := btOfList 2 [q 2 [],q 1 [],q 3 [],q 0 []]
def B_12_2 : BT (List (List Nat)) := BT.empty
lemma B_12_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 2 xs.toFinset) B_12_2 := .empty
def U_12_3 : List Nat := [0,1]
def P_12_3 : BT (Option BoundPool) := buildPoolsSubBT 2 W_12 r_12 S_12 ps_12 U_12_3
def N_12_3 : List NodeSpec := [([6,0,1,2],[],[]),([0,7,8,9],[0,1],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_3 : checkNodesBT W_12 g_12 F_12 P_12_3 A_12 B_12_2 3 N_12_3 = true := by decide +kernel
def B_12_3 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_3
set_option maxRecDepth 500000 in
lemma B_12_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 3 xs.toFinset) B_12_3 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_2_ok C_12_3
def U_12_4 : List Nat := [1,2,3]
def P_12_4 : BT (Option BoundPool) := buildPoolsSubBT 2 W_12 r_12 S_12 ps_12 U_12_4
def N_12_4 : List NodeSpec := [([0,1,2,5,3],[2],[0]),([10,0,1,2,3],[],[]),([0,1,2,11,8],[1,3],[10])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_4 : checkNodesBT W_12 g_12 F_12 P_12_4 A_12 B_12_3 4 N_12_4 = true := by decide +kernel
def B_12_4 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_4
set_option maxRecDepth 500000 in
lemma B_12_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 4 xs.toFinset) B_12_4 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_3_ok C_12_4
def U_12_5 : List Nat := (r 0 4)
def P_12_5 : BT (Option BoundPool) := buildPoolsSubBT 2 W_12 r_12 S_12 ps_12 U_12_5
def N_12_5 : List NodeSpec := [([0,1,4,2,3],(r 0 4),[0,1,3,5,7,9])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_5 : checkNodesBT W_12 g_12 F_12 P_12_5 A_12 B_12_4 5 N_12_5 = true := by decide +kernel
def B_12_5 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_5
set_option maxRecDepth 500000 in
lemma B_12_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 5 xs.toFinset) B_12_5 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_4_ok C_12_5
def U_12_6 : List Nat := (r 0 4)
def P_12_6 : BT (Option BoundPool) := buildPoolsSubBT 2 W_12 r_12 S_12 ps_12 U_12_6
def N_12_6 : List NodeSpec := [([0,1,2,3],(r 0 4),[0,2,4,6,8,11])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_12_6 : checkNodesBT W_12 g_12 F_12 P_12_6 A_12 B_12_5 6 N_12_6 = true := by decide +kernel
def B_12_6 : BT (List (List Nat)) := buildBucketsBT W_12 N_12_6
set_option maxRecDepth 500000 in
lemma B_12_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_12 6 xs.toFinset) B_12_6 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok (buildPoolsSubBT_sound S_12_ok) A_12_ok B_12_5_ok C_12_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_12_ok : forestRootCheck r_12 g_12 [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 3,1,9)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_12_in : bucketContainsBT B_12_6 r_12 = true := by decide +kernel
lemma low_12 : Lower r_12 g_12 7 := lower_of_forestBT root_12_ok B_12_6_ok root_12_in
def g_13 := (d 0xfff8e880fff8e880)
def r_13 : List Nat := varsOf 31
def p_13 : List Nat := [7,7,7,11,11,11,13,13,13,14,14,14,19,19,19,20,20,21,21,22,22,24,24,25,25,26,26,28]
def q_13 : List Nat := [6,5,3,10,9,3,12,9,5,12,10,6,18,17,3,16,4,17,5,18,6,16,8,17,9,18,10,12]
def F_13 : Nat := fullMask 28
set_option maxHeartbeats 0 in
lemma gp_13 : goodPairs g_13 p_13 q_13 := goodPairs_of (by decide +kernel)
def W_13 : BT Decor := buildWiresBT 8 (mkBase p_13 q_13 r_13) [(1,2,3),(0,0,1),(1,6,4),(0,5,7),(0,2,3),(1,9,4),(0,6,2),(1,11,4),(0,3,12),(1,3,12),(3,13,14),(1,6,9),(2,16,4),(0,0,5),(2,0,4),(0,0,3),(0,1,2),(1,20,21),(2,22,4),(1,21,4),(1,20,24),(0,0,2),(1,26,4),(0,1,3),(1,28,4),(1,6,2),(1,30,4),(3,6,31),(0,6,3),(1,33,4),(0,2,34),(1,2,34),(3,3,36),(3,6,10),(1,9,7),(1,3,4),(1,2,4),(0,0,41),(1,20,4),(1,37,33),(0,1,41),(0,3,24),(1,3,24),(3,46,47),(1,28,2),(1,49,4),(0,0,50),(0,2,29),(0,3,41),(0,3,7),(1,54,2),(1,3,7),(0,6,5),(1,57,4),(2,6,4),(1,59,9),(3,54,56),(2,2,34),(3,2,34),(0,2,7),(0,3,31),(3,45,3),(2,5,4),(2,2,7),(3,2,7),(0,2,56),(3,54,2),(1,5,4),(1,30,3),(3,6,73),(2,2,3),(1,75,4),(2,5,7),(3,3,7),(3,6,3),(2,30,4),(3,6,2),(1,6,3),(3,28,41),(2,2,4),(3,79,41),(3,33,41),(3,79,40),(3,28,2),(1,88,4),(3,3,31),(0,0,10),(2,1,4),(3,92,0),(3,3,27),(0,1,5),(2,73,4),(1,75,7),(3,21,3),(3,59,5),(2,0,46),(1,79,2),(1,59,75),(1,74,4),(1,37,6),(1,79,4),(3,3,30),(3,79,5),(0,2,43),(2,3,2),(3,109,7),(1,81,4),(1,75,6),(2,112,4),(0,6,40),(3,114,2),(2,3,4),(1,116,2),(3,3,12),(2,0,29),(3,6,72),(1,64,3),(3,26,3),(3,6,117),(3,28,0),(1,26,3),(3,9,7),(1,20,2),(2,127,4),(3,122,40),(3,28,27),(3,20,0),(1,131,4),(1,2,43),(2,2,29),(3,2,29),(1,19,2),(3,28,136),(0,28,41),(3,138,0),(0,0,40),(0,2,40),(3,2,14),(1,142,26),(2,0,10),(2,9,4),(3,145,5),(3,95,0),(3,75,41),(2,0,53),(0,1,40),(3,150,0),(3,84,3),(3,109,40),(3,150,2),(1,84,6),(1,92,3),(1,122,4),(2,1,2),(3,158,0),(1,18,4),(3,33,2),(3,19,3),(0,0,24),(0,26,40),(1,116,26),(1,158,4),(2,1,3),(3,167,2),(1,168,4),(1,125,4),(3,167,0),(1,11,3),(0,26,3),(1,173,4),(0,6,41),(0,21,3),(3,176,0),(0,0,72),(1,167,4),(1,75,20),(3,142,0),(1,92,2),(3,158,40),(3,116,2),(3,116,0),(2,75,4),(3,109,0),(2,26,3),(2,26,4),(2,6,3),(3,92,2),(2,0,9),(2,131,2),(1,131,2),(2,131,4)]
lemma W_13_ok : btAll (fun x => faithful p_13 q_13 x ∧ x.1 < 2^256) W_13 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_13 : List (List (Nat × Nat)) := [[],[(2,3)],[(0,1)],[(0,1),(2,3)]]
def A_13 : BT (List (Nat × Nat)) := btOfList 2 al_13
set_option maxHeartbeats 0 in
lemma A_13_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_13 = g_13) A_13 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_13_0 : Slice r_13 g_13 (subcubeFast 0 1) 7 := by
  have hc : Lower (varsOf 30) (d 0xfffcfcc0fffcfcc0) 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_12
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_1 : Slice r_13 g_13 (subcubeFast 0 2) 7 := by
  have hc : Lower (varsOf 29) (d 0xfffafaa0fffafaa0) 7 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_12
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_2 : Slice r_13 g_13 (subcubeFast 16 0) 7 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_1
set_option maxHeartbeats 0 in
lemma sl_13_3 : Slice r_13 g_13 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) (d 0xfff0a000fff0a000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_4 : Slice r_13 g_13 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) (d 0xff888800ff888800) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_5 : Slice r_13 g_13 (subcubeFast 0 4) 5 := by
  have hc : Lower (varsOf 27) (d 0xffffee88ffffee88) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_6 : Slice r_13 g_13 (subcubeFast 8 0) 5 := by
  have hc : Lower (varsOf 23) (d 0xf8f88080f8f88080) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_7 : Slice r_13 g_13 (subcubeFast 0 8) 5 := by
  have hc : Lower (varsOf 23) (d 0xffffe8e8ffffe8e8) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_8 : Slice r_13 g_13 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) (d 0xfff0c000fff0c000) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_9 : Slice r_13 g_13 (subcubeFast 16 8) 4 := by
  exact slice_fast_direct_f (z := 16) (o := 8) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_13_10 : Slice r_13 g_13 (subcubeFast 16 4) 4 := by
  have hc : Lower (varsOf 11) (d 0xee88ee88ee88ee88) 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_11 : Slice r_13 g_13 (subcubeFast 16 2) 4 := by
  have hc : Lower (varsOf 13) (d 0xfaa0faa0faa0faa0) 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_12 : Slice r_13 g_13 (subcubeFast 8 2) 4 := by
  have hc : Lower (varsOf 21) (d 0xfafaa0a0fafaa0a0) 4 := carry_of (swaps := [(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 8) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_13 : Slice r_13 g_13 (subcubeFast 4 2) 4 := by
  have hc : Lower (varsOf 25) (d 0xffaaaa00ffaaaa00) 4 := carry_of (swaps := [(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_14 : Slice r_13 g_13 (subcubeFast 16 1) 4 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_15 : Slice r_13 g_13 (subcubeFast 8 1) 4 := by
  have hc : Lower (varsOf 22) (d 0xfcfcc0c0fcfcc0c0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 8) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_16 : Slice r_13 g_13 (subcubeFast 4 1) 4 := by
  have hc : Lower (varsOf 26) (d 0xffcccc00ffcccc00) 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_17 : Slice r_13 g_13 (subcubeFast 2 1) 4 := by
  have hc : Lower (varsOf 28) (d 0xfff0f000fff0f000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 2) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_18 : Slice r_13 g_13 (subcubeFast 1 2) 4 := by
  have hc : Lower (varsOf 28) (d 0xfff0f000fff0f000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_13_19 : Slice r_13 g_13 (identDom 2 3) 6 := by
  have hc : Lower (varsOf 23) (d 0xf8f8e0e0f8f8e0e0) 6 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_2
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
def S_13 : BT (Option (Nat × Nat)) := btOfList 5 [some (subcubeFast 0 1,7),some (subcubeFast 0 2,7),some (subcubeFast 16 0,7),some (subcubeFast 2 0,5),some (subcubeFast 4 0,5),some (subcubeFast 0 4,5),some (subcubeFast 8 0,5),some (subcubeFast 0 8,5),some (subcubeFast 1 0,5),some (subcubeFast 16 8,4),some (subcubeFast 16 4,4),some (subcubeFast 16 2,4),some (subcubeFast 8 2,4),some (subcubeFast 4 2,4),some (subcubeFast 16 1,4),some (subcubeFast 8 1,4),some (subcubeFast 4 1,4),some (subcubeFast 2 1,4),some (subcubeFast 1 2,4),some (identDom 2 3,6)]
lemma S_13_ok : btAll (fun o => ∀ p, o = some p → Slice r_13 g_13 p.1 p.2) S_13 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_13_0) (forall_cons (fun _ h => by cases h; exact sl_13_1) (forall_cons (fun _ h => by cases h; exact sl_13_2) (forall_cons (fun _ h => by cases h; exact sl_13_3) (forall_cons (fun _ h => by cases h; exact sl_13_4) (forall_cons (fun _ h => by cases h; exact sl_13_5) (forall_cons (fun _ h => by cases h; exact sl_13_6) (forall_cons (fun _ h => by cases h; exact sl_13_7) (forall_cons (fun _ h => by cases h; exact sl_13_8) (forall_cons (fun _ h => by cases h; exact sl_13_9) (forall_cons (fun _ h => by cases h; exact sl_13_10) (forall_cons (fun _ h => by cases h; exact sl_13_11) (forall_cons (fun _ h => by cases h; exact sl_13_12) (forall_cons (fun _ h => by cases h; exact sl_13_13) (forall_cons (fun _ h => by cases h; exact sl_13_14) (forall_cons (fun _ h => by cases h; exact sl_13_15) (forall_cons (fun _ h => by cases h; exact sl_13_16) (forall_cons (fun _ h => by cases h; exact sl_13_17) (forall_cons (fun _ h => by cases h; exact sl_13_18) (forall_cons (fun _ h => by cases h; exact sl_13_19) (fun _ h => (List.not_mem_nil h).elim)))))))))))))))))))))
set_option maxRecDepth 500000 in
def ps_13 : BT (Option PoolSpec) := btOfList 9 [q 1 [12296,36889,12297],q 1 [],q 0 [],q 4 [4],q 6 [4],q 19 [],q 19 [4096,20504,16613],q 5 [],q 7 [],q 4 [],q 19 [4096,16410],q 1 [12296,36889],q 8 [],q 3 [],q 1 [16409,16393,167936],q 19 [4096,20507],q 2 [12296,12297],q 0 [12296,16421,12297],q 1 [12296,16421,12297],q 1 [12296,12297],q 19 [4096,20480],q 6 [],q 0 [12313,16409,16397],q 2 [4096,12313],q 0 [8217,12313,12297],q 12 [],q 9 [],q 5 [16386],q 2 [4096,12312,168071],q 19 [4096,16386],q 2 [],q 19 [4096,16409],q 19 [16390,371],q 1 [12297],q 0 [12297],q 0 [8216,16429],q 1 [8216,16429],q 0 [8217,12409,16678],q 2 [12288],q 2 [4096,163864,8651],q 0 [8217,16505,126991],q 15 [],q 3 [12288],q 0 [12296,36889,12297],q 0 [12297,16405,294939],q 19 [4096,20504],q 0 [12312,16517],q 1 [12312,16517],q 2 [4096,12312],q 10 [],q 0 [8196,16469],q 1 [16393],q 0 [16393],q 0 [12393,16489,16397],q 2 [8192,12393],q 2 [12292,168048,555],q 0 [16397,163848],q 2 [8192,163840,163848],q 0 [16489,16397,163848],q 2 [12296,12297,21063],q 19 [20484,383],q 0 [16393,167948],q 2 [167948,217090],q 0 [16393,167951],q 2 [167936],q 2 [167936,167948],q 0 [16393,167940],q 0 [16397,163844],q 2 [163844,603],q 2 [12298,12627],q 0 [12298,16393],q 2 [8206,164279],q 13 [],q 2 [8205,163848],q 0 [12296,12297],q 19 [20480],q 19 [16421],q 1 [16397],q 2 [163844,8795],q 0 [12296,16421],q 0 [12297,20484],q 2 [12296,8231,12589],q 0 [12296,8231,12589],q 0 [12297,16406],q 2 [12297],q 19 [16386],q 17 [],q 1 [371],q 2 [371],q 0 [12296,36889],q 0 [16394,24913],q 1 [12297,20480],q 1 [12296],q 4 [4096],q 3 [16386],q 2 [12296],q 1 [16386],q 1 [12288],q 1 [16394],q 2 [4096,12288],q 2 [167951],q 2 [4096,28687],q 0 [16409,28687],q 0 [12298,24877],q 0 [16398,8657],q 3 [8192],q 1 [8192],q 2 [4096,8192],q 1 [12657],q 0 [16390,12657],q 2 [4096],q 1 [16409],q 0 [16409],q 0 [16409,16393],q 1 [16409,16393],q 14 [],q 1 [12298],q 19 [4096],q 0 [16465],q 1 [12288,16465],q 0 [12298,8495,16421],q 1 [12298,8495,16421],q 2 [4096,12315],q 1 [16393,168051],q 2 [12292,168051],q 0 [8217,12409],q 2 [8192,12395],q 0 [12395,16873],q 2 [8198,635],q 7 [16386],q 0 [8196,86097],q 1 [12288,86097],q 16 [],q 0 [12297,16457],q 1 [12297,20480,16457],q 0 [12315,8509],q 0 [12312,8327],q 1 [12312,8327],q 2 [4096,12312,8327],q 1 [12290,16386,12367],q 2 [12290,12367],q 0 [8217,12298],q 1 [12296,16421],q 2 [4096,8216],q 2 [12292,8307],q 1 [8307,16393],q 8 [12292],q 0 [12292],q 6 [4096],q 2 [8192,163944],q 0 [8219,12297],q 1 [8219,12297],q 2 [4096,8219],q 2 [12288,167951],q 0 [8219,16393],q 0 [12297,20507],q 0 [16398,106961],q 0 [8198,17017],q 0 [8219],q 1 [8219],q 0 [8217,12313],q 0 [8216],q 1 [8216],q 0 [8217,16409],q 2 [12290,167948],q 0 [8219,16709],q 1 [8863,17057],q 7 [17057],q 2 [12294,8863],q 1 [8217,8192],q 0 [12313,16397],q 0 [12313,8205],q 8 [8196],q 0 [8196],q 2 [4,8196],q 1 [16469],q 2 [4096,8217],q 0 [8217,16506],q 0 [8217,16394],q 0 [16489],q 1 [8192,16489],q 7 [16393],q 1 [8219,16393],q 0 [8217,12410],q 1 [8219,16709],q 2 [12294,671],q 0 [8216,12333],q 1 [8216,12333],q 2 [4096,8216,12333],q 0 [16410],q 1 [16410],q 5 [16397],q 2 [8205],q 0 [8205,16397],q 0 [8217,16505],q 7 [16394],q 0 [12297,16394],q 1 [12298,24877],q 0 [12297,16405],q 2 [12292],q 0 [12298,12589],q 0 [12392,17077],q 2 [8196],q 2 [12298],q 2 [4096,167960],q 0 [12292,16497],q 0 [16393,167963],q 2 [4096,167963],q 1 [16393,167963],q 1 [16393,167936],q 2 [4096,167936],q 1 [8307,16737],q 1 [115],q 2 [12292,115],q 1 [8217,12298],q 0 [12298,16685],q 1 [12372,707],q 2 [8196,12372,707],q 2 [8192,12392],q 1 [8192,12392,17077],q 0 [12393,16885],q 0 [8273,16465],q 0 [12393,16397],q 0 [8273,16394],q 2 [12297,294912],q 2 [12288,8273],q 0 [8273,16894],q 2 [8192],q 11 [],q 0 [16489,16397],q 2 [8192,110607],q 0 [16489,110607],q 1 [17053],q 2 [12294],q 0 [12294,17053],q 0 [8207,82221],q 0 [16397,163851],q 2 [163851,571],q 2 [8192,163840],q 0 [16397],q 2 [8192,163848],q 0 [16390,8561],q 2 [8198,164475],q 0 [16398,8659],q 1 [16398,8657],q 0 [16398],q 18 [],q 1 [16393,167951],q 1 [12298,16393],q 1 [12298,16685],q 0 [8206],q 2 [8206,439],q 1 [8206,439],q 1 [12297,16406],q 1 [12297,16405],q 2 [12297,20480],q 1 [8205,16397],q 2 [12290],q 2 [12298,8495],q 0 [12298,8495],q 1 [8307],q 0 [8269],q 1 [16386,8269],q 2 [8269],q 0 [8273],q 1 [12288,8273],q 0 [12294],q 0 [12393],q 1 [8192,12393],q 0 [16394],q 0 [12394],q 0 [12298],q 0 [8217],q 1 [8217],q 0 [16490],q 0 [12314],q 0 [8198],q 1 [635],q 1 [16397,163848],q 2 [163848],q 0 [12296],q 1 [8563],q 2 [8563],q 0 [12392],q 1 [8192,12392],q 0 [8207],q 2 [8198],q 1 [12296,36866],q 2 [12296,36866],q 1 [8863],q 0 [12294,8863],q 0 [8718],q 0 [16909],q 1 [12290,16909],q 1 [12290],q 1 [12298,12589],q 2 [12298,12589],q 0 [16390],q 0 [8717],q 0 [16910],q 2 [12296,8231],q 0 [12296,8231],q 1 [12297,16394]]
def B_13_2 : BT (List (List Nat)) := BT.empty
lemma B_13_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_13 2 xs.toFinset) B_13_2 := .empty
def U_13_3 : List Nat := []
def P_13_3 : BT (Option BoundPool) := buildPoolsSubBT 9 W_13 r_13 S_13 ps_13 U_13_3
def N_13_3 : List NodeSpec := [([0,1,8,10],[],[]),([15,0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_13_3 : checkNodesBT W_13 g_13 F_13 P_13_3 A_13 B_13_2 3 N_13_3 = true := by decide +kernel
def B_13_3 : BT (List (List Nat)) := buildBucketsBT W_13 N_13_3
set_option maxRecDepth 500000 in
lemma B_13_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_13 3 xs.toFinset) B_13_3 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok (buildPoolsSubBT_sound S_13_ok) A_13_ok B_13_2_ok C_13_3
def U_13_4 : List Nat := (r 0 7)
def P_13_4 : BT (Option BoundPool) := buildPoolsSubBT 9 W_13 r_13 S_13 ps_13 U_13_4
def N_13_4 : List NodeSpec := [([17,0,1,5,4],[],[]),([18,1,16,5,4],[0],[]),([19,1,16,5,4],[0],[]),([23,6,2,3,4],[],[]),([6,2,3,4,25],[1,2],[]),([6,2,3,27,29],[3,4],[]),([32,0,2,3,29],[],[]),([0,1,35,3,36],[],[1]),([37,0,1,2,34],[],[]),([38,0,1,5,4],[],[]),([0,1,5,4,39],[5],[]),([0,1,2,8,40],[],[]),([37,42,1,2,43],[],[]),([44,0,1,2,4],[],[]),([42,45,2,3,7],[],[]),([48,0,1,2,4],[],[]),([51,1,52,3,4],[],[]),([42,1,2,53,43],[],[]),([0,1,9,8,4],[5],[0]),([0,1,55,4,56],[5],[]),([0,1,9,5,58],[6],[]),([0,1,55,7,40],[],[]),([0,1,60,5,4],[],[]),([61,0,1,2,4],[],[]),([62,63,0,1,3],[],[1]),([0,1,5,7,10],[],[0]),([0,1,64,65,4],[5],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_13_4 : checkNodesBT W_13 g_13 F_13 P_13_4 A_13 B_13_3 4 N_13_4 = true := by decide +kernel
def B_13_4 : BT (List (List Nat)) := buildBucketsBT W_13 N_13_4
set_option maxRecDepth 500000 in
lemma B_13_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_13 4 xs.toFinset) B_13_4 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok (buildPoolsSubBT_sound S_13_ok) A_13_ok B_13_3_ok C_13_4
def U_13_5 : List Nat := (r 0 6++r 7 54)
def P_13_5 : BT (Option BoundPool) := buildPoolsSubBT 9 W_13 r_13 S_13 ps_13 U_13_5
def N_13_5 : List NodeSpec := [([37,66,0,1,2,4],[],[]),([59,67,0,1,2,3],[7,8],[]),([59,0,1,9,5,4],[9,10],[0]),([19,1,2,16,3,4],[2,11],[0]),([68,69,0,1,3,4],[],[1]),([0,1,70,3,4,7],[8],[1]),([71,0,1,3,4,7],[],[]),([0,1,2,3,7,72],[12,13],[]),([37,0,1,2,3,7],[],[]),([42,1,2,3,7,41],[14],[0]),([0,1,64,3,4,31],[],[0,1]),([74,0,1,9,5,4],[5,9,15],[]),([0,1,2,3,76,7],[8],[]),e5 [77] [],([78,79,0,1,2,4],[],[]),([80,0,1,2,3,7],[2,7],[]),u5 [60] [],([6,0,1,5,4,10],[16,17,18],[0]),([6,18,1,9,5,4],[7,19,20],[0]),([0,1,2,3,27,29],[9,12,13,21],[0]),([62,0,1,2,3,34],[],[0]),([81,0,1,5,4,40],[9],[]),([0,1,2,5,7,40],[],[0]),([42,1,2,3,43,41],[],[0]),([0,1,2,82,7,40],[12,13,22,23],[]),([83,6,0,2,3,4],[2],[]),([32,0,1,3,5,4],[21],[]),([0,1,30,82,5,4],[12,13,24,25],[]),([19,67,6,1,2,3],[26,27],[]),([84,79,0,1,5,4],[9],[]),([37,33,0,1,2,4],[7],[0]),e5 [85] [13],e5 [86] [28],([19,6,1,9,5,4],[16,19,29],[0]),([87,0,1,2,4,40],[21,30],[]),([0,1,2,3,89,29],[9,13,21],[]),u5 [23] [],([90,0,1,2,4,7],[],[]),([91,0,1,5,4,10],[17],[]),e5 [74] [],([0,1,9,5,4,7],[7,9,31],[0]),([93,0,1,9,5,4],[32],[]),([94,0,1,2,27,40],[21],[]),([81,79,0,1,5,4],[9],[]),([6,18,95,2,3,4],[7,8,33,34],[]),([0,1,2,3,12,14],[9,12,13,35,36],[1]),([96,6,0,1,2,3],[37],[]),([75,0,1,3,7,41],[],[]),e5 [97] [7],([37,98,0,1,2,4],[],[]),e5 [32] [],e5 [99] [],([100,1,2,3,4,24],[],[]),([81,0,1,3,4,72],[12,13],[1]),([0,1,64,3,7,41],[],[1]),e5 [83] [],a5 [8] [1,2,7,9,13] [0,1],([81,0,1,101,3,4],[],[]),u5 [25] [1,2,8,13],e5 [102] [],e5 [103] [1,2],([81,0,1,3,7,41],[12,13,30],[]),e5 [104] [7],([0,1,2,5,4,105],[9],[]),([106,79,0,1,2,4],[],[]),([107,0,1,2,5,4],[9,21],[]),([0,1,108,3,43,41],[38],[]),([67,81,0,1,3,4],[],[]),([37,81,0,1,3,4],[],[]),e5 [110] [9],([0,1,2,3,5,58],[],[0]),u5 [39] [1,2,7,9],([0,1,2,3,111,7],[9,12,13],[]),([81,0,1,82,5,4],[9,12,13],[]),e5 [113] [],([115,0,1,3,4,40],[39],[]),([81,0,1,117,3,4],[],[]),([6,26,2,3,4,29],[3],[0,1]),([118,0,1,2,3,12],[],[1]),([90,6,0,1,2,4],[40],[]),([119,6,2,3,4,29],[41],[]),([6,22,2,3,4],[1,2,42],[0]),([32,20,1,2,3,4],[8],[2]),([37,6,20,1,2,4],[8],[]),([19,112,1,2,3,4],[],[]),([0,1,16,5,4],[0,5,43],[0,2]),u5 [17] [],([6,0,1,16,5,4],[0,9,43],[]),e5 [120] [2,44],([37,20,42,1,2,4],[2,7],[0]),([57,0,1,9,5,4],[5,9,16,45],[0]),([0,1,2,121,4,7],[9],[1]),([74,0,1,2,4,40],[30],[]),([0,1,2,3,7,10],[9,12,13,21],[0]),([94,122,0,1,2,4],[],[]),([84,74,0,1,3,4],[],[]),([112,0,1,3,4,41],[],[]),([0,1,35,2,3,34],[12,13,21,46,47,48],[0]),([75,32,0,1,3,4],[],[]),([6,0,2,3,24,40],[3,4,49,50],[1]),([6,42,45,2,3,4],[7,51,52],[0]),e5 [123] [],([37,124,0,1,2,4],[],[]),([0,1,2,125,27,40],[9,12,53,54],[]),e5 [126] [],([51,1,2,3,4,29],[7],[0]),u5 [38] [],([128,0,1,2,3,43],[2,7],[]),([129,0,1,2,4,40],[21,30],[]),([78,0,1,2,7,40],[21],[]),([88,0,1,3,29,41],[13,21,30],[]),e5 [130] [],([0,1,2,3,132,24],[8],[]),([37,0,1,2,43,41],[21],[0]),([0,1,108,3,4,133],[],[2,3]),([134,135,0,1,3,4],[],[1]),e5 [137] [],([139,1,2,3,4,41],[55],[]),([26,140,1,141,3,4],[8,56,57],[1]),([26,0,143,1,3,4],[7],[]),([67,93,0,1,2,3],[],[]),([144,0,1,5,4,10],[41],[]),([0,1,141,3,27,40],[58],[1]),([0,1,146,4],[25,41,59],[]),([84,0,1,2,3,34],[7,13],[]),([147,0,1,9,5,4],[60],[]),([0,1,2,3,12,40],[9,12,13,21,35,36],[1]),([42,0,1,3,148,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_13_5 : checkNodesBT W_13 g_13 F_13 P_13_5 A_13 B_13_4 5 N_13_5 = true := by decide +kernel
def B_13_5 : BT (List (List Nat)) := buildBucketsBT W_13 N_13_5
set_option maxRecDepth 500000 in
lemma B_13_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_13 5 xs.toFinset) B_13_5 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok (buildPoolsSubBT_sound S_13_ok) A_13_ok B_13_4_ok C_13_5
def U_13_6 : List Nat := (r 1 5++r 7 7++r 16 4++[21,23,25,26,27]++r 29 5++[35,36,38,41,42]++r 48 5++[54,56]++r 61 182)
def P_13_6 : BT (Option BoundPool) := buildPoolsSubBT 9 W_13 r_13 S_13 ps_13 U_13_6
def N_13_6 : List NodeSpec := [e5 [149,41] [2,8,12,61,62],a5 [37,42] [8,12,21,63] [0,2],a5 [42,53] [7,8,12,21,26,61,64,65] [1],u5 [42,45] [1,12,13,51,66],e5 [151,40] [1,2,12,67,68],([75,0,1,152,4],[9,21,25,69],[0]),([75,42,0,1,3,4,41],[70],[0]),([0,1,2,153,4,40],[8,21,71],[1,3]),([0,1,141,5,4],[8,72,73],[]),([18,0,1,9,5,4],[7,16,19,26,41,74,75],[0,2]),([0,1,9,5,4,10],[9,16,17,18,25,26,41,76],[]),a5 [154,40] [8,9,77,78] [1],u5 [144,10] [12,41],u5 [91,10] [12,79],u5 [147,5] [1,2,12,80],([0,1,9,5,4],[5,7,25,26,81,82],[]),([19,67,0,1,2,3],[2,7,8,26,27,83,84],[0,2]),([19,0,1,9,5,4],[9,16,19,26,41,85],[0,2]),e5 [75,93] [9,12,32,86,87],u5 [93,5] [7,12,86,88],u5 [6,16] [9,11,89],e5 [6,155] [1,2,9,90],([6,18,1,2,3,5,4],[2,7,8,33,91],[0]),([19,6,1,9,2,3,4],(r 92 5),[0]),([84,6,20,1,2,3,4],[26,42,93,97,98,99],[]),u5 [59,9] [9,13],a5 [37,6] [1,2,7,8,12,13,63,100] [0,2],u5 [78,6] [8,12,13,101,102],e5 [6,112] [1,2,9,103],u5 [6,117] [1,7,12,13,21,26,104],([6,26,1,2,3,4,40],[25,49,77,93,105,106,107],[1,2,3]),a5 [26,156] [8,9,13,25,108,109] [3],a5 [78,7] [8,13,21,110] [0,1],a5 [81,82] [8,9,12,13,25] [0,1],u5 [68,7] [7,9],a5 [7,31] [7,9,111,112] [0,1],([0,1,2,3,7,41],[9,12,13,110,113,114],[0,1,2]),u5 [9,7] [7,8,9,21,110],([19,75,6,1,2,3,4],[12,29,49,94,96,115,116],[0]),([6,0,1,9,5,4],[7,9,16,19,25,74,117],[0,2]),a5 [108,43] [7,9,12,21,38,118,119] [0,3],e5 [10] [9,12,13,26,120,121],a5 [84,79] [9,21,49,122] [0,1],u5 [83] [2,7,12,13,123,124],u5 [6,73] [1,110,125],a5 [26,157] [7,8,9,12,126,127] [3],e5 [159,40] [7,8,12,72,86,128],([19,6,1,2,3,5,4],[12,27,33,84,94,96,115,129],[0]),u5 [22] [25,30,130,131,132],e5 [160] [7,8,12,13,133,134],u5 [6,101] [1,7,12,13,135],([161,0,1,3,4],[9,21,136,137,138],[]),([145,0,1,5,4],[9,25,26],[0]),([131,1,2,162,4],[12,21,25,129,139,140],[]),([75,6,0,1,30,3,4],[9,12,13,141],[]),e5 [163,24] [12,50],u5 [6,10] [12,13,79,95,142],a5 [12] [8,9,21,35,36,143] [0,1],([88,0,1,3,4,41],[7,9,21,30,132,144,145],[3]),([6,26,28,2,3,4],[1,2,93,105,106,146,147,148],[0,1,3]),a5 [164,40] [21,30,77,149] [3],([81,0,1,3,5,4],[9,21,150,151],[0,1]),a5 [81,7] [7,9,110,152] [0,1],e5 [153] [1,2,8,12,13,21],([37,20,0,1,2,4],[2,7,8,63,153],[0,1,2]),([81,6,0,1,3,4,41],[7,12,13,110,152,154],[0]),a5 [74] [1,7,9,13,30,155] [0,1],e5 [26,165] [21,156],e5 [131,166] [8,49,72,157],a5 [81,40] [8,9,12,13,21,152,158,159] [0,1],([37,20,0,1,2,4,41],[7,21,52,63,153],[0]),u5 [30,82] [7,8,12,13,25,72,160],u5 [18,95] [1,12,13,33,80],a5 [11,40] [8,9,12,13,21,30,143,161,162] [0,1],a5 [30,7] [7,12,13,72,110,163] [0,1],([131,0,1,2,53,4,41],[7,8,164],[]),u5 [6,111] [1,7,12,13,152,165],u5 [74,5] [7,9,13,21],e5 [74,6] [1,2,7,155],e5 [169] [2,7,9,12,166,167,168],([0,1,5,4,10],[9,17,18,26],[0,2]),([26,1,30,3,4],[7,12,49,169],[]),([6,0,1,2,82,4,40],[12,13,21,23,170],[0]),([6,0,1,2,82,5,4],[12,13,21,72,171],[0]),([19,6,21,2,3,4],[1,3,25,41,49,94,96,115,172,173,174],[]),a5 [64,7] [7,9,12,13,110,111,112] [0,1],([6,0,2,3,4,24],[3,4,13,49,50,174,175],[0,1]),u5 [80,6] [1,2,9,12,13,176,177],([84,6,0,1,30,3,4],[9,12,13,178],[]),a5 [27,170] [8,12,21,49,179,180] [1,3],([81,0,1,3,4,41],[9,30,152,154,181,182],[0,1]),u5 [106,6] [8,12,13,72,183],u5 [84,33] [9,13,48,49],u5 [57,5] [7,9,21,84],a5 [5,7] [7,8,9,21,110] [0,1],a5 [111] [8,9,21,165,184] [1],e5 [84,171] [9,49,185],a5 [75,7] [7,8,9,12,13,21,31,110,111,112] [0,1],([0,1,2,172,4],[8,9,186,187,188],[]),u5 [59,75] [7,9,10,12,13,189,190],u5 [119,29] [12,41],([6,0,1,2,5,4,40],[8,72,110,191,192,193],[0,1]),a5 [16] [11,13,25,30,72,89,93,148] [0,2],u5 [6,31] [1,25,194],([84,6,0,1,3,5,4],[9,25,49,195,196],[0]),a5 [112] [1,7,9,13,30,72,93,103,197] [0,2],a5 [6,72] [1,7,8,12,13,84,198] [0,1],a5 [88,29] [7,9,144,199] [0,3],u5 [6,5] [1,7,8,9,12,13,21,25,200],([0,1,2,3,174],[9,12,21,25,201],[]),u5 [131,24] [8,12,41,50,202],([81,6,0,1,3,5,4],[7,12,13,25,150],[0]),([75,6,0,1,3,4,41],[7,9,70,203],[0]),u5 [59,5] [7,8,9,13,21,110],a5 [175,41] [9,26,30,204] [0,1],([0,1,2,3,12],[9,35,36],[0,1]),a5 [26,29] [7,9,12,199,205] [0,1,3],a5 [32] [1,8,13,21,206,207,208] [0,2],e5 [83,28] [1,7,13,123],e5 [32,6] [1,2,7,206],([6,42,1,2,3,4,41],[2,7,51,209,210],[0]),e5 [32,41] [9,13,207],e5 [89] [7,21,132,211],u5 [124,41] [7,12,13,41,212,213],([75,0,1,30,3,4],[7,21,49,72,141,214],[]),u5 [6,76] [1,9,12,13,26,49,215],e5 [84,124] [9,12,49,147,213],([177,1,2,3,4],[9,12,21,216,217],[]),e5 [174] [9,12,25,201,218,219],a5 [26,170] [7,86,106,220] [3],a5 [127,43] [7,38,132,221] [0,1],([26,0,1,2,125,4,40],[9,12,21,54,222],[0]),([84,20,0,1,127,3,4],[9,21,223],[]),([178,1,2,3,4],[7,8,12,224],[]),u5 [128,20] [9,225,226],a5 [67,6] [1,2,7,12,13,26,83] [0,1,2],a5 [94,27] [8,9,21,227] [0,3],a5 [88,40] [9,21,77,191,228] [1],([88,0,28,1,3,4,41],[7,13,21,144,145,199],[0]),([0,1,2,3,27,40],[9,12,21,49,180,229],[0,1,2]),u5 [134,29] [7,9],([26,0,1,2,3,27,40],[9,12,41,49,229],[0,3]),u5 [94,26] [8,9,230,231],a5 [26,179] [9,13,25,26,232,233,234] [2],e5 [180] [25,26,30,235],e5 [181,40] [8,9,12,21,30,41,236,237],a5 [37,26] [8,9,63,115] [2],([6,0,1,2,3,7,41],[12,13,30,72,113],[0,1]),([26,140,1,2,3,4,40],[2,8,49,238],[0,1]),e5 [83,41] [9,13,124],a5 [81,79] [7,9,21] [0,1],([26,0,1,141,3,4,40],[7,8,56,239,240],[0]),e5 [131,182] [7,8,12,41,241],e5 [183,40] [13,242],u5 [93,9] [9,12,86]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_13_6 : checkNodesBT W_13 g_13 F_13 P_13_6 A_13 B_13_5 6 N_13_6 = true := by decide +kernel
def B_13_6 : BT (List (List Nat)) := buildBucketsBT W_13 N_13_6
set_option maxRecDepth 500000 in
lemma B_13_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_13 6 xs.toFinset) B_13_6 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok (buildPoolsSubBT_sound S_13_ok) A_13_ok B_13_5_ok C_13_6
def U_13_7 : List Nat := ([1,2,5,7,8,9,12,13,16,19,21,25,26,27,30,33,34,38,41,49,51,52,54,56,63,64,70,72,74,77,79]++r 83 6++[91,92,93]++r 95 4++[100]++r 104 4++[110,111,112,115,116,117,128,132,142,143,144,147,152,158,159,161,168,176,179,180,189,193,196,198,199,200,202,203,209,212,213,215,218,225,227,233,239]++r 243 60)
def P_13_7 : BT (Option BoundPool) := buildPoolsSubBT 9 W_13 r_13 S_13 ps_13 U_13_7
def N_13_7 : List NodeSpec := [a5 [184] [2,12,21,26,30,72,243] [1],u5 [117] [7,12,13,21,26,104,244],e5 [185] [1,2,7,9,12,13,21,26,245,246],a5 [37,41] [7,9,21,26,30,51,52,63,247] [0,1,2,3],a5 [37] [1,2,7,8,9,12,13,30,63,100,247] [0,2],([84,0,1,2,3,41],[7,9,30,72,132],[]),e5 [42] [1,2,7,8,12,13,21,52,64,132,246],([84,75,0,1,3,4],[9,21,26,72,203],[0]),([75,0,1,3,4,41],[7,9,26,70,248],[0,1,2]),e5 [186] [1,2,8,9,12,13,72,203],u5 [76] [9,12,13,26,49,215,249],e5 [187] [1,2,7,12,13,41,132,246,250,251,252],a5 [67] [1,2,7,12,13,26,30,49,83,253] [0,2],a5 [72] [1,2,7,8,12,13,84,198,254] [0,2],([75,0,1,2,5,4],[2,5,9,26,34,72],[0]),u5 [18] [1,2,7,8,12,13,30,34,41,91,132,246,255],([0,1,2,5,4,40],[8,30,49,193,256],[0]),e5 [9,41] [7,9,26,51,52,72,95,132],e5 [9,5] [5,9,25,26,33,34,41],a5 [131,21] [8,13,25,41,132,202,246,257] [0,2],a5 [26,41] [7,9,26,41,51,52,72,115] [0,3],([0,1,9,2,5,4],[5,7,16,49,72,74],[]),a5 [26,28] [41,72,147,199,227] [0,1,3],([19,131,1,2,3,4],[2,12,21,26,49,246,257],[0]),([6,26,1,2,3,4],[2,7,12,25,72,93,105,106,107],[0,1,2]),u5 [9] [2,9,12,25,41,258,259],a5 [27] [8,9,13,21,49,179,180,227] [0,1,2,3],u5 [88] [1,2,7,9,12,21,30,132,144,260],a5 [84,20] [8,9,21,26,38,49,86,97,98,132] [0,1,2],a5 [136] [1,7,8,13,21,261,262,263] [2,3],a5 [88,28] [7,41,72,144,147,199] [0,3],e5 [127] [7,9,13,21,25,49,225,264,265],([131,20,1,2,3,4],[2,8,25,26],[]),a5 [19,167] [8,12,13,25,26,49,72,115,132,233,246,266] [2],a5 [19,5] [7,8,9,12,21,26,27,33,34,49,84,86,96,115] [0,2],a5 [26,125] [9,41,54,72,267,268] [0,1],a5 [84,6] [1,2,9,13,25,26,49,72,110,269] [0,1,2],e5 [75] [1,2,5,7,9,12,13,26,72],e5 [188] [1,8,9,13,26,270],a5 [81] [1,8,9,13,21,30,152,158,159] [0,1],a5 [75,41] [7,9,21,51,52,72,132,203] [1],a5 [75,6] [1,2,8,9,12,13,21,25,41,72,110,117,203,271] [0,2],a5 [11] [8,9,13,21,30,143,161] [0,1],a5 [30] [1,7,8,21,49,272,273] [0,2],a5 [19,21] [1,12,13,25,26,41,115,132,202,246] [0,2],e5 [189] [1,8,9,12,13,21,72,227,274],a5 [26,27] [9,41,49,72,179,180,227] [0,1,3],e5 [190] [7,8,9,13,26,275],a5 [159] [1,2,8,12,13,21,72,86,128,276,277] [0,1],a5 [141,40] [8,49,56,77,239,278,279] [0,1,2,3],a5 [7] [7,8,9,13,21,110,111,112] [0,1],a5 [81,6] [2,7,12,13,25,72,110,152,158] [0,1],a5 [6,7] [12,13,25,72,110,111,112] [0,1],([19,6,1,2,3,4],[12,25,26,30,49,72,96,110],[0,1]),a5 [6,9] [7,9,13,25,72,92,93,95,110,280] [0,2],e5 [26,5] [9,21,33,34,41,49,72],a5 [6,30] [12,13,25,72,176,272,273] [0,1],a5 [59] [7,8,9,13,21,110,189] [0,1],a5 [191] [1,8,21,30,132,281,282] [3],a5 [6,5] [7,8,9,12,13,21,25,33,34,41,72,84,110,132] [0,1,2],a5 [42,41] [7,26,51,52,64,209] [0,1,3],a5 [173] [1,9,12,13,21,25,30,218,283,284] [0,2],u5 [75,20] [2,7,8,21,25,26,97,285],u5 [124] [2,7,9,12,13,41,147,212,213],([0,1,9,5,4],[5,7,9,16,19,25,26,41,74],[0,2]),a5 [26,40] [8,9,12,21,41,49,77,86,106,227,239] [0,1,3],a5 [18,5] [7,9,26,33,34,84,91] [0,2],u5 [9,10] [9,25,26,41,49,79,142],a5 [6,41] [7,9,12,13,25,26,51,52,72,110,132] [0,1,2,3],a5 [131,158] [7,8,13,25,41,72,86,132,246,257,276,286] [0,3],e5 [192] [1,2,9,12,13,41,72,132,246,280,287,288],u5 [168] [2,9,12,25,132,168,289,290],e5 [193] [1,7,8,13,26,291],a5 [19,75] [7,9,12,26,41,49,85,86,96,115,116,271] [0,2],u5 [141] [2,7,8,12,30,72,132,279],a5 [132] [7,9,13,26,292,293] [2,3],a5 [131,41] [7,9,26,41,51,52,86,132,294] [0,3],u5 [5] [7,8,9,12,13,21,26,200,295,296],a5 [84,131] [8,9,26,49,86,98,132,269,294] [2],a5 [93] [2,7,8,9,12,13,21,87,88,297] [0,1],e5 [194] [1,13,41,49,298],a5 [19,9] [7,9,12,26,41,49,86,92,95,96,115] [0,2],e5 [195] [1,7,8,9,13,246,257,299],([75,0,1,9,3,4],[2,5,9,21,25,26,300,301],[0]),a5 [10] [9,12,13,21,26,49,79,95,142] [0,2],([84,0,1,3,5,4],[9,21,26,49,196,302],[0]),u5 [145] [1,2,9,12,13,21,25,95]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_13_7 : checkNodesBT W_13 g_13 F_13 P_13_7 A_13 B_13_6 7 N_13_7 = true := by decide +kernel
def B_13_7 : BT (List (List Nat)) := buildBucketsBT W_13 N_13_7
set_option maxRecDepth 500000 in
lemma B_13_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_13 7 xs.toFinset) B_13_7 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok (buildPoolsSubBT_sound S_13_ok) A_13_ok B_13_6_ok C_13_7
def U_13_8 : List Nat := [1,2,5,7,8,9,12,13,25,26,30,33,34,41,49,51,52,72,84,92,95,96,98,106,110,115,116,132,227,257,269,271,280,294]
def P_13_8 : BT (Option BoundPool) := buildPoolsSubBT 9 W_13 r_13 S_13 ps_13 U_13_8
def N_13_8 : List NodeSpec := [a5 [84] [1,2,9,30,49,98,269] [0,1,2,3],a5 [41] [7,30,51,52] [0,1,2,3],a5 [5] [7,8,26,33,34,49,84] [0,1,2,3],a5 [75] [1,2,5,8,9,26,30,72,116,132,271] [0,1,2,3],a5 [19] [1,2,12,30,96,115] [0,1,2,3],a5 [131] [1,2,8,30,41,257,294] [0,2,3],a5 [26] [1,2,9,30,72,106,227] [0,1,2,3],a5 [9] [9,25,41,72,92,95,132,280] [0,1,2],a5 [6] [1,2,13,30,110] [0,1,2,3]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_13_8 : checkNodesBT W_13 g_13 F_13 P_13_8 A_13 B_13_7 8 N_13_8 = true := by decide +kernel
def B_13_8 : BT (List (List Nat)) := buildBucketsBT W_13 N_13_8
set_option maxRecDepth 500000 in
lemma B_13_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_13 8 xs.toFinset) B_13_8 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok (buildPoolsSubBT_sound S_13_ok) A_13_ok B_13_7_ok C_13_8
def U_13_9 : List Nat := [1,2,30]
def P_13_9 : BT (Option BoundPool) := buildPoolsSubBT 9 W_13 r_13 S_13 ps_13 U_13_9
def N_13_9 : List NodeSpec := [a5 [] [1,2,30] [0,1,2,3]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_13_9 : checkNodesBT W_13 g_13 F_13 P_13_9 A_13 B_13_8 9 N_13_9 = true := by decide +kernel
def B_13_9 : BT (List (List Nat)) := buildBucketsBT W_13 N_13_9
set_option maxRecDepth 500000 in
lemma B_13_9_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_13 9 xs.toFinset) B_13_9 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok (buildPoolsSubBT_sound S_13_ok) A_13_ok B_13_8_ok C_13_9
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_13_ok : forestRootCheck r_13 g_13 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11),(VAR 4,3,19)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_13_in : bucketContainsBT B_13_9 r_13 = true := by decide +kernel
lemma low_13 : Lower r_13 g_13 10 := lower_of_forestBT root_13_ok B_13_9_ok root_13_in
def g_14 := (d 0xfee8f000fee8f000)
def r_14 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_14 : Lower r_14 g_14 8 := by
  exact lift_of_f (z := 0) (o := 16) (other := r_12) (G := g_12) (essPairs := [(VAR 4,3,19)]) (by decide +kernel) low_12
def g_15 := (d 0xfcc08000fcc08000)
def r_15 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_15 : Lower r_15 g_15 8 := by
  have hc : Lower (varsOf 30) (d 0xfcc0c000fcc0c000) 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact lift_of_f (z := 0) (o := 1) (essPairs := [(VAR 0,14,15)]) (by decide +kernel) hc
def g_16 := (d 0xfffefcc0fffefcc0)
def r_16 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_16 : Lower r_16 g_16 8 := by
  have hc : Lower (varsOf 30) (d 0xfffcfcc0fffcfcc0) 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_12
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,16,17)]) (by decide +kernel) hc
def g_17 := (d 0xffe8c000ffe8c000)
def r_17 : List Nat := varsOf 31
def p_17 : List Nat := [14,14,14,15,15,15,19,19,19,21,21,21,22,22,22,23,24,24,25,25,26,26,27,28,28,29]
def q_17 : List Nat := [12,10,6,13,11,7,18,17,3,20,17,5,20,18,6,7,16,8,17,9,18,10,11,20,12,13]
def F_17 : Nat := fullMask 26
set_option maxHeartbeats 0 in
lemma gp_17 : goodPairs g_17 p_17 q_17 := goodPairs_of (by decide +kernel)
def W_17 : BT Decor := buildWiresBT 5 (mkBase p_17 q_17 r_17) [(0,2,4),(3,5,1),(2,2,3),(3,7,1),(0,1,2),(0,1,4),(2,1,3),(0,9,4),(3,9,4),(1,9,3),(0,0,4),(2,0,3)]
lemma W_17_ok : btAll (fun x => faithful p_17 q_17 x ∧ x.1 < 2^256) W_17 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_17 : List (List (Nat × Nat)) := [[],[(1,2)]]
def A_17 : BT (List (Nat × Nat)) := btOfList 1 al_17
set_option maxHeartbeats 0 in
lemma A_17_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_17 = g_17) A_17 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_17_0 : Slice r_17 g_17 (subcubeFast 0 1) 6 := by
  have hc : Lower (varsOf 30) (d 0xfffcc000fffcc000) 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_1 : Slice r_17 g_17 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) (d 0xffc0c000ffc0c000) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_2 : Slice r_17 g_17 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) (d 0xfffaf000fffaf000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_3 : Slice r_17 g_17 (subcubeFast 0 4) 5 := by
  have hc : Lower (varsOf 27) (d 0xffeecc00ffeecc00) 5 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_4 : Slice r_17 g_17 (subcubeFast 8 0) 5 := by
  have hc : Lower (varsOf 23) (d 0xe8e80000e8e80000) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_5 : Slice r_17 g_17 (subcubeFast 0 16) 5 := by
  exact slice_fast_direct_f (z := 0) (o := 16) (by decide +kernel) low_3
set_option maxHeartbeats 0 in
lemma sl_17_6 : Slice r_17 g_17 (subcubeFast 8 16) 4 := by
  exact slice_fast_direct_f (z := 8) (o := 16) (by decide +kernel) low_0
set_option maxHeartbeats 0 in
lemma sl_17_7 : Slice r_17 g_17 (subcubeFast 1 4) 4 := by
  have hc : Lower (varsOf 26) (d 0xffcccc00ffcccc00) 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_17_8 : Slice r_17 g_17 (identDom 2 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xf8f8c0c0f8f8c0c0) 5 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_9
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
def S_17 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 0 1,6),some (subcubeFast 1 0,5),some (subcubeFast 0 2,5),some (subcubeFast 0 4,5),some (subcubeFast 8 0,5),some (subcubeFast 0 16,5),some (subcubeFast 8 16,4),some (subcubeFast 1 4,4),some (identDom 2 3,5)]
lemma S_17_ok : btAll (fun o => ∀ p, o = some p → Slice r_17 g_17 p.1 p.2) S_17 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_17_0) (forall_cons (fun _ h => by cases h; exact sl_17_1) (forall_cons (fun _ h => by cases h; exact sl_17_2) (forall_cons (fun _ h => by cases h; exact sl_17_3) (forall_cons (fun _ h => by cases h; exact sl_17_4) (forall_cons (fun _ h => by cases h; exact sl_17_5) (forall_cons (fun _ h => by cases h; exact sl_17_6) (forall_cons (fun _ h => by cases h; exact sl_17_7) (forall_cons (fun _ h => by cases h; exact sl_17_8) (fun _ h => (List.not_mem_nil h).elim))))))))))
def ps_17 : BT (Option PoolSpec) := btOfList 4 [q 3 [],q 5 [],q 4 [],q 0 [],q 1 [],q 8 [],q 0 [16388],q 6 [],q 2 [],q 0 [12294],q 0 [8196],q 7 []]
def B_17_4 : BT (List (List Nat)) := BT.empty
lemma B_17_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 4 xs.toFinset) B_17_4 := .empty
def U_17_5 : List Nat := (r 0 6)
def P_17_5 : BT (Option BoundPool) := buildPoolsSubBT 4 W_17 r_17 S_17 ps_17 U_17_5
def N_17_5 : List NodeSpec := [e5 [6] [],e5 [8] [],([0,9,10,2,3,4],[0,1],[]),([11,0,9,2,3,4],[0,2],[]),e5 [12] (r 2 4),e5 [13] [3,4],e5 [14] [3,4]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_5 : checkNodesBT W_17 g_17 F_17 P_17_5 A_17 B_17_4 5 N_17_5 = true := by decide +kernel
def B_17_5 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_5
set_option maxRecDepth 500000 in
lemma B_17_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 5 xs.toFinset) B_17_5 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_4_ok C_17_5
def U_17_6 : List Nat := (r 0 12)
def P_17_6 : BT (Option BoundPool) := buildPoolsSubBT 4 W_17 r_17 S_17 ps_17 U_17_6
def N_17_6 : List NodeSpec := [a5 [10] [0,6,7,8] [0,1],a5 [11] [0,2,5,7,8,9] [0,1],a5 [9] [1,2,4,5,8,10,11] [0,1],([15,1,2,3,4],[4,7,11],[]),([16,1,2,3,4],[3,4,7,11],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_6 : checkNodesBT W_17 g_17 F_17 P_17_6 A_17 B_17_5 6 N_17_6 = true := by decide +kernel
def B_17_6 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_6
set_option maxRecDepth 500000 in
lemma B_17_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 6 xs.toFinset) B_17_6 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_5_ok C_17_6
def U_17_7 : List Nat := (r 0 4++[7,8])
def P_17_7 : BT (Option BoundPool) := buildPoolsSubBT 4 W_17 r_17 S_17 ps_17 U_17_7
def N_17_7 : List NodeSpec := [a5 [] (r 0 4++[7,8]) [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_17_7 : checkNodesBT W_17 g_17 F_17 P_17_7 A_17 B_17_6 7 N_17_7 = true := by decide +kernel
def B_17_7 : BT (List (List Nat)) := buildBucketsBT W_17 N_17_7
set_option maxRecDepth 500000 in
lemma B_17_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_17 7 xs.toFinset) B_17_7 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok (buildPoolsSubBT_sound S_17_ok) A_17_ok B_17_6_ok C_17_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_17_ok : forestRootCheck r_17 g_17 [(VAR 0,18,19),(VAR 1,12,14),(VAR 2,10,14),(VAR 3,6,14),(VAR 4,3,19)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_17_in : bucketContainsBT B_17_7 r_17 = true := by decide +kernel
lemma low_17 : Lower r_17 g_17 8 := lower_of_forestBT root_17_ok B_17_7_ok root_17_in
def g_18 := (d 0xfffafc80fffafc80)
def r_18 : List Nat := varsOf 31
def p_18 : List Nat := [7,7,7,10,10,11,11,12,12,13,13,14,17,17,19,19,20,20,21,22,22,24,24,25,26]
def q_18 : List Nat := [6,5,3,8,2,9,3,8,4,9,5,6,16,1,18,3,16,4,5,18,6,16,8,9,18]
def F_18 : Nat := fullMask 25
set_option maxHeartbeats 0 in
lemma gp_18 : goodPairs g_18 p_18 q_18 := goodPairs_of (by decide +kernel)
def W_18 : BT Decor := buildWiresBT 5 (mkBase p_18 q_18 r_18) [(1,2,3),(1,2,4),(1,3,4),(2,1,4),(3,8,5),(2,2,4),(1,10,3),(2,5,4),(1,5,4),(0,0,6),(2,2,3),(3,2,7),(1,1,4)]
lemma W_18_ok : btAll (fun x => faithful p_18 q_18 x ∧ x.1 < 2^256) W_18 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_18 : List (List (Nat × Nat)) := [[],[(0,1),(3,4)]]
def A_18 : BT (List (Nat × Nat)) := btOfList 1 al_18
set_option maxHeartbeats 0 in
lemma A_18_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_18 = g_18) A_18 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_18_0 : Slice r_18 g_18 (identDom 0 1) 7 := by
  have hc : Lower (varsOf 29) (d 0xfffafaa0fffafaa0) 7 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_12
  exact slice_ident (u := 0) (v := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_1 : Slice r_18 g_18 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) (d 0xfffffcc0fffffcc0) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_2 : Slice r_18 g_18 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) (d 0xfff0fc00fff0fc00) 5 := carry_of (swaps := [(0,4),(1,4),(2,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_3 : Slice r_18 g_18 (subcubeFast 16 0) 5 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_9
set_option maxHeartbeats 0 in
lemma sl_18_4 : Slice r_18 g_18 (subcubeFast 8 0) 5 := by
  have hc : Lower (varsOf 23) (d 0xfafa8080fafa8080) 5 := carry_of (swaps := [(0,1),(3,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_5 : Slice r_18 g_18 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) (d 0xfffaffa0fffaffa0) 5 := carry_of (swaps := [(1,4),(2,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_6 : Slice r_18 g_18 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) (d 0xfffaf000fffaf000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_7 : Slice r_18 g_18 (subcubeFast 3 0) 4 := by
  have hc : Lower (varsOf 28) (d 0xfff0f000fff0f000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 3) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_8 : Slice r_18 g_18 (subcubeFast 16 1) 4 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_9 : Slice r_18 g_18 (subcubeFast 8 2) 4 := by
  have hc : Lower (varsOf 21) (d 0xfafaa0a0fafaa0a0) 4 := carry_of (swaps := [(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 8) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_18_10 : Slice r_18 g_18 (subcubeFast 4 0) 4 := by
  have hc : Lower (varsOf 27) (d 0xffaacc00ffaacc00) 4 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_10
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
def S_18 : BT (Option (Nat × Nat)) := btOfList 4 [some (identDom 0 1,7),some (subcubeFast 0 1,5),some (subcubeFast 1 0,5),some (subcubeFast 16 0,5),some (subcubeFast 8 0,5),some (subcubeFast 0 2,5),some (subcubeFast 2 0,5),some (subcubeFast 3 0,4),some (subcubeFast 16 1,4),some (subcubeFast 8 2,4),some (subcubeFast 4 0,4)]
lemma S_18_ok : btAll (fun o => ∀ p, o = some p → Slice r_18 g_18 p.1 p.2) S_18 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_18_0) (forall_cons (fun _ h => by cases h; exact sl_18_1) (forall_cons (fun _ h => by cases h; exact sl_18_2) (forall_cons (fun _ h => by cases h; exact sl_18_3) (forall_cons (fun _ h => by cases h; exact sl_18_4) (forall_cons (fun _ h => by cases h; exact sl_18_5) (forall_cons (fun _ h => by cases h; exact sl_18_6) (forall_cons (fun _ h => by cases h; exact sl_18_7) (forall_cons (fun _ h => by cases h; exact sl_18_8) (forall_cons (fun _ h => by cases h; exact sl_18_9) (forall_cons (fun _ h => by cases h; exact sl_18_10) (fun _ h => (List.not_mem_nil h).elim))))))))))))
def ps_18 : BT (Option PoolSpec) := btOfList 5 [q 3 [],q 4 [],q 6 [],q 5 [],q 2 [],q 1 [],q 3 [24576],q 4 [16390],q 8 [],q 10 [],q 9 [],q 5 [12297],q 0 [16390],q 2 [16390],q 1 [16390],q 7 [],q 1 [16394],q 2 [16389],q 1 [16389],q 0 []]
def B_18_3 : BT (List (List Nat)) := BT.empty
lemma B_18_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_18 3 xs.toFinset) B_18_3 := .empty
def U_18_4 : List Nat := [0,1]
def P_18_4 : BT (Option BoundPool) := buildPoolsSubBT 5 W_18 r_18 S_18 ps_18 U_18_4
def N_18_4 : List NodeSpec := [([0,1,5,6,7],[0,1],[]),([0,2,3,9,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_18_4 : checkNodesBT W_18 g_18 F_18 P_18_4 A_18 B_18_3 4 N_18_4 = true := by decide +kernel
def B_18_4 : BT (List (List Nat)) := buildBucketsBT W_18 N_18_4
set_option maxRecDepth 500000 in
lemma B_18_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_18 4 xs.toFinset) B_18_4 :=
  buildBucketsBT_sound (by decide) gp_18 W_18_ok (buildPoolsSubBT_sound S_18_ok) A_18_ok B_18_3_ok C_18_4
def U_18_5 : List Nat := (r 0 10)
def P_18_5 : BT (Option BoundPool) := buildPoolsSubBT 5 W_18 r_18 S_18 ps_18 U_18_5
def N_18_5 : List NodeSpec := [e5 [11] [2,3],e5 [12] [2,3],e5 [13] (r 2 4),([10,0,1,3,5,4],[1],[]),([14,1,2,3,4,6],[5,6],[]),([8,15,0,2,3,4],[7],[]),e5 [16] [],([0,1,2,3,6,7],[1,8,9],[0]),([0,1,3,5,4,6],[0,1],[0]),([8,0,2,3,5,4],[2,7],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_18_5 : checkNodesBT W_18 g_18 F_18 P_18_5 A_18 B_18_4 5 N_18_5 = true := by decide +kernel
def B_18_5 : BT (List (List Nat)) := buildBucketsBT W_18 N_18_5
set_option maxRecDepth 500000 in
lemma B_18_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_18 5 xs.toFinset) B_18_5 :=
  buildBucketsBT_sound (by decide) gp_18 W_18_ok (buildPoolsSubBT_sound S_18_ok) A_18_ok B_18_4_ok C_18_5
def U_18_6 : List Nat := (r 0 6++r 7 12)
def P_18_6 : BT (Option BoundPool) := buildPoolsSubBT 5 W_18 r_18 S_18 ps_18 U_18_6
def N_18_6 : List NodeSpec := [a5 [7] [1,8,9,10] [0,1],a5 [5] (r 0 6++[9,10,11]) [0,1],([8,0,2,3,4],([0,2,7,8]++r 12 4),[0]),a5 [10] (r 0 6++[8,9,16]) [0,1],([0,2,3,4,17],[8,10,17,18],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_18_6 : checkNodesBT W_18 g_18 F_18 P_18_6 A_18 B_18_5 6 N_18_6 = true := by decide +kernel
def B_18_6 : BT (List (List Nat)) := buildBucketsBT W_18 N_18_6
set_option maxRecDepth 500000 in
lemma B_18_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_18 6 xs.toFinset) B_18_6 :=
  buildBucketsBT_sound (by decide) gp_18 W_18_ok (buildPoolsSubBT_sound S_18_ok) A_18_ok B_18_5_ok C_18_6
def U_18_7 : List Nat := (r 0 6++[19])
def P_18_7 : BT (Option BoundPool) := buildPoolsSubBT 5 W_18 r_18 S_18 ps_18 U_18_7
def N_18_7 : List NodeSpec := [a5 [] (r 0 6++[19]) [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_18_7 : checkNodesBT W_18 g_18 F_18 P_18_7 A_18 B_18_6 7 N_18_7 = true := by decide +kernel
def B_18_7 : BT (List (List Nat)) := buildBucketsBT W_18 N_18_7
set_option maxRecDepth 500000 in
lemma B_18_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_18 7 xs.toFinset) B_18_7 :=
  buildBucketsBT_sound (by decide) gp_18 W_18_ok (buildPoolsSubBT_sound S_18_ok) A_18_ok B_18_6_ok C_18_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_18_ok : forestRootCheck r_18 g_18 [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,2,10),(VAR 4,1,17)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_18_in : bucketContainsBT B_18_7 r_18 = true := by decide +kernel
lemma low_18 : Lower r_18 g_18 8 := lower_of_forestBT root_18_ok B_18_7_ok root_18_in
def g_19 := (d 0xffe08000ffe08000)
def r_19 : List Nat := varsOf 31
def p_19 : List Nat := [15,15,15,15,21,21,21,22,22,22,23,23,24,24,25,25,26,26,27,27,28,28,29,30]
def q_19 : List Nat := [14,13,11,7,20,17,5,20,18,6,19,7,16,8,17,9,18,10,19,11,20,12,13,14]
def F_19 : Nat := fullMask 24
set_option maxHeartbeats 0 in
lemma gp_19 : goodPairs g_19 p_19 q_19 := goodPairs_of (by decide +kernel)
def W_19 : BT Decor := buildWiresBT 6 (mkBase p_19 q_19 r_19) [(1,3,4),(0,2,5),(0,0,6),(0,1,6),(0,3,4),(2,2,9),(0,10,5),(3,9,5),(2,12,1),(0,12,0),(3,1,6),(3,1,5),(0,0,3),(1,17,4),(0,2,18),(0,0,5),(0,1,5),(1,1,9),(0,10,0),(0,10,1),(0,17,4),(3,25,0),(3,3,4),(3,9,3),(2,0,3),(2,0,4),(3,30,3),(3,29,4),(0,1,3),(0,33,4),(3,34,2),(1,33,4),(0,0,36),(0,0,4),(1,29,4),(2,1,9),(2,1,3),(3,41,0),(2,1,4),(3,43,3),(2,0,44),(3,28,1),(3,46,0),(2,2,31),(2,10,1),(3,34,0),(3,27,0),(3,28,0),(3,33,4),(3,41,4),(0,1,4),(3,55,0),(1,38,3),(1,30,3),(3,55,3),(2,17,4)]
lemma W_19_ok : btAll (fun x => faithful p_19 q_19 x ∧ x.1 < 2^256) W_19 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_19 : List (List (Nat × Nat)) := [[],[(0,1)]]
def A_19 : BT (List (Nat × Nat)) := btOfList 1 al_19
set_option maxHeartbeats 0 in
lemma A_19_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_19 = g_19) A_19 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_19_0 : Slice r_19 g_19 (subcubeFast 0 4) 6 := by
  have hc : Lower (varsOf 27) (d 0xffee8800ffee8800) 6 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_19_1 : Slice r_19 g_19 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) (d 0xfff0c000fff0c000) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_19_2 : Slice r_19 g_19 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) (d 0xfff0a000fff0a000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_19_3 : Slice r_19 g_19 (subcubeFast 0 3) 4 := by
  have hc : Lower (varsOf 28) (d 0xfff0f000fff0f000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 0) (o := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_19_4 : Slice r_19 g_19 (identDom 1 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xecec8080ecec8080) 5 := carry_of (swaps := [(1,2),(3,4)]) (by decide +kernel) low_8
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_19_5 : Slice r_19 g_19 (identDom 0 3) 5 := by
  have hc : Lower (varsOf 23) (d 0xeaea8080eaea8080) 5 := carry_of (swaps := [(0,2),(1,2),(3,4)]) (by decide +kernel) low_8
  exact slice_ident (u := 0) (v := 3) (by decide +kernel) hc
def S_19 : BT (Option (Nat × Nat)) := btOfList 3 [some (subcubeFast 0 4,6),some (subcubeFast 0 1,5),some (subcubeFast 0 2,5),some (subcubeFast 0 3,4),some (identDom 1 3,5),some (identDom 0 3,5)]
lemma S_19_ok : btAll (fun o => ∀ p, o = some p → Slice r_19 g_19 p.1 p.2) S_19 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_19_0) (forall_cons (fun _ h => by cases h; exact sl_19_1) (forall_cons (fun _ h => by cases h; exact sl_19_2) (forall_cons (fun _ h => by cases h; exact sl_19_3) (forall_cons (fun _ h => by cases h; exact sl_19_4) (forall_cons (fun _ h => by cases h; exact sl_19_5) (fun _ h => (List.not_mem_nil h).elim)))))))
def ps_19 : BT (Option PoolSpec) := btOfList 5 [q 0 [16396,16397,20519],q 0 [16396,16397],q 0 [16398,16399],q 0 [],q 4 [],q 3 [],q 0 [16397,20487],q 0 [16397,20480],q 2 [],q 1 [],q 0 [12294,167],q 5 [],q 2 [16386],q 0 [16388,223],q 0 [16396,36866],q 2 [223],q 2 [12288],q 0 [16396,36869],q 0 [16399],q 0 [16398],q 0 [16397],q 0 [16396],q 0 [16386],q 0 [16384],q 0 [12290],q 0 [12288]]
def B_19_1 : BT (List (List Nat)) := BT.empty
lemma B_19_1_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_19 1 xs.toFinset) B_19_1 := .empty
def U_19_2 : List Nat := []
def P_19_2 : BT (Option BoundPool) := buildPoolsSubBT 5 W_19 r_19 S_19 ps_19 U_19_2
def N_19_2 : List NodeSpec := [([7,8,9],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_19_2 : checkNodesBT W_19 g_19 F_19 P_19_2 A_19 B_19_1 2 N_19_2 = true := by decide +kernel
def B_19_2 : BT (List (List Nat)) := buildBucketsBT W_19 N_19_2
set_option maxRecDepth 500000 in
lemma B_19_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_19 2 xs.toFinset) B_19_2 :=
  buildBucketsBT_sound (by decide) gp_19 W_19_ok (buildPoolsSubBT_sound S_19_ok) A_19_ok B_19_1_ok C_19_2
def U_19_3 : List Nat := []
def P_19_3 : BT (Option BoundPool) := buildPoolsSubBT 5 W_19 r_19 S_19 ps_19 U_19_3
def N_19_3 : List NodeSpec := [([11,12,0,1],[],[]),([13,12,0,2],[],[]),([14,12,1,2],[],[]),([15,0,6,9],[],[]),([7,1,6,9],[],[0]),([12,16,0,2],[],[]),([16,0,6,9],[],[]),([0,1,19,9],[],[]),([20,21,2,9],[],[]),([20,1,6,9],[],[]),([12,0,1,6],[],[]),([0,6,9,22],[],[]),([12,0,2,22],[],[]),([7,8,3,4],[],[0]),([12,20,1,2],[],[]),([23,24,3,4],[],[]),([0,1,6,9],[],[]),([11,0,1,9],[],[]),([26,1,6,9],[],[]),([26,12,1,2],[],[]),([10,12,0,1],[],[]),([12,0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_19_3 : checkNodesBT W_19 g_19 F_19 P_19_3 A_19 B_19_2 3 N_19_3 = true := by decide +kernel
def B_19_3 : BT (List (List Nat)) := buildBucketsBT W_19 N_19_3
set_option maxRecDepth 500000 in
lemma B_19_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_19 3 xs.toFinset) B_19_3 :=
  buildBucketsBT_sound (by decide) gp_19 W_19_ok (buildPoolsSubBT_sound S_19_ok) A_19_ok B_19_2_ok C_19_3
def U_19_4 : List Nat := [0,1]
def P_19_4 : BT (Option BoundPool) := buildPoolsSubBT 5 W_19 r_19 S_19 ps_19 U_19_4
def N_19_4 : List NodeSpec := [([27,12,0,1,2],[],[]),([28,12,0,1,2],[],[]),([10,0,1,3,4],[],[]),([28,0,1,6,3],[],[0]),([15,0,6,3,4],[],[0]),([7,1,6,3,4],[],[0]),([16,0,6,3,4],[],[0]),([20,1,6,3,4],[],[0]),([20,21,2,3,4],[],[0]),([27,20,1,2,4],[],[]),([12,0,1,2,4],[],[]),([12,0,1,2,3],[],[]),([0,1,6,9,3],[],[]),([12,0,1,2,5],[0],[0,1]),([12,0,1,2,9],[0],[0,1]),([29,1,2,31,4],[],[]),([0,1,6,9,4],[],[]),([30,1,2,3,32],[],[]),([35,0,1,3,4],[],[]),([27,0,1,6,4],[],[0]),([37,1,2,3,4],[],[]),([38,1,2,3,18],[],[]),([27,0,1,2,39],[],[]),([26,40,2,3,4],[],[]),([20,1,2,9,4],[],[]),([26,1,2,9,5],[],[0]),([16,20,2,3,4],[],[]),([27,42,1,2,4],[],[]),([45,1,2,3,4],[],[]),([26,1,2,3,4],[],[]),([0,1,2,9,18],[],[0]),([10,0,3,22,4],[],[]),([47,1,2,3,4],[],[]),([0,1,19,3,4],[],[0]),([26,2,3,22,4],[],[]),([0,2,9,22,5],[],[0]),([48,0,1,3,4],[],[]),([26,10,1,3,4],[],[]),([23,10,1,3,4],[],[0]),([12,0,1,2],[0],[0,1]),([42,1,2,9,4],[],[]),([49,10,0,3,4],[],[]),([10,0,1,9,5],[],[0]),([20,1,2,9,5],[],[0]),([0,1,2,9,5],[],[0]),([50,1,2,3,4],[],[]),([28,27,0,1,2],[],[0]),([16,0,2,9,5],[],[0]),([0,1,6,9],[1],[0,1]),([0,1,6,3,4],[],[0]),([0,1,6,9,5],[],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_19_4 : checkNodesBT W_19 g_19 F_19 P_19_4 A_19 B_19_3 4 N_19_4 = true := by decide +kernel
def B_19_4 : BT (List (List Nat)) := buildBucketsBT W_19 N_19_4
set_option maxRecDepth 500000 in
lemma B_19_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_19 4 xs.toFinset) B_19_4 :=
  buildBucketsBT_sound (by decide) gp_19 W_19_ok (buildPoolsSubBT_sound S_19_ok) A_19_ok B_19_3_ok C_19_4
def U_19_5 : List Nat := (r 1 17)
def P_19_5 : BT (Option BoundPool) := buildPoolsSubBT 5 W_19 r_19 S_19 ps_19 U_19_5
def N_19_5 : List NodeSpec := [e5 [51] [],([28,27,0,1,2,4],[],[0]),([28,27,0,1,2],[2],[0]),([27,0,1,2,4,5],[3],[0,1]),([0,1,6,3,4,5],[3],[0,1]),([0,1,6,3,4],[],[0,1]),([16,0,2,3,4,5],[4,5,6],[0]),e5 [20] [],([20,1,2,3,4],[7],[0]),a5 [52] [8] [1],([0,1,2,9,4,5],[],[0,1]),a5 [9] [3,8,9] [0,1],([0,1,2,9,5],[1],[0,1]),u5 [27] [],u5 [39] [9],([17,0,1,2,9,4],[9],[0]),([42,1,2,3,4],[10],[0]),([29,0,1,2,9,4],[9],[1]),([27,17,0,1,2,4],[9],[]),a5 [18] [3,8,11] [0,1],([10,0,1,3,4],[],[0,1]),([20,1,2,3,4,5],[7,9],[0]),e5 [53] [],([30,29,1,2,3,4],[12],[0]),a5 [54] [] [1],([56,1,2,3,4],[13],[]),([28,0,1,2,3,5],[3],[0]),([26,1,2,9,3,4],[9,14],[0]),a5 [25] [3,8] [0,1],([56,55,1,2,3,4],[9,15],[]),([28,0,1,2,9,4],[3],[0]),([29,27,0,1,2,4],[9],[0,1]),e5 [57] [11],([28,27,0,1,2,3],[],[0]),([0,1,2,9,3,5],[],[0]),a5 [44] [3,9] [0,1],e5 [58] [],([17,38,1,2,3,4],[11,16],[0]),e5 [59] [],([0,2,9,3,22,4],[5,17],[0,1]),e5 [60] [],([30,38,1,2,3,4],[3,5,9],[]),([26,1,2,3,4],[14],[]),u5 [5] [3,4,8,9,11],e5 [26] [],([10,0,1,9,3,4],[3],[0,1]),u5 [28] [],([27,0,1,2,9,3],[3],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_19_5 : checkNodesBT W_19 g_19 F_19 P_19_5 A_19 B_19_4 5 N_19_5 = true := by decide +kernel
def B_19_5 : BT (List (List Nat)) := buildBucketsBT W_19 N_19_5
set_option maxRecDepth 500000 in
lemma B_19_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_19 5 xs.toFinset) B_19_5 :=
  buildBucketsBT_sound (by decide) gp_19 W_19_ok (buildPoolsSubBT_sound S_19_ok) A_19_ok B_19_4_ok C_19_5
def U_19_6 : List Nat := ([3,4,5,8,9,11]++r 18 8)
def P_19_6 : BT (Option BoundPool) := buildPoolsSubBT 5 W_19 r_19 S_19 ps_19 U_19_6
def N_19_6 : List NodeSpec := [a5 [27] [4,8,9,11,18] [0,1],a5 [28] [8,9,19] [0,1],a5 [5] [4,8,9,11,20] [0,1],a5 [9] [8,9,21] [0,1],a5 [30] [5,9,11,22] [0,1],a5 [38] [5,9,11,23] [0,1],a5 [29] [3,5,8,9,11,24] [0,1],a5 [17] [5,11,25] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_19_6 : checkNodesBT W_19 g_19 F_19 P_19_6 A_19 B_19_5 6 N_19_6 = true := by decide +kernel
def B_19_6 : BT (List (List Nat)) := buildBucketsBT W_19 N_19_6
set_option maxRecDepth 500000 in
lemma B_19_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_19 6 xs.toFinset) B_19_6 :=
  buildBucketsBT_sound (by decide) gp_19 W_19_ok (buildPoolsSubBT_sound S_19_ok) A_19_ok B_19_5_ok C_19_6
def U_19_7 : List Nat := [3,5]
def P_19_7 : BT (Option BoundPool) := buildPoolsSubBT 5 W_19 r_19 S_19 ps_19 U_19_7
def N_19_7 : List NodeSpec := [a5 [] [3,5] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_19_7 : checkNodesBT W_19 g_19 F_19 P_19_7 A_19 B_19_6 7 N_19_7 = true := by decide +kernel
def B_19_7 : BT (List (List Nat)) := buildBucketsBT W_19 N_19_7
set_option maxRecDepth 500000 in
lemma B_19_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_19 7 xs.toFinset) B_19_7 :=
  buildBucketsBT_sound (by decide) gp_19 W_19_ok (buildPoolsSubBT_sound S_19_ok) A_19_ok B_19_6_ok C_19_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_19_ok : forestRootCheck r_19 g_19 [(VAR 0,14,15),(VAR 1,13,15),(VAR 2,11,15),(VAR 3,7,15),(VAR 4,5,21)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_19_in : bucketContainsBT B_19_7 r_19 = true := by decide +kernel
lemma low_19 : Lower r_19 g_19 8 := lower_of_forestBT root_19_ok B_19_7_ok root_19_in
def g_20 := (d 0xfeecf800feecf800)
def r_20 : List Nat := varsOf 31
def p_20 : List Nat := [11,11,11,12,12,13,13,14,14,15,18,18,19,19,21,21,21,22,22,23,25,25,25,26,26,28,28]
def q_20 : List Nat := [10,9,3,8,4,9,5,10,6,7,16,2,17,3,20,17,5,20,6,7,24,17,9,24,10,24,20]
def F_20 : Nat := fullMask 27
set_option maxHeartbeats 0 in
lemma gp_20 : goodPairs g_20 p_20 q_20 := goodPairs_of (by decide +kernel)
def W_20 : BT Decor := buildWiresBT 4 (mkBase p_20 q_20 r_20) [(0,3,4),(2,0,5),(0,0,3),(0,0,4),(3,8,3),(0,7,4),(1,1,2)]
lemma W_20_ok : btAll (fun x => faithful p_20 q_20 x ∧ x.1 < 2^256) W_20 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_20 : List (List (Nat × Nat)) := [[],[(1,2),(3,4)]]
def A_20 : BT (List (Nat × Nat)) := btOfList 1 al_20
set_option maxHeartbeats 0 in
lemma A_20_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_20 = g_20) A_20 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_20_0 : Slice r_20 g_20 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) (d 0xfffcfc00fffcfc00) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_20_1 : Slice r_20 g_20 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) (d 0xfaa0f000faa0f000) 5 := carry_of (swaps := [(1,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_20_2 : Slice r_20 g_20 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) (d 0xeecc8800eecc8800) 5 := carry_of (swaps := [(1,2),(2,4),(3,4)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_20_3 : Slice r_20 g_20 (subcubeFast 0 8) 5 := by
  have hc : Lower (varsOf 23) (d 0xfefef8f8fefef8f8) 5 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_20_4 : Slice r_20 g_20 (subcubeFast 0 16) 5 := by
  have hc : Lower (varsOf 15) (d 0xfeecfeecfeecfeec) 5 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_3
  exact slice_fast_direct_f (z := 0) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_20_5 : Slice r_20 g_20 (subcubeFast 4 1) 4 := by
  have hc : Lower (varsOf 26) (d 0xffcccc00ffcccc00) 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_20_6 : Slice r_20 g_20 (subcubeFast 2 16) 4 := by
  have hc : Lower (varsOf 13) (d 0xfaa0faa0faa0faa0) 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 2) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_20_7 : Slice r_20 g_20 (subcubeFast 4 8) 4 := by
  have hc : Lower (varsOf 19) (d 0xeeee8888eeee8888) 4 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_20_8 : Slice r_20 g_20 (subcubeFast 2 1) 4 := by
  have hc : Lower (varsOf 28) (d 0xfff0f000fff0f000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 2) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_20_9 : Slice r_20 g_20 (identDom 1 3) 6 := by
  have hc : Lower (varsOf 23) (d 0xececc8c8ececc8c8) 6 := carry_of (swaps := [(1,3),(2,3),(3,4)]) (by decide +kernel) low_2
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_20_10 : Slice r_20 g_20 (identDom 2 4) 6 := by
  have hc : Lower (varsOf 15) (d 0xf8e0f8e0f8e0f8e0) 6 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_2
  exact slice_ident (u := 2) (v := 4) (by decide +kernel) hc
def S_20 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 0 1,5),some (subcubeFast 2 0,5),some (subcubeFast 4 0,5),some (subcubeFast 0 8,5),some (subcubeFast 0 16,5),some (subcubeFast 4 1,4),some (subcubeFast 2 16,4),some (subcubeFast 4 8,4),some (subcubeFast 2 1,4),some (identDom 1 3,6),some (identDom 2 4,6)]
lemma S_20_ok : btAll (fun o => ∀ p, o = some p → Slice r_20 g_20 p.1 p.2) S_20 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_20_0) (forall_cons (fun _ h => by cases h; exact sl_20_1) (forall_cons (fun _ h => by cases h; exact sl_20_2) (forall_cons (fun _ h => by cases h; exact sl_20_3) (forall_cons (fun _ h => by cases h; exact sl_20_4) (forall_cons (fun _ h => by cases h; exact sl_20_5) (forall_cons (fun _ h => by cases h; exact sl_20_6) (forall_cons (fun _ h => by cases h; exact sl_20_7) (forall_cons (fun _ h => by cases h; exact sl_20_8) (forall_cons (fun _ h => by cases h; exact sl_20_9) (forall_cons (fun _ h => by cases h; exact sl_20_10) (fun _ h => (List.not_mem_nil h).elim))))))))))))
def ps_20 : BT (Option PoolSpec) := btOfList 4 [q 3 [],q 4 [],q 9 [],q 1 [],q 10 [],q 2 [],q 0 [],q 6 [],q 7 [],q 0 [8197],q 5 [],q 3 [8197],q 8 []]
def B_20_4 : BT (List (List Nat)) := BT.empty
lemma B_20_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_20 4 xs.toFinset) B_20_4 := .empty
def U_20_5 : List Nat := (r 0 6)
def P_20_5 : BT (Option BoundPool) := buildPoolsSubBT 4 W_20 r_20 S_20 ps_20 U_20_5
def N_20_5 : List NodeSpec := [e5 [6] [],([7,8,1,2,3,4],[0,1],[]),e5 [9] [],e5 [10] (r 2 4)]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_20_5 : checkNodesBT W_20 g_20 F_20 P_20_5 A_20 B_20_4 5 N_20_5 = true := by decide +kernel
def B_20_5 : BT (List (List Nat)) := buildBucketsBT W_20 N_20_5
set_option maxRecDepth 500000 in
lemma B_20_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_20 5 xs.toFinset) B_20_5 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok (buildPoolsSubBT_sound S_20_ok) A_20_ok B_20_4_ok C_20_5
def U_20_6 : List Nat := ([0,1,3]++r 5 8)
def P_20_6 : BT (Option BoundPool) := buildPoolsSubBT 4 W_20 r_20 S_20 ps_20 U_20_6
def N_20_6 : List NodeSpec := [u5 [5] ([3]++r 5 4),e5 [11] ([3]++r 7 5),a5 [7] [0,1,3,5,10,12] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_20_6 : checkNodesBT W_20 g_20 F_20 P_20_6 A_20 B_20_5 6 N_20_6 = true := by decide +kernel
def B_20_6 : BT (List (List Nat)) := buildBucketsBT W_20 N_20_6
set_option maxRecDepth 500000 in
lemma B_20_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_20 6 xs.toFinset) B_20_6 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok (buildPoolsSubBT_sound S_20_ok) A_20_ok B_20_5_ok C_20_6
def U_20_7 : List Nat := (r 0 9++[10,12])
def P_20_7 : BT (Option BoundPool) := buildPoolsSubBT 4 W_20 r_20 S_20 ps_20 U_20_7
def N_20_7 : List NodeSpec := [a5 [] (r 0 9++[10,12]) [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_20_7 : checkNodesBT W_20 g_20 F_20 P_20_7 A_20 B_20_6 7 N_20_7 = true := by decide +kernel
def B_20_7 : BT (List (List Nat)) := buildBucketsBT W_20 N_20_7
set_option maxRecDepth 500000 in
lemma B_20_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_20 7 xs.toFinset) B_20_7 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok (buildPoolsSubBT_sound S_20_ok) A_20_ok B_20_6_ok C_20_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_20_ok : forestRootCheck r_20 g_20 [(VAR 0,10,11),(VAR 1,9,11),(VAR 2,8,12),(VAR 3,3,11),(VAR 4,2,18)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_20_in : bucketContainsBT B_20_7 r_20 = true := by decide +kernel
lemma low_20 : Lower r_20 g_20 8 := lower_of_forestBT root_20_ok B_20_7_ok root_20_in
def g_21 := (d 0xffe8f000ffe8f000)
def r_21 : List Nat := varsOf 31
def p_21 : List Nat := [12,12,13,13,14,14,15,15,19,19,19,21,21,21,22,22,22,23,24,24,25,25,26,26,27,28]
def q_21 : List Nat := [8,4,9,5,10,6,11,7,18,17,3,20,17,5,20,18,6,7,16,8,17,9,18,10,11,20]
def F_21 : Nat := fullMask 26
set_option maxHeartbeats 0 in
lemma gp_21 : goodPairs g_21 p_21 q_21 := goodPairs_of (by decide +kernel)
def W_21 : BT Decor := buildWiresBT 4 (mkBase p_21 q_21 r_21) [(0,2,4),(3,5,4),(2,2,3),(1,2,3),(3,1,4),(0,0,4),(2,0,3),(1,1,3)]
lemma W_21_ok : btAll (fun x => faithful p_21 q_21 x ∧ x.1 < 2^256) W_21 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_21 : List (List (Nat × Nat)) := [[],[(0,1)]]
def A_21 : BT (List (Nat × Nat)) := btOfList 1 al_21
set_option maxHeartbeats 0 in
lemma A_21_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_21 = g_21) A_21 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_21_0 : Slice r_21 g_21 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) (d 0xfffcf000fffcf000) 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_1 : Slice r_21 g_21 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) (d 0xffa0f000ffa0f000) 5 := carry_of (swaps := [(1,4),(2,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_2 : Slice r_21 g_21 (subcubeFast 0 2) 5 := by
  have hc : Lower (varsOf 29) (d 0xfffaf000fffaf000) 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_3 : Slice r_21 g_21 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) (d 0xffc0f000ffc0f000) 5 := carry_of (swaps := [(0,4),(1,4),(2,4)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_4 : Slice r_21 g_21 (subcubeFast 8 0) 5 := by
  have hc : Lower (varsOf 23) (d 0xe8e80000e8e80000) 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_21_5 : Slice r_21 g_21 (subcubeFast 0 16) 5 := by
  exact slice_fast_direct_f (z := 0) (o := 16) (by decide +kernel) low_3
set_option maxHeartbeats 0 in
lemma sl_21_6 : Slice r_21 g_21 (subcubeFast 8 16) 4 := by
  exact slice_fast_direct_f (z := 8) (o := 16) (by decide +kernel) low_0
def S_21 : BT (Option (Nat × Nat)) := btOfList 3 [some (subcubeFast 0 1,5),some (subcubeFast 2 0,5),some (subcubeFast 0 2,5),some (subcubeFast 1 0,5),some (subcubeFast 8 0,5),some (subcubeFast 0 16,5),some (subcubeFast 8 16,4)]
lemma S_21_ok : btAll (fun o => ∀ p, o = some p → Slice r_21 g_21 p.1 p.2) S_21 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_21_0) (forall_cons (fun _ h => by cases h; exact sl_21_1) (forall_cons (fun _ h => by cases h; exact sl_21_2) (forall_cons (fun _ h => by cases h; exact sl_21_3) (forall_cons (fun _ h => by cases h; exact sl_21_4) (forall_cons (fun _ h => by cases h; exact sl_21_5) (forall_cons (fun _ h => by cases h; exact sl_21_6) (fun _ h => (List.not_mem_nil h).elim))))))))
def ps_21 : BT (Option PoolSpec) := btOfList 4 [q 0 [],q 5 [],q 4 [],q 3 [],q 1 [],q 2 [],q 6 [],q 3 [16391],q 0 [16391],q 1 [16384],q 2 [16384],q 1 [12290],q 2 [12290],q 3 [12293],q 0 [12293]]
def B_21_4 : BT (List (List Nat)) := BT.empty
lemma B_21_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_21 4 xs.toFinset) B_21_4 := .empty
def U_21_5 : List Nat := [0,1,2]
def P_21_5 : BT (Option BoundPool) := buildPoolsSubBT 4 W_21 r_21 S_21 ps_21 U_21_5
def N_21_5 : List NodeSpec := [([6,0,1,5,2,3],[0,1],[]),([7,0,1,2,8,4],[2],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_21_5 : checkNodesBT W_21 g_21 F_21 P_21_5 A_21 B_21_4 5 N_21_5 = true := by decide +kernel
def B_21_5 : BT (List (List Nat)) := buildBucketsBT W_21 N_21_5
set_option maxRecDepth 500000 in
lemma B_21_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_21 5 xs.toFinset) B_21_5 :=
  buildBucketsBT_sound (by decide) gp_21 W_21_ok (buildPoolsSubBT_sound S_21_ok) A_21_ok B_21_4_ok C_21_5
def U_21_6 : List Nat := (r 0 15)
def P_21_6 : BT (Option BoundPool) := buildPoolsSubBT 4 W_21 r_21 S_21 ps_21 U_21_6
def N_21_6 : List NodeSpec := [u5 [6] (r 0 7),u5 [7] ([0]++r 2 5),u5 [8] ([0]++r 2 5),([9,0,2,3,4],(r 5 4),[]),([10,1,2,3,4],[3,6,9,10],[]),u5 [5] ([0]++r 3 4),([11,1,2,3,4],[0,3,6,11,12],[]),([0,2,3,12,4],[2,5,6,13,14],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_21_6 : checkNodesBT W_21 g_21 F_21 P_21_6 A_21 B_21_5 6 N_21_6 = true := by decide +kernel
def B_21_6 : BT (List (List Nat)) := buildBucketsBT W_21 N_21_6
set_option maxRecDepth 500000 in
lemma B_21_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_21 6 xs.toFinset) B_21_6 :=
  buildBucketsBT_sound (by decide) gp_21 W_21_ok (buildPoolsSubBT_sound S_21_ok) A_21_ok B_21_5_ok C_21_6
def U_21_7 : List Nat := (r 0 7)
def P_21_7 : BT (Option BoundPool) := buildPoolsSubBT 4 W_21 r_21 S_21 ps_21 U_21_7
def N_21_7 : List NodeSpec := [a5 [] (r 0 7) [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_21_7 : checkNodesBT W_21 g_21 F_21 P_21_7 A_21 B_21_6 7 N_21_7 = true := by decide +kernel
def B_21_7 : BT (List (List Nat)) := buildBucketsBT W_21 N_21_7
set_option maxRecDepth 500000 in
lemma B_21_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_21 7 xs.toFinset) B_21_7 :=
  buildBucketsBT_sound (by decide) gp_21 W_21_ok (buildPoolsSubBT_sound S_21_ok) A_21_ok B_21_6_ok C_21_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_21_ok : forestRootCheck r_21 g_21 [(VAR 0,18,19),(VAR 1,17,19),(VAR 2,8,12),(VAR 3,4,12),(VAR 4,3,19)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_21_in : bucketContainsBT B_21_7 r_21 = true := by decide +kernel
lemma low_21 : Lower r_21 g_21 8 := lower_of_forestBT root_21_ok B_21_7_ok root_21_in
def g_22 := (d 0xfffe8000fffe8000)
def r_22 : List Nat := varsOf 31
def p_22 : List Nat := [15,15,15,15,17,17,18,18,19,20,20,21,22,23,24,24,25,26,27,28,29,30]
def q_22 : List Nat := [14,13,11,7,16,1,16,2,3,16,4,5,6,7,16,8,9,10,11,12,13,14]
def F_22 : Nat := fullMask 22
set_option maxHeartbeats 0 in
lemma gp_22 : goodPairs g_22 p_22 q_22 := goodPairs_of (by decide +kernel)
def W_22 : BT Decor := buildWiresBT 7 (mkBase p_22 q_22 r_22) [(0,3,4),(1,3,4),(3,5,6),(0,0,6),(0,2,4),(1,2,4),(3,9,10),(2,11,3),(0,7,0),(0,0,3),(0,14,4),(3,15,0),(1,3,0),(1,17,4),(3,3,18),(0,0,4),(1,0,4),(3,20,21),(1,5,2),(3,3,4),(0,1,21),(2,0,4),(1,1,4),(0,0,27),(0,2,27),(1,0,1),(0,30,4),(1,31,3),(2,3,4),(3,33,17),(0,2,3),(1,0,2),(3,35,36),(2,30,2),(1,38,3),(0,0,1),(1,40,4),(3,3,41),(3,2,21),(1,24,14),(0,35,4),(3,45,0),(3,2,4),(1,47,0),(2,48,3),(0,17,4),(0,1,2),(3,51,3),(3,52,0),(2,1,4),(3,54,3),(3,55,0),(1,51,4),(0,0,57),(1,2,3),(0,59,4),(3,60,0),(1,30,4),(3,3,62),(1,20,3),(1,20,2),(3,0,4),(2,1,5),(2,30,3),(1,24,0),(1,30,2),(2,40,4),(3,35,0),(1,1,2),(0,40,4),(0,40,2),(3,33,0),(2,30,4),(3,35,4),(3,59,4)]
lemma W_22_ok : btAll (fun x => faithful p_22 q_22 x ∧ x.1 < 2^256) W_22 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_22 : List (List (Nat × Nat)) := [[],[(2,3)],[(1,2)],[(1,3),(2,3)],[(1,2),(2,3)],[(0,1)],[(0,1),(2,3)],[(0,2),(1,2)],[(0,3),(1,3),(2,3)],[(0,2),(1,2),(2,3)],[(0,3),(1,3)],[(0,1),(1,2)],[(0,2)],[(0,3),(2,3)],[(0,2),(1,3)],[(0,3),(1,2),(2,3)],[(0,1),(1,2),(2,3)],[(0,1),(1,3)],[(0,2),(2,3)],[(0,3)],[(0,2),(1,3),(2,3)]]
def A_22 : BT (List (Nat × Nat)) := btOfList 5 al_22
set_option maxHeartbeats 0 in
lemma A_22_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_22 = g_22) A_22 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_22_0 : Slice r_22 g_22 (identDom 2 3) 6 := by
  have hc : Lower (varsOf 23) (d 0xfefe8080fefe8080) 6 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_2
  exact slice_ident (u := 2) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_1 : Slice r_22 g_22 (identDom 1 3) 6 := by
  have hc : Lower (varsOf 23) (d 0xfefe8080fefe8080) 6 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_2
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_2 : Slice r_22 g_22 (identDom 1 2) 6 := by
  have hc : Lower (varsOf 27) (d 0xffee8800ffee8800) 6 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_ident (u := 1) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_3 : Slice r_22 g_22 (identDom 0 3) 6 := by
  have hc : Lower (varsOf 23) (d 0xfefe8080fefe8080) 6 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_2
  exact slice_ident (u := 0) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_4 : Slice r_22 g_22 (identDom 0 2) 6 := by
  have hc : Lower (varsOf 27) (d 0xffee8800ffee8800) 6 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_ident (u := 0) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_5 : Slice r_22 g_22 (identDom 0 1) 6 := by
  have hc : Lower (varsOf 29) (d 0xfffaa000fffaa000) 6 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_ident (u := 0) (v := 1) (by decide +kernel) hc
def S_22 : BT (Option (Nat × Nat)) := btOfList 3 [some (identDom 2 3,6),some (identDom 1 3,6),some (identDom 1 2,6),some (identDom 0 3,6),some (identDom 0 2,6),some (identDom 0 1,6)]
lemma S_22_ok : btAll (fun o => ∀ p, o = some p → Slice r_22 g_22 p.1 p.2) S_22 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_22_0) (forall_cons (fun _ h => by cases h; exact sl_22_1) (forall_cons (fun _ h => by cases h; exact sl_22_2) (forall_cons (fun _ h => by cases h; exact sl_22_3) (forall_cons (fun _ h => by cases h; exact sl_22_4) (forall_cons (fun _ h => by cases h; exact sl_22_5) (fun _ h => (List.not_mem_nil h).elim)))))))
def ps_22 : BT (Option PoolSpec) := btOfList 6 [q 5 [16504,12413],q 3 [12296,9,147599],q 5 [8314,12441],q 2 [12495,211],q 2 [16589,233472],q 5 [],q 4 [],q 3 [],q 0 [],q 3 [16399],q 1 [16399],q 0 [16399],q 1 [],q 5 [12410],q 3 [4097,12410],q 1 [4097,12410],q 3 [16399,97],q 5 [8313],q 4 [4097],q 2 [4097],q 1 [13],q 0 [13],q 4 [4096],q 3 [4096],q 5 [16546],q 5 [16545],q 4 [12296,143],q 3 [12296,143],q 0 [143],q 2 [4],q 4 [4,8197],q 5 [8197],q 5 [16386],q 2 [],q 5 [8352],q 2 [4096],q 5 [16504],q 3 [16398,135],q 0 [16623],q 5 [16385],q 4 [16385],q 3 [16385],q 5 [16384],q 4 [16384],q 3 [16384],q 4 [16386],q 3 [16386],q 3 [4097],q 1 [4097],q 1 [4096]]
def B_22_2 : BT (List (List Nat)) := BT.empty
lemma B_22_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 2 xs.toFinset) B_22_2 := .empty
def U_22_3 : List Nat := []
def P_22_3 : BT (Option BoundPool) := buildPoolsSubBT 6 W_22 r_22 S_22 ps_22 U_22_3
def N_22_3 : List NodeSpec := [([7,8,1,2],[],[]),([12,11,0,1],[],[]),([13,7,1,2],[],[]),([16,7,1,2],[],[]),([19,22,1,2],[],[]),([7,0,1,23],[],[]),([7,0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_3 : checkNodesBT W_22 g_22 F_22 P_22_3 A_22 B_22_2 3 N_22_3 = true := by decide +kernel
def B_22_3 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_3
set_option maxRecDepth 500000 in
lemma B_22_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 3 xs.toFinset) B_22_3 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound S_22_ok) A_22_ok B_22_2_ok C_22_3
def U_22_4 : List Nat := (r 0 5)
def P_22_4 : BT (Option BoundPool) := buildPoolsSubBT 6 W_22 r_22 S_22 ps_22 U_22_4
def N_22_4 : List NodeSpec := [([24,7,0,1,2],[],[]),([19,0,25,2,4],[],[]),([26,22,1,2,3],[],[]),([28,1,29,3,4],[],[]),([24,8,1,2,4],[],[]),([7,0,1,2,4],[],[]),([0,1,2,32,4],[0],[]),([0,1,2,34,4],[],[]),([37,0,1,3,4],[1],[]),([0,1,2,39,4],[2],[]),([7,0,1,2,6],[],[0,5,11,16,17,19]),([42,0,1,2,4],[],[]),([16,1,2,5,6],[],[0]),([19,43,0,1,4],[],[]),([20,1,2,3,41],[],[]),([0,44,1,2,4],[],[]),([46,1,2,3,4],[],[]),([49,0,1,2,4],[],[]),([0,1,2,50,6],[],[]),([53,1,2,3,4],[3],[]),([19,0,1,2,4],[],[]),([56,1,2,3,4],[],[]),([58,1,2,3,4],[4],[]),([61,1,2,3,4],[],[]),([16,1,2,3,4],[],[]),([63,0,1,2,4],[],[]),([20,1,2,64,21],[],[8]),([20,1,2,3,21],[],[8]),([26,1,2,64,4],[],[]),([0,1,65,64,4],[],[]),([7,0,1,2,5],[],[0,2,5,7,11]),([26,66,1,2,3],[],[8]),([7,0,1,2],[],[0,1,3,5,8,11]),([16,67,2,3,4],[],[]),([20,25,2,3,21],[],[8]),([16,1,3,23,4],[],[]),([19,20,1,2,21],[],[0]),([7,0,1,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_4 : checkNodesBT W_22 g_22 F_22 P_22_4 A_22 B_22_3 4 N_22_4 = true := by decide +kernel
def B_22_4 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_4
set_option maxRecDepth 500000 in
lemma B_22_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 4 xs.toFinset) B_22_4 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound S_22_ok) A_22_ok B_22_3_ok C_22_4
def U_22_5 : List Nat := (r 5 40)
def P_22_5 : BT (Option BoundPool) := buildPoolsSubBT 6 W_22 r_22 S_22 ps_22 U_22_5
def N_22_5 : List NodeSpec := [([26,66,1,2,3,4],[],[8]),([26,66,0,1,2,3],[],[8]),a5 [20] [5,6,7] [0,8,13,19],([19,0,1,2,4,21],[7],[0,2]),([28,1,2,3,4,27],[],[0,1,3,5,6,8]),([24,0,1,2,4,6],(r 8 4),[16]),a5 [68] ([7,8]++r 12 4) [1],a5 [69] [5,6,16] [0,1,3],([19,0,1,2,4],[],[]),([24,14,0,1,2,4],[9],[0]),e5 [70] [17,18,19],([0,1,2,17,4,6],[7,20,21],[0]),([40,20,1,2,3,4],[5,22,23],[0]),u5 [26] [],e5 [71] [24],a5 [41] [25] [0,1,5,11,16],([20,0,1,2,3,21],[],[8]),e5 [19] [],a5 [72] [5,8,26,27,28] [8],([20,1,2,3,21],[],[0,1,2,3,4,8,13,19]),([40,0,2,73,3,4],[29,30,31],[15]),([26,1,30,2,3,4],[32],[8]),([16,1,2,5,3,4],[7],[0,2]),a5 [74] [12,33] [3,8,14,20],a5 [24] [] [16],e5 [75] [22,34,35],([26,66,1,2,3],[],[0,8]),a5 [21] [5,6,7] [0,1,3],a5 [31] [36] [0,1,3,8,14,20],a5 [76] [5,6,37] [10,15,19],e5 [77] [],([26,20,1,2,3,4],[8],[0,1,3]),([16,1,2,3,4],[],[]),e5 [78] [],e5 [79] [38],([20,0,1,2,64,4],[],[0,2,8,13,19]),([20,1,2,3,4,21],(r 39 6),[8]),a5 [62] [12,33] [0,1,3,8],e5 [16] [],([24,0,1,2,5,3],[8],[16]),([26,0,1,2,3,21],[8],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_5 : checkNodesBT W_22 g_22 F_22 P_22_5 A_22 B_22_4 5 N_22_5 = true := by decide +kernel
def B_22_5 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_5
set_option maxRecDepth 500000 in
lemma B_22_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 5 xs.toFinset) B_22_5 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound S_22_ok) A_22_ok B_22_4_ok C_22_5
def U_22_6 : List Nat := (r 5 8++[18,19,22,23,32,33,35]++r 39 11)
def P_22_6 : BT (Option BoundPool) := buildPoolsSubBT 6 W_22 r_22 S_22 ps_22 U_22_6
def N_22_6 : List NodeSpec := [a5 [24] (r 7 6) [0,2,5,7,11,16],a5 [26] [5,6,7,32,45,46] [0,2,4,8,13,19],a5 [20] [5,6,7,42,43,44] [0,1,2,3,4,8,13,19],a5 [21] [5,6,7,39,40,41] [0,1,2,3,4,5,8,11,13,16,19],a5 [30] [5,12,18,19,33,47,48] [0,1,3,5,8,11,12,14,16,18],a5 [40] [5,12,22,23,33,35,49] [0,1,3,5,6,8,14,20]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_6 : checkNodesBT W_22 g_22 F_22 P_22_6 A_22 B_22_5 6 N_22_6 = true := by decide +kernel
def B_22_6 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_6
set_option maxRecDepth 500000 in
lemma B_22_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 6 xs.toFinset) B_22_6 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound S_22_ok) A_22_ok B_22_5_ok C_22_6
def U_22_7 : List Nat := (r 5 4++[12,33])
def P_22_7 : BT (Option BoundPool) := buildPoolsSubBT 6 W_22 r_22 S_22 ps_22 U_22_7
def N_22_7 : List NodeSpec := [a5 [] (r 5 4++[12,33]) [0,1,2,3,4,5,7,8,9,11,14,16]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_7 : checkNodesBT W_22 g_22 F_22 P_22_7 A_22 B_22_6 7 N_22_7 = true := by decide +kernel
def B_22_7 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_7
set_option maxRecDepth 500000 in
lemma B_22_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 7 xs.toFinset) B_22_7 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound S_22_ok) A_22_ok B_22_6_ok C_22_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_22_ok : forestRootCheck r_22 g_22 [(VAR 0,14,15),(VAR 1,13,15),(VAR 2,11,15),(VAR 3,7,15),(VAR 4,1,17)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_22_in : bucketContainsBT B_22_7 r_22 = true := by decide +kernel
lemma low_22 : Lower r_22 g_22 8 := lower_of_forestBT root_22_ok B_22_7_ok root_22_in
def g_23 := (d 0xfffeffa8fcc08000)
def r_23 : List Nat := varsOf 63
def p_23 : List Nat := [15,15,15,15,22,22,22,23,23,23,26,26,26,27,27,27,28,28,28,29,29,29,30,35,35,35,37,37,37,39,39,40,40,41,41,42,42,43,44,44,45,46,46,49,49,49,50,50,50,51,52,52,52,53,54,56,56,57]
def q_23 : List Nat := [14,13,11,7,20,18,6,21,19,7,24,18,10,25,19,11,24,20,12,25,21,13,14,34,33,3,36,33,5,38,7,32,8,33,9,34,10,11,36,12,13,38,14,48,33,17,48,34,18,19,48,36,20,21,38,48,24,25]
def F_23 : Nat := fullMask 58
set_option maxHeartbeats 0 in
lemma gp_23 : goodPairs g_23 p_23 q_23 := goodPairs_of (by decide +kernel)
def W_23 : BT Decor := buildWiresBT 9 (mkBase p_23 q_23 r_23) [(1,1,4),(1,3,5),(0,6,7),(0,2,8),(1,2,8),(3,9,10),(0,1,4),(0,2,4),(1,2,4),(3,13,14),(3,15,1),(2,15,1),(3,17,7),(1,1,2),(0,19,7),(0,20,4),(1,20,4),(3,21,22),(0,1,2),(0,2,5),(1,2,5),(3,25,26),(3,1,4),(1,27,3),(3,28,29),(0,29,6),(0,14,7),(1,1,32),(3,13,33),(0,15,1),(1,15,1),(2,1,3),(0,15,5),(1,37,38),(0,15,7),(0,1,5),(2,15,41),(1,42,3),(1,3,4),(0,19,44),(0,45,5),(1,45,5),(3,46,47),(2,20,4),(3,20,4),(2,1,32),(3,1,32),(3,24,22),(3,12,6),(2,54,2),(3,54,2),(0,0,22),(2,0,21),(3,3,5),(0,0,4),(1,60,3),(2,15,3),(0,62,5),(1,63,3),(0,36,7),(3,16,7),(1,17,3),(1,16,3),(2,27,4),(1,69,37),(1,62,41),(3,37,15),(0,62,1),(2,54,3),(2,74,25),(1,41,3),(0,15,76),(3,3,4),(3,78,27),(0,27,44),(3,27,4),(2,0,81),(1,1,5),(3,41,83),(2,84,2),(3,84,2),(2,27,3),(1,27,4),(0,1,88),(3,2,4),(1,84,3),(0,27,1),(2,1,4),(0,27,6),(2,27,12),(3,2,8),(3,37,27),(3,28,27),(0,1,29),(2,2,3),(1,100,12),(0,101,5),(1,102,3),(1,15,5),(2,1,5),(3,105,15),(2,45,5),(3,45,5),(0,1,32),(1,27,1),(3,3,47),(3,60,7),(3,112,19),(2,0,4),(1,114,3),(1,24,5),(3,0,7),(3,4,7),(3,118,19),(3,1,5),(1,4,5),(0,19,121),(0,27,4),(0,4,7),(2,19,124),(0,0,7),(2,15,5),(3,15,5),(2,0,20),(2,0,13),(2,36,3),(1,120,3),(0,44,116),(0,0,20),(3,62,1),(3,2,91),(2,54,25),(3,62,5),(1,128,3),(1,84,4),(3,2,140),(0,4,5),(1,3,142),(0,1,143),(0,2,143),(1,4,7),(0,1,146),(0,1,7),(1,1,7),(0,4,149),(3,2,149),(1,2,7),(0,1,152),(3,4,149),(3,27,1),(0,2,7),(1,90,148),(3,1,7),(3,2,7),(3,28,7),(3,2,146),(0,2,132),(1,90,3),(0,163,83),(3,2,5),(1,165,3),(0,166,6),(0,2,149),(1,25,3),(1,122,3),(3,156,6),(0,14,83),(2,19,3),(1,173,5),(3,114,7),(3,156,152),(1,59,24),(1,24,142),(0,0,116),(3,24,44),(2,2,4),(3,4,5),(3,124,146),(2,4,5),(3,184,0),(3,28,166),(1,182,24),(2,19,5),(0,0,5),(1,189,24),(2,122,3),(3,173,121),(2,1,2),(2,0,3),(1,1,3),(3,0,116),(1,189,3),(0,19,143),(3,13,132),(0,44,83),(2,2,1),(3,201,143),(1,13,41),(1,203,3),(1,37,13),(3,205,5),(1,15,3),(1,182,3),(3,118,149),(0,6,26),(1,12,25),(2,203,3),(3,90,7),(3,3,6),(1,214,5),(1,78,5),(2,4,7),(2,44,5),(0,0,146),(1,184,3),(2,2,7),(3,221,0),(2,195,5),(3,2,143),(3,3,121),(2,0,7),(2,1,7),(3,120,44),(2,166,4),(0,166,4),(3,2,132),(0,1,166),(1,105,78),(2,2,5),(3,234,44),(3,3,83),(3,25,1),(1,41,2),(1,59,90),(1,105,3),(1,105,90),(1,90,41),(2,163,5),(1,163,5),(1,28,3),(3,2,245),(0,1,163),(3,181,7),(1,181,41),(1,93,165),(1,93,5),(3,0,251),(1,93,3),(2,253,5),(1,253,5),(3,181,83),(2,214,5),(3,120,14),(3,234,6),(1,24,3),(3,24,121),(3,59,6),(1,114,5),(3,3,263),(1,93,59),(1,188,3),(3,189,195),(2,0,5),(3,13,83),(3,3,251),(0,0,1),(1,271,3),(2,272,5),(3,24,7),(1,37,142),(2,260,5),(1,184,24),(1,193,5),(1,61,5),(3,3,116),(3,182,195),(0,195,121),(1,60,5),(1,184,193),(1,272,5),(1,37,5),(1,260,5),(3,60,19),(2,173,5),(3,217,0),(1,234,12),(1,173,4),(0,0,2),(3,293,83),(1,12,5),(1,90,5),(3,3,296),(1,100,271),(3,3,14),(1,37,60),(3,189,19),(3,293,7),(1,271,5),(3,3,303),(3,201,44),(3,293,195),(1,100,41),(1,37,189),(1,193,60),(1,193,3),(2,310,5),(3,60,195),(0,195,14),(1,181,37),(3,60,83),(1,194,5),(1,105,60),(1,184,37),(2,61,5),(2,6,5),(1,320,3),(2,19,142),(2,115,5),(3,201,7),(1,12,3),(2,325,5),(3,3,278),(1,193,142),(1,78,193),(3,3,26),(1,165,12),(1,234,271),(1,60,24),(3,59,19),(3,181,195),(1,37,165),(3,184,19),(3,182,19),(1,78,41),(1,2,3),(3,28,340),(3,28,26),(1,201,3),(3,120,340),(1,310,5),(1,59,193),(3,173,4),(3,3,283),(3,201,121),(1,234,93),(2,195,142),(1,182,193),(1,325,5),(3,13,195),(1,193,189),(3,25,195),(0,195,26),(3,234,195),(3,184,195),(1,100,5),(3,78,19),(3,100,6),(1,78,165),(1,37,90),(3,78,83),(3,100,83),(1,234,37),(3,100,121),(1,182,37),(3,3,295),(3,25,44),(1,28,165),(3,13,7),(1,78,24),(1,59,12),(3,25,6)]
lemma W_23_ok : btAll (fun x => faithful p_23 q_23 x ∧ x.1 < 2^256) W_23 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_23 : List (List (Nat × Nat)) := [[],[(1,2)]]
def A_23 : BT (List (Nat × Nat)) := btOfList 1 al_23
set_option maxHeartbeats 0 in
lemma A_23_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_23 = g_23) A_23 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_23_0 : Slice r_23 g_23 (subcubeFast 0 1) 9 := by
  have hc : Lower (varsOf 62) (d 0xfffffffcfcc0c000) 9 := carry_of (swaps := [(0,5),(1,5),(2,5),(3,5),(4,5)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_1 : Slice r_23 g_23 (subcubeFast 8 0) 9 := by
  have hc : Lower (varsOf 55) (d 0xfefea8a8c0c00000) 9 := carry_of (swaps := [(3,5),(4,5)]) (by decide +kernel) low_11
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_2 : Slice r_23 g_23 (identDom 0 2) 10 := by
  have hc : Lower (varsOf 59) (d 0xffeeffaaee888800) 10 := carry_of (swaps := [(0,2),(1,2),(2,5),(4,5)]) (by decide +kernel) low_13
  exact slice_ident (u := 0) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_3 : Slice r_23 g_23 (identDom 0 1) 10 := by
  have hc : Lower (varsOf 61) (d 0xfffaffaafaa0a000) 10 := carry_of (swaps := [(0,2),(1,5),(4,5)]) (by decide +kernel) low_13
  exact slice_ident (u := 0) (v := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_4 : Slice r_23 g_23 (subcubeFast 1 0) 8 := by
  have hc : Lower (varsOf 62) (d 0xfffcff00fcc00000) 8 := carry_of (swaps := [(0,5),(1,5),(2,5),(3,5)]) (by decide +kernel) low_14
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_5 : Slice r_23 g_23 (subcubeFast 32 0) 8 := by
  exact slice_fast_direct_f (z := 32) (o := 0) (by decide +kernel) low_15
set_option maxHeartbeats 0 in
lemma sl_23_6 : Slice r_23 g_23 (subcubeFast 0 16) 8 := by
  have hc : Lower (varsOf 47) (d 0xfffefffefcc0fcc0) 8 := carry_of (swaps := [(4,5)]) (by decide +kernel) low_16
  exact slice_fast_direct_f (z := 0) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_7 : Slice r_23 g_23 (subcubeFast 32 1) 7 := by
  have hc : Lower (varsOf 30) (d 0xfcc0c000fcc0c000) 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 32) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_8 : Slice r_23 g_23 (subcubeFast 1 16) 7 := by
  have hc : Lower (varsOf 46) (d 0xfffcfffcfcc0fcc0) 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4),(4,5)]) (by decide +kernel) low_12
  exact slice_fast_direct_f (z := 1) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_9 : Slice r_23 g_23 (subcubeFast 4 0) 8 := by
  have hc : Lower (varsOf 59) (d 0xffeeff88cc000000) 8 := carry_of (swaps := [(2,5),(4,5)]) (by decide +kernel) low_17
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_10 : Slice r_23 g_23 (subcubeFast 2 0) 8 := by
  have hc : Lower (varsOf 61) (d 0xfffaffa0f0000000) 8 := carry_of (swaps := [(1,5),(2,5),(4,5)]) (by decide +kernel) low_17
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_11 : Slice r_23 g_23 (subcubeFast 0 4) 8 := by
  have hc : Lower (varsOf 59) (d 0xffffffaaffcc8800) 8 := carry_of (swaps := [(2,5),(3,5),(4,5)]) (by decide +kernel) low_18
  exact slice_fast_direct_f (z := 0) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_12 : Slice r_23 g_23 (subcubeFast 0 2) 8 := by
  have hc : Lower (varsOf 61) (d 0xffffffaafff0a000) 8 := carry_of (swaps := [(1,5),(2,5),(3,5),(4,5)]) (by decide +kernel) low_18
  exact slice_fast_direct_f (z := 0) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_13 : Slice r_23 g_23 (subcubeFast 16 0) 8 := by
  have hc : Lower (varsOf 47) (d 0xffa8ffa880008000) 8 := carry_of (swaps := [(0,2),(1,2),(4,5)]) (by decide +kernel) low_19
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_14 : Slice r_23 g_23 (identDom 1 2) 8 := by
  have hc : Lower (varsOf 59) (d 0xffeeff88cccc8800) 8 := carry_of (swaps := [(1,3),(2,5),(4,5)]) (by decide +kernel) low_20
  exact slice_ident (u := 1) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_15 : Slice r_23 g_23 (identDom 0 4) 8 := by
  have hc : Lower (varsOf 47) (d 0xffaaffaaa880a880) 8 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4),(4,5)]) (by decide +kernel) low_21
  exact slice_ident (u := 0) (v := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_16 : Slice r_23 g_23 (subcubeFast 2 1) 6 := by
  have hc : Lower (varsOf 60) (d 0xfffffff0f0000000) 6 := carry_of (swaps := [(0,4),(1,5),(2,4),(3,5)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 2) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_17 : Slice r_23 g_23 (subcubeFast 8 1) 6 := by
  have hc : Lower (varsOf 54) (d 0xfffffcfcc0c00000) 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,5)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 8) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_18 : Slice r_23 g_23 (subcubeFast 4 1) 6 := by
  have hc : Lower (varsOf 58) (d 0xffffffcccc000000) 6 := carry_of (swaps := [(0,4),(1,4),(2,5),(3,4),(4,5)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 4) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_19 : Slice r_23 g_23 (subcubeFast 16 1) 6 := by
  have hc : Lower (varsOf 46) (d 0xfffcfffcc000c000) 6 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4),(4,5)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 16) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_20 : Slice r_23 g_23 (identDom 4 5) 8 := by
  exact slice_ident (u := 4) (v := 5) (by decide +kernel) low_22
set_option maxHeartbeats 0 in
lemma sl_23_21 : Slice r_23 g_23 (subcubeFast 12 32) 4 := by
  have hc : Lower (varsOf 19) (d 0xeeee8888eeee8888) 4 := carry_of (swaps := [(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 12) (o := 32) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_22 : Slice r_23 g_23 (subcubeFast 10 32) 4 := by
  have hc : Lower (varsOf 21) (d 0xfafaa0a0fafaa0a0) 4 := carry_of (swaps := [(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 10) (o := 32) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_23 : Slice r_23 g_23 (subcubeFast 16 6) 4 := by
  have hc : Lower (varsOf 41) (d 0xffaaffaaaa00aa00) 4 := carry_of (swaps := [(1,3),(2,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 16) (o := 6) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_24 : Slice r_23 g_23 (subcubeFast 32 17) 4 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 32) (o := 17) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_25 : Slice r_23 g_23 (subcubeFast 33 16) 4 := by
  have hc : Lower (varsOf 14) (d 0xfcc0fcc0fcc0fcc0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 33) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_26 : Slice r_23 g_23 (subcubeFast 32 9) 4 := by
  have hc : Lower (varsOf 22) (d 0xfcfcc0c0fcfcc0c0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 32) (o := 9) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_27 : Slice r_23 g_23 (subcubeFast 9 16) 4 := by
  have hc : Lower (varsOf 38) (d 0xfcfcfcfcc0c0c0c0) 4 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 9) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_28 : Slice r_23 g_23 (subcubeFast 32 5) 4 := by
  have hc : Lower (varsOf 26) (d 0xffcccc00ffcccc00) 4 := carry_of (swaps := [(0,3),(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 32) (o := 5) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_29 : Slice r_23 g_23 (subcubeFast 5 16) 4 := by
  have hc : Lower (varsOf 42) (d 0xffccffcccc00cc00) 4 := carry_of (swaps := [(0,3),(1,3),(2,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 5) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_30 : Slice r_23 g_23 (subcubeFast 32 3) 4 := by
  have hc : Lower (varsOf 28) (d 0xfff0f000fff0f000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 32) (o := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_31 : Slice r_23 g_23 (subcubeFast 3 16) 4 := by
  have hc : Lower (varsOf 44) (d 0xfff0fff0f000f000) 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 3) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_32 : Slice r_23 g_23 (subcubeFast 3 4) 4 := by
  have hc : Lower (varsOf 56) (d 0xffffff00ff000000) 4 := carry_of (swaps := [(0,3),(1,4),(2,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 3) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_33 : Slice r_23 g_23 (subcubeFast 5 2) 4 := by
  have hc : Lower (varsOf 56) (d 0xffffff00ff000000) 4 := carry_of (swaps := [(0,3),(1,4),(2,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 5) (o := 2) (by decide +kernel) hc
def S_23 : BT (Option (Nat × Nat)) := btOfList 6 [some (subcubeFast 0 1,9),some (subcubeFast 8 0,9),some (identDom 0 2,10),some (identDom 0 1,10),some (subcubeFast 1 0,8),some (subcubeFast 32 0,8),some (subcubeFast 0 16,8),some (subcubeFast 32 1,7),some (subcubeFast 1 16,7),some (subcubeFast 4 0,8),some (subcubeFast 2 0,8),some (subcubeFast 0 4,8),some (subcubeFast 0 2,8),some (subcubeFast 16 0,8),some (identDom 1 2,8),some (identDom 0 4,8),some (subcubeFast 2 1,6),some (subcubeFast 8 1,6),some (subcubeFast 4 1,6),some (subcubeFast 16 1,6),some (identDom 4 5,8),some (subcubeFast 12 32,4),some (subcubeFast 10 32,4),some (subcubeFast 16 6,4),some (subcubeFast 32 17,4),some (subcubeFast 33 16,4),some (subcubeFast 32 9,4),some (subcubeFast 9 16,4),some (subcubeFast 32 5,4),some (subcubeFast 5 16,4),some (subcubeFast 32 3,4),some (subcubeFast 3 16,4),some (subcubeFast 3 4,4),some (subcubeFast 5 2,4)]
lemma S_23_ok : btAll (fun o => ∀ p, o = some p → Slice r_23 g_23 p.1 p.2) S_23 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_23_0) (forall_cons (fun _ h => by cases h; exact sl_23_1) (forall_cons (fun _ h => by cases h; exact sl_23_2) (forall_cons (fun _ h => by cases h; exact sl_23_3) (forall_cons (fun _ h => by cases h; exact sl_23_4) (forall_cons (fun _ h => by cases h; exact sl_23_5) (forall_cons (fun _ h => by cases h; exact sl_23_6) (forall_cons (fun _ h => by cases h; exact sl_23_7) (forall_cons (fun _ h => by cases h; exact sl_23_8) (forall_cons (fun _ h => by cases h; exact sl_23_9) (forall_cons (fun _ h => by cases h; exact sl_23_10) (forall_cons (fun _ h => by cases h; exact sl_23_11) (forall_cons (fun _ h => by cases h; exact sl_23_12) (forall_cons (fun _ h => by cases h; exact sl_23_13) (forall_cons (fun _ h => by cases h; exact sl_23_14) (forall_cons (fun _ h => by cases h; exact sl_23_15) (forall_cons (fun _ h => by cases h; exact sl_23_16) (forall_cons (fun _ h => by cases h; exact sl_23_17) (forall_cons (fun _ h => by cases h; exact sl_23_18) (forall_cons (fun _ h => by cases h; exact sl_23_19) (forall_cons (fun _ h => by cases h; exact sl_23_20) (forall_cons (fun _ h => by cases h; exact sl_23_21) (forall_cons (fun _ h => by cases h; exact sl_23_22) (forall_cons (fun _ h => by cases h; exact sl_23_23) (forall_cons (fun _ h => by cases h; exact sl_23_24) (forall_cons (fun _ h => by cases h; exact sl_23_25) (forall_cons (fun _ h => by cases h; exact sl_23_26) (forall_cons (fun _ h => by cases h; exact sl_23_27) (forall_cons (fun _ h => by cases h; exact sl_23_28) (forall_cons (fun _ h => by cases h; exact sl_23_29) (forall_cons (fun _ h => by cases h; exact sl_23_30) (forall_cons (fun _ h => by cases h; exact sl_23_31) (forall_cons (fun _ h => by cases h; exact sl_23_32) (forall_cons (fun _ h => by cases h; exact sl_23_33) (fun _ h => (List.not_mem_nil h).elim)))))))))))))))))))))))))))))))))))
set_option maxRecDepth 500000 in
def ps_23 : BT (Option PoolSpec) := btOfList 11 [q 10 [20488,20489,106599],q 14 [20493],q 8 [4156,4157],q 0 [16392,16393,57399,4156,4157],q 1 [16392,16393,57399,4156,4157],q 21 [],q 12 [16392,16393,57399],q 11 [16388,16389,24627],q 8 [8410,8411],q 0 [16388,16389,24627,8410,8411],q 1 [16388,16389,24627,8410,8411],q 14 [20495],q 5 [8196,8197,28748],q 23 [],q 7 [16388,16389,24627],q 1 [16388,16389,24627,20488,20489,106599],q 22 [],q 0 [16392,16393,57399],q 5 [16392,16393,57399],q 1 [16392,16393,57399],q 4 [16392,16393,57399],q 1 [16392,16393,57399,20484,167998],q 10 [16392,16393,57399],q 1 [16392,16393,57399,4344,61735],q 9 [16388,16389,24627],q 13 [20488,20489,106599],q 4 [20488,20489,106599],q 0 [20488,20489,106599],q 12 [20488,20489,106599],q 1 [20488,20489,106599],q 1 [20488,20489,106599,110907],q 6 [20488,20489,106599],q 1 [20488,20489,106599,180332],q 7 [16397,180332],q 8 [20488,20489,106599],q 20 [],q 7 [16494,16495],q 1 [20488,20489,106599,16494,16495],q 2 [20484,20485,340135,8530,8531],q 0 [20484,20485,340135,8530,8531],q 7 [8530,8531],q 14 [],q 11 [20484,20485,340135],q 9 [20484,20485,340135],q 1 [20484,20485,340135,8530,8531],q 26 [],q 1 [16391,20488,20489,106599],q 7 [16493,360452],q 1 [20488,20489,106599,16493,360452],q 1 [16395,20484,20485,340135],q 4 [16391,20488,20489,106599],q 7 [16390,16391],q 1 [16390,16391,20488,20489,106599],q 1 [16389,20488,20489,106599],q 2 [16388,16389,20493,28696],q 0 [16388,16389,20493,28696],q 10 [20493,28696],q 1 [20488,20489,106599,110743],q 1 [16392,16393,57399,61591],q 7 [12397,118788],q 1 [20488,20489,106599,118788],q 5 [],q 7 [16392,16393,57399],q 5 [16388,16389,24627],q 1 [16388,16389,24627,8410],q 7 [4204,4205],q 1 [20488,20489,106599,4204,4205],q 2 [16388,16389,24627,8410,8411],q 0 [8196,8197,20493,28748],q 14 [20493,28748],q 9 [20493,28748],q 1 [8196,8197,28748],q 3 [16392,16393,57399,20493],q 0 [16392,16393,57399,20493],q 8 [4157],q 0 [16392,16393,57399,4157],q 1 [16392,16393,57399,4157],q 0 [8196,8197],q 14 [16384,20493,28915],q 0 [],q 4 [],q 5 [8196,8197],q 4 [8196,8197],q 14 [16384,12529,20493],q 32 [],q 1 [16392,16393,57399,20486,20487],q 8 [8196,20577,8197],q 8 [4156],q 0 [16392,16393,57399,4156],q 1 [16392,16393,57399,4156],q 7 [16492,16493],q 1 [20488,20489,106599,16492,16493],q 1 [16392,16393,57399,20540],q 0 [16392,16393,57399,20540,12441],q 1 [8197,28672,28688,507982],q 5 [8197,28748],q 8 [4159],q 0 [16392,16393,57399,4159],q 1 [16392,16393,57399,4159],q 4 [20484,20485,340135],q 1 [16392,53250,20484,20485,340135],q 8 [20484,20485,340135],q 11 [20577,16397,475312],q 1 [8196,20577,8197,475312],q 6 [8196,20577,8197],q 3 [16392,16393,57399,20495],q 0 [16392,16393,57399,20495],q 1 [16392,16393,57399,4158],q 0 [16392,16393,57399,4158,12357],q 7 [16388,16389],q 1 [16388,16389,20488,20489,106599],q 8 [8410],q 0 [16388,16389,24627,8410],q 1 [20484,20485,340135,372747],q 7 [12625,372747],q 4 [16388,16389,24627],q 0 [16388,16389,24627],q 1 [16388,16389,24627],q 0 [16388,16389,24627,20488,102618],q 0 [16392,16393,57399,4159,12353],q 0 [16392,16393,57399,20484,12453],q 1 [16392,16393,57399,20484],q 7 [16721,573451],q 1 [20484,20485,340135,16721,573451],q 1 [16392,16393,57399,20484,20485],q 9 [],q 10 [],q 8 [20493],q 10 [20493,28688],q 1 [28688,28689,598020],q 13 [20493,598020],q 5 [28688,28689,598020],q 6 [20493,28676],q 11 [],q 1 [28676,28688,508497],q 5 [28676,28688,508497],q 4 [20493,28677,610320],q 12 [20493,28672],q 13 [20493,28672],q 2 [20493,28672,28677,610315],q 11 [20493,28672],q 4 [20493,28677,610315],q 1 [28672,28677,610315],q 8 [20493,28677,610315],q 0 [20493,28677,610315],q 5 [28672,28677,610315],q 4 [20493,28681,622596],q 10 [20493,28672],q 1 [28672,28681,622596],q 8 [20493,28681,622596],q 0 [20493,28681,622596],q 5 [28672,28681,622596],q 7 [16399],q 7 [16397],q 7 [16495],q 7 [16494],q 0 [20493,28677,610323],q 6 [20493,28675],q 10 [20493,28675,610323],q 12 [20493,28675],q 1 [28675,28677,610323],q 5 [28675,28677,610323],q 7 [28677,610323],q 7 [16493],q 7 [16492],q 1 [20488,20489,106599,16492],q 7 [4207],q 2 [20484,20485,340135],q 2 [20484,20485,340135,8530],q 0 [20484,20485,340135],q 0 [20484,20485,340135,8530],q 7 [8530],q 1 [20484,20485,340135],q 6 [20484,20485,340135],q 13 [20484,20485,340135],q 6 [20493,28677,610315],q 11 [20493,28691],q 12 [],q 10 [20493,610315],q 1 [28677,610315,28691],q 5 [28677,610315],q 10 [20493,610315,28691],q 7 [4205],q 29 [],q 11 [20493],q 10 [20493,28680],q 16 [16395],q 11 [20493,28676],q 1 [16395,28676,606569],q 11 [20493,28675],q 12 [20493,28683],q 9 [20493],q 0 [16391,20493,28787],q 10 [20493,28675],q 10 [20493,28787,28675],q 9 [20493,28675],q 1 [28675],q 1 [16391,28787,28675],q 5 [28675],q 0 [20493,28689,598027],q 1 [28675,28689,598027],q 5 [28675,28689,598027],q 7 [28689,598027],q 1 [16395,20485,340620],q 13 [20485,340620],q 0 [8197,20493,28748],q 2 [],q 2 [20493,28672],q 1 [8197,28672,28748],q 6 [20491,12949],q 1 [],q 1 [16389,20491,25240],q 5 [16389,25240],q 10 [20493,610312],q 9 [20493,28676],q 1 [28676,28677,610312],q 6 [20488,12389],q 12 [20488,12389],q 0 [16390,16391,20488,12389],q 4 [16390,16391],q 1 [16390,16391,20488],q 9 [16390,16391],q 5 [16390,16391],q 0 [20493],q 10 [20493,28672,28748],q 6 [20493,28672],q 11 [20497],q 13 [20493,28675],q 6 [],q 6 [20493,28680],q 8 [20493,28680],q 18 [16389],q 1 [16389,28680,25203],q 8 [8197],q 0 [8197,16397,180300],q 12 [16397],q 11 [16397],q 9 [16397,180300],q 10 [16397,180300],q 13 [8197,180300],q 1 [8197,180300],q 10 [20493,28675,28748],q 11 [20485],q 10 [16393,340024],q 1 [20485,16393,340024],q 5 [16393,340024],q 6 [12294,20485],q 13 [],q 5 [8197,12366],q 7 [8197,12366],q 10 [12366,21173,20495],q 12 [21173,20495],q 8 [8196,8197],q 9 [20497,495692],q 0 [8196,8197,20496,581645],q 14 [20496,581645],q 9 [20496,581645],q 11 [20496,581645],q 1 [8196,8197,20496],q 13 [8196,8197],q 8 [12350],q 1 [8196,8197],q 0 [8196,8197,20493],q 14 [16384,20493],q 11 [16384],q 1 [16384,8196,8197],q 0 [20493,29131],q 4 [20493],q 0 [20493,28676],q 4 [20493,28676],q 12 [20493],q 7 [8196,8197,28748],q 1 [28680,28681,623219],q 10 [16397,475312],q 9 [16397,475312],q 1 [8196,20577,475312],q 6 [8196,20577],q 7 [8196,8197],q 11 [20495,98541],q 1 [8196,8197,20496,581729],q 11 [20496,581729],q 6 [8196,8197,581729],q 0 [8197],q 24 [],q 2 [16384,20493,28915],q 13 [20493],q 4 [8196,20577,8197],q 11 [20577,475136],q 0 [8196,20577,8197],q 11 [16397,180323],q 1 [8196,8197,180323],q 4 [8196],q 5 [8196],q 6 [20486,20487],q 10 [16394,16395],q 5 [16394,16395],q 11 [20486,20487],q 1 [16394,16395,20486,20487],q 0 [16394,16395,20486,20487],q 7 [16394,16395],q 2 [8196,20577,8197],q 11 [16386,20577],q 1 [8196,20577,8197],q 10 [20493,28748],q 1 [8197,28748],q 8 [20491,12949],q 10 [20491,12949],q 11 [16388,16389],q 7 [12398],q 11 [20577,20499],q 1 [8196,20577,8197,20499],q 0 [8196,20577,8197,20499],q 8 [12294],q 1 [28688,28689,598515],q 10 [20493,610320],q 13 [20493,28676],q 4 [8197,12366],q 1 [20498,739],q 1 [8197,20498,739],q 9 [20498,739],q 10 [20498,739],q 11 [20498,739],q 8 [8197,12366],q 5 [739],q 12 [20498,739],q 1 [8197,28672,28688],q 14 [20498,739],q 1 [8196,8197,20498,739],q 19 [],q 14 [20496,20497],q 1 [8196,8197,20496,20497],q 9 [20496,20497],q 11 [20496,20497],q 6 [8196,8197],q 20 [8196,8197],q 11 [20499,99033],q 1 [8196,8197,20499,99033],q 27 [],q 0 [8196,99061,8197],q 11 [20480,99061],q 1 [20480,8196,99061,8197],q 1 [8197,28691,78299],q 7 [12294],q 12 [20497,496311],q 6 [8197,12366],q 4 [8198],q 5 [8198],q 0 [8196],q 8 [20485],q 1 [16392,16393,57399,20485],q 2 [16384,12529,20493],q 0 [12529,20493],q 4 [8197],q 6 [12529,20493],q 5 [8197],q 1 [16384],q 4 [20493,28683],q 0 [20493,28683],q 0 [12745],q 1 [16386],q 2 [16386,20493,29131],q 0 [12745,8196,8197],q 14 [16386,12745],q 9 [16386,12745],q 11 [16386,12745],q 1 [16386,8196,8197],q 19 [8196,8197],q 11 [16399,20497],q 13 [8197,495692],q 1 [8197,20497,495692],q 5 [8197,495692],q 11 [12290,20577],q 8 [12293],q 11 [20577,475139],q 12 [20493,28680],q 1 [28676,28680,639569],q 5 [28676,28680,639569],q 0 [13045,8196,8197],q 14 [20480,13045],q 9 [20480,13045],q 11 [20480,13045],q 11 [20577,16397],q 11 [20577,20497],q 7 [16390],q 1 [16390,20488,20489,106599],q 10 [16392,16393],q 5 [16392,16393],q 7 [16392,16393],q 8 [20486,20487],q 1 [16392,16393,20486,20487],q 9 [20486,20487],q 0 [16389,20493,28696],q 11 [20493,28688],q 19 [8197],q 1 [8197,28688,507982],q 0 [12529,8196,8197],q 14 [16384,12529],q 9 [16384,12529],q 9 [20493,28728],q 1 [16393,28676,28728],q 14 [20493,28672],q 1 [8196,8197,28672],q 5 [8196,8197,28672],q 12 [20496,581645],q 1 [8197,20496,585804],q 5 [8197,585804],q 1 [20496],q 9 [20487,12769],q 1 [16392,20487,540727],q 12 [16392,540727],q 5 [16392,540727],q 6 [20493,28683],q 10 [16397,340144],q 11 [20485,16397,340144],q 1 [8198,20485,340144],q 5 [16397,340144],q 6 [8198,20485],q 10 [20493,28675,610315],q 1 [28675,28677,610315],q 5 [28675,28677,610315],q 7 [28677,610315],q 1 [16388,16389,28696],q 5 [16388,16389,28696],q 8 [20488,12389],q 10 [20488,12389],q 1 [16388,16389,20488],q 9 [16388,16389],q 10 [16392],q 12 [16392,167989],q 5 [16392,13101],q 7 [12293],q 12 [16392,53397],q 1 [16392,53397],q 4 [20486,20487],q 10 [16392,53250],q 5 [16392,53250],q 1 [16392,53250,20486,20487],q 6 [53250,20486,20487],q 4 [20487,12769],q 12 [16392,53250],q 8 [20487,12769],q 8 [12349],q 14 [16386,20493],q 11 [16386],q 14 [20499,13017],q 9 [20499,13017],q 11 [20499,13017],q 4 [20484,20485],q 1 [16392,53250,20484,20485],q 9 [20484,20485],q 6 [53250,20484,20485],q 8 [20484,20485],q 8 [20541],q 6 [20493],q 1 [8197,28748,28688],q 33 [],q 0 [8198],q 12 [20491,12949],q 0 [16390,16391],q 11 [16390,16391],q 8 [20542],q 9 [16388],q 10 [12298],q 6 [20493,28677],q 10 [20493,28691,610779],q 8 [20486],q 4 [20484,12453],q 1 [16392,53250,20484],q 9 [20484,12453],q 6 [53250,20484,12453],q 8 [20484,12453],q 8 [20489],q 10 [20489,106520],q 1 [16388,16389,20489,106520],q 7 [4204],q 7 [16388],q 11 [16388,102449],q 6 [20488,102449,20489],q 1 [16388,20488,102449,20489],q 10 [20488,20489],q 12 [20488,102449,20489],q 7 [16395],q 2 [16388,16389,24627],q 2 [16388,16389,24627,8410],q 5 [16392],q 9 [20484],q 5 [16392,13102],q 8 [20488,20489],q 1 [16388,20488,20489,106599],q 7 [16389],q 1 [20487],q 7 [12397],q 1 [16388,16389,24627,20491],q 0 [16388,16389,24627,20491],q 5 [16389,24591],q 7 [16389,24591],q 6 [21337,20495],q 2 [16389,20493,28696],q 13 [20493,28696],q 6 [20488,20489],q 12 [20488,20489],q 1 [16390,16391,20488,20489],q 0 [16390,16391,20488,20489],q 8 [20493,21349],q 0 [20493,28690,21349],q 2 [20493,28689,598027],q 1 [28689,598027],q 16 [],q 10 [20493],q 1 [28689,598020],q 1 [28689,598016],q 1 [28688,28689],q 7 [13025],q 17 [],q 10 [20493,28683],q 2 [20493,28691],q 0 [20493,28691],q 10 [20493,28691],q 1 [28682,887],q 5 [28682,887],q 10 [20493,610327],q 0 [20493,28677,610327],q 3 [20493,28677,610327],q 2 [20496,581645],q 0 [20496,581645],q 10 [20496,581645],q 1 [20496,585739],q 0 [20496,581645,585739],q 7 [585739],q 4 [20493,28677],q 0 [20493,28677],q 11 [20493,28677],q 9 [20493,28677],q 1 [28677,28691],q 5 [28677],q 12 [20493,28691],q 3 [20493,28691],q 2 [20493,28677,610315],q 3 [20493,28677,610315],q 1 [28677,610315],q 7 [495631],q 8 [],q 10 [20497,495631],q 4 [20493,28688],q 0 [20493,28688],q 9 [20493,28688],q 1 [28676,28688],q 12 [20493,28688],q 5 [28676,28688],q 4 [20493,28680],q 0 [20493,28680],q 1 [28676,28680],q 13 [20493,28680],q 5 [28680],q 1 [28675,28691],q 1 [28675,28688],q 3 [],q 3 [20493,28677],q 1 [28675,28677],q 18 [],q 1 [28674,907],q 1 [28672,28688],q 5 [28672,28688],q 10 [20493,610323],q 1 [28677,610323],q 2 [20493,28672,28683],q 1 [28672,28683],q 5 [28672],q 8 [20493,28683],q 3 [20493,28678],q 3 [20493,28672],q 9 [20493,28672],q 1 [28672,28678],q 4 [20493,28678],q 8 [20493,28678],q 8 [20493,28677],q 6 [20487],q 4 [20491,12949],q 0 [20491,12949],q 1 [20491],q 13 [20491,12949],q 7 [17050],q 31 [],q 7 [17048],q 1 [20491,17048],q 2 [20487,12769],q 0 [20487,12769],q 11 [20487,12769],q 6 [20487,12769],q 13 [20487,12769],q 7 [540683],q 10 [12769,540683],q 12 [540683],q 1 [20487,540683],q 7 [679940],q 9 [12949,679940],q 1 [20491,679940],q 4 [20486],q 6 [739],q 8 [20486,319909],q 0 [20486,16399,319909],q 10 [16399],q 5 [16399,319909],q 1 [20486,319909],q 8 [20490],q 9 [16397],q 28 [],q 1 [20490,181163],q 5 [16399],q 13 [20486,20487],q 1 [20486,20487],q 4 [20485],q 12 [16399],q 6 [20485,339983],q 8 [20485,339983],q 0 [20485,16399,339983],q 9 [20485,339983],q 13 [20485,339983],q 1 [20485,340144],q 5 [16397],q 1 [20484,20485],q 11 [20484,20485],q 10 [16397],q 6 [20484,12453],q 4 [20488,4199],q 9 [16399],q 6 [20488,4199],q 1 [20488,4199],q 4 [20484,8357],q 11 [16399],q 6 [20484,8357],q 1 [20484,8357],q 12 [8357],q 13 [20495],q 1 [16395,28680],q 4 [16395,20493],q 12 [16395],q 1 [16395,28676],q 1 [28672],q 1 [16395,28672],q 0 [16395],q 1 [16391,28787],q 8 [20493,28787],q 10 [20493,28787],q 5 [16391,28787],q 10 [16395],q 5 [16395],q 2 [20486,20487],q 2 [16395,20486,20487],q 0 [20486,20487],q 0 [16395,20486,20487],q 1 [16395,20486,20487],q 2 [20486,12709],q 0 [20486,12709],q 6 [20486,12709],q 1 [20486],q 1 [16395,20486],q 11 [20486,12709],q 4 [16395],q 8 [20486,369061],q 0 [16395,20486,369061],q 1 [16395,20486,369061],q 11 [20486],q 11 [20485,339983],q 1 [16395],q 2 [20485,339983],q 10 [339983],q 6 [20484,168297],q 1 [16395,20484,168297],q 13 [20484],q 8 [12649,21134],q 0 [16395,12649,21134],q 13 [21134],q 8 [12649,21133],q 0 [16395,12649,21133],q 13 [21133],q 4 [16395,12649],q 0 [16395,12649],q 5 [16395,12649],q 9 [12649],q 10 [16395,12649],q 30 [],q 6 [12649],q 0 [20493,28677,610320],q 3 [20493,28677,610320],q 1 [28677,610320],q 0 [20485],q 3 [16395,12649],q 12 [16395,12649],q 1 [16395,20485],q 2 [16391,12401],q 0 [16391,12401],q 1 [16391],q 11 [16391,12401],q 9 [16391,12401],q 5 [16391,12401],q 8 [12401,1003531],q 0 [16391,12401,1003531],q 12 [1003531],q 1 [16391,1003531],q 8 [12649,667652],q 0 [16395,12649,667652],q 1 [16395,667652],q 1 [16394,29399],q 9 [12949],q 1 [16390,20491],q 4 [16390],q 0 [16390],q 5 [16390],q 10 [16394],q 5 [16394],q 7 [16394],q 6 [20484],q 1 [16394,20484,168661],q 1 [16390,16391],q 6 [20486],q 0 [16394,16395],q 4 [16394,16395],q 6 [20488],q 12 [20488],q 10 [20491],q 11 [16390],q 1 [16390,20491,676213],q 0 [16390,20853],q 10 [1028099],q 1 [16390,20853,1028099],q 13 [20484,20485],q 8 [21494],q 1 [16390,21494],q 10 [21494],q 8 [21493],q 10 [21493],q 9 [20485],q 1 [16394,20485,340695],q 12 [16394],q 1 [16389,28696],q 5 [16389,28696],q 9 [16389],q 1 [16389,28683],q 6 [20495],q 12 [20495],q 8 [20493,28676],q 16 [16393],q 12 [16393],q 1 [16393,28676],q 1 [16389],q 10 [12769],q 1 [16395,20487],q 8 [21338],q 1 [28678,28688],q 13 [20493,28678],q 0 [20493,28678],q 8 [21337],q 10 [24591,21337],q 12 [21337],q 1 [16389,21337],q 7 [16393],q 11 [20487],q 1 [16393,20487,57827],q 4 [16389],q 0 [16389],q 3 [20491,12949],q 11 [16389],q 5 [16389],q 1 [16389,20491],q 12 [20490],q 9 [16389,106520],q 12 [20489],q 5 [16389,106520],q 1 [16389,20489,106520],q 4 [20489],q 0 [20489],q 1 [20489],q 1 [16389,20489],q 6 [20489],q 11 [16389,24591],q 4 [16397],q 0 [16397],q 1 [8197,20558],q 6 [8197,20558],q 4 [8197,20558],q 10 [20558],q 1 [8197],q 0 [8197,20493],q 1 [16384,8197],q 8 [8196,12385],q 1 [8196],q 1 [8197,20486],q 10 [12366],q 9 [20486,12366],q 9 [20486],q 7 [8197],q 10 [20490],q 4 [20499,13017],q 0 [20499,13017],q 10 [20499,13017],q 1 [8196,20499],q 6 [8196],q 8 [8196],q 10 [20497],q 9 [20497],q 1 [8196,20497,495715],q 10 [16393],q 1 [20485,16393],q 5 [16393],q 2 [12294,20485],q 0 [12294,20485],q 7 [8196],q 10 [20496],q 9 [20496],q 1 [8196,20496,581729],q 6 [8196,581729],q 13 [8196],q 10 [20495],q 9 [20495],q 11 [20495],q 0 [12745,20486],q 5 [16386,12745],q 1 [16386,20486],q 10 [16386,12745],q 7 [12745],q 0 [13045,8197],q 10 [20480,13045],q 12 [20480,13045],q 1 [20480],q 1 [20480,8197],q 10 [20495,24815],q 4 [20496,20497],q 10 [20496,20497],q 20 [8196],q 1 [8196,20577,20499],q 0 [8196,20577,20499],q 7 [12709],q 4 [20484],q 11 [53250],q 1 [16392,53250],q 6 [53250],q 8 [20484],q 8 [8196,20577],q 15 [],q 1 [28672,28690],q 13 [8197,12366],q 9 [12366],q 1 [8197,20498],q 1 [8196,20577],q 4 [8196,20577],q 3 [8196,20577],q 2 [8196,20577],q 10 [12290],q 10 [475136],q 9 [475136],q 0 [8196,20577],q 1 [8196,28672],q 0 [20937,1077263],q 6 [1077263],q 8 [20495],q 10 [20558,13041],q 0 [8197,20558,13041],q 3 [8197,20558,13041],q 9 [20558,13041],q 2 [8197,20558,13041],q 12 [13041],q 0 [12293,799479],q 1 [20480,799479],q 4 [12293],q 0 [12529,8196],q 10 [16384,12529],q 1 [16384,8196],q 4 [20497],q 0 [20497],q 1 [20497],q 1 [8197,20497],q 5 [12298],q 7 [12298],q 14 [20482],q 1 [20482,8196,8197],q 9 [20482],q 11 [20482],q 0 [8196,8197,16399],q 14 [16399],q 9 [20480],q 2 [8196,8197],q 11 [20480],q 14 [20480],q 8 [20485,340023],q 0 [16392,20485,340023],q 10 [16392,340023],q 12 [16392],q 0 [13045],q 0 [13045,8196],q 14 [20497],q 1 [8196,8197,20497],q 8 [1028111],q 10 [1028111],q 0 [13373,21570],q 1 [4096,21570],q 7 [],q 7 [13373],q 8 [21570],q 11 [20577],q 1 [16392,53250,20486],q 4 [20486,12709],q 3 [20486,12709],q 9 [20486,12709],q 9 [16386],q 2 [20498,739],q 2 [8198,20498,739],q 8 [8198],q 2 [20493],q 9 [16384],q 1 [16384,28683],q 11 [20486,16399],q 4 [8197,20486],q 0 [8197,20486],q 6 [8197,20486],q 2 [16399,20793],q 0 [16399,20793],q 10 [16399,20793],q 6 [20793],q 11 [16399,20793],q 13 [8197],q 5 [16386],q 3 [8197,20558],q 12 [16386],q 1 [20496,581781],q 13 [12294],q 10 [21522],q 0 [8196,12385,21522],q 2 [20484,12453],q 0 [20484,12453],q 1 [20484],q 11 [20484,12453],q 8 [8196,99041],q 0 [8196,20498,99041],q 10 [20498],q 9 [20498],q 1 [8196,20498,99041],q 4 [8198,21253],q 0 [8198,21253],q 9 [21253],q 6 [8198,21253],q 1 [8198,21253],q 0 [16399],q 8 [8197,20558],q 12 [16384],q 0 [12529,20725],q 4 [20725],q 8 [20725],q 9 [20499],q 11 [20499],q 1 [8196,8197,20499],q 0 [8196,8197,20499],q 14 [20499],q 10 [16384],q 1 [8198],q 0 [8198,20493],q 1 [16384,8198],q 10 [475151],q 0 [8196,20577,475151],q 10 [20499,799451],q 12 [20499],q 1 [20499,799451],q 6 [12293],q 3 [16386,20493,29131],q 1 [16386,29131],q 14 [16384],q 10 [20497,496396],q 12 [20497],q 1 [20497,496396],q 4 [12294,20485],q 11 [16384,20485],q 1 [16384,20485],q 9 [12294,20485],q 19 [20493],q 19 [8198],q 10 [16386],q 1 [16386,8198],q 0 [12529,20485],q 12 [16384,12529],q 0 [20721,8197],q 10 [16384,20721],q 25 [],q 11 [16384,20721],q 8 [8198,791265],q 0 [8198,20498,791265],q 9 [20498,791265],q 11 [20498],q 1 [8198,20498,791265],q 0 [13373,21569],q 3 [13373,21569],q 10 [21569],q 1 [4096,21569],q 8 [21569],q 5 [4096,13373],q 4 [20485,339983],q 3 [20485,339983],q 3 [8197,12366],q 2 [8197,12366],q 1 [16386,8197],q 1 [8196,180323],q 4 [12294,20629],q 3 [12294,20629],q 2 [12294,20629],q 9 [12294,20629],q 1 [16386,20629],q 0 [12294,20629],q 10 [21521],q 9 [21521],q 1 [8196,21521],q 5 [8196,12385],q 0 [8196,12385,21521],q 7 [8196,12385],q 9 [20493,28691],q 1 [28690,28691],q 0 [8197,78067],q 9 [16384,78067],q 10 [16384,78067],q 1 [16384,8197,78067],q 10 [12366,21174],q 0 [8197,12366,21174],q 3 [8197,12366,21174],q 12 [21174],q 1 [28690,871],q 8 [20490,50089],q 0 [16388,20490,50089],q 1 [16388,20490,50089],q 0 [8197,12366,17077],q 1 [8197,17077],q 9 [12366,17077],q 10 [12366,17077],q 11 [17077],q 0 [13373,20493],q 11 [16397,20498],q 6 [8197],q 2 [16397,20498],q 14 [16397],q 2 [20485,341143],q 0 [20485,341143],q 5 [8192,341143],q 1 [8192,20485,341143],q 12 [20496,20497],q 1 [20496,20497],q 20 [12293],q 6 [12294,20629],q 1 [20629],q 1 [20629,16395],q 5 [12294],q 11 [12294,20629],q 5 [16388],q 11 [16388,20529],q 1 [16388,20529],q 6 [20529,20495],q 8 [20841,1212431],q 0 [16395,20841,1212431],q 13 [1212431],q 0 [12298,1110417],q 9 [4096],q 1 [4096,1110417],q 8 [12298],q 7 [12298,1110417],q 0 [13045,8198],q 2 [20480,13045],q 10 [16393,57359],q 9 [57359],q 1 [16393,20486],q 4 [12293,20486],q 2 [12293,20486],q 9 [12293,20486],q 0 [12293,20486],q 11 [16386,20486],q 2 [16384,12529],q 0 [12529],q 0 [12529,8197],q 1 [16384,20629],q 8 [12294,20629],q 0 [12529,20486],q 5 [16384,12529],q 11 [16384,12529],q 1 [16384,20486],q 0 [12294,245909],q 4 [12294],q 1 [16384,245909],q 19 [8196],q 0 [8196,20493],q 1 [16386,8196],q 14 [20498],q 0 [12745,8197],q 12 [16386,12745],q 9 [12366,20495],q 10 [12366,20495],q 0 [8197,78583],q 9 [20480,78583],q 10 [20480,78583],q 1 [20480,8197,78583],q 12 [20480],q 4 [12293,21262],q 1 [16386,21262],q 3 [12293,21262],q 10 [21262],q 2 [12293,21262],q 9 [12293,21262],q 14 [20496],q 11 [20496],q 6 [12290],q 2 [20493,29847],q 0 [20493,29847],q 0 [21565,1241103],q 7 [1241103],q 10 [1241103],q 8 [1241103],q 10 [475139],q 8 [4106],q 11 [16397,181031],q 1 [4106,181031],q 10 [16397,181031],q 0 [12293,799895],q 1 [8192,799895],q 9 [12293],q 7 [12293,799895],q 1 [20484,168337],q 8 [20529,20493],q 0 [16388,20529,20493],q 1 [16393,20486,20487],q 0 [12294,774293],q 1 [20480,774293],q 10 [20480],q 9 [12290],q 11 [12290],q 14 [12290],q 2 [16388,16389],q 2 [16388,16389,20491],q 0 [16388,16389],q 0 [16388,16389,20491],q 5 [16388,16389],q 1 [16388,16389],q 6 [20491],q 1 [16388,16389,20491],q 0 [8198,246533],q 9 [16384,246533],q 1 [16384,8198,246533],q 0 [16389,20493],q 1 [16389,28675],q 10 [21722],q 0 [8196,99061],q 1 [20480,8196,99061],q 0 [12293,798963],q 1 [16384,798963],q 1 [20486,28672],q 2 [20493,28683],q 1 [16386,28683],q 1 [8197,28672],q 0 [20937,8197],q 10 [16386,20937],q 11 [16386,20937],q 3 [16392,53250],q 3 [16392,53250,20487],q 4 [20487],q 9 [20487],q 8 [20487],q 5 [12293],q 11 [16384,20486],q 5 [16384],q 8 [12293,21262],q 9 [12293,58124],q 11 [12293],q 1 [16393,58124],q 10 [16393,58124],q 1 [16394,152277],q 9 [12294],q 7 [16392],q 0 [20485,340211],q 5 [16384,340211],q 4 [8196,12385],q 3 [8196,12385],q 2 [8196,12385],q 0 [8196,12385],q 12 [20491],q 2 [16390,16391],q 1 [16390,16391,20491],q 0 [16390,16391,20491],q 0 [21257,8197],q 10 [12290,21257],q 11 [12290,21257],q 0 [20486,246181],q 5 [16384,246181],q 1 [16384,20486,246181],q 11 [20486,16397],q 0 [12745,8198],q 2 [16386,12745],q 6 [8198],q 4 [16393],q 0 [16393],q 8 [12294,152289],q 0 [12294,20498,152289],q 1 [20498,152289],q 0 [12529,20726],q 8 [20726],q 8 [13569],q 10 [20506,13569],q 12 [13569],q 1 [16389,20506],q 0 [12745,20485],q 3 [16386,12745],q 1 [16386,20485],q 6 [20485],q 0 [20493,28915],q 5 [16384,28915],q 1 [16384,28915],q 9 [20496,581710],q 10 [20496,581710],q 1 [8197,20496,581710],q 4 [20496,581645],q 0 [8196,20496,581645],q 1 [8196,20496],q 6 [12293,20486],q 1 [20486,16395],q 2 [12293,20486,16395],q 1 [8197,28675],q 0 [12745,20942],q 6 [20942],q 0 [12745,8196],q 1 [28676],q 1 [16384,28676],q 14 [16386],q 10 [20493,29479],q 0 [4106,20493,29479],q 3 [4106,20493,29479],q 8 [12337,21782],q 0 [16388,12337,21782],q 1 [16388,21782],q 10 [21782],q 0 [13045,12293],q 10 [1138703],q 13 [8197,20558],q 0 [8197,20558],q 7 [8198],q 9 [20496,582405],q 1 [8198,20496,582405],q 6 [8198,582405],q 13 [8198],q 11 [16397,20658],q 2 [16397,20658],q 8 [8198,790841],q 0 [8198,16399,790841],q 9 [16399,790841],q 1 [8198,790841],q 2 [16388,20529,20491],q 0 [16388,20529,20491],q 6 [20529,20491],q 11 [12293,21262],q 4 [16392,16393],q 1 [16392,16393],q 10 [20489,106511],q 13 [20489,106511],q 0 [12294,20489,106511],q 2 [12294,20489,106511],q 6 [20491,49813],q 9 [16388,49813],q 11 [16388],q 1 [16388,20491,49813],q 2 [16399,20497],q 0 [16399,20497],q 11 [20493,28679],q 1 [16395,28679],q 0 [16393,20484,12453],q 1 [16393,20484],q 12 [12453],q 8 [12298,49553],q 0 [12298,16388,49553],q 1 [16388,49553],q 12 [12298,49553],q 13 [12298],q 10 [20499],q 1 [8196,20499,99033],q 0 [20490,1110953],q 1 [4096,20490,1110953],q 3 [8197,20493,28748],q 2 [8197,20493,28748],q 7 [8197,28748],q 2 [20498,13025],q 0 [20498,13025],q 10 [20498,13025],q 11 [20498,13025],q 6 [13025],q 0 [16395,20493],q 1 [16395,28675],q 1 [8197,28688],q 0 [8196,98545],q 1 [16384,8196,98545],q 9 [20495,78063],q 10 [20495,78063],q 1 [8197,78063],q 0 [8197,20496,581645],q 1 [8197,20496],q 6 [581645],q 1 [16394,799447],q 10 [16394,799447],q 20 [8197],q 10 [20497,495692],q 11 [20497,495631],q 2 [20497,495631],q 1 [20491,675989],q 9 [12294,675989],q 11 [12294],q 6 [8197,739],q 8 [8197,78563],q 0 [8197,20498,78563],q 9 [20498,78563],q 10 [20498,78563],q 12 [20498],q 9 [20499,78555],q 10 [20499,78555],q 1 [8197,20499,78555],q 8 [12297,1392755],q 0 [12297,16391,1392755],q 10 [12297,1392755],q 11 [16391],q 1 [16391,1392755],q 2 [20499,13017],q 1 [20499],q 1 [8197,20499],q 13 [13017],q 8 [20489,106611],q 0 [16391,20489,106611],q 10 [20489,106611],q 1 [16391,20489,106611],q 10 [13093,20489],q 0 [4106,13093,20489],q 3 [4106,13093,20489],q 1 [4106,20489],q 5 [12297],q 7 [12297],q 12 [12297],q 6 [20484,20485],q 10 [12297,1393123],q 1 [20487,1393123],q 1 [16393],q 1 [16393,20485],q 8 [12297],q 10 [12297],q 10 [21721],q 9 [13061,21721],q 0 [8198,13061,21721],q 2 [8198,13061,21721],q 1 [8198,21721],q 11 [21721],q 1 [16393,21262],q 6 [12293,21262],q 9 [20493,622596],q 2 [20493,28681,622596],q 1 [28681,622596],q 11 [20485,16397],q 1 [8198,20485],q 4 [8198,20485],q 0 [8198,20485],q 9 [20495,790765],q 1 [8198,790765],q 0 [20493,28689],q 0 [8197,12366,17079],q 1 [8197,17079],q 9 [12366,17079],q 10 [12366,17079],q 11 [17079],q 0 [20721,1159183],q 7 [1159183],q 8 [1159183],q 0 [8198,20496,581645],q 1 [8198,20496],q 3 [12294,20485],q 11 [16386,20485],q 2 [20496,20497],q 2 [8198,20496,20497],q 0 [20496,20497],q 0 [8198,20496,20497],q 20 [8198],q 6 [12294],q 20 [12294],q 8 [12337,20493],q 0 [16388,12337,20493],q 11 [16388,12337],q 11 [20497,496423],q 10 [20497,496423],q 1 [4106,20497,496423],q 9 [16390],q 1 [16390,20490,381865],q 1 [20496,582414],q 12 [20496],q 13 [12293],q 9 [20499,791257],q 1 [8198,20499,791257],q 1 [8198,20499],q 1 [28676,28677],q 8 [12337,21781],q 0 [16388,12337,21781],q 1 [16388,21781],q 10 [21781],q 8 [12297,12337],q 0 [12297,16388,12337],q 9 [16388,12337],q 12 [12297,12337],q 13 [12297],q 8 [12293,798775],q 0 [12293,16392,798775],q 1 [16392,798775],q 11 [12293,798775],q 2 [20484,20485],q 2 [16395,20484,20485],q 0 [20484,20485],q 0 [16395,20484,20485],q 1 [16395,20484,20485],q 6 [12297],q 0 [8198,774917],q 9 [20480,774917],q 1 [20480,8198,774917],q 1 [20488,798823],q 9 [20493,28679],q 1 [28678,28679],q 13 [20493,28679],q 7 [339983],q 1 [20485],q 10 [20493,339983],q 6 [12293,739],q 1 [28675,28683],q 1 [8197,28691],q 10 [20489,107276],q 0 [12293,20489,107276],q 3 [12293,20489,107276],q 9 [12293,107276],q 2 [12293,20489,107276],q 1 [20489,107276],q 10 [20490,799659],q 0 [12293,20490,799659],q 3 [12293,20490,799659],q 1 [20490,799659],q 4 [20495],q 4 [20488,12389],q 0 [20488,12389],q 1 [16390,20488],q 0 [16390,20488,12389],q 0 [20496,581645,585732],q 7 [585732],q 1 [20496,585732],q 3 [20493,28676],q 1 [16386,28676],q 0 [12529,8198],q 8 [12293,799459],q 0 [12293,20498,799459],q 10 [20498,799459],q 3 [12298,20881],q 0 [12298,20881],q 6 [12298,20881],q 1 [20485,16395],q 2 [12294,20485,16395],q 8 [8197,78139],q 0 [8197,16399,78139],q 9 [16399,78139],q 1 [8197,78139],q 10 [16399,78139],q 1 [16389,24979],q 12 [12298],q 13 [20491],q 6 [12298],q 8 [12294,368789],q 0 [12294,16395,368789],q 1 [16395,368789],q 9 [12294,368789],q 8 [20485,340283],q 0 [20485,16399,340283],q 10 [16399,340283],q 1 [20485,340283],q 4 [20488,20489],q 1 [20488,20489],q 13 [20488,20489],q 10 [12298,340371],q 0 [12298,20485,340371],q 3 [12298,20485,340371],q 1 [20485,340371],q 1 [20497,496019],q 4 [20497,495631],q 9 [20497,495631],q 1 [20499,152281],q 8 [20529,20489],q 0 [16388,20529,20489],q 10 [20489],q 6 [12293,53250],q 8 [20529,1208335],q 0 [16388,20529,1208335],q 10 [1208335],q 0 [20488,20489],q 8 [20488],q 10 [20488],q 1 [20488,180327],q 7 [16391],q 6 [20491,675953],q 9 [16391,675953],q 1 [16391,20491,675953],q 10 [20491,675953],q 10 [12366,21173],q 0 [8197,12366,21173],q 3 [8197,12366,21173],q 9 [12366,21173],q 2 [8197,12366,21173],q 1 [8197,21173],q 12 [21173],q 11 [21173],q 2 [8198,20493,28672],q 1 [8198,28672],q 1 [16392,16393,20486],q 8 [20493,28727],q 0 [16392,20493,28727],q 4 [16388,16389],q 8 [20486,12709],q 6 [20484,167989],q 1 [16392,20484,167989],q 11 [20484,167989],q 1 [20488],q 8 [8196,98617],q 0 [8196,16399,98617],q 1 [8196,98617],q 1 [16393,20484,20485],q 6 [20495,49389],q 1 [16389,20488,24679],q 1 [28688],q 5 [28688],q 2 [20493,28676],q 5 [28676],q 3 [20493],q 8 [20793],q 1 [20793],q 13 [20486],q 0 [20490],q 4 [20490],q 6 [20490],q 13 [20490],q 0 [20486],q 8 [13025],q 1 [20498],q 13 [20489],q 2 [20486],q 3 [20489],q 2 [20485],q 13 [20485],q 11 [20484],q 1 [28690],q 0 [20493,28690],q 0 [20495],q 2 [20495],q 0 [16395,20486],q 2 [16395,20485],q 0 [16395,20485],q 3 [16395],q 2 [20484],q 2 [16395,20484],q 0 [20484],q 0 [16395,20484],q 1 [16395,20484],q 8 [12649],q 1 [16390],q 0 [20491],q 4 [20491],q 2 [16390],q 0 [16390,20491],q 0 [16394],q 4 [16394],q 2 [8198,21253],q 0 [20499],q 4 [20499],q 0 [8196,20499],q 4 [16399],q 0 [20486,16399],q 2 [20486,16399],q 4 [20496],q 0 [20498],q 4 [20498],q 3 [20498],q 0 [8197,16399],q 0 [8196,16399],q 2 [20499],q 0 [8198,20499],q 0 [12293,20489],q 3 [12293,20489],q 2 [12293,20489],q 2 [12293],q 0 [12293],q 0 [12293,21262],q 1 [21262],q 1 [28683],q 3 [20493,28683],q 5 [28683],q 2 [20482],q 2 [8198],q 2 [20482,8198],q 10 [20482],q 6 [20482],q 1 [20482],q 0 [12294],q 6 [20480],q 3 [12294],q 2 [12294],q 4 [16392],q 0 [16392],q 0 [16392,20486],q 3 [12293],q 2 [20480],q 2 [20480,8198],q 3 [8198],q 0 [20937],q 3 [20497],q 0 [8197,20498],q 2 [16395,20493],q 3 [8197],q 2 [8197],q 12 [12290],q 5 [12290],q 3 [8196],q 1 [16390,20853],q 4 [12297],q 0 [12297],q 0 [12297,20486],q 1 [28691],q 5 [28691],q 8 [20841],q 0 [16395,20841],q 9 [20841],q 1 [16395,20841],q 2 [16386],q 2 [16386,8198],q 12 [20482],q 3 [20485],q 2 [8198,20493],q 2 [16384],q 2 [16384,8198],q 8 [20529],q 0 [16388,20529],q 10 [8192],q 1 [8192],q 6 [8192],q 5 [8192],q 2 [12290],q 2 [12290,8198],q 8 [12337],q 0 [16388,12337],q 1 [16388],q 3 [12297],q 2 [12297],q 1 [4096],q 11 [4096],q 5 [4096],q 0 [12294,20498],q 2 [12294,20498],q 0 [21565],q 1 [4096,21565],q 2 [16397],q 2 [8198,16397],q 0 [8198,16397],q 1 [28677],q 1 [28678],q 1 [20658],q 0 [13373],q 1 [28689],q 0 [12298],q 4 [12298],q 0 [12298,20486],q 2 [16399],q 0 [8198,16399],q 3 [20486],q 4 [20488],q 1 [16388,20488],q 13 [20488],q 0 [20487],q 2 [20487],q 13 [20487],q 0 [20721],q 6 [20721],q 0 [21257],q 1 [21257],q 0 [12294,16392],q 1 [16392],q 3 [8197,20493],q 2 [8197,20493],q 2 [8198,20485],q 2 [20496],q 2 [8198,20496],q 0 [20496],q 0 [8198,20496],q 2 [20497],q 2 [8198,20497],q 0 [8198,20497],q 2 [20498],q 2 [16389],q 2 [16389,20491],q 0 [16389,20491],q 0 [12297,16388],q 4 [16388],q 0 [16388],q 3 [16388,20495],q 2 [12293,16395],q 0 [12293,16395],q 2 [20491,16397],q 0 [20491,16397],q 2 [12293,20491],q 0 [12293,20491],q 3 [20491],q 0 [12293,20498],q 9 [13061],q 0 [8198,13061],q 2 [8198,13061],q 0 [12294,16395],q 0 [12294,20489],q 0 [16388,20489],q 2 [16388],q 2 [16388,20491],q 0 [16388,20491],q 3 [16388,20491],q 1 [16388,20491],q 0 [20485,16399],q 3 [16399],q 0 [16388,20493],q 0 [20488],q 0 [16390,20488],q 2 [20489],q 10 [20506],q 2 [20491],q 2 [16395]]
def B_23_3 : BT (List (List Nat)) := BT.empty
lemma B_23_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 3 xs.toFinset) B_23_3 := .empty
def U_23_4 : List Nat := []
def P_23_4 : BT (Option BoundPool) := buildPoolsSubBT 11 W_23 r_23 S_23 ps_23 U_23_4
def N_23_4 : List NodeSpec := [([11,0,12,3,5],[],[]),([0,16,18,3,5],[],[]),([23,0,24,3,5],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_4 : checkNodesBT W_23 g_23 F_23 P_23_4 A_23 B_23_3 4 N_23_4 = true := by decide +kernel
def B_23_4 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_4
set_option maxRecDepth 500000 in
lemma B_23_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 4 xs.toFinset) B_23_4 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok (buildPoolsSubBT_sound S_23_ok) A_23_ok B_23_3_ok C_23_4
def U_23_5 : List Nat := (r 0 25)
def P_23_5 : BT (Option BoundPool) := buildPoolsSubBT 11 W_23 r_23 S_23 ps_23 U_23_5
def N_23_5 : List NodeSpec := [([27,0,30,1,3,4],[0],[]),([11,0,1,3,4,5],[],[0]),([27,0,1,3,31,4],[0],[]),([34,0,1,3,32,5],[],[]),([0,12,9,3,10,5],[],[0]),([35,0,36,3,5,7],(r 1 4),[]),([15,39,0,1,3,5],[],[]),([35,40,0,1,3,5],[5,6],[]),([15,0,1,3,43,5],[],[]),([48,0,1,2,3,4],[],[]),([49,50,0,24,3,5],[],[0]),([51,52,0,13,3,5],[],[1]),([23,0,1,2,3,5],[],[0]),([53,0,20,3,4,5],[],[]),([55,0,56,3,5,7],([1]++r 7 4),[1]),([57,24,20,3,4,5],[],[]),([58,24,20,3,4,5],[],[]),([59,35,0,36,3,5],[4,11],[]),([0,24,20,61,4,5],[12],[]),([40,0,16,1,3,5],[6],[]),([27,54,0,3],(r 13 4),[]),([62,15,0,1,64,5],[17,18,19],[]),([15,0,1,65,3,5],[17,20],[]),([15,66,0,1,3,5],[],[]),([59,15,0,1,67,5],[5,6],[]),([15,0,1,18,3,5],[],[0]),([62,42,0,1,3,5],[21,22],[]),([59,55,0,56,3,5],[10,11],[]),([59,15,0,1,68,5],[5,22],[]),([70,27,0,1,3,4],[],[]),([15,0,1,71,3,5],[],[]),([0,24,21,3,22,5],[],[0]),([62,72,0,1,3,5],[22,23],[]),([75,54,0,2,3,5],[24],[]),([77,15,0,1,3,5],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_5 : checkNodesBT W_23 g_23 F_23 P_23_5 A_23 B_23_4 5 N_23_5 = true := by decide +kernel
def B_23_5 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_5
set_option maxRecDepth 500000 in
lemma B_23_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 5 xs.toFinset) B_23_5 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok (buildPoolsSubBT_sound S_23_ok) A_23_ok B_23_4_ok C_23_5
def U_23_6 : List Nat := ([0,2]++r 4 7++[12,13]++r 16 5++[22]++r 24 101)
def P_23_6 : BT (Option BoundPool) := buildPoolsSubBT 11 W_23 r_23 S_23 ps_23 U_23_6
def N_23_6 : List NodeSpec := [([79,27,0,1,3,4],([0]++r 25 6),[]),([80,27,0,1,3,4],([0]++r 26 4++[31,32,33]),[]),([82,27,1,3,4],[5,26,34],[]),([69,0,1,81,3],[5,25,31,35,36,37],[]),([85,0,86,3,4],([5]++r 38 7),[]),([87,27,28,0,1,3,4],[5,16,28,45,46],[]),([27,0,89,3,4],[0,5,47,48],[]),([90,84,0,2,3,91,4],[5,16,42,43,49],[1]),([92,27,28,0,3,4],[0,5,28,31,50],[]),([93,27,28,0,3],[16,28,31,51,52],[0]),([51,52,0,2,3,4,5],[],[0,1]),([94,27,0,1,3,4],([0]++r 26 4++[31,45]),[]),([27,0,1,3,29,4,6],[0,5,16,28,53],[0]),([95,27,0,1,3,4],([0,16]++r 25 5++[31]),[]),([96,0,12,2,3,8,5],[],[1]),([51,0,1,13,3,32,5],[],[0]),([0,12,2,3,8,10,5],[54,55,56],[0,1]),([97,27,0,1,3,4],[0,25,26,27,29,31,57],[]),([37,17,15,0,3,5],[5,6,13,19,22],[]),([98,27,0,1,3,4],([0]++r 25 5++[31,45]),[]),([72,15,0,1,3,5],([5]++r 17 4++[22,58]),[]),([27,0,99,3,4],[0,5,59,60],[]),([0,1,101,2,103,4,5],[61],[]),([38,0,1,3,104],[5,18,35,62],[]),([49,50,0,1,2,3,5],[],[0]),([106,15,0,1,3,5],[5,17,19,20,22],[]),([57,1,2,20,3,4,5],[],[0]),([107,108,0,1,2,3,4],[],[0]),([0,1,2,46,3,4,47],[],[0]),([59,55,54,0,2,3,5],[16,63,64],[0,1]),([50,0,24,20,3,4,5],[],[0]),([0,109,2,3,4,33,5],[],[1]),([87,27,0,1,3,4,6],[5,16,31,45,53],[]),([58,1,2,20,3,4,5],[],[0]),([92,0,110,3,4],[0,5,28,41,65,66],[]),([55,0,56,3,5],(r 7 4++[24,41,67]),[0]),([0,24,21,20,3,4,5],([12]++r 68 4),[0]),([15,0,1,36,3,5,7],([5,6,22]++r 72 5),[0]),([111,0,1,2,45,4,5],[],[]),([62,15,0,41,1,3,5],[6,13,18,22],[0,1]),([69,37,27,0,1,3,4],[0,5,31],[0]),([112,0,24,19,3,4,5],[77,78],[]),([60,0,24,20,3,4,5],[68,71],[0]),([0,12,9,2,3,8,5],[],[0]),e6 [113] [79,80],([0,19,3,115,4,5,116],[5,81],[]),([0,24,19,61,4,5,7],[81,82,83],[0]),([117,1,2,119,3,4,5],[79,84],[]),([105,15,120,0,3],[5,18,22,62,85],[1]),([0,122,3,4,116],[5,86],[]),([35,15,0,1,3,5,7],[5,13,22,87,88,89],[0]),([123,0,1,3,88],[5,25,31,35,90,91],[]),([15,0,1,3,64,5],[5,6,18,20,22,92,93],[0]),([125,126,1,2,3,4,5],[94],[]),([69,92,27,0,1,3,4],[0,5,25,28,31],[]),([0,24,20,3,4,22,5],[68,70],[0]),([127,0,1,128,3],[5,35,62],[]),([129,0,24,20,3,4,5],[68],[]),([0,1,2,20,61,4,5],[80,95],[0]),([15,0,16,1,3,5,7],[5,13,22,96,97,98],[0,1]),([130,84,2,3,4],[5,43,99,100,101],[]),([35,0,36,3,5],[2,4,6,22,41],[0]),([59,35,15,0,1,3,5],[5,18,89],[0]),([49,0,24,20,3,4,5],[],[0]),([0,1,2,21,3,22,5],[],[0]),([131,15,0,1,3,5],([5,6,13]++r 17 4++[22,76]),[]),([15,0,1,3,132,5],[13,17,18,20],[]),([0,19,3,4,133,5],[5,102,103,104],[]),([59,15,0,1,36,3,5],[5,6,18,76,105,106],[0]),([134,0,24,20,3,4,5],[12,68,71],[]),([15,0,1,3,67,5],[5,13,18,20,107,108],[0]),([27,0,12,3,6],[0,16,31,109,110],[0]),([55,54,0,2,3,5,7],[7,16,64,111,112],[0,1]),([40,15,0,1,3,5],[5,6,17,20,22],[0]),([37,38,15,0,1,3,5],[5,6,18,22],[0]),([59,15,0,16,1,3,5],[5,18,98],[0,1]),([62,15,0,135,1,3,5],[6,13,22],[]),([62,38,15,0,1,3,5],[5,18,92],[0]),([136,84,0,3,4],[16,42,113,114],[]),([73,62,15,0,1,3,5],[6,13,22],[0]),([137,54,0,2,3,5],([13,24,63]++r 115 4),[0,1]),([63,62,15,0,1,3,5],[5,18],[0]),([62,15,0,1,3,138,5],[5,18],[]),([15,0,1,3,139,5],[13,17,18,20],[]),([15,0,1,3,68,5],[5,13,18,20,22,98,119],[0]),([15,0,1,3,76,5],[13,18,20,22,120,121],[0,1]),([141,84,0,3,4],[16,42,122,123],[]),([114,0,24,20,3,4,5],[68],[]),([15,0,41,3,83],[5,62,124],[1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_6 : checkNodesBT W_23 g_23 F_23 P_23_6 A_23 B_23_5 6 N_23_6 = true := by decide +kernel
def B_23_6 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_6
set_option maxRecDepth 500000 in
lemma B_23_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 6 xs.toFinset) B_23_6 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok (buildPoolsSubBT_sound S_23_ok) A_23_ok B_23_5_ok C_23_6
def U_23_7 : List Nat := ([0,5,6,7,12,13,14]++r 16 5++[22]++r 24 6++[31,42,43,45,49,51,53,56]++r 61 4++[68,70,71,74]++r 76 8++r 86 4++[95,96,98,104,109,111,112,116,117,121]++r 125 378)
def P_23_7 : BT (Option BoundPool) := buildPoolsSubBT 11 W_23 r_23 S_23 ps_23 U_23_7
def N_23_7 : List NodeSpec := [e6 [144,145] [13,125,126],([0,147,2,3,124,5],([5]++r 127 5),[]),e6 [8] ([79,80,125,128]++r 132 4),([126,1,2,3,150,5],[5,136,137,138],[]),([151,126,1,3,4,5],([5,137]++r 139 7),[]),([126,153,2,3,4,5],([5,140]++r 146 6),[]),([78,27,0,1,3,4],([0,5,13,16]++r 25 5++[152]),[0]),([27,0,1,3,4,44],[5,13,16,29,31,153],[0]),([27,0,1,81,3,4],[0,5,25,28,31,154],[0]),([69,27,0,1,3,4],([0,5,13]++r 25 5++[31,45,155]),[0]),([154,117,1,2,3,5],(r 156 7),[]),([27,0,1,3,4,88],[0,5,28,31,163],[0,1]),([123,27,0,1,3,4],[0,5,13,25,26,28,29,31,45,164,165],[0]),([27,0,155,1,3,4],[0,5,25,28,31,166],[1]),([85,84,0,2,3,4],([13,16,42,43,45]++r 167 8),[0]),([118,151,0,1,3,4,5],([5,141,144]++r 175 7),[]),([27,0,1,110,3,4],[0,5,25,28,31,182],[0]),([90,0,148,1,156,3,4,5],[183,184,185],[]),e6 [157,7] [183,186,187,188],([90,158,117,1,2,3,4,5],[5,16,159,189],[]),e6 [159,160] [125,133,190,191],([117,1,160,2,3,4,5],([157,189]++r 192 7),[]),([161,117,1,3,4,5],([157,189]++r 199 4),[]),([90,0,1,162,3,132,4,5],[16,133],[]),e6 [164] [61,79,80,126,133,203,204],e6 [126,20] ([5,80]++r 205 4),e6 [167] ([79,80,126,133,177]++r 209 4),([0,148,168,3,4,5],[45,213,214,215],[]),([93,28,0,2,3,169,5],(r 216 7),[1]),([126,1,2,20,3,4,5],[5,138,207,208,223,224,225],[]),e6 [122,170] [5,45,226],([118,117,1,2,19,3,4,5],[5,157,189,227],[0]),e6 [171,7] ([133]++r 228 5),u6 [45,47] ([5,61]++r 233 4),u6 [46,45] ([5,61,233,234]++r 237 4),([117,1,2,20,3,4,5],[5,157,205,227,241],[]),([37,0,2,3,4,172,5],([5]++r 242 5),[]),u6 [49,20] [228,247],([59,0,1,2,4,174],([5]++r 248 4),[]),([0,24,122,3,4,5],[5,252,253],[0]),([0,24,19,3,4,143,5],([81,82]++r 254 6),[]),([62,15,0,1,3,5],[5,6,13,18,19,20,22,260],[0]),([60,0,24,19,3,4,5,7],([5,82]++r 261 5),[0]),u6 [129,20] [79,80,205],e6 [148,175] ([126,177]++r 266 5),([0,24,20,3,4,5],[5,12,68,70,71,271],[0]),([176,0,1,3,4,5],[5,16,45,272],[]),u6 [133] ([5,79,80]++r 273 4),([0,177,19,3,4,5],[5,277,278],[]),([0,19,3,4,178,5],[13,259,277,279,280,281],[]),u6 [112,19] ([133]++r 282 4),([179,19,3,4,5,116],[5,13,86,286,287,288],[]),([180,0,19,3,4,5],[5,13,252,289,290],[]),([0,24,1,2,61,4,5,7],[13,291,292],[0]),([105,181,90,120,0,3],(r 293 7),[0,1]),([114,0,19,3,4,5,116],[5,13,277,286,288,300,301,302],[0]),u6 [21,20] [70,95,205,228,247,303,304],([0,12,2,3,166,6,5],[109,305,306,307],[1]),([87,27,0,1,3,4],[0,5,16,25,26,28,29,31,308],[0]),([182,0,19,3,4,116],[13,81,104,277,309,310,311],[]),u6 [60,20] [80,205,283,304],([37,15,0,1,3,5],([5,13]++r 17 4++[22,312]),[0]),([183,0,1,2,3,5],[5,16,127,313],[]),([0,148,2,3,150,5],[5,314,315],[]),([173,185,1,2,3,4,5],([5,80]++r 316 9),[]),([126,1,2,19,3,124,4,5],[5,137,138,140,147,225,325],[0]),([185,24,19,3,4,5],[5,82,252,319,326,327],[]),e6 [186,166] [177],u6 [114,20] [80,205,328],([0,24,19,3,142,121],([277]++r 329 6),[]),([0,187,19,3,4,5],[13,277,335,336],[]),e6 [188,115] [5,328,337],u6 [108,45] [5,61],([0,190,19,3,4,5],[13,81,82,338,339,340],[]),u6 [119,7] [5,45,176,210,223,233,247,267,341],e6 [191,122] [5,45,210],([37,27,0,1,3,4],[0,5,13,25,26,27,29,31,342],[0]),e6 [192] [5,79,80,177,210,343,344],([193,0,1,2,61,4,5,7],[83,345,346],[]),e6 [112,148] [126,177,268,269,270],([15,0,1,3,5,7],[5,13,17,18,19,22,127],[0,1]),u6 [112,24] [13,125,347],([15,0,1,3,5,83],[5,6,13,17,22,348,349],[0]),([0,1,2,19,61,4,5,7],([45,285]++r 350 5),[0]),([179,0,19,3,4,5,116],[5,86,104,286,287,288,300],[]),e6 [188,61] [5,45,337,354,355],e6 [159,112] [125,133,191,356,357],u6 [115,116] [5,45,80,292,337,358,359],e6 [159,175] [125,133,191,266,356,357,360],([0,24,19,3,115,4,5],([5,81,82,125,333]++r 361 6),[0]),u6 [51,32] [126,177],([78,0,1,2,122,3,5],([5]++r 367 4),[]),([194,0,19,3,4,5,116],[5,86,104,277,286,300,302,371],[]),u6 [107,45] [5,61],([15,0,1,3,195,5],[5,13,18,19,372],[]),([196,19,3,4,5,116],[5,277,288,373],[]),e6 [20] [79,80,185,187,214,228,247,374,375,376],([0,24,19,3,197,4,5],([81,82,252]++r 377 4),[]),([0,19,3,4,44,5,116],[5,86,286,288,381],[0]),([0,19,3,4,116,121],[5,86,382],[0]),([93,27,0,1,3,4],[5,13,16,31,383,384],[0]),u6 [50,20] [228,247],e6 [118,20] [5,176,228,247,285],([105,120,0,13,3,14],(r 385 6),[0,1]),([117,1,2,3,4,8,5],[16,79,157,189,195,391],[]),u6 [125,7] [133,228,392,393,394],([0,24,19,3,61,4,5],[5,13,81,82,265,395,396,397],[0]),e6 [148,32] [5,126,132,177,184,270,398,399],([126,24,19,3,4,5],[5,82,252,400,401,402],[]),e6 [198] [61,79,80,125,126,247,257,403,404,405],u6 [20,22] [70,184,205,228,247,270,303],e6 [198,143] [61,133,406],e6 [199] ([61,79,80,133,177,210,228]++r 407 4),e6 [159,8] [16,125,133,191,411],([193,0,2,3,4,200,5],([5]++r 412 5),[]),([59,15,0,1,3,5],[5,18,19,62],[0,1]),([151,117,1,3,4,5],([144,159,189]++r 417 4),[]),e6 [202,143] [61,125,406],([0,12,2,3,8,5],[16,56,127,421,422],[0,1]),([0,12,2,3,169,6,5],([109]++r 423 4),[1]),e6 [203,204] [5,45,427,428,429],([27,0,1,3,195,4],[0,13,16,28,29,430],[]),e6 [206,205] [5,61,431,432],([105,130,120,2,3,4],([388,390]++r 433 5),[0]),([130,1,2,3,132,4,5],[80,125,407,435,438,439,440],[]),([15,0,1,3,207,5],[5,13,18,19,441],[]),([35,15,0,1,3,5],[6,13,17,20,22,87,88,89],[0]),([114,0,24,19,3,4,5,7],[82,262,365,366,442,443],[0]),([0,24,19,3,208,4,5],[77,81,82,125,333,444,445,446],[]),e6 [167,166] [228],([15,0,1,36,3,5],[5,13,17,18,19,74,76],[0]),([15,0,16,1,3,5],[5,6,13,18,19,22,96,98],[0,1]),([130,41,2,3,4,83],([435,439]++r 447 5),[0]),([38,15,0,1,3,5],[5,6,13,17,18,20,22,62],[0]),([15,0,1,3,5,104],[5,13,17,452],[0]),e6 [20,124] [5,184,228,247,270,303,392,453,454],e6 [193,112] [78,126,455,456],([93,28,0,2,3,166,5],[209,219,222,457,458,459],[1]),([127,15,0,1,3,5],[5,6,13,18,20,22,460],[0]),u6 [102,101] [5,16,61,461,462],([15,0,1,128,3,5],[13,19,62],[0]),([15,0,41,1,3,5],[13,22,62,121],[0,1]),e6 [209] [5,79,80,125,133,177,228,463,464],([105,15,0,1,3,5],[5,13,17,20,22,465],[0]),([130,1,2,3,76,4,5],([125,434,435]++r 466 5),[]),([0,12,2,3,210,5],[16,307,471,472,473],[]),([92,27,0,1,3,4],([0,5,13,16]++r 25 4++[31,474]),[0]),([0,1,211,3,4,26],([16]++r 475 6),[]),([90,84,0,2,3,4],[16,42,43,45,49,167,169,174,481],[0,1]),([55,54,0,2,3,5],[7,13,16,24,63,64,111,112,116,117,482,483],[0,1]),e6 [212,203] [5,45,210,484,485,486],([0,12,25,3,6,26],[109,307,479,487],[0,1]),([27,0,12,1,3,4],[0,5,13,16,475,488],[0,1]),([27,0,1,3,4,6],[0,5,28,31,45,53,489],[0]),e6 [199,132] [61,125,490],([27,0,1,3,29,4],[0,5,16,25,28,29,31,491],[0,1]),e6 [148,213] [126,177,187,270],([165,54,0,2,3,5],[13,14,63,116,117,482,492,493],[1]),([59,0,1,2,4,215],[5,494,495,496],[]),([159,117,1,2,3,4,6,5],[5,16,157,189],[]),a6 [109,32] [126,177,184,398] [0,1],a6 [96,8] [125,133] [0,1],a6 [8,10] [56,125,133,270,391,453,497,498] [0,1],u6 [134,20] [79,80,95,205,304],([93,28,0,25,3,26],([51,222,459,487]++r 499 4),[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_7 : checkNodesBT W_23 g_23 F_23 P_23_7 A_23 B_23_6 7 N_23_7 = true := by decide +kernel
def B_23_7 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_7
set_option maxRecDepth 500000 in
lemma B_23_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 7 xs.toFinset) B_23_7 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok (buildPoolsSubBT_sound S_23_ok) A_23_ok B_23_6_ok C_23_7
def U_23_8 : List Nat := ([1,5,11,13,16,19,29,45,51,56,61,70,77]++r 79 4++[84,95,109]++r 125 4++[132,133,137,138,140,144,147,150,152,153,157,159,176,177,178]++r 183 5++r 189 5++[195,196,198,199,205,207,209,210,214,216,217,219,221,222,223]++r 225 5++[231,233]++r 235 4++[240,242]++r 246 4++[252,253]++r 255 5++r 261 10++[276,277,282,283,285,288]++r 291 4++[296,302,303,304,306,307,312]++r 314 4++r 319 6++[326,328,329]++r 331 4++[337,342]++r 344 5++[351,352]++r 354 4++[359,360]++r 362 4++[367,370,372,378,379,380,383,385,386,390,392,393,396,397,400,403,406,407,411,412,415,416,424,426,427,430,433,434,435,439]++r 442 6++[449,451,453]++r 455 5++[461,462,463,465,467,468,471,475,479,481,484,485,489,490,494,495,499,500]++r 503 1019)
def P_23_8 : BT (Option BoundPool) := buildPoolsSubBT 11 W_23 r_23 S_23 ps_23 U_23_8
def N_23_8_0 : List NodeSpec := [([0,1,2,3,4,216,7],[5,210,285,503,504],[]),([218,0,1,2,3,4,7],[5,127,210],[]),([161,0,1,3,4,5,7],[5,16,127,184,199,505,506],[0]),([0,147,2,3,4,5,7],[5,127,507,508,509],[0]),([219,1,2,3,4,5,7],[5,16,79,223,267,453,510],[]),([0,1,2,3,124,5,146],[5,127,128,285,511],[0,1]),([0,1,2,220,4,5,7],[5,285,512],[]),([185,1,2,3,4,5,7],[5,127,267,317,320,324,513],[]),e6 [118,159] ([5,16,133,176,190,228,356,357,411]++r 514 4),([222,1,2,3,4,5,7],[5,16,79,127,191,223,267,518,519],[]),([223,0,1,2,3,4,7],[5,45,210,270,520,521,522],[]),e6 [224,143] ([13,45,61,125,247,256,257,403]++r 523 6),u6 [118,149] ([5,177,183,285,463,508,516]++r 529 8),([151,0,1,3,4,5,7],[13,45,144,178,184,270,537,538,539],[0]),([225,0,1,2,4,5,7],[5,453,540,541,542],[]),u6 [148,124] ([5,128,177,187,247,268,269,270,315,392,453]++r 543 6),a6 [148,156] ([5,132,184,185,214,229,268,269,270,315]++r 549 5) [0,1],([118,117,1,2,3,4,5,7],[5,16,127,157,159,189,193,195,198,223,227,516,541,554],[]),([118,117,1,2,3,4,5],[5,16,79,157,159,189,193,195,198,516,554],[0]),([117,1,2,3,124,4,5,7],[5,16,127,159,189,193,195,223,227,544,555],[]),([117,1,2,3,4,5,149],([5,157,159,193,328,530]++r 556 4),[0]),([126,1,2,3,4,5,7],[5,16,79,127,223,267,560],[]),([126,1,2,3,124,4,5],[5,16,127,137,138,140,543,561,562],[0]),([154,0,1,2,3,5,7],[5,127,177,453,563,564],[0]),([159,126,1,2,3,4,5],([5,16,45,84,137,138,140,147,207,225,356]++r 565 4),[]),([227,126,1,2,3,4,5],([5,138,140,147,225,556]++r 569 6),[]),([126,1,2,3,4,5,149],[5,45,137,138,507,529,541,575],[0,1]),e6 [228] [16,80,125,133,153,177,228,235,576],e6 [229,166] ([5,13,61,133,209,247,306,457]++r 577 6),e6 [230,166] [5,13,209,228,306,457,577,578,579,583,584],e6 [231,132] ([13,16,61,125,177,407,490]++r 585 9),a6 [232,166] ([5,13,133,177,209,306,457]++r 577 4++[582,594,595,596]) [1],([105,185,1,2,3,4,5],[5,80,319,320,321,323,465,597,598],[]),e6 [233] ([5,13,61,79,80,125,133]++r 599 5),e6 [235] ([126,177]++r 604 4),([105,78,120,0,2,3,4],[126,152,296,390,433,601,608,609,610],[1]),([185,1,2,3,4,5,83],[5,320,323,324,348,507,611],[]),([78,236,0,1,2,4,5],([5,228]++r 612 6),[]),u6 [200] [5,13,125,133,235,348,412,415,618],([0,41,2,3,4,44,83],[153,235,449,451,619,620,621],[1]),([0,1,2,76,4,44,5],[16,45,153,247,622,623],[]),([78,237,0,2,3,4,5],([125,126,152,601]++r 624 4),[]),([78,0,1,238,3,4,5],([126,152,601]++r 628 4),[]),([0,1,238,3,4,44,5],[153,236,622,630,631,632],[]),e6 [239] [5,80,126,177,481,633],([90,0,1,156,3,4,5,7],[5,183,184,185,191,453,455,552,559,634,635],[0]),u6 [90,148,7] [5,184,186,187,270,508,582,636,637],([90,126,1,2,3,4,5,7],[5,127,137,140,147,183,207,455,567,571,582,638,639,640],[]),a6 [160,7] [16,177,184,191,192,223,267,270,285,582,641] [0,1],e6 [160] ([16,125,126,133,192,228,270,582]++r 641 4),([105,90,120,0,2,3,4],([45,126,293,296,390,481,609,610]++r 645 7),[0]),e6 [90,240] ([5,45,126,133,247,640,645]++r 652 7),e6 [241] ([5,45,61,79,80,183,210,645]++r 659 4),e6 [236,90] ([5,45,133,177,228,247,617,636,640,646,658]++r 663 4),e6 [242] [45,125,126,210,481,606,645,667,668,669],e6 [243] [5,79,80,126,177,247,670,671,672],e6 [244] [5,79,80,126,177,228,673,674,675],e6 [105,163] ([45,126,133,247,656,662,664]++r 676 7),([0,1,2,3,150,5,7],[5,45,177,285,314,328,683,684,685],[0]),u6 [163,83] ([45,242,247,611,677,682]++r 686 4),e6 [246,245] ([16,45,125,177,247]++r 690 10),e6 [247,163] [5,45,133,177,247,664,676,677,678,680,688,700,701,702],e6 [248] [5,126,127,177,191,703],u6 [93,166] ([5,13,133,209,306,577,578]++r 704 5),([105,181,120,0,2,3,4],[5,293,390,433,649,709,710],[0,1]),e6 [249] [13,126,210,283,485,709,711,712,713],([93,28,0,2,3,5,7],[16,127,221,270,453,458,459,714],[1]),([105,181,90,0,1,3,5],[5,228,294,662,715,716,717],[0]),([93,28,0,25,2,3,5],[51,219,221,222,458,714,718,719],[0,1]),e6 [250] [5,80,126,133,210,383,720,721,722],([252,1,2,3,4,5,251],[5,80,541,723,724,725],[]),([78,0,41,2,3,4,83],[152,177,447,449,612,620,621,726],[1]),e6 [254] [5,80,125,126,727,728,729],e6 [255] [5,79,126,730,731],e6 [256] [5,348,732,733,734],a6 [8] [16,56,125,127,133,270,735,736] [0,1],u6 [159,6,7] [5,16,184,453,568,737,738],([93,59,28,0,2,3,5],[51,219,221,222,458,459,714,739,740],[1]),a6 [148,14,7] ([5,184,191,270,508]++r 741 4) [0,1],([214,59,0,1,2,4,5],[45,228,494,495,739,740,745],[0]),a6 [90,132] ([16,61,133,177,183,247,407,481,490]++r 585 4++[636,746,747]) [0,1],e6 [257] [5,79,80,126,177,748],u6 [227,124] [5,127,128,392,543,544,545,573,749,750,751],u6 [215] ([5,494]++r 752 4),e6 [258] [16,80,133,177,210,228,576,743,756,757,758],u6 [166,6] ([5,126,177,209,306,457,578,579,704]++r 759 6),e6 [259] [45,210,604,606,737,765],a6 [210] ([13,16,45,210,471,762]++r 766 4) [0,1],e6 [214,26] ([5,45,61,125,133,337,767]++r 770 6),e6 [188,44] ([5,177,210,228,235,247,605,606,619,622]++r 776 6),u6 [60,19,7] [5,45,184,264,267,283,285,352,782,783,784],([0,1,2,260,4,44,5],[5,247,605,622,785,786],[]),([105,173,0,2,3,4,5],[45,177,662,787,788,789],[]),([105,234,0,19,3,4,5],[5,125,126,662,790,791,792],[]),u6 [24,208] ([13,45,291,292,337,347,445]++r 793 5),e6 [261] ([5,80,125,126,210]++r 798 4),([37,0,2,3,4,14,5,83],([5,242,246,743]++r 802 5),[0]),u6 [178] ([13,45]++r 807 6),u6 [177] [5,79,80,228,247,807,813],([59,0,24,19,3,4,5],[11,77,81,82,133,259,261,277,333,814,815],[0]),e6 [105,115] ([84,126,328,337,359,363,364,715]++r 816 5),u6 [19,197] ([45,233,337,352,354,379,380]++r 821 5),e6 [262] [5,125,489,740,826],([185,24,1,2,3,4,5],[5,80,291,319,320,598,798],[0]),([0,24,1,2,3,142,121],[5,331,807,827,828,829],[0]),([182,0,1,2,3,4,116],[13,125,126,276,292,807,830,831],[0]),([0,1,2,240,4,5,7],[5,508,832],[]),([130,41,1,2,3,4,5],([80,125,434,435,467,485]++r 833 5),[0]),([0,1,2,3,4,116,121],[5,125,247,799,838],[0]),([217,126,1,2,3,4,5],[5,127,137,138,140,147,571,839,840],[]),u6 [184,173] [45,133,177,247,283,782,788,841,842,843],u6 [194,116] ([5,125,126,276,513,807,838]++r 844 5),([179,1,2,3,4,5,116],[5,13,79,838,845,849,850,851],[0]),([126,24,1,2,3,4,5],[5,80,147,225,291,571,798,852],[0]),e6 [264] [5,61,126,177,228,853,854],e6 [265] [5,79,80,125,126,383,813,855],e6 [266] ([5,45,80,778]++r 856 6),e6 [267] [16,80,125,133,228,372,862,863,864],u6 [24,61] [5,13,291,292,397,865,866,867],u6 [173,121] ([5,45,61,177,226,344,788,799,800]++r 868 4),u6 [44,116] [5,622,776,777,838,845,851],([105,100,120,0,2,3,4],[293,390,433,462,609,610,649,872,873],[1]),([268,0,24,19,3,4,5],([77,82,252,277]++r 874 4),[]),([78,0,24,19,3,4,5],[5,13,77,81,82,125,252,259,261,625,629,878,879],[]),([189,0,24,19,3,4,5],([77,81,82,252,261,333]++r 880 4),[0]),e6 [269] ([5,61,79,80,125,133,228]++r 884 4),u6 [24,197] [13,45,80,291,292,337,379,798,822,824,888,889],([0,24,19,3,4,5,121],[5,226,252,800,890,891],[0]),e6 [270] [5,80,125,126,892,893],e6 [273] ([5,125,228]++r 894 5),([0,19,3,4,5,116],[5,13,81,125,277,288,302,899],[0]),([105,130,1,2,3,4,5],[5,80,125,434,435,465,597,790,835,836,900],[0]),e6 [114,240] ([45,126,228,328,443,652,818]++r 901 4),([193,185,1,2,3,4,5],[16,319,320,321,326,345,598,905,906,907],[]),e6 [274] [5,13,79,80,126,228,247,508],u6 [159,60,7] [5,45,184,356,357,908,909,910],([105,78,0,2,19,3,4,5],([5,126,354,601,612,625,787]++r 911 4),[]),e6 [19,216] ([5,45,177,247,282,352]++r 915 6),u6 [188,114] [45,80,228,328,359,606,778,780,781,904,921,922,923],e6 [275] [45,125,133,342,808,924,925],e6 [276] [5,13,45,79,80,126,210,228,247,926,927],a6 [90,76] ([16,45,126,247,468,481,623,645]++r 928 4) [1],e6 [277] ([5,61,79,80,125,126,210]++r 932 5),e6 [78,278] ([5,126,133,247,337,346,601]++r 937 6),u6 [188,60] [45,80,283,355,606,778,780,781,909,922,943,944],e6 [279] [5,80,126,177,945,946,947],([182,0,24,19,3,4,5],([77,81,82,133,261,277,333,334]++r 948 5),[0]),u6 [193,60,7] ([5,45,263,264,267,283,455,908]++r 953 4),e6 [280] [5,13,45,61,79,80,126,228,247,957,958],e6 [281] ([16,125,133,430]++r 959 4),([130,1,2,3,4,5,83],[5,348,439,559,611,732],[0]),([126,1,2,3,4,5,83],[5,137,147,348,507,567,611],[]),a6 [175,7] [45,184,191,266,267,270,360,453,508,963,964] [0,1],([60,0,24,19,3,4,5],[5,13,77,81,82,261,264,265,277,881,909,965],[0]),a6 [8,7] [16,127,184,191,223,267,735,736] [0,1],e6 [282] [5,16,133,372,966,967,968],([37,60,0,2,3,4,5,83],([283,342,805,806,944,953]++r 969 4),[]),e6 [114,193,7] ([45,267,345,442,443,455,908,955]++r 973 4),e6 [61,83] [13,126,283,337,611,971,977,978],e6 [19,283] ([5,177,233]++r 979 4),e6 [44,278] ([5,133,236,606,622,776,777]++r 937 5),e6 [284] ([16,61,79,80,125,133,210,934]++r 983 5),u6 [179,116] [5,79,125,126,276,838,845,846,847,849,851],e6 [285] ([5,125,556,897]++r 988 6),e6 [236,60] [5,45,80,264,283,355,614,665,666,909,971,994,995],e6 [114,173] [45,80,228,316,328,788,842,996,997,998],u6 [180] [5,13,61,80,125,126,605,622,798,999],e6 [114,286] ([5,45,126,228,328,342,443,904,975]++r 1000 6),e6 [287] ([5,13,79,80,228,247]++r 1006 6),([217,118,0,1,2,3,5],[5,127,285,453,517,1012,1013],[0]),e6 [288] ([13,80,125,126,210,283,352]++r 1014 4),e6 [289] ([5,45,79,80,125,126,228,247]++r 1018 4),([290,1,2,3,4,5,7],[5,16,79,127,223,267,1022],[]),([105,120,0,2,3,4,44],[153,293,296,390,610,619,622],[1]),e6 [291] [16,79,80,177,210,228,461,1023,1024,1025],e6 [173,292] ([45,177,247,344,541]++r 1026 5),([0,1,2,272,4,5,7],[16,61,80,127,267,508,1031],[]),([184,0,1,2,19,3,44,5],[5,283,782,920,1032,1033,1034],[]),([0,24,19,3,4,44,5],[5,81,236,252,261,605,1035],[0]),e6 [294] ([5,61,79,80,210,348,611,732]++r 1036 4),([0,1,2,3,195,142,121],[331,332,430,828,962,1040,1041,1042],[]),e6 [90,286] ([5,45,126,133,247,640,645,658,1002,1003,1005]++r 1043 5),([59,0,1,2,3,4,295],([5,126,247,475,813]++r 1048 4),[]),e6 [297] [5,79,80,126,177,247,1052,1053,1054],e6 [298] ([5,16,61,125,210]++r 1055 5),e6 [193,197] [45,337,345,346,378,379,380,822,824,907,1060,1061],e6 [105,299] [45,126,133,337,662,715,1062,1063,1064],([105,114,0,2,3,195,4,5],([359,430,818,923,975]++r 1065 5),[]),u6 [19,61] [5,45,84,177,233,247,337,352,354,355,397,455,784,866,978,1070,1071,1072],e6 [60,286] ([5,45,126,264,283,342,909,953]++r 1000 4++[1005,1073,1074]),e6 [105,61] ([84,126,283,337,355,397,866]++r 1075 4),e6 [300] [125,133,210,283,953,1079,1080,1081],u6 [114,24,7] [13,267,291,904,973,975,1082,1083,1084],([184,0,24,19,3,4,5],[5,77,82,133,252,259,334,935,986,1085],[0]),u6 [19,115] [5,84,177,328,337,354,359,363,393,455,817,819,998,1033,1086,1087],([173,59,0,1,2,4,5],[45,133,177,248,249,740,782,815,1088,1089],[0]),e6 [301] ([45,80,125,126,210,233,352,606]++r 1090 5),e6 [223,114] ([45,80,228,328,443,904,923]++r 1095 6),([0,24,19,3,142,4,5],[258,259,277,333,809,1101,1102],[0]),e6 [188,194] [5,80,513,780,781,791,922,943,1103]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_8_0 : checkNodesBT W_23 g_23 F_23 P_23_8 A_23 B_23_7 8 N_23_8_0 = true := by decide +kernel
def N_23_8_1 : List NodeSpec := [e6 [302] [5,79,126,127,177,1104,1105],e6 [304] ([5,125,126]++r 1106 4),([196,1,2,3,4,5,116],[5,13,80,328,807,851,1110],[0]),e6 [305] ([5,61,133,183,235,605]++r 1111 4),e6 [306] ([5,61,80,372,864]++r 1115 4),e6 [307] [45,126,228,247,462,485,873,1119],([0,24,19,3,4,5,7],[1,5,77,81,82,184,191,259,261,262,277,333],[0]),([0,1,2,3,4,295,7],[5,247,508,1050,1120,1121],[]),([105,120,0,2,3,4,14],[45,293,296,756,802,804,1122],[0,1]),e6 [308] [45,125,133,210,228,312,1080,1123,1124,1125],([194,0,24,19,3,4,5],[5,81,82,252,261,333,881,1126,1127,1128],[0]),([165,0,12,2,3,6,5],([109,228,307,720]++r 1129 8),[0,1]),e6 [309] [13,125,133,210,264,283,345,1137,1138,1139],([117,1,2,3,4,6,5,7],[16,127,189,195,223,231,759,1140,1141],[0]),e6 [311] [5,45,79,80,126,210,228,247,1142],u6 [190] [13,45,126,210,291,292,880,1125,1143,1144],e6 [312] [16,80,125,133,228,372,864,1145,1146],([105,126,1,2,3,4,5],[5,140,147,225,465,567,570,571,597,638,1147],[]),u6 [114,159,7] [5,45,191,267,356,357,443,904,908,973,1148,1149],u6 [126,19,7] [5,45,140,184,267,282,352,783,1150],e6 [19,263] [5,177,283,352,1033,1151,1152,1153],([130,120,1,2,3,4,5],([435,439,835,836]++r 1154 5),[0]),([105,60,0,2,3,195,4,5],([16,355,944,953]++r 1065 4++[1078,1159,1160,1161]),[]),([130,1,2,3,4,5,7],[5,127,267,434,439,559,835],[]),e6 [223,60] ([45,80,264,283,355,909,944,1095]++r 1097 4++[1162]),e6 [313] ([16,61,372,743]++r 1163 4),e6 [314] [5,13,61,80,125,210,312,1167,1168],([105,120,0,13,2,3,4],[5,293,296,390,427,433,484,1169],[0,1]),e6 [315] [13,61,79,125,210,283,611,1170,1171],e6 [114,260] ([5,13,45,125,126,328,921,1009,1084]++r 1172 4),([93,165,28,0,2,3,5],([51,222,458,459,714,1135]++r 1176 4),[0,1]),e6 [19,316] [5,177,233,981,1180,1181,1182],e6 [317] [13,45,61,84,125,133,210,283,597,953,1183,1184,1185],([105,0,2,19,3,4,44,5],[5,235,605,622,681,790,912,914,1186],[]),e6 [193,115] [5,45,337,345,346,359,362,363,364,455,819,974,1187,1188,1189],e6 [240,14] [5,45,125,133,652,653,654,802,1064,1190,1191],e6 [318] [5,16,61,79,80,125,133,210,925,934,1192,1193,1194],e6 [319] [5,126,177,210,896,1195,1196],e6 [321] ([5,125]++r 1197 4),e6 [115,83] ([45,337,455,611,820,1087]++r 1201 4),a6 [112,7] [45,61,127,184,191,210,223,267,270,453,508,1205,1206,1207] [0,1],e6 [322] [13,45,80,125,126,210,791,1208,1209,1210],u6 [24,143] [13,256,291,292,524,525,1211,1212,1213],([105,90,0,2,3,195,4,5],[5,126,636,645,655,664,1066,1067,1068,1159,1214,1215,1216],[]),u6 [114,19,7] [45,184,267,352,393,443,453,783,973,998],([117,1,2,19,3,4,5,7],[5,157,159,193,227,352,393,783,1217],[0]),e6 [323] [5,126,177,210,228,1218,1219],u6 [24,115] [5,13,292,328,363,817,819,1082,1084,1220],u6 [60,148,7] [45,267,268,269,283,944,1221,1222],([114,0,24,19,3,4,5],[5,77,81,82,261,277,333,365,443,881,904,1223],[0]),e6 [324] [5,80,84,1224,1225,1226],e6 [326] ([5,79,80,125,126,247]++r 1227 4),u6 [60,24,7] [5,13,267,283,291,786,867,909,953,1083],([0,1,2,197,195,4,5],[45,126,372,380,822,823,864,1231],[]),([37,185,1,2,3,4,5],[5,80,312,317,319,320,321,323,598,1080],[]),([0,1,2,61,4,5,7],[45,61,267,283,351],[0,1]),e6 [327] [5,45,61,79,80,126,228,247,1232],e6 [188,78] [5,177,247,337,608,612,625,780,781,942,1233,1234],u6 [45] ([5,61,233]++r 235 4++[240]),e6 [328] ([13,45,808,1102]++r 1235 5),e6 [218,19] [5,125,126,133,177,233,282,283,352,354,782,1240,1241],e6 [329] ([5,13,61,79,80,125,133,210,601,629]++r 1242 4),([165,0,1,2,3,4,295],[5,126,475,720,1048,1049,1246,1247,1248],[]),e6 [223,90] [5,45,133,177,228,247,636,640,646,658,664,1098,1099,1249],([37,0,1,13,3,14,5],[5,125,312,385,386,1168,1250,1251],[0]),([37,330,0,1,2,4,5],([5,13,16,45,133,177]++r 1252 4),[]),e6 [331] ([5,133,210,228,475,720]++r 1256 4),([78,0,1,2,19,3,5,121],[5,247,354,367,871,920,1033,1260,1261],[0]),a6 [90,158,7] [5,16,184,270,455,645,1262,1263] [0,1],a6 [76,14] [16,45,125,133,468,623,802,804,928,931,1190,1264,1265,1266] [1],([126,1,2,19,3,4,5],[5,16,137,140,147,233,352,567,571,1150],[0]),([126,1,2,19,3,4,5,7],[5,45,137,138,140,147,207,225,233,282,783,1150],[0]),a6 [101] ([5,16,61,177,228,461,462]++r 1267 5) [0,1],u6 [187] [13,45,80,125,126,210,807,948,1272,1273],e6 [332] [16,125,210,228,604,1056,1274,1275],u6 [20] [5,16,70,80,95,125,126,184,205,228,247,270,303,304,1276,1277,1278],e6 [19,220] ([5,45,125,133,177,247,282,352,920]++r 1279 5),u6 [20,7] [5,95,205,223,267,270,285,303,304,453],([90,117,1,2,3,4,5,7],[5,157,159,186,189,193,195,196,198,223,227,481,559,658,1284,1285],[0,1]),u6 [19,124,7] [5,184,270,285,392,393,453,508,1033,1286],e6 [333] [5,13,45,125,126,210,283,291,909,953,1287,1288],([37,130,1,2,3,4,5],[5,80,125,312,434,435,835,836,1080,1168],[]),e6 [334] [5,228,247,740,791,815,1289,1290,1291],u6 [19,143] [45,247,256,257,352,354,403,406,523,524,525,920,1292,1293,1294],e6 [335] [5,16,61,372,734,1117,1295,1296],([0,1,2,19,3,142,121],[45,331,332,791,828,1033,1040,1041,1297],[0]),([27,0,1,3,4],[29,896],[0,1]),u6 [122] [5,16,45,226,233,253,370,967,1298],e6 [225,19] [5,45,125,126,133,177,233,282,352,354,542,782,1299,1300],([126,1,2,3,124,4,5,7],[5,16,127,137,138,140,147,223,267,544,561,562,571],[]),e6 [336] [5,80,125,133,210,228,247,342,720,1301,1302,1303],([185,1,2,19,3,4,5],[5,16,233,319,320,321,323,324,352,1304],[0]),e6 [337] ([5,13,16,125,126,283,986]++r 1305 5),e6 [338] [45,210,228,606,791,949,960,1033,1310,1311,1312],e6 [339] [45,125,126,133,152,210,601,669],e6 [341] ([5,61,79,80,126,210,228]++r 1313 5),u6 [19,208] ([45,133,177,282,337,352,354,445,446,794,795,1033]++r 1318 4),e6 [342] ([13,16,45,125,126,210,228,767,1316]++r 1322 4),([0,1,3,343,4,5,26],([5,13,45]++r 1326 4),[]),([0,41,2,3,340,4,83],([449,620,621,726]++r 1330 4),[1]),e6 [344] [5,80,126,177,228,247,757,1331,1332,1334,1335],e6 [236,14] [5,45,125,133,613,665,743,804,1190,1191,1336,1337],([0,12,2,3,340,6,5],[16,307,426,1133,1134,1338,1339],[1]),e6 [345] ([45,79,80,228,247]++r 1340 6),e6 [223,14] [5,45,125,133,177,743,804,1098,1099,1190,1191,1346,1347],([0,153,2,3,4,5,7],[13,45,150,184,507,508,582,1348,1349,1350],[0,1]),e6 [114,236] [5,45,80,228,328,443,665,666,904,994,995,1203],([193,0,2,3,4,44,5,83],([5,235,416,619,622]++r 1351 4),[0]),e6 [346] [5,80,125,133,228,247,813,815,1235,1355,1356],([117,1,2,3,4,5,146],[5,157,159,507,559,839,1357],[0,1]),e6 [173,347] ([45,177,247,322,841]++r 1358 5),e6 [348] [5,126,177,1363,1364,1365],a6 [193,143] [45,247,255,256,257,346,406,455,523,524,525,1239,1294,1366,1367] [1],([114,37,0,2,3,4,5,83],[342,805,806,923,969,972,975,1203,1368,1369],[]),([193,0,1,2,3,142,121],([16,329,331,332,828,1235]++r 1370 5),[]),([37,0,1,2,3,142,121],[228,331,332,342,827,828,1041,1375,1376],[]),([0,1,2,325,4,5,7],[16,61,126,285,1377,1378,1379],[]),e6 [349] [5,133,210,800,967,1111,1380,1381,1382],([0,1,2,3,4,286,7],[5,45,210,508],[]),e6 [350] [16,80,126,210,604,792,1383,1384],e6 [351] [16,80,125,133,210,228,430,1385,1386,1387],e6 [352] [45,80,125,133,210,228,606,949,1189,1235,1272,1388,1389],e6 [193,208] [45,337,345,346,444,445,446,456,794,795,1189,1318,1390],([105,0,2,3,195,4,14,5],[5,662,681,743,802,1066,1214,1336],[]),([0,148,2,3,4,5,149],[5,45,315,508,1391],[0,1]),e6 [353] ([5,79,80,125,133,177]++r 1392 4),([126,148,1,2,3,4,5],[5,45,138,140,147,225,269,570,571,582,638],[]),([0,1,2,325,340,4,5],([16,125,247,1339,1379]++r 1396 5),[]),e6 [354] ([16,61,79,80,125,133,887,1117]++r 1401 4),([90,0,41,2,3,4,83],([45,177,449,481,620,621,636,726,1333]++r 1405 5),[0,1]),([93,28,0,2,3,340,5],[16,221,222,459,714,1332,1338,1410],[1]),e6 [355] [45,125,133,210,228,345,606,882,907,1125,1411,1412,1413],e6 [356] [16,80,125,228,247,430,1117,1414],([227,158,0,2,3,4,5],[5,45,270,508,1415,1416,1417],[1]),([236,0,1,2,4,5,7],[5,270,617,1418,1419,1420],[]),([185,1,2,3,195,4,5],[5,317,320,321,323,324,372,864,1421],[]),([0,12,2,3,6,5,7],[16,127,307,426,508,1131,1134],[0,1]),([159,117,1,2,3,4,5],[5,16,79,157,159,189,193,198,227,357,1422],[0,1]),u6 [118,19,7] [5,176,184,233,285,453,920,1423],e6 [357] ([13,16,61,80]++r 1424 6),e6 [358] ([13,16,80,228,606,1117]++r 1430 4),([59,130,1,2,3,4,5],[80,434,435,439,814,835,836,855,1434],[]),u6 [93,169] ([5,13,45,216,424,706,708,1383]++r 1435 4),([105,120,0,2,3,340,4],[293,296,390,609,610,1330,1331,1339],[1]),([0,1,2,195,4,143,5],[45,126,257,403,430,525,1387],[]),u6 [144,143] [13,45,177,247,256,257,403,406,524,525,1211,1439,1440,1441],u6 [114,148,7] [5,45,267,268,269,508,923,973,1442,1443],u6 [193,61] [5,283,337,346,396,397,455,866,907,956,1077,1444],e6 [359] [5,16,133,1309,1387,1445,1446,1447],e6 [6,360] [16,45,125,737,759,760,1448,1449,1450],([37,90,0,2,3,4,5,83],[5,126,242,246,636,645,646,805,806,972,1046,1451,1452],[]),e6 [361] ([5,13,61,125,126,612,629]++r 1453 5),e6 [362] [5,61,177,183,737,1058,1458,1459],e6 [363] [5,80,126,152,177,1460],([93,100,28,0,2,3,5],[16,219,221,222,228,714,1058,1459,1461],[1]),([93,28,0,2,3,5,26],[16,458,459,471,767,774],[0,1]),a6 [12,166] [5,13,45,133,177,306,457,475,577,578,579,704] [0,1],e6 [173,60] [45,80,283,316,322,784,788,842,996,997],e6 [364] ([5,61,79,80,125,183,210,645]++r 1462 4),e6 [365] ([5,13,61,125,133,612]++r 1466 4),([37,0,1,25,3,4,26],[133,342,479,499,1303,1470,1471,1472],[0]),e6 [366] ([5,13,80,228,455,732]++r 1473 4),e6 [367] [16,79,80,228,247,606,1168],e6 [368] [5,126,177,800,1058,1477],([37,225,0,1,2,4,5],[5,177,312,542,1375,1478,1479],[]),u6 [114,116] ([5,13,45,125,126,328,359,807]++r 844 4++[851]),e6 [369] [45,80,125,133,210,228,342,1272,1375,1480],([0,1,2,3,4,295,26],[5,125,247,1049,1481,1482,1483],[]),([130,1,2,3,195,4,5],[5,372,434,435,439,835,864,1117,1484],[]),e6 [370] [5,79,80,125,126,247,1485,1486,1487],([93,0,1,25,3,4,26],[16,479,499,708,1470,1488],[0]),([15,0,1,3,5],[19,541],[0,1]),([0,12,25,2,3,6,5],[109,426,1134,1489,1490],[0,1]),e6 [371] [80,125,126,153,177,228,283,605,1491],([0,12,2,3,6,5,26],[16,307,471,1131,1483],[0,1]),e6 [372] ([5,80,125,133,210,228,1316]++r 1492 5),u6 [174] ([45,228,247]++r 1497 8),([193,126,1,2,3,4,5],[5,140,147,207,225,345,400,567,571,907,1505,1506],[]),([105,0,1,13,3,14,5],[5,125,385,386,465,790,1250,1251,1507],[0]),e6 [373] [5,79,80,126,133,177,228,285,1508,1509],([59,0,12,2,3,6,5],[109,228,307,426,739,813,1131,1133,1134,1510],[1]),e6 [60,240] [45,126,264,283,652,901,902,903,909,1078,1511],a6 [203] [45,126,133,210,427,485,669,1169,1512,1513,1514] [0,1],a6 [112] [79,125,126,133,177,267,283,1205,1207] [0,1],a6 [12,169] [5,45,216,217,247,424,461,475,1435,1436,1515] [0,1],([237,0,2,3,4,44,5],[126,153,605,622,626,627],[]),e6 [374] [5,13,61,79,80,125,126,210,601,625,1516,1517,1518],([0,12,1,25,3,4,26],[16,475,479,499,500,1258,1470],[0,1]),([0,41,2,3,4,14,83],[45,451,621,743,756,804,1519],[1]),e6 [375] [5,125,228,475,813,1520],e6 [376] [45,80,125,210,283,489,719,737,1521]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_8_1 : checkNodesBT W_23 g_23 F_23 P_23_8 A_23 B_23_7 8 N_23_8_1 = true := by decide +kernel
def N_23_8 := N_23_8_0 ++ N_23_8_1
def B_23_8 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_8
set_option maxRecDepth 500000 in
lemma B_23_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 8 xs.toFinset) B_23_8 := by
  have hP := buildPoolsSubBT_sound (pdepth := 11) (W := W_23) (raw := r_23) (pspecs := ps_23) (used := U_23_8) S_23_ok
  have hm0 := checkNodesBT_mem (by decide) gp_23 W_23_ok hP A_23_ok B_23_7_ok C_23_8_0
  have hm1 := checkNodesBT_mem (by decide) gp_23 W_23_ok hP A_23_ok B_23_7_ok C_23_8_1
  exact buildBucketsBT_of_mem (forall_append (hm0) hm1)
def U_23_9 : List Nat := ([1,5,11,13,16,35,41,45,61,77,79,80,84,125,126,127,133,152,153,177,183,184,191,196,198,206,210,223,226,228,233,235,236,242,247,261,264,267,268,270,282,283,285,291,292,312,317,323,328,337,342]++r 345 4++[352,354,355,357,358,359,372,383,406,427,430,443,453,455,456,461,462,465,471,475,481,484,485,489,490,507,508,513,530,541,544,557,559,567,576,579,582,597,601,605,606,608,610,611,612,619,620,622,625,627,629,631,633,636,638,640,645,646,652,653,655,658,662,664,665,669,677,679,686]++r 704 6++[712,714,715]++r 718 4++[732,737,739,740,743,745,747,756,757,759,760,762,763,764,767,770,771,772,774,776,777]++r 781 4++[786,787,788,790,791,792]++r 796 5++[802]++r 804 6++r 812 4++[818,820,824,829,833,835,844,848,851,864]++r 867 4++[872,874,876,877,879,880,882,883,888,890,896,904,907,908,909,913,916]++r 920 4++[925,930,934,935,938,939,941,942,944,948,949]++r 952 5++[960,962,965,967,975,976,986,996,998,1002,1005,1033,1035,1041,1042,1044,1046,1048,1050,1056,1058,1066,1068,1071,1080,1083,1084,1085,1094,1099,1101,1102,1103,1117]++r 1125 4++[1134,1135,1148,1157,1159,1161,1164,1168,1175,1176,1189,1190,1191,1203,1204,1221,1223,1234,1235,1239,1258,1265,1271,1272,1280,1284,1293,1297,1303,1309,1319,1330,1331,1332,1336,1338,1339,1352,1354,1367,1374,1375,1376,1383,1386,1387,1390,1400,1410,1419,1434,1437,1459,1460,1461,1483,1490,1515]++r 1522 200)
def P_23_9 : BT (Option BoundPool) := buildPoolsSubBT 11 W_23 r_23 S_23 ps_23 U_23_9
def N_23_9 : List NodeSpec := [a6 [208] [45,125,126,133,177,228,337,896,1319] [0,1],a6 [124,7] [5,13,16,127,184,270,285,328,544,1522,1523] [0,1],u6 [7,121] [5,127,210,247,270,508,541,799,896,967],a6 [148,7] [5,16,84,177,184,223,267,268,285,453,507,508,582,1221,1524,1525] [0,1],u6 [226,7] [5,16,127,191,267,453,508,513,896,908,1526],([126,1,2,3,4,5],[80,541,567,638],[0,1]),([78,0,1,2,3,5,121],[5,16,61,210,247,541],[0]),u6 [216] [5,16,125,126,133,177,247,916,1527,1528],([126,1,2,3,4,5,7],[5,16,45,79,127,223,267,567,638],[0,1]),a6 [166] [5,126,133,177,228,247,579,704,896] [0,1],u6 [105,7] [5,177,184,191,267,270,285,453,508,655,715,896,1529],u6 [105,234] ([5,125,133,177,597,715,790,792,896]++r 1529 6),([105,120,0,2,3,4],[61,126,610,896],[0,1]),u6 [240] [5,45,80,125,126,133,177,228,247,652,653,655],u6 [220] [5,16,125,126,133,177,247,1280,1535,1536],u6 [184,7] [5,184,191,228,267,270,285,453,508,541,896,934,1309,1536],u6 [44,83] [5,235,236,242,348,605,619,622,732,777,1419],e6 [105,26] [5,125,133,177,662,715,770,774,790,896,1483,1529,1537,1538],e6 [83,26] [5,125,126,242,767,774,896,1204,1537,1539,1540,1541],a6 [78,41] [152,228,485,601,625,629,669,833,930,1542] [0,1],u6 [217,7] [5,16,127,184,191,223,267,270,285,328,508,1543,1544],a6 [41,44] [153,177,228,236,247,485,605,619,622,712,776,777,930,1542] [0,1],([0,41,2,3,4,83],[61,177,620,896],[0,1]),a6 [76] [16,45,125,126,133,228,247,896,930] [0,1],([237,0,2,3,4,5],[125,126,627,896],[0]),([0,1,238,3,4,5],[126,133,631,896],[0]),a6 [59,90] [61,228,247,481,633,636,640,645,646,658,664,740,813,814,815,1545,1546] [0,1],u6 [105,90] [5,61,126,228,247,465,636,640,645,646,655,658,662,664,790,1529,1534,1538,1547],a6 [90,83] [5,61,125,126,177,242,348,636,640,645,646,664,686,732,1419,1540,1541,1548,1549,1550] [0,1],a6 [90,41] ([45,125,228,247,481,485,645,664,669,712,930,1542]++r 1551 5) [0,1],a6 [143] [45,125,126,133,177,247,406,896] [0,1],a6 [163] [45,61,126,133,177,247,664,677,679,1556] [0,1],u6 [93,59] [61,383,706,707,708,721,739,813,814,815,1383,1434,1545,1557],a6 [93,165] ([13,61,125,133,383,705,707,708,720,1135]++r 1557 5) [0,1],a6 [105,181] [5,177,228,597,709,715,790,1534,1562,1563] [0,1],a6 [93,26] [16,125,133,247,471,707,708,770,771,774,1383,1483] [0,1],a6 [173] [45,61,79,80,125,126,133,177,210,228,247,782,788,996] [0,1],u6 [278] [5,80,126,133,228,247,346,455,606,938,939,941,1564],([0,1,2,3,142,121],[35,228,896,1041],[0,1]),u6 [182,24] [45,291,292,347,786,796,797,807,829,948,1272,1565,1566,1567],u6 [188] [5,61,79,80,125,126,133,177,210,228,247,606,781,922,1234],u6 [24,121] [5,61,133,177,798,799,800,868],u6 [105,78] [5,61,126,597,601,608,612,625,629,655,662,790,942,1529,1534,1568,1569,1570],u6 [24,142] [13,786,807,808,809,1571],u6 [59,24] [291,292,347,633,739,786,797,807,812,813,814,1434,1545],u6 [105,184] [5,61,126,177,228,247,597,896,934,935,986,1309,1534,1572,1573],u6 [184,83] [5,126,177,228,242,611,732,896,1541,1574],u6 [24,7] [5,133,177,191,223,267,285,291,292,347,453,508,786,797,807,812,1083],a6 [93,7] [5,16,61,127,184,191,223,247,267,453,508,707,721,1383,1557] [0,1],u6 [24,44] [5,292,605,619,622,776,786,798],u6 [116] [5,13,79,80,125,126,228,247,292,807,844,851],a6 [225] [5,16,80,125,126,133,177,210,247,541,870] [0,1],u6 [253] [13,16,45,61,125,126,133,541,1557],u6 [260] [5,13,45,61,79,80,125,126,228,247,786,1175],a6 [78,19] [125,126,133,177,210,228,233,247,282,352,354,601,608,612,625,629,782,920,1575] [0,1],u6 [78,24] [5,13,125,291,292,347,601,625,786,798,812,1576],u6 [182,193] [45,61,125,133,177,345,346,456,949,952,954,1189,1235,1272,1319,1374,1390,1565,1577,1578],([184,0,1,2,3,44,5],[5,16,61,210,247,541],[0]),a6 [195,26] ([5,13,133,430,767,772,1117,1159,1483,1539]++r 1579 5) [0,1],u6 [223] [5,45,61,79,80,125,133,177,228,247,1099,1584,1585],a6 [159,7] [5,13,16,61,84,125,184,191,223,270,285,357,453,508,908,1148,1586,1587,1588] [0,1],e6 [268,193] ([16,206,345,456,874,876,877,896,907,1235]++r 1589 5),e6 [268,37] ([80,312,342,876,877,896,1080]++r 1592 4),u6 [37,189] ([79,80,312,824,880,882,1046,1080,1125,1168]++r 1595 4),([185,1,2,3,4,5],[80,317,323,541],[0,1]),a6 [105,13] [5,125,177,247,427,465,484,662,790,1534,1599,1600,1601] [0,1],u6 [189,195] [126,372,824,864,880,882,962,1094,1117,1159,1582,1583,1602],u6 [193,189] [45,79,206,345,346,456,824,882,883,907,954,1125,1590,1596,1603,1604,1605],u6 [263] [5,16,80,125,126,133,177,210,228,328,1606],u6 [184,24] [5,291,347,798,812,829,934,935,1572],e6 [83,121] [5,126,247,348,799,896,967,1607],a6 [41,14] [45,125,133,177,228,712,756,802,804,1190,1191,1265,1336,1542] [0,1],e6 [105,121] [5,177,226,228,247,799,800,868,896],a6 [114,7] [5,45,191,223,267,328,359,443,453,508,896,904,908,923,975,1526] [0,1],u6 [184,19] [5,16,61,125,126,133,177,233,282,352,782,920,934,935,986,1297,1309,1608],a6 [90,7] [5,61,125,127,184,191,223,270,285,508,541,636,640,645,646,664,908,1284,1609] [0,1],u6 [194,19] ([84,125,126,233,282,352,354,455,513,782,848,1033,1126,1127]++r 1610 4),([105,0,2,3,195,4,5],[5,126,177,210,655,662,1066,1068,1159],[0]),u6 [195,142] [126,228,406,430,808,809,1102,1117,1164,1386,1387],u6 [194,24] [5,80,126,291,292,347,513,786,797,798,848,1126,1613,1614],u6 [251] [5,79,125,126,133,541,1615],u6 [114,24] [5,126,228,291,292,328,347,359,786,797,807,904,921,975,1084,1614],u6 [60,19] [84,125,126,228,233,247,264,282,352,354,355,455,782,784,791,909,944,953,1033,1161,1610,1611],a6 [105,340] [5,13,84,125,133,655,662,1330,1332,1339,1400,1410,1534,1538,1616,1617,1618] [0,1],a6 [118,7] [5,16,61,127,183,184,191,223,247,267,270,285,453,508,582,1619,1620] [0,1],u6 [296] ([16,126,133,177,247]++r 1621 4),u6 [114,193] [16,125,206,328,345,346,443,455,456,954,975,976,1189,1223,1235,1590,1625,1626],e6 [268,195] [372,430,864,876,877,1583,1592,1594,1602,1627],e6 [194,83] [126,348,455,513,611,732,896,1204,1419,1540,1612,1628],a6 [193,7] [1,5,16,61,125,184,223,285,345,453,456,508,908,954,955,1189,1239,1629] [0,1],u6 [193,60] [16,206,264,345,346,455,456,907,953,954,956,965,1189,1235,1590,1630,1631],([130,1,2,3,4,5],[80,125,541,835],[0]),u6 [126,7] [5,16,45,84,127,191,223,267,453,455,508,582,638,908,1526],u6 [295] [5,125,126,133,247,1050,1632,1633],u6 [268,24] [5,291,347,798,807,876,896,1592,1593],([117,1,2,3,4,5,7],[5,16,80,196,198,223,328,507,559],[0,1]),u6 [60,83] [13,126,355,611,686,732,896,944,1419,1540,1628],u6 [114,37] [16,80,84,228,328,342,359,443,904,921,975,1046,1080,1168,1375,1595,1598],([105,0,2,19,3,4,5],[5,61,84,125,126,177,354,662,787,913],[0]),u6 [114,19] [84,125,126,228,282,328,352,354,359,443,455,782,791,904,921,923,975,998,1033,1610,1611],a6 [37,293] ([5,16,80,312,1046,1080,1168,1595]++r 1634 4) [1],e6 [194,193] [16,125,206,345,346,455,513,848,907,954,1127,1128,1189,1590,1638,1639],a6 [115] [125,126,133,177,328,358,359,820] [0,1],u6 [325] [16,45,61,125,126,133,247,1640,1641,1642],a6 [271,340] ([5,16,125,126,1330,1338,1339,1410,1616,1617]++r 1643 5) [1],a6 [197] [45,61,80,125,126,133,177,337,541,824,888] [0,1],u6 [19,142] [45,125,126,228,247,406,782,791,808,809,920,1033,1102,1293,1386],u6 [184,37] [5,61,126,925,934,935,986,1046,1080,1168,1303,1375,1376,1536,1572,1573,1595,1648,1649],u6 [303] [5,80,125,126,133,541,1650,1651],u6 [105,114] [80,84,228,328,359,443,597,655,715,790,818,896,904,975,1538],a6 [193,44] [16,177,236,346,605,619,622,777,907,954,1035,1652,1653,1654] [0,1],u6 [189,24] [45,126,291,292,347,786,797,798,824,880,1125,1614],u6 [268,19] [45,233,282,352,791,876,877,1592,1594,1610,1627],u6 [59,6] [126,177,228,489,737,739,740,745,759,760,762,763,813,814,815],u6 [182,19] [45,125,126,133,177,247,282,352,354,782,791,948,949,960,1033,1272,1297,1319],u6 [189,19] [45,125,126,233,282,352,354,782,824,880,882,1033,1094,1125,1610,1611],a6 [271,7] [5,16,127,191,267,453,896,908,1056,1526,1645,1646] [0,1],a6 [7,149] [5,13,45,223,270,285,453,508,530,557,1526,1655] [0,1],a6 [37,165] [61,125,133,177,342,579,720,925,1046,1135,1303,1375,1460,1558,1559,1595,1598] [0,1],u6 [114,83] [126,328,455,611,686,732,896,923,1203,1204,1419,1540,1628],a6 [227,7] [5,45,177,184,191,223,267,285,453,507,508,582,1656] [0,1],u6 [218] [5,16,80,125,126,133,177,210,541,1657],u6 [272] [16,45,61,125,126,133,541,1645,1658],a6 [7,146] [5,16,127,223,247,1659] [0,1],a6 [195,14] [16,126,177,372,743,802,804,1117,1159,1164,1336] [0,1],a6 [105,100] [5,84,125,177,462,597,655,715,790,1271,1459,1461,1529,1534,1660,1661,1662] [0,1],a6 [61] [61,80,125,126,133,177,283,337,355,541,1071] [0,1],u6 [78,193] [13,16,125,126,133,345,346,456,601,608,629,879,907,942,954,1239,1663,1664],u6 [105,60] [80,84,228,264,355,465,597,655,790,896,909,953,1538,1665],a6 [78,165] [61,125,133,152,228,579,601,608,612,629,720,942,1176,1460,1558,1559,1663] [0,1],a6 [12,25] [45,177,247,461,475,718,719,1490,1515,1642,1666,1667,1668] [0,1],a6 [90,120] [45,61,126,177,228,247,481,490,576,636,640,646,664,747,757,1157,1550,1669,1670,1671] [0,1],e6 [105,194] [80,84,465,513,597,655,790,848,896,1103,1126,1127,1538],u6 [59,19] [125,126,133,177,282,352,354,633,739,740,782,791,813,814,815,920,1033],u6 [283] [5,16,125,126,133,177,210,541,1672,1673],a6 [37,121] [5,61,226,312,799,800,868,870,925,1046,1168,1303] [0,1],u6 [37,60] [13,16,80,84,228,264,312,342,355,909,953,1046,1080,1161,1168,1595,1598],a6 [286] [5,45,80,125,126,133,228,247,1002,1005,1044,1046] [0,1],u6 [60,195] [13,16,126,264,355,372,430,864,909,944,1117,1159,1582,1583,1602],u6 [114,195] [13,16,126,328,359,430,443,455,864,904,923,962,1117,1159,1582,1583,1602],u6 [316] [5,16,125,126,133,177,541,1674,1675],u6 [60,24] [5,13,126,291,292,347,786,807,867,909,953,1614],a6 [37,13] [5,16,125,133,177,247,312,427,484,925,1046,1168,1303,1595,1599,1600,1676,1677] [0,1],u6 [83,7] [5,126,210,270,285,453,896,1204,1526,1541],u6 [19,7] [5,16,184,191,270,282,285,352,354,453,508,782,783,791,908,920,1033,1678,1679],u6 [19,121] [5,16,61,226,233,354,782,799,800,920,967],([193,0,2,3,4,5,83],[5,13,61,126,177,242,346,455,1352,1354,1680],[0,1]),a6 [19,44] [125,126,133,177,233,235,236,247,354,605,619,622,782] [0,1],u6 [193,142] ([45,177,228,247,406,808,809,954,1101,1102,1189,1235,1239,1367]++r 1681 4),a6 [193,121] [16,125,226,799,800,869,890,907,1685,1686,1687] [0,1],u6 [184,193] [16,125,126,133,345,456,934,986,1085,1239,1374,1572,1688],a6 [60,7] [5,45,127,191,223,264,267,355,508,896,908,909,944,953,1526] [0,1],a6 [165,6] [45,125,126,177,228,489,745,760,762,763,764,1135,1176,1689,1690,1691] [0,1],a6 [12,340] [5,16,125,133,247,1048,1258,1330,1332,1338,1339,1400,1616,1617,1642,1692] [0,1],a6 [59,12] [228,247,461,475,633,739,740,813,814,815,1048,1258,1434,1545,1642,1693,1694,1695] [0,1],a6 [93,340] [5,16,125,133,707,708,721,1330,1338,1339,1410,1557,1560,1616,1617] [0,1],a6 [6,26] [16,471,737,745,760,762,763,767,772] [0,1],([0,24,19,3,4,5],[41,77,125,133,261],[0]),a6 [90,195] [16,126,177,247,372,636,645,646,664,1117,1159,1164,1387,1582,1583,1696,1697] [0,1],u6 [182,195] [126,177,247,430,864,948,949,960,962,1042,1117,1159,1164,1319,1583],a6 [37,14] [16,125,133,177,312,802,804,1046,1168,1190,1303,1336] [0,1],([93,28,0,2,3,5],[177,228,541,714],[0,1]),a6 [165,44] [125,153,228,235,236,247,579,619,622,720,777,1135,1176,1652,1698,1699] [1],a6 [165,195] [125,126,177,430,579,962,1135,1159,1164,1176,1387,1460,1582,1583,1700,1701,1702] [1],u6 [59,193] [11,61,125,133,177,345,346,456,633,739,813,815,954,1189,1235,1239,1545,1546],a6 [214] [45,61,80,125,133,177,210,337,541,745] [0,1],a6 [105,293] [5,79,80,465,597,790,896,1534,1634,1636,1665] [1],u6 [195,121] [5,61,226,372,799,870,967,1117,1159,1164,1387],u6 [182,37] [61,177,342,948,949,1046,1080,1168,1272,1303,1319,1375,1376,1565,1566,1595],u6 [184,195] [5,61,126,177,372,864,986,1042,1117,1164,1309,1387,1536,1583,1703],([37,0,2,3,4,5,83],[5,61,126,177,242,805,806,1046,1419],[0]),a6 [105,44] [5,235,236,465,605,619,622,655,662,776,790] [0,1],a6 [310] [16,45,61,80,126,133,228,247,455,954,1704,1705,1706] [0,1],a6 [93,100] [5,16,228,462,706,707,708,872,1058,1383,1461,1557,1660,1661] [0,1],a6 [236] [5,45,61,79,80,125,126,133,177,210,228,247,665,1419] [0,1],a6 [37,90] [16,125,126,228,247,312,640,645,646,658,664,925,1046,1168,1303,1595,1598,1707] [0,1],a6 [37,25] [177,342,718,925,1168,1375,1490,1515,1666,1668] [0,1],([0,12,2,3,6,5],[126,541,1134],[0,1]),a6 [37,26] [5,13,61,84,125,133,770,771,772,774,925,1046,1168,1303,1375,1483,1537,1595,1598,1708] [0,1],u6 [37,142] [177,228,247,342,406,808,809,925,1102,1168,1303,1571],a6 [12,26] [16,61,125,177,228,247,471,767,770,771,1258,1483,1694,1709,1710] [0,1],a6 [165,12] ([45,228,247,475,720,1048,1135,1176,1258,1460,1558,1559,1642,1694]++r 1710 5) [0,1],u6 [78,83] [5,13,61,126,177,242,348,601,608,611,612,686,732,942,1419,1541,1715,1716],a6 [12,7] [16,61,127,177,184,191,210,223,267,270,285,461,508,541,1258,1642,1694,1717] [0,1],a6 [105,14] [5,125,133,465,655,662,743,790,802,804,1190,1336] [0,1],a6 [93,25] [45,177,383,706,707,708,718,1383,1437,1490,1515,1666,1718,1719] [0,1],a6 [41,340] [125,133,177,669,712,930,1330,1331,1339,1400,1410,1542,1616,1617] [0,1],a6 [6,7] [16,127,184,191,270,508,737,745,760,762,763] [0,1],a6 [271,26] [16,79,125,471,770,774,896,1539,1720] [1],u6 [320] [5,61,80,125,133,177,210,541,1721]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_9 : checkNodesBT W_23 g_23 F_23 P_23_9 A_23 B_23_8 9 N_23_9 = true := by decide +kernel
def B_23_9 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_9
set_option maxRecDepth 500000 in
lemma B_23_9_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 9 xs.toFinset) B_23_9 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok (buildPoolsSubBT_sound S_23_ok) A_23_ok B_23_8_ok C_23_9
def U_23_10 : List Nat := [35,41,61,79,80,125,126,133,177,206,210,223,228,247,282,347,355,359,406,456,541,556,579,640,655,664,686,745,782,786,824,870,896,908,930,942,954,1319,1419,1526,1534,1536,1538,1540,1557,1558,1572,1582,1583,1590,1594,1595,1598,1602,1610,1611,1628,1642,1645,1694,1722,1723]
def P_23_10 : BT (Option BoundPool) := buildPoolsSubBT 11 W_23 r_23 S_23 ps_23 U_23_10
def N_23_10 : List NodeSpec := [a6 [184] [35,61,79,80,125,126,133,177,210,247,541,1536,1572] [0,1],a6 [78] [61,79,80,125,126,133,177,210,247,541,942] [0,1],a6 [165] [61,79,126,133,177,206,210,228,247,579,896,1558,1722] [0,1],u6 [105] [61,79,80,125,126,133,177,210,228,247,655,896,1534,1538],a6 [41] [61,79,80,125,126,133,210,228,247,896,930] [0,1],a6 [90] [61,79,125,126,133,177,206,210,247,541,640,664,1723] [0,1],a6 [271] [61,79,80,125,126,206,210,228,541,556,896,1645] [0,1],a6 [93] [61,79,80,125,126,133,210,228,541,1557] [0,1],a6 [194] [61,79,80,125,126,206,210,228,541,556,896] [0,1],u6 [24] [61,79,80,125,126,228,247,347,786],a6 [142] [125,126,133,177,247,406,896] [0,1],a6 [7] [61,79,80,125,126,133,177,210,223,228,247,896,908,1526] [0,1],a6 [114] [61,79,80,125,126,206,210,228,359,556,896] [0,1],a6 [182] [35,61,79,80,125,126,133,177,210,228,896,1319] [0,1],a6 [59] [61,79,80,125,126,133,177,210,228,247,896] [0,1],a6 [189] [61,79,80,125,126,206,210,228,541,556,824] [0,1],a6 [37] [61,79,80,125,126,133,210,228,247,1595,1598] [0,1],a6 [19] [61,125,126,133,177,206,228,247,282,782,1610,1611] [0,1],a6 [268] [79,80,541,556,896,1594] [0,1],a6 [121] [61,125,126,133,177,247,541,870] [0,1],u6 [193] [41,61,79,126,133,206,210,228,247,456,954,1590],a6 [195] [61,125,126,133,177,210,228,247,556,1582,1583,1602] [0,1],a6 [44] [61,125,126,133,177,210,541] [0,1],a6 [83] [61,79,125,126,133,177,228,247,556,686,896,1419,1540,1628] [0,1],a6 [12] [61,79,80,125,126,133,177,210,247,541,1642,1694] [0,1],a6 [60] [61,79,80,125,126,206,210,355,541,556,896] [0,1],a6 [6] [61,125,126,133,177,541,745] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_10 : checkNodesBT W_23 g_23 F_23 P_23_10 A_23 B_23_9 10 N_23_10 = true := by decide +kernel
def B_23_10 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_10
set_option maxRecDepth 500000 in
lemma B_23_10_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 10 xs.toFinset) B_23_10 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok (buildPoolsSubBT_sound S_23_ok) A_23_ok B_23_9_ok C_23_10
def U_23_11 : List Nat := [79,206,210,556]
def P_23_11 : BT (Option BoundPool) := buildPoolsSubBT 11 W_23 r_23 S_23 ps_23 U_23_11
def N_23_11 : List NodeSpec := [a6 [] [79,206,210,556] [0,1]]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_11 : checkNodesBT W_23 g_23 F_23 P_23_11 A_23 B_23_10 11 N_23_11 = true := by decide +kernel
def B_23_11 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_11
set_option maxRecDepth 500000 in
lemma B_23_11_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 11 xs.toFinset) B_23_11 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok (buildPoolsSubBT_sound S_23_ok) A_23_ok B_23_10_ok C_23_11
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_23_ok : forestRootCheck r_23 g_23 [(VAR 0,14,15),(VAR 1,13,15),(VAR 2,11,15),(VAR 3,7,15),(VAR 4,6,22),(VAR 5,3,35)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_23_in : bucketContainsBT B_23_11 r_23 = true := by decide +kernel
lemma low_23 : Lower r_23 g_23 12 := lower_of_forestBT root_23_ok B_23_11_ok root_23_in

def g_orig := (d 0xfeeaeaa8ece8e8a0)
set_option maxHeartbeats 0 in
lemma low_orig : Lower (varsOf 63) g_orig 12 := carry_of (swaps := [(0,5),(1,4),(2,3),(3,4)]) (by decide +kernel) low_23
def targetFn (x : Fin 6 → Bool) : Bool := Nat.testBit (4276808360 * 2 ^ 32 + 3974686880) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def temoin : List Gate := [⟨.or,[3,4]⟩,⟨.or,[1,6]⟩,⟨.and,[6,1]⟩,⟨.and,[3,4]⟩,⟨.or,[8,0]⟩,⟨.and,[2,10]⟩,⟨.and,[7,0]⟩,⟨.or,[10,2]⟩,⟨.or,[5,8]⟩,⟨.and,[13,14]⟩,⟨.or,[9,12]⟩,⟨.and,[16,15]⟩,⟨.or,[11,17]⟩]
lemma temoin_ok : PEqualNP.MetaComplexity.Monotone2 ⟨temoin, 18⟩ := by
  intro g hg; simp [temoin] at hg; rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxHeartbeats 0 in
lemma tgt_eq_G : ∀ r : Row, targetFn (evalInput6 r) = g_orig.testBit r.val := by decide +kernel
set_option maxHeartbeats 0 in
lemma temoin_eval : ∀ r : Row, Circuit.eval ⟨temoin, 18⟩ (List.ofFn (evalInput6 r)) = g_orig.testBit r.val := by decide +kernel

end PEqualNP.Outside.L_meta_45474

open PEqualNP.Outside.L_meta_45474 in
theorem PEqualNP.Outside.L_meta_45474 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808360 * 2 ^ 32 + 3974686880) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808360 * 2 ^ 32 + 3974686880) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  exact replace_of_lower6 g_orig (by decide) (by decide) (by decide) 12 low_orig temoin 18 (by decide) temoin_ok targetFn tgt_eq_G temoin_eval
