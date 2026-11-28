import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_51784
namespace Wide
open PEqualNP.CircuitLowerBounds
abbrev Row := Fin 256
abbrev Wire := Row → Bool
def bin (d a b : Nat) : Nat :=
  match d with
  | 0 => a &&& b
  | 1 => a ||| b
  | 2 => a ^^^ (a &&& b)
  | _ => b ^^^ (a &&& b)
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
set_option maxRecDepth 16000 in
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
def Essential (T : Nat) (roots : List Nat) (a : Nat) : Prop :=
  ∃ r s : Row, T.testBit r.val ≠ T.testBit s.val ∧ ∀ v ∈ roots, v ≠ a → v.testBit r.val = v.testBit s.val
lemma raw_required {T k S} (h : Live T k S) (roots : List Nat) (a : Nat)
    (sub : ∀ v ∈ S, v ∈ roots) (he : Essential T roots a) : a ∈ S := by
  obtain ⟨r, s, hd, hiso⟩ := he
  obtain ⟨v, hv, hvd⟩ := live_sep h hd
  by_cases veq : v = a
  · exact veq ▸ hv
  · exact (hvd (hiso v (sub v hv) veq)).elim
lemma obs_not_const {T : Nat} (hT0 : T ≠ 0) (hTlt : T < 2^256) (hTb0 : T.testBit 0 = false) :
    ¬Constant (obs T) := by
  intro hc
  have h := normPack_const hc
  rw [normPack_eq_of_obs hTlt hTb0] at h
  exact hT0 h
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
def varsOf (m : Nat) : List Nat :=
  (List.range 8).filterMap fun i => if m.testBit i then some (VAR i) else none
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
def liftCheck (z o : Nat) (roots : List Nat) (T : Nat) (other : List Nat) (G : Nat)
    (essPairs : List (Nat × Nat × Nat)) : Bool :=
  checkProper T && checkRoots roots && checkProper G &&
    decide (essPairs.map Prod.fst).Nodup &&
    (fixWord z o T == G) &&
    roots.all (fun a => freeIn other (fixWord z o a)) &&
    essPairs.all (fun e => checkEss1 T roots e.1 e.2.1 e.2.2 &&
      (fixWord z o e.1 == 0 || fixWord z o e.1 == ALL256))
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
    · exact ⟨true, by rw [h1]; funext r'; simp only [obs, ALL256]; have := r'.isLt; exact Nat.testBit_two_pow_sub_one 256 r'.val |> fun e => by simpa [this] using e⟩
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
      have hi7 : i < 8 := by simpa using hi2
      have hv : (varsOf 255)[i]? = some (VAR i) := by
        interval_cases i <;> decide
      simp only [List.getElem_map, List.getElem_ofFn, seeds, evalInput, swRead, Bool.false_bne]
      have hget : (varsOf 255)[i]'(by simpa [seeds] using hi1) = VAR i := by
        have := List.getElem?_eq_some_iff.mp hv; exact this.2
      rw [hget]
      exact var_testBit ⟨i, hi7⟩ r
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

end Wide
namespace Small
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
def opIdx (s t : Bool) : Nat := if s then (if t then 1 else 3) else (if t then 2 else 0)
def reps (w : List SWire) : List Nat := w.map Prod.snd
def simple (w : List SWire) (z : Nat) : Prop := z = 0 ∨ z ∈ reps w
def priced (w : List SWire) (paid : Bool) (z : Nat) : Prop :=
  simple w z ∨ (paid = true ∧ ∃ d < 4, ∃ a ∈ reps w, ∃ b ∈ reps w, a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧ z = bin d a b)
lemma bin_eq_cases (d a b : Nat) (hd : d < 4) (h : a = 0 ∨ b = 0 ∨ a = b) :
    bin d a b = 0 ∨ bin d a b = a ∨ bin d a b = b := by
  rcases h with rfl | rfl | rfl <;> interval_cases d <;> simp [bin]
lemma opIdx_lt (s t : Bool) : opIdx s t < 4 := by cases s <;> cases t <;> decide
lemma made_priced (w : List SWire) (d : Nat) (a b : SWire) (hd : d < 4)
    (pa : simple w a.2) (pb : simple w b.2) : priced w true (bin d a.2 b.2) := by
  by_cases h : a.2 = 0 ∨ b.2 = 0 ∨ a.2 = b.2
  · rcases bin_eq_cases d a.2 b.2 hd h with e | e | e
    · exact Or.inl (Or.inl e)
    · rw [e]; exact Or.inl pa
    · rw [e]; exact Or.inl pb
  · push Not at h
    exact Or.inr ⟨rfl, d, hd, a.2, pa.resolve_left h.1, b.2, pb.resolve_left h.2.1, h.1, h.2.1, h.2.2, rfl⟩
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
lemma array_forall_of_list {α : Type} {P : α → Prop} {l : List α} (h : ∀ x ∈ l, P x) :
    ∀ i (hi : i < l.toArray.size), P l.toArray[i] :=
  fun i hi => h l.toArray[i] (Array.getElem_mem_toList hi)
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
  have hinit : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) (BT.empty : BT (Option BoundPool)) := trivial
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

def dualRow (r : Row) : Row := ⟨(r.val ^^^ 127) % 128, Nat.mod_lt _ (by decide)⟩

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

def identifyRow (z o i j : Nat) (r : Row) : Row :=
  let mask := if r.val.testBit i then 1 <<< j else 0
  ⟨((fixRow z o r).val &&& (127 ^^^ (1 <<< j)) ||| mask) % 128, Nat.mod_lt _ (by decide)⟩
lemma mappedSlice {f : Row → Row} {raw R : List Nat} {T G D L : Nat}
    (proper : checkProper G = true) (inDomain : ∀ r : Row, D.testBit (f r).val = true)
    (covered : raw.all (fun v => freeIn R (renameW f v)) = true)
    (mapped : renameW f T = G) (bound : Lower R G L) : Slice raw T D L := by
  have ⟨g0,glt,gb0⟩ := checkProper_sound proper
  refine ⟨f, R, inDomain, fun a ha => freeIn_sound (List.all_eq_true.mp covered a ha), ?_, ?_⟩
  · rw [← obs_renameW, mapped]
    exact obs_not_const g0 glt gb0
  · rw [← obs_renameW, mapped]
    exact bound

def lb78 (entries : List (List Nat × List Nat)) : List NodeSpec :=
  entries.map (fun entry => (entry.1, entry.2, [0]))

def lb26 : List Nat := varsOf 21
def lb18 : Nat := 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0
def lb25 : List Nat := [17,20,5,5,20,17]
def lb20 : List Nat := [16,16,1,4,4,1]
def lb19 : Nat := fullMask 6
def lb9 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,45,36),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,30,24),(0xffff0000ffff0000ffff0000ffff0000,51,3)]
def lb31 : List (Nat × Nat × Nat) := []
def lb33 : BT Decor := buildWiresBT 2 lb9 lb31
def lb6 : List (List (Nat × Nat)) := [[],[(2,4)],[(0,2)],[(0,4)],[(2,4),(0,2)],[(2,4),(0,4)]]
def lb7 : BT (List (Nat × Nat)) := btOfList 3 lb6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb22 : goodPairs lb18 lb25 lb20 := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb10 : ∀ x ∈ lb9, faithful lb25 lb20 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb34 : btAll (fun x => faithful lb25 lb20 x ∧ x.1 < 2^128) lb33 := buildWiresBT_faithful lb10
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb8 : btAll (fun sw => swapsValid sw = true ∧ permWord sw lb18 = lb18) lb7 := btAll_ofList (autos_of (by decide +kernel))
def lb27 : List (Option (Nat × Nat)) := []
def lb28 : BT (Option (Nat × Nat)) := btOfList 1 lb27
def lb30 : List PoolSpec := []
def lb23 : BT (Option BoundPool) := buildPoolsBT 1 lb33 lb26 lb28 lb30
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb29 : btAll (fun o => ∀ p, o = some p → Slice lb26 lb18 p.1 p.2) lb28 := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice lb26 lb18 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb24 : btAll (fun o => ∀ c, o = some c → ValidPool lb26 lb18 c) lb23 := buildPoolsBT_sound lb29
def lb16 : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb17 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb18 (3 - 1) xs.toFinset) lb16 := trivial
def lb11 : List NodeSpec := lb78 [([0,1,2],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb32 : checkNodesBT lb33 lb18 lb19 lb23 lb7 lb16 3 lb11 = true := by decide +kernel
def lb21 : List NodeSpec := lb11
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb15 : checkNodesBT lb33 lb18 lb19 lb23 lb7 lb16 3 lb21 = true := lb32
def lb13 : BT (List (List Nat)) := buildBucketsBT lb33 lb21
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb14 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb18 3 xs.toFinset) lb13 := buildBucketsBT_sound (by decide) lb22 lb34 lb24 lb8 lb17 lb15
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb12 : Lower lb26 lb18 4 := lower_of_forestBT (essPairs := [(VAR 0,4,5),(VAR 2,1,5),(VAR 4,1,17)]) (by decide +kernel) lb14 (by decide +kernel)
def lb2 : List Nat := varsOf 13
def lb1 : Nat := 0xfaa0faa0faa0faa0faa0faa0faa0faa0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb0 : Lower lb2 lb1 4 := carry_of (swaps := [(3,4)]) (roots2 := lb26) (T2 := lb18) (by decide +kernel) lb12
def lb5 : List Nat := varsOf 15
def lb4 : Nat := 0xfae8fae8fae8fae8fae8fae8fae8fae8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb3 : Lower lb5 lb4 5 := lift_of (z := 2) (o := 0) (essPairs := [(VAR 1,1,3)]) (by decide +kernel) lb0
def lb37 : List Nat := varsOf 19
def lb36 : Nat := 0xeeee8888eeee8888eeee8888eeee8888
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb35 : Lower lb37 lb36 4 := carry_of (swaps := [(1,2)]) (roots2 := lb26) (T2 := lb18) (by decide +kernel) lb12
def lb40 : List Nat := varsOf 27
def lb39 : Nat := 0xeeeeaa88eeeeaa88eeeeaa88eeeeaa88
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb38 : Lower lb40 lb39 5 := lift_of (z := 8) (o := 0) (essPairs := [(VAR 3,1,9)]) (by decide +kernel) lb35
def lb43 : List Nat := varsOf 29
def lb42 : Nat := 0xfaaafaa0faaafaa0faaafaa0faaafaa0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb41 : Lower lb43 lb42 5 := carry_of (swaps := [(3,4),(1,2)]) (roots2 := lb40) (T2 := lb39) (by decide +kernel) lb38
def lb77 : List Nat := varsOf 23
def lb76 : Nat := 0xeeeee8e8eeeee8e8eeeee8e8eeeee8e8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb75 : Lower lb77 lb76 5 := carry_of (swaps := [(3,4),(1,2)]) (roots2 := lb5) (T2 := lb4) (by decide +kernel) lb3
def lb63 : List Nat := varsOf 31
def lb55 : Nat := 0xfeeefae8feeefae8feeefae8feeefae8
def lb62 : List Nat := [5,6,3,3,6,5,12,9,9,18,17,17,26,12,28,26,28]
def lb57 : List Nat := [4,4,1,2,2,1,4,1,8,2,1,16,24,8,24,10,20]
def lb56 : Nat := fullMask 17
def lb47 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,3501,1188),(0xcccccccccccccccccccccccccccccccc,0x921e,0x8218),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x16073,0x10043),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x1f1c0,0xf100),(0xffff0000ffff0000ffff0000ffff0000,0x1de00,0x15800)]
def lb73 : BT Decor := buildWiresBT 3 lb47 lb31
def lb44 : List (List (Nat × Nat)) := [[],[(3,4),(1,2)]]
def lb45 : BT (List (Nat × Nat)) := btOfList 1 lb44
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb59 : goodPairs lb55 lb62 lb57 := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb48 : ∀ x ∈ lb47, faithful lb62 lb57 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb74 : btAll (fun x => faithful lb62 lb57 x ∧ x.1 < 2^128) lb73 := buildWiresBT_faithful lb48
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb46 : btAll (fun sw => swapsValid sw = true ∧ permWord sw lb55 = lb55) lb45 := btAll_ofList (autos_of (by decide +kernel))
def lb68 : List (Option (Nat × Nat)) := [some (subcubeFast 2 0,5),some (subcubeFast 4 0,5),some (subcubeFast 8 0,5),some (subcubeFast 16 0,5)]
def lb69 : BT (Option (Nat × Nat)) := btOfList 2 lb68
def lb71 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[])]
def lb60 : BT (Option BoundPool) := buildPoolsBT 2 lb73 lb63 lb69 lb71
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb67 : Slice lb63 lb55 (subcubeFast 16 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) lb3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb66 : Slice lb63 lb55 (subcubeFast 8 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) lb75
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb65 : Slice lb63 lb55 (subcubeFast 4 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) lb38
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb64 : Slice lb63 lb55 (subcubeFast 2 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) lb41
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb70 : btAll (fun o => ∀ p, o = some p → Slice lb63 lb55 p.1 p.2) lb69 := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice lb63 lb55 p.1 p.2) (forall_cons (fun _ h => by cases h; exact lb64) (forall_cons (fun _ h => by cases h; exact lb65) (forall_cons (fun _ h => by cases h; exact lb66) (forall_cons (fun _ h => by cases h; exact lb67) (fun _ h => (List.not_mem_nil h).elim)))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb61 : btAll (fun o => ∀ c, o = some c → ValidPool lb63 lb55 c) lb60 := buildPoolsBT_sound lb70
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb54 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb55 (6 - 1) xs.toFinset) lb16 := trivial
def lb49 : List NodeSpec := lb78 [([0,1,2,3,4],[0,1,2,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb72 : checkNodesBT lb73 lb55 lb56 lb60 lb45 lb16 6 lb49 = true := by decide +kernel
def lb58 : List NodeSpec := lb49
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb53 : checkNodesBT lb73 lb55 lb56 lb60 lb45 lb16 6 lb58 = true := lb72
def lb51 : BT (List (List Nat)) := buildBucketsBT lb73 lb58
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb52 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb55 6 xs.toFinset) lb51 := buildBucketsBT_sound (by decide) lb59 lb74 lb61 lb46 lb54 lb53
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb50 : Lower lb63 lb55 7 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 3,1,9),(VAR 4,1,17)]) (by decide +kernel) lb52 (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q1 : Lower (varsOf 61) 0xfffafafaffaafaa0fffafafaffaafaa0 7 := by
  apply carry_of (swaps := [(4, 5), (3, 4), (2, 3), (1, 2)]) (roots2 := lb63) (T2 := lb55) _ lb50
  decide +kernel
def lb99 : Nat := 0xffffff00ff000000ffffff00ff000000
def lb109 : List Nat := varsOf 56
def lb185 : List Nat := [24,24,40,40,48,48,24,40,48]
def lb177 : List Nat := [16,8,32,8,32,16,32,16,8]
def lb159 : Nat := fullMask 9
def lb123 : List Decor := [(0xff00ff00ff00ff00ff00ff00ff00ff00,0xcf,0x10a),(0xffff0000ffff0000ffff0000ffff0000,0x173,0xa1),(0xffffffff00000000ffffffff00000000,0x1bc,0x54)]
def lb115 : Array Decor := buildWires lb123 lb31
def lb119 : Array (List (Nat × Nat)) := #[]
def lb195 : List (Nat × Nat) := []
def lb197 : Array (Nat × Nat) := lb195.toArray
def lb105 : Array (Option BoundPool) := buildPools lb115 lb109 lb197 lb30
lemma lb165 : goodPairs lb99 lb185 lb177 := goodPairs_of (by decide +kernel)
lemma lb124 : ∀ x ∈ lb123, faithful lb185 lb177 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma lb116 : ∀ x ∈ lb115.toList, faithful lb185 lb177 x ∧ x.1 < 2^128 := buildWires_faithful lb124
lemma lb120 : ∀ sw ∈ lb119.toList, swapsValid sw = true ∧ permWord sw lb99 = lb99 := autos_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma lb198 : ∀ i (hi : i < lb197.size), Slice lb109 lb99 lb197[i].1 lb197[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice lb109 lb99 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma lb106 : ∀ i (hi : i < lb105.size), ∀ c, lb105[i] = some c → ValidPool lb109 lb99 c := buildPools_sound lb198
def lb133 : Array (List (List Nat)) := #[]
lemma lb134 : ∀ i (hi : i < lb133.size), ∀ xs ∈ lb133[i], Impossible lb99 (0 - 1) xs.toFinset := by intro i hi; simp [lb133] at hi
def lb179 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb148 : checkNodes lb115 lb99 lb159 lb105 lb119 lb133 0 lb179 = true := by decide +kernel
def lb127 : Array (List (List Nat)) := buildBuckets 1 lb115 lb179
lemma lb128 : ∀ i (hi : i < lb127.size), ∀ xs ∈ lb127[i], Impossible lb99 0 xs.toFinset :=
  buildBuckets_sound (by decide) lb165 lb116 lb106 lb120 lb134 lb148
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb149 : checkNodes lb115 lb99 lb159 lb105 lb119 lb127 1 lb179 = true := by decide +kernel
lemma lb129 : ∀ i (hi : i < lb127.size), ∀ xs ∈ lb127[i], Impossible lb99 1 xs.toFinset :=
  buildBuckets_sound (by decide) lb165 lb116 lb106 lb120 lb128 lb149
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb150 : checkNodes lb115 lb99 lb159 lb105 lb119 lb127 2 lb179 = true := by decide +kernel
lemma lb130 : ∀ i (hi : i < lb127.size), ∀ xs ∈ lb127[i], Impossible lb99 2 xs.toFinset :=
  buildBuckets_sound (by decide) lb165 lb116 lb106 lb120 lb129 lb150
def lb180 : List NodeSpec := [([0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb151 : checkNodes lb115 lb99 lb159 lb105 lb119 lb127 3 lb180 = true := by decide +kernel
def lb131 : Array (List (List Nat)) := buildBuckets 1 lb115 lb180
lemma lb132 : ∀ i (hi : i < lb131.size), ∀ xs ∈ lb131[i], Impossible lb99 3 xs.toFinset :=
  buildBuckets_sound (by decide) lb165 lb116 lb106 lb120 lb130 lb151
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb162 : forestRootCheck lb109 lb99 [(VAR 3,24,16),(VAR 4,24,8),(VAR 5,40,8)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb161 : bucketContains lb131 lb109 = true := by decide +kernel
lemma lb167 : Lower lb109 lb99 4 := lower_of_forest lb162 lb132 lb161
def lb100 : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def lb110 : List Nat := varsOf 7
lemma lb169 : carryOK [(2,5),(1,4),(0,3)] lb110 lb100 lb109 lb99 = true := by decide +kernel
lemma lb168 : Lower lb110 lb100 4 := carry_of lb169 lb167
def lb102 : Nat := 0xeeeeeeee88888888eeeeeeee88888888
def lb112 : List Nat := varsOf 35
lemma lb172 : carryOK [(1,2),(0,2),(1,4),(0,3)] lb112 lb102 lb109 lb99 = true := by decide +kernel
lemma lb171 : Lower lb112 lb102 4 := carry_of lb172 lb167
def lb103 : Nat := 0xfafafafaa0a0a0a0fafafafaa0a0a0a0
def lb113 : List Nat := varsOf 37
lemma lb174 : carryOK [(2,4),(0,1),(0,3)] lb113 lb103 lb109 lb99 = true := by decide +kernel
lemma lb173 : Lower lb113 lb103 4 := carry_of lb174 lb167
def lb104 : Nat := 0xfcfcfcfcc0c0c0c0fcfcfcfcc0c0c0c0
def lb114 : List Nat := varsOf 38
lemma lb176 : carryOK [(2,4),(1,3)] lb114 lb104 lb109 lb99 = true := by decide +kernel
lemma lb175 : Lower lb114 lb104 4 := carry_of lb176 lb167
def lb101 : Nat := 0xfefefefee8e8e8e8fefefefee8e8e8e8
def lb111 : List Nat := varsOf 39
def lb186 : List Nat := [3,3,5,5,6,6,33,33,34,34,36,36,3,3,5,5,6,6,33,33,34,34,36,36]
def lb178 : List Nat := [2,1,4,1,4,2,32,1,32,2,32,4,4,32,2,32,1,32,2,4,1,4,1,2]
def lb160 : Nat := fullMask 24
def lb125 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcf0cf,0x51008a),(0xcccccccccccccccccccccccccccccccc,0x333333,0x844221),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xc3cc3c,0x281814),(0xffffffff00000000ffffffff00000000,0xfc0fc0,0x2a540)]
def lb201 : List (Nat × Nat × Nat) := [(1,0,1),(2,4,2),(1,4,2),(1,0,2),(2,6,3),(1,1,2)]
def lb117 : Array Decor := buildWires lb125 lb201
def lb121 : Array (List (Nat × Nat)) := #[[],[(2,5)],[(0,1)],[(2,5),(0,1)],[(1,2)],[(1,5),(1,2)],[(0,1),(0,2)],[(1,5),(0,1),(0,2)],[(1,5),(0,2)]]
def lb196 : List (Nat × Nat) := [(subcube 2 0,4),(subcube 1 0,4),(subcube 32 0,4),(subcube 4 0,4)]
def lb199 : Array (Nat × Nat) := lb196.toArray
def lb107 : Array (Option BoundPool) := buildPools lb117 lb111 lb199 lb71
lemma lb166 : goodPairs lb101 lb186 lb178 := goodPairs_of (by decide +kernel)
lemma lb126 : ∀ x ∈ lb125, faithful lb186 lb178 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma lb118 : ∀ x ∈ lb117.toList, faithful lb186 lb178 x ∧ x.1 < 2^128 := buildWires_faithful lb126
lemma lb122 : ∀ sw ∈ lb121.toList, swapsValid sw = true ∧ permWord sw lb101 = lb101 := autos_of (by decide +kernel)
lemma lb188 : sliceDirectCheck 2 0 0 lb111 lb101 lb113 lb103 = true := by decide +kernel
lemma lb187 : Slice lb111 lb101 (subcube 2 0) 4 := slice_direct lb188 lb173
lemma lb190 : sliceDirectCheck 1 0 0 lb111 lb101 lb114 lb104 = true := by decide +kernel
lemma lb189 : Slice lb111 lb101 (subcube 1 0) 4 := slice_direct lb190 lb175
lemma lb192 : sliceDirectCheck 32 0 0 lb111 lb101 lb110 lb100 = true := by decide +kernel
lemma lb191 : Slice lb111 lb101 (subcube 32 0) 4 := slice_direct lb192 lb168
lemma lb194 : sliceDirectCheck 4 0 0 lb111 lb101 lb112 lb102 = true := by decide +kernel
lemma lb193 : Slice lb111 lb101 (subcube 4 0) 4 := slice_direct lb194 lb171
set_option maxRecDepth 200000 in
lemma lb200 : ∀ i (hi : i < lb199.size), Slice lb111 lb101 lb199[i].1 lb199[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice lb111 lb101 p.1 p.2) (forall_cons lb187 (forall_cons lb189 (forall_cons lb191 (forall_cons lb193 (fun _ h => (List.not_mem_nil h).elim)))))
lemma lb108 : ∀ i (hi : i < lb107.size), ∀ c, lb107[i] = some c → ValidPool lb111 lb101 c := buildPools_sound lb200
lemma lb147 : ∀ i (hi : i < lb133.size), ∀ xs ∈ lb133[i], Impossible lb101 (0 - 1) xs.toFinset := by intro i hi; simp [lb133] at hi
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb152 : checkNodes lb117 lb101 lb160 lb107 lb121 lb133 0 lb179 = true := by decide +kernel
def lb135 : Array (List (List Nat)) := buildBuckets 1 lb117 lb179
lemma lb136 : ∀ i (hi : i < lb135.size), ∀ xs ∈ lb135[i], Impossible lb101 0 xs.toFinset :=
  buildBuckets_sound (by decide) lb166 lb118 lb108 lb122 lb147 lb152
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb153 : checkNodes lb117 lb101 lb160 lb107 lb121 lb135 1 lb179 = true := by decide +kernel
lemma lb137 : ∀ i (hi : i < lb135.size), ∀ xs ∈ lb135[i], Impossible lb101 1 xs.toFinset :=
  buildBuckets_sound (by decide) lb166 lb118 lb108 lb122 lb136 lb153
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb154 : checkNodes lb117 lb101 lb160 lb107 lb121 lb135 2 lb179 = true := by decide +kernel
lemma lb138 : ∀ i (hi : i < lb135.size), ∀ xs ∈ lb135[i], Impossible lb101 2 xs.toFinset :=
  buildBuckets_sound (by decide) lb166 lb118 lb108 lb122 lb137 lb154
def lb181 : List NodeSpec := [([8,0,1,2],[],[]),([4,7,9,3],[0,1],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb155 : checkNodes lb117 lb101 lb160 lb107 lb121 lb135 3 lb181 = true := by decide +kernel
def lb139 : Array (List (List Nat)) := buildBuckets 1 lb117 lb181
lemma lb140 : ∀ i (hi : i < lb139.size), ∀ xs ∈ lb139[i], Impossible lb101 3 xs.toFinset :=
  buildBuckets_sound (by decide) lb166 lb118 lb108 lb122 lb138 lb155
def lb182 : List NodeSpec := [([5,0,1,2,3],[],[]),([0,1,2,6,3],[2],[0]),([1,4,2,7,3],[0,3],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb156 : checkNodes lb117 lb101 lb160 lb107 lb121 lb139 4 lb182 = true := by decide +kernel
def lb141 : Array (List (List Nat)) := buildBuckets 2 lb117 lb182
lemma lb142 : ∀ i (hi : i < lb141.size), ∀ xs ∈ lb141[i], Impossible lb101 4 xs.toFinset :=
  buildBuckets_sound (by decide) lb166 lb118 lb108 lb122 lb140 lb156
def lb183 : List NodeSpec := [([0,1,4,2,3],[0,1,3,2],[0,1,2,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb157 : checkNodes lb117 lb101 lb160 lb107 lb121 lb141 5 lb183 = true := by decide +kernel
def lb143 : Array (List (List Nat)) := buildBuckets 1 lb117 lb183
lemma lb144 : ∀ i (hi : i < lb143.size), ∀ xs ∈ lb143[i], Impossible lb101 5 xs.toFinset :=
  buildBuckets_sound (by decide) lb166 lb118 lb108 lb122 lb142 lb157
def lb184 : List NodeSpec := [([0,1,2,3],[0,1,3,2],[0,4,5,6,7,8])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb158 : checkNodes lb117 lb101 lb160 lb107 lb121 lb143 6 lb184 = true := by decide +kernel
def lb145 : Array (List (List Nat)) := buildBuckets 1 lb117 lb184
lemma lb146 : ∀ i (hi : i < lb145.size), ∀ xs ∈ lb145[i], Impossible lb101 6 xs.toFinset :=
  buildBuckets_sound (by decide) lb166 lb118 lb108 lb122 lb144 lb158
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb164 : forestRootCheck lb111 lb101 [(VAR 0,3,2),(VAR 1,3,1),(VAR 2,5,1),(VAR 5,33,1)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb163 : bucketContains lb145 lb111 = true := by decide +kernel
lemma lb170 : Lower lb111 lb101 7 := lower_of_forest lb164 lb146 lb163
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q2 : Lower (varsOf 39) 0xfefefefee8e8e8e8fefefefee8e8e8e8 7 := by
  apply carry_of (swaps := []) (roots2 := lb111) (T2 := lb101) _ lb170
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q3 : Lower (varsOf 27) 0xffeeee88ffeeee88ffeeee88ffeeee88 7 := by
  apply carry_of (swaps := [(4, 5), (2, 3)]) (roots2 := lb111) (T2 := lb101) _ lb170
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q4 : Lower (varsOf 29) 0xfffafaa0fffafaa0fffafaa0fffafaa0 7 := by
  apply carry_of (swaps := [(4, 5), (2, 3), (1, 2)]) (roots2 := lb111) (T2 := lb101) _ lb170
  decide +kernel
def lb220 : List Nat := varsOf 25
def lb213 : Nat := 0xffaaaa00ffaaaa00ffaaaa00ffaaaa00
def lb219 : List Nat := [17,24,9,9,24,17]
def lb214 : List Nat := [16,16,1,8,8,1]
def lb205 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,45,36),(0xff00ff00ff00ff00ff00ff00ff00ff00,30,24),(0xffff0000ffff0000ffff0000ffff0000,51,3)]
def lb223 : BT Decor := buildWiresBT 2 lb205 lb31
def lb202 : List (List (Nat × Nat)) := [[]]
def lb203 : BT (List (Nat × Nat)) := btOfList 1 lb202
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb216 : goodPairs lb213 lb219 lb214 := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb206 : ∀ x ∈ lb205, faithful lb219 lb214 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb224 : btAll (fun x => faithful lb219 lb214 x ∧ x.1 < 2^128) lb223 := buildWiresBT_faithful lb206
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb204 : btAll (fun sw => swapsValid sw = true ∧ permWord sw lb213 = lb213) lb203 := btAll_ofList (autos_of (by decide +kernel))
def lb217 : BT (Option BoundPool) := buildPoolsBT 1 lb223 lb220 lb28 lb30
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb221 : btAll (fun o => ∀ p, o = some p → Slice lb220 lb213 p.1 p.2) lb28 := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice lb220 lb213 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb218 : btAll (fun o => ∀ c, o = some c → ValidPool lb220 lb213 c) lb217 := buildPoolsBT_sound lb221
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb212 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb213 (3 - 1) xs.toFinset) lb16 := trivial
def lb207 : List NodeSpec := [([0,1,2],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb222 : checkNodesBT lb223 lb213 lb19 lb217 lb203 lb16 3 lb207 = true := by decide +kernel
def lb215 : List NodeSpec := lb207
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb211 : checkNodesBT lb223 lb213 lb19 lb217 lb203 lb16 3 lb215 = true := lb222
def lb209 : BT (List (List Nat)) := buildBucketsBT lb223 lb215
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb210 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb213 3 xs.toFinset) lb209 := buildBucketsBT_sound (by decide) lb216 lb224 lb218 lb204 lb212 lb211
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb208 : Lower lb220 lb213 4 := lower_of_forestBT (essPairs := [(VAR 0,8,9),(VAR 3,1,9),(VAR 4,1,17)]) (by decide +kernel) lb210 (by decide +kernel)
def lb227 : List Nat := varsOf 61
def lb226 : Nat := 0xfffafafafffaaa00fffafafafffaaa00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb225 : Lower lb227 lb226 6 := lift_of (z := 36) (o := 0) (essPairs := [(VAR 2,16,20),(VAR 5,1,33)]) (by decide +kernel) lb208
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q5 : Lower (varsOf 62) 0xfffcfcfcffccf0c0fffcfcfcffccf0c0 6 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (2, 3), (0, 1)]) (roots2 := lb227) (T2 := lb226) _ lb225
  decide +kernel
def lb228 : Nat := 0xffccffcccc00cc00ffccffcccc00cc00
def lb231 : List Nat := varsOf 42
def lb251 : List Nat := [10,10,34,34,40,40,10,34,40]
def lb250 : List Nat := [8,2,32,2,32,8,32,8,2]
def lb238 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xcf,0x10a),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x173,0xa1),(0xffffffff00000000ffffffff00000000,0x1bc,0x54)]
def lb233 : BT Decor := buildWiresBT 2 lb238 lb31
def lb235 : List (List (Nat × Nat)) := []
def lb236 : BT (List (Nat × Nat)) := btOfList 1 lb235
def lb252 : BT (Option PoolSpec) := btOfList 1 []
lemma lb246 : goodPairs lb228 lb251 lb250 := goodPairs_of (by decide +kernel)
lemma lb239 : ∀ x ∈ lb238, faithful lb251 lb250 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma lb234 : btAll (fun x => faithful lb251 lb250 x ∧ x.1 < 2^128) lb233 := buildWiresBT_faithful lb239
set_option maxRecDepth 500000 in
lemma lb237 : btAll (fun sw => swapsValid sw = true ∧ permWord sw lb228 = lb228) lb236 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma lb253 : btAll (fun o => ∀ p, o = some p → Slice lb231 lb228 p.1 p.2) lb28 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice lb231 lb228 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma lb240 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb228 2 xs.toFinset) lb16 := trivial
def lb230 : BT (Option BoundPool) := buildPoolsSubBT 1 lb233 lb231 lb28 lb252 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb243 : checkNodesBT lb233 lb228 lb159 lb230 lb236 lb16 3 lb180 = true := by decide +kernel
def lb241 : BT (List (List Nat)) := buildBucketsBT lb233 lb180
set_option maxRecDepth 500000 in
lemma lb242 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb228 3 xs.toFinset) lb241 :=
  buildBucketsBT_sound (by decide) lb246 lb234 (buildPoolsSubBT_sound lb253) lb237 lb240 lb243
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma lb245 : forestRootCheck lb231 lb228 [(VAR 1,10,8),(VAR 3,10,2),(VAR 5,34,2)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma lb244 : bucketContainsBT lb241 lb231 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma lb247 : Lower lb231 lb228 4 := lower_of_forestBT lb245 lb242 lb244
def lb229 : Nat := 0xffccffcccccccc00ffccffcccccccc00
def lb232 : List Nat := varsOf 58
lemma lb249 : liftCheck 16 0 lb232 lb229 lb231 lb228 [(VAR 4,18,2)] = true := by decide +kernel
lemma lb248 : Lower lb232 lb229 5 := lift_of lb249 lb247
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q6 : Lower (varsOf 57) 0xffaaaaaaffaaaa00ffaaaaaaffaaaa00 5 := by
  apply carry_of (swaps := [(4, 5), (0, 1)]) (roots2 := lb232) (T2 := lb229) _ lb248
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q7 : Lower (varsOf 53) 0xfafafafaaaaaa0a0fafafafaaaaaa0a0 5 := by
  apply carry_of (swaps := [(2, 3), (0, 1)]) (roots2 := lb232) (T2 := lb229) _ lb248
  decide +kernel
def lb254 : Nat := 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0
def lb257 : List Nat := varsOf 14
def lb274 : List Nat := [6,6,10,10,12,12,6,10,12]
def lb273 : List Nat := [4,2,8,2,8,4,8,4,2]
def lb261 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xcf,0x10a),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x173,0xa1),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x1bc,0x54)]
def lb258 : BT Decor := buildWiresBT 2 lb261 lb31
lemma lb269 : goodPairs lb254 lb274 lb273 := goodPairs_of (by decide +kernel)
lemma lb262 : ∀ x ∈ lb261, faithful lb274 lb273 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma lb259 : btAll (fun x => faithful lb274 lb273 x ∧ x.1 < 2^128) lb258 := buildWiresBT_faithful lb262
set_option maxRecDepth 500000 in
lemma lb260 : btAll (fun sw => swapsValid sw = true ∧ permWord sw lb254 = lb254) lb236 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma lb275 : btAll (fun o => ∀ p, o = some p → Slice lb257 lb254 p.1 p.2) lb28 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice lb257 lb254 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma lb263 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb254 2 xs.toFinset) lb16 := trivial
def lb256 : BT (Option BoundPool) := buildPoolsSubBT 1 lb258 lb257 lb28 lb252 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb266 : checkNodesBT lb258 lb254 lb159 lb256 lb236 lb16 3 lb180 = true := by decide +kernel
def lb264 : BT (List (List Nat)) := buildBucketsBT lb258 lb180
set_option maxRecDepth 500000 in
lemma lb265 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb254 3 xs.toFinset) lb264 :=
  buildBucketsBT_sound (by decide) lb269 lb259 (buildPoolsSubBT_sound lb275) lb260 lb263 lb266
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma lb268 : forestRootCheck lb257 lb254 [(VAR 1,6,4),(VAR 2,6,2),(VAR 3,10,2)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma lb267 : bucketContainsBT lb264 lb257 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma lb270 : Lower lb257 lb254 4 := lower_of_forestBT lb268 lb265 lb267
def lb255 : Nat := 0xfce8fce8fce8fce8fce8fce8fce8fce8
lemma lb272 : liftCheck 1 0 lb5 lb255 lb257 lb254 [(VAR 0,3,2)] = true := by decide +kernel
lemma lb271 : Lower lb5 lb255 5 := lift_of lb272 lb270
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q8 : Lower (varsOf 51) 0xeeeeeeeeeeee8888eeeeeeeeeeee8888 5 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (0, 1), (1, 2), (2, 3), (3, 4)]) (roots2 := lb5) (T2 := lb255) _ lb271
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q9 : Lower (varsOf 43) 0xeeeeeeeeaa88aa88eeeeeeeeaa88aa88 5 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (0, 1), (1, 2)]) (roots2 := lb232) (T2 := lb229) _ lb248
  decide +kernel
def lb287 : Nat := 0xeea0eea0eea0eea0eea0eea0eea0eea0
def lb294 : List Nat := [5,7,9,5,7,9,10,14]
def lb289 : List Nat := [4,6,8,1,3,1,2,6]
def lb288 : Nat := fullMask 8
def lb279 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,63,56),(0xcccccccccccccccccccccccccccccccc,210,210),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,155,131),(0xff00ff00ff00ff00ff00ff00ff00ff00,228,4)]
def lb297 : BT Decor := buildWiresBT 2 lb279 lb31
def lb276 : List (List (Nat × Nat)) := [[],[(1,2),(0,3)]]
def lb277 : BT (List (Nat × Nat)) := btOfList 1 lb276
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb291 : goodPairs lb287 lb294 lb289 := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb280 : ∀ x ∈ lb279, faithful lb294 lb289 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb298 : btAll (fun x => faithful lb294 lb289 x ∧ x.1 < 2^128) lb297 := buildWiresBT_faithful lb280
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb278 : btAll (fun sw => swapsValid sw = true ∧ permWord sw lb287 = lb287) lb277 := btAll_ofList (autos_of (by decide +kernel))
def lb292 : BT (Option BoundPool) := buildPoolsBT 1 lb297 lb5 lb28 lb30
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb295 : btAll (fun o => ∀ p, o = some p → Slice lb5 lb287 p.1 p.2) lb28 := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice lb5 lb287 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb293 : btAll (fun o => ∀ c, o = some c → ValidPool lb5 lb287 c) lb292 := buildPoolsBT_sound lb295
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb286 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb287 (3 - 1) xs.toFinset) lb16 := trivial
def lb281 : List NodeSpec := lb78 [([0,1,2,3],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb296 : checkNodesBT lb297 lb287 lb288 lb292 lb277 lb16 3 lb281 = true := by decide +kernel
def lb290 : List NodeSpec := lb281
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb285 : checkNodesBT lb297 lb287 lb288 lb292 lb277 lb16 3 lb290 = true := lb296
def lb283 : BT (List (List Nat)) := buildBucketsBT lb297 lb290
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb284 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb287 3 xs.toFinset) lb283 := buildBucketsBT_sound (by decide) lb291 lb298 lb293 lb278 lb286 lb285
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb282 : Lower lb5 lb287 4 := lower_of_forestBT (essPairs := [(VAR 0,4,5),(VAR 1,8,10),(VAR 2,1,5),(VAR 3,1,9)]) (by decide +kernel) lb284 (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q10 : Lower (varsOf 60) 0xfff0f0f0ff00f000fff0f0f0ff00f000 4 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (1, 2), (2, 3), (3, 4), (1, 2), (2, 3), (0, 1), (1, 2)]) (roots2 := lb5) (T2 := lb287) _ lb282
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q11 : Lower (varsOf 58) 0xffccccccffcc0000ffccccccffcc0000 4 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (2, 3), (3, 4), (1, 2), (2, 3), (0, 1)]) (roots2 := lb5) (T2 := lb287) _ lb282
  decide +kernel
def lb311 : List Nat := [5,6,3,3,6,5]
def lb307 : List Nat := [4,4,1,2,2,1]
def lb300 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,45,36),(0xcccccccccccccccccccccccccccccccc,30,24),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,51,3)]
def lb314 : BT Decor := buildWiresBT 2 lb300 lb31
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb308 : goodPairs lb100 lb311 lb307 := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb301 : ∀ x ∈ lb300, faithful lb311 lb307 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb315 : btAll (fun x => faithful lb311 lb307 x ∧ x.1 < 2^128) lb314 := buildWiresBT_faithful lb301
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb299 : btAll (fun sw => swapsValid sw = true ∧ permWord sw lb100 = lb100) lb203 := btAll_ofList (autos_of (by decide +kernel))
def lb309 : BT (Option BoundPool) := buildPoolsBT 1 lb314 lb110 lb28 lb30
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb312 : btAll (fun o => ∀ p, o = some p → Slice lb110 lb100 p.1 p.2) lb28 := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice lb110 lb100 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb310 : btAll (fun o => ∀ c, o = some c → ValidPool lb110 lb100 c) lb309 := buildPoolsBT_sound lb312
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb306 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb100 (3 - 1) xs.toFinset) lb16 := trivial
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb313 : checkNodesBT lb314 lb100 lb19 lb309 lb203 lb16 3 lb207 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb305 : checkNodesBT lb314 lb100 lb19 lb309 lb203 lb16 3 lb215 = true := lb313
def lb303 : BT (List (List Nat)) := buildBucketsBT lb314 lb215
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb304 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb100 3 xs.toFinset) lb303 := buildBucketsBT_sound (by decide) lb308 lb315 lb310 lb299 lb306 lb305
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb302 : Lower lb110 lb100 4 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5)]) (by decide +kernel) lb304 (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q12 : Lower (varsOf 38) 0xfcfcfcfcc0c0c0c0fcfcfcfcc0c0c0c0 4 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (1, 2), (0, 1)]) (roots2 := lb110) (T2 := lb100) _ lb302
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q13 : Lower (varsOf 37) 0xfafafafaa0a0a0a0fafafafaa0a0a0a0 4 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (1, 2)]) (roots2 := lb110) (T2 := lb100) _ lb302
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q14 : Lower (varsOf 35) 0xeeeeeeee88888888eeeeeeee88888888 4 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5)]) (roots2 := lb110) (T2 := lb100) _ lb302
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q15 : Lower (varsOf 25) 0xffaaaa00ffaaaa00ffaaaa00ffaaaa00 4 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (1, 2), (2, 3)]) (roots2 := lb110) (T2 := lb100) _ lb302
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q16 : Lower (varsOf 19) 0xeeee8888eeee8888eeee8888eeee8888 4 := by
  apply carry_of (swaps := [(2, 3), (3, 4)]) (roots2 := lb110) (T2 := lb100) _ lb302
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q17 : Lower (varsOf 13) 0xfaa0faa0faa0faa0faa0faa0faa0faa0 4 := by
  apply carry_of (swaps := [(2, 3), (1, 2)]) (roots2 := lb110) (T2 := lb100) _ lb302
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q18 : Lower (varsOf 7) 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8 4 := by
  apply carry_of (swaps := []) (roots2 := lb110) (T2 := lb100) _ lb302
  decide +kernel
def s0NR : List Nat := varsOf 63
def s0NG : Nat := 0xfffefefeffeefae8fffefefeffeefae8
def s0NPos : List Nat := [3,3,3,5,5,6,6,6,9,9,9,9,9,11,12,12,12,14,17,17,17,18,18,18,21,22,24,24,24,24,24,28,33,33,33,33,33,34,34,34,34,35,36,36,36,41,42,42,44,49,50,52,52,56,56]
def s0NNeg : List Nat := [0,1,2,1,4,1,2,4,0,1,8,10,40,10,4,8,10,10,1,20,48,2,16,48,20,20,8,10,16,20,48,20,0,1,32,40,48,0,1,2,32,1,4,32,40,40,10,40,40,48,48,20,48,40,48]
def s0NMask : Nat := fullMask 55
def s0NBase : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x2221f011c3f1f,0x2420004022a),(0xcccccccccccccccccccccccccccccccc,0x4c3e002e220e7,0x408008232844),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x191c008303c0f8,0x80400a3084090),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x61e000fc03ff00,0x21f0080c03bc00),(0xffff0000ffff0000ffff0000ffff0000,0x7e0000fffc0000,0x5e0010f3d80000),(0xffffffff00000000ffffffff00000000,0x7fffff00000000,0x77b91c40901000)]
def s0NSteps : List (Nat × Nat × Nat) := [(1,0,1),(1,0,2),(1,1,2),(1,1,3),(1,2,4),(1,2,9),(2,0,2),(1,0,5),(1,1,5),(3,1,13),(1,9,5),(2,0,5),(1,0,10),(2,0,10),(1,6,2),(2,20,5),(2,6,2),(1,6,5),(3,0,11),(1,19,2),(1,6,10),(3,2,26),(2,6,10),(1,28,2),(3,0,16),(2,6,5),(1,1,10),(3,3,26),(2,26,5),(2,0,1),(1,35,2),(1,35,5),(1,35,10),(3,3,38),(0,0,5),(1,40,1),(1,40,2),(3,1,5),(1,9,13),(3,1,44),(3,2,44),(3,4,44),(3,9,13),(1,48,1),(1,2,5),(3,2,5),(1,2,13),(3,2,13),(1,17,1),(1,17,2),(1,17,9),(2,56,4),(3,0,5),(1,0,9),(3,2,59),(2,60,4),(2,59,4),(2,0,9),(1,63,2),(1,63,8),(2,59,5),(1,2,59),(1,62,2),(1,63,1),(1,63,5),(3,1,70),(1,43,0),(1,9,10)]
def s0NW : BT Decor := buildWiresBT 7 s0NBase s0NSteps
def s0NAutoList : List (List (Nat × Nat)) := [[],[(1,2),(3,4)]]
def s0NAutos : BT (List (Nat × Nat)) := btOfList 1 s0NAutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NPairs : goodPairs s0NG s0NPos s0NNeg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBaseOk : ∀ x ∈ s0NBase, faithful s0NPos s0NNeg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NWOk : btAll (fun x => faithful s0NPos s0NNeg x ∧ x.1 < 2^128) s0NW := buildWiresBT_faithful s0NBaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NAutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw s0NG = s0NG) s0NAutos := btAll_ofList (autos_of (by decide +kernel))
def s0NSliceList : List (Option (Nat × Nat)) := [some (subcubeFast 2 0,7),some (subcubeFast 24 0,7),some (0xf000f00000f000f0f000f00000f000f,7),some (0x33330000000033333333000000003333,7),some (subcubeFast 1 0,6),some (subcubeFast 6 0,5),some (subcubeFast 10 0,5),some (subcubeFast 12 0,5),some (subcubeFast 20 0,5),some (subcubeFast 3 0,4),some (subcubeFast 5 0,4),some (subcubeFast 25 0,4),some (subcubeFast 26 0,4),some (subcubeFast 28 0,4),some (subcubeFast 38 0,4),some (subcubeFast 44 0,4),some (subcubeFast 50 0,4),some (subcubeFast 56 0,4)]
def s0NSlices : BT (Option (Nat × Nat)) := btOfList 5 s0NSliceList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice0 : Slice s0NR s0NG (subcubeFast 2 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 61) (qGoal := 0xfffafafaffaafaa0fffafafaffaafaa0) (by decide +kernel) q1
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice1 : Slice s0NR s0NG (subcubeFast 24 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 39) (qGoal := 0xfefefefee8e8e8e8fefefefee8e8e8e8) (by decide +kernel) q2
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice2 : Slice s0NR s0NG 0xf000f00000f000f0f000f00000f000f 7 := mappedSlice (f := identifyRow 4 0 3 5) (R := varsOf 27) (G := 0xffeeee88ffeeee88ffeeee88ffeeee88) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) q3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice3 : Slice s0NR s0NG 0x33330000000033333333000000003333 7 := mappedSlice (f := identifyRow 2 0 4 5) (R := varsOf 29) (G := 0xfffafaa0fffafaa0fffafaa0fffafaa0) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) q4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice4 : Slice s0NR s0NG (subcubeFast 1 0) 6 := slice_fast_direct (zDead := 0) (qRoots := varsOf 62) (qGoal := 0xfffcfcfcffccf0c0fffcfcfcffccf0c0) (by decide +kernel) q5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice5 : Slice s0NR s0NG (subcubeFast 6 0) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 57) (qGoal := 0xffaaaaaaffaaaa00ffaaaaaaffaaaa00) (by decide +kernel) q6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice6 : Slice s0NR s0NG (subcubeFast 10 0) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 53) (qGoal := 0xfafafafaaaaaa0a0fafafafaaaaaa0a0) (by decide +kernel) q7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice7 : Slice s0NR s0NG (subcubeFast 12 0) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 51) (qGoal := 0xeeeeeeeeeeee8888eeeeeeeeeeee8888) (by decide +kernel) q8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice8 : Slice s0NR s0NG (subcubeFast 20 0) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 43) (qGoal := 0xeeeeeeeeaa88aa88eeeeeeeeaa88aa88) (by decide +kernel) q9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice9 : Slice s0NR s0NG (subcubeFast 3 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 60) (qGoal := 0xfff0f0f0ff00f000fff0f0f0ff00f000) (by decide +kernel) q10
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice10 : Slice s0NR s0NG (subcubeFast 5 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 58) (qGoal := 0xffccccccffcc0000ffccccccffcc0000) (by decide +kernel) q11
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice11 : Slice s0NR s0NG (subcubeFast 25 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 38) (qGoal := 0xfcfcfcfcc0c0c0c0fcfcfcfcc0c0c0c0) (by decide +kernel) q12
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice12 : Slice s0NR s0NG (subcubeFast 26 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 37) (qGoal := 0xfafafafaa0a0a0a0fafafafaa0a0a0a0) (by decide +kernel) q13
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice13 : Slice s0NR s0NG (subcubeFast 28 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 35) (qGoal := 0xeeeeeeee88888888eeeeeeee88888888) (by decide +kernel) q14
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice14 : Slice s0NR s0NG (subcubeFast 38 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 25) (qGoal := 0xffaaaa00ffaaaa00ffaaaa00ffaaaa00) (by decide +kernel) q15
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice15 : Slice s0NR s0NG (subcubeFast 44 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 19) (qGoal := 0xeeee8888eeee8888eeee8888eeee8888) (by decide +kernel) q16
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice16 : Slice s0NR s0NG (subcubeFast 50 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 13) (qGoal := 0xfaa0faa0faa0faa0faa0faa0faa0faa0) (by decide +kernel) q17
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice17 : Slice s0NR s0NG (subcubeFast 56 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 7) (qGoal := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8) (by decide +kernel) q18
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlicesOk : btAll (fun o => ∀ p, o = some p → Slice s0NR s0NG p.1 p.2) s0NSlices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice s0NR s0NG p.1 p.2) (forall_cons (fun _ h => by cases h; exact s0NSlice0) (forall_cons (fun _ h => by cases h; exact s0NSlice1) (forall_cons (fun _ h => by cases h; exact s0NSlice2) (forall_cons (fun _ h => by cases h; exact s0NSlice3) (forall_cons (fun _ h => by cases h; exact s0NSlice4) (forall_cons (fun _ h => by cases h; exact s0NSlice5) (forall_cons (fun _ h => by cases h; exact s0NSlice6) (forall_cons (fun _ h => by cases h; exact s0NSlice7) (forall_cons (fun _ h => by cases h; exact s0NSlice8) (forall_cons (fun _ h => by cases h; exact s0NSlice9) (forall_cons (fun _ h => by cases h; exact s0NSlice10) (forall_cons (fun _ h => by cases h; exact s0NSlice11) (forall_cons (fun _ h => by cases h; exact s0NSlice12) (forall_cons (fun _ h => by cases h; exact s0NSlice13) (forall_cons (fun _ h => by cases h; exact s0NSlice14) (forall_cons (fun _ h => by cases h; exact s0NSlice15) (forall_cons (fun _ h => by cases h; exact s0NSlice16) (forall_cons (fun _ h => by cases h; exact s0NSlice17) (fun _ h => (List.not_mem_nil h).elim)))))))))))))))))))
def s0NEmpty : BT (List (List Nat)) := BT.empty
lemma s0NEmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible s0NG (4 - 1) xs.toFinset) s0NEmpty := trivial
def s0NBlock4_0Specs : List PoolSpec := [(14,[])]
def s0NBlock4_0Pools : BT (Option BoundPool) := buildPoolsBT 1 s0NW s0NR s0NSlices s0NBlock4_0Specs
def s0NBlock4_0 : List NodeSpec := [([21,0,20,9,10],[0],[]),([61,0,8,9,5],[],[]),([27,0,9,10,5],[],[]),([24,6,9,10,5],[],[]),([0,29,9,10,5],[0],[]),([0,65,9,10,5],[0],[]),([6,25,9,10,5],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock4_0Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock4_0Pools s0NAutos s0NEmpty 4 s0NBlock4_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock4_0Mem : ∀ ns ∈ s0NBlock4_0, Impossible s0NG 4 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NEmptyOk s0NBlock4_0Ok
def s0NNodes4 : List NodeSpec := s0NBlock4_0
def s0NBucket4 : BT (List (List Nat)) := buildBucketsBT s0NW s0NNodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s0NG 4 xs.toFinset) s0NBucket4 := buildBucketsBT_of_mem s0NBlock4_0Mem
def s0NBlock5_0Specs : List PoolSpec := [(14,[])]
def s0NBlock5_0Pools : BT (Option BoundPool) := buildPoolsBT 1 s0NW s0NR s0NSlices s0NBlock5_0Specs
def s0NBlock5_0 : List NodeSpec := [([21,0,6,2,9,4],[],[]),([21,0,2,20,9,4],[0],[0]),([66,43,0,2,9,4],[],[]),([34,0,1,2,3,10],[],[]),([19,6,2,9,10,5],[],[0]),([19,6,8,3,10,5],[],[]),([28,0,2,9,10,5],[],[0]),([61,0,1,2,9,5],[],[0]),([57,0,1,2,9,5],[],[]),([62,43,0,2,9,5],[],[]),([62,0,2,8,9,5],[],[0]),([47,0,1,2,9,5],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock5_0Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock5_0Pools s0NAutos s0NBucket4 5 s0NBlock5_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock5_0Mem : ∀ ns ∈ s0NBlock5_0, Impossible s0NG 5 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket4Ok s0NBlock5_0Ok
def s0NBlock5_1Specs : List PoolSpec := [(5,[]),(7,[])]
def s0NBlock5_1Pools : BT (Option BoundPool) := buildPoolsBT 1 s0NW s0NR s0NSlices s0NBlock5_1Specs
def s0NBlock5_1 : List NodeSpec := [([63,0,8,9,10,5],[0],[0]),([39,0,1,2,10,5],[],[]),([33,0,1,2,10,5],[],[]),([60,0,8,9,4,5],[],[0]),([27,0,1,3,10,5],[],[0]),([46,0,1,9,4,5],[],[]),([43,0,2,9,4,70],[],[]),([71,0,2,9,4,5],[],[]),([45,0,2,9,4,5],[],[]),([24,0,1,9,10,5],[1],[0]),([24,6,2,9,4,5],[],[0]),([30,6,2,9,4,5],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock5_1Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock5_1Pools s0NAutos s0NBucket4 5 s0NBlock5_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock5_1Mem : ∀ ns ∈ s0NBlock5_1, Impossible s0NG 5 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket4Ok s0NBlock5_1Ok
def s0NBlock5_2Specs : List PoolSpec := [(5,[]),(14,[]),(7,[]),(12,[]),(15,[]),(1,[])]
def s0NBlock5_2Pools : BT (Option BoundPool) := buildPoolsBT 3 s0NW s0NR s0NSlices s0NBlock5_2Specs
def s0NBlock5_2 : List NodeSpec := [([0,1,2,68,9,5],[],[]),([0,1,29,3,10,5],[1],[0]),([0,1,64,9,10,5],[],[0]),([0,1,59,11,10,5],[],[]),([0,69,2,9,10,5],[],[0,1]),([0,49,2,9,4,5],[5],[]),([0,6,7,9,10,5],[0],[]),([0,6,20,9,10,5],[1],[]),([0,6,9,11,10,5],[2,3],[0]),([0,2,65,9,4,5],[1],[0]),([0,2,9,10,26,5],[4],[0]),([0,64,8,9,4,5],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock5_2Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock5_2Pools s0NAutos s0NBucket4 5 s0NBlock5_2 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock5_2Mem : ∀ ns ∈ s0NBlock5_2, Impossible s0NG 5 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket4Ok s0NBlock5_2Ok
def s0NBlock5_3Specs : List PoolSpec := [(5,[]),(9,[]),(14,[]),(6,[]),(11,[]),(12,[]),(13,[])]
def s0NBlock5_3Pools : BT (Option BoundPool) := buildPoolsBT 3 s0NW s0NR s0NSlices s0NBlock5_3Specs
def s0NBlock5_3 : List NodeSpec := [([0,8,9,59,10,5],[6],[0]),([0,20,9,10,5],[2],[0]),([1,6,25,3,10,5],[],[0]),([6,2,3,18,32,5],[],[]),([6,2,9,4,13,16],[3],[]),([6,2,9,10,18,5],[4,5],[]),([6,7,9,11,4,5],[1],[]),([6,7,9,10,5],[],[]),([6,8,3,10,18,5],[0],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock5_3Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock5_3Pools s0NAutos s0NBucket4 5 s0NBlock5_3 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock5_3Mem : ∀ ns ∈ s0NBlock5_3, Impossible s0NG 5 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket4Ok s0NBlock5_3Ok
def s0NNodes5 : List NodeSpec := s0NBlock5_0 ++ s0NBlock5_1 ++ s0NBlock5_2 ++ s0NBlock5_3
def s0NBucket5 : BT (List (List Nat)) := buildBucketsBT s0NW s0NNodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s0NG 5 xs.toFinset) s0NBucket5 := buildBucketsBT_of_mem (forall_append (forall_append (forall_append s0NBlock5_0Mem s0NBlock5_1Mem) s0NBlock5_2Mem) s0NBlock5_3Mem)
def s0NBlock6_0Specs : List PoolSpec := [(5,[]),(14,[]),(6,[]),(11,[]),(12,[]),(0,[]),(1,[(1,0,9)])]
def s0NBlock6_0Pools : BT (Option BoundPool) := buildPoolsBT 3 s0NW s0NR s0NSlices s0NBlock6_0Specs
def s0NBlock6_0 : List NodeSpec := [([17,6,2,9,4,5],[1,2,3],[]),([21,0,1,6,2,3,4],[],[0]),([21,0,1,2,20,3,4],[1],[0,1]),([21,0,1,2,3,4],[1],[]),([66,0,1,2,9,4,5],[3,5],[0]),([19,1,6,2,3,10,5],[],[0]),([28,0,1,2,3,10,5],[],[0]),([62,0,1,2,9,59,5],[3],[]),([62,0,1,2,9,5],[3,4,6],[0]),([63,43,0,2,9,4,5],[1],[0]),([63,0,1,2,9,10,5],[0],[0,1]),([63,0,2,8,9,4,5],[0],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_0Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock6_0Pools s0NAutos s0NBucket5 6 s0NBlock6_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_0Mem : ∀ ns ∈ s0NBlock6_0, Impossible s0NG 6 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket5Ok s0NBlock6_0Ok
def s0NBlock6_1Specs : List PoolSpec := [(4,[]),(9,[]),(14,[]),(6,[]),(11,[]),(16,[]),(1,[(1,0,1),(2,6,2)]),(0,[]),(1,[(1,0,5),(3,1,13)])]
def s0NBlock6_1Pools : BT (Option BoundPool) := buildPoolsBT 4 s0NW s0NR s0NSlices s0NBlock6_1Specs
def s0NBlock6_1 : List NodeSpec := [([48,0,1,2,9,4,5],[],[0]),([12,6,2,9,4,5],[2,3,4],[]),([22,0,2,9,4,5],[1,2,3,6],[]),([60,0,1,2,9,4,5],[4,7],[0]),([35,1,2,3,10,18,5],[4],[]),([43,0,2,9,59,4,5],[4,5],[0]),([43,0,2,9,4,13],[1,2,3,5],[]),([15,0,6,2,3,4,5],[0],[]),([15,0,2,3,4,5,23],[0],[]),([15,0,2,3,4,13,14],[2],[]),([15,0,2,9,4,5],[2,8],[]),([15,0,2,9,4,5,13],[2],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_1Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock6_1Pools s0NAutos s0NBucket5 6 s0NBlock6_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_1Mem : ∀ ns ∈ s0NBlock6_1, Impossible s0NG 6 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket5Ok s0NBlock6_1Ok
def s0NBlock6_2Specs : List PoolSpec := [(4,[]),(10,[]),(14,[]),(6,[]),(11,[]),(16,[]),(7,[]),(15,[]),(0,[]),(13,[])]
def s0NBlock6_2Pools : BT (Option BoundPool) := buildPoolsBT 4 s0NW s0NR s0NSlices s0NBlock6_2Specs
def s0NBlock6_2 : List NodeSpec := [([15,6,2,3,4,5,13],[0],[]),([24,0,1,2,9,4,5],[6,8],[0]),([30,0,1,2,9,4,5],[7,8],[0]),([0,72,2,9,4,5],[2,3,5],[]),([0,1,6,20,3,10,5],[1,2],[0]),([0,1,2,64,9,4,5],[8],[0]),([0,1,2,3,10,38,5],[4],[0]),([0,1,2,3,10,26,5],[7],[0]),([0,1,2,9,56,4,5],[4],[0]),([0,1,2,9,59,10,5],[4,9],[0,1]),([0,1,2,9,4,5,70],[8],[0]),([0,1,2,9,4,5,44],[9],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_2Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock6_2Pools s0NAutos s0NBucket5 6 s0NBlock6_2 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_2Mem : ∀ ns ∈ s0NBlock6_2, Impossible s0NG 6 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket5Ok s0NBlock6_2Ok
def s0NBlock6_3Specs : List PoolSpec := [(4,[]),(5,[]),(9,[]),(14,[]),(6,[]),(11,[]),(8,[]),(12,[]),(15,[]),(13,[]),(1,[(1,2,9)]),(1,[(1,9,10)])]
def s0NBlock6_3Pools : BT (Option BoundPool) := buildPoolsBT 4 s0NW s0NR s0NSlices s0NBlock6_3Specs
def s0NBlock6_3 : List NodeSpec := [([0,1,2,9,4,13,16],[4,8],[0]),([0,1,2,9,10,73,5],[7,9,11],[]),([0,1,2,59,11,4,5],[1],[0,1]),([0,1,2,59,4,5,16],[2,7],[]),([0,1,36,3,10,5],[3,5],[]),([0,1,9,11,10,5],[3,7,8,9,10],[0,1]),([0,54,2,9,4,5],[3,5],[]),([0,69,2,9,4,5],[2,3,4,5],[0,1]),([0,6,2,7,9,4,5],[1,2],[0]),([0,6,2,20,9,4,5],[2,3],[0]),([0,6,2,3,4,13,14],[0],[]),([0,6,2,3,10,32,5],[6,7],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_3Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock6_3Pools s0NAutos s0NBucket5 6 s0NBlock6_3 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_3Mem : ∀ ns ∈ s0NBlock6_3, Impossible s0NG 6 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket5Ok s0NBlock6_3Ok
def s0NBlock6_4Specs : List PoolSpec := [(4,[]),(5,[]),(9,[]),(14,[]),(1,[(1,0,1),(1,0,2)]),(6,[]),(11,[]),(1,[(1,0,1),(1,1,2)]),(8,[]),(1,[(1,0,1),(1,6,2)]),(7,[]),(12,[]),(15,[]),(13,[]),(1,[(1,1,2)])]
def s0NBlock6_4Pools : BT (Option BoundPool) := buildPoolsBT 4 s0NW s0NR s0NSlices s0NBlock6_4Specs
def s0NBlock6_4 : List NodeSpec := [([0,6,2,9,11,4,5],[2,5,10],[0]),([0,6,2,9,4,5,13],[2,3],[]),([0,6,2,9,4,5,23],[3],[]),([0,6,2,9,4,5,16],[2,5,12],[0]),([0,6,2,9,10,5],[3,11],[0]),([0,6,7,8,3,4,5],[0],[]),([0,6,8,3,10,5],[3,7,8],[0]),([0,2,8,9,59,4,5],[5,6,13],[0,1]),([0,2,20,9,4,5],[2,3,9],[0]),([0,8,9,10,5],[3,11,13,14],[0,1]),([1,6,2,3,10,18,5],[1,6],[0]),([6,2,7,9,4,5],[2,3,4,5],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_4Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock6_4Pools s0NAutos s0NBucket5 6 s0NBlock6_4 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_4Mem : ∀ ns ∈ s0NBlock6_4, Impossible s0NG 6 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket5Ok s0NBlock6_4Ok
def s0NBlock6_5Specs : List PoolSpec := [(4,[]),(9,[]),(14,[]),(1,[(1,0,1),(1,0,2),(1,1,2)]),(6,[]),(16,[]),(1,[(1,0,1),(1,0,5),(1,1,5)])]
def s0NBlock6_5Pools : BT (Option BoundPool) := buildPoolsBT 3 s0NW s0NR s0NSlices s0NBlock6_5Specs
def s0NBlock6_5 : List NodeSpec := [([6,2,3,4,13,14],[0,2,6],[]),([6,2,9,4,5,13],[1,2,4,5],[0]),([6,7,8,3,4,5],[0,2,3],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_5Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock6_5Pools s0NAutos s0NBucket5 6 s0NBlock6_5 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock6_5Mem : ∀ ns ∈ s0NBlock6_5, Impossible s0NG 6 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket5Ok s0NBlock6_5Ok
def s0NNodes6 : List NodeSpec := s0NBlock6_0 ++ s0NBlock6_1 ++ s0NBlock6_2 ++ s0NBlock6_3 ++ s0NBlock6_4 ++ s0NBlock6_5
def s0NBucket6 : BT (List (List Nat)) := buildBucketsBT s0NW s0NNodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s0NG 6 xs.toFinset) s0NBucket6 := buildBucketsBT_of_mem (forall_append (forall_append (forall_append (forall_append (forall_append s0NBlock6_0Mem s0NBlock6_1Mem) s0NBlock6_2Mem) s0NBlock6_3Mem) s0NBlock6_4Mem) s0NBlock6_5Mem)
def s0NBlock7_0Specs : List PoolSpec := [(4,[]),(9,[]),(14,[]),(6,[]),(11,[]),(8,[]),(1,[(1,0,1),(2,6,2)]),(1,[(1,0,1),(2,6,5)]),(1,[(1,0,5),(3,1,13)]),(17,[]),(1,[(3,1,5)])]
def s0NBlock7_0Pools : BT (Option BoundPool) := buildPoolsBT 4 s0NW s0NR s0NSlices s0NBlock7_0Specs
def s0NBlock7_0 : List NodeSpec := [([17,0,1,2,9,4,5],[2,3,4],[0]),([17,1,6,2,3,4,5],[2,4],[0]),([31,0,1,2,3,4,5],[1,2,7],[]),([63,0,1,2,9,4,5],[2,3,4],[0,1]),([12,1,6,2,3,4,5],[2,4],[0]),([22,0,1,2,3,4,5],[1,2,6],[0]),([35,0,1,2,3,10,5],[2,4,5],[0,1]),([35,1,2,3,4,5,13],[2,4],[]),([43,0,1,2,3,4,13],[1,2,9],[0]),([43,0,2,9,4,5],[2,3,10],[0]),([15,0,1,2,3,4,5],[2,8],[0]),([15,0,1,2,3,4,5,13],[0,2],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_0Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock7_0Pools s0NAutos s0NBucket6 7 s0NBlock7_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_0Mem : ∀ ns ∈ s0NBlock7_0, Impossible s0NG 7 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket6Ok s0NBlock7_0Ok
def s0NBlock7_1Specs : List PoolSpec := [(4,[]),(5,[]),(9,[]),(10,[]),(14,[]),(11,[]),(8,[]),(1,[(1,0,1),(1,6,2)]),(1,[(1,0,1)]),(17,[])]
def s0NBlock7_1Pools : BT (Option BoundPool) := buildPoolsBT 4 s0NW s0NR s0NSlices s0NBlock7_1Specs
def s0NBlock7_1 : List NodeSpec := [([0,72,1,2,3,4,5],[4,9],[0]),([0,1,54,2,3,4,5],[4,5],[0]),([0,1,6,2,7,3,4,5],[0,1,2,3],[0,1]),([0,1,6,2,20,3,4,5],[2,3,4],[0]),([0,1,6,2,3,4,5,13],[0,2,4],[0]),([0,1,6,2,3,4,5,23],[2,4],[0]),([0,1,6,2,3,10,5],[3,4,6,8],[0,1]),([0,1,2,36,3,4,5],[4,5],[0]),([0,1,2,20,3,4,5],[2,3,4,7],[0,1]),([0,1,2,3,4,5,37],[4,5],[]),([0,1,2,3,4,5,13],[4,5],[]),([0,1,2,3,4,5,13,23],[2,4],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_1Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock7_1Pools s0NAutos s0NBucket6 7 s0NBlock7_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_1Mem : ∀ ns ∈ s0NBlock7_1, Impossible s0NG 7 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket6Ok s0NBlock7_1Ok
def s0NBlock7_2Specs : List PoolSpec := [(4,[]),(9,[]),(14,[]),(6,[]),(11,[]),(1,[(1,0,1),(1,1,2)]),(7,[]),(12,[]),(15,[]),(1,[(1,0,1)]),(1,[(1,0,1),(1,1,5)]),(1,[(1,0,1),(1,6,5)]),(13,[]),(1,[(1,0,5)]),(1,[(1,0,5),(1,1,5)]),(1,[(1,1,2)]),(1,[(1,0,9)])]
def s0NBlock7_2Pools : BT (Option BoundPool) := buildPoolsBT 5 s0NW s0NR s0NSlices s0NBlock7_2Specs
def s0NBlock7_2 : List NodeSpec := [([0,1,2,3,4,5,23],[1,2,11],[0]),([0,1,2,3,4,13,14],[0,2,14],[0]),([0,1,2,9,59,4,5],[2,4,7,16],[0,1]),([0,1,2,9,11,4,5],[1,2,6,7],[0,1]),([0,1,2,9,4,5,13],[1,2,3,13],[0]),([0,1,2,9,4,5,16],[1,2,7,8],[0]),([0,1,2,9,10,5],[2,7,12],[0,1]),([0,41,2,3,4,5],[2,4],[]),([0,6,2,8,3,4,5],[1,2,5],[0]),([0,6,2,3,4,5,14],[1,2,10],[0]),([0,6,2,9,4,5],[1,2,3,9],[0]),([0,2,8,9,4,5],[2,3,15],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_2Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock7_2Pools s0NAutos s0NBucket6 7 s0NBlock7_2 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_2Mem : ∀ ns ∈ s0NBlock7_2, Impossible s0NG 7 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket6Ok s0NBlock7_2Ok
def s0NBlock7_3Specs : List PoolSpec := [(4,[]),(9,[]),(10,[]),(14,[]),(1,[(1,0,1),(1,0,2)]),(1,[(1,0,1),(1,0,5)])]
def s0NBlock7_3Pools : BT (Option BoundPool) := buildPoolsBT 3 s0NW s0NR s0NSlices s0NBlock7_3Specs
def s0NBlock7_3 : List NodeSpec := [([1,6,2,7,3,4,5],[0,1,2,3,4],[0,1]),([1,6,2,3,4,5,13],[0,1,3,5],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_3Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock7_3Pools s0NAutos s0NBucket6 7 s0NBlock7_3 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock7_3Mem : ∀ ns ∈ s0NBlock7_3, Impossible s0NG 7 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket6Ok s0NBlock7_3Ok
def s0NNodes7 : List NodeSpec := s0NBlock7_0 ++ s0NBlock7_1 ++ s0NBlock7_2 ++ s0NBlock7_3
def s0NBucket7 : BT (List (List Nat)) := buildBucketsBT s0NW s0NNodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s0NG 7 xs.toFinset) s0NBucket7 := buildBucketsBT_of_mem (forall_append (forall_append (forall_append s0NBlock7_0Mem s0NBlock7_1Mem) s0NBlock7_2Mem) s0NBlock7_3Mem)
def s0NBlock8_0Specs : List PoolSpec := [(4,[]),(9,[]),(14,[]),(6,[]),(11,[]),(1,[(1,0,1)]),(0,[]),(1,[]),(2,[]),(3,[]),(1,[(1,0,5)]),(17,[]),(1,[(1,1,2)]),(1,[(1,1,5)])]
def s0NBlock8_0Pools : BT (Option BoundPool) := buildPoolsBT 4 s0NW s0NR s0NSlices s0NBlock8_0Specs
def s0NBlock8_0 : List NodeSpec := [([17,0,1,2,3,4,5],[2,4],[0,1]),([35,0,1,2,3,4,5],[2,4,6],[0,1]),([43,0,1,2,3,4,5],[0,2,11],[0]),([58,0,1,2,3,4,5],[0,2,11],[0]),([40,0,1,2,3,4,5],[2,4,7,8,9],[0,1]),([0,1,6,2,3,4,5],[0,1,2,5,6],[0]),([0,1,2,8,3,4,5],[0,2,12],[0,1]),([0,1,2,3,4,5,13],[0,2,10],[0,1]),([0,1,2,3,4,5,14],[0,2,13],[0]),([0,1,2,9,4,5],[2,3,6,7],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock8_0Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock8_0Pools s0NAutos s0NBucket7 8 s0NBlock8_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock8_0Mem : ∀ ns ∈ s0NBlock8_0, Impossible s0NG 8 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket7Ok s0NBlock8_0Ok
def s0NNodes8 : List NodeSpec := s0NBlock8_0
def s0NBucket8 : BT (List (List Nat)) := buildBucketsBT s0NW s0NNodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s0NG 8 xs.toFinset) s0NBucket8 := buildBucketsBT_of_mem s0NBlock8_0Mem
def s0NBlock9_0Specs : List PoolSpec := [(0,[]),(1,[]),(2,[])]
def s0NBlock9_0Pools : BT (Option BoundPool) := buildPoolsBT 2 s0NW s0NR s0NSlices s0NBlock9_0Specs
def s0NBlock9_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock9_0Ok : checkNodesBT s0NW s0NG s0NMask s0NBlock9_0Pools s0NAutos s0NBucket8 9 s0NBlock9_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBlock9_0Mem : ∀ ns ∈ s0NBlock9_0, Impossible s0NG 9 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NBucket8Ok s0NBlock9_0Ok
def s0NNodes9 : List NodeSpec := s0NBlock9_0
def s0NBucket9 : BT (List (List Nat)) := buildBucketsBT s0NW s0NNodes9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBucket9Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s0NG 9 xs.toFinset) s0NBucket9 := buildBucketsBT_of_mem s0NBlock9_0Mem
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBound : Lower s0NR s0NG 10 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 3,1,9),(VAR 4,1,17),(VAR 5,1,33)]) (by decide +kernel) s0NBucket9Ok (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q0 : Lower (varsOf 63) 0xffffffeaffecfee8ffffffeaffecfee8 10 := by
  apply carry_of (swaps := [(4, 5), (3, 4), (0, 1), (1, 2), (2, 3)]) (roots2 := s0NR) (T2 := s0NG) _ s0NBound
  decide +kernel
lemma lb428 : carryOK [(1,2),(1,5),(2,4),(1,3)] lb257 lb254 lb109 lb99 = true := by decide +kernel
lemma lb427 : Lower lb257 lb254 4 := carry_of lb428 lb167
lemma lb408 : carryOK [(2,4),(1,2),(1,3)] lb231 lb228 lb109 lb99 = true := by decide +kernel
lemma lb407 : Lower lb231 lb228 4 := carry_of lb408 lb167
def lb316 : Nat := 0xfff0f000fff0f000fff0f000fff0f000
def lb330 : List Nat := varsOf 28
lemma lb410 : carryOK [(2,5),(2,4),(2,3)] lb330 lb316 lb109 lb99 = true := by decide +kernel
lemma lb409 : Lower lb330 lb316 4 := carry_of lb410 lb167
def lb317 : Nat := 0xfff0fff0f000f000fff0fff0f000f000
def lb331 : List Nat := varsOf 44
lemma lb412 : carryOK [(2,4),(2,3)] lb331 lb317 lb109 lb99 = true := by decide +kernel
lemma lb411 : Lower lb331 lb317 4 := carry_of lb412 lb167
def lb318 : Nat := 0xffffcccccccc0000ffffcccccccc0000
def lb332 : List Nat := varsOf 50
lemma lb414 : carryOK [(1,2),(1,3)] lb332 lb318 lb109 lb99 = true := by decide +kernel
lemma lb413 : Lower lb332 lb318 4 := carry_of lb414 lb167
def lb319 : Nat := 0xfffff0f0f0f00000fffff0f0f0f00000
def lb333 : List Nat := varsOf 52
lemma lb416 : carryOK [(2,3)] lb333 lb319 lb109 lb99 = true := by decide +kernel
lemma lb415 : Lower lb333 lb319 4 := carry_of lb416 lb167
def lb320 : Nat := 0xfff0f000f0000000fff0f000f0000000
def lb334 : List Nat := varsOf 60
def lb442 : List Nat := [28,28,28,44,44,44,52,52,52,56,56,56,28,28,28,44,44,44,52,52,52,56,56,56]
def lb429 : List Nat := [24,20,12,40,36,12,48,36,20,48,40,24,36,40,48,20,24,48,12,24,40,12,20,36]
def lb347 : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x1ff1ff,0xe491b6),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xe3fe3f,0x3d2c2d),(0xffff0000ffff0000ffff0000ffff0000,0xfc7fc7,0x4bcb43),(0xffffffff00000000ffffffff00000000,0xff8ff8,0x9276d8)]
def lb485 : List (Nat × Nat × Nat) := [(0,0,1),(0,0,2),(3,4,2),(0,4,2),(0,1,2),(3,7,3)]
def lb339 : Array Decor := buildWires lb347 lb485
def lb343 : Array (List (Nat × Nat)) := #[[],[(4,5)],[(2,3)],[(4,5),(2,3)],[(3,4)],[(3,5),(3,4)],[(2,3),(2,4)],[(3,5),(2,3),(2,4)],[(3,5),(2,4)]]
def lb479 : List (Nat × Nat) := [(subcube 0 16,4),(subcube 0 4,4),(subcube 0 8,4),(subcube 0 32,4)]
def lb481 : Array (Nat × Nat) := lb479.toArray
def lb326 : Array (Option BoundPool) := buildPools lb339 lb334 lb481 lb71
lemma lb405 : goodPairs lb320 lb442 lb429 := goodPairs_of (by decide +kernel)
lemma lb348 : ∀ x ∈ lb347, faithful lb442 lb429 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma lb340 : ∀ x ∈ lb339.toList, faithful lb442 lb429 x ∧ x.1 < 2^128 := buildWires_faithful lb348
lemma lb344 : ∀ sw ∈ lb343.toList, swapsValid sw = true ∧ permWord sw lb320 = lb320 := autos_of (by decide +kernel)
lemma lb446 : sliceDirectCheck 0 16 0 lb334 lb320 lb331 lb317 = true := by decide +kernel
lemma lb445 : Slice lb334 lb320 (subcube 0 16) 4 := slice_direct lb446 lb411
lemma lb448 : sliceDirectCheck 0 4 0 lb334 lb320 lb109 lb99 = true := by decide +kernel
lemma lb447 : Slice lb334 lb320 (subcube 0 4) 4 := slice_direct lb448 lb167
lemma lb450 : sliceDirectCheck 0 8 0 lb334 lb320 lb333 lb319 = true := by decide +kernel
lemma lb449 : Slice lb334 lb320 (subcube 0 8) 4 := slice_direct lb450 lb415
lemma lb452 : sliceDirectCheck 0 32 0 lb334 lb320 lb330 lb316 = true := by decide +kernel
lemma lb451 : Slice lb334 lb320 (subcube 0 32) 4 := slice_direct lb452 lb409
set_option maxRecDepth 200000 in
lemma lb482 : ∀ i (hi : i < lb481.size), Slice lb334 lb320 lb481[i].1 lb481[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice lb334 lb320 p.1 p.2) (forall_cons lb445 (forall_cons lb447 (forall_cons lb449 (forall_cons lb451 (fun _ h => (List.not_mem_nil h).elim)))))
lemma lb327 : ∀ i (hi : i < lb326.size), ∀ c, lb326[i] = some c → ValidPool lb334 lb320 c := buildPools_sound lb482
lemma lb363 : ∀ i (hi : i < lb133.size), ∀ xs ∈ lb133[i], Impossible lb320 (0 - 1) xs.toFinset := by intro i hi; simp [lb133] at hi
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb383 : checkNodes lb339 lb320 lb160 lb326 lb343 lb133 0 lb179 = true := by decide +kernel
def lb351 : Array (List (List Nat)) := buildBuckets 1 lb339 lb179
lemma lb352 : ∀ i (hi : i < lb351.size), ∀ xs ∈ lb351[i], Impossible lb320 0 xs.toFinset :=
  buildBuckets_sound (by decide) lb405 lb340 lb327 lb344 lb363 lb383
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb384 : checkNodes lb339 lb320 lb160 lb326 lb343 lb351 1 lb179 = true := by decide +kernel
lemma lb353 : ∀ i (hi : i < lb351.size), ∀ xs ∈ lb351[i], Impossible lb320 1 xs.toFinset :=
  buildBuckets_sound (by decide) lb405 lb340 lb327 lb344 lb352 lb384
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb385 : checkNodes lb339 lb320 lb160 lb326 lb343 lb351 2 lb179 = true := by decide +kernel
lemma lb354 : ∀ i (hi : i < lb351.size), ∀ xs ∈ lb351[i], Impossible lb320 2 xs.toFinset :=
  buildBuckets_sound (by decide) lb405 lb340 lb327 lb344 lb353 lb385
def lb431 : List NodeSpec := [([4,5,8,3],[0,1],[]),([9,0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb386 : checkNodes lb339 lb320 lb160 lb326 lb343 lb351 3 lb431 = true := by decide +kernel
def lb355 : Array (List (List Nat)) := buildBuckets 1 lb339 lb431
lemma lb356 : ∀ i (hi : i < lb355.size), ∀ xs ∈ lb355[i], Impossible lb320 3 xs.toFinset :=
  buildBuckets_sound (by decide) lb405 lb340 lb327 lb344 lb354 lb386
def lb432 : List NodeSpec := [([4,5,1,2,3],[0,2],[0]),([6,0,1,2,3],[],[]),([7,0,1,2,3],[3],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb387 : checkNodes lb339 lb320 lb160 lb326 lb343 lb355 4 lb432 = true := by decide +kernel
def lb357 : Array (List (List Nat)) := buildBuckets 2 lb339 lb432
lemma lb358 : ∀ i (hi : i < lb357.size), ∀ xs ∈ lb357[i], Impossible lb320 4 xs.toFinset :=
  buildBuckets_sound (by decide) lb405 lb340 lb327 lb344 lb356 lb387
def lb433 : List NodeSpec := [([4,0,1,2,3],[2,1,0,3],[0,1,2,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb388 : checkNodes lb339 lb320 lb160 lb326 lb343 lb357 5 lb433 = true := by decide +kernel
def lb359 : Array (List (List Nat)) := buildBuckets 1 lb339 lb433
lemma lb360 : ∀ i (hi : i < lb359.size), ∀ xs ∈ lb359[i], Impossible lb320 5 xs.toFinset :=
  buildBuckets_sound (by decide) lb405 lb340 lb327 lb344 lb358 lb388
def lb434 : List NodeSpec := [([0,1,2,3],[1,2,0,3],[0,4,5,6,7,8])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb389 : checkNodes lb339 lb320 lb160 lb326 lb343 lb359 6 lb434 = true := by decide +kernel
def lb361 : Array (List (List Nat)) := buildBuckets 1 lb339 lb434
lemma lb362 : ∀ i (hi : i < lb361.size), ∀ xs ∈ lb361[i], Impossible lb320 6 xs.toFinset :=
  buildBuckets_sound (by decide) lb405 lb340 lb327 lb344 lb360 lb389
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb402 : forestRootCheck lb334 lb320 [(VAR 2,28,24),(VAR 3,28,20),(VAR 4,28,12),(VAR 5,44,12)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb401 : bucketContains lb361 lb334 = true := by decide +kernel
lemma lb417 : Lower lb334 lb320 7 := lower_of_forest lb402 lb362 lb401
def lb321 : Nat := 0xfcc0c000fcc0c000fcc0c000fcc0c000
def lb335 : List Nat := varsOf 30
lemma lb419 : carryOK [(1,5),(1,4),(1,3),(1,2)] lb335 lb321 lb334 lb320 = true := by decide +kernel
lemma lb418 : Lower lb335 lb321 7 := carry_of lb419 lb417
def lb322 : Nat := 0xfcc0fcc0c000c000fcc0fcc0c000c000
def lb336 : List Nat := varsOf 46
lemma lb421 : carryOK [(1,4),(1,3),(1,2)] lb336 lb322 lb334 lb320 = true := by decide +kernel
lemma lb420 : Lower lb336 lb322 7 := carry_of lb421 lb417
def lb323 : Nat := 0xfcfcc0c0c0c00000fcfcc0c0c0c00000
def lb337 : List Nat := varsOf 54
lemma lb423 : carryOK [(1,3),(1,2)] lb337 lb323 lb334 lb320 = true := by decide +kernel
lemma lb422 : Lower lb337 lb323 7 := carry_of lb423 lb417
def lb324 : Nat := 0xffcccc00cc000000ffcccc00cc000000
lemma lb425 : carryOK [(1,2)] lb232 lb324 lb334 lb320 = true := by decide +kernel
lemma lb424 : Lower lb232 lb324 7 := carry_of lb425 lb417
def lb325 : Nat := 0xfcc0c000c0000000fcc0c000c0000000
def lb338 : List Nat := varsOf 62
def lb443 : List Nat := [30,30,30,30,46,46,46,46,54,54,54,54,58,58,58,58,60,60,60,60,30,30,30,30,30,30,46,46,46,46,46,46,54,54,54,54,54,54,58,58,58,58,58,58,60,60,60,60,60,60]
def lb430 : List Nat := [28,26,22,14,44,42,38,14,52,50,38,22,56,50,42,26,56,52,44,28,38,42,44,50,52,56,22,26,28,50,52,56,14,26,28,42,44,56,14,22,28,38,44,52,14,22,26,38,42,50]
def lb400 : Nat := fullMask 50
def lb349 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xffffff0ffff,0x3f2cb2cb0eeee),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x3f03fffff0fff,0xbfd5555e0ddd),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x3ffc0fffff0ff,0x1557f9a6dd0bb),(0xffff0000ffff0000ffff0000ffff0000,0x3ffff03ffff0f,0x269a6ff8bbb07),(0xffffffff00000000ffffffff00000000,0x3fffffc0ffff0,0x38e38e3f77770)]
def lb486 : List (Nat × Nat × Nat) := [(0,0,1),(0,2,3),(0,0,2),(3,5,2),(0,5,2),(0,1,3),(0,3,4),(3,8,3),(2,5,6),(0,9,3),(0,1,2),(0,0,3),(3,9,3),(0,5,3),(3,13,0),(0,1,4),(0,2,4),(3,12,4),(3,16,4),(3,14,4),(0,0,4),(3,14,0),(0,12,4),(1,14,4),(2,2,11),(0,17,4),(0,14,4),(0,16,4),(3,17,4),(3,14,1),(3,31,0)]
def lb341 : Array Decor := buildWires lb349 lb486
def lb345 : Array (List (Nat × Nat)) := #[[],[(1,2)],[(1,3),(1,2)],[(1,2),(2,4),(1,5)],[(4,5)],[(1,5),(1,4),(1,3),(1,2)],[(3,5),(3,4)],[(3,5),(2,3),(2,4)],[(3,5),(1,2),(1,4)],[(2,3),(1,3),(2,5),(1,4)],[(2,3),(3,5),(2,4)],[(3,4),(3,5)],[(3,4)],[(3,4),(2,3),(2,5)],[(2,3),(2,4)],[(3,4),(2,3),(1,2),(1,5)],[(2,3),(1,2),(1,4)],[(3,5),(2,3),(1,2),(1,4)],[(3,5),(2,4)],[(2,5),(2,4),(2,3)],[(2,4)],[(2,3),(3,5),(1,2),(1,4)],[(2,3)],[(1,4),(1,3),(1,2)],[(2,4),(2,3)],[(4,5),(1,2),(1,3)],[(2,5),(1,4)],[(4,5),(1,2)],[(4,5),(2,3)],[(1,2),(1,4)],[(3,4),(1,2)],[(4,5),(1,3),(1,2)],[(2,5),(2,4)],[(3,5),(3,4),(1,2)],[(1,3),(1,4),(1,2)],[(3,5),(1,3),(1,4),(1,2)],[(2,4),(1,3)],[(1,2),(2,3),(1,4)],[(1,2),(1,3)],[(2,4),(1,2),(1,3)],[(2,3),(2,5),(1,4)],[(2,5),(2,4),(1,2),(1,3)],[(2,5),(2,4),(1,3)],[(1,2),(1,5),(2,4),(1,3)]]
def lb480 : List (Nat × Nat) := [(subcube 0 12,4),(subcube 0 6,4),(subcube 0 32,7),(subcube 0 48,4),(subcube 0 2,7),(subcube 0 24,4),(subcube 0 20,4),(subcube 0 10,4),(subcube 0 8,7),(subcube 0 16,7),(subcube 0 4,7),(subcube 0 34,4),(subcube 0 18,4)]
def lb483 : Array (Nat × Nat) := lb480.toArray
def lb444 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(2,[(0,0,1),(0,0,2),(0,1,2)]),(8,[(0,0,1),(0,0,3),(0,1,3)]),(9,[]),(4,[(0,5,2),(0,9,3),(3,14,4)]),(2,[(0,0,1),(0,5,2),(3,9,3)]),(4,[(0,5,2),(0,5,3),(0,2,3)]),(10,[]),(9,[(0,0,1),(0,0,2)]),(8,[(0,0,1),(0,1,3)]),(2,[(0,0,1),(3,5,2)]),(8,[(0,0,1),(3,8,3)]),(9,[(0,0,1),(3,5,2)]),(4,[(0,2,3),(2,5,6)]),(8,[]),(9,[(0,0,1),(0,5,2)]),(4,[(0,5,2),(0,2,3)]),(2,[(0,0,1),(0,5,2)]),(4,[(0,1,2)]),(9,[(0,0,1),(0,0,2),(0,1,2)]),(10,[(0,5,2),(0,0,3)]),(8,[(0,0,1),(0,0,3)]),(11,[]),(4,[(0,5,2),(0,9,3)]),(4,[(0,5,2),(3,9,3)]),(10,[(0,5,2),(3,9,3)]),(8,[(0,0,1),(3,9,3)]),(2,[(0,0,1),(0,0,2)]),(10,[(0,5,2),(0,9,3)]),(8,[(0,0,1),(0,9,3)]),(4,[(0,5,2),(0,5,3)]),(12,[]),(8,[(0,0,1)]),(9,[(0,0,1)]),(4,[(0,2,3)]),(10,[(0,2,3)]),(10,[(0,0,2)]),(4,[(0,5,2)]),(10,[(0,5,2)]),(2,[(0,0,1)])]
def lb328 : Array (Option BoundPool) := buildPools lb341 lb338 lb483 lb444
lemma lb406 : goodPairs lb325 lb443 lb430 := goodPairs_of (by decide +kernel)
lemma lb350 : ∀ x ∈ lb349, faithful lb443 lb430 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma lb342 : ∀ x ∈ lb341.toList, faithful lb443 lb430 x ∧ x.1 < 2^128 := buildWires_faithful lb350
lemma lb346 : ∀ sw ∈ lb345.toList, swapsValid sw = true ∧ permWord sw lb325 = lb325 := autos_of (by decide +kernel)
lemma lb454 : sliceDirectCheck 0 12 0 lb338 lb325 lb332 lb318 = true := by decide +kernel
lemma lb453 : Slice lb338 lb325 (subcube 0 12) 4 := slice_direct lb454 lb413
lemma lb462 : sliceDirectCheck 0 6 0 lb338 lb325 lb109 lb99 = true := by decide +kernel
lemma lb455 : Slice lb338 lb325 (subcube 0 6) 4 := slice_direct lb462 lb167
lemma lb464 : sliceDirectCheck 0 32 0 lb338 lb325 lb335 lb321 = true := by decide +kernel
lemma lb463 : Slice lb338 lb325 (subcube 0 32) 7 := slice_direct lb464 lb418
lemma lb466 : sliceDirectCheck 0 48 0 lb338 lb325 lb257 lb254 = true := by decide +kernel
lemma lb465 : Slice lb338 lb325 (subcube 0 48) 4 := slice_direct lb466 lb427
lemma lb468 : sliceDirectCheck 0 2 0 lb338 lb325 lb334 lb320 = true := by decide +kernel
lemma lb467 : Slice lb338 lb325 (subcube 0 2) 7 := slice_direct lb468 lb417
lemma lb470 : sliceDirectCheck 0 24 0 lb338 lb325 lb114 lb104 = true := by decide +kernel
lemma lb469 : Slice lb338 lb325 (subcube 0 24) 4 := slice_direct lb470 lb175
lemma lb472 : sliceDirectCheck 0 20 0 lb338 lb325 lb231 lb228 = true := by decide +kernel
lemma lb471 : Slice lb338 lb325 (subcube 0 20) 4 := slice_direct lb472 lb407
lemma lb474 : sliceDirectCheck 0 10 0 lb338 lb325 lb333 lb319 = true := by decide +kernel
lemma lb473 : Slice lb338 lb325 (subcube 0 10) 4 := slice_direct lb474 lb415
lemma lb476 : sliceDirectCheck 0 8 0 lb338 lb325 lb337 lb323 = true := by decide +kernel
lemma lb475 : Slice lb338 lb325 (subcube 0 8) 7 := slice_direct lb476 lb422
lemma lb478 : sliceDirectCheck 0 16 0 lb338 lb325 lb336 lb322 = true := by decide +kernel
lemma lb477 : Slice lb338 lb325 (subcube 0 16) 7 := slice_direct lb478 lb420
lemma lb457 : sliceDirectCheck 0 4 0 lb338 lb325 lb232 lb324 = true := by decide +kernel
lemma lb456 : Slice lb338 lb325 (subcube 0 4) 7 := slice_direct lb457 lb424
lemma lb459 : sliceDirectCheck 0 34 0 lb338 lb325 lb330 lb316 = true := by decide +kernel
lemma lb458 : Slice lb338 lb325 (subcube 0 34) 4 := slice_direct lb459 lb409
lemma lb461 : sliceDirectCheck 0 18 0 lb338 lb325 lb331 lb317 = true := by decide +kernel
lemma lb460 : Slice lb338 lb325 (subcube 0 18) 4 := slice_direct lb461 lb411
set_option maxRecDepth 200000 in
lemma lb484 : ∀ i (hi : i < lb483.size), Slice lb338 lb325 lb483[i].1 lb483[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice lb338 lb325 p.1 p.2) (forall_cons lb453 (forall_cons lb455 (forall_cons lb463 (forall_cons lb465 (forall_cons lb467 (forall_cons lb469 (forall_cons lb471 (forall_cons lb473 (forall_cons lb475 (forall_cons lb477 (forall_cons lb456 (forall_cons lb458 (forall_cons lb460 (fun _ h => (List.not_mem_nil h).elim))))))))))))))
lemma lb329 : ∀ i (hi : i < lb328.size), ∀ c, lb328[i] = some c → ValidPool lb338 lb325 c := buildPools_sound lb484
lemma lb382 : ∀ i (hi : i < lb133.size), ∀ xs ∈ lb133[i], Impossible lb325 (0 - 1) xs.toFinset := by intro i hi; simp [lb133] at hi
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb390 : checkNodes lb341 lb325 lb400 lb328 lb345 lb133 0 lb179 = true := by decide +kernel
def lb364 : Array (List (List Nat)) := buildBuckets 1 lb341 lb179
lemma lb365 : ∀ i (hi : i < lb364.size), ∀ xs ∈ lb364[i], Impossible lb325 0 xs.toFinset :=
  buildBuckets_sound (by decide) lb406 lb342 lb329 lb346 lb382 lb390
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb391 : checkNodes lb341 lb325 lb400 lb328 lb345 lb364 1 lb179 = true := by decide +kernel
lemma lb366 : ∀ i (hi : i < lb364.size), ∀ xs ∈ lb364[i], Impossible lb325 1 xs.toFinset :=
  buildBuckets_sound (by decide) lb406 lb342 lb329 lb346 lb365 lb391
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb392 : checkNodes lb341 lb325 lb400 lb328 lb345 lb364 2 lb179 = true := by decide +kernel
lemma lb367 : ∀ i (hi : i < lb364.size), ∀ xs ∈ lb364[i], Impossible lb325 2 xs.toFinset :=
  buildBuckets_sound (by decide) lb406 lb342 lb329 lb346 lb366 lb392
def lb435 : List NodeSpec := [([29,8,16,20],[],[]),([29,12,25,1],[],[]),([9,32,10,21],[0],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb393 : checkNodes lb341 lb325 lb400 lb328 lb345 lb364 3 lb435 = true := by decide +kernel
def lb368 : Array (List (List Nat)) := buildBuckets 2 lb341 lb435
lemma lb369 : ∀ i (hi : i < lb368.size), ∀ xs ∈ lb368[i], Impossible lb325 3 xs.toFinset :=
  buildBuckets_sound (by decide) lb406 lb342 lb329 lb346 lb367 lb393
def lb436 : List NodeSpec := [([8,16,20,2,11],[1],[0]),([23,8,10,2,4],[],[]),([29,12,0,1,4],[],[0,1]),([12,25,1,2,11],[2],[0]),([12,25,20,2,3],[],[]),([26,34,2,3,4],[],[]),([26,1,2,3,28],[],[]),([9,16,20,2,11],[3],[2]),([23,9,10,2,4],[],[]),([17,25,20,2,3],[],[]),([35,1,2,3,4],[],[]),([9,32,10,2,4],[0],[0]),([9,16,10,21,4],[],[0,1]),([5,7,10,21,11],[],[]),([29,8,16,1,4],[],[3,4,0]),([14,25,20,2,3],[2],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb394 : checkNodes lb341 lb325 lb400 lb328 lb345 lb368 4 lb436 = true := by decide +kernel
def lb370 : Array (List (List Nat)) := buildBuckets 6 lb341 lb436
lemma lb371 : ∀ i (hi : i < lb370.size), ∀ xs ∈ lb370[i], Impossible lb325 4 xs.toFinset :=
  buildBuckets_sound (by decide) lb406 lb342 lb329 lb346 lb369 lb394
def lb437 : List NodeSpec := [([5,19,1,2,3,4],[4],[]),([14,0,1,2,3,4],[2],[5]),([5,7,10,6,4],[5,1,6,7],[6,7,8,9]),([8,16,1,2,11,4],[1],[4,8,0]),([8,16,20,2,3,4],[],[10,8,0]),([5,7,15,11,3,4],[5,1,6,7,0,8],[11,12,6,13,14,7,15,16,17]),([8,16,10,2,4],[5,1,9],[4,18,8]),([5,7,10,21,3,4],[],[19,20,15,21,9,0]),([12,0,1,2,11,4],[2],[0,1]),([22,0,1,2,3,4],[],[]),([23,8,1,2,3,4],[],[0]),([9,16,10,2,4],[10,0,7,1,9],[4,0,1]),([9,5,16,10,2,4],[0,6,7,1],[]),([24,5,0,1,2,3],[11],[]),([9,5,16,1,6,4],[0,7,6,1],[]),([17,25,1,2,3,4],[2,12],[0,22]),([17,5,16,1,2,4],[10,7],[]),([26,5,1,2,3,4],[4],[]),([12,25,1,2,3,4],[2],[0]),([27,0,1,2,3,4],[],[2]),([24,0,1,2,3,4],[],[]),([14,0,1,2,3,28],[],[0,1,2,23,5]),([9,16,1,2,11,4],[3],[19,1,0,2,22]),([26,9,1,2,3,4],[4],[24]),([14,25,1,2,3,4],[2],[0,22,24]),([9,16,20,2,3,4],[],[4,1,22,25,0]),([26,14,1,2,3,4],[4],[0,22,24]),([29,8,0,1,3,4],[],[2,26,3,0,4,27]),([30,0,1,2,3,4],[12],[]),([17,9,16,1,2,4],[10,7,1],[]),([24,14,0,1,2,3],[2],[]),([9,18,0,1,6,4],[0,6,13],[]),([24,9,0,1,2,3],[],[]),([23,9,1,2,3,4],[],[0,22]),([24,0,1,2,3],[],[]),([31,0,1,2,3,4],[],[0,1,2,23,5]),([9,32,1,2,3,4],[0],[0,4,22,28]),([33,0,1,2,3,4],[12],[23])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb395 : checkNodes lb341 lb325 lb400 lb328 lb345 lb370 5 lb437 = true := by decide +kernel
def lb372 : Array (List (List Nat)) := buildBuckets 13 lb341 lb437
lemma lb373 : ∀ i (hi : i < lb372.size), ∀ xs ∈ lb372[i], Impossible lb325 5 xs.toFinset :=
  buildBuckets_sound (by decide) lb406 lb342 lb329 lb346 lb371 lb395
def lb438 : List NodeSpec := [([5,7,10,2,3,4],[14,4,1,6,7,15,16],[6,20,14,7,16,29,8,0,30]),([8,0,1,2,11,3,4],[1,3,0,17],[0,4,18,8,1,27]),([12,0,1,2,3,4],[6,4,1,18,2,19],[0,1]),([13,5,0,1,2,3,4],[20],[0,1]),([9,5,0,1,6,3,4],[21,0,7,6,1,22,23],[0,1]),([14,9,0,1,2,3,4],[10,24,22],[0,1,2,23]),([9,0,1,2,11,3,4],[3,1,0,24],[0,23,5,4,1,27,2,31]),([5,7,15,3,4],[25,14,21,1,0,26,8,7],[12,6,14,7,16,17,0]),([9,16,1,2,3,4],[10,0,7,1,22,27,28],[0,4,22]),([17,9,0,1,2,3,4],[10,0,1,7,22],[23,0,1,2]),([14,5,0,1,2,3,4],[5,29,30],[0,1]),([17,5,0,1,2,3,4],[21,10,6,0,7,22,31],[23,0,1]),([8,16,1,2,3,4],[5,4,1,28,19],[4,18,0]),([17,0,1,2,3,4],[0,4,7,1,22,2,31,32,33,12],[23,0,1,2]),([5,7,1,2,11,3,4],[5,1,6,7,34],[11,24,19,13,20,32,0,8,30,33,9,34,35]),([14,0,1,2,3,4],[30,35,36,22,2],[0,1,2,23]),([9,5,16,1,2,3,4],[0,7,6,1],[0]),([9,18,0,1,2,3,4],[22,21,0,37],[23,2,0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb396 : checkNodes lb341 lb325 lb400 lb328 lb345 lb372 6 lb438 = true := by decide +kernel
def lb374 : Array (List (List Nat)) := buildBuckets 7 lb341 lb438
lemma lb375 : ∀ i (hi : i < lb374.size), ∀ xs ∈ lb374[i], Impossible lb325 6 xs.toFinset :=
  buildBuckets_sound (by decide) lb406 lb342 lb329 lb346 lb373 lb396
def lb439 : List NodeSpec := [([5,0,1,6,2,3,4],[0,38,5,1,39,40,3,41,42,29],[0,36,2,23,12,6,14,22,24,16,37,38,39,33,9,40]),([5,7,1,2,3,4],[43,21,0,4,1,15,34,7,39],[12,6,14,7,0,4,22,28]),([8,0,1,2,3,4],[14,0,4,1,39,10,2,17,19],[0,4,1,27]),([9,5,0,1,2,3,4],[21,0,7,1,6,29,22,24,44,45,39],[0,4,1,27]),([9,0,1,2,3,4],[0,7,1,10,22,2,24,44,45,39],[0,4,1,27,2,31])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb397 : checkNodes lb341 lb325 lb400 lb328 lb345 lb374 7 lb439 = true := by decide +kernel
def lb376 : Array (List (List Nat)) := buildBuckets 2 lb341 lb439
lemma lb377 : ∀ i (hi : i < lb376.size), ∀ xs ∈ lb376[i], Impossible lb325 7 xs.toFinset :=
  buildBuckets_sound (by decide) lb406 lb342 lb329 lb346 lb375 lb397
def lb440 : List NodeSpec := [([5,0,1,2,3,4],[14,4,21,1,39,10,40,2,46],[0,12,6,1,30,33,11])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb398 : checkNodes lb341 lb325 lb400 lb328 lb345 lb376 8 lb440 = true := by decide +kernel
def lb378 : Array (List (List Nat)) := buildBuckets 1 lb341 lb440
lemma lb379 : ∀ i (hi : i < lb378.size), ∀ xs ∈ lb378[i], Impossible lb325 8 xs.toFinset :=
  buildBuckets_sound (by decide) lb406 lb342 lb329 lb346 lb377 lb398
def lb441 : List NodeSpec := [([0,1,2,3,4],[4,14,21,10,2],[0,22,24,19,38,39,41,36,42,43])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb399 : checkNodes lb341 lb325 lb400 lb328 lb345 lb378 9 lb441 = true := by decide +kernel
def lb380 : Array (List (List Nat)) := buildBuckets 1 lb341 lb441
lemma lb381 : ∀ i (hi : i < lb380.size), ∀ xs ∈ lb380[i], Impossible lb325 9 xs.toFinset :=
  buildBuckets_sound (by decide) lb406 lb342 lb329 lb346 lb379 lb399
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb404 : forestRootCheck lb338 lb325 [(VAR 1,30,28),(VAR 2,30,26),(VAR 3,30,22),(VAR 4,30,14),(VAR 5,46,14)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb403 : bucketContains lb380 lb338 = true := by decide +kernel
lemma lb426 : Lower lb338 lb325 10 := lower_of_forest lb404 lb381 lb403
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q20d : Lower (varsOf 31) 0xe8808000e8808000e8808000e8808000 10 := by
  apply carry_of (swaps := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5)]) (roots2 := lb338) (T2 := lb325) _ lb426
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q20 : Lower (varsOf 31) 0xfffefee8fffefee8fffefee8fffefee8 10 := dualLower (by decide +kernel) (by decide +kernel) q20d
def s1NR : List Nat := varsOf 63
def s1NG : Nat := 0xfffefeeefffafee8fffefeeefffafee8
def s1NPos : List Nat := [3,3,5,5,6,6,9,9,10,10,12,12,17,17,20,20,24,24,33,33,34,44,44,50,50,52]
def s1NNeg : List Nat := [1,2,1,4,2,4,1,8,2,8,4,8,1,16,4,16,8,16,1,32,2,36,40,18,48,36]
def s1NMask : Nat := fullMask 26
def s1NBase : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xc30cf,0x41045),(0xcccccccccccccccccccccccccccccccc,0x1900333,0x900112),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x260cc3c,0x2204428),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x630fc0,0x410a80),(0xffff0000ffff0000ffff0000ffff0000,0x383f000,0x182a000),(0xffffffff00000000ffffffff00000000,0x3fc0000,0x3680000)]
def s1NSteps : List (Nat × Nat × Nat) := []
def s1NW : BT Decor := buildWiresBT 3 s1NBase s1NSteps
def s1NAutoList : List (List (Nat × Nat)) := [[],[(2,3)]]
def s1NAutos : BT (List (Nat × Nat)) := btOfList 1 s1NAutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NPairs : goodPairs s1NG s1NPos s1NNeg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBaseOk : ∀ x ∈ s1NBase, faithful s1NPos s1NNeg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NWOk : btAll (fun x => faithful s1NPos s1NNeg x ∧ x.1 < 2^128) s1NW := buildWiresBT_faithful s1NBaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NAutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw s1NG = s1NG) s1NAutos := btAll_ofList (autos_of (by decide +kernel))
def s1NSliceList : List (Option (Nat × Nat)) := [some (0xffff00000000ffffffff00000000ffff,10)]
def s1NSlices : BT (Option (Nat × Nat)) := btOfList 1 s1NSliceList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlice0 : Slice s1NR s1NG 0xffff00000000ffffffff00000000ffff 10 := mappedSlice (f := identifyRow 0 0 4 5) (R := varsOf 31) (G := 0xfffefee8fffefee8fffefee8fffefee8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) q20
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlicesOk : btAll (fun o => ∀ p, o = some p → Slice s1NR s1NG p.1 p.2) s1NSlices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice s1NR s1NG p.1 p.2) (forall_cons (fun _ h => by cases h; exact s1NSlice0) (fun _ h => (List.not_mem_nil h).elim))
def s1NEmpty : BT (List (List Nat)) := BT.empty
lemma s1NEmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible s1NG (9 - 1) xs.toFinset) s1NEmpty := trivial
def s1NBlock9_0Specs : List PoolSpec := [(0,[])]
def s1NBlock9_0Pools : BT (Option BoundPool) := buildPoolsBT 1 s1NW s1NR s1NSlices s1NBlock9_0Specs
def s1NBlock9_0 : List NodeSpec := [([0,1,2,3,4,5],[0],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock9_0Ok : checkNodesBT s1NW s1NG s1NMask s1NBlock9_0Pools s1NAutos s1NEmpty 9 s1NBlock9_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBlock9_0Mem : ∀ ns ∈ s1NBlock9_0, Impossible s1NG 9 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NEmptyOk s1NBlock9_0Ok
def s1NNodes9 : List NodeSpec := s1NBlock9_0
def s1NBucket9 : BT (List (List Nat)) := buildBucketsBT s1NW s1NNodes9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBucket9Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s1NG 9 xs.toFinset) s1NBucket9 := buildBucketsBT_of_mem s1NBlock9_0Mem
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBound : Lower s1NR s1NG 10 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 3,1,9),(VAR 4,1,17),(VAR 5,1,33)]) (by decide +kernel) s1NBucket9Ok (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q19 : Lower (varsOf 95) 0xfffefefefffefefeffecfee8ffecfee8 10 := by
  apply carry_of (swaps := [(4, 5), (5, 6), (1, 2), (2, 3), (0, 1)]) (roots2 := s1NR) (T2 := s1NG) _ s1NBound
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q21 : Lower (varsOf 111) 0xfffefffefefefefeffeaffeafee8fee8 10 := by
  apply carry_of (swaps := [(4, 5), (5, 6), (4, 5), (1, 2), (2, 3)]) (roots2 := s1NR) (T2 := s1NG) _ s1NBound
  decide +kernel
def lb532 : List (List (Nat × Nat)) := [[],[(1,2)],[(0,1)],[(0,2)],[(1,2),(0,1)],[(1,2),(0,2)]]
def lb533 : BT (List (Nat × Nat)) := btOfList 3 lb532
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb534 : btAll (fun sw => swapsValid sw = true ∧ permWord sw lb100 = lb100) lb533 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb539 : checkNodesBT lb314 lb100 lb19 lb309 lb533 lb16 3 lb11 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb538 : checkNodesBT lb314 lb100 lb19 lb309 lb533 lb16 3 lb21 = true := lb539
def lb536 : BT (List (List Nat)) := buildBucketsBT lb314 lb21
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb537 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb100 3 xs.toFinset) lb536 := buildBucketsBT_sound (by decide) lb308 lb315 lb310 lb534 lb306 lb538
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb535 : Lower lb110 lb100 4 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5)]) (by decide +kernel) lb537 (by decide +kernel)
def lb541 : Nat := 0xe800e800e800e800e800e800e800e800
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb540 : Lower lb5 lb541 5 := lift_of (z := 0) (o := 8) (essPairs := [(VAR 3,3,11)]) (by decide +kernel) lb535
def lb543 : Nat := 0xe8a8e8a8e8a8e8a8e8a8e8a8e8a8e8a8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb542 : Lower lb5 lb543 5 := lift_of (z := 0) (o := 8) (essPairs := [(VAR 3,6,14)]) (by decide +kernel) lb535
def lb554 : Nat := 0xeeaaee00eeaaee00eeaaee00eeaaee00
def lb559 : List Nat := [9,19,9,10,10,19,17,26]
def lb555 : List Nat := [8,18,1,2,8,3,1,18]
def lb547 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,103,100),(0xcccccccccccccccccccccccccccccccc,186,170),(0xff00ff00ff00ff00ff00ff00ff00ff00,157,17),(0xffff0000ffff0000ffff0000ffff0000,226,130)]
def lb562 : BT Decor := buildWiresBT 2 lb547 lb31
def lb544 : List (List (Nat × Nat)) := [[],[(1,4),(0,3)]]
def lb545 : BT (List (Nat × Nat)) := btOfList 1 lb544
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb556 : goodPairs lb554 lb559 lb555 := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb548 : ∀ x ∈ lb547, faithful lb559 lb555 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb563 : btAll (fun x => faithful lb559 lb555 x ∧ x.1 < 2^128) lb562 := buildWiresBT_faithful lb548
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb546 : btAll (fun sw => swapsValid sw = true ∧ permWord sw lb554 = lb554) lb545 := btAll_ofList (autos_of (by decide +kernel))
def lb557 : BT (Option BoundPool) := buildPoolsBT 1 lb562 lb40 lb28 lb30
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb560 : btAll (fun o => ∀ p, o = some p → Slice lb40 lb554 p.1 p.2) lb28 := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice lb40 lb554 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb558 : btAll (fun o => ∀ c, o = some c → ValidPool lb40 lb554 c) lb557 := buildPoolsBT_sound lb560
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb553 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb554 (3 - 1) xs.toFinset) lb16 := trivial
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb561 : checkNodesBT lb562 lb554 lb288 lb557 lb545 lb16 3 lb281 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb552 : checkNodesBT lb562 lb554 lb288 lb557 lb545 lb16 3 lb290 = true := lb561
def lb550 : BT (List (List Nat)) := buildBucketsBT lb562 lb290
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb551 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb554 3 xs.toFinset) lb550 := buildBucketsBT_sound (by decide) lb556 lb563 lb558 lb546 lb553 lb552
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb549 : Lower lb40 lb554 4 := lower_of_forestBT (essPairs := [(VAR 0,8,9),(VAR 1,8,10),(VAR 3,1,9),(VAR 4,1,17)]) (by decide +kernel) lb551 (by decide +kernel)
def lb565 : Nat := 0xfaaafa00faaafa00faaafa00faaafa00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb564 : Lower lb43 lb565 4 := carry_of (swaps := [(1,2)]) (roots2 := lb40) (T2 := lb554) (by decide +kernel) lb549
def lb506 : Nat := 0xe8a8e800e8a8e800e8a8e800e8a8e800
def lb515 : List Nat := [13,14,21,14,13,14,11,19,21,11,13,21,11,30,11,23,23,19,21]
def lb508 : List Nat := [12,12,22,10,9,6,3,3,20,10,5,5,9,22,8,22,7,17,17]
def lb507 : Nat := fullMask 19
def lb490 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x7dfd5,0x71cd0),(0xcccccccccccccccccccccccccccccccc,0x3f2ea,0x1a2ec),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x5ad3f,0x1ad27),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x767b,0x521b),(0xffff0000ffff0000ffff0000ffff0000,0x7a984,0x6a104)]
def lb526 : List (Nat × Nat × Nat) := [(0,0,1),(3,0,1),(0,1,2),(2,2,5)]
def lb530 : BT Decor := buildWiresBT 4 lb490 lb526
def lb487 : List (List (Nat × Nat)) := [[],[(1,2)]]
def lb488 : BT (List (Nat × Nat)) := btOfList 1 lb487
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb512 : goodPairs lb506 lb515 lb508 := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb491 : ∀ x ∈ lb490, faithful lb515 lb508 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb531 : btAll (fun x => faithful lb515 lb508 x ∧ x.1 < 2^128) lb530 := buildWiresBT_faithful lb491
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb489 : btAll (fun sw => swapsValid sw = true ∧ permWord sw lb506 = lb506) lb488 := btAll_ofList (autos_of (by decide +kernel))
def lb522 : List (Option (Nat × Nat)) := [some (subcubeFast 0 2,4),some (subcubeFast 0 4,4),some (subcubeFast 0 8,4),some (subcubeFast 0 16,5),some (subcubeFast 16 0,5),some (subcubeFast 16 8,4)]
def lb523 : BT (Option (Nat × Nat)) := btOfList 3 lb522
def lb525 : List PoolSpec := [(1,[]),(0,[]),(3,[]),(4,[]),(5,[]),(2,[])]
def lb513 : BT (Option BoundPool) := buildPoolsBT 3 lb530 lb63 lb523 lb525
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb521 : Slice lb63 lb506 (subcubeFast 16 8) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) lb535
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb520 : Slice lb63 lb506 (subcubeFast 16 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) lb540
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb519 : Slice lb63 lb506 (subcubeFast 0 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) lb542
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb518 : Slice lb63 lb506 (subcubeFast 0 8) 4 := slice_fast_direct (zDead := 16) (by decide +kernel) lb535
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb517 : Slice lb63 lb506 (subcubeFast 0 4) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) lb549
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb516 : Slice lb63 lb506 (subcubeFast 0 2) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) lb564
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb524 : btAll (fun o => ∀ p, o = some p → Slice lb63 lb506 p.1 p.2) lb523 := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice lb63 lb506 p.1 p.2) (forall_cons (fun _ h => by cases h; exact lb516) (forall_cons (fun _ h => by cases h; exact lb517) (forall_cons (fun _ h => by cases h; exact lb518) (forall_cons (fun _ h => by cases h; exact lb519) (forall_cons (fun _ h => by cases h; exact lb520) (forall_cons (fun _ h => by cases h; exact lb521) (fun _ h => (List.not_mem_nil h).elim)))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb514 : btAll (fun o => ∀ c, o = some c → ValidPool lb63 lb506 c) lb513 := buildPoolsBT_sound lb524
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb505 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb506 (4 - 1) xs.toFinset) lb16 := trivial
def lb492 : List NodeSpec := lb78 [([0,1,3,4,8],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb527 : checkNodesBT lb530 lb506 lb507 lb513 lb488 lb16 4 lb492 = true := by decide +kernel
def lb509 : List NodeSpec := lb492
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb502 : checkNodesBT lb530 lb506 lb507 lb513 lb488 lb16 4 lb509 = true := lb527
def lb496 : BT (List (List Nat)) := buildBucketsBT lb530 lb509
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb497 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb506 4 xs.toFinset) lb496 := buildBucketsBT_sound (by decide) lb512 lb531 lb514 lb489 lb505 lb502
def lb493 : List NodeSpec := lb78 [([0,1,2,3,4,5],[0]),([0,1,2,3,4,6],[2,3]),([0,1,2,3,4,7],[1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb528 : checkNodesBT lb530 lb506 lb507 lb513 lb488 lb496 5 lb493 = true := by decide +kernel
def lb510 : List NodeSpec := lb493
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb503 : checkNodesBT lb530 lb506 lb507 lb513 lb488 lb496 5 lb510 = true := lb528
def lb498 : BT (List (List Nat)) := buildBucketsBT lb530 lb510
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb499 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb506 5 xs.toFinset) lb498 := buildBucketsBT_sound (by decide) lb512 lb531 lb514 lb489 lb497 lb503
def lb494 : List NodeSpec := [([0,1,2,3,4],[0,1,2,3,4,5],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb529 : checkNodesBT lb530 lb506 lb507 lb513 lb488 lb498 6 lb494 = true := by decide +kernel
def lb511 : List NodeSpec := lb494
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb504 : checkNodesBT lb530 lb506 lb507 lb513 lb488 lb498 6 lb511 = true := lb529
def lb500 : BT (List (List Nat)) := buildBucketsBT lb530 lb511
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb501 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb506 6 xs.toFinset) lb500 := buildBucketsBT_sound (by decide) lb512 lb531 lb514 lb489 lb499 lb504
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma lb495 : Lower lb63 lb506 7 := lower_of_forestBT (essPairs := [(VAR 0,10,11),(VAR 1,9,11),(VAR 2,9,13),(VAR 3,3,11),(VAR 4,3,19)]) (by decide +kernel) lb501 (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q23d : Lower (varsOf 62) 0xfcf0f000ccc0c000fcf0f000ccc0c000 7 := by
  apply carry_of (swaps := [(4, 5), (2, 3), (3, 4), (1, 2), (2, 3), (0, 1), (1, 2), (0, 1)]) (roots2 := lb63) (T2 := lb506) _ lb495
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q23 : Lower (varsOf 62) 0xfffcfcccfff0f0c0fffcfcccfff0f0c0 7 := dualLower (by decide +kernel) (by decide +kernel) q23d
lemma lb614 : carryOK [(0,3),(0,2),(0,1)] lb110 lb100 lb257 lb254 = true := by decide +kernel
lemma lb610 : Lower lb110 lb100 4 := carry_of lb614 lb270
def lb568 : Nat := 0xeaeaeaeae8e8e8e8eaeaeaeae8e8e8e8
lemma lb616 : liftCheck 32 0 lb111 lb568 lb110 lb100 [(VAR 5,33,1)] = true := by decide +kernel
lemma lb615 : Lower lb111 lb568 5 := lift_of lb616 lb610
def lb569 : Nat := 0xfaaafaaaf0a0f0a0faaafaaaf0a0f0a0
def lb577 : List Nat := varsOf 45
def lb627 : List Nat := [5,5,12,12,13,33,33,37,41,41,44,44,5,5,5,12,12,12,33,33,33]
def lb621 : List Nat := [4,1,8,4,9,32,1,36,40,9,40,36,9,36,40,9,36,40,9,36,40]
def lb603 : Nat := fullMask 21
def lb586 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x1c73f3,0x49252),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x3fc9f,0x92889),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x38f1c,0x16d714),(0xffffffff00000000ffffffff00000000,0x1c0fe0,0x1b6da0)]
def lb580 : BT Decor := buildWiresBT 2 lb586 lb31
lemma lb609 : goodPairs lb569 lb627 lb621 := goodPairs_of (by decide +kernel)
lemma lb587 : ∀ x ∈ lb586, faithful lb627 lb621 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma lb581 : btAll (fun x => faithful lb627 lb621 x ∧ x.1 < 2^128) lb580 := buildWiresBT_faithful lb587
set_option maxRecDepth 500000 in
lemma lb583 : btAll (fun sw => swapsValid sw = true ∧ permWord sw lb569 = lb569) lb236 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma lb644 : btAll (fun o => ∀ p, o = some p → Slice lb577 lb569 p.1 p.2) lb28 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice lb577 lb569 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma lb595 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb569 2 xs.toFinset) lb16 := trivial
def lb625 : List NodeSpec := [([0,1,2,3],[],[])]
def lb574 : BT (Option BoundPool) := buildPoolsSubBT 1 lb580 lb577 lb28 lb252 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb601 : checkNodesBT lb580 lb569 lb603 lb574 lb236 lb16 3 lb625 = true := by decide +kernel
def lb596 : BT (List (List Nat)) := buildBucketsBT lb580 lb625
set_option maxRecDepth 500000 in
lemma lb597 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb569 3 xs.toFinset) lb596 :=
  buildBucketsBT_sound (by decide) lb609 lb581 (buildPoolsSubBT_sound lb644) lb583 lb595 lb601
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma lb607 : forestRootCheck lb577 lb569 [(VAR 0,5,4),(VAR 2,5,1),(VAR 3,12,4),(VAR 5,33,1)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma lb606 : bucketContainsBT lb596 lb577 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma lb617 : Lower lb577 lb569 4 := lower_of_forestBT lb607 lb597 lb606
def lb570 : Nat := 0xfeeafeeafeeafeeafeeafeeafeeafeea
lemma lb619 : liftCheck 1 0 lb5 lb570 lb257 lb254 [(VAR 0,1,0)] = true := by decide +kernel
lemma lb618 : Lower lb5 lb570 5 := lift_of lb619 lb270
def lb566 : Nat := 0xeeaaeeaacc88cc88eeaaeeaacc88cc88
def lb575 : List Nat := varsOf 43
lemma lb612 : carryOK [(1,2)] lb575 lb566 lb577 lb569 = true := by decide +kernel
lemma lb611 : Lower lb575 lb566 4 := carry_of lb612 lb617
def lb567 : Nat := 0xfeeafeeafce8fce8feeafeeafce8fce8
def lb576 : List Nat := varsOf 47
def lb626 : List Nat := [3,3,5,5,6,6,10,10,11,12,12,13,33,33,35,37,38,38,41,41,42,42,44,44,3,3,3,3,5,5,5,5,6,6,6,6,10,10,10,10,12,12,12,12,33,33,33,33]
def lb620 : List Nat := [2,1,4,1,4,2,8,2,9,8,4,9,32,1,34,36,36,34,40,9,40,34,40,36,9,34,36,40,9,34,36,40,9,34,36,40,9,34,36,40,9,34,36,40,9,34,36,40]
def lb602 : Nat := fullMask 48
def lb584 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf000ff0cf90f,0x11111108290a),(0xcccccccccccccccccccccccccccccccc,0xff0f3341f3,0x2222222240a1),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf0ff0c38e3c,0x444444818414),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xff000fc0fc0,0x9999995c0b40),(0xffffffff00000000ffffffff00000000,0xf00000fff000,0xeeeeeef7d000)]
def lb645 : List (Nat × Nat × Nat) := [(1,1,2),(2,5,3)]
def lb578 : BT Decor := buildWiresBT 3 lb584 lb645
def lb641 : List (Option (Nat × Nat)) := [some (subcubeFast 2 0,4),some (subcubeFast 8 0,5),some (subcubeFast 0 32,5),some (subcubeFast 32 0,5),some (subcubeFast 1 32,4),some (subcubeFast 4 0,4)]
def lb642 : BT (Option (Nat × Nat)) := btOfList 3 lb641
def lb628 : BT (Option PoolSpec) := btOfList 3 [some (0,[]),some (1,[]),some (2,[]),some (3,[]),some (4,[]),some (5,[])]
lemma lb608 : goodPairs lb567 lb626 lb620 := goodPairs_of (by decide +kernel)
lemma lb585 : ∀ x ∈ lb584, faithful lb626 lb620 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma lb579 : btAll (fun x => faithful lb626 lb620 x ∧ x.1 < 2^128) lb578 := buildWiresBT_faithful lb585
set_option maxRecDepth 500000 in
lemma lb582 : btAll (fun sw => swapsValid sw = true ∧ permWord sw lb567 = lb567) lb203 := btAll_ofList (autos_of (by decide +kernel))
lemma lb630 : sliceDirectCheck 2 0 0 lb576 lb567 lb577 lb569 = true := by decide +kernel
lemma lb629 : Slice lb576 lb567 (subcubeFast 2 0) 4 := slice_fast_direct lb630 lb617
lemma lb632 : sliceDirectCheck 8 0 0 lb576 lb567 lb111 lb568 = true := by decide +kernel
lemma lb631 : Slice lb576 lb567 (subcubeFast 8 0) 5 := slice_fast_direct lb632 lb615
lemma lb634 : sliceDirectCheck 0 32 0 lb576 lb567 lb5 lb570 = true := by decide +kernel
lemma lb633 : Slice lb576 lb567 (subcubeFast 0 32) 5 := slice_fast_direct lb634 lb618
lemma lb636 : sliceDirectCheck 32 0 0 lb576 lb567 lb5 lb255 = true := by decide +kernel
lemma lb635 : Slice lb576 lb567 (subcubeFast 32 0) 5 := slice_fast_direct lb636 lb271
lemma lb638 : sliceDirectCheck 1 32 0 lb576 lb567 lb257 lb254 = true := by decide +kernel
lemma lb637 : Slice lb576 lb567 (subcubeFast 1 32) 4 := slice_fast_direct lb638 lb270
lemma lb640 : sliceDirectCheck 4 0 0 lb576 lb567 lb575 lb566 = true := by decide +kernel
lemma lb639 : Slice lb576 lb567 (subcubeFast 4 0) 4 := slice_fast_direct lb640 lb611
set_option maxRecDepth 500000 in
lemma lb643 : btAll (fun o => ∀ p, o = some p → Slice lb576 lb567 p.1 p.2) lb642 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice lb576 lb567 p.1 p.2) (forall_cons (fun _ h => by cases h; exact lb629) (forall_cons (fun _ h => by cases h; exact lb631) (forall_cons (fun _ h => by cases h; exact lb633) (forall_cons (fun _ h => by cases h; exact lb635) (forall_cons (fun _ h => by cases h; exact lb637) (forall_cons (fun _ h => by cases h; exact lb639) (fun _ h => (List.not_mem_nil h).elim)))))))
lemma lb588 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb567 3 xs.toFinset) lb16 := trivial
def lb622 : List NodeSpec := [([6,0,1,2,4],[],[])]
def lb571 : BT (Option BoundPool) := buildPoolsSubBT 3 lb578 lb576 lb642 lb628 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb598 : checkNodesBT lb578 lb567 lb602 lb571 lb203 lb16 4 lb622 = true := by decide +kernel
def lb589 : BT (List (List Nat)) := buildBucketsBT lb578 lb622
set_option maxRecDepth 500000 in
lemma lb590 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb567 4 xs.toFinset) lb589 :=
  buildBucketsBT_sound (by decide) lb608 lb579 (buildPoolsSubBT_sound lb643) lb582 lb588 lb598
def lb623 : List NodeSpec := [([0,1,2,5,3,4],[0,1,2,3],[0])]
def lb572 : BT (Option BoundPool) := buildPoolsSubBT 3 lb578 lb576 lb642 lb628 [0,1,2,3]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb599 : checkNodesBT lb578 lb567 lb602 lb572 lb203 lb589 5 lb623 = true := by decide +kernel
def lb591 : BT (List (List Nat)) := buildBucketsBT lb578 lb623
set_option maxRecDepth 500000 in
lemma lb592 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb567 5 xs.toFinset) lb591 :=
  buildBucketsBT_sound (by decide) lb608 lb579 (buildPoolsSubBT_sound lb643) lb582 lb590 lb599
def lb624 : List NodeSpec := [([0,1,2,3,4],[4,1,3,0,5],[0])]
def lb573 : BT (Option BoundPool) := buildPoolsSubBT 3 lb578 lb576 lb642 lb628 [0,1,3,4,5]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb600 : checkNodesBT lb578 lb567 lb602 lb573 lb203 lb591 6 lb624 = true := by decide +kernel
def lb593 : BT (List (List Nat)) := buildBucketsBT lb578 lb624
set_option maxRecDepth 500000 in
lemma lb594 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb567 6 xs.toFinset) lb593 :=
  buildBucketsBT_sound (by decide) lb608 lb579 (buildPoolsSubBT_sound lb643) lb582 lb592 lb600
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma lb605 : forestRootCheck lb576 lb567 [(VAR 0,3,2),(VAR 1,3,1),(VAR 2,5,1),(VAR 3,10,2),(VAR 5,33,1)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma lb604 : bucketContainsBT lb593 lb576 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma lb613 : Lower lb576 lb567 7 := lower_of_forestBT lb605 lb594 lb604
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q24 : Lower (varsOf 61) 0xfffafaaafff0faa0fffafaaafff0faa0 7 := by
  apply carry_of (swaps := [(3, 4), (2, 3), (1, 2)]) (roots2 := lb576) (T2 := lb567) _ lb613
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q25d : Lower (varsOf 59) 0xeeaaee0088888800eeaaee0088888800 7 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (3, 4), (2, 3)]) (roots2 := lb63) (T2 := lb506) _ lb495
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q25 : Lower (varsOf 59) 0xffeeeeeeff88aa88ffeeeeeeff88aa88 7 := dualLower (by decide +kernel) (by decide +kernel) q25d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q26 : Lower (varsOf 55) 0xfefeeeeef8f8e8e8fefeeeeef8f8e8e8 7 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (0, 1), (1, 2)]) (roots2 := lb576) (T2 := lb567) _ lb613
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q27 : Lower (varsOf 47) 0xfeeefeeefae8fae8feeefeeefae8fae8 7 := by
  apply carry_of (swaps := [(4, 5)]) (roots2 := lb63) (T2 := lb55) _ lb50
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q28 : Lower (varsOf 15) 0xfee8fee8fee8fee8fee8fee8fee8fee8 7 := by
  apply carry_of (swaps := [(4, 5), (3, 4)]) (roots2 := lb111) (T2 := lb101) _ lb170
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q29 : Lower (varsOf 23) 0xfefee8e8fefee8e8fefee8e8fefee8e8 7 := by
  apply carry_of (swaps := [(4, 5)]) (roots2 := lb111) (T2 := lb101) _ lb170
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q30 : Lower (varsOf 45) 0xfaaafaaafaa0faa0faaafaaafaa0faa0 5 := by
  apply carry_of (swaps := [(4, 5), (2, 3), (3, 4), (0, 1)]) (roots2 := lb232) (T2 := lb229) _ lb248
  decide +kernel
def lb97 : List Nat := [12,12,20,20,24,24,12,20,24]
def lb96 : List Nat := [8,4,16,4,16,8,16,8,4]
def lb84 : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xcf,0x10a),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x173,0xa1),(0xffff0000ffff0000ffff0000ffff0000,0x1bc,0x54)]
def lb81 : BT Decor := buildWiresBT 2 lb84 lb31
lemma lb92 : goodPairs lb316 lb97 lb96 := goodPairs_of (by decide +kernel)
lemma lb85 : ∀ x ∈ lb84, faithful lb97 lb96 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma lb82 : btAll (fun x => faithful lb97 lb96 x ∧ x.1 < 2^128) lb81 := buildWiresBT_faithful lb85
set_option maxRecDepth 500000 in
lemma lb83 : btAll (fun sw => swapsValid sw = true ∧ permWord sw lb316 = lb316) lb236 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma lb98 : btAll (fun o => ∀ p, o = some p → Slice lb330 lb316 p.1 p.2) lb28 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice lb330 lb316 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma lb86 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb316 2 xs.toFinset) lb16 := trivial
def lb80 : BT (Option BoundPool) := buildPoolsSubBT 1 lb81 lb330 lb28 lb252 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma lb89 : checkNodesBT lb81 lb316 lb159 lb80 lb236 lb16 3 lb180 = true := by decide +kernel
def lb87 : BT (List (List Nat)) := buildBucketsBT lb81 lb180
set_option maxRecDepth 500000 in
lemma lb88 : btAll (fun bk => ∀ xs ∈ bk, Impossible lb316 3 xs.toFinset) lb87 :=
  buildBucketsBT_sound (by decide) lb92 lb82 (buildPoolsSubBT_sound lb98) lb83 lb86 lb89
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma lb91 : forestRootCheck lb330 lb316 [(VAR 2,12,8),(VAR 3,12,4),(VAR 4,20,4)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma lb90 : bucketContainsBT lb87 lb330 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma lb93 : Lower lb330 lb316 4 := lower_of_forestBT lb91 lb88 lb90
def lb79 : Nat := 0xfffffffffff0f000fffffffffff0f000
lemma lb95 : liftCheck 32 0 lb334 lb79 lb330 lb316 [(VAR 5,32,0)] = true := by decide +kernel
lemma lb94 : Lower lb334 lb79 5 := lift_of lb95 lb93
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q31 : Lower (varsOf 43) 0xffeeffeeff88ff88ffeeffeeff88ff88 5 := by
  apply carry_of (swaps := [(4, 5), (1, 2), (2, 3), (3, 4), (0, 1), (1, 2)]) (roots2 := lb334) (T2 := lb79) _ lb94
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q32 : Lower (varsOf 39) 0xfefefefef8f8f8f8fefefefef8f8f8f8 5 := by
  apply carry_of (swaps := [(4, 5), (1, 2), (2, 3), (3, 4), (0, 1), (1, 2), (2, 3)]) (roots2 := lb334) (T2 := lb79) _ lb94
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q33 : Lower (varsOf 23) 0xf8f8e8e8f8f8e8e8f8f8e8e8f8f8e8e8 5 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (3, 4), (0, 1), (1, 2), (2, 3), (0, 1), (1, 2)]) (roots2 := lb232) (T2 := lb229) _ lb248
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q34 : Lower (varsOf 54) 0xfcfcccccfcfcc0c0fcfcccccfcfcc0c0 5 := by
  apply carry_of (swaps := [(4, 5), (2, 3)]) (roots2 := lb232) (T2 := lb229) _ lb248
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q35 : Lower (varsOf 51) 0xeeeeeeeecccc8888eeeeeeeecccc8888 5 := by
  apply carry_of (swaps := [(2, 3), (0, 1), (1, 2), (0, 1)]) (roots2 := lb232) (T2 := lb229) _ lb248
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q36 : Lower (varsOf 57) 0xffaaaaaaff00aa00ffaaaaaaff00aa00 4 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (1, 2), (2, 3), (3, 4), (1, 2), (2, 3)]) (roots2 := lb5) (T2 := lb287) _ lb282
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q37 : Lower (varsOf 54) 0xfcfcccccf0f0c0c0fcfcccccf0f0c0c0 4 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (1, 2), (2, 3), (3, 4), (1, 2), (0, 1)]) (roots2 := lb5) (T2 := lb287) _ lb282
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q38 : Lower (varsOf 53) 0xfafaaaaaf0f0a0a0fafaaaaaf0f0a0a0 4 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (1, 2), (2, 3), (3, 4), (1, 2)]) (roots2 := lb5) (T2 := lb287) _ lb282
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q39 : Lower (varsOf 28) 0xfff0f000fff0f000fff0f000fff0f000 4 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (1, 2), (2, 3), (0, 1), (1, 2)]) (roots2 := lb110) (T2 := lb100) _ lb302
  decide +kernel
def s2NR : List Nat := varsOf 63
def s2NG : Nat := 0xfffefeeefff8fae8fffefeeefff8fae8
def s2NPos : List Nat := [3,3,3,3,3,5,5,5,5,5,6,6,6,6,6,9,9,9,9,11,12,12,12,12,14,19,19,19,20,20,20,20,21,22,22,24,24,24,24,25,26,26,33,33,33,34,34,37,38,41,42,42,44,44,49,49,50,50,52,52,56,56]
def s2NNeg : List Nat := [0,1,2,17,18,1,4,10,17,36,0,2,4,10,36,1,8,10,17,10,0,4,8,10,10,16,17,18,4,16,17,18,17,4,18,8,16,17,18,17,10,18,1,17,32,2,32,36,36,40,10,40,36,40,17,48,18,48,36,48,40,48]
def s2NMask : Nat := fullMask 62
def s2NBase : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xc29c810e0f83ff,0x400ca14404812a),(0xcccccccccccccccccccccccccccccccc,0x30d63060f087c1f,0x1042344898a2894),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xc318007f1f07fe0,0x411800210205240),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x303e03f801ff8000,0x102e010801cb2080),(0xffff0000ffff0000ffff0000ffff0000,0x3fc003fffe000000,0x2bc00af5ee040118),(0xffffffff00000000ffffffff00000000,0x3ffffc0000000000,0x3ebbd00000004200)]
def s2NSteps : List (Nat × Nat × Nat) := [(1,0,1),(1,0,2),(1,1,2),(1,6,3),(1,8,3),(2,8,3),(3,1,7),(1,1,3),(1,2,3),(1,6,2),(3,2,13),(1,15,3),(2,15,3),(3,2,9),(2,6,5),(1,20,2),(2,14,4),(1,2,4),(1,3,4),(1,0,3),(3,1,25),(1,2,5),(2,7,3),(1,0,4),(1,12,3),(2,12,3),(1,7,3),(3,2,25),(1,26,2),(1,33,1),(3,2,5),(3,1,29),(3,0,4),(1,0,5),(3,0,13),(1,40,2),(1,1,4),(1,1,5),(1,3,5),(1,4,5)]
def s2NW : BT Decor := buildWiresBT 6 s2NBase s2NSteps
def s2NAutoList : List (List (Nat × Nat)) := [[],[(0,2),(1,3),(4,5)]]
def s2NAutos : BT (List (Nat × Nat)) := btOfList 1 s2NAutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NPairs : goodPairs s2NG s2NPos s2NNeg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NBaseOk : ∀ x ∈ s2NBase, faithful s2NPos s2NNeg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NWOk : btAll (fun x => faithful s2NPos s2NNeg x ∧ x.1 < 2^128) s2NW := buildWiresBT_faithful s2NBaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NAutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw s2NG = s2NG) s2NAutos := btAll_ofList (autos_of (by decide +kernel))
def s2NSliceList : List (Option (Nat × Nat)) := [some (subcubeFast 1 0,7),some (subcubeFast 2 0,7),some (subcubeFast 4 0,7),some (subcubeFast 8 0,7),some (subcubeFast 16 0,7),some (0xcccc333300000000cccc3333,7),some (0xff00000000ff0000ff00000000ff,7),some (0xff0000000000ff00ff0000000000ff,7),some (subcubeFast 18 0,5),some (subcubeFast 4 16,5),some (subcubeFast 20 0,5),some (subcubeFast 8 16,5),some (subcubeFast 40 0,5),some (0x44114411441144114411441144114411,5),some (0xc030c030c030c030c030c030c030c03,5),some (subcubeFast 6 0,4),some (subcubeFast 9 0,4),some (subcubeFast 10 0,4),some (subcubeFast 12 16,4),some (subcubeFast 28 0,4),some (subcubeFast 3 32,4),some (subcubeFast 35 0,4),some (subcubeFast 50 0,4),some (subcubeFast 56 0,4)]
def s2NSlices : BT (Option (Nat × Nat)) := btOfList 5 s2NSliceList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice0 : Slice s2NR s2NG (subcubeFast 1 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 62) (qGoal := 0xfffcfcccfff0f0c0fffcfcccfff0f0c0) (by decide +kernel) q23
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice1 : Slice s2NR s2NG (subcubeFast 2 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 61) (qGoal := 0xfffafaaafff0faa0fffafaaafff0faa0) (by decide +kernel) q24
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice2 : Slice s2NR s2NG (subcubeFast 4 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 59) (qGoal := 0xffeeeeeeff88aa88ffeeeeeeff88aa88) (by decide +kernel) q25
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice3 : Slice s2NR s2NG (subcubeFast 8 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 55) (qGoal := 0xfefeeeeef8f8e8e8fefeeeeef8f8e8e8) (by decide +kernel) q26
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice4 : Slice s2NR s2NG (subcubeFast 16 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 47) (qGoal := 0xfeeefeeefae8fae8feeefeeefae8fae8) (by decide +kernel) q27
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice5 : Slice s2NR s2NG 0xcccc333300000000cccc3333 7 := mappedSlice (f := identifyRow 32 0 1 4) (R := varsOf 15) (G := 0xfee8fee8fee8fee8fee8fee8fee8fee8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) q28
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice6 : Slice s2NR s2NG 0xff00000000ff0000ff00000000ff 7 := mappedSlice (f := identifyRow 16 0 3 5) (R := varsOf 15) (G := 0xfee8fee8fee8fee8fee8fee8fee8fee8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) q28
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice7 : Slice s2NR s2NG 0xff0000000000ff00ff0000000000ff 7 := mappedSlice (f := identifyRow 8 0 4 5) (R := varsOf 23) (G := 0xfefee8e8fefee8e8fefee8e8fefee8e8) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) q29
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice8 : Slice s2NR s2NG (subcubeFast 18 0) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 45) (qGoal := 0xfaaafaaafaa0faa0faaafaaafaa0faa0) (by decide +kernel) q30
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice9 : Slice s2NR s2NG (subcubeFast 4 16) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 43) (qGoal := 0xffeeffeeff88ff88ffeeffeeff88ff88) (by decide +kernel) q31
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice10 : Slice s2NR s2NG (subcubeFast 20 0) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 43) (qGoal := 0xeeeeeeeeaa88aa88eeeeeeeeaa88aa88) (by decide +kernel) q9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice11 : Slice s2NR s2NG (subcubeFast 8 16) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 39) (qGoal := 0xfefefefef8f8f8f8fefefefef8f8f8f8) (by decide +kernel) q32
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice12 : Slice s2NR s2NG (subcubeFast 40 0) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 23) (qGoal := 0xf8f8e8e8f8f8e8e8f8f8e8e8f8f8e8e8) (by decide +kernel) q33
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice13 : Slice s2NR s2NG 0x44114411441144114411441144114411 5 := mappedSlice (f := identifyRow 1 0 1 3) (R := varsOf 54) (G := 0xfcfcccccfcfcc0c0fcfcccccfcfcc0c0) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) q34
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice14 : Slice s2NR s2NG 0xc030c030c030c030c030c030c030c03 5 := mappedSlice (f := identifyRow 4 0 1 3) (R := varsOf 51) (G := 0xeeeeeeeecccc8888eeeeeeeecccc8888) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) q35
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice15 : Slice s2NR s2NG (subcubeFast 6 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 57) (qGoal := 0xffaaaaaaff00aa00ffaaaaaaff00aa00) (by decide +kernel) q36
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice16 : Slice s2NR s2NG (subcubeFast 9 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 54) (qGoal := 0xfcfcccccf0f0c0c0fcfcccccf0f0c0c0) (by decide +kernel) q37
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice17 : Slice s2NR s2NG (subcubeFast 10 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 53) (qGoal := 0xfafaaaaaf0f0a0a0fafaaaaaf0f0a0a0) (by decide +kernel) q38
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice18 : Slice s2NR s2NG (subcubeFast 12 16) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 35) (qGoal := 0xeeeeeeee88888888eeeeeeee88888888) (by decide +kernel) q14
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice19 : Slice s2NR s2NG (subcubeFast 28 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 35) (qGoal := 0xeeeeeeee88888888eeeeeeee88888888) (by decide +kernel) q14
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice20 : Slice s2NR s2NG (subcubeFast 3 32) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 28) (qGoal := 0xfff0f000fff0f000fff0f000fff0f000) (by decide +kernel) q39
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice21 : Slice s2NR s2NG (subcubeFast 35 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 28) (qGoal := 0xfff0f000fff0f000fff0f000fff0f000) (by decide +kernel) q39
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice22 : Slice s2NR s2NG (subcubeFast 50 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 13) (qGoal := 0xfaa0faa0faa0faa0faa0faa0faa0faa0) (by decide +kernel) q17
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice23 : Slice s2NR s2NG (subcubeFast 56 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 7) (qGoal := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8) (by decide +kernel) q18
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlicesOk : btAll (fun o => ∀ p, o = some p → Slice s2NR s2NG p.1 p.2) s2NSlices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice s2NR s2NG p.1 p.2) (forall_cons (fun _ h => by cases h; exact s2NSlice0) (forall_cons (fun _ h => by cases h; exact s2NSlice1) (forall_cons (fun _ h => by cases h; exact s2NSlice2) (forall_cons (fun _ h => by cases h; exact s2NSlice3) (forall_cons (fun _ h => by cases h; exact s2NSlice4) (forall_cons (fun _ h => by cases h; exact s2NSlice5) (forall_cons (fun _ h => by cases h; exact s2NSlice6) (forall_cons (fun _ h => by cases h; exact s2NSlice7) (forall_cons (fun _ h => by cases h; exact s2NSlice8) (forall_cons (fun _ h => by cases h; exact s2NSlice9) (forall_cons (fun _ h => by cases h; exact s2NSlice10) (forall_cons (fun _ h => by cases h; exact s2NSlice11) (forall_cons (fun _ h => by cases h; exact s2NSlice12) (forall_cons (fun _ h => by cases h; exact s2NSlice13) (forall_cons (fun _ h => by cases h; exact s2NSlice14) (forall_cons (fun _ h => by cases h; exact s2NSlice15) (forall_cons (fun _ h => by cases h; exact s2NSlice16) (forall_cons (fun _ h => by cases h; exact s2NSlice17) (forall_cons (fun _ h => by cases h; exact s2NSlice18) (forall_cons (fun _ h => by cases h; exact s2NSlice19) (forall_cons (fun _ h => by cases h; exact s2NSlice20) (forall_cons (fun _ h => by cases h; exact s2NSlice21) (forall_cons (fun _ h => by cases h; exact s2NSlice22) (forall_cons (fun _ h => by cases h; exact s2NSlice23) (fun _ h => (List.not_mem_nil h).elim)))))))))))))))))))))))))
def s2NEmpty : BT (List (List Nat)) := BT.empty
lemma s2NEmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible s2NG (5 - 1) xs.toFinset) s2NEmpty := trivial
def s2NBlock5_0Specs : List PoolSpec := [(0,[])]
def s2NBlock5_0Pools : BT (Option BoundPool) := buildPoolsBT 1 s2NW s2NR s2NSlices s2NBlock5_0Specs
def s2NBlock5_0 : List NodeSpec := [([20,22,0,1,2,3],[],[]),([28,1,7,25,4,27],[],[]),([11,6,7,3,4,5],[],[]),([6,7,3,10,4,5],[0],[]),([6,7,13,14,4,5],[],[]),([7,8,3,9,4,5],[],[]),([7,8,25,13,4,5],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NBlock5_0Ok : checkNodesBT s2NW s2NG s2NMask s2NBlock5_0Pools s2NAutos s2NEmpty 5 s2NBlock5_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NBlock5_0Mem : ∀ ns ∈ s2NBlock5_0, Impossible s2NG 5 (nodeValsBT s2NW ns).toFinset := checkNodesBT_mem (by decide) s2NPairs s2NWOk (buildPoolsBT_sound s2NSlicesOk) s2NAutosOk s2NEmptyOk s2NBlock5_0Ok
def s2NNodes5 : List NodeSpec := s2NBlock5_0
def s2NBucket5 : BT (List (List Nat)) := buildBucketsBT s2NW s2NNodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NBucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s2NG 5 xs.toFinset) s2NBucket5 := buildBucketsBT_of_mem s2NBlock5_0Mem
def s2NBlock6_0Specs : List PoolSpec := [(0,[]),(20,[]),(5,[]),(22,[]),(18,[])]
def s2NBlock6_0Pools : BT (Option BoundPool) := buildPoolsBT 3 s2NW s2NR s2NSlices s2NBlock6_0Specs
def s2NBlock6_0 : List NodeSpec := [([20,0,1,2,3,14,4],[3],[0]),([20,0,1,2,3,4,23],[],[]),([20,0,1,2,3,4,24],[],[]),([31,0,1,2,3,4,5],[],[]),([28,0,1,2,25,4,5],[4],[]),([28,1,2,7,25,4,5],[0],[0]),([11,0,6,2,3,4,5],[],[0]),([18,0,1,2,3,4,5],[],[]),([33,0,1,2,13,4,5],[4],[]),([16,0,1,2,25,4,5],[4],[]),([16,0,6,2,3,4,5],[0],[]),([19,0,1,2,3,4,5],[1,2],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NBlock6_0Ok : checkNodesBT s2NW s2NG s2NMask s2NBlock6_0Pools s2NAutos s2NBucket5 6 s2NBlock6_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NBlock6_0Mem : ∀ ns ∈ s2NBlock6_0, Impossible s2NG 6 (nodeValsBT s2NW ns).toFinset := checkNodesBT_mem (by decide) s2NPairs s2NWOk (buildPoolsBT_sound s2NSlicesOk) s2NAutosOk s2NBucket5Ok s2NBlock6_0Ok
def s2NBlock6_1Specs : List PoolSpec := [(0,[]),(20,[]),(9,[]),(12,[]),(8,[]),(21,[]),(5,[]),(4,[])]
def s2NBlock6_1Pools : BT (Option BoundPool) := buildPoolsBT 3 s2NW s2NR s2NSlices s2NBlock6_1Specs
def s2NBlock6_1 : List NodeSpec := [([12,0,2,15,3,4,5],[1,5],[]),([12,1,2,7,3,29,5],[1],[1]),([12,6,2,7,3,4,5],[1],[]),([26,1,2,7,3,4,5],[1],[1]),([0,1,35,2,3,4,5],[1,6],[]),([0,1,2,21,3,4],[1],[]),([0,1,2,34,3,4,5],[],[]),([0,1,2,41,3,4,5],[2,7],[]),([0,1,2,3,30,4,5],[2,4],[]),([0,1,2,3,17,4,5],[1,2,6],[]),([0,6,2,3,10,4,5],[0],[0]),([0,6,2,13,14,4,5],[3,4],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NBlock6_1Ok : checkNodesBT s2NW s2NG s2NMask s2NBlock6_1Pools s2NAutos s2NBucket5 6 s2NBlock6_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NBlock6_1Mem : ∀ ns ∈ s2NBlock6_1, Impossible s2NG 6 (nodeValsBT s2NW ns).toFinset := checkNodesBT_mem (by decide) s2NPairs s2NWOk (buildPoolsBT_sound s2NSlicesOk) s2NAutosOk s2NBucket5Ok s2NBlock6_1Ok
def s2NBlock6_2Specs : List PoolSpec := [(20,[]),(9,[]),(12,[]),(21,[]),(13,[]),(18,[])]
def s2NBlock6_2Pools : BT (Option BoundPool) := buildPoolsBT 3 s2NW s2NR s2NSlices s2NBlock6_2Specs
def s2NBlock6_2 : List NodeSpec := [([0,2,8,3,9,4,5],[0,1],[0]),([0,2,8,25,13,4,5],[0,5],[0]),([0,2,15,3,13,4,5],[0,2],[]),([1,6,7,3,14,4,5],[],[0,1]),([1,2,7,15,3,29,5],[0,3],[]),([1,2,7,3,9,4,5],[0,1],[0,1]),([1,2,7,25,13,4,5],[0],[0,1]),([1,2,3,25,9,29,5],[0,3],[]),([1,2,25,13,29,5],[0,4,5],[]),([1,7,8,3,25,4,5],[],[0,1]),([1,7,3,25,4,27],[0,5],[0]),([1,7,3,29,27],[0,5],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NBlock6_2Ok : checkNodesBT s2NW s2NG s2NMask s2NBlock6_2Pools s2NAutos s2NBucket5 6 s2NBlock6_2 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NBlock6_2Mem : ∀ ns ∈ s2NBlock6_2, Impossible s2NG 6 (nodeValsBT s2NW ns).toFinset := checkNodesBT_mem (by decide) s2NPairs s2NWOk (buildPoolsBT_sound s2NSlicesOk) s2NAutosOk s2NBucket5Ok s2NBlock6_2Ok
def s2NBlock6_3Specs : List PoolSpec := [(20,[]),(9,[]),(17,[])]
def s2NBlock6_3Pools : BT (Option BoundPool) := buildPoolsBT 2 s2NW s2NR s2NSlices s2NBlock6_3Specs
def s2NBlock6_3 : List NodeSpec := [([6,2,7,3,13,4,5],[0,2],[0]),([6,7,8,3,4,5],[0,1],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NBlock6_3Ok : checkNodesBT s2NW s2NG s2NMask s2NBlock6_3Pools s2NAutos s2NBucket5 6 s2NBlock6_3 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NBlock6_3Mem : ∀ ns ∈ s2NBlock6_3, Impossible s2NG 6 (nodeValsBT s2NW ns).toFinset := checkNodesBT_mem (by decide) s2NPairs s2NWOk (buildPoolsBT_sound s2NSlicesOk) s2NAutosOk s2NBucket5Ok s2NBlock6_3Ok
def s2NNodes6 : List NodeSpec := s2NBlock6_0 ++ s2NBlock6_1 ++ s2NBlock6_2 ++ s2NBlock6_3
def s2NBucket6 : BT (List (List Nat)) := buildBucketsBT s2NW s2NNodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NBucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s2NG 6 xs.toFinset) s2NBucket6 := buildBucketsBT_of_mem (forall_append (forall_append (forall_append s2NBlock6_0Mem s2NBlock6_1Mem) s2NBlock6_2Mem) s2NBlock6_3Mem)
def s2NBlock7_0Specs : List PoolSpec := [(20,[]),(9,[]),(17,[]),(11,[]),(21,[]),(5,[]),(22,[]),(2,[(1,0,1),(2,6,5)]),(3,[(1,0,1),(2,6,5)]),(18,[]),(16,[]),(2,[(3,1,7)]),(4,[]),(19,[])]
def s2NBlock7_0Pools : BT (Option BoundPool) := buildPoolsBT 4 s2NW s2NR s2NSlices s2NBlock7_0Specs
def s2NBlock7_0 : List NodeSpec := [([20,0,1,2,3,4],[0,6,7,8],[0]),([33,0,1,2,3,4,5],[0,5,9,10],[0]),([36,38,0,1,2,3],[4,13],[]),([36,0,1,2,3,25,4],[4,9],[]),([36,0,1,2,3,29],[4,9],[]),([12,0,1,2,7,3,4,5],[0,1],[0,1]),([12,0,1,2,3,4,5],[0,3,5,11],[0]),([26,0,1,2,3,4,5],[0,1,4,5,10],[0,1]),([37,0,1,2,3,4,5],[0,9],[]),([37,0,1,2,3,29,5],[0,9],[]),([40,0,1,2,3,4,5],[0,1,2,4,12],[0,1]),([38,0,1,2,3,13,5],[0,13],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NBlock7_0Ok : checkNodesBT s2NW s2NG s2NMask s2NBlock7_0Pools s2NAutos s2NBucket6 7 s2NBlock7_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NBlock7_0Mem : ∀ ns ∈ s2NBlock7_0, Impossible s2NG 7 (nodeValsBT s2NW ns).toFinset := checkNodesBT_mem (by decide) s2NPairs s2NWOk (buildPoolsBT_sound s2NSlicesOk) s2NAutosOk s2NBucket6Ok s2NBlock7_0Ok
def s2NBlock7_1Specs : List PoolSpec := [(20,[]),(9,[]),(17,[]),(15,[]),(12,[]),(8,[]),(21,[]),(23,[]),(13,[]),(22,[]),(14,[]),(10,[]),(18,[]),(16,[])]
def s2NBlock7_1Pools : BT (Option BoundPool) := buildPoolsBT 4 s2NW s2NR s2NSlices s2NBlock7_1Specs
def s2NBlock7_1 : List NodeSpec := [([0,1,6,2,3,14,4,5],[0,4,5,10],[0,1]),([0,1,6,2,3,4,23,5],[1,9,11],[0]),([0,1,6,2,3,4,24,5],[1,7],[0]),([0,1,2,7,15,3,4,5],[0,3,6],[0]),([0,1,2,7,3,13,4,5],[0,2,12],[0,1]),([0,1,2,8,3,25,4,5],[0,3,8,12],[0,1]),([0,1,2,15,3,4,5],[0,1,3,6,7],[0]),([0,1,2,3,25,9,4,5],[0,2,4,8],[0]),([0,1,2,3,25,32,4,5],[7,12,13],[0]),([0,1,2,3,25,4,27],[0,12],[0]),([0,1,2,3,13,9,4,5],[0,2,4,8],[]),([0,1,2,3,13,29,5],[0,12],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NBlock7_1Ok : checkNodesBT s2NW s2NG s2NMask s2NBlock7_1Pools s2NAutos s2NBucket6 7 s2NBlock7_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NBlock7_1Mem : ∀ ns ∈ s2NBlock7_1, Impossible s2NG 7 (nodeValsBT s2NW ns).toFinset := checkNodesBT_mem (by decide) s2NPairs s2NWOk (buildPoolsBT_sound s2NSlicesOk) s2NAutosOk s2NBucket6Ok s2NBlock7_1Ok
def s2NBlock7_2Specs : List PoolSpec := [(20,[]),(9,[]),(17,[]),(2,[(1,0,1)]),(15,[]),(12,[]),(8,[]),(3,[(1,0,1)]),(11,[]),(21,[]),(5,[]),(13,[]),(10,[]),(18,[]),(16,[])]
def s2NBlock7_2Pools : BT (Option BoundPool) := buildPoolsBT 4 s2NW s2NR s2NSlices s2NBlock7_2Specs
def s2NBlock7_2 : List NodeSpec := [([0,1,2,3,9,4,5],[0,1,2,7,9,10,11],[0,1]),([0,1,2,3,4,23,5,39],[1,12],[]),([0,1,2,3,29,27],[0,13],[0]),([0,1,2,25,13,4,5],[0,2,6,8,9,11],[0,1]),([0,6,2,8,3,4,5],[0,1,3,4],[0]),([0,6,2,3,13,4,5],[0,2,5,6,7,8,9],[0]),([1,6,2,7,3,4,5],[0,1,3],[0]),([1,2,7,3,25,4,5],[0,13,14],[0,1]),([1,2,7,3,29,5],[0,9,13],[0,1]),([1,2,3,25,29,5],[0,9,13,14],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NBlock7_2Ok : checkNodesBT s2NW s2NG s2NMask s2NBlock7_2Pools s2NAutos s2NBucket6 7 s2NBlock7_2 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NBlock7_2Mem : ∀ ns ∈ s2NBlock7_2, Impossible s2NG 7 (nodeValsBT s2NW ns).toFinset := checkNodesBT_mem (by decide) s2NPairs s2NWOk (buildPoolsBT_sound s2NSlicesOk) s2NAutosOk s2NBucket6Ok s2NBlock7_2Ok
def s2NNodes7 : List NodeSpec := s2NBlock7_0 ++ s2NBlock7_1 ++ s2NBlock7_2
def s2NBucket7 : BT (List (List Nat)) := buildBucketsBT s2NW s2NNodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NBucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s2NG 7 xs.toFinset) s2NBucket7 := buildBucketsBT_of_mem (forall_append (forall_append s2NBlock7_0Mem s2NBlock7_1Mem) s2NBlock7_2Mem)
def s2NBlock8_0Specs : List PoolSpec := [(0,[]),(20,[]),(9,[]),(17,[]),(2,[(1,0,1)]),(12,[]),(8,[]),(3,[(1,0,1)]),(21,[]),(5,[]),(23,[]),(22,[]),(10,[]),(18,[]),(16,[]),(5,[(1,0,2)]),(2,[]),(3,[]),(4,[]),(19,[]),(6,[]),(2,[(1,0,5)]),(1,[]),(2,[(1,1,5)])]
def s2NBlock8_0Pools : BT (Option BoundPool) := buildPoolsBT 5 s2NW s2NR s2NSlices s2NBlock8_0Specs
def s2NBlock8_0 : List NodeSpec := [([38,0,1,2,3,5],[0,1,8,19,20],[0,1]),([0,1,6,2,3,4,5],[1,2,4,6,7,8,9],[0]),([0,1,2,7,3,4,5],[0,1,12,13,15,16],[0,1]),([0,1,2,3,25,4,5],[0,1,10,13,14,17],[0,1]),([0,1,2,3,13,4,5],[1,3,5,11,13,17,22],[0,1]),([0,1,2,3,4,29,5],[1,9,13,18],[0]),([0,1,2,3,4,42,5],[11,13],[]),([0,1,2,3,4,5,39],[1,8,10,21],[0,1]),([0,1,2,3,4,5,43],[1,5,11,23],[1]),([0,1,2,3,4,5,45],[1,13],[]),([0,1,2,3,29,5],[0,1,8,13,18],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NBlock8_0Ok : checkNodesBT s2NW s2NG s2NMask s2NBlock8_0Pools s2NAutos s2NBucket7 8 s2NBlock8_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NBlock8_0Mem : ∀ ns ∈ s2NBlock8_0, Impossible s2NG 8 (nodeValsBT s2NW ns).toFinset := checkNodesBT_mem (by decide) s2NPairs s2NWOk (buildPoolsBT_sound s2NSlicesOk) s2NAutosOk s2NBucket7Ok s2NBlock8_0Ok
def s2NNodes8 : List NodeSpec := s2NBlock8_0
def s2NBucket8 : BT (List (List Nat)) := buildBucketsBT s2NW s2NNodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NBucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s2NG 8 xs.toFinset) s2NBucket8 := buildBucketsBT_of_mem s2NBlock8_0Mem
def s2NBlock9_0Specs : List PoolSpec := [(0,[]),(5,[]),(2,[]),(4,[]),(1,[]),(7,[])]
def s2NBlock9_0Pools : BT (Option BoundPool) := buildPoolsBT 3 s2NW s2NR s2NSlices s2NBlock9_0Specs
def s2NBlock9_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,4,5],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NBlock9_0Ok : checkNodesBT s2NW s2NG s2NMask s2NBlock9_0Pools s2NAutos s2NBucket8 9 s2NBlock9_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NBlock9_0Mem : ∀ ns ∈ s2NBlock9_0, Impossible s2NG 9 (nodeValsBT s2NW ns).toFinset := checkNodesBT_mem (by decide) s2NPairs s2NWOk (buildPoolsBT_sound s2NSlicesOk) s2NAutosOk s2NBucket8Ok s2NBlock9_0Ok
def s2NNodes9 : List NodeSpec := s2NBlock9_0
def s2NBucket9 : BT (List (List Nat)) := buildBucketsBT s2NW s2NNodes9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NBucket9Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s2NG 9 xs.toFinset) s2NBucket9 := buildBucketsBT_of_mem s2NBlock9_0Mem
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NBound : Lower s2NR s2NG 10 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 3,1,9),(VAR 4,4,20),(VAR 5,1,33)]) (by decide +kernel) s2NBucket9Ok (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q22 : Lower (varsOf 125) 0xfffffffafffafafaffffffaaffa0faa0 10 := by
  apply carry_of (swaps := [(5, 6), (3, 4), (4, 5), (3, 4), (2, 3), (1, 2)]) (roots2 := s2NR) (T2 := s2NG) _ s2NBound
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q40 : Lower (varsOf 126) 0xfffffffcfffcfcfcffffffc0ffccfcc0 10 := by
  apply carry_of (swaps := [(5, 6), (4, 5), (3, 4), (2, 3), (1, 2), (0, 1)]) (roots2 := s2NR) (T2 := s2NG) _ s2NBound
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q42 : Lower (varsOf 30) 0xfffcfcc0fffcfcc0fffcfcc0fffcfcc0 7 := by
  apply carry_of (swaps := [(4, 5), (2, 3), (1, 2), (0, 1)]) (roots2 := lb111) (T2 := lb101) _ lb170
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q43 : Lower (varsOf 51) 0xeeeeeeeeaaaa8888eeeeeeeeaaaa8888 5 := by
  apply carry_of (swaps := [(2, 3), (0, 1), (1, 2)]) (roots2 := lb232) (T2 := lb229) _ lb248
  decide +kernel
def s3NR : List Nat := varsOf 63
def s3NG : Nat := 0xfffefeeefffafce8fffefeeefffafce8
def s3NPos : List Nat := [3,3,5,5,6,6,10,10,12,12,17,17,20,20,24,24,33,34,41,41,44,50,50,52,56,56]
def s3NNeg : List Nat := [1,2,1,4,2,4,2,8,4,8,1,16,4,16,8,16,1,2,9,40,40,18,48,48,40,48]
def s3NMask : Nat := fullMask 26
def s3NBase : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xd0c0f,0x50405),(0xcccccccccccccccccccccccccccccccc,0x6200f3,0x220052),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x90333c,0x1128),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x31cc3c0,0x11c4280),(0xffff0000ffff0000ffff0000ffff0000,0x3e0fc00,0x2e0a800),(0xffffffff00000000ffffffff00000000,0x3ff0000,0x3d80000)]
def s3NSteps : List (Nat × Nat × Nat) := [(1,2,5),(3,2,5)]
def s3NW : BT Decor := buildWiresBT 3 s3NBase s3NSteps
def s3NAutoList : List (List (Nat × Nat)) := [[],[(0,1),(3,4)]]
def s3NAutos : BT (List (Nat × Nat)) := btOfList 1 s3NAutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s3NPairs : goodPairs s3NG s3NPos s3NNeg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s3NBaseOk : ∀ x ∈ s3NBase, faithful s3NPos s3NNeg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s3NWOk : btAll (fun x => faithful s3NPos s3NNeg x ∧ x.1 < 2^128) s3NW := buildWiresBT_faithful s3NBaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s3NAutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw s3NG = s3NG) s3NAutos := btAll_ofList (autos_of (by decide +kernel))
def s3NSliceList : List (Option (Nat × Nat)) := [some (0x33003300003300333300330000330033,7),some (0x55550000000055555555000000005555,7),some (subcubeFast 12 0,5),some (subcubeFast 28 0,4),some (subcubeFast 3 32,4),some (subcubeFast 35 0,4)]
def s3NSlices : BT (Option (Nat × Nat)) := btOfList 3 s3NSliceList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s3NSlice0 : Slice s3NR s3NG 0x33003300003300333300330000330033 7 := mappedSlice (f := identifyRow 2 0 3 5) (R := varsOf 29) (G := 0xfffafaa0fffafaa0fffafaa0fffafaa0) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) q4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s3NSlice1 : Slice s3NR s3NG 0x55550000000055555555000000005555 7 := mappedSlice (f := identifyRow 1 0 4 5) (R := varsOf 30) (G := 0xfffcfcc0fffcfcc0fffcfcc0fffcfcc0) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) q42
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s3NSlice2 : Slice s3NR s3NG (subcubeFast 12 0) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 51) (qGoal := 0xeeeeeeeeaaaa8888eeeeeeeeaaaa8888) (by decide +kernel) q43
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s3NSlice3 : Slice s3NR s3NG (subcubeFast 28 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 35) (qGoal := 0xeeeeeeee88888888eeeeeeee88888888) (by decide +kernel) q14
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s3NSlice4 : Slice s3NR s3NG (subcubeFast 3 32) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 28) (qGoal := 0xfff0f000fff0f000fff0f000fff0f000) (by decide +kernel) q39
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s3NSlice5 : Slice s3NR s3NG (subcubeFast 35 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 28) (qGoal := 0xfff0f000fff0f000fff0f000fff0f000) (by decide +kernel) q39
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s3NSlicesOk : btAll (fun o => ∀ p, o = some p → Slice s3NR s3NG p.1 p.2) s3NSlices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice s3NR s3NG p.1 p.2) (forall_cons (fun _ h => by cases h; exact s3NSlice0) (forall_cons (fun _ h => by cases h; exact s3NSlice1) (forall_cons (fun _ h => by cases h; exact s3NSlice2) (forall_cons (fun _ h => by cases h; exact s3NSlice3) (forall_cons (fun _ h => by cases h; exact s3NSlice4) (forall_cons (fun _ h => by cases h; exact s3NSlice5) (fun _ h => (List.not_mem_nil h).elim)))))))
def s3NEmpty : BT (List (List Nat)) := BT.empty
lemma s3NEmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible s3NG (7 - 1) xs.toFinset) s3NEmpty := trivial
def s3NBlock7_0Specs : List PoolSpec := [(4,[]),(2,[]),(5,[])]
def s3NBlock7_0Pools : BT (Option BoundPool) := buildPoolsBT 2 s3NW s3NR s3NSlices s3NBlock7_0Specs
def s3NBlock7_0 : List NodeSpec := [([7,0,1,2,3,4],[1,2],[]),([0,1,2,3,4,6],[0,1],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s3NBlock7_0Ok : checkNodesBT s3NW s3NG s3NMask s3NBlock7_0Pools s3NAutos s3NEmpty 7 s3NBlock7_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s3NBlock7_0Mem : ∀ ns ∈ s3NBlock7_0, Impossible s3NG 7 (nodeValsBT s3NW ns).toFinset := checkNodesBT_mem (by decide) s3NPairs s3NWOk (buildPoolsBT_sound s3NSlicesOk) s3NAutosOk s3NEmptyOk s3NBlock7_0Ok
def s3NNodes7 : List NodeSpec := s3NBlock7_0
def s3NBucket7 : BT (List (List Nat)) := buildBucketsBT s3NW s3NNodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s3NBucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s3NG 7 xs.toFinset) s3NBucket7 := buildBucketsBT_of_mem s3NBlock7_0Mem
def s3NBlock8_0Specs : List PoolSpec := [(4,[]),(5,[]),(3,[]),(0,[]),(1,[])]
def s3NBlock8_0Pools : BT (Option BoundPool) := buildPoolsBT 3 s3NW s3NR s3NSlices s3NBlock8_0Specs
def s3NBlock8_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,4],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s3NBlock8_0Ok : checkNodesBT s3NW s3NG s3NMask s3NBlock8_0Pools s3NAutos s3NBucket7 8 s3NBlock8_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s3NBlock8_0Mem : ∀ ns ∈ s3NBlock8_0, Impossible s3NG 8 (nodeValsBT s3NW ns).toFinset := checkNodesBT_mem (by decide) s3NPairs s3NWOk (buildPoolsBT_sound s3NSlicesOk) s3NAutosOk s3NBucket7Ok s3NBlock8_0Ok
def s3NNodes8 : List NodeSpec := s3NBlock8_0
def s3NBucket8 : BT (List (List Nat)) := buildBucketsBT s3NW s3NNodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s3NBucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s3NG 8 xs.toFinset) s3NBucket8 := buildBucketsBT_of_mem s3NBlock8_0Mem
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s3NBound : Lower s3NR s3NG 9 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 3,2,10),(VAR 4,1,17),(VAR 5,1,33)]) (by decide +kernel) s3NBucket8Ok (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q41 : Lower (varsOf 123) 0xffffffeeffeeeeeeffffffaaffccee88 9 := by
  apply carry_of (swaps := [(5, 6), (4, 5), (3, 4), (2, 3)]) (roots2 := s3NR) (T2 := s3NG) _ s3NBound
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q44 : Lower (varsOf 71) 0xfefefefefefefefee8e8e8e8e8e8e8e8 7 := by
  apply carry_of (swaps := [(5, 6)]) (roots2 := lb111) (T2 := lb101) _ lb170
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q45 : Lower (varsOf 27) 0xffccee88ffccee88ffccee88ffccee88 5 := by
  apply carry_of (swaps := [(3, 4), (2, 3)]) (roots2 := lb5) (T2 := lb255) _ lb271
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q46 : Lower (varsOf 56) 0xffffff00ff000000ffffff00ff000000 4 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (1, 2), (2, 3), (3, 4), (0, 1), (1, 2), (2, 3)]) (roots2 := lb110) (T2 := lb100) _ lb302
  decide +kernel
def rootNR : List Nat := varsOf 127
def rootNG : Nat := 0xfffffffefffefefeffffffeaffecfee8
def rootNPos : List Nat := [3,3,5,5,6,6,9,9,10,10,12,12,18,18,21,21,24,24,24,28,33,33,38,38,40,40,44,52,52,65,65,66,66,68,68,68,76,81,84,84,88,88,98,100,100,104,104]
def rootNNeg : List Nat := [1,2,1,4,2,4,1,8,2,8,4,8,2,16,17,20,8,16,20,20,1,32,34,36,8,32,36,20,36,1,64,2,64,0,4,64,72,17,20,80,72,80,34,36,96,72,96]
def rootNMask : Nat := fullMask 47
def rootNBase : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x206030c0cf,0x2020104045),(0xcccccccccccccccccccccccccccccccc,0x40180c03333,0x40080401112),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x18de1cc8cc3c,0x8441c8c8428),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x6310070f0fc0,0x211001010a80),(0xffff0000ffff0000ffff0000ffff0000,0x3e0180ff000,0x2e0080ee000),(0xffffffff00000000ffffffff00000000,0x7c001ff00000,0x5c0016e00000),(0xffffffffffffffff0000000000000000,0x7fffe0000000,0x739940000000)]
def rootNSteps : List (Nat × Nat × Nat) := [(1,2,3),(1,3,6),(3,2,8),(1,2,8),(3,3,10)]
def rootNW : BT Decor := buildWiresBT 4 rootNBase rootNSteps
def rootNAutoList : List (List (Nat × Nat)) := [[],[(0,1),(4,5)]]
def rootNAutos : BT (List (Nat × Nat)) := btOfList 1 rootNAutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNPairs : goodPairs rootNG rootNPos rootNNeg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBaseOk : ∀ x ∈ rootNBase, faithful rootNPos rootNNeg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNWOk : btAll (fun x => faithful rootNPos rootNNeg x ∧ x.1 < 2^128) rootNW := buildWiresBT_faithful rootNBaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNAutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw rootNG = rootNG) rootNAutos := btAll_ofList (autos_of (by decide +kernel))
def rootNSliceList : List (Option (Nat × Nat)) := [some (subcubeFast 64 0,10),some (subcubeFast 32 0,10),some (subcubeFast 16 0,10),some (subcubeFast 2 0,10),some (subcubeFast 1 0,10),some (subcubeFast 4 0,9),some (subcubeFast 56 0,7),some (subcubeFast 100 0,5),some (subcubeFast 120 0,4),some (subcubeFast 7 64,4)]
def rootNSlices : BT (Option (Nat × Nat)) := btOfList 4 rootNSliceList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice0 : Slice rootNR rootNG (subcubeFast 64 0) 10 := slice_fast_direct (zDead := 0) (qRoots := varsOf 63) (qGoal := 0xffffffeaffecfee8ffffffeaffecfee8) (by decide +kernel) q0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice1 : Slice rootNR rootNG (subcubeFast 32 0) 10 := slice_fast_direct (zDead := 0) (qRoots := varsOf 95) (qGoal := 0xfffefefefffefefeffecfee8ffecfee8) (by decide +kernel) q19
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice2 : Slice rootNR rootNG (subcubeFast 16 0) 10 := slice_fast_direct (zDead := 0) (qRoots := varsOf 111) (qGoal := 0xfffefffefefefefeffeaffeafee8fee8) (by decide +kernel) q21
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice3 : Slice rootNR rootNG (subcubeFast 2 0) 10 := slice_fast_direct (zDead := 0) (qRoots := varsOf 125) (qGoal := 0xfffffffafffafafaffffffaaffa0faa0) (by decide +kernel) q22
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice4 : Slice rootNR rootNG (subcubeFast 1 0) 10 := slice_fast_direct (zDead := 0) (qRoots := varsOf 126) (qGoal := 0xfffffffcfffcfcfcffffffc0ffccfcc0) (by decide +kernel) q40
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice5 : Slice rootNR rootNG (subcubeFast 4 0) 9 := slice_fast_direct (zDead := 0) (qRoots := varsOf 123) (qGoal := 0xffffffeeffeeeeeeffffffaaffccee88) (by decide +kernel) q41
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice6 : Slice rootNR rootNG (subcubeFast 56 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 71) (qGoal := 0xfefefefefefefefee8e8e8e8e8e8e8e8) (by decide +kernel) q44
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice7 : Slice rootNR rootNG (subcubeFast 100 0) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 27) (qGoal := 0xffccee88ffccee88ffccee88ffccee88) (by decide +kernel) q45
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice8 : Slice rootNR rootNG (subcubeFast 120 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 7) (qGoal := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8) (by decide +kernel) q18
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlice9 : Slice rootNR rootNG (subcubeFast 7 64) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 56) (qGoal := 0xffffff00ff000000ffffff00ff000000) (by decide +kernel) q46
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNSlicesOk : btAll (fun o => ∀ p, o = some p → Slice rootNR rootNG p.1 p.2) rootNSlices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice rootNR rootNG p.1 p.2) (forall_cons (fun _ h => by cases h; exact rootNSlice0) (forall_cons (fun _ h => by cases h; exact rootNSlice1) (forall_cons (fun _ h => by cases h; exact rootNSlice2) (forall_cons (fun _ h => by cases h; exact rootNSlice3) (forall_cons (fun _ h => by cases h; exact rootNSlice4) (forall_cons (fun _ h => by cases h; exact rootNSlice5) (forall_cons (fun _ h => by cases h; exact rootNSlice6) (forall_cons (fun _ h => by cases h; exact rootNSlice7) (forall_cons (fun _ h => by cases h; exact rootNSlice8) (forall_cons (fun _ h => by cases h; exact rootNSlice9) (fun _ h => (List.not_mem_nil h).elim)))))))))))
def rootNEmpty : BT (List (List Nat)) := BT.empty
lemma rootNEmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible rootNG (8 - 1) xs.toFinset) rootNEmpty := trivial
def rootNBlock8_0Specs : List PoolSpec := [(9,[]),(8,[]),(7,[])]
def rootNBlock8_0Pools : BT (Option BoundPool) := buildPoolsBT 2 rootNW rootNR rootNSlices rootNBlock8_0Specs
def rootNBlock8_0 : List NodeSpec := [([11,0,1,2,4,5,8],[0,2],[]),([9,0,1,7,4,5,8],[0,1],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock8_0Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock8_0Pools rootNAutos rootNEmpty 8 rootNBlock8_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock8_0Mem : ∀ ns ∈ rootNBlock8_0, Impossible rootNG 8 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNEmptyOk rootNBlock8_0Ok
def rootNNodes8 : List NodeSpec := rootNBlock8_0
def rootNBucket8 : BT (List (List Nat)) := buildBucketsBT rootNW rootNNodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible rootNG 8 xs.toFinset) rootNBucket8 := buildBucketsBT_of_mem rootNBlock8_0Mem
def rootNBlock9_0Specs : List PoolSpec := [(9,[]),(6,[]),(3,[(1,2,3),(1,3,6)]),(4,[(1,2,3),(1,3,6)]),(0,[(1,2,3)]),(5,[(1,3,6)]),(6,[(1,2,8)]),(6,[(3,2,8)]),(0,[])]
def rootNBlock9_0Pools : BT (Option BoundPool) := buildPoolsBT 4 rootNW rootNR rootNSlices rootNBlock9_0Specs
def rootNBlock9_0 : List NodeSpec := [([9,0,1,2,3,4,5,8],[0,7,8],[0]),([0,1,2,3,4,5,8,10],[0,5,6],[0]),([0,1,2,7,4,5,8],[0,1,2,3,4,5],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock9_0Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock9_0Pools rootNAutos rootNBucket8 9 rootNBlock9_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock9_0Mem : ∀ ns ∈ rootNBlock9_0, Impossible rootNG 9 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket8Ok rootNBlock9_0Ok
def rootNNodes9 : List NodeSpec := rootNBlock9_0
def rootNBucket9 : BT (List (List Nat)) := buildBucketsBT rootNW rootNNodes9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBucket9Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible rootNG 9 xs.toFinset) rootNBucket9 := buildBucketsBT_of_mem rootNBlock9_0Mem
def rootNBlock10_0Specs : List PoolSpec := [(6,[]),(0,[(1,2,3)]),(5,[(1,3,6)]),(3,[(1,2,3)]),(4,[(1,2,3)]),(5,[]),(0,[]),(3,[(1,3,6)]),(4,[(1,3,6)])]
def rootNBlock10_0Pools : BT (Option BoundPool) := buildPoolsBT 4 rootNW rootNR rootNSlices rootNBlock10_0Specs
def rootNBlock10_0 : List NodeSpec := [([0,1,2,3,7,4,5,6],[0,1,3,4,5],[0]),([0,1,2,3,4,5,8],[0,2,6,7,8],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock10_0Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock10_0Pools rootNAutos rootNBucket9 10 rootNBlock10_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock10_0Mem : ∀ ns ∈ rootNBlock10_0, Impossible rootNG 10 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket9Ok rootNBlock10_0Ok
def rootNNodes10 : List NodeSpec := rootNBlock10_0
def rootNBucket10 : BT (List (List Nat)) := buildBucketsBT rootNW rootNNodes10
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBucket10Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible rootNG 10 xs.toFinset) rootNBucket10 := buildBucketsBT_of_mem rootNBlock10_0Mem
def rootNBlock11_0Specs : List PoolSpec := [(6,[]),(5,[]),(0,[]),(3,[]),(4,[]),(1,[]),(2,[])]
def rootNBlock11_0Pools : BT (Option BoundPool) := buildPoolsBT 3 rootNW rootNR rootNSlices rootNBlock11_0Specs
def rootNBlock11_0 : List NodeSpec := [([0,1,2,3,4,5,6],[0,1,2,3,4,5,6],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock11_0Ok : checkNodesBT rootNW rootNG rootNMask rootNBlock11_0Pools rootNAutos rootNBucket10 11 rootNBlock11_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBlock11_0Mem : ∀ ns ∈ rootNBlock11_0, Impossible rootNG 11 (nodeValsBT rootNW ns).toFinset := checkNodesBT_mem (by decide) rootNPairs rootNWOk (buildPoolsBT_sound rootNSlicesOk) rootNAutosOk rootNBucket10Ok rootNBlock11_0Ok
def rootNNodes11 : List NodeSpec := rootNBlock11_0
def rootNBucket11 : BT (List (List Nat)) := buildBucketsBT rootNW rootNNodes11
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBucket11Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible rootNG 11 xs.toFinset) rootNBucket11 := buildBucketsBT_of_mem rootNBlock11_0Mem
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rootNBound : Lower rootNR rootNG 12 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 3,1,9),(VAR 4,2,18),(VAR 5,1,33),(VAR 6,1,65)]) (by decide +kernel) rootNBucket11Ok (by decide +kernel)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma sevenGraph : Lower (varsOf 127) 0xfffffffffffffffaffffffeefefeeca0 12 := carry_of (swaps := [(1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (2, 3), (3, 4), (4, 5), (0, 1), (1, 2), (2, 3), (3, 4), (1, 2), (2, 3)]) (roots2 := rootNR) (T2 := rootNG) (by decide +kernel) rootNBound
end Small
namespace Relate
def insertRow (r : Small.Row) : Wide.Row :=
  ⟨(0 + ((r.val / 1) % 2) * 1 + ((r.val / 2) % 2) * 2 + ((r.val / 4) % 2) * 8 + ((r.val / 8) % 2) * 16 + ((r.val / 16) % 2) * 32 + ((r.val / 32) % 2) * 64 + ((r.val / 64) % 2) * 128) % 256, Nat.mod_lt _ (by decide)⟩
def project (w : Wide.Wire) : Small.Wire := fun r => w (insertRow r)
lemma avail {b : List Wide.Wire} {v : Wide.Wire} (h : Wide.Avail b v) :
    Small.Avail (b.map project) (project v) := by
  rcases h with h | ⟨k, rfl⟩ | h
  · exact Or.inl (List.mem_map_of_mem h)
  · exact Or.inr (Or.inl ⟨k,rfl⟩)
  · exact Or.inr (Or.inr (List.mem_map_of_mem (f := project) h))
lemma reach {roots b : List Wide.Wire} {n : Nat} (h : Wide.Reach roots n b) :
    Small.Reach (roots.map project) n (b.map project) := by
  induction n generalizing b with
  | zero => change b = roots at h; rw [h]; rfl
  | succ n ih =>
    obtain ⟨op,bank,a,b,hr,ha,hb,rfl⟩ := h
    refine ⟨op, bank.map project, project a, project b, ih hr, avail ha, avail hb, ?_⟩
    cases op <;> rfl
lemma liftPins : Wide.Lower (Wide.varsOf 255) 0xfffffffffffffffffffffffffffffffafffffffffffffefeffeeffeeeeccaa00 13 := by
  have bound : Wide.Lower (Wide.varsOf 251) 0xffffffffffffffffffffffffffffffaaffffffffffffeeeeffeeffeeeeccaa00 12 := by
    intro n bank hr ha
    have proots : (((Wide.varsOf 251).map Wide.obs).map project) = (Small.varsOf 127).map Small.obs := by
      change [_,_,_,_,_,_,_] = [_,_,_,_,_,_,_]
      repeat' apply congrArg₂ List.cons
      all_goals first | rfl | funext r; revert r; decide +kernel
    have target : project (Wide.obs 0xffffffffffffffffffffffffffffffaaffffffffffffeeeeffeeffeeeeccaa00) = Small.obs 0xfffffffffffffffaffffffeefefeeca0 := by funext r; revert r; decide +kernel
    have r := reach hr
    have a := avail ha
    rw [proots] at r
    rw [target] at a
    exact Small.sevenGraph n _ r a
  exact Wide.lift_of (z := 4) (o := 0) (essPairs := [(Wide.VAR 2,64,68)]) (by decide +kernel) bound
end Relate
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def f (x : Fin 8 → Bool) : Bool := (x 0 && x 3) || (x 1 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 4 && x 6) || (x 5 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 5 && x 7) || (x 6 && x 7)
def onWit : List Gate := [⟨.or, [6, 3]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [5, 4]⟩, ⟨.or, [6, 12]⟩, ⟨.or, [2, 12]⟩, ⟨.and, [1, 13]⟩, ⟨.and, [8, 10]⟩, ⟨.and, [11, 14]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [17, 19]⟩, ⟨.or, [18, 20]⟩]

theorem onWitBasis : ∀ g ∈ onWit,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [onWit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem onWitCorrect : ∀ x : Fin 8 → Bool,
    Circuit.eval ⟨onWit, 21⟩ (List.ofFn x) = f x := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem onGraphCorrect : ∀ x : Fin 8 → Bool, f x = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  decide +kernel

theorem onFinal :
∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o hfit _hone hev
  have hf : ∀ y : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn y) = f y := fun y => (hev y).trans (onGraphCorrect y).symm
  have hrow : ∀ r : Wide.Row, f (Wide.evalInput r) = (0xfffffffffffffffffffffffffffffffafffffffffffffefeffeeffeeeeccaa00 : Nat).testBit r.val := by decide +kernel
  have hw : ∀ r : Wide.Row, Circuit.eval ⟨onWit, 21⟩ (List.ofFn (Wide.evalInput r)) = (0xfffffffffffffffffffffffffffffffafffffffffffffefeffeeffeeeeccaa00 : Nat).testBit r.val :=
    fun r => (onWitCorrect (Wide.evalInput r)).trans (hrow r)
  obtain ⟨gs, out, hg, hlen, hev⟩ := Wide.replace_of_lower (0xfffffffffffffffffffffffffffffffafffffffffffffefeffeeffeeeeccaa00 : Nat) (by decide) (by decide) (by decide)
    13 Relate.liftPins onWit 21 (by decide) onWitBasis f hrow hw gates o hfit hf
  exact ⟨gs, out, hg, hlen, fun x => (hev x).trans (onGraphCorrect x)⟩
end PEqualNP.Outside.L_meta_51784

theorem PEqualNP.Outside.L_meta_51784 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  PEqualNP.Outside.L_meta_51784.onFinal
