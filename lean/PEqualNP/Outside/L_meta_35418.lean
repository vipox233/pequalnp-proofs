import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_35418
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

def d0 : Nat := 0xfffff0f0f0f00000fffff0f0f0f00000
def d11 : List Nat := varsOf 52
def d92 : List Nat := [20,20,36,36,48,48,20,36,48]
def d84 : List Nat := [16,4,32,4,32,16,32,16,4]
def d64 : Nat := fullMask 9
def d28 : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xcf,0x10a),(0xffff0000ffff0000ffff0000ffff0000,0x173,0xa1),(0xffffffff00000000ffffffff00000000,0x1bc,0x54)]
def d110 : List (Nat × Nat × Nat) := []
def d18 : BT Decor := buildWiresBT 2 d28 d110
def d22 : List (List (Nat × Nat)) := []
def d24 : BT (List (Nat × Nat)) := btOfList 1 d22
def d104 : List (Option (Nat × Nat)) := []
def d106 : BT (Option (Nat × Nat)) := btOfList 1 d104
def d94 : List PoolSpec := []
def d7 : BT (Option BoundPool) := buildPoolsBT 1 d18 d11 d106 d94
lemma d70 : goodPairs d0 d92 d84 := goodPairs_of (by decide +kernel)
lemma d29 : ∀ x ∈ d28, faithful d92 d84 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma d19 : btAll (fun x => faithful d92 d84 x ∧ x.1 < 2^128) d18 := buildWiresBT_faithful d29
set_option maxRecDepth 500000 in
lemma d25 : btAll (fun sw => swapsValid sw = true ∧ permWord sw d0 = d0) d24 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma d107 : btAll (fun o => ∀ p, o = some p → Slice d11 d0 p.1 p.2) d106 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice d11 d0 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 500000 in
lemma d8 : btAll (fun o => ∀ c, o = some c → ValidPool d11 d0 c) d7 := buildPoolsBT_sound d107
def d38 : BT (List (List Nat)) := BT.empty
lemma d39 : btAll (fun bk => ∀ xs ∈ bk, Impossible d0 (0 - 1) xs.toFinset) d38 := trivial
def d86 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d53 : checkNodesBT d18 d0 d64 d7 d24 d38 0 d86 = true := by decide +kernel
def d32 : BT (List (List Nat)) := buildBucketsBT d18 d86
set_option maxRecDepth 500000 in
lemma d33 : btAll (fun bk => ∀ xs ∈ bk, Impossible d0 0 xs.toFinset) d32 :=
  buildBucketsBT_sound (by decide) d70 d19 d8 d25 d39 d53
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d54 : checkNodesBT d18 d0 d64 d7 d24 d32 1 d86 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma d34 : btAll (fun bk => ∀ xs ∈ bk, Impossible d0 1 xs.toFinset) d32 :=
  buildBucketsBT_sound (by decide) d70 d19 d8 d25 d33 d54
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d55 : checkNodesBT d18 d0 d64 d7 d24 d32 2 d86 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma d35 : btAll (fun bk => ∀ xs ∈ bk, Impossible d0 2 xs.toFinset) d32 :=
  buildBucketsBT_sound (by decide) d70 d19 d8 d25 d34 d55
def d87 : List NodeSpec := [([0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d56 : checkNodesBT d18 d0 d64 d7 d24 d32 3 d87 = true := by decide +kernel
def d36 : BT (List (List Nat)) := buildBucketsBT d18 d87
set_option maxRecDepth 500000 in
lemma d37 : btAll (fun bk => ∀ xs ∈ bk, Impossible d0 3 xs.toFinset) d36 :=
  buildBucketsBT_sound (by decide) d70 d19 d8 d25 d35 d56
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma d67 : forestRootCheck d11 d0 [(VAR 2,20,16),(VAR 4,20,4),(VAR 5,36,4)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma d66 : bucketContainsBT d36 d11 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma d72 : Lower d11 d0 4 := lower_of_forestBT d67 d37 d66
def d4 : Nat := 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0
def d15 : List Nat := varsOf 22
lemma d79 : carryOK [(3,5),(1,3),(1,4),(1,2)] d15 d4 d11 d0 = true := by decide +kernel
lemma d78 : Lower d15 d4 4 := carry_of d79 d72
def d5 : Nat := 0xfcfcfcfcc0c0c0c0fcfcfcfcc0c0c0c0
def d16 : List Nat := varsOf 38
lemma d81 : carryOK [(1,3),(1,4),(1,2)] d16 d5 d11 d0 = true := by decide +kernel
lemma d80 : Lower d16 d5 4 := carry_of d81 d72
def d6 : Nat := 0xffffcccccccc0000ffffcccccccc0000
def d17 : List Nat := varsOf 50
lemma d83 : carryOK [(1,2)] d17 d6 d11 d0 = true := by decide +kernel
lemma d82 : Lower d17 d6 4 := carry_of d83 d72
def d1 : Nat := 0xfcfcc0c0c0c00000fcfcc0c0c0c00000
def d12 : List Nat := varsOf 54
def d93 : List Nat := [22,22,22,38,38,38,50,50,50,52,52,52,22,22,22,38,38,38,50,50,50,52,52,52]
def d85 : List Nat := [20,18,6,36,34,6,48,34,18,48,36,20,34,36,48,18,20,48,6,20,36,6,18,34]
def d65 : Nat := fullMask 24
def d30 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0x1ff1ff,0xe491b6),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xe3fe3f,0x3d2c2d),(0xffff0000ffff0000ffff0000ffff0000,0xfc7fc7,0x4bcb43),(0xffffffff00000000ffffffff00000000,0xff8ff8,0x9276d8)]
def d111 : List (Nat × Nat × Nat) := [(0,0,1),(3,4,2),(0,0,2),(0,4,2),(0,1,2),(3,7,3)]
def d20 : BT Decor := buildWiresBT 4 d30 d111
def d23 : List (List (Nat × Nat)) := [[],[(4,5)],[(1,2)],[(4,5),(1,2)],[(2,4)],[(2,5),(2,4)],[(1,2),(1,4)],[(2,5),(1,2),(1,4)],[(2,5),(1,4)]]
def d26 : BT (List (Nat × Nat)) := btOfList 4 d23
def d105 : List (Option (Nat × Nat)) := [some (subcubeFast 0 16,4),some (subcubeFast 0 2,4),some (subcubeFast 0 4,4),some (subcubeFast 0 32,4)]
def d108 : BT (Option (Nat × Nat)) := btOfList 2 d105
def d95 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[])]
def d9 : BT (Option BoundPool) := buildPoolsBT 2 d20 d12 d108 d95
lemma d71 : goodPairs d1 d93 d85 := goodPairs_of (by decide +kernel)
lemma d31 : ∀ x ∈ d30, faithful d93 d85 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma d21 : btAll (fun x => faithful d93 d85 x ∧ x.1 < 2^128) d20 := buildWiresBT_faithful d31
set_option maxRecDepth 500000 in
lemma d27 : btAll (fun sw => swapsValid sw = true ∧ permWord sw d1 = d1) d26 := btAll_ofList (autos_of (by decide +kernel))
lemma d97 : sliceDirectCheck 0 16 0 d12 d1 d16 d5 = true := by decide +kernel
lemma d96 : Slice d12 d1 (subcubeFast 0 16) 4 := slice_fast_direct d97 d80
lemma d99 : sliceDirectCheck 0 2 0 d12 d1 d11 d0 = true := by decide +kernel
lemma d98 : Slice d12 d1 (subcubeFast 0 2) 4 := slice_fast_direct d99 d72
lemma d101 : sliceDirectCheck 0 4 0 d12 d1 d17 d6 = true := by decide +kernel
lemma d100 : Slice d12 d1 (subcubeFast 0 4) 4 := slice_fast_direct d101 d82
lemma d103 : sliceDirectCheck 0 32 0 d12 d1 d15 d4 = true := by decide +kernel
lemma d102 : Slice d12 d1 (subcubeFast 0 32) 4 := slice_fast_direct d103 d78
set_option maxRecDepth 500000 in
lemma d109 : btAll (fun o => ∀ p, o = some p → Slice d12 d1 p.1 p.2) d108 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice d12 d1 p.1 p.2) (forall_cons (fun _ h => by cases h; exact d96) (forall_cons (fun _ h => by cases h; exact d98) (forall_cons (fun _ h => by cases h; exact d100) (forall_cons (fun _ h => by cases h; exact d102) (fun _ h => (List.not_mem_nil h).elim)))))
set_option maxRecDepth 500000 in
lemma d10 : btAll (fun o => ∀ c, o = some c → ValidPool d12 d1 c) d9 := buildPoolsBT_sound d109
lemma d52 : btAll (fun bk => ∀ xs ∈ bk, Impossible d1 (0 - 1) xs.toFinset) d38 := trivial
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d57 : checkNodesBT d20 d1 d65 d9 d26 d38 0 d86 = true := by decide +kernel
def d40 : BT (List (List Nat)) := buildBucketsBT d20 d86
set_option maxRecDepth 500000 in
lemma d41 : btAll (fun bk => ∀ xs ∈ bk, Impossible d1 0 xs.toFinset) d40 :=
  buildBucketsBT_sound (by decide) d71 d21 d10 d27 d52 d57
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d58 : checkNodesBT d20 d1 d65 d9 d26 d40 1 d86 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma d42 : btAll (fun bk => ∀ xs ∈ bk, Impossible d1 1 xs.toFinset) d40 :=
  buildBucketsBT_sound (by decide) d71 d21 d10 d27 d41 d58
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d59 : checkNodesBT d20 d1 d65 d9 d26 d40 2 d86 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma d43 : btAll (fun bk => ∀ xs ∈ bk, Impossible d1 2 xs.toFinset) d40 :=
  buildBucketsBT_sound (by decide) d71 d21 d10 d27 d42 d59
def d88 : List NodeSpec := [([4,6,8,3],[0,1],[]),([9,0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d60 : checkNodesBT d20 d1 d65 d9 d26 d40 3 d88 = true := by decide +kernel
def d44 : BT (List (List Nat)) := buildBucketsBT d20 d88
set_option maxRecDepth 500000 in
lemma d45 : btAll (fun bk => ∀ xs ∈ bk, Impossible d1 3 xs.toFinset) d44 :=
  buildBucketsBT_sound (by decide) d71 d21 d10 d27 d43 d60
def d89 : List NodeSpec := [([5,0,1,2,3],[],[]),([4,6,1,2,3],[0,2],[0]),([7,0,1,2,3],[3],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d61 : checkNodesBT d20 d1 d65 d9 d26 d44 4 d89 = true := by decide +kernel
def d46 : BT (List (List Nat)) := buildBucketsBT d20 d89
set_option maxRecDepth 500000 in
lemma d47 : btAll (fun bk => ∀ xs ∈ bk, Impossible d1 4 xs.toFinset) d46 :=
  buildBucketsBT_sound (by decide) d71 d21 d10 d27 d45 d61
def d90 : List NodeSpec := [([4,0,1,2,3],[2,1,0,3],[0,1,2,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d62 : checkNodesBT d20 d1 d65 d9 d26 d46 5 d90 = true := by decide +kernel
def d48 : BT (List (List Nat)) := buildBucketsBT d20 d90
set_option maxRecDepth 500000 in
lemma d49 : btAll (fun bk => ∀ xs ∈ bk, Impossible d1 5 xs.toFinset) d48 :=
  buildBucketsBT_sound (by decide) d71 d21 d10 d27 d47 d62
def d91 : List NodeSpec := [([0,1,2,3],[1,2,0,3],[0,4,5,6,7,8])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d63 : checkNodesBT d20 d1 d65 d9 d26 d48 6 d91 = true := by decide +kernel
def d50 : BT (List (List Nat)) := buildBucketsBT d20 d91
set_option maxRecDepth 500000 in
lemma d51 : btAll (fun bk => ∀ xs ∈ bk, Impossible d1 6 xs.toFinset) d50 :=
  buildBucketsBT_sound (by decide) d71 d21 d10 d27 d49 d63
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma d69 : forestRootCheck d12 d1 [(VAR 1,22,20),(VAR 2,22,18),(VAR 4,22,6),(VAR 5,38,6)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma d68 : bucketContainsBT d50 d12 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma d73 : Lower d12 d1 7 := lower_of_forestBT d69 d51 d68
def d2 : Nat := 0xfc00c000c0000000fc00c000c0000000
def d13 : List Nat := varsOf 62
lemma d75 : liftCheck 0 8 d13 d2 d12 d1 [(VAR 3,30,22)] = true := by decide +kernel
lemma d74 : Lower d13 d2 8 := lift_of d75 d73
def d3 : Nat := 0xe8008000e8008000e8008000e8008000
def d14 : List Nat := varsOf 31
lemma d77 : carryOK [(0,5),(0,4),(0,2),(0,1)] d14 d3 d13 d2 = true := by decide +kernel
lemma d76 : Lower d14 d3 8 := carry_of d77 d74
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q1d : Lower (varsOf 93) 0xfa00a000fa00a000a0000000a0000000 8 := by
  apply carry_of (swaps := [(4, 5), (5, 6), (2, 3), (3, 4), (2, 3), (1, 2)]) (roots2 := d14) (T2 := d3) _ d76
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q1 : Lower (varsOf 93) 0xfffffffafffffffafffaffa0fffaffa0 8 := dualLower (by decide +kernel) (by decide +kernel) q1d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q0 : Lower (varsOf 95) 0xfffffefafffffefafefaeca0fefaeca0 9 := lift_of (z := 0) (o := 2) (essPairs := [(VAR 1,8,10)]) (by decide +kernel) q1
def d143 : Nat := 0xffffff00ff000000ffffff00ff000000
def d155 : List Nat := varsOf 56
def d231 : List Nat := [24,24,40,40,48,48,24,40,48]
def d225 : List Nat := [16,8,32,8,32,16,32,16,8]
def d169 : List Decor := [(0xff00ff00ff00ff00ff00ff00ff00ff00,0xcf,0x10a),(0xffff0000ffff0000ffff0000ffff0000,0x173,0xa1),(0xffffffff00000000ffffffff00000000,0x1bc,0x54)]
def d161 : BT Decor := buildWiresBT 2 d169 d110
def d233 : BT (Option PoolSpec) := btOfList 1 []
lemma d211 : goodPairs d143 d231 d225 := goodPairs_of (by decide +kernel)
lemma d170 : ∀ x ∈ d169, faithful d231 d225 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma d162 : btAll (fun x => faithful d231 d225 x ∧ x.1 < 2^128) d161 := buildWiresBT_faithful d170
set_option maxRecDepth 500000 in
lemma d166 : btAll (fun sw => swapsValid sw = true ∧ permWord sw d143 = d143) d24 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma d248 : btAll (fun o => ∀ p, o = some p → Slice d155 d143 p.1 p.2) d106 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice d155 d143 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma d179 : btAll (fun bk => ∀ xs ∈ bk, Impossible d143 (0 - 1) xs.toFinset) d38 := trivial
def d150 : BT (Option BoundPool) := buildPoolsSubBT 1 d161 d155 d106 d233 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d194 : checkNodesBT d161 d143 d64 d150 d24 d38 0 d86 = true := by decide +kernel
def d173 : BT (List (List Nat)) := buildBucketsBT d161 d86
set_option maxRecDepth 500000 in
lemma d174 : btAll (fun bk => ∀ xs ∈ bk, Impossible d143 0 xs.toFinset) d173 :=
  buildBucketsBT_sound (by decide) d211 d162 (buildPoolsSubBT_sound d248) d166 d179 d194
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d195 : checkNodesBT d161 d143 d64 d150 d24 d173 1 d86 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma d175 : btAll (fun bk => ∀ xs ∈ bk, Impossible d143 1 xs.toFinset) d173 :=
  buildBucketsBT_sound (by decide) d211 d162 (buildPoolsSubBT_sound d248) d166 d174 d195
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d196 : checkNodesBT d161 d143 d64 d150 d24 d173 2 d86 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma d176 : btAll (fun bk => ∀ xs ∈ bk, Impossible d143 2 xs.toFinset) d173 :=
  buildBucketsBT_sound (by decide) d211 d162 (buildPoolsSubBT_sound d248) d166 d175 d196
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d197 : checkNodesBT d161 d143 d64 d150 d24 d173 3 d87 = true := by decide +kernel
def d177 : BT (List (List Nat)) := buildBucketsBT d161 d87
set_option maxRecDepth 500000 in
lemma d178 : btAll (fun bk => ∀ xs ∈ bk, Impossible d143 3 xs.toFinset) d177 :=
  buildBucketsBT_sound (by decide) d211 d162 (buildPoolsSubBT_sound d248) d166 d176 d197
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma d208 : forestRootCheck d155 d143 [(VAR 3,24,16),(VAR 4,24,8),(VAR 5,40,8)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma d207 : bucketContainsBT d177 d155 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma d213 : Lower d155 d143 4 := lower_of_forestBT d208 d178 d207
def d148 : Nat := 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0
def d159 : List Nat := varsOf 14
lemma d222 : carryOK [(1,2),(1,5),(2,4),(1,3)] d159 d148 d155 d143 = true := by decide +kernel
lemma d221 : Lower d159 d148 4 := carry_of d222 d213
def d149 : Nat := 0xfff0ff00ff000000fff0ff00ff000000
def d160 : List Nat := varsOf 60
lemma d224 : liftCheck 0 4 d160 d149 d155 d143 [(VAR 2,52,48)] = true := by decide +kernel
lemma d223 : Lower d160 d149 5 := lift_of d224 d213
def d144 : Nat := 0xfcc0fc00fcc0fc00fcc0fc00fcc0fc00
def d156 : List Nat := varsOf 30
lemma d215 : carryOK [(1,2),(2,5),(1,4)] d156 d144 d160 d149 = true := by decide +kernel
lemma d214 : Lower d156 d144 5 := carry_of d215 d223
def d145 : Nat := 0xfcc0fcc0fc00fc00fcc0fcc0fc00fc00
def d157 : List Nat := varsOf 46
lemma d217 : carryOK [(2,5),(1,4)] d157 d145 d160 d149 = true := by decide +kernel
lemma d216 : Lower d157 d145 5 := carry_of d217 d223
def d146 : Nat := 0xffccff00ff000000ffccff00ff000000
def d158 : List Nat := varsOf 58
lemma d219 : carryOK [(1,2)] d158 d146 d160 d149 = true := by decide +kernel
lemma d218 : Lower d158 d146 5 := carry_of d219 d223
def d147 : Nat := 0xfcc0fc00fc000000fcc0fc00fc000000
def d232 : List Nat := [26,26,26,28,28,28,30,30,42,42,42,44,44,44,46,46,54,54,54,54,58,58,60,60,26,26,26,26,26,26,28,28,28,28,28,28,42,42,42,42,42,42,44,44,44,44,44,44,54,54]
def d226 : List Nat := [24,18,10,24,20,12,22,14,40,34,10,40,36,12,38,14,52,50,38,22,56,50,56,52,14,22,38,50,52,56,14,22,38,50,52,56,14,22,38,50,52,56,14,22,38,50,52,56,14,56]
def d206 : Nat := fullMask 50
def d171 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0x303f03f3fc7c7,0x13cf3cf2ec6c6),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x3fc0fc0cff8f8,0x15d75d78df0f0),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xfffffff0ffff,0x386186150adad),(0xffff0000ffff0000ffff0000ffff0000,0x3000fffff00ff,0x2ebaebafb005b),(0xffffffff00000000ffffffff00000000,0x3fff000ffff00,0x2f3cf3cf75b00)]
def d251 : List (Nat × Nat × Nat) := [(0,0,3),(2,0,2),(0,0,2),(0,6,3),(3,5,2),(1,5,2),(3,7,3),(0,7,3),(3,6,3),(3,7,1),(0,1,10),(3,13,4),(3,12,1)]
def d163 : BT Decor := buildWiresBT 5 d171 d251
def d165 : List (List (Nat × Nat)) := [[],[(2,5),(1,4)],[(4,5)],[(1,2)],[(4,5),(1,2)],[(1,2),(2,5),(1,4)]]
def d167 : BT (List (Nat × Nat)) := btOfList 3 d165
def d247 : List (Option (Nat × Nat)) := [some (subcubeFast 0 16,5),some (subcubeFast 0 6,4),some (subcubeFast 0 4,5),some (subcubeFast 0 2,5),some (subcubeFast 0 32,5),some (subcubeFast 0 48,4)]
def d249 : BT (Option (Nat × Nat)) := btOfList 3 d247
def d234 : BT (Option PoolSpec) := btOfList 3 [some (0,[]),some (1,[]),some (2,[]),some (3,[]),some (4,[]),some (5,[])]
lemma d212 : goodPairs d147 d232 d226 := goodPairs_of (by decide +kernel)
lemma d172 : ∀ x ∈ d171, faithful d232 d226 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma d164 : btAll (fun x => faithful d232 d226 x ∧ x.1 < 2^128) d163 := buildWiresBT_faithful d172
set_option maxRecDepth 500000 in
lemma d168 : btAll (fun sw => swapsValid sw = true ∧ permWord sw d147 = d147) d167 := btAll_ofList (autos_of (by decide +kernel))
lemma d236 : sliceDirectCheck 0 16 0 d13 d147 d157 d145 = true := by decide +kernel
lemma d235 : Slice d13 d147 (subcubeFast 0 16) 5 := slice_fast_direct d236 d216
lemma d238 : sliceDirectCheck 0 6 0 d13 d147 d155 d143 = true := by decide +kernel
lemma d237 : Slice d13 d147 (subcubeFast 0 6) 4 := slice_fast_direct d238 d213
lemma d240 : sliceDirectCheck 0 4 0 d13 d147 d158 d146 = true := by decide +kernel
lemma d239 : Slice d13 d147 (subcubeFast 0 4) 5 := slice_fast_direct d240 d218
lemma d242 : sliceDirectCheck 0 2 0 d13 d147 d160 d149 = true := by decide +kernel
lemma d241 : Slice d13 d147 (subcubeFast 0 2) 5 := slice_fast_direct d242 d223
lemma d244 : sliceDirectCheck 0 32 0 d13 d147 d156 d144 = true := by decide +kernel
lemma d243 : Slice d13 d147 (subcubeFast 0 32) 5 := slice_fast_direct d244 d214
lemma d246 : sliceDirectCheck 0 48 0 d13 d147 d159 d148 = true := by decide +kernel
lemma d245 : Slice d13 d147 (subcubeFast 0 48) 4 := slice_fast_direct d246 d221
set_option maxRecDepth 500000 in
lemma d250 : btAll (fun o => ∀ p, o = some p → Slice d13 d147 p.1 p.2) d249 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice d13 d147 p.1 p.2) (forall_cons (fun _ h => by cases h; exact d235) (forall_cons (fun _ h => by cases h; exact d237) (forall_cons (fun _ h => by cases h; exact d239) (forall_cons (fun _ h => by cases h; exact d241) (forall_cons (fun _ h => by cases h; exact d243) (forall_cons (fun _ h => by cases h; exact d245) (fun _ h => (List.not_mem_nil h).elim)))))))
lemma d193 : btAll (fun bk => ∀ xs ∈ bk, Impossible d147 (0 - 1) xs.toFinset) d38 := trivial
def d151 : BT (Option BoundPool) := buildPoolsSubBT 3 d163 d13 d249 d234 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d198 : checkNodesBT d163 d147 d206 d151 d167 d38 0 d86 = true := by decide +kernel
def d180 : BT (List (List Nat)) := buildBucketsBT d163 d86
set_option maxRecDepth 500000 in
lemma d181 : btAll (fun bk => ∀ xs ∈ bk, Impossible d147 0 xs.toFinset) d180 :=
  buildBucketsBT_sound (by decide) d212 d164 (buildPoolsSubBT_sound d250) d168 d193 d198
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d199 : checkNodesBT d163 d147 d206 d151 d167 d180 1 d86 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma d182 : btAll (fun bk => ∀ xs ∈ bk, Impossible d147 1 xs.toFinset) d180 :=
  buildBucketsBT_sound (by decide) d212 d164 (buildPoolsSubBT_sound d250) d168 d181 d199
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d200 : checkNodesBT d163 d147 d206 d151 d167 d180 2 d86 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma d183 : btAll (fun bk => ∀ xs ∈ bk, Impossible d147 2 xs.toFinset) d180 :=
  buildBucketsBT_sound (by decide) d212 d164 (buildPoolsSubBT_sound d250) d168 d182 d200
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d201 : checkNodesBT d163 d147 d206 d151 d167 d180 3 d86 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma d184 : btAll (fun bk => ∀ xs ∈ bk, Impossible d147 3 xs.toFinset) d180 :=
  buildBucketsBT_sound (by decide) d212 d164 (buildPoolsSubBT_sound d250) d168 d183 d201
def d227 : List NodeSpec := [([0,15,2,3,4],[],[]),([16,0,1,2,3],[],[]),([17,0,2,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d202 : checkNodesBT d163 d147 d206 d151 d167 d180 4 d227 = true := by decide +kernel
def d185 : BT (List (List Nat)) := buildBucketsBT d163 d227
set_option maxRecDepth 500000 in
lemma d186 : btAll (fun bk => ∀ xs ∈ bk, Impossible d147 4 xs.toFinset) d185 :=
  buildBucketsBT_sound (by decide) d212 d164 (buildPoolsSubBT_sound d250) d168 d184 d202
def d228 : List NodeSpec := [([8,0,1,2,3,4],[],[]),([7,5,1,2,3,4],[0,1],[]),([9,0,1,2,3,4],[],[]),([0,1,2,10,3,4],[0,2,3,4],[0,1]),([11,0,1,2,3,4],[],[]),([12,0,1,2,3,4],[2,4],[0,1]),([0,1,2,13,3,4],[4],[0]),([14,0,2,3,4],[],[]),([14,7,0,2,3,4],[2],[]),([6,7,1,2,3,4],[1],[])]
def d152 : BT (Option BoundPool) := buildPoolsSubBT 3 d163 d13 d249 d234 [0,1,2,3,4]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d203 : checkNodesBT d163 d147 d206 d152 d167 d185 5 d228 = true := by decide +kernel
def d187 : BT (List (List Nat)) := buildBucketsBT d163 d228
set_option maxRecDepth 500000 in
lemma d188 : btAll (fun bk => ∀ xs ∈ bk, Impossible d147 5 xs.toFinset) d187 :=
  buildBucketsBT_sound (by decide) d212 d164 (buildPoolsSubBT_sound d250) d168 d186 d203
def d229 : List NodeSpec := [([5,0,1,2,3,4],[1,5],[0,1]),([6,0,1,2,3,4],[1,0,4],[0,2]),([7,0,1,2,3,4],[1,0,4],[0,2])]
def d153 : BT (Option BoundPool) := buildPoolsSubBT 3 d163 d13 d249 d234 [0,1,4,5]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d204 : checkNodesBT d163 d147 d206 d153 d167 d187 6 d229 = true := by decide +kernel
def d189 : BT (List (List Nat)) := buildBucketsBT d163 d229
set_option maxRecDepth 500000 in
lemma d190 : btAll (fun bk => ∀ xs ∈ bk, Impossible d147 6 xs.toFinset) d189 :=
  buildBucketsBT_sound (by decide) d212 d164 (buildPoolsSubBT_sound d250) d168 d188 d204
def d230 : List NodeSpec := [([0,1,2,3,4],[1,5],[0,2,3,4,1,5])]
def d154 : BT (Option BoundPool) := buildPoolsSubBT 3 d163 d13 d249 d234 [1,5]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d205 : checkNodesBT d163 d147 d206 d154 d167 d189 7 d230 = true := by decide +kernel
def d191 : BT (List (List Nat)) := buildBucketsBT d163 d230
set_option maxRecDepth 500000 in
lemma d192 : btAll (fun bk => ∀ xs ∈ bk, Impossible d147 7 xs.toFinset) d191 :=
  buildBucketsBT_sound (by decide) d212 d164 (buildPoolsSubBT_sound d250) d168 d190 d205
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma d210 : forestRootCheck d13 d147 [(VAR 1,26,24),(VAR 2,28,24),(VAR 3,26,18),(VAR 4,26,10),(VAR 5,42,10)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma d209 : bucketContainsBT d191 d13 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma d220 : Lower d13 d147 8 := lower_of_forestBT d210 d192 d209
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q3d : Lower (varsOf 31) 0xe8e0e000e8e0e000e8e0e000e8e0e000 8 := by
  apply carry_of (swaps := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5)]) (roots2 := d13) (T2 := d147) _ d220
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q3 : Lower (varsOf 31) 0xfff8f8e8fff8f8e8fff8f8e8fff8f8e8 8 := dualLower (by decide +kernel) (by decide +kernel) q3d
def d347 : List Nat := [6,6,10,10,12,12,6,10,12]
def d340 : List Nat := [4,2,8,2,8,4,8,4,2]
def d273 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xcf,0x10a),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x173,0xa1),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x1bc,0x54)]
def d262 : Array Decor := buildWires d273 d110
def d268 : Array (List (Nat × Nat)) := #[]
def d361 : List (Nat × Nat) := []
def d363 : Array (Nat × Nat) := d361.toArray
def d256 : Array (Option BoundPool) := buildPools d262 d159 d363 d94
lemma d328 : goodPairs d148 d347 d340 := goodPairs_of (by decide +kernel)
lemma d274 : ∀ x ∈ d273, faithful d347 d340 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma d263 : ∀ x ∈ d262.toList, faithful d347 d340 x ∧ x.1 < 2^128 := buildWires_faithful d274
lemma d269 : ∀ sw ∈ d268.toList, swapsValid sw = true ∧ permWord sw d148 = d148 := autos_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma d364 : ∀ i (hi : i < d363.size), Slice d159 d148 d363[i].1 d363[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice d159 d148 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma d257 : ∀ i (hi : i < d256.size), ∀ c, d256[i] = some c → ValidPool d159 d148 c := buildPools_sound d364
def d285 : Array (List (List Nat)) := #[]
lemma d286 : ∀ i (hi : i < d285.size), ∀ xs ∈ d285[i], Impossible d148 (0 - 1) xs.toFinset := by intro i hi; simp [d285] at hi
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d306 : checkNodes d262 d148 d64 d256 d268 d285 0 d86 = true := by decide +kernel
def d279 : Array (List (List Nat)) := buildBuckets 1 d262 d86
lemma d280 : ∀ i (hi : i < d279.size), ∀ xs ∈ d279[i], Impossible d148 0 xs.toFinset :=
  buildBuckets_sound (by decide) d328 d263 d257 d269 d286 d306
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d307 : checkNodes d262 d148 d64 d256 d268 d279 1 d86 = true := by decide +kernel
lemma d281 : ∀ i (hi : i < d279.size), ∀ xs ∈ d279[i], Impossible d148 1 xs.toFinset :=
  buildBuckets_sound (by decide) d328 d263 d257 d269 d280 d307
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d308 : checkNodes d262 d148 d64 d256 d268 d279 2 d86 = true := by decide +kernel
lemma d282 : ∀ i (hi : i < d279.size), ∀ xs ∈ d279[i], Impossible d148 2 xs.toFinset :=
  buildBuckets_sound (by decide) d328 d263 d257 d269 d281 d308
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d309 : checkNodes d262 d148 d64 d256 d268 d279 3 d87 = true := by decide +kernel
def d283 : Array (List (List Nat)) := buildBuckets 1 d262 d87
lemma d284 : ∀ i (hi : i < d283.size), ∀ xs ∈ d283[i], Impossible d148 3 xs.toFinset :=
  buildBuckets_sound (by decide) d328 d263 d257 d269 d282 d309
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d323 : forestRootCheck d159 d148 [(VAR 1,6,4),(VAR 2,6,2),(VAR 3,10,2)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d322 : bucketContains d283 d159 = true := by decide +kernel
lemma d331 : Lower d159 d148 4 := lower_of_forest d323 d284 d322
def d252 : Nat := 0xfcc00000fcc00000fcc00000fcc00000
lemma d333 : liftCheck 0 16 d156 d252 d159 d148 [(VAR 4,22,6)] = true := by decide +kernel
lemma d332 : Lower d156 d252 5 := lift_of d333 d331
lemma d335 : liftCheck 0 16 d156 d144 d159 d148 [(VAR 4,22,6)] = true := by decide +kernel
lemma d334 : Lower d156 d144 5 := lift_of d335 d331
def d253 : Nat := 0xfff0ff00fff00000fff0ff00fff00000
def d348 : List Nat := [20,20,24,24,28,40,40,44,44,52,52,56,20,20,20,24,24,24,40,40,40]
def d341 : List Nat := [16,4,16,8,12,32,8,36,12,48,36,48,12,36,48,12,36,48,12,36,48]
def d321 : Nat := fullMask 21
def d275 : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x7793,0xdb592),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x1f89fc,0x49158),(0xffff0000ffff0000ffff0000ffff0000,0x3fe1f,0x124a05),(0xffffffff00000000ffffffff00000000,0x1c0fe0,0x1b6ea0)]
def d264 : Array Decor := buildWires d275 d110
def d258 : Array (Option BoundPool) := buildPools d264 d160 d363 d94
lemma d329 : goodPairs d253 d348 d341 := goodPairs_of (by decide +kernel)
lemma d276 : ∀ x ∈ d275, faithful d348 d341 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma d265 : ∀ x ∈ d264.toList, faithful d348 d341 x ∧ x.1 < 2^128 := buildWires_faithful d276
lemma d270 : ∀ sw ∈ d268.toList, swapsValid sw = true ∧ permWord sw d253 = d253 := autos_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma d365 : ∀ i (hi : i < d363.size), Slice d160 d253 d363[i].1 d363[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice d160 d253 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma d259 : ∀ i (hi : i < d258.size), ∀ c, d258[i] = some c → ValidPool d160 d253 c := buildPools_sound d365
lemma d293 : ∀ i (hi : i < d285.size), ∀ xs ∈ d285[i], Impossible d253 (0 - 1) xs.toFinset := by intro i hi; simp [d285] at hi
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d310 : checkNodes d264 d253 d321 d258 d268 d285 0 d86 = true := by decide +kernel
def d287 : Array (List (List Nat)) := buildBuckets 1 d264 d86
lemma d288 : ∀ i (hi : i < d287.size), ∀ xs ∈ d287[i], Impossible d253 0 xs.toFinset :=
  buildBuckets_sound (by decide) d329 d265 d259 d270 d293 d310
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d311 : checkNodes d264 d253 d321 d258 d268 d287 1 d86 = true := by decide +kernel
lemma d289 : ∀ i (hi : i < d287.size), ∀ xs ∈ d287[i], Impossible d253 1 xs.toFinset :=
  buildBuckets_sound (by decide) d329 d265 d259 d270 d288 d311
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d312 : checkNodes d264 d253 d321 d258 d268 d287 2 d86 = true := by decide +kernel
lemma d290 : ∀ i (hi : i < d287.size), ∀ xs ∈ d287[i], Impossible d253 2 xs.toFinset :=
  buildBuckets_sound (by decide) d329 d265 d259 d270 d289 d312
def d343 : List NodeSpec := [([0,1,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d313 : checkNodes d264 d253 d321 d258 d268 d287 3 d343 = true := by decide +kernel
def d291 : Array (List (List Nat)) := buildBuckets 1 d264 d343
lemma d292 : ∀ i (hi : i < d291.size), ∀ xs ∈ d291[i], Impossible d253 3 xs.toFinset :=
  buildBuckets_sound (by decide) d329 d265 d259 d270 d290 d313
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d325 : forestRootCheck d160 d253 [(VAR 2,20,16),(VAR 3,24,16),(VAR 4,20,4),(VAR 5,40,8)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d324 : bucketContains d291 d160 = true := by decide +kernel
lemma d336 : Lower d160 d253 4 := lower_of_forest d325 d292 d324
def d254 : Nat := 0xffccff00ffcc0000ffccff00ffcc0000
lemma d338 : carryOK [(1,2)] d158 d254 d160 d253 = true := by decide +kernel
lemma d337 : Lower d158 d254 4 := carry_of d338 d336
def d255 : Nat := 0xfcc0fc00fcc00000fcc0fc00fcc00000
def d349 : List Nat := [22,22,22,26,26,26,28,28,28,30,42,42,42,44,44,44,46,46,54,54,54,58,58,60,60,22,22,22,22,22,26,26,26,26,26,28,28,28,28,28,42,42,42,42,42,44,44,44,44,44]
def d342 : List Nat := [20,18,6,24,18,10,24,20,12,14,40,34,10,40,36,12,38,14,52,50,38,56,50,56,52,14,38,50,52,56,14,38,50,52,56,14,38,50,52,56,14,38,50,52,56,14,38,50,52,56]
def d277 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0x1f07fe7f1e3f,0xe739ce5b1a36),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x3e0f83f9fe3c7,0x16b5ad717c385),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x3ffffc1e3fff8,0x2318c62a2b768),(0xffff0000ffff0000ffff0000ffff0000,0xfffffc03ff,0x39ce739ec00db),(0xffffffff00000000ffffffff00000000,0x3ff0001fffc00,0x3def7bdfd6c00)]
def d368 : List (Nat × Nat × Nat) := [(2,0,2),(0,0,2),(0,0,1),(3,6,1)]
def d266 : Array Decor := buildWires d277 d368
def d271 : Array (List (Nat × Nat)) := #[[],[(1,2)]]
def d362 : List (Nat × Nat) := [(subcube 0 32,5),(subcube 32 0,5),(subcube 0 2,4),(subcube 0 4,4),(subcube 0 48,4)]
def d366 : Array (Nat × Nat) := d362.toArray
def d350 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[])]
def d260 : Array (Option BoundPool) := buildPools d266 d13 d366 d350
lemma d330 : goodPairs d255 d349 d342 := goodPairs_of (by decide +kernel)
lemma d278 : ∀ x ∈ d277, faithful d349 d342 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma d267 : ∀ x ∈ d266.toList, faithful d349 d342 x ∧ x.1 < 2^128 := buildWires_faithful d278
lemma d272 : ∀ sw ∈ d271.toList, swapsValid sw = true ∧ permWord sw d255 = d255 := autos_of (by decide +kernel)
lemma d352 : sliceDirectCheck 0 32 0 d13 d255 d156 d144 = true := by decide +kernel
lemma d351 : Slice d13 d255 (subcube 0 32) 5 := slice_direct d352 d334
lemma d354 : sliceDirectCheck 32 0 0 d13 d255 d156 d252 = true := by decide +kernel
lemma d353 : Slice d13 d255 (subcube 32 0) 5 := slice_direct d354 d332
lemma d356 : sliceDirectCheck 0 2 0 d13 d255 d160 d253 = true := by decide +kernel
lemma d355 : Slice d13 d255 (subcube 0 2) 4 := slice_direct d356 d336
lemma d358 : sliceDirectCheck 0 4 0 d13 d255 d158 d254 = true := by decide +kernel
lemma d357 : Slice d13 d255 (subcube 0 4) 4 := slice_direct d358 d337
lemma d360 : sliceDirectCheck 0 48 0 d13 d255 d159 d148 = true := by decide +kernel
lemma d359 : Slice d13 d255 (subcube 0 48) 4 := slice_direct d360 d331
set_option maxRecDepth 200000 in
lemma d367 : ∀ i (hi : i < d366.size), Slice d13 d255 d366[i].1 d366[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice d13 d255 p.1 p.2) (forall_cons d351 (forall_cons d353 (forall_cons d355 (forall_cons d357 (forall_cons d359 (fun _ h => (List.not_mem_nil h).elim))))))
lemma d261 : ∀ i (hi : i < d260.size), ∀ c, d260[i] = some c → ValidPool d13 d255 c := buildPools_sound d367
lemma d305 : ∀ i (hi : i < d285.size), ∀ xs ∈ d285[i], Impossible d255 (0 - 1) xs.toFinset := by intro i hi; simp [d285] at hi
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d314 : checkNodes d266 d255 d206 d260 d271 d285 0 d86 = true := by decide +kernel
def d294 : Array (List (List Nat)) := buildBuckets 1 d266 d86
lemma d295 : ∀ i (hi : i < d294.size), ∀ xs ∈ d294[i], Impossible d255 0 xs.toFinset :=
  buildBuckets_sound (by decide) d330 d267 d261 d272 d305 d314
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d315 : checkNodes d266 d255 d206 d260 d271 d294 1 d86 = true := by decide +kernel
lemma d296 : ∀ i (hi : i < d294.size), ∀ xs ∈ d294[i], Impossible d255 1 xs.toFinset :=
  buildBuckets_sound (by decide) d330 d267 d261 d272 d295 d315
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d316 : checkNodes d266 d255 d206 d260 d271 d294 2 d86 = true := by decide +kernel
lemma d297 : ∀ i (hi : i < d294.size), ∀ xs ∈ d294[i], Impossible d255 2 xs.toFinset :=
  buildBuckets_sound (by decide) d330 d267 d261 d272 d296 d316
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d317 : checkNodes d266 d255 d206 d260 d271 d294 3 d86 = true := by decide +kernel
lemma d298 : ∀ i (hi : i < d294.size), ∀ xs ∈ d294[i], Impossible d255 3 xs.toFinset :=
  buildBuckets_sound (by decide) d330 d267 d261 d272 d297 d317
def d344 : List NodeSpec := [([8,0,2,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d318 : checkNodes d266 d255 d206 d260 d271 d294 4 d344 = true := by decide +kernel
def d299 : Array (List (List Nat)) := buildBuckets 1 d266 d344
lemma d300 : ∀ i (hi : i < d299.size), ∀ xs ∈ d299[i], Impossible d255 4 xs.toFinset :=
  buildBuckets_sound (by decide) d330 d267 d261 d272 d298 d318
def d345 : List NodeSpec := [([5,0,1,2,3,4],[0,1,2],[]),([6,0,1,2,3,4],[3],[0]),([7,0,1,2,3,4],[2],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d319 : checkNodes d266 d255 d206 d260 d271 d299 5 d345 = true := by decide +kernel
def d301 : Array (List (List Nat)) := buildBuckets 2 d266 d345
lemma d302 : ∀ i (hi : i < d301.size), ∀ xs ∈ d301[i], Impossible d255 5 xs.toFinset :=
  buildBuckets_sound (by decide) d330 d267 d261 d272 d300 d319
def d346 : List NodeSpec := [([0,1,2,3,4],[2,3,4,1],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d320 : checkNodes d266 d255 d206 d260 d271 d301 6 d346 = true := by decide +kernel
def d303 : Array (List (List Nat)) := buildBuckets 1 d266 d346
lemma d304 : ∀ i (hi : i < d303.size), ∀ xs ∈ d303[i], Impossible d255 6 xs.toFinset :=
  buildBuckets_sound (by decide) d330 d267 d261 d272 d302 d320
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d327 : forestRootCheck d13 d255 [(VAR 1,22,20),(VAR 2,22,18),(VAR 3,26,18),(VAR 4,22,6),(VAR 5,42,10)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d326 : bucketContains d303 d13 = true := by decide +kernel
lemma d339 : Lower d13 d255 7 := lower_of_forest d327 d304 d326
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q4d : Lower (varsOf 62) 0xfcf0f000ccc0c000fcf0f000ccc0c000 7 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (1, 2), (2, 3), (1, 2)]) (roots2 := d13) (T2 := d255) _ d339
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q4 : Lower (varsOf 62) 0xfffcfcccfff0f0c0fffcfcccfff0f0c0 7 := dualLower (by decide +kernel) (by decide +kernel) q4d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q5d : Lower (varsOf 61) 0xfaf0f000aaa0a000faf0f000aaa0a000 7 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (1, 2), (2, 3), (1, 2), (0, 1)]) (roots2 := d13) (T2 := d255) _ d339
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q5 : Lower (varsOf 61) 0xfffafaaafff0f0a0fffafaaafff0f0a0 7 := dualLower (by decide +kernel) (by decide +kernel) q5d
def d387 : BT Decor := buildWiresBT 2 d273 d110
set_option maxRecDepth 500000 in
lemma d388 : btAll (fun x => faithful d347 d340 x ∧ x.1 < 2^128) d387 := buildWiresBT_faithful d274
set_option maxRecDepth 500000 in
lemma d394 : btAll (fun sw => swapsValid sw = true ∧ permWord sw d148 = d148) d24 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma d462 : btAll (fun o => ∀ p, o = some p → Slice d159 d148 p.1 p.2) d106 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice d159 d148 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma d402 : btAll (fun bk => ∀ xs ∈ bk, Impossible d148 2 xs.toFinset) d38 := trivial
def d376 : BT (Option BoundPool) := buildPoolsSubBT 1 d387 d159 d106 d233 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d415 : checkNodesBT d387 d148 d64 d376 d24 d38 3 d87 = true := by decide +kernel
def d403 : BT (List (List Nat)) := buildBucketsBT d387 d87
set_option maxRecDepth 500000 in
lemma d404 : btAll (fun bk => ∀ xs ∈ bk, Impossible d148 3 xs.toFinset) d403 :=
  buildBucketsBT_sound (by decide) d328 d388 (buildPoolsSubBT_sound d462) d394 d402 d415
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma d422 : forestRootCheck d159 d148 [(VAR 1,6,4),(VAR 2,6,2),(VAR 3,10,2)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma d421 : bucketContainsBT d403 d159 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma d429 : Lower d159 d148 4 := lower_of_forestBT d422 d404 d421
def d369 : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def d381 : List Nat := varsOf 7
lemma d434 : carryOK [(0,3),(0,2),(0,1)] d381 d369 d159 d148 = true := by decide +kernel
lemma d430 : Lower d381 d369 4 := carry_of d434 d429
def d372 : Nat := 0xeaeaeaeae8e8e8e8eaeaeaeae8e8e8e8
def d384 : List Nat := varsOf 39
lemma d436 : liftCheck 32 0 d384 d372 d381 d369 [(VAR 5,33,1)] = true := by decide +kernel
lemma d435 : Lower d384 d372 5 := lift_of d436 d430
def d373 : Nat := 0xfaaafaaaf0a0f0a0faaafaaaf0a0f0a0
def d385 : List Nat := varsOf 45
def d448 : List Nat := [5,5,12,12,13,33,33,37,41,41,44,44,5,5,5,12,12,12,33,33,33]
def d443 : List Nat := [4,1,8,4,9,32,1,36,40,9,40,36,9,36,40,9,36,40,9,36,40]
def d400 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x1c73f3,0x49252),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x3fc9f,0x92889),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x38f1c,0x16d714),(0xffffffff00000000ffffffff00000000,0x1c0fe0,0x1b6da0)]
def d391 : BT Decor := buildWiresBT 2 d400 d110
lemma d428 : goodPairs d373 d448 d443 := goodPairs_of (by decide +kernel)
lemma d401 : ∀ x ∈ d400, faithful d448 d443 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma d392 : btAll (fun x => faithful d448 d443 x ∧ x.1 < 2^128) d391 := buildWiresBT_faithful d401
set_option maxRecDepth 500000 in
lemma d397 : btAll (fun sw => swapsValid sw = true ∧ permWord sw d373 = d373) d24 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma d465 : btAll (fun o => ∀ p, o = some p → Slice d385 d373 p.1 p.2) d106 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice d385 d373 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma d412 : btAll (fun bk => ∀ xs ∈ bk, Impossible d373 2 xs.toFinset) d38 := trivial
def d380 : BT (Option BoundPool) := buildPoolsSubBT 1 d391 d385 d106 d233 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d419 : checkNodesBT d391 d373 d321 d380 d24 d38 3 d343 = true := by decide +kernel
def d413 : BT (List (List Nat)) := buildBucketsBT d391 d343
set_option maxRecDepth 500000 in
lemma d414 : btAll (fun bk => ∀ xs ∈ bk, Impossible d373 3 xs.toFinset) d413 :=
  buildBucketsBT_sound (by decide) d428 d392 (buildPoolsSubBT_sound d465) d397 d412 d419
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma d426 : forestRootCheck d385 d373 [(VAR 0,5,4),(VAR 2,5,1),(VAR 3,12,4),(VAR 5,33,1)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma d425 : bucketContainsBT d413 d385 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma d437 : Lower d385 d373 4 := lower_of_forestBT d426 d414 d425
def d374 : Nat := 0xfce8fce8fce8fce8fce8fce8fce8fce8
def d386 : List Nat := varsOf 15
lemma d439 : liftCheck 1 0 d386 d374 d159 d148 [(VAR 0,3,2)] = true := by decide +kernel
lemma d438 : Lower d386 d374 5 := lift_of d439 d429
def d375 : Nat := 0xfeeafeeafeeafeeafeeafeeafeeafeea
lemma d441 : liftCheck 1 0 d386 d375 d159 d148 [(VAR 0,1,0)] = true := by decide +kernel
lemma d440 : Lower d386 d375 5 := lift_of d441 d429
def d370 : Nat := 0xeeaaeeaacc88cc88eeaaeeaacc88cc88
def d382 : List Nat := varsOf 43
lemma d432 : carryOK [(1,2)] d382 d370 d385 d373 = true := by decide +kernel
lemma d431 : Lower d382 d370 4 := carry_of d432 d437
def d371 : Nat := 0xfeeafeeafce8fce8feeafeeafce8fce8
def d383 : List Nat := varsOf 47
def d447 : List Nat := [3,3,5,5,6,6,10,10,11,12,12,13,33,33,35,37,38,38,41,41,42,42,44,44,3,3,3,3,5,5,5,5,6,6,6,6,10,10,10,10,12,12,12,12,33,33,33,33]
def d442 : List Nat := [2,1,4,1,4,2,8,2,9,8,4,9,32,1,34,36,36,34,40,9,40,34,40,36,9,34,36,40,9,34,36,40,9,34,36,40,9,34,36,40,9,34,36,40,9,34,36,40]
def d420 : Nat := fullMask 48
def d398 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf000ff0cf90f,0x11111108290a),(0xcccccccccccccccccccccccccccccccc,0xff0f3341f3,0x2222222240a1),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf0ff0c38e3c,0x444444818414),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xff000fc0fc0,0x9999995c0b40),(0xffffffff00000000ffffffff00000000,0xf00000fff000,0xeeeeeef7d000)]
def d466 : List (Nat × Nat × Nat) := [(1,1,2),(2,5,3)]
def d389 : BT Decor := buildWiresBT 3 d398 d466
def d393 : List (List (Nat × Nat)) := [[]]
def d395 : BT (List (Nat × Nat)) := btOfList 1 d393
def d461 : List (Option (Nat × Nat)) := [some (subcubeFast 2 0,4),some (subcubeFast 8 0,5),some (subcubeFast 0 32,5),some (subcubeFast 32 0,5),some (subcubeFast 1 32,4),some (subcubeFast 4 0,4)]
def d463 : BT (Option (Nat × Nat)) := btOfList 3 d461
lemma d427 : goodPairs d371 d447 d442 := goodPairs_of (by decide +kernel)
lemma d399 : ∀ x ∈ d398, faithful d447 d442 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma d390 : btAll (fun x => faithful d447 d442 x ∧ x.1 < 2^128) d389 := buildWiresBT_faithful d399
set_option maxRecDepth 500000 in
lemma d396 : btAll (fun sw => swapsValid sw = true ∧ permWord sw d371 = d371) d395 := btAll_ofList (autos_of (by decide +kernel))
lemma d450 : sliceDirectCheck 2 0 0 d383 d371 d385 d373 = true := by decide +kernel
lemma d449 : Slice d383 d371 (subcubeFast 2 0) 4 := slice_fast_direct d450 d437
lemma d452 : sliceDirectCheck 8 0 0 d383 d371 d384 d372 = true := by decide +kernel
lemma d451 : Slice d383 d371 (subcubeFast 8 0) 5 := slice_fast_direct d452 d435
lemma d454 : sliceDirectCheck 0 32 0 d383 d371 d386 d375 = true := by decide +kernel
lemma d453 : Slice d383 d371 (subcubeFast 0 32) 5 := slice_fast_direct d454 d440
lemma d456 : sliceDirectCheck 32 0 0 d383 d371 d386 d374 = true := by decide +kernel
lemma d455 : Slice d383 d371 (subcubeFast 32 0) 5 := slice_fast_direct d456 d438
lemma d458 : sliceDirectCheck 1 32 0 d383 d371 d159 d148 = true := by decide +kernel
lemma d457 : Slice d383 d371 (subcubeFast 1 32) 4 := slice_fast_direct d458 d429
lemma d460 : sliceDirectCheck 4 0 0 d383 d371 d382 d370 = true := by decide +kernel
lemma d459 : Slice d383 d371 (subcubeFast 4 0) 4 := slice_fast_direct d460 d431
set_option maxRecDepth 500000 in
lemma d464 : btAll (fun o => ∀ p, o = some p → Slice d383 d371 p.1 p.2) d463 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice d383 d371 p.1 p.2) (forall_cons (fun _ h => by cases h; exact d449) (forall_cons (fun _ h => by cases h; exact d451) (forall_cons (fun _ h => by cases h; exact d453) (forall_cons (fun _ h => by cases h; exact d455) (forall_cons (fun _ h => by cases h; exact d457) (forall_cons (fun _ h => by cases h; exact d459) (fun _ h => (List.not_mem_nil h).elim)))))))
lemma d405 : btAll (fun bk => ∀ xs ∈ bk, Impossible d371 3 xs.toFinset) d38 := trivial
def d444 : List NodeSpec := [([6,0,1,2,4],[],[])]
def d377 : BT (Option BoundPool) := buildPoolsSubBT 3 d389 d383 d463 d234 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d416 : checkNodesBT d389 d371 d420 d377 d395 d38 4 d444 = true := by decide +kernel
def d406 : BT (List (List Nat)) := buildBucketsBT d389 d444
set_option maxRecDepth 500000 in
lemma d407 : btAll (fun bk => ∀ xs ∈ bk, Impossible d371 4 xs.toFinset) d406 :=
  buildBucketsBT_sound (by decide) d427 d390 (buildPoolsSubBT_sound d464) d396 d405 d416
def d445 : List NodeSpec := [([0,1,2,5,3,4],[0,1,2,3],[0])]
def d378 : BT (Option BoundPool) := buildPoolsSubBT 3 d389 d383 d463 d234 [0,1,2,3]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d417 : checkNodesBT d389 d371 d420 d378 d395 d406 5 d445 = true := by decide +kernel
def d408 : BT (List (List Nat)) := buildBucketsBT d389 d445
set_option maxRecDepth 500000 in
lemma d409 : btAll (fun bk => ∀ xs ∈ bk, Impossible d371 5 xs.toFinset) d408 :=
  buildBucketsBT_sound (by decide) d427 d390 (buildPoolsSubBT_sound d464) d396 d407 d417
def d446 : List NodeSpec := [([0,1,2,3,4],[4,1,3,0,5],[0])]
def d379 : BT (Option BoundPool) := buildPoolsSubBT 3 d389 d383 d463 d234 [0,1,3,4,5]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d418 : checkNodesBT d389 d371 d420 d379 d395 d408 6 d446 = true := by decide +kernel
def d410 : BT (List (List Nat)) := buildBucketsBT d389 d446
set_option maxRecDepth 500000 in
lemma d411 : btAll (fun bk => ∀ xs ∈ bk, Impossible d371 6 xs.toFinset) d410 :=
  buildBucketsBT_sound (by decide) d427 d390 (buildPoolsSubBT_sound d464) d396 d409 d418
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma d424 : forestRootCheck d383 d371 [(VAR 0,3,2),(VAR 1,3,1),(VAR 2,5,1),(VAR 3,10,2),(VAR 5,33,1)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma d423 : bucketContainsBT d410 d383 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma d433 : Lower d383 d371 7 := lower_of_forestBT d424 d411 d423
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q6 : Lower (varsOf 55) 0xfefeeeeef8f8e8e8fefeeeeef8f8e8e8 7 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (0, 1), (1, 2)]) (roots2 := d383) (T2 := d371) _ d433
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q7 : Lower (varsOf 47) 0xfeeefeeef8e8f8e8feeefeeef8e8f8e8 7 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (3, 4), (0, 1), (1, 2)]) (roots2 := d383) (T2 := d371) _ d433
  decide +kernel
def d482 : List Nat := [18,20,6,6,20,18]
def d477 : List Nat := [16,16,2,4,4,2]
def d476 : Nat := fullMask 6
def d468 : List Decor := [(0xcccccccccccccccccccccccccccccccc,45,36),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,30,24),(0xffff0000ffff0000ffff0000ffff0000,51,3)]
def d485 : BT Decor := buildWiresBT 2 d468 d110
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma d479 : goodPairs d4 d482 d477 := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma d469 : ∀ x ∈ d468, faithful d482 d477 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma d486 : btAll (fun x => faithful d482 d477 x ∧ x.1 < 2^128) d485 := buildWiresBT_faithful d469
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma d467 : btAll (fun sw => swapsValid sw = true ∧ permWord sw d4 = d4) d395 := btAll_ofList (autos_of (by decide +kernel))
def d480 : BT (Option BoundPool) := buildPoolsBT 1 d485 d15 d106 d94
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma d483 : btAll (fun o => ∀ p, o = some p → Slice d15 d4 p.1 p.2) d106 := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice d15 d4 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma d481 : btAll (fun o => ∀ c, o = some c → ValidPool d15 d4 c) d480 := buildPoolsBT_sound d483
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma d475 : btAll (fun bk => ∀ xs ∈ bk, Impossible d4 (3 - 1) xs.toFinset) d38 := trivial
def d470 : List NodeSpec := [([0,1,2],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma d484 : checkNodesBT d485 d4 d476 d480 d395 d38 3 d470 = true := by decide +kernel
def d478 : List NodeSpec := d470
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma d474 : checkNodesBT d485 d4 d476 d480 d395 d38 3 d478 = true := d484
def d472 : BT (List (List Nat)) := buildBucketsBT d485 d478
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma d473 : btAll (fun bk => ∀ xs ∈ bk, Impossible d4 3 xs.toFinset) d472 := buildBucketsBT_sound (by decide) d479 d486 d481 d467 d475 d474
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma d471 : Lower d15 d4 4 := lower_of_forestBT (essPairs := [(VAR 1,4,6),(VAR 2,2,6),(VAR 4,2,18)]) (by decide +kernel) d473 (by decide +kernel)
def d489 : List Nat := varsOf 55
def d488 : Nat := 0xfefeeaeafcfcc0c0fefeeaeafcfcc0c0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma d487 : Lower d489 d488 6 := lift_of (z := 1) (o := 32) (essPairs := [(VAR 0,32,33),(VAR 5,1,33)]) (by decide +kernel) d471
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q8 : Lower (varsOf 59) 0xffeeeeeeff888888ffeeeeeeff888888 6 := by
  apply carry_of (swaps := [(4, 5), (0, 1), (1, 2), (2, 3)]) (roots2 := d489) (T2 := d488) _ d487
  decide +kernel
def d516 : List Nat := [6,6,18,18,20,20,6,18,20]
def d515 : List Nat := [4,2,16,2,16,4,16,4,2]
def d496 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xcf,0x10a),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x173,0xa1),(0xffff0000ffff0000ffff0000ffff0000,0x1bc,0x54)]
def d493 : Array Decor := buildWires d496 d110
def d491 : Array (Option BoundPool) := buildPools d493 d15 d363 d94
lemma d511 : goodPairs d4 d516 d515 := goodPairs_of (by decide +kernel)
lemma d497 : ∀ x ∈ d496, faithful d516 d515 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma d494 : ∀ x ∈ d493.toList, faithful d516 d515 x ∧ x.1 < 2^128 := buildWires_faithful d497
lemma d495 : ∀ sw ∈ d268.toList, swapsValid sw = true ∧ permWord sw d4 = d4 := autos_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma d517 : ∀ i (hi : i < d363.size), Slice d15 d4 d363[i].1 d363[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice d15 d4 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma d492 : ∀ i (hi : i < d491.size), ∀ c, d491[i] = some c → ValidPool d15 d4 c := buildPools_sound d517
lemma d504 : ∀ i (hi : i < d285.size), ∀ xs ∈ d285[i], Impossible d4 (0 - 1) xs.toFinset := by intro i hi; simp [d285] at hi
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d505 : checkNodes d493 d4 d64 d491 d268 d285 0 d86 = true := by decide +kernel
def d498 : Array (List (List Nat)) := buildBuckets 1 d493 d86
lemma d499 : ∀ i (hi : i < d498.size), ∀ xs ∈ d498[i], Impossible d4 0 xs.toFinset :=
  buildBuckets_sound (by decide) d511 d494 d492 d495 d504 d505
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d506 : checkNodes d493 d4 d64 d491 d268 d498 1 d86 = true := by decide +kernel
lemma d500 : ∀ i (hi : i < d498.size), ∀ xs ∈ d498[i], Impossible d4 1 xs.toFinset :=
  buildBuckets_sound (by decide) d511 d494 d492 d495 d499 d506
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d507 : checkNodes d493 d4 d64 d491 d268 d498 2 d86 = true := by decide +kernel
lemma d501 : ∀ i (hi : i < d498.size), ∀ xs ∈ d498[i], Impossible d4 2 xs.toFinset :=
  buildBuckets_sound (by decide) d511 d494 d492 d495 d500 d507
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d508 : checkNodes d493 d4 d64 d491 d268 d498 3 d87 = true := by decide +kernel
def d502 : Array (List (List Nat)) := buildBuckets 1 d493 d87
lemma d503 : ∀ i (hi : i < d502.size), ∀ xs ∈ d502[i], Impossible d4 3 xs.toFinset :=
  buildBuckets_sound (by decide) d511 d494 d492 d495 d501 d508
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d510 : forestRootCheck d15 d4 [(VAR 1,6,4),(VAR 2,6,2),(VAR 4,18,2)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d509 : bucketContains d502 d15 = true := by decide +kernel
lemma d512 : Lower d15 d4 4 := lower_of_forest d510 d503 d509
def d490 : Nat := 0xfc00c000fc00c000fc00c000fc00c000
lemma d514 : liftCheck 0 8 d156 d490 d15 d4 [(VAR 3,14,6)] = true := by decide +kernel
lemma d513 : Lower d156 d490 5 := lift_of d514 d512
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q9d : Lower (varsOf 51) 0xeeee000088880000eeee000088880000 5 := by
  apply carry_of (swaps := [(4, 5), (3, 4), (0, 1), (1, 2)]) (roots2 := d156) (T2 := d490) _ d513
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q9 : Lower (varsOf 51) 0xffffeeeeffff8888ffffeeeeffff8888 5 := dualLower (by decide +kernel) (by decide +kernel) q9d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q10d : Lower (varsOf 43) 0xee00ee0088008800ee00ee0088008800 5 := by
  apply carry_of (swaps := [(4, 5), (0, 1), (1, 2)]) (roots2 := d156) (T2 := d490) _ d513
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q10 : Lower (varsOf 43) 0xffeeffeeff88ff88ffeeffeeff88ff88 5 := dualLower (by decide +kernel) (by decide +kernel) q10d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q11d : Lower (varsOf 39) 0xe0e0e0e080808080e0e0e0e080808080 5 := by
  apply carry_of (swaps := [(4, 5), (0, 1), (1, 2), (2, 3)]) (roots2 := d156) (T2 := d490) _ d513
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q11 : Lower (varsOf 39) 0xfefefefef8f8f8f8fefefefef8f8f8f8 5 := dualLower (by decide +kernel) (by decide +kernel) q11d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q12 : Lower (varsOf 35) 0xeeeeeeee88888888eeeeeeee88888888 4 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (0, 1), (1, 2)]) (roots2 := d159) (T2 := d148) _ d331
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q13 : Lower (varsOf 28) 0xfff0f000fff0f000fff0f000fff0f000 4 := by
  apply carry_of (swaps := [(3, 4), (2, 3), (1, 2)]) (roots2 := d159) (T2 := d148) _ d331
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q14 : Lower (varsOf 7) 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8 4 := by
  apply carry_of (swaps := [(0, 1), (1, 2), (2, 3)]) (roots2 := d159) (T2 := d148) _ d331
  decide +kernel
def s0NR : List Nat := varsOf 63
def s0NG : Nat := 0xfffefeeefff8f8e8fffefeeefff8f8e8
def s0NPos : List Nat := [3,3,3,3,3,5,5,5,5,6,6,11,11,12,12,12,12,12,13,14,19,19,20,21,22,24,24,25,25,26,26,33,33,33,34,34,37,38,41,41,42,44,44,49,50,52,52,56,56]
def s0NNeg : List Nat := [0,1,2,4,10,0,1,4,9,2,4,9,10,0,4,8,9,10,9,10,17,18,4,17,18,8,16,9,17,10,18,1,32,36,2,32,36,36,9,40,40,36,40,17,48,36,48,40,48]
def s0NMask : Nat := fullMask 49
def s0NBase : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x8d398b419ff,0x84098950942),(0xcccccccccccccccccccccccccccccccc,0x112c61381e1f,0x4612a1214),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x663001cfe7e0,0x223200404488),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x187c07e0ff800,0x85c02a0f9910),(0xffff0000ffff0000ffff0000ffff0000,0x1f8007ff00000,0x1580055b00000),(0xffffffff00000000ffffffff00000000,0x1ffff80000000,0x1f7bb00000000)]
def s0NSteps : List (Nat × Nat × Nat) := [(1,0,1),(1,0,2),(1,1,2),(3,1,7),(1,6,2),(3,0,10),(2,6,5),(1,12,2),(1,2,3),(2,14,4),(2,2,3),(1,12,16),(1,2,4),(2,2,4),(1,3,4),(1,16,0),(1,16,1),(1,16,6),(3,1,2),(1,2,5),(3,0,2),(1,26,1),(1,26,5),(1,0,3),(3,1,29),(1,0,4),(1,1,3),(1,1,4),(2,21,1),(1,16,5)]
def s0NW : BT Decor := buildWiresBT 6 s0NBase s0NSteps
def s0NAutoList : List (List (Nat × Nat)) := [[],[(3,4)],[(0,1)],[(0,1),(3,4)]]
def s0NAutos : BT (List (Nat × Nat)) := btOfList 2 s0NAutoList
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
def s0NSliceList : List (Option (Nat × Nat)) := [some (subcubeFast 32 0,8),some (subcubeFast 1 0,7),some (subcubeFast 2 0,7),some (subcubeFast 8 0,7),some (subcubeFast 16 0,7),some (subcubeFast 4 0,6),some (subcubeFast 4 8,5),some (subcubeFast 4 16,5),some (subcubeFast 16 8,5),some (subcubeFast 12 16,4),some (subcubeFast 20 8,4),some (subcubeFast 3 32,4),some (subcubeFast 35 0,4),some (subcubeFast 56 0,4)]
def s0NSlices : BT (Option (Nat × Nat)) := btOfList 4 s0NSliceList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice0 : Slice s0NR s0NG (subcubeFast 32 0) 8 := slice_fast_direct (zDead := 0) (qRoots := varsOf 31) (qGoal := 0xfff8f8e8fff8f8e8fff8f8e8fff8f8e8) (by decide +kernel) q3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice1 : Slice s0NR s0NG (subcubeFast 1 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 62) (qGoal := 0xfffcfcccfff0f0c0fffcfcccfff0f0c0) (by decide +kernel) q4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice2 : Slice s0NR s0NG (subcubeFast 2 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 61) (qGoal := 0xfffafaaafff0f0a0fffafaaafff0f0a0) (by decide +kernel) q5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice3 : Slice s0NR s0NG (subcubeFast 8 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 55) (qGoal := 0xfefeeeeef8f8e8e8fefeeeeef8f8e8e8) (by decide +kernel) q6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice4 : Slice s0NR s0NG (subcubeFast 16 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 47) (qGoal := 0xfeeefeeef8e8f8e8feeefeeef8e8f8e8) (by decide +kernel) q7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice5 : Slice s0NR s0NG (subcubeFast 4 0) 6 := slice_fast_direct (zDead := 0) (qRoots := varsOf 59) (qGoal := 0xffeeeeeeff888888ffeeeeeeff888888) (by decide +kernel) q8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice6 : Slice s0NR s0NG (subcubeFast 4 8) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 51) (qGoal := 0xffffeeeeffff8888ffffeeeeffff8888) (by decide +kernel) q9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice7 : Slice s0NR s0NG (subcubeFast 4 16) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 43) (qGoal := 0xffeeffeeff88ff88ffeeffeeff88ff88) (by decide +kernel) q10
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice8 : Slice s0NR s0NG (subcubeFast 16 8) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 39) (qGoal := 0xfefefefef8f8f8f8fefefefef8f8f8f8) (by decide +kernel) q11
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice9 : Slice s0NR s0NG (subcubeFast 12 16) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 35) (qGoal := 0xeeeeeeee88888888eeeeeeee88888888) (by decide +kernel) q12
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice10 : Slice s0NR s0NG (subcubeFast 20 8) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 35) (qGoal := 0xeeeeeeee88888888eeeeeeee88888888) (by decide +kernel) q12
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice11 : Slice s0NR s0NG (subcubeFast 3 32) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 28) (qGoal := 0xfff0f000fff0f000fff0f000fff0f000) (by decide +kernel) q13
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice12 : Slice s0NR s0NG (subcubeFast 35 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 28) (qGoal := 0xfff0f000fff0f000fff0f000fff0f000) (by decide +kernel) q13
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlice13 : Slice s0NR s0NG (subcubeFast 56 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 7) (qGoal := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8) (by decide +kernel) q14
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NSlicesOk : btAll (fun o => ∀ p, o = some p → Slice s0NR s0NG p.1 p.2) s0NSlices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice s0NR s0NG p.1 p.2) (forall_cons (fun _ h => by cases h; exact s0NSlice0) (forall_cons (fun _ h => by cases h; exact s0NSlice1) (forall_cons (fun _ h => by cases h; exact s0NSlice2) (forall_cons (fun _ h => by cases h; exact s0NSlice3) (forall_cons (fun _ h => by cases h; exact s0NSlice4) (forall_cons (fun _ h => by cases h; exact s0NSlice5) (forall_cons (fun _ h => by cases h; exact s0NSlice6) (forall_cons (fun _ h => by cases h; exact s0NSlice7) (forall_cons (fun _ h => by cases h; exact s0NSlice8) (forall_cons (fun _ h => by cases h; exact s0NSlice9) (forall_cons (fun _ h => by cases h; exact s0NSlice10) (forall_cons (fun _ h => by cases h; exact s0NSlice11) (forall_cons (fun _ h => by cases h; exact s0NSlice12) (forall_cons (fun _ h => by cases h; exact s0NSlice13) (fun _ h => (List.not_mem_nil h).elim)))))))))))))))
def s0NEmpty : BT (List (List Nat)) := BT.empty
lemma s0NEmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible s0NG (5 - 1) xs.toFinset) s0NEmpty := trivial
def s0NB5_0S : List PoolSpec := []
def s0NB5_0P : BT (Option BoundPool) := buildPoolsBT 1 s0NW s0NR s0NSlices s0NB5_0S
def s0NB5_0 : List NodeSpec := [([12,15,0,1,2,3],[],[]),([17,0,1,2,3,4],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NB5_0Ok : checkNodesBT s0NW s0NG s0NMask s0NB5_0P s0NAutos s0NEmpty 5 s0NB5_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NB5_0Mem : ∀ ns ∈ s0NB5_0, Impossible s0NG 5 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NEmptyOk s0NB5_0Ok
def s0NNodes5 : List NodeSpec := s0NB5_0
def s0NK5 : BT (List (List Nat)) := buildBucketsBT s0NW s0NNodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NK5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s0NG 5 xs.toFinset) s0NK5 := buildBucketsBT_of_mem s0NB5_0Mem
def s0NB6_0S : List PoolSpec := [(11,[]),(4,[(1,0,1),(2,6,5)])]
def s0NB6_0P : BT (Option BoundPool) := buildPoolsBT 1 s0NW s0NR s0NSlices s0NB6_0S
def s0NB6_0 : List NodeSpec := [([12,16,0,1,2,3,4],[0],[0]),([12,0,1,2,3,14,4],[1],[0]),([12,0,1,2,3,4,20],[1],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NB6_0Ok : checkNodesBT s0NW s0NG s0NMask s0NB6_0P s0NAutos s0NK5 6 s0NB6_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NB6_0Mem : ∀ ns ∈ s0NB6_0, Impossible s0NG 6 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NK5Ok s0NB6_0Ok
def s0NB6_1S : List PoolSpec := [(11,[]),(13,[]),(1,[(1,2,3),(2,14,4)])]
def s0NB6_1P : BT (Option BoundPool) := buildPoolsBT 2 s0NW s0NR s0NSlices s0NB6_1S
def s0NB6_1 : List NodeSpec := [([15,0,1,6,2,3,5],[1,2],[0]),([34,0,1,2,3,4,5],[],[]),([9,6,2,7,3,4,5],[0],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NB6_1Ok : checkNodesBT s0NW s0NG s0NMask s0NB6_1P s0NAutos s0NK5 6 s0NB6_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NB6_1Mem : ∀ ns ∈ s0NB6_1, Impossible s0NG 6 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NK5Ok s0NB6_1Ok
def s0NB6_2S : List PoolSpec := [(11,[]),(5,[]),(12,[])]
def s0NB6_2P : BT (Option BoundPool) := buildPoolsBT 2 s0NW s0NR s0NSlices s0NB6_2S
def s0NB6_2 : List NodeSpec := [([11,1,2,7,3,4,5],[0],[]),([11,1,2,10,3,4,5],[0,2],[]),([11,1,7,8,3,4,5],[1],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NB6_2Ok : checkNodesBT s0NW s0NG s0NMask s0NB6_2P s0NAutos s0NK5 6 s0NB6_2 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NB6_2Mem : ∀ ns ∈ s0NB6_2, Impossible s0NG 6 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NK5Ok s0NB6_2Ok
def s0NB6_3S : List PoolSpec := [(11,[]),(12,[])]
def s0NB6_3P : BT (Option BoundPool) := buildPoolsBT 1 s0NW s0NR s0NSlices s0NB6_3S
def s0NB6_3 : List NodeSpec := [([0,1,23,2,3,4,5],[0,1],[]),([0,1,2,13,3,4],[0],[]),([21,1,6,2,3,4,5],[0],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NB6_3Ok : checkNodesBT s0NW s0NG s0NMask s0NB6_3P s0NAutos s0NK5 6 s0NB6_3 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NB6_3Mem : ∀ ns ∈ s0NB6_3, Impossible s0NG 6 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NK5Ok s0NB6_3Ok
def s0NB6_4S : List PoolSpec := [(11,[]),(5,[]),(12,[]),(6,[]),(7,[])]
def s0NB6_4P : BT (Option BoundPool) := buildPoolsBT 3 s0NW s0NR s0NSlices s0NB6_4S
def s0NB6_4 : List NodeSpec := [([6,2,7,8,3,4,5],[0,1,2],[]),([6,7,8,3,4,5],[0,3,4],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NB6_4Ok : checkNodesBT s0NW s0NG s0NMask s0NB6_4P s0NAutos s0NK5 6 s0NB6_4 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NB6_4Mem : ∀ ns ∈ s0NB6_4, Impossible s0NG 6 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NK5Ok s0NB6_4Ok
def s0NNodes6 : List NodeSpec := s0NB6_0 ++ s0NB6_1 ++ s0NB6_2 ++ s0NB6_3 ++ s0NB6_4
def s0NK6 : BT (List (List Nat)) := buildBucketsBT s0NW s0NNodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NK6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s0NG 6 xs.toFinset) s0NK6 := buildBucketsBT_of_mem (forall_append (forall_append (forall_append (forall_append s0NB6_0Mem s0NB6_1Mem) s0NB6_2Mem) s0NB6_3Mem) s0NB6_4Mem)
def s0NB7_0S : List PoolSpec := [(11,[]),(5,[]),(4,[(1,0,1),(2,6,5)]),(3,[(1,0,1),(2,6,5)]),(1,[(1,2,3),(2,14,4)]),(9,[]),(0,[(1,0,1),(2,2,3)]),(1,[(2,2,3)]),(0,[(1,2,3),(2,14,4)]),(2,[(1,2,3),(2,14,4)])]
def s0NB7_0P : BT (Option BoundPool) := buildPoolsBT 4 s0NW s0NR s0NSlices s0NB7_0S
def s0NB7_0 : List NodeSpec := [([12,0,1,2,3,4],[0,2,3],[0,1]),([15,0,1,2,3,5],[4,5,8,9],[0]),([16,0,1,6,2,3,4,5],[0,1,6,7],[0,2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NB7_0Ok : checkNodesBT s0NW s0NG s0NMask s0NB7_0P s0NAutos s0NK6 7 s0NB7_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NB7_0Mem : ∀ ns ∈ s0NB7_0, Impossible s0NG 7 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NK6Ok s0NB7_0Ok
def s0NB7_1S : List PoolSpec := [(11,[]),(5,[]),(12,[]),(9,[]),(8,[])]
def s0NB7_1P : BT (Option BoundPool) := buildPoolsBT 3 s0NW s0NR s0NSlices s0NB7_1S
def s0NB7_1 : List NodeSpec := [([24,0,1,7,3,4,5],[0,3],[]),([9,0,1,2,7,3,4,5],[0,1],[0,2]),([9,0,1,2,3,4,5],[0,2,3,4],[2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NB7_1Ok : checkNodesBT s0NW s0NG s0NMask s0NB7_1P s0NAutos s0NK6 7 s0NB7_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NB7_1Mem : ∀ ns ∈ s0NB7_1, Impossible s0NG 7 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NK6Ok s0NB7_1Ok
def s0NB7_2S : List PoolSpec := [(11,[]),(6,[]),(9,[]),(1,[(2,2,3)]),(10,[]),(0,[])]
def s0NB7_2P : BT (Option BoundPool) := buildPoolsBT 3 s0NW s0NR s0NSlices s0NB7_2S
def s0NB7_2 : List NodeSpec := [([30,0,1,2,3,4,5],[0,4],[]),([26,0,1,3,4,25],[0,1],[]),([0,21,1,2,3,4,5],[0,2,3,5],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NB7_2Ok : checkNodesBT s0NW s0NG s0NMask s0NB7_2P s0NAutos s0NK6 7 s0NB7_2 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NB7_2Mem : ∀ ns ∈ s0NB7_2, Impossible s0NG 7 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NK6Ok s0NB7_2Ok
def s0NB7_3S : List PoolSpec := [(11,[]),(6,[]),(13,[]),(9,[]),(1,[(1,2,3)]),(4,[(1,0,1)]),(1,[(1,3,4)])]
def s0NB7_3P : BT (Option BoundPool) := buildPoolsBT 3 s0NW s0NR s0NSlices s0NB7_3S
def s0NB7_3 : List NodeSpec := [([0,1,27,2,3,4,5],[0,3],[]),([0,1,6,2,3,14,4,5],[1,2,3,4,5],[0]),([0,1,6,2,3,4,20,5],[1,2,5,6],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NB7_3Ok : checkNodesBT s0NW s0NG s0NMask s0NB7_3P s0NAutos s0NK6 7 s0NB7_3 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NB7_3Mem : ∀ ns ∈ s0NB7_3, Impossible s0NG 7 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NK6Ok s0NB7_3Ok
def s0NB7_4S : List PoolSpec := [(11,[]),(5,[]),(12,[]),(9,[])]
def s0NB7_4P : BT (Option BoundPool) := buildPoolsBT 2 s0NW s0NR s0NSlices s0NB7_4S
def s0NB7_4 : List NodeSpec := [([0,1,2,7,8,3,4,5],[0,1,2],[0,2]),([0,1,2,7,10,3,4,5],[0,2],[0,2]),([0,1,2,7,3,4,25],[0,3],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NB7_4Ok : checkNodesBT s0NW s0NG s0NMask s0NB7_4P s0NAutos s0NK6 7 s0NB7_4 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NB7_4Mem : ∀ ns ∈ s0NB7_4, Impossible s0NG 7 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NK6Ok s0NB7_4Ok
def s0NB7_5S : List PoolSpec := [(11,[]),(12,[]),(6,[]),(7,[]),(13,[]),(9,[])]
def s0NB7_5P : BT (Option BoundPool) := buildPoolsBT 3 s0NW s0NR s0NSlices s0NB7_5S
def s0NB7_5 : List NodeSpec := [([0,1,2,10,3,4,5],[0,1,2,3,4],[0,2]),([0,1,2,3,4,35],[0,5],[]),([0,1,2,3,4,28],[0,5],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NB7_5Ok : checkNodesBT s0NW s0NG s0NMask s0NB7_5P s0NAutos s0NK6 7 s0NB7_5 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NB7_5Mem : ∀ ns ∈ s0NB7_5, Impossible s0NG 7 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NK6Ok s0NB7_5Ok
def s0NB7_6S : List PoolSpec := [(11,[]),(12,[]),(6,[]),(7,[]),(9,[]),(10,[])]
def s0NB7_6P : BT (Option BoundPool) := buildPoolsBT 3 s0NW s0NR s0NSlices s0NB7_6S
def s0NB7_6 : List NodeSpec := [([0,1,7,8,3,4,5],[0,2,3],[0,2]),([0,1,7,3,4,25],[0,4,5],[]),([1,6,2,7,3,4,5],[0,1,2,3],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NB7_6Ok : checkNodesBT s0NW s0NG s0NMask s0NB7_6P s0NAutos s0NK6 7 s0NB7_6 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NB7_6Mem : ∀ ns ∈ s0NB7_6, Impossible s0NG 7 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NK6Ok s0NB7_6Ok
def s0NNodes7 : List NodeSpec := s0NB7_0 ++ s0NB7_1 ++ s0NB7_2 ++ s0NB7_3 ++ s0NB7_4 ++ s0NB7_5 ++ s0NB7_6
def s0NK7 : BT (List (List Nat)) := buildBucketsBT s0NW s0NNodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NK7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s0NG 7 xs.toFinset) s0NK7 := buildBucketsBT_of_mem (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append s0NB7_0Mem s0NB7_1Mem) s0NB7_2Mem) s0NB7_3Mem) s0NB7_4Mem) s0NB7_5Mem) s0NB7_6Mem)
def s0NB8_0S : List PoolSpec := [(11,[]),(6,[]),(7,[]),(9,[]),(4,[(1,0,1)]),(1,[(2,2,3)]),(3,[(1,0,1)]),(0,[(1,0,1)]),(1,[]),(0,[]),(0,[(2,2,3)]),(2,[(2,2,3)])]
def s0NB8_0P : BT (Option BoundPool) := buildPoolsBT 4 s0NW s0NR s0NSlices s0NB8_0S
def s0NB8_0 : List NodeSpec := [([16,0,1,2,3,4,5],[3,5,10,11],[0,2]),([26,0,1,2,3,4,5],[0,3,8,9],[0,2]),([0,1,6,2,3,4,5],[0,1,2,4,6,7,8],[0,1,2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NB8_0Ok : checkNodesBT s0NW s0NG s0NMask s0NB8_0P s0NAutos s0NK7 8 s0NB8_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NB8_0Mem : ∀ ns ∈ s0NB8_0, Impossible s0NG 8 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NK7Ok s0NB8_0Ok
def s0NB8_1S : List PoolSpec := [(11,[]),(6,[]),(13,[]),(9,[]),(1,[(1,2,3)]),(1,[]),(10,[]),(0,[(1,0,2)]),(3,[]),(0,[(1,2,3)]),(4,[]),(2,[(1,2,3)])]
def s0NB8_1P : BT (Option BoundPool) := buildPoolsBT 4 s0NW s0NR s0NSlices s0NB8_1S
def s0NB8_1 : List NodeSpec := [([0,1,2,7,3,4,5],[0,3,5,6,7],[0]),([0,1,2,3,29,4,5],[0,2,6,8],[0]),([0,1,2,3,14,4,5],[1,3,4,9,10,11],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NB8_1Ok : checkNodesBT s0NW s0NG s0NMask s0NB8_1P s0NAutos s0NK7 8 s0NB8_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NB8_1Mem : ∀ ns ∈ s0NB8_1, Impossible s0NG 8 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NK7Ok s0NB8_1Ok
def s0NB8_2S : List PoolSpec := [(11,[]),(13,[]),(9,[]),(1,[(1,3,4)]),(10,[]),(0,[]),(3,[]),(2,[(1,3,4)])]
def s0NB8_2P : BT (Option BoundPool) := buildPoolsBT 3 s0NW s0NR s0NSlices s0NB8_2S
def s0NB8_2 : List NodeSpec := [([0,1,2,3,4,20,5],[1,2,3,6,7],[0]),([0,1,2,3,4,25],[0,2,4,5],[0,2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NB8_2Ok : checkNodesBT s0NW s0NG s0NMask s0NB8_2P s0NAutos s0NK7 8 s0NB8_2 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NB8_2Mem : ∀ ns ∈ s0NB8_2, Impossible s0NG 8 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NK7Ok s0NB8_2Ok
def s0NNodes8 : List NodeSpec := s0NB8_0 ++ s0NB8_1 ++ s0NB8_2
def s0NK8 : BT (List (List Nat)) := buildBucketsBT s0NW s0NNodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NK8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s0NG 8 xs.toFinset) s0NK8 := buildBucketsBT_of_mem (forall_append (forall_append s0NB8_0Mem s0NB8_1Mem) s0NB8_2Mem)
def s0NB9_0S : List PoolSpec := [(1,[]),(0,[]),(3,[]),(4,[]),(2,[])]
def s0NB9_0P : BT (Option BoundPool) := buildPoolsBT 3 s0NW s0NR s0NSlices s0NB9_0S
def s0NB9_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,4],[0,1,2,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NB9_0Ok : checkNodesBT s0NW s0NG s0NMask s0NB9_0P s0NAutos s0NK8 9 s0NB9_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NB9_0Mem : ∀ ns ∈ s0NB9_0, Impossible s0NG 9 (nodeValsBT s0NW ns).toFinset := checkNodesBT_mem (by decide) s0NPairs s0NWOk (buildPoolsBT_sound s0NSlicesOk) s0NAutosOk s0NK8Ok s0NB9_0Ok
def s0NNodes9 : List NodeSpec := s0NB9_0
def s0NK9 : BT (List (List Nat)) := buildBucketsBT s0NW s0NNodes9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NK9Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s0NG 9 xs.toFinset) s0NK9 := buildBucketsBT_of_mem s0NB9_0Mem
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s0NBound : Lower s0NR s0NG 10 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 3,4,12),(VAR 4,4,20),(VAR 5,1,33)]) (by decide +kernel) s0NK9Ok (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q2 : Lower (varsOf 111) 0xfffffffffefafefaffeeffeeeca0eca0 10 := by
  apply carry_of (swaps := [(1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (1, 2), (2, 3), (3, 4), (4, 5), (2, 3)]) (roots2 := s0NR) (T2 := s0NG) _ s0NBound
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q16d : Lower (varsOf 117) 0xfafaa0a000000000a0a0000000000000 8 := by
  apply carry_of (swaps := [(4, 5), (5, 6), (3, 4), (4, 5), (2, 3), (3, 4), (1, 2)]) (roots2 := d14) (T2 := d3) _ d76
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q16 : Lower (varsOf 117) 0xfffffffffffffafafffffffffafaa0a0 8 := dualLower (by decide +kernel) (by decide +kernel) q16d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q15 : Lower (varsOf 119) 0xfffffffffffffefefffffffffefeecec 9 := lift_of (z := 2) (o := 0) (essPairs := [(VAR 1,0,2)]) (by decide +kernel) q16
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q18d : Lower (varsOf 31) 0xa8808000a8808000a8808000a8808000 8 := by
  apply carry_of (swaps := [(2, 3), (1, 2), (0, 1)]) (roots2 := d14) (T2 := d3) _ d76
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q18 : Lower (varsOf 31) 0xfffefeeafffefeeafffefeeafffefeea 8 := dualLower (by decide +kernel) (by decide +kernel) q18d
def d528 : BT Decor := buildWiresBT 2 d496 d110
def d521 : BT (Option BoundPool) := buildPoolsBT 1 d528 d15 d106 d94
set_option maxRecDepth 500000 in
lemma d529 : btAll (fun x => faithful d516 d515 x ∧ x.1 < 2^128) d528 := buildWiresBT_faithful d497
set_option maxRecDepth 500000 in
lemma d533 : btAll (fun sw => swapsValid sw = true ∧ permWord sw d4 = d4) d24 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma d597 : btAll (fun o => ∀ p, o = some p → Slice d15 d4 p.1 p.2) d106 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice d15 d4 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 500000 in
lemma d522 : btAll (fun o => ∀ c, o = some c → ValidPool d15 d4 c) d521 := buildPoolsBT_sound d597
lemma d544 : btAll (fun bk => ∀ xs ∈ bk, Impossible d4 (0 - 1) xs.toFinset) d38 := trivial
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d558 : checkNodesBT d528 d4 d64 d521 d24 d38 0 d86 = true := by decide +kernel
def d538 : BT (List (List Nat)) := buildBucketsBT d528 d86
set_option maxRecDepth 500000 in
lemma d539 : btAll (fun bk => ∀ xs ∈ bk, Impossible d4 0 xs.toFinset) d538 :=
  buildBucketsBT_sound (by decide) d511 d529 d522 d533 d544 d558
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d559 : checkNodesBT d528 d4 d64 d521 d24 d538 1 d86 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma d540 : btAll (fun bk => ∀ xs ∈ bk, Impossible d4 1 xs.toFinset) d538 :=
  buildBucketsBT_sound (by decide) d511 d529 d522 d533 d539 d559
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d560 : checkNodesBT d528 d4 d64 d521 d24 d538 2 d86 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma d541 : btAll (fun bk => ∀ xs ∈ bk, Impossible d4 2 xs.toFinset) d538 :=
  buildBucketsBT_sound (by decide) d511 d529 d522 d533 d540 d560
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d561 : checkNodesBT d528 d4 d64 d521 d24 d538 3 d87 = true := by decide +kernel
def d542 : BT (List (List Nat)) := buildBucketsBT d528 d87
set_option maxRecDepth 500000 in
lemma d543 : btAll (fun bk => ∀ xs ∈ bk, Impossible d4 3 xs.toFinset) d542 :=
  buildBucketsBT_sound (by decide) d511 d529 d522 d533 d541 d561
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma d585 : forestRootCheck d15 d4 [(VAR 1,6,4),(VAR 2,6,2),(VAR 4,18,2)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma d584 : bucketContainsBT d542 d15 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma d570 : Lower d15 d4 4 := lower_of_forestBT d585 d543 d584

lemma d573 : carryOK [(0,3),(0,4),(0,2),(0,1)] d381 d369 d15 d4 = true := by decide +kernel
lemma d571 : Lower d381 d369 4 := carry_of d573 d570

def d519 : Nat := 0xeeee8888eeee8888eeee8888eeee8888
def d526 : List Nat := varsOf 19
lemma d575 : carryOK [(0,2),(0,1)] d526 d519 d15 d4 = true := by decide +kernel
lemma d574 : Lower d526 d519 4 := carry_of d575 d570

def d520 : Nat := 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0
def d527 : List Nat := varsOf 21
lemma d577 : carryOK [(0,1)] d527 d520 d15 d4 = true := by decide +kernel
lemma d576 : Lower d527 d520 4 := carry_of d577 d570

def d518 : Nat := 0xfefee8e8fefee8e8fefee8e8fefee8e8
def d525 : List Nat := varsOf 23
def d583 : List Nat := [3,3,5,5,6,6,17,17,18,18,20,20,3,3,5,5,6,6,17,17,18,18,20,20]
def d578 : List Nat := [2,1,4,1,4,2,16,1,16,2,16,4,4,16,2,16,1,16,2,4,1,4,1,2]
def d536 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcf0cf,0x51008a),(0xcccccccccccccccccccccccccccccccc,0x333333,0x844221),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xc3cc3c,0x281814),(0xffff0000ffff0000ffff0000ffff0000,0xfc0fc0,0x2a540)]
def d600 : List (Nat × Nat × Nat) := [(1,0,1),(2,4,2),(1,4,2),(1,0,2),(2,6,3),(1,1,2)]
def d530 : BT Decor := buildWiresBT 4 d536 d600
def d532 : List (List (Nat × Nat)) := [[],[(2,4)],[(0,1)],[(2,4),(0,1)],[(1,2)],[(1,4),(1,2)],[(0,1),(0,2)],[(1,4),(0,1),(0,2)],[(1,4),(0,2)]]
def d534 : BT (List (Nat × Nat)) := btOfList 4 d532
def d596 : List (Option (Nat × Nat)) := [some (subcubeFast 2 0,4),some (subcubeFast 1 0,4),some (subcubeFast 16 0,4),some (subcubeFast 4 0,4)]
def d598 : BT (Option (Nat × Nat)) := btOfList 2 d596
def d523 : BT (Option BoundPool) := buildPoolsBT 2 d530 d525 d598 d95
lemma d569 : goodPairs d518 d583 d578 := goodPairs_of (by decide +kernel)
lemma d537 : ∀ x ∈ d536, faithful d583 d578 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma d531 : btAll (fun x => faithful d583 d578 x ∧ x.1 < 2^128) d530 := buildWiresBT_faithful d537
set_option maxRecDepth 500000 in
lemma d535 : btAll (fun sw => swapsValid sw = true ∧ permWord sw d518 = d518) d534 := btAll_ofList (autos_of (by decide +kernel))
lemma d589 : sliceDirectCheck 2 0 0 d525 d518 d527 d520 = true := by decide +kernel
lemma d588 : Slice d525 d518 (subcubeFast 2 0) 4 := slice_fast_direct d589 d576
lemma d591 : sliceDirectCheck 1 0 0 d525 d518 d15 d4 = true := by decide +kernel
lemma d590 : Slice d525 d518 (subcubeFast 1 0) 4 := slice_fast_direct d591 d570
lemma d593 : sliceDirectCheck 16 0 0 d525 d518 d381 d369 = true := by decide +kernel
lemma d592 : Slice d525 d518 (subcubeFast 16 0) 4 := slice_fast_direct d593 d571
lemma d595 : sliceDirectCheck 4 0 0 d525 d518 d526 d519 = true := by decide +kernel
lemma d594 : Slice d525 d518 (subcubeFast 4 0) 4 := slice_fast_direct d595 d574
set_option maxRecDepth 500000 in
lemma d599 : btAll (fun o => ∀ p, o = some p → Slice d525 d518 p.1 p.2) d598 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice d525 d518 p.1 p.2) (forall_cons (fun _ h => by cases h; exact d588) (forall_cons (fun _ h => by cases h; exact d590) (forall_cons (fun _ h => by cases h; exact d592) (forall_cons (fun _ h => by cases h; exact d594) (fun _ h => (List.not_mem_nil h).elim)))))
set_option maxRecDepth 500000 in
lemma d524 : btAll (fun o => ∀ c, o = some c → ValidPool d525 d518 c) d523 := buildPoolsBT_sound d599
lemma d557 : btAll (fun bk => ∀ xs ∈ bk, Impossible d518 (0 - 1) xs.toFinset) d38 := trivial
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d562 : checkNodesBT d530 d518 d65 d523 d534 d38 0 d86 = true := by decide +kernel
def d545 : BT (List (List Nat)) := buildBucketsBT d530 d86
set_option maxRecDepth 500000 in
lemma d546 : btAll (fun bk => ∀ xs ∈ bk, Impossible d518 0 xs.toFinset) d545 :=
  buildBucketsBT_sound (by decide) d569 d531 d524 d535 d557 d562
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d563 : checkNodesBT d530 d518 d65 d523 d534 d545 1 d86 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma d547 : btAll (fun bk => ∀ xs ∈ bk, Impossible d518 1 xs.toFinset) d545 :=
  buildBucketsBT_sound (by decide) d569 d531 d524 d535 d546 d563
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d564 : checkNodesBT d530 d518 d65 d523 d534 d545 2 d86 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma d548 : btAll (fun bk => ∀ xs ∈ bk, Impossible d518 2 xs.toFinset) d545 :=
  buildBucketsBT_sound (by decide) d569 d531 d524 d535 d547 d564
def d579 : List NodeSpec := [([8,0,1,2],[],[]),([4,7,9,3],[0,1],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d565 : checkNodesBT d530 d518 d65 d523 d534 d545 3 d579 = true := by decide +kernel
def d549 : BT (List (List Nat)) := buildBucketsBT d530 d579
set_option maxRecDepth 500000 in
lemma d550 : btAll (fun bk => ∀ xs ∈ bk, Impossible d518 3 xs.toFinset) d549 :=
  buildBucketsBT_sound (by decide) d569 d531 d524 d535 d548 d565
def d580 : List NodeSpec := [([5,0,1,2,3],[],[]),([0,1,2,6,3],[2],[0]),([1,4,2,7,3],[0,3],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d566 : checkNodesBT d530 d518 d65 d523 d534 d549 4 d580 = true := by decide +kernel
def d551 : BT (List (List Nat)) := buildBucketsBT d530 d580
set_option maxRecDepth 500000 in
lemma d552 : btAll (fun bk => ∀ xs ∈ bk, Impossible d518 4 xs.toFinset) d551 :=
  buildBucketsBT_sound (by decide) d569 d531 d524 d535 d550 d566
def d581 : List NodeSpec := [([0,1,4,2,3],[0,1,3,2],[0,1,2,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d567 : checkNodesBT d530 d518 d65 d523 d534 d551 5 d581 = true := by decide +kernel
def d553 : BT (List (List Nat)) := buildBucketsBT d530 d581
set_option maxRecDepth 500000 in
lemma d554 : btAll (fun bk => ∀ xs ∈ bk, Impossible d518 5 xs.toFinset) d553 :=
  buildBucketsBT_sound (by decide) d569 d531 d524 d535 d552 d567
def d582 : List NodeSpec := [([0,1,2,3],[0,1,3,2],[0,4,5,6,7,8])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d568 : checkNodesBT d530 d518 d65 d523 d534 d553 6 d582 = true := by decide +kernel
def d555 : BT (List (List Nat)) := buildBucketsBT d530 d582
set_option maxRecDepth 500000 in
lemma d556 : btAll (fun bk => ∀ xs ∈ bk, Impossible d518 6 xs.toFinset) d555 :=
  buildBucketsBT_sound (by decide) d569 d531 d524 d535 d554 d568
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma d587 : forestRootCheck d525 d518 [(VAR 0,3,2),(VAR 1,3,1),(VAR 2,5,1),(VAR 4,17,1)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma d586 : bucketContainsBT d555 d525 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma d572 : Lower d525 d518 7 := lower_of_forestBT d587 d556 d586

def d603 : List Nat := varsOf 27
def d602 : Nat := 0xffeeee88ffeeee88ffeeee88ffeeee88
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma d601 : Lower d603 d602 7 := carry_of (swaps := [(2,3)]) (roots2 := d525) (T2 := d518) (by decide +kernel) d572
def d606 : List Nat := varsOf 59
def d605 : Nat := 0xffeeeeeeffeeee88ffeeeeeeffeeee88
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma d604 : Lower d606 d605 8 := lift_of (z := 32) (o := 0) (essPairs := [(VAR 5,1,33)]) (by decide +kernel) d601
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q19 : Lower (varsOf 31) 0xfffcfce8fffcfce8fffcfce8fffcfce8 8 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (3, 4), (2, 3), (1, 2), (0, 1)]) (roots2 := d606) (T2 := d605) _ d604
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q20d : Lower (varsOf 59) 0xeecccc00aa888800eecccc00aa888800 7 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (1, 2), (2, 3), (0, 1), (1, 2), (0, 1)]) (roots2 := d13) (T2 := d255) _ d339
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q20 : Lower (varsOf 59) 0xffeeeeaaffcccc88ffeeeeaaffcccc88 7 := dualLower (by decide +kernel) (by decide +kernel) q20d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q21 : Lower (varsOf 55) 0xfefeeaeafcfce8e8fefeeaeafcfce8e8 7 := by
  apply carry_of (swaps := [(3, 4)]) (roots2 := d383) (T2 := d371) _ d433
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q22 : Lower (varsOf 47) 0xfeeafeeafce8fce8feeafeeafce8fce8 7 := by
  apply carry_of (swaps := []) (roots2 := d383) (T2 := d371) _ d433
  decide +kernel
def d616 : Array Decor := buildWires d169 d110
def d610 : Array (Option BoundPool) := buildPools d616 d155 d363 d94
lemma d617 : ∀ x ∈ d616.toList, faithful d231 d225 x ∧ x.1 < 2^128 := buildWires_faithful d170
lemma d620 : ∀ sw ∈ d268.toList, swapsValid sw = true ∧ permWord sw d143 = d143 := autos_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma d682 : ∀ i (hi : i < d363.size), Slice d155 d143 d363[i].1 d363[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice d155 d143 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma d611 : ∀ i (hi : i < d610.size), ∀ c, d610[i] = some c → ValidPool d155 d143 c := buildPools_sound d682
lemma d631 : ∀ i (hi : i < d285.size), ∀ xs ∈ d285[i], Impossible d143 (0 - 1) xs.toFinset := by intro i hi; simp [d285] at hi
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d645 : checkNodes d616 d143 d64 d610 d268 d285 0 d86 = true := by decide +kernel
def d625 : Array (List (List Nat)) := buildBuckets 1 d616 d86
lemma d626 : ∀ i (hi : i < d625.size), ∀ xs ∈ d625[i], Impossible d143 0 xs.toFinset :=
  buildBuckets_sound (by decide) d211 d617 d611 d620 d631 d645
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d646 : checkNodes d616 d143 d64 d610 d268 d625 1 d86 = true := by decide +kernel
lemma d627 : ∀ i (hi : i < d625.size), ∀ xs ∈ d625[i], Impossible d143 1 xs.toFinset :=
  buildBuckets_sound (by decide) d211 d617 d611 d620 d626 d646
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d647 : checkNodes d616 d143 d64 d610 d268 d625 2 d86 = true := by decide +kernel
lemma d628 : ∀ i (hi : i < d625.size), ∀ xs ∈ d625[i], Impossible d143 2 xs.toFinset :=
  buildBuckets_sound (by decide) d211 d617 d611 d620 d627 d647
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d648 : checkNodes d616 d143 d64 d610 d268 d625 3 d87 = true := by decide +kernel
def d629 : Array (List (List Nat)) := buildBuckets 1 d616 d87
lemma d630 : ∀ i (hi : i < d629.size), ∀ xs ∈ d629[i], Impossible d143 3 xs.toFinset :=
  buildBuckets_sound (by decide) d211 d617 d611 d620 d628 d648
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d657 : forestRootCheck d155 d143 [(VAR 3,24,16),(VAR 4,24,8),(VAR 5,40,8)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d656 : bucketContains d629 d155 = true := by decide +kernel
lemma d661 : Lower d155 d143 4 := lower_of_forest d657 d630 d656
def d607 : Nat := 0xfff0f000fff0f000fff0f000fff0f000
def d614 : List Nat := varsOf 28
lemma d663 : carryOK [(2,5),(2,4),(2,3)] d614 d607 d155 d143 = true := by decide +kernel
lemma d662 : Lower d614 d607 4 := carry_of d663 d661
def d608 : Nat := 0xfff0fff0f000f000fff0fff0f000f000
def d615 : List Nat := varsOf 44
lemma d665 : carryOK [(2,4),(2,3)] d615 d608 d155 d143 = true := by decide +kernel
lemma d664 : Lower d615 d608 4 := carry_of d665 d661
lemma d667 : carryOK [(2,3)] d11 d0 d155 d143 = true := by decide +kernel
lemma d666 : Lower d11 d0 4 := carry_of d667 d661
def d609 : Nat := 0xfff0f000f0000000fff0f000f0000000
def d672 : List Nat := [28,28,28,44,44,44,52,52,52,56,56,56,28,28,28,44,44,44,52,52,52,56,56,56]
def d669 : List Nat := [24,20,12,40,36,12,48,36,20,48,40,24,36,40,48,20,24,48,12,24,40,12,20,36]
def d623 : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x1ff1ff,0xe491b6),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xe3fe3f,0x3d2c2d),(0xffff0000ffff0000ffff0000ffff0000,0xfc7fc7,0x4bcb43),(0xffffffff00000000ffffffff00000000,0xff8ff8,0x9276d8)]
def d685 : List (Nat × Nat × Nat) := [(0,0,1),(0,0,2),(3,4,2),(0,4,2),(0,1,2),(3,7,3)]
def d618 : Array Decor := buildWires d623 d685
def d621 : Array (List (Nat × Nat)) := #[[],[(4,5)],[(2,3)],[(4,5),(2,3)],[(3,4)],[(3,5),(3,4)],[(2,3),(2,4)],[(3,5),(2,3),(2,4)],[(3,5),(2,4)]]
def d681 : List (Nat × Nat) := [(subcube 0 16,4),(subcube 0 4,4),(subcube 0 8,4),(subcube 0 32,4)]
def d683 : Array (Nat × Nat) := d681.toArray
def d612 : Array (Option BoundPool) := buildPools d618 d160 d683 d95
lemma d660 : goodPairs d609 d672 d669 := goodPairs_of (by decide +kernel)
lemma d624 : ∀ x ∈ d623, faithful d672 d669 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma d619 : ∀ x ∈ d618.toList, faithful d672 d669 x ∧ x.1 < 2^128 := buildWires_faithful d624
lemma d622 : ∀ sw ∈ d621.toList, swapsValid sw = true ∧ permWord sw d609 = d609 := autos_of (by decide +kernel)
lemma d674 : sliceDirectCheck 0 16 0 d160 d609 d615 d608 = true := by decide +kernel
lemma d673 : Slice d160 d609 (subcube 0 16) 4 := slice_direct d674 d664
lemma d676 : sliceDirectCheck 0 4 0 d160 d609 d155 d143 = true := by decide +kernel
lemma d675 : Slice d160 d609 (subcube 0 4) 4 := slice_direct d676 d661
lemma d678 : sliceDirectCheck 0 8 0 d160 d609 d11 d0 = true := by decide +kernel
lemma d677 : Slice d160 d609 (subcube 0 8) 4 := slice_direct d678 d666
lemma d680 : sliceDirectCheck 0 32 0 d160 d609 d614 d607 = true := by decide +kernel
lemma d679 : Slice d160 d609 (subcube 0 32) 4 := slice_direct d680 d662
set_option maxRecDepth 200000 in
lemma d684 : ∀ i (hi : i < d683.size), Slice d160 d609 d683[i].1 d683[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice d160 d609 p.1 p.2) (forall_cons d673 (forall_cons d675 (forall_cons d677 (forall_cons d679 (fun _ h => (List.not_mem_nil h).elim)))))
lemma d613 : ∀ i (hi : i < d612.size), ∀ c, d612[i] = some c → ValidPool d160 d609 c := buildPools_sound d684
lemma d644 : ∀ i (hi : i < d285.size), ∀ xs ∈ d285[i], Impossible d609 (0 - 1) xs.toFinset := by intro i hi; simp [d285] at hi
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d649 : checkNodes d618 d609 d65 d612 d621 d285 0 d86 = true := by decide +kernel
def d632 : Array (List (List Nat)) := buildBuckets 1 d618 d86
lemma d633 : ∀ i (hi : i < d632.size), ∀ xs ∈ d632[i], Impossible d609 0 xs.toFinset :=
  buildBuckets_sound (by decide) d660 d619 d613 d622 d644 d649
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d650 : checkNodes d618 d609 d65 d612 d621 d632 1 d86 = true := by decide +kernel
lemma d634 : ∀ i (hi : i < d632.size), ∀ xs ∈ d632[i], Impossible d609 1 xs.toFinset :=
  buildBuckets_sound (by decide) d660 d619 d613 d622 d633 d650
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d651 : checkNodes d618 d609 d65 d612 d621 d632 2 d86 = true := by decide +kernel
lemma d635 : ∀ i (hi : i < d632.size), ∀ xs ∈ d632[i], Impossible d609 2 xs.toFinset :=
  buildBuckets_sound (by decide) d660 d619 d613 d622 d634 d651
def d670 : List NodeSpec := [([4,5,8,3],[0,1],[]),([9,0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d652 : checkNodes d618 d609 d65 d612 d621 d632 3 d670 = true := by decide +kernel
def d636 : Array (List (List Nat)) := buildBuckets 1 d618 d670
lemma d637 : ∀ i (hi : i < d636.size), ∀ xs ∈ d636[i], Impossible d609 3 xs.toFinset :=
  buildBuckets_sound (by decide) d660 d619 d613 d622 d635 d652
def d671 : List NodeSpec := [([4,5,1,2,3],[0,2],[0]),([6,0,1,2,3],[],[]),([7,0,1,2,3],[3],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d653 : checkNodes d618 d609 d65 d612 d621 d636 4 d671 = true := by decide +kernel
def d638 : Array (List (List Nat)) := buildBuckets 2 d618 d671
lemma d639 : ∀ i (hi : i < d638.size), ∀ xs ∈ d638[i], Impossible d609 4 xs.toFinset :=
  buildBuckets_sound (by decide) d660 d619 d613 d622 d637 d653
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d654 : checkNodes d618 d609 d65 d612 d621 d638 5 d90 = true := by decide +kernel
def d640 : Array (List (List Nat)) := buildBuckets 1 d618 d90
lemma d641 : ∀ i (hi : i < d640.size), ∀ xs ∈ d640[i], Impossible d609 5 xs.toFinset :=
  buildBuckets_sound (by decide) d660 d619 d613 d622 d639 d654
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d655 : checkNodes d618 d609 d65 d612 d621 d640 6 d91 = true := by decide +kernel
def d642 : Array (List (List Nat)) := buildBuckets 1 d618 d91
lemma d643 : ∀ i (hi : i < d642.size), ∀ xs ∈ d642[i], Impossible d609 6 xs.toFinset :=
  buildBuckets_sound (by decide) d660 d619 d613 d622 d641 d655
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d659 : forestRootCheck d160 d609 [(VAR 2,28,24),(VAR 3,28,20),(VAR 4,28,12),(VAR 5,44,12)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d658 : bucketContains d642 d160 = true := by decide +kernel
lemma d668 : Lower d160 d609 7 := lower_of_forest d659 d643 d658
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q23d : Lower (varsOf 30) 0xfcc0c000fcc0c000fcc0c000fcc0c000 7 := by
  apply carry_of (swaps := [(1, 2), (2, 3), (3, 4), (4, 5)]) (roots2 := d160) (T2 := d609) _ d668
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q23 : Lower (varsOf 30) 0xfffcfcc0fffcfcc0fffcfcc0fffcfcc0 7 := dualLower (by decide +kernel) (by decide +kernel) q23d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q24d : Lower (varsOf 29) 0xaaa0a000aaa0a000aaa0a000aaa0a000 5 := by
  apply carry_of (swaps := [(2, 3), (1, 2), (0, 1)]) (roots2 := d156) (T2 := d490) _ d513
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q24 : Lower (varsOf 29) 0xfffafaaafffafaaafffafaaafffafaaa 5 := dualLower (by decide +kernel) (by decide +kernel) q24d
def d712 : List Nat := [5,5,17,17,20,20,5,17,20]
def d711 : List Nat := [4,1,16,1,16,4,16,4,1]
def d695 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcf,0x10a),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x173,0xa1),(0xffff0000ffff0000ffff0000ffff0000,0x1bc,0x54)]
def d692 : BT Decor := buildWiresBT 2 d695 d110
lemma d703 : goodPairs d520 d712 d711 := goodPairs_of (by decide +kernel)
lemma d696 : ∀ x ∈ d695, faithful d712 d711 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma d693 : btAll (fun x => faithful d712 d711 x ∧ x.1 < 2^128) d692 := buildWiresBT_faithful d696
set_option maxRecDepth 500000 in
lemma d694 : btAll (fun sw => swapsValid sw = true ∧ permWord sw d520 = d520) d24 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma d713 : btAll (fun o => ∀ p, o = some p → Slice d527 d520 p.1 p.2) d106 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice d527 d520 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
lemma d697 : btAll (fun bk => ∀ xs ∈ bk, Impossible d520 2 xs.toFinset) d38 := trivial
def d689 : BT (Option BoundPool) := buildPoolsSubBT 1 d692 d527 d106 d233 []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d700 : checkNodesBT d692 d520 d64 d689 d24 d38 3 d87 = true := by decide +kernel
def d698 : BT (List (List Nat)) := buildBucketsBT d692 d87
set_option maxRecDepth 500000 in
lemma d699 : btAll (fun bk => ∀ xs ∈ bk, Impossible d520 3 xs.toFinset) d698 :=
  buildBucketsBT_sound (by decide) d703 d693 (buildPoolsSubBT_sound d713) d694 d697 d700
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma d702 : forestRootCheck d527 d520 [(VAR 0,5,4),(VAR 2,5,1),(VAR 4,17,1)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma d701 : bucketContainsBT d698 d527 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma d704 : Lower d527 d520 4 := lower_of_forestBT d702 d699 d701
def d686 : Nat := 0xfaa0faa0faa0faa0faa0faa0faa0faa0
def d690 : List Nat := varsOf 13
lemma d706 : carryOK [(3,4)] d690 d686 d527 d520 = true := by decide +kernel
lemma d705 : Lower d690 d686 4 := carry_of d706 d704
def d687 : Nat := 0xfaa0faa0fa00fa00faa0faa0fa00fa00
lemma d708 : liftCheck 0 32 d385 d687 d690 d686 [(VAR 5,37,5)] = true := by decide +kernel
lemma d707 : Lower d385 d687 5 := lift_of d708 d705
def d688 : Nat := 0xeeee8888cccc8888eeee8888cccc8888
def d691 : List Nat := varsOf 51
lemma d710 : carryOK [(2,4),(1,2),(1,3)] d691 d688 d385 d687 = true := by decide +kernel
lemma d709 : Lower d691 d688 5 := carry_of d710 d707
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q25d : Lower (varsOf 27) 0xeecccc00eecccc00eecccc00eecccc00 5 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (3, 4), (0, 1), (1, 2), (2, 3), (1, 2), (0, 1)]) (roots2 := d691) (T2 := d688) _ d709
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q25 : Lower (varsOf 27) 0xffcccc88ffcccc88ffcccc88ffcccc88 5 := dualLower (by decide +kernel) (by decide +kernel) q25d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q26d : Lower (varsOf 23) 0xa8a88080a8a88080a8a88080a8a88080 5 := by
  apply carry_of (swaps := [(0, 1), (1, 2), (2, 3), (1, 2), (0, 1)]) (roots2 := d156) (T2 := d490) _ d513
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q26 : Lower (varsOf 23) 0xfefeeaeafefeeaeafefeeaeafefeeaea 5 := dualLower (by decide +kernel) (by decide +kernel) q26d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q27 : Lower (varsOf 53) 0xfafaaaaaf0f0a0a0fafaaaaaf0f0a0a0 4 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (1, 2), (2, 3), (0, 1)]) (roots2 := d160) (T2 := d253) _ d336
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q28 : Lower (varsOf 51) 0xeeeeaaaacccc8888eeeeaaaacccc8888 4 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (1, 2), (2, 3), (0, 1), (1, 2)]) (roots2 := d160) (T2 := d253) _ d336
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q29 : Lower (varsOf 45) 0xfaaafaaaf0a0f0a0faaafaaaf0a0f0a0 4 := by
  apply carry_of (swaps := [(1, 2), (2, 3), (3, 4), (1, 2), (2, 3), (0, 1)]) (roots2 := d160) (T2 := d253) _ d336
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q30 : Lower (varsOf 43) 0xeeaaeeaacc88cc88eeaaeeaacc88cc88 4 := by
  apply carry_of (swaps := [(1, 2), (2, 3), (3, 4), (1, 2), (2, 3), (0, 1), (1, 2)]) (roots2 := d160) (T2 := d253) _ d336
  decide +kernel
def s1NR : List Nat := varsOf 63
def s1NG : Nat := 0xfffefeeafffcfce8fffefeeafffcfce8
def s1NPos : List Nat := [3,3,3,3,5,5,5,5,6,6,10,10,10,11,12,12,12,13,18,18,19,20,20,22,24,24,25,25,26,33,33,38,38,41,41,42,42,44,44,49,49,50,50,52,52,56,56]
def s1NNeg : List Nat := [1,2,9,17,1,4,9,17,2,4,0,2,8,9,0,4,8,9,2,16,17,4,16,2,8,16,9,17,2,1,32,34,36,9,40,34,40,36,40,17,48,34,48,36,48,40,48]
def s1NMask : Nat := fullMask 47
def s1NBase : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x1866c1220ff,0x822c1220dd),(0xcccccccccccccccccccccccccccccccc,0x619909c3f0f,0x20890840902),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x186180e3c3f0,0x82100208220),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x607e1f03fc00,0x205605033044),(0xffff0000ffff0000ffff0000ffff0000,0x7f801ffc0000,0x55800a580088),(0xffffffff00000000ffffffff00000000,0x7fffe0000000,0x7f7dc0000000)]
def s1NSteps : List (Nat × Nat × Nat) := [(1,1,2),(1,1,3),(1,2,3),(1,6,4),(2,6,4),(1,7,4),(2,7,4),(1,8,4),(2,8,4),(1,2,4),(1,3,4),(2,6,3),(1,1,4),(1,6,3),(0,19,4),(2,19,4),(1,19,4),(3,3,22),(1,17,4),(2,17,4),(3,2,7),(3,2,18),(1,26,4),(3,2,11),(1,12,2)]
def s1NW : BT Decor := buildWiresBT 5 s1NBase s1NSteps
def s1NAutoList : List (List (Nat × Nat)) := [[],[(3,4)],[(1,2)],[(1,2),(3,4)]]
def s1NAutos : BT (List (Nat × Nat)) := btOfList 2 s1NAutoList
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
def s1NSliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 32,8),some (subcubeFast 32 0,8),some (subcubeFast 2 0,7),some (subcubeFast 4 0,7),some (subcubeFast 8 0,7),some (subcubeFast 16 0,7),some (subcubeFast 1 32,7),some (subcubeFast 2 32,5),some (subcubeFast 36 0,5),some (subcubeFast 8 32,5),some (subcubeFast 10 0,4),some (subcubeFast 12 0,4),some (subcubeFast 18 0,4),some (subcubeFast 20 0,4),some (subcubeFast 56 0,4)]
def s1NSlices : BT (Option (Nat × Nat)) := btOfList 4 s1NSliceList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlice0 : Slice s1NR s1NG (subcubeFast 0 32) 8 := slice_fast_direct (zDead := 0) (qRoots := varsOf 31) (qGoal := 0xfffefeeafffefeeafffefeeafffefeea) (by decide +kernel) q18
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlice1 : Slice s1NR s1NG (subcubeFast 32 0) 8 := slice_fast_direct (zDead := 0) (qRoots := varsOf 31) (qGoal := 0xfffcfce8fffcfce8fffcfce8fffcfce8) (by decide +kernel) q19
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlice2 : Slice s1NR s1NG (subcubeFast 2 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 61) (qGoal := 0xfffafaaafff0f0a0fffafaaafff0f0a0) (by decide +kernel) q5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlice3 : Slice s1NR s1NG (subcubeFast 4 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 59) (qGoal := 0xffeeeeaaffcccc88ffeeeeaaffcccc88) (by decide +kernel) q20
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlice4 : Slice s1NR s1NG (subcubeFast 8 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 55) (qGoal := 0xfefeeaeafcfce8e8fefeeaeafcfce8e8) (by decide +kernel) q21
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlice5 : Slice s1NR s1NG (subcubeFast 16 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 47) (qGoal := 0xfeeafeeafce8fce8feeafeeafce8fce8) (by decide +kernel) q22
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlice6 : Slice s1NR s1NG (subcubeFast 1 32) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 30) (qGoal := 0xfffcfcc0fffcfcc0fffcfcc0fffcfcc0) (by decide +kernel) q23
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlice7 : Slice s1NR s1NG (subcubeFast 2 32) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 29) (qGoal := 0xfffafaaafffafaaafffafaaafffafaaa) (by decide +kernel) q24
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlice8 : Slice s1NR s1NG (subcubeFast 36 0) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 27) (qGoal := 0xffcccc88ffcccc88ffcccc88ffcccc88) (by decide +kernel) q25
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlice9 : Slice s1NR s1NG (subcubeFast 8 32) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 23) (qGoal := 0xfefeeaeafefeeaeafefeeaeafefeeaea) (by decide +kernel) q26
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlice10 : Slice s1NR s1NG (subcubeFast 10 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 53) (qGoal := 0xfafaaaaaf0f0a0a0fafaaaaaf0f0a0a0) (by decide +kernel) q27
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlice11 : Slice s1NR s1NG (subcubeFast 12 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 51) (qGoal := 0xeeeeaaaacccc8888eeeeaaaacccc8888) (by decide +kernel) q28
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlice12 : Slice s1NR s1NG (subcubeFast 18 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 45) (qGoal := 0xfaaafaaaf0a0f0a0faaafaaaf0a0f0a0) (by decide +kernel) q29
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlice13 : Slice s1NR s1NG (subcubeFast 20 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 43) (qGoal := 0xeeaaeeaacc88cc88eeaaeeaacc88cc88) (by decide +kernel) q30
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlice14 : Slice s1NR s1NG (subcubeFast 56 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 7) (qGoal := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8) (by decide +kernel) q14
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NSlicesOk : btAll (fun o => ∀ p, o = some p → Slice s1NR s1NG p.1 p.2) s1NSlices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice s1NR s1NG p.1 p.2) (forall_cons (fun _ h => by cases h; exact s1NSlice0) (forall_cons (fun _ h => by cases h; exact s1NSlice1) (forall_cons (fun _ h => by cases h; exact s1NSlice2) (forall_cons (fun _ h => by cases h; exact s1NSlice3) (forall_cons (fun _ h => by cases h; exact s1NSlice4) (forall_cons (fun _ h => by cases h; exact s1NSlice5) (forall_cons (fun _ h => by cases h; exact s1NSlice6) (forall_cons (fun _ h => by cases h; exact s1NSlice7) (forall_cons (fun _ h => by cases h; exact s1NSlice8) (forall_cons (fun _ h => by cases h; exact s1NSlice9) (forall_cons (fun _ h => by cases h; exact s1NSlice10) (forall_cons (fun _ h => by cases h; exact s1NSlice11) (forall_cons (fun _ h => by cases h; exact s1NSlice12) (forall_cons (fun _ h => by cases h; exact s1NSlice13) (forall_cons (fun _ h => by cases h; exact s1NSlice14) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))
def s1NEmpty : BT (List (List Nat)) := BT.empty
lemma s1NEmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible s1NG (5 - 1) xs.toFinset) s1NEmpty := trivial
def s1NB5_0S : List PoolSpec := []
def s1NB5_0P : BT (Option BoundPool) := buildPoolsBT 1 s1NW s1NR s1NSlices s1NB5_0S
def s1NB5_0 : List NodeSpec := [([10,0,7,8,4,5],[],[]),([12,0,6,8,4,5],[],[]),([17,0,1,2,20,5],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NB5_0Ok : checkNodesBT s1NW s1NG s1NMask s1NB5_0P s1NAutos s1NEmpty 5 s1NB5_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NB5_0Mem : ∀ ns ∈ s1NB5_0, Impossible s1NG 5 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NEmptyOk s1NB5_0Ok
def s1NB5_1S : List PoolSpec := []
def s1NB5_1P : BT (Option BoundPool) := buildPoolsBT 1 s1NW s1NR s1NSlices s1NB5_1S
def s1NB5_1 : List NodeSpec := [([23,0,1,2,4,5],[],[]),([26,0,2,18,16,5],[],[]),([0,2,7,18,13,5],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NB5_1Ok : checkNodesBT s1NW s1NG s1NMask s1NB5_1P s1NAutos s1NEmpty 5 s1NB5_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NB5_1Mem : ∀ ns ∈ s1NB5_1, Impossible s1NG 5 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NEmptyOk s1NB5_1Ok
def s1NB5_2S : List PoolSpec := [(3,[]),(10,[])]
def s1NB5_2P : BT (Option BoundPool) := buildPoolsBT 1 s1NW s1NR s1NSlices s1NB5_2S
def s1NB5_2 : List NodeSpec := [([0,2,7,9,16,5],[1],[]),([0,6,7,15,16,5],[1],[]),([0,6,8,4,11,5],[0],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NB5_2Ok : checkNodesBT s1NW s1NG s1NMask s1NB5_2P s1NAutos s1NEmpty 5 s1NB5_2 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NB5_2Mem : ∀ ns ∈ s1NB5_2, Impossible s1NG 5 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NEmptyOk s1NB5_2Ok
def s1NB5_3S : List PoolSpec := []
def s1NB5_3P : BT (Option BoundPool) := buildPoolsBT 1 s1NW s1NR s1NSlices s1NB5_3S
def s1NB5_3 : List NodeSpec := [([0,7,8,4,9,5],[],[]),([0,7,8,18,15,5],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NB5_3Ok : checkNodesBT s1NW s1NG s1NMask s1NB5_3P s1NAutos s1NEmpty 5 s1NB5_3 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NB5_3Mem : ∀ ns ∈ s1NB5_3, Impossible s1NG 5 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NEmptyOk s1NB5_3Ok
def s1NNodes5 : List NodeSpec := s1NB5_0 ++ s1NB5_1 ++ s1NB5_2 ++ s1NB5_3
def s1NK5 : BT (List (List Nat)) := buildBucketsBT s1NW s1NNodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NK5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s1NG 5 xs.toFinset) s1NK5 := buildBucketsBT_of_mem (forall_append (forall_append (forall_append s1NB5_0Mem s1NB5_1Mem) s1NB5_2Mem) s1NB5_3Mem)
def s1NB6_0S : List PoolSpec := [(4,[(1,1,2),(2,6,4)]),(3,[(1,1,3),(2,7,4)]),(7,[]),(8,[]),(5,[(1,1,2),(2,6,3)])]
def s1NB6_0P : BT (Option BoundPool) := buildPoolsBT 3 s1NW s1NR s1NSlices s1NB6_0S
def s1NB6_0 : List NodeSpec := [([25,0,1,2,3,4,5],[2,3,4],[]),([10,0,2,3,7,4,5],[0],[0]),([12,0,1,2,8,4,5],[1],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NB6_0Ok : checkNodesBT s1NW s1NG s1NMask s1NB6_0P s1NAutos s1NK5 6 s1NB6_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NB6_0Mem : ∀ ns ∈ s1NB6_0, Impossible s1NG 6 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NK5Ok s1NB6_0Ok
def s1NB6_1S : List PoolSpec := [(3,[(1,1,3),(2,7,4)]),(2,[(1,6,3),(2,19,4)]),(0,[(1,1,2),(1,6,3),(2,19,4)]),(1,[(1,1,2),(1,6,3),(2,19,4)])]
def s1NB6_1P : BT (Option BoundPool) := buildPoolsBT 2 s1NW s1NR s1NSlices s1NB6_1S
def s1NB6_1 : List NodeSpec := [([12,0,2,6,3,4,5],[0],[0]),([21,0,1,2,6,3,5],[1,2,3],[]),([21,0,1,2,3,7,5],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NB6_1Ok : checkNodesBT s1NW s1NG s1NMask s1NB6_1P s1NAutos s1NK5 6 s1NB6_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NB6_1Mem : ∀ ns ∈ s1NB6_1, Impossible s1NG 6 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NK5Ok s1NB6_1Ok
def s1NB6_2S : List PoolSpec := [(1,[(1,1,2),(1,6,3),(2,19,4)]),(5,[(1,1,2)]),(6,[(1,1,2),(1,6,3),(2,19,4)])]
def s1NB6_2P : BT (Option BoundPool) := buildPoolsBT 2 s1NW s1NR s1NSlices s1NB6_2S
def s1NB6_2 : List NodeSpec := [([21,0,1,2,3,19,5],[1],[]),([21,0,1,2,3,4,5],[],[]),([21,0,1,2,3,5],[0,2],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NB6_2Ok : checkNodesBT s1NW s1NG s1NMask s1NB6_2P s1NAutos s1NK5 6 s1NB6_2 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NB6_2Mem : ∀ ns ∈ s1NB6_2, Impossible s1NG 6 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NK5Ok s1NB6_2Ok
def s1NB6_3S : List PoolSpec := [(10,[]),(2,[])]
def s1NB6_3P : BT (Option BoundPool) := buildPoolsBT 1 s1NW s1NR s1NSlices s1NB6_3S
def s1NB6_3 : List NodeSpec := [([17,0,1,2,7,4,5],[1],[]),([17,0,1,2,19,4,5],[1],[0]),([17,0,2,6,7,4,5],[0],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NB6_3Ok : checkNodesBT s1NW s1NG s1NMask s1NB6_3P s1NAutos s1NK5 6 s1NB6_3 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NB6_3Mem : ∀ ns ∈ s1NB6_3, Impossible s1NG 6 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NK5Ok s1NB6_3Ok
def s1NB6_4S : List PoolSpec := [(10,[]),(0,[(1,1,3),(1,7,4),(3,2,11)])]
def s1NB6_4P : BT (Option BoundPool) := buildPoolsBT 1 s1NW s1NR s1NSlices s1NB6_4S
def s1NB6_4 : List NodeSpec := [([26,0,1,2,4,16,5],[0],[0]),([26,0,2,3,4,18,5],[],[0]),([29,0,1,2,3,4,5],[1],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NB6_4Ok : checkNodesBT s1NW s1NG s1NMask s1NB6_4P s1NAutos s1NK5 6 s1NB6_4 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NB6_4Mem : ∀ ns ∈ s1NB6_4, Impossible s1NG 6 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NK5Ok s1NB6_4Ok
def s1NB6_5S : List PoolSpec := [(3,[(1,1,3),(2,7,4)]),(5,[(1,1,2),(2,6,3)])]
def s1NB6_5P : BT (Option BoundPool) := buildPoolsBT 1 s1NW s1NR s1NSlices s1NB6_5S
def s1NB6_5 : List NodeSpec := [([0,1,2,30,3,4,5],[0],[]),([0,1,2,3,20,19,5],[],[0,1]),([0,1,2,3,4,24,5],[1],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NB6_5Ok : checkNodesBT s1NW s1NG s1NMask s1NB6_5P s1NAutos s1NK5 6 s1NB6_5 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NB6_5Mem : ∀ ns ∈ s1NB6_5, Impossible s1NG 6 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NK5Ok s1NB6_5Ok
def s1NB6_6S : List PoolSpec := [(10,[])]
def s1NB6_6P : BT (Option BoundPool) := buildPoolsBT 1 s1NW s1NR s1NSlices s1NB6_6S
def s1NB6_6 : List NodeSpec := [([0,1,2,3,4,28,5],[],[]),([0,1,2,3,4,22,5],[],[0,1]),([0,1,2,7,15,16,5],[0],[0,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NB6_6Ok : checkNodesBT s1NW s1NG s1NMask s1NB6_6P s1NAutos s1NK5 6 s1NB6_6 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NB6_6Mem : ∀ ns ∈ s1NB6_6, Impossible s1NG 6 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NK5Ok s1NB6_6Ok
def s1NB6_7S : List PoolSpec := [(3,[]),(5,[(1,1,2)])]
def s1NB6_7P : BT (Option BoundPool) := buildPoolsBT 1 s1NW s1NR s1NSlices s1NB6_7S
def s1NB6_7 : List NodeSpec := [([0,1,2,8,4,11,5],[0],[0,2]),([0,1,2,19,4,16,5],[1],[1,3]),([0,2,6,3,4,11,5],[0],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NB6_7Ok : checkNodesBT s1NW s1NG s1NMask s1NB6_7P s1NAutos s1NK5 6 s1NB6_7 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NB6_7Mem : ∀ ns ∈ s1NB6_7, Impossible s1NG 6 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NK5Ok s1NB6_7Ok
def s1NB6_8S : List PoolSpec := [(10,[])]
def s1NB6_8P : BT (Option BoundPool) := buildPoolsBT 1 s1NW s1NR s1NSlices s1NB6_8S
def s1NB6_8 : List NodeSpec := [([0,2,6,7,4,16,5],[],[0,2]),([0,2,3,7,4,9,5],[0],[0]),([0,2,7,8,4,18,5],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NB6_8Ok : checkNodesBT s1NW s1NG s1NMask s1NB6_8P s1NAutos s1NK5 6 s1NB6_8 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NB6_8Mem : ∀ ns ∈ s1NB6_8, Impossible s1NG 6 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NK5Ok s1NB6_8Ok
def s1NB6_9S : List PoolSpec := [(2,[(1,2,3)]),(6,[(1,1,2),(1,1,3),(1,2,3)]),(11,[]),(3,[(1,1,3)]),(1,[(1,1,2),(1,1,3),(1,2,3)]),(10,[]),(2,[]),(14,[]),(6,[(1,1,3),(1,1,4),(1,3,4)])]
def s1NB6_9P : BT (Option BoundPool) := buildPoolsBT 4 s1NW s1NR s1NSlices s1NB6_9S
def s1NB6_9 : List NodeSpec := [([0,2,7,18,16,5],[6,7,8],[0,1]),([0,6,3,7,4,15,5],[5],[0,1,2]),([0,6,7,8,4,5],[0,1,2,3,4],[0,2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NB6_9Ok : checkNodesBT s1NW s1NG s1NMask s1NB6_9P s1NAutos s1NK5 6 s1NB6_9 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NB6_9Mem : ∀ ns ∈ s1NB6_9, Impossible s1NG 6 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NK5Ok s1NB6_9Ok
def s1NNodes6 : List NodeSpec := s1NB6_0 ++ s1NB6_1 ++ s1NB6_2 ++ s1NB6_3 ++ s1NB6_4 ++ s1NB6_5 ++ s1NB6_6 ++ s1NB6_7 ++ s1NB6_8 ++ s1NB6_9
def s1NK6 : BT (List (List Nat)) := buildBucketsBT s1NW s1NNodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NK6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s1NG 6 xs.toFinset) s1NK6 := buildBucketsBT_of_mem (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append s1NB6_0Mem s1NB6_1Mem) s1NB6_2Mem) s1NB6_3Mem) s1NB6_4Mem) s1NB6_5Mem) s1NB6_6Mem) s1NB6_7Mem) s1NB6_8Mem) s1NB6_9Mem)
def s1NB7_0S : List PoolSpec := [(10,[]),(3,[(1,1,3),(2,7,4)]),(4,[(1,1,2)]),(7,[]),(8,[]),(2,[(2,6,3)]),(0,[(1,1,2),(2,6,3)]),(1,[(1,1,2),(2,6,3)]),(5,[(1,1,2),(2,6,3)]),(6,[(1,1,2),(2,6,3)]),(3,[(2,6,3)]),(14,[]),(6,[(1,1,3),(2,7,4)])]
def s1NB7_0P : BT (Option BoundPool) := buildPoolsBT 4 s1NW s1NR s1NSlices s1NB7_0S
def s1NB7_0 : List NodeSpec := [([12,0,1,2,3,4,5],[0,1,11,12],[0]),([17,0,1,2,6,3,4,5],[2,3,4,5,6,7],[0,2]),([17,0,1,2,3,4,5],[2,5,7,8,9,10],[0,1,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NB7_0Ok : checkNodesBT s1NW s1NG s1NMask s1NB7_0P s1NAutos s1NK6 7 s1NB7_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NB7_0Mem : ∀ ns ∈ s1NB7_0, Impossible s1NG 7 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NK6Ok s1NB7_0Ok
def s1NB7_1S : List PoolSpec := [(3,[]),(11,[]),(3,[(1,1,3)]),(10,[]),(4,[(1,1,2)]),(2,[(1,6,3)]),(5,[(1,1,2)]),(0,[(1,1,2),(1,6,3)]),(1,[(1,1,2),(1,6,3)]),(14,[]),(2,[(1,3,4)]),(9,[]),(12,[]),(6,[(1,1,3),(3,2,7)])]
def s1NB7_1P : BT (Option BoundPool) := buildPoolsBT 4 s1NW s1NR s1NSlices s1NB7_1S
def s1NB7_1 : List NodeSpec := [([26,0,1,2,3,4,5],[2,3,12,13],[0]),([0,1,2,6,3,19,4,5],[1,3,4,5,6,7,8],[0]),([0,1,2,6,3,4,16,5],[0,4,9,10,11],[0,1,2,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NB7_1Ok : checkNodesBT s1NW s1NG s1NMask s1NB7_1P s1NAutos s1NK6 7 s1NB7_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NB7_1Mem : ∀ ns ∈ s1NB7_1, Impossible s1NG 7 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NK6Ok s1NB7_1Ok
def s1NB7_2S : List PoolSpec := [(11,[]),(10,[]),(14,[]),(12,[]),(13,[])]
def s1NB7_2P : BT (Option BoundPool) := buildPoolsBT 3 s1NW s1NR s1NSlices s1NB7_2S
def s1NB7_2 : List NodeSpec := [([0,1,2,3,7,19,4,5],[0,1,2],[0]),([0,1,2,3,7,4,15,5],[1,4],[0,1,2,3]),([0,1,2,3,7,4,11,5],[1,2,3],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NB7_2Ok : checkNodesBT s1NW s1NG s1NMask s1NB7_2P s1NAutos s1NK6 7 s1NB7_2 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NB7_2Mem : ∀ ns ∈ s1NB7_2, Impossible s1NG 7 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NK6Ok s1NB7_2Ok
def s1NB7_3S : List PoolSpec := [(3,[]),(2,[(1,2,3)]),(11,[]),(3,[(1,1,3)]),(10,[]),(4,[(1,1,2)]),(2,[(1,6,3)]),(5,[(1,1,2)]),(6,[(1,1,2),(1,6,3)]),(3,[(1,6,3)]),(14,[]),(9,[]),(12,[]),(6,[(1,1,3),(1,2,3)]),(6,[(1,1,3),(1,7,4)]),(2,[(1,7,4)])]
def s1NB7_3P : BT (Option BoundPool) := buildPoolsBT 4 s1NW s1NR s1NSlices s1NB7_3S
def s1NB7_3 : List NodeSpec := [([0,1,2,3,19,4,5],[2,4,5,6,7,8,9],[0,1,3]),([0,1,2,3,4,11,5],[0,4,10,12,14,15],[0,1]),([0,1,2,7,8,4,5],[1,2,3,4,11,13],[0,2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NB7_3Ok : checkNodesBT s1NW s1NG s1NMask s1NB7_3P s1NAutos s1NK6 7 s1NB7_3 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NB7_3Mem : ∀ ns ∈ s1NB7_3, Impossible s1NG 7 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NK6Ok s1NB7_3Ok
def s1NB7_4S : List PoolSpec := [(3,[(1,1,3)]),(10,[]),(4,[(1,1,2)]),(6,[(1,1,2),(1,1,3)]),(2,[]),(1,[(1,1,2),(1,1,3)]),(14,[]),(2,[(1,3,4)]),(6,[(1,1,3),(1,1,4)]),(12,[]),(6,[(1,1,3),(1,3,4)])]
def s1NB7_4P : BT (Option BoundPool) := buildPoolsBT 4 s1NW s1NR s1NSlices s1NB7_4S
def s1NB7_4 : List NodeSpec := [([0,1,2,7,4,16,5],[1,6,7,10],[0,2]),([0,2,6,3,7,4,5],[0,1,2,3,4,5],[0]),([0,2,3,7,4,18,5],[1,4,6,8,9],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NB7_4Ok : checkNodesBT s1NW s1NG s1NMask s1NB7_4P s1NAutos s1NK6 7 s1NB7_4 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NB7_4Mem : ∀ ns ∈ s1NB7_4, Impossible s1NG 7 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NK6Ok s1NB7_4Ok
def s1NNodes7 : List NodeSpec := s1NB7_0 ++ s1NB7_1 ++ s1NB7_2 ++ s1NB7_3 ++ s1NB7_4
def s1NK7 : BT (List (List Nat)) := buildBucketsBT s1NW s1NNodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NK7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s1NG 7 xs.toFinset) s1NK7 := buildBucketsBT_of_mem (forall_append (forall_append (forall_append (forall_append s1NB7_0Mem s1NB7_1Mem) s1NB7_2Mem) s1NB7_3Mem) s1NB7_4Mem)
def s1NB8_0S : List PoolSpec := [(3,[]),(3,[(1,1,3)]),(10,[]),(4,[(1,1,2)]),(2,[]),(5,[(1,1,2)]),(14,[]),(2,[(1,3,4)]),(6,[(1,1,2)]),(1,[(1,1,2)]),(6,[(1,1,3)]),(4,[]),(1,[(1,1,3)]),(6,[(1,3,4)]),(3,[(1,3,4)])]
def s1NB8_0P : BT (Option BoundPool) := buildPoolsBT 4 s1NW s1NR s1NSlices s1NB8_0S
def s1NB8_0 : List NodeSpec := [([0,1,2,6,3,4,5],[0,3,4,5,8,9],[0,1,2,3]),([0,1,2,3,7,4,5],[1,2,4,6,10,11,12],[0]),([0,1,2,3,4,16,5],[6,7,11,13,14],[0,1,2,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NB8_0Ok : checkNodesBT s1NW s1NG s1NMask s1NB8_0P s1NAutos s1NK7 8 s1NB8_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NB8_0Mem : ∀ ns ∈ s1NB8_0, Impossible s1NG 8 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NK7Ok s1NB8_0Ok
def s1NNodes8 : List NodeSpec := s1NB8_0
def s1NK8 : BT (List (List Nat)) := buildBucketsBT s1NW s1NNodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NK8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s1NG 8 xs.toFinset) s1NK8 := buildBucketsBT_of_mem s1NB8_0Mem
def s1NB9_0S : List PoolSpec := [(3,[]),(2,[]),(4,[]),(6,[]),(5,[]),(1,[])]
def s1NB9_0P : BT (Option BoundPool) := buildPoolsBT 3 s1NW s1NR s1NSlices s1NB9_0S
def s1NB9_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,4,5],[0,1,2,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NB9_0Ok : checkNodesBT s1NW s1NG s1NMask s1NB9_0P s1NAutos s1NK8 9 s1NB9_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NB9_0Mem : ∀ ns ∈ s1NB9_0, Impossible s1NG 9 (nodeValsBT s1NW ns).toFinset := checkNodesBT_mem (by decide) s1NPairs s1NWOk (buildPoolsBT_sound s1NSlicesOk) s1NAutosOk s1NK8Ok s1NB9_0Ok
def s1NNodes9 : List NodeSpec := s1NB9_0
def s1NK9 : BT (List (List Nat)) := buildBucketsBT s1NW s1NNodes9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NK9Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s1NG 9 xs.toFinset) s1NK9 := buildBucketsBT_of_mem s1NB9_0Mem
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s1NBound : Lower s1NR s1NG 10 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 3,2,10),(VAR 4,2,18),(VAR 5,1,33)]) (by decide +kernel) s1NK9Ok (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q17 : Lower (varsOf 119) 0xfffffffffffffafafefeeeeefafaa0a0 10 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (5, 6), (0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (2, 3), (3, 4), (1, 2)]) (roots2 := s1NR) (T2 := s1NG) _ s1NBound
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q31 : Lower (varsOf 123) 0xffffffffffffeeaaffeeffeeeeaacc00 10 := by
  apply carry_of (swaps := [(1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (1, 2), (2, 3), (3, 4), (4, 5), (3, 4), (2, 3)]) (roots2 := s0NR) (T2 := s0NG) _ s0NBound
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q32 : Lower (varsOf 125) 0xfffffffffffffffafffffffffffaffa0 9 := lift_of (z := 8) (o := 0) (essPairs := [(VAR 3,0,8)]) (by decide +kernel) q16
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q33 : Lower (varsOf 125) 0xfffffffffffffafafffaffaafafaa0a0 10 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (5, 6), (0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (2, 3), (3, 4), (2, 3), (1, 2)]) (roots2 := s1NR) (T2 := s1NG) _ s1NBound
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q35d : Lower (varsOf 55) 0xeaeae0e088888080eaeae0e088888080 7 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (0, 1), (1, 2), (2, 3), (0, 1)]) (roots2 := d13) (T2 := d255) _ d339
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q35 : Lower (varsOf 55) 0xfefeeeeef8f8a8a8fefeeeeef8f8a8a8 7 := dualLower (by decide +kernel) (by decide +kernel) q35d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q36d : Lower (varsOf 47) 0xeae0eae088808880eae0eae088808880 7 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (0, 1), (1, 2), (2, 3), (3, 4), (0, 1)]) (roots2 := d13) (T2 := d255) _ d339
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q36 : Lower (varsOf 47) 0xfeeefeeef8a8f8a8feeefeeef8a8f8a8 7 := dualLower (by decide +kernel) (by decide +kernel) q36d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q37d : Lower (varsOf 31) 0xeae0e000eae0e000eae0e000eae0e000 7 := by
  apply carry_of (swaps := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (1, 2), (2, 3), (3, 4), (0, 1), (1, 2), (2, 3), (0, 1), (1, 2)]) (roots2 := d13) (T2 := d255) _ d339
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q37 : Lower (varsOf 31) 0xfff8f8a8fff8f8a8fff8f8a8fff8f8a8 7 := dualLower (by decide +kernel) (by decide +kernel) q37d
def d141 : List Nat := [6,6,34,34,36,36,6,34,36]
def d140 : List Nat := [4,2,32,2,32,4,32,4,2]
def d119 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xcf,0x10a),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x173,0xa1),(0xffffffff00000000ffffffff00000000,0x1bc,0x54)]
def d116 : BT Decor := buildWiresBT 2 d119 d110
def d114 : BT (Option BoundPool) := buildPoolsBT 1 d116 d16 d106 d94
lemma d134 : goodPairs d5 d141 d140 := goodPairs_of (by decide +kernel)
lemma d120 : ∀ x ∈ d119, faithful d141 d140 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma d117 : btAll (fun x => faithful d141 d140 x ∧ x.1 < 2^128) d116 := buildWiresBT_faithful d120
set_option maxRecDepth 500000 in
lemma d118 : btAll (fun sw => swapsValid sw = true ∧ permWord sw d5 = d5) d24 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma d142 : btAll (fun o => ∀ p, o = some p → Slice d16 d5 p.1 p.2) d106 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice d16 d5 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 500000 in
lemma d115 : btAll (fun o => ∀ c, o = some c → ValidPool d16 d5 c) d114 := buildPoolsBT_sound d142
lemma d127 : btAll (fun bk => ∀ xs ∈ bk, Impossible d5 (0 - 1) xs.toFinset) d38 := trivial
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d128 : checkNodesBT d116 d5 d64 d114 d24 d38 0 d86 = true := by decide +kernel
def d121 : BT (List (List Nat)) := buildBucketsBT d116 d86
set_option maxRecDepth 500000 in
lemma d122 : btAll (fun bk => ∀ xs ∈ bk, Impossible d5 0 xs.toFinset) d121 :=
  buildBucketsBT_sound (by decide) d134 d117 d115 d118 d127 d128
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d129 : checkNodesBT d116 d5 d64 d114 d24 d121 1 d86 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma d123 : btAll (fun bk => ∀ xs ∈ bk, Impossible d5 1 xs.toFinset) d121 :=
  buildBucketsBT_sound (by decide) d134 d117 d115 d118 d122 d129
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d130 : checkNodesBT d116 d5 d64 d114 d24 d121 2 d86 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma d124 : btAll (fun bk => ∀ xs ∈ bk, Impossible d5 2 xs.toFinset) d121 :=
  buildBucketsBT_sound (by decide) d134 d117 d115 d118 d123 d130
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma d131 : checkNodesBT d116 d5 d64 d114 d24 d121 3 d87 = true := by decide +kernel
def d125 : BT (List (List Nat)) := buildBucketsBT d116 d87
set_option maxRecDepth 500000 in
lemma d126 : btAll (fun bk => ∀ xs ∈ bk, Impossible d5 3 xs.toFinset) d125 :=
  buildBucketsBT_sound (by decide) d134 d117 d115 d118 d124 d131
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma d133 : forestRootCheck d16 d5 [(VAR 1,6,4),(VAR 2,6,2),(VAR 5,34,2)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma d132 : bucketContainsBT d125 d16 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma d135 : Lower d16 d5 4 := lower_of_forestBT d133 d126 d132
def d112 : Nat := 0xfcfc0000c0c00000fcfc0000c0c00000
lemma d137 : liftCheck 0 16 d12 d112 d16 d5 [(VAR 4,22,6)] = true := by decide +kernel
lemma d136 : Lower d12 d112 5 := lift_of d137 d135
def d113 : Nat := 0xfc000000c0000000fc000000c0000000
lemma d139 : liftCheck 0 8 d13 d113 d12 d112 [(VAR 3,30,22)] = true := by decide +kernel
lemma d138 : Lower d13 d113 6 := lift_of d139 d136
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q38d : Lower (varsOf 61) 0xaaa0a00000000000aaa0a00000000000 6 := by
  apply carry_of (swaps := [(4, 5), (2, 3), (1, 2), (0, 1)]) (roots2 := d13) (T2 := d113) _ d138
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q38 : Lower (varsOf 61) 0xfffffffffffafaaafffffffffffafaaa 6 := dualLower (by decide +kernel) (by decide +kernel) q38d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q39d : Lower (varsOf 39) 0xeaeaeaea88888888eaeaeaea88888888 5 := by
  apply carry_of (swaps := [(4, 5), (3, 4), (2, 3), (0, 1)]) (roots2 := d691) (T2 := d688) _ d709
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q39 : Lower (varsOf 39) 0xeeeeeeeea8a8a8a8eeeeeeeea8a8a8a8 5 := dualLower (by decide +kernel) (by decide +kernel) q39d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q40d : Lower (varsOf 29) 0xfaf0f000faf0f000faf0f000faf0f000 5 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (3, 4), (0, 1), (1, 2), (2, 3), (0, 1), (1, 2), (0, 1)]) (roots2 := d691) (T2 := d688) _ d709
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q40 : Lower (varsOf 29) 0xfff0f0a0fff0f0a0fff0f0a0fff0f0a0 5 := dualLower (by decide +kernel) (by decide +kernel) q40d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q41 : Lower (varsOf 15) 0xf8a8f8a8f8a8f8a8f8a8f8a8f8a8f8a8 4 := by
  apply carry_of (swaps := [(1, 2), (2, 3), (3, 4), (4, 5), (0, 1), (1, 2), (2, 3), (3, 4), (1, 2), (0, 1)]) (roots2 := d160) (T2 := d253) _ d336
  decide +kernel
def s2NR : List Nat := varsOf 63
def s2NG : Nat := 0xfffefeeefff8f8a8fffefeeefff8f8a8
def s2NPos : List Nat := [3,3,3,3,3,3,5,5,5,5,5,7,11,11,11,12,12,12,13,14,14,19,19,20,20,21,22,24,24,25,25,26,26,33,33,34,34,37,38,38,41,41,42,42,44,44,49,50,50,52]
def s2NNeg : List Nat := [0,1,2,6,9,10,0,1,4,6,9,6,2,9,10,0,4,8,9,6,10,17,18,4,16,17,6,8,16,9,17,10,18,1,32,2,32,36,6,36,9,40,10,40,36,40,17,18,48,36]
def s2NMask : Nat := fullMask 50
def s2NBase : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x432662647fff,0x410262242492),(0xcccccccccccccccccccccccccccccccc,0x18cd98478783f,0x844984585a2c),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x230e0079f8fc0,0x210e004890b08),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x3f01f81ff000,0x2f00a8166430),(0xffff0000ffff0000ffff0000ffff0000,0x3c001ffe00000,0x1c00153600000),(0xffffffff00000000ffffffff00000000,0x3fffe00000000,0x33ab400000000)]
def s2NSteps : List (Nat × Nat × Nat) := [(1,0,1),(2,6,5),(1,2,3),(2,8,4),(2,2,3),(1,2,4),(2,2,4),(1,3,4),(0,6,5),(2,0,1),(1,15,2),(1,10,15),(0,0,2),(1,18,1),(1,18,3),(1,18,4),(1,18,5),(1,0,2),(2,0,2),(3,0,2),(1,0,3),(2,0,3),(1,27,4),(1,0,4),(2,0,4),(1,0,5),(2,0,5),(1,1,2),(3,1,2),(1,1,3),(1,1,4),(1,1,5),(1,2,5),(2,2,5),(1,3,5),(1,4,5)]
def s2NW : BT Decor := buildWiresBT 6 s2NBase s2NSteps
def s2NAutoList : List (List (Nat × Nat)) := [[],[(3,4)],[(1,5)],[(1,5),(3,4)],[(0,2),(1,3),(4,5)],[(0,2),(1,3),(3,5),(4,5)],[(0,2),(1,4),(3,4),(4,5)],[(0,2),(1,4),(3,5)]]
def s2NAutos : BT (List (Nat × Nat)) := btOfList 3 s2NAutoList
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
def s2NSliceList : List (Option (Nat × Nat)) := [some (subcubeFast 2 0,7),some (subcubeFast 8 0,7),some (subcubeFast 16 0,7),some (subcubeFast 32 0,7),some (subcubeFast 0 2,6),some (subcubeFast 4 8,5),some (subcubeFast 8 16,5),some (subcubeFast 16 8,5),some (subcubeFast 24 0,5),some (subcubeFast 34 0,5),some (subcubeFast 12 16,4),some (subcubeFast 20 8,4),some (subcubeFast 3 32,4),some (subcubeFast 33 2,4),some (subcubeFast 48 0,4)]
def s2NSlices : BT (Option (Nat × Nat)) := btOfList 4 s2NSliceList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice0 : Slice s2NR s2NG (subcubeFast 2 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 61) (qGoal := 0xfffafaaafff0f0a0fffafaaafff0f0a0) (by decide +kernel) q5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice1 : Slice s2NR s2NG (subcubeFast 8 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 55) (qGoal := 0xfefeeeeef8f8a8a8fefeeeeef8f8a8a8) (by decide +kernel) q35
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice2 : Slice s2NR s2NG (subcubeFast 16 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 47) (qGoal := 0xfeeefeeef8a8f8a8feeefeeef8a8f8a8) (by decide +kernel) q36
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice3 : Slice s2NR s2NG (subcubeFast 32 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 31) (qGoal := 0xfff8f8a8fff8f8a8fff8f8a8fff8f8a8) (by decide +kernel) q37
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice4 : Slice s2NR s2NG (subcubeFast 0 2) 6 := slice_fast_direct (zDead := 0) (qRoots := varsOf 61) (qGoal := 0xfffffffffffafaaafffffffffffafaaa) (by decide +kernel) q38
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice5 : Slice s2NR s2NG (subcubeFast 4 8) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 51) (qGoal := 0xffffeeeeffff8888ffffeeeeffff8888) (by decide +kernel) q9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice6 : Slice s2NR s2NG (subcubeFast 8 16) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 39) (qGoal := 0xfefefefef8f8f8f8fefefefef8f8f8f8) (by decide +kernel) q11
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice7 : Slice s2NR s2NG (subcubeFast 16 8) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 39) (qGoal := 0xfefefefef8f8f8f8fefefefef8f8f8f8) (by decide +kernel) q11
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice8 : Slice s2NR s2NG (subcubeFast 24 0) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 39) (qGoal := 0xeeeeeeeea8a8a8a8eeeeeeeea8a8a8a8) (by decide +kernel) q39
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice9 : Slice s2NR s2NG (subcubeFast 34 0) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 29) (qGoal := 0xfff0f0a0fff0f0a0fff0f0a0fff0f0a0) (by decide +kernel) q40
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice10 : Slice s2NR s2NG (subcubeFast 12 16) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 35) (qGoal := 0xeeeeeeee88888888eeeeeeee88888888) (by decide +kernel) q12
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice11 : Slice s2NR s2NG (subcubeFast 20 8) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 35) (qGoal := 0xeeeeeeee88888888eeeeeeee88888888) (by decide +kernel) q12
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice12 : Slice s2NR s2NG (subcubeFast 3 32) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 28) (qGoal := 0xfff0f000fff0f000fff0f000fff0f000) (by decide +kernel) q13
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice13 : Slice s2NR s2NG (subcubeFast 33 2) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 28) (qGoal := 0xfff0f000fff0f000fff0f000fff0f000) (by decide +kernel) q13
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlice14 : Slice s2NR s2NG (subcubeFast 48 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 15) (qGoal := 0xf8a8f8a8f8a8f8a8f8a8f8a8f8a8f8a8) (by decide +kernel) q41
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NSlicesOk : btAll (fun o => ∀ p, o = some p → Slice s2NR s2NG p.1 p.2) s2NSlices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice s2NR s2NG p.1 p.2) (forall_cons (fun _ h => by cases h; exact s2NSlice0) (forall_cons (fun _ h => by cases h; exact s2NSlice1) (forall_cons (fun _ h => by cases h; exact s2NSlice2) (forall_cons (fun _ h => by cases h; exact s2NSlice3) (forall_cons (fun _ h => by cases h; exact s2NSlice4) (forall_cons (fun _ h => by cases h; exact s2NSlice5) (forall_cons (fun _ h => by cases h; exact s2NSlice6) (forall_cons (fun _ h => by cases h; exact s2NSlice7) (forall_cons (fun _ h => by cases h; exact s2NSlice8) (forall_cons (fun _ h => by cases h; exact s2NSlice9) (forall_cons (fun _ h => by cases h; exact s2NSlice10) (forall_cons (fun _ h => by cases h; exact s2NSlice11) (forall_cons (fun _ h => by cases h; exact s2NSlice12) (forall_cons (fun _ h => by cases h; exact s2NSlice13) (forall_cons (fun _ h => by cases h; exact s2NSlice14) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))
def s2NEmpty : BT (List (List Nat)) := BT.empty
lemma s2NEmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible s2NG (5 - 1) xs.toFinset) s2NEmpty := trivial
def s2NB5_0S : List PoolSpec := []
def s2NB5_0P : BT (Option BoundPool) := buildPoolsBT 1 s2NW s2NR s2NSlices s2NB5_0S
def s2NB5_0 : List NodeSpec := [([7,9,0,1,2,3],[],[]),([9,0,1,14,2,3],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NB5_0Ok : checkNodesBT s2NW s2NG s2NMask s2NB5_0P s2NAutos s2NEmpty 5 s2NB5_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NB5_0Mem : ∀ ns ∈ s2NB5_0, Impossible s2NG 5 (nodeValsBT s2NW ns).toFinset := checkNodesBT_mem (by decide) s2NPairs s2NWOk (buildPoolsBT_sound s2NSlicesOk) s2NAutosOk s2NEmptyOk s2NB5_0Ok
def s2NNodes5 : List NodeSpec := s2NB5_0
def s2NK5 : BT (List (List Nat)) := buildBucketsBT s2NW s2NNodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NK5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s2NG 5 xs.toFinset) s2NK5 := buildBucketsBT_of_mem s2NB5_0Mem
def s2NB6_0S : List PoolSpec := [(2,[(1,0,1),(2,6,5)])]
def s2NB6_0P : BT (Option BoundPool) := buildPoolsBT 1 s2NW s2NR s2NSlices s2NB6_0S
def s2NB6_0 : List NodeSpec := [([7,10,0,1,2,3,4],[],[]),([7,0,1,2,3,8,4],[0],[0]),([7,0,1,2,3,4,13],[0],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NB6_0Ok : checkNodesBT s2NW s2NG s2NMask s2NB6_0P s2NAutos s2NK5 6 s2NB6_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NB6_0Mem : ∀ ns ∈ s2NB6_0, Impossible s2NG 6 (nodeValsBT s2NW ns).toFinset := checkNodesBT_mem (by decide) s2NPairs s2NWOk (buildPoolsBT_sound s2NSlicesOk) s2NAutosOk s2NK5Ok s2NB6_0Ok
def s2NB6_1S : List PoolSpec := [(12,[]),(14,[]),(4,[])]
def s2NB6_1P : BT (Option BoundPool) := buildPoolsBT 2 s2NW s2NR s2NSlices s2NB6_1S
def s2NB6_1 : List NodeSpec := [([10,0,1,14,2,3,4],[0,2],[]),([17,0,1,2,3,4,5],[],[]),([0,1,14,2,3,8,4],[1],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NB6_1Ok : checkNodesBT s2NW s2NG s2NMask s2NB6_1P s2NAutos s2NK5 6 s2NB6_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NB6_1Mem : ∀ ns ∈ s2NB6_1, Impossible s2NG 6 (nodeValsBT s2NW ns).toFinset := checkNodesBT_mem (by decide) s2NPairs s2NWOk (buildPoolsBT_sound s2NSlicesOk) s2NAutosOk s2NK5Ok s2NB6_1Ok
def s2NB6_2S : List PoolSpec := [(14,[])]
def s2NB6_2P : BT (Option BoundPool) := buildPoolsBT 1 s2NW s2NR s2NSlices s2NB6_2S
def s2NB6_2 : List NodeSpec := [([0,1,14,2,3,4,13],[0],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NB6_2Ok : checkNodesBT s2NW s2NG s2NMask s2NB6_2P s2NAutos s2NK5 6 s2NB6_2 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NB6_2Mem : ∀ ns ∈ s2NB6_2, Impossible s2NG 6 (nodeValsBT s2NW ns).toFinset := checkNodesBT_mem (by decide) s2NPairs s2NWOk (buildPoolsBT_sound s2NSlicesOk) s2NAutosOk s2NK5Ok s2NB6_2Ok
def s2NNodes6 : List NodeSpec := s2NB6_0 ++ s2NB6_1 ++ s2NB6_2
def s2NK6 : BT (List (List Nat)) := buildBucketsBT s2NW s2NNodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NK6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s2NG 6 xs.toFinset) s2NK6 := buildBucketsBT_of_mem (forall_append (forall_append s2NB6_0Mem s2NB6_1Mem) s2NB6_2Mem)
def s2NB7_0S : List PoolSpec := [(2,[(1,0,1),(2,6,5)]),(12,[]),(1,[(1,0,1),(2,6,5)]),(4,[]),(7,[])]
def s2NB7_0P : BT (Option BoundPool) := buildPoolsBT 3 s2NW s2NR s2NSlices s2NB7_0S
def s2NB7_0 : List NodeSpec := [([7,0,1,2,3,4],[0,1,2],[0,1]),([10,15,0,1,2,3,4,5],[3,4],[0]),([10,0,1,6,2,3,4,5],[1,3],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NB7_0Ok : checkNodesBT s2NW s2NG s2NMask s2NB7_0P s2NAutos s2NK6 7 s2NB7_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NB7_0Mem : ∀ ns ∈ s2NB7_0, Impossible s2NG 7 (nodeValsBT s2NW ns).toFinset := checkNodesBT_mem (by decide) s2NPairs s2NWOk (buildPoolsBT_sound s2NSlicesOk) s2NAutosOk s2NK6Ok s2NB7_0Ok
def s2NB7_1S : List PoolSpec := [(12,[]),(4,[]),(2,[(1,0,1)]),(6,[]),(8,[]),(1,[(2,0,1)])]
def s2NB7_1P : BT (Option BoundPool) := buildPoolsBT 3 s2NW s2NR s2NSlices s2NB7_1S
def s2NB7_1 : List NodeSpec := [([15,0,1,2,3,4,13,5],[1,3,4,5],[]),([0,1,6,2,3,8,4,5],[0,1,2],[0,4]),([0,1,6,2,3,4,13,5],[0,1,2],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NB7_1Ok : checkNodesBT s2NW s2NG s2NMask s2NB7_1P s2NAutos s2NK6 7 s2NB7_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NB7_1Mem : ∀ ns ∈ s2NB7_1, Impossible s2NG 7 (nodeValsBT s2NW ns).toFinset := checkNodesBT_mem (by decide) s2NPairs s2NWOk (buildPoolsBT_sound s2NSlicesOk) s2NAutosOk s2NK6Ok s2NB7_1Ok
def s2NB7_2S : List PoolSpec := [(12,[]),(4,[]),(6,[]),(7,[]),(10,[]),(9,[]),(0,[(1,3,4)]),(1,[(1,1,5)])]
def s2NB7_2P : BT (Option BoundPool) := buildPoolsBT 3 s2NW s2NR s2NSlices s2NB7_2S
def s2NB7_2 : List NodeSpec := [([0,1,2,16,3,4,5],[0,2,3],[]),([0,1,2,23,3,4,5],[0,4],[]),([0,1,2,3,4,13,5,37],[1,5,6,7],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NB7_2Ok : checkNodesBT s2NW s2NG s2NMask s2NB7_2P s2NAutos s2NK6 7 s2NB7_2 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NB7_2Mem : ∀ ns ∈ s2NB7_2, Impossible s2NG 7 (nodeValsBT s2NW ns).toFinset := checkNodesBT_mem (by decide) s2NPairs s2NWOk (buildPoolsBT_sound s2NSlicesOk) s2NAutosOk s2NK6Ok s2NB7_2Ok
def s2NB7_3S : List PoolSpec := [(12,[]),(5,[]),(10,[])]
def s2NB7_3P : BT (Option BoundPool) := buildPoolsBT 2 s2NW s2NR s2NSlices s2NB7_3S
def s2NB7_3 : List NodeSpec := [([0,1,2,3,28,5],[0,2],[]),([0,19,2,3,4,5],[0,1],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NB7_3Ok : checkNodesBT s2NW s2NG s2NMask s2NB7_3P s2NAutos s2NK6 7 s2NB7_3 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NB7_3Mem : ∀ ns ∈ s2NB7_3, Impossible s2NG 7 (nodeValsBT s2NW ns).toFinset := checkNodesBT_mem (by decide) s2NPairs s2NWOk (buildPoolsBT_sound s2NSlicesOk) s2NAutosOk s2NK6Ok s2NB7_3Ok
def s2NNodes7 : List NodeSpec := s2NB7_0 ++ s2NB7_1 ++ s2NB7_2 ++ s2NB7_3
def s2NK7 : BT (List (List Nat)) := buildBucketsBT s2NW s2NNodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NK7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s2NG 7 xs.toFinset) s2NK7 := buildBucketsBT_of_mem (forall_append (forall_append (forall_append s2NB7_0Mem s2NB7_1Mem) s2NB7_2Mem) s2NB7_3Mem)
def s2NB8_0S : List PoolSpec := [(12,[]),(6,[]),(1,[(2,0,1)]),(2,[(2,0,1)]),(5,[]),(10,[]),(2,[]),(11,[])]
def s2NB8_0P : BT (Option BoundPool) := buildPoolsBT 3 s2NW s2NR s2NSlices s2NB8_0S
def s2NB8_0 : List NodeSpec := [([27,0,1,2,3,4,5],[0,6,7],[0]),([24,0,1,2,3,4,5],[0,5,7],[0]),([15,0,1,2,3,4,5],[0,1,2,3,4],[0,1,4,5])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NB8_0Ok : checkNodesBT s2NW s2NG s2NMask s2NB8_0P s2NAutos s2NK7 8 s2NB8_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NB8_0Mem : ∀ ns ∈ s2NB8_0, Impossible s2NG 8 (nodeValsBT s2NW ns).toFinset := checkNodesBT_mem (by decide) s2NPairs s2NWOk (buildPoolsBT_sound s2NSlicesOk) s2NAutosOk s2NK7Ok s2NB8_0Ok
def s2NB8_1S : List PoolSpec := [(12,[]),(4,[]),(2,[(1,0,1)]),(1,[(1,0,1)]),(3,[]),(10,[]),(0,[]),(1,[]),(2,[]),(11,[]),(13,[])]
def s2NB8_1P : BT (Option BoundPool) := buildPoolsBT 4 s2NW s2NR s2NSlices s2NB8_1S
def s2NB8_1 : List NodeSpec := [([18,0,1,2,3,4,5],[0,4,5,6,7,8],[0,2,4,5]),([0,1,6,2,3,4,5],[0,1,2,3,4],[0,1]),([0,1,2,23,3,4,5],[0,5,9,10],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NB8_1Ok : checkNodesBT s2NW s2NG s2NMask s2NB8_1P s2NAutos s2NK7 8 s2NB8_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NB8_1Mem : ∀ ns ∈ s2NB8_1, Impossible s2NG 8 (nodeValsBT s2NW ns).toFinset := checkNodesBT_mem (by decide) s2NPairs s2NWOk (buildPoolsBT_sound s2NSlicesOk) s2NAutosOk s2NK7Ok s2NB8_1Ok
def s2NB8_2S : List PoolSpec := [(12,[]),(0,[]),(1,[]),(11,[]),(13,[]),(9,[]),(1,[(1,1,5)]),(2,[(1,1,5)])]
def s2NB8_2P : BT (Option BoundPool) := buildPoolsBT 3 s2NW s2NR s2NSlices s2NB8_2S
def s2NB8_2 : List NodeSpec := [([0,1,2,3,26,4,5],[0,2,3,4],[]),([0,1,2,3,35,4,5],[3,4],[]),([0,1,2,3,4,5,37],[0,1,5,6,7],[0,4,5])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NB8_2Ok : checkNodesBT s2NW s2NG s2NMask s2NB8_2P s2NAutos s2NK7 8 s2NB8_2 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NB8_2Mem : ∀ ns ∈ s2NB8_2, Impossible s2NG 8 (nodeValsBT s2NW ns).toFinset := checkNodesBT_mem (by decide) s2NPairs s2NWOk (buildPoolsBT_sound s2NSlicesOk) s2NAutosOk s2NK7Ok s2NB8_2Ok
def s2NNodes8 : List NodeSpec := s2NB8_0 ++ s2NB8_1 ++ s2NB8_2
def s2NK8 : BT (List (List Nat)) := buildBucketsBT s2NW s2NNodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NK8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s2NG 8 xs.toFinset) s2NK8 := buildBucketsBT_of_mem (forall_append (forall_append s2NB8_0Mem s2NB8_1Mem) s2NB8_2Mem)
def s2NB9_0S : List PoolSpec := [(3,[]),(0,[]),(1,[]),(2,[])]
def s2NB9_0P : BT (Option BoundPool) := buildPoolsBT 2 s2NW s2NR s2NSlices s2NB9_0S
def s2NB9_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3],[0,1,2,3,4,5,6])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NB9_0Ok : checkNodesBT s2NW s2NG s2NMask s2NB9_0P s2NAutos s2NK8 9 s2NB9_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NB9_0Mem : ∀ ns ∈ s2NB9_0, Impossible s2NG 9 (nodeValsBT s2NW ns).toFinset := checkNodesBT_mem (by decide) s2NPairs s2NWOk (buildPoolsBT_sound s2NSlicesOk) s2NAutosOk s2NK8Ok s2NB9_0Ok
def s2NNodes9 : List NodeSpec := s2NB9_0
def s2NK9 : BT (List (List Nat)) := buildBucketsBT s2NW s2NNodes9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NK9Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible s2NG 9 xs.toFinset) s2NK9 := buildBucketsBT_of_mem s2NB9_0Mem
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma s2NBound : Lower s2NR s2NG 10 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 3,4,12),(VAR 4,4,20),(VAR 5,1,33)]) (by decide +kernel) s2NK9Ok (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q34 : Lower (varsOf 63) 0xfffeffeefefaeca0fffeffeefefaeca0 10 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (1, 2)]) (roots2 := s2NR) (T2 := s2NG) _ s2NBound
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q42 : Lower (varsOf 126) 0xfffffffffffffcf0fffcffccfcf0cc00 10 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (5, 6), (0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (2, 3), (3, 4), (2, 3), (1, 2), (0, 1)]) (roots2 := s2NR) (T2 := s2NG) _ s2NBound
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q43d : Lower (varsOf 87) 0xc8c88080c8c880808080000080800000 8 := by
  apply carry_of (swaps := [(4, 5), (5, 6), (2, 3), (3, 4), (1, 2)]) (roots2 := d14) (T2 := d3) _ d76
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q43 : Lower (varsOf 87) 0xfffffefefffffefefefeececfefeecec 8 := dualLower (by decide +kernel) (by decide +kernel) q43d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q44d : Lower (varsOf 107) 0xffccffcc88008800aa88aa8800000000 8 := by
  apply carry_of (swaps := [(5, 6), (3, 4), (4, 5), (2, 3), (0, 1), (1, 2), (0, 1)]) (roots2 := d13) (T2 := d147) _ d220
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q44 : Lower (varsOf 107) 0xffffffffeeaaeeaaffeeffeecc00cc00 8 := dualLower (by decide +kernel) (by decide +kernel) q44d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q45 : Lower (varsOf 117) 0xfffffffffffffafafafaaaaafafaa0a0 8 := by
  apply carry_of (swaps := [(1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (4, 5), (3, 4)]) (roots2 := d606) (T2 := d605) _ d604
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q46d : Lower (varsOf 47) 0xfac8fac888008800fac8fac888008800 7 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (0, 1), (1, 2), (2, 3), (3, 4), (1, 2), (2, 3), (0, 1)]) (roots2 := d13) (T2 := d255) _ d339
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q46 : Lower (varsOf 47) 0xffeeffeeeca0eca0ffeeffeeeca0eca0 7 := dualLower (by decide +kernel) (by decide +kernel) q46d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q47d : Lower (varsOf 55) 0xfafaa0a088888080fafaa0a088888080 7 := by
  apply carry_of (swaps := [(4, 5), (2, 3), (3, 4), (0, 1), (1, 2), (2, 3), (0, 1), (1, 2)]) (roots2 := d13) (T2 := d255) _ d339
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q47 : Lower (varsOf 55) 0xfefeeeeefafaa0a0fefeeeeefafaa0a0 7 := dualLower (by decide +kernel) (by decide +kernel) q47d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q48 : Lower (varsOf 103) 0xfffffffffafafafaeeeeeeeea0a0a0a0 7 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (5, 6), (0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (2, 3), (1, 2)]) (roots2 := d383) (T2 := d371) _ d433
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q49d : Lower (varsOf 59) 0xffccaa8888008800ffccaa8888008800 7 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (2, 3), (0, 1), (1, 2), (0, 1)]) (roots2 := d13) (T2 := d255) _ d339
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q49 : Lower (varsOf 59) 0xffeeffeeeeaacc00ffeeffeeeeaacc00 7 := dualLower (by decide +kernel) (by decide +kernel) q49d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q50 : Lower (varsOf 115) 0xffffffffffffaaaaeeeeeeeeaaaa0000 7 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (5, 6), (0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (1, 2), (2, 3), (3, 4), (1, 2)]) (roots2 := d383) (T2 := d371) _ d433
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q51d : Lower (varsOf 61) 0xfafaa0a0aa00a000fafaa0a0aa00a000 7 := by
  apply carry_of (swaps := [(4, 5), (2, 3), (3, 4), (1, 2), (0, 1)]) (roots2 := d13) (T2 := d255) _ d339
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q51 : Lower (varsOf 61) 0xfffaffaafafaa0a0fffaffaafafaa0a0 7 := dualLower (by decide +kernel) (by decide +kernel) q51d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q52 : Lower (varsOf 109) 0xfffffffffafafafaffaaffaaa0a0a0a0 7 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (5, 6), (0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (1, 2)]) (roots2 := d383) (T2 := d371) _ d433
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q53 : Lower (varsOf 121) 0xffffffffffffaaaaffaaffaaaaaa0000 7 := by
  apply carry_of (swaps := [(2, 3), (3, 4), (4, 5), (5, 6), (0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (1, 2), (2, 3), (3, 4), (2, 3)]) (roots2 := d383) (T2 := d371) _ d433
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q54d : Lower (varsOf 110) 0xffccffcccc00cc00f0c0f0c000000000 7 := by
  apply carry_of (swaps := [(4, 5), (5, 6), (3, 4), (4, 5), (2, 3)]) (roots2 := d13) (T2 := d255) _ d339
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q54 : Lower (varsOf 110) 0xfffffffffcf0fcf0ffccffcccc00cc00 7 := dualLower (by decide +kernel) (by decide +kernel) q54d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q55d : Lower (varsOf 118) 0xfffff0f0ccccc0c0f0f0000000000000 7 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (5, 6), (3, 4), (4, 5), (2, 3), (3, 4), (1, 2)]) (roots2 := d13) (T2 := d255) _ d339
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q55 : Lower (varsOf 118) 0xfffffffffffff0f0fcfcccccf0f00000 7 := dualLower (by decide +kernel) (by decide +kernel) q55d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q56d : Lower (varsOf 122) 0xffccffcccc00cc00ffcc000000000000 7 := by
  apply carry_of (swaps := [(4, 5), (5, 6), (3, 4), (4, 5), (3, 4), (2, 3)]) (roots2 := d13) (T2 := d255) _ d339
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q56 : Lower (varsOf 122) 0xffffffffffffcc00ffccffcccc00cc00 7 := dualLower (by decide +kernel) (by decide +kernel) q56d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q57d : Lower (varsOf 124) 0xfffff0f0ff00f000f0f0000000000000 7 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (5, 6), (3, 4), (4, 5), (2, 3), (3, 4), (2, 3), (1, 2)]) (roots2 := d13) (T2 := d255) _ d339
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q57 : Lower (varsOf 124) 0xfffffffffffff0f0fff0ff00f0f00000 7 := dualLower (by decide +kernel) (by decide +kernel) q57d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q58d : Lower (varsOf 85) 0xfafaa0a0fafaa0a0a0a00000a0a00000 7 := by
  apply carry_of (swaps := [(5, 6), (1, 2), (2, 3), (0, 1)]) (roots2 := d160) (T2 := d609) _ d668
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q58 : Lower (varsOf 85) 0xfffffafafffffafafafaa0a0fafaa0a0 7 := dualLower (by decide +kernel) (by decide +kernel) q58d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q59 : Lower (varsOf 79) 0xfefafefafefafefaeca0eca0eca0eca0 6 := by
  apply carry_of (swaps := [(4, 5), (5, 6), (3, 4), (0, 1)]) (roots2 := d489) (T2 := d488) _ d487
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q60d : Lower (varsOf 103) 0xc8c8c8c8000000008080808000000000 6 := by
  apply carry_of (swaps := [(5, 6), (4, 5), (0, 1), (1, 2), (2, 3), (1, 2)]) (roots2 := d13) (T2 := d113) _ d138
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q60 : Lower (varsOf 103) 0xfffffffffefefefeffffffffecececec 6 := dualLower (by decide +kernel) (by decide +kernel) q60d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q61 : Lower (varsOf 94) 0xfffffcf0fffffcf0fcf0cc00fcf0cc00 6 := by
  apply carry_of (swaps := [(4, 5), (5, 6), (2, 3), (3, 4), (1, 2), (0, 1)]) (roots2 := d489) (T2 := d488) _ d487
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q62d : Lower (varsOf 118) 0xccccc0c000000000c0c0000000000000 6 := by
  apply carry_of (swaps := [(5, 6), (4, 5), (2, 3), (3, 4), (1, 2)]) (roots2 := d13) (T2 := d113) _ d138
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q62 : Lower (varsOf 118) 0xfffffffffffffcfcfffffffffcfccccc 6 := dualLower (by decide +kernel) (by decide +kernel) q62d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q63d : Lower (varsOf 43) 0xaa88aa8888008800aa88aa8888008800 5 := by
  apply carry_of (swaps := [(4, 5), (2, 3), (0, 1), (1, 2), (0, 1)]) (roots2 := d156) (T2 := d490) _ d513
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q63 : Lower (varsOf 43) 0xffeeffeeeeaaeeaaffeeffeeeeaaeeaa 5 := dualLower (by decide +kernel) (by decide +kernel) q63d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q64d : Lower (varsOf 77) 0xfa00fa00fa00fa00a000a000a000a000 5 := by
  apply carry_of (swaps := [(4, 5), (5, 6), (0, 1)]) (roots2 := d156) (T2 := d490) _ d513
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q64 : Lower (varsOf 77) 0xfffafffafffafffaffa0ffa0ffa0ffa0 5 := dualLower (by decide +kernel) (by decide +kernel) q64d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q65d : Lower (varsOf 53) 0xfafaa0a0aaaaa0a0fafaa0a0aaaaa0a0 5 := by
  apply carry_of (swaps := [(0, 1), (1, 2)]) (roots2 := d691) (T2 := d688) _ d709
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q65 : Lower (varsOf 53) 0xfafaaaaafafaa0a0fafaaaaafafaa0a0 5 := dualLower (by decide +kernel) (by decide +kernel) q65d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q66d : Lower (varsOf 86) 0xccccc0c0ccccc0c0c0c00000c0c00000 5 := by
  apply carry_of (swaps := [(4, 5), (5, 6), (2, 3), (3, 4), (1, 2)]) (roots2 := d156) (T2 := d490) _ d513
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q66 : Lower (varsOf 86) 0xfffffcfcfffffcfcfcfcccccfcfccccc 5 := dualLower (by decide +kernel) (by decide +kernel) q66d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q67d : Lower (varsOf 106) 0xffccffcccc00cc000000000000000000 5 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (5, 6), (3, 4), (4, 5), (2, 3)]) (roots2 := d156) (T2 := d490) _ d513
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q67 : Lower (varsOf 106) 0xffffffffffffffffffccffcccc00cc00 5 := dualLower (by decide +kernel) (by decide +kernel) q67d
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q68 : Lower (varsOf 39) 0xeeeeeeeea0a0a0a0eeeeeeeea0a0a0a0 4 := by
  apply carry_of (swaps := [(4, 5), (1, 2), (2, 3), (3, 4), (0, 1), (1, 2), (2, 3), (0, 1)]) (roots2 := d160) (T2 := d253) _ d336
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q69 : Lower (varsOf 51) 0xeeeeeeeeaaaa0000eeeeeeeeaaaa0000 4 := by
  apply carry_of (swaps := [(4, 5), (1, 2), (2, 3), (0, 1), (1, 2), (0, 1)]) (roots2 := d160) (T2 := d253) _ d336
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q70 : Lower (varsOf 102) 0xfffffffff0f0f0f0cccccccc00000000 4 := by
  apply carry_of (swaps := [(4, 5), (5, 6), (3, 4), (4, 5), (1, 2), (2, 3), (1, 2)]) (roots2 := d160) (T2 := d253) _ d336
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q71 : Lower (varsOf 114) 0xffffffffffff0000cccccccc00000000 4 := by
  apply carry_of (swaps := [(4, 5), (5, 6), (3, 4), (4, 5), (2, 3), (3, 4), (1, 2)]) (roots2 := d160) (T2 := d253) _ d336
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q72 : Lower (varsOf 21) 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0 4 := by
  apply carry_of (swaps := [(3, 4), (0, 1)]) (roots2 := d159) (T2 := d148) _ d331
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q73 : Lower (varsOf 69) 0xfafafafafafafafaa0a0a0a0a0a0a0a0 4 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (5, 6), (0, 1)]) (roots2 := d159) (T2 := d148) _ d331
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q74 : Lower (varsOf 81) 0xffffaaaaffffaaaaaaaa0000aaaa0000 4 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (5, 6), (2, 3), (3, 4), (0, 1)]) (roots2 := d159) (T2 := d148) _ d331
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q75 : Lower (varsOf 97) 0xffffffffaaaaaaaaaaaaaaaa00000000 4 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (5, 6), (2, 3), (3, 4), (4, 5), (0, 1)]) (roots2 := d159) (T2 := d148) _ d331
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q76 : Lower (varsOf 42) 0xffccffcccc00cc00ffccffcccc00cc00 4 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (2, 3)]) (roots2 := d159) (T2 := d148) _ d331
  decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma q77 : Lower (varsOf 84) 0xfffff0f0fffff0f0f0f00000f0f00000 4 := by
  apply carry_of (swaps := [(3, 4), (4, 5), (5, 6), (2, 3), (3, 4), (1, 2)]) (roots2 := d159) (T2 := d148) _ d331
  decide +kernel
def rR : List Nat := varsOf 127
def rG : Nat := 0xfffffffffffffefafffeffeefefaeca0
def rPos : List Nat := [5,5,5,5,5,5,5,7,7,10,10,11,11,13,13,14,14,17,17,17,17,17,19,19,20,20,20,20,20,21,21,22,22,25,25,26,26,28,28,33,33,33,33,33,33,33,34,34,34,34,34,34,34,35,35,37,37,37,38,38,38,40,40,40,41,41,44,49,49,49,50,50,52,52,52,56,65,65,65,65,67,67,67,68,68,68,68,69,69,69,70,70,73,73,73,74,74,76,76,80,80,80,81,81,81,82,82,88,88,96,96,96,96,96,97,97,97,98,98,100,100,100,104,104,112,112]
def rNeg : List Nat := [0,1,3,4,6,36,64,3,6,2,8,3,9,9,12,6,12,0,1,3,16,48,3,18,0,4,16,36,48,1,16,6,18,9,24,18,24,12,24,0,1,3,32,36,48,64,0,2,3,6,18,32,66,2,3,4,32,36,2,6,36,8,9,32,8,9,12,1,16,48,18,48,4,36,48,24,0,1,32,64,2,3,66,0,4,36,64,4,36,64,6,66,8,9,72,66,72,12,72,16,48,64,1,16,48,18,66,24,72,0,32,36,48,64,0,1,64,2,66,4,36,64,8,72,16,48]
def rMask : Nat := fullMask 126
def rBase : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x1c01c07387f03b03e03f8660fe79ff,0x800402002200a40410302204c3886),(0xcccccccccccccccccccccccccccccccc,0x6006018c0700c01c7fc01980c19f80,0x6006008c0700400c77820980c88b94),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x38000060ff807041f800061ff01e1ff,0x180800205b003041a8208208a01c138),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xc001807f0000807e000007e0001fe00,0xc001807700008076000007600017400),(0xffff0000ffff0000ffff0000ffff0000,0x30001ff800000ff80000007ffffe0000,0x30010b9800000cf00004105d54b00000),(0xffffffff00000000ffffffff00000000,0x3fffe00000000fffffffff8000000000,0x2101c110012046a093081c0018200020),(0xffffffffffffffff0000000000000000,0x3ffffffffffff0000000000000000000,0xa521425ca4480000010200000000040)]
def rSteps : List (Nat × Nat × Nat) := [(1,0,1),(2,7,2),(1,8,4),(1,8,6),(2,7,4),(2,7,6),(1,12,2),(1,12,4),(1,2,4),(1,2,6),(1,4,6),(1,15,6),(3,0,18),(3,4,16),(1,0,2),(1,0,4),(1,1,3),(1,21,6),(2,21,6),(1,22,6),(2,22,6),(1,1,5),(0,3,28),(3,3,28),(3,1,5),(1,31,6),(1,1,6),(1,3,5),(3,3,5),(1,3,6),(1,15,5),(1,5,6),(2,5,6),(1,2,5),(1,4,5),(1,0,6),(1,21,4),(2,21,4),(3,4,42),(3,2,42),(1,2,32),(1,31,42),(1,46,31),(1,1,42),(1,40,6),(0,40,42),(1,4,52),(1,21,5),(2,21,5),(1,3,42),(1,5,42),(2,5,42),(3,5,16),(1,46,5),(2,60,6),(3,6,57),(1,58,6),(1,1,21),(1,43,6),(3,2,65),(3,4,65),(2,43,6),(1,44,6),(0,4,24),(1,25,4),(3,21,17),(1,1,4),(1,29,70),(1,31,2),(1,31,21),(1,21,32),(3,4,77),(3,6,77),(2,21,32),(1,80,6),(3,0,40),(3,4,5),(3,4,40),(2,40,6),(1,21,3),(1,43,5),(2,87,6),(2,43,5),(1,44,5),(3,2,54),(3,21,5),(1,92,0),(1,92,2),(1,92,4),(3,4,54),(2,54,6),(1,54,6),(3,4,98),(1,55,4),(1,55,6),(3,5,24),(1,25,5),(1,3,4),(3,21,41),(1,83,2),(1,83,21),(2,21,38),(3,21,38),(1,39,2),(1,39,21),(1,0,3),(1,0,5),(3,2,5),(1,114,4),(1,114,6),(1,4,113),(3,4,113),(3,2,38),(1,4,38),(3,4,38),(3,5,42),(0,5,42),(1,2,123),(1,4,123),(3,123,113),(1,62,2),(1,62,4),(3,0,37),(3,15,113),(3,0,38),(1,82,6),(3,0,41),(1,91,4),(1,91,6),(2,91,6),(1,39,4),(3,39,113),(3,2,57),(1,4,57),(3,4,57),(3,0,98),(0,4,98),(2,62,4),(3,0,5),(1,94,4),(2,94,4),(1,94,6),(2,94,6),(1,145,4),(3,2,63),(1,4,63),(3,4,63),(1,1,2),(3,15,42),(1,46,4),(1,31,0),(1,157,4),(3,0,77),(3,2,48),(1,4,48),(3,4,48),(3,31,42),(1,155,31),(3,1,42),(1,165,3),(1,2,3),(1,155,5),(2,40,42),(3,40,42),(1,114,42),(3,114,42),(3,0,60),(3,46,57),(1,58,46),(1,46,1),(1,46,3),(3,46,5),(3,3,42),(1,1,123),(1,3,123),(3,123,57),(1,58,0),(1,122,2),(2,184,4),(1,122,4),(2,122,4),(3,0,154),(1,188,4),(1,188,6),(2,154,4),(1,191,0),(1,191,6),(2,154,6),(1,76,4),(3,0,195),(2,195,6),(2,76,4),(2,157,2),(2,157,4),(2,157,6),(3,0,75),(1,75,4),(2,75,4),(2,75,6),(1,31,4),(3,2,37),(1,37,6),(2,37,6),(1,82,4),(2,82,4),(2,41,6),(1,83,0),(1,83,6),(1,84,0),(1,84,6),(2,84,6),(1,93,4),(2,93,4),(2,93,6),(3,0,115),(1,115,6),(2,115,6)]
def rW : BT Decor := buildWiresBT 8 rBase rSteps
def rAutoList : List (List (Nat × Nat)) := [[],[(2,4)],[(1,3)],[(1,3),(2,4)],[(0,6)],[(0,6),(2,4)],[(0,6),(1,3)],[(0,6),(1,3),(2,4)]]
def rAutos : BT (List (Nat × Nat)) := btOfList 3 rAutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rPairs : goodPairs rG rPos rNeg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rBaseOk : ∀ x ∈ rBase, faithful rPos rNeg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rWOk : btAll (fun x => faithful rPos rNeg x ∧ x.1 < 2^128) rW := buildWiresBT_faithful rBaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rAutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw rG = rG) rAutos := btAll_ofList (autos_of (by decide +kernel))
def rSliceList : List (Option (Nat × Nat)) := [some (subcubeFast 32 0,9),some (subcubeFast 16 0,10),some (subcubeFast 0 8,9),some (subcubeFast 8 0,10),some (subcubeFast 4 0,10),some (subcubeFast 0 2,9),some (subcubeFast 2 0,10),some (subcubeFast 64 0,10),some (subcubeFast 1 0,10),some (subcubeFast 32 8,8),some (subcubeFast 20 0,8),some (subcubeFast 32 2,8),some (subcubeFast 10 0,8),some (subcubeFast 80 0,7),some (subcubeFast 72 0,7),some (subcubeFast 24 0,7),some (subcubeFast 68 0,7),some (subcubeFast 12 0,7),some (subcubeFast 66 0,7),some (subcubeFast 18 0,7),some (subcubeFast 6 0,7),some (subcubeFast 17 0,7),some (subcubeFast 9 0,7),some (subcubeFast 5 0,7),some (subcubeFast 3 0,7),some (subcubeFast 34 8,7),some (subcubeFast 40 2,7),some (subcubeFast 48 0,6),some (subcubeFast 16 8,6),some (subcubeFast 33 0,6),some (subcubeFast 1 8,6),some (subcubeFast 80 4,5),some (subcubeFast 48 2,5),some (subcubeFast 74 0,5),some (subcubeFast 33 8,5),some (subcubeFast 17 4,5),some (subcubeFast 88 0,4),some (subcubeFast 76 0,4),some (subcubeFast 25 0,4),some (subcubeFast 13 0,4),some (subcubeFast 104 2,4),some (subcubeFast 50 8,4),some (subcubeFast 38 8,4),some (subcubeFast 44 2,4),some (subcubeFast 30 0,4),some (subcubeFast 69 16,4),some (subcubeFast 81 4,4),some (subcubeFast 85 0,4),some (subcubeFast 35 8,4),some (subcubeFast 41 2,4)]
def rSlices : BT (Option (Nat × Nat)) := btOfList 6 rSliceList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rSlice0 : Slice rR rG (subcubeFast 32 0) 9 := slice_fast_direct (zDead := 0) (qRoots := varsOf 95) (qGoal := 0xfffffefafffffefafefaeca0fefaeca0) (by decide +kernel) q0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rSlice1 : Slice rR rG (subcubeFast 16 0) 10 := slice_fast_direct (zDead := 0) (qRoots := varsOf 111) (qGoal := 0xfffffffffefafefaffeeffeeeca0eca0) (by decide +kernel) q2
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rSlice2 : Slice rR rG (subcubeFast 0 8) 9 := slice_fast_direct (zDead := 0) (qRoots := varsOf 119) (qGoal := 0xfffffffffffffefefffffffffefeecec) (by decide +kernel) q15
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rSlice3 : Slice rR rG (subcubeFast 8 0) 10 := slice_fast_direct (zDead := 0) (qRoots := varsOf 119) (qGoal := 0xfffffffffffffafafefeeeeefafaa0a0) (by decide +kernel) q17
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rSlice4 : Slice rR rG (subcubeFast 4 0) 10 := slice_fast_direct (zDead := 0) (qRoots := varsOf 123) (qGoal := 0xffffffffffffeeaaffeeffeeeeaacc00) (by decide +kernel) q31
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rSlice5 : Slice rR rG (subcubeFast 0 2) 9 := slice_fast_direct (zDead := 0) (qRoots := varsOf 125) (qGoal := 0xfffffffffffffffafffffffffffaffa0) (by decide +kernel) q32
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rSlice6 : Slice rR rG (subcubeFast 2 0) 10 := slice_fast_direct (zDead := 0) (qRoots := varsOf 125) (qGoal := 0xfffffffffffffafafffaffaafafaa0a0) (by decide +kernel) q33
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rSlice7 : Slice rR rG (subcubeFast 64 0) 10 := slice_fast_direct (zDead := 0) (qRoots := varsOf 63) (qGoal := 0xfffeffeefefaeca0fffeffeefefaeca0) (by decide +kernel) q34
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rSlice8 : Slice rR rG (subcubeFast 1 0) 10 := slice_fast_direct (zDead := 0) (qRoots := varsOf 126) (qGoal := 0xfffffffffffffcf0fffcffccfcf0cc00) (by decide +kernel) q42
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rSlice9 : Slice rR rG (subcubeFast 32 8) 8 := slice_fast_direct (zDead := 0) (qRoots := varsOf 87) (qGoal := 0xfffffefefffffefefefeececfefeecec) (by decide +kernel) q43
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rSlice10 : Slice rR rG (subcubeFast 20 0) 8 := slice_fast_direct (zDead := 0) (qRoots := varsOf 107) (qGoal := 0xffffffffeeaaeeaaffeeffeecc00cc00) (by decide +kernel) q44
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rSlice11 : Slice rR rG (subcubeFast 32 2) 8 := slice_fast_direct (zDead := 0) (qRoots := varsOf 93) (qGoal := 0xfffffffafffffffafffaffa0fffaffa0) (by decide +kernel) q1
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rSlice12 : Slice rR rG (subcubeFast 10 0) 8 := slice_fast_direct (zDead := 0) (qRoots := varsOf 117) (qGoal := 0xfffffffffffffafafafaaaaafafaa0a0) (by decide +kernel) q45
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rSlice13 : Slice rR rG (subcubeFast 80 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 47) (qGoal := 0xffeeffeeeca0eca0ffeeffeeeca0eca0) (by decide +kernel) q46
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rSlice14 : Slice rR rG (subcubeFast 72 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 55) (qGoal := 0xfefeeeeefafaa0a0fefeeeeefafaa0a0) (by decide +kernel) q47
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rSlice15 : Slice rR rG (subcubeFast 24 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 103) (qGoal := 0xfffffffffafafafaeeeeeeeea0a0a0a0) (by decide +kernel) q48
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rSlice16 : Slice rR rG (subcubeFast 68 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 59) (qGoal := 0xffeeffeeeeaacc00ffeeffeeeeaacc00) (by decide +kernel) q49
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rSlice17 : Slice rR rG (subcubeFast 12 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 115) (qGoal := 0xffffffffffffaaaaeeeeeeeeaaaa0000) (by decide +kernel) q50
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rSlice18 : Slice rR rG (subcubeFast 66 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 61) (qGoal := 0xfffaffaafafaa0a0fffaffaafafaa0a0) (by decide +kernel) q51
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rSlice19 : Slice rR rG (subcubeFast 18 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 109) (qGoal := 0xfffffffffafafafaffaaffaaa0a0a0a0) (by decide +kernel) q52
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rSlice20 : Slice rR rG (subcubeFast 6 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 121) (qGoal := 0xffffffffffffaaaaffaaffaaaaaa0000) (by decide +kernel) q53
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rSlice21 : Slice rR rG (subcubeFast 17 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 110) (qGoal := 0xfffffffffcf0fcf0ffccffcccc00cc00) (by decide +kernel) q54
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rSlice22 : Slice rR rG (subcubeFast 9 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 118) (qGoal := 0xfffffffffffff0f0fcfcccccf0f00000) (by decide +kernel) q55
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rSlice23 : Slice rR rG (subcubeFast 5 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 122) (qGoal := 0xffffffffffffcc00ffccffcccc00cc00) (by decide +kernel) q56
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rSlice24 : Slice rR rG (subcubeFast 3 0) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 124) (qGoal := 0xfffffffffffff0f0fff0ff00f0f00000) (by decide +kernel) q57
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rSlice25 : Slice rR rG (subcubeFast 34 8) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 85) (qGoal := 0xfffffafafffffafafafaa0a0fafaa0a0) (by decide +kernel) q58
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rSlice26 : Slice rR rG (subcubeFast 40 2) 7 := slice_fast_direct (zDead := 0) (qRoots := varsOf 85) (qGoal := 0xfffffafafffffafafafaa0a0fafaa0a0) (by decide +kernel) q58
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rSlice27 : Slice rR rG (subcubeFast 48 0) 6 := slice_fast_direct (zDead := 0) (qRoots := varsOf 79) (qGoal := 0xfefafefafefafefaeca0eca0eca0eca0) (by decide +kernel) q59
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rSlice28 : Slice rR rG (subcubeFast 16 8) 6 := slice_fast_direct (zDead := 0) (qRoots := varsOf 103) (qGoal := 0xfffffffffefefefeffffffffecececec) (by decide +kernel) q60
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rSlice29 : Slice rR rG (subcubeFast 33 0) 6 := slice_fast_direct (zDead := 0) (qRoots := varsOf 94) (qGoal := 0xfffffcf0fffffcf0fcf0cc00fcf0cc00) (by decide +kernel) q61
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rSlice30 : Slice rR rG (subcubeFast 1 8) 6 := slice_fast_direct (zDead := 0) (qRoots := varsOf 118) (qGoal := 0xfffffffffffffcfcfffffffffcfccccc) (by decide +kernel) q62
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rSlice31 : Slice rR rG (subcubeFast 80 4) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 43) (qGoal := 0xffeeffeeeeaaeeaaffeeffeeeeaaeeaa) (by decide +kernel) q63
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rSlice32 : Slice rR rG (subcubeFast 48 2) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 77) (qGoal := 0xfffafffafffafffaffa0ffa0ffa0ffa0) (by decide +kernel) q64
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rSlice33 : Slice rR rG (subcubeFast 74 0) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 53) (qGoal := 0xfafaaaaafafaa0a0fafaaaaafafaa0a0) (by decide +kernel) q65
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rSlice34 : Slice rR rG (subcubeFast 33 8) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 86) (qGoal := 0xfffffcfcfffffcfcfcfcccccfcfccccc) (by decide +kernel) q66
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rSlice35 : Slice rR rG (subcubeFast 17 4) 5 := slice_fast_direct (zDead := 0) (qRoots := varsOf 106) (qGoal := 0xffffffffffffffffffccffcccc00cc00) (by decide +kernel) q67
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rSlice36 : Slice rR rG (subcubeFast 88 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 39) (qGoal := 0xeeeeeeeea0a0a0a0eeeeeeeea0a0a0a0) (by decide +kernel) q68
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rSlice37 : Slice rR rG (subcubeFast 76 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 51) (qGoal := 0xeeeeeeeeaaaa0000eeeeeeeeaaaa0000) (by decide +kernel) q69
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rSlice38 : Slice rR rG (subcubeFast 25 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 102) (qGoal := 0xfffffffff0f0f0f0cccccccc00000000) (by decide +kernel) q70
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rSlice39 : Slice rR rG (subcubeFast 13 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 114) (qGoal := 0xffffffffffff0000cccccccc00000000) (by decide +kernel) q71
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rSlice40 : Slice rR rG (subcubeFast 104 2) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 21) (qGoal := 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0) (by decide +kernel) q72
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rSlice41 : Slice rR rG (subcubeFast 50 8) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 69) (qGoal := 0xfafafafafafafafaa0a0a0a0a0a0a0a0) (by decide +kernel) q73
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rSlice42 : Slice rR rG (subcubeFast 38 8) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 81) (qGoal := 0xffffaaaaffffaaaaaaaa0000aaaa0000) (by decide +kernel) q74
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rSlice43 : Slice rR rG (subcubeFast 44 2) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 81) (qGoal := 0xffffaaaaffffaaaaaaaa0000aaaa0000) (by decide +kernel) q74
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rSlice44 : Slice rR rG (subcubeFast 30 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 97) (qGoal := 0xffffffffaaaaaaaaaaaaaaaa00000000) (by decide +kernel) q75
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rSlice45 : Slice rR rG (subcubeFast 69 16) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 42) (qGoal := 0xffccffcccc00cc00ffccffcccc00cc00) (by decide +kernel) q76
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rSlice46 : Slice rR rG (subcubeFast 81 4) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 42) (qGoal := 0xffccffcccc00cc00ffccffcccc00cc00) (by decide +kernel) q76
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rSlice47 : Slice rR rG (subcubeFast 85 0) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 42) (qGoal := 0xffccffcccc00cc00ffccffcccc00cc00) (by decide +kernel) q76
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rSlice48 : Slice rR rG (subcubeFast 35 8) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 84) (qGoal := 0xfffff0f0fffff0f0f0f00000f0f00000) (by decide +kernel) q77
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rSlice49 : Slice rR rG (subcubeFast 41 2) 4 := slice_fast_direct (zDead := 0) (qRoots := varsOf 84) (qGoal := 0xfffff0f0fffff0f0f0f00000f0f00000) (by decide +kernel) q77
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rSlicesOk : btAll (fun o => ∀ p, o = some p → Slice rR rG p.1 p.2) rSlices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice rR rG p.1 p.2) (forall_cons (fun _ h => by cases h; exact rSlice0) (forall_cons (fun _ h => by cases h; exact rSlice1) (forall_cons (fun _ h => by cases h; exact rSlice2) (forall_cons (fun _ h => by cases h; exact rSlice3) (forall_cons (fun _ h => by cases h; exact rSlice4) (forall_cons (fun _ h => by cases h; exact rSlice5) (forall_cons (fun _ h => by cases h; exact rSlice6) (forall_cons (fun _ h => by cases h; exact rSlice7) (forall_cons (fun _ h => by cases h; exact rSlice8) (forall_cons (fun _ h => by cases h; exact rSlice9) (forall_cons (fun _ h => by cases h; exact rSlice10) (forall_cons (fun _ h => by cases h; exact rSlice11) (forall_cons (fun _ h => by cases h; exact rSlice12) (forall_cons (fun _ h => by cases h; exact rSlice13) (forall_cons (fun _ h => by cases h; exact rSlice14) (forall_cons (fun _ h => by cases h; exact rSlice15) (forall_cons (fun _ h => by cases h; exact rSlice16) (forall_cons (fun _ h => by cases h; exact rSlice17) (forall_cons (fun _ h => by cases h; exact rSlice18) (forall_cons (fun _ h => by cases h; exact rSlice19) (forall_cons (fun _ h => by cases h; exact rSlice20) (forall_cons (fun _ h => by cases h; exact rSlice21) (forall_cons (fun _ h => by cases h; exact rSlice22) (forall_cons (fun _ h => by cases h; exact rSlice23) (forall_cons (fun _ h => by cases h; exact rSlice24) (forall_cons (fun _ h => by cases h; exact rSlice25) (forall_cons (fun _ h => by cases h; exact rSlice26) (forall_cons (fun _ h => by cases h; exact rSlice27) (forall_cons (fun _ h => by cases h; exact rSlice28) (forall_cons (fun _ h => by cases h; exact rSlice29) (forall_cons (fun _ h => by cases h; exact rSlice30) (forall_cons (fun _ h => by cases h; exact rSlice31) (forall_cons (fun _ h => by cases h; exact rSlice32) (forall_cons (fun _ h => by cases h; exact rSlice33) (forall_cons (fun _ h => by cases h; exact rSlice34) (forall_cons (fun _ h => by cases h; exact rSlice35) (forall_cons (fun _ h => by cases h; exact rSlice36) (forall_cons (fun _ h => by cases h; exact rSlice37) (forall_cons (fun _ h => by cases h; exact rSlice38) (forall_cons (fun _ h => by cases h; exact rSlice39) (forall_cons (fun _ h => by cases h; exact rSlice40) (forall_cons (fun _ h => by cases h; exact rSlice41) (forall_cons (fun _ h => by cases h; exact rSlice42) (forall_cons (fun _ h => by cases h; exact rSlice43) (forall_cons (fun _ h => by cases h; exact rSlice44) (forall_cons (fun _ h => by cases h; exact rSlice45) (forall_cons (fun _ h => by cases h; exact rSlice46) (forall_cons (fun _ h => by cases h; exact rSlice47) (forall_cons (fun _ h => by cases h; exact rSlice48) (forall_cons (fun _ h => by cases h; exact rSlice49) (fun _ h => (List.not_mem_nil h).elim)))))))))))))))))))))))))))))))))))))))))))))))))))
def rEmpty : BT (List (List Nat)) := BT.empty
lemma rEmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible rG (5 - 1) xs.toFinset) rEmpty := trivial
def rB5_0S : List PoolSpec := []
def rB5_0P : BT (Option BoundPool) := buildPoolsBT 1 rW rR rSlices rB5_0S
def rB5_0 : List NodeSpec := [([46,0,1,74,5,6],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB5_0Ok : checkNodesBT rW rG rMask rB5_0P rAutos rEmpty 5 rB5_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB5_0Mem : ∀ ns ∈ rB5_0, Impossible rG 5 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rEmptyOk rB5_0Ok
def rNodes5 : List NodeSpec := rB5_0
def rK5 : BT (List (List Nat)) := buildBucketsBT rW rNodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rK5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible rG 5 xs.toFinset) rK5 := buildBucketsBT_of_mem rB5_0Mem
def rB6_0S : List PoolSpec := [(44,[]),(30,[]),(23,[(1,1,5),(3,3,28)])]
def rB6_0P : BT (Option BoundPool) := buildPoolsBT 2 rW rR rSlices rB6_0S
def rB6_0 : List NodeSpec := [([25,30,1,22,15,5,6],[],[]),([25,1,29,22,15,5,6],[],[]),([44,30,1,4,5,42,16],[],[]),([44,1,29,4,5,42,16],[],[]),([45,30,1,21,4,5,16],[],[]),([45,1,21,29,4,5,16],[],[]),([30,46,0,1,70,5,6],[],[]),([30,66,0,1,4,5,6],[],[]),([30,1,21,4,5,42,18],[1],[]),([30,1,21,4,5,16,26],[],[]),([30,1,21,22,5,6,18],[],[]),([30,1,21,22,5,16,17],[],[]),([30,1,21,15,5,42,17],[2],[]),([30,1,22,15,5,6,24],[0],[]),([46,0,1,29,70,5,6],[],[0]),([66,0,1,29,4,5,6],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB6_0Ok : checkNodesBT rW rG rMask rB6_0P rAutos rK5 6 rB6_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB6_0Mem : ∀ ns ∈ rB6_0, Impossible rG 6 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK5Ok rB6_0Ok
def rB6_1S : List PoolSpec := [(44,[]),(22,[]),(36,[])]
def rB6_1P : BT (Option BoundPool) := buildPoolsBT 2 rW rR rSlices rB6_1S
def rB6_1 : List NodeSpec := [([49,0,1,3,70,5,6],[],[]),([0,1,2,74,5,6,24],[],[0]),([1,21,29,4,5,42,18],[1],[]),([1,21,29,4,5,16,26],[],[]),([1,21,29,22,5,6,18],[],[]),([1,21,29,22,5,16,17],[],[]),([1,21,29,15,5,42,17],[2],[]),([1,29,22,15,5,6,24],[0],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB6_1Ok : checkNodesBT rW rG rMask rB6_1P rAutos rK5 6 rB6_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB6_1Mem : ∀ ns ∈ rB6_1, Impossible rG 6 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK5Ok rB6_1Ok
def rNodes6 : List NodeSpec := rB6_0 ++ rB6_1
def rK6 : BT (List (List Nat)) := buildBucketsBT rW rNodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rK6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible rG 6 xs.toFinset) rK6 := buildBucketsBT_of_mem (forall_append rB6_0Mem rB6_1Mem)
def rB7_0S : List PoolSpec := [(31,[]),(13,[]),(45,[]),(47,[]),(6,[]),(3,[(1,0,2),(1,0,4),(1,2,4),(2,21,6)]),(44,[]),(36,[]),(5,[(1,0,2),(1,21,4),(2,43,6)])]
def rB7_0P : BT (Option BoundPool) := buildPoolsBT 4 rW rR rSlices rB7_0S
def rB7_0 : List NodeSpec := [([25,30,0,1,4,15,5,6],[6],[0]),([25,30,1,2,4,22,5,6],[],[0]),([25,31,1,3,22,15,5,6],[0,3],[]),([25,0,1,29,4,15,5,6],[7],[0]),([25,1,2,29,4,22,5,6],[],[0]),([25,1,3,23,22,15,5,6],[5],[]),([25,1,3,22,15,5,28,6],[],[0]),([79,0,1,2,3,4,5,32],[4],[]),([79,157,1,2,3,4,5,42],[1],[]),([68,30,0,1,2,4,5,6],[],[]),([68,0,1,2,29,4,5,6],[8],[]),([197,0,157,1,2,3,4,5],[],[]),([61,173,1,2,3,4,5,42],[0],[]),([61,1,21,3,4,5,60,42],[0],[]),([62,122,131,1,2,3,4,57],[],[]),([62,67,1,2,3,5,113,42],[2],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB7_0Ok : checkNodesBT rW rG rMask rB7_0P rAutos rK6 7 rB7_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB7_0Mem : ∀ ns ∈ rB7_0, Impossible rG 7 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK6Ok rB7_0Ok
def rB7_1S : List PoolSpec := [(31,[]),(26,[]),(40,[]),(45,[]),(47,[]),(46,[]),(7,[(1,0,2),(1,1,5),(2,21,4),(0,3,28)]),(7,[(1,0,2),(1,1,5),(2,21,4),(3,3,28)]),(25,[]),(1,[(1,0,6),(1,1,5),(0,3,28),(3,15,42)]),(1,[(1,0,6),(1,1,5),(3,3,28),(3,15,42)])]
def rB7_1P : BT (Option BoundPool) := buildPoolsBT 4 rW rR rSlices rB7_1S
def rB7_1 : List NodeSpec := [([62,99,0,1,2,3,5,57],[0],[]),([62,131,1,2,3,4,40,57],[],[]),([62,131,1,2,3,4,54,38],[2],[]),([62,0,1,2,3,143,5,57],[4],[]),([62,1,2,3,70,5,113,42],[5],[]),([97,131,1,2,3,4,5,113],[],[]),([97,131,1,2,3,4,5,57],[],[]),([97,131,1,2,3,4,113,38],[8],[]),([155,30,0,1,2,4,5,6],[10],[]),([155,0,1,2,29,4,5,6],[1,8,9],[]),([44,30,0,1,4,5,6,16],[7],[0]),([44,30,1,2,4,5,6,42],[7],[0]),([44,31,1,3,4,5,42,16],[0,3],[]),([44,0,1,29,4,5,6,16],[6],[0]),([44,1,2,29,4,5,6,42],[6],[0]),([44,1,2,3,4,5,32,42],[3],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB7_1Ok : checkNodesBT rW rG rMask rB7_1P rAutos rK6 7 rB7_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB7_1Mem : ∀ ns ∈ rB7_1, Impossible rG 7 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK6Ok rB7_1Ok
def rB7_2S : List PoolSpec := [(31,[]),(44,[]),(3,[(1,0,2),(1,0,6),(1,2,6),(2,21,4)]),(3,[(1,0,2),(1,0,6),(1,2,6),(3,4,42)]),(4,[(1,0,6),(1,1,5),(3,3,28),(3,4,42)]),(4,[(1,0,6),(1,1,5),(3,4,42),(0,3,28)]),(25,[(1,0,2),(1,21,6),(3,4,24)]),(5,[(1,0,2),(1,21,6),(3,4,24)]),(7,[(1,1,5),(1,2,42),(3,3,28),(3,4,24)])]
def rB7_2P : BT (Option BoundPool) := buildPoolsBT 4 rW rR rSlices rB7_2S
def rB7_2 : List NodeSpec := [([44,1,3,23,4,5,42,16],[2],[]),([44,1,3,4,5,28,42,16],[],[0]),([45,30,1,2,21,4,5,6],[4],[0]),([45,31,1,21,3,4,5,16],[],[]),([45,1,2,21,29,4,5,6],[5],[0]),([45,1,21,3,23,4,5,16],[3],[]),([45,1,21,3,4,5,28,16],[],[0]),([67,30,0,1,2,21,5,6],[],[]),([67,30,0,1,2,4,5,6],[],[]),([67,30,0,1,2,5,6],[],[]),([67,30,0,1,2,5,6,42],[8],[]),([67,30,0,1,2,5,6,24],[1],[]),([67,131,1,2,3,5,6,57],[0],[]),([67,0,1,2,21,29,5,6],[],[]),([67,0,1,2,29,4,5,6],[],[]),([67,0,1,2,29,5,6],[6,7],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB7_2Ok : checkNodesBT rW rG rMask rB7_2P rAutos rK6 7 rB7_2 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB7_2Mem : ∀ ns ∈ rB7_2, Impossible rG 7 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK6Ok rB7_2Ok
def rB7_3S : List PoolSpec := [(31,[]),(45,[]),(44,[]),(30,[]),(36,[]),(25,[]),(0,[(1,0,6),(1,2,42),(3,4,24)]),(9,[(1,0,6),(1,2,42),(3,4,24)]),(11,[(1,0,6),(1,2,42),(3,4,24)]),(12,[(1,0,6),(1,2,42),(3,4,24)]),(7,[(1,1,5),(1,2,42),(0,3,28),(3,4,24)]),(7,[(1,1,5),(1,2,42),(3,3,28),(0,4,24)])]
def rB7_3P : BT (Option BoundPool) := buildPoolsBT 4 rW rR rSlices rB7_3S
def rB7_3 : List NodeSpec := [([67,0,1,2,29,5,6,42],[8,9,10],[]),([67,0,1,2,29,5,6,24],[4],[]),([67,0,1,2,3,5,6,48],[],[]),([67,157,1,2,3,5,6,42],[0],[]),([67,1,2,3,5,113,42,38],[1,6],[]),([67,1,2,3,113,42,38],[1,7,8],[]),([78,0,1,2,3,5,6,32],[],[]),([78,0,1,2,3,5,6,48],[],[]),([99,131,1,2,3,5,113,6],[0],[]),([30,72,0,1,2,4,5,6],[],[]),([30,46,0,1,21,4,5,6],[5],[]),([30,46,0,1,4,5,6,24],[5],[0]),([30,46,1,21,4,5,6,42],[3],[]),([30,0,1,2,21,70,5,6],[],[]),([30,0,1,2,70,5,6,42],[2,11],[0]),([30,0,1,2,70,5,6,24],[],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB7_3Ok : checkNodesBT rW rG rMask rB7_3P rAutos rK6 7 rB7_3 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB7_3Mem : ∀ ns ∈ rB7_3, Impossible rG 7 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK6Ok rB7_3Ok
def rB7_4S : List PoolSpec := [(31,[]),(40,[]),(44,[]),(9,[(1,0,2),(1,0,4),(1,2,4)]),(22,[]),(10,[(1,1,5),(3,3,28)]),(30,[]),(23,[(1,1,5),(3,3,28)]),(25,[(1,0,2),(1,0,6),(1,2,6)]),(7,[(1,0,2),(1,1,5),(3,3,28)]),(4,[(1,0,6),(1,1,5),(3,3,28)]),(7,[(1,0,2),(1,1,5),(2,21,4),(3,3,28)]),(1,[(1,0,6),(1,1,5),(3,2,42),(3,3,28)])]
def rB7_4P : BT (Option BoundPool) := buildPoolsBT 4 rW rR rSlices rB7_4S
def rB7_4 : List NodeSpec := [([30,0,1,2,4,71,5,6],[],[]),([30,0,1,2,4,156,5,6],[12],[]),([30,0,1,2,4,5,6,69],[11],[]),([30,0,1,2,4,5,6,65],[],[0,1]),([30,0,1,21,4,5,6,18],[6],[0]),([30,0,1,21,15,5,6,17],[7],[0,1,4]),([30,0,1,4,15,5,6,24],[2],[0,4]),([30,1,2,21,4,5,42,17],[7],[0,5]),([30,1,2,4,22,5,6,24],[2],[0,1]),([30,1,2,4,43,5,6,42],[1],[4,5]),([30,1,21,4,22,5,6,16],[],[0]),([30,1,21,4,15,5,6,42],[],[0,1]),([30,1,21,4,5,42,16],[7,8,9,10],[0,4]),([30,1,21,22,15,5,6],[3,5,6],[0,1]),([46,31,0,1,3,70,5,6],[0],[0]),([46,0,1,21,29,4,5,6],[4],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB7_4Ok : checkNodesBT rW rG rMask rB7_4P rAutos rK6 7 rB7_4 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB7_4Mem : ∀ ns ∈ rB7_4, Impossible rG 7 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK6Ok rB7_4Ok
def rB7_5S : List PoolSpec := [(31,[]),(24,[]),(45,[]),(47,[]),(8,[]),(22,[]),(10,[(3,1,5),(1,21,6)]),(23,[(3,1,5)]),(3,[(1,0,2),(1,21,4),(1,43,6),(3,2,65)]),(3,[(1,0,2),(1,21,6),(3,2,24),(0,4,24)]),(1,[(1,0,6),(3,1,5),(3,15,42),(1,155,31)])]
def rB7_5P : BT (Option BoundPool) := buildPoolsBT 4 rW rR rSlices rB7_5S
def rB7_5 : List NodeSpec := [([46,0,1,29,4,5,6,24],[5],[0]),([46,0,1,3,23,70,5,6],[9],[]),([46,0,1,3,70,5,28,6],[],[0]),([46,1,21,29,4,5,6,42],[5],[]),([46,1,21,3,4,5,32,42],[4],[]),([66,31,0,1,3,4,5,6],[],[]),([66,0,1,3,23,4,5,6],[8],[]),([66,0,1,3,4,5,28,6],[],[0]),([31,1,21,3,4,5,42,18],[0,1,3],[]),([31,1,21,3,4,5,16,26],[0,2],[]),([31,1,21,3,22,5,6,18],[0,3],[]),([31,1,21,3,22,5,16,17],[],[]),([31,1,21,3,15,5,42,17],[0,3,7],[]),([31,1,3,22,15,5,6,24],[0,6],[]),([164,0,1,2,3,4,5,6],[10],[]),([49,0,1,21,3,4,5,6],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB7_5Ok : checkNodesBT rW rG rMask rB7_5P rAutos rK6 7 rB7_5 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB7_5Mem : ∀ ns ∈ rB7_5, Impossible rG 7 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK6Ok rB7_5Ok
def rB7_6S : List PoolSpec := [(31,[]),(45,[]),(46,[]),(6,[]),(22,[]),(36,[]),(7,[(1,0,2),(1,1,5),(2,21,4),(0,3,28)]),(29,[]),(4,[]),(1,[(1,0,6),(1,1,5),(3,2,42),(0,3,28)]),(3,[])]
def rB7_6P : BT (Option BoundPool) := buildPoolsBT 4 rW rR rSlices rB7_6S
def rB7_6 : List NodeSpec := [([49,0,1,3,4,5,6,24],[],[0]),([49,1,21,3,4,5,6,42],[7],[]),([196,157,1,2,3,4,5,6],[10],[]),([159,1,2,3,4,5,6,48],[8],[]),([131,1,2,3,70,5,6,57],[1,2],[]),([0,1,2,29,70,5,6,24],[],[0,1]),([0,1,2,29,4,71,5,6],[],[]),([0,1,2,29,4,156,5,6],[9],[]),([0,1,2,29,4,5,6,69],[6],[]),([0,1,2,29,4,5,6,65],[],[0,1]),([0,1,2,3,4,5,32,81],[3],[]),([0,1,21,29,4,5,6,18],[4],[0]),([0,1,21,29,15,5,6,17],[5],[0,1,4]),([0,1,29,4,15,5,6,24],[5],[0,4]),([0,1,3,70,5,60,6],[0],[]),([1,2,21,29,4,5,42,17],[5],[0,5])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB7_6Ok : checkNodesBT rW rG rMask rB7_6P rAutos rK6 7 rB7_6 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB7_6Mem : ∀ ns ∈ rB7_6, Impossible rG 7 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK6Ok rB7_6Ok
def rB7_7S : List PoolSpec := [(31,[]),(40,[]),(45,[]),(46,[]),(3,[(1,0,2),(1,0,4),(1,2,4),(1,15,6)]),(44,[]),(3,[(1,0,2),(1,0,4),(1,2,6),(1,4,6)]),(3,[(1,0,2),(1,0,4),(1,2,6),(1,22,6)]),(23,[(1,1,3)]),(11,[(1,0,2),(1,0,4),(1,2,4)]),(22,[]),(3,[(1,0,2),(1,0,6),(1,2,4),(1,4,6)]),(3,[(1,0,2),(1,0,6),(1,2,4),(1,15,6)]),(25,[(1,0,2),(1,0,6),(1,2,6)]),(36,[]),(14,[(1,0,2)]),(39,[]),(17,[(1,0,6)]),(5,[(1,0,2),(1,0,6),(1,2,6)]),(25,[]),(27,[]),(41,[]),(32,[])]
def rB7_7P : BT (Option BoundPool) := buildPoolsBT 5 rW rR rSlices rB7_7S
def rB7_7 : List NodeSpec := [([1,2,29,4,22,5,6,24],[5],[0,1]),([1,2,29,4,43,5,6,42],[14],[4,5]),([1,2,3,70,5,113,42,38],[2,3,20],[]),([1,2,3,70,113,42,38],[2,21,22],[]),([1,2,3,4,43,5,32,42],[1],[]),([1,2,3,4,60,113,42,38],[2,19],[]),([1,21,29,4,22,5,6,16],[],[0]),([1,21,29,4,15,5,6,42],[],[0,1]),([1,21,29,4,5,42,16],[13,15,16,17,18],[0,4]),([1,21,29,22,15,5,6],[5,9,10],[0,1]),([1,21,3,23,4,5,42,18],[10,12],[]),([1,21,3,23,4,5,16,26],[7],[]),([1,21,3,23,22,5,6,18],[4],[]),([1,21,3,23,22,5,16,17],[6],[]),([1,21,3,23,15,5,42,17],[8,11],[]),([1,21,3,4,15,5,32,42],[0],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB7_7Ok : checkNodesBT rW rG rMask rB7_7P rAutos rK6 7 rB7_7 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB7_7Mem : ∀ ns ∈ rB7_7, Impossible rG 7 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK6Ok rB7_7Ok
def rB7_8S : List PoolSpec := [(43,[]),(31,[]),(24,[]),(40,[]),(45,[]),(19,[]),(3,[(1,0,2),(1,0,4),(1,2,4),(1,21,6)]),(23,[(1,1,5)]),(10,[(3,1,5),(1,31,6)]),(29,[])]
def rB7_8P : BT (Option BoundPool) := buildPoolsBT 4 rW rR rSlices rB7_8S
def rB7_8 : List NodeSpec := [([1,21,3,4,5,60,42,38],[1],[]),([1,21,3,4,5,28,42,18],[2],[0]),([1,21,3,4,5,28,16,26],[],[0]),([1,21,3,4,5,32,42,47],[0,3],[]),([1,21,3,4,5,42,48,16],[3,9],[]),([1,21,3,22,15,5,6,32],[1,8],[]),([1,21,3,22,5,28,6,18],[],[0]),([1,21,3,22,5,28,16,17],[],[0]),([1,21,3,15,5,28,42,17],[7],[0]),([1,21,3,5,53,6],[0,4],[]),([1,3,23,22,15,5,6,24],[5,6],[]),([1,3,22,15,5,28,6,24],[5],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB7_8Ok : checkNodesBT rW rG rMask rB7_8P rAutos rK6 7 rB7_8 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB7_8Mem : ∀ ns ∈ rB7_8, Impossible rG 7 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK6Ok rB7_8Ok
def rNodes7 : List NodeSpec := rB7_0 ++ rB7_1 ++ rB7_2 ++ rB7_3 ++ rB7_4 ++ rB7_5 ++ rB7_6 ++ rB7_7 ++ rB7_8
def rK7 : BT (List (List Nat)) := buildBucketsBT rW rNodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rK7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible rG 7 xs.toFinset) rK7 := buildBucketsBT_of_mem (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append rB7_0Mem rB7_1Mem) rB7_2Mem) rB7_3Mem) rB7_4Mem) rB7_5Mem) rB7_6Mem) rB7_7Mem) rB7_8Mem)
def rB8_0S : List PoolSpec := [(31,[]),(40,[]),(45,[]),(47,[]),(19,[]),(3,[(1,0,2),(1,0,4),(1,2,4),(2,21,6)]),(3,[(1,0,2),(1,0,4),(2,21,6)]),(23,[(1,1,5),(3,3,28)]),(6,[(1,0,2),(1,0,4),(1,2,4),(2,21,6)]),(25,[(1,0,2),(1,0,6),(1,2,6)]),(36,[]),(14,[(1,0,2)]),(39,[]),(7,[(1,0,2),(1,1,5),(3,3,28)]),(29,[]),(3,[(1,0,2),(1,2,4),(2,21,6)]),(25,[(1,0,2),(2,21,6)]),(5,[(1,0,2),(1,21,4),(2,43,6)]),(25,[(1,0,2),(1,21,4),(2,43,6)]),(28,[]),(10,[(3,1,5),(2,21,6)]),(42,[]),(25,[(1,0,6),(1,2,42),(3,4,24)]),(7,[(3,1,5),(1,31,0),(1,157,2)]),(10,[(3,1,5),(1,31,0),(2,157,6)]),(1,[(3,1,5),(1,31,0),(2,157,6)])]
def rB8_0P : BT (Option BoundPool) := buildPoolsBT 5 rW rR rSlices rB8_0S
def rB8_0 : List NodeSpec := [([58,67,0,1,2,3,5,6],[2,22],[]),([58,1,21,3,4,5,42,16],[0,1,2,9,14],[]),([201,0,1,2,3,4,15,5,6],[0,24,25],[]),([80,0,1,2,3,4,5,6,32],[0],[0]),([25,30,0,1,2,4,5,6],[7,13,16,19],[0]),([25,31,0,1,3,4,15,5,6],[0,20],[0]),([25,31,1,2,3,4,22,5,6],[0,2],[0]),([25,0,1,2,29,4,5,6],[10,11,12,16],[0]),([25,0,1,3,23,4,15,5,6],[4,15],[0]),([25,0,1,3,4,15,5,28,6],[4],[0]),([25,1,2,3,23,4,22,5,6],[6],[0]),([25,1,2,3,4,22,5,28,6],[],[0]),([25,1,3,22,15,5,6],[2,3,5,8],[0,2]),([79,0,157,1,2,3,4,5,6],[21,23],[0,4]),([68,39,0,1,2,3,4,5],[2,18],[]),([68,31,0,1,2,3,4,5,6],[0,3,17],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB8_0Ok : checkNodesBT rW rG rMask rB8_0P rAutos rK7 8 rB8_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB8_0Mem : ∀ ns ∈ rB8_0, Impossible rG 8 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK7Ok rB8_0Ok
def rB8_1S : List PoolSpec := [(40,[]),(45,[]),(47,[]),(46,[]),(44,[]),(25,[(1,0,2),(1,0,4),(1,2,4)]),(10,[(2,5,6)]),(29,[]),(8,[(1,5,42)]),(2,[(1,0,2),(1,21,4),(2,43,6)]),(3,[(1,0,2),(1,21,4),(2,43,6)]),(5,[(1,0,2),(1,21,4),(2,43,6)]),(25,[(1,0,2),(1,21,4),(2,43,6)]),(34,[]),(48,[]),(1,[(1,0,5),(1,113,6),(2,113,6)]),(4,[(1,0,5),(1,113,6),(2,113,6)]),(7,[(1,5,42),(3,0,57)])]
def rB8_1P : BT (Option BoundPool) := buildPoolsBT 5 rW rR rSlices rB8_1S
def rB8_1 : List NodeSpec := [([68,0,1,2,3,23,4,5,6],[4,9,10],[]),([68,0,1,2,3,4,5,28,6],[11,12],[0]),([39,1,21,3,22,15,5,6],[1,5,6],[]),([62,122,0,1,2,3,4,57],[1,7],[0]),([62,122,1,2,3,4,113,42],[1,14],[]),([62,46,1,2,3,4,5,113,42],[1],[]),([62,139,0,1,2,3,4,5,57],[3],[]),([62,131,1,2,3,4,5,42],[1,3,7,8],[]),([62,131,1,2,3,4,5,42,57],[1,7,17],[0]),([62,131,1,2,3,4,5,57],[0,7],[0,1]),([62,131,1,2,3,4,113,38],[0,7],[0,1,4,5]),([62,0,1,2,3,4,15,5,57],[1,2,15],[]),([62,0,1,2,3,4,5,57,98],[1,16],[0,4]),([62,0,1,2,3,4,40,57],[3,16],[0]),([62,0,1,2,3,4,54,38],[0,3,14],[0]),([62,0,1,2,3,115,6],[1,13],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB8_1Ok : checkNodesBT rW rG rMask rB8_1P rAutos rK7 8 rB8_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB8_1Mem : ∀ ns ∈ rB8_1, Impossible rG 8 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK7Ok rB8_1Ok
def rB8_2S : List PoolSpec := [(43,[]),(40,[]),(45,[]),(46,[]),(23,[]),(29,[]),(7,[(1,0,2),(1,5,42)]),(16,[]),(25,[(1,0,2),(1,21,4),(2,87,6)]),(25,[(1,0,2),(2,54,6)]),(1,[(1,0,5),(1,0,6),(2,113,6)]),(48,[]),(25,[(1,2,4),(1,15,113),(2,87,6)]),(26,[(1,2,4),(1,15,113),(2,87,6)]),(42,[]),(7,[(1,0,5),(1,2,113)]),(0,[(1,2,113),(2,54,6)]),(9,[(1,2,113),(2,54,6)]),(11,[(1,2,113),(2,54,6)]),(4,[(1,0,5),(1,113,6),(2,54,6)])]
def rB8_2P : BT (Option BoundPool) := buildPoolsBT 5 rW rR rSlices rB8_2S
def rB8_2 : List NodeSpec := [([62,1,2,21,3,4,5,42],[2,3],[]),([62,1,2,21,3,4,5,42,57],[2,3,6],[]),([62,1,2,3,4,15,5,113,42],[2,10],[]),([62,1,2,3,4,5,113,42,24],[2,3],[0]),([62,1,2,3,4,5,54,42],[3,5,7],[]),([62,1,2,3,4,113,40,42],[3,11],[]),([85,0,1,21,3,4,5,38],[1,3],[]),([97,0,1,2,3,4,5,113,38],[14,15,16],[0]),([97,0,1,2,3,4,5,113,57],[2,5],[0]),([97,0,1,2,3,4,5,38],[3,9],[]),([97,0,1,2,3,4,5,57],[3,19],[0]),([97,0,1,2,3,4,113,38],[0,3,5,17,18],[0]),([97,1,2,3,4,5,113,42],[3,4,5],[]),([88,0,1,2,3,4,5],[2,8],[]),([88,0,1,2,3,4,5,113],[2,12,13],[]),([126,1,2,3,4,113,6,42],[2,5],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB8_2Ok : checkNodesBT rW rG rMask rB8_2P rAutos rK7 8 rB8_2 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB8_2Mem : ∀ ns ∈ rB8_2, Impossible rG 8 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK7Ok rB8_2Ok
def rB8_3S : List PoolSpec := [(31,[]),(26,[]),(13,[]),(40,[]),(45,[]),(44,[]),(10,[(1,1,5),(3,3,28)]),(23,[(1,1,5),(3,3,28)]),(25,[(1,0,2),(1,0,6),(1,2,6)]),(39,[]),(7,[(1,0,2),(1,1,5),(2,21,4),(0,3,28)]),(7,[(1,0,2),(1,1,5),(2,21,4),(3,3,28)]),(29,[]),(7,[(1,0,2),(3,1,5),(2,21,4)]),(25,[]),(11,[(1,0,2),(2,21,4)]),(25,[(1,0,2),(2,21,4)]),(25,[(1,0,6)]),(7,[(1,0,5),(3,0,57),(3,5,57)]),(1,[(1,0,6),(1,1,3),(3,15,42)]),(3,[(1,0,6),(1,2,4),(3,15,42)]),(1,[(1,0,6),(1,1,5),(3,15,42)]),(1,[(1,0,6),(3,1,5),(3,15,42)]),(25,[(1,0,6),(1,122,2),(2,184,4)])]
def rB8_3P : BT (Option BoundPool) := buildPoolsBT 5 rW rR rSlices rB8_3S
def rB8_3 : List NodeSpec := [([55,1,2,3,4,5,42,38],[0,2,4],[]),([55,1,3,4,5,42,16],[0,4,8],[]),([122,131,1,2,3,4,113,6],[3,4,12],[]),([122,131,1,2,3,4,113,6,57],[12,18],[0]),([122,1,2,3,4,113,42,38],[4,17],[]),([182,0,1,2,3,4,6],[4,17],[]),([182,0,1,2,3,4,6,57],[3,4,12,17],[]),([155,31,0,1,2,3,4,5,6],[0,14,22],[0]),([155,0,1,2,3,23,4,5,6],[5,14,19,20],[]),([155,0,1,2,3,4,5,28,6],[1,14,21],[0]),([185,0,1,2,3,5,6],[4,23],[]),([44,30,0,1,2,4,5,6],[6,7,11,16],[0]),([44,31,0,1,3,4,5,6,16],[0,4,13],[0]),([44,31,1,2,3,4,5,6,42],[0,4,13],[0]),([44,0,1,2,29,4,5,6],[5,9,10,15],[0]),([44,0,1,2,3,4,5,6,32],[0,4],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB8_3Ok : checkNodesBT rW rG rMask rB8_3P rAutos rK7 8 rB8_3 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB8_3Mem : ∀ ns ∈ rB8_3, Impossible rG 8 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK7Ok rB8_3Ok
def rB8_4S : List PoolSpec := [(31,[]),(45,[]),(19,[]),(3,[(1,0,2),(1,0,6),(1,2,6),(2,21,4)]),(3,[(1,0,2),(1,0,6),(1,2,6),(3,4,42)]),(7,[(1,0,2),(1,1,3),(2,21,4)]),(3,[(1,0,2),(1,0,6),(2,21,4)]),(3,[(1,0,2),(1,0,6),(3,4,42)]),(4,[(1,0,6),(1,1,3),(3,4,42)]),(7,[(1,0,2),(1,1,5),(2,21,4)]),(4,[(1,0,6),(1,1,5),(3,4,42)]),(4,[(1,0,6),(3,1,5),(3,4,42)]),(6,[(1,0,2),(1,0,6),(1,2,6),(2,21,4)]),(6,[(1,0,2),(1,0,6),(1,2,6),(3,4,42)]),(3,[(1,0,2),(1,2,6),(2,21,4)]),(25,[(1,0,2),(1,21,6),(3,4,24)]),(7,[(1,0,2),(3,1,5),(3,4,24)]),(8,[(3,1,5),(1,21,6),(3,4,24)]),(0,[(1,0,6),(1,2,42),(3,4,24)]),(7,[(3,1,5),(1,2,42),(3,4,24)]),(10,[(3,1,5),(1,31,0)])]
def rB8_4P : BT (Option BoundPool) := buildPoolsBT 5 rW rR rSlices rB8_4S
def rB8_4 : List NodeSpec := [([44,0,1,3,23,4,5,6,16],[5,14],[0]),([44,0,1,3,4,5,28,6,16],[9],[0]),([44,1,2,3,23,4,5,6,42],[5,6],[0]),([44,1,2,3,4,5,28,6,42],[9],[0]),([44,1,2,3,4,5,42,38],[0,1],[]),([44,1,3,4,5,42,16],[0,1,3,12],[0,2]),([198,0,157,1,2,3,4,5,6],[1,20],[]),([45,31,1,2,21,3,4,5,6],[0,11],[0]),([45,1,2,21,3,23,4,5,6],[7,8],[0]),([45,1,2,21,3,4,5,28,6],[10],[0]),([45,1,21,3,4,5,16],[1,4,13],[0,2]),([67,31,0,1,2,21,3,5,6],[0,1],[]),([67,31,0,1,2,3,4,5,6],[0,1],[]),([67,31,0,1,2,3,5,6],[0,1,15,16,17],[]),([67,31,0,1,2,3,5,6,42],[1,18,19],[0,4]),([67,31,0,1,2,3,5,6,24],[0,1,2],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB8_4Ok : checkNodesBT rW rG rMask rB8_4P rAutos rK7 8 rB8_4 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB8_4Mem : ∀ ns ∈ rB8_4, Impossible rG 8 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK7Ok rB8_4Ok
def rB8_5S : List PoolSpec := [(31,[]),(45,[]),(19,[]),(3,[(1,0,2),(1,21,6),(3,4,24)]),(25,[(1,0,2),(1,21,6),(3,4,24)]),(12,[(1,0,2),(1,21,6),(3,4,24)]),(5,[(1,0,2),(1,21,6),(3,4,24)]),(25,[(1,0,2),(1,54,6),(3,4,98)]),(25,[(1,0,2),(1,21,38),(3,4,98)]),(26,[(1,0,2),(1,21,38),(3,4,98)]),(9,[(1,0,6),(1,2,42),(3,4,24)]),(11,[(1,0,6),(1,2,42),(3,4,24)]),(3,[(1,0,6),(1,2,42),(3,4,24)]),(7,[(1,1,3),(1,2,42),(3,4,24)]),(12,[(1,0,6),(1,2,42),(3,4,24)]),(25,[(1,0,6),(1,2,42),(3,4,24)]),(7,[(1,1,5),(1,2,42),(3,4,24)]),(26,[(1,0,6),(1,2,42),(3,4,24)])]
def rB8_5P : BT (Option BoundPool) := buildPoolsBT 5 rW rR rSlices rB8_5S
def rB8_5 : List NodeSpec := [([67,0,1,2,21,3,23,5,6],[0,1,3],[]),([67,0,1,2,21,3,5,28,6],[0,1],[0]),([67,0,1,2,3,23,4,5,6],[0,1,3],[]),([67,0,1,2,3,23,5,6],[3,4,5],[]),([67,0,1,2,3,23,5,6,42],[1,10,12,13,14],[]),([67,0,1,2,3,23,5,6,24],[0,1,2,3],[]),([67,0,1,2,3,4,5,28,6],[0,1],[0]),([67,0,1,2,3,5,28,6],[4,6],[0]),([67,0,1,2,3,5,28,6,42],[11,15,16],[0]),([67,0,1,2,3,5,28,6,24],[0,1,2],[0]),([67,0,1,2,3,5,6,50],[1,17],[]),([67,0,1,2,3,5,6,57],[1,10,11,14],[0,4]),([67,1,2,3,5,113,6,42],[1,10,11],[0]),([99,0,1,2,3,5,113,6,57],[1],[0]),([99,0,1,2,3,5,6],[1,7],[]),([99,0,1,2,3,5,6,38],[1,8,9],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB8_5Ok : checkNodesBT rW rG rMask rB8_5P rAutos rK7 8 rB8_5 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB8_5Mem : ∀ ns ∈ rB8_5, Impossible rG 8 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK7Ok rB8_5Ok
def rB8_6S : List PoolSpec := [(43,[]),(31,[]),(40,[]),(45,[]),(44,[]),(9,[(1,0,2),(1,0,4)]),(10,[(1,1,5),(3,3,28)]),(30,[]),(21,[(1,1,5),(3,3,28)]),(23,[(1,1,5),(3,3,28)]),(25,[(1,0,2),(1,0,6)]),(36,[]),(7,[(1,0,2),(1,1,5),(3,3,28)]),(4,[(1,0,6),(1,1,5),(3,3,28)]),(9,[(1,0,2),(1,2,4)]),(25,[(1,0,2),(1,2,6)]),(25,[(1,0,2),(1,21,6)]),(8,[(1,1,5),(1,2,4),(3,3,28)]),(8,[(1,1,5),(1,2,6),(3,3,28)]),(16,[(1,1,5),(3,3,28)]),(25,[(1,0,2),(1,21,4)]),(8,[(1,1,5),(1,21,4),(3,3,28)]),(28,[]),(4,[(1,1,5),(1,21,6),(3,3,28)]),(8,[(1,1,5),(1,21,6),(3,3,28)]),(25,[(1,0,6),(3,2,42)]),(25,[(1,113,6),(1,2,57),(3,4,98)]),(26,[(1,113,6),(1,2,57),(3,4,98)]),(7,[(1,1,5),(1,2,42),(3,3,28)]),(7,[(1,1,5),(3,2,42),(3,3,28)]),(1,[(1,0,6),(1,1,5),(3,2,42),(3,3,28)]),(8,[(1,1,5),(3,2,42),(3,3,28)])]
def rB8_6P : BT (Option BoundPool) := buildPoolsBT 5 rW rR rSlices rB8_6S
def rB8_6 : List NodeSpec := [([99,0,1,2,3,5,6,57],[3,26,27],[0,4]),([30,46,0,1,2,4,5,6],[13,25,29,30,31],[0,1,5]),([30,46,0,1,2,4,5,6,42],[7,13,29],[0,4]),([30,0,1,2,21,4,43,5,6],[6,8,9],[]),([30,0,1,2,21,4,5,6,24],[9,19],[0]),([30,0,1,2,21,4,5,6,17],[2,9,22],[0,1,4,5]),([30,0,1,2,4,15,5,6,42],[2,4,13,17],[0,1,4,5]),([30,0,1,2,4,43,5,6],[2,6,8,9,20,21],[0,4,5]),([30,0,1,2,4,5,6,42,24],[9,13,19,28],[0]),([30,0,1,2,4,5,6,24],[9,12,16,19,22,23,24],[0,4]),([30,0,1,21,4,15,5,6],[6,9,14,17],[0]),([30,0,1,21,4,5,6,16],[0,9,12,15,18,19],[0,4]),([30,1,2,21,4,22,5,6],[5,6,7,8,9],[0,1]),([30,1,2,21,4,5,6,42],[7,9,10,12,13],[0,1]),([72,31,0,1,2,3,4,5,6],[1,3],[]),([72,0,1,2,3,23,4,5,6],[3,11],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB8_6Ok : checkNodesBT rW rG rMask rB8_6P rAutos rK7 8 rB8_6 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB8_6Mem : ∀ ns ∈ rB8_6, Impossible rG 8 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK7Ok rB8_6Ok
def rB8_7S : List PoolSpec := [(31,[]),(24,[]),(40,[]),(45,[]),(46,[]),(6,[]),(36,[]),(17,[(1,0,6)]),(29,[]),(16,[]),(3,[(1,0,2),(1,21,6),(3,2,24)]),(25,[]),(48,[]),(8,[(3,2,113),(1,5,6)]),(49,[]),(25,[(1,0,6),(3,2,42)]),(11,[(1,0,6),(3,2,42)]),(42,[]),(33,[]),(12,[(1,0,6),(3,2,42)]),(7,[(1,1,5),(3,2,42),(0,3,28)]),(1,[(1,0,6),(1,1,5),(3,2,42),(0,3,28)]),(8,[(1,1,5),(3,2,42),(0,3,28)])]
def rB8_7P : BT (Option BoundPool) := buildPoolsBT 5 rW rR rSlices rB8_7S
def rB8_7 : List NodeSpec := [([72,0,1,2,3,4,5,28,6],[3,6],[0]),([91,131,1,2,3,4,5,6,57],[4],[]),([91,131,1,2,3,4,113,6,38],[8],[]),([91,1,2,3,4,5,42,38],[4,9,12,13],[]),([91,1,2,3,4,113,42,38],[2,4,12,13],[]),([91,1,2,3,4,42,38],[4,9,12,14],[]),([46,31,0,1,21,3,4,5,6],[0,5],[0]),([46,31,0,1,3,4,5,6,24],[0,5],[0]),([46,31,1,21,3,4,5,6,42],[0,1],[0]),([46,49,0,1,2,3,4,5,6],[11],[0]),([46,131,1,2,3,4,5,6,57],[3],[]),([46,0,1,2,29,4,5,6],[7,15,16,20,21,22],[0,1,5]),([46,0,1,2,29,4,5,6,42],[7,14,16,18,19,20],[0,4]),([46,0,1,2,3,4,5,6,48],[17],[]),([46,0,1,21,3,23,4,5,6],[10],[]),([46,0,1,21,3,4,5,28,6],[5],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB8_7Ok : checkNodesBT rW rG rMask rB8_7P rAutos rK7 8 rB8_7 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB8_7Mem : ∀ ns ∈ rB8_7, Impossible rG 8 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK7Ok rB8_7Ok
def rB8_8S : List PoolSpec := [(31,[]),(24,[]),(40,[]),(45,[]),(47,[]),(46,[]),(6,[]),(22,[]),(3,[(1,0,2),(1,0,6),(3,2,42)]),(29,[]),(8,[(3,2,42),(1,5,6)]),(3,[(1,0,2),(1,21,4),(1,43,6),(3,2,65)]),(3,[(1,0,2),(1,21,6),(3,2,24)]),(3,[(1,0,2),(1,21,6),(3,2,24),(0,4,24)]),(25,[]),(6,[(1,0,2),(1,21,4),(1,43,6),(3,2,65)]),(6,[(1,0,2),(1,21,6),(3,2,24),(0,4,24)]),(7,[(1,0,5)]),(0,[(1,0,6),(3,2,42)]),(25,[(1,0,6),(3,2,42)]),(11,[(1,0,6),(3,2,42)]),(7,[(3,1,5),(1,31,0),(3,2,42)]),(4,[(1,0,6),(3,1,5),(1,31,42)]),(4,[(3,1,5),(1,31,0),(1,157,6)])]
def rB8_8P : BT (Option BoundPool) := buildPoolsBT 5 rW rR rSlices rB8_8S
def rB8_8 : List NodeSpec := [([46,0,1,3,23,4,5,6,24],[12],[0]),([46,0,1,3,70,5,6],[3,13,16],[0,2]),([46,0,1,3,4,5,28,6,24],[6],[0]),([46,157,1,2,3,4,5,6,42],[1,21],[4]),([46,1,2,3,4,5,113,42,38],[3,18],[0]),([46,1,2,3,4,113,42,38],[2,3,9,10,17,19,20],[]),([46,1,21,3,23,4,5,6,42],[7,8],[]),([46,1,21,3,4,5,28,6,42],[1],[0]),([46,1,21,3,4,5,42,38],[3,10],[0]),([160,0,157,1,2,3,4,5,6],[0,23],[]),([160,0,1,2,3,4,5,6,48],[0,22],[]),([66,0,1,3,4,5,6],[3,11,15],[0,2]),([139,131,1,2,3,4,5,113,6],[2,5],[]),([175,0,1,2,3,4,5,6],[3,19],[]),([31,0,1,2,3,70,5,6,24],[0,3],[0,1]),([31,0,1,2,3,4,71,5,6],[0,4,14],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB8_8Ok : checkNodesBT rW rG rMask rB8_8P rAutos rK7 8 rB8_8 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB8_8Mem : ∀ ns ∈ rB8_8, Impossible rG 8 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK7Ok rB8_8Ok
def rB8_9S : List PoolSpec := [(31,[]),(24,[]),(40,[]),(45,[]),(47,[]),(46,[]),(25,[(1,0,2),(1,0,4),(1,2,4)]),(10,[(3,1,5),(1,21,6)]),(10,[(3,1,5)]),(21,[(3,1,5)]),(23,[(3,1,5)]),(10,[]),(25,[(1,0,2),(1,0,6),(1,2,6)]),(29,[]),(4,[(1,0,6),(3,1,5)]),(7,[(1,0,2),(3,1,5),(1,21,4)]),(7,[(1,0,2),(3,1,5),(2,21,4)]),(25,[]),(25,[(1,0,6),(3,2,42)]),(4,[(1,0,6),(3,1,5),(1,46,31)]),(7,[(3,1,5),(3,2,42),(1,46,31)]),(1,[(1,0,6),(3,1,5),(3,2,42),(1,46,31)]),(8,[(3,1,5),(3,2,42),(1,46,31)]),(1,[(1,0,6),(3,1,5),(3,2,42)])]
def rB8_9P : BT (Option BoundPool) := buildPoolsBT 5 rW rR rSlices rB8_9S
def rB8_9 : List NodeSpec := [([31,0,1,2,3,4,156,5,6],[0,3,23],[]),([31,0,1,2,3,4,5,6,69],[0,3,16],[]),([31,0,1,2,3,4,5,6,65],[0,4,17],[0,1]),([31,0,1,21,3,4,5,6,18],[0,1,4],[0]),([31,0,1,21,3,15,5,6,17],[0,10,11],[0,1,4]),([31,0,1,3,4,15,5,6,24],[0,7],[0,4]),([31,1,2,21,3,4,5,42,17],[0,3,10],[0,5]),([31,1,2,3,4,22,5,6,24],[0,3,7],[0,1]),([31,1,2,3,4,43,5,6,42],[0,4,15],[0,4,5]),([31,1,21,3,4,22,5,6,16],[0,3],[0]),([31,1,21,3,4,15,5,6,42],[0,4],[0,1]),([31,1,21,3,4,5,42,16],[2,3,5,10,12,14],[0,4]),([31,1,21,3,22,15,5,6],[0,3,6,8,9],[0,1]),([49,0,1,2,3,4,5,6],[3,18,19,20,21,22],[]),([49,0,1,2,3,4,5,6,42],[2,13,19,20],[0,4]),([173,1,2,3,4,5,60,6,42],[2,3],[0,4])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB8_9Ok : checkNodesBT rW rG rMask rB8_9P rAutos rK7 8 rB8_9 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB8_9Mem : ∀ ns ∈ rB8_9, Impossible rG 8 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK7Ok rB8_9Ok
def rB8_10S : List PoolSpec := [(43,[]),(40,[]),(35,[]),(45,[]),(47,[]),(26,[(1,2,4),(1,15,6),(3,0,18)]),(46,[]),(23,[]),(29,[]),(27,[]),(25,[(1,2,4),(3,0,37)]),(1,[(1,0,5),(1,5,6),(3,0,38)]),(4,[(1,0,5),(1,113,6),(3,0,57)]),(7,[(1,0,5),(1,2,113),(3,0,38)]),(4,[(1,0,5),(1,5,6),(3,0,38)]),(1,[(1,0,5),(1,113,6),(3,0,57)]),(4,[(1,0,5),(1,113,6),(3,0,98)])]
def rB8_10P : BT (Option BoundPool) := buildPoolsBT 5 rW rR rSlices rB8_10S
def rB8_10 : List NodeSpec := [([82,1,2,3,4,5,113,117,6],[2,7],[]),([82,1,2,3,4,5,113,6,57],[6,7],[]),([82,1,2,3,4,113,41,6],[0,6,8],[]),([82,1,2,3,4,113,6,38],[0,6,8],[]),([129,1,2,3,4,5,113,6],[3,10],[]),([19,1,7,2,3,4,5,6],[3,5],[]),([131,1,2,3,4,15,5,113,6],[3,4,11],[]),([131,1,2,3,4,15,113,6,38],[3,9,11],[]),([131,1,2,3,4,5,113,54,6],[1,3,7,8],[0]),([131,1,2,3,4,5,113,6,98],[3,15],[0]),([131,1,2,3,4,5,54,6,57],[1,12],[0]),([131,1,2,3,4,5,6,24,57],[3,6],[0]),([131,1,2,3,4,113,40,6],[1,6,8],[]),([131,1,2,3,4,113,40,6,57],[6,8,12],[0]),([131,1,2,3,4,113,54,6,38],[3,8,13,14],[0]),([142,1,2,3,4,5,113,6,57],[6,16],[4])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB8_10Ok : checkNodesBT rW rG rMask rB8_10P rAutos rK7 8 rB8_10 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB8_10Mem : ∀ ns ∈ rB8_10, Impossible rG 8 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK7Ok rB8_10Ok
def rB8_11S : List PoolSpec := [(43,[]),(31,[]),(26,[]),(40,[]),(45,[]),(26,[(1,2,4),(1,2,6),(1,4,6)]),(44,[]),(10,[]),(7,[(1,0,2),(1,1,3),(2,21,4)]),(36,[]),(14,[(1,0,2)]),(39,[]),(17,[(1,0,6)]),(3,[(1,0,2),(2,21,4),(1,44,6)]),(3,[(1,0,2),(1,21,6),(0,4,24)]),(25,[(1,0,2),(1,21,6)]),(3,[(1,0,2),(2,21,6),(1,25,4)]),(8,[(1,1,5),(1,2,4),(0,3,28)]),(37,[]),(38,[]),(11,[(1,0,2),(1,21,4)]),(8,[(1,1,5),(1,21,4),(0,3,28)]),(25,[]),(8,[(1,1,5),(1,21,6),(0,3,28)]),(4,[(1,1,5),(1,21,6),(0,3,28)]),(32,[]),(11,[(1,0,6),(1,2,42)]),(33,[]),(12,[(1,0,6),(1,2,42)]),(1,[(1,0,6),(1,1,3),(3,2,42)]),(3,[(1,0,6),(3,2,42),(1,46,4)]),(15,[(1,0,6)]),(7,[(1,1,5),(1,2,42),(0,3,28)]),(10,[(3,1,5),(1,31,0)]),(4,[(3,1,5),(1,31,0),(1,157,6)])]
def rB8_11P : BT (Option BoundPool) := buildPoolsBT 6 rW rR rSlices rB8_11S
def rB8_11 : List NodeSpec := [([0,157,1,2,3,4,195,5,6],[3,7],[0]),([0,1,7,3,15,5,16,17],[0,4,5],[]),([0,1,2,174,3,4,5,6,57],[4],[]),([0,1,2,21,29,4,43,5,6],[6,11,19],[]),([0,1,2,21,29,4,5,6,24],[6,11,18],[0]),([0,1,2,21,29,4,5,6,17],[9,11],[0,1,4,5]),([0,1,2,76,3,4,158,5,6],[1,4,33],[]),([0,1,2,76,3,4,5,6,48],[1,3,34],[4]),([0,1,2,29,4,15,5,6,42],[6,12,17,25,27],[0,1,4,5]),([0,1,2,29,4,43,5,6],[6,9,11,19,20,21],[0,4,5]),([0,1,2,29,4,5,6,42,24],[11,12,18,26,28,31,32],[0]),([0,1,2,29,4,5,6,24],[6,10,11,15,18,23,24],[0,4]),([0,1,2,3,23,70,5,6,24],[1,4,14],[0,1]),([0,1,2,3,23,4,71,5,6],[2,6,16],[]),([0,1,2,3,23,4,156,5,6],[22,27,29,30],[]),([0,1,2,3,23,4,5,6,69],[2,6,8,13],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB8_11Ok : checkNodesBT rW rG rMask rB8_11P rAutos rK7 8 rB8_11 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB8_11Mem : ∀ ns ∈ rB8_11, Impossible rG 8 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK7Ok rB8_11Ok
def rB8_12S : List PoolSpec := [(31,[]),(26,[]),(40,[]),(45,[]),(47,[]),(46,[]),(44,[]),(10,[(3,1,5),(1,31,6)]),(10,[]),(23,[]),(7,[(1,0,2),(1,1,5),(2,21,4)]),(3,[(1,0,2),(1,21,4),(1,43,6)]),(25,[(1,0,2),(1,21,4)]),(25,[]),(28,[]),(25,[(1,0,2),(1,55,6)]),(48,[]),(32,[]),(1,[(1,0,6),(1,1,5),(3,2,42)]),(4,[(1,0,6),(3,1,5),(1,31,42)]),(1,[(1,0,6),(3,1,5),(1,31,42)]),(1,[(1,0,6),(3,15,42),(1,155,5)]),(25,[(1,0,6),(3,40,42)])]
def rB8_12P : BT (Option BoundPool) := buildPoolsBT 5 rW rR rSlices rB8_12S
def rB8_12 : List NodeSpec := [([0,1,2,3,23,4,5,6,65],[1,6,11],[0,1]),([0,1,2,3,70,5,28,6,24],[0,3],[0,1]),([0,1,2,3,70,5,6,57],[3,5,6,14,17],[0,4]),([0,1,2,3,4,71,5,28,6],[1,13],[0]),([0,1,2,3,4,156,5,28,6],[1,13,18],[0]),([0,1,2,3,4,15,5,6,48],[0,8,20],[]),([0,1,2,3,4,43,5,6,32],[0,4],[0]),([0,1,2,3,4,5,168,6],[1,3,13,21],[]),([0,1,2,3,4,5,60,6],[3,22],[]),([0,1,2,3,4,5,28,6,69],[1,10,13],[0]),([0,1,2,3,4,5,28,6,65],[1,12],[0,1]),([0,1,2,3,4,5,6,32,77],[7,9],[0]),([0,1,2,3,4,5,6,48,24],[0,19,20],[0]),([0,1,2,3,4,5,6,48,77],[0,19,20],[0,4]),([0,1,2,3,4,5,101,38],[3,15],[]),([0,1,2,3,115,113,6,57],[2,3,16],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB8_12Ok : checkNodesBT rW rG rMask rB8_12P rAutos rK7 8 rB8_12 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB8_12Mem : ∀ ns ∈ rB8_12, Impossible rG 8 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK7Ok rB8_12Ok
def rB8_13S : List PoolSpec := [(43,[]),(31,[]),(24,[]),(40,[]),(45,[]),(19,[]),(44,[]),(23,[(1,1,3)]),(22,[]),(23,[(1,1,5)]),(10,[(3,1,5),(1,31,6)]),(14,[(1,0,2)]),(39,[]),(29,[]),(3,[(1,0,2),(1,2,4),(1,21,6)]),(3,[(1,0,2),(1,2,4),(1,4,6)]),(3,[(1,0,2),(1,2,4),(1,15,6)]),(25,[(1,0,2),(1,2,6)]),(8,[(1,1,5),(1,2,4),(0,3,28)]),(11,[(1,0,2),(1,2,4)]),(8,[(1,1,5),(1,2,6),(0,3,28)]),(37,[]),(25,[(1,0,6)]),(25,[(1,113,6)]),(42,[])]
def rB8_13P : BT (Option BoundPool) := buildPoolsBT 5 rW rR rSlices rB8_13S
def rB8_13 : List NodeSpec := [([0,1,2,3,115,6,57],[3,4,13,23],[]),([0,1,2,3,5,53,6],[4,24],[0,4]),([0,1,21,29,4,15,5,6],[6,12,18,19],[0]),([0,1,21,29,4,5,6,16],[11,12,17,20,21],[0,4]),([0,1,21,3,23,4,5,6,18],[8,16],[0]),([0,1,21,3,23,15,5,6,17],[7,15],[0,1,4]),([0,1,21,3,4,15,5,6,32],[1,10],[0]),([0,1,21,3,4,5,60,6],[4],[]),([0,1,21,3,4,5,28,6,18],[2],[0]),([0,1,21,3,4,5,6,32,47],[0,3,13],[0]),([0,1,21,3,15,5,28,6,17],[9],[0,1,4]),([0,1,3,23,4,15,5,6,24],[5,14],[0,4]),([0,1,3,4,15,5,28,6,24],[5],[0,4]),([0,1,3,4,5,60,6,24],[4],[0]),([0,1,3,4,124,6,57],[3,4,13,22],[]),([157,1,2,76,3,4,5,6,42],[3,13,24],[0,4])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB8_13Ok : checkNodesBT rW rG rMask rB8_13P rAutos rK7 8 rB8_13 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB8_13Mem : ∀ ns ∈ rB8_13, Impossible rG 8 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK7Ok rB8_13Ok
def rB8_14S : List PoolSpec := [(43,[]),(31,[]),(40,[]),(45,[]),(47,[]),(19,[]),(46,[]),(3,[(1,0,2),(1,0,4),(1,21,6)]),(23,[(1,1,3)]),(23,[(1,1,5)]),(10,[(3,1,5),(1,31,6)]),(23,[(3,1,5)]),(23,[]),(3,[(1,0,2),(1,0,6),(1,21,4)]),(3,[(1,0,2),(1,0,6),(1,4,6)]),(25,[(1,0,2),(1,0,6)]),(4,[(1,0,6),(3,1,5),(1,31,6)]),(29,[]),(16,[]),(27,[]),(41,[]),(1,[(1,0,5),(1,0,6),(1,5,6)]),(1,[(1,0,6),(3,1,5),(1,31,0)])]
def rB8_14P : BT (Option BoundPool) := buildPoolsBT 5 rW rR rSlices rB8_14S
def rB8_14 : List NodeSpec := [([157,1,2,3,4,15,5,6,42],[1,2,22],[4,5]),([157,1,2,3,4,5,6,42,24],[11,18,22],[0]),([1,2,127,3,4,5,113,42],[6,12,17],[]),([1,2,21,3,23,4,5,42,17],[8,14],[0,5]),([1,2,21,3,4,22,5,6,32],[1,3,10],[0]),([1,2,21,3,4,5,28,42,17],[9],[0,5]),([1,2,21,3,4,5,6,42,48],[1,2,12,17],[0]),([1,2,21,3,4,5,32,42],[1,2,3,15,16,17],[0]),([1,2,21,3,4,5,63,42],[3,6],[]),([1,2,3,23,4,22,5,6,24],[5,7],[0,1]),([1,2,3,23,4,43,5,6,42],[2,13],[4,5]),([1,2,3,4,22,5,28,6,24],[5],[0,1]),([1,2,3,4,15,5,113,42,38],[3,4,19,21],[]),([1,2,3,4,15,113,42,38],[0,3,4,20,21],[]),([1,2,3,4,43,5,28,6,42],[2],[0,4,5]),([1,2,3,4,43,5,42,38],[3,4],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB8_14Ok : checkNodesBT rW rG rMask rB8_14P rAutos rK7 8 rB8_14 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB8_14Mem : ∀ ns ∈ rB8_14, Impossible rG 8 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK7Ok rB8_14Ok
def rB8_15S : List PoolSpec := [(43,[]),(24,[]),(26,[]),(13,[]),(40,[]),(45,[]),(46,[]),(44,[]),(9,[(1,0,2),(1,0,4),(1,2,4)]),(3,[(1,0,2),(1,0,4),(1,2,4)]),(3,[(1,0,2),(1,0,4),(1,2,6)]),(23,[(1,1,3)]),(3,[(1,0,2),(1,0,6),(1,2,4)]),(25,[(1,0,2),(1,0,6),(1,2,6)]),(12,[(1,0,2),(1,0,6),(1,2,6)]),(7,[(1,0,2),(1,1,3)]),(4,[(1,0,6),(1,1,3)]),(3,[(1,0,2),(1,0,6),(1,2,6)]),(25,[(1,0,2),(1,0,6)]),(29,[]),(26,[(1,0,2),(1,0,6)]),(34,[]),(7,[(1,0,5)]),(25,[(1,0,6)]),(4,[(1,0,5),(1,0,6),(1,5,6)]),(48,[]),(25,[(1,0,6),(1,2,113)]),(26,[(1,0,6),(1,2,113)]),(0,[(1,0,6),(1,2,42)]),(9,[(1,0,6),(1,2,42)]),(11,[(1,0,6),(1,2,42)])]
def rB8_15P : BT (Option BoundPool) := buildPoolsBT 5 rW rR rSlices rB8_15S
def rB8_15 : List NodeSpec := [([1,2,3,4,5,60,113,6,42],[5,19],[0,4]),([1,2,3,4,5,113,54,42,38],[0,4,5,19],[]),([1,2,3,4,5,113,6,132],[2,6,21],[]),([1,2,3,4,5,113,42,24,38],[5,6,28],[0]),([1,2,3,4,5,54,42,38],[3,6,18],[]),([1,2,3,4,113,40,42,38],[0,6,23,24],[]),([1,2,3,4,113,54,42,38],[0,5,6,22,24,26,27],[]),([1,2,3,4,113,116,42],[2,6,25],[]),([1,2,3,4,113,42,24,38],[5,6,29,30],[0]),([1,2,3,4,54,42,38],[3,6,18,20],[]),([1,2,3,115,113,6,42],[2,5,25],[]),([1,21,3,23,4,22,5,6,16],[10],[0]),([1,21,3,23,4,15,5,6,42],[12],[0,1]),([1,21,3,23,4,5,42,16],[11,13,14,15,16,17],[0,4]),([1,21,3,23,22,15,5,6],[1,7,8,9],[0,1]),([1,21,3,4,22,5,28,6,16],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB8_15Ok : checkNodesBT rW rG rMask rB8_15P rAutos rK7 8 rB8_15 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB8_15Mem : ∀ ns ∈ rB8_15, Impossible rG 8 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK7Ok rB8_15Ok
def rB8_16S : List PoolSpec := [(43,[]),(31,[]),(24,[]),(40,[]),(45,[]),(47,[]),(46,[]),(8,[]),(3,[(1,0,2),(1,0,4),(1,2,6),(1,22,6)]),(11,[(1,0,2),(1,0,4),(1,2,4)]),(25,[(1,0,2),(1,0,4),(1,2,4)]),(10,[(1,1,5)]),(25,[(1,0,2),(1,0,4)]),(23,[(1,1,5)]),(10,[]),(26,[(1,0,2),(1,0,4),(1,2,4)]),(10,[(1,5,6)]),(23,[]),(6,[(1,0,2),(1,0,4),(1,2,6),(1,22,6)]),(3,[(1,0,2),(1,0,6),(1,2,4),(1,15,6)]),(25,[(1,0,2),(1,0,6),(1,2,6)]),(25,[(1,0,2),(1,0,6)]),(5,[(1,0,2),(1,0,6),(1,2,6)]),(7,[(1,0,2),(1,1,5)]),(4,[(1,0,6),(1,1,5)]),(29,[]),(26,[(1,0,2),(1,0,6),(1,2,6)]),(18,[]),(26,[(1,0,2),(1,0,6)]),(6,[(1,0,2),(1,0,6),(1,2,4),(1,15,6)]),(25,[(1,0,2),(1,0,6),(1,40,6)]),(7,[(1,0,2),(1,5,42)]),(16,[]),(25,[(1,0,2),(1,0,6),(1,2,38)]),(26,[(1,0,2),(1,0,6),(1,2,38)]),(8,[(1,5,6)])]
def rB8_16P : BT (Option BoundPool) := buildPoolsBT 6 rW rR rSlices rB8_16S
def rB8_16 : List NodeSpec := [([1,21,3,4,15,5,28,6,42],[],[0,1]),([1,21,3,4,15,5,42,38],[4,5],[]),([1,21,3,4,5,60,6,42],[4,25],[0]),([1,21,3,4,5,28,42,16],[13,20,22,23,24],[0,4]),([1,21,3,4,5,52,6],[0,4,7],[0]),([1,21,3,4,5,40,42,38],[0,3,4,6,21],[]),([1,21,3,4,5,42,50,16],[2,4,26,27],[]),([1,21,3,4,5,42,16,57],[4,6,20,26,31],[]),([1,21,3,4,5,42,18],[4,5,7,19,29],[0,2]),([1,21,3,4,5,42,38,51],[3,6,32,33,34,35],[]),([1,21,3,4,5,42,51],[4,6,7,30],[]),([1,21,3,4,5,16,26],[1,4,8,18],[0,2]),([1,21,3,4,40,42,38],[3,6,21,28],[]),([1,21,3,22,15,5,28,6],[2,9,10,11],[0,1]),([1,21,3,22,15,5,6,38],[4,10,15,16],[]),([1,21,3,22,5,40,41,6],[0,4,12,14,17],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB8_16Ok : checkNodesBT rW rG rMask rB8_16P rAutos rK7 8 rB8_16 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB8_16Mem : ∀ ns ∈ rB8_16, Impossible rG 8 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK7Ok rB8_16Ok
def rB8_17S : List PoolSpec := [(31,[]),(13,[]),(45,[]),(47,[]),(8,[]),(3,[(1,0,2),(1,0,4),(1,2,4),(1,21,6)]),(3,[(1,0,2),(1,0,4),(1,2,4),(1,15,6)]),(3,[(1,0,2),(1,0,4),(1,2,6),(1,4,6)]),(25,[(1,0,2),(1,0,4),(1,2,4)]),(25,[(1,0,2),(1,0,4)]),(6,[(1,0,2),(1,0,4),(1,2,4),(1,21,6)]),(10,[(1,21,6)]),(10,[]),(6,[(1,0,2),(1,0,4),(1,2,4),(1,15,6)]),(6,[(1,0,2),(1,0,4),(1,2,6),(1,4,6)]),(3,[(1,0,2),(1,0,6),(1,2,4),(1,4,6)]),(6,[(1,0,2),(1,0,6),(1,2,4),(1,4,6)]),(48,[])]
def rB8_17P : BT (Option BoundPool) := buildPoolsBT 5 rW rR rSlices rB8_17S
def rB8_17 : List NodeSpec := [([1,21,3,22,5,37,6],[2,4,8,12],[]),([1,21,3,22,5,6,18],[2,3,6,13],[0,2]),([1,21,3,22,5,16,17],[2,7,14],[0,2]),([1,21,3,22,40,41,6],[0,2,9,12],[]),([1,21,3,15,5,42,17],[1,2,3,15,16],[0,2]),([1,3,4,113,124,6,42],[2,17],[]),([1,3,22,15,5,6,24],[2,5,10,11],[0,2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB8_17Ok : checkNodesBT rW rG rMask rB8_17P rAutos rK7 8 rB8_17 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB8_17Mem : ∀ ns ∈ rB8_17, Impossible rG 8 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK7Ok rB8_17Ok
def rNodes8 : List NodeSpec := rB8_0 ++ rB8_1 ++ rB8_2 ++ rB8_3 ++ rB8_4 ++ rB8_5 ++ rB8_6 ++ rB8_7 ++ rB8_8 ++ rB8_9 ++ rB8_10 ++ rB8_11 ++ rB8_12 ++ rB8_13 ++ rB8_14 ++ rB8_15 ++ rB8_16 ++ rB8_17
def rK8 : BT (List (List Nat)) := buildBucketsBT rW rNodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rK8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible rG 8 xs.toFinset) rK8 := buildBucketsBT_of_mem (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append rB8_0Mem rB8_1Mem) rB8_2Mem) rB8_3Mem) rB8_4Mem) rB8_5Mem) rB8_6Mem) rB8_7Mem) rB8_8Mem) rB8_9Mem) rB8_10Mem) rB8_11Mem) rB8_12Mem) rB8_13Mem) rB8_14Mem) rB8_15Mem) rB8_16Mem) rB8_17Mem)
def rB9_0S : List PoolSpec := [(31,[]),(40,[]),(45,[]),(26,[(1,2,4)]),(47,[]),(1,[(1,0,1),(2,7,6)]),(19,[]),(46,[]),(23,[(1,1,3)]),(23,[(1,1,5)]),(23,[(3,1,5)]),(10,[]),(23,[]),(7,[(1,0,2),(1,1,3)]),(25,[(1,0,2),(1,0,6)]),(7,[(1,0,2),(1,1,5)]),(7,[(1,0,2),(3,1,5)]),(4,[(1,0,6),(2,5,42)]),(3,[(1,0,2),(1,2,4),(2,21,6)]),(25,[(1,0,2),(2,21,6)]),(12,[(1,0,2),(2,21,6)]),(3,[(1,0,2),(2,21,6)]),(5,[(1,0,2),(2,21,6)]),(6,[(1,0,2),(1,2,4),(2,21,6)]),(10,[(2,21,6)]),(27,[]),(41,[]),(25,[(1,0,2),(2,21,38)]),(26,[(1,0,2),(2,21,38)]),(25,[(1,0,6)]),(48,[]),(25,[(1,0,6),(3,2,42)]),(42,[]),(25,[(1,0,6),(1,2,42)]),(7,[(3,1,5),(1,31,0)]),(1,[(3,1,5),(1,31,0),(2,157,6)]),(4,[(3,1,5),(1,31,0),(2,157,6)])]
def rB9_0P : BT (Option BoundPool) := buildPoolsBT 6 rW rR rSlices rB9_0S
def rB9_0 : List NodeSpec := [([108,0,1,2,3,4,5,6,38],[0,2,27,28],[0]),([58,122,0,1,2,3,4,6],[2,29],[0]),([58,46,0,1,2,3,4,5,6],[2,31],[0]),([58,0,1,2,3,4,15,5,6],[2,11,26],[]),([58,0,1,2,3,4,5,6,24],[2,7,25,33],[0]),([58,1,2,21,3,4,5,6,42],[1,7,14,17],[0]),([169,0,1,2,3,4,5,6],[7,32],[]),([220,0,1,2,3,4,5,6],[7,30],[]),([201,0,1,2,3,4,5,6],[0,2,30,34,35,36],[0]),([12,0,1,2,3,4,15,5,6],[2,3,4,5],[]),([149,0,1,2,3,4,5,6],[0,32],[]),([25,31,0,1,2,3,4,5,6],[0,2,6,10,16,19],[0]),([25,0,1,2,3,23,4,5,6],[6,8,13,19,20,21],[0]),([25,0,1,2,3,4,5,28,6],[6,9,15,19,22],[0]),([25,0,1,3,4,15,5,6],[2,18,23,24],[0,2]),([25,0,1,3,4,5,40,6],[7,12,19],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB9_0Ok : checkNodesBT rW rG rMask rB9_0P rAutos rK8 9 rB9_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB9_0Mem : ∀ ns ∈ rB9_0, Impossible rG 9 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK8Ok rB9_0Ok
def rB9_1S : List PoolSpec := [(43,[]),(31,[]),(13,[]),(45,[]),(47,[]),(46,[]),(3,[(1,0,2),(1,0,4),(2,21,6)]),(25,[(1,0,2),(1,0,4)]),(10,[(2,5,6)]),(6,[(1,0,2),(1,0,4),(2,21,6)]),(16,[]),(3,[(1,0,2),(1,21,4),(2,43,6)]),(25,[(1,0,2),(1,2,4)]),(25,[(1,0,2),(1,21,4)]),(25,[(1,0,2),(2,21,4)]),(25,[(1,0,2)]),(27,[]),(6,[(1,0,2),(1,21,4),(2,43,6)]),(34,[]),(41,[]),(4,[]),(48,[]),(25,[(1,2,4)]),(1,[(1,0,5),(2,5,6)]),(10,[(1,0,5),(2,113,6)]),(1,[(1,0,5),(2,113,6)]),(42,[])]
def rB9_1P : BT (Option BoundPool) := buildPoolsBT 5 rW rR rSlices rB9_1S
def rB9_1 : List NodeSpec := [([25,1,2,3,4,22,5,6],[1,3,6,9],[0,2]),([68,0,1,2,3,4,5,6],[3,4,11,17],[0,2,4,6]),([39,44,0,1,2,3,4,5,6],[3,5,14],[]),([39,91,0,1,2,3,4,6],[5,18],[]),([39,0,1,2,3,4,15,113,6],[3,4,22,23],[]),([39,0,1,2,3,4,43,5,6],[2,3,4,13],[0]),([39,0,1,2,3,4,113,54,6],[3,5,21,26],[]),([39,0,1,2,3,4,54,6],[5,15],[]),([39,0,1,21,3,4,15,5,6],[3,8,12],[0]),([39,0,1,21,3,4,40,6],[5,15],[]),([39,1,2,21,3,4,22,5,6],[1,2,3,7],[0]),([62,114,0,1,2,3,4,6],[5,18],[0]),([62,0,1,2,127,3,4,5,6],[5,20,21],[]),([62,0,1,2,3,4,15,5,113,6],[3,16,24,25],[0,4]),([62,0,1,2,3,4,15,5,6],[0,3,19,24,25],[0,4]),([62,0,1,2,3,4,5,40,6],[5,10,21],[4])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB9_1Ok : checkNodesBT rW rG rMask rB9_1P rAutos rK8 9 rB9_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB9_1Mem : ∀ ns ∈ rB9_1, Impossible rG 9 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK8Ok rB9_1Ok
def rB9_2S : List PoolSpec := [(43,[]),(31,[]),(26,[]),(13,[]),(45,[]),(47,[]),(46,[]),(8,[]),(23,[]),(25,[(1,0,2),(1,0,6)]),(29,[]),(16,[]),(25,[(1,0,2),(1,2,6)]),(25,[(1,0,2),(1,21,4)]),(25,[]),(25,[(1,0,2)]),(25,[(1,0,2),(2,54,6)]),(1,[(1,0,5),(1,0,6),(2,113,6)]),(7,[(1,0,5)]),(48,[]),(49,[]),(4,[(1,0,5),(1,0,6),(2,113,6)]),(1,[(1,0,5),(1,113,6),(2,113,6)]),(0,[(1,113,6)]),(42,[]),(4,[(1,0,5),(1,113,6),(2,113,6)]),(25,[(1,2,113),(2,54,6)]),(26,[(1,2,113),(2,54,6)]),(25,[(1,0,6),(3,40,42)])]
def rB9_2P : BT (Option BoundPool) := buildPoolsBT 5 rW rR rSlices rB9_2S
def rB9_2 : List NodeSpec := [([62,0,1,2,3,4,5,54,6],[6,11,19],[0]),([62,0,1,2,3,4,5,57],[19,22,23,25],[0,1]),([62,0,1,2,3,4,113,40,6],[6,14,19],[0]),([62,0,1,2,3,4,40,6],[6,19,20],[0]),([62,1,2,3,4,5,113,42],[7,17,18,19,21],[0,1]),([85,145,0,1,2,3,4,6],[6,24],[]),([85,0,1,2,3,4,5,113,6],[0,6,14],[4]),([85,0,1,2,3,4,113,6],[0,6,10,24],[]),([85,0,1,21,3,4,5,6],[0,6,8],[0]),([97,0,1,2,3,4,5,113,6],[6,8,10,24,26,27],[0]),([97,0,1,2,3,4,5,6],[2,6,8,16],[0]),([170,0,1,2,3,4,5,6],[2,4,28],[0]),([55,0,1,2,3,4,5,6,38],[1,3,4,15],[0]),([55,0,1,3,4,5,6,16],[1,4,12],[0]),([55,1,2,3,4,5,6,42],[1,3,4,9],[0]),([89,0,1,2,3,4,5,6],[1,2,5,13],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB9_2Ok : checkNodesBT rW rG rMask rB9_2P rAutos rK8 9 rB9_2 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB9_2Mem : ∀ ns ∈ rB9_2, Impossible rG 9 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK8Ok rB9_2Ok
def rB9_3S : List PoolSpec := [(31,[]),(26,[]),(40,[]),(45,[]),(8,[]),(10,[(3,1,5)]),(23,[(3,1,5)]),(29,[]),(7,[(1,0,2),(3,1,5),(2,21,4)]),(25,[(1,0,2),(1,21,6)]),(25,[]),(25,[(1,0,2),(2,21,4)]),(25,[(1,0,6)]),(48,[]),(26,[(1,0,6)]),(0,[(1,113,6)]),(25,[(1,113,6)]),(26,[(1,113,6)]),(25,[(2,94,4)]),(3,[(1,0,6),(1,2,4),(3,15,42)]),(6,[(1,0,6),(1,2,4),(3,15,42)]),(1,[(1,0,6),(3,15,42)]),(25,[(2,75,4)])]
def rB9_3P : BT (Option BoundPool) := buildPoolsBT 5 rW rR rSlices rB9_3S
def rB9_3 : List NodeSpec := [([122,0,1,2,3,4,5,113,6],[3,13,15],[]),([122,0,1,2,3,4,5,113,6,57],[2,3,7,15],[]),([122,0,1,2,3,4,5,6],[3,16],[]),([122,0,1,2,3,4,5,6,57],[2,3,7,16],[]),([122,0,1,2,3,4,113,6],[3,13,16,17],[]),([122,0,1,2,3,4,113,6,57],[3,7,16,17],[0]),([122,0,1,2,3,4,6,57],[3,16,17],[0,4]),([122,1,2,3,4,5,113,6,42],[3,7,12],[0]),([122,1,2,3,4,113,6,42],[3,4,12,14],[0]),([102,0,1,2,3,4,5,6],[0,1,3,9],[]),([130,0,1,2,3,4,5,6],[3,13],[]),([155,0,1,2,3,4,5,6],[1,3,10,19,20,21],[0,2]),([219,0,1,2,3,4,5,6],[3,13],[]),([204,0,1,2,3,4,5,6],[3,22],[]),([147,0,1,2,3,4,5,6],[3,18],[]),([44,31,0,1,2,3,4,5,6],[0,3,5,6,8,11],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB9_3Ok : checkNodesBT rW rG rMask rB9_3P rAutos rK8 9 rB9_3 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB9_3Mem : ∀ ns ∈ rB9_3, Impossible rG 9 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK8Ok rB9_3Ok
def rB9_4S : List PoolSpec := [(43,[]),(31,[]),(26,[]),(35,[]),(45,[]),(46,[]),(44,[]),(23,[(1,1,3)]),(10,[(1,1,5)]),(23,[(1,1,5)]),(10,[]),(23,[]),(7,[(1,0,2),(1,1,3),(2,21,4)]),(3,[(1,0,2),(1,0,6),(2,21,4)]),(7,[(1,0,2),(1,1,5),(2,21,4)]),(6,[(1,0,2),(1,0,6),(2,21,4)]),(7,[(1,0,2),(2,21,4)]),(3,[(1,0,2),(1,2,6),(2,21,4)]),(9,[(1,0,2),(2,21,4)]),(3,[(1,0,2),(2,21,4)]),(25,[]),(11,[(1,0,2),(2,21,4)]),(25,[(1,0,2),(2,21,4)]),(25,[(1,0,2)]),(6,[(1,0,2),(1,2,6),(2,21,4)]),(26,[(1,0,2),(2,21,4)]),(34,[]),(4,[]),(48,[]),(42,[]),(9,[(3,4,40)])]
def rB9_4P : BT (Option BoundPool) := buildPoolsBT 5 rW rR rSlices rB9_4S
def rB9_4 : List NodeSpec := [([44,0,1,2,3,23,4,5,6],[6,7,12,18,19],[0]),([44,0,1,2,3,4,5,28,6],[8,9,14,21,22],[0]),([44,0,1,2,3,4,5,6,38],[4,5,22,25],[0]),([44,0,1,2,3,5,41,6],[2,4,10,22],[]),([44,0,1,3,4,5,6,16],[1,4,16,17,24],[0,2]),([44,1,2,3,4,5,6,42],[1,4,13,15,16],[0,2]),([83,82,0,1,2,3,4,6],[4,29],[]),([83,0,1,2,3,4,54,6],[1,4,23],[]),([83,0,1,21,3,4,40,6],[0,1,4,11],[]),([118,114,0,1,2,3,4,6],[5,26],[]),([118,0,1,2,3,4,5,40,6],[4,5,10,28],[]),([118,0,1,2,3,4,5,54,6],[4,5,10,28],[]),([118,0,1,2,3,4,113,40,6],[3,4,11,28],[]),([118,0,1,2,3,4,40,6],[3,4,27,28],[]),([84,145,0,1,2,3,4,6],[4,30],[]),([84,0,1,2,3,4,5,113,6],[0,4,5,20],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB9_4Ok : checkNodesBT rW rG rMask rB9_4P rAutos rK8 9 rB9_4 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB9_4Mem : ∀ ns ∈ rB9_4, Impossible rG 9 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK8Ok rB9_4Ok
def rB9_5S : List PoolSpec := [(43,[]),(31,[]),(40,[]),(35,[]),(45,[]),(46,[]),(26,[(1,2,6),(3,4,16)]),(8,[]),(10,[(1,1,5),(3,3,28)]),(23,[(1,1,5),(3,3,28)]),(10,[]),(21,[]),(3,[(1,0,2),(1,0,6),(3,4,42)]),(7,[(1,0,2),(1,1,5),(3,3,28)]),(4,[(1,0,6),(1,1,5),(3,3,28)]),(6,[(1,0,2),(1,0,6),(3,4,42)]),(4,[(1,0,6),(3,4,42)]),(26,[(1,0,2)]),(3,[(1,0,2),(1,21,6),(3,4,24)]),(8,[(1,1,5),(1,2,4),(3,3,28)]),(25,[]),(8,[(1,1,5),(3,3,28)]),(4,[(1,1,5),(3,3,28)]),(25,[(1,0,2),(3,4,54)]),(6,[(1,0,2),(1,21,6),(3,4,24)]),(7,[(1,0,2),(3,4,24)]),(8,[(1,21,6),(3,4,24)]),(41,[]),(25,[(1,0,6)]),(25,[(1,2,4)]),(42,[]),(25,[(1,2,113),(3,4,54)]),(26,[(1,2,113),(3,4,54)]),(3,[(1,0,6),(1,2,42),(3,4,24)]),(7,[(1,1,5),(3,3,28)]),(1,[(1,0,6),(1,1,5),(3,3,28)]),(6,[(1,0,6),(1,2,42),(3,4,24)]),(7,[(1,2,42),(3,4,24)]),(7,[(1,1,5),(1,2,4),(3,3,28)])]
def rB9_5P : BT (Option BoundPool) := buildPoolsBT 6 rW rR rSlices rB9_5S
def rB9_5 : List NodeSpec := [([84,0,1,2,3,4,113,6],[0,4,11,20,30],[]),([84,0,1,21,3,4,5,6],[0,4,7,10],[]),([96,0,1,2,3,4,5,113,6],[3,4,31,32],[]),([96,0,1,2,3,4,5,6],[1,4,23],[]),([45,1,2,21,3,4,5,6],[1,4,12,15,16],[0,2]),([20,0,1,7,2,3,4,5,6],[4,5,6],[]),([67,0,1,2,21,3,5,6],[1,4,18,24],[0,2]),([67,0,1,2,3,4,5,6],[1,4,18,24],[0,2]),([67,0,1,2,3,5,6],[1,4,18,24,25,26],[0,2]),([67,0,1,2,3,5,6,42],[4,33,36,37],[0,2,4]),([67,0,1,2,3,5,6,24],[1,4,10,18,24],[0,2]),([30,0,1,2,21,4,5,6],[8,9,13,17,21,22],[0]),([30,0,1,2,4,15,5,6],[8,19,22,29,38],[0,1,4,5]),([30,0,1,2,4,5,6,42],[14,21,28,34,35],[0,1,4,5]),([105,0,1,2,3,4,5,6],[4,20,27],[]),([109,0,1,2,3,4,5,6],[2,3],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB9_5Ok : checkNodesBT rW rG rMask rB9_5P rAutos rK8 9 rB9_5 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB9_5Mem : ∀ ns ∈ rB9_5, Impossible rG 9 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK8Ok rB9_5Ok
def rB9_6S : List PoolSpec := [(31,[]),(26,[]),(13,[]),(40,[]),(45,[]),(47,[]),(46,[]),(6,[]),(23,[]),(29,[]),(16,[]),(27,[]),(34,[]),(48,[]),(4,[(1,0,5),(1,0,6)]),(8,[(3,2,113),(1,5,6)]),(49,[]),(25,[(3,2,113)]),(25,[(1,113,6)]),(25,[(3,2,41)])]
def rB9_6P : BT (Option BoundPool) := buildPoolsBT 5 rW rR rSlices rB9_6S
def rB9_6 : List NodeSpec := [([199,0,1,2,3,4,5,6],[0,13],[]),([114,0,1,2,3,4,113,117,6],[4,5,11,13],[]),([114,0,1,2,3,4,113,6,57],[3,4,6,13],[0]),([114,0,1,2,3,4,6,57],[3,4,6,9,18],[0]),([114,1,2,3,4,113,6,42],[1,6,8,13],[0]),([91,0,1,2,3,4,5,6,38],[0,10,13,15],[0]),([91,0,1,2,3,4,5,6,57],[4,6,13],[0]),([91,0,1,2,3,4,113,6,38],[3,6,13,15],[0]),([91,0,1,2,3,4,6,38],[6,10,13,16],[0]),([91,0,1,21,3,4,5,6],[6,7,12],[]),([91,0,1,3,4,5,40,6],[6,17],[]),([91,0,1,3,4,5,54,6],[6,7,12],[]),([91,0,1,3,4,113,40,6],[6,13],[]),([91,1,2,3,4,5,113,6,42],[6,13],[0]),([91,1,2,3,4,5,6,42],[2,6,13,14],[0]),([207,0,1,3,4,5,40,6],[6,19],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB9_6Ok : checkNodesBT rW rG rMask rB9_6P rAutos rK8 9 rB9_6 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB9_6Mem : ∀ ns ∈ rB9_6, Impossible rG 9 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK8Ok rB9_6Ok
def rB9_7S : List PoolSpec := [(24,[]),(40,[]),(35,[]),(45,[]),(46,[]),(6,[]),(30,[]),(10,[]),(4,[(1,0,6),(1,1,3)]),(4,[(1,0,6),(1,1,5)]),(29,[]),(4,[(1,0,6),(3,1,5)]),(20,[]),(3,[(1,0,2),(1,21,6),(3,2,24)]),(6,[(1,0,2),(1,21,6),(3,2,24)]),(41,[]),(32,[]),(0,[(1,0,6),(3,2,42)]),(25,[(1,0,6),(3,2,42)]),(11,[(1,0,6),(3,2,42)]),(42,[]),(33,[]),(3,[(1,0,6),(3,2,42)]),(7,[(1,1,3),(3,2,42)]),(12,[(1,0,6),(3,2,42)]),(1,[(1,0,6),(1,1,3),(3,2,42)]),(8,[(1,1,3),(3,2,42)]),(7,[(1,1,5),(3,2,42)]),(1,[(1,0,6),(1,1,5),(3,2,42)]),(8,[(1,1,5),(3,2,42)]),(7,[(3,1,5),(3,2,42)]),(1,[(1,0,6),(3,1,5),(3,2,42)]),(8,[(3,1,5),(3,2,42)]),(26,[(1,0,6),(3,2,42)]),(4,[(1,0,6),(1,5,42)])]
def rB9_7P : BT (Option BoundPool) := buildPoolsBT 6 rW rR rSlices rB9_7S
def rB9_7 : List NodeSpec := [([207,0,1,3,4,5,37,6],[3,7,16],[]),([207,0,1,3,4,40,41,6],[4,7,15],[]),([151,0,1,2,3,4,5,6],[1,2],[]),([46,31,0,1,2,3,4,5,6],[2,3,11,18,30,31,32],[0,1,5]),([46,31,0,1,2,3,4,5,6,42],[3,10,11,17,30],[0,4]),([46,0,1,176,2,3,4,5,6],[3,5,33],[]),([46,0,1,178,2,3,4,5,6],[3,18],[0]),([46,0,1,2,3,23,4,5,6],[8,18,22,23,24,25,26],[0,1,5]),([46,0,1,2,3,23,4,5,6,42],[3,6,8,19,21,22,23,24],[0,4]),([46,0,1,2,3,4,5,60,6],[3,18,33],[0]),([46,0,1,2,3,4,5,28,6],[9,18,19,27,28,29],[0,1,5]),([46,0,1,2,3,4,5,28,6,42],[0,9,18,19,27],[0,4]),([46,0,1,2,3,4,5,6,50],[3,12,33],[]),([46,0,1,2,3,4,5,6,57],[3,18,20,33,34],[0,4]),([46,0,1,21,3,4,5,6],[3,5,13,14],[0,2]),([46,0,1,3,4,5,6,24],[3,5,13,14],[0,2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB9_7Ok : checkNodesBT rW rG rMask rB9_7P rAutos rK8 9 rB9_7 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB9_7Mem : ∀ ns ∈ rB9_7, Impossible rG 9 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK8Ok rB9_7Ok
def rB9_8S : List PoolSpec := [(31,[]),(24,[]),(26,[]),(35,[]),(45,[]),(47,[]),(19,[]),(46,[]),(8,[]),(25,[(1,0,2),(1,0,4)]),(10,[(3,1,5)]),(21,[(3,1,5)]),(23,[(3,1,5)]),(3,[(1,0,2),(1,0,6),(3,2,42)]),(4,[(1,0,6),(3,1,5)]),(7,[(1,0,2),(3,1,5)]),(18,[]),(6,[(1,0,2),(1,0,6),(3,2,42)]),(20,[]),(25,[(1,0,2),(1,2,6)]),(25,[(1,0,2),(1,21,6)]),(25,[(1,0,2),(1,2,4)]),(25,[(1,0,2),(1,21,4)]),(8,[(3,1,5),(1,2,4)]),(8,[(3,1,5),(1,2,6)]),(16,[(3,1,5)]),(8,[(3,1,5),(1,21,4)]),(8,[(3,1,5),(1,21,6)]),(4,[(3,1,5),(1,21,6)]),(27,[]),(7,[(1,0,5)]),(49,[]),(0,[(1,0,6),(1,2,42)]),(25,[(1,0,6),(3,2,42)]),(11,[(1,0,6),(3,2,42)]),(4,[(1,0,5),(1,113,6)]),(25,[(1,113,6),(3,2,57)]),(26,[(1,113,6),(3,2,57)]),(10,[(1,0,6),(3,1,5)]),(1,[(1,0,6),(3,1,5)]),(7,[(3,1,5),(1,2,42)])]
def rB9_8P : BT (Option BoundPool) := buildPoolsBT 6 rW rR rSlices rB9_8S
def rB9_8 : List NodeSpec := [([46,1,2,3,4,5,113,6,42],[4,30,31,33,34],[0,4]),([46,1,21,3,4,5,6,42],[4,8,13,17],[0,2]),([139,0,1,2,3,4,5,113,6],[7,35,36,37],[]),([139,0,1,2,3,4,5,113,6,57],[7,35],[0]),([139,0,1,2,3,4,5,6],[2,7,35,36],[]),([139,0,1,2,3,4,5,6,57],[7,35,36,37],[0,4]),([31,0,1,2,21,3,4,43,5,6],[0,5,10,11,12],[]),([31,0,1,2,21,3,4,5,6,24],[0,4,10,12,25],[0]),([31,0,1,2,21,3,4,5,6,17],[0,4,6,12,16],[0,1,4,5]),([31,0,1,2,3,4,15,5,6,42],[4,14,16,23,29,38],[0,1,4,5]),([31,0,1,2,3,4,43,5,6],[4,5,10,11,12,16,22,26],[0,4,5]),([31,0,1,2,3,4,5,6,42,24],[0,4,12,14,25,32,39,40],[0,4]),([31,0,1,2,3,4,5,6,24],[0,4,6,12,15,20,25,27,28],[0,4]),([31,0,1,21,3,4,15,5,6],[0,10,12,21,23],[0]),([31,0,1,21,3,4,5,6,16],[0,4,12,15,18,19,24,25],[0,4]),([31,1,2,21,3,4,22,5,6],[1,3,4,9,10,11,12],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB9_8Ok : checkNodesBT rW rG rMask rB9_8P rAutos rK8 9 rB9_8 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB9_8Mem : ∀ ns ∈ rB9_8, Impossible rG 9 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK8Ok rB9_8Ok
def rB9_9S : List PoolSpec := [(43,[]),(24,[]),(26,[]),(40,[]),(35,[]),(45,[]),(46,[]),(8,[]),(6,[]),(23,[(3,1,5)]),(10,[]),(23,[]),(21,[]),(25,[(1,0,2),(1,0,6)]),(29,[]),(4,[(1,0,6),(3,1,5)]),(7,[(1,0,2),(3,1,5)]),(8,[(1,5,6)]),(4,[]),(32,[]),(25,[(1,2,4),(3,0,37)]),(25,[(1,2,4)]),(1,[(1,0,5),(1,5,6),(3,0,38)]),(42,[]),(4,[(1,0,5),(1,113,6),(3,0,57)]),(4,[(1,0,5),(1,5,6),(3,0,38)]),(1,[(1,0,5),(1,113,6),(3,0,57)]),(8,[(1,113,6)]),(1,[(3,0,5),(1,15,5)]),(25,[(3,0,115)])]
def rB9_9P : BT (Option BoundPool) := buildPoolsBT 5 rW rR rSlices rB9_9S
def rB9_9 : List NodeSpec := [([31,1,2,21,3,4,5,6,42],[1,5,6,9,13,15,16],[0,1]),([202,0,1,2,3,4,5,6],[4,23],[]),([221,0,1,2,3,4,5,6],[5,29],[]),([221,0,1,2,3,115,5,6],[5,19],[]),([145,0,1,2,3,4,37,6],[5,21,28],[]),([82,0,1,2,3,4,5,41,6],[5,12,23],[0]),([82,0,1,2,3,4,41,6],[4,5,23],[]),([82,1,2,21,3,4,5,6],[0,6,8],[]),([82,1,2,3,4,5,113,54,6],[6,11,14,23],[]),([82,1,2,3,4,5,113,6],[0,6,14,18],[0,4]),([82,1,2,3,4,5,54,6],[0,6,8],[]),([82,1,2,3,4,113,40,6],[0,6],[]),([82,1,21,3,4,5,40,6],[0,6,7],[]),([129,0,1,2,3,4,5,6],[2,5,10,20],[0]),([131,1,2,3,4,5,113,6],[3,14,17,22,25],[0,1]),([131,1,2,3,4,5,113,6,57],[3,14,24,26,27],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB9_9Ok : checkNodesBT rW rG rMask rB9_9P rAutos rK8 9 rB9_9 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB9_9Mem : ∀ ns ∈ rB9_9, Impossible rG 9 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK8Ok rB9_9Ok
def rB9_10S : List PoolSpec := [(31,[]),(24,[]),(40,[]),(35,[]),(45,[]),(26,[(1,2,4),(1,2,6)]),(19,[]),(26,[(1,2,4),(1,15,6)]),(26,[(1,2,6),(1,4,6)]),(46,[]),(23,[]),(29,[]),(8,[(1,5,6)]),(8,[(1,5,42)]),(25,[]),(8,[(3,1,5),(1,2,4)]),(25,[(1,0,6)]),(48,[]),(32,[]),(25,[(1,2,4)]),(1,[(1,0,5),(1,5,6),(3,0,38)]),(42,[]),(4,[(1,0,5),(1,5,6),(3,0,38)]),(7,[(3,1,5),(1,31,0)]),(1,[(1,0,6),(1,5,42),(3,0,57)]),(4,[(1,0,6),(1,5,42),(3,0,57)]),(10,[(3,1,5),(1,31,0)]),(4,[(3,1,5),(1,31,0),(1,157,6)]),(7,[(3,1,5),(1,31,0),(1,157,2)]),(4,[(3,1,5),(1,31,0)]),(1,[(3,1,5),(1,31,0),(1,157,6)]),(10,[(1,83,0)])]
def rB9_10P : BT (Option BoundPool) := buildPoolsBT 5 rW rR rSlices rB9_10S
def rB9_10 : List NodeSpec := [([131,1,2,3,4,5,6,42],[2,4,9,13],[4,5]),([131,1,2,3,4,5,6,42,57],[2,4,9,13,24,25],[0,1,4,5]),([131,1,2,3,4,113,6,38],[2,12,14,20,22],[0,1,4,5]),([0,192,1,2,3,4,5,6],[4,18],[]),([0,213,1,2,3,4,40,6],[9,14,31],[]),([0,215,1,2,3,4,5,6],[0,4,21],[]),([0,157,1,2,76,3,4,5,6],[17,21,26,28,29],[0,4]),([0,157,1,2,3,4,15,5,6],[0,2,11,15,19,26,29],[0,4,5]),([0,157,1,2,3,4,5,6,48],[2,17,23,26,27,30],[0,1,4,5]),([0,1,163,2,3,4,5,6],[4,16],[]),([0,1,7,2,3,4,5,6,18],[1,4,7],[0]),([0,1,7,2,3,4,5,16,17],[4,6,8],[0]),([0,1,7,3,4,15,5,6,16],[4,5,6],[0]),([0,1,2,13,3,4,5,6],[2,3],[]),([0,1,2,110,3,4,113,6],[9,11,14],[]),([0,1,2,127,3,4,5,113,6],[9,10,17,21],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB9_10Ok : checkNodesBT rW rG rMask rB9_10P rAutos rK8 9 rB9_10 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB9_10Mem : ∀ ns ∈ rB9_10, Impossible rG 9 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK8Ok rB9_10Ok
def rB9_11S : List PoolSpec := [(31,[]),(26,[]),(40,[]),(45,[]),(26,[(1,2,4)]),(47,[]),(19,[]),(46,[]),(44,[]),(21,[(1,1,3)]),(23,[(1,1,3)]),(10,[(1,1,5)]),(21,[(1,1,5)]),(23,[(1,1,5)]),(10,[(3,1,5),(1,31,6)]),(10,[]),(23,[]),(7,[(1,0,2),(3,1,5)]),(18,[]),(16,[(1,1,3)]),(2,[(1,0,2),(1,21,4)]),(3,[(1,0,2),(1,21,4)]),(3,[(1,0,2),(1,21,6)]),(2,[(1,0,2),(1,4,6)]),(3,[(1,0,2),(1,4,6)]),(8,[(1,1,5),(1,2,4),(0,3,28)]),(16,[(1,1,5)]),(25,[]),(25,[(1,0,2)]),(4,[(3,1,5),(1,31,6)]),(8,[(3,1,5),(1,31,6)]),(25,[(1,0,6)]),(48,[]),(1,[(3,0,5),(1,145,2)]),(25,[(1,0,6),(1,122,2)]),(7,[(1,1,5),(1,2,4),(0,3,28)]),(15,[])]
def rB9_11P : BT (Option BoundPool) := buildPoolsBT 6 rW rR rSlices rB9_11S
def rB9_11 : List NodeSpec := [([0,1,2,127,3,4,5,6],[1,7,16,32],[]),([0,1,2,172,3,4,5,6],[3,31],[]),([0,1,2,184,3,4,5,6],[0,3,15,34],[0]),([0,1,2,94,3,4,41,6],[3,27,33],[]),([0,1,2,21,3,23,4,43,5,6],[8,9,10,20,21],[]),([0,1,2,21,3,23,4,5,6,24],[0,3,8,10,19,22],[0]),([0,1,2,21,3,23,4,5,6,17],[8,10,18,23,24],[0,1,4,5]),([0,1,2,21,3,4,43,5,28,6],[0,5,11,12,13],[0]),([0,1,2,21,3,4,5,28,6,24],[0,3,11,13,26],[0]),([0,1,2,21,3,4,5,28,6,17],[0,3,6,13,18],[0,1,4,5]),([0,1,2,21,3,4,5,6,32],[0,2,3,14,17,28,29,30],[0]),([0,1,2,21,3,95,5,6],[3,28],[]),([0,1,2,111,3,4,5,6],[7,28],[]),([0,1,2,107,3,4,5,6],[3,28],[]),([0,1,2,76,3,4,5,6],[7,28],[]),([0,1,2,29,4,15,5,6],[4,8,25,35,36],[0,1,4,5])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB9_11Ok : checkNodesBT rW rG rMask rB9_11P rAutos rK8 9 rB9_11 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB9_11Mem : ∀ ns ∈ rB9_11, Impossible rG 9 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK8Ok rB9_11Ok
def rB9_12S : List PoolSpec := [(43,[]),(31,[]),(26,[]),(35,[]),(45,[]),(47,[]),(19,[]),(46,[]),(44,[]),(21,[(1,1,3)]),(23,[(1,1,3)]),(10,[]),(7,[(1,0,2),(1,1,3)]),(4,[(1,0,6),(1,1,3)]),(18,[]),(8,[(1,1,3),(1,2,4)]),(16,[(1,1,3)]),(3,[(1,0,2),(1,21,4)]),(9,[(1,0,2),(1,21,4)]),(8,[(1,1,3),(1,21,4)]),(3,[(1,0,2),(1,21,6)]),(3,[(1,0,2),(1,21,6),(0,4,24)]),(25,[(1,0,2),(1,21,6)]),(12,[(1,0,2),(1,21,6)]),(4,[(1,1,3),(1,21,6)]),(8,[(1,1,3),(1,21,6)]),(3,[(1,0,2),(2,21,6),(1,25,4)]),(25,[]),(25,[(1,0,2),(1,55,4)]),(6,[(1,0,2),(1,21,6),(0,4,24)]),(6,[(1,0,2),(2,21,6),(1,25,4)]),(48,[]),(9,[(1,0,6),(1,2,42)]),(25,[(1,2,4)]),(1,[(1,0,5),(1,5,6)]),(1,[(1,0,5),(1,113,6)]),(42,[]),(2,[(1,0,6),(1,2,4)]),(33,[]),(3,[(1,0,6),(1,2,4)]),(1,[(1,0,6),(1,1,3)]),(3,[(1,0,6),(1,2,42)]),(7,[(1,1,3),(1,2,42)]),(12,[(1,0,6),(1,2,42)]),(3,[(1,0,6),(3,2,42),(1,46,4)]),(6,[(1,0,6),(3,2,42),(1,46,4)]),(1,[(1,0,6),(3,2,42)])]
def rB9_12P : BT (Option BoundPool) := buildPoolsBT 6 rW rR rSlices rB9_12S
def rB9_12 : List NodeSpec := [([0,1,2,3,23,4,15,5,6,42],[8,13,15,37,38,39],[0,1,4,5]),([0,1,2,3,23,4,43,5,6],[8,9,10,14,17,18,19],[0,4,5]),([0,1,2,3,23,4,5,6,42,24],[1,4,10,13,16,32,40,41,42,43],[0]),([0,1,2,3,23,4,5,6,24],[6,10,12,16,20,22,23,24,25],[0,4]),([0,1,2,3,70,5,6,24],[1,4,21,29],[0,1,2]),([0,1,2,3,4,71,5,6],[4,5,26,30],[0,2]),([0,1,2,3,4,100,5,6],[4,5,11,28],[]),([0,1,2,3,4,9,5,6],[0,1],[]),([0,1,2,3,4,115,113,6],[3,4,27],[]),([0,1,2,3,4,134,5,113,6],[4,7,31],[]),([0,1,2,3,4,134,5,6],[1,4,31],[]),([0,1,2,3,4,156,5,6],[1,4,44,45,46],[0,2]),([0,1,2,3,4,189,5,6],[4,8],[]),([0,1,2,3,4,210,5,6],[2,4,11,36],[]),([0,1,2,3,4,15,5,113,6,38],[4,5,33,34],[0,4]),([0,1,2,3,4,15,5,113,6,57],[4,5,35],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB9_12Ok : checkNodesBT rW rG rMask rB9_12P rAutos rK8 9 rB9_12 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB9_12Mem : ∀ ns ∈ rB9_12, Impossible rG 9 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK8Ok rB9_12Ok
def rB9_13S : List PoolSpec := [(43,[]),(31,[]),(26,[]),(40,[]),(35,[]),(45,[]),(26,[(1,2,4)]),(47,[]),(46,[]),(10,[(1,1,5)]),(21,[(1,1,5)]),(23,[(1,1,5)]),(10,[]),(23,[]),(4,[(1,0,6),(1,1,5)]),(29,[]),(18,[]),(25,[(1,0,2),(2,21,6)]),(8,[(1,1,5),(1,2,4)]),(11,[(1,0,2),(1,21,4)]),(25,[(1,0,2),(1,21,4)]),(8,[(1,1,5),(1,21,4)]),(25,[(1,0,2),(2,21,4)]),(27,[]),(26,[(1,0,2),(1,21,4)]),(41,[]),(25,[(1,0,6)]),(32,[]),(25,[(1,0,6),(3,2,42)]),(25,[(1,2,4)]),(1,[(1,0,5),(1,5,6)]),(1,[(1,0,5),(1,113,6)]),(0,[(1,4,113)]),(4,[(1,0,5),(1,113,6)]),(0,[(1,113,6)]),(25,[(1,94,4)]),(1,[(3,0,5),(1,145,2)]),(1,[(3,0,5),(1,145,6)]),(10,[(1,0,6),(1,1,5)]),(26,[(1,0,6),(3,2,42)]),(4,[(1,0,6),(1,46,5)]),(7,[(3,2,42),(1,46,5)]),(8,[(3,2,42),(1,46,5)]),(1,[(1,0,6),(3,2,42),(1,46,5)]),(25,[(1,75,4)]),(1,[(3,1,5),(1,31,2)])]
def rB9_13P : BT (Option BoundPool) := buildPoolsBT 6 rW rR rSlices rB9_13S
def rB9_13 : List NodeSpec := [([0,1,2,3,4,15,5,28,6,42],[5,14,16,18,25,27,38],[0,1,4,5]),([0,1,2,3,4,15,5,6,63],[5,7,29,37],[]),([0,1,2,3,4,15,5,6,50],[0,5,12],[]),([0,1,2,3,4,15,5,6,57],[0,5,7,25,31],[0,4]),([0,1,2,3,4,15,113,6,38],[5,6,7,29,30],[0,4]),([0,1,2,3,4,203,5,6],[5,44,45],[]),([0,1,2,3,4,146,5,6],[5,35,36],[]),([0,1,2,3,4,43,5,28,6],[9,10,11,16,19,20,21],[0,4,5]),([0,1,2,3,4,43,5,6,38],[5,7,20,24],[0]),([0,1,2,3,4,123,6,57],[3,5,15,26],[0,1]),([0,1,2,3,4,5,103,6],[2,8,13,17],[]),([0,1,2,3,4,5,90,6],[2,8,13,22],[]),([0,1,2,3,4,5,60,6],[1,5,28,39,40,41,42,43],[]),([0,1,2,3,4,5,60,6,42],[3,5,15,28,39,40,41],[0,4]),([0,1,2,3,4,5,113,40,117,6],[4,5,13,23,32],[0]),([0,1,2,3,4,5,113,40,6,57],[3,8,15,33,34],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB9_13Ok : checkNodesBT rW rG rMask rB9_13P rAutos rK8 9 rB9_13 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB9_13Mem : ∀ ns ∈ rB9_13, Impossible rG 9 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK8Ok rB9_13Ok
def rB9_14S : List PoolSpec := [(31,[]),(26,[]),(13,[]),(40,[]),(35,[]),(45,[]),(26,[(1,2,4)]),(47,[]),(19,[]),(46,[]),(8,[]),(22,[]),(23,[(1,1,5)]),(10,[]),(7,[(1,0,2),(1,1,5)]),(4,[(1,0,6),(1,1,5)]),(29,[]),(25,[(1,0,2),(1,21,6)]),(16,[(1,1,5)]),(25,[]),(5,[(1,0,2),(1,21,6)]),(4,[(1,1,5),(1,21,6)]),(8,[(1,1,5),(1,21,6)]),(25,[(1,0,2)]),(7,[(1,0,5)]),(48,[]),(49,[]),(11,[(1,0,6),(1,2,42)]),(10,[(1,0,5)]),(1,[(1,0,5),(1,15,5)]),(25,[(1,2,4),(1,15,113)]),(26,[(1,2,4),(1,15,113)]),(1,[(1,0,5),(1,113,6)]),(4,[(1,0,5),(1,113,6)]),(25,[(1,113,6)]),(42,[]),(0,[(1,2,113),(1,4,113)]),(25,[(1,2,113),(1,4,113)]),(26,[(1,2,113),(1,4,113)]),(0,[(1,2,113)]),(0,[(1,2,113),(1,113,6)]),(25,[(1,2,113),(1,113,6)]),(11,[(1,2,113),(1,113,6)]),(4,[(1,0,5),(1,91,6)]),(25,[(1,0,6),(1,2,42)]),(1,[(1,0,6),(1,1,5)]),(7,[(1,1,5),(1,2,42)]),(7,[])]
def rB9_14P : BT (Option BoundPool) := buildPoolsBT 6 rW rR rSlices rB9_14S
def rB9_14 : List NodeSpec := [([0,1,2,3,4,5,113,54,117,6],[4,5,28,36],[0,1]),([0,1,2,3,4,5,113,54,6,38],[3,5,9,16,35,39],[0]),([0,1,2,3,4,5,113,54,6,57],[5,9,16,24,33,40],[0]),([0,1,2,3,4,5,113,37,6],[5,6,10,28,29],[0]),([0,1,2,3,4,5,113,87,6],[5,7,24,30,31],[0]),([0,1,2,3,4,5,113,6,135],[9,25,43],[]),([0,1,2,3,4,5,113,6,57,98],[5,9,32,33],[0]),([0,1,2,3,4,5,28,6,42,24],[12,15,18,27,44,45,46],[0]),([0,1,2,3,4,5,28,6,24],[8,12,14,17,18,20,21,22],[0,4]),([0,1,2,3,4,5,52,6],[1,5,11,13,19,35,47],[0,4]),([0,1,2,3,4,5,40,6,57],[3,9,16,33,34],[]),([0,1,2,3,4,5,54,41,6],[0,5,13,23],[]),([0,1,2,3,4,5,54,117,6],[4,5,28,37,38],[]),([0,1,2,3,4,5,54,6],[9,23],[]),([0,1,2,3,4,5,54,6,38],[2,5,9,23],[0]),([0,1,2,3,4,5,54,6,57],[5,9,24,26,33,41,42],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB9_14Ok : checkNodesBT rW rG rMask rB9_14P rAutos rK8 9 rB9_14 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB9_14Mem : ∀ ns ∈ rB9_14, Impossible rG 9 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK8Ok rB9_14Ok
def rB9_15S : List PoolSpec := [(43,[]),(31,[]),(26,[]),(13,[]),(40,[]),(45,[]),(47,[]),(46,[]),(29,[]),(16,[]),(7,[(1,0,2),(2,21,4)]),(3,[(1,0,2),(1,21,4),(1,43,6)]),(3,[(1,0,2),(2,21,4),(1,44,6)]),(25,[(1,0,2),(1,21,4)]),(6,[(1,0,2),(1,21,4),(1,43,6)]),(6,[(1,0,2),(2,21,4),(1,44,6)]),(25,[(1,0,2),(1,55,6)]),(25,[(1,0,2),(1,21,38)]),(26,[(1,0,2),(1,21,38)]),(25,[(1,0,6)]),(48,[]),(49,[]),(32,[]),(9,[(1,0,6),(1,2,42)]),(11,[(1,0,6),(1,2,42)]),(42,[]),(4,[(1,0,5),(1,91,6)]),(12,[(1,0,6),(1,2,42)]),(4,[(1,0,6),(3,1,5),(1,31,42)]),(1,[(1,0,6),(3,1,5),(1,31,42)]),(7,[(3,1,5),(1,31,42)]),(8,[(3,1,5),(1,31,42)]),(26,[(1,0,6),(1,2,42)]),(7,[(2,5,42),(1,58,42)])]
def rB9_15P : BT (Option BoundPool) := buildPoolsBT 6 rW rR rSlices rB9_15S
def rB9_15 : List NodeSpec := [([0,1,2,3,4,5,87,6],[2,3,5,6,13],[0]),([0,1,2,3,4,5,6,101],[1,2,5,16],[0]),([0,1,2,3,4,5,6,69],[1,5,10,12,15],[0,2]),([0,1,2,3,4,5,6,10],[0,1],[]),([0,1,2,3,4,5,6,135],[2,7,20,26],[]),([0,1,2,3,4,5,6,190],[7,21],[]),([0,1,2,3,4,5,6,63,148],[4,7,25],[]),([0,1,2,3,4,5,6,132],[2,7,9,25],[0]),([0,1,2,3,4,5,6,42,48],[1,4,5,8,19,28,29,30,31],[0,1,4,5]),([0,1,2,3,4,5,6,42,57],[5,8,19,33],[]),([0,1,2,3,4,5,6,171],[7,19],[]),([0,1,2,3,4,5,6,48],[1,4,5,8,19,28,29,30,31],[0,1]),([0,1,2,3,4,5,6,50,24],[1,5,22,32],[0]),([0,1,2,3,4,5,6,24,57],[5,7,23,24,27],[0,4]),([0,1,2,3,4,5,6,65],[5,6,11,14],[0,1,2]),([0,1,2,3,4,5,6,38,98],[3,5,7,17,18],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB9_15Ok : checkNodesBT rW rG rMask rB9_15P rAutos rK8 9 rB9_15 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB9_15Mem : ∀ ns ∈ rB9_15, Impossible rG 9 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK8Ok rB9_15Ok
def rB9_16S : List PoolSpec := [(26,[]),(13,[]),(40,[]),(35,[]),(45,[]),(26,[(1,2,4)]),(46,[]),(8,[]),(10,[]),(23,[]),(29,[]),(26,[(1,0,2)]),(25,[]),(25,[(1,0,2)]),(8,[(1,2,5),(1,5,6)]),(25,[(1,0,2),(1,54,6)]),(7,[(1,0,5)]),(25,[(1,0,6)]),(10,[(1,0,5)]),(1,[(1,0,5),(1,15,5)]),(25,[(1,2,4)]),(1,[(1,0,5),(1,113,6)]),(1,[(1,0,5),(1,2,5)]),(4,[(1,0,5),(1,5,6)]),(4,[(1,0,5),(1,113,6)]),(25,[(1,113,6)]),(25,[(1,4,113)]),(26,[(1,4,113)]),(26,[(1,113,6)]),(8,[(3,2,5),(1,114,4)]),(25,[(1,2,113)]),(26,[(1,2,113)]),(25,[(1,113,6),(1,2,57)]),(26,[(1,113,6),(1,2,57)]),(7,[(2,5,42),(1,58,42)]),(25,[(1,0,115)])]
def rB9_16P : BT (Option BoundPool) := buildPoolsBT 6 rW rR rSlices rB9_16S
def rB9_16 : List NodeSpec := [([0,1,2,3,4,5,6,57],[4,6,10,17,34],[]),([0,1,2,3,4,5,6,57,98],[4,6,21,24,32,33],[0,4]),([0,1,2,3,4,5,6,98],[0,4,6,8,15],[0]),([0,1,2,3,4,138,113,6],[4,12],[]),([0,1,2,3,4,113,40,41,6],[3,4,12,18,22],[0,1]),([0,1,2,3,4,113,40,117,6],[3,4,9,26,27],[1]),([0,1,2,3,4,113,40,6,38],[2,6,10,12,14,16,23],[0,4]),([0,1,2,3,4,113,40,6,57],[6,10,24,25,28],[0]),([0,1,2,3,4,113,54,6,38],[4,6,10,16,23,30,31],[0]),([0,1,2,3,4,113,37,6],[4,5,7,19,20],[]),([0,1,2,3,4,113,6,116],[6,10,12],[0]),([0,1,2,3,4,40,6,63],[2,6,12],[]),([0,1,2,3,4,40,6,57],[6,24,25,28],[0,4]),([0,1,2,3,4,54,41,6],[4,6,8,13],[]),([0,1,2,3,4,54,6,38],[1,6,11,13],[0]),([0,1,2,3,115,218,5,6],[4,29,35],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB9_16Ok : checkNodesBT rW rG rMask rB9_16P rAutos rK8 9 rB9_16 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB9_16Mem : ∀ ns ∈ rB9_16, Impossible rG 9 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK8Ok rB9_16Ok
def rB9_17S : List PoolSpec := [(31,[]),(40,[]),(35,[]),(45,[]),(47,[]),(46,[]),(8,[]),(44,[]),(23,[(1,1,3)]),(10,[(1,1,5)]),(23,[(1,1,5)]),(10,[]),(10,[(1,5,6)]),(7,[(1,0,2),(1,1,3)]),(7,[(1,0,2),(1,1,5)]),(29,[]),(16,[]),(20,[]),(3,[(1,0,2),(1,2,4),(1,15,6)]),(9,[(1,0,2),(1,2,4)]),(8,[(1,1,3),(1,2,4)]),(3,[(1,0,2),(1,2,4)]),(25,[(1,0,2),(1,2,6)]),(8,[(1,1,3),(1,2,6)]),(12,[(1,0,2),(1,2,6)]),(16,[(1,1,3)]),(3,[(1,0,2),(1,2,6)]),(11,[(1,0,2),(1,2,4)]),(25,[(1,0,2),(1,2,4)]),(8,[(1,1,5),(1,2,4)]),(8,[(1,1,5),(1,2,6)]),(5,[(1,0,2),(1,2,6)]),(16,[(1,1,5)]),(25,[]),(25,[(1,0,2)]),(6,[(1,0,2),(1,2,4),(1,15,6)]),(26,[(1,0,2),(1,2,4)]),(27,[]),(8,[(1,2,5),(1,5,6)]),(25,[(1,0,6)]),(8,[(3,2,5),(1,114,4)]),(7,[(3,1,42),(1,165,3)])]
def rB9_17P : BT (Option BoundPool) := buildPoolsBT 6 rW rR rSlices rB9_17S
def rB9_17 : List NodeSpec := [([0,1,2,3,115,5,6,42],[3,39,40],[0,4]),([0,1,2,3,115,113,6],[2,3,15,33,40],[0]),([0,1,2,166,4,5,6,42],[3,39,41],[]),([0,1,110,21,3,4,5,6],[5,6,34],[]),([0,1,106,21,3,4,5,6],[3,6,34],[]),([0,1,75,21,3,4,5,6],[5,6,34],[]),([0,1,94,21,3,4,5,6],[5,34],[]),([0,1,21,3,23,4,15,5,6],[7,8,19,20,21],[0]),([0,1,21,3,23,4,5,6,16],[8,13,17,22,23,24,25,26],[0,4]),([0,1,21,3,4,15,5,28,6],[9,10,27,28,29],[0]),([0,1,21,3,4,15,5,6,38],[3,12,28,36],[0]),([0,1,21,3,4,5,28,6,16],[10,14,17,22,30,31,32],[0,4]),([0,1,21,3,4,5,40,41,6],[0,3,34,37],[0]),([0,1,21,3,4,5,40,6,38],[1,5,16,34,38],[0]),([0,1,21,3,4,5,37,6],[3,6,11,28],[0]),([0,1,21,3,4,5,6,18],[3,4,6,18,35],[0,2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB9_17Ok : checkNodesBT rW rG rMask rB9_17P rAutos rK8 9 rB9_17 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB9_17Mem : ∀ ns ∈ rB9_17, Impossible rG 9 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK8Ok rB9_17Ok
def rB9_18S : List PoolSpec := [(31,[]),(24,[]),(26,[]),(13,[]),(40,[]),(45,[]),(46,[]),(8,[]),(44,[]),(9,[(1,0,2),(1,0,4)]),(21,[(1,1,3)]),(23,[(1,1,3)]),(3,[(1,0,2),(1,0,4)]),(22,[]),(10,[(1,1,5)]),(25,[(1,0,2),(1,0,4)]),(5,[(1,0,2),(1,0,4)]),(21,[(1,1,5)]),(23,[(1,1,5)]),(10,[(1,21,6)]),(10,[]),(7,[(1,0,2),(1,1,3)]),(4,[(1,0,6),(1,1,3)]),(25,[(1,0,2),(1,0,6)]),(12,[(1,0,2),(1,0,6)]),(3,[(1,0,2),(1,0,6)]),(29,[]),(16,[]),(8,[(1,5,6)]),(26,[(1,0,2)]),(3,[(1,0,2),(1,2,4),(1,21,6)]),(3,[(1,0,2),(1,2,4),(1,4,6)]),(25,[(1,0,2),(1,21,6)]),(25,[(1,0,2)]),(6,[(1,0,2),(1,2,4),(1,21,6)]),(6,[(1,0,2),(1,2,4),(1,4,6)]),(25,[(1,0,2),(1,40,6)]),(25,[(1,0,2),(1,2,38)]),(26,[(1,0,2),(1,2,38)]),(25,[(1,0,6)]),(1,[(1,0,6),(3,1,5),(1,31,0)]),(7,[(3,1,5),(1,31,0)]),(4,[(1,0,6),(3,1,5),(1,31,0)]),(7,[]),(7,[(0,5,42),(1,1,123)]),(7,[(0,5,42),(1,2,123)]),(7,[(2,5,42),(1,58,0)])]
def rB9_18P : BT (Option BoundPool) := buildPoolsBT 6 rW rR rSlices rB9_18S
def rB9_18 : List NodeSpec := [([0,1,21,3,4,5,6,38,51],[4,6,27,28,37,38],[0]),([0,1,21,3,4,5,6,51],[6,7,27,36],[0]),([0,1,21,3,4,40,41,6],[5,6,20,33],[0]),([0,1,21,3,4,40,6,38],[4,6,29,33],[0]),([0,1,21,3,15,5,6,17],[3,5,20,31,35],[0,1,2,4]),([0,1,3,4,15,5,6,24],[5,19,30,34],[0,2,4]),([0,1,3,4,5,124,6,42],[5,39,45],[0,4]),([0,1,3,4,5,40,6,24],[2,6,20,27,32],[]),([0,2,3,4,5,180,6,42],[5,39,44],[]),([183,1,2,3,4,5,6,42],[5,6,26,39,46],[4,5]),([93,1,2,21,3,4,5,6],[6,33],[]),([93,1,2,3,4,5,6,42],[6,39,43],[4]),([157,1,2,3,4,5,6,42],[0,5,26,39,40,41,42],[0,1,4,5]),([1,2,21,3,23,4,22,5,6],[1,8,9,10,11,12],[0,1]),([1,2,21,3,23,4,5,6,42],[11,13,21,22,23,24,25],[0,1]),([1,2,21,3,4,22,5,28,6],[1,12,14,15,16,17,18],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB9_18Ok : checkNodesBT rW rG rMask rB9_18P rAutos rK8 9 rB9_18 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB9_18Mem : ∀ ns ∈ rB9_18, Impossible rG 9 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK8Ok rB9_18Ok
def rB9_19S : List PoolSpec := [(43,[]),(31,[]),(24,[]),(13,[]),(40,[]),(45,[]),(47,[]),(46,[]),(8,[]),(3,[(1,0,2),(1,0,4),(1,21,6)]),(25,[(1,0,2),(1,0,4)]),(23,[(1,1,5)]),(10,[]),(23,[]),(6,[(1,0,2),(1,0,4),(1,21,6)]),(26,[(1,0,2),(1,0,4)]),(3,[(1,0,2),(1,0,6),(1,21,4)]),(3,[(1,0,2),(1,0,6),(1,4,6)]),(25,[(1,0,2),(1,0,6)]),(3,[(1,0,2),(1,0,6)]),(7,[(1,0,2),(1,1,5)]),(4,[(1,0,6),(1,1,5)]),(5,[(1,0,2),(1,0,6)]),(29,[]),(18,[]),(26,[(1,0,2),(1,0,6)]),(7,[(1,0,2),(1,5,42)]),(6,[(1,0,2),(1,0,6),(1,21,4)]),(6,[(1,0,2),(1,0,6),(1,4,6)]),(8,[(1,5,6)]),(4,[(1,0,6),(1,5,6)]),(8,[(1,5,42)]),(41,[]),(1,[(1,0,5),(1,0,6),(1,5,6)]),(7,[(1,0,5)]),(1,[(1,0,5),(1,0,6)]),(25,[(1,0,6)]),(4,[(1,0,5),(1,0,6),(1,5,6)]),(48,[]),(26,[(1,0,6)]),(4,[(1,0,5),(1,0,6)]),(25,[(1,0,6),(1,2,113)]),(26,[(1,0,6),(1,2,113)]),(9,[(1,0,6),(1,2,42)]),(11,[(1,0,6),(1,2,42)])]
def rB9_19P : BT (Option BoundPool) := buildPoolsBT 6 rW rR rSlices rB9_19S
def rB9_19 : List NodeSpec := [([1,2,21,3,4,22,5,6,38],[1,3,5,10,15],[0]),([1,2,21,3,4,5,28,6,42],[2,11,18,19,20,21,22],[0,1]),([1,2,21,3,4,5,6,42,50],[0,1,2,5,24,25],[0]),([1,2,21,3,4,5,6,42,57],[5,7,18,25,26,31],[0]),([1,2,21,3,4,5,42,17],[1,3,5,17,28],[0,2,5]),([1,2,21,3,4,5,42,38],[1,4,5,13,18,25,29,30],[0]),([1,2,3,4,22,5,6,24],[1,5,9,12,14],[0,1,2]),([1,2,3,4,15,5,113,6,42],[0,5,6,32,34,35],[0,4,5]),([1,2,3,4,43,5,6,42],[3,5,6,16,27],[0,2,4,5]),([1,2,3,4,123,113,6,42],[5,8,38],[0,1]),([1,2,3,4,5,113,40,6,42],[0,7,13,23,34,36],[0,4]),([1,2,3,4,5,113,54,6,42],[0,7,13,23,34,40,41,42],[0,4]),([1,2,3,4,5,113,6,42,24],[5,7,13,35,43,44],[0]),([1,2,3,4,5,113,42,38],[4,23,29,33,34,36,37],[0,1,4,5]),([1,2,3,4,5,54,6,42],[3,7,13,18],[0,4]),([1,2,3,4,113,40,6,42],[7,36,39,40],[0,4])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB9_19Ok : checkNodesBT rW rG rMask rB9_19P rAutos rK8 9 rB9_19 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB9_19Mem : ∀ ns ∈ rB9_19, Impossible rG 9 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK8Ok rB9_19Ok
def rB9_20S : List PoolSpec := [(31,[]),(35,[]),(45,[]),(47,[]),(46,[]),(8,[(1,2,6)]),(8,[]),(3,[(1,0,2),(1,0,4),(1,2,4)]),(3,[(1,0,2),(1,0,4),(1,2,6)]),(25,[(1,0,2),(1,0,4)]),(10,[]),(6,[(1,0,2),(1,0,4),(1,2,4)]),(23,[]),(21,[]),(6,[(1,0,2),(1,0,4),(1,2,6)]),(3,[(1,0,2),(1,0,6),(1,2,4)]),(3,[(1,0,2),(1,0,6),(1,2,6)]),(25,[(1,0,2),(1,0,6)]),(6,[(1,0,2),(1,0,6),(1,2,4)]),(16,[]),(6,[(1,0,2),(1,0,6),(1,2,6)]),(4,[(1,0,6)]),(8,[(1,5,6)]),(1,[(1,0,5),(1,0,6),(1,5,6)]),(7,[(1,0,5)]),(25,[(1,0,6)]),(4,[(1,0,5),(1,0,6),(1,5,6)]),(26,[(1,0,6)])]
def rB9_20P : BT (Option BoundPool) := buildPoolsBT 5 rW rR rSlices rB9_20S
def rB9_20 : List NodeSpec := [([1,2,3,4,113,42,38],[22,23,24,25,26,27],[0,1,4,5]),([1,21,3,4,22,5,40,6],[4,9,10,13],[0]),([1,21,3,4,22,5,6,16],[0,2,8,14],[0,2]),([1,21,3,4,15,5,6,42],[2,3,15,18],[0,1,2]),([1,21,3,4,5,40,6,42],[4,12,17],[0]),([1,21,3,4,5,42,16],[0,2,5,16,19,20,21],[0,2,4]),([1,21,3,22,15,5,6],[1,2,6,7,10,11],[0,1,2,4,6])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB9_20Ok : checkNodesBT rW rG rMask rB9_20P rAutos rK8 9 rB9_20 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB9_20Mem : ∀ ns ∈ rB9_20, Impossible rG 9 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK8Ok rB9_20Ok
def rNodes9 : List NodeSpec := rB9_0 ++ rB9_1 ++ rB9_2 ++ rB9_3 ++ rB9_4 ++ rB9_5 ++ rB9_6 ++ rB9_7 ++ rB9_8 ++ rB9_9 ++ rB9_10 ++ rB9_11 ++ rB9_12 ++ rB9_13 ++ rB9_14 ++ rB9_15 ++ rB9_16 ++ rB9_17 ++ rB9_18 ++ rB9_19 ++ rB9_20
def rK9 : BT (List (List Nat)) := buildBucketsBT rW rNodes9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rK9Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible rG 9 xs.toFinset) rK9 := buildBucketsBT_of_mem (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append (forall_append rB9_0Mem rB9_1Mem) rB9_2Mem) rB9_3Mem) rB9_4Mem) rB9_5Mem) rB9_6Mem) rB9_7Mem) rB9_8Mem) rB9_9Mem) rB9_10Mem) rB9_11Mem) rB9_12Mem) rB9_13Mem) rB9_14Mem) rB9_15Mem) rB9_16Mem) rB9_17Mem) rB9_18Mem) rB9_19Mem) rB9_20Mem)
def rB10_0S : List PoolSpec := [(24,[]),(26,[]),(13,[]),(45,[]),(47,[]),(1,[(1,0,1),(2,7,6)]),(7,[(1,0,1)]),(4,[(1,0,1),(2,7,6)]),(46,[]),(8,[]),(10,[]),(23,[]),(29,[]),(7,[(1,0,2),(2,21,4)]),(7,[(1,0,2)]),(26,[(1,0,2)]),(20,[]),(3,[(1,0,2),(2,21,4)]),(3,[(1,0,2),(2,21,6)]),(25,[]),(25,[(1,0,2)]),(10,[(2,21,6)]),(27,[]),(6,[(1,0,2),(2,21,4)]),(6,[(1,0,2),(2,21,6)]),(4,[(2,5,6)]),(8,[(2,5,6)]),(4,[]),(7,[(1,0,5)]),(25,[(1,0,6)]),(48,[]),(26,[(1,0,6)]),(1,[(1,0,5),(2,5,6)]),(1,[(1,0,5),(2,113,6)]),(42,[]),(4,[(1,0,5),(2,5,6)]),(4,[(1,0,5),(2,113,6)]),(26,[(2,113,6)]),(8,[(2,113,6)]),(7,[]),(7,[(2,5,42)]),(8,[(2,5,42)]),(7,[(3,5,42)]),(8,[(3,5,42)]),(1,[(1,2,5)]),(26,[(3,4,40)])]
def rB10_0P : BT (Option BoundPool) := buildPoolsBT 6 rW rR rSlices rB10_0S
def rB10_0 : List NodeSpec := [([58,0,1,2,3,4,5,6,42],[3,8,22,29,34,40,41],[0,1,4,5]),([12,0,1,2,3,4,5,6],[0,1,5,6,7],[0,1]),([25,0,1,2,3,4,5,6],[1,3,11,14,18,19,21,24],[0,2]),([39,0,1,2,21,3,4,5,6],[2,3,8,11,14,20,25,26],[0]),([39,0,1,2,3,4,113,6],[12,19,26,28,32,35],[0,1]),([62,0,1,2,3,4,5,113,6],[9,19,28,30,33,36],[0,1,4]),([62,0,1,2,3,4,5,6],[19,28,30,33,36,37,38],[0,1,4,5]),([55,0,1,2,3,4,5,6],[2,3,4,11,15,20],[0]),([122,0,1,2,3,4,5,6],[3,8,10,29,31,42,43],[0,1]),([122,0,1,2,3,4,5,6,42],[3,9,29,31,42],[0,4]),([44,0,1,2,3,4,5,6],[1,10,11,13,17,19,23],[0,2,4,6]),([191,0,1,2,3,4,5,6],[1,3,9,16,39],[0,4]),([83,0,1,2,21,3,4,5,6],[3,11,20],[0]),([83,0,1,2,3,4,40,6],[8,10,19],[0,4]),([84,0,1,2,3,4,5,40,6],[8,27,34,44],[1]),([84,0,1,2,3,4,5,6],[3,9,10,19,34,39,44,45],[0,1,4,5])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB10_0Ok : checkNodesBT rW rG rMask rB10_0P rAutos rK9 10 rB10_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB10_0Mem : ∀ ns ∈ rB10_0, Impossible rG 10 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK9Ok rB10_0Ok
def rB10_1S : List PoolSpec := [(31,[]),(24,[]),(26,[]),(13,[]),(45,[]),(8,[(1,2,4)]),(46,[]),(8,[]),(10,[(3,1,5)]),(23,[(3,1,5)]),(10,[]),(23,[]),(21,[]),(29,[]),(4,[(1,0,6),(3,1,5)]),(7,[(1,0,2),(3,1,5)]),(4,[(1,0,6)]),(20,[]),(25,[]),(8,[(1,1,5),(3,3,28)]),(4,[(1,1,5),(3,3,28)]),(25,[(1,0,2)]),(8,[(3,1,5),(1,2,4)]),(4,[(3,1,5)]),(8,[(3,1,5)]),(8,[(1,2,5)]),(7,[(1,0,5)]),(25,[(1,0,6)]),(48,[]),(26,[(1,0,6)]),(25,[(1,2,4)]),(4,[(1,0,5)]),(8,[(3,2,5)]),(26,[(3,2,113)]),(8,[(3,2,113)]),(4,[(3,0,5)]),(10,[(3,0,5)]),(7,[(3,0,5),(1,2,4)]),(1,[(3,0,5),(1,2,5)]),(3,[(1,0,6),(3,2,42)]),(3,[(1,0,6)]),(7,[(1,1,5),(3,3,28)]),(1,[(1,0,6),(3,1,5)]),(7,[(3,1,5)]),(6,[(1,0,6)]),(7,[(3,1,42)]),(7,[]),(1,[(1,0,6)]),(6,[(1,0,6),(3,2,42)]),(7,[(3,2,42)]),(1,[(1,0,6),(3,2,42)]),(8,[(3,2,42)]),(1,[(1,1,5),(3,3,28)]),(7,[(3,1,5),(1,2,4)])]
def rB10_1P : BT (Option BoundPool) := buildPoolsBT 6 rW rR rSlices rB10_1S
def rB10_1 : List NodeSpec := [([30,0,1,2,4,5,6],[18,19,20,41,52],[0,1,4,5]),([92,0,1,2,21,3,4,5,6],[6,10,11,21],[0]),([8,0,1,2,3,4,5,6],[0,1,2,3],[0]),([114,0,1,2,3,4,5,6,42],[6,27,32,46,47],[0,4]),([114,0,1,2,3,4,113,6],[6,11,13,18,31,32],[0,1]),([91,0,1,2,3,4,5,113,6],[6,12,26,28,31],[0,1]),([91,0,1,2,3,4,5,6],[3,6,18,28,31,33,34],[0,1,4]),([46,0,1,2,3,4,5,6],[2,4,16,18,39,48,49,50,51],[0,1,2,5]),([46,0,1,2,3,4,5,6,42],[4,7,16,27,29,39,48,49],[0,2,4]),([31,0,1,2,21,3,4,5,6],[0,4,8,9,11,15,21,23,24],[0]),([31,0,1,2,3,4,15,5,6],[8,22,23,30,53],[0,1,4,5]),([31,0,1,2,3,4,5,6,42],[4,6,14,24,27,42,43],[0,1,4,5]),([165,0,1,2,3,4,5,6,42],[4,29,40,44,45],[0]),([188,0,1,2,3,4,5,6],[2,3,6,17],[0]),([145,0,1,2,3,4,15,5,6],[5,30,35,36,37],[0,4,5]),([145,0,1,2,3,4,40,6],[6,11,18,25,35,38],[0,1,4])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB10_1Ok : checkNodesBT rW rG rMask rB10_1P rAutos rK9 10 rB10_1 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB10_1Mem : ∀ ns ∈ rB10_1, Impossible rG 10 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK9Ok rB10_1Ok
def rB10_2S : List PoolSpec := [(31,[]),(24,[]),(13,[]),(45,[]),(26,[(1,2,4)]),(47,[]),(7,[(1,0,1)]),(19,[]),(10,[(1,0,1)]),(8,[(1,2,4)]),(7,[(1,0,1),(1,2,4)]),(1,[(1,0,1)]),(6,[(1,2,4)]),(46,[]),(26,[(1,2,6)]),(8,[(1,2,6)]),(4,[(1,0,1)]),(8,[]),(44,[]),(23,[(1,1,3)]),(10,[(1,1,5)]),(23,[(1,1,5)]),(10,[]),(23,[]),(21,[]),(7,[(1,0,2),(1,1,3)]),(7,[(1,0,2),(1,1,5)]),(29,[]),(16,[]),(26,[(1,0,2)]),(20,[]),(3,[(1,0,2),(1,21,4)]),(3,[(1,0,2),(1,21,6)]),(4,[(1,1,3)]),(8,[(1,1,3)]),(12,[(1,0,2)]),(3,[(1,0,2)]),(25,[]),(8,[(1,1,5)]),(25,[(1,0,2)]),(4,[(1,1,5)]),(4,[(3,1,5)]),(8,[(3,1,5)]),(8,[(1,2,5)]),(6,[(1,0,2),(1,21,4)]),(6,[(1,0,2),(1,21,6)]),(4,[(1,4,5)]),(4,[]),(42,[]),(8,[(3,2,5)]),(1,[(3,0,5),(1,145,2)]),(4,[(3,0,5)]),(8,[(1,145,2)]),(7,[(3,1,5),(1,31,0)]),(4,[(3,1,5),(1,31,0)]),(1,[(3,1,5),(1,31,0)]),(1,[(3,1,5),(1,31,2)]),(26,[(3,0,40)]),(4,[(3,0,40)]),(4,[(1,114,0)])]
def rB10_2P : BT (Option BoundPool) := buildPoolsBT 6 rW rR rSlices rB10_2S
def rB10_2 : List NodeSpec := [([82,0,1,2,3,4,5,40,6],[13,37,43,47,48],[0]),([82,0,1,2,3,4,5,6],[2,13,37,43,48,57,58],[0,1,4]),([0,93,1,2,3,4,5,6],[2,13,37,49,59],[0,1,4]),([0,157,1,2,3,4,5,6],[27,37,42,53,54,55],[0,1,4,5]),([0,1,7,2,3,4,15,5,6],[1,4,8,9,10,11,12],[0,1]),([0,1,7,2,3,4,5,6,16],[1,3,6,8,13,14,15,16],[0]),([0,1,2,75,3,4,5,6],[2,13,17,37,41,56],[0,4]),([0,1,2,94,3,4,5,6],[2,13,37,50,51,52],[0,4]),([0,1,2,21,64,3,4,5,6],[1,13,23,29,30],[]),([0,1,2,21,3,23,4,5,6],[18,19,25,29,33,34,35,36],[0]),([0,1,2,21,3,4,73,5,6],[3,7,29],[]),([0,1,2,21,3,4,43,5,6],[0,3,5,22,23,24,31,44],[0,2]),([0,1,2,21,3,4,5,28,6],[20,21,26,29,36,38,39,40],[0]),([0,1,2,21,3,4,5,54,6],[13,23,29,39],[0]),([0,1,2,21,3,4,5,41,6],[3,22,23,29,37,39,46],[0,1]),([0,1,2,21,3,4,5,6,24],[0,3,22,23,28,32,45],[0,2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB10_2Ok : checkNodesBT rW rG rMask rB10_2P rAutos rK9 10 rB10_2 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB10_2Mem : ∀ ns ∈ rB10_2, Impossible rG 10 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK9Ok rB10_2Ok
def rB10_3S : List PoolSpec := [(43,[]),(31,[]),(26,[]),(13,[]),(40,[]),(45,[]),(26,[(1,2,4)]),(47,[]),(8,[(1,2,4)]),(6,[(1,2,4)]),(46,[]),(8,[]),(44,[]),(10,[(1,1,5)]),(10,[]),(23,[]),(21,[]),(4,[(1,0,6),(1,1,3)]),(4,[(1,0,6),(1,1,5)]),(29,[]),(4,[(1,0,6)]),(8,[(1,5,6)]),(7,[(1,0,2)]),(26,[(1,0,2)]),(20,[]),(8,[(1,1,3),(1,2,4)]),(3,[(1,0,2),(1,21,4)]),(3,[(1,0,2),(1,4,6)]),(4,[(1,1,3)]),(8,[(1,1,3)]),(8,[(1,1,5),(1,2,4)]),(25,[]),(8,[(1,1,5)]),(25,[(1,0,2)]),(4,[(1,1,5)]),(8,[(1,2,5)]),(6,[(1,0,2),(1,21,4)]),(8,[(1,21,4)]),(6,[(1,0,2),(1,4,6)]),(4,[(1,5,6)]),(7,[(1,0,5)]),(25,[(1,0,6)]),(48,[]),(26,[(1,0,6)]),(10,[(1,0,5)]),(25,[(1,2,4)]),(1,[(1,0,5),(1,5,6)]),(1,[(1,0,5),(1,113,6)]),(7,[(1,0,5),(1,2,4)]),(1,[(1,0,5)]),(1,[(1,0,5),(1,2,5)]),(4,[(1,0,5),(1,5,6)]),(4,[(1,0,5),(1,113,6)]),(25,[(1,113,6)]),(4,[(1,0,5)]),(26,[(1,113,6)]),(8,[(3,2,5),(1,114,4)]),(25,[(1,2,113)]),(26,[(1,2,113)]),(8,[(1,2,113)]),(8,[(1,113,6)]),(7,[(1,1,2)]),(3,[(1,0,6),(1,2,4)]),(1,[(1,0,6),(1,1,3)]),(7,[(1,1,3)]),(12,[(1,0,6)]),(3,[(1,0,6)]),(1,[(1,0,6),(1,1,5)]),(7,[(1,1,5)]),(6,[(1,0,6)]),(10,[(1,0,6)]),(6,[(1,0,6),(1,2,4)]),(7,[]),(1,[(1,0,6)]),(7,[(0,5,42)]),(12,[]),(7,[(1,1,3),(1,2,4)]),(7,[(1,1,5),(1,2,4)]),(7,[(3,2,5),(1,114,4)])]
def rB10_3P : BT (Option BoundPool) := buildPoolsBT 7 rW rR rSlices rB10_3S
def rB10_3 : List NodeSpec := [([0,1,2,21,3,4,5,6,17],[1,3,5,15,27,38],[0,1,2,4,5]),([0,1,2,21,3,4,5,6,38],[3,4,5,10,15,21,22,23,31,33,39],[0]),([0,1,2,154,3,4,5,6,42],[10,24,43,61],[]),([0,1,2,3,23,4,15,5,6],[9,12,25,28,45,75,76],[0,1,4,5]),([0,1,2,3,23,4,5,6,42],[17,29,41,63,64,65,66],[0,1,4,5]),([0,1,2,3,4,115,5,6],[5,14,31,56,78],[0,1,4,5]),([0,1,2,3,4,15,5,113,6],[6,8,19,31,44,45,48,49],[0,4,5]),([0,1,2,3,4,15,5,28,6],[6,13,30,34,45,77],[0,1,4,5]),([0,1,2,3,4,15,5,6,42],[5,8,20,62,70,71,72],[0,1,2,4,5]),([0,1,2,3,4,43,5,6],[2,3,5,7,14,15,16,26,31,36,37],[0,2,4,5,6]),([0,1,2,3,4,123,5,6,42],[5,11,20,41,66,69,73,74],[0,1,2,4]),([0,1,2,3,4,5,113,40,6],[0,10,19,31,35,40,50,54],[0,1,4]),([0,1,2,3,4,5,113,54,6],[10,15,16,40,42,54,57,58,59],[0,1,4]),([0,1,2,3,4,5,113,6,38],[4,19,21,31,40,46,51],[0,1,4,5]),([0,1,2,3,4,5,113,6,57],[40,42,47,52,53,55,60],[0,1,4,5]),([0,1,2,3,4,5,28,6,42],[18,32,41,43,66,67,68],[0,1,4,5])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB10_3Ok : checkNodesBT rW rG rMask rB10_3P rAutos rK9 10 rB10_3 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB10_3Mem : ∀ ns ∈ rB10_3, Impossible rG 10 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK9Ok rB10_3Ok
def rB10_4S : List PoolSpec := [(43,[]),(31,[]),(24,[]),(26,[]),(13,[]),(40,[]),(45,[]),(26,[(1,2,4)]),(46,[]),(8,[]),(10,[]),(23,[]),(18,[]),(16,[]),(4,[(1,0,6)]),(8,[(1,5,6)]),(8,[(1,5,42)]),(7,[(1,0,2)]),(26,[(1,0,2)]),(3,[(1,0,2),(1,21,6)]),(25,[]),(25,[(1,0,2)]),(27,[]),(8,[(1,2,5)]),(4,[(1,21,5)]),(8,[(1,21,5)]),(6,[(1,0,2),(1,21,6)]),(8,[(1,21,6)]),(4,[(1,21,6)]),(4,[(1,4,5)]),(7,[(1,0,5)]),(25,[(1,0,6)]),(26,[(1,0,6)]),(32,[]),(25,[(1,2,4)]),(1,[(1,0,5),(1,5,6)]),(1,[(1,0,5),(1,113,6)]),(1,[(1,0,5),(1,2,5)]),(4,[(1,0,5),(1,5,6)]),(4,[(1,0,5),(1,113,6)]),(25,[(1,113,6)]),(4,[(1,0,5)]),(42,[]),(26,[(1,113,6)]),(8,[(3,2,5),(1,114,4)]),(8,[(1,113,6)]),(1,[(3,0,5),(1,145,6)]),(8,[(1,145,6)]),(4,[(3,0,5),(1,145,6)]),(7,[(3,0,5)]),(3,[(1,0,6),(1,2,42)]),(7,[(1,1,42)]),(8,[(1,1,42)]),(6,[(1,0,6)]),(7,[]),(1,[(1,0,6)]),(6,[(1,0,6),(1,2,42)]),(7,[(1,2,42)]),(4,[(1,0,6),(1,5,42)]),(7,[(1,5,42)]),(1,[(1,0,6),(1,5,42)]),(1,[(1,15,5)]),(25,[(1,0,40)]),(26,[(1,0,40)]),(25,[(1,4,40)]),(26,[(1,4,40)]),(1,[(1,2,5)]),(7,[(3,2,5),(1,114,4)]),(4,[(1,114,4)])]
def rB10_4P : BT (Option BoundPool) := buildPoolsBT 7 rW rR rSlices rB10_4S
def rB10_4 : List NodeSpec := [([0,1,2,3,4,5,40,54,6],[8,11,23,62,63],[0]),([0,1,2,3,4,5,40,41,6],[6,8,10,20,22,29,42],[0,1,4,5]),([0,1,2,3,4,5,40,37,6],[8,10,64,65,66],[0,1]),([0,1,2,3,4,5,40,6,42],[8,14,20,23,31,32,54],[0,4]),([0,1,2,3,4,5,54,6],[4,8,11,18,21,24,25],[0,4]),([0,1,2,3,4,5,37,6],[6,7,9,10,34,54,61],[0,1,4,5]),([0,1,2,3,4,5,6,63],[5,20,46,47,48,49],[0,1,4,5]),([0,1,2,3,4,5,6,42,50],[0,2,6,8,12,32,33,51,52,53],[0,1,4,5]),([0,1,2,3,4,5,6,42,24],[6,8,11,13,14,50,55,56,57],[0,2,4]),([0,1,2,3,4,5,6,42,57],[6,8,16,31,32,58,59,60],[0,1,4,5]),([0,1,2,3,4,5,6,24],[1,3,6,10,11,13,17,19,20,26,27,28],[0,2,4]),([0,1,2,3,4,5,6,57],[30,36,39,40,43,45],[0,1,4]),([0,1,2,3,4,113,40,6],[3,8,20,23,37,41],[0,1,4]),([0,1,2,3,4,113,6,38],[3,15,20,30,35,38],[0,1,4,5]),([0,1,2,3,4,40,41,6],[3,6,8,10,20,29],[0,1,4,5]),([0,1,2,3,115,5,6],[20,44,67,68],[0,4])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB10_4Ok : checkNodesBT rW rG rMask rB10_4P rAutos rK9 10 rB10_4 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB10_4Mem : ∀ ns ∈ rB10_4, Impossible rG 10 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK9Ok rB10_4Ok
def rB10_5S : List PoolSpec := [(31,[]),(35,[]),(45,[]),(8,[(1,2,4)]),(46,[]),(8,[(1,2,6)]),(8,[]),(3,[(1,0,2),(1,0,4)]),(10,[]),(23,[]),(21,[]),(6,[(1,0,2),(1,0,4)]),(3,[(1,0,2),(1,0,6)]),(16,[]),(4,[(1,0,6)]),(7,[(1,0,2)]),(6,[(1,0,2),(1,0,6)]),(26,[(1,0,2)]),(3,[(1,0,2),(1,2,4)]),(3,[(1,0,2),(1,2,6)]),(25,[(1,0,2)]),(6,[(1,0,2),(1,2,4)]),(8,[(1,2,5)]),(6,[(1,0,2),(1,2,6)]),(7,[(1,0,5)]),(1,[(1,0,5),(1,0,6)]),(25,[(1,0,6)]),(26,[(1,0,6)]),(4,[(1,0,5),(1,0,6)])]
def rB10_5P : BT (Option BoundPool) := buildPoolsBT 5 rW rR rSlices rB10_5S
def rB10_5 : List NodeSpec := [([0,1,21,3,4,15,5,6],[0,2,3,8,9,18,21],[0,2,4,6]),([0,1,21,3,4,5,40,6],[4,8,9,17,20,22],[0]),([0,1,21,3,4,5,6,16],[0,2,5,8,9,13,15,19,23],[0,2,4]),([1,2,21,3,4,22,5,6],[1,2,6,7,8,9,10,11],[0,1,2,4,6]),([1,2,21,3,4,5,6,42],[0,2,6,9,12,14,15,16],[0,1,2]),([1,2,3,4,5,113,6,42],[6,24,25,26,27,28],[0,1,4,5])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB10_5Ok : checkNodesBT rW rG rMask rB10_5P rAutos rK9 10 rB10_5 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB10_5Mem : ∀ ns ∈ rB10_5, Impossible rG 10 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK9Ok rB10_5Ok
def rNodes10 : List NodeSpec := rB10_0 ++ rB10_1 ++ rB10_2 ++ rB10_3 ++ rB10_4 ++ rB10_5
def rK10 : BT (List (List Nat)) := buildBucketsBT rW rNodes10
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rK10Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible rG 10 xs.toFinset) rK10 := buildBucketsBT_of_mem (forall_append (forall_append (forall_append (forall_append (forall_append rB10_0Mem rB10_1Mem) rB10_2Mem) rB10_3Mem) rB10_4Mem) rB10_5Mem)
def rB11_0S : List PoolSpec := [(26,[]),(7,[(1,0,1)]),(8,[(1,2,4)]),(1,[(1,0,1)]),(6,[(1,2,4)]),(4,[(1,0,1)]),(8,[]),(6,[]),(10,[]),(23,[]),(4,[(1,0,6)]),(7,[(1,0,2)]),(4,[(1,1,3)]),(8,[(1,1,3)]),(3,[(1,0,2)]),(25,[]),(8,[(1,1,5)]),(4,[(1,1,5)]),(4,[(3,1,5)]),(8,[(3,1,5)]),(8,[(1,2,5)]),(4,[]),(6,[(1,0,2)]),(7,[(1,0,5)]),(1,[(1,0,5)]),(4,[(1,0,5)]),(8,[(3,2,5)]),(4,[(3,0,5)]),(7,[(3,0,5)]),(1,[(3,0,5)]),(7,[(1,1,2)]),(7,[(1,1,3)]),(3,[(1,0,6)]),(7,[(1,1,5)]),(7,[(3,1,5)]),(6,[(1,0,6)]),(7,[]),(1,[(1,0,6)]),(8,[(1,1,2)]),(12,[]),(1,[(1,1,3)]),(1,[(1,1,5)]),(3,[]),(1,[(3,1,5)]),(3,[(1,2,4)]),(7,[(1,2,4)]),(1,[(1,2,5)]),(7,[(1,2,5)]),(7,[(3,2,5)]),(1,[])]
def rB11_0P : BT (Option BoundPool) := buildPoolsBT 6 rW rR rSlices rB11_0S
def rB11_0 : List NodeSpec := [([114,0,1,2,3,4,5,6],[8,15,21,26,48,49],[0,1,4,5]),([31,0,1,2,3,4,5,6],[15,18,19,34,43],[0,1,4,5]),([145,0,1,2,3,4,5,6],[6,15,27,28,29],[0,1,4,5]),([0,1,7,2,3,4,5,6],[0,1,3,5,6,7],[0,1]),([0,1,2,21,3,4,5,6],[0,6,8,9,11,14,15,21,22],[0,2,4,6]),([0,1,2,154,3,4,5,6],[0,7,8,21,30,38],[0,1,4,5]),([0,1,2,3,23,4,5,6],[7,12,13,15,31,39,40],[0,1,4,5]),([0,1,2,3,4,15,5,6],[0,2,4,8,15,21,44,45],[0,1,2,4,5,6]),([0,1,2,3,4,5,113,6],[0,6,15,23,24,25],[0,1,4,5]),([0,1,2,3,4,5,28,6],[0,15,16,17,33,41,42],[0,1,4,5]),([0,1,2,3,4,5,40,6],[0,8,15,20,21,46,47],[0,1,4,5]),([0,1,2,3,4,5,6,42],[0,6,10,15,32,35,36,37],[0,1,2,3,4,5])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB11_0Ok : checkNodesBT rW rG rMask rB11_0P rAutos rK10 11 rB11_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB11_0Mem : ∀ ns ∈ rB11_0, Impossible rG 11 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK10Ok rB11_0Ok
def rNodes11 : List NodeSpec := rB11_0
def rK11 : BT (List (List Nat)) := buildBucketsBT rW rNodes11
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rK11Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible rG 11 xs.toFinset) rK11 := buildBucketsBT_of_mem rB11_0Mem
def rB12_0S : List PoolSpec := [(8,[]),(6,[]),(4,[]),(7,[]),(3,[]),(1,[])]
def rB12_0P : BT (Option BoundPool) := buildPoolsBT 3 rW rR rSlices rB12_0S
def rB12_0 : List NodeSpec := [([0,1,2,3,4,5,6],[0,1,2,3,4,5],[0,1,2,3,4,5,6])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB12_0Ok : checkNodesBT rW rG rMask rB12_0P rAutos rK11 12 rB12_0 = true := by decide +kernel
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rB12_0Mem : ∀ ns ∈ rB12_0, Impossible rG 12 (nodeValsBT rW ns).toFinset := checkNodesBT_mem (by decide) rPairs rWOk (buildPoolsBT_sound rSlicesOk) rAutosOk rK11Ok rB12_0Ok
def rNodes12 : List NodeSpec := rB12_0
def rK12 : BT (List (List Nat)) := buildBucketsBT rW rNodes12
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rK12Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible rG 12 xs.toFinset) rK12 := buildBucketsBT_of_mem rB12_0Mem
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma rBound : Lower rR rG 13 := lower_of_forestBT (essPairs := [(VAR 0,4,5),(VAR 1,8,10),(VAR 2,1,5),(VAR 3,2,10),(VAR 4,1,17),(VAR 5,1,33),(VAR 6,1,65)]) (by decide +kernel) rK12Ok (by decide +kernel)

end Small
namespace Relate
def insertZero (r : Small.Row) : Wide.Row :=
  ⟨(r.val % 4 + 8 * (r.val / 4)) % 256, Nat.mod_lt _ (by decide)⟩
def project (w : Wide.Wire) : Small.Wire := fun r => w (insertZero r)
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
lemma liftPin (h : Small.Lower (Small.varsOf 127) 0xfffffffffffffefafffeffeefefaeca0 13) : Wide.Lower (Wide.varsOf 255) 0xfffffffffffffffffffffffffffefffafffffffefffffefefffefffaeeccaa00 14 := by
  have bound : Wide.Lower (Wide.varsOf 251) 0xffffffffffffffffffffffffffeeffaaffffffeeffffeeeeffeeffaaeeccaa00 13 := by
    intro n bank hr ha
    have proots : (((Wide.varsOf 251).map Wide.obs).map project) = (Small.varsOf 127).map Small.obs := by
      change [_,_,_,_,_,_,_] = [_,_,_,_,_,_,_]
      repeat' apply congrArg₂ List.cons
      all_goals first | rfl | funext r; revert r; decide +kernel
    have target : project (Wide.obs 0xffffffffffffffffffffffffffeeffaaffffffeeffffeeeeffeeffaaeeccaa00) = Small.obs 0xfffffffffffffefafffeffeefefaeca0 := by funext r; revert r; decide +kernel
    have r := reach hr
    have a := avail ha
    rw [proots] at r
    rw [target] at a
    exact h n _ r a
  exact Wide.lift_of (z := 4) (o := 0) (essPairs := [(Wide.VAR 2,32,36)]) (by decide +kernel) bound
end Relate
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def f (x : Fin 8 → Bool) : Bool := (x 0 && x 3) || (x 0 && x 5) || (x 0 && x 6) || (x 0 && x 7) || (x 1 && x 4) || (x 1 && x 6) || (x 2 && x 5) || (x 2 && x 6) || (x 2 && x 7) || (x 3 && x 5) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 6 && x 7)
def onWit : List Gate := [⟨.or, [4, 6]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [11, 3]⟩, ⟨.or, [11, 4]⟩, ⟨.or, [3, 5]⟩, ⟨.or, [14, 6]⟩, ⟨.and, [1, 8]⟩, ⟨.and, [15, 9]⟩, ⟨.and, [12, 10]⟩, ⟨.and, [13, 6]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [20, 18]⟩, ⟨.or, [21, 19]⟩]

theorem onWitBasis : ∀ g ∈ onWit,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [onWit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem onWitCorrect : ∀ x : Fin 8 → Bool,
    Circuit.eval ⟨onWit, 22⟩ (List.ofFn x) = f x := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem onGraphCorrect : ∀ x : Fin 8 → Bool, f x = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  decide +kernel

theorem onFinal :
∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o hfit _hone hev
  have hf : ∀ y : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn y) = f y := fun y => (hev y).trans (onGraphCorrect y).symm
  have hrow : ∀ r : Wide.Row, f (Wide.evalInput r) = (0xfffffffffffffffffffffffffffefffafffffffefffffefefffefffaeeccaa00 : Nat).testBit r.val := by decide +kernel
  have hw : ∀ r : Wide.Row, Circuit.eval ⟨onWit,22⟩ (List.ofFn (Wide.evalInput r)) = (0xfffffffffffffffffffffffffffefffafffffffefffffefefffefffaeeccaa00 : Nat).testBit r.val :=
    fun r => (onWitCorrect (Wide.evalInput r)).trans (hrow r)
  obtain ⟨gs, out, hg, hlen, hev⟩ := Wide.replace_of_lower (0xfffffffffffffffffffffffffffefffafffffffefffffefefffefffaeeccaa00 : Nat) (by decide) (by decide) (by decide)
    14 (Relate.liftPin Small.rBound) onWit 22 (by decide) onWitBasis f hrow hw gates o hfit hf
  exact ⟨gs, out, hg, hlen, fun x => (hev x).trans (onGraphCorrect x)⟩
end PEqualNP.Outside.L_meta_35418

theorem PEqualNP.Outside.L_meta_35418 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) :=
  PEqualNP.Outside.L_meta_35418.onFinal
