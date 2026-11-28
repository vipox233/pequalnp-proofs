import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_51292

open PEqualNP.CircuitLowerBounds

def gd (c : List ℕ) (a : ℕ) : ℕ := c.getD a 0

def gcol (op : GateOp) (ins : List ℕ) (c : List ℕ) : ℕ :=
  match op, ins with
  | .and, [] => 63
  | .and, [a] => gd c a
  | .and, [a, b] => gd c a &&& gd c b
  | .or, [] => 0
  | .or, [a] => gd c a
  | .or, [a, b] => gd c a ||| gd c b
  | .not, [] => 63
  | .not, [a] => 63 ^^^ gd c a
  | .not, [a, _] => 63 ^^^ gd c a
  | _, _ => 0

theorem gate_bit (t : ℕ) (ht : t < 6) (w : List Bool) (c : List ℕ)
    (h : ∀ i, w.getD i false = (gd c i).testBit t) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    g.op.eval (g.inputs.map fun i => w.getD i false) = (gcol g.op g.inputs c).testBit t := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  have tfull : (63 : ℕ).testBit t = true := by interval_cases t <;> decide
  have h' : ∀ i, w[i]?.getD false = (gd c i).testBit t := by
    intro i
    simpa using h i
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  dsimp only at hop hlen ⊢
  rcases hop with rfl | rfl | rfl
  · match ins, hlen with
    | [], _ => simp [gcol, GateOp.eval, tfull]
    | [a], _ => simp [gcol, GateOp.eval, h']
    | [a, b], _ => simp [gcol, GateOp.eval, h']
    | _ :: _ :: _ :: _, hl => simp at hl
  · match ins, hlen with
    | [], _ => simp [gcol, GateOp.eval]
    | [a], _ => simp [gcol, GateOp.eval, h']
    | [a, b], _ => simp [gcol, GateOp.eval, h']
    | _ :: _ :: _ :: _, hl => simp at hl
  · match ins, hlen with
    | [], _ => simp [gcol, GateOp.eval, tfull]
    | [a], _ => simp [gcol, GateOp.eval, h', tfull]
    | [a, b], _ => simp [gcol, GateOp.eval, h', tfull]
    | _ :: _ :: _ :: _, hl => simp at hl

theorem sim (t : ℕ) (ht : t < 6) (gs : List Gate) :
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    ∀ (w : List Bool) (c : List ℕ), w.length = c.length →
      (∀ i, w.getD i false = (gd c i).testBit t) →
      ∀ i, ((gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false)
        = (gd (gs.foldl (fun c g => c ++ [gcol g.op g.inputs c]) c) i).testBit t := by
  induction gs with
  | nil => intro _ w c _ h; exact h
  | cons g gs ih =>
    intro hfan w c hl h
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg'))
    · simp [hl]
    · intro i
      have key := gate_bit t ht w c h g (hfan g (by simp))
      unfold gd
      by_cases hi : i < w.length
      · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (hl ▸ hi)]
        exact h i
      · have hw : w.length ≤ i := Nat.le_of_not_lt hi
        rw [List.getD_append_right _ _ _ _ hw, List.getD_append_right _ _ _ _ (hl ▸ hw), hl]
        rcases Nat.eq_zero_or_pos (i - c.length) with h0 | h0
        · rw [h0]; simpa using key
        · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp h0)
          rw [hk]; simp

def has (S : List ℕ) (a : ℕ) : Bool := S.any fun v => v % 64 == a % 64

def miss (a b d : ℕ) (S : List ℕ) : ℕ :=
  (if has S a then 0 else 1) + (if has S b then 0 else 1) + (if has S d then 0 else 1)

def kids (S : List ℕ) : List ℕ :=
  ((S.flatMap fun x => S.flatMap fun y => [x &&& y, x ||| y]).filter fun v => !S.contains v).dedup

def nkids (S : List ℕ) : List ℕ :=
  ((S.map fun x => 63 ^^^ x).filter fun v => !S.contains v).dedup

def search (a b d : ℕ) : ℕ → ℕ → List ℕ → Bool
  | 0, _, S => Nat.beq (miss a b d S) 0
  | f + 1, n, S => Nat.ble (miss a b d S) (f + 1) &&
      (Nat.beq (miss a b d S) 0 || search a b d f n S
        || ((kids S).any fun v => search a b d f n (v :: S))
        || (Nat.ble 1 n && (nkids S).any fun v => search a b d f (n - 1) (v :: S)))

theorem has_mono {c S : List ℕ} (hs : ∀ v ∈ c, v ∈ S) (z : ℕ) (h : has c z = true) : has S z = true := by
  simp only [has, List.any_eq_true] at h ⊢
  obtain ⟨v, hv, hva⟩ := h
  exact ⟨v, hs v hv, hva⟩

theorem miss_mono (a b d : ℕ) {c S : List ℕ} (hs : ∀ v ∈ c, v ∈ S) (h : miss a b d c = 0) :
    miss a b d S = 0 := by
  have key : ∀ z : ℕ, (if has c z then 0 else 1) = 0 → (if has S z then 0 else 1) = 0 := by
    intro z hz
    by_cases h1 : has c z = true
    · simp [has_mono hs z h1]
    · simp [h1] at hz
  unfold miss at h ⊢
  have ha := key a (by omega)
  have hb := key b (by omega)
  have hd := key d (by omega)
  omega

theorem miss_step {a b d : ℕ} (hab : a % 64 ≠ b % 64) (had : a % 64 ≠ d % 64)
    (hbd : b % 64 ≠ d % 64) (v : ℕ) (S : List ℕ) :
    miss a b d S ≤ miss a b d (v :: S) + 1 := by
  have key : ∀ z : ℕ, (if has S z then 0 else 1) ≤
      (if has (v :: S) z then 0 else 1) + (if v % 64 = z % 64 then 1 else 0) := by
    intro z
    have e : has (v :: S) z = (v % 64 == z % 64 || has S z) := by simp [has, List.any_cons]
    rw [e]
    by_cases h2 : v % 64 = z % 64
    · by_cases h1 : has S z = true <;> simp [h1, h2]
    · by_cases h1 : has S z = true <;> simp [h1, h2]
  have ka := key a
  have kb := key b
  have kd := key d
  have h1 : (if v % 64 = a % 64 then 1 else 0) + (if v % 64 = b % 64 then 1 else 0)
      + (if v % 64 = d % 64 then 1 else 0) ≤ 1 := by
    split_ifs <;> omega
  unfold miss
  omega

theorem gd_mem (c S : List ℕ) (hs : ∀ v ∈ c, v ∈ S) (h0 : 0 ∈ S) (a : ℕ) : gd c a ∈ S := by
  unfold gd
  by_cases ha : a < c.length
  · rw [List.getD_eq_getElem _ _ ha]; exact hs _ (List.getElem_mem ha)
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt ha)]; exact h0

theorem mem_kids {S : List ℕ} {x y v : ℕ} (hx : x ∈ S) (hy : y ∈ S)
    (hv : v = x &&& y ∨ v = x ||| y) (hin : v ∉ S) : v ∈ kids S := by
  unfold kids
  rw [List.mem_dedup, List.mem_filter]
  refine ⟨List.mem_flatMap.2 ⟨x, hx, List.mem_flatMap.2 ⟨y, hy, ?_⟩⟩, by simpa using hin⟩
  simpa using hv

theorem mem_nkids {S : List ℕ} {x : ℕ} (hx : x ∈ S) (hin : (63 ^^^ x) ∉ S) :
    (63 ^^^ x) ∈ nkids S := by
  unfold nkids
  rw [List.mem_dedup, List.mem_filter]
  exact ⟨List.mem_map.2 ⟨x, hx, rfl⟩, by simpa using hin⟩

theorem search_of_zero (a b d f n : ℕ) (S : List ℕ) (h : miss a b d S = 0) :
    search a b d f n S = true := by
  cases f with
  | zero => simp [search, h]
  | succ f => simp [search, h]

theorem skip_step (a b d f n : ℕ) (S : List ℕ) (hm : miss a b d S ≤ f + 1)
    (h : search a b d f n S = true) : search a b d (f + 1) n S = true := by
  have hb : Nat.ble (miss a b d S) (f + 1) = true := by simpa using hm
  simp only [search, hb, h, Bool.or_true, Bool.true_or, Bool.true_and]

theorem kid_step (a b d f n : ℕ) (S : List ℕ) (hm : miss a b d S ≤ f + 1) (v : ℕ) (hv : v ∈ kids S)
    (h : search a b d f n (v :: S) = true) : search a b d (f + 1) n S = true := by
  have hb : Nat.ble (miss a b d S) (f + 1) = true := by simpa using hm
  have this : ((kids S).any fun v => search a b d f n (v :: S)) = true :=
    List.any_eq_true.mpr ⟨v, hv, h⟩
  simp only [search, hb, this, Bool.or_true, Bool.true_or, Bool.true_and]

theorem nkid_step (a b d f n : ℕ) (S : List ℕ) (hm : miss a b d S ≤ f + 1) (hn : 1 ≤ n) (v : ℕ)
    (hv : v ∈ nkids S) (h : search a b d f (n - 1) (v :: S) = true) :
    search a b d (f + 1) n S = true := by
  have hb : Nat.ble (miss a b d S) (f + 1) = true := by simpa using hm
  have hn' : Nat.ble 1 n = true := by simpa using hn
  have this : ((nkids S).any fun v => search a b d f (n - 1) (v :: S)) = true :=
    List.any_eq_true.mpr ⟨v, hv, h⟩
  simp only [search, hb, hn', this, Bool.or_true, Bool.true_or, Bool.true_and, Bool.and_true]

theorem nc_tail (g : Gate) (gs : List Gate) :
    PEqualNP.NotBracket.notCount ⟨gs, 0⟩ ≤ PEqualNP.NotBracket.notCount ⟨g :: gs, 0⟩ := by
  unfold PEqualNP.NotBracket.notCount
  simp only [List.filter_cons]
  split
  · simp
  · exact le_rfl

theorem nc_not (ins : List ℕ) (gs : List Gate) :
    PEqualNP.NotBracket.notCount ⟨⟨GateOp.not, ins⟩ :: gs, 0⟩ = PEqualNP.NotBracket.notCount ⟨gs, 0⟩ + 1 := by
  simp [PEqualNP.NotBracket.notCount]

theorem reach_miss {a b d : ℕ} (hab : a % 64 ≠ b % 64) (had : a % 64 ≠ d % 64)
    (hbd : b % 64 ≠ d % 64) (gs : List Gate) :
    ∀ (c S : List ℕ), (∀ v ∈ c, v ∈ S) →
      miss a b d (gs.foldl (fun c g => c ++ [gcol g.op g.inputs c]) c) = 0 →
      miss a b d S ≤ gs.length := by
  induction gs with
  | nil =>
    intro c S hs h
    exact le_of_eq (miss_mono a b d hs h)
  | cons g gs ih =>
    intro c S hs h
    simp only [List.foldl_cons] at h
    have r := ih (c ++ [gcol g.op g.inputs c]) (gcol g.op g.inputs c :: S)
      (by intro v hv'; rcases List.mem_append.mp hv' with h1 | h1
          · exact List.mem_cons_of_mem _ (hs v h1)
          · rw [List.mem_singleton.mp h1]; exact List.mem_cons_self ..) h
    have st := miss_step hab had hbd (gcol g.op g.inputs c) S
    simp only [List.length_cons]
    omega

theorem sound {a b d : ℕ} (hab : a % 64 ≠ b % 64) (had : a % 64 ≠ d % 64)
    (hbd : b % 64 ≠ d % 64) (gs : List Gate) :
    ∀ (c S : List ℕ) (f n : ℕ), (∀ v ∈ c, v ∈ S) → 0 ∈ S → 63 ∈ S →
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      gs.length ≤ f → PEqualNP.NotBracket.notCount ⟨gs, 0⟩ ≤ n →
      miss a b d (gs.foldl (fun c g => c ++ [gcol g.op g.inputs c]) c) = 0 →
      search a b d f n S = true := by
  induction gs with
  | nil =>
    intro c S f n hs _ _ _ _ _ h
    exact search_of_zero a b d f n S (miss_mono a b d hs h)
  | cons g gs ih =>
    intro c S f n hs h0 hfull hfan hlen hnot h
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hlen; omega⟩
    have hlen' : gs.length ≤ f := by simpa using hlen
    have hm : miss a b d S ≤ f + 1 := le_trans (reach_miss hab had hbd (g :: gs) c S hs h) hlen
    have hfan' : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg')
    have hnot' : PEqualNP.NotBracket.notCount ⟨gs, 0⟩ ≤ n := le_trans (nc_tail g gs) hnot
    simp only [List.foldl_cons] at h
    have mem := gd_mem c S hs h0
    by_cases hv : gcol g.op g.inputs c ∈ S
    · exact skip_step a b d f n S hm (ih (c ++ [gcol g.op g.inputs c]) S f n
        (by intro v hv'; rcases List.mem_append.mp hv' with h1 | h1
            · exact hs v h1
            · rw [List.mem_singleton.mp h1]; exact hv) h0 hfull hfan' hlen' hnot' h)
    · have ext : ∀ v ∈ c ++ [gcol g.op g.inputs c], v ∈ gcol g.op g.inputs c :: S := by
        intro v hv'
        rcases List.mem_append.mp hv' with h1 | h1
        · exact List.mem_cons_of_mem _ (hs v h1)
        · rw [List.mem_singleton.mp h1]; exact List.mem_cons_self ..
      have recur : ∀ n', PEqualNP.NotBracket.notCount ⟨gs, 0⟩ ≤ n' →
          search a b d f n' (gcol g.op g.inputs c :: S) = true := fun n' hn' =>
        ih _ (gcol g.op g.inputs c :: S) f n' ext (List.mem_cons_of_mem _ h0)
          (List.mem_cons_of_mem _ hfull) hfan' hlen' hn' h
      obtain ⟨hop, hl⟩ := hfan g (by simp)
      obtain ⟨op, ins⟩ := g
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      dsimp only at hop hl hv recur hnot
      rcases hop with rfl | rfl | rfl
      · match ins, hl with
        | [], _ => exact absurd (by simpa [gcol] using hfull) hv
        | [x], _ => exact absurd (by simpa [gcol] using mem x) hv
        | [x, y], _ =>
          exact kid_step a b d f n S hm _ (mem_kids (mem x) (mem y) (Or.inl rfl) hv) (recur n hnot')
        | _ :: _ :: _ :: _, hl => simp at hl
      · match ins, hl with
        | [], _ => exact absurd (by simpa [gcol] using h0) hv
        | [x], _ => exact absurd (by simpa [gcol] using mem x) hv
        | [x, y], _ =>
          exact kid_step a b d f n S hm _ (mem_kids (mem x) (mem y) (Or.inr rfl) hv) (recur n hnot')
        | _ :: _ :: _ :: _, hl => simp at hl
      · have hn : 1 ≤ n ∧ PEqualNP.NotBracket.notCount ⟨gs, 0⟩ ≤ n - 1 := by
          rw [nc_not] at hnot; omega
        match ins, hl with
        | [], _ => exact absurd (by simpa [gcol] using hfull) hv
        | [x], _ => exact nkid_step a b d f n S hm hn.1 _ (mem_nkids (mem x) hv) (recur (n - 1) hn.2)
        | [x, _], _ => exact nkid_step a b d f n S hm hn.1 _ (mem_nkids (mem x) hv) (recur (n - 1) hn.2)
        | _ :: _ :: _ :: _, hl => simp at hl

theorem base (t : Fin 6) (i : ℕ) :
    (((List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true]).getD i false)
      = (gd [62, 60, 56, 48, 32, 0, 63] i).testBit t.val := by
  unfold gd
  by_cases hi : i < 7
  · interval_cases i <;> fin_cases t <;> decide
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    simp

theorem agree_of (v a : ℕ) (h : ∀ t : Fin 6, v.testBit t.val = a.testBit t.val) :
    (v % 64 == a % 64) = true := by
  have e : v % 2 ^ 6 = a % 2 ^ 6 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
    by_cases hi : i < 6
    · have := h ⟨i, hi⟩
      simp [hi, this]
    · simp [hi]
  simpa using e

theorem grow (gs : List Gate) : ∀ c : List ℕ, 0 ∈ c →
    0 ∈ gs.foldl (fun c g => c ++ [gcol g.op g.inputs c]) c := by
  induction gs with
  | nil => intro c hc; exact hc
  | cons g gs ih => intro c hc; exact ih _ (List.mem_append_left _ hc)

theorem none_of (a b d s : ℕ) (hab : a % 64 ≠ b % 64) (had : a % 64 ≠ d % 64)
    (hbd : b % 64 ≠ d % 64) (rej : search a b d s 2 [62, 60, 56, 48, 32, 0, 63] = false) :
    ¬ (∃ (D : Circuit) (p q r : Fin (7 + D.size)),
      PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
      PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ s ∧
      ∀ t : Fin 6,
        let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true]
        let w := D.wires xs
        w.getD p.val false = (a : ℕ).testBit t.val ∧
        w.getD q.val false = (b : ℕ).testBit t.val ∧
        w.getD r.val false = (d : ℕ).testBit t.val) := by
  rintro ⟨D, p, q, r, hfan, -, hnot, hsize, h⟩
  have col : ∀ (i : ℕ) (t : Fin 6),
      (D.wires ((List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true])).getD i false
        = (gd (D.gates.foldl (fun c g => c ++ [gcol g.op g.inputs c]) [62, 60, 56, 48, 32, 0, 63]) i).testBit t.val :=
    fun i t => sim t.val t.isLt D.gates hfan _ _ (by simp) (base t) i
  have inS : ∀ i : ℕ, gd (D.gates.foldl (fun c g => c ++ [gcol g.op g.inputs c]) [62, 60, 56, 48, 32, 0, 63]) i
      ∈ (D.gates.foldl (fun c g => c ++ [gcol g.op g.inputs c]) [62, 60, 56, 48, 32, 0, 63]) :=
    fun i => gd_mem _ _ (fun v hv => hv) (grow D.gates _ (by decide)) i
  have hh : miss a b d (D.gates.foldl (fun c g => c ++ [gcol g.op g.inputs c]) [62, 60, 56, 48, 32, 0, 63]) = 0 := by
    have h1 : has (D.gates.foldl (fun c g => c ++ [gcol g.op g.inputs c]) [62, 60, 56, 48, 32, 0, 63]) a = true :=
      List.any_eq_true.mpr ⟨_, inS p.val, agree_of _ _ fun t => by rw [← col]; exact (h t).1⟩
    have h2 : has (D.gates.foldl (fun c g => c ++ [gcol g.op g.inputs c]) [62, 60, 56, 48, 32, 0, 63]) b = true :=
      List.any_eq_true.mpr ⟨_, inS q.val, agree_of _ _ fun t => by rw [← col]; exact (h t).2.1⟩
    have h3 : has (D.gates.foldl (fun c g => c ++ [gcol g.op g.inputs c]) [62, 60, 56, 48, 32, 0, 63]) d = true :=
      List.any_eq_true.mpr ⟨_, inS r.val, agree_of _ _ fun t => by rw [← col]; exact (h t).2.2⟩
    simp [miss, h1, h2, h3]
  have := sound hab had hbd D.gates [62, 60, 56, 48, 32, 0, 63] [62, 60, 56, 48, 32, 0, 63] s 2 (fun v hv => hv)
    (by decide) (by decide) hfan hsize hnot hh
  rw [rej] at this
  exact Bool.false_ne_true this

theorem reject : search 2 14 40 5 2 [62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

end PEqualNP.Outside.L_meta_51292

theorem PEqualNP.Outside.L_meta_51292 :
    ¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (2 : Nat).testBit t.val ∧
    w.getD q.val false = (14 : Nat).testBit t.val ∧
    w.getD r.val false = (40 : Nat).testBit t.val) :=
  PEqualNP.Outside.L_meta_51292.none_of 2 14 40 5 (by decide) (by decide) (by decide)
    PEqualNP.Outside.L_meta_51292.reject
