import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_517_aux

def geomSum (B : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => 1 + B * geomSum B m

theorem geomSum_mul_sub_one (B : ℕ) (hB : 1 ≤ B) (m : ℕ) :
    (B - 1) * geomSum B m = B ^ m - 1 := by
  induction m with
  | zero => simp [geomSum]
  | succ m ih =>
    have hpow : 1 ≤ B ^ m := Nat.one_le_pow m B (by omega)
    have hpow1 : 1 ≤ B ^ (m + 1) := Nat.one_le_pow (m + 1) B (by omega)
    simp only [geomSum, Nat.mul_add, Nat.mul_one]
    have hcomm : (B - 1) * (B * geomSum B m) = B * ((B - 1) * geomSum B m) := by ring
    rw [hcomm, ih, Nat.mul_sub_left_distrib, Nat.mul_one, ← Nat.pow_succ']
    have hle : B ≤ B ^ (m + 1) := by
      rw [Nat.pow_succ']
      exact Nat.le_mul_of_pos_right B (by omega)
    change B - 1 + (B ^ (m + 1) - B) = B ^ (m + 1) - 1
    omega

theorem div_full_eq_geomSum {k j : ℕ} (hj : j < k) :
    (2 ^ (2 ^ k) - 1) / (2 ^ (2 * 2 ^ j) - 1) =
      geomSum (2 ^ (2 * 2 ^ j)) (2 ^ (k - (j + 1))) := by
  set run := 2 ^ j
  set B := 2 ^ (2 * run)
  set m := 2 ^ (k - (j + 1))
  have h2run : 2 * run = 2 ^ (j + 1) := by rw [Nat.pow_succ]; omega
  have hmul : 2 * run * m = 2 ^ k := by
    rw [h2run, ← Nat.pow_add, Nat.add_sub_of_le (by omega)]
  have hBpow : B ^ m = 2 ^ (2 ^ k) := by
    dsimp only [B]
    rw [← Nat.pow_mul, hmul]
  have hB2 : 2 ≤ B := by
    dsimp only [B]
    have hpos : 1 ≤ 2 * run := by
      have : 1 ≤ run := Nat.one_le_two_pow
      omega
    exact le_trans (by norm_num : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by omega) hpos)
  have hprod : (B - 1) * geomSum B m = 2 ^ (2 ^ k) - 1 := by
    rw [geomSum_mul_sub_one B (by omega) m, hBpow]
  rw [← hprod, Nat.mul_div_right _ (by omega)]

theorem testBit_mul_geomSum (d a : ℕ) (_hd : 0 < d) (ha : a < 2 ^ d) :
    ∀ m w : ℕ, w < m * d →
      (a * geomSum (2 ^ d) m).testBit w = a.testBit (w % d) := by
  intro m
  induction m with
  | zero => intro w hw; simp at hw
  | succ m ih =>
    intro w hw
    simp only [geomSum, Nat.mul_add, Nat.mul_one]
    have hcomm : a * (2 ^ d * geomSum (2 ^ d) m) = 2 ^ d * (a * geomSum (2 ^ d) m) := by ring
    rw [hcomm, Nat.add_comm, Nat.two_pow_add_eq_or_of_lt ha, Nat.testBit_or, Nat.testBit_two_pow_mul]
    by_cases hlt : w < d
    · have hge : ¬ d ≤ w := by omega
      rw [decide_eq_false hge, Bool.false_and, Bool.false_or, Nat.mod_eq_of_lt hlt]
    · have hge : d ≤ w := by omega
      have ha_zero : a.testBit w = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) hge))
      have hw' : w - d < m * d := by
        rw [Nat.succ_mul] at hw; omega
      have hmod : (w - d) % d = w % d := by
        have h1 : w = (w - d) + d := by omega
        conv_rhs => rw [h1]
        rw [Nat.add_mod_right]
      rw [decide_eq_true hge, Bool.true_and, ha_zero, Bool.or_false, ih (w - d) hw', hmod]

theorem testBit_tile {k j w : ℕ} (hj : j < k) (hw : w < 2 ^ k) :
    let lanes := 2 ^ k
    let full := 2 ^ lanes - 1
    let run := 2 ^ j
    let tile := ((2 ^ run - 1) <<< run) * (full / (2 ^ (2 * run) - 1))
    tile.testBit w = w.testBit j := by
  intro lanes full run tile
  have hrun_pos : 0 < run := Nat.two_pow_pos j
  have h2run : 2 * run = 2 ^ (j + 1) := by rw [Nat.pow_succ]; omega
  have hmul : 2 ^ (k - (j + 1)) * (2 * run) = 2 ^ k := by
    rw [h2run, ← Nat.pow_add, Nat.sub_add_cancel (by omega)]
  have ha_lt : ((2 ^ run - 1) <<< run) < 2 ^ (2 * run) := by
    rw [Nat.shiftLeft_eq]
    have h1 : 2 ^ run - 1 < 2 ^ run := Nat.sub_lt (Nat.two_pow_pos run) (by omega)
    calc (2 ^ run - 1) * 2 ^ run < 2 ^ run * 2 ^ run := Nat.mul_lt_mul_of_pos_right h1 (Nat.two_pow_pos run)
      _ = 2 ^ (2 * run) := by rw [← Nat.pow_add]; congr 1; omega
  dsimp only [tile, full, lanes]
  rw [div_full_eq_geomSum hj]
  rw [testBit_mul_geomSum (2 * run) ((2 ^ run - 1) <<< run) (by omega) ha_lt (2 ^ (k - (j + 1))) w (by rw [hmul]; exact hw)]
  rw [Nat.testBit_shiftLeft]
  set r' := w % (2 * run)
  have hr'_lt : r' < 2 * run := Nat.mod_lt w (by omega)
  have hbit_w : w.testBit j = decide (run ≤ r') := by
    rw [Nat.testBit_eq_decide_div_mod_eq]
    have hdiv : w / run = 2 * (w / (2 * run)) + r' / run := by
      have hdm := Nat.div_add_mod w (2 * run)
      have h1 : 2 * run * (w / (2 * run)) = run * (2 * (w / (2 * run))) := by ring
      have h2 : w = run * (2 * (w / (2 * run))) + r' := by
        dsimp only [r']; omega
      conv_lhs => rw [h2]
      rw [Nat.mul_add_div hrun_pos]
    rw [hdiv, Nat.mul_add_mod]
    by_cases hle : run ≤ r'
    · have hq : r' / run = 1 := by
        have hlo : 1 ≤ r' / run := (Nat.le_div_iff_mul_le hrun_pos).mpr (by omega)
        have hhi : r' / run < 2 := (Nat.div_lt_iff_lt_mul hrun_pos).mpr (by omega)
        omega
      simp [hle, hq]
    · have hq : r' / run = 0 := Nat.div_eq_of_lt (by omega)
      simp [hle, hq]
  rw [hbit_w]
  by_cases hle : run ≤ r'
  · simp only [ge_iff_le, hle, decide_true, Bool.true_and, Nat.testBit_two_pow_sub_one]
    exact decide_eq_true (by omega)
  · simp [hle]

theorem testBit_keyPlane {k : ℕ} (hk : 0 < k) (shift : Fin (2 ^ k)) (pos : ℕ) (w : Fin (2 ^ k)) :
    let lanes := 2 ^ k
    let full := 2 ^ lanes - 1
    let run := 2 ^ (pos % k)
    let tile := ((2 ^ run - 1) <<< run) * (full / (2 ^ (2 * run) - 1))
    let kp := if shift.val.testBit (pos % k) then full ^^^ tile else tile
    kp.testBit w.val = (w.val ^^^ shift.val).testBit (pos % k) := by
  intro lanes full run tile kp
  have hj : pos % k < k := Nat.mod_lt pos hk
  have htile : tile.testBit w.val = w.val.testBit (pos % k) := testBit_tile hj w.isLt
  have hfull : full.testBit w.val = true := by
    dsimp only [full, lanes]
    rw [Nat.testBit_two_pow_sub_one]
    exact decide_eq_true w.isLt
  rw [Nat.testBit_xor]
  dsimp only [kp]
  cases hs : shift.val.testBit (pos % k)
  · simp [htile]
  · simp [Nat.testBit_xor, hfull, htile]

theorem testBit_rot {k : ℕ} (hk : 0 < k) (s word : ℕ) (hword : word < 2 ^ k) (i : ℕ) (hi : i < k) :
    (((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k).testBit i =
      word.testBit ((i + k - s % k) % k) := by
  set s' := s % k
  have hs' : s' < k := Nat.mod_lt s hk
  rw [Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and,
      Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  by_cases hle : s' ≤ i
  · have hhi : word.testBit (k - s' + i) = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hword (Nat.pow_le_pow_right (by omega) (by omega)))
    have hidx : (i + k - s') % k = i - s' := by
      have h1 : i + k - s' = (i - s') + k := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [decide_eq_true hle, Bool.true_and, hhi, Bool.or_false, hidx]
  · have hlt : i < s' := by omega
    have hidx : (i + k - s') % k = k - s' + i := by
      have h1 : i + k - s' = k - s' + i := by omega
      rw [h1, Nat.mod_eq_of_lt (by omega)]
    rw [decide_eq_false (by omega), Bool.false_and, Bool.false_or, hidx]

theorem source_k_sub_gap {k gap : ℕ} (hgap : gap ≤ k) (j : ℕ) :
    (j % k + k - (k - gap) % k) % k = (j + gap) % k := by
  by_cases hgk : gap = k
  · subst hgk
    simp only [Nat.sub_self, Nat.zero_mod, Nat.sub_zero, Nat.add_mod_right, Nat.mod_mod]
  · by_cases hgap0 : gap = 0
    · subst hgap0
      simp only [Nat.sub_zero, Nat.mod_self, Nat.sub_zero, Nat.add_mod_right, Nat.mod_mod, Nat.add_zero]
    · have hlt : k - gap < k := by omega
      rw [Nat.mod_eq_of_lt hlt]
      have h1 : j % k + k - (k - gap) = j % k + gap := by omega
      rw [h1, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

theorem source_mod_left {k : ℕ} (j amount : ℕ) :
    (j % k + k - amount % k) % k = (j + k - amount % k) % k := by
  by_cases hk : k = 0
  · subst hk; simp
  · have ha : amount % k < k := Nat.mod_lt amount (by omega)
    have h1 : j % k + k - amount % k = j % k + (k - amount % k) := by omega
    have h2 : j + k - amount % k = j + (k - amount % k) := by omega
    rw [h1, h2, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

def stepPrefix (k raw : ℕ) (m : ℕ) : ℕ :=
  (List.range m).foldl (fun acc b =>
    acc ||| ((xor (raw.testBit b)
      (!(raw.testBit ((b + 1) % k)) && raw.testBit ((b + 2) % k))).toNat <<< b)) 0

theorem stepPrefix_spec (k raw : ℕ) : ∀ m : ℕ,
    stepPrefix k raw m < 2 ^ m ∧
    ∀ i : ℕ, (stepPrefix k raw m).testBit i =
      if i < m then xor (raw.testBit i)
        (!(raw.testBit ((i + 1) % k)) && raw.testBit ((i + 2) % k))
      else false := by
  intro m
  induction m with
  | zero =>
    refine ⟨by simp [stepPrefix], fun i => by simp [stepPrefix]⟩
  | succ m ih =>
    rcases ih with ⟨hlt, hbit⟩
    set bitVal : Bool := xor (raw.testBit m) (!(raw.testBit ((m + 1) % k)) && raw.testBit ((m + 2) % k))
    have hstep : stepPrefix k raw (m + 1) = stepPrefix k raw m ||| (bitVal.toNat <<< m) := by
      dsimp only [stepPrefix]
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hstep]
    have hsh_lt : (bitVal.toNat <<< m) < 2 ^ (m + 1) := by
      rw [Nat.shiftLeft_eq, Nat.pow_succ']
      cases bitVal <;> simp [Bool.toNat]
    have hlt1 : stepPrefix k raw m < 2 ^ (m + 1) :=
      lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) (by omega))
    refine ⟨Nat.or_lt_two_pow hlt1 hsh_lt, fun i => ?_⟩
    rw [Nat.testBit_or, hbit i, Nat.testBit_shiftLeft]
    by_cases him : i < m
    · have him1 : i < m + 1 := by omega
      simp only [him, him1, ↓reduceIte, decide_eq_false (show ¬ m ≤ i by omega), Bool.false_and, Bool.or_false]
    · by_cases hieq : i = m
      · subst hieq
        simp only [lt_irrefl, ↓reduceIte, Nat.lt_succ_self, ge_iff_le, le_refl, decide_true,
          Bool.true_and, Nat.sub_self, Bool.false_or]
        change bitVal.toNat.testBit 0 = bitVal
        cases bitVal <;> rfl
      · have hgt : m < i := by omega
        have hnot1 : ¬ i < m + 1 := by omega
        have hbm : bitVal.toNat.testBit (i - m) = false := by
          apply Nat.testBit_lt_two_pow
          have h1 : bitVal.toNat < 2 ^ 1 := by cases bitVal <;> decide
          exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by omega) (by omega))
        simp only [him, hnot1, ↓reduceIte, hbm, Bool.and_false, Bool.or_false]

theorem array_ofFn_getD {α : Type*} [Inhabited α] {n : ℕ} (f : Fin n → α) (i : ℕ) (hi : i < n) (d : α) :
    (Array.ofFn f).getD i d = f ⟨i, hi⟩ := by
  simp [Array.getD, hi]

theorem full_xor_testBit {lanes x w : ℕ} (hw : w < lanes) :
    ((2 ^ lanes - 1) ^^^ x).testBit w = !(x.testBit w) := by
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, decide_eq_true hw, Bool.true_xor]

theorem full_ite_testBit {lanes w : ℕ} (b : Bool) (hw : w < lanes) :
    (if b then 2 ^ lanes - 1 else 0).testBit w = b := by
  cases b
  · simp
  · simp [Nat.testBit_two_pow_sub_one, hw]

theorem main_proof : ∀ (k r : ℕ), 2 ≤ k → ∀ (column : Bool) (name shift : Fin (2 ^ k)),
  let lanes := 2 ^ k
  let full := 2 ^ lanes - 1
  let keyPlane := fun pos : ℕ =>
    let run := 2 ^ (pos % k)
    let tile := ((2 ^ run - 1) <<< run) * (full / (2 ^ (2 * run) - 1))
    if shift.val.testBit (pos % k) then full ^^^ tile else tile
  let gap : ℕ := if column then 2 else 1
  let start : ℕ := if column then 3 else 1
  let offset := fun roundIdx : ℕ => if column then 3 * (roundIdx + 1) + 1 else 2 * roundIdx
  let constant := fun time : ℕ =>
    3 ^ (k + (if column then r + (time + 1) else time + 1)) % lanes
  let source := fun (index amount : ℕ) => (index + k - amount % k) % k
  let initial := Array.ofFn (fun site : Fin k =>
    keyPlane (source site.val start) ^^^ (if name.val.testBit site.val then full else 0))
  let planes := (List.range r).foldl (fun (old : Array ℕ) roundNo =>
    let mixed := fun j : ℕ =>
      old.getD (j % k) 0 ^^^ old.getD (source j gap) 0 ^^^ old.getD ((j + gap) % k) 0
    Array.ofFn (fun bit : Fin k =>
      (mixed bit.val ^^^ ((full ^^^ mixed (bit.val + 1)) &&& mixed (bit.val + 2))) ^^^
      keyPlane (source bit.val (offset roundNo)) ^^^
      (if (constant roundNo).testBit bit.val then full else 0))) initial
  let rot := fun (s word : ℕ) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % lanes
  let step := fun raw : ℕ =>
    (List.range k).foldl (fun acc b =>
      acc ||| ((xor (raw.testBit b)
        (!(raw.testBit ((b + 1) % k)) && raw.testBit ((b + 2) % k))).toNat <<< b)) 0
  let scalar := fun w : Fin lanes =>
    let key := w.val ^^^ shift.val
    (List.range r).foldl (fun x t =>
      step (x ^^^ rot gap x ^^^ rot (k - gap) x) ^^^ rot (offset t) key ^^^ constant t)
      (rot start key ^^^ name.val)
  (∀ (i : Fin k) (w : Fin lanes),
    (planes.getD i.val 0).testBit w.val = (scalar w).testBit i.val) ∧
  ∀ (h : ℕ), h ≤ k → ∀ target : Fin (2 ^ h),
    let mask := (List.range h).foldl (fun selected digit =>
      let plane := planes.getD (k - h + digit) 0
      selected &&& (if target.val.testBit digit then plane else full ^^^ plane)) full
    ∀ lane : Fin lanes, mask.testBit lane.val =
      decide (scalar lane >>> (k - h) = target.val) := by
  intro k r hk column name shift lanes full keyPlane gap start offset constant source initial planes rot step scalar
  have hk0 : 0 < k := by omega
  have hgap_le : gap ≤ k := by cases column <;> dsimp [gap] <;> omega
  have hlanes_pos : 0 < lanes := Nat.two_pow_pos k
  let planesAt : ℕ → Array ℕ := fun t =>
    (List.range t).foldl (fun (old : Array ℕ) roundNo =>
      let mixed := fun j : ℕ =>
        old.getD (j % k) 0 ^^^ old.getD (source j gap) 0 ^^^ old.getD ((j + gap) % k) 0
      Array.ofFn (fun bit : Fin k =>
        (mixed bit.val ^^^ ((full ^^^ mixed (bit.val + 1)) &&& mixed (bit.val + 2))) ^^^
        keyPlane (source bit.val (offset roundNo)) ^^^
        (if (constant roundNo).testBit bit.val then full else 0))) initial
  let scalarAt : ℕ → Fin lanes → ℕ := fun t w =>
    let key := w.val ^^^ shift.val
    (List.range t).foldl (fun x roundNo =>
      step (x ^^^ rot gap x ^^^ rot (k - gap) x) ^^^ rot (offset roundNo) key ^^^ constant roundNo)
      (rot start key ^^^ name.val)
  have hkey_lt : ∀ w : Fin lanes, w.val ^^^ shift.val < 2 ^ k := fun w =>
    Nat.xor_lt_two_pow w.isLt shift.isLt
  have hrot_lt : ∀ s word : ℕ, rot s word < 2 ^ k := fun s word =>
    Nat.mod_lt _ hlanes_pos
  have hconst_lt : ∀ t : ℕ, constant t < 2 ^ k := fun t =>
    Nat.mod_lt _ hlanes_pos
  have hstep_eq : ∀ raw : ℕ, step raw = stepPrefix k raw k := fun _ => rfl
  have hstep_lt : ∀ raw : ℕ, step raw < 2 ^ k := fun raw => (stepPrefix_spec k raw k).1
  have hround_inv : ∀ t : ℕ,
      (∀ w : Fin lanes, scalarAt t w < 2 ^ k) ∧
      (∀ (i : Fin k) (w : Fin lanes), ((planesAt t).getD i.val 0).testBit w.val = (scalarAt t w).testBit i.val) := by
    intro t
    induction t with
    | zero =>
      constructor
      · intro w
        dsimp only [scalarAt, List.range_zero, List.foldl_nil]
        exact Nat.xor_lt_two_pow (hrot_lt start (w.val ^^^ shift.val)) name.isLt
      · intro i w
        dsimp only [planesAt, scalarAt, List.range_zero, List.foldl_nil, initial]
        rw [array_ofFn_getD _ i.val i.isLt 0]
        rw [Nat.testBit_xor, Nat.testBit_xor, full_ite_testBit _ w.isLt]
        have hkp := testBit_keyPlane hk0 shift (source i.val start) w
        have hsrc_lt : source i.val start < k := Nat.mod_lt _ hk0
        have hsrc_mod : source i.val start % k = source i.val start := Nat.mod_eq_of_lt hsrc_lt
        have hrt := testBit_rot hk0 start (w.val ^^^ shift.val) (hkey_lt w) i.val i.isLt
        dsimp only [keyPlane, rot, lanes, full] at hkp hrt ⊢
        rw [hkp, hsrc_mod, hrt]
    | succ t ih =>
      rcases ih with ⟨hscal_lt, hbit_ih⟩
      have hpl_step : planesAt (t + 1) =
          let old := planesAt t
          let mixed := fun j : ℕ =>
            old.getD (j % k) 0 ^^^ old.getD (source j gap) 0 ^^^ old.getD ((j + gap) % k) 0
          Array.ofFn (fun bit : Fin k =>
            (mixed bit.val ^^^ ((full ^^^ mixed (bit.val + 1)) &&& mixed (bit.val + 2))) ^^^
            keyPlane (source bit.val (offset t)) ^^^
            (if (constant t).testBit bit.val then full else 0)) := by
        dsimp only [planesAt]
        rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hsc_step : ∀ w : Fin lanes, scalarAt (t + 1) w =
          let x := scalarAt t w
          let key := w.val ^^^ shift.val
          step (x ^^^ rot gap x ^^^ rot (k - gap) x) ^^^ rot (offset t) key ^^^ constant t := by
        intro w
        dsimp only [scalarAt]
        rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      constructor
      · intro w
        rw [hsc_step w]
        exact Nat.xor_lt_two_pow
          (Nat.xor_lt_two_pow (hstep_lt _) (hrot_lt (offset t) (w.val ^^^ shift.val)))
          (hconst_lt t)
      · intro i w
        rw [hpl_step, hsc_step w]
        dsimp only
        rw [array_ofFn_getD _ i.val i.isLt 0]
        set x := scalarAt t w
        set raw := x ^^^ rot gap x ^^^ rot (k - gap) x
        have hx_lt : x < 2 ^ k := hscal_lt w
        have hmix_bit : ∀ j : ℕ,
            ((planesAt t).getD (j % k) 0 ^^^ (planesAt t).getD (source j gap) 0 ^^^
              (planesAt t).getD ((j + gap) % k) 0).testBit w.val = raw.testBit (j % k) := by
          intro j
          have hj1 : j % k < k := Nat.mod_lt j hk0
          have hj2 : source j gap < k := Nat.mod_lt _ hk0
          have hj3 : (j + gap) % k < k := Nat.mod_lt _ hk0
          rw [Nat.testBit_xor, Nat.testBit_xor,
              hbit_ih ⟨j % k, hj1⟩ w, hbit_ih ⟨source j gap, hj2⟩ w, hbit_ih ⟨(j + gap) % k, hj3⟩ w]
          dsimp only [raw]
          rw [Nat.testBit_xor, Nat.testBit_xor]
          have hr1 := testBit_rot hk0 gap x hx_lt (j % k) hj1
          have hr2 := testBit_rot hk0 (k - gap) x hx_lt (j % k) hj1
          dsimp only [rot, lanes] at hr1 hr2 ⊢
          rw [hr1, hr2, source_mod_left j gap, source_k_sub_gap hgap_le j]
        have himod : i.val % k = i.val := Nat.mod_eq_of_lt i.isLt
        rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_and,
            full_xor_testBit w.isLt, full_ite_testBit _ w.isLt,
            hmix_bit i.val, hmix_bit (i.val + 1), hmix_bit (i.val + 2), himod]
        have hkp := testBit_keyPlane hk0 shift (source i.val (offset t)) w
        have hsrc_lt : source i.val (offset t) < k := Nat.mod_lt _ hk0
        have hsrc_mod : source i.val (offset t) % k = source i.val (offset t) := Nat.mod_eq_of_lt hsrc_lt
        have hrt := testBit_rot hk0 (offset t) (w.val ^^^ shift.val) (hkey_lt w) i.val i.isLt
        have hst := (stepPrefix_spec k raw k).2 i.val
        simp only [i.isLt, ↓reduceIte] at hst
        dsimp only [keyPlane, rot, lanes, full] at hkp hrt ⊢
        rw [hkp, hsrc_mod]
        conv_rhs => rw [Nat.testBit_xor, Nat.testBit_xor, hrt]
        change xor (xor (xor (raw.testBit i.val) (!(raw.testBit ((i.val + 1) % k)) && raw.testBit ((i.val + 2) % k)))
            ((w.val ^^^ shift.val).testBit (source i.val (offset t)))) ((constant t).testBit i.val) =
          xor (xor ((stepPrefix k raw k).testBit i.val)
            ((w.val ^^^ shift.val).testBit (source i.val (offset t)))) ((constant t).testBit i.val)
        rw [hst]
  rcases hround_inv r with ⟨hscal_r_lt, hpart1⟩
  refine ⟨hpart1, ?_⟩
  intro h hh target mask lane
  let maskAt : ℕ → ℕ := fun d =>
    (List.range d).foldl (fun selected digit =>
      let plane := planes.getD (k - h + digit) 0
      selected &&& (if target.val.testBit digit then plane else full ^^^ plane)) full
  have hmask_spec : ∀ d ≤ h,
      (maskAt d).testBit lane.val = true ↔
        ∀ digit < d, (scalar lane).testBit (k - h + digit) = target.val.testBit digit := by
    intro d
    induction d with
    | zero =>
      intro _
      dsimp only [maskAt, List.range_zero, List.foldl_nil, full, lanes]
      rw [Nat.testBit_two_pow_sub_one, decide_eq_true lane.isLt]
      simp
    | succ d ih =>
      intro hd
      have hstep : maskAt (d + 1) =
          maskAt d &&& (if target.val.testBit d then planes.getD (k - h + d) 0
            else full ^^^ planes.getD (k - h + d) 0) := by
        dsimp only [maskAt]
        rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [hstep, Nat.testBit_and, Bool.and_eq_true, ih (by omega)]
      have hidx : k - h + d < k := by omega
      have hp : (planes.getD (k - h + d) 0).testBit lane.val = (scalar lane).testBit (k - h + d) :=
        hpart1 ⟨k - h + d, hidx⟩ lane
      have hchoice : (if target.val.testBit d then planes.getD (k - h + d) 0
          else full ^^^ planes.getD (k - h + d) 0).testBit lane.val = true ↔
          (scalar lane).testBit (k - h + d) = target.val.testBit d := by
        cases ht : target.val.testBit d
        · simp only [Bool.false_eq_true, ↓reduceIte]
          dsimp only [full, lanes]
          rw [full_xor_testBit lane.isLt, hp]
          cases (scalar lane).testBit (k - h + d) <;> decide
        · simp only [↓reduceIte, hp]
      rw [hchoice]
      constructor
      · rintro ⟨hprev, hcur⟩ digit hdig
        by_cases heq : digit = d
        · subst heq; exact hcur
        · exact hprev digit (by omega)
      · intro hall
        exact ⟨fun digit hdig => hall digit (by omega), hall d (Nat.lt_succ_self d)⟩
  have hiff : mask.testBit lane.val = true ↔ scalar lane >>> (k - h) = target.val := by
    change (maskAt h).testBit lane.val = true ↔ _
    rw [hmask_spec h le_rfl]
    constructor
    · intro hall
      apply Nat.eq_of_testBit_eq
      intro digit
      rw [Nat.testBit_shiftRight]
      by_cases hd : digit < h
      · exact hall digit hd
      · have h1 : (scalar lane).testBit (k - h + digit) = false :=
          Nat.testBit_lt_two_pow (lt_of_lt_of_le (hscal_r_lt lane) (Nat.pow_le_pow_right (by omega) (by omega)))
        have h2 : target.val.testBit digit = false :=
          Nat.testBit_lt_two_pow (lt_of_lt_of_le target.isLt (Nat.pow_le_pow_right (by omega) (by omega)))
        rw [h1, h2]
    · intro heq digit hd
      have := congrArg (fun n => n.testBit digit) heq
      rw [Nat.testBit_shiftRight] at this
      exact this
  cases hm : mask.testBit lane.val
  · symm; apply decide_eq_false; intro heq
    have := hiff.mpr heq; rw [hm] at this; cases this
  · symm; apply decide_eq_true; exact hiff.mp hm

end PEqualNP.Outside.L_lib_517_aux

theorem PEqualNP.Outside.L_lib_517 : (∀ (k r : ℕ), 2 ≤ k → ∀ (column : Bool) (name shift : Fin (2 ^ k)),
  let lanes := 2 ^ k
  let full := 2 ^ lanes - 1
  let keyPlane := fun pos : ℕ =>
    let run := 2 ^ (pos % k)
    let tile := ((2 ^ run - 1) <<< run) * (full / (2 ^ (2 * run) - 1))
    if shift.val.testBit (pos % k) then full ^^^ tile else tile
  let gap : ℕ := if column then 2 else 1
  let start : ℕ := if column then 3 else 1
  let offset := fun roundIdx : ℕ => if column then 3 * (roundIdx + 1) + 1 else 2 * roundIdx
  let constant := fun time : ℕ =>
    3 ^ (k + (if column then r + (time + 1) else time + 1)) % lanes
  let source := fun (index amount : ℕ) => (index + k - amount % k) % k
  let initial := Array.ofFn (fun site : Fin k =>
    keyPlane (source site.val start) ^^^ (if name.val.testBit site.val then full else 0))
  let planes := (List.range r).foldl (fun (old : Array ℕ) roundNo =>
    let mixed := fun j : ℕ =>
      old.getD (j % k) 0 ^^^ old.getD (source j gap) 0 ^^^ old.getD ((j + gap) % k) 0
    Array.ofFn (fun bit : Fin k =>
      (mixed bit.val ^^^ ((full ^^^ mixed (bit.val + 1)) &&& mixed (bit.val + 2))) ^^^
      keyPlane (source bit.val (offset roundNo)) ^^^
      (if (constant roundNo).testBit bit.val then full else 0))) initial
  let rot := fun (s word : ℕ) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % lanes
  let step := fun raw : ℕ =>
    (List.range k).foldl (fun acc b =>
      acc ||| ((xor (raw.testBit b)
        (!(raw.testBit ((b + 1) % k)) && raw.testBit ((b + 2) % k))).toNat <<< b)) 0
  let scalar := fun w : Fin lanes =>
    let key := w.val ^^^ shift.val
    (List.range r).foldl (fun x t =>
      step (x ^^^ rot gap x ^^^ rot (k - gap) x) ^^^ rot (offset t) key ^^^ constant t)
      (rot start key ^^^ name.val)
  (∀ (i : Fin k) (w : Fin lanes),
    (planes.getD i.val 0).testBit w.val = (scalar w).testBit i.val) ∧
  ∀ (h : ℕ), h ≤ k → ∀ target : Fin (2 ^ h),
    let mask := (List.range h).foldl (fun selected digit =>
      let plane := planes.getD (k - h + digit) 0
      selected &&& (if target.val.testBit digit then plane else full ^^^ plane)) full
    ∀ lane : Fin lanes, mask.testBit lane.val =
      decide (scalar lane >>> (k - h) = target.val)) :=
  PEqualNP.Outside.L_lib_517_aux.main_proof
