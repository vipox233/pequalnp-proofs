import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33684_aux

def packBits : (k : Nat) → (Fin k → Bool) → Nat
  | 0, _ => 0
  | k + 1, v => (v 0).toNat + 2 * packBits k (fun i => v i.succ)

theorem packBits_lt : ∀ (k : Nat) (v : Fin k → Bool), packBits k v < 2 ^ k
  | 0, _ => by simp [packBits]
  | k + 1, v => by
    have ih := packBits_lt k (fun i => v i.succ)
    cases hv : v 0 <;> simp [packBits, hv, Nat.pow_succ] <;> omega

theorem packBits_testBit : ∀ (k : Nat) (v : Fin k → Bool) (p : Nat) (hp : p < k),
    (packBits k v).testBit p = v ⟨p, hp⟩
  | 0, _, _, hp => by omega
  | k + 1, v, 0, _ => by
    cases hv : v 0
    · simp [packBits, hv, Nat.testBit_zero]
    · simp [packBits, hv, Nat.testBit_zero, Nat.add_mod]
  | k + 1, v, p + 1, hp => by
    have ih := packBits_testBit k (fun i => v i.succ) p (by omega)
    cases hv : v 0
    · simp only [packBits, hv, Bool.toNat_false, Nat.zero_add]
      rw [Nat.testBit_succ]
      have hdiv : (2 * packBits k (fun i => v i.succ)) / 2 = packBits k (fun i => v i.succ) := by omega
      rw [hdiv, ih]
      rfl
    · simp only [packBits, hv, Bool.toNat_true]
      rw [Nat.testBit_succ]
      have hdiv : (1 + 2 * packBits k (fun i => v i.succ)) / 2 = packBits k (fun i => v i.succ) := by omega
      rw [hdiv, ih]
      rfl

def rotFn (k s z : Nat) : Nat :=
  ((z <<< (s % k)) ||| (z >>> (k - s % k))) % 2 ^ k

def mixFn (k d z : Nat) : Nat :=
  z ^^^ rotFn k d z ^^^ rotFn k (k - d) z

def atSite (k start i : Nat) : Nat :=
  (start + i) % k

theorem rotFn_lt (k s z : Nat) : rotFn k s z < 2 ^ k :=
  Nat.mod_lt _ (Nat.two_pow_pos k)

theorem rotFn_zero (k s : Nat) : rotFn k s 0 = 0 := by
  simp [rotFn]

theorem mixFn_zero (k d : Nat) : mixFn k d 0 = 0 := by
  simp [mixFn, rotFn_zero]

theorem testBit_false_of_lt_pow {z k m : Nat} (hz : z < 2 ^ k) (hm : k ≤ m) :
    z.testBit m = false := by
  have hpow : 2 ^ k ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) hm
  have hdiv : z / 2 ^ m = 0 := Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hz hpow)
  simp [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv]

theorem rotFn_testBit {k s z p : Nat} (hk : 0 < k) (hz : z < 2 ^ k) (hp : p < k) :
    (rotFn k s z).testBit p = z.testBit ((p + k - s % k) % k) := by
  unfold rotFn
  rw [Nat.testBit_mod_two_pow]
  simp only [hp, decide_true, Bool.true_and, Nat.testBit_or, Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight]
  have hs : s % k < k := Nat.mod_lt s hk
  by_cases hle : s % k ≤ p
  · have hge : k ≤ k - s % k + p := by omega
    have hhi : z.testBit (k - s % k + p) = false := testBit_false_of_lt_pow hz hge
    have hidx : (p + k - s % k) % k = p - s % k := by
      have h1 : p + k - s % k = (p - s % k) + k := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    simp [hle, hhi, hidx]
  · have hidx : (p + k - s % k) % k = k - s % k + p := by
      have h1 : p + k - s % k = k - s % k + p := by omega
      rw [h1, Nat.mod_eq_of_lt (by omega)]
    simp [hle, hidx]

theorem mixFn_testBit {k d z p : Nat} (hd : 0 < d) (hdk : d < k) (hz : z < 2 ^ k) (hp : p < k) :
    (mixFn k d z).testBit p =
      xor (xor (z.testBit p) (z.testBit ((p + k - d) % k))) (z.testBit ((p + d) % k)) := by
  have hk : 0 < k := by omega
  unfold mixFn
  rw [Nat.testBit_xor, Nat.testBit_xor, rotFn_testBit hk hz hp, rotFn_testBit hk hz hp]
  have hdmod : d % k = d := Nat.mod_eq_of_lt hdk
  have hkdmod : (k - d) % k = k - d := Nat.mod_eq_of_lt (by omega)
  have hpd : p + k - (k - d) = p + d := by omega
  rw [hdmod, hkdmod, hpd]

theorem xor_six (a1 a2 a3 b1 b2 b3 : Bool) :
    xor (xor (xor a1 b1) (xor a2 b2)) (xor a3 b3) =
      xor (xor (xor a1 a2) a3) (xor (xor b1 b2) b3) := by
  cases a1 <;> cases a2 <;> cases a3 <;> cases b1 <;> cases b2 <;> cases b3 <;> rfl

theorem mixFn_xor_testBit {k d w u p : Nat} (hd : 0 < d) (hdk : d < k)
    (hw : w < 2 ^ k) (hu : u < 2 ^ k) (hp : p < k) :
    (mixFn k d (w ^^^ u)).testBit p = xor ((mixFn k d w).testBit p) ((mixFn k d u).testBit p) := by
  have hwu : w ^^^ u < 2 ^ k := Nat.xor_lt_two_pow hw hu
  rw [mixFn_testBit hd hdk hwu hp, mixFn_testBit hd hdk hw hp, mixFn_testBit hd hdk hu hp]
  simp only [Nat.testBit_xor]
  exact xor_six _ _ _ _ _ _

theorem mod_shift_cancel {k start r : Nat} (hr : r < k) :
    ((start + r) % k + k - start % k) % k = r := by
  have hk : 0 < k := by omega
  have hst : start % k < k := Nat.mod_lt start hk
  have hadd : (start + r) % k = (start % k + r) % k := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt hr]
  rw [hadd]
  by_cases hlt : start % k + r < k
  · rw [Nat.mod_eq_of_lt hlt]
    have h1 : start % k + r + k - start % k = r + k := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hr]
  · have hsub : (start % k + r) % k = start % k + r - k := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hsub]
    have h1 : start % k + r - k + k - start % k = r := by omega
    rw [h1, Nat.mod_eq_of_lt hr]

def stripOf (k d a start u : Nat) : Fin (a + 2) → Bool :=
  fun s => (mixFn k d u).testBit (atSite k start s.val)

def solveW (d a : Nat) (hd : 0 < d) (m : Fin (a + 2) → Bool) (idx : Nat) : Bool :=
  if h1 : d ≤ idx then
    if h2 : idx - d < a + 2 then
      let s := idx - d
      let prev := if s < d then false else solveW d a hd m (s - d)
      xor (m ⟨s, h2⟩) (xor (solveW d a hd m s) prev)
    else
      false
  else
    false
termination_by idx
decreasing_by
  all_goals omega

theorem solveW_ge (d a : Nat) (hd : 0 < d) (m : Fin (a + 2) → Bool) {idx : Nat}
    (h : d + a + 2 ≤ idx) : solveW d a hd m idx = false := by
  conv_lhs => rw [solveW]
  have h1 : d ≤ idx := by omega
  have h2 : ¬ idx - d < a + 2 := by omega
  simp [h1, h2]

theorem solveW_step (d a : Nat) (hd : 0 < d) (m : Fin (a + 2) → Bool) (s : Fin (a + 2)) :
    solveW d a hd m (d + s.val) =
      xor (m s) (xor (solveW d a hd m s.val) (if s.val < d then false else solveW d a hd m (s.val - d))) := by
  conv_lhs => rw [solveW]
  have h1 : d ≤ d + s.val := by omega
  have h2 : d + s.val - d < a + 2 := by omega
  rw [dif_pos h1, dif_pos h2]
  dsimp only
  have hsub : d + s.val - d = s.val := by omega
  have hfin : (⟨d + s.val - d, h2⟩ : Fin (a + 2)) = s := Fin.ext hsub
  rw [hfin]
  simp only [hsub]

theorem xor_cancel_right (x y : Bool) : xor y (xor x y) = x := by
  cases x <;> cases y <;> rfl

theorem stripOf_surj {k d a start : Nat} (hd : 0 < d) (hk : a + 2 + 2 * d ≤ k)
    (m : Fin (a + 2) → Bool) :
    ∃ u < 2 ^ k, stripOf k d a start u = m := by
  have hkpos : 0 < k := by omega
  have hdk : d < k := by omega
  let v : Fin k → Bool := fun p => solveW d a hd m ((p.val + k - start % k) % k)
  refine ⟨packBits k v, packBits_lt k v, ?_⟩
  have hu : packBits k v < 2 ^ k := packBits_lt k v
  have hshift : ∀ r, r < k → (packBits k v).testBit ((start + r) % k) = solveW d a hd m r := by
    intro r hr
    rw [packBits_testBit k v ((start + r) % k) (Nat.mod_lt _ hkpos)]
    show solveW d a hd m (((start + r) % k + k - start % k) % k) = solveW d a hd m r
    rw [mod_shift_cancel hr]
  funext s
  unfold stripOf atSite
  have hp : (start + s.val) % k < k := Nat.mod_lt _ hkpos
  rw [mixFn_testBit hd hdk hu hp]
  have h0 : (packBits k v).testBit ((start + s.val) % k) = solveW d a hd m s.val :=
    hshift s.val (by omega)
  have hplus_idx : ((start + s.val) % k + d) % k = (start + (d + s.val)) % k := by
    rw [Nat.mod_add_mod]
    congr 1
    omega
  have h2 : (packBits k v).testBit (((start + s.val) % k + d) % k) = solveW d a hd m (d + s.val) := by
    rw [hplus_idx]
    exact hshift (d + s.val) (by omega)
  have h1 : (packBits k v).testBit (((start + s.val) % k + k - d) % k) =
      if s.val < d then false else solveW d a hd m (s.val - d) := by
    have hrew : (start + s.val) % k + k - d = (start + s.val) % k + (k - d) := by omega
    rw [hrew, Nat.mod_add_mod]
    by_cases hsd : s.val < d
    · have hidx : start + s.val + (k - d) = start + (k - d + s.val) := by omega
      rw [hidx, hshift (k - d + s.val) (by omega)]
      simp only [hsd, ite_true]
      exact solveW_ge d a hd m (by omega)
    · have hidx : start + s.val + (k - d) = start + (s.val - d) + k := by omega
      rw [hidx, Nat.add_mod_right, hshift (s.val - d) (by omega)]
      simp only [hsd, ite_false]
  rw [h0, h1, h2, solveW_step d a hd m s]
  exact xor_cancel_right _ _

def labelFn (k d start init last c u x j : Nat) : Bool :=
  let y := mixFn k d (rotFn k init (x % 2 ^ k) ^^^ u)
  let s := atSite k start
  xor (xor (y.testBit (s j))
    (!(y.testBit (s (j + 1))) && y.testBit (s (j + 2))))
    (xor ((rotFn k last (x % 2 ^ k)).testBit (s j)) (c.testBit (s j)))

def blockFn (k d start init last c u x offset len : Nat) : Finset Nat :=
  (Finset.range len).filter (fun i => labelFn k d start init last c u x (offset + i))

def extrasFn (k d a h start init last c q : Nat)
    (key : Finset Nat → Fin q → Nat) (sensors : Finset Nat → Fin q → Finset Nat)
    (u : Nat) : Fin q → Finset Nat :=
  let y := blockFn k d start init last c u 0 (a - h) h
  fun j : Fin q => (blockFn k d start init last c u (key y j) (a - h) h) ∩ sensors y j

theorem labelFn_zero {k d start init last c u j : Nat} :
    labelFn k d start init last c u 0 j =
      xor (xor ((mixFn k d u).testBit (atSite k start j))
        (!((mixFn k d u).testBit (atSite k start (j + 1))) &&
          (mixFn k d u).testBit (atSite k start (j + 2))))
        (c.testBit (atSite k start j)) := by
  unfold labelFn
  have h0 : 0 % 2 ^ k = 0 := Nat.zero_mod _
  simp [h0, rotFn_zero]

theorem labelFn_congr_of_strip {k d a start init last c u1 u2 x j : Nat}
    (hd : 0 < d) (hdk : d < k) (hu1 : u1 < 2 ^ k) (hu2 : u2 < 2 ^ k) (hj : j < a)
    (h0 : stripOf k d a start u1 ⟨j, by omega⟩ = stripOf k d a start u2 ⟨j, by omega⟩)
    (h1 : stripOf k d a start u1 ⟨j + 1, by omega⟩ = stripOf k d a start u2 ⟨j + 1, by omega⟩)
    (h2 : stripOf k d a start u1 ⟨j + 2, by omega⟩ = stripOf k d a start u2 ⟨j + 2, by omega⟩) :
    labelFn k d start init last c u1 x j = labelFn k d start init last c u2 x j := by
  have hkpos : 0 < k := by omega
  have hw : rotFn k init (x % 2 ^ k) < 2 ^ k := rotFn_lt k init _
  have hs : ∀ i, atSite k start i < k := fun i => Nat.mod_lt _ hkpos
  unfold labelFn
  dsimp only
  rw [mixFn_xor_testBit hd hdk hw hu1 (hs j),
    mixFn_xor_testBit hd hdk hw hu1 (hs (j + 1)),
    mixFn_xor_testBit hd hdk hw hu1 (hs (j + 2)),
    mixFn_xor_testBit hd hdk hw hu2 (hs j),
    mixFn_xor_testBit hd hdk hw hu2 (hs (j + 1)),
    mixFn_xor_testBit hd hdk hw hu2 (hs (j + 2))]
  unfold stripOf at h0 h1 h2
  dsimp only at h0 h1 h2
  rw [h0, h1, h2]

theorem suffix_congr_of_strip {k d a h start init last c q : Nat}
    (key : Finset Nat → Fin q → Nat) (sensors : Finset Nat → Fin q → Finset Nat)
    (hd : 0 < d) (hha : h ≤ a) (hdk : d < k)
    {u1 u2 : Nat} (hu1 : u1 < 2 ^ k) (hu2 : u2 < 2 ^ k)
    (hsuf : ∀ i : Fin (a + 2), a - h ≤ i.val →
      stripOf k d a start u1 i = stripOf k d a start u2 i) :
    (∀ x, blockFn k d start init last c u1 x (a - h) h =
        blockFn k d start init last c u2 x (a - h) h) ∧
      extrasFn k d a h start init last c q key sensors u1 =
        extrasFn k d a h start init last c q key sensors u2 := by
  have hblk : ∀ x, blockFn k d start init last c u1 x (a - h) h =
      blockFn k d start init last c u2 x (a - h) h := by
    intro x
    unfold blockFn
    apply Finset.filter_congr
    intro i hi
    have hil : i < h := Finset.mem_range.mp hi
    have hj : a - h + i < a := by omega
    have hlbl := labelFn_congr_of_strip (a := a) (start := start) (init := init) (last := last)
      (c := c) (x := x) hd hdk hu1 hu2 hj
      (hsuf ⟨a - h + i, by omega⟩ (by dsimp; omega))
      (hsuf ⟨a - h + i + 1, by omega⟩ (by dsimp; omega))
      (hsuf ⟨a - h + i + 2, by omega⟩ (by dsimp; omega))
    rw [hlbl]
  refine ⟨hblk, ?_⟩
  unfold extrasFn
  dsimp only
  funext j
  rw [hblk 0, hblk (key (blockFn k d start init last c u2 0 (a - h) h) j)]

def extendStrip (k a h start c : Nat) (hh : 0 < h) (hha : h ≤ a)
    (mBase : Fin (a + 2) → Bool) (P : Finset Nat) (s : Nat) : Bool :=
  if hlt : s < a - h then
    let b1 := extendStrip k a h start c hh hha mBase P (s + 1)
    let b2 := extendStrip k a h start c hh hha mBase P (s + 2)
    xor (xor (decide (s ∈ P)) (c.testBit (atSite k start s))) (!b1 && b2)
  else if hbound : s < a + 2 then
    mBase ⟨s, hbound⟩
  else
    false
termination_by a + 2 - s
decreasing_by
  all_goals omega

theorem extendStrip_ge (k a h start c : Nat) (hh : 0 < h) (hha : h ≤ a)
    (mBase : Fin (a + 2) → Bool) (P : Finset Nat) (i : Fin (a + 2)) (hge : a - h ≤ i.val) :
    extendStrip k a h start c hh hha mBase P i.val = mBase i := by
  conv_lhs => rw [extendStrip]
  rw [dif_neg (by omega), dif_pos i.isLt]

theorem extendStrip_lt (k a h start c : Nat) (hh : 0 < h) (hha : h ≤ a)
    (mBase : Fin (a + 2) → Bool) (P : Finset Nat) {s : Nat} (hlt : s < a - h) :
    extendStrip k a h start c hh hha mBase P s =
      xor (xor (decide (s ∈ P)) (c.testBit (atSite k start s)))
        (!(extendStrip k a h start c hh hha mBase P (s + 1)) &&
          extendStrip k a h start c hh hha mBase P (s + 2)) := by
  conv_lhs => rw [extendStrip]
  rw [dif_pos hlt]

theorem xor_solve_back (p b c : Bool) :
    xor (xor (xor (xor p c) b) b) c = p := by
  cases p <;> cases b <;> cases c <;> rfl

theorem prefix_realize {k d a h start init last c q : Nat}
    (key : Finset Nat → Fin q → Nat) (sensors : Finset Nat → Fin q → Finset Nat)
    (hd : 0 < d) (hh : 0 < h) (hha : h ≤ a) (hk : a + 2 + 2 * d ≤ k)
    {u0 : Nat} (hu0 : u0 < 2 ^ k) {P : Finset Nat} (hP : P ⊆ Finset.range (a - h)) :
    ∃ u < 2 ^ k,
      blockFn k d start init last c u 0 0 a =
        P ∪ (blockFn k d start init last c u0 0 (a - h) h).image (fun r => a - h + r) ∧
      extrasFn k d a h start init last c q key sensors u =
        extrasFn k d a h start init last c q key sensors u0 := by
  let mBase : Fin (a + 2) → Bool := stripOf k d a start u0
  let m' : Fin (a + 2) → Bool := fun i => extendStrip k a h start c hh hha mBase P i.val
  obtain ⟨u, hu, hstrip⟩ := stripOf_surj (start := start) hd hk m'
  have hsuf : ∀ i : Fin (a + 2), a - h ≤ i.val →
      stripOf k d a start u i = stripOf k d a start u0 i := by
    intro i hi
    rw [hstrip]
    exact extendStrip_ge k a h start c hh hha mBase P i hi
  have hdk : d < k := by omega
  have ⟨hblk_suf, hext_eq⟩ := suffix_congr_of_strip (init := init) (last := last) (c := c)
    key sensors hd hha hdk hu hu0 hsuf
  refine ⟨u, hu, ?_, hext_eq⟩
  ext t
  simp only [blockFn, Finset.mem_filter, Finset.mem_range, Nat.zero_add,
    Finset.mem_union, Finset.mem_image]
  by_cases ht : t < a - h
  · have hta : t < a := by omega
    have hlbl : labelFn k d start init last c u 0 t = decide (t ∈ P) := by
      rw [labelFn_zero]
      have hst0 : (mixFn k d u).testBit (atSite k start t) = m' ⟨t, by omega⟩ := by
        have := congrFun hstrip ⟨t, by omega⟩
        exact this
      have hst1 : (mixFn k d u).testBit (atSite k start (t + 1)) = m' ⟨t + 1, by omega⟩ := by
        have := congrFun hstrip ⟨t + 1, by omega⟩
        exact this
      have hst2 : (mixFn k d u).testBit (atSite k start (t + 2)) = m' ⟨t + 2, by omega⟩ := by
        have := congrFun hstrip ⟨t + 2, by omega⟩
        exact this
      rw [hst0, hst1, hst2]
      dsimp only [m']
      rw [extendStrip_lt k a h start c hh hha mBase P ht]
      exact xor_solve_back _ _ _
    constructor
    · intro ⟨_, hl⟩
      rw [hlbl] at hl
      exact Or.inl (of_decide_eq_true hl)
    · intro hmem
      rcases hmem with htp | ⟨r, _, hr⟩
      · refine ⟨hta, ?_⟩
        rw [hlbl]
        exact decide_eq_true htp
      · omega
  · have hnotP : t ∉ P := by
      intro htp
      have := Finset.mem_range.mp (hP htp)
      omega
    constructor
    · intro ⟨hta, hl⟩
      right
      refine ⟨t - (a - h), ⟨by omega, ?_⟩, by omega⟩
      have hteq : a - h + (t - (a - h)) = t := by omega
      rw [hteq]
      have hlbl_eq := labelFn_congr_of_strip (a := a) (start := start) (init := init) (last := last)
        (c := c) (x := 0) hd hdk hu hu0 hta
        (hsuf ⟨t, by omega⟩ (by dsimp; omega))
        (hsuf ⟨t + 1, by omega⟩ (by dsimp; omega))
        (hsuf ⟨t + 2, by omega⟩ (by dsimp; omega))
      rw [← hlbl_eq]
      exact hl
    · intro hmem
      rcases hmem with htp | ⟨r, ⟨hrlt, hrlbl⟩, hreq⟩
      · exact False.elim (hnotP htp)
      · have hta : t < a := by omega
        refine ⟨hta, ?_⟩
        have hlbl_eq := labelFn_congr_of_strip (a := a) (start := start) (init := init) (last := last)
          (c := c) (x := 0) hd hdk hu hu0 hta
          (hsuf ⟨t, by omega⟩ (by dsimp; omega))
          (hsuf ⟨t + 1, by omega⟩ (by dsimp; omega))
          (hsuf ⟨t + 2, by omega⟩ (by dsimp; omega))
        rw [hlbl_eq, ← hreq]
        exact hrlbl

theorem main : ∀ (k d a h start init last c q : Nat), 0 < d → 0 < h → h ≤ a → a+2+2*d ≤ k →
    ∀ (key : Finset Nat → Fin q → Nat) (sensors : Finset Nat → Fin q → Finset Nat),
    let words := Finset.range (2^k)
    let rot := fun (s z : Nat) => ((z <<< (s % k)) ||| (z >>> (k - s % k))) % 2^k
    let mix := fun z : Nat => z ^^^ rot d z ^^^ rot (k-d) z
    let label := fun (u x j : Nat) =>
      let y := mix (rot init (x % 2^k) ^^^ u)
      let atSite := fun i : Nat => (start+i) % k
      xor (xor (y.testBit (atSite j))
        (!(y.testBit (atSite (j+1))) && y.testBit (atSite (j+2))))
        (xor ((rot last (x % 2^k)).testBit (atSite j)) (c.testBit (atSite j)))
    let block := fun (u x offset len : Nat) =>
      (Finset.range len).filter (fun i => label u x (offset+i))
    let extras := fun u : Nat =>
      let y := block u 0 (a-h) h
      fun j : Fin q => (block u (key y j) (a-h) h) ∩ sensors y j
    let transcripts := fun (offset len : Nat) =>
      words.image (fun u => (block u 0 offset len, extras u))
    (transcripts 0 a).card = 2^(a-h) * (transcripts (a-h) h).card := by
  intro k d a h start init last c q hd hh hha hk key sensors
  dsimp only
  let words := Finset.range (2 ^ k)
  let transcripts := fun (offset len : Nat) =>
    words.image (fun u =>
      (blockFn k d start init last c u 0 offset len,
       extrasFn k d a h start init last c q key sensors u))
  change (transcripts 0 a).card = 2 ^ (a - h) * (transcripts (a - h) h).card
  have hprod : 2 ^ (a - h) * (transcripts (a - h) h).card =
      ((Finset.range (a - h)).powerset ×ˢ transcripts (a - h) h).card := by
    rw [Finset.card_product, Finset.card_powerset, Finset.card_range]
  rw [hprod]
  symm
  refine Finset.card_bij
    (fun p _ => (p.1 ∪ p.2.1.image (fun r => a - h + r), p.2.2)) ?_ ?_ ?_
  · intro p hp
    rcases p with ⟨P, y, ext⟩
    rcases Finset.mem_product.mp hp with ⟨hP, ht⟩
    have hPsub : P ⊆ Finset.range (a - h) := Finset.mem_powerset.mp hP
    rcases Finset.mem_image.mp ht with ⟨u0, hu0w, hu0eq⟩
    rcases Prod.mk.inj hu0eq with ⟨hy_eq, hext_eq⟩
    have hu0 : u0 < 2 ^ k := Finset.mem_range.mp hu0w
    obtain ⟨u, hu, hblk, hext⟩ := prefix_realize key sensors hd hh hha hk hu0 hPsub
    refine Finset.mem_image.mpr ⟨u, Finset.mem_range.mpr hu, ?_⟩
    rw [← hy_eq, ← hext_eq]
    exact Prod.ext hblk hext
  · intro p1 hp1 p2 hp2 heq
    rcases Finset.mem_product.mp hp1 with ⟨hP1, _⟩
    rcases Finset.mem_product.mp hp2 with ⟨hP2, _⟩
    have hP1sub : p1.1 ⊆ Finset.range (a - h) := Finset.mem_powerset.mp hP1
    have hP2sub : p2.1 ⊆ Finset.range (a - h) := Finset.mem_powerset.mp hP2
    rcases Prod.mk.inj heq with ⟨hfst, hsnd⟩
    have h1eq : p1.1 = p2.1 := by
      ext t
      constructor
      · intro ht1
        have htlt : t < a - h := Finset.mem_range.mp (hP1sub ht1)
        have hmem : t ∈ p2.1 ∪ p2.2.1.image (fun r => a - h + r) := by
          rw [← hfst]
          exact Finset.mem_union_left _ ht1
        rcases Finset.mem_union.mp hmem with ht2 | himg
        · exact ht2
        · rcases Finset.mem_image.mp himg with ⟨r, _, hr⟩
          omega
      · intro ht2
        have htlt : t < a - h := Finset.mem_range.mp (hP2sub ht2)
        have hmem : t ∈ p1.1 ∪ p1.2.1.image (fun r => a - h + r) := by
          rw [hfst]
          exact Finset.mem_union_left _ ht2
        rcases Finset.mem_union.mp hmem with ht1 | himg
        · exact ht1
        · rcases Finset.mem_image.mp himg with ⟨r, _, hr⟩
          omega
    have h2eq : p1.2.1 = p2.2.1 := by
      ext r
      constructor
      · intro hr1
        have hmem : a - h + r ∈ p2.1 ∪ p2.2.1.image (fun r => a - h + r) := by
          rw [← hfst]
          exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨r, hr1, rfl⟩)
        rcases Finset.mem_union.mp hmem with htp2 | himg
        · have := Finset.mem_range.mp (hP2sub htp2)
          omega
        · rcases Finset.mem_image.mp himg with ⟨r', hr', hreq⟩
          have : r' = r := by omega
          subst this
          exact hr'
      · intro hr2
        have hmem : a - h + r ∈ p1.1 ∪ p1.2.1.image (fun r => a - h + r) := by
          rw [hfst]
          exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨r, hr2, rfl⟩)
        rcases Finset.mem_union.mp hmem with htp1 | himg
        · have := Finset.mem_range.mp (hP1sub htp1)
          omega
        · rcases Finset.mem_image.mp himg with ⟨r', hr', hreq⟩
          have : r' = r := by omega
          subst this
          exact hr'
    exact Prod.ext h1eq (Prod.ext h2eq hsnd)
  · intro b hb
    rcases Finset.mem_image.mp hb with ⟨u, huw, hueq⟩
    let P := (blockFn k d start init last c u 0 0 a).filter (fun t => t < a - h)
    let y := blockFn k d start init last c u 0 (a - h) h
    let ext := extrasFn k d a h start init last c q key sensors u
    refine ⟨(P, (y, ext)), ?_, ?_⟩
    · refine Finset.mem_product.mpr ⟨Finset.mem_powerset.mpr ?_, Finset.mem_image.mpr ⟨u, huw, rfl⟩⟩
      intro t ht
      exact Finset.mem_range.mpr (Finset.mem_filter.mp ht).2
    · rw [← hueq]
      refine Prod.ext ?_ rfl
      ext t
      simp only [P, y, blockFn, Finset.mem_union, Finset.mem_filter, Finset.mem_range,
        Nat.zero_add, Finset.mem_image]
      constructor
      · intro hmem
        rcases hmem with ⟨⟨hta, hl⟩, _⟩ | ⟨r, ⟨hrlt, hrlbl⟩, hreq⟩
        · exact ⟨hta, hl⟩
        · refine ⟨by omega, ?_⟩
          rw [← hreq]
          exact hrlbl
      · intro ⟨hta, hl⟩
        by_cases hlt : t < a - h
        · exact Or.inl ⟨⟨hta, hl⟩, hlt⟩
        · right
          refine ⟨t - (a - h), ⟨by omega, ?_⟩, by omega⟩
          have hteq : a - h + (t - (a - h)) = t := by omega
          rw [hteq]
          exact hl

end PEqualNP.Outside.L_meta_33684_aux

theorem PEqualNP.Outside.L_meta_33684 : (∀ (k d a h start init last c q : Nat), 0 < d → 0 < h → h ≤ a → a+2+2*d ≤ k →
  ∀ (key : Finset Nat → Fin q → Nat) (sensors : Finset Nat → Fin q → Finset Nat),
  let words := Finset.range (2^k)
  let rot := fun (s z : Nat) => ((z <<< (s % k)) ||| (z >>> (k - s % k))) % 2^k
  let mix := fun z : Nat => z ^^^ rot d z ^^^ rot (k-d) z
  let label := fun (u x j : Nat) =>
    let y := mix (rot init (x % 2^k) ^^^ u)
    let atSite := fun i : Nat => (start+i) % k
    xor (xor (y.testBit (atSite j))
      (!(y.testBit (atSite (j+1))) && y.testBit (atSite (j+2))))
      (xor ((rot last (x % 2^k)).testBit (atSite j)) (c.testBit (atSite j)))
  let block := fun (u x offset len : Nat) =>
    (Finset.range len).filter (fun i => label u x (offset+i))
  let extras := fun u : Nat =>
    let y := block u 0 (a-h) h
    fun j : Fin q => (block u (key y j) (a-h) h) ∩ sensors y j
  let transcripts := fun (offset len : Nat) =>
    words.image (fun u => (block u 0 offset len, extras u))
  (transcripts 0 a).card = 2^(a-h) * (transcripts (a-h) h).card) :=
  PEqualNP.Outside.L_meta_33684_aux.main
