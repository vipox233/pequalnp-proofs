import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_390_aux

abbrev State (d : ℕ) := Fin (d + 1) → Bool
abbrev Tail (d : ℕ) := Fin d → Bool
abbrev Config (d L : ℕ) := Fin L → Tail d → Bool
abbrev Tape (d L : ℕ) := Fin (L + d + 1) → Bool

def tail {d} (s : State d) : Tail d := fun b => s b.succ

lemma cancel (u v : Bool) : xor (xor u v) v = u := by cases u <;> cases v <;> rfl

def rowEquiv {d} (f : Tail d → Bool) : State d ≃ State d where
  toFun s := Fin.lastCases (xor (s 0) (f (tail s))) (tail s)
  invFun s := Fin.cases (xor (s (Fin.last d)) (f (fun b => s b.castSucc)))
    (fun b => s b.castSucc)
  left_inv s := by
    funext j
    refine Fin.cases ?_ (fun b => ?_) j
    · simp only [Fin.cases_zero, Fin.lastCases_last, Fin.lastCases_castSucc]
      exact cancel (s 0) (f (tail s))
    · simp [tail]
  right_inv s := by
    funext j
    refine Fin.lastCases ?_ (fun b => ?_) j
    · simp only [Fin.lastCases_last, Fin.cases_zero]
      exact cancel (s (Fin.last d)) (f (fun b => s b.castSucc))
    · simp [tail]

def switches {d L} (c : Config d L) (n : ℕ) : Tail d → Bool :=
  if h : n < L then c ⟨n, h⟩ else fun _ => false

def sweep {d L} (c : Config d L) : ℕ → State d ≃ State d
  | 0 => Equiv.refl _
  | n + 1 => (sweep c n).trans (rowEquiv (switches c n))

def start {d L} (c : Config d L) (i : Fin L) (z : Tail d) : State d :=
  (sweep c i.val).symm (Fin.cases false z)

lemma sweep_prefix {d L} (c c' : Config d L) (n : ℕ)
    (agree : ∀ h : Fin L, h.val < n → c h = c' h) : sweep c n = sweep c' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have prior := ih (fun h hh => agree h (by omega))
    have same : switches c n = switches c' n := by
      unfold switches
      split
      · exact agree _ (by simp)
      · rfl
    simp [sweep, prior, same]

def bit {d L} (c : Config d L) (a : State d) (n : ℕ) := (sweep c n a) 0

lemma shifted {d L} (c : Config d L) (a : State d) (n : ℕ) (j : Fin d) :
    sweep c (n+1) a j.castSucc = sweep c n a j.succ := by
  simp [sweep, rowEquiv, tail]

lemma window {d L} (c : Config d L) (a : State d) (j : ℕ) (hj : j < d+1) (n : ℕ) :
    bit c a (n+j) = sweep c n a ⟨j, hj⟩ := by
  induction j generalizing n with
  | zero => rfl
  | succ j ih =>
    have h : j < d := by omega
    rw [show n+(j+1) = (n+1)+j by omega, ih (by omega)]
    exact shifted c a n ⟨j,h⟩

lemma update {d L} (c : Config d L) (a : State d) (i : Fin L) :
    bit c a (i.val + (d+1)) = xor (bit c a i.val)
      (c i (fun b => bit c a (i.val + b.succ.val))) := by
  rw [show i.val+(d+1) = (i.val+1)+d by omega, window c a d (by omega)]
  change rowEquiv (switches c i.val) (sweep c i.val a) (Fin.last d) = _
  simp only [rowEquiv, Equiv.coe_fn_mk, Fin.lastCases_last]
  simp only [switches, i.isLt, ↓reduceDIte]
  congr 1
  apply congrArg (c i)
  funext b
  exact (window c a b.succ.val b.succ.isLt i.val).symm

lemma selected {d L} (c : Config d L) (i : Fin L) (z : Tail d) :
    bit c (start c i z) (i.val + (d+1)) = c i z := by
  have hi : sweep c i.val (start c i z) = Fin.cases false z :=
    (sweep c i.val).apply_symm_apply _
  rw [update]
  have head : bit c (start c i z) i.val = false := by simp [bit, hi]
  have rest : (fun b : Fin d => bit c (start c i z) (i.val + b.succ.val)) = z := by
    funext b
    rw [window _ _ _ b.succ.isLt, hi]
    exact Fin.cases_succ b
  rw [head, rest]
  simp

def readBit {N : ℕ} (x : Fin (N+1) → Bool) (n : ℕ) := x (Fin.ofNat (N+1) n)

def encoded {d L} (c : Config d L) (a : State d) : Tape d L := fun j => bit c a j.val

lemma encoded_at {d L} (c : Config d L) (a : State d) {n : ℕ} (hn : n < L+d+1) :
    readBit (encoded c a) n = bit c a n := by
  simp [readBit, encoded, Fin.ofNat, Nat.mod_eq_of_lt hn]

def obeys {d L} (c : Config d L) (x : Tape d L) : Prop := ∀ i : Fin L,
  readBit x (i.val+(d+1)) = xor (readBit x i.val) (c i (fun b => readBit x (i.val+b.succ.val)))

def pins {d L} (a : State d) (x : Tape d L) : Prop := ∀ r : Fin (d+1), readBit x r.val = a r

lemma encoded_obeys {d L} (c : Config d L) (a : State d) : obeys c (encoded c a) := by
  intro i
  have hi := i.isLt
  have e (b : Fin d) : readBit (encoded c a) (i.val+b.succ.val) = bit c a (i.val+b.succ.val) :=
    encoded_at _ _ (by have := b.isLt; simp only [Fin.val_succ]; omega)
  simpa only [encoded_at c a (show i.val+(d+1)<L+d+1 by omega),
    encoded_at c a (show i.val<L+d+1 by omega), e] using update c a i

lemma encoded_pins {d L} (c : Config d L) (a : State d) : pins (L:=L) a (encoded c a) := by
  intro j
  rw [encoded_at _ _ (by have := j.isLt; omega)]
  simpa [sweep] using window c a j.val j.isLt 0

lemma unique_tape {d L} (c : Config d L) (a : State d) (x y : Tape d L)
    (hx : obeys c x) (hy : obeys c y) (px : pins a x) (py : pins a y) : x = y := by
  have same (n : ℕ) (hn : n < L+d+1) : readBit x n = readBit y n := by
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      by_cases small : n < d+1
      · exact (px ⟨n,small⟩).trans (py ⟨n,small⟩).symm
      · let i : Fin L := ⟨n-(d+1),by omega⟩
        have add : i.val+(d+1) = n := by dsimp [i]; omega
        have heads : readBit x i.val = readBit y i.val := ih _ (by omega) (by omega)
        have tails (b : Fin d) : readBit x (i.val+b.succ.val) = readBit y (i.val+b.succ.val) := by
          have hb := b.isLt
          apply ih <;> simp only [Fin.val_succ] <;> omega
        rw [←add, hx i, hy i, heads]
        exact congrArg (fun z => xor (readBit y i.val) (c i z)) (funext tails)
  funext j
  simpa [readBit, Fin.ofNat, Nat.mod_eq_of_lt j.isLt] using same j.val j.isLt

lemma wraps {d L} (x : Tape d L) (r : Fin (d+1)) :
    readBit x (L+r.val+(d+1)) = readBit x r.val := by
  apply congrArg x
  apply Fin.ext
  change (L+r.val+(d+1)) % (L+d+1) = r.val % (L+d+1)
  rw [show L+r.val+(d+1) = r.val+(L+d+1) by omega, Nat.add_mod_right]

def accepts {d L} (c : Config d L) (a : State d) (k : Fin (d+1)) (x : Tape d L) : Prop :=
  (∀ i : Fin L, decide (readBit x (i.val+(d+1)) = xor (readBit x i.val)
    (c i (fun b => readBit x (i.val+b.succ.val)))) = true) ∧
  ∀ r : Fin (d+1), decide (readBit x (L+r.val+(d+1)) = a r ∧
    (r.val=0 → readBit x (L+r.val+k.val)=true)) = true

lemma accepts_iff {d L} (c : Config d L) (a : State d) (k : Fin (d+1)) (x : Tape d L) :
    accepts c a k x ↔ obeys c x ∧ pins a x ∧ readBit x (L+k.val) = true := by
  simp only [accepts, decide_eq_true_eq, wraps]
  constructor
  · rintro ⟨h, stop⟩
    exact ⟨h, fun r => (stop r).1, by simpa using (stop 0).2 rfl⟩
  · rintro ⟨h, p, t⟩
    exact ⟨h, fun r => ⟨p r, fun hr => by simpa only [hr, Nat.add_zero] using t⟩⟩

lemma query {d L} (c : Config d L) (i : Fin L) (z : Tail d) (near : L ≤ i.val+(d+1)) :
    let k := Fin.ofNat (d+1) ((d+1)-(L-i.val))
    ∀ x : Tape d L, accepts c (start c i z) k x ↔ x = encoded c (start c i z) ∧ c i z = true := by
  intro k x
  let a := start c i z
  have hi := i.isLt
  have offset : L+k.val = i.val+(d+1) := by
    dsimp only [k, Fin.ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have probe : readBit (encoded c a) (L+k.val) = c i z := by
    rw [offset, encoded_at _ _ (by omega)]
    exact selected c i z
  rw [accepts_iff]
  constructor
  · rintro ⟨h,p,t⟩
    have u := unique_tape c a x _ h (encoded_obeys c a) p (encoded_pins c a)
    exact ⟨u, by rwa [u, probe] at t⟩
  · rintro ⟨rfl, v⟩
    exact ⟨encoded_obeys c a, encoded_pins c a, probe.trans v⟩

end PEqualNP.Outside.L_lib_390_aux

theorem PEqualNP.Outside.L_lib_390 : (∀ (d L : ℕ),
  let w := d + 1
  let State := Fin w → Bool
  let Tail := Fin d → Bool
  let Pat := Fin (w + 1) → Bool
  let Part := fun k : ℕ => Fin k → Pat → Bool
  let Config := Fin L → Tail → Bool
  let first := fun (c : Config) (h : Fin L) (p : Pat) =>
    decide (p (Fin.last w) = xor (p 0) (c h (fun b => p b.succ.castSucc)))
  let last := fun (a : State) (k : Fin w) (r : Fin w) (p : Pat) =>
    decide (p (Fin.last w) = a r ∧ (r.val = 0 → p k.castSucc = true))
  let ok := fun (P : Part L) (Q : Part w) (x : Fin (L + d + 1) → Bool) =>
    (∀ row : Fin L, P row (fun j => x (Fin.ofNat (L + d + 1) (row.val + j.val))) = true) ∧
    ∀ r : Fin w, Q r (fun j => x (Fin.ofNat (L + d + 1) (L + r.val + j.val))) = true
  ∃ selectStart : Config → Fin L → Tail → State,
    (∀ (c c' : Config) (i : Fin L) (z : Tail),
      (∀ h : Fin L, h.val < i.val → c h = c' h) → selectStart c i z = selectStart c' i z) ∧
    ∀ (c : Config) (i : Fin L) (z : Tail), L ≤ i.val + w →
      let k := Fin.ofNat w (w - (L - i.val))
      (Finset.univ.filter (ok (first c) (last (selectStart c i z) k))).card =
        (if c i z = true then 1 else 0)) := by
  intro d L
  dsimp only
  refine ⟨PEqualNP.Outside.L_lib_390_aux.start, ?_, ?_⟩
  · intro c c' i z agree
    unfold PEqualNP.Outside.L_lib_390_aux.start
    rw [PEqualNP.Outside.L_lib_390_aux.sweep_prefix c c' i.val agree]
  · intro c i z near
    let k := Fin.ofNat (d+1) ((d+1)-(L-i.val))
    let a := PEqualNP.Outside.L_lib_390_aux.start c i z
    have classify := PEqualNP.Outside.L_lib_390_aux.query c i z near
    by_cases yes : c i z = true
    · rw [ite_eq_left yes]
      apply Finset.card_eq_one.mpr
      refine ⟨PEqualNP.Outside.L_lib_390_aux.encoded c a, ?_⟩
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      change PEqualNP.Outside.L_lib_390_aux.accepts c a k x ↔ x = PEqualNP.Outside.L_lib_390_aux.encoded c a
      simpa only [yes, and_true, eq_self] using classify x
    · rw [ite_eq_right yes]
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact yes ((classify x).mp (Finset.mem_filter.mp hx).2).2
