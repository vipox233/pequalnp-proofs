import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_226_aux

open Classical
open PEqualNP.ProofComplexity PEqualNP.Search

def bitsToNat : ∀ (k : ℕ), (Fin k → Bool) → ℕ
  | 0, _ => 0
  | k + 1, f => (if f 0 then 1 else 0) + 2 * bitsToNat k (fun j => f j.succ)

theorem bitsToNat_lt : ∀ (k : ℕ) (f : Fin k → Bool), bitsToNat k f < 2 ^ k
  | 0, _ => by simp [bitsToNat]
  | k + 1, f => by
    have ih := bitsToNat_lt k (fun j => f j.succ)
    have hp : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [bitsToNat, hp]
    cases f 0 <;> simp <;> omega

theorem testBit_bitsToNat : ∀ (k : ℕ) (f : Fin k → Bool) (j : Fin k),
    (bitsToNat k f).testBit j.val = f j
  | 0, _, j => Fin.elim0 j
  | k + 1, f, j => by
    refine Fin.cases ?_ ?_ j
    · simp only [bitsToNat, Fin.val_zero]
      cases h0 : f 0
      · simp
      · simp [Nat.testBit_zero]
    · intro j'
      have ih := testBit_bitsToNat k (fun i => f i.succ) j'
      simp only [bitsToNat, Fin.val_succ]
      rw [Nat.testBit_succ]
      have hdiv : ((if f 0 then 1 else 0) + 2 * bitsToNat k (fun i => f i.succ)) / 2 =
          bitsToNat k (fun i => f i.succ) := by
        cases f 0 <;> simp <;> omega
      rw [hdiv]
      exact ih

theorem bitsToNat_testBit : ∀ (k : ℕ) (x : ℕ), x < 2 ^ k →
    bitsToNat k (fun j : Fin k => x.testBit j.val) = x
  | 0, x, hx => by simp [bitsToNat]; omega
  | k + 1, x, hx => by
    have hp : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    have hlt : x / 2 < 2 ^ k := by omega
    have ih := bitsToNat_testBit k (x / 2) hlt
    simp only [bitsToNat, Fin.val_zero, Fin.val_succ]
    have hsucc : (fun j : Fin k => x.testBit (j.val + 1)) =
        (fun j : Fin k => (x / 2).testBit j.val) := by
      funext j
      exact Nat.testBit_succ x j.val
    rw [hsucc, ih]
    have hmod : x % 2 = 0 ∨ x % 2 = 1 := Nat.mod_two_eq_zero_or_one x
    rcases hmod with h0 | h1
    · have hb : x.testBit 0 = false := by simp [Nat.testBit_zero, h0]
      simp only [hb, Bool.false_eq_true, ↓reduceIte]; omega
    · have hb : x.testBit 0 = true := by simp [Nat.testBit_zero, h1]
      simp only [hb, ↓reduceIte]; omega

abbrev State (w : ℕ) := Fin (2 ^ w)
abbrev Pat (w : ℕ) := Fin (2 ^ (w + 1))

def decState (w : ℕ) (s : State w) : Fin w → Bool :=
  fun j => s.val.testBit j.val

def encState (w : ℕ) (f : Fin w → Bool) : State w :=
  ⟨bitsToNat w f, bitsToNat_lt w f⟩

theorem decState_encState (w : ℕ) (f : Fin w → Bool) :
    decState w (encState w f) = f := by
  funext j
  exact testBit_bitsToNat w f j

theorem encState_decState (w : ℕ) (s : State w) :
    encState w (decState w s) = s := by
  apply Fin.ext
  exact bitsToNat_testBit w s.val s.isLt

def consBool {w : ℕ} (b : Bool) (f : Fin w → Bool) : Fin (w + 1) → Bool :=
  fun j => if h : j.val = 0 then b else f ⟨j.val - 1, by have := j.isLt; omega⟩

def snocBool {w : ℕ} (f : Fin w → Bool) (b : Bool) : Fin (w + 1) → Bool :=
  fun j => if h : j.val < w then f ⟨j.val, h⟩ else b

def patHead {w : ℕ} (p : Pat w) : Bool :=
  decide (2 ^ w ≤ p.val)

def patDst {w : ℕ} (p : Pat w) : State w :=
  ⟨p.val % 2 ^ w, Nat.mod_lt _ (Nat.two_pow_pos w)⟩

def patFun {w : ℕ} (p : Pat w) : Fin (w + 1) → Bool :=
  consBool (patHead p) (decState w (patDst p))

def patOfFun {w : ℕ} (f : Fin (w + 1) → Bool) : Pat w :=
  ⟨(if f 0 then 2 ^ w else 0) + bitsToNat w (fun j => f j.succ), by
    have h := bitsToNat_lt w (fun j => f j.succ)
    have hp : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ, Nat.mul_comm]
    cases f 0 <;> simp <;> omega⟩

def patSrc {w : ℕ} (p : Pat w) : State w :=
  encState w (fun j => patFun p j.castSucc)

theorem patFun_patOfFun {w : ℕ} (f : Fin (w + 1) → Bool) :
    patFun (patOfFun f) = f := by
  have hlt := bitsToNat_lt w (fun j => f j.succ)
  have hh : patHead (patOfFun f) = f 0 := by
    by_cases h0 : f 0 = true
    · simp only [patHead, patOfFun, h0, ↓reduceIte, decide_eq_true_eq]
      omega
    · have hf0 : f 0 = false := Bool.eq_false_iff.mpr h0
      simp only [patHead, patOfFun, hf0, Bool.false_eq_true, ↓reduceIte, zero_add,
        decide_eq_false_iff_not, not_le]
      exact hlt
  have hd : patDst (patOfFun f) = encState w (fun j => f j.succ) := by
    apply Fin.ext
    by_cases h0 : f 0 = true
    · simp only [patDst, patOfFun, encState, h0, ↓reduceIte]
      rw [Nat.add_mod_left, Nat.mod_eq_of_lt hlt]
    · have hf0 : f 0 = false := Bool.eq_false_iff.mpr h0
      simp only [patDst, patOfFun, encState, hf0, Bool.false_eq_true, ↓reduceIte, zero_add]
      exact Nat.mod_eq_of_lt hlt
  funext j
  unfold patFun consBool
  by_cases hj : j.val = 0
  · simp only [hj, ↓reduceDIte, hh]
    congr 1
    exact Fin.ext hj.symm
  · simp only [hj, ↓reduceDIte, hd, decState_encState]
    congr 1
    apply Fin.ext
    simp only [Fin.val_succ]
    omega

theorem patOfFun_patFun {w : ℕ} (p : Pat w) :
    patOfFun (patFun p) = p := by
  apply Fin.ext
  have hlt : p.val < 2 ^ (w + 1) := p.isLt
  have hpow : 2 ^ (w + 1) = 2 ^ w + 2 ^ w := by rw [Nat.pow_succ]; omega
  unfold patOfFun
  have h0 : patFun p 0 = patHead p := by simp [patFun, consBool]
  have hs : (fun j : Fin w => patFun p j.succ) = decState w (patDst p) := by
    funext j
    simp [patFun, consBool]
  simp only [h0, hs]
  have hdec : bitsToNat w (decState w (patDst p)) = p.val % 2 ^ w :=
    bitsToNat_testBit w (p.val % 2 ^ w) (Nat.mod_lt _ (Nat.two_pow_pos w))
  rw [hdec]
  unfold patHead
  by_cases hge : 2 ^ w ≤ p.val
  · simp only [hge, decide_true, ↓reduceIte]
    have hmod : p.val % 2 ^ w = p.val - 2 ^ w := by
      have : p.val = 2 ^ w + (p.val - 2 ^ w) := by omega
      conv_lhs => rw [this]
      rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    omega
  · simp only [hge, decide_false, Bool.false_eq_true, ↓reduceIte, zero_add]
    exact Nat.mod_eq_of_lt (by omega)

def inPat {w : ℕ} (b : Bool) (s : State w) : Pat w :=
  ⟨(if b then 2 ^ w else 0) + s.val, by
    have h := s.isLt
    have hp : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ, Nat.mul_comm]
    cases b <;> simp <;> omega⟩

def outPat {w : ℕ} (s : State w) (b : Bool) : Pat w :=
  patOfFun (snocBool (decState w s) b)

theorem patDst_inPat {w : ℕ} (b : Bool) (s : State w) :
    patDst (inPat b s) = s := by
  apply Fin.ext
  unfold patDst inPat
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
    exact Nat.mod_eq_of_lt s.isLt
  · simp only [↓reduceIte]
    rw [Nat.add_mod_left, Nat.mod_eq_of_lt s.isLt]

theorem patHead_inPat {w : ℕ} (b : Bool) (s : State w) :
    patHead (inPat b s) = b := by
  unfold patHead inPat
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, zero_add, decide_eq_false_iff_not, not_le]
    exact s.isLt
  · simp only [↓reduceIte, decide_eq_true_eq]
    omega

theorem patDst_eq_iff {w : ℕ} (p : Pat w) (s : State w) :
    patDst p = s ↔ p = inPat false s ∨ p = inPat true s := by
  constructor
  · intro h
    have hlt := p.isLt
    have hpow : 2 ^ (w + 1) = 2 ^ w + 2 ^ w := by rw [Nat.pow_succ]; omega
    have hval : p.val % 2 ^ w = s.val := congrArg Fin.val h
    by_cases hge : 2 ^ w ≤ p.val
    · right
      apply Fin.ext
      simp only [inPat, ↓reduceIte]
      have hmod : p.val % 2 ^ w = p.val - 2 ^ w := by
        have : p.val = 2 ^ w + (p.val - 2 ^ w) := by omega
        conv_lhs => rw [this]
        rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
      omega
    · left
      apply Fin.ext
      simp only [inPat, Bool.false_eq_true, ↓reduceIte, zero_add]
      rw [← hval, Nat.mod_eq_of_lt (by omega)]
  · rintro (rfl | rfl)
    · exact patDst_inPat false s
    · exact patDst_inPat true s

theorem patSrc_outPat {w : ℕ} (s : State w) (b : Bool) :
    patSrc (outPat s b) = s := by
  simp only [patSrc, outPat, patFun_patOfFun]
  have hf : (fun j : Fin w => snocBool (decState w s) b j.castSucc) = decState w s := by
    funext j
    simp [snocBool, j.isLt]
  rw [hf, encState_decState]

theorem patSrc_eq_iff {w : ℕ} (p : Pat w) (s : State w) :
    patSrc p = s ↔ p = outPat s false ∨ p = outPat s true := by
  constructor
  · intro h
    have hfn : patFun p = snocBool (decState w s) (patFun p (Fin.last w)) := by
      funext j
      unfold snocBool
      by_cases hj : j.val < w
      · simp only [hj, ↓reduceDIte, ← h, patSrc, decState_encState]
        rfl
      · simp only [hj, ↓reduceDIte]
        congr 1
        apply Fin.ext
        have := j.isLt
        simp only [Fin.val_last]
        omega
    cases hb : patFun p (Fin.last w)
    · left
      rw [← patOfFun_patFun p, hfn, hb]
      rfl
    · right
      rw [← patOfFun_patFun p, hfn, hb]
      rfl
  · rintro (rfl | rfl)
    · exact patSrc_outPat s false
    · exact patSrc_outPat s true

theorem patFun_zero {w : ℕ} (p : Pat w) : patFun p 0 = patHead p := by
  simp [patFun, consBool]

theorem patFun_succ {w : ℕ} (p : Pat w) (j : Fin w) :
    patFun p j.succ = decState w (patDst p) j := by
  simp [patFun, consBool]

theorem patFun_castSucc {w : ℕ} (p : Pat w) (j : Fin w) :
    patFun p j.castSucc = decState w (patSrc p) j := by
  simp [patSrc, decState_encState]

theorem cycle_patFun_eq {n w : ℕ} (hn : 0 < n) (ps : Fin n → Pat w)
    (hstep : ∀ i : Fin n, patDst (ps i) = patSrc (ps ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩)) :
    ∀ (j : Fin (w + 1)) (i : Fin n),
      patFun (ps i) j = patHead (ps ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩) := by
  intro j
  induction j using Fin.induction with
  | zero =>
    intro i
    simp [patFun_zero, Nat.mod_eq_of_lt i.isLt]
  | succ j ih =>
    intro i
    rw [patFun_succ, hstep i, ← patFun_castSucc]
    have h1 := ih ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩
    rw [h1]
    have hidx : (⟨((i.val + 1) % n + j.castSucc.val) % n, Nat.mod_lt _ hn⟩ : Fin n) =
        ⟨(i.val + j.succ.val) % n, Nat.mod_lt _ hn⟩ := by
      apply Fin.ext
      simp only [Fin.val_castSucc, Fin.val_succ]
      rw [Nat.mod_add_mod]
      exact congrArg (· % n) (by omega)
    rw [hidx]

abbrev Var (n w : ℕ) := Sum (Fin n) (Fin n × (Fin (w + 1) → Bool))

abbrev AuxT (n w : ℕ) :=
  (Fin n × Pat w) ⊕
  ((State w × Fin (n + 1) × State w) ⊕
  ((State w × Fin (n + 1) × State w) ⊕
  ((Fin n × Pat w × State w) ⊕
  ((Fin n × Pat w) ⊕
  ((Fin n × Pat w) ⊕
   (Fin n × Pat w))))))

noncomputable def mCard (n w : ℕ) : ℕ := Fintype.card (AuxT n w)

noncomputable def eAux (n w : ℕ) : AuxT n w ≃ Fin (mCard n w) :=
  Fintype.equivFin (AuxT n w)

abbrev TotVar (n w : ℕ) := Sum (Var n w) (Fin (mCard n w))

noncomputable def vWord {n w : ℕ} (i : Fin n) : TotVar n w :=
  Sum.inl (Sum.inl i)

noncomputable def vTab {n w : ℕ} (i : Fin n) (p : Pat w) : TotVar n w :=
  Sum.inl (Sum.inr (i, patFun p))

noncomputable def vDis {n w : ℕ} (i : Fin n) (p : Pat w) : TotVar n w :=
  Sum.inr (eAux n w (Sum.inl (i, p)))

noncomputable def vNoPref {n w : ℕ} (s0 : State w) (k : Fin (n + 1)) (s : State w) : TotVar n w :=
  Sum.inr (eAux n w (Sum.inr (Sum.inl (s0, k, s))))

noncomputable def vNoSuff {n w : ℕ} (s0 : State w) (k : Fin (n + 1)) (s : State w) : TotVar n w :=
  Sum.inr (eAux n w (Sum.inr (Sum.inr (Sum.inl (s0, k, s)))))

noncomputable def vAllFail {n w : ℕ} (i : Fin n) (p : Pat w) (t : State w) : TotVar n w :=
  Sum.inr (eAux n w (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, p, t))))))

noncomputable def vUnsup {n w : ℕ} (i : Fin n) (p : Pat w) : TotVar n w :=
  Sum.inr (eAux n w (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, p)))))))

noncomputable def vPrefU {n w : ℕ} (i : Fin n) (p : Pat w) : TotVar n w :=
  Sum.inr (eAux n w (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, p))))))))

noncomputable def vSuffU {n w : ℕ} (i : Fin n) (p : Pat w) : TotVar n w :=
  Sum.inr (eAux n w (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (i, p))))))))

noncomputable def cl1 {α : Type} (a : Literal α) : Clause α := {a}

noncomputable def cl2 {α : Type} (a b : Literal α) : Clause α := {a, b}

noncomputable def cl3 {α : Type} (a b c : Literal α) : Clause α := {a, b, c}

theorem card_cl1_le {α : Type} (a : Literal α) : (cl1 a).card ≤ 3 := by
  simp [cl1]

theorem card_cl2_le {α : Type} (a b : Literal α) : (cl2 a b).card ≤ 3 :=
  le_trans Finset.card_le_two (by decide)

theorem card_cl3_le {α : Type} (a b c : Literal α) : (cl3 a b c).card ≤ 3 :=
  Finset.card_le_three

theorem up_imp1 {V : Type} {Γ : Set (Clause V)} {A : Set (Literal V)}
    {x y : Literal V} (hC : cl2 (negLit x) y ∈ Γ) (hx : UPForces Γ A x) :
    UPForces Γ A y := by
  apply UPForces.unit hC (by simp [cl2])
  intro l' hl' hne
  simp only [cl2, Finset.mem_insert, Finset.mem_singleton] at hl'
  rcases hl' with rfl | rfl
  · simpa [negLit] using hx
  · exact (hne rfl).elim

theorem up_imp2 {V : Type} {Γ : Set (Clause V)} {A : Set (Literal V)}
    {x y z : Literal V} (hC : cl3 (negLit x) (negLit y) z ∈ Γ)
    (hx : UPForces Γ A x) (hy : UPForces Γ A y) :
    UPForces Γ A z := by
  apply UPForces.unit hC (by simp [cl3])
  intro l' hl' hne
  simp only [cl3, Finset.mem_insert, Finset.mem_singleton] at hl'
  rcases hl' with rfl | rfl | rfl
  · simpa [negLit] using hx
  · simpa [negLit] using hy
  · exact (hne rfl).elim

theorem up_unit {V : Type} {Γ : Set (Clause V)} {A : Set (Literal V)}
    {x : Literal V} (hC : cl1 x ∈ Γ) :
    UPForces Γ A x := by
  apply UPForces.unit hC (by simp [cl1])
  intro l' hl' hne
  simp only [cl1, Finset.mem_singleton] at hl'
  exact (hne hl').elim

theorem sat_cl1 {V : Type} {a : V → Bool} {x : Literal V}
    (hx : a x.1 = x.2) : ClauseSat a (cl1 x) :=
  ⟨x, by simp [cl1], hx⟩

theorem sat_cl2 {V : Type} {a : V → Bool} {x y : Literal V}
    (h : a x.1 = x.2 → a y.1 = y.2) : ClauseSat a (cl2 (negLit x) y) := by
  by_cases hx : a x.1 = x.2
  · exact ⟨y, by simp [cl2], h hx⟩
  · refine ⟨negLit x, by simp [cl2], ?_⟩
    simp only [negLit]
    cases hv : a x.1 <;> cases hx2 : x.2 <;> simp_all

theorem sat_cl3 {V : Type} {a : V → Bool} {x y z : Literal V}
    (h : a x.1 = x.2 → a y.1 = y.2 → a z.1 = z.2) :
    ClauseSat a (cl3 (negLit x) (negLit y) z) := by
  by_cases hx : a x.1 = x.2
  · by_cases hy : a y.1 = y.2
    · exact ⟨z, by simp [cl3], h hx hy⟩
    · refine ⟨negLit y, by simp [cl3], ?_⟩
      simp only [negLit]
      cases hv : a y.1 <;> cases hy2 : y.2 <;> simp_all
  · refine ⟨negLit x, by simp [cl3], ?_⟩
    simp only [negLit]
    cases hv : a x.1 <;> cases hx2 : x.2 <;> simp_all

noncomputable def unionList {α : Type} : List (Finset α) → Finset α
  | [] => ∅
  | s :: rest => s ∪ unionList rest

theorem mem_unionList {α : Type} {x : α} :
    ∀ {L : List (Finset α)}, x ∈ unionList L ↔ ∃ s ∈ L, x ∈ s
  | [] => by simp [unionList]
  | s :: rest => by
    simp only [unionList, Finset.mem_union, List.mem_cons, mem_unionList]
    constructor
    · rintro (h | ⟨t, ht, hx⟩)
      · exact ⟨s, Or.inl rfl, h⟩
      · exact ⟨t, Or.inr ht, hx⟩
    · rintro ⟨t, rfl | ht, hx⟩
      · exact Or.inl hx
      · exact Or.inr ⟨t, ht, hx⟩

theorem card_unionList_le {α : Type} :
    ∀ (L : List (Finset α)), (unionList L).card ≤ (L.map Finset.card).sum
  | [] => by simp [unionList]
  | s :: rest => by
    simp only [unionList, List.map_cons, List.sum_cons]
    exact le_trans (Finset.card_union_le _ _) (Nat.add_le_add_left (card_unionList_le rest) _)

def stateZero (w : ℕ) : State w := ⟨0, Nat.two_pow_pos w⟩
def stateLast (w : ℕ) : State w := ⟨2 ^ w - 1, Nat.sub_lt (Nat.two_pow_pos w) (by decide)⟩
def patZero (w : ℕ) : Pat w := ⟨0, Nat.two_pow_pos (w + 1)⟩
def patMidLo (w : ℕ) : Pat w := ⟨2 ^ w - 1, by
  have hp : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ, Nat.mul_comm]
  have := Nat.two_pow_pos w; omega⟩
def patMidHi (w : ℕ) : Pat w := ⟨2 ^ w, by
  have hp : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ, Nat.mul_comm]
  have := Nat.two_pow_pos w; omega⟩
def patLast (w : ℕ) : Pat w := ⟨2 ^ (w + 1) - 1, Nat.sub_lt (Nat.two_pow_pos (w + 1)) (by decide)⟩

noncomputable def F_disTab (n w : ℕ) : Finset (Clause (TotVar n w)) :=
  (Finset.univ : Finset (Fin n × Pat w)).image fun ⟨i, p⟩ =>
    cl2 (vTab i p, true) (vDis i p, true)

noncomputable def F_disWord (n w : ℕ) : Finset (Clause (TotVar n w)) :=
  (Finset.univ : Finset (Fin n × Pat w)).image fun ⟨i, p⟩ =>
    cl2 (vWord i, patHead p) (vDis i p, true)

noncomputable def F_prefBase (n w : ℕ) : Finset (Clause (TotVar n w)) :=
  ((Finset.univ : Finset (State w × State w)).filter fun x => x.1 ≠ x.2).image fun ⟨s0, s⟩ =>
    cl1 (vNoPref s0 0 s, true)

noncomputable def F_prefStep1 (n w : ℕ) : Finset (Clause (TotVar n w)) :=
  (Finset.univ : Finset (State w × Fin n × State w)).image fun ⟨s0, k, s⟩ =>
    cl3 (vNoPref s0 k.castSucc (patSrc (inPat false s)), false)
        (vNoPref s0 k.castSucc (patSrc (inPat true s)), false)
        (vNoPref s0 k.succ s, true)

noncomputable def F_prefStep2 (n w : ℕ) : Finset (Clause (TotVar n w)) :=
  (Finset.univ : Finset (State w × Fin n × State w)).image fun ⟨s0, k, s⟩ =>
    cl3 (vNoPref s0 k.castSucc (patSrc (inPat false s)), false)
        (vDis k (inPat true s), false)
        (vNoPref s0 k.succ s, true)

noncomputable def F_prefStep3 (n w : ℕ) : Finset (Clause (TotVar n w)) :=
  (Finset.univ : Finset (State w × Fin n × State w)).image fun ⟨s0, k, s⟩ =>
    cl3 (vDis k (inPat false s), false)
        (vNoPref s0 k.castSucc (patSrc (inPat true s)), false)
        (vNoPref s0 k.succ s, true)

noncomputable def F_prefStep4 (n w : ℕ) : Finset (Clause (TotVar n w)) :=
  (Finset.univ : Finset (State w × Fin n × State w)).image fun ⟨s0, k, s⟩ =>
    cl3 (vDis k (inPat false s), false)
        (vDis k (inPat true s), false)
        (vNoPref s0 k.succ s, true)

noncomputable def F_suffBase (n w : ℕ) : Finset (Clause (TotVar n w)) :=
  ((Finset.univ : Finset (State w × State w)).filter fun x => x.1 ≠ x.2).image fun ⟨s0, s⟩ =>
    cl1 (vNoSuff s0 (Fin.last n) s, true)

noncomputable def F_suffStep1 (n w : ℕ) : Finset (Clause (TotVar n w)) :=
  (Finset.univ : Finset (State w × Fin n × State w)).image fun ⟨s0, k, s⟩ =>
    cl3 (vNoSuff s0 k.succ (patDst (outPat s false)), false)
        (vNoSuff s0 k.succ (patDst (outPat s true)), false)
        (vNoSuff s0 k.castSucc s, true)

noncomputable def F_suffStep2 (n w : ℕ) : Finset (Clause (TotVar n w)) :=
  (Finset.univ : Finset (State w × Fin n × State w)).image fun ⟨s0, k, s⟩ =>
    cl3 (vNoSuff s0 k.succ (patDst (outPat s false)), false)
        (vDis k (outPat s true), false)
        (vNoSuff s0 k.castSucc s, true)

noncomputable def F_suffStep3 (n w : ℕ) : Finset (Clause (TotVar n w)) :=
  (Finset.univ : Finset (State w × Fin n × State w)).image fun ⟨s0, k, s⟩ =>
    cl3 (vDis k (outPat s false), false)
        (vNoSuff s0 k.succ (patDst (outPat s true)), false)
        (vNoSuff s0 k.castSucc s, true)

noncomputable def F_suffStep4 (n w : ℕ) : Finset (Clause (TotVar n w)) :=
  (Finset.univ : Finset (State w × Fin n × State w)).image fun ⟨s0, k, s⟩ =>
    cl3 (vDis k (outPat s false), false)
        (vDis k (outPat s true), false)
        (vNoSuff s0 k.castSucc s, true)

noncomputable def F_allFailBaseP (n w : ℕ) : Finset (Clause (TotVar n w)) :=
  (Finset.univ : Finset (Fin n × Pat w)).image fun ⟨i, p⟩ =>
    cl2 (vNoPref (stateZero w) i.castSucc (patSrc p), false)
        (vAllFail i p (stateZero w), true)

noncomputable def F_allFailBaseS (n w : ℕ) : Finset (Clause (TotVar n w)) :=
  (Finset.univ : Finset (Fin n × Pat w)).image fun ⟨i, p⟩ =>
    cl2 (vNoSuff (stateZero w) i.succ (patDst p), false)
        (vAllFail i p (stateZero w), true)

noncomputable def F_allFailStepP (n w : ℕ) : Finset (Clause (TotVar n w)) :=
  ((Finset.univ : Finset (Fin n × Pat w × State w)).filter fun x => x.2.2.val + 1 < 2 ^ w).image
    fun ⟨i, p, t⟩ =>
      if h : t.val + 1 < 2 ^ w then
        cl3 (vAllFail i p t, false)
            (vNoPref ⟨t.val + 1, h⟩ i.castSucc (patSrc p), false)
            (vAllFail i p ⟨t.val + 1, h⟩, true)
      else ∅

noncomputable def F_allFailStepS (n w : ℕ) : Finset (Clause (TotVar n w)) :=
  ((Finset.univ : Finset (Fin n × Pat w × State w)).filter fun x => x.2.2.val + 1 < 2 ^ w).image
    fun ⟨i, p, t⟩ =>
      if h : t.val + 1 < 2 ^ w then
        cl3 (vAllFail i p t, false)
            (vNoSuff ⟨t.val + 1, h⟩ i.succ (patDst p), false)
            (vAllFail i p ⟨t.val + 1, h⟩, true)
      else ∅

noncomputable def F_unsupDis (n w : ℕ) : Finset (Clause (TotVar n w)) :=
  (Finset.univ : Finset (Fin n × Pat w)).image fun ⟨i, p⟩ =>
    cl2 (vDis i p, false) (vUnsup i p, true)

noncomputable def F_unsupFail (n w : ℕ) : Finset (Clause (TotVar n w)) :=
  (Finset.univ : Finset (Fin n × Pat w)).image fun ⟨i, p⟩ =>
    cl2 (vAllFail i p (stateLast w), false) (vUnsup i p, true)

noncomputable def F_prefUBase (n w : ℕ) : Finset (Clause (TotVar n w)) :=
  (Finset.univ : Finset (Fin n)).image fun i =>
    cl2 (vUnsup i (patZero w), false) (vPrefU i (patZero w), true)

noncomputable def F_prefUStep (n w : ℕ) : Finset (Clause (TotVar n w)) :=
  ((Finset.univ : Finset (Fin n × Pat w)).filter fun x => x.2.val + 1 < 2 ^ (w + 1)).image
    fun ⟨i, p⟩ =>
      if h : p.val + 1 < 2 ^ (w + 1) then
        cl3 (vPrefU i p, false)
            (vUnsup i ⟨p.val + 1, h⟩, false)
            (vPrefU i ⟨p.val + 1, h⟩, true)
      else ∅

noncomputable def F_suffUBase (n w : ℕ) : Finset (Clause (TotVar n w)) :=
  (Finset.univ : Finset (Fin n)).image fun i =>
    cl2 (vUnsup i (patLast w), false) (vSuffU i (patLast w), true)

noncomputable def F_suffUStep (n w : ℕ) : Finset (Clause (TotVar n w)) :=
  ((Finset.univ : Finset (Fin n × Pat w)).filter fun x => x.2.val + 1 < 2 ^ (w + 1)).image
    fun ⟨i, p⟩ =>
      if h : p.val + 1 < 2 ^ (w + 1) then
        cl3 (vSuffU i ⟨p.val + 1, h⟩, false)
            (vUnsup i p, false)
            (vSuffU i p, true)
      else ∅

noncomputable def F_wordTrue (n w : ℕ) : Finset (Clause (TotVar n w)) :=
  (Finset.univ : Finset (Fin n)).image fun i =>
    cl2 (vPrefU i (patMidLo w), false) (vWord i, true)

noncomputable def F_wordFalse (n w : ℕ) : Finset (Clause (TotVar n w)) :=
  (Finset.univ : Finset (Fin n)).image fun i =>
    cl2 (vSuffU i (patMidHi w), false) (vWord i, false)

noncomputable def F_tabForce (n w : ℕ) : Finset (Clause (TotVar n w)) :=
  (Finset.univ : Finset (Fin n × Pat w)).image fun ⟨i, p⟩ =>
    if h0 : p.val = 0 then
      cl2 (vSuffU i ⟨1, by
            have hp : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ, Nat.mul_comm]
            have := Nat.two_pow_pos w; omega⟩, false)
          (vTab i p, true)
    else if hlast : p.val + 1 = 2 ^ (w + 1) then
      cl2 (vPrefU i ⟨p.val - 1, by omega⟩, false)
          (vTab i p, true)
    else
      cl3 (vPrefU i ⟨p.val - 1, by omega⟩, false)
          (vSuffU i ⟨p.val + 1, by omega⟩, false)
          (vTab i p, true)

noncomputable def F_conflict (n w : ℕ) (hn : 0 < n) : Finset (Clause (TotVar n w)) :=
  {cl1 (vPrefU ⟨0, hn⟩ (patLast w), false)}

noncomputable def F_list (n w : ℕ) (hn : 0 < n) : List (Finset (Clause (TotVar n w))) :=
  [ F_disTab n w, F_disWord n w,
    F_prefBase n w, F_prefStep1 n w, F_prefStep2 n w, F_prefStep3 n w, F_prefStep4 n w,
    F_suffBase n w, F_suffStep1 n w, F_suffStep2 n w, F_suffStep3 n w, F_suffStep4 n w,
    F_allFailBaseP n w, F_allFailBaseS n w, F_allFailStepP n w, F_allFailStepS n w,
    F_unsupDis n w, F_unsupFail n w,
    F_prefUBase n w, F_prefUStep n w, F_suffUBase n w, F_suffUStep n w,
    F_wordTrue n w, F_wordFalse n w, F_tabForce n w, F_conflict n w hn ]

noncomputable def F_all (n w : ℕ) (hn : 0 < n) : Finset (Clause (TotVar n w)) :=
  unionList (F_list n w hn)

theorem mem_F_all_of_mem {n w : ℕ} {hn : 0 < n} {S : Finset (Clause (TotVar n w))}
    {D : Clause (TotVar n w)} (hS : S ∈ F_list n w hn) (hD : D ∈ S) :
    D ∈ (↑(F_all n w hn) : Set (Clause (TotVar n w))) := by
  exact Finset.mem_coe.mpr (mem_unionList.mpr ⟨S, hS, hD⟩)

theorem card_le_three_F_all (n w : ℕ) (hn : 0 < n) :
    ∀ D ∈ F_all n w hn, D.card ≤ 3 := by
  intro D hD
  rcases mem_unionList.mp hD with ⟨S, hS, hDS⟩
  simp only [F_list, List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                 rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                 rfl | rfl | rfl | rfl | rfl | rfl
  · rcases Finset.mem_image.mp hDS with ⟨⟨i, p⟩, _, rfl⟩; exact card_cl2_le _ _
  · rcases Finset.mem_image.mp hDS with ⟨⟨i, p⟩, _, rfl⟩; exact card_cl2_le _ _
  · rcases Finset.mem_image.mp hDS with ⟨⟨s0, s⟩, _, rfl⟩; exact card_cl1_le _
  · rcases Finset.mem_image.mp hDS with ⟨⟨s0, k, s⟩, _, rfl⟩; exact card_cl3_le _ _ _
  · rcases Finset.mem_image.mp hDS with ⟨⟨s0, k, s⟩, _, rfl⟩; exact card_cl3_le _ _ _
  · rcases Finset.mem_image.mp hDS with ⟨⟨s0, k, s⟩, _, rfl⟩; exact card_cl3_le _ _ _
  · rcases Finset.mem_image.mp hDS with ⟨⟨s0, k, s⟩, _, rfl⟩; exact card_cl3_le _ _ _
  · rcases Finset.mem_image.mp hDS with ⟨⟨s0, s⟩, _, rfl⟩; exact card_cl1_le _
  · rcases Finset.mem_image.mp hDS with ⟨⟨s0, k, s⟩, _, rfl⟩; exact card_cl3_le _ _ _
  · rcases Finset.mem_image.mp hDS with ⟨⟨s0, k, s⟩, _, rfl⟩; exact card_cl3_le _ _ _
  · rcases Finset.mem_image.mp hDS with ⟨⟨s0, k, s⟩, _, rfl⟩; exact card_cl3_le _ _ _
  · rcases Finset.mem_image.mp hDS with ⟨⟨s0, k, s⟩, _, rfl⟩; exact card_cl3_le _ _ _
  · rcases Finset.mem_image.mp hDS with ⟨⟨i, p⟩, _, rfl⟩; exact card_cl2_le _ _
  · rcases Finset.mem_image.mp hDS with ⟨⟨i, p⟩, _, rfl⟩; exact card_cl2_le _ _
  · rcases Finset.mem_image.mp hDS with ⟨⟨i, p, t⟩, _, rfl⟩
    dsimp only
    split_ifs
    · exact card_cl3_le _ _ _
    · simp
  · rcases Finset.mem_image.mp hDS with ⟨⟨i, p, t⟩, _, rfl⟩
    dsimp only
    split_ifs
    · exact card_cl3_le _ _ _
    · simp
  · rcases Finset.mem_image.mp hDS with ⟨⟨i, p⟩, _, rfl⟩; exact card_cl2_le _ _
  · rcases Finset.mem_image.mp hDS with ⟨⟨i, p⟩, _, rfl⟩; exact card_cl2_le _ _
  · rcases Finset.mem_image.mp hDS with ⟨i, _, rfl⟩; exact card_cl2_le _ _
  · rcases Finset.mem_image.mp hDS with ⟨⟨i, p⟩, _, rfl⟩
    dsimp only
    split_ifs
    · exact card_cl3_le _ _ _
    · simp
  · rcases Finset.mem_image.mp hDS with ⟨i, _, rfl⟩; exact card_cl2_le _ _
  · rcases Finset.mem_image.mp hDS with ⟨⟨i, p⟩, _, rfl⟩
    dsimp only
    split_ifs
    · exact card_cl3_le _ _ _
    · simp
  · rcases Finset.mem_image.mp hDS with ⟨i, _, rfl⟩; exact card_cl2_le _ _
  · rcases Finset.mem_image.mp hDS with ⟨i, _, rfl⟩; exact card_cl2_le _ _
  · rcases Finset.mem_image.mp hDS with ⟨⟨i, p⟩, _, rfl⟩
    dsimp only
    split_ifs
    · exact card_cl2_le _ _
    · exact card_cl2_le _ _
    · exact card_cl3_le _ _ _
  · simp only [F_conflict, Finset.mem_singleton] at hDS
    rw [hDS]
    exact card_cl1_le _

theorem pow_two_mul_self (w : ℕ) : 2 ^ w * 2 ^ w = 4 ^ w := by
  induction w with
  | zero => simp
  | succ w ih =>
    rw [Nat.pow_succ 2 w, Nat.pow_succ 4 w]
    calc 2 ^ w * 2 * (2 ^ w * 2) = (2 ^ w * 2 ^ w) * 4 := by
          rw [Nat.mul_assoc, Nat.mul_left_comm 2 (2 ^ w) 2, ← Nat.mul_assoc]
      _ = 4 ^ w * 4 := by rw [ih]

theorem two_pow_le_four_pow (w : ℕ) : 2 ^ w ≤ 4 ^ w :=
  Nat.pow_le_pow_left (by decide) w

theorem card_imgProd_le (n w : ℕ) (S : Finset (Fin n × Pat w))
    (g : Fin n × Pat w → Clause (TotVar n w)) :
    (S.image g).card ≤ 2 * ((n + 1) * 4 ^ w) := by
  have h24 : 2 ^ w ≤ 4 ^ w := two_pow_le_four_pow w
  have hpow1 : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ, Nat.mul_comm]
  have hn4leB : n * 4 ^ w ≤ (n + 1) * 4 ^ w := Nat.mul_le_mul_right _ (Nat.le_succ n)
  calc (S.image g).card ≤ S.card := Finset.card_image_le
    _ ≤ (Finset.univ : Finset (Fin n × Pat w)).card := Finset.card_le_univ S
    _ = n * 2 ^ (w + 1) := by simp [Pat]
    _ = 2 * (n * 2 ^ w) := by rw [hpow1, Nat.mul_left_comm]
    _ ≤ 2 * (n * 4 ^ w) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left n h24)
    _ ≤ 2 * ((n + 1) * 4 ^ w) := Nat.mul_le_mul_left 2 hn4leB

theorem card_imgSS_le (n w : ℕ) (S : Finset (State w × State w))
    (g : State w × State w → Clause (TotVar n w)) :
    (S.image g).card ≤ (n + 1) * 4 ^ w := by
  calc (S.image g).card ≤ S.card := Finset.card_image_le
    _ ≤ (Finset.univ : Finset (State w × State w)).card := Finset.card_le_univ S
    _ = 2 ^ w * 2 ^ w := by simp [State]
    _ = 4 ^ w := pow_two_mul_self w
    _ ≤ (n + 1) * 4 ^ w := Nat.le_mul_of_pos_left _ (Nat.succ_pos n)

theorem card_imgSnS_le (n w : ℕ) (g : State w × Fin n × State w → Clause (TotVar n w)) :
    ((Finset.univ : Finset (State w × Fin n × State w)).image g).card ≤ (n + 1) * 4 ^ w := by
  calc ((Finset.univ : Finset (State w × Fin n × State w)).image g).card
      ≤ (Finset.univ : Finset (State w × Fin n × State w)).card := Finset.card_image_le
    _ = 2 ^ w * (n * 2 ^ w) := by simp [State]
    _ = n * (2 ^ w * 2 ^ w) := Nat.mul_left_comm _ _ _
    _ = n * 4 ^ w := by rw [pow_two_mul_self w]
    _ ≤ (n + 1) * 4 ^ w := Nat.mul_le_mul_right _ (Nat.le_succ n)

theorem card_imgNPS_le (n w : ℕ) (S : Finset (Fin n × Pat w × State w))
    (g : Fin n × Pat w × State w → Clause (TotVar n w)) :
    (S.image g).card ≤ 2 * ((n + 1) * 4 ^ w) := by
  have hpow1 : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ, Nat.mul_comm]
  have hn4leB : n * 4 ^ w ≤ (n + 1) * 4 ^ w := Nat.mul_le_mul_right _ (Nat.le_succ n)
  calc (S.image g).card ≤ S.card := Finset.card_image_le
    _ ≤ (Finset.univ : Finset (Fin n × Pat w × State w)).card := Finset.card_le_univ S
    _ = n * (2 ^ (w + 1) * 2 ^ w) := by simp [Pat, State]
    _ = 2 * (n * 4 ^ w) := by rw [hpow1, Nat.mul_assoc, pow_two_mul_self w, Nat.mul_left_comm]
    _ ≤ 2 * ((n + 1) * 4 ^ w) := Nat.mul_le_mul_left 2 hn4leB

theorem card_imgN_le (n w : ℕ) (g : Fin n → Clause (TotVar n w)) :
    ((Finset.univ : Finset (Fin n)).image g).card ≤ (n + 1) * 4 ^ w := by
  have h4pos : 1 ≤ 4 ^ w := Nat.one_le_pow w 4 (by decide)
  calc ((Finset.univ : Finset (Fin n)).image g).card
      ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_image_le
    _ = n := by simp
    _ ≤ n + 1 := Nat.le_succ n
    _ = (n + 1) * 1 := (Nat.mul_one _).symm
    _ ≤ (n + 1) * 4 ^ w := Nat.mul_le_mul_left _ h4pos

theorem card_grp1 (n w : ℕ) :
    (F_disTab n w).card + ((F_disWord n w).card + ((F_prefBase n w).card +
    ((F_prefStep1 n w).card + ((F_prefStep2 n w).card + (F_prefStep3 n w).card)))) ≤
    8 * ((n + 1) * 4 ^ w) := by
  have h1 : (F_disTab n w).card ≤ 2 * ((n + 1) * 4 ^ w) := card_imgProd_le n w _ _
  have h2 : (F_disWord n w).card ≤ 2 * ((n + 1) * 4 ^ w) := card_imgProd_le n w _ _
  have h3 : (F_prefBase n w).card ≤ (n + 1) * 4 ^ w := card_imgSS_le n w _ _
  have h4 : (F_prefStep1 n w).card ≤ (n + 1) * 4 ^ w := card_imgSnS_le n w _
  have h5 : (F_prefStep2 n w).card ≤ (n + 1) * 4 ^ w := card_imgSnS_le n w _
  have h6 : (F_prefStep3 n w).card ≤ (n + 1) * 4 ^ w := card_imgSnS_le n w _
  exact (show ∀ a b c d e f B : ℕ,
      a ≤ 2 * B → b ≤ 2 * B → c ≤ B → d ≤ B → e ≤ B → f ≤ B →
      a + (b + (c + (d + (e + f)))) ≤ 8 * B from by intros; omega) _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6

theorem card_grp2 (n w : ℕ) :
    (F_prefStep4 n w).card + ((F_suffBase n w).card + ((F_suffStep1 n w).card +
    ((F_suffStep2 n w).card + ((F_suffStep3 n w).card + (F_suffStep4 n w).card)))) ≤
    6 * ((n + 1) * 4 ^ w) := by
  have h1 : (F_prefStep4 n w).card ≤ (n + 1) * 4 ^ w := card_imgSnS_le n w _
  have h2 : (F_suffBase n w).card ≤ (n + 1) * 4 ^ w := card_imgSS_le n w _ _
  have h3 : (F_suffStep1 n w).card ≤ (n + 1) * 4 ^ w := card_imgSnS_le n w _
  have h4 : (F_suffStep2 n w).card ≤ (n + 1) * 4 ^ w := card_imgSnS_le n w _
  have h5 : (F_suffStep3 n w).card ≤ (n + 1) * 4 ^ w := card_imgSnS_le n w _
  have h6 : (F_suffStep4 n w).card ≤ (n + 1) * 4 ^ w := card_imgSnS_le n w _
  exact (show ∀ a b c d e f B : ℕ,
      a ≤ B → b ≤ B → c ≤ B → d ≤ B → e ≤ B → f ≤ B →
      a + (b + (c + (d + (e + f)))) ≤ 6 * B from by intros; omega) _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6

theorem card_grp3 (n w : ℕ) :
    (F_allFailBaseP n w).card + ((F_allFailBaseS n w).card + ((F_allFailStepP n w).card +
    ((F_allFailStepS n w).card + ((F_unsupDis n w).card + (F_unsupFail n w).card)))) ≤
    12 * ((n + 1) * 4 ^ w) := by
  have h1 : (F_allFailBaseP n w).card ≤ 2 * ((n + 1) * 4 ^ w) := card_imgProd_le n w _ _
  have h2 : (F_allFailBaseS n w).card ≤ 2 * ((n + 1) * 4 ^ w) := card_imgProd_le n w _ _
  have h3 : (F_allFailStepP n w).card ≤ 2 * ((n + 1) * 4 ^ w) := card_imgNPS_le n w _ _
  have h4 : (F_allFailStepS n w).card ≤ 2 * ((n + 1) * 4 ^ w) := card_imgNPS_le n w _ _
  have h5 : (F_unsupDis n w).card ≤ 2 * ((n + 1) * 4 ^ w) := card_imgProd_le n w _ _
  have h6 : (F_unsupFail n w).card ≤ 2 * ((n + 1) * 4 ^ w) := card_imgProd_le n w _ _
  exact (show ∀ a b c d e f B : ℕ,
      a ≤ 2 * B → b ≤ 2 * B → c ≤ 2 * B → d ≤ 2 * B → e ≤ 2 * B → f ≤ 2 * B →
      a + (b + (c + (d + (e + f)))) ≤ 12 * B from by intros; omega) _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6

theorem card_grp4 (n w : ℕ) (hn : 0 < n) :
    (F_prefUBase n w).card + ((F_prefUStep n w).card + ((F_suffUBase n w).card +
    ((F_suffUStep n w).card + ((F_wordTrue n w).card + ((F_wordFalse n w).card +
    ((F_tabForce n w).card + ((F_conflict n w hn).card + 0))))))) ≤
    11 * ((n + 1) * 4 ^ w) := by
  have h1 : (F_prefUBase n w).card ≤ (n + 1) * 4 ^ w := card_imgN_le n w _
  have h2 : (F_prefUStep n w).card ≤ 2 * ((n + 1) * 4 ^ w) := card_imgProd_le n w _ _
  have h3 : (F_suffUBase n w).card ≤ (n + 1) * 4 ^ w := card_imgN_le n w _
  have h4 : (F_suffUStep n w).card ≤ 2 * ((n + 1) * 4 ^ w) := card_imgProd_le n w _ _
  have h5 : (F_wordTrue n w).card ≤ (n + 1) * 4 ^ w := card_imgN_le n w _
  have h6 : (F_wordFalse n w).card ≤ (n + 1) * 4 ^ w := card_imgN_le n w _
  have h7 : (F_tabForce n w).card ≤ 2 * ((n + 1) * 4 ^ w) := card_imgProd_le n w _ _
  have h8 : (F_conflict n w hn).card ≤ (n + 1) * 4 ^ w := by
    simp only [F_conflict, Finset.card_singleton]
    exact le_trans (Nat.one_le_pow w 4 (by decide)) (Nat.le_mul_of_pos_left _ (Nat.succ_pos n))
  exact (show ∀ a b c d e f g h B : ℕ,
      a ≤ B → b ≤ 2 * B → c ≤ B → d ≤ 2 * B → e ≤ B → f ≤ B → g ≤ 2 * B → h ≤ B →
      a + (b + (c + (d + (e + (f + (g + (h + 0))))))) ≤ 11 * B from by intros; omega)
    _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8

theorem sum26_le
    {a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 B : ℕ}
    (h1 : a1 + (a2 + (a3 + (a4 + (a5 + a6)))) ≤ 8 * B)
    (h2 : a7 + (a8 + (a9 + (a10 + (a11 + a12)))) ≤ 6 * B)
    (h3 : a13 + (a14 + (a15 + (a16 + (a17 + a18)))) ≤ 12 * B)
    (h4 : a19 + (a20 + (a21 + (a22 + (a23 + (a24 + (a25 + (a26 + 0))))))) ≤ 11 * B) :
    a1 + (a2 + (a3 + (a4 + (a5 + (a6 + (a7 + (a8 + (a9 + (a10 + (a11 + (a12 +
    (a13 + (a14 + (a15 + (a16 + (a17 + (a18 + (a19 + (a20 + (a21 + (a22 +
    (a23 + (a24 + (a25 + (a26 + 0))))))))))))))))))))))))) ≤ 37 * B := by
  have hstep : ∀ x1 x2 x3 x4 x5 x6 R : ℕ,
      x1 + (x2 + (x3 + (x4 + (x5 + (x6 + R))))) = (x1 + (x2 + (x3 + (x4 + (x5 + x6))))) + R := by
    intro x1 x2 x3 x4 x5 x6 R; omega
  rw [hstep a1 a2 a3 a4 a5 a6, hstep a7 a8 a9 a10 a11 a12, hstep a13 a14 a15 a16 a17 a18]
  exact (show ∀ u1 u2 u3 u4 b : ℕ,
      u1 ≤ 8 * b → u2 ≤ 6 * b → u3 ≤ 12 * b → u4 ≤ 11 * b →
      u1 + (u2 + (u3 + u4)) ≤ 37 * b from by intros; omega) _ _ _ _ B h1 h2 h3 h4

theorem size_bound_F_all (n w : ℕ) (hn : 0 < n) :
    mCard n w + ∑ D ∈ F_all n w hn, D.card ≤ 128 * (n + 1) * 4 ^ w := by
  set B := (n + 1) * 4 ^ w
  have h24 : 2 ^ w ≤ 4 ^ w := two_pow_le_four_pow w
  have hmul : 2 ^ w * 2 ^ w = 4 ^ w := pow_two_mul_self w
  have hpow1 : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ, Nat.mul_comm]
  have hn4leB : n * 4 ^ w ≤ B := Nat.mul_le_mul_right _ (Nat.le_succ n)
  have hn2leB : n * 2 ^ (w + 1) ≤ 2 * B := by
    calc n * 2 ^ (w + 1) = 2 * (n * 2 ^ w) := by rw [hpow1, Nat.mul_left_comm]
      _ ≤ 2 * (n * 4 ^ w) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left n h24)
      _ ≤ 2 * B := Nat.mul_le_mul_left 2 hn4leB
  have h2n4 : n * (2 ^ (w + 1) * 2 ^ w) ≤ 2 * B := by
    have heq : n * (2 ^ (w + 1) * 2 ^ w) = 2 * (n * 4 ^ w) := by
      rw [hpow1, Nat.mul_assoc, hmul, Nat.mul_left_comm]
    rw [heq]
    exact Nat.mul_le_mul_left 2 hn4leB
  have hsnsB : 2 ^ w * ((n + 1) * 2 ^ w) = B := by
    change 2 ^ w * ((n + 1) * 2 ^ w) = (n + 1) * 4 ^ w
    rw [Nat.mul_left_comm, hmul]
  have hm : mCard n w ≤ 12 * B := by
    have hcard : mCard n w =
        n * 2 ^ (w + 1) + (2 ^ w * ((n + 1) * 2 ^ w) + (2 ^ w * ((n + 1) * 2 ^ w) +
        (n * (2 ^ (w + 1) * 2 ^ w) + (n * 2 ^ (w + 1) + (n * 2 ^ (w + 1) + n * 2 ^ (w + 1)))))) := by
      simp [mCard, AuxT, State, Pat, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    rw [hcard, hsnsB]
    omega
  have hsum : ∑ D ∈ F_all n w hn, D.card ≤ 3 * (F_all n w hn).card := by
    calc ∑ D ∈ F_all n w hn, D.card
        ≤ ∑ _D ∈ F_all n w hn, 3 := Finset.sum_le_sum fun D hD => card_le_three_F_all n w hn D hD
      _ = 3 * (F_all n w hn).card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  have hFcard : (F_all n w hn).card ≤ 37 * B := by
    have hsumL : ((F_list n w hn).map Finset.card).sum ≤ 37 * B := by
      rw [F_list]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      exact sum26_le (card_grp1 n w) (card_grp2 n w) (card_grp3 n w) (card_grp4 n w hn)
    exact le_trans (card_unionList_le (F_list n w hn)) hsumL
  have hRHS : 128 * (n + 1) * 4 ^ w = 128 * B := by
    simp only [B, Nat.mul_assoc]
  rw [hRHS]
  omega

def evalDis {n w : ℕ} (a : Var n w → Bool) (i : Fin n) (p : Pat w) : Bool :=
  !a (Sum.inr (i, patFun p)) || (a (Sum.inl i) != patHead p)

def evalNoPref {n w : ℕ} (a : Var n w → Bool) (s0 : State w) : (k : ℕ) → State w → Bool
  | 0, s => decide (s0 ≠ s)
  | k + 1, s =>
    if hk : k < n then
      (evalNoPref a s0 k (patSrc (inPat false s)) || evalDis a ⟨k, hk⟩ (inPat false s)) &&
      (evalNoPref a s0 k (patSrc (inPat true s)) || evalDis a ⟨k, hk⟩ (inPat true s))
    else true

def evalNoSuffAux {n w : ℕ} (a : Var n w → Bool) (s0 : State w) : (d : ℕ) → State w → Bool
  | 0, s => decide (s0 ≠ s)
  | d + 1, s =>
    if hk : n - (d + 1) < n then
      (evalNoSuffAux a s0 d (patDst (outPat s false)) || evalDis a ⟨n - (d + 1), hk⟩ (outPat s false)) &&
      (evalNoSuffAux a s0 d (patDst (outPat s true)) || evalDis a ⟨n - (d + 1), hk⟩ (outPat s true))
    else true

def evalNoSuff {n w : ℕ} (a : Var n w → Bool) (s0 : State w) (k : Fin (n + 1)) (s : State w) : Bool :=
  evalNoSuffAux a s0 (n - k.val) s

def evalAllFailAux {n w : ℕ} (a : Var n w → Bool) (i : Fin n) (p : Pat w) : (t : ℕ) → Bool
  | 0 => evalNoPref a (stateZero w) i.val (patSrc p) || evalNoSuff a (stateZero w) i.succ (patDst p)
  | t + 1 =>
    if ht : t + 1 < 2 ^ w then
      evalAllFailAux a i p t &&
      (evalNoPref a ⟨t + 1, ht⟩ i.val (patSrc p) || evalNoSuff a ⟨t + 1, ht⟩ i.succ (patDst p))
    else true

def evalUnsup {n w : ℕ} (a : Var n w → Bool) (i : Fin n) (p : Pat w) : Bool :=
  evalDis a i p || evalAllFailAux a i p (2 ^ w - 1)

def evalPrefUAux {n w : ℕ} (a : Var n w → Bool) (i : Fin n) : (t : ℕ) → Bool
  | 0 => evalUnsup a i (patZero w)
  | t + 1 =>
    if ht : t + 1 < 2 ^ (w + 1) then
      evalPrefUAux a i t && evalUnsup a i ⟨t + 1, ht⟩
    else true

def evalSuffUAux {n w : ℕ} (a : Var n w → Bool) (i : Fin n) : (d : ℕ) → Bool
  | 0 => evalUnsup a i (patLast w)
  | d + 1 =>
    if ht : 2 ^ (w + 1) - 1 - (d + 1) < 2 ^ (w + 1) then
      evalSuffUAux a i d && evalUnsup a i ⟨2 ^ (w + 1) - 1 - (d + 1), ht⟩
    else true

def evalSuffU {n w : ℕ} (a : Var n w → Bool) (i : Fin n) (p : Pat w) : Bool :=
  evalSuffUAux a i (2 ^ (w + 1) - 1 - p.val)

noncomputable def evalAuxT {n w : ℕ} (a : Var n w → Bool) : AuxT n w → Bool
  | Sum.inl (i, p) => evalDis a i p
  | Sum.inr (Sum.inl (s0, k, s)) => evalNoPref a s0 k.val s
  | Sum.inr (Sum.inr (Sum.inl (s0, k, s))) => evalNoSuff a s0 k s
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, p, t)))) => evalAllFailAux a i p t.val
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, p))))) => evalUnsup a i p
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, p)))))) => evalPrefUAux a i p.val
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (i, p)))))) => evalSuffU a i p

noncomputable def evalAux {n w : ℕ} (a : Var n w → Bool) : Fin (mCard n w) → Bool :=
  fun x => evalAuxT a ((eAux n w).symm x)

theorem evalNoPref_false_of_win {n w : ℕ} (hn : 0 < n) (a : Var n w → Bool)
    (hacc : ∀ i : Fin n, a (Sum.inr (i, fun j : Fin (w + 1) =>
      a (Sum.inl ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩))) = true) :
    let sOf := fun k : ℕ => encState w (fun j : Fin w => a (Sum.inl ⟨(k + j.val) % n, Nat.mod_lt _ hn⟩))
    ∀ k : ℕ, k ≤ n → evalNoPref a (sOf 0) k (sOf k) = false := by
  intro sOf k
  induction k with
  | zero =>
    intro _
    simp [evalNoPref]
  | succ k ih =>
    intro hk
    have hklt : k < n := by omega
    have ihk := ih (by omega)
    let p : Pat w := patOfFun (fun j : Fin (w + 1) => a (Sum.inl ⟨(k + j.val) % n, Nat.mod_lt _ hn⟩))
    have hpDst : patDst p = sOf (k + 1) := by
      have h1 : decState w (patDst p) = decState w (sOf (k + 1)) := by
        funext j
        rw [← patFun_succ, patFun_patOfFun]
        simp only [sOf, decState_encState]
        congr 2
        exact Fin.ext (congrArg (· % n) (by simp only [Fin.val_succ]; omega))
      rw [← encState_decState w (patDst p), h1, encState_decState]
    have hpSrc : patSrc p = sOf k := by
      simp only [p, patSrc, patFun_patOfFun, sOf, Fin.val_castSucc]
    have hpDis : evalDis a ⟨k, hklt⟩ p = false := by
      have hT : a (Sum.inr (⟨k, hklt⟩, patFun p)) = true := by
        simpa [p, patFun_patOfFun] using hacc ⟨k, hklt⟩
      have hH : patHead p = a (Sum.inl ⟨k, hklt⟩) := by
        rw [← patFun_zero, patFun_patOfFun]
        have hidx : (⟨(k + 0) % n, Nat.mod_lt _ hn⟩ : Fin n) = ⟨k, hklt⟩ :=
          Fin.ext (by change (k + 0) % n = k; rw [Nat.add_zero, Nat.mod_eq_of_lt hklt])
        simpa [Fin.val_zero] using congrArg (fun u => a (Sum.inl u)) hidx
      simp [evalDis, hT, hH]
    simp only [evalNoPref, hklt, ↓reduceDIte]
    rcases (patDst_eq_iff p (sOf (k + 1))).mp hpDst with hp | hp
    · rw [hp] at hpSrc hpDis
      simp [hpSrc, ihk, hpDis]
    · rw [hp] at hpSrc hpDis
      simp [hpSrc, ihk, hpDis]

theorem evalNoSuff_false_of_win {n w : ℕ} (hn : 0 < n) (a : Var n w → Bool)
    (hacc : ∀ i : Fin n, a (Sum.inr (i, fun j : Fin (w + 1) =>
      a (Sum.inl ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩))) = true) :
    let sOf := fun k : ℕ => encState w (fun j : Fin w => a (Sum.inl ⟨(k + j.val) % n, Nat.mod_lt _ hn⟩))
    ∀ d : ℕ, d ≤ n → evalNoSuffAux a (sOf 0) d (sOf (n - d)) = false := by
  intro sOf d
  induction d with
  | zero =>
    intro _
    simp only [evalNoSuffAux, Nat.sub_zero, decide_eq_false_iff_not, not_not]
    have hf : (fun j : Fin w => a (Sum.inl ⟨(0 + j.val) % n, Nat.mod_lt _ hn⟩)) =
        (fun j : Fin w => a (Sum.inl ⟨(n + j.val) % n, Nat.mod_lt _ hn⟩)) := by
      funext j
      congr 2
      exact Fin.ext (by simp [Nat.add_mod_left])
    simp only [sOf, hf]
  | succ d ih =>
    intro hd
    have hklt : n - (d + 1) < n := by omega
    have ihd := ih (by omega)
    let k := n - (d + 1)
    let p : Pat w := patOfFun (fun j : Fin (w + 1) => a (Sum.inl ⟨(k + j.val) % n, Nat.mod_lt _ hn⟩))
    have hpSrc : patSrc p = sOf k := by
      simp only [p, patSrc, patFun_patOfFun, sOf, Fin.val_castSucc]
    have hpDst : patDst p = sOf (n - d) := by
      have h1 : decState w (patDst p) = decState w (sOf (n - d)) := by
        funext j
        rw [← patFun_succ, patFun_patOfFun]
        simp only [sOf, decState_encState]
        congr 2
        exact Fin.ext (congrArg (· % n) (by simp only [Fin.val_succ, k]; omega))
      rw [← encState_decState w (patDst p), h1, encState_decState]
    have hpDis : evalDis a ⟨k, hklt⟩ p = false := by
      have hT : a (Sum.inr (⟨k, hklt⟩, patFun p)) = true := by
        simpa [p, patFun_patOfFun] using hacc ⟨k, hklt⟩
      have hH : patHead p = a (Sum.inl ⟨k, hklt⟩) := by
        rw [← patFun_zero, patFun_patOfFun]
        have hidx : (⟨(k + 0) % n, Nat.mod_lt _ hn⟩ : Fin n) = ⟨k, hklt⟩ :=
          Fin.ext (by change (k + 0) % n = k; rw [Nat.add_zero, Nat.mod_eq_of_lt hklt])
        simpa [Fin.val_zero] using congrArg (fun u => a (Sum.inl u)) hidx
      simp [evalDis, hT, hH]
    simp only [evalNoSuffAux, hklt, ↓reduceDIte]
    rcases (patSrc_eq_iff p (sOf k)).mp hpSrc with hp | hp
    · rw [hp] at hpDst hpDis
      simp only [k] at hpDst hpDis
      simp [hpDst, ihd, hpDis]
    · rw [hp] at hpDst hpDis
      simp only [k] at hpDst hpDis
      simp [hpDst, ihd, hpDis]

theorem evalAllFailAux_eq_true_iff {n w : ℕ} (a : Var n w → Bool) (i : Fin n) (p : Pat w) :
    ∀ t : ℕ, t < 2 ^ w →
      (evalAllFailAux a i p t = true ↔
        ∀ s0 : State w, s0.val ≤ t →
          evalNoPref a s0 i.val (patSrc p) = true ∨ evalNoSuff a s0 i.succ (patDst p) = true) := by
  intro t
  induction t with
  | zero =>
    intro _
    simp only [evalAllFailAux, Bool.or_eq_true]
    constructor
    · intro h s0 hs0
      have : s0 = stateZero w := Fin.ext (by change s0.val = 0; omega)
      rw [this]; exact h
    · intro h
      exact h (stateZero w) (by simp [stateZero])
  | succ t ih =>
    intro ht
    have ih' := ih (by omega)
    simp only [evalAllFailAux, ht, ↓reduceDIte, Bool.and_eq_true, Bool.or_eq_true, ih']
    constructor
    · rintro ⟨h1, h2⟩ s0 hs0
      by_cases hlt : s0.val ≤ t
      · exact h1 s0 hlt
      · have : s0 = ⟨t + 1, ht⟩ := Fin.ext (by change s0.val = t + 1; omega)
        rw [this]; exact h2
    · intro h
      exact ⟨fun s0 hs0 => h s0 (by omega), h ⟨t + 1, ht⟩ (by simp)⟩

theorem evalPrefUAux_eq_true_iff {n w : ℕ} (a : Var n w → Bool) (i : Fin n) :
    ∀ t : ℕ, t < 2 ^ (w + 1) →
      (evalPrefUAux a i t = true ↔ ∀ p : Pat w, p.val ≤ t → evalUnsup a i p = true) := by
  intro t
  induction t with
  | zero =>
    intro _
    simp only [evalPrefUAux]
    constructor
    · intro h p hp
      have : p = patZero w := Fin.ext (by change p.val = 0; omega)
      rw [this]; exact h
    · intro h
      exact h (patZero w) (by simp [patZero])
  | succ t ih =>
    intro ht
    have ih' := ih (by omega)
    simp only [evalPrefUAux, ht, ↓reduceDIte, Bool.and_eq_true, ih']
    constructor
    · rintro ⟨h1, h2⟩ p hp
      by_cases hlt : p.val ≤ t
      · exact h1 p hlt
      · have : p = ⟨t + 1, ht⟩ := Fin.ext (by change p.val = t + 1; omega)
        rw [this]; exact h2
    · intro h
      exact ⟨fun p hp => h p (by omega), h ⟨t + 1, ht⟩ (by simp)⟩

theorem evalSuffUAux_eq_true_iff {n w : ℕ} (a : Var n w → Bool) (i : Fin n) :
    ∀ d : ℕ, d < 2 ^ (w + 1) →
      (evalSuffUAux a i d = true ↔
        ∀ p : Pat w, 2 ^ (w + 1) - 1 - d ≤ p.val → evalUnsup a i p = true) := by
  intro d
  induction d with
  | zero =>
    intro _
    simp only [evalSuffUAux, Nat.sub_zero]
    constructor
    · intro h p hp
      have : p = patLast w := Fin.ext (by simp [patLast]; have := p.isLt; omega)
      rw [this]; exact h
    · intro h
      exact h (patLast w) (by simp [patLast])
  | succ d ih =>
    intro hd
    have ih' := ih (by omega)
    have hlt : 2 ^ (w + 1) - 1 - (d + 1) < 2 ^ (w + 1) := by
      have := Nat.two_pow_pos (w + 1); omega
    simp only [evalSuffUAux, hlt, ↓reduceDIte, Bool.and_eq_true, ih']
    constructor
    · rintro ⟨h1, h2⟩ p hp
      by_cases hge : 2 ^ (w + 1) - 1 - d ≤ p.val
      · exact h1 p hge
      · have : p = ⟨2 ^ (w + 1) - 1 - (d + 1), hlt⟩ := Fin.ext (by simp only [Fin.val_mk]; omega)
        rw [this]; exact h2
    · intro h
      exact ⟨fun p hp => h p (by omega), h ⟨2 ^ (w + 1) - 1 - (d + 1), hlt⟩ (by simp)⟩

theorem evalSuffU_eq_true_iff {n w : ℕ} (a : Var n w → Bool) (i : Fin n) (p : Pat w) :
    evalSuffU a i p = true ↔ ∀ q : Pat w, p.val ≤ q.val → evalUnsup a i q = true := by
  have hd : 2 ^ (w + 1) - 1 - p.val < 2 ^ (w + 1) := by
    have := p.isLt; omega
  rw [evalSuffU, evalSuffUAux_eq_true_iff a i _ hd]
  have heq : 2 ^ (w + 1) - 1 - (2 ^ (w + 1) - 1 - p.val) = p.val := by
    have := p.isLt; omega
  rw [heq]

theorem evalUnsup_win_false {n w : ℕ} (hn : 0 < n) (a : Var n w → Bool)
    (hacc : ∀ i : Fin n, a (Sum.inr (i, fun j : Fin (w + 1) =>
      a (Sum.inl ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩))) = true) (i : Fin n) :
    let p : Pat w := patOfFun (fun j : Fin (w + 1) =>
      a (Sum.inl ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩))
    evalUnsup a i p = false := by
  intro p
  let sOf := fun k : ℕ => encState w (fun j : Fin w => a (Sum.inl ⟨(k + j.val) % n, Nat.mod_lt _ hn⟩))
  have hdis : evalDis a i p = false := by
    have hT : a (Sum.inr (i, patFun p)) = true := by
      simpa [p, patFun_patOfFun] using hacc i
    have hH : patHead p = a (Sum.inl i) := by
      rw [← patFun_zero, patFun_patOfFun]
      have hidx : (⟨(i.val + 0) % n, Nat.mod_lt _ hn⟩ : Fin n) = i :=
        Fin.ext (by simp [Nat.mod_eq_of_lt i.isLt])
      simpa [Fin.val_zero] using congrArg (fun u => a (Sum.inl u)) hidx
    simp [evalDis, hT, hH]
  have hpSrc : patSrc p = sOf i.val := by
    simp only [p, patSrc, patFun_patOfFun, sOf, Fin.val_castSucc]
  have hpDst : patDst p = sOf (i.val + 1) := by
    have h1 : decState w (patDst p) = decState w (sOf (i.val + 1)) := by
      funext j
      rw [← patFun_succ, patFun_patOfFun]
      simp only [sOf, decState_encState]
      congr 2
      exact Fin.ext (congrArg (· % n) (by simp only [Fin.val_succ]; omega))
    rw [← encState_decState w (patDst p), h1, encState_decState]
  have hnp : evalNoPref a (sOf 0) i.val (patSrc p) = false := by
    rw [hpSrc]; exact evalNoPref_false_of_win hn a hacc i.val (le_of_lt i.isLt)
  have hns : evalNoSuff a (sOf 0) i.succ (patDst p) = false := by
    rw [evalNoSuff, hpDst]
    have h1 := evalNoSuff_false_of_win hn a hacc (n - (i.val + 1)) (by omega)
    have h2 : n - (n - (i.val + 1)) = i.val + 1 := by omega
    rw [h2] at h1
    exact h1
  have hfail : evalAllFailAux a i p (2 ^ w - 1) = false := by
    cases h : evalAllFailAux a i p (2 ^ w - 1)
    · rfl
    · exfalso
      have hlt : 2 ^ w - 1 < 2 ^ w := Nat.sub_lt (Nat.two_pow_pos w) (by decide)
      have hall := (evalAllFailAux_eq_true_iff a i p (2 ^ w - 1) hlt).mp h
      have hs0 := hall (sOf 0) (by have := (sOf 0).isLt; omega)
      rcases hs0 with h1 | h2 <;> simp_all
  simp [evalUnsup, hdis, hfail]

theorem evalAux_satisfies {n w : ℕ} (hn : 0 < n) (a : Var n w → Bool)
    (hacc : ∀ i : Fin n, a (Sum.inr (i, fun j : Fin (w + 1) =>
      a (Sum.inl ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩))) = true) :
    Satisfies (Sum.elim a (evalAux a)) (↑(F_all n w hn) : Set (Clause (TotVar n w))) := by
  have hW : ∀ i, Sum.elim a (evalAux a) (vWord i) = a (Sum.inl i) := fun _ => rfl
  have hT : ∀ i p, Sum.elim a (evalAux a) (vTab i p) = a (Sum.inr (i, patFun p)) := fun _ _ => rfl
  have hD : ∀ i p, Sum.elim a (evalAux a) (vDis i p) = evalDis a i p := by
    intro i p; simp [vDis, evalAux, evalAuxT]
  have hP : ∀ s0 k s, Sum.elim a (evalAux a) (vNoPref s0 k s) = evalNoPref a s0 k.val s := by
    intro s0 k s; simp [vNoPref, evalAux, evalAuxT]
  have hS : ∀ s0 k s, Sum.elim a (evalAux a) (vNoSuff s0 k s) = evalNoSuff a s0 k s := by
    intro s0 k s; simp [vNoSuff, evalAux, evalAuxT]
  have hAF : ∀ i p t, Sum.elim a (evalAux a) (vAllFail i p t) = evalAllFailAux a i p t.val := by
    intro i p t; simp [vAllFail, evalAux, evalAuxT]
  have hU : ∀ i p, Sum.elim a (evalAux a) (vUnsup i p) = evalUnsup a i p := by
    intro i p; simp [vUnsup, evalAux, evalAuxT]
  have hPU : ∀ i p, Sum.elim a (evalAux a) (vPrefU i p) = evalPrefUAux a i p.val := by
    intro i p; simp [vPrefU, evalAux, evalAuxT]
  have hSU : ∀ i p, Sum.elim a (evalAux a) (vSuffU i p) = evalSuffU a i p := by
    intro i p; simp [vSuffU, evalAux, evalAuxT]
  intro D hDmem
  rcases mem_unionList.mp (Finset.mem_coe.mp hDmem) with ⟨S, hSmem, hDS⟩
  simp only [F_list, List.mem_cons, List.not_mem_nil, or_false] at hSmem
  rcases hSmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                    rfl | rfl | rfl | rfl | rfl | rfl
  · rcases Finset.mem_image.mp hDS with ⟨⟨i, p⟩, _, rfl⟩
    have hsat : ClauseSat (Sum.elim a (evalAux a)) (cl2 (negLit (vTab i p, false)) (vDis i p, true)) := by
      apply sat_cl2
      intro ht; simp only [hT] at ht; simp [hD, evalDis, ht]
    simpa [negLit] using hsat
  · rcases Finset.mem_image.mp hDS with ⟨⟨i, p⟩, _, rfl⟩
    have hsat : ClauseSat (Sum.elim a (evalAux a)) (cl2 (negLit (vWord i, !patHead p)) (vDis i p, true)) := by
      apply sat_cl2
      intro hw; simp only [hW] at hw; simp [hD, evalDis, hw]
    simpa [negLit] using hsat
  · rcases Finset.mem_image.mp hDS with ⟨⟨s0, s⟩, hne, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hne
    apply sat_cl1
    simp [hP, evalNoPref, hne]
  · rcases Finset.mem_image.mp hDS with ⟨⟨s0, k, s⟩, _, rfl⟩
    apply sat_cl3 (x := (vNoPref s0 k.castSucc (patSrc (inPat false s)), true))
                  (y := (vNoPref s0 k.castSucc (patSrc (inPat true s)), true))
                  (z := (vNoPref s0 k.succ s, true))
    intro h1 h2; simp only [hP, Fin.val_castSucc] at h1 h2; simp [hP, evalNoPref, k.isLt, h1, h2]
  · rcases Finset.mem_image.mp hDS with ⟨⟨s0, k, s⟩, _, rfl⟩
    apply sat_cl3 (x := (vNoPref s0 k.castSucc (patSrc (inPat false s)), true))
                  (y := (vDis k (inPat true s), true))
                  (z := (vNoPref s0 k.succ s, true))
    intro h1 h2; simp only [hP, hD, Fin.val_castSucc] at h1 h2; simp [hP, evalNoPref, k.isLt, h1, h2]
  · rcases Finset.mem_image.mp hDS with ⟨⟨s0, k, s⟩, _, rfl⟩
    apply sat_cl3 (x := (vDis k (inPat false s), true))
                  (y := (vNoPref s0 k.castSucc (patSrc (inPat true s)), true))
                  (z := (vNoPref s0 k.succ s, true))
    intro h1 h2; simp only [hP, hD, Fin.val_castSucc] at h1 h2; simp [hP, evalNoPref, k.isLt, h1, h2]
  · rcases Finset.mem_image.mp hDS with ⟨⟨s0, k, s⟩, _, rfl⟩
    apply sat_cl3 (x := (vDis k (inPat false s), true))
                  (y := (vDis k (inPat true s), true))
                  (z := (vNoPref s0 k.succ s, true))
    intro h1 h2; simp only [hD] at h1 h2; simp [hP, evalNoPref, k.isLt, h1, h2]
  · rcases Finset.mem_image.mp hDS with ⟨⟨s0, s⟩, hne, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hne
    apply sat_cl1
    simp [hS, evalNoSuff, evalNoSuffAux, hne]
  · rcases Finset.mem_image.mp hDS with ⟨⟨s0, k, s⟩, _, rfl⟩
    apply sat_cl3 (x := (vNoSuff s0 k.succ (patDst (outPat s false)), true))
                  (y := (vNoSuff s0 k.succ (patDst (outPat s true)), true))
                  (z := (vNoSuff s0 k.castSucc s, true))
    intro h1 h2
    simp only [hS, evalNoSuff, Fin.val_succ, Fin.val_castSucc] at h1 h2 ⊢
    have hsub : n - k.val = (n - (k.val + 1)) + 1 := by have := k.isLt; omega
    rw [hsub]
    have hsub2 : n - (n - (k.val + 1) + 1) = k.val := by have := k.isLt; omega
    simp [evalNoSuffAux, hsub2, k.isLt, h1, h2]
  · rcases Finset.mem_image.mp hDS with ⟨⟨s0, k, s⟩, _, rfl⟩
    apply sat_cl3 (x := (vNoSuff s0 k.succ (patDst (outPat s false)), true))
                  (y := (vDis k (outPat s true), true))
                  (z := (vNoSuff s0 k.castSucc s, true))
    intro h1 h2
    simp only [hS, hD, evalNoSuff, Fin.val_succ, Fin.val_castSucc] at h1 h2 ⊢
    have hsub : n - k.val = (n - (k.val + 1)) + 1 := by have := k.isLt; omega
    rw [hsub]
    have hsub2 : n - (n - (k.val + 1) + 1) = k.val := by have := k.isLt; omega
    simp [evalNoSuffAux, hsub2, k.isLt, h1, h2]
  · rcases Finset.mem_image.mp hDS with ⟨⟨s0, k, s⟩, _, rfl⟩
    apply sat_cl3 (x := (vDis k (outPat s false), true))
                  (y := (vNoSuff s0 k.succ (patDst (outPat s true)), true))
                  (z := (vNoSuff s0 k.castSucc s, true))
    intro h1 h2
    simp only [hS, hD, evalNoSuff, Fin.val_succ, Fin.val_castSucc] at h1 h2 ⊢
    have hsub : n - k.val = (n - (k.val + 1)) + 1 := by have := k.isLt; omega
    rw [hsub]
    have hsub2 : n - (n - (k.val + 1) + 1) = k.val := by have := k.isLt; omega
    simp [evalNoSuffAux, hsub2, k.isLt, h1, h2]
  · rcases Finset.mem_image.mp hDS with ⟨⟨s0, k, s⟩, _, rfl⟩
    apply sat_cl3 (x := (vDis k (outPat s false), true))
                  (y := (vDis k (outPat s true), true))
                  (z := (vNoSuff s0 k.castSucc s, true))
    intro h1 h2
    simp only [hS, hD, evalNoSuff, Fin.val_castSucc] at h1 h2 ⊢
    have hsub : n - k.val = (n - (k.val + 1)) + 1 := by have := k.isLt; omega
    rw [hsub]
    have hsub2 : n - (n - (k.val + 1) + 1) = k.val := by have := k.isLt; omega
    simp [evalNoSuffAux, hsub2, k.isLt, h1, h2]
  · rcases Finset.mem_image.mp hDS with ⟨⟨i, p⟩, _, rfl⟩
    apply sat_cl2 (x := (vNoPref (stateZero w) i.castSucc (patSrc p), true))
                  (y := (vAllFail i p (stateZero w), true))
    intro h1
    simp only [hP, Fin.val_castSucc] at h1
    rw [hAF]
    change evalAllFailAux a i p 0 = true
    simp [evalAllFailAux, h1]
  · rcases Finset.mem_image.mp hDS with ⟨⟨i, p⟩, _, rfl⟩
    apply sat_cl2 (x := (vNoSuff (stateZero w) i.succ (patDst p), true))
                  (y := (vAllFail i p (stateZero w), true))
    intro h1
    simp only [hS] at h1
    rw [hAF]
    change evalAllFailAux a i p 0 = true
    simp [evalAllFailAux, h1]
  · rcases Finset.mem_image.mp hDS with ⟨⟨i, p, t⟩, hflt, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hflt
    simp only [hflt, ↓reduceDIte]
    apply sat_cl3 (x := (vAllFail i p t, true))
                  (y := (vNoPref ⟨t.val + 1, hflt⟩ i.castSucc (patSrc p), true))
                  (z := (vAllFail i p ⟨t.val + 1, hflt⟩, true))
    intro h1 h2
    simp only [hAF, hP, Fin.val_castSucc] at h1 h2 ⊢
    simp [evalAllFailAux, hflt, h1, h2]
  · rcases Finset.mem_image.mp hDS with ⟨⟨i, p, t⟩, hflt, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hflt
    simp only [hflt, ↓reduceDIte]
    apply sat_cl3 (x := (vAllFail i p t, true))
                  (y := (vNoSuff ⟨t.val + 1, hflt⟩ i.succ (patDst p), true))
                  (z := (vAllFail i p ⟨t.val + 1, hflt⟩, true))
    intro h1 h2
    simp only [hAF, hS] at h1 h2 ⊢
    simp [evalAllFailAux, hflt, h1, h2]
  · rcases Finset.mem_image.mp hDS with ⟨⟨i, p⟩, _, rfl⟩
    apply sat_cl2 (x := (vDis i p, true)) (y := (vUnsup i p, true))
    intro h1; simp only [hD] at h1; simp [hU, evalUnsup, h1]
  · rcases Finset.mem_image.mp hDS with ⟨⟨i, p⟩, _, rfl⟩
    apply sat_cl2 (x := (vAllFail i p (stateLast w), true)) (y := (vUnsup i p, true))
    intro h1; simp only [hAF, stateLast] at h1; simp [hU, evalUnsup, h1]
  · rcases Finset.mem_image.mp hDS with ⟨i, _, rfl⟩
    apply sat_cl2 (x := (vUnsup i (patZero w), true)) (y := (vPrefU i (patZero w), true))
    intro h1
    simp only [hU] at h1
    rw [hPU]
    change evalPrefUAux a i 0 = true
    exact h1
  · rcases Finset.mem_image.mp hDS with ⟨⟨i, p⟩, hflt, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hflt
    simp only [hflt, ↓reduceDIte]
    apply sat_cl3 (x := (vPrefU i p, true))
                  (y := (vUnsup i ⟨p.val + 1, hflt⟩, true))
                  (z := (vPrefU i ⟨p.val + 1, hflt⟩, true))
    intro h1 h2; simp only [hPU, hU] at h1 h2 ⊢; simp [evalPrefUAux, hflt, h1, h2]
  · rcases Finset.mem_image.mp hDS with ⟨i, _, rfl⟩
    apply sat_cl2 (x := (vUnsup i (patLast w), true)) (y := (vSuffU i (patLast w), true))
    intro h1
    simp only [hU] at h1
    rw [hSU, evalSuffU]
    change evalSuffUAux a i (2 ^ (w + 1) - 1 - (2 ^ (w + 1) - 1)) = true
    rw [Nat.sub_self]
    exact h1
  · rcases Finset.mem_image.mp hDS with ⟨⟨i, p⟩, hflt, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hflt
    simp only [hflt, ↓reduceDIte]
    apply sat_cl3 (x := (vSuffU i ⟨p.val + 1, hflt⟩, true))
                  (y := (vUnsup i p, true))
                  (z := (vSuffU i p, true))
    intro h1 h2
    simp only [hSU, hU, evalSuffU] at h1 h2 ⊢
    have hsub : 2 ^ (w + 1) - 1 - p.val = (2 ^ (w + 1) - 1 - (p.val + 1)) + 1 := by omega
    rw [hsub]
    have hsub2 : 2 ^ (w + 1) - 1 - (2 ^ (w + 1) - 1 - (p.val + 1) + 1) = p.val := by omega
    simp [evalSuffUAux, hsub2, p.isLt, h1, h2]
  · rcases Finset.mem_image.mp hDS with ⟨i, _, rfl⟩
    apply sat_cl2 (x := (vPrefU i (patMidLo w), true)) (y := (vWord i, true))
    intro h1
    simp only [hPU, hW] at h1 ⊢
    have hwin := evalUnsup_win_false hn a hacc i
    let p : Pat w := patOfFun (fun j : Fin (w + 1) =>
      a (Sum.inl ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩))
    have hall := (evalPrefUAux_eq_true_iff a i (patMidLo w).val (patMidLo w).isLt).mp h1
    have hgt : ¬ p.val ≤ 2 ^ w - 1 := by
      intro hle
      have := hall p hle
      simp_all [p]
    have hhead : patHead p = true := by
      simp only [patHead, decide_eq_true_eq]
      have := Nat.two_pow_pos w; omega
    have h0 : patHead p = a (Sum.inl i) := by
      rw [← patFun_zero, patFun_patOfFun]
      have hidx : (⟨(i.val + 0) % n, Nat.mod_lt _ hn⟩ : Fin n) = i :=
        Fin.ext (by simp [Nat.mod_eq_of_lt i.isLt])
      simpa [Fin.val_zero] using congrArg (fun u => a (Sum.inl u)) hidx
    rw [← h0, hhead]
  · rcases Finset.mem_image.mp hDS with ⟨i, _, rfl⟩
    apply sat_cl2 (x := (vSuffU i (patMidHi w), true)) (y := (vWord i, false))
    intro h1
    simp only [hSU, hW] at h1 ⊢
    have hwin := evalUnsup_win_false hn a hacc i
    let p : Pat w := patOfFun (fun j : Fin (w + 1) =>
      a (Sum.inl ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩))
    have hall := (evalSuffU_eq_true_iff a i (patMidHi w)).mp h1
    have hlt : ¬ 2 ^ w ≤ p.val := by
      intro hge
      have := hall p hge
      simp_all [p]
    have hhead : patHead p = false := by
      simp [patHead, hlt]
    have h0 : patHead p = a (Sum.inl i) := by
      rw [← patFun_zero, patFun_patOfFun]
      have hidx : (⟨(i.val + 0) % n, Nat.mod_lt _ hn⟩ : Fin n) = i :=
        Fin.ext (by simp [Nat.mod_eq_of_lt i.isLt])
      simpa [Fin.val_zero] using congrArg (fun u => a (Sum.inl u)) hidx
    rw [← h0, hhead]
  · rcases Finset.mem_image.mp hDS with ⟨⟨i, p⟩, _, rfl⟩
    dsimp only
    let q : Pat w := patOfFun (fun j : Fin (w + 1) =>
      a (Sum.inl ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩))
    have hwin : evalUnsup a i q = false := evalUnsup_win_false hn a hacc i
    have hqT : a (Sum.inr (i, patFun q)) = true := by
      simp only [q, patFun_patOfFun]; exact hacc i
    split_ifs with h0 hlast
    · apply sat_cl2 (x := (vSuffU i ⟨1, by
          have hp : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ, Nat.mul_comm]
          have := Nat.two_pow_pos w; omega⟩, true))
                    (y := (vTab i p, true))
      intro h1
      simp only [hSU, hT] at h1 ⊢
      have hall := (evalSuffU_eq_true_iff a i _).mp h1
      have hqp : q = p := by
        apply Fin.ext
        by_contra hne
        have hge : 1 ≤ q.val := by omega
        have := hall q hge
        simp_all
      rw [← hqp]; exact hqT
    · apply sat_cl2 (x := (vPrefU i ⟨p.val - 1, by omega⟩, true))
                    (y := (vTab i p, true))
      intro h1
      simp only [hPU, hT] at h1 ⊢
      have hall := (evalPrefUAux_eq_true_iff a i (p.val - 1) (by omega)).mp h1
      have hqp : q = p := by
        apply Fin.ext
        by_contra hne
        have hle : q.val ≤ p.val - 1 := by have := q.isLt; omega
        have := hall q hle
        simp_all
      rw [← hqp]; exact hqT
    · apply sat_cl3 (x := (vPrefU i ⟨p.val - 1, by omega⟩, true))
                    (y := (vSuffU i ⟨p.val + 1, by omega⟩, true))
                    (z := (vTab i p, true))
      intro h1 h2
      simp only [hPU, hSU, hT] at h1 h2 ⊢
      have hall1 := (evalPrefUAux_eq_true_iff a i (p.val - 1) (by omega)).mp h1
      have hall2 := (evalSuffU_eq_true_iff a i ⟨p.val + 1, by omega⟩).mp h2
      have hqp : q = p := by
        apply Fin.ext
        by_contra hne
        by_cases hlt : q.val < p.val
        · have := hall1 q (by omega); simp_all
        · have := hall2 q (by change p.val + 1 ≤ q.val; omega); simp_all
      rw [← hqp]; exact hqT
  · simp only [F_conflict, Finset.mem_singleton] at hDS
    rw [hDS]
    apply sat_cl1
    simp only [hPU]
    cases hp : evalPrefUAux a ⟨0, hn⟩ (patLast w).val
    · rfl
    · exfalso
      have hall := (evalPrefUAux_eq_true_iff a ⟨0, hn⟩ (patLast w).val (patLast w).isLt).mp hp
      let q : Pat w := patOfFun (fun j : Fin (w + 1) =>
        a (Sum.inl ⟨(0 + j.val) % n, Nat.mod_lt _ hn⟩))
      have h1 := hall q (by simp [patLast]; have := q.isLt; omega)
      have h2 := evalUnsup_win_false hn a hacc ⟨0, hn⟩
      simp_all [q]

theorem up_sound {V : Type} {Γ : Set (Clause V)} {A : Set (Literal V)} {σ : V → Bool}
    (hΓ : Satisfies σ Γ) (hA : ∀ l ∈ A, σ l.1 = l.2) :
    ∀ {l : Literal V}, UPForces Γ A l → σ l.1 = l.2 := by
  intro l h
  induction h with
  | hyp hl => exact hA _ hl
  | @unit D l₁ hD hlD hrest ih =>
    rcases hΓ _ hD with ⟨l', hl'D, hsat⟩
    by_cases heq : l' = l₁
    · subst heq; exact hsat
    · exfalso
      have hneg := ih l' hl'D heq
      simp only [negLit] at hneg
      rw [hsat] at hneg
      cases l'.2 <;> simp at hneg

theorem up_dis {n w : ℕ} (hn : 0 < n) (ρ : Var n w → Option Bool)
    (i : Fin n) (p : Pat w)
    (h : ρ (Sum.inr (i, patFun p)) = some false ∨ ρ (Sum.inl i) = some (!patHead p)) :
    let F : Set (Clause (TotVar n w)) := ↑(F_all n w hn)
    let A : Set (Literal (TotVar n w)) := {l | ∃ v, l.1 = Sum.inl v ∧ ρ v = some l.2}
    UPForces F A (vDis i p, true) := by
  intro F A
  rcases h with ht | hw
  · have hC : cl2 (negLit (vTab i p, false)) (vDis i p, true) ∈ F :=
      mem_F_all_of_mem (S := F_disTab n w) (by simp [F_list])
        (Finset.mem_image.mpr ⟨(i, p), Finset.mem_univ _, by simp [negLit]⟩)
    exact up_imp1 hC (UPForces.hyp ⟨Sum.inr (i, patFun p), rfl, ht⟩)
  · have hC : cl2 (negLit (vWord i, !patHead p)) (vDis i p, true) ∈ F :=
      mem_F_all_of_mem (S := F_disWord n w) (by simp [F_list])
        (Finset.mem_image.mpr ⟨(i, p), Finset.mem_univ _, by simp [negLit]⟩)
    exact up_imp1 hC (UPForces.hyp ⟨Sum.inl i, rfl, hw⟩)

theorem up_noPref_complete {n w : ℕ} (hn : 0 < n) (ρ : Var n w → Option Bool) (s0 : State w) :
    let F : Set (Clause (TotVar n w)) := ↑(F_all n w hn)
    let A : Set (Literal (TotVar n w)) := {l | ∃ v, l.1 = Sum.inl v ∧ ρ v = some l.2}
    ∀ (k : ℕ) (hk : k ≤ n) (s : State w),
      ¬ UPForces F A (vNoPref s0 ⟨k, Nat.lt_succ_of_le hk⟩ s, true) →
      ∃ (path : Fin k → Pat w),
        (∀ r : Fin k, ¬ UPForces F A (vDis ⟨r.val, by omega⟩ (path r), true)) ∧
        (∀ h0 : 0 < k, patSrc (path ⟨0, h0⟩) = s0) ∧
        (∀ (r : Fin k) (hr : r.val + 1 < k), patDst (path r) = patSrc (path ⟨r.val + 1, hr⟩)) ∧
        (∀ h0 : 0 < k, patDst (path ⟨k - 1, by omega⟩) = s) ∧
        (k = 0 → s = s0) := by
  intro F A k
  induction k with
  | zero =>
    intro hk s hnot
    have heq : s = s0 := by
      by_contra hne
      apply hnot
      have hC : cl1 (vNoPref s0 0 s, true) ∈ F :=
        mem_F_all_of_mem (S := F_prefBase n w) (by simp [F_list])
          (Finset.mem_image.mpr ⟨(s0, s), by simp [Ne.symm hne], rfl⟩)
      exact up_unit hC
    exact ⟨fun r => Fin.elim0 r, fun r => Fin.elim0 r, fun h0 => (Nat.lt_irrefl 0 h0).elim,
           fun r => Fin.elim0 r, fun h0 => (Nat.lt_irrefl 0 h0).elim, fun _ => heq⟩
  | succ k ih =>
    intro hk s hnot
    have hklt : k < n := by omega
    let kf : Fin n := ⟨k, hklt⟩
    let p0 := inPat false s
    let p1 := inPat true s
    have hmem1 : cl3 (vNoPref s0 kf.castSucc (patSrc p0), false)
        (vNoPref s0 kf.castSucc (patSrc p1), false) (vNoPref s0 kf.succ s, true) ∈ F :=
      mem_F_all_of_mem (S := F_prefStep1 n w) (by simp [F_list])
        (Finset.mem_image.mpr ⟨(s0, kf, s), Finset.mem_univ _, rfl⟩)
    have hmem2 : cl3 (vNoPref s0 kf.castSucc (patSrc p0), false)
        (vDis kf p1, false) (vNoPref s0 kf.succ s, true) ∈ F :=
      mem_F_all_of_mem (S := F_prefStep2 n w) (by simp [F_list])
        (Finset.mem_image.mpr ⟨(s0, kf, s), Finset.mem_univ _, rfl⟩)
    have hmem3 : cl3 (vDis kf p0, false)
        (vNoPref s0 kf.castSucc (patSrc p1), false) (vNoPref s0 kf.succ s, true) ∈ F :=
      mem_F_all_of_mem (S := F_prefStep3 n w) (by simp [F_list])
        (Finset.mem_image.mpr ⟨(s0, kf, s), Finset.mem_univ _, rfl⟩)
    have hmem4 : cl3 (vDis kf p0, false)
        (vDis kf p1, false) (vNoPref s0 kf.succ s, true) ∈ F :=
      mem_F_all_of_mem (S := F_prefStep4 n w) (by simp [F_list])
        (Finset.mem_image.mpr ⟨(s0, kf, s), Finset.mem_univ _, rfl⟩)
    have hex : ∃ b : Bool,
        ¬ UPForces F A (vNoPref s0 kf.castSucc (patSrc (inPat b s)), true) ∧
        ¬ UPForces F A (vDis kf (inPat b s), true) := by
      by_contra hall
      push_neg at hall
      have h0 := hall false
      have h1 := hall true
      apply hnot
      by_cases a0 : UPForces F A (vNoPref s0 kf.castSucc (patSrc p0), true)
      · by_cases a1 : UPForces F A (vNoPref s0 kf.castSucc (patSrc p1), true)
        · exact up_imp2 (x := (vNoPref s0 kf.castSucc (patSrc p0), true))
            (y := (vNoPref s0 kf.castSucc (patSrc p1), true)) hmem1 a0 a1
        · exact up_imp2 (x := (vNoPref s0 kf.castSucc (patSrc p0), true))
            (y := (vDis kf p1, true)) hmem2 a0 (h1 a1)
      · by_cases a1 : UPForces F A (vNoPref s0 kf.castSucc (patSrc p1), true)
        · exact up_imp2 (x := (vDis kf p0, true))
            (y := (vNoPref s0 kf.castSucc (patSrc p1), true)) hmem3 (h0 a0) a1
        · exact up_imp2 (x := (vDis kf p0, true))
            (y := (vDis kf p1, true)) hmem4 (h0 a0) (h1 a1)
    rcases hex with ⟨b, hnp, hnd⟩
    rcases ih (by omega) (patSrc (inPat b s)) hnp with ⟨prev, hdis, hstart, hconn, hend, hzero⟩
    let path : Fin (k + 1) → Pat w := fun r =>
      if hr : r.val < k then prev ⟨r.val, hr⟩ else inPat b s
    refine ⟨path, ?_, ?_, ?_, ?_, fun h0 => by omega⟩
    · intro r
      by_cases hr : r.val < k
      · simpa [path, hr] using hdis ⟨r.val, hr⟩
      · have hreq : r.val = k := by omega
        have hkeq : (⟨r.val, by omega⟩ : Fin n) = kf := Fin.ext hreq
        simpa [path, hr, hkeq] using hnd
    · intro _
      by_cases hk0 : k = 0
      · subst hk0
        simp only [path, Nat.lt_irrefl, ↓reduceDIte]
        exact hzero rfl
      · have hkpos : 0 < k := by omega
        simpa [path, hkpos] using hstart hkpos
    · intro r hr
      by_cases hr1 : r.val + 1 < k
      · have hr0 : r.val < k := by omega
        simpa [path, hr0, hr1] using hconn ⟨r.val, hr0⟩ hr1
      · have hr0 : r.val < k := by omega
        have hkpos : 0 < k := by omega
        have hidx : (⟨r.val, hr0⟩ : Fin k) = ⟨k - 1, by omega⟩ :=
          Fin.ext (by change r.val = k - 1; omega)
        simp only [path, hr0, ↓reduceDIte, show ¬ r.val + 1 < k by omega]
        rw [hidx]
        exact hend hkpos
    · intro _
      simp only [path, Nat.add_sub_cancel, Nat.lt_irrefl, ↓reduceDIte]
      exact patDst_inPat b s

theorem up_noSuff_complete {n w : ℕ} (hn : 0 < n) (ρ : Var n w → Option Bool) (s0 : State w) :
    let F : Set (Clause (TotVar n w)) := ↑(F_all n w hn)
    let A : Set (Literal (TotVar n w)) := {l | ∃ v, l.1 = Sum.inl v ∧ ρ v = some l.2}
    ∀ (d : ℕ) (hd : d ≤ n) (s : State w),
      ¬ UPForces F A (vNoSuff s0 ⟨n - d, by omega⟩ s, true) →
      ∃ (path : Fin d → Pat w),
        (∀ r : Fin d, ¬ UPForces F A (vDis ⟨n - d + r.val, by omega⟩ (path r), true)) ∧
        (∀ h0 : 0 < d, patSrc (path ⟨0, h0⟩) = s) ∧
        (∀ (r : Fin d) (hr : r.val + 1 < d), patDst (path r) = patSrc (path ⟨r.val + 1, hr⟩)) ∧
        (∀ h0 : 0 < d, patDst (path ⟨d - 1, by omega⟩) = s0) ∧
        (d = 0 → s = s0) := by
  intro F A d
  induction d with
  | zero =>
    intro hd s hnot
    have heq : s = s0 := by
      by_contra hne
      apply hnot
      have hC : cl1 (vNoSuff s0 (Fin.last n) s, true) ∈ F :=
        mem_F_all_of_mem (S := F_suffBase n w) (by simp [F_list])
          (Finset.mem_image.mpr ⟨(s0, s), by simp [Ne.symm hne], rfl⟩)
      exact up_unit hC
    exact ⟨fun r => Fin.elim0 r, fun r => Fin.elim0 r, fun h0 => (Nat.lt_irrefl 0 h0).elim,
           fun r => Fin.elim0 r, fun h0 => (Nat.lt_irrefl 0 h0).elim, fun _ => heq⟩
  | succ d ih =>
    intro hd s hnot
    have hklt : n - (d + 1) < n := by omega
    let kf : Fin n := ⟨n - (d + 1), hklt⟩
    let p0 := outPat s false
    let p1 := outPat s true
    have hmem1 : cl3 (vNoSuff s0 kf.succ (patDst p0), false)
        (vNoSuff s0 kf.succ (patDst p1), false) (vNoSuff s0 kf.castSucc s, true) ∈ F :=
      mem_F_all_of_mem (S := F_suffStep1 n w) (by simp [F_list])
        (Finset.mem_image.mpr ⟨(s0, kf, s), Finset.mem_univ _, rfl⟩)
    have hmem2 : cl3 (vNoSuff s0 kf.succ (patDst p0), false)
        (vDis kf p1, false) (vNoSuff s0 kf.castSucc s, true) ∈ F :=
      mem_F_all_of_mem (S := F_suffStep2 n w) (by simp [F_list])
        (Finset.mem_image.mpr ⟨(s0, kf, s), Finset.mem_univ _, rfl⟩)
    have hmem3 : cl3 (vDis kf p0, false)
        (vNoSuff s0 kf.succ (patDst p1), false) (vNoSuff s0 kf.castSucc s, true) ∈ F :=
      mem_F_all_of_mem (S := F_suffStep3 n w) (by simp [F_list])
        (Finset.mem_image.mpr ⟨(s0, kf, s), Finset.mem_univ _, rfl⟩)
    have hmem4 : cl3 (vDis kf p0, false)
        (vDis kf p1, false) (vNoSuff s0 kf.castSucc s, true) ∈ F :=
      mem_F_all_of_mem (S := F_suffStep4 n w) (by simp [F_list])
        (Finset.mem_image.mpr ⟨(s0, kf, s), Finset.mem_univ _, rfl⟩)
    have hex : ∃ b : Bool,
        ¬ UPForces F A (vNoSuff s0 kf.succ (patDst (outPat s b)), true) ∧
        ¬ UPForces F A (vDis kf (outPat s b), true) := by
      by_contra hall
      push_neg at hall
      have h0 := hall false
      have h1 := hall true
      apply hnot
      by_cases a0 : UPForces F A (vNoSuff s0 kf.succ (patDst p0), true)
      · by_cases a1 : UPForces F A (vNoSuff s0 kf.succ (patDst p1), true)
        · exact up_imp2 (x := (vNoSuff s0 kf.succ (patDst p0), true))
            (y := (vNoSuff s0 kf.succ (patDst p1), true)) hmem1 a0 a1
        · exact up_imp2 (x := (vNoSuff s0 kf.succ (patDst p0), true))
            (y := (vDis kf p1, true)) hmem2 a0 (h1 a1)
      · by_cases a1 : UPForces F A (vNoSuff s0 kf.succ (patDst p1), true)
        · exact up_imp2 (x := (vDis kf p0, true))
            (y := (vNoSuff s0 kf.succ (patDst p1), true)) hmem3 (h0 a0) a1
        · exact up_imp2 (x := (vDis kf p0, true))
            (y := (vDis kf p1, true)) hmem4 (h0 a0) (h1 a1)
    rcases hex with ⟨b, hns, hnd⟩
    have hksucc : kf.succ = ⟨n - d, by omega⟩ := Fin.ext (by simp [kf]; omega)
    rw [hksucc] at hns
    rcases ih (by omega) (patDst (outPat s b)) hns with ⟨next, hdis, hstart, hconn, hend, hzero⟩
    let path : Fin (d + 1) → Pat w := fun r =>
      if hr : r.val = 0 then outPat s b else next ⟨r.val - 1, by omega⟩
    refine ⟨path, ?_, ?_, ?_, ?_, fun h0 => by omega⟩
    · intro r
      by_cases hr : r.val = 0
      · have hpath : path r = outPat s b := by
          dsimp only [path]
          exact dif_pos hr
        have hidx : (⟨n - (d + 1) + r.val, by omega⟩ : Fin n) = kf :=
          Fin.ext (by change n - (d + 1) + r.val = n - (d + 1); omega)
        rw [hpath, hidx]
        exact hnd
      · have hlt1 : r.val - 1 < d := by have := r.isLt; omega
        have hidx : (⟨n - (d + 1) + r.val, by omega⟩ : Fin n) = ⟨n - d + (r.val - 1), by omega⟩ :=
          Fin.ext (by change n - (d + 1) + r.val = n - d + (r.val - 1); omega)
        have hpath : path r = next ⟨r.val - 1, hlt1⟩ := by
          dsimp only [path]
          exact dif_neg hr
        rw [hpath, hidx]
        exact hdis ⟨r.val - 1, hlt1⟩
    · intro _
      simp only [path, Fin.val_zero, ↓reduceDIte]
      exact patSrc_outPat s b
    · intro r hr
      by_cases hr0 : r.val = 0
      · have hdpos : 0 < d := by omega
        have hne1 : r.val + 1 ≠ 0 := by omega
        simp only [path, dif_pos hr0, dif_neg hne1]
        have hidx : (⟨r.val + 1 - 1, by omega⟩ : Fin d) = ⟨0, hdpos⟩ :=
          Fin.ext (by change r.val + 1 - 1 = 0; omega)
        rw [hidx, hstart hdpos]
      · have hne1 : r.val + 1 ≠ 0 := by omega
        simp only [path, dif_neg hr0, dif_neg hne1]
        have hlt1 : r.val - 1 < d := by have := r.isLt; omega
        have hlt2 : r.val - 1 + 1 < d := by omega
        have h1 := hconn ⟨r.val - 1, hlt1⟩ hlt2
        have hidx : (⟨r.val - 1 + 1, hlt2⟩ : Fin d) = ⟨r.val + 1 - 1, by omega⟩ :=
          Fin.ext (by change r.val - 1 + 1 = r.val + 1 - 1; omega)
        rw [hidx] at h1
        exact h1
    · intro _
      by_cases hd0 : d = 0
      · subst hd0
        simp only [path, Nat.sub_self, ↓reduceDIte]
        exact hzero rfl
      · have hdpos : 0 < d := by omega
        simp only [path, Nat.add_sub_cancel, show d ≠ 0 by omega, ↓reduceDIte]
        exact hend hdpos

theorem up_allFail_of_forall {n w : ℕ} (hn : 0 < n) (ρ : Var n w → Option Bool)
    (i : Fin n) (p : Pat w) :
    let F : Set (Clause (TotVar n w)) := ↑(F_all n w hn)
    let A : Set (Literal (TotVar n w)) := {l | ∃ v, l.1 = Sum.inl v ∧ ρ v = some l.2}
    (∀ s0 : State w,
      UPForces F A (vNoPref s0 i.castSucc (patSrc p), true) ∨
      UPForces F A (vNoSuff s0 i.succ (patDst p), true)) →
    ∀ (t : ℕ) (ht : t < 2 ^ w), UPForces F A (vAllFail i p ⟨t, ht⟩, true) := by
  intro F A hall t
  induction t with
  | zero =>
    intro ht
    have hs : (⟨0, ht⟩ : State w) = stateZero w := rfl
    rw [hs]
    rcases hall (stateZero w) with h1 | h2
    · have hC : cl2 (vNoPref (stateZero w) i.castSucc (patSrc p), false)
          (vAllFail i p (stateZero w), true) ∈ F :=
        mem_F_all_of_mem (S := F_allFailBaseP n w) (by simp [F_list])
          (Finset.mem_image.mpr ⟨(i, p), Finset.mem_univ _, rfl⟩)
      exact up_imp1 (x := (vNoPref (stateZero w) i.castSucc (patSrc p), true)) hC h1
    · have hC : cl2 (vNoSuff (stateZero w) i.succ (patDst p), false)
          (vAllFail i p (stateZero w), true) ∈ F :=
        mem_F_all_of_mem (S := F_allFailBaseS n w) (by simp [F_list])
          (Finset.mem_image.mpr ⟨(i, p), Finset.mem_univ _, rfl⟩)
      exact up_imp1 (x := (vNoSuff (stateZero w) i.succ (patDst p), true)) hC h2
  | succ t ih =>
    intro ht
    have hprev := ih (by omega)
    rcases hall ⟨t + 1, ht⟩ with h1 | h2
    · have hC : cl3 (vAllFail i p ⟨t, by omega⟩, false)
          (vNoPref ⟨t + 1, ht⟩ i.castSucc (patSrc p), false)
          (vAllFail i p ⟨t + 1, ht⟩, true) ∈ F :=
        mem_F_all_of_mem (S := F_allFailStepP n w) (by simp [F_list])
          (Finset.mem_image.mpr ⟨(i, p, ⟨t, by omega⟩), by simp [ht], by simp [ht]⟩)
      exact up_imp2 (x := (vAllFail i p ⟨t, by omega⟩, true))
        (y := (vNoPref ⟨t + 1, ht⟩ i.castSucc (patSrc p), true)) hC hprev h1
    · have hC : cl3 (vAllFail i p ⟨t, by omega⟩, false)
          (vNoSuff ⟨t + 1, ht⟩ i.succ (patDst p), false)
          (vAllFail i p ⟨t + 1, ht⟩, true) ∈ F :=
        mem_F_all_of_mem (S := F_allFailStepS n w) (by simp [F_list])
          (Finset.mem_image.mpr ⟨(i, p, ⟨t, by omega⟩), by simp [ht], by simp [ht]⟩)
      exact up_imp2 (x := (vAllFail i p ⟨t, by omega⟩, true))
        (y := (vNoSuff ⟨t + 1, ht⟩ i.succ (patDst p), true)) hC hprev h2

theorem up_unsup_complete {n w : ℕ} (hn : 0 < n) (ρ : Var n w → Option Bool)
    (i : Fin n) (p : Pat w) :
    let F : Set (Clause (TotVar n w)) := ↑(F_all n w hn)
    let A : Set (Literal (TotVar n w)) := {l | ∃ v, l.1 = Sum.inl v ∧ ρ v = some l.2}
    ¬ UPForces F A (vUnsup i p, true) →
    ∃ a : Var n w → Bool,
      (∀ k : Fin n, a (Sum.inr (k, fun j : Fin (w + 1) =>
        a (Sum.inl ⟨(k.val + j.val) % n, Nat.mod_lt _ hn⟩))) = true) ∧
      (∀ v b, ρ v = some b → a v = b) ∧
      (fun j : Fin (w + 1) => a (Sum.inl ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩)) = patFun p := by
  intro F A hnot
  have hndis : ¬ UPForces F A (vDis i p, true) := by
    intro hd
    apply hnot
    have hC : cl2 (vDis i p, false) (vUnsup i p, true) ∈ F :=
      mem_F_all_of_mem (S := F_unsupDis n w) (by simp [F_list])
        (Finset.mem_image.mpr ⟨(i, p), Finset.mem_univ _, rfl⟩)
    exact up_imp1 (x := (vDis i p, true)) hC hd
  have hnaf : ¬ UPForces F A (vAllFail i p (stateLast w), true) := by
    intro haf
    apply hnot
    have hC : cl2 (vAllFail i p (stateLast w), false) (vUnsup i p, true) ∈ F :=
      mem_F_all_of_mem (S := F_unsupFail n w) (by simp [F_list])
        (Finset.mem_image.mpr ⟨(i, p), Finset.mem_univ _, rfl⟩)
    exact up_imp1 (x := (vAllFail i p (stateLast w), true)) hC haf
  have hexS0 : ∃ s0 : State w,
      ¬ UPForces F A (vNoPref s0 i.castSucc (patSrc p), true) ∧
      ¬ UPForces F A (vNoSuff s0 i.succ (patDst p), true) := by
    by_contra hall
    push_neg at hall
    apply hnaf
    have hlt : 2 ^ w - 1 < 2 ^ w := Nat.sub_lt (Nat.two_pow_pos w) (by decide)
    exact up_allFail_of_forall hn ρ i p
      (fun s0 => by by_cases h : UPForces F A (vNoPref s0 i.castSucc (patSrc p), true)
                    · exact Or.inl h
                    · exact Or.inr (hall s0 h))
      (2 ^ w - 1) hlt
  rcases hexS0 with ⟨s0, hnp, hns⟩
  rcases up_noPref_complete hn ρ s0 i.val (le_of_lt i.isLt) (patSrc p) hnp with
    ⟨pref, hpdis, hpstart, hpconn, hpend, hpzero⟩
  have hisucc : i.succ = ⟨n - (n - (i.val + 1)), by have := i.isLt; omega⟩ :=
    Fin.ext (by simp; have := i.isLt; omega)
  rw [hisucc] at hns
  rcases up_noSuff_complete hn ρ s0 (n - (i.val + 1)) (by omega) (patDst p) hns with
    ⟨suff, hsdis, hsstart, hsconn, hsend, hszero⟩
  let ps : Fin n → Pat w := fun k =>
    if hk1 : k.val < i.val then pref ⟨k.val, hk1⟩
    else if hk2 : k.val = i.val then p
    else suff ⟨k.val - (i.val + 1), by have := k.isLt; omega⟩
  have hps_dis : ∀ k : Fin n, ¬ UPForces F A (vDis k (ps k), true) := by
    intro k
    by_cases hk1 : k.val < i.val
    · simp only [ps, dif_pos hk1]
      exact hpdis ⟨k.val, hk1⟩
    · by_cases hk2 : k.val = i.val
      · simp only [ps, dif_neg hk1, dif_pos hk2]
        have hki : k = i := Fin.ext hk2
        rw [hki]
        exact hndis
      · simp only [ps, dif_neg hk1, dif_neg hk2]
        have hidx : (⟨n - (n - (i.val + 1)) + (k.val - (i.val + 1)), by have := k.isLt; have := i.isLt; omega⟩ : Fin n) = k :=
          Fin.ext (by change n - (n - (i.val + 1)) + (k.val - (i.val + 1)) = k.val; have := k.isLt; have := i.isLt; omega)
        have hsd := hsdis ⟨k.val - (i.val + 1), by have := k.isLt; omega⟩
        rw [hidx] at hsd
        exact hsd
  have hps_step : ∀ k : Fin n,
      patDst (ps k) = patSrc (ps ⟨(k.val + 1) % n, Nat.mod_lt _ hn⟩) := by
    intro k
    by_cases hlast : k.val + 1 = n
    · have hmod : (k.val + 1) % n = 0 := by rw [hlast, Nat.mod_self]
      have h0 : (⟨(k.val + 1) % n, Nat.mod_lt _ hn⟩ : Fin n) = ⟨0, hn⟩ := Fin.ext hmod
      rw [h0]
      have hsrc0 : patSrc (ps ⟨0, hn⟩) = s0 := by
        by_cases hi0 : 0 < i.val
        · simp only [ps, dif_pos hi0]; exact hpstart hi0
        · have hi0' : i.val = 0 := by omega
          have heq0 : (0 : ℕ) = i.val := hi0'.symm
          simp only [ps, dif_neg hi0, dif_pos heq0]
          exact hpzero hi0'
      have hdstLast : patDst (ps k) = s0 := by
        by_cases hk1 : k.val < i.val
        · exfalso; have := i.isLt; omega
        · by_cases hk2 : k.val = i.val
          · simp only [ps, dif_neg hk1, dif_pos hk2]
            exact hszero (by omega)
          · simp only [ps, dif_neg hk1, dif_neg hk2]
            have hdpos : 0 < n - (i.val + 1) := by have := i.isLt; omega
            have hidx : (⟨k.val - (i.val + 1), by have := k.isLt; omega⟩ : Fin (n - (i.val + 1))) =
                ⟨n - (i.val + 1) - 1, by omega⟩ :=
              Fin.ext (by change k.val - (i.val + 1) = n - (i.val + 1) - 1; omega)
            rw [hidx]
            exact hsend hdpos
      rw [hdstLast, hsrc0]
    · have hmod : (k.val + 1) % n = k.val + 1 := Nat.mod_eq_of_lt (by have := k.isLt; omega)
      have hnx : (⟨(k.val + 1) % n, Nat.mod_lt _ hn⟩ : Fin n) = ⟨k.val + 1, by have := k.isLt; omega⟩ :=
        Fin.ext hmod
      rw [hnx]
      by_cases hk1 : k.val < i.val
      · by_cases hk1' : k.val + 1 < i.val
        · simp only [ps, dif_pos hk1, dif_pos hk1']
          exact hpconn ⟨k.val, hk1⟩ hk1'
        · have hkeq : k.val + 1 = i.val := by omega
          simp only [ps, dif_pos hk1, dif_neg hk1', dif_pos hkeq]
          have hipos : 0 < i.val := by omega
          have hidx : (⟨k.val, hk1⟩ : Fin i.val) = ⟨i.val - 1, by omega⟩ :=
            Fin.ext (by change k.val = i.val - 1; omega)
          rw [hidx]
          exact hpend hipos
      · by_cases hk2 : k.val = i.val
        · have hnotlt : ¬ k.val + 1 < i.val := by omega
          have hnoteq : k.val + 1 ≠ i.val := by omega
          simp only [ps, dif_neg hk1, dif_pos hk2, dif_neg hnotlt, dif_neg hnoteq]
          have hdpos : 0 < n - (i.val + 1) := by have := k.isLt; omega
          have hidx : (⟨k.val + 1 - (i.val + 1), by have := k.isLt; omega⟩ : Fin (n - (i.val + 1))) =
              ⟨0, hdpos⟩ := Fin.ext (by change k.val + 1 - (i.val + 1) = 0; omega)
          rw [hidx]
          exact (hsstart hdpos).symm
        · have hnotlt : ¬ k.val + 1 < i.val := by omega
          have hnoteq : k.val + 1 ≠ i.val := by omega
          simp only [ps, dif_neg hk1, dif_neg hk2, dif_neg hnotlt, dif_neg hnoteq]
          have hlt1 : k.val - (i.val + 1) < n - (i.val + 1) := by have := k.isLt; omega
          have hlt2 : k.val - (i.val + 1) + 1 < n - (i.val + 1) := by have := k.isLt; omega
          have h1 := hsconn ⟨k.val - (i.val + 1), hlt1⟩ hlt2
          have hidx : (⟨k.val - (i.val + 1) + 1, hlt2⟩ : Fin (n - (i.val + 1))) =
              ⟨k.val + 1 - (i.val + 1), by have := k.isLt; omega⟩ :=
            Fin.ext (by change k.val - (i.val + 1) + 1 = k.val + 1 - (i.val + 1); omega)
          rw [hidx] at h1
          exact h1
  let a : Var n w → Bool := fun v =>
    match v with
    | Sum.inl k => patHead (ps k)
    | Sum.inr (k, f) =>
      match ρ (Sum.inr (k, f)) with
      | some false => false
      | _ => true
  have hwin_eq : ∀ k : Fin n,
      (fun j : Fin (w + 1) => a (Sum.inl ⟨(k.val + j.val) % n, Nat.mod_lt _ hn⟩)) = patFun (ps k) := by
    intro k
    funext j
    exact (cycle_patFun_eq hn ps hps_step j k).symm
  refine ⟨a, ?_, ?_, ?_⟩
  · intro k
    rw [hwin_eq k]
    simp only [a]
    cases hρ : ρ (Sum.inr (k, patFun (ps k))) with
    | none => rfl
    | some b =>
      cases b with
      | true => rfl
      | false =>
        exfalso
        exact hps_dis k (up_dis hn ρ k (ps k) (Or.inl hρ))
  · intro v b hρ
    cases v with
    | inl k =>
      simp only [a]
      by_contra hne
      have hneg : b = !patHead (ps k) := by
        cases b <;> cases hpk : patHead (ps k) <;> simp_all
      rw [hneg] at hρ
      exact hps_dis k (up_dis hn ρ k (ps k) (Or.inr hρ))
    | inr kf =>
      simp only [a, hρ]
      cases b <;> rfl
  · rw [hwin_eq i]
    simp [ps]

theorem up_prefU_of_forall {n w : ℕ} (hn : 0 < n) (ρ : Var n w → Option Bool) (i : Fin n) :
    let F : Set (Clause (TotVar n w)) := ↑(F_all n w hn)
    let A : Set (Literal (TotVar n w)) := {l | ∃ v, l.1 = Sum.inl v ∧ ρ v = some l.2}
    ∀ (t : ℕ) (ht : t < 2 ^ (w + 1)),
      (∀ p : Pat w, p.val ≤ t → UPForces F A (vUnsup i p, true)) →
      UPForces F A (vPrefU i ⟨t, ht⟩, true) := by
  intro F A t
  induction t with
  | zero =>
    intro ht hall
    have hC : cl2 (vUnsup i (patZero w), false) (vPrefU i (patZero w), true) ∈ F :=
      mem_F_all_of_mem (S := F_prefUBase n w) (by simp [F_list])
        (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    exact up_imp1 (x := (vUnsup i (patZero w), true)) hC (hall (patZero w) (by simp [patZero]))
  | succ t ih =>
    intro ht hall
    have hprev := ih (by omega) (fun p hp => hall p (by omega))
    have hcur := hall ⟨t + 1, ht⟩ (by simp)
    have hC : cl3 (vPrefU i ⟨t, by omega⟩, false)
        (vUnsup i ⟨t + 1, ht⟩, false) (vPrefU i ⟨t + 1, ht⟩, true) ∈ F :=
      mem_F_all_of_mem (S := F_prefUStep n w) (by simp [F_list])
        (Finset.mem_image.mpr ⟨(i, ⟨t, by omega⟩), by simp [ht], by simp [ht]⟩)
    exact up_imp2 (x := (vPrefU i ⟨t, by omega⟩, true))
      (y := (vUnsup i ⟨t + 1, ht⟩, true)) hC hprev hcur

theorem up_suffU_of_forall {n w : ℕ} (hn : 0 < n) (ρ : Var n w → Option Bool) (i : Fin n) :
    let F : Set (Clause (TotVar n w)) := ↑(F_all n w hn)
    let A : Set (Literal (TotVar n w)) := {l | ∃ v, l.1 = Sum.inl v ∧ ρ v = some l.2}
    ∀ (d : ℕ) (hd : d < 2 ^ (w + 1)),
      (∀ p : Pat w, 2 ^ (w + 1) - 1 - d ≤ p.val → UPForces F A (vUnsup i p, true)) →
      UPForces F A (vSuffU i ⟨2 ^ (w + 1) - 1 - d, by have := Nat.two_pow_pos (w + 1); omega⟩, true) := by
  intro F A d
  induction d with
  | zero =>
    intro hd hall
    have hC : cl2 (vUnsup i (patLast w), false) (vSuffU i (patLast w), true) ∈ F :=
      mem_F_all_of_mem (S := F_suffUBase n w) (by simp [F_list])
        (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    exact up_imp1 (x := (vUnsup i (patLast w), true)) hC (hall (patLast w) (by simp [patLast]))
  | succ d ih =>
    intro hd hall
    have hprev := ih (by omega) (fun p hp => hall p (by omega))
    have hlt : 2 ^ (w + 1) - 1 - (d + 1) < 2 ^ (w + 1) := by
      have := Nat.two_pow_pos (w + 1); omega
    have hlt1 : 2 ^ (w + 1) - 1 - (d + 1) + 1 < 2 ^ (w + 1) := by omega
    have heq : (⟨2 ^ (w + 1) - 1 - (d + 1) + 1, hlt1⟩ : Pat w) =
        ⟨2 ^ (w + 1) - 1 - d, by have := Nat.two_pow_pos (w + 1); omega⟩ :=
      Fin.ext (by simp only [Fin.val_mk]; omega)
    have hcur := hall ⟨2 ^ (w + 1) - 1 - (d + 1), hlt⟩ (by simp)
    have hC : cl3 (vSuffU i ⟨2 ^ (w + 1) - 1 - (d + 1) + 1, hlt1⟩, false)
        (vUnsup i ⟨2 ^ (w + 1) - 1 - (d + 1), hlt⟩, false)
        (vSuffU i ⟨2 ^ (w + 1) - 1 - (d + 1), hlt⟩, true) ∈ F :=
      mem_F_all_of_mem (S := F_suffUStep n w) (by simp [F_list])
        (Finset.mem_image.mpr
          ⟨(i, ⟨2 ^ (w + 1) - 1 - (d + 1), hlt⟩), by simp [hlt1], by simp [hlt1]⟩)
    rw [heq] at hC
    exact up_imp2 (x := (vSuffU i ⟨2 ^ (w + 1) - 1 - d, by have := Nat.two_pow_pos (w + 1); omega⟩, true))
      (y := (vUnsup i ⟨2 ^ (w + 1) - 1 - (d + 1), hlt⟩, true)) hC hprev hcur

theorem up_suffU_of_ge {n w : ℕ} (hn : 0 < n) (ρ : Var n w → Option Bool) (i : Fin n) (p : Pat w) :
    let F : Set (Clause (TotVar n w)) := ↑(F_all n w hn)
    let A : Set (Literal (TotVar n w)) := {l | ∃ v, l.1 = Sum.inl v ∧ ρ v = some l.2}
    (∀ q : Pat w, p.val ≤ q.val → UPForces F A (vUnsup i q, true)) →
    UPForces F A (vSuffU i p, true) := by
  intro F A hall
  have hd : 2 ^ (w + 1) - 1 - p.val < 2 ^ (w + 1) := by have := p.isLt; omega
  have heq : (⟨2 ^ (w + 1) - 1 - (2 ^ (w + 1) - 1 - p.val), by have := Nat.two_pow_pos (w + 1); omega⟩ : Pat w) = p :=
    Fin.ext (by simp only [Fin.val_mk]; have := p.isLt; omega)
  have h := up_suffU_of_forall hn ρ i (2 ^ (w + 1) - 1 - p.val) hd (fun q hq => by
    apply hall q; have := p.isLt; omega)
  rw [heq] at h
  exact h

end PEqualNP.Outside.L_pcx_226_aux

open PEqualNP.ProofComplexity PEqualNP.Search PEqualNP.Outside.L_pcx_226_aux in
theorem PEqualNP.Outside.L_pcx_226 : (∀ (n w : ℕ) (hn : 0 < n),
  let V := Sum (Fin n) (Fin n × (Fin (w + 1) → Bool))
  let accepts := fun (a : V → Bool) =>
    ∀ i : Fin n, a (Sum.inr (i, fun j : Fin (w + 1) =>
      a (Sum.inl ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩))) = true
  ∃ (m : ℕ) (F : Finset (PEqualNP.ProofComplexity.Clause (Sum V (Fin m)))),
    m + (∑ D ∈ F, D.card) ≤ 128 * (n + 1) * 4 ^ w ∧
    (∀ D ∈ F, D.card ≤ 3) ∧
    (∀ a : V → Bool, accepts a ↔ ∃ aux : Fin m → Bool,
      PEqualNP.ProofComplexity.Satisfies (Sum.elim a aux) (↑F : Set _)) ∧
    ∀ ρ : V → Option Bool,
      let assumptions : Set (PEqualNP.ProofComplexity.Literal (Sum V (Fin m))) :=
        {l | ∃ v : V, l.1 = Sum.inl v ∧ ρ v = some l.2}
      let completion := fun (a : V → Bool) =>
        accepts a ∧ ∀ (v : V) (b : Bool), ρ v = some b → a v = b
      ((¬ ∃ a : V → Bool, completion a) ↔
        ∃ D ∈ F, ∀ l ∈ D, PEqualNP.Search.UPForces (↑F : Set _) assumptions
          (PEqualNP.Search.negLit l)) ∧
      ((∃ a : V → Bool, completion a) → ∀ (v : V) (b : Bool),
        (∀ a : V → Bool, completion a → a v = b) ↔
          PEqualNP.Search.UPForces (↑F : Set _) assumptions (Sum.inl v, b))) := by
  classical
  intro n w hn
  refine ⟨mCard n w, F_all n w hn, size_bound_F_all n w hn, card_le_three_F_all n w hn, ?_, ?_⟩
  · intro a
    constructor
    · intro hacc
      exact ⟨evalAux a, evalAux_satisfies hn a hacc⟩
    · rintro ⟨aux, hsat⟩
      by_contra hnotacc
      let ρ : Var n w → Option Bool := fun v => some (a v)
      let A : Set (Literal (TotVar n w)) := {l | ∃ v, l.1 = Sum.inl v ∧ ρ v = some l.2}
      have hA : ∀ l ∈ A, (Sum.elim a aux) l.1 = l.2 := by
        rintro l ⟨v, hl1, hl2⟩
        simp only [ρ, Option.some.injEq] at hl2
        rw [hl1, Sum.elim_inl, hl2]
      have hallU : ∀ p : Pat w, UPForces (↑(F_all n w hn) : Set _) A (vUnsup ⟨0, hn⟩ p, true) := by
        intro p
        by_contra hnp
        rcases up_unsup_complete hn ρ ⟨0, hn⟩ p hnp with ⟨a', ha'acc, ha'ρ, _⟩
        have haeq : a' = a := by
          funext v
          exact ha'ρ v (a v) rfl
        rw [haeq] at ha'acc
        exact hnotacc ha'acc
      have hpref := up_prefU_of_forall hn ρ ⟨0, hn⟩ (patLast w).val (patLast w).isLt
        (fun p _ => hallU p)
      have hconf : cl1 (vPrefU ⟨0, hn⟩ (patLast w), false) ∈ (↑(F_all n w hn) : Set _) :=
        mem_F_all_of_mem (S := F_conflict n w hn) (by simp [F_list]) (by simp [F_conflict])
      have hfalse : (Sum.elim a aux) (vPrefU ⟨0, hn⟩ (patLast w)) = false := by
        rcases hsat _ hconf with ⟨l, hl, hval⟩
        simp only [cl1, Finset.mem_singleton] at hl
        rw [hl] at hval
        exact hval
      have htrue : (Sum.elim a aux) (vPrefU ⟨0, hn⟩ (patLast w)) = true :=
        up_sound hsat hA hpref
      rw [hfalse] at htrue
      exact Bool.noConfusion htrue
  · intro ρ
    let A : Set (Literal (TotVar n w)) := {l | ∃ v, l.1 = Sum.inl v ∧ ρ v = some l.2}
    constructor
    · constructor
      · intro hno
        have hallU : ∀ p : Pat w, UPForces (↑(F_all n w hn) : Set _) A (vUnsup ⟨0, hn⟩ p, true) := by
          intro p
          by_contra hnp
          rcases up_unsup_complete hn ρ ⟨0, hn⟩ p hnp with ⟨a, hacc, hρ, _⟩
          exact hno ⟨a, hacc, hρ⟩
        have hpref := up_prefU_of_forall hn ρ ⟨0, hn⟩ (patLast w).val (patLast w).isLt
          (fun p _ => hallU p)
        refine ⟨cl1 (vPrefU ⟨0, hn⟩ (patLast w), false), ?_, ?_⟩
        · exact Finset.mem_coe.mp (mem_F_all_of_mem (S := F_conflict n w hn) (by simp [F_list]) (by simp [F_conflict]))
        · intro l hl
          simp only [cl1, Finset.mem_singleton] at hl
          rw [hl]
          simpa [negLit] using hpref
      · rintro ⟨D, hDF, hall⟩ ⟨a, hacc, hρ⟩
        have hsat := evalAux_satisfies hn a hacc
        have hA : ∀ l ∈ A, (Sum.elim a (evalAux a)) l.1 = l.2 := by
          rintro l ⟨v, hl1, hl2⟩
          rw [hl1, Sum.elim_inl]
          exact hρ v l.2 hl2
        rcases hsat D hDF with ⟨l, hlD, hval⟩
        have hneg := up_sound hsat hA (hall l hlD)
        simp only [negLit] at hneg
        rw [hval] at hneg
        cases l.2 <;> simp at hneg
    · intro ⟨a0, ha0acc, ha0ρ⟩ v b
      constructor
      · intro hforced
        cases v with
        | inl i =>
          cases b with
          | true =>
            have hallU : ∀ p : Pat w, p.val ≤ (patMidLo w).val →
                UPForces (↑(F_all n w hn) : Set _) A (vUnsup i p, true) := by
              intro p hp
              by_contra hnp
              rcases up_unsup_complete hn ρ i p hnp with ⟨a, hacc, hρ, hwin⟩
              have ht := hforced a ⟨hacc, hρ⟩
              have h0 : a (Sum.inl i) = patHead p := by
                have hzero := congrFun hwin 0
                have hidx : (⟨i.val % n, Nat.mod_lt _ hn⟩ : Fin n) = i :=
                  Fin.ext (Nat.mod_eq_of_lt i.isLt)
                simpa [patFun_zero, Fin.val_zero, hidx] using hzero
              have hf : patHead p = false := by
                simp only [patHead, decide_eq_false_iff_not, not_le]
                simp only [patMidLo] at hp
                have := Nat.two_pow_pos w; omega
              rw [h0, hf] at ht
              exact Bool.noConfusion ht
            have hpref := up_prefU_of_forall hn ρ i (patMidLo w).val (patMidLo w).isLt hallU
            have hC : cl2 (vPrefU i (patMidLo w), false) (vWord i, true) ∈ (↑(F_all n w hn) : Set _) :=
              mem_F_all_of_mem (S := F_wordTrue n w) (by simp [F_list])
                (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
            exact up_imp1 (x := (vPrefU i (patMidLo w), true)) hC hpref
          | false =>
            have hallU : ∀ p : Pat w, (patMidHi w).val ≤ p.val →
                UPForces (↑(F_all n w hn) : Set _) A (vUnsup i p, true) := by
              intro p hp
              by_contra hnp
              rcases up_unsup_complete hn ρ i p hnp with ⟨a, hacc, hρ, hwin⟩
              have hf := hforced a ⟨hacc, hρ⟩
              have h0 : a (Sum.inl i) = patHead p := by
                have hzero := congrFun hwin 0
                have hidx : (⟨i.val % n, Nat.mod_lt _ hn⟩ : Fin n) = i :=
                  Fin.ext (Nat.mod_eq_of_lt i.isLt)
                simpa [patFun_zero, Fin.val_zero, hidx] using hzero
              have ht : patHead p = true := by
                simp only [patHead, decide_eq_true_eq]
                simpa [patMidHi] using hp
              rw [h0, ht] at hf
              exact Bool.noConfusion hf
            have hsuff := up_suffU_of_ge hn ρ i (patMidHi w) hallU
            have hC : cl2 (vSuffU i (patMidHi w), false) (vWord i, false) ∈ (↑(F_all n w hn) : Set _) :=
              mem_F_all_of_mem (S := F_wordFalse n w) (by simp [F_list])
                (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
            exact up_imp1 (x := (vSuffU i (patMidHi w), true)) hC hsuff
        | inr ip =>
          rcases ip with ⟨i, f⟩
          let p : Pat w := patOfFun f
          have hfEq : patFun p = f := patFun_patOfFun f
          cases b with
          | false =>
            cases hρf : ρ (Sum.inr (i, f)) with
            | some c =>
              have hc : c = false := by
                have h1 := ha0ρ (Sum.inr (i, f)) c hρf
                have h2 := hforced a0 ⟨ha0acc, ha0ρ⟩
                rw [← h1, h2]
              subst hc
              exact UPForces.hyp ⟨Sum.inr (i, f), rfl, hρf⟩
            | none =>
              exfalso
              let a1 : Var n w → Bool := fun u =>
                if u = Sum.inr (i, f) then true else a0 u
              have ha1acc : ∀ k : Fin n, a1 (Sum.inr (k, fun j : Fin (w + 1) =>
                  a1 (Sum.inl ⟨(k.val + j.val) % n, Nat.mod_lt _ hn⟩))) = true := by
                intro k
                have hw : (fun j : Fin (w + 1) => a1 (Sum.inl ⟨(k.val + j.val) % n, Nat.mod_lt _ hn⟩)) =
                    (fun j : Fin (w + 1) => a0 (Sum.inl ⟨(k.val + j.val) % n, Nat.mod_lt _ hn⟩)) := by
                  funext j; simp [a1]
                rw [hw]
                simp only [a1]
                split_ifs
                · rfl
                · exact ha0acc k
              have ha1ρ : ∀ u c, ρ u = some c → a1 u = c := by
                intro u c huc
                simp only [a1]
                split_ifs with heq
                · subst heq; rw [hρf] at huc; cases huc
                · exact ha0ρ u c huc
              have hval := hforced a1 ⟨ha1acc, ha1ρ⟩
              simp [a1] at hval
          | true =>
            cases hρf : ρ (Sum.inr (i, f)) with
            | some c =>
              have hc : c = true := by
                have h1 := ha0ρ (Sum.inr (i, f)) c hρf
                have h2 := hforced a0 ⟨ha0acc, ha0ρ⟩
                rw [← h1, h2]
              subst hc
              exact UPForces.hyp ⟨Sum.inr (i, f), rfl, hρf⟩
            | none =>
              have hother : ∀ q : Pat w, q ≠ p →
                  UPForces (↑(F_all n w hn) : Set _) A (vUnsup i q, true) := by
                intro q hqp
                by_contra hnq
                rcases up_unsup_complete hn ρ i q hnq with ⟨a1, ha1acc, ha1ρ, hwin⟩
                let a2 : Var n w → Bool := fun u =>
                  if u = Sum.inr (i, f) then false else a1 u
                have ha2acc : ∀ k : Fin n, a2 (Sum.inr (k, fun j : Fin (w + 1) =>
                    a2 (Sum.inl ⟨(k.val + j.val) % n, Nat.mod_lt _ hn⟩))) = true := by
                  intro k
                  have hw : (fun j : Fin (w + 1) => a2 (Sum.inl ⟨(k.val + j.val) % n, Nat.mod_lt _ hn⟩)) =
                      (fun j : Fin (w + 1) => a1 (Sum.inl ⟨(k.val + j.val) % n, Nat.mod_lt _ hn⟩)) := by
                    funext j; simp [a2]
                  rw [hw]
                  simp only [a2]
                  split_ifs with heq
                  · exfalso
                    have hk : k = i := by
                      have := Sum.inr.inj heq
                      exact congrArg Prod.fst this
                    subst hk
                    have hfe : (fun j : Fin (w + 1) => a1 (Sum.inl ⟨(k.val + j.val) % n, Nat.mod_lt _ hn⟩)) = f := by
                      have := Sum.inr.inj heq
                      exact congrArg Prod.snd this
                    rw [hwin, ← hfEq] at hfe
                    have : q = p := by
                      rw [← patOfFun_patFun q, ← patOfFun_patFun p, hfe]
                    exact hqp this
                  · exact ha1acc k
                have ha2ρ : ∀ u c, ρ u = some c → a2 u = c := by
                  intro u c huc
                  simp only [a2]
                  split_ifs with heq
                  · subst heq; rw [hρf] at huc; cases huc
                  · exact ha1ρ u c huc
                have hval := hforced a2 ⟨ha2acc, ha2ρ⟩
                simp [a2] at hval
              have hCmem : ∀ C, C ∈ F_tabForce n w → C ∈ (↑(F_all n w hn) : Set _) := by
                intro C hC
                exact mem_F_all_of_mem (S := F_tabForce n w) (by simp [F_list]) hC
              have htabEq : (Sum.inl (Sum.inr (i, f)), true) = (vTab i p, true) := by
                simp [vTab, hfEq]
              rw [htabEq]
              by_cases h0 : p.val = 0
              · have h1lt : 1 < 2 ^ (w + 1) := by
                  have hp : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ, Nat.mul_comm]
                  have := Nat.two_pow_pos w; omega
                have hsuff := up_suffU_of_ge hn ρ i ⟨1, h1lt⟩
                  (fun q hq => hother q (fun heq => by
                    rw [heq] at hq
                    change 1 ≤ p.val at hq
                    omega))
                have hC : cl2 (vSuffU i ⟨1, h1lt⟩, false)
                    (vTab i p, true) ∈ (↑(F_all n w hn) : Set _) := by
                  apply hCmem
                  exact Finset.mem_image.mpr ⟨(i, p), Finset.mem_univ _, by simp [h0]⟩
                exact up_imp1 (x := (vSuffU i ⟨1, h1lt⟩, true)) hC hsuff
              · by_cases hlast : p.val + 1 = 2 ^ (w + 1)
                · have hpref := up_prefU_of_forall hn ρ i (p.val - 1) (by omega)
                    (fun q hq => hother q (fun heq => by rw [heq] at hq; omega))
                  have hC : cl2 (vPrefU i ⟨p.val - 1, by omega⟩, false)
                      (vTab i p, true) ∈ (↑(F_all n w hn) : Set _) := by
                    apply hCmem
                    exact Finset.mem_image.mpr ⟨(i, p), Finset.mem_univ _, by simp [h0, hlast]⟩
                  exact up_imp1 (x := (vPrefU i ⟨p.val - 1, by omega⟩, true)) hC hpref
                · have hpref := up_prefU_of_forall hn ρ i (p.val - 1) (by omega)
                    (fun q hq => hother q (fun heq => by rw [heq] at hq; omega))
                  have hsuff := up_suffU_of_ge hn ρ i ⟨p.val + 1, by have := p.isLt; omega⟩
                    (fun q hq => hother q (fun heq => by
                      rw [heq] at hq
                      change p.val + 1 ≤ p.val at hq
                      omega))
                  have hC : cl3 (vPrefU i ⟨p.val - 1, by omega⟩, false)
                      (vSuffU i ⟨p.val + 1, by have := p.isLt; omega⟩, false)
                      (vTab i p, true) ∈ (↑(F_all n w hn) : Set _) := by
                    apply hCmem
                    exact Finset.mem_image.mpr ⟨(i, p), Finset.mem_univ _, by simp [h0, hlast]⟩
                  exact up_imp2 (x := (vPrefU i ⟨p.val - 1, by omega⟩, true))
                    (y := (vSuffU i ⟨p.val + 1, by have := p.isLt; omega⟩, true)) hC hpref hsuff
      · intro hup a ⟨hacc, hρ⟩
        have hsat := evalAux_satisfies hn a hacc
        have hA : ∀ l ∈ A, (Sum.elim a (evalAux a)) l.1 = l.2 := by
          rintro l ⟨u, hl1, hl2⟩
          rw [hl1, Sum.elim_inl]
          exact hρ u l.2 hl2
        exact up_sound hsat hA hup
