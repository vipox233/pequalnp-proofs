import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29410.Core

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def mask256 : Nat := 2 ^ 256 - 1

def negD (d w : Nat) : Nat := (w ^^^ mask256) &&& d
def andD (d a b : Nat) : Nat := (a &&& b) &&& d
def orD (d a b : Nat) : Nat := (a ||| b) &&& d
def binD (d : Nat) (isOr : Bool) (a b : Nat) : Nat := if isOr then orD d a b else andD d a b

def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

def RunD (d y : Nat) (t : ℕ) (ws : List Nat) : Prop :=
  ∀ P : ℕ → List Nat → Prop, P 0 [y] →
    (∀ {s xs zs}, List.Perm xs zs → P s xs → P s zs) →
    (∀ {s a r} (save : Bool),
      negD d a ≠ 0 → negD d a ≠ d → negD d a ∉ (a :: r) →
      P s (negD d a :: kept save a r) → P (s + 1) (a :: r)) →
    (∀ {s a b r} (c ka kb : Bool),
      (if c then andD d a b else orD d a b) ≠ 0 →
      (if c then andD d a b else orD d a b) ≠ d →
      (if c then andD d a b else orD d a b) ∉ (a :: b :: r) →
      P s ((if c then andD d a b else orD d a b) :: kept ka a (kept kb b r)) →
      P (s + 1) (a :: b :: r)) → P t ws

section
variable {d y : Nat}

theorem Run.done : RunD d y 0 [y] := fun _ dn _ _ _ => dn
theorem Run.perm {s xs zs} (p : List.Perm xs zs) (h : RunD d y s xs) :
    RunD d y s zs := fun P dn q u b => q p (h P dn q u b)
theorem Run.one {s a r} (save : Bool)
    (h0 : negD d a ≠ 0) (hd : negD d a ≠ d) (hm : negD d a ∉ (a :: r))
    (h : RunD d y s (negD d a :: kept save a r)) :
    RunD d y (s + 1) (a :: r) := fun P dn q u b => u save h0 hd hm (h P dn q u b)
theorem Run.two {s a b r} (c ka kb : Bool)
    (h0 : (if c then andD d a b else orD d a b) ≠ 0)
    (hd : (if c then andD d a b else orD d a b) ≠ d)
    (hm : (if c then andD d a b else orD d a b) ∉ (a :: b :: r))
    (h : RunD d y s ((if c then andD d a b else orD d a b) :: kept ka a (kept kb b r))) :
    RunD d y (s + 1) (a :: b :: r) := fun P dn q u v => v c ka kb h0 hd hm (h P dn q u v)

theorem Run.fold {P : ∀ t ws, RunD d y t ws → Prop}
    (done : P 0 [y] Run.done)
    (perm : ∀ {s xs zs} (hp : List.Perm xs zs) (h : RunD d y s xs),
      P s xs h → P s zs (Run.perm hp h))
    (one : ∀ {s a r} (save : Bool)
      (h0 : negD d a ≠ 0) (hd : negD d a ≠ d) (hm : negD d a ∉ (a :: r))
      (h : RunD d y s (negD d a :: kept save a r)),
      P _ _ h → P _ _ (Run.one save h0 hd hm h))
    (two : ∀ {s a b r} (c ka kb : Bool)
      (h0 : (if c then andD d a b else orD d a b) ≠ 0)
      (hd : (if c then andD d a b else orD d a b) ≠ d)
      (hm : (if c then andD d a b else orD d a b) ∉ (a :: b :: r))
      (h : RunD d y s ((if c then andD d a b else orD d a b) :: kept ka a (kept kb b r))),
      P _ _ h → P _ _ (Run.two c ka kb h0 hd hm h))
    {t ws} (h : RunD d y t ws) : P t ws h := by
  have hex := h (fun s xs => ∃ h' : RunD d y s xs, P s xs h')
    ⟨Run.done, done⟩
    (fun hp ⟨h', ih⟩ => ⟨Run.perm hp h', perm hp h' ih⟩)
    (fun k h0 hd hm ⟨h', ih⟩ => ⟨Run.one k h0 hd hm h', one k h0 hd hm h' ih⟩)
    (fun c a b h0 hd hm ⟨h', ih⟩ => ⟨Run.two c a b h0 hd hm h', two c a b h0 hd hm h' ih⟩)
  exact hex.elim fun _ hp => hp
end

theorem kept_map {α β : Type} (e : α → β) (b : Bool) (x : α) (xs : List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e) := by cases b <;> simp [kept]

theorem mem_kept {α : Type} (b : Bool) (x a : α) (xs : List α) :
    a ∈ kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs := by cases b <;> simp [kept]

theorem nodup_kept {α : Type} (b : Bool) (x : α) (xs : List α) (h : xs.Nodup) (hx : x ∉ xs) :
    (kept b x xs).Nodup := by
  cases b
  · simpa [kept] using h
  · simpa [kept] using And.intro hx h

theorem keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys) := by cases b <;> simpa [kept] using p

theorem run_len {d y s xs} (h : RunD d y s xs) :
    xs.length ≤ s + 1 := by
  induction h using Run.fold with
  | done => simp
  | perm hp _ ih => rwa [← hp.length_eq]
  | one save _ _ _ _ ih => cases save <;> simp_all [kept] <;> omega
  | two conj ka kb _ _ _ _ ih => cases ka <;> cases kb <;> simp_all [kept] <;> omega

theorem zero_done {d y t ws} (h : RunD d y t ws) :
    t = 0 → ws = [y] := by
  induction h using Run.fold with
  | done => simp
  | perm p _ ih => intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | one => simp
  | two => simp

def IsConst (d w : Nat) : Prop := (w &&& d) = 0 ∨ (w &&& d) = d
def isConstB (d w : Nat) : Bool := (w &&& d == 0) || (w &&& d == d)

theorem isConstB_iff (d w : Nat) : isConstB d w = true ↔ IsConst d w := by
  simp [isConstB, IsConst]

def Avail (d : Nat) (bank : List Nat) (w : Nat) : Prop :=
  IsConst d w ∨ ∃ v ∈ bank, (v &&& d) = (w &&& d)

def availB (d : Nat) (bank : List Nat) (w : Nat) : Bool :=
  let m := w &&& d
  m == 0 || m == d || bank.any (fun v => (v &&& d) == m)

theorem availB_iff (d : Nat) (bank : List Nat) (w : Nat) :
    availB d bank w = true ↔ Avail d bank w := by
  simp [availB, Avail, IsConst, or_assoc]

def NatReach (d : Nat) (roots : List Nat) : Nat → List Nat → Prop
  | 0, bank => bank = roots
  | p + 1, bank =>
    (∃ b a, bank = negD d a :: b ∧ NatReach d roots p b ∧ Avail d b a) ∨
    (∃ b a c op, bank = binD d op a c :: b ∧ NatReach d roots p b ∧ Avail d b a ∧ Avail d b c)

def Lower (d : Nat) (roots : List Nat) (T : Nat) (L : Nat) : Prop :=
  ∀ p bank, NatReach d roots p bank → Avail d bank T → L ≤ p

theorem mask256_bit (i : Nat) : mask256.testBit i = decide (i < 256) := by
  rw [mask256, Nat.testBit_two_pow_sub_one]

theorem negD_and_sub {d d1 : Nat} (hd : d &&& mask256 = d) (hsub : d &&& d1 = d) (a : Nat) :
    negD d1 a &&& d = negD d a := by
  apply Nat.eq_of_testBit_eq; intro i
  have h1 := congrArg (fun v => v.testBit i) hd
  have h2 := congrArg (fun v => v.testBit i) hsub
  simp only [negD, Nat.testBit_and, Nat.testBit_xor] at *
  cases hi : d.testBit i <;> simp_all

theorem andD_and_sub {d d1 : Nat} (hsub : d &&& d1 = d) (a b : Nat) :
    andD d1 a b &&& d = andD d a b := by
  apply Nat.eq_of_testBit_eq; intro i
  have h2 := congrArg (fun v => v.testBit i) hsub
  simp only [andD, Nat.testBit_and] at *
  cases hi : d.testBit i <;> simp_all

theorem orD_and_sub {d d1 : Nat} (hsub : d &&& d1 = d) (a b : Nat) :
    orD d1 a b &&& d = orD d a b := by
  apply Nat.eq_of_testBit_eq; intro i
  have h2 := congrArg (fun v => v.testBit i) hsub
  simp only [orD, Nat.testBit_and, Nat.testBit_or] at *
  cases hi : d.testBit i <;> simp_all

theorem negD_const {d : Nat} (hd : d &&& mask256 = d) {a : Nat} (hc : IsConst d a) :
    IsConst d (negD d a) := by
  rcases hc with h0 | h1
  · right; apply Nat.eq_of_testBit_eq; intro i
    have h0i := congrArg (fun v => v.testBit i) h0
    have hdi := congrArg (fun v => v.testBit i) hd
    simp only [negD, Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit] at *
    cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
  · left; apply Nat.eq_of_testBit_eq; intro i
    have h1i := congrArg (fun v => v.testBit i) h1
    have hdi := congrArg (fun v => v.testBit i) hd
    simp only [negD, Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit] at *
    cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all

theorem binD_const_left {d : Nat} {a b : Nat} (op : Bool) (hc : IsConst d a) :
    (binD d op a b &&& d = 0) ∨ (binD d op a b &&& d = d) ∨ (binD d op a b &&& d = b &&& d) := by
  rcases hc with h0 | h1
  · cases op
    · left; apply Nat.eq_of_testBit_eq; intro i
      have h0i := congrArg (fun v => v.testBit i) h0
      simp only [binD, andD, Nat.testBit_and, Nat.zero_testBit, ite_false] at *
      cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
    · right; right; apply Nat.eq_of_testBit_eq; intro i
      have h0i := congrArg (fun v => v.testBit i) h0
      simp only [binD, orD, Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit, ite_true] at *
      cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
  · cases op
    · right; right; apply Nat.eq_of_testBit_eq; intro i
      have h1i := congrArg (fun v => v.testBit i) h1
      simp only [binD, andD, Nat.testBit_and, ite_false] at *
      cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
    · right; left; apply Nat.eq_of_testBit_eq; intro i
      have h1i := congrArg (fun v => v.testBit i) h1
      simp only [binD, orD, Nat.testBit_and, Nat.testBit_or, ite_true] at *
      cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all

theorem binD_comm (d : Nat) (op : Bool) (a b : Nat) : binD d op a b = binD d op b a := by
  cases op <;> simp [binD, andD, orD, Nat.and_comm, Nat.or_comm]

theorem avail_cons {d : Nat} {bank : List Nat} (z w : Nat) (h : Avail d bank w) :
    Avail d (z :: bank) w := by
  rcases h with hc | ⟨v, hv, he⟩
  · exact Or.inl hc
  · exact Or.inr ⟨v, List.mem_cons_of_mem _ hv, he⟩

theorem avail_of_eq {d : Nat} {bank : List Nat} {v w : Nat}
    (he : v &&& d = w &&& d) (h : Avail d bank v) : Avail d bank w := by
  rcases h with (h0 | h1) | ⟨u, hu, hue⟩
  · exact Or.inl (Or.inl (he.symm.trans h0))
  · exact Or.inl (Or.inr (he.symm.trans h1))
  · exact Or.inr ⟨u, hu, hue.trans he⟩

theorem countP_kept_ge {α : Type} (p : α → Bool) (b : Bool) (a : α) (xs : List α) :
    xs.countP p ≤ (kept b a xs).countP p := by
  cases b <;> simp [kept, List.countP_cons] <;> split <;> omega

theorem contraction {d d1 T : Nat} (hd : d &&& mask256 = d) (hsub : d &&& d1 = d)
    (hnc : ¬ IsConst d T) {s ws} (h : RunD d1 T s ws) {roots p bank}
    (hp : NatReach d roots p bank) (hs : ∀ w ∈ ws, Avail d bank w) :
    ∃ q next, NatReach d roots q next ∧ Avail d next T ∧
      q + ws.countP (isConstB d) ≤ p + s := by
  induction h using Run.fold generalizing p bank with
  | done =>
    have hfalse : isConstB d T = false := by
      cases hc : isConstB d T with
      | false => rfl
      | true => exact absurd ((isConstB_iff d T).1 hc) hnc
    exact ⟨p, bank, hp, hs T (by simp), by simp [hfalse]⟩
  | perm eq _ ih =>
    obtain ⟨q, next, hq, ht, hle⟩ := ih hp (fun w hw => hs w (eq.mem_iff.1 hw))
    rw [eq.countP_eq] at hle
    exact ⟨q, next, hq, ht, hle⟩
  | @one s a r save _ _ _ _ ih =>
    have ha := hs a List.mem_cons_self
    by_cases hca : IsConst d a
    · have hc_neg : IsConst d (negD d1 a) := by
        have e := negD_and_sub hd hsub a
        rcases negD_const hd hca with h0 | h1
        · exact Or.inl (e.trans (by simpa [negD, Nat.and_assoc, Nat.and_self] using h0))
        · exact Or.inr (e.trans (by simpa [negD, Nat.and_assoc, Nat.and_self] using h1))
      have hs' : ∀ w ∈ negD d1 a :: kept save a r, Avail d bank w := by
        intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact Or.inl hc_neg
        · exact hs w (by rw [mem_kept] at hw; rcases hw with ⟨_, rfl⟩ | hw <;> simp [hw])
      obtain ⟨q, next, hq, ht, hle⟩ := ih hp hs'
      have h1 : isConstB d (negD d1 a) = true := (isConstB_iff _ _).2 hc_neg
      have h2 : isConstB d a = true := (isConstB_iff _ _).2 hca
      have hk := countP_kept_ge (isConstB d) save a r
      simp only [List.countP_cons, h1, h2, ite_true] at hle ⊢
      exact ⟨q, next, hq, ht, by omega⟩
    · have hreach' : NatReach d roots (p + 1) (negD d a :: bank) := Or.inl ⟨bank, a, rfl, hp, ha⟩
      have hneg_av : Avail d (negD d a :: bank) (negD d1 a) :=
        Or.inr ⟨negD d a, List.mem_cons_self, by rw [negD_and_sub hd hsub a]; simp [negD, Nat.and_assoc, Nat.and_self]⟩
      have hs' : ∀ w ∈ negD d1 a :: kept save a r, Avail d (negD d a :: bank) w := by
        intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact hneg_av
        · exact avail_cons _ _ (hs w (by rw [mem_kept] at hw; rcases hw with ⟨_, rfl⟩ | hw <;> simp [hw]))
      obtain ⟨q, next, hq, ht, hle⟩ := ih hreach' hs'
      have h2 : isConstB d a = false := by
        cases h : isConstB d a with | false => rfl | true => exact absurd ((isConstB_iff _ _).1 h) hca
      have hk := countP_kept_ge (isConstB d) save a r
      simp only [List.countP_cons, h2, Bool.false_eq_true, ite_false] at hle ⊢
      exact ⟨q, next, hq, ht, by omega⟩
  | @two s a b r conj ka kb _ _ _ _ ih =>
    have ha := hs a List.mem_cons_self
    have hb := hs b (List.mem_cons_of_mem _ List.mem_cons_self)
    set z1 := if conj then andD d1 a b else orD d1 a b
    set z0 := binD d (!conj) a b
    have hz_eq : z1 &&& d = z0 &&& d := by
      cases conj
      · simp only [z1, z0, Bool.false_eq_true, ite_false, Bool.not_false, binD, ite_true]
        rw [orD_and_sub hsub]; simp [orD, Nat.and_assoc, Nat.and_self]
      · simp only [z1, z0, ite_true, Bool.not_true, Bool.false_eq_true, binD, ite_false]
        rw [andD_and_sub hsub]; simp [andD, Nat.and_assoc, Nat.and_self]
    by_cases hcab : IsConst d a ∨ IsConst d b
    · have hz_av : Avail d bank z1 := by
        apply avail_of_eq hz_eq.symm
        rcases hcab with hca | hcb
        · rcases binD_const_left (!conj) hca with h0 | h1 | he
          · exact Or.inl (Or.inl h0)
          · exact Or.inl (Or.inr h1)
          · exact avail_of_eq he.symm hb
        · dsimp only [z0]; rw [binD_comm]
          rcases binD_const_left (!conj) hcb with h0 | h1 | he
          · exact Or.inl (Or.inl h0)
          · exact Or.inl (Or.inr h1)
          · exact avail_of_eq he.symm ha
      have hs' : ∀ w ∈ z1 :: kept ka a (kept kb b r), Avail d bank w := by
        intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact hz_av
        · rw [mem_kept, mem_kept] at hw
          rcases hw with ⟨_, rfl⟩ | ⟨_, rfl⟩ | hw
          · exact ha
          · exact hb
          · exact hs w (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw))
      obtain ⟨q, next, hq, ht, hle⟩ := ih hp hs'
      have hkr : r.countP (isConstB d) ≤ (kept ka a (kept kb b r)).countP (isConstB d) :=
        le_trans (countP_kept_ge _ kb b r) (countP_kept_ge _ ka a _)
      have hcost : (if isConstB d a = true then 1 else 0) + (if isConstB d b = true then 1 else 0)
          ≤ 1 + (if isConstB d z1 = true then 1 else 0) := by
        rcases hcab with hca | hcb
        · have ha1 : isConstB d a = true := (isConstB_iff _ _).2 hca
          rcases binD_const_left (!conj) hca with h0 | h1 | he
          · have hz1 : isConstB d z1 = true := (isConstB_iff _ _).2 (Or.inl (hz_eq.trans h0))
            simp [ha1, hz1]; split <;> omega
          · have hz1 : isConstB d z1 = true := (isConstB_iff _ _).2 (Or.inr (hz_eq.trans h1))
            simp [ha1, hz1]; split <;> omega
          · have hzb : isConstB d z1 = isConstB d b := by
              simp only [isConstB, hz_eq.trans he]
            simp [ha1, hzb]
        · have hb1 : isConstB d b = true := (isConstB_iff _ _).2 hcb
          have hz_eq' : z1 &&& d = binD d (!conj) b a &&& d := by rw [hz_eq, binD_comm]
          rcases binD_const_left (!conj) hcb with h0 | h1 | he
          · have hz1 : isConstB d z1 = true := (isConstB_iff _ _).2 (Or.inl (hz_eq'.trans h0))
            simp [hb1, hz1]; split <;> omega
          · have hz1 : isConstB d z1 = true := (isConstB_iff _ _).2 (Or.inr (hz_eq'.trans h1))
            simp [hb1, hz1]; split <;> omega
          · have hza : isConstB d z1 = isConstB d a := by
              simp only [isConstB, hz_eq'.trans he]
            simp [hb1, hza]
      simp only [List.countP_cons] at hle ⊢
      exact ⟨q, next, hq, ht, by omega⟩
    · have hna : isConstB d a = false := by
        cases h : isConstB d a with | false => rfl | true => exact absurd (Or.inl ((isConstB_iff _ _).1 h)) hcab
      have hnb : isConstB d b = false := by
        cases h : isConstB d b with | false => rfl | true => exact absurd (Or.inr ((isConstB_iff _ _).1 h)) hcab
      have hreach' : NatReach d roots (p + 1) (z0 :: bank) := Or.inr ⟨bank, a, b, !conj, rfl, hp, ha, hb⟩
      have hz_av : Avail d (z0 :: bank) z1 := Or.inr ⟨z0, List.mem_cons_self, hz_eq.symm⟩
      have hs' : ∀ w ∈ z1 :: kept ka a (kept kb b r), Avail d (z0 :: bank) w := by
        intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact hz_av
        · rw [mem_kept, mem_kept] at hw
          rcases hw with ⟨_, rfl⟩ | ⟨_, rfl⟩ | hw
          · exact avail_cons _ _ ha
          · exact avail_cons _ _ hb
          · exact avail_cons _ _ (hs w (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw)))
      obtain ⟨q, next, hq, ht, hle⟩ := ih hreach' hs'
      have hkr : r.countP (isConstB d) ≤ (kept ka a (kept kb b r)).countP (isConstB d) :=
        le_trans (countP_kept_ge _ kb b r) (countP_kept_ge _ ka a _)
      simp only [List.countP_cons, hna, hnb, Bool.false_eq_true, ite_false] at hle ⊢
      exact ⟨q, next, hq, ht, by omega⟩

-- Backward extraction: NatReach d roots p bank + Avail d bank T -> RunD d (T &&& d) s ws!
theorem mask_idemp (d w : Nat) : (w &&& d) &&& d = w &&& d := by
  simp [Nat.and_assoc, Nat.and_self]

theorem negD_mask (d a : Nat) : negD d (a &&& d) = negD d a := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [negD, Nat.testBit_and, Nat.testBit_xor]
  cases d.testBit i <;> simp

theorem andD_mask (d a b : Nat) : andD d (a &&& d) (b &&& d) = andD d a b := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [andD, Nat.testBit_and]
  cases d.testBit i <;> simp

theorem orD_mask (d a b : Nat) : orD d (a &&& d) (b &&& d) = orD d a b := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [orD, Nat.testBit_and, Nat.testBit_or]
  cases d.testBit i <;> simp

theorem pull_one {d Y k ws} (hd : d &&& mask256 = d) (hnd : ws.Nodup)
    (hprop : ∀ w ∈ ws, w ≠ 0 ∧ w ≠ d) (h : RunD d Y k ws)
    {b : List Nat} {a : Nat} (ha : Avail d b a) (hsub : ∀ w ∈ ws, w ∈ negD d a :: b.map (· &&& d)) :
    ∃ k' ws', k' ≤ k + 1 ∧ ws'.Nodup ∧ (∀ w ∈ ws', w ≠ 0 ∧ w ≠ d) ∧
      (∀ w ∈ ws', w ∈ b.map (· &&& d)) ∧ RunD d Y k' ws' := by
  set z := negD d a
  by_cases hzm : z ∈ ws
  · by_cases hzb : z ∈ b.map (· &&& d)
    · exact ⟨k, ws, by omega, hnd, hprop, fun w hw => by
        rcases List.mem_cons.1 (hsub w hw) with rfl | hm
        · exact hzb
        · exact hm, h⟩
    · have hzp := hprop z hzm
      have ha_nc : ¬ IsConst d a := by
        intro hc
        rcases negD_const hd hc with h0 | h1
        · exact hzp.1 (by simpa [z, negD, Nat.and_assoc, Nat.and_self] using h0)
        · exact hzp.2 (by simpa [z, negD, Nat.and_assoc, Nat.and_self] using h1)
      obtain ⟨v, hv, hve⟩ := ha.resolve_left ha_nc
      set a' := a &&& d
      have ha'_mem : a' ∈ b.map (· &&& d) := List.mem_map.2 ⟨v, hv, hve⟩
      have ha'_prop : a' ≠ 0 ∧ a' ≠ d := ⟨fun e => ha_nc (Or.inl e), fun e => ha_nc (Or.inr e)⟩
      set rest := ws.erase z
      have hrest_nd : rest.Nodup := hnd.erase z
      have hrest_sub : ∀ w ∈ rest, w ∈ b.map (· &&& d) := by
        intro w hw
        have ⟨hne, hm⟩ := hnd.mem_erase_iff.1 hw
        rcases List.mem_cons.1 (hsub w hm) with rfl | hmb
        · exact absurd rfl hne
        · exact hmb
      have hrest_prop : ∀ w ∈ rest, w ≠ 0 ∧ w ≠ d := fun w hw => hprop w (List.mem_of_mem_erase hw)
      have hp1 : ws.Perm (z :: rest) := List.perm_cons_erase hzm
      have ez : negD d a' = z := negD_mask d a
      have h1 : RunD d Y k (negD d a' :: rest) := by
        rw [ez]; exact Run.perm hp1 h
      have hne0 : negD d a' ≠ 0 := ez.symm ▸ hzp.1
      have hned : negD d a' ≠ d := ez.symm ▸ hzp.2
      by_cases ham : a' ∈ rest
      · have hp2 : rest.Perm (a' :: rest.erase a') := List.perm_cons_erase ham
        have h2 : RunD d Y k (negD d a' :: kept true a' (rest.erase a')) :=
          Run.perm (hp2.cons _) h1
        have hnm : negD d a' ∉ (a' :: rest.erase a') := by
          rw [ez, List.mem_cons]; rintro (e | hm)
          · exact hzb (e ▸ ha'_mem)
          · exact hnd.not_mem_erase (List.mem_of_mem_erase hm)
        refine ⟨k + 1, rest, le_rfl, hrest_nd, hrest_prop, hrest_sub, ?_⟩
        exact Run.perm hp2.symm (Run.one true hne0 hned hnm h2)
      · have h2 : RunD d Y k (negD d a' :: kept false a' rest) := h1
        have hnm : negD d a' ∉ (a' :: rest) := by
          rw [ez, List.mem_cons]; rintro (e | hm)
          · exact hzb (e ▸ ha'_mem)
          · exact hnd.not_mem_erase hm
        refine ⟨k + 1, a' :: rest, le_rfl, List.nodup_cons.2 ⟨ham, hrest_nd⟩, ?_, ?_, Run.one false hne0 hned hnm h2⟩
        · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
          · exact ha'_prop
          · exact hrest_prop w hw
        · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
          · exact ha'_mem
          · exact hrest_sub w hw
  · exact ⟨k, ws, by omega, hnd, hprop, fun w hw => by
      rcases List.mem_cons.1 (hsub w hw) with rfl | hm
      · exact absurd hw hzm
      · exact hm, h⟩

theorem pull_two {d Y k ws} (hnd : ws.Nodup)
    (hprop : ∀ w ∈ ws, w ≠ 0 ∧ w ≠ d) (h : RunD d Y k ws)
    {b : List Nat} {a c : Nat} (op : Bool) (ha : Avail d b a) (hc : Avail d b c)
    (hsub : ∀ w ∈ ws, w ∈ binD d op a c :: b.map (· &&& d)) :
    ∃ k' ws', k' ≤ k + 1 ∧ ws'.Nodup ∧ (∀ w ∈ ws', w ≠ 0 ∧ w ≠ d) ∧
      (∀ w ∈ ws', w ∈ b.map (· &&& d)) ∧ RunD d Y k' ws' := by
  set z := binD d op a c
  have hz_mask : z &&& d = z := by cases op <;> simp [z, binD, andD, orD, Nat.and_assoc, Nat.and_self]
  by_cases hzm : z ∈ ws
  · by_cases hzb : z ∈ b.map (· &&& d)
    · exact ⟨k, ws, by omega, hnd, hprop, fun w hw => by
        rcases List.mem_cons.1 (hsub w hw) with rfl | hm
        · exact hzb
        · exact hm, h⟩
    · have hzp := hprop z hzm
      have ha_nc : ¬ IsConst d a := by
        intro hca
        rcases binD_const_left op hca with h0 | h1 | he
        · exact hzp.1 (hz_mask.symm.trans h0)
        · exact hzp.2 (hz_mask.symm.trans h1)
        · rcases hc with hcc | ⟨v, hv, hve⟩
          · rcases hcc with h0 | h1
            · exact hzp.1 (hz_mask.symm.trans (he.trans h0))
            · exact hzp.2 (hz_mask.symm.trans (he.trans h1))
          · exact hzb (List.mem_map.2 ⟨v, hv, hve.trans (he.symm.trans hz_mask)⟩)
      have hc_nc : ¬ IsConst d c := by
        intro hcc
        have hz' : z = binD d op c a := binD_comm d op a c
        rcases binD_const_left op hcc with h0 | h1 | he
        · exact hzp.1 (hz_mask.symm.trans (by rw [hz']; exact h0))
        · exact hzp.2 (hz_mask.symm.trans (by rw [hz']; exact h1))
        · rcases ha with hca | ⟨v, hv, hve⟩
          · exact absurd hca ha_nc
          · have he' : z &&& d = a &&& d := hz'.symm ▸ he
            exact hzb (List.mem_map.2 ⟨v, hv, hve.trans (he'.symm.trans hz_mask)⟩)
      obtain ⟨va, hva, hvae⟩ := ha.resolve_left ha_nc
      obtain ⟨vc, hvc, hvce⟩ := hc.resolve_left hc_nc
      set a' := a &&& d
      set c' := c &&& d
      have ha'_mem : a' ∈ b.map (· &&& d) := List.mem_map.2 ⟨va, hva, hvae⟩
      have hc'_mem : c' ∈ b.map (· &&& d) := List.mem_map.2 ⟨vc, hvc, hvce⟩
      have ha'_prop : a' ≠ 0 ∧ a' ≠ d := ⟨fun e => ha_nc (Or.inl e), fun e => ha_nc (Or.inr e)⟩
      have hc'_prop : c' ≠ 0 ∧ c' ≠ d := ⟨fun e => hc_nc (Or.inl e), fun e => hc_nc (Or.inr e)⟩
      have hne_ac : a' ≠ c' := by
        intro heq
        dsimp only [a', c'] at heq
        have hz_eq : z = a' := by
          cases op
          · simp only [z, binD, Bool.false_eq_true, ite_false]; rw [← andD_mask, ← heq]; simp [andD, a', Nat.and_assoc, Nat.and_self]
          · simp only [z, binD, ite_true]; rw [← orD_mask, ← heq]; simp [orD, a', Nat.and_assoc, Nat.and_self]
        exact hzb (hz_eq ▸ ha'_mem)
      set rest := ws.erase z
      have hrest_nd : rest.Nodup := hnd.erase z
      have hrest_sub : ∀ w ∈ rest, w ∈ b.map (· &&& d) := by
        intro w hw
        have ⟨hne, hm⟩ := hnd.mem_erase_iff.1 hw
        rcases List.mem_cons.1 (hsub w hm) with rfl | hmb
        · exact absurd rfl hne
        · exact hmb
      have hrest_prop : ∀ w ∈ rest, w ≠ 0 ∧ w ≠ d := fun w hw => hprop w (List.mem_of_mem_erase hw)
      have hp1 : ws.Perm (z :: rest) := List.perm_cons_erase hzm
      have ez : (if !op then andD d a' c' else orD d a' c') = z := by
        cases op
        · simp [z, binD, a', c', andD_mask]
        · simp [z, binD, a', c', orD_mask]
      have h1 : RunD d Y k ((if !op then andD d a' c' else orD d a' c') :: rest) := by
        rw [ez]; exact Run.perm hp1 h
      set ka := decide (a' ∈ rest)
      set kb := decide (c' ∈ rest)
      set tail := (rest.erase a').erase c'
      have htail_nd : tail.Nodup := (hrest_nd.erase a').erase c'
      have hna_tail : a' ∉ tail := by
        intro hm; exact hrest_nd.not_mem_erase (List.mem_of_mem_erase hm)
      have hnc_tail : c' ∉ tail := (hrest_nd.erase a').not_mem_erase
      have hna_mid : a' ∉ kept kb c' tail := by
        rw [mem_kept]; rintro (⟨_, h⟩ | h)
        · exact hne_ac h
        · exact hna_tail h
      have hrest_perm : rest.Perm (kept ka a' (kept kb c' tail)) := by
        refine (List.perm_ext_iff_of_nodup hrest_nd (nodup_kept ka a' _ (nodup_kept kb c' _ htail_nd hnc_tail) hna_mid)).2 ?_
        intro x
        rw [mem_kept, mem_kept, (hrest_nd.erase a').mem_erase_iff, hrest_nd.mem_erase_iff]
        by_cases hxa : x = a' <;> by_cases hxc : x = c' <;> by_cases hxr : x ∈ rest <;>
          simp_all [ka, kb]
      have h2 := Run.perm (hrest_perm.cons _) h1
      have hne0 : (if !op then andD d a' c' else orD d a' c') ≠ 0 := ez.symm ▸ hzp.1
      have hned : (if !op then andD d a' c' else orD d a' c') ≠ d := ez.symm ▸ hzp.2
      have hnm : (if !op then andD d a' c' else orD d a' c') ∉ (a' :: c' :: tail) := by
        rw [ez, List.mem_cons, List.mem_cons]; rintro (e | e | hm)
        · exact hzb (e ▸ ha'_mem)
        · exact hzb (e ▸ hc'_mem)
        · exact hnd.not_mem_erase (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
      have h3 : RunD d Y (k + 1) (a' :: c' :: tail) := Run.two (!op) ka kb hne0 hned hnm h2
      have hnd3 : (a' :: c' :: tail).Nodup :=
        List.nodup_cons.2 ⟨by simp [hne_ac, hna_tail], List.nodup_cons.2 ⟨hnc_tail, htail_nd⟩⟩
      refine ⟨k + 1, a' :: c' :: tail, le_rfl, hnd3, ?_, ?_, h3⟩
      · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact ha'_prop
        · rcases List.mem_cons.1 hw with rfl | hw
          · exact hc'_prop
          · exact hrest_prop w (List.mem_of_mem_erase (List.mem_of_mem_erase hw))
      · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact ha'_mem
        · rcases List.mem_cons.1 hw with rfl | hw
          · exact hc'_mem
          · exact hrest_sub w (List.mem_of_mem_erase (List.mem_of_mem_erase hw))
  · exact ⟨k, ws, by omega, hnd, hprop, fun w hw => by
      rcases List.mem_cons.1 (hsub w hw) with rfl | hm
      · exact absurd hw hzm
      · exact hm, h⟩

theorem reach_to_run_aux {d : Nat} {roots : List Nat} {p bank} (hd : d &&& mask256 = d)
    (hr : NatReach d roots p bank) :
    ∀ {Y k ws}, ws.Nodup → (∀ w ∈ ws, w ≠ 0 ∧ w ≠ d) →
      (∀ w ∈ ws, w ∈ bank.map (· &&& d)) → RunD d Y k ws →
      ∃ k' ws', k' ≤ p + k ∧ ws'.Nodup ∧ (∀ w ∈ ws', w ≠ 0 ∧ w ≠ d) ∧
        (∀ w ∈ ws', w ∈ roots.map (· &&& d)) ∧ RunD d Y k' ws' := by
  induction p generalizing bank with
  | zero =>
    intro Y k ws hnd hprop hsub hrun
    subst hr
    exact ⟨k, ws, by omega, hnd, hprop, hsub, hrun⟩
  | succ p ih =>
    intro Y k ws hnd hprop hsub hrun
    rcases hr with ⟨b, a, rfl, hrb, ha⟩ | ⟨b, a, c, op, rfl, hrb, ha, hc⟩
    · have hsub' : ∀ w ∈ ws, w ∈ negD d a :: b.map (· &&& d) := by
        intro w hw; have := hsub w hw; simp only [List.map_cons, negD, Nat.and_assoc, Nat.and_self] at this; exact this
      obtain ⟨k1, ws1, hk1, hnd1, hprop1, hsub1, hrun1⟩ := pull_one hd hnd hprop hrun ha hsub'
      obtain ⟨k2, ws2, hk2, hnd2, hprop2, hsub2, hrun2⟩ := ih hrb hnd1 hprop1 hsub1 hrun1
      exact ⟨k2, ws2, by omega, hnd2, hprop2, hsub2, hrun2⟩
    · have hsub' : ∀ w ∈ ws, w ∈ binD d op a c :: b.map (· &&& d) := by
        intro w hw; have := hsub w hw
        have ez : binD d op a c &&& d = binD d op a c := by cases op <;> simp [binD, andD, orD, Nat.and_assoc, Nat.and_self]
        simpa [List.map_cons, ez] using this
      obtain ⟨k1, ws1, hk1, hnd1, hprop1, hsub1, hrun1⟩ := pull_two hnd hprop hrun op ha hc hsub'
      obtain ⟨k2, ws2, hk2, hnd2, hprop2, hsub2, hrun2⟩ := ih hrb hnd1 hprop1 hsub1 hrun1
      exact ⟨k2, ws2, by omega, hnd2, hprop2, hsub2, hrun2⟩

theorem reach_to_run {d : Nat} {roots : List Nat} {T : Nat} {p bank} (hd : d &&& mask256 = d)
    (hnc : ¬ IsConst d T) (hr : NatReach d roots p bank) (ha : Avail d bank T) :
    ∃ s ws, s ≤ p ∧ ws.Nodup ∧ (∀ w ∈ ws, w ∈ roots.map (· &&& d)) ∧ RunD d (T &&& d) s ws := by
  obtain ⟨v, hv, hve⟩ := ha.resolve_left hnc
  have hprop : ∀ w ∈ [T &&& d], w ≠ 0 ∧ w ≠ d := by
    intro w hw; rw [List.mem_singleton.1 hw]
    exact ⟨fun e => hnc (Or.inl e), fun e => hnc (Or.inr e)⟩
  have hsub : ∀ w ∈ [T &&& d], w ∈ bank.map (· &&& d) := by
    intro w hw; rw [List.mem_singleton.1 hw]; exact List.mem_map.2 ⟨v, hv, hve⟩
  obtain ⟨s, ws, hs, hnd, _, hsub', hrun⟩ := reach_to_run_aux hd hr (List.nodup_singleton _) hprop hsub Run.done
  exact ⟨s, ws, by omega, hnd, hsub', hrun⟩

-- Essential variable lemma + lower_slice + lower_base + lower_iso!
theorem runD_bits {d y s ws} (hd : d &&& mask256 = d) (h : RunD d y s ws) (i j : Nat)
    (hi : d.testBit i = true) (hj : d.testBit j = true)
    (hw : ∀ w ∈ ws, w.testBit i = w.testBit j) : y.testBit i = y.testBit j := by
  have hmi : mask256.testBit i = true := by
    have := congrArg (fun v => v.testBit i) hd; simp [Nat.testBit_and, hi] at this; exact this
  have hmj : mask256.testBit j = true := by
    have := congrArg (fun v => v.testBit j) hd; simp [Nat.testBit_and, hj] at this; exact this
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | one save _ _ _ _ ih =>
    apply ih; have ha := hw _ List.mem_cons_self
    intro w hm; cases save <;> simp only [kept, Bool.false_eq_true, ite_false, ite_true, List.mem_cons] at hm
    · rcases hm with rfl | hr
      · simp [negD, ha, hi, hj, hmi, hmj]
      · exact hw _ (by simp [hr])
    · rcases hm with rfl | rfl | hr
      · simp [negD, ha, hi, hj, hmi, hmj]
      · exact ha
      · exact hw _ (by simp [hr])
  | two conj ka kb _ _ _ _ ih =>
    apply ih; have ha := hw _ List.mem_cons_self; have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hm; cases conj <;> cases ka <;> cases kb <;>
      simp only [kept, Bool.false_eq_true, ite_false, ite_true, List.mem_cons] at hm <;>
      rcases hm with rfl | hr <;>
      first | simp [andD, orD, ha, hb, hi, hj] | exact hw _ (by simp only [List.mem_cons]; tauto)

theorem runD_bits_le {d y s ws} (h : RunD d y s ws) (hl : ws.length = s + 1) (i j : Nat)
    (hi : d.testBit i = true) (hj : d.testBit j = true)
    (hw : ∀ w ∈ ws, w.testBit i ≤ w.testBit j) : y.testBit i ≤ y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (hp.length_eq.trans hl) (fun w h => hw w (hp.mem_iff.1 h))
  | one save _ _ _ h _ => have hh := run_len h; cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb _ _ _ h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    apply ih (by simp [kept]; omega)
    have ha := hw _ List.mem_cons_self; have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hm; simp only [kept, Bool.false_eq_true, ite_false, List.mem_cons] at hm
    rcases hm with rfl | hr
    · cases conj <;> simp only [andD, orD, ite_true, Bool.false_eq_true, ite_false, Nat.testBit_and, Nat.testBit_or, hi, hj, Bool.and_true] <;> grind
    · exact hw _ (by simp [hr])

theorem lower_base {d : Nat} {roots : List Nat} {T : Nat} (h : availB d roots T = false) :
    Lower d roots T 1 := by
  intro p bank hr ha
  cases p with
  | zero =>
    dsimp only [NatReach] at hr; rw [hr] at ha
    have ht := (availB_iff d roots T).2 ha
    rw [h] at ht; contradiction
  | succ p => omega

-- moveBits & lower_iso!
def moveBits (tag d w : Nat) : Nat :=
  ((w &&& tag) <<< d) ||| ((w >>> d) &&& tag) |||
    (w ^^^ ((w &&& tag) ||| (w &&& (tag <<< d))))

theorem moved (tag d i w : Nat) (h : (tag &&& (tag <<< d)) = 0) :
    (moveBits tag d w).testBit i =
      (if tag.testBit i then w.testBit (d + i)
       else if (tag <<< d).testBit i then w.testBit (i - d) else w.testBit i) := by
  have ht := congrArg (fun v : Nat => v.testBit i) h
  simp only [Nat.testBit_and, Nat.zero_testBit] at ht
  simp only [moveBits, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_and,
    Nat.testBit_shiftRight, Nat.testBit_xor] at *
  by_cases hi : d ≤ i <;> simp [hi] at * <;> grind

theorem move_hom (tag d : Nat) (h : (tag &&& (tag <<< d)) = 0) (a b : Nat) :
    moveBits tag d (a &&& b) = (moveBits tag d a &&& moveBits tag d b) ∧
    moveBits tag d (a ||| b) = (moveBits tag d a ||| moveBits tag d b) ∧
    moveBits tag d (a ^^^ b) = (moveBits tag d a ^^^ moveBits tag d b) := by
  refine ⟨?_, ?_, ?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, moved tag d i _ h] <;>
    split_ifs <;> simp

theorem move_zero (tag d : Nat) (h : (tag &&& (tag <<< d)) = 0) : moveBits tag d 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro i; rw [moved tag d i 0 h]; split_ifs <;> simp

def applyMoves (ms : List (Nat × Nat)) (w : Nat) : Nat :=
  ms.foldl (fun acc p => moveBits p.1 p.2 acc) w

def moveOK256 (p : Nat × Nat) : Bool :=
  (p.1 &&& (p.1 <<< p.2) == 0) && (moveBits p.1 p.2 mask256 == mask256)

theorem applyMoves_hom (ms : List (Nat × Nat)) (hok : ms.all moveOK256 = true) :
    (∀ a b, applyMoves ms (a &&& b) = applyMoves ms a &&& applyMoves ms b) ∧
    (∀ a b, applyMoves ms (a ||| b) = applyMoves ms a ||| applyMoves ms b) ∧
    (∀ a b, applyMoves ms (a ^^^ b) = applyMoves ms a ^^^ applyMoves ms b) ∧
    applyMoves ms 0 = 0 ∧ applyMoves ms mask256 = mask256 := by
  induction ms with
  | nil => exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩
  | cons p ps ih =>
    simp only [List.all_cons, Bool.and_eq_true, moveOK256, beq_iff_eq] at hok
    obtain ⟨⟨hz, hm⟩, hps⟩ := hok
    obtain ⟨hand, hor, hxor, h0, h256⟩ := ih hps
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro a b; simp only [applyMoves, List.foldl_cons, (move_hom p.1 p.2 hz a b).1]; exact hand _ _
    · intro a b; simp only [applyMoves, List.foldl_cons, (move_hom p.1 p.2 hz a b).2.1]; exact hor _ _
    · intro a b; simp only [applyMoves, List.foldl_cons, (move_hom p.1 p.2 hz a b).2.2]; exact hxor _ _
    · simp only [applyMoves, List.foldl_cons, move_zero p.1 p.2 hz]; exact h0
    · simp only [applyMoves, List.foldl_cons, hm]; exact h256

theorem move_invol (tag d w : Nat) (h : (tag &&& (tag <<< d)) = 0) :
    moveBits tag d (moveBits tag d w) = w := by
  apply Nat.eq_of_testBit_eq; intro i
  have ht := congrArg (fun v : Nat => v.testBit i) h
  simp only [Nat.testBit_and, Nat.zero_testBit] at ht
  rw [moved tag d i _ h]
  by_cases h1 : tag.testBit i = true
  · simp only [h1, ite_true, moved tag d (d + i) w h]
    have h2 : tag.testBit (d + i) = false := by
      have htd := congrArg (fun v : Nat => v.testBit (d + i)) h
      simp only [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.zero_testBit] at htd
      have hge : d ≤ d + i := Nat.le_add_right d i
      have hsub : d + i - d = i := Nat.add_sub_cancel_left d i
      simp [hge, hsub, h1] at htd; exact htd
    have h3 : (tag <<< d).testBit (d + i) = true := by
      simp [Nat.testBit_shiftLeft, Nat.le_add_right, Nat.add_sub_cancel_left, h1]
    simp [h2, h3, Nat.add_sub_cancel_left]
  · simp only [h1, ite_false]
    by_cases h2 : (tag <<< d).testBit i = true
    · simp only [h2, ite_true, moved tag d (i - d) w h]
      rw [Nat.testBit_shiftLeft] at h2
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
      simp [h2.2, Nat.add_sub_of_le h2.1]
    · simp [h1, h2, moved tag d i w h]

theorem applyMoves_inj (ms : List (Nat × Nat)) (hok : ms.all moveOK256 = true) :
    Function.Injective (applyMoves ms) := by
  induction ms with
  | nil => intro a b h; exact h
  | cons p ps ih =>
    simp only [List.all_cons, Bool.and_eq_true, moveOK256, beq_iff_eq] at hok
    intro a b h
    simp only [applyMoves, List.foldl_cons] at h
    have h1 := ih hok.2 h
    have := congrArg (moveBits p.1 p.2) h1
    rwa [move_invol p.1 p.2 a hok.1.1, move_invol p.1 p.2 b hok.1.1] at this

theorem applyMoves_runD {d Y s} (ms : List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    (hd : applyMoves ms d = d) (hY : applyMoves ms Y = Y) {ws} (h : RunD d Y s ws) :
    RunD d Y s (ws.map (applyMoves ms)) := by
  obtain ⟨hand, hor, hxor, h0, h256⟩ := applyMoves_hom ms hok
  have hinj := applyMoves_inj ms hok
  have hneg : ∀ a, applyMoves ms (negD d a) = negD d (applyMoves ms a) := fun a => by
    simp only [negD, hand, hxor, h256, hd]
  have hand' : ∀ a b, applyMoves ms (andD d a b) = andD d (applyMoves ms a) (applyMoves ms b) := fun a b => by
    simp only [andD, hand, hd]
  have hor' : ∀ a b, applyMoves ms (orD d a b) = orD d (applyMoves ms a) (applyMoves ms b) := fun a b => by
    simp only [orD, hand, hor, hd]
  rw [← hY]
  induction h using Run.fold with
  | done => exact Run.done
  | perm hp _ ih => exact Run.perm (hp.map _) ih
  | @one s a r save hne0 hned hnm _ ih =>
    have e1 : (negD d a :: kept save a r).map (applyMoves ms) =
        negD d (applyMoves ms a) :: kept save (applyMoves ms a) (r.map (applyMoves ms)) := by
      simp [kept_map, hneg]
    rw [e1] at ih
    refine Run.one save ?_ ?_ ?_ ih
    · intro e; rw [← hneg] at e; exact hne0 (hinj (e.trans h0.symm))
    · intro e; rw [← hneg] at e; exact hned (hinj (e.trans hd.symm))
    · rw [← hneg, ← List.map_cons, List.mem_map]; rintro ⟨x, hx, he⟩; exact hnm (hinj he ▸ hx)
  | @two s a b r conj ka kb hne0 hned hnm _ ih =>
    have eop : applyMoves ms (if conj then andD d a b else orD d a b) =
        (if conj then andD d (applyMoves ms a) (applyMoves ms b) else orD d (applyMoves ms a) (applyMoves ms b)) := by
      cases conj <;> simp [hand', hor']
    have e1 : ((if conj then andD d a b else orD d a b) :: kept ka a (kept kb b r)).map (applyMoves ms) =
        (if conj then andD d (applyMoves ms a) (applyMoves ms b) else orD d (applyMoves ms a) (applyMoves ms b)) ::
          kept ka (applyMoves ms a) (kept kb (applyMoves ms b) (r.map (applyMoves ms))) := by
      simp [kept_map, eop]
    rw [e1] at ih
    refine Run.two conj ka kb ?_ ?_ ?_ ih
    · intro e; rw [← eop] at e; exact hne0 (hinj (e.trans h0.symm))
    · intro e; rw [← eop] at e; exact hned (hinj (e.trans hd.symm))
    · rw [← eop, ← List.map_cons, ← List.map_cons, List.mem_map]; rintro ⟨x, hx, he⟩; exact hnm (hinj he ▸ hx)

theorem reach_map_moves (ms : List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    {d1 d2 : Nat} (hd : applyMoves ms d2 = d1)
    {roots1 roots2 : List Nat} (hroots : ∀ r ∈ roots2, Avail d1 roots1 (applyMoves ms r)) :
    ∀ {p bank}, NatReach d2 roots2 p bank →
      ∃ bank', NatReach d1 roots1 p bank' ∧ ∀ v ∈ bank, Avail d1 bank' (applyMoves ms v) := by
  obtain ⟨hand, hor, hxor, h0, h256⟩ := applyMoves_hom ms hok
  have hav : ∀ {b b' w}, (∀ v ∈ b, Avail d1 b' (applyMoves ms v)) →
      Avail d2 b w → Avail d1 b' (applyMoves ms w) := by
    intro b b' w hbb hw
    rcases hw with (hz | h1) | ⟨v, hv, he⟩
    · exact Or.inl (Or.inl (by rw [← hd, ← hand, hz, h0]))
    · exact Or.inl (Or.inr (by rw [← hd, ← hand, h1]))
    · have hve : applyMoves ms v &&& d1 = applyMoves ms w &&& d1 := by rw [← hd, ← hand, ← hand, he]
      exact avail_of_eq hve (hbb v hv)
  intro p
  induction p with
  | zero =>
    intro bank hr; subst hr
    exact ⟨roots1, rfl, hroots⟩
  | succ p ih =>
    intro bank hr
    rcases hr with ⟨b, a, rfl, hrb, ha⟩ | ⟨b, a, c, op, rfl, hrb, ha, hc⟩
    · obtain ⟨b', hrb', hbb⟩ := ih hrb
      have ha' := hav hbb ha
      refine ⟨negD d1 (applyMoves ms a) :: b', Or.inl ⟨b', applyMoves ms a, rfl, hrb', ha'⟩, ?_⟩
      intro v hv; rcases List.mem_cons.1 hv with rfl | hv
      · exact Or.inr ⟨negD d1 (applyMoves ms a), List.mem_cons_self, by simp only [negD, hand, hxor, h256, hd]⟩
      · exact avail_cons _ _ (hbb v hv)
    · obtain ⟨b', hrb', hbb⟩ := ih hrb
      have ha' := hav hbb ha; have hc' := hav hbb hc
      refine ⟨binD d1 op (applyMoves ms a) (applyMoves ms c) :: b',
        Or.inr ⟨b', applyMoves ms a, applyMoves ms c, op, rfl, hrb', ha', hc'⟩, ?_⟩
      intro v hv; rcases List.mem_cons.1 hv with rfl | hv
      · exact Or.inr ⟨binD d1 op (applyMoves ms a) (applyMoves ms c), List.mem_cons_self, by
          cases op <;> simp only [binD, andD, orD, hand, hor, hd, ite_true, ite_false, Bool.false_eq_true]⟩
      · exact avail_cons _ _ (hbb v hv)

theorem lower_iso {d1 d2 T1 T2 L : Nat} {roots1 roots2 : List Nat}
    (ms : List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    (hd : applyMoves ms d2 = d1) (hT : applyMoves ms T2 = T1)
    (hroots : roots2.all (fun r => availB d1 roots1 (applyMoves ms r)) = true)
    (h1 : Lower d1 roots1 T1 L) : Lower d2 roots2 T2 L := by
  obtain ⟨hand, _, _, h0, _⟩ := applyMoves_hom ms hok
  have hr : ∀ r ∈ roots2, Avail d1 roots1 (applyMoves ms r) := fun r hr =>
    (availB_iff _ _ _).1 (List.all_eq_true.1 hroots r hr)
  intro p bank hreach ha
  obtain ⟨bank', hrb', hbb⟩ := reach_map_moves ms hok hd hr hreach
  apply h1 p bank' hrb'
  rcases ha with (hz | ho) | ⟨v, hv, he⟩
  · exact Or.inl (Or.inl (by rw [← hT, ← hd, ← hand, hz, h0]))
  · exact Or.inl (Or.inr (by rw [← hT, ← hd, ← hand, ho]))
  · have hve : applyMoves ms v &&& d1 = T1 &&& d1 := by rw [← hT, ← hd, ← hand, ← hand, he]
    exact avail_of_eq hve (hbb v hv)

-- lower_slice!
def pairOK (d T : Nat) (p : Nat × Nat) : Bool :=
  d.testBit p.1 && d.testBit p.2 && (T.testBit p.1 != T.testBit p.2)

def essOK (d T : Nat) (roots : List Nat) (a : Nat) (p : Nat × Nat) : Bool :=
  pairOK d T p && roots.all (fun v => (v == a) || (v.testBit p.1 == v.testBit p.2))

theorem countP_ge_sublist (p : Nat → Bool) {xs ys : List Nat}
    (hnd : xs.Nodup) (hsub : ∀ a ∈ xs, a ∈ ys) (hall : ∀ a ∈ xs, p a = true) :
    xs.length ≤ ys.countP p := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    have ⟨hna, hnd'⟩ := List.nodup_cons.1 hnd
    have ham : a ∈ ys := hsub a List.mem_cons_self
    have hperm : ys.Perm (a :: ys.erase a) := List.perm_cons_erase ham
    rw [hperm.countP_eq, List.countP_cons, hall a List.mem_cons_self]
    have ih' := ih hnd' (fun x hx => by
      have hne : x ≠ a := fun e => hna (e ▸ hx)
      exact (List.mem_erase_of_ne hne).2 (hsub x (List.mem_cons_of_mem _ hx)))
      (fun x hx => hall x (List.mem_cons_of_mem _ hx))
    simp only [ite_true, List.length_cons]
    omega

theorem lower_slice {d dSub T TSub L : Nat} {roots rootsSub : List Nat}
    (hd : d &&& mask256 = d) (hdSub : dSub &&& mask256 = dSub) (hsub : dSub &&& d = dSub)
    (hT : T &&& dSub = TSub &&& dSub)
    (hnc : isConstB d T = false) (hncSub : isConstB dSub TSub = false)
    (hcov : roots.all (availB dSub rootsSub) = true)
    (singles : List (Nat × Nat × Nat))
    (hs_nd : (singles.map Prod.fst).Nodup)
    (hs_ok : singles.all (fun e => isConstB dSub e.1 && essOK d (T &&& d) (roots.map (· &&& d)) e.1 e.2) = true)
    (hprior : Lower dSub rootsSub TSub L) :
    Lower d roots T (L + singles.length) := by
  have hnc' : ¬ IsConst d T := fun h => by rw [(isConstB_iff _ _).2 h] at hnc; contradiction
  have hncSub' : ¬ IsConst dSub (T &&& d) := by
    intro h
    have e : (T &&& d) &&& dSub = TSub &&& dSub := by
      rw [Nat.and_assoc, Nat.and_comm d dSub, hsub, hT]
    rcases h with h0 | h1
    · exact absurd ((isConstB_iff _ _).2 (Or.inl (e.symm.trans h0))) (by simp [hncSub])
    · exact absurd ((isConstB_iff _ _).2 (Or.inr (e.symm.trans h1))) (by simp [hncSub])
  intro p bank hr ha
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run hd hnc' hr ha
  have hws_av : ∀ w ∈ ws, Avail dSub rootsSub w := by
    intro w hw
    obtain ⟨r, hr_m, rfl⟩ := List.mem_map.1 (hws_sub w hw)
    have hav := (availB_iff _ _ _).1 (List.all_eq_true.1 hcov r hr_m)
    exact avail_of_eq (by rw [Nat.and_assoc, Nat.and_comm d dSub, hsub]) hav
  obtain ⟨q, next, hq, ht, hle⟩ := contraction hdSub hsub hncSub' hrun (p := 0) (bank := rootsSub) rfl hws_av
  have hTSub_av : Avail dSub next TSub := avail_of_eq (by
    rw [Nat.and_assoc, Nat.and_comm d dSub, hsub, hT]) ht
  have hL : L ≤ q := hprior q next hq hTSub_av
  have hsin_mem : ∀ a ∈ singles.map Prod.fst, a ∈ ws := by
    intro a ha
    obtain ⟨⟨a', r1, r2⟩, hm, rfl⟩ := List.mem_map.1 ha
    have hok := List.all_eq_true.1 hs_ok (a', r1, r2) hm
    simp only [Bool.and_eq_true, essOK, pairOK, bne_iff_ne, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at hok
    obtain ⟨_, ⟨⟨hr1, hr2⟩, hdiff⟩, hiso⟩ := hok
    by_contra hnot
    apply hdiff
    apply runD_bits hd hrun r1 r2 hr1 hr2
    intro w hw
    rcases hiso w (hws_sub w hw) with rfl | heq
    · exact absurd hw hnot
    · exact heq
  have hsin_const : ∀ a ∈ singles.map Prod.fst, isConstB dSub a = true := by
    intro a ha
    obtain ⟨⟨a', r1, r2⟩, hm, rfl⟩ := List.mem_map.1 ha
    have hok := List.all_eq_true.1 hs_ok _ hm
    simp only [Bool.and_eq_true] at hok
    exact hok.1
  have hcnt := countP_ge_sublist (isConstB dSub) hs_nd hsin_mem hsin_const
  simp only [List.length_map] at hcnt
  omega

-- poolCut (compact 52-bit hint!) + covers + eval6 + bar!
def runChoices (d : Nat) (pool : List Nat) : Nat → Nat → Option (List Nat)
  | 0, _ => some pool
  | p + 1, bits =>
    let code := bits &&& 1023
    let op := code &&& 3
    let ia := (code >>> 2) &&& 15
    let ib := (code >>> 6) &&& 15
    if ia < pool.length && (op == 2 || ib < pool.length) then
      let a := pool.getD ia 0
      let b := pool.getD ib 0
      let w := if op == 2 then negD d a else binD d (op == 1) a b
      runChoices d (pool ++ [w]) p (bits >>> 10)
    else none

theorem getD_mem {xs : List Nat} {i : Nat} (hi : i < xs.length) : xs.getD i 0 ∈ xs := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact List.getElem_mem hi

theorem runChoices_sound {d : Nat} {roots : List Nat} :
    ∀ (p bits q : Nat) (bank pool result : List Nat),
      NatReach d roots q bank →
      (∀ v ∈ pool, Avail d bank v) →
      runChoices d pool p bits = some result →
      ∃ bank', NatReach d roots (q + p) bank' ∧ ∀ v ∈ result, Avail d bank' v
  | 0, _, q, bank, pool, result, hr, hsup, hok => by
    simp only [runChoices, Option.some.injEq] at hok; subst hok; exact ⟨bank, hr, hsup⟩
  | p + 1, bits, q, bank, pool, result, hr, hsup, hok => by
    simp only [runChoices] at hok
    split at hok
    · rename_i hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at hcond
      obtain ⟨hia, hopb⟩ := hcond
      set code := bits &&& 1023
      set op := code &&& 3
      set ia := (code >>> 2) &&& 15
      set ib := (code >>> 6) &&& 15
      set a := pool.getD ia 0
      set b := pool.getD ib 0
      set w := if op == 2 then negD d a else binD d (op == 1) a b
      have ha : Avail d bank a := hsup a (getD_mem hia)
      have hr1 : NatReach d roots (q + 1) (w :: bank) := by
        by_cases h2 : op = 2
        · simp only [w, h2, beq_self_eq_true, ite_true]
          exact Or.inl ⟨bank, a, rfl, hr, ha⟩
        · have hib : ib < pool.length := hopb.resolve_left h2
          have hb : Avail d bank b := hsup b (getD_mem hib)
          simp only [w, h2, beq_iff_eq, ite_false]
          exact Or.inr ⟨bank, a, b, (op == 1), rfl, hr, ha, hb⟩
      have hsup1 : ∀ v ∈ pool ++ [w], Avail d (w :: bank) v := by
        intro v hv; rcases List.mem_append.1 hv with hv | hv
        · exact avail_cons _ _ (hsup v hv)
        · rw [List.mem_singleton.1 hv]; exact Or.inr ⟨w, List.mem_cons_self, rfl⟩
      obtain ⟨bank', hrb', hsb'⟩ := runChoices_sound p (bits >>> 10) (q + 1) (w :: bank) (pool ++ [w]) result hr1 hsup1 hok
      exact ⟨bank', by simpa [Nat.add_assoc, Nat.add_comm 1] using hrb', hsb'⟩
    · contradiction

def checkCutEntry (dSub : Nat) (rootsSub : List Nat) (LSub s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  let p := (hint >>> 8) &&& 15
  decide (s + p < LSub + ws.countP (isConstB dSub)) &&
  match runChoices dSub rootsSub p (hint >>> 12) with
  | none => false
  | some pool => ws.all (availB dSub pool)

theorem checkCutEntry_sound {d dSub T TSub LSub s : Nat} {rootsSub ws : List Nat}
    (hdSub : dSub &&& mask256 = dSub) (hsub : dSub &&& d = dSub)
    (hT : T &&& dSub = TSub &&& dSub) (hncSub : isConstB dSub TSub = false)
    (hprior : Lower dSub rootsSub TSub LSub) (hint : Nat)
    (hchk : checkCutEntry dSub rootsSub LSub s ws hint = true) :
    ¬ RunD d (T &&& d) s ws := by
  intro hrun
  simp only [checkCutEntry, Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨hineq, hmatch⟩ := hchk
  cases hrc : runChoices dSub rootsSub ((hint >>> 8) &&& 15) (hint >>> 12) with
  | none => rw [hrc] at hmatch; contradiction
  | some pool =>
    rw [hrc] at hmatch
    have hsup0 : ∀ v ∈ rootsSub, Avail dSub rootsSub v := fun v hv => Or.inr ⟨v, hv, rfl⟩
    obtain ⟨bank, hrb, hsb⟩ := runChoices_sound _ _ 0 rootsSub rootsSub pool rfl hsup0 hrc
    simp only [Nat.zero_add] at hrb
    have hws_av : ∀ w ∈ ws, Avail dSub bank w := by
      intro w hw
      have hav := (availB_iff _ _ _).1 (List.all_eq_true.1 hmatch w hw)
      rcases hav with hc | ⟨v, hv, he⟩
      · exact Or.inl hc
      · exact avail_of_eq he (hsb v hv)
    have hnc' : ¬ IsConst dSub (T &&& d) := by
      intro h; have e : (T &&& d) &&& dSub = TSub &&& dSub := by rw [Nat.and_assoc, Nat.and_comm d dSub, hsub, hT]
      rcases h with h0 | h1
      · exact absurd ((isConstB_iff _ _).2 (Or.inl (e.symm.trans h0))) (by simp [hncSub])
      · exact absurd ((isConstB_iff _ _).2 (Or.inr (e.symm.trans h1))) (by simp [hncSub])
    obtain ⟨q, next, hq, ht, hle⟩ := contraction hdSub hsub hnc' hrun hrb hws_av
    have hL := hprior q next hq (avail_of_eq (by rw [Nat.and_assoc, Nat.and_comm d dSub, hsub, hT]) ht)
    omega

-- covers, eval6, hw256, hk, bsr, bar, bar_all!
def coversP (pairs : List (Nat × Nat)) (s : Nat) (ws : List Nat) : Bool :=
  if ws.length == s + 1 then
    pairs.all (fun p => ws.any (fun w => !w.testBit p.1 && w.testBit p.2))
  else
    pairs.all (fun p => ws.any (fun w => w.testBit p.1 != w.testBit p.2))

theorem coversP_ok {d T s : Nat} (hd : d &&& mask256 = d)
    (pairs : List (Nat × Nat))
    (hpairs : pairs.all (fun p => d.testBit p.1 && d.testBit p.2 && !(T &&& d).testBit p.1 && (T &&& d).testBit p.2) = true)
    {ws : List Nat} (h : RunD d (T &&& d) s ws) : coversP pairs s ws = true := by
  unfold coversP
  by_cases hl : ws.length = s + 1
  · simp only [hl, beq_self_eq_true, ite_true, List.all_eq_true, List.any_eq_true]
    intro ⟨u, v⟩ hm
    have hp := List.all_eq_true.1 hpairs (u, v) hm
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
    by_contra! hall
    have hle := runD_bits_le h hl v u hp.1.1.2 hp.1.1.1 (fun w hw => by
      have hbad := hall w hw
      cases hu : w.testBit u <;> cases hv : w.testBit v <;> simp_all)
    rw [hp.1.2, hp.2] at hle; contradiction
  · simp only [hl, beq_iff_eq, ite_false, List.all_eq_true, List.any_eq_true, bne_iff_ne]
    intro ⟨u, v⟩ hm
    have hp := List.all_eq_true.1 hpairs (u, v) hm
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
    by_contra! hall
    have heq := runD_bits hd h u v hp.1.1.1 hp.1.1.2 hall
    rw [hp.1.2, hp.2] at heq; contradiction

def unorientedCov (pairs : List (Nat × Nat)) (ws : List Nat) : Bool :=
  pairs.all (fun p => ws.any (fun w => w.testBit p.1 != w.testBit p.2))

theorem unorientedCov_ok {d T s : Nat} (hd : d &&& mask256 = d)
    (pairs : List (Nat × Nat))
    (hpairs : pairs.all (fun p => d.testBit p.1 && d.testBit p.2 && !(T &&& d).testBit p.1 && (T &&& d).testBit p.2) = true)
    {ws : List Nat} (h : RunD d (T &&& d) s ws) : unorientedCov pairs ws = true := by
  simp only [unorientedCov, List.all_eq_true, List.any_eq_true, bne_iff_ne]
  intro ⟨u, v⟩ hm
  have hp := List.all_eq_true.1 hpairs (u, v) hm
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
  by_contra! hall
  have heq := runD_bits hd h u v hp.1.1.1 hp.1.1.2 hall
  rw [hp.1.2, hp.2] at heq; contradiction

-- Fast bitmask-decorated covers (150x faster than per-pair testBit!)
def maskP (m : Nat) : Nat := 2 ^ m - 1

def projBit (rs : List Nat) (w : Nat) : Nat :=
  rs.foldr (fun r acc => (acc <<< 1) ||| (if w.testBit r then 1 else 0)) 0

theorem projBit_testBit (rs : List Nat) (w : Nat) (i : Nat) :
    (projBit rs w).testBit i = if h : i < rs.length then w.testBit rs[i] else false := by
  induction rs generalizing i with
  | nil => simp [projBit]
  | cons r rs ih =>
    cases i with
    | zero =>
      simp only [projBit, List.foldr_cons, Nat.testBit_or, Nat.testBit_shiftLeft,
        Nat.not_le.2 Nat.zero_lt_one, decide_false, Bool.false_and, Bool.false_or,
        List.length_cons, Nat.zero_lt_succ, dite_true, List.getElem_cons_zero]
      cases w.testBit r <;> simp
    | succ i =>
      simp only [projBit, List.foldr_cons, Nat.testBit_or, Nat.testBit_shiftLeft,
        Nat.succ_le_succ (Nat.zero_le i), decide_true, Bool.true_and, Nat.add_sub_cancel,
        List.length_cons, Nat.succ_lt_succ_iff, List.getElem_cons_succ]
      have h1 : (if w.testBit r = true then 1 else 0).testBit (i + 1) = false := by
        cases w.testBit r <;> simp [Nat.testBit_succ]
      rw [h1, Bool.or_false]; exact ih i

theorem projBit_negD {dm : Nat} (hd : dm &&& mask256 = dm) {rs : List Nat}
    (hrs : ∀ r ∈ rs, dm.testBit r = true) (w : Nat) :
    projBit rs (negD dm w) = projBit rs w ^^^ maskP rs.length := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [projBit_testBit, Nat.testBit_xor, projBit_testBit, maskP, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < rs.length
  · have hdr := hrs rs[i] (List.getElem_mem hi)
    have hmr : mask256.testBit rs[i] = true := by
      have := congrArg (fun v => v.testBit rs[i]) hd; simp [Nat.testBit_and, hdr] at this; exact this
    simp [hi, negD, hdr, hmr]
  · simp [hi]

theorem projBit_andD {dm : Nat} {rs : List Nat} (hrs : ∀ r ∈ rs, dm.testBit r = true) (a b : Nat) :
    projBit rs (andD dm a b) = projBit rs a &&& projBit rs b := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [projBit_testBit, Nat.testBit_and, projBit_testBit, projBit_testBit]
  by_cases hi : i < rs.length
  · simp [hi, andD, hrs rs[i] (List.getElem_mem hi)]
  · simp [hi]

theorem projBit_orD {dm : Nat} {rs : List Nat} (hrs : ∀ r ∈ rs, dm.testBit r = true) (a b : Nat) :
    projBit rs (orD dm a b) = projBit rs a ||| projBit rs b := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [projBit_testBit, Nat.testBit_or, projBit_testBit, projBit_testBit]
  by_cases hi : i < rs.length
  · simp [hi, orD, hrs rs[i] (List.getElem_mem hi)]
  · simp [hi]

theorem foldl_or_testBit {α : Type} (g : α → Nat) (xs : List α) (acc i : Nat) :
    (xs.foldl (fun a x => a ||| g x) acc).testBit i = (acc.testBit i || xs.any (fun x => (g x).testBit i)) := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, Nat.testBit_or, List.any_cons, Bool.or_assoc]

def coversD (mp s : Nat) (dws : List (Nat × Nat × Nat)) : Bool :=
  if dws.length == s + 1 then
    dws.foldl (fun acc d => acc ||| ((d.2.1 ^^^ mp) &&& d.2.2)) 0 == mp
  else
    dws.foldl (fun acc d => acc ||| (d.2.1 ^^^ d.2.2)) 0 == mp

theorem coversD_eq (pairs : List (Nat × Nat)) (s : Nat) (ws : List Nat) :
    coversD (maskP pairs.length) s (ws.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w))) =
      coversP pairs s ws := by
  set r1s := pairs.map Prod.fst
  set r2s := pairs.map Prod.snd
  set mp := maskP pairs.length
  have hr1 : r1s.length = pairs.length := List.length_map _
  have hr2 : r2s.length = pairs.length := List.length_map _
  unfold coversD coversP
  simp only [List.length_map]
  split
  · apply Bool.eq_iff_iff.2
    rw [beq_iff_eq, List.all_eq_true]
    constructor
    · intro heq pr hpr
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hpr
      have hb := congrArg (fun v => v.testBit i) heq
      rw [foldl_or_testBit, Nat.zero_testBit, Bool.false_or, List.any_map] at hb
      simp only [mp, maskP, Nat.testBit_two_pow_sub_one, hi, decide_true] at hb
      obtain ⟨w, hw, hwt⟩ := List.any_eq_true.1 hb
      simp only [Function.comp_def, Nat.testBit_and, Nat.testBit_xor, projBit_testBit, hr1, hr2, hi, dite_true,
        Nat.testBit_two_pow_sub_one, decide_true, Bool.xor_true] at hwt
      exact List.any_eq_true.2 ⟨w, hw, by simpa [r1s, r2s] using hwt⟩
    · intro hall
      apply Nat.eq_of_testBit_eq; intro i
      rw [foldl_or_testBit, Nat.zero_testBit, Bool.false_or, List.any_map]
      simp only [mp, maskP, Nat.testBit_two_pow_sub_one]
      by_cases hi : i < pairs.length
      · simp only [hi, decide_true]
        obtain ⟨w, hw, hwt⟩ := List.any_eq_true.1 (hall pairs[i] (List.getElem_mem hi))
        exact List.any_eq_true.2 ⟨w, hw, by
          simp only [Function.comp_def, Nat.testBit_and, Nat.testBit_xor, projBit_testBit, hr1, hr2, hi, dite_true,
            Nat.testBit_two_pow_sub_one, decide_true, Bool.xor_true, r1s, r2s, List.getElem_map]
          exact hwt⟩
      · simp only [hi, decide_false, List.any_eq_false]
        intro w _
        simp only [Function.comp_def, Nat.testBit_and, Nat.testBit_xor, projBit_testBit, hr1, hr2, hi, dite_false,
          Nat.testBit_two_pow_sub_one, decide_false, Bool.xor_false, Bool.and_false, not_false_eq_true, Bool.false_eq_true]
  · apply Bool.eq_iff_iff.2
    rw [beq_iff_eq, List.all_eq_true]
    constructor
    · intro heq pr hpr
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hpr
      have hb := congrArg (fun v => v.testBit i) heq
      rw [foldl_or_testBit, Nat.zero_testBit, Bool.false_or, List.any_map] at hb
      simp only [mp, maskP, Nat.testBit_two_pow_sub_one, hi, decide_true] at hb
      obtain ⟨w, hw, hwt⟩ := List.any_eq_true.1 hb
      simp only [Function.comp_def, Nat.testBit_xor, projBit_testBit, hr1, hr2, hi, dite_true] at hwt
      exact List.any_eq_true.2 ⟨w, hw, by simpa [r1s, r2s, bne] using hwt⟩
    · intro hall
      apply Nat.eq_of_testBit_eq; intro i
      rw [foldl_or_testBit, Nat.zero_testBit, Bool.false_or, List.any_map]
      simp only [mp, maskP, Nat.testBit_two_pow_sub_one]
      by_cases hi : i < pairs.length
      · simp only [hi, decide_true]
        obtain ⟨w, hw, hwt⟩ := List.any_eq_true.1 (hall pairs[i] (List.getElem_mem hi))
        exact List.any_eq_true.2 ⟨w, hw, by
          simp only [Function.comp_def, Nat.testBit_xor, projBit_testBit, hr1, hr2, hi, dite_true, r1s, r2s, List.getElem_map]
          simpa [bne] using hwt⟩
      · simp only [hi, decide_false, List.any_eq_false]
        intro w _
        simp only [Function.comp_def, Nat.testBit_xor, projBit_testBit, hr1, hr2, hi, dite_false,
          Bool.xor_false, Bool.false_eq_true, not_false_eq_true]

theorem erase_map_inj {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (f : α → β) (hinj : Function.Injective f) (xs : List α) (a : α) :
    (xs.map f).erase (f a) = (xs.erase a).map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.erase_cons]
    by_cases h : x = a
    · subst h; simp
    · have hf : (f x == f a) = false := beq_false_of_ne (fun e => h (hinj e))
      have hx : (x == a) = false := beq_false_of_ne h
      simp [hf, hx, ih]

def value6 (a b c d e f : Bool) : Nat :=
  let x := b.toNat + c.toNat
  let y := (!e).toNat + (!f).toNat
  if a then (if d then y else max x (max y (x + y - 1))) else (if d then 0 else x)

theorem value6_and : ∀ a b c d e f g h i j l m : Bool,
    value6 (a && g) (b && h) (c && i) (d && j) (e && l) (f && m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem value6_or : ∀ a b c d e f g h i j l m : Bool,
    value6 (a || g) (b || h) (c || i) (d || j) (e || l) (f || m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem score_bound {d y s ws} (h : RunD d y s ws) (hl : ws.length = s + 1)
    (v : Nat → Nat) (hand : ∀ a b, v (andD d a b) ≤ v a + v b)
    (hor : ∀ a b, v (orD d a b) ≤ v a + v b) : v y ≤ (ws.map v).sum := by
  induction h using Run.fold with
  | done => simp
  | perm p _ ih => rw [← (p.map v).sum_eq]; exact ih (p.length_eq.trans hl)
  | one save _ _ _ h _ => have hh := run_len h; cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb _ _ _ h ih =>
    have hh := run_len h; cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    have ih' := ih (by simp [kept]; omega)
    cases conj <;> simp [kept] at ih' ⊢ <;>
      first | grw [← Nat.add_assoc, ← hand]; exact ih' | grw [← Nat.add_assoc, ← hor]; exact ih'

def eval6 (a b c d e f v : Nat) := value6 (v.testBit a) (v.testBit b) (v.testBit c)
    (v.testBit d) (v.testBit e) (v.testBit f)

theorem eval6_bound {dm y s ws} (h : RunD dm y s ws) (hl : ws.length = s + 1)
    (a b c d e f : Nat)
    (ha : dm.testBit a = true) (hb : dm.testBit b = true) (hc : dm.testBit c = true)
    (hd : dm.testBit d = true) (he : dm.testBit e = true) (hf : dm.testBit f = true) :
    eval6 a b c d e f y ≤ (ws.map (eval6 a b c d e f)).sum := by
  apply score_bound h hl
  · intro v w
    simpa only [eval6, andD, Nat.testBit_and, ha, hb, hc, hd, he, hf, Bool.and_true] using value6_and
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)
  · intro v w
    simpa only [eval6, orD, Nat.testBit_and, Nat.testBit_or, ha, hb, hc, hd, he, hf, Bool.and_true] using value6_or
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)

def sumBelow (v : Nat → Nat) : List Nat → Nat → Bool
  | [], n => n != 0
  | w :: ws, n => decide (v w < n) && sumBelow v ws (n - v w)

theorem sumBelow_iff (v : Nat → Nat) (ws : List Nat) (n : Nat) :
    sumBelow v ws n = true ↔ (ws.map v).sum < n := by
  induction ws generalizing n with
  | nil => simp [sumBelow]
  | cons w ws ih => rw [sumBelow, Bool.and_eq_true, decide_eq_true_eq, ih, List.map_cons, List.sum_cons]; omega

def scoreCheck (dm y s : Nat) (ws : List Nat) (code : Nat) : Bool :=
  let a := code &&& 255
  let b := (code >>> 8) &&& 255
  let c := (code >>> 16) &&& 255
  let d := (code >>> 24) &&& 255
  let e := (code >>> 32) &&& 255
  let f := (code >>> 40) &&& 255
  dm.testBit a && dm.testBit b && dm.testBit c && dm.testBit d && dm.testBit e && dm.testBit f &&
    ws.length == s + 1 && sumBelow (eval6 a b c d e f) ws (eval6 a b c d e f y)

theorem scoreCheck_no {dm y s ws} (h : RunD dm y s ws) (code : Nat) :
    scoreCheck dm y s ws code = false := by
  unfold scoreCheck
  by_cases hok : dm.testBit (code &&& 255) = true ∧ dm.testBit ((code >>> 8) &&& 255) = true ∧
      dm.testBit ((code >>> 16) &&& 255) = true ∧ dm.testBit ((code >>> 24) &&& 255) = true ∧
      dm.testBit ((code >>> 32) &&& 255) = true ∧ dm.testBit ((code >>> 40) &&& 255) = true ∧
      ws.length = s + 1
  · obtain ⟨ha, hb, hc, hd, he, hf, hl⟩ := hok
    simp only [ha, hb, hc, hd, he, hf, hl, beq_self_eq_true, Bool.true_and]
    by_contra hbad
    have hsum := (sumBelow_iff _ _ _).1 (Bool.eq_true_of_not_eq_false hbad)
    exact (Nat.not_lt_of_ge (eval6_bound h hl _ _ _ _ _ _ ha hb hc hd he hf)) hsum
  · by_contra hbad
    have ht := Bool.eq_true_of_not_eq_false hbad
    simp only [Bool.and_eq_true, beq_iff_eq] at ht
    exact hok ⟨ht.1.1.1.1.1.1.1, ht.1.1.1.1.1.1.2, ht.1.1.1.1.1.2, ht.1.1.1.1.2, ht.1.1.1.2, ht.1.1.2, ht.1.2⟩

def scr (dm y s : Nat) (pool : List Nat) (zs : List Nat) : Bool :=
  zs.length == s + 1 && pool.any (scoreCheck dm y s zs)

theorem scr_no {dm y s : Nat} (pool : List Nat) {zs : List Nat}
    (h : RunD dm y s zs) : scr dm y s pool zs = false := by
  unfold scr; rw [Bool.and_eq_false_iff]; right; rw [List.any_eq_false]
  intro x _; rw [scoreCheck_no h x]; simp

def nextD (dm : Nat) (slack : Nat) (ws : List Nat) (f : List Nat → Bool) : Bool :=
  ws.any fun a =>
    let ra := ws.erase a
    (slack ≥ 1 &&
      (let w := negD dm a
       w != 0 && w != dm && !(ws.contains w) &&
         (f (w :: ra) || (slack ≥ 2 && f (w :: a :: ra))))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        [false, true].any fun conj =>
          let w := if conj then andD dm a b else orD dm a b
          w != 0 && w != dm && !(ws.contains w) &&
            (f (w :: r) || (slack ≥ 1 && (f (w :: a :: r) || f (w :: b :: r))) ||
              (slack ≥ 2 && f (w :: a :: b :: r))))

theorem nextD_one {dm y a rest} {save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h0 : negD dm a ≠ 0) (hd : negD dm a ≠ dm) (hnm : negD dm a ∉ (a :: rest))
    (h : RunD dm y s (negD dm a :: kept save a rest))
    (f : List Nat → Bool) (hf : ∀ ys, RunD dm y s ys → f ys = true) :
    nextD dm (s + 2 - ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a) := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hh := run_len h; have hl := p.length_eq; simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s + 2 - ws.length := by cases save <;> simp [kept] at hh <;> omega
  have hnc : ws.contains (negD dm a) = false := by
    cases h : ws.contains (negD dm a) with
    | false => rfl
    | true => exact absurd (p.mem_iff.2 (by simpa using h)) hnm
  have h0b : (negD dm a != 0) = true := bne_iff_ne.2 h0
  have hdb : (negD dm a != dm) = true := bne_iff_ne.2 hd
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; left; rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl, ?_⟩
  simp only [h0b, hdb, hnc, Bool.not_false, Bool.true_and]
  have ht := hf _ (Run.perm ((keep_perm pr save a).cons _) h)
  cases save with
  | false => simp [kept] at ht; simp [ht]
  | true => simp [kept] at ht hh; simp [ht, show 2 ≤ s + 2 - ws.length by omega]

theorem nextD_two_sorted {dm y a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h0 : (if conj then andD dm a b else orD dm a b) ≠ 0)
    (hd : (if conj then andD dm a b else orD dm a b) ≠ dm)
    (hnm : (if conj then andD dm a b else orD dm a b) ∉ (a :: b :: rest))
    (h : RunD dm y s ((if conj then andD dm a b else orD dm a b) :: kept ka a (kept kb b rest)))
    (f : List Nat → Bool) (hf : ∀ ys, RunD dm y s ys → f ys = true) :
    nextD dm (s + 2 - ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pp := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hb := pp.mem_iff.1 List.mem_cons_self
  have pr := (pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh := run_len h; have hl := p.length_eq; simp only [List.length_cons] at hl hh
  have hnc : ws.contains (if conj then andD dm a b else orD dm a b) = false := by
    cases h : ws.contains (if conj then andD dm a b else orD dm a b) with
    | false => rfl
    | true => exact absurd (p.mem_iff.2 (by simpa using h)) hnm
  have h0b : ((if conj then andD dm a b else orD dm a b) != 0) = true := bne_iff_ne.2 h0
  have hdb : ((if conj then andD dm a b else orD dm a b) != dm) = true := bne_iff_ne.2 hd
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; right; apply List.any_eq_true.2 ⟨b, hb, ?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab, ?_⟩
  apply List.any_eq_true.2 ⟨conj, by cases conj <;> simp, ?_⟩
  simp only [h0b, hdb, hnc, Bool.not_false, Bool.true_and]
  have ht := hf _ (Run.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht, Bool.true_or, Bool.or_true, Bool.and_true] <;>
    first | (simp [show 2 ≤ s + 2 - ws.length by omega]) | (simp [show 1 ≤ s + 2 - ws.length by omega])

theorem nextD_two {dm y a b rest} {conj ka kb : Bool} {s ws} (p : (a :: b :: rest).Perm ws)
    (h0 : (if conj then andD dm a b else orD dm a b) ≠ 0)
    (hd : (if conj then andD dm a b else orD dm a b) ≠ dm)
    (hnm : (if conj then andD dm a b else orD dm a b) ∉ (a :: b :: rest))
    (h : RunD dm y s ((if conj then andD dm a b else orD dm a b) :: kept ka a (kept kb b rest)))
    (f : List Nat → Bool) (hf : ∀ ys, RunD dm y s ys → f ys = true) :
    nextD dm (s + 2 - ws.length) ws f = true := by
  rcases le_total a b with hab | hba
  · exact nextD_two_sorted hab p h0 hd hnm h f hf
  · have he : (if conj then andD dm a b else orD dm a b) = (if conj then andD dm b a else orD dm b a) := by
      cases conj <;> simp [andD, orD, Nat.and_comm, Nat.or_comm]
    have hnm' : (if conj then andD dm b a else orD dm b a) ∉ (b :: a :: rest) := by
      rw [← he]; intro hm; exact hnm ((List.Perm.swap _ _ _).mem_iff.1 hm)
    apply nextD_two_sorted (conj := conj) (ka := kb) (kb := ka) hba ((List.Perm.swap _ _ _).trans p)
      (he ▸ h0) (he ▸ hd) hnm' _ f hf
    rw [he] at h; apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]; exact List.Perm.swap _ _ _

theorem nextD_complete {dm y t ws} (h : RunD dm y t ws) :
    ∀ s, t = s + 1 → ∀ zs, ws.Perm zs → ∀ f : List Nat → Bool,
      (∀ ys, RunD dm y s ys → f ys = true) →
      nextD dm (s + 2 - zs.length) zs f = true := by
  induction h using Run.fold with
  | done => simp
  | perm p _ ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one save h0 hd hnm h _ => intro s he zs p f hf; cases he; exact nextD_one p h0 hd hnm h f hf
  | two conj ka kb h0 hd hnm h _ => intro s he zs p f hf; cases he; exact nextD_two p h0 hd hnm h f hf

def span (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n + 1, i => f i && span f n (i + 1)

theorem span_ok {f n o} (h : span f n o = true) : ∀ i, o ≤ i → i < o + n → f i = true := by
  induction n generalizing o with
  | zero => omega
  | succ n ih =>
    simp only [span, Bool.and_eq_true] at h; intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)

theorem range_split {P : Nat → Prop} {lo mid hi : Nat}
    (h1 : ∀ i, lo ≤ i → i < mid → P i) (h2 : ∀ i, mid ≤ i → i < hi → P i) :
    ∀ i, lo ≤ i → i < hi → P i := fun i hlo hhi =>
  if h : i < mid then h1 i hlo h else h2 i (Nat.le_of_not_lt h) hhi

def fld (T w i : Nat) : Nat :=
  (T >>> (w * i)) &&& (if w == 32 then 4294967295 else if w == 52 then 4503599627370495 else if w == 256 then mask256 else 2 ^ w - 1)

def bsr (read : Nat → Nat) (h : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if lo + 1 < hi then
      (if read ((lo + hi) / 2) ≤ h then bsr read h f ((lo + hi) / 2) hi
       else bsr read h f lo ((lo + hi) / 2))
    else lo

def hw256 (seed w : Nat) : Nat :=
  let x := (((w &&& 4294967295) ^^^ seed) * 2654435761 +
            (((w >>> 32) &&& 4294967295) ^^^ seed) * 2246822519 +
            (((w >>> 64) &&& 4294967295) ^^^ seed) * 3266489917 +
            (((w >>> 96) &&& 4294967295) ^^^ seed) * 668265263 +
            (((w >>> 128) &&& 4294967295) ^^^ seed) * 374761393 +
            (((w >>> 160) &&& 4294967295) ^^^ seed) * 1274126177 +
            (((w >>> 192) &&& 4294967295) ^^^ seed) * 2869860233 +
            (((w >>> 224) &&& 4294967295) ^^^ seed) * 1640531527) &&& 4294967295
  let y := ((x ^^^ (x >>> 16)) * 2246822519) &&& 4294967295
  ((y ^^^ (y >>> 13)) * 3266489917) &&& 4294967295

def hz (seed : Nat) : List Nat → Nat
  | [] => 0
  | w :: t => hw256 seed w + hz seed t

def hk (seed : Nat) (zs : List Nat) : Nat := hz seed zs &&& 4294967295

def found (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat)
    (s : Nat) (zs : List Nat) : Bool :=
  decide (idx s zs < N s) && zs.isPerm (S s (idx s zs))

def foundH (S : Nat → Nat → List Nat) (N : Nat → Nat) (htAt : Nat → Nat → Nat)
    (idxH : Nat → Nat → Nat) (s h : Nat) (zs : List Nat) : Bool :=
  let i := idxH s h
  decide (i < N s) && (htAt s i == h) && zs.isPerm (S s i)

def nextD_decor (dm mp : Nat) (slack : Nat) (dws : List (Nat × Nat × Nat))
    (f : List (Nat × Nat × Nat) → Bool) : Bool :=
  dws.any fun da =>
    let a := da.1
    let ra := dws.erase da
    (slack ≥ 1 &&
      (let w := negD dm a
       w != 0 && w != dm && !(dws.any (fun x => x.1 == w)) &&
         let dw := (w, da.2.1 ^^^ mp, da.2.2 ^^^ mp)
         (f (dw :: ra) || (slack ≥ 2 && f (dw :: da :: ra))))) ||
    ra.any fun db =>
      let b := db.1
      a ≤ b && (let r := ra.erase db
        [false, true].any fun conj =>
          let w := if conj then andD dm a b else orD dm a b
          w != 0 && w != dm && !(dws.any (fun x => x.1 == w)) &&
            let dw := if conj then (w, da.2.1 &&& db.2.1, da.2.2 &&& db.2.2)
                      else (w, da.2.1 ||| db.2.1, da.2.2 ||| db.2.2)
            (f (dw :: r) || (slack ≥ 1 && (f (dw :: da :: r) || f (dw :: db :: r))) ||
              (slack ≥ 2 && f (dw :: da :: db :: r))))

theorem nextD_decor_gen (dm mp : Nat) (dec : Nat → Nat × Nat × Nat)
    (hfst : ∀ w, (dec w).1 = w)
    (hneg : ∀ a, (negD dm a, (dec a).2.1 ^^^ mp, (dec a).2.2 ^^^ mp) = dec (negD dm a))
    (hbin : ∀ (c : Bool) a b,
      (if c then (if c then andD dm a b else orD dm a b, (dec a).2.1 &&& (dec b).2.1, (dec a).2.2 &&& (dec b).2.2)
       else (if c then andD dm a b else orD dm a b, (dec a).2.1 ||| (dec b).2.1, (dec a).2.2 ||| (dec b).2.2)) =
      dec (if c then andD dm a b else orD dm a b))
    (slack : Nat) (ws : List Nat) (g : List (Nat × Nat × Nat) → Bool) :
    nextD_decor dm mp slack (ws.map dec) g = nextD dm slack ws (fun zs => g (zs.map dec)) := by
  have hinj : Function.Injective dec := fun x y h => by rw [← hfst x, ← hfst y, h]
  have herase : ∀ (l : List Nat) x, (l.map dec).erase (dec x) = (l.erase x).map dec :=
    fun l x => erase_map_inj dec hinj l x
  have hcont : ∀ (l : List Nat) w, (l.map dec).any (fun x => x.1 == w) = l.contains w := by
    intro l w; apply Bool.eq_iff_iff.2; simp [hfst]
  unfold nextD_decor nextD
  simp only [List.any_map, Function.comp_def, hfst, herase, hcont, hneg, hbin, List.map_cons]

theorem nextD_decor_eq {dm : Nat} (hd : dm &&& mask256 = dm)
    (pairs : List (Nat × Nat))
    (hr1 : ∀ r ∈ pairs.map Prod.fst, dm.testBit r = true)
    (hr2 : ∀ r ∈ pairs.map Prod.snd, dm.testBit r = true)
    (slack : Nat) (ws : List Nat) (g : List (Nat × Nat × Nat) → Bool) :
    let dec := fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w)
    nextD_decor dm (maskP pairs.length) slack (ws.map dec) g =
      nextD dm slack ws (fun zs => g (zs.map dec)) := by
  intro dec
  apply nextD_decor_gen
  · intro w; rfl
  · intro a
    simp only [dec, projBit_negD hd hr1, projBit_negD hd hr2, List.length_map]
  · intro c a b
    cases c <;> simp only [dec, ↓reduceIte, Bool.false_eq_true, projBit_andD hr1, projBit_andD hr2,
      projBit_orD hr1, projBit_orD hr2]

def colB (mp : Nat) (d : Bool) (p : Nat × Nat) : Nat :=
  if d then (p.1 ^^^ mp) &&& p.2 else p.1 ^^^ p.2

def addC (x : Nat) (c : Nat × Nat × Nat) : Nat × Nat × Nat :=
  (c.1 ||| x, c.2.1 ||| (c.1 &&& x), c.2.2 ||| (c.2.1 &&& x))

def cov3 (mp : Nat) (d : Bool) (dws : List (Nat × Nat × Nat)) : Nat × Nat × Nat :=
  dws.foldl (fun c dw => addC (colB mp d dw.2) c) (0, 0, 0)

def takeOne (c : Nat × Nat × Nat) (x : Nat) : Nat := (c.1 ^^^ x) ||| c.2.1
def takeTwo (c : Nat × Nat × Nat) (x y : Nat) : Nat :=
  (c.1 ^^^ (x ||| y)) ||| (c.2.1 &&& (x ^^^ y)) ||| c.2.2

theorem cov3_bit (mp : Nat) (d : Bool) (dws : List (Nat × Nat × Nat)) (i : Nat) :
    let k := dws.countP (fun dw => (colB mp d dw.2).testBit i)
    (cov3 mp d dws).1.testBit i = decide (1 ≤ k) ∧
    (cov3 mp d dws).2.1.testBit i = decide (2 ≤ k) ∧
    (cov3 mp d dws).2.2.testBit i = decide (3 ≤ k) := by
  have hgen : ∀ (xs : List (Nat × Nat × Nat)) (c : Nat × Nat × Nat) (k0 : Nat),
      (c.1.testBit i = decide (1 ≤ k0) ∧ c.2.1.testBit i = decide (2 ≤ k0) ∧ c.2.2.testBit i = decide (3 ≤ k0)) →
      let k := k0 + xs.countP (fun dw => (colB mp d dw.2).testBit i)
      (xs.foldl (fun acc dw => addC (colB mp d dw.2) acc) c).1.testBit i = decide (1 ≤ k) ∧
      (xs.foldl (fun acc dw => addC (colB mp d dw.2) acc) c).2.1.testBit i = decide (2 ≤ k) ∧
      (xs.foldl (fun acc dw => addC (colB mp d dw.2) acc) c).2.2.testBit i = decide (3 ≤ k) := by
    intro xs
    induction xs with
    | nil => intro c k0 ⟨h1, h2, h3⟩; simp [h1, h2, h3]
    | cons dw xs ih =>
      intro c k0 ⟨h1, h2, h3⟩
      simp only [List.foldl_cons, List.countP_cons]
      have hc : (addC (colB mp d dw.2) c).1.testBit i =
            decide (1 ≤ k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) ∧
          (addC (colB mp d dw.2) c).2.1.testBit i =
            decide (2 ≤ k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) ∧
          (addC (colB mp d dw.2) c).2.2.testBit i =
            decide (3 ≤ k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) := by
        simp only [addC, Nat.testBit_or, Nat.testBit_and, h1, h2, h3]
        cases hb : (colB mp d dw.2).testBit i <;>
          rcases k0 with _ | _ | _ | k0 <;>
          simp [hb, Nat.le_add_left]
      have ih' := ih (addC (colB mp d dw.2) c) (k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) hc
      cases hb : (colB mp d dw.2).testBit i <;> simp only [hb, ↓reduceIte, Bool.false_eq_true, Nat.add_zero] at ih' ⊢
      · exact ih'
      · simpa only [Nat.add_assoc, Nat.add_comm 1] using ih'
  simpa only [cov3, Nat.zero_testBit, Nat.zero_add] using hgen dws (0, 0, 0) 0 (by simp)

theorem cov3_perm (mp : Nat) (d : Bool) {xs ys : List (Nat × Nat × Nat)} (p : xs.Perm ys) :
    cov3 mp d xs = cov3 mp d ys := by
  have heq : ∀ i, (cov3 mp d xs).1.testBit i = (cov3 mp d ys).1.testBit i ∧
      (cov3 mp d xs).2.1.testBit i = (cov3 mp d ys).2.1.testBit i ∧
      (cov3 mp d xs).2.2.testBit i = (cov3 mp d ys).2.2.testBit i := by
    intro i
    obtain ⟨a1, a2, a3⟩ := cov3_bit mp d xs i
    obtain ⟨b1, b2, b3⟩ := cov3_bit mp d ys i
    rw [p.countP_eq] at a1 a2 a3
    exact ⟨a1.trans b1.symm, a2.trans b2.symm, a3.trans b3.symm⟩
  apply Prod.ext
  · exact Nat.eq_of_testBit_eq (fun i => (heq i).1)
  · apply Prod.ext
    · exact Nat.eq_of_testBit_eq (fun i => (heq i).2.1)
    · exact Nat.eq_of_testBit_eq (fun i => (heq i).2.2)

theorem takeOne_eq (mp : Nat) (d : Bool) (a : Nat × Nat × Nat) (rest : List (Nat × Nat × Nat)) :
    takeOne (cov3 mp d (a :: rest)) (colB mp d a.2) = (cov3 mp d rest).1 := by
  apply Nat.eq_of_testBit_eq; intro i
  obtain ⟨h1, h2, _⟩ := cov3_bit mp d (a :: rest) i
  obtain ⟨r1, _, _⟩ := cov3_bit mp d rest i
  simp only [takeOne, Nat.testBit_or, Nat.testBit_xor, h1, h2, r1, List.countP_cons]
  set k := rest.countP (fun dw => (colB mp d dw.2).testBit i)
  cases ha : (colB mp d a.2).testBit i <;> simp only [ha, Bool.false_eq_true, ↓reduceIte] <;>
    rcases k with _ | _ | _ | k
  · decide
  · decide
  · decide
  · simp only [show 1 ≤ k + 3 by omega, show 2 ≤ k + 3 by omega, decide_true, Bool.xor_false, Bool.or_true]
  · decide
  · decide
  · decide
  · simp only [show 1 ≤ k + 3 + 1 by omega, show 2 ≤ k + 3 + 1 by omega, show 1 ≤ k + 3 by omega,
      decide_true, Bool.xor_true, Bool.or_true, Bool.or_false]

theorem takeTwo_eq (mp : Nat) (d : Bool) (a b : Nat × Nat × Nat) (rest : List (Nat × Nat × Nat)) :
    takeTwo (cov3 mp d (a :: b :: rest)) (colB mp d a.2) (colB mp d b.2) = (cov3 mp d rest).1 := by
  apply Nat.eq_of_testBit_eq; intro i
  obtain ⟨h1, h2, h3⟩ := cov3_bit mp d (a :: b :: rest) i
  obtain ⟨r1, _, _⟩ := cov3_bit mp d rest i
  simp only [takeTwo, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor, h1, h2, h3, r1, List.countP_cons]
  set k := rest.countP (fun dw => (colB mp d dw.2).testBit i)
  cases ha : (colB mp d a.2).testBit i <;> cases hb : (colB mp d b.2).testBit i <;>
    simp only [ha, hb, Bool.false_eq_true, ↓reduceIte] <;>
    rcases k with _ | _ | _ | k <;>
    (first | decide | simp only [
      show 1 ≤ k + 3 by omega, show 2 ≤ k + 3 by omega, show 3 ≤ k + 3 by omega,
      show 1 ≤ k + 3 + 1 by omega, show 2 ≤ k + 3 + 1 by omega, show 3 ≤ k + 3 + 1 by omega,
      show 1 ≤ k + 3 + 1 + 1 by omega, show 2 ≤ k + 3 + 1 + 1 by omega, show 3 ≤ k + 3 + 1 + 1 by omega,
      decide_true, Bool.xor_true, Bool.xor_false, Bool.or_true, Bool.or_false, Bool.and_true, Bool.and_false])

theorem cov3_coversD (mp s : Nat) (dw : Nat × Nat × Nat) (rest : List (Nat × Nat × Nat)) :
    let d := (dw :: rest).length == s + 1
    ((cov3 mp d rest).1 ||| colB mp d dw.2 == mp) = coversD mp s (dw :: rest) := by
  intro d
  have e : ∀ b : Bool, ((cov3 mp b rest).1 ||| colB mp b dw.2) =
      (dw :: rest).foldl (fun acc x => acc ||| colB mp b x.2) 0 := by
    intro b; apply Nat.eq_of_testBit_eq; intro i
    obtain ⟨h1, _, _⟩ := cov3_bit mp b rest i
    rw [foldl_or_testBit, Nat.zero_testBit, Bool.false_or, Nat.testBit_or, h1, List.any_cons]
    have hp : decide (1 ≤ rest.countP (fun dw => (colB mp b dw.2).testBit i)) =
        rest.any (fun x => (colB mp b x.2).testBit i) := by
      rw [Bool.eq_iff_iff, decide_eq_true_eq, Nat.succ_le_iff, List.countP_pos_iff, List.any_eq_true]
    rw [hp, Bool.or_comm]
  have hf : ∀ b : Bool, (cov3 mp b rest).1 ||| colB mp b dw.2 =
      (dw :: rest).foldl (fun acc x => acc ||| (if b then (x.2.1 ^^^ mp) &&& x.2.2 else x.2.1 ^^^ x.2.2)) 0 := by
    intro b; simpa only [colB] using e b
  unfold coversD
  dsimp only [d]
  cases (dw :: rest).length == s + 1
  · simpa only [Bool.false_eq_true, ↓reduceIte] using congrArg (· == mp) (hf false)
  · simpa only [↓reduceIte] using congrArg (· == mp) (hf true)

def nextD_cov (dm mp s slack : Nat) (dws : List (Nat × Nat × Nat))
    (f : List (Nat × Nat × Nat) → Bool) : Bool :=
  let len := dws.length
  let covF := cov3 mp false dws
  let covT := cov3 mp true dws
  let du0 := len == s + 1
  let du1 := len + 1 == s + 1
  let db0 := len - 1 == s + 1
  let db1 := len == s + 1
  let db2 := len + 1 == s + 1
  dws.any fun da =>
    let a := da.1
    (slack ≥ 1 &&
      (let pneg := (da.2.1 ^^^ mp, da.2.2 ^^^ mp)
       let uok0 := (takeOne (if du0 then covT else covF) (colB mp du0 da.2) ||| colB mp du0 pneg) == mp
       let uok1 := slack ≥ 2 && (((if du1 then covT.1 else covF.1) ||| colB mp du1 pneg) == mp)
       (uok0 || uok1) &&
       (let w := negD dm a
        w != 0 && w != dm && !(dws.any (fun x => x.1 == w)) &&
          let dw := (w, pneg)
          let ra := dws.erase da
          ((uok0 && f (dw :: ra)) || (uok1 && f (dw :: da :: ra)))))) ||
    (dws.erase da).any fun db =>
      let b := db.1
      a ≤ b &&
        [false, true].any fun conj =>
          let pz := if conj then (da.2.1 &&& db.2.1, da.2.2 &&& db.2.2)
                    else (da.2.1 ||| db.2.1, da.2.2 ||| db.2.2)
          let ok0 := (takeTwo (if db0 then covT else covF) (colB mp db0 da.2) (colB mp db0 db.2) ||| colB mp db0 pz) == mp
          let ok1a := slack ≥ 1 && ((takeOne (if db1 then covT else covF) (colB mp db1 db.2) ||| colB mp db1 pz) == mp)
          let ok1b := slack ≥ 1 && ((takeOne (if db1 then covT else covF) (colB mp db1 da.2) ||| colB mp db1 pz) == mp)
          let ok2 := slack ≥ 2 && (((if db2 then covT.1 else covF.1) ||| colB mp db2 pz) == mp)
          (ok0 || ok1a || ok1b || ok2) &&
          (let w := if conj then andD dm a b else orD dm a b
           w != 0 && w != dm && !(dws.any (fun x => x.1 == w)) &&
             let dw := (w, pz)
             let r := (dws.erase da).erase db
             ((ok0 && f (dw :: r)) || (ok1a && f (dw :: da :: r)) || (ok1b && f (dw :: db :: r)) || (ok2 && f (dw :: da :: db :: r))))

theorem nextD_cov_eq (dm mp s slack : Nat) (dws : List (Nat × Nat × Nat))
    (g : List (Nat × Nat × Nat) → Bool) :
    nextD_cov dm mp s slack dws g =
      nextD_decor dm mp slack dws (fun dzs => coversD mp s dzs && g dzs) := by
  unfold nextD_cov nextD_decor
  dsimp only
  apply Bool.eq_iff_iff.2; simp only [List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨da, hda, hrest⟩
    refine ⟨da, hda, ?_⟩
    rcases hrest with ⟨hsl, _, ⟨⟨hw0, hwdm⟩, hnw⟩, hfx⟩ | ⟨db, hdb, hab, conj, hcj, _, ⟨⟨hw0, hwdm⟩, hnw⟩, hfx⟩
    · left
      refine ⟨hsl, ⟨⟨hw0, hwdm⟩, hnw⟩, ?_⟩
      set dw := (negD dm da.1, da.2.1 ^^^ mp, da.2.2 ^^^ mp)
      set ra := dws.erase da
      have hp : dws.Perm (da :: ra) := List.perm_cons_erase hda
      have hcov0 : ((takeOne (if dws.length == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length == s + 1) da.2) ||| colB mp (dws.length == s + 1) (da.2.1 ^^^ mp, da.2.2 ^^^ mp)) == mp) =
          coversD mp s (dw :: ra) := by
        have hl : (dw :: ra).length = dws.length := by simp [hp.length_eq]
        have hc : ∀ d, cov3 mp d dws = cov3 mp d (da :: ra) := fun d => cov3_perm mp d hp
        have hc0 := cov3_coversD mp s dw ra
        rw [hl] at hc0
        cases hd : (dws.length == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hc0 ⊢
        · rw [hc false, takeOne_eq, hc0]
        · rw [hc true, takeOne_eq, hc0]
      have hcov1 :
          (((if dws.length + 1 == s + 1 then (cov3 mp true dws).1 else (cov3 mp false dws).1) |||
            colB mp (dws.length + 1 == s + 1) (da.2.1 ^^^ mp, da.2.2 ^^^ mp)) == mp) =
          coversD mp s (dw :: da :: ra) := by
        have hl : (dw :: da :: ra).length = dws.length + 1 := by simp [hp.length_eq]
        have hc : ∀ d, cov3 mp d dws = cov3 mp d (da :: ra) := fun d => cov3_perm mp d hp
        have hc1 := cov3_coversD mp s dw (da :: ra)
        rw [hl] at hc1
        cases hd : (dws.length + 1 == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hc1 ⊢
        · rw [hc false, hc1]
        · rw [hc true, hc1]
      rcases hfx with ⟨hu0, hf0⟩ | ⟨⟨hsl2, hu1⟩, hf1⟩
      · left; exact ⟨hcov0 ▸ hu0, hf0⟩
      · right; exact ⟨hsl2, hcov1 ▸ hu1, hf1⟩
    · right
      refine ⟨db, hdb, hab, conj, hcj, ⟨⟨hw0, hwdm⟩, hnw⟩, ?_⟩
      set pz := if conj then (da.2.1 &&& db.2.1, da.2.2 &&& db.2.2) else (da.2.1 ||| db.2.1, da.2.2 ||| db.2.2)
      set w := if conj then andD dm da.1 db.1 else orD dm da.1 db.1
      set dw := (w, pz)
      have hdw : (if conj = true then (w, da.2.1 &&& db.2.1, da.2.2 &&& db.2.2)
                  else (w, da.2.1 ||| db.2.1, da.2.2 ||| db.2.2)) = dw := by cases conj <;> rfl
      simp only [hdw]
      set ra := dws.erase da
      set r := ra.erase db
      have hp : dws.Perm (da :: db :: r) := (List.perm_cons_erase hda).trans (List.Perm.cons _ (List.perm_cons_erase hdb))
      have hlen_r : (dw :: r).length = dws.length - 1 := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hlen_a : (dw :: da :: r).length = dws.length := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hlen_b : (dw :: db :: r).length = dws.length := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hlen_ab : (dw :: da :: db :: r).length = dws.length + 1 := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hc2 : ∀ d, cov3 mp d dws = cov3 mp d (da :: db :: r) := fun d => cov3_perm mp d hp
      have hcov0 := cov3_coversD mp s dw r
      rw [hlen_r] at hcov0
      have hcov0' : ((takeTwo (if dws.length - 1 == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length - 1 == s + 1) da.2) (colB mp (dws.length - 1 == s + 1) db.2) |||
          colB mp (dws.length - 1 == s + 1) pz) == mp) = coversD mp s (dw :: r) := by
        cases hd : (dws.length - 1 == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov0 ⊢
        · rw [hc2 false, takeTwo_eq, hcov0]
        · rw [hc2 true, takeTwo_eq, hcov0]
      have hc_a : ∀ d, cov3 mp d dws = cov3 mp d (db :: da :: r) :=
        fun d => cov3_perm mp d (hp.trans (List.Perm.swap _ _ _))
      have hcov1a := cov3_coversD mp s dw (da :: r)
      rw [hlen_a] at hcov1a
      have hcov1a' : ((takeOne (if dws.length == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length == s + 1) db.2) ||| colB mp (dws.length == s + 1) pz) == mp) = coversD mp s (dw :: da :: r) := by
        cases hd : (dws.length == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov1a ⊢
        · rw [hc_a false, takeOne_eq, hcov1a]
        · rw [hc_a true, takeOne_eq, hcov1a]
      have hcov1b := cov3_coversD mp s dw (db :: r)
      rw [hlen_b] at hcov1b
      have hcov1b' : ((takeOne (if dws.length == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length == s + 1) da.2) ||| colB mp (dws.length == s + 1) pz) == mp) = coversD mp s (dw :: db :: r) := by
        cases hd : (dws.length == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov1b ⊢
        · rw [hc2 false, takeOne_eq, hcov1b]
        · rw [hc2 true, takeOne_eq, hcov1b]
      have hcov2 := cov3_coversD mp s dw (da :: db :: r)
      rw [hlen_ab] at hcov2
      have hcov2' : (((if dws.length + 1 == s + 1 then (cov3 mp true dws).1 else (cov3 mp false dws).1) |||
          colB mp (dws.length + 1 == s + 1) pz) == mp) = coversD mp s (dw :: da :: db :: r) := by
        cases hd : (dws.length + 1 == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov2 ⊢
        · rw [hc2 false, hcov2]
        · rw [hc2 true, hcov2]
      rcases hfx with ((⟨hu0, hf0⟩ | ⟨⟨hsl1, hu1a⟩, hf1a⟩) | ⟨⟨hsl1, hu1b⟩, hf1b⟩) | ⟨⟨hsl2, hu2⟩, hf2⟩
      · left; left; exact ⟨hcov0' ▸ hu0, hf0⟩
      · left; right; exact ⟨hsl1, Or.inl ⟨hcov1a' ▸ hu1a, hf1a⟩⟩
      · left; right; exact ⟨hsl1, Or.inr ⟨hcov1b' ▸ hu1b, hf1b⟩⟩
      · right; exact ⟨hsl2, hcov2' ▸ hu2, hf2⟩
  · rintro ⟨da, hda, hrest⟩
    refine ⟨da, hda, ?_⟩
    rcases hrest with ⟨hsl, ⟨⟨hw0, hwdm⟩, hnw⟩, hfx⟩ | ⟨db, hdb, hab, conj, hcj, ⟨⟨hw0, hwdm⟩, hnw⟩, hfx⟩
    · left
      set dw := (negD dm da.1, da.2.1 ^^^ mp, da.2.2 ^^^ mp)
      set ra := dws.erase da
      have hp : dws.Perm (da :: ra) := List.perm_cons_erase hda
      have hcov0 : ((takeOne (if dws.length == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length == s + 1) da.2) ||| colB mp (dws.length == s + 1) (da.2.1 ^^^ mp, da.2.2 ^^^ mp)) == mp) =
          coversD mp s (dw :: ra) := by
        have hl : (dw :: ra).length = dws.length := by simp [hp.length_eq]
        have hc : ∀ d, cov3 mp d dws = cov3 mp d (da :: ra) := fun d => cov3_perm mp d hp
        have hc0 := cov3_coversD mp s dw ra; rw [hl] at hc0
        cases hd : (dws.length == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hc0 ⊢
        · rw [hc false, takeOne_eq, hc0]
        · rw [hc true, takeOne_eq, hc0]
      have hcov1 : (((if dws.length + 1 == s + 1 then (cov3 mp true dws).1 else (cov3 mp false dws).1) |||
            colB mp (dws.length + 1 == s + 1) (da.2.1 ^^^ mp, da.2.2 ^^^ mp)) == mp) =
          coversD mp s (dw :: da :: ra) := by
        have hl : (dw :: da :: ra).length = dws.length + 1 := by simp [hp.length_eq]
        have hc : ∀ d, cov3 mp d dws = cov3 mp d (da :: ra) := fun d => cov3_perm mp d hp
        have hc1 := cov3_coversD mp s dw (da :: ra); rw [hl] at hc1
        cases hd : (dws.length + 1 == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hc1 ⊢
        · rw [hc false, hc1]
        · rw [hc true, hc1]
      rcases hfx with ⟨hc0, hg0⟩ | ⟨hsl2, hc1, hg1⟩
      · have hu0 : ((takeOne _ _ ||| _) == mp) = true := hcov0.symm ▸ hc0
        exact ⟨hsl, Or.inl hu0, ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inl ⟨hu0, hg0⟩⟩
      · have hu1 : ((_ ||| _) == mp) = true := hcov1.symm ▸ hc1
        exact ⟨hsl, Or.inr ⟨hsl2, hu1⟩, ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inr ⟨⟨hsl2, hu1⟩, hg1⟩⟩
    · right
      refine ⟨db, hdb, hab, conj, hcj, ?_⟩
      set pz := if conj then (da.2.1 &&& db.2.1, da.2.2 &&& db.2.2) else (da.2.1 ||| db.2.1, da.2.2 ||| db.2.2)
      set w := if conj then andD dm da.1 db.1 else orD dm da.1 db.1
      set dw := (w, pz)
      have hdw : (if conj = true then (w, da.2.1 &&& db.2.1, da.2.2 &&& db.2.2)
                  else (w, da.2.1 ||| db.2.1, da.2.2 ||| db.2.2)) = dw := by cases conj <;> rfl
      simp only [hdw] at hfx
      set ra := dws.erase da
      set r := ra.erase db
      have hp : dws.Perm (da :: db :: r) := (List.perm_cons_erase hda).trans (List.Perm.cons _ (List.perm_cons_erase hdb))
      have hlen_r : (dw :: r).length = dws.length - 1 := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hlen_a : (dw :: da :: r).length = dws.length := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hlen_b : (dw :: db :: r).length = dws.length := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hlen_ab : (dw :: da :: db :: r).length = dws.length + 1 := by
        have := hp.length_eq; simp only [List.length_cons] at this ⊢; omega
      have hc2 : ∀ d, cov3 mp d dws = cov3 mp d (da :: db :: r) := fun d => cov3_perm mp d hp
      have hcov0 := cov3_coversD mp s dw r; rw [hlen_r] at hcov0
      have hcov0' : ((takeTwo (if dws.length - 1 == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length - 1 == s + 1) da.2) (colB mp (dws.length - 1 == s + 1) db.2) |||
          colB mp (dws.length - 1 == s + 1) pz) == mp) = coversD mp s (dw :: r) := by
        cases hd : (dws.length - 1 == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov0 ⊢
        · rw [hc2 false, takeTwo_eq, hcov0]
        · rw [hc2 true, takeTwo_eq, hcov0]
      have hc_a : ∀ d, cov3 mp d dws = cov3 mp d (db :: da :: r) :=
        fun d => cov3_perm mp d (hp.trans (List.Perm.swap _ _ _))
      have hcov1a := cov3_coversD mp s dw (da :: r); rw [hlen_a] at hcov1a
      have hcov1a' : ((takeOne (if dws.length == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length == s + 1) db.2) ||| colB mp (dws.length == s + 1) pz) == mp) = coversD mp s (dw :: da :: r) := by
        cases hd : (dws.length == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov1a ⊢
        · rw [hc_a false, takeOne_eq, hcov1a]
        · rw [hc_a true, takeOne_eq, hcov1a]
      have hcov1b := cov3_coversD mp s dw (db :: r); rw [hlen_b] at hcov1b
      have hcov1b' : ((takeOne (if dws.length == s + 1 then cov3 mp true dws else cov3 mp false dws)
          (colB mp (dws.length == s + 1) da.2) ||| colB mp (dws.length == s + 1) pz) == mp) = coversD mp s (dw :: db :: r) := by
        cases hd : (dws.length == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov1b ⊢
        · rw [hc2 false, takeOne_eq, hcov1b]
        · rw [hc2 true, takeOne_eq, hcov1b]
      have hcov2 := cov3_coversD mp s dw (da :: db :: r); rw [hlen_ab] at hcov2
      have hcov2' : (((if dws.length + 1 == s + 1 then (cov3 mp true dws).1 else (cov3 mp false dws).1) |||
          colB mp (dws.length + 1 == s + 1) pz) == mp) = coversD mp s (dw :: da :: db :: r) := by
        cases hd : (dws.length + 1 == s + 1) <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at hcov2 ⊢
        · rw [hc2 false, hcov2]
        · rw [hc2 true, hcov2]
      rcases hfx with (⟨hc0, hg0⟩ | ⟨hsl1, ⟨hc1a, hg1a⟩ | ⟨hc1b, hg1b⟩⟩) | ⟨hsl2, hc2', hg2⟩
      · have u0 : ((takeTwo _ _ _ ||| _) == mp) = true := hcov0'.symm ▸ hc0
        exact ⟨Or.inl (Or.inl (Or.inl u0)), ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inl (Or.inl (Or.inl ⟨u0, hg0⟩))⟩
      · have u1a : ((takeOne _ _ ||| _) == mp) = true := hcov1a'.symm ▸ hc1a
        exact ⟨Or.inl (Or.inl (Or.inr ⟨hsl1, u1a⟩)), ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inl (Or.inl (Or.inr ⟨⟨hsl1, u1a⟩, hg1a⟩))⟩
      · have u1b : ((takeOne _ _ ||| _) == mp) = true := hcov1b'.symm ▸ hc1b
        exact ⟨Or.inl (Or.inr ⟨hsl1, u1b⟩), ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inl (Or.inr ⟨⟨hsl1, u1b⟩, hg1b⟩)⟩
      · have u2 : ((_ ||| _) == mp) = true := hcov2'.symm ▸ hc2'
        exact ⟨Or.inr ⟨hsl2, u2⟩, ⟨⟨hw0, hwdm⟩, hnw⟩, Or.inr ⟨⟨hsl2, u2⟩, hg2⟩⟩

def bar (dm Y : Nat) (pairs : List (Nat × Nat)) (r1s r2s : List Nat) (mp : Nat)
    (SD : Nat → Nat → List (Nat × Nat × Nat)) (S : Nat → Nat → List Nat)
    (N : Nat → Nat) (htAt idxH : Nat → Nat → Nat)
    (ori : List Nat → List Nat) (seed : Nat) (pool : List Nat) (cutHitH : Nat → Nat → List Nat → Bool) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [Y])
  | s + 1, i =>
    let dws := SD (s + 1) i
    !(nextD_cov dm mp s (s + 2 - dws.length) dws fun dzs =>
        let zs := dzs.map Prod.fst
        !(scr dm Y s pool zs) &&
        (let cz := ori zs
         let h := hk seed cz
         !(cutHitH s h cz) && !(foundH S N htAt idxH s h cz)))

theorem bar_all {dm T : Nat} {pairs r1s r2s mp SD S N htAt idxH ori seed pool cutHitH cap}
    (hd : dm &&& mask256 = dm)
    (hr1_eq : r1s = pairs.map Prod.fst) (hr2_eq : r2s = pairs.map Prod.snd) (hmp_eq : mp = maskP pairs.length)
    (hSD : ∀ s j, SD s j = (S s j).map (fun w => (w, projBit r1s w, projBit r2s w)))
    (hpairs : pairs.all (fun p => dm.testBit p.1 && dm.testBit p.2 && !(T &&& dm).testBit p.1 && (T &&& dm).testBit p.2) = true)
    (hr : ∀ {u ys}, RunD dm (T &&& dm) u ys → RunD dm (T &&& dm) u (ori ys))
    (hcut : ∀ {u ys}, cutHitH u (hk seed ys) ys = true → ¬ RunD dm (T &&& dm) u ys)
    (hc : ∀ s ≤ cap, ∀ i < N s, bar dm (T &&& dm) pairs r1s r2s mp SD S N htAt idxH ori seed pool cutHitH s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ RunD dm (T &&& dm) s (S s i) := by
  subst hr1_eq hr2_eq hmp_eq
  have hr1 : ∀ r ∈ pairs.map Prod.fst, dm.testBit r = true := by
    intro r hr'; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr'
    have h := List.all_eq_true.1 hpairs p hp; simp only [Bool.and_eq_true] at h; exact h.1.1.1
  have hr2 : ∀ r ∈ pairs.map Prod.snd, dm.testBit r = true := by
    intro r hr'; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr'
    have h := List.all_eq_true.1 hpairs p hp; simp only [Bool.and_eq_true] at h; exact h.1.1.2
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    have hb := hc s hs i hi
    cases s with
    | zero => simp [bar, zero_done hh rfl] at hb
    | succ s =>
      by_contra! hn
      let F (zs : List Nat) :=
        coversP pairs s zs && !(scr dm (T &&& dm) s pool zs) &&
        (let cz := ori zs
         let h := hk seed cz
         !(cutHitH s h cz) && !(foundH S N htAt idxH s h cz))
      have hF (zs) (hz : RunD dm (T &&& dm) s zs) : F zs = true := by
        have hcz := hr hz
        have hcutf : cutHitH s (hk seed (ori zs)) (ori zs) = false := by
          cases h : cutHitH s (hk seed (ori zs)) (ori zs) with
          | false => rfl
          | true => exact absurd hcz (hcut h)
        simp only [F, coversP_ok hd pairs hpairs hz, scr_no pool hz, hcutf, Bool.not_false, Bool.true_and, foundH]
        simp only [Bool.not_eq_true', Bool.and_eq_false_imp, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
        rintro ⟨hj, _⟩
        by_contra! hp
        have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
        exact ih s (by omega) (by omega) _ hj (Run.perm p hcz)
      have hN := nextD_complete hh s rfl _ (List.Perm.refl _) F hF
      dsimp only [bar] at hb
      rw [hSD, List.length_map, nextD_cov_eq, nextD_decor_eq hd pairs hr1 hr2] at hb
      have hFeq : (fun zs => coversD (maskP pairs.length) s (zs.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w))) &&
          (let zs' := (zs.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w))).map Prod.fst
           !(scr dm (T &&& dm) s pool zs') &&
           (let cz := ori zs'
            let h := hk seed cz
            !(cutHitH s h cz) && !(foundH S N htAt idxH s h cz)))) = F := by
        funext zs
        have hfst : (zs.map (fun w => (w, projBit (pairs.map Prod.fst) w, projBit (pairs.map Prod.snd) w))).map Prod.fst = zs := by
          simp [List.map_map, Function.comp_def]
        rw [coversD_eq, hfst]
        simp only [F, Bool.and_assoc]
      rw [hFeq, hN] at hb
      contradiction

def pickMin (seed : Nat) (orig : List Nat) : List (List (Nat × Nat)) → List Nat → Nat → List Nat
  | [], best, _ => best
  | ms :: rest, best, bestH =>
    let img := orig.map (applyMoves ms)
    let h := hk seed img
    if h < bestH then pickMin seed orig rest img h else pickMin seed orig rest best bestH

theorem pickMin_runD {dm Y u} (seed : Nat) (orig : List Nat) (h0 : RunD dm Y u orig) :
    ∀ (syms : List (List (Nat × Nat))) (best : List Nat) (bestH : Nat),
      syms.all (fun ms => ms.all moveOK256 && (applyMoves ms dm == dm) && (applyMoves ms Y == Y)) = true →
      RunD dm Y u best →
      RunD dm Y u (pickMin seed orig syms best bestH)
  | [], _, _, _, hb => hb
  | ms :: rest, best, bestH, hok, hb => by
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at hok
    unfold pickMin; dsimp only; split
    · exact pickMin_runD seed orig h0 rest _ _ hok.2 (applyMoves_runD ms hok.1.1.1 hok.1.1.2 hok.1.2 h0)
    · exact pickMin_runD seed orig h0 rest best bestH hok.2 hb

-- Bridge: HasCircuitSize 8 fG s -> Lower mask256 xs256 (enc256 fG) lb -> lb <= s!
def gvN (w : List Nat) (g : Gate) : Nat :=
  match g.op with
  | .and => g.inputs.foldr (fun i acc => andD mask256 (w.getD i 0) acc) mask256
  | .or  => g.inputs.foldr (fun i acc => orD mask256 (w.getD i 0) acc) 0
  | .not => match g.inputs with | [] => mask256 | i :: _ => negD mask256 (w.getD i 0)
  | _ => 0

def execN (gs : List Gate) (w : List Nat) : List Nat :=
  gs.foldl (fun l g => l ++ [gvN l g]) w

theorem gvN_bit (w : List Nat) (g : Gate) (r : Nat) (hr : r < 256)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    (gvN w g).testBit r = g.op.eval (g.inputs.map fun i => (w.map (·.testBit r)).getD i false) := by
  have hm : mask256.testBit r = true := by simp [mask256_bit, hr]
  have hgd : ∀ i, (w.map (·.testBit r)).getD i false = (w.getD i 0).testBit r := by
    intro i; simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases w[i]? with | none => simp | some v => rfl
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with h | h | h
  · simp only [gvN, GateOp.eval, h]
    induction g.inputs with
    | nil => simp [hm]
    | cons i l ih =>
      rw [List.foldr_cons, List.map_cons, List.all_cons, id_eq, andD, Nat.testBit_and, Nat.testBit_and, hm, Bool.and_true, hgd, ih]
  · simp only [gvN, GateOp.eval, h]
    induction g.inputs with
    | nil => simp
    | cons i l ih =>
      rw [List.foldr_cons, List.map_cons, List.any_cons, id_eq, orD, Nat.testBit_and, Nat.testBit_or, hm, Bool.and_true, hgd, ih]
  · simp only [gvN, GateOp.eval, h]
    cases g.inputs with
    | nil => simp [hm]
    | cons i l => simp only [List.map_cons, List.headD_cons, negD, Nat.testBit_and, Nat.testBit_xor, hm, Bool.and_true, Bool.xor_true, hgd]

theorem execN_bit (gs : List Gate) (w : List Nat) (r : Nat) (hr : r < 256)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    (execN gs w).map (·.testBit r) =
      gs.foldl (fun l g => l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)]) (w.map (·.testBit r)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [execN, List.foldl_cons] at ih ⊢
    rw [ih _ (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg'))]
    simp [gvN_bit w g r hr (hfan g List.mem_cons_self)]

theorem execN_reach (gs : List Gate) (roots : List Nat)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ (p : Nat) (w bank : List Nat), NatReach mask256 roots p bank →
      (∀ v ∈ w, Avail mask256 bank v) →
      ∃ p' bank', p' ≤ p + gs.length ∧ NatReach mask256 roots p' bank' ∧
        ∀ v ∈ execN gs w, Avail mask256 bank' v := by
  induction gs with
  | nil => intro p w bank hr hsup; exact ⟨p, bank, by omega, hr, hsup⟩
  | cons g gs ih =>
    intro p w bank hr hsup
    have hav_gd : ∀ i, Avail mask256 bank (w.getD i 0) := by
      intro i; by_cases hi : i < w.length
      · exact hsup _ (getD_mem hi)
      · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
    -- Use gvN_step directly on roots=roots:
    have hstep : ∃ p1 bank1, p1 ≤ p + 1 ∧ NatReach mask256 roots p1 bank1 ∧
        (∀ v ∈ w ++ [gvN w g], Avail mask256 bank1 v) := by
      have hg := hfan g List.mem_cons_self
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      obtain ⟨hop, hlen⟩ := hg
      have hand_m : ∀ a, andD mask256 a mask256 &&& mask256 = a &&& mask256 := fun a => by
        simp [andD, Nat.and_assoc, Nat.and_self]
      have hor_0 : ∀ a, orD mask256 a 0 &&& mask256 = a &&& mask256 := fun a => by
        simp [orD, Nat.and_assoc, Nat.and_self]
      have lift_w : ∀ z, (∀ v ∈ w, Avail mask256 (z :: bank) v) := fun z v hv => avail_cons z v (hsup v hv)
      rcases hop with h | h | h
      · rcases hgi : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨k, l⟩⟩⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inr (by simp [gvN, h, hgi]))⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi, List.foldr_cons, List.foldr_nil]
              exact avail_of_eq (hand_m _).symm (hav_gd i)⟩
        · refine ⟨p + 1, binD mask256 false (w.getD i 0) (w.getD j 0) :: bank, le_rfl,
            Or.inr ⟨bank, _, _, false, rfl, hr, hav_gd i, hav_gd j⟩, fun v hv => ?_⟩
          rcases List.mem_append.1 hv with hv | hv; · exact lift_w _ v hv
          · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi, List.foldr_cons, List.foldr_nil]
            exact Or.inr ⟨_, List.mem_cons_self, by simp [binD, andD, Nat.and_assoc, Nat.and_self]⟩
        · rw [hgi] at hlen; simp at hlen
      · rcases hgi : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨k, l⟩⟩⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inl (by simp [gvN, h, hgi]))⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi, List.foldr_cons, List.foldr_nil]
              exact avail_of_eq (hor_0 _).symm (hav_gd i)⟩
        · refine ⟨p + 1, binD mask256 true (w.getD i 0) (w.getD j 0) :: bank, le_rfl,
            Or.inr ⟨bank, _, _, true, rfl, hr, hav_gd i, hav_gd j⟩, fun v hv => ?_⟩
          rcases List.mem_append.1 hv with hv | hv; · exact lift_w _ v hv
          · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi, List.foldr_cons, List.foldr_nil]
            exact Or.inr ⟨_, List.mem_cons_self, by apply Nat.eq_of_testBit_eq; intro r; simp [binD, orD]; cases mask256.testBit r <;> simp⟩
        · rw [hgi] at hlen; simp at hlen
      · rcases hgi : g.inputs with _ | ⟨i, l⟩
        · exact ⟨p, bank, by omega, hr, fun v hv => by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inr (by simp [gvN, h, hgi]))⟩
        · refine ⟨p + 1, negD mask256 (w.getD i 0) :: bank, le_rfl,
            Or.inl ⟨bank, _, rfl, hr, hav_gd i⟩, fun v hv => ?_⟩
          rcases List.mem_append.1 hv with hv | hv; · exact lift_w _ v hv
          · rw [List.mem_singleton.1 hv]; simp only [gvN, h, hgi]; exact Or.inr ⟨_, List.mem_cons_self, rfl⟩
    obtain ⟨p1, bank1, hp1, hr1, hsup1⟩ := hstep
    obtain ⟨p2, bank2, hp2, hr2, hsup2⟩ := ih (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg')) p1 _ bank1 hr1 hsup1
    exact ⟨p2, bank2, by simp; omega, hr2, hsup2⟩

def xs256 : List Nat :=
  [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
   0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,
   0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
   0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,
   0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,
   0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,
   0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,
   0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]

def pt8 (r : Nat) : Fin 8 → Bool := fun i => r.testBit i.val

theorem xs256_bits : ∀ r : Fin 256, xs256.map (·.testBit r.val) = List.ofFn (pt8 r.val) := by
  decide +kernel

theorem lower_to_circuit (f : (Fin 8 → Bool) → Bool) (T lb : Nat)
    (hT : ∀ r : Fin 256, T.testBit r.val = f (pt8 r.val))
    (hlow : Lower mask256 xs256 T lb) :
    ∀ t : ℕ, HasCircuitSize 8 f t → lb ≤ t := by
  rintro t ⟨C, hfan, hsz, hev⟩
  have hsup0 : ∀ v ∈ xs256, Avail mask256 xs256 v := fun v hv => Or.inr ⟨v, hv, rfl⟩
  obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach C.gates xs256 hfan 0 xs256 xs256 rfl hsup0
  have hout : (execN C.gates xs256).getD C.output 0 &&& mask256 = T &&& mask256 := by
    apply Nat.eq_of_testBit_eq; intro r
    rw [Nat.testBit_and, Nat.testBit_and, mask256_bit]
    by_cases hlt : r < 256
    · simp only [hlt, decide_true, Bool.and_true]
      have h1 := execN_bit C.gates xs256 r hlt (fun g hg => (hfan g hg).1)
      have h2 := congrArg (fun l => l.getD C.output false) h1
      rw [xs256_bits ⟨r, hlt⟩] at h2
      have hgd : ((execN C.gates xs256).map (·.testBit r)).getD C.output false =
          ((execN C.gates xs256).getD C.output 0).testBit r := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (execN C.gates xs256)[C.output]? with | none => simp | some v => rfl
      rw [hgd] at h2
      have h3 : (C.wires (List.ofFn (pt8 r))).getD C.output false = f (pt8 r) := hev (pt8 r)
      exact h2.trans (h3.trans (hT ⟨r, hlt⟩).symm)
    · simp [hlt]
  have hav_out : Avail mask256 bank ((execN C.gates xs256).getD C.output 0) := by
    by_cases hi : C.output < (execN C.gates xs256).length
    · exact hsup _ (getD_mem hi)
    · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
  have hL := hlow p bank hr (avail_of_eq hout hav_out)
  show lb ≤ t
  have : C.gates.length ≤ t := hsz
  omega

def dom_13 : Nat := 0x3333
def goal_13 : Nat := 0xfaa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0
def roots_13 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0]

def dom_19 : Nat := 0xf000f
def goal_19 : Nat := 0xeeee8888eeee8888eeee8888eeee8888eeee8888eeee8888eeee8888eeee8888
def roots_19 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0]

def dom_25 : Nat := 0x3030303
def goal_25 : Nat := 0xffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00
def roots_25 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_35 : Nat := 0xf0000000f
def goal_35 : Nat := 0xeeeeeeee88888888eeeeeeee88888888eeeeeeee88888888eeeeeeee88888888
def roots_35 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0]

def dom_37 : Nat := 0x3300000033
def goal_37 : Nat := 0xfafafafaa0a0a0a0fafafafaa0a0a0a0fafafafaa0a0a0a0fafafafaa0a0a0a0
def roots_37 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 5 0]

def dom_15 : Nat := 0xffff
def goal_15 : Nat := 0xfaa8faa8faa8faa8faa8faa8faa8faa8faa8faa8faa8faa8faa8faa8faa8faa8
def roots_15 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0]

def dom_27 : Nat := 0xf0f0f0f
def goal_27 : Nat := 0xffeeaa88ffeeaa88ffeeaa88ffeeaa88ffeeaa88ffeeaa88ffeeaa88ffeeaa88
def roots_27 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_23 : Nat := 0xff00ff
def goal_23 : Nat := 0xeeeea8a8eeeea8a8eeeea8a8eeeea8a8eeeea8a8eeeea8a8eeeea8a8eeeea8a8
def roots_23 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0]

def dom_29 : Nat := 0x33333333
def goal_29 : Nat := 0xffaafaa0ffaafaa0ffaafaa0ffaafaa0ffaafaa0ffaafaa0ffaafaa0ffaafaa0
def roots_29 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_39 : Nat := 0xff000000ff
def goal_39 : Nat := 0xfefefefea8a8a8a8fefefefea8a8a8a8fefefefea8a8a8a8fefefefea8a8a8a8
def roots_39 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0]

def dom_43 : Nat := 0xf0f00000f0f
def goal_43 : Nat := 0xeeeeeeeeaa88aa88eeeeeeeeaa88aa88eeeeeeeeaa88aa88eeeeeeeeaa88aa88
def roots_43 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_45 : Nat := 0x333300003333
def goal_45 : Nat := 0xfafafafafaa0faa0fafafafafaa0faa0fafafafafaa0faa0fafafafafaa0faa0
def roots_45 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_51 : Nat := 0xf000f000f000f
def goal_51 : Nat := 0xeeeeeeeeeeee8888eeeeeeeeeeee8888eeeeeeeeeeee8888eeeeeeeeeeee8888
def roots_51 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_53 : Nat := 0x33003300330033
def goal_53 : Nat := 0xfafafafaaaaaa0a0fafafafaaaaaa0a0fafafafaaaaaa0a0fafafafaaaaaa0a0
def roots_53 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_57 : Nat := 0x303030303030303
def goal_57 : Nat := 0xffaaaaaaffaaaa00ffaaaaaaffaaaa00ffaaaaaaffaaaa00ffaaaaaaffaaaa00
def roots_57 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_31 : Nat := 0xffffffff
def goal_31 : Nat := 0xffeefaa8ffeefaa8ffeefaa8ffeefaa8ffeefaa8ffeefaa8ffeefaa8ffeefaa8
def roots_31 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_62 : Nat := 0x5555555555555555
def goal_62 : Nat := 0xfffcfcfcffccf000fffcfcfcffccf000fffcfcfcffccf000fffcfcfcffccf000
def roots_62 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_47 : Nat := 0xffff0000ffff
def goal_47 : Nat := 0xfefefefefaa8faa8fefefefefaa8faa8fefefefefaa8faa8fefefefefaa8faa8
def roots_47 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xfefefefeeeeea8a8fefefefeeeeea8a8fefefefeeeeea8a8fefefefeeeeea8a8
def roots_55 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xffeeeeeeffeeaa88ffeeeeeeffeeaa88ffeeeeeeffeeaa88ffeeeeeeffeeaa88
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_61 : Nat := 0x3333333333333333
def goal_61 : Nat := 0xfffafafaffaafaa0fffafafaffaafaa0fffafafaffaafaa0fffafafaffaafaa0
def roots_61 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xfffefefeffeefaa8fffefefeffeefaa8fffefefeffeefaa8fffefefeffeefaa8
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

namespace S_13
def pairsG : List (Nat × Nat) := [(1, 5), (1, 9), (4, 5), (4, 12), (8, 9), (8, 12)]
def r1sG : List Nat := [1, 1, 4, 4, 8, 8]
def r2sG : List Nat := [5, 9, 5, 12, 9, 12]
def mpG : Nat := 0x3f
def pool6G : List Nat := [4402476484869]
def xsM : List Nat := roots_13.map (· &&& dom_13)
def goalM : Nat := goal_13 &&& dom_13
def NN : Nat → Nat
  | 3 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xb9ef265f
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x330000000000000000000000000000000000000000000000000000000000000030300000000000000000000000000000000000000000000000000000000000002222
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x243
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 10
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 2 0) :: stateWires n (ids >>> 2)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x30000000000000000000000000000000000000000000000000000000000000000c0000000000000000000000000000000000000000000000000000000000000003
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3a000000000000000000000000000000000000000000000000000000000000002d0000000000000000000000000000000000000000000000000000000000000017
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 3 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 3 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 3 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 3 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 2 0) :: stateWiresD n (ids >>> 2)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 2 0) :: stateWiresS n (ids >>> 2)
def SD (s j : Nat) : List (Nat × Nat × Nat) :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAt (s i : Nat) : Nat := fld (HT s (i / 64)) 32 (i % 64)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 2 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat
  | _, _ => 0
def CV : Nat → Nat → Nat
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 1 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_13 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_13 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_13 == dom_13) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_13 goalM u ys) : RunD dom_13 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_13 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_13 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD dom_13 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by
    have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_13 roots_13 goal_13 4 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_13 goal_13 := by
    have h0 : isConstB dom_13 goal_13 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub
  have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq
    rw [hcov] at hbad; contradiction

end S_13

theorem low_13 : Lower dom_13 roots_13 goal_13 4 := S_13.noCircuit

def isoMv_19 : List (Nat × Nat) := [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem low_19 : Lower dom_19 roots_19 goal_19 4 :=
  lower_iso isoMv_19 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_13

def isoMv_25 : List (Nat × Nat) := [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)]
theorem low_25 : Lower dom_25 roots_25 goal_25 4 :=
  lower_iso isoMv_25 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_13

def isoMv_35 : List (Nat × Nat) := [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem low_35 : Lower dom_35 roots_35 goal_35 4 :=
  lower_iso isoMv_35 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_13

def isoMv_37 : List (Nat × Nat) := [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]
theorem low_37 : Lower dom_37 roots_37 goal_37 4 :=
  lower_iso isoMv_37 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_13

theorem low_15 : Lower dom_15 roots_15 goal_15 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xcccc, 1, 3)] (by decide +kernel) (by decide +kernel) low_13

theorem low_27 : Lower dom_27 roots_27 goal_27 5 :=
  lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [(0xc0c0c0c, 1, 3)] (by decide +kernel) (by decide +kernel) low_25

def isoMv_23 : List (Nat × Nat) := [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem low_23 : Lower dom_23 roots_23 goal_23 5 :=
  lower_iso isoMv_23 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15

def isoMv_29 : List (Nat × Nat) := [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem low_29 : Lower dom_29 roots_29 goal_29 5 :=
  lower_iso isoMv_29 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_27

def isoMv_39 : List (Nat × Nat) := [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]
theorem low_39 : Lower dom_39 roots_39 goal_39 5 :=
  lower_iso isoMv_39 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_27

def isoMv_43 : List (Nat × Nat) := [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem low_43 : Lower dom_43 roots_43 goal_43 5 :=
  lower_iso isoMv_43 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15

def isoMv_45 : List (Nat × Nat) := [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]
theorem low_45 : Lower dom_45 roots_45 goal_45 5 :=
  lower_iso isoMv_45 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_27

def isoMv_51 : List (Nat × Nat) := [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)]
theorem low_51 : Lower dom_51 roots_51 goal_51 5 :=
  lower_iso isoMv_51 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_27

def isoMv_53 : List (Nat × Nat) := [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)]
theorem low_53 : Lower dom_53 roots_53 goal_53 5 :=
  lower_iso isoMv_53 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15

def isoMv_57 : List (Nat × Nat) := [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)]
theorem low_57 : Lower dom_57 roots_57 goal_57 5 :=
  lower_iso isoMv_57 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15

namespace S_31
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (1, 9), (1, 17), (2, 3), (2, 18), (4, 5), (4, 12), (6, 7), (6, 14), (6, 22), (8, 9), (8, 12), (8, 24), (10, 11), (10, 14), (10, 26), (16, 17), (16, 18), (16, 24), (20, 21), (20, 22), (20, 28)]
def r1sG : List Nat := [1, 1, 1, 1, 2, 2, 4, 4, 6, 6, 6, 8, 8, 8, 10, 10, 10, 16, 16, 16, 20, 20, 20]
def r2sG : List Nat := [3, 5, 9, 17, 3, 18, 5, 12, 7, 14, 22, 9, 12, 24, 11, 14, 26, 17, 18, 24, 21, 22, 28]
def mpG : Nat := 0x7fffff
def pool6G : List Nat := [1125618159875, 1125449992453, 22016020251410, 11020903449868, 1142562751241]
def xsM : List Nat := roots_31.map (· &&& dom_31)
def goalM : Nat := goal_31 &&& dom_31
def NN : Nat → Nat
  | 5 => 1
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0x14e17f6b
  | 6, 0 => 0x1f16380d
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xaaaaaaaa00000000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000ff00ff0000000000000000000000000000000000000000000000000000000000f0f0f0f000000000000000000000000000000000000000000000000000000000cccccccc0000000000000000000000000000000000000000000000000000000055555555
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x46885
  | 6, 0, 0 => 0x468d5
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 19
  | 6 => 19
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 3 0) :: stateWires n (ids >>> 3)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xf00000000000000000000000000000000000000000000000000000000007e0000000000000000000000000000000000000000000000000000000000000001f80000000000000000000000000000000000000000000000000000000000007007c0000000000000000000000000000000000000000000000000000000000001c73000000000000000000000000000000000000000000000000000000000007ffff0
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x12495f00000000000000000000000000000000000000000000000000000000007f2428000000000000000000000000000000000000000000000000000000000049fa8400000000000000000000000000000000000000000000000000000000007097c2000000000000000000000000000000000000000000000000000000000025c73100000000000000000000000000000000000000000000000000000000006db6a0
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 6 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 6 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 6 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 6 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 3 0) :: stateWiresD n (ids >>> 3)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 3 0) :: stateWiresS n (ids >>> 3)
def SD (s j : Nat) : List (Nat × Nat × Nat) :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAt (s i : Nat) : Nat := fld (HT s (i / 64)) 32 (i % 64)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 2 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 5 => 4
  | _ => 0
def CH : Nat → Nat → Nat
  | 5, 0 => 0xb41bdfa3599be9b238e260a01f16380d
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 5, 0 => 0x2000000000000000000000000030000000000001
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 4 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_27 roots_27 5 s ws hint
  | 1 => checkCutEntry dom_29 roots_29 5 s ws hint
  | 2 => checkCutEntry dom_15 roots_15 5 s ws hint
  | 3 => checkCutEntry dom_23 roots_23 5 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_31 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_27 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_29 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_23 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_31 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_31 == dom_31) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_31 goalM u ys) : RunD dom_31 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_31 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
  · exact fun i hi => z6 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_31 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_31 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_31 roots_31 goal_31 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_31 goal_31 := by
    have h0 : isConstB dom_31 goal_31 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub
  have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq
    rw [hcov] at hbad; contradiction

end S_31

theorem low_31 : Lower dom_31 roots_31 goal_31 7 := S_31.noCircuit

namespace S_62
def pairsG : List (Nat × Nat) := [(2, 18), (2, 34), (4, 12), (4, 36), (6, 14), (6, 22), (6, 38), (8, 12), (8, 24), (10, 14), (10, 26), (10, 42), (16, 18), (16, 24), (20, 22), (20, 28), (20, 52), (32, 34), (32, 36), (40, 42), (40, 44), (40, 56), (48, 50), (48, 52), (48, 56)]
def r1sG : List Nat := [2, 2, 4, 4, 6, 6, 6, 8, 8, 10, 10, 10, 16, 16, 20, 20, 20, 32, 32, 40, 40, 40, 48, 48, 48]
def r2sG : List Nat := [18, 34, 12, 36, 14, 22, 38, 12, 24, 14, 26, 42, 18, 24, 22, 28, 52, 34, 36, 42, 44, 56, 50, 52, 56]
def mpG : Nat := 0x1ffffff
def pool6G : List Nat := [44067172128780, 22033284074520, 44006572823074, 44006404918308, 22016675682322]
def xsM : List Nat := roots_62.map (· &&& dom_62)
def goalM : Nat := goal_62 &&& dom_62
def NN : Nat → Nat
  | 5 => 2
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0x1a3d9d910c99170a
  | 6, 0 => 0xc99170a
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x5500550055005500000000000000000000000000000000000000000000000055555555000000000000000000000000000000000000000000000000000000005555000055550000000000000000000000000000000000000000000000000000550055005500550000000000000000000000000000000000000000000000000050505050505050500000000000000000000000000000000000000000000000004444444444444444
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x2322ac6885
  | 6, 0, 0 => 0x46885
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 19
  | 6 => 19
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 3 0) :: stateWires n (ids >>> 3)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x1c7f07f0000000000000000000000000000000000000000000000000000000001fe00000000000000000000000000000000000000000000000000000000000001c1f0000000000000000000000000000000000000000000000000000000000000380f80000000000000000000000000000000000000000000000000000000000001c07c0000000000000000000000000000000000000000000000000000000000000e73
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xc7506b0000000000000000000000000000000000000000000000000000000001ff084a0000000000000000000000000000000000000000000000000000000001e1f521000000000000000000000000000000000000000000000000000000000138af94000000000000000000000000000000000000000000000000000000000095c2fc00000000000000000000000000000000000000000000000000000000004a5e73
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 6 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 6 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 6 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 6 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 3 0) :: stateWiresD n (ids >>> 3)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 3 0) :: stateWiresS n (ids >>> 3)
def SD (s j : Nat) : List (Nat × Nat × Nat) :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAt (s i : Nat) : Nat := fld (HT s (i / 64)) 32 (i % 64)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 3 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | _ => 0
def CH : Nat → Nat → Nat
  | _, _ => 0
def CV : Nat → Nat → Nat
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 1 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_62 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_62 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_62 == dom_62) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_62 goalM u ys) : RunD dom_62 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_62 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i, 0 ≤ i → i < 2 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 2 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
  · exact fun i hi => z6 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_62 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_62 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_62 roots_62 goal_62 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_62 goal_62 := by
    have h0 : isConstB dom_62 goal_62 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub
  have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq
    rw [hcov] at hbad; contradiction

end S_62

theorem low_62 : Lower dom_62 roots_62 goal_62 7 := S_62.noCircuit

def isoMv_47 : List (Nat × Nat) := [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]
theorem low_47 : Lower dom_47 roots_47 goal_47 7 :=
  lower_iso isoMv_47 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_31

def isoMv_55 : List (Nat × Nat) := [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]
theorem low_55 : Lower dom_55 roots_55 goal_55 7 :=
  lower_iso isoMv_55 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_31

def isoMv_59 : List (Nat × Nat) := [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)]
theorem low_59 : Lower dom_59 roots_59 goal_59 7 :=
  lower_iso isoMv_59 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_31

def isoMv_61 : List (Nat × Nat) := [(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)]
theorem low_61 : Lower dom_61 roots_61 goal_61 7 :=
  lower_iso isoMv_61 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_31

namespace S_63
def pairsG : List (Nat × Nat) := [(1, 3), (1, 5), (1, 9), (1, 17), (1, 33), (2, 3), (2, 18), (2, 34), (4, 5), (4, 12), (4, 36), (6, 7), (6, 14), (6, 22), (6, 38), (8, 9), (8, 12), (8, 24), (10, 11), (10, 14), (10, 26), (10, 42), (16, 17), (16, 18), (16, 24), (20, 21), (20, 22), (20, 28), (20, 52), (32, 33), (32, 34), (32, 36), (40, 41), (40, 42), (40, 44), (40, 56), (48, 49), (48, 50), (48, 52), (48, 56)]
def r1sG : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 4, 4, 4, 6, 6, 6, 6, 8, 8, 8, 10, 10, 10, 10, 16, 16, 16, 20, 20, 20, 20, 32, 32, 32, 40, 40, 40, 40, 48, 48, 48, 48]
def r2sG : List Nat := [3, 5, 9, 17, 33, 3, 18, 34, 5, 12, 36, 7, 14, 22, 38, 9, 12, 24, 11, 14, 26, 42, 17, 18, 24, 21, 22, 28, 52, 33, 34, 36, 41, 42, 44, 56, 49, 50, 52, 56]
def mpG : Nat := 0xffffffffff
def pool6G : List Nat := [44067172128780, 1125618159875, 1271480320801, 1125449992453, 52819525699864, 52802665845282, 1186218643717, 52820181129234, 1185512817425, 11020903449868, 1306009011489, 52802346878244, 1142562751241, 1143134619907, 22033284074520, 1306342721809, 44006404918308, 22016020251410, 44006253855522, 1272117203209, 44023432676130, 44066381825304, 52819525698328, 44023752692258, 44066382350616, 44066383398180, 8882801353740, 1142798288131, 1125618418947, 52862627482660, 2405855533074, 22033990945036, 1103909626889, 1104143718403, 22016020252946, 1103975946245, 44066381825316, 11020903975180]
def xsM : List Nat := roots_63.map (· &&& dom_63)
def goalM : Nat := goal_63 &&& dom_63
def NN : Nat → Nat
  | 5 => 55
  | 6 => 248
  | 7 => 522
  | 8 => 146
  | 9 => 11
  | 10 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0xdf747f60a9ddfdc76eb3214269038bc55fa3c3655c9a367b58ac284155b6f0c94e52a7d04370ca5540ba5b353abe733938536db837a24b72364ed4763430e43832805eb3323a9b8231bd778d2f747ac52b5b84f0264306422538064a244ccc4522be606e1f11d30f1efa73dd1e64d4021a84b3891a3c3285195e22e115e4cf371500613f14acb86f1423bf600e5ebf580dbed4410da9de830d2349ca0c55b4270c3dfa730b3b397809aca34908f3b0ee08bce8f707ede7d106a23ef805a659ef057837f00506563104674300019074f700df2f260053fb77002fb5e6
  | 6, 0 => 0xeba320c0e2146200dcebac60da39ff50d7ff5950d56a8a00d3faa8e0d239a210d213aee0cf9cfce0cf03a770cd656920cc817910caedf080ca3b5de0c9f78540c9485630ba200f30b9ba5e70b45e8510ae2c9b70a8d5f380a85c5fe09fa4f09097f425509636a7f091987c608d7f62e08b6f5e50804782a07f0940f07be378e07b65170078f119f075218f50750b076073c0d4906e3c49e0694e74a068aa963060c738c05fcea2e0525b9a704ebb28c04d50ade04394601041bd56a039700010306024b026c6c0001c06322019a0d4d01920f54013248aa013160170116f07a0115bbb600f98fb200cda18300b7d23400a0e2de0070b0dc006a33af00598859
  | 6, 1 => 0x23a2798d23620fd7233004bc22f1c67422da472622143a7921b6266f218bddaa2112c5ad207e27b3201c965c1fd528dc1e1782331df1d91a1dc1a4da1dbecb4f1d948b6c1d4a39ee1d2d55d31c78fc451c4214131b9c6b311ad56e621a4661f419a4c68718f5aae118e357811870426017d03ea217b1715b17a19b701786a86116bd834f16b5fea7168fe8f3165c684c16597d231603466915ff171615ef68e515891687154488fa15319ff6149fd5ab13e50f3d13deddce135e65a913308af91230673012010f8111ef7e1e11ea3d2411bc82c911aafad5108dfb001047d2861041c8030ffd811d0fad79d40f6b3e1a0f1d5f8e0f1408940f12db0a0efd143c
  | 6, 2 => 0x47cc5f524674b52644b3d84941e085b641c38b7f41826078417a81cf3fead9ec3f620fee3f25fd303e7d0cf03dbad3cf3d69256c3d6089e83c4e908c3bd2c6a83bcbb2e73b36a74b3b050c113aded38e3ac8a78739efa32738f5c08d38cc926f388f117a37dfe0bd3747122337077a4236dd881e356bb79a3542f1fb34efc72c3490825e3434456e33d88edc33d1e4c433b9eedc31835c65302ba5682f422ef02eff5d632e0141282dff6efc2d676a9a2d1631b32c6b0b4a2c2d59f52bc7bccc2b41ecbc2af54b082a23370d29a772152981fc7227eed9c727017ce926fbd8cf26871db6258785ef2538064a252ad67924c2625e248274aa2475975124099f8f
  | 6, 3 => 0xa5e8478295aaf34393cf05898d54bf8189f5a01188fb14e484fccbd182d2ba4981edcbaf80ff70067d1446527c5be39e7bd4e92f7afe2d787a4bfcea78fa52ae726727cb6a6e859668b5f159689eda7667f8396a67e244ad65d9a5ee64dba370643eed1c63d527146333303162641829625429c760e0af5060a2a7735e33a9d55d9ef9a05d6449345c5049045c4f34145c0439a359df37c5599dec4b58dd2abc5738c89657151ed6564852af55b6f0c951c11cf950d3973b4cd1cab54bf1ebdb4b6882954af740144ac7e3654a3c8210492f7eb1486588bf48230709480a63c2
  | 7, 0 => 0x533fba60523a06c050cdc2205079cff04f5e95404cfcbb004b7811a0496165b0474d6a10446c582043d33b9041cbc31041767240414a8770408974203c61cd003b1e82a03ac249f03a0a63e0342ee7a0335143e0331cac6031c85c902f2e5b202db817802d338cd02c4fbd3027dd2a4026aed28025a493c025a06d30229321f0224028a01fd268701e9ecaa01dd076b01d838ff01c7bd4b01c0cf2f01bf50c301be086c01b60d15019fb52f0188bf720185e19d016d7b820169bc49015f401001271ba7010155d70101155700f26ece00c69bbc00bcc88900ae951800aa571900a8eff1009978f50091daa4007e6b570059d3fb003d62dd001528ba0010041b
  | 7, 1 => 0xb0ab8450afcab140a9cd3050a668a080a5db90d0a4a18090a4721420a43775b0a3a77c00a3643350a1c88f40a01adfb09dbbd9309bad191097f42550979a5d3095586ce093090f108f40b1b08e9797408e7e79d08da97c208cb9ce108c04d1d08ae6dda0895d519086df8bb08359101083381a50812e9d20805d13208028ac807f0940f07f028bf07dd4fa807d5316f07cb813407c64465079ce55907983db60770769c074a9e1907493bb1071ebcc6070b6e2706d1977a0674bcee0644efc80634607c0620bd3c06094b0a05ff187405f3a13e05d8d5fa05c6c8a205b2eac505ab6a7705aa94bf05a7c7630584bedf0573298d056af0ba0558271f0542e934
  | 7, 2 => 0x149a4ea1147ef8371460b592143930801425a526141f8fdd13ff4d9413fda56313b478a2138eec7e138bc72e133bd65513351fbd1332ca01132f6d15131fe96f130e3cd912e4a74a12d4145e1288b0461227f09d120feeaa11b98cfd1183b7ed115b2e171149f22210bfb418108dfb0010739a891073336b0fcf05c80fa349150f5e8c8c0f5d5bef0f4b6df20eeac9300ed51c0e0eb3ce750e5684bd0e4ce4f90df384db0dea00600de1f81f0dc02f8f0d52fdb80d4b6ee40d2f75e70d2562560d1a20270d16ec7b0cfdf2310cf96de80cf3454b0c76b2fc0c4feadd0c3025590c2d1daa0c2225300c1de1fe0c1b94cd0bdd5bdf0b9ee2060b7bd44a0b236e97
  | 7, 3 => 0x1eaf1d421e99e7201e82e74f1e4df89f1e10a1721df5c4f81df3a9141de93ccb1de5ae731de04d2a1daf8ff81da185e31d9ebe2f1d5b97f41d0839f91cec56da1c59b8491c1160c61b903cc61b8f4bc21b5aa7ce1b50f3c41b2750f31b1e11341ae554351a76b50e1a6d03dc1a2448241a11c01919f7a8a219ed676819d8d66d19d360661996d3a0191c880718fa400b18f7b2bb18b26e221893c351189270981877b407185ae160184a9daa181b6ec817ebe64817e17fa41783d36c1782dbd41769b9701747ce40171bcf5d1714a0de16a0d74d164cdf49162026971601e6a615e3d4b915a29c41159dc5ad151f94c7150c58971506cbab14d1b9a314b3ce6e
  | 7, 4 => 0x2aafe6892a71985b2a1fbbbc29ec033029d523c129cb7a7329c95011297cc0d4297400f829676491292cb8d4290c466228a5bcb428708577285a7d782807443f27e8f33927b43dd42780f8822773e4862730f4cd2707962226723f6725d07e9b259f1f6f2578e98625613c15255eaa50255cb14a24f4abb424f1d90e24e82e8e24df4c9e24927c11244c901023e4b7822371f15e23419c112331768c22abcb442284b333227d2b9e223ec96b21ea349621d6d25821883b57217fbd7e2161cccc214525f5210d82f720d1d0a420a9da742070a08e2059642220448ff3202b40b21ff874121fd910571fcf4aa11fcef5c61f415ead1ee037e11ed593121eb4212a
  | 7, 5 => 0x3d71fd593d68e4823cf4fcd73cafee803c9f81c53c43a1fe3bcc4b8e3b1437703b0d98e73a9cdd1a3a8e31643a48df3c3a1fbb5339f7320a38f9f1d0380acf4536f03f6536c90eb0368845d5366eb16e362ed30d3583222d355a85df35389f9734ae4d7b3456a4b43434456e3403b3df33f8b6f932aa415a328aacd0326889ca32681bf4324f851831c4e58f31b52cbf316e3c87315de65d3119d491311656bb3107d3ae303247ff302f8f9930108d352fa60ebd2f3679eb2ed106232ea605a32e9f17e82e80ed852e79a6882ded15fc2da2fbfc2cfd4cb22cc6b4a22cbfb75d2ca054372bdaea362b8991172b8962062b0c54332af160712ac5b9242abf74ef
  | 7, 6 => 0x5550ce975539a68b5522f61055073dee548cc5b55412a70454101d3f534c3a7b52f219fd52bc8da3521771ed520b52db50fece0850fc0177506f73194ef588884eaa869d4e5aaf8b4e2ff7f04e2e2ce84e022cb64dab360f4d8edfa44cd1cab54c69cffe4bf1bf454b685d854aee95694ac954934ac781234a241fda4954f821492ffa97486b9cc547b74cd347ae2d7e473a6d9246cd9c50464f4da14600690545da4cbe45d5b36a45b5059c454de4cd43f8662a43dc1dad43a70ae5424c63d041eec1fc4197cdb140429616400633023faa646c3f96f1e83f775e1d3f4d583b3e9bf4f73e6edb873e209aba3e118dd93e066e433dccbcab3dbce0d53dbc044b
  | 7, 7 => 0x89696dcd88c8f8608574e55284fccbd1827719248209a612819b4b0880fcaa617fda735e7cc2c9797c67cfb87c3f68397a39a61379f474e879e8d72b788c2ff5782718a176bbf7e375c5b47472eb0432727f37757223dad16edf7c9c6d72199c6d1ed6446c6b07056b504f2a6ac5e76669548d24690e76076904c44368f9245d689eda7668377a7467353b4c65af630c655c4e5a635f225d628562b16178d6cc612e0d7f5f31b6b85f16df6a5e8bce515e86d97f5e27b0bb5e278f0e5cb2738c5c31f5785be7e2d45b3983f85aca5d735a2b544f59cb464e58acce9758808bdb5874c9ef580aba225710d06856ac910056803d4a565e118d562ecd4155eaa365
  | 7, 8 => 0xae110ad79e08ec0a99eeacab957a19a9939c8143933689f88e9d72eb8e1d627c8c86d0e28b55b5f8
  | 8, 0 => 0x155b070715303b8814b7efae147ef837147be17a14445611141f8fdd13b478a2128177ed126ac74e11f546a611c9fc591106cdc710eee49c10dfc44d108cbea210739a890f1c517e0ecd7e060eccb7400eb2ba8a0de1f81f0db6ae630db3a33c0d4c5b2b0d359d660d2c2e290cda57470cd4669f0bedd9ed0b8bbf6b0af1fed60a9f6c030a5133e10a4a180909d69a7109703723093db6800907828d0801277907a3890607852a5a0769545207540f080700687906e4120e06d33f7406940e5504be9b5d0499b2c1046cf47e0451cc9a03edab4903e5727602fbbdeb02c7e1c6025a06d3020fff7e01dd076b01c0cf2f0185e19d01737d88010c7f3d00f26ece
  | 8, 1 => 0x690b0d396438425e63e020e46013f4555ebd6c475b8a9b545b7badac5a0f56b153fb90b350ba5f8b4c1021324b0d465449e5240849d837ae492e513d48be36e946cd9c5041e4c45340f62fdf409e34a43fd242ec3ef2c9303e51fe3b3d9f9c853ce83b323c8ae61d3bcc4b8e3a9cdd1a35db239333c0c9003354954530b17a1b30a941482ff00c9c2f1583e82cfda1512ceb381e2aa9504828a5bcb427e495672595651924f1d90e248349f2242a74e0241a19e722b3913a2085ba6f1f28e87e1c1a73291c1160c61c02e4e51b2750f31ae5543519b15e68196939d21917953718b98c20184d71d4180f157b17c02815178028051742223f1703b38d169ad4dc
  | 8, 2 => 0xb40748eeb03b1c5f8e9d72eb88c8f86084fccbd183b31a7d8128f3f38077f71979e8d72b78101b4376abcfae76a6ae1376374ac775a3370773a4843a7278be2071a8d4f069904ec9
  | 9, 0 => 0xb40748eeb03b1c5f69904ec9448b58423ef2c9303e51fe3b242a74e0196926bf1957081117a485a0167ebc1d
  | 10, 0 => 0x69904ec9
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00ff00ff00ff00000000000000000000000000000000000000000000000000cccccccccccccccc0000000000000000000000000000000000000000000000000505050505050505000000000000000000000000000000000000000000000000ffffffff00000000000000000000000000000000000000000000000000000000ffffaaaaffffaaaa000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f0000000000000000000000000000000000000000000000000eeeeeeeeeeeecccc00000000000000000000000000000000000000000000000000ff00ff00ff00ff
  | 0, 1 => 0xf0f0f0f0f0f0f0f00000000000000000000000000000000000000000000000011111111333333330000000000000000000000000000000000000000000000000000000055555555000000000000000000000000000000000000000000000000ff00ff0000ff00ff000000000000000000000000000000000000000000000000aaaaaaaaaaaaaaaa0000000000000000000000000000000000000000000000000000ffff0000ffff000000000000000000000000000000000000000000000000ffffffffa8a8a8a8000000000000000000000000000000000000000000000000ffff0000ffff0000
  | 0, 2 => 0xffaaff00ffaaff000000000000000000000000000000000000000000000000000000555500005555000000000000000000000000000000000000000000000000ffff8888ffff888800000000000000000000000000000000000000000000000000000000ffffffff000000000000000000000000000000000000000000000000fafafafafafafafa000000000000000000000000000000000000000000000000ffffffff888888880000000000000000000000000000000000000000000000001111111111111111000000000000000000000000000000000000000000000000aaaaaaaa55555555
  | 0, 3 => 0xffaaaaaaffaaaaaa00000000000000000000000000000000000000000000000000000000000000ff000000000000000000000000000000000000000000000000ffffffffaa88aa88000000000000000000000000000000000000000000000000ffa8ffa8ffa8ffa8000000000000000000000000000000000000000000000000ffffffffff00ff00000000000000000000000000000000000000000000000000ffccffccffccffcc00000000000000000000000000000000000000000000000011111111555555550000000000000000000000000000000000000000000000003333333333333333
  | 0, 4 => 0xfffcfffcfffcfffc00000000000000000000000000000000000000000000000005550555055505550000000000000000000000000000000000000000000000001111333311113333000000000000000000000000000000000000000000000000ffffffffaaaaaaaa000000000000000000000000000000000000000000000000fafafafafaf0faf0000000000000000000000000000000000000000000000000fefefefef0f0f0f0000000000000000000000000000000000000000000000000cc33cc33cc33cc330000000000000000000000000000000000000000000000005555555555555555
  | 0, 5 => 0xf0f0f0f00f0f0f0f000000000000000000000000000000000000000000000000aa55aa55aa55aa55000000000000000000000000000000000000000000000000eeeecccceeeecccc000000000000000000000000000000000000000000000000ffffaa00ffffaa000000000000000000000000000000000000000000000000000055005500550055000000000000000000000000000000000000000000000000ffffffffcccccccc000000000000000000000000000000000000000000000000eeeeeeeeaaaaaaaa000000000000000000000000000000000000000000000000ffffccccffff0000
  | 0, 6 => 0xfff0fff0fff0fff0000000000000000000000000000000000000000000000000ffffffffffffff00000000000000000000000000000000000000000000000000ffffffffffaaaaaa000000000000000000000000000000000000000000000000fffffffffffff0f0000000000000000000000000000000000000000000000000fafafafaaaaaaaaa000000000000000000000000000000000000000000000000ffffffffffff0000000000000000000000000000000000000000000000000000ffccccccffcccccc000000000000000000000000000000000000000000000000eeeeeecceeeeeecc
  | 0, 7 => 0xfcfcfcfcfcfcfcfc000000000000000000000000000000000000000000000000eeeeaaaaeeeeaaaa0000000000000000000000000000000000000000000000000000333300003333000000000000000000000000000000000000000000000000ffffaaa0ffffaaa0000000000000000000000000000000000000000000000000ffaaffaaffaaffaa000000000000000000000000000000000000000000000000ffaaffa0ffaaffa0000000000000000000000000000000000000000000000000f003f003f003f003000000000000000000000000000000000000000000000000ffa0ffa0ffa0ffa0
  | 0, 8 => 0xcccccccc333333330000000000000000000000000000000000000000000000000000000033333333000000000000000000000000000000000000000000000000faf8faf8faf8faf8000000000000000000000000000000000000000000000000fafafaf0fafafaf00000000000000000000000000000000000000000000000009999999999999999000000000000000000000000000000000000000000000000eeeeeeeecccccccc000000000000000000000000000000000000000000000000ffffffffffccffcc000000000000000000000000000000000000000000000000fffff0f0fffff0f0
  | 0, 9 => 0xff555555ff555555000000000000000000000000000000000000000000000000eeeeeeeeeecceecc000000000000000000000000000000000000000000000000aaaaaa00aaaaaa00000000000000000000000000000000000000000000000000fafafafaf0f0f0f0000000000000000000000000000000000000000000000000f0f0f0f0f0a0f0a0000000000000000000000000000000000000000000000000ccffccff00ff00ff000000000000000000000000000000000000000000000000aaaaaaaa00000000000000000000000000000000000000000000000000000000050505050f0f0f0f
  | 0, 10 => 0xffffccccffffcccc000000000000000000000000000000000000000000000000fcfcfcfcfcfcf0f0000000000000000000000000000000000000000000000000ffffeeeeffffeeee000000000000000000000000000000000000000000000000fffafffafffafffa000000000000000000000000000000000000000000000000faaafaaafaaafaaa000000000000000000000000000000000000000000000000ccccffff0000ffff000000000000000000000000000000000000000000000000ffffffffaa00aa0000000000000000000000000000000000000000000000000000ff00fa00ff00fa
  | 0, 11 => 0xfffffffff0f0f0f0000000000000000000000000000000000000000000000000feeefeeefeeefeee000000000000000000000000000000000000000000000000a5a5a5a5a5a5a5a50000000000000000000000000000000000000000000000001155115511551155000000000000000000000000000000000000000000000000eaeaeaeaeaeaeaea0000000000000000000000000000000000000000000000008888888888888888000000000000000000000000000000000000000000000000eeeeeeeeeeeeeeee000000000000000000000000000000000000000000000000fffffcfcfffffcfc
  | 0, 12 => 0xffffffccffffffcc000000000000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000fffff000fffff000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000cc88cc88cc88cc88000000000000000000000000000000000000000000000000ff00ff00f000f0000000000000000000000000000000000000000000000000000505050555555555
  | 0, 13 => 0xfcccfcccfcccfccc000000000000000000000000000000000000000000000000fffffffffcfcfcfc000000000000000000000000000000000000000000000000aa88aa88aa88aa88000000000000000000000000000000000000000000000000c3c3c3c3c3c3c3c3000000000000000000000000000000000000000000000000aaaaaaaaaaaa0000000000000000000000000000000000000000000000000000ffffffffffffaa00000000000000000000000000000000000000000000000000ffccff00ffccff00000000000000000000000000000000000000000000000000cccc0000cccc0000
  | 0, 14 => 0xa8a8a8a8a8a8a8a8000000000000000000000000000000000000000000000000cccccccccccc0000000000000000000000000000000000000000000000000000fffafffaffaaffaa0000000000000000000000000000000000000000000000000055555500555555000000000000000000000000000000000000000000000000fcfcfcfcf0f0f0f00000000000000000000000000000000000000000000000001111555511115555000000000000000000000000000000000000000000000000cccc3333cccc3333000000000000000000000000000000000000000000000000aaaa8888aaaa8888
  | 0, 15 => 0xffffffffeeeeeeee000000000000000000000000000000000000000000000000fcfcfcfcf8f8f8f8000000000000000000000000000000000000000000000000ccccccccffccffcc000000000000000000000000000000000000000000000000ffffffffffaaffaa000000000000000000000000000000000000000000000000fffffffffa00fa00000000000000000000000000000000000000000000000000ffffa8a8ffffa8a8000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000ffffff00ffffff00
  | 1, 0 => 0xccccc0c0ccccc0c0000000000000000000000000000000000000000000000000f0f00000f0f0000000000000000000000000000000000000000000000000000000000f0f00000f0f000000000000000000000000000000000000000000000000ff00ffffff00ff00000000000000000000000000000000000000000000000000ffccffccff88ff88000000000000000000000000000000000000000000000000fffffffff000f000000000000000000000000000000000000000000000000000ffffffff330033000000000000000000000000000000000000000000000000000077007700770077
  | 1, 1 => 0xffffaaaaaaaaaaaa000000000000000000000000000000000000000000000000c0c0c0c0c0c0c0c0000000000000000000000000000000000000000000000000ff00ff0000000000000000000000000000000000000000000000000000000000eeee0000eeee0000000000000000000000000000000000000000000000000000fffffffffafafafa000000000000000000000000000000000000000000000000fcfcfcfcecececec000000000000000000000000000000000000000000000000f0f0f0f0a0a0a0a0000000000000000000000000000000000000000000000000ffaaffaaffa0ffa0
  | 1, 2 => 0xffffffffcccc0000000000000000000000000000000000000000000000000000ffaa0000ffaa0000000000000000000000000000000000000000000000000000aaaaaaaaaa00aa000000000000000000000000000000000000000000000000000707070707070707000000000000000000000000000000000000000000000000fafaaaaafafaaaaa000000000000000000000000000000000000000000000000aaaaaaaaa0a0a0a0000000000000000000000000000000000000000000000000fff0fff0ff00ff00000000000000000000000000000000000000000000000000eeaaeeaaeeaaeeaa
  | 1, 3 => 0x303030303030303000000000000000000000000000000000000000000000000fffffafaffff0000000000000000000000000000000000000000000000000000f0a0f0a0f0a0f0a0000000000000000000000000000000000000000000000000faf0faf0faf0faf0000000000000000000000000000000000000000000000000cccccccccc00cc00000000000000000000000000000000000000000000000000fffffafafffffafa000000000000000000000000000000000000000000000000113311331133113300000000000000000000000000000000000000000000000000000fff00000fff
  | 1, 4 => 0xffcceeccffcceecc000000000000000000000000000000000000000000000000f0f0f0f0f0f5f0f5000000000000000000000000000000000000000000000000ffffffffeeee0000000000000000000000000000000000000000000000000000fcfcfcfccccccccc000000000000000000000000000000000000000000000000ffffcccccccccccc000000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000003300ff003300ff000000000000000000000000000000000000000000000000f0f0f0f0c0c0c0c0
  | 1, 5 => 0xccccfcfcccccfcfc000000000000000000000000000000000000000000000000fff0f0f0fff0f0f0000000000000000000000000000000000000000000000000ffffeeeeeeeeeeee000000000000000000000000000000000000000000000000cccccccc00000000000000000000000000000000000000000000000000000000a0a0a0a0a0a0a0a0000000000000000000000000000000000000000000000000ffccffccff00ff00000000000000000000000000000000000000000000000000fefefefefefefefe000000000000000000000000000000000000000000000000030303030f0f0f0f
  | 1, 6 => 0xcfcfcfcf0f0f0f0f0000000000000000000000000000000000000000000000000f0f0f0f00000f0f000000000000000000000000000000000000000000000000fffff0f0ffff000000000000000000000000000000000000000000000000000000000000f0f0ffff000000000000000000000000000000000000000000000000ffeeffeeffeeffee00000000000000000000000000000000000000000000000000000f0f0000ffff000000000000000000000000000000000000000000000000fffffff0fffffff0000000000000000000000000000000000000000000000000ffffeeeeffff0000
  | 1, 7 => 0xffffffffa0a0a0a0000000000000000000000000000000000000000000000000ffaaffaaff00ff000000000000000000000000000000000000000000000000000000030300000303000000000000000000000000000000000000000000000000ffffccccffff8888000000000000000000000000000000000000000000000000ffffffffcccc8888000000000000000000000000000000000000000000000000ffeeccccffeecccc000000000000000000000000000000000000000000000000ffaaffaa00000000000000000000000000000000000000000000000000000000ccccccccc0c0c0c0
  | 1, 8 => 0x101010101010101000000000000000000000000000000000000000000000000cc00cc00cc00cc00000000000000000000000000000000000000000000000000f0f0f0f000000000000000000000000000000000000000000000000000000000fcfcf8f8fcfcf8f8000000000000000000000000000000000000000000000000fefefefecccccccc000000000000000000000000000000000000000000000000ffffeeeeffffaaaa000000000000000000000000000000000000000000000000000000000f0f0f0f000000000000000000000000000000000000000000000000fefefafafefefafa
  | 1, 9 => 0x5555550055555500000000000000000000000000000000000000000000000000fefefefe00000000000000000000000000000000000000000000000000000000f0faf0faf0faf0fa000000000000000000000000000000000000000000000000ffffffffeecceecc000000000000000000000000000000000000000000000000eecceecceecceecc0000000000000000000000000000000000000000000000000000cccc0000cccc000000000000000000000000000000000000000000000000ffccffcccccccccc000000000000000000000000000000000000000000000000fafaf0f0fafaf0f0
  | 1, 10 => 0x5500550055005500000000000000000000000000000000000000000000000000f0f0f0f0f5f5f5f500000000000000000000000000000000000000000000000000000000ffffaaaa0000000000000000000000000000000000000000000000000033003300330033000000000000000000000000000000000000000000000000ffffffffeeeeaaaa000000000000000000000000000000000000000000000000aa00aa00aa00aa00000000000000000000000000000000000000000000000000222222222222222200000000000000000000000000000000000000000000000000005f5f00005f5f
  | 1, 11 => 0xee00ee00ee00ee00000000000000000000000000000000000000000000000000ffffffff0000ff0000000000000000000000000000000000000000000000000000000000aaaaaaaa000000000000000000000000000000000000000000000000ffff3030ffff3030000000000000000000000000000000000000000000000000ffeeffeeeeeeeeee000000000000000000000000000000000000000000000000ffff0c0cffff0c0c000000000000000000000000000000000000000000000000ffffaaaaffff0000000000000000000000000000000000000000000000000000aaaaa0a0aaaaa0a0
  | 1, 12 => 0xfffffffffffff000000000000000000000000000000000000000000000000000fcfc0000fcfc0000000000000000000000000000000000000000000000000000fffffafaffffaaaa0000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000aaaa0000aaaa0000000000000000000000000000000000000000000000000a0a0a0a0a0a0a0a00000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000000000000000000000000000cccceeeecccceeee
  | 1, 13 => 0xffffffff55005500000000000000000000000000000000000000000000000000eeeeeeee000000000000000000000000000000000000000000000000000000000000fafa0000fafa000000000000000000000000000000000000000000000000ffffffffffffcccc000000000000000000000000000000000000000000000000afaaafaaafaaafaa000000000000000000000000000000000000000000000000ccc0ccc0ccc0ccc0000000000000000000000000000000000000000000000000ddddccccddddcccc000000000000000000000000000000000000000000000000ffeeffeeffaaffaa
  | 1, 14 => 0x333033303330333000000000000000000000000000000000000000000000000044444444444444440000000000000000000000000000000000000000000000000000f0f00000f0f00000000000000000000000000000000000000000000000000000000000ff00ff00000000000000000000000000000000000000000000000033330000333300000000000000000000000000000000000000000000000000000333033303330333000000000000000000000000000000000000000000000000fa00fa00fa00fa00000000000000000000000000000000000000000000000000fefefefefafafafa
  | 1, 15 => 0xffffffffff000000000000000000000000000000000000000000000000000000ffffffaaffffaaaa000000000000000000000000000000000000000000000000ffffffffffeeffee000000000000000000000000000000000000000000000000fcfcf0f0fcfcf0f00000000000000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000003333303033333030000000000000000000000000000000000000000000000000fffffffffafaf0f0000000000000000000000000000000000000000000000000ffaaffaaaaaaaaaa
  | 2, 0 => 0xff00ff00000000000000000000000000000000000000000000000000000000ffeeff00ffeeff0000000000000000000000000000000000000000000000000033333333222222220000000000000000000000000000000000000000000000005555555500000000000000000000000000000000000000000000000000000000ffff00ffffff000000000000000000000000000000000000000000000000000000000000ff00ff00000000000000000000000000000000000000000000000000ffffffaaffffffaa000000000000000000000000000000000000000000000000aaaa0000aaaa0000
  | 2, 1 => 0xf5f5f5f5f0f0f0f0000000000000000000000000000000000000000000000000ffff0000ffffff00000000000000000000000000000000000000000000000000ffffffffc0c0c0c00000000000000000000000000000000000000000000000000c0c0c0c0c0c0c0c000000000000000000000000000000000000000000000000ecececececececec0000000000000000000000000000000000000000000000000f0f0f0f00000000000000000000000000000000000000000000000000000000fefefefeeeeeeeee000000000000000000000000000000000000000000000000fffffffffffcfffc
  | 2, 2 => 0xccfcccfcccfcccfc000000000000000000000000000000000000000000000000e0e0e0e0e0e0e0e0000000000000000000000000000000000000000000000000ffffffffffffa0a0000000000000000000000000000000000000000000000000ffffa0a0ffffa0a00000000000000000000000000000000000000000000000000f0f00000f0f0000000000000000000000000000000000000000000000000000ffffffffffffaaaa000000000000000000000000000000000000000000000000cccccccccccc8888000000000000000000000000000000000000000000000000fcfcccccfcfccccc
  | 2, 3 => 0xffffaaaa00000000000000000000000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000ffffcccc00000000000000000000000000000000000000000000000000000000ff00aa00ff00aa00000000000000000000000000000000000000000000000000ffffffffaaaa0000000000000000000000000000000000000000000000000000f0f0f000f0f0f0000000000000000000000000000000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000ffffffffffaaff00
  | 2, 4 => 0xfff0fff0f0f0f0f0000000000000000000000000000000000000000000000000ffff5555ffff0000000000000000000000000000000000000000000000000000ffecffecffecffec000000000000000000000000000000000000000000000000ffff0505ffff0505000000000000000000000000000000000000000000000000ffffff00ff00ff000000000000000000000000000000000000000000000000003232323232323232000000000000000000000000000000000000000000000000fffafffafafafafa00000000000000000000000000000000000000000000000000000000f0f0f0f0
  | 2, 5 => 0x3300330033003300000000000000000000000000000000000000000000000000fffffffffffafffa00000000000000000000000000000000000000000000000000f000f000f000f0000000000000000000000000000000000000000000000000333322223333222200000000000000000000000000000000000000000000000000aa00aa00aa00aa000000000000000000000000000000000000000000000000ff11ff11ff11ff11000000000000000000000000000000000000000000000000ffffffff00aa00aa0000000000000000000000000000000000000000000000000000000005050505
  | 2, 6 => 0xf0f0f0f0a0a0a0a000000000000000000000000000000000000000000000000fffffa00fffffa00000000000000000000000000000000000000000000000000f2f2f2f2f2f2f2f200000000000000000000000000000000000000000000000000ff00aa00ff00aa0000000000000000000000000000000000000000000000005555505055555050000000000000000000000000000000000000000000000000050f050f050f050f000000000000000000000000000000000000000000000000babababababababa000000000000000000000000000000000000000000000000aafaaafaaafaaafa
  | 2, 7 => 0xffffffffcc00cc00000000000000000000000000000000000000000000000000f8f8f8f8f8f8f8f8000000000000000000000000000000000000000000000000fffcfcfcfffcfcfc000000000000000000000000000000000000000000000000aaeeaaeeaaeeaaee000000000000000000000000000000000000000000000000fffffcfcfffff0f00000000000000000000000000000000000000000000000000055005555555555000000000000000000000000000000000000000000000000ffeeffeeff00ff00000000000000000000000000000000000000000000000000f0fcf0fcf0fcf0fc
  | 2, 8 => 0xf0f0a0a0f0f0a0a0000000000000000000000000000000000000000000000000ff88ff88ff88ff8800000000000000000000000000000000000000000000000000cc00cc00cc00cc000000000000000000000000000000000000000000000000fafafafa00000000000000000000000000000000000000000000000000000000fffff0f0f0f0f0f00000000000000000000000000000000000000000000000003333333300000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x200e2203035400040400842205000103e02030794001d0401c04115000103813030294001b04068041950002018020586140017010182c145000540e0208851400090404c0c005000480e02088294000803818200f5000200e02070354000c01018160a500024100703015400040180802005
  | 5, 0, 1 => 0x106e0613029400361a87c0406500090100200801400340181c66065000c8363101081400040380860165000200e2f0308140004040085c1850001c042d0b0514002c0101856145000a80e29078294001b140680420500010102703099400040181c4a0f5000102a0208801400240388c0c0a5
  | 5, 0, 2 => 0x200e0221035400081d9140c14500020764403051400040400886005000900e4207829464412001c7e0b6000100e3e078f540004040185c0f500010783b010614002a03808320a50001070130c02940004040e80c0550001010390302d40004040dc302650002004060800140004040e00c055
  | 5, 0, 3 => 0x641b200687e0b6000900e0624029400080111c16005000e0260605051400040185c300f500090044200029400080380832465
  | 6, 0, 0 => 0xd8081f0101816c001a86c101f0101980032121000e130330000807011480c206001441007058601ec00020200406059418002a020b0760203300008082781c04186000200e02210181ac000d8100607010b580004038089c0b0530000607010189a146000200e4c010181ac00020200e4b0308180004040089406103000100701124300d6
  | 6, 0, 1 => 0x200e440302c28c002f8200e1303035800240401c045923300008080d178a6026000101007031740ac00020203402059718000426018160005300048040401c7e5b600010ae021f02c00c0002020b25a078018002a120200e5907b000080803808b243600010b057038087cc00020200e5603081800042a80c2e0203300008082a0dca6066
  | 6, 0, 2 => 0x901007031ac1ec0035010583b0101980004041a47e1305b00008580384cd00b600010ce0303808b2c001202034070110980004040cc0418003000103733018401460001c04061002828c000219434022c82d800000215c0e3e07a800c8070302c1e63600010101a0118840c000d820c20203081800041401c0406103000005f0401c0c605
  | 6, 0, 3 => 0x100e13031dc14c00191900406100018002a0401c047610300008082602c300060017c1075038cc0cc00190100e02031d1800000d820347305a800080803818e40f6000000807011c416a00020200e593803d80004039bc0420053000be0719818160a6001b848080384c0cc000202076063683d80000020200e6c05a80008081d81c7e5b6
  | 6, 0, 4 => 0x48072601814a00408207602058618000404018160f40300000040185c0c0f5000100e060592014c003f81010073f02d800080380840180a30001007011f44014600104480803808b2c003e0901007260198007b040ec2602033000087a0101816006000c836790101840c00021e0760203059800120401c045908b000040b0c00014146
  | 6, 0, 5 => 0x22c080803a2816c002f8200e890308180004440080c0b0530000808038fd0e2060015c0e023408028c0003a180c0b4285180004040e8040b0c3000002404008840050001108060583c14c1b2f820763f0302dc00043c0080c0b3a30000808418080c2060017c10071982c30c00410200e3f03081800042a80c0e0216b00054080380852206
  | 6, 0, 6 => 0xd89006081d8080ce000401c0c4907835800080b818160f0a3000080739818400a600010101a0124040c000d8481007011658008f038080c0b31b0000808038fc0c266000200e3f4708028c000d97c101a1f82d8001b468080c20053000001503808b21450000024070116414a0002100d2130302d800040380918060b3010f0400d04c0c0b7
  | 6, 0, 7 => 0x17c08030b8080cc000482004060580180004041a47e021030000057038087c14500010b007011a040c00021000e9305861800240401c044206b0000840038fc7c0b600010f01f1f8080cc001923c760701019800040384c0c9205300010022c968001460009108020302c14c001500c1007010a5800040401c046d08b0006403488080c0b6
  | 6, 0, 8 => 0x100e020308130c0000010ae021f0014008b120200e0221300008080102c1c006000012e40038fc16a00000d8081f010194002a120200459003000100701018e4146000207602031b428c1b0210010270302dc000002020700602a80008784b0080c206000101002031b456c000202076024a8618000404018169400300008780f8080c746
  | 6, 0, 9 => 0x1010071fa8040c00021e0063b01019800040401d1c204fb000083729818160a6002080e020308014c320d8204e020302dc00244f01c2602033000080803a740c056000101002031c800c00091541007011658007c02020769c03300008080d0093620600010f09a1d8080cc00020200e0b4c83d80004038080c700b300010020302d00146
  | 6, 0, 10 => 0x17c1007199640cc04018200e3f09965c00000181c042d0a28014a5703808b20b60020810070108030c00020200ea4010818000404210040610300008650d0080c206000c946070116416c000413c0e0203051800043c8080c2051300010020302d421460001006171f8080cc00150207607010a580000120200e0207286c085804068040b7
  | 6, 0, 11 => 0xa960070116416c000001080071f8f940004038095e2005300064045701c0c206000c95a070101816c001501d580b078298000709819560a0a300008aa0302c1e0a60000036280d00816a00040080c4900035800040a81d52022cb00008080381840a860001010a70380840c000201c401807829800043c00d4e0205b000080803a980c0b6
  | 6, 0, 12 => 0x1c04200c02828c000201c04062685980004039a0160f1eb000000803808840d51b01080071f81816e000401c0c0b5b051800045a81c040610306c0840040687e0b7000101007558600ac000401c0c0b07ad180008039bc04200a3000be240401c7e59600010f003598080cc000202070a90981980004038080c2059300008b1018ec04066
  | 6, 0, 13 => 0x100e023402d7ac001201178070116580000120200e0624280176030401c045960001010730308000c00021012606058018000404068760214b00008085d01c042060006c10b90101840c00020200e3f5c08180024020200e7e2cb0003624040dc2606600010ae070123040c0000010100703175400040401d6e0610300080074981816146
  | 6, 0, 14 => 0x10f0031d80830c000401c660605b058681b04068040605b8000867018ec0406600010ae07600087cc001201c9802030298008b5f8200e130330000e9c0302c14146000108003038cc0cc0012010ae07010f9800321215c0e022cb0000807058601e0a6000c946070101840c00022f80c0b07829800810401c161807b00008150401cb20f6
  | 6, 0, 15 => 0x10071981982a000200c100762165800040401d860210300054c20401c04296001e0f2020308028c002f89010070986180004038080c200530012e40038080c206
  | 7, 0, 0 => 0x10101a098098c0b7001f008081b8080c0b7000c808570d01c040b7000100e022c818160a7000c836081b8080c0b7000900e020302c141470000008086401816006000101007098087c067000111e0803818160f70001010070101816c77000000808010a40c006000d808080d0080c0b7000c8080803a700c0b70d8101007010f80c0b800010100703318400f700000be0762818160a6
  | 7, 0, 1 => 0xc83603038080c0b700330080803809960b700010800803aa40c0b700010100701018160d7001001007098181614700010060701018166370006c08080380816187000101007012400c207000d808783c8080c0b70001010070101840ca700010f03b01018160a70001010c9038080c20700010101a1d8080c0b7000101037331640c0b719090103b038080c0b80017c080701018400a7
  | 7, 0, 2 => 0x10103b0101816d470000008070132c160a60034c0808038087c067000c808081b9980c0b7001f008081d8080cd2700010100205861a200700010ce081d8080c0b70000008070101816d060001010070101840cf70000008080981956006000200ece098080c0b70001010cd010181600700000083801018160a600010103b038cc04067000a8080803808b20b7000101002032b040007
  | 7, 0, 3 => 0x200e020302db0147000c81007198080c0b7000100e020302c560a700090080803aa404067000901007098080c14700010f0080101840d7700010800803818160570000008b50101816006000100608039640c0f70000008085f008161860001010076b0080c0b700010500803818160f7000c84808038080c2070001010071f84c161870001010070101816d570001010071fb200c0b7
  | 7, 0, 4 => 0x200e022c81828dd700010340701018400a700010101a1d808c40b70000008dc038081618600000820803809580b600010f0081d84c04067001fc080803808b25a70001162080380816187000200e060583c141470001010db038080c0b700011b40803818160f70001080d9038080c0b70000008783c8080c20600010f00801018400070000010ae038181614600010503b038080c0b7
  | 7, 0, 5 => 0x828038080c206150108003038080c0b80000008080d0fccc0b6000900808038080c0570009010070102c30147000100e060583dc40a70000036040407c04066000200e060583c28e17000c808031d81c04067000100e0270018160a70001010b30137c0c0b700000be0803b14161860000008071fa38160a6000ec0e020302c1414700010100746818400f700378080701018160a7
  | 7, 0, 6 => 0xc8089a038080c0b70001010071f964160f70000008280d01c040b600010ae0303808b20671901010071f84c0c0b800011ca08038cc04067000d06464038080c0b70009008020302c000a700010f0081d80816187000200e06058801e1470017c080803808401870001c04060583c141470006d2e08038080c0b70001010070101840e4700010101f038fc040670001004060580014e37
  | 7, 0, 7 => 0x207607098080c14700010101f038080c747000200e020308000147000101007013a40c2070002004063402c001470022c0808038080c0b70001010e8550080c0b70039c0865038080c0b7000101007730080c207000207e020302c001470017c1007629640c0b7000200e0203081ae14700010800809818160070001010370384c0c207000000e0203080141460000008081c00816186
  | 7, 0, 8 => 0x100e020302c14ed700010aa0701018160a7003b008080101816007000900808098080c0070210010071f84c0c0b80000008081d809a4186000116203038080c0b7000106e070102c300a7000d0080701018160a7000101007033ac160f7000101096038080c2070001010070102c302b7000900808418080c0b7000111e0803808b20670001080031d81c0406700010100701019d4207
  | 7, 0, 9 => 0xd80808038080c20700010f0080d008b20b700010f0031d8080c0b700010100701018408570001076020302c000a7003bc0808038080c207000a808070302c1e0a7000c808081c0080c0b70017c480803a240c0b700010103b038080c0570001080080380816187000000004160ec04065001fc1007013b80c0b70006c1007010184014700010101a03808401870001080085f0080c0b7
  | 7, 0, 10 => 0x10103b098080c007000101007010193620700010100701164163d700010100705861e60f70001010070302c220f7000000004040dca60650000008080380816f260006c083b01018160a700010103701018162b7000c808081d8080cd2700010103b09bc4040670000010070108030146000c80803038080c0b70001010ae038fc0c0b70009008080102c30007000101007781cc0c0b7
  | 7, 0, 11 => 0x100e3f01018400a7000108003038080c0b700010ae080380840f67000100e3f0302c14f5700010aa080380816187000101007548080c0b70009010070101816c17000100e06058601e0a700010ae08038080c20700010103b01019a42b7000200e022c81840147000d0080803808161870000064041881c040b600010102703818160f7000c810070101816f47000206e3b0101816147
  | 7, 0, 12 => 0x101007030801efb7000101002058601e007000c8084003818160f70001010070102c30fa700010b00701018160a700000089101018160a6003e40808038080c0b7000a80808038fc0420700010103b0102c30007000000808038fcb60b60001034071f808160a7000481037038080c0b70001006087c01c0406700010100752008162070001010070102c30f770006c08080101840d77
  | 7, 0, 13 => 0x1202783c8080c0b70000008d903818160f60001c04060582829027001e080070101816147000100e022c82c14ca7001f0080803818160f70001202080d0080c0b70006c08081d80816187000c8360803818160f70000008070101a00166003fc10071f8080c0b70001010070302c1e63700011fc08038080c0b7003f40808038080c0b700000646403818160f60000008087e01816006
  | 7, 0, 14 => 0x6c1007010184104700010101301018160070d810103b011640c0b80001010022c818400070001006080302c1e007000100e0257818160a70001006081d81c04067000a848080384c040670000008070302c1e0a6000100e0203080141670d810b008038080c0b80001010270d0098c0b70006c48083c8080c0b70000009030101816006000200e020331840147000d00803038080c0b7
  | 7, 0, 15 => 0x190100637038080c0b80001010aa038080c20700010100701018ec2070006cbe0701018160a70000008400401c66066004200808038080c0b7000a84808038081618700010100701018161e70009008080380920067000c810020302c0107700010b0080380816187000101106011640c0b70001010070101817057000000808488081618600010103703808b25a7000c83657038080c0b7
  | 7, 1, 0 => 0x43810070101816147000000808038080c746004340808038080c20700090100701018166370001010071f018160f7000101091011640c0b7000108015038080c0b7000200e02058602902700010100701018410c7000101002858181600700010ae030101816007000200e0233018401470006c08080d008b20b70009010070302c1f0a7000101007848080c0b7000200e022d81816147
  | 7, 1, 1 => 0x3628038080c0b6000c8082c038080c0b700010b003038080c0b7000101007010a40c2070006c108d098080c0b70001006085381c040b70001006070302c1f13700000ca070101816146000111e08010181600700010f03b4b0080c0b70044808080380a220b7000101007880080c20700000081a01318160a6000101007878080c20719010101a038fc040b800010040605924000a7
  | 7, 1, 2 => 0x116a0701018162070017c080803aa40c0b702020343b098080c0b8000120208038080c2070001010b9038080c2070001010073984c0c0b7000c808070101816857003b0080803808b20b700010f0081d818160f70017c100701018160d70001010b3038080c2070017c080803818400f70006cbe080380816187004540914038080c0b70001010072c818160f700010101a03808520b7
  | 7, 1, 3 => 0x101007640081618700020040605880001470046008080b8080c0b70000024040401c045960001010028b818160070001010071f94c0c0b70001134080384c0cab7000101007014580c2070002004060580028e170000008081d819a40f600010100221018160070001010070302c1e2b7001e01007010181614700010100205924300070d97c1007011640c0b80001010070101816607
  | 7, 1, 4 => 0x8070142c160a6000123a08038080c2070001010072f0080c0b70017c4808038080c2070001080071f818160a700000480701018920a60001202088e0080c0b70009008080302c1e0070006e3608038080c0b700010f00803808840b700010ae080d0ec040b7000c85408038080c20700010103f0116416007000d80840038080c0b7000101007014680c207000100e020308015197
  | 7, 1, 5 => 0x1010070102c312270000010074e0181614600010101a01198b20b7000101121038080c0b70001c04060582829207000c8071f038080c0b70022c0808038fc0c0b700010aa0803818160f7000100e0203081ec0a7000a808020302c000a70001010370382c300f700011b21a038080c0b70017c08080981816007000000914038081618600010100701018411e70001006080380852067
  | 7, 1, 6 => 0x4a40808010181600700010100701018172870001011270384c0c0b7190100607098080c0b8000900808348080c0b70006c08081d818160f7000124c08038080c2070000010373301816146000101125038080c0b700000081503818160f6000000878018ec040660001010020302c22007000124808038080c0b7000116a03038080c0b7001f0100701018161470001246081d8080c0b7
  | 7, 1, 7 => 0x104080803818160f700010100701018172c700010103103818160f700000082c03818160f6000a8a208038080c0b70001010691d8080c0b70000010070102c3014600010040605802560a71201006080384c04068000d80808038080c0b7001f008080101816007000200e021f018161470001010073c808401870001010020302c0063700010100701080300a700010112a038080c0b7
  | 7, 1, 8 => 0x1f03608468080c0b700000ae07011a0161460000010380101816146000a81007012b016207004b80808038080c0b700010060701018400a7001e0103b010181614700010101301018012b7000101007398080c20700000540803808520b6001f010b9038080c0b70006c48081d8080c0b7000100e020302d240a700010100203080012d70001010071f8181605700090080803a4c04067
  | 7, 1, 9 => 0x100608550080c0b70006c08070102c300a700000080739818160a60006c0e020302c151970017c080801018400070001010022c81816007000101007014c416187001044808038080c0b7000a8480803808b2067002080808038080c207000100e020302c14167000101002034c0160070002034070101840147000113408038fc0c0b700010100701080312f70001010021f01816007
  | 7, 1, 10 => 0x6c08080d0080c20700010103b1f8080cd270001c040605b48141470006c108d011640c0b700010ca0701018162070006c083701018160a700000240701018160a60000008b5038080c20600010101a1d84c04067000101007010184133700010101a038095820700154100701018161470000008080381817326000a8060803809580b7000116a3b038080c0b71201080080384c0c0b8
  | 7, 1, 11 => 0x190901007098080c0b8003b00808038080c2070001010b303808c40b700010100703081ec0f70001080070102c300a719010101a1d8080c0b8000126c07098080c0b700010100716818160f700010aa080101816007000100e020302c14dd70001080080384c0c2070001010370102c300070001010079a8081618700090080701018400a70001010020302c0134700010ae0803964160f7
  | 7, 1, 12 => 0xa8080803aa4040b7000101007012240c2070001010072c82c1f0c7000100ea901018160a700010113801018160070001010070102c30dd70001010070302c1f377000116007011640c0b7000100e02030801e0a7000900808038084018700010760701018400a700010f079098080c0b700000080701018169860001010020302c004670001006080380830d17000101007030801e0a7
  | 7, 1, 13 => 0x807058601e0a6000108007431640c0b7000000808010f80c006004600808038080c0b70006c08070302c1e0a70001010371d8080c2070000008790101816a26000200ec8010181614700010101a011980c207000001007010f80c14600000080803a38169f60017e3608038080c0b700010100701018173a7000101139011640c0b70006c08080d0fc040b7000c8c8070101816207
  | 7, 1, 14 => 0x101007780080c0b70001010070302c1edd7000127608039cc0c0b7000000865038080c2060001010020302cee0070006c48080384c04067000200e0203081ec147000c808070302c1e0a70000064045701c0c0b60006c08080382c300f70001006081b9980c0b70001134080380816187000101007010803014700010ae030d01c040b7002081007011640c0b70000008080381816a86
  | 7, 1, 15 => 0x240401c044250006c0808038080c2070001c04590302c1414700000080701018400a6000000e0205860141460001010371da740c0b7000006464038080c206000101002034f01600700011b20803818160f7190a81007098080c0b80001080081b8ec0c0b70001010070101840117000c848080384c0406700010103b0384d3a0670006c08080d0080c0b70001080080382c300f7
  | 7, 2, 0 => 0x12e40038080c0b60001184080380852067004fc4808038080c0b700012280803808161870001010070302da20f70000064a3038080c0b60001010371d8080c0b7000100f3e01018160a700010113d038080c0b7001000e020302c14147
  | 8, 0, 0 => 0xd8101007011640c0b80001010070102c3140700010ca08038080c0b70001010370101816007000c808073c8080c0b71901010070101816008000101007298080c0b7000c8080701018160a7000a8080803808b20b7020200e022c8181600800010100701018160d70006c0808038081618700010101a1d8080c0b70200c10070101816148000000808039cc0c0b6000100e022c818160a7
  | 8, 0, 1 => 0xd8108008038080c0b8000900808038080c2070022c0808038080c0b7000c808080380816187020207696038080c0b8000128208038080c0b712010100701018160f8000101007011641618712010103b038080c0b8000200e020302da4147020206e071f8080c0b8000100e0203318160a70006c08081b8080c0b7000002408038080c0b600010800701018160a71906c0808038080c0b8
  | 8, 0, 2 => 0xc80803038080c0b702020760701018160f800010f00803818160f700000080803808b25a60d8101007010181700800010800803808161870001010020302c01437000100e8d01018160a7024040608038080c0b8000100e0233018160a7020200e13a10080c0b81501010070101816208190101007011640c0b82f8101007098080c0b8000101007032b0160f712010ae08038080c0b8
  | 8, 0, 3 => 0x202034070101816ab800011b208038080c0b700010ae080d01c040b7000108003038080c0b7000200e0243018161470001010070119816187000101007548080c0b700010ae08038080c207020200e020302c401880215c100701018160f80001010070102e0018700010100701018400f70215c103b038080c0b8120101007010191c0b8021001007011640c0b8000101007520080c0b7
  | 8, 0, 4 => 0x1a0108008038080c0b800010101301018160070001010070302c1e0070001006081d81c040670000008070302c1e0a6000101007010191c2070001010070101816f47190101007011980c0b8000200e020302d56147000010408038080c0b61a0c80808038080c0b8020200e8d011640c0b800000084003a180c0b6020200e02331640c0b8020207607010191c0b80001010074e0080c0b7
  | 8, 0, 5 => 0x10f0080101816007000102a08038080c0b715010103b038080c0b8000101007012400c0b7000101144038080c0b70001010070101841047001e0100701018161470000008080394c04066890100608038080c0b80001010072c818160f70202076b9038080c0b8000100608038080c0b70001010020302c0107702021663b038080c0b82f810f008038080c0b8020200e3f098080c0b8
  | 8, 0, 6 => 0x1010022c818160071a17c0808038080c0b8020200e3f01018160082f81010070101817008020200e02430181620800010ae08038080c0b7000000808038080c206020200e79098080c0b8020200e1301018160582f8108008038080c0b80000010070102c30146000d80808038080c0b7000200e020302c00147021e010071f8080c0b80200c1007015140c0b80000008783c8080c0b6
  | 8, 0, 7 => 0x1010020302c012d70001010070102c300a70d81010070101816208000100e020302c400a7021e00608038080c0b8120101007098080c0b80200c100701019580b800010100701018171e73f8a80808038080c0b8020200e02032b016208004340808038080c0b7000200e023301816147020200e3f011640c0b80001010aa038080c0b700000a208038080c0b6000200e020302e00147
  | 8, 0, 8 => 0x1010371d8080c0b70006c0808038080c20700000080701018400a6000100e020302c1e0a70001010070302c1e0a7003b00808038080c0b70006c08080d0080c0b70000008b5038080c0b60001010070102c30d1700010101a03809580b7021e0103b038080c0b80001010070101958207022688008038080c0b80017c08080101816007000000808a20080c0b6000000808038080c0b6
  | 8, 0, 9 => 0x6c0808038080c0b700000080701018160a6
  | 9, 0, 0 => 0x1b020200e020302dc0004038080c0b0530000808038080c0b6020200e020302cb4e042b8200e020302dc00040401c04061030100608038080c0b7020200e020302c40e04041900e020302dc0808039e4040605b810100701018160a7
  | 10, 0, 0 => 0x808038080c0b6
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 58
  | 6 => 67
  | 7 => 76
  | 8 => 76
  | 9 => 67
  | 10 => 58
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 9 0) :: stateWires n (ids >>> 9)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xf003f800000000000000000000000000000000000000000000000000000000000003c78e0000000000000000000000000000000000000000000000000000000ffe1ff80e0000000000000000000000000000000000000000000000000000000ffe0000000000000000000000000000000000000000000000000000000000000f01fc0001f000000000000000000000000000000000000000000000000000000001e007f0000000000000000000000000000000000000000000000000000000000003c78e0000000000000000000000000000000000000000000000000000000f0ffc07fff
  | 0, 1 => 0xffe1ff80ff000000000000000000000000000000000000000000000000000000ffffc3871f000000000000000000000000000000000000000000000000000000001fffffe00000000000000000000000000000000000000000000000000000000f1fc07fff000000000000000000000000000000000000000000000000000000000000001f0000000000000000000000000000000000000000000000000000000fe03fffff000000000000000000000000000000000000000000000000000000ffe0000000000000000000000000000000000000000000000000000000000000f01fc00000
  | 0, 2 => 0xf003f80000000000000000000000000000000000000000000000000000000000fe03fffe0000000000000000000000000000000000000000000000000000000f01fc00000000000000000000000000000000000000000000000000000000000001fffffff000000000000000000000000000000000000000000000000000000001e007f1f000000000000000000000000000000000000000000000000000000ffe0000000000000000000000000000000000000000000000000000000000000ffffc38700000000000000000000000000000000000000000000000000000000001fffffe0
  | 0, 3 => 0x1f0000000000000000000000000000000000000000000000000000000000007fff000000000000000000000000000000000000000000000000000000ffe00000000000000000000000000000000000000000000000000000000000000f003f8000000000000000000000000000000000000000000000000000000000ffe03f80000000000000000000000000000000000000000000000000000000000f003ff8e0000000000000000000000000000000000000000000000000000000ffffffffe0000000000000000000000000000000000000000000000000000000ffffc3871f
  | 0, 4 => 0xf1e3fffe0000000000000000000000000000000000000000000000000000000ffffffffe0000000000000000000000000000000000000000000000000000000ffffc3871f000000000000000000000000000000000000000000000000000000ffe000001f000000000000000000000000000000000000000000000000000000001e007f00000000000000000000000000000000000000000000000000000000001e007f00000000000000000000000000000000000000000000000000000000f0fffc071f000000000000000000000000000000000000000000000000000000ffffffffe0
  | 0, 5 => 0x1ff80ff000000000000000000000000000000000000000000000000000000f0ffc07fe000000000000000000000000000000000000000000000000000000000003c78e0000000000000000000000000000000000000000000000000000000f01fc00000000000000000000000000000000000000000000000000000000000f0ffc07fe0000000000000000000000000000000000000000000000000000000ffe03c78e0000000000000000000000000000000000000000000000000000000000000001f000000000000000000000000000000000000000000000000000000f01fc00000
  | 0, 6 => 0xf1e3fff00000000000000000000000000000000000000000000000000000000ffffff8000000000000000000000000000000000000000000000000000000000ffe000001f000000000000000000000000000000000000000000000000000000ffffc07f00000000000000000000000000000000000000000000000000000000000000001f000000000000000000000000000000000000000000000000000000ffffc0000000000000000000000000000000000000000000000000000000000000003c78e000000000000000000000000000000000000000000000000000000000003c78e0
  | 0, 7 => 0x1e3c7fe0000000000000000000000000000000000000000000000000000000000000001f0000000000000000000000000000000000000000000000000000000fe003871f000000000000000000000000000000000000000000000000000000f01fc000000000000000000000000000000000000000000000000000000000000f003f801f0000000000000000000000000000000000000000000000000000000f003f8000000000000000000000000000000000000000000000000000000000f0e1c0001f0000000000000000000000000000000000000000000000000000000f003f8000
  | 0, 8 => 0x1fc3871f000000000000000000000000000000000000000000000000000000001fc3871f000000000000000000000000000000000000000000000000000000001e007f00000000000000000000000000000000000000000000000000000000001e007f00000000000000000000000000000000000000000000000000000000ffffc3870000000000000000000000000000000000000000000000000000000000003c78e0000000000000000000000000000000000000000000000000000000ffe03ff8e0000000000000000000000000000000000000000000000000000000f01fc07f00
  | 0, 9 => 0xffffffffe000000000000000000000000000000000000000000000000000000000003c78e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001e007f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f0ffc07fff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffe1ff80ff
  | 0, 10 => 0xf01ffc78e0000000000000000000000000000000000000000000000000000000001e007f00000000000000000000000000000000000000000000000000000000f01ffc78ff0000000000000000000000000000000000000000000000000000000f1e3fff1f000000000000000000000000000000000000000000000000000000000000001f0000000000000000000000000000000000000000000000000000000fe03fffff000000000000000000000000000000000000000000000000000000ffe0000000000000000000000000000000000000000000000000000000000000f01fc07f1f
  | 0, 11 => 0xfffe007f0000000000000000000000000000000000000000000000000000000000003c78ff000000000000000000000000000000000000000000000000000000ffe1ff80e0000000000000000000000000000000000000000000000000000000ffffc3ffe0000000000000000000000000000000000000000000000000000000000000781f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003c78ff000000000000000000000000000000000000000000000000000000f01ffc7fe0
  | 0, 12 => 0xff1ffff8e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f01fc00000000000000000000000000000000000000000000000000000000000f00000000000000000000000000000000000000000000000000000000000000000003fffff00000000000000000000000000000000000000000000000000000000003c00000000000000000000000000000000000000000000000000000000000f00000000000000000000000000000000000000000000000000000000000000ffffffffe0
  | 0, 13 => 0x3c78e0000000000000000000000000000000000000000000000000000000fffe3c7fe00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffe1c3f81f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffc000000000000000000000000000000000000000000000000000000000000f003f80000000000000000000000000000000000000000000000000000000000000000000
  | 0, 14 => 0xf003f801f000000000000000000000000000000000000000000000000000000ffffffffe0000000000000000000000000000000000000000000000000000000001e007f00000000000000000000000000000000000000000000000000000000ffffffffe00000000000000000000000000000000000000000000000000000000fe003871f0000000000000000000000000000000000000000000000000000000000000000
  | 0, 15 => 0xffe03c78ff000000000000000000000000000000000000000000000000000000001e007f0000000000000000000000000000000000000000000000000000000000003ff8e0000000000000000000000000000000000000000000000000000000ffe03f801f000000000000000000000000000000000000000000000000000000ffe0000000000000000000000000000000000000000000000000000000000000f01fc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ff1fff8000
  | 1, 0 => 0x7800000000000000000000000000000000000000000000000000000000001e0000000000000000000000000000000000000000000000000000000000000fe03f80ff0000000000000000000000000000000000000000000000000000000fe03f80000000000000000000000000000000000000000000000000000000000f003f8000000000000000000000000000000000000000000000000000000000ffe0000000000000000000000000000000000000000000000000000000000000ffe0038000000000000000000000000000000000000000000000000000000000f0ffc07fff
  | 1, 1 => 0xf00000001f00000000000000000000000000000000000000000000000000000000000078000000000000000000000000000000000000000000000000000000000f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000fffe007f1f00000000000000000000000000000000000000000000000000000000003c78e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f003f8000
  | 1, 2 => 0xffe000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffe1ff80ff000000000000000000000000000000000000000000000000000000001e00001f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f003f800000000000000000000000000000000000000000000000000000000000003c001f
  | 1, 3 => 0xffe1c3801f000000000000000000000000000000000000000000000000000000f01fc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001e007f0000000000000000000000000000000000000000000000000000000000003c0000000000000000000000000000000000000000000000000000000000f01fc07f1f000000000000000000000000000000000000000000000000000000ffffc3871f0000000000000000000000000000000000000000000000000000000fe03fffff
  | 1, 4 => 0x3c78e0000000000000000000000000000000000000000000000000000000001fc07fe0000000000000000000000000000000000000000000000000000000ffe000000000000000000000000000000000000000000000000000000000000000003c78e0000000000000000000000000000000000000000000000000000000f0003c78e000000000000000000000000000000000000000000000000000000000e0007fff000000000000000000000000000000000000000000000000000000f0ffc07fff0000000000000000000000000000000000000000000000000000000000007800
  | 1, 5 => 0x3c7fe0000000000000000000000000000000000000000000000000000000001e007f00000000000000000000000000000000000000000000000000000000f0003c78ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f003f8000000000000000000000000000000000000000000000000000000000001e3c7fff000000000000000000000000000000000000000000000000000000ffe1ff80ff
  | 1, 6 => 0xffe1ff80ff000000000000000000000000000000000000000000000000000000ffe03f80ff000000000000000000000000000000000000000000000000000000f01fc00000000000000000000000000000000000000000000000000000000000001e3fffff0000000000000000000000000000000000000000000000000000000f003ff8ff0000000000000000000000000000000000000000000000000000000fe03fffff000000000000000000000000000000000000000000000000000000ff1fffff00000000000000000000000000000000000000000000000000000000f01fc00000
  | 1, 7 => 0xffe00000000000000000000000000000000000000000000000000000000000000f003f80000000000000000000000000000000000000000000000000000000000fe003801f000000000000000000000000000000000000000000000000000000f01fc00000000000000000000000000000000000000000000000000000000000ffe000000000000000000000000000000000000000000000000000000000000000003c78e00000000000000000000000000000000000000000000000000000000f000000000000000000000000000000000000000000000000000000000000000000007800
  | 1, 8 => 0xffe1c3800000000000000000000000000000000000000000000000000000000000003c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001e007f0000000000000000000000000000000000000000000000000000000000003c78e0000000000000000000000000000000000000000000000000000000f01fc0001f0000000000000000000000000000000000000000000000000000000001ff80ff000000000000000000000000000000000000000000000000000000001e007f1f
  | 1, 9 => 0xff1fff80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001e007f1f000000000000000000000000000000000000000000000000000000ffe03c78e000000000000000000000000000000000000000000000000000000000003c78e000000000000000000000000000000000000000000000000000000000003c78e00000000000000000000000000000000000000000000000000000000f003c78e0000000000000000000000000000000000000000000000000000000001e007f00
  | 1, 10 => 0xf003f8000000000000000000000000000000000000000000000000000000000001fffffe0000000000000000000000000000000000000000000000000000000001fc0001f000000000000000000000000000000000000000000000000000000f0ffc0071f000000000000000000000000000000000000000000000000000000ffe000001f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001f0000000000000000000000000000000000000000000000000000000fe03fffff
  | 1, 11 => 0x3c0000000000000000000000000000000000000000000000000000000000ffe03f8000000000000000000000000000000000000000000000000000000000000000001f000000000000000000000000000000000000000000000000000000f01fc007000000000000000000000000000000000000000000000000000000000f003c78ff000000000000000000000000000000000000000000000000000000f01ffc00e0000000000000000000000000000000000000000000000000000000f01fc000000000000000000000000000000000000000000000000000000000000000000000
  | 1, 12 => 0xffffc00000000000000000000000000000000000000000000000000000000000001e000000000000000000000000000000000000000000000000000000000000f01fc0001f0000000000000000000000000000000000000000000000000000000f003f8000000000000000000000000000000000000000000000000000000000000000001f000000000000000000000000000000000000000000000000000000000000001f000000000000000000000000000000000000000000000000000000001fc0000000000000000000000000000000000000000000000000000000000000003c78ff
  | 1, 13 => 0xffe03f800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000007f1f000000000000000000000000000000000000000000000000000000fffffc78e00000000000000000000000000000000000000000000000000000000f003f801f00000000000000000000000000000000000000000000000000000000003c7800000000000000000000000000000000000000000000000000000000f01ffc78e00000000000000000000000000000000000000000000000000000000f003f801f
  | 1, 14 => 0xf1e03870000000000000000000000000000000000000000000000000000000000003c78e00000000000000000000000000000000000000000000000000000000000007f00000000000000000000000000000000000000000000000000000000001fc07fff000000000000000000000000000000000000000000000000000000f01fc00000000000000000000000000000000000000000000000000000000000ffffc3871f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001e007f1f
  | 1, 15 => 0xffe0000000000000000000000000000000000000000000000000000000000000ff1fc0001f000000000000000000000000000000000000000000000000000000ffe03ff8ff000000000000000000000000000000000000000000000000000000001e007f000000000000000000000000000000000000000000000000000000000f003f8000000000000000000000000000000000000000000000000000000000f01fc00700000000000000000000000000000000000000000000000000000000fffe007f000000000000000000000000000000000000000000000000000000000f0000001f
  | 2, 0 => 0xf0e00000000000000000000000000000000000000000000000000000000000000f003f8000000000000000000000000000000000000000000000000000000000ffe000001f000000000000000000000000000000000000000000000000000000ffe0000000000000000000000000000000000000000000000000000000000000f0ffc0000000000000000000000000000000000000000000000000000000000000003f8000000000000000000000000000000000000000000000000000000000ff1fff801f0000000000000000000000000000000000000000000000000000000000000000
  | 2, 1 => 0xfffe007f00000000000000000000000000000000000000000000000000000000f01fff8000000000000000000000000000000000000000000000000000000000ffe000780000000000000000000000000000000000000000000000000000000000003c00e000000000000000000000000000000000000000000000000000000000003c78e0000000000000000000000000000000000000000000000000000000ffe000000000000000000000000000000000000000000000000000000000000000003c78ff000000000000000000000000000000000000000000000000000000fffe3fffe0
  | 2, 2 => 0x1e3c7fe00000000000000000000000000000000000000000000000000000000000007800000000000000000000000000000000000000000000000000000000ffffc00000000000000000000000000000000000000000000000000000000000f01fc00000000000000000000000000000000000000000000000000000000000f001c00000000000000000000000000000000000000000000000000000000000ffffc0001f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001e3c78e0
  | 2, 3 => 0xf000000000000000000000000000000000000000000000000000000000000000f0e1c000ff000000000000000000000000000000000000000000000000000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffe0000000000000000000000000000000000000000000000000000000000000001e0000000000000000000000000000000000000000000000000000000000000fe0000000000000000000000000000000000000000000000000000000000000ffe03f8000
  | 2, 4 => 0xf1e007f00000000000000000000000000000000000000000000000000000000ffffc000000000000000000000000000000000000000000000000000000000000f003ff8e0000000000000000000000000000000000000000000000000000000ffffff80e0000000000000000000000000000000000000000000000000000000ff003f8000000000000000000000000000000000000000000000000000000000001e00071f0000000000000000000000000000000000000000000000000000000f1e007f1f000000000000000000000000000000000000000000000000000000001e007f00
  | 2, 5 => 0xf00038000000000000000000000000000000000000000000000000000000000fffe3fff1f000000000000000000000000000000000000000000000000000000001e007f00000000000000000000000000000000000000000000000000000000f01fc0001f000000000000000000000000000000000000000000000000000000000000001f000000000000000000000000000000000000000000000000000000ffffff8700000000000000000000000000000000000000000000000000000000ffe000001f0000000000000000000000000000000000000000000000000000000001ff80e0
  | 2, 6 => 0xffe000001f000000000000000000000000000000000000000000000000000000f01fc00000000000000000000000000000000000000000000000000000000000001e007f1f000000000000000000000000000000000000000000000000000000f01fc0001f000000000000000000000000000000000000000000000000000000f01fc07f00000000000000000000000000000000000000000000000000000000ffe1ff80ff000000000000000000000000000000000000000000000000000000001e00071f000000000000000000000000000000000000000000000000000000001e007f1f
  | 2, 7 => 0xffe03c0000000000000000000000000000000000000000000000000000000000001e007f00000000000000000000000000000000000000000000000000000000001e3c7fe000000000000000000000000000000000000000000000000000000000000078ff000000000000000000000000000000000000000000000000000000f01fc07f00000000000000000000000000000000000000000000000000000000f0ffffffe00000000000000000000000000000000000000000000000000000000f003f8000000000000000000000000000000000000000000000000000000000001e007fe0
  | 2, 8 => 0x1e0000000000000000000000000000000000000000000000000000000000000f003f800000000000000000000000000000000000000000000000000000000000000078e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f01e007f00000000000000000000000000000000000000000000000000000000ffe0000000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x8f093f92040000000000000000000000000000000000000000000000000000002244bc78e1000000000000000000000000000000000000000000000000000000aa41b200c0000000000000000000000000000000000000000000000000000000fff0204490000000000000000000000000000000000000000000000000000000f93fd6a97f000000000000000000000000000000000000000000000000000000449e097f020000000000000000000000000000000000000000000000000000003366fc78f900000000000000000000000000000000000000000000000000000070f6c06dfb
  | 0, 1 => 0xbb61f680fd000000000000000000000000000000000000000000000000000000cc9b43870e000000000000000000000000000000000000000000000000000000000d9b32400000000000000000000000000000000000000000000000000000008f06e0296b000000000000000000000000000000000000000000000000000000112244893f00000000000000000000000000000000000000000000000000000007e02ddfb7000000000000000000000000000000000000000000000000000000fff2244db3000000000000000000000000000000000000000000000000000000f81fd22048
  | 0, 2 => 0x9f0b7f920c00000000000000000000000000000000000000000000000000000006c0295680000000000000000000000000000000000000000000000000000000f81fd62869000000000000000000000000000000000000000000000000000000000fdfbb6f00000000000000000000000000000000000000000000000000000055be4dff3f000000000000000000000000000000000000000000000000000000fff0244cb1000000000000000000000000000000000000000000000000000000cc99030600000000000000000000000000000000000000000000000000000000112d9b3250
  | 0, 3 => 0x992b56893f0000000000000000000000000000000000000000000000000000000000000923000000000000000000000000000000000000000000000000000000fff024ccb50000000000000000000000000000000000000000000000000000008f0b3f9b27000000000000000000000000000000000000000000000000000000fff93fd694000000000000000000000000000000000000000000000000000000af4dbffae5000000000000000000000000000000000000000000000000000000cc9d9b3640000000000000000000000000000000000000000000000000000000ddbb43871e
  | 0, 4 => 0xefdfbfffe7000000000000000000000000000000000000000000000000000000ead5b264c0000000000000000000000000000000000000000000000000000000cdb9038716000000000000000000000000000000000000000000000000000000fff264cdbf00000000000000000000000000000000000000000000000000000055be0dff1600000000000000000000000000000000000000000000000000000077fe297f9200000000000000000000000000000000000000000000000000000052b27c151a000000000000000000000000000000000000000000000000000000eeddbb76c0
  | 0, 5 => 0x4491d6c46d00000000000000000000000000000000000000000000000000000061d484e4c40000000000000000000000000000000000000000000000000000003246fc78e9000000000000000000000000000000000000000000000000000000f91fd6a04c00000000000000000000000000000000000000000000000000000060d48064c0000000000000000000000000000000000000000000000000000000fff4bc7cf1000000000000000000000000000000000000000000000000000000336264c9bf000000000000000000000000000000000000000000000000000000fa5ff260c8
  | 0, 6 => 0xcf9f3fff06000000000000000000000000000000000000000000000000000000fffffff6dc000000000000000000000000000000000000000000000000000000fffb76cdbf000000000000000000000000000000000000000000000000000000fffffb7fda00000000000000000000000000000000000000000000000000000055b244cd3f000000000000000000000000000000000000000000000000000000fffff264d8000000000000000000000000000000000000000000000000000000aa4dbe78e10000000000000000000000000000000000000000000000000000003346fcf8ed
  | 0, 7 => 0x66debd7fe30000000000000000000000000000000000000000000000000000003126d4a97f00000000000000000000000000000000000000000000000000000005a0018716000000000000000000000000000000000000000000000000000000f91fd6a94e0000000000000000000000000000000000000000000000000000009f2b7f9b3f0000000000000000000000000000000000000000000000000000009f0b7f9b0e00000000000000000000000000000000000000000000000000000014284912180000000000000000000000000000000000000000000000000000008f0b3f9b06
  | 0, 8 => 0x224b63c38e000000000000000000000000000000000000000000000000000000000b43830e000000000000000000000000000000000000000000000000000000459e0dff27000000000000000000000000000000000000000000000000000000559e4dff0e000000000000000000000000000000000000000000000000000000cc99070e210000000000000000000000000000000000000000000000000000003364bc78f1000000000000000000000000000000000000000000000000000000fffdbffef5000000000000000000000000000000000000000000000000000000fc9fdb7f4a
  | 0, 9 => 0xeeddbb76c00000000000000000000000000000000000000000000000000000003364bcf8f5000000000000000000000000000000000000000000000000000000110244800c00000000000000000000000000000000000000000000000000000055be097f12000000000000000000000000000000000000000000000000000000449a095f0200000000000000000000000000000000000000000000000000000072f6e06dfb0000000000000000000000000000000000000000000000000000001120000010000000000000000000000000000000000000000000000000000000aa41f680ed
  | 0, 10 => 0xfa5ffe78e900000000000000000000000000000000000000000000000000000066deb97fc2000000000000000000000000000000000000000000000000000000fb7ffef9ff000000000000000000000000000000000000000000000000000000dfbf7fff3f000000000000000000000000000000000000000000000000000000152a4d9b3f00000000000000000000000000000000000000000000000000000027e02ddfb7000000000000000000000000000000000000000000000000000000fff024c49400000000000000000000000000000000000000000000000000000070b6c06d7b
  | 0, 11 => 0xfffe297f92000000000000000000000000000000000000000000000000000000376efdfbff000000000000000000000000000000000000000000000000000000aa43b209c2000000000000000000000000000000000000000000000000000000ecdd8366c000000000000000000000000000000000000000000000000000000011264cf93f00000000000000000000000000000000000000000000000000000000000408210000000000000000000000000000000000000000000000000000003366fcf9ff000000000000000000000000000000000000000000000000000000fedfff7feb
  | 0, 12 => 0xff5ffffaed0000000000000000000000000000000000000000000000000000000408091200000000000000000000000000000000000000000000000000000000fc1fdb3248000000000000000000000000000000000000000000000000000000f81000000000000000000000000000000000000000000000000000000000000000000d9b2700000000000000000000000000000000000000000000000000000002003c18210000000000000000000000000000000000000000000000000000008f08291200000000000000000000000000000000000000000000000000000000aa4dbb32c0
  | 0, 13 => 0x264cbd7ae1000000000000000000000000000000000000000000000000000000fffebd7ff3000000000000000000000000000000000000000000000000000000010004882500000000000000000000000000000000000000000000000000000099254af81c0000000000000000000000000000000000000000000000000000001122400018000000000000000000000000000000000000000000000000000000fffff6e4dc000000000000000000000000000000000000000000000000000000af0dbfb2440000000000000000000000000000000000000000000000000000002004902040
  | 0, 14 => 0x20409230000000000000000000000000000000000000000000000000000002244b060c0000000000000000000000000000000000000000000000000000000dfbb7fdf3f00000000000000000000000000000000000000000000000000000066d4a976c000000000000000000000000000000000000000000000000000000066de297f82000000000000000000000000000000000000000000000000000000ced92b568000000000000000000000000000000000000000000000000000000025a491a7560000000000000000000000000000000000000000000000000000001002440829
  | 0, 15 => 0xfff6fcfdff00000000000000000000000000000000000000000000000000000066de2d7fa3000000000000000000000000000000000000000000000000000000224dbffae5000000000000000000000000000000000000000000000000000000fffb7fdfbf000000000000000000000000000000000000000000000000000000fff82dd694000000000000000000000000000000000000000000000000000000f81fd6296b0000000000000000000000000000000000000000000000000000008809120000000000000000000000000000000000000000000000000000000000ff1fffb24c
  | 1, 0 => 0x2004987840000000000000000000000000000000000000000000000000000000401e00200000000000000000000000000000000000000000000000000000000003602480b50000000000000000000000000000000000000000000000000000008fe93fd694000000000000000000000000000000000000000000000000000000af493fdaa5000000000000000000000000000000000000000000000000000000fff8295690000000000000000000000000000000000000000000000000000000fff923c69400000000000000000000000000000000000000000000000000000070f6c065da
  | 1, 1 => 0xf93244893f00000000000000000000000000000000000000000000000000000000040878000000000000000000000000000000000000000000000000000000008f002000000000000000000000000000000000000000000000000000000000003006d02048000000000000000000000000000000000000000000000000000000fffe6dffbf00000000000000000000000000000000000000000000000000000066d6bc7de30000000000000000000000000000000000000000000000000000004492004d020000000000000000000000000000000000000000000000000000009f2b3f9b16
  | 1, 2 => 0xfff4b064d0000000000000000000000000000000000000000000000000000000980b5200080000000000000000000000000000000000000000000000000000001120048014000000000000000000000000000000000000000000000000000000bb61f280dc000000000000000000000000000000000000000000000000000000513e44a93f0000000000000000000000000000000000000000000000000000001122000912000000000000000000000000000000000000000000000000000000cf993fd60400000000000000000000000000000000000000000000000000000013227c993f
  | 1, 3 => 0x992142801c000000000000000000000000000000000000000000000000000000fdbfd26458000000000000000000000000000000000000000000000000000000040a091b02000000000000000000000000000000000000000000000000000000459e0dff0600000000000000000000000000000000000000000000000000000022403c5080000000000000000000000000000000000000000000000000000000fdbfdfff7f000000000000000000000000000000000000000000000000000000dcbb43071a00000000000000000000000000000000000000000000000000000003e024cdb7
  | 1, 4 => 0xab4dbef8e5000000000000000000000000000000000000000000000000000000449e897f42000000000000000000000000000000000000000000000000000000fff6f064d800000000000000000000000000000000000000000000000000000066d4bc7ce1000000000000000000000000000000000000000000000000000000fa54bc78e100000000000000000000000000000000000000000000000000000000e0004db300000000000000000000000000000000000000000000000000000050f2404dbb0000000000000000000000000000000000000000000000000000004494087c00
  | 1, 5 => 0x26c4bd7fe3000000000000000000000000000000000000000000000000000000cc9f1b7f02000000000000000000000000000000000000000000000000000000fb76fcf9ff00000000000000000000000000000000000000000000000000000022402040800000000000000000000000000000000000000000000000000000000002000902000000000000000000000000000000000000000000000000000000af493fd28400000000000000000000000000000000000000000000000000000077fefdffff0000000000000000000000000000000000000000000000000000009921d6807d
  | 1, 6 => 0xbb61f6c0fd000000000000000000000000000000000000000000000000000000bb602480b5000000000000000000000000000000000000000000000000000000fc9fd26448000000000000000000000000000000000000000000000000000000000e0dbb27000000000000000000000000000000000000000000000000000000bf6ffffbff00000000000000000000000000000000000000000000000000000003602d9bb7000000000000000000000000000000000000000000000000000000ff9fffff4e000000000000000000000000000000000000000000000000000000fb7ff260d8
  | 1, 7 => 0xfff2204d920000000000000000000000000000000000000000000000000000009f293f92140000000000000000000000000000000000000000000000000000000120008014000000000000000000000000000000000000000000000000000000fa5ff668e9000000000000000000000000000000000000000000000000000000fff4b46cf1000000000000000000000000000000000000000000000000000000ba4ffe78e90000000000000000000000000000000000000000000000000000009f202000100000000000000000000000000000000000000000000000000000002244287880
  | 1, 8 => 0x880102000000000000000000000000000000000000000000000000000000000002003c10000000000000000000000000000000000000000000000000000000004490004400000000000000000000000000000000000000000000000000000000649e9d7f6300000000000000000000000000000000000000000000000000000077f4bc7cf1000000000000000000000000000000000000000000000000000000fb7ff6e9ff0000000000000000000000000000000000000000000000000000000001d6806d00000000000000000000000000000000000000000000000000000075beddff7f
  | 1, 9 => 0xee1dbb324000000000000000000000000000000000000000000000000000000077f020449000000000000000000000000000000000000000000000000000000054be497f3b000000000000000000000000000000000000000000000000000000fff4bcfcf50000000000000000000000000000000000000000000000000000002344bcf8e500000000000000000000000000000000000000000000000000000002402c58a1000000000000000000000000000000000000000000000000000000af44bc78e1000000000000000000000000000000000000000000000000000000549e497f0a
  | 1, 10 => 0x8e093b1200000000000000000000000000000000000000000000000000000000449f9b7f42000000000000000000000000000000000000000000000000000000000fd6a96f00000000000000000000000000000000000000000000000000000050b240051a000000000000000000000000000000000000000000000000000000fff6f4edff0000000000000000000000000000000000000000000000000000000100048004000000000000000000000000000000000000000000000000000000112240811e00000000000000000000000000000000000000000000000000000007e02dd6b5
  | 1, 11 => 0x3003c9004000000000000000000000000000000000000000000000000000000fff02dd694000000000000000000000000000000000000000000000000000000000244892f000000000000000000000000000000000000000000000000000000fc9fd3274a000000000000000000000000000000000000000000000000000000bf66fcf9ff000000000000000000000000000000000000000000000000000000fa5ff620e9000000000000000000000000000000000000000000000000000000f93fd22058000000000000000000000000000000000000000000000000000000100240090a
  | 1, 12 => 0xfffffb76d8000000000000000000000000000000000000000000000000000000601e902040000000000000000000000000000000000000000000000000000000fdbfd6ed7f00000000000000000000000000000000000000000000000000000007002d92040000000000000000000000000000000000000000000000000000000120048937000000000000000000000000000000000000000000000000000000112044803d000000000000000000000000000000000000000000000000000000000fd220480000000000000000000000000000000000000000000000000000002364bcf9f7
  | 1, 13 => 0xfff93b5690000000000000000000000000000000000000000000000000000000336020409000000000000000000000000000000000000000000000000000000005a00ddf37000000000000000000000000000000000000000000000000000000fffffe7cf90000000000000000000000000000000000000000000000000000009b2376893f00000000000000000000000000000000000000000000000000000002043c7800000000000000000000000000000000000000000000000000000000ea5dbe78e1000000000000000000000000000000000000000000000000000000bf6b7fdbbf
  | 1, 14 => 0xcd9b0387060000000000000000000000000000000000000000000000000000002244b870c00000000000000000000000000000000000000000000000000000000480095f020000000000000000000000000000000000000000000000000000000006c0296b000000000000000000000000000000000000000000000000000000d81b420008000000000000000000000000000000000000000000000000000000d9b342851e00000000000000000000000000000000000000000000000000000005080d920400000000000000000000000000000000000000000000000000000077fe6dffbf
  | 1, 15 => 0xfff9324490000000000000000000000000000000000000000000000000000000ff3ff6a97f000000000000000000000000000000000000000000000000000000ffffffffff000000000000000000000000000000000000000000000000000000649e997f420000000000000000000000000000000000000000000000000000008b01368004000000000000000000000000000000000000000000000000000000dc9b43070a000000000000000000000000000000000000000000000000000000fffe697f9a0000000000000000000000000000000000000000000000000000009f2264893f
  | 2, 0 => 0x70f0004490000000000000000000000000000000000000000000000000000000bf0fffb24c000000000000000000000000000000000000000000000000000000ddb240851e000000000000000000000000000000000000000000000000000000eed0204480000000000000000000000000000000000000000000000000000000f8ffd264d800000000000000000000000000000000000000000000000000000000091f9204000000000000000000000000000000000000000000000000000000ff3fffbb7f0000000000000000000000000000000000000000000000000000001002400008
  | 2, 1 => 0xeede297f82000000000000000000000000000000000000000000000000000000f81fdfb24c000000000000000000000000000000000000000000000000000000fff4287c900000000000000000000000000000000000000000000000000000002240b400e10000000000000000000000000000000000000000000000000000002246bc79e3000000000000000000000000000000000000000000000000000000bb6020009000000000000000000000000000000000000000000000000000000077f6fcfdff000000000000000000000000000000000000000000000000000000ffffbffff7
  | 2, 2 => 0x62d6bc7de30000000000000000000000000000000000000000000000000000000006087902000000000000000000000000000000000000000000000000000000fffff26dda000000000000000000000000000000000000000000000000000000f81fd2294a000000000000000000000000000000000000000000000000000000b801d20048000000000000000000000000000000000000000000000000000000fffff6edff0000000000000000000000000000000000000000000000000000002244b468e1000000000000000000000000000000000000000000000000000000625ebc78e1
  | 2, 3 => 0xf9300000100000000000000000000000000000000000000000000000000000003060c000f9000000000000000000000000000000000000000000000000000000fa502040800000000000000000000000000000000000000000000000000000008909168004000000000000000000000000000000000000000000000000000000fff2604498000000000000000000000000000000000000000000000000000000441e09320000000000000000000000000000000000000000000000000000000007e0204490000000000000000000000000000000000000000000000000000000fffb7fd69c
  | 2, 4 => 0xcf9e297f02000000000000000000000000000000000000000000000000000000fedff264c8000000000000000000000000000000000000000000000000000000af4fbffbe7000000000000000000000000000000000000000000000000000000fa5ff220c8000000000000000000000000000000000000000000000000000000ff193f920400000000000000000000000000000000000000000000000000000055ba41871e000000000000000000000000000000000000000000000000000000dfbe6dff3f000000000000000000000000000000000000000000000000000000000e093b02
  | 2, 5 => 0x8d09038204000000000000000000000000000000000000000000000000000000ffff7fffbf0000000000000000000000000000000000000000000000000000004096006d02000000000000000000000000000000000000000000000000000000d93b42811e000000000000000000000000000000000000000000000000000000102240093b000000000000000000000000000000000000000000000000000000cf993f9604000000000000000000000000000000000000000000000000000000fff2604dbb0000000000000000000000000000000000000000000000000000000001920040
  | 2, 6 => 0xbb606480bd000000000000000000000000000000000000000000000000000000fd1fdfb24c00000000000000000000000000000000000000000000000000000055be49ff1e0000000000000000000000000000000000000000000000000000007036c0297b000000000000000000000000000000000000000000000000000000ec9d9b7640000000000000000000000000000000000000000000000000000000ba61f200f900000000000000000000000000000000000000000000000000000055ba458f3f00000000000000000000000000000000000000000000000000000051b644ed3f
  | 2, 7 => 0xfff03c5490000000000000000000000000000000000000000000000000000000449e0d7f23000000000000000000000000000000000000000000000000000000eedfbf7fe30000000000000000000000000000000000000000000000000000003166c4e9ff000000000000000000000000000000000000000000000000000000fedffb7fca00000000000000000000000000000000000000000000000000000060dd9b76c0000000000000000000000000000000000000000000000000000000bf693fd29400000000000000000000000000000000000000000000000000000064de897fe3
  | 2, 8 => 0x401e0029020000000000000000000000000000000000000000000000000000008f093f9a2500000000000000000000000000000000000000000000000000000020448068e100000000000000000000000000000000000000000000000000000055b0004410000000000000000000000000000000000000000000000000000000fc9e097f02000000000000000000000000000000000000000000000000000000ddb0000410
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 326 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 326 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 326 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 326 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 9 0) :: stateWiresD n (ids >>> 9)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 9 0) :: stateWiresS n (ids >>> 9)
def SD (s j : Nat) : List (Nat × Nat × Nat) :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresD (packed &&& 15) (packed >>> 4)
def SS (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWiresS (packed &&& 15) (packed >>> 4)
theorem stateWiresD_eq (n ids : Nat) :
    stateWiresD n ids = (stateWiresS n ids).map (fun w => (w, projBit r1sG w, projBit r2sG w)) := by
  induction n generalizing ids with
  | zero => rfl
  | succ n ih => simp [stateWiresD, stateWiresS, wireSAt, wireDAt_eq, ih]
theorem SD_eq (s j : Nat) :
    SD s j = (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w)) :=
  stateWiresD_eq _ _

def htAt (s i : Nat) : Nat := fld (HT s (i / 64)) 32 (i % 64)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 11 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 5 => 83
  | 6 => 689
  | 7 => 1192
  | 8 => 197
  | _ => 0
def CH : Nat → Nat → Nat
  | 5, 0 => 0x3af747523abf7e5b36887bb132dec1332f9a97832f8389112cde2a2c2b93dcd72b1f1a362af54b082a0df81428d7f3c027eed9c727d4578c279712ef274bb9eb24de996622f1c674209f6f761ee69e011e4a78b01d9f20d41c768bba1b70749818704260185d73c517d03ea216d917bd15ef68e515a819e313b4709112ec1fb812306730120feeaa11ea3d24114ebb1a11478c3f1102b1b4103c76e9102493bc0f6bb11b0ea733580e5e63150e41bacf0dc02f8f0d3faa8e0d206e660b44b4360b2d5a6b0b1298e70b0643fc091987c608eecbfb088b2a6c0727620106f786ca06577d4905c9b0b403062a2902e354b502ceffe002b1583802aec935008169c2
  | 5, 1 => 0xa5e8478289696dcd797c0213611d73bd5fe9ed715bcbf8395a87e5f15a7788dd58e13c5853ea782451a40ceb4cd75e004a7584eb4674b52643c8310b4184eeaa3f02519e3e19300f3d214f93
  | 6, 0 => 0x4e587be04e437fd04b88c2b04b2efae04a98e2004a48fc50496165b0489427f0486c585047c71240446c582043a8655041b54f604173c1604167c5903ff6a6f03d6a79c03d201c103d0fb3c03cdafc403c5a40d03770d530360c75a0349bb5e02ed76e002e58f2b02d338cd02c94b9a02c912bd02c256eb029fc0b9029b3eb6028ef692028c2f0b0282416a026aed280262e26f025f10850251cf7a0250646b0231bf31022416c00206798801f914f501cb040901c02121019fe3bc019d119b0163189c015c7936011a8e44010c7f3d00d677b900d2c4d700bf18a700ae951800a95b240091daa4004aa3d60046e4ed00412c3d003e89ff003ca43e0010041b
  | 6, 1 => 0x979a5d309583c290952c7e2094cec4209185426090a37110905670508f7f14308f40b1b08bb56c808ad139f088cedd70881bfb8087fcca408770ba60872a45508707bd2086ba10a083deb500825ce0e081dc834080f25b007dd4fa807d0680207cbaed307c974a807bf110f07b18e4b079ce559078aa6e8077f82f30740f9780739e7fc072b8745071ee5b7071cc81007198c070711348a070b6e2706e5324d06e4120e06d9a45606d880bd06c6d9d006a40df30656511b063eb569062aedd3060fc959060d28c705ff187405f3a13e05d9de1805bb94a90598c5ad05811f320573298d055b34bd0558271f055323a505489cc40514ad1204febc9904ee497a
  | 6, 2 => 0x1013128c100211c60ff0a3a60fb71aff0fb28dd10fb1193a0f829e5e0f6174440f4527f60f27dc140f14bd410f0df8fb0ef102130eccb7400eb67df00e9fc0db0e9214770e4ec9a10e2be0630dff31450dda3cec0dcf85ae0dccde940dc02f8f0da501c20d83a50c0d705e4c0d6e65f60d6b472b0d6365870d0b76e30d0aaccc0cf7765c0ced3a210ce8e1d80ccca2390cb084e50ca9b94f0c76b2fc0c6a061c0c5aa15f0c3165330c2b2ad90bdadfef0bd88d5a0bc500b50bb868730b78f2cf0b497d930b283fd80b25f4c10b2180270b0d22f20ab90b9e0a7a72560a703ea40a33c9650a2303e40a09563509f05b0c09cf589909be471009a9f76109a3d92c
  | 6, 3 => 0x1615b491160befb3160be53615e9940615e07c9415c8eab715a29c41159e8940158d7e83158b10bf153a0472153315f2152aeaef152894da1504458814e4974614d66da11495e02c14931536146b8c3f1461d1371447a38e142fd87414230f881407801813fd1f6e13fb1c6a13f2ead713c885491385f3fe13810b82137d1694133b127a131b153c13184b0412e9657212e2b22b128e14221242351f1214f0d9120feeaa11f7fb6711983cf4119459bb11719df2116be9da11285c89110f775d110c7901110a6dff10fe1f3810e6ef5f10d2472810d1afae10cf6e2e10c63b4a10b97da6109911fc10835138106f32011067322d1064c20d1050401b10462057
  | 6, 4 => 0x1c61cb871c3edbed1c0316c31bb9f6c01b955ea21b8281ef1b7710261b609aaa1b32c92d1b0bd8191affc6121ae554351a9a86021a7dc6081a7331e11a2c019b19b9c8681996d3a01964efb11964d378195c328319485b0c1916829d1906f09d18edcf5218d6b6df18bd49cc18bb42ad18af80cd185ae1601858c0a3184d71d41845cab8183d5a6b17f4260017c9d31e17ba9f9317ace86d17a101581783d36c1782dbd417802805177c24c61765f31f175fc7a61744ac411721cb3717015c7216dee14316d1a88d16ccd75f16bc18fe16b7bd0716ab8c8d1682f921166be595165d2f9b165701d0164cdf49164cd1711638a69a163694bf161c34951618a86e
  | 6, 5 => 0x2374b284236dd296236a7fa8232f66fe232cbacb22fa285722f7085c22f32c9722cb4d0d22abcb4422508f1622502a7f224f4a542226504722057d7b21fbb8c821df3d1d2183dc4121615074215a91f0213c10992129e587210826392100902d20ef398220d921aa20d8c04520b30561208a8efc205713b7203020341fe205301fe10dfc1fdef4131fde28751fdd18991fbc85101f8b04051f0c092f1eea2a391ee36c6c1ec054711e6c983a1e215ac11e10a1721e06cafd1df000af1de116e81dcbf19e1dca59811db7f4151daf23d21d7c73511d5b97f41d50e4ea1d4c83ba1d3892091d30b2eb1d2f3b941d116eb11cec23b51cb9e6b01cb88b5f1c95f7d5
  | 6, 6 => 0x2e74b9152e5701362e2837842e0bcca52e00a7792db7c00f2d9b40532cfd4cb22c9ef41c2c6f9da32c6593332c62e6d52c5e54df2c1fb7682bf6794a2be5f3fb2b4f69f52b38c7742b2e8b242b00ec7e2af926f52abf04d12aa6546e2a836b2f2a5f178b29ec033029c5e2c329bd53ce29982fed29635a192901240a28f497c528dacd8728d6087228d427a8288899a12868c675285edda1281d3cc02811b2b727e49567272ee6e7272b4f0726cfb50a26c1d593266a57682667716326121912260756dc25fa3fed259e5ab025932370254f63322544cb8525368d682526120924df4c9e24dc4a8924d9cda724d836c72470566623cd54fa2387b4f023835c17
  | 6, 7 => 0x39b2d81e399b6b423967b4d438c294a838b9625a388a78f7381aa4aa380b058f3808868d37f46bb0379c2fd2372767023723f98a36f111dd3690e87b365ad9b735adfb61355ce181351e06e534bd11df34bb44be34ab5128347817ff34736aa63470f13a34666b693460efb63456a4b434127ccc33acca93339a36b6338e538b3379e4f333761bd933697a67332ff082331a7faa330bd1fa3308b54b32eec14b32dcbebe3258c5ce324f8518322895b232124cbd3204226431ff90e931e978d131d548db313736ce30efa4b730b17a1b30ab2653308b8d4b3052c5db303373852fec249a2f77968f2f6155352f5d89fe2f3679eb2f2c6ffd2eaac7592e9f17e8
  | 6, 8 => 0x47e80dd94791fa5c475d2eb4475962ae473ca83a46f99297469a00e0466fc4f7466496c545bfd2144584b1bc458265bb456b353045171037450e3cf744be9bbd4494201243cca41343706e9b4365bd3742cfc309429a249b42371c4f422d532141f44f354188d6894173263f413870484126cadd410d282340dc393040766d7f404296163efccea83eebff8f3ebe4adb3eb752293e6edb873e51fe3b3e4a58b53e32b2353e2743bd3d5352743cdab6253cd6190a3cb625373cafee803c76559f3c38b2173c07c4dd3bcc4b8e3b5c06d43b565e153b45c1bd3af777873ad1f5463acbd1773ac119a03aa1aa6a3a9af2043a75cc833a57a61e39ec9a3e39e8c164
  | 6, 9 => 0x66063cb2657e37b6653d59ad6480965162afdfb5620fe41561963c785f31b6b85ee8f0a85ecf3e455dcca36d5dc3cdd35d92f88e5ce16beb5cb1fe155bf69d8e5bce51b95b6c088b5b00f2a558a5bb2857ec096e5789bea3571b125f56b51528560596cd55f2918a55aa1a5055614b865511616d54af0e2654ae7981545d943453da5ec753ad9f7952cb67f95253886251f280be4fdecd1d4f863a0f4f7559824f02fe524eb7e6524e881d3e4e681b594e4b60e54e1594024d87e54b4d0196dd4cff85024cda37c74caa6c484b73f32f4af193184ae3c8134a4343e749e282cf49c80e9649a4ba1c493bf4dc492e513d48ea497248d937e748a4403f485326f6
  | 6, 10 => 0xcea1ffb3bf774553b68d3f41b03b1c5faeec9bcaaa33b18aa7e6b62da40a703691db2e508fa1088c8dfe79d68cd6b49d8b4eeeb38ada9f858ab2318f889f1ccb8277192481ba835b819b4b0880fdd7427f5540ab7eb3e21e7e5dc07f7cd86cd17b7902c07b73065079951c5e7975219a7960b5c678ed702f78e4d34078101b43758c4b0474289a007423dda97309227571a8d4f071382dc67096d0c66e63675c6d7385ff6d1524fe69904ec968fbb076680aa95967b8508d6765c9fa675059e167353b4c
  | 7, 0 => 0x371beab036321e00343f594032ca92b032ad7b0031029e102fbbdeb02f5fddb02e42d5302df9ee002d7e51b02d3625402c7e1c602c57eb202c2c7cf02c256eb02a4c08f02a36d9d0298e12a028e48480265ec620263fddc024b5a4102463e47023e56a5023de7c802210919021dfac8021bff8a020a3495020343d901fde65c01f9a20601f7725301eb76ea01e7038d01dfe0b301c289d901ace790019f51af019520ef017961310178a597016dcd98014657c0012d94cb0129179e01189fc601185c610104396601035fe800fda5aa00fb7f9100d64fc300bd6281004aa5ad00412c3d003a955e002f48270025265100242408001c45a1001611440014ac10
  | 7, 1 => 0x5d82c6c05d2cb9505b8ad5a05b329cf05a8bf0c05a02dba0584e5c605640497055450540544cdf605406a460532d237052d9e0f050f8f19050deacb05032bb404fa6d9d04ee497a04ede40504ec2fca04e70ca904e6013d04dbe27c04d4175504d064d104c9b54f04b2efae04b1bc0e049fe5830499b2c1047e8d1504715e16046f348304675516046531a90451cc9a043f6445043502bc042978390405c082040486150402104d03fcd6e203f5a31803edab4903e863b503e0152903ddb4b703d42f3f03d0d83403c8775403be42c303b92f8603b6a79003afd08103af162503ad58cf03ab96e403a9625c03a7a7ad039e9771039a82b703887dd8037feef9
  | 7, 2 => 0x8bd92c00892763f08915f04088f8c2f088ec9d50883b66b087d45640878803008754700082d470a0828fed7082470f7081475360801277907f2e66c07e60fd707d513eb07c8d1c207ad9e1307a1618d07a09209078e9574078cc03207852a5a0778512e07780a8f075f54fb0758d02607540f080750f592074e33b20749dc20074491b00740f978073e6337073325e00700687906f34a7f06e4120e06e0c14b06dd1a6f06d79cfb06d33f7406d133fa06c6272f06b6b95906afa0d906a6e2bb06a471e50694c235068d4b130682030e0672c3e8065b88aa06487f4b063719b70626d8910618f4030612365d05f6b71805eac08505e0f05005dba0bf05db450a
  | 7, 3 => 0xba8a9e60ba5a4d20ba2b5cf0b8caf690b8bbf6b0b8301230b7770420b760dc10b70e1e80b66943c0b619aaf0b53118e0b49b0210b4595710b414e1e0b24a2690b0d46330afaed940af848bf0af6227c0af1588d0ae4e73e0ad79ab60accf95f0accc2510acc9fe20ac78f9b0abdb32f0aba57dc0a61674a0a52f1e50a51d1c70a5133e10a49c2db0a35091a0a2d480b0a2632930a200d4a0a0eeb5709d69a7109d41c9d09c8d28f09baeccb09b0b8780993718c098a34cd097b206e097a53e009618cf2096007a60958e6e8095537f9094cec42094b9571094b711c094a91aa093db6800931d2630918ed40090b2c30090422d808fdf28908f2644d08c012b3
  | 7, 4 => 0xe56b56b0e499dbe0e4719060e4468b30e41de8b0e3e77060e29ee160e22de870e0b84730dfa82c30dea41370dde4b6f0dda1f680db9ad4e0db6ae630db3a33c0db338d30daeef0b0d97b0ef0d8f4d4d0d8687440d83a50c0d6f1a4b0d6a41550d5babb30d4c96070d359d660d31a8270d2e8f990d1f677b0d16e72c0d152e4a0d0b05da0d0994b80ce117920cd494d50cd3e9650cd020e50cbb9b490cb2e1170cac17b70c9f1b370c98ae110c9328990c91dae20c854abc0c7515ce0c684c340c4eb6810c4d96010c3b0d7b0c23ba7d0c1f09b30c11c00d0c10da480c0ce0890c0600430bf7de240bf1fbec0bdf8fea0bd00f4f0bbea25c0bb355150bac8394
  | 7, 5 => 0x1194d57e11932b791183546d1165c3021158bc8d11418fe4113c00b6112ec5f5112e07291117f300110fc782110c69a71100bba210f31c5810eed49110c9a57610c7913810ae3699109d794c109aa9431098793310873aff1082e40b107eac711077ed451072fc5e1056c74b104dd56b10494ce710391595101cf3100ffd599a0fe3bfab0fd8b3870fd4c59b0fcc143d0fb9c5eb0fb19ba80f9f8c4e0f88b3880f7d0cdf0f66eb650f52f7e70f44efe30f4449ac0f27162b0f1d523d0ee047db0edabba70ed4b88e0ecd7e060eccb7400ec37ec90eabbbcd0e9b4d760e8e44ca0e8ab2870e86711a0e7b5b730e7871670e73d9ef0e68f5ce0e68bc0a0e61175a
  | 7, 6 => 0x159c89ed159b56a615930133158cf5071585bdc91585b988155d1ba415554fd01548cb761542379b153315f215303b88152d86e31515e2611511f02a14f4acfd14e6f9fa14d57a2914b7efae14b7c4bd14afea85147387c8146dd678146907d9145fccb3145be6f11454aa95144456111410a821140984d713e9376613e34d8013b13c8e13ac2e7a139e8f9613997a1e1387c0481383ce79135fcdb11345c7c513422a8c131d3b5413184b0413181fe312ed65f812e220cf12d9123b12c5aae212b62121128628ed1255565b124c5a831238304e123727b51231c29f122e34fb122bc8a91229b727122391de1205328f11f546a611c9fc5911a20b2a119a2057
  | 7, 7 => 0x195e4838195708111937c60519324a89192f3fd61929eff618f5929718f4e10a18ce2c7618c367c318bc18ae18baa09918b98c2018a28870189246be18721382186b8f5c1867f91c184e84e3184d71d41843d43e183e41311805cbd217f4260017ecd99c17d58bc317cf99f217c2485d17bee38a17bd685317bc20f017acc8a517a485a017919cb617803e9d17802805177ed454176a6ff9176707ad1765f31f174309b4172babbb171e0abb1702826617015c7216f8c3a616e53d6716e3f63b16c7550716c4ecbb169ad4dc167ebc1d1635ced6162c9eb5161ad833160e52821609134215f6076a15e2d06915dc7c8415c5698315b8d2ee15aaf6f5159e41e5
  | 7, 8 => 0x1dd9276e1dc7c5df1db48e521daa88951da1c6791d7fe65b1d714dfe1d57bc371d48e0fa1d3526381d2535041d1ff9bc1cfddd5e1cbc51791ca64f5b1c92106b1c90119b1c8d91dd1c711fd81c6686f61c54452b1c2a84421c166f5f1c0feb111c0377111c02e4e51be597ef1bdb1f341bd07d241bb8628c1bb5a1481b8240731b77905d1b55c5ef1b3609e11b23c71b1b0cee2b1b01564c1af7262a1adb9ef91acb72991ac426e21ab708871aa077081a9a638c1a939d131a8bc8ff1a7ee44a1a63bf4d1a3c6d051a28899f1a190bd81a0fd8341a09085a19fbd81019dee4d419da568f19bab7be19b9c86819b7d66c19b15e6819728323196939d2196926bf
  | 7, 9 => 0x22b12ef022696ae82254b62c224a07432232fccd222a6a2d22272e9b2222d264221f408b22034eb621c06e8b218b094a2185dc372181ace6217de2142171d801216f8e38216cd56f21677a512164fee0214d3e85213fe88e2132c46a2125b167210940e420fdc49f20fce69520fb4f1320d6bd8420b6d82820b45b6820b14afe20a37ff7208cb324206d00e32059c65c204cfb9c2014b88420134c372003aca51fe205301fce16b31fc882a41fc1b3651fa4671a1f90ec081f865e5b1f4d462b1f2f304f1f17eaae1ef21b201ebc9cbe1eb906901ea89fbe1e9a33da1e9742441e6e6ef41e5acd281e56cbc31e30bcd41e1b2e8b1e0c97d61df4fadf1df000af
  | 7, 10 => 0x289b7f932898a3ce289037b82885da4d2868c675285eafc828508030282e0aca281e7a94281da14c27e4956727d6d48b27d6774d27c0bc9727c003a92794709c2718f8a726de0b2926d06c1026a6ede526893acd2688f48d267c8539266d2ce42613f6fd26099ed525fd7cc625f87f7325c7bf3b25c57f8825c5372925b75869259918d02597e26925836aef257d279f256ad9fc24fe889724e5436124d5ba0324c9c37e24c4815c24bff09524a4de90248db16a2474a46c2461748c245dbecd243eccea242a74e02422aaa324216c99241a19e723e95a4623b0b50723a558352380f5722379a87f236e490a23450ca4232fdfb72328989d2305e8be22f21031
  | 7, 11 => 0x2dee4d682de3d37c2dd5e4112db947482d6eb0c32d3564552d1a98902cfda1512cf45da32ce182462cdf28f32cdb62292cba5f7d2cafca952ca651be2ca5acfa2c9c92ba2c9ae42c2c87d0ef2c7be8862c60eef42c498b2b2c42fb072c13df762bb7e6892ba8843d2b93415e2b862f342b6d142c2b6b82922b6ae73c2b6692a32b641f9a2b55b7142b411ce62b3e9fc02aff1c0f2afe093c2ad1ccd52aa950482a9c4a942a9ac7da2a7f6c962a71ab6e2a6a8d172a5f79ad2a3e98622a335b0a2a2f82d32a0e200a29f1b85829c5e2c3295f74a62959a0af293c0fd52935e746290449ee28e13c0c28e07b2128d427a828c5433128c3a7c328b7dffc28acf73c
  | 7, 12 => 0x33f8bf9833c6beda33addc9633a0985b3382681d33513a60332ff082332b6cf03302747932f5b1f632efb38032e0ac8132dfb21b32c69f3432c2068732ac8e813247800a3217679231eb022d31bdaf9d318e383a318ad8e131558eeb314763493146060b30ec4ec230dd2abe30b17a1b30a94148309c69e33092a0e230914522308b8d4b307c57413074800e306461c7304ed9152ff0c8502fb4080e2fa75c792f7e31ac2f775b232f56ff032f46327b2f3d7c162f2d333f2f15f2d72f14219e2ef590472ef0ffff2eed69452ee9e7722ee11b4d2ea15e5e2e802b212e65c3952e4f101d2e46958b2e43c3c12e3448982e28a2bd2e19d2062e00a7792dffefc0
  | 7, 13 => 0x3d35d18c3d1bf2473cfa499c3cdd86b93c5cd0913c2cf4da3bc01a9d3b9f76a43b9f4fa53b9777a23b8441d43b719fde3b6fd6b23b27d3a13b1fa0fa3b0bddbf3aefec363ac456db3aaffb383aa1aa6a3a987e5d3a75cc833a6372fa39bb472c39ad638a3950403a39424cbb3928b26a38f9c94538a997b93895e6533873d422385db80938495668382a570f3827c71137eb4e1037635109375c328c374cd3033729f273371fff31371be02136fc90e836f1a5a336936f6836817d763661bf253620182035db239335ccf2f8359b882e35937adb356cf1f33564cd08353ffe89353f36783502d30834ea9d8534d143a234be4ea334aeaf24341c5d50340559ee
  | 7, 14 => 0x45f4fb8345e42abb45d1eda1458c1b0845662134451526ee450bc69044e4a4f844e281d0448b584244333198441fad5c43f9671443d4b8364398ddee437f917b434740f14340b35a432efcf842f438a742d3da7d4258c7cf424d62df423f8f0e41ff453e41f44f3541c3487d4184918f4173da3e4156fa7440f8462740ee780340e6327b40df8d3440b04b79408d53e240811af0407b21bb40677ecd40587af6404543e74028fd2e3ff21efc3fe1dd833fdd96333faa68c13f9fabee3f8bd5363f1911403ef2c9303ee078eb3eadf8b13e81c75e3e5c8dc83e51fe3b3e4848ff3e2a98cc3e24e9a83de6cc3b3dc8296e3dc089333d927cff3d92073c3d43831d
  | 7, 15 => 0x51bb968e51a7318a5192c0e7508168075028bc574fe884164f0a1a614ed052bc4ec6057e4e8e76284e4db1944e3c11704df00e084defa2b84d6d7cb44d6207e44cfebf194ca53e9f4c980e0e4c93aeed4c8b8f134c36b62c4c2f80744c2f2f0b4bef9b8c4b92cec84b8379624b6fa6144b6d7f204b17c2144b0721694a7c52f94a4cd7ba4a40b0044a22dbc94a058ddf49d837ae49ce1add49c6fd4349c16cfa499f41ff498aeb90496d8ee3495d70bd49486086492e513d491ee4d848dd5c0848be36e948b14f3c48a98b884843e7c54819470e47f6dbed47d9b37e47b9f592477912bf46cfadf846b09930466a8462466217a94625d32f4616d436460863bc
  | 7, 16 => 0x6336422f632afeaa62e9c1c962c46bf9620dd29e61caaf5260cfe67b608f820d6061a65e605f5b23602bde886015d01a6013f4555ffed7895ff7d54a5faa9ff55f48864b5f35ce335e85061a5e7bfcba5da5e68a5d9f04085d45a2725cfd51295cd503df5c8048ac5bf745775bdb091e5bd3319f5b8aad865b5a06b45b2fc81f5b0dbc325aef23a75a7c05d15a0f56b159b8f8d4595f3581594545ac58e3a88858d6963f58a5bb28589f243d58543af7582571e658224c15580cf40057c41e7d56f73cc156cabf7a569e151f566c768055f8209255e3586253ed427d53c3f8a4539e25065396465d530b24bc52e0693b5226ff2852267abf520551e451c3d1ac
  | 7, 17 => 0x7d4847ff7ca36db37ab727927aa4be5f796641d9795b686a789de8b6785978f078101b43780e15a177dbdffd77c708b576abcfae76a6ae1375a337077527fdbd7419a07b73e7dc16739605b47278be2071a8d4f0717d774a715adeae70827fab6fd553446da5f5c16d4dd02f6c1cce2b6c0ecbaf6bee9c076babee2a6ad97ffd6a4cc30469fccf4469c67d5369904ec969506ea2690b0d3968fcf56368c3f13e68939ee068571614672c096467068df5668c788066759eef6666173766621f5f66606e586658320f66484c30664278a865f1537665df9c0164b7656c649f79ed648096516438425e64292621640c7b0763f84ee763ea40ce63b2961b6376351f
  | 7, 18 => 0xc2c4be0cb40748eeb21631a8b03b1c5faf0a244eaeec9bcaadf473f8accfe86caa939139a31a0fd1a0ca51299e99574a9e9849ad9d185a189839f57d949410e393e29c4491f26bdb91cac90e900e35ef8f533e868ec7b0ec8e6b60fe8d9ceb668c39f18b888e78d48687ba5683b31a7d8315c73282b6236a819ab9cc8157242d8128f3f38077f7197f2619507f1dbf9e7f1a8fd67eee8de77da5dec27d6ef37c
  | 8, 0 => 0x131d3b5412fd05a512d88d1712c7ac7e129b1125126f593f122bc8a911b6e00f11afac1a117fcfcb116093e1111d5c611101c9f510bcd6ce109989db108a8de8108a262d0f970d4b0f52f7e70ed133ec0e9187990e62c7b30e532e160d31a8270d2e3d660d16e72c0cc838990c9500f20c5bdf350c23ba7d0c11c00d0c041eab0b8daa5b0b203b970b15b6280aeb16150ae68dfb09efeca509c8d28f092808eb08cb2a3508719fb807f0d02407e641970790ca2a076d9aca075d3abb0626d89105c078cc05a02dba0544cdf604e56c620426a5410402104d0346c6ec0327c54502f5fddb019bcd0d0193adbd0132a60a0122554d011dc737009cec3f002f4827
  | 8, 1 => 0x2f21b87a2ee9e7722cf45da32b7a0cc6293de185292c0d9727d93e0027928aca27819342276f815f267c85392639e61125e008592563fe192547379b24c4815c249d63ef24923197240356ad23fc0e4423bebf2123937e852232fccd2222d264220a9a9b2209c1492205790021b4474221a9023c1feb40ca1feab86f1fbe639e1e21c84f1da3c2791d22f2e51cc1ea541c91f0b51c3bd1d81b54b30e1ad3e37a1a4426601a3039c41a28899f19edd2a919728323196926bf19570811194d07b418bc18ae189246be18097fbf1804d3f11803566017a485a01773f9151741648716ff67ae169f5cd9167ebc1d167506e1161ad833159b56a614755aa7147387c8
  | 8, 2 => 0x805efbd8759045d873f742fa7391a151735a86ea706ffaba6f9675c96f653f376d16df326bee9c07690b8184611f66576091d2585f6ce3e65eec2d245dfdbd4f5c5597f65ab5abb158652e3d572b3dcc55b00d5b52377d0750a840dd4ef5be6c4d476b1d4cfebf194b8b4c2a4b43cfa04a93910d482cc71147aec13b45d1eda145c57163455fb1d0449d41de448b584244333198438a0115412582f0411da5b73f643da43f1911403e0da1cd3d9cd9ed3c5cd0913c05e1c639559c2f3860df7e380b1a5e375c328c368f6cac3661bf2536209e1533dbc03533740dd132db8bcc32c96d1e327c9e7a3263f9b8313507a63116eaad30a6803d3092a0e23069bd2d
  | 8, 3 => 0xb3ef6d88adf473f8ab8588069839f57d92bd4609
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 5, 0 => 0xb000000000000500000000000030000000000003000000000000200000000000070000000000009000000000000000000000000000000000000002000000000000e000000000000200000000000080000000000000000000000000e000000000000d000000000000900000000000060000000000006000000000000200000000000090000000000001000000000000a000000000000800000000000030000000000006000000000000000000000000050000000000008000000000000d00000000000120000000000009
  | 5, 1 => 0xb00000000000000000000000007000000000000d0000000000007000000000000000000000000020000000000003000000000001100000000000000000000000004000000000000100000000000090000000000000000000000000100000000000020000000000006000000000000a00000000000040000000000003000000000001000000000000080000000000008000000000000f000000000000a0000000000001000000000000e00000000000010000000000009000000000000300000000000010000000000011
  | 5, 2 => 0x11000000000000800000000000010000000000008000000000000100000000000000000000000006000000000000c000000000000200000000000070000000000000000000000000c000000000000000000000000020000000000006000000000000800000000000020000000000010000000000000a
  | 6, 0 => 0x400000000121120000000006114000000000000300000000021080000000000002000000000000d000000000e114000000000000e0000000006112000000000000f00000000000120000000000012000000000001300000000000130000000002113000000010d10d000000000000400000000000080000000000013000000001210800000000000080000000000006000000000000f000000000000d0000000000000000000000000f000000000a1080000000000005000000000a1130000000000001000000000e105
  | 6, 1 => 0xd11120000000000008000000000000f0000000000013000000000000f00000000021080000000000004000000000000b00000000000040000000000002000000000000a000000000000300000000021080000000000003000000000000900000000000020000000000004000000000210800000000000020000000002108000000000000e0000000000010000000000e108000000000000900000000000010000000000002000000000a1080000000000000000000001211400000000000080000000000012000000000e105
  | 6, 2 => 0x8000000000610d00000000000080000000000002000000000000c0000000012108000000000e1130000000000007000000000000800000000121080000000000000000000000e11300000000000080000000000009000000000000a00000000000040000000000005000000000e113000000004d113000000010911300000000000000000000006113000000008510d000000000000c0000000002112000000000000400000000000090000000006113000000000e114000000000e10500000000000020000000000012
  | 6, 3 => 0x2000000000610d000000000001000000000000120000000006108000000000a113000000000610800000000000080000000000013000000000000f0000000000003000000000610d0000000000004000000001210800000000061080000000002108000000001210d0000000000007000000000000f0000000000008000000000a105000000000000f00000000491050000000000003000000000000c0000000000001000000000000a00000000121080000000000012000000000000b00000000121130000000000014
  | 6, 4 => 0x4000000000000e0000000000000000000000610d000000000001000000000000110000000002108000000000001000000000000060000000000010000000000000900000000000090000000000009000000000000b00000000000070000000000000000000000e10800000000000020000000000001000000000611300000000000120000000000002000000000000b000000000000e000000000000400000000000000000000000000000000000000b000000000e105000000000001000000000061050000000000002
  | 6, 5 => 0x3000000000000400000000000040000000000001000000000a113000000000210d000000000000800000000000030000000000002000000000e10800000000000040000000002105000000000001200000000000080000000000013000000000000e000000000000400000000121130000000000001000000000000e00000000000000000000000014000000000000a0000000000008000000000e10500000000000080000000000014000000000a1130000000002105000000000000b000000000000c000000000e113
  | 6, 6 => 0x80000000000008000000000001400000000000000000000000013000000010d1050000000000000000000000e1140000000000005000000000000c000000000211300000000000000000000006108000000000000000000000000020000000000005000000000000e00000000c910400000000000020000000000005000000000000200000000000090000000000013000000009111300000000000020000000002114000000000a1080000000109113000000000a1080000000000003000000000000c000000000000e
  | 6, 7 => 0xe113000000008510500000000000140000000000000000000001210500000000000020000000000013000000000610500000000000000000000000003000000000610d0000000000012000000000000600000000000000000000012108000000000000100000000000070000000000002000000000000b0000000000005000000000210500000000000030000000000007000000000e1130000000000000000000000e112000000000000f0000000002105000000000000f000000001211400000000021120000000000003
  | 6, 8 => 0x3000000000001300000000000120000000000007000000000000700000000121120000000000004000000000a10d00000000000000000000000005000000000000600000000000130000000000000000000000000e000000000000100000000000080000000000012000000000000800000000000020000000006112000000000000c000000000e108000000000e105000000000000f0000000000005000000000000e0000000000003000000000000b0000000002108000000000210800000000121080000000000006
  | 6, 9 => 0x700000000000040000000000006000000000210d000000000000e00000000000090000000000011000000000000b0000000000014000000000611200000000000080000000000003000000000000d000000000e1080000000000004000000000a11400000000000080000000000011000000000000000000000000000000000006113000000001210d0000000000003000000000000c0000000000000000000000000800000000c51130000000000002000000000000a000000000e10800000000021120000000000005
  | 6, 10 => 0xe112000000000001000000000000060000000006113000000000000700000000061080000000000004000000000000000000000000000000000000008000000000000d000000008510500000000000050000000000010000000000000800000000000000000000012105000000000000f0000000000009000000000000500000000000070000000000002000000000000b0000000000002000000000000a000000000000b0000000000010000000000610d000000000000a000000000000200000000021120000000000008
  | 6, 11 => 0xb0000000006112000000010911400000000000030000000012108000000000e1130000000000008000000000e10800000000000130000000000011000000000e108000000000000f0000000012108000000000000e00000000000080000000000002000000000000b00000000000030000000000005000000000000400000000000030000000000007000000000000500000000000030000000000002000000000000b00000000000000000000000000000000000a1080000000000001000000000a1050000000000012
  | 6, 12 => 0x121140000000000000000000000000d000000000000600000000000130000000006113000000000a10d00000000000030000000000005000000000a113000000000000c0000000000009000000000000e0000000000005000000000000d000000000000000000000121120000000000009000000000000100000000000090000000000004000000000000d000000004910d000000000000200000000000140000000000014000000000000700000000000010000000000008000000000000200000000021130000000000002
  | 6, 13 => 0x12112000000000000800000000000140000000000000000000000000800000000000020000000000002000000000e10800000000000040000000006113000000000001100000000000110000000000013000000001210d000000000a113000000000001000000000000130000000000006000000000e11200000000000020000000109113000000001210d0000000000004000000000000a000000000000600000000000080000000000008000000000a10d0000000000002000000000000400000000000080000000000002
  | 6, 14 => 0x3000000000000200000000061050000000000008000000000000200000000000050000000006105000000000000b0000000000004000000000000800000000000090000000000006000000000610d0000000012112000000000000d00000000000020000000000006000000000000000000000021050000000000012000000000000200000000000080000000000012000000000000b000000000000d00000000000130000000012114000000000000b0000000000002000000000000200000000000080000000000003
  | 6, 15 => 0x200000000000040000000000007000000000a10800000000000020000000000004000000000e114000000000000500000000000020000000012112000000000001200000000000120000000000007000000000000e000000000000d00000000021050000000000002000000001210d000000000000b000000000000c0000000000003000000000001000000000000110000000000010000000000000700000000000040000000000014000000000000200000000d1105000000000a112000000000000a0000000000004
  | 6, 16 => 0x110000000000004000000000000800000000000060000000006108000000000001300000000000080000000006108000000000a1130000000000000000000000000f00000000000060000000000001000000010d10d00000000000040000000085105000000004910d000000000e114000000000000a000000000e1080000000000002000000000000800000000000020000000000004000000000000800000000121080000000000012000000001210800000000000080000000012108000000000000d000000000e105
  | 6, 17 => 0x1400000000000020000000000008000000000e10d00000000000070000000006113000000010d1050000000002105000000000000100000000000030000000000002000000001210d00000000000000000000000000000000000000f00000000061080000000000008000000000a105000000000000c00000000000020000000000008000000000a108000000001211300000000000020000000000005000000000a10500000000000060000000012108000000000610d00000000d1112000000000000e0000000109113
  | 6, 18 => 0x110000000002112000000000001300000000021080000000006108000000000000c000000008d104000000000a10d00000000c511300000000000070000000000007000000000a1130000000000004000000000000c00000000121080000000012108000000000a114000000000000800000000000100000000000001000000000e10800000000021130000000000004000000000000f000000000e108000000000a108000000000000800000000000080000000085105000000000e1140000000000012
  | 6, 19 => 0x4d1140000000006108000000000000c0000000000008000000000000a000000000000f0000000000013000000000000a0000000000002000000010d112000000000000700000000000010000000000000000000000001100000000000040000000000009000000000000000000000000050000000000001000000000001300000000000110000000000010000000000000800000000d110d000000000000b00000000000020000000002113000000000e1130000000000005000000000000600000000000110000000006105
  | 6, 20 => 0x12114000000000210d000000000e112000000000211200000000000010000000012108000000000610800000000000040000000000001000000000211200000000000040000000006113000000000000800000000000000000000000005000000000e10500000000000080000000006105000000000e1130000000000008000000000000b00000000000010000000000003000000000000b000000000e105000000000000800000000000070000000000003000000000210d0000000000002000000000000c0000000000000
  | 6, 21 => 0x13000000000000a0000000000008000000000e1120000000000008000000000a11200000000000140000000000013000000000000700000000000080000000000002000000000000200000000000080000000000002000000000001200000000000030000000000001
  | 7, 0 => 0x12000000000000500000000000080000000000000000000000000e00000000d11050000000000008000000000a10d0000000000002000000000001400000000000030000000000013000000000001300000000000040000000006113000000000a112000000000000d0000000000014000000000001400000000000130000000000013000000000e1130000000000002000000000e1080000000000005000000000e10800000000000130000000000007000000000000c000000000001200000000000050000000000008
  | 7, 1 => 0xd000000000000d0000000000005000000000000000000000000130000000000013000000000000500000000000080000000000002000000000000200000000000080000000000012000000000000d000000000001200000000000120000000000008000000000e114000000000000000000000061080000000000002000000000000b000000000000d0000000000000000000001210d000000000001100000000000130000000000008000000000000c0000000000005000000000e1120000000000012000000008510d
  | 7, 2 => 0x9000000000000d000000000001000000000000120000000000007000000000000900000000000040000000000014000000000001300000000000120000000000011000000000000e000000010d11200000000000110000000000013000000000000d000000000000d000000000001300000000000080000000000005000000000000d00000000000120000000012108000000000e10800000000121080000000002112000000000001300000000061080000000000005000000000611300000000000040000000000013
  | 7, 3 => 0x610800000000000020000000000006000000000000a0000000000001000000000000d00000000000000000000006105000000000000800000000000080000000000004000000000000c0000000000011000000000000600000000000020000000000008000000000000100000000000120000000000008000000000000f000000000000800000000000120000000000005000000000000800000000121050000000000012000000000000d0000000000008000000000000800000000000130000000006108000000001210d
  | 7, 4 => 0x8000000000001400000000000130000000012114000000000000600000000000140000000000008000000000000400000000d1105000000000000c000000000000d000000000000600000000000130000000000005000000000000200000000000020000000000009000000000000c0000000006114000000000e11200000000061120000000012114000000000001300000000000060000000000013000000000001300000000000020000000002105000000000000500000000000120000000000002000000004d114
  | 7, 5 => 0x5000000000000d000000000001300000000000140000000000004000000000a114000000000001400000000000080000000000008000000000000d00000000000000000000000008000000000e1080000000000013000000000000500000000000050000000000002000000000001300000000000050000000006108000000000001200000000000130000000000005000000001210800000000000120000000000008000000000000c0000000000013000000000e113000000000000c000000000000c000000000a108
  | 7, 6 => 0x8000000000e10d0000000000010000000000000d000000000000b000000000000100000000061130000000000001000000000000300000000000080000000012114000000000001000000000000080000000000005000000000000500000000000080000000012105000000000000e000000000001300000000121050000000000012000000000000800000000000130000000000002000000000000d000000000001300000000061120000000000010000000000a112000000000a1130000000000008000000000000d
  | 7, 7 => 0x1100000000000050000000000008000000000000900000000061130000000002112000000000e1120000000000013000000000001100000000021140000000000003000000000000d000000000000b0000000000012000000000000200000000061080000000012113000000000000200000000000140000000000012000000000000c000000000000a0000000000006000000000001400000000000140000000000004000000000001200000000000000000000000008000000000e1140000000000001000000000000b
  | 7, 8 => 0x8000000000000d000000000e105000000000000e000000000a105000000000000800000000000110000000000008000000000000d000000000000600000000000120000000000012000000000e113000000000001100000000000030000000000004000000000000600000000000080000000000009000000000000800000000000130000000000008000000000000000000000000010000000000001000000000e105000000000001400000000000110000000000001000000000000c000000000a1080000000000000
  | 7, 9 => 0x10000000000000c00000000000080000000002108000000000611400000000000020000000000013000000000001300000000000080000000000009000000000e108000000000000d00000000000130000000000009000000000a113000000000e11200000000000120000000000010000000000001200000000000140000000000013000000000000d0000000000004000000000611400000000000120000000000006000000000e1050000000000013000000001210800000000021130000000000005000000000000f
  | 7, 10 => 0x110000000012105000000000000d000000000000700000000000130000000000008000000000e114000000000000600000000000120000000000014000000000000d0000000000013000000000000c00000000121140000000000003000000000e1080000000000008000000000a11200000000000100000000000008000000000000a000000000000b0000000000001000000000001300000000000050000000006108000000000000800000000000100000000000013000000000a10d000000000000d0000000000014
  | 7, 11 => 0xa10d000000000000c00000000000060000000000002000000000a1050000000000013000000000000e0000000000001000000000000800000000000130000000000014000000000000d000000000000f0000000000003000000000000c0000000006114000000000211400000000000050000000006112000000000000d00000000000020000000000010000000000000100000000000000000000000014000000000000000000000021050000000002113000000000000d000000000001000000000000010000000000005
  | 7, 12 => 0x1200000000000040000000000008000000000001000000000000110000000000002000000000001300000000000140000000000004000000000000d0000000000014000000000000500000000000010000000006113000000000000200000000d111200000000000120000000006112000000000000f000000000000500000000000140000000012108000000000000d00000000000080000000000005000000000000f000000000000700000000021120000000002108000000000210500000000000090000000000005
  | 7, 13 => 0xd0000000000008000000000000d0000000000008000000000a10d0000000000013000000000000d00000000000100000000000002000000000000d0000000000012000000000000800000000000080000000006108000000000000500000000000140000000000014000000000001300000000000070000000006114000000000000d000000000000d000000000000500000000000140000000085105000000000000a000000000000d00000000061050000000000003000000000001200000000000020000000000013
  | 7, 14 => 0x12000000000000a00000000000090000000000005000000000000500000000000040000000000007000000000001300000000000080000000012113000000000000d00000000000110000000000008000000000000500000000000080000000000007000000001211300000000121130000000000008000000000000d00000000061140000000000013000000000000d00000000000140000000012112000000000001300000000000020000000000004000000001210d00000000000120000000000013000000000000b
  | 7, 15 => 0x12114000000000000d00000000000070000000000007000000000000c0000000000002000000000000d000000000211400000000000020000000000005000000000001300000000000050000000012108000000000000d0000000000008000000000000d000000000000d000000000000d00000000061120000000000005000000000000d0000000000008000000001211200000000000120000000000005000000000000c00000000000140000000000005000000000e112000000000a11300000000000070000000000008
  | 7, 16 => 0x1210d000000000000c00000000000100000000002105000000000000300000000121130000000000004000000000a10d0000000000002000000000000b00000000000020000000000013000000000001300000000021050000000000005000000000000000000000000080000000000006000000000000500000000000140000000000002000000000001200000000000120000000000008000000000000800000000000030000000000008000000000000b0000000002113000000000001300000000000090000000000008
  | 7, 17 => 0xe1120000000000014000000000001200000000000040000000012108000000000000400000000c511400000000000020000000000012000000000000400000000061130000000000014000000000000d0000000000004000000000a108000000000000100000000021080000000012108000000000000c0000000002114000000000000500000000000080000000000010000000001210d000000000a112000000000000200000000000130000000002113000000000000d0000000002105000000000610d
  | 7, 18 => 0xd00000000000110000000006114000000000000300000000021140000000000008000000000a10800000000000020000000000012000000000000d0000000000005000000000e108000000000000d000000000000900000000000130000000000012000000000a113000000000000000000000000140000000000008000000000000e000000000000f0000000000008000000000000e000000000000300000000000130000000012108000000000a1080000000012112000000000001200000000000140000000000008
  | 7, 19 => 0xf00000000000090000000000005000000000001300000000000050000000000005000000000000f0000000000008000000000000d0000000000000000000000211400000000000130000000000009000000000000800000000000140000000000001000000000000e00000000000070000000000001000000000000c0000000002114000000000000900000000000120000000000013000000000e10500000000000100000000000002000000000000d000000000000700000000000140000000000014000000000e108
  | 7, 20 => 0x12105000000000210d000000000a10800000000000020000000000006000000000000300000000000130000000006113000000000000d0000000000012000000000000000000000000090000000000000000000000a1080000000000004000000000610d000000004910d0000000000008000000000000100000000000140000000000012000000000210d0000000000007000000000000d0000000000005000000000e1050000000000005000000000000400000000000030000000000000000000000e113000000000000d
  | 7, 21 => 0x13000000000000e000000000000400000000000140000000000013000000001210800000000021120000000000003000000000000d0000000000004000000000000500000000000140000000000001000000000000800000000021080000000000009000000000000e00000000000040000000002108000000000000200000000000130000000000005000000000001200000000000000000000000003000000000a11200000000000110000000000007000000000000e0000000006112000000000a1130000000000000
  | 7, 22 => 0x9000000000001300000000000110000000006113000000000211400000000000040000000000000000000000000800000000000060000000000013000000000a10500000000000090000000000012000000000e1140000000000002000000000000500000000000060000000109113000000000000f00000000000080000000000005000000000001200000000000140000000000000000000000210800000000061050000000000005000000000000d0000000000001000000000a11400000000000060000000012112
  | 7, 23 => 0x200000000000070000000000001000000000000400000000d110d000000000000a000000000001400000000000130000000000013000000000001300000000000080000000000013000000001211300000000000070000000000005000000000000800000000000050000000000006000000000001300000000000120000000000001000000000000e00000000000080000000006108000000000e10d0000000000012000000000000e000000000000f000000001210d0000000000006000000000000d0000000000013
  | 7, 24 => 0x800000000000140000000000005000000000001200000000000050000000000004000000000210800000000000020000000000005000000000000800000000000120000000000012000000000000a0000000000001000000000000700000000000140000000012108000000000001200000000000120000000000012000000000000d00000000000030000000000000000000000e1050000000000005000000000000d000000000000800000000000130000000000005000000000000f00000000000080000000000013
  | 7, 25 => 0xd0000000000014000000000211200000000121050000000000014000000000001200000000000080000000000013000000000000d00000000000070000000000014000000000000800000000061080000000000007000000000000d000000000000f00000000000120000000000002000000000a114000000000000d000000000001000000000000080000000000002000000000000d000000000e1120000000000001000000000000800000000000120000000000012000000000000d00000000000080000000006113
  | 7, 26 => 0x13000000000000800000000000080000000000000000000000000d000000004d113000000000000d00000000000030000000000004000000000001400000000121140000000000007000000000a108000000000000e00000000000080000000000013000000000000500000000121120000000012112000000000000d000000000e113000000000000c00000000000120000000000009000000000a10d0000000000014000000000000a00000000000130000000000005000000000210500000000121050000000000007
  | 7, 27 => 0x2113000000000000600000000021080000000000008000000000000800000000121050000000000012000000000000700000000000020000000000008000000000000e0000000000000000000000000d000000000000100000000000060000000000008000000000000800000000000130000000000012000000000001200000000000040000000000008000000000000c000000000000000000000061120000000000008000000000000e0000000000012000000000000500000000000050000000000002000000000000d
  | 7, 28 => 0x12000000000e10500000000021140000000000005000000000211300000000000020000000000013000000000000d00000000000130000000000002000000000001200000000121120000000000007000000000a112000000000001200000000000130000000000008000000000001300000000000130000000012113000000000000500000000000140000000000008000000000210d000000000611400000000000130000000000014000000000000d0000000000006000000000001300000000000000000000000012
  | 7, 29 => 0x610800000000000050000000000005000000000e1050000000000010000000000000c000000000000200000000000090000000000008000000000000800000000000140000000000014000000000001200000000000140000000000000000000000000f000000000000d0000000000007000000000001300000000000050000000000004000000000e113000000000000600000000000080000000000008000000000000500000000000120000000000013000000000000900000000000120000000000005000000000000f
  | 7, 30 => 0x1300000000851050000000000012000000000000b0000000000013000000000001300000000000050000000000007000000000000800000000000080000000000002000000000000d00000000000090000000000008000000000001400000000061050000000012108000000000000400000000000080000000000002000000000000100000000000120000000000010000000000000500000000000050000000000014000000000000400000000000080000000000005000000000a10800000000000010000000000014
  | 7, 31 => 0x1000000000000400000000000010000000000008000000000000d0000000000011000000000000a000000000001300000000000000000000000005000000000a1120000000000003000000000a108000000000000e000000000001400000000000140000000000003000000000000500000000000050000000000013000000000e11400000000021050000000000003000000000e10800000000000050000000000014000000000001400000000021080000000000003000000000000c0000000000012
  | 7, 32 => 0x80000000000007000000000000c0000000000004000000009111400000000000080000000006113000000000000d00000000121140000000000013000000000001400000000000050000000000013000000000000f00000000000080000000000008000000000000c0000000000007000000000a11200000000000140000000000006000000000000800000000000100000000000004000000000a11400000000000110000000000002000000000001200000000000060000000000007000000000000d0000000000013
  | 7, 33 => 0x800000000000050000000000001000000000001200000000000020000000000000000000000001400000000000030000000000005000000000001300000000000080000000000012000000000e1080000000000009000000000e10800000000000000000000000004000000000000200000000000140000000000000000000000000800000000000140000000000010000000010d10d000000000000d00000000000090000000000014000000000000b00000000000130000000000006000000000a1080000000000011
  | 7, 34 => 0x13000000000000d000000000000c00000000000080000000000007000000000a105000000000000e0000000000009000000000000d000000000000000000000000130000000002108000000000a108000000000001300000000000080000000000003000000000000d00000000061130000000002112000000000001400000000000080000000000004000000000e11200000000000130000000000008000000000610d000000000000600000000000000000000000013000000000000000000000000090000000000008
  | 7, 35 => 0xa10800000000061120000000000013000000000001300000000000000000000000010000000000000800000000061050000000000005000000000000d00000000000020000000000008000000000210800000000000130000000002113000000000000700000000000020000000000008000000000000700000000000060000000000008000000000000300000000000080000000000004000000000000c00000000000050000000000009000000000000d0000000012114000000000001400000000000080000000006113
  | 7, 36 => 0x120000000000005000000000611200000000000130000000000001000000000000f0000000000013000000000000e00000000000050000000000008000000000a108000000000a1140000000000008000000000000100000000000030000000006108000000000000700000000000020000000000012000000000e10500000000000030000000002113000000000000d0000000000008000000000a10d00000000000010000000012105000000000a10d0000000000010000000000610500000000000140000000000014
  | 7, 37 => 0x1300000000000120000000000008000000000000d0000000000012000000000000800000000000130000000000008
  | 8, 0 => 0x8000000000001200000000000010000000000008000000000000d000000000000100000000000080000000000008000000000000800000000000120000000000010000000000000800000000000100000000000005000000000000a000000000001300000000000080000000000014000000000000800000000000050000000000012000000000001200000000000130000000000012000000000000800000000000120000000000012000000000000800000000000050000000000012000000000000d0000000000013
  | 8, 1 => 0xd0000000000013000000000001400000000000000000000000008000000000000e0000000000014000000000000600000000000130000000000012000000000001300000000000070000000000012000000000000000000000000050000000000008000000000000f000000000000e000000000001400000000000120000000000010000000000001300000000000120000000000013000000000000d000000000000500000000000140000000000012000000000000500000000000080000000000008000000000000f
  | 8, 2 => 0x1200000000000120000000000005000000000000300000000000080000000000001000000000000e000000000000d000000000001300000000000080000000000005000000000001300000000000130000000000008000000000000d00000000000080000000000013000000000000800000000000040000000000008000000000000200000000000120000000000008000000000001000000000000080000000000008000000000000d000000000000d000000000000d00000000000130000000000005000000000000d
  | 8, 3 => 0xe00000000000120000000000013000000000001400000000000050000000000008000000000001200000000000100000000000002000000000001300000000000120000000000013000000000001200000000000140000000000007000000000001200000000000020000000000005000000000001200000000000020000000000012000000000000100000000000050000000000008000000000001300000000000050000000000013000000000000f000000000001100000000000050000000000013000000000000d
  | 8, 4 => 0xd000000000000700000000000040000000000008000000000001400000000000140000000000003000000000000000000000000080000000000014000000000000d000000000000800000000000080000000000014000000000000500000000000130000000000013000000000000d000000000001200000000000130000000000002000000000000c00000000000130000000000008000000000000f0000000000012000000000000100000000000050000000000012000000000001300000000000080000000000006
  | 8, 5 => 0x12000000000000c000000000000f00000000000050000000000005000000000000e00000000000050000000000005000000000000d0000000000014000000000000d000000000000f0000000000009000000000001200000000000050000000000008000000000000b00000000000080000000000007000000000000500000000000020000000000012000000000001400000000000000000000000008000000000001400000000000140000000000005000000000000d000000000001200000000000120000000000005
  | 8, 6 => 0xd0000000000013000000000000300000000000130000000000012
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 12 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_53 roots_53 5 s ws hint
  | 1 => checkCutEntry dom_13 roots_13 4 s ws hint
  | 2 => checkCutEntry dom_57 roots_57 5 s ws hint
  | 3 => checkCutEntry dom_43 roots_43 5 s ws hint
  | 4 => checkCutEntry dom_51 roots_51 5 s ws hint
  | 5 => checkCutEntry dom_59 roots_59 7 s ws hint
  | 6 => checkCutEntry dom_19 roots_19 4 s ws hint
  | 7 => checkCutEntry dom_37 roots_37 4 s ws hint
  | 8 => checkCutEntry dom_62 roots_62 7 s ws hint
  | 9 => checkCutEntry dom_23 roots_23 5 s ws hint
  | 10 => checkCutEntry dom_29 roots_29 5 s ws hint
  | 11 => checkCutEntry dom_15 roots_15 5 s ws hint
  | 12 => checkCutEntry dom_25 roots_25 4 s ws hint
  | 13 => checkCutEntry dom_47 roots_47 7 s ws hint
  | 14 => checkCutEntry dom_45 roots_45 5 s ws hint
  | 15 => checkCutEntry dom_39 roots_39 5 s ws hint
  | 16 => checkCutEntry dom_35 roots_35 4 s ws hint
  | 17 => checkCutEntry dom_27 roots_27 5 s ws hint
  | 18 => checkCutEntry dom_55 roots_55 7 s ws hint
  | 19 => checkCutEntry dom_61 roots_61 7 s ws hint
  | 20 => checkCutEntry dom_31 roots_31 7 s ws hint
  | _ => false
def cutHitH (s h : Nat) (ws : List Nat) : Bool :=
  let i := cidxH s h
  decide (i < CN s) && (chAt s i == h) && checkCutByIdx s ws (fld (CV s (i / 32)) 52 (i % 32))

def cutHit (s : Nat) (ws : List Nat) : Bool := cutHitH s (hk 0 ws) ws

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_63 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_53 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_13 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_57 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_43 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_51 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_59 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_19 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_37 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_62 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_23 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_29 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_25 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_47 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_45 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_39 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_35 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_27 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_55 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_61 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_31 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_63 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_63 == dom_63) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_63 goalM u ys) : RunD dom_63 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_63 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
private theorem z4 : ∀ i, 0 ≤ i → i < 0 → Z 4 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 16 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_16 : ∀ i, 16 ≤ i → i < 32 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_32 : ∀ i, 32 ≤ i → i < 48 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_48 : ∀ i, 48 ≤ i → i < 55 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 7 48 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 55 → Z 5 i = true := (range_split (range_split z5_0 z5_16) (range_split z5_32 z5_48))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 16 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_16 : ∀ i, 16 ≤ i → i < 32 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_32 : ∀ i, 32 ≤ i → i < 48 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_48 : ∀ i, 48 ≤ i → i < 64 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_64 : ∀ i, 64 ≤ i → i < 80 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_80 : ∀ i, 80 ≤ i → i < 96 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 80 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_96 : ∀ i, 96 ≤ i → i < 112 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_112 : ∀ i, 112 ≤ i → i < 128 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 112 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_128 : ∀ i, 128 ≤ i → i < 144 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 128 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_144 : ∀ i, 144 ≤ i → i < 160 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 144 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_160 : ∀ i, 160 ≤ i → i < 176 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 160 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_176 : ∀ i, 176 ≤ i → i < 192 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 176 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_192 : ∀ i, 192 ≤ i → i < 208 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 192 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_208 : ∀ i, 208 ≤ i → i < 224 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 208 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_224 : ∀ i, 224 ≤ i → i < 240 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 224 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_240 : ∀ i, 240 ≤ i → i < 248 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 240 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 248 → Z 6 i = true := (range_split (range_split (range_split (range_split z6_0 z6_16) (range_split z6_32 z6_48)) (range_split (range_split z6_64 z6_80) (range_split z6_96 z6_112))) (range_split (range_split (range_split z6_128 z6_144) (range_split z6_160 z6_176)) (range_split (range_split z6_192 z6_208) (range_split z6_224 z6_240))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_0 : ∀ i, 0 ≤ i → i < 16 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_16 : ∀ i, 16 ≤ i → i < 32 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_32 : ∀ i, 32 ≤ i → i < 48 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_48 : ∀ i, 48 ≤ i → i < 64 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_64 : ∀ i, 64 ≤ i → i < 80 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_80 : ∀ i, 80 ≤ i → i < 96 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 80 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_96 : ∀ i, 96 ≤ i → i < 112 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_112 : ∀ i, 112 ≤ i → i < 128 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 112 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_128 : ∀ i, 128 ≤ i → i < 144 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 128 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_144 : ∀ i, 144 ≤ i → i < 160 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 144 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_160 : ∀ i, 160 ≤ i → i < 176 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 160 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_176 : ∀ i, 176 ≤ i → i < 192 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 176 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_192 : ∀ i, 192 ≤ i → i < 208 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 192 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_208 : ∀ i, 208 ≤ i → i < 224 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 208 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_224 : ∀ i, 224 ≤ i → i < 240 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 224 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_240 : ∀ i, 240 ≤ i → i < 256 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 240 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_256 : ∀ i, 256 ≤ i → i < 272 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 256 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_272 : ∀ i, 272 ≤ i → i < 288 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 272 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_288 : ∀ i, 288 ≤ i → i < 304 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 288 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_304 : ∀ i, 304 ≤ i → i < 320 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 304 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_320 : ∀ i, 320 ≤ i → i < 336 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 320 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_336 : ∀ i, 336 ≤ i → i < 352 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 336 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_352 : ∀ i, 352 ≤ i → i < 368 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 352 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_368 : ∀ i, 368 ≤ i → i < 384 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 368 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_384 : ∀ i, 384 ≤ i → i < 400 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 384 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_400 : ∀ i, 400 ≤ i → i < 416 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 400 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_416 : ∀ i, 416 ≤ i → i < 432 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 416 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_432 : ∀ i, 432 ≤ i → i < 448 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 432 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_448 : ∀ i, 448 ≤ i → i < 464 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 448 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_464 : ∀ i, 464 ≤ i → i < 480 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 464 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_480 : ∀ i, 480 ≤ i → i < 496 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 480 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_496 : ∀ i, 496 ≤ i → i < 512 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 16 496 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_512 : ∀ i, 512 ≤ i → i < 522 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 10 512 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 522 → Z 7 i = true := (range_split (range_split (range_split (range_split (range_split z7_0 z7_16) (range_split z7_32 z7_48)) (range_split (range_split z7_64 z7_80) (range_split z7_96 z7_112))) (range_split (range_split (range_split z7_128 z7_144) (range_split z7_160 z7_176)) (range_split (range_split z7_192 z7_208) (range_split z7_224 z7_240)))) (range_split (range_split (range_split (range_split z7_256 z7_272) (range_split z7_288 z7_304)) (range_split (range_split z7_320 z7_336) (range_split z7_352 z7_368))) (range_split (range_split (range_split z7_384 z7_400) (range_split z7_416 z7_432)) (range_split (range_split z7_448 z7_464) (range_split z7_480 (range_split z7_496 z7_512))))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_0 : ∀ i, 0 ≤ i → i < 16 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_16 : ∀ i, 16 ≤ i → i < 32 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_32 : ∀ i, 32 ≤ i → i < 48 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 32 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_48 : ∀ i, 48 ≤ i → i < 64 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 48 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_64 : ∀ i, 64 ≤ i → i < 80 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 64 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_80 : ∀ i, 80 ≤ i → i < 96 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 80 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_96 : ∀ i, 96 ≤ i → i < 112 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 96 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_112 : ∀ i, 112 ≤ i → i < 128 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 112 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_128 : ∀ i, 128 ≤ i → i < 144 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 16 128 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z8_144 : ∀ i, 144 ≤ i → i < 146 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 2 144 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 146 → Z 8 i = true := (range_split (range_split (range_split z8_0 z8_16) (range_split z8_32 (range_split z8_48 z8_64))) (range_split (range_split z8_80 z8_96) (range_split z8_112 (range_split z8_128 z8_144))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9 : ∀ i, 0 ≤ i → i < 11 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 11 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
theorem checked (s : Nat) (hs : s ≤ 10) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
  · exact fun i hi => z6 i (Nat.zero_le i) hi
  · exact fun i hi => z7 i (Nat.zero_le i) hi
  · exact fun i hi => z8 i (Nat.zero_le i) hi
  · exact fun i hi => z9 i (Nat.zero_le i) hi
  · exact fun i hi => z10 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_63 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 6 5 = true := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 10) (h : RunD dom_63 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_63 roots_63 goal_63 11 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_63 goal_63 := by
    have h0 : isConstB dom_63 goal_63 = false := by decide +kernel
    intro h; rw [(isConstB_iff _ _).2 h] at h0; contradiction
  obtain ⟨s, ws, hs_le, hnd, hws_sub, hrun⟩ := reach_to_run (by decide +kernel) hnc hr ha
  have hperm_sub : ∃ zs, zs.Sublist xsM ∧ ws.Perm zs := by
    refine ⟨xsM.filter (fun x => decide (x ∈ ws)), List.filter_sublist, ?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ (by decide +kernel : xsM.Nodup))).2 ?_
    intro x; simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hws_sub x hx, hx⟩, fun h => h.2⟩
  obtain ⟨zs, hsub, hpz⟩ := hperm_sub
  have hrun' := Run.perm hpz hrun
  by_cases heq : zs = xsM
  · subst heq; exact noRunFull s (by omega) hrun'
  · have hcov := unorientedCov_ok (by decide +kernel) pairsG (by decide +kernel) hrun'
    have hbad := proper_failG zs (List.mem_sublists.2 hsub) heq
    rw [hcov] at hbad; contradiction

end S_63

theorem low_63 : Lower dom_63 roots_63 goal_63 11 := S_63.noCircuit

def pt6 (r : Nat) : Fin 6 → Bool := fun i => r.testBit i.val
theorem roots_63_bits : ∀ r : Fin 64, roots_63.map (·.testBit r.val) = List.ofFn (pt6 r.val) := by decide +kernel
theorem dom_63_lt : ∀ r : Fin 64, dom_63.testBit r.val = true := by decide +kernel
theorem lower_to_circuit6 (f : (Fin 6 → Bool) → Bool) (T lb : Nat)
    (hT : ∀ r : Fin 64, T.testBit r.val = f (pt6 r.val))
    (hncT : ¬ IsConst dom_63 T)
    (hlow : Lower dom_63 roots_63 T lb) :
    ∀ t : ℕ, HasCircuitSize 6 f t → lb ≤ t := by
  rintro t ⟨C, hfan, hsz, hev⟩
  have hsup0 : ∀ v ∈ roots_63, Avail mask256 roots_63 v := fun v hv => Or.inr ⟨v, hv, rfl⟩
  obtain ⟨p, bank, hp, hr, hsup⟩ := execN_reach C.gates roots_63 hfan 0 roots_63 roots_63 rfl hsup0
  set out := (execN C.gates roots_63).getD C.output 0
  have hout : out &&& dom_63 = T &&& dom_63 := by
    apply Nat.eq_of_testBit_eq; intro r
    rw [Nat.testBit_and, Nat.testBit_and]
    by_cases hlt : r < 64
    · rw [dom_63_lt ⟨r, hlt⟩, Bool.and_true, Bool.and_true]
      have h1 := execN_bit C.gates roots_63 r (by omega) (fun g hg => (hfan g hg).1)
      have h2 := congrArg (fun l => l.getD C.output false) h1
      rw [roots_63_bits ⟨r, hlt⟩] at h2
      have hgd : ((execN C.gates roots_63).map (·.testBit r)).getD C.output false =
          out.testBit r := by
        simp only [out, List.getD_eq_getElem?_getD, List.getElem?_map]
        cases (execN C.gates roots_63)[C.output]? with | none => simp | some v => rfl
      rw [hgd] at h2
      exact h2.trans ((hev (pt6 r)).trans (hT ⟨r, hlt⟩).symm)
    · have hd : dom_63.testBit r = false := by
        apply Nat.testBit_lt_two_pow
        have h64 : dom_63 < 2 ^ 64 := by decide
        exact lt_of_lt_of_le h64 (Nat.pow_le_pow_right (by omega) (by omega))
      rw [hd, Bool.and_false, Bool.and_false]
  have hav_out : Avail mask256 bank out := by
    by_cases hi : C.output < (execN C.gates roots_63).length
    · exact hsup _ (getD_mem hi)
    · rw [show out = 0 from List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
  have hd63 : dom_63 &&& mask256 = dom_63 := by decide
  have hm256 : mask256 &&& mask256 = mask256 := by decide
  have houtm : (out &&& mask256) &&& dom_63 = T &&& dom_63 := by
    rw [Nat.and_assoc, Nat.and_comm mask256 dom_63, hd63, hout]
  have hnc_m : ¬ IsConst dom_63 (out &&& mask256) := fun hc => hncT (by rcases hc with h0 | h1; exact Or.inl (houtm.symm.trans h0); exact Or.inr (houtm.symm.trans h1))
  have hnc_256 : ¬ IsConst mask256 out := fun hc => hnc_m (by
    rcases hc with h0 | h1
    · exact Or.inl (by rw [h0]; simp)
    · exact Or.inr (by rw [h1, Nat.and_comm, hd63]))
  obtain ⟨s, ws, hs, _, hws, hrun⟩ := reach_to_run hm256 hnc_256 hr hav_out
  have hws63 : ∀ w ∈ ws, Avail dom_63 roots_63 w := fun w hw => by
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 (hws w hw)
    exact Or.inr ⟨u, hu, by rw [Nat.and_assoc, Nat.and_comm mask256 dom_63, hd63]⟩
  obtain ⟨q, next, hq, hav_q, hqp⟩ := contraction hd63 hd63 hnc_m hrun (show NatReach dom_63 roots_63 0 roots_63 from rfl) hws63
  have hL := hlow q next hq (avail_of_eq houtm hav_q)
  show lb ≤ t
  have : C.gates.length ≤ t := hsz
  omega

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 15]⟩], 16⟩

theorem upper : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (18446461494925130408 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x)) 11 :=
  ⟨wit, by simp [wit, PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

theorem hT6 : ∀ r : Fin 64, goal_63.testBit r.val = (18446461494925130408 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex (pt6 r.val)) := by decide +kernel

theorem lower : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (18446461494925130408 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x)) t → 11 ≤ t :=
  lower_to_circuit6 (fun x : Fin 6 → Bool => (18446461494925130408 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x)) goal_63 11 hT6 (by unfold IsConst; decide) low_63

end PEqualNP.Outside.L_meta_29410.Core


namespace PEqualNP.Outside.L_meta_29410.Arm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Circuit restrictions adapted from L-meta-9349 and L-meta-9129.
lemma lLC {α:Type _} {a : α} {l:List α}:(a::l).length=l.length+1:=List.length_cons
lemma lLA {α:Type _} {l1 l2:List α}:(l1++l2).length=l1.length+l2.length:=List.length_append
lemma fUN {α:Type _} [DecidableEq α] {β : α->Sort _} {f:∀ a,β a} {a b : α} {v : β a} (h:b≠a):Function.update f a v b=f b:=Function.update_of_ne h v f
lemma fUS {α:Type _} [DecidableEq α] {β : α->Sort _} {f:∀ a,β a} {a : α} {v : β a}:Function.update f a v a=v:=Function.update_self a v f
lemma nAA (a b d:Nat):a+b+d=a+(b+d):=Nat.add_assoc a b d
lemma lMMp {α β γ:Type _} {g : β->γ} {f : α->β} {l:List α}:(l.map f).map g=l.map (g ∘ f):=List.map_map
lemma lGD {α:Type _} (l:List α) (d : α) {i:Nat} (h:l.length<=i):l.getD i d=d:=List.getD_eq_default l d h
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool
def q3 (gs:List Gate) (w:List Bool):List Bool :=
 gs.foldl (fun w g => w++[g.op.eval (g.inputs.map fun i => w.getD i false)]) w
lemma zd (gs gs':List Gate) (w:List Bool) :
   q3 (gs++gs') w=q3 gs' (q3 gs w):=by
 simp [q3,List.foldl_append]
lemma y1 (gs:List Gate):∀ w:List Bool,
   ∃ t:List Bool,q3 gs w=w++t/\t.length=gs.length:=by
 induction gs with
 | nil => intro w;exact ⟨[],by simp [q3],rfl⟩
 | cons g gs ih =>
   intro w
   obtain ⟨t,ht,hl⟩:=ih (w++[g.op.eval (g.inputs.map fun i => w.getD i false)])
   refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false)::t,?_,by simp [hl]⟩
   have:q3 (g::gs) w
       = q3 gs (w++[g.op.eval (g.inputs.map fun i => w.getD i false)]):=rfl
   rw [this,ht];simp
lemma qu (gs:List Gate) (w:List Bool) :
   (q3 gs w).length=w.length+gs.length:=by
 obtain ⟨t,ht,hl⟩:=y1 gs w
 rw [ht];simp [hl]
def Ok (g:Gate):Prop :=
 g.op ∈ ({GateOp.and,GateOp.or,GateOp.not}:Set GateOp)/\g.inputs.length<=2
lemma q8 {α:Type} (L:List α) (S d : α) (j : ℕ) (h:j≠L.length) :
   (L++[S]).getD j d=L.getD j d:=by
 by_cases hj:j < L.length
 . exact List.getD_append _ _ _ _ hj
 . rw [lGD _ _ (by simp;omega),lGD _ _ (by omega)]
lemma z0 {α:Type} (L:List α) (S d : α):(L++[S]).getD L.length d=S:=by
 simp
lemma z2 {α:Type} (L:List α) (S d : α) (k : ℕ) (h:L.length=k) :
   (L++[S]).getD k d=S:=by
 subst h;simp
def yb {n : ℕ} (L:List (Finset (Fin n))) (g:Gate):Finset (Fin n) :=
 (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅
lemma q71 {n : ℕ} (l:List ℕ) (F : ℕ->Finset (Fin n)) (i:Fin n) :
   i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l,i ∈ F a:=by
 induction l with
 | nil => simp
 | cons b l ih => simp [ih]
lemma kf {n : ℕ} (L:List (Finset (Fin n))) (g:Gate) (i:Fin n) :
   i ∈ yb L g ↔ ∃ a ∈ g.inputs,i ∈ L.getD a ∅ :=
 q71 _ _ _
def zb {n : ℕ} (gs:List Gate) (L:List (Finset (Fin n))):List (Finset (Fin n)) :=
 gs.foldl (fun L g => L++[yb L g]) L
def qr (n : ℕ):List (Finset (Fin n)):=List.ofFn fun i:Fin n => {i}
def q207 {n : ℕ} (x y:Fin n->Bool) (L:List (Finset (Fin n))) (w w':List Bool):Prop :=
 L.length=w.length/\w.length=w'.length /\
   ∀ j : ℕ,(∀ i ∈ L.getD j ∅,x i=y i)->w.getD j false=w'.getD j false
lemma k6 {n : ℕ} (x y:Fin n->Bool) (gs:List Gate) :
   ∀ (L:List (Finset (Fin n))) (w w':List Bool),q207 x y L w w' ->
     q207 x y (zb gs L) (q3 gs w) (q3 gs w'):=by
 induction gs with
 | nil => intro L w w' h;exact h
 | cons g gs ih =>
   intro L w w' h
   obtain ⟨h1,h2,h3⟩:=h
   apply ih (L++[yb L g])
     (w++[g.op.eval (g.inputs.map fun i => w.getD i false)])
     (w'++[g.op.eval (g.inputs.map fun i => w'.getD i false)])
   refine ⟨by simp [h1],by simp [h2],?_⟩
   intro j hj
   by_cases hjl:j=L.length
   . subst hjl
     rw [z0] at hj
     rw [h1,z0,h2,z0]
     congr 1
     apply List.map_congr_left
     intro a ha
     exact h3 a (fun i hi => hj i ((kf L g i).2 ⟨a,ha,hi⟩))
   . rw [q8 _ _ _ _ hjl] at hj
     rw [q8 _ _ _ _ (by omega),q8 _ _ _ _ (by omega)]
     exact h3 j hj
lemma j4 {n : ℕ} (x y:Fin n->Bool) :
   q207 x y (qr n) (List.ofFn x) (List.ofFn y):=by
 refine ⟨by simp [qr],by simp,?_⟩
 intro j hj
 by_cases hjn:j < n
 . have hx:x ⟨j,hjn⟩=y ⟨j,hjn⟩:=hj _ (by simp [qr,hjn])
   simp [hjn,hx]
 . rw [lGD _ _ (by simp;omega),lGD _ _ (by simp;omega)]
def vg (g:Gate):Gate :=
 match g.op with
 | GateOp.not => ⟨GateOp.not,g.inputs.take 1⟩
 | _ => g
lemma q107 (g:Gate) (F : ℕ->Bool) :
   (vg g).op.eval ((vg g).inputs.map F)=g.op.eval (g.inputs.map F):=by
 obtain ⟨op,inputs⟩:=g
 cases op <;> simp only [vg]
 cases inputs <;> simp [GateOp.eval]
def NOk (g:Gate):Prop:=Ok g/\(g.op=GateOp.not->g.inputs.length<=1)
lemma q45 (g:Gate) (h:Ok g):NOk (vg g):=by
 obtain ⟨op,inputs⟩:=g
 obtain ⟨hop,hlen⟩:=h
 rcases hop with h | h | h
 . have:op=GateOp.and:=h
   subst this;exact ⟨⟨Or.inl rfl,hlen⟩,by simp [vg]⟩
 . have:op=GateOp.or:=h
   subst this;exact ⟨⟨Or.inr (Or.inl rfl),hlen⟩,by simp [vg]⟩
 . have:op=GateOp.not:=h
   subst this
   refine ⟨⟨Or.inr (Or.inr rfl),?_⟩,fun _ => ?_⟩ <;> simp [vg]
lemma jd (gs:List Gate):∀ w:List Bool,
   q3 (gs.map vg) w=q3 gs w:=by
 induction gs with
 | nil => intro w;rfl
 | cons g gs ih =>
   intro w
   have s1:q3 ((g::gs).map vg) w=q3 (gs.map vg)
       (w++[(vg g).op.eval ((vg g).inputs.map fun i => w.getD i false)]):=rfl
   have s2:q3 (g::gs) w
       = q3 gs (w++[g.op.eval (g.inputs.map fun i => w.getD i false)]):=rfl
   rw [s1,s2,q107,ih]
abbrev Stat:=Sum Bool ℕ
def ze (w:List Bool):Stat->Bool
 | Sum.inl c => c
 | Sum.inr j => w.getD j false
def qn (m : ℕ):Stat->Prop
 | Sum.inl _ => True
 | Sum.inr j => j < m
def wr (m : ℕ):List Stat->Option Gate × Stat
 | [] => (none,Sum.inl true)
 | Sum.inl c::_ => (none,Sum.inl (!c))
 | Sum.inr j::_ => (some ⟨GateOp.not,[j]⟩,Sum.inr m)
def ko (m : ℕ):List Stat->Option Gate × Stat
 | [] => (none,Sum.inl true)
 | [Sum.inl c] => (none,Sum.inl c)
 | [Sum.inr j] => (none,Sum.inr j)
 | [Sum.inl c,Sum.inl d] => (none,Sum.inl (c&&d))
 | [Sum.inl c,Sum.inr j] => (none,bif c then Sum.inr j else Sum.inl false)
 | [Sum.inr j,Sum.inl c] => (none,bif c then Sum.inr j else Sum.inl false)
 | [Sum.inr j,Sum.inr k] => (some ⟨GateOp.and,[j,k]⟩,Sum.inr m)
 | _ => (none,Sum.inl false)
def ji (m : ℕ):List Stat->Option Gate × Stat
 | [] => (none,Sum.inl false)
 | [Sum.inl c] => (none,Sum.inl c)
 | [Sum.inr j] => (none,Sum.inr j)
 | [Sum.inl c,Sum.inl d] => (none,Sum.inl (c||d))
 | [Sum.inl c,Sum.inr j] => (none,bif c then Sum.inl true else Sum.inr j)
 | [Sum.inr j,Sum.inl c] => (none,bif c then Sum.inl true else Sum.inr j)
 | [Sum.inr j,Sum.inr k] => (some ⟨GateOp.or,[j,k]⟩,Sum.inr m)
 | _ => (none,Sum.inl false)
def qg (op:GateOp) (m : ℕ) (ins:List Stat):Option Gate × Stat :=
 match op with
 | GateOp.and => ko m ins
 | GateOp.or => ji m ins
 | GateOp.not => wr m ins
 | _ => (none,Sum.inl false)
lemma q151 (op:GateOp) (m : ℕ) (ins:List Stat) :
   ∀ g ∈ (qg op m ins).1,Ok g:=by
 intro g hg
 cases op <;> simp only [qg] at hg
 . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
     simp_all [ko, Ok]
   subst g
   simp
 . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
     simp_all [ji, Ok]
   subst g
   simp
 . rcases ins with _ | ⟨a,l⟩ <;> (try cases a) <;>
     simp_all [wr, Ok]
   subst g
   simp
 . simp at hg
 . simp at hg
lemma jh (op:GateOp) (m : ℕ) (ins:List Stat)
   (hop:op=GateOp.and\/op=GateOp.or\/op=GateOp.not) (hlen:ins.length<=2)
   (hnot:op=GateOp.not->ins.length<=1) (hc:∃ c,Sum.inl c ∈ ins) :
   (qg op m ins).1=none:=by
 obtain ⟨c,hc⟩:=hc
 rcases hop with rfl | rfl | rfl
 . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨d,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
     simp_all [qg,ko]
 . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨d,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
     simp_all [qg,ji]
 . have:=hnot rfl
   rcases ins with _ | ⟨a,_ | ⟨b,l⟩⟩ <;> (try cases a) <;> simp_all [qg,wr]
lemma kn (op:GateOp) (hop:op=GateOp.and\/op=GateOp.or\/op=GateOp.not)
   (w:List Bool) (ins:List Stat) (hlen:ins.length<=2)
   (hv:∀ s ∈ ins,qn w.length s) :
   qn (w.length+(qg op w.length ins).1.toList.length) (qg op w.length ins).2 /\
   ze (q3 (qg op w.length ins).1.toList w) (qg op w.length ins).2
     = op.eval (ins.map (ze w)):=by
 rcases hop with rfl | rfl | rfl
 . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨d,l⟩⟩⟩
   . simp [qg,ko,qn,ze,GateOp.eval]
   . cases a <;> simp_all [qg,ko,qn,ze,GateOp.eval,q3]
   . cases a <;> cases b <;> (rename_i c e; cases c) <;> cases e <;>
       simp_all [qg,ko,qn,ze,GateOp.eval,q3]
   . simp at hlen
 . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨d,l⟩⟩⟩
   . simp [qg,ji,qn,ze,GateOp.eval]
   . cases a <;> simp_all [qg,ji,qn,ze,GateOp.eval,q3]
   . cases a <;> cases b <;> (rename_i c e; cases c) <;> cases e <;>
       simp_all [qg,ji,qn,ze,GateOp.eval,q3]
   . simp at hlen
 . rcases ins with _ | ⟨a,l⟩
   . simp [qg,wr,qn,ze,GateOp.eval]
   . cases a <;> simp_all [qg,wr,qn,ze,GateOp.eval,q3]
def qa (n : ℕ) (acc:List Stat × List Gate) (g:Gate):List Stat × List Gate :=
 (acc.1++[(qg g.op (n+acc.2.length)
     (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
   acc.2++(qg g.op (n+acc.2.length)
     (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)
def elim (n : ℕ) (gs:List Gate) (acc:List Stat × List Gate):List Stat × List Gate :=
 gs.foldl (qa n) acc
lemma k4 (n : ℕ) (g:Gate) (gs:List Gate) (acc:List Stat × List Gate) :
   elim n (g::gs) acc=elim n gs (qa n acc g):=rfl
lemma jz (n : ℕ) (pre post:List Gate) (acc:List Stat × List Gate) :
   elim n (pre++post) acc=elim n post (elim n pre acc):=by
 simp [elim,List.foldl_append]
lemma q50 (n : ℕ) (gs:List Gate):∀ acc:List Stat × List Gate,
   (elim n gs acc).1.length=acc.1.length+gs.length:=by
 induction gs with
 | nil => intro acc;rfl
 | cons g gs ih =>
   intro acc
   rw [k4,ih]
   simp only [qa,lLA,lLC,List.length_nil]
   omega
lemma wy (n k : ℕ) (d:Stat) (gs:List Gate):∀ acc:List Stat × List Gate,
   k < acc.1.length->(elim n gs acc).1.getD k d=acc.1.getD k d:=by
 induction gs with
 | nil => intro acc _;rfl
 | cons g gs ih =>
   intro acc hk
   rw [k4,ih (qa n acc g) (by simp [qa];omega)]
   exact q8 _ _ _ _ (by omega)
lemma y2 {α:Type} (o:Option α):o.toList.length<=1:=by
 cases o <;> simp
lemma q156 (n : ℕ) (gs:List Gate):∀ acc:List Stat × List Gate,
   (∀ g ∈ acc.2,Ok g)->∀ g ∈ (elim n gs acc).2,Ok g:=by
 induction gs with
 | nil => intro acc h;exact h
 | cons g gs ih =>
   intro acc h
   apply ih (qa n acc g)
   intro g' hg'
   rcases List.mem_append.1 hg' with h1 | h1
   . exact h g' h1
   . exact q151 _ _ _ g' (by simpa using h1)
lemma q29 (n : ℕ) (gs:List Gate):∀ acc:List Stat × List Gate,
   (elim n gs acc).2.length<=acc.2.length+gs.length:=by
 induction gs with
 | nil => intro acc;simp [elim]
 | cons g gs ih =>
   intro acc
   have h1:=ih (qa n acc g)
   have h2:(qa n acc g).2.length<=acc.2.length+1:=by
     simp only [qa,lLA]
     have:=y2 (qg g.op (n+acc.2.length)
       (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
     omega
   rw [k4,lLC];omega
lemma zt (n k : ℕ) (gs:List Gate):∀ acc:List Stat × List Gate,
   (∀ g ∈ gs,NOk g)->k < acc.1.length->(∃ c,acc.1.getD k (Sum.inl false)=Sum.inl c) ->
   (∃ g ∈ gs,k ∈ g.inputs)->(elim n gs acc).2.length+1<=acc.2.length+gs.length:=by
 induction gs with
 | nil => intro acc _ _ _ h;obtain ⟨g,hg,_⟩:=h;simp at hg
 | cons g gs ih =>
   intro acc hok hk hc hex
   rw [k4,lLC]
   by_cases hkg:k ∈ g.inputs
   . obtain ⟨c,hc⟩:=hc
     have hnok:=hok g List.mem_cons_self
     have hnone:(qg g.op (n+acc.2.length)
         (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1=none:=by
       apply jh
       . exact hnok.1.1
       . simpa using hnok.1.2
       . intro h;simpa using hnok.2 h
       . exact ⟨c,List.mem_map.2 ⟨k,hkg,hc⟩⟩
     have h2:(qa n acc g).2.length=acc.2.length:=by
       show (acc.2++(qg g.op (n+acc.2.length)
         (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length=_
       rw [hnone];simp
     have:=q29 n gs (qa n acc g)
     omega
   . have hex':∃ g' ∈ gs,k ∈ g'.inputs:=by
       obtain ⟨g',hg',hk'⟩:=hex
       rcases List.mem_cons.1 hg' with rfl | h
       . exact absurd hk' hkg
       . exact ⟨g',h,hk'⟩
     have h1:=ih (qa n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
       (by simp [qa];omega)
       (by
         obtain ⟨c,hc⟩:=hc
         refine ⟨c,?_⟩
         simp only [qa]
         rw [q8 _ _ _ _ (by omega)];exact hc)
       hex'
     have h2:(qa n acc g).2.length<=acc.2.length+1:=by
       simp only [qa,lLA]
       have:=y2 (qg g.op (n+acc.2.length)
         (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
       omega
     omega
lemma km {m m' : ℕ} (h:m<=m'):∀ s:Stat,qn m s->qn m' s
 | Sum.inl _,_ => trivial
 | Sum.inr _,hj => lt_of_lt_of_le hj h
lemma jg (w t:List Bool):∀ s:Stat,qn w.length s ->
   ze (w++t) s=ze w s
 | Sum.inl _,_ => rfl
 | Sum.inr _,hj => List.getD_append _ _ _ _ hj
def Inv (n : ℕ) (y:List Bool) (w:List Bool) (acc:List Stat × List Gate):Prop :=
 acc.1.length=w.length/\∀ i : ℕ,
   qn (n+acc.2.length) (acc.1.getD i (Sum.inl false)) /\
   ze (q3 acc.2 y) (acc.1.getD i (Sum.inl false))=w.getD i false
lemma j7 (n : ℕ) (y:List Bool) (hy:y.length=n) (gs:List Gate) :
   ∀ (w:List Bool) (acc:List Stat × List Gate),(∀ g ∈ gs,Ok g)->Inv n y w acc ->
     Inv n y (q3 gs w) (elim n gs acc):=by
 induction gs with
 | nil => intro w acc _ h;exact h
 | cons g gs ih =>
   intro w acc hok h
   apply ih (w++[g.op.eval (g.inputs.map fun i => w.getD i false)]) (qa n acc g)
     (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
   obtain ⟨hl,hi⟩:=h
   set w':=q3 acc.2 y with hw'
   have lw':w'.length=n+acc.2.length:=by rw [hw',qu,hy]
   set ins:=g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
   have hgok:=hok g List.mem_cons_self
   have hs:=kn g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
     (by
       intro s hs
       obtain ⟨a,_,rfl⟩:=List.mem_map.1 hs
       rw [lw'];exact (hi a).1)
   rw [lw'] at hs
   set r:=qg g.op (n+acc.2.length) ins with hr
   have hvals:ins.map (ze w')=g.inputs.map fun i => w.getD i false:=by
     rw [hins,lMMp]
     apply List.map_congr_left
     intro a _
     exact (hi a).2
   have hnew:q3 (acc.2++r.1.toList) y=q3 r.1.toList w':=by
     rw [zd]
   obtain ⟨t,ht,_⟩:=y1 r.1.toList w'
   refine ⟨by simp [qa,hl],?_⟩
   intro i
   show qn (n+(acc.2++r.1.toList).length) ((acc.1++[r.2]).getD i (Sum.inl false)) /\
     ze (q3 (acc.2++r.1.toList) y) ((acc.1++[r.2]).getD i (Sum.inl false))=_
   rw [hnew,lLA,← nAA]
   by_cases hil:i=acc.1.length
   . subst hil
     rw [z0,hl,z0]
     exact ⟨hs.1,by rw [hs.2,hvals]⟩
   . rw [q8 _ _ _ _ hil,q8 _ _ _ _ (by omega)]
     refine ⟨km (by omega) _ (hi i).1,?_⟩
     rw [ht,jg _ _ _ (by rw [lw'];exact (hi i).1)]
     exact (hi i).2
def qd (n : ℕ) (b:Bool):List Stat :=
 List.ofFn (fun i:Fin n => Sum.inr (i : ℕ))++[Sum.inl b]
lemma kp (n : ℕ) (b:Bool) :
   (qd n b).getD n (Sum.inl false)=Sum.inl b :=
 z2 _ _ _ _ (by simp)
lemma q159 (n : ℕ) (b:Bool) (y:Fin n->Bool) :
   Inv n (List.ofFn y) (List.ofFn y++[b]) (qd n b,[]):=by
 refine ⟨by simp [qd],?_⟩
 intro i
 have l1:(List.ofFn (fun i:Fin n => (Sum.inr (i : ℕ):Stat))).length=n:=by simp
 have l2:(List.ofFn y).length=n:=by simp
 by_cases hin:i=n
 . subst hin
   simp only [qd]
   rw [z2 _ _ _ _ l1,z2 _ _ _ _ l2]
   exact ⟨trivial,rfl⟩
 . simp only [qd]
   rw [q8 _ _ _ _ (by omega),q8 _ _ _ _ (by omega)]
   by_cases hlt:i < n
   . simp [hlt,qn,ze,q3]
   . rw [lGD _ _ (by omega),lGD _ _ (by omega)]
     exact ⟨trivial,rfl⟩
lemma q134 (n : ℕ) (y:Fin n->Bool) (b:Bool) :
   List.ofFn (Fin.snoc y b:Fin (n+1)->Bool)=List.ofFn y++[b]:=by
 rw [List.ofFn_succ']
 simp
lemma jr (n : ℕ) (gs:List Gate):∀ L:List (Finset (Fin (n+1))),
   (∀ g ∈ gs,n ∉ g.inputs)->(∀ j : ℕ,j≠n->Fin.last n ∉ L.getD j ∅) ->
   ∀ j : ℕ,j≠n->Fin.last n ∉ (zb gs L).getD j ∅:=by
 induction gs with
 | nil => intro L _ h;exact h
 | cons g gs ih =>
   intro L hno h
   apply ih (L++[yb L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
   intro j hj
   by_cases hjl:j=L.length
   . subst hjl
     rw [z0]
     intro hmem
     obtain ⟨a,ha,hia⟩:=(kf L g _).1 hmem
     exact h a (fun e => hno g List.mem_cons_self (e ▸ ha)) hia
   . rw [q8 _ _ _ _ hjl];exact h j hj
lemma q74 (m j : ℕ) (h:j < m) :
   (qr m).getD j ∅={⟨j,h⟩}:=by
 simp [qr,h]
lemma yi (n : ℕ):∀ j : ℕ,j≠n ->
   Fin.last n ∉ (qr (n+1)).getD j ∅:=by
 intro j hj
 by_cases hlt:j < n+1
 . have e:(qr (n+1)).getD j ∅={⟨j,hlt⟩}:=q74 (n+1) j hlt
   rw [e,Finset.mem_singleton]
   intro e'
   exact hj (by have:=congrArg Fin.val e';simpa using this.symm)
 . rw [lGD _ _ (by simp [qr];omega)];simp
lemma q115 (n : ℕ) (f:(Fin (n+1)->Bool)->Bool) (b:Bool) (s : ℕ)
   (hdep:∃ x:Fin (n+1)->Bool,f (Function.update x (Fin.last n) (!x (Fin.last n)))≠f x)
   (hnc:∃ y y':Fin n->Bool,f (Fin.snoc y b)≠f (Fin.snoc y' b))
   (h:HasCircuitSize (n+1) f s) :
   ∃ s',s'+1<=s/\HasCircuitSize n (fun y:Fin n->Bool => f (Fin.snoc y b)) s':=by
 obtain ⟨C,ok,hsz,hev⟩:=h
 have hsz':C.gates.length<=s:=hsz
 set gs:=C.gates.map vg with hgs
 have hnok:∀ g ∈ gs,NOk g:=by
   intro g hg
   obtain ⟨g0,hg0,rfl⟩:=List.mem_map.1 hg
   exact q45 g0 (ok g0 hg0)
 have hevg:∀ x:Fin (n+1)->Bool,(q3 gs (List.ofFn x)).getD C.output false=f x:=by
   intro x
   rw [hgs,jd,← hev x];rfl
 set acc:=elim n gs (qd n b,[]) with hacc
 have hinv:∀ y:Fin n->Bool,
     Inv n (List.ofFn y) (q3 gs (List.ofFn (Fin.snoc y b:Fin (n+1)->Bool))) acc:=by
   intro y
   rw [q134]
   exact j7 n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (q159 n b y)
 have hval:∀ y:Fin n->Bool,
     ze (q3 acc.2 (List.ofFn y)) (acc.1.getD C.output (Sum.inl false))
       = f (Fin.snoc y b):=by
   intro y
   rw [((hinv y).2 C.output).2,hevg]
 cases hst:acc.1.getD C.output (Sum.inl false) with
 | inl c =>
   exfalso
   obtain ⟨y,y',hne⟩:=hnc
   apply hne
   rw [← hval y,← hval y',hst];rfl
 | inr j =>
   have hlen:acc.2.length+1<=s:=by
     by_cases hread:∃ g ∈ gs,n ∈ g.inputs
     . have:=zt n n gs (qd n b,[]) hnok (by simp [qd])
         ⟨b,z2 _ _ _ _ (by simp)⟩ hread
       rw [← hacc] at this
       have hl:gs.length=C.gates.length:=by simp [hgs]
       simp only [List.length_nil,zero_add] at this
       omega
     . exfalso
       push Not at hread
       have hout:C.output≠n:=by
         intro e
         rw [e,hacc,wy n n _ gs _ (by simp [qd])] at hst
         have hb:(qd n b).getD n (Sum.inl false)=Sum.inl b :=
           z2 _ _ _ _ (by simp)
         rw [show ((qd n b,([]:List Gate))).1=qd n b from rfl,hb] at hst
         cases hst
       obtain ⟨x,hx⟩:=hdep
       apply hx
       have hns:=jr n gs (qr (n+1)) hread (yi n) C.output hout
       have hag:=(k6 (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
         (j4 _ _)).2.2 C.output (by
           intro k hk
           have:k≠Fin.last n:=fun e => hns (e ▸ hk)
           simp [fUN this])
       rw [← hevg,← hevg]
       exact hag
   refine ⟨acc.2.length,hlen,⟨acc.2,j⟩,q156 n gs _ (by simp),le_refl _,?_⟩
   intro y
   have:=hval y
   rw [hst] at this
   exact this
lemma q79 (op:GateOp) (m : ℕ) (ins:List Stat)
   (hop:op=GateOp.and\/op=GateOp.or\/op=GateOp.not) (hlen:ins.length<=2)
   (hnot:op=GateOp.not->ins.length<=1) (b:Bool)
   (hand:op=GateOp.and->b=false) (hor:op=GateOp.or->b=true)
   (hc:Sum.inl b ∈ ins):∃ c,(qg op m ins).2=Sum.inl c:=by
 rcases hop with rfl | rfl | rfl
 . have:=hand rfl
   subst this
   rcases ins with _ | ⟨a,_ | ⟨d,_ | ⟨e,l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
     simp_all [qg,ko]
 . have:=hor rfl
   subst this
   rcases ins with _ | ⟨a,_ | ⟨d,_ | ⟨e,l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
     simp_all [qg,ji]
 . have:=hnot rfl
   rcases ins with _ | ⟨a,_ | ⟨d,l⟩⟩ <;> (try cases a) <;> simp_all [qg,wr]
lemma vs (n : ℕ) (acc:List Stat × List Gate) (g:Gate) (hg:NOk g) (k : ℕ)
   (hk:k ∈ g.inputs) (c:Bool) (hc:acc.1.getD k (Sum.inl false)=Sum.inl c) :
   (qa n acc g).2.length=acc.2.length:=by
 have hnone:(qg g.op (n+acc.2.length)
     (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1=none:=by
   apply jh
   . exact hg.1.1
   . simpa using hg.1.2
   . intro h;simpa using hg.2 h
   . exact ⟨c,List.mem_map.2 ⟨k,hk,hc⟩⟩
 show (acc.2++(qg g.op (n+acc.2.length)
   (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length=_
 rw [hnone];simp
def wl (g:Gate):Bool :=
 match g.op with
 | GateOp.or => true
 | _ => false
lemma q90 (n : ℕ) (acc:List Stat × List Gate) (g:Gate) (hg:NOk g) (k : ℕ)
   (hk:k ∈ g.inputs) (hc:acc.1.getD k (Sum.inl false)=Sum.inl (wl g)) :
   ∃ c,(qa n acc g).1.getD acc.1.length (Sum.inl false)=Sum.inl c:=by
 have e:(qa n acc g).1.getD acc.1.length (Sum.inl false)
     = (qg g.op (n+acc.2.length)
       (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2:=z0 _ _ _
 rw [e]
 apply q79 _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
   (wl g)
 . intro h;simp [wl,h]
 . intro h;simp [wl,h]
 . exact List.mem_map.2 ⟨k,hk,hc⟩
lemma q53 {n : ℕ} (pre post:List Gate) (L:List (Finset (Fin n))) :
   zb (pre++post) L=zb post (zb pre L):=by
 simp [zb,List.foldl_append]
lemma q54 {n : ℕ} (gs:List Gate):∀ L:List (Finset (Fin n)),
   (zb gs L).length=L.length+gs.length:=by
 induction gs with
 | nil => intro L;rfl
 | cons g gs ih =>
   intro L
   have h:zb (g::gs) L=zb gs (L++[yb L g]):=rfl
   rw [h,ih]
   simp only [lLA,lLC,List.length_nil]
   omega
lemma q124 (n : ℕ) (D : ℕ->Prop) (gs:List Gate) :
   ∀ L:List (Finset (Fin (n+1))),
   (∀ g ∈ gs,∀ a ∈ g.inputs,¬ D a)->(∀ j : ℕ,¬ D j->Fin.last n ∉ L.getD j ∅) ->
   ∀ j : ℕ,¬ D j->Fin.last n ∉ (zb gs L).getD j ∅:=by
 induction gs with
 | nil => intro L _ h;exact h
 | cons g gs ih =>
   intro L hno h
   apply ih (L++[yb L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
   intro j hj
   by_cases hjl:j=L.length
   . subst hjl
     rw [z0]
     intro hmem
     obtain ⟨a,ha,hia⟩:=(kf L g _).1 hmem
     exact h a (hno g List.mem_cons_self a ha) hia
   . rw [q8 _ _ _ _ hjl];exact h j hj
lemma q173 (n : ℕ) (gs:List Gate) (hnok:∀ g ∈ gs,NOk g) (o : ℕ)
   (hdep:Fin.last n ∈ (zb gs (qr (n+1))).getD o ∅)
   (hout:∀ b c,(elim n gs (qd n b,[])).1.getD o (Sum.inl false)≠Sum.inl c) :
   ∃ b,(elim n gs (qd n b,[])).2.length+2<=gs.length:=by
 have hon:o≠n:=by
   intro e
   apply hout false false
   rw [e,wy n n _ gs _ (by simp [qd])]
   exact kp n false
 by_cases hread:∃ g ∈ gs,n ∈ g.inputs
 swap
 . exfalso
   push Not at hread
   exact jr n gs (qr (n+1)) hread (yi n) o hon hdep
 obtain ⟨g,hg,hng⟩:=hread
 obtain ⟨pre,post,rfl⟩:=List.append_of_mem hg
 have hgn:NOk g:=hnok g hg
 have hpren:∀ g' ∈ pre,NOk g':=fun g' h => hnok g' (List.mem_append_left _ h)
 have hpostn:∀ g' ∈ post,NOk g' :=
   fun g' h => hnok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
 have hsplit:∀ b,elim n (pre++g::post) (qd n b,[])
     = elim n post (qa n (elim n pre (qd n b,[])) g) :=
   fun b => by rw [jz,k4]
 have hAn:∀ b,(elim n pre (qd n b,[])).1.getD n (Sum.inl false)=Sum.inl b:=by
   intro b
   rw [wy n n _ pre _ (by simp [qd])]
   exact kp n b
 have hAl:∀ b,(elim n pre (qd n b,[])).1.length=n+1+pre.length:=by
   intro b
   rw [q50]
   simp [qd]
 have hA2:∀ b,(elim n pre (qd n b,[])).2.length<=0+pre.length :=
   fun b => q29 n pre (qd n b,[])
 have hB2:=fun b => vs n (elim n pre (qd n b,[])) g hgn n hng b (hAn b)
 have hBl:∀ b,(qa n (elim n pre (qd n b,[])) g).1.length
     = n+1+pre.length+1:=by
   intro b
   simp [qa,hAl b]
 have hBn:∀ b,(qa n (elim n pre (qd n b,[])) g).1.getD n (Sum.inl false)
     = Sum.inl b:=by
   intro b
   show ((elim n pre (qd n b,[])).1++[_]).getD n _=_
   rw [q8 _ _ _ _ (by rw [hAl b];omega)]
   exact hAn b
 have hF:=fun b => q29 n post (qa n (elim n pre (qd n b,[])) g)
 have hlen:(pre++g::post).length=pre.length+post.length+1:=by
   simp only [lLA,lLC];omega
 by_cases h1:∃ g' ∈ pre,n ∈ g'.inputs
 . refine ⟨false,?_⟩
   have a1:(elim n pre (qd n false,[])).2.length+1<=0+pre.length :=
     zt n n pre (qd n false,[]) hpren (by simp [qd])
       ⟨false,kp n false⟩ h1
   have:=hF false
   have:=hB2 false
   rw [hsplit,hlen]
   omega
 by_cases h2:∃ g' ∈ post,n ∈ g'.inputs
 . refine ⟨false,?_⟩
   have a1:=zt n n post (qa n (elim n pre (qd n false,[])) g) hpostn
     (by rw [hBl];omega) ⟨false,hBn false⟩ h2
   have:=hA2 false
   have:=hB2 false
   rw [hsplit,hlen]
   omega
 obtain ⟨c,hc⟩:=q90 n (elim n pre (qd n (wl g),[])) g hgn n hng
   (hAn (wl g))
 rw [hAl (wl g)] at hc
 refine ⟨wl g,?_⟩
 by_cases h3:∃ g' ∈ post,(n+1+pre.length) ∈ g'.inputs
 . have a1:=zt n (n+1+pre.length) post
     (qa n (elim n pre (qd n (wl g),[])) g) hpostn
     (by rw [hBl];omega) ⟨c,hc⟩ h3
   have:=hA2 (wl g)
   have:=hB2 (wl g)
   rw [hsplit,hlen]
   omega
 . exfalso
   have hom:o≠n+1+pre.length:=by
     intro e
     apply hout (wl g) c
     rw [hsplit,e,wy n _ _ post _ (by rw [hBl];omega)]
     exact hc
   push Not at h1 h2 h3
   have hs:zb (pre++g::post) (qr (n+1))
       = zb post (zb pre (qr (n+1))
         ++ [yb (zb pre (qr (n+1))) g]):=by
     rw [q53];rfl
   rw [hs] at hdep
   have hL:=jr n pre (qr (n+1)) h1 (yi n)
   have hLl:(zb pre (qr (n+1))).length=n+1+pre.length:=by
     rw [q54]
     simp [qr]
   refine q124 n (fun j => j=n\/j=n+1+pre.length) post _ ?_ ?_ o
     (by simp [hon,hom]) hdep
   . intro g' hg' a ha hD
     rcases hD with rfl | rfl
     . exact h2 g' hg' ha
     . exact h3 g' hg' ha
   . intro j hj
     have hj':j≠n/\j≠n+1+pre.length:=by
       constructor
       . exact fun e => hj (Or.inl e)
       . exact fun e => hj (Or.inr e)
     rw [q8 _ _ _ _ (by rw [hLl];exact hj'.2)]
     exact hL j hj'.1
lemma q114 (n : ℕ) (f:(Fin (n+1)->Bool)->Bool) (s : ℕ)
   (hdep:∃ x:Fin (n+1)->Bool,f (Function.update x (Fin.last n) (!x (Fin.last n)))≠f x)
   (hnc:∀ b:Bool,∃ y y':Fin n->Bool,f (Fin.snoc y b)≠f (Fin.snoc y' b))
   (h:HasCircuitSize (n+1) f s) :
   ∃ (b:Bool) (s' : ℕ),s'+2<=s /\
     HasCircuitSize n (fun y:Fin n->Bool => f (Fin.snoc y b)) s':=by
 obtain ⟨C,ok,hsz,hev⟩:=h
 have hsz':C.gates.length<=s:=hsz
 set gs:=C.gates.map vg with hgs
 have hl:gs.length=C.gates.length:=by simp [hgs]
 have hnok:∀ g ∈ gs,NOk g:=by
   intro g hg
   obtain ⟨g0,hg0,rfl⟩:=List.mem_map.1 hg
   exact q45 g0 (ok g0 hg0)
 have hevg:∀ x:Fin (n+1)->Bool,(q3 gs (List.ofFn x)).getD C.output false=f x:=by
   intro x
   rw [hgs,jd,← hev x];rfl
 have hinv:∀ (b:Bool) (y:Fin n->Bool),
     Inv n (List.ofFn y) (q3 gs (List.ofFn (Fin.snoc y b:Fin (n+1)->Bool)))
       (elim n gs (qd n b,[])):=by
   intro b y
   rw [q134]
   exact j7 n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (q159 n b y)
 have hval:∀ (b:Bool) (y:Fin n->Bool),
     ze (q3 (elim n gs (qd n b,[])).2 (List.ofFn y))
       ((elim n gs (qd n b,[])).1.getD C.output (Sum.inl false))=f (Fin.snoc y b):=by
   intro b y
   rw [((hinv b y).2 C.output).2,hevg]
 have hout:∀ b c,
     (elim n gs (qd n b,[])).1.getD C.output (Sum.inl false)≠Sum.inl c:=by
   intro b c hst
   obtain ⟨y,y',hne⟩:=hnc b
   apply hne
   rw [← hval b y,← hval b y',hst];rfl
 have hsupp:Fin.last n ∈ (zb gs (qr (n+1))).getD C.output ∅:=by
   by_contra hns
   obtain ⟨x,hx⟩:=hdep
   apply hx
   have hag:=(k6 (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
     (j4 _ _)).2.2 C.output (by
       intro k hk
       have:k≠Fin.last n:=fun e => hns (e ▸ hk)
       simp [fUN this])
   rw [← hevg,← hevg]
   exact hag
 obtain ⟨b,hb⟩:=q173 n gs hnok C.output hsupp hout
 cases hst:(elim n gs (qd n b,[])).1.getD C.output (Sum.inl false) with
 | inl c => exact absurd hst (hout b c)
 | inr j =>
   refine ⟨b,(elim n gs (qd n b,[])).2.length,by omega,
     ⟨(elim n gs (qd n b,[])).2,j⟩,q156 n gs _ (by simp),le_refl _,?_⟩
   intro y
   have:=hval b y
   rw [hst] at this
   exact this
def wmap (n m : ℕ) (π:Fin n->Fin m) (w : ℕ) : ℕ :=
 if h:w < n then (π ⟨w,h⟩ : ℕ) else w - n+m
def jt (n m : ℕ) (π:Fin n->Fin m) (g:Gate):Gate :=
 ⟨g.op,g.inputs.map (wmap n m π)⟩
def q174 (n m : ℕ) (π:Fin n->Fin m) (C:Circuit):Circuit :=
 ⟨C.gates.map (jt n m π),wmap n m π C.output⟩
def step (w:List Bool) (g:Gate):List Bool :=
 w++[g.op.eval (g.inputs.map fun i => w.getD i false)]
def Rel (n m : ℕ) (π:Fin n->Fin m) (W W':List Bool):Prop :=
 n<=W.length/\W'.length+n=W.length+m /\
   ∀ w : ℕ,W'.getD (wmap n m π w) false=W.getD w false
lemma q182 (n m : ℕ) (π:Fin n->Fin m) (W W':List Bool) (g:Gate)
   (h:Rel n m π W W'):Rel n m π (step W g) (step W' (jt n m π g)):=by
 obtain ⟨h1,h2,h3⟩:=h
 have hv:(jt n m π g).op.eval
     ((jt n m π g).inputs.map fun i => W'.getD i false)
     = g.op.eval (g.inputs.map fun i => W.getD i false):=by
   simp only [jt,lMMp]
   congr 1
   apply List.map_congr_left
   intro a _
   exact h3 a
 refine ⟨by simp [step];omega,by simp [step];omega,?_⟩
 intro w
 simp only [step,hv]
 rcases Nat.lt_trichotomy w W.length with hw | hw | hw
 . have hlt:wmap n m π w < W'.length:=by
     unfold wmap
     split
     . have:=(π ⟨w,by assumption⟩).2;omega
     . omega
   rw [List.getD_append _ _ _ _ hlt,List.getD_append _ _ _ _ hw]
   exact h3 w
 . have he:wmap n m π w=W'.length:=by
     unfold wmap
     split
     . omega
     . omega
   rw [he,hw,z0,z0]
 . have hge:W'.length+1<=wmap n m π w:=by
     unfold wmap
     split
     . omega
     . omega
   rw [lGD _ _ (by simp;omega),lGD _ _ (by simp;omega)]
lemma q184 (n m : ℕ) (π:Fin n->Fin m) (gs:List Gate) :
   ∀ W W':List Bool,Rel n m π W W' ->
     Rel n m π (gs.foldl step W) ((gs.map (jt n m π)).foldl step W'):=by
 induction gs with
 | nil => intro W W' h;exact h
 | cons g gs ih =>
   intro W W' h
   exact ih _ _ (q182 n m π W W' g h)
lemma q183 (n m : ℕ) (π:Fin n->Fin m) (x:Fin m->Bool) :
   Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x):=by
 refine ⟨by simp,by simp;omega,?_⟩
 intro w
 unfold wmap
 split
 . rename_i hw
   rw [List.getD_eq_getElem _ _ (by simp),List.getD_eq_getElem _ _ (by simpa using hw)]
   simp
 . rename_i hw
   rw [lGD _ _ (by simp),lGD _ _ (by simp;omega)]
lemma yn {n m : ℕ} (π:Fin n->Fin m) (h:(Fin n->Bool)->Bool) (s : ℕ)
   (hc:HasCircuitSize n h s):HasCircuitSize m (fun x => h (x ∘ π)) s:=by
 obtain ⟨C,ok,hsz,hev⟩:=hc
 refine ⟨q174 n m π C,?_,?_,?_⟩
 . intro g hg
   obtain ⟨g0,hg0,rfl⟩:=List.mem_map.1 hg
   exact ⟨(ok g0 hg0).1,by simpa [jt] using (ok g0 hg0).2⟩
 . simpa [q174,Circuit.size] using hsz
 . intro x
   show _=h (x ∘ π)
   rw [← hev (x ∘ π)]
   have:=(q184 n m π C.gates _ _ (q183 n m π x)).2.2 C.output
   exact this
lemma ks (n : ℕ) (p:Fin (n+1)) (x:Fin (n+1)->Bool) (b:Bool) :
   (Fin.snoc (fun j:Fin n => x (Equiv.swap p (Fin.last n) j.castSucc)) b :
       Fin (n+1)->Bool) ∘ (Equiv.swap p (Fin.last n))
     = Function.update x p b:=by
 funext j
 simp only [Function.comp_apply]
 by_cases hj:j=p
 . subst hj
   rw [Equiv.swap_apply_left,Fin.snoc_last,fUS]
 . have hl:Equiv.swap p (Fin.last n) j≠Fin.last n:=by
     intro e
     apply hj
     have:=congrArg (Equiv.swap p (Fin.last n)) e
     rwa [Equiv.swap_apply_self,Equiv.swap_apply_right] at this
   obtain ⟨t,ht⟩:=Fin.exists_castSucc_eq.2 hl
   rw [← ht,Fin.snoc_castSucc,ht,Equiv.swap_apply_self,fUN hj]
lemma q70 (n : ℕ) (f:(Fin (n+1)->Bool)->Bool) (p:Fin (n+1)) (b:Bool) (s : ℕ)
   (hdep:∃ x:Fin (n+1)->Bool,f (Function.update x p (!x p))≠f x)
   (hnc:∃ x y:Fin (n+1)->Bool,
     f (Function.update x p b)≠f (Function.update y p b))
   (h:HasCircuitSize (n+1) f s) :
   ∃ s' : ℕ,s'+1<=s /\
     HasCircuitSize (n+1) (fun x => f (Function.update x p b)) s':=by
 set σ:Equiv.Perm (Fin (n+1)):=Equiv.swap p (Fin.last n) with hσ
 have hg:HasCircuitSize (n+1) (fun x => f (x ∘ σ)) s:=yn (⇑σ) f s h
 have hss:∀ x:Fin (n+1)->Bool,(x ∘ σ) ∘ σ=x:=by
   intro x;funext j;simp [hσ,Equiv.swap_apply_self]
 have hsl : σ.symm (Fin.last n)=p:=by
   rw [hσ,Equiv.symm_swap,Equiv.swap_apply_right]
 have hdep':∃ x:Fin (n+1)->Bool,
     (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
       ≠ (fun x => f (x ∘ σ)) x:=by
   obtain ⟨x0,hx0⟩:=hdep
   refine ⟨x0 ∘ σ,?_⟩
   simp only
   rw [Function.update_comp_equiv,hsl,hss]
   have:(x0 ∘ ⇑σ) (Fin.last n)=x0 p:=by simp [hσ,Equiv.swap_apply_right]
   rw [this];exact hx0
 have hnc':∃ y y':Fin n->Bool,
     (fun x => f (x ∘ σ)) (Fin.snoc y b)≠(fun x => f (x ∘ σ)) (Fin.snoc y' b):=by
   obtain ⟨x,y,hxy⟩:=hnc
   refine ⟨fun j => x (σ j.castSucc),fun j => y (σ j.castSucc),?_⟩
   simp only
   rw [ks,ks]
   exact hxy
 obtain ⟨s',hs,h'⟩:=q115 n _ b s hdep' hnc' hg
 refine ⟨s',hs,?_⟩
 have h'':=yn (fun j:Fin n => σ j.castSucc) _ s' h'
 have e:(fun x:Fin (n+1)->Bool =>
     (fun y:Fin n->Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
       (x ∘ fun j:Fin n => σ j.castSucc))
     = fun x => f (Function.update x p b):=by
   funext x
   simp only
   exact congrArg f (ks n p x b)
 rw [e] at h''
 exact h''
lemma q141 (n : ℕ) (f:(Fin (n+1)->Bool)->Bool) (p:Fin (n+1)) (s : ℕ)
   (hdep:∃ x:Fin (n+1)->Bool,f (Function.update x p (!x p))≠f x)
   (hnc:∀ b:Bool,∃ x y:Fin (n+1)->Bool,
     f (Function.update x p b)≠f (Function.update y p b))
   (h:HasCircuitSize (n+1) f s) :
   ∃ (b:Bool) (s' : ℕ),s'+2<=s /\
     HasCircuitSize (n+1) (fun x => f (Function.update x p b)) s':=by
 set σ:Equiv.Perm (Fin (n+1)):=Equiv.swap p (Fin.last n) with hσ
 have hg:HasCircuitSize (n+1) (fun x => f (x ∘ σ)) s:=yn (⇑σ) f s h
 have hss:∀ x:Fin (n+1)->Bool,(x ∘ σ) ∘ σ=x:=by
   intro x;funext j;simp [hσ,Equiv.swap_apply_self]
 have hsl : σ.symm (Fin.last n)=p:=by
   rw [hσ,Equiv.symm_swap,Equiv.swap_apply_right]
 have hdep':∃ x:Fin (n+1)->Bool,
     (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
       ≠ (fun x => f (x ∘ σ)) x:=by
   obtain ⟨x0,hx0⟩:=hdep
   refine ⟨x0 ∘ σ,?_⟩
   simp only
   rw [Function.update_comp_equiv,hsl,hss]
   have:(x0 ∘ ⇑σ) (Fin.last n)=x0 p:=by simp [hσ,Equiv.swap_apply_right]
   rw [this];exact hx0
 have hnc':∀ b:Bool,∃ y y':Fin n->Bool,
     (fun x => f (x ∘ σ)) (Fin.snoc y b)≠(fun x => f (x ∘ σ)) (Fin.snoc y' b):=by
   intro b
   obtain ⟨x,y,hxy⟩:=hnc b
   refine ⟨fun j => x (σ j.castSucc),fun j => y (σ j.castSucc),?_⟩
   simp only
   rw [ks,ks]
   exact hxy
 obtain ⟨b,s',hs,h'⟩:=q114 n _ s hdep' hnc' hg
 refine ⟨b,s',hs,?_⟩
 have h'':=yn (fun j:Fin n => σ j.castSucc) _ s' h'
 have e:(fun x:Fin (n+1)->Bool =>
     (fun y:Fin n->Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
       (x ∘ fun j:Fin n => σ j.castSucc))
     = fun x => f (Function.update x p b):=by
   funext x
   simp only
   exact congrArg f (ks n p x b)
 rw [e] at h''
 exact h''



def fix {n : ℕ} (f : BFn n) (p : Fin n) (b : Bool) : BFn n :=
  fun x => f (Function.update x p b)

def depends {n : ℕ} (f : BFn n) (p : Fin n) : Prop :=
  ∃ x : Fin n → Bool, fix f p (!x p) x ≠ f x

def nonconstant {n : ℕ} (f : BFn n) : Prop :=
  ∃ x y : Fin n → Bool, f x ≠ f y

-- Fix the end of a two-edge arm, then fix its intermediate vertex to false.
-- The first restriction can save two gates in one of the two branches.
lemma arm_lower {n k s : ℕ} {f g : BFn (n+1)} {leaf inner : Fin (n+1)}
    (usesLeaf : depends f leaf)
    (usesInner : ∀ b : Bool, depends (fix f leaf b) inner)
    (vary : nonconstant g)
    (reduce : ∀ b : Bool, fix (fix f leaf b) inner false = g)
    (lower : ∀ t, HasCircuitSize (n+1) g t → k ≤ t)
    (small : HasCircuitSize (n+1) f s) : k + 3 ≤ s := by
  have varySlice (b : Bool) : nonconstant (fix f leaf b) := by
    obtain ⟨x, y, hxy⟩ := vary
    exact ⟨Function.update x inner false, Function.update y inner false, by
      simpa only [← reduce b, fix] using hxy⟩
  obtain ⟨b, t, ht, first⟩ := q141 n f leaf s usesLeaf varySlice small
  have varyTwice : nonconstant (fix (fix f leaf b) inner false) := (reduce b).symm ▸ vary
  obtain ⟨u, hu, second⟩ :=
    q70 n (fix f leaf b) inner false t (usesInner b) varyTwice first
  have hk := lower u (reduce b ▸ second)
  omega


end PEqualNP.Outside.L_meta_29410.Arm

namespace PEqualNP.Outside.L_meta_29410.Lift
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_29410.Arm

def edgeList : List Nat := [0, 3, 0, 4, 1, 4, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7]
def graphF (x : Fin 8 → Bool) : Bool := decide (∃ i < edgeList.length / 2,
  (List.ofFn x).getD (edgeList.getD (2*i) 0) false = true ∧
  (List.ofFn x).getD (edgeList.getD (2*i+1) 0) false = true)
def residual : BFn 8 := fix (fix graphF 2 false) 6 false
def assignment (a : Nat) (i : Fin 8) : Bool := a.testBit i.val
def order : Fin 8 → Fin 6 := ![1,2,0,4,5,3,0,0]

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem residualLower (s : Nat) (h : HasCircuitSize 8 residual s) : 11 ≤ s := by
  have small := yn order residual s h
  have eqn : (fun x : Fin 6 → Bool => residual (x ∘ order)) =
      (fun x : Fin 6 → Bool => (18446461494925130408 : Nat).testBit (tableIndex x)) := by
    funext x; revert x; decide +kernel
  rw [eqn] at small
  exact PEqualNP.Outside.L_meta_29410.Core.lower s small

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem lowerBound (s : Nat) (h : HasCircuitSize 8 graphF s) : 14 ≤ s := by
  apply arm_lower (leaf := 2) (inner := 6) (g := residual)
    (k := 11) _ _ _ _ residualLower h
  · exact ⟨assignment 64, by decide +kernel⟩
  · intro b
    cases b
    · exact ⟨assignment 1, by decide +kernel⟩
    · exact ⟨assignment 0, by decide +kernel⟩
  · exact ⟨assignment 0, assignment 255, by decide +kernel⟩
  · intro b
    funext x
    revert x b
    decide +kernel

def candidate : Circuit := ⟨[⟨.or,[0,1]⟩, ⟨.or,[6,7]⟩, ⟨.or,[4,9]⟩, ⟨.and,[8,10]⟩, ⟨.and,[2,6]⟩, ⟨.or,[3,4]⟩, ⟨.or,[9,0]⟩, ⟨.and,[13,14]⟩, ⟨.or,[3,7]⟩, ⟨.or,[1,16]⟩, ⟨.and,[5,17]⟩, ⟨.or,[11,12]⟩, ⟨.or,[19,15]⟩, ⟨.or,[20,18]⟩], 21⟩
theorem basis : ∀ g ∈ candidate.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by simp [candidate]
set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem correct : ∀ x : Fin 8 → Bool, candidate.eval (List.ofFn x) = graphF x := by
  decide +kernel
end PEqualNP.Outside.L_meta_29410.Lift

open PEqualNP.Outside.L_meta_29410.Lift PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_29410 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o allowed _ realizes
  have small : HasCircuitSize 8 graphF gates.length := by
    refine ⟨⟨gates,o⟩, ?_, le_rfl, realizes⟩
    intro g hg
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using allowed g hg
  exact ⟨candidate.gates, candidate.output, basis,
    Nat.le_trans (by decide : candidate.gates.length ≤ 14) (lowerBound _ small), correct⟩
