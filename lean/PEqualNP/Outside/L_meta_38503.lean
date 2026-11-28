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

namespace PEqualNP.Outside.L_meta_38503_aux

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

section RunFacts
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
end RunFacts

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
  let x := (((w % 170141183460469231731687303715884105727) ^^^ seed) * 0x9e3779b97f4a7c15f39cc0605cedc835) &&& 0xffffffffffffffffffffffffffffffff
  let y := ((x ^^^ (x >>> 61)) * 0xc2b2ae3d27d4eb4f165667b19e3779f9) &&& 0xffffffffffffffffffffffffffffffff
  y >>> 96

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

def dom_55 : Nat := 0xff00ff00ff00ff
def goal_55 : Nat := 0xeaeae8e8a8a8a0a0eaeae8e8a8a8a0a0eaeae8e8a8a8a0a0eaeae8e8a8a8a0a0
def roots_55 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_31_32 : Nat := 0xffffffff00000000
def goal_31_32 : Nat := 0xeeeaeae8eeeaeae8eeeaeae8eeeaeae8eeeaeae8eeeaeae8eeeaeae8eeeaeae8
def roots_31_32 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_61_2 : Nat := 0xcccccccccccccccc
def goal_61_2 : Nat := 0xfffafafaffaafaa0fffafafaffaafaa0fffafafaffaafaa0fffafafaffaafaa0
def roots_61_2 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_31 : Nat := 0xffffffff
def goal_31 : Nat := 0xeea8eaa0eea8eaa0eea8eaa0eea8eaa0eea8eaa0eea8eaa0eea8eaa0eea8eaa0
def roots_31 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_62_1 : Nat := 0xaaaaaaaaaaaaaaaa
def goal_62_1 : Nat := 0xfffffffcfffcfff0fffffffcfffcfff0fffffffcfffcfff0fffffffcfffcfff0
def roots_62_1 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_15 : Nat := 0xffff
def goal_15 : Nat := 0xeaa0eaa0eaa0eaa0eaa0eaa0eaa0eaa0eaa0eaa0eaa0eaa0eaa0eaa0eaa0eaa0
def roots_15 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0]

def dom_23_32 : Nat := 0xff00ff00000000
def goal_23_32 : Nat := 0xeaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8eaeae8e8
def roots_23_32 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0]

def dom_51 : Nat := 0xf000f000f000f
def goal_51 : Nat := 0xaaaa888888880000aaaa888888880000aaaa888888880000aaaa888888880000
def roots_51 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_54_1 : Nat := 0xaa00aa00aa00aa
def goal_54_1 : Nat := 0xfffffcfcfcfcf0f0fffffcfcfcfcf0f0fffffcfcfcfcf0f0fffffcfcfcfcf0f0
def roots_54_1 : List Nat := [xs256.getD 1 0, xs256.getD 2 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_39 : Nat := 0xff000000ff
def goal_39 : Nat := 0xe8e8e8e8a0a0a0a0e8e8e8e8a0a0a0a0e8e8e8e8a0a0a0a0e8e8e8e8a0a0a0a0
def roots_39 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 5 0]

def dom_29_2 : Nat := 0xcccccccc
def goal_29_2 : Nat := 0xffaafaa0ffaafaa0ffaafaa0ffaafaa0ffaafaa0ffaafaa0ffaafaa0ffaafaa0
def roots_29_2 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def goal_59 : Nat := 0xeeaaaa88ee88aa00eeaaaa88ee88aa00eeaaaa88ee88aa00eeaaaa88ee88aa00
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_47_16 : Nat := 0xffff0000ffff0000
def goal_47_16 : Nat := 0xeeeaeeeaeea8eea8eeeaeeeaeea8eea8eeeaeeeaeea8eea8eeeaeeeaeea8eea8
def roots_47_16 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_47 : Nat := 0xffff0000ffff
def goal_47 : Nat := 0xeae8eae8eaa0eaa0eae8eae8eaa0eaa0eae8eae8eaa0eaa0eae8eae8eaa0eaa0
def roots_47 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_57_2 : Nat := 0xc0c0c0c0c0c0c0c
def goal_57_2 : Nat := 0xffaaaaaaffaaaa00ffaaaaaaffaaaa00ffaaaaaaffaaaa00ffaaaaaaffaaaa00
def roots_57_2 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_58_1 : Nat := 0xa0a0a0a0a0a0a0a
def goal_58_1 : Nat := 0xffffffccffccff00ffffffccffccff00ffffffccffccff00ffffffccffccff00
def roots_58_1 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

def dom_27 : Nat := 0xf0f0f0f
def goal_27 : Nat := 0xee88aa00ee88aa00ee88aa00ee88aa00ee88aa00ee88aa00ee88aa00ee88aa00
def roots_27 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0]

def dom_45_2 : Nat := 0xcccc0000cccc
def goal_45_2 : Nat := 0xfafafafafaa0faa0fafafafafaa0faa0fafafafafaa0faa0fafafafafaa0faa0
def roots_45_2 : List Nat := [xs256.getD 0 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 5 0]

def dom_63 : Nat := 0xffffffffffffffff
def goal_63 : Nat := 0xeeeaeae8eea8eaa0eeeaeae8eea8eaa0eeeaeae8eea8eaa0eeeaeae8eea8eaa0
def roots_63 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 2 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]

namespace S_55
def pairsG : List (Nat × Nat) := [(1, 5), (3, 7), (3, 19), (3, 35), (4, 5), (6, 7), (6, 38), (17, 19), (17, 21), (17, 49), (18, 19), (20, 21), (22, 23), (22, 54), (33, 35), (33, 37), (33, 49), (34, 35), (34, 38), (36, 37), (36, 38), (48, 49), (50, 51), (50, 54), (52, 53), (52, 54)]
def r1sG : List Nat := [1, 3, 3, 3, 4, 6, 6, 17, 17, 17, 18, 20, 22, 22, 33, 33, 33, 34, 34, 36, 36, 48, 50, 50, 52, 52]
def r2sG : List Nat := [5, 7, 19, 35, 5, 7, 38, 19, 21, 49, 19, 21, 23, 54, 35, 37, 49, 35, 38, 37, 38, 49, 51, 54, 53, 54]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := [4402914403077, 18709718897413, 6601937658629, 4403183560197, 18705139442451, 4411504337669, 36356950790961, 22063819924229, 37396383401251, 39728733947174, 37400627840294, 37409217774886, 19864830215443, 36301636510469, 36297057047331]
def xsM : List Nat := roots_55.map (· &&& dom_55)
def goalM : Nat := goal_55 &&& dom_55
def NN : Nat → Nat
  | 4 => 3
  | 5 => 48
  | 6 => 25
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xe1c0a31447baa0702f6cd3f0
  | 5, 0 => 0xfd05eeb0fb273fd9e7a2b4e0e1a85648dfe8340dd9a12700d1281c73c8c371c7c02fff4cbafcd3b3b6f3eb28b6943d31b5787098b4c0e045af452846a83b4da2a4f836c397b5c1248f224ea98d6d681c7bb571f576fa35f173ea86206b85db746ac3bed86493ec5a62f268f95dbf3d605a43850356c06ab354c5e11154375cd74cd9999447baa070411ca7c63d0687ed2ef024e02935d46028206f8320d129b4183db73912b606eb125d7cbe0ab1732e0982ab17066ead8103f5f65301def71f
  | 6, 0 => 0xfd05eeb0e0d44139c9d5353ac2948086b5787098a4f836c392c817469034ec5b88ca29be7f9c59f373ea86206b85db7469ad921162f268f9514fa09150eeb30f47baa070464257373daee4bc2f17f7c427ca5be020b49e3817bdcd4415dbc31515521a2e
  | 7, 0 => 0x47baa070
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x550055005500550000000000000000000000000000000000000000000000000033003300330033000000000000000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000f0000000f0000000000000000000000000000000000000000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000aa000000aa0000000000000000000000000000000000000000000000000000000f0000000f0000000000000000000000000000000000000000000000000000000000ff00ff
  | 0, 1 => 0xc800c800c800c800000000000000000000000000000000000000000000000000c000c000c000c000000000000000000000000000000000000000000000000000aa00aa00aa00aa00000000000000000000000000000000000000000000000000aa00a000aa00a000000000000000000000000000000000000000000000000000aa000000aa000000000000000000000000000000000000000000000000000000a000a000a000a00000000000000000000000000000000000000000000000000088008800880088000000000000000000000000000000000000000000000000005500ff005500ff
  | 0, 2 => 0xf000f000a000a000000000000000000000000000000000000000000000000000f000f00000000000000000000000000000000000000000000000000000000000f0000000f0000000000000000000000000000000000000000000000000000000ee00ee00ee00ee00000000000000000000000000000000000000000000000000ee00ee0000000000000000000000000000000000000000000000000000000000cc00cc00cc00cc00000000000000000000000000000000000000000000000000cc00cc0000000000000000000000000000000000000000000000000000000000cc000000cc0000
  | 0, 3 => 0xff000000cc000000000000000000000000000000000000000000000000000000ff000000aa000000000000000000000000000000000000000000000000000000fc00fc00fc00fc00000000000000000000000000000000000000000000000000fa00fa00fa00fa00000000000000000000000000000000000000000000000000fa00f000fa00f000000000000000000000000000000000000000000000000000fa000000fa000000000000000000000000000000000000000000000000000000f000ff00f000ff00000000000000000000000000000000000000000000000000f000f000f000f0
  | 0, 4 => 0xff00f000ff000000000000000000000000000000000000000000000000000000ff00cc00ff00cc00000000000000000000000000000000000000000000000000ff00cc00ff000000000000000000000000000000000000000000000000000000ff00cc0000000000000000000000000000000000000000000000000000000000ff00aa00ff00aa00000000000000000000000000000000000000000000000000ff00a000ff00a000000000000000000000000000000000000000000000000000ff005500ff005500000000000000000000000000000000000000000000000000ff000000ff0000
  | 0, 5 => 0xff00ff00ff000000000000000000000000000000000000000000000000000000ff00ff00f000f000000000000000000000000000000000000000000000000000ff00ff00cc00cc00000000000000000000000000000000000000000000000000ff00ff00a000a000000000000000000000000000000000000000000000000000ff00ff0000000000000000000000000000000000000000000000000000000000ff00f000ff00f0
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x91840d4a6061235407d844d4
  | 5, 0, 0 => 0xa6060f356981848d58184d2356999840d5a605d2356048d1405a60614256948d1435a6848d15696122c75a5848d056a81848d5a52345116c81648d5a5e612356961234c5
  | 5, 0, 1 => 0xa606121d5848d0c05a1848d01697d848d5920612356995848d581848d01696123435a5234b156b81844d5a68612356985848d5a6048715699d848d5a6071229696123445
  | 5, 0, 2 => 0xa6048d15696d848d5a68552355848d2c05a62612356965848d581848701696121c35a686121d698584875a5848d096060d1805a5848d2d698d848b5a5a61235696123485
  | 6, 0, 0 => 0xa6061244d602061234050296123435a6061238d6029a1848d5a606123456a6061448d602981848d5a606123436a6881848d6a606123496a606123476a6061548d6a606123466a6061240d6a6075848d6
  | 6, 0, 1 => 0x298123455a6061234a6a6381848d6ae981848d602961234b50298184875a6071848d6a6061234b6b6981848d6
  | 7, 0, 0 => 0x2981848d5
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 34
  | 5 => 34
  | 6 => 40
  | 7 => 34
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 6 0) :: stateWires n (ids >>> 6)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x3fe3c70000000000000000000000000000000000000000000000000000000000339cb910000000000000000000000000000000000000000000000000000000000e7c78f0000000000000000000000000000000000000000000000000000000000e0078000000000000000000000000000000000000000000000000000000000001fc07f000000000000000000000000000000000000000000000000000000000001c00f000000000000000000000000000000000000000000000000000000000007c00f0000000000000000000000000000000000000000000000000000000000003fff
  | 0, 1 => 0x306e0000000000000000000000000000000000000000000000000000000000003060000000000000000000000000000000000000000000000000000000000001c38f000000000000000000000000000000000000000000000000000000000000038000000000000000000000000000000000000000000000000000000000000003800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000e0000000000000000000000000000000000000000000000000000000003fffc7f
  | 0, 2 => 0x3180000000000000000000000000000000000000000000000000000000000000318000000000000000000000000000000000000000000000000000000000000030038000000000000000000000000000000000000000000000000000000000000c7f7ef0000000000000000000000000000000000000000000000000000000000c7c0000000000000000000000000000000000000000000000000000000000000c6346e0000000000000000000000000000000000000000000000000000000000c600000000000000000000000000000000000000000000000000000000000000c03400
  | 0, 3 => 0x3e034000000000000000000000000000000000000000000000000000000000003e003800000000000000000000000000000000000000000000000000000000003de3c7e000000000000000000000000000000000000000000000000000000000319fbff0000000000000000000000000000000000000000000000000000000003183bf00000000000000000000000000000000000000000000000000000000003003b8000000000000000000000000000000000000000000000000000000000031ff87f0000000000000000000000000000000000000000000000000000000003183870
  | 0, 4 => 0x3f83f800000000000000000000000000000000000000000000000000000000003e63fee0000000000000000000000000000000000000000000000000000000003e63f800000000000000000000000000000000000000000000000000000000003e600000000000000000000000000000000000000000000000000000000000003e1ff8f0000000000000000000000000000000000000000000000000000000003e03f800000000000000000000000000000000000000000000000000000000003fe3ff00000000000000000000000000000000000000000000000000000000003e03f80
  | 0, 5 => 0x3ffff800000000000000000000000000000000000000000000000000000000003fff8700000000000000000000000000000000000000000000000000000000003fff46e0000000000000000000000000000000000000000000000000000000003ffc0000000000000000000000000000000000000000000000000000000000003ffc0000000000000000000000000000000000000000000000000000000000003f83ff0
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x29420400000000000000000000000000000000000000000000000000000000001298b11000000000000000000000000000000000000000000000000000000000063468c000000000000000000000000000000000000000000000000000000000061068400000000000000000000000000000000000000000000000000000000001ec07b00000000000000000000000000000000000000000000000000000000000ac03b00000000000000000000000000000000000000000000000000000000000240080000000000000000000000000000000000000000000000000000000000001db7
  | 0, 1 => 0x2d674ee000000000000000000000000000000000000000000000000000000000294306200000000000000000000000000000000000000000000000000000000016bdfbf0000000000000000000000000000000000000000000000000000000001699fb70000000000000000000000000000000000000000000000000000000001611f84000000000000000000000000000000000000000000000000000000000108993300000000000000000000000000000000000000000000000000000000004254ae00000000000000000000000000000000000000000000000000000000029ee07b
  | 0, 2 => 0x39cb97300000000000000000000000000000000000000000000000000000000039ca04000000000000000000000000000000000000000000000000000000000038039000000000000000000000000000000000000000000000000000000000003ffffff0000000000000000000000000000000000000000000000000000000003ffe2480000000000000000000000000000000000000000000000000000000002d674ee0000000000000000000000000000000000000000000000000000000002d660480000000000000000000000000000000000000000000000000000000002c03484
  | 0, 3 => 0x3e136840000000000000000000000000000000000000000000000000000000003e13f840000000000000000000000000000000000000000000000000000000003defdff0000000000000000000000000000000000000000000000000000000003ffffff0000000000000000000000000000000000000000000000000000000003fdbff70000000000000000000000000000000000000000000000000000000003e13f8400000000000000000000000000000000000000000000000000000000039ef97b00000000000000000000000000000000000000000000000000000000039cb973
  | 0, 4 => 0x3fdbfc40000000000000000000000000000000000000000000000000000000003f77fee0000000000000000000000000000000000000000000000000000000003f77fcc0000000000000000000000000000000000000000000000000000000003f762480000000000000000000000000000000000000000000000000000000003ebffbf0000000000000000000000000000000000000000000000000000000003e9bfb70000000000000000000000000000000000000000000000000000000003f53fc40000000000000000000000000000000000000000000000000000000003e13f84
  | 0, 5 => 0x3ffffcc0000000000000000000000000000000000000000000000000000000003fffb7b0000000000000000000000000000000000000000000000000000000003fff6ee0000000000000000000000000000000000000000000000000000000003fffb7b0000000000000000000000000000000000000000000000000000000003ffe2480000000000000000000000000000000000000000000000000000000003fdbff7
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 46 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 46 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 46 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 46 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 6 0) :: stateWiresD n (ids >>> 6)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 6 0) :: stateWiresS n (ids >>> 6)
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 7 0 (NN s)
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_55 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_55 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_55 == dom_55) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_55 goalM u ys) : RunD dom_55 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_55 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 16 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_16 : ∀ i, 16 ≤ i → i < 32 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_32 : ∀ i, 32 ≤ i → i < 48 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 32 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 48 → Z 5 i = true := (range_split (range_split z5_0 z5_16) z5_32)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 16 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_16 : ∀ i, 16 ≤ i → i < 25 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 9 16 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 25 → Z 6 i = true := (range_split z6_0 z6_16)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_0 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := z7_0
theorem checked (s : Nat) (hs : s ≤ 7) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
  · exact fun i hi => z6 i (Nat.zero_le i) hi
  · exact fun i hi => z7 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_55 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD dom_55 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_55 roots_55 goal_55 8 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_55 goal_55 := by
    have h0 : isConstB dom_55 goal_55 = false := by decide +kernel
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

end S_55

theorem low_55 : Lower dom_55 roots_55 goal_55 8 := S_55.noCircuit

namespace S_31_32
def pairsG : List (Nat × Nat) := [(33, 35), (33, 37), (33, 41), (33, 49), (34, 35), (34, 38), (36, 37), (36, 38), (40, 41), (42, 43), (42, 46), (42, 58), (44, 45), (44, 46), (48, 49), (50, 51), (50, 54), (50, 58), (52, 53), (52, 54), (56, 57), (56, 58), (60, 61), (60, 62)]
def r1sG : List Nat := [33, 33, 33, 33, 34, 34, 36, 36, 40, 42, 42, 42, 44, 44, 48, 50, 50, 50, 52, 52, 56, 56, 60, 60]
def r2sG : List Nat := [35, 37, 41, 49, 35, 38, 37, 38, 41, 43, 46, 58, 45, 46, 49, 51, 54, 58, 53, 54, 57, 58, 61, 62]
def mpG : Nat := 0xffffff
def pool6G : List Nat := [37525735744803, 46322064958249, 39724859860517, 61787955864378, 46321962984739, 46351893472041, 46322064961833, 55118023762737, 61753596650298, 55156526885178, 39724725445413, 48520952685349, 55118324966947, 57317179925285, 39729003569958]
def xsM : List Nat := roots_31_32.map (· &&& dom_31_32)
def goalM : Nat := goal_31_32 &&& dom_31_32
def NN : Nat → Nat
  | 4 => 13
  | 5 => 47
  | 6 => 24
  | 7 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xcb85f5a5b07954b5b0273326afd37c517b0c59c06e0a56136151fc205f5ce351584362093668ecf31933c25c01313b960009ff46
  | 5, 0 => 0xfb45fe20f329cbdceea07002dc1b0d52cd07a878cce3300ebac05386ba24852eb740b46eaecd9a48a3c71882964a89bc8de7e228837263dc77dc40c7764c6cf37523d75b643ce693636d008b608578e95f5ce3515eeace285afe27275843620952a1850f50ff384b4726db884684411f42d4580c3c2f10113a877c6036c13d3b33ff42532c8bb1972a92d0ea239e6b931d05c19c1ccdf1150eac844f0e094e0c0c9503e80c70127509f3bf12082f92a30706fd0b0467640c02a103ae
  | 6, 0 => 0xeea07002e584d83dccf2db85b740b46e8f1909028986d9d586cfb07d7d657ff377186efb7523d75b608578e95fcdfb9d5f5ce351531e2a99527e04584fbea8484995ef473c415933358964b82f5e14ef273b926c1dcf21030706fd0b059706fd
  | 7, 0 => 0x5f5ce351
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x33333333000000000000000000000000000000000000000000000000000000000f0f0f0f000000000000000000000000000000000000000000000000000000000f0f0000000000000000000000000000000000000000000000000000000000000f000f000000000000000000000000000000000000000000000000000000000000ff00ff00000000000000000000000000000000000000000000000000000000000f000f000000000000000000000000000000000000000000000000000000000000ffff0000000000000000000000000000000000000000000000000000000000000f0f00000000
  | 0, 1 => 0xcccc000000000000000000000000000000000000000000000000000000000000cc00cc0000000000000000000000000000000000000000000000000000000000c0c0c0c000000000000000000000000000000000000000000000000000000000aaaaaaaa00000000000000000000000000000000000000000000000000000000aa00aa0000000000000000000000000000000000000000000000000000000000a0a0a0a00000000000000000000000000000000000000000000000000000000088888888000000000000000000000000000000000000000000000000000000005555555500000000
  | 0, 2 => 0xf000f00000000000000000000000000000000000000000000000000000000000eeeeeeee00000000000000000000000000000000000000000000000000000000eeeecccc00000000000000000000000000000000000000000000000000000000eeee000000000000000000000000000000000000000000000000000000000000ecececec00000000000000000000000000000000000000000000000000000000eaeaeaea00000000000000000000000000000000000000000000000000000000e0e0e0e000000000000000000000000000000000000000000000000000000000cccccccc00000000
  | 0, 3 => 0xff00000000000000000000000000000000000000000000000000000000000000fcfcfcfc00000000000000000000000000000000000000000000000000000000fafafafa00000000000000000000000000000000000000000000000000000000faf0faf000000000000000000000000000000000000000000000000000000000f8f8f8f800000000000000000000000000000000000000000000000000000000f0fff0ff00000000000000000000000000000000000000000000000000000000f0f0f0f000000000000000000000000000000000000000000000000000000000f0f0000000000000
  | 0, 4 => 0xfff0fff000000000000000000000000000000000000000000000000000000000fff0faf000000000000000000000000000000000000000000000000000000000fff0f0f000000000000000000000000000000000000000000000000000000000ffc0ffc000000000000000000000000000000000000000000000000000000000ffaaffaa00000000000000000000000000000000000000000000000000000000ffaaff0000000000000000000000000000000000000000000000000000000000ff00ff0000000000000000000000000000000000000000000000000000000000ff00aa0000000000
  | 0, 5 => 0xffffff0000000000000000000000000000000000000000000000000000000000fffff0f000000000000000000000000000000000000000000000000000000000fffff00000000000000000000000000000000000000000000000000000000000ffffcccc00000000000000000000000000000000000000000000000000000000ffffc0c000000000000000000000000000000000000000000000000000000000ffffa0a000000000000000000000000000000000000000000000000000000000ffff888800000000000000000000000000000000000000000000000000000000ffff000000000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0xa2179240289903100ba7307402f9503100a21753402e9d02100a216d64a216503140ba740c402e40c0900b6740c402e9103100ba14904
  | 5, 0, 0 => 0xba1750316ea2740c5a2165531689d034c5a193070d6985940c5a27650216881940c5a21710316889940c5b6165031688d940b59d940c05689d940c5a21408196b85940c5
  | 5, 0, 1 => 0x85940805688594085a21653316c8593cc585940c056885940c5a2764c1d6840c183502e9d0312869940c585940c01616503055a21307196840c1845a21450316885e34c5
  | 5, 0, 2 => 0x2f7d940c5ba765031688503065a2165625688592075650303056885b40c5a2585031688593075a21652416a85940c5a2740c196885d40a585951031689d740c5
  | 6, 0, 0 => 0xa2165030a602885940850216503015a2165840c602885940c5a2385940c6a2165640c6b2885940c6a216503086a216503016a216503096a216503076ba885940c6a2165034c60289d940c5a217d940c6
  | 6, 0, 1 => 0x288503065a2175940c6be885940c60288593075a2179940c6a216503066a2165030b6a2165038c6
  | 7, 0, 0 => 0x2885940c5
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 34
  | 5 => 34
  | 6 => 40
  | 7 => 34
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 6 0) :: stateWires n (ids >>> 6)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xfc71cf000000000000000000000000000000000000000000000000000000000033cf3f000000000000000000000000000000000000000000000000000000000033c0000000000000000000000000000000000000000000000000000000000000300f0000000000000000000000000000000000000000000000000000000000000fc0ff000000000000000000000000000000000000000000000000000000000003c03f0000000000000000000000000000000000000000000000000000000000003fff0000000000000000000000000000000000000000000000000000000000000f3f
  | 0, 1 => 0x380000000000000000000000000000000000000000000000000000000000000000e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000fffff0
  | 0, 2 => 0xc030000000000000000000000000000000000000000000000000000000000000038e3f0000000000000000000000000000000000000000000000000000000000038e3000000000000000000000000000000000000000000000000000000000000380000000000000000000000000000000000000000000000000000000000000038e30000000000000000000000000000000000000000000000000000000000000000f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000038e30
  | 0, 3 => 0xf000000000000000000000000000000000000000000000000000000000000000cfbef00000000000000000000000000000000000000000000000000000000000cc30cf0000000000000000000000000000000000000000000000000000000000cc30c00000000000000000000000000000000000000000000000000000000000cc30c00000000000000000000000000000000000000000000000000000000000cff0ff0000000000000000000000000000000000000000000000000000000000cc30c00000000000000000000000000000000000000000000000000000000000cc0000
  | 0, 4 => 0xfc3fc00000000000000000000000000000000000000000000000000000000000fc30c00000000000000000000000000000000000000000000000000000000000fc30c00000000000000000000000000000000000000000000000000000000000f03f000000000000000000000000000000000000000000000000000000000000f03f0f0000000000000000000000000000000000000000000000000000000000f03f000000000000000000000000000000000000000000000000000000000000f03f000000000000000000000000000000000000000000000000000000000000f00000
  | 0, 5 => 0xffff000000000000000000000000000000000000000000000000000000000000fff0c00000000000000000000000000000000000000000000000000000000000fff0000000000000000000000000000000000000000000000000000000000000ffce300000000000000000000000000000000000000000000000000000000000ffc0000000000000000000000000000000000000000000000000000000000000ffc0000000000000000000000000000000000000000000000000000000000000ffc0000000000000000000000000000000000000000000000000000000000000ffc000
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x54514e000000000000000000000000000000000000000000000000000000000032cb1d000000000000000000000000000000000000000000000000000000000032c8080000000000000000000000000000000000000000000000000000000000320b0400000000000000000000000000000000000000000000000000000000000dc0fb000000000000000000000000000000000000000000000000000000000000c01900000000000000000000000000000000000000000000000000000000000037f70000000000000000000000000000000000000000000000000000000000000315
  | 0, 1 => 0xab88000000000000000000000000000000000000000000000000000000000000a22e0000000000000000000000000000000000000000000000000000000000008924a0000000000000000000000000000000000000000000000000000000000054d35f0000000000000000000000000000000000000000000000000000000000501304000000000000000000000000000000000000000000000000000000000044104200000000000000000000000000000000000000000000000000000000000082110000000000000000000000000000000000000000000000000000000000ab2ca0
  | 0, 2 => 0xc034000000000000000000000000000000000000000000000000000000000000ffffff0000000000000000000000000000000000000000000000000000000000ffeeb90000000000000000000000000000000000000000000000000000000000ffc8080000000000000000000000000000000000000000000000000000000000efbef30000000000000000000000000000000000000000000000000000000000ddf7ff0000000000000000000000000000000000000000000000000000000000cd34e20000000000000000000000000000000000000000000000000000000000abaeb1
  | 0, 3 => 0xf208000000000000000000000000000000000000000000000000000000000000efbef30000000000000000000000000000000000000000000000000000000000ddf7ff0000000000000000000000000000000000000000000000000000000000dd37e60000000000000000000000000000000000000000000000000000000000cdb6f30000000000000000000000000000000000000000000000000000000000cdf4fb0000000000000000000000000000000000000000000000000000000000cd34e20000000000000000000000000000000000000000000000000000000000cd0000
  | 0, 4 => 0xff3fe60000000000000000000000000000000000000000000000000000000000ff3fe60000000000000000000000000000000000000000000000000000000000ff3ce20000000000000000000000000000000000000000000000000000000000fb3fa40000000000000000000000000000000000000000000000000000000000f6ff5f0000000000000000000000000000000000000000000000000000000000f6ff0c0000000000000000000000000000000000000000000000000000000000f23f040000000000000000000000000000000000000000000000000000000000f21b04
  | 0, 5 => 0xffff0c0000000000000000000000000000000000000000000000000000000000fffcea0000000000000000000000000000000000000000000000000000000000fffc080000000000000000000000000000000000000000000000000000000000ffeeb90000000000000000000000000000000000000000000000000000000000ffeca80000000000000000000000000000000000000000000000000000000000ffd84a0000000000000000000000000000000000000000000000000000000000ffca190000000000000000000000000000000000000000000000000000000000ffc808
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 48 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 48 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 48 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 48 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 6 0) :: stateWiresD n (ids >>> 6)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 6 0) :: stateWiresS n (ids >>> 6)
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 7 0 (NN s)
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_31_32 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_31_32 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_31_32 == dom_31_32) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_31_32 goalM u ys) : RunD dom_31_32 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_31_32 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 13 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 13 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 13 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 16 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_16 : ∀ i, 16 ≤ i → i < 32 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 16 16 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_32 : ∀ i, 32 ≤ i → i < 47 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 15 32 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 47 → Z 5 i = true := (range_split (range_split z5_0 z5_16) z5_32)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 16 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 16 0 = true)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_16 : ∀ i, 16 ≤ i → i < 24 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 8 16 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 24 → Z 6 i = true := (range_split z6_0 z6_16)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z7_0 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 1 0 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 1 → Z 7 i = true := z7_0
theorem checked (s : Nat) (hs : s ≤ 7) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
  · exact fun i hi => z6 i (Nat.zero_le i) hi
  · exact fun i hi => z7 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_31_32 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD dom_31_32 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_31_32 roots_31_32 goal_31_32 8 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_31_32 goal_31_32 := by
    have h0 : isConstB dom_31_32 goal_31_32 = false := by decide +kernel
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

end S_31_32

theorem low_31_32 : Lower dom_31_32 roots_31_32 goal_31_32 8 := S_31_32.noCircuit

namespace S_61_2
def pairsG : List (Nat × Nat) := [(3, 7), (3, 11), (3, 19), (3, 35), (6, 7), (6, 14), (6, 38), (10, 11), (10, 14), (10, 26), (18, 19), (18, 26), (22, 23), (22, 30), (22, 54), (34, 35), (34, 38), (42, 43), (42, 46), (42, 58), (50, 51), (50, 54), (50, 58)]
def r1sG : List Nat := [3, 3, 3, 3, 6, 6, 6, 10, 10, 10, 18, 18, 22, 22, 22, 34, 34, 42, 42, 42, 50, 50, 50]
def r2sG : List Nat := [7, 11, 19, 35, 7, 14, 38, 11, 14, 26, 19, 26, 23, 30, 54, 35, 38, 43, 46, 58, 51, 54, 58]
def mpG : Nat := 0x7fffff
def pool6G : List Nat := [11008102762251, 6610123361031, 19834210552602, 37409217775398, 19804263680787]
def xsM : List Nat := roots_61_2.map (· &&& dom_61_2)
def goalM : Nat := goal_61_2 &&& dom_61_2
def NN : Nat → Nat
  | 4 => 1
  | 5 => 5
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xf32b5140
  | 5, 0 => 0xfcb866b4f32b5140944067425e5fa95d3b9dd91e
  | 6, 0 => 0xf32b5140
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xcccccccc00000000000000000000000000000000000000000000000000000000cccc0000cccc0000000000000000000000000000000000000000000000000000cc00cc00cc00cc00000000000000000000000000000000000000000000000000c0c0c0c0c0c0c0c00000000000000000000000000000000000000000000000008888888888888888000000000000000000000000000000000000000000000000444444444444444400000000000000000000000000000000000000000000000000cc00cc00cc00cc00000000000000000000000000000000000000000000000000000000cccccccc
  | 0, 1 => 0xcccccccccc00cc00
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x765435
  | 5, 0, 0 => 0x765425765435764315865435654305
  | 6, 0, 0 => 0x765435
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 24
  | 5 => 24
  | 6 => 24
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 4 0) :: stateWires n (ids >>> 4)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x7f80000000000000000000000000000000000000000000000000000000000000707c0000000000000000000000000000000000000000000000000000000000000e03800000000000000000000000000000000000000000000000000000000000007070000000000000000000000000000000000000000000000000000000000000000f00000000000000000000000000000000000000000000000000000000007ffff0000000000000000000000000000000000000000000000000000000000071fc7f0000000000000000000000000000000000000000000000000000000000007fff
  | 0, 1 => 0x7f8380
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x7fc0480000000000000000000000000000000000000000000000000000000000787e0400000000000000000000000000000000000000000000000000000000004e2ba20000000000000000000000000000000000000000000000000000000000257171000000000000000000000000000000000000000000000000000000000012949f00000000000000000000000000000000000000000000000000000000006d6b60000000000000000000000000000000000000000000000000000000000031d45d0000000000000000000000000000000000000000000000000000000000003fb7
  | 0, 1 => 0x7febea
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 9 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 9 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 9 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 9 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 4 0) :: stateWiresD n (ids >>> 4)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 4 0) :: stateWiresS n (ids >>> 4)
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 4 0 (NN s)
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_61_2 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_61_2 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_61_2 == dom_61_2) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_61_2 goalM u ys) : RunD dom_61_2 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_61_2 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 5 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 5 0 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 5 → Z 5 i = true := z5_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := z6_0
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
  scr dom_61_2 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 3 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD dom_61_2 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_61_2 roots_61_2 goal_61_2 7 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_61_2 goal_61_2 := by
    have h0 : isConstB dom_61_2 goal_61_2 = false := by decide +kernel
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

end S_61_2

theorem low_61_2 : Lower dom_61_2 roots_61_2 goal_61_2 7 := S_61_2.noCircuit

namespace S_31
def pairsG : List (Nat × Nat) := [(1, 5), (1, 9), (3, 7), (3, 11), (3, 19), (4, 5), (6, 7), (6, 14), (8, 9), (10, 11), (10, 14), (10, 26), (12, 13), (12, 14), (17, 19), (17, 21), (17, 25), (18, 19), (18, 26), (20, 21), (22, 23), (22, 30), (24, 25), (24, 26), (28, 29), (28, 30)]
def r1sG : List Nat := [1, 1, 3, 3, 3, 4, 6, 6, 8, 10, 10, 10, 12, 12, 17, 17, 17, 18, 18, 20, 22, 22, 24, 24, 28, 28]
def r2sG : List Nat := [5, 9, 7, 11, 19, 5, 7, 14, 9, 11, 14, 26, 13, 14, 19, 21, 25, 19, 26, 21, 23, 30, 25, 26, 29, 30]
def mpG : Nat := 0x3ffffff
def pool6G : List Nat := [4402510170373, 8800489571593, 6601533425925, 13198536082697, 8800691688201, 13198603192581, 13237375665422, 19804263680275]
def xsM : List Nat := roots_31.map (· &&& dom_31)
def goalM : Nat := goal_31 &&& dom_31
def NN : Nat → Nat
  | 4 => 3
  | 5 => 8
  | 6 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0xac05225e9e9e13794462b438
  | 5, 0 => 0xc5159104be3fb924ac05225e8c616cec640253eb5299e96d3a6b8d412b0e7274
  | 6, 0 => 0xac05225e
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xccccc0c000000000000000000000000000000000000000000000000000000000cccc000000000000000000000000000000000000000000000000000000000000aaaaaaaa00000000000000000000000000000000000000000000000000000000555555550000000000000000000000000000000000000000000000000000000033333333000000000000000000000000000000000000000000000000000000000f0f0f0f0000000000000000000000000000000000000000000000000000000000ff00ff000000000000000000000000000000000000000000000000000000000000ffff
  | 0, 1 => 0xfffff0f000000000000000000000000000000000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000ff00ff0000000000000000000000000000000000000000000000000000000000fcfcf0f000000000000000000000000000000000000000000000000000000000f0f0f0f000000000000000000000000000000000000000000000000000000000cccccccc
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0xcb98550b97540ba854
  | 5, 0, 0 => 0xb98505cb9535cb9855c98515b98655cb8525cb9845db9855
  | 6, 0, 0 => 0xcb9855
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 24
  | 5 => 24
  | 6 => 24
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 4 0) :: stateWires n (ids >>> 4)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x3600c00000000000000000000000000000000000000000000000000000000000360000000000000000000000000000000000000000000000000000000000000001c01f0000000000000000000000000000000000000000000000000000000003fe3fe00000000000000000000000000000000000000000000000000000000003c9f1230000000000000000000000000000000000000000000000000000000000c7cf1f00000000000000000000000000000000000000000000000000000000003fc0ff0000000000000000000000000000000000000000000000000000000000003fff
  | 0, 1 => 0x3fff0e00000000000000000000000000000000000000000000000000000000003ffc0000000000000000000000000000000000000000000000000000000000003c03f0000000000000000000000000000000000000000000000000000000000033e30e000000000000000000000000000000000000000000000000000000000033830e00000000000000000000000000000000000000000000000000000000000360edc
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x2b66cd40000000000000000000000000000000000000000000000000000000002b6481000000000000000000000000000000000000000000000000000000000015bd37f0000000000000000000000000000000000000000000000000000000002a42c8000000000000000000000000000000000000000000000000000000000014991230000000000000000000000000000000000000000000000000000000000c74b1a00000000000000000000000000000000000000000000000000000000001ac07500000000000000000000000000000000000000000000000000000000000037ef
  | 0, 1 => 0x3fffcf50000000000000000000000000000000000000000000000000000000003ffc8100000000000000000000000000000000000000000000000000000000003e53f8a0000000000000000000000000000000000000000000000000000000003befcf5000000000000000000000000000000000000000000000000000000000338b4e50000000000000000000000000000000000000000000000000000000002b66edc
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 14 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 14 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 14 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 14 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 4 0) :: stateWiresD n (ids >>> 4)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 4 0) :: stateWiresS n (ids >>> 4)
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 5 0 (NN s)
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_31 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_31 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := []
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_31 == dom_31) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_31 goalM u ys) : RunD dom_31 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_31 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 3 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 3 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 8 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 8 0 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 8 → Z 5 i = true := z5_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 1 0 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 1 → Z 6 i = true := z6_0
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

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
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

namespace S_62_1
def pairsG : List (Nat × Nat) := [(1, 5), (1, 9), (3, 7), (3, 11), (3, 19), (3, 35), (17, 19), (17, 21), (17, 25), (17, 49), (33, 35), (33, 37), (33, 41), (33, 49)]
def r1sG : List Nat := [1, 1, 3, 3, 3, 3, 17, 17, 17, 17, 33, 33, 33, 33]
def r2sG : List Nat := [5, 9, 7, 11, 19, 35, 19, 21, 25, 49, 35, 37, 41, 49]
def mpG : Nat := 0x3fff
def pool6G : List Nat := [18705139442451]
def xsM : List Nat := roots_62_1.map (· &&& dom_62_1)
def goalM : Nat := goal_62_1 &&& dom_62_1
def NN : Nat → Nat
  | 4 => 2
  | 5 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 4, 0 => 0x4ced50031873cbb6
  | 5, 0 => 0x4ced5003
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xaaaaaaaa00000000000000000000000000000000000000000000000000000000aaaa0000aaaa0000000000000000000000000000000000000000000000000000aaa0aaa0aaa0aaa0000000000000000000000000000000000000000000000000aa00aa00aa00aa00000000000000000000000000000000000000000000000000a0a0a0a0a0a0a0a00000000000000000000000000000000000000000000000008888888888888888
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 4, 0, 0 => 0x2c4428b184
  | 5, 0, 0 => 0x58885
  | _, _, _ => 0
def stateW : Nat → Nat
  | 4 => 19
  | 5 => 19
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 3 0) :: stateWires n (ids >>> 3)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x3c0000000000000000000000000000000000000000000000000000000000000003c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003c
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3e2000000000000000000000000000000000000000000000000000000000000023d0000000000000000000000000000000000000000000000000000000000000198f000000000000000000000000000000000000000000000000000000000000110a0000000000000000000000000000000000000000000000000000000000000885000000000000000000000000000000000000000000000000000000000000047c
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_62_1 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_62_1 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_62_1 == dom_62_1) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_62_1 goalM u ys) : RunD dom_62_1 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_62_1 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
private theorem z3 : ∀ i, 0 ≤ i → i < 0 → Z 3 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 2 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 2 → Z 4 i = true := z4_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 1 0 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 1 → Z 5 i = true := z5_0
theorem checked (s : Nat) (hs : s ≤ 5) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_62_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 4 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 5) (h : RunD dom_62_1 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_62_1 roots_62_1 goal_62_1 6 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_62_1 goal_62_1 := by
    have h0 : isConstB dom_62_1 goal_62_1 = false := by decide +kernel
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

end S_62_1

theorem low_62_1 : Lower dom_62_1 roots_62_1 goal_62_1 6 := S_62_1.noCircuit

namespace S_15
def pairsG : List (Nat × Nat) := [(1, 5), (1, 9), (3, 7), (3, 11), (4, 5), (6, 7), (6, 14), (8, 9), (10, 11), (10, 14), (12, 13), (12, 14)]
def r1sG : List Nat := [1, 1, 3, 3, 4, 6, 6, 8, 10, 10, 12, 12]
def r2sG : List Nat := [5, 9, 7, 11, 5, 7, 14, 9, 11, 14, 13, 14]
def mpG : Nat := 0xfff
def pool6G : List Nat := [6601533425925, 8800489571593]
def xsM : List Nat := roots_15.map (· &&& dom_15)
def goalM : Nat := goal_15 &&& dom_15
def NN : Nat → Nat
  | 3 => 1
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xa8d11512
  | 4, 0 => 0xa8d11512
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00000000000000000000000000000000000000000000000000000000000000f0f0000000000000000000000000000000000000000000000000000000000000cccc000000000000000000000000000000000000000000000000000000000000aaaa
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xe44
  | 4, 0, 0 => 0xe44
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 12
  | 4 => 12
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 2 0) :: stateWires n (ids >>> 2)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xf800000000000000000000000000000000000000000000000000000000000000c70000000000000000000000000000000000000000000000000000000000000036c000000000000000000000000000000000000000000000000000000000000000f
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfca0000000000000000000000000000000000000000000000000000000000000e750000000000000000000000000000000000000000000000000000000000000b6c00000000000000000000000000000000000000000000000000000000000005bf
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 4 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 4 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 4 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 4 then wireAt i else 0
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_15 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_15 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_15 == dom_15) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_15 goalM u ys) : RunD dom_15 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_15 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := z4_0
theorem checked (s : Nat) (hs : s ≤ 4) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_15 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 4) (h : RunD dom_15 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_15 roots_15 goal_15 5 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_15 goal_15 := by
    have h0 : isConstB dom_15 goal_15 = false := by decide +kernel
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

end S_15

theorem low_15 : Lower dom_15 roots_15 goal_15 5 := S_15.noCircuit

namespace S_23_32
def pairsG : List (Nat × Nat) := [(33, 35), (33, 37), (33, 49), (34, 35), (34, 38), (36, 37), (36, 38), (48, 49), (50, 51), (50, 54), (52, 53), (52, 54)]
def r1sG : List Nat := [33, 33, 33, 34, 34, 36, 36, 48, 50, 50, 52, 52]
def r2sG : List Nat := [35, 37, 49, 35, 38, 37, 38, 49, 51, 54, 53, 54]
def mpG : Nat := 0xfff
def pool6G : List Nat := [37525735744803, 39724725445413]
def xsM : List Nat := roots_23_32.map (· &&& dom_23_32)
def goalM : Nat := goal_23_32 &&& dom_23_32
def NN : Nat → Nat
  | 3 => 1
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0xaccce520
  | 4, 0 => 0xaccce520
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00000000000000000000000000000000000000000000000000000000000000f000f00000000000000000000000000000000000000000000000000000000000cc00cc0000000000000000000000000000000000000000000000000000000000aa00aa00000000
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xe44
  | 4, 0, 0 => 0xe44
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 12
  | 4 => 12
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 2 0) :: stateWires n (ids >>> 2)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xf800000000000000000000000000000000000000000000000000000000000000c6000000000000000000000000000000000000000000000000000000000000003180000000000000000000000000000000000000000000000000000000000000007
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xf840000000000000000000000000000000000000000000000000000000000000e720000000000000000000000000000000000000000000000000000000000000b5900000000000000000000000000000000000000000000000000000000000005af
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 4 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 4 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 4 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 4 then wireAt i else 0
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_23_32 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_23_32 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_23_32 == dom_23_32) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_23_32 goalM u ys) : RunD dom_23_32 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_23_32 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := z4_0
theorem checked (s : Nat) (hs : s ≤ 4) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_23_32 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 4) (h : RunD dom_23_32 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_23_32 roots_23_32 goal_23_32 5 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_23_32 goal_23_32 := by
    have h0 : isConstB dom_23_32 goal_23_32 = false := by decide +kernel
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

end S_23_32

theorem low_23_32 : Lower dom_23_32 roots_23_32 goal_23_32 5 := S_23_32.noCircuit

namespace S_51
def pairsG : List (Nat × Nat) := [(3, 19), (3, 35), (17, 19), (17, 49), (18, 19), (33, 35), (33, 49), (34, 35), (48, 49), (50, 51)]
def r1sG : List Nat := [3, 3, 17, 17, 18, 33, 33, 34, 48, 50]
def r2sG : List Nat := [19, 35, 19, 49, 19, 35, 49, 35, 49, 51]
def mpG : Nat := 0x3ff
def pool6G : List Nat := [18705139442451]
def xsM : List Nat := roots_51.map (· &&& dom_51)
def goalM : Nat := goal_51 &&& dom_51
def NN : Nat → Nat
  | 3 => 1
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x6ba3d11
  | 4, 0 => 0x6ba3d11
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xf000f00000000000000000000000000000000000000000000000000000000000f0000000f0000000000000000000000000000000000000000000000000000000c000c000c000c000000000000000000000000000000000000000000000000000a000a000a000a
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xe44
  | 4, 0, 0 => 0xe44
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 12
  | 4 => 12
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 2 0) :: stateWires n (ids >>> 2)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x3e0000000000000000000000000000000000000000000000000000000000000031c0000000000000000000000000000000000000000000000000000000000000293000000000000000000000000000000000000000000000000000000000000006f
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3ea000000000000000000000000000000000000000000000000000000000000035d00000000000000000000000000000000000000000000000000000000000002b700000000000000000000000000000000000000000000000000000000000003ff
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 4 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 4 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 4 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 4 then wireAt i else 0
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_51 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_51 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_51 == dom_51) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_51 goalM u ys) : RunD dom_51 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_51 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := z4_0
theorem checked (s : Nat) (hs : s ≤ 4) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_51 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 4) (h : RunD dom_51 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_51 roots_51 goal_51 5 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_51 goal_51 := by
    have h0 : isConstB dom_51 goal_51 = false := by decide +kernel
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

end S_51

theorem low_51 : Lower dom_51 roots_51 goal_51 5 := S_51.noCircuit

namespace S_54_1
def pairsG : List (Nat × Nat) := [(1, 5), (3, 7), (3, 19), (3, 35), (17, 19), (17, 21), (17, 49), (33, 35), (33, 37), (33, 49)]
def r1sG : List Nat := [1, 3, 3, 3, 17, 17, 17, 33, 33, 33]
def r2sG : List Nat := [5, 7, 19, 35, 19, 21, 49, 35, 37, 49]
def mpG : Nat := 0x3ff
def pool6G : List Nat := [18705139442451]
def xsM : List Nat := roots_54_1.map (· &&& dom_54_1)
def goalM : Nat := goal_54_1 &&& dom_54_1
def NN : Nat → Nat
  | 3 => 1
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x2f304193
  | 4, 0 => 0x2f304193
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xaa00aa0000000000000000000000000000000000000000000000000000000000aa000000aa000000000000000000000000000000000000000000000000000000a000a000a000a00000000000000000000000000000000000000000000000000088008800880088
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xe44
  | 4, 0, 0 => 0xe44
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 12
  | 4 => 12
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 2 0) :: stateWires n (ids >>> 2)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x38000000000000000000000000000000000000000000000000000000000000000700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000e
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x3c800000000000000000000000000000000000000000000000000000000000002740000000000000000000000000000000000000000000000000000000000000123000000000000000000000000000000000000000000000000000000000000009e
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 4 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 4 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 4 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 4 then wireAt i else 0
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_54_1 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_54_1 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_54_1 == dom_54_1) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_54_1 goalM u ys) : RunD dom_54_1 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_54_1 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := z4_0
theorem checked (s : Nat) (hs : s ≤ 4) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_54_1 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 4) (h : RunD dom_54_1 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_54_1 roots_54_1 goal_54_1 5 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_54_1 goal_54_1 := by
    have h0 : isConstB dom_54_1 goal_54_1 = false := by decide +kernel
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

end S_54_1

theorem low_54_1 : Lower dom_54_1 roots_54_1 goal_54_1 5 := S_54_1.noCircuit

namespace S_39
def pairsG : List (Nat × Nat) := [(1, 5), (3, 7), (3, 35), (4, 5), (6, 7), (6, 38), (33, 35), (33, 37), (34, 35), (34, 38), (36, 37), (36, 38)]
def r1sG : List Nat := [1, 3, 3, 4, 6, 6, 33, 33, 34, 34, 36, 36]
def r2sG : List Nat := [5, 7, 35, 5, 7, 38, 35, 37, 35, 38, 37, 38]
def mpG : Nat := 0xfff
def pool6G : List Nat := [4402914403077]
def xsM : List Nat := roots_39.map (· &&& dom_39)
def goalM : Nat := goal_39 &&& dom_39
def NN : Nat → Nat
  | 3 => 2
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x257ee56101edb3d8
  | 4, 0 => 0x257ee561
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xff00000000000000000000000000000000000000000000000000000000000000f0000000f0000000000000000000000000000000000000000000000000000000cc000000cc000000000000000000000000000000000000000000000000000000cc00000000000000000000000000000000000000000000000000000000000000aa000000aa
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x8d040c83
  | 4, 0, 0 => 0x8d04
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 16
  | 4 => 16
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 3 0) :: stateWires n (ids >>> 3)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xfc00000000000000000000000000000000000000000000000000000000000000c380000000000000000000000000000000000000000000000000000000000000336000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000000c7
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfe40000000000000000000000000000000000000000000000000000000000000ebb0000000000000000000000000000000000000000000000000000000000000b760000000000000000000000000000000000000000000000000000000000000b6400000000000000000000000000000000000000000000000000000000000005df
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 5 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 5 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 5 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 5 then wireAt i else 0
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_39 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_39 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_39 == dom_39) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_39 goalM u ys) : RunD dom_39 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_39 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 2 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 2 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 2 → Z 3 i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := z4_0
theorem checked (s : Nat) (hs : s ≤ 4) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_39 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 4) (h : RunD dom_39 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_39 roots_39 goal_39 5 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_39 goal_39 := by
    have h0 : isConstB dom_39 goal_39 = false := by decide +kernel
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

end S_39

theorem low_39 : Lower dom_39 roots_39 goal_39 5 := S_39.noCircuit

namespace S_29_2
def pairsG : List (Nat × Nat) := [(3, 7), (3, 11), (3, 19), (6, 7), (6, 14), (10, 11), (10, 14), (10, 26), (18, 19), (18, 26), (22, 23), (22, 30)]
def r1sG : List Nat := [3, 3, 3, 6, 6, 10, 10, 10, 18, 18, 22, 22]
def r2sG : List Nat := [7, 11, 19, 7, 14, 11, 14, 26, 19, 26, 23, 30]
def mpG : Nat := 0xfff
def pool6G : List Nat := [6610123361031, 11008102762251]
def xsM : List Nat := roots_29_2.map (· &&& dom_29_2)
def goalM : Nat := goal_29_2 &&& dom_29_2
def NN : Nat → Nat
  | 3 => 2
  | 4 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 3, 0 => 0x644f355f3162df00
  | 4, 0 => 0x3162df00
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0xccccc0c000000000000000000000000000000000000000000000000000000000cccc000000000000000000000000000000000000000000000000000000000000cc00cc0000000000000000000000000000000000000000000000000000000000c0c0c0c00000000000000000000000000000000000000000000000000000000088888888
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0x11036884
  | 4, 0, 0 => 0x6884
  | _, _, _ => 0
def stateW : Nat → Nat
  | 3 => 16
  | 4 => 16
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 3 0) :: stateWires n (ids >>> 3)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0xf180000000000000000000000000000000000000000000000000000000000000f0000000000000000000000000000000000000000000000000000000000000000e00000000000000000000000000000000000000000000000000000000000000c180000000000000000000000000000000000000000000000000000000000000007
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0xfdd0000000000000000000000000000000000000000000000000000000000000f840000000000000000000000000000000000000000000000000000000000000af20000000000000000000000000000000000000000000000000000000000000c59000000000000000000000000000000000000000000000000000000000000052f
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 5 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 5 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 5 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 5 then wireAt i else 0
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

theorem cutHitH_sound {u ys} (h : cutHitH u (hk 0 ys) ys = true) : ¬ RunD dom_29_2 goalM u ys := by
  unfold cutHitH at h
  simp only [Bool.and_eq_true] at h
  have hc := h.2
  unfold checkCutByIdx at hc
  split at hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_29_2 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_29_2 == dom_29_2) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {u ys} (h : RunD dom_29_2 goalM u ys) : RunD dom_29_2 goalM u (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h

def Z (s : Nat) := bar dom_29_2 goalM pairsG r1sG r2sG mpG SD SS NN htAt idxH ori 0 pool6G cutHitH s
private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega
private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega
private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z3_0 : ∀ i, 0 ≤ i → i < 2 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 2 0 = true)
private theorem z3 : ∀ i, 0 ≤ i → i < 2 → Z 3 i = true := z3_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z4_0 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 1 0 = true)
private theorem z4 : ∀ i, 0 ≤ i → i < 1 → Z 4 i = true := z4_0
theorem checked (s : Nat) (hs : s ≤ 4) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
def RootG (s : Nat) : Bool :=
  scr dom_29_2 goalM s pool6G xsM || cutHit s (ori xsM) || found SS NN idx s (ori xsM)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 3 = true := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 4) (h : RunD dom_29_2 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutHit_sound hcut (ori_ok h)
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (by decide +kernel) rfl rfl (by decide +kernel) SD_eq (by decide +kernel) ori_ok cutHitH_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))

theorem noCircuit : Lower dom_29_2 roots_29_2 goal_29_2 5 := by
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst dom_29_2 goal_29_2 := by
    have h0 : isConstB dom_29_2 goal_29_2 = false := by decide +kernel
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

end S_29_2

theorem low_29_2 : Lower dom_29_2 roots_29_2 goal_29_2 5 := S_29_2.noCircuit

def isoMv_59 : List (Nat × Nat) := [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]
theorem low_59 : Lower dom_59 roots_59 goal_59 8 :=
  lower_iso isoMv_59 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_55

def isoMv_47_16 : List (Nat × Nat) := [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]
theorem low_47_16 : Lower dom_47_16 roots_47_16 goal_47_16 8 :=
  lower_iso isoMv_47_16 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_31_32

def isoMv_47 : List (Nat × Nat) := [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]
theorem low_47 : Lower dom_47 roots_47 goal_47 7 :=
  lower_iso isoMv_47 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_31

def isoMv_57_2 : List (Nat × Nat) := [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)]
theorem low_57_2 : Lower dom_57_2 roots_57_2 goal_57_2 5 :=
  lower_iso isoMv_57_2 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_23_32

def isoMv_58_1 : List (Nat × Nat) := [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)]
theorem low_58_1 : Lower dom_58_1 roots_58_1 goal_58_1 5 :=
  lower_iso isoMv_58_1 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_54_1

def isoMv_27 : List (Nat × Nat) := [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]
theorem low_27 : Lower dom_27 roots_27 goal_27 5 :=
  lower_iso isoMv_27 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_39

def isoMv_45_2 : List (Nat × Nat) := [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]
theorem low_45_2 : Lower dom_45_2 roots_45_2 goal_45_2 5 :=
  lower_iso isoMv_45_2 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_29_2

namespace S_63
def pairsG : List (Nat × Nat) := [(1, 5), (1, 9), (3, 7), (3, 11), (3, 19), (3, 35), (4, 5), (6, 7), (6, 14), (6, 38), (8, 9), (10, 11), (10, 14), (10, 26), (12, 13), (12, 14), (17, 19), (17, 21), (17, 25), (17, 49), (18, 19), (18, 26), (20, 21), (22, 23), (22, 30), (22, 54), (24, 25), (24, 26), (28, 29), (28, 30), (33, 35), (33, 37), (33, 41), (33, 49), (34, 35), (34, 38), (36, 37), (36, 38), (40, 41), (42, 43), (42, 46), (42, 58), (44, 45), (44, 46), (48, 49), (50, 51), (50, 54), (50, 58), (52, 53), (52, 54), (56, 57), (56, 58), (60, 61), (60, 62)]
def r1sG : List Nat := [1, 1, 3, 3, 3, 3, 4, 6, 6, 6, 8, 10, 10, 10, 12, 12, 17, 17, 17, 17, 18, 18, 20, 22, 22, 22, 24, 24, 28, 28, 33, 33, 33, 33, 34, 34, 36, 36, 40, 42, 42, 42, 44, 44, 48, 50, 50, 50, 52, 52, 56, 56, 60, 60]
def r2sG : List Nat := [5, 9, 7, 11, 19, 35, 5, 7, 14, 38, 9, 11, 14, 26, 13, 14, 19, 21, 25, 49, 19, 26, 21, 23, 30, 54, 25, 26, 29, 30, 35, 37, 41, 49, 35, 38, 37, 38, 41, 43, 46, 58, 45, 46, 49, 51, 54, 58, 53, 54, 57, 58, 61, 62]
def mpG : Nat := 0x3fffffffffffff
def pool6G : List Nat := [4402510170373, 8800489571593, 6601533425925, 13198536082697, 8800691688201, 13198603192581, 4402914403077, 21995368878853, 39587286491909, 19804263680275, 6610123361031, 8801230068233, 4403183560197, 21995369604613, 39587419130117, 11020903449870, 36356950790961, 18709046233349, 18726361109257, 18709717650949, 36319084024585, 18709718897413, 19864425989395, 18718309557765, 36310359083269, 11000252406281, 4411773491717, 55019087923482, 18726427428105, 26431785607962, 18743607297289, 13198804848137, 24262472500499, 13199141441029, 46321424532771, 4402914403081, 46321424533795, 55001403820326, 55156021594406, 66091899488517, 52918461532465, 61616157696794, 61714554554673, 57200662876966, 4402745837829, 36319085533705, 57247722243377, 18743810204421]
def xsM : List Nat := roots_63.map (· &&& dom_63)
def goalM : Nat := goal_63 &&& dom_63
def NN : Nat → Nat
  | 5 => 15
  | 6 => 123
  | 7 => 326
  | 8 => 131
  | 9 => 16
  | 10 => 1
  | _ => 0
def HT : Nat → Nat → Nat
  | 5, 0 => 0xbe271c8da9d7edd6a41f66e59fa06ee38beba93e674bfd885c3cfa52532a6f1247faa54a3294dd262c3b49d118f5d15710d6c9fb08553ab50844917b
  | 6, 0 => 0x48208d5b47992a1746101c7d44fd7ad443f9aa2241d0c44040f35052408614eb383f24cd36bd7d7436b34ac935c3f55a35626a9e347d3d4f33d6909a33c54d993292cbac31c47c2e317e6f9030d0deed3099cb89304f0a8f2ee6f2792ebe6d1e2a902adb29b62f0f28becc5b2779c54f2540075924d87e4324af7386235b96e02244ea1622240e13211585151eb8214b1cdb9a501cd4a8b61a57720e182c9d1f181e35b9169c522615e9827215bb7540154fe2f0152e636e0d5edc4a0bcf66f60abc61d8093087d408f317a508b6a952088502d80762ccac06e4336306d95953065ba74406165d7604af4c4e040779340251a44601af582a007ff329006e6655
  | 6, 1 => 0xf55da781ef07b76ee580cb8ae239d3cee0688701dd8f3560db4faba4da6f5407d3d9d373d11902c2b8e76ab4b5ed8edbb110dfb9ad0897dcac947fdeaa9fb6c0a97672a3a6d960c6a35c9dd6a0b7fc57a008b32d9e04e86b9b4906209aecc3119784c54096ebab2d95584c7b93b517009304109191d2873e8dfb55e68a893019872a2994847b91867ef74a907c3409da78ad1f3a788aa5397744b5187540a7b3734bd99471fc8ae76d2273ec6a8772f968f7280068eb1e2568a37bea6838efd067aab8ca63e5ff9a6208e6b157530f6053884309534dfcc25101a6094f7a9f414ca3c01c4a75e4464952e235
  | 7, 0 => 0x1c93c9e31c8b50101c193f401baefe391b8076ce1b42406d1b3bd7731a04b31019ba301a19affd6f1980bc291921f28d186c3881182b4031181c7acd181315341808214e17ddd9591673385e15d3b4e415ba6e63153fc09e14cc203913dbfd0413bbd24e13967e2f130a5a8912cd450012300b71120eee5411bd50f410a92875109410fb1010f37c0ee057d40e79ef230e42a8180e19c3470d3dec4f0d34394d0b3080880af197a60a7677f50a1382ef0919997807d530e907b8035306415f2606237d4e057c0b7a052aa49504824cd4046088880442bd8604064f33029f514b0232af73020b934d01a44b7b0166035701430e7d01189ba900d76e02003e83f9
  | 7, 1 => 0x3c3792743c21f90f3b1599a03aff97ee3a950bd439c6347938e8b0de38c0d21d3812097437962c63377efee63644f7dd34717ed0346502b533cd017f32eb626b32bc68083252e2e031959d4e303037e92ff7be3e2f67316b2e9b5e9e2e9987ce2e8bb09f2e8a65942e28d5a52df013cb2dd37e3b2d7296ec2d5ab92f2d06d0c22c009a592bc612742bbea46f2b811d732b7b467f2b71f2482b52c4ba2b35846d2ad6e7a929af2b6429259dd728bd116f28ba41a327d25737279f070c2748e4d0265916eb2648e3a82578bf4e24f59d08240b208923f0c29e23e65826232c6add21f73ff420f506ac204fb0ae204b60b61ee33eba1df8f12c1cd038361c96ea49
  | 7, 2 => 0x6087d247607f1ebe601d48af5f5675315f3648d15f18482b5ef408b65e2a7c045dd41be55d0b15675c0bbbc75bccb9a15b5034d95b34bf745a5bc665592f01985925466958f4b53d5794fb7056488c3a5617fb0e55f5a32a54fd3cee54b99c515462936b53c0149952fb824352a2b541509cf9d3506b190f501ec8144ffcc3574e5372144c6601af4c2eb5784b77d19c4b222bf34b093b3e4aeba8ec4a9428d249e8ddff49cc486f49bb2fc34989478048f6d72e48e6246948b0ac9d47fa579745a7f59844fe76974486548a445ca64c441caf3c43c1fcc9431f7df74243f1c9418c685a3fd3ef6d3fca826d3f3bf5403f2afc363d3e89f93d2c7c353cba78eb
  | 7, 3 => 0x97a53cfb96424b419605da2495955e8d94b8834e9329f8a28f0315698e92684e8e3f8c778e2302ba8d94f5ad8cda2ccd8ca14df68b6aabe78b3b49c589b9a4c5884d6a8e8786f1f785f6241e82e2ff4781e0e92680b2da9b7fe1a60d7f123d697f0507a47ef09be27eeeae697eaf48d67da0a7537c79c7f27bd28ea77ad7bf5b79f05dc079cce619797004af7849360277b0fd7076549099760a28d074cf39e473da4b1a72e94115727718da72286c4f6fb8decd6edb0ec36df7e42c6da2ccf46b302ff16a729fe4694fc71e68935998680f799366e47320663dd11465b3f9f76546574f6433ac9f6423aefe6407b8f162d73fc861d0c2e5615bf9fd6119d7e1
  | 7, 4 => 0xe849f352e4e88dfde41e5447e0d0507fe041dc16dd6521e7dd5eacb4db4f33a9dae9e1fadae11edcda5a49e8d85d0165d661e951d405b4dbcf2627a1c9f553bac8bcd3fdc7d22c68c7b46166c6dfc8e3c6919570c4d7a737c25c674ac1f9e755bd05f62ebab9a1bdba9cdb19b91d4ce9b7dce78eb75d88c1b66e795fb5446adbb43b799cb41b0a9db413f1b2ae2a8799ae1abeb8aca9b064ac829a92ac71715eaba990fba99c2534a994b72fa96b9408a7853e24a635ef77a57519cca494c22fa44634c2a39ec2eea372610ea369b0e6a362549ba2d0fecfa0c208bf9ed6de7b9cdce07a9c0b11509b74bd5f9b258fe99af887159aca79e39a6201359848d5ba
  | 7, 5 => 0xfc53b9bbf966b7b2f31ff462f1f83380f1c1d962ed3bc136
  | 8, 0 => 0x4f0fba7a4ed5e3f64e2ce2974c4c79c44c173de94b62f61f4ac0774d4a0d197449e125c648b0ac9d44cd758b425327d74214fad14079af633f49363a3e4ce77f3d8620523c21f90f3bf167e33a8b9b213899ed18387c2216363c57f435f834e9359f67e7354bc4fd342cdee932ba82ac315024ba2f62b4552f1362052de85b922d90db782cb7e2692b81626d2b44f41a29f1177428a4a83e275958f226beaf6f261c309d22c7351320292edb1fb72b911ec21db31be563841b52f332175a929b14121a0c11eb7ccf119811441187183a0f8898390e93ae780e7e15130e7dd0190cabde0a0c22507d0acf09dd06cd9ad406291d83059e8b1703f1b95200f5a3d2
  | 8, 1 => 0xe73f702ce7283c3dd87f9952d7d8277ed5d13c99d4fb6d4fceeb1ad8c41df566c31b6fd9bd2744b8b253eee6b12375bdb080f6ebaf1123ebae064aa9ab681b8eaa8df529aa87c3f1a661d0dfa494c22fa3f2435da1807b919d3508f494b8834e90061e318a81f0ca89beef4c88f300e1867726a183c5bc5283233d80828511a4806266ad7ecd8d627e05acff7dd5c4a57d303bbe7cea112d7bf841387bf0d33379e15a2877d135d076f0de3375c5ccea705b5d9f6f38fc7e6e9f1e276cbe1d396c4b6e046bcf90f3689e6745679d352a62623a355aa8a6b958a5f17754b47b985316929452acbe7d523dc211520a3fab515c2919514aca6d51099cc64fb2394c
  | 8, 2 => 0xffcceadcec164c1eea39f55d
  | 9, 0 => 0x7e1a8a567cea112d76f0de33764e5f61705b5d9f5fbac6fd5cde0cce4f8c57c242b779a334064f6c1e7359ed1b78d4bc1729918f0e7e151305169eb001bed059
  | 10, 0 => 0x42b779a3
  | _, _ => 0
def dictB : Nat → Nat → Nat
  | 0, 0 => 0x550f5f00550f5f0000000000000000000000000000000000000000000000000055005500550055000000000000000000000000000000000000000000000000000f000f000f000f000000000000000000000000000000000000000000000000000c000c000c000c000000000000000000000000000000000000000000000000000a000a000a000a00000000000000000000000000000000000000000000000000050f0f00050f0f0000000000000000000000000000000000000000000000000000ffff0000ffff00000000000000000000000000000000000000000000000000000000ffffffff
  | 0, 1 => 0x5050f0f05050f0f00000000000000000000000000000000000000000000000005050505ffffffff000000000000000000000000000000000000000000000000050505050505050500000000000000000000000000000000000000000000000003030f0f03030f0f00000000000000000000000000000000000000000000000001010f0f01010f0f00000000000000000000000000000000000000000000000000ff00ff00ff00ff00000000000000000000000000000000000000000000000000ee00ee00ee00ee0000000000000000000000000000000000000000000000000077007700770077
  | 0, 2 => 0x44444444444444440000000000000000000000000000000000000000000000003377337733773377000000000000000000000000000000000000000000000000333733373337333700000000000000000000000000000000000000000000000033333333333333330000000000000000000000000000000000000000000000001111111111ff11ff0000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f0000000000000000000000000000000000000000000000000e0e0e0e0e0e0e0e0000000000000000000000000000000000000000000000000707070707070707
  | 0, 3 => 0x88888888888888880000000000000000000000000000000000000000000000008888888800000000000000000000000000000000000000000000000000000000777777777777777700000000000000000000000000000000000000000000000066666666666666660000000000000000000000000000000000000000000000005577557755775577000000000000000000000000000000000000000000000000555555555555555500000000000000000000000000000000000000000000000055555555000000000000000000000000000000000000000000000000000000005555000055550000
  | 0, 4 => 0xaaaaaaaaaaaaaaaa000000000000000000000000000000000000000000000000aaaaaaaa00000000000000000000000000000000000000000000000000000000aaaaaaa0aaa0aaa0000000000000000000000000000000000000000000000000aaaa0000aaaa0000000000000000000000000000000000000000000000000000aaa0aaa0aaa0aaa0000000000000000000000000000000000000000000000000aa88aa88aa88aa88000000000000000000000000000000000000000000000000aa88aa88aa00aa00000000000000000000000000000000000000000000000000a8a8a8a8a8a8a8a8
  | 0, 5 => 0xcccc0000cccc0000000000000000000000000000000000000000000000000000ccc8ccc8ccc8ccc8000000000000000000000000000000000000000000000000ccc0ccc0ccc0ccc0000000000000000000000000000000000000000000000000cc88cc88cc88cc88000000000000000000000000000000000000000000000000c8c8c8c8c8c8c8c8000000000000000000000000000000000000000000000000c8c8c0c0c8c8c0c0000000000000000000000000000000000000000000000000bbbbbbbbbbbbbbbb000000000000000000000000000000000000000000000000bbb3bbb3bbb3bbb3
  | 0, 6 => 0xeeee0000eeee0000000000000000000000000000000000000000000000000000eeeceeecaaa0aaa0000000000000000000000000000000000000000000000000dddddddddddddddd000000000000000000000000000000000000000000000000dddddddd55555555000000000000000000000000000000000000000000000000dddd5555dddd5555000000000000000000000000000000000000000000000000cccccccccccccccc000000000000000000000000000000000000000000000000cccccccc00000000000000000000000000000000000000000000000000000000cccc888888888888
  | 0, 7 => 0xf0f0fffff0f0ffff000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f0000000000000000000000000000000000000000000000000eeeeeeeeeeeeeeee000000000000000000000000000000000000000000000000eeeeeeeeee00ee00000000000000000000000000000000000000000000000000eeeeeeeeaaaaaaaa000000000000000000000000000000000000000000000000eeeeeeee00000000000000000000000000000000000000000000000000000000eeeee0e0eeeee0e0000000000000000000000000000000000000000000000000eeeeaaaaeeeeaaaa
  | 0, 8 => 0xfafa0000fafa0000000000000000000000000000000000000000000000000000faf8faf8faf8faf8000000000000000000000000000000000000000000000000faf8faf8faf0faf0000000000000000000000000000000000000000000000000f8f8f8f8f8f8f8f8000000000000000000000000000000000000000000000000f8f8f8f8f0f0f0f0000000000000000000000000000000000000000000000000f8f8f0f0f8f8f0f0000000000000000000000000000000000000000000000000f5f5f5f5f5f5f5f5000000000000000000000000000000000000000000000000f3f3f3f3f3f3f3f3
  | 0, 9 => 0xfcfcf0f0fcfcf0f0000000000000000000000000000000000000000000000000fcf8fcf8fcf8fcf8000000000000000000000000000000000000000000000000fca8fca8fca8fca8000000000000000000000000000000000000000000000000fafafafafafafafa000000000000000000000000000000000000000000000000fafafafafa00fa00000000000000000000000000000000000000000000000000fafafafaf0f0f0f0000000000000000000000000000000000000000000000000fafafafa00000000000000000000000000000000000000000000000000000000fafaf0f0fafaf0f0
  | 0, 10 => 0xff77ff77ff77ff77000000000000000000000000000000000000000000000000ff55ff55ff55ff55000000000000000000000000000000000000000000000000ff33ff33ff33ff33000000000000000000000000000000000000000000000000ff00ff00ffffffff000000000000000000000000000000000000000000000000ff00ff00ff00ff00000000000000000000000000000000000000000000000000fefef0f0fefef0f0000000000000000000000000000000000000000000000000fcfcfcfcfcfcfcfc000000000000000000000000000000000000000000000000fcfcfcfcf0f0f0f0
  | 0, 11 => 0xffbbffbbffbbffbb000000000000000000000000000000000000000000000000ffaaffaaffaaffaa000000000000000000000000000000000000000000000000ffaaffaaff00ff00000000000000000000000000000000000000000000000000ffaaff00ffaaff00000000000000000000000000000000000000000000000000ffaaf0a0ffaaf0a0000000000000000000000000000000000000000000000000ffaa0000ffaa0000000000000000000000000000000000000000000000000000ffa8ffa8ffa8ffa8000000000000000000000000000000000000000000000000ff88ff88ff88ff88
  | 0, 12 => 0xfff8fff8fff8fff8000000000000000000000000000000000000000000000000fff5fff5fff5fff5000000000000000000000000000000000000000000000000fff3fff3fff3fff3000000000000000000000000000000000000000000000000fff0fff0fff0fff0000000000000000000000000000000000000000000000000ffeeffeeff00ff00000000000000000000000000000000000000000000000000ffccffccffccffcc000000000000000000000000000000000000000000000000ffccffccff00ff00000000000000000000000000000000000000000000000000ffccff00ffccff00
  | 0, 13 => 0xfffcfffcfffcfffc000000000000000000000000000000000000000000000000fffcfff0fffcfff0000000000000000000000000000000000000000000000000fffafffafffafffa000000000000000000000000000000000000000000000000fffafffaff00ff00000000000000000000000000000000000000000000000000fffafffa00000000000000000000000000000000000000000000000000000000fffafff0fffafff0000000000000000000000000000000000000000000000000fffaf0f0fffaf0f0000000000000000000000000000000000000000000000000fffa0000fffa0000
  | 0, 14 => 0xfffff0f0fffff0f0000000000000000000000000000000000000000000000000fffff0f0f0f0f0f0000000000000000000000000000000000000000000000000ffffaaaaaaaaaaaa000000000000000000000000000000000000000000000000ffffaaa0aaa0aaa0000000000000000000000000000000000000000000000000ffff888888888888000000000000000000000000000000000000000000000000ffff555555555555000000000000000000000000000000000000000000000000ffff0000ffff0000000000000000000000000000000000000000000000000000ffff000000000000
  | 0, 15 => 0xffffffffff00ff00000000000000000000000000000000000000000000000000ffffffff00000000000000000000000000000000000000000000000000000000fffffff0fff0fff0000000000000000000000000000000000000000000000000ffffff00ff00ff00
  | _, _ => 0
def stateB : Nat → Nat → Nat → Nat
  | 5, 0, 0 => 0x1efbe47a7d7df74e502afbc8e59275f7df21a28beadb24e157de4a4c93afac8c93875e34df1c00befbb234157d717c7052fbef917275e3925a728bebbd37c71724b649c0afbef9d9275
  | 6, 0, 0 => 0x1c723e78c93b00f7c723e7a7d80537c68a0100c03be4a69ca00601c76537c9ca300a6fdf272801807a7cf4f8a02c03d77c955927601ef8dc7cc8d300e34cd142401807ba6c8d1202c03d717a7c90a601ebbd3889ca300f5c5f3d3a29807aa4f992714c03d77a7399276
  | 6, 0, 1 => 0x1c69be7a74037ae9c69be649dc053a4f992700deb8d37cd9927701ddf2728280300f5c59272229807bc8f9bb24ec03dd37c68a01601ef24c649c0b00f74dfbe4e51807be3a9f324ec03df1c911927601ef8d334509300f4dd9272429807be39192b4ec03d71a6f939c6
  | 6, 0, 2 => 0x16a9b24e480300e3931be649d807be34df3d3ac038d37cc93936014dd324e480b00f74e93e649d807aef4d3940ac02dd37cc9380601eb8d37ca13b00e34e6324601807be39262728c029be7a7c080601ea9be649c3b00f4f99271205807aef9299a28c03d537ef8d146
  | 6, 0, 3 => 0x1ebbca649c5300e3529b23449805aa6f939400c03dd36ec9392601efbefc8c93b00f7c6c3e6469807ae34e2b24ec03df1b2f99276014df3c649c0b00f49ca121405807ba6f9e9f02c029b7649c900601c69bc649c9300f5df2554e51807be34de9f24c03d537cc938b6
  | 6, 0, 4 => 0xf991a140403007ef992714018071a6f9a9700c03df7a6f8d14601ef8dc7c9ca300e2c8d121401807aef1192714c03d5aa6f8d146014d39424040300f5df25d649d807be39df324ec03d77c9859276f5c69be649d2b80f7c69b24e458054a6f991a02c038c97c9ca0a6
  | 6, 0, 5 => 0x1efbd388c93b00f7c5f323415807aa6f4f9202c03df1b0f9e9f601ea9be649c1300f7de9be7a7d8077a71192700c03df7c8c939460003df7649c2a80f5c6f3e46518071a6f972700c03df1c8f97276014e4be64680b00f54cd1424058000f7df23234a03dd37ce59276
  | 6, 0, 6 => 0x3d64b6c93a80ef4d9270a01807ae34df272ac03d5ba6f9394601ea9b24e440b00e3529a728498077c94d91a00c0007ae34df1c501eb8d388b53b00f5de9b24e41807ae379f3242c03de8c8f9927601dea537cc8d300f7df23d649d807aa73192302c034d37cc93806
  | 6, 0, 7 => 0xf5c69be3a71807ae34e7ab4ec03d71345090a6014df3a64680b00f7df2324e7d807ae34df1f38c03df7db91927601efbe4649cd30001efbe44e51407be3319270ac0192724280806
  | 7, 0, 0 => 0x1eb8d37c9d194701ea9be629ca01701eb8dfa6f9394701c69be6ac8d00701eb8f0a6c8d12701ea9be6468a01701ebbe4a6c9394701eb8d3629ca12701ebbd37cc939d701c69be6468b80701eb8d37cd1927701eb8d36468a1270003d77a6c9385601c725e7cc93807014df3d649c080701eb8d38cf99277
  | 7, 0, 1 => 0x1eb8d37c98d14701ee9be7ac9381701ebbd388c939f701eb8e0a6c939270003de47cc9381601eb8d3a0f991a701eb8cf7cc938a701ef8d37ac939270003d777cc8d0a601eb8d382f8d14700038d37cf4f80601ef8d3a2f991a70003d324e4850160003d717cc9389601ef8d37cc8f9a70003d77c9799276
  | 7, 0, 2 => 0x1ebbd37c9cf94701eb8f0a6f8d14700029be74c9381601eb8be64c4d0a701ea9be6468c81701eb8d8a6c9392701eb8d37c68c14701ebbbe649d30a701ef8d37cd591a700038d374c9392601eb8d8a6f9e9f701eb8d37ce191f701c6ad37cc9380701ebbd37c9cd14701eb8be6490d0a701ebb71a7319277
  | 7, 0, 3 => 0x1ebbe4a6f5927701ebbdda6f9927701c69be649d000700038c97cc938a601ebbd37ca5394701eb8e4a701927700038d37cf1927601ebbe1a6f992770003d714e5090a60003df1a6f9e9f601c69b25e9c900701eb8e6a6f992770002d537cc9380601ebbbe649ca0a701eac537cc9381701eb8d37cc8d057
  | 7, 0, 4 => 0x1ef8edc8f9927701eb8b24e7c90a701ef8e47cc939a701eb8d6a6c8d12701c6a5398f9927701eb8be649ce8a701eb8d39af9927701e9f324e68501701eb8e0a6f9394701ea9ca7cc9381701eb8b24e6890a701c75e4a6f992770003df1c8f9394601ea9be76c9381701ea9be7ac8d0170003d3e4e505016
  | 7, 0, 5 => 0x1eb8d390f939470003bd37cc8d00601c6f53649c900701ea8be649c501701eb8d37cc93a1701ef8e47cc939f701ef8d37cc93a0701eb8d37cc938c70003dd37cdd927600029b24e48080601e9f324e7c501701eb8d8a6f9394701ef8d364bd392701eab537cc8d01701c76d37cc9380701eb8de7cc93857
  | 7, 0, 6 => 0x1eb8d380f94a7701c69be6490d00701eb8d394f9394701c69be64a5380701c725398c9380701eb8c07cc938a7017a9be649c080701eb8d37ced394701eb8d386c939f701ea9c17cc9381701eb8d5a6f991a701c69be64b1380701c69cf7cc9380700038d4a6f991a601eb8d37c9ce97701c72537ce99277
  | 7, 0, 7 => 0x1ef8d37cbd39470003d71a6f8d14601eb8d384c939f70003df7a6f991a60003df1b8f9927601eb8be4e7ca0a70003dd3649c901601de9be649ca00701eb8d37cc901a70003d537cdd91a6017ad537cc9380701c69be649cb80701ebb71a6f939470003d5aa6f991a601eb8be4e68a0a701eb8d37cc938f7
  | 7, 0, 8 => 0x3d536468901601eb8d37cad394701c69be649ce80701ea9be64b5381701c663e649c5007014df324e68080701929be649c080700038e3a6f9927601ef8d37cc921a701c6ad37c9ca00701ea9be649c301701c6f537c9ca00701eb8d382f9394701eb8be529ca0a700029be4e50080601ea9c47cc93817
  | 7, 0, 9 => 0x1ea9b24e9890170003dd37c9ca01601eb8d3a131927701eb8d39cf9927701eb8d37cc562770003d71bcf99236018a9be649c080701eaf537cc8d01701eb8d37cc961a701eb8d39ef991a7014df324e7c08070003df1a69ca12601eb8d37cbcd14701eb8e4a701394701eb8d37cc8f9a701efbd37cc93947
  | 7, 0, 10 => 0x3d537c68a01601ee9be649cf8170003d537ef939460003d71a668a12601ef8d3649cf92701eb8d37cc939b701eb8d37cb5394701ebbd37cc8d14701c69be4e68a00701c72537c9ca00701ee9be649cd01701ea9b24e509017f5c69be64c53a3801eb8d37c9ca06701ef8d3649cd12701c69c07cc93807
  | 7, 0, 11 => 0x1efbd37cf5927701eb8d37cc8e9a701eb8b24e9090a701ea9d07cc9381701ef8d380f9927701eb2537cc8d01701eb8d34e98a12701ea9bf7cc939a701c69be529ca00701eb8c07c9ca0a701eab537cc9381701eb8d5a6f8d14701ee9d17cc9381701eb8dea6f8d14701c69be4e7ca00701eb8d6a6c93927
  | 7, 0, 12 => 0x1ea9bd649c901701eb8d37cc9527701ea9be649c281701ebbd8a6f9927701ea9d17cc8d01701eb1537cc8d01701eb8f0a69ca12701ea9be647cd01701ef8e47cc93a4701eb8b2629c90a701ea9bf7cc939f701eb8e2a6c8d12701eb8d3647cd12701ea9be4e98a01701eb971a6f991a701c69c97cc95a77
  | 7, 0, 13 => 0x1eb8d37c9ca05701eb8d37ca4d14701eb8e4a721927701ebbd6a6f991a701eb8be629ca0a701eb8d37c7cd1470003df1b0f992760003d71a6f4f92601eb8d37cc9727701c69be7a9cf8070003d71a6f9e9d601eb8be6498d0a701eb8e4a6f8d14701eb8d36ac8d12701eb8d37cc9388701eb8e47cc96277
  | 7, 0, 14 => 0x1c69be649d180701eb8e1bcf992770003d536ec9392601c69be649d100701ebb71c94d927701c69b24e90900701eb8d37c68b94701def537cc9380701eb8e4a72992770003d5ba6f9927601eb8e4bcf939470002a537cc9381601c69c07c9ca00701c69cc92f9394700038d4a6c9392601eb8dda6f991a7
  | 7, 0, 15 => 0x1eb8d37cc939670003d5aa6f9394601ebb717cc938a701eb971a6f9927701eb8d37cc939d701eb8ca7cc938a701ef8efc8f9927701c5f325e9c500701eb8e4a6f9e9f701eb8d37c74d14701eb8c87cc938a701ef8d380f9394701eb8d7a6f9927701eb8dca6f991a701ebc71a6f991a701eb8e5a6f99277
  | 7, 1, 0 => 0x1eb8d37cc919a701ea9be64c4d01701efbd37cc939a701ef8d37c9d214701ebbe4a6c98a7701ead537cc939f701eb8d364c4d12701eb8d37cc938470003df7a6f9394601eb8e4c2f9927701eb8eea6f9927701ea9be64b1381701eb8eaa6f9927701eb8e4a711927701ebaf1a6f9394701eb8d364b13927
  | 7, 1, 1 => 0xf5c78537cc93a3801eb8d37c9cb94701ea9b24e7c901701c69c87cc9380701ea9b24e68901701eb8d37cf4f9d701ebbd6a6f9927701eaf537c9ca01701eb8d39ef939470003d77a6f8d14601eb8dea69ca12701efbd37cc939f70003d534e509016000007bef91927501eb8eda6f9394701eb8d37c9cd147
  | 7, 1, 2 => 0x3d71a6f9727601eb8f0649c90a701e9f324e50501701eb8d8a6f991a701ea9be649c681701eb8b24e5090a701eb8d37c9ce94701eb8d37ccd91a70003df1c8f991a60003d3e6468501601c6b537cc8d0070003d71a6f9a9760003d71646890a601eb8e5a6f9394701eb8d37cb539f701eb153649c9017
  | 7, 1, 3 => 0x14df324e50080701eb8e6a6f991a701eb8d37cc9383701eb9f1a6f9927701e9f3d649c501701eb8bd649c90a701c6f537cc8d00700029be6468080601eb8d37cf539d700038eca6f9927601ef8d37cc979a701eb8e7a6f9927701ef8d37cc95a7701eb8be4e98a0a70003bd4a6f9927601c69cc7cc938e7
  | 7, 1, 4 => 0x1eb8e4a6f9727701ebcf1a6f9927701eb8d37cc969a701eb8d37cc9827701ef8d398f9394701eb8d3649d1127
  | 8, 0, 0 => 0xf5c77e4a6f99278f5c69cc7cc97a7801c6f537cc9380701eb8d382f9927700029be649c080601ef8d37cc97a770003d71a6f991a601eb8d17cc938a700038d3649c900601eb8be649cf8a701eb8d6a6f991a701ebb71a6f9927701eb8be649cd0a7f5c69cc8ef9927801eb8d394f9927701eb8d37ced9277
  | 8, 0, 1 => 0x1eb8dea6f991a701c69be649cf8070003d537cc8d0160003d77c94d92760003d537ef992760003d71a6c8d12601eb8d37cc96a7701c69be649cd00701c72537cc9380701eb8d37cc9386700038d37c9ca00601eb8d388f992770003dd37cc938160003df1a6c9392601eb8d37cc979a701eb8d37cc95a77
  | 8, 0, 2 => 0xf5c785ea6f992780003d71a6f8d14601ef8d37cc939f7f5c6f537cc9394801eb8f0a6c9392701ea9be649ca017f5c6f537cc93a6801ef8d37cc939a701eb8d3649ca127f5c6c537cc939f801ea9be649d301701eb8d398f9394701eb8d3649d31270003df1a6f9394601c69d17cc9380701c71537cc93807
  | 8, 0, 3 => 0xf5c72537cc9394801c69cc92f9927701eb8d37ac9392701eb8d37cc9385701eb8f0a6f93947f5c69be649d31a8f5c72537cc93a6801eb8be64c538a701eb8e2a6f991a701eb8d37cc8f9a701eb8d37c9d314701eb8d3a0f9927701eb8e4a6f991a7f5c715398f99278f5c69cc7cc939f801ef8d3a2f99277
  | 8, 0, 4 => 0x1eb8d37cc93a070003d537cdd92760003d5aa6f99276f5c72537cf5927801eb8d5a6f992770003d71a6f9e9f6f5c78537cc939f801eb8d37cd591a7f5c69be649cf9e8f5c78537cc939a801eb8d37cc8d177f5c7864a6f99278f5c69be649d31f801eb8e4bcf9927701ea9be7ac93817f5c69be649cd148
  | 8, 0, 5 => 0x1eb8d37cc94a7701eaf537cc9381701eb8d39ef99277f5c6f5aa6f9927801eb8d37cbd394701eb8d37cc939f70003d77a6f991a601eb8dea6c939270003d53649c901601eb8eda6f9927701eb8d37cc939a701ef8d37cc93a470003d71a6f939460003df7a6f99276f5c6f537cc97a7801ebaf1a6f99277
  | 8, 0, 6 => 0x1eb8d37c9cf947f5c72537cc939a801eb8be649d30a701eb8d37c9cd14701eb8e4a6f9394701ebbd37cf59277f5c6f537cc9627801eb8d37cc939d701eb8d5a6f939470003d71a69ca126f5c69be64bd39f801ebbd37cc9394701eb8d37cc93977f5c69be64bd39a8f5c72537cc97a7801eb8d37cc921a7
  | 8, 0, 7 => 0x1eb8d37cc8d14701eb8d37cc8d18701eb8d37cc93a3701ea9be64c53817f5c6f537cc93a4801eb8d364c53927f5c69be649cf9d801ef8d398f9927701eb8d37cf539f7f5c69be6ac939a8f5c71537cc939a8f5c69be649cf9a8f5c72537cc939f801eb8dda6f9927701eb8d37ca53947f5c76e4a6f99278
  | 8, 0, 8 => 0x1eb8d37cf591a70003d71649c90a601eb8f0a6f991a7
  | 9, 0, 0 => 0xf5c71537cc93bfae34df324e7dfd71a6f992734feb8e4a6f9927701eb8d37c9ca300f54df324e05807ae34d92724deb8d37cc97a7701eb8d37cc93b7ae34df3d649dfd71e14df324efeb8d37cc93947f5c69be649d3380f5c69be6469bd71a731f324ee03df1a6f99276
  | 10, 0, 0 => 0x3d71a6f99276
  | _, _, _ => 0
def stateW : Nat → Nat
  | 5 => 39
  | 6 => 53
  | 7 => 60
  | 8 => 60
  | 9 => 53
  | 10 => 46
  | _ => 0
def wireAt (i : Nat) : Nat := fld (dictB (i / 128) (i / 8 % 16)) 256 (i % 8)
def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids 7 0) :: stateWires n (ids >>> 7)
def S (s j : Nat) : List Nat :=
  let packed := fld (stateB s (j / 256) (j / 16 % 16)) (stateW s) (j % 16)
  stateWires (packed &&& 15) (packed >>> 4)

def dictP1B : Nat → Nat → Nat
  | 0, 0 => 0x3f3ffc3f03fff0000000000000000000000000000000000000000000000000003f03c03f003c00000000000000000000000000000000000000000000000000000f00fc03f003f0000000000000000000000000000000000000000000000000000e00c0030003c00000000000000000000000000000000000000000000000000000003c00f003f0000000000000000000000000000000000000000000000000000f3cfc0303c3f00000000000000000000000000000000000000000000000000000fffc000ffff000000000000000000000000000000000000000000000000000000003fffffff
  | 0, 1 => 0xcf3cfcc303c3f000000000000000000000000000000000000000000000000000cf3cc3fffffff000000000000000000000000000000000000000000000000000cf3cc0c303c00000000000000000000000000000000000000000000000000000c13cfcc0f3c3f000000000000000000000000000000000000000000000000000c13cfcc003c3f0000000000000000000000000000000000000000000000000003f03fc3ff03ff0000000000000000000000000000000000000000000000000000e00fc3bf03bf0000000000000000000000000000000000000000000000000003f03fc3ff03c3
  | 0, 2 => 0xe38c03b03b80000000000000000000000000000000000000000000000000003ffc7fffffc7c3000000000000000000000000000000000000000000000000003ffc7ffc7fc443000000000000000000000000000000000000000000000000003f1c73fc4fc443000000000000000000000000000000000000000000000000003f1c703fffc7ff000000000000000000000000000000000000000000000000000cf3cfcc3f3c3f0000000000000000000000000000000000000000000000000000e38fc03f383f000000000000000000000000000000000000000000000000000cf3cfcc3f3c03
  | 0, 3 => 0x3c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003fffffffffffc30000000000000000000000000000000000000000000000000000e38fc3bf3b83000000000000000000000000000000000000000000000000003fffffffffffc3000000000000000000000000000000000000000000000000003ffffc3ff0ffc0000000000000000000000000000000000000000000000000003ffffc00000000000000000000000000000000000000000000000000000000003ff0003ff00000
  | 0, 4 => 0x3c00f003f00000000000000000000000000000000000000000000000000000003c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003c
  | 0, 5 => 0xe00003b000000000000000000000000000000000000000000000000000000000038003803bbc0000000000000000000000000000000000000000000000000000038003803b80000000000000000000000000000000000000000000000000000003800000383c00000000000000000000000000000000000000000000000000000000038003bc0000000000000000000000000000000000000000000000000000000003800380000000000000000000000000000000000000000000000000003f1c73fc4fc47f000000000000000000000000000000000000000000000000003f1c73fc4fc443
  | 0, 6 => 0xe00003bf00000000000000000000000000000000000000000000000000000000e38c00000000000000000000000000000000000000000000000000000000003ffffc3ff0fffc000000000000000000000000000000000000000000000000003ffffc3ff0ffc0000000000000000000000000000000000000000000000000003ffffc3ff0ffc00000000000000000000000000000000000000000000000000000e38c03b03bbc0000000000000000000000000000000000000000000000000000e38c000000000000000000000000000000000000000000000000000000000000e0000000003c
  | 0, 7 => 0x330ffff3c0ffff00000000000000000000000000000000000000000000000000330c3033c0c3c00000000000000000000000000000000000000000000000000000e38fc3bf3bbf0000000000000000000000000000000000000000000000000000e38fc00038000000000000000000000000000000000000000000000000000000e38fc00f003f0000000000000000000000000000000000000000000000000000e38fc00000000000000000000000000000000000000000000000000000000000e00003bf03800000000000000000000000000000000000000000000000000000e003c3bf003f
  | 0, 8 => 0x33000033cf000000000000000000000000000000000000000000000000000000330c3033c0c3fc00000000000000000000000000000000000000000000000000330c3033c0c3c000000000000000000000000000000000000000000000000000330c3033c0c3fc00000000000000000000000000000000000000000000000000330c3033c0c3c000000000000000000000000000000000000000000000000000330c3033c0c3c0000000000000000000000000000000000000000000000000003ffffc3ff0ffc0000000000000000000000000000000000000000000000000003f1c73ffcfc7c3
  | 0, 9 => 0x33ec3033f0c3c000000000000000000000000000000000000000000000000000330fb033c0fbfc00000000000000000000000000000000000000000000000000300f803000f83c00000000000000000000000000000000000000000000000000330c33f3cfc3ff00000000000000000000000000000000000000000000000000330c33f000c00000000000000000000000000000000000000000000000000000330c33f3c0c3c000000000000000000000000000000000000000000000000000330c33c000000000000000000000000000000000000000000000000000000000330c3033cfc3c0
  | 0, 10 => 0x3fffffffffffc3000000000000000000000000000000000000000000000000003ffffc3ff0ffc0000000000000000000000000000000000000000000000000003f1ff3fc4ffc43000000000000000000000000000000000000000000000000003c0fc03fffffff000000000000000000000000000000000000000000000000003c0fc03c00fc000000000000000000000000000000000000000000000000000033ec3033ffc3c00000000000000000000000000000000000000000000000000033efbc33f0fbfc0000000000000000000000000000000000000000000000000033efbc33c0c3c0
  | 0, 11 => 0x3f1ff3fc4ffc7f000000000000000000000000000000000000000000000000003c0fc3fc0ffc3f000000000000000000000000000000000000000000000000003c0fc3fc00fc00000000000000000000000000000000000000000000000000003c0fc03c0ffc00000000000000000000000000000000000000000000000000003c0c003c0fc000000000000000000000000000000000000000000000000000003c00003c0f0000000000000000000000000000000000000000000000000000003c0fc03c00fc3c000000000000000000000000000000000000000000000000003c0fc03c00fc3c
  | 0, 12 => 0x3f0ff03fc0fffc000000000000000000000000000000000000000000000000003ffffc3ff0ffc0000000000000000000000000000000000000000000000000003f1ff3ffcfffc3000000000000000000000000000000000000000000000000003f0ff03fc0ffc0000000000000000000000000000000000000000000000000003cefcffc00fc00000000000000000000000000000000000000000000000000003cefcc3fb0ffbc000000000000000000000000000000000000000000000000003cefcc3c00fc00000000000000000000000000000000000000000000000000003cefc03fb0fc00
  | 0, 13 => 0x3feffc3ff0fffc000000000000000000000000000000000000000000000000003feff03ff0ffc0000000000000000000000000000000000000000000000000003f0ff3ffcfffff000000000000000000000000000000000000000000000000003f0ff3fc00fc00000000000000000000000000000000000000000000000000003f0ff3c0000000000000000000000000000000000000000000000000000000003f0ff03fcfffc0000000000000000000000000000000000000000000000000003f0c303fcfc3c0000000000000000000000000000000000000000000000000003f00003fcf0000
  | 0, 14 => 0x3ffc303fffc3c0000000000000000000000000000000000000000000000000003ffc3033c0c3c0000000000000000000000000000000000000000000000000003ff003c00f003f000000000000000000000000000000000000000000000000003ff00000000000000000000000000000000000000000000000000000000000003ff0000000003c000000000000000000000000000000000000000000000000003ffffc3ff0ffc0000000000000000000000000000000000000000000000000003ff0003fff0000000000000000000000000000000000000000000000000000003ff00000000000
  | 0, 15 => 0x3ffffffc00fc00000000000000000000000000000000000000000000000000003fffffc0000000000000000000000000000000000000000000000000000000003ffff03fc0ffc0000000000000000000000000000000000000000000000000003fffc03c00fc00
  | _, _ => 0
def dictP2B : Nat → Nat → Nat
  | 0, 0 => 0x240ed42000e2a0000000000000000000000000000000000000000000000000002402802000200000000000000000000000000000000000000000000000000000030064019003000000000000000000000000000000000000000000000000000002004401100300000000000000000000000000000000000000000000000000000300640190030000000000000000000000000000000000000000000000000000000c540000c2a00000000000000000000000000000000000000000000000000000dfdc000dfef000000000000000000000000000000000000000000000000000000003df7fddf
  | 0, 1 => 0x882c548202c2a000000000000000000000000000000000000000000000000000882003df7fddf0000000000000000000000000000000000000000000000000008820008202000000000000000000000000000000000000000000000000000000410c7440c0c2a000000000000000000000000000000000000000000000000000000c540000c2a0000000000000000000000000000000000000000000000000003703ec2db02f50000000000000000000000000000000000000000000000000003703ec2db02f50000000000000000000000000000000000000000000000000003503a824a0241
  | 0, 2 => 0x2acb282b20b3000000000000000000000000000000000000000000000000000017547b964e464300000000000000000000000000000000000000000000000000151453944e444300000000000000000000000000000000000000000000000000151453944e44430000000000000000000000000000000000000000000000000000000000d300d5000000000000000000000000000000000000000000000000000cb2c74c3d2c3a000000000000000000000000000000000000000000000000000cb2c74c3d2c3a000000000000000000000000000000000000000000000000000c92430c2c2402
  | 0, 3 => 0x2084409108bc0000000000000000000000000000000000000000000000000000208440000020000000000000000000000000000000000000000000000000003fdf7bbf6ef743000000000000000000000000000000000000000000000000003fdf7bbf6ef743000000000000000000000000000000000000000000000000002bdb3aab6ab341000000000000000000000000000000000000000000000000002acb282b20b300000000000000000000000000000000000000000000000000002acb2802000200000000000000000000000000000000000000000000000000002ac2002b202000
  | 0, 4 => 0x1534d7d4df4cff000000000000000000000000000000000000000000000000001534d7c0080020000000000000000000000000000000000000000000000000001534d394ce4ccf0000000000000000000000000000000000000000000000000015300214df0010000000000000000000000000000000000000000000000000001504d194c64ccf000000000000000000000000000000000000000000000000001424c554954cbe000000000000000000000000000000000000000000000000001424c554044c2a00000000000000000000000000000000000000000000000000112494d0d348fd
  | 0, 5 => 0x2ae2002bb12010000000000000000000000000000000000000000000000000002aebac6bb1bbbc000000000000000000000000000000000000000000000000002acba82ba0bb8c0000000000000000000000000000000000000000000000000028ab8469b1b9bc000000000000000000000000000000000000000000000000002269ac63919bbc0000000000000000000000000000000000000000000000000022692823919394000000000000000000000000000000000000000000000000001534d7d4df4cff000000000000000000000000000000000000000000000000001514d394ce4ccf
  | 0, 6 => 0x3ff2023fff2010000000000000000000000000000000000000000000000000003feffdd6c64eef000000000000000000000000000000000000000000000000002aebac6bb1bbbc000000000000000000000000000000000000000000000000002aebac6b20b320000000000000000000000000000000000000000000000000002aeb282bb1b310000000000000000000000000000000000000000000000000002aebac6bb1bbbc000000000000000000000000000000000000000000000000002aebac42000220000000000000000000000000000000000000000000000000002ae284429108bc
  | 0, 7 => 0x334dfdf3c2dfef00000000000000000000000000000000000000000000000000334d38b3c2d3c5000000000000000000000000000000000000000000000000003fffffffffffff000000000000000000000000000000000000000000000000003fffffff2cff2a000000000000000000000000000000000000000000000000003fffffd6df4eff000000000000000000000000000000000000000000000000003fffffc2080220000000000000000000000000000000000000000000000000003fff3abffff3d5000000000000000000000000000000000000000000000000003ff6d7ffff6cff
  | 0, 8 => 0x37700237df001000000000000000000000000000000000000000000000000000376dfdf7d7dfff00000000000000000000000000000000000000000000000000376dfdf7c6dfef00000000000000000000000000000000000000000000000000336dbcf3d3dbfd00000000000000000000000000000000000000000000000000336dbcf3c2d3e500000000000000000000000000000000000000000000000000336d38b3d3d3d5000000000000000000000000000000000000000000000000003bcf38bbe2f3c500000000000000000000000000000000000000000000000000375d7bb7ced7c7
  | 0, 9 => 0x3bef38bbf3f3d5000000000000000000000000000000000000000000000000003befbcfbf3fbfd0000000000000000000000000000000000000000000000000039af94f9f3f9fd00000000000000000000000000000000000000000000000000377dfff7dfdfff00000000000000000000000000000000000000000000000000377dfff70cdf2a00000000000000000000000000000000000000000000000000377dfff3cad3e500000000000000000000000000000000000000000000000000377dffc208022000000000000000000000000000000000000000000000000000377d3ab7dfd3d5
  | 0, 10 => 0x3fdffbbf6eff4b000000000000000000000000000000000000000000000000003ecfe93f24ff0a000000000000000000000000000000000000000000000000003d9fd3bd6efd4b000000000000000000000000000000000000000000000000003c8fc13df7fddf000000000000000000000000000000000000000000000000003c8fc13d24fd0a000000000000000000000000000000000000000000000000003fff3abffff3d5000000000000000000000000000000000000000000000000003befbcfbf3fbfd000000000000000000000000000000000000000000000000003befbcf3c2d3e5
  | 0, 11 => 0x3dbfd7fdfffdff000000000000000000000000000000000000000000000000003dbfd7fdfffdff000000000000000000000000000000000000000000000000003dbfd7fd2cfd2a000000000000000000000000000000000000000000000000003dbfc33dfffd1a000000000000000000000000000000000000000000000000003dbf12bdfff1d5000000000000000000000000000000000000000000000000003db2023dff2010000000000000000000000000000000000000000000000000003dafd5fdf7fdff000000000000000000000000000000000000000000000000003cafc57db5fdbe
  | 0, 12 => 0x3feffdfff7ffff000000000000000000000000000000000000000000000000003fcff9bfe6ffcf000000000000000000000000000000000000000000000000003fdffbbfeeffcf000000000000000000000000000000000000000000000000003fcff9bfe6ffcf000000000000000000000000000000000000000000000000003fffffff2cff2a000000000000000000000000000000000000000000000000003eefed7fb5ffbe000000000000000000000000000000000000000000000000003eefed7f24ff2a000000000000000000000000000000000000000000000000003eefc13fb5fd1a
  | 0, 13 => 0x3feffdfff7ffff000000000000000000000000000000000000000000000000003feff9bff7ffdf000000000000000000000000000000000000000000000000003fffffffffffff000000000000000000000000000000000000000000000000003fffffff2cff2a000000000000000000000000000000000000000000000000003fffffc2080220000000000000000000000000000000000000000000000000003ffffbbfffffdf000000000000000000000000000000000000000000000000003fff3abffff3d5000000000000000000000000000000000000000000000000003ff2023fff2010
  | 0, 14 => 0x3fff3abffff3d5000000000000000000000000000000000000000000000000003fff3ab3cad3c5000000000000000000000000000000000000000000000000003ff6d7d6df4cff000000000000000000000000000000000000000000000000003ff6d396ce4ccf000000000000000000000000000000000000000000000000003ff286429908bc000000000000000000000000000000000000000000000000003ffb2a2b28b300000000000000000000000000000000000000000000000000003ff2023fff2010000000000000000000000000000000000000000000000000003ff20202080000
  | 0, 15 => 0x3fffffff2cff2a000000000000000000000000000000000000000000000000003fffffc2080220000000000000000000000000000000000000000000000000003ffffbbfeeffcf000000000000000000000000000000000000000000000000003fffc33f2cfd0a
  | _, _ => 0
def p1At (i : Nat) : Nat := fld (dictP1B (i / 128) (i / 8 % 16)) 256 (i % 8)
def p2At (i : Nat) : Nat := fld (dictP2B (i / 128) (i / 8 % 16)) 256 (i % 8)
def wireDAt (i : Nat) : Nat × Nat × Nat :=
  if i < 124 then (wireAt i, p1At i, p2At i) else (0, 0, 0)
def wireDOK (i : Nat) : Bool :=
  (p1At i == projBit r1sG (wireAt i)) && (p2At i == projBit r2sG (wireAt i))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem wireD_ok_all : span wireDOK 124 0 = true := by decide +kernel
theorem projBit_zero (rs : List Nat) : projBit rs 0 = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [projBit, List.foldr_cons, Nat.zero_testBit, Bool.false_eq_true, ite_false] at ih ⊢; rw [ih]; rfl
theorem wireDAt_eq (i : Nat) :
    wireDAt i = (let w := if i < 124 then wireAt i else 0; (w, projBit r1sG w, projBit r2sG w)) := by
  unfold wireDAt
  split
  · next hi =>
    have h := span_ok wireD_ok_all i (Nat.zero_le i) (by omega)
    simp only [wireDOK, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2]
  · simp [projBit_zero]
def wireSAt (i : Nat) : Nat := if i < 124 then wireAt i else 0
def stateWiresD : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, ids => wireDAt (fld ids 7 0) :: stateWiresD n (ids >>> 7)
def stateWiresS : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireSAt (fld ids 7 0) :: stateWiresS n (ids >>> 7)
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
def idxH (s h : Nat) : Nat := bsr (htAt s) h 10 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def CN : Nat → Nat
  | 5 => 12
  | 6 => 444
  | 7 => 1615
  | 8 => 467
  | 9 => 12
  | _ => 0
def CH : Nat → Nat → Nat
  | 5, 0 => 0xd50e1c75b57cc11aab454227a635ef778c7f6ed181b42a4b7f583dfa5e2d8aab49e72c9642b779a30d228ab30b01f523
  | 6, 0 => 0x15a322c015260be214b3d7de138cd63712f8fd59125dee4811fd39c0119dfe10118e7374106d4705104283190fe749af0fde460f0fa22a3f0f8898390f5a3b3b0f415ad90f2f0b0d0eb903040e7e15130e3f25de0e28db320e15721d0e0a8d390de788260daabbb60cd40f4c0cabde0a0c8981740c4a462b0c0630490bd5dce90b8e1f2b0b0acdf70ab3b82d09e76cd909b7c852096e9438095e497f09209d2309115a4608d3e389088f3001080764f207d6fdfe07962ead064ae448058adacd0505ca7204773d4504360c7703a107f2031f015502a7935102953104017c2aac017648a5013f67a60116dc7e00f84fe700e3021600bbc06900a9e32300862c61
  | 6, 1 => 0x2a8022532a47f4e42a2ac81c29f117742948b054292f8a3b2909654c28abb43f28a4a83e28703eee28693b4327fa285b2794cf0a2713cf0026d3ff3726c09f492697790e2625fbd4259c3dab257a8a91255713b32516813c24997c0723e3e51a23d1706322ed2e1722c4e84a2216623b21cf268720f4b6342036b16120292edb201787bc1fccc3341fc65dff1f7973ec1f6ad58b1ec21db31e881ec81e534ff81dc96b4f1be563841baefe391b932b621adf1ef61ad2d1f51a888b681a585ef41a3cec081a0f2ada19d5fa50198c51fb197c445219429b4719146ee01905f79c18d42f2c18a819b2186c388117f02ecc16ec765a16eb0e041673385e15dcfbc2
  | 6, 2 => 0x44171c5a438d39b242c814bf42b779a3427c1aec4243f1c942227f7c41e2448a41cc51263fd62b0b3f8bbd3f3f7141a53f2952a13e60b6cc3df59e8a3d513e8d3d303da33c90e5203c7b85e53c62cb853c21f90f3bfe0f263b723e203ac40ac7392df15a39241b633909d1e538efb48937b9f30e37809ff0376135eb371f64bd36d44ad33681559c3660102c36370022357914e534b7a1463483875034720705346502b534639f9f33b438b6339e64ea332d048932e5408e32b0b299327189f53257a9653202a4623037bc2b2f98de682f732a3a2f6848b42f62b4552e6465742c41a44e2c151fca2be61f7b2bdaef432b81626d2b44f41a2b1414b12ad3c302
  | 6, 3 => 0x62d5987362501bbd61868c926118463c60f6fc0860a194d3609dc991606bbcf75fb4c6925f1113255e3026f45e2f68925d26770c5b599cb35b2a96f85aa8a6b95a5437a0596304d65925466958a8d875587acba5582bf5fa57f5134d5798592e5724b262567bf90a56488c3a55262b1954b1935f54aa5a8a544e9a7452daacc152715fc651f0649051c3d9c051bcbf8e514552f8510100775070db8b4f1bb8244e8b95e04e3b612d4ddb76074d035fd24c6448994c447a174c30865f4be8975b4ab737524aae3b9e4a899ff94a3975f34a2c3dc048e5994d48dfbb6f485b4b0148558c39474ea9b0472315b44675c8f945eca59f45ce0d5944debf4444540250
  | 6, 4 => 0x7fb22b547f78bc997f0741177e2b6dd97d37c1197c5cfe467c50c69b7bf841387aaf2d897a9854157a9059ab7a7d53047a2af07b79e1b8a679e15a287830ad7a77f0430977efa4c177d021bc77ba444e77377e1475b2778375413da674c2ba8f74484f2e743d2db173ddc31473b05cba732cd8d9730c7bc7727718da7267536d7263ed847258a0d5722eeeb671c6cf517128a55d70f028e070aa5d93705b5d9f6fe7d5c56fa542716f38fc7e6ecfff346ec2382d6e7107f36e5d2e3b6bcf90f36b43cd8a6a74145f6a195e2c6994faf968e89b85689e6745682121e2658b5d0d654b05bf653a105f641f9ee9641b2f9563f5006b63ebcd73631faa3a63128d16
  | 6, 5 => 0xa3600842a26cae21a25e4bf1a194c2cba0c89d3ca0b7e878a05b39a29f9291c59ebc2a2d9e9e89fe9e1b11719df726d99de751349d1960ac9b7186cd989a6927985e9e28980948ae97d04e5497ac0d109771e88f96ce6dfd96911e4996424b4196066259951a1d2594f097dd94d2bf9d94ab739f94836f6d93b30e8292c480a29104b3f3907b4dcd8fd4a8f68c243bc08b6e47048ad7cec68ac412cc8a81f0ca8a7e13518a618f158a39a5c389b2bdc18892411787345c3f8643ceda861954578612750f85e097ab85aeb8ef85497f0a84b6983b8421f27883fd0fd48340c9be8335bae0831d6c2c82d1fec0828c2ecf8257272981f0b5648110aa54808f945b
  | 6, 6 => 0xfd4ecf59fac52187f86e66d5f5e663caf4591915f3175066ecb47af8ec164c1ee8d9024ce2f6af66df7ea6b7dee74686dae11edcd7b130c7d78fc00fd62597bad539c1bed38ed5b1d2a0aeedd08f8647cdd710f1cd786ec8cafa56c2c9ae378fc8bcd3fdc6e183cfc6ce6bb3c67def90c5b7867ec35a3d98c109d3aac01c213cbe8cb8c5b9770643b5a27b4bb46bdf36b39a081ab36d65c4b3088cf5b239bc2cb1aef324b143dc6fb0b01378afcaef98ae3e6a51adb11268aa7416c3aa63c7b4a99c2534a8e83cbfa8531185a7e5106ea7c9ee2ba7a477d1a6a7ba4ca4e838f8a4e3c223a4596378a3d584c7a3a9d24f
  | 7, 0 => 0x4df8b0c04c9880c049f4c59049d41a404941f6a048faf4c048ad07d0479bbe104673f1304427d3b042b899703d4cc4103a624c70384d1180357f0400355cd58033a727c0318307a030a418d02c1685702b2728d02b14efe0294122e028de01e0246bcc0023f5c5b023e29650213d651020cdeec01cde88101c90a2501bed05901abdea4019fd767019f361a0195ffdc0191869801794b5f0165a78a01652a32015fcb3e015a7e8d01551783014ecf68014268c7011c51870114ca86011182d800f9b8fb00f76a5900ea3c8100ea38dd00da586b00bd561a00b9120700b6512f009614c30082d9db007dbb7a0031a7ea002e9cb3002d875e00184b5e0014cd4c
  | 7, 1 => 0xab8b2690aad79ad0a9628be09ee1b6f09d9969709d1727609c0e32809bd51ef0989c7c309723fd90945c8c3093e735608e87c7c08df973908d0d2ed08c7c03908c5dc3f08b46af108664b500865d84f0844bf830829c345081c74db0804e8ba07fab1ba07f70b8707ed8a3207ca96c507c20e2707962ead078179cf07489433073d42b70725e9590711d49e0709752007073daf0700d46406fb5c5206ce230906b5fac606ab2bd9068bc39d0684017d0681af190651b5d5064cb8090644c92306291d83060f596e060e01a405f2790c05e9221005c61dd605bb49a605ad2f340590ddec057729b60550fa010535f29d05169eb00509fa1f04fe0c3a04e553f8
  | 7, 2 => 0xf2c4f190f1c66040f16fff20f0494aa0eef2d5f0ee2d2210ee0de320ed7a1e90ed019dd0ecc23a60ebee7890e974d5b0e90cf7c0e7e15130e7db3450e67dc250e4f8ba70e1f55bb0e1f184a0e05ccb20de1cc4b0db9c7830da91e400da145ba0d9cbe430d8ede180d5a81df0d570f570d49c4170d4430e80d42bf170d40e0e10d3586890ce9ab6b0cd896110cd412060cc9d2110c97cf590c969c940c8aad3c0c867e660c825c970c7d9f2b0c6f23470c6d8e9c0c232aad0c22507d0c0bf6ea0bc47b370b8a0d5e0b7f14bf0b65ede90b53d07a0b41c7720b2c8ce60b2912830b258c830b25135a0b2179b20b1e949f0b067d740ae653d70acf09dd0abce842
  | 7, 3 => 0x1547871e15423b41150cfd8114e907ff14e6b4ae14db2920149c907c1499cfe514466a841421b37a13fe949713e1552d13e0e2a713c8e2b213c146b613ab1ac3138cad0013346ed1132f4ac71320e8dc1317dd2b12ddb43412bb814412b46cf312a8595d127638531265ef971247bf781233466a122fe1a912245a68122261f8121b11231216ddca12140faf120d1dd3120061e011c1f92a11b9e05611894c1a1187183a11804b36117804a4116c6f821161181a115e10321156a952114518c711408e9a110f8d8e10d95ce110a80043109bbfbb10705cfe1019bd290fe6d3690fc7e3a30fb1a7760f9aa5fd0f808c130f77871a0f622c520f53334a0f48aa66
  | 7, 4 => 0x1ac6cf551a9c7f661a9329761a6a04de1a63a0ea1a4dc7a41a33b1c31a04d97919ff9c8019fd5caf19fc1ed919f487eb19f37e0719c7c79119c5957e198916cb196672e119468cb719389a7718f302eb18e3fb0a18c40ebb188349881882b169183afea718261f78182361ff17e4d13d17d64a9117b7e34f17a3f1f5179c6b23178973c3178953db1781fd24175a929b173e6e341729918f171f64aa1708743b16e96cfa16d77b9d16d21d8816c91dcd16bcc03716b50ee916b01e541695814b168bc85d1661bbe9164f38e0164042a216357735162d41ba16279856161648bc160c7aef16066cd915e9498b15cb6ef015af65f1158c470e15863d83155ed0bb
  | 7, 5 => 0x209d2b87208f5f632064873a2063e54f20292edb1fecb1011fd3c25f1fb72b911fa939b01fa565611fa23c8a1f3e5d811f05df5c1ed55caf1ea663541ea4ddda1e961c6a1e95def71e7359ed1e5c09241e2d04af1e184c7d1deba4451de355b91dad67911d98a19b1d948ff71d85da9b1d83b5c31d7de1f81d7215931d1165dd1d07cbc61d06d2eb1cfd2fc91cf34cfd1ccf54311ca81a3a1ca481c01c8e80241c8bee751c84fb571c8349911c5d76581c397d011c25bd721c1ffead1bbaa2fd1ba714161b933b9e1b8548e61b7eaebf1b78d4bc1b61a0cd1b6003b71b55df541b52f3321b3fed3d1b25c5621b1c36fd1afecaa01af371971ac819931ac6e6c7
  | 7, 6 => 0x27c009a427a5bdfb27795cd1275d28bc2750b4f62713cf002710b40c26eeeb7b26beaf6f26bb2fef26b4fa7626ad119126ac92fa26786863266407622639a0bd26110117260a164f260932412602a34725f8185a25d992dc259fb2c9258a6ea42588220825611dd02533899e24f9d1c424bf6a3624b5fa3e2467ee6a243971d5241d33132416c07e24123a1f23f513e823d0e82e237feffe236d9b64233e51982335ab5622d85c9a22d2ddb122c96b3022c4f10a229030a42289ec0b226df44b225e9c11223c385a223380ee21eaa96f21e6cbde21ce372521a5f968219016092177d4282145e849213dff8120fb7ea420f42dff20df43cc20d5617920b18a1e
  | 7, 7 => 0x2d1e3c9c2d19df392d076f792ceeda7a2ce139a22cdf3e6c2cbf60152cbb9f1f2cb7e2692c86b1b52c7afb6d2c58dac22c565d622c536d5d2c4f91e52c42325c2c2937292c22b7412c18d8712c14318a2bc573ef2baf6f8f2badab652ba065fa2b96fbd22b87620c2b81626d2b19bbf42afd8c522af8e8dd2ac54d632aa00b9d2a9cb57b2a8c3c9c2a8999b02a8811fe2a5617002a2ab54a2a245e7b2a1fc85a29f0b1cd29ed6e3b29e942c429ce843e2993998d2989cbc029874d1e2980ce6629428e4b29342757291d2a9e28e5022c28e3ecc328d1b8ee28c93b9c28c73e9828b96dc828b7d39928a4a83e28a101cd286658d0285879f12857f16a284514cc
  | 7, 8 => 0x339be830337bedf033511330334e11ad3330c746332a82ad330bca3f330a8e35330961a632f11b9a32d045d132ba82ac32a9a19b32a1bcd5326bf53f3264f1943228b4233228114a3210954331ffed8331c615273198218b3159aba13157bf6e3130272031242ee93122199e30dba21430d9fb7930d5282030959bfe308c42f8303f34b830377c1a302ca777301b2a853016b5f93014f875301052cd2ffb65112fbdf3d12fbbf89b2f62b4552f3594f12f2d39052f1d2f5b2f1abea52efbd9642ecaebe82ec68d272e8e6a142e3b996a2de6358a2dcd71e42dcb18752dac07892da94f942d90db782d70ced82d52d1502d4518622d43d71c2d3e70562d2f16c6
  | 7, 9 => 0x39775201396f572d3956e3ad394f1420390ed69f38f4c7e038ed825b38e1a69e38c6876638bbb164389cbe363884b8a9387c22163864fc31382f747e382eb67e381fcf143819d23937d8e1ca37a858aa37a4666c3791ff6b378398053743a61d371a462236d88c8636cd76be36b521a236b066473678c0eb3669c03b366946d0366487033652e1123652c142364691d8363e94ef35fe022a35f834e935f2a55735e7486435d89aaa359f67e7358d94f1358833f835771853356512d0355e29643541768b3531b47734fa962534f524f934ecd7be34d9f43b34d2fbb734b7456634718ef03466ebee3456261334487e1234064f6c33df688433da662c33a2828e
  | 7, 10 => 0x406f21e940616ebb4041a8df403af74d4028922d401a1c4f3fe000373fd72a663fb101cf3fa66a2d3f8398af3f69bd633f49d8473f4622693f3143b83f1e2b9c3f15457d3ee052543e79bb8a3e791ea93e5766453e444aad3e3a3ac43e38dfb93e277fff3de1cf0e3d9b691e3d946b583d8a3cae3d6d79af3d2999453d10cdeb3d0e52963d049def3cfaa5163ce437ac3cd396533cbde0b03c7d7cf23c407f353c3ab5c83c35f2033c21b4153bf167e33bed01ee3bcc8c933bc8e96e3bc2c63b3bbe60cd3b8aa58d3b7fb1233b5dab7f3b4d023c3b4891dc3b40a23f3b05d6f73ae826bb3a8e04dd3a8512d93a64e63a3a48a48639fa66b039ddbebc39a3264a
  | 7, 11 => 0x4755b8444727debc471718c446df279b46dd85d846c9322546b88460469949b54687df064667f2b74626019545f9c57745abfc7845a2cc4a459774c2457e7d5744ecccfe44cd758b4493ef314490ec0c445a478f4458f2e54418c5644417aa9f440fd5ef4408d56744032d5043f5039043eb0c0643db6ae443d6f05343c469ce43ab146a439b611c4397d140439406ca43686f9d43555fb0434bdc18433cb82e432dfd8243110caa4305883642e7b5af42b779a3428a98aa42824baf42759974425ac010424d728e42454fb9424083084214fad141e3271541b7ba044183d887417fec1d416de72c415fc25e414a8c1f41320659412c1b3840d32ec340bbc127
  | 7, 12 => 0x4f0494734ed5e3f64ea817a54ea26bcf4e9a87094e757aba4e3b68614e18a5394e1717654df560734df05b3d4dc9c7c04db0fe984dace24a4d7dd0274d2ff4d14cf5a2254cec75af4ce11a174cc34f264ca1aa074c8a818c4c7463374c58a4c04c46545e4c43d6c54c3ec3374c29021d4c173de94bddb78f4b8c97694b6978864b5e75fd4b50406a4b2478044b2472944aee73794ac7dfcf4aab57be4a9730f94a932f4e4a8291714a77d2104a57ba7f4a25f4994a1660524a0a039049f3d2f349e125c649c3e2a949bc923c4987e828497253c149148db0490584c948ae22b54824b16847f536de47f2bd0447dc65b847b76ea347a0deee47703dcb476a5be9
  | 7, 13 => 0x57d21cf857b421825795fc8d578d26c0574f4bb2574ab38e574874375727b7f4571462ac5707fb6756c5d00a568d8c7e567ee6cd56403068562fa21b5618ad15559d3a72552e1ac455067f9c54fdc76d54e2c70654de0ffe54d4e82754b47b9854af2ec554acafc454a96c0954a268625476a805544bdb3153ca920853b2be725395ea5853812058537c0e45535634b6533cb2ca531108d652f7ac6e52ce9ec2525903715253af2952534f94523dc21151ed228251e9127651954e1e5139dea750dc89c550b00f9a509f5416509e2120508e1ebc507207e45069bcbd500139404fff2dd54fcc8ff24fa260824f99f6424f8c57c24f4a343c4f46dbe14f0d6f11
  | 7, 14 => 0x5e10c3f05dfe16575de083ce5dd08b735dcdee225db99de25db7bfac5d8c46d45d8bf1475d87fd325d8030b75d5fdc975d53729c5d48a8d45d1e66bc5d0eae245cde0cce5cbdab195cb746015ca6fca85c97debb5c91de815c7a05f25c79bb025c5fae8d5c5858275c3b8dfc5c33c1815bf13ab45bb2ead45b8c3f8e5b7d5c3f5b4dbe2c5b3409c15b26580e5ae1ffbf5ac69a115ac679ad5aadae925aa8a6b95aa52f8d5a97a4eb5a8322685a5dfd7e5a252e6659fcbebe59f375e159efad2e59ed3d0e59d5a23b59c84b7059a0c2fc59952f0b59907843597bfa8958d7b5fd58b5610058a9df505875705b58737aaa5817addf5810d46d580ad4f357e9dfe2
  | 7, 15 => 0x66e5ae6b66b2ba9b669e5573667f2e9a66730cef66314d2e6625b9e96617db0a660f2a8666078f2065542827653315e46532bf64650aa1d364df0e0764b153c164789948646b28aa643ac406641ca4e7641b71f164179578640e6da163e6353e63e50b4763939f336332600f632bad9e6320cbf7631fb15362fa02de62dfa08f62c7850d62735d4f62623a35624d6d5b61a45f8b61381f9760e8d6d560afae3b60ad45a2606f06466069010360687f66604693fd60409ff76008d5905fbac6fd5fa8e5035f942b505f6251ca5f6139d15f4d79415f4569945f411ea25f26c7b65ef492105ecd913b5ec2fe405eb986e35e7cab7d5e56e6485e5492d85e394d3c
  | 7, 16 => 0x6dcc76296db3cd8b6dab2ce86d7e78d66d4717016d055eef6ceccbe26cd455236ccc398e6c96b4706c8c37936c64553c6c4b6e046c41d5016c2229556be5d2566bd6e2826bd20d4e6bcf90f36bcb63fb6bba30316bba04806ba0f1c86b91dda16b67104f6b50c44f6b3934176b3457826ae5c9b86abcdfc56ababa2c6a91b37d6a4320db6a258de66a13aebb6a08291469da0c1f69b86ac26969e1b669218327691a8b4368c89a3568a77400689e674568959ecc688d1b55682efe61682ec21a68201ef168090f896805cfb767eb4a3067be1d3b67b7d8a267a2b2bd6796379167891a306786b847677d84d8677213ae672edba16724067666fc748866fb4c91
  | 7, 17 => 0x76b57f7c76b41f6f768129007668611b764e5f617613d46a7605ae2176046f6075f8f90e7554e386755160847544c0b17539d2697523065074ae2b347485a1e9746a0e0a744e9df37447c6f97425a9647419ba3e73f993ba73e9209c73bcfd3f73a4887973938159736647aa734eaa0d73437dc2734049fb7309ea2f72739f5472464c2171d3d74b71c52b6a719e52c1718d4b85718aa31d7180f687717f4ee0716be577711820f570f943ac70e81d7570d5611b70bb677e70607efa705b5d9f70383375701d07ab70120e997005f1236fe18fc46fa5e0046f897d916f831bc76f13e0ff6ee8713b6ecfcc7c6ec911ee6eaec77d6ea3e37a6e80d99b6e16b7eb
  | 7, 18 => 0x7f4af1e47f2587b17f0df4cc7f01445f7eeb3f2f7edbceae7ea020fc7e1a8a567e0951f67dfb85ac7df4a2987dd765af7dc60fd37dc3639f7dbf1e687db173387cea112d7ce4b2627ca8786f7c69c65e7c4bfba17c4260817c1abb197c0dda9d7bf841387bd0c6937b9474917b8f3da37b665f577b4332737b1b71df7b16ea687ae6a9707aaf2d897aa157477a46e9767a260a2f7a00aa8b79d3e13a79c02f72796fc1e179684f6278bb1eaa78a6665978925775785250aa7819d3857812897277a217b1778509c2777652a77763860f7746c8397744f9e7773f55317731b80f7724cfaa77231e6a771f39f876fdbb7a76fcecf676f0de3376f096c376df94a6
  | 7, 19 => 0x8afbf1a48ae257588adfa09e8aaf207c8aa701598aa3b04f8a81f0ca8a6f268c8a4b888989efee9189b52b508983c187895f8fa988f823fd88f300e188ede02888e50a94881f30c0881af38987fc390c87ec230287e088dd87de9c8a87ba84e887b2ceb4872d942987077a6d86e4b06486b63847867726a1865e272f865ca3e4861a00e985d25c7484c93e8b845d1c6684594c5e8450d9fa844c64498422cac983c7f1fb838f94ca83804071833df90382fee33982a1ab69828511a4826e4ef28267361782585f948245e572821853fe81e538fd818c8a2480bec1e180b3c2048092095080822666807ddea7806266ad8034d29c8032d7667f75ea277f632327
  | 7, 20 => 0x9ae5da449a7a06c29a6ab1be9a6914bc9a1f18269a07492d994b9d089944066398ff0c1898468f5c97a00225979c56d897708ba5976add7d960d324a95ddc41b95d4c56f95a7bcd39551aacc94d38517949f308d947fb43293f91dd793c2bae393b396f99301777592bdfe3b92bb0e5892aa9916921c84c1921c7d4491ed9b59919a80f89190d39c9151006c91503a3090f610e690868a319066fa269049058a9012847290061e318fe490d68fb5d0938fa972eb8f9d1d5f8f80fc978f4062dd8ee425888ee20b498e9ca8a18e7679718dbe23998da9d0028d5a65f78d3157b68cd766ed8caed4eb8c76140e8c66e23c8bc68b508b9764df8b1fd6d78b080e6a
  | 7, 21 => 0xaa9c0d31aa8df529a9f3d131a9ebdc13a9e97bd2a9accd36a89398e1a881b3bea828f69ba7fbc882a7966e15a78745f7a78014d6a6aeac0ca69d5214a65c3616a61bfe94a52c7e6ba5268c5fa4ef705ca4e3c223a4c4fe3ba4b188daa40177f8a3f2435da3eb5964a3ad5187a34c1558a34731dba3098384a2cfe23ca2a97873a29245d0a265fcc7a26534afa1f783b5a1d7c0d5a0c59c23a099d7c29ff394c19fce48649f7298a79f4bf0ab9f3c616f9f281e6a9f1c706f9f0c76639eba82119e5f4b7a9e56566f9e519fea9e418da49e1860da9db823729daae7359da9d51f9cf14cd49cd7cbd59c8160609c5a86729c354d039bccaadf9bb583f29b34b121
  | 7, 22 => 0xba558546ba231cbbb9c9cb8ab94719e8b8f9e3e0b7ef6c85b79ef288b793d28db6f964b2b69b6c10b691c424b66f714eb666254db5bed785b55f3ecfb4c180c1b4b7aa29b4abe74eb4309820b42863c4b3c505beb3bf8a8eb391ac48b37c045eb370e1a9b325de37b2ce525eb272d876b2118fd6b1ff7463b17989ffb0e1dcffb0dfdfceb0a47233b04d71d7b02f596cb0231954afd5f4c9afcd53fcafc500beaf76925faf75ff26af0e842aaf0c12d5aee7287daebe772fae87a2bbae1bf85dae064aa9adf352c3ade4afffadd6bb62ad9c65faad9683faad783fe6ad58a5d0ad25830eac41cfbeabd053b4ab8bcb77ab3d78dcab227451aac9e59baaa935da
  | 7, 23 => 0xcf33b5c0cf01a125ce81f3a6cdf98342cde202f0cbb8063dcb51ce3acaca82d9caaee697ca5d1f3fc8d8951dc7ed3172c7ec7312c7ea0248c7bda704c7b633fcc7a207a9c73369bbc731841fc6bc9380c63e6ab8c5ff83fec5736c6ac5307439c416706bc3e98555c3d681efc3c26a3dc3ad2618c38e86d8c35f24b6c31b6fd9c310f424c2bcb42dc23c0a35c23b26dcc1f4f1c7c1eeb825c19d30e4c17173dcc11b9ec3c1041042c0d8bcdac088ed64bfe7e809bfda4f41bfcadb5cbf25a648befa2055bec0a575beb33ceebe9af3a5bd8be129bd41015bbd376e02bd1c3529bcc91ac8bc545819bc2c003fbc1a5d6dbc19ed6dbc042ef7bbe34f76bb5ca883
  | 7, 24 => 0xee6d5a1cee02495bedfa1c5eed56b179ed302685ecbba0bdecb47af8ec8449e5eafba6c3ea39f55de9f83c15e86b6e21e7c700b7e73f702ce7283c3de6d0b57ee69515eae5cb74e9e5499e93e2f6af66e2835ba7e232c2d0e21681bae152e27ee1283faae1151f08e02ccb21df204264dede789bde622395ddf8e307ddb7dd18db8afdaddb8893fbdb3a67f6db29855cdaa10b17da62d3c3da4ab022da3ac1add96359b3d84ccd00d803eed7d7e2f6add7a472f4d68b73c0d5b2f80dd5ab9fc9d568b144d53d3f77d491135cd47b26a0d445852fd4067395d4001a12d317dc6dd26e2c13d1d6acffd1537ebad13a9d20d0188098d00c244bcfaaeb5dcfa1a4c1
  | 7, 25 => 0xffcceadcff6dda91fe63576bfdd6902af9b835b8f8e8bc33f808cdccf5ab4c3ff4d74db7f3eac703f1c51099f0cb655ef0a96dc2f053c1fdef3160dc
  | 8, 0 => 0x14e6b4ae141a4f1c1413d608135211a2131bfefa1317dd2b12b8ab4112b8884a129997eb12798028124e26351232479711d748061142fa411134c9341004221f0fc22fb60f60b9f30f3badb20e8414b20e783ebe0e589c450d9cbe430d61f2fb0d52c9a60d4d98860cea20e10cc7aa850c867e660c167f100bb2ffb10b41c7720ab7b9ae0aa9dacf09ee1b6f09eba6f408aedd46089ab0f30878675807bd347d07af559e075140fd06ecbabd06b07a0305c61dd605ad2f34058ce34a05869eb105169eb004d0acec03e36454036df1500360127102d5abde0296f5790291d00a01bed0590129b75501283a170086a50c006499150027347900103def0008238d
  | 8, 1 => 0x2882e2b2284db2db2774c460272770732705880d26d2458e26aa53c326396ad4262d41fb25bece64258a6ea424cb7b2924a7e76c2438a2592429651523fe6fae23afce9222ea3ac022daf26b225c73322236825921f6124621a5f96821698b1520df43cc20d196be2081cc61204aaf2d203e530f203cd04e1fd3d3851f3d31db1ee472391ebb13731eb3facb1e739d441e7359ed1e17d8601e08e1531c1ffead1bea35011bde45011b78d4bc1b70b1901b61a0cd1a45ab1d1a2bfa9c1a0ece7019e3604919deb3e219b1d448196672e1191531f41900f42918e3fb0a183e830517d7cb9517d07b001729918f16e8db1816b50ee915f86a8015f022ce1561a43a
  | 8, 2 => 0x3c3d49423c39fd5e3bc2d8a43b76a7473b23954e3b0787993acd3e823a8b1a653a861c993a4766343a305add39de879e396f572d3950034038ad846e37dd7e80378f31e836e4026d36c744ae36b6da923678c0eb36778df536224d1b35d89aaa358e7c13357bcd573555b6173528ce783523a1113518dab134cf795334746a9f34064f6c33d93c6b33ab0d08330961a632e7627a329cbbfb3294bf403264f1943150ae1431381b073129ad3f3055c0a6302ca777302a0a262fc976f62fbf18df2f7655c82efbd9642eedfa852ee51d392d6df75a2d014b912cf3c0ef2c9946a22c1543872ba0a43a2b48380c2a6cf0712a5175e429e942c42964176b291abe56
  | 8, 3 => 0x596bf2065923c1c6582e787856dbe56f567ee6cd5640306856240dff55bb43f755ab6c4653b7a8b5531915d152e996fb52de426a528ca24251d2062b51bf3f2b51a4e007516924ff50c4b4ed5059633d4f9b055d4f943bc44f8c57c24f717d1d4e1db72a4de254b54dc27b5b4d17706a4cfd734b4cd8ba054c5cc68f4c1e35cd4b02825d4aee737949d602e849bfa213499b08ca4980ebae49148db048f889f84879fd83475141bb46e1bded4609964845c07cca43b9f0a34365b3a9432891ef4305883642b779a341d9fb7841d622d341a8390641a4b5d640db2d8b40d001243e9c5ebb3e277fff3dc32c533d6d0b963d21e10c3d18fbc93cedcf813c9f3cdf
  | 8, 4 => 0x7260e48f71be65bd7005f1236f69601f6e38e6f66d483b2f6cd622c66be1bd3a6bcb63fb6b89f08a6b7c11ab6b6909ce6b58c0516b46b4d16b1be3666af785736aa2ab606a7ff6686a5eea176a510b3869c6f98169b07ce3692e70ee6920920f683fb3fc67425c616709aa6166fb4c9166742ba7655d937964789948645092fc6449b75d640159026379a67663669d9563353df463275f1562b43c176292bf226284e04362542af86240ab8761aa336860f8c4a560c016455fbac6fd5eebace45ec2fe405e90082e5e22a7545d93d62e5d7bf2db5d3a46645d2e415c5d1e66bc5cde0cce5c9fbd605c91de815c0095e65bff541c5af03eb059d66aa0596cee2e
  | 8, 5 => 0x8f9d1d5f8f7fd14d8f78512d8f46f2108e7679718ce77a638c8386ea8c1a6ee88bed86128bc68b508bbc73f08b308e208aef68758ab84b5d8a8bfac78a0d10dd8968a0cb89605ac288ede02887ec2302877c8a9f87080352868cb4248651842c85faf2fb8549f6d285210b03850f030e84e9742a8492c7cd83f048fb83804071833df90382dbd05f82d3eb997fe35f827f97da8d7f27d8097ebbf6017e8559377e1a8a567dfd47397c0721267ac854af7ab597257aa157477a85129f79dc30da798a90b278925775785a178978493a7f781054e377211a3f76f0916b76db0b2e766385db764e5f6174f2245d73f60c3a72b28339727daf3d72739f547263b2ee
  | 8, 6 => 0xd3a21f4ed0a7e5c1cf6e15b1cecb96dfc8d8951dc7a9b843c6f762cbc44be902c3d681efc2afde01c110cb7dbee065e9bc545819bc18011abbec3344bab08b31baa8a17cba9e7ab4ba2399e2b84d21e0b7a3f583b59a84ddb52557b8b3feb3cab32b1ae2b20ffb62b1b17014b108215ab0e1dcffaf01b67aaec64c0eada32de2ad85a160abbe6e52aaa935daaa3f12b1a98c5b5da8e78fc4a77ce252a309310ca07b39919ffd08839f9262399eab30d29e6bbe4b9c97dd089b71391a9b34b1219b308e9f9a9c46339a488f169a36658d9985b80798553ede974e731793cd8fe0939a9e6193602c46928df768927a567e925c0be491b98d1290f70fa9906d2611
  | 8, 7 => 0xfe12eeb4fce2758bf9acd0faf734b506f6e94291f646c3bff11d8484f053c1fdee22ff53ee03301ae575a6eae1283faae07b344edede789bd96359b3d8dd76c6d7c2c847d697c1d4d56748ab
  | 9, 0 => 0xc3d681efc2afde019b34b1218ab84b5d5e22a7545059633d4aee73793e277fff2efbd9642eedfa851561a43a1142fa41
  | _, _ => 0
def CV : Nat → Nat → Nat
  | 5, 0 => 0xa00016424c930200002424c930200000000c9100000000000000a000000000000d00000525002010000000000004000000000000a000000000000000006424c930200191500c9302
  | 6, 0 => 0xc9100000000480a2000000000012105000000000e1020000000012105000000480e201000000480a2010000020480200000000010910400000018c920000000540812000000051081201000000000a105000000590020100000000121060000000000003000000380220000000048062000000000006100000000010910100000039092010000000100101000000000610600000059002010000052440203000000000000b00000018c9200000000090920100000524402030000001802202000000000000a00000058c9202
  | 6, 1 => 0x1909202000005350020200000001041030000053412203000000000a10400000000c910000000028c02000000010440200000000000000a000000000000100006424c930200000104402000000003802201000000380a201000000480e200000005300a2000000000000008000000480220100000018022010000000002100000005240e20000000500c92000000000000000000000000000c000000480e200000000000610000000048c9200000000480a20000000104402030000000000010000000000000d0000000000000
  | 6, 2 => 0xa0000000000005000000000a10400000048c92030000000006103000000000e100000000480620000000424c9202000000000000f000000000a10000000540812000000000909202000000000000d00000000c51040000000012100000000000610500000434c92030000004806201000000480220000000324c1203000000480a2020000000000000000005244020300000104402010000000000011000000390920100000048c020000000018c92000000004806201000000380220300000540412030000004802201
  | 6, 3 => 0x90920100000000121010000052500202000005240e20000000019092010000000002104000000000a102000000000a1040000002802200000000000000a00000039092010000000000000000000190020100000000000040000010440202000000480e202000000000000d0000001909201000000480220000000018c0200000000280220100000009092010000000012105000000380a20200000048022020000000000000000005304120000000204802000000050109201000000280220200000000000100000004806200
  | 6, 4 => 0xc9100000000000210000000028062000000051081201000000000a10400000029092010000054081200000000180220200000008c020000000324812020000000002104000000480e20300000001091040000001802201000000000000d000000000000a00000000000010018d50085303000000480e201000005108120100000000c510400000540812000000000006100000000000e104000000000a10600000018c92000000000012102000000000e100000000380220000000000c9100000000280220000000434c9203
  | 6, 5 => 0xe104000005408120000000001091040000000000000000000000210200000540412000000000109101000000000001100000028c0200000000380a20100000530412010000003909201000005300a20000000000c510400000048022030000003802202000000000000d000000000a104000000000610000000038062010000001802200000000000000a00000008c9203000000000a10400000018c920000000029002010000001909201000002048020000000048c9200000000480220300000038062020000032481202
  | 6, 6 => 0x200000424c92020000051081201000000000000d000000010d106000005404120100000000c51040000002806202000000000000d00000434c9203000005148020000000000000000000000012103000000090920100000038022010000000002101000000000000d0000002802201000000000000000000048c92000000000000001000000000000800000001091040000052500201000000000000c0018d54081303000000000e10400000000021020000004802201000000000000100000000000000000003806200
  | 6, 7 => 0x1909201000000380220200000000121030000002802200000000000000e000000001210400000524c0200000000480e20100000434c920300000000000000000000006105000000380a20000000000121040000000012104000000010910500000104402000000000000003000000000000d00000018022030000000000000000000010910400000018c9202000005108120000000434c12030000002806201000000290920100000018022010000000909201000000001210000000424c920200000501092010000000000005
  | 6, 8 => 0x90020100016434c9303000000000a10400000000121040000052440202000000000000d000000000210000000000061000000000109104000000390920100000000c910000000028062000000053500202000000001210100000524402030000053041200000000480220100000434c920300000540812000000000000011000000000000300000000c010000002434c93030000000000000000000380a2030000000002104000005404120200000324c1203000000380220000000434c920300000424c920200000424c9202
  | 6, 9 => 0x51081200000000480a200000000000000a000000000000000000048c02000000000109102000000380a20000000008c9200000005001220100000048c920000000018c020000000009092010000000012101000000000000d000000380a200000005240e200000000000610500000424812020000000006101000000480620100000039092020000000900201000000480220000000524c020000000009092020000003806203000005350020200000039002010000000000007000000008010000000000021040000000000005
  | 6, 10 => 0x5350020200000028c92000000000012100000000000000f0000053041201000000000000a0000000000008000000280620000000008c9200000000180220000000434c9203000000000a10100000434c9203000000280620100000008c92000000001802202000000000e100000000480a2030000004806202000005240e20000000424812020000003806201000000280220000000048c9200000000000a10000000510c12010000002806202000005404120000149424c0301000000000000600000540412010000000000007
  | 6, 11 => 0x3900201000000480a2010000053484200000000001210300000028c92000000000002106000000000a101000000000000c00000000061000000000000009000000000e102000000380a201000000000610400000500c92020000002802200000005348020000000000061000000000000005000000480220000000018022000000054041200000000000e10500000008c920000000018c02000000004802200000000290d203000000000000a00000048062030000000002104000000000000700000018022010000000012104
  | 6, 12 => 0x900201000000000210400000000000040000000109101000000480e2010000000002105000000000610100000008c92000000000006104000000000210400000000000040000010440201000000480a2020000003909201000000380a202000000000000a0000053440202000000000000c000005404120000000000021030000001802201000001044020000000000061020000032500200000000480620100000048c0200000000000000c000000000000a0000000000000000000000610200000501092010000054081200
  | 6, 13 => 0x2806200000000000210400000018c92000000000002104000005244020200000018022000000054081200000000000a100000000380a201000000000000400000424c920200000058c92030000054081200000000000000b00000019002010000001909202000000380a2000000000000005000000480a2010000000000004000000000e1040000000000004000000000610400000544402020000051081200000000000000c000000000000c000000480e200
  | 7, 0 => 0xe10500000000121030000000002105000000000000600000000021010000000006102000000000610300000000c1102000000380a20000000000851020000003802203000000000000d00000000021030000000002100000000000000100000000c5102000000000610300000000000020000000002106000000000210100000000000010000000012102000000000000400000000c01000000000002103000000008010000000000000080000000041102000005304120100000028022000000000006102000000000000c
  | 7, 1 => 0x290020100000000c01000000000104100000000000000d000000000000500000000121000000000040101000000000000100000434c920300000000061020000000002103000000000610200000058c92020000053081201000000000000300000000021010000000000000000000000a1000000003802200000000010c10000000000000110000000006100000000000000d0000000002101000000010d1060000000002105000000000210200000000121020000001909201000000000a103000000000a1010000000000000
  | 7, 2 => 0x2103000000010010000000540412030000000081100000000180220100000000c910300000000021020000000002102000005304120100000001091010000004806202000000000000100000000c41000000000002101000000480220000000000000040000000002100000001044020000000048022010000000000005000000000a10000000000000040000000085101000000001210200000001041010000000000007000000010910100000000021030000000081100000000000610100000000c01000000000006104
  | 7, 3 => 0x40000001802201000000010c1010000000002100000000380620200000001041000000000000000000000000e10200000000021000000000006103000000000000500000000000040000000002100000000000210300000000c51040000000002106000000000e100000000000210300000000061010000000002103000000000a100000000000a100000000000610000000000121030000053041200000000004010100000000121000000003806202000000000e1040000000000005000000380a202000000000e103
  | 7, 4 => 0x3806203000000010d10600000000000060000000000007000000010910100000540412030000000002103000000010910400000000061000000001802202000000000000a00000540812000000004806200000000000210400000000401000000000002102000005350420300000000c910000000000061060000000109101000000000a10000000000061010000010440203000000000a10000000001091010000000000003000000000e1000000000006102000000000e100000000000000700000000021000000000012101
  | 7, 5 => 0x21020000000000006000000001210000000001091020000000002101000000000000200000000c91000000000000000000000000e1020000001802201000000000e1010000003806202000000001210600000000021000000004806202000000004010000000000c010100000001091020000000000004000000000e10000000000000000000000012103000000000610100000000c91030000000000001000005250020100000000401000000003806200000000001210100000000c41010000000012102000000000e101
  | 7, 6 => 0x600000000c0100000000000a10100000000061040000002806200000000001210600000000411030000000000000000000000210100000000c0100000000001210400000000061010000000000004000000000210000000000c5103000000000000c00000000401010000000100101000000010d1030000000000004000000000610200000000000030000000100103000000000000a00000000000030000000002101000000000000c000000000210200000000000070000000081100000000000210400000000c9103
  | 7, 7 => 0x909201000000000000600000000000060000002802200000000000e1000000002802202000000001210200000000000030000000012101000000000a1040000000000004000000008510200000104402020000000006102000000000a10000000000c110300000000000000000000012101000000000000100000000000000000000000002000000000000d000000380620300000000061020000004802200000000000a1040000000104101000000000000d00000000000020000000012100000000000e101000000000a100
  | 7, 8 => 0x10c10000000000c910000000000c91000000000040101000000010d1030000000100100000000000a106000000000210100000000c0100000000001210300000000000020000004802201000000000000c0000000002102000000000e1000000000006100000000000210200000000411010000000000000000000000a101000005240e20000000001041000000052412202000000000a102000000380a200000000000000000000000c91020000000000004000000000000c000000000000700000000021000000000006101
  | 7, 9 => 0x1001000000000000007000000000210200000000c01000000000006101000000480a20300000000021020000000000007000000000000a000000000000200000000021030000000006102000000000000d000000000a10200000424c920200000000021010000000006100000000000000400000000c510400000000121020000000040102000000000210200000000c010100000000000070000000002105000000000a10400000008c9200000000000210100000000000040000004802202000000000e102000000000a102
  | 7, 10 => 0x7000000000e1030000000081100000000010d1030000050085203000000000e10200000000121020000000012102000000010110200000000401020000000109101000000001210300000000061000000000109104000000000210300000000000030000000006100000000008110200000000841000000053500203000000000610000000000021030000000081103000000000000100000000021030000000000011000000000e103000000000000d0000003806202000000010910200000038062030000051081201
  | 7, 11 => 0x610300000001091020000000000001000000010c10100000000061020000000006104000000480a20300000000401010000000000003000000000a10100000000061010000000006100000000000000500000038022020000000006100000000000210500000000000050000000002103000000010c10000000000c5104000000000e101000000010010100000424c920200000000061020000000109102000000000210300000000021040000004802203000000000610100000000000060000000002105000000000000d
  | 7, 12 => 0x3000000000a103000000000210200000001091030000000109101000000000e103000000000000000000000000020000000000002000000000a101000000000e1040000000006101000000000e101000000000e10000000001091010000000012101000000000610300000000021030000004802203000000000e101000000000000700000000021030000000000007000000000a10200000000021020000000000007000000010d106000000010c101000000000610000000000000040000000109104
  | 7, 13 => 0xc510400000000c0100000000000a100000000010010100000000061000000000000004000000000a100000000480e200000000000210200000000c010100000000c910000000028062000000000000004000000000000500000000c11020000000002101000000010d10300000000021020000000104100000000090920100000000c9102000000000a1000000000006100000000000610300000540c12020000052412202000000000210400000000061030000000000000000000010410100000001091020000000000004
  | 7, 14 => 0x61060000000000002000000000210600000000c9102000000000e1000000000006104000000280620100000000000040000000000006000000000e100000000000210200000000c510400000000061020000003806200000000290d203000000000a1010000000002101000001044020100000000000050000000002104000000000000400000000021030000000000004000000004010000000000c1103000000010d103000000000210100000000000100000001802200000000180220200000000811000000003806201
  | 7, 15 => 0xc11030000000081100000000000e104000000010d10300000000061040000000006104000000090d20300000000c910000000000401020000000002100000000480a20100000000061010000000041102000000000000600000001091010000000000007000000000000c0000000109102000000000210000000001091020000000101102000000000000600000000021010000003909202000000010d103000000000e10100000000021030000000006102000000000000700000000121000000000000003000000000e101
  | 7, 16 => 0x21010000052412201000000000a1000000000012102000000000a1030000000081100000000480220000000000c5103000000000e104000000000e1040000000006100000000000e1040000000002101000000000610200000000000100000000000000000000004010300000000811000000000000000000000000a10300000000021000000000109101000000480620300000000061030000000000007000000000210000000000021040000010440201000000000610200000000c9102000000000a1020000000006102
  | 7, 17 => 0x100000424c9202000000480620300000048c9200000000000610100000000061000000000012104000000000a105000000000e100000000004110100000000021030000000006101000000001210100000000121000000000080101000000000e101000000004010000000524122020000003909202000000000210100000000c5104000000010910100000000c910200000000000060000000000005000000090d20300000000000020000002802202000000000000e0000000000010000000000000d0000000000005
  | 7, 18 => 0x10000000000e1010000000006101000000280220300000018c02000000000000004000000000210000000000000060000000012105000000004110200000000061010000000002102000000000a1060000000002103000000000000500000000c910000000000401000000000109101000000001210000000000061020000000000004000000000000a000000000000400000000121040000000109102000000000a1000000052412201000000000a1010000000041100000000004010000000000c41000000000000004
  | 7, 19 => 0xe10500000000000030000000006100000000000000500000000021010000052412202000000000e101000000000a102000000000000c00000000121040000002802201000000000000700000000061030000000085103000000000a1030000000100100000000000a10400000000c910300000000121010000002802202000000000000200000018022020000032481202000000000e10000000000c91000000000081100000000000000d000000380a2010000000104103000000010010000000038062000000000002102
  | 7, 20 => 0x81102000000190d203000005408120300000000811020000000006101000000000e1030000050504202000000000e10100000000000040000054081203000000000a104000000004010000000000c010000000028022030000000000000000000010410000000000121020000000002102000000000e1000000004806203000000000610100000530812010000000006101000000280620300000000c910200000000061000000004802202000000000a10300000424c9202000000000a10300000000401010000000000003
  | 7, 21 => 0xa1000000000000002000000000000800000000121010000000006101000000000a10400000000061010000000006102000000000610400000000000050000000002101000000000000c0000000002100000000001210000000000811000000053041200000000000210300000001001010000053041201000000000210200000000021010000004802200000000000210500000540412030000000000000000000008510100000524122010000000040103000000008110000000000021020000000040100000000000a106
  | 7, 22 => 0x10910200000048c92000000000000007000000000610300000000121010000000000001000000000e100000000000e100000000001210100000000c0100000000000610100000038022000000000000000000000190d203000000000000500000001041010000000000003000000000e102000000010910400000000121000000000002100000000010910100000000061020000000040102000000008410100000009002010000000000011000000000000c0000054041201000000000a10000000000061010000000006102
  | 7, 23 => 0x2806201000000000a103000000000a10500000104402020000000002101000000008110200000000c0100000000000e10300000000061050000001802202000000000e1020000000080101000000004110200000000021020000000000000000000000000c0000000000006000000000610200000000000050000000000004000000000000600000018022020000000109102000000000e1010000002802202000000000e10000000000121030000000000005000000000000100000000000050000000002103000000000000c
  | 7, 24 => 0x2102000000380a2030000000012104000000000e1030000000101100000000000210100000048c9202000000190d20300000000000070000000002102000000380a20100000000c9100000000000000f000000001210100000000000040000000012105000000000210000000018022030000000109101000000000210100000000c41010000000012101000000000610600000000000070000000000006000000010910400000000c91000000000104102000000000000d0000003909202000000380a2010000000002104
  | 7, 25 => 0x2104000000010010100000000000010000000002101000000000210000000000061000000000012102000000000e10500000000c4100000000008510100000000121000000000000004000000010010100000000000010000000002100000000380a200000000010010300000000c01000000000000003000000000a1050000000041103000000000000700000000000050000000909202000000000000300000048c9200000000000e103000000000000700000000061020000000000005000000000a1040000000000004
  | 7, 26 => 0xa10300000008c920000000000121050000000081100000000010d103000000000000100000524122020000000002101000000000e100000000000000c0000000002105000000000000700000540412010000000000002000000010d1030000000000004000000000e1000000000002104000000000a105000000000a1020000000006103000000010910200000000401030000000000000000000000a1050000000109102000000000a10300000018c920000000000c4100000000000a10600000008c920000000018c9203
  | 7, 27 => 0x530412000000000002103000000004110200000018022020000000000006000000480e201000000000a100000000000a106000000000a1030000000006101000000000a103000000000e10300000000021000000000002101000000000e1020000010440202000000000a103000000000a1020000000002101000000000000400000000c0100000000001210100000540c12020000000002104000000000a104000000480a200000000000610000000000021030000000002101000000000a100000000000e1010000000002105
  | 7, 28 => 0x2000000000000d000000008510700000000000070000000012102000000000e100000000000000400000000000040000000006103000000000610300000000061040000000041100000000000e100000000000610100000019092010000000000006000000000000700000000121000000000000004000000000e1010000000002103000000000a101000000000e10100000000121000000000012104000005404120300000000021020000000109101000000000e10500000028062010000000012102000000000a102
  | 7, 29 => 0x411030000000012101000000000a102000000280620000000018c920000000001091010000000000001000000000a1050000000000007000000000e101000000000e101000000000e1040000000012103000000001210200000000000040000054041203000000000a10000000000021000000000012104000000000e106000000000000a000000000610200000000121000000000104101000000000000800000000c5102000000000210100000000021010000000000004000000000000e000000001210400000000c9100
  | 7, 30 => 0x6106000000000610300000000061000000000040100000000000210300000000401000000000100101000000001210400000038062000000000081100000000001210500000000c4101000000004110100000000061050000003806201000000000e100000000000210100000008c920000000000000070000000002101000000000a1000000000000001000000000000a00000000021010000000006101000000380620300000000c0100000000010910100000000c9100000000000210500000000021030000000002100
  | 7, 31 => 0x20000001802201000000000a101000000000e101000000000a100000000000000d000000380a200000000480a2020000000002101000000010910300000000000110000000006101000000000210100000000021060000000109104000000000000300000000000010000000006101000000000210400000000061050000000006102000000010910100000000c0100000000000a100000000480e200000000008510000000038062030000052500203000000000a1020000000006103000000000e1030000010440202
  | 7, 32 => 0x6103000000000000600000000121040000000002100000000000210300000000061000000000109102000000000e10100000000061030000000109101000000010010300000000c0100000000000000c000000000000200000000061010000000909202000000480e202000000000a102000000480e201000000480620100000000801010000000080100000000010c100000000000000e00000000000010000053440203000000000000400000000811030000000012103000000000a10200000000000000000000002101
  | 7, 33 => 0x610100000000c010000000000121000000000000002000000000000d000000010410100000000000020000000012103000000000210400000000121060000000002101000000000000d000000004010100000028022010000000012104000000480a20300000000c0101000000000a1050000000000004000000000610000000000021050000000012103000000000000600000001041000000000006100000000000000a000000000210500000540412000000000012102000000000610300000000000000000000006103
  | 7, 34 => 0xa1000000000000002000000000e10000000000021040000000000004000000000e102000000000000100000000061050000000100101000000010d1030000000006101000003250020000000540c120200000000000050000002802201000000000610000000000000050000000000001000000480e202000000000e1010000000012105000000000a102000000004010300000001091010000003802203000000000a100000000480220300000000000030000000012105000000000000100000000000080000003802202
  | 7, 35 => 0x2000000000000c0000000085102000000010d103000000000000000000104402020000000002105000000010c10100000000000060000000002101000000480a20200000000121040000000000004000000000e10000000000021040000004806200000000000a102000000000a105000000010c101000000004010200000000121040000000002101000000000000400000000000010000000000001000000000610400000000121060000000000003000000380220100000000c510400000000061010000000104101
  | 7, 36 => 0xa100000000000000200000000061020000003909201000000001210100000018c920000000000000040000000081103000000000a100000005404120000000540812000000004806201000000000610200000001011030000000000005000000000a10300000540c12020000000002104000000000e1010000000006100000000001210200000000061040000003909201000000000000d0000001909201000000001210300000000000000000053500202000000000000600000000021000000000000002000000000e103
  | 7, 37 => 0xe10000000000c51020000000012102000000000210100000000061040000000002102000000000000a000000000000000000000021000000000000002000000000000e00000000021030000000002100000000000e10000000001001020000000000000000000004010000000000000000000000002104000001044020100000000061010000000002101000000000a106000000010d10300000000021010000000006104000000000000600000000000020000000006101000000004010000000000c91030000000000001
  | 7, 38 => 0x40000000006102000000000a1020000000000005000000000a101000000000a100000000000210300000018022000000004806203000000001210300000000c91000000000000004000000000000d00000000000040000000002103000000000e101000000000001100000000021040000000041100000000480a2020000000002102000000000000700000000121000000000000005000000010910200000000061050000000109101000000000000400000000c510400000000c510400000000061030000004806203
  | 7, 39 => 0x9092020000000000007000000000000a00000000000020000000002105000001044020200000000061010000000002102000000000e1010000000000003000000004010000000000401030000000109101000000010010100000000061010000000000004000000480a202000000000e1000000000002104000000000001000000001041000000000002105000000280220300000000c91000000000002103000000000e100000000000000a000000000000d000000000a10300000000000070000000109105000000010d103
  | 7, 40 => 0x48022000000000000002000000000000e00000000021000000004802201000000000e1000000000000005000000001210400000000021040000000006100000000000000c000000001210200000048022030000000002101000000480e200000000000e103000000000e1060000000000007000000190d20300000000021000000000000005000000000a1000000000109105000000004010100000048022010000000002102000000010d10600000000061060000000006102000000004110100000000061010000000002100
  | 7, 41 => 0x210400000028062010000000109105000000280220000000000c11020000000002100000000000000800000000000060000000000005000000000610200000000021010000000104103000000008510000000000061020000000002104000000000000300000048022000000000000001000000000a1000000000084101000000180220100000000c9100000000000000200000000c910000000000c9100000000190d203000000000210200000000000030000003900201000000004010000000000061010000004806200
  | 7, 42 => 0xa102000000008110000000000021020000000002102000000000000d0000000002101000000000000700000000000050000000000005000000000000500000000c9103000000000a104000000000000600000000021030000000000003000000000e100000000000610500000000c01010000000000000000000000210000000001041030000000000007000000000000300000028062030000000081103000000000000700000000c410000000434c920300000000c01000000000000002000005240e2000000000080100
  | 7, 43 => 0xc9100000000000000400000540412030000000100101000005240e20000000000121000000000000004000000010910200000000061020000000000002000000000a10200000000000100000000006102000000010d1030000000100101000000000000300000000000070000000000011000000000000a000000001210500000000000000000003806200000000008110200000000c0100000000000610000000001001010000000041101000000000e1020000000040100000000000000500000000c91000000010440200
  | 7, 44 => 0x10910500000000c0101000000010c10000000000000050000002802200000000001210300000001041010000000081102000000000e103000000000e1000000000100102000000000e10300000001091010000000002102000000004110300000000c91020000000000004000000000e102000000000610300000000c51040000000000003000000000000b000000000e101000000000000400000000000000000000002104000000004010000000000000040000000109102000000000a10100000000000000000000002100
  | 7, 45 => 0x61010000000000000000000000210000000530812010000054081200000000380620100000000841000000000006103000000000a10000000001091020000000000004000000000e1010000000000007000000000210400000000c010000000000c51020000000040102000000000610100000000061050000000109101000000010410300000000811020000053041201000000000000d000000000e1030000010440201000000000000400000534402020000000000007000000000210000000505042030000000000004
  | 7, 46 => 0x10000000010410100000000c9100000000000000700000000c91020000000000007000000380a20100000018c9200000005308120100000000061010000000000004000000000a101000000000000a00000000000070000000109101000000010910500000000021020000000000002000000010d106000000000610000000000c0100000000180220200000000c5103000000000610000000000021000000000000004000000000e10300000018022000000000000005000000000210100000000c91000000000109102
  | 7, 47 => 0xe10000000000021030000000002101000000000000200000000000050000000012101000000000210200000000c9100000000000e103000000000000100000000061010000000000001000000000610100000000000050000000109102000000010910100000000c01000000000000004000000000000100000000000040000000000004000000000a10100000000021000000000002100000000000000d000000010910100000001091000000000002100000000000210400000000c0100000000010c1000000000000004
  | 7, 48 => 0xa1010000000006103000000000000b0000000006103000001044020000000000c01000000000002101000000480a2010000000002101000000380a202000000000a100000000000610500000000c9100000000000000400000000000080000000085101000000010c100000000000000400000000c910200000000401010000000000004000000001210300000000061030000000002102000000000610000000000000070000000002101000000000000200000000121020000000012103000000000a1000000000012103
  | 7, 49 => 0xe000000000000a0000000002103000000000000700000008c9203000000001210300000000000050000000006105000000004110000000000021020000000000004000000000a10000000000061000000000002104000000000210300000000000020000000012101000000000000700000000121030000000000004000000000000c000000480e201000000000e105000000000000700000000021010000000002101000000000000700000000000050000000002102000000000000d00000000021040000000000000
  | 7, 50 => 0x2104000000001210200000000021050000000000007000000380a203000000000e1030000000000007000000000a100000000000000400000500c9202000000000000300000000000040000000000002000000000610000000000c9100
  | 8, 0 => 0x10c100000000000000200000000021020000000000003000000000000100000000c0100000000000001000000000061000000000006102000000000000200000000c910300000000411010000000000004000000001210300000000000010000000000000000000000000100000000c410000000000851030000000100100000000000000200000001041000000000104101000000004110100000000000000000000000001000000000000600000000811020000000000001000000001210300000000000030000000000003
  | 8, 1 => 0x10d1030000000081102000000000000200000001041010000000002100000000000000200000000000040000000081103000000000000200000000000000000000000000000000000000400000000021010000000000001000000000000100000000000040000000000010000000010d10300000000c01010000000000001000000000000400000000000050000000000001000000000a10300000000000000000000081102000000000000000000000000040000000006100000000000000a00000000000000000000006101
  | 8, 2 => 0x10c101000000000000200000000c11020000000104103000000000000200000000c4101000000000000300000000021030000000000001000000000000400000000000040000000085100000000000000600000000000000000000000001000000010410300000000000020000000000006000000000a1010000000006100000000004010000000000851010000000000005000000008110300000000000050000000040101000000000000200000000061020000000002102000000000000300000000000030000000000001
  | 8, 3 => 0xc01000000000000004000000000210300000000000040000000000000000000000000000000000000020000000000000000000000000200000000061020000000000004000000010010300000000000050000000000003000000000000700000000000080000000006102000000000000600000000c4100000000000000500000000c410100000000c9100000000000210300000000c910300000000061030000000000000000000008110200000000411000000000000003000000004110200000000000030000000000001
  | 8, 4 => 0x400000000000000000000000006000000000e100000000000000600000000000050000000000002000000000e10100000000000010000000000002000000000e1030000000081101000000000a10000000000c91000000000085103000000000000600000000411020000000000000000000000000200000001001010000000040103000000000000300000000000030000000104100000000000000300000000851010000000000003000000000a1010000000100103000000000210200000000000010000000006103
  | 8, 5 => 0x4110200000000000040000000104102000000000000300000000000040000000000002000000010410000000000000010000000012100000000001210100000000000070000000000002000000000000300000000000070000000000001000000010010200000000000010000000006102000000000000100000000c01000000000000005000000000000200000000401020000000000005000000000e1030000000000003000000000000000000000000050000000000006000000000000000000000000030000000081101
  | 8, 6 => 0x1210100000000000020000000000006000000000000000000000021010000000109101000000000a10200000000000010000000000005000000000210200000000121000000000006101000000000000d0000000000002000000000000500000000000010000000006101000000000000000000000000070000000002101000000004110300000000000010000000000004000000000000300000001001000000000000000000000000000000000000411010000000000000000000000000300000000000030000000000003
  | 8, 7 => 0xc5103000000000000400000000000020000000000004000000000210000000000021010000000012103000000010410100000000000040000000000010000000000000700000000c0100000000000000500000000000100000000000003000000001210300000000c0101000000000000000000000851010000000000003000000000000700000000401010000000000003000000004110200000000000040000000000006000000000000100000000811000000000000002000000000000100000000c91000000000000001
  | 8, 8 => 0x12100000000004110200000000061000000000000001000000000210000000000021020000000000003000000000000000000000c9102000000010410200000001001030000000000004000000010d1030000000000000000000000000300000001001010000000000006000000010410200000000000020000000000001000000000000100000000000000000000000003000000000000400000000000010000000006100000000000610200000000c11030000000000004000000000000a00000000000100000000000004
  | 8, 9 => 0x21020000000000000000000000a103000000000000400000000000040000000000001000000000a101000000000a102000000000610200000000851000000000085102000000008110000000001041030000000000007000000000000000000001041020000000000002000000000a103000000000000000000000c510200000000000020000000000003000000004010000000000401020000000000007000000000000300000000000030000000002101000000010c100000000010d10300000000000010000000081103
  | 8, 10 => 0x400000000000010000000000000000000000000a00000000000020000000002102000000000000200000000c910200000000000000000000006103000000004110000000001001030000000085102000000000610200000000000020000000000002000000000000000000000061020000000040102000000000a1020000000000003000000000e100000000010c10100000000811000000000100103000000000000000000000c110300000000061010000000000002000000001210000000000000050000000000006
  | 8, 11 => 0x210200000000000110000000000000000000000000200000000021000000000085103000000004110100000000000040000000000003000000000610200000000c5103000000000000800000000000040000000000000000000004010300000000c010000000000c010100000001041010000000000004000000000000500000000851020000000000001000000000000500000000c5102000000000000500000000c0101000000004010200000000811000000000000004000000000210300000000c910300000000c9100
  | 8, 12 => 0x300000000000040000000002100000000000000500000000811010000000000004000000000e1010000000012103000000000a101000000000000100000000000020000000040101000000010c100000000000610200000000061000000000000001000000000000500000000000050000000000001000000000000400000000c5102000000004010200000000c410100000000c91000000000000001000000000000100000000000030000000000003000000000210200000000c910200000000000000000000000001
  | 8, 13 => 0x1000000000000400000000021010000000000001000000000610100000000000080000000000002000000000000400000000000010000000000000000000001210100000000000050000000000004000000000a103000000000000300000000000070000000000004000000010c100000000000000a0000000000004000000000610000000000811030000000041102000000004110000000000000030000000100101000000000000000000000000060000000000004000000000000400000000000030000000000004
  | 8, 14 => 0x401000000000000000000000000001000000000021000000000000000000000010c101000000000610000000000061010000000000000000000000000400000000021010000000000004000000000210200000000021010000000104100000000000000100000000851010000000040101
  | 9, 0 => 0x200000000000000000000000001000000000000000000000000020000000000003000000000000200000000000020000000000000000000000000200000000000010000000000001
  | _, _ => 0
def chAt (s i : Nat) : Nat := fld (CH s (i / 64)) 32 (i % 64)
def cidxH (s h : Nat) : Nat := bsr (chAt s) h 12 0 (CN s)
def cidx (s : Nat) (zs : List Nat) : Nat := cidxH s (hk 0 zs)
def checkCutByIdx (s : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  match hint &&& 255 with
  | 0 => checkCutEntry dom_55 roots_55 8 s ws hint
  | 1 => checkCutEntry dom_59 roots_59 8 s ws hint
  | 2 => checkCutEntry dom_31_32 roots_31_32 8 s ws hint
  | 3 => checkCutEntry dom_47_16 roots_47_16 8 s ws hint
  | 4 => checkCutEntry dom_61_2 roots_61_2 7 s ws hint
  | 5 => checkCutEntry dom_31 roots_31 7 s ws hint
  | 6 => checkCutEntry dom_47 roots_47 7 s ws hint
  | 7 => checkCutEntry dom_62_1 roots_62_1 6 s ws hint
  | 8 => checkCutEntry dom_15 roots_15 5 s ws hint
  | 9 => checkCutEntry dom_23_32 roots_23_32 5 s ws hint
  | 10 => checkCutEntry dom_51 roots_51 5 s ws hint
  | 11 => checkCutEntry dom_57_2 roots_57_2 5 s ws hint
  | 12 => checkCutEntry dom_54_1 roots_54_1 5 s ws hint
  | 13 => checkCutEntry dom_58_1 roots_58_1 5 s ws hint
  | 14 => checkCutEntry dom_39 roots_39 5 s ws hint
  | 15 => checkCutEntry dom_27 roots_27 5 s ws hint
  | 16 => checkCutEntry dom_29_2 roots_29_2 5 s ws hint
  | 17 => checkCutEntry dom_45_2 roots_45_2 5 s ws hint
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
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_55 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_59 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_31_32 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_47_16 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_61_2 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_31 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_47 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_62_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_15 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_23_32 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_51 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_57_2 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_54_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_58_1 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_39 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_27 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_29_2 _ hc
  · exact checkCutEntry_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_45_2 _ hc
  · contradiction
theorem cutHit_sound {u ys} (h : cutHit u ys = true) : ¬ RunD dom_63 goalM u ys := cutHitH_sound h

def symsG : List (List (Nat × Nat)) := [[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)]]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
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
private theorem z5_0 : ∀ i, 0 ≤ i → i < 15 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 15 0 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 15 → Z 5 i = true := z5_0
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
private theorem z6_112 : ∀ i, 112 ≤ i → i < 123 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 11 112 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 123 → Z 6 i = true := (range_split (range_split (range_split z6_0 z6_16) (range_split z6_32 z6_48)) (range_split (range_split z6_64 z6_80) (range_split z6_96 z6_112)))
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
private theorem z7_320 : ∀ i, 320 ≤ i → i < 326 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 6 320 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 326 → Z 7 i = true := (range_split (range_split (range_split (range_split (range_split z7_0 z7_16) (range_split z7_32 z7_48)) (range_split (range_split z7_64 z7_80) (range_split z7_96 z7_112))) (range_split (range_split (range_split z7_128 z7_144) (range_split z7_160 z7_176)) (range_split (range_split z7_192 z7_208) (range_split z7_224 z7_240)))) (range_split (range_split (range_split z7_256 z7_272) (range_split z7_288 z7_304)) z7_320))
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
private theorem z8_128 : ∀ i, 128 ≤ i → i < 131 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 3 128 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 131 → Z 8 i = true := (range_split (range_split (range_split (range_split z8_0 z8_16) (range_split z8_32 z8_48)) (range_split (range_split z8_64 z8_80) (range_split z8_96 z8_112))) z8_128)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z9_0 : ∀ i, 0 ≤ i → i < 16 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 16 0 = true)
private theorem z9 : ∀ i, 0 ≤ i → i < 16 → Z 9 i = true := z9_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem z10_0 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := span_ok (by decide +kernel : span (Z 10) 1 0 = true)
private theorem z10 : ∀ i, 0 ≤ i → i < 1 → Z 10 i = true := z10_0
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

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
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

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 14]⟩], 16⟩

theorem wit_mono : PEqualNP.MetaComplexity.Monotone2 wit := by
  simp [wit, PEqualNP.MetaComplexity.Monotone2]

theorem wit_sz : wit.size ≤ 11 := by decide

set_option maxRecDepth 40000 in
theorem wit_ev : ∀ x : Fin 6 → Bool, wit.eval (List.ofFn x) = Nat.testBit (4008372968 * 2 ^ 32 + 4004047520) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by decide +kernel

set_option maxRecDepth 40000 in
theorem hT6 : ∀ r : Fin 64, goal_63.testBit r.val = (fun x : Fin 6 → Bool => Nat.testBit (4008372968 * 2 ^ 32 + 4004047520) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) (pt6 r.val) := by decide +kernel

theorem lower : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372968 * 2 ^ 32 + 4004047520) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) t → 11 ≤ t :=
  lower_to_circuit6 (fun x : Fin 6 → Bool => Nat.testBit (4008372968 * 2 ^ 32 + 4004047520) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) goal_63 11 hT6 (by unfold IsConst; decide) low_63

end PEqualNP.Outside.L_meta_38503_aux

theorem PEqualNP.Outside.L_meta_38503 :
  ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372968 * 2 ^ 32 + 4004047520) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372968 * 2 ^ 32 + 4004047520) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hs
  exact ⟨PEqualNP.Outside.L_meta_38503_aux.wit, PEqualNP.Outside.L_meta_38503_aux.wit_mono, le_trans PEqualNP.Outside.L_meta_38503_aux.wit_sz (PEqualNP.Outside.L_meta_38503_aux.lower s hs), PEqualNP.Outside.L_meta_38503_aux.wit_ev⟩
